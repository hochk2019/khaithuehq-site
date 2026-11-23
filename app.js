/* Văn bản XNK — tra cứu kết quả phân tích phân loại.
   Vanilla JS, không framework, không CDN. Tìm kiếm chạy hoàn toàn
   trên trình duyệt với dữ liệu trong data.json. */
(function () {
'use strict';

/* ================= Helpers ================= */

function esc(s) {
  return String(s == null ? '' : s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

/* Chuẩn hóa tiếng Việt: bỏ dấu, thường hóa, bỏ dấu câu.
   NFD tách dấu tổ hợp; đ/Đ xử lý riêng (không tách được bằng NFD). */
function norm(s) {
  return String(s == null ? '' : s)
    .normalize('NFC')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .replace(/đ/g, 'd').replace(/Đ/g, 'D')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, ' ')
    .trim();
}

function hsDigits(hs) { return String(hs || '').replace(/\D/g, ''); }

/* Levenshtein với ngưỡng cắt sớm: trả về > max nếu khoảng cách vượt max. */
function lev(a, b, max) {
  var la = a.length, lb = b.length;
  if (Math.abs(la - lb) > max) return max + 1;
  if (la === 0) return lb;
  if (lb === 0) return la;
  var prev = [], cur = [], i, j, cost;
  for (j = 0; j <= lb; j++) prev[j] = j;
  for (i = 1; i <= la; i++) {
    cur[0] = i;
    var rowMin = cur[0];
    for (j = 1; j <= lb; j++) {
      cost = a[i - 1] === b[j - 1] ? 0 : 1;
      cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost);
      if (cur[j] < rowMin) rowMin = cur[j];
    }
    if (rowMin > max) return max + 1;
    var tmp = prev; prev = cur; cur = tmp;
  }
  return prev[lb];
}

function parseDate(ngay) {
  var m = /^(\d{2})\/(\d{2})\/(\d{4})/.exec(String(ngay || ''));
  if (!m) return 0;
  return new Date(+m[3], +m[2] - 1, +m[1]).getTime();
}

/* Từ đồng nghĩa / cách gọi khác thường dùng (đã chuẩn hóa, không dấu).
   Chỉ dùng để mở rộng khớp, không thay đổi nội dung văn bản. */
var SYN = {
  'quan ao': ['may mac', 'hang det', 'det may'],
  'o to': ['xe o to', 'phu tung o to'],
  'xe may': ['xe gan may', 'phu tung xe'],
  'do gia dung': ['dung cu nha bep', 'do dung gia dinh'],
  'thuc pham': ['nguyen lieu thuc pham', 'che bien thuc pham'],
  'my pham': ['hoa my pham', 'cham soc da'],
  'thuoc': ['duoc pham', 'duoc lieu'],
  'giay': ['giay dep'],
  'tui': ['tui xach', 'ba lo'],
  'nhua': ['plastic'],
  'sat': ['thep'],
  'go': ['van go', 'do go'],
  'dien thoai': ['dien thoai di dong'],
  'may tinh': ['thiet bi tin hoc'],
  'sua': ['sua bot'],
  'ca phe': ['hat ca phe']
};

var LOAI_LABEL = {
  'phan_tich_phan_loai': 'Phân tích phân loại',
  'xac_dinh_truoc_ma_so': 'Xác định trước mã số',
  'khac': 'Văn bản khác'
};

/* ================= Index ================= */

var DOCS = [];
var DRIVE = {};
var IMG = {}; /* ma -> Drive file ID của ảnh trang 1 (WebP, thư mục "Anh trang 1") */
var META = {};
var IDX = []; /* song song với DOCS */

function buildIndex(docs) {
  IDX = docs.map(function (d) {
    var soNum = String(d.so_hieu || '').split('/')[0].replace(/\D/g, '');
    var hs = hsDigits(d.ma_hs);
    var nProd = norm(d.mat_hang);
    var nSum = norm(d.trich_yeu);
    var words = {};
    (nProd + ' ' + nSum).split(' ').forEach(function (w) {
      if (w.length >= 3) words[w] = true;
    });
    return {
      soNum: soNum,
      nSo: norm(d.so_hieu),
      hs: hs,
      chapter: hs ? hs.slice(0, 2) : '',
      nProd: nProd,
      nSum: nSum,
      nText: norm(d.post_text),
      words: Object.keys(words),
      dateSort: parseDate(d.ngay),
      year: (function () {
        var m = /(\d{4})\s*$/.exec(String(d.ngay || ''));
        return m ? m[1] : '';
      })()
    };
  });
}

function passesFilters(i, f) {
  var d = DOCS[i], x = IDX[i];
  if (f.loai && d.loai !== f.loai) return false;
  if (f.chapter && x.chapter !== f.chapter) return false;
  if (f.year && x.year !== f.year) return false;
  return true;
}

function fuzzyWord(token, words) {
  var best = null, bestD = 99;
  var maxD = token.length >= 7 ? 2 : 1;
  for (var i = 0; i < words.length; i++) {
    var w = words[i];
    if (Math.abs(w.length - token.length) > maxD) continue;
    var dist = lev(token, w, maxD);
    if (dist < bestD) { bestD = dist; best = w; }
    if (bestD === 1 && token.length < 7) break;
  }
  return bestD <= maxD ? { word: best, dist: bestD } : null;
}

/* ================= Tìm kiếm thông minh ================= */
/* Trả về [{doc, score, reasons[]}] đã xếp hạng. */
function searchDocs(query, filters) {
  filters = filters || {};
  var q = norm(query);
  var tokens;
  if (/^[\d. ]+$/.test(String(query).trim()) && q.replace(/\D/g, '').length >= 2) {
    /* Chỉ gõ số/chấm (vd. "3504.00.00", "3504 00"): coi cả dãy số là MỘT
       token mã HS, không tách thành "3504", "00", "00". */
    tokens = [q.replace(/\D/g, '')];
  } else {
    tokens = q.split(' ').filter(function (t) {
      return t.length >= 2 || /^\d+$/.test(t);
    });
  }
  /* Mở rộng từ đồng nghĩa: cụm từ trong câu truy vấn kích hoạt thêm từ khóa. */
  var extra = [];
  Object.keys(SYN).forEach(function (key) {
    if (q.indexOf(key) !== -1) {
      SYN[key].forEach(function (v) { extra.push(v); });
    }
  });

  var out = [];
  for (var i = 0; i < DOCS.length; i++) {
    if (!passesFilters(i, filters)) continue;
    var d = DOCS[i], x = IDX[i];
    if (tokens.length === 0) {
      out.push({ doc: d, score: 0, reasons: [], i: i });
      continue;
    }
    var score = 0, reasons = [], ok = true;
    for (var t = 0; t < tokens.length; t++) {
      var tok = tokens[t], matched = false;
      var isDigits = /^\d+$/.test(tok);
      /* 1. Số hiệu */
      if (isDigits) {
        if (x.soNum === tok) { score += 120; reasons.push('Số hiệu ' + d.so_hieu); matched = true; }
        else if (x.soNum && x.soNum.indexOf(tok) === 0) { score += 90; reasons.push('Số hiệu ' + d.so_hieu); matched = true; }
        else if (x.nSo.indexOf(tok) !== -1) { score += 60; reasons.push('Số hiệu'); matched = true; }
      } else if (x.nSo.indexOf(tok) !== -1) {
        score += 70; reasons.push('Số hiệu'); matched = true;
      }
      /* 2. Mã HS (bỏ dấu chấm để so sánh) — chỉ cho token số */
      if (isDigits && x.hs) {
        if (x.hs === tok) { score += 130; reasons.push('Mã HS ' + d.ma_hs); matched = true; }
        else if (x.hs.indexOf(tok) === 0) { score += 100; reasons.push('Mã HS ' + d.ma_hs); matched = true; }
      }
      /* 3–5. Chỉ cho token chữ: token số không khớp lung tung vào
         tên hàng (ví dụ "58" khớp "58%" trong mô tả) hay fuzzy. */
      if (!isDigits) {
        /* 3. Tên hàng */
        if (x.nProd.indexOf(tok) !== -1) {
          score += 45; reasons.push('Tên hàng'); matched = true;
        } else if (tok.length >= 4) {
          var fz = fuzzyWord(tok, x.words);
          if (fz) {
            score += 18; reasons.push('Gần giống “' + tok + '”'); matched = true;
          }
        }
        /* 4. Tóm tắt */
        if (x.nSum.indexOf(tok) !== -1) {
          score += 25; reasons.push('Tóm tắt'); matched = true;
        }
        /* 5. Từ đồng nghĩa */
        if (!matched) {
          for (var e = 0; e < extra.length; e++) {
            if (x.nProd.indexOf(extra[e]) !== -1 || x.nSum.indexOf(extra[e]) !== -1) {
              score += 20; reasons.push('Liên quan'); matched = true; break;
            }
          }
        }
      }
      if (!matched) { ok = false; break; }
    }
    /* Khớp nguyên cụm trong tên hàng/tóm tắt (vd. "vai sofa" khớp cả cụm
       thì hơn khớp rời 2 từ ở 2 chỗ). */
    if (q.length >= 5) {
      if (x.nProd.indexOf(q) !== -1) { score += 30; reasons.push('Cụm từ khớp'); }
      else if (x.nSum.indexOf(q) !== -1) { score += 12; reasons.push('Cụm từ khớp'); }
    }
    /* Định danh tuyệt đối: gõ đúng một số hiệu / mã HS đầy đủ thì văn bản
       đó luôn đứng đầu, bất kể các token khác. */
    if (tokens.length === 1 && /^\d+$/.test(tokens[0])) {
      if (x.soNum === tokens[0] || x.hs === tokens[0]) score += 1000;
    }
    /* Tín hiệu hành vi trên chính máy người dùng (localStorage): văn bản
       đã mở sau khi tìm thì tăng hạng nhẹ, tối đa +5. */
    var cb = clickBoost(i);
    if (cb) score += cb;
    if (ok) out.push({ doc: d, score: score, reasons: reasons, i: i });
  }
  out.sort(function (a, b) {
    if (b.score !== a.score) return b.score - a.score;
    return IDX[b.i].dateSort - IDX[a.i].dateSort;
  });
  return out;
}

/* ================= Gần đây & lượt mở (chỉ trên máy này) ================= */
/* Lưu trong localStorage, không gửi đi đâu — giữ đúng cam kết không theo dõi. */
function lsGet(key) {
  try { if (typeof localStorage === 'undefined') return null; return localStorage.getItem(key); }
  catch (e) { return null; }
}
function lsSet(key, val) {
  try { if (typeof localStorage === 'undefined') return; localStorage.setItem(key, val); }
  catch (e) { /* bộ nhớ đầy / chế độ riêng tư: bỏ qua */ }
}
var _recents = null, _clicks = null;
function recents() {
  if (_recents) return _recents;
  try { _recents = JSON.parse(lsGet('vbxnk_recents_v1') || '[]'); } catch (e) { _recents = []; }
  if (!Array.isArray(_recents)) _recents = [];
  return _recents;
}
function recordRecent(q) {
  var s = String(q || '').trim();
  if (s.length < 2) return;
  var r = recents().filter(function (x) { return norm(x) !== norm(s); });
  r.unshift(s);
  _recents = r.slice(0, 5);
  lsSet('vbxnk_recents_v1', JSON.stringify(_recents));
}
function clickMap() {
  if (_clicks) return _clicks;
  try { _clicks = JSON.parse(lsGet('vbxnk_clicks_v1') || '{}'); } catch (e) { _clicks = {}; }
  return _clicks;
}
function recordClick(ma) {
  var m = clickMap();
  m[String(ma)] = Math.min((m[String(ma)] || 0) + 1, 20);
  lsSet('vbxnk_clicks_v1', JSON.stringify(m));
}
function clickBoost(i) {
  var m = clickMap();
  var c = m[String(DOCS[i].ma)] || 0;
  return Math.min(c, 5);
}

/* ================= Từ vựng kho & "Ý bạn là" ================= */
/* Từ điển ở đây là từ vựng của chính kho văn bản (từ trong tên hàng +
   tóm tắt), kèm tần suất xuất hiện — kiểu Peter Norvig: từ gõ sai không
   có trong từ vựng nhưng gần 1 từ trong kho (sửa 1–2 ký tự) thì gần như
   chắc chắn là lỗi gõ của từ đó. Chạy trên chuỗi đã chuẩn hóa không dấu. */
var _vocab = null;
function buildVocab() {
  _vocab = {};
  IDX.forEach(function (x) {
    x.words.forEach(function (w) { _vocab[w] = (_vocab[w] || 0) + 1; });
  });
  return _vocab;
}
function vocab() { return _vocab || buildVocab(); }

var _ALPHA = 'abcdefghijklmnopqrstuvwxyz';
function edits1(word) {
  var out = {}, i, c;
  for (i = 0; i < word.length; i++) out[word.slice(0, i) + word.slice(i + 1)] = true;
  for (i = 0; i < word.length - 1; i++)
    out[word.slice(0, i) + word[i + 1] + word[i] + word.slice(i + 2)] = true;
  for (i = 0; i < word.length; i++)
    for (c = 0; c < _ALPHA.length; c++)
      out[word.slice(0, i) + _ALPHA[c] + word.slice(i + 1)] = true;
  for (i = 0; i <= word.length; i++)
    for (c = 0; c < _ALPHA.length; c++)
      out[word.slice(0, i) + _ALPHA[c] + word.slice(i)] = true;
  return Object.keys(out);
}
function correctToken(tok, v) {
  /* Bỏ qua token chứa chữ số (mã HS, số hiệu, mã thép như sus304):
     "sửa" chúng dễ đổi sang một mã khác hẳn (sus304 → sus201). */
  if (v[tok] || tok.length < 3 || /\d/.test(tok)) return null;
  var best = null, bestF = 0, i, j;
  var c1 = edits1(tok);
  for (i = 0; i < c1.length; i++) {
    if (v[c1[i]] && v[c1[i]] > bestF) { bestF = v[c1[i]]; best = c1[i]; }
  }
  if (best) return best;
  if (tok.length >= 6) { /* thử 2 lần sửa, chỉ qua nhánh xóa (lỗi thiếu chữ) */
    for (i = 0; i < tok.length; i++) {
      var del = tok.slice(0, i) + tok.slice(i + 1);
      var c2 = edits1(del);
      for (j = 0; j < c2.length; j++) {
        if (v[c2[j]] && v[c2[j]] > bestF) { bestF = v[c2[j]]; best = c2[j]; }
      }
      if (bestF >= 3) break; /* đủ tin thì dừng sớm */
    }
  }
  return best;
}
/* Trả về truy vấn đã sửa, hoặc null nếu không có gợi ý sửa đáng tin. */
function didYouMean(query) {
  var v = vocab();
  var toks = norm(query).split(' ').filter(Boolean);
  if (!toks.length) return null;
  var fixed = toks.map(function (t) { return correctToken(t, v) || t; });
  var out = fixed.join(' ');
  return out !== norm(query) ? out : null;
}

/* Nới truy vấn khi 0 kết quả: bỏ token ít gặp nhất trong kho rồi tìm lại. */
function relaxedSearch(q) {
  var toks = norm(q).split(' ').filter(Boolean);
  if (toks.length < 2) return null;
  var v = vocab();
  var drop = null, dropF = Infinity;
  toks.forEach(function (t) {
    var f = /^\d+$/.test(t) ? Infinity : (v[t] || 0);
    if (f < dropF) { dropF = f; drop = t; }
  });
  if (!drop || dropF === Infinity) return null;
  var rest = toks.filter(function (t) { return t !== drop; }).join(' ');
  var results = searchDocs(rest, { loai: state.loai, chapter: state.chapter, year: state.year });
  return results.length ? { dropped: drop, results: results } : null;
}

/* "Tìm kiếm liên quan" kiểu Shopee: cụm từ trong tên hàng của các kết quả
   đầu, chứa ít nhất 1 từ truy vấn nhưng khác truy vấn — vd. gõ "vải" thì
   gợi ý "vải sofa", "vải dệt thoi". */
function relatedSearches(results, tokens) {
  if (!tokens.length || results.length < 2) return [];
  if (tokens.every(function (t) { return /^\d+$/.test(t); })) return [];
  var counts = {};
  results.slice(0, 10).forEach(function (r) {
    var x = IDX[r.i];
    if (!x) return;
    var pw = x.nProd.split(' ').filter(function (w) { return w.length >= 3; });
    for (var j = 0; j + 1 < pw.length; j++) {
      var bg = pw[j] + ' ' + pw[j + 1];
      if (bg === norm(state.query)) continue;
      var hit = false;
      tokens.forEach(function (t) { if (bg.indexOf(t) !== -1) hit = true; });
      if (hit) counts[bg] = (counts[bg] || 0) + 1;
    }
  });
  return Object.keys(counts).sort(function (a, b) { return counts[b] - counts[a]; }).slice(0, 5);
}

function chapterCount(ch) {
  var n = 0;
  IDX.forEach(function (x) { if (x.chapter === ch) n++; });
  return n;
}

/* Gợi ý khi đang gõ: nhóm theo loại (như Google/Shopee) — tìm gần đây,
   số hiệu (mở thẳng văn bản), mã HS, chương HS, cụm từ mặt hàng.
   Mọi gợi ý đều dẫn tới ít nhất 1 văn bản, không bao giờ gợi ý 0 kết quả. */
var _suggestPool = null;
function suggestPool() {
  if (_suggestPool) return _suggestPool;
  var so = {}, hs = {}, words = {}, phrases = {}, chapters = {};
  DOCS.forEach(function (d, i) {
    so[d.so_hieu] = d.ma;
    if (d.ma_hs) hs[d.ma_hs] = (hs[d.ma_hs] || 0) + 1;
    var ch = IDX[i].chapter;
    if (ch) chapters[ch] = (chapters[ch] || 0) + 1;
    var pw = IDX[i].nProd.split(' ').filter(function (w) { return w.length >= 3; });
    pw.forEach(function (w) { words[w] = (words[w] || 0) + 1; });
    for (var k = 0; k + 1 < pw.length; k++) {
      var bg = pw[k] + ' ' + pw[k + 1];
      phrases[bg] = (phrases[bg] || 0) + 1;
    }
  });
  _suggestPool = {
    so: Object.keys(so).sort(),
    soMa: so,
    hs: Object.keys(hs).sort(),
    hsCount: hs,
    chapters: chapters,
    /* Giữ toàn bộ từ/cụm (đã xếp theo tần suất) để gợi ý tiền tố không bị
       cắt mất cụm ít gặp nhưng đúng ý người gõ (vd. "vai sofa" chỉ 3 bài). */
    words: Object.keys(words).sort(function (a, b) { return words[b] - words[a]; }),
    wordCount: words,
    phrases: Object.keys(phrases).sort(function (a, b) { return phrases[b] - phrases[a]; }),
    phraseCount: phrases
  };
  return _suggestPool;
}

/* Mỗi gợi ý: {text, kind, group, action, ma?, chapter?, count?}.
   action: 'search' (chạy tìm kiếm) | 'open' (mở thẳng văn bản) | 'chapter'. */
function suggest(query) {
  var q = norm(query);
  var pool = suggestPool(), out = [];
  /* Giới hạn mỗi nhóm để không nhóm nào chiếm hết dropdown (vd. gõ "35"
     mà 8 mục toàn số hiệu chứa "35" thì mã HS/chương HS không còn chỗ). */
  var caps = q ? { 'Tìm gần đây': 2, 'Văn bản': 3, 'Mã HS': 3, 'Chương HS': 1, 'Mặt hàng': 4, 'Tìm nhiều': 6 }
               : { 'Tìm gần đây': 5, 'Tìm nhiều': 3 };
  var counts = {};
  function push(text, kind, group, action, extra) {
    if (out.length >= 8) return;
    if ((counts[group] || 0) >= (caps[group] || 8)) return;
    counts[group] = (counts[group] || 0) + 1;
    var it = { text: text, kind: kind, group: group, action: action || 'search' };
    if (extra) for (var k in extra) it[k] = extra[k];
    out.push(it);
  }
  /* Ô trống: hiện "Tìm nhiều" (cụm phổ biến trong kho) + tìm gần đây. */
  if (!q) {
    recents().forEach(function (r) { push(r, 'Tìm gần đây', 'Tìm gần đây'); });
    pool.phrases.slice(0, 6).forEach(function (p) {
      push(p, 'Mặt hàng · ' + (pool.phraseCount[p] || 0) + ' văn bản', 'Tìm nhiều');
    });
    return out;
  }
  /* Tìm gần đây khớp tiền tố — luôn đứng đầu, như Google. */
  recents().forEach(function (r) {
    if (norm(r).indexOf(q) === 0) push(r, 'Tìm gần đây', 'Tìm gần đây');
  });
  if (q.length < 2) return out;
  var digits = q.replace(/\D/g, '');
  /* Số hiệu: khớp đầu số hiệu trước, rồi mới tới khớp ở giữa — khớp là
     mở thẳng văn bản. */
  pool.so.forEach(function (s) {
    if (norm(s).indexOf(q) === 0)
      push(s, 'Văn bản', 'Văn bản', 'open', { ma: pool.soMa[s] });
  });
  pool.so.forEach(function (s) {
    if (norm(s).indexOf(q) > 0)
      push(s, 'Văn bản', 'Văn bản', 'open', { ma: pool.soMa[s] });
  });
  /* Mã HS theo tiền tố + chương HS khi gõ đúng 2 chữ số của chương. */
  if (digits.length >= 2) {
    pool.hs.forEach(function (s) {
      if (out.length < 8 && hsDigits(s).indexOf(digits) === 0)
        push(s, 'Mã HS · ' + (pool.hsCount[s] || 0) + ' văn bản', 'Mã HS');
    });
    if (digits.length === 2 && pool.chapters[digits]) {
      push('Chương ' + digits, 'Chương HS · ' + pool.chapters[digits] + ' văn bản',
        'Chương HS', 'chapter', { chapter: digits });
    }
  }
  /* Cụm từ mặt hàng (tiền tố) rồi từ đơn. */
  pool.phrases.forEach(function (p) {
    if (out.length < 8 && p.indexOf(q) === 0)
      push(p, 'Mặt hàng · ' + (pool.phraseCount[p] || 0) + ' văn bản', 'Mặt hàng');
  });
  pool.words.forEach(function (w) {
    if (out.length < 8 && w.indexOf(q) === 0) push(w, 'Tên hàng', 'Mặt hàng');
  });
  /* Hết gợi ý tiền tố mà gõ sai 1–2 ký tự: gợi ý mờ (fuzzy) tối đa 2 mục. */
  if (!out.length && q.length >= 4) {
    var v = vocab(), cands = [], md = q.length >= 7 ? 2 : 1;
    Object.keys(v).forEach(function (w) {
      if (Math.abs(w.length - q.length) <= md && lev(q, w, md) <= md) cands.push(w);
    });
    cands.sort(function (a, b) { return v[b] - v[a]; }).slice(0, 2).forEach(function (w) {
      push(w, 'Gần giống', 'Mặt hàng');
    });
  }
  return out;
}

/* Gợi ý khi gõ trong ô hỏi: hoàn thiện cụm đang gõ (tên hàng, chất liệu,
   công dụng) từ chính tên hàng trong kho, giữ nguyên phần đầu câu đã gõ.
   Gõ không dấu vẫn ra cụm có dấu; gõ sai nhẹ thì gợi ý từ gần giống. */
var ASK_START_STOP = ('của và với các những là thì có được này đó khi nếu hoặc hay như một mới ' +
  'đã chưa mã model nhãn hiệu').split(' ');
var ASK_END_EXTRA = ('dùng để bằng từ làm pha chứa gồm sử dành dạng mã model nhãn hiệu ' +
  'công dụng tên thương mại').split(' ');
var ASK_USE_START = ['dùng', 'sử', 'dành', 'để'];
var ASK_KIND = { goods: 'Tên hàng', material: 'Chất liệu', use: 'Công dụng' };
var _askPool = null;
function askPool() {
  if (_askPool) return _askPool;
  var map = {}, byFirst = {}, pairs = {}, next = {};
  var mats = {};
  NL_MATERIAL.concat(NL_MATERIAL_PHRASES).forEach(function (m) { mats[viKey(m).split(' ')[0]] = 1; });
  function endOk(w) { return NL_STOP.indexOf(w) === -1 && ASK_END_EXTRA.indexOf(w) === -1; }
  DOCS.forEach(function (d) {
    var src = d.mat_hang || d.trich_yeu || '';
    String(src).split(/[,;:()\[\]\/.\n"“”]+/).forEach(function (clause) {
      var ws = viKey(clause).split(' ').filter(Boolean);
      for (var i = 0; i < ws.length; i++) {
        if (i) {
          var pa = ws[i - 1], pb = ws[i], nx = next[pa] = next[pa] || { t: 0, w: {} };
          pairs[norm(pa) + ' ' + norm(pb)] = 1; nx.t++; nx.w[pb] = (nx.w[pb] || 0) + 1;
        }
        if (/\d/.test(ws[i]) || ASK_START_STOP.indexOf(ws[i]) !== -1) continue;
        for (var L = 1; L <= 4 && i + L <= ws.length; L++) {
          var w = ws[i + L - 1];
          if (/\d/.test(w) || w.length > 20) break;
          if (!endOk(w) || (L === 1 && w.length < 2)) continue;
          var text = ws.slice(i, i + L).join(' '), key = norm(text), e = map[key];
          if (!e) {
            var f = key.split(' ')[0];
            e = map[key] = { key: key, len: L, forms: {}, docs: {}, n: 0,
              kind: ASK_USE_START.indexOf(ws[i]) !== -1 && L > 1 ? 'use' : mats[ws[i]] ? 'material' : 'goods' };
            (byFirst[f] = byFirst[f] || []).push(e);
          }
          e.forms[text] = (e.forms[text] || 0) + 1;
          if (!e.docs[d.ma]) { e.docs[d.ma] = 1; e.n++; }
        }
      }
    });
  });
  Object.keys(map).forEach(function (k) {
    var e = map[k], best = '', bn = 0;
    Object.keys(e.forms).forEach(function (t) { if (e.forms[t] > bn) { bn = e.forms[t]; best = t; } });
    e.text = best; if (e.len === 1) e.spell = e.forms; delete e.forms; delete e.docs;
    /* Cụm dừng giữa chừng ("phân bón hữu", "cảm biến vị") không đáng gợi ý: từ cuối
       gần như luôn đi kèm một từ sau. */
    var nx = next[best.split(' ').pop()], top = 0, topW = '';
    if (nx) Object.keys(nx.w).forEach(function (w) { if (nx.w[w] > top) { top = nx.w[w]; topW = w; } });
    e.dangling = e.len < 4 && !!nx && nx.t >= 3 && top / nx.t >= 0.75 && endOk(topW);
  });
  /* Số văn bản dùng một cách gọi bất kỳ trong mỗi nhóm đồng nghĩa (cụm dài hơn 4 từ cũng tính). */
  var texts = DOCS.map(function (d) { return ' ' + norm((d.mat_hang || '') + ' ' + (d.trich_yeu || '')) + ' '; });
  var synN = NL_SYN_GROUPS.map(function (g) {
    var keys = g.map(function (t) { return ' ' + norm(t) + ' '; });
    return texts.filter(function (x) { return keys.some(function (k) { return x.indexOf(k) !== -1; }); }).length;
  });
  _askPool = { map: map, byFirst: byFirst, firsts: Object.keys(byFirst), pairs: pairs, synN: synN };
  return _askPool;
}

/* Mỗi gợi ý: {text, html, kind, action: 'ask' | 'open', ma?}. */
function askSuggest(text) {
  var raw = String(text == null ? '' : text);
  var words = raw.trim().split(/\s+/).filter(Boolean);
  if (!words.length || norm(raw).length < 2) return [];
  var endsSpace = /\s$/.test(raw), pool = askPool(), sp = suggestPool();
  var out = [], seen = {};
  function push(it) {
    var k = it.ma ? 'ma:' + it.ma : norm(it.text);
    if (out.length >= 8 || seen[k]) return;
    seen[k] = 1; out.push(it);
  }
  var lastRaw = words[words.length - 1];
  var headAll = words.slice(0, -1).join(' ');
  /* Số hiệu văn bản (mở thẳng bài) và mã HS theo tiền tố. */
  if (/\d/.test(lastRaw) && !endsSpace) {
    var lr = norm(lastRaw), dg = lastRaw.replace(/\D/g, '');
    if (words.filter(function (w) { return norm(w); }).length === 1) {
      /* Theo từng văn bản: cùng số hiệu ở các năm khác nhau vẫn hiện đủ. */
      DOCS.filter(function (d) { return d.so_hieu && norm(d.so_hieu).indexOf(lr) === 0; })
        .sort(function (a, b) {
          var da = (a.ngay || '').split('/').reverse().join(''), db = (b.ngay || '').split('/').reverse().join('');
          return a.so_hieu < b.so_hieu ? -1 : a.so_hieu > b.so_hieu ? 1 : da < db ? 1 : -1;
        })
        .slice(0, 4).forEach(function (d) {
          push({ text: d.so_hieu, html: '<b>' + esc(d.so_hieu) + '</b>' +
              '<span class="sugg-sub">' + esc(shortText(d.trich_yeu || d.mat_hang || '', 70)) + '</span>',
            kind: (d.ngay ? d.ngay + ' · ' : '') + 'mở bài', action: 'open', ma: d.ma });
        });
    }
    if (dg.length >= 2 && /^[\d.]+$/.test(lastRaw)) {
      sp.hs.filter(function (h) { return hsDigits(h).indexOf(dg) === 0; })
        .sort(function (a, b) { return (sp.hsCount[b] || 0) - (sp.hsCount[a] || 0) || (a < b ? -1 : 1); })
        .slice(0, 5).forEach(function (h) {
          push({ text: (headAll ? headAll + ' ' : '') + h,
            html: (headAll ? esc(headAll) + ' ' : '') + '<b>' + esc(h) + '</b>',
            kind: 'Mã HS · ' + (sp.hsCount[h] || 0) + ' văn bản', action: 'ask' });
        });
    }
    return out;
  }
  function phraseMatches(ws, fuzzy) {
    var levels = [];
    for (var k = Math.min(4, ws.length); k >= 1; k--) {
      var tailWs = ws.slice(ws.length - k), tail = norm(tailWs.join(' '));
      /* Ký hiệu rời ("-", "%") giữ nguyên ở phần đầu câu, không ghép vào cụm cần khớp. */
      if (tailWs.some(function (w) { return !norm(w); })) continue;
      if (!tail || (k === 1 && tail.length < 2 && !endsSpace)) continue;
      var typedWs = tailWs.map(viKey), typed = typedWs.join(' '), first = tail.split(' ')[0], lists;
      if (k === 1 && !endsSpace) {
        lists = pool.firsts.filter(function (f) { return f.indexOf(tail) === 0; })
          .map(function (f) { return pool.byFirst[f]; });
      } else lists = [pool.byFirst[first] || []];
      var head = ws.slice(0, ws.length - k).join(' ');
      var prev = head ? norm(ws[ws.length - k - 1]) : '';
      var cands = [];
      lists.forEach(function (list) {
        list.forEach(function (e) {
          if (endsSpace ? e.key.indexOf(tail + ' ') !== 0 : e.key.indexOf(tail) !== 0) return;
          if (e.len > k + 3) return;
          /* Cụm đã gõ đủ: chỉ gợi ý khi thêm được dấu ("vai det kim" → "vải dệt kim"). */
          if (!fuzzy && e.key === tail && e.text === typed) return;
          if (e.dangling) return;
          /* Từ đã gõ có dấu thì phải đúng dấu ("dùng" không gợi "dụng", "áp" không gợi "apple"). */
          var pw = e.text.split(' ');
          for (var j = 0; j < typedWs.length; j++) {
            var tw = typedWs[j], full = j < typedWs.length - 1 || endsSpace;
            if (tw === norm(tw)) continue;
            if (full ? pw[j] !== tw : pw[j].indexOf(tw) !== 0) return;
          }
          /* Nối vào phần đầu câu phải thành cụm có thật trong kho ("ống bằng thép", không "ống bằng thực phẩm"). */
          if (prev && !pool.pairs[prev + ' ' + e.key.split(' ')[0]] &&
              !(k === 1 && e.len === 1 && (fuzzy || tail.length >= 3))) return;
          var keep = Math.min(k, pw.length), lastW = pw[keep - 1], tw0 = typedWs[keep - 1] || '';
          var typedPart = esc(pw.slice(0, keep).join(' '));
          if (!endsSpace && keep === typedWs.length && lastW.length > tw0.length &&
              norm(lastW).indexOf(norm(tw0)) === 0) {
            typedPart = esc(pw.slice(0, keep - 1).concat([lastW.slice(0, tw0.length)]).join(' ')) +
              '<b>' + esc(lastW.slice(tw0.length)) + '</b>';
          }
          cands.push({ score: Math.log(1 + e.n) * 12 - Math.abs(e.len - k - 1) * 6 + (e.kind === 'goods' ? 2 : 0),
            text: (head ? head + ' ' : '') + e.text,
            html: (head ? esc(head) + ' ' : '') + typedPart +
              (pw.length > keep ? ' <b>' + esc(pw.slice(keep).join(' ')) + '</b>' : ''),
            kind: ASK_KIND[e.kind] + ' · ' + e.n + ' văn bản' + (fuzzy ? ' · gần giống' : ''),
            action: 'ask' });
        });
      });
      /* Cách gọi khác trong nhóm đồng nghĩa ("thuc pham chuc" → "thực phẩm chức năng",
         "thực phẩm bảo vệ sức khỏe"), chỉ khi trong kho có văn bản dùng một trong các cách gọi. */
      if (!fuzzy && tail.length >= (k === 1 ? 4 : 3)) NL_SYN_GROUPS.forEach(function (g, gi) {
        var n = pool.synN[gi];
        if (!n) return;
        g.forEach(function (t) {
          var nt = norm(t);
          if (nt.indexOf(tail) !== 0 || nt === tail) return;
          if (!hasDia(t) && g.some(function (x) { return x !== t && norm(x) === nt; })) return;
          /* Cách gọi đang gõ không có trong kho: gợi ý thêm cách gọi mà văn bản dùng. */
          var alts = pool.map[nt] ? [t] : g.filter(function (x) { return x !== t && pool.map[norm(x)]; });
          if (!alts.length) alts = [t];
          alts.forEach(function (x) {
            var e = pool.map[norm(x)];
            cands.push({ score: Math.log(1 + n) * 12 - 3, text: (head ? head + ' ' : '') + x,
              html: (head ? esc(head) + ' ' : '') + '<b>' + esc(x) + '</b>',
              kind: e ? ASK_KIND[e.kind] + ' · ' + e.n + ' văn bản' : 'Cách gọi khác · ' + n + ' văn bản',
              action: 'ask' });
          });
        });
      });
      cands.sort(function (a, b) { return b.score - a.score; });
      if (cands.length) levels.push({ k: k, c: cands });
    }
    /* Ưu tiên khớp dài nhất với phần đang gõ; chỉ lấy thêm mức kế tiếp khi còn ít gợi ý. */
    var res = levels[0] ? levels[0].c : [];
    if (res.length < 4 && levels[1] && levels[1].k === levels[0].k - 1) res = res.concat(levels[1].c);
    return res.map(function (c) { c.html = c.html.replace(/<\/b> <b>/g, ' '); return c; });
  }
  phraseMatches(words, false).forEach(push);
  /* Không có cụm nào khớp tiền tố: sửa từ cuối theo từ gần giống trong kho. */
  var nl = norm(lastRaw);
  /* Từ cuối có trong kho và (nối được với từ trước hoặc là từ phổ biến): không cần sửa. */
  var prevNl = words.length > 1 ? norm(words[words.length - 2]) : '';
  /* Từ cuối có đúng cách viết này trong kho ("cápb" không tính là "CAPB"). */
  var vlast = viKey(lastRaw), single0 = pool.map[nl];
  var typedKnown = !!single0 && (vlast === nl || !!(single0.spell && single0.spell[vlast]));
  var known = typedKnown && (!prevNl || pool.pairs[prevNl + ' ' + nl] || pool.map[nl].n >= 5);
  if (!out.length && nl.length >= 3 && !/\d/.test(nl) && !known) {
    var md = nl.length >= 7 ? 2 : 1, fixes = [];
    /* Từ cuối đã gõ có dấu thì so cả dấu ("suất" không thành "sữa"). */
    var vl = viKey(lastRaw), useDia = vl !== nl;
    /* Chỉ sai dấu ("áp lức"): sửa thành cách viết có dấu trong kho ("áp lực"), không đổi sang từ khác. */
    var accentOnly = !!single0 && !typedKnown && useDia &&
      Object.keys(single0.spell || {}).some(hasDia);
    if (accentOnly) {
      var sp1 = single0.spell;
      Object.keys(sp1).filter(hasDia).sort(function (a, b) { return sp1[b] - sp1[a]; })
        .slice(0, 3).forEach(function (t) {
          phraseMatches(words.slice(0, -1).concat([t]), true).slice(0, 3).forEach(push);
        });
    }
    /* Không cách viết có dấu nào khớp ("nguyên kiệu"): sửa lỗi gõ như bình thường. */
    if (!out.length) pool.firsts.forEach(function (f) {
      var single = pool.map[f];
      if (!single) return;
      var a = useDia ? vl : nl, b = useDia ? single.text : f;
      var d = lev(a, b, md);
      /* Từ đã có trong kho chỉ sửa theo cả từ ("tròn" không thành "trọng"). */
      if (d > md && !endsSpace && !typedKnown && a.length >= 4 && b.length > a.length &&
          lev(a, b.slice(0, a.length), 1) <= 1) d = 1;
      /* Từ đã có trong kho chỉ được sửa thành cụm có thật với từ trước ("vải diệt" → "vải dệt"; "thép tròn" giữ nguyên). */
      if (typedKnown && prevNl && !pool.pairs[prevNl + ' ' + f]) return;
      if (d <= md && f !== nl) fixes.push(single);
    });
    fixes.sort(function (a, b) { return b.n - a.n; }).slice(0, 3).forEach(function (e) {
      phraseMatches(words.slice(0, -1).concat([e.text]), true).slice(0, 3).forEach(push);
    });
  }
  /* Vẫn chưa có gợi ý: tìm tên hàng chứa đủ các từ đã gõ, không cần liền nhau
     ("thép tròn" → "thép tròn trơn" từ "Thép không hợp kim dạng que, tròn trơn"). */
  if (!out.length) askCooccur(words, endsSpace).forEach(push);
  return out;
}
var _askToks = null;
function askCooccur(words, endsSpace) {
  var ws = words.filter(function (w) { return norm(w); });
  if (ws.length < 2) return [];
  var heads = ws.slice(0, -1).map(viKey), last = viKey(ws[ws.length - 1]);
  if (!endsSpace && norm(last).length < 2) return [];
  if (!_askToks) _askToks = DOCS.map(function (d) {
    var toks = [];
    String(d.mat_hang || d.trich_yeu || '').split(/[,;:()\[\]\/\.\n"“”]+/).forEach(function (cl, ci) {
      viKey(cl).split(' ').filter(Boolean).forEach(function (w) { toks.push({ w: w, n: norm(w), c: ci }); });
    });
    return toks;
  });
  function same(tw, t, prefix) {
    var a = hasDia(tw) ? t.w : t.n, b = hasDia(tw) ? tw : norm(tw);
    return prefix ? a.indexOf(b) === 0 : a === b;
  }
  function endOk(w) { return NL_STOP.indexOf(w) === -1 && ASK_END_EXTRA.indexOf(w) === -1 && !/\d/.test(w); }
  var headNs = heads.map(norm), found = {};
  _askToks.forEach(function (toks) {
    if (!heads.every(function (hw) { return toks.some(function (t) { return same(hw, t, false); }); })) return;
    var seenDoc = {};
    toks.forEach(function (t, i) {
      if (headNs.indexOf(t.n) !== -1 || !same(last, t, !endsSpace)) return;
      var tail = [t.w];
      for (var j = i + 1; j < toks.length && tail.length < (endsSpace ? 2 : 2) && toks[j].c === t.c; j++) {
        if (!endOk(toks[j].w) || toks[j].w.length > 20) break;
        tail.push(toks[j].w);
      }
      while (tail.length && !endOk(tail[tail.length - 1])) tail.pop();
      if (!tail.length || (endsSpace && tail.length < 2)) return;
      var key = norm(tail.join(' '));
      if (seenDoc[key]) return;
      seenDoc[key] = 1;
      var f = found[key] = found[key] || { tail: tail, n: 0 };
      f.n++;
    });
  });
  var headRaw = ws.slice(0, endsSpace ? ws.length : -1).join(' ');
  return Object.keys(found).map(function (k) { return found[k]; })
    .sort(function (a, b) { return b.n - a.n || a.tail.length - b.tail.length; })
    .slice(0, 4).map(function (f) {
      var rest = endsSpace ? f.tail.slice(1) : f.tail, typedN = endsSpace ? 0 : norm(last).length;
      var first = rest[0], html = esc(headRaw) + ' ';
      if (!endsSpace) html += esc(first.slice(0, typedN)) + '<b>' + esc(first.slice(typedN) + (rest.length > 1 ? ' ' + rest.slice(1).join(' ') : '')) + '</b>';
      else html += '<b>' + esc(rest.join(' ')) + '</b>';
      return { text: headRaw + ' ' + rest.join(' '), html: html,
        kind: 'Tên hàng · ' + f.n + ' văn bản', action: 'ask' };
    });
}

/* ================= Tách nội dung bài ================= */

function parseDocDetail(doc) {
  var pt = doc.post_text || '';
  var sec1 = doc.mat_hang || doc.trich_yeu || '—';
  var sec2 = doc.trich_yeu || '—';
  var m2 = /2\.\s*Tóm tắt mô tả:\s*([\s\S]*?)(?=\n3\.|\n📌|\n🔗|#HaiQuan|$)/.exec(pt);
  if (m2 && m2[1].trim()) sec2 = m2[1].trim();
  var sec3 = doc.ma_hs ? ('mã số ' + doc.ma_hs) : '—';
  var m3 = /3\.\s*Kết quả:\s*([\s\S]*?)(?=\n📌|\n🔗|\n#|$)/.exec(pt);
  if (m3 && m3[1].trim()) sec3 = m3[1].trim().replace(/\n+/g, ' ');
  var other = [];
  var mo = /📌 Thông tin khác:\s*([\s\S]*?)(?=\n🔗|\n#|$)/.exec(pt);
  if (mo) {
    mo[1].split('\n').forEach(function (line) {
      var t = line.replace(/^[•\-\s]+/, '').trim();
      if (t) other.push(t);
    });
  }
  var coquan = (/Cơ quan:\s*([^\n]+)/.exec(pt) || [])[1] || '';
  var soKqpt = (/Số KQPT:\s*([^\n]+)/.exec(pt) || [])[1] || '';
  var don = (/Đơn đề nghị số ([^\n]+)/.exec(pt) || [])[1] || '';
  return { sec1: sec1, sec2: sec2, sec3: sec3, other: other,
           coquan: coquan.trim(), soKqpt: soKqpt.trim(), don: don.trim() };
}

function chapterOf(doc) {
  var hs = hsDigits(doc.ma_hs);
  return hs ? hs.slice(0, 2) : '';
}

function relatedDocs(doc) {
  var ch = chapterOf(doc);
  var same = [], sameLoai = [], rest = [];
  var heading = hsDigits(doc.ma_hs).slice(0, 4);
  DOCS.forEach(function (d) {
    if (d.ma === doc.ma) return;
    if (ch && chapterOf(d) === ch) {
      if (heading && hsDigits(d.ma_hs).slice(0, 4) === heading) same.push(d);
      else sameLoai.push(d);
    } else if (d.loai === doc.loai) rest.push(d);
  });
  function byDate(a, b) { return parseDate(b.ngay) - parseDate(a.ngay); }
  same.sort(byDate); sameLoai.sort(byDate); rest.sort(byDate);
  return same.concat(sameLoai, rest).slice(0, 5);
}

function drivePreviewUrl(id) {
  return 'https://drive.google.com/file/d/' + id + '/preview';
}
function driveViewUrl(id) {
  return 'https://drive.google.com/file/d/' + id + '/view';
}
function extractDriveId(input) {
  var s = String(input || '').trim();
  var m = /\/d\/([A-Za-z0-9_-]{10,})/.exec(s) || /[?&]id=([A-Za-z0-9_-]{10,})/.exec(s);
  if (m) return m[1];
  if (/^[A-Za-z0-9_-]{10,}$/.test(s)) return s;
  return '';
}

/* Highlight từ khóa (không phân biệt dấu) trong chuỗi gốc.
   Văn bản NFC: mỗi ký tự có dấu là 1 đơn vị mã, sau khi tách dấu
   độ dài chuỗi bằng độ dài gốc nên ánh xạ chỉ số 1-1. */
function highlight(text, tokens) {
  var raw = String(text == null ? '' : text);
  if (!tokens || !tokens.length) return esc(raw);
  var stripped = norm(raw);
  var marks = [];
  tokens.forEach(function (tok) {
    var t = norm(tok);
    if (t.length < 2) return;
    var from = 0, idx;
    while ((idx = stripped.indexOf(t, from)) !== -1) {
      marks.push([idx, idx + t.length]);
      from = idx + t.length;
    }
  });
  if (!marks.length) return esc(raw);
  marks.sort(function (a, b) { return a[0] - b[0]; });
  var merged = [marks[0]];
  for (var i = 1; i < marks.length; i++) {
    var last = merged[merged.length - 1];
    if (marks[i][0] <= last[1]) last[1] = Math.max(last[1], marks[i][1]);
    else merged.push(marks[i]);
  }
  var out = '', pos = 0;
  merged.forEach(function (pair) {
    out += esc(raw.slice(pos, pair[0])) + '<mark>' + esc(raw.slice(pair[0], pair[1])) + '</mark>';
    pos = pair[1];
  });
  return out + esc(raw.slice(pos));
}

/* ================= Hỏi bằng tiếng Việt tự nhiên ================= */
/* Chạy hoàn toàn trên trình duyệt: tách câu hỏi thành từ khóa mặt hàng /
   chất liệu / công dụng, mở rộng bằng từ đồng nghĩa, chấm điểm kiểu BM25
   với tên hàng, mô tả, kết quả phân loại và trích yếu của từng văn bản.
   Từ gõ có dấu được so đúng dấu ("tủ" khác "từ", "bông" khác "bóng");
   gõ không dấu thì so dạng không dấu như ô tìm từ khóa. */

/* Chữ thường NFC, bỏ dấu câu, đưa dấu kiểu cũ về kiểu mới (hoá → hóa,
   thuỷ → thủy) để hai cách gõ khớp nhau. */
function viKey(s) {
  return String(s == null ? '' : s).normalize('NFC').toLowerCase()
    .replace(/[^0-9a-z\u00c0-\u1ef9]+/g, ' ')
    .normalize('NFD')
    .replace(/(^|[^q])([ou])([aey])([\u0300\u0301\u0303\u0309\u0323])(?![a-z\u0300-\u036f])/g, '$1$2$4$3')
    .normalize('NFC')
    .replace(/\s+/g, ' ').trim();
}
function hasDia(s) { return norm(s) !== String(s).replace(/\s+/g, ' ').trim(); }

/* Từ chức năng bỏ qua (có dấu) và dạng không dấu an toàn để bỏ. */
var NL_STOP = ('tôi mình em anh chị bạn muốn cần hỏi tra cứu xin cho của và với các những ' +
  'một mấy là gì nào thì có không được nhập xuất khẩu vào về này đó kia ấy ạ nhé nhỉ ' +
  'à ơi vậy sao thế bao nhiêu mã số hs loại hàng thuộc khai báo nên đúng giúp hộ đang ' +
  'sẽ đã rồi như hay hoặc theo trong ra lên khi nếu').split(' ');
var NL_STOP_ASCII = ('toi minh em anh chi ban muon can hoi tra cuu xin cho cua va voi cac nhung ' +
  'mot may la gi nao thi khong duoc nhap xuat khau vao ve nay kia ay a nhe nhi oi vay ' +
  'sao the bao nhieu ma so hs loai hang khai nen dung giup ho dang se roi nhu hay hoac ' +
  'theo trong ra len khi neu de').split(' ');
/* Cụm đổi ngữ cảnh: sau cụm là công dụng hoặc chất liệu. */
var NL_CUES = [
  ['sử dụng cho', 'use'], ['sử dụng để', 'use'], ['sử dụng trong', 'use'],
  ['dùng để', 'use'], ['dùng cho', 'use'], ['dùng làm', 'use'], ['dùng trong', 'use'],
  ['để làm', 'use'], ['dành cho', 'use'], ['phục vụ', 'use'], ['làm', 'use'], ['dùng', 'use'],
  ['làm từ', 'material'], ['làm bằng', 'material'], ['bằng', 'material'],
  ['chất liệu', 'material'], ['thành phần', 'material'], ['pha', 'material'],
  ['từ', 'material'], ['chứa', 'material'], ['gồm', 'material']
];
/* Từ đơn vẫn nhận khi gõ không dấu vì không lẫn nghĩa. */
var NL_CUE_ASCII = ['làm', 'pha', 'dùng'];
var NL_STOP_PHRASES = ['mã hs', 'mã số', 'là gì', 'nhập khẩu', 'xuất khẩu', 'hàng hóa',
  'sản phẩm', 'mặt hàng', 'phân loại', 'áp mã', 'như thế nào', 'bao nhiêu', 'thế nào',
  'tại sao', 'vì sao', 'loại nào'];
var NL_MATERIAL = ('cotton bông polyester polyeste nylon nilon spandex elastane rayon visco viscose ' +
  'len lụa sợi xơ filament thép inox sắt nhôm đồng kẽm thiếc niken titan gỗ tre nứa mây ' +
  'nhựa pvc pe pp pet abs pu silicon silicone da giấy gốm sứ carbon cacbon composite ' +
  'acrylic polyme polymer xốp thep nhom nhua').split(' ');
var NL_MATERIAL_PHRASES = ['kim loại', 'hợp kim', 'cao su', 'thủy tinh', 'tơ tằm', 'thép không gỉ'];

/* Nhóm đồng nghĩa (hai chiều). Chỉ mở rộng khớp, không đổi dữ liệu. */
var NL_SYN_GROUPS = [
  ['cotton', 'bông', 'sợi bông'], ['polyester', 'polyeste', 'filament polyester'],
  ['nylon', 'nilon', 'polyamide'], ['spandex', 'elastane'],
  ['dệt kim', 'knitted'], ['dệt thoi', 'woven'], ['không dệt', 'non woven'],
  ['áo thun', 'áo phông', 't shirt'], ['quần áo', 'may mặc', 'trang phục'],
  ['vải', 'fabric'], ['sofa', 'ghế sofa'],
  ['inox', 'thép không gỉ', 'stainless'], ['sắt', 'thép'],
  ['nhựa', 'plastic', 'polyme', 'polymer'], ['hạt nhựa', 'nhựa nguyên sinh'],
  ['cao su', 'rubber'], ['gỗ', 'ván gỗ', 'wood'],
  ['ô tô', 'xe hơi', 'xe ô tô', 'oto'], ['xe máy', 'xe gắn máy', 'motorcycle'],
  ['phụ tùng', 'linh kiện', 'bộ phận'], ['điện thoại', 'smartphone'],
  ['máy tính', 'laptop', 'computer'],
  ['đồng hồ thông minh', 'smartwatch', 'thiết bị đeo tay thông minh'],
  ['tai nghe', 'headphone', 'earphone'], ['đèn led', 'led'],
  ['pin', 'battery', 'ắc quy'], ['dây điện', 'cáp điện', 'cable'], ['cảm biến', 'sensor'],
  ['thực phẩm chức năng', 'thực phẩm bảo vệ sức khỏe', 'food supplement'],
  ['canxi', 'calci', 'calcium'], ['sữa', 'milk'], ['whey', 'whey protein'],
  ['hương liệu', 'flavour', 'flavor', 'chất tạo hương'],
  ['thức ăn chăn nuôi', 'thức ăn gia súc', 'thức ăn bổ sung'],
  ['phân bón', 'fertilizer'], ['hóa chất', 'chemical'],
  ['mỹ phẩm', 'cosmetic', 'chăm sóc da'], ['thuốc', 'dược phẩm'],
  ['cà phê', 'coffee'], ['bột', 'powder', 'dạng bột'], ['máy chiếu', 'projector'],
  ['màn hình', 'display', 'monitor'], ['áp suất', 'áp lực']
];
var NL_SYN = {};
NL_SYN_GROUPS.forEach(function (g) {
  g.forEach(function (t) {
    var k = norm(t);
    NL_SYN[k] = (NL_SYN[k] || []).concat(g.filter(function (x) { return x !== t; }));
  });
});

/* Thuộc tính loại trừ nhau: hỏi một loại mà văn bản ghi loại khác thì hạ điểm
   (dệt thoi 5407 khác dệt kim 6001 — cặp dễ nhầm nhất). */
var NL_EXCLUSIVE = [['dệt kim', 'dệt thoi', 'không dệt']];
var NL_CAT_LABEL = { goods: 'mặt hàng', material: 'chất liệu', use: 'công dụng' };
var NL_CAT_WEIGHT = { goods: 1.25, material: 1, use: 0.8 };
var NL_FIELD_WEIGHT = { p: 3, r: 1.4, b: 1.2, s: 0.8 };
var NL_FIELD_LABEL = { p: 'tên hàng', r: 'kết quả phân loại', b: 'mô tả', s: 'trích yếu' };
var NL_DISCLAIMER = 'Kết quả chỉ mang tính tham khảo, dựa trên các văn bản trong kho; ' +
  'không thay thế quyết định phân loại của cơ quan hải quan.';

/* Tách câu hỏi thành đơn vị nội dung {raw, n, cat, seg, pos, words}. */
function parseQuestion(text) {
  var hsQ = [];
  /* Mã HS có dấu chấm (8421.99.94) lấy riêng trước khi bỏ dấu câu. */
  text = String(text == null ? '' : text).replace(/\b\d{4}(?:\.\d{2}){1,3}\b/g, function (m) {
    hsQ.push(m.replace(/\./g, '')); return ' ';
  });
  var toks = viKey(text).split(' ').filter(Boolean).map(function (r) {
    return { raw: r, n: norm(r) };
  });
  var units = [], cat = 'goods', seg = 0, i = 0;
  function joinN(a, len) {
    return toks.slice(a, a + len).map(function (t) { return t.n; }).join(' ');
  }
  /* Cụm nhiều từ so được cả dạng không dấu; từ đơn phải đúng dấu
     (gõ "từ" mới là chất liệu, "tủ" thì không). */
  function matchList(list, at) {
    for (var k = 0; k < list.length; k++) {
      var words = (typeof list[k] === 'string' ? list[k] : list[k][0]).split(' ');
      if (at + words.length > toks.length) continue;
      var ok = words.every(function (w, j) {
        var t = toks[at + j];
        return t.raw === w || ((words.length > 1 || NL_CUE_ASCII.indexOf(w) !== -1) &&
          t.raw === t.n && t.n === norm(w));
      });
      if (ok) return { len: words.length, item: list[k] };
    }
    return null;
  }
  function byLen(a, b) {
    return (typeof b === 'string' ? b : b[0]).split(' ').length -
      (typeof a === 'string' ? a : a[0]).split(' ').length;
  }
  var cues = NL_CUES.slice().sort(byLen), stopPh = NL_STOP_PHRASES.slice().sort(byLen);
  while (i < toks.length) {
    var t = toks[i];
    if (/^\d{4,8}$/.test(t.n)) { hsQ.push(t.n); i++; seg++; continue; }
    var L = 0;
    for (var l = 4; l >= 2; l--) {
      if (i + l <= toks.length && NL_SYN[joinN(i, l)]) { L = l; break; }
    }
    if (!L) {
      var cue = matchList(cues, i);
      if (cue) { cat = cue.item[1]; i += cue.len; seg++; continue; }
      var sp = matchList(stopPh, i);
      if (sp) { i += sp.len; seg++; continue; }
      if (NL_STOP.indexOf(t.raw) !== -1 || (t.raw === t.n && NL_STOP_ASCII.indexOf(t.n) !== -1) ||
          t.n.length < 2) { i++; seg++; continue; }
      L = 1;
    }
    var raw = toks.slice(i, i + L).map(function (x) { return x.raw; }).join(' ');
    units.push({ raw: raw, n: joinN(i, L), words: L, seg: seg, pos: i,
      cat: NL_MATERIAL.indexOf(raw) !== -1 || NL_MATERIAL_PHRASES.indexOf(raw) !== -1 ? 'material' : cat });
    i += L;
  }
  return { units: units, hs: hsQ };
}

/* Chỉ mục riêng cho hỏi đáp (dạng không dấu + dạng có dấu), dựng khi cần. */
var _nlIdx = null, _nlDf = {};
function nlParts(pt) {
  var keep = [], res = [], inRes = false;
  String(pt || '').split('\n').forEach(function (line) {
    var l = line.trim();
    if (!l) return;
    if (/^3\.\s*Kết quả/.test(l)) inRes = true;
    else if (/^(🔗|#|🏷️|⚠️|📌 Lưu ý|Số:|Cơ quan:|Đơn đề nghị|• NSX|• Nhà sản xuất|• Tờ khai|• Đơn vị XNK|Đơn vị XNK|Số KQPT|Số phiếu)/.test(l)) {
      inRes = false; return;
    } else if (/^[12]\.\s/.test(l)) inRes = false;
    (inRes ? res : keep).push(l);
  });
  return { b: keep.join(' '), r: res.join(' ') };
}
function nlIndex() {
  if (_nlIdx) return _nlIdx;
  _nlDf = {};
  _nlIdx = DOCS.map(function (d) {
    var parts = nlParts(d.post_text), x = {};
    var src = { p: d.mat_hang, r: parts.r, b: parts.b, s: d.trich_yeu };
    Object.keys(src).forEach(function (f) {
      var k = viKey(src[f]);
      x[f + 'd'] = ' ' + k + ' ';
      x[f] = ' ' + norm(k) + ' ';
    });
    var head = x.pd.split(' ').slice(0, 13).join(' ') + ' ';
    x.headd = head; x.head = ' ' + norm(head) + ' ';
    x.cancel = /^\s*h[uủ]y\b/i.test(String(d.trich_yeu || ''));
    return x;
  });
  return _nlIdx;
}
/* Một thuật ngữ: {key, dia} — dia: so với dạng có dấu. */
function nlTerm(s) { var k = viKey(s); return hasDia(k) ? { key: k, dia: true } : { key: norm(k), dia: false }; }
function countIn(hay, key) {
  var needle = ' ' + key + ' ', n = 0, from = 0, idx;
  while ((idx = hay.indexOf(needle, from)) !== -1) { n++; from = idx + needle.length - 1; if (n >= 3) break; }
  return n;
}
function termInDoc(x, t) {
  var best = 0, field = '', total = 0, sfx = t.dia ? 'd' : '';
  ['p', 'r', 'b', 's'].forEach(function (f) {
    var tf = countIn(x[f + sfx], t.key);
    if (!tf) return;
    var s = NL_FIELD_WEIGHT[f] * (tf / (tf + 0.6));
    total += s;
    if (s > best) { best = s; field = f; }
  });
  return { score: best + 0.25 * (total - best), field: field,
    head: field === 'p' && x['head' + sfx].indexOf(' ' + t.key + ' ') !== -1 };
}
function nlIdf(t) {
  var ck = (t.dia ? 'd:' : 'n:') + t.key;
  if (_nlDf[ck]) return _nlDf[ck];
  var idx = nlIndex(), df = 0, N = idx.length;
  for (var i = 0; i < N; i++) {
    if (termInDoc(idx[i], t).score) df++;
  }
  _nlDf[ck] = { df: df, idf: Math.log(1 + (N - df + 0.5) / (df + 0.5)) };
  return _nlDf[ck];
}

/* Biến thể của một đơn vị: chính nó, dạng không dấu (khi gõ dấu sai),
   sửa lỗi gõ, đồng nghĩa. Mỗi biến thể {t, w, show}. */
function nlVariants(u, v) {
  var vars = [], self = nlTerm(u.raw);
  vars.push({ t: self, w: 1, show: '' });
  if (self.dia) vars.push({ t: { key: u.n, dia: false }, w: 0.85, show: '' });
  if (u.words === 1 && u.n.length >= 4 && !nlIdf({ key: u.n, dia: false }).df) {
    var fix = correctToken(u.n, v);
    if (fix) vars.push({ t: { key: fix, dia: false }, w: 0.8, show: fix });
  }
  (NL_SYN[u.n] || []).forEach(function (s) { vars.push({ t: nlTerm(s), w: 0.7, show: s }); });
  return vars.filter(function (vv) { vv.stat = nlIdf(vv.t); return vv.stat.df > 0; });
}

/* Hỏi đáp: {parsed, concepts, results[], hsList[], keywords, weak}. */
function askDocs(question, opts) {
  opts = opts || {};
  var limit = opts.limit || 5;
  var parsed = parseQuestion(question);
  var idx = nlIndex(), v = vocab(), N = idx.length;
  var maxIdf = Math.log(1 + (N - 0.5) / 1.5);
  /* Ghép 2 từ đơn liền nhau thành một khái niệm khi kho có đúng cụm đó
     ("tủ lạnh", "hữu cơ", "gia súc"); từng từ đơn vẫn được tính một phần. */
  var concepts = [], us = parsed.units, k = 0;
  while (k < us.length) {
    var a = us[k], b = us[k + 1];
    if (b && a.words === 1 && b.words === 1 && a.seg === b.seg && b.pos === a.pos + 1) {
      var pair = { raw: a.raw + ' ' + b.raw, n: a.n + ' ' + b.n, words: 2, cat: a.cat === 'material' || b.cat === 'material' ? 'material' : a.cat };
      var pv = nlVariants(pair, v);
      var known = function (u) { return NL_SYN[u.n] || NL_MATERIAL.indexOf(u.raw) !== -1; };
      if (pv.length || (!known(a) && !known(b))) {
        [a, b].forEach(function (u) {
          nlVariants(u, v).forEach(function (vv) { vv.w *= 0.4; vv.part = u.raw; pv.push(vv); });
        });
        pair.vars = pv; concepts.push(pair); k += 2; continue;
      }
    }
    a.vars = nlVariants(a, v); concepts.push(a); k++;
  }
  var seen = {};
  concepts = concepts.filter(function (c) { if (seen[c.n]) return false; seen[c.n] = true; return true; });
  concepts.forEach(function (c) {
    c.idf = c.vars.length ? Math.max.apply(null, c.vars.map(function (vv) { return vv.stat.idf; })) : maxIdf * 0.6;
    c.weight = c.idf * NL_CAT_WEIGHT[c.cat] * (c.words > 1 ? 1.3 : 1);
  });
  var totalW = concepts.reduce(function (s, c) { return s + c.weight; }, 0);
  var keywords = concepts.map(function (c) { return c.raw; }).join(' ');
  var base = { parsed: parsed, concepts: concepts, keywords: keywords, results: [], hsList: [], weak: true };
  if (!concepts.length && !parsed.hs.length) return base;

  var out = [];
  for (var i = 0; i < DOCS.length; i++) {
    var d = DOCS[i], x = idx[i];
    if (!d.ma_hs) continue;
    var score = 0, got = 0, matched = [], missing = [], head = false;
    concepts.forEach(function (c) {
      var best = null, full = false;
      c.vars.forEach(function (vv) {
        var r = termInDoc(x, vv.t);
        if (!r.score) return;
        /* Từ được gõ có dấu thì "khớp đủ" phải đúng cả dấu ("dầu cọ" không tính "dầu có"). */
        var folded = !vv.t.dia && c.vars.some(function (v2) {
          return v2.t.dia && !v2.part && norm(v2.t.key) === vv.t.key;
        });
        if (!vv.part && !folded && (r.field === 'p' || r.field === 'r')) full = true;
        var s = r.score * vv.w * vv.stat.idf * (r.head ? 1.2 : 1);
        if (!best || s > best.s) best = { s: s, r: r, vv: vv };
      });
      if (!best) { missing.push(c); return; }
      score += best.s * NL_CAT_WEIGHT[c.cat];
      got += c.weight * Math.min(1, best.vv.w) * (best.r.field === 'p' || best.r.field === 'r' ? 1 : 0.8);
      matched.push({ c: c, field: best.r.field, show: best.vv.part ? '' : best.vv.show, part: best.vv.part || '',
        full: full });
      if (best.r.head && c.cat !== 'use' && !best.vv.part) head = true;
    });
    var conflict = '';
    NL_EXCLUSIVE.forEach(function (g) {
      var asked = g.filter(function (t) { return seen[norm(t)]; });
      if (!asked.length || asked.some(function (t) { return x.pd.indexOf(' ' + t + ' ') !== -1; })) return;
      var other = g.filter(function (t) { return asked.indexOf(t) === -1 && x.pd.indexOf(' ' + t + ' ') !== -1; });
      if (other.length) conflict = other[0] + ' (câu hỏi: ' + asked.join(', ') + ')';
    });
    if (conflict) score *= 0.5;
    var hsD = hsDigits(d.ma_hs), hsHit = false;
    parsed.hs.forEach(function (h) {
      if (hsD.indexOf(h) === 0) { hsHit = true; score += 12; got += totalW ? totalW * 0.25 : 1; if (!concepts.length) head = true; }
    });
    if (!score) continue;
    var coverage = totalW ? Math.min(1, got / totalW) : (head ? 1 : 0.5);
    if (x.cancel) score *= 0.5;
    out.push({ doc: d, i: i, score: score * (0.5 + coverage), coverage: coverage,
      matched: matched, missing: missing, head: head, hsHit: hsHit, cancel: x.cancel, conflict: conflict });
  }
  out.sort(function (a, b) {
    if (b.score !== a.score) return b.score - a.score;
    return IDX[b.i].dateSort - IDX[a.i].dateSort;
  });
  var top = out[0];
  out.forEach(function (r) {
    var lvl = r.coverage >= 0.88 && r.head ? 3 : r.coverage >= 0.6 ? 2 : 1;
    if (top && lvl === 3 && r.score < top.score * 0.7) lvl = 2;
    if (r.conflict) lvl = 1;
    if (r.cancel && lvl > 1) lvl--;
    r.level = lvl;
    r.confidence = lvl === 3 ? 'Cao' : lvl === 2 ? 'Trung bình' : 'Thấp';
  });
  base.weak = !top || top.coverage < 0.45;
  if (base.weak) return base;
  /* Tối đa 3 văn bản cùng một mã HS để còn chỗ cho mã thay thế. */
  var good = out.filter(function (r) { return r.coverage >= 0.4; });
  /* Các hạng sau hạng 1 phải trùng mã HS được hỏi, hoặc khớp từ chỉ mặt hàng chính (từ đầu câu hỏi)
     ở tên hàng hoặc kết quả phân loại; tránh kết quả lấp chỗ chỉ trùng một từ chung. */
  var headC = concepts.filter(function (c) { return c.cat !== 'use'; })[0] || concepts[0];
  if (headC) good = good.filter(function (r) {
    return r === top || r.hsHit || r.matched.some(function (m) {
      return m.c === headC && m.full;
    });
  });
  var picked = [], perHs = {}, rest = [];
  good.forEach(function (r) {
    if (picked.length >= limit) return;
    if ((perHs[r.doc.ma_hs] || 0) >= 3) { rest.push(r); return; }
    perHs[r.doc.ma_hs] = (perHs[r.doc.ma_hs] || 0) + 1;
    picked.push(r);
  });
  while (picked.length < limit && rest.length) picked.push(rest.shift());
  picked.sort(function (a, b) { return b.score - a.score; });
  var hsMap = {}, hsList = [];
  picked.forEach(function (r) {
    var h = r.doc.ma_hs;
    if (!hsMap[h]) { hsMap[h] = { hs: h, count: 0, level: 0, score: 0 }; hsList.push(hsMap[h]); }
    hsMap[h].count++;
    hsMap[h].level = Math.max(hsMap[h].level, r.level);
    hsMap[h].score += r.score;
  });
  base.results = picked; base.hsList = hsList;
  return base;
}

/* Lý do ngắn gọn cho một kết quả hỏi đáp. */
function askReason(r) {
  var parts = { goods: [], material: [], use: [] }, where = [];
  r.matched.forEach(function (m) {
    var label = m.part ? m.part : m.c.raw + (m.show && norm(m.show) !== m.c.n ? ' (≈ ' + m.show + ')' : '');
    parts[m.c.cat].push(label);
    var w = NL_FIELD_LABEL[m.field];
    if (where.indexOf(w) === -1) where.push(w);
  });
  var segs = [];
  ['goods', 'material', 'use'].forEach(function (k) {
    if (parts[k].length) segs.push(NL_CAT_LABEL[k] + ' ' + parts[k].join(', '));
  });
  var s = segs.length ? 'Trùng ' + segs.join('; ') : 'Trùng mã HS trong câu hỏi';
  if (where.length) s += ' (trong ' + where.join(', ') + ')';
  s += '.';
  var miss = r.missing.map(function (c) { return c.raw; });
  r.matched.forEach(function (m) { if (m.part) miss.push(m.c.raw); });
  if (miss.length) s += ' Chưa khớp: ' + miss.join(', ') + '.';
  if (r.conflict) s += ' Khác loại: văn bản ghi ' + r.conflict + '.';
  if (r.cancel) s += ' Lưu ý: đây là văn bản hủy một thông báo trước đó.';
  return s;
}

/* ================= Phân biệt mã dễ nhầm =================
   Cặp văn bản có tên hàng/mô tả gần giống nhau nhưng mã HS khác nhau,
   phát hiện tự động bằng độ giống cosine (TF-IDF) trên mat_hang, trich_yeu và phần mô tả. */
var CP_MIN = 0.26;
var CP_STOP = ('mã hàng mới hiệu không nhãn model mét cuộn kt khổ định lượng kích thước trọng lượng ' +
  'nsx nhà sản xuất xuất xứ đóng gói gói hộp thùng bao chai lọ túi kg gam gram cái chiếc bộ ' +
  'và của cho các có được loại dạng là từ với theo trong để dùng sử dụng làm một hai khoảng ' +
  'thành phần gồm chứa tỷ lệ hàng hóa sản phẩm tên thông báo kết quả phân tích phân loại ' +
  'xác định trước số mẫu khai báo nêu tại tờ khai đã chưa lot hsd cb ctcvn batch date').split(' ');
var CP_STOP_SET = {};
/* Từ nhiễu chỉ bỏ ở hàng "Từ chỉ có trong tên hàng" (số lô, số hiệu, mã đơn...). */
var CP_UNIQ_STOP = {};
('no số lô lo lot batch ref code mã sn serial seri po invoice part pn item art').split(' ')
  .forEach(function (w) { CP_UNIQ_STOP[w] = 1; });
CP_STOP.forEach(function (w) { CP_STOP_SET[w] = 1; });
/* Cặp mẫu biên soạn tay, luôn đứng đầu danh sách. */
var CP_SEED = [{
  a: '1440/TBKQPTPL-Đ3', b: '1419/TBKQPTPL-Đ3',
  title: 'Vải polyester bọc sofa: dệt thoi (5407.53.00) hay dệt kim tạo lông (6001.92.90)?',
  lead: 'Hai lô vải cùng 100% polyester, cùng đã nhuộm, cùng dùng để bọc sofa, cùng một doanh nghiệp ' +
    'và cùng một tờ khai, nhưng được xếp vào hai chương khác nhau. Điều quyết định là cấu trúc vải, ' +
    'không phải chất liệu hay công dụng.',
  points: [
    'Cấu trúc: 1440 là vải dệt thoi, kiểu dệt phức tạp (không phải kiểu dệt đặc biệt của Chương 58); ' +
      '1419 là vải dệt kim tạo vòng lông một mặt, vòng lông đã được cắt.',
    'Loại sợi: lớp vải chính của 1440 dệt từ sợi filament polyester nên vào nhóm 54.07 (vải dệt thoi ' +
      'bằng sợi filament tổng hợp); 1419 là vải nổi vòng dệt kim từ xơ polyester nên vào nhóm 60.01.',
    'Lớp ép: 1440 có một mặt ép dán lớp vải không dệt polyester (25,2% khối lượng), nhưng lớp dệt thoi ' +
      '(74,8%) là lớp chính quyết định mã; 1419 chưa ngâm tẩm, tráng phủ hay ép lớp.',
    'Khi khai báo vải bọc nội thất: ghi "100% polyester, bọc sofa" là chưa đủ để chọn mã. Cần xác định ' +
      'dệt thoi hay dệt kim, có nổi vòng hay không, và sợi filament hay xơ.'
  ]
}];
/* Thuộc tính thường quyết định mã: so hai bên để tìm điểm khác. */
var CP_ATTRS = [
  { label: 'Cấu trúc vải', terms: ['dệt thoi', 'dệt kim', 'không dệt', 'nổi vòng', 'vòng lông', 'tạo lông',
    'sơnin', 'chenille', 'ép lớp', 'ép dán', 'tráng phủ', 'ngâm tẩm', 'đã nhuộm', 'đã in', 'đàn hồi',
    'sợi filament', 'xơ staple', 'sợi đơn', 'sợi xe'] },
  { label: 'Dạng / hình thức', terms: ['dạng bột', 'dạng lỏng', 'dạng viên', 'viên nén', 'viên nang', 'dạng hạt',
    'dạng cuộn', 'dạng thanh', 'dạng tấm', 'dạng que', 'dạng ống', 'dạng sợi', 'dạng gel', 'dạng kem',
    'dạng khối', 'dạng dây', 'dạng lá', 'dạng mảnh', 'dạng nhũ tương', 'dạng huyền phù', 'dạng cốm'] },
  { label: 'Gia công / thành phần', terms: ['cán nóng', 'cán nguội', 'mạ kẽm', 'mạ', 'sơn phủ', 'đúc', 'rèn',
    'đông lạnh', 'sấy khô', 'rang', 'lên men', 'tinh chế', 'thủy phân', 'đã qua xử lý', 'chưa qua xử lý',
    'không hợp kim', 'hợp kim', 'đã cắt', 'không cắt', 'không gỉ'] },
  { label: 'Chất liệu', terms: NL_MATERIAL_PHRASES.filter(function (t) { return t !== 'hợp kim'; })
    .concat(NL_MATERIAL.filter(function (t) { return hasDia(t) || !/^(thep|nhom|nhua)$/.test(t); })) }
];
CP_ATTRS.forEach(function (g) {
  g.keys = g.terms.slice().sort(function (a, b) { return b.length - a.length; })
    .map(function (t) { var k = viKey(t); return { t: t, w: k, len: k.split(' ').length }; });
});

var _cp = null;
function cpWords(text) {
  return viKey(text).split(' ').filter(function (w) {
    return w.length > 1 && !/\d/.test(w) && !CP_STOP_SET[w];
  });
}
function cpFeatures(text, w, into) {
  var ws = cpWords(text);
  ws.forEach(function (t, i) {
    into[t] = Math.max(into[t] || 0, w);
    if (i) { var bg = ws[i - 1] + ' ' + t; into[bg] = Math.max(into[bg] || 0, w * 1.5); }
  });
}
function cpSim(x, y) {
  var s = 0;
  Object.keys(x.v).forEach(function (k) { if (y.v[k]) s += x.v[k] * y.v[k]; });
  return s / (x.n * y.n);
}
function cpData() {
  if (_cp) return _cp;
  var docs = [], df = {}, byMa = {};
  DOCS.forEach(function (d) {
    if (!hsDigits(d.ma_hs)) return;
    var f = {};
    cpFeatures(d.mat_hang || d.trich_yeu, 1, f);
    cpFeatures(d.trich_yeu, 0.6, f);
    cpFeatures(parseDocDetail(d).sec2, 0.4, f);
    var x = { d: d, f: f };
    docs.push(x); byMa[d.ma] = x;
    Object.keys(f).forEach(function (k) { df[k] = (df[k] || 0) + 1; });
  });
  var N = docs.length, post = {};
  docs.forEach(function (x, a) {
    var nn = 0, v = {};
    Object.keys(x.f).forEach(function (k) {
      var wt = x.f[k] * Math.log(N / df[k]);
      if (wt > 0) { v[k] = wt; nn += wt * wt; }
    });
    x.v = v; x.n = Math.sqrt(nn) || 1; x.hs = hsDigits(x.d.ma_hs);
    Object.keys(v).forEach(function (k) {
      if (df[k] >= 2 && df[k] <= N * 0.15) (post[k] = post[k] || []).push(a);
    });
  });
  var dot = {};
  Object.keys(post).forEach(function (k) {
    var L = post[k];
    for (var p = 0; p < L.length; p++) {
      for (var q = p + 1; q < L.length; q++) {
        var a = L[p], b = L[q];
        if (docs[a].hs === docs[b].hs) continue;
        var key = a * N + b;
        dot[key] = (dot[key] || 0) + docs[a].v[k] * docs[b].v[k];
      }
    }
  });
  var groups = {}, list = [], forDoc = {};
  function addPair(A, B, sim, seed) {
    if (!seed && hsDigits(A.ma_hs) > hsDigits(B.ma_hs)) { var t = A; A = B; B = t; }
    var gk = [hsDigits(A.ma_hs), hsDigits(B.ma_hs)].sort().join('|');
    var g = groups[gk];
    if (!g) { g = groups[gk] = { pairs: [] }; list.push(g); }
    var pair = { a: A, b: B, sim: sim, seed: seed || null };
    if (seed) { g.pairs.unshift(pair); g.seed = seed; } else g.pairs.push(pair);
    [A, B].forEach(function (d) { (forDoc[d.ma] = forDoc[d.ma] || []).push(pair); });
  }
  var seeded = {};
  CP_SEED.forEach(function (s) {
    var A = null, B = null;
    docs.forEach(function (x) { if (x.d.so_hieu === s.a) A = x; if (x.d.so_hieu === s.b) B = x; });
    if (!A || !B) return;
    seeded[A.d.ma + '-' + B.d.ma] = seeded[B.d.ma + '-' + A.d.ma] = 1;
    addPair(A.d, B.d, cpSim(A, B), s);
  });
  Object.keys(dot).forEach(function (key) {
    var a = Math.floor(key / N), b = key % N;
    /* dot chỉ tính từ hiếm nên luôn nhỏ hơn cosine đầy đủ; bỏ sớm cặp quá xa để đỡ tốn thời gian. */
    if (dot[key] / (docs[a].n * docs[b].n) < CP_MIN / 2) return;
    var sim = cpSim(docs[a], docs[b]);
    if (sim < CP_MIN || seeded[docs[a].d.ma + '-' + docs[b].d.ma]) return;
    addPair(docs[a].d, docs[b].d, sim);
  });
  list.forEach(function (g) {
    g.pairs.sort(function (p, q) { return (q.seed ? 1 : 0) - (p.seed ? 1 : 0) || q.sim - p.sim; });
    g.best = g.pairs[0];
  });
  list.sort(function (g, h) { return (h.seed ? 1 : 0) - (g.seed ? 1 : 0) || h.best.sim - g.best.sim; });
  Object.keys(forDoc).forEach(function (ma) {
    forDoc[ma].sort(function (p, q) { return (q.seed ? 1 : 0) - (p.seed ? 1 : 0) || q.sim - p.sim; });
  });
  _cp = { groups: list, forDoc: forDoc, byMa: byMa, df: df, N: N };
  return _cp;
}
function cpGroupOf(a, b) {
  var gk = [hsDigits(a.ma_hs), hsDigits(b.ma_hs)].sort().join('|'), found = null;
  cpData().groups.forEach(function (g) {
    if ([hsDigits(g.best.a.ma_hs), hsDigits(g.best.b.ma_hs)].sort().join('|') === gk) found = g;
  });
  return found;
}
/* Các cặp liên quan một văn bản, mỗi mã HS bên kia lấy một cặp giống nhất. */
function cpForDoc(ma) {
  var seen = {}, out = [];
  (cpData().forDoc[ma] || []).forEach(function (p) {
    var other = String(p.a.ma) === String(ma) ? p.b : p.a;
    if (seen[other.ma_hs]) return;
    seen[other.ma_hs] = 1;
    out.push({ pair: p, other: other });
  });
  return out;
}
/* Thuộc tính có trong văn bản; bỏ qua thuộc tính bị phủ định ("chưa ngâm tẩm, tráng phủ hay ép lớp",
   "không chứa sợi đàn hồi") trong khoảng 8 từ sau "chưa"/"không" của cùng một câu. */
function cpAttrs(text) {
  var found = CP_ATTRS.map(function () { return []; });
  String(text || '').split(/[.;()\n]+/).forEach(function (seg) {
    var w = viKey(seg).split(' '), neg = -99, i = 0;
    while (i < w.length) {
      var hit = null;
      for (var g = 0; g < CP_ATTRS.length && !hit; g++) {
        CP_ATTRS[g].keys.forEach(function (x) {
          if (hit && hit.len >= x.len) return;
          if (w.slice(i, i + x.len).join(' ') === x.w) hit = { g: g, t: x.t, len: x.len };
        });
      }
      if (hit) {
        if (hit.t.indexOf('đã ') === 0 || hit.t.indexOf('dạng ') === 0) neg = -99;
        if (i - neg > 8 && found[hit.g].indexOf(hit.t) === -1) found[hit.g].push(hit.t);
        i += hit.len;
        continue;
      }
      if (w[i] === 'chưa' || w[i] === 'không') neg = i;
      else if (w[i] === 'đã' || w[i] === 'dạng') neg = -99;
      i++;
    }
  });
  return found;
}
function cpUse(text) {
  var m = /(?:dùng để|dùng cho|dùng làm|dùng trong|sử dụng cho|sử dụng để|sử dụng trong|làm nguyên liệu)\s+[^,.;:()\n]{3,60}/i
    .exec(text);
  return m ? m[0].trim() : '';
}
function cpOther(det, re) {
  var v = '';
  det.other.forEach(function (l) { var m = re.exec(l); if (m && !v) v = m[1].trim().replace(/[.\s]+$/, ''); });
  return v;
}
/* So sánh hai văn bản: điểm khác (theo nhóm thuộc tính) và điểm giống. */
function cpDiff(a, b) {
  var da = parseDocDetail(a), db = parseDocDetail(b), cp = cpData();
  var ta = (a.mat_hang || a.trich_yeu || '') + ' . ' + da.sec2;
  var tb = (b.mat_hang || b.trich_yeu || '') + ' . ' + db.sec2;
  var aa = cpAttrs(ta), ab = cpAttrs(tb), diffs = [], same = [];
  CP_ATTRS.forEach(function (g, i) {
    var onlyA = aa[i].filter(function (t) { return ab[i].indexOf(t) === -1; });
    var onlyB = ab[i].filter(function (t) { return aa[i].indexOf(t) === -1; });
    var both = aa[i].filter(function (t) { return ab[i].indexOf(t) !== -1; });
    if (onlyA.length || onlyB.length) diffs.push({ label: g.label, a: aa[i], b: ab[i] });
    if (both.length) same.push(g.label + ': ' + both.join(', '));
  });
  var ua = cpUse(ta), ub = cpUse(tb);
  if (ua && ub && norm(ua) === norm(ub)) same.push('Công dụng: ' + ua);
  else if (ua || ub) diffs.push({ label: 'Công dụng', a: ua ? [ua] : [], b: ub ? [ub] : [] });
  var wa = {}, wb = {};
  cpWords(a.mat_hang || a.trich_yeu).forEach(function (w) { wa[w] = 1; });
  cpWords(b.mat_hang || b.trich_yeu).forEach(function (w) { wb[w] = 1; });
  function uniq(x, y) {
    return Object.keys(x).filter(function (w) { return !y[w] && cp.df[w] && !CP_UNIQ_STOP[w]; })
      .sort(function (p, q) { return cp.df[p] - cp.df[q]; }).slice(0, 5);
  }
  var na = uniq(wa, wb), nb = uniq(wb, wa);
  if (na.length || nb.length) diffs.push({ label: 'Từ chỉ có trong tên hàng', a: na, b: nb });
  var ca = cpOther(da, /^Đơn vị XNK:\s*(.+)$/), cb = cpOther(db, /^Đơn vị XNK:\s*(.+)$/);
  if (ca && norm(ca) === norm(cb)) same.push('Cùng đơn vị XNK: ' + ca);
  var ka = cpOther(da, /^Tờ khai:\s*(.+)$/), kb = cpOther(db, /^Tờ khai:\s*(.+)$/);
  if (ka && norm(ka) === norm(kb)) same.push('Cùng tờ khai: ' + ka);
  var x = cp.byMa[a.ma], y = cp.byMa[b.ma];
  return { a: a, b: b, da: da, db: db, diffs: diffs, same: same,
    sim: x && y ? cpSim(x, y) : 0 };
}

/* Cho phép kiểm thử bằng Node: VBXNK.searchDocs(...) */
if (typeof globalThis !== 'undefined') {
  globalThis.VBXNK = {
    detectMode: detectMode, hsTreeData: hsTreeData, followMatch: followMatch, follows: follows,
    toggleFollow: toggleFollow, newDocs: newDocs, totalNew: totalNew, seenSet: seenSet, markSeen: markSeen, statsData: statsData, inBranch: inBranch,
    norm: norm, lev: lev, hsDigits: hsDigits, parseDate: parseDate,
    buildIndex: buildIndex, searchDocs: searchDocs, suggest: suggest, askSuggest: askSuggest,
    didYouMean: didYouMean, relaxedSearch: relaxedSearch,
    relatedSearches: relatedSearches, chapterCount: chapterCount,
    recordRecent: recordRecent, recents: recents,
    parseDocDetail: parseDocDetail, relatedDocs: relatedDocs,
    extractDriveId: extractDriveId, highlight: highlight,
    viKey: viKey, parseQuestion: parseQuestion, askDocs: askDocs, askReason: askReason,
    NL_DISCLAIMER: NL_DISCLAIMER,
    cpData: cpData, cpDiff: cpDiff, cpForDoc: cpForDoc, cpGroupOf: cpGroupOf,
    _pdfBlockHtml: pdfBlockHtml, _renderDetail: renderDetail,
    _setData: function (docs, drive, meta, img) {
      DOCS = docs; DRIVE = drive || {}; META = meta || {}; IMG = img || {};
      _suggestPool = null; _askPool = null; _vocab = null; _recents = null; _clicks = null; _nlIdx = null; _nlDf = {}; _cp = null;
      _follows = null; _seen = null; _followSnap = null;
      buildIndex(docs);
    }
  };
}

/* ================= Hiển thị (chỉ chạy trên trình duyệt) ================= */

var PAGE_SIZE = 30;
var state = { query: '', loai: '', chapter: '', year: '', shown: PAGE_SIZE,
  mode: 'keyword', auto: 'keyword', forced: false, askText: '', askWeak: false, branch: null };
var _lastResults = [];

function $(sel) { return document.querySelector(sel); }
function imgTag(doc, cls) {
  /* Ảnh trang 1 lưu trên Google Drive (repo chỉ chứa file text, không chứa
     ảnh nhị phân). File ảnh được chia sẻ Anyone with the link qua thừa kế
     thư mục "Anh trang 1" nên thumbnail mở được cho mọi người xem. */
  var id = IMG[doc.ma] || IMG[String(doc.ma)] || '';
  if (!id) return '';
  return '<img class="' + (cls || '') + '" src="https://drive.google.com/thumbnail?id=' +
    encodeURIComponent(id) + '&sz=w900" alt="Trang 1 văn bản ' + esc(doc.so_hieu) +
    '" loading="lazy" onerror="this.style.display=\'none\'">';
}

function loaiBadge(doc) {
  return '<span class="loai-badge">' + esc(LOAI_LABEL[doc.loai] || 'Văn bản') + '</span>';
}
function hsBadge(doc) {
  return doc.ma_hs ? '<span class="hs-badge">HS ' + esc(doc.ma_hs) + '</span>' : '';
}
function shortText(s, n) {
  s = String(s || '');
  return s.length > n ? s.slice(0, n).trim() + '…' : s;
}

function currentTokens() {
  return norm(state.query).split(' ').filter(Boolean);
}

function cardHtml(r) {
  var d = r.doc, toks = currentTokens();
  var title = highlight(d.so_hieu, toks);
  var prod = highlight(shortText(d.mat_hang || d.trich_yeu, 160), toks);
  var reason = '';
  if (r.reasons && r.reasons.length) {
    var uniq = [];
    r.reasons.forEach(function (x) { if (uniq.indexOf(x) === -1) uniq.push(x); });
    reason = '<p class="match-reason">Khớp: <b>' + esc(uniq.slice(0, 2).join(' · ')) + '</b></p>';
  }
  return '<article class="card">' +
    '<h3><a href="#/bai/' + d.ma + '">' + title + '</a></h3>' +
    '<p class="sub">' + esc(d.ngay || '') + ' · ' + loaiBadge(d) + ' ' + hsFollowPill(d) + '</p>' +
    '<p>' + prod + '</p>' + reason +
    '</article>';
}

/* Trang 0 kết quả: thừa nhận truy vấn, sửa lỗi gõ, nới truy vấn, dẫn tới
   chương liên quan, cho văn bản mới nhất và nút hỏi Trang — không để độc
   giả rơi vào ngõ cụt (chuẩn Baymard: 68% site làm tệ phần này). */
function zeroResultHtml() {
  var q = state.query.trim();
  var escQ = esc(q);
  var html = '<div class="zero-recovery"><h2>Không tìm thấy văn bản nào cho “' + escQ + '”</h2>';
  var corr = didYouMean(q);
  if (corr) {
    html += '<p class="did-you-mean">Ý bạn là: <button type="button" class="dym-btn" data-q="' +
      esc(corr) + '">' + esc(corr) + '</button>?</p>';
  }
  var relaxed = relaxedSearch(q);
  if (relaxed && relaxed.results.length) {
    html += '<p class="relaxed-note">Kết quả gần đúng — đã bỏ từ “' + esc(relaxed.dropped) + '”:</p>' +
      relaxed.results.slice(0, 5).map(cardHtml).join('');
  }
  var digits = norm(q).replace(/\D/g, '');
  if (digits.length >= 2) {
    var ch = digits.slice(0, 2);
    var count = chapterCount(ch);
    if (count) {
      html += '<p><a class="btn ghost" href="#/chuong/' + ch + '">Duyệt Chương ' + ch +
        ' (' + count + ' văn bản)</a></p>';
    }
  }
  var newest = DOCS.slice().sort(function (a, b) { return parseDate(b.ngay) - parseDate(a.ngay); }).slice(0, 5);
  html += '<h3>Văn bản mới nhất trong kho</h3>' +
    newest.map(function (d) {
      return '<article class="card"><h3><a href="#/bai/' + d.ma + '">' + esc(d.so_hieu) +
        '</a></h3><p class="sub">' + esc(d.ngay || '') + ' · ' + hsBadge(d) + '</p><p>' +
        esc(shortText(d.mat_hang || d.trich_yeu, 140)) + '</p></article>';
    }).join('');
  html += '<p><a class="btn" href="https://m.me/tiepvanhoangkim1" target="_blank" rel="noopener">' +
    'Hỏi Trang về mặt hàng này</a></p>' +
    '<p class="pdf-note">Nhắn cho Trang Văn bản XNK kèm từ khóa “' + escQ +
    '” — Trang sẽ tra cứu và trả lời.</p></div>';
  return html;
}

/* Chỉ khi truy vấn bằng đúng toàn bộ số hiệu hoặc mã HS; tiền tố ("85", "3504") không tính. */
function isExactIdHit(r) {
  var d = r.doc, q = String(state.query || '').trim(), qd = q.replace(/[\s.]/g, '');
  if (/^\d+$/.test(qd)) {
    var soNum = String(d.so_hieu || '').split('/')[0].replace(/\D/g, '');
    return soNum === qd || hsDigits(d.ma_hs) === qd;
  }
  return !!q && norm(d.so_hieu) === norm(q);
}
function wireResultButtons() {
  document.querySelectorAll('#view .dym-btn, #view .rel-chip').forEach(function (b) {
    b.addEventListener('click', function () {
      var q = $('#q');
      q.value = b.getAttribute('data-q');
      commitSearch(q.value);
    });
  });
}

function renderList() {
  var results = searchDocs(state.query, {
    loai: state.loai, chapter: state.chapter, year: state.year
  });
  if (state.branch) results = results.filter(function (r) { return inBranch(r.doc, state.branch); });
  _lastResults = results;
  var view = $('#view');
  var info = $('#resultInfo');
  var asking = state.mode === 'ask' && !!state.askText;
  if (state.branch) {
    info.textContent = 'Tìm thấy ' + results.length + ' văn bản thuộc ' + branchLabel(state.branch) + '.';
  } else if (state.query || state.loai || state.chapter || state.year) {
    info.textContent = 'Tìm thấy ' + results.length + ' văn bản' +
      (state.query ? ' khớp từ khóa “' + state.query.trim() + '”' : '') + '.';
  } else {
    info.textContent = 'Hiển thị văn bản mới nhất. Gõ từ khóa để tìm trong cả kho.';
  }
  var pre = '';
  if (state.branch) {
    pre += '<div class="branch-bar"><span>Đang xem <b>' + esc(branchLabel(state.branch)) +
      '</b> trong cây mã HS</span><a href="#/cay-hs">← Cây mã HS</a><a href="#/">Bỏ lọc nhánh</a></div>';
  }
  if (asking) {
    if (!state.askWeak) {
      pre += '<h2 class="list-head">Kết quả khớp từ khóa' +
        (state.query.trim() ? ' “' + esc(state.query.trim()) + '”' : '') + '</h2>';
    }
  }
  if (!results.length) {
    view.innerHTML = pre + (asking && !state.askWeak
      ? '<p class="empty">Không có văn bản nào chứa đủ các từ khóa này. Xem các văn bản gợi ý ở phía trên.</p>'
      : zeroResultHtml());
    wireResultButtons();
    return;
  }
  var html = pre;
  var corr = state.query ? didYouMean(state.query) : null;
  if (corr) {
    html += '<p class="did-you-mean">Có phải bạn muốn tìm: <button type="button" class="dym-btn" data-q="' +
      esc(corr) + '">' + esc(corr) + '</button>?</p>';
  }
  var shown = results.slice(0, state.shown);
  if (!asking && !state.branch && detectMode(state.query) === 'code') {
    var exact = shown.filter(isExactIdHit), rest = shown.filter(function (r) { return !isExactIdHit(r); });
    if (exact.length) html += '<h2 class="list-head">Khớp chính xác số hiệu / mã HS</h2>' + exact.map(cardHtml).join('');
    if (rest.length) html += (exact.length ? '<h2 class="list-head">Kết quả khớp từ khóa</h2>' : '') + rest.map(cardHtml).join('');
  } else {
    html += shown.map(cardHtml).join('');
  }
  var rel = relatedSearches(results, currentTokens());
  if (rel.length) {
    html += '<div class="related-search"><span>Tìm kiếm liên quan:</span>' +
      rel.map(function (r) {
        return '<button type="button" class="chip rel-chip" data-q="' + esc(r) + '">' + esc(r) + '</button>';
      }).join('') + '</div>';
  }
  if (results.length > state.shown) {
    html += '<button type="button" class="load-more" id="moreBtn">Xem thêm (' +
      (results.length - state.shown) + ' văn bản nữa)</button>';
  }
  view.innerHTML = html;
  wireResultButtons();
  var more = $('#moreBtn');
  if (more) more.addEventListener('click', function () {
    state.shown += PAGE_SIZE; renderList();
  });
}

function renderChapters() {
  var counts = {}, noHs = 0;
  DOCS.forEach(function (d) {
    var ch = chapterOf(d);
    if (ch) counts[ch] = (counts[ch] || 0) + 1; else noHs++;
  });
  var keys = Object.keys(counts).sort();
  var html = '<h2 style="margin-top:4px">Duyệt theo chương HS</h2>' +
    '<p class="result-info">Chọn một chương để xem các văn bản có mã HS thuộc chương đó.</p>' +
    '<div class="chapter-grid">';
  keys.forEach(function (ch) {
    html += '<a class="chapter-card" href="#/chuong/' + ch + '"><b>Chương ' + ch +
      '</b><span>' + counts[ch] + ' văn bản</span></a>';
  });
  if (noHs) {
    html += '<a class="chapter-card" href="#/chuong/khong-co-ma"><b>Chưa có mã HS</b><span>' +
      noHs + ' văn bản</span></a>';
  }
  html += '</div>';
  $('#view').innerHTML = html;
  $('#resultInfo').textContent = keys.length + ' chương HS có văn bản trong kho.';
  updateMeta(null);
}

function pdfBlockHtml(doc) {
  var driveId = DRIVE[doc.so_hieu] || '';
  var html = '<div class="pdf-block"><h2>Xem PDF gốc</h2>';
  if (driveId) {
    html += '<iframe src="' + drivePreviewUrl(driveId) + '" title="PDF ' + esc(doc.so_hieu) +
      ' trên Google Drive" loading="lazy" allowfullscreen></iframe>' +
      '<div class="pdf-links"><a class="btn ghost" href="' + driveViewUrl(driveId) +
      '" target="_blank" rel="noopener">Mở trên Google Drive</a>';
    if (doc.detail_url) {
      html += '<a class="btn ghost" href="' + esc(doc.detail_url) +
        '" target="_blank" rel="noopener">Xem bản gốc customs.gov.vn</a>';
    }
    html += '</div><p class="pdf-note">PDF lưu trên Google Drive của Văn bản XNK. ' +
      'Nếu khung xem báo quá tải lượt xem, dùng link dự phòng bên trên.</p>';
  } else if (doc.pdf_url) {
    var gview = 'https://docs.google.com/gview?url=' + encodeURIComponent(doc.pdf_url) + '&embedded=true';
    html += '<iframe src="' + gview + '" title="PDF ' + esc(doc.so_hieu) +
      '" loading="lazy" allowfullscreen></iframe>' +
      '<div class="pdf-links"><a class="btn ghost" href="' + esc(doc.pdf_url) +
      '" target="_blank" rel="noopener">Tải / mở PDF gốc</a>';
    if (doc.detail_url) {
      html += '<a class="btn ghost" href="' + esc(doc.detail_url) +
        '" target="_blank" rel="noopener">Xem bản gốc customs.gov.vn</a>';
    }
    html += '</div><p class="pdf-note">Đang xem qua Google Docs Viewer từ file gốc của hải quan.</p>' +
      '<div class="drive-paste"><label for="driveInput"><b>Có file PDF này trên Google Drive?</b> ' +
      'Dán link chia sẻ “Anyone with the link” vào đây để nhúng trình xem Drive:</label>' +
      '<input id="driveInput" type="url" placeholder="https://drive.google.com/file/d/…/view">' +
      '<button type="button" class="btn" id="driveBtn">Nhúng từ Drive</button></div>';
  } else if (doc.detail_url) {
    html += '<p>Chưa có file PDF đính kèm cho văn bản này.</p>' +
      '<p><a class="btn ghost" href="' + esc(doc.detail_url) +
      '" target="_blank" rel="noopener">Xem bản gốc customs.gov.vn</a></p>';
  }
  html += '</div>';
  return html;
}

function renderDetail(ma) {
  var doc = null;
  DOCS.forEach(function (d) { if (String(d.ma) === String(ma)) doc = d; });
  var view = $('#view');
  if (!doc) {
    view.innerHTML = '<p class="empty">Không tìm thấy văn bản này trong kho.</p>' +
      '<p><a href="#/">← Về trang chính</a></p>';
    updateMeta(null);
    return;
  }
  var det = parseDocDetail(doc);
  markSeen([doc]); updateFollowBadge();
  var sub = [];
  if (det.coquan) sub.push(esc(det.coquan));
  if (det.soKqpt) sub.push('Số KQPT: ' + esc(det.soKqpt));
  if (det.don) sub.push('Đơn đề nghị số ' + esc(det.don));
  var html = '<a class="back-link" href="#/">← Về danh sách</a>' +
    '<article class="article">' +
    '<h1>' + esc(doc.so_hieu) + '</h1>' +
    '<p class="sub">' + esc(doc.ngay || '') + ' · ' + loaiBadge(doc) + ' ' + hsBadge(doc) +
    (hsDigits(doc.ma_hs).length >= 2 ? ' ' + followBtnHtml(hsDigits(doc.ma_hs), 'Theo dõi mã HS ' + doc.ma_hs, 'follow-doc') : '') +
    (sub.length ? '<br>' + sub.join(' · ') : '') + '</p>' +
    '<h2>1. Tên hàng theo khai báo</h2><p>' + esc(det.sec1) + '</p>' +
    '<h2>2. Tóm tắt mô tả</h2><p>' + esc(det.sec2) + '</p>' +
    '<h2>3. Kết quả</h2><p class="hs-result">' + esc(det.sec3) + '</p>';
  if (det.other.length) {
    html += '<h2>Thông tin khác</h2><ul class="other">' +
      det.other.map(function (x) { return '<li>' + esc(x) + '</li>'; }).join('') + '</ul>';
  }
  var img = imgTag(doc);
  if (img) {
    html += '<figure>' + img +
      '<figcaption>Trang 1 của văn bản ' + esc(doc.so_hieu) + '</figcaption></figure>';
  }
  html += pdfBlockHtml(doc) +
    '<div class="actions">' +
    '<button type="button" class="btn" id="copyBtn">Sao chép link bài</button>' +
    (doc.post_url ? '<a class="btn ghost" href="' + esc(doc.post_url) +
      '" target="_blank" rel="noopener">Xem bài đã đăng trên Facebook</a>' : '') +
    '<span class="spacer"></span>' +
    '<a class="report-link" href="https://m.me/tiepvanhoangkim1" target="_blank" rel="noopener">' +
    'Báo sai nội dung / link qua Messenger Trang Văn bản XNK</a>' +
    '</div></article>';

  html += '<div id="cpRel"></div>';
  var rel = relatedDocs(doc);
  if (rel.length) {
    html += '<section class="related"><h2>Bài liên quan</h2>' +
      rel.map(function (r) {
        return '<article class="card"><h3><a href="#/bai/' + r.ma + '">' + esc(r.so_hieu) +
          '</a></h3><p class="sub">' + esc(r.ngay || '') + ' · ' + hsBadge(r) + '</p><p>' +
          esc(shortText(r.mat_hang || r.trich_yeu, 140)) + '</p></article>';
      }).join('') + '</section>';
  }
  view.innerHTML = html;
  /* Dò cặp dễ nhầm sau khi bài viết đã hiện, để lần mở đầu không phải chờ. */
  setTimeout(function () {
    var box = $('#cpRel');
    if (box && location.hash.indexOf('#/bai/' + doc.ma) === 0) box.innerHTML = cpRelatedHtml(doc);
  }, 0);

  var copyBtn = $('#copyBtn');
  if (copyBtn) copyBtn.addEventListener('click', function () {
    var url = location.href.split('#')[0] + '#/bai/' + doc.ma;
    function done() { copyBtn.textContent = 'Đã sao chép link!'; }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(url).then(done, function () {
        window.prompt('Sao chép link bài:', url);
      });
    } else window.prompt('Sao chép link bài:', url);
  });
  var driveBtn = $('#driveBtn');
  if (driveBtn) driveBtn.addEventListener('click', function () {
    var id = extractDriveId($('#driveInput').value);
    if (!id) { window.alert('Link Drive chưa đúng. Dán link dạng drive.google.com/file/d/…/view'); return; }
    var block = document.querySelector('.pdf-block');
    if (block) {
      block.innerHTML = '<h2>Xem PDF gốc</h2>' +
        '<iframe src="' + drivePreviewUrl(id) + '" title="PDF ' + esc(doc.so_hieu) +
        ' trên Google Drive" loading="lazy" allowfullscreen></iframe>' +
        '<div class="pdf-links"><a class="btn ghost" href="' + driveViewUrl(id) +
        '" target="_blank" rel="noopener">Mở trên Google Drive</a></div>' +
        '<p class="pdf-note">Đã nhúng trình xem Drive cho phiên xem này (chưa lưu vào kho).</p>';
    }
  });
  updateMeta(doc);
  window.scrollTo(0, 0);
}

function updateMeta(doc) {
  var titleEl = document.querySelector('title');
  var desc = document.querySelector('meta[name="description"]');
  var ogT = document.querySelector('meta[property="og:title"]');
  var ogD = document.querySelector('meta[property="og:description"]');
  var ogU = document.querySelector('meta[property="og:url"]');
  var baseTitle = 'Văn bản XNK — Kết quả phân tích phân loại';
  if (!doc) {
    if (titleEl) titleEl.textContent = baseTitle;
    if (desc) desc.setAttribute('content',
      'Tra cứu kết quả phân tích phân loại và xác định trước mã số hải quan — kho Văn bản XNK.');
    if (ogT) ogT.setAttribute('content', baseTitle);
    if (ogD) ogD.setAttribute('content',
      'Tra cứu kết quả phân tích phân loại và xác định trước mã số hải quan — kho Văn bản XNK.');
    if (ogU) ogU.setAttribute('content', location.href.split('#')[0]);
    return;
  }
  var short = shortText(doc.mat_hang || doc.trich_yeu, 90);
  var t = doc.so_hieu + (doc.ma_hs ? ' — HS ' + doc.ma_hs : '') + ' | Văn bản XNK';
  var d = doc.so_hieu + (doc.ma_hs ? ' — mã HS ' + doc.ma_hs : '') + '. ' + short;
  if (titleEl) titleEl.textContent = t;
  if (desc) desc.setAttribute('content', d);
  if (ogT) ogT.setAttribute('content', t);
  if (ogD) ogD.setAttribute('content', d);
  if (ogU) ogU.setAttribute('content', location.href.split('#')[0] + '#/bai/' + doc.ma);
}

/* ---------- Trang "Phân biệt mã dễ nhầm" ---------- */
var _cpShown = PAGE_SIZE;
function cpUrl(p) { return '#/phan-biet/' + p.a.ma + '-' + p.b.ma; }
function sourceLinksHtml(d) {
  var id = DRIVE[d.so_hieu];
  var h = '<a class="btn" href="#/bai/' + d.ma + '">Xem văn bản</a>';
  if (id) h += '<a class="btn ghost" href="' + driveViewUrl(id) + '" target="_blank" rel="noopener">PDF gốc</a>';
  else if (d.pdf_url) h += '<a class="btn ghost" href="' + esc(d.pdf_url) + '" target="_blank" rel="noopener">PDF gốc</a>';
  if (d.detail_url) {
    h += '<a class="btn ghost" href="' + esc(d.detail_url) + '" target="_blank" rel="noopener">Nguồn customs.gov.vn</a>';
  }
  return h;
}
function cpSideMini(d) {
  return '<div class="cmp-mini"><span class="ask-hs-pill">' + esc(d.ma_hs) + '</span>' +
    '<b>' + esc(d.so_hieu) + '</b><p>' + esc(shortText(d.mat_hang || d.trich_yeu, 110)) + '</p></div>';
}
function cpPct(sim) { return Math.round(Math.min(1, sim) * 100) + '%'; }
function cpCardHtml(g) {
  var p = g.best, more = g.pairs.length - 1;
  return '<a class="cmp-card" href="' + cpUrl(p) + '">' +
    '<div class="cmp-card-top">' + (g.seed ? '<span class="cmp-seed">Cặp mẫu</span>' : '') +
    (g.seed ? '' : '<span class="cmp-sim">Giống ' + cpPct(p.sim) + '</span>') +
    '<span class="cmp-go">So sánh →</span></div>' +
    (g.seed ? '<p class="cmp-card-title">' + esc(g.seed.title) + '</p>' : '') +
    '<div class="cmp-vs">' + cpSideMini(p.a) + '<span class="cmp-vs-mark" aria-label="khác mã">≠</span>' +
    cpSideMini(p.b) + '</div>' +
    (more > 0 ? '<p class="cmp-more">+' + more + ' cặp văn bản khác giữa hai mã này</p>' : '') +
    '</a>';
}
function renderCompareList() {
  var groups = cpData().groups;
  $('#resultInfo').textContent = 'Có ' + groups.length + ' cặp mã HS dễ nhầm, phát hiện tự động từ kho văn bản.';
  var html = '<section class="cmp-page"><h1 class="page-title">Phân biệt mã dễ nhầm</h1>' +
    '<p class="disclaimer" role="note">' + esc(NL_DISCLAIMER) + '</p>' +
    '<p class="cmp-intro">Các cặp văn bản có tên hàng, mô tả gần giống nhau nhưng được xếp vào mã HS khác nhau, ' +
    'xếp theo mức độ giống nhau. Chọn một cặp để xem hai văn bản đặt cạnh nhau và điểm khác biệt quyết định.</p>' +
    groups.slice(0, _cpShown).map(cpCardHtml).join('');
  if (groups.length > _cpShown) {
    html += '<button type="button" class="load-more" id="cpMore">Xem thêm (' + (groups.length - _cpShown) +
      ' cặp nữa)</button>';
  }
  $('#view').innerHTML = html + '</section>';
  var more = $('#cpMore');
  if (more) more.addEventListener('click', function () { _cpShown += PAGE_SIZE; renderCompareList(); });
  updateMeta(null);
  var t = document.querySelector('title');
  if (t) t.textContent = 'Phân biệt mã HS dễ nhầm | Văn bản XNK';
}
function cpTermsHtml(list) {
  return list.length ? list.map(esc).join(', ') : '<span class="cmp-none">không ghi</span>';
}
function cpSideHtml(d, det, tag) {
  return '<div class="cmp-side"><p class="cmp-side-tag">' + tag + '</p>' +
    '<p class="cmp-side-hs"><span class="ask-hs-pill">' + esc(d.ma_hs) + '</span></p>' +
    '<p class="sub"><a href="#/bai/' + d.ma + '"><b>' + esc(d.so_hieu) + '</b></a> · ' + esc(d.ngay || '') +
    ' · ' + esc(LOAI_LABEL[d.loai] || 'Văn bản') + '</p>' +
    '<h3>Tên hàng theo khai báo</h3><p>' + esc(det.sec1) + '</p>' +
    '<h3>Tóm tắt mô tả</h3><p>' + esc(det.sec2) + '</p>' +
    '<h3>Kết quả</h3><p class="hs-result">' + esc(det.sec3) + '</p>' +
    '<div class="ask-links">' + sourceLinksHtml(d) + '</div></div>';
}
function renderCompare(maA, maB) {
  var a = null, b = null;
  DOCS.forEach(function (d) {
    if (String(d.ma) === String(maA)) a = d;
    if (String(d.ma) === String(maB)) b = d;
  });
  var view = $('#view');
  if (!a || !b || a === b) {
    view.innerHTML = '<p class="empty">Không tìm thấy cặp văn bản này trong kho.</p>' +
      '<p><a href="#/phan-biet">← Danh sách mã dễ nhầm</a></p>';
    updateMeta(null);
    return;
  }
  var r = cpDiff(a, b), g = cpGroupOf(a, b), seed = null;
  CP_SEED.forEach(function (s) {
    if ((s.a === a.so_hieu && s.b === b.so_hieu) || (s.a === b.so_hieu && s.b === a.so_hieu)) seed = s;
  });
  var nA = esc(a.so_hieu.split('/')[0]), nB = esc(b.so_hieu.split('/')[0]);
  $('#resultInfo').textContent = 'So sánh hai văn bản có tên hàng gần giống nhau nhưng khác mã HS.';
  var html = '<a class="back-link" href="#/phan-biet">← Danh sách mã dễ nhầm</a>' +
    '<article class="article cmp-article">' +
    '<p class="disclaimer" role="note">' + esc(NL_DISCLAIMER) + '</p>' +
    '<h1>' + (seed ? esc(seed.title) : 'Phân biệt mã HS ' + esc(a.ma_hs) + ' và ' + esc(b.ma_hs)) + '</h1>' +
    '<p class="sub">Văn bản ' + nA + ' (' + esc(a.ma_hs) + ') và văn bản ' + nB + ' (' + esc(b.ma_hs) + ')' +
    (seed ? '' : ' · Độ giống tên hàng, mô tả: ' + cpPct(r.sim)) + '</p>';
  if (seed) {
    html += '<div class="cmp-lead"><p>' + esc(seed.lead) + '</p><ul>' +
      seed.points.map(function (x) { return '<li>' + esc(x) + '</li>'; }).join('') + '</ul></div>';
  }
  html += '<h2>Điểm khác biệt' + (seed ? ' tìm thấy trong văn bản' : ' quyết định') + '</h2>';
  if (r.diffs.length) {
    html += '<div class="cmp-diff">' + r.diffs.map(function (x) {
      return '<div class="cmp-diff-row"><p class="cmp-diff-label">' + esc(x.label) + '</p>' +
        '<p><span class="cmp-tag">' + nA + '</span>' + cpTermsHtml(x.a) + '</p>' +
        '<p><span class="cmp-tag cmp-tag-b">' + nB + '</span>' + cpTermsHtml(x.b) + '</p></div>';
    }).join('') + '</div>';
  } else {
    html += '<p>Không thấy khác biệt rõ trong tên hàng. Hãy đọc kỹ phần mô tả và kết quả của hai văn bản bên dưới.</p>';
  }
  if (r.same.length) {
    html += '<h2>Điểm giống nhau</h2><ul class="cmp-same">' +
      r.same.map(function (x) { return '<li>' + esc(x) + '</li>'; }).join('') + '</ul>';
  }
  html += '<h2>Hai văn bản đặt cạnh nhau</h2><div class="cmp-grid">' +
    cpSideHtml(a, r.da, 'Văn bản ' + nA) + cpSideHtml(b, r.db, 'Văn bản ' + nB) + '</div>' +
    '<h2>Nguồn trích dẫn</h2><ol class="cmp-cite">' + [a, b].map(function (d) {
      return '<li><a href="#/bai/' + d.ma + '"><b>' + esc(d.so_hieu) + '</b></a> ngày ' + esc(d.ngay || '') +
        ', mã HS ' + esc(d.ma_hs) +
        (d.detail_url ? ' · <a href="' + esc(d.detail_url) + '" target="_blank" rel="noopener">customs.gov.vn</a>' : '') +
        '</li>';
    }).join('') + '</ol></article>';
  var others = g ? g.pairs.filter(function (p) {
    return !((p.a === a && p.b === b) || (p.a === b && p.b === a));
  }) : [];
  if (others.length) {
    html += '<section class="related"><h2>Các cặp văn bản khác giữa hai mã này</h2>' +
      others.map(function (p) {
        return '<a class="cmp-card" href="' + cpUrl(p) + '"><div class="cmp-card-top"><span class="cmp-sim">Giống ' +
          cpPct(p.sim) + '</span><span class="cmp-go">So sánh →</span></div><div class="cmp-vs">' +
          cpSideMini(p.a) + '<span class="cmp-vs-mark" aria-label="khác mã">≠</span>' + cpSideMini(p.b) +
          '</div></a>';
      }).join('') + '</section>';
  }
  view.innerHTML = html;
  updateMeta(null);
  var t = document.querySelector('title');
  if (t) t.textContent = 'Phân biệt HS ' + a.ma_hs + ' và ' + b.ma_hs + ' | Văn bản XNK';
  window.scrollTo(0, 0);
}
function cpRelatedHtml(doc) {
  var list = cpForDoc(doc.ma).slice(0, 3);
  if (!list.length) return '';
  return '<section class="related"><h2>Dễ nhầm với</h2>' + list.map(function (x) {
    var o = x.other;
    return '<article class="card"><h3><a href="' + cpUrl(x.pair) + '">So sánh với ' + esc(o.so_hieu) +
      '</a></h3><p class="sub">' + esc(o.ngay || '') + ' · ' + hsBadge(o) + ' · ' + (x.pair.seed ? 'Cặp mẫu' : 'Giống ' + cpPct(x.pair.sim)) +
      '</p><p>' + esc(shortText(o.mat_hang || o.trich_yeu, 140)) + '</p></article>';
  }).join('') + '</section>';
}

/* ---------- Cây mã HS + thống kê (tính lười khi mở #/cay-hs) ---------- */
var HS_SECTIONS = [
  ['I', 1, 5, 'Động vật sống; các sản phẩm từ động vật'],
  ['II', 6, 14, 'Các sản phẩm thực vật'],
  ['III', 15, 15, 'Chất béo và dầu có nguồn gốc từ động vật, thực vật hoặc vi sinh vật'],
  ['IV', 16, 24, 'Thực phẩm chế biến; đồ uống, rượu và giấm; thuốc lá'],
  ['V', 25, 27, 'Khoáng sản'],
  ['VI', 28, 38, 'Sản phẩm của ngành công nghiệp hóa chất hoặc các ngành liên quan'],
  ['VII', 39, 40, 'Plastic và cao su; các sản phẩm bằng plastic và cao su'],
  ['VIII', 41, 43, 'Da sống, da thuộc, da lông và sản phẩm của chúng; hàng du lịch, túi xách'],
  ['IX', 44, 46, 'Gỗ và các mặt hàng bằng gỗ; lie; sản phẩm từ rơm, vật liệu tết bện'],
  ['X', 47, 49, 'Bột giấy; giấy, bìa và các sản phẩm của chúng; sản phẩm in'],
  ['XI', 50, 63, 'Nguyên liệu dệt và các sản phẩm dệt'],
  ['XII', 64, 67, 'Giày dép, mũ, ô dù, ba toong, roi; lông vũ chế biến; hoa nhân tạo'],
  ['XIII', 68, 70, 'Sản phẩm bằng đá, thạch cao, xi măng, amiăng, mica; đồ gốm, sứ; thủy tinh'],
  ['XIV', 71, 71, 'Ngọc trai, đá quý, kim loại quý và sản phẩm của chúng; đồ trang sức'],
  ['XV', 72, 83, 'Kim loại cơ bản và các sản phẩm bằng kim loại cơ bản'],
  ['XVI', 84, 85, 'Máy và thiết bị cơ khí; máy và thiết bị điện; bộ phận của chúng'],
  ['XVII', 86, 89, 'Xe cộ, phương tiện bay, tàu thuyền và thiết bị vận tải liên quan'],
  ['XVIII', 90, 92, 'Dụng cụ quang học, đo lường, y tế; đồng hồ; nhạc cụ'],
  ['XIX', 93, 93, 'Vũ khí và đạn; bộ phận và phụ kiện của chúng'],
  ['XX', 94, 96, 'Các mặt hàng khác'],
  ['XXI', 97, 97, 'Các tác phẩm nghệ thuật, đồ sưu tầm và đồ cổ']
];
var HS_CHAPTER_NAMES = {
  '01': 'Động vật sống', '02': 'Thịt và phụ phẩm dạng thịt ăn được sau giết mổ',
  '03': 'Cá, động vật giáp xác, thân mềm và thủy sinh khác',
  '04': 'Sữa, trứng, mật ong và sản phẩm ăn được gốc động vật', '05': 'Sản phẩm gốc động vật khác',
  '06': 'Cây sống, củ, rễ, hoa cắt và cành lá trang trí', '07': 'Rau và một số loại củ, rễ ăn được',
  '08': 'Quả và quả hạch ăn được', '09': 'Cà phê, chè và các loại gia vị', '10': 'Ngũ cốc',
  '11': 'Sản phẩm xay xát; malt; tinh bột; gluten', '12': 'Hạt và quả có dầu; hạt giống; cây công nghiệp, dược liệu',
  '13': 'Nhựa cánh kiến, gôm, nhựa cây và chiết xuất thực vật', '14': 'Vật liệu thực vật để tết bện; sản phẩm thực vật khác',
  '15': 'Chất béo và dầu động vật, thực vật', '16': 'Chế phẩm từ thịt, cá, động vật thủy sinh',
  '17': 'Đường và các loại kẹo đường', '18': 'Ca cao và chế phẩm từ ca cao',
  '19': 'Chế phẩm từ ngũ cốc, bột, tinh bột hoặc sữa; các loại bánh', '20': 'Chế phẩm từ rau, quả, quả hạch',
  '21': 'Các chế phẩm ăn được khác', '22': 'Đồ uống, rượu và giấm', '23': 'Phế liệu ngành thực phẩm; thức ăn chăn nuôi',
  '24': 'Thuốc lá và nguyên liệu thay thế', '25': 'Muối; lưu huỳnh; đất, đá; thạch cao, vôi, xi măng',
  '26': 'Quặng, xỉ và tro', '27': 'Nhiên liệu khoáng, dầu khoáng và sản phẩm chưng cất', '28': 'Hóa chất vô cơ',
  '29': 'Hóa chất hữu cơ', '30': 'Dược phẩm', '31': 'Phân bón', '32': 'Thuốc nhuộm, thuốc màu, sơn, véc ni, mực',
  '33': 'Tinh dầu, nước hoa, mỹ phẩm và chế phẩm vệ sinh', '34': 'Xà phòng, chất hoạt động bề mặt, chế phẩm giặt rửa, bôi trơn, sáp',
  '35': 'Chất chứa albumin, tinh bột biến tính, keo, enzim', '36': 'Chất nổ, pháo, diêm', '37': 'Vật liệu ảnh, điện ảnh',
  '38': 'Các sản phẩm hóa chất khác', '39': 'Plastic và sản phẩm bằng plastic', '40': 'Cao su và sản phẩm bằng cao su',
  '41': 'Da sống và da thuộc', '42': 'Sản phẩm bằng da thuộc; hàng du lịch, túi xách', '43': 'Da lông và da lông nhân tạo',
  '44': 'Gỗ và mặt hàng bằng gỗ; than củi', '45': 'Lie và sản phẩm bằng lie', '46': 'Sản phẩm từ rơm, cỏ giấy, song mây',
  '47': 'Bột giấy; giấy loại thu hồi', '48': 'Giấy và bìa; sản phẩm bằng giấy, bìa', '49': 'Sách, báo, tranh ảnh và sản phẩm in',
  '50': 'Tơ tằm', '51': 'Lông cừu, lông động vật', '52': 'Bông', '53': 'Xơ dệt gốc thực vật khác',
  '54': 'Sợi filament nhân tạo', '55': 'Xơ sợi staple nhân tạo', '56': 'Mền xơ, phớt, vải không dệt; sợi xe, thừng, cáp',
  '57': 'Thảm và hàng dệt trải sàn', '58': 'Vải dệt thoi đặc biệt, ren, hàng thêu',
  '59': 'Vải dệt đã ngâm tẩm, tráng, phủ, ép lớp; hàng dệt dùng trong công nghiệp', '60': 'Vải dệt kim hoặc móc',
  '61': 'Quần áo dệt kim hoặc móc', '62': 'Quần áo không dệt kim hoặc móc', '63': 'Hàng dệt hoàn thiện khác; quần áo cũ',
  '64': 'Giày, dép và bộ phận', '65': 'Mũ và vật đội đầu', '66': 'Ô, dù, ba toong, roi', '67': 'Lông vũ chế biến; hoa nhân tạo; tóc người',
  '68': 'Sản phẩm bằng đá, thạch cao, xi măng, amiăng, mica', '69': 'Đồ gốm, sứ', '70': 'Thủy tinh và sản phẩm bằng thủy tinh',
  '71': 'Ngọc trai, đá quý, kim loại quý; đồ trang sức', '72': 'Sắt và thép', '73': 'Sản phẩm bằng sắt hoặc thép',
  '74': 'Đồng và sản phẩm bằng đồng', '75': 'Niken và sản phẩm bằng niken', '76': 'Nhôm và sản phẩm bằng nhôm',
  '78': 'Chì và sản phẩm bằng chì', '79': 'Kẽm và sản phẩm bằng kẽm', '80': 'Thiếc và sản phẩm bằng thiếc',
  '81': 'Kim loại cơ bản khác; gốm kim loại', '82': 'Dụng cụ, dao, kéo, bộ đồ ăn bằng kim loại cơ bản',
  '83': 'Hàng tạp hóa bằng kim loại cơ bản', '84': 'Máy và thiết bị cơ khí; bộ phận của chúng',
  '85': 'Máy và thiết bị điện; bộ phận của chúng', '86': 'Đầu máy, toa xe lửa; thiết bị đường sắt',
  '87': 'Xe cộ (trừ đường sắt) và bộ phận, phụ kiện', '88': 'Phương tiện bay, tàu vũ trụ', '89': 'Tàu thủy, thuyền và kết cấu nổi',
  '90': 'Dụng cụ quang học, đo lường, kiểm tra, y tế', '91': 'Đồng hồ và bộ phận', '92': 'Nhạc cụ',
  '93': 'Vũ khí và đạn', '94': 'Đồ nội thất; bộ đồ giường, đệm; đèn; nhà lắp ghép', '95': 'Đồ chơi, thiết bị trò chơi, dụng cụ thể thao',
  '96': 'Các mặt hàng khác', '97': 'Tác phẩm nghệ thuật, đồ sưu tầm, đồ cổ'
};
function sectionOfChapter(ch) {
  var n = +ch;
  for (var i = 0; i < HS_SECTIONS.length; i++) {
    if (n >= HS_SECTIONS[i][1] && n <= HS_SECTIONS[i][2]) return HS_SECTIONS[i];
  }
  return null;
}
function inBranch(d, br) {
  var dg = hsDigits(d.ma_hs);
  if (br.type === 'nhom') return dg.length >= 4 && dg.slice(0, 4) === br.key;
  if (dg.length < 2) return false;
  var s = sectionOfChapter(dg.slice(0, 2));
  return !!s && s[0] === br.key;
}
function branchLabel(br) {
  if (br.type === 'nhom') return 'Nhóm ' + br.key;
  var s = HS_SECTIONS.filter(function (x) { return x[0] === br.key; })[0];
  return 'Phần ' + br.key + (s ? ' (Chương ' + pad2(s[1]) + (s[2] !== s[1] ? '–' + pad2(s[2]) : '') + ')' : '');
}
function pad2(n) { return (n < 10 ? '0' : '') + n; }
var _hsTree = null, _hsTreeOf = null;
function hsTreeData() {
  if (_hsTree && _hsTreeOf === DOCS) return _hsTree;
  var secs = HS_SECTIONS.map(function (s) { return { id: s[0], from: s[1], to: s[2], name: s[3], n: 0, ch: {} }; });
  var other = { id: '', name: 'Chương khác', n: 0, ch: {} }, noHs = 0;
  DOCS.forEach(function (d) {
    var dg = hsDigits(d.ma_hs);
    if (dg.length < 2) { noHs++; return; }
    var c = dg.slice(0, 2), s = sectionOfChapter(c), sec = s ? secs[HS_SECTIONS.indexOf(s)] : other;
    sec.n++;
    var ch = sec.ch[c] = sec.ch[c] || { id: c, n: 0, h: {} };
    ch.n++;
    if (dg.length >= 4) ch.h[dg.slice(0, 4)] = (ch.h[dg.slice(0, 4)] || 0) + 1;
  });
  if (other.n) secs.push(other);
  _hsTree = { secs: secs, noHs: noHs };
  _hsTreeOf = DOCS;
  return _hsTree;
}
var _treeOpen = {};
function treeNodeHtml(id, label, count, href, childrenHtml, followK) {
  var open = !!_treeOpen[id], hasKids = !!childrenHtml;
  return '<li class="tree-node' + (count ? '' : ' is-empty') + '"><div class="tree-row">' +
    (hasKids ? '<button type="button" class="tree-toggle" data-node="' + id + '" aria-expanded="' + open +
      '" aria-controls="tn-' + id + '" aria-label="' + (open ? 'Thu gọn' : 'Mở rộng') + '">' + (open ? '−' : '+') + '</button>'
      : '<span class="tree-spacer"></span>') +
    (count ? '<a class="tree-link" href="' + href + '">' : '<span class="tree-link">') +
    '<span class="tree-name">' + label + '</span><span class="tree-count">' + count + '</span>' +
    (count ? '</a>' : '</span>') +
    (followK ? newBadgeHtml(followK) + followBtnHtml(followK, 'Theo dõi', 'follow-sm') : '') + '</div>' +
    (hasKids ? '<ul id="tn-' + id + '"' + (open ? '' : ' hidden') + '>' + childrenHtml + '</ul>' : '') + '</li>';
}
function hsTreeHtml() {
  var t = hsTreeData();
  var html = t.secs.map(function (sec) {
    var kids = Object.keys(sec.ch).sort().map(function (c) {
      var ch = sec.ch[c];
      var hk = Object.keys(ch.h).sort().map(function (h) {
        return treeNodeHtml('h' + h, '<b>Nhóm ' + h + '</b>', ch.h[h], '#/nhanh/nhom/' + h, '', h);
      }).join('');
      return treeNodeHtml('c' + c, '<b>Chương ' + c + '</b> · ' + esc(HS_CHAPTER_NAMES[c] || ''), ch.n, '#/chuong/' + c, hk, c);
    }).join('');
    var label = sec.id ? '<b>Phần ' + sec.id + '</b> · ' + esc(sec.name) +
      ' <small>(Chương ' + pad2(sec.from) + (sec.to !== sec.from ? '–' + pad2(sec.to) : '') + ')</small>' : '<b>' + esc(sec.name) + '</b>';
    return treeNodeHtml('s' + (sec.id || 'x'), label, sec.n, sec.id ? '#/nhanh/phan/' + sec.id : '#/chuong', kids);
  }).join('');
  html += treeNodeHtml('none', '<b>Chưa có mã HS</b>', t.noHs, '#/chuong/khong-co-ma', '');
  return '<ul class="hs-tree">' + html + '</ul>';
}
function docLoaiKey(d) { return d.loai === 'phan_tich_phan_loai' || d.loai === 'xac_dinh_truoc_ma_so' ? d.loai : 'khac'; }
var _stats = null, _statsOf = null;
function statsData() {
  if (_stats && _statsOf === DOCS) return _stats;
  var st = { total: DOCS.length, withHs: 0, loai: { phan_tich_phan_loai: 0, xac_dinh_truoc_ma_so: 0, khac: 0 },
    years: {}, months: {}, chapters: {}, newest: [] };
  var latest = 0;
  DOCS.forEach(function (d) {
    var dg = hsDigits(d.ma_hs);
    if (dg.length >= 2) { st.withHs++; st.chapters[dg.slice(0, 2)] = (st.chapters[dg.slice(0, 2)] || 0) + 1; }
    st.loai[docLoaiKey(d)]++;
    var t = parseDate(d.ngay);
    if (!t) return;
    var dt = new Date(t), y = dt.getFullYear(), mk = y + '-' + pad2(dt.getMonth() + 1);
    st.years[y] = (st.years[y] || 0) + 1;
    st.months[mk] = (st.months[mk] || 0) + 1;
    if (t > latest) latest = t;
  });
  var end = new Date(Math.max(latest, Date.now()));
  st.monthList = [];
  for (var i = 11; i >= 0; i--) {
    var m = new Date(end.getFullYear(), end.getMonth() - i, 1);
    var k = m.getFullYear() + '-' + pad2(m.getMonth() + 1);
    st.monthList.push({ k: k, label: pad2(m.getMonth() + 1) + '/' + String(m.getFullYear()).slice(2), n: st.months[k] || 0 });
  }
  st.topCh = Object.keys(st.chapters).map(function (c) { return { c: c, n: st.chapters[c] }; })
    .sort(function (a, b) { return b.n - a.n || (a.c < b.c ? -1 : 1); }).slice(0, 10);
  st.newest = DOCS.slice().sort(function (a, b) { return parseDate(b.ngay) - parseDate(a.ngay); }).slice(0, 10);
  _stats = st; _statsOf = DOCS;
  return st;
}
function hbarHtml(rows) {
  var max = Math.max.apply(null, rows.map(function (r) { return r.n; }).concat([1]));
  return rows.map(function (r) {
    var w = Math.max(1, Math.round(r.n / max * 100));
    var inner = '<span class="hbar-label" title="' + esc(r.title || r.label) + '">' + r.label + '</span>' +
      '<svg viewBox="0 0 100 12" preserveAspectRatio="none" aria-hidden="true"><rect x="0" y="1" height="10" rx="2" width="' + w + '"></rect></svg>' +
      '<span class="hbar-n">' + r.n + '</span>';
    return r.href ? '<a class="hbar-row" href="' + r.href + '">' + inner + '</a>' : '<div class="hbar-row">' + inner + '</div>';
  }).join('');
}
function monthChartSvg(list) {
  var W = 360, H = 170, top = 18, bottom = 30, gap = 6, bw = (W - gap * 13) / 12;
  var max = Math.max.apply(null, list.map(function (m) { return m.n; }).concat([1]));
  var svg = '<svg class="month-chart" viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="Số văn bản theo tháng, 12 tháng gần nhất">';
  svg += '<line x1="0" x2="' + W + '" y1="' + (H - bottom) + '" y2="' + (H - bottom) + '" stroke="#d9e1e8"></line>';
  list.forEach(function (m, i) {
    var h = Math.round(m.n / max * (H - top - bottom)), x = gap + i * (bw + gap), y = H - bottom - h;
    svg += '<g><title>Tháng ' + m.label + ': ' + m.n + ' văn bản</title>' +
      '<rect x="' + x.toFixed(1) + '" y="' + y + '" width="' + bw.toFixed(1) + '" height="' + h + '" rx="3"' +
      (i === list.length - 1 ? ' class="is-last"' : '') + '></rect>' +
      '<text class="v" x="' + (x + bw / 2).toFixed(1) + '" y="' + (y - 4) + '" text-anchor="middle">' + m.n + '</text>' +
      '<text x="' + (x + bw / 2).toFixed(1) + '" y="' + (H - bottom + 14) + '" text-anchor="middle">' + m.label + '</text></g>';
  });
  return svg + '</svg>';
}
function renderTreePage(scrollToStats) {
  var st = statsData();
  $('#resultInfo').textContent = '';
  var pct = st.total ? Math.round(st.withHs / st.total * 100) : 0;
  var html = '<section class="tree-page"><h1 class="page-title">Cây mã HS &amp; thống kê kho</h1>' +
    '<p class="cmp-intro">Duyệt kho văn bản theo Phần → Chương → Nhóm của Biểu thuế. Số bên phải là số văn bản trong kho thuộc nhánh đó; ' +
    'bấm vào tên nhánh để xem danh sách văn bản.</p>' +
    '<div class="stats-grid" id="thongKe">' +
    '<div class="stat-card"><b>' + st.total + '</b><span>Tổng số văn bản</span></div>' +
    '<div class="stat-card"><b>' + st.withHs + '</b><span>Có mã HS (' + pct + '%)</span></div>' +
    '<div class="stat-card"><b>' + st.loai.phan_tich_phan_loai + '</b><span>Phân tích phân loại</span></div>' +
    '<div class="stat-card"><b>' + st.loai.xac_dinh_truoc_ma_so + '</b><span>Xác định trước mã số</span></div>' +
    '<div class="stat-card"><b>' + st.loai.khac + '</b><span>Văn bản khác</span></div></div>' +
    '<div class="stats-panel"><h2>Cây mã HS</h2><div class="tree-tools">' +
    '<button type="button" id="treeOpenAll">Mở tất cả</button><button type="button" id="treeCloseAll">Thu gọn tất cả</button></div>' +
    '<div id="hsTree">' + hsTreeHtml() + '</div></div>' +
    '<div class="stats-panel"><h2>Số văn bản theo tháng (12 tháng gần nhất)</h2>' + monthChartSvg(st.monthList) + '</div>' +
    '<div class="stats-cols"><div class="stats-panel"><h2>Top 10 chương được phân loại nhiều nhất</h2>' +
    hbarHtml(st.topCh.map(function (x) {
      return { label: 'Chương ' + x.c + ' · ' + esc(HS_CHAPTER_NAMES[x.c] || ''), title: 'Chương ' + x.c + ' · ' + (HS_CHAPTER_NAMES[x.c] || ''),
        n: x.n, href: '#/chuong/' + x.c };
    })) + '</div>' +
    '<div class="stats-panel"><h2>Số văn bản theo năm</h2>' +
    hbarHtml(Object.keys(st.years).sort().reverse().map(function (y) { return { label: 'Năm ' + y, n: st.years[y] }; })) +
    '</div></div>' +
    '<div class="stats-panel"><h2>Mới nhất</h2>' + st.newest.map(function (d) {
      return '<article class="card"><h3><a href="#/bai/' + d.ma + '">' + esc(d.so_hieu) + '</a></h3><p class="sub">' +
        esc(d.ngay || '') + ' · ' + loaiBadge(d) + ' ' + hsFollowPill(d) + '</p><p>' +
        esc(shortText(d.mat_hang || d.trich_yeu, 140)) + '</p></article>';
    }).join('') + '</div></section>';
  var view = $('#view');
  view.innerHTML = html;
  function setAll(open) {
    view.querySelectorAll('.tree-toggle').forEach(function (b) { setNode(b, open); });
  }
  function setNode(b, open) {
    var id = b.getAttribute('data-node'), ul = document.getElementById('tn-' + id);
    _treeOpen[id] = open;
    b.setAttribute('aria-expanded', String(open));
    b.setAttribute('aria-label', open ? 'Thu gọn' : 'Mở rộng');
    b.textContent = open ? '−' : '+';
    if (ul) ul.hidden = !open;
  }
  $('#hsTree').addEventListener('click', function (e) {
    var b = e.target.closest('.tree-toggle');
    if (b) setNode(b, b.getAttribute('aria-expanded') !== 'true');
  });
  $('#treeOpenAll').addEventListener('click', function () { setAll(true); });
  $('#treeCloseAll').addEventListener('click', function () { setAll(false); });
  updateMeta(null);
  var t = document.querySelector('title');
  if (t) t.textContent = 'Cây mã HS & thống kê | Văn bản XNK';
  if (scrollToStats) { var el = $('#thongKe'); if (el && el.scrollIntoView) el.scrollIntoView(); }
  else window.scrollTo(0, 0);
}

/* ================= Theo dõi mã HS (chỉ lưu trên trình duyệt này) ================= */
/* Mã theo dõi lưu dạng chữ số: 2 số = Chương, 4 số = Nhóm (khớp tiền tố), dài hơn = đúng mã đó.
   "Mốc đã xem" là tập ma của các văn bản đã hiện cho người dùng; lần đầu mở site lấy cả kho làm mốc. */
var FOLLOW_KEY = 'vbxnk_follows_v1', SEEN_KEY = 'vbxnk_seen_v1';
var _follows = null, _seen = null;
function follows() {
  if (_follows) return _follows;
  try { _follows = JSON.parse(lsGet(FOLLOW_KEY) || '[]'); } catch (e) { _follows = []; }
  if (!Array.isArray(_follows)) _follows = [];
  _follows = _follows.filter(function (k) { return /^\d{2,}$/.test(k); });
  return _follows;
}
function isFollowed(k) { return follows().indexOf(k) !== -1; }
function followMatch(k, hs) {
  var dg = hsDigits(hs);
  if (!dg || !k) return false;
  return k.length <= 4 ? dg.indexOf(k) === 0 : dg === k;
}
function followDocs(k) {
  return DOCS.filter(function (d) { return followMatch(k, d.ma_hs); })
    .sort(function (a, b) { return parseDate(b.ngay) - parseDate(a.ngay); });
}
function saveSeen() { lsSet(SEEN_KEY, JSON.stringify(Object.keys(_seen))); }
function seenSet() {
  if (_seen) return _seen;
  var raw = lsGet(SEEN_KEY), arr = null;
  try { arr = raw == null ? null : JSON.parse(raw); } catch (e) { arr = null; }
  _seen = {};
  if (Array.isArray(arr)) arr.forEach(function (m) { _seen[m] = 1; });
  else { DOCS.forEach(function (d) { _seen[d.ma] = 1; }); saveSeen(); }
  return _seen;
}
function markSeen(docs) {
  if (lsGet(SEEN_KEY) != null) _seen = null;
  var st = seenSet(), changed = false;
  docs.forEach(function (d) { if (!st[d.ma]) { st[d.ma] = 1; changed = true; } });
  if (changed) saveSeen();
}
function newDocs(k) {
  var st = seenSet();
  return followDocs(k).filter(function (d) { return !st[d.ma]; });
}
function totalNew() {
  var st = seenSet(), fs = follows(), n = 0;
  if (!fs.length) return 0;
  DOCS.forEach(function (d) {
    if (!st[d.ma] && fs.some(function (k) { return followMatch(k, d.ma_hs); })) n++;
  });
  return n;
}
/* Bắt đầu theo dõi thì coi các văn bản hiện có của mã đó là đã xem: chỉ báo văn bản về sau. */
function toggleFollow(k, on) {
  if (lsGet(FOLLOW_KEY) != null) _follows = null;
  var fs = follows(), i = fs.indexOf(k);
  if (on === undefined) on = i === -1;
  if (on && i === -1) {
    markSeen(followDocs(k).filter(function (d) {
      return !fs.some(function (f) { return followMatch(f, d.ma_hs); });
    }));
    fs.push(k);
  }
  else if (!on && i !== -1) fs.splice(i, 1);
  lsSet(FOLLOW_KEY, JSON.stringify(fs));
  return on;
}
function hsDisplay(k) {
  for (var i = 0; i < DOCS.length; i++) if (hsDigits(DOCS[i].ma_hs) === k) return DOCS[i].ma_hs;
  return k.length === 8 ? k.slice(0, 4) + '.' + k.slice(4, 6) + '.' + k.slice(6) : k;
}
function followLabel(k) {
  if (k.length === 2) return 'Chương ' + k;
  if (k.length === 4) return 'Nhóm ' + k;
  return 'Mã HS ' + hsDisplay(k);
}
function followName(k) {
  var c = k.slice(0, 2), n = HS_CHAPTER_NAMES[c] || '';
  if (k.length === 2) return n;
  return 'Chương ' + c + (n ? ' · ' + n : '');
}
function followTitle(k, on) { return (on ? 'Bỏ theo dõi ' : 'Theo dõi ') + followLabel(k); }
function followBtnHtml(k, label, cls) {
  var on = isFollowed(k);
  return '<button type="button" class="follow-btn' + (cls ? ' ' + cls : '') + (on ? ' is-on' : '') +
    '" data-follow="' + k + '" data-label="' + esc(label) + '" aria-pressed="' + on + '" title="' +
    esc(followTitle(k, on)) + '">' + (on ? 'Đang theo dõi ✓' : esc(label)) + '</button>';
}
/* Mã HS dạng pill bấm được để theo dõi đúng mã đó. */
function hsFollowPill(d, cls) {
  var k = hsDigits(d.ma_hs);
  if (k.length < 2) return cls ? '<span class="' + cls + '">' + esc(d.ma_hs || '') + '</span>' : hsBadge(d);
  var on = isFollowed(k);
  return '<button type="button" class="' + (cls || 'hs-badge') + ' hs-follow' + (on ? ' is-on' : '') +
    '" data-follow="' + k + '" data-pill="1" aria-pressed="' + on + '" title="' + esc(followTitle(k, on)) + '">' +
    (cls ? '' : 'HS ') + esc(d.ma_hs) + ' <small>' + (on ? 'Đang theo dõi ✓' : '+ Theo dõi') + '</small></button>';
}
function newBadgeHtml(k) {
  if (!isFollowed(k)) return '';
  var n = newDocs(k).length;
  return n ? '<span class="new-badge" data-new="' + k + '" title="' + n + ' văn bản mới từ lần xem trước">' + n + ' mới</span>' : '';
}
function refreshFollowButtons(k) {
  var on = isFollowed(k);
  document.querySelectorAll('[data-follow="' + k + '"]').forEach(function (b) {
    b.classList.toggle('is-on', on);
    b.setAttribute('aria-pressed', String(on));
    b.setAttribute('title', followTitle(k, on));
    if (b.getAttribute('data-pill')) { var sm = b.querySelector('small'); if (sm) sm.textContent = on ? 'Đang theo dõi ✓' : '+ Theo dõi'; }
    else b.textContent = on ? 'Đang theo dõi ✓' : b.getAttribute('data-label');
  });
  document.querySelectorAll('.new-badge[data-new="' + k + '"]').forEach(function (b) { b.remove(); });
}
function updateFollowBadge() {
  var b = document.getElementById('followBadge');
  if (!b) return;
  var n = totalNew();
  b.textContent = n > 99 ? '99+' : String(n);
  b.hidden = !n;
  var a = b.closest('a');
  if (a) a.setAttribute('aria-label', 'Đang theo dõi' + (n ? ', ' + n + ' văn bản mới' : ''));
}
function followHref(k) {
  if (k.length === 2) return '#/chuong/' + k;
  if (k.length === 4) return '#/nhanh/nhom/' + k;
  return '?q=' + encodeURIComponent(hsDisplay(k)) + '#/';
}
var _followSnap = null;
function renderFollowPage() {
  $('#resultInfo').textContent = '';
  var fs = follows().slice(), seen = seenSet(), shown = [];
  if (!_followSnap) {
    _followSnap = {};
    DOCS.forEach(function (d) { if (!seen[d.ma]) _followSnap[d.ma] = 1; });
  }
  var st = {};
  DOCS.forEach(function (d) { if (!_followSnap[d.ma]) st[d.ma] = 1; });
  var html = '<section class="follow-page"><h1 class="page-title">Đang theo dõi</h1>';
  if (!fs.length) {
    html += '<div class="follow-empty"><p>Bạn chưa theo dõi mã HS nào. Bấm <b>Theo dõi</b> cạnh mã HS ở trang văn bản, ' +
      'ở Chương/Nhóm trong <a href="#/cay-hs">cây mã HS</a> hoặc trên mã HS của kết quả tra cứu. Mỗi lần quay lại, ' +
      'chuông ở đầu trang sẽ báo số văn bản mới thuộc các mã bạn theo dõi.</p>' +
      '<h2>Gợi ý: các chương có nhiều văn bản nhất trong kho</h2><ul class="follow-suggest">' +
      statsData().topCh.slice(0, 5).map(function (x) {
        return '<li><a href="#/chuong/' + x.c + '"><b>Chương ' + x.c + '</b> · ' + esc(HS_CHAPTER_NAMES[x.c] || '') + '</a>' +
          '<span class="tree-count">' + x.n + ' văn bản</span>' + followBtnHtml(x.c, 'Theo dõi', 'follow-sm') + '</li>';
      }).join('') + '</ul></div>';
  } else {
    html += '<div class="follow-tools"><button type="button" class="btn ghost" id="seenAll">Đánh dấu đã xem hết</button></div>' +
      '<ul class="follow-list">' + fs.map(function (k) {
        var all = followDocs(k), fresh = all.filter(function (d) { return !st[d.ma]; });
        var latest = fresh.concat(all.filter(function (d) { return st[d.ma]; })).slice(0, 5), nNew = fresh.length;
        shown = shown.concat(all);
        var name = followName(k);
        return '<li class="follow-item"><div class="follow-head"><div class="follow-title"><b>' + esc(followLabel(k)) + '</b>' +
          (name ? '<span>' + esc(name) + '</span>' : '') + '</div>' +
          '<span class="tree-count">' + all.length + ' văn bản</span>' +
          (nNew ? '<span class="new-badge" data-new="' + k + '">' + nNew + ' mới</span>' : '') +
          '<button type="button" class="follow-btn follow-sm" data-unfollow="' + k + '">Bỏ theo dõi</button></div>' +
          (latest.length ? '<ul class="follow-docs">' + latest.map(function (d) {
            return '<li><a href="#/bai/' + d.ma + '"><b>' + esc(d.so_hieu) + '</b></a>' +
              (st[d.ma] ? '' : ' <span class="new-tag">Mới</span>') + ' · ' + esc(d.ngay || '') + ' · HS ' + esc(d.ma_hs) +
              '<br><span class="follow-goods">' + esc(shortText(d.mat_hang || d.trich_yeu, 120)) + '</span></li>';
          }).join('') + '</ul>' : '<p class="empty">Chưa có văn bản nào trong kho thuộc mã này.</p>') +
          (all.length > latest.length ? '<p class="follow-more"><a href="' + followHref(k) + '">Xem tất cả ' + all.length +
            ' văn bản →</a></p>' : '') + '</li>';
      }).join('') + '</ul>';
  }
  html += '<p class="follow-note">Danh sách theo dõi chỉ lưu trên trình duyệt này.</p></section>';
  $('#view').innerHTML = html;
  markSeen(shown);
  updateFollowBadge();
  var sa = $('#seenAll');
  if (sa) sa.addEventListener('click', function () {
    markSeen(DOCS); _followSnap = {}; updateFollowBadge();
    document.querySelectorAll('#view .new-badge, #view .new-tag').forEach(function (b) { b.remove(); });
  });
  updateMeta(null);
  var t = document.querySelector('title');
  if (t) t.textContent = 'Đang theo dõi | Văn bản XNK';
  window.scrollTo(0, 0);
}
function onFollowClick(e) {
  var u = e.target.closest('[data-unfollow]');
  if (u) { toggleFollow(u.getAttribute('data-unfollow'), false); updateFollowBadge(); renderFollowPage(); return; }
  var b = e.target.closest('[data-follow]');
  if (!b) return;
  e.preventDefault();
  var k = b.getAttribute('data-follow');
  toggleFollow(k);
  if (_followSnap) followDocs(k).forEach(function (d) { delete _followSnap[d.ma]; });
  refreshFollowButtons(k);
  updateFollowBadge();
  if (/^#\/theo-doi/.test(location.hash)) renderFollowPage();
}

/* ================= Định tuyến & khởi động ================= */

function route() {
  var h = location.hash || '#/';
  var m = /^#\/bai\/(\d+)/.exec(h);
  var pb = /^#\/phan-biet(?:\/(\d+)-(\d+))?/.exec(h);
  var tree = /^#\/(cay-hs|thong-ke)\/?$/.test(h), fd = /^#\/theo-doi\/?$/.test(h);
  document.body.classList.toggle('is-detail', !!m || !!pb || tree || fd);
  if (m) { renderDetail(m[1]); return; }
  if (pb) { if (pb[1]) renderCompare(pb[1], pb[2]); else renderCompareList(); return; }
  if (tree) { renderTreePage(h.indexOf('thong-ke') !== -1); return; }
  if (fd) { renderFollowPage(); return; }
  _followSnap = null;
  var nb = /^#\/nhanh\/(phan|nhom)\/([0-9IVX]+)/.exec(h);
  if (nb) {
    clearAsk();
    state.query = ''; state.shown = PAGE_SIZE;
    var qb = $('#q'); if (qb) qb.value = '';
    state.branch = { type: nb[1], key: nb[2] };
    state.chapter = nb[1] === 'nhom' ? nb[2].slice(0, 2) : '';
    if (nb[1] === 'nhom' && isFollowed(nb[2])) { markSeen(followDocs(nb[2])); updateFollowBadge(); }
    syncQueryToUrl(); syncFilterControls();
    renderList();
    return;
  }
  state.branch = null;
  var c = /^#\/chuong\/([0-9]{2}|khong-co-ma)/.exec(h);
  if (c) {
    clearAsk();
    state.chapter = c[1] === 'khong-co-ma' ? '' : c[1];
    if (isFollowed(c[1])) { markSeen(followDocs(c[1])); updateFollowBadge(); }
    if (/[?&]hoi=/.test(location.search)) { state.query = ''; syncQueryToUrl(); }
    state.query = '';
    var q = $('#q'); if (q) q.value = '';
    if (c[1] === 'khong-co-ma') {
      /* Chương "chưa có mã HS": lọc bằng tay vì chapter rỗng. */
      var results = [];
      DOCS.forEach(function (d) { if (!chapterOf(d)) results.push({ doc: d, score: 0, reasons: [] }); });
      results.sort(function (a, b) { return parseDate(b.doc.ngay) - parseDate(a.doc.ngay); });
      _lastResults = results;
      $('#resultInfo').textContent = 'Tìm thấy ' + results.length + ' văn bản chưa có mã HS.';
      $('#view').innerHTML = results.slice(0, state.shown).map(cardHtml).join('') ||
        '<p class="empty">Không có văn bản nào.</p>';
      updateMeta(null);
      return;
    }
    syncFilterControls();
    renderList();
    return;
  }
  if (h === '#/chuong') { renderChapters(); return; }
  state.chapter = '';
  syncFilterControls();
  renderList();
}

function syncFilterControls() {
  var fl = $('#fLoai'); if (fl) fl.value = state.loai;
  var fc = $('#fChuong'); if (fc) fc.value = state.chapter;
  var fy = $('#fNam'); if (fy) fy.value = state.year;
}

function fillFilterOptions() {
  var chapters = {}, years = {};
  DOCS.forEach(function (d) {
    var ch = chapterOf(d);
    if (ch) chapters[ch] = (chapters[ch] || 0) + 1;
    var y = (function () {
      var m = /(\d{4})\s*$/.exec(String(d.ngay || ''));
      return m ? m[1] : '';
    })();
    if (y) years[y] = (years[y] || 0) + 1;
  });
  var fc = $('#fChuong');
  Object.keys(chapters).sort().forEach(function (ch) {
    var o = document.createElement('option');
    o.value = ch; o.textContent = 'Chương ' + ch + ' (' + chapters[ch] + ')';
    fc.appendChild(o);
  });
  var fy = $('#fNam');
  Object.keys(years).sort().reverse().forEach(function (y) {
    var o = document.createElement('option');
    o.value = y; o.textContent = 'Năm ' + y + ' (' + years[y] + ')';
    fy.appendChild(o);
  });
}

/* Dropdown gợi ý nhóm theo loại + điều hướng bàn phím (chuẩn ARIA combobox:
   ↑/↓ di chuyển, Enter chọn, Esc đóng và khôi phục truy vấn gốc, Tab đóng
   mà không chọn). Khi di chuyển bằng phím, ô nhập hiện tạm gợi ý đang chọn. */
/* ---------- Ô tra cứu hợp nhất: gợi ý khi gõ (cơ chế bước 3) ---------- */
var _suggItems = [], _suggActive = -1, _qBeforeNav = '';
function hideSuggestions() {
  var box = $('#suggest');
  if (box) { box.hidden = true; box.innerHTML = ''; }
  _suggItems = []; _suggActive = -1;
  var q = $('#q');
  if (q) {
    q.setAttribute('aria-expanded', 'false');
    q.removeAttribute('aria-activedescendant');
  }
}
/* Ô trống: tìm gần đây + tìm nhiều; đang gõ: gợi ý tên hàng, chất liệu, công dụng,
   mã HS, số hiệu; nếu không có thì dùng gợi ý từ khóa cũ (chương, số hiệu…). */
function unifiedSuggest(v) {
  if (!String(v || '').trim()) return suggest('');
  var items = askSuggest(v);
  return items.length ? items : suggest(v);
}
function showSuggestions() {
  var box = $('#suggest'), q = $('#q'), status = $('#suggestStatus');
  if (!box || !q) return;
  var atEnd = q.selectionStart == null || q.selectionStart >= q.value.length;
  var items = atEnd ? unifiedSuggest(q.value) : [];
  _suggItems = items; _suggActive = -1; _qBeforeNav = q.value;
  if (!items.length) { hideSuggestions(); if (status) status.textContent = ''; return; }
  var html = '', lastGroup = '';
  items.forEach(function (it, i) {
    if (it.group && it.group !== lastGroup) {
      html += '<div class="sugg-group" role="presentation">' + esc(it.group) + '</div>';
      lastGroup = it.group;
    }
    html += '<button type="button" role="option" id="sugg-' + i + '" data-i="' + i + '" tabindex="-1">' +
      '<span class="sugg-text">' + (it.html || esc(it.text)) + '</span><span class="kind">' +
      esc(it.kind || '') + '</span></button>';
  });
  box.innerHTML = html;
  box.hidden = false;
  q.setAttribute('aria-expanded', 'true');
  if (status) status.textContent = items.length + ' gợi ý';
}
function markActive(i) {
  _suggActive = i;
  var box = $('#suggest'), q = $('#q');
  box.querySelectorAll('button').forEach(function (b, j) { b.classList.toggle('active', j === i); });
  if (i >= 0 && _suggItems[i]) {
    q.setAttribute('aria-activedescendant', 'sugg-' + i);
    q.value = _suggItems[i].text;
    var b = $('#sugg-' + i);
    if (b && b.scrollIntoView) b.scrollIntoView({ block: 'nearest' });
  } else {
    q.removeAttribute('aria-activedescendant');
    q.value = _qBeforeNav;
  }
}
function activateSuggestion(i) {
  var it = _suggItems[i];
  if (!it) return;
  var q = $('#q');
  hideSuggestions();
  if (it.action === 'open' && it.ma) { q.value = it.text; location.hash = '#/bai/' + it.ma; return; }
  if (it.action === 'chapter' && it.chapter) { location.hash = '#/chuong/' + it.chapter; return; }
  q.value = it.text;
  runLookup(it.text);
}

/* ---------- Tự chọn chế độ tra cứu ---------- */
/* Cụm chỉ công dụng / chất liệu: "làm áo thun", "cho ô tô", "pha polyester"… */
var ASK_CUES = ['làm', 'dùng', 'cho', 'để', 'bằng', 'pha', 'chứa', 'gồm', 'dành'];
var ASK_CUES_ASCII = ['lam', 'dung', 'cho', 'bang', 'pha', 'chua', 'gom', 'danh'];
function detectMode(text) {
  var raw = String(text == null ? '' : text).trim();
  if (!raw) return 'keyword';
  var ws = raw.split(/\s+/).filter(function (w) { return norm(w); });
  if (!ws.length) return 'keyword';
  if (/^[\d.\s]+$/.test(raw) || (ws.length === 1 && /\d/.test(ws[0]) && /^[\dA-Za-zĐđ.\/-]+$/.test(ws[0]))) return 'code';
  if (ws.length >= 4) return 'ask';
  if (ws.length >= 2 && ws.slice(1).some(function (w) {
    var k = viKey(w);
    return hasDia(k) ? ASK_CUES.indexOf(k) !== -1 : ASK_CUES_ASCII.indexOf(norm(w)) !== -1;
  })) return 'ask';
  return 'keyword';
}
function looksLikeDescription(text) {
  var m = detectMode(text);
  return m === 'ask' || (m === 'keyword' && String(text).trim().split(/\s+/).length >= 3);
}
function clearAsk() {
  state.mode = 'keyword'; state.askText = ''; state.askWeak = false; state.forced = false;
  var out = $('#askOut'); if (out) out.innerHTML = '';
}
/* Chạy tra cứu: chế độ Hỏi hiện thẻ trả lời ở trên + danh sách khớp từ khóa bên
   dưới; chế độ từ khóa / mã số chỉ hiện danh sách. opts.mode ép chế độ. */
var _inputDeb = null;
/* Danh sách dưới thẻ trả lời: bỏ dần từ cuối cho tới khi có văn bản chứa đủ các từ còn lại. */
function askListQuery(kw) {
  var ws = String(kw || '').trim().split(/\s+/).filter(Boolean);
  while (ws.length > 1 && !searchDocs(ws.join(' '), {}).length) ws.pop();
  return ws.join(' ');
}
function runLookup(text, opts) {
  opts = opts || {};
  clearTimeout(_inputDeb);
  var t = String(text == null ? '' : text).trim();
  var auto = detectMode(t), autoMode = looksLikeDescription(t) ? 'ask' : 'keyword';
  var mode = t ? (opts.mode || autoMode) : 'keyword';
  state.auto = auto; state.forced = !!opts.mode && !!t && opts.mode !== autoMode;
  state.mode = mode; state.shown = PAGE_SIZE; state.branch = null;
  hideSuggestions();
  if (mode === 'ask') {
    var ans = renderAsk(t);
    state.askText = t; state.askWeak = !!ans.weak;
    state.query = ans.weak ? (ans.keywords || t) : askListQuery(ans.keywords || t);
  } else {
    var forced = state.forced;
    clearAsk(); state.forced = forced;
    state.query = t;
  }
  if (t) recordRecent(t);
  if (auto === 'code' && isFollowed(hsDigits(t))) { markSeen(followDocs(hsDigits(t))); updateFollowBadge(); }
  syncQueryToUrl();
 
  var onPage = onPageRoute() || /^#\/nhanh\//.test(location.hash);
  if (opts.restore && onPage) return;
  if (onPage) location.hash = '#/';
  else renderList();
}
/* Chốt một truy vấn từ khóa (nút "Ý bạn là", tìm kiếm liên quan). */
/* Trang riêng (bài viết, so sánh, cây HS): tìm kiếm hoặc hỏi xong thì quay về danh sách. */
function onPageRoute() { return /^#\/(bai\/|phan-biet|cay-hs|thong-ke|theo-doi)/.test(location.hash); }
function commitSearch(text) {
  runLookup(text, { mode: 'keyword' });
}
/* Đưa truy vấn vào URL để link chia sẻ được, nút Back hoạt động và Cloudflare
   Web Analytics (không cookie) ghi lại truy vấn thật: ?q= cho từ khóa,
   ?hoi= cho câu hỏi tự nhiên (giữ tương thích link cũ của cả hai ô). */
function syncQueryToUrl() {
  try {
    var url = new URL(location.href);
    url.searchParams.delete('q'); url.searchParams.delete('hoi');
    if (state.mode === 'ask' && state.askText) url.searchParams.set('hoi', state.askText);
    else if (state.query && state.query.trim()) url.searchParams.set('q', state.query.trim());
    history.replaceState(null, '', url.pathname + url.search + location.hash);
  } catch (e) { /* trình duyệt quá cũ: bỏ qua */ }
}

function confClass(level) { return level === 3 ? 'conf-high' : level === 2 ? 'conf-mid' : 'conf-low'; }
/* Khối trả lời "Hỏi bằng tiếng Việt tự nhiên". */
function confClass(level) { return level === 3 ? 'conf-high' : level === 2 ? 'conf-mid' : 'conf-low'; }
function askResultHtml(r, n) {
  var d = r.doc;
  var links = '<a class="btn" href="#/bai/' + d.ma + '">Xem văn bản</a>';
  if (d.pdf_url) {
    links += '<a class="btn ghost" href="' + esc(d.pdf_url) + '" target="_blank" rel="noopener">PDF gốc</a>';
  } else if (d.detail_url) {
    links += '<a class="btn ghost" href="' + esc(d.detail_url) + '" target="_blank" rel="noopener">Nguồn customs.gov.vn</a>';
  }
  return '<li class="ask-item">' +
    '<div class="ask-item-head"><span class="ask-rank">' + n + '</span>' +
    hsFollowPill(d, 'ask-hs') +
    '<span class="conf ' + confClass(r.level) + '">Tin cậy: ' + r.confidence + '</span></div>' +
    '<p class="ask-goods">' + esc(shortText(d.mat_hang || d.trich_yeu, 180)) + '</p>' +
    '<p class="ask-cite">Nguồn: <a href="#/bai/' + d.ma + '"><b>' + esc(d.so_hieu) + '</b></a> · ' +
      esc(d.ngay || '') + ' · ' + esc(LOAI_LABEL[d.loai] || 'Văn bản') + '</p>' +
    '<p class="ask-why"><b>Lý do:</b> ' + esc(askReason(r)) + '</p>' +
    '<div class="ask-links">' + links + '</div>' +
    '</li>';
}
function renderAsk(question, opts) {
  opts = opts || {};
  var out = $('#askOut');
  question = String(question || '').trim();
  var ans = askDocs(question);
  if (!out) return ans;
  var html = '<div class="ask-answer"><p class="disclaimer" role="note">' + esc(NL_DISCLAIMER) + '</p>';
  if (ans.weak) {
    html += '<p class="ask-fallback">Chưa tìm được văn bản đủ khớp với mô tả “' + esc(question) + '”. ' +
      'Đã chuyển sang tìm kiếm từ khóa' + (ans.keywords ? ' với “<b>' + esc(ans.keywords) + '</b>”' : '') +
      ' ở bên dưới. Bạn có thể mô tả rõ hơn tên hàng, chất liệu hoặc công dụng.</p>';
  } else {
    html += '<div class="ask-summary"><span>Mã HS trong các văn bản dưới đây:</span>' + ans.hsList.map(function (h) {
      return '<span class="ask-hs-pill ' + confClass(h.level) + '">' + esc(h.hs) +
        ' <small>' + h.count + ' văn bản</small></span>';
    }).join('') + '</div>';
    var c = ans.concepts.filter(function (x) { return x.vars.length; });
    if (c.length) {
      html += '<p class="ask-parsed">Đã hiểu: ' + ['goods', 'material', 'use'].map(function (k) {
        var xs = c.filter(function (x) { return x.cat === k; }).map(function (x) { return esc(x.raw); });
        return xs.length ? '<span class="ask-kw">' + NL_CAT_LABEL[k] + ': <b>' + xs.join(', ') + '</b></span>' : '';
      }).join('') + '</p>';
    }
    html += '<ol class="ask-list">' + ans.results.map(function (r, i) { return askResultHtml(r, i + 1); }).join('') + '</ol>';
    html += '<p class="ask-filter-note">Bộ lọc loại văn bản, chương, năm chỉ áp dụng cho danh sách khớp từ khóa bên dưới; ' +
      'các văn bản gợi ý ở đây không bị lọc.</p>';
  }
  html += '</div>';
  out.innerHTML = html;
  return ans;
}
function boot() {
  Promise.all([
    fetch('data.json').then(function (r) { return r.json(); }),
    fetch('drive_ids.json').then(function (r) { return r.json(); }).catch(function () { return {}; }),
    fetch('meta.json').then(function (r) { return r.json(); }).catch(function () { return {}; }),
    fetch('images_drive_ids.json').then(function (r) { return r.json(); }).catch(function () { return {}; })
  ]).then(function (parts) {
    DOCS = parts[0]; DRIVE = parts[1]; META = parts[2]; IMG = parts[3] || {};
    buildIndex(DOCS);
    seenSet(); updateFollowBadge();
    document.addEventListener('click', onFollowClick);
    var total = document.getElementById('totalCount');
    if (total) total.textContent = (META.total || DOCS.length).toLocaleString('vi-VN');
    var upd = document.getElementById('updatedAt');
    if (upd) upd.textContent = META.generated_at_display || '—';
    fillFilterOptions();

    var q = $('#q'), box = $('#suggest'), form = $('#searchForm');
    /* Link chia sẻ cũ: ?q= (từ khóa) và ?hoi= (câu hỏi tự nhiên). */
    var initialQ = '', initialHoi = '';
    try {
      var sp = new URLSearchParams(location.search);
      initialQ = sp.get('q') || ''; initialHoi = sp.get('hoi') || '';
    } catch (e) { /* bỏ qua */ }
    if (initialHoi) q.value = initialHoi;
    else if (initialQ) { q.value = initialQ; state.query = initialQ; state.auto = detectMode(initialQ); }
    q.addEventListener('input', function () {
      clearTimeout(_inputDeb);
      _inputDeb = setTimeout(function () {
        showSuggestions();
        var v = q.value;
        /* Đang gõ một câu mô tả: chờ Enter mới hỏi, không làm mới danh sách liên tục. */
        if (detectMode(v) === 'ask') return;
        clearAsk();
        state.auto = detectMode(v); state.query = v; state.shown = PAGE_SIZE; state.branch = null;
        syncQueryToUrl();
        if (onPageRoute() || /^#\/nhanh\//.test(location.hash)) location.hash = '#/';
        else renderList();
      }, 150);
    });
    /* Dựng sẵn bộ gợi ý khi người dùng chạm vào ô, không làm chậm lần tải trang. */
    q.addEventListener('focus', function () { setTimeout(askPool, 0); }, { once: true });
    q.addEventListener('focus', function () {
      if (!q.value.trim()) showSuggestions(); /* ô trống: "Tìm nhiều" + gần đây */
    });
    q.addEventListener('keydown', function (e) {
      if (e.isComposing) return;
      if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
        if (box.hidden) showSuggestions();
        if (!_suggItems.length) return;
        e.preventDefault();
        markActive(e.key === 'ArrowDown'
          ? (_suggActive + 1 >= _suggItems.length ? -1 : _suggActive + 1)
          : (_suggActive <= -1 ? _suggItems.length - 1 : _suggActive - 1));
      } else if (e.key === 'Enter') {
        /* Enter khi đang chọn gợi ý: chạy gợi ý đó; không thì form submit tra đúng câu đã gõ. */
        if (!box.hidden && _suggActive >= 0) { e.preventDefault(); activateSuggestion(_suggActive); }
        else hideSuggestions();
      } else if (e.key === 'Escape') {
        /* Chặn Chrome xóa sạch ô type=search; Esc chỉ đóng gợi ý và trả lại phần đã gõ. */
        e.preventDefault();
        e.stopPropagation();
        if (!box.hidden) { q.value = _qBeforeNav; hideSuggestions(); }
      } else if (e.key === 'Tab') {
        hideSuggestions();
      }
    });
    /* mousedown giữ con trỏ trong ô; click mới chọn (chạm trên điện thoại cũng vậy). */
    box.addEventListener('mousedown', function (e) { e.preventDefault(); });
    box.addEventListener('click', function (e) {
      var b = e.target.closest('button[data-i]');
      if (b) activateSuggestion(+b.getAttribute('data-i'));
    });
    document.addEventListener('click', function (e) {
      if (!box.hidden && !e.target.closest('.ask-row')) hideSuggestions();
    });
    form.addEventListener('submit', function (e) {
      e.preventDefault();
      runLookup(q.value);
    });
    $('#askOut').addEventListener('click', function (e) {
      var a = e.target.closest('a[href^="#/bai/"]');
      if (!a) return;
      var m = /^#\/bai\/(\d+)/.exec(a.getAttribute('href') || '');
      if (m) recordClick(m[1]);
    });
    /* Ghi lại lượt mở văn bản (tín hiệu hạng nhẹ trên máy này) + lịch sử tìm. */
    document.getElementById('view').addEventListener('click', function (e) {
      var a = e.target.closest('a[href^="#/bai/"]');
      if (!a) return;
      var m = /^#\/bai\/(\d+)/.exec(a.getAttribute('href') || '');
      if (m) recordClick(m[1]);
      if (state.query) recordRecent(state.query);
    });
    /* Nút Back/Forward của trình duyệt: khôi phục truy vấn từ URL. */
    window.addEventListener('popstate', function () {
      try {
        var sp2 = new URLSearchParams(location.search);
        var ph = sp2.get('hoi') || '', pq = sp2.get('q') || '';
        if (ph) {
          if (ph !== state.askText) { q.value = ph; runLookup(ph, { mode: 'ask', restore: true }); }
        } else if (state.mode !== 'ask' || state.askText) {
          clearAsk(); q.value = pq; state.query = pq; state.shown = PAGE_SIZE;
        }
      } catch (e) { /* bỏ qua */ }
      route();
    });
    document.querySelectorAll('.lookup-box .chip').forEach(function (c) {
      c.addEventListener('click', function () {
        q.value = c.getAttribute('data-q');
        runLookup(q.value);
      });
    });
    $('#fLoai').addEventListener('change', function (e) {
      state.loai = e.target.value; state.shown = PAGE_SIZE; renderList();
    });
    $('#fChuong').addEventListener('change', function (e) {
      state.chapter = e.target.value; state.shown = PAGE_SIZE; renderList();
    });
    $('#fNam').addEventListener('change', function (e) {
      state.year = e.target.value; state.shown = PAGE_SIZE; renderList();
    });
    $('#clearFilters').addEventListener('click', function () {
      state.loai = ''; state.chapter = ''; state.year = ''; state.query = '';
      q.value = ''; state.shown = PAGE_SIZE; state.branch = null;
      clearAsk();
      syncFilterControls();
      syncQueryToUrl();
      if (location.hash && location.hash !== '#/') location.hash = '#/';
      else renderList();
    });

    window.addEventListener('hashchange', route);
    route();
    if (initialHoi) runLookup(initialHoi, { mode: 'ask', restore: true });
    else if (initialQ && looksLikeDescription(initialQ)) runLookup(initialQ, { restore: true });
   
  }).catch(function (err) {
    document.getElementById('view').innerHTML =
      '<p class="empty">Không tải được dữ liệu kho (data.json). ' +
      'Hãy mở trang qua máy chủ web tĩnh, không mở trực tiếp file.</p>';
    document.getElementById('resultInfo').textContent = 'Lỗi tải dữ liệu.';
  });
}

if (typeof document !== 'undefined' && document.addEventListener) {
  document.addEventListener('DOMContentLoaded', boot);
}

})();
