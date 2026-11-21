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
      var best = null;
      c.vars.forEach(function (vv) {
        var r = termInDoc(x, vv.t);
        if (!r.score) return;
        var s = r.score * vv.w * vv.stat.idf * (r.head ? 1.2 : 1);
        if (!best || s > best.s) best = { s: s, r: r, vv: vv };
      });
      if (!best) { missing.push(c); return; }
      score += best.s * NL_CAT_WEIGHT[c.cat];
      got += c.weight * Math.min(1, best.vv.w) * (best.r.field === 'p' || best.r.field === 'r' ? 1 : 0.8);
      matched.push({ c: c, field: best.r.field, show: best.vv.part ? '' : best.vv.show, part: best.vv.part || '' });
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
      return m.c === headC && (m.field === 'p' || (m.field === 'r' && !m.part));
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
        if (hit.t.indexOf('đã ') === 0) neg = -99;
        if (i - neg > 8 && found[hit.g].indexOf(hit.t) === -1) found[hit.g].push(hit.t);
        i += hit.len;
        continue;
      }
      if (w[i] === 'chưa' || w[i] === 'không') neg = i;
      else if (w[i] === 'đã') neg = -99;
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
    return Object.keys(x).filter(function (w) { return !y[w] && cp.df[w]; })
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
    norm: norm, lev: lev, hsDigits: hsDigits, parseDate: parseDate,
    buildIndex: buildIndex, searchDocs: searchDocs, suggest: suggest,
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
      _suggestPool = null; _vocab = null; _recents = null; _clicks = null; _nlIdx = null; _nlDf = {}; _cp = null;
      buildIndex(docs);
    }
  };
}

/* ================= Hiển thị (chỉ chạy trên trình duyệt) ================= */

var PAGE_SIZE = 30;
var state = { query: '', loai: '', chapter: '', year: '', shown: PAGE_SIZE };
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
    '<p class="sub">' + esc(d.ngay || '') + ' · ' + loaiBadge(d) + ' ' + hsBadge(d) + '</p>' +
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
  _lastResults = results;
  var view = $('#view');
  var info = $('#resultInfo');
  if (state.query || state.loai || state.chapter || state.year) {
    info.textContent = 'Tìm thấy ' + results.length + ' văn bản' +
      (state.query ? ' cho “' + state.query.trim() + '”' : '') + '.';
  } else {
    info.textContent = 'Hiển thị văn bản mới nhất. Gõ từ khóa để tìm trong cả kho.';
  }
  if (!results.length) {
    view.innerHTML = zeroResultHtml();
    wireResultButtons();
    return;
  }
  var html = '';
  var corr = state.query ? didYouMean(state.query) : null;
  if (corr) {
    html += '<p class="did-you-mean">Có phải bạn muốn tìm: <button type="button" class="dym-btn" data-q="' +
      esc(corr) + '">' + esc(corr) + '</button>?</p>';
  }
  var shown = results.slice(0, state.shown);
  html += shown.map(cardHtml).join('');
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
  var sub = [];
  if (det.coquan) sub.push(esc(det.coquan));
  if (det.soKqpt) sub.push('Số KQPT: ' + esc(det.soKqpt));
  if (det.don) sub.push('Đơn đề nghị số ' + esc(det.don));
  var html = '<a class="back-link" href="#/">← Về danh sách</a>' +
    '<article class="article">' +
    '<h1>' + esc(doc.so_hieu) + '</h1>' +
    '<p class="sub">' + esc(doc.ngay || '') + ' · ' + loaiBadge(doc) + ' ' + hsBadge(doc) +
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

  html += cpRelatedHtml(doc);
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
      '</a></h3><p class="sub">' + esc(o.ngay || '') + ' · ' + hsBadge(o) + ' · Giống ' + cpPct(x.pair.sim) +
      '</p><p>' + esc(shortText(o.mat_hang || o.trich_yeu, 140)) + '</p></article>';
  }).join('') + '</section>';
}

/* ================= Định tuyến & khởi động ================= */

function route() {
  var h = location.hash || '#/';
  var m = /^#\/bai\/(\d+)/.exec(h);
  var pb = /^#\/phan-biet(?:\/(\d+)-(\d+))?/.exec(h);
  document.body.classList.toggle('is-detail', !!m || !!pb);
  if (m) { renderDetail(m[1]); return; }
  if (pb) { if (pb[1]) renderCompare(pb[1], pb[2]); else renderCompareList(); return; }
  var c = /^#\/chuong\/([0-9]{2}|khong-co-ma)/.exec(h);
  if (c) {
    state.chapter = c[1] === 'khong-co-ma' ? '' : c[1];
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
function showSuggestions() {
  var box = $('#suggest'), q = $('#q');
  if (!box || !q) return;
  var items = suggest(q.value);
  _suggItems = items; _suggActive = -1; _qBeforeNav = q.value;
  var status = $('#suggestStatus');
  if (!items.length) { hideSuggestions(); if (status) status.textContent = ''; return; }
  var html = '', lastGroup = '';
  items.forEach(function (it, i) {
    if (it.group !== lastGroup) {
      html += '<div class="sugg-group" role="presentation">' + esc(it.group) + '</div>';
      lastGroup = it.group;
    }
    html += '<button type="button" role="option" id="sugg-' + i + '" data-i="' + i + '">' +
      esc(it.text) + '<span class="kind">' + esc(it.kind) + '</span></button>';
  });
  box.innerHTML = html;
  box.hidden = false;
  q.setAttribute('aria-expanded', 'true');
  if (status) status.textContent = items.length + ' gợi ý';
  box.querySelectorAll('button').forEach(function (b) {
    b.addEventListener('click', function () { activateSuggestion(+b.getAttribute('data-i')); });
  });
}
function markActive(i) {
  _suggActive = i;
  var box = $('#suggest'), q = $('#q');
  box.querySelectorAll('button').forEach(function (b, j) {
    b.classList.toggle('active', j === i);
  });
  if (i >= 0 && _suggItems[i]) {
    q.setAttribute('aria-activedescendant', 'sugg-' + i);
    q.value = _suggItems[i].text;
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
  if (it.action === 'open' && it.ma) { location.hash = '#/bai/' + it.ma; return; }
  if (it.action === 'chapter' && it.chapter) { location.hash = '#/chuong/' + it.chapter; return; }
  q.value = it.text;
  commitSearch(it.text);
}
/* Chốt một truy vấn: ghi lại lịch sử tìm, đồng bộ URL (?q=), hiển thị. */
/* Trang riêng (bài viết, so sánh): tìm kiếm hoặc hỏi xong thì quay về danh sách. */
function onPageRoute() { return /^#\/(bai\/|phan-biet)/.test(location.hash); }
function commitSearch(text) {
  state.query = text; state.shown = PAGE_SIZE;
  recordRecent(text);
  syncQueryToUrl();
  if (onPageRoute()) location.hash = '#/';
  else renderList();
}
/* Đưa truy vấn vào URL (?q=) để link tìm kiếm chia sẻ được, nút Back hoạt
   động, và Cloudflare Web Analytics (đã bật, không cookie) ghi lại top
   truy vấn thật của độc giả — nguồn duy nhất để cải tiến từ đồng nghĩa
   và gợi ý theo hành vi thật mà không cần backend. */
function syncQueryToUrl() {
  try {
    var url = new URL(location.href);
    if (state.query && state.query.trim()) url.searchParams.set('q', state.query.trim());
    else url.searchParams.delete('q');
    history.replaceState(null, '', url.pathname + url.search + location.hash);
  } catch (e) { /* trình duyệt quá cũ: bỏ qua */ }
}

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
    '<span class="ask-hs">' + esc(d.ma_hs) + '</span>' +
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
  var onDetail = onPageRoute();
  if (!out) return;
  question = String(question || '').trim();
  if (!question) { out.innerHTML = ''; return; }
  var ans = askDocs(question);
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
  }
  html += '</div>';
  out.innerHTML = html;
  /* Câu hỏi khôi phục từ URL không được đẩy người đọc rời trang văn bản. */
  if (opts.restore && onDetail) return;
  if (ans.weak) {
    var q = $('#q');
    if (q) q.value = ans.keywords || question;
    commitSearch(ans.keywords || question);
  } else if (onDetail) {
    location.hash = '#/';
  }
}
function wireAsk() {
  var form = $('#askForm'), input = $('#ask');
  if (!form || !input) return;
  form.addEventListener('submit', function (e) {
    e.preventDefault();
    renderAsk(input.value);
    syncAskToUrl(input.value);
  });
  document.querySelectorAll('.ask-chip').forEach(function (b) {
    b.addEventListener('click', function () {
      input.value = b.getAttribute('data-ask');
      renderAsk(input.value);
      syncAskToUrl(input.value);
    });
  });
  $('#askOut').addEventListener('click', function (e) {
    var a = e.target.closest('a[href^="#/bai/"]');
    if (!a) return;
    var m = /^#\/bai\/(\d+)/.exec(a.getAttribute('href') || '');
    if (m) recordClick(m[1]);
  });
  try {
    var initial = new URLSearchParams(location.search).get('hoi');
    if (initial) { input.value = initial; renderAsk(initial, { restore: true }); }
  } catch (e) { /* bỏ qua */ }
}
function syncAskToUrl(text) {
  try {
    var url = new URL(location.href);
    if (text && text.trim()) url.searchParams.set('hoi', text.trim());
    else url.searchParams.delete('hoi');
    history.replaceState(null, '', url.pathname + url.search + location.hash);
  } catch (e) { /* bỏ qua */ }
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
    var total = document.getElementById('totalCount');
    if (total) total.textContent = (META.total || DOCS.length).toLocaleString('vi-VN');
    var upd = document.getElementById('updatedAt');
    if (upd) upd.textContent = META.generated_at_display || '—';
    fillFilterOptions();

    var q = $('#q');
    /* Truy vấn mở sẵn từ link chia sẻ (?q=...). */
    try {
      var initialQ = new URLSearchParams(location.search).get('q');
      if (initialQ) { q.value = initialQ; state.query = initialQ; }
    } catch (e) { /* bỏ qua */ }
    var deb = null;
    q.addEventListener('input', function () {
      clearTimeout(deb);
      deb = setTimeout(function () {
        state.query = q.value; state.shown = PAGE_SIZE;
        syncQueryToUrl();
        showSuggestions();
        if (onPageRoute()) location.hash = '#/';
        else renderList();
      }, 150);
    });
    q.addEventListener('focus', function () {
      if (!q.value.trim()) showSuggestions(); /* ô trống: "Tìm nhiều" + gần đây */
    });
    q.addEventListener('keydown', function (e) {
      if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
        e.preventDefault();
        if ($('#suggest').hidden) { showSuggestions(); }
        if (!_suggItems.length) return;
        var next = e.key === 'ArrowDown'
          ? (_suggActive + 1) % _suggItems.length
          : (_suggActive - 1 + _suggItems.length) % _suggItems.length;
        markActive(next);
      } else if (e.key === 'Enter') {
        hideSuggestions();
        commitSearch(q.value);
      } else if (e.key === 'Escape') {
        /* Ngăn hành vi mặc định của Chrome với input type=search (Esc xóa
           sạch ô nhập). Chỉ xử lý khi dropdown đang mở; dropdown đã đóng
           thì Esc không làm gì (tránh khôi phục nhầm truy vấn cũ). */
        e.preventDefault();
        e.stopPropagation();
        if (!$('#suggest').hidden) {
          hideSuggestions();
          q.value = _qBeforeNav;
          state.query = _qBeforeNav; state.shown = PAGE_SIZE;
          syncQueryToUrl();
          renderList();
        }
      }
    });
    document.addEventListener('click', function (e) {
      var box = $('#suggest');
      if (box && !box.hidden && !e.target.closest('.search-box')) hideSuggestions();
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
        var pq = new URLSearchParams(location.search).get('q') || '';
        q.value = pq; state.query = pq; state.shown = PAGE_SIZE;
      } catch (e) { /* bỏ qua */ }
      route();
    });
    document.querySelectorAll('.chip').forEach(function (c) {
      c.addEventListener('click', function () {
        q.value = c.getAttribute('data-q');
        commitSearch(q.value);
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
      q.value = ''; state.shown = PAGE_SIZE;
      syncFilterControls();
      syncQueryToUrl();
      if (location.hash && location.hash !== '#/') location.hash = '#/';
      else renderList();
    });

    window.addEventListener('hashchange', route);
    route();
    wireAsk();
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
