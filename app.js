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
  var tokens = q.split(' ').filter(function (t) {
    return t.length >= 2 || /^\d+$/.test(t);
  });
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
    if (ok) out.push({ doc: d, score: score, reasons: reasons, i: i });
  }
  out.sort(function (a, b) {
    if (b.score !== a.score) return b.score - a.score;
    return IDX[b.i].dateSort - IDX[a.i].dateSort;
  });
  return out;
}

/* Gợi ý khi đang gõ: số hiệu, mã HS, từ tên hàng phổ biến. */
var _suggestPool = null;
function suggestPool() {
  if (_suggestPool) return _suggestPool;
  var so = {}, hs = {}, words = {};
  DOCS.forEach(function (d, i) {
    so[d.so_hieu] = true;
    if (d.ma_hs) hs[d.ma_hs] = true;
    IDX[i].nProd.split(' ').forEach(function (w) {
      if (w.length >= 3) words[w] = (words[w] || 0) + 1;
    });
  });
  _suggestPool = {
    so: Object.keys(so).sort(),
    hs: Object.keys(hs).sort(),
    words: Object.keys(words).sort(function (a, b) { return words[b] - words[a]; }).slice(0, 300)
  };
  return _suggestPool;
}

function suggest(query) {
  var q = norm(query);
  if (q.length < 2) return [];
  var pool = suggestPool(), out = [];
  pool.so.forEach(function (s) {
    if (out.length < 8 && norm(s).indexOf(q) !== -1) out.push({ text: s, kind: 'Số hiệu' });
  });
  pool.hs.forEach(function (s) {
    if (out.length < 8 && hsDigits(s).indexOf(q.replace(/\D/g, '')) === 0 && q.replace(/\D/g, '').length >= 2)
      out.push({ text: s, kind: 'Mã HS' });
  });
  pool.words.forEach(function (w) {
    if (out.length < 8 && w.indexOf(q) === 0) out.push({ text: w, kind: 'Tên hàng' });
  });
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

/* Cho phép kiểm thử bằng Node: VBXNK.searchDocs(...) */
if (typeof globalThis !== 'undefined') {
  globalThis.VBXNK = {
    norm: norm, lev: lev, hsDigits: hsDigits, parseDate: parseDate,
    buildIndex: buildIndex, searchDocs: searchDocs, suggest: suggest,
    parseDocDetail: parseDocDetail, relatedDocs: relatedDocs,
    extractDriveId: extractDriveId, highlight: highlight,
    _pdfBlockHtml: pdfBlockHtml, _renderDetail: renderDetail,
    _setData: function (docs, drive, meta, img) {
      DOCS = docs; DRIVE = drive || {}; META = meta || {}; IMG = img || {};
      _suggestPool = null; buildIndex(docs);
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
    view.innerHTML = '<p class="empty">Không tìm thấy văn bản nào khớp. ' +
      'Thử gõ không dấu, chỉ một phần số hiệu hoặc mã HS (ví dụ: “vai sofa”, “3504”, “1397”).</p>';
    return;
  }
  var shown = results.slice(0, state.shown);
  var html = shown.map(cardHtml).join('');
  if (results.length > state.shown) {
    html += '<button type="button" class="load-more" id="moreBtn">Xem thêm (' +
      (results.length - state.shown) + ' văn bản nữa)</button>';
  }
  view.innerHTML = html;
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

/* ================= Định tuyến & khởi động ================= */

function route() {
  var h = location.hash || '#/';
  var m = /^#\/bai\/(\d+)/.exec(h);
  if (m) { renderDetail(m[1]); return; }
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

function showSuggestions() {
  var box = $('#suggest'), q = $('#q');
  var items = suggest(q.value);
  if (!items.length) { box.hidden = true; box.innerHTML = ''; return; }
  box.innerHTML = items.map(function (it, i) {
    return '<button type="button" data-i="' + i + '" data-text="' + esc(it.text) + '">' +
      esc(it.text) + '<span class="kind">' + esc(it.kind) + '</span></button>';
  }).join('');
  box.hidden = false;
  box.querySelectorAll('button').forEach(function (b) {
    b.addEventListener('click', function () {
      q.value = b.getAttribute('data-text');
      box.hidden = true;
      state.query = q.value; state.shown = PAGE_SIZE;
      if (location.hash && location.hash !== '#/') location.hash = '#/';
      renderList();
    });
  });
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
    var deb = null;
    q.addEventListener('input', function () {
      clearTimeout(deb);
      deb = setTimeout(function () {
        state.query = q.value; state.shown = PAGE_SIZE;
        if (location.hash && location.hash !== '#/' && location.hash.indexOf('#/bai/') !== 0) {
          /* đang ở trang chương: quay về danh sách để tìm */
        }
        showSuggestions();
        if (location.hash.indexOf('#/bai/') === 0) location.hash = '#/';
        else renderList();
      }, 150);
    });
    q.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') { $('#suggest').hidden = true; }
      if (e.key === 'Enter') { $('#suggest').hidden = true; renderList(); }
    });
    document.addEventListener('click', function (e) {
      var box = $('#suggest');
      if (box && !box.hidden && !e.target.closest('.search-box')) box.hidden = true;
    });
    document.querySelectorAll('.chip').forEach(function (c) {
      c.addEventListener('click', function () {
        q.value = c.getAttribute('data-q');
        state.query = q.value; state.shown = PAGE_SIZE;
        if (location.hash.indexOf('#/bai/') === 0) location.hash = '#/';
        else renderList();
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
      if (location.hash && location.hash !== '#/') location.hash = '#/';
      else renderList();
    });

    window.addEventListener('hashchange', route);
    route();
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
