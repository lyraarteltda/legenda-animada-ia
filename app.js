/**
 * Legenda Animada IA — app.js
 *
 * Fluxo: vídeo do membro (fica no navegador) → áudio extraído e reamostrado
 * para WAV 16 kHz mono → transcrição com tempo por palavra na chave do membro
 * (fal.ai Whisper ou OpenAI Whisper) → revisão opcional na OpenRouter (corrige
 * o texto SEM mexer nos tempos e marca destaques/emojis) → agrupamento
 * determinístico em cartelas → pré-visualização em canvas sobre o vídeo →
 * gravação do vídeo final (canvas + áudio original via MediaRecorder).
 *
 * O mesmo desenhador (drawCaptions) serve a pré-visualização, as miniaturas
 * dos estilos e a gravação — o que você vê é o que sai no arquivo.
 */
const App = (function () {
  'use strict';

  var NS = 'legenda-animada-ia';
  var MAX_SECONDS = 180;                 // limite honesto de transcrição por vídeo
  var MAX_BYTES = 500 * 1024 * 1024;
  var PROJ_PREFIX = NS + '_proj_';
  var PROJ_INDEX = NS + '_projects';
  var STYLE_SLOT = NS + '_style';
  var MYSTYLE_SLOT = NS + '_mystyle';
  var FAL_MODEL = 'fal-ai/whisper';

  var FONT_SPEC = {
    'Montserrat': { weight: '900', css: '"Montserrat"' },
    'Anton': { weight: '400', css: '"Anton"' },
    'Bangers': { weight: '400', css: '"Bangers"' },
    'Permanent Marker': { weight: '400', css: '"Permanent Marker"' },
    'Nunito': { weight: '800', css: '"Nunito"' }
  };
  var EMOJI_STACK = '"Apple Color Emoji","Segoe UI Emoji","Noto Color Emoji",sans-serif';

  var PRESETS = [
    { id: 'pop', name: 'Pop', desc: 'Contorno grosso, a palavra falada pula na cor de destaque.',
      st: { mode: 'pop', font: 'Montserrat', size: 8, color: '#ffffff', hl: '#ffd23f', upper: true, anim: 'pop' } },
    { id: 'karaoke', name: 'Karaokê', desc: 'A frase inteira aparece e acende conforme é dita.',
      st: { mode: 'karaoke', font: 'Montserrat', size: 7.5, color: '#ffffff', hl: '#4ade80', upper: true, anim: 'none' } },
    { id: 'box', name: 'Caixa', desc: 'Faixa escura atrás do texto e um marcador na palavra falada.',
      st: { mode: 'box', font: 'Nunito', size: 7, color: '#ffffff', hl: '#e63946', upper: false, anim: 'pop' } },
    { id: 'oneword', name: 'Uma palavra', desc: 'Só a palavra falada, enorme, no centro da atenção.',
      st: { mode: 'oneword', font: 'Anton', size: 12, color: '#ffffff', hl: '#ffd23f', upper: true, anim: 'pop' } },
    { id: 'minimal', name: 'Discreta', desc: 'Frase curta, sem contorno, com sombra suave.',
      st: { mode: 'minimal', font: 'Nunito', size: 6, color: '#ffffff', hl: '#ffd23f', upper: false, anim: 'none' } },
    { id: 'gibi', name: 'Gibi', desc: 'Balão de quadrinho com a palavra falada em vermelho.',
      st: { mode: 'gibi', font: 'Bangers', size: 8, color: '#141414', hl: '#e63946', upper: true, anim: 'pop' } }
  ];
  var DEFAULT_STYLE = Object.assign({ preset: 'pop', pos: 70, emoji: true }, PRESETS[0].st);

  var state = {
    wired: false,
    file: null, url: '', sig: '', name: '', dur: 0, vw: 0, vh: 0, isSample: false,
    cues: [], maxWords: 3,
    style: Object.assign({}, DEFAULT_STYLE),
    busy: false, abort: null, exporting: null,
    resultUrl: '', seq: 0, lastCue: -1
  };

  function $(id) { return document.getElementById(id); }
  function esc(s) { return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]; }); }
  function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }
  function fmtClock(t) { t = Math.max(0, t || 0); var m = Math.floor(t / 60), s = Math.floor(t % 60); return m + ':' + (s < 10 ? '0' : '') + s; }
  function fmtCue(t) { t = Math.max(0, t || 0); var m = Math.floor(t / 60), s = t - m * 60; return m + ':' + (s < 10 ? '0' : '') + s.toFixed(1).replace('.', ','); }
  function fmtSrt(t) {
    t = Math.max(0, t || 0); var ms = Math.round(t * 1000);
    var h = Math.floor(ms / 3600000); ms -= h * 3600000; var m = Math.floor(ms / 60000); ms -= m * 60000; var s = Math.floor(ms / 1000); ms -= s * 1000;
    function p(n, l) { n = String(n); while (n.length < l) n = '0' + n; return n; }
    return p(h, 2) + ':' + p(m, 2) + ':' + p(s, 2) + ',' + p(ms, 3);
  }
  var toastTimer = null;
  function toast(msg) {
    var t = $('toast'); if (!t) return;
    t.textContent = msg; t.classList.add('show');
    clearTimeout(toastTimer); toastTimer = setTimeout(function () { t.classList.remove('show'); }, 4200);
  }
  function lsGet(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
  function lsSet(k, v) { try { localStorage.setItem(k, v); return true; } catch (e) { return false; } }
  function lsDel(k) { try { localStorage.removeItem(k); } catch (e) {} }
  function show(el, on) { if (el) el.hidden = !on; }

  // ── Palavras e cartelas ────────────────────────────────────────────────
  var PUNCT_END = /[.!?…]["»”)]?$/;
  var PUNCT_SOFT = /[,;:]["»”)]?$/;

  function cleanWords(raw) {
    var out = [], last = 0;
    raw.forEach(function (w) {
      var txt = String(w.w || '').replace(/\s+/g, ' ').trim();
      if (!txt) return;
      var s = Number(w.s), e = Number(w.e);
      if (!isFinite(s)) s = last;
      if (!isFinite(e) || e <= s) e = s + 0.35;
      if (s < last) s = last;
      if (e <= s) e = s + 0.12;
      out.push({ w: txt, s: s, e: e, hl: !!w.hl, emoji: w.emoji || '' });
      last = s;
    });
    return out;
  }

  function groupCues(words, maxWords) {
    var maxChars = maxWords <= 1 ? 999 : maxWords * 7 + 4;
    var cues = [], cur = [];
    function flush() { if (cur.length) { cues.push(cur); cur = []; } }
    words.forEach(function (w) {
      if (cur.length) {
        var prev = cur[cur.length - 1];
        var chars = cur.reduce(function (a, x) { return a + x.w.length + 1; }, 0) + w.w.length;
        if (cur.length >= maxWords || chars > maxChars || (w.s - prev.e) > 0.7 || PUNCT_END.test(prev.w) || (PUNCT_SOFT.test(prev.w) && cur.length >= 2)) flush();
      }
      cur.push(Object.assign({}, w));
    });
    flush();
    var res = cues.map(function (ws) {
      var emoji = ''; ws.forEach(function (x) { if (!emoji && x.emoji) emoji = x.emoji; });
      return { id: 'c' + (++state.seq), s: ws[0].s, e: ws[ws.length - 1].e, words: ws, emoji: emoji };
    });
    for (var i = 0; i < res.length; i++) {
      var c = res[i], next = res[i + 1];
      var limit = next ? next.s : c.e + 0.6;
      c.e = Math.min(Math.max(c.e + 0.25, c.s + 0.35), Math.max(limit, c.e));
      if (next && c.e > next.s) c.e = next.s;
    }
    return res;
  }

  function flatWords() {
    var out = [];
    state.cues.forEach(function (c) {
      c.words.forEach(function (w, i) { out.push({ w: w.w, s: w.s, e: w.e, hl: w.hl, emoji: i === 0 ? (c.emoji || '') : '' }); });
    });
    return out;
  }

  function cueToText(c) {
    return c.words.map(function (w) {
      if (!w.hl) return w.w;
      var m = /^(.*?)([.,!?;:…]*)$/.exec(w.w);
      return '*' + m[1] + '*' + m[2];
    }).join(' ');
  }

  function parseCueText(text) {
    return String(text || '').split(/\s+/).filter(Boolean).map(function (tok) {
      var m = /^\*(.+?)\*([.,!?;:…"»”)]*)$/.exec(tok);
      if (m) return { w: m[1] + m[2], hl: true };
      return { w: tok.replace(/\*/g, ''), hl: false };
    }).filter(function (t) { return t.w; });
  }

  function retimeCue(c, toks) {
    if (toks.length === c.words.length) {
      toks.forEach(function (t, i) { c.words[i].w = t.w; c.words[i].hl = t.hl; });
      return;
    }
    var span = Math.max(0.2, c.e - c.s), total = 0;
    toks.forEach(function (t) { total += t.w.length + 2; });
    var at = c.s;
    c.words = toks.map(function (t) {
      var d = span * (t.w.length + 2) / total;
      var w = { w: t.w, s: at, e: at + d, hl: t.hl, emoji: '' };
      at += d; return w;
    });
  }

  function heuristicHighlights(words) {
    for (var i = 0; i < words.length; i += 5) {
      var best = -1, bestLen = 0;
      for (var j = i; j < Math.min(i + 5, words.length); j++) {
        var bare = words[j].w.replace(/[^\wÀ-ÿ%]/g, '');
        if (/\d/.test(bare)) { best = j; break; }
        if (bare.length > bestLen) { bestLen = bare.length; best = j; }
      }
      if (best !== -1 && (bestLen >= 6 || /\d/.test(words[best].w))) words[best].hl = true;
    }
    return words;
  }

  // ── Desenhador (pré-visualização, miniaturas e gravação) ──────────────
  function fontFor(style, px) {
    var f = FONT_SPEC[style.font] || FONT_SPEC.Montserrat;
    return f.weight + ' ' + Math.round(px) + 'px ' + f.css + ',' + EMOJI_STACK;
  }
  function displayWord(style, w) { return style.upper ? w.toLocaleUpperCase('pt-BR') : w; }

  function findCue(t) {
    var cues = state.cues, n = cues.length;
    var i = state.lastCue;
    if (i >= 0 && i < n && cues[i].s <= t && t < cues[i].e) return i;
    for (var k = 0; k < n; k++) { if (cues[k].s <= t && t < cues[k].e) { state.lastCue = k; return k; } }
    return -1;
  }

  function roundRect(ctx, x, y, w, h, r) {
    r = Math.min(r, h / 2, w / 2);
    ctx.beginPath();
    ctx.moveTo(x + r, y); ctx.lineTo(x + w - r, y); ctx.quadraticCurveTo(x + w, y, x + w, y + r);
    ctx.lineTo(x + w, y + h - r); ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    ctx.lineTo(x + r, y + h); ctx.quadraticCurveTo(x, y + h, x, y + h - r);
    ctx.lineTo(x, y + r); ctx.quadraticCurveTo(x, y, x + r, y); ctx.closePath();
  }

  // Desenha a cartela `cue` no instante `t` num canvas W×H.
  function drawCue(ctx, W, H, cue, t, style) {
    if (!cue || !cue.words.length) return;
    var base = Math.min(W, H) * style.size / 100;
    var mode = style.mode;
    var px = mode === 'oneword' ? base * 1.15 : base;
    var words = cue.words;
    var active = -1;
    for (var i = 0; i < words.length; i++) { if (words[i].s <= t) active = i; }
    if (active === -1) active = 0;
    var list = mode === 'oneword' ? [active] : words.map(function (_, i) { return i; });

    // entrada da cartela
    var since = t - cue.s, enter = clamp(since / 0.08, 0, 1);
    var anim = style.anim === 'pop';

    ctx.save();
    ctx.textBaseline = 'middle';
    ctx.textAlign = 'left';
    var maxW = W * 0.88, scaleFit = 1, lines, space, lineH, items;

    for (var pass = 0; pass < 4; pass++) {
      var fpx = px * scaleFit;
      ctx.font = fontFor(style, fpx);
      space = fpx * 0.34; lineH = fpx * 1.18;
      items = list.map(function (idx) {
        var txt = displayWord(style, words[idx].w);
        return { idx: idx, txt: txt, w: ctx.measureText(txt).width };
      });
      lines = []; var cur = [], curW = 0, widest = 0;
      items.forEach(function (it) {
        var add = (cur.length ? space : 0) + it.w;
        if (cur.length && curW + add > maxW) { lines.push({ items: cur, w: curW }); cur = []; curW = 0; add = it.w; }
        cur.push(it); curW += add;
      });
      if (cur.length) lines.push({ items: cur, w: curW });
      lines.forEach(function (l) { widest = Math.max(widest, l.w); });
      if (widest <= maxW || pass === 3) break;
      scaleFit *= maxW / widest * 0.98;
    }
    var fpxFinal = px * scaleFit;
    var blockH = lines.length * lineH;
    var cy = H * style.pos / 100;
    var top = clamp(cy - blockH / 2, H * 0.03, H * 0.97 - blockH);

    if (anim && enter < 1) {
      var k = 0.86 + 0.14 * enter;
      ctx.translate(W / 2, top + blockH / 2); ctx.scale(k, k); ctx.translate(-W / 2, -(top + blockH / 2));
    }
    ctx.globalAlpha = anim ? Math.max(0.25, enter) : 1;

    var widestLine = 0; lines.forEach(function (l) { widestLine = Math.max(widestLine, l.w); });
    var ink = '#141414';

    if (mode === 'gibi') {
      var padX = fpxFinal * 0.55, padY = fpxFinal * 0.38;
      var bx = W / 2 - widestLine / 2 - padX, by = top - padY, bw = widestLine + padX * 2, bh = blockH + padY * 2;
      ctx.lineWidth = Math.max(2, fpxFinal * 0.11); ctx.strokeStyle = ink; ctx.fillStyle = '#ffffff'; ctx.lineJoin = 'round';
      roundRect(ctx, bx, by, bw, bh, fpxFinal * 0.7);
      ctx.fill(); ctx.stroke();
      // rabicho do balão
      var tx = bx + bw * 0.28, ty = by + bh;
      ctx.beginPath(); ctx.moveTo(tx - fpxFinal * 0.35, ty - ctx.lineWidth); ctx.lineTo(tx - fpxFinal * 0.6, ty + fpxFinal * 0.6); ctx.lineTo(tx + fpxFinal * 0.35, ty - ctx.lineWidth); ctx.closePath();
      ctx.fill(); ctx.beginPath(); ctx.moveTo(tx - fpxFinal * 0.35, ty); ctx.lineTo(tx - fpxFinal * 0.6, ty + fpxFinal * 0.6); ctx.lineTo(tx + fpxFinal * 0.35, ty); ctx.stroke();
    }
    if (mode === 'box') {
      ctx.fillStyle = 'rgba(20,20,20,0.82)';
      lines.forEach(function (l, li) {
        var lx = W / 2 - l.w / 2, ly = top + li * lineH;
        roundRect(ctx, lx - fpxFinal * 0.35, ly + lineH * 0.04, l.w + fpxFinal * 0.7, lineH * 0.96, fpxFinal * 0.22); ctx.fill();
      });
    }

    lines.forEach(function (l, li) {
      var x = W / 2 - l.w / 2, y = top + li * lineH + lineH / 2;
      l.items.forEach(function (it, n) {
        if (n) x += space;
        var w = words[it.idx];
        var isActive = it.idx === active && t >= w.s;
        var spoken = t >= w.s;
        var color = style.color, scale = 1;
        if (mode === 'karaoke') {
          color = isActive ? style.hl : style.color;
          ctx.globalAlpha = spoken ? 1 : 0.42;
        } else if (mode === 'oneword') {
          color = w.hl ? style.hl : style.color;
        } else {
          if (isActive || w.hl) color = style.hl;
        }
        if (anim && isActive) {
          var dt = t - w.s; if (dt < 0.16) scale = 1 + 0.2 * (1 - dt / 0.16);
        }
        if (mode === 'box' && isActive) {
          ctx.save(); ctx.globalAlpha = 1; ctx.fillStyle = style.hl;
          roundRect(ctx, x - fpxFinal * 0.12, y - lineH * 0.46, it.w + fpxFinal * 0.24, lineH * 0.92, fpxFinal * 0.16); ctx.fill(); ctx.restore();
          color = ink === style.hl ? '#ffffff' : (luma(style.hl) > 0.55 ? ink : '#ffffff');
        }
        ctx.save();
        if (scale !== 1) { ctx.translate(x + it.w / 2, y); ctx.scale(scale, scale); ctx.translate(-(x + it.w / 2), -y); }
        if (mode === 'pop' || mode === 'karaoke' || mode === 'oneword') {
          ctx.lineJoin = 'round'; ctx.miterLimit = 2;
          ctx.shadowColor = 'rgba(0,0,0,0.35)'; ctx.shadowOffsetY = fpxFinal * 0.06; ctx.shadowBlur = fpxFinal * 0.08;
          ctx.lineWidth = fpxFinal * 0.2; ctx.strokeStyle = ink; ctx.strokeText(it.txt, x, y);
          ctx.shadowColor = 'transparent';
        } else if (mode === 'minimal') {
          ctx.shadowColor = 'rgba(0,0,0,0.75)'; ctx.shadowBlur = fpxFinal * 0.3; ctx.shadowOffsetY = fpxFinal * 0.05;
        }
        ctx.fillStyle = color; ctx.fillText(it.txt, x, y);
        ctx.restore();
        if (mode === 'karaoke') ctx.globalAlpha = anim ? Math.max(0.25, enter) : 1;
        x += it.w;
      });
    });

    if (style.emoji && cue.emoji && mode !== 'oneword') {
      var epx = fpxFinal * 1.15, pop = anim ? 0.6 + 0.4 * enter : 1;
      ctx.globalAlpha = 1; ctx.textAlign = 'center';
      ctx.font = Math.round(epx * pop) + 'px ' + EMOJI_STACK;
      var ey = top - epx * 0.7 - (mode === 'gibi' ? fpxFinal * 0.4 : 0);
      if (ey < epx * 0.6) ey = top + blockH + epx * 0.75;
      ctx.fillText(cue.emoji, W / 2, ey);
    }
    ctx.restore();
  }

  function luma(hex) {
    var m = /^#?([0-9a-f]{6})$/i.exec(hex || ''); if (!m) return 1;
    var n = parseInt(m[1], 16); return (0.299 * ((n >> 16) & 255) + 0.587 * ((n >> 8) & 255) + 0.114 * (n & 255)) / 255;
  }

  function drawCaptions(ctx, W, H, t) {
    var i = findCue(t);
    if (i !== -1) drawCue(ctx, W, H, state.cues[i], t, state.style);
    return i;
  }

  // ── Pré-visualização ──────────────────────────────────────────────────
  var overlayDims = { w: 0, h: 0 };
  function sizeOverlay() {
    var v = $('video'), c = $('overlay');
    if (!v || !c || !state.vw) return;
    var rect = v.getBoundingClientRect();
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var k = (rect.width * dpr) / state.vw;
    var w = Math.max(2, Math.round(state.vw * k)), h = Math.max(2, Math.round(state.vh * k));
    if (w !== overlayDims.w || h !== overlayDims.h) { c.width = w; c.height = h; overlayDims = { w: w, h: h }; }
  }
  function drawPreview() {
    var v = $('video'), c = $('overlay');
    if (!v || !c || !state.vw) return;
    var ctx = c.getContext('2d');
    ctx.clearRect(0, 0, c.width, c.height);
    var i = drawCaptions(ctx, c.width, c.height, v.currentTime || 0);
    markActiveCue(i);
    var d = state.dur || v.duration || 0;
    $('timecode').textContent = fmtClock(v.currentTime) + ' / ' + fmtClock(d);
    if (!state.scrubbing && d) $('scrub').value = String(Math.round((v.currentTime / d) * 1000));
  }
  var rafId = 0;
  function loop() {
    drawPreview();
    var v = $('video');
    if (v && !v.paused && !v.ended) rafId = requestAnimationFrame(loop); else rafId = 0;
  }
  function startLoop() { if (!rafId) rafId = requestAnimationFrame(loop); }

  var activeCueEl = null;
  function markActiveCue(i) {
    var id = i >= 0 && state.cues[i] ? state.cues[i].id : '';
    if (activeCueEl && activeCueEl.getAttribute('data-cue') === id) return;
    if (activeCueEl) activeCueEl.classList.remove('now');
    activeCueEl = id ? document.querySelector('.cue[data-cue="' + id + '"]') : null;
    if (activeCueEl) activeCueEl.classList.add('now');
  }

  // ── Carregar vídeo ────────────────────────────────────────────────────
  function signatureOf(file, dur) { return [file.name, file.size, Math.round(dur || 0)].join('|'); }

  function loadVideoFile(file, opts) {
    opts = opts || {};
    showNote('');
    if (!file) return Promise.resolve(false);
    if (state.busy || state.exporting) { toast('Aguarde a etapa em andamento terminar.'); return Promise.resolve(false); }
    var okType = /^video\//.test(file.type) || /\.(mp4|mov|m4v|webm|mkv)$/i.test(file.name || '');
    if (!okType) { showNote('Esse arquivo não parece ser um vídeo. Envie um MP4, MOV ou WebM.'); return Promise.resolve(false); }
    if (file.size > MAX_BYTES) { showNote('Esse vídeo tem mais de 500 MB. Exporte uma versão menor (até 1080p) e tente de novo.'); return Promise.resolve(false); }

    var v = $('video');
    if (state.url) { try { URL.revokeObjectURL(state.url); } catch (e) {} }
    clearResult();
    var url = URL.createObjectURL(file);
    return new Promise(function (resolve) {
      var done = false;
      function fail(msg) {
        if (done) return; done = true;
        try { URL.revokeObjectURL(url); } catch (e) {}
        showNote(msg); resolve(false);
      }
      var to = setTimeout(function () { fail('Não consegui abrir esse vídeo neste navegador. Tente exportá-lo em MP4 (H.264).'); }, 15000);
      v.onloadedmetadata = function () {
        if (done) return;
        clearTimeout(to);
        if (!v.videoWidth || !v.videoHeight) { fail('Não encontrei imagem nesse arquivo. Envie um vídeo (MP4, MOV ou WebM).'); return; }
        done = true;
        state.file = file; state.url = url; state.name = file.name || 'video';
        state.dur = isFinite(v.duration) ? v.duration : 0;
        state.vw = v.videoWidth; state.vh = v.videoHeight;
        state.sig = signatureOf(file, state.dur);
        state.isSample = !!opts.sample;
        state.cues = []; state.lastCue = -1;
        $('dropzone').hidden = true; $('player').hidden = false;
        $('screenbox').classList.toggle('is-wide', state.vw > state.vh);
        $('file-meta').textContent = state.vw + '×' + state.vh + ' · ' + fmtClock(state.dur) + (state.dur > MAX_SECONDS ? ' · acima de 3 min' : '');
        var pill = $('file-pill'); pill.textContent = state.name; pill.hidden = false;
        $('stage-caption').textContent = 'Quadro 1 · ' + (state.vw > state.vh ? 'horizontal' : (state.vw === state.vh ? 'quadrado' : 'vertical'));
        if (!opts.sample && restoreProject()) toast('Recuperei as legendas que você já tinha feito para este vídeo.');
        requestAnimationFrame(function () { sizeOverlay(); drawPreview(); });
        renderAll();
        resolve(true);
      };
      v.onerror = function () { clearTimeout(to); fail('Não consegui abrir esse vídeo neste navegador. Tente exportá-lo em MP4 (H.264).'); };
      v.src = url;
      v.load();
    });
  }

  function showNote(msg) { var n = $('dz-note'); n.textContent = msg || ''; n.hidden = !msg; }

  function loadSample() {
    if (state.busy || state.exporting) return;
    var btn = $('sample-btn'); btn.disabled = true;
    var ac = new AbortController(); var to = setTimeout(function () { ac.abort(); }, 20000);
    Promise.all([
      fetch('sample/exemplo.mp4', { signal: ac.signal }).then(function (r) { if (!r.ok) throw new Error('vídeo'); return r.blob(); }),
      fetch('sample/exemplo.json', { signal: ac.signal }).then(function (r) { if (!r.ok) throw new Error('palavras'); return r.json(); })
    ]).then(function (res) {
      var file = new File([res[0]], 'exemplo-legenda-animada.mp4', { type: 'video/mp4' });
      return loadVideoFile(file, { sample: true }).then(function (ok) {
        if (!ok) return;
        state.maxWords = 3; $('in-words').value = '3';
        state.cues = groupCues(cleanWords(res[1].words || []), state.maxWords);
        renderAll(); drawPreview();
        gotoTab('estilo');
        toast('Vídeo de exemplo carregado com a transcrição e a revisão já feitas. Escolha um estilo e dê play.');
      });
    }).catch(function () {
      showNote('Não consegui carregar o vídeo de exemplo agora. Confira a conexão e tente de novo.');
    }).then(function () { clearTimeout(to); btn.disabled = false; });
  }

  // ── Áudio: extrair e reamostrar para WAV 16 kHz mono ─────────────────
  function extractWav(file, signal) {
    return file.arrayBuffer().then(function (ab) {
      if (signal && signal.aborted) throw abortErr();
      var Ctx = window.AudioContext || window.webkitAudioContext;
      var ac = new Ctx();
      return new Promise(function (res, rej) {
        try {
          var p = ac.decodeAudioData(ab, res, function () { rej(new Error('noaudio')); });
          if (p && p.then) p.then(res, function () { rej(new Error('noaudio')); });
        } catch (e) { rej(new Error('noaudio')); }
      }).then(function (buf) {
        try { ac.close(); } catch (e) {}
        if (!buf || !buf.length) throw new Error('noaudio');
        var rate = 16000, len = Math.ceil(buf.duration * rate);
        var off = new OfflineAudioContext(1, len, rate);
        var src = off.createBufferSource(); src.buffer = buf; src.connect(off.destination); src.start(0);
        return off.startRendering();
      }, function (e) { try { ac.close(); } catch (er) {} throw e; });
    }).then(function (rendered) {
      var data = rendered.getChannelData(0);
      var peak = 0; for (var i = 0; i < data.length; i += 40) { var a = Math.abs(data[i]); if (a > peak) peak = a; }
      if (peak < 0.003) throw new Error('silent');
      return encodeWav(data, 16000);
    });
  }
  function encodeWav(samples, rate) {
    var buf = new ArrayBuffer(44 + samples.length * 2), dv = new DataView(buf);
    function str(o, s) { for (var i = 0; i < s.length; i++) dv.setUint8(o + i, s.charCodeAt(i)); }
    str(0, 'RIFF'); dv.setUint32(4, 36 + samples.length * 2, true); str(8, 'WAVE'); str(12, 'fmt ');
    dv.setUint32(16, 16, true); dv.setUint16(20, 1, true); dv.setUint16(22, 1, true); dv.setUint32(24, rate, true);
    dv.setUint32(28, rate * 2, true); dv.setUint16(32, 2, true); dv.setUint16(34, 16, true); str(36, 'data'); dv.setUint32(40, samples.length * 2, true);
    for (var i = 0, o = 44; i < samples.length; i++, o += 2) { var s = Math.max(-1, Math.min(1, samples[i])); dv.setInt16(o, s < 0 ? s * 0x8000 : s * 0x7fff, true); }
    return new Blob([buf], { type: 'audio/wav' });
  }
  function blobToDataUrl(blob) {
    return new Promise(function (res, rej) { var r = new FileReader(); r.onload = function () { res(r.result); }; r.onerror = function () { rej(new Error('leitura')); }; r.readAsDataURL(blob); });
  }
  function abortErr() { var e = new Error('Cancelado.'); e.aborted = true; return e; }
  function sleep(ms, signal) {
    return new Promise(function (res, rej) {
      var t = setTimeout(res, ms);
      if (signal) signal.addEventListener('abort', function () { clearTimeout(t); rej(abortErr()); }, { once: true });
    });
  }
  function limited(endpoint, fn) {
    var p = (window.RateLimiter && RateLimiter.executeWithLimit) ? RateLimiter.executeWithLimit(endpoint, fn) : fn();
    return Promise.resolve(p).then(function (r) { if (r == null) throw new Error('Limite de uso por minuto atingido. Aguarde um pouco e tente de novo.'); return r; });
  }

  // ── Transcrição ───────────────────────────────────────────────────────
  function falError(status, txt) {
    var detail = ''; try { var j = JSON.parse(txt); detail = typeof j.detail === 'string' ? j.detail : (j.detail && j.detail[0] && j.detail[0].msg) || j.message || ''; } catch (e) {}
    if (/exhausted balance|top up|locked/i.test(detail + txt)) return 'Os créditos da sua conta fal.ai acabaram. Recarregue em fal.ai/dashboard/billing e tente de novo.';
    if (status === 401 || status === 403) return 'A fal.ai recusou a chave. Confira se você colou a chave inteira (formato xxxxxxxx-...:xxxxxxxx).';
    if (status === 429) return 'A fal.ai está limitando as requisições. Aguarde alguns segundos e tente de novo.';
    return 'A fal.ai respondeu com erro ' + status + (detail ? ': ' + detail : '.');
  }
  function transcribeFal(wav, key, lang, signal, onStatus) {
    var headers = { 'Authorization': 'Key ' + key, 'Content-Type': 'application/json' };
    return blobToDataUrl(wav).then(function (dataUrl) {
      dataUrl = dataUrl.replace(/^data:audio\/wav/, 'data:audio/x-wav');
      var body = { audio_url: dataUrl, task: 'transcribe', chunk_level: 'word' };
      if (lang) body.language = lang;
      onStatus('Enviando o áudio para a fal.ai…');
      return fetch('https://queue.fal.run/' + FAL_MODEL, { method: 'POST', headers: headers, body: JSON.stringify(body), signal: signal });
    }).then(function (r) {
      return r.text().then(function (txt) {
        if (!r.ok) throw new Error(falError(r.status, txt));
        var j = JSON.parse(txt);
        if (!j.response_url) throw new Error('A fal.ai não devolveu o pedido de transcrição.');
        return j;
      });
    }).then(function (job) {
      var t0 = Date.now();
      function poll() {
        if (Date.now() - t0 > 6 * 60 * 1000) throw new Error('A transcrição passou de 6 minutos. Tente de novo em instantes.');
        return sleep(1500, signal).then(function () {
          return fetch(job.status_url || (job.response_url + '/status'), { headers: { 'Authorization': 'Key ' + key }, signal: signal });
        }).then(function (r) {
          return r.text().then(function (txt) {
            if (!r.ok && r.status !== 202) throw new Error(falError(r.status, txt));
            var s = {}; try { s = JSON.parse(txt); } catch (e) {}
            if (s.status === 'COMPLETED') return fetch(job.response_url, { headers: { 'Authorization': 'Key ' + key }, signal: signal });
            onStatus(s.status === 'IN_QUEUE' ? 'Na fila da fal.ai…' : 'Transcrevendo palavra por palavra…');
            return poll();
          });
        });
      }
      return poll();
    }).then(function (r) {
      return r.text().then(function (txt) {
        if (!r.ok) throw new Error(falError(r.status, txt));
        var d = JSON.parse(txt);
        if (d && d.detail && !d.chunks) throw new Error(falError(r.status, txt));
        var chunks = d.chunks || [];
        return chunks.map(function (c) {
          var ts = c.timestamp || [];
          return { w: String(c.text || '').trim(), s: ts[0], e: ts[1] == null ? (ts[0] + 0.4) : ts[1] };
        });
      });
    });
  }
  function transcribeOpenAI(wav, key, lang, vocab, signal, onStatus) {
    var fd = new FormData();
    fd.append('file', new File([wav], 'audio.wav', { type: 'audio/wav' }));
    fd.append('model', 'whisper-1');
    fd.append('response_format', 'verbose_json');
    fd.append('timestamp_granularities[]', 'word');
    if (lang) fd.append('language', lang);
    if (vocab) fd.append('prompt', vocab.slice(0, 200));
    onStatus('Transcrevendo com o Whisper da OpenAI…');
    return fetch('https://api.openai.com/v1/audio/transcriptions', { method: 'POST', headers: { 'Authorization': 'Bearer ' + key }, body: fd, signal: signal })
      .then(function (r) {
        return r.text().then(function (txt) {
          var j = {}; try { j = JSON.parse(txt); } catch (e) {}
          if (!r.ok) {
            var m = (j.error && j.error.message) || '';
            if (r.status === 401) throw new Error('A OpenAI recusou a chave. Confira a chave sk-... colada.');
            if (r.status === 429 || /quota|billing|credit/i.test(m)) throw new Error('A conta da OpenAI está sem créditos ou no limite de uso' + (m ? ' (' + m + ')' : '') + '.');
            throw new Error('A OpenAI respondeu com erro ' + r.status + (m ? ': ' + m : '.'));
          }
          var words = j.words || [];
          if (!words.length && j.text) throw new Error('A OpenAI devolveu o texto sem o tempo das palavras. Tente de novo.');
          return words.map(function (w) { return { w: w.word, s: w.start, e: w.end }; });
        });
      });
  }

  // ── Revisão com IA (OpenRouter, chave do membro) ──────────────────────
  function fetchLLM(messages, signal) {
    var key = window.ApiKeyManager ? ApiKeyManager.getActiveKey() : null;
    if (!key) return Promise.reject(new Error('sem chave'));
    var model = ApiKeyManager.getModel();
    var body = { model: model, messages: messages, temperature: 0.2, max_tokens: 16000 }; // COR-053
    if (model.indexOf('deepseek/') !== 0) body.reasoning = { effort: 'low' }; // COR-034 / COR-035
    function once() {
      return fetch('https://openrouter.ai/api/v1/chat/completions', {
        method: 'POST', signal: signal,
        headers: { 'Authorization': 'Bearer ' + key.key, 'Content-Type': 'application/json', 'HTTP-Referer': location.origin, 'X-Title': 'Legenda Animada IA - Maestros da IA' },
        body: JSON.stringify(body)
      }).then(function (r) {
        return r.text().then(function (txt) {
          if (!r.ok) {
            var msg = 'Erro ' + r.status + ' da OpenRouter.';
            try { var j = JSON.parse(txt); msg = (j.error && (j.error.message || j.error)) || msg; } catch (e) {}
            if (r.status === 401) msg = 'A OpenRouter recusou a chave. Confira a chave sk-or-... colada.';
            else if (r.status === 402) msg = 'Créditos insuficientes na sua conta OpenRouter.';
            else if (r.status === 429) msg = 'A OpenRouter está limitando as requisições. Aguarde e tente de novo.';
            throw new Error(String(msg));
          }
          var data = JSON.parse(txt);
          var c = data.choices && data.choices[0] && data.choices[0].message && data.choices[0].message.content;
          if (Array.isArray(c)) c = c.map(function (p) { return p && p.text ? p.text : ''; }).join('');
          if (!c || !String(c).trim()) { var em = new Error('Resposta vazia do modelo.'); em.emptyContent = true; throw em; }
          return String(c);
        });
      });
    }
    return limited('openrouter', function () {
      return once().catch(function (e) { if (e && e.emptyContent && body.reasoning) { delete body.reasoning; return once(); } throw e; }); // COR-035
    });
  }
  function parseJSONLadder(raw) {
    var s = String(raw).replace(/```json/gi, '').replace(/```/g, '').trim();
    var a = s.indexOf('{'), b = s.lastIndexOf('}'); if (a !== -1 && b > a) s = s.slice(a, b + 1);
    var tries = [s, s.replace(/,\s*([}\]])/g, '$1')];
    tries.push(tries[1].replace(/[\x00-\x1f]+/g, ' '));
    tries.push(tries[2].replace(/[“”]/g, '"'));
    for (var i = 0; i < tries.length; i++) { try { var o = JSON.parse(tries[i]); if (o && typeof o === 'object') return o; } catch (e) {} }
    return null;
  }
  function reviewPrompt(lang, vocab) {
    var lname = { pt: 'português do Brasil', en: 'inglês', es: 'espanhol' }[lang] || 'o idioma do próprio texto';
    return [
      'Você revisa legendas de vídeos curtos (Reels, TikTok, Shorts). Recebe a transcrição automática como uma lista numerada de palavras no formato "índice|palavra". O idioma é ' + lname + '.',
      'Cada índice corresponde a um trecho do áudio com tempo marcado — por isso você NUNCA junta, separa ou cria palavras: cada correção troca o texto de UM índice por UM texto. Para apagar uma palavra que a transcrição inventou ou repetiu, use o texto vazio "" nesse índice (nunca repita a palavra vizinha no lugar dela).',
      '',
      'Responda SOMENTE com um objeto JSON, sem markdown, com estas chaves:',
      '{"correcoes": [[índice, "texto corrigido"]], "destaques": [índice], "emojis": [[índice, "emoji"]]}',
      '',
      'Regras:',
      '- correcoes: só os índices que mudam. Corrija ortografia, acentos, maiúsculas de início de frase e nomes próprios, e pontuação grudada na palavra (vírgula, ponto, interrogação). Números ditos por extenso viram algarismos quando é o natural numa legenda (ex.: "oitenta e cinco por cento" já transcrito como "85%" fica; "cinco" pode virar "5"). Mantenha gírias e o jeito oral de falar; não reescreva frases, não traduza, não troque palavras por sinônimos.',
      '- destaques: as palavras-chave que merecem cor de destaque — números, a palavra mais forte de cada frase, benefícios, alertas. Mais ou menos uma a cada 4 a 6 palavras. Nunca artigos, preposições ou conectivos.',
      '- emojis: no máximo um a cada 8 a 10 palavras, só quando combinar muito com a palavra (ex.: dinheiro 💰, atenção ⚠️, fogo 🔥, ideia 💡). Pode ser lista vazia.',
      vocab ? '- Estes nomes e termos aparecem no vídeo e devem ser escritos exatamente assim: ' + vocab + '.' : '',
      '- Índices são números inteiros da lista recebida. Não invente índices.'
    ].filter(Boolean).join('\n');
  }
  function reviewWords(words, lang, vocab, signal, onStatus) {
    var CH = 300, chunks = [];
    for (var i = 0; i < words.length; i += CH) chunks.push([i, Math.min(words.length, i + CH)]);
    var out = words.map(function (w) { return Object.assign({}, w); });
    var seq = Promise.resolve();
    chunks.forEach(function (ch, n) {
      seq = seq.then(function () {
        onStatus('Revisando o texto com IA' + (chunks.length > 1 ? ' (' + (n + 1) + '/' + chunks.length + ')' : '') + '…');
        var lines = [];
        for (var k = ch[0]; k < ch[1]; k++) lines.push(k + '|' + words[k].w);
        var msgs = [{ role: 'system', content: reviewPrompt(lang, vocab) }, { role: 'user', content: lines.join('\n') }];
        return fetchLLM(msgs, signal).then(function (txt) {
          var o = parseJSONLadder(txt);
          if (o) return o;
          var strict = msgs.concat([{ role: 'user', content: 'Sua resposta anterior NÃO era um JSON válido. Responda novamente APENAS com o objeto JSON pedido, aspas retas, sem markdown.' }]);
          return fetchLLM(strict, signal).then(function (t2) { var o2 = parseJSONLadder(t2); if (!o2) throw new Error('A revisão não voltou no formato certo.'); return o2; }); // COR-032
        }).then(function (o) {
          var okIdx = function (x) { x = Number(x); return Number.isInteger(x) && x >= ch[0] && x < ch[1] ? x : -1; };
          (Array.isArray(o.correcoes) ? o.correcoes : []).forEach(function (p) {
            var idx = okIdx(p && p[0]), t = p && typeof p[1] === 'string' ? p[1].replace(/\s+/g, ' ').trim() : '';
            if (idx !== -1 && t.length <= 40 && p && typeof p[1] === 'string') { out[idx].w = t; out[idx].fixed = true; }
          });
          (Array.isArray(o.destaques) ? o.destaques : []).forEach(function (x) { var idx = okIdx(x); if (idx !== -1) out[idx].hl = true; });
          (Array.isArray(o.emojis) ? o.emojis : []).forEach(function (p) {
            var idx = okIdx(p && p[0]), e = p && typeof p[1] === 'string' ? p[1].trim() : '';
            if (idx !== -1 && e && e.length <= 8 && !/[\w<>]/.test(e)) out[idx].emoji = e;
          });
        });
      });
    });
    return seq.then(function () { return dropRemoved(out, words); });
  }
  // Tira as palavras apagadas pela revisão ("") e as duplicatas vizinhas que uma
  // correção criou ("o direto." → "direto. direto."), cedendo o tempo à vizinha.
  function norm(w) { return String(w || '').toLocaleLowerCase('pt-BR').replace(/[^\wÀ-ÿ%]/g, ''); }
  function dropRemoved(out, orig) {
    var keep = [];
    out.forEach(function (w, i) {
      var prev = keep[keep.length - 1];
      var dup = w.fixed && prev && norm(w.w) && norm(w.w) === norm(prev.w) && norm(orig[i].w) !== norm(w.w);
      var nextW = out[i + 1];
      var dupNext = w.fixed && nextW && norm(w.w) && norm(w.w) === norm(nextW.w) && norm(orig[i].w) !== norm(w.w);
      if (!w.w || dup || dupNext) {
        if (dupNext && nextW) { nextW.s = Math.min(nextW.s, w.s); if (w.hl) nextW.hl = true; if (w.emoji && !nextW.emoji) nextW.emoji = w.emoji; }
        else if (prev) { prev.e = Math.max(prev.e, w.e); if (w.emoji && !prev.emoji) prev.emoji = w.emoji; }
        return;
      }
      delete w.fixed; keep.push(w);
    });
    keep.forEach(function (w) { delete w.fixed; });
    return keep;
  }

  function runTranscription() {
    if (state.busy || !state.file) return;
    var tr = window.ApiKeyManager ? ApiKeyManager.getTranscriber() : null;
    if (!tr) { syncKeys(); return; }
    if (state.dur > MAX_SECONDS) { showTrError('Este vídeo tem ' + fmtClock(state.dur) + '. A transcrição aceita até 3 minutos por vídeo — corte em partes e legende cada uma.'); return; }
    if (state.cues.length && !confirm('Transcrever de novo substitui as cartelas atuais (e as suas correções). Continuar?')) return;

    var lang = $('in-lang').value, vocab = $('in-vocab').value.trim();
    var wantReview = $('in-review').checked;
    var canReview = wantReview && !!(window.ApiKeyManager && ApiKeyManager.getActiveKey());
    var ac = new AbortController(); state.abort = ac; state.busy = true;
    showTrError(''); setTrProgress(4, 'Tirando o áudio do vídeo…');
    syncButtons();
    var warn = '';
    limited('transcribe', function () {
      return extractWav(state.file, ac.signal).then(function (wav) {
        setTrProgress(18, 'Áudio pronto (' + Math.round(wav.size / 1024) + ' KB). Enviando…');
        var onStatus = function (m) { setTrProgress(Math.min(70, (state.trPct || 18) + 6), m); };
        return tr.service === 'openai'
          ? transcribeOpenAI(wav, tr.key, lang, vocab, ac.signal, onStatus)
          : transcribeFal(wav, tr.key, lang, ac.signal, onStatus);
      });
    }).then(function (raw) {
      var words = cleanWords(raw);
      if (!words.length) throw new Error('Não encontrei fala nesse vídeo. Se ele tem só música, não há o que legendar.');
      setTrProgress(74, words.length + ' palavras transcritas.');
      if (!canReview) {
        if (wantReview) warn = 'Sem chave da OpenRouter: o texto não foi revisado e os destaques foram escolhidos por uma regra simples (números e palavras longas).';
        return heuristicHighlights(words);
      }
      return reviewWords(words, lang, vocab, ac.signal, function (m) { setTrProgress(82, m); }).catch(function (e) {
        if (e && e.aborted) throw e;
        if (e && e.name === 'AbortError') throw abortErr();
        warn = 'A revisão com IA falhou (' + e.message + '). As cartelas usam a transcrição original — você pode corrigir à mão.';
        return heuristicHighlights(words);
      });
    }).then(function (words) {
      state.maxWords = Number($('in-words').value) || 3;
      state.cues = groupCues(words, state.maxWords);
      state.lastCue = -1;
      saveProject();
      setTrProgress(100, 'Pronto: ' + state.cues.length + ' cartelas.');
      renderAll(); drawPreview();
      gotoTab('texto');
      toast(warn || 'Transcrição pronta. Confira as cartelas e escolha o estilo.');
      if (warn) showTrError(warn, true);
    }).catch(function (e) {
      if ((e && e.aborted) || (e && e.name === 'AbortError')) { setTrProgress(0, ''); toast('Transcrição cancelada.'); return; }
      var m = e && e.message;
      if (m === 'noaudio') m = 'Não consegui ler o áudio desse vídeo. Ele pode estar sem som, ou num formato de áudio que este navegador não abre — exporte em MP4 (H.264 + AAC).';
      else if (m === 'silent') m = 'O áudio desse vídeo está em silêncio. Não há fala para legendar.';
      else if (e instanceof TypeError || /Failed to fetch|NetworkError/i.test(m || '')) m = 'Falha de conexão com o provedor de transcrição. Confira a internet e tente de novo.';
      showTrError(m || 'Algo deu errado na transcrição.');
      setTrProgress(0, '');
    }).then(function () {
      state.busy = false; state.abort = null; syncButtons();
      setTimeout(function () { if (!state.busy) $('tr-progress').hidden = true; }, 1600);
    });
  }
  function setTrProgress(pct, text) {
    state.trPct = pct;
    $('tr-progress').hidden = !pct && !text;
    $('tr-fill').style.width = pct + '%';
    $('tr-text').textContent = text || '';
  }
  function showTrError(msg, soft) { var e = $('tr-error'); e.textContent = msg || ''; e.hidden = !msg; e.classList.toggle('soft', !!soft); }

  // ── Projetos salvos (legendas por vídeo, neste navegador) ─────────────
  function saveProject() {
    if (!state.sig || state.isSample) return;
    var data = { name: state.name, dur: state.dur, maxWords: state.maxWords, savedAt: Date.now(), words: flatWords() };
    var idx = []; try { idx = JSON.parse(lsGet(PROJ_INDEX) || '[]'); } catch (e) {}
    idx = idx.filter(function (x) { return x !== state.sig; }); idx.unshift(state.sig);
    while (idx.length > 12) lsDel(PROJ_PREFIX + idx.pop());
    lsSet(PROJ_PREFIX + state.sig, JSON.stringify(data)); lsSet(PROJ_INDEX, JSON.stringify(idx));
  }
  var saveTimer = null;
  function saveSoon() { clearTimeout(saveTimer); saveTimer = setTimeout(saveProject, 400); }
  function restoreProject() {
    var raw = lsGet(PROJ_PREFIX + state.sig); if (!raw) return false;
    try {
      var d = JSON.parse(raw); if (!d.words || !d.words.length) return false;
      state.maxWords = d.maxWords || 3; $('in-words').value = String(state.maxWords);
      state.cues = groupCues(cleanWords(d.words), state.maxWords);
      return true;
    } catch (e) { return false; }
  }

  // ── Estilo ────────────────────────────────────────────────────────────
  function loadStyle() {
    try { var s = JSON.parse(lsGet(STYLE_SLOT) || 'null'); if (s && s.mode) state.style = Object.assign({}, DEFAULT_STYLE, s); } catch (e) {}
  }
  function saveStyle() { lsSet(STYLE_SLOT, JSON.stringify(state.style)); }
  function styleToControls() {
    var s = state.style;
    $('st-font').value = s.font; $('st-anim').value = s.anim; $('st-size').value = String(s.size); $('st-pos').value = String(s.pos);
    $('st-color').value = s.color; $('st-hl').value = s.hl; $('st-upper').checked = !!s.upper; $('st-emoji').checked = !!s.emoji;
    $('st-size-out').textContent = String(s.size).replace('.', ',');
    $('st-pos-out').textContent = s.pos + '% da altura';
    document.querySelectorAll('.preset').forEach(function (b) {
      var on = b.getAttribute('data-preset') === s.preset;
      b.classList.toggle('on', on); b.setAttribute('aria-checked', on ? 'true' : 'false'); b.tabIndex = on ? 0 : -1;
    });
    $('load-style').hidden = !lsGet(MYSTYLE_SLOT);
  }
  function applyPreset(id) {
    var p = PRESETS.filter(function (x) { return x.id === id; })[0]; if (!p) return;
    state.style = Object.assign({}, state.style, p.st, { preset: id });
    saveStyle(); styleToControls(); ensureFont().then(drawPreview);
  }
  function onStyleInput() {
    var s = state.style;
    s.font = $('st-font').value; s.anim = $('st-anim').value; s.size = Number($('st-size').value); s.pos = Number($('st-pos').value);
    s.color = $('st-color').value; s.hl = $('st-hl').value; s.upper = $('st-upper').checked; s.emoji = $('st-emoji').checked;
    $('st-size-out').textContent = String(s.size).replace('.', ',');
    $('st-pos-out').textContent = s.pos + '% da altura';
    saveStyle(); ensureFont().then(drawPreview);
  }
  function ensureFont() {
    var f = FONT_SPEC[state.style.font] || FONT_SPEC.Montserrat;
    if (!document.fonts || !document.fonts.load) return Promise.resolve();
    return Promise.race([document.fonts.load(f.weight + ' 40px ' + f.css), sleep(3000)]).catch(function () {});
  }

  var THUMB_CUE = { s: 0, e: 9, emoji: '🔥', words: [{ w: 'Legenda', s: 0, e: 1, hl: false }, { w: 'que', s: 1, e: 2, hl: false }, { w: 'prende', s: 2, e: 3, hl: true }] };
  function renderPresets() {
    var box = $('presets');
    box.innerHTML = PRESETS.map(function (p) {
      return '<button type="button" class="preset" role="radio" aria-checked="false" data-preset="' + p.id + '">' +
        '<canvas class="preset-canvas" width="240" height="150" aria-hidden="true"></canvas>' +
        '<span class="preset-name">' + esc(p.name) + '</span><span class="preset-desc">' + esc(p.desc) + '</span></button>';
    }).join('');
    var fonts = Object.keys(FONT_SPEC).map(function (k) { return document.fonts && document.fonts.load ? document.fonts.load(FONT_SPEC[k].weight + ' 30px ' + FONT_SPEC[k].css) : null; });
    Promise.race([Promise.all(fonts), sleep(3000)]).catch(function () {}).then(function () {
      box.querySelectorAll('.preset').forEach(function (b) {
        var p = PRESETS.filter(function (x) { return x.id === b.getAttribute('data-preset'); })[0];
        var c = b.querySelector('canvas'), ctx = c.getContext('2d');
        var g = ctx.createLinearGradient(0, 0, 240, 150); g.addColorStop(0, '#1d3557'); g.addColorStop(0.55, '#a8324a'); g.addColorStop(1, '#f4a259');
        ctx.fillStyle = g; ctx.fillRect(0, 0, 240, 150);
        var st = Object.assign({}, p.st, { pos: 56, emoji: false, size: p.st.size * 1.9 });
        drawCue(ctx, 240, 150, THUMB_CUE, 1.5, st);
      });
    });
  }

  // ── Cartelas (lista editável) ─────────────────────────────────────────
  function renderCues() {
    var list = $('cue-list');
    activeCueEl = null;
    if (!state.cues.length) { list.innerHTML = ''; $('cues-empty').hidden = false; return; }
    $('cues-empty').hidden = true;
    list.innerHTML = state.cues.map(function (c, i) {
      return '<div class="cue" data-cue="' + c.id + '">' +
        '<div class="cue-head">' +
          '<span class="cue-n">' + (i + 1) + '</span>' +
          '<button type="button" class="cue-time" data-act="seek" title="Ir para esta cartela no vídeo">' + fmtCue(c.s) + ' → ' + fmtCue(c.e) + '</button>' +
          '<input type="text" class="cue-emoji" data-act="emoji" maxlength="8" value="' + esc(c.emoji || '') + '" aria-label="Emoji da cartela ' + (i + 1) + '" placeholder="emoji">' +
        '</div>' +
        '<div class="cue-balloon"><input type="text" class="cue-text" data-act="text" value="' + esc(cueToText(c)) + '" aria-label="Texto da cartela ' + (i + 1) + '"></div>' +
        '<div class="cue-times">' +
          '<span class="cue-tools-label">Início</span>' +
          '<button type="button" class="nudge" data-act="s-" aria-label="Começar 0,1 s antes">−0,1</button>' +
          '<button type="button" class="nudge" data-act="s+" aria-label="Começar 0,1 s depois">+0,1</button>' +
          '<span class="cue-tools-label">Fim</span>' +
          '<button type="button" class="nudge" data-act="e-" aria-label="Terminar 0,1 s antes">−0,1</button>' +
          '<button type="button" class="nudge" data-act="e+" aria-label="Terminar 0,1 s depois">+0,1</button>' +
        '</div><div class="cue-tools">' +
          (i < state.cues.length - 1 ? '<button type="button" class="cue-btn" data-act="merge">Juntar com a próxima</button>' : '') +
          (c.words.length > 1 ? '<button type="button" class="cue-btn" data-act="split">Dividir</button>' : '') +
          '<button type="button" class="cue-btn cue-btn-del" data-act="del">Apagar</button>' +
        '</div></div>';
    }).join('');
  }
  function cueIndex(el) {
    var box = el.closest('.cue'); if (!box) return -1;
    var id = box.getAttribute('data-cue');
    for (var i = 0; i < state.cues.length; i++) if (state.cues[i].id === id) return i;
    return -1;
  }
  function onCueClick(e) {
    var b = e.target.closest('button[data-act]'); if (!b) return;
    var i = cueIndex(b); if (i === -1) return;
    var act = b.getAttribute('data-act'), c = state.cues[i];
    if (act === 'seek') { seekTo(c.s + 0.01); return; }
    if (act === 'del') { state.cues.splice(i, 1); }
    else if (act === 'merge') {
      var n = state.cues[i + 1]; if (!n) return;
      c.words = c.words.concat(n.words); c.e = Math.max(c.e, n.e); c.emoji = c.emoji || n.emoji; state.cues.splice(i + 1, 1);
    } else if (act === 'split') {
      if (c.words.length < 2) return;
      var mid = Math.ceil(c.words.length / 2);
      var second = { id: 'c' + (++state.seq), words: c.words.slice(mid), s: c.words[mid].s, e: c.e, emoji: '' };
      c.words = c.words.slice(0, mid); c.e = second.s;
      state.cues.splice(i + 1, 0, second);
    } else if (/^[se][+-]$/.test(act)) {
      var d = act.charAt(1) === '+' ? 0.1 : -0.1;
      var prev = state.cues[i - 1], next = state.cues[i + 1];
      if (act.charAt(0) === 's') {
        c.s = clamp(Math.round((c.s + d) * 100) / 100, prev ? prev.e : 0, c.e - 0.15);
        if (c.words[0]) c.words[0].s = Math.max(c.s, Math.min(c.words[0].s, c.e));
        if (d > 0) c.words.forEach(function (w) { if (w.s < c.s) w.s = c.s; });
        else if (c.words[0]) c.words[0].s = c.s;
      } else {
        c.e = clamp(Math.round((c.e + d) * 100) / 100, c.s + 0.15, next ? next.s : (state.dur || c.e + 5));
        c.words.forEach(function (w) { if (w.s > c.e - 0.05) w.s = c.e - 0.05; if (w.e > c.e) w.e = c.e; });
      }
      var tm = b.closest('.cue').querySelector('.cue-time'); if (tm) tm.textContent = fmtCue(c.s) + ' → ' + fmtCue(c.e);
      state.lastCue = -1; saveSoon(); seekTo(act.charAt(0) === 's' ? c.s + 0.01 : Math.max(c.s, c.e - 0.5));
      return;
    }
    state.lastCue = -1; saveSoon(); renderCues(); renderCounts(); drawPreview();
  }
  function onCueInput(e) {
    var inp = e.target; var act = inp.getAttribute('data-act'); if (!act) return;
    var i = cueIndex(inp); if (i === -1) return;
    var c = state.cues[i];
    if (act === 'text') {
      var toks = parseCueText(inp.value);
      if (toks.length) retimeCue(c, toks); else c.words = [];
    } else if (act === 'emoji') {
      c.emoji = inp.value.trim();
    }
    saveSoon(); drawPreview();
  }
  function onCueChange(e) {
    var inp = e.target; if (inp.getAttribute('data-act') !== 'text') return;
    var i = cueIndex(inp); if (i === -1) return;
    if (!state.cues[i].words.length) { state.cues.splice(i, 1); state.lastCue = -1; saveSoon(); renderCues(); renderCounts(); drawPreview(); }
    else inp.value = cueToText(state.cues[i]);
  }
  function regroup() {
    if (!state.cues.length) return;
    state.maxWords = Number($('in-words').value) || 3;
    state.cues = groupCues(flatWords(), state.maxWords);
    state.lastCue = -1; saveProject(); renderCues(); renderCounts(); drawPreview();
    toast('Cartelas refeitas: ' + state.cues.length + '.');
  }

  function seekTo(t) {
    var v = $('video'); if (!v || !state.vw) return;
    try { v.currentTime = clamp(t, 0, Math.max(0, (state.dur || v.duration) - 0.05)); } catch (e) {}
  }

  // ── Exportar (gravar o vídeo com a legenda) ───────────────────────────
  function pickMime() {
    if (!window.MediaRecorder) return null;
    var c = ['video/mp4;codecs=avc1.640028,mp4a.40.2', 'video/mp4;codecs=avc1.42E01F,mp4a.40.2', 'video/mp4;codecs=avc1,mp4a', 'video/mp4',
      'video/webm;codecs=vp9,opus', 'video/webm;codecs=vp8,opus', 'video/webm'];
    for (var i = 0; i < c.length; i++) { try { if (MediaRecorder.isTypeSupported(c[i])) return c[i]; } catch (e) {} }
    return null;
  }
  function formatNote() {
    var m = pickMime(), n = $('format-note');
    if (!m) { n.textContent = 'Este navegador não consegue gravar vídeo. Use o Chrome, o Edge ou o Firefox no computador — ou baixe o .SRT.'; n.classList.add('bad'); return; }
    n.classList.remove('bad');
    n.textContent = /mp4/.test(m) ? 'Formato de saída: MP4 (H.264 + áudio AAC) — sobe direto no Instagram, TikTok e YouTube.'
      : 'Formato de saída: WebM (este navegador não grava MP4). O YouTube aceita WebM; para o Instagram, abra no Chrome atualizado para gravar em MP4.';
  }

  function runExport() {
    if (state.exporting || state.busy || !state.cues.length || !state.url) return;
    var mime = pickMime();
    if (!mime) { formatNote(); return; }
    var target = Number($('ex-res').value) || 1080;
    var k = Math.min(1, target / Math.min(state.vw, state.vh));
    var W = Math.round(state.vw * k / 2) * 2, H = Math.round(state.vh * k / 2) * 2;
    var preview = $('video'); try { preview.pause(); } catch (e) {}
    clearResult(); showExError('');
    var job = { cancelled: false, iv: 0, rvfc: 0 };
    state.exporting = job; syncButtons();
    setExProgress(1, 'Preparando a gravação…');

    var canvas = document.createElement('canvas'); canvas.width = W; canvas.height = H;
    var ctx = canvas.getContext('2d', { alpha: false });
    var v = document.createElement('video');
    v.playsInline = true; v.preload = 'auto'; v.src = state.url; v.muted = false; v.volume = 1;
    job.video = v;
    var ac = null, recorder = null, chunks = [];

    function cleanup() {
      clearInterval(job.iv); clearInterval(job.watch);
      try { if (job.rvfc && v.cancelVideoFrameCallback) v.cancelVideoFrameCallback(job.rvfc); } catch (e) {}
      try { v.pause(); } catch (e) {}
      v.removeAttribute('src'); try { v.load(); } catch (e) {}
      if (ac) { try { ac.close(); } catch (e) {} }
      document.removeEventListener('visibilitychange', onVis);
    }
    function finish(err) {
      if (state.exporting !== job) return;
      cleanup(); state.exporting = null; syncButtons();
      if (err) { setExProgress(0, ''); showExError(err); }
    }
    function frame() {
      if (v.readyState >= 2) { ctx.drawImage(v, 0, 0, W, H); drawCaptions(ctx, W, H, v.currentTime); }
      var d = state.dur || v.duration || 1;
      setExProgress(Math.max(2, Math.min(99, Math.round(v.currentTime / d * 100))), 'Gravando… ' + fmtClock(v.currentTime) + ' de ' + fmtClock(d));
    }
    job.stop = function () {
      job.cancelled = true;
      try { if (recorder && recorder.state !== 'inactive') recorder.stop(); } catch (e) {}
      finish(''); setExProgress(0, '');
    };
    function onVis() {
      if (!recorder || recorder.state === 'inactive') return;
      if (document.hidden) { try { v.pause(); recorder.pause(); } catch (e) {} }
      else { try { recorder.resume(); v.play(); } catch (e) {} }
    }

    new Promise(function (res, rej) {
      var to = setTimeout(function () { rej(new Error('Não consegui preparar o vídeo para gravar. Tente de novo.')); }, 15000);
      v.onloadeddata = function () { clearTimeout(to); res(); };
      v.onerror = function () { clearTimeout(to); rej(new Error('Não consegui ler o vídeo para gravar.')); };
    }).then(ensureFont).then(function () {
      if (job.cancelled) throw abortErr();
      var stream = canvas.captureStream(30);
      try {
        var Ctx = window.AudioContext || window.webkitAudioContext;
        ac = new Ctx();
        var src = ac.createMediaElementSource(v), dest = ac.createMediaStreamDestination();
        src.connect(dest);
        dest.stream.getAudioTracks().forEach(function (t) { stream.addTrack(t); });
      } catch (e) { /* sem trilha de áudio utilizável: grava só a imagem */ }
      var vbps = Math.min(12e6, Math.max(2.5e6, Math.round(W * H * 30 * 0.11)));
      recorder = new MediaRecorder(stream, { mimeType: mime, videoBitsPerSecond: vbps, audioBitsPerSecond: 128000 });
      recorder.ondataavailable = function (e) { if (e.data && e.data.size) chunks.push(e.data); };
      recorder.onstop = function () {
        if (job.cancelled) return;
        var type = mime.split(';')[0];
        var blob = new Blob(chunks, { type: type });
        finish('');
        if (!blob.size) { showExError('A gravação saiu vazia. Deixe a aba visível durante a gravação e tente de novo.'); return; }
        showResult(blob, type, W, H);
      };
      ctx.fillStyle = '#000'; ctx.fillRect(0, 0, W, H);
      if (v.requestVideoFrameCallback) {
        var cb = function () { if (state.exporting !== job) return; frame(); job.rvfc = v.requestVideoFrameCallback(cb); };
        job.rvfc = v.requestVideoFrameCallback(cb);
      }
      job.iv = setInterval(function () { if (!v.paused) frame(); }, 1000 / 30);
      var lastT = -1, still = 0;
      job.watch = setInterval(function () {
        if (v.paused || document.hidden) { still = 0; return; }
        if (Math.abs(v.currentTime - lastT) < 0.01) { still++; } else { still = 0; lastT = v.currentTime; }
        if (still >= 8) { job.cancelled = true; try { recorder.stop(); } catch (e) {} finish('A gravação travou. Deixe esta aba aberta e visível e tente de novo.'); }
      }, 1000);
      v.onended = function () { frame(); setTimeout(function () { try { if (recorder.state !== 'inactive') recorder.stop(); } catch (e) {} }, 120); };
      document.addEventListener('visibilitychange', onVis);
      v.currentTime = 0;
      recorder.start(1000);
      frame();
      return v.play();
    }).catch(function (e) {
      if (e && e.aborted) { finish(''); setExProgress(0, ''); return; }
      finish((e && e.message) || 'Não consegui gravar o vídeo neste navegador.');
    });
  }
  function cancelExport() {
    var job = state.exporting; if (!job || !job.stop) return;
    job.stop(); toast('Gravação interrompida.');
  }
  function setExProgress(pct, text) {
    $('ex-progress').hidden = !pct && !text;
    $('ex-fill').style.width = pct + '%';
    $('ex-text').textContent = text || '';
  }
  function showExError(msg) { var e = $('ex-error'); e.textContent = msg || ''; e.hidden = !msg; }
  function baseName() { return (state.name || 'video').replace(/\.[^.]+$/, '').replace(/[^\w\-À-ÿ]+/g, '-').replace(/-+/g, '-').slice(0, 60) || 'video'; }
  function showResult(blob, type, W, H) {
    if (state.resultUrl) { try { URL.revokeObjectURL(state.resultUrl); } catch (e) {} }
    state.resultUrl = URL.createObjectURL(blob);
    var ext = /mp4/.test(type) ? 'mp4' : 'webm';
    $('result-video').src = state.resultUrl;
    var a = $('dl-video'); a.href = state.resultUrl; a.download = baseName() + '-legendado.' + ext;
    a.textContent = 'Baixar o vídeo (.' + ext + ')';
    $('result-meta').textContent = W + '×' + H + ' · ' + ext.toUpperCase() + ' · ' + (blob.size / 1048576).toFixed(1).replace('.', ',') + ' MB';
    $('result').hidden = false;
    setExProgress(100, 'Vídeo gravado.');
    setTimeout(function () { if (!state.exporting) $('ex-progress').hidden = true; }, 1500);
    toast('Vídeo legendado pronto para baixar.');
  }
  function clearResult() {
    if (state.resultUrl) { try { URL.revokeObjectURL(state.resultUrl); } catch (e) {} state.resultUrl = ''; }
    var r = $('result'); if (r) r.hidden = true;
    var rv = $('result-video'); if (rv) rv.removeAttribute('src');
  }

  function downloadText(name, text, type) {
    var blob = new Blob([text], { type: type || 'text/plain;charset=utf-8' });
    var url = URL.createObjectURL(blob), a = document.createElement('a');
    a.href = url; a.download = name; document.body.appendChild(a); a.click(); a.remove();
    setTimeout(function () { URL.revokeObjectURL(url); }, 2000);
  }
  function plainCue(c) { return c.words.map(function (w) { return w.w; }).join(' '); }
  function exportSrt() {
    if (!state.cues.length) return;
    var out = state.cues.map(function (c, i) { return (i + 1) + '\n' + fmtSrt(c.s) + ' --> ' + fmtSrt(c.e) + '\n' + plainCue(c) + '\n'; }).join('\n');
    downloadText(baseName() + '.srt', out, 'application/x-subrip;charset=utf-8');
  }
  function exportTxt() {
    if (!state.cues.length) return;
    downloadText(baseName() + '.txt', state.cues.map(plainCue).join(' ').replace(/\s+([.,!?;:])/g, '$1') + '\n');
  }

  // ── Estado da interface ───────────────────────────────────────────────
  function syncKeys() {
    if (!window.ApiKeyManager) return;
    var sel = $('in-provider'), cur = ApiKeyManager.getTranscriber();
    var opts = [['fal', 'fal.ai (Whisper)'], ['openai', 'OpenAI (Whisper)']];
    sel.innerHTML = opts.map(function (o) {
      var has = !!ApiKeyManager.getKey(o[0]);
      return '<option value="' + o[0] + '"' + (has ? '' : ' disabled') + '>' + o[1] + (has ? '' : ' — sem chave') + '</option>';
    }).join('');
    if (cur) sel.value = cur.service;
    var hasRouter = !!ApiKeyManager.getActiveKey();
    var w = $('key-warn'), msg = '';
    if (!cur) msg = 'Conecte uma chave da fal.ai ou da OpenAI (ícone de chave no topo) para transcrever. Sem chave, dá para experimentar com o vídeo de exemplo.';
    else if ($('in-review').checked && !hasRouter) msg = 'Sem chave da OpenRouter, o texto não é revisado e os destaques saem por uma regra simples. Adicione a chave no ícone de chave, ou desmarque a revisão.';
    w.textContent = msg; w.hidden = !msg;
    $('review-model-field').hidden = !$('in-review').checked;
    syncButtons();
  }
  function syncButtons() {
    var hasT = !!(window.ApiKeyManager && ApiKeyManager.getTranscriber());
    var busy = state.busy || !!state.exporting;
    $('transcribe-btn').disabled = busy || !state.file || !hasT || state.dur > MAX_SECONDS;
    $('transcribe-btn').textContent = state.cues.length && !state.isSample ? 'Transcrever de novo' : 'Transcrever o vídeo';
    $('cancel-btn').hidden = !state.busy;
    $('export-btn').disabled = busy || !state.cues.length || !pickMime();
    $('export-cancel').hidden = !state.exporting;
    $('dl-srt').disabled = !state.cues.length; $('dl-txt').disabled = !state.cues.length;
    $('regroup-btn').disabled = busy || !state.cues.length;
    $('change-video').disabled = busy; $('sample-btn').disabled = busy;
    $('dropzone').classList.toggle('is-off', busy);
    if (state.file && state.dur > MAX_SECONDS && !state.busy) showTrError('Este vídeo tem ' + fmtClock(state.dur) + '. A transcrição aceita até 3 minutos por vídeo — corte em partes e legende cada uma.');
  }
  function renderCounts() {
    var n = $('count-cues'); n.textContent = String(state.cues.length); n.hidden = !state.cues.length;
    syncButtons();
  }
  function renderAll() { renderCues(); renderCounts(); syncKeys(); formatNote(); }

  function gotoTab(name) {
    document.querySelectorAll('.tab').forEach(function (t) {
      var on = t.getAttribute('data-tab') === name;
      t.classList.toggle('on', on); t.setAttribute('aria-selected', on ? 'true' : 'false'); t.tabIndex = on ? 0 : -1;
    });
    document.querySelectorAll('.pane').forEach(function (p) { p.classList.toggle('on', p.id === 'pane-' + name); });
    if (window.matchMedia && window.matchMedia('(max-width: 900px)').matches) {
      var bench = document.querySelector('.bench'); if (bench && bench.getBoundingClientRect().top < 0) bench.scrollIntoView({ block: 'start' });
    }
  }

  function init() {
    if (state.wired) { var s = $('model-select'); if (window.ApiKeyManager && s && !s.options.length) ApiKeyManager.renderModelPicker('model-select'); syncKeys(); return; }
    state.wired = true;
    if (window.ApiKeyManager) ApiKeyManager.renderModelPicker('model-select'); // COR-041/047
    loadStyle(); renderPresets(); styleToControls();

    document.querySelectorAll('.tab').forEach(function (b) { b.addEventListener('click', function () { gotoTab(b.getAttribute('data-tab')); }); });
    document.querySelector('.tabs').addEventListener('keydown', function (e) {
      if (e.key !== 'ArrowRight' && e.key !== 'ArrowLeft') return;
      var tabs = Array.prototype.slice.call(document.querySelectorAll('.tab'));
      var i = tabs.indexOf(document.activeElement); if (i === -1) return;
      var n = tabs[(i + (e.key === 'ArrowRight' ? 1 : tabs.length - 1)) % tabs.length];
      n.focus(); gotoTab(n.getAttribute('data-tab')); e.preventDefault();
    });

    var dz = $('dropzone'), fi = $('file-input');
    fi.addEventListener('change', function () { var f = fi.files && fi.files[0]; loadVideoFile(f).then(function () { fi.value = ''; }); });
    ['dragenter', 'dragover'].forEach(function (ev) { dz.addEventListener(ev, function (e) { e.preventDefault(); dz.classList.add('drag'); }); });
    ['dragleave', 'drop'].forEach(function (ev) { dz.addEventListener(ev, function (e) { e.preventDefault(); dz.classList.remove('drag'); }); });
    dz.addEventListener('drop', function (e) { if (e.dataTransfer && e.dataTransfer.files.length) loadVideoFile(e.dataTransfer.files[0]); });
    window.addEventListener('dragover', function (e) { e.preventDefault(); });
    window.addEventListener('drop', function (e) {
      e.preventDefault();
      if (!$('player').hidden && e.dataTransfer && e.dataTransfer.files.length && !state.busy && !state.exporting) loadVideoFile(e.dataTransfer.files[0]);
    });
    $('change-video').addEventListener('click', function () { if (!state.busy && !state.exporting) fi.click(); });
    $('sample-btn').addEventListener('click', loadSample);

    var v = $('video');
    v.addEventListener('play', function () { $('play-btn').classList.add('playing'); $('play-btn').setAttribute('aria-label', 'Pausar'); startLoop(); });
    v.addEventListener('pause', function () { $('play-btn').classList.remove('playing'); $('play-btn').setAttribute('aria-label', 'Reproduzir'); drawPreview(); });
    v.addEventListener('seeked', drawPreview);
    v.addEventListener('timeupdate', function () { if (v.paused) drawPreview(); });
    $('play-btn').addEventListener('click', function () { if (!state.vw) return; if (v.paused) { var p = v.play(); if (p && p.catch) p.catch(function () {}); } else v.pause(); });
    $('mute-btn').addEventListener('click', function () { v.muted = !v.muted; this.classList.toggle('is-muted', v.muted); this.setAttribute('aria-pressed', v.muted ? 'true' : 'false'); this.setAttribute('aria-label', v.muted ? 'Ligar o som' : 'Tirar o som'); });
    var sc = $('scrub');
    sc.addEventListener('input', function () { state.scrubbing = true; var d = state.dur || v.duration || 0; seekTo(d * Number(sc.value) / 1000); });
    sc.addEventListener('change', function () { state.scrubbing = false; });
    window.addEventListener('resize', function () { sizeOverlay(); drawPreview(); });
    if (window.ResizeObserver) new ResizeObserver(function () { sizeOverlay(); drawPreview(); }).observe($('screenbox'));

    $('transcribe-btn').addEventListener('click', runTranscription);
    $('cancel-btn').addEventListener('click', function () { if (state.abort) state.abort.abort(); });
    $('in-provider').addEventListener('change', function () { ApiKeyManager.setTranscriber(this.value); syncKeys(); });
    $('in-review').addEventListener('change', syncKeys);
    document.addEventListener('legenda:keys-changed', syncKeys);
    var km = $('key-modal');
    if (km && window.MutationObserver) new MutationObserver(function () { if (km.style.display === 'none') syncKeys(); }).observe(km, { attributes: true, attributeFilter: ['style'] });

    var cl = $('cue-list');
    cl.addEventListener('click', onCueClick);
    cl.addEventListener('input', onCueInput);
    cl.addEventListener('change', onCueChange);
    cl.addEventListener('keydown', function (e) { if (e.key === 'Enter' && e.target.matches('input')) { e.preventDefault(); e.target.blur(); } });
    $('regroup-btn').addEventListener('click', regroup);

    $('presets').addEventListener('click', function (e) { var b = e.target.closest('.preset'); if (b) applyPreset(b.getAttribute('data-preset')); });
    $('presets').addEventListener('keydown', function (e) {
      if (['ArrowRight', 'ArrowDown', 'ArrowLeft', 'ArrowUp'].indexOf(e.key) === -1) return;
      var bs = Array.prototype.slice.call(document.querySelectorAll('.preset'));
      var i = bs.indexOf(document.activeElement); if (i === -1) return;
      var n = bs[(i + (e.key === 'ArrowRight' || e.key === 'ArrowDown' ? 1 : bs.length - 1)) % bs.length];
      n.focus(); applyPreset(n.getAttribute('data-preset')); e.preventDefault();
    });
    ['st-font', 'st-anim', 'st-size', 'st-pos', 'st-color', 'st-hl', 'st-upper', 'st-emoji'].forEach(function (id) {
      $(id).addEventListener('input', onStyleInput); $(id).addEventListener('change', onStyleInput);
    });
    $('save-style').addEventListener('click', function () { lsSet(MYSTYLE_SLOT, JSON.stringify(state.style)); styleToControls(); toast('Estilo salvo. Ele fica disponível nos próximos vídeos, neste navegador.'); });
    $('load-style').addEventListener('click', function () {
      try { var s = JSON.parse(lsGet(MYSTYLE_SLOT) || 'null'); if (s) { state.style = Object.assign({}, DEFAULT_STYLE, s); saveStyle(); styleToControls(); ensureFont().then(drawPreview); toast('Usando o seu estilo salvo.'); } } catch (e) {}
    });

    $('export-btn').addEventListener('click', runExport);
    $('export-cancel').addEventListener('click', cancelExport);
    $('dl-srt').addEventListener('click', exportSrt);
    $('dl-txt').addEventListener('click', exportTxt);

    // COR-062: ao sair, o formulário de login fica vazio para a próxima pessoa
    var lo = $('logout-btn');
    if (lo) lo.addEventListener('click', function () {
      var em = $('gate-email'), ph = $('gate-phone'), er = $('gate-error');
      if (em) em.value = ''; if (ph) ph.value = ''; if (er) { er.textContent = ''; er.style.display = 'none'; }
      try { v.pause(); } catch (e) {}
    });
    $('wipe-local').addEventListener('click', function () {
      if (state.busy || state.exporting) { toast('Aguarde a etapa em andamento terminar.'); return; }
      if (!confirm('Apagar deste navegador as legendas salvas, o seu estilo, as suas chaves de IA e a sua sessão? Isso não pode ser desfeito.')) return;
      try {
        var drop = [];
        for (var i = 0; i < localStorage.length; i++) { var k = localStorage.key(i); if (k.indexOf(NS) === 0 || k.indexOf('maestria_') === 0) drop.push(k); }
        drop.forEach(function (k) { localStorage.removeItem(k); });
      } catch (e) {}
      location.reload();
    });
    window.addEventListener('beforeunload', function (e) {
      if (state.exporting || state.busy) { e.preventDefault(); e.returnValue = ''; }
    });

    renderAll();
  }

  return {
    init: init,
    _group: groupCues, _clean: cleanWords, _parse: parseCueText, _state: function () { return state; },
    _dump: function () { return { words: flatWords() }; }
  };
})();

// ── Gatilhos de inicialização: evento + DOMContentLoaded + MutationObserver (COR-044) ──
(function () {
  function go() { App.init(); }
  document.addEventListener('maestria:app-ready', go);
  document.addEventListener('DOMContentLoaded', function () {
    var app = document.getElementById('app-screen');
    if (app && app.classList.contains('active')) setTimeout(go, 100);
    if (app) {
      var mo = new MutationObserver(function () { if (app.classList.contains('active')) go(); });
      mo.observe(app, { attributes: true, attributeFilter: ['class'] });
    }
  });
})();

// As chaves ficam em <form>s; Enter não pode recarregar a página.
document.addEventListener('submit', function (e) {
  var f = e.target;
  if (f && (f.id === 'key-inputs' || f.id === 'modal-key-inputs')) e.preventDefault();
});
