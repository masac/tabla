// ====================================================================
// COD COMPLET - VERSIUNE FINALĂ 
// ====================================================================

pdfjsLib.GlobalWorkerOptions.workerSrc = _pdfWorkerSrc;

const wrap = document.getElementById('canvas-wrap');
const boardBgC = document.getElementById('bg-canvas');
const boardDrawC = document.getElementById('draw-canvas');
const boardOverlayC = document.getElementById('overlay-canvas');
const boardSelC = document.getElementById('selection-canvas');
const imagesContainer = document.getElementById('images-container');
const mathInfo = document.getElementById('math-info');
const selectionInfo = document.getElementById('selection-info');

let bgC = boardBgC, drawC = boardDrawC, overlayC = boardOverlayC, selC = boardSelC;
let bgCtx = bgC.getContext('2d');
let ctx = drawC.getContext('2d');
let overlayCtx = overlayC.getContext('2d');
let selCtx = selC.getContext('2d');

// Undo/redo stacks și selecții — devin "pointeri" comutabili per suprafață
// (tablă normală / fereastră PDF sus / fereastră PDF jos)
let boardUndoStack = [];
let boardRedoStack = [];

let DPR = window.devicePixelRatio || 1;
let tool = 'pen', color = '#ffffff';
let lastPenSize = 3, lastEraserSize = 25;

let drawing = false;
let currentStroke = [];

let multiSelectMode = false;
let mathStartPoint = null;
let mathEndPoint = null;
let isMathDrawing = false;
let compassPhase = 0;
let compassCenter = null;
let compassRadiusPoint = null;
let isCompassRadiusPreview = false;
let protractorPhase = 0;

let bgColor = '#000000';

// ================================================================
// VARIABILE PENTRU SELECTARE ȘI MUTARE
// ================================================================
let selectedStrokes = new Set();
let isSelecting = false;
let selectionStartX = 0, selectionStartY = 0;
let lassoPoints = [];
let lassoAdditive = false;
let lassoBaseSelection = new Set();
let isDraggingSelected = false;
let isResizingStroke = false;
let resizeStrokeIndex = -1;
let resizeOriginalStroke = null;
let resizeAnchor = { x: 0, y: 0 };
let resizeStartDist = 1;
let currentResizeHandle = null; // { x, y, strokeIdx }
let dragStartMouseX = 0, dragStartMouseY = 0;
let dragStartPositions = new Map();
let moveUndoSnapshots = new Map();

// ================================================================
// STRUCTURA PAGINILOR
// ================================================================
let pages = [{ 
  strokes: [], 
  images: []
}];
let currentPageIdx = 0;
let imageIdCounter = 0;

let undoStack = boardUndoStack;
let redoStack = boardRedoStack;

// ================================================================
// FIȘĂ PDF - STARE FERESTRE (SUS / JOS)
// ================================================================
let pdfModeActive = false;   // true când e afișat modul "Fișă PDF" (2 ferestre)
let activeSurface = 'board'; // 'board' | 'top' | 'bottom'
let pdfDoc = null;           // documentul PDF încărcat (pdf.js), comun ambelor ferestre
let pdfTotalPages = 0;

function makePdfPane() {
  return {
    strokes: [], images: [],
    undoStack: [], redoStack: [],
    pageNum: 1, zoom: 1, panX: 0, panY: 0,
    canvasW: 0, canvasH: 0
  };
}
let pdfPanes = { top: makePdfPane() };

// ================================================================
// FUNCȚII PENTRU IMAGINI
// ================================================================

function getCurrentPage() {
  if (pdfModeActive && activeSurface === 'top') {
    return pdfPanes[activeSurface];
  }
  return pages[currentPageIdx];
}

// ================================================================
// FIȘĂ PDF - MOTOR FERESTRE DUALE (sus / jos)
// ================================================================

function getPaneEls(name) {
  const root = document.getElementById('pdf-pane-' + name);
  return {
    root,
    bg: root.querySelector('.pdf-pane-bg'),
    draw: root.querySelector('.pdf-pane-draw'),
    overlay: root.querySelector('.pdf-pane-overlay'),
    select: root.querySelector('.pdf-pane-select'),
    pagenum: root.querySelector('.pdf-pane-pagenum')
  };
}

// Repointează suprafața activă de desen ('board' | 'top' | 'bottom').
// Toate funcțiile de desen (pointerdown/move/up, drawStrokeOn, redrawStrokes,
// undo/redo, selecție) folosesc variabilele globale de mai jos, deci
// schimbarea acestor referințe redirecționează automat TOATE uneltele
// existente către noua suprafață, fără nicio altă modificare.
function activatePane(name) {
  if (activeSurface !== name) {
    selectedStrokes.clear();
    selectedImages.clear();
    updateImageSelection();
    hideSelectionInfo();
  }
  activeSurface = name;

  document.querySelectorAll('.pdf-pane').forEach(p => p.classList.remove('active-pane'));

  if (name === 'board') {
    bgC = boardBgC; drawC = boardDrawC; overlayC = boardOverlayC; selC = boardSelC;
    bgCtx = bgC.getContext('2d');
    ctx = drawC.getContext('2d', { willReadFrequently: true });
    overlayCtx = overlayC.getContext('2d');
    selCtx = selC.getContext('2d');
    undoStack = boardUndoStack; redoStack = boardRedoStack;
  } else {
    const els = getPaneEls(name);
    els.root.classList.add('active-pane');
    bgC = els.bg; drawC = els.draw; overlayC = els.overlay; selC = els.select;
    bgCtx = bgC.getContext('2d');
    ctx = drawC.getContext('2d', { willReadFrequently: true });
    overlayCtx = overlayC.getContext('2d');
    selCtx = selC.getContext('2d');
    undoStack = pdfPanes[name].undoStack; redoStack = pdfPanes[name].redoStack;
  }
  const container = (name === 'board') ? wrap : getPaneEls(name).root;
  if (mathInfo.parentElement !== container) container.appendChild(mathInfo);
  if (selectionInfo.parentElement !== container) container.appendChild(selectionInfo);

  redrawStrokes();
  updateStatus();
  renderImages();
}

// Dimensionează canvas-urile de desen/overlay/selecție ale unei ferestre PDF
// la mărimea containerului (independente de pan/zoom-ul fișei PDF de dedesubt).
function initPaneDrawCanvas(name) {
  const els = getPaneEls(name);
  const rect = els.root.getBoundingClientRect();
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  [els.draw, els.overlay, els.select].forEach(c => {
    c.width = Math.max(1, Math.round(rect.width * dpr));
    c.height = Math.max(1, Math.round(rect.height * dpr));
    c.style.width = rect.width + 'px';
    c.style.height = rect.height + 'px';
  });
  if (activeSurface === name) {
    ctx = els.draw.getContext('2d', { willReadFrequently: true });
    overlayCtx = els.overlay.getContext('2d');
    selCtx = els.select.getContext('2d');
    ctx.resetTransform(); ctx.scale(dpr, dpr);
    overlayCtx.resetTransform(); overlayCtx.scale(dpr, dpr);
    selCtx.resetTransform(); selCtx.scale(dpr, dpr);
    redrawStrokes();
    drawSelectionHighlights();
  }
}

function renderPdfPane(name) {
  if (!pdfDoc) return;
  const pane = pdfPanes[name];
  const els = getPaneEls(name);
  pdfDoc.getPage(pane.pageNum).then(function(page) {
    const viewport = page.getViewport({ scale: 1.0 });
    const rect = els.root.getBoundingClientRect();
    const padding = 10;
    const maxW = Math.max(50, rect.width - padding * 2);
    const maxH = Math.max(50, rect.height - padding * 2);
    // La zoom 1, fișa umple întreaga lățime a ferestrei (poate depăși
    // vertical - de-asta există pan sus/jos, ca să vezi câte un exercițiu).
    const baseScale = Math.min(maxW / viewport.width, 4.0);
    const finalScale = Math.max(0.1, baseScale * pane.zoom);
    const scaledViewport = page.getViewport({ scale: finalScale });
    els.bg.width = Math.round(scaledViewport.width);
    els.bg.height = Math.round(scaledViewport.height);
    els.bg.style.width = scaledViewport.width + 'px';
    els.bg.style.height = scaledViewport.height + 'px';
    // Centrare automată pe orizontală (și pe verticală, dacă încape) -
    // pan-ul utilizatorului (panX/panY) se adaugă peste această poziție centrată,
    // așa că zoom-ul crește uniform, din centru, nu din colțul stânga-sus.
    const centerX = (rect.width - scaledViewport.width) / 2;
    const centerY = Math.max(0, (rect.height - scaledViewport.height) / 2);
    els.bg.style.transform = 'translate(' + (centerX + pane.panX) + 'px, ' + (centerY + pane.panY) + 'px)';
    page.render({ canvasContext: els.bg.getContext('2d'), viewport: scaledViewport }).promise.then(function() {
      els.root.classList.add('has-doc');
      els.pagenum.textContent = pane.pageNum + '/' + pdfTotalPages;
    }).catch(function(e) { console.error(e); });
  }).catch(function(e) { console.error(e); });
}

function setBoardMode(isPdf) {
  pdfModeActive = isPdf;
  document.getElementById('pdf-pane-top').style.display = isPdf ? '' : 'none';
  document.getElementById('pdf-pane-divider').style.display = isPdf ? '' : 'none';
  if (isPdf) {
    // Tabla de jos devine o tablă neagră, pe care rămân disponibile
    // toate uneltele, inclusiv rigla/echerul/raportorul/compasul.
    setBackgroundColor('#000000', 'bg-black');

    initPaneDrawCanvas('top');
    renderPdfPane('top');
  }
  activatePane('board');
  initCanvas();
  document.getElementById('btn-toggle-pdf-mode').classList.toggle('active', isPdf);
}

// ===== Încărcare fișă PDF =====
const pdfFileInput = document.getElementById('pdf-file-input');
document.getElementById('btn-load-pdf').addEventListener('click', () => pdfFileInput.click());
pdfFileInput.addEventListener('change', function(e) {
  const file = e.target.files[0];
  pdfFileInput.value = '';
  if (!file) return;
  const reader = new FileReader();
  reader.onload = function(ev) {
    pdfjsLib.getDocument({ data: ev.target.result }).promise.then(function(doc) {
      pdfDoc = doc;
      pdfTotalPages = doc.numPages;
      pdfPanes.top = makePdfPane();
      document.getElementById('btn-toggle-pdf-mode').disabled = false;
      showToast('✓ Fișă PDF încărcată (' + pdfTotalPages + ' pagini)');
      setBoardMode(true);
    }).catch(function(err) {
      alert('Eroare la încărcarea PDF: ' + err.message);
    });
  };
  reader.readAsArrayBuffer(file);
});

document.getElementById('btn-toggle-pdf-mode').addEventListener('click', () => {
  if (!pdfDoc) return;
  setBoardMode(!pdfModeActive);
});

// ===== Evenimente de desen pe fereastra PDF (sus) =====
(function() {
  const name = 'top';
  const els = getPaneEls(name);
  els.draw.addEventListener('pointerdown', function(e) { activatePane(name); handlePointerDown(e); });
  els.draw.addEventListener('pointermove', handlePointerMove);
  els.draw.addEventListener('pointerup', handlePointerUp);
  els.draw.addEventListener('pointercancel', handlePointerUp);
  els.draw.addEventListener('pointerleave', handlePointerLeave);
  els.draw.addEventListener('dblclick', function(e) { activatePane(name); handleDblClick(e); });
})();

// ===== Controale fereastră PDF: pan / zoom / pagină =====
function panePanStep(name) {
  const els = getPaneEls(name);
  return Math.max(20, Math.min(els.root.clientWidth, els.root.clientHeight) * 0.12);
}

document.querySelectorAll('.pdf-pane-controls .pdf-ctl').forEach(function(btn) {
  btn.addEventListener('click', function() {
    const paneRoot = btn.closest('.pdf-pane');
    const name = paneRoot.dataset.pane;
    activatePane(name);
    const pane = pdfPanes[name];
    const act = btn.dataset.act;
    const step = panePanStep(name);
    if (act === 'up') pane.panY -= step;
    else if (act === 'down') pane.panY += step;
    else if (act === 'left') pane.panX -= step;
    else if (act === 'right') pane.panX += step;
    else if (act === 'zoomin') pane.zoom = Math.min(10, pane.zoom + 0.25);
    else if (act === 'zoomout') pane.zoom = Math.max(0.2, pane.zoom - 0.25);
    else if (act === 'center') { pane.panX = 0; pane.panY = 0; }
    else if (act === 'reset') { pane.panX = 0; pane.panY = 0; pane.zoom = 1; }
    else if (act === 'pageprev') { if (pane.pageNum > 1) pane.pageNum--; }
    else if (act === 'pagenext') { if (pane.pageNum < pdfTotalPages) pane.pageNum++; }
    renderPdfPane(name);
  });
});

// Panare cu degetul direct pe fișă (2 degete) și zoom cu pinch
function attachPanePanZoom(name) {
  const els = getPaneEls(name);
  const root = els.root;
  let pts = new Map();
  let lastDist = null, lastMid = null;

  root.addEventListener('pointerdown', function(e) {
    if (e.pointerType !== 'touch') return;
    pts.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (pts.size === 2) {
      activatePane(name);
      lastDist = null; lastMid = null;
      // Anulează orice linie începută cu primul deget, ca gestul cu 2 degete
      // (pan/zoom pe fișă) să nu lase o urmă nedorită pe desen.
      if (drawing) {
        drawing = false;
        currentStroke = [];
        overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
        redrawStrokes();
      }
    }
  }, { passive: true });

  root.addEventListener('pointermove', function(e) {
    if (!pts.has(e.pointerId)) return;
    pts.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (pts.size === 2) {
      const [a, b] = Array.from(pts.values());
      const dist = Math.hypot(a.x - b.x, a.y - b.y);
      const mid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
      const pane = pdfPanes[name];
      if (lastDist != null) {
        const scaleDelta = dist / lastDist;
        pane.zoom = Math.max(0.2, Math.min(10, pane.zoom * scaleDelta));
        pane.panX += (mid.x - lastMid.x);
        pane.panY += (mid.y - lastMid.y);
        renderPdfPane(name);
      }
      lastDist = dist; lastMid = mid;
    }
  }, { passive: true });

  function clearPt(e) { pts.delete(e.pointerId); if (pts.size < 2) { lastDist = null; lastMid = null; } }
  root.addEventListener('pointerup', clearPt, { passive: true });
  root.addEventListener('pointercancel', clearPt, { passive: true });
  root.addEventListener('pointerleave', clearPt, { passive: true });
}
attachPanePanZoom('top');

// ===== Divizor redimensionabil între fereastra PDF și tabla neagră =====
(function setupPaneDivider() {
  const divider = document.getElementById('pdf-pane-divider');
  const topPane = document.getElementById('pdf-pane-top');
  const container = document.getElementById('workspace');
  let dragging = false;
  let rafPending = false;

  function applyResize() {
    rafPending = false;
    initPaneDrawCanvas('top');
    renderPdfPane('top');
    initCanvas();
  }

  divider.addEventListener('pointerdown', function(e) {
    dragging = true;
    divider.setPointerCapture(e.pointerId);
  });
  divider.addEventListener('pointermove', function(e) {
    if (!dragging) return;
    const rect = container.getBoundingClientRect();
    const dividerH = divider.getBoundingClientRect().height;
    let topH = e.clientY - rect.top;
    const minH = 80;
    topH = Math.max(minH, Math.min(rect.height - dividerH - minH, topH));
    topPane.style.flex = '0 0 ' + topH + 'px';
    // Redimensionează live canvas-urile (tabla neagră + fereastra PDF),
    // ca să nu rămână o bandă goală vizibilă în timp ce tragi bara.
    if (!rafPending) {
      rafPending = true;
      requestAnimationFrame(applyResize);
    }
  });
  function endDrag() {
    if (!dragging) return;
    dragging = false;
    initPaneDrawCanvas('top');
    renderPdfPane('top');
    initCanvas();
  }
  divider.addEventListener('pointerup', endDrag);
  divider.addEventListener('pointercancel', endDrag);
})();

window.addEventListener('resize', function() {
  if (pdfModeActive) {
    initPaneDrawCanvas('top');
    renderPdfPane('top');
    initCanvas();
  }
});

function addImageToPage(page, img, x, y, w, h) {
  const id = ++imageIdCounter;
  const imageData = {
    id,
    img,
    x: x || 40,
    y: y || 40,
    w: w || 200,
    h: h || 150,
    locked: false,
    dataUrl: null
  };
  try {
    const canvas = document.createElement('canvas');
    canvas.width = img.naturalWidth || img.width;
    canvas.height = img.naturalHeight || img.height;
    canvas.getContext('2d').drawImage(img, 0, 0);
    imageData.dataUrl = canvas.toDataURL('image/png');
  } catch(e) {}
  
  page.images.push(imageData);
  renderImages();
  updateStatus();
  return id;
}

function removeImageFromPage(page, imageId) {
  const idx = page.images.findIndex(img => img.id === imageId);
  if (idx !== -1) {
    page.images.splice(idx, 1);
    renderImages();
    updateStatus();
    return true;
  }
  return false;
}

function getImageAt(page, x, y) {
  for (let i = page.images.length - 1; i >= 0; i--) {
    const img = page.images[i];
    if (x >= img.x && x <= img.x + img.w && y >= img.y && y <= img.y + img.h) {
      return img;
    }
  }
  return null;
}

function renderImages() {
  imagesContainer.innerHTML = '';
  const page = getCurrentPage();
  if (!page) return;

  page.images.forEach(imgData => {
    const div = document.createElement('div');
    div.className = 'image-item' + (imgData.locked ? ' locked' : '');
    div.dataset.imageId = imgData.id;
    div.style.left = imgData.x + 'px';
    div.style.top = imgData.y + 'px';
    div.style.width = imgData.w + 'px';
    div.style.height = imgData.h + 'px';
    
    const img = document.createElement('img');
    img.src = imgData.img.src || imgData.dataUrl;
    img.draggable = false;
    div.appendChild(img);

    const lockBtn = document.createElement('div');
    lockBtn.className = 'img-lock-btn';
    lockBtn.textContent = imgData.locked ? '🔒' : '🔓';
    lockBtn.title = imgData.locked ? 'Deblochează imaginea' : 'Blochează imaginea (previne mutare/redimensionare/ștergere)';
    lockBtn.addEventListener('click', (e) => {
      e.stopPropagation();
      imgData.locked = !imgData.locked;
      renderImages();
      showToast(imgData.locked ? '🔒 Imagine blocată' : '🔓 Imagine deblocată');
    });
    div.appendChild(lockBtn);
    
    const delBtn = document.createElement('div');
    delBtn.className = 'img-delete-btn';
    delBtn.textContent = '×';
    delBtn.title = 'Șterge imaginea';
    delBtn.addEventListener('click', async (e) => {
      e.stopPropagation();
      if (imgData.locked) { showToast('🔒 Imaginea e blocată — deblocheaz-o întâi'); return; }
      if (await customConfirm('Ștergi această imagine?')) {
        const idx = page.images.findIndex(img => img.id === imgData.id);
        if (idx !== -1) {
          undoStack.push({ type: 'imageDelete', page, items: [{ index: idx, img: page.images[idx] }] });
          redoStack = [];
        }
        removeImageFromPage(page, imgData.id);
        if (selectedImages.has(imgData.id)) {
          selectedImages.delete(imgData.id);
          updateStatus();
        }
      }
    });
    div.appendChild(delBtn);
    
    const resizer = document.createElement('div');
    resizer.className = 'resizer';
    div.appendChild(resizer);
    
    imagesContainer.appendChild(div);
  });
  
  updateImageSelection();
}

// ================================================================
// SELECTARE IMAGINI
// ================================================================
let selectedImages = new Set();
let isImageDrag = false;
let imageDragStartX = 0, imageDragStartY = 0;
let isImageResize = false;
let resizeImageId = null;
let resizeStartX = 0, resizeStartY = 0;
let resizeOrigW = 0, resizeOrigH = 0;
let imageDragStartPositions = new Map();

function updateImageSelection() {
  document.querySelectorAll('.image-item').forEach(el => {
    const id = parseInt(el.dataset.imageId);
    el.classList.toggle('selected', selectedImages.has(id));
  });
}

function toggleImageSelection(id, shiftKey) {
  if (shiftKey) {
    if (selectedImages.has(id)) {
      selectedImages.delete(id);
    } else {
      selectedImages.add(id);
    }
  } else {
    if (selectedImages.size === 1 && selectedImages.has(id)) {
      selectedImages.clear();
    } else {
      selectedImages.clear();
      selectedImages.add(id);
    }
  }
  updateImageSelection();
  updateStatus();
  const count = selectedImages.size;
  if (count > 0) {
    showSelectionInfo(`🖼 ${count} imagine(images) selectată(e) (Delete pentru ștergere)`);
  } else {
    hideSelectionInfo();
  }
}

function reorderSelectedImages(direction) {
  if (selectedImages.size === 0) return;
  const page = getCurrentPage();
  if (!page) return;

  const ids = Array.from(selectedImages);
  const beforeOrder = page.images.slice();

  if (direction === 'front') {
    const selected = page.images.filter(img => ids.includes(img.id));
    const rest = page.images.filter(img => !ids.includes(img.id));
    page.images = rest.concat(selected);
  } else if (direction === 'back') {
    const selected = page.images.filter(img => ids.includes(img.id));
    const rest = page.images.filter(img => !ids.includes(img.id));
    page.images = selected.concat(rest);
  } else if (direction === 'forward') {
    for (let i = page.images.length - 2; i >= 0; i--) {
      if (ids.includes(page.images[i].id) && !ids.includes(page.images[i + 1].id)) {
        [page.images[i], page.images[i + 1]] = [page.images[i + 1], page.images[i]];
      }
    }
  } else if (direction === 'backward') {
    for (let i = 1; i < page.images.length; i++) {
      if (ids.includes(page.images[i].id) && !ids.includes(page.images[i - 1].id)) {
        [page.images[i], page.images[i - 1]] = [page.images[i - 1], page.images[i]];
      }
    }
  }

  const afterOrder = page.images.slice();
  undoStack.push({ type: 'imageReorder', page, beforeOrder, afterOrder });
  redoStack = [];

  renderImages();
  const labels = { front: '⬆ Adusă în față', back: '⬇ Trimisă în spate', forward: '↑ Un nivel mai sus', backward: '↓ Un nivel mai jos' };
  showToast(labels[direction] || 'Ordine actualizată');
}

function deleteSelectedImages() {
  if (selectedImages.size === 0) return;
  const page = getCurrentPage();
  if (!page) return;
  
  const ids = Array.from(selectedImages);
  const lockedCount = ids.filter(id => {
    const img = page.images.find(i => i.id === id);
    return img && img.locked;
  }).length;
  const deletableIds = ids.filter(id => {
    const img = page.images.find(i => i.id === id);
    return img && !img.locked;
  });
  
  const removedItems = [];
  for (const id of deletableIds) {
    const idx = page.images.findIndex(img => img.id === id);
    if (idx !== -1) {
      removedItems.push({ index: idx, img: page.images[idx] });
      page.images.splice(idx, 1);
    }
  }
  removedItems.sort((a, b) => a.index - b.index);
  if (removedItems.length > 0) {
    undoStack.push({ type: 'imageDelete', page, items: removedItems });
    redoStack = [];
  }
  renderImages();
  selectedImages.clear();
  updateStatus();
  hideSelectionInfo();
  if (lockedCount > 0) {
    showToast(`✓ ${deletableIds.length} imagini șterse (${lockedCount} blocate au fost păstrate)`);
  } else {
    showToast(`✓ ${deletableIds.length} imagini șterse`);
  }
}

// ================================================================
// EVENIMENTE PENTRU IMAGINI
// ================================================================

imagesContainer.addEventListener('pointerdown', (e) => {
  if (tool !== 'select') return;
  
  const target = e.target.closest('.image-item');
  if (!target) return;
  
  const imageId = parseInt(target.dataset.imageId);
  const page = getCurrentPage();
  const imgData = page.images.find(img => img.id === imageId);
  if (!imgData) return;
  
  if (e.target.closest('.img-delete-btn')) return;
  if (e.target.closest('.img-lock-btn')) return;
  
  if (e.target.closest('.resizer')) {
    if (imgData.locked) { showToast('🔒 Imaginea e blocată — deblocheaz-o întâi'); return; }
    isImageResize = true;
    resizeImageId = imageId;
    resizeStartX = e.clientX;
    resizeStartY = e.clientY;
    resizeOrigW = imgData.w;
    resizeOrigH = imgData.h;
    e.preventDefault();
    return;
  }
  
  const shiftKey = e.shiftKey || e.metaKey || multiSelectMode;
  const alreadySelectedNoShift = !shiftKey && selectedImages.has(imageId);
  if (!alreadySelectedNoShift) {
    toggleImageSelection(imageId, shiftKey);
  }
  
  if (selectedImages.size > 0) {
    isImageDrag = true;
    imageDragStartX = e.clientX;
    imageDragStartY = e.clientY;
    imageDragStartPositions.clear();
    for (const id of selectedImages) {
      const img = page.images.find(i => i.id === id);
      if (img && !img.locked) {
        imageDragStartPositions.set(id, { x: img.x, y: img.y });
      }
    }
    imagesContainer.setPointerCapture(e.pointerId);
  }
});

document.addEventListener('pointermove', (e) => {
  if (isImageResize && resizeImageId !== null) {
    const page = getCurrentPage();
    const imgData = page.images.find(img => img.id === resizeImageId);
    if (!imgData) return;
    
    const dx = (e.clientX - resizeStartX);
    const dy = (e.clientY - resizeStartY);
    const aspect = resizeOrigW / resizeOrigH;
    const delta = Math.abs(dx) > Math.abs(dy) ? dx : dy;
    let newW = Math.max(40, resizeOrigW + delta);
    let newH = newW / aspect;
    imgData.w = newW;
    imgData.h = newH;
    renderImages();
    return;
  }
  
  if (isImageDrag && selectedImages.size > 0) {
    const dx = e.clientX - imageDragStartX;
    const dy = e.clientY - imageDragStartY;
    const page = getCurrentPage();
    
    for (const id of selectedImages) {
      const imgData = page.images.find(img => img.id === id);
      if (imgData) {
        const start = imageDragStartPositions.get(id);
        if (start) {
          imgData.x = start.x + dx;
          imgData.y = start.y + dy;
        }
      }
    }
    renderImages();
    return;
  }
});

document.addEventListener('pointerup', () => {
  if (isImageResize) {
    isImageResize = false;
    if (resizeImageId !== null) {
      const page = getCurrentPage();
      const imgData = page && page.images.find(img => img.id === resizeImageId);
      if (imgData && (imgData.w !== resizeOrigW || imgData.h !== resizeOrigH)) {
        undoStack.push({
          type: 'imageResize',
          page,
          item: { img: imgData, before: { w: resizeOrigW, h: resizeOrigH }, after: { w: imgData.w, h: imgData.h } }
        });
        redoStack = [];
      }
    }
    resizeImageId = null;
  }
  if (isImageDrag) {
    isImageDrag = false;
    const page = getCurrentPage();
    if (page) {
      const items = [];
      for (const [id, before] of imageDragStartPositions) {
        const imgData = page.images.find(img => img.id === id);
        if (imgData && (imgData.x !== before.x || imgData.y !== before.y)) {
          items.push({ img: imgData, before, after: { x: imgData.x, y: imgData.y } });
        }
      }
      if (items.length > 0) {
        undoStack.push({ type: 'imageMove', page, items });
        redoStack = [];
      }
    }
    imageDragStartPositions.clear();
  }
});

// ================================================================
// FUNCȚII DE BAZĂ
// ================================================================

function pushStroke(page, stroke) {
  page.strokes.push(stroke);
  undoStack.push({ type: 'draw', page, stroke });
  redoStack = [];
}

let toastTimer = null;
function showToast(msg, duration = 3000) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), duration);
}

function initCanvas() {
  DPR = window.devicePixelRatio || 1;
  const w = wrap.clientWidth, h = wrap.clientHeight;
  [bgC, drawC, overlayC, selC].forEach(c => {
    c.width = w * DPR; c.height = h * DPR;
    c.style.width = w + 'px'; c.style.height = h + 'px';
  });
  [bgCtx, ctx, overlayCtx, selCtx].forEach(cx => { cx.resetTransform(); cx.scale(DPR, DPR); });
  drawBg(); 
  redrawStrokes(); 
  updateStatus(); 
  drawSelectionHighlights();
  renderImages();
}

function drawBg() {
  bgCtx.clearRect(0, 0, bgC.width, bgC.height);
  bgCtx.fillStyle = bgColor;
  bgCtx.fillRect(0, 0, bgC.width, bgC.height);
}

function drawStrokeOn(c, stroke) {
  if (!stroke) return;

  if (stroke.type === 'solid3d') {
    c.save();
    const baseWidth = stroke.size || 2.4;
    c.lineJoin = 'round';
    c.lineCap = 'round';

    // muchii ascunse (plan secundar) — mai subțiri, mai deschise la culoare, punctate clar
    c.globalAlpha = 0.55;
    c.strokeStyle = stroke.color;
    c.lineWidth = Math.max(1, baseWidth * 0.75);
    c.setLineDash([baseWidth * 3, baseWidth * 2.4]);
    (stroke.hidden || []).forEach(seg => {
      if (!seg || seg.length < 2) return;
      c.beginPath();
      c.moveTo(seg[0].x, seg[0].y);
      c.lineTo(seg[1].x, seg[1].y);
      c.stroke();
    });

    // muchii vizibile (plan principal) — pline, opace
    c.globalAlpha = 1;
    c.setLineDash([]);
    c.strokeStyle = stroke.color;
    c.lineWidth = baseWidth;
    (stroke.visible || []).forEach(seg => {
      if (!seg || seg.length < 2) return;
      c.beginPath();
      c.moveTo(seg[0].x, seg[0].y);
      c.lineTo(seg[1].x, seg[1].y);
      c.stroke();
    });
    c.restore();
    return;
  }
  if (stroke.type === 'function') {
    c.save();
    const axisColor = stroke.axisColor || '#7a7a7a';

    // axele Ox / Oy (linii pline)
    c.strokeStyle = axisColor;
    c.lineWidth = 1.4;
    if (stroke.xAxis && stroke.xAxis.length === 2) {
      c.beginPath();
      c.moveTo(stroke.xAxis[0].x, stroke.xAxis[0].y);
      c.lineTo(stroke.xAxis[1].x, stroke.xAxis[1].y);
      c.stroke();
    }
    if (stroke.yAxis && stroke.yAxis.length === 2) {
      c.beginPath();
      c.moveTo(stroke.yAxis[0].x, stroke.yAxis[0].y);
      c.lineTo(stroke.yAxis[1].x, stroke.yAxis[1].y);
      c.stroke();
    }

    // săgeți: Ox spre dreapta, Oy în sus
    function arrowHead(tipX, tipY, dirX, dirY) {
      const size = 9;
      const angle = Math.atan2(dirY, dirX);
      const a1 = angle + Math.PI - 0.42;
      const a2 = angle + Math.PI + 0.42;
      c.beginPath();
      c.moveTo(tipX, tipY);
      c.lineTo(tipX + size * Math.cos(a1), tipY + size * Math.sin(a1));
      c.lineTo(tipX + size * Math.cos(a2), tipY + size * Math.sin(a2));
      c.closePath();
      c.fillStyle = axisColor;
      c.fill();
    }
    if (stroke.xAxis && stroke.xAxis.length === 2) {
      arrowHead(stroke.xAxis[1].x, stroke.xAxis[1].y, 1, 0);
    }
    if (stroke.yAxis && stroke.yAxis.length === 2) {
      arrowHead(stroke.yAxis[1].x, stroke.yAxis[1].y, 0, -1);
    }

    // diviziuni (ticks) pe Ox și Oy
    c.strokeStyle = axisColor;
    c.lineWidth = 1;
    c.fillStyle = axisColor;
    c.font = '12px system-ui, sans-serif';
    (stroke.xTicks || []).forEach(t => {
      c.beginPath();
      c.moveTo(t.x, t.y - 4);
      c.lineTo(t.x, t.y + 4);
      c.stroke();
      c.textAlign = 'center';
      c.textBaseline = 'top';
      c.fillText(t.label, t.x, t.y + 6);
    });
    (stroke.yTicks || []).forEach(t => {
      c.beginPath();
      c.moveTo(t.x - 4, t.y);
      c.lineTo(t.x + 4, t.y);
      c.stroke();
      c.textAlign = 'right';
      c.textBaseline = 'middle';
      c.fillText(t.label, t.x - 7, t.y);
    });

    // valorile extreme (domeniu pe Ox, imaginea vizibilă pe Oy) — evidențiate
    c.font = 'bold 12px system-ui, sans-serif';
    c.fillStyle = stroke.color || axisColor;
    (stroke.extremes || []).forEach(ex => {
      c.beginPath();
      if (ex.axis === 'x') {
        c.moveTo(ex.x, ex.y - 5);
        c.lineTo(ex.x, ex.y + 5);
        c.stroke();
        c.textAlign = 'center';
        c.textBaseline = 'top';
        c.fillText(ex.label, ex.x, ex.y + 8);
      } else {
        c.moveTo(ex.x - 5, ex.y);
        c.lineTo(ex.x + 5, ex.y);
        c.stroke();
        c.textAlign = 'right';
        c.textBaseline = 'middle';
        c.fillText(ex.label, ex.x - 8, ex.y);
      }
    });

    // curba funcției
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 3;
    c.lineJoin = 'round';
    c.lineCap = 'round';
    (stroke.segments || []).forEach(seg => {
      if (!seg || seg.length < 2) return;
      c.beginPath();
      c.moveTo(seg[0].x, seg[0].y);
      for (let i = 1; i < seg.length; i++) c.lineTo(seg[i].x, seg[i].y);
      c.stroke();
    });
    c.restore();
    return;
  }
  if (stroke.type === 'text') {
    c.save();
    c.font = stroke.font;
    c.fillStyle = stroke.color;
    c.textAlign = stroke.textAlign || 'left';
    c.textBaseline = 'top';
    const lines = stroke.text.split('\n');
    const fs = stroke.fontSize || 28;
    const lineHeight = fs * 1.3;
    let maxWidth = 0;
    lines.forEach(line => {
      const w = c.measureText(line).width;
      if (w > maxWidth) maxWidth = w;
    });
    if (stroke.textAlign === 'center') {
      lines.forEach((line, i) => c.fillText(line, stroke.x + maxWidth/2, stroke.y + i * lineHeight));
    } else if (stroke.textAlign === 'right') {
      lines.forEach((line, i) => c.fillText(line, stroke.x + maxWidth, stroke.y + i * lineHeight));
    } else {
      lines.forEach((line, i) => c.fillText(line, stroke.x, stroke.y + i * lineHeight));
    }
    c.restore();
    return;
  }
  if (stroke.type === 'midpoint') {
    c.save();
    c.fillStyle = stroke.color || '#c0392b';
    c.strokeStyle = '#ffffff';
    c.lineWidth = 1;
    c.beginPath();
    c.arc(stroke.x, stroke.y, 4.5, 0, Math.PI * 2);
    c.fill();
    c.stroke();
    c.restore();
    return;
  }
  if (stroke.type === 'circle') {
    c.save();
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 2;
    c.beginPath();
    c.arc(stroke.cx, stroke.cy, stroke.radius, 0, Math.PI * 2);
    c.stroke();
    c.restore();
    return;
  }
  if (stroke.type === 'arc') {
    c.save();
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 2;
    c.beginPath();
    c.arc(stroke.cx, stroke.cy, stroke.radius, stroke.startAngle, stroke.endAngle);
    c.stroke();
    c.restore();
    return;
  }
  if (stroke.type === 'angle') {
    c.save();
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 1.5;
    c.beginPath();
    c.moveTo(stroke.vertex.x, stroke.vertex.y);
    c.lineTo(stroke.ray1.x, stroke.ray1.y);
    c.stroke();
    c.beginPath();
    c.moveTo(stroke.vertex.x, stroke.vertex.y);
    c.lineTo(stroke.ray2.x, stroke.ray2.y);
    c.stroke();
    const r = Math.min(30, Math.sqrt((stroke.ray1.x - stroke.vertex.x)**2 + (stroke.ray1.y - stroke.vertex.y)**2) / 2);
    let a1 = Math.atan2(stroke.ray1.y - stroke.vertex.y, stroke.ray1.x - stroke.vertex.x);
    let a2 = Math.atan2(stroke.ray2.y - stroke.vertex.y, stroke.ray2.x - stroke.vertex.x);
    let startA = a1, endA = a2;
    if (endA < startA) endA += 2 * Math.PI;
    let angleDiff = endA - startA;
    if (angleDiff > Math.PI) {
      let temp = startA;
      startA = endA;
      endA = temp + 2 * Math.PI;
      angleDiff = endA - startA;
    }
    c.beginPath();
    c.arc(stroke.vertex.x, stroke.vertex.y, r, startA, endA);
    c.stroke();
    const midA = (startA + endA) / 2;
    const labelR = r + 14;
    const deg = (angleDiff * 180 / Math.PI);
    c.font = '11px sans-serif';
    c.fillStyle = stroke.color;
    c.textAlign = 'center';
    c.textBaseline = 'bottom';
    c.fillText(deg.toFixed(0) + '°', stroke.vertex.x + labelR * Math.cos(midA), stroke.vertex.y + labelR * Math.sin(midA));
    c.restore();
    return;
  }
  if (stroke.ruler) {
    c.save();
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 2;
    c.lineCap = 'round';
    c.beginPath();
    c.moveTo(stroke.points[0].x, stroke.points[0].y);
    c.lineTo(stroke.points[1].x, stroke.points[1].y);
    c.stroke();
    c.restore();
    return;
  }
  if (stroke.type === 'arrow') {
    c.save();
    c.strokeStyle = stroke.color;
    c.fillStyle = stroke.color;
    c.lineWidth = stroke.size || 2;
    c.lineCap = 'round';
    const p1 = stroke.points[0];
    const p2 = stroke.points[1];
    const dx = p2.x - p1.x, dy = p2.y - p1.y;
    const len = Math.sqrt(dx*dx + dy*dy);
    if (len < 5) { c.restore(); return; }
    const angle = Math.atan2(dy, dx);
    const headLen = Math.min(20, len * 0.4);
    const headAngle = 0.45;
    c.beginPath();
    c.moveTo(p1.x, p1.y);
    c.lineTo(p2.x, p2.y);
    c.stroke();
    c.beginPath();
    c.moveTo(p2.x, p2.y);
    c.lineTo(p2.x - headLen * Math.cos(angle - headAngle), p2.y - headLen * Math.sin(angle - headAngle));
    c.lineTo(p2.x - headLen * Math.cos(angle + headAngle), p2.y - headLen * Math.sin(angle + headAngle));
    c.closePath();
    c.fill();
    c.restore();
    return;
  }
  if (stroke.type === 'rect') {
    c.save();
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 2;
    c.strokeRect(stroke.x, stroke.y, stroke.w, stroke.h);
    c.restore();
    return;
  }
  if (stroke.type === 'polygon') {
    c.save();
    c.strokeStyle = stroke.color;
    c.lineWidth = stroke.size || 2;
    c.lineJoin = 'round';
    c.beginPath();
    if (stroke.points && stroke.points.length > 0) {
      c.moveTo(stroke.points[0].x, stroke.points[0].y);
      for (let i = 1; i < stroke.points.length; i++) {
        c.lineTo(stroke.points[i].x, stroke.points[i].y);
      }
      if (stroke.closed) {
        c.closePath();
      }
      c.stroke();
    }
    c.restore();
    return;
  }
  if (!stroke.points?.length) return;
  c.save();
  c.globalCompositeOperation = stroke.erase ? 'destination-out' : 'source-over';
  c.strokeStyle = stroke.erase ? 'rgba(0,0,0,1)' : stroke.color;
  c.lineWidth = stroke.size;
  c.lineCap = c.lineJoin = 'round';
  if (stroke.dashed) c.setLineDash([stroke.size*2.5, stroke.size*1.8]);
  c.beginPath();
  if (stroke.points.length === 1) {
    c.arc(stroke.points[0].x, stroke.points[0].y, stroke.size/2, 0, Math.PI*2);
    c.fillStyle = stroke.erase ? 'rgba(0,0,0,1)' : stroke.color;
    c.fill();
  } else {
    c.moveTo(stroke.points[0].x, stroke.points[0].y);
    for (let i = 1; i < stroke.points.length; i++) c.lineTo(stroke.points[i].x, stroke.points[i].y);
    c.stroke();
  }
  c.restore();
}

function redrawStrokes(limit) {
  ctx.clearRect(0, 0, drawC.width, drawC.height);
  const page = getCurrentPage();
  if (!page) return;
  const n = limit !== undefined ? limit : page.strokes.length;
  for (let i = 0; i < n; i++) drawStrokeOn(ctx, page.strokes[i]);
  drawSelectionHighlights();
}

function updateStatus() {
  const MAX_UNDO = 100;
  if (undoStack.length > MAX_UNDO) undoStack.splice(0, undoStack.length - MAX_UNDO);
  if (redoStack.length > MAX_UNDO) redoStack.splice(0, redoStack.length - MAX_UNDO);

  const page = getCurrentPage();
  const totalStrokes = page ? page.strokes.length : 0;
  const imageCount = page ? page.images.length : 0;

  const selCount = selectedStrokes.size + selectedImages.size;
  document.getElementById('status-strokes').textContent =
    `${totalStrokes} linii  ·  ${imageCount} imagini`;

  const selEl = document.getElementById('status-selection');
  if (selCount > 0) {
    selEl.style.display = 'inline';
    const imgSel = selectedImages.size;
    const strokeSel = selectedStrokes.size;
    let parts = [];
    if (strokeSel > 0) parts.push(`${strokeSel} stroke-uri`);
    if (imgSel > 0) parts.push(`${imgSel} imagini`);
    selEl.textContent = `● ${parts.join(' + ')} selectate (Delete pentru ștergere)`;
  } else {
    selEl.style.display = 'none';
  }

  document.getElementById('page-num').textContent = `${currentPageIdx + 1} / ${pages.length}`;
  document.getElementById('btn-prev-page').disabled = (currentPageIdx === 0);
}

const pos = e => {
  const r = drawC.getBoundingClientRect();
  return { x: e.clientX - r.left, y: e.clientY - r.top };
};

function snapPointToAngle(start, end) {
  const dx = end.x - start.x, dy = end.y - start.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const step = Math.PI / 12;
  let angle = Math.round(Math.atan2(dy, dx) / step) * step;
  return { x: start.x + dist * Math.cos(angle), y: start.y + dist * Math.sin(angle) };
}

function showMathInfo(text) {
  mathInfo.textContent = text;
  mathInfo.classList.add('show');
  clearTimeout(mathInfo._hideTimer);
  mathInfo._hideTimer = setTimeout(() => mathInfo.classList.remove('show'), 4000);
}

function pointInPolygon(x, y, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const xi = poly[i].x, yi = poly[i].y;
    const xj = poly[j].x, yj = poly[j].y;
    const intersect = ((yi > y) !== (yj > y)) &&
      (x < (xj - xi) * (y - yi) / (yj - yi) + xi);
    if (intersect) inside = !inside;
  }
  return inside;
}

function distToSegment(px, py, x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const lenSq = dx*dx + dy*dy;
  if (lenSq === 0) return Math.sqrt((px - x1)**2 + (py - y1)**2);
  let t = ((px - x1) * dx + (py - y1) * dy) / lenSq;
  t = Math.max(0, Math.min(1, t));
  const projX = x1 + t * dx;
  const projY = y1 + t * dy;
  return Math.sqrt((px - projX)**2 + (py - projY)**2);
}

// Calculează geometria unui stroke scalat cu 'factor' față de un punct ancoră (anchorX, anchorY).
// 'orig' este un clonă neschimbată a stroke-ului la începutul redimensionării, pentru a evita erori cumulate.
function computeScaledGeometry(orig, anchorX, anchorY, factor) {
  const sp = (px, py) => ({ x: anchorX + (px - anchorX) * factor, y: anchorY + (py - anchorY) * factor });
  const out = {};
  switch (orig.type) {
    case 'text': {
      const p = sp(orig.x, orig.y);
      out.x = p.x; out.y = p.y;
      out.fontSize = Math.max(6, (orig.fontSize || 28) * factor);
      out.font = (orig.font || '').replace(/[\d.]+px/, out.fontSize.toFixed(1) + 'px');
      break;
    }
    case 'midpoint': {
      const p = sp(orig.x, orig.y); out.x = p.x; out.y = p.y;
      out.p1 = sp(orig.p1.x, orig.p1.y);
      out.p2 = sp(orig.p2.x, orig.p2.y);
      break;
    }
    case 'circle':
    case 'arc': {
      const p = sp(orig.cx, orig.cy); out.cx = p.x; out.cy = p.y;
      out.radius = Math.max(2, orig.radius * factor);
      break;
    }
    case 'angle': {
      out.vertex = sp(orig.vertex.x, orig.vertex.y);
      out.ray1 = sp(orig.ray1.x, orig.ray1.y);
      out.ray2 = sp(orig.ray2.x, orig.ray2.y);
      break;
    }
    case 'rect': {
      const p = sp(orig.x, orig.y); out.x = p.x; out.y = p.y;
      out.w = orig.w * factor; out.h = orig.h * factor;
      break;
    }
    case 'function': {
      out.segments = (orig.segments || []).map(seg => seg.map(pt => sp(pt.x, pt.y)));
      out.xAxis = (orig.xAxis || []).map(pt => sp(pt.x, pt.y));
      out.yAxis = (orig.yAxis || []).map(pt => sp(pt.x, pt.y));
      out.xTicks = (orig.xTicks || []).map(t => ({ ...sp(t.x, t.y), label: t.label }));
      out.yTicks = (orig.yTicks || []).map(t => ({ ...sp(t.x, t.y), label: t.label }));
      out.extremes = (orig.extremes || []).map(t => ({ ...sp(t.x, t.y), label: t.label, axis: t.axis }));
      break;
    }
    case 'solid3d': {
      out.visible = (orig.visible || []).map(seg => seg.map(pt => sp(pt.x, pt.y)));
      out.hidden = (orig.hidden || []).map(seg => seg.map(pt => sp(pt.x, pt.y)));
      break;
    }
    default: {
      if (orig.points) out.points = orig.points.map(pt => sp(pt.x, pt.y));
    }
  }
  if (typeof orig.size === 'number') out.size = Math.max(0.5, orig.size * factor);
  return out;
}

function getStrokeBoundingBox(stroke) {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  
  if (stroke.type === 'midpoint') {
    return { x: stroke.x - 6, y: stroke.y - 6, w: 12, h: 12 };
  }
  if (stroke.type === 'text') {
    const fs = stroke.fontSize || 28;
    const lines = stroke.text ? stroke.text.split('\n') : [''];
    const maxW = Math.max(...lines.map(l => l.length * fs * 0.6));
    const h = lines.length * fs * 1.3;
    return { x: stroke.x, y: stroke.y, w: maxW, h: h };
  }
  if (stroke.type === 'rect') {
    return { x: stroke.x, y: stroke.y, w: stroke.w, h: stroke.h };
  }
  if (stroke.type === 'polygon' && stroke.points) {
    for (const p of stroke.points) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    return { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
  }
  if (stroke.type === 'circle') {
    const r = stroke.radius;
    return { x: stroke.cx - r, y: stroke.cy - r, w: r * 2, h: r * 2 };
  }
  if (stroke.type === 'arc') {
    const samples = [];
    const steps = 16;
    for (let i = 0; i <= steps; i++) {
      const a = stroke.startAngle + (stroke.endAngle - stroke.startAngle) * (i / steps);
      samples.push({ x: stroke.cx + stroke.radius * Math.cos(a), y: stroke.cy + stroke.radius * Math.sin(a) });
    }
    for (const p of samples) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    return { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
  }
  if (stroke.type === 'angle') {
    const pts = [stroke.vertex, stroke.ray1, stroke.ray2];
    for (const p of pts) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    return { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
  }
  if (stroke.points && stroke.points.length > 0) {
    for (const p of stroke.points) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    const pad = stroke.size || 5;
    return { x: minX - pad, y: minY - pad, w: maxX - minX + pad * 2, h: maxY - minY + pad * 2 };
  }
  if (stroke.type === 'solid3d') {
    const allPts = [];
    (stroke.visible || []).forEach(seg => allPts.push(...seg));
    (stroke.hidden || []).forEach(seg => allPts.push(...seg));
    for (const p of allPts) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    if (!isFinite(minX)) return { x: 0, y: 0, w: 10, h: 10 };
    const pad = stroke.size || 6;
    return { x: minX - pad, y: minY - pad, w: maxX - minX + pad * 2, h: maxY - minY + pad * 2 };
  }
  if (stroke.type === 'function') {
    if (stroke.xAxis) allPts.push(...stroke.xAxis);
    if (stroke.yAxis) allPts.push(...stroke.yAxis);
    (stroke.xTicks || []).forEach(t => allPts.push({ x: t.x, y: t.y }));
    (stroke.yTicks || []).forEach(t => allPts.push({ x: t.x, y: t.y }));
    (stroke.extremes || []).forEach(t => allPts.push({ x: t.x, y: t.y }));
    for (const p of allPts) {
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
      if (p.x > maxX) maxX = p.x;
      if (p.y > maxY) maxY = p.y;
    }
    if (!isFinite(minX)) return { x: 0, y: 0, w: 10, h: 10 };
    const pad = 34;
    return { x: minX - pad, y: minY - pad, w: maxX - minX + pad * 2, h: maxY - minY + pad * 2 };
  }
  return { x: 0, y: 0, w: 10, h: 10 };
}

function findSegmentStrokeAt(x, y, page) {
  let best = -1, bestDist = 14;
  for (let i = page.strokes.length - 1; i >= 0; i--) {
    const s = page.strokes[i];
    if (s.erase) continue;
    if (s.type && s.type !== 'arrow') continue;
    if (!s.points || s.points.length !== 2) continue;
    const d = distToSegment(x, y, s.points[0].x, s.points[0].y, s.points[1].x, s.points[1].y);
    if (d < bestDist) { bestDist = d; best = i; }
  }
  return best;
}

function findStrokeAt(x, y, page) {
  for (let i = page.strokes.length - 1; i >= 0; i--) {
    const s = page.strokes[i];
    if (s.type === 'midpoint') {
      if (Math.hypot(x - s.x, y - s.y) < 10) return i;
    } else if (s.type === 'text') {
      const fs = s.fontSize || 28;
      const lines = s.text ? s.text.split('\n') : [''];
      const maxW = Math.max(...lines.map(l => l.length * fs * 0.6));
      const h = lines.length * fs * 1.3;
      if (x >= s.x && x <= s.x + maxW && y >= s.y && y <= s.y + h) return i;
    } else if (s.type === 'rect') {
      if (x >= s.x && x <= s.x + s.w && y >= s.y && y <= s.y + s.h) return i;
    } else if (s.type === 'polygon' && s.points && s.points.length > 2) {
      if (pointInPolygon(x, y, s.points)) return i;
    } else if (s.type === 'circle') {
      const dist = Math.sqrt((x - s.cx)**2 + (y - s.cy)**2);
      if (Math.abs(dist - s.radius) < 15) return i;
    } else if (s.type === 'arc') {
      const dist = Math.sqrt((x - s.cx)**2 + (y - s.cy)**2);
      if (Math.abs(dist - s.radius) < 15) {
        let ang = Math.atan2(y - s.cy, x - s.cx);
        while (ang < s.startAngle) ang += 2 * Math.PI;
        if (ang <= s.endAngle) return i;
      }
    } else if (s.type === 'angle') {
      const d1 = distToSegment(x, y, s.vertex.x, s.vertex.y, s.ray1.x, s.ray1.y);
      const d2 = distToSegment(x, y, s.vertex.x, s.vertex.y, s.ray2.x, s.ray2.y);
      if (Math.min(d1, d2) < 12) return i;
    } else if (s.type === 'solid3d') {
      const allSegs = [...(s.visible || []), ...(s.hidden || [])];
      for (const seg of allSegs) {
        const d = distToSegment(x, y, seg[0].x, seg[0].y, seg[1].x, seg[1].y);
        if (d < 12) return i;
      }
    } else if (s.type === 'function') {
      for (const seg of (s.segments || [])) {
        for (let j = 0; j < seg.length - 1; j++) {
          const d = distToSegment(x, y, seg[j].x, seg[j].y, seg[j+1].x, seg[j+1].y);
          if (d < 12) return i;
        }
      }
    } else if (s.points && s.points.length > 0) {
      for (let j = 0; j < s.points.length - 1; j++) {
        const p1 = s.points[j], p2 = s.points[j+1];
        const d = distToSegment(x, y, p1.x, p1.y, p2.x, p2.y);
        if (d < 12) return i;
      }
    }
  }
  return -1;
}

function strokeIntersectsLasso(stroke, poly) {
  if (poly.length < 3) return false;
  if (stroke.points && stroke.points.length > 0) {
    for (const pt of stroke.points) {
      if (pointInPolygon(pt.x, pt.y, poly)) return true;
    }
    return false;
  }
  const bbox = getStrokeBoundingBox(stroke);
  const corners = [
    { x: bbox.x, y: bbox.y },
    { x: bbox.x + bbox.w, y: bbox.y },
    { x: bbox.x, y: bbox.y + bbox.h },
    { x: bbox.x + bbox.w, y: bbox.y + bbox.h },
    { x: bbox.x + bbox.w / 2, y: bbox.y + bbox.h / 2 }
  ];
  return corners.some(c => pointInPolygon(c.x, c.y, poly));
}

function drawSelectionHighlights() {
  selCtx.clearRect(0, 0, selC.width, selC.height);
  if (selectedStrokes.size === 0) return;
  
  const page = getCurrentPage();
  if (!page) return;
  
  selCtx.save();
  selCtx.strokeStyle = '#e67e00';
  selCtx.lineWidth = 2;
  selCtx.setLineDash([5, 4]);
  
  for (const idx of selectedStrokes) {
    const stroke = page.strokes[idx];
    if (!stroke) continue;
    const bbox = getStrokeBoundingBox(stroke);
    selCtx.strokeRect(bbox.x - 2, bbox.y - 2, bbox.w + 4, bbox.h + 4);
    selCtx.fillStyle = 'rgba(230, 126, 0, 0.15)';
    selCtx.fillRect(bbox.x - 2, bbox.y - 2, bbox.w + 4, bbox.h + 4);
  }
  
  selCtx.setLineDash([]);
  selCtx.restore();

  // Mâner de scalare — vizibil doar când e selectat un singur stroke
  currentResizeHandle = null;
  if (selectedStrokes.size === 1) {
    const idx = [...selectedStrokes][0];
    const stroke = page.strokes[idx];
    if (stroke) {
      const bbox = getStrokeBoundingBox(stroke);
      const hx = bbox.x + bbox.w + 2;
      const hy = bbox.y + bbox.h + 2;
      currentResizeHandle = { x: hx, y: hy, strokeIdx: idx };
      selCtx.save();
      selCtx.fillStyle = '#e67e00';
      selCtx.strokeStyle = '#ffffff';
      selCtx.lineWidth = 3;
      selCtx.beginPath();
      selCtx.arc(hx, hy, 13, 0, Math.PI * 2);
      selCtx.fill();
      selCtx.stroke();
      selCtx.restore();
    }
  }
}

function toggleSelection(idx, shiftKey) {
  const page = getCurrentPage();
  if (!page || idx < 0 || idx >= page.strokes.length) return;
  
  if (shiftKey) {
    if (selectedStrokes.has(idx)) {
      selectedStrokes.delete(idx);
    } else {
      selectedStrokes.add(idx);
    }
  } else {
    if (selectedStrokes.size === 1 && selectedStrokes.has(idx)) {
      selectedStrokes.clear();
    } else {
      selectedStrokes.clear();
      selectedStrokes.add(idx);
    }
  }
  
  updateStatus();
  drawSelectionHighlights();
    
  const count = selectedStrokes.size + selectedImages.size;
  if (count > 0) {
    let msg = '';
    if (selectedStrokes.size > 0) msg += `${selectedStrokes.size} stroke-uri`;
    if (selectedImages.size > 0) msg += (msg ? ' + ' : '') + `${selectedImages.size} imagini`;
    showSelectionInfo(`✓ ${msg} selectate (Delete pentru ștergere)`);
  } else {
    hideSelectionInfo();
  }
}

function showSelectionInfo(msg) {
  selectionInfo.textContent = msg;
  selectionInfo.classList.add('show');
  clearTimeout(selectionInfo._hideTimer);
}

function hideSelectionInfo() {
  selectionInfo.classList.remove('show');
}

function deleteSelectedStrokes() {
  if (selectedStrokes.size === 0) return;
  
  const page = getCurrentPage();
  if (!page) return;
  
  const sorted = Array.from(selectedStrokes).sort((a, b) => b - a);
  const removedItems = [];

  for (const idx of sorted) {
    removedItems.push({ index: idx, stroke: page.strokes[idx] });
    page.strokes.splice(idx, 1);
  }
  removedItems.sort((a, b) => a.index - b.index);

  undoStack.push({ type: 'delete', page, items: removedItems });
  redoStack = [];
  
  selectedStrokes.clear();
  hideSelectionInfo();
  redrawStrokes();
  updateStatus();
    showToast(`✓ ${sorted.length} stroke-uri șterse`);
}

function snapshotStrokePosition(stroke) {
  if (!stroke) return null;
  if (stroke.type === 'midpoint') return { x: stroke.x, y: stroke.y, p1: { ...stroke.p1 }, p2: { ...stroke.p2 } };
  if (stroke.type === 'text') return { x: stroke.x, y: stroke.y, textAlign: stroke.textAlign };
  if (stroke.type === 'rect') return { x: stroke.x, y: stroke.y, w: stroke.w, h: stroke.h };
  if (stroke.type === 'polygon') return { points: stroke.points.map(p => ({ x: p.x, y: p.y })) };
  if (stroke.type === 'circle' || stroke.type === 'arc') return { cx: stroke.cx, cy: stroke.cy };
  if (stroke.type === 'angle') return {
    vertex: { x: stroke.vertex.x, y: stroke.vertex.y },
    ray1: { x: stroke.ray1.x, y: stroke.ray1.y },
    ray2: { x: stroke.ray2.x, y: stroke.ray2.y }
  };
  if (stroke.points) return { points: stroke.points.map(p => ({ x: p.x, y: p.y })) };
  if (stroke.type === 'solid3d') {
    return {
      visible: (stroke.visible || []).map(seg => seg.map(p => ({ x: p.x, y: p.y }))),
      hidden: (stroke.hidden || []).map(seg => seg.map(p => ({ x: p.x, y: p.y })))
    };
  }
  if (stroke.type === 'function') {
    return {
      segments: (stroke.segments || []).map(seg => seg.map(p => ({ x: p.x, y: p.y }))),
      xAxis: (stroke.xAxis || []).map(p => ({ x: p.x, y: p.y })),
      yAxis: (stroke.yAxis || []).map(p => ({ x: p.x, y: p.y })),
      xTicks: (stroke.xTicks || []).map(t => ({ x: t.x, y: t.y, label: t.label })),
      yTicks: (stroke.yTicks || []).map(t => ({ x: t.x, y: t.y, label: t.label })),
      extremes: (stroke.extremes || []).map(t => ({ x: t.x, y: t.y, label: t.label, axis: t.axis }))
    };
  }
  return null;
}

function restoreStrokePosition(stroke, snap) {
  if (!stroke || !snap) return;
  if (stroke.type === 'midpoint') {
    stroke.x = snap.x; stroke.y = snap.y;
    if (snap.p1) stroke.p1 = { x: snap.p1.x, y: snap.p1.y };
    if (snap.p2) stroke.p2 = { x: snap.p2.x, y: snap.p2.y };
  } else if (stroke.type === 'text') {
    stroke.x = snap.x; stroke.y = snap.y;
    if (snap.textAlign) stroke.textAlign = snap.textAlign;
  } else if (stroke.type === 'rect') {
    stroke.x = snap.x; stroke.y = snap.y; stroke.w = snap.w; stroke.h = snap.h;
  } else if (stroke.type === 'polygon' && snap.points) {
    stroke.points = snap.points.map(p => ({ x: p.x, y: p.y }));
  } else if (stroke.type === 'circle' || stroke.type === 'arc') {
    stroke.cx = snap.cx; stroke.cy = snap.cy;
  } else if (stroke.type === 'angle' && snap.vertex) {
    stroke.vertex = { x: snap.vertex.x, y: snap.vertex.y };
    stroke.ray1 = { x: snap.ray1.x, y: snap.ray1.y };
    stroke.ray2 = { x: snap.ray2.x, y: snap.ray2.y };
  } else if (stroke.type === 'solid3d' && snap.visible) {
    stroke.visible = snap.visible.map(seg => seg.map(p => ({ x: p.x, y: p.y })));
    stroke.hidden = (snap.hidden || []).map(seg => seg.map(p => ({ x: p.x, y: p.y })));
  } else if (stroke.type === 'function' && snap.segments) {
    stroke.segments = snap.segments.map(seg => seg.map(p => ({ x: p.x, y: p.y })));
    stroke.xAxis = (snap.xAxis || []).map(p => ({ x: p.x, y: p.y }));
    stroke.yAxis = (snap.yAxis || []).map(p => ({ x: p.x, y: p.y }));
    stroke.xTicks = (snap.xTicks || []).map(t => ({ x: t.x, y: t.y, label: t.label }));
    stroke.yTicks = (snap.yTicks || []).map(t => ({ x: t.x, y: t.y, label: t.label }));
    stroke.extremes = (snap.extremes || []).map(t => ({ x: t.x, y: t.y, label: t.label, axis: t.axis }));
  } else if (stroke.points && snap.points) {
    stroke.points = snap.points.map(p => ({ x: p.x, y: p.y }));
  }
}

function samePosition(a, b) {
  if (!a || !b) return a === b;
  return JSON.stringify(a) === JSON.stringify(b);
}

// ================================================================
// FINALIZARE POLIGON
// ================================================================

function finalizePolygon() {
  if (!(tool === 'polygon' && drawing && currentStroke && currentStroke.length >= 3)) return false;
  const page = getCurrentPage();
  const stroke = {
    type: 'polygon',
    points: currentStroke.map(p => ({ x: p.x, y: p.y })),
    color: color,
    size: lastPenSize,
    closed: true
  };
  pushStroke(page, stroke);
  currentStroke = [];
  drawing = false;
  redrawStrokes();
  updateStatus();
  showToast(`✓ Poligon desenat (${stroke.points.length} laturi)`);
  return true;
}

function handlePointerDown(e) {

  if (tool === 'midpoint') {
    const p = pos(e);
    const page = getCurrentPage();
    const idx = findSegmentStrokeAt(p.x, p.y, page);
    if (idx >= 0) {
      const s = page.strokes[idx];
      const p1 = { x: s.points[0].x, y: s.points[0].y };
      const p2 = { x: s.points[s.points.length - 1].x, y: s.points[s.points.length - 1].y };
      const mid = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
      pushStroke(page, { type: 'midpoint', x: mid.x, y: mid.y, p1, p2, color: s.color || color, size: s.size || lastPenSize });
      redrawStrokes();
      updateStatus();
      showToast('✓ Mijlocul segmentului a fost adăugat');
    } else {
      showToast('⚠ Dă click chiar pe un segment (linie dreaptă)');
    }
    return;
  }
  
  if (tool === 'select') {
    const p = pos(e);
    const page = getCurrentPage();

    if (currentResizeHandle && selectedStrokes.has(currentResizeHandle.strokeIdx)) {
      const dhx = p.x - currentResizeHandle.x, dhy = p.y - currentResizeHandle.y;
      const hitRadius = e.pointerType === 'touch' ? 30 : 16;
      if (Math.sqrt(dhx * dhx + dhy * dhy) < hitRadius && page) {
        const stroke = page.strokes[currentResizeHandle.strokeIdx];
        if (stroke) {
          const bbox = getStrokeBoundingBox(stroke);
          isResizingStroke = true;
          resizeStrokeIndex = currentResizeHandle.strokeIdx;
          resizeOriginalStroke = JSON.parse(JSON.stringify(stroke));
          resizeAnchor = { x: bbox.x, y: bbox.y };
          const ddx = p.x - resizeAnchor.x, ddy = p.y - resizeAnchor.y;
          resizeStartDist = Math.max(1, Math.sqrt(ddx * ddx + ddy * ddy));
          drawC.setPointerCapture(e.pointerId);
          e.preventDefault();
          showToast('↔ Trage pentru a scala');
          return;
        }
      }
    }
    
    const imgAt = getImageAt(page, p.x, p.y);
    if (imgAt) {
      const shiftKey = e.shiftKey || e.metaKey || multiSelectMode;
      const alreadySelectedNoShift = !shiftKey && selectedImages.has(imgAt.id);
      if (!alreadySelectedNoShift) {
        toggleImageSelection(imgAt.id, shiftKey);
      }
      return;
    }
    
    const idx = findStrokeAt(p.x, p.y, page);
    
    if (idx >= 0) {
      const shiftKey = e.shiftKey || e.metaKey || multiSelectMode;
      const alreadySelectedNoShift = !shiftKey && selectedStrokes.has(idx);
      if (!alreadySelectedNoShift) {
        toggleSelection(idx, shiftKey);
      }
      
      if (selectedStrokes.size >= 1) {
        isDraggingSelected = true;
        dragStartMouseX = e.clientX;
        dragStartMouseY = e.clientY;
        dragStartPositions.clear();
        moveUndoSnapshots.clear();
        
        for (const si of selectedStrokes) {
          const s = page.strokes[si];
          moveUndoSnapshots.set(si, snapshotStrokePosition(s));
          if (s.type === 'polygon' && s.points && s.points.length > 0) {
            dragStartPositions.set(si, { points: s.points.map(pt => ({ x: pt.x, y: pt.y })) });
          } else if (s.type === 'midpoint') {
            dragStartPositions.set(si, { x: s.x, y: s.y, p1: { x: s.p1.x, y: s.p1.y }, p2: { x: s.p2.x, y: s.p2.y } });
          } else if (s.type === 'text') {
            dragStartPositions.set(si, { x: s.x, y: s.y });
          } else if (s.type === 'rect') {
            dragStartPositions.set(si, { x: s.x, y: s.y });
          } else if (s.type === 'circle' || s.type === 'arc') {
            dragStartPositions.set(si, { x: s.cx, y: s.cy });
          } else if (s.type === 'angle') {
            dragStartPositions.set(si, {
              x: s.vertex.x, y: s.vertex.y,
              ray1: { x: s.ray1.x, y: s.ray1.y },
              ray2: { x: s.ray2.x, y: s.ray2.y }
            });
          } else if (s.type === 'solid3d') {
            dragStartPositions.set(si, {
              visible: (s.visible || []).map(seg => seg.map(pt => ({ x: pt.x, y: pt.y }))),
              hidden: (s.hidden || []).map(seg => seg.map(pt => ({ x: pt.x, y: pt.y })))
            });
          } else if (s.type === 'function') {
            dragStartPositions.set(si, {
              segments: (s.segments || []).map(seg => seg.map(pt => ({ x: pt.x, y: pt.y }))),
              xAxis: (s.xAxis || []).map(pt => ({ x: pt.x, y: pt.y })),
              yAxis: (s.yAxis || []).map(pt => ({ x: pt.x, y: pt.y })),
              xTicks: (s.xTicks || []).map(t => ({ x: t.x, y: t.y, label: t.label })),
              yTicks: (s.yTicks || []).map(t => ({ x: t.x, y: t.y, label: t.label })),
              extremes: (s.extremes || []).map(t => ({ x: t.x, y: t.y, label: t.label, axis: t.axis }))
            });
          } else if (s.points && s.points.length > 0) {
            dragStartPositions.set(si, { points: s.points.map(pt => ({ x: pt.x, y: pt.y })) });
          }
        }
        drawC.setPointerCapture(e.pointerId);
        showToast(`📦 ${selectedStrokes.size} elemente selectate - trage pentru a muta`);
      }
    } else {
      isSelecting = true;
      selectionStartX = p.x;
      selectionStartY = p.y;
      lassoPoints = [{ x: p.x, y: p.y }];
      lassoAdditive = e.shiftKey || multiSelectMode;
      lassoBaseSelection = lassoAdditive ? new Set(selectedStrokes) : new Set();
      if (!lassoAdditive) {
        selectedStrokes.clear();
        selectedImages.clear();
        updateImageSelection();
        hideSelectionInfo();
              }
      updateStatus();
      drawSelectionHighlights();
      drawC.setPointerCapture(e.pointerId);
    }
    return;
  }
  
  if (tool === 'polygon') {
    const p = pos(e);
    if (!drawing) {
      drawing = true;
      currentStroke = [p];
      showToast(`🟨 Poligon: punctul 1 (${Math.round(p.x)}, ${Math.round(p.y)}) - click pentru următorul punct`);
      ctx.clearRect(0, 0, drawC.width, drawC.height);
      redrawStrokes();
      ctx.save();
      ctx.fillStyle = color;
      ctx.beginPath();
      ctx.arc(p.x, p.y, 4, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
      drawC.setPointerCapture(e.pointerId);
    } else {
      if (e.detail >= 2) {
        finalizePolygon();
        return;
      }
      const last = currentStroke[currentStroke.length - 1];
      if (Math.hypot(p.x - last.x, p.y - last.y) > 5) {
        currentStroke.push(p);
        showToast(`🟨 Poligon: punctul ${currentStroke.length} (${Math.round(p.x)}, ${Math.round(p.y)}) - dublu-click pentru finalizare`);
        ctx.clearRect(0, 0, drawC.width, drawC.height);
        redrawStrokes();
        ctx.save();
        ctx.strokeStyle = color;
        ctx.lineWidth = lastPenSize;
        ctx.lineJoin = 'round';
        ctx.beginPath();
        ctx.moveTo(currentStroke[0].x, currentStroke[0].y);
        for (let i = 1; i < currentStroke.length; i++) {
          ctx.lineTo(currentStroke[i].x, currentStroke[i].y);
        }
        ctx.stroke();
        ctx.fillStyle = color;
        currentStroke.forEach(pt => {
          ctx.beginPath();
          ctx.arc(pt.x, pt.y, 4, 0, Math.PI * 2);
          ctx.fill();
        });
        ctx.restore();
      }
    }
    return;
  }
  
  if (tool === 'rect') {
    drawing = true;
    currentStroke = [pos(e), pos(e)];
    drawC.setPointerCapture(e.pointerId);
    return;
  }
  
  
  if (tool === 'text') {
    const p = pos(e);
    const page = getCurrentPage();
    const idx = findStrokeAt(p.x, p.y, page);
    if (idx >= 0 && page.strokes[idx].type === 'text') {
      const s = page.strokes[idx];
      showTextOverlay(s.x, s.y, idx);
      showToast('✏️ Editare text - Enter pentru a salva');
    } else {
      showTextOverlay(p.x, p.y);
    }
    return;
  }
  
  if (tool === 'pen' || tool === 'line' || tool === 'dashed' || tool === 'arrow' || 
      tool === 'circle' || tool === 'erase') {
    drawing = true;
    const startP = pos(e);
    const isSnapTool = (tool === 'pen' || tool === 'line' || tool === 'dashed' || tool === 'arrow');
    lastSnapGuideName = null;
    currentStroke = [isSnapTool ? snapToGuides(startP) : startP];
        drawC.setPointerCapture(e.pointerId);
  }
}

function handlePointerMove(e) {
  
  const p = pos(e);
  
  if (tool === 'pen' && !geoActiveDrag) {
    const gd = nearestGuideDist(p);
    drawC.style.cursor = (gd < GUIDE_SNAP_DIST) ? GEO_PEN_CURSOR : '';
  }

  if (tool === 'select' && isResizingStroke) {
    const page = getCurrentPage();
    if (page && resizeOriginalStroke) {
      const stroke = page.strokes[resizeStrokeIndex];
      if (stroke) {
        const ddx = p.x - resizeAnchor.x, ddy = p.y - resizeAnchor.y;
        const dist = Math.sqrt(ddx * ddx + ddy * ddy);
        const factor = Math.min(20, Math.max(0.05, dist / resizeStartDist));
        Object.assign(stroke, computeScaledGeometry(resizeOriginalStroke, resizeAnchor.x, resizeAnchor.y, factor));
        redrawStrokes();
        drawSelectionHighlights();
      }
    }
    return;
  }
  
  if (tool === 'select' && isSelecting) {
    const page = getCurrentPage();
    lassoPoints.push({ x: p.x, y: p.y });

    selectedStrokes = new Set(lassoBaseSelection);
    if (page && lassoPoints.length >= 3) {
      page.strokes.forEach((s, i) => {
        if (strokeIntersectsLasso(s, lassoPoints)) selectedStrokes.add(i);
      });
    }
    
    if (page && lassoPoints.length >= 3) {
      page.images.forEach(img => {
        const corners = [
          { x: img.x, y: img.y },
          { x: img.x + img.w, y: img.y },
          { x: img.x, y: img.y + img.h },
          { x: img.x + img.w, y: img.y + img.h }
        ];
        if (corners.some(c => pointInPolygon(c.x, c.y, lassoPoints))) {
          selectedImages.add(img.id);
        } else if (!lassoAdditive) {
          selectedImages.delete(img.id);
        }
      });
    }
    
    drawSelectionHighlights();
    updateImageSelection();

    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    overlayCtx.save();
    overlayCtx.strokeStyle = '#0055cc';
    overlayCtx.fillStyle = 'rgba(0,85,204,0.08)';
    overlayCtx.lineWidth = 1.5;
    overlayCtx.lineJoin = 'round';
    overlayCtx.lineCap = 'round';
    overlayCtx.setLineDash([5, 4]);
    overlayCtx.beginPath();
    overlayCtx.moveTo(lassoPoints[0].x, lassoPoints[0].y);
    for (let i = 1; i < lassoPoints.length; i++) overlayCtx.lineTo(lassoPoints[i].x, lassoPoints[i].y);
    overlayCtx.closePath();
    overlayCtx.fill();
    overlayCtx.stroke();
    overlayCtx.restore();

    const count = selectedStrokes.size + selectedImages.size;
    showSelectionInfo(count > 0 ? `✓ ${count} elemente selectate (Delete pentru ștergere)` : '📦 Trage pentru a selecta (lasou)');
    return;
  }

  if (tool === 'select' && isDraggingSelected && selectedStrokes.size >= 1) {
    const page = getCurrentPage();
    const dx = (e.clientX - dragStartMouseX);
    const dy = (e.clientY - dragStartMouseY);
    
    ctx.clearRect(0, 0, drawC.width, drawC.height);
    redrawStrokes();
    
    for (const si of selectedStrokes) {
      const s = page.strokes[si];
      if (!s) continue;
      const start = dragStartPositions.get(si);
      if (!start) continue;
      
      if (s.type === 'polygon' && s.points) {
        for (let i = 0; i < s.points.length; i++) {
          const orig = start.points && start.points[i];
          if (!orig) continue;
          s.points[i].x = orig.x + dx;
          s.points[i].y = orig.y + dy;
        }
      } else if (s.type === 'midpoint') {
        s.x = start.x + dx;
        s.y = start.y + dy;
        if (start.p1) { s.p1 = { x: start.p1.x + dx, y: start.p1.y + dy }; }
        if (start.p2) { s.p2 = { x: start.p2.x + dx, y: start.p2.y + dy }; }
      } else if (s.type === 'text') {
        s.x = start.x + dx;
        s.y = start.y + dy;
      } else if (s.type === 'rect') {
        s.x = start.x + dx;
        s.y = start.y + dy;
      } else if (s.type === 'circle' || s.type === 'arc') {
        s.cx = start.x + dx;
        s.cy = start.y + dy;
      } else if (s.type === 'angle') {
        s.vertex.x = start.x + dx;
        s.vertex.y = start.y + dy;
        s.ray1.x = start.ray1.x + dx;
        s.ray1.y = start.ray1.y + dy;
        s.ray2.x = start.ray2.x + dx;
        s.ray2.y = start.ray2.y + dy;
      } else if (s.type === 'solid3d' && start.visible) {
        s.visible = start.visible.map(seg => seg.map(pt => ({ x: pt.x + dx, y: pt.y + dy })));
        s.hidden = (start.hidden || []).map(seg => seg.map(pt => ({ x: pt.x + dx, y: pt.y + dy })));
      } else if (s.type === 'function' && start.segments) {
        s.segments = start.segments.map(seg => seg.map(pt => ({ x: pt.x + dx, y: pt.y + dy })));
        s.xAxis = (start.xAxis || []).map(pt => ({ x: pt.x + dx, y: pt.y + dy }));
        s.yAxis = (start.yAxis || []).map(pt => ({ x: pt.x + dx, y: pt.y + dy }));
        s.xTicks = (start.xTicks || []).map(t => ({ x: t.x + dx, y: t.y + dy, label: t.label }));
        s.yTicks = (start.yTicks || []).map(t => ({ x: t.x + dx, y: t.y + dy, label: t.label }));
        s.extremes = (start.extremes || []).map(t => ({ x: t.x + dx, y: t.y + dy, label: t.label, axis: t.axis }));
      } else if (s.points) {
        for (let i = 0; i < s.points.length; i++) {
          const orig = start.points && start.points[i];
          if (!orig) continue;
          s.points[i].x = orig.x + dx;
          s.points[i].y = orig.y + dy;
        }
      }
    }
    redrawStrokes();
    return;
  }
  
  if (isMathDrawing) {
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    const size = lastPenSize;
    
    if (tool === 'ruler' && mathStartPoint) {
      let ex = p.x, ey = p.y;
      const snapping = e.shiftKey;
      if (snapping) {
        const angle = Math.atan2(p.y - mathStartPoint.y, p.x - mathStartPoint.x);
        const snapRad = 15 * Math.PI / 180;
        const snapped = Math.round(angle / snapRad) * snapRad;
        const len = Math.sqrt((p.x - mathStartPoint.x)**2 + (p.y - mathStartPoint.y)**2);
        ex = mathStartPoint.x + len * Math.cos(snapped);
        ey = mathStartPoint.y + len * Math.sin(snapped);
      }
      drawRuler(overlayCtx, mathStartPoint.x, mathStartPoint.y, ex, ey, color, size, snapping);
      const dist = Math.sqrt((ex - mathStartPoint.x)**2 + (ey - mathStartPoint.y)**2);
      const angle = Math.atan2(ey - mathStartPoint.y, ex - mathStartPoint.x);
      let trigDeg = -angle * 180 / Math.PI;
      trigDeg = ((trigDeg % 360) + 360) % 360;
      showMathInfo('📏 ' + (dist/50).toFixed(2) + ' cm  |  ' + trigDeg.toFixed(snapping?0:1) + '°' + (snapping ? '  (snap activ)' : '  |  Shift = snap unghi'));
    }
    return;
  }
  
  if (tool === 'protractor' && protractorPhase === 2 && mathStartPoint && mathEndPoint) {
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    const size = lastPenSize;
    let ray2 = p;
    if (e.shiftKey) {
      const a1 = Math.atan2(mathEndPoint.y - mathStartPoint.y, mathEndPoint.x - mathStartPoint.x);
      let a2 = Math.atan2(p.y - mathStartPoint.y, p.x - mathStartPoint.x);
      let diff = a2 - a1;
      if (diff < 0) diff += 2 * Math.PI;
      const isCCW = diff > Math.PI;
      
      let angleToSnap;
      if (isCCW) {
        angleToSnap = a2 - 2 * Math.PI;
      } else {
        angleToSnap = a2;
      }
      
      const snapRad = 5 * Math.PI / 180;
      const snapped = Math.round((angleToSnap - a1) / snapRad) * snapRad;
      const finalAngle = a1 + snapped;
      const len2 = Math.sqrt((p.x - mathStartPoint.x)**2 + (p.y - mathStartPoint.y)**2) || 80;
      ray2 = { x: mathStartPoint.x + len2 * Math.cos(finalAngle), y: mathStartPoint.y + len2 * Math.sin(finalAngle) };
    }
    drawProtractor(overlayCtx, mathStartPoint, mathEndPoint, ray2, color, size);
    let a1 = Math.atan2(mathEndPoint.y - mathStartPoint.y, mathEndPoint.x - mathStartPoint.x);
    let a2 = Math.atan2(ray2.y - mathStartPoint.y, ray2.x - mathStartPoint.x);
    let diff = a2 - a1;
    if (diff < 0) diff += 2 * Math.PI;
    if (diff > Math.PI) diff = 2 * Math.PI - diff;
    showMathInfo('📐 ' + (diff * 180 / Math.PI).toFixed(e.shiftKey ? 0 : 1) + '°' + (e.shiftKey ? '  (snap 5°)' : '  |  Shift = snap 5°'));
    return;
  }
  
  if (tool === 'rect' && drawing) {
    ctx.clearRect(0, 0, drawC.width, drawC.height);
    redrawStrokes();
    const start = currentStroke[0];
    let w = p.x - start.x;
    let h = p.y - start.y;
    if (e.shiftKey) {
      const side = Math.max(Math.abs(w), Math.abs(h));
      w = side * (w < 0 ? -1 : 1);
      h = side * (h < 0 ? -1 : 1);
    }
    ctx.save();
    ctx.strokeStyle = color;
    ctx.lineWidth = lastPenSize;
    ctx.strokeRect(start.x, start.y, w, h);
    ctx.restore();
    return;
  }
  
  if (tool === 'polygon') return;
  
  if (!drawing) return;
  const size = tool === 'erase' ? lastEraserSize : lastPenSize;
  if (tool === 'circle') {
    ctx.clearRect(0, 0, drawC.width, drawC.height);
    redrawStrokes();
    const cx = currentStroke[0].x, cy = currentStroke[0].y;
    const radius = Math.sqrt((p.x - cx)**2 + (p.y - cy)**2);
    ctx.beginPath();
    ctx.arc(cx, cy, radius, 0, 2 * Math.PI);
    ctx.strokeStyle = color; ctx.lineWidth = size;
    ctx.stroke();
  } else if (tool === 'line' || tool === 'arrow' || tool === 'dashed') {
    ctx.clearRect(0, 0, drawC.width, drawC.height);
    redrawStrokes();
    const endPoint = e.shiftKey ? snapPointToAngle(currentStroke[0], p) : snapToGuides(p);
    ctx.beginPath();
    ctx.moveTo(currentStroke[0].x, currentStroke[0].y);
    ctx.lineTo(endPoint.x, endPoint.y);
    ctx.strokeStyle = color; ctx.lineWidth = size; ctx.lineCap = 'round';
    if (tool === 'dashed') ctx.setLineDash([size*2.5, size*1.8]);
    ctx.stroke();
    ctx.setLineDash([]);
    if (tool === 'arrow') {
      const dx = endPoint.x - currentStroke[0].x, dy = endPoint.y - currentStroke[0].y;
      const len = Math.sqrt(dx*dx + dy*dy);
      if (len > 5) {
        const angle = Math.atan2(dy, dx);
        const headLen = Math.min(20, len * 0.4);
        const headAngle = 0.45;
        ctx.fillStyle = color;
        ctx.beginPath();
        ctx.moveTo(endPoint.x, endPoint.y);
        ctx.lineTo(endPoint.x - headLen * Math.cos(angle - headAngle), endPoint.y - headLen * Math.sin(angle - headAngle));
        ctx.lineTo(endPoint.x - headLen * Math.cos(angle + headAngle), endPoint.y - headLen * Math.sin(angle + headAngle));
        ctx.closePath();
        ctx.fill();
      }
    }
  } else {
    currentStroke.push(tool === 'pen' ? snapToGuides(p) : p);
    ctx.clearRect(0, 0, drawC.width, drawC.height);
    redrawStrokes();
    drawStrokeOn(ctx, {points: currentStroke, color, size, erase: tool==='erase'});
  }
}

function handlePointerUp(e) {

  if (tool === 'select' && isResizingStroke) {
    isResizingStroke = false;
    const page = getCurrentPage();
    const stroke = page ? page.strokes[resizeStrokeIndex] : null;
    if (page && stroke && resizeOriginalStroke) {
      const after = JSON.parse(JSON.stringify(stroke));
      if (JSON.stringify(after) !== JSON.stringify(resizeOriginalStroke)) {
        undoStack.push({ type: 'resizeStroke', page, stroke, before: resizeOriginalStroke, after });
        redoStack = [];
        showToast('✓ Stroke scalat');
      }
    }
    resizeOriginalStroke = null;
    resizeStrokeIndex = -1;
    updateStatus();
    return;
  }

  if (tool === 'select' && isSelecting) {
    isSelecting = false;
    const p = pos(e);
    const dragDist = Math.hypot(p.x - selectionStartX, p.y - selectionStartY);
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    lassoPoints = [];

    if (dragDist < 3) {
      selectedStrokes = new Set(lassoAdditive ? lassoBaseSelection : []);
      if (!lassoAdditive) {
        selectedImages.clear();
        updateImageSelection();
      }
    }

    drawSelectionHighlights();
    updateStatus();
    
    const count = selectedStrokes.size + selectedImages.size;
    if (count > 0) {
      let msg = '';
      if (selectedStrokes.size > 0) msg += `${selectedStrokes.size} stroke-uri`;
      if (selectedImages.size > 0) msg += (msg ? ' + ' : '') + `${selectedImages.size} imagini`;
      showSelectionInfo(`✓ ${msg} selectate (Delete pentru ștergere)`);
    } else {
      hideSelectionInfo();
    }
    return;
  }

  if (tool === 'select' && isDraggingSelected) {
    isDraggingSelected = false;
    const page = getCurrentPage();
    if (page) {
      const items = [];
      for (const [si, before] of moveUndoSnapshots) {
        const stroke = page.strokes[si];
        const after = snapshotStrokePosition(stroke);
        if (!samePosition(before, after)) {
          items.push({ stroke, before, after });
        }
      }
      if (items.length > 0) {
        undoStack.push({ type: 'move', page, items });
        redoStack = [];
      }
    }
    moveUndoSnapshots.clear();
    dragStartPositions.clear();
    showToast(`✓ ${selectedStrokes.size} stroke-uri mutate`);
    updateStatus();
    return;
  }
  
  if (tool === 'polygon' && drawing) {
    return;
  }
  
  if (isMathDrawing) {
    isMathDrawing = false;
    const p = pos(e);
    const page = getCurrentPage();
    const size = tool === 'erase' ? lastEraserSize : lastPenSize;
    
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    
    if (tool === 'ruler' && mathStartPoint) {
      let ep = p;
      if (e.shiftKey) {
        const angle = Math.atan2(p.y - mathStartPoint.y, p.x - mathStartPoint.x);
        const snapRad = 15 * Math.PI / 180;
        const snapped = Math.round(angle / snapRad) * snapRad;
        const len = Math.sqrt((p.x - mathStartPoint.x)**2 + (p.y - mathStartPoint.y)**2);
        ep = { x: mathStartPoint.x + len * Math.cos(snapped), y: mathStartPoint.y + len * Math.sin(snapped) };
      }
      const dist = Math.sqrt((ep.x - mathStartPoint.x)**2 + (ep.y - mathStartPoint.y)**2);
      if (dist > 10) {
        pushStroke(page, {
          points: [mathStartPoint, ep],
          color: color,
          size: size,
          erase: false,
          ruler: true
        });
        showToast('✓ Riglă: ' + (dist/50).toFixed(2) + ' cm');
      }
    }
    
    mathStartPoint = null;
    redrawStrokes();
    updateStatus();
    mathInfo.classList.remove('show');
    return;
  }
  
  if (tool === 'protractor' && protractorPhase === 2 && mathStartPoint && mathEndPoint) {
    const p = pos(e);
    const page = getCurrentPage();
    const size = lastPenSize;
    
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    
    const ray1 = mathEndPoint;
    let ray2 = p;
    if (e.shiftKey) {
      const a1 = Math.atan2(ray1.y - mathStartPoint.y, ray1.x - mathStartPoint.x);
      let a2 = Math.atan2(p.y - mathStartPoint.y, p.x - mathStartPoint.x);
      let diff = a2 - a1;
      if (diff < 0) diff += 2 * Math.PI;
      const isCCW = diff > Math.PI;
      
      let angleToSnap;
      if (isCCW) {
        angleToSnap = a2 - 2 * Math.PI;
      } else {
        angleToSnap = a2;
      }
      
      const snapRad = 5 * Math.PI / 180;
      const snapped = Math.round((angleToSnap - a1) / snapRad) * snapRad;
      const finalAngle = a1 + snapped;
      const len2 = Math.sqrt((p.x - mathStartPoint.x)**2 + (p.y - mathStartPoint.y)**2) || 80;
      ray2 = { x: mathStartPoint.x + len2 * Math.cos(finalAngle), y: mathStartPoint.y + len2 * Math.sin(finalAngle) };
    }
    
    let a1 = Math.atan2(ray1.y - mathStartPoint.y, ray1.x - mathStartPoint.x);
    let a2 = Math.atan2(ray2.y - mathStartPoint.y, ray2.x - mathStartPoint.x);
    let diff = a2 - a1;
    if (diff < 0) diff += 2 * Math.PI;
    if (diff > Math.PI) diff = 2 * Math.PI - diff;
    
    if (diff > 0.05) {
      pushStroke(page, {
        type: 'angle',
        vertex: { x: mathStartPoint.x, y: mathStartPoint.y },
        ray1: { x: ray1.x, y: ray1.y },
        ray2: { x: ray2.x, y: ray2.y },
        color: color,
        size: size
      });
      showToast('✓ Unghi desenat: ' + (diff * 180 / Math.PI).toFixed(1) + '°');
    }
    
    mathStartPoint = null;
    mathEndPoint = null;
    protractorPhase = 0;
    redrawStrokes();
    updateStatus();
    mathInfo.classList.remove('show');
    return;
  }
  
  if (tool === 'protractor' && protractorPhase === 1 && mathStartPoint) {
    const p = pos(e);
    mathEndPoint = p;
    protractorPhase = 2;
    showMathInfo('🔄 Trage pentru a roti a doua latură  |  Shift = snap 5°');
    return;
  }
  
  if (tool === 'rect' && drawing) {
    drawing = false;
    const p = pos(e);
    const page = getCurrentPage();
    const start = currentStroke[0];
    let w = p.x - start.x;
    let h = p.y - start.y;
    if (e.shiftKey) {
      const side = Math.max(Math.abs(w), Math.abs(h));
      w = side * (w < 0 ? -1 : 1);
      h = side * (h < 0 ? -1 : 1);
    }
    const endX = start.x + w, endY = start.y + h;
    if (Math.abs(w) > 3 && Math.abs(h) > 3) {
      const rect = {
        type: 'rect',
        x: Math.min(start.x, endX),
        y: Math.min(start.y, endY),
        w: Math.abs(w),
        h: Math.abs(h),
        color: color,
        size: lastPenSize
      };
      pushStroke(page, rect);
      showToast(e.shiftKey ? `✓ Pătrat desenat (${Math.round(Math.abs(w))}×${Math.round(Math.abs(h))})` : `✓ Dreptunghi desenat (${Math.round(Math.abs(w))}×${Math.round(Math.abs(h))})`);
    }
    currentStroke = [];
    redrawStrokes();
    updateStatus();
    return;
  }
  
  if (!drawing) return;
  drawing = false;
  const page = getCurrentPage();
  const size = tool === 'erase' ? lastEraserSize : lastPenSize;
  if (tool === 'line') {
    const endP = e.shiftKey ? snapPointToAngle(currentStroke[0], pos(e)) : snapToGuides(pos(e));
    pushStroke(page, {points: [currentStroke[0], endP], color, size, erase: false});
  } else if (tool === 'dashed') {
    const endP = e.shiftKey ? snapPointToAngle(currentStroke[0], pos(e)) : snapToGuides(pos(e));
    pushStroke(page, {points: [currentStroke[0], endP], color, size, erase: false, dashed: true});
  } else if (tool === 'arrow') {
    const endP = e.shiftKey ? snapPointToAngle(currentStroke[0], pos(e)) : snapToGuides(pos(e));
    pushStroke(page, {type: 'arrow', points: [currentStroke[0], endP], color, size, erase: false});
  } else if (tool === 'circle') {
    const cx = currentStroke[0].x, cy = currentStroke[0].y;
    const endP = pos(e);
    const radius = Math.sqrt((endP.x - cx)**2 + (endP.y - cy)**2);
    if (radius > 3) {
      pushStroke(page, {type: 'circle', cx, cy, radius, color, size});
    }
  } else if (currentStroke.length) {
    pushStroke(page, {points: [...currentStroke], color, size, erase: tool==='erase'});
  }
  currentStroke = [];
  redrawStrokes();
  updateStatus();
}

function handlePointerLeave() {
  if (tool === 'pen') drawC.style.cursor = '';
}

function handleDblClick(e) {

  if (tool === 'polygon' && drawing && currentStroke && currentStroke.length >= 3) {
    finalizePolygon();
    return;
  }

  if (!isMathTool()) {
    const p = pos(e);
    const page = getCurrentPage();
    const idx = findStrokeAt(p.x, p.y, page);
    if (idx >= 0 && page.strokes[idx].type === 'text') {
      const s = page.strokes[idx];
      setTool('text');
      showTextOverlay(s.x, s.y, idx);
      showToast('✏️ Editare text - Enter pentru a salva');
      return;
    }
  }

}

boardDrawC.addEventListener('pointerdown', function(e) { activatePane('board'); handlePointerDown(e); });
boardDrawC.addEventListener('pointermove', handlePointerMove);
boardDrawC.addEventListener('pointerup', handlePointerUp);
boardDrawC.addEventListener('pointercancel', handlePointerUp);
boardDrawC.addEventListener('pointerleave', handlePointerLeave);
boardDrawC.addEventListener('dblclick', handleDblClick);

document.addEventListener('keydown', e => {
  if (e.key === 'Escape') {
    if (tool === 'polygon' && drawing) {
      drawing = false;
      currentStroke = [];
      redrawStrokes();
      showToast('❌ Poligon anulat');
    }
    if (protractorPhase > 0) {
      protractorPhase = 0;
      mathStartPoint = null;
      mathEndPoint = null;
    }
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    mathInfo.classList.remove('show');
  }
  
  if (e.key === 'Enter' && tool === 'polygon' && drawing && currentStroke && currentStroke.length >= 3) {
    finalizePolygon();
    return;
  }
  
  if (e.key === 'Delete' || e.key === 'Backspace') {
    if ((selectedStrokes.size > 0 || selectedImages.size > 0) && !e.target.matches('input, textarea')) {
      e.preventDefault();
      if (selectedStrokes.size > 0) deleteSelectedStrokes();
      if (selectedImages.size > 0) deleteSelectedImages();
    }
  }
  
  if ((e.key === ']' || e.key === '[') && selectedImages.size > 0 && !e.target.matches('input, textarea')) {
    e.preventDefault();
    if (e.key === ']') reorderSelectedImages(e.shiftKey ? 'front' : 'forward');
    else reorderSelectedImages(e.shiftKey ? 'back' : 'backward');
  }
  
  if (e.key === 'Escape' && (selectedStrokes.size > 0 || selectedImages.size > 0)) {
    selectedStrokes.clear();
    selectedImages.clear();
    updateImageSelection();
    hideSelectionInfo();
    updateStatus();
    drawSelectionHighlights();
        showToast('❌ Selecție anulată');
  }

  if (e.key === 'Escape' && isSelecting) {
    isSelecting = false;
    lassoPoints = [];
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
  }
  
  if ((e.key === 'v' || e.key === 'V') && !e.ctrlKey && !e.metaKey) {
    e.preventDefault();
    setTool('select');
  }
});

function isMathTool() {
  return false;
}

// ================================================================
// SETARE INSTRUMENTE
// ================================================================

function setTool(t) {
  drawC.style.cursor = '';
  if (tool === 'polygon' && drawing && currentStroke && currentStroke.length >= 3) {
    finalizePolygon();
  } else if (tool === 'polygon' && drawing) {
    drawing = false;
    currentStroke = [];
    redrawStrokes();
  }
  
  protractorPhase = 0;
  mathStartPoint = null;
  mathEndPoint = null;
  isSelecting = false;
  lassoPoints = [];
  isDraggingSelected = false;
  isResizingStroke = false;
  resizeOriginalStroke = null;
  resizeStrokeIndex = -1;
  dragStartPositions.clear();
  moveUndoSnapshots.clear();
  overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
  mathInfo.classList.remove('show');
  
  if (t !== 'select') {
    selectedStrokes.clear();
    selectedImages.clear();
    updateImageSelection();
    hideSelectionInfo();
    updateStatus();
    drawSelectionHighlights();
      }
  
  tool = t;
  imagesContainer.classList.toggle('interactive', tool === 'select');
  const allTools = ['btn-pen','btn-line','btn-dashed','btn-arrow','btn-circle','btn-rect','btn-polygon','btn-erase','btn-text','btn-midpoint','btn-select'];
  allTools.forEach(id => {
    const el = document.getElementById(id);
    if (el) {
      el.classList.toggle('active', tool === id.replace('btn-',''));
    }
  });
  
  if (t !== 'text') hideTextOverlay();
  if (tool === 'erase') {
    document.getElementById('size-val').textContent = lastEraserSize;
  } else {
    document.getElementById('size-val').textContent = lastPenSize;
  }
  
  if (t === 'select') {
    showMathInfo('🖱️ Click pe stroke sau imagine pentru a selecta | Trage pentru a muta | Shift = selecție multiplă | Delete pentru ștergere');
  } else if (t === 'polygon') {
    showMathInfo('🟨 Clickuri pentru puncte, dublu-click sau Enter pentru finalizare | Esc pentru anulare');
  } else if (t === 'rect') {
    showMathInfo('▭ Trage pentru a desena un dreptunghi/patrat  |  Shift = pătrat');
  }
}

// ================================================================
// FUNCȚII PENTRU PAGINI
// ================================================================

function addPage() {
  pages.push({strokes:[], images:[]});
  currentPageIdx = pages.length - 1;
  drawBg(); 
  redrawStrokes(); 
  renderImages();
  updateStatus(); 
}

function prevPage() { 
  if (currentPageIdx > 0) { 
    currentPageIdx--; 
    drawBg(); 
    redrawStrokes(); 
    selectedStrokes.clear();
    selectedImages.clear();
    updateImageSelection();
    hideSelectionInfo();
    renderImages();
    updateStatus(); 
  }
}

function nextPage() {
  if (currentPageIdx >= pages.length - 1) {
    addPage();
  } else {
    currentPageIdx++;
    drawBg();
    redrawStrokes();
    renderImages();
    updateStatus();
  }
  selectedStrokes.clear();
  selectedImages.clear();
  updateImageSelection();
  hideSelectionInfo();
}

async function deletePage() {
  if (pages.length <= 1) {
    if (!(await customConfirm('Aceasta este singura pagină. Ștergerea îi va goli tot conținutul (linii, imagini). Continui?'))) return;
    pages[0] = { strokes: [], images: [] };
    currentPageIdx = 0;
  } else {
    if (!(await customConfirm(`Ștergi pagina ${currentPageIdx + 1} din ${pages.length}? Acțiunea nu poate fi anulată.`))) return;
    pages.splice(currentPageIdx, 1);
    if (currentPageIdx >= pages.length) currentPageIdx = pages.length - 1;
  }
  undoStack = [];
  redoStack = [];
  selectedStrokes.clear();
  selectedImages.clear();
  updateImageSelection();
  hideSelectionInfo();
  drawBg();
  redrawStrokes();
  renderImages();
  updateStatus();
  showToast('✓ Pagina ștearsă');
}

// ================================================================
// FUNCȚII PENTRU ÎNCĂRCARE IMAGINI
// ================================================================

function loadMultipleImages(files) {
  if (!files || files.length === 0) return;
  
  let loaded = 0;
  const total = files.length;
  let currentPage = getCurrentPage();
  
  if (currentPage.strokes.length > 0 || currentPage.images.length > 0) {
    addPage();
    currentPage = getCurrentPage();
  }
  
  Array.from(files).forEach((file, idx) => {
    const img = new Image();
    img.onload = () => {
      const maxW = wrap.clientWidth * 0.8;
      const maxH = wrap.clientHeight * 0.7;
      let w = img.naturalWidth * 1.5;
      let h = img.naturalHeight * 1.5;
      if (w > maxW) { h = h * maxW / w; w = maxW; }
      if (h > maxH) { w = w * maxH / h; h = maxH; }
      
      const page = getCurrentPage();
      const id = addImageToPage(page, img, 40, 40, w, h);
      const imgData = page.images[page.images.length - 1];
      undoStack.push({ type: 'imageAdd', page, img: imgData });
      redoStack = [];
      loaded++;

      if (loaded < total) {
        addPage();
      } else {
        setTool('select');
        selectedImages.clear();
        selectedImages.add(id);
        updateImageSelection();
        showToast(`✓ ${total} imagini încărcate (câte una pe pagină)`);
        updateStatus();
      }
    };
    img.onerror = () => {
      loaded++;
      if (loaded === total) {
        showToast(`⚠ ${total - files.length + loaded} imagini încărcate, unele au eșuat`);
      }
    };
    img.src = URL.createObjectURL(file);
  });
}

// ================================================================
// FUNCȚII DRAW (ruler, protractor, compass)
// ================================================================

function drawRuler(ctx2, x1, y1, x2, y2, color, size, snapping) {
  const dx = x2 - x1, dy = y2 - y1;
  const len = Math.sqrt(dx*dx + dy*dy);
  if (len < 5) return;
  const angle = Math.atan2(dy, dx);
  const perp = angle + Math.PI / 2;
  const cosP = Math.cos(perp), sinP = Math.sin(perp);
  const cosA = Math.cos(angle), sinA = Math.sin(angle);

  ctx2.save();
  ctx2.lineCap = 'round';

  const rulerW = 46;
  const bx1 = x1 - cosA * 18, by1 = y1 - sinA * 18;
  const bx2 = x2 + cosA * 26, by2 = y2 + sinA * 26;

  ctx2.save();
  ctx2.translate(bx1, by1);
  ctx2.rotate(angle);
  const bodyLen = Math.sqrt((bx2-bx1)**2 + (by2-by1)**2);

  ctx2.save();
  ctx2.shadowColor = 'rgba(30,40,70,0.35)';
  ctx2.shadowBlur = 10;
  ctx2.shadowOffsetY = 4;
  const grad = ctx2.createLinearGradient(0, -rulerW/2, 0, rulerW/2);
  grad.addColorStop(0,   'rgba(232,238,250,0.92)');
  grad.addColorStop(0.12,'rgba(255,255,255,0.96)');
  grad.addColorStop(0.5, 'rgba(207,217,238,0.88)');
  grad.addColorStop(0.9, 'rgba(178,192,222,0.9)');
  grad.addColorStop(1,   'rgba(196,208,232,0.9)');
  ctx2.fillStyle = grad;
  ctx2.beginPath();
  ctx2.roundRect(0, -rulerW/2, bodyLen, rulerW, 5);
  ctx2.fill();
  ctx2.restore();

  ctx2.strokeStyle = 'rgba(90,110,160,0.85)';
  ctx2.lineWidth = 1.5;
  ctx2.beginPath();
  ctx2.roundRect(0, -rulerW/2, bodyLen, rulerW, 5);
  ctx2.stroke();

  const shine = ctx2.createLinearGradient(0, -rulerW/2, 0, -rulerW/2 + rulerW*0.4);
  shine.addColorStop(0, 'rgba(255,255,255,0.75)');
  shine.addColorStop(1, 'rgba(255,255,255,0)');
  ctx2.fillStyle = shine;
  ctx2.beginPath();
  ctx2.roundRect(2, -rulerW/2 + 2, bodyLen - 4, rulerW*0.42, 4);
  ctx2.fill();

  ctx2.strokeStyle = 'rgba(90,110,160,0.5)';
  ctx2.lineWidth = 1;
  ctx2.beginPath();
  ctx2.moveTo(4, rulerW/2 - 4);
  ctx2.lineTo(bodyLen - 4, rulerW/2 - 4);
  ctx2.stroke();

  ctx2.restore();

  const cmStep = 50;
  const mmStep = cmStep / 10;
  const graduationBase = -rulerW/2 + 6;

  for (let d = 0; d <= len; d += mmStep) {
    const t = d / len;
    const px = x1 + dx * t;
    const py = y1 + dy * t;
    const isCm = Math.abs(d % cmStep) < 0.5;
    const isHalfCm = Math.abs(d % (cmStep/2)) < 0.5;
    const mLen = isCm ? 16 : (isHalfCm ? 11 : 6.5);
    ctx2.strokeStyle = isCm ? '#1a1f33' : '#3a4260';
    ctx2.lineWidth = isCm ? 1.6 : 1;
    ctx2.beginPath();
    ctx2.moveTo(px + cosP * graduationBase, py + sinP * graduationBase);
    ctx2.lineTo(px + cosP * (graduationBase + mLen), py + sinP * (graduationBase + mLen));
    ctx2.stroke();

    if (isCm) {
      const n = Math.round(d / cmStep);
      ctx2.font = '600 12px "Segoe UI", sans-serif';
      ctx2.fillStyle = '#1a1f33';
      ctx2.textAlign = 'center';
      ctx2.textBaseline = 'middle';
      ctx2.save();
      ctx2.translate(px + cosP * (graduationBase + mLen + 9), py + sinP * (graduationBase + mLen + 9));
      ctx2.rotate(angle);
      ctx2.fillText(n, 0, 0);
      ctx2.restore();
    }
  }

  ctx2.strokeStyle = color;
  ctx2.lineWidth = size || 2;
  ctx2.beginPath();
  ctx2.moveTo(x1, y1);
  ctx2.lineTo(x2, y2);
  ctx2.stroke();
  ctx2.fillStyle = color;
  ctx2.beginPath(); ctx2.arc(x1, y1, 3.5, 0, Math.PI*2); ctx2.fill();
  ctx2.beginPath(); ctx2.arc(x2, y2, 3.5, 0, Math.PI*2); ctx2.fill();

  const midX = (x1 + x2) / 2;
  const midY = (y1 + y2) / 2;
  let trigDeg = -angle * 180 / Math.PI;
  trigDeg = ((trigDeg % 360) + 360) % 360;
  const label = (len/50).toFixed(1) + ' cm' + (snapping ? '  |  ' + Math.round(trigDeg) + '°' : '');

  ctx2.font = 'bold 13px sans-serif';
  const tw = ctx2.measureText(label).width;
  const labelOffset = rulerW/2 + 18;
  ctx2.fillStyle = 'rgba(255,255,255,0.95)';
  ctx2.strokeStyle = color;
  ctx2.lineWidth = 1.2;
  ctx2.beginPath();
  ctx2.roundRect(midX - cosP*labelOffset - tw/2 - 5, midY - sinP*labelOffset - 10, tw + 10, 20, 5);
  ctx2.fill(); ctx2.stroke();
  ctx2.fillStyle = color;
  ctx2.textAlign = 'center';
  ctx2.textBaseline = 'middle';
  ctx2.fillText(label, midX - cosP*labelOffset, midY - sinP*labelOffset);

  ctx2.restore();
}

function drawProtractor(ctx2, vertex, ray1end, ray2end, color, size) {
  ctx2.save();

  let a1 = Math.atan2(ray1end.y - vertex.y, ray1end.x - vertex.x);
  let a2 = Math.atan2(ray2end.y - vertex.y, ray2end.x - vertex.x);

  let cwDiff = a2 - a1;
  if (cwDiff < 0) cwDiff += 2 * Math.PI;
  let ccwDiff = a1 - a2;
  if (ccwDiff < 0) ccwDiff += 2 * Math.PI;

  let isCCW, angleDiff, startA, endA;
  if (cwDiff <= Math.PI) {
    isCCW = false;
    angleDiff = cwDiff;
    startA = a1;
    endA = a2 < a1 ? a2 + 2*Math.PI : a2;
  } else {
    isCCW = true;
    angleDiff = ccwDiff;
    startA = a1;
    endA = a1 - angleDiff;
  }

  const deg = angleDiff * 180 / Math.PI;
  const rProtr = Math.min(Math.max(60, 90), 120);

  ctx2.save();
  ctx2.translate(vertex.x, vertex.y);

  const drawProtractorBody = (sweepSign) => {
    const bodyR = rProtr + 14;

    const grad = ctx2.createRadialGradient(0, 0, bodyR*0.15, 0, 0, bodyR);
    grad.addColorStop(0,   'rgba(255,250,225,0.55)');
    grad.addColorStop(0.75,'rgba(255,225,140,0.42)');
    grad.addColorStop(1,   'rgba(240,190,60,0.5)');
    ctx2.save();
    ctx2.shadowColor = 'rgba(120,90,0,0.25)';
    ctx2.shadowBlur = 8;
    ctx2.fillStyle = grad;
    ctx2.strokeStyle = 'rgba(150,110,0,0.75)';
    ctx2.lineWidth = 1.8;
    ctx2.beginPath();
    ctx2.arc(0, 0, bodyR, 0, sweepSign * angleDiff, sweepSign < 0);
    ctx2.lineTo(0, 0);
    ctx2.closePath();
    ctx2.fill();
    ctx2.stroke();
    ctx2.restore();

    ctx2.save();
    ctx2.strokeStyle = 'rgba(255,255,255,0.55)';
    ctx2.lineWidth = 3;
    ctx2.beginPath();
    ctx2.arc(0, 0, bodyR - 3, sweepSign*0.05, sweepSign * angleDiff * 0.85, sweepSign < 0);
    ctx2.stroke();
    ctx2.restore();

    for (let d = 0; d <= Math.round(deg); d++) {
      const rad = sweepSign * d * Math.PI / 180;
      if (Math.abs(rad) > angleDiff + 0.005) break;
      const isMajor = d % 10 === 0;
      const isMid = d % 5 === 0;
      const tickLen = isMajor ? 13 : (isMid ? 9 : 5);
      const r0 = rProtr - tickLen;
      ctx2.strokeStyle = isMajor ? '#3a2a00' : 'rgba(80,60,0,0.65)';
      ctx2.lineWidth = isMajor ? 1.4 : 0.9;
      ctx2.beginPath();
      ctx2.moveTo(r0 * Math.cos(rad), r0 * Math.sin(rad));
      ctx2.lineTo(rProtr * Math.cos(rad), rProtr * Math.sin(rad));
      ctx2.stroke();

      if (isMajor && d > 0 && d < Math.round(deg)) {
        ctx2.font = '600 9px sans-serif';
        ctx2.fillStyle = '#3a2a00';
        ctx2.textAlign = 'center';
        ctx2.textBaseline = 'middle';
        const lr = rProtr - 20;
        ctx2.fillText(d, lr * Math.cos(rad), lr * Math.sin(rad));
      }
    }

    ctx2.strokeStyle = 'rgba(150,110,0,0.8)';
    ctx2.lineWidth = 2;
    ctx2.beginPath();
    ctx2.moveTo(0, 0);
    ctx2.lineTo(bodyR * Math.cos(0), bodyR * Math.sin(0));
    ctx2.stroke();

    ctx2.fillStyle = 'rgba(255,255,255,0.9)';
    ctx2.strokeStyle = 'rgba(120,90,0,0.9)';
    ctx2.lineWidth = 1;
    ctx2.beginPath(); ctx2.arc(0, 0, 3, 0, Math.PI*2); ctx2.fill(); ctx2.stroke();
  };

  if (isCCW) {
    ctx2.rotate(startA);
    drawProtractorBody(-1);
  } else {
    ctx2.rotate(startA);
    drawProtractorBody(1);
  }
  ctx2.restore();

  ctx2.strokeStyle = color;
  ctx2.lineWidth = size || 2;
  ctx2.lineCap = 'round';
  ctx2.beginPath();
  ctx2.moveTo(vertex.x, vertex.y); ctx2.lineTo(ray1end.x, ray1end.y); ctx2.stroke();
  ctx2.beginPath();
  ctx2.moveTo(vertex.x, vertex.y); ctx2.lineTo(ray2end.x, ray2end.y); ctx2.stroke();

  ctx2.fillStyle = color;
  ctx2.beginPath(); ctx2.arc(vertex.x, vertex.y, 5, 0, Math.PI*2); ctx2.fill();

  const arcR = Math.min(rProtr - 14, 50);
  ctx2.strokeStyle = color;
  ctx2.lineWidth = (size || 2) + 0.5;
  ctx2.beginPath();
  if (isCCW) {
    ctx2.arc(vertex.x, vertex.y, arcR, a1, a1 - angleDiff, true);
  } else {
    ctx2.arc(vertex.x, vertex.y, arcR, startA, endA);
  }
  ctx2.stroke();

  const midA = isCCW ? (a1 - angleDiff / 2) : ((startA + endA) / 2);
  const labelR = arcR + 22;
  const lx = vertex.x + labelR * Math.cos(midA);
  const ly = vertex.y + labelR * Math.sin(midA);
  const txt = deg.toFixed(1) + '°';
  ctx2.font = 'bold 15px sans-serif';
  const tw = ctx2.measureText(txt).width;
  ctx2.fillStyle = 'rgba(255,255,255,0.9)';
  ctx2.strokeStyle = color;
  ctx2.lineWidth = 1.5;
  ctx2.beginPath();
  ctx2.roundRect(lx - tw/2 - 5, ly - 11, tw + 10, 22, 5);
  ctx2.fill(); ctx2.stroke();
  ctx2.fillStyle = color;
  ctx2.textAlign = 'center';
  ctx2.textBaseline = 'middle';
  ctx2.fillText(txt, lx, ly);

  ctx2.restore();
}

function drawCompassBody(ctx2, center, tip, color) {
  const dx = tip.x - center.x, dy = tip.y - center.y;
  const d = Math.sqrt(dx*dx + dy*dy);
  if (d < 1) return;
  const ux = dx / d, uy = dy / d;
  const nx = -uy, ny = ux;

  const half = d / 2;
  let L = Math.max(d * 0.7, 100);
  const minL = half + 6;
  if (L < minL) L = minL + 8;
  L = Math.min(L, minL + 260);
  const h = Math.sqrt(Math.max(L * L - half * half, 6));

  const midx = (center.x + tip.x) / 2, midy = (center.y + tip.y) / 2;
  const hingeX = midx + nx * h, hingeY = midy + ny * h;

  ctx2.save();

  function drawLeg(x1, y1, x2, y2) {
    const a = Math.atan2(y2 - y1, x2 - x1);
    const legW = 6.5;
    const px = Math.cos(a + Math.PI / 2), py = Math.sin(a + Math.PI / 2);

    const grad = ctx2.createLinearGradient(x1 - px * legW, y1 - py * legW, x1 + px * legW, y1 + py * legW);
    grad.addColorStop(0,    '#6f7480');
    grad.addColorStop(0.42, '#cdd1d9');
    grad.addColorStop(0.55, '#f0f2f6');
    grad.addColorStop(0.7,  '#c3c7d0');
    grad.addColorStop(1,    '#565a64');

    ctx2.save();
    ctx2.shadowColor = 'rgba(20,20,30,0.3)';
    ctx2.shadowBlur = 4;
    ctx2.shadowOffsetY = 2;
    ctx2.strokeStyle = grad;
    ctx2.lineWidth = legW * 2;
    ctx2.lineCap = 'round';
    ctx2.beginPath();
    ctx2.moveTo(x1, y1);
    ctx2.lineTo(x2, y2);
    ctx2.stroke();
    ctx2.restore();

    ctx2.strokeStyle = 'rgba(40,42,50,0.55)';
    ctx2.lineWidth = 1;
    ctx2.beginPath(); ctx2.moveTo(x1 - px*legW, y1 - py*legW); ctx2.lineTo(x2 - px*legW, y2 - py*legW); ctx2.stroke();
    ctx2.beginPath(); ctx2.moveTo(x1 + px*legW, y1 + py*legW); ctx2.lineTo(x2 + px*legW, y2 + py*legW); ctx2.stroke();

    const ex = x1 + (x2 - x1) * 0.44, ey = y1 + (y2 - y1) * 0.44;
    const jg = ctx2.createRadialGradient(ex-2, ey-2, 1, ex, ey, legW*1.05);
    jg.addColorStop(0, '#6a6e78');
    jg.addColorStop(1, '#33353c');
    ctx2.fillStyle = jg;
    ctx2.beginPath(); ctx2.arc(ex, ey, legW*1.05, 0, Math.PI*2); ctx2.fill();
    ctx2.strokeStyle = 'rgba(255,255,255,0.3)'; ctx2.lineWidth = 1;
    ctx2.stroke();
  }

  drawLeg(hingeX, hingeY, center.x, center.y);
  drawLeg(hingeX, hingeY, tip.x, tip.y);

  const hingeR = 11;
  const hg = ctx2.createRadialGradient(hingeX-3, hingeY-3, 1.5, hingeX, hingeY, hingeR);
  hg.addColorStop(0, '#484b52');
  hg.addColorStop(1, '#191b1f');
  ctx2.fillStyle = hg;
  ctx2.beginPath(); ctx2.arc(hingeX, hingeY, hingeR, 0, Math.PI*2); ctx2.fill();
  ctx2.strokeStyle = 'rgba(0,0,0,0.45)'; ctx2.lineWidth = 1.2;
  ctx2.stroke();
  ctx2.fillStyle = 'rgba(255,255,255,0.28)';
  ctx2.beginPath(); ctx2.arc(hingeX-3, hingeY-3, 3, 0, Math.PI*2); ctx2.fill();

  ctx2.strokeStyle = '#15161b';
  ctx2.lineWidth = 2;
  ctx2.beginPath();
  ctx2.moveTo(center.x - ux*10, center.y - uy*10);
  ctx2.lineTo(center.x, center.y);
  ctx2.stroke();
  ctx2.fillStyle = '#0d0d10';
  ctx2.beginPath(); ctx2.arc(center.x, center.y, 2.2, 0, Math.PI*2); ctx2.fill();

  const pa = Math.atan2(tip.y - hingeY, tip.x - hingeX);
  const cosPA = Math.cos(pa), sinPA = Math.sin(pa);
  ctx2.strokeStyle = '#a7adb8';
  ctx2.lineWidth = 6.5;
  ctx2.lineCap = 'butt';
  ctx2.beginPath();
  ctx2.moveTo(tip.x, tip.y);
  ctx2.lineTo(tip.x + cosPA*7, tip.y + sinPA*7);
  ctx2.stroke();
  ctx2.strokeStyle = color;
  ctx2.lineWidth = 3.2;
  ctx2.beginPath();
  ctx2.moveTo(tip.x + cosPA*7, tip.y + sinPA*7);
  ctx2.lineTo(tip.x + cosPA*16, tip.y + sinPA*16);
  ctx2.stroke();
  ctx2.fillStyle = '#202020';
  ctx2.beginPath(); ctx2.arc(tip.x + cosPA*16.5, tip.y + sinPA*16.5, 1.4, 0, Math.PI*2); ctx2.fill();

  ctx2.restore();
}

function drawCompassRadiusPreview(ctx2, center, currentPoint, color, size) {
  if (!center || !currentPoint) return;
  const radius = Math.sqrt((currentPoint.x - center.x)**2 + (currentPoint.y - center.y)**2);
  if (radius < 2) return;

  ctx2.save();
  ctx2.setLineDash([8, 6]);
  ctx2.strokeStyle = color;
  ctx2.lineWidth = 1.5;
  ctx2.globalAlpha = 0.35;
  ctx2.beginPath();
  ctx2.arc(center.x, center.y, radius, 0, Math.PI * 2);
  ctx2.stroke();
  ctx2.setLineDash([]);
  ctx2.globalAlpha = 1;

  drawCompassBody(ctx2, center, currentPoint, color);

  const angle = Math.atan2(currentPoint.y - center.y, currentPoint.x - center.x);
  const midX = center.x + radius/2 * Math.cos(angle);
  const midY = center.y + radius/2 * Math.sin(angle);
  const perpA = angle + Math.PI/2;
  const off = 18;
  const lx = midX + off * Math.cos(perpA);
  const ly = midY + off * Math.sin(perpA);
  const txt = 'r = ' + (radius/50).toFixed(2) + ' cm';
  ctx2.font = 'bold 13px sans-serif';
  const tw = ctx2.measureText(txt).width;
  ctx2.fillStyle = 'rgba(255,255,255,0.9)';
  ctx2.strokeStyle = color; ctx2.lineWidth = 1;
  ctx2.beginPath(); ctx2.roundRect(lx - tw/2 - 4, ly - 10, tw + 8, 20, 4); ctx2.fill(); ctx2.stroke();
  ctx2.fillStyle = color;
  ctx2.textAlign = 'center'; ctx2.textBaseline = 'middle';
  ctx2.fillText(txt, lx, ly);

  ctx2.restore();
  showMathInfo('⭕ Rază: ' + (radius/50).toFixed(2) + ' cm  |  Click stânga = confirmare rază  |  Dublu-click = cerc complet');
}

function drawCompassArcPreview(ctx2, center, radiusPoint, currentPoint, color, size) {
  ctx2.save();

  const radius = Math.sqrt((radiusPoint.x - center.x)**2 + (radiusPoint.y - center.y)**2);
  if (radius < 2) { ctx2.restore(); return; }

  const startAngle = Math.atan2(radiusPoint.y - center.y, radiusPoint.x - center.x);
  let endAngle = Math.atan2(currentPoint.y - center.y, currentPoint.x - center.x);
  if (endAngle < startAngle) endAngle += 2 * Math.PI;
  let angleDiff = endAngle - startAngle;
  if (angleDiff < 0) angleDiff += 2 * Math.PI;

  let interiorAngle = angleDiff;
  let displayStart = startAngle, displayEnd = endAngle;
  if (interiorAngle > Math.PI) {
    interiorAngle = 2 * Math.PI - interiorAngle;
    displayStart = endAngle;
    displayEnd = startAngle + 2 * Math.PI;
  }

  ctx2.setLineDash([6, 8]);
  ctx2.strokeStyle = color;
  ctx2.lineWidth = 1;
  ctx2.globalAlpha = 0.2;
  ctx2.beginPath();
  ctx2.arc(center.x, center.y, radius, 0, Math.PI * 2);
  ctx2.stroke();
  ctx2.setLineDash([]);
  ctx2.globalAlpha = 1;

  ctx2.strokeStyle = color;
  ctx2.lineWidth = (size || 2) + 1;
  ctx2.lineCap = 'round';
  ctx2.beginPath();
  ctx2.arc(center.x, center.y, radius, displayStart, displayEnd);
  ctx2.stroke();

  ctx2.setLineDash([4, 4]);
  ctx2.lineWidth = 1;
  ctx2.globalAlpha = 0.45;
  ctx2.beginPath();
  ctx2.moveTo(center.x, center.y);
  ctx2.lineTo(center.x + radius * Math.cos(startAngle), center.y + radius * Math.sin(startAngle));
  ctx2.stroke();
  ctx2.beginPath();
  ctx2.moveTo(center.x, center.y);
  ctx2.lineTo(center.x + radius * Math.cos(endAngle), center.y + radius * Math.sin(endAngle));
  ctx2.stroke();
  ctx2.setLineDash([]);
  ctx2.globalAlpha = 1;

  const drawAngle = Math.atan2(currentPoint.y - center.y, currentPoint.x - center.x);
  const pencilPoint = {
    x: center.x + radius * Math.cos(drawAngle),
    y: center.y + radius * Math.sin(drawAngle)
  };
  drawCompassBody(ctx2, center, pencilPoint, color);

  const midA = (displayStart + displayEnd) / 2;
  const deg = interiorAngle * 180 / Math.PI;
  const labelR = radius + 28;
  const lx = center.x + labelR * Math.cos(midA);
  const ly = center.y + labelR * Math.sin(midA);
  const txt = deg.toFixed(1) + '°';
  ctx2.font = 'bold 14px sans-serif';
  const tw = ctx2.measureText(txt).width;
  ctx2.fillStyle = 'rgba(255,255,255,0.92)';
  ctx2.strokeStyle = color; ctx2.lineWidth = 1.5;
  ctx2.beginPath(); ctx2.roundRect(lx - tw/2 - 5, ly - 11, tw + 10, 22, 5); ctx2.fill(); ctx2.stroke();
  ctx2.fillStyle = color;
  ctx2.textAlign = 'center'; ctx2.textBaseline = 'middle';
  ctx2.fillText(txt, lx, ly);

  const rxl = center.x + (radius + 16) * Math.cos(startAngle);
  const ryl = center.y + (radius + 16) * Math.sin(startAngle);
  const rtxt = 'r = ' + (radius/50).toFixed(2) + ' cm';
  ctx2.font = '11px sans-serif';
  ctx2.fillStyle = color;
  ctx2.textAlign = 'left'; ctx2.textBaseline = 'bottom';
  ctx2.fillText(rtxt, rxl + 4, ryl - 2);

  showMathInfo('⭕ Rază: ' + (radius/50).toFixed(2) + ' cm  |  Arc: ' + deg.toFixed(1) + '°  |  Dublu-click = cerc complet');

  ctx2.restore();
}

function isColorDark(hex) {
  const h = hex.replace('#', '');
  const r = parseInt(h.substring(0, 2), 16);
  const g = parseInt(h.substring(2, 4), 16);
  const b = parseInt(h.substring(4, 6), 16);
  const luminance = (0.299 * r + 0.587 * g + 0.114 * b) / 255;
  return luminance < 0.5;
}

function updateGeoToolContrast() {
  document.body.classList.toggle('dark-board', isColorDark(bgColor));
}

function setBackgroundColor(newColor, btnId) {
  bgColor = newColor;
  document.querySelectorAll('.bg-color-btn').forEach(b => b.classList.remove('active-bg'));
  if (btnId) {
    document.getElementById(btnId).classList.add('active-bg');
  }
  // Fundalul div-ului (nu doar al canvas-ului) trebuie sincronizat, altfel
  // în timpul redimensionării (ex. tragerea barei dintre fișă și tablă)
  // apare pentru o clipă fundalul implicit al div-ului, nu culoarea aleasă.
  wrap.style.background = newColor;
  updateGeoToolContrast();
  drawBg();
  redrawStrokes();
}

function setColorFromButton(c, btnId) {
  color = c;
  document.getElementById('color-pick').value = c;
  document.querySelectorAll('.color-btn').forEach(b => b.classList.remove('active-color'));
  document.getElementById(btnId).classList.add('active-color');
}

function getCurrentSize() {
  return tool === 'erase' ? lastEraserSize : lastPenSize;
}

function setCurrentSize(v) {
  v = Math.max(1, Math.min(50, v));
  if (tool === 'erase') lastEraserSize = v; else lastPenSize = v;
  document.getElementById('size-val').textContent = v;
}

// ================================================================
// TEXT OVERLAY
// ================================================================

const textOverlay = document.getElementById('text-overlay');
const txtArea = document.getElementById('txt-area');
const txtFontSel = document.getElementById('txt-font');
const txtSizeInput = document.getElementById('txt-size');
const txtBoldBtn = document.getElementById('txt-bold');
const txtItalicBtn = document.getElementById('txt-italic');
const txtAlignLeft = document.getElementById('txt-align-left');
const txtAlignCenter = document.getElementById('txt-align-center');
const txtAlignRight = document.getElementById('txt-align-right');
const txtColorPicker = document.getElementById('txt-color-pick');
const txtColorPalette = document.getElementById('txt-color-palette');

let txtBold = false, txtItalic = false, txtAlign = 'left';
let txtCanvasX = 0, txtCanvasY = 0;
let editingStrokeIndex = null;
let txtColorOverride = null;

function updateAlignButtons() {
  [txtAlignLeft, txtAlignCenter, txtAlignRight].forEach(btn => btn.classList.remove('active-align'));
  if (txtAlign === 'left') txtAlignLeft.classList.add('active-align');
  else if (txtAlign === 'center') txtAlignCenter.classList.add('active-align');
  else if (txtAlign === 'right') txtAlignRight.classList.add('active-align');
}

txtAlignLeft.addEventListener('click', () => { txtAlign = 'left'; updateAlignButtons(); autoResizeTxtArea(); });
txtAlignCenter.addEventListener('click', () => { txtAlign = 'center'; updateAlignButtons(); autoResizeTxtArea(); });
txtAlignRight.addEventListener('click', () => { txtAlign = 'right'; updateAlignButtons(); autoResizeTxtArea(); });

function fontFamilyFromFontString(font) {
  if (!font) return 'sans-serif';
  if (font.includes('monospace')) return 'monospace';
  if (font.includes('Arial')) return 'Arial, sans-serif';
  if (font.includes('Georgia')) return 'Georgia, serif';
  if (font.includes('sans-serif')) return 'sans-serif';
  if (font.includes('serif')) return 'serif';
  return 'sans-serif';
}

function getTextDimensions(text, fontSize, fontFamily, bold, italic) {
  const font = (italic ? 'italic ' : '') + (bold ? 'bold ' : '') + fontSize + 'px ' + fontFamily;
  const canvas = document.createElement('canvas');
  const ctx = canvas.getContext('2d');
  ctx.font = font;
  const lines = text.split('\n');
  const widths = lines.map(l => ctx.measureText(l || ' ').width);
  const maxWidth = Math.max(...widths, 20);
  const height = lines.length * fontSize * 1.3 + 10;
  return { width: maxWidth + 20, height: height, maxWidth: maxWidth };
}

function showTextOverlay(cx, cy, editIndex = null) {
  // Dacă suntem într-o fereastră PDF, mutăm caseta de text în acel container,
  // altfel poziția s-ar calcula față de tabla normală (ascunsă).
  const container = (pdfModeActive && activeSurface === 'top')
    ? getPaneEls(activeSurface).root
    : wrap;
  if (textOverlay.parentElement !== container) container.appendChild(textOverlay);

  const rect = drawC.getBoundingClientRect();
  const wrapRect = container.getBoundingClientRect();
  const sx = cx + rect.left - wrapRect.left;
  const sy = cy + rect.top - wrapRect.top;
  txtCanvasX = cx;
  txtCanvasY = cy;
  
  const padding = 10;
  textOverlay.style.left = Math.max(padding, sx) + 'px';
  textOverlay.style.top = Math.max(padding, sy) + 'px';
  textOverlay.style.display = 'block';
  textOverlay.style.width = 'auto';
  textOverlay.style.height = 'auto';
  textOverlay.style.minWidth = '220px';
  textOverlay.style.minHeight = '100px';

  editingStrokeIndex = editIndex;
  const page = getCurrentPage();
  const existing = (editIndex !== null && page) ? page.strokes[editIndex] : null;

  if (existing) {
    txtArea.value = existing.text || '';
    txtSizeInput.value = existing.fontSize || 28;
    txtFontSel.value = fontFamilyFromFontString(existing.font);
    txtBold = !!(existing.font && existing.font.includes('bold'));
    txtItalic = !!(existing.font && existing.font.includes('italic'));
    txtAlign = existing.textAlign || 'left';
    txtColorOverride = existing.color;
    txtColorPicker.value = existing.color || color;
  } else {
    txtArea.value = '';
    txtBold = false;
    txtItalic = false;
    txtAlign = 'left';
    txtColorOverride = null;
    txtColorPicker.value = color;
  }
  
  txtBoldBtn.classList.toggle('active-fmt', txtBold);
  txtItalicBtn.classList.toggle('active-fmt', txtItalic);
  updateAlignButtons();

  updateColorPaletteActive(txtColorPicker.value);

  const fs = parseInt(txtSizeInput.value) || 28;
  const fontFamily = txtFontSel.value;
  const currentColor = txtColorOverride || txtColorPicker.value || color;
  txtArea.style.fontSize = fs + 'px';
  txtArea.style.fontFamily = fontFamily;
  txtArea.style.fontWeight = txtBold ? 'bold' : 'normal';
  txtArea.style.fontStyle = txtItalic ? 'italic' : 'normal';
  txtArea.style.color = currentColor;
  txtArea.style.textAlign = txtAlign;
  txtArea.style.minWidth = '100%';
  txtArea.style.minHeight = '50px';
  
  autoResizeTxtArea();
  setTimeout(() => { 
    txtArea.focus(); 
    if (existing) txtArea.select();
    autoResizeTxtArea();
    txtArea.style.width = '100%';
    txtArea.style.height = 'calc(100% - 4px)';
  }, 30);
}

function updateColorPaletteActive(color) {
  document.querySelectorAll('#txt-color-palette .mini-color').forEach(el => {
    el.classList.toggle('active-txt-color', el.dataset.color === color);
  });
}

function hideTextOverlay() {
  textOverlay.style.display = 'none';
  txtArea.value = '';
  editingStrokeIndex = null;
  txtColorOverride = null;
}

function autoResizeTxtArea() {
  const fs = parseInt(txtSizeInput.value) || 28;
  const fontFamily = txtFontSel.value;
  const text = txtArea.value || '';
  
  const dims = getTextDimensions(text, fs, fontFamily, txtBold, txtItalic);
  const currentColor = txtColorOverride || txtColorPicker.value || color;
  txtArea.style.fontSize = fs + 'px';
  txtArea.style.fontFamily = fontFamily;
  txtArea.style.fontWeight = txtBold ? 'bold' : 'normal';
  txtArea.style.fontStyle = txtItalic ? 'italic' : 'normal';
  txtArea.style.color = currentColor;
  txtArea.style.textAlign = txtAlign;
  txtArea.style.width = '100%';
  txtArea.style.height = 'calc(100% - 4px)';
  txtArea.style.minHeight = '50px';
}

function commitText() {
  const text = txtArea.value;
  if (!text.trim() && editingStrokeIndex === null) { 
    hideTextOverlay(); 
    return; 
  }
  
  const fs = parseInt(txtSizeInput.value) || 28;
  const fontFamily = txtFontSel.value;
  const font = (txtItalic ? 'italic ' : '') + (txtBold ? 'bold ' : '') + fs + 'px ' + fontFamily;
  const page = getCurrentPage();
  const finalColor = txtColorOverride || txtColorPicker.value || color;

  if (editingStrokeIndex !== null && page && page.strokes[editingStrokeIndex]) {
    const s = page.strokes[editingStrokeIndex];
    s.text = text;
    s.font = font;
    s.color = finalColor;
    s.fontSize = fs;
    s.textAlign = txtAlign;
  } else if (text.trim()) {
    pushStroke(page, {
      type: 'text',
      text: text,
      x: txtCanvasX,
      y: txtCanvasY,
      font: font,
      color: finalColor,
      fontSize: fs,
      textAlign: txtAlign
    });
  }
  redrawStrokes();
  updateStatus();
    hideTextOverlay();
}

txtArea.addEventListener('input', autoResizeTxtArea);
txtArea.addEventListener('keydown', e => {
  e.stopPropagation();
  if (e.key === 'Escape') {
    e.preventDefault();
    hideTextOverlay();
  }
  if (e.ctrlKey && e.key === 'Enter') {
    e.preventDefault();
    commitText();
  }
});

txtBoldBtn.addEventListener('click', () => {
  txtBold = !txtBold;
  txtBoldBtn.classList.toggle('active-fmt', txtBold);
  autoResizeTxtArea();
});
txtItalicBtn.addEventListener('click', () => {
  txtItalic = !txtItalic;
  txtItalicBtn.classList.toggle('active-fmt', txtItalic);
  autoResizeTxtArea();
});
txtFontSel.addEventListener('change', autoResizeTxtArea);
txtSizeInput.addEventListener('input', autoResizeTxtArea);

txtColorPicker.addEventListener('input', () => {
  txtColorOverride = txtColorPicker.value;
  updateColorPaletteActive(txtColorPicker.value);
  autoResizeTxtArea();
});

txtColorPalette.addEventListener('click', (e) => {
  const el = e.target.closest('.mini-color');
  if (!el) return;
  const c = el.dataset.color;
  txtColorOverride = c;
  txtColorPicker.value = c;
  updateColorPaletteActive(c);
  autoResizeTxtArea();
});

document.getElementById('txt-ok').addEventListener('click', commitText);
document.getElementById('txt-cancel').addEventListener('click', hideTextOverlay);

let textResizing = false;
let textResizeStartX = 0, textResizeStartY = 0;
let textResizeStartW = 0, textResizeStartH = 0;

const txtResizeHandle = document.getElementById('txt-resize-handle');

txtResizeHandle.addEventListener('pointerdown', (e) => {
  e.stopPropagation();
  e.preventDefault();
  textResizing = true;
  textResizeStartX = e.clientX;
  textResizeStartY = e.clientY;
  textResizeStartW = textOverlay.offsetWidth;
  textResizeStartH = textOverlay.offsetHeight;
  txtResizeHandle.setPointerCapture(e.pointerId);
});

document.addEventListener('pointermove', (e) => {
  if (!textResizing) return;
  
  const dx = e.clientX - textResizeStartX;
  const dy = e.clientY - textResizeStartY;
  
  let newW = Math.max(220, textResizeStartW + dx);
  let newH = Math.max(100, textResizeStartH + dy);
  
  const wrapRect = wrap.getBoundingClientRect();
  const overlayRect = textOverlay.getBoundingClientRect();
  const maxW = wrapRect.width - overlayRect.left + wrapRect.left - 20;
  const maxH = wrapRect.height - overlayRect.top + wrapRect.top - 20;
  
  newW = Math.min(newW, maxW);
  newH = Math.min(newH, maxH);
  
  textOverlay.style.width = newW + 'px';
  textOverlay.style.height = newH + 'px';
  
  txtArea.style.width = '100%';
  txtArea.style.height = 'calc(100% - 4px)';
  txtArea.style.minHeight = '50px';
});

document.addEventListener('pointerup', () => {
  if (textResizing) {
    textResizing = false;
    txtArea.style.width = '100%';
    txtArea.style.height = 'calc(100% - 4px)';
  }
});

// ================================================================
// REPREZENTARE GRAFICĂ A FUNCȚIILOR f(x)
// ================================================================

// Convertește o expresie scrisă (opțional în LaTeX) într-o expresie JS evaluabilă.
function parseMathExpression(raw) {
  let expr = (raw || '').trim();
  if (!expr) return '';

  // elimină prefixe gen "f(x)=" sau "y="
  expr = expr.replace(/^\s*[a-zA-Z]\w*\s*\(\s*x\s*\)\s*=\s*/i, '');
  expr = expr.replace(/^\s*y\s*=\s*/i, '');

  expr = expr.replace(/\\left/g, '').replace(/\\right/g, '');
  expr = expr.replace(/\\cdot/g, '*').replace(/\\times/g, '*');

  // \frac{a}{b} -> ((a)/(b)), aplicat repetat pentru fracții imbricate simplu
  let prev;
  do {
    prev = expr;
    expr = expr.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '(($1)/($2))');
  } while (expr !== prev);

  // \sqrt[n]{a} -> ((a)**(1/(n)))
  expr = expr.replace(/\\sqrt\[([^\[\]]*)\]\{([^{}]*)\}/g, '(($2)**(1/($1)))');
  // \sqrt{a} -> sqrt(a)
  do {
    prev = expr;
    expr = expr.replace(/\\sqrt\{([^{}]*)\}/g, 'sqrt($1)');
  } while (expr !== prev);

  // exponent cu acolade: ^{...} -> **(...)
  do {
    prev = expr;
    expr = expr.replace(/\^\{([^{}]*)\}/g, '**($1)');
  } while (expr !== prev);
  // restul de exponenți: ^ -> **
  expr = expr.replace(/\^/g, '**');

  expr = expr.replace(/\\pi\b/g, 'PI');
  // înmulțire implicită în jurul constantei PI (ex: "\pi x" sau "2\pi")
  expr = expr.replace(/\bPI\b\s*(?=[a-zA-Z0-9(])/g, 'PI*');
  expr = expr.replace(/([a-zA-Z0-9)])\s*\bPI\b/g, '$1*PI');

  // funcții latex cu backslash: elimină backslash-ul (asin/acos/atan gestionate separat)
  expr = expr.replace(/\\arcsin/g, 'asin').replace(/\\arccos/g, 'acos').replace(/\\arctan/g, 'atan');
  expr = expr.replace(/\\ln\b/g, 'ln');
  expr = expr.replace(/\\(sin|cos|tan|sinh|cosh|tanh|log|exp|min|max|abs|floor|ceil|round|sign)\b/g, '$1');

  // spațiere latex
  expr = expr.replace(/\\[,;:!]/g, '');
  // orice altă comandă latex necunoscută: păstrează doar litera
  expr = expr.replace(/\\([a-zA-Z]+)/g, '$1');
  // acolade rămase -> paranteze
  expr = expr.replace(/\{/g, '(').replace(/\}/g, ')');

  // înmulțire implicită: cifră urmată de literă sau paranteză
  expr = expr.replace(/(\d)(?=[a-zA-Z(])/g, '$1*');
  // paranteză închisă urmată de cifră/literă/paranteză deschisă
  expr = expr.replace(/\)(?=[\da-zA-Z(])/g, ')*');

  // ln și log -> logaritm natural (Math.log)
  expr = expr.replace(/\bln\b/g, 'log');

  const fnNames = ['asin','acos','atan','sinh','cosh','tanh','sin','cos','tan','sqrt','abs','exp','log','min','max','floor','ceil','round','sign'];
  for (const fn of fnNames) {
    expr = expr.replace(new RegExp('\\b' + fn + '\\b', 'g'), 'Math.' + fn);
  }
  expr = expr.replace(/\bPI\b/g, 'Math.PI');
  expr = expr.replace(/\bE\b/g, 'Math.E');

  return expr;
}

function compileFunctionExpr(raw) {
  const jsExpr = parseMathExpression(raw);
  if (!jsExpr || !/^[0-9a-zA-Z_.+\-*/%(),\s]*$/.test(jsExpr)) {
    throw new Error('Expresie invalidă. Verifică sintaxa.');
  }
  let fn;
  try {
    fn = new Function('x', 'return (' + jsExpr + ');');
  } catch (err) {
    throw new Error('Nu am putut interpreta funcția.');
  }
  return fn;
}

function isTrigExpression(raw) {
  return /\\?(a?rc)?(sin|cos|tan|csc|sec|cot)h?\s*\(/i.test(raw) || /\\(sin|cos|tan|csc|sec|cot)\b/i.test(raw);
}

function gcdInt(a, b) {
  a = Math.abs(a); b = Math.abs(b);
  while (b) { [a, b] = [b, a % b]; }
  return a || 1;
}

function niceNumber(range, round) {
  if (!(range > 0)) return 1;
  const exponent = Math.floor(Math.log10(range));
  const fraction = range / Math.pow(10, exponent);
  let niceFraction;
  if (round) {
    if (fraction < 1.5) niceFraction = 1;
    else if (fraction < 3) niceFraction = 2;
    else if (fraction < 7) niceFraction = 5;
    else niceFraction = 10;
  } else {
    if (fraction <= 1) niceFraction = 1;
    else if (fraction <= 2) niceFraction = 2;
    else if (fraction <= 5) niceFraction = 5;
    else niceFraction = 10;
  }
  return niceFraction * Math.pow(10, exponent);
}

function computeNiceStep(min, max, targetTicks) {
  const range = niceNumber(Math.max(max - min, 1e-9), false);
  return niceNumber(range / Math.max(targetTicks - 1, 1), true);
}

function formatNumber(n) {
  if (Math.abs(n) < 1e-9) return '0';
  const r = Math.round(n * 1000) / 1000;
  if (Number.isInteger(r)) return String(r);
  return String(parseFloat(r.toFixed(3)));
}

function formatPiLabel(val) {
  if (Math.abs(val) < 1e-9) return '0';
  const k = val / Math.PI;
  const denominators = [1, 2, 3, 4, 6];
  for (const d of denominators) {
    const numerator = Math.round(k * d);
    if (Math.abs(k * d - numerator) < 1e-6 && numerator !== 0) {
      const sign = numerator < 0 ? '-' : '';
      const absNum = Math.abs(numerator);
      if (d === 1) return sign + (absNum === 1 ? '' : absNum) + 'π';
      const g = gcdInt(absNum, d);
      const n2 = absNum / g, d2 = d / g;
      return sign + (n2 === 1 ? '' : n2) + 'π/' + d2;
    }
  }
  return formatNumber(val);
}

function plotFunctionOnCanvas(rawExpr, xMin, xMax, strokeColor) {
  const fn = compileFunctionExpr(rawExpr);
  const page = getCurrentPage();
  if (!page) throw new Error('Nu există o pagină activă.');
  if (!(xMax > xMin)) throw new Error('Intervalul de x este invalid.');

  const rect = drawC.getBoundingClientRect();
  const W = rect.width, H = rect.height;
  const marginX = W * 0.10, marginY = H * 0.10;
  const plotW = Math.max(W - marginX * 2, 50);
  const plotH = Math.max(H - marginY * 2, 50);
  const originX = marginX + plotW / 2;
  const originY = marginY + plotH / 2;

  const N = 500;
  const xRange = xMax - xMin;
  const rawPoints = [];
  for (let i = 0; i <= N; i++) {
    const xVal = xMin + (xRange * i) / N;
    let yVal;
    try { yVal = fn(xVal); } catch (e) { yVal = NaN; }
    rawPoints.push({ x: xVal, y: (typeof yVal === 'number' && isFinite(yVal)) ? yVal : NaN });
  }

  const finiteYs = rawPoints.map(p => p.y).filter(y => isFinite(y)).sort((a, b) => a - b);
  if (finiteYs.length === 0) throw new Error('Funcția nu produce valori numerice reale în acest interval.');

  const lo = finiteYs[Math.max(0, Math.floor(finiteYs.length * 0.02))];
  const hi = finiteYs[Math.min(finiteYs.length - 1, Math.ceil(finiteYs.length * 0.98) - 1)];
  let yMin = Math.min(lo, 0);
  let yMax = Math.max(hi, 0);
  if (yMax - yMin < 1e-6) { yMin -= 1; yMax += 1; }
  const yPad = (yMax - yMin) * 0.12;
  yMin -= yPad; yMax += yPad;

  const scaleX = plotW / xRange;
  const scaleY = plotH / (yMax - yMin);
  const xMid = (xMin + xMax) / 2, yMid = (yMin + yMax) / 2;

  function toCanvas(xVal, yVal) {
    return { x: originX + (xVal - xMid) * scaleX, y: originY - (yVal - yMid) * scaleY };
  }

  const hardMin = yMin - (yMax - yMin) * 3;
  const hardMax = yMax + (yMax - yMin) * 3;
  const segments = [];
  let current = [];
  for (const p of rawPoints) {
    if (!isFinite(p.y) || p.y < hardMin || p.y > hardMax) {
      if (current.length > 1) segments.push(current);
      current = [];
      continue;
    }
    current.push(toCanvas(p.x, p.y));
  }
  if (current.length > 1) segments.push(current);
  if (segments.length === 0) throw new Error('Funcția nu produce un grafic vizibil în acest interval.');

  // Poziția reală a axelor Ox (y=0) și Oy (x=0), sau cea mai apropiată margine dacă 0 nu e în interval
  const oxY = (0 >= yMin && 0 <= yMax) ? 0 : (yMin > 0 ? yMin : yMax);
  const oyX = (0 >= xMin && 0 <= xMax) ? 0 : (xMin > 0 ? xMin : xMax);

  const trig = isTrigExpression(rawExpr);
  let xStep;
  if (trig) {
    let step = Math.PI / 2;
    while ((xMax - xMin) / step > 10) step *= 2;
    while ((xMax - xMin) / step < 4) step /= 2;
    xStep = step;
  } else {
    xStep = computeNiceStep(xMin, xMax, 9);
  }
  const yStep = computeNiceStep(yMin, yMax, 8);

  const xTicks = [];
  {
    const start = Math.ceil((xMin - 1e-9) / xStep) * xStep;
    for (let v = start; v <= xMax + xStep * 1e-6; v += xStep) {
      if (Math.abs(v) < xStep * 1e-6) continue; // skip origin, drawn separately
      const p = toCanvas(v, oxY);
      xTicks.push({ x: p.x, y: p.y, label: trig ? formatPiLabel(v) : formatNumber(v) });
    }
  }
  const yTicks = [];
  {
    const start = Math.ceil((yMin - 1e-9) / yStep) * yStep;
    for (let v = start; v <= yMax + yStep * 1e-6; v += yStep) {
      if (Math.abs(v) < yStep * 1e-6) continue;
      const p = toCanvas(oyX, v);
      yTicks.push({ x: p.x, y: p.y, label: formatNumber(v) });
    }
  }

  // Etichete pentru valorile extreme (domeniul pe Ox, codomeniul vizibil pe Oy)
  const extremes = [];
  const pMinX = toCanvas(xMin, oxY), pMaxX = toCanvas(xMax, oxY);
  extremes.push({ x: pMinX.x, y: pMinX.y, label: trig ? formatPiLabel(xMin) : formatNumber(xMin), axis: 'x' });
  extremes.push({ x: pMaxX.x, y: pMaxX.y, label: trig ? formatPiLabel(xMax) : formatNumber(xMax), axis: 'x' });
  const pMinY = toCanvas(oyX, yMin), pMaxY = toCanvas(oyX, yMax);
  extremes.push({ x: pMinY.x, y: pMinY.y, label: formatNumber(yMin), axis: 'y' });
  extremes.push({ x: pMaxY.x, y: pMaxY.y, label: formatNumber(yMax), axis: 'y' });

  const stroke = {
    type: 'function',
    expr: rawExpr,
    color: strokeColor,
    size: 3,
    segments: segments,
    axisColor: '#7a7a7a',
    xAxis: [toCanvas(xMin, oxY), toCanvas(xMax, oxY)],
    yAxis: [toCanvas(oyX, yMin), toCanvas(oyX, yMax)],
    xTicks, yTicks, extremes
  };

  pushStroke(page, stroke);
  redrawStrokes();
  updateStatus();
  showToast(`✓ Grafic desenat: f(x) = ${rawExpr}`);
}

const fnModalBackdrop = document.getElementById('function-modal-backdrop');
const fnExprInput = document.getElementById('fn-expr-input');
const fnXMinInput = document.getElementById('fn-xmin-input');
const fnXMaxInput = document.getElementById('fn-xmax-input');
const fnColorInput = document.getElementById('fn-color-input');
const fnErrorMsg = document.getElementById('fn-error-msg');

function openFunctionModal() {
  fnErrorMsg.textContent = '';
  fnModalBackdrop.classList.add('show');
  setTimeout(() => fnExprInput.focus(), 50);
}

function closeFunctionModal() {
  fnModalBackdrop.classList.remove('show');
}

function submitFunctionModal() {
  fnErrorMsg.textContent = '';
  const rawExpr = fnExprInput.value.trim();
  if (!rawExpr) {
    fnErrorMsg.textContent = 'Scrie o funcție, ex: x^2 - 3x + 2';
    return;
  }
  const xMin = parseFloat(fnXMinInput.value);
  const xMax = parseFloat(fnXMaxInput.value);
  try {
    plotFunctionOnCanvas(rawExpr, xMin, xMax, fnColorInput.value);
    closeFunctionModal();
  } catch (err) {
    fnErrorMsg.textContent = err.message || 'A apărut o eroare la reprezentarea funcției.';
  }
}

document.getElementById('fn-ok-btn').onclick = submitFunctionModal;
document.getElementById('fn-cancel-btn').onclick = closeFunctionModal;
fnModalBackdrop.addEventListener('mousedown', (e) => {
  if (e.target === fnModalBackdrop) closeFunctionModal();
});
fnExprInput.addEventListener('keydown', (e) => {
  if (e.key === 'Enter') { e.preventDefault(); submitFunctionModal(); }
  if (e.key === 'Escape') { e.preventDefault(); closeFunctionModal(); }
});

// ================================================================
// CORPURI GEOMETRICE 3D (Cub, Prisme, Piramide, Cilindru, Con, Sferă...)
// ================================================================

const SOLID_DEG2RAD = Math.PI / 180;
const SOLID_OBLIQUE_ANGLE = 28 * SOLID_DEG2RAD;
const SOLID_OBLIQUE_K = 0.6;

// Proiectează un punct din planul solului (X = stânga-dreapta, Z = adâncime) plus înălțimea Y
// într-un punct 2D (stil desen în perspectivă oblică / cavalieră), folosit pentru toate corpurile.
function solidProjectGP(X, Z, Y) {
  return {
    x: X + Z * SOLID_OBLIQUE_K * Math.cos(SOLID_OBLIQUE_ANGLE),
    y: -Y - Z * SOLID_OBLIQUE_K * Math.sin(SOLID_OBLIQUE_ANGLE)
  };
}

// Proiecție fără forfecare (doar o "turtire" pe verticală a adâncimii, fără deplasare pe orizontală) —
// folosită pentru hexagon, ca să rămână aproape regulat (laturi aproape egale) și fața din față
// să fie un dreptunghi / triunghi isoscel / trapez isoscel curat, la fel ca la corpurile rotunde.
const HEX_SQUASH = 0.85;
function hexProjectGP(X, Z, Y) {
  return { x: X, y: -Y - Z * HEX_SQUASH };
}

// Determină, pentru fiecare muchie a unui poligon (dat prin puncte {x,z}), dacă fața laterală
// corespunzătoare e vizibilă (orientată spre privitor) sau ascunsă (spre spate).
function solidPolygonVisibility(pts) {
  const n = pts.length;
  const cx = pts.reduce((s, p) => s + p.x, 0) / n;
  const cz = pts.reduce((s, p) => s + p.z, 0) / n;
  const vis = [];
  for (let i = 0; i < n; i++) {
    const j = (i + 1) % n;
    let nx = pts[j].z - pts[i].z, nz = -(pts[j].x - pts[i].x);
    const mx = (pts[i].x + pts[j].x) / 2, mz = (pts[i].z + pts[j].z) / 2;
    if (nx * (mx - cx) + nz * (mz - cz) < 0) { nx = -nx; nz = -nz; }
    // O muchie e vizibilă dacă peretele ei "privește" spre spectator (nz < 0, adică spre față).
    // Doar când peretele e exact perpendicular pe adâncime (nz ≈ 0, ca la o cutie axă-aliniată,
    // unde pereții stânga/dreapta au normala pur orizontală) se folosește nx ca rezolvare:
    // convenția standard arată fața dreaptă, nu pe cea stângă.
    const EPS = 1e-6;
    let visible;
    if (nz < -EPS) visible = true;
    else if (nz > EPS) visible = false;
    else visible = nx > 0;
    vis.push(visible);
  }
  return vis;
}

// Construiește muchiile (vizibile/ascunse) pentru o prismă, piramidă sau trunchi de piramidă,
// pornind de la un poligon de bază (basePts), o înălțime și un factor de scalare pentru fața de sus
// (1 = prismă, 0 = piramidă/vârf unic, între 0 și 1 = trunchi de piramidă).
function buildPolygonalSolidLocal(basePts, height, topScale, projectFn) {
  const proj = projectFn || solidProjectGP;
  const n = basePts.length;
  const edgeVis = solidPolygonVisibility(basePts);
  const cx = basePts.reduce((s, p) => s + p.x, 0) / n;
  const cz = basePts.reduce((s, p) => s + p.z, 0) / n;
  const baseScreen = basePts.map(p => proj(p.x, p.z, 0));
  let topScreen = null, apexScreen = null;
  if (topScale === 0) {
    apexScreen = proj(cx, cz, height);
  } else {
    topScreen = basePts.map(p => proj(cx + (p.x - cx) * topScale, cz + (p.z - cz) * topScale, height));
  }
  const visible = [], hidden = [];
  for (let i = 0; i < n; i++) {
    const j = (i + 1) % n;
    (edgeVis[i] ? visible : hidden).push([baseScreen[i], baseScreen[j]]);
  }
  if (topScreen) {
    for (let i = 0; i < n; i++) {
      const j = (i + 1) % n;
      visible.push([topScreen[i], topScreen[j]]);
    }
  }
  for (let i = 0; i < n; i++) {
    const vis = edgeVis[(i - 1 + n) % n] || edgeVis[i];
    const p2 = apexScreen || topScreen[i];
    (vis ? visible : hidden).push([baseScreen[i], p2]);
  }
  return { visible, hidden };
}

function solidRegularNGon(n, R, phaseDeg) {
  const pts = [];
  for (let i = 0; i < n; i++) {
    const t = (phaseDeg + i * 360 / n) * SOLID_DEG2RAD;
    pts.push({ x: R * Math.cos(t), z: R * Math.sin(t) });
  }
  return pts;
}
function solidRectBase(halfW, halfD) {
  return [{ x: -halfW, z: -halfD }, { x: halfW, z: -halfD }, { x: halfW, z: halfD }, { x: -halfW, z: halfD }];
}
function solidTrapezoidBase(w1, w2, d) {
  return [{ x: -w1 / 2, z: -d / 2 }, { x: w1 / 2, z: -d / 2 }, { x: w2 / 2, z: d / 2 }, { x: -w2 / 2, z: d / 2 }];
}
// Triunghi cu muchia din spate perfect orizontală (cele două vârfuri din spate au aceeași adâncime)
// și vârful din față deplasat spre dreapta cu shiftX.
function solidTriangleFrontShift(R, shiftX) {
  const zBack = R * 0.5, xBack = R * Math.cos(30 * SOLID_DEG2RAD);
  return [
    { x: shiftX, z: -R },
    { x: xBack, z: zBack },
    { x: -xBack, z: zBack }
  ];
}
// Hexagon cu cele două vârfuri din față ușor depărtate de centru (nudge), ca muchiile verticale
// laterale ale feței din față să nu cadă exact peste muchiile punctate din spate.
function solidHexagonFrontNudge(R, phaseDeg, nudge) {
  const pts = solidRegularNGon(6, R, phaseDeg);
  pts[0] = { x: pts[0].x * nudge, z: pts[0].z };
  pts[1] = { x: pts[1].x * nudge, z: pts[1].z };
  return pts;
}

// Construiește cilindrul / conul / trunchiul de con (R2 = 0 înseamnă con, cu vârf unic)
function buildRoundSolidLocal(R1, R2, height) {
  const segs = 48;
  const squash = 0.4; // raportul rază-verticală / rază-orizontală al elipselor (ca la sferă)

  function ellipsePts(R, cy) {
    const pts = [];
    for (let i = 0; i <= segs; i++) {
      const t = i / segs * 2 * Math.PI;
      pts.push({ x: R * Math.cos(t), y: cy + R * squash * Math.sin(t) });
    }
    return pts;
  }

  const baseScreen = ellipsePts(R1, 0);
  const visible = [], hidden = [];
  for (let i = 0; i < segs; i++) {
    const my = (baseScreen[i].y + baseScreen[i + 1].y) / 2;
    (my > 0 ? visible : hidden).push([baseScreen[i], baseScreen[i + 1]]);
  }

  let topScreen = null, apexScreen = null;
  if (R2 > 0) {
    topScreen = ellipsePts(R2, -height);
    for (let i = 0; i < segs; i++) {
      const my = (topScreen[i].y + topScreen[i + 1].y) / 2;
      (my > -height ? visible : hidden).push([topScreen[i], topScreen[i + 1]]);
    }
  } else {
    apexScreen = { x: 0, y: -height };
  }

  const leftIdx = Math.round(segs / 2), rightIdx = 0;
  const leftTop = topScreen ? topScreen[leftIdx] : apexScreen;
  const rightTop = topScreen ? topScreen[rightIdx] : apexScreen;
  visible.push([baseScreen[leftIdx], leftTop]);
  visible.push([baseScreen[rightIdx], rightTop]);
  // Linia diametrului (secțiunea axială): jos, cu linie întreruptă (trece prin interiorul corpului);
  // sus rămâne plină, dacă există o față superioară plană (cilindru / trunchi de con).
  hidden.push([baseScreen[rightIdx], baseScreen[leftIdx]]);
  if (topScreen) visible.push([topScreen[rightIdx], topScreen[leftIdx]]);
  return { visible, hidden };
}

// Construiește sfera: un cerc exterior (mereu vizibil) + o elipsă "ecuator" (parțial ascunsă)
function buildSphereLocal(R) {
  const segs = 48;
  const outer = [];
  for (let i = 0; i <= segs; i++) {
    const t = i / segs * 2 * Math.PI;
    outer.push({ x: R * Math.cos(t), y: R * Math.sin(t) });
  }
  const visible = [];
  for (let i = 0; i < segs; i++) visible.push([outer[i], outer[i + 1]]);
  const hidden = [];
  const ry = R * 0.45;
  const eq = [];
  for (let i = 0; i <= segs; i++) {
    const t = i / segs * 2 * Math.PI;
    eq.push({ x: R * Math.cos(t), y: ry * Math.sin(t) });
  }
  for (let i = 0; i < segs; i++) {
    const seg = [eq[i], eq[i + 1]];
    (((eq[i].y + eq[i + 1].y) / 2) > 0 ? visible : hidden).push(seg);
  }
  // Diametrul sferei, cu linie întreruptă (trece prin interior).
  hidden.push([{ x: -R, y: 0 }, { x: R, y: 0 }]);
  return { visible, hidden };
}

const SOLID_SHAPES = {
  cub: { label: 'Cub', build: () => buildPolygonalSolidLocal(solidRectBase(55, 55), 110, 1) },
  paralelipiped: { label: 'Paralelipiped dreptunghic', build: () => buildPolygonalSolidLocal(solidRectBase(75, 45), 90, 1) },
  prismaTriunghiulara: { label: 'Prismă triunghiulară', build: () => buildPolygonalSolidLocal(solidTriangleFrontShift(65, 28), 110, 1) },
  prismaPatrulatera: { label: 'Prismă patrulateră', build: () => buildPolygonalSolidLocal(solidRectBase(60, 60), 130, 1) },
  prismaHexagonala: { label: 'Prismă hexagonală', build: () => buildPolygonalSolidLocal(solidHexagonFrontNudge(60, 240, 1.18), 100, 1, hexProjectGP) },
  piramidaTriunghiulara: { label: 'Piramidă triunghiulară', build: () => buildPolygonalSolidLocal(solidTriangleFrontShift(65, 28), 120, 0) },
  piramidaPatrulatera: { label: 'Piramidă patrulateră', build: () => buildPolygonalSolidLocal(solidRectBase(65, 65), 130, 0) },
  piramidaHexagonala: { label: 'Piramidă hexagonală', build: () => buildPolygonalSolidLocal(solidRegularNGon(6, 60, 240), 130, 0, hexProjectGP) },
  trunchiPiramidaTriunghiulara: { label: 'Trunchiul de piramidă triunghiulară', build: () => buildPolygonalSolidLocal(solidTriangleFrontShift(65, 28), 95, 0.5) },
  trunchiPiramidaPatrulatera: { label: 'Trunchiul de piramidă patrulateră', build: () => buildPolygonalSolidLocal(solidRectBase(70, 70), 95, 0.5) },
  trunchiPiramidaHexagonala: { label: 'Trunchiul de piramidă hexagonală', build: () => buildPolygonalSolidLocal(solidRegularNGon(6, 60, 240), 95, 0.5, hexProjectGP) },
  cilindru: { label: 'Cilindru', build: () => buildRoundSolidLocal(60, 60, 110) },
  con: { label: 'Con', build: () => buildRoundSolidLocal(60, 0, 125) },
  trunchiCon: { label: 'Trunchiul de con', build: () => buildRoundSolidLocal(65, 32, 100) },
  sfera: { label: 'Sferă', build: () => buildSphereLocal(65) }
};

// Randează un mic SVG-pictogramă pentru o formă, refolosind exact aceeași geometrie ca desenul real.
function buildShapeIconSVG(shapeKey, size) {
  const spec = SOLID_SHAPES[shapeKey];
  const built = spec.build();
  const allPts = [];
  built.visible.forEach(s => allPts.push(...s));
  built.hidden.forEach(s => allPts.push(...s));
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  allPts.forEach(p => {
    if (p.x < minX) minX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x;
    if (p.y > maxY) maxY = p.y;
  });
  const w = (maxX - minX) || 1, h = (maxY - minY) || 1;
  const pad = 2;
  const scale = Math.min((size - 2 * pad) / w, (size - 2 * pad) / h);
  const offX = pad - minX * scale + (size - 2 * pad - w * scale) / 2;
  const offY = pad - minY * scale + (size - 2 * pad - h * scale) / 2;
  const tp = p => ({ x: p.x * scale + offX, y: p.y * scale + offY });
  let lines = '';
  built.hidden.forEach(seg => {
    const a = tp(seg[0]), b = tp(seg[1]);
    lines += `<line x1="${a.x.toFixed(1)}" y1="${a.y.toFixed(1)}" x2="${b.x.toFixed(1)}" y2="${b.y.toFixed(1)}" stroke-dasharray="3,2.4" stroke-width="1" opacity="0.55"/>`;
  });
  built.visible.forEach(seg => {
    const a = tp(seg[0]), b = tp(seg[1]);
    lines += `<line x1="${a.x.toFixed(1)}" y1="${a.y.toFixed(1)}" x2="${b.x.toFixed(1)}" y2="${b.y.toFixed(1)}"/>`;
  });
  return `<svg width="${size}" height="${size}" viewBox="0 0 ${size} ${size}" fill="none" stroke="currentColor" stroke-width="1.3" stroke-linecap="round">${lines}</svg>`;
}

function insertSolidShape(shapeKey) {
  const spec = SOLID_SHAPES[shapeKey];
  if (!spec) return;
  const page = getCurrentPage();
  if (!page) return;

  const built = spec.build();
  const allPts = [];
  built.visible.forEach(s => allPts.push(...s));
  built.hidden.forEach(s => allPts.push(...s));
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  allPts.forEach(p => {
    if (p.x < minX) minX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x;
    if (p.y > maxY) maxY = p.y;
  });
  const rect = drawC.getBoundingClientRect();
  const cx = rect.width / 2, cy = rect.height * 0.28;
  const offX = cx - (minX + maxX) / 2, offY = cy - (minY + maxY) / 2;
  const shift = seg => seg.map(p => ({ x: p.x + offX, y: p.y + offY }));

  const stroke = {
    type: 'solid3d',
    shape: shapeKey,
    color: color,
    size: 2.4,
    visible: built.visible.map(shift),
    hidden: built.hidden.map(shift)
  };

  pushStroke(page, stroke);
  setTool('select');
  selectedStrokes = new Set([page.strokes.length - 1]);
  selectedImages.clear();
  updateImageSelection();
  redrawStrokes();
  drawSelectionHighlights();
  updateStatus();
  showToast(`✓ ${spec.label} — selectat(ă), trage pentru a muta sau scala`);
}

// Dialog de confirmare propriu — window.confirm() nativ forțează browserul să iasă din
// modul fullscreen; acesta rămâne în pagină, deci nu întrerupe fullscreen-ul.
const confirmModalBackdrop = document.getElementById('confirm-modal-backdrop');
const confirmModalMsg = document.getElementById('confirm-modal-msg');
const confirmModalOk = document.getElementById('confirm-modal-ok');
const confirmModalCancel = document.getElementById('confirm-modal-cancel');
let confirmModalResolve = null;
function customConfirm(message) {
  return new Promise(resolve => {
    confirmModalResolve = resolve;
    confirmModalMsg.textContent = message;
    confirmModalBackdrop.classList.add('show');
  });
}
function closeConfirmModal(result) {
  confirmModalBackdrop.classList.remove('show');
  if (confirmModalResolve) { confirmModalResolve(result); confirmModalResolve = null; }
}
confirmModalOk.onclick = () => closeConfirmModal(true);
confirmModalCancel.onclick = () => closeConfirmModal(false);
confirmModalBackdrop.addEventListener('mousedown', (e) => {
  if (e.target === confirmModalBackdrop) closeConfirmModal(false);
});

const solidsMenuEl = document.getElementById('solids-menu');
const btnSolids = document.getElementById('btn-solids');
btnSolids.innerHTML = buildShapeIconSVG('cub', 20);

solidsMenuEl.innerHTML = Object.keys(SOLID_SHAPES).map(key => {
  const spec = SOLID_SHAPES[key];
  const icon = buildShapeIconSVG(key, 22);
  return `<div class="solids-menu-item" data-shape="${key}">${icon}<span>${spec.label}</span></div>`;
}).join('');

function toggleSolidsMenu() {
  if (solidsMenuEl.classList.contains('show')) {
    closeSolidsMenu();
    return;
  }
  const r = btnSolids.getBoundingClientRect();
  solidsMenuEl.style.left = Math.round(r.left) + 'px';
  solidsMenuEl.style.top = Math.round(r.bottom + 6) + 'px';
  solidsMenuEl.classList.add('show');
}
function closeSolidsMenu() {
  solidsMenuEl.classList.remove('show');
}
btnSolids.onclick = (e) => { e.stopPropagation(); toggleSolidsMenu(); };
solidsMenuEl.querySelectorAll('.solids-menu-item').forEach(item => {
  item.onclick = () => {
    insertSolidShape(item.dataset.shape);
    closeSolidsMenu();
  };
});
document.addEventListener('pointerdown', (e) => {
  if (solidsMenuEl.classList.contains('show') && !solidsMenuEl.contains(e.target) && e.target !== btnSolids && !btnSolids.contains(e.target)) {
    closeSolidsMenu();
  }
});

// ================================================================
// EVENT LISTENERS BUTOANE
// ================================================================


document.getElementById('btn-pen').onclick = () => setTool('pen');
document.getElementById('btn-line').onclick = () => setTool('line');
document.getElementById('btn-dashed').onclick = () => setTool('dashed');
document.getElementById('btn-arrow').onclick = () => setTool('arrow');
document.getElementById('btn-circle').onclick = () => setTool('circle');
document.getElementById('btn-rect').onclick = () => setTool('rect');
document.getElementById('btn-polygon').onclick = () => setTool('polygon');
document.getElementById('btn-finish-polygon').onclick = () => {
  finalizePolygon();
};
document.getElementById('btn-erase').onclick = () => setTool('erase');
document.getElementById('btn-text').onclick = () => setTool('text');
document.getElementById('btn-function').onclick = () => openFunctionModal();
document.getElementById('btn-midpoint').onclick = () => setTool('midpoint');
document.getElementById('btn-select').onclick = () => setTool('select');
document.getElementById('btn-multiselect').onclick = () => {
  multiSelectMode = !multiSelectMode;
  document.getElementById('btn-multiselect').classList.toggle('active', multiSelectMode);
  showToast(multiSelectMode ? '✓ Selecție multiplă activă (fiecare atingere adaugă la selecție)' : 'Selecție multiplă dezactivată');
};
document.getElementById('btn-compass').onclick = () => toggleGeoGuide('compass', 'btn-compass');
document.getElementById('btn-prev-page').onclick = () => { prevPage(); };
document.getElementById('btn-next-page').onclick = () => { nextPage(); };
document.getElementById('btn-del-page').onclick = () => { deletePage(); };
document.getElementById('color-pick').oninput = e => color = e.target.value;
document.getElementById('size-minus').onclick = () => setCurrentSize(getCurrentSize() - 1);
document.getElementById('size-plus').onclick = () => setCurrentSize(getCurrentSize() + 1);

document.getElementById('color-red').onclick = () => setColorFromButton('#ff0000', 'color-red');
document.getElementById('color-green').onclick = () => setColorFromButton('#2ecc71', 'color-green');
document.getElementById('color-blue').onclick = () => setColorFromButton('#3498db', 'color-blue');
document.getElementById('color-purple').onclick = () => setColorFromButton('#9b59b6', 'color-purple');
document.getElementById('color-yellow').onclick = () => setColorFromButton('#f1c40f', 'color-yellow');
document.getElementById('color-black').onclick = () => setColorFromButton('#000000', 'color-black');
document.getElementById('color-white').onclick = () => setColorFromButton('#ffffff', 'color-white');
document.getElementById('color-white').classList.add('active-color');
color = '#ffffff';

document.getElementById('bg-white').onclick = () => setBackgroundColor('#ffffff', 'bg-white');
document.getElementById('bg-black').onclick = () => setBackgroundColor('#000000', 'bg-black');
document.getElementById('bg-gray').onclick = () => setBackgroundColor('#808080', 'bg-gray');
document.getElementById('bg-lightgray').onclick = () => setBackgroundColor('#d3d3d3', 'bg-lightgray');
document.getElementById('bg-beige').onclick = () => setBackgroundColor('#f5f5dc', 'bg-beige');
document.getElementById('bg-blue').onclick = () => setBackgroundColor('#add8e6', 'bg-blue');
document.getElementById('bg-green').onclick = () => setBackgroundColor('#90ee90', 'bg-green');

document.getElementById('btn-upload').onclick = () => document.getElementById('file-input').click();
document.getElementById('file-input').onchange = e => {
  const f = e.target.files[0];
  if (!f) return;
  const img = new Image();
  img.onload = () => {
    const page = getCurrentPage();
    const maxW = wrap.clientWidth * 0.7;
    const maxH = wrap.clientHeight * 0.6;
    let w = img.naturalWidth * 1.5;
    let h = img.naturalHeight * 1.5;
    if (w > maxW) { h = h * maxW / w; w = maxW; }
    if (h > maxH) { w = w * maxH / h; h = maxH; }
    addImageToPage(page, img, 40, 40, w, h);
    const imgData = page.images[page.images.length - 1];
    undoStack.push({ type: 'imageAdd', page, img: imgData });
    redoStack = [];
    setTool('select');
    selectedImages.clear();
    selectedImages.add(imgData.id);
    updateImageSelection();
    updateStatus();
    showSelectionInfo('🖼 Imagine încărcată - trage colțul pentru redimensionare (Delete pentru ștergere)');
    showToast('✓ Imagine încărcată');
  };
  img.src = URL.createObjectURL(f);
  e.target.value = '';
};

document.getElementById('btn-upload-multi').onclick = () => {
  document.getElementById('file-input-multi').click();
};
document.getElementById('file-input-multi').onchange = e => {
  loadMultipleImages(e.target.files);
  e.target.value = ''; 
};

let pasteOffsetCount = 0;
let pasteOffsetResetTimer = null;

document.addEventListener('paste', (e) => {
  if (e.target && e.target.matches('input, textarea')) return;

  const items = e.clipboardData && e.clipboardData.items;
  if (!items) return;

  let imageFile = null;
  for (const item of items) {
    if (item.kind === 'file' && item.type.startsWith('image/')) {
      imageFile = item.getAsFile();
      break;
    }
  }
  if (!imageFile) return;

  e.preventDefault();

  const img = new Image();
  img.onload = () => {
    const maxW = wrap.clientWidth * 0.7;
    const maxH = wrap.clientHeight * 0.6;
    let w = img.naturalWidth;
    let h = img.naturalHeight;
    if (w > maxW) { h = h * maxW / w; w = maxW; }
    if (h > maxH) { w = w * maxH / h; h = maxH; }

    clearTimeout(pasteOffsetResetTimer);
    pasteOffsetResetTimer = setTimeout(() => { pasteOffsetCount = 0; }, 4000);
    const offset = (pasteOffsetCount % 8) * 28;
    pasteOffsetCount++;

    const x = Math.max(20, (wrap.clientWidth - w) / 2) + offset;
    const y = Math.max(20, (wrap.clientHeight - h) / 2) + offset;

    const page = getCurrentPage();
    const id = addImageToPage(page, img, x, y, w, h);
    const imgData = page.images[page.images.length - 1];

    undoStack.push({ type: 'imageAdd', page, img: imgData });
    redoStack = [];

    setTool('select');
    selectedImages.clear();
    selectedImages.add(id);
    updateImageSelection();
    updateStatus();
    showSelectionInfo('🖼 Imagine lipită - trage colțul pentru redimensionare (Delete pentru ștergere)');
    showToast('✓ Imagine din clipboard adăugată');
  };
  img.src = URL.createObjectURL(imageFile);
});

document.getElementById('btn-undo').onclick = () => {
  if (undoStack.length === 0) return;
  const action = undoStack.pop();
  const page = action.page;

  if (action.type === 'draw') {
    const idx = page.strokes.lastIndexOf(action.stroke);
    if (idx !== -1) page.strokes.splice(idx, 1);
  } else if (action.type === 'delete') {
    for (const item of action.items) {
      page.strokes.splice(item.index, 0, item.stroke);
    }
  } else if (action.type === 'move') {
    for (const item of action.items) {
      restoreStrokePosition(item.stroke, item.before);
    }
  } else if (action.type === 'resizeStroke') {
    Object.assign(action.stroke, action.before);
  } else if (action.type === 'imageMove') {
    for (const item of action.items) {
      item.img.x = item.before.x;
      item.img.y = item.before.y;
    }
  } else if (action.type === 'imageResize') {
    action.item.img.w = action.item.before.w;
    action.item.img.h = action.item.before.h;
  } else if (action.type === 'imageDelete') {
    for (const item of action.items) {
      page.images.splice(item.index, 0, item.img);
    }
  } else if (action.type === 'imageAdd') {
    const idx = page.images.indexOf(action.img);
    if (idx !== -1) page.images.splice(idx, 1);
    selectedImages.delete(action.img.id);
  } else if (action.type === 'imageReorder') {
    page.images = action.beforeOrder.slice();
  }

  redoStack.push(action);
  if (page === getCurrentPage()) {
    redrawStrokes(); updateStatus();
        drawSelectionHighlights();
    renderImages();
  }
};

document.getElementById('btn-redo').onclick = () => {
  if (redoStack.length === 0) return;
  const action = redoStack.pop();
  const page = action.page;

  if (action.type === 'draw') {
    page.strokes.push(action.stroke);
  } else if (action.type === 'delete') {
    const sorted = [...action.items].sort((a, b) => b.index - a.index);
    for (const item of sorted) {
      const idx = page.strokes.indexOf(item.stroke);
      if (idx !== -1) page.strokes.splice(idx, 1);
    }
  } else if (action.type === 'move') {
    for (const item of action.items) {
      restoreStrokePosition(item.stroke, item.after);
    }
  } else if (action.type === 'resizeStroke') {
    Object.assign(action.stroke, action.after);
  } else if (action.type === 'imageMove') {
    for (const item of action.items) {
      item.img.x = item.after.x;
      item.img.y = item.after.y;
    }
  } else if (action.type === 'imageResize') {
    action.item.img.w = action.item.after.w;
    action.item.img.h = action.item.after.h;
  } else if (action.type === 'imageDelete') {
    const sorted = [...action.items].sort((a, b) => b.index - a.index);
    for (const item of sorted) {
      const idx = page.images.indexOf(item.img);
      if (idx !== -1) page.images.splice(idx, 1);
    }
  } else if (action.type === 'imageAdd') {
    if (page.images.indexOf(action.img) === -1) page.images.push(action.img);
  } else if (action.type === 'imageReorder') {
    page.images = action.afterOrder.slice();
  }

  undoStack.push(action);
  if (page === getCurrentPage()) {
    redrawStrokes(); updateStatus();
        drawSelectionHighlights();
    renderImages();
  }
};

document.getElementById('btn-clear').onclick = async () => {
  if (await customConfirm('Ștergi complet pagina?')) {
    const p = getCurrentPage();
    p.strokes = []; p.images = [];
    undoStack = undoStack.filter(a => a.page !== p);
    redoStack = redoStack.filter(a => a.page !== p);
    selectedStrokes.clear();
    selectedImages.clear();
    updateImageSelection();
    hideSelectionInfo();
    drawBg(); redrawStrokes(); renderImages(); updateStatus();
  }
};

document.getElementById('btn-pdf').onclick = () => {
  const { jsPDF } = window.jspdf;
  const doc = new jsPDF('l', 'px', [bgC.width / DPR, bgC.height / DPR]);
  
  pages.forEach((page, index) => {
    if (index > 0) doc.addPage();
    
    const tempC = document.createElement('canvas');
    tempC.width = bgC.width; tempC.height = bgC.height;
    const tCtx = tempC.getContext('2d');
    tCtx.scale(DPR, DPR);
    
    tCtx.fillStyle = bgColor;
    tCtx.fillRect(0, 0, bgC.width/DPR, bgC.height/DPR);
    
    page.images.forEach(img => {
      tCtx.drawImage(img.img, img.x, img.y, img.w, img.h);
    });
    
    page.strokes.forEach(s => drawStrokeOn(tCtx, s));
    
    const dataUrl = tempC.toDataURL('image/png');
    doc.addImage(dataUrl, 'PNG', 0, 0, bgC.width/DPR, bgC.height/DPR);
  });
  
  doc.save('whiteboard.pdf');
};

async function saveSession() {

  const pagesData = await Promise.all(pages.map(async (page) => {
    const imagesData = await Promise.all(page.images.map(async (imgData) => {
      let dataUrl = imgData.dataUrl;
      if (!dataUrl && imgData.img) {
        try {
          const canvas = document.createElement('canvas');
          canvas.width = imgData.img.naturalWidth || imgData.img.width;
          canvas.height = imgData.img.naturalHeight || imgData.img.height;
          canvas.getContext('2d').drawImage(imgData.img, 0, 0);
          dataUrl = canvas.toDataURL('image/png');
        } catch(e) {}
      }
      return {
        id: imgData.id,
        x: imgData.x,
        y: imgData.y,
        w: imgData.w,
        h: imgData.h,
        locked: !!imgData.locked,
        dataUrl: dataUrl
      };
    }));
    
    return {
      strokes: page.strokes,
      images: imagesData
    };
  }));

  const sessionData = {
    version: 2,
    savedAt: new Date().toISOString(),
    currentPageIdx,
    pages: pagesData,
    bgColor: bgColor,
    imageIdCounter: imageIdCounter
  };

  const json = JSON.stringify(sessionData);
  const blob = new Blob([json], { type: 'application/json' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  const ts = new Date().toISOString().slice(0,19).replace('T','_').replace(/:/g,'-');
  a.download = `whiteboard_${ts}.wbs`;
  a.click();
  URL.revokeObjectURL(a.href);
  showToast('✓ Sesiunea a fost salvată!');
}

function loadSession(file) {
  if (!file) return;
  const reader = new FileReader();
  reader.onload = async (e) => {
    try {
      const data = JSON.parse(e.target.result);
      if (!data.version || !Array.isArray(data.pages)) throw new Error('Format invalid');

      const newPages = await Promise.all(data.pages.map((pd) => {
        return new Promise((resolve) => {
          const page = {
            strokes: pd.strokes || [],
            images: []
          };
          
          const loadImages = pd.images ? pd.images.map((imgData) => {
            return new Promise((res) => {
              if (imgData.dataUrl) {
                const img = new Image();
                img.onload = () => {
                  page.images.push({
                    id: imgData.id,
                    img: img,
                    x: imgData.x || 40,
                    y: imgData.y || 40,
                    w: imgData.w || 200,
                    h: imgData.h || 150,
                    locked: !!imgData.locked,
                    dataUrl: imgData.dataUrl
                  });
                  res();
                };
                img.onerror = () => res();
                img.src = imgData.dataUrl;
              } else {
                res();
              }
            });
          }) : [];
          
          Promise.all(loadImages).then(() => resolve(page));
        });
      }));

      pages = newPages;
      currentPageIdx = Math.min(data.currentPageIdx ?? 0, pages.length - 1);
      if (data.imageIdCounter) imageIdCounter = data.imageIdCounter;
      
      if (data.bgColor) {
        bgColor = data.bgColor;
        document.querySelectorAll('.bg-color-btn').forEach(b => b.classList.remove('active-bg'));
        const btnMap = {
          '#ffffff': 'bg-white',
          '#000000': 'bg-black',
          '#808080': 'bg-gray',
          '#d3d3d3': 'bg-lightgray',
          '#f5f5dc': 'bg-beige',
          '#add8e6': 'bg-blue',
          '#90ee90': 'bg-green'
        };
        if (btnMap[bgColor]) {
          document.getElementById(btnMap[bgColor]).classList.add('active-bg');
        }
      }
      
      selectedStrokes.clear();
      selectedImages.clear();
      updateImageSelection();
      hideSelectionInfo();
      
      drawBg();
      redrawStrokes();
      renderImages();
      updateStatus();
      showToast(`✓ Sesiunea a fost restaurată! (${pages.length} pagini, ${imageIdCounter} imagini)`);
    } catch(err) {
      showToast('⚠ Fișier invalid sau corupt.', 4000);
    }
  };
  reader.readAsText(file);
}

document.getElementById('btn-save-session').onclick = saveSession;
document.getElementById('btn-load-session').onclick = () => {
  document.getElementById('session-file-input').click();
};
document.getElementById('session-file-input').onchange = e => {
  loadSession(e.target.files[0]);
  e.target.value = '';
};

// ================================================================
// KEYBOARD SHORTCUTS
// ================================================================

document.addEventListener('keydown', e => {
  if (e.target && e.target.matches && e.target.matches('input, textarea')) {
    if (e.target === txtArea && e.ctrlKey && e.key === 'Enter') {
      e.preventDefault();
      commitText();
    }
    return;
  }

  if (e.key === 'ArrowLeft') { e.preventDefault(); prevPage(); return; }
  if (e.key === 'ArrowRight') { e.preventDefault(); nextPage(); return; }
  
  if (e.key === 'Escape') {
    selectedStrokes.clear();
    selectedImages.clear();
    updateImageSelection();
    hideSelectionInfo();
    drawSelectionHighlights();
    updateStatus();
  }
  
  if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
    e.preventDefault();
    document.getElementById('btn-undo').click();
  }
  
  if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'y') {
    e.preventDefault();
    document.getElementById('btn-redo').click();
  }
});

// ================================================================
// FULLSCREEN
// ================================================================

const btnFs = document.getElementById('btn-fullscreen');

function updateFsButton() {
  const isFs = !!document.fullscreenElement;
  btnFs.classList.toggle('active', isFs);
  btnFs.innerHTML = isFs
    ? '<i class="ti ti-minimize"></i>'
    : '<i class="ti ti-maximize"></i>';
  btnFs.title = isFs ? 'Ieși din ecran complet (Esc)' : 'Ecran complet (F11)';
}

btnFs.addEventListener('click', () => {
  if (!document.fullscreenElement) {
    document.documentElement.requestFullscreen().catch(() => {});
  } else {
    document.exitFullscreen().catch(() => {});
  }
});

document.addEventListener('fullscreenchange', () => {
  updateFsButton();
  setTimeout(initCanvas, 80);
});

let resizeDebounceTimer = null;
window.addEventListener('resize', () => {
  clearTimeout(resizeDebounceTimer);
  resizeDebounceTimer = setTimeout(initCanvas, 150);
});

// ================================================================
// INSTRUMENTE GEOMETRICE: RIGLĂ, ECHER, RAPORTOR, COMPAS
// ================================================================

const guideSvg = document.getElementById('guide-svg');
const GUIDE_SNAP_DIST = 14;
const PX_PER_CM = 50;
const PX_PER_MM = PX_PER_CM / 10;
const GEO_PEN_CURSOR = `url("data:image/svg+xml;utf8,${encodeURIComponent(
  '<svg xmlns="http://www.w3.org/2000/svg" width="26" height="26" viewBox="0 0 26 26">' +
  '<g transform="rotate(45 13 13)">' +
  '<rect x="11" y="2" width="4" height="15" fill="#ffb300" stroke="#333" stroke-width="1"/>' +
  '<polygon points="11,17 15,17 13,24" fill="#5c3b1e" stroke="#333" stroke-width="1"/>' +
  '<rect x="11" y="1" width="4" height="3" fill="#c0392b" stroke="#333" stroke-width="1"/>' +
  '</g></svg>'
)}") 4 22, crosshair`;

let lastSnapGuideName = null;
const geoGuides = {
  ruler:      { visible: false, x: 160, y: 160, angle: 0,             length: 700, thickness: 50 },
  setsquare:  { visible: false, x: 520, y: 560, angle: 0,             size: 420 },
  protractor: { visible: false, x: 360, y: 600, angle: 0,             radius: 260, arcAngle: 60, arcRadiusScale: 0.45 },
  compass:    { visible: false, x: 520, y: 380, angle: -Math.PI * 0.65, radius: 160 }
};

function geoEl(tag, attrs) {
  const n = document.createElementNS('http://www.w3.org/2000/svg', tag);
  for (const k in attrs) n.setAttribute(k, attrs[k]);
  return n;
}
function geoClear(node) { while (node.firstChild) node.removeChild(node.firstChild); }

const geoGroups = {};

// ---------------- RIGLĂ ----------------
function buildGeoRuler() {
  const g = geoEl('g', { class: 'guide', id: 'guide-ruler' });
  const body = geoEl('rect', { class: 'guide-body',
    fill: 'rgba(255,255,255,0.55)', stroke: 'rgba(0,85,204,0.8)', 'stroke-width': 1.5 });
  g.appendChild(body);
  const ticks = geoEl('g', { class: 'guide-ticks' });
  g.appendChild(ticks);
  const rotateHandle = geoEl('circle', { class: 'guide-handle', r: 10,
    fill: '#0055cc', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(rotateHandle);
  const resizeHandle = geoEl('rect', { class: 'guide-handle', width: 16, height: 16, rx: 3,
    fill: '#e67e00', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(resizeHandle);
  guideSvg.appendChild(g);
  geoGroups.ruler = { g, body, ticks, rotateHandle, resizeHandle };
  renderGeoRuler();
}

function renderGeoRuler() {
  const st = geoGuides.ruler;
  const { body, ticks, rotateHandle, resizeHandle } = geoGroups.ruler;
  const L = st.length, T = st.thickness;
  body.setAttribute('x', 0); body.setAttribute('y', 0);
  body.setAttribute('width', L); body.setAttribute('height', T);

  geoClear(ticks);
  const totalMM = Math.round(L / PX_PER_MM);
  for (let mm = 0; mm <= totalMM; mm++) {
    const x = mm * PX_PER_MM;
    const isCM = mm % 10 === 0;
    const isHalf = mm % 5 === 0;
    const tickH = isCM ? T * 0.55 : (isHalf ? T * 0.38 : T * 0.2);
    ticks.appendChild(geoEl('line', { x1: x, y1: 0, x2: x, y2: tickH,
      stroke: 'rgba(20,20,20,0.7)', 'stroke-width': isCM ? 1.6 : (isHalf ? 1.1 : 0.7) }));
    if (isCM && mm > 0) {
      const t = geoEl('text', { class: 'guide-label', x: x - 4, y: T - 8 });
      t.textContent = mm / 10;
      ticks.appendChild(t);
    }
  }
  rotateHandle.setAttribute('cx', 26);
  rotateHandle.setAttribute('cy', T / 2);
  resizeHandle.setAttribute('x', L - 8);
  resizeHandle.setAttribute('y', T / 2 - 8);
}

// ---------------- ECHER ----------------
function buildGeoSetsquare() {
  const g = geoEl('g', { class: 'guide', id: 'guide-setsquare' });
  const body = geoEl('polygon', { class: 'guide-body',
    fill: 'rgba(255,255,255,0.55)', stroke: 'rgba(0,85,204,0.8)', 'stroke-width': 1.5 });
  g.appendChild(body);
  const ticks = geoEl('g', { class: 'guide-ticks' });
  g.appendChild(ticks);
  const rotateHandle = geoEl('circle', { class: 'guide-handle', r: 10,
    fill: '#0055cc', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(rotateHandle);
  const resizeHandle = geoEl('rect', { class: 'guide-handle', width: 16, height: 16, rx: 3,
    fill: '#e67e00', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(resizeHandle);
  guideSvg.appendChild(g);
  geoGroups.setsquare = { g, body, ticks, rotateHandle, resizeHandle };
  renderGeoSetsquare();
}

function renderGeoSetsquare() {
  const st = geoGuides.setsquare;
  const { body, ticks, rotateHandle, resizeHandle } = geoGroups.setsquare;
  const S = st.size;
  body.setAttribute('points', `0,0 ${S},0 0,${-S}`);

  geoClear(ticks);
  const totalMM = Math.round(S / PX_PER_MM);
  for (let mm = 0; mm <= totalMM; mm++) {
    const d = mm * PX_PER_MM;
    const isCM = mm % 10 === 0;
    const isHalf = mm % 5 === 0;
    const tickLen = isCM ? 16 : (isHalf ? 11 : 6);
    const sw = isCM ? 1.6 : (isHalf ? 1.1 : 0.7);
    ticks.appendChild(geoEl('line', { x1: d, y1: 0, x2: d, y2: -tickLen, stroke: 'rgba(20,20,20,0.65)', 'stroke-width': sw }));
    ticks.appendChild(geoEl('line', { x1: 0, y1: -d, x2: tickLen, y2: -d, stroke: 'rgba(20,20,20,0.65)', 'stroke-width': sw }));
    if (isCM && mm > 0) {
      const t1 = geoEl('text', { class: 'guide-label', x: d - 4, y: -6 });
      t1.textContent = mm / 10;
      ticks.appendChild(t1);
      const t2 = geoEl('text', { class: 'guide-label', x: 4, y: -d - 3 });
      t2.textContent = mm / 10;
      ticks.appendChild(t2);
    }
  }
  rotateHandle.setAttribute('cx', 24);
  rotateHandle.setAttribute('cy', -24);
  resizeHandle.setAttribute('x', S - 8);
  resizeHandle.setAttribute('y', -8);
}

// ---------------- RAPORTOR ----------------
function buildGeoProtractor() {
  const g = geoEl('g', { class: 'guide', id: 'guide-protractor' });

  const body = geoEl('path', { class: 'guide-body', 'fill-rule': 'evenodd',
    fill: 'rgba(255,255,255,0.55)', stroke: 'rgba(0,85,204,0.85)', 'stroke-width': 1.5 });
  g.appendChild(body);

  const spokes = geoEl('g', { class: 'guide-ticks', stroke: 'rgba(0,85,204,0.28)', 'stroke-width': 0.8 });
  g.appendChild(spokes);

  const ticks = geoEl('g', { class: 'guide-ticks' });
  g.appendChild(ticks);

  const notch = geoEl('path', { fill: 'none', stroke: 'rgba(0,85,204,0.85)', 'stroke-width': 1.3 });
  g.appendChild(notch);

  const centerHole = geoEl('circle', { cx: 0, cy: 0, r: 16, fill: 'rgba(255,255,255,0)', stroke: 'none' });
  g.appendChild(centerHole);
  
  const vertexDot = geoEl('circle', { cx: 0, cy: 0, r: 4, fill: 'rgba(255,255,255,0)', stroke: '#e63946', 'stroke-width': 1.5 });
  g.appendChild(vertexDot);

  const rotateHandle = geoEl('circle', { class: 'guide-handle', r: 10,
    fill: '#0055cc', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(rotateHandle);

  const resizeHandle = geoEl('rect', { class: 'guide-handle', width: 16, height: 16, rx: 3,
    fill: '#e67e00', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(resizeHandle);

  const arcMark = geoEl('path', { fill: 'none', stroke: '#2d9d4f', 'stroke-width': 2,
    'stroke-dasharray': '5,4', 'pointer-events': 'none' });
  g.appendChild(arcMark);

  const arcLabel = geoEl('text', { class: 'guide-label', 'font-weight': 'bold', fill: '#2d9d4f', 'font-size': '12' });
  g.appendChild(arcLabel);

  const arcHandle = geoEl('circle', { class: 'guide-handle', r: 9,
    fill: '#2d9d4f', stroke: '#ffffff', 'stroke-width': 1.5 });
  g.appendChild(arcHandle);

  const arcRadiusHandle = geoEl('circle', { class: 'guide-handle', r: 6,
    fill: '#e67e00', stroke: '#ffffff', 'stroke-width': 1.5 });
  arcRadiusHandle.setAttribute('cx', 0);
  arcRadiusHandle.setAttribute('cy', -50);
  g.appendChild(arcRadiusHandle);

  const arcBuildBox = geoEl('rect', { x: -138, y: -78, width: 18, height: 18, rx: 3,
    fill: '#ffffff', stroke: '#2d9d4f', 'stroke-width': 1.5, style: 'cursor:pointer; pointer-events:auto;' });
  arcBuildBox.setAttribute('data-checked', '0');
  g.appendChild(arcBuildBox);

  const arcBuildCheck = geoEl('path', { d: '', fill: 'none', stroke: '#2d9d4f',
    'stroke-width': 2.5, 'stroke-linecap': 'round', 'stroke-linejoin': 'round', 'pointer-events': 'none' });
  g.appendChild(arcBuildCheck);

  const arcBuildToggle = (e) => { e.stopPropagation(); e.preventDefault(); toggleProtractorArcCheckbox(); };
  arcBuildBox.addEventListener('pointerdown', e => e.stopPropagation());
  arcBuildBox.addEventListener('click', arcBuildToggle);

  guideSvg.appendChild(g);
  geoGroups.protractor = { g, body, spokes, ticks, notch, centerHole, vertexDot, rotateHandle, resizeHandle, arcMark, arcLabel, arcHandle, arcRadiusHandle, arcBuildBox, arcBuildCheck };
  renderGeoProtractor();
}

function toggleProtractorArcCheckbox() {
  const st = geoGuides.protractor;
  const { arcBuildBox, arcBuildCheck } = geoGroups.protractor;
  const isChecked = arcBuildBox.getAttribute('data-checked') === '1';
  if (isChecked) {
    arcBuildBox.setAttribute('data-checked', '0');
    arcBuildBox.setAttribute('fill', '#ffffff');
    arcBuildCheck.setAttribute('d', '');
    return;
  }
  if (!st.arcAngle || st.arcAngle < 1) { showToast('⚠ Setați mai întâi un unghi pe raportor'); return; }
  arcBuildBox.setAttribute('data-checked', '1');
  arcBuildBox.setAttribute('fill', '#2d9d4f');
  arcBuildCheck.setAttribute('d', 'M -133 -69 L -130 -65 L -124 -74');
  finalizeProtractorArc(true);
  setTimeout(() => {
    arcBuildBox.setAttribute('data-checked', '0');
    arcBuildBox.setAttribute('fill', '#ffffff');
    arcBuildCheck.setAttribute('d', '');
  }, 600);
}

function renderGeoProtractor() {
  const st = geoGuides.protractor;
  const { body, spokes, ticks, notch, rotateHandle, resizeHandle, arcMark, arcLabel, arcHandle, arcRadiusHandle } = geoGroups.protractor;
  const R = st.radius;
  const arcR = R * (st.arcRadiusScale || 0.45);

  let d = `M ${-R} 0 `;
  for (let deg = 180; deg >= 0; deg -= 2) {
    const rad = deg * Math.PI / 180;
    d += `L ${R * Math.cos(rad)} ${-R * Math.sin(rad)} `;
  }
  d += 'Z ';
  const holeR = 16;
  d += `M ${holeR} 0 A ${holeR} ${holeR} 0 1 0 ${-holeR} 0 A ${holeR} ${holeR} 0 1 0 ${holeR} 0 Z`;
  body.setAttribute('d', d);

  const nR = 13;
  notch.setAttribute('d', `M ${-nR} 0 A ${nR} ${nR} 0 0 1 ${nR} 0`);

  geoClear(spokes);
  geoClear(ticks);

  const r0 = 22;
  const rimIn = R - 30;

  for (let deg = 0; deg <= 180; deg += 10) {
    const rad = deg * Math.PI / 180;
    const cx = Math.cos(rad), sy = -Math.sin(rad);
    spokes.appendChild(geoEl('line', { x1: r0 * cx, y1: r0 * sy, x2: rimIn * cx, y2: rimIn * sy }));
  }

  for (let deg = 0; deg <= 180; deg += 1) {
    const big = deg % 10 === 0;
    const med = deg % 5 === 0;
    const rad = deg * Math.PI / 180;
    const cx = Math.cos(rad), sy = -Math.sin(rad);
    const tickLen = big ? 26 : (med ? 17 : 10);
    const x1 = R * cx, y1 = R * sy;
    const x2 = (R - tickLen) * cx, y2 = (R - tickLen) * sy;
    ticks.appendChild(geoEl('line', { x1, y1, x2, y2,
      stroke: 'rgba(20,20,20,0.75)', 'stroke-width': big ? 1.7 : (med ? 1.1 : 0.6) }));
    if (big) {
      const rt1 = R - 40;
      const t1 = geoEl('text', { class: 'guide-label', x: rt1 * cx - 8, y: rt1 * sy + 4 });
      t1.textContent = deg;
      ticks.appendChild(t1);
      const rt2 = R - 58;
      const t2 = geoEl('text', { class: 'guide-label', x: rt2 * cx - 8, y: rt2 * sy + 4 });
      t2.textContent = 180 - deg;
      ticks.appendChild(t2);
    }
  }

  rotateHandle.setAttribute('cx', 0);
  rotateHandle.setAttribute('cy', -R + 34);
  resizeHandle.setAttribute('x', R - 8);
  resizeHandle.setAttribute('y', -8);

  const aRad = st.arcAngle * Math.PI / 180;
  const hx = arcR * Math.cos(aRad);
  const hy = -arcR * Math.sin(aRad);
  
  let markD = `M ${arcR} 0 `;
  const steps = Math.max(1, Math.round(st.arcAngle / 3));
  for (let i = 1; i <= steps; i++) {
    const d2 = (st.arcAngle * i) / steps;
    const r2 = d2 * Math.PI / 180;
    markD += `L ${arcR * Math.cos(r2)} ${-arcR * Math.sin(r2)} `;
  }
  arcMark.setAttribute('d', markD);
  arcHandle.setAttribute('cx', hx);
  arcHandle.setAttribute('cy', hy);
  const labelR = arcR + 16;
  arcLabel.setAttribute('x', labelR * Math.cos(aRad / 2) - 10);
  arcLabel.setAttribute('y', -labelR * Math.sin(aRad / 2));
  arcLabel.textContent = Math.round(st.arcAngle) + '°';

  const radiusHandleDist = Math.max(30, Math.min(R - 20, arcR));
  arcRadiusHandle.setAttribute('cx', 0);
  arcRadiusHandle.setAttribute('cy', -radiusHandleDist);
}

// ---------------- COMPAS ----------------
function buildGeoCompass() {
  const g = geoEl('g', { class: 'guide', id: 'guide-compass' });

  const armLine = geoEl('line', { stroke: '#6b4a2b', 'stroke-width': 4, 'stroke-linecap': 'round' });
  g.appendChild(armLine);

  const radiusLabel = geoEl('text', { class: 'guide-label', 'font-weight': 'bold', 'font-size': '11' });
  g.appendChild(radiusLabel);

  const centerHandle = geoEl('circle', { class: 'guide-handle', r: 7,
    fill: '#0055cc', stroke: '#ffffff', 'stroke-width': 1.3 });
  g.appendChild(centerHandle);

  const midHandle = geoEl('rect', { class: 'guide-handle', width: 14, height: 14, rx: 3,
    fill: '#e9e9e9', stroke: '#888888', 'stroke-width': 1.6 });
  g.appendChild(midHandle);

  const resizeHandle = geoEl('rect', { class: 'guide-handle', width: 13, height: 13, rx: 3,
    fill: '#ffffff', stroke: '#e67e00', 'stroke-width': 1.6 });
  g.appendChild(resizeHandle);

  const tipHandle = geoEl('circle', { class: 'guide-handle', r: 8,
    fill: '#e63946', stroke: '#ffffff', 'stroke-width': 1.3 });
  g.appendChild(tipHandle);

  const arcLabel = geoEl('text', { class: 'guide-label', 'font-weight': 'bold', 'font-size': '11', fill: '#e63946' });
  g.appendChild(arcLabel);

  guideSvg.appendChild(g);
  geoGroups.compass = { g, armLine, radiusLabel, centerHandle, midHandle, resizeHandle, tipHandle, arcLabel };
  renderGeoCompass();
}

function renderGeoCompass() {
  const st = geoGuides.compass;
  const { armLine, radiusLabel, centerHandle, midHandle, resizeHandle, tipHandle } = geoGroups.compass;
  const cosA = Math.cos(st.angle), sinA = Math.sin(st.angle);
  const tipX = st.x + st.radius * cosA;
  const tipY = st.y + st.radius * sinA;
  const midX = st.x + st.radius * 0.5 * cosA;
  const midY = st.y + st.radius * 0.5 * sinA;
  const rzDist = Math.max(st.radius - 22, st.radius * 0.5 + 10);
  const rzX = st.x + rzDist * cosA;
  const rzY = st.y + rzDist * sinA;

  armLine.setAttribute('x1', st.x); armLine.setAttribute('y1', st.y);
  armLine.setAttribute('x2', tipX); armLine.setAttribute('y2', tipY);
  centerHandle.setAttribute('cx', st.x); centerHandle.setAttribute('cy', st.y);

  midHandle.setAttribute('x', midX - 7);
  midHandle.setAttribute('y', midY - 7);

  resizeHandle.setAttribute('x', rzX - 6.5);
  resizeHandle.setAttribute('y', rzY - 6.5);

  tipHandle.setAttribute('cx', tipX); tipHandle.setAttribute('cy', tipY);

  const perp = st.angle + Math.PI / 2;
  radiusLabel.setAttribute('x', midX + 18 * Math.cos(perp));
  radiusLabel.setAttribute('y', midY + 18 * Math.sin(perp));
  radiusLabel.textContent = 'r = ' + (st.radius / 50).toFixed(2) + ' cm';
}

// starea desenării curente cu compasul
let compassDraw = null;

function compassArcFromAccumulated(startAngle, accumulated) {
  const angleDiff = Math.min(Math.abs(accumulated), 2 * Math.PI);
  let displayStart, displayEnd;
  if (accumulated >= 0) {
    displayStart = startAngle;
    displayEnd = startAngle + angleDiff;
  } else {
    displayStart = startAngle - angleDiff;
    displayEnd = startAngle;
  }
  return { angleDiff, displayStart, displayEnd };
}

function compassRenderLivePreview() {
  if (!compassDraw) return;
  const st = geoGuides.compass;
  overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
  const { angleDiff, displayStart, displayEnd } = compassArcFromAccumulated(compassDraw.startAngle, compassDraw.accumulated);
  overlayCtx.save();
  overlayCtx.strokeStyle = color;
  overlayCtx.lineWidth = (lastPenSize || 2) + 1;
  overlayCtx.lineCap = 'round';
  overlayCtx.beginPath();
  if (angleDiff >= 2 * Math.PI - 0.1) {
    overlayCtx.arc(st.x, st.y, st.radius, 0, 2 * Math.PI);
  } else {
    overlayCtx.arc(st.x, st.y, st.radius, displayStart, displayEnd);
  }
  overlayCtx.stroke();
  overlayCtx.restore();

  const { arcLabel } = geoGroups.compass;
  const tipX = st.x + st.radius * Math.cos(st.angle);
  const tipY = st.y + st.radius * Math.sin(st.angle);
  arcLabel.setAttribute('x', tipX + 16);
  arcLabel.setAttribute('y', tipY);
  const deg = angleDiff * 180 / Math.PI;
  arcLabel.textContent = (angleDiff >= 2 * Math.PI - 0.1 ? '360°' : deg.toFixed(1) + '°');

  showMathInfo('🔄 Rază: ' + (st.radius / 50).toFixed(2) + ' cm  |  Arc: ' + arcLabel.textContent);
}

function compassFinalizeDraw() {
  if (!compassDraw) return;
  const st = geoGuides.compass;
  const page = getCurrentPage();
  const size = lastPenSize;
  const { angleDiff, displayStart, displayEnd } = compassArcFromAccumulated(compassDraw.startAngle, compassDraw.accumulated);

  overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
  geoGroups.compass.arcLabel.textContent = '';

  if (angleDiff > 0.05) {
    const dir = compassDraw.accumulated >= 0 ? 1 : -1;
    if (angleDiff >= 2 * Math.PI - 0.1) {
      pushStroke(page, { type: 'circle', cx: st.x, cy: st.y, radius: st.radius, color: color, size: size, startAngle: compassDraw.startAngle, dir });
      showToast('✓ Cerc complet desenat: raza ' + (st.radius / 50).toFixed(1) + ' cm');
    } else {
      pushStroke(page, { type: 'arc', cx: st.x, cy: st.y, radius: st.radius, startAngle: displayStart, endAngle: displayEnd, color: color, size: size, dir });
      showToast('✓ Arc desenat: ' + (angleDiff * 180 / Math.PI).toFixed(1) + '°  |  rază ' + (st.radius / 50).toFixed(1) + ' cm');
    }
    redrawStrokes();
    updateStatus();
  }
  compassDraw = null;
}

buildGeoRuler(); buildGeoSetsquare(); buildGeoProtractor(); buildGeoCompass();


function updateGeoTransform(name) {
  const st = geoGuides[name];
  geoGroups[name].g.setAttribute('transform', `translate(${st.x},${st.y}) rotate(${st.angle * 180 / Math.PI})`);
}
Object.keys(geoGuides).forEach(name => { if (name !== 'compass') updateGeoTransform(name); });

const GEO_ROTATE_HANDLE_LOCAL_ANGLE = {
  ruler: Math.atan2(geoGuides.ruler.thickness / 2, 26),
  setsquare: Math.atan2(-24, 24),
  protractor: -Math.PI / 2
};

let geoActiveDrag = null;
Object.keys(geoGroups).forEach(name => {
  if (name === 'compass') return;
  const grp = geoGroups[name];
  grp.body.addEventListener('pointerdown', e => {
    e.stopPropagation(); e.preventDefault();
    const p = pos(e);
    geoActiveDrag = { name, mode: 'move', offX: p.x - geoGuides[name].x, offY: p.y - geoGuides[name].y };
    try { grp.body.setPointerCapture(e.pointerId); } catch (err) {}
  });
  grp.rotateHandle.addEventListener('pointerdown', e => {
    e.stopPropagation(); e.preventDefault();
    if (e.shiftKey) {
      geoActiveDrag = { name, mode: 'rotateSnap', lastAngle: geoGuides[name].angle };
    } else {
      geoActiveDrag = { name, mode: 'rotate', localOffset: GEO_ROTATE_HANDLE_LOCAL_ANGLE[name] || 0 };
    }
    try { grp.rotateHandle.setPointerCapture(e.pointerId); } catch (err) {}
  });
  if (grp.resizeHandle) {
    grp.resizeHandle.addEventListener('pointerdown', e => {
      e.stopPropagation(); e.preventDefault();
      geoActiveDrag = { name, mode: 'resize' };
      try { grp.resizeHandle.setPointerCapture(e.pointerId); } catch (err) {}
    });
  }
});

geoGroups.protractor.arcHandle.addEventListener('pointerdown', e => {
  e.stopPropagation(); e.preventDefault();
  geoActiveDrag = { name: 'protractor', mode: 'protractorArc' };
  try { geoGroups.protractor.arcHandle.setPointerCapture(e.pointerId); } catch (err) {}
});

geoGroups.protractor.arcRadiusHandle.addEventListener('pointerdown', e => {
  e.stopPropagation(); e.preventDefault();
  geoActiveDrag = { name: 'protractor', mode: 'protractorArcRadius' };
  try { geoGroups.protractor.arcRadiusHandle.setPointerCapture(e.pointerId); } catch (err) {}
});

(function wireCompassDrag() {
  const grp = geoGroups.compass;

  grp.centerHandle.addEventListener('pointerdown', e => {
    e.stopPropagation(); e.preventDefault();
    const p = pos(e);
    const st = geoGuides.compass;
    geoActiveDrag = { name: 'compass', mode: 'compassMove', offX: p.x - st.x, offY: p.y - st.y };
    try { grp.centerHandle.setPointerCapture(e.pointerId); } catch (err) {}
  });

  grp.midHandle.addEventListener('pointerdown', e => {
    e.stopPropagation(); e.preventDefault();
    if (e.shiftKey) {
      geoActiveDrag = { name: 'compass', mode: 'compassRotateSnap', lastAngle: geoGuides.compass.angle };
    } else {
      geoActiveDrag = { name: 'compass', mode: 'compassRotate' };
    }
    try { grp.midHandle.setPointerCapture(e.pointerId); } catch (err) {}
  });

  grp.resizeHandle.addEventListener('pointerdown', e => {
    e.stopPropagation(); e.preventDefault();
    if (e.shiftKey) {
      geoActiveDrag = { name: 'compass', mode: 'compassResizeSnap', lastRadius: geoGuides.compass.radius };
    } else {
      geoActiveDrag = { name: 'compass', mode: 'compassResize' };
    }
    try { grp.resizeHandle.setPointerCapture(e.pointerId); } catch (err) {}
  });

  grp.tipHandle.addEventListener('pointerdown', e => {
    e.stopPropagation(); e.preventDefault();
    const st = geoGuides.compass;
    compassDraw = { startAngle: st.angle, lastAngle: st.angle, accumulated: 0 };
    geoActiveDrag = { name: 'compass', mode: 'compassRotateTip' };
    try { grp.tipHandle.setPointerCapture(e.pointerId); } catch (err) {}
  });
})();

function geoDragMove(e) {
  if (!geoActiveDrag) return;
  e.preventDefault();
  const p = pos(e);
  const st = geoGuides[geoActiveDrag.name];
  
  if (geoActiveDrag.mode === 'move') {
    st.x = p.x - geoActiveDrag.offX;
    st.y = p.y - geoActiveDrag.offY;
    updateGeoTransform(geoActiveDrag.name);
  } else if (geoActiveDrag.mode === 'rotate') {
    st.angle = Math.atan2(p.y - st.y, p.x - st.x) - geoActiveDrag.localOffset;
    updateGeoTransform(geoActiveDrag.name);
  } else if (geoActiveDrag.mode === 'rotateSnap') {
    const rawAngle = Math.atan2(p.y - st.y, p.x - st.x) - geoActiveDrag.localOffset;
    const snapRad = 1 * Math.PI / 180;
    st.angle = Math.round(rawAngle / snapRad) * snapRad;
    updateGeoTransform(geoActiveDrag.name);
  } else if (geoActiveDrag.mode === 'resize') {
    const dx = p.x - st.x, dy = p.y - st.y;
    const cos = Math.cos(st.angle), sin = Math.sin(st.angle);
    const proj = dx * cos + dy * sin;
    if (geoActiveDrag.name === 'ruler') {
      st.length = Math.max(150, Math.min(2400, proj));
      renderGeoRuler();
    } else if (geoActiveDrag.name === 'setsquare') {
      st.size = Math.max(120, Math.min(1400, proj));
      renderGeoSetsquare();
    } else if (geoActiveDrag.name === 'protractor') {
      st.radius = Math.max(90, Math.min(900, proj));
      renderGeoProtractor();
    }
  } else if (geoActiveDrag.mode === 'compassMove') {
    st.x = p.x - geoActiveDrag.offX;
    st.y = p.y - geoActiveDrag.offY;
    renderGeoCompass();
  } else if (geoActiveDrag.mode === 'compassRotate') {
    st.angle = Math.atan2(p.y - st.y, p.x - st.x);
    renderGeoCompass();
  } else if (geoActiveDrag.mode === 'compassRotateSnap') {
    const rawAngle = Math.atan2(p.y - st.y, p.x - st.x);
    const snapRad = 1 * Math.PI / 180;
    st.angle = Math.round(rawAngle / snapRad) * snapRad;
    renderGeoCompass();
  } else if (geoActiveDrag.mode === 'compassResize') {
    const cos = Math.cos(st.angle), sin = Math.sin(st.angle);
    const proj = (p.x - st.x) * cos + (p.y - st.y) * sin;
    st.radius = Math.max(30, Math.min(1000, proj));
    renderGeoCompass();
  } else if (geoActiveDrag.mode === 'compassResizeSnap') {
    const cos = Math.cos(st.angle), sin = Math.sin(st.angle);
    const proj = (p.x - st.x) * cos + (p.y - st.y) * sin;
    const snapPx = 0.5 * 50;
    st.radius = Math.round(proj / snapPx) * snapPx;
    st.radius = Math.max(30, Math.min(1000, st.radius));
    renderGeoCompass();
  } else if (geoActiveDrag.mode === 'compassRotateTip') {
    const newAngle = Math.atan2(p.y - st.y, p.x - st.x);
    if (compassDraw) {
      let delta = newAngle - compassDraw.lastAngle;
      if (delta > Math.PI) delta -= 2 * Math.PI;
      if (delta < -Math.PI) delta += 2 * Math.PI;
      compassDraw.accumulated += delta;
      compassDraw.lastAngle = newAngle;
    }
    st.angle = newAngle;
    renderGeoCompass();
    if (compassDraw) compassRenderLivePreview();
  } else if (geoActiveDrag.mode === 'protractorArc') {
    const local = geoWorldToLocal(st, p.x, p.y);
    let deg = -Math.atan2(local.y, local.x) * 180 / Math.PI;
    deg = Math.max(0, Math.min(180, deg));
    st.arcAngle = deg;
    renderGeoProtractor();
  } else if (geoActiveDrag.mode === 'protractorArcRadius') {
    const local = geoWorldToLocal(st, p.x, p.y);
    const dist = Math.sqrt(local.x * local.x + local.y * local.y);
    const minR = 15;
    const maxR = st.radius - 10;
    const newScale = Math.max(minR / st.radius, Math.min(maxR / st.radius, dist / st.radius));
    st.arcRadiusScale = newScale;
    renderGeoProtractor();
  }
}
function geoDragEnd() {
  if (geoActiveDrag && geoActiveDrag.mode === 'compassRotateTip' && compassDraw) {
    compassFinalizeDraw();
  }
  geoActiveDrag = null;
}
window.addEventListener('pointermove', geoDragMove);
window.addEventListener('pointerup', geoDragEnd);
window.addEventListener('pointercancel', geoDragEnd);

// ================================================================
// FINALIZARE ARC RAPORTOR - CORECȚIE COMPLETĂ
// Arcul trebuie să fie mereu în interiorul raportorului (maxim 180°)
// ================================================================
function finalizeProtractorArc(skipUsageRecord) {
  const st = geoGuides.protractor;
  if (st.arcAngle < 1 || st.arcAngle > 180) return;

  const arcR = st.radius * (st.arcRadiusScale || 0.45);
  const aRad = st.arcAngle * Math.PI / 180;
  
  // Punctul de start este întotdeauna la baza raportorului (0° în sistem local)
  const p0_local = { x: arcR, y: 0 };
  // Punctul de sfârșit este la unghiul setat
  const p1_local = { x: arcR * Math.cos(aRad), y: -arcR * Math.sin(aRad) };
  
  // Transformăm în coordonate globale
  const p0 = geoLocalToWorld(st, p0_local.x, p0_local.y);
  const p1 = geoLocalToWorld(st, p1_local.x, p1_local.y);
  
  // Calculăm unghiurile în sistemul global
  const a0 = Math.atan2(p0.y - st.y, p0.x - st.x);
  const a1 = Math.atan2(p1.y - st.y, p1.x - st.x);
  
  // Determinăm arcul MIC între a0 și a1 (maxim 180°)
  let diff = a1 - a0;
  while (diff > Math.PI) diff -= 2 * Math.PI;
  while (diff < -Math.PI) diff += 2 * Math.PI;
  
  const dir = diff >= 0 ? 1 : -1;
  const absDiff = Math.min(Math.abs(diff), Math.PI);
  const finalDir = diff >= 0 ? 1 : -1;
  
  let startAngle = a0;
  let endAngle;
  if (finalDir >= 0) {
    endAngle = a0 + absDiff;
  } else {
    endAngle = a0 - absDiff;
  }
  
  const finalAngleDiff = Math.abs(endAngle - startAngle);
  if (finalAngleDiff < 0.01) return;
  
  const page = getCurrentPage();
  
  // Desenăm arcul
  pushStroke(page, { 
    type: 'arc', 
    cx: st.x, 
    cy: st.y, 
    radius: arcR, 
    startAngle: Math.min(startAngle, endAngle), 
    endAngle: Math.max(startAngle, endAngle), 
    color, 
    size: lastPenSize, 
    dir: finalDir
  });

  // Adăugăm eticheta cu valoarea unghiului
  const labelR = arcR + 16;
  const midRad = (st.arcAngle / 2) * Math.PI / 180;
  const labelPos = geoLocalToWorld(st, labelR * Math.cos(midRad), -labelR * Math.sin(midRad));
  const labelFontSize = 16;
  pushStroke(page, {
    type: 'text',
    text: Math.round(st.arcAngle) + '°',
    x: labelPos.x - 10,
    y: labelPos.y - labelFontSize / 2,
    font: `bold ${labelFontSize}px sans-serif`,
    color: color,
    fontSize: labelFontSize,
    textAlign: 'left'
  });
  
  showToast('✓ Arc construit: ' + Math.round(st.arcAngle) + '°');
  redrawStrokes();
  updateStatus();
  }

function toggleGeoGuide(name, btnId) {
  geoGuides[name].visible = !geoGuides[name].visible;
  geoGroups[name].g.classList.toggle('visible', geoGuides[name].visible);
  document.getElementById(btnId).classList.toggle('active', geoGuides[name].visible);
  if (name === 'compass' && geoGuides.compass.visible) {
    showMathInfo('⭕ Albastru = centru (trage pentru a muta)  |  Pătrățel gri = trage liber pentru a roti / a mări-micșora raza, fără să deseneze  |  Roșu = trage pentru a desena cercul/arcul');
  }
  if (name === 'protractor' && geoGuides.protractor.visible) {
    showMathInfo('📐 Mânerul verde: trage-l de-a lungul raportorului pentru a seta unghiul  |  Bifează căsuța pentru a construi arcul');
  }
}
document.getElementById('btn-ruler').onclick = () => toggleGeoGuide('ruler', 'btn-ruler');
document.getElementById('btn-setsquare').onclick = () => toggleGeoGuide('setsquare', 'btn-setsquare');
document.getElementById('btn-protractor').onclick = () => toggleGeoGuide('protractor', 'btn-protractor');

// lipirea (snap) punctelor desenate de muchiile instrumentelor vizibile
function geoLocalToWorld(st, lx, ly) {
  const cos = Math.cos(st.angle), sin = Math.sin(st.angle);
  return { x: st.x + lx * cos - ly * sin, y: st.y + lx * sin + ly * cos };
}

function geoWorldToLocal(st, wx, wy) {
  const dx = wx - st.x, dy = wy - st.y;
  const cos = Math.cos(-st.angle), sin = Math.sin(-st.angle);
  return { x: dx * cos - dy * sin, y: dx * sin + dy * cos };
}

function getGeoSegments(name) {
  const st = geoGuides[name];
  if (!st.visible) return [];
  if (name === 'ruler') {
    const L = st.length, T = st.thickness;
    return [
      [geoLocalToWorld(st, 0, 0), geoLocalToWorld(st, L, 0)],
      [geoLocalToWorld(st, 0, T), geoLocalToWorld(st, L, T)]
    ];
  }
  if (name === 'setsquare') {
    const S = st.size;
    return [
      [geoLocalToWorld(st, 0, 0), geoLocalToWorld(st, S, 0)],
      [geoLocalToWorld(st, 0, 0), geoLocalToWorld(st, 0, -S)],
      [geoLocalToWorld(st, S, 0), geoLocalToWorld(st, 0, -S)]
    ];
  }
  if (name === 'protractor') {
    const R = st.radius;
    const segs = [[geoLocalToWorld(st, -R, 0), geoLocalToWorld(st, R, 0)]];
    let prev = geoLocalToWorld(st, R, 0);
    for (let deg = 6; deg <= 180; deg += 6) {
      const rad = deg * Math.PI / 180;
      const p = geoLocalToWorld(st, R * Math.cos(rad), -R * Math.sin(rad));
      segs.push([prev, p]);
      prev = p;
    }
    return segs;
  }
  return [];
}

function geoClosestOnSegment(p, a, b) {
  const dx = b.x - a.x, dy = b.y - a.y;
  const len2 = dx * dx + dy * dy || 1;
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / len2;
  t = Math.max(0, Math.min(1, t));
  const cx = a.x + dx * t, cy = a.y + dy * t;
  return { x: cx, y: cy, d: Math.hypot(p.x - cx, p.y - cy) };
}

function nearestGuideDist(p) {
  let bestD = Infinity;
  Object.keys(geoGuides).forEach(name => {
    getGeoSegments(name).forEach(seg => {
      const c = geoClosestOnSegment(p, seg[0], seg[1]);
      if (c.d < bestD) bestD = c.d;
    });
  });
  return bestD;
}

function snapToGuides(p) {
  let best = null, bestD = GUIDE_SNAP_DIST, bestName = null;
  Object.keys(geoGuides).forEach(name => {
    if (name === 'compass') return;
    getGeoSegments(name).forEach(seg => {
      const c = geoClosestOnSegment(p, seg[0], seg[1]);
      if (c.d < bestD) { bestD = c.d; best = { x: c.x, y: c.y }; bestName = name; }
    });
  });
  lastSnapGuideName = bestName;
  return best || p;
}

// ================================================================
// INITIALIZARE
// ================================================================

document.getElementById('btn-pen').classList.add('active');
tool = 'pen';

updateGeoToolContrast();
setTimeout(initCanvas, 100);
