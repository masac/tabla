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

let DPR = Math.min(window.devicePixelRatio || 1, 2);
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
let boardRuling = 'none'; // 'none' | 'grid' | 'dictando' | 'music'
let rulingSize = 28; // distanța de bază (px) dintre liniile/pătratele liniaturii
let rulingColor = '#ffffff'; // culoarea liniaturii; implicit alb, fiindcă tabla pornește cu fundal negru
let rulingOpacity = 0.5; // opacitatea liniaturii (0-1); implicit 50%

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
let isRotatingSolid = false;
let rotateStrokeIndex = -1;
let rotateOriginalStroke = null;
let rotateStartX = 0;
let rotateStartRotationY = 0;
let currentRotateHandle = null; // { x, y, strokeIdx }
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
  }
  initCanvas();
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

let angleReadoutTimer = null;
function showAngleReadout(rotationYRadians, opts = {}) {
  const el = document.getElementById('angle-readout');
  if (!el) return;
  let deg = (rotationYRadians * 180 / Math.PI) % 360;
  if (deg < 0) deg += 360;
  el.textContent = `Unghi rotație: ${deg.toFixed(1)}°`;
  el.classList.add('show');
  clearTimeout(angleReadoutTimer);
  if (opts.persist) {
    // stays visible while actively dragging; hidden explicitly via hideAngleReadout()
    return;
  }
  const duration = opts.duration != null ? opts.duration : 4000;
  angleReadoutTimer = setTimeout(() => el.classList.remove('show'), duration);
}
function hideAngleReadout(duration = 4000) {
  const el = document.getElementById('angle-readout');
  if (!el) return;
  clearTimeout(angleReadoutTimer);
  angleReadoutTimer = setTimeout(() => el.classList.remove('show'), duration);
}

function initCanvas() {
  DPR = Math.min(window.devicePixelRatio || 1, 2);
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
  drawBoardRuling();
}

// Convertește o culoare (hex #rrggbb sau rgba(...)) într-un string rgba cu opacitatea dată,
// suprascriind orice canal alfa existent.
function colorWithOpacity(colorStr, opacity) {
  let r, g, b;
  if (colorStr.startsWith('#')) {
    const h = colorStr.replace('#', '');
    r = parseInt(h.substring(0, 2), 16);
    g = parseInt(h.substring(2, 4), 16);
    b = parseInt(h.substring(4, 6), 16);
  } else {
    const m = colorStr.match(/rgba?\(\s*([\d.]+)\s*,\s*([\d.]+)\s*,\s*([\d.]+)/);
    r = m ? +m[1] : 255; g = m ? +m[2] : 255; b = m ? +m[3] : 255;
  }
  return `rgba(${r},${g},${b},${opacity})`;
}

// Culoare de liniatură puternic contrastantă ("stridentă") față de fundal, ca liniile
// caietului să rămână clar vizibile indiferent de culoarea aleasă pentru tablă. Dacă
// utilizatorul a ales manual o culoare (rulingColor), aceasta are prioritate.
function getRulingColor() {
  const base = rulingColor || (isColorDark(bgColor) ? '#ffe100' : '#e6007e');
  return colorWithOpacity(base, rulingOpacity);
}

// Desenează, peste culoarea de fundal, liniatura aleasă de utilizator: caroiaj (ca în
// caietul de matematică), liniatură dictando (linii orizontale simple, ca în caietul de
// scriere/dictando) sau portativ (ca în caietul de muzică). Toate distanțele se scalează
// proporțional cu rulingSize, controlat din bara de instrumente. Se folosesc dimensiuni CSS
// (nu cele scalate cu DPR), fiindcă bgCtx e deja scalat cu bgCtx.scale(DPR, DPR) în initCanvas().
function drawBoardRuling() {
  if (boardRuling === 'none') return;
  const w = bgC.width / DPR, h = bgC.height / DPR;
  const cx = bgCtx;
  const scale = rulingSize / 28;
  cx.save();
  cx.strokeStyle = getRulingColor();

  if (boardRuling === 'grid') {
    const step = rulingSize;
    cx.lineWidth = 1;
    cx.beginPath();
    for (let x = 0; x <= w; x += step) { cx.moveTo(x + 0.5, 0); cx.lineTo(x + 0.5, h); }
    for (let y = 0; y <= h; y += step) { cx.moveTo(0, y + 0.5); cx.lineTo(w, y + 0.5); }
    cx.stroke();
  } else if (boardRuling === 'dictando') {
    // linii orizontale simple, egal distanțate, exact ca în caietul de dictando din imagine.
    const step = rulingSize;
    cx.lineWidth = 1;
    cx.beginPath();
    for (let y = step; y <= h; y += step) { cx.moveTo(0, y + 0.5); cx.lineTo(w, y + 0.5); }
    cx.stroke();
  } else if (boardRuling === 'music') {
    const lineGap = 9 * scale, staffGap = 56 * scale;
    const staffHeight = lineGap * 4;
    const period = staffHeight + staffGap;
    cx.lineWidth = 1.2;
    for (let top = 40 * scale; top < h; top += period) {
      cx.beginPath();
      for (let i = 0; i < 5; i++) {
        const y = top + i * lineGap + 0.5;
        cx.moveTo(0, y); cx.lineTo(w, y);
      }
      cx.stroke();
    }
  }
  cx.restore();
}

function drawStrokeOn(c, stroke) {
  if (!stroke) return;

  if (stroke.type === 'solid3d' || stroke.type === 'solidNet') {
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
      out.baseScale = (orig.baseScale || 1) * factor;
      break;
    }
    case 'solidNet': {
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
  if (stroke.type === 'solid3d' || stroke.type === 'solidNet') {
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
    } else if (s.type === 'solid3d' || s.type === 'solidNet') {
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

  // Mâner de rotire — doar pentru corpuri 3D poligonale/rotunde (nu și pentru sferă, care arată
  // la fel din orice unghi), poziționat în colțul opus mânerului de scalare.
  currentRotateHandle = null;
  if (selectedStrokes.size === 1) {
    const idx = [...selectedStrokes][0];
    const stroke = page.strokes[idx];
    if (stroke && stroke.type === 'solid3d') {
      const spec = SOLID_SHAPES[stroke.shape];
      if (spec && !spec.noRotate) {
        const bbox = getStrokeBoundingBox(stroke);
        const rx = bbox.x - 2;
        const ry = bbox.y - 2;
        currentRotateHandle = { x: rx, y: ry, strokeIdx: idx };
        selCtx.save();
        selCtx.fillStyle = '#2d7dd2';
        selCtx.strokeStyle = '#ffffff';
        selCtx.lineWidth = 3;
        selCtx.beginPath();
        selCtx.arc(rx, ry, 13, 0, Math.PI * 2);
        selCtx.fill();
        selCtx.stroke();
        // săgeată circulară simplă ca indiciu vizual de rotire
        selCtx.strokeStyle = '#ffffff';
        selCtx.lineWidth = 1.8;
        selCtx.beginPath();
        selCtx.arc(rx, ry, 6, -0.3 * Math.PI, 1.2 * Math.PI);
        selCtx.stroke();
        const ah = 1.2 * Math.PI;
        const ahx = rx + 6 * Math.cos(ah), ahy = ry + 6 * Math.sin(ah);
        selCtx.beginPath();
        selCtx.moveTo(ahx, ahy);
        selCtx.lineTo(ahx - 4, ahy - 2);
        selCtx.moveTo(ahx, ahy);
        selCtx.lineTo(ahx - 1, ahy + 4);
        selCtx.stroke();
        selCtx.restore();
      }
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
  if (stroke.type === 'solid3d' || stroke.type === 'solidNet') {
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
  } else if ((stroke.type === 'solid3d' || stroke.type === 'solidNet') && snap.visible) {
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

    if (currentRotateHandle && selectedStrokes.has(currentRotateHandle.strokeIdx)) {
      const rhx = p.x - currentRotateHandle.x, rhy = p.y - currentRotateHandle.y;
      const rotHitRadius = e.pointerType === 'touch' ? 30 : 16;
      if (Math.sqrt(rhx * rhx + rhy * rhy) < rotHitRadius && page) {
        const stroke = page.strokes[currentRotateHandle.strokeIdx];
        if (stroke) {
          isRotatingSolid = true;
          rotateStrokeIndex = currentRotateHandle.strokeIdx;
          rotateOriginalStroke = JSON.parse(JSON.stringify(stroke));
          rotateStartX = p.x;
          rotateStartRotationY = stroke.rotationY || 0;
          drawC.setPointerCapture(e.pointerId);
          e.preventDefault();
          showToast('↻ Trage stânga/dreapta pentru a roti');
          return;
        }
      }
    }

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
          } else if (s.type === 'solid3d' || s.type === 'solidNet') {
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

  if (tool === 'select' && isRotatingSolid) {
    const page = getCurrentPage();
    if (page && rotateOriginalStroke) {
      const stroke = page.strokes[rotateStrokeIndex];
      if (stroke) {
        const dx = p.x - rotateStartX;
        const newRotationY = rotateStartRotationY + dx * 0.012;
        rotateSolid3D(stroke, newRotationY);
        showAngleReadout(newRotationY, { persist: true });
        redrawStrokes();
        drawSelectionHighlights();
      }
    }
    return;
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
      } else if ((s.type === 'solid3d' || s.type === 'solidNet') && start.visible) {
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

  if (tool === 'select' && isRotatingSolid) {
    isRotatingSolid = false;
    const page = getCurrentPage();
    const stroke = page ? page.strokes[rotateStrokeIndex] : null;
    if (page && stroke && rotateOriginalStroke) {
      const after = JSON.parse(JSON.stringify(stroke));
      if (JSON.stringify(after) !== JSON.stringify(rotateOriginalStroke)) {
        undoStack.push({ type: 'resizeStroke', page, stroke, before: rotateOriginalStroke, after });
        redoStack = [];
        let deg = ((stroke.rotationY || 0) * 180 / Math.PI) % 360;
        if (deg < 0) deg += 360;
        showToast(`✓ Rotit (${deg.toFixed(1)}°)`);
      }
    }
    hideAngleReadout(5000);
    rotateOriginalStroke = null;
    rotateStrokeIndex = -1;
    updateStatus();
    return;
  }

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
  isRotatingSolid = false;
  rotateOriginalStroke = null;
  rotateStrokeIndex = -1;
  hideAngleReadout(0);
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
  syncRulingColorPicker();
}

function setBoardRuling(type, btnId) {
  boardRuling = type;
  document.querySelectorAll('.ruling-btn').forEach(b => b.classList.remove('active'));
  if (btnId) {
    document.getElementById(btnId).classList.add('active');
  }
  drawBg();
}

// Actualizează swatch-ul selectorului de culoare al liniaturii ca să reflecte culoarea
// efectiv folosită: cea aleasă manual (rulingColor), sau — dacă e pe automat — o variantă
// opacă a culorii de contrast calculate pentru fundalul curent.
function syncRulingColorPicker() {
  const picker = document.getElementById('ruling-color-pick');
  if (!picker) return;
  picker.value = rulingColor || (isColorDark(bgColor) ? '#ffe100' : '#e6007e');
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
fnModalBackdrop.addEventListener('pointerdown', (e) => {
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

// Proiecție cu forfecare (aceeași convenție cavalieră ca la celelalte corpuri) — folosită și
// pentru hexagon. Fără forfecare, la anumite rotații un vârf din spate (ascuns) putea ajunge mai
// în afară pe orizontală decât conturul vizibil din față, făcând ca o muchie punctată să iasă
// vizibil în afara conturului plin — o "umflătură" clar greșită. Forfecarea ține vârfurile din
// spate mai "trase înăuntru" pe măsură ce corpul se rotește, la fel ca la cub/prismă/piramidă.
function hexProjectGP(X, Z, Y) {
  return solidProjectGP(X, Z, Y);
}

// Comutator global: dacă e true, muchiile "din spate" ale corpurilor 3D se desenează cu linie
// întreruptă (convenția clasică de manual, implicit); dacă e false, toate muchiile sunt continue.
let SOLID_SHOW_HIDDEN_LINES = true;

// Determină, pentru fiecare muchie a bazei unui corp (prismă/trunchi/piramidă), dacă fața
// laterală corespunzătoare e vizibilă (spre privitor) sau ascunsă, în proiecția oblică
// (cavalieră) folosită de toate corpurile. Calculul e geometric EXACT în 3D: pentru fiecare
// față laterală (patrulater Vi,Vj,Tj,Ti — sau triunghi Vi,Vj,Apex la piramide, unde topScale=0)
// se calculează normala reală (produs vectorial pe muchiile feței, ținând cont de înălțime și
// de topScale — cât de mult se îngustează partea de sus față de bază) și se compară cu direcția
// reală de proiecție a desenului oblic (unghiul SOLID_OBLIQUE_ANGLE, factorul SOLID_OBLIQUE_K).
// Nu se mai folosește nicio aproximare bazată doar pe conturul bazei (de sus) și niciun
// histerezis artificial — fiecare muchie își schimbă starea exact la unghiul la care fața ei
// devine cu adevărat vizibilă/ascunsă, ceea ce e corect indiferent de formă, înălțime sau cât
// de asimetrică e baza (ex. o piramidă cu vârful din față deplasat lateral).
function solidPolygonVisibility(pts, height, topScale) {
  const n = pts.length;
  const cx = pts.reduce((s, p) => s + p.x, 0) / n;
  const cz = pts.reduce((s, p) => s + p.z, 0) / n;
  const s = (topScale == null ? 0 : topScale) - 1; // 0 -> -1 (piramidă), 1 -> 0 (prismă)
  const a = SOLID_OBLIQUE_K * Math.cos(SOLID_OBLIQUE_ANGLE);
  const b = SOLID_OBLIQUE_K * Math.sin(SOLID_OBLIQUE_ANGLE);
  const vis = [];
  for (let i = 0; i < n; i++) {
    const j = (i + 1) % n;
    const dx = pts[j].x - pts[i].x, dz = pts[j].z - pts[i].z;
    // normala orizontală "spre exterior" a bazei, pt orientarea corectă a normalei feței 3D
    let nxg = dz, nzg = -dx;
    const mx = (pts[i].x + pts[j].x) / 2, mz = (pts[i].z + pts[j].z) / 2;
    if (nxg * (mx - cx) + nzg * (mz - cz) < 0) { nxg = -nxg; nzg = -nzg; }
    const ex = s * (pts[i].x - cx), ez = s * (pts[i].z - cz);
    let Nx = -dz * height, Ny = dz * ex - dx * ez, Nz = dx * height;
    if (Nx * nxg + Nz * nzg < 0) { Nx = -Nx; Ny = -Ny; Nz = -Nz; }
    const NdotD = Nx * (-a) + Ny * (-b) + Nz;
    vis.push(NdotD < -1e-9);
  }
  return vis;
}

// Construiește muchiile pentru o prismă, piramidă sau trunchi de piramidă, pornind de la un
// poligon de bază (basePts), o înălțime și un factor de scalare pentru fața de sus (1 = prismă,
// 0 = piramidă/vârf unic, între 0 și 1 = trunchi de piramidă). Implicit toate muchiile sunt
// continue; dacă SOLID_SHOW_HIDDEN_LINES e activ, muchiile din spate devin întrerupte.
function buildPolygonalSolidLocal(basePts, height, topScale, projectFn, rot, hysteresisDeg) {
  const proj = projectFn || solidProjectGP;
  const n = basePts.length;
  const edgeVis = SOLID_SHOW_HIDDEN_LINES ? solidPolygonVisibility(basePts, height, topScale) : null;
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
    const isVis = !edgeVis || edgeVis[i];
    (isVis ? visible : hidden).push([baseScreen[i], baseScreen[j]]);
  }
  if (topScreen) {
    for (let i = 0; i < n; i++) {
      const j = (i + 1) % n;
      visible.push([topScreen[i], topScreen[j]]);
    }
  }
  for (let i = 0; i < n; i++) {
    const p2 = apexScreen || topScreen[i];
    const isVis = !edgeVis || edgeVis[(i - 1 + n) % n] || edgeVis[i];
    (isVis ? visible : hidden).push([baseScreen[i], p2]);
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
function buildRoundSolidLocal(R1, R2, height, rot) {
  rot = rot || 0;
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

  // Conturul (elipsele) rămâne fix — un cilindru/con arată la fel din orice unghi de rotație în
  // jurul axei sale. Doar punctele folosite pentru liniile tangente/diametru "se rotesc" pe acest
  // contur fix, dând senzația vizuală de rotire a "cusăturii" fără să deformeze silueta reală.
  let idxOffset = Math.round(rot / (2 * Math.PI) * segs);
  idxOffset = ((idxOffset % segs) + segs) % segs;
  const leftIdx = (Math.round(segs / 2) + idxOffset) % segs;
  const rightIdx = idxOffset % segs;
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

// Construiește sfera: un cerc exterior (mereu vizibil) + o elipsă "ecuator" (parțial ascunsă).
// Sfera arată identic din orice unghi de vizualizare, deci nu primește parametru de rotație.
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

// Rotește punctele bazei (plan orizontal x,z) în jurul axei verticale — folosit pentru rotirea
// interactivă a corpurilor cu mâna/mouse-ul.
function rotateGroundPts(pts, angle) {
  if (!angle) return pts;
  const c = Math.cos(angle), s = Math.sin(angle);
  return pts.map(p => ({ x: p.x * c - p.z * s, z: p.x * s + p.z * c }));
}

const SOLID_SHAPES = {
  cub: { label: 'Cub', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRectBase(55, 55), rot), 110, 1, undefined, rot) },
  paralelipiped: { label: 'Paralelipiped dreptunghic', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRectBase(75, 45), rot), 90, 1, undefined, rot) },
  prismaTriunghiulara: { label: 'Prismă triunghiulară', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidTriangleFrontShift(65, 28), rot), 110, 1, undefined, rot) },
  prismaPatrulatera: { label: 'Prismă patrulateră', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRectBase(60, 60), rot), 130, 1, undefined, rot) },
  prismaHexagonala: { label: 'Prismă hexagonală', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidHexagonFrontNudge(75, 240, 1.18), rot), 100, 1, hexProjectGP, rot) },
  piramidaTriunghiulara: { label: 'Piramidă triunghiulară', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidTriangleFrontShift(65, 28), rot), 120, 0, undefined, rot) },
  piramidaPatrulatera: { label: 'Piramidă patrulateră', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRectBase(65, 65), rot), 130, 0, undefined, rot) },
  piramidaHexagonala: { label: 'Piramidă hexagonală', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRegularNGon(6, 75, 240), rot), 130, 0, hexProjectGP, rot) },
  trunchiPiramidaTriunghiulara: { label: 'Trunchiul de piramidă triunghiulară', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidTriangleFrontShift(65, 28), rot), 95, 0.5, undefined, rot) },
  trunchiPiramidaPatrulatera: { label: 'Trunchiul de piramidă patrulateră', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRectBase(70, 70), rot), 95, 0.5, undefined, rot) },
  trunchiPiramidaHexagonala: { label: 'Trunchiul de piramidă hexagonală', kind: 'poly', build: (rot) => buildPolygonalSolidLocal(rotateGroundPts(solidRegularNGon(6, 75, 240), rot), 95, 0.5, hexProjectGP, rot) },
  cilindru: { label: 'Cilindru', kind: 'round', build: (rot) => buildRoundSolidLocal(60, 60, 110, rot) },
  con: { label: 'Con', kind: 'round', build: (rot) => buildRoundSolidLocal(60, 0, 125, rot) },
  trunchiCon: { label: 'Trunchiul de con', kind: 'round', build: (rot) => buildRoundSolidLocal(65, 32, 100, rot) },
  sfera: { label: 'Sferă', kind: 'sphere', noRotate: true, build: () => buildSphereLocal(65) }
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

  // Prisma hexagonală arată mai bine rotită ușor spre dreapta chiar de la afișarea inițială
  // (nu exact la 0°), în loc să pornească nerotită ca restul corpurilor.
  const initialRotationY = shapeKey === 'prismaHexagonala' ? (12 * Math.PI / 180) : 0;
  const built = spec.build(initialRotationY);
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
    rotationY: initialRotationY,
    baseScale: 1,
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

// Reconstruiește un corp 3D la un nou unghi de rotație, păstrând poziția curentă pe ecran
// (centrul conturului) și scara curentă (baseScale) — folosit la rotirea interactivă cu mâna/mouse.
function rotateSolid3D(stroke, newRotationY) {
  const spec = SOLID_SHAPES[stroke.shape];
  if (!spec) return false;
  if (spec.noRotate) return false;

  const allPts = [];
  (stroke.visible || []).forEach(seg => allPts.push(...seg));
  (stroke.hidden || []).forEach(seg => allPts.push(...seg));
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  allPts.forEach(p => {
    if (p.x < minX) minX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x;
    if (p.y > maxY) maxY = p.y;
  });
  const curCenterX = (minX + maxX) / 2, curCenterY = (minY + maxY) / 2;

  const built = spec.build(newRotationY);
  const freshPts = [];
  built.visible.forEach(seg => freshPts.push(...seg));
  built.hidden.forEach(seg => freshPts.push(...seg));
  let fMinX = Infinity, fMinY = Infinity, fMaxX = -Infinity, fMaxY = -Infinity;
  freshPts.forEach(p => {
    if (p.x < fMinX) fMinX = p.x;
    if (p.y < fMinY) fMinY = p.y;
    if (p.x > fMaxX) fMaxX = p.x;
    if (p.y > fMaxY) fMaxY = p.y;
  });
  const freshCenterX = (fMinX + fMaxX) / 2, freshCenterY = (fMinY + fMaxY) / 2;
  const scale = stroke.baseScale || 1;
  const place = p => ({ x: (p.x - freshCenterX) * scale + curCenterX, y: (p.y - freshCenterY) * scale + curCenterY });

  stroke.visible = built.visible.map(seg => seg.map(place));
  stroke.hidden = built.hidden.map(seg => seg.map(place));
  stroke.rotationY = newRotationY;
  return true;
}

// ================================================================
// DESFĂȘURAREA ÎN PLAN A CORPURILOR GEOMETRICE
// ================================================================

// Dintr-o listă de poligoane plane (fiecare = listă de puncte {x,y}), extrage muchiile:
// cele care apar în DOUĂ poligoane (muchie comună = linie de îndoit) devin punctate;
// cele care apar într-un singur poligon (contur exterior, de tăiat) rămân pline.
function netEdgesFromPolygons(polys) {
  const edgeMap = new Map();
  const r = v => Math.round(v * 100) / 100;
  function key(p1, p2) {
    const a = `${r(p1.x)},${r(p1.y)}`, b = `${r(p2.x)},${r(p2.y)}`;
    return a < b ? a + '|' + b : b + '|' + a;
  }
  polys.forEach(poly => {
    const n = poly.length;
    for (let i = 0; i < n; i++) {
      const p1 = poly[i], p2 = poly[(i + 1) % n];
      const k = key(p1, p2);
      if (!edgeMap.has(k)) edgeMap.set(k, { p1, p2, count: 0 });
      edgeMap.get(k).count++;
    }
  });
  const visible = [], hidden = [];
  edgeMap.forEach(e => (e.count > 1 ? hidden : visible).push([e.p1, e.p2]));
  return { visible, hidden };
}

function netNgonFlat(n, R) {
  const pts = [];
  for (let i = 0; i < n; i++) {
    const a = i * 2 * Math.PI / n - Math.PI / 2;
    pts.push({ x: R * Math.cos(a), y: R * Math.sin(a) });
  }
  return pts;
}

// Un n-gon regulat cu o muchie fixată exact la (x0,y0)-(x0+s,y0), extinzându-se mai sus sau mai jos.
function netNgonEdgeAttached(n, s, x0, y0, below) {
  const R = s / (2 * Math.sin(Math.PI / n));
  const apo = s / (2 * Math.tan(Math.PI / n));
  const midX = x0 + s / 2;
  const cy = below ? y0 + apo : y0 - apo;
  const cx = midX;
  const ang0 = Math.atan2(y0 - cy, x0 - cx);
  const step = 2 * Math.PI / n;
  const testX = cx + R * Math.cos(ang0 + step), testY = cy + R * Math.sin(ang0 + step);
  const sign = (Math.abs(testX - (x0 + s)) < 0.05 && Math.abs(testY - y0) < 0.05) ? 1 : -1;
  const pts = [];
  for (let k = 0; k < n; k++) {
    const a = ang0 + sign * step * k;
    pts.push({ x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) });
  }
  return pts;
}

// Ca mai sus, dar muchia poate avea orice orientare (nu doar orizontală) — folosit pt a
// atașa un n-gon la muchia unei alte fețe oriunde ar fi ea în planul desfășurării.
function netNgonAttachedToEdge(n, p1, p2, below) {
  const s = Math.hypot(p2.x - p1.x, p2.y - p1.y);
  const R = s / (2 * Math.sin(Math.PI / n));
  const apo = s / (2 * Math.tan(Math.PI / n));
  const midX = (p1.x + p2.x) / 2, midY = (p1.y + p2.y) / 2;
  const dx = (p2.x - p1.x) / s, dy = (p2.y - p1.y) / s;
  const perpX = -dy, perpY = dx;
  const sign = below ? -1 : 1;
  const cx = midX + perpX * apo * sign, cy = midY + perpY * apo * sign;
  const ang0 = Math.atan2(p1.y - cy, p1.x - cx);
  const step = 2 * Math.PI / n;
  const testX = cx + R * Math.cos(ang0 + step), testY = cy + R * Math.sin(ang0 + step);
  const dirSign = (Math.hypot(testX - p2.x, testY - p2.y) < 0.05) ? 1 : -1;
  const pts = [];
  for (let k = 0; k < n; k++) {
    const a = ang0 + dirSign * step * k;
    pts.push({ x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) });
  }
  return pts;
}

// Cub / paralelipiped / prismă patrulateră: desfășurare "cruce" (6 dreptunghiuri).
function netBoxFaces(W, D, H) {
  const rect = (x0, y0, x1, y1) => [{ x: x0, y: y0 }, { x: x1, y: y0 }, { x: x1, y: y1 }, { x: x0, y: y1 }];
  return [
    rect(0, 0, W, H),
    rect(-D, 0, 0, H),
    rect(W, 0, W + D, H),
    rect(W + D, 0, 2 * W + D, H),
    rect(0, -D, W, 0),
    rect(0, H, W, H + D)
  ];
}

// Prismă (n-gon): fâșie de n dreptunghiuri laterale + cele două baze atașate.
function netPrismFaces(n, R, H) {
  const s = 2 * R * Math.sin(Math.PI / n);
  const faces = [];
  let x = 0;
  for (let i = 0; i < n; i++) {
    faces.push([{ x: x, y: 0 }, { x: x + s, y: 0 }, { x: x + s, y: H }, { x: x, y: H }]);
    x += s;
  }
  faces.push(netNgonEdgeAttached(n, s, 0, 0, false));
  faces.push(netNgonEdgeAttached(n, s, 0, H, true));
  return { faces, s };
}

// Piramidă (n-gon): baza + n triunghiuri isoscele "înflorite" în jurul ei.
function netPyramidFaces(n, R, height) {
  const base = netNgonFlat(n, R);
  const apoBase = R * Math.cos(Math.PI / n);
  const slant = Math.sqrt(height * height + apoBase * apoBase);
  const faces = [base];
  for (let i = 0; i < n; i++) {
    const p1 = base[i], p2 = base[(i + 1) % n];
    const midX = (p1.x + p2.x) / 2, midY = (p1.y + p2.y) / 2;
    const dlen = Math.hypot(midX, midY) || 1;
    const dx = midX / dlen, dy = midY / dlen;
    const apex = { x: midX + dx * slant, y: midY + dy * slant };
    faces.push([p1, p2, apex]);
  }
  return faces;
}

// Trunchi de piramidă (n-gon): baza mare + n trapeze isoscele în jur + vârful mic
// atașat la muchia superioară a primului trapez (participă la împăturire, ca un net real).
function netFrustumFaces(n, R1, R2, height) {
  const base = netNgonFlat(n, R1);
  const apoB = R1 * Math.cos(Math.PI / n), apoT = R2 * Math.cos(Math.PI / n);
  const slant = Math.sqrt(height * height + (apoB - apoT) * (apoB - apoT));
  const s2 = 2 * R2 * Math.sin(Math.PI / n);
  const faces = [base];
  let firstTA = null, firstTB = null;
  for (let i = 0; i < n; i++) {
    const p1 = base[i], p2 = base[(i + 1) % n];
    const midX = (p1.x + p2.x) / 2, midY = (p1.y + p2.y) / 2;
    const dlen = Math.hypot(midX, midY) || 1;
    const dx = midX / dlen, dy = midY / dlen;
    const topMidX = midX + dx * slant, topMidY = midY + dy * slant;
    const perpX = -dy, perpY = dx;
    const t1 = { x: topMidX - perpX * s2 / 2, y: topMidY - perpY * s2 / 2 };
    const t2 = { x: topMidX + perpX * s2 / 2, y: topMidY + perpY * s2 / 2 };
    const dT1P1 = Math.hypot(t1.x - p1.x, t1.y - p1.y), dT1P2 = Math.hypot(t1.x - p2.x, t1.y - p2.y);
    const [tA, tB] = dT1P1 < dT1P2 ? [t1, t2] : [t2, t1];
    faces.push([p1, p2, tB, tA]);
    if (i === 0) { firstTA = tA; firstTB = tB; }
  }
  const topFace = netNgonAttachedToEdge(n, firstTB, firstTA, false);
  faces.push(topFace);
  return faces;
}

function buildNetFromFaces(faces) {
  const built = netEdgesFromPolygons(faces);
  return { visible: built.visible, hidden: built.hidden, faces };
}

// ====================================================================
// ANIMAȚIA DE ÎMPĂTURIRE / DESPĂTURIRE A DESFĂȘURĂRILOR
// (arată procesul, nu doar rezultatul final plat)
// ====================================================================

// ---- vectori & rotații 3D minimale ----
function netVnorm(a) { const l = Math.sqrt(a.x * a.x + a.y * a.y + a.z * a.z) || 1; return { x: a.x / l, y: a.y / l, z: a.z / l }; }
function netMatVec(R, p) {
  return {
    x: R[0] * p.x + R[1] * p.y + R[2] * p.z,
    y: R[3] * p.x + R[4] * p.y + R[5] * p.z,
    z: R[6] * p.x + R[7] * p.y + R[8] * p.z
  };
}
function netMatMul(A, B) {
  const R = new Array(9);
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
    let s = 0;
    for (let k = 0; k < 3; k++) s += A[i * 3 + k] * B[k * 3 + j];
    R[i * 3 + j] = s;
  }
  return R;
}
const NET_MAT_ID = [1, 0, 0, 0, 1, 0, 0, 0, 1];
const NET_RT_ID = { R: NET_MAT_ID, T: { x: 0, y: 0, z: 0 } };

// rotație Rodrigues în jurul unei axe (versor) ce trece prin origine
function netRodrigues(axis, angle) {
  const { x: ux, y: uy, z: uz } = axis;
  const c = Math.cos(angle), s = Math.sin(angle), t = 1 - c;
  return [
    t * ux * ux + c, t * ux * uy - s * uz, t * ux * uz + s * uy,
    t * ux * uy + s * uz, t * uy * uy + c, t * uy * uz - s * ux,
    t * ux * uz - s * uy, t * uy * uz + s * ux, t * uz * uz + c
  ];
}
// rotație în jurul dreptei p1->p2, cu unghi dat — returnează transformarea rigidă {R,T}
function netRotationAboutLine(p1, p2, angle) {
  const axis = netVnorm({ x: p2.x - p1.x, y: p2.y - p1.y, z: 0 });
  const R = netRodrigues(axis, angle);
  const Rp1 = netMatVec(R, { x: p1.x, y: p1.y, z: 0 });
  return { R, T: { x: p1.x - Rp1.x, y: p1.y - Rp1.y, z: -Rp1.z } };
}
function netComposeRT(outer, inner) {
  const R = netMatMul(outer.R, inner.R);
  const Ti = netMatVec(outer.R, inner.T);
  return { R, T: { x: Ti.x + outer.T.x, y: Ti.y + outer.T.y, z: Ti.z + outer.T.z } };
}
function netApplyRT(tr, p) {
  const rp = netMatVec(tr.R, p);
  return { x: rp.x + tr.T.x, y: rp.y + tr.T.y, z: rp.z + tr.T.z };
}
// proiecție pseudo-3D: privim de sus, ușor înclinat (tilt), pt un efect vizual de adâncime
function netProject(p3, tilt) {
  return { x: p3.x, y: p3.y * Math.cos(tilt) - p3.z * Math.sin(tilt) };
}
// proiecție 3D->2D pt animație: la t=1 e IDENTICĂ cu proiecția oblică folosită de corpurile 3D
// reale (solidProjectGP), la t=0 devine o proiecție plată de sus (exact desfășurarea statică) —
// asigură că forma de start a animației arată exact ca desenul din butonul "Corpuri geometrice".
function netProjectAssembled(p3, t) {
  const Kc = SOLID_OBLIQUE_K * Math.cos(SOLID_OBLIQUE_ANGLE);
  const Ks = SOLID_OBLIQUE_K * Math.sin(SOLID_OBLIQUE_ANGLE);
  return {
    x: p3.x + t * Kc * p3.y,
    y: (1 - t) * p3.y - t * p3.z - t * Ks * p3.y
  };
}
function netEase(x) { return x < 0.5 ? 4 * x * x * x : 1 - Math.pow(-2 * x + 2, 3) / 2; }

// unghiul diedru corect de îndoire pt fiecare tip de desfășurare (nu un 90° arbitrar):
// - box: fețele laterale sunt mereu perpendiculare pe bază -> 90°
// - prism: fâșia laterală se împăturește cu unghiul exterior al poligonului (360°/n) între
//   fețele laterale consecutive, iar capacele se ridică perpendicular (90°) pe fâșie
// - piramidă: unghiul la care trebuie ridicată fața triunghiulară ca vârful să ajungă la
//   înălțimea reală = arctan(înălțime / apotema bazei)
// - trunchi de piramidă: analog, cu diferența de apoteme în loc de apotema simplă
function netHingeMaxAngle(netKind, p, childFaceIdx) {
  if (netKind === 'prism') {
    return childFaceIdx < p.n ? (2 * Math.PI / p.n) : Math.PI / 2;
  }
  if (netKind === 'pyramid') {
    const apo = p.R * Math.cos(Math.PI / p.n);
    return Math.PI - Math.atan2(p.height, apo);
  }
  if (netKind === 'frustum') {
    const apoB = p.R1 * Math.cos(Math.PI / p.n), apoT = p.R2 * Math.cos(Math.PI / p.n);
    const delta1 = Math.PI - Math.atan2(p.height, Math.abs(apoB - apoT));
    // capacul mic e atașat la primul trapez lateral (nu la bază) — axele celor două
    // balamale (bază→trapez și trapez→capac) sunt paralele, deci unghiurile se compun
    // prin adunare; ca planul capacului să ajungă orizontal (paralel cu baza), suma
    // trebuie să fie 180°.
    if (childFaceIdx > p.n) return Math.PI - delta1;
    return delta1;
  }
  return Math.PI / 2; // box / implicit
}
function netAnnotateHingeAngles(forest, netKind, p) {
  forest.hinge.forEach((h, idx) => {
    if (!h) return;
    h.maxAngle = netHingeMaxAngle(netKind, p, idx);
  });
}

// ---- construiește arborele de "balamale" dintr-o listă de fețe (poligoane 2D) ----
function netFacesTopology(faces) {
  const r = v => Math.round(v * 100) / 100;
  const ptKey = p => r(p.x) + ',' + r(p.y);
  const edgeMap = new Map();
  faces.forEach((poly, fi) => {
    const n = poly.length;
    for (let i = 0; i < n; i++) {
      const p1 = poly[i], p2 = poly[(i + 1) % n];
      const a = ptKey(p1), b = ptKey(p2);
      const k = a < b ? a + '|' + b : b + '|' + a;
      if (!edgeMap.has(k)) edgeMap.set(k, []);
      edgeMap.get(k).push({ faceIdx: fi, i });
    }
  });
  const edgeEntries = [...edgeMap.values()];
  const edgesIndexed = edgeEntries.map(list => ({ ref: list[0], hidden: list.length > 1 }));
  const adj = faces.map(() => []);
  edgeEntries.forEach(list => {
    if (list.length === 2 && list[0].faceIdx !== list[1].faceIdx) {
      const [a, b] = list;
      adj[a.faceIdx].push({ other: b.faceIdx, i: a.i });
      adj[b.faceIdx].push({ other: a.faceIdx, i: b.i });
    }
  });
  return { edgesIndexed, adj };
}

function buildHingeForest(faces) {
  const { edgesIndexed, adj } = netFacesTopology(faces);
  const n = faces.length;
  const parent = new Array(n).fill(-1);
  const hinge = new Array(n).fill(null);
  const visited = new Array(n).fill(false);
  for (let start = 0; start < n; start++) {
    if (visited[start]) continue;
    visited[start] = true;
    const queue = [start];
    while (queue.length) {
      const cur = queue.shift();
      adj[cur].forEach(({ other, i }) => {
        if (visited[other]) return;
        visited[other] = true;
        parent[other] = cur;
        const poly = faces[cur];
        const p1 = poly[i], p2 = poly[(i + 1) % poly.length];
        // semn ales ca fața copil să se "ridice" (z pozitiv) când se împăturește
        const hd = netVnorm({ x: p2.x - p1.x, y: p2.y - p1.y, z: 0 });
        let ccx = 0, ccy = 0;
        faces[other].forEach(pt => { ccx += pt.x; ccy += pt.y; });
        ccx /= faces[other].length; ccy /= faces[other].length;
        const toC = { x: ccx - p1.x, y: ccy - p1.y };
        const sign = (hd.x * toC.y - hd.y * toC.x) >= 0 ? 1 : -1;
        hinge[other] = { p1, p2, sign };
        queue.push(other);
      });
    }
  }
  return { parent, hinge, edgesIndexed };
}

function netFaceTransforms(faces, parent, hinge, t) {
  const n = faces.length;
  const transforms = new Array(n);
  const done = new Array(n).fill(false);
  function resolve(i) {
    if (done[i]) return transforms[i];
    if (parent[i] === -1) {
      transforms[i] = NET_RT_ID;
    } else {
      const pT = resolve(parent[i]);
      const h = hinge[i];
      const maxAngle = h.maxAngle != null ? h.maxAngle : Math.PI / 2;
      transforms[i] = netComposeRT(pT, netRotationAboutLine(h.p1, h.p2, t * maxAngle * h.sign));
    }
    done[i] = true;
    return transforms[i];
  }
  for (let i = 0; i < n; i++) resolve(i);
  return transforms;
}

// construiește o funcție renderAt(t) reutilizabilă atât de auto-play cât și de slider-ul manual
// (t: 1 = asamblat ca la "Corpuri geometrice" -> 0 = plat/desfășurat complet)
function makeNetRenderer(faces, forest, shiftPoint, strokeColor, lineSize) {
  const { parent, hinge, edgesIndexed } = forest;
  return function renderAt(t) {
    const transforms = netFaceTransforms(faces, parent, hinge, t);
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    overlayCtx.save();
    overlayCtx.lineJoin = 'round';
    overlayCtx.lineCap = 'round';
    overlayCtx.strokeStyle = strokeColor;
    edgesIndexed.forEach(({ ref, hidden }) => {
      const poly = faces[ref.faceIdx];
      const i1 = ref.i, i2 = (ref.i + 1) % poly.length;
      const tr = transforms[ref.faceIdx];
      const a3 = netApplyRT(tr, { x: poly[i1].x, y: poly[i1].y, z: 0 });
      const b3 = netApplyRT(tr, { x: poly[i2].x, y: poly[i2].y, z: 0 });
      const a = shiftPoint(netProjectAssembled(a3, t));
      const b = shiftPoint(netProjectAssembled(b3, t));
      overlayCtx.globalAlpha = hidden ? 0.5 : 1;
      overlayCtx.lineWidth = hidden ? Math.max(1, lineSize * 0.75) : lineSize;
      overlayCtx.setLineDash(hidden ? [lineSize * 3, lineSize * 2.4] : []);
      overlayCtx.beginPath();
      overlayCtx.moveTo(a.x, a.y);
      overlayCtx.lineTo(b.x, b.y);
      overlayCtx.stroke();
    });
    overlayCtx.restore();
  };
}

function makeCylinderRenderer(R, H, shiftPoint, strokeColor, lineSize) {
  const circumf = 2 * Math.PI * R;
  const segs = 48, nSub = 24;
  const eX = Math.max(1, circumf * 0.002), eY = Math.max(0.5, H * 0.01);
  return function renderAt(t) {
    const b = t, tilt = t * 0.55;
    const angleTotal = b * 2 * Math.PI;
    const radiusB = angleTotal > 1e-4 ? circumf / angleTotal : null;
    const bend = (x, y) => {
      if (radiusB === null) return { x: x - circumf / 2, y, z: 0 };
      const theta = (x / circumf - 0.5) * angleTotal;
      return { x: radiusB * Math.sin(theta), y, z: radiusB * (1 - Math.cos(theta)) };
    };
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    overlayCtx.save();
    overlayCtx.lineJoin = 'round';
    overlayCtx.lineCap = 'round';
    overlayCtx.strokeStyle = strokeColor;
    overlayCtx.lineWidth = lineSize;
    overlayCtx.setLineDash([]);
    overlayCtx.globalAlpha = 1;
    const seg = (p1, p2) => {
      const a = shiftPoint(netProject(p1, tilt)), c = shiftPoint(netProject(p2, tilt));
      overlayCtx.beginPath(); overlayCtx.moveTo(a.x, a.y); overlayCtx.lineTo(c.x, c.y); overlayCtx.stroke();
    };
    for (let i = 0; i < nSub; i++) {
      const x1 = circumf * i / nSub, x2 = circumf * (i + 1) / nSub;
      seg(bend(x1, 0), bend(x2, 0));
      seg(bend(x1, H), bend(x2, H));
    }
    seg(bend(0, 0), bend(0, H));
    seg(bend(circumf, 0), bend(circumf, H));
    // capacele: atașate printr-o balama reală (rotație rigidă la punctul de tangență)
    [[0, -1, -R], [H, 1, H + R]].forEach(([y0, flipSign, cy0]) => {
      const x0 = circumf / 2;
      const bend2 = (x, y) => bend(x, y);
      const attachFlat = { x: x0 - circumf / 2, y: y0, z: 0 };
      const foldAt = (px, py) => threeFoldCapPoint(bend2, x0, y0, px - attachFlat.x, py - attachFlat.y, t, eX, eY, flipSign);
      const pts = []; for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; pts.push(foldAt(R * Math.cos(a), cy0 + R * Math.sin(a))); }
      for (let i = 0; i < segs; i++) seg(pts[i], pts[i + 1]);
    });
    overlayCtx.restore();
  };
}

function makeConeRenderer(R, G, shiftPoint, strokeColor, lineSize) {
  const angle = 2 * Math.PI * R / G, halfAngle = angle / 2;
  const alpha = Math.asin(Math.min(1, R / G));
  const segs = 48;
  const ptAt = (r, a, b) => {
    const flat = { x: r * Math.sin(a), y: -r * Math.cos(a), z: 0 };
    if (b <= 0.0005) return flat;
    const phi = a * (Math.PI / halfAngle);
    const radial = r * Math.sin(alpha), axisH = r * Math.cos(alpha);
    const closed = { x: radial * Math.cos(phi), y: radial * Math.sin(phi), z: axisH };
    return { x: flat.x + (closed.x - flat.x) * b, y: flat.y + (closed.y - flat.y) * b, z: flat.z + (closed.z - flat.z) * b };
  };
  return function renderAt(t) {
    const b = t, tilt = t * 0.55;
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    overlayCtx.save();
    overlayCtx.lineJoin = 'round';
    overlayCtx.lineCap = 'round';
    overlayCtx.strokeStyle = strokeColor;
    overlayCtx.lineWidth = lineSize;
    overlayCtx.setLineDash([]);
    overlayCtx.globalAlpha = 1;
    const seg = (p1, p2) => {
      const a = shiftPoint(netProject(p1, tilt)), c = shiftPoint(netProject(p2, tilt));
      overlayCtx.beginPath(); overlayCtx.moveTo(a.x, a.y); overlayCtx.lineTo(c.x, c.y); overlayCtx.stroke();
    };
    for (let i = 0; i < segs; i++) {
      const a1 = -halfAngle + angle * i / segs, a2 = -halfAngle + angle * (i + 1) / segs;
      seg(ptAt(G, a1, b), ptAt(G, a2, b));
    }
    seg(ptAt(0, 0, b), ptAt(G, -halfAngle, b));
    seg(ptAt(0, 0, b), ptAt(G, halfAngle, b));
    // capacul: atașat prin interpolare analitică (plat -> perpendicular pe axă)
    const cy0 = -G - R;
    const pts = []; for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; pts.push(threeConeCapPoint(R * Math.cos(a), cy0 + R * Math.sin(a), G, alpha, b)); }
    for (let i = 0; i < segs; i++) seg(pts[i], pts[i + 1]);
    overlayCtx.restore();
  };
}

function makeConeFrustumRenderer(R1, R2, Gf, shiftPoint, strokeColor, lineSize) {
  const rInner = Gf * R2 / (R1 - R2);
  const rOuter = rInner + Gf;
  const angle = 2 * Math.PI * R1 / rOuter, halfAngle = angle / 2;
  const alpha = Math.asin(Math.min(1, R1 / rOuter));
  const segs = 48;
  const ptAt = (r, a, b) => {
    const flat = { x: r * Math.sin(a), y: -r * Math.cos(a), z: 0 };
    if (b <= 0.0005) return flat;
    const phi = a * (Math.PI / halfAngle);
    const radial = r * Math.sin(alpha), axisH = r * Math.cos(alpha);
    const closed = { x: radial * Math.cos(phi), y: radial * Math.sin(phi), z: axisH };
    return { x: flat.x + (closed.x - flat.x) * b, y: flat.y + (closed.y - flat.y) * b, z: flat.z + (closed.z - flat.z) * b };
  };
  return function renderAt(t) {
    const b = t, tilt = t * 0.55;
    overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
    overlayCtx.save();
    overlayCtx.lineJoin = 'round';
    overlayCtx.lineCap = 'round';
    overlayCtx.strokeStyle = strokeColor;
    overlayCtx.lineWidth = lineSize;
    overlayCtx.setLineDash([]);
    overlayCtx.globalAlpha = 1;
    const seg = (p1, p2) => {
      const a = shiftPoint(netProject(p1, tilt)), c = shiftPoint(netProject(p2, tilt));
      overlayCtx.beginPath(); overlayCtx.moveTo(a.x, a.y); overlayCtx.lineTo(c.x, c.y); overlayCtx.stroke();
    };
    for (let i = 0; i < segs; i++) {
      const a1 = -halfAngle + angle * i / segs, a2 = -halfAngle + angle * (i + 1) / segs;
      seg(ptAt(rOuter, a1, b), ptAt(rOuter, a2, b));
      seg(ptAt(rInner, a1, b), ptAt(rInner, a2, b));
    }
    seg(ptAt(rInner, -halfAngle, b), ptAt(rOuter, -halfAngle, b));
    seg(ptAt(rInner, halfAngle, b), ptAt(rOuter, halfAngle, b));
    // ambele capace: atașate prin rotație rigidă, tangente la razele reale — capacul mic se
    // extinde spre originea desfășurării (ca să nu se suprapună cu sectorul lateral), deci
    // folosește o rotație diferită (90°, nu 180° ca cel mare)
    [[rOuter, -rOuter - R1, R1, -1], [rInner, -rInner + R2, R2, 1]].forEach(([rAttach, cy0, r, extendSign]) => {
      const pts = []; for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; pts.push(threeConeCapPoint(r * Math.cos(a), cy0 + r * Math.sin(a), rAttach, alpha, b, extendSign)); }
      for (let i = 0; i < segs; i++) seg(pts[i], pts[i + 1]);
    });
    overlayCtx.restore();
  };
}

// ---- panoul cu slider interactiv: control manual al împăturirii/rulării ----
function netCreateSliderPanel(label) {
  const wrap = document.createElement('div');
  wrap.id = 'net-slider-panel';
  wrap.style.cssText = 'position:fixed; left:50%; bottom:44px; transform:translateX(-50%);'
    + 'background:#222; color:#fff; padding:10px 16px; border-radius:10px; font-size:13px; z-index:200;'
    + 'display:flex; flex-direction:column; gap:6px; width:min(92vw,420px); box-shadow:0 4px 18px rgba(0,0,0,0.4);'
    + 'font-family:inherit;';
  wrap.innerHTML =
    '<div style="display:flex; align-items:center; justify-content:space-between;">' +
    '<span style="font-weight:600;">' + label + '</span>' +
    '<span id="net-slider-pct" style="opacity:0.75;">0%</span>' +
    '</div>' +
    '<input id="net-slider-input" type="range" min="0" max="100" value="0" step="1" style="width:100%; accent-color:#4da3ff;">' +
    '<div style="display:flex; align-items:center; justify-content:space-between; font-size:11px; opacity:0.7;">' +
    '<span>◀ Asamblat</span><span>Desfășurat ▶</span>' +
    '</div>' +
    '<div style="display:flex; gap:8px; justify-content:flex-end; margin-top:2px;">' +
    '<button id="net-slider-cancel" style="background:#3a3a3a; color:#fff; border:none; border-radius:6px; padding:7px 12px; font-size:12px;">✕ Renunță</button>' +
    '<button id="net-slider-done" style="background:#4da3ff; color:#fff; border:none; border-radius:6px; padding:7px 14px; font-size:12px; font-weight:600;">✓ Gata</button>' +
    '</div>';
  document.body.appendChild(wrap);
  return {
    el: wrap,
    slider: wrap.querySelector('#net-slider-input'),
    pctLabel: wrap.querySelector('#net-slider-pct'),
    doneBtn: wrap.querySelector('#net-slider-done'),
    cancelBtn: wrap.querySelector('#net-slider-cancel'),
    destroy() { wrap.remove(); }
  };
}

// rulează animația automat o dată, apoi lasă sliderul deschis pt control manual;
// se rezolvă cu true dacă utilizatorul apasă "Gata", sau false dacă apasă "Renunță"
function netRunInteractive(renderAt, label, autoplayDuration) {
  return new Promise(resolve => {
    const panel = netCreateSliderPanel(label);
    let userInteracting = false;
    let rafId = null;

    function setT(t) {
      const pct = Math.round((1 - t) * 100);
      panel.slider.value = String(pct);
      panel.pctLabel.textContent = pct + '%';
      renderAt(t);
    }

    setT(1); // start: complet asamblat, ca la "Corpuri geometrice"

    const start = performance.now();
    function frame(now) {
      if (userInteracting) return;
      const p = Math.min(1, (now - start) / autoplayDuration);
      const t = 1 - netEase(p);
      setT(t);
      if (p < 1) rafId = requestAnimationFrame(frame);
    }
    rafId = requestAnimationFrame(frame);

    const stopAutoplay = () => { userInteracting = true; if (rafId) cancelAnimationFrame(rafId); };
    panel.slider.addEventListener('pointerdown', stopAutoplay);
    panel.slider.addEventListener('input', () => {
      stopAutoplay();
      const pct = parseInt(panel.slider.value, 10);
      panel.pctLabel.textContent = pct + '%';
      renderAt(1 - pct / 100);
    });

    function finish(result) {
      if (rafId) cancelAnimationFrame(rafId);
      panel.destroy();
      resolve(result);
    }
    panel.doneBtn.addEventListener('click', () => finish(true));
    panel.cancelBtn.addEventListener('click', () => finish(false));
  });
}

// Cilindru: dreptunghi (circumferință × înălțime) + 2 cercuri, tangente la marginile lungi.
function buildCylinderNet(R, H) {
  const circumf = 2 * Math.PI * R;
  const visible = [];
  visible.push([{ x: 0, y: 0 }, { x: circumf, y: 0 }]);
  visible.push([{ x: circumf, y: 0 }, { x: circumf, y: H }]);
  visible.push([{ x: circumf, y: H }, { x: 0, y: H }]);
  visible.push([{ x: 0, y: H }, { x: 0, y: 0 }]);
  const segs = 48;
  function circle(cx, cy) {
    const pts = [];
    for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; pts.push({ x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) }); }
    for (let i = 0; i < segs; i++) visible.push([pts[i], pts[i + 1]]);
  }
  circle(circumf / 2, -R);
  circle(circumf / 2, H + R);
  return { visible, hidden: [] };
}

// Con: sector circular (rază = apotema laterală G) + 1 cerc, tangent la arc.
function buildConeNet(R, G) {
  const angle = 2 * Math.PI * R / G;
  const visible = [];
  const segs = 48;
  const arcPts = [];
  for (let i = 0; i <= segs; i++) {
    const a = -angle / 2 + angle * i / segs;
    arcPts.push({ x: G * Math.sin(a), y: -G * Math.cos(a) });
  }
  for (let i = 0; i < segs; i++) visible.push([arcPts[i], arcPts[i + 1]]);
  visible.push([{ x: 0, y: 0 }, arcPts[0]]);
  visible.push([{ x: 0, y: 0 }, arcPts[segs]]);
  const circleCenter = { x: 0, y: -G - R };
  const circlePts = [];
  for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; circlePts.push({ x: circleCenter.x + R * Math.cos(a), y: circleCenter.y + R * Math.sin(a) }); }
  for (let i = 0; i < segs; i++) visible.push([circlePts[i], circlePts[i + 1]]);
  return { visible, hidden: [] };
}

// Trunchi de con: sector inelar (între două arce) + 2 cercuri.
function buildConeFrustumNet(R1, R2, Gf) {
  const rInner = Gf * R2 / (R1 - R2);
  const rOuter = rInner + Gf;
  const angle = 2 * Math.PI * R1 / rOuter;
  const segs = 48;
  const visible = [];
  const outerPts = [], innerPts = [];
  for (let i = 0; i <= segs; i++) {
    const a = -angle / 2 + angle * i / segs;
    outerPts.push({ x: rOuter * Math.sin(a), y: -rOuter * Math.cos(a) });
    innerPts.push({ x: rInner * Math.sin(a), y: -rInner * Math.cos(a) });
  }
  for (let i = 0; i < segs; i++) visible.push([outerPts[i], outerPts[i + 1]]);
  for (let i = 0; i < segs; i++) visible.push([innerPts[i], innerPts[i + 1]]);
  visible.push([innerPts[0], outerPts[0]]);
  visible.push([innerPts[segs], outerPts[segs]]);
  const bigCenter = { x: 0, y: -rOuter - R1 };
  const bigPts = [];
  for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; bigPts.push({ x: bigCenter.x + R1 * Math.cos(a), y: bigCenter.y + R1 * Math.sin(a) }); }
  for (let i = 0; i < segs; i++) visible.push([bigPts[i], bigPts[i + 1]]);
  const smallCenter = { x: 0, y: -rInner + R2 };
  const smallPts = [];
  for (let i = 0; i <= segs; i++) { const a = i / segs * 2 * Math.PI; smallPts.push({ x: smallCenter.x + R2 * Math.cos(a), y: smallCenter.y + R2 * Math.sin(a) }); }
  for (let i = 0; i < segs; i++) visible.push([smallPts[i], smallPts[i + 1]]);
  return { visible, hidden: [] };
}

const NET_SHAPES = {
  cub: { label: 'Cub (desfășurare)', build: () => buildNetFromFaces(netBoxFaces(90, 90, 90)), netKind: 'box' },
  paralelipiped: { label: 'Paralelipiped (desfășurare)', build: () => buildNetFromFaces(netBoxFaces(110, 60, 70)), netKind: 'box' },
  prismaTriunghiulara: { label: 'Prismă triunghiulară (desfășurare)', build: () => buildNetFromFaces(netPrismFaces(3, 55, 110).faces), netKind: 'prism', netParams: { n: 3 } },
  prismaPatrulatera: { label: 'Prismă patrulateră (desfășurare)', build: () => buildNetFromFaces(netBoxFaces(85, 85, 120)), netKind: 'box' },
  prismaHexagonala: { label: 'Prismă hexagonală (desfășurare)', build: () => buildNetFromFaces(netPrismFaces(6, 45, 95).faces), netKind: 'prism', netParams: { n: 6 } },
  piramidaTriunghiulara: { label: 'Piramidă triunghiulară (desfășurare)', build: () => buildNetFromFaces(netPyramidFaces(3, 55, 110)), netKind: 'pyramid', netParams: { n: 3, R: 55, height: 110 } },
  piramidaPatrulatera: { label: 'Piramidă patrulateră (desfășurare)', build: () => buildNetFromFaces(netPyramidFaces(4, 55, 115)), netKind: 'pyramid', netParams: { n: 4, R: 55, height: 115 } },
  piramidaHexagonala: { label: 'Piramidă hexagonală (desfășurare)', build: () => buildNetFromFaces(netPyramidFaces(6, 50, 120)), netKind: 'pyramid', netParams: { n: 6, R: 50, height: 120 } },
  trunchiPiramidaTriunghiulara: { label: 'Trunchi piramidă triunghiulară (desfășurare)', build: () => buildNetFromFaces(netFrustumFaces(3, 60, 33, 85)), netKind: 'frustum', netParams: { n: 3, R1: 60, R2: 33, height: 85 } },
  trunchiPiramidaPatrulatera: { label: 'Trunchi piramidă patrulateră (desfășurare)', build: () => buildNetFromFaces(netFrustumFaces(4, 60, 33, 85)), netKind: 'frustum', netParams: { n: 4, R1: 60, R2: 33, height: 85 } },
  trunchiPiramidaHexagonala: { label: 'Trunchi piramidă hexagonală (desfășurare)', build: () => buildNetFromFaces(netFrustumFaces(6, 55, 30, 85)), netKind: 'frustum', netParams: { n: 6, R1: 55, R2: 30, height: 85 } },
  cilindru: { label: 'Cilindru (desfășurare)', build: () => buildCylinderNet(45, 110), curved: 'cilindru', params: { R: 45, H: 110 } },
  con: { label: 'Con (desfășurare)', build: () => buildConeNet(50, 120), curved: 'con', params: { R: 50, G: 120 } },
  trunchiCon: { label: 'Trunchi de con (desfășurare)', build: () => buildConeFrustumNet(55, 28, 95), curved: 'trunchiCon', params: { R1: 55, R2: 28, Gf: 95 } }
};

function buildNetIconSVG(shapeKey, size) {
  const spec = NET_SHAPES[shapeKey];
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
    lines += `<line x1="${a.x.toFixed(1)}" y1="${a.y.toFixed(1)}" x2="${b.x.toFixed(1)}" y2="${b.y.toFixed(1)}" stroke-dasharray="2,2"/>`;
  });
  built.visible.forEach(seg => {
    const a = tp(seg[0]), b = tp(seg[1]);
    lines += `<line x1="${a.x.toFixed(1)}" y1="${a.y.toFixed(1)}" x2="${b.x.toFixed(1)}" y2="${b.y.toFixed(1)}"/>`;
  });
  return `<svg width="${size}" height="${size}" viewBox="0 0 ${size} ${size}" fill="none" stroke="currentColor" stroke-width="1.3" stroke-linecap="round">${lines}</svg>`;
}

async function insertSolidNet(shapeKey) {
  const spec = NET_SHAPES[shapeKey];
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
  const w = maxX - minX, h = maxY - minY;
  // scalăm dacă desfășurarea e prea mare pentru fereastra curentă
  const fitScale = Math.min(1, (rect.width * 0.7) / w, (rect.height * 0.6) / h);
  const cx = rect.width / 2, cy = rect.height * 0.32;
  const shift = seg => seg.map(p => ({
    x: (p.x - (minX + maxX) / 2) * fitScale + cx,
    y: (p.y - (minY + maxY) / 2) * fitScale + cy
  }));
  const shiftPoint = p => ({
    x: (p.x - (minX + maxX) / 2) * fitScale + cx,
    y: (p.y - (minY + maxY) / 2) * fitScale + cy
  });

  // ---- construim funcția de randare renderAt(t) potrivită formei, apoi arătăm panoul
  //      cu slider: se joacă animația o dată automat, iar utilizatorul poate apoi trage
  //      manual de slider între "Asamblat" (ca la Corpuri geometrice) și "Desfășurat" ----
  const netLineSize = 2.2;
  let renderAt = null;
  if (built.faces && built.faces.length) {
    const forest = buildHingeForest(built.faces);
    netAnnotateHingeAngles(forest, spec.netKind, spec.netParams);
    renderAt = makeNetRenderer(built.faces, forest, shiftPoint, color, netLineSize);
  } else if (spec.curved === 'cilindru') {
    const { R, H } = spec.params;
    renderAt = makeCylinderRenderer(R, H, shiftPoint, color, netLineSize);
  } else if (spec.curved === 'con') {
    const { R, G } = spec.params;
    renderAt = makeConeRenderer(R, G, shiftPoint, color, netLineSize);
  } else if (spec.curved === 'trunchiCon') {
    const { R1, R2, Gf } = spec.params;
    renderAt = makeConeFrustumRenderer(R1, R2, Gf, shiftPoint, color, netLineSize);
  }

  let confirmed = true;
  if (renderAt) {
    try {
      confirmed = await netRunInteractive(renderAt, spec.label, 1500);
    } catch (e) {
      console.warn('Eroare animație desfășurare:', e);
    }
  }
  overlayCtx.clearRect(0, 0, overlayC.width, overlayC.height);
  if (!confirmed) { showToast('Desfășurare anulată'); return; }

  const stroke = {
    type: 'solidNet',
    shape: shapeKey,
    color: color,
    size: netLineSize,
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
confirmModalBackdrop.addEventListener('pointerdown', (e) => {
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

// ====================================================================
// MODUL 3D INTERACTIV — corpurile geometrice pot fi rotite liber (ca în
// Blender: tragi cu degetul/mouse-ul, ciupești pt zoom), fețele sunt ușor
// transparente (se văd și muchiile din plan secundar), iar un slider permite
// animarea desfășurării în plan a corpului, direct în spațiul 3D (aceeași
// matematică de împăturire — unghiuri diedre corecte — ca la desfășurările
// 2D, dar aplicată acum ca poziții 3D reale, nu ca proiecție pe canvas).
// La apăsarea "Inserează" se face o "poză" (PNG) a stării curente (asamblat,
// pe jumătate desfăcut sau complet plat, din orice unghi), adăugată pe tablă
// ca o imagine obișnuită (selectabilă/mutabilă/redimensionabilă).
// ====================================================================
const THREE_SOLID_COLOR = 0x5b8def;
const THREE_FACE_OPACITY = 0.45;

function threeMakeFaceMaterial() {
  return new THREE.MeshPhongMaterial({
    color: THREE_SOLID_COLOR, shininess: 25, flatShading: true,
    side: THREE.DoubleSide, transparent: true, opacity: THREE_FACE_OPACITY, depthWrite: false
  });
}
function threeMakeEdgeMaterial() {
  // depthTest:false -> muchiile din plan secundar rămân vizibile prin fețele transparente
  return new THREE.LineBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.95, depthTest: false });
}
// convenția rețelei plate: x = stânga-dreapta, y = adâncimea din desfășurarea
// plată, z = înălțimea de împăturire -> în Three.js (Y = sus) mapăm z->Y, y->Z
function threeRemap(p) { return { x: p.x, y: p.z, z: p.y }; }

// ---- grup animat pt desfășurări poligonale (cub, paralelipiped, prisme, piramide, trunchiuri) ----
function buildAnimatedPolyNetGroup(faces, forest) {
  const faceTris = faces.map(poly => {
    const idx = [];
    for (let i = 1; i < poly.length - 1; i++) idx.push([0, i, i + 1]);
    return idx;
  });
  const totalTris = faceTris.reduce((s, t) => s + t.length, 0);

  const faceGeo = new THREE.BufferGeometry();
  faceGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(totalTris * 9), 3));
  const faceMesh = new THREE.Mesh(faceGeo, threeMakeFaceMaterial());

  const edgeGeo = new THREE.BufferGeometry();
  edgeGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(forest.edgesIndexed.length * 6), 3));
  const edgeLines = new THREE.LineSegments(edgeGeo, threeMakeEdgeMaterial());
  edgeLines.renderOrder = 10;

  const group = new THREE.Group();
  group.add(faceMesh, edgeLines);

  function updateAt(t) {
    const transforms = netFaceTransforms(faces, forest.parent, forest.hinge, t);
    const fPos = faceGeo.attributes.position.array;
    let vi = 0;
    faces.forEach((poly, fi) => {
      const tr = transforms[fi];
      const pts3 = poly.map(p => threeRemap(netApplyRT(tr, { x: p.x, y: p.y, z: 0 })));
      faceTris[fi].forEach(([a, b, c]) => {
        [pts3[a], pts3[b], pts3[c]].forEach(p => { fPos[vi++] = p.x; fPos[vi++] = p.y; fPos[vi++] = p.z; });
      });
    });
    faceGeo.attributes.position.needsUpdate = true;
    faceGeo.computeVertexNormals();
    faceGeo.computeBoundingSphere();

    const ePos = edgeGeo.attributes.position.array;
    let ei = 0;
    forest.edgesIndexed.forEach(({ ref }) => {
      const poly = faces[ref.faceIdx];
      const tr = transforms[ref.faceIdx];
      const i1 = ref.i, i2 = (ref.i + 1) % poly.length;
      const a3 = threeRemap(netApplyRT(tr, { x: poly[i1].x, y: poly[i1].y, z: 0 }));
      const b3 = threeRemap(netApplyRT(tr, { x: poly[i2].x, y: poly[i2].y, z: 0 }));
      ePos[ei++] = a3.x; ePos[ei++] = a3.y; ePos[ei++] = a3.z;
      ePos[ei++] = b3.x; ePos[ei++] = b3.y; ePos[ei++] = b3.z;
    });
    edgeGeo.attributes.position.needsUpdate = true;
    edgeGeo.computeBoundingSphere();
  }
  updateAt(1);
  return { group, updateAt };
}

// ---- grup animat generic pt suprafețe curbe (cilindru / con / trunchi de con) ----
// bendFn(x, y, t) -> {x,y,z} pe rețeaua plată la parametrul de împăturire t (1=asamblat, 0=plat)
// caps: listă de {cy0, r} pt discurile capacelor (0, 1 sau 2 capace)
// îndoaie un punct al unui capac (disc) în jurul liniei tangente la marginea curbă de care
// e atașat, la parametrul curent de asamblare — cadrul local (tangentă + direcție de
// extindere) se calculează numeric (derivată), ca să funcționeze la fel pt orice
// parametrizare (cilindru: x=poziție pe circumferință, con/trunchi: x=unghi, y=rază).
function threeFoldCapPoint(bend2, x0, y0, dx, dy, foldFrac, epsX, epsY, flipSign) {
  const P = bend2(x0, y0);
  const A1 = bend2(x0 - epsX, y0), B1 = bend2(x0 + epsX, y0);
  const e1 = netVnorm({ x: B1.x - A1.x, y: B1.y - A1.y, z: B1.z - A1.z });
  const A2 = bend2(x0, y0 - epsY), B2 = bend2(x0, y0 + epsY);
  const e2 = netVnorm({ x: B2.x - A2.x, y: B2.y - A2.y, z: B2.z - A2.z });
  const e3 = netVnorm({ x: e1.y * e2.z - e1.z * e2.y, y: e1.z * e2.x - e1.x * e2.z, z: e1.x * e2.y - e1.y * e2.x });
  const phi = (Math.PI / 2) * foldFrac * flipSign;
  const c = Math.cos(phi), s = Math.sin(phi);
  return {
    x: P.x + dx * e1.x + dy * (c * e2.x + s * e3.x),
    y: P.y + dx * e1.y + dy * (c * e2.y + s * e3.y),
    z: P.z + dx * e1.z + dy * (c * e2.z + s * e3.z)
  };
}

function buildAnimatedCurvedGroup(xMax, H, bendFn, caps) {
  const nSub = 48, segs = 48;
  const group = new THREE.Group();

  const lateralGeo = new THREE.BufferGeometry();
  lateralGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(nSub * 6 * 3), 3));
  const lateralMesh = new THREE.Mesh(lateralGeo, threeMakeFaceMaterial());
  group.add(lateralMesh);

  const edgeGeo = new THREE.BufferGeometry();
  edgeGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array((nSub * 2 + 2) * 2 * 3), 3));
  const edgeLines = new THREE.LineSegments(edgeGeo, threeMakeEdgeMaterial());
  edgeLines.renderOrder = 10;
  group.add(edgeLines);

  const capMeshes = caps.map(() => {
    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(segs * 9), 3));
    const mesh = new THREE.Mesh(geo, threeMakeFaceMaterial());
    const edGeo = new THREE.BufferGeometry();
    edGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(segs * 2 * 3), 3));
    const edLines = new THREE.LineSegments(edGeo, threeMakeEdgeMaterial());
    edLines.renderOrder = 10;
    group.add(mesh, edLines);
    return { mesh, edLines };
  });

  function updateAt(t) {
    const bend2 = (x, y) => bendFn(x, y, t);
    const rowBottom = [], rowTop = [];
    for (let i = 0; i <= nSub; i++) {
      const x = xMax * i / nSub;
      rowBottom.push(threeRemap(bend2(x, 0)));
      rowTop.push(threeRemap(bend2(x, H)));
    }
    const fPos = lateralGeo.attributes.position.array;
    let vi = 0;
    for (let i = 0; i < nSub; i++) {
      const a = rowBottom[i], b2 = rowBottom[i + 1], c = rowTop[i], d = rowTop[i + 1];
      [a, b2, d, a, d, c].forEach(p => { fPos[vi++] = p.x; fPos[vi++] = p.y; fPos[vi++] = p.z; });
    }
    lateralGeo.attributes.position.needsUpdate = true;
    lateralGeo.computeVertexNormals();
    lateralGeo.computeBoundingSphere();

    const ePos = edgeGeo.attributes.position.array;
    let ei = 0;
    const pushEdge = (p1, p2) => { ePos[ei++] = p1.x; ePos[ei++] = p1.y; ePos[ei++] = p1.z; ePos[ei++] = p2.x; ePos[ei++] = p2.y; ePos[ei++] = p2.z; };
    for (let i = 0; i < nSub; i++) { pushEdge(rowBottom[i], rowBottom[i + 1]); pushEdge(rowTop[i], rowTop[i + 1]); }
    pushEdge(rowBottom[0], rowTop[0]);
    pushEdge(rowBottom[nSub], rowTop[nSub]);
    edgeGeo.attributes.position.needsUpdate = true;
    edgeGeo.computeBoundingSphere();

    caps.forEach((cap, ci) => {
      const { mesh, edLines } = capMeshes[ci];
      const foldAt = (px, py) => cap.foldPoint(px, py, t);
      const center = threeRemap(foldAt(cap.cx, cap.cy0));
      const arr = mesh.geometry.attributes.position.array;
      const earr = edLines.geometry.attributes.position.array;
      let k = 0, ek = 0;
      const rimPts = [];
      for (let i = 0; i <= segs; i++) {
        const a = i / segs * 2 * Math.PI;
        rimPts.push(threeRemap(foldAt(cap.cx + cap.r * Math.cos(a), cap.cy0 + cap.r * Math.sin(a))));
      }
      for (let i = 0; i < segs; i++) {
        [center, rimPts[i], rimPts[i + 1]].forEach(p => { arr[k++] = p.x; arr[k++] = p.y; arr[k++] = p.z; });
        earr[ek++] = rimPts[i].x; earr[ek++] = rimPts[i].y; earr[ek++] = rimPts[i].z;
        earr[ek++] = rimPts[i + 1].x; earr[ek++] = rimPts[i + 1].y; earr[ek++] = rimPts[i + 1].z;
      }
      mesh.geometry.attributes.position.needsUpdate = true;
      mesh.geometry.computeVertexNormals();
      mesh.geometry.computeBoundingSphere();
      edLines.geometry.attributes.position.needsUpdate = true;
      edLines.geometry.computeBoundingSphere();
    });
  }
  updateAt(1);
  return { group, updateAt };
}

function buildAnimatedCylinderGroup(R, H) {
  const circumf = 2 * Math.PI * R;
  const bendFn = (x, y, t) => {
    const angleTotal = t * 2 * Math.PI;
    const radiusB = angleTotal > 1e-4 ? circumf / angleTotal : null;
    if (radiusB === null) return { x: x - circumf / 2, y, z: 0 };
    const theta = (x / circumf - 0.5) * angleTotal;
    return { x: radiusB * Math.sin(theta), y, z: radiusB * (1 - Math.cos(theta)) };
  };
  const eX = Math.max(1, circumf * 0.002), eY = Math.max(0.5, H * 0.01);
  const makeFold = (y0, flipSign) => (px, py, t) => {
    const x0 = circumf / 2;
    const bend2 = (x, y) => bendFn(x, y, t);
    const attachFlat = bendFn(x0, y0, 0);
    return threeFoldCapPoint(bend2, x0, y0, px - attachFlat.x, py - attachFlat.y, t, eX, eY, flipSign);
  };
  const caps = [
    { cx: 0, cy0: -R, r: R, foldPoint: makeFold(0, -1) },
    { cx: 0, cy0: H + R, r: R, foldPoint: makeFold(H, 1) }
  ];
  return buildAnimatedCurvedGroup(circumf, H, bendFn, caps);
}

// pt suprafețele conice (con/trunchi de con), îndoirea laterală e o interpolare directă
// (nu o rotație rigidă), deci și capacul se calculează analitic prin interpolare între
// poziția plată și poziția finală corectă (tangentă + rotită perpendicular pe axă),
// nu prin derivate numerice locale (care nu au sens pt o interpolare, doar pt o rotație).
// pt capacele conice (con/trunchi de con): rotație reală (nu doar interpolare liniară a
// poziției), analog cu balamaua rigidă de la cilindru — axa și unghiul total de rotație
// sunt fixe (independente de raza de atașare), calculate o singură dată din geometria
// generică a atașării tangente la arc (unghi a0=0). Pivotul (punctul de tangență) se
// translatează odată cu restul suprafeței laterale, dar orientarea capacului se ROTEȘTE
// rigid în jurul lui, nu alunecă în linie dreaptă.
// capacul care se extinde spre exterior (departe de originea desfășurării) — rotație 180°
// în jurul unei axe diagonale (derivată analitic din geometria atașării tangente)
const CONE_CAP_AXIS_OUT = netVnorm({ x: 1, y: 1, z: 0 });
const CONE_CAP_ANGLE_OUT = -Math.PI;
// capacul care se extinde spre originea desfășurării (necesar când extinderea spre exterior
// s-ar suprapune cu sectorul lateral, ex. baza mică a trunchiului de con) — rotație 90° în
// jurul axei Z locale (derivată analitic separat, geometria fiind oglindită)
const CONE_CAP_AXIS_IN = { x: 0, y: 0, z: 1 };
const CONE_CAP_ANGLE_IN = Math.PI / 2;
function threeConeCapPoint(capX, capY, rAttach, alpha, t, extendSign) {
  const radial = rAttach * Math.sin(alpha), axisH = rAttach * Math.cos(alpha);
  const originFlat = { x: 0, y: -rAttach, z: 0 };
  const originClosed = { x: radial, y: 0, z: axisH };
  const pivot = {
    x: originFlat.x + (originClosed.x - originFlat.x) * t,
    y: originFlat.y + (originClosed.y - originFlat.y) * t,
    z: originFlat.z + (originClosed.z - originFlat.z) * t
  };
  const localVec = { x: capX, y: capY - originFlat.y, z: 0 };
  const axis = extendSign > 0 ? CONE_CAP_AXIS_IN : CONE_CAP_AXIS_OUT;
  const angle = (extendSign > 0 ? CONE_CAP_ANGLE_IN : CONE_CAP_ANGLE_OUT) * t;
  const Rt = netRodrigues(axis, angle);
  const rotated = netMatVec(Rt, localVec);
  return { x: pivot.x + rotated.x, y: pivot.y + rotated.y, z: pivot.z + rotated.z };
}

function buildAnimatedConeGroup(R, G) {
  const angle = 2 * Math.PI * R / G, halfAngle = angle / 2;
  const alpha = Math.asin(Math.min(1, R / G));
  const bendFn = (r, a0, t) => {
    // aici parametrii "x,y" ai bendFn generic sunt refolositi ca (raza r, unghi a) pt con
    const flat = { x: r * Math.sin(a0), y: -r * Math.cos(a0), z: 0 };
    if (t <= 0.0005) return flat;
    const phi = a0 * (Math.PI / halfAngle);
    const radial = r * Math.sin(alpha), axisH = r * Math.cos(alpha);
    const closed = { x: radial * Math.cos(phi), y: radial * Math.sin(phi), z: axisH };
    return { x: flat.x + (closed.x - flat.x) * t, y: flat.y + (closed.y - flat.y) * t, z: flat.z + (closed.z - flat.z) * t };
  };
  // adaptam la semnatura (x,y,t) folosita de buildAnimatedCurvedGroup: x=unghi deplasat, y=raza
  const wrapped = (xShift, r, t) => bendFn(r, xShift - halfAngle, t);
  const caps = [{ cx: 0, cy0: -G - R, r: R, foldPoint: (px, py, t) => threeConeCapPoint(px, py, G, alpha, t) }];
  return buildAnimatedCurvedGroup(angle, G, (x, y, t) => wrapped(x, y, t), caps);
}

function buildAnimatedConeFrustumGroup(R1, R2, Gf) {
  const rInner = Gf * R2 / (R1 - R2);
  const rOuter = rInner + Gf;
  const angle = 2 * Math.PI * R1 / rOuter, halfAngle = angle / 2;
  const alpha = Math.asin(Math.min(1, R1 / rOuter));
  const ptAt = (r, a0, t) => {
    const flat = { x: r * Math.sin(a0), y: -r * Math.cos(a0), z: 0 };
    if (t <= 0.0005) return flat;
    const phi = a0 * (Math.PI / halfAngle);
    const radial = r * Math.sin(alpha), axisH = r * Math.cos(alpha);
    const closed = { x: radial * Math.cos(phi), y: radial * Math.sin(phi), z: axisH };
    return { x: flat.x + (closed.x - flat.x) * t, y: flat.y + (closed.y - flat.y) * t, z: flat.z + (closed.z - flat.z) * t };
  };
  const wrapped = (xShift, y, t) => ptAt(rInner + y, xShift - halfAngle, t);
  const caps = [
    { cx: 0, cy0: -rOuter - R1, r: R1, foldPoint: (px, py, t) => threeConeCapPoint(px, py, rOuter, alpha, t, -1) },
    { cx: 0, cy0: -rInner + R2, r: R2, foldPoint: (px, py, t) => threeConeCapPoint(px, py, rInner, alpha, t, 1) }
  ];
  return buildAnimatedCurvedGroup(angle, Gf, (x, y, t) => wrapped(x, y, t), caps);
}

function build3DShapeGroupAnimated(shapeKey) {
  if (shapeKey === 'sfera') {
    const geo = new THREE.SphereGeometry(65, 32, 24);
    const mat = new THREE.MeshPhongMaterial({ color: THREE_SOLID_COLOR, shininess: 25, transparent: true, opacity: THREE_FACE_OPACITY + 0.1, depthWrite: false });
    const group = new THREE.Group();
    group.add(new THREE.Mesh(geo, mat));
    return { group, updateAt: null };
  }
  const spec = NET_SHAPES[shapeKey];
  if (!spec) return null;
  if (spec.curved === 'cilindru') { const { R, H } = spec.params; return buildAnimatedCylinderGroup(R, H); }
  if (spec.curved === 'con') { const { R, G } = spec.params; return buildAnimatedConeGroup(R, G); }
  if (spec.curved === 'trunchiCon') { const { R1, R2, Gf } = spec.params; return buildAnimatedConeFrustumGroup(R1, R2, Gf); }
  const built = spec.build();
  const forest = buildHingeForest(built.faces);
  netAnnotateHingeAngles(forest, spec.netKind, spec.netParams);
  return buildAnimatedPolyNetGroup(built.faces, forest);
}

function disposeThreeGroup(group) {
  group.traverse(obj => {
    if (obj.geometry) obj.geometry.dispose();
    if (obj.material) {
      if (Array.isArray(obj.material)) obj.material.forEach(m => m.dispose());
      else obj.material.dispose();
    }
  });
}

// decupează canvas-ul WebGL la conturul obiectului (elimină spațiul gol transparent din jur)
function captureTrimmedSnapshot(sourceCanvas, padding) {
  const off = document.createElement('canvas');
  off.width = sourceCanvas.width;
  off.height = sourceCanvas.height;
  const octx = off.getContext('2d');
  octx.drawImage(sourceCanvas, 0, 0);
  let minX = off.width, minY = off.height, maxX = 0, maxY = 0, found = false;
  const { data, width, height } = octx.getImageData(0, 0, off.width, off.height);
  for (let y = 0; y < height; y += 2) {
    for (let x = 0; x < width; x += 2) {
      if (data[(y * width + x) * 4 + 3] > 10) {
        found = true;
        if (x < minX) minX = x;
        if (x > maxX) maxX = x;
        if (y < minY) minY = y;
        if (y > maxY) maxY = y;
      }
    }
  }
  if (!found) return off.toDataURL('image/png');
  minX = Math.max(0, minX - padding);
  minY = Math.max(0, minY - padding);
  maxX = Math.min(width, maxX + padding);
  maxY = Math.min(height, maxY + padding);
  const crop = document.createElement('canvas');
  crop.width = maxX - minX;
  crop.height = maxY - minY;
  crop.getContext('2d').drawImage(off, minX, minY, crop.width, crop.height, 0, 0, crop.width, crop.height);
  return crop.toDataURL('image/png');
}

function open3DViewer() {
  if (typeof THREE === 'undefined') { showToast('Modulul 3D nu s-a putut încărca'); return; }

  const backdrop = document.createElement('div');
  backdrop.id = 'viewer3d-backdrop';
  backdrop.style.cssText = 'position:fixed; inset:0; background:rgba(10,10,10,0.96); z-index:500; display:flex; flex-direction:column;';

  const topBar = document.createElement('div');
  topBar.style.cssText = 'flex:0 0 auto; padding:10px 12px; display:flex; gap:8px; overflow-x:auto; -webkit-overflow-scrolling:touch; background:#161616; border-bottom:1px solid #333;';
  Object.keys(NET_SHAPES).concat(['sfera']).forEach(key => {
    const label = (SOLID_SHAPES[key] && SOLID_SHAPES[key].label) || key;
    const icon = buildShapeIconSVG(key, 18);
    const btn = document.createElement('button');
    btn.innerHTML = `<span style="display:inline-flex; align-items:center; justify-content:center;">${icon}</span><span>${label}</span>`;
    btn.dataset.shapeKey = key;
    btn.style.cssText = 'flex:0 0 auto; display:flex; align-items:center; gap:6px; background:#2a2a2a; color:#fff; border:1px solid #444; border-radius:8px; padding:8px 14px; font-size:13px; white-space:nowrap; cursor:pointer;';
    topBar.appendChild(btn);
  });
  backdrop.appendChild(topBar);

  const viewerArea = document.createElement('div');
  viewerArea.style.cssText = 'flex:1 1 auto; position:relative; touch-action:none; overflow:hidden;';
  backdrop.appendChild(viewerArea);

  const hint = document.createElement('div');
  hint.textContent = 'Trage pentru a roti • Ciupește / derulează pentru zoom';
  hint.style.cssText = 'position:absolute; top:10px; left:50%; transform:translateX(-50%); color:#bbb; font-size:12px; background:rgba(0,0,0,0.5); padding:5px 12px; border-radius:6px; pointer-events:none;';
  viewerArea.appendChild(hint);

  // ---- panoul cu sliderul de desfășurare în plan (ascuns pt sferă, care nu are desfășurare) ----
  const foldBar = document.createElement('div');
  foldBar.style.cssText = 'flex:0 0 auto; padding:8px 16px 4px; background:#161616; border-top:1px solid #333;';
  foldBar.innerHTML =
    '<div style="display:flex; align-items:center; justify-content:space-between; font-size:11px; color:#bbb; margin-bottom:2px;">' +
    '<span>◀ Asamblat</span><span id="viewer3d-fold-pct">0%</span><span>Desfășurat ▶</span>' +
    '</div>' +
    '<div style="display:flex; align-items:center; gap:10px;">' +
    '<button id="viewer3d-fold-play" title="Redă animația de desfășurare" style="flex:0 0 auto; width:30px; height:30px; border-radius:50%; border:none; background:#4da3ff; color:#fff; font-size:13px; line-height:1; cursor:pointer; display:flex; align-items:center; justify-content:center;">▶</button>' +
    '<input id="viewer3d-fold-slider" type="range" min="0" max="100" value="0" step="1" style="flex:1 1 auto; width:100%; accent-color:#4da3ff;">' +
    '</div>';
  backdrop.appendChild(foldBar);
  const foldSlider = foldBar.querySelector('#viewer3d-fold-slider');
  const foldPct = foldBar.querySelector('#viewer3d-fold-pct');
  const foldPlayBtn = foldBar.querySelector('#viewer3d-fold-play');

  // ---- panoul cu sliderul de viteză a rotației automate (merge indiferent dacă
  //      forma e asamblată, pe jumătate desfăcută sau complet plată) ----
  const rotateBar = document.createElement('div');
  rotateBar.style.cssText = 'flex:0 0 auto; padding:8px 16px; background:#161616; border-top:1px solid #333;';
  rotateBar.innerHTML =
    '<div style="display:flex; align-items:center; justify-content:space-between; font-size:11px; color:#bbb; margin-bottom:2px;">' +
    '<span>⟲ Rotație automată</span><span id="viewer3d-rotate-val">Oprită</span>' +
    '</div>' +
    '<input id="viewer3d-rotate-slider" type="range" min="-10" max="10" value="0" step="1" style="width:100%; accent-color:#4da3ff;">';
  backdrop.appendChild(rotateBar);
  const rotateSlider = rotateBar.querySelector('#viewer3d-rotate-slider');
  const rotateVal = rotateBar.querySelector('#viewer3d-rotate-val');

  const bottomBar = document.createElement('div');
  bottomBar.style.cssText = 'flex:0 0 auto; padding:12px; display:flex; justify-content:center; gap:12px; background:#161616; border-top:1px solid #333;';
  bottomBar.innerHTML =
    '<button id="viewer3d-cancel" style="background:#3a3a3a; color:#fff; border:none; border-radius:8px; padding:10px 22px; font-size:14px;">✕ Renunță</button>' +
    '<button id="viewer3d-ok" style="background:#4da3ff; color:#fff; border:none; border-radius:8px; padding:10px 26px; font-size:14px; font-weight:600;">✓ Inserează pe tablă</button>';
  backdrop.appendChild(bottomBar);

  document.body.appendChild(backdrop);

  // ---- scena Three.js ----
  const scene = new THREE.Scene();
  const camera = new THREE.PerspectiveCamera(45, 1, 1, 6000);
  const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true, preserveDrawingBuffer: true });
  renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1));
  renderer.domElement.style.cssText = 'position:absolute; inset:0; width:100%; height:100%; display:block;';
  viewerArea.appendChild(renderer.domElement);

  scene.add(new THREE.AmbientLight(0xffffff, 0.55));
  const dirLight = new THREE.DirectionalLight(0xffffff, 0.85);
  dirLight.position.set(150, 220, 180);
  scene.add(dirLight);
  const dirLight2 = new THREE.DirectionalLight(0xffffff, 0.35);
  dirLight2.position.set(-150, -80, -120);
  scene.add(dirLight2);

  const controls = new THREE.OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.08;
  controls.target.set(0, 0, 0);
  controls.autoRotate = false;
  controls.autoRotateSpeed = 0;

  rotateSlider.addEventListener('input', () => {
    const v = parseInt(rotateSlider.value, 10);
    controls.autoRotateSpeed = v * 3; // OrbitControls: implicit 2 ≈ 30s/tură; scalăm pt control mai vizibil
    controls.autoRotate = v !== 0;
    rotateVal.textContent = v === 0 ? 'Oprită' : (v > 0 ? `→ ${v}` : `← ${Math.abs(v)}`);
  });

  let currentGroup = null;
  let currentUpdateAt = null;
  function loadShape(key) {
    stopFoldPlay();
    if (currentGroup) { scene.remove(currentGroup); disposeThreeGroup(currentGroup); }
    const built = build3DShapeGroupAnimated(key);
    if (!built) return;
    currentGroup = built.group;
    currentUpdateAt = built.updateAt;
    scene.add(currentGroup);

    const hasFold = !!currentUpdateAt;
    foldBar.style.display = hasFold ? '' : 'none';
    foldSlider.value = '0';
    foldPct.textContent = '0%';

    // distanța camerei se calculează pt cel mai mare caz (starea complet desfăcută e
    // de obicei mult mai întinsă decât cea asamblată) — ca toată plaja sliderului să încapă
    let maxSize = 0;
    if (currentUpdateAt) {
      currentUpdateAt(0);
      maxSize = new THREE.Box3().setFromObject(currentGroup).getSize(new THREE.Vector3()).length();
      currentUpdateAt(1);
    }
    const box = new THREE.Box3().setFromObject(currentGroup);
    const center = box.getCenter(new THREE.Vector3());
    currentGroup.position.sub(center);
    const size = box.getSize(new THREE.Vector3());
    maxSize = Math.max(maxSize, size.length());
    const dist = maxSize * 1.1 + 60;
    camera.position.set(dist * 0.6, dist * 0.45, dist * 0.75);
    camera.near = 1; camera.far = dist * 10;
    camera.updateProjectionMatrix();
    controls.target.set(0, 0, 0);
    controls.update();
    [...topBar.children].forEach(b => { b.style.background = b.dataset.shapeKey === key ? '#4da3ff' : '#2a2a2a'; });
  }

  function applyFold(pct) {
    foldSlider.value = String(pct);
    foldPct.textContent = Math.round(pct) + '%';
    if (currentUpdateAt) {
      currentUpdateAt(1 - pct / 100);
      currentGroup.position.set(0, 0, 0);
      const box = new THREE.Box3().setFromObject(currentGroup);
      const center = box.getCenter(new THREE.Vector3());
      currentGroup.position.sub(center);
    }
  }

  foldSlider.addEventListener('input', () => {
    stopFoldPlay();
    applyFold(parseInt(foldSlider.value, 10));
  });

  // ---- animație PLAY: desfășoară automat corpul, apoi îl reasamblează, în buclă ----
  let foldPlayRafId = null;
  let foldPlayDir = 1; // 1 = spre desfășurat, -1 = spre asamblat
  const FOLD_PLAY_PCT_PER_FRAME = 0.8;
  function stopFoldPlay() {
    if (foldPlayRafId !== null) {
      cancelAnimationFrame(foldPlayRafId);
      foldPlayRafId = null;
    }
    foldPlayBtn.textContent = '▶';
  }
  function stepFoldPlay() {
    let pct = parseInt(foldSlider.value, 10) + foldPlayDir * FOLD_PLAY_PCT_PER_FRAME;
    if (pct >= 100) { pct = 100; foldPlayDir = -1; }
    else if (pct <= 0) { pct = 0; foldPlayDir = 1; }
    applyFold(pct);
    foldPlayRafId = requestAnimationFrame(stepFoldPlay);
  }
  foldPlayBtn.addEventListener('click', () => {
    if (foldPlayRafId !== null) {
      stopFoldPlay();
      return;
    }
    if (parseInt(foldSlider.value, 10) >= 100) foldPlayDir = -1;
    else foldPlayDir = 1;
    foldPlayBtn.textContent = '⏸';
    foldPlayRafId = requestAnimationFrame(stepFoldPlay);
  });

  function resize() {
    const w = viewerArea.clientWidth, h = viewerArea.clientHeight;
    if (!w || !h) return;
    camera.aspect = w / h;
    camera.updateProjectionMatrix();
    renderer.setSize(w, h);
  }
  resize();
  window.addEventListener('resize', resize);

  let rafId;
  function animate() {
    controls.update();
    renderer.render(scene, camera);
    rafId = requestAnimationFrame(animate);
  }
  animate();

  topBar.addEventListener('click', (e) => {
    const btn = e.target.closest('button[data-shape-key]');
    if (btn) loadShape(btn.dataset.shapeKey);
  });

  loadShape('cub');

  function cleanup() {
    stopFoldPlay();
    cancelAnimationFrame(rafId);
    window.removeEventListener('resize', resize);
    controls.dispose();
    if (currentGroup) disposeThreeGroup(currentGroup);
    renderer.dispose();
    backdrop.remove();
  }

  document.getElementById('viewer3d-cancel').addEventListener('click', cleanup);

  document.getElementById('viewer3d-ok').addEventListener('click', () => {
    renderer.render(scene, camera);
    const dataUrl = captureTrimmedSnapshot(renderer.domElement, 24);
    const img = new Image();
    img.onload = () => {
      const maxW = wrap.clientWidth * 0.5;
      const maxH = wrap.clientHeight * 0.5;
      let w = img.naturalWidth, h = img.naturalHeight;
      if (w > maxW) { h = h * maxW / w; w = maxW; }
      if (h > maxH) { w = w * maxH / h; h = maxH; }
      const x = Math.max(20, (wrap.clientWidth - w) / 2);
      const y = Math.max(20, (wrap.clientHeight - h) / 2);
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
      showToast('✓ Corp 3D inserat pe tablă');
    };
    img.src = dataUrl;
    cleanup();
  });
}

document.getElementById('btn-3d').addEventListener('click', () => open3DViewer());

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
document.getElementById('ruling-none').onclick = () => setBoardRuling('none', 'ruling-none');
document.getElementById('ruling-grid').onclick = () => setBoardRuling('grid', 'ruling-grid');
document.getElementById('ruling-dictando').onclick = () => setBoardRuling('dictando', 'ruling-dictando');
document.getElementById('ruling-music').onclick = () => setBoardRuling('music', 'ruling-music');
document.getElementById('ruling-size-minus').onclick = () => {
  rulingSize = Math.max(10, rulingSize - 4);
  document.getElementById('ruling-size-val').textContent = rulingSize;
  drawBg();
};
document.getElementById('ruling-size-plus').onclick = () => {
  rulingSize = Math.min(80, rulingSize + 4);
  document.getElementById('ruling-size-val').textContent = rulingSize;
  drawBg();
};
document.getElementById('ruling-color-pick').addEventListener('input', (e) => {
  rulingColor = e.target.value;
  drawBg();
});
document.getElementById('ruling-opacity-minus').onclick = () => {
  rulingOpacity = Math.max(0.1, Math.round((rulingOpacity - 0.1) * 10) / 10);
  document.getElementById('ruling-opacity-val').textContent = Math.round(rulingOpacity * 100) + '%';
  drawBg();
};
document.getElementById('ruling-opacity-plus').onclick = () => {
  rulingOpacity = Math.min(1, Math.round((rulingOpacity + 0.1) * 10) / 10);
  document.getElementById('ruling-opacity-val').textContent = Math.round(rulingOpacity * 100) + '%';
  drawBg();
};
syncRulingColorPicker();

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
    boardRuling: boardRuling,
    rulingSize: rulingSize,
    rulingColor: rulingColor,
    rulingOpacity: rulingOpacity,
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

      boardRuling = data.boardRuling || 'none';
      document.querySelectorAll('.ruling-btn').forEach(b => b.classList.remove('active'));
      const rulingBtnMap = { none: 'ruling-none', grid: 'ruling-grid', dictando: 'ruling-dictando', music: 'ruling-music' };
      const activeRulingBtn = document.getElementById(rulingBtnMap[boardRuling]);
      if (activeRulingBtn) activeRulingBtn.classList.add('active');
      rulingSize = data.rulingSize || 28;
      document.getElementById('ruling-size-val').textContent = rulingSize;
      rulingColor = data.rulingColor || '#ffffff';
      rulingOpacity = (data.rulingOpacity != null) ? data.rulingOpacity : 0.5;
      document.getElementById('ruling-opacity-val').textContent = Math.round(rulingOpacity * 100) + '%';
      syncRulingColorPicker();
      
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
// AJUTOR ȘI LICENȚĂ
// ================================================================

const HELP_CONTENT_HTML = `
<h4>Desen</h4>
<ul>
  <li><b>Creion</b> — desen liber cu mâna.</li>
  <li><b>Linie</b>, <b>linie întreruptă</b>, <b>săgeată</b> — trage din punctul de start până la cel final.</li>
  <li><b>Cerc</b> — trage din centru spre exterior.</li>
  <li><b>Dreptunghi</b>, <b>poligon</b> — pentru poligon, atinge fiecare vârf, apoi apasă bifa (✓) ca să închizi forma.</li>
  <li><b>Radieră</b>, <b>text</b> — șterge sau adaugă text.</li>
</ul>

<h4>Matematică</h4>
<ul>
  <li><b>f(x)</b> — reprezintă grafic o funcție.</li>
  <li><b>Corpuri geometrice</b> — inserează un corp 3D predefinit (cub, prismă, piramidă, trunchi etc.).</li>
  <li><b>Corp 3D interactiv</b> — creează un corp pe care îl poți roti liber (ca în Blender) înainte să-l inserezi; sliderul de desfășurare are și un buton ▶ care animă automat asamblarea/desfacerea corpului.</li>
  <li><b>Mijlocul unui segment</b> — atinge un segment existent ca să-i marchezi mijlocul.</li>
  <li><b>Riglă, echer, raportor, compas</b> — instrumente de desen tehnic.</li>
</ul>

<h4>Rotirea corpurilor 3D</h4>
<ul>
  <li>Selectează corpul, apoi trage de mânerul de rotire (cercul albastru).</li>
  <li>Cât timp tragi, jos apare unghiul curent de rotație.</li>
  <li>Implicit, muchiile din spate (ascunse privirii) se desenează cu linie întreruptă — convenția clasică de manual.</li>
  <li>Dacă preferi ca toate muchiile să fie continue, bifează opțiunea de mai jos.</li>
</ul>
<p style="display:flex;align-items:center;gap:8px;">
  <label style="display:flex;align-items:center;gap:6px;cursor:pointer;font-size:13px;">
    <input type="checkbox" id="toggle-hidden-lines"> Arată toate muchiile cu linie continuă
  </label>
</p>

<h4>Selecție și editare</h4>
<ul>
  <li><b>Selectare</b> — atinge sau încercuiește (lasou) elementele dorite.</li>
  <li><b>Selecție multiplă</b> — utilă pe ecran tactil, fără tasta Shift.</li>
  <li>Un element selectat poate fi mutat, redimensionat (mânerul portocaliu) sau șters (tasta Delete / butonul radieră).</li>
</ul>

<h4>Culoare și grosime</h4>
<p>Alege o culoare din paletă sau selectorul de culoare, iar grosimea liniei cu butoanele <code>−</code> / <code>+</code>.</p>

<h4>Imagini și fișe PDF</h4>
<ul>
  <li><b>Încarcă imagine</b> (una sau mai multe) — le poți plasa oriunde pe tablă.</li>
  <li><b>Fișă PDF</b> — încarcă un test/fișă de lucru ca fundal, apoi comută între tablă și fișă.</li>
</ul>

<h4>Fișier și istoric</h4>
<ul>
  <li><b>Anulează / Refă</b> — undo/redo pentru orice acțiune.</li>
  <li><b>Șterge tot</b> — golește pagina curentă.</li>
  <li><b>Exportă PDF</b> — salvează tabla curentă ca document PDF.</li>
  <li><b>Salvează / Încarcă sesiune</b> — salvează progresul într-un fișier <code>.wbs</code> pe care îl poți relua ulterior.</li>
</ul>

<h4>Pagini și fundal</h4>
<p>Navighează între pagini cu săgețile din colț, adaugă sau șterge pagini, și schimbă culoarea fundalului tablei din paleta din dreapta jos a barei de instrumente.</p>
<p>Din grupul alăturat de butoane poți alege și o liniatură pentru tablă: <b>caroiaj</b> (ca în caietul de matematică), <b>dictando</b> (linii ca în caietul de scriere/dictando) sau <b>portativ</b> (ca în caietul de muzică). Cu butoanele −/+ reglezi mărimea pătratelor/liniilor și opacitatea lor, iar cu selectorul de culoare alegi manual culoarea liniaturii — implicit e alb, la 50% opacitate, potrivit fundalului negru al tablei.</p>
`;

const LICENSE_CONTENT_HTML = `
<h4>Licența aplicației</h4>
<p>Acest software este pus la dispoziție "ca atare", fără nicio garanție explicită sau implicită. Utilizarea lui este pe propria răspundere.</p>

<h4>Biblioteci terțe folosite</h4>
<p>Aplicația este construită folosind exclusiv biblioteci gratuite și open-source:</p>
<table>
  <tr><th>Bibliotecă</th><th>Scop</th><th>Licență</th></tr>
  <tr><td>Tabler Icons</td><td>Set de iconițe pentru interfață</td><td>MIT</td></tr>
  <tr><td>jsPDF</td><td>Generarea și exportul fișierelor PDF</td><td>MIT</td></tr>
  <tr><td>PDF.js</td><td>Afișarea fișelor de lucru încărcate în format PDF</td><td>Apache 2.0</td></tr>
  <tr><td>Three.js</td><td>Randarea corpului 3D interactiv</td><td>MIT</td></tr>
  <tr><td>OrbitControls (Three.js)</td><td>Rotirea/zoom-ul cu mouse-ul sau degetul în modulul 3D interactiv</td><td>MIT</td></tr>
</table>
<p>Fiecare bibliotecă terță rămâne sub licența proprie, publicată de autorii ei originali; nicio bibliotecă folosită aici nu impune costuri de utilizare.</p>

<h4>Conținut generat de utilizator</h4>
<p>Desenele, textele și fișierele PDF/sesiune create sau încărcate de tine rămân proprietatea ta. Aplicația nu revendică niciun drept asupra lor.</p>

<h4>Contact</h4>
<p>Pentru întrebări legate de licențiere sau utilizare, contactează administratorul aplicației.</p>
`;

function openInfoModal(title, bodyHtml) {
  const backdrop = document.getElementById('info-modal-backdrop');
  const titleEl = document.getElementById('info-modal-title');
  const bodyEl = document.getElementById('info-modal-body');
  if (!backdrop || !titleEl || !bodyEl) return;
  titleEl.textContent = title;
  bodyEl.innerHTML = bodyHtml;
  backdrop.classList.add('show');
  const hiddenLinesToggle = document.getElementById('toggle-hidden-lines');
  if (hiddenLinesToggle) {
    // Bifat = "arată toate muchiile continue" → SOLID_SHOW_HIDDEN_LINES = false.
    // Nebifat (implicit) = muchiile din spate întrerupte → SOLID_SHOW_HIDDEN_LINES = true.
    hiddenLinesToggle.checked = !SOLID_SHOW_HIDDEN_LINES;
    hiddenLinesToggle.addEventListener('change', () => {
      SOLID_SHOW_HIDDEN_LINES = !hiddenLinesToggle.checked;
      rebuildAllSolid3DStrokes();
      redrawStrokes();
      drawSelectionHighlights();
    });
  }
}
function closeInfoModal() {
  const backdrop = document.getElementById('info-modal-backdrop');
  if (backdrop) backdrop.classList.remove('show');
}

// Reconstruiește (la aceeași rotație) toate corpurile 3D deja desenate, pe toate paginile —
// folosit când se schimbă comutatorul de linii ascunse, ca schimbarea să se vadă imediat și
// pe formele plasate deja, nu doar pe cele noi.
function rebuildAllSolid3DStrokes() {
  pages.forEach(page => {
    (page.strokes || []).forEach(stroke => {
      if (stroke.type === 'solid3d' && SOLID_SHAPES[stroke.shape]) {
        rotateSolid3D(stroke, stroke.rotationY || 0);
      }
    });
  });
}

const btnHelp = document.getElementById('btn-help');
if (btnHelp) btnHelp.addEventListener('click', () => openInfoModal('Ajutor', HELP_CONTENT_HTML));
const btnLicense = document.getElementById('btn-license');
if (btnLicense) btnLicense.addEventListener('click', () => openInfoModal('Licență', LICENSE_CONTENT_HTML));
const infoModalClose = document.getElementById('info-modal-close');
if (infoModalClose) infoModalClose.addEventListener('click', closeInfoModal);
const infoModalBackdrop = document.getElementById('info-modal-backdrop');
if (infoModalBackdrop) {
  infoModalBackdrop.addEventListener('click', (e) => {
    if (e.target === infoModalBackdrop) closeInfoModal();
  });
}

// ================================================================
// INITIALIZARE
// ================================================================

document.getElementById('btn-pen').classList.add('active');
tool = 'pen';

updateGeoToolContrast();
setTimeout(initCanvas, 100);
