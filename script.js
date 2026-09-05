// Zoom and pan state
const zoomLevels = { 
    cfg: 1, 
    blocks: 1, 
    callgraph: 1, 
    symbols: 1, 
    fullscreen: 1 
};

let isPanning = false;
let startX, startY;
let translateX = {
    cfg: 0, 
    blocks: 0, 
    callgraph: 0, 
    symbols: 0, 
    fullscreen: 0
};
let translateY = {
    cfg: 0, 
    blocks: 0, 
    callgraph: 0, 
    symbols: 0, 
    fullscreen: 0
};
let currentId = null;

// Update transform
function updateTransform(id) {
    const img = document.getElementById(id + 'Image');
    if (img) {
        img.style.transform = `translate(${translateX[id]}px, ${translateY[id]}px) scale(${zoomLevels[id]})`;
        const zoomLevelElement = document.getElementById(id + 'ZoomLevel');
        if (zoomLevelElement) {
            zoomLevelElement.textContent = Math.round(zoomLevels[id] * 100) + '%';
        }
    }
}

// Button zoom
function zoomImage(id, delta) {
    zoomLevels[id] = Math.max(0.2, Math.min(5, zoomLevels[id] + delta));
    updateTransform(id);
}

// Reset zoom
function resetZoom(id) {
    zoomLevels[id] = 1;
    translateX[id] = 0;
    translateY[id] = 0;
    updateTransform(id);
}

// Setup wheel zoom
function setupWheelZoom(id) {
    const wrapper = document.getElementById(id + 'Wrapper');
    if (!wrapper) return;
    
    wrapper.addEventListener('wheel', (e) => {
        e.preventDefault();
        
        const delta = e.deltaY * -0.001;
        const oldZoom = zoomLevels[id];
        const newZoom = Math.max(0.2, Math.min(5, oldZoom + delta));
        
        if (oldZoom === newZoom) return;
        
        const rect = wrapper.getBoundingClientRect();
        const mouseX = e.clientX - rect.left - rect.width / 2;
        const mouseY = e.clientY - rect.top - rect.height / 2;
        
        const zoomRatio = newZoom / oldZoom;
        translateX[id] = (translateX[id] - mouseX) * zoomRatio + mouseX;
        translateY[id] = (translateY[id] - mouseY) * zoomRatio + mouseY;
        
        zoomLevels[id] = newZoom;
        updateTransform(id);
    }, { passive: false });
}

// Pan start
function startPan(e, id) {
    if (e.button !== 0) return;
    isPanning = true;
    currentId = id;
    const wrapper = document.getElementById(id + 'Wrapper') || 
                    document.getElementById(id + 'Content');
    if (!wrapper) return;
    wrapper.classList.add('grabbing');
    startX = e.clientX - translateX[id];
    startY = e.clientY - translateY[id];
    e.preventDefault();
}

// Mouse move
document.addEventListener('mousemove', (e) => {
    if (!isPanning || !currentId) return;
    e.preventDefault();
    translateX[currentId] = e.clientX - startX;
    translateY[currentId] = e.clientY - startY;
    updateTransform(currentId);
});

// Mouse up
document.addEventListener('mouseup', () => {
    if (currentId) {
        const wrapper = document.getElementById(currentId + 'Wrapper');
        if (wrapper) wrapper.classList.remove('grabbing');
    }
    isPanning = false;
    currentId = null;
});

// Mouse leave
document.addEventListener('mouseleave', () => {
    if (currentId) {
        const wrapper = document.getElementById(currentId + 'Wrapper');
        if (wrapper) wrapper.classList.remove('grabbing');
    }
    isPanning = false;
    currentId = null;
});

// Fullscreen
function openFullscreen(id) {
    const img = document.getElementById(id + 'Image');
    if (!img) return;
    
    const modal = document.getElementById('fullscreenModal');
    if (!modal) return;
    
    modal.innerHTML = `
        <div style="position: fixed; top: 20px; right: 20px; z-index: 10000;">
            <button class="zoom-btn" onclick="zoomImage('fullscreen', -0.1)">−</button>
            <span class="zoom-level" id="fullscreenZoomLevel">100%</span>
            <button class="zoom-btn" onclick="zoomImage('fullscreen', 0.1)">+</button>
            <button class="zoom-btn" onclick="resetZoom('fullscreen')">⟲</button>
            <button class="zoom-btn" style="background: #ff6b6b;" onclick="closeFullscreen()">✕ Close</button>
        </div>
        <div style="width: 100%; height: 100%; overflow: auto; cursor: grab;" id="fullscreenContent" onmousedown="startPan(event, 'fullscreen')">
            <img id="fullscreenImage" src="${img.src}" style="display: block; margin: auto; max-width: 90vw; max-height: 90vh; object-fit: contain;">
        </div>
    `;
    
    modal.classList.add('active');
    zoomLevels.fullscreen = 1;
    translateX.fullscreen = 0;
    translateY.fullscreen = 0;
}

function closeFullscreen() {
    const modal = document.getElementById('fullscreenModal');
    if (modal) {
        modal.classList.remove('active');
    }
}

// CFG Tab switching
function showCFGTab(tabName) {
    const tabs = document.querySelectorAll('.tab-content');
    const buttons = document.querySelectorAll('.tab-btn');
    
    tabs.forEach(tab => tab.classList.remove('active'));
    buttons.forEach(btn => btn.classList.remove('active'));
    
    document.getElementById('cfg-' + tabName).classList.add('active');
    event.target.classList.add('active');
}

// Initialize on page load
document.addEventListener('DOMContentLoaded', () => {
    setupWheelZoom('cfg');
    setupWheelZoom('blocks');
    setupWheelZoom('callgraph');
    setupWheelZoom('symbols');
    
    // Close fullscreen on ESC
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') closeFullscreen();
    });
});
