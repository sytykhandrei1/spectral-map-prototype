const canvas = document.getElementById("spectrumCanvas");
const ctx = canvas.getContext("2d");
const trackList = document.getElementById("trackList");
const conflictList = document.getElementById("conflictList");
const cursorReadout = document.getElementById("cursorReadout");
const smoothInput = document.getElementById("smooth");
const decayInput = document.getElementById("decay");
const thresholdInput = document.getElementById("threshold");
const resetFocus = document.getElementById("resetFocus");
const conflictCount = document.getElementById("conflictCount");
const pointInspector = document.getElementById("pointInspector");
const inspectState = document.getElementById("inspectState");
const audioFilesInput = document.getElementById("audioFiles");
const audioStatus = document.getElementById("audioStatus");
const timelineStatus = document.getElementById("timelineStatus");
const timeReadout = document.getElementById("timeReadout");
const windowReadout = document.getElementById("windowReadout");
const timelineScrub = document.getElementById("timelineScrub");
const scrubCurrent = document.getElementById("scrubCurrent");
const scrubDuration = document.getElementById("scrubDuration");
const demoButton = document.getElementById("demoButton");
const playButton = document.getElementById("playButton");
const restartButton = document.getElementById("restartButton");
const waveAmpInput = document.getElementById("waveAmp");
const waveGlowInput = document.getElementById("waveGlow");
const waveFillInput = document.getElementById("waveFill");
const waveWidthInput = document.getElementById("waveWidth");
const waveDimInput = document.getElementById("waveDim");
const waveHueInput = document.getElementById("waveHue");
const resetVisuals = document.getElementById("resetVisuals");

const bins = 256;
const maxCompareTracks = 4;
const minDb = -78;
const maxDb = 6;
const minFreq = 20;
const maxFreq = 20000;
let width = 0;
let height = 0;
let dpr = 1;
let mode = "compare";
let focusedTrack = null;
let frozen = false;
let heatmap = true;
let pointer = null;
let lockedPointer = null;
let hoveredTrack = null;
let lastFrame = 0;
let lastSidebarRender = 0;
let lastInspectIndex = -1;
let lastInspectRender = 0;
let audioMode = false;
let audioContext = null;
let masterGain = null;
let masterAnalyser = null;
let masterFreqData = null;
let isPlaying = false;
let startedAt = 0;
let pausedAt = 0;
let loadedFileNames = [];
let loadedDuration = 0;
let isScrubbing = false;

const palette = ["#5cf2c8", "#7897ff", "#ff6d91", "#ffbd63", "#b77dff", "#46c4ff", "#d8f26b", "#f27ce4"];
const defaultVisuals = {
  amp: 1,
  glow: 14,
  fill: 0.03,
  width: 1.6,
  dim: 0.26,
  hue: 0,
};

let tracks = [
  { id: "kick", name: "Kick", color: palette[0], base: 0.88, peaks: [[58, 1.0, 0.045], [118, 0.45, 0.035], [3200, 0.16, 0.08]] },
  { id: "bass", name: "Bass", color: palette[1], base: 0.8, peaks: [[72, 0.9, 0.07], [142, 0.72, 0.06], [720, 0.22, 0.08]] },
  { id: "vocal", name: "Vocal", color: palette[2], base: 0.7, peaks: [[210, 0.24, 0.08], [1200, 0.68, 0.11], [3100, 0.86, 0.12], [8200, 0.38, 0.12]] },
  { id: "drums", name: "Drum Bus", color: palette[3], base: 0.58, peaks: [[180, 0.34, 0.06], [2400, 0.35, 0.18], [9000, 0.62, 0.18]] },
  { id: "pad", name: "Pad", color: palette[4], base: 0.54, peaks: [[260, 0.28, 0.1], [820, 0.46, 0.14], [5200, 0.35, 0.2]] },
  { id: "lead", name: "Lead", color: palette[5], base: 0.5, peaks: [[540, 0.2, 0.08], [1800, 0.74, 0.1], [5600, 0.52, 0.12]] },
  { id: "hats", name: "Hats", color: palette[6], base: 0.44, peaks: [[6800, 0.58, 0.16], [11200, 0.72, 0.13], [15800, 0.28, 0.12]] },
  { id: "fx", name: "FX Return", color: palette[7], base: 0.38, peaks: [[430, 0.18, 0.12], [3900, 0.36, 0.2], [12600, 0.4, 0.18]] },
]
  .slice(0, maxCompareTracks)
  .map((track, index) => ({
  ...track,
  phase: index * 7.13,
  spectrum: new Array(bins).fill(minDb),
  target: new Array(bins).fill(minDb),
  rms: -24,
  peak: -9,
  visible: true,
  analyser: null,
  freqData: null,
  timeData: null,
  buffer: null,
  source: null,
}));

const master = {
  spectrum: new Array(bins).fill(minDb),
  peakHold: new Array(bins).fill(minDb),
};

function resizeCanvas() {
  const rect = canvas.getBoundingClientRect();
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  width = Math.max(1, Math.floor(rect.width));
  height = Math.max(1, Math.floor(rect.height));
  canvas.width = Math.floor(width * dpr);
  canvas.height = Math.floor(height * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}

function freqAt(index) {
  const t = index / (bins - 1);
  return minFreq * Math.pow(maxFreq / minFreq, t);
}

function xForFreq(freq) {
  return (Math.log(freq / minFreq) / Math.log(maxFreq / minFreq)) * width;
}

function dbToY(db) {
  const normalized = (db - minDb) / (maxDb - minDb);
  return height - Math.max(0, Math.min(1, normalized)) * (height - 42) - 22;
}

function styledDb(db) {
  const amp = Number(waveAmpInput.value);
  return Math.max(minDb, Math.min(maxDb, minDb + (db - minDb) * amp));
}

function colorWithHue(hex) {
  const shift = Number(waveHueInput.value);
  if (!shift) return hex;
  const r = parseInt(hex.slice(1, 3), 16) / 255;
  const g = parseInt(hex.slice(3, 5), 16) / 255;
  const b = parseInt(hex.slice(5, 7), 16) / 255;
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  let h = 0;
  let s = 0;
  const l = (max + min) / 2;
  const d = max - min;
  if (d !== 0) {
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    if (max === r) h = (g - b) / d + (g < b ? 6 : 0);
    else if (max === g) h = (b - r) / d + 2;
    else h = (r - g) / d + 4;
    h *= 60;
  }
  return `hsl(${(h + shift + 360) % 360} ${Math.round(s * 100)}% ${Math.round(l * 100)}%)`;
}

function gaussLog(freq, center, amp, spread) {
  const distance = Math.log(freq / center) / Math.log(maxFreq / minFreq);
  return amp * Math.exp(-(distance * distance) / (2 * spread * spread));
}

function generateTrack(track, time) {
  const pulse = 0.78 + Math.sin(time * (1.1 + track.base * 0.8) + track.phase) * 0.12;
  let energy = 0;

  for (let i = 0; i < bins; i++) {
    const freq = freqAt(i);
    const tilt = 1 - i / bins;
    const breath = Math.sin(time * 2.2 + track.phase + i * 0.08) * 0.035;
    const noise = Math.sin(time * 7.0 + i * 1.7 + track.phase) * 0.018;
    let value = 0.035 + tilt * 0.12 + breath + noise;

    for (const peak of track.peaks) {
      value += gaussLog(freq, peak[0], peak[1], peak[2]);
    }

    value *= track.base * pulse;
    const db = minDb + value * 72;
    track.target[i] = Math.max(minDb, Math.min(maxDb, db));
    track.spectrum[i] += (track.target[i] - track.spectrum[i]) * Number(smoothInput.value);
    energy += Math.pow(10, track.spectrum[i] / 20);
  }

  track.rms = 20 * Math.log10(energy / bins + 0.0001) + 9;
  track.peak = Math.max(...track.spectrum) - 4;
}

function updateMaster() {
  for (let i = 0; i < bins; i++) {
    let linear = 0;
    for (const track of tracks) {
      if (!track.visible) continue;
      linear += Math.pow(10, track.spectrum[i] / 20);
    }
    const db = 20 * Math.log10(linear / 2.2 + 0.00001);
    master.spectrum[i] += (db - master.spectrum[i]) * 0.18;
    master.peakHold[i] = Math.max(master.spectrum[i], master.peakHold[i] * Number(decayInput.value) + minDb * (1 - Number(decayInput.value)));
  }
}

function setupAnalyser(analyser) {
  analyser.fftSize = 4096;
  analyser.minDecibels = minDb;
  analyser.maxDecibels = maxDb;
  analyser.smoothingTimeConstant = 0.72;
}

async function ensureAudioContext() {
  if (audioContext) return audioContext;
  audioContext = new AudioContext();
  masterGain = audioContext.createGain();
  masterGain.gain.value = 0.82;
  masterAnalyser = audioContext.createAnalyser();
  setupAnalyser(masterAnalyser);
  masterFreqData = new Float32Array(masterAnalyser.frequencyBinCount);
  masterGain.connect(masterAnalyser);
  masterAnalyser.connect(audioContext.destination);
  return audioContext;
}

async function loadAudioFiles(files) {
  const selected = [...files].slice(0, maxCompareTracks);
  if (!selected.length) return;
  audioStatus.textContent = `Selected ${selected.length} file${selected.length > 1 ? "s" : ""}, preparing decoder...`;
  console.info("Selected audio files", selected.map((file) => `${file.name} (${file.type || "unknown"}, ${file.size} bytes)`));
  const ctxAudio = await ensureAudioContext();
  if (ctxAudio.state === "suspended") await ctxAudio.resume();
  stopAudio(false);
  audioStatus.textContent = `Decoding ${selected.length} of ${maxCompareTracks}: ${selected.map((file) => file.name).join(" · ")}`;

  const decoded = await Promise.all(
    selected.map(async (file, index) => {
      const arrayBuffer = await file.arrayBuffer();
      let buffer;
      try {
        buffer = await ctxAudio.decodeAudioData(arrayBuffer.slice(0));
      } catch (error) {
        throw new Error(`Could not decode ${file.name}. Try PCM WAV, AIFF, MP3, M4A, FLAC, or OGG. ${error.message || error}`);
      }
      return createAudioTrack(file.name.replace(/\.[^/.]+$/, ""), buffer, index);
    }),
  );

  tracks = decoded;
  loadedFileNames = decoded.map((track) => track.name);
  loadedDuration = Math.max(...decoded.map((track) => track.buffer?.duration || 0));
  audioMode = true;
  focusedTrack = null;
  hoveredTrack = null;
  lockedPointer = null;
  for (let i = 0; i < bins; i++) {
    master.spectrum[i] = minDb;
    master.peakHold[i] = minDb;
  }
  renderTracks();
  clearPointInspector();
  updateAudioStatus("loaded");
  playButton.textContent = "Play";
  playButton.classList.remove("is-active");
  timelineScrub.disabled = false;
  timelineScrub.value = "0";
  updateTimelineReadout();
}

async function loadDemoAudio() {
  const ctxAudio = await ensureAudioContext();
  if (ctxAudio.state === "suspended") await ctxAudio.resume();
  stopAudio(false);
  const duration = 16;
  const specs = [
    { name: "Demo Kick", freq: 58, colorIndex: 0 },
    { name: "Demo Bass", freq: 92, colorIndex: 1 },
    { name: "Demo Vocal", freq: 720, colorIndex: 2 },
    { name: "Demo Drums", freq: 4200, colorIndex: 3 },
  ];

  tracks = specs.map((spec, index) => {
    const buffer = createDemoBuffer(ctxAudio, duration, spec.freq, index);
    const track = createAudioTrack(spec.name, buffer, index);
    track.color = palette[spec.colorIndex];
    return track;
  });
  loadedFileNames = tracks.map((track) => track.name);
  loadedDuration = duration;
  audioMode = true;
  pausedAt = 0;
  focusedTrack = null;
  hoveredTrack = null;
  lockedPointer = null;
  for (let i = 0; i < bins; i++) {
    master.spectrum[i] = minDb;
    master.peakHold[i] = minDb;
  }
  renderTracks();
  updateAudioStatus("loaded");
  timelineScrub.disabled = false;
  timelineScrub.value = "0";
  updateTimelineReadout();
  audioStatus.textContent = "Loaded demo audio buffers";
}

function createDemoBuffer(ctxAudio, duration, baseFreq, index) {
  const sampleRate = ctxAudio.sampleRate;
  const frameCount = Math.floor(duration * sampleRate);
  const buffer = ctxAudio.createBuffer(1, frameCount, sampleRate);
  const data = buffer.getChannelData(0);
  for (let i = 0; i < frameCount; i++) {
    const t = i / sampleRate;
    const gate = 0.45 + 0.55 * Math.max(0, Math.sin(t * Math.PI * (index === 0 ? 4 : 1 + index * 0.4)));
    const harmonic = Math.sin(Math.PI * 2 * baseFreq * t) * 0.45;
    const overtone = Math.sin(Math.PI * 2 * baseFreq * (index + 2) * t) * 0.12;
    const movement = Math.sin(Math.PI * 2 * (baseFreq * (1 + Math.sin(t * 0.8) * 0.02)) * t) * 0.18;
    data[i] = (harmonic + overtone + movement) * gate * 0.38;
  }
  return buffer;
}

function createAudioTrack(name, buffer, index) {
  const analyser = audioContext.createAnalyser();
  setupAnalyser(analyser);
  analyser.connect(masterGain);
  return {
    id: `audio-${index}`,
    name: name || `Track ${index + 1}`,
    color: palette[index % palette.length],
    base: 0,
    peaks: [],
    phase: index * 7.13,
    spectrum: new Array(bins).fill(minDb),
    target: new Array(bins).fill(minDb),
    rms: minDb,
    peak: minDb,
    visible: true,
    analyser,
    freqData: new Float32Array(analyser.frequencyBinCount),
    timeData: new Float32Array(analyser.fftSize),
    buffer,
    source: null,
  };
}

function playAudio() {
  if (!audioMode || !tracks.length) return;
  ensureAudioContext().then((ctxAudio) => {
    if (isPlaying) {
      stopAudio(true);
      return;
    }

    if (ctxAudio.state === "suspended") ctxAudio.resume();
    const startOffset = pausedAt;
    const longest = Math.max(...tracks.map((track) => track.buffer?.duration || 0));
    if (startOffset >= longest - 0.05) pausedAt = 0;

    for (const track of tracks) {
      const source = ctxAudio.createBufferSource();
      source.buffer = track.buffer;
      source.connect(track.analyser);
      source.start(0, pausedAt % track.buffer.duration);
      track.source = source;
    }

    startedAt = ctxAudio.currentTime - pausedAt;
    isPlaying = true;
    playButton.textContent = "Stop";
    playButton.classList.add("is-active");
    updateAudioStatus("playing");
  });
}

function stopAudio(keepPosition) {
  if (audioContext && keepPosition) {
    pausedAt = Math.max(0, audioContext.currentTime - startedAt);
  } else if (!keepPosition) {
    pausedAt = 0;
  }

  for (const track of tracks) {
    if (!track.source) continue;
    try {
      track.source.stop();
    } catch {
      // Source may already be stopped by the browser.
    }
    track.source.disconnect();
    track.source = null;
  }

  isPlaying = false;
  if (playButton) {
    playButton.textContent = keepPosition ? "Play" : "Play";
    playButton.classList.remove("is-active");
  }
  if (audioMode) updateAudioStatus(keepPosition ? "paused" : "loaded");
}

function restartAudio() {
  if (!audioMode || !tracks.length) return;
  stopAudio(false);
  pausedAt = 0;
  playAudio();
}

function seekAudio(seconds) {
  if (!audioMode || !loadedDuration) return;
  const wasPlaying = isPlaying;
  pausedAt = Math.max(0, Math.min(loadedDuration, seconds));
  stopAudio(false);
  pausedAt = Math.max(0, Math.min(loadedDuration, seconds));
  updateTimelineReadout();
  if (wasPlaying) playAudio();
}

function updateAudioStatus(state) {
  if (!audioMode) {
    audioStatus.textContent = "Mock 4-track compare running";
    return;
  }

  const visibleNames = loadedFileNames.slice(0, 3).join(" · ");
  const extra = loadedFileNames.length > 3 ? ` · +${loadedFileNames.length - 3}` : "";
  const prefix =
    state === "playing"
      ? "Playing"
      : state === "paused"
        ? "Paused"
        : "Loaded";
  audioStatus.textContent = `${prefix} ${tracks.length}/${maxCompareTracks}: ${visibleNames}${extra}`;
}

function currentAudioTime() {
  if (!audioMode || !audioContext) return 0;
  return isPlaying ? Math.max(0, audioContext.currentTime - startedAt) : pausedAt;
}

function formatTime(seconds) {
  const safeSeconds = Math.max(0, seconds || 0);
  const minutes = Math.floor(safeSeconds / 60);
  const wholeSeconds = Math.floor(safeSeconds % 60);
  const tenths = Math.floor((safeSeconds % 1) * 10);
  return `${minutes}:${String(wholeSeconds).padStart(2, "0")}.${tenths}`;
}

function updateTimelineReadout() {
  if (!audioMode) {
    timeReadout.textContent = "Mock signal";
    windowReadout.textContent = "Spectrum now: x = frequency, y = dB";
    timelineStatus.textContent = "No timeline · synthetic live signal";
    scrubCurrent.textContent = "0:00.0";
    scrubDuration.textContent = "0:00.0";
    timelineScrub.disabled = true;
    timelineScrub.value = "0";
    return;
  }

  const now = Math.min(currentAudioTime(), loadedDuration || 0);
  const progress = loadedDuration ? Math.round((now / loadedDuration) * 100) : 0;
  const fftWindowMs = audioContext ? Math.round((4096 / audioContext.sampleRate) * 1000) : 93;
  timeReadout.textContent = `${formatTime(now)} / ${formatTime(loadedDuration)}`;
  windowReadout.textContent = `Analyzing current ~${fftWindowMs} ms window`;
  timelineStatus.textContent = `${progress}% through loaded audio`;
  scrubCurrent.textContent = formatTime(now);
  scrubDuration.textContent = formatTime(loadedDuration);
  if (!isScrubbing) {
    timelineScrub.value = loadedDuration ? String(Math.round((now / loadedDuration) * 1000)) : "0";
  }
}

function audioFrequencyToBinIndex(freqData, freq) {
  const nyquist = audioContext.sampleRate * 0.5;
  return Math.max(0, Math.min(freqData.length - 1, Math.round((freq / nyquist) * (freqData.length - 1))));
}

function updateAudioAnalysis() {
  if (!audioContext || !tracks.length) return;
  for (const track of tracks) {
    if (!track.analyser) continue;
    track.analyser.getFloatFrequencyData(track.freqData);
    track.analyser.getFloatTimeDomainData(track.timeData);
    let rmsLinear = 0;
    let peak = minDb;

    for (let i = 0; i < track.timeData.length; i++) {
      rmsLinear += track.timeData[i] * track.timeData[i];
    }
    track.rms = 20 * Math.log10(Math.sqrt(rmsLinear / track.timeData.length) + 0.000001);

    for (let i = 0; i < bins; i++) {
      const freq = freqAt(i);
      const sourceIndex = audioFrequencyToBinIndex(track.freqData, freq);
      const value = Math.max(minDb, Math.min(maxDb, track.freqData[sourceIndex]));
      const previous = track.spectrum[i];
      track.spectrum[i] += (value - previous) * Number(smoothInput.value);
      peak = Math.max(peak, track.spectrum[i]);
    }
    track.peak = peak;
  }

  if (masterAnalyser) {
    masterAnalyser.getFloatFrequencyData(masterFreqData);
    for (let i = 0; i < bins; i++) {
      const freq = freqAt(i);
      const sourceIndex = audioFrequencyToBinIndex(masterFreqData, freq);
      const value = Math.max(minDb, Math.min(maxDb, masterFreqData[sourceIndex]));
      master.spectrum[i] += (value - master.spectrum[i]) * 0.18;
      master.peakHold[i] = Math.max(master.spectrum[i], master.peakHold[i] * Number(decayInput.value) + minDb * (1 - Number(decayInput.value)));
    }
  }
}

function drawGrid() {
  ctx.clearRect(0, 0, width, height);
  ctx.fillStyle = "#080b0d";
  ctx.fillRect(0, 0, width, height);

  const freqs = [20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000];
  ctx.strokeStyle = "rgba(255,255,255,0.075)";
  ctx.lineWidth = 1;
  for (const freq of freqs) {
    const x = xForFreq(freq);
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, height);
    ctx.stroke();
  }

  for (let db = -72; db <= 0; db += 12) {
    const y = dbToY(db);
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(width, y);
    ctx.stroke();
    ctx.fillStyle = "rgba(237,243,245,0.38)";
    ctx.font = "11px Inter, sans-serif";
    ctx.fillText(`${db}`, 12, y - 5);
  }
}

function makePath(values, floor = height - 20) {
  const path = new Path2D();
  path.moveTo(0, floor);
  for (let i = 0; i < values.length; i++) {
    const x = (i / (values.length - 1)) * width;
    const y = dbToY(styledDb(values[i]));
    if (i === 0) path.lineTo(x, y);
    else path.lineTo(x, y);
  }
  path.lineTo(width, floor);
  path.closePath();
  return path;
}

function drawCurve(values, color, alpha = 1, lineWidth = 2, fillAlpha = 0.08) {
  const displayColor = colorWithHue(color);
  const displayFill = Math.max(fillAlpha, Number(waveFillInput.value));
  const area = makePath(values);
  const gradient = ctx.createLinearGradient(0, 0, 0, height);
  gradient.addColorStop(0, displayColor);
  gradient.addColorStop(1, "rgba(0,0,0,0)");
  ctx.globalAlpha = displayFill;
  ctx.fillStyle = gradient;
  ctx.fill(area);
  ctx.globalAlpha = 1;

  ctx.beginPath();
  for (let i = 0; i < values.length; i++) {
    const x = (i / (values.length - 1)) * width;
    const y = dbToY(styledDb(values[i]));
    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }
  ctx.strokeStyle = displayColor;
  ctx.globalAlpha = alpha;
  ctx.lineWidth = lineWidth;
  ctx.lineJoin = "round";
  ctx.shadowBlur = Number(waveGlowInput.value);
  ctx.shadowColor = displayColor;
  ctx.stroke();
  ctx.shadowBlur = 0;
  ctx.globalAlpha = 1;
}

function getTrackPeaks(track, limit = 4) {
  const peaks = [];
  for (let i = 4; i < bins - 4; i += 2) {
    const current = track.spectrum[i];
    if (current < -58) continue;
    if (current > track.spectrum[i - 2] && current > track.spectrum[i + 2]) {
      peaks.push({ index: i, db: current });
    }
  }

  return peaks.sort((a, b) => b.db - a.db).slice(0, limit);
}

function drawTrackIslands(track, alpha = 0.72, labelMode = "peak") {
  getTrackPeaks(track, 4).forEach((peak, peakNumber) => {
      const x = (peak.index / (bins - 1)) * width;
      const y = dbToY(peak.db);
      const masterY = dbToY(master.spectrum[peak.index]);
      const energy = Math.max(0, Math.min(1, (peak.db + 58) / 42));
      const markerY = Math.min(y, masterY + 18);
      const stemTop = Math.min(markerY + 8, height - 36);
      const stemBottom = Math.min(masterY + 30 + energy * 18, height - 28);
      const capsuleW = 8 + energy * 16;
      const capsuleH = 4 + energy * 4;

      ctx.strokeStyle = track.color;
      ctx.globalAlpha = alpha * 0.42;
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(x, stemTop);
      ctx.lineTo(x, stemBottom);
      ctx.stroke();

      ctx.fillStyle = track.color;
      ctx.globalAlpha = alpha * 0.86;
      ctx.beginPath();
      ctx.roundRect(x - capsuleW * 0.5, markerY - capsuleH * 0.5, capsuleW, capsuleH, capsuleH * 0.5);
      ctx.fill();

      ctx.globalAlpha = alpha * 0.22;
      ctx.fillRect(x - 1, stemBottom, 2, Math.max(0, height - stemBottom - 30));
      ctx.globalAlpha = 1;

      if ((labelMode === "all" && peakNumber < 2) || (labelMode === "peak" && peakNumber === 0 && energy > 0.4)) {
        drawTrackLabel(track, x + 8, markerY - 18, `${track.name} ${peak.db.toFixed(0)}`);
      }
    });
}

function drawTrackLabel(track, x, y, text) {
  const displayColor = colorWithHue(track.color);
  ctx.font = "11px Inter, sans-serif";
  const labelWidth = Math.min(86, ctx.measureText(text).width + 18);
  const labelX = Math.min(width - labelWidth - 8, Math.max(8, x));
  const labelY = Math.min(height - 48, Math.max(10, y));

  ctx.fillStyle = "rgba(8,10,12,0.74)";
  ctx.strokeStyle = displayColor;
  ctx.lineWidth = 1;
  roundRect(labelX, labelY, labelWidth, 22, 6);
  ctx.fill();
  ctx.stroke();

  ctx.fillStyle = displayColor;
  ctx.beginPath();
  ctx.arc(labelX + 8, labelY + 11, 3, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = "rgba(237,243,245,0.9)";
  ctx.fillText(text, labelX + 15, labelY + 14, labelWidth - 20);
}

function drawTerrainTexture() {
  for (let i = 0; i < bins; i += 3) {
    const x = (i / (bins - 1)) * width;
    const y = dbToY(master.spectrum[i]);
    const h = height - y - 26;
    const alpha = Math.max(0.02, Math.min(0.14, (master.spectrum[i] - minDb) / 95));
    ctx.fillStyle = `rgba(237,243,245,${alpha})`;
    ctx.fillRect(x, y, Math.max(1, width / bins), h);
  }
}

function findConflicts() {
  const threshold = Number(thresholdInput.value);
  const zones = [];
  const visible = tracks.filter((track) => track.visible);
  const reference = focusedTrack ? visible.find((track) => track.id === focusedTrack) : null;

  for (let start = 0; start < bins; start += 8) {
    const end = Math.min(bins, start + 16);
    const active = visible
      .map((track) => {
        const avg = track.spectrum.slice(start, end).reduce((sum, v) => sum + v, 0) / (end - start);
        return { track, avg };
      })
      .filter((entry) => entry.avg > threshold)
      .sort((a, b) => b.avg - a.avg);

    const pair = reference
      ? [
          active.find((entry) => entry.track.id === reference.id),
          active.filter((entry) => entry.track.id !== reference.id).sort((a, b) => b.avg - a.avg)[0],
        ].filter(Boolean)
      : active.slice(0, 2);

    if (pair.length >= 2) {
      const spread = Math.abs(pair[0].avg - pair[1].avg);
      const loudness = Math.max(0, Math.min(1, (Math.max(pair[0].avg, pair[1].avg) - threshold) / 28));
      const closeness = Math.max(0, Math.min(1, 1 - spread / 28));
      const intensity = Math.max(0, Math.min(1, loudness * 0.62 + closeness * 0.38));
      if (intensity > 0.32) {
        zones.push({
          start,
          end,
          from: freqAt(start),
          to: freqAt(end - 1),
          active: pair,
          delta: spread,
          referenceId: reference?.id || null,
          intensity,
        });
      }
    }
  }

  return zones
    .sort((a, b) => b.intensity - a.intensity)
    .filter((zone, index, all) => index === 0 || zone.start - all[index - 1].start > 9)
    .slice(0, 5);
}

function drawConflicts(zones) {
  if (!heatmap) return;
  for (const zone of zones.slice(0, 3)) {
    const center = Math.round((zone.start + zone.end) * 0.5);
    const x = (center / (bins - 1)) * width;
    const first = zone.active[0];
    const second = zone.active[1];
    const y1 = dbToY(styledDb(first.track.spectrum[center]));
    const y2 = dbToY(styledDb(second.track.spectrum[center]));
    const topY = Math.min(y1, y2);
    const bottomY = Math.max(y1, y2);
    const midY = (topY + bottomY) * 0.5;

    ctx.strokeStyle = `rgba(255,221,154,${0.52 + zone.intensity * 0.26})`;
    ctx.lineWidth = 1.4;
    ctx.beginPath();
    ctx.moveTo(x, topY);
    ctx.lineTo(x, bottomY);
    ctx.moveTo(x - 9, topY);
    ctx.lineTo(x + 9, topY);
    ctx.moveTo(x - 9, bottomY);
    ctx.lineTo(x + 9, bottomY);
    ctx.stroke();

    drawConflictDot(x, y1, first.track.color);
    drawConflictDot(x, y2, second.track.color);
    drawConflictBadge(zone, x + 14, midY - 24, center);

    const stripX = (zone.start / (bins - 1)) * width;
    const stripW = ((zone.end - zone.start) / (bins - 1)) * width;
    ctx.fillStyle = `rgba(255,191,95,${0.18 + zone.intensity * 0.32})`;
    ctx.fillRect(stripX, height - 8, Math.max(14, stripW), 3);
  }
}

function drawConflictDot(x, y, color) {
  ctx.fillStyle = colorWithHue(color);
  ctx.strokeStyle = "rgba(8,10,12,0.78)";
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.arc(x, y, 5, 0, Math.PI * 2);
  ctx.fill();
  ctx.stroke();
}

function drawConflictBadge(zone, x, y, center) {
  const first = zone.active[0];
  const second = zone.active[1];
  const firstDb = first.track.spectrum[center].toFixed(0);
  const secondDb = second.track.spectrum[center].toFixed(0);
  const title = `${first.track.name} / ${second.track.name}`;
  const detail = `${firstDb} vs ${secondDb} dB   Δ ${zone.delta.toFixed(1)}`;
  const badgeWidth = 156;
  const badgeHeight = 44;
  const labelX = Math.min(width - badgeWidth - 10, Math.max(10, x));
  const labelY = Math.min(height - badgeHeight - 16, Math.max(12, y));

  ctx.fillStyle = "rgba(8,10,12,0.84)";
  ctx.strokeStyle = `rgba(255,221,154,${0.38 + zone.intensity * 0.34})`;
  ctx.lineWidth = 1;
  roundRect(labelX, labelY, badgeWidth, badgeHeight, 7);
  ctx.fill();
  ctx.stroke();

  ctx.fillStyle = first.track.color;
  ctx.beginPath();
  ctx.arc(labelX + 10, labelY + 14, 3, 0, Math.PI * 2);
  ctx.fill();
  ctx.fillStyle = second.track.color;
  ctx.beginPath();
  ctx.arc(labelX + 18, labelY + 14, 3, 0, Math.PI * 2);
  ctx.fill();

  ctx.font = "11px Inter, sans-serif";
  ctx.fillStyle = "rgba(237,243,245,0.94)";
  ctx.fillText(title, labelX + 27, labelY + 17, badgeWidth - 34);
  ctx.fillStyle = "rgba(255,221,154,0.9)";
  ctx.fillText(detail, labelX + 10, labelY + 33, badgeWidth - 18);
}

function roundRect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function renderTracks() {
  trackList.innerHTML = tracks
    .map((track) => {
      const selectedId = focusedTrack || hoveredTrack;
      const muted = selectedId && selectedId !== track.id;
      return `
        <button class="track-card ${selectedId === track.id ? "is-focus" : ""} ${muted ? "is-muted" : ""}" data-track="${track.id}" style="--track-color:${track.color}">
          <span class="track-swatch"></span>
          <span>
            <span class="track-name">${track.name}</span>
            <span class="track-meta"><span>${focusedTrack === track.id ? "Reference" : "Compare"}</span><span>RMS ${track.rms.toFixed(1)}</span><span>Peak ${track.peak.toFixed(1)}</span></span>
          </span>
          <strong class="track-value">${Math.round(track.peak)}</strong>
        </button>
      `;
    })
    .join("");
}

function formatFreq(freq) {
  if (freq >= 1000) return `${(freq / 1000).toFixed(freq >= 10000 ? 0 : 1)} kHz`;
  return `${Math.round(freq)} Hz`;
}

function noteForFreq(freq) {
  const noteNumber = Math.round(12 * Math.log2(freq / 440) + 69);
  const names = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
  const octave = Math.floor(noteNumber / 12) - 1;
  return `${names[((noteNumber % 12) + 12) % 12]}${octave}`;
}

function inspectAtIndex(index) {
  const freq = freqAt(index);
  const ranked = tracks
    .map((track) => ({ track, db: track.spectrum[index] }))
    .sort((a, b) => b.db - a.db)
    .slice(0, 4);
  const reference = focusedTrack ? tracks.find((track) => track.id === focusedTrack) : null;
  const referenceEntry = reference ? { track: reference, db: reference.spectrum[index] } : ranked[0];
  const comparisonEntry = reference
    ? tracks
        .filter((track) => track.id !== reference.id)
        .map((track) => ({ track, db: track.spectrum[index] }))
        .sort((a, b) => b.db - a.db)[0]
    : ranked[1];
  const delta = referenceEntry && comparisonEntry ? Math.abs(referenceEntry.db - comparisonEntry.db) : 0;
  const isConflict =
    referenceEntry &&
    comparisonEntry &&
    referenceEntry.db > Number(thresholdInput.value) &&
    comparisonEntry.db > Number(thresholdInput.value);

  return {
    index,
    freq,
    note: noteForFreq(freq),
    masterDb: master.spectrum[index],
    ranked,
    referenceEntry,
    comparisonEntry,
    delta,
    isConflict,
  };
}

function inspectAt(x) {
  const rawIndex = Math.max(0, Math.min(bins - 1, Math.round((x / width) * (bins - 1))));
  const stableIndex = Math.max(0, Math.min(bins - 1, Math.round(rawIndex / 3) * 3));
  return inspectAtIndex(stableIndex);
}

function renderPointInspector(data, locked = false) {
  if (!inspectState || !pointInspector) return;
  inspectState.textContent = locked ? "Locked" : frozen ? "Paused inspect" : "Live hover";
  pointInspector.innerHTML = `
    <div class="inspect-primary">
      <strong>${formatFreq(data.freq)} <span>${data.note}</span></strong>
      <span>${data.referenceEntry.track.name} vs ${data.comparisonEntry.track.name} · ${data.isConflict ? "Conflict" : "Clear"} · Δ ${data.delta.toFixed(1)} dB</span>
    </div>
    <div class="inspect-tracks">
      <div class="inspect-track is-reference" style="--track-color:${data.referenceEntry.track.color}">
        <span><i></i>Reference · ${data.referenceEntry.track.name}</span>
        <strong>${data.referenceEntry.db.toFixed(1)} dB</strong>
      </div>
      <div class="inspect-track is-compared" style="--track-color:${data.comparisonEntry.track.color}">
        <span><i></i>Compared · ${data.comparisonEntry.track.name}</span>
        <strong>${data.comparisonEntry.db.toFixed(1)} dB</strong>
      </div>
      ${data.ranked
        .filter((entry) => entry.track.id !== data.referenceEntry.track.id && entry.track.id !== data.comparisonEntry.track.id)
        .map(
          (entry) => `
            <div class="inspect-track" style="--track-color:${entry.track.color}">
              <span><i></i>${entry.track.name}</span>
              <strong>${entry.db.toFixed(1)} dB</strong>
            </div>
          `,
        )
        .join("")}
    </div>
  `;
}

function clearPointInspector() {
  if (lockedPointer || !inspectState || !pointInspector) return;
  inspectState.textContent = frozen ? "Paused" : "Live hover";
  pointInspector.innerHTML = `
    <div class="inspect-primary">
      <strong>${focusedTrack ? "Reference Compare" : "4 Track Compare"}</strong>
      <span>${focusedTrack ? "Hover to compare selected reference against the strongest other track." : "Click a lane to make it the reference, or hover the graph for loudest-vs-second delta."}</span>
    </div>
  `;
}

function renderConflicts(zones) {
  if (!conflictCount || !conflictList) return;
  conflictCount.textContent = `${zones.length} live`;
  if (!zones.length) {
    conflictList.innerHTML = `<div class="empty-state">No strong overlap in this moment.</div>`;
    return;
  }
  conflictList.innerHTML = zones
    .map((zone) => {
      const names = zone.active.map((entry) => entry.track.name).join(" + ");
      const firstTrack = zone.referenceId || zone.active[0].track.id;
      return `
        <button class="conflict-item" data-track="${firstTrack}">
          <div class="conflict-top">
            <span>${names}</span>
            <span class="conflict-range">${formatFreq(zone.from)}-${formatFreq(zone.to)}</span>
          </div>
          <div class="conflict-tracks">${zone.referenceId ? "Reference delta" : "Top pair delta"} ${zone.delta.toFixed(1)} dB · Overlap ${(zone.intensity * 100).toFixed(0)}%</div>
          <div class="conflict-bar" style="transform:scaleX(${zone.intensity})"></div>
        </button>
      `;
    })
    .join("");
}

function drawPointer() {
  const activePointer = lockedPointer || pointer;
  if (!activePointer) return;
  const data = inspectAt(activePointer.x);
  const x = (data.index / (bins - 1)) * width;
  const shouldRenderInspector =
    lockedPointer || data.index !== lastInspectIndex || performance.now() - lastInspectRender > 120;
  lastInspectIndex = data.index;

  ctx.strokeStyle = lockedPointer ? "rgba(255,221,154,0.58)" : "rgba(237,243,245,0.34)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(x, 0);
  ctx.lineTo(x, height);
  ctx.stroke();

  cursorReadout.classList.remove("is-hidden");
  cursorReadout.style.left = `${x}px`;
  cursorReadout.style.top = "58px";
  cursorReadout.innerHTML = `
    <strong>Δ ${data.delta.toFixed(1)} dB</strong>
    <span>${data.referenceEntry.track.name} vs ${data.comparisonEntry.track.name}</span>
    <span>${formatFreq(data.freq)} · ${data.note}${data.isConflict ? " · conflict" : ""}</span>
  `;

  if (shouldRenderInspector) {
    lastInspectRender = performance.now();
    renderPointInspector(data, Boolean(lockedPointer));
  }
}

function frame(now) {
  if (now - lastFrame < 32) {
    requestAnimationFrame(frame);
    return;
  }
  lastFrame = now;

  const time = now / 1000;
  if (!frozen) {
    if (audioMode) {
      updateAudioAnalysis();
    } else {
      for (const track of tracks) generateTrack(track, time);
      updateMaster();
    }
  }

  const conflicts = findConflicts();
  drawGrid();
  const selectedId = focusedTrack || hoveredTrack;
  const baseWidth = Number(waveWidthInput.value);
  const dimAlpha = Number(waveDimInput.value);

  for (const track of tracks) {
    const isSelected = selectedId === track.id;
    const isMuted = selectedId && !isSelected;
    drawCurve(
      track.spectrum,
      track.color,
      isMuted ? dimAlpha : isSelected ? 0.98 : 0.62,
      isSelected ? baseWidth + 1 : baseWidth,
      isSelected ? Number(waveFillInput.value) + 0.05 : Number(waveFillInput.value),
    );
  }

  drawConflicts(conflicts);

  if (selectedId) {
    const selected = tracks.find((track) => track.id === selectedId);
    if (selected) {
      getTrackPeaks(selected, 3).forEach((peak) => {
        drawTrackLabel(selected, (peak.index / (bins - 1)) * width + 8, dbToY(styledDb(peak.db)) - 22, `${selected.name} ${peak.db.toFixed(0)}`);
      });
    }
  }

  drawPointer();

  if (now - lastSidebarRender > 460) {
    lastSidebarRender = now;
    renderTracks();
    renderConflicts(conflicts);
    updateTimelineReadout();
  }

  requestAnimationFrame(frame);
}

function bindEvents() {
  trackList.addEventListener("click", (event) => {
    const card = event.target.closest(".track-card");
    if (!card) return;
    focusedTrack = focusedTrack === card.dataset.track ? null : card.dataset.track;
    clearPointInspector();
  });

  trackList.addEventListener("mouseover", (event) => {
    const card = event.target.closest(".track-card");
    if (!card || focusedTrack) return;
    hoveredTrack = card.dataset.track;
  });

  trackList.addEventListener("mouseleave", () => {
    hoveredTrack = null;
  });

  if (conflictList) {
    conflictList.addEventListener("click", (event) => {
      const item = event.target.closest(".conflict-item");
      if (!item) return;
      focusedTrack = item.dataset.track;
    });
  }

  resetFocus.addEventListener("click", () => {
    focusedTrack = null;
    hoveredTrack = null;
    lockedPointer = null;
    clearPointInspector();
  });

  canvas.addEventListener("mousemove", (event) => {
    const rect = canvas.getBoundingClientRect();
    pointer = { x: event.clientX - rect.left, y: event.clientY - rect.top };
  });

  canvas.addEventListener("click", (event) => {
    const rect = canvas.getBoundingClientRect();
    const nextPointer = { x: event.clientX - rect.left, y: event.clientY - rect.top };
    if (lockedPointer && Math.abs(lockedPointer.x - nextPointer.x) < 8) {
      lockedPointer = null;
      clearPointInspector();
      return;
    }
    lockedPointer = nextPointer;
  });

  canvas.addEventListener("mouseleave", () => {
    pointer = null;
    if (!lockedPointer) {
      cursorReadout.classList.add("is-hidden");
      clearPointInspector();
    }
  });

  document.getElementById("freezeButton").addEventListener("click", (event) => {
    frozen = !frozen;
    event.currentTarget.classList.toggle("is-active", frozen);
    event.currentTarget.textContent = frozen ? "Resume" : "Pause";
    if (inspectState) {
      inspectState.textContent = lockedPointer ? "Locked" : frozen ? "Paused" : "Live hover";
    }
  });

  document.getElementById("snapshotButton").addEventListener("click", (event) => {
    event.currentTarget.classList.add("is-active");
    setTimeout(() => event.currentTarget.classList.remove("is-active"), 420);
  });

  document.getElementById("heatmapButton").addEventListener("click", (event) => {
    heatmap = !heatmap;
    event.currentTarget.classList.toggle("is-active", heatmap);
  });

  resetVisuals.addEventListener("click", () => {
    waveAmpInput.value = defaultVisuals.amp;
    waveGlowInput.value = defaultVisuals.glow;
    waveFillInput.value = defaultVisuals.fill;
    waveWidthInput.value = defaultVisuals.width;
    waveDimInput.value = defaultVisuals.dim;
    waveHueInput.value = defaultVisuals.hue;
  });

  audioFilesInput.addEventListener("change", (event) => {
    loadAudioFiles(event.target.files).catch((error) => {
      audioStatus.textContent = error.message || "Could not load audio";
      console.error(error);
    });
  });

  demoButton.addEventListener("click", () => {
    loadDemoAudio().catch((error) => {
      audioStatus.textContent = error.message || "Could not create demo audio";
      console.error(error);
    });
  });

  playButton.addEventListener("click", playAudio);
  restartButton.addEventListener("click", restartAudio);

  timelineScrub.addEventListener("input", () => {
    if (!audioMode || !loadedDuration) return;
    isScrubbing = true;
    const seconds = (Number(timelineScrub.value) / 1000) * loadedDuration;
    scrubCurrent.textContent = formatTime(seconds);
    timeReadout.textContent = `${formatTime(seconds)} / ${formatTime(loadedDuration)}`;
    timelineStatus.textContent = `${Math.round((seconds / loadedDuration) * 100)}% through loaded audio`;
  });

  timelineScrub.addEventListener("change", () => {
    if (!audioMode || !loadedDuration) return;
    const seconds = (Number(timelineScrub.value) / 1000) * loadedDuration;
    isScrubbing = false;
    seekAudio(seconds);
  });

  window.addEventListener("resize", resizeCanvas);
}

resizeCanvas();
bindEvents();
renderTracks();
requestAnimationFrame(frame);
const canvas = document.getElementById("spectrumCanvas");
const ctx = canvas.getContext("2d");
const trackList = document.getElementById("trackList");
const conflictList = document.getElementById("conflictList");
const cursorReadout = document.getElementById("cursorReadout");
const smoothInput = document.getElementById("smooth");
const decayInput = document.getElementById("decay");
const thresholdInput = document.getElementById("threshold");
const resetFocus = document.getElementById("resetFocus");
const conflictCount = document.getElementById("conflictCount");
const pointInspector = document.getElementById("pointInspector");
const inspectState = document.getElementById("inspectState");
const audioFilesInput = document.getElementById("audioFiles");
const audioStatus = document.getElementById("audioStatus");
const timelineStatus = document.getElementById("timelineStatus");
const timeReadout = document.getElementById("timeReadout");
const windowReadout = document.getElementById("windowReadout");
const timelineScrub = document.getElementById("timelineScrub");
const scrubCurrent = document.getElementById("scrubCurrent");
const scrubDuration = document.getElementById("scrubDuration");
const playButton = document.getElementById("playButton");
const restartButton = document.getElementById("restartButton");
const waveAmpInput = document.getElementById("waveAmp");
const waveGlowInput = document.getElementById("waveGlow");
const waveFillInput = document.getElementById("waveFill");
const waveWidthInput = document.getElementById("waveWidth");
const waveDimInput = document.getElementById("waveDim");
const waveHueInput = document.getElementById("waveHue");
const resetVisuals = document.getElementById("resetVisuals");

const bins = 256;
const maxCompareTracks = 4;
const minDb = -78;
const maxDb = 6;
const minFreq = 20;
const maxFreq = 20000;
let width = 0;
let height = 0;
let dpr = 1;
let mode = "compare";
let focusedTrack = null;
let frozen = false;
let heatmap = true;
let pointer = null;
let lockedPointer = null;
let hoveredTrack = null;
let lastFrame = 0;
let lastSidebarRender = 0;
let lastInspectIndex = -1;
let lastInspectRender = 0;
let audioMode = false;
let audioContext = null;
let masterGain = null;
let masterAnalyser = null;
let masterFreqData = null;
let isPlaying = false;
let startedAt = 0;
let pausedAt = 0;
let loadedFileNames = [];
let loadedDuration = 0;
let isScrubbing = false;

const palette = ["#5cf2c8", "#7897ff", "#ff6d91", "#ffbd63", "#b77dff", "#46c4ff", "#d8f26b", "#f27ce4"];
const defaultVisuals = {
  amp: 1,
  glow: 14,
  fill: 0.03,
  width: 1.6,
  dim: 0.26,
  hue: 0,
};

let tracks = [
  { id: "kick", name: "Kick", color: palette[0], base: 0.88, peaks: [[58, 1.0, 0.045], [118, 0.45, 0.035], [3200, 0.16, 0.08]] },
  { id: "bass", name: "Bass", color: palette[1], base: 0.8, peaks: [[72, 0.9, 0.07], [142, 0.72, 0.06], [720, 0.22, 0.08]] },
  { id: "vocal", name: "Vocal", color: palette[2], base: 0.7, peaks: [[210, 0.24, 0.08], [1200, 0.68, 0.11], [3100, 0.86, 0.12], [8200, 0.38, 0.12]] },
  { id: "drums", name: "Drum Bus", color: palette[3], base: 0.58, peaks: [[180, 0.34, 0.06], [2400, 0.35, 0.18], [9000, 0.62, 0.18]] },
  { id: "pad", name: "Pad", color: palette[4], base: 0.54, peaks: [[260, 0.28, 0.1], [820, 0.46, 0.14], [5200, 0.35, 0.2]] },
  { id: "lead", name: "Lead", color: palette[5], base: 0.5, peaks: [[540, 0.2, 0.08], [1800, 0.74, 0.1], [5600, 0.52, 0.12]] },
  { id: "hats", name: "Hats", color: palette[6], base: 0.44, peaks: [[6800, 0.58, 0.16], [11200, 0.72, 0.13], [15800, 0.28, 0.12]] },
  { id: "fx", name: "FX Return", color: palette[7], base: 0.38, peaks: [[430, 0.18, 0.12], [3900, 0.36, 0.2], [12600, 0.4, 0.18]] },
]
  .slice(0, maxCompareTracks)
  .map((track, index) => ({
  ...track,
  phase: index * 7.13,
  spectrum: new Array(bins).fill(minDb),
  target: new Array(bins).fill(minDb),
  rms: -24,
  peak: -9,
  visible: true,
  analyser: null,
  freqData: null,
  timeData: null,
  buffer: null,
  source: null,
}));

const master = {
  spectrum: new Array(bins).fill(minDb),
  peakHold: new Array(bins).fill(minDb),
};

function resizeCanvas() {
  const rect = canvas.getBoundingClientRect();
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  width = Math.max(1, Math.floor(rect.width));
  height = Math.max(1, Math.floor(rect.height));
  canvas.width = Math.floor(width * dpr);
  canvas.height = Math.floor(height * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}

function freqAt(index) {
  const t = index / (bins - 1);
  return minFreq * Math.pow(maxFreq / minFreq, t);
}

function xForFreq(freq) {
  return (Math.log(freq / minFreq) / Math.log(maxFreq / minFreq)) * width;
}

function dbToY(db) {
  const normalized = (db - minDb) / (maxDb - minDb);
  return height - Math.max(0, Math.min(1, normalized)) * (height - 42) - 22;
}

function styledDb(db) {
  const amp = Number(waveAmpInput.value);
  return Math.max(minDb, Math.min(maxDb, minDb + (db - minDb) * amp));
}

function colorWithHue(hex) {
  const shift = Number(waveHueInput.value);
  if (!shift) return hex;
  const r = parseInt(hex.slice(1, 3), 16) / 255;
  const g = parseInt(hex.slice(3, 5), 16) / 255;
  const b = parseInt(hex.slice(5, 7), 16) / 255;
  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  let h = 0;
  let s = 0;
  const l = (max + min) / 2;
  const d = max - min;
  if (d !== 0) {
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    if (max === r) h = (g - b) / d + (g < b ? 6 : 0);
    else if (max === g) h = (b - r) / d + 2;
    else h = (r - g) / d + 4;
    h *= 60;
  }
  return `hsl(${(h + shift + 360) % 360} ${Math.round(s * 100)}% ${Math.round(l * 100)}%)`;
}

function gaussLog(freq, center, amp, spread) {
  const distance = Math.log(freq / center) / Math.log(maxFreq / minFreq);
  return amp * Math.exp(-(distance * distance) / (2 * spread * spread));
}

function generateTrack(track, time) {
  const pulse = 0.78 + Math.sin(time * (1.1 + track.base * 0.8) + track.phase) * 0.12;
  let energy = 0;

  for (let i = 0; i < bins; i++) {
    const freq = freqAt(i);
    const tilt = 1 - i / bins;
    const breath = Math.sin(time * 2.2 + track.phase + i * 0.08) * 0.035;
    const noise = Math.sin(time * 7.0 + i * 1.7 + track.phase) * 0.018;
    let value = 0.035 + tilt * 0.12 + breath + noise;

    for (const peak of track.peaks) {
      value += gaussLog(freq, peak[0], peak[1], peak[2]);
    }

    value *= track.base * pulse;
    const db = minDb + value * 72;
    track.target[i] = Math.max(minDb, Math.min(maxDb, db));
    track.spectrum[i] += (track.target[i] - track.spectrum[i]) * Number(smoothInput.value);
    energy += Math.pow(10, track.spectrum[i] / 20);
  }

  track.rms = 20 * Math.log10(energy / bins + 0.0001) + 9;
  track.peak = Math.max(...track.spectrum) - 4;
}

function updateMaster() {
  for (let i = 0; i < bins; i++) {
    let linear = 0;
    for (const track of tracks) {
      if (!track.visible) continue;
      linear += Math.pow(10, track.spectrum[i] / 20);
    }
    const db = 20 * Math.log10(linear / 2.2 + 0.00001);
    master.spectrum[i] += (db - master.spectrum[i]) * 0.18;
    master.peakHold[i] = Math.max(master.spectrum[i], master.peakHold[i] * Number(decayInput.value) + minDb * (1 - Number(decayInput.value)));
  }
}

function setupAnalyser(analyser) {
  analyser.fftSize = 4096;
  analyser.minDecibels = minDb;
  analyser.maxDecibels = maxDb;
  analyser.smoothingTimeConstant = 0.72;
}

async function ensureAudioContext() {
  if (audioContext) return audioContext;
  audioContext = new AudioContext();
  masterGain = audioContext.createGain();
  masterGain.gain.value = 0.82;
  masterAnalyser = audioContext.createAnalyser();
  setupAnalyser(masterAnalyser);
  masterFreqData = new Float32Array(masterAnalyser.frequencyBinCount);
  masterGain.connect(masterAnalyser);
  masterAnalyser.connect(audioContext.destination);
  return audioContext;
}

async function loadAudioFiles(files) {
  const selected = [...files].slice(0, maxCompareTracks);
  if (!selected.length) return;
  const ctxAudio = await ensureAudioContext();
  stopAudio(false);
  audioStatus.textContent = `Decoding ${selected.length} of ${maxCompareTracks} compare slots`;

  const decoded = await Promise.all(
    selected.map(async (file, index) => {
      const arrayBuffer = await file.arrayBuffer();
      const buffer = await ctxAudio.decodeAudioData(arrayBuffer);
      return createAudioTrack(file.name.replace(/\.[^/.]+$/, ""), buffer, index);
    }),
  );

  tracks = decoded;
  loadedFileNames = decoded.map((track) => track.name);
  loadedDuration = Math.max(...decoded.map((track) => track.buffer?.duration || 0));
  audioMode = true;
  focusedTrack = null;
  hoveredTrack = null;
  lockedPointer = null;
  for (let i = 0; i < bins; i++) {
    master.spectrum[i] = minDb;
    master.peakHold[i] = minDb;
  }
  renderTracks();
  clearPointInspector();
  updateAudioStatus("loaded");
  playButton.textContent = "Play";
  playButton.classList.remove("is-active");
  timelineScrub.disabled = false;
  timelineScrub.value = "0";
  updateTimelineReadout();
}

function createAudioTrack(name, buffer, index) {
  const analyser = audioContext.createAnalyser();
  setupAnalyser(analyser);
  analyser.connect(masterGain);
  return {
    id: `audio-${index}`,
    name: name || `Track ${index + 1}`,
    color: palette[index % palette.length],
    base: 0,
    peaks: [],
    phase: index * 7.13,
    spectrum: new Array(bins).fill(minDb),
    target: new Array(bins).fill(minDb),
    rms: minDb,
    peak: minDb,
    visible: true,
    analyser,
    freqData: new Float32Array(analyser.frequencyBinCount),
    timeData: new Float32Array(analyser.fftSize),
    buffer,
    source: null,
  };
}

function playAudio() {
  if (!audioMode || !tracks.length) return;
  ensureAudioContext().then((ctxAudio) => {
    if (isPlaying) {
      stopAudio(true);
      return;
    }

    if (ctxAudio.state === "suspended") ctxAudio.resume();
    const startOffset = pausedAt;
    const longest = Math.max(...tracks.map((track) => track.buffer?.duration || 0));
    if (startOffset >= longest - 0.05) pausedAt = 0;

    for (const track of tracks) {
      const source = ctxAudio.createBufferSource();
      source.buffer = track.buffer;
      source.connect(track.analyser);
      source.start(0, pausedAt % track.buffer.duration);
      track.source = source;
    }

    startedAt = ctxAudio.currentTime - pausedAt;
    isPlaying = true;
    playButton.textContent = "Stop";
    playButton.classList.add("is-active");
    updateAudioStatus("playing");
  });
}

function stopAudio(keepPosition) {
  if (audioContext && keepPosition) {
    pausedAt = Math.max(0, audioContext.currentTime - startedAt);
  } else if (!keepPosition) {
    pausedAt = 0;
  }

  for (const track of tracks) {
    if (!track.source) continue;
    try {
      track.source.stop();
    } catch {
      // Source may already be stopped by the browser.
    }
    track.source.disconnect();
    track.source = null;
  }

  isPlaying = false;
  if (playButton) {
    playButton.textContent = keepPosition ? "Play" : "Play";
    playButton.classList.remove("is-active");
  }
  if (audioMode) updateAudioStatus(keepPosition ? "paused" : "loaded");
}

function restartAudio() {
  if (!audioMode || !tracks.length) return;
  stopAudio(false);
  pausedAt = 0;
  playAudio();
}

function seekAudio(seconds) {
  if (!audioMode || !loadedDuration) return;
  const wasPlaying = isPlaying;
  pausedAt = Math.max(0, Math.min(loadedDuration, seconds));
  stopAudio(false);
  pausedAt = Math.max(0, Math.min(loadedDuration, seconds));
  updateTimelineReadout();
  if (wasPlaying) playAudio();
}

function updateAudioStatus(state) {
  if (!audioMode) {
    audioStatus.textContent = "Mock 4-track compare running";
    return;
  }

  const visibleNames = loadedFileNames.slice(0, 3).join(" · ");
  const extra = loadedFileNames.length > 3 ? ` · +${loadedFileNames.length - 3}` : "";
  const prefix =
    state === "playing"
      ? "Playing"
      : state === "paused"
        ? "Paused"
        : "Loaded";
  audioStatus.textContent = `${prefix} ${tracks.length}/${maxCompareTracks}: ${visibleNames}${extra}`;
}

function currentAudioTime() {
  if (!audioMode || !audioContext) return 0;
  return isPlaying ? Math.max(0, audioContext.currentTime - startedAt) : pausedAt;
}

function formatTime(seconds) {
  const safeSeconds = Math.max(0, seconds || 0);
  const minutes = Math.floor(safeSeconds / 60);
  const wholeSeconds = Math.floor(safeSeconds % 60);
  const tenths = Math.floor((safeSeconds % 1) * 10);
  return `${minutes}:${String(wholeSeconds).padStart(2, "0")}.${tenths}`;
}

function updateTimelineReadout() {
  if (!audioMode) {
    timeReadout.textContent = "Mock signal";
    windowReadout.textContent = "Spectrum now: x = frequency, y = dB";
    timelineStatus.textContent = "No timeline · synthetic live signal";
    scrubCurrent.textContent = "0:00.0";
    scrubDuration.textContent = "0:00.0";
    timelineScrub.disabled = true;
    timelineScrub.value = "0";
    return;
  }

  const now = Math.min(currentAudioTime(), loadedDuration || 0);
  const progress = loadedDuration ? Math.round((now / loadedDuration) * 100) : 0;
  const fftWindowMs = audioContext ? Math.round((4096 / audioContext.sampleRate) * 1000) : 93;
  timeReadout.textContent = `${formatTime(now)} / ${formatTime(loadedDuration)}`;
  windowReadout.textContent = `Analyzing current ~${fftWindowMs} ms window`;
  timelineStatus.textContent = `${progress}% through loaded audio`;
  scrubCurrent.textContent = formatTime(now);
  scrubDuration.textContent = formatTime(loadedDuration);
  if (!isScrubbing) {
    timelineScrub.value = loadedDuration ? String(Math.round((now / loadedDuration) * 1000)) : "0";
  }
}

function audioFrequencyToBinIndex(freqData, freq) {
  const nyquist = audioContext.sampleRate * 0.5;
  return Math.max(0, Math.min(freqData.length - 1, Math.round((freq / nyquist) * (freqData.length - 1))));
}

function updateAudioAnalysis() {
  if (!audioContext || !tracks.length) return;
  for (const track of tracks) {
    if (!track.analyser) continue;
    track.analyser.getFloatFrequencyData(track.freqData);
    track.analyser.getFloatTimeDomainData(track.timeData);
    let rmsLinear = 0;
    let peak = minDb;

    for (let i = 0; i < track.timeData.length; i++) {
      rmsLinear += track.timeData[i] * track.timeData[i];
    }
    track.rms = 20 * Math.log10(Math.sqrt(rmsLinear / track.timeData.length) + 0.000001);

    for (let i = 0; i < bins; i++) {
      const freq = freqAt(i);
      const sourceIndex = audioFrequencyToBinIndex(track.freqData, freq);
      const value = Math.max(minDb, Math.min(maxDb, track.freqData[sourceIndex]));
      const previous = track.spectrum[i];
      track.spectrum[i] += (value - previous) * Number(smoothInput.value);
      peak = Math.max(peak, track.spectrum[i]);
    }
    track.peak = peak;
  }

  if (masterAnalyser) {
    masterAnalyser.getFloatFrequencyData(masterFreqData);
    for (let i = 0; i < bins; i++) {
      const freq = freqAt(i);
      const sourceIndex = audioFrequencyToBinIndex(masterFreqData, freq);
      const value = Math.max(minDb, Math.min(maxDb, masterFreqData[sourceIndex]));
      master.spectrum[i] += (value - master.spectrum[i]) * 0.18;
      master.peakHold[i] = Math.max(master.spectrum[i], master.peakHold[i] * Number(decayInput.value) + minDb * (1 - Number(decayInput.value)));
    }
  }
}

function drawGrid() {
  ctx.clearRect(0, 0, width, height);
  ctx.fillStyle = "#080b0d";
  ctx.fillRect(0, 0, width, height);

  const freqs = [20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000];
  ctx.strokeStyle = "rgba(255,255,255,0.075)";
  ctx.lineWidth = 1;
  for (const freq of freqs) {
    const x = xForFreq(freq);
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, height);
    ctx.stroke();
  }

  for (let db = -72; db <= 0; db += 12) {
    const y = dbToY(db);
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(width, y);
    ctx.stroke();
    ctx.fillStyle = "rgba(237,243,245,0.38)";
    ctx.font = "11px Inter, sans-serif";
    ctx.fillText(`${db}`, 12, y - 5);
  }
}

function makePath(values, floor = height - 20) {
  const path = new Path2D();
  path.moveTo(0, floor);
  for (let i = 0; i < values.length; i++) {
    const x = (i / (values.length - 1)) * width;
    const y = dbToY(styledDb(values[i]));
    if (i === 0) path.lineTo(x, y);
    else path.lineTo(x, y);
  }
  path.lineTo(width, floor);
  path.closePath();
  return path;
}

function drawCurve(values, color, alpha = 1, lineWidth = 2, fillAlpha = 0.08) {
  const displayColor = colorWithHue(color);
  const displayFill = Math.max(fillAlpha, Number(waveFillInput.value));
  const area = makePath(values);
  const gradient = ctx.createLinearGradient(0, 0, 0, height);
  gradient.addColorStop(0, displayColor);
  gradient.addColorStop(1, "rgba(0,0,0,0)");
  ctx.globalAlpha = displayFill;
  ctx.fillStyle = gradient;
  ctx.fill(area);
  ctx.globalAlpha = 1;

  ctx.beginPath();
  for (let i = 0; i < values.length; i++) {
    const x = (i / (values.length - 1)) * width;
    const y = dbToY(styledDb(values[i]));
    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }
  ctx.strokeStyle = displayColor;
  ctx.globalAlpha = alpha;
  ctx.lineWidth = lineWidth;
  ctx.lineJoin = "round";
  ctx.shadowBlur = Number(waveGlowInput.value);
  ctx.shadowColor = displayColor;
  ctx.stroke();
  ctx.shadowBlur = 0;
  ctx.globalAlpha = 1;
}

function getTrackPeaks(track, limit = 4) {
  const peaks = [];
  for (let i = 4; i < bins - 4; i += 2) {
    const current = track.spectrum[i];
    if (current < -58) continue;
    if (current > track.spectrum[i - 2] && current > track.spectrum[i + 2]) {
      peaks.push({ index: i, db: current });
    }
  }

  return peaks.sort((a, b) => b.db - a.db).slice(0, limit);
}

function drawTrackIslands(track, alpha = 0.72, labelMode = "peak") {
  getTrackPeaks(track, 4).forEach((peak, peakNumber) => {
      const x = (peak.index / (bins - 1)) * width;
      const y = dbToY(peak.db);
      const masterY = dbToY(master.spectrum[peak.index]);
      const energy = Math.max(0, Math.min(1, (peak.db + 58) / 42));
      const markerY = Math.min(y, masterY + 18);
      const stemTop = Math.min(markerY + 8, height - 36);
      const stemBottom = Math.min(masterY + 30 + energy * 18, height - 28);
      const capsuleW = 8 + energy * 16;
      const capsuleH = 4 + energy * 4;

      ctx.strokeStyle = track.color;
      ctx.globalAlpha = alpha * 0.42;
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(x, stemTop);
      ctx.lineTo(x, stemBottom);
      ctx.stroke();

      ctx.fillStyle = track.color;
      ctx.globalAlpha = alpha * 0.86;
      ctx.beginPath();
      ctx.roundRect(x - capsuleW * 0.5, markerY - capsuleH * 0.5, capsuleW, capsuleH, capsuleH * 0.5);
      ctx.fill();

      ctx.globalAlpha = alpha * 0.22;
      ctx.fillRect(x - 1, stemBottom, 2, Math.max(0, height - stemBottom - 30));
      ctx.globalAlpha = 1;

      if ((labelMode === "all" && peakNumber < 2) || (labelMode === "peak" && peakNumber === 0 && energy > 0.4)) {
        drawTrackLabel(track, x + 8, markerY - 18, `${track.name} ${peak.db.toFixed(0)}`);
      }
    });
}

function drawTrackLabel(track, x, y, text) {
  const displayColor = colorWithHue(track.color);
  ctx.font = "11px Inter, sans-serif";
  const labelWidth = Math.min(86, ctx.measureText(text).width + 18);
  const labelX = Math.min(width - labelWidth - 8, Math.max(8, x));
  const labelY = Math.min(height - 48, Math.max(10, y));

  ctx.fillStyle = "rgba(8,10,12,0.74)";
  ctx.strokeStyle = displayColor;
  ctx.lineWidth = 1;
  roundRect(labelX, labelY, labelWidth, 22, 6);
  ctx.fill();
  ctx.stroke();

  ctx.fillStyle = displayColor;
  ctx.beginPath();
  ctx.arc(labelX + 8, labelY + 11, 3, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = "rgba(237,243,245,0.9)";
  ctx.fillText(text, labelX + 15, labelY + 14, labelWidth - 20);
}

function drawTerrainTexture() {
  for (let i = 0; i < bins; i += 3) {
    const x = (i / (bins - 1)) * width;
    const y = dbToY(master.spectrum[i]);
    const h = height - y - 26;
    const alpha = Math.max(0.02, Math.min(0.14, (master.spectrum[i] - minDb) / 95));
    ctx.fillStyle = `rgba(237,243,245,${alpha})`;
    ctx.fillRect(x, y, Math.max(1, width / bins), h);
  }
}

function findConflicts() {
  const threshold = Number(thresholdInput.value);
  const zones = [];
  const visible = tracks.filter((track) => track.visible);
  const reference = focusedTrack ? visible.find((track) => track.id === focusedTrack) : null;

  for (let start = 0; start < bins; start += 8) {
    const end = Math.min(bins, start + 16);
    const active = visible
      .map((track) => {
        const avg = track.spectrum.slice(start, end).reduce((sum, v) => sum + v, 0) / (end - start);
        return { track, avg };
      })
      .filter((entry) => entry.avg > threshold)
      .sort((a, b) => b.avg - a.avg);

    const pair = reference
      ? [
          active.find((entry) => entry.track.id === reference.id),
          active.filter((entry) => entry.track.id !== reference.id).sort((a, b) => b.avg - a.avg)[0],
        ].filter(Boolean)
      : active.slice(0, 2);

    if (pair.length >= 2) {
      const spread = Math.abs(pair[0].avg - pair[1].avg);
      const loudness = Math.max(0, Math.min(1, (Math.max(pair[0].avg, pair[1].avg) - threshold) / 28));
      const closeness = Math.max(0, Math.min(1, 1 - spread / 28));
      const intensity = Math.max(0, Math.min(1, loudness * 0.62 + closeness * 0.38));
      if (intensity > 0.32) {
        zones.push({
          start,
          end,
          from: freqAt(start),
          to: freqAt(end - 1),
          active: pair,
          delta: spread,
          referenceId: reference?.id || null,
          intensity,
        });
      }
    }
  }

  return zones
    .sort((a, b) => b.intensity - a.intensity)
    .filter((zone, index, all) => index === 0 || zone.start - all[index - 1].start > 9)
    .slice(0, 5);
}

function drawConflicts(zones) {
  if (!heatmap) return;
  for (const zone of zones.slice(0, 3)) {
    const center = Math.round((zone.start + zone.end) * 0.5);
    const x = (center / (bins - 1)) * width;
    const first = zone.active[0];
    const second = zone.active[1];
    const y1 = dbToY(styledDb(first.track.spectrum[center]));
    const y2 = dbToY(styledDb(second.track.spectrum[center]));
    const topY = Math.min(y1, y2);
    const bottomY = Math.max(y1, y2);
    const midY = (topY + bottomY) * 0.5;

    ctx.strokeStyle = `rgba(255,221,154,${0.52 + zone.intensity * 0.26})`;
    ctx.lineWidth = 1.4;
    ctx.beginPath();
    ctx.moveTo(x, topY);
    ctx.lineTo(x, bottomY);
    ctx.moveTo(x - 9, topY);
    ctx.lineTo(x + 9, topY);
    ctx.moveTo(x - 9, bottomY);
    ctx.lineTo(x + 9, bottomY);
    ctx.stroke();

    drawConflictDot(x, y1, first.track.color);
    drawConflictDot(x, y2, second.track.color);
    drawConflictBadge(zone, x + 14, midY - 24, center);

    const stripX = (zone.start / (bins - 1)) * width;
    const stripW = ((zone.end - zone.start) / (bins - 1)) * width;
    ctx.fillStyle = `rgba(255,191,95,${0.18 + zone.intensity * 0.32})`;
    ctx.fillRect(stripX, height - 8, Math.max(14, stripW), 3);
  }
}

function drawConflictDot(x, y, color) {
  ctx.fillStyle = colorWithHue(color);
  ctx.strokeStyle = "rgba(8,10,12,0.78)";
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.arc(x, y, 5, 0, Math.PI * 2);
  ctx.fill();
  ctx.stroke();
}

function drawConflictBadge(zone, x, y, center) {
  const first = zone.active[0];
  const second = zone.active[1];
  const firstDb = first.track.spectrum[center].toFixed(0);
  const secondDb = second.track.spectrum[center].toFixed(0);
  const title = `${first.track.name} / ${second.track.name}`;
  const detail = `${firstDb} vs ${secondDb} dB   Δ ${zone.delta.toFixed(1)}`;
  const badgeWidth = 156;
  const badgeHeight = 44;
  const labelX = Math.min(width - badgeWidth - 10, Math.max(10, x));
  const labelY = Math.min(height - badgeHeight - 16, Math.max(12, y));

  ctx.fillStyle = "rgba(8,10,12,0.84)";
  ctx.strokeStyle = `rgba(255,221,154,${0.38 + zone.intensity * 0.34})`;
  ctx.lineWidth = 1;
  roundRect(labelX, labelY, badgeWidth, badgeHeight, 7);
  ctx.fill();
  ctx.stroke();

  ctx.fillStyle = first.track.color;
  ctx.beginPath();
  ctx.arc(labelX + 10, labelY + 14, 3, 0, Math.PI * 2);
  ctx.fill();
  ctx.fillStyle = second.track.color;
  ctx.beginPath();
  ctx.arc(labelX + 18, labelY + 14, 3, 0, Math.PI * 2);
  ctx.fill();

  ctx.font = "11px Inter, sans-serif";
  ctx.fillStyle = "rgba(237,243,245,0.94)";
  ctx.fillText(title, labelX + 27, labelY + 17, badgeWidth - 34);
  ctx.fillStyle = "rgba(255,221,154,0.9)";
  ctx.fillText(detail, labelX + 10, labelY + 33, badgeWidth - 18);
}

function roundRect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function renderTracks() {
  trackList.innerHTML = tracks
    .map((track) => {
      const selectedId = focusedTrack || hoveredTrack;
      const muted = selectedId && selectedId !== track.id;
      return `
        <button class="track-card ${selectedId === track.id ? "is-focus" : ""} ${muted ? "is-muted" : ""}" data-track="${track.id}" style="--track-color:${track.color}">
          <span class="track-swatch"></span>
          <span>
            <span class="track-name">${track.name}</span>
            <span class="track-meta"><span>${focusedTrack === track.id ? "Reference" : "Compare"}</span><span>RMS ${track.rms.toFixed(1)}</span><span>Peak ${track.peak.toFixed(1)}</span></span>
          </span>
          <strong class="track-value">${Math.round(track.peak)}</strong>
        </button>
      `;
    })
    .join("");
}

function formatFreq(freq) {
  if (freq >= 1000) return `${(freq / 1000).toFixed(freq >= 10000 ? 0 : 1)} kHz`;
  return `${Math.round(freq)} Hz`;
}

function noteForFreq(freq) {
  const noteNumber = Math.round(12 * Math.log2(freq / 440) + 69);
  const names = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
  const octave = Math.floor(noteNumber / 12) - 1;
  return `${names[((noteNumber % 12) + 12) % 12]}${octave}`;
}

function inspectAtIndex(index) {
  const freq = freqAt(index);
  const ranked = tracks
    .map((track) => ({ track, db: track.spectrum[index] }))
    .sort((a, b) => b.db - a.db)
    .slice(0, 4);
  const reference = focusedTrack ? tracks.find((track) => track.id === focusedTrack) : null;
  const referenceEntry = reference ? { track: reference, db: reference.spectrum[index] } : ranked[0];
  const comparisonEntry = reference
    ? tracks
        .filter((track) => track.id !== reference.id)
        .map((track) => ({ track, db: track.spectrum[index] }))
        .sort((a, b) => b.db - a.db)[0]
    : ranked[1];
  const delta = referenceEntry && comparisonEntry ? Math.abs(referenceEntry.db - comparisonEntry.db) : 0;
  const isConflict =
    referenceEntry &&
    comparisonEntry &&
    referenceEntry.db > Number(thresholdInput.value) &&
    comparisonEntry.db > Number(thresholdInput.value);

  return {
    index,
    freq,
    note: noteForFreq(freq),
    masterDb: master.spectrum[index],
    ranked,
    referenceEntry,
    comparisonEntry,
    delta,
    isConflict,
  };
}

function inspectAt(x) {
  const rawIndex = Math.max(0, Math.min(bins - 1, Math.round((x / width) * (bins - 1))));
  const stableIndex = Math.max(0, Math.min(bins - 1, Math.round(rawIndex / 3) * 3));
  return inspectAtIndex(stableIndex);
}

function renderPointInspector(data, locked = false) {
  if (!inspectState || !pointInspector) return;
  inspectState.textContent = locked ? "Locked" : frozen ? "Paused inspect" : "Live hover";
  pointInspector.innerHTML = `
    <div class="inspect-primary">
      <strong>${formatFreq(data.freq)} <span>${data.note}</span></strong>
      <span>${data.referenceEntry.track.name} vs ${data.comparisonEntry.track.name} · ${data.isConflict ? "Conflict" : "Clear"} · Δ ${data.delta.toFixed(1)} dB</span>
    </div>
    <div class="inspect-tracks">
      <div class="inspect-track is-reference" style="--track-color:${data.referenceEntry.track.color}">
        <span><i></i>Reference · ${data.referenceEntry.track.name}</span>
        <strong>${data.referenceEntry.db.toFixed(1)} dB</strong>
      </div>
      <div class="inspect-track is-compared" style="--track-color:${data.comparisonEntry.track.color}">
        <span><i></i>Compared · ${data.comparisonEntry.track.name}</span>
        <strong>${data.comparisonEntry.db.toFixed(1)} dB</strong>
      </div>
      ${data.ranked
        .filter((entry) => entry.track.id !== data.referenceEntry.track.id && entry.track.id !== data.comparisonEntry.track.id)
        .map(
          (entry) => `
            <div class="inspect-track" style="--track-color:${entry.track.color}">
              <span><i></i>${entry.track.name}</span>
              <strong>${entry.db.toFixed(1)} dB</strong>
            </div>
          `,
        )
        .join("")}
    </div>
  `;
}

function clearPointInspector() {
  if (lockedPointer || !inspectState || !pointInspector) return;
  inspectState.textContent = frozen ? "Paused" : "Live hover";
  pointInspector.innerHTML = `
    <div class="inspect-primary">
      <strong>${focusedTrack ? "Reference Compare" : "4 Track Compare"}</strong>
      <span>${focusedTrack ? "Hover to compare selected reference against the strongest other track." : "Click a lane to make it the reference, or hover the graph for loudest-vs-second delta."}</span>
    </div>
  `;
}

function renderConflicts(zones) {
  if (!conflictCount || !conflictList) return;
  conflictCount.textContent = `${zones.length} live`;
  if (!zones.length) {
    conflictList.innerHTML = `<div class="empty-state">No strong overlap in this moment.</div>`;
    return;
  }
  conflictList.innerHTML = zones
    .map((zone) => {
      const names = zone.active.map((entry) => entry.track.name).join(" + ");
      const firstTrack = zone.referenceId || zone.active[0].track.id;
      return `
        <button class="conflict-item" data-track="${firstTrack}">
          <div class="conflict-top">
            <span>${names}</span>
            <span class="conflict-range">${formatFreq(zone.from)}-${formatFreq(zone.to)}</span>
          </div>
          <div class="conflict-tracks">${zone.referenceId ? "Reference delta" : "Top pair delta"} ${zone.delta.toFixed(1)} dB · Overlap ${(zone.intensity * 100).toFixed(0)}%</div>
          <div class="conflict-bar" style="transform:scaleX(${zone.intensity})"></div>
        </button>
      `;
    })
    .join("");
}

function drawPointer() {
  const activePointer = lockedPointer || pointer;
  if (!activePointer) return;
  const data = inspectAt(activePointer.x);
  const x = (data.index / (bins - 1)) * width;
  const shouldRenderInspector =
    lockedPointer || data.index !== lastInspectIndex || performance.now() - lastInspectRender > 120;
  lastInspectIndex = data.index;

  ctx.strokeStyle = lockedPointer ? "rgba(255,221,154,0.58)" : "rgba(237,243,245,0.34)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(x, 0);
  ctx.lineTo(x, height);
  ctx.stroke();

  cursorReadout.classList.remove("is-hidden");
  cursorReadout.style.left = `${x}px`;
  cursorReadout.style.top = "58px";
  cursorReadout.innerHTML = `
    <strong>Δ ${data.delta.toFixed(1)} dB</strong>
    <span>${data.referenceEntry.track.name} vs ${data.comparisonEntry.track.name}</span>
    <span>${formatFreq(data.freq)} · ${data.note}${data.isConflict ? " · conflict" : ""}</span>
  `;

  if (shouldRenderInspector) {
    lastInspectRender = performance.now();
    renderPointInspector(data, Boolean(lockedPointer));
  }
}

function frame(now) {
  if (now - lastFrame < 32) {
    requestAnimationFrame(frame);
    return;
  }
  lastFrame = now;

  const time = now / 1000;
  if (!frozen) {
    if (audioMode) {
      updateAudioAnalysis();
    } else {
      for (const track of tracks) generateTrack(track, time);
      updateMaster();
    }
  }

  const conflicts = findConflicts();
  drawGrid();
  const selectedId = focusedTrack || hoveredTrack;
  const baseWidth = Number(waveWidthInput.value);
  const dimAlpha = Number(waveDimInput.value);

  for (const track of tracks) {
    const isSelected = selectedId === track.id;
    const isMuted = selectedId && !isSelected;
    drawCurve(
      track.spectrum,
      track.color,
      isMuted ? dimAlpha : isSelected ? 0.98 : 0.62,
      isSelected ? baseWidth + 1 : baseWidth,
      isSelected ? Number(waveFillInput.value) + 0.05 : Number(waveFillInput.value),
    );
  }

  drawConflicts(conflicts);

  if (selectedId) {
    const selected = tracks.find((track) => track.id === selectedId);
    if (selected) {
      getTrackPeaks(selected, 3).forEach((peak) => {
        drawTrackLabel(selected, (peak.index / (bins - 1)) * width + 8, dbToY(styledDb(peak.db)) - 22, `${selected.name} ${peak.db.toFixed(0)}`);
      });
    }
  }

  drawPointer();

  if (now - lastSidebarRender > 460) {
    lastSidebarRender = now;
    renderTracks();
    renderConflicts(conflicts);
    updateTimelineReadout();
  }

  requestAnimationFrame(frame);
}

function bindEvents() {
  trackList.addEventListener("click", (event) => {
    const card = event.target.closest(".track-card");
    if (!card) return;
    focusedTrack = focusedTrack === card.dataset.track ? null : card.dataset.track;
    clearPointInspector();
  });

  trackList.addEventListener("mouseover", (event) => {
    const card = event.target.closest(".track-card");
    if (!card || focusedTrack) return;
    hoveredTrack = card.dataset.track;
  });

  trackList.addEventListener("mouseleave", () => {
    hoveredTrack = null;
  });

  if (conflictList) {
    conflictList.addEventListener("click", (event) => {
      const item = event.target.closest(".conflict-item");
      if (!item) return;
      focusedTrack = item.dataset.track;
    });
  }

  resetFocus.addEventListener("click", () => {
    focusedTrack = null;
    hoveredTrack = null;
    lockedPointer = null;
    clearPointInspector();
  });

  canvas.addEventListener("mousemove", (event) => {
    const rect = canvas.getBoundingClientRect();
    pointer = { x: event.clientX - rect.left, y: event.clientY - rect.top };
  });

  canvas.addEventListener("click", (event) => {
    const rect = canvas.getBoundingClientRect();
    const nextPointer = { x: event.clientX - rect.left, y: event.clientY - rect.top };
    if (lockedPointer && Math.abs(lockedPointer.x - nextPointer.x) < 8) {
      lockedPointer = null;
      clearPointInspector();
      return;
    }
    lockedPointer = nextPointer;
  });

  canvas.addEventListener("mouseleave", () => {
    pointer = null;
    if (!lockedPointer) {
      cursorReadout.classList.add("is-hidden");
      clearPointInspector();
    }
  });

  document.getElementById("freezeButton").addEventListener("click", (event) => {
    frozen = !frozen;
    event.currentTarget.classList.toggle("is-active", frozen);
    event.currentTarget.textContent = frozen ? "Resume" : "Pause";
    if (inspectState) {
      inspectState.textContent = lockedPointer ? "Locked" : frozen ? "Paused" : "Live hover";
    }
  });

  document.getElementById("snapshotButton").addEventListener("click", (event) => {
    event.currentTarget.classList.add("is-active");
    setTimeout(() => event.currentTarget.classList.remove("is-active"), 420);
  });

  document.getElementById("heatmapButton").addEventListener("click", (event) => {
    heatmap = !heatmap;
    event.currentTarget.classList.toggle("is-active", heatmap);
  });

  resetVisuals.addEventListener("click", () => {
    waveAmpInput.value = defaultVisuals.amp;
    waveGlowInput.value = defaultVisuals.glow;
    waveFillInput.value = defaultVisuals.fill;
    waveWidthInput.value = defaultVisuals.width;
    waveDimInput.value = defaultVisuals.dim;
    waveHueInput.value = defaultVisuals.hue;
  });

  audioFilesInput.addEventListener("change", (event) => {
    loadAudioFiles(event.target.files).catch((error) => {
      audioStatus.textContent = "Could not load audio";
      console.error(error);
    });
  });

  playButton.addEventListener("click", playAudio);
  restartButton.addEventListener("click", restartAudio);

  timelineScrub.addEventListener("input", () => {
    if (!audioMode || !loadedDuration) return;
    isScrubbing = true;
    const seconds = (Number(timelineScrub.value) / 1000) * loadedDuration;
    scrubCurrent.textContent = formatTime(seconds);
    timeReadout.textContent = `${formatTime(seconds)} / ${formatTime(loadedDuration)}`;
    timelineStatus.textContent = `${Math.round((seconds / loadedDuration) * 100)}% through loaded audio`;
  });

  timelineScrub.addEventListener("change", () => {
    if (!audioMode || !loadedDuration) return;
    const seconds = (Number(timelineScrub.value) / 1000) * loadedDuration;
    isScrubbing = false;
    seekAudio(seconds);
  });

  window.addEventListener("resize", resizeCanvas);
}

resizeCanvas();
bindEvents();
renderTracks();
requestAnimationFrame(frame);

