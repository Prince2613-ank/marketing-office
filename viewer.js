'use strict';
// Dependency-free GLB 2 renderer for this Blender export. Loads marketing_office.glb, people.bin and tv_video.mp4 from this folder.
const canvas = document.querySelector('#view'),
  gl = canvas.getContext('webgl2', { antialias: true, alpha: false });
const $ = (s) => document.querySelector(s);
let draws = [],
  ready = false,
  center = [11.5, 1, -16.8],
  yaw = 0.1,
  pitch = 1.04,
  distance = 51,
  drag = null,
  lastVP,
  viewEye = [30, 30, 30];
if (new URLSearchParams(location.search).get('view') === 'display') {
  center = [11.3395, 1.2, -13.4783];
  yaw = 0.55;
  pitch = 0.72;
  distance = 8;
}
if (new URLSearchParams(location.search).get('view') === 'service') {
  center = [18.3, 1, -17.6];
  yaw = 0.45;
  pitch = 1.08;
  distance = 13;
}
if (new URLSearchParams(location.search).get('view') === 'workstations') {
  center = [19.8, 1, -25.5];
  yaw = 0.35;
  pitch = 0.85;
  distance = 10;
}
if (new URLSearchParams(location.search).get('view') === 'console') {
  center = [15.75, 1.2, -25];
  yaw = 1.15;
  pitch = 1.23;
  distance = 8.5;
}
const I = () => [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1];
function mul(a, b) {
  let o = new Array(16).fill(0);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) for (let k = 0; k < 4; k++) o[c * 4 + r] += a[k * 4 + r] * b[c * 4 + k];
  return o;
}
function transform(m, p) {
  let x = [p[0], p[1], p[2], p[3] ?? 1],
    o = [0, 0, 0, 0];
  for (let r = 0; r < 4; r++) for (let k = 0; k < 4; k++) o[r] += m[k * 4 + r] * x[k];
  return o;
}
const sub = (a, b) => a.map((x, i) => x - b[i]),
  cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]],
  norm = (a) => {
    let d = Math.hypot(...a) || 1;
    return a.map((x) => x / d);
  },
  dot = (a, b) => a.reduce((n, x, i) => n + x * b[i], 0);
function inverse(m) {
  let rows = Array.from({ length: 4 }, (_, r) => [...Array.from({ length: 4 }, (_, c) => m[c * 4 + r]), ...Array.from({ length: 4 }, (_, c) => +(c === r))]);
  for (let c = 0; c < 4; c++) {
    let k = c;
    for (let r = c + 1; r < 4; r++) if (Math.abs(rows[r][c]) > Math.abs(rows[k][c])) k = r;
    [rows[k], rows[c]] = [rows[c], rows[k]];
    let d = rows[c][c];
    if (Math.abs(d) < 1e-12) return I();
    rows[c] = rows[c].map((x) => x / d);
    for (let r = 0; r < 4; r++)
      if (r !== c) {
        let q = rows[r][c];
        rows[r] = rows[r].map((x, i) => x - q * rows[c][i]);
      }
  }
  return Array.from({ length: 16 }, (_, i) => rows[i % 4][4 + Math.floor(i / 4)]);
}
function nodeMatrix(n) {
  if (n.matrix) return n.matrix;
  let [x, y, z, w] = n.rotation || [0, 0, 0, 1],
    s = n.scale || [1, 1, 1],
    t = n.translation || [0, 0, 0];
  return [
    (1 - 2 * y * y - 2 * z * z) * s[0],
    (2 * x * y + 2 * z * w) * s[0],
    (2 * x * z - 2 * y * w) * s[0],
    0,
    (2 * x * y - 2 * z * w) * s[1],
    (1 - 2 * x * x - 2 * z * z) * s[1],
    (2 * y * z + 2 * x * w) * s[1],
    0,
    (2 * x * z + 2 * y * w) * s[2],
    (2 * y * z - 2 * x * w) * s[2],
    (1 - 2 * x * x - 2 * y * y) * s[2],
    0,
    ...t,
    1,
  ];
}
function shader(type, source) {
  let s = gl.createShader(type);
  gl.shaderSource(s, source);
  gl.compileShader(s);
  if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw Error(gl.getShaderInfoLog(s));
  return s;
}
let nightMode = new URLSearchParams(location.search).get('mode') === 'night',
  dynamicTimer;
const automaticDoors = new Map(),
  businessScreens = [];
let presentationImages = [];
let program,
  U = {},
  shadowProgram,
  shadowU = {},
  shadowFbo,
  shadowTexture,
  shadowVP,
  lastShadow = '',
  whiteTexture;
function look(eye, target) {
  let z = norm(sub(eye, target)),
    x = norm(cross([0, 1, 0], z)),
    y = cross(z, x);
  return [x[0], y[0], z[0], 0, x[1], y[1], z[1], 0, x[2], y[2], z[2], 0, -dot(x, eye), -dot(y, eye), -dot(z, eye), 1];
}
function ortho(l, r, b, t, n, f) {
  return [2 / (r - l), 0, 0, 0, 0, 2 / (t - b), 0, 0, 0, 0, -2 / (f - n), 0, -(r + l) / (r - l), -(t + b) / (t - b), -(f + n) / (f - n), 1];
}
function setup() {
  if (!gl) throw Error('WebGL 2 is unavailable. Enable hardware acceleration in your browser.');
  program = gl.createProgram();
  gl.attachShader(
    program,
    shader(
      gl.VERTEX_SHADER,
      `#version 300 es
 layout(location=0) in vec3 position;layout(location=1) in vec3 normal;layout(location=2) in vec2 uv;layout(location=3) in vec4 joints;layout(location=4) in vec4 weights;uniform mat4 vp;uniform mat4 model;uniform int skinMode;uniform highp sampler2D boneTex;uniform int boneRow;out vec3 P;out vec3 N;out vec2 UV;mat4 bone(float j){int x=int(j+.5)*3;vec4 a=texelFetch(boneTex,ivec2(x,boneRow),0),b=texelFetch(boneTex,ivec2(x+1,boneRow),0),c=texelFetch(boneTex,ivec2(x+2,boneRow),0);return mat4(a.x,b.x,c.x,0.,a.y,b.y,c.y,0.,a.z,b.z,c.z,0.,a.w,b.w,c.w,1.);}void main(){vec4 p=vec4(position,1.);vec3 n=normal;if(skinMode==1){mat4 s=bone(joints.x)*weights.x+bone(joints.y)*weights.y+bone(joints.z)*weights.z+bone(joints.w)*weights.w;p=s*p;n=mat3(s)*n;}p=model*p;n=mat3(model)*n;P=p.xyz;N=n;UV=uv;gl_Position=vp*p;}`,
    ),
  );
  gl.attachShader(
    program,
    shader(
      gl.FRAGMENT_SHADER,
      `#version 300 es
 precision highp float;in vec3 P;in vec3 N;in vec2 UV;uniform vec4 blobs[16];uniform vec4 color;uniform float cutoff;uniform float alphaTest;uniform bool highlight;uniform bool textured;uniform sampler2D baseMap;uniform sampler2D shadowMap;uniform mat4 shadowMatrix;uniform vec3 emission;uniform bool emissionMapped;uniform bool interior;uniform bool night;uniform bool clearGlass;uniform bool liveTV;uniform bool fixtureLight;uniform bool displayScreen;uniform bool floorSurface;uniform sampler2D reflectionMap;uniform vec2 viewportSize;uniform float roughness;uniform float metallic;uniform vec3 viewEye;out vec4 outColor;
 // Fixed light-space taps stay stable while the camera moves.
 float shadowAmount(vec3 n){
   vec4 q=shadowMatrix*vec4(P+n*.07,1.);vec3 c=q.xyz/q.w*.5+.5;
   if(c.x<0.||c.x>1.||c.y<0.||c.y>1.||c.z>1.)return 1.;
   float bias=max(.00018,.00065*(1.-dot(n,normalize(vec3(-21.,40.,25.)))));
   vec2 taps[9]=vec2[9](vec2(0.),vec2(.95,.30),vec2(-.85,-.42),vec2(-.32,.96),vec2(.36,-.92),vec2(1.15,-.88),vec2(-1.12,.80),vec2(.84,1.11),vec2(-.80,-1.14));
   float sum=0.;for(int i=0;i<9;i++){float d=texture(shadowMap,c.xy+taps[i]*1.25/2048.).r;sum+=c.z-bias<=d?1.:0.;}
   return sum/9.;
 }
 void main(){if(P.y>cutoff)discard;vec3 n=normalize(N);if(dot(n,viewEye-P)<0.)n=-n;vec4 texel=textured?texture(baseMap,UV):vec4(1.);if(liveTV){outColor=vec4(pow(max(texel.rgb,vec3(0.)),vec3(1./2.2)),1.);return;}if(color.a*texel.a<alphaTest)discard;vec3 albedo=color.rgb*texel.rgb;if(!night&&fixtureLight)albedo=vec3(1.,.95,.86);float shadow=shadowAmount(n);float direct=max(dot(n,normalize(vec3(-21.,40.,25.))),0.);float fill=max(dot(n,normalize(vec3(1.,.55,-.3))),0.);float nicheWash=step(18.6,P.x)*step(P.x,19.40)*smoothstep(-3.95,-3.70,P.z)*(1.-smoothstep(-2.70,-2.45,P.z))*smoothstep(.85,1.5,P.y)*(1.-smoothstep(3.0,3.15,P.y));float pool=0.;vec2 lamps[13]=vec2[13](vec2(4.35,-13.85),vec2(11.32,-13.31),vec2(17.3,-12.65),vec2(10.4,-7.45),vec2(15.95,-5.85),vec2(20.1,-19.45),vec2(16.6,-6.3),vec2(17.6,-22.5),vec2(20.6,-22.5),vec2(17.6,-26.5),vec2(20.6,-26.5),vec2(17.6,-30.2),vec2(20.6,-30.2));for(int i=0;i<13;i++){float d=length(P.xz-lamps[i]);pool+=1./(1.+d*d*.22);}vec3 light=night?(vec3(.14,.13,.115)+vec3(.38,.27,.155)*min(pool,1.4)+vec3(.10,.11,.13)*fill+vec3(.045,.05,.065)*direct*shadow):((interior?vec3(.47,.445,.405):vec3(.55,.55,.535))+vec3(.55,.49,.40)*direct*shadow+vec3(.12,.14,.17)*fill);float cz=step(-16.98,P.z)*step(P.z,-10.36)*step(18.6,P.x);float coffeeWash=cz*exp(-(3.8-P.y)/.55)*.55+step(18.85,P.x)*step(-14.77,P.z)*step(P.z,-12.53)*smoothstep(.95,1.1,P.y)*(1.-smoothstep(2.1,2.2,P.y))*.75+exp(-P.y/.16)*(1.-step(17.07,P.x))*step(16.7,P.x)*step(-15.30,P.z)*step(P.z,-12.0)*.8;coffeeWash*=step(P.x,19.40);light+=vec3(.70,.47,.22)*coffeeWash*(night?1.6:.8);float twz=step(21.07,P.x)*step(P.x,22.9)*step(-11.9,P.z)*step(P.z,-6.84)*step(P.y,3.74);light+=vec3(.62,.44,.24)*twz*(exp(-(3.74-P.y)/.8)*.6+.22)*(night?1.5:.75);float wsz=step(15.45,P.x)*step(P.x,22.95)*step(P.z,-17.35)*step(-34.9,P.z)*step(P.y,3.79);light+=vec3(.70,.47,.22)*wsz*(exp(-(3.8-P.y)/.55)*.55+.16)*(night?1.6:.8);float loungeDome=step(3.81,P.y)*(1.-smoothstep(1.75,2.25,length(P.xz-vec2(4.35,-13.85))));light+=vec3(.42,.29,.13)*loungeDome*(night?1.5:1.);light+=vec3(.70,.46,.20)*nicheWash*(.45+.55*smoothstep(1.2,3.0,P.y))*(night?1.9:1.0);if(night){float tvz=-P.z-13.85;float onTV=step(1.15,P.x)*exp(-pow((P.x-1.25)/.32,2.))*step(11.1,-P.z)*step(-P.z,16.97);float cove=exp(-(3.8-P.y)/.85);float pil=exp(-pow((abs(tvz)-1.57)/.30,2.))*smoothstep(.0,.6,P.y);float under=exp(-pow((P.y-.42)/.28,2.))*step(abs(tvz),1.85);light+=vec3(.78,.50,.24)*onTV*(cove*1.15+pil*1.0+under*.7);float rw=step(P.x,12.25)*exp(-pow((P.x-12.2)/.3,2.))*step(4.75,-P.z)*step(-P.z,8.66);light+=vec3(.5,.36,.2)*rw*(.45+.35*exp(-(3.8-P.y)/1.2));float bw=step(P.x,19.40)*exp(-pow((P.x-19.30)/.3,2.))*exp(-pow((-P.z-12.65)/1.3,2.))*exp(-pow((P.y-2.)/.9,2.));float bc=exp(-pow((P.x-17.3)/.9,2.))*exp(-pow((-P.z-12.65)/1.6,2.))*exp(-pow((P.y-1.05)/.5,2.));light+=vec3(.55,.38,.2)*(bw*.7+bc*.45);float sw=step(P.x,19.40)*exp(-pow((P.x-19.22)/.3,2.))*(exp(-pow((-P.z-3.65)/.45,2.))+exp(-pow((-P.z-7.95)/.45,2.)))*exp(-pow((P.y-1.78)/.7,2.));light+=vec3(.6,.42,.22)*sw*.8;float lr=length(vec2(P.x-4.35,-P.z-13.85));light+=vec3(.30,.22,.13)*smoothstep(3.0,2.7,lr)*smoothstep(3.75,3.9,P.y);}// Material-aware analytic reflection: stable, inexpensive and view dependent.
 vec3 v=normalize(viewEye-P),l=normalize(vec3(-21.,40.,25.)),h=normalize(v+l);
 float nv=max(dot(n,v),.001),nl=max(dot(n,l),0.),nh=max(dot(n,h),0.);
 float r=clamp(roughness,.16,1.),a=r*r,a2=a*a;
 float denom=nh*nh*(a2-1.)+1.;float D=a2/(3.14159265*denom*denom+.0001);
 float k=(r+1.)*(r+1.)/8.;float G=(nv/(nv*(1.-k)+k))*(nl/(nl*(1.-k)+k));
 vec3 f0=mix(vec3(.04),albedo,metallic),F=f0+(1.-f0)*pow(1.-max(dot(v,h),0.),5.);
 vec3 spec=min(vec3(.9),D*G*F/max(4.*nv*max(nl,.001),.001))*nl*shadow*(night?.22:.70);
 vec3 reflected=reflect(-v,n);float sky=smoothstep(-.15,.85,reflected.y);
 vec3 environment=mix(vec3(.13,.115,.09),night?vec3(.34,.27,.18):vec3(.59,.63,.65),sky);
 vec3 grazing=f0+(1.-f0)*pow(1.-nv,5.);
 vec3 reflection=environment*grazing*(1.-r*.72)*(night?.34:.48);
 float hemisphere=mix(.80,1.,clamp(n.y*.5+.5,0.,1.));
 float blobAO=1.;for(int i=0;i<16;i++){vec4 b=blobs[i];if(b.w<=0.)continue;vec2 dd=P.xz-b.xy;blobAO*=1.-b.w*exp(-dot(dd,dd)/(b.z*b.z));}light*=mix(1.,blobAO,1.-smoothstep(.015,.09,P.y));
 vec3 c=albedo*light*hemisphere*(1.-metallic*.72)+spec+reflection+emission*(night?1.25:(displayScreen?.42:(fixtureLight?1.15:0.)))*(emissionMapped?texel.rgb:vec3(1.));if(clearGlass)c=mix(vec3(.58,.67,.69),environment,.28)+grazing*.12;if(floorSurface&&n.y>.7){vec2 uv=gl_FragCoord.xy/viewportSize;vec2 d=vec2(1.5)/viewportSize;vec3 reflectedColor=(texture(reflectionMap,uv+d).rgb+texture(reflectionMap,uv-d).rgb+texture(reflectionMap,uv+vec2(d.x,-d.y)).rgb+texture(reflectionMap,uv+vec2(-d.x,d.y)).rgb)*.25;vec3 reflectedLinear=-log(max(vec3(.001),vec3(1.)-pow(reflectedColor,vec3(2.2))))/(night?1.5:1.38);c=mix(c,reflectedLinear,.30+.34*pow(1.-nv,5.));}if(highlight)c=mix(c,vec3(.3,1.,.82),.5);c=vec3(1.)-exp(-c*(night?1.5:1.38));float opacity=color.a*texel.a;if(clearGlass)opacity*=1.+.8*pow(1.-nv,4.);outColor=vec4(pow(c,vec3(1./2.2)),opacity);}`,
    ),
  );
  gl.linkProgram(program);
  if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw Error(gl.getProgramInfoLog(program));
  gl.useProgram(program);
  for (let n of [
    'vp',
    'color',
    'cutoff',
    'alphaTest',
    'highlight',
    'textured',
    'baseMap',
    'shadowMap',
    'shadowMatrix',
    'emission',
    'emissionMapped',
    'interior',
    'night',
    'clearGlass',
    'liveTV',
    'fixtureLight',
    'displayScreen',
    'roughness',
    'metallic',
    'viewEye',
    'floorSurface',
    'reflectionMap',
    'viewportSize',
    'model',
    'skinMode',
    'boneTex',
    'boneRow',
    'blobs',
  ])
    U[n] = gl.getUniformLocation(program, n);
  gl.uniform1i(U.baseMap, 0);
  gl.uniform1i(U.shadowMap, 1);
  gl.uniformMatrix4fv(U.model, false, new Float32Array(I()));
  gl.uniform1i(U.skinMode, 0);
  gl.uniform1i(U.boneTex, 4);
  whiteTexture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, whiteTexture);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array([255, 255, 255, 255]));
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  shadowProgram = gl.createProgram();
  gl.attachShader(
    shadowProgram,
    shader(
      gl.VERTEX_SHADER,
      `#version 300 es
 layout(location=0) in vec3 position;uniform mat4 vp;out float height;void main(){height=position.y;gl_Position=vp*vec4(position,1.);}`,
    ),
  );
  gl.attachShader(
    shadowProgram,
    shader(
      gl.FRAGMENT_SHADER,
      `#version 300 es
 precision highp float;in float height;uniform float cutoff;void main(){if(height>cutoff)discard;}`,
    ),
  );
  gl.linkProgram(shadowProgram);
  for (let n of ['vp', 'cutoff']) shadowU[n] = gl.getUniformLocation(shadowProgram, n);
  shadowTexture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, shadowTexture);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT24, 2048, 2048, 0, gl.DEPTH_COMPONENT, gl.UNSIGNED_INT, null);
  for (let n of [gl.TEXTURE_MIN_FILTER, gl.TEXTURE_MAG_FILTER]) gl.texParameteri(gl.TEXTURE_2D, n, gl.NEAREST);
  for (let n of [gl.TEXTURE_WRAP_S, gl.TEXTURE_WRAP_T]) gl.texParameteri(gl.TEXTURE_2D, n, gl.CLAMP_TO_EDGE);
  shadowFbo = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, shadowFbo);
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, shadowTexture, 0);
  gl.drawBuffers([gl.NONE]);
  gl.readBuffer(gl.NONE);
  if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) throw Error('Shadow framebuffer unavailable');
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  shadowVP = mul(ortho(-27, 27, -27, 27, 0.1, 110), look([-10, 40, 8], [11, 0, -17]));
  gl.enable(gl.DEPTH_TEST);
  gl.enable(gl.BLEND);
  gl.depthFunc(gl.LEQUAL);
  gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
}
async function load() {
  const statusEl = $('#status');
  statusEl.textContent = 'Downloading office model...';
  const response = await fetch('marketing_office.glb');
  if (!response.ok) throw Error('GLB failed to load: ' + response.status);
  let buf;
  const headerLen = response.headers.get('content-length');
  const expectedTotal = headerLen ? parseInt(headerLen, 10) : 57611152;
  if (response.body) {
    let loaded = 0;
    const reader = response.body.getReader();
    const chunks = [];
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      chunks.push(value);
      loaded += value.length;
      const pct = Math.min(99, Math.round((loaded / expectedTotal) * 100));
      const mb = (loaded / (1024 * 1024)).toFixed(1);
      const totalMb = (expectedTotal / (1024 * 1024)).toFixed(1);
      statusEl.textContent = `Downloading office model... ${pct}% (${mb} MB / ${totalMb} MB)`;
    }
    const all = new Uint8Array(loaded);
    let pos = 0;
    for (const c of chunks) {
      all.set(c, pos);
      pos += c.length;
    }
    buf = all.buffer;
  } else {
    buf = await response.arrayBuffer();
  }
  statusEl.textContent = 'Loading scene...';

  let dv = new DataView(buf);
  if (dv.getUint32(0, true) !== 0x46546c67) throw Error('Invalid GLB');
  let json, bin;
  for (let off = 12; off < buf.byteLength;) {
    let len = dv.getUint32(off, true),
      type = dv.getUint32(off + 4, true);
    if (type === 0x4e4f534a) json = JSON.parse(new TextDecoder().decode(new Uint8Array(buf, off + 8, len)));
    if (type === 0x004e4942) bin = new DataView(buf, off + 8, len);
    off += 8 + len;
  }
  const textures = [];
  const retainedImages = new Map();
  for (let info of json.textures || []) {
    let im = json.images[info.source],
      view = json.bufferViews[im.bufferView],
      bytes = new Uint8Array(binaryBuffer(bin), view.byteOffset || 0, view.byteLength);
    let bitmap = await createImageBitmap(new Blob([bytes], { type: im.mimeType }));
    let texture = gl.createTexture();
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, texture);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.SRGB8_ALPHA8, gl.RGBA, gl.UNSIGNED_BYTE, bitmap);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
    gl.generateMipmap(gl.TEXTURE_2D);
    textures.push(texture);
    const sourceName = json.materials
      .filter((m) => m.pbrMetallicRoughness?.baseColorTexture?.index === textures.length - 1)
      .map((m) => m.name)
      .join(' ');
    if (/project visualisation print/.test(sourceName)) retainedImages.set(sourceName, bitmap);
    else bitmap.close();
  }
  function binaryBuffer(view) {
    return view.buffer.slice(view.byteOffset, view.byteOffset + view.byteLength);
  }
  function read(id) {
    let a = json.accessors[id],
      v = json.bufferViews[a.bufferView],
      n = { SCALAR: 1, VEC2: 2, VEC3: 3, VEC4: 4 }[a.type],
      bytes = { 5120: 1, 5121: 1, 5122: 2, 5123: 2, 5125: 4, 5126: 4 }[a.componentType],
      stride = v.byteStride || n * bytes,
      start = (v.byteOffset || 0) + (a.byteOffset || 0),
      out = [];
    for (let i = 0; i < a.count; i++)
      for (let j = 0; j < n; j++) {
        let off = start + i * stride + j * bytes;
        let val =
          a.componentType === 5126
            ? bin.getFloat32(off, true)
            : a.componentType === 5125
              ? bin.getUint32(off, true)
              : a.componentType === 5123
                ? bin.getUint16(off, true)
                : a.componentType === 5122
                  ? bin.getInt16(off, true)
                  : a.componentType === 5120
                    ? bin.getInt8(off)
                    : bin.getUint8(off);
        if (a.q) val = a.q[j] + ((val + 32767) / 65534) * (a.q[n + j] - a.q[j]);
        else if (a.nq) val /= 127;
        out.push(val);
      }
    return out;
  }
  function visit(id, parent) {
    let n = json.nodes[id],
      world = mul(parent, nodeMatrix(n));
    if (n.mesh !== undefined)
      for (let p of json.meshes[n.mesh].primitives) {
        if (p.mode !== undefined && p.mode !== 4) continue;
        let pos = read(p.attributes.POSITION),
          normals = p.attributes.NORMAL !== undefined ? read(p.attributes.NORMAL) : null,
          uv = p.attributes.TEXCOORD_0 !== undefined ? read(p.attributes.TEXCOORD_0) : null,
          invWorld = inverse(world),
          idx = p.indices !== undefined ? read(p.indices) : Array.from({ length: pos.length / 3 }, (_, i) => i),
          data = [],
          min = [Infinity, Infinity, Infinity],
          max = [-Infinity, -Infinity, -Infinity];
        for (let i = 0; i < idx.length; i += 3) {
          let tri = idx.slice(i, i + 3).map((v) => transform(world, pos.slice(v * 3, v * 3 + 3)).slice(0, 3)),
            normal = norm(cross(sub(tri[1], tri[0]), sub(tri[2], tri[0])));
          for (let ti = 0; ti < tri.length; ti++) {
            let v = tri[ti],
              index = idx[i + ti];
            for (let a = 0; a < 3; a++) {
              min[a] = Math.min(min[a], v[a]);
              max[a] = Math.max(max[a], v[a]);
            }
            let nn = normal;
            if (normals) {
              let nx = normals[index * 3],
                ny = normals[index * 3 + 1],
                nz = normals[index * 3 + 2];
              nn = norm([invWorld[0] * nx + invWorld[1] * ny + invWorld[2] * nz, invWorld[4] * nx + invWorld[5] * ny + invWorld[6] * nz, invWorld[8] * nx + invWorld[9] * ny + invWorld[10] * nz]);
            }
            data.push(...v, ...nn, ...(uv ? uv.slice(index * 2, index * 2 + 2) : [0, 0]));
          }
        }
        let material = json.materials?.[p.material],
          color = [...(material?.pbrMetallicRoughness?.baseColorFactor || [1, 1, 1, 1])];
        if (material?.name === 'Low iron clear glass') {
          color = [0.91, 0.97, 0.97, 0.035];
        }
        draws.push({
          floor: /^Office floor/.test(n.name || ''),
          roughness: material?.pbrMetallicRoughness?.roughnessFactor ?? 1,
          metallic: material?.pbrMetallicRoughness?.metallicFactor ?? 1,
          emissionMapped:
            material?.emissiveTexture !== undefined &&
            material?.pbrMetallicRoughness?.baseColorTexture !== undefined &&
            json.textures[material.emissiveTexture.index].source === json.textures[material.pbrMetallicRoughness.baseColorTexture.index].source,
          alphaTest: material?.alphaMode === 'MASK' ? (material.alphaCutoff ?? 0.5) : 0,
          name: n.name || 'Object',
          screenLight: /(?:active (?:screen|display)|project presentation)/i.test(n.name || ''),
          data,
          count: data.length / 8,
          texture: textures[material?.pbrMetallicRoughness?.baseColorTexture?.index],
          emission: (material?.emissiveFactor || [0, 0, 0]).map((x) => x * (material?.extensions?.KHR_materials_emissive_strength?.emissiveStrength || 1)),
          cuttable: ['Structure', 'Partitions'].includes(n.extras?.category) && !/^Structural column|^Charcoal column/.test(n.name),
          color,
          min,
          max,
          extras: n.extras || {},
          nightOnly: !!n.extras?.night_only,
          ceiling: /^Ceiling/.test(n.name) || !!n.extras?.eye_ceiling_fixture,
          glass: color[3] < 0.99,
          architectural: ['Structure', 'Partitions', 'Glazing', 'Doors'].includes(n.extras?.category),
          door: /^(D[123]|GD[12]|GL[123]|V1)-/.test(n.name),
        });
      }
    for (let ch of n.children || []) visit(ch, world);
  }
  for (let n of json.scenes[json.scene || 0].nodes) visit(n, I());
  if (window.PEOPLE) draws = PEOPLE.prepare(draws);
  const sourceParts = draws.length,
    groups = new Map();
  for (const d of draws) {
    if (d.extras.auto_door_id) {
      const id = d.extras.auto_door_id;
      let rig = automaticDoors.get(id);
      if (!rig) {
        rig = { id, hinge: d.extras.auto_door_hinge, center: d.extras.auto_door_center, angle: d.extras.auto_door_angle, amount: 0, target: 0, lastNear: -Infinity, parts: [], segments: [] };
        automaticDoors.set(id, rig);
      }
      rig.parts.push(d);
      d.rig = rig;
      d.original = new Float32Array(d.data);
      const begin = collisionSegments.length;
      captureCollision(d);
      rig.segments.push(...collisionSegments.splice(begin));
    } else captureCollision(d);
  }
  presentationImages = [...retainedImages.values()];
  for (const d of draws) {
    d.depthBias = 0; // Physical depth only: slope offsets can project columns across mounted TVs.
    const key = JSON.stringify([
      d.ceiling,
      d.nightOnly,
      d.screenLight,
      !!d.extras.capital_crest_display,
      d.glass || d.rig || d.extras.business_screen !== undefined ? d.name : null,
      d.depthBias,
      d.floor,
      d.color,
      d.roughness,
      d.metallic,
      d.emission,
      d.emissionMapped,
      d.alphaTest,
      d.texture ? textures.indexOf(d.texture) : -1,
      d.glass,
    ]);
    let g = groups.get(key);
    if (!g) {
      g = { ...d, chunks: [], count: 0 };
      groups.set(key, g);
    }
    g.chunks.push(d.data);
    g.count += d.count;
    for (let i = 0; i < 3; i++) {
      g.min[i] = Math.min(g.min[i], d.min[i]);
      g.max[i] = Math.max(g.max[i], d.max[i]);
    }
  }
  draws = [...groups.values()];
  for (const d of draws) {
    const packed = new Float32Array(d.count * 8);
    let offset = 0;
    for (const chunk of d.chunks) {
      packed.set(chunk, offset);
      offset += chunk.length;
    }
    delete d.chunks;
    delete d.data;
    d.vao = gl.createVertexArray();
    gl.bindVertexArray(d.vao);
    const buffer = gl.createBuffer();
    d.buffer = buffer;
    gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
    gl.bufferData(gl.ARRAY_BUFFER, packed, d.rig ? gl.DYNAMIC_DRAW : gl.STATIC_DRAW);
    for (const [a, size, offset] of [
      [0, 3, 0],
      [1, 3, 12],
      [2, 2, 24],
    ]) {
      gl.enableVertexAttribArray(a);
      gl.vertexAttribPointer(a, size, gl.FLOAT, false, 32, offset);
    }
  }
  for (const d of draws) {
    if (d.rig) {
      const rig = d.rig;
      rig.parts = rig.parts.filter((p) => p.name !== d.name);
      rig.parts.push(d);
    }
    if (d.extras.business_screen !== undefined) createBusinessScreen(d);
  }
  if (window.PEOPLE) await PEOPLE.init();
  ready = true;
  window.officeViewer = {
    ready: true,
    objects: sourceParts,
    drawCalls: draws.length,
    textures: textures.length,
    triangles: draws.reduce((n, d) => n + d.count / 3, 0),
    bounds: draws.reduce(
      (b, d) => [b[0].map((x, i) => Math.min(x, d.min[i])), b[1].map((x, i) => Math.max(x, d.max[i]))],
      [
        [Infinity, Infinity, Infinity],
        [-Infinity, -Infinity, -Infinity],
      ],
    ),
  };
  $('#status').textContent = eyeMode ? 'Eye level · ' + eyeStations[Number($('#viewpoint').value) || 0].name : '';
  requestAnimationFrame(render);
}
function visible(d) {
  return (!d.ceiling || eyeMode) && (!d.nightOnly || nightMode);
}
// Orthographic zoom changes framing only. Keep the eye outside the complete
// scene and derive depth planes from all eight world-bound corners on every view.
function cameraProjection(bounds, focus, azimuth, elevation, zoom, width, height) {
  const midpoint = bounds[0].map((v, i) => (v + bounds[1][i]) / 2);
  const radius = Math.hypot(...sub(bounds[1], bounds[0])) / 2;
  const eyeDistance = radius + Math.hypot(...sub(focus, midpoint)) + 10;
  const cp = Math.cos(elevation),
    eye = [focus[0] + eyeDistance * cp * Math.sin(azimuth), focus[1] + eyeDistance * Math.sin(elevation), focus[2] + eyeDistance * cp * Math.cos(azimuth)];
  const view = look(eye, focus);
  let minDepth = Infinity,
    maxDepth = -Infinity;
  for (let i = 0; i < 8; i++) {
    const corner = [bounds[(i >> 0) & 1][0], bounds[(i >> 1) & 1][1], bounds[(i >> 2) & 1][2]];
    const depth = -transform(view, corner)[2];
    minDepth = Math.min(minDepth, depth);
    maxDepth = Math.max(maxDepth, depth);
  }
  const near = Math.max(0.05, minDepth - 2),
    far = Math.max(near + 1, maxDepth + 2);
  const aspect = Math.max(1, width) / Math.max(1, height),
    extent = zoom * 0.35 * Math.max(1, 0.8 / aspect);
  return { matrix: mul(ortho(-extent * aspect, extent * aspect, -extent, extent, near, far), view), near, far, eyeDistance, minDepth, maxDepth, eye };
}
function viewProjection() {
  if (eyeMode) {
    viewEye = walkPosition;
    return eyeProjection(canvas.width, canvas.height);
  }
  const result = cameraProjection(window.officeViewer.bounds, center, yaw, pitch, distance, canvas.width, canvas.height);
  window.officeViewer.camera = { near: result.near, far: result.far, minDepth: result.minDepth, maxDepth: result.maxDepth, zoom: distance };
  viewEye = result.eye;
  return result.matrix;
}
function cutoff(d) {
  return 99;
}
let framePending = false;
function invalidate() {
  if (!framePending && ready) {
    framePending = true;
    requestAnimationFrame(render);
  }
}
function render(now = performance.now()) {
  framePending = false;
  if (window.PEOPLE && PEOPLE.ready && PEOPLE.playing && !document.hidden) invalidate();
  const dt = Math.min(0.05, (now - lastWalkTime) / 1000 || 0.016);
  lastWalkTime = now;
  updateAutomaticDoors(now, dt);
  updateBusinessScreens(now);
  if (eyeMode && moveKeys.size) {
    let forward = (moveKeys.has('KeyW') || moveKeys.has('ArrowUp') ? 1 : 0) - (moveKeys.has('KeyS') || moveKeys.has('ArrowDown') ? 1 : 0),
      side = (moveKeys.has('KeyD') ? 1 : 0) - (moveKeys.has('KeyA') ? 1 : 0);
    const n = Math.hypot(forward, side) || 1,
      speed = walkFast ? 2.6 : 1.5;
    moveEye((forward / n) * speed * dt, (side / n) * speed * dt);
  }
  let ratio = Math.min(devicePixelRatio, 1.5),
    w = Math.round(canvas.clientWidth * ratio),
    h = Math.round(canvas.clientHeight * ratio);
  if (canvas.width !== w || canvas.height !== h) {
    canvas.width = w;
    canvas.height = h;
  }
  let signature = (eyeMode ? 'eye' : 'overview') + (nightMode ? '-night' : '-day');
  if (signature !== lastShadow) {
    lastShadow = signature;
    gl.bindFramebuffer(gl.FRAMEBUFFER, shadowFbo);
    gl.viewport(0, 0, 2048, 2048);
    gl.depthMask(true);
    gl.clear(gl.DEPTH_BUFFER_BIT);
    gl.enable(gl.POLYGON_OFFSET_FILL);
    gl.polygonOffset(2, 4);
    gl.useProgram(shadowProgram);
    gl.uniformMatrix4fv(shadowU.vp, false, new Float32Array(shadowVP));
    for (let d of draws) {
      if (d.glass || d.name === 'Reception concierge' || (d.nightOnly && !nightMode)) continue;
      gl.bindVertexArray(d.vao);
      gl.uniform1f(shadowU.cutoff, cutoff(d));
      gl.drawArrays(gl.TRIANGLES, 0, d.count);
    }
    gl.disable(gl.POLYGON_OFFSET_FILL);
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  }
  gl.useProgram(program);
  gl.uniform1i(U.interior, eyeMode);
  gl.uniform1i(U.night, nightMode);
  gl.viewport(0, 0, w, h);
  if (eyeMode) {
    if (nightMode) gl.clearColor(0.035, 0.045, 0.075, 1);
    else gl.clearColor(0.68, 0.77, 0.83, 1);
  } else gl.clearColor(0.095, 0.12, 0.15, 1);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  lastVP = viewProjection();
  gl.uniformMatrix4fv(U.shadowMatrix, false, new Float32Array(shadowVP));
  gl.activeTexture(gl.TEXTURE1);
  gl.bindTexture(gl.TEXTURE_2D, shadowTexture);
  {
    const rk = lastVP.map((v) => v.toFixed(5)).join(',') + w + 'x' + h + (nightMode ? 'n' : 'd') + [...automaticDoors.values()].map((r) => r.amount.toFixed(3)).join('');
    if (rk !== window.__reflKey) {
      window.__reflKey = rk;
      renderFloorReflection(w, h, lastVP);
    }
  }
  gl.uniform2f(U.viewportSize, w, h);
  gl.uniform1i(U.reflectionMap, 2);
  gl.activeTexture(gl.TEXTURE2);
  gl.bindTexture(gl.TEXTURE_2D, floorReflection.texture);
  gl.uniform3fv(U.viewEye, viewEye);
  gl.uniformMatrix4fv(U.vp, false, new Float32Array(lastVP));
  gl.uniformMatrix4fv(U.shadowMatrix, false, new Float32Array(shadowVP));
  gl.activeTexture(gl.TEXTURE1);
  gl.bindTexture(gl.TEXTURE_2D, shadowTexture);
  if (window.PEOPLE) PEOPLE.update(now);
  const ordered = draws
    .filter((d) => !d.glass)
    .concat(
      draws
        .filter((d) => d.glass)
        .sort((a, b) => {
          const pa = transform(
              lastVP,
              a.min.map((v, i) => (v + a.max[i]) / 2),
            ),
            pb = transform(
              lastVP,
              b.min.map((v, i) => (v + b.max[i]) / 2),
            );
          return pb[2] - pa[2];
        }),
    );
  for (let transparent of [false, true]) {
    gl.depthMask(!transparent);
    if (transparent && window.PEOPLE) {
      PEOPLE.draw();
      gl.depthMask(false);
    }
    for (let d of ordered) {
      if (d.glass !== transparent || !visible(d)) continue;
      gl.bindVertexArray(d.vao);
      if (d.depthBias) {
        gl.enable(gl.POLYGON_OFFSET_FILL);
        gl.polygonOffset(-1, d.depthBias);
      } else gl.disable(gl.POLYGON_OFFSET_FILL);
      gl.uniform1i(U.floorSurface, !!d.floor);
      gl.uniform1f(U.roughness, d.roughness);
      gl.uniform1f(U.metallic, d.metallic);
      gl.uniform1i(U.clearGlass, d.glass);
      gl.uniform4fv(U.color, d.color);
      gl.uniform3fv(U.emission, d.emission);
      gl.uniform1i(U.emissionMapped, !!d.emissionMapped);
      gl.uniform1i(U.liveTV, d.extras.business_screen !== undefined);
      gl.uniform1i(U.displayScreen, !!d.screenLight);
      gl.uniform1i(U.fixtureLight, !d.screenLight && !d.extras.capital_crest_display && d.emission.some((v) => v > 0));
      gl.uniform1f(U.cutoff, cutoff(d));
      gl.uniform1f(U.alphaTest, d.alphaTest);
      gl.uniform1i(U.highlight, false);
      gl.uniform1i(U.textured, !!d.texture);
      gl.activeTexture(gl.TEXTURE0);
      gl.bindTexture(gl.TEXTURE_2D, d.texture || whiteTexture);
      gl.drawArrays(gl.TRIANGLES, 0, d.count);
    }
  }
  gl.disable(gl.POLYGON_OFFSET_FILL);
  gl.depthMask(true);
  if (eyeMode && (moveKeys.size || [...automaticDoors.values()].some((r) => Math.abs(r.amount - r.target) > 0.001))) invalidate();
  else if (businessScreens.length && !document.hidden && !(tvFilm && tvFilm.requestVideoFrameCallback)) {
    clearTimeout(dynamicTimer);
    dynamicTimer = setTimeout(invalidate, 33);
  }
}
// Public-area visitor stations. Heights are in metres, glTF Y-up.
let eyeMode = false,
  walkYaw = 0,
  walkPitch = 0,
  walkPosition = [8.4, 1.6, -9.5],
  walkFast = false,
  lastWalkTime = 0;
const moveKeys = new Set(),
  collisionSegments = [],
  collisionHulls = [];
const eyeStations = [
  { name: 'Reception', position: [7.38, 1.59, -7.07], target: [12.1, 1.86, -6.84] },
  { name: 'Project model', position: [8.8, 1.6, -12], target: [11.34, 1.45, -13.4783] },
  { name: 'Lounge', position: [8.35, 1.6, -13.1], target: [3.8, 1.8, -16.8] },
  { name: 'Meeting', position: [13.15, 1.6, -4.95], target: [18.2, 1.1, -6.6] },
  { name: 'Meeting doorway', position: [12.817, 1.6, -9.9], target: [12.817, 1.6, -8.1] },
  { name: 'Workstations', position: [20, 1.6, -23.85], target: [20, 1.4, -26.8] },
  { name: 'Storage', position: [19.2, 1.6, -31.95], target: [19.2, 1.4, -33.3] },
  { name: 'PDF · Multimedia lounge', position: [8.9, 1.72, -13.85], target: [1.2, 1.45, -13.85] },
  { name: 'PDF · Scale model', position: [7.6, 2.6, -9.6], target: [11.3, 0.5, -13.3] },
  { name: 'PDF · Coffee bar', position: [13.2, 1.6, -13.65], target: [19.4, 1.5, -13.65] },
  { name: 'PDF · Reception', position: [7.65, 1.59, -7.75], target: [12.1, 1.79, -6.83] },
  { name: 'PDF · Meeting room', position: [12.62, 1.55, -7.45], target: [19.4, 1.2, -5.7] },
  { name: 'Toilet', position: [21.35, 1.6, -11.6], target: [22.9, 1.15, -10.3] },
];
const walkOutline = [
  [715, 54],
  [951, 54],
  [951, 1127],
  [831, 1092],
  [615, 999],
  [301, 824],
  [244, 789],
  [244, 596],
  [715, 596],
].map(([x, y]) => [((x - 244) * 7.69) / 236, (-(1127 - y) * 7.69) / 236]);
function pointInPolygon(p, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const a = poly[i],
      b = poly[j];
    if (a[1] > p[1] !== b[1] > p[1] && p[0] < ((b[0] - a[0]) * (p[1] - a[1])) / (b[1] - a[1]) + a[0]) inside = !inside;
  }
  return inside;
}
function segmentDistance(p, a, b) {
  const dx = b[0] - a[0],
    dy = b[1] - a[1],
    l = dx * dx + dy * dy,
    t = l ? Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / l)) : 0;
  return Math.hypot(p[0] - a[0] - t * dx, p[1] - a[1] - t * dy);
}
function convexHull(points) {
  points.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  const cross2 = (a, b, c) => (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]);
  const lower = [],
    upper = [];
  for (const p of points) {
    while (lower.length > 1 && cross2(lower.at(-2), lower.at(-1), p) <= 0) lower.pop();
    lower.push(p);
  }
  for (let i = points.length - 1; i >= 0; i--) {
    const p = points[i];
    while (upper.length > 1 && cross2(upper.at(-2), upper.at(-1), p) <= 0) upper.pop();
    upper.push(p);
  }
  lower.pop();
  upper.pop();
  return lower.concat(upper);
}
function captureCollision(d) {
  if (d.ceiling || d.max[1] < 0.25 || d.min[1] > 1.45 || d.extras.capital_crest_display || d.extras.gallery_decor || d.extras.console_luxury_decor) return;
  if (d.architectural) {
    for (let i = 0; i < d.data.length; i += 24) {
      const tri = [d.data.slice(i, i + 3), d.data.slice(i + 8, i + 11), d.data.slice(i + 16, i + 19)],
        points = [];
      for (let j = 0; j < 3; j++) {
        const a = tri[j],
          b = tri[(j + 1) % 3];
        if ((a[1] <= 1 && b[1] > 1) || (b[1] <= 1 && a[1] > 1)) {
          const t = (1 - a[1]) / (b[1] - a[1]);
          points.push([a[0] + t * (b[0] - a[0]), a[2] + t * (b[2] - a[2])]);
        }
      }
      if (points.length === 2 && Math.hypot(points[0][0] - points[1][0], points[0][1] - points[1][1]) > 0.00001) collisionSegments.push(points);
    }
  } else {
    const points = [];
    for (let i = 0; i < d.data.length; i += 8) points.push([d.data[i], d.data[i + 2]]);
    const hull = convexHull(points);
    let area = 0;
    for (let i = 0, j = hull.length - 1; i < hull.length; j = i++) area += (hull[j][0] + hull[i][0]) * (hull[j][1] - hull[i][1]);
    area = Math.abs(area) / 2;
    if (area > 1.0) {
      for (const yc of [0.35, 0.85]) {
        for (let i = 0; i < d.data.length; i += 24) {
          const tri = [d.data.slice(i, i + 3), d.data.slice(i + 8, i + 11), d.data.slice(i + 16, i + 19)],
            q = [];
          for (let j = 0; j < 3; j++) {
            const a = tri[j],
              b = tri[(j + 1) % 3];
            if ((a[1] <= yc && b[1] > yc) || (b[1] <= yc && a[1] > yc)) {
              const t = (yc - a[1]) / (b[1] - a[1]);
              q.push([a[0] + t * (b[0] - a[0]), a[2] + t * (b[2] - a[2])]);
            }
          }
          if (q.length === 2 && Math.hypot(q[0][0] - q[1][0], q[0][1] - q[1][1]) > 0.00001) collisionSegments.push(q);
        }
      }
    } else if (hull.length > 2) collisionHulls.push({ hull, min: [d.min[0], d.min[2]], max: [d.max[0], d.max[2]] });
  }
}
function entranceApproach(x, z) {
  const r = automaticDoors.get('GD2-08');
  if (!r) return false;
  const dx = r.center[0] - r.hinge[0],
    dz = r.center[2] - r.hinge[2],
    length = Math.hypot(dx, dz),
    ux = dx / length,
    uz = dz / length,
    px = x - r.center[0],
    pz = z - r.center[2];
  return Math.abs(px * ux + pz * uz) < 0.6 && Math.abs(-px * uz + pz * ux) < 1.25;
}
function canStand(x, z, radius = 0.16) {
  const p = [x, z];
  for (const rig of automaticDoors.values()) {
    if (rig.amount > 0.02 || rig.target > 0) continue;
    for (const [a, b] of rig.segments) {
      const aa = doorPoint(rig, a, rig.amount),
        bb = doorPoint(rig, b, rig.amount);
      if (segmentDistance(p, aa, bb) < radius) return false;
    }
  }
  for (const offset of [
    [0, 0],
    [radius, 0],
    [-radius, 0],
    [0, radius],
    [0, -radius],
  ])
    if (!pointInPolygon([x + offset[0], z + offset[1]], walkOutline) && !entranceApproach(x + offset[0], z + offset[1])) return false;
  if (!window.__segGrid) {
    const G = new Map();
    for (const s of collisionSegments) {
      const x0 = Math.floor(Math.min(s[0][0], s[1][0]) - 0.3),
        x1 = Math.floor(Math.max(s[0][0], s[1][0]) + 0.3),
        z0 = Math.floor(Math.min(s[0][1], s[1][1]) - 0.3),
        z1 = Math.floor(Math.max(s[0][1], s[1][1]) + 0.3);
      for (let gx = x0; gx <= x1; gx++)
        for (let gz = z0; gz <= z1; gz++) {
          const k = gx + ',' + gz;
          if (!G.has(k)) G.set(k, []);
          G.get(k).push(s);
        }
    }
    window.__segGrid = G;
  }
  for (const [a, b] of window.__segGrid.get(Math.floor(x) + ',' + Math.floor(z)) || []) if (segmentDistance(p, a, b) < radius) return false;
  for (const { hull, min, max } of collisionHulls) {
    if (x < min[0] - radius || x > max[0] + radius || z < min[1] - radius || z > max[1] + radius) continue;
    if (pointInPolygon(p, hull)) return false;
    for (let i = 0; i < hull.length; i++) if (segmentDistance(p, hull[i], hull[(i + 1) % hull.length]) < radius) return false;
  }
  return true;
}
function moveEye(forward, side) {
  const stuck = !canStand(walkPosition[0], walkPosition[2]);
  const dx = Math.sin(walkYaw) * forward + Math.cos(walkYaw) * side,
    dz = -Math.cos(walkYaw) * forward + Math.sin(walkYaw) * side,
    steps = Math.max(1, Math.ceil(Math.hypot(dx, dz) / 0.055));
  for (let i = 0; i < steps; i++) {
    const nx = walkPosition[0] + dx / steps,
      nz = walkPosition[2] + dz / steps;
    if (stuck || canStand(nx, walkPosition[2])) walkPosition[0] = nx;
    if (stuck || canStand(walkPosition[0], nz)) walkPosition[2] = nz;
  }
}
function perspective(fov, aspect, near, far) {
  const f = 1 / Math.tan(fov / 2);
  return [f / aspect, 0, 0, 0, 0, f, 0, 0, 0, 0, (far + near) / (near - far), -1, 0, 0, (2 * far * near) / (near - far), 0];
}
function eyeProjection(width, height) {
  const cp = Math.cos(walkPitch),
    target = [walkPosition[0] + Math.sin(walkYaw) * cp, walkPosition[1] + Math.sin(walkPitch), walkPosition[2] - Math.cos(walkYaw) * cp];
  return mul(perspective(Math.PI / 3, Math.max(1, width) / Math.max(1, height), 0.08, 150), look(walkPosition, target));
}
function selectStation(index) {
  const station = eyeStations[index] || eyeStations[0];
  walkPosition = [...station.position];
  const d = sub(station.target, station.position);
  walkYaw = Math.atan2(d[0], -d[2]);
  walkPitch = Math.atan2(d[1], Math.hypot(d[0], d[2]));
  moveKeys.clear();
  $('#status').textContent = 'Eye level · ' + station.name;
  invalidate();
}
function setEyeMode(enabled) {
  eyeMode = enabled;
  moveKeys.clear();
  drag = null;
  document.body.classList.toggle('eye-level', enabled);
  $('#viewpoint').hidden = !enabled;
  $('#eye-level').setAttribute('aria-pressed', enabled);
  $('#overview').setAttribute('aria-pressed', !enabled);
  $('footer').textContent = enabled ? 'Drag to look · W A S D or ↑↓ to walk · ←→ to turn · Wheel to step' : 'Drag to orbit · Wheel to zoom · Right-drag / Shift-drag to pan';
  if (enabled) selectStation(Number($('#viewpoint').value) || 0);
  else {
    $('#status').textContent = '';
    center = [11.5, 1, -16.8];
    yaw = 0.1;
    pitch = 1.04;
    distance = 51;
  }
  canvas.focus();
  invalidate();
}
canvas.oncontextmenu = (e) => e.preventDefault();
canvas.onpointerdown = (e) => {
  canvas.focus();
  drag = { x: e.clientX, y: e.clientY, pan: e.button === 2 || e.shiftKey };
  canvas.setPointerCapture(e.pointerId);
};
canvas.onpointermove = (e) => {
  if (!drag) return;
  const dx = e.clientX - drag.x,
    dy = e.clientY - drag.y;
  if (eyeMode) {
    walkYaw += dx * 0.004;
    walkPitch = Math.max(-0.9, Math.min(0.9, walkPitch - dy * 0.004));
  } else if (drag.pan) {
    const k = distance * 0.0008;
    center[0] -= k * (dx * Math.cos(yaw) + dy * Math.sin(yaw));
    center[2] += k * (dx * Math.sin(yaw) - dy * Math.cos(yaw));
  } else {
    yaw -= dx * 0.006;
    pitch = Math.max(0.6, Math.min(1.565, pitch + dy * 0.006));
  }
  drag.x = e.clientX;
  drag.y = e.clientY;
  invalidate();
};
canvas.onpointerup =
  canvas.onpointercancel =
  canvas.onlostpointercapture =
    () => {
      drag = null;
    };
canvas.onwheel = (e) => {
  e.preventDefault();
  if (eyeMode) moveEye(Math.max(-0.65, Math.min(0.65, -e.deltaY * 0.003)), 0);
  else distance = Math.max(4, Math.min(56, distance * Math.exp(e.deltaY * 0.001)));
  invalidate();
};
canvas.tabIndex = 0;
canvas.setAttribute('aria-label', 'Office 3D view');
const keyHandler = (e) => {
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  if (e.key.toLowerCase() === 'e') {
    if (e.repeat) return;
    setEyeMode(!eyeMode);
    e.preventDefault();
    return;
  }
  if (e.key === 'Home') {
    setEyeMode(false);
    e.preventDefault();
    return;
  }
  if (eyeMode) {
    if (['KeyW', 'KeyA', 'KeyS', 'KeyD', 'ArrowUp', 'ArrowDown'].includes(e.code)) {
      if (!moveKeys.has(e.code))
        moveEye(e.code === 'KeyW' || e.code === 'ArrowUp' ? 0.07 : e.code === 'KeyS' || e.code === 'ArrowDown' ? -0.07 : 0, e.code === 'KeyD' ? 0.07 : e.code === 'KeyA' ? -0.07 : 0);
      moveKeys.add(e.code);
      e.preventDefault();
      invalidate();
      return;
    }
    if (e.code.startsWith('Shift')) {
      walkFast = true;
      return;
    }
    if (e.key === 'ArrowLeft') walkYaw -= 0.09;
    else if (e.key === 'ArrowRight') walkYaw += 0.09;
    else if (e.key === 'ArrowUp') walkPitch = Math.min(0.9, walkPitch + 0.06);
    else if (e.key === 'ArrowDown') walkPitch = Math.max(-0.9, walkPitch - 0.06);
    else return;
  } else {
    if (e.key === 'ArrowLeft') yaw -= 0.16;
    else if (e.key === 'ArrowRight') yaw += 0.16;
    else if (e.key === 'ArrowUp') pitch = Math.min(1.565, pitch + 0.12);
    else if (e.key === 'ArrowDown') pitch = Math.max(0.6, pitch - 0.12);
    else if (e.key === '+' || e.key === '=') distance = Math.max(4, distance * 0.9);
    else if (e.key === '-') distance = Math.min(56, distance / 0.9);
    else return;
  }
  e.preventDefault();
  invalidate();
};
canvas.onkeydown = keyHandler;
window.addEventListener('keydown', (e) => {
  if (e.target === canvas) return;
  const t = (e.target && e.target.tagName) || '';
  if (t === 'INPUT' || t === 'TEXTAREA' || (t === 'SELECT' && e.key.startsWith('Arrow'))) return;
  keyHandler(e);
});
window.addEventListener('keyup', (e) => {
  moveKeys.delete(e.code);
  if (e.code.startsWith('Shift')) walkFast = false;
});
window.addEventListener('blur', () => {
  moveKeys.clear();
  walkFast = false;
  drag = null;
});
window.addEventListener('resize', invalidate);
$('#day-night').onclick = () => {
  nightMode = !nightMode;
  $('#day-night').textContent = nightMode ? 'Day' : 'Night';
  $('#day-night').setAttribute('aria-pressed', nightMode);
  invalidate();
};
$('#day-night').textContent = nightMode ? 'Day' : 'Night';
$('#day-night').setAttribute('aria-pressed', nightMode);
$('#overview').onclick = () => setEyeMode(false);
$('#eye-level').onclick = () => setEyeMode(true);
$('#viewpoint').onchange = () => {
  setEyeMode(true);
  selectStation(Number($('#viewpoint').value));
  canvas.focus();
};
{
  const q = new URLSearchParams(location.search),
    requested = q.get('spot'),
    index =
      { reception: 0, model: 1, lounge: 2, meeting: 3, doors: 4, workstations: 5, storage: 6, lounge2: 2, model2: 1, bar: 9, reception2: 0, meeting2: 3, toilet: 12 }[requested] ?? (q.size ? 2 : 0);
  $('#viewpoint').value = String(index);
  if (!q.size || q.get('view') === 'eye' || requested) setEyeMode(true);
}

// Door sensors use distance to the opening, from either side, with a hold-open zone.
function doorPoint(r, p, amount) {
  const a = r.angle * amount,
    c = Math.cos(a),
    s = Math.sin(a),
    x = p[0] - r.hinge[0],
    z = p[1] - r.hinge[2];
  return [r.hinge[0] + c * x + s * z, r.hinge[2] - s * x + c * z];
}
function updateAutomaticDoors(now, dt) {
  for (const r of automaticDoors.values()) {
    const ddx = r.center[0] - walkPosition[0],
      ddz = r.center[2] - walkPosition[2],
      dist = Math.hypot(ddx, ddz),
      wc = /WC$/.test(r.id),
      facing = (Math.sin(walkYaw) * ddx - Math.cos(walkYaw) * ddz) / Math.max(dist, 0.001);
    const near = eyeMode && (wc ? (walkPosition[0] > 21.05 && dist < 2.2) || (dist < 1.1 && Math.abs(ddz) < 0.55 && Math.sin(walkYaw) > 0.55) : dist < 1.65);
    if (near) r.lastNear = now;
    r.target = eyeMode && (near || now - r.lastNear < (wc ? 450 : 1800)) ? 1 : 0;
    const next = Math.max(0, Math.min(1, r.amount + Math.sign(r.target - r.amount) * Math.min(Math.abs(r.target - r.amount), dt * 1.8)));
    if (Math.abs(next - r.amount) < 0.00001) continue;
    r.amount = next;
    const angle = r.angle * next,
      c = Math.cos(angle),
      s = Math.sin(angle);
    for (const d of r.parts) {
      const data = new Float32Array(d.original);
      d.min = [Infinity, Infinity, Infinity];
      d.max = [-Infinity, -Infinity, -Infinity];
      for (let i = 0; i < data.length; i += 8) {
        const x = data[i] - r.hinge[0],
          z = data[i + 2] - r.hinge[2],
          nx = data[i + 3],
          nz = data[i + 5];
        data[i] = r.hinge[0] + c * x + s * z;
        data[i + 2] = r.hinge[2] - s * x + c * z;
        data[i + 3] = c * nx + s * nz;
        data[i + 5] = -s * nx + c * nz;
        for (let k = 0; k < 3; k++) {
          d.min[k] = Math.min(d.min[k], data[i + k]);
          d.max[k] = Math.max(d.max[k], data[i + k]);
        }
      }
      gl.bindBuffer(gl.ARRAY_BUFFER, d.buffer);
      gl.bufferSubData(gl.ARRAY_BUFFER, 0, data);
    }
    lastShadow = '';
  }
}
// One decoder and one GPU texture supply synchronized video to all three TVs.
let tvFilm,
  tvFilmTexture,
  tvFilmTime = -1,
  tvFilmWidth = 0,
  tvFilmHeight = 0;
function startTVFilm() {
  if (!tvFilm) return;
  const pending = tvFilm.play();
  if (pending)
    pending.catch(() => {
      $('#status').textContent = 'Click the view to start the TV video';
    });
}
function initializeTVFilm() {
  tvFilm = document.createElement('video');
  tvFilm.muted = true;
  tvFilm.defaultMuted = true;
  tvFilm.loop = true;
  tvFilm.playsInline = true;
  tvFilm.preload = 'auto';
  tvFilm.setAttribute('playsinline', '');
  tvFilm.style.display = 'none';
  document.body.appendChild(tvFilm);
  tvFilm.src = 'tv_video.mp4';
  tvFilmTexture = gl.createTexture();
  gl.activeTexture(gl.TEXTURE0);
  gl.bindTexture(gl.TEXTURE_2D, tvFilmTexture);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.SRGB8_ALPHA8, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array([230, 230, 224, 255]));
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  tvFilm.addEventListener('loadeddata', () => {
    startTVFilm();
    invalidate();
  });
  tvFilm.addEventListener('error', () => {
    console.warn('TV video not found or could not play');
  });
  if (tvFilm.requestVideoFrameCallback) {
    let lastTVFrame = 0;
    const frame = (now) => {
      if (now - lastTVFrame >= 30) {
        lastTVFrame = now;
        invalidate();
      }
      tvFilm.requestVideoFrameCallback(frame);
    };
    tvFilm.requestVideoFrameCallback(frame);
  }
  document.addEventListener('pointerdown', startTVFilm, { once: true });
  document.addEventListener('keydown', startTVFilm, { once: true });
  startTVFilm();
}
function createBusinessScreen(d) {
  if (!tvFilm) initializeTVFilm();
  d.texture = tvFilmTexture;
  d.color = [1, 1, 1, 1];
  d.emission = [0.65, 0.65, 0.65];
  d.emissionMapped = true;
  businessScreens.push({ d, index: d.extras.business_screen });
}
function updateBusinessScreens() {
  if (!tvFilm || tvFilm.readyState < 2 || tvFilm.currentTime === tvFilmTime) return;
  gl.activeTexture(gl.TEXTURE0);
  gl.bindTexture(gl.TEXTURE_2D, tvFilmTexture);
  gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false);
  if (tvFilmWidth !== tvFilm.videoWidth || tvFilmHeight !== tvFilm.videoHeight) {
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.SRGB8_ALPHA8, gl.RGBA, gl.UNSIGNED_BYTE, tvFilm);
    tvFilmWidth = tvFilm.videoWidth;
    tvFilmHeight = tvFilm.videoHeight;
  } else gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, gl.RGBA, gl.UNSIGNED_BYTE, tvFilm);
  tvFilmTime = tvFilm.currentTime;
}

document.addEventListener('visibilitychange', () => {
  if (document.hidden) {
    clearTimeout(dynamicTimer);
    if (tvFilm) tvFilm.pause();
  } else {
    startTVFilm();
    invalidate();
  }
});

try {
  setup();
  load().catch(fail);
} catch (e) {
  fail(e);
}
function fail(e) {
  $('#error').hidden = false;
  $('#error').textContent = e.message + ' — Reload this page in a browser with WebGL 2 enabled.';
  $('#status').textContent = 'Viewer could not load';
  console.error(e);
}

// Planar floor reflections render actual scene geometry, not a painted highlight.
const floorReflection = {};
function renderFloorReflection(w, h, vp) {
  const rw = Math.max(1, w >> 1),
    rh = Math.max(1, h >> 1),
    f = floorReflection;
  if (!f.fbo) {
    f.fbo = gl.createFramebuffer();
    f.texture = gl.createTexture();
    f.depth = gl.createRenderbuffer();
  }
  if (f.w !== rw || f.h !== rh) {
    f.w = rw;
    f.h = rh;
    gl.activeTexture(gl.TEXTURE2);
    gl.bindTexture(gl.TEXTURE_2D, f.texture);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, rw, rh, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.bindRenderbuffer(gl.RENDERBUFFER, f.depth);
    gl.renderbufferStorage(gl.RENDERBUFFER, gl.DEPTH_COMPONENT16, rw, rh);
    gl.bindFramebuffer(gl.FRAMEBUFFER, f.fbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, f.texture, 0);
    gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.RENDERBUFFER, f.depth);
  }
  gl.bindFramebuffer(gl.FRAMEBUFFER, f.fbo);
  gl.viewport(0, 0, rw, rh);
  gl.depthMask(true);
  gl.clearColor(nightMode ? 0.035 : 0.58, nightMode ? 0.04 : 0.65, nightMode ? 0.055 : 0.7, 1);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.activeTexture(gl.TEXTURE2);
  gl.bindTexture(gl.TEXTURE_2D, whiteTexture);
  gl.uniform1i(U.reflectionMap, 2);
  gl.uniform1i(U.floorSurface, false);
  gl.uniform3fv(U.viewEye, [viewEye[0], -viewEye[1], viewEye[2]]);
  gl.uniformMatrix4fv(U.vp, false, new Float32Array(mul(vp, [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0.002, 0, 1])));
  for (const transparent of [false, true]) {
    gl.depthMask(!transparent);
    for (const d of draws) {
      if (d.floor || d.glass !== transparent || !visible(d)) continue;
      gl.bindVertexArray(d.vao);
      gl.uniform1f(U.roughness, d.roughness);
      gl.uniform1f(U.metallic, d.metallic);
      gl.uniform1i(U.clearGlass, d.glass);
      gl.uniform4fv(U.color, d.color);
      gl.uniform3fv(U.emission, d.emission);
      gl.uniform1i(U.emissionMapped, !!d.emissionMapped);
      gl.uniform1i(U.liveTV, d.extras.business_screen !== undefined);
      gl.uniform1i(U.displayScreen, !!d.screenLight);
      gl.uniform1i(U.fixtureLight, !d.screenLight && !d.extras.capital_crest_display && d.emission.some((v) => v > 0));
      gl.uniform1f(U.cutoff, cutoff(d));
      gl.uniform1f(U.alphaTest, d.alphaTest);
      gl.uniform1i(U.highlight, false);
      gl.uniform1i(U.textured, !!d.texture);
      gl.activeTexture(gl.TEXTURE0);
      gl.bindTexture(gl.TEXTURE_2D, d.texture || whiteTexture);
      gl.drawArrays(gl.TRIANGLES, 0, d.count);
    }
  }
  gl.depthMask(true);
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  gl.viewport(0, 0, w, h);
}

// Animated visitors: GPU-skinned RenderPeople figures + coffee-cup props, baked choreography.
window.PEOPLE = (function () {
  'use strict';
  const HIDE = new Set(['Lounge / north guest', 'Lounge / east guest', 'Lounge / south guest left', 'Lounge / south guest right', 'Coffee bar / service attendant']);
  const CUP_NODE = 'Coffee V4 patterned cappuccino cups with latte art';
  const SAUCER0 = [17.25, 1.054, -12.6],
    CUP0 = [17.25, 1.065, -12.6],
    LATTE0 = [17.25, 1.121, -12.6];
  const P = { playing: true, actors: [], props: { saucer: [], cup: [], latte: [] }, ready: false, t: 0, last: null, speed: 1, blobs: new Float32Array(64) };
  let H,
    bin,
    boneTex,
    boneData,
    maxBones = 0,
    stream = null;
  function prepare(draws) {
    const out = [];
    for (const d of draws) {
      if (HIDE.has(d.name)) continue;
      if (d.name === CUP_NODE) {
        const keep = [],
          sau = [],
          cup = [];
        let latte = true,
          any = false;
        for (let i = 0; i < d.data.length; i += 24) {
          const cx = (d.data[i] + d.data[i + 8] + d.data[i + 16]) / 3,
            cy = (d.data[i + 1] + d.data[i + 9] + d.data[i + 17]) / 3,
            cz = (d.data[i + 2] + d.data[i + 10] + d.data[i + 18]) / 3;
          if (cx > 17.1 && cx < 17.4 && cz > -12.78 && cz < -12.42) {
            any = true;
            const tri = d.data.slice(i, i + 24);
            if (Math.abs(cy - 1.121) > 0.003) latte = false;
            (cy < 1.0655 ? sau : cup).push(tri);
          } else for (let k = 0; k < 24; k++) keep.push(d.data[i + k]);
        }
        if (any) {
          const mk = (list, o) => {
            const a = new Float32Array(list.length * 24);
            list.forEach((t, j) => {
              for (let v = 0; v < 3; v++) {
                const b = j * 24 + v * 8;
                for (let k = 0; k < 8; k++) a[b + k] = t[v * 8 + k];
                a[b] -= o[0];
                a[b + 1] -= o[1];
                a[b + 2] -= o[2];
              }
            });
            return a;
          };
          const mat = { color: d.color, roughness: d.roughness, metallic: d.metallic, texture: d.texture, emission: d.emission };
          if (latte && cup.length) P.props.latte.push({ ...mat, data: mk(cup, LATTE0) });
          else {
            if (sau.length) P.props.saucer.push({ ...mat, data: mk(sau, SAUCER0) });
            if (cup.length) P.props.cup.push({ ...mat, data: mk(cup, CUP0) });
          }
          d.data = keep;
          d.count = keep.length / 8;
          if (!d.count) continue;
        }
      }
      if (d.name === 'Coffee V4 espresso machine and grinder' && (d.texture || (d.color[0] > 0.85 && d.color[1] > 0.85) || (d.metallic > 0.8 && d.color[2] < 0.4 && d.color[0] > 0.7))) {
        const keep = [];
        for (let i = 0; i < d.data.length; i += 24) {
          const cx = (d.data[i] + d.data[i + 8] + d.data[i + 16]) / 3,
            cy = (d.data[i + 1] + d.data[i + 9] + d.data[i + 17]) / 3,
            cz = (d.data[i + 2] + d.data[i + 10] + d.data[i + 18]) / 3;
          if (cx > 18.66 && cx < 18.86 && cz > -13.22 && cz < -13.02 && cy < 1.06) continue;
          for (let k = 0; k < 24; k++) keep.push(d.data[i + k]);
        }
        d.data = keep;
        d.count = keep.length / 8;
        if (!d.count) continue;
      }
      out.push(d);
    }
    return out;
  }
  function view(o, type) {
    return new type(bin.buffer, bin.byteOffset + H.off + o[0], o[1] / type.BYTES_PER_ELEMENT);
  }
  function staticVAO(data) {
    const vao = gl.createVertexArray();
    gl.bindVertexArray(vao);
    const b = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, b);
    gl.bufferData(gl.ARRAY_BUFFER, data, gl.STATIC_DRAW);
    for (const [a, size, offset] of [
      [0, 3, 0],
      [1, 3, 12],
      [2, 2, 24],
    ]) {
      gl.enableVertexAttribArray(a);
      gl.vertexAttribPointer(a, size, gl.FLOAT, false, 32, offset);
    }
    gl.bindVertexArray(null);
    return vao;
  }
  async function init() {
    try {
      const st = document.getElementById('status');
      if (st) st.textContent = 'Loading visitors...';
      const res = await fetch('people.bin');
      if (!res.ok) throw Error('people.bin failed to load: ' + res.status);
      let bytes = new Uint8Array(await res.arrayBuffer());
      if (bytes[0] === 0x1f && bytes[1] === 0x8b) bytes = new Uint8Array(await new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer());
      const dv = new DataView(bytes.buffer);
      const hl = dv.getUint32(4, true);
      H = JSON.parse(new TextDecoder().decode(bytes.subarray(8, 8 + hl)));
      H.off = 8 + hl;
      bin = bytes;
      for (const A of H.actors) {
        const vao = gl.createVertexArray();
        gl.bindVertexArray(vao);
        const attr = (loc, arr, size, type, normalized) => {
          const b = gl.createBuffer();
          gl.bindBuffer(gl.ARRAY_BUFFER, b);
          gl.bufferData(gl.ARRAY_BUFFER, arr, gl.STATIC_DRAW);
          gl.enableVertexAttribArray(loc);
          gl.vertexAttribPointer(loc, size, type, normalized, 0, 0);
        };
        attr(0, view(A.pos, Float32Array), 3, gl.FLOAT, false);
        attr(1, view(A.nrm, Int8Array), 3, gl.BYTE, true);
        attr(2, view(A.uv, Float32Array), 2, gl.FLOAT, false);
        attr(3, view(A.j, Uint8Array), 4, gl.UNSIGNED_BYTE, false);
        attr(4, view(A.w, Uint8Array), 4, gl.UNSIGNED_BYTE, true);
        const ib = gl.createBuffer();
        gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, ib);
        gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, A.u32 ? view(A.idx, Uint32Array) : view(A.idx, Uint16Array), gl.STATIC_DRAW);
        gl.bindVertexArray(null);
        const bmp = await createImageBitmap(new Blob([view(A.tex, Uint8Array)], { type: 'image/jpeg' }));
        const tex = gl.createTexture();
        gl.activeTexture(gl.TEXTURE0);
        gl.bindTexture(gl.TEXTURE_2D, tex);
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.SRGB8_ALPHA8, gl.RGBA, gl.UNSIGNED_BYTE, bmp);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
        gl.generateMipmap(gl.TEXTURE_2D);
        bmp.close();
        P.actors.push({
          A,
          vao,
          tex,
          count: A.nt * 3,
          u32: A.u32,
          par: view(A.par, Int16Array),
          rest: view(A.rest, Float32Array),
          inv: view(A.inv, Float32Array),
          hip: view(A.hip, Float32Array),
          q: view(A.q, Int16Array),
          world: new Float32Array(A.nb * 12),
        });
        maxBones = Math.max(maxBones, A.nb);
      }
      boneData = new Float32Array(maxBones * 3 * 4 * P.actors.length);
      boneTex = gl.createTexture();
      gl.activeTexture(gl.TEXTURE4);
      gl.bindTexture(gl.TEXTURE_2D, boneTex);
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, maxBones * 3, P.actors.length, 0, gl.RGBA, gl.FLOAT, null);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
      gl.activeTexture(gl.TEXTURE0);
      for (const k of ['saucer', 'cup', 'latte'])
        for (const p of P.props[k]) {
          p.vao = staticVAO(p.data);
          p.count = p.data.length / 8;
        }
      P.sau = view(H.props.saucer, Float32Array);
      P.cupM = view(H.props.cup, Float32Array);
      P.level = view(H.props.level, Float32Array);
      P.stream = view(H.props.stream, Uint8Array);
      // coffee stream: thin cylinder from y=0 down to y=-1
      const seg = 10,
        r = 0.0032,
        cyl = [];
      for (let i = 0; i < seg; i++) {
        const a0 = (i / seg) * Math.PI * 2,
          a1 = ((i + 1) / seg) * Math.PI * 2;
        const v = (a, y) => [Math.cos(a) * r, y, Math.sin(a) * r, Math.cos(a), 0, Math.sin(a), 0, 0];
        cyl.push(...v(a0, 0), ...v(a1, 0), ...v(a1, -1), ...v(a0, 0), ...v(a1, -1), ...v(a0, -1));
      }
      stream = { vao: staticVAO(new Float32Array(cyl)), count: cyl.length / 8 };
      gl.useProgram(program);
      gl.uniform1i(U.boneTex, 4);
      gl.uniformMatrix4fv(U.model, false, new Float32Array(I()));
      gl.uniform1i(U.skinMode, 0);
      P.ready = true;
      P.start = performance.now();
      const btn = document.getElementById('people-toggle');
      if (btn) {
        btn.hidden = false;
        btn.onclick = () => {
          P.playing = !P.playing;
          btn.textContent = P.playing ? 'Pause people' : 'Play people';
          btn.setAttribute('aria-pressed', P.playing);
          P.last = null;
          invalidate();
        };
      }
    } catch (e) {
      console.warn('People animation unavailable', e);
    }
  }
  function qmat(x, y, z, w) {
    return [
      1 - 2 * (y * y + z * z),
      2 * (x * y - z * w),
      2 * (x * z + y * w),
      2 * (x * y + z * w),
      1 - 2 * (x * x + z * z),
      2 * (y * z - x * w),
      2 * (x * z - y * w),
      2 * (y * z + x * w),
      1 - 2 * (x * x + y * y),
    ];
  }
  function m34mul(a, ao, b, bo, o, oo) {
    // 3x4 row-major
    for (let r = 0; r < 3; r++) {
      const a0 = a[ao + r * 4],
        a1 = a[ao + r * 4 + 1],
        a2 = a[ao + r * 4 + 2],
        a3 = a[ao + r * 4 + 3];
      o[oo + r * 4] = a0 * b[bo] + a1 * b[bo + 4] + a2 * b[bo + 8];
      o[oo + r * 4 + 1] = a0 * b[bo + 1] + a1 * b[bo + 5] + a2 * b[bo + 9];
      o[oo + r * 4 + 2] = a0 * b[bo + 2] + a1 * b[bo + 6] + a2 * b[bo + 10];
      o[oo + r * 4 + 3] = a0 * b[bo + 3] + a1 * b[bo + 7] + a2 * b[bo + 11] + a3;
    }
  }
  const tmp = new Float32Array(12),
    rq = new Float32Array(12);
  function quatAt(arr, base, stride, f0, f1, w, scale) {
    // nlerp int16 or float quats
    let x0 = arr[f0 * stride + base],
      y0 = arr[f0 * stride + base + 1],
      z0 = arr[f0 * stride + base + 2],
      w0 = arr[f0 * stride + base + 3];
    let x1 = arr[f1 * stride + base],
      y1 = arr[f1 * stride + base + 1],
      z1 = arr[f1 * stride + base + 2],
      w1 = arr[f1 * stride + base + 3];
    if (x0 * x1 + y0 * y1 + z0 * z1 + w0 * w1 < 0) {
      x1 = -x1;
      y1 = -y1;
      z1 = -z1;
      w1 = -w1;
    }
    let x = x0 + (x1 - x0) * w,
      y = y0 + (y1 - y0) * w,
      z = z0 + (z1 - z0) * w,
      q = w0 + (w1 - w0) * w;
    const n = Math.hypot(x, y, z, q) || 1;
    return [x / n, y / n, z / n, q / n];
  }
  function update(now) {
    if (!P.ready) return;
    if (P.playing) {
      if (P.last !== null) P.t = (P.t + Math.min(0.1, (now - P.last) / 1000) * P.speed) % H.L;
      P.last = now;
    }
    const f = P.t * H.fps,
      N = H.frames,
      f0 = Math.floor(f) % N,
      f1 = (f0 + 1) % N,
      w = f - Math.floor(f);
    P.f0 = f0;
    P.f1 = f1;
    P.w = w;
    let nb = 0;
    P.blobs.fill(0);
    P.actors.forEach((ac, row) => {
      const A = ac.A,
        n = A.nb,
        W = ac.world,
        base = row * maxBones * 12;
      for (let i = 0; i < n; i++) {
        const q = quatAt(ac.q, i * 4, n * 4, f0, f1, w),
          R = qmat(...q);
        rq[0] = R[0];
        rq[1] = R[1];
        rq[2] = R[2];
        rq[3] = 0;
        rq[4] = R[3];
        rq[5] = R[4];
        rq[6] = R[5];
        rq[7] = 0;
        rq[8] = R[6];
        rq[9] = R[7];
        rq[10] = R[8];
        rq[11] = 0;
        const p = ac.par[i];
        if (p < 0) {
          for (let k = 0; k < 12; k++) W[k] = rq[k];
          W[3] = ac.hip[f0 * 3] + (ac.hip[f1 * 3] - ac.hip[f0 * 3]) * w;
          W[7] = ac.hip[f0 * 3 + 1] + (ac.hip[f1 * 3 + 1] - ac.hip[f0 * 3 + 1]) * w;
          W[11] = ac.hip[f0 * 3 + 2] + (ac.hip[f1 * 3 + 2] - ac.hip[f0 * 3 + 2]) * w;
        } else {
          m34mul(W, p * 12, ac.rest, i * 12, tmp, 0);
          m34mul(tmp, 0, rq, 0, W, i * 12);
        }
        m34mul(W, i * 12, ac.inv, i * 12, boneData, base + i * 12);
      }
      // contact shadows
      for (const fi of [A.feet[0], A.feet[1]]) {
        const x = W[fi * 12 + 3],
          y = W[fi * 12 + 7],
          z = W[fi * 12 + 11];
        if (nb < 16) {
          P.blobs.set([x, z, 0.13, 0.42 * Math.max(0, 1 - (y - 0.06) / 0.35)], nb * 4);
          nb++;
        }
      }
      const hy = W[7];
      if (hy > 0.7 && nb < 16) {
        P.blobs.set([W[3], W[11], 0.32, 0.2], nb * 4);
        nb++;
      }
    });
    gl.activeTexture(gl.TEXTURE4);
    gl.bindTexture(gl.TEXTURE_2D, boneTex);
    gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, maxBones * 3, P.actors.length, gl.RGBA, gl.FLOAT, boneData);
    gl.activeTexture(gl.TEXTURE0);
    gl.uniform4fv(U.blobs, P.blobs);
  }
  function rigid(arr, f0, f1, w) {
    const a = f0 * 7,
      b = f1 * 7,
      p = [0, 1, 2].map((k) => arr[a + k] + (arr[b + k] - arr[a + k]) * w);
    const q = quatAt(arr, 3, 7, f0, f1, w),
      R = qmat(...q);
    return [R[0], R[3], R[6], 0, R[1], R[4], R[7], 0, R[2], R[5], R[8], 0, p[0], p[1], p[2], 1];
  }
  function setMat(d) {
    gl.uniform1i(U.floorSurface, false);
    gl.uniform1f(U.roughness, d.roughness);
    gl.uniform1f(U.metallic, d.metallic);
    gl.uniform1i(U.clearGlass, false);
    gl.uniform4fv(U.color, d.color);
    gl.uniform3fv(U.emission, d.emission || [0, 0, 0]);
    gl.uniform1i(U.emissionMapped, false);
    gl.uniform1i(U.liveTV, false);
    gl.uniform1i(U.displayScreen, false);
    gl.uniform1i(U.fixtureLight, false);
    gl.uniform1f(U.cutoff, 99);
    gl.uniform1f(U.alphaTest, 0);
    gl.uniform1i(U.highlight, false);
    gl.uniform1i(U.textured, !!d.texture);
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, d.texture || whiteTexture);
  }
  function draw() {
    if (!P.ready) return;
    gl.depthMask(true);
    gl.disable(gl.POLYGON_OFFSET_FILL);
    gl.uniform1i(U.skinMode, 1);
    gl.uniformMatrix4fv(U.model, false, new Float32Array(I()));
    P.actors.forEach((ac, row) => {
      setMat({ roughness: 0.78, metallic: 0, color: [1, 1, 1, 1], texture: ac.tex });
      gl.uniform1i(U.boneRow, row);
      gl.bindVertexArray(ac.vao);
      gl.drawElements(gl.TRIANGLES, ac.count, ac.u32 ? gl.UNSIGNED_INT : gl.UNSIGNED_SHORT, 0);
    });
    gl.uniform1i(U.skinMode, 0);
    const { f0, f1, w } = P,
      S = rigid(P.sau, f0, f1, w),
      C = rigid(P.cupM, f0, f1, w);
    for (const d of P.props.saucer) {
      setMat(d);
      gl.uniformMatrix4fv(U.model, false, new Float32Array(S));
      gl.bindVertexArray(d.vao);
      gl.drawArrays(gl.TRIANGLES, 0, d.count);
    }
    for (const d of P.props.cup) {
      setMat(d);
      gl.uniformMatrix4fv(U.model, false, new Float32Array(C));
      gl.bindVertexArray(d.vao);
      gl.drawArrays(gl.TRIANGLES, 0, d.count);
    }
    const lv = P.level[f0] + (P.level[f1] - P.level[f0]) * w;
    if (lv > 0.013 && P.level[f0] > 0.013) {
      // keep the coffee surface level; shrink it with the taper of the cup
      const s = (0.028 + ((0.041 - 0.028) * (lv - 0.008)) / 0.048) / 0.041,
        cx = C[12] + C[4] * lv,
        cy = C[13] + C[5] * lv,
        cz = C[14] + C[6] * lv,
        yaw = Math.atan2(C[8], C[10]),
        c = Math.cos(yaw) * s,
        sn = Math.sin(yaw) * s;
      const M = [c, 0, -sn, 0, 0, 1, 0, 0, sn, 0, c, 0, cx, cy, cz, 1];
      for (const d of P.props.latte) {
        setMat(d);
        gl.uniformMatrix4fv(U.model, false, new Float32Array(M));
        gl.bindVertexArray(d.vao);
        gl.drawArrays(gl.TRIANGLES, 0, d.count);
      }
    }
    if (P.stream[f0] && stream) {
      const top = H.spout,
        bottom = C[13] + C[5] * Math.max(lv, 0.012),
        len = Math.max(0.01, top[1] - bottom),
        wob = 1 + 0.15 * Math.sin(performance.now() / 40);
      setMat({ roughness: 0.3, metallic: 0, color: [0.22, 0.12, 0.05, 1] });
      gl.uniformMatrix4fv(U.model, false, new Float32Array([wob, 0, 0, 0, 0, len, 0, 0, 0, 0, wob, 0, top[0], top[1], top[2], 1]));
      gl.bindVertexArray(stream.vao);
      gl.drawArrays(gl.TRIANGLES, 0, stream.count);
    }
    gl.uniformMatrix4fv(U.model, false, new Float32Array(I()));
    gl.bindVertexArray(null);
  }
  P.prepare = prepare;
  P.init = init;
  P.update = update;
  P.draw = draw;
  return P;
})();

// Live employee monitors: one animated canvas atlas, a different app on every screen.
(function () {
  const COLS = 5,
    ROWS = 4,
    TW = 384,
    TH = 216,
    cv = document.createElement('canvas');
  cv.width = COLS * TW;
  cv.height = ROWS * TH;
  const g = cv.getContext('2d');
  let tex = null,
    frame = 0;
  const apps = ['sheet', 'chart', 'code', 'crm', 'mail', 'cad', 'call', 'tower', 'calendar', 'sheet', 'code', 'chart', 'crm', 'cad', 'mail', 'call', 'tower', 'sheet', 'chart', 'calendar'];
  const rnd = (s) => {
    let x = Math.sin(s * 12.9898) * 43758.5453;
    return x - Math.floor(x);
  };
  function chrome(x, y, title, accent) {
    g.fillStyle = '#f4f6f8';
    g.fillRect(x, y, TW, TH);
    g.fillStyle = accent;
    g.fillRect(x, y, TW, 18);
    g.fillStyle = '#fff';
    g.font = 'bold 10px Arial';
    g.fillText(title, x + 8, y + 12);
    g.fillStyle = '#1d2733';
    g.fillRect(x, y + TH - 12, TW, 12);
    g.fillStyle = '#9fb3c8';
    g.font = '8px Arial';
    g.fillText(new Date().toLocaleTimeString(), x + TW - 58, y + TH - 3);
  }
  function draw(i, t) {
    const x = (i % COLS) * TW,
      y = Math.floor(i / COLS) * TH,
      a = apps[i];
    if (a === 'sheet') {
      chrome(x, y, 'Sales tracker · Capital Crest.xlsx', '#1f7a4d');
      g.font = '9px Arial';
      for (let r = 0; r < 11; r++)
        for (let c = 0; c < 6; c++) {
          g.strokeStyle = '#d5dbe1';
          g.strokeRect(x + 6 + c * 62, y + 24 + r * 15, 62, 15);
          g.fillStyle = r === 0 ? '#1f7a4d' : '#33404d';
          const v =
            r === 0
              ? ['Unit', 'Tower', 'Area', 'Price', 'Status', 'Agent'][c]
              : c === 3
                ? '₹' + (1.2 + rnd(i * 99 + r * 7 + c + Math.floor(t / 3)) * 3).toFixed(2) + ' Cr'
                : c === 4
                  ? rnd(r + i) > 0.5
                    ? 'Booked'
                    : 'Open'
                  : c === 0
                    ? 'A-' + (100 + r * 3 + i)
                    : c === 2
                      ? 1450 + Math.floor(rnd(r * c + i) * 900) + ' sqft'
                      : c === 1
                        ? 'T' + (1 + (r % 3))
                        : ['Riya', 'Aman', 'Neha', 'Karan'][r % 4];
          g.fillText(v, x + 10 + c * 62, y + 35 + r * 15);
        }
      g.fillStyle = 'rgba(31,122,77,.18)';
      g.fillRect(x + 6, y + 24 + 15 * (1 + (Math.floor(t * 1.5) % 10)), 372, 15);
    } else if (a === 'chart') {
      chrome(x, y, 'Site visits · live analytics', '#2f5fb3');
      g.strokeStyle = '#d5dbe1';
      for (let k = 0; k < 5; k++) {
        g.beginPath();
        g.moveTo(x + 30, y + 40 + k * 30);
        g.lineTo(x + 370, y + 40 + k * 30);
        g.stroke();
      }
      g.strokeStyle = '#2f5fb3';
      g.lineWidth = 2;
      g.beginPath();
      for (let k = 0; k <= 34; k++) {
        const v = 60 + 40 * Math.sin((k + t * 2 + i) / 4) + 20 * rnd(k + Math.floor(t) + i);
        g.lineTo(x + 30 + k * 10, y + 165 - v);
      }
      g.stroke();
      g.strokeStyle = '#e08a2e';
      g.beginPath();
      for (let k = 0; k <= 34; k++) {
        const v = 40 + 30 * Math.cos((k + t * 1.5) / 5);
        g.lineTo(x + 30 + k * 10, y + 165 - v);
      }
      g.stroke();
      g.lineWidth = 1;
      g.fillStyle = '#2f5fb3';
      g.font = 'bold 18px Arial';
      g.fillText(1200 + (Math.floor(t * 3) % 400) + ' visits', x + 240, y + 36);
    } else if (a === 'code') {
      g.fillStyle = '#1e1e1e';
      g.fillRect(x, y, TW, TH);
      g.fillStyle = '#333';
      g.fillRect(x, y, TW, 16);
      g.fillStyle = '#ccc';
      g.font = '9px monospace';
      g.fillText('booking_service.py — VS Code', x + 8, y + 11);
      const L = [
        'def reserve_unit(unit, client):',
        '    if unit.status != "open":',
        '        raise UnitTaken(unit.id)',
        '    price = quote(unit, client.plan)',
        '    lead = crm.find(client.phone)',
        '    lead.stage = "booked"',
        '    unit.status = "booked"',
        '    notify(client, price)',
        '    return Booking(unit, client)',
        '',
        'class Quote:',
        '    tower: str',
        '    floor: int',
      ];
      const shown = Math.floor(t * 6 + i * 5) % (L.length * 12);
      const cols = ['#c586c0', '#9cdcfe', '#ce9178', '#dcdcaa', '#4ec9b0'];
      for (let k = 0; k < L.length; k++) {
        g.fillStyle = '#6e7681';
        g.fillText(String(k + 1).padStart(2), x + 6, y + 30 + k * 13);
        g.fillStyle = cols[(k + i) % 5];
        let s = L[k];
        if (k === Math.floor(shown / 12) % L.length) s = s.slice(0, Math.min(s.length, (shown % 12) * 4)) + '▌';
        g.fillText(s, x + 26, y + 30 + k * 13);
      }
    } else if (a === 'crm') {
      chrome(x, y, 'CRM · Leads pipeline', '#7a3fb3');
      const st = ['New', 'Contacted', 'Site visit', 'Negotiation', 'Booked'];
      for (let c = 0; c < 5; c++) {
        g.fillStyle = '#e6e9ee';
        g.fillRect(x + 6 + c * 75, y + 24, 71, 170);
        g.fillStyle = '#55606b';
        g.font = 'bold 8px Arial';
        g.fillText(st[c], x + 10 + c * 75, y + 34);
        const n = 2 + Math.floor(rnd(c + i + Math.floor(t / 4)) * 4);
        for (let k = 0; k < n; k++) {
          g.fillStyle = '#fff';
          g.fillRect(x + 9 + c * 75, y + 40 + k * 30, 65, 25);
          g.fillStyle = ['#7a3fb3', '#2f5fb3', '#e08a2e', '#1f7a4d', '#c0392b'][(k + c) % 5];
          g.fillRect(x + 9 + c * 75, y + 40 + k * 30, 3, 25);
          g.fillStyle = '#333';
          g.font = '8px Arial';
          g.fillText(['Mehta', 'Sharma', 'Gupta', 'Khan', 'Rao', 'Iyer'][(k + c + i) % 6], x + 15 + c * 75, y + 51 + k * 30);
          g.fillStyle = '#888';
          g.fillText('₹' + (1 + ((k * c + i) % 5) * 0.4).toFixed(1) + ' Cr', x + 15 + c * 75, y + 61 + k * 30);
        }
      }
    } else if (a === 'mail') {
      chrome(x, y, 'Inbox — Outlook', '#0b6cbd');
      g.font = '9px Arial';
      for (let k = 0; k < 10; k++) {
        const r = (k + Math.floor(t / 2) + i) % 14;
        g.fillStyle = k === 0 ? '#dbe9f7' : '#fff';
        g.fillRect(x + 6, y + 22 + k * 17, 372, 16);
        g.fillStyle = '#1d2733';
        g.font = (k < 3 ? 'bold ' : '') + '9px Arial';
        g.fillText(
          ['Site visit confirmed', 'Payment schedule', 'Brochure request', 'Tower B floor plans', 'Loan pre-approval', 'Booking amount', 'Club house update', 'Weekly sales report'][r % 8],
          x + 10,
          y + 33 + k * 17,
        );
        g.fillStyle = '#7d8a97';
        g.font = '8px Arial';
        g.fillText(['Aarav', 'Diya', 'Kabir', 'Isha', 'Vihaan'][r % 5] + ' · ' + (9 + (r % 9)) + ':' + String((r * 7) % 60).padStart(2, '0'), x + 260, y + 33 + k * 17);
      }
    } else if (a === 'cad') {
      g.fillStyle = '#0f1720';
      g.fillRect(x, y, TW, TH);
      g.strokeStyle = '#2e3b48';
      for (let k = 0; k < TW; k += 16) {
        g.beginPath();
        g.moveTo(x + k, y);
        g.lineTo(x + k, y + TH);
        g.stroke();
      }
      for (let k = 0; k < TH; k += 16) {
        g.beginPath();
        g.moveTo(x, y + k);
        g.lineTo(x + TW, y + k);
        g.stroke();
      }
      g.strokeStyle = '#5fd3ff';
      g.lineWidth = 2;
      g.strokeRect(x + 40, y + 30, 300, 150);
      g.beginPath();
      g.moveTo(x + 150, y + 30);
      g.lineTo(x + 150, y + 180);
      g.moveTo(x + 40, y + 110);
      g.lineTo(x + 150, y + 110);
      g.moveTo(x + 250, y + 30);
      g.lineTo(x + 250, y + 120);
      g.lineTo(x + 340, y + 120);
      g.stroke();
      g.strokeStyle = '#ffd166';
      g.beginPath();
      g.arc(x + 150, y + 110, 22, 0, Math.PI / 2);
      g.stroke();
      g.lineWidth = 1;
      g.fillStyle = '#9fe8ff';
      g.font = '9px monospace';
      g.fillText('LIVING 5.2 x 4.1', x + 165, y + 80);
      g.fillText('BED 1 3.6 x 3.4', x + 50, y + 70);
      g.fillText('KITCHEN', x + 265, y + 70);
      const cx = x + 40 + ((t * 30) % 300);
      g.strokeStyle = '#ff5c8a';
      g.beginPath();
      g.moveTo(cx, y + 20);
      g.lineTo(cx, y + 190);
      g.stroke();
    } else if (a === 'call') {
      g.fillStyle = '#202124';
      g.fillRect(x, y, TW, TH);
      for (let k = 0; k < 4; k++) {
        const px = x + 8 + (k % 2) * 186,
          py = y + 8 + Math.floor(k / 2) * 96;
        g.fillStyle = ['#3c4043', '#4a3f35', '#35414a', '#3f4a3c'][k];
        g.fillRect(px, py, 180, 90);
        g.fillStyle = ['#e8b89a', '#c99b7b', '#f0c8a8', '#a8795b'][k];
        g.beginPath();
        g.arc(px + 90, py + 40, 18, 0, 7);
        g.fill();
        g.fillRect(px + 68, py + 58, 44, 30);
        if (Math.floor(t * 2 + k) % 4 === 0) {
          g.strokeStyle = '#8ab4f8';
          g.lineWidth = 3;
          g.strokeRect(px, py, 180, 90);
          g.lineWidth = 1;
        }
        g.fillStyle = '#fff';
        g.font = '8px Arial';
        g.fillText(['Sales head', 'Architect', 'Client', 'Site engineer'][k], px + 5, py + 85);
      }
    } else if (a === 'tower') {
      const gr = g.createLinearGradient(x, y, x, y + TH);
      gr.addColorStop(0, '#9cc6e8');
      gr.addColorStop(1, '#e8f1f8');
      g.fillStyle = gr;
      g.fillRect(x, y, TW, TH);
      const w = 70 + 20 * Math.sin(t / 2 + i);
      g.fillStyle = '#2c4a66';
      g.fillRect(x + TW / 2 - w / 2, y + 30, w, 170);
      g.fillStyle = '#4f7ea3';
      g.fillRect(x + TW / 2 - w / 2 + w * 0.55, y + 30, w * 0.45, 170);
      g.fillStyle = '#bfe3ff';
      for (let r = 0; r < 14; r++) for (let c = 0; c < 5; c++) if (rnd(r * 5 + c + Math.floor(t)) > 0.35) g.fillRect(x + TW / 2 - w / 2 + 4 + (c * (w - 8)) / 5, y + 36 + r * 12, (w - 8) / 5 - 3, 7);
      g.fillStyle = '#5d8a3c';
      g.fillRect(x, y + 198, TW, 6);
      g.fillStyle = '#1d2733';
      g.font = 'bold 10px Arial';
      g.fillText('Capital Crest — 3D view', x + 8, y + 16);
    } else {
      chrome(x, y, 'Calendar — this week', '#c0392b');
      const d = ['Mon', 'Tue', 'Wed', 'Thu', 'Fri'];
      g.font = '8px Arial';
      for (let c = 0; c < 5; c++) {
        g.fillStyle = '#55606b';
        g.fillText(d[c], x + 20 + c * 72, y + 32);
        for (let k = 0; k < 3; k++) {
          if (rnd(c * 3 + k + i) > 0.45) {
            g.fillStyle = ['#f6c9c4', '#c9def6', '#cdeccf'][k];
            const yy = y + 40 + k * 48 + rnd(c + k) * 10;
            g.fillRect(x + 10 + c * 72, yy, 66, 34);
            g.fillStyle = '#333';
            g.fillText(['Client walk-in', 'Site visit', 'Team sync', 'Bank meeting'][(c + k + i) % 4], x + 13 + c * 72, yy + 12);
          }
        }
      }
      const ny = y + 40 + ((t * 8) % 150);
      g.fillStyle = '#c0392b';
      g.fillRect(x + 6, ny, 372, 1.5);
    }
  }
  function update() {
    const t = performance.now() / 1000;
    for (let i = 0; i < COLS * ROWS; i++) draw(i, t + i * 0.37);
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false);
    gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, gl.RGBA, gl.UNSIGNED_BYTE, cv);
    invalidate();
  }
  function init() {
    if (!window.officeViewer || !window.officeViewer.ready) {
      setTimeout(init, 300);
      return;
    }
    const ds = draws.filter((d) => d.extras && d.extras.monitor_live !== undefined);
    if (!ds.length) return;
    tex = gl.createTexture();
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.SRGB8_ALPHA8, cv.width, cv.height, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    for (const d of ds) {
      d.texture = tex;
      d.color = [1, 1, 1, 1];
      d.emissionMapped = true;
      d.screenLight = true;
    }
    update();
    setInterval(() => {
      if (!document.hidden) update();
    }, 500);
  }
  init();
})();

// Merge PDF viewpoints into their matching stations.
(function () {
  const S = eyeStations,
    map = { 0: 10, 1: 8, 2: 7, 3: 11 };
  for (const [to, from] of Object.entries(map)) {
    S[to].position = [...S[from].position];
    S[to].target = [...S[from].target];
  }
  S[9].name = 'Coffee bar';
  const sel = document.getElementById('viewpoint');
  for (const o of [...sel.options]) {
    if (['7', '8', '10', '11'].includes(o.value)) o.remove();
    if (o.value === '9') o.textContent = 'Coffee bar';
  }
  if (!['0', '1', '2', '3', '4', '5', '6', '9', '12'].includes(sel.value)) {
    sel.value = '2';
  }
  if (eyeMode) selectStation(Number(sel.value));
})();

// Viewpoint pop-up menu (replaces the native select).
(function () {
  const sel = document.getElementById('viewpoint');
  if (!sel) return;
  const wrap = document.createElement('span');
  wrap.className = 'vp-wrap';
  const tog = document.createElement('button');
  tog.id = 'viewpoint-toggle';
  tog.type = 'button';
  tog.setAttribute('aria-haspopup', 'true');
  tog.setAttribute('aria-expanded', 'false');
  const menu = document.createElement('div');
  menu.className = 'vp-menu';
  menu.hidden = true;
  menu.setAttribute('role', 'menu');
  sel.parentNode.insertBefore(wrap, sel);
  wrap.append(tog, menu, sel);
  const label = () => {
    const o = sel.options[sel.selectedIndex];
    tog.textContent = o ? o.textContent : 'Viewpoint';
  };
  function build() {
    menu.innerHTML = '';
    for (const o of sel.options) {
      const b = document.createElement('button');
      b.type = 'button';
      b.textContent = o.textContent;
      b.setAttribute('role', 'menuitem');
      b.setAttribute('aria-current', o.value === sel.value);
      b.onclick = (e) => {
        e.stopPropagation();
        sel.value = o.value;
        sel.dispatchEvent(new Event('change', { bubbles: true }));
        label();
        close();
      };
      menu.append(b);
    }
  }
  function close() {
    menu.hidden = true;
    tog.setAttribute('aria-expanded', 'false');
  }
  tog.onclick = (e) => {
    e.stopPropagation();
    if (menu.hidden) {
      build();
      menu.hidden = false;
      tog.setAttribute('aria-expanded', 'true');
    } else close();
  };
  document.addEventListener('pointerdown', (e) => {
    if (!wrap.contains(e.target)) close();
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') close();
  });
  sel.addEventListener('change', label);
  setInterval(label, 400);
  label();
})();

// After any UI click, give keyboard control back to the 3D view.
document.querySelectorAll('.view-switch button,.view-switch select').forEach((el) => {
  el.addEventListener('change', () => setTimeout(() => canvas.focus(), 0));
  el.addEventListener('click', () => setTimeout(() => canvas.focus(), 0));
});
