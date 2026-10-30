'use strict';
// Dependency-free GLB 2 renderer for this Blender export. No external network requests.
const canvas=document.querySelector('#view'),gl=canvas.getContext('webgl2',{antialias:true,alpha:false});
const $=s=>document.querySelector(s);let draws=[],ready=false,center=[11.5,1,-16.8],yaw=.10,pitch=1.04,distance=51,drag=null,lastVP;
if(new URLSearchParams(location.search).get('view')==='display'){center=[11.3395,1.2,-14.7283];yaw=.55;pitch=.72;distance=8}
if(new URLSearchParams(location.search).get('view')==='service'){center=[18.3,1,-17.6];yaw=.45;pitch=1.08;distance=13}
if(new URLSearchParams(location.search).get('view')==='workstations'){center=[19.8,1,-25.5];yaw=.35;pitch=.85;distance=10}
if(new URLSearchParams(location.search).get('view')==='console'){center=[15.75,1.2,-25];yaw=1.15;pitch=1.23;distance=8.5}
const I=()=>[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1];
function mul(a,b){let o=new Array(16).fill(0);for(let c=0;c<4;c++)for(let r=0;r<4;r++)for(let k=0;k<4;k++)o[c*4+r]+=a[k*4+r]*b[c*4+k];return o}
function transform(m,p){let x=[p[0],p[1],p[2],p[3]??1],o=[0,0,0,0];for(let r=0;r<4;r++)for(let k=0;k<4;k++)o[r]+=m[k*4+r]*x[k];return o}
const sub=(a,b)=>a.map((x,i)=>x-b[i]),cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],norm=a=>{let d=Math.hypot(...a)||1;return a.map(x=>x/d)},dot=(a,b)=>a.reduce((n,x,i)=>n+x*b[i],0);
function inverse(m){let rows=Array.from({length:4},(_,r)=>[...Array.from({length:4},(_,c)=>m[c*4+r]),...Array.from({length:4},(_,c)=>+(c===r))]);for(let c=0;c<4;c++){let k=c;for(let r=c+1;r<4;r++)if(Math.abs(rows[r][c])>Math.abs(rows[k][c]))k=r;[rows[k],rows[c]]=[rows[c],rows[k]];let d=rows[c][c];if(Math.abs(d)<1e-12)return I();rows[c]=rows[c].map(x=>x/d);for(let r=0;r<4;r++)if(r!==c){let q=rows[r][c];rows[r]=rows[r].map((x,i)=>x-q*rows[c][i])}}return Array.from({length:16},(_,i)=>rows[i%4][4+Math.floor(i/4)])}
function nodeMatrix(n){if(n.matrix)return n.matrix;let [x,y,z,w]=n.rotation||[0,0,0,1],s=n.scale||[1,1,1],t=n.translation||[0,0,0];return [(1-2*y*y-2*z*z)*s[0],(2*x*y+2*z*w)*s[0],(2*x*z-2*y*w)*s[0],0,(2*x*y-2*z*w)*s[1],(1-2*x*x-2*z*z)*s[1],(2*y*z+2*x*w)*s[1],0,(2*x*z+2*y*w)*s[2],(2*y*z-2*x*w)*s[2],(1-2*x*x-2*y*y)*s[2],0,...t,1]}
function shader(type,source){let s=gl.createShader(type);gl.shaderSource(s,source);gl.compileShader(s);if(!gl.getShaderParameter(s,gl.COMPILE_STATUS))throw Error(gl.getShaderInfoLog(s));return s}
let nightMode=new URLSearchParams(location.search).get('mode')==='night',dynamicTimer;const automaticDoors=new Map(),businessScreens=[];let presentationImages=[];
let program,U={},shadowProgram,shadowU={},shadowFbo,shadowTexture,shadowVP,lastShadow='',whiteTexture;
function look(eye,target){let z=norm(sub(eye,target)),x=norm(cross([0,1,0],z)),y=cross(z,x);return [x[0],y[0],z[0],0,x[1],y[1],z[1],0,x[2],y[2],z[2],0,-dot(x,eye),-dot(y,eye),-dot(z,eye),1]}
function ortho(l,r,b,t,n,f){return [2/(r-l),0,0,0,0,2/(t-b),0,0,0,0,-2/(f-n),0,-(r+l)/(r-l),-(t+b)/(t-b),-(f+n)/(f-n),1]}
function setup(){
 if(!gl)throw Error('WebGL 2 is unavailable. Enable hardware acceleration in your browser.');
 program=gl.createProgram();
 gl.attachShader(program,shader(gl.VERTEX_SHADER,`#version 300 es
 layout(location=0) in vec3 position;layout(location=1) in vec3 normal;layout(location=2) in vec2 uv;uniform mat4 vp;out vec3 P;out vec3 N;out vec2 UV;void main(){P=position;N=normal;UV=uv;gl_Position=vp*vec4(position,1.);}`));
 gl.attachShader(program,shader(gl.FRAGMENT_SHADER,`#version 300 es
 precision highp float;in vec3 P;in vec3 N;in vec2 UV;uniform vec4 color;uniform float cutoff;uniform float alphaTest;uniform bool highlight;uniform bool textured;uniform sampler2D baseMap;uniform sampler2D shadowMap;uniform mat4 shadowMatrix;uniform vec3 emission;uniform bool emissionMapped;uniform bool interior;uniform bool night;uniform bool clearGlass;out vec4 outColor;
 float shadowAmount(vec3 n){vec4 q=shadowMatrix*vec4(P,1.);vec3 c=q.xyz/q.w*.5+.5;if(c.x<0.||c.x>1.||c.y<0.||c.y>1.||c.z>1.)return 1.;float bias=max(.0009,.0018*(1.-dot(n,normalize(vec3(-21.,40.,25.)))));float sum=0.;for(int x=-1;x<=1;x++)for(int y=-1;y<=1;y++){float d=texture(shadowMap,c.xy+vec2(x,y)/2048.).r;sum+=c.z-bias<=d?1.:.0;}return sum/9.;}
 void main(){if(P.y>cutoff)discard;vec3 n=normalize(N);vec4 texel=textured?texture(baseMap,UV):vec4(1.);if(color.a*texel.a<alphaTest)discard;vec3 albedo=color.rgb*texel.rgb;float shadow=shadowAmount(n);float direct=max(dot(n,normalize(vec3(-21.,40.,25.))),0.);float fill=max(dot(n,normalize(vec3(1.,.55,-.3))),0.);float pool=0.;vec2 lamps[6]=vec2[6](vec2(6.4,-13.4),vec2(11.3,-14.7),vec2(16.4,-5.9),vec2(20.1,-19.45),vec2(20.05,-26.5),vec2(21.3,-14.6));for(int i=0;i<6;i++){float d=length(P.xz-lamps[i]);pool+=1./(1.+d*d*.22);}vec3 light=night?(vec3(.24,.22,.19)+vec3(.42,.30,.17)*min(pool,1.4)+vec3(.10,.11,.13)*fill+vec3(.16,.15,.13)*direct*shadow):((interior?vec3(.57,.55,.51):vec3(.42,.43,.43))+vec3(.55,.49,.40)*direct*shadow+vec3(.12,.14,.17)*fill);vec3 c=albedo*light+emission*(night?1.25:.42)*(emissionMapped?texel.rgb:vec3(1.));if(clearGlass)c=vec3(.76,.86,.87);if(highlight)c=mix(c,vec3(.3,1.,.82),.5);c=vec3(1.)-exp(-c*1.5);outColor=vec4(pow(c,vec3(1./2.2)),color.a*texel.a);}`));
 gl.linkProgram(program);if(!gl.getProgramParameter(program,gl.LINK_STATUS))throw Error(gl.getProgramInfoLog(program));gl.useProgram(program);
 for(let n of ['vp','color','cutoff','alphaTest','highlight','textured','baseMap','shadowMap','shadowMatrix','emission','emissionMapped','interior','night','clearGlass'])U[n]=gl.getUniformLocation(program,n);
 gl.uniform1i(U.baseMap,0);gl.uniform1i(U.shadowMap,1);
 whiteTexture=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,whiteTexture);gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,1,1,0,gl.RGBA,gl.UNSIGNED_BYTE,new Uint8Array([255,255,255,255]));gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR);
 shadowProgram=gl.createProgram();gl.attachShader(shadowProgram,shader(gl.VERTEX_SHADER,`#version 300 es
 layout(location=0) in vec3 position;uniform mat4 vp;out float height;void main(){height=position.y;gl_Position=vp*vec4(position,1.);}`));gl.attachShader(shadowProgram,shader(gl.FRAGMENT_SHADER,`#version 300 es
 precision highp float;in float height;uniform float cutoff;void main(){if(height>cutoff)discard;}`));gl.linkProgram(shadowProgram);for(let n of ['vp','cutoff'])shadowU[n]=gl.getUniformLocation(shadowProgram,n);
 shadowTexture=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,shadowTexture);gl.texImage2D(gl.TEXTURE_2D,0,gl.DEPTH_COMPONENT24,2048,2048,0,gl.DEPTH_COMPONENT,gl.UNSIGNED_INT,null);for(let n of [gl.TEXTURE_MIN_FILTER,gl.TEXTURE_MAG_FILTER])gl.texParameteri(gl.TEXTURE_2D,n,gl.NEAREST);for(let n of [gl.TEXTURE_WRAP_S,gl.TEXTURE_WRAP_T])gl.texParameteri(gl.TEXTURE_2D,n,gl.CLAMP_TO_EDGE);
 shadowFbo=gl.createFramebuffer();gl.bindFramebuffer(gl.FRAMEBUFFER,shadowFbo);gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.DEPTH_ATTACHMENT,gl.TEXTURE_2D,shadowTexture,0);gl.drawBuffers([gl.NONE]);gl.readBuffer(gl.NONE);if(gl.checkFramebufferStatus(gl.FRAMEBUFFER)!==gl.FRAMEBUFFER_COMPLETE)throw Error('Shadow framebuffer unavailable');gl.bindFramebuffer(gl.FRAMEBUFFER,null);
 shadowVP=mul(ortho(-27,27,-27,27,.1,110),look([-10,40,8],[11,0,-17]));gl.enable(gl.DEPTH_TEST);gl.enable(gl.BLEND);gl.depthFunc(gl.LEQUAL);gl.blendFunc(gl.SRC_ALPHA,gl.ONE_MINUS_SRC_ALPHA);
}
async function load(){const statusEl=$('#status');
 statusEl.textContent='Downloading office model...';
 const response=await fetch('marketing_office.glb');
 if(!response.ok)throw Error('GLB failed to load: '+response.status);
 let buf;
 const contentLength=response.headers.get('content-length');
 if(contentLength&&response.body){
  const total=parseInt(contentLength,10);
  let loaded=0;
  const reader=response.body.getReader();
  const chunks=[];
  while(true){
   const {done,value}=await reader.read();
   if(done)break;
   chunks.push(value);
   loaded+=value.length;
   if(total){
    const pct=Math.round((loaded/total)*100);
    statusEl.textContent=`Downloading office model... ${pct}%`;
   }
  }
  const all=new Uint8Array(loaded);
  let pos=0;
  for(const c of chunks){all.set(c,pos);pos+=c.length}
  buf=all.buffer;
 }else{
  buf=await response.arrayBuffer();
 }
 statusEl.textContent='Loading scene...';
 let dv=new DataView(buf);if(dv.getUint32(0,true)!==0x46546c67)throw Error('Invalid GLB');let json,bin;for(let off=12;off<buf.byteLength;){let len=dv.getUint32(off,true),type=dv.getUint32(off+4,true);if(type===0x4e4f534a)json=JSON.parse(new TextDecoder().decode(new Uint8Array(buf,off+8,len)));if(type===0x004e4942)bin=new DataView(buf,off+8,len);off+=8+len}
const textures=[];const retainedImages=new Map();
for(let info of json.textures||[]){let im=json.images[info.source],view=json.bufferViews[im.bufferView],bytes=new Uint8Array(binaryBuffer(bin), (view.byteOffset||0),view.byteLength);let bitmap=await createImageBitmap(new Blob([bytes],{type:im.mimeType}));let texture=gl.createTexture();gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,texture);gl.texImage2D(gl.TEXTURE_2D,0,gl.SRGB8_ALPHA8,gl.RGBA,gl.UNSIGNED_BYTE,bitmap);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR_MIPMAP_LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.REPEAT);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.REPEAT);gl.generateMipmap(gl.TEXTURE_2D);textures.push(texture);const sourceName=json.materials.filter(m=>m.pbrMetallicRoughness?.baseColorTexture?.index===textures.length-1).map(m=>m.name).join(' ');if(/project visualisation print/.test(sourceName))retainedImages.set(sourceName,bitmap);else bitmap.close();}
function binaryBuffer(view){return view.buffer.slice(view.byteOffset,view.byteOffset+view.byteLength)}
function read(id){let a=json.accessors[id],v=json.bufferViews[a.bufferView],n={SCALAR:1,VEC2:2,VEC3:3,VEC4:4}[a.type],bytes={5121:1,5123:2,5125:4,5126:4}[a.componentType],stride=v.byteStride||n*bytes,start=(v.byteOffset||0)+(a.byteOffset||0),out=[];for(let i=0;i<a.count;i++)for(let j=0;j<n;j++){let off=start+i*stride+j*bytes;out.push(a.componentType===5126?bin.getFloat32(off,true):a.componentType===5125?bin.getUint32(off,true):a.componentType===5123?bin.getUint16(off,true):bin.getUint8(off))}return out}
function visit(id,parent){let n=json.nodes[id],world=mul(parent,nodeMatrix(n));if(n.mesh!==undefined)for(let p of json.meshes[n.mesh].primitives){if(p.mode!==undefined&&p.mode!==4)continue;let pos=read(p.attributes.POSITION),normals=p.attributes.NORMAL!==undefined?read(p.attributes.NORMAL):null,uv=p.attributes.TEXCOORD_0!==undefined?read(p.attributes.TEXCOORD_0):null,invWorld=inverse(world),idx=p.indices!==undefined?read(p.indices):Array.from({length:pos.length/3},(_,i)=>i),data=[],min=[Infinity,Infinity,Infinity],max=[-Infinity,-Infinity,-Infinity];for(let i=0;i<idx.length;i+=3){let tri=idx.slice(i,i+3).map(v=>transform(world,pos.slice(v*3,v*3+3)).slice(0,3)),normal=norm(cross(sub(tri[1],tri[0]),sub(tri[2],tri[0])));for(let ti=0;ti<tri.length;ti++){let v=tri[ti],index=idx[i+ti];for(let a=0;a<3;a++){min[a]=Math.min(min[a],v[a]);max[a]=Math.max(max[a],v[a])}let nn=normal;if(normals){let nx=normals[index*3],ny=normals[index*3+1],nz=normals[index*3+2];nn=norm([invWorld[0]*nx+invWorld[1]*ny+invWorld[2]*nz,invWorld[4]*nx+invWorld[5]*ny+invWorld[6]*nz,invWorld[8]*nx+invWorld[9]*ny+invWorld[10]*nz]);}data.push(...v,...nn,...(uv?uv.slice(index*2,index*2+2):[0,0]))}}let material=json.materials?.[p.material],color=[...(material?.pbrMetallicRoughness?.baseColorFactor||[1,1,1,1])];if(material?.name==='Low iron clear glass'){color=[.91,.97,.97,.035]}draws.push({emissionMapped:material?.emissiveTexture!==undefined&&material?.pbrMetallicRoughness?.baseColorTexture!==undefined&&json.textures[material.emissiveTexture.index].source===json.textures[material.pbrMetallicRoughness.baseColorTexture.index].source,alphaTest:material?.alphaMode==='MASK'?(material.alphaCutoff??.5):0,name:n.name||'Object',data,count:data.length/8,texture:textures[material?.pbrMetallicRoughness?.baseColorTexture?.index],emission:(material?.emissiveFactor||[0,0,0]).map(x=>x*(material?.extensions?.KHR_materials_emissive_strength?.emissiveStrength||1)),cuttable:['Structure','Partitions'].includes(n.extras?.category)&&!/^Structural column|^Charcoal column/.test(n.name),color,min,max,extras:n.extras||{},ceiling:/^Ceiling/.test(n.name)||!!n.extras?.eye_ceiling_fixture,glass:color[3]<.99,architectural:['Structure','Partitions','Glazing','Doors'].includes(n.extras?.category),door:/^(D[123]|GD[12]|GL[123]|V1)-/.test(n.name)})}for(let ch of n.children||[])visit(ch,world)}
for(let n of json.scenes[json.scene||0].nodes)visit(n,I());const sourceParts=draws.length,groups=new Map();
for(const d of draws){
 if(d.extras.auto_door_id){const id=d.extras.auto_door_id;let rig=automaticDoors.get(id);if(!rig){rig={id,hinge:d.extras.auto_door_hinge,center:d.extras.auto_door_center,angle:d.extras.auto_door_angle,amount:0,target:0,lastNear:-Infinity,parts:[],segments:[]};automaticDoors.set(id,rig)}rig.parts.push(d);d.rig=rig;d.original=new Float32Array(d.data);const begin=collisionSegments.length;captureCollision(d);rig.segments.push(...collisionSegments.splice(begin));}
 else captureCollision(d);
}
presentationImages=[...retainedImages.values()];
for(const d of draws){d.depthBias=/^Charcoal column cap/.test(d.name)?-4:/^Structural column/.test(d.name)?-2:0;const key=JSON.stringify([d.ceiling,(d.glass||d.rig||d.extras.business_screen!==undefined)?d.name:null,d.depthBias,d.color,d.emission,d.emissionMapped,d.alphaTest,d.texture?textures.indexOf(d.texture):-1,d.glass]);let g=groups.get(key);if(!g){g={...d,chunks:[],count:0};groups.set(key,g)}g.chunks.push(d.data);g.count+=d.count;for(let i=0;i<3;i++){g.min[i]=Math.min(g.min[i],d.min[i]);g.max[i]=Math.max(g.max[i],d.max[i])}}
draws=[...groups.values()];for(const d of draws){const packed=new Float32Array(d.count*8);let offset=0;for(const chunk of d.chunks){packed.set(chunk,offset);offset+=chunk.length}delete d.chunks;delete d.data;d.vao=gl.createVertexArray();gl.bindVertexArray(d.vao);const buffer=gl.createBuffer();d.buffer=buffer;gl.bindBuffer(gl.ARRAY_BUFFER,buffer);gl.bufferData(gl.ARRAY_BUFFER,packed,d.rig?gl.DYNAMIC_DRAW:gl.STATIC_DRAW);for(const [a,size,offset] of [[0,3,0],[1,3,12],[2,2,24]]){gl.enableVertexAttribArray(a);gl.vertexAttribPointer(a,size,gl.FLOAT,false,32,offset)}}
for(const d of draws){if(d.rig){const rig=d.rig;rig.parts=rig.parts.filter(p=>p.name!==d.name);rig.parts.push(d)}if(d.extras.business_screen!==undefined)createBusinessScreen(d)}
ready=true;window.officeViewer={ready:true,objects:sourceParts,drawCalls:draws.length,textures:textures.length,triangles:draws.reduce((n,d)=>n+d.count/3,0),bounds:draws.reduce((b,d)=>[b[0].map((x,i)=>Math.min(x,d.min[i])),b[1].map((x,i)=>Math.max(x,d.max[i]))],[[Infinity,Infinity,Infinity],[-Infinity,-Infinity,-Infinity]])};$('#status').textContent=eyeMode?'Eye level • '+eyeStations[Number($('#viewpoint').value)||0].name:'Office ready • Drag to explore';requestAnimationFrame(render)}
function visible(d){return !d.ceiling||eyeMode}
// Orthographic zoom changes framing only. Keep the eye outside the complete
// scene and derive depth planes from all eight world-bound corners on every view.
function cameraProjection(bounds,focus,azimuth,elevation,zoom,width,height){
 const midpoint=bounds[0].map((v,i)=>(v+bounds[1][i])/2);
 const radius=Math.hypot(...sub(bounds[1],bounds[0]))/2;
 const eyeDistance=radius+Math.hypot(...sub(focus,midpoint))+10;
 const cp=Math.cos(elevation),eye=[focus[0]+eyeDistance*cp*Math.sin(azimuth),focus[1]+eyeDistance*Math.sin(elevation),focus[2]+eyeDistance*cp*Math.cos(azimuth)];
 const view=look(eye,focus);let minDepth=Infinity,maxDepth=-Infinity;
 for(let i=0;i<8;i++){const corner=[bounds[(i>>0)&1][0],bounds[(i>>1)&1][1],bounds[(i>>2)&1][2]];const depth=-transform(view,corner)[2];minDepth=Math.min(minDepth,depth);maxDepth=Math.max(maxDepth,depth)}
 const near=Math.max(.05,minDepth-2),far=Math.max(near+1,maxDepth+2);
 const aspect=Math.max(1,width)/Math.max(1,height),extent=zoom*.35*Math.max(1,.80/aspect);
 return {matrix:mul(ortho(-extent*aspect,extent*aspect,-extent,extent,near,far),view),near,far,eyeDistance,minDepth,maxDepth};
}
function viewProjection(){
 if(eyeMode)return eyeProjection(canvas.width,canvas.height);
 const result=cameraProjection(window.officeViewer.bounds,center,yaw,pitch,distance,canvas.width,canvas.height);
 window.officeViewer.camera={near:result.near,far:result.far,minDepth:result.minDepth,maxDepth:result.maxDepth,zoom:distance};
 return result.matrix;
}
function cutoff(d){return 99}
let framePending=false;function invalidate(){if(!framePending&&ready){framePending=true;requestAnimationFrame(render)}}
function render(now=performance.now()){framePending=false;const dt=Math.min(.05,(now-lastWalkTime)/1000||.016);lastWalkTime=now;updateAutomaticDoors(now,dt);updateBusinessScreens(now);if(eyeMode&&moveKeys.size){let forward=(moveKeys.has('KeyW')?1:0)-(moveKeys.has('KeyS')?1:0),side=(moveKeys.has('KeyD')?1:0)-(moveKeys.has('KeyA')?1:0);const n=Math.hypot(forward,side)||1,speed=walkFast?2.6:1.5;moveEye(forward/n*speed*dt,side/n*speed*dt)}
 let ratio=Math.min(devicePixelRatio,1.5),w=Math.round(canvas.clientWidth*ratio),h=Math.round(canvas.clientHeight*ratio);if(canvas.width!==w||canvas.height!==h){canvas.width=w;canvas.height=h}
 let signature=eyeMode?'eye':'overview';
 if(signature!==lastShadow){lastShadow=signature;gl.bindFramebuffer(gl.FRAMEBUFFER,shadowFbo);gl.viewport(0,0,2048,2048);gl.depthMask(true);gl.clear(gl.DEPTH_BUFFER_BIT);gl.enable(gl.POLYGON_OFFSET_FILL);gl.polygonOffset(2,4);gl.useProgram(shadowProgram);gl.uniformMatrix4fv(shadowU.vp,false,new Float32Array(shadowVP));for(let d of draws){if(d.glass||!visible(d))continue;gl.bindVertexArray(d.vao);gl.uniform1f(shadowU.cutoff,cutoff(d));gl.drawArrays(gl.TRIANGLES,0,d.count)}gl.disable(gl.POLYGON_OFFSET_FILL);gl.bindFramebuffer(gl.FRAMEBUFFER,null)}
 gl.useProgram(program);gl.uniform1i(U.interior,eyeMode);gl.uniform1i(U.night,nightMode);gl.viewport(0,0,w,h);if(eyeMode){if(nightMode)gl.clearColor(.035,.045,.075,1);else gl.clearColor(.68,.77,.83,1);}else gl.clearColor(.095,.12,.15,1);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);lastVP=viewProjection();gl.uniformMatrix4fv(U.vp,false,new Float32Array(lastVP));gl.uniformMatrix4fv(U.shadowMatrix,false,new Float32Array(shadowVP));gl.activeTexture(gl.TEXTURE1);gl.bindTexture(gl.TEXTURE_2D,shadowTexture);
 const ordered=draws.filter(d=>!d.glass).concat(draws.filter(d=>d.glass).sort((a,b)=>{const pa=transform(lastVP,a.min.map((v,i)=>(v+a.max[i])/2)),pb=transform(lastVP,b.min.map((v,i)=>(v+b.max[i])/2));return pb[2]-pa[2]}));
 for(let transparent of [false,true]){gl.depthMask(!transparent);for(let d of ordered){if(d.glass!==transparent||!visible(d))continue;gl.bindVertexArray(d.vao);if(d.depthBias){gl.enable(gl.POLYGON_OFFSET_FILL);gl.polygonOffset(-1,d.depthBias)}else gl.disable(gl.POLYGON_OFFSET_FILL);gl.uniform1i(U.clearGlass,d.glass);gl.uniform4fv(U.color,d.color);gl.uniform3fv(U.emission,d.emission);gl.uniform1i(U.emissionMapped,!!d.emissionMapped);gl.uniform1f(U.cutoff,cutoff(d));gl.uniform1f(U.alphaTest,d.alphaTest);gl.uniform1i(U.highlight,false);gl.uniform1i(U.textured,!!d.texture);gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,d.texture||whiteTexture);gl.drawArrays(gl.TRIANGLES,0,d.count)}}gl.disable(gl.POLYGON_OFFSET_FILL);gl.depthMask(true);if(eyeMode&&(moveKeys.size||[...automaticDoors.values()].some(r=>Math.abs(r.amount-r.target)>.001)))invalidate();else if(businessScreens.length&&!document.hidden){clearTimeout(dynamicTimer);dynamicTimer=setTimeout(invalidate,125)}
}
// Public-area visitor stations. Heights are in metres, glTF Y-up.
let eyeMode=false,walkYaw=0,walkPitch=0,walkPosition=[8.4,1.6,-9.5],walkFast=false,lastWalkTime=0;
const moveKeys=new Set(),collisionSegments=[],collisionHulls=[];
const eyeStations=[
 {name:'Reception',position:[8.4,1.6,-9.5],target:[11.33,1.80,-7.20]},
 {name:'Project model',position:[8.8,1.6,-12],target:[11.34,1.45,-14.73]},
 {name:'Lounge',position:[3,1.6,-14.3],target:[1.25,1.65,-13.49]},
 {name:'Meeting',position:[18.2,1.6,-7.45],target:[12.448,1.6,-5.8]},
 {name:'Meeting doorway',position:[12.817,1.6,-9.9],target:[12.817,1.6,-8.1]},
 {name:'Workstations',position:[20,1.6,-23.85],target:[20,1.4,-26.8]},
 {name:'Storage',position:[19.2,1.6,-31.95],target:[19.2,1.4,-33.3]}
];
const walkOutline=[[715,54],[951,54],[951,1127],[831,1092],[615,999],[301,824],[244,789],[244,596],[715,596]].map(([x,y])=>[(x-244)*7.690/236,-(1127-y)*7.690/236]);
function pointInPolygon(p,poly){let inside=false;for(let i=0,j=poly.length-1;i<poly.length;j=i++){const a=poly[i],b=poly[j];if((a[1]>p[1])!==(b[1]>p[1])&&p[0]<(b[0]-a[0])*(p[1]-a[1])/(b[1]-a[1])+a[0])inside=!inside}return inside}
function segmentDistance(p,a,b){const dx=b[0]-a[0],dy=b[1]-a[1],l=dx*dx+dy*dy,t=l?Math.max(0,Math.min(1,((p[0]-a[0])*dx+(p[1]-a[1])*dy)/l)):0;return Math.hypot(p[0]-a[0]-t*dx,p[1]-a[1]-t*dy)}
function convexHull(points){points.sort((a,b)=>a[0]-b[0]||a[1]-b[1]);const cross2=(a,b,c)=>(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]);const lower=[],upper=[];for(const p of points){while(lower.length>1&&cross2(lower.at(-2),lower.at(-1),p)<=0)lower.pop();lower.push(p)}for(let i=points.length-1;i>=0;i--){const p=points[i];while(upper.length>1&&cross2(upper.at(-2),upper.at(-1),p)<=0)upper.pop();upper.push(p)}lower.pop();upper.pop();return lower.concat(upper)}
function captureCollision(d){
 if(d.ceiling||d.max[1]<.25||d.min[1]>1.45||d.extras.capital_crest_display||d.extras.gallery_decor||d.extras.console_luxury_decor)return;
 if(d.architectural){
  for(let i=0;i<d.data.length;i+=24){const tri=[d.data.slice(i,i+3),d.data.slice(i+8,i+11),d.data.slice(i+16,i+19)],points=[];
   for(let j=0;j<3;j++){const a=tri[j],b=tri[(j+1)%3];if((a[1]<=1&&b[1]>1)||(b[1]<=1&&a[1]>1)){const t=(1-a[1])/(b[1]-a[1]);points.push([a[0]+t*(b[0]-a[0]),a[2]+t*(b[2]-a[2])])}}
   if(points.length===2&&Math.hypot(points[0][0]-points[1][0],points[0][1]-points[1][1])>.00001)collisionSegments.push(points);
  }
 }else{
  const points=[];for(let i=0;i<d.data.length;i+=8)points.push([d.data[i],d.data[i+2]]);
  const hull=convexHull(points);if(hull.length>2)collisionHulls.push({hull,min:[d.min[0],d.min[2]],max:[d.max[0],d.max[2]]});
 }
}
function entranceApproach(x,z){const r=automaticDoors.get('GD2-08');if(!r)return false;const dx=r.center[0]-r.hinge[0],dz=r.center[2]-r.hinge[2],length=Math.hypot(dx,dz),ux=dx/length,uz=dz/length,px=x-r.center[0],pz=z-r.center[2];return Math.abs(px*ux+pz*uz)<.60&&Math.abs(-px*uz+pz*ux)<1.25}
function canStand(x,z,radius=.19){
 const p=[x,z];for(const rig of automaticDoors.values()){for(const [a,b] of rig.segments){const aa=doorPoint(rig,a,rig.amount),bb=doorPoint(rig,b,rig.amount);if(segmentDistance(p,aa,bb)<radius)return false;}}for(const offset of [[0,0],[radius,0],[-radius,0],[0,radius],[0,-radius]])if(!pointInPolygon([x+offset[0],z+offset[1]],walkOutline)&&!entranceApproach(x+offset[0],z+offset[1]))return false;
 for(const [a,b] of collisionSegments)if(segmentDistance(p,a,b)<radius)return false;
 for(const {hull,min,max} of collisionHulls){if(x<min[0]-radius||x>max[0]+radius||z<min[1]-radius||z>max[1]+radius)continue;if(pointInPolygon(p,hull))return false;for(let i=0;i<hull.length;i++)if(segmentDistance(p,hull[i],hull[(i+1)%hull.length])<radius)return false}
 return true;
}
function moveEye(forward,side){const dx=Math.sin(walkYaw)*forward+Math.cos(walkYaw)*side,dz=-Math.cos(walkYaw)*forward+Math.sin(walkYaw)*side,steps=Math.max(1,Math.ceil(Math.hypot(dx,dz)/.055));for(let i=0;i<steps;i++){const nx=walkPosition[0]+dx/steps,nz=walkPosition[2]+dz/steps;if(canStand(nx,walkPosition[2]))walkPosition[0]=nx;if(canStand(walkPosition[0],nz))walkPosition[2]=nz}}
function perspective(fov,aspect,near,far){const f=1/Math.tan(fov/2);return [f/aspect,0,0,0,0,f,0,0,0,0,(far+near)/(near-far),-1,0,0,2*far*near/(near-far),0]}
function eyeProjection(width,height){const cp=Math.cos(walkPitch),target=[walkPosition[0]+Math.sin(walkYaw)*cp,walkPosition[1]+Math.sin(walkPitch),walkPosition[2]-Math.cos(walkYaw)*cp];return mul(perspective(Math.PI/3,Math.max(1,width)/Math.max(1,height),.08,150),look(walkPosition,target))}
function selectStation(index){const station=eyeStations[index]||eyeStations[0];walkPosition=[...station.position];const d=sub(station.target,station.position);walkYaw=Math.atan2(d[0],-d[2]);walkPitch=Math.atan2(d[1],Math.hypot(d[0],d[2]));moveKeys.clear();$('#status').textContent='Eye level • '+station.name;invalidate()}
function setEyeMode(enabled){eyeMode=enabled;moveKeys.clear();drag=null;document.body.classList.toggle('eye-level',enabled);$('#viewpoint').hidden=!enabled;$('#eye-level').setAttribute('aria-pressed',enabled);$('#overview').setAttribute('aria-pressed',!enabled);$('footer').textContent=enabled?'Drag to look • WASD to move • Wheel to step forward / back':'Drag to orbit • Wheel to zoom • Right-drag / Shift-drag to pan';if(enabled)selectStation(Number($('#viewpoint').value)||0);else{$('#status').textContent='Office ready • Drag to explore';center=[11.5,1,-16.8];yaw=.1;pitch=1.04;distance=51}canvas.focus();invalidate()}
canvas.oncontextmenu=e=>e.preventDefault();
canvas.onpointerdown=e=>{canvas.focus();drag={x:e.clientX,y:e.clientY,pan:e.button===2||e.shiftKey};canvas.setPointerCapture(e.pointerId)};
canvas.onpointermove=e=>{if(!drag)return;const dx=e.clientX-drag.x,dy=e.clientY-drag.y;if(eyeMode){walkYaw+=dx*.004;walkPitch=Math.max(-.9,Math.min(.9,walkPitch-dy*.004))}else if(drag.pan){const k=distance*.0008;center[0]-=k*(dx*Math.cos(yaw)+dy*Math.sin(yaw));center[2]+=k*(dx*Math.sin(yaw)-dy*Math.cos(yaw))}else{yaw-=dx*.006;pitch=Math.max(.60,Math.min(1.565,pitch+dy*.006))}drag.x=e.clientX;drag.y=e.clientY;invalidate()};
canvas.onpointerup=canvas.onpointercancel=canvas.onlostpointercapture=()=>{drag=null};
canvas.onwheel=e=>{e.preventDefault();if(eyeMode)moveEye(Math.max(-.65,Math.min(.65,-e.deltaY*.003)),0);else distance=Math.max(4,Math.min(56,distance*Math.exp(e.deltaY*.001)));invalidate()};
canvas.tabIndex=0;canvas.setAttribute('aria-label','Office 3D view');
canvas.onkeydown=e=>{
 if(e.ctrlKey||e.metaKey||e.altKey)return;
 if(e.key.toLowerCase()==='e'){if(e.repeat)return;setEyeMode(!eyeMode);e.preventDefault();return}
 if(e.key==='Home'){setEyeMode(false);e.preventDefault();return}
 if(eyeMode){if(['KeyW','KeyA','KeyS','KeyD'].includes(e.code)){if(!moveKeys.has(e.code))moveEye(e.code==='KeyW'?.07:e.code==='KeyS'?-.07:0,e.code==='KeyD'?.07:e.code==='KeyA'?-.07:0);moveKeys.add(e.code);e.preventDefault();invalidate();return}if(e.code.startsWith('Shift')){walkFast=true;return}if(e.key==='ArrowLeft')walkYaw-=.09;else if(e.key==='ArrowRight')walkYaw+=.09;else if(e.key==='ArrowUp')walkPitch=Math.min(.9,walkPitch+.06);else if(e.key==='ArrowDown')walkPitch=Math.max(-.9,walkPitch-.06);else return}
 else{if(e.key==='ArrowLeft')yaw-=.16;else if(e.key==='ArrowRight')yaw+=.16;else if(e.key==='ArrowUp')pitch=Math.min(1.565,pitch+.12);else if(e.key==='ArrowDown')pitch=Math.max(.60,pitch-.12);else if(e.key==='+'||e.key==='=')distance=Math.max(4,distance*.9);else if(e.key==='-')distance=Math.min(56,distance/.9);else return}e.preventDefault();invalidate();
};
window.addEventListener('keyup',e=>{moveKeys.delete(e.code);if(e.code.startsWith('Shift'))walkFast=false});
window.addEventListener('blur',()=>{moveKeys.clear();walkFast=false;drag=null});window.addEventListener('resize',invalidate);
$('#day-night').onclick=()=>{nightMode=!nightMode;$('#day-night').textContent=nightMode?'Day':'Night';$('#day-night').setAttribute('aria-pressed',nightMode);invalidate()};$('#day-night').textContent=nightMode?'Day':'Night';$('#day-night').setAttribute('aria-pressed',nightMode);
$('#overview').onclick=()=>setEyeMode(false);$('#eye-level').onclick=()=>setEyeMode(true);$('#viewpoint').onchange=()=>{selectStation(Number($('#viewpoint').value));canvas.focus()};
if(new URLSearchParams(location.search).get('view')==='eye'){
 const requested=new URLSearchParams(location.search).get('spot'),index={reception:0,model:1,lounge:2,meeting:3,doors:4,workstations:5,storage:6}[requested]??1;$('#viewpoint').value=String(index);setEyeMode(true);
}

// Door sensors use distance to the opening, from either side, with a hold-open zone.
function doorPoint(r,p,amount){const a=r.angle*amount,c=Math.cos(a),s=Math.sin(a),x=p[0]-r.hinge[0],z=p[1]-r.hinge[2];return [r.hinge[0]+c*x+s*z,r.hinge[2]-s*x+c*z]}
function updateAutomaticDoors(now,dt){
 for(const r of automaticDoors.values()){
  const near=eyeMode&&Math.hypot(walkPosition[0]-r.center[0],walkPosition[2]-r.center[2])<1.65;
  if(near)r.lastNear=now;
  r.target=eyeMode&&(near||now-r.lastNear<1800)?1:0;
  const next=Math.max(0,Math.min(1,r.amount+Math.sign(r.target-r.amount)*Math.min(Math.abs(r.target-r.amount),dt*1.8)));
  if(Math.abs(next-r.amount)<.00001)continue;r.amount=next;
  const angle=r.angle*next,c=Math.cos(angle),s=Math.sin(angle);
  for(const d of r.parts){const data=new Float32Array(d.original);d.min=[Infinity,Infinity,Infinity];d.max=[-Infinity,-Infinity,-Infinity];for(let i=0;i<data.length;i+=8){const x=data[i]-r.hinge[0],z=data[i+2]-r.hinge[2],nx=data[i+3],nz=data[i+5];data[i]=r.hinge[0]+c*x+s*z;data[i+2]=r.hinge[2]-s*x+c*z;data[i+3]=c*nx+s*nz;data[i+5]=-s*nx+c*nz;for(let k=0;k<3;k++){d.min[k]=Math.min(d.min[k],data[i+k]);d.max[k]=Math.max(d.max[k],data[i+k])}}gl.bindBuffer(gl.ARRAY_BUFFER,d.buffer);gl.bufferSubData(gl.ARRAY_BUFFER,0,data)}
  lastShadow='';
 }
}
function createBusinessScreen(d){
 const surface=document.createElement('canvas');surface.width=960;surface.height=540;
 const texture=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,texture);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.LINEAR);for(const side of [gl.TEXTURE_WRAP_S,gl.TEXTURE_WRAP_T])gl.texParameteri(gl.TEXTURE_2D,side,gl.CLAMP_TO_EDGE);
 d.texture=texture;d.color=[1,1,1,1];d.emission=[.65,.65,.65];d.emissionMapped=true;businessScreens.push({d,surface,ctx:surface.getContext('2d'),index:d.extras.business_screen,last:-Infinity});
}
function updateBusinessScreens(now){
 for(const screen of businessScreens){if(now-screen.last<120)continue;screen.last=now;
  const {ctx:c,surface,index}=screen,t=now/1000,slide=Math.floor(t/9+index)%3;
  c.fillStyle=['#101f2b','#1c2928','#27211c'][index];c.fillRect(0,0,960,540);
  c.fillStyle='#d4b276';c.font='20px sans-serif';c.fillText('CAPITAL CREST  /  PROJECT GALLERY',42,43);
  const titles=[['ARCHITECTURE IN FOCUS','A DISTINCTIVE ARRIVAL','THE PROJECT AT A GLANCE'],['MATERIALS & DETAIL','DESIGN CONVERSATIONS','CRAFTED EXPERIENCES'],['PROJECT PRESENTATION','SPACE TO COLLABORATE','EXPLORE THE DESIGN']];
  c.fillStyle='#f2eee5';c.font='bold 34px sans-serif';c.fillText(titles[index][slide],42,99);
  if(presentationImages.length){const im=presentationImages[(slide+index)%presentationImages.length];const iw=im.width,ih=im.height,w=610,h=w*ih/iw;c.save();c.beginPath();c.rect(315,132,610,335);c.clip();const zoom=1+.018*Math.sin(t*.3+index);c.translate(620,299);c.scale(zoom,zoom);c.drawImage(im,-w/2,-h/2,w,h);c.restore();}
  c.font='21px sans-serif';c.fillStyle='#d5c39f';const lines=[['ARCHITECTURE','ARRIVAL','SITE CONTEXT'],['STONE & OAK','BRONZE & GLASS','TEXTURE & LIGHT'],['DISCOVER','DISCUSS','EXPERIENCE']][index];
  lines.forEach((line,i)=>{c.fillStyle=i===slide?'#f3d391':'#93a6a8';c.fillText(line,42,180+i*66);c.fillStyle='#4e686e';c.fillRect(42,198+i*66,130+25*Math.sin(t*.6+i),3)});
  c.fillStyle='#8d9d9f';c.font='15px sans-serif';c.fillText('ILLUSTRATIVE DESIGN PRESENTATION',42,498);c.fillStyle='#e9c685';c.fillRect(42,518,876*((t%9)/9),3);
  gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,screen.d.texture);gl.texImage2D(gl.TEXTURE_2D,0,gl.SRGB8_ALPHA8,gl.RGBA,gl.UNSIGNED_BYTE,surface);
 }
}
document.addEventListener('visibilitychange',()=>{if(document.hidden)clearTimeout(dynamicTimer);else invalidate()});

try{setup();load().catch(fail)}catch(e){fail(e)}function fail(e){$('#error').hidden=false;$('#error').textContent=e.message+'  -  Start the local server as described in README.txt. Open http://localhost:8000/viewer/';$('#status').textContent='Viewer could not load';console.error(e)}