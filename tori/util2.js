let scrW = 0, scrH = 0;
let refresh = _=>_;
let drawCircle = _=>_;
let draw = _=>_;
let mouseContact = _=>_;
window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  scrW = 600;
  scrH = 600*5/8;

  const gl = cvs.getContext("webgl");
  gl.disable(gl.BLEND);
  gl.disable(gl.DEPTH_TEST);
  gl.disable(gl.CULL_FACE);
  gl.viewport(0,0,1200,450);
  gl.clearColor(1,1,1,1);

  const frameBuffer = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER,frameBuffer);
  const worldTexture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D,worldTexture);
  gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,scrW*2,scrH*2,0,gl.RGBA,gl.UNSIGNED_BYTE,null);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);
  gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.COLOR_ATTACHMENT0,gl.TEXTURE_2D,worldTexture,0);
  gl.bindFramebuffer(gl.FRAMEBUFFER,null);

  const verts = [-1,-1,-1,1,1,-1,1,1];
  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
  gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(verts),gl.STATIC_DRAW);

  const vsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    attribute vec2 position;
    varying vec2 coord;
    varying vec2 physCoord;
    uniform vec2 resolution;
    void main(void){
      coord = position;
      physCoord = (position*0.5+0.5) * resolution;
      gl_Position = vec4(position,0.,1.);
    }
  `;
  const fsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec2 coord;
    varying vec2 physCoord;
    uniform vec4 circle[3];
    uniform vec2 resolution;
    void main(void){
      vec3 pos;
      pos.x = 0.8 * cos(coord.x * pi) + 0.5 * cos(coord.y * pi) * cos(coord.x * pi);
      pos.y = 0.5 * sin(coord.y * pi);
      pos.z = 0.8 * sin(coord.x * pi) + 0.5 * cos(coord.y * pi) * sin(coord.x * pi);
      vec3 color = pos*0.2+0.8;

      vec2 p = physCoord;
      float eps = 0.5, eeps = 0.02;
      for(int i=0;i<3;i++){
        float hue = float(i)/3.;
        vec3 col = cos(vec3(1,0,-1)*pi*2./3. + hue*pi*2.) * 0.5 + 0.5;
        col += pos * 0.4;
        for(int j=-1;j<=1;j++){
          for(int k=-1;k<=1;k++){
            vec2 dif = vec2(float(j),float(k)) * resolution;
            vec2 relP = physCoord - circle[i].xy - dif;
            float t = circle[i].z;
            float r = circle[i].w;
            float l = length(relP);
            if(l < r + eps){
              float factor = 1.;
              if(l + eps > r*0.9)factor = mix(factor, 0.5, smoothstep(-eps,eps,l-r*0.9));
              vec2 lc = relP * mat2(cos(t),-sin(t),sin(t),cos(t)) / r;
              if(abs(lc.x) < 0.05 + eeps && lc.y < 0.01 + eeps)factor = mix(factor, 0.5, smoothstep(-eeps,eeps,min(0.05-abs(lc.x),0.01-lc.y)));
              color = mix(color, col * factor, smoothstep(-eps,eps,r-l));
            }
          }
        }
      }

      gl_FragColor = vec4(color,1);
    }
  `;

  const avsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    attribute vec2 position;
    varying vec2 texCoord;
    void main(void){
      texCoord = position * 0.5 + 0.5;
      gl_Position = vec4(position*vec2(0.5,4.0/3.0*5.0/8.0)+vec2(0.5,0),0.,1.);
    }
  `;
  const afsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec2 texCoord;
    uniform sampler2D worldTex;
    uniform vec2 resolution;
    void main(void){
      vec2 tc = texCoord;
      vec3 color = texture2D(worldTex,tc).rgb;
      gl_FragColor = vec4(color,1);
    }
  `;

  const tvsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    attribute vec2 position;
    varying vec2 coord;
    uniform vec2 resolution;
    void main(void){
      coord = position * resolution;
      gl_Position = vec4(position*vec2(0.5,1)-vec2(0.5,0),0.,1.);
    }
  `;
  const tfsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec2 coord;
    uniform vec2 resolution;
    uniform vec3 camera;
    uniform mat3 transform;
    uniform float fov;
    uniform sampler2D worldTex;
    float field(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      float qx = length(vec2(x,z)) - 0.8;
      float qy = y;
      return length(vec2(qx,qy)) - 0.5;
    }
    void main(void){
      vec2 uv = coord/resolution.y;
      vec3 cur = camera;
      vec3 dir = normalize(vec3(uv.x,uv.y,1./tan(fov*pi/180.)));
      dir = transform * dir;
      // Raymarch
      vec3 pos;
      float d = 0.;
      int maxIter = -1;
      for(int i=0;i<100;i++){
        pos = cur+dir*d;
        float f = field(pos);
        if(abs(f)<0.01){
          maxIter = i;
          break;
        }
        d += f;
      }
      // Discontinuity reduction
      for(int i=0;i<5;i++){
        d += field(pos) - 0.001*d;
        pos = cur+dir*d;
      }
      pos = cur+dir*d;
      float err = field(pos);
      if(abs(err) < 0.01){
        vec3 p = pos;
        float aux = atan(p.z,p.x);
        vec3 relP = p - vec3(cos(aux),0,sin(aux)) * 0.8;
        float relY = dot(relP,vec3(0,1,0));
        float relX = dot(relP,vec3(cos(aux),0,sin(aux)));
        float auy = atan(relY,relX);
        vec2 pp = vec2(aux/pi,auy/pi)*0.5+0.5;
        vec3 col = texture2D(worldTex,pp).rgb;
        gl_FragColor = vec4(col,1);
      }else{
        gl_FragColor = vec4(1);
      }
    }
  `;

  let program, aprogram, tprogram;
  let resolutionLocation, circleLocations = [];
  let aresolutionLocation, aworldTexLocation;
  let tresolutionLocation, tcameraLocation, ttransformLocation, tfovLocation, tworldTexLocation;

  let objects = {};

  let origin = [0,0,0];
  let adir = 0.8, rdir = 0, cameraDist = 6;
  let adirTo = adir, rdirTo = rdir;
  let camera = [0,0,0];
  let transform = [1,0,0,0,1,0,0,0,1];
  let transformI = [1,0,0,0,1,0,0,0,1];
  let fov = 26/2;

  let grabWorld = false, grabObject = null, grabFlipped = false;
  let prevMouseX = null, prevMouseY;
  cvs.addEventListener("mousedown",e=>{
    let eoX = e.offsetX - scrW;
    let eoY = e.offsetY - (450 - scrH) / 2;
    prevMouseX = eoX;
    prevMouseY = eoY;
    let collide = null;
    for(let i=0;i<3;i++){
      let o = objects[i];
      let dx = o.x - eoX;
      let dy = o.y - (scrH-eoY);
      let dr = o.r;
      if(dx*dx+dy*dy <= dr*dr){
        collide = {
          ix:i,
          x:eoX,y:scrH-eoY
        };
      }
    }
    if(collide){
      grabObject = collide;
    }else{
      grabWorld = true;
    }
  });
  cvs.addEventListener("mousemove",e=>{
    let eoX = e.offsetX - scrW;
    let eoY = e.offsetY - (450 - scrH) / 2;
    let dx = eoX - prevMouseX;
    let dy = eoY - prevMouseY;
    if(grabWorld){
      rdirTo -= dx/80;
      adirTo += dy/80;
      if(adirTo < -Math.PI/2)adirTo = -Math.PI/2;
      if(adirTo >  Math.PI/2)adirTo =  Math.PI/2;
    }
    if(grabObject){
      grabObject.x = eoX;
      grabObject.y = scrH-eoY;
    }
    prevMouseX = eoX;
    prevMouseY = eoY;
  });
  cvs.addEventListener("mouseup",e=>{
    grabWorld = false;
    grabObject = null;
  });

  function matMult(a,b){
    let c = [];
    for(let i=0;i<9;i++){
      let s = 0;
      for(let j=0;j<3;j++){
        s += a[Math.floor(i/3)*3+j]*b[i%3+j*3];
      }
      c.push(s);
    }
    return c;
  }
  function setCamera(){
    rdir += (rdirTo - rdir) / 2;
    adir += (adirTo - adir) / 2;
    let xRot = [1,0,0,0,Math.cos(adir),Math.sin(adir),0,-Math.sin(adir),Math.cos(adir)];
    let yRot = [Math.cos(rdir),0,Math.sin(rdir),0,1,0,-Math.sin(rdir),0,Math.cos(rdir)];
    let xRotI = [1,0,0,0,Math.cos(adir),-Math.sin(adir),0,Math.sin(adir),Math.cos(adir)];
    let yRotI = [Math.cos(rdir),0,-Math.sin(rdir),0,1,0,Math.sin(rdir),0,Math.cos(rdir)];
    transform = matMult(xRot,yRot);
    transformI = matMult(yRotI,xRotI);
    camera = [
      -transformI[2]*cameraDist + origin[0],
      -transformI[5]*cameraDist + origin[1],
      -transformI[8]*cameraDist + origin[2]
    ];
  }

  function compile(){
    function makeShader(type,source){
      const s = gl.createShader(type);
      gl.shaderSource(s,source);
      gl.compileShader(s);
      if(!gl.getShaderParameter(s,gl.COMPILE_STATUS)){
        console.error(gl.getShaderInfoLog(s));
        return null;
      }
      return s;
    }
    function makeProgram(vs,fs){
      const pr = gl.createProgram();
      gl.attachShader(pr,vs);
      gl.attachShader(pr,fs);
      gl.linkProgram(pr);
      if(!gl.getProgramParameter(pr,gl.LINK_STATUS)){
        console.error(gl.getProgramInfoLog(pr));
        return null;
      }
      return pr;
    }
    // Field rendering
    const vs = makeShader(gl.VERTEX_SHADER,vsSource);
    const fs = makeShader(gl.FRAGMENT_SHADER,fsSource);
    if(!vs || !fs)return;
    program = makeProgram(vs,fs);
    if(!program)return;
    gl.useProgram(program);

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(program,0,"position");
    gl.enableVertexAttribArray(0);

    resolutionLocation = gl.getUniformLocation(program,"resolution");
    for(let i=0;i<3;i++){
      circleLocations[i] = gl.getUniformLocation(program,"circle["+i+"]");
    }

    // Atlas rendering
    const avs = makeShader(gl.VERTEX_SHADER,avsSource);
    const afs = makeShader(gl.FRAGMENT_SHADER,afsSource);
    if(!avs || !afs)return;
    aprogram = makeProgram(avs,afs);
    if(!aprogram)return;
    gl.useProgram(aprogram);

    aresolutionLocation = gl.getUniformLocation(aprogram,"resolution");
    aworldTexLocation = gl.getUniformLocation(aprogram,"worldTex");
    gl.uniform1i(aworldTexLocation,0);

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(aprogram,0,"position");
    gl.enableVertexAttribArray(0);

    // Torus rendering
    const tvs = makeShader(gl.VERTEX_SHADER,tvsSource);
    const tfs = makeShader(gl.FRAGMENT_SHADER,tfsSource);
    if(!tvs || !tfs)return;
    tprogram = makeProgram(tvs,tfs);
    if(!tprogram)return;
    gl.useProgram(tprogram);

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(tprogram,0,"position");
    gl.enableVertexAttribArray(0);

    tcameraLocation = gl.getUniformLocation(tprogram,"camera");
    ttransformLocation = gl.getUniformLocation(tprogram,"transform");
    tfovLocation = gl.getUniformLocation(tprogram,"fov");
    tresolutionLocation = gl.getUniformLocation(tprogram,"resolution");
    tworldTexLocation = gl.getUniformLocation(tprogram,"worldTex");
    gl.uniform1i(tworldTexLocation,0);

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(tprogram,0,"position");
    gl.enableVertexAttribArray(0);
  }
  compile();

  let cnt = 0;
  refresh = _=>{
    gl.clear(gl.COLOR_BUFFER_BIT);
    cnt = 0;
  };
  drawCircle = (x,y,t,r)=>{
    objects[cnt] = {
      x:x,
      y:y,
      t:t,
      r:r
    };
    cnt++;
  };
  draw = _=>{
    if(!program)return;
    setCamera();
    gl.viewport(0,0,scrW*2,scrH*2);
    gl.bindFramebuffer(gl.FRAMEBUFFER,frameBuffer);
    gl.useProgram(program);
    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.vertexAttribPointer(0,2,gl.FLOAT,false,8,0);
    gl.enableVertexAttribArray(0);
    gl.uniform2f(resolutionLocation,scrW,scrH);
    for(let i=0;i<3;i++){
      gl.uniform4f(circleLocations[i],objects[i].x,objects[i].y,objects[i].t,objects[i].r);
    }
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
    gl.bindFramebuffer(gl.FRAMEBUFFER,null);

    gl.viewport(0,0,1200,450);
    gl.useProgram(aprogram);
    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.vertexAttribPointer(0,2,gl.FLOAT,false,8,0);
    gl.enableVertexAttribArray(0);
    gl.uniform2f(aresolutionLocation,scrW,scrH);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);

    gl.useProgram(tprogram);
    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.vertexAttribPointer(0,2,gl.FLOAT,false,8,0);
    gl.enableVertexAttribArray(0);
    gl.uniform2f(tresolutionLocation,600,450);
    gl.uniform3f(tcameraLocation,camera[0],camera[1],camera[2]);
    gl.uniformMatrix3fv(ttransformLocation,false,transform);
    gl.uniform1f(tfovLocation,fov);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
  };
  mouseContact = (i)=>{
    if(!grabObject)return [];
    if(grabObject.ix != i)return [];
    let x = grabObject.x;
    let y = grabObject.y;
    return [{
      x:x, y:y
    }];
  }
});
