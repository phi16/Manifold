let scrW = 0, scrH = 0;
let refresh = _=>_, compile = _=>_, draw = _=>_;
window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  scrW = cvs.width;
  scrH = cvs.height;

  const gl = cvs.getContext("webgl");
  const verts = [-1,-1,-1,1,1,-1,1,1];
  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
  gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(verts),gl.STATIC_DRAW);
  gl.disable(gl.BLEND);
  gl.disable(gl.DEPTH_TEST);
  gl.viewport(0,0,scrW,scrH);
  gl.clearColor(0,0,0,1);

  const vsSource = `
    precision mediump float;
    attribute vec2 position;
    varying vec2 coord;
    uniform vec2 resolution;
    void main(void){
      coord = position * resolution;
      gl_Position = vec4(position,0.,1.);
    }
  `;
  const fsSource = (f,g)=>`
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec2 coord;
    uniform vec2 resolution;
    uniform vec3 circle;
    float field(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return ` + f + `;
    }
    vec3 gradient(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return ` + g + `;
    }
    void main(void){
      vec2 uv = coord/resolution.y;
      vec3 cur = vec3(0,0,-5.);
      vec3 dir = normalize(vec3(uv.x,uv.y,4));
      // Raymarch
      vec3 pos, nrm;
      float d = 0.;
      int maxIter = -1;
      for(int i=0;i<100;i++){
        pos = cur+dir*d;
        nrm = gradient(pos);
        float f = field(pos)/length(nrm);
        if(abs(f)<0.01){
          maxIter = i;
          break;
        }
        d += f;
      }
      // Discontinuity reduction
      for(int i=0;i<1;i++){
        nrm = gradient(pos);
        d += field(pos)/length(nrm) - 0.01*d;
      }
      pos = cur+dir*d;
      nrm = gradient(pos);

      //float theta = coord.x/resolution.x*pi;
      //float phi = coord.y/resolution.y*pi/2.;
      //pos = vec3(cos(phi)*cos(theta),cos(phi)*sin(theta),sin(phi));

      // Coloring
      vec3 color;
      if(maxIter == -1){
        color = vec3(1);
      }else{
        nrm = normalize(nrm);
        color = vec3(-nrm.z*0.5+0.5);
        if(-nrm.z<0.4){
          color = vec3(0.3);
        }
      }
      if(length(pos-circle) < 0.2){
        color *= vec3(1,0.9,0.8);
        if(length(pos-circle) > 0.18){
          color *= vec3(1,0.5,0);
        }
      }
      gl_FragColor = vec4(color,1.);
    }
  `;

  let program;
  let resLocation, posLocation;
  let circleLocation;

  refresh = _=>{
    gl.clear(gl.COLOR_BUFFER_BIT);
    gl.uniform2f(resLocation,scrW,scrH);
  };
  draw = (x,y,z)=>{
    if(!program)return;
    gl.uniform3f(circleLocation,x,y,z);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
  };
  compile = (field,grad)=>{
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
    const vs = makeShader(gl.VERTEX_SHADER,vsSource);
    const fs = makeShader(gl.FRAGMENT_SHADER,fsSource(field,grad));
    if(!vs || !fs)return;
    program = makeProgram(vs,fs);
    gl.useProgram(program);
    if(!program)return;

    resLocation = gl.getUniformLocation(program,"resolution");
    circleLocation = gl.getUniformLocation(program,"circle");

    posLocation = gl.getAttribLocation(program,"position");
    gl.enableVertexAttribArray(posLocation);
    gl.vertexAttribPointer(posLocation,2,gl.FLOAT,false,0,0);
  };
});
