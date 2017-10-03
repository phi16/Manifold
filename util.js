let scrW = 0, scrH = 0;
let refresh = _=>_;
let drawCircle = _=>_;
let drawRect = _=>_;
let drawContact = _=>_;
window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  const ctx = cvs.getContext('2d');
  scrW = cvs.width;
  scrH = cvs.height;

  let cnt = 0;
  let colors = [
    "rgb(255,174,201)",
    "rgb(255,201,14)",
    "rgb(181,230,29)",
    "rgb(153,217,234)",
    "rgb(112,146,190)",
    "rgb(200,191,231)"
  ];
  refresh = _=>{
    ctx.fillStyle = "#fff";
    ctx.fillRect(0,0,scrW*3,scrH*3);
    cnt=0;
  };
  drawCircle = (x,y,t,r)=>{
    ctx.strokeStyle = "#000";
    ctx.fillStyle = colors[Math.floor(cnt/9)];
    ctx.beginPath();
    ctx.arc(x,y,r,0,Math.PI*2,1);
    ctx.stroke();
    ctx.fill();
    //ctx.beginPath();
    //ctx.moveTo(x,y);
    //ctx.lineTo(x+r*Math.cos(t),y+r*Math.sin(t));
    //ctx.stroke();
    cnt++;
  };
  drawRect = (x,y,t,w,h)=>{
    ctx.strokeStyle = "#000";
    ctx.fillStyle = colors[Math.floor(cnt/9)];
    ctx.save();
    ctx.beginPath();
    ctx.translate(x,y);
    ctx.rotate(t);
    ctx.rect(-w/2,-h/2,w,h);
    ctx.stroke();
    ctx.fill();
    ctx.restore();
    cnt++;
  };
  drawContact = (x,y,vx,vy,d)=>{
    ctx.fillStyle = "#f00";
    ctx.strokeStyle = "#f00";
    ctx.beginPath();
    ctx.arc(x,y,2,0,Math.PI*2,1);
    ctx.fill();
    ctx.beginPath();
    ctx.moveTo(x,y);
    ctx.lineTo(x+vx*d,y+vy*d);
    ctx.stroke();
  };
});
