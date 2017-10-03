let scrW = 0, scrH = 0;
let refresh = _=>_;
let drawCircle = _=>_;
let draw = _=>_;
window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  const ctx = cvs.getContext('2d');
  scrW = 600;
  scrH = 600*5/8;

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
  draw = _=>{

  };
});
