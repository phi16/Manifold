const list1 = [
  {path:"plane",name:"Plane"},
  {path:"disc",name:"Disc"},
  {path:"horn2d",name:"Horn 2D"},
  {path:"hemi",name:"Hemisphere"},
  {path:"sphere",name:"Sphere"},
  {path:"torus",name:"Torus"},
];
const list2 = [
  {path:"plane1",name:"Plane"},
  {path:"disc1",name:"Disc"},
  {path:"horn2d1",name:"Horn 2D"},
  {path:"hemi1",name:"Hemisphere"},
  {path:"sphere1",name:"Sphere"},
  {path:"torus1",name:"Torus"},
];
const list3 = [
  {path:"horn1",name:"Horn"},
  {path:"proj1",name:"Projective Plane"},
  {path:"projtorus1",name:"Projective Torus"}
];
const list4 = [
  {path:"horn",name:"Horn"},
  {path:"proj",name:"Projective Plane"},
  {path:"projtorus",name:"Projective Torus"},
  {path:"tori",name:"3D Torus / 4D Torus Embedded in 3D"}
];
window.addEventListener("load",_=>{
  const frame1 = document.getElementById("frame1");
  const frame2 = document.getElementById("frame2");
  const name = document.getElementById("name");
  function addContent(target,list){
    list.forEach(l=>{
      const img = document.createElement("img");
      img.src="/Manifold/" + l.path + "/" + l.path + ".png";
      img.addEventListener("click",_=>{
        if(l.path == "tori"){
          frame1.src = "/Manifold/" + l.path + "/index1.html"
          frame2.src = "/Manifold/" + l.path + "/index2.html"
          frame2.style.display = "block";
          frame1.className = "po";
          frame2.className = "po";
        }else{
          frame1.src = "/Manifold/" + l.path + "/index.html";
          frame2.style.display = "none";
          frame1.className = "";
          frame2.className = "";
        }
        name.textContent = l.name;
      });
      target.appendChild(img);
    });
  }
  function po(n,p){
    const e = document.getElementById(n);
    addContent(e,p);
  }
  po("list1",list1);
  po("list2",list2);
  po("list3",list3);
  po("list4",list4);
});
