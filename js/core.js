// A-Tags core: find black squares, straighten them, read the 10x10 grid, match against 151 tags.
const ATAG=(()=>{
const UNIT=[[0,0],[1,0],[1,1],[0,1]];
function solveH(src,dst){const A=[],b=[];for(let i=0;i<4;i++){const[u,v]=src[i],[x,y]=dst[i];A.push([u,v,1,0,0,0,-u*x,-v*x]);b.push(x);A.push([0,0,0,u,v,1,-u*y,-v*y]);b.push(y)}
  for(let c=0;c<8;c++){let p=c;for(let r=c+1;r<8;r++)if(Math.abs(A[r][c])>Math.abs(A[p][c]))p=r;[A[c],A[p]]=[A[p],A[c]];[b[c],b[p]]=[b[p],b[c]];const d=A[c][c];if(Math.abs(d)<1e-12)return null;
    for(let r=0;r<8;r++){if(r===c)continue;const f=A[r][c]/d;if(!f)continue;for(let k=c;k<8;k++)A[r][k]-=f*A[c][k];b[r]-=f*b[c]}}
  const h=b.map((v,i)=>v/A[i][i]);return[[h[0],h[1],h[2]],[h[3],h[4],h[5]],[h[6],h[7],1]]}
function applyH(H,u,v){const w=H[2][0]*u+H[2][1]*v+H[2][2];return[(H[0][0]*u+H[0][1]*v+H[0][2])/w,(H[1][0]*u+H[1][1]*v+H[1][2])/w]}
function bil(g,W,H,x,y){x-=.5;y-=.5;if(x<0||y<0||x>W-2||y>H-2)return -1;const x0=x|0,y0=y|0,fx=x-x0,fy=y-y0,k=y0*W+x0;return g[k]*(1-fx)*(1-fy)+g[k+1]*fx*(1-fy)+g[k+W]*(1-fx)*fy+g[k+W+1]*fx*fy}

// ---- tag codes: inner 8x8 cells (border ring is always black), 4 rotations ----
let CODES=null,NAMES=null;
function init(data){NAMES=data.names;CODES=[];
  data.grids.forEach((s,id)=>{let g=[];for(let r=0;r<10;r++)g.push([...s.slice(r*10,r*10+10)].map(Number));
    for(let k=0;k<4;k++){const inner=new Float32Array(64);for(let r=0;r<8;r++)for(let c=0;c<8;c++)inner[r*8+c]=g[r+1][c+1];CODES.push({id,k,bits:inner});
      g=g[0].map((_,c)=>g.map(row=>row[c]).reverse())}})} // rotate 90° clockwise

// ---- candidate squares (adaptive threshold + connected components + 4 corners) ----
let bin,lab,stk,pix,Ibuf;
function candidates(g,W,H,maxN=40){
  const P=W*H;if(!bin||bin.length!==P){bin=new Uint8Array(P);lab=new Int32Array(P);stk=new Int32Array(P);pix=new Int32Array(P)}
  if(!Ibuf||Ibuf.length!==(W+1)*(H+1))Ibuf=new Int32Array((W+1)*(H+1));const I=Ibuf;let gm=0;
  for(let y=0;y<H;y++){let row=0;for(let x=0;x<W;x++){const v=g[y*W+x];gm+=v;row+=v;I[(y+1)*(W+1)+x+1]=I[y*(W+1)+x+1]+row}}
  gm/=P;const r=Math.max(7,Math.round(Math.max(W,H)/26));
  for(let y=0;y<H;y++){const y0=Math.max(0,y-r),y1=Math.min(H,y+r+1);for(let x=0;x<W;x++){const x0=Math.max(0,x-r),x1=Math.min(W,x+r+1);
    const s=I[y1*(W+1)+x1]-I[y0*(W+1)+x1]-I[y1*(W+1)+x0]+I[y0*(W+1)+x0];const mean=s/((y1-y0)*(x1-x0));const v=g[y*W+x];
    bin[y*W+x]=(v<mean-7||v<gm*.42)?1:0}}
  lab.fill(0);let nl=0,pc=0;const comps=[];
  for(let p0=0;p0<P;p0++){if(!bin[p0]||lab[p0])continue;nl++;let sp=0;stk[sp++]=p0;lab[p0]=nl;const st=pc;let mnx=W,mxx=0,mny=H,mxy=0,sx=0,sy=0;
    while(sp){const p=stk[--sp];pix[pc++]=p;const x=p%W,y=(p-x)/W;sx+=x;sy+=y;if(x<mnx)mnx=x;if(x>mxx)mxx=x;if(y<mny)mny=y;if(y>mxy)mxy=y;
      if(x>0&&bin[p-1]&&!lab[p-1]){lab[p-1]=nl;stk[sp++]=p-1}if(x<W-1&&bin[p+1]&&!lab[p+1]){lab[p+1]=nl;stk[sp++]=p+1}
      if(y>0&&bin[p-W]&&!lab[p-W]){lab[p-W]=nl;stk[sp++]=p-W}if(y<H-1&&bin[p+W]&&!lab[p+W]){lab[p+W]=nl;stk[sp++]=p+W}}
    const n=pc-st,bw=mxx-mnx+1,bh=mxy-mny+1;
    if(n<120||bw<12||bh<12||mnx===0||mny===0||mxx===W-1||mxy===H-1||bw>bh*4||bh>bw*4)continue;
    comps.push({st,n,cx:sx/n,cy:sy/n})}
  comps.sort((a,b)=>b.n-a.n);const out=[];
  for(const c of comps.slice(0,maxN)){
    const end=c.st+c.n;let A=0,bd=-1;
    for(let k=c.st;k<end;k++){const p=pix[k],x=p%W,y=(p-x)/W,d=(x-c.cx)**2+(y-c.cy)**2;if(d>bd){bd=d;A=p}}
    const ax=A%W,ay=(A-ax)/W;let C=0;bd=-1;
    for(let k=c.st;k<end;k++){const p=pix[k],x=p%W,y=(p-x)/W,d=(x-ax)**2+(y-ay)**2;if(d>bd){bd=d;C=p}}
    const cx=C%W,cy=(C-cx)/W,ex=cx-ax,ey=cy-ay;let B=0,D=0,bmax=-1e9,dmin=1e9;
    for(let k=c.st;k<end;k++){const p=pix[k],x=p%W,y=(p-x)/W,cr=ex*(y-ay)-ey*(x-ax);if(cr>bmax){bmax=cr;B=p}if(cr<dmin){dmin=cr;D=p}}
    const L2=ex*ex+ey*ey;if(bmax<.2*L2||-dmin<.2*L2)continue;
    let q=[[ax,ay],[B%W,(B-B%W)/W],[cx,cy],[D%W,(D-D%W)/W]].map(([x,y])=>[x+.5,y+.5]);
    let area=0;for(let i=0;i<4;i++){const[a,b]=q[i],[e,f]=q[(i+1)%4];area+=a*f-e*b}
    if(area<0)q=[q[0],q[3],q[2],q[1]];
    const sides=q.map((p,i)=>Math.hypot(q[(i+1)%4][0]-p[0],q[(i+1)%4][1]-p[1]));if(Math.max(...sides)>4*Math.min(...sides))continue;
    // the black square should fill most of its outline (rejects L-shapes, lines, etc.)
    if(c.n<.35*Math.abs(area)/2)continue;
    out.push(q)}
  return{bin,quads:out}}

// ---- sub-pixel edge refinement on the full-size frame ----
function refine(g,W,H,q){
  const lines=[];
  for(let i=0;i<4;i++){const a=q[i],b=q[(i+1)%4],dx=b[0]-a[0],dy=b[1]-a[1],L=Math.hypot(dx,dy);if(L<8)return null;
    const nx=-dy/L,ny=dx/L,R=Math.max(3,Math.min(10,L*.06)),pts=[];
    for(let s=1;s<=24;s++){const t=.08+.84*s/25,mx=a[0]+dx*t,my=a[1]+dy*t;let best=0,bo=0,prev=bil(g,W,H,mx-nx*(R+.5),my-ny*(R+.5)),gr=[];
      for(let o=-R;o<=R;o+=.5){const v=bil(g,W,H,mx+nx*o,my+ny*o);if(v<0||prev<0){prev=v;gr.push(0);continue}const d=Math.abs(v-prev);gr.push(d);if(d>best){best=d;bo=gr.length-1}prev=v}
      if(best<12||bo===0||bo===gr.length-1)continue;const l=gr[bo-1],c=gr[bo],r=gr[bo+1],den=l-2*c+r,sh=den?.5*(l-r)/den:0;
      const o=-R+(bo+sh)*.5-.25;pts.push([mx+nx*o,my+ny*o])}
    if(pts.length<8)return null;
    let cx=0,cy=0;for(const p of pts){cx+=p[0];cy+=p[1]}cx/=pts.length;cy/=pts.length;let sxx=0,sxy=0,syy=0;
    for(const p of pts){const u=p[0]-cx,v=p[1]-cy;sxx+=u*u;sxy+=u*v;syy+=v*v}
    const th=.5*Math.atan2(2*sxy,sxx-syy);lines.push([cx,cy,Math.cos(th),Math.sin(th)])}
  const out=[];
  for(let i=0;i<4;i++){const[x1,y1,u1,v1]=lines[(i+3)%4],[x2,y2,u2,v2]=lines[i],den=u1*v2-v1*u2;if(Math.abs(den)<1e-6)return null;
    const t=((x2-x1)*v2-(y2-y1)*u2)/den,p=[x1+u1*t,y1+v1*t];if(Math.hypot(p[0]-q[i][0],p[1]-q[i][1])>Math.max(6,.08*Math.hypot(q[1][0]-q[0][0],q[1][1]-q[0][1])))return null;out.push(p)}
  return out}

// ---- read the 10x10 grid and match ----
// returns null (not a tag) or {id,k,quad (corner 0 = tag's top-left),score,prob,second,secondProb,unsure,cells}
function readGrid(g,W,H,q){
  const Hm=solveH(UNIT,q);if(!Hm)return null;const cells=new Float32Array(100);
  for(let r=0;r<10;r++)for(let c=0;c<10;c++){let s=0,n=0;
    for(const a of[.3,.5,.7])for(const b of[.3,.5,.7]){const[x,y]=applyH(Hm,(c+a)/10,(r+b)/10),v=bil(g,W,H,x,y);if(v>=0){s+=v;n++}}
    if(n<5)return null;cells[r*10+c]=s/n}
  const ring=[];for(let i=0;i<10;i++){ring.push(cells[i],cells[90+i],cells[i*10],cells[i*10+9])}
  ring.sort((a,b)=>a-b);const black=ring[ring.length>>1];
  const inner=[];for(let r=1;r<9;r++)for(let c=1;c<9;c++)inner.push(cells[r*10+c]);
  const sorted=[...inner].sort((a,b)=>a-b),white=sorted[Math.floor(sorted.length*.95)];
  if(white-black<25)return null;                       // no contrast: plain black square
  const ringWhite=ring.filter(v=>(v-black)/(white-black)>.5).length;if(ringWhite>4)return null; // border must be black
  const v=inner.map(x=>Math.min(1,Math.max(0,(x-black)/(white-black))));
  return{v,cells,black,white,H:Hm}}
function match(v){
  const best=new Float32Array(NAMES.length).fill(1e9),bestK=new Int8Array(NAMES.length);
  for(const c of CODES){let d=0;const b=c.bits;for(let i=0;i<64;i++){const e=v[i]-b[i];d+=e<0?-e:e}if(d<best[c.id]){best[c.id]=d;bestK[c.id]=c.k}}
  let i1=0;for(let i=1;i<best.length;i++)if(best[i]<best[i1])i1=i;
  let i2=i1===0?1:0;for(let i=0;i<best.length;i++)if(i!==i1&&best[i]<best[i2])i2=i;
  let Z=0;for(let i=0;i<best.length;i++)Z+=Math.exp(-2*(best[i]-best[i1]));
  return{id:i1,k:bestK[i1],dist:best[i1],second:i2,dist2:best[i2],prob:1/Z,prob2:Math.exp(-2*(best[i2]-best[i1]))/Z}}
function decode(g,W,H,q){
  const r=readGrid(g,W,H,q);if(!r)return null;const m=match(r.v);
  if(m.dist>5)return null;                              // too far from every tag
  // reorder corners so corner 0 is the tag's own top-left (undo the rotation k)
  const quad=[0,1,2,3].map(i=>q[(i+m.k)%4]);
  return{...m,quad,unsure:(m.dist2-m.dist)<.6,v:r.v}}

return{init,candidates,refine,decode,solveH,applyH,UNIT,names:()=>NAMES}})();
if(typeof module!=="undefined")module.exports=ATAG;
