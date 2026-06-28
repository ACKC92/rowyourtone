(function(){
  "use strict";
  const SHARP=['C','C\u266F','D','D\u266F','E','F','F\u266F','G','G\u266F','A','A\u266F','B'];
  const FLAT =['C','D\u266D','D','E\u266D','E','F','G\u266D','G','A\u266D','A','B\u266D','B'];
  // palette layout: naturals stand alone; accidental pitch classes are an enharmonic pair
  const NOTE_LAYOUT=[
    {nat:{pc:0,name:'C'}},
    {pair:{pc:1,sharp:'C\u266F',flat:'D\u266D'}},
    {nat:{pc:2,name:'D'}},
    {pair:{pc:3,sharp:'D\u266F',flat:'E\u266D'}},
    {nat:{pc:4,name:'E'}},
    {nat:{pc:5,name:'F'}},
    {pair:{pc:6,sharp:'F\u266F',flat:'G\u266D'}},
    {nat:{pc:7,name:'G'}},
    {pair:{pc:8,sharp:'G\u266F',flat:'A\u266D'}},
    {nat:{pc:9,name:'A'}},
    {pair:{pc:10,sharp:'A\u266F',flat:'B\u266D'}},
    {nat:{pc:11,name:'B'}}
  ];
  const mod12=n=>((n%12)+12)%12;
  const $=id=>document.getElementById(id);

  let inputMode='notes';   // 'notes' | 'int'
  let dispMode ='notes';   // 'notes' | 'int'
  let spelling ='sharp';   // 'sharp' | 'flat'  (computed cells + un-named entries)
  let entered  =[];        // [{pc, name|null}]
  let state    =null;      // built matrix (only after Generate)
  let cellEls  =[];
  let subsetK  =3;
  let imbricate=false;
  const formOpen={P:false,I:false,R:false,RI:false};
  let dragIdx=-1, dragGhost=null, dragSX=0, dragSY=0, dragArmed=false;
  let genOps   ={T:false,I:false,R:false,RI:false};
  let genResults=null;      // last derivation search result
  let buildMode='allint';
  let genPath=false;   // 'allint' | 'allcomb' | 'risym' | 'derived' | 'contains'
  let combSource='any';     // source hexachord id for all-combinatorial
  let derSize=3;            // derived-row segment size (3 or 4)
  let derClass='any';       // derived-row set class (Forte name) or 'any'
  let containsSpec='';      // user-entered set class for "contains"
  let buildResults=null;    // last constrained-generation result

  // ----- mode gate -----
  let mode=null;            // null (gate) | 'twelve' | 'stravinsky' | 'custom'
  let ROWLEN=12;            // row length for the shared workspace (12 twelve · 6 stravinsky)
  let customN=4;            // chosen row length in Custom mode (2–11; default tetrachord)
  let stravForm='P';        // selected form in the rotational-array view
  let stravIvals=false;     // show interval annotations in the array (off by default)
  let stravPick={kind:'row',idx:0}; // which row/vertical hexachord is selected for subset analysis
  const modeStash={twelve:{entered:[],state:null}, stravinsky:{entered:[],state:null}, custom:{entered:[],state:null}};

  // Stravinsky example hexachords. The first two are real arrays Stravinsky built rotational
  // arrays from; the rest are representative orderings of well-known hexachordal set classes.
  const STRAV_EX={
    sermon: {pcs:[3,2,6,4,5,8], note:'A Sermon, a Narrative and a Prayer \u2014 I-hexachord (E\u266D D G\u266D E F A\u266D)'},
    requiem:{pcs:[5,0,11,9,10,2], note:'Requiem Canticles \u2014 P1a hexachord (6-Z40)'},
    '6-1':  {pcs:[0,1,2,3,4,5], note:'chromatic hexachord 6-1 (012345)'},
    '6-20': {pcs:[0,1,4,5,8,9], note:'hexatonic / all-combinatorial 6-20 (014589)'},
    '6-32': {pcs:[0,2,4,5,7,9], note:'diatonic hexachord 6-32 (024579)'},
    '6-35': {pcs:[0,2,4,6,8,10], note:'whole-tone hexachord 6-35 (02468T)'}
  };
  function randomHexPcs(){ const a=[0,1,2,3,4,5,6,7,8,9,10,11]; for(let i=11;i>0;i--){const j=Math.floor(Math.random()*(i+1)); const t=a[i];a[i]=a[j];a[j]=t;} return a.slice(0,6); }

  const enteredPcs = ()=>entered.map(e=>e.pc);
  const spellName  = pc=>(spelling==='flat'?FLAT:SHARP)[pc];
  const nameFor    = e=>e.name || spellName(e.pc);
  const showPc     = v=>dispMode==='notes' ? spellName(v) : String(v);

  // ---------- set-class theory (Rahn/Straus) ----------
  const pcTok=v=>v===10?'T':v===11?'E':String(v);
  const uniqSort=a=>[...new Set(a.map(mod12))].sort((x,y)=>x-y);
  const spanVec=rot=>{const v=[];for(let m=1;m<rot.length;m++)v.push(mod12(rot[m]-rot[0]));return v;};
  function tighter(a,b){const va=spanVec(a),vb=spanVec(b);for(let m=va.length-1;m>=0;m--){if(va[m]!==vb[m])return va[m]<vb[m];}return a[0]<b[0];}
  function normalForm(pcs){
    const s=uniqSort(pcs),n=s.length; if(n<=1)return s.slice();
    let best=null;
    for(let i=0;i<n;i++){const rot=[];for(let k=0;k<n;k++)rot.push(s[(i+k)%n]);if(best===null||tighter(rot,best))best=rot;}
    return best;
  }
  function packedLeft(a,b){for(let m=1;m<a.length;m++){if(a[m]!==b[m])return a[m]<b[m]?a:b;}return a;}
  function primeForm(pcs){
    const nf=normalForm(pcs); if(nf.length===0)return [];
    const t0=nf.map(x=>mod12(x-nf[0]));
    const nfi=normalForm(pcs.map(x=>mod12(-x)));
    const t0i=nfi.map(x=>mod12(x-nfi[0]));
    return packedLeft(t0,t0i);
  }
  function icVector(pcs){const s=uniqSort(pcs),v=[0,0,0,0,0,0];for(let i=0;i<s.length;i++)for(let j=i+1;j<s.length;j++){let d=mod12(s[i]-s[j]);d=Math.min(d,12-d);if(d>=1)v[d-1]++;}return v;}
  const SC_RAW={
    2:[['2-1',[0,1]],['2-2',[0,2]],['2-3',[0,3]],['2-4',[0,4]],['2-5',[0,5]],['2-6',[0,6]]],
    3:[['3-1',[0,1,2]],['3-2',[0,1,3]],['3-3',[0,1,4]],['3-4',[0,1,5]],['3-5',[0,1,6]],['3-6',[0,2,4]],['3-7',[0,2,5]],['3-8',[0,2,6]],['3-9',[0,2,7]],['3-10',[0,3,6]],['3-11',[0,3,7]],['3-12',[0,4,8]]],
    4:[['4-1',[0,1,2,3]],['4-2',[0,1,2,4]],['4-3',[0,1,3,4]],['4-4',[0,1,2,5]],['4-5',[0,1,2,6]],['4-6',[0,1,2,7]],['4-7',[0,1,4,5]],['4-8',[0,1,5,6]],['4-9',[0,1,6,7]],['4-10',[0,2,3,5]],['4-11',[0,1,3,5]],['4-12',[0,2,3,6]],['4-13',[0,1,3,6]],['4-14',[0,2,3,7]],['4-Z15',[0,1,4,6]],['4-16',[0,1,5,7]],['4-17',[0,3,4,7]],['4-18',[0,1,4,7]],['4-19',[0,1,4,8]],['4-20',[0,1,5,8]],['4-21',[0,2,4,6]],['4-22',[0,2,4,7]],['4-23',[0,2,5,7]],['4-24',[0,2,4,8]],['4-25',[0,2,6,8]],['4-26',[0,3,5,8]],['4-27',[0,2,5,8]],['4-28',[0,3,6,9]],['4-Z29',[0,1,3,7]]],
    5:[['5-1',[0,1,2,3,4]],['5-2',[0,1,2,3,5]],['5-3',[0,1,2,4,5]],['5-4',[0,1,2,3,6]],['5-5',[0,1,2,3,7]],['5-6',[0,1,2,5,6]],['5-7',[0,1,2,6,7]],['5-8',[0,2,3,4,6]],['5-9',[0,1,2,4,6]],['5-10',[0,1,3,4,6]],['5-11',[0,2,3,4,7]],['5-Z12',[0,1,3,5,6]],['5-13',[0,1,2,4,8]],['5-14',[0,1,2,5,7]],['5-15',[0,1,2,6,8]],['5-16',[0,1,3,4,7]],['5-Z17',[0,1,3,4,8]],['5-Z18',[0,1,4,5,7]],['5-19',[0,1,3,6,7]],['5-20',[0,1,3,7,8]],['5-21',[0,1,4,5,8]],['5-22',[0,1,4,7,8]],['5-23',[0,2,3,5,7]],['5-24',[0,1,3,5,7]],['5-25',[0,2,3,5,8]],['5-26',[0,2,4,5,8]],['5-27',[0,1,3,5,8]],['5-28',[0,2,3,6,8]],['5-29',[0,1,3,6,8]],['5-30',[0,1,4,6,8]],['5-31',[0,1,3,6,9]],['5-32',[0,1,4,6,9]],['5-33',[0,2,4,6,8]],['5-34',[0,2,4,6,9]],['5-35',[0,2,4,7,9]],['5-Z36',[0,1,2,4,7]],['5-Z37',[0,3,4,5,8]],['5-Z38',[0,1,2,5,8]]],
    6:[['6-1',[0,1,2,3,4,5]],['6-2',[0,1,2,3,4,6]],['6-Z3',[0,1,2,3,5,6]],['6-Z4',[0,1,2,4,5,6]],['6-5',[0,1,2,3,6,7]],['6-Z6',[0,1,2,5,6,7]],['6-7',[0,1,2,6,7,8]],['6-8',[0,2,3,4,5,7]],['6-9',[0,1,2,3,5,7]],['6-Z10',[0,1,3,4,5,7]],['6-Z11',[0,1,2,4,5,7]],['6-Z12',[0,1,2,4,6,7]],['6-Z13',[0,1,3,4,6,7]],['6-14',[0,1,3,4,5,8]],['6-15',[0,1,2,4,5,8]],['6-16',[0,1,4,5,6,8]],['6-Z17',[0,1,2,4,7,8]],['6-18',[0,1,2,5,7,8]],['6-Z19',[0,1,3,4,7,8]],['6-20',[0,1,4,5,8,9]],['6-21',[0,2,3,4,6,8]],['6-22',[0,1,2,4,6,8]],['6-Z23',[0,2,3,5,6,8]],['6-Z24',[0,1,3,4,6,8]],['6-Z25',[0,1,3,5,6,8]],['6-Z26',[0,1,3,5,7,8]],['6-27',[0,1,3,4,6,9]],['6-Z28',[0,1,3,5,6,9]],['6-Z29',[0,2,3,6,7,9]],['6-30',[0,1,3,6,7,9]],['6-31',[0,1,4,5,7,9]],['6-32',[0,2,4,5,7,9]],['6-33',[0,2,3,5,7,9]],['6-34',[0,1,3,5,7,9]],['6-35',[0,2,4,6,8,10]],['6-Z36',[0,1,2,3,4,7]],['6-Z37',[0,1,2,3,4,8]],['6-Z38',[0,1,2,3,7,8]],['6-Z39',[0,2,3,4,5,8]],['6-Z40',[0,1,2,3,5,8]],['6-Z41',[0,1,2,3,6,8]],['6-Z42',[0,1,2,3,6,9]],['6-Z43',[0,1,2,5,6,8]],['6-Z44',[0,1,2,5,6,9]],['6-Z45',[0,2,3,4,6,9]],['6-Z46',[0,1,2,4,6,9]],['6-Z47',[0,1,2,4,7,9]],['6-Z48',[0,1,2,5,7,9]],['6-Z49',[0,1,3,4,7,9]],['6-Z50',[0,1,4,6,7,9]]]
  };
  // Extend the catalogue to the larger cardinalities by complementation: every set class and its
  // complement share the same Forte ordinal (7-35 is the complement of 5-35, 8-Z29 of 4-Z29, and so
  // on), so 7-12-note classes are derived from the 5/4/3/2-note tables already verified above. This
  // means an entered 7-11-note cell still gets a correct Forte label even though no segment is that big.
  (function(){
    const comp=pcs=>{const s=new Set(pcs.map(mod12)),c=[];for(let i=0;i<12;i++)if(!s.has(i))c.push(i);return c;};
    [2,3,4,5].forEach(card=>{ const big=12-card; SC_RAW[big]=SC_RAW[card].map(([nm,pcs])=>[nm.replace(/^\d+/,String(big)),comp(pcs)]); });
    SC_RAW[1]=[['1-1',[0]]]; SC_RAW[11]=[['11-1',[0,1,2,3,4,5,6,7,8,9,10]]]; SC_RAW[12]=[['12-1',[0,1,2,3,4,5,6,7,8,9,10,11]]];
  })();
  const SC_LOOKUP={};
  for(const card in SC_RAW) for(const pair of SC_RAW[card]) SC_LOOKUP[primeForm(pair[1]).join(',')]=pair[0];
  const forteName=pcs=>SC_LOOKUP[primeForm(pcs).join(',')]||null;
  function cellForms(A){const out=[];for(let n=0;n<12;n++){const t=A.map(x=>mod12(x+n)),iv=A.map(x=>mod12(n-x));out.push(['T'+n,t]);out.push(['I'+n,iv]);out.push(['R'+n,t.slice().reverse()]);out.push(['RI'+n,iv.slice().reverse()]);}return out;}
  // pitch-class SET relations: every T_n and T_nI that maps the SET of A onto the SET of B
  // (order-independent — two segments that are the same set class related by T7 are detected even
  //  when their notes appear in a different order, e.g. [4,10,2] -> [11,9,5] is T7). An operator is
  // marked with "*" when it ALSO holds as an ordered relationship: applying it to A note-for-note
  // reproduces B in the same order (a literal transposition/inversion of the melodic cell, not just
  // a set correspondence).
  function segRelations(A,B){
    const sa=[...new Set(A)], sb=[...new Set(B)];
    if(sa.length!==sb.length) return [];
    const key=a=>a.map(x=>mod12(x)).sort((p,q)=>p-q).join(','), bk=key(sb);
    const bOrd=B.map(x=>mod12(x)).join(','), out=[];
    for(let n=0;n<12;n++) if(key(sa.map(x=>x+n))===bk){ const ord=A.map(x=>mod12(x+n)).join(',')===bOrd; out.push('T'+n+(ord?'*':'')); }
    for(let n=0;n<12;n++) if(key(sa.map(x=>n-x))===bk){ const ord=A.map(x=>mod12(n-x)).join(',')===bOrd; out.push('T'+n+'I'+(ord?'*':'')); }
    return out;
  }

  // Common tonal sonorities & collections, recognised from the actual pitch-class SET (so e.g. a
  // major triad and a minor triad — same set class 3-11 — are still told apart). Returns a name or null.
  function tonalName(pcs){
    const u=uniqSort(pcs), n=u.length;
    if(n===2){ let d=mod12(u[1]-u[0]); d=Math.min(d,12-d);
      return ['','minor 2nd / major 7th','major 2nd / minor 7th','minor 3rd / major 6th','major 3rd / minor 6th','perfect 4th / 5th','tritone'][d]||null; }
    const PROTO=[
      ['major triad',[0,4,7]],['minor triad',[0,3,7]],['diminished triad',[0,3,6]],['augmented triad',[0,4,8]],
      ['dominant 7th',[0,4,7,10]],['major 7th',[0,4,7,11]],['minor 7th',[0,3,7,10]],['half-diminished 7th',[0,3,6,10]],
      ['fully diminished 7th',[0,3,6,9]],['minor-major 7th',[0,3,7,11]],['augmented-major 7th',[0,4,8,11]],
      ['pentatonic scale',[0,2,4,7,9]],
      ['whole-tone scale',[0,2,4,6,8,10]],['hexatonic (augmented) scale',[0,1,4,5,8,9]],['chromatic cluster',[0,1,2,3,4,5]],
      ['diatonic scale (major / minor modes)',[0,2,4,5,7,9,11]],['harmonic minor scale',[0,2,3,5,7,8,11]],['melodic minor scale',[0,2,3,5,7,9,11]],
      ['octatonic scale',[0,1,3,4,6,7,9,10]],
      ['harmonic major scale',[0,2,4,5,7,8,11]],['double harmonic / Hungarian minor scale',[0,1,4,5,7,8,11]],
      ['Neapolitan minor scale',[0,1,3,5,7,8,11]],['Neapolitan major scale',[0,1,3,5,7,9,11]],['blues scale (hexatonic)',[0,3,5,6,7,10]]];
    const key=arr=>uniqSort(arr).join(','), target=key(u);
    for(const pr of PROTO){ if(pr[1].length!==n) continue; for(let t=0;t<12;t++){ if(key(pr[1].map(x=>x+t))===target) return pr[0]; } }
    return null;
  }

  // Degrees of symmetry, as in a Forte-style table: how many transpositions Tn and how many
  // inversions TnI map the (unordered) set onto itself. T is always >= 1; I > 0 means the set is
  // inversionally symmetric.
  function symDegrees(pcs){
    const u=uniqSort(pcs), key=a=>uniqSort(a).join(','), t=key(u);
    let T=0,I=0;
    for(let n=0;n<12;n++){ if(key(u.map(x=>x+n))===t) T++; if(key(u.map(x=>n-x))===t) I++; }
    return {T,I};
  }
  function symWord(s){ return s.T>1&&s.I>0?'transpositional + inversional':s.T>1?'transpositional':s.I>0?'inversional':'asymmetric'; }
  const symText = s => `symmetry ${symWord(s)} (T-${s.T}, I-${s.I})`;

  // ---------- text parsing (mixed spelling preserved) ----------
  const NOTE_BASE={c:0,d:2,e:4,f:5,g:7,a:9,b:11};
  function parseNoteEntry(tok){
    const m=tok.match(/^([A-Ga-g])(##|bb|x|#|b|\u266F|\u266D|\u266E)?$/);
    if(!m) return null;
    const L=m[1].toUpperCase(); let pc=NOTE_BASE[m[1].toLowerCase()]; const a=m[2]; let name=null;
    if(a==='#'||a==='\u266F'){pc+=1; name=L+'\u266F';}
    else if(a==='b'||a==='\u266D'){pc-=1; name=L+'\u266D';}
    else if(a==='x'||a==='##'){pc+=2;}
    else if(a==='bb'){pc-=2;}
    else if(!a||a==='\u266E'){name=L;}
    return {pc:mod12(pc), name};
  }
  function parseIntEntry(tok){
    const t=tok.toLowerCase(); let pc=null;
    if(t==='t'||t==='a') pc=10; else if(t==='e'||t==='b') pc=11;
    else if(/^\d{1,2}$/.test(t)){const v=parseInt(t,10); if(v>=0&&v<=11) pc=v;}
    return pc===null?null:{pc,name:null};
  }
  function parseRow(str,mode){
    const toks=str.trim().split(/[\s,;]+/).filter(Boolean);
    if(toks.length===0) return {error:'Enter 12 pitch classes.'};
    // Accept integers regardless of the "Enter with" toggle: if every token reads as a
    // pitch-class integer (0–11, with t = 10 and e = 11), parse as integers; else as note names.
    const useInt = toks.every(t=>parseIntEntry(t)!==null) || mode==='int';
    const out=[];
    for(const tok of toks){
      const e=useInt?parseIntEntry(tok):parseNoteEntry(tok);
      if(!e) return {error:`Couldn't read "${tok}" as ${useInt?'an integer 0–11 (t = 10, e = 11)':'a note name'}.`};
      out.push(e);
    }
    if(out.length>12) return {error:`That's ${out.length} pitch classes — enter at most 12.`};
    const seen=new Set();
    for(const e of out){ if(seen.has(e.pc)) return {error:`${SHARP[e.pc]} appears more than once — use each pitch class at most once.`}; seen.add(e.pc); }
    return {entries:out};
  }

  // ---------- build ----------
  function buildState(pcs, root){
    const N=pcs.length;
    const firstPc=pcs[0];
    const p0=pcs.map(x=>mod12(x-firstPc));
    root=mod12(root||0);                                   // the pitch class the top row (P-root) begins on
    const M=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>mod12(p0[j]-p0[i]+root)));
    const inputRowIndex=M.findIndex(r=>r[0]===firstPc);
    return {input:pcs.slice(), firstPc, p0, M, inputRowIndex, root};
  }
  // Custom mode roots the matrix on the entered row (so it heads the grid as P-firstPc); twelve-tone stays on P0/C.
  function bs(pcs){ return buildState(pcs, mode==='custom' ? mod12(pcs[0]) : 0); }
  function reRoot(delta){ if(!state || (mode!=='twelve'&&mode!=='custom')) return; state=buildState(state.input, mod12(state.root+delta)); renderAll(); }
  function reRootTo(pc){ if(!state || (mode!=='twelve'&&mode!=='custom')) return; state=buildState(state.input, mod12(pc)); renderAll(); }

  // ---------- palette + slots ----------
  function renderPalette(){
    const host=$('palette'); host.innerHTML=''; const used=enteredPcs();
    if(inputMode==='notes'){
      const mkKey=(pc,name)=>{const b=document.createElement('button'); b.className='key'; b.textContent=name; if(used.includes(pc)) b.disabled=true; b.addEventListener('click',()=>addNote(pc,name)); return b;};
      for(const item of NOTE_LAYOUT){
        if(item.nat){ host.appendChild(mkKey(item.nat.pc,item.nat.name)); continue; }
        const p=item.pair;
        const wrap=document.createElement('div'); wrap.className='pair'+(used.includes(p.pc)?' used':'');
        wrap.innerHTML='<svg class="pair-link" viewBox="0 0 100 12" preserveAspectRatio="none" aria-hidden="true"><polyline points="25,11 50,2 75,11" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round" stroke-linecap="round" vector-effect="non-scaling-stroke"/></svg>';
        const keys=document.createElement('div'); keys.className='pair-keys';
        keys.appendChild(mkKey(p.pc,p.sharp)); keys.appendChild(mkKey(p.pc,p.flat));
        wrap.appendChild(keys); host.appendChild(wrap);
      }
    } else {
      for(let pc=0;pc<12;pc++){
        const b=document.createElement('button'); b.className='key int'; b.textContent=String(pc);
        if(used.includes(pc)) b.disabled=true;
        b.addEventListener('click',()=>addNote(pc,null));
        host.appendChild(b);
      }
    }
  }
  function renderSlots(){
    const host=$('slots'); host.innerHTML='';
    for(let k=0;k<ROWLEN;k++){
      const s=document.createElement('div'); const filled=k<entered.length;
      s.className='slot'+(filled?' filled':'')+(k===entered.length && entered.length<ROWLEN?' next':'');
      s.textContent = filled ? (dispMode==='notes'?nameFor(entered[k]):String(entered[k].pc)) : (k===entered.length?'?':'');
      if(filled){ s.dataset.idx=k; s.tabIndex=0; s.setAttribute('role','button'); s.setAttribute('aria-label', (dispMode==='notes'?nameFor(entered[k]):('pitch class '+entered[k].pc))+' — position '+(k+1)+' of '+entered.length+'; drag or use arrow keys to reorder'); }
      host.appendChild(s);
    }
    $('slot-count').textContent=entered.length+' / '+ROWLEN;
    $('undo').disabled  = entered.length===0;
    $('clear').disabled = entered.length===0;
    $('generate').disabled = entered.length!==ROWLEN;
    { const pb=$('play-row'); if(pb) pb.hidden = entered.length===0; }
  }
  function addNote(pc,name){
    if(entered.length>=ROWLEN || enteredPcs().includes(pc)) return;
    entered.push({pc,name}); state=null; genResults=null; const ex=$('ex-note'); if(ex) ex.textContent=''; renderAll();
  }

  // ---------- availability of display controls ----------
  function updateToggles(){
    const lock = !state;
    ['dp-notes','dp-int','sp-sharp','sp-flat'].forEach(id=>{ $(id).disabled=lock; });
    $('seg-disp').classList.toggle('locked',lock);
    $('seg-spell').classList.toggle('locked',lock);
  }
  function pathAvailable(){ return mode==='twelve' || (mode==='custom' && divisorKs(ROWLEN).length>0); }
  function applyPath(){
    const avail=pathAvailable(); if(!avail) genPath=false;
    const sw=$('path-switch'); if(sw) sw.hidden=!avail;
    document.body.classList.toggle('path-generate', avail && genPath);
    document.body.classList.toggle('path-input', !(avail && genPath));
    const ib=$('path-input-btn'), gb=$('path-gen-btn');
    if(ib) ib.setAttribute('aria-pressed', String(!(avail && genPath)));
    if(gb) gb.setAttribute('aria-pressed', String(avail && genPath));
  }

  // ---------- identification ----------
  function renderStatus(){
    const s=$('status');
    if(state){
      const {firstPc,p0}=state;
      const topLabel = mode==='stravinsky' ? 'P0 (array top)' : 'P0 (matrix top)';
      const idLabel  = mode==='stravinsky' ? 'Input hexachord = ' : 'Input row = ';
      const _ident=
        `<div class="ident">
           <div class="big">${idLabel}<b>P${firstPc}</b></div>
           <div class="meta">first pc&nbsp; <span>${firstPc} (${nameFor(entered[0])})</span></div>
           <div class="meta">notes&nbsp; <span>${entered.map(nameFor).join(' ')}</span></div>
           <div class="meta">integers&nbsp; <span>${enteredPcs().join(' ')}</span></div>
           <div class="meta">${topLabel}&nbsp; <span>${p0.join(' ')}</span></div>
         </div>`;
      const _rb=$('rowinfo-body'); if(_rb) _rb.innerHTML=_ident;
      const _ro=$('rowinfo-open'); if(_ro){ _ro.textContent=idLabel+'P'+firstPc; _ro.hidden=false; }
      s.innerHTML='';
    } else {
      { const _ro=$('rowinfo-open'); if(_ro) _ro.hidden=true; }
      const unit = mode==='stravinsky' ? 'hexachord' : 'row';
      const doneMsg = mode==='stravinsky'
        ? `<span class="hint">Hexachord complete — press <b>Generate</b> to build the arrays.</span>`
        : `<span class="hint">Row complete — press <b>Generate</b> to build the matrix.</span>`;
      s.innerHTML = entered.length===ROWLEN ? doneMsg
        : (entered.length===0
            ? `<span class="hint">Click notes to build your ${unit} — used pitches lock so every class is used once.</span>`
            : `<span class="hint">${entered.length} of ${ROWLEN} entered — keep going.</span>`);
    }
  }

  // ---------- matrix ----------
  function clearHi(){ document.querySelectorAll('.cell.hi').forEach(c=>c.classList.remove('hi')); }
  function setReadout(i,j){
    const r=$('readout'); if(!state){r.innerHTML='';return;}
    if(i==null){ const act=(window.matchMedia&&window.matchMedia('(hover: none)').matches)?'Tap':'Hover'; r.innerHTML=`<span class="k">${act} a cell to read its row &amp; column forms; click a P / I / R / RI label to play that form. Your input row is</span> <b>P${state.firstPc}</b>.`; return; }
    const {M}=state, a=M[i][0], b=M[0][j], v=M[i][j];
    r.innerHTML=`<span class="k">row</span> <b>P${a}</b> &nbsp;<span class="k">·</span>&nbsp; <span class="k">col</span> <b>I${b}</b> &nbsp;<span class="k">·</span>&nbsp; <span class="k">cell</span> ${v} (${spellName(v)}) &nbsp;<span class="k">·</span>&nbsp; <span class="k">read ◂ for</span> R${a}<span class="k">, ▴ for</span> RI${b}`;
  }
  // ---------- audio playback (Web Audio, self-contained) ----------
  let audioCtx=null, _seqOsc=[], _seqTimers=[], _playing=false;
  function actx(){ try{ if(!audioCtx) audioCtx=new (window.AudioContext||window.webkitAudioContext)(); if(audioCtx && audioCtx.state==='suspended') audioCtx.resume(); }catch(e){ audioCtx=null; } return audioCtx; }
  function pcFreq(pc){ return 440*Math.pow(2,(mod12(pc)-9)/12); }   // one octave from C4 (pc0)
  function toneAt(ctx,freq,t0,dur,peakOverride){
    // piano-like voice (pure Web Audio, no samples): additive sine partials with a fast
    // hammer attack and continuous exponential decay (no sustain plateau); upper partials
    // decay faster, and a touch of inharmonicity gives the struck-string colour.
    const peak=(typeof peakOverride==='number'?peakOverride:0.13), atk=0.004, tauF=Math.min(0.5,Math.max(0.22,dur*0.85));
    const out=ctx.createGain(); out.gain.setValueAtTime(peak,t0);
    const lp=ctx.createBiquadFilter(); lp.type='lowpass';
    lp.frequency.setValueAtTime(Math.min(ctx.sampleRate/2-1500,freq*6+1800),t0); lp.Q.setValueAtTime(0.5,t0);
    lp.connect(out); out.connect(ctx.destination);
    const parts=[[1,1.0,1.0],[2,0.5,1.3],[3,0.3,1.7],[4,0.17,2.2],[5,0.10,2.8],[6,0.06,3.5],[7,0.035,4.3]];
    const norm=parts.reduce((s,p)=>s+p[1],0), oscs=[];
    for(const pr of parts){ const n=pr[0], a=pr[1], ds=pr[2];
      const f=freq*n*Math.sqrt(1+0.0004*n*n); if(f>=ctx.sampleRate/2-500) continue;
      const o=ctx.createOscillator(); o.type='sine'; o.frequency.setValueAtTime(f,t0);
      const g=ctx.createGain(), tau=tauF/ds;
      g.gain.setValueAtTime(0.0001,t0);
      g.gain.exponentialRampToValueAtTime(Math.max(0.0002,a/norm),t0+atk);
      g.gain.setTargetAtTime(0.0001,t0+atk,tau);
      o.connect(g); g.connect(lp); o.start(t0); o.stop(t0+atk+tau*4+0.08); oscs.push(o);
    }
    return { stop:function(when){ const tt=(typeof when==='number')?when:ctx.currentTime;
      try{ out.gain.cancelScheduledValues(tt); out.gain.setTargetAtTime(0.0001,tt,0.015); }catch(e){}
      oscs.forEach(function(o){ try{ o.stop(tt+0.05); }catch(e){} }); } };
  }
  function setPlayBtn(on){ const b=$('play-row'); if(b){ b.textContent = on?'■ Stop':'▶ Play'; b.classList.toggle('playing',!!on); } }
  function clearPlayHi(){ const s=$('slots'); if(s) s.querySelectorAll('.slot.playing').forEach(x=>x.classList.remove('playing')); }
  function stopSeq(){ _seqTimers.forEach(clearTimeout); _seqTimers=[]; _seqOsc.forEach(o=>{ try{o.stop();}catch(e){} }); _seqOsc=[]; _playing=false; setPlayBtn(false); clearPlayHi(); }
  function playSeq(pcs,opts){ opts=opts||{}; const ctx=actx(); if(!ctx||!pcs||!pcs.length) return; stopSeq(); const dur=opts.dur||0.44, step=dur+(opts.gap||0.03), t0=ctx.currentTime+0.05; _playing=true; setPlayBtn(true); const slots=opts.hi?(function(){const s=$('slots'); return s?Array.from(s.querySelectorAll('.slot')):null;})():null; pcs.forEach((pc,k)=>{ _seqOsc.push(toneAt(ctx,pcFreq(pc),t0+k*step,dur)); if(slots){ const ms=Math.max(0,(t0+k*step-ctx.currentTime)*1000); _seqTimers.push(setTimeout(()=>{ clearPlayHi(); if(slots[k]) slots[k].classList.add('playing'); },ms)); } }); _seqTimers.push(setTimeout(()=>{ _playing=false; setPlayBtn(false); clearPlayHi(); }, (pcs.length*step+0.15)*1000)); }
  function playPitch(pc){ const ctx=actx(); if(!ctx) return; toneAt(ctx,pcFreq(pc),ctx.currentTime+0.01,0.32); }
  function semiFreq(s){ return 440*Math.pow(2,(s-9)/12); }
  function chordVoicing(pcs, inv){ const S=[...new Set(pcs.map(x=>mod12(x)))].sort((a,b)=>a-b); const k=S.length; if(!k) return []; inv=((inv|0)%k+k)%k; const v=[]; for(let j=0;j<k;j++){ const idx=inv+j; v.push(S[idx%k]+12*Math.floor(idx/k)); } return v; }
  function playChord(pcs, inv){ const ctx=actx(); if(!ctx||!pcs||!pcs.length) return; stopSeq(); const v=chordVoicing(pcs, inv||0); if(!v.length) return; const t0=ctx.currentTime+0.05, dur=0.95, pk=0.13*Math.min(1,2.2/v.length); _playing=true; setPlayBtn(true); v.forEach(s=>{ _seqOsc.push(toneAt(ctx,semiFreq(s),t0,dur,pk)); }); _seqTimers.push(setTimeout(()=>{ _playing=false; setPlayBtn(false); }, (dur+0.25)*1000)); }
  function togglePlayRow(){ if(_playing){ stopSeq(); return; } const pcs=enteredPcs(); if(!pcs.length) return; playSeq(pcs,{hi:true}); }

  function renderMatrix(){
    const msec=$('matrix-section');
    const rr=$('mx-reroot'), nt=$('mx-note');
    const canRoot  = (mode==='twelve' || mode==='custom') && !!state;
    const showNote = (mode==='custom') && !!state;
    if(rr) rr.classList.toggle('hidden', !canRoot);
    if(nt) nt.classList.toggle('hidden', !showNote);
    if(mode!=='twelve' && mode!=='custom'){ if(msec) msec.classList.add('hidden'); return; }
    if(msec) msec.classList.remove('hidden');
    const host=$('matrix-host');
    if(!state){
      host.innerHTML=`<div class="empty"><p class="mono">${entered.length===ROWLEN?'Row complete — press Generate to build the matrix.':'Build your row above, then press Generate.'}</p></div>`;
      $('legend').style.display='none'; $('readout').innerHTML=''; return;
    }
    const {M,inputRowIndex,root,firstPc}=state; const N=M.length;
    if(canRoot){
      const lab=$('mx-root-lab'); if(lab) lab.innerHTML='top row <b>P'+root+'</b>'+(dispMode==='notes'?' &middot; '+spellName(root):'');
      const rb=$('mx-reset'); if(rb) rb.textContent=(mode==='custom')?'↺ your row':'↺ P0';
    }
    if(showNote && nt){ nt.innerHTML='This matrix is rooted on your row, so it heads the grid as <b>P'+firstPc+'</b>. Use the arrows to re-root it on any of the twelve transpositions — e.g. <b>P0</b> shows the same matrix as if your row began on C. Re-rooting only renames the P / I / R / RI levels and transposes the pitches shown; your row and its set-class analysis don’t change.'; }
    const mxToggle = canRoot ? '<button type="button" class="iv-toggle" id="mx-iv-toggle" aria-haspopup="dialog" title="Show the directed-interval succession of each row form">Show Intervallic Distances</button>' : '';
    const scroll=document.createElement('div'); scroll.className='matrix-scroll';
    const grid=document.createElement('div'); grid.className='matrix'; grid.style.gridTemplateColumns='var(--label-w) repeat('+N+', var(--cell)) var(--label-w)';
    cellEls=Array.from({length:N},()=>new Array(N));
    const mk=(cls,txt)=>{const d=document.createElement('div'); d.className=cls; if(txt!=null)d.textContent=txt; return d;};

    grid.appendChild(mk('corner tl'));
    for(let j=0;j<N;j++){ const lab=mk('lab top lab-play','I'+M[0][j]); lab.dataset.pcs=M.map(r=>r[j]).join(','); lab.title='Play I'+M[0][j]+' (down this column)'; grid.appendChild(lab); }
    grid.appendChild(mk('corner'));

    for(let i=0;i<N;i++){
      const isIn=i===inputRowIndex;
      { const lab=mk('lab left lab-play'+(isIn?' inrow-lab':''),'P'+M[i][0]); lab.dataset.pcs=M[i].join(','); lab.title='Play P'+M[i][0]+' (this row, left to right)'; grid.appendChild(lab); }
      for(let j=0;j<N;j++){
        const c=mk('cell');
        // the input row preserves the user's chosen spellings
        c.textContent = (isIn && dispMode==='notes') ? nameFor(entered[j]) : showPc(M[i][j]);
        c.dataset.i=i; c.dataset.j=j;
        if(i===j) c.classList.add('diag');
        if(isIn)  c.classList.add('inrow');
        cellEls[i][j]=c; grid.appendChild(c);
      }
      { const lab=mk('lab right lab-play'+(isIn?' inrow-lab':''),'R'+M[i][0]); lab.dataset.pcs=M[i].slice().reverse().join(','); lab.title='Play R'+M[i][0]+' (this row, right to left)'; grid.appendChild(lab); }
    }
    grid.appendChild(mk('corner'));
    for(let j=0;j<N;j++){ const lab=mk('lab bottom lab-play','RI'+M[0][j]); lab.dataset.pcs=M.map(r=>r[j]).slice().reverse().join(','); lab.title='Play RI'+M[0][j]+' (up this column)'; grid.appendChild(lab); }
    grid.appendChild(mk('corner'));
    for(let j=0;j<N;j++) cellEls[0][j].style.borderTop='1px solid var(--line-strong)';

    const hover=e=>{const c=e.target.closest('.cell'); if(!c)return; const i=+c.dataset.i,j=+c.dataset.j; clearHi(); for(let k=0;k<N;k++){cellEls[i][k].classList.add('hi'); cellEls[k][j].classList.add('hi');} setReadout(i,j);};
    grid.addEventListener('mouseover',hover);
    grid.addEventListener('click',hover);
    grid.addEventListener('mouseleave',()=>{clearHi(); setReadout(null);});

    grid.addEventListener('click', e=>{ const c=e.target.closest('.cell'); if(c) playPitch(M[+c.dataset.i][+c.dataset.j]); });
    grid.addEventListener('click', e=>{ const lab=e.target.closest('.lab-play'); if(lab && lab.dataset.pcs) playSeq(lab.dataset.pcs.split(',').map(Number)); });
    scroll.appendChild(grid); host.innerHTML=''; if(mxToggle) host.insertAdjacentHTML('beforeend', mxToggle); host.appendChild(scroll); { const mt=$('mx-iv-toggle'); if(mt) mt.addEventListener('click', openMxIvModal); }
    $('legend').style.display='flex';
    { const li=$('legend-inrow'); if(li) li.style.display=(inputRowIndex>=0)?'':'none'; }
    setReadout(null);
  }

  // ---------- 48 forms ----------
  function decorateFam(box, tag){
    const h3=box.querySelector('h3'); if(!h3) return;
    h3.classList.add('fam-head'); h3.setAttribute('data-fam', tag); h3.setAttribute('role','button'); h3.setAttribute('tabindex','0'); h3.setAttribute('aria-expanded', formOpen[tag]?'true':'false');
    if(!h3.querySelector('.fam-chev')){ const ch=document.createElement('span'); ch.className='fam-chev'; ch.setAttribute('aria-hidden','true'); ch.textContent='\u25be'; h3.appendChild(ch); }
    const body=document.createElement('div'); body.className='fam-body';
    Array.from(box.querySelectorAll(':scope > .fline')).forEach(l=>body.appendChild(l));
    box.appendChild(body);
    if(!formOpen[tag]) box.classList.add('collapsed');
  }
  function renderForms(){
    const sec=$('forms-section'), wrap=$('forms-grid');
    if(mode!=='twelve' && mode!=='custom'){ if(sec) sec.classList.add('hidden'); return; }
    if(!state){ sec.classList.add('hidden'); return; }
    sec.classList.remove('hidden');
    if(mode==='custom'){ renderFormsCustom(); return; }
    { const h2=$('forms-h2'); if(h2) h2.textContent='The 48 row forms'; }
    const {p0,firstPc}=state;
    const P=n=>p0.map(x=>mod12(x+n));
    const I=n=>p0.map(x=>mod12(n-x));
    // ordered symmetry of the row itself: how many of the 48 forms are distinct, and whether the
    // row maps onto its own retrograde (palindrome) or retrograde-inversion.
    const rs=$('row-sym');
    if(rs){
      const forms=[]; for(let n=0;n<12;n++){ forms.push(P(n)); forms.push(I(n)); forms.push(P(n).slice().reverse()); forms.push(I(n).slice().reverse()); }
      const distinct=new Set(forms.map(f=>f.join(','))).size;
      const p0s=p0.join(','); let ri=false,r=false;
      for(let n=0;n<12;n++){ if(I(n).slice().reverse().join(',')===p0s) ri=true; if(P(n).slice().reverse().join(',')===p0s) r=true; }
      const kinds=[]; if(ri) kinds.push('its own retrograde-inversion (RI-symmetric)'); if(r) kinds.push('its own retrograde (palindromic)');
      rs.innerHTML = `<b>${distinct}</b> distinct forms` + (kinds.length
        ? ` — the row is ${kinds.join(' and ')}, so the 48 forms collapse to ${distinct}.`
        : ` — no internal symmetry (all 48 are distinct).`);
    }
    const fams=[
      {name:'Prime',tag:'P',get:P,mark:firstPc},
      {name:'Inversion',tag:'I',get:I,mark:-1},
      {name:'Retrograde',tag:'R',get:n=>P(n).slice().reverse(),mark:-1},
      {name:'Retrograde-Inversion',tag:'RI',get:n=>I(n).slice().reverse(),mark:-1},
    ];
    wrap.innerHTML='';
    for(const f of fams){
      const box=document.createElement('div'); box.className='fam fam-'+f.tag.toLowerCase();
      box.innerHTML=`<h3>${f.name} <span class="tag">${f.tag}0–${f.tag}11</span></h3>`;
      for(let n=0;n<12;n++){
        const line=document.createElement('div'); line.className='fline'+(n===f.mark?' mark':'');
        line.innerHTML=`<span class="flab">${f.tag}${n}</span><span class="fpc">${f.get(n).map(showPc).join(' ')}</span>`;
        line.dataset.pcs=f.get(n).join(','); line.classList.add('playable');
        box.appendChild(line);
      }
      decorateFam(box, f.tag);
      wrap.appendChild(box);
    }
  }

  // ---------- subset analysis (Block 2) ----------
  const segWord=k=>k===2?'dyad':k===3?'trichord':k===4?'tetrachord':k===5?'pentachord':'hexachord';
  const segAbbr=k=>k===2?'Dy':k===3?'Tri':k===4?'Tet':k===5?'Pent':'Hex';
  const divisorKs=N=>[2,3,4,5,6].filter(k=>N%k===0 && k<N);
  function unevenLayouts(N){ const out=[]; (function rec(rem,acc){ if(rem===0){ out.push(acc.slice()); return; } for(const p of [2,3]){ if(p<=rem){ acc.push(p); rec(rem-p,acc); acc.pop(); } } })(N,[]); return out; }
  const cap=s=>s[0].toUpperCase()+s.slice(1);
  const SEG_COLORS=['#4733e6','#bb6c0c','#1f9e57','#c0392b','#2a7de1','#8e44ad'];

  // Pitch-class clock: 0 at twelve o'clock, ascending clockwise. The segment's pcs are drawn as a
  // coloured polygon over the 12 positions, so congruent shapes (rotation = T, reflection = I) line up.
  function clockSVG(pcs, color){
    const S=128, c=S/2, R=c-21, rOn=3.6, rOff=1.7;
    const pos=(p,rad)=>{const a=(-90+p*30)*Math.PI/180; return [c+rad*Math.cos(a), c+rad*Math.sin(a)];};
    const set=new Set(uniqSort(pcs));
    const sorted=uniqSort(pcs);
    const pts=sorted.map(p=>{const[x,y]=pos(p,R);return `${x.toFixed(1)},${y.toFixed(1)}`;}).join(' ');
    const poly = sorted.length>=2 ? `<polygon points="${pts}" fill="${color}" fill-opacity="0.12" stroke="${color}" stroke-width="1.5" stroke-linejoin="round"/>` : '';
    let dots='',labels='';
    for(let p=0;p<12;p++){
      const on=set.has(p), [x,y]=pos(p,R), [lx,ly]=pos(p,R+11);
      dots+=`<circle cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="${on?rOn:rOff}" fill="${on?color:'#cfd0cb'}"/>`;
      labels+=`<text x="${lx.toFixed(1)}" y="${(ly+3).toFixed(1)}" text-anchor="middle" font-size="8.5" font-family="ui-monospace,Menlo,Consolas,monospace" fill="${on?color:'#a4a6ac'}">${showPc(p)}</text>`;
    }
    return `<svg viewBox="0 0 ${S} ${S}" width="${S}" height="${S}" class="clock-svg" role="img"><circle cx="${c}" cy="${c}" r="${R}" fill="none" stroke="#e5e5e1" stroke-width="1"/>${poly}${dots}${labels}</svg>`;
  }

  function combPanel(){
    const {p0,input,firstPc}=state;
    const comp=new Set(input.slice(6));
    const P=n=>p0.map(x=>mod12(x+n)), I=n=>p0.map(x=>mod12(n-x));
    const fams={P:n=>P(n), I:n=>I(n), R:n=>P(n).slice().reverse(), RI:n=>I(n).slice().reverse()};
    const setEq=(a,b)=>{if(a.size!==b.size)return false;for(const x of a)if(!b.has(x))return false;return true;};
    const hits={P:[],I:[],R:[],RI:[]};
    for(const fam of ['P','I','R','RI']) for(let n=0;n<12;n++){const fh=new Set(fams[fam](n).slice(0,6)); if(setEq(fh,comp)) hits[fam].push(fam+n);}
    const present=['P','I','R','RI'].filter(f=>hits[f].length>0);
    const meaningful=present.filter(f=>f!=='R');
    let headline;
    if(present.length===4) headline='All-combinatorial hexachord';
    else if(meaningful.length===1) headline=meaningful[0]+'-combinatorial (semi-combinatorial)';
    else if(meaningful.length>1) headline=meaningful.join(' & ')+'-combinatorial';
    else headline='Not combinatorial (only the universal R)';
    const pf1=primeForm(input.slice(0,6)), pf2=primeForm(input.slice(6));
    const scRel = pf1.join()===pf2.join()
      ? `Discrete hexachords are the <b>same set class</b> (${pf1.map(pcTok).join('')}) — complementary.`
      : `Discrete hexachords are <b>Z-related</b>: (${pf1.map(pcTok).join('')}) and (${pf2.map(pcTok).join('')}) — same ic vector, complementary.`;
    const box=document.createElement('div'); box.className='comb-box';
    box.innerHTML=`<div class="ctype"><b>${headline}</b></div><div class="comb-rel">${scRel}</div>`;
    for(const f of ['P','I','R','RI']){
      const line=document.createElement('div'); line.className='comb-line';
      line.innerHTML=`<span class="cf">${f}-combinatorial</span><span class="cv">${hits[f].length?hits[f].join(', '):'\u2014'}</span>`;
      box.appendChild(line);
    }
    const note=document.createElement('div'); note.className='comb-note';
    note.textContent='A form is combinatorial with your row (P'+firstPc+') when its first six notes complete the aggregate against your first hexachord. Every row is trivially R-combinatorial.';
    box.appendChild(note);
    return box;
  }

  // Uneven sets: collection length has no equal segmentation into dyad..hexachord cells.
  // Show the whole-set identity + clock, then every consecutive dyad/trichord layout (no segment
  // relationships, since the cells are not uniform). Used by the Custom Row Analyser (lengths 5/7/11).
  function buildUnevenInto(body, row){
    const dom=[]; row.forEach(pc=>{ const m=mod12(pc); if(!dom.includes(m)) dom.push(m); });
    const N=dom.length;
    const pf=primeForm(dom), fn=forteName(dom), v=icVector(dom), tn=tonalName(dom);
    const head=document.createElement('div'); head.className='sc-summary';
    head.innerHTML='This '+N+'-note set is <b>('+pf.map(pcTok).join('')+')</b>'+(fn?' '+fn:'')+(tn?' · '+tn:'')+', ic vector ['+v.join('')+'] — it has no equal division into dyads, trichords, tetrachords, pentachords or hexachords, so it is read as <b>uneven</b>. Each consecutive grouping is shown below with full set-class detail.';
    body.appendChild(head);
    const clkHead=document.createElement('div'); clkHead.className='panel-head'; clkHead.style.margin='16px 0 8px';
    clkHead.innerHTML='<h2 style="font-size:12px">Clock view</h2><span class="hint">the whole set on the pitch-class clock</span>';
    body.appendChild(clkHead);
    const clk=document.createElement('div'); clk.className='clock-row';
    const cell=document.createElement('div'); cell.className='clock-cell';
    cell.innerHTML=clockSVG(dom, SEG_COLORS[0])+'<div class="cpcs">'+dom.map(showPc).join(' ')+'</div>'+(tn?'<div class="cname" style="color:'+SEG_COLORS[0]+'">'+tn+'</div>':'');
    clk.appendChild(cell); body.appendChild(clk);
    const layouts=unevenLayouts(N);
    const lh=document.createElement('div'); lh.className='panel-head'; lh.style.margin='20px 0 8px';
    lh.innerHTML='<h2 style="font-size:12px">Subset layouts</h2><span class="hint">each consecutive dyad / trichord grouping, with the same set-class detail as a normal row</span>';
    body.appendChild(lh);
    if(!layouts.length){ const none=document.createElement('div'); none.className='sc-summary none'; none.innerHTML='No dyad/trichord layout fits this length.'; body.appendChild(none); return; }
    layouts.forEach(parts=>{
      const block=document.createElement('div'); block.className='uneven-layout';
      const t=document.createElement('div'); t.className='ul-title'; t.textContent=parts.map(p=>cap(segWord(p))).join(' + '); block.appendChild(t);
      const segs=[]; { let pos=0; parts.forEach(p=>{ segs.push(dom.slice(pos,pos+p)); pos+=p; }); }
      // compact overview strip (coloured cells)
      const strip=document.createElement('div'); strip.className='seg-strip';
      const tcA={};
      segs.forEach((seg,idx)=>{
        const p=parts[idx]; tcA[p]=(tcA[p]||0)+1; const col=SEG_COLORS[idx%SEG_COLORS.length];
        const g=document.createElement('div'); g.className='seg-grp';
        g.innerHTML='<span class="glab" style="color:'+col+'">'+segAbbr(p)+'-'+tcA[p]+'</span>';
        const cells=document.createElement('div'); cells.className='gcells';
        seg.forEach(pc=>{const c=document.createElement('div'); c.className='seg-cell'; c.textContent=showPc(pc); cells.appendChild(c);});
        g.appendChild(cells);
        const tnn=tonalName(seg); if(tnn){const nm=document.createElement('span'); nm.className='gname'; nm.style.color=col; nm.textContent=tnn; g.appendChild(nm);}
        strip.appendChild(g);
      });
      block.appendChild(strip);
      // full detailed set-class cards — same format as a normal row's segments
      const cards=document.createElement('div'); cards.className='sc-cards';
      const tcB={};
      segs.forEach((seg,idx)=>{ const p=parts[idx]; tcB[p]=(tcB[p]||0)+1; cards.appendChild(scCard(seg, cap(segWord(p))+' '+tcB[p])); });
      block.appendChild(cards);
      body.appendChild(block);
    });
  }
  function renderSubset(){
    const sec=$('subset-section');
    if(mode!=='twelve' && mode!=='stravinsky' && mode!=='custom'){ if(sec) sec.classList.add('hidden'); return; }
    if(!state){sec.classList.add('hidden');return;} sec.classList.remove('hidden');
    // each analysed unit is 12 notes (twelve-tone row) or 6 (a Stravinsky row/vertical hexachord)
    const N = (mode==='stravinsky') ? 6 : state.input.length;
    const validKs=divisorKs(N);
    const useUneven=validKs.length===0;
    ['2','3','4','5','6'].forEach(k=>{ const b=$('ss-'+k); if(b) b.classList.toggle('hidden', !validKs.includes(+k)); });
    { const ub=$('ss-uneven'); if(ub) ub.classList.toggle('hidden', !useUneven); }
    { const ib=$('ss-imbricate'); if(ib){ const _si=(mode==='twelve'||mode==='custom')&&!useUneven; ib.classList.toggle('hidden',!_si); ib.setAttribute('aria-pressed', String(_si&&imbricate)); } }
    if(useUneven){ ['2','3','4','5','6'].forEach(k=>{ const b=$('ss-'+k); if(b) b.setAttribute('aria-pressed','false'); }); const ub=$('ss-uneven'); if(ub) ub.setAttribute('aria-pressed','true'); }
    else { if(!validKs.includes(subsetK)) subsetK = validKs.includes(3)?3:validKs[0]; ['2','3','4','5','6'].forEach(k=>{ const b=$('ss-'+k); if(b) b.setAttribute('aria-pressed', String(+k===subsetK)); }); const ub=$('ss-uneven'); if(ub) ub.setAttribute('aria-pressed','false'); }
    const hint=$('subset-hint'); if(hint) hint.textContent = (mode==='stravinsky'
        ? 'pick a row or vertical hexachord, then segment it'
        : ((imbricate&&!useUneven)?'overlapping (imbricated) segments of your row':'discrete segments of your row'))+' \u00b7 set classes & relationships';
    const body=$('subset-body'); body.innerHTML='';
    if(mode==='stravinsky'){ renderStravSubsetInto(body); return; }
    if(useUneven){ buildUnevenInto(body, state.input); return; }
    buildSubsetInto(body, state.input, subsetK);
    if(subsetK===6 && !imbricate) body.appendChild(combPanel());
  }

  // renders the discrete-segment analysis (strip · cards · summary · clock · relationships) of an ordered pc array.
  // Repeated pitch classes are collapsed first (a vertical such as [1,1,1,1,1,7] is the dyad {1,7}), so a
  // segment is never padded with duplicate notes; if the collapsed collection is too small to fill the chosen
  // segment size, a "No <size>s" notice is shown instead of degenerate cards.
  // one detailed set-class card (Forte tag, pcs, normal, prime, ic vector, symmetry) for a segment
  function scCard(seg, headLabel){
    const nf=normalForm(seg), pf=primeForm(seg), v=icVector(seg), fn=forteName(seg), tn=tonalName(seg), sy=symDegrees(seg);
    const card=document.createElement('div'); card.className='sc-card';
    const _ord=['','1st','2nd','3rd']; let invBtns=''; if(seg.length>=2&&seg.length<=4){ for(let _i=1;_i<seg.length;_i++) invBtns+='<button type="button" class="seg-play seg-inv" data-pcs="'+seg.join(',')+'" data-pl="chord" data-inv="'+_i+'" title="Play as a chord, '+_ord[_i]+' inversion" aria-label="Play chord '+_ord[_i]+' inversion">'+_ord[_i]+'</button>'; }
    const invRow = invBtns ? '<span class="inv-row">'+invBtns+'</span>' : '';
    card.innerHTML=`<h4><span class="card-hl"><span class="card-title">${headLabel}</span><span class="tag">${fn||'set class'}</span></span><span class="seg-pl"><button type="button" class="seg-play" data-pcs="${seg.join(',')}" data-pl="line" title="Play melodically — one note after another" aria-label="Play segment as a line"><svg class="pl-ic" width="14" height="14" viewBox="0 0 16 16" aria-hidden="true"><polyline points="3,11.5 8,8 13,4.5" fill="none" stroke="currentColor" stroke-width="1.2" stroke-linecap="round" stroke-linejoin="round"/><circle cx="3" cy="11.5" r="1.7" fill="currentColor"/><circle cx="8" cy="8" r="1.7" fill="currentColor"/><circle cx="13" cy="4.5" r="1.7" fill="currentColor"/></svg>line</button><button type="button" class="seg-play seg-chord" data-pcs="${seg.join(',')}" data-pl="chord" title="Play as a chord — close position, all notes together" aria-label="Play segment as a chord"><svg class="pl-ic" width="14" height="14" viewBox="0 0 16 16" aria-hidden="true"><line x1="10.6" y1="3.2" x2="10.6" y2="13" stroke="currentColor" stroke-width="1.1" stroke-linecap="round"/><circle cx="7.6" cy="4.2" r="1.85" fill="currentColor"/><circle cx="7.6" cy="8" r="1.85" fill="currentColor"/><circle cx="7.6" cy="11.8" r="1.85" fill="currentColor"/></svg>chord</button></span>${invRow}</h4>`+
      (tn?`<div class="sc-row"><span class="k">name</span><span class="v sc-name">${tn}</span></div>`:'')+
      `<div class="sc-row"><span class="k">pcs</span><span class="v">${seg.map(showPc).join(' ')}</span></div>`+
      `<div class="sc-row"><span class="k">normal</span><span class="v">[${nf.map(pcTok).join(',')}]</span></div>`+
      `<div class="sc-row"><span class="k">prime</span><span class="v">(${pf.map(pcTok).join('')})</span></div>`+
      `<div class="sc-row"><span class="k">ic vector</span><span class="v">[${v.join('')}]</span></div>`+
      `<div class="sc-row"><span class="k">symmetry</span><span class="v">${symWord(sy)} <span class="sc-sym">T-${sy.T}·I-${sy.I}</span></span></div>`;
    return card;
  }
  function buildSubsetInto(body, row, k){
    const ab=segAbbr(k);
    const dom=[]; row.forEach(pc=>{ const m=mod12(pc); if(!dom.includes(m)) dom.push(m); }); // distinct pcs, order of first appearance
    const count=Math.floor(dom.length/k);
    if(count===0){
      const none=document.createElement('div'); none.className='sc-summary none';
      none.innerHTML=`<b>No ${cap(segWord(k))}s.</b> This collection reduces to <b>${dom.length}</b> distinct pitch ${dom.length===1?'class':'classes'} (${dom.map(showPc).join(' ')}) \u2014 too few to form a ${segWord(k)}.`;
      body.appendChild(none);
      return;
    }
    const segs=[]; if(imbricate){ for(let i=0;i+k<=dom.length;i++) segs.push(dom.slice(i,i+k)); } else { for(let i=0;i<count;i++) segs.push(dom.slice(i*k,(i+1)*k)); }

    const strip=document.createElement('div'); strip.className='seg-strip';
    segs.forEach((seg,idx)=>{
      const col=SEG_COLORS[idx%SEG_COLORS.length];
      const g=document.createElement('div'); g.className='seg-grp';
      g.innerHTML=`<span class="glab" style="color:${col}">${ab}-${idx+1}</span>`;
      const cells=document.createElement('div'); cells.className='gcells';
      seg.forEach(pc=>{const c=document.createElement('div'); c.className='seg-cell'; c.textContent=showPc(pc); cells.appendChild(c);});
      g.appendChild(cells);
      const tn=tonalName(seg); if(tn){const nm=document.createElement('span'); nm.className='gname'; nm.style.color=col; nm.textContent=tn; g.appendChild(nm);}
      strip.appendChild(g);
    });
    body.appendChild(strip);

    const cards=document.createElement('div'); cards.className='sc-cards';
    segs.forEach((seg,idx)=>{ cards.appendChild(scCard(seg, cap(segWord(k))+' '+(idx+1))); });
    body.appendChild(cards);

    const pfStrs=segs.map(s=>primeForm(s).join(',')); const distinct=[...new Set(pfStrs)];
    const summ=document.createElement('div');
    if(count===1){
      const pf=primeForm(segs[0]), fn=forteName(segs[0]);
      summ.className='sc-summary';
      summ.innerHTML=`This ${segWord(k)} is <b>(${pf.map(pcTok).join('')})</b>${fn?' '+fn:''}, ic vector [${icVector(segs[0]).join('')}].`;
    } else if(distinct.length===1){
      const pf=primeForm(segs[0]), fn=forteName(segs[0]);
      summ.className='sc-summary derived';
      let lead;
      if(k===2) lead=`All ${count} dyads share one interval class`;
      else if(count===2) lead=`Both ${segWord(k)}s belong to the same set class`;
      else lead=`All ${count} ${segWord(k)}s belong to one set class — this is a <b>derived row</b>`;
      summ.innerHTML=`${lead}: <b>(${pf.map(pcTok).join('')})</b>${fn?' '+fn:''}, ic vector [${icVector(segs[0]).join('')}].`;
    } else {
      summ.className='sc-summary';
      const items=distinct.map(d=>{const arr=d.split(',').map(Number);const fn=forteName(arr);return `(${arr.map(pcTok).join('')})${fn?' '+fn:''}`;});
      summ.innerHTML=`The ${count} ${segWord(k)}s use <b>${distinct.length}</b> distinct set classes: ${items.join(' \u00b7 ')}.`;
    }
    body.appendChild(summ);

    // ---- clock view: each segment on the pitch-class clock ----
    const clkHead=document.createElement('div'); clkHead.className='panel-head'; clkHead.style.margin='20px 0 8px';
    clkHead.innerHTML=`<h2 style="font-size:12px">Clock view</h2><span class="hint">each ${segWord(k)} on the pitch-class clock — congruent shapes are T- or I-related</span>`;
    body.appendChild(clkHead);
    const clk=document.createElement('div'); clk.className='clock-row';
    segs.forEach((seg,idx)=>{
      const col=SEG_COLORS[idx%SEG_COLORS.length];
      const cell=document.createElement('div'); cell.className='clock-cell';
      const tn=tonalName(seg);
      cell.innerHTML=`<div class="clab" style="color:${col}">${ab}-${idx+1}</div>`+clockSVG(seg,col)+
        `<div class="cpcs">${seg.map(showPc).join(' ')}</div>`+(tn?`<div class="cname" style="color:${col}">${tn}</div>`:'');
      clk.appendChild(cell);
    });
    body.appendChild(clk);

    // ---- all-pairs relationships: T_n / T_nI mapping each row-segment's pitch-class SET onto each column-segment's ----
    if(count>=2){
      const relHead=document.createElement('div'); relHead.className='panel-head'; relHead.style.margin='20px 0 8px';
      relHead.innerHTML=`<h2 style="font-size:12px">Segment relationships</h2><span class="hint">transposition (T<sub>n</sub>) &amp; inversion (T<sub>n</sub>I) relating each segment\u2019s pitch-class set to another</span>`;
      body.appendChild(relHead);
      const mtx=document.createElement('table'); mtx.className='rel-table rel-matrix';
      let head='<tr><th></th>'+segs.map((s,j)=>`<th style="color:${SEG_COLORS[j%SEG_COLORS.length]}">${ab}-${j+1}</th>`).join('')+'</tr>';
      let rowsHtml='';
      segs.forEach((si,i)=>{
        let tds='';
        segs.forEach((sj,j)=>{
          if(i===j){ tds+='<td class="diag">\u2014</td>'; return; }
          const r=segRelations(si,sj);
          tds+=`<td class="rel">${r.length?r.join(' '):'\u00b7'}</td>`;
        });
        rowsHtml+=`<tr><th class="rowh" style="color:${SEG_COLORS[i%SEG_COLORS.length]}">${ab}-${i+1}</th>${tds}</tr>`;
      });
      mtx.innerHTML=head+rowsHtml;
      { const relWrap=document.createElement('div'); relWrap.className='rel-scroll'; relWrap.appendChild(mtx); body.appendChild(relWrap); }
      const relNote=document.createElement('div'); relNote.className='rel-note';
      relNote.innerHTML='Read row \u2192 column. <b>T<sub>n</sub></b> = transposition, <b>T<sub>n</sub>I</b> = inversion (the <b>I</b> denotes inversion). An <b>asterisk</b> (e.g. T<sub>n</sub>*) marks an <b>ordered</b> relationship \u2014 the operation maps the segments note-for-note in the same order. Operators <b>without</b> an asterisk are unordered: they relate the segments only as pitch-class sets (same collection, different order). <b>\u00b7</b> = unrelated (different set class). The diagonal is each segment with itself.';
      body.appendChild(relNote);
    }
  }

  // Stravinsky subset analysis: pick any row (degree) or vertical hexachord of the current form, then segment it
  function renderStravSubsetInto(body){
    const h=state.input.slice(), fh=stravFormHex(h,stravForm), arr=rotArray(fh), N=fh.length;
    const rows=arr.map((r,i)=>({kind:'row', idx:i, label:ROMAN[i], pcs:r.pcs.slice()}));
    const cols=[]; for(let j=0;j<N;j++) cols.push({kind:'col', idx:j, label:'v'+(j+1), pcs:arr.map(r=>r.pcs[j])});
    { const cur=(stravPick.kind==='col'?cols:rows).find(x=>x.idx===stravPick.idx); if(!cur || new Set(cur.pcs).size===1){ const ok=rows.find(r=>new Set(r.pcs).size>1) || cols.find(c=>new Set(c.pcs).size>1); if(ok) stravPick={kind:ok.kind, idx:ok.idx}; } } // v1 is one pitch class — not selectable

    const pick=document.createElement('div'); pick.className='hexpick';
    const mkGroup=(title, items)=>{
      const grp=document.createElement('div'); grp.className='hp-group';
      grp.innerHTML=`<div class="hp-glabel">${title}</div>`;
      const wrap=document.createElement('div'); wrap.className='hp-cards';
      items.forEach(it=>{
        const isV1 = new Set(it.pcs).size===1;
        const sel  = !isV1 && stravPick.kind===it.kind && stravPick.idx===it.idx;
        const d=[...new Set(it.pcs)], cpf=primeForm(d), cfn=forteName(d);
        const scTxt = isV1 ? 'single pc' : `(${cpf.map(pcTok).join('')})${cfn?' '+cfn:''}`;
        const btn=document.createElement('button'); btn.type='button'; btn.className='hp-card'+(isV1?' off':'');
        if(sel) btn.setAttribute('aria-pressed','true');
        if(isV1) btn.disabled=true; else { btn.dataset.kind=it.kind; btn.dataset.idx=String(it.idx); }
        btn.innerHTML=`<span class="hp-k">${it.label}</span><span class="hp-p">${d.map(showPc).join(' ')}</span><span class="hp-sc">${scTxt}</span>`;
        wrap.appendChild(btn);
      });
      grp.appendChild(wrap); return grp;
    };
    pick.appendChild(mkGroup('Rows \u2014 read as melodies (the degrees I\u2013VI)', rows));
    pick.appendChild(mkGroup('Verticals \u2014 columns read as harmonies', cols));
    body.appendChild(pick);
    pick.querySelectorAll('.hp-card:not([disabled])').forEach(b=>b.addEventListener('click',()=>{ stravPick={kind:b.dataset.kind, idx:+b.dataset.idx}; renderSubset(); }));

    const selItem = (stravPick.kind==='col'?cols:rows).find(x=>x.idx===stravPick.idx) || rows[0];
    const selPcs=selItem.pcs.slice();
    const dd=[...new Set(selPcs)], spf=primeForm(dd), sfn=forteName(dd), sv=icVector(dd);
    const selHead=document.createElement('div'); selHead.className='hp-selhead';
    selHead.innerHTML=`<span class="hp-selk">${stravPick.kind==='col'?'Vertical '+selItem.label:'Row '+selItem.label} \u2014 ${stravForm} form</span>`+
      `<span class="hp-selp">${dd.map(showPc).join(' ')}</span>`+
      `<span class="hp-selsc">(${spf.map(pcTok).join('')})${sfn?' '+sfn:''} \u00b7 ic [${sv.join('')}]</span>`;
    body.appendChild(selHead);

    const bd=document.createElement('div'); body.appendChild(bd);
    if(dd.length===5){
      // pentachord collapse — 5 distinct pcs have no equal division into dyad..hexachord cells,
      // so route through the Uneven-sets gate + display (the same one the Custom analyser uses)
      // and override the size selector to match. Only pentachords are handled this way.
      ['2','3','4','5','6'].forEach(k=>{ const b=$('ss-'+k); if(b){ b.classList.add('hidden'); b.setAttribute('aria-pressed','false'); } });
      const ub=$('ss-uneven'); if(ub){ ub.classList.remove('hidden'); ub.setAttribute('aria-pressed','true'); }
      buildUnevenInto(bd, selPcs);
    } else {
      buildSubsetInto(bd, selPcs, subsetK);
    }
  }

  // ---------- row generator: derivation from the entered cell (Block 3) ----------
  const genShow = pc => inputMode==='notes' ? spellName(pc) : String(pc);
  const famOf = lab => lab.match(/^[A-Z]+/)[0];
  const CELL_SIZES = [2,3,4,6];
  const cellName = k => k===2?'dyad':k===3?'trichord':k===4?'tetrachord':k===5?'pentachord':'hexachord';
  const sizeListWord = ks => ks.length<=1 ? (ks[0]+'-note') : ks.length===2 ? (ks[0]+'- or '+ks[1]+'-note') : (ks.slice(0,-1).join('-, ')+'-, or '+ks[ks.length-1]+'-note');

  // The cell is the notes entered above. We show set identity for ANY 2–11-note subset; the
  // derivation controls (and Generate) are enabled only for a true 2 / 3 / 4 / 6-note cell.
  const cellWord = n => divisorKs(ROWLEN).includes(n)?cellName(n):(n+'-note set');
  function updateDeriveZone(){
    const zone=$('derive-zone'), hint=$('dz-hint'); if(!zone||!hint) return;
    if(mode!=='twelve' && mode!=='custom'){ zone.classList.add('hidden'); hint.classList.add('hidden'); return; }
    const sizes=divisorKs(ROWLEN);
    if(mode==='custom' && sizes.length===0){ zone.classList.add('hidden'); hint.classList.add('hidden'); return; }
    const target=ROWLEN;
    const n=entered.length, isCell=sizes.includes(n), hasSet=n>=2 && n<target;
    zone.classList.toggle('hidden', !hasSet);
    hint.classList.toggle('hidden', hasSet || n===12 || n===0);
    if(!hint.classList.contains('hidden')){
      hint.textContent = `${n} note${n===1?'':'s'} entered — add up to ${target===12?'twelve':target} for the full ${mode==='custom'?'row':'matrix'}.`;
    }
    const ctrl=$('dz-ctrl'); if(ctrl) ctrl.hidden = !isCell;
    const na=$('dz-na');     if(na){ na.hidden = !(hasSet && !isCell);
      if(!na.hidden) na.textContent = `Identity shown below — deriving ${target===12?'a twelve-tone':'this '+target+'-note'} row needs a ${sizeListWord(sizes)} set.`; }
    const info=$('gen-scinfo');
    if(info){
      if(hasSet){
        const pcs=enteredPcs(), pf=primeForm(pcs), fn=forteName(pcs), tn=tonalName(pcs), sy=symDegrees(pcs);
        const head = tn ? `<b>${tn}</b> · ${cellWord(n)}` : `<b>${cellWord(n)}</b>`;
        info.innerHTML=`these ${n} notes — ${head} (${pf.map(pcTok).join('')})${fn?' '+fn:''} · ic vector [${icVector(pcs).join('')}] · ${symText(sy)}`;
      } else info.textContent='';
    }
    const anyOp = genOps.T||genOps.I||genOps.R||genOps.RI;
    const run=$('gen-run'); if(run) run.disabled = !isCell || !anyOp;
    const note=$('dz-note'); if(note) note.textContent = (isCell && !anyOp)
      ? 'Select at least one operation — T / I / R / RI — to generate.'
      : `or keep adding notes to ${target===12?'twelve':target} for the ${mode==='custom'?'row':'matrix'}`;
  }

  function deriveRows(cellPcs, ops, capN){
    const k=cellPcs.length, m=ROWLEN/k;
    const forms=cellForms(cellPcs).filter(lf=>ops[famOf(lf[0])]);
    const used=new Set(cellPcs);
    if(used.size!==k) return {results:[],truncated:false};
    const results=[]; const seq=[{label:'cell',pcs:cellPcs.slice()}]; let steps=0, truncated=false;
    (function bt(){
      if(truncated||results.length>=capN) return;
      if(seq.length===m){ results.push(seq.map(s=>({label:s.label,pcs:s.pcs.slice()}))); return; }
      for(const lf of forms){
        if(++steps>3e6){ truncated=true; return; }
        const pcs=lf[1]; let ok=true;
        for(const p of pcs){ if(used.has(p)){ ok=false; break; } }
        if(!ok) continue;
        for(const p of pcs) used.add(p);
        seq.push({label:lf[0],pcs});
        bt();
        seq.pop();
        for(const p of pcs) used.delete(p);
        if(truncated||results.length>=capN) return;
      }
    })();
    return {results,truncated};
  }

  function runGen(){
    if(mode!=='twelve' && mode!=='custom') return;
    const pcs=enteredPcs();
    if(!divisorKs(ROWLEN).includes(pcs.length)) return;
    const CAP=80;
    const r=deriveRows(pcs,genOps,CAP);
    genResults={results:r.results, truncated:r.truncated, cap:CAP};
    renderGenResults();
  }

  function renderGenResults(){
    const host=$('gen-body'); if(!host) return; host.innerHTML='';
    if(mode!=='twelve' && mode!=='custom') return;
    if(!genResults) return;
    const {results,truncated,cap}=genResults;
    if(results.length===0){
      const e=document.createElement('div'); e.className='gen-empty';
      e.textContent=`No ${ROWLEN===12?'12-tone':ROWLEN+'-note'} row can be tiled from this set with the allowed operations. Try enabling more of T / I / R / RI, or a different set.`;
      host.appendChild(e); return;
    }
    const c=document.createElement('div'); c.className='gen-count';
    c.innerHTML=`<b>${results.length}${truncated?'+':''}</b> row${results.length===1?'':'s'} found — each begins with your set${truncated?`; showing first ${cap}`:''}.`;
    host.appendChild(c);
    { const ca=document.createElement('button'); ca.className='gen-copyall'; ca.textContent='Copy all'; ca.title='Copy all rows as text'; ca.addEventListener('click',()=>{ const txt=results.map(seqArr=>{ const rp=seqArr.flatMap(s=>s.pcs); const ops=seqArr.map((s,i)=>i===0?'cell':s.label).join(' \u00b7 '); return rp.map(genShow).join(' ')+'   ('+ops+')'; }).join('\n'); copyBtn(ca,txt); }); c.appendChild(ca); }
    results.forEach(seqArr=>{
      const rowPcs=seqArr.flatMap(s=>s.pcs);
      const item=document.createElement('div'); item.className='gen-item';
      const ops=document.createElement('div'); ops.className='gen-ops';
      seqArr.forEach((s,i)=>{const chip=document.createElement('span'); chip.className='gen-op'+(i===0?' cell':''); chip.textContent=i===0?'cell':s.label; ops.appendChild(chip);});
      item.appendChild(ops);
      const pcs=document.createElement('div'); pcs.className='gen-pcs'; pcs.textContent=rowPcs.map(genShow).join(' ');
      item.appendChild(pcs);
      const load=document.createElement('button'); load.className='gen-load'; load.textContent='Load into matrix';
      load.addEventListener('click',()=>{ entered=rowPcs.map(pc=>({pc,name:null})); state=bs(rowPcs); genResults=null; expandSections(); renderAll(); const t=$('matrix-section'); if(t) t.scrollIntoView({behavior:'smooth',block:'start'}); });
      item.appendChild(load);
      host.appendChild(item);
    });
  }

  // ---------- Block 4: generate fresh constrained rows ----------
  function shuffle(a){a=a.slice();for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));const t=a[i];a[i]=a[j];a[j]=t;}return a;}
  const SOURCE_HEX=[
    {id:'6-1', name:'chromatic',  prime:[0,1,2,3,4,5]},
    {id:'6-7', name:'',           prime:[0,1,2,6,7,8]},
    {id:'6-8', name:'',           prime:[0,2,3,4,5,7]},
    {id:'6-20',name:'hexatonic',  prime:[0,1,4,5,8,9]},
    {id:'6-32',name:'diatonic',   prime:[0,2,4,5,7,9]},
    {id:'6-35',name:'whole-tone', prime:[0,2,4,6,8,10]}
  ];
  // all-interval rows beginning on 0 — the 11 successive intervals are a permutation of 1..11.
  let AI_COUNT=null;
  function countAllInterval(){
    if(AI_COUNT!=null) return AI_COUNT;
    let count=0; const row=[0]; const upc=new Array(12).fill(false); upc[0]=true; const uiv=new Array(12).fill(false);
    (function bt(){ if(row.length===12){count++;return;} const prev=row[row.length-1];
      for(let iv=1;iv<=11;iv++){ if(uiv[iv])continue; const pc=mod12(prev+iv); if(upc[pc])continue; uiv[iv]=true;upc[pc]=true;row.push(pc); bt(); row.pop();upc[pc]=false;uiv[iv]=false; } })();
    AI_COUNT=count; return count;
  }
  function sampleAllInterval(limit){
    const out=[]; const row=[0]; const upc=new Array(12).fill(false);upc[0]=true; const uiv=new Array(12).fill(false); let stop=false;
    (function bt(){ if(stop)return; if(row.length===12){out.push(row.slice()); if(out.length>=limit)stop=true; return;}
      const prev=row[row.length-1]; for(const iv of shuffle([1,2,3,4,5,6,7,8,9,10,11])){ if(uiv[iv])continue; const pc=mod12(prev+iv); if(upc[pc])continue; uiv[iv]=true;upc[pc]=true;row.push(pc); bt(); row.pop();upc[pc]=false;uiv[iv]=false; if(stop)return; } })();
    return out;
  }
  function genAllComb(sourceId, limit){
    const pool = sourceId==='any' ? SOURCE_HEX : SOURCE_HEX.filter(s=>s.id===sourceId);
    const out=[]; const seen=new Set(); let guard=0;
    while(out.length<limit && guard<limit*80){ guard++;
      const src=pool[Math.floor(Math.random()*pool.length)];
      const base = Math.random()<0.5 ? src.prime.map(x=>mod12(-x)) : src.prime.slice();
      const t=Math.floor(Math.random()*12);
      const A=uniqSort(base.map(x=>mod12(x+t))); if(A.length!==6) continue;
      const Aset=new Set(A); const B=[]; for(let p=0;p<12;p++) if(!Aset.has(p)) B.push(p);
      const pcs=shuffle(A).concat(shuffle(B)); const key=pcs.join(',');
      if(seen.has(key)) continue; seen.add(key);
      out.push({pcs, src});
    }
    return out;
  }
  function genRISymN(N, limit){
    const out=[], seen=new Set(); let guard=0, odd=N%2===1;
    while(out.length<limit && guard<limit*200){ guard++;
      const c = odd ? [0,2,4,6,8,10][Math.floor(Math.random()*6)] : Math.floor(Math.random()*12);
      const used=new Set(), dyads=[];
      for(let a=0;a<12;a++){ const b=mod12(c-a); if(a===b||used.has(a)) continue; used.add(a);used.add(b); dyads.push([a,b]); }
      const fixed=[]; for(let mm=0;mm<12;mm++) if(mod12(2*mm)===c) fixed.push(mm);
      const half=odd?(N-1)/2:N/2;
      if(dyads.length<half) continue;
      let mid=null; if(odd){ if(!fixed.length) continue; mid=fixed[Math.floor(Math.random()*fixed.length)]; }
      const pick=shuffle(dyads).slice(0,half), row=new Array(N);
      pick.forEach((pr,k)=>{ const o=Math.random()<0.5; row[k]=o?pr[0]:pr[1]; row[N-1-k]=mod12(c-row[k]); });
      if(odd) row[(N-1)/2]=mid;
      if(new Set(row).size!==N) continue; const key=row.join(',');
      if(seen.has(key)) continue; seen.add(key); out.push({pcs:row, c});
    }
    return out;
  }
  // ----- (C) derived rows & "contains a set class" -----
  const _ciCache={};
  function classImages(pf){
    const key=pf.join(','); if(_ciCache[key]) return _ciCache[key];
    const set=new Set();
    for(let t=0;t<12;t++) for(const base of [pf, pf.map(x=>mod12(-x))]){
      const u=uniqSort(base.map(x=>mod12(x+t))); if(u.length===pf.length) set.add(u.join(','));
    }
    const res=[...set].map(s=>s.split(',').map(Number)); _ciCache[key]=res; return res;
  }
  const maskOf=arr=>{ let m=0; for(const x of arr) m|=(1<<x); return m; };
  // exact cover of {0..11} by `copies` T/I images of pf (randomized order); returns segments or null
  function findTilingN(pf, m, mustCover){
    const imgs=shuffle(classImages(pf)).map(a=>({arr:a,mask:maskOf(a)})), full=(1<<12)-1, chosen=[];
    function bt(fill){ if(chosen.length===m) return mustCover ? fill===full : true;
      const rem=(~fill)&full, lowBit=rem&(-rem);
      for(const im of imgs){ if(im.mask&fill) continue; if(mustCover && !(im.mask&lowBit)) continue; chosen.push(im); if(bt(fill|im.mask)) return true; chosen.pop(); }
      return false;
    }
    return bt(0)?chosen.map(c=>c.arr):null;
  }
  const DERIVABLE_CACHE={};
  function derivableFor(N,k){
    const key=N+'-'+k; if(DERIVABLE_CACHE[key]) return DERIVABLE_CACHE[key];
    const m=N/k, mustCover=(N===12), list=[];
    for(const pair of (SC_RAW[k]||[])){ const pf=primeForm(pair[1]); if(findTilingN(pf,m,mustCover)) list.push({name:pair[0],pf}); }
    DERIVABLE_CACHE[key]=list; return list;
  }
  function genDerivedN(pf, m, mustCover, limit){
    const out=[], seen=new Set(); let guard=0;
    while(out.length<limit && guard<limit*150){ guard++;
      const cover=findTilingN(pf,m,mustCover); if(!cover) break;
      const segs=shuffle(cover).map(seg=>shuffle(seg)), pcs=[].concat(...segs), key=pcs.join(',');
      if(seen.has(key)) continue; seen.add(key); out.push({pcs});
    }
    return out;
  }
  function genContainsN(pf, N, limit){
    const imgs=classImages(pf), out=[], seen=new Set(); let guard=0; if(pf.length>N) return out;
    while(out.length<limit && guard<limit*150){ guard++;
      const A=imgs[Math.floor(Math.random()*imgs.length)], As=new Set(A), rest=[];
      for(let p=0;p<12;p++) if(!As.has(p)) rest.push(p);
      const extra=shuffle(rest).slice(0, N-A.length);
      const pcs=shuffle(A).concat(shuffle(extra)), key=pcs.join(',');
      if(seen.has(key)) continue; seen.add(key); out.push({pcs});
    }
    return out;
  }
  function resolveSC(str){
    str=(str||'').trim(); if(!str) return null;
    const fm=str.match(/^(\d+)-(z?)(\d+)$/i);
    if(fm){ const card=fm[1], want=(card+'-'+(fm[2]?'z':'')+fm[3]).toLowerCase(); const row=(SC_RAW[card]||[]).find(p=>p[0].toLowerCase()===want); return row?{pf:primeForm(row[1]),forte:row[0]}:null; }
    const r=parseRow(str); if(r.error||!r.entries) return null; const pcs=r.entries.map(e=>e.pc);
    if(pcs.length<2||pcs.length>10) return null;
    return {pf:primeForm(pcs), forte:forteName(pcs)};
  }
  function populateDerSC(){
    const sel=$('der-sc'); if(!sel) return;
    const list=derivableFor(ROWLEN, derSize);
    if(derClass!=='any' && !list.some(c=>c.name===derClass)) derClass='any';
    sel.innerHTML=['<option value="any">Any (mix)</option>'].concat(list.map(c=>`<option value="${c.name}">${c.name} (${c.pf.map(pcTok).join('')})</option>`)).join('');
    sel.value=derClass;
  }
  function derivedSizes(){ return mode==='twelve' ? [3,4] : divisorKs(ROWLEN); }
  function renderDerSizes(){
    const host=$('der-sizes'); if(!host) return; const sizes=derivedSizes();
    if(!sizes.length){ host.innerHTML=''; return; }
    if(!sizes.includes(derSize)) derSize=sizes[0];
    host.innerHTML='';
    sizes.forEach(k=>{ const b=document.createElement('button'); b.type='button'; b.id='der-'+k;
      b.setAttribute('aria-pressed', String(k===derSize)); b.textContent=cap(cellName(k))+'s';
      b.addEventListener('click',()=>{ if(derSize===k) return; derSize=k; populateDerSC(); buildResults=null; renderDerSizes(); renderBuild(); });
      host.appendChild(b); });
  }

  function runBuild(){
    if(mode!=='twelve' && !(mode==='custom' && divisorKs(ROWLEN).length>0)) return;
    if(mode==='custom' && (buildMode==='allint'||buildMode==='allcomb')) buildMode='derived';
    const N=ROWLEN, LIM=12;
    if(buildMode==='allint'){ buildResults={mode:'allint', rows:sampleAllInterval(LIM).map(pcs=>({pcs}))}; }
    else if(buildMode==='allcomb'){ buildResults={mode:'allcomb', rows:genAllComb(combSource,LIM)}; }
    else if(buildMode==='risym'){ buildResults={mode:'risym', rows:genRISymN(N,LIM)}; }
    else if(buildMode==='derived'){
      const copies=N/derSize, mustCover=(N===12); let rows=[]; const pool=derivableFor(N,derSize);
      if(derClass==='any'){ const seen=new Set(); let guard=0;
        while(rows.length<LIM && guard<LIM*200){ guard++; if(!pool.length) break; const cl=pool[Math.floor(Math.random()*pool.length)]; const one=genDerivedN(cl.pf,copies,mustCover,1); if(one.length){ const key=one[0].pcs.join(','); if(seen.has(key))continue; seen.add(key); one[0].cls=cl.name; rows.push(one[0]); } }
      } else { const cl=pool.find(c=>c.name===derClass); if(cl) rows=genDerivedN(cl.pf,copies,mustCover,LIM).map(r=>{ r.cls=cl.name; return r; }); }
      buildResults={mode:'derived', size:derSize, rows};
    }
    else if(buildMode==='contains'){
      const sc=resolveSC(containsSpec);
      buildResults = (sc && sc.pf.length<=N) ? {mode:'contains', sc, rows:genContainsN(sc.pf,N,LIM)} : {mode:'contains', bad:true, rows:[]};
    }
    renderBuild();
  }
  function buildLoad(rowPcs){ entered=rowPcs.map(pc=>({pc,name:null})); state=bs(rowPcs); genResults=null; buildResults=null; expandSections(); const ex=$('ex-note'); if(ex) ex.textContent=''; renderAll(); const t=$('matrix-section'); if(t) t.scrollIntoView({behavior:'smooth',block:'start'}); }
  function exNote(t){ const el=$('ex-note'); if(!el) return; el.textContent=t||''; clearTimeout(el._t); if(t) el._t=setTimeout(function(){ el.textContent=''; },3000); }
  let _derSig='';
  function renderBuild(){
    const bs=$('build-section');
    if(mode!=='twelve' && !(mode==='custom' && divisorKs(ROWLEN).length>0)){ if(bs) bs.classList.add('hidden'); return; }
    if(bs) bs.classList.remove('hidden');
    if(mode==='custom' && (buildMode==='allint'||buildMode==='allcomb')) buildMode='derived';
    [['bk-allint','allint'],['bk-allcomb','allcomb'],['bk-risym','risym'],['bk-derived','derived'],['bk-contains','contains']].forEach(([id,mm])=>{const b=$(id); if(b) b.setAttribute('aria-pressed',String(mm===buildMode));});
    { const sig=mode+'|'+ROWLEN; if(sig!==_derSig){ _derSig=sig; renderDerSizes(); populateDerSC(); } }
    const sr=$('src-row'); if(sr) sr.hidden = buildMode!=='allcomb';
    const dr=$('der-row'); if(dr) dr.hidden = buildMode!=='derived';
    const cr=$('con-row'); if(cr) cr.hidden = buildMode!=='contains';
    const info=$('build-info'); const host=$('build-body'); if(!host) return; host.innerHTML='';
    if(info){
      if(buildMode==='allint') info.innerHTML=`There are <b>${countAllInterval().toLocaleString()}</b> all-interval rows beginning on C — the eleven successive intervals run through every interval 1–11, so the first and last notes are always a tritone apart. Generate draws a fresh sample.`;
      else if(buildMode==='allcomb') info.innerHTML=`An <b>all-combinatorial</b> row's first hexachord is one of the six source hexachords (6-1, 6-7, 6-8, 6-20, 6-32, 6-35); its complement completes the aggregate, so the row is P-, I-, R- and RI-combinatorial.`;
      else if(buildMode==='risym') info.innerHTML=`An <b>RI-symmetric</b> row maps onto its own retrograde-inversion: paired positions sum to a constant, so the ${4*ROWLEN} row forms collapse to ${2*ROWLEN}.`;
      else if(buildMode==='derived'){ const w=cellName(derSize)+'s'; info.innerHTML=`A <b>derived</b> row's ${ROWLEN/derSize} discrete ${w} all belong to one set class — formed by tiling the ${ROWLEN===12?'aggregate':'row'} with T / I copies of that set class. Pick a class or let it mix.`; }
      else info.innerHTML=`Generates rows that <b>open with a chosen set class</b> as the first segment; the remaining pitches complete the ${ROWLEN===12?'aggregate':'row'}. Enter a Forte name (e.g. 4-z15) or the pitches themselves (0 1 4 6, or C C# E F#).`;
    }
    if(!buildResults){ const e=document.createElement('div'); e.className='gen-empty'; e.textContent='Press Generate to build rows.'; host.appendChild(e); return; }
    const rows=buildResults.rows;
    if(!rows.length){ const e=document.createElement('div'); e.className='gen-empty'; e.textContent = buildResults.bad ? 'Enter a valid set class above — a Forte name like 4-z15, or 2–10 pitch classes (e.g. 0 1 4 6).' : 'No rows found — try a different option.'; host.appendChild(e); return; }
    const c=document.createElement('div'); c.className='gen-count';
    c.innerHTML=`<b>${rows.length}</b> row${rows.length===1?'':'s'} — each is a complete ${ROWLEN===12?'twelve-tone':ROWLEN+'-note'} row. Load one to build its matrix.`;
    host.appendChild(c);
    { const ca=document.createElement('button'); ca.className='gen-copyall'; ca.textContent='Copy all'; ca.title='Copy all rows as text'; ca.addEventListener('click',()=>{ const txt=rows.map(r=>r.pcs.map(genShow).join(' ')).join('\n'); copyBtn(ca,txt); }); c.appendChild(ca); }
    rows.forEach(r=>{
      const pcs=r.pcs;
      const item=document.createElement('div'); item.className='gen-item';
      const ops=document.createElement('div'); ops.className='gen-ops';
      let detail='';
      if(buildResults.mode==='allint'){
        ops.innerHTML='<span class="gen-op alt">all-interval</span>';
        const ints=pcs.slice(1).map((p,i)=>mod12(p-pcs[i]));
        detail=`intervals \u27e8 ${ints.map(pcTok).join(' ')} \u27e9`;
      } else if(buildResults.mode==='allcomb'){
        const hp=primeForm(pcs.slice(0,6));
        ops.innerHTML=`<span class="gen-op alt">all-combinatorial</span><span class="gen-op">${r.src.id}${r.src.name?' ('+r.src.name+')':''}</span>`;
        detail=`first hexachord (${hp.map(pcTok).join('')})${forteName(pcs.slice(0,6))?' '+forteName(pcs.slice(0,6)):''}`;
      } else if(buildResults.mode==='derived'){
        const m=buildResults.size, seg0=primeForm(pcs.slice(0,m)), fn=forteName(pcs.slice(0,m));
        ops.innerHTML=`<span class="gen-op alt">derived</span><span class="gen-op">${cellName(m)}s</span>${fn?`<span class="gen-op">${fn}</span>`:''}`;
        detail=`every ${cellName(m)} = (${seg0.map(pcTok).join('')})${fn?' '+fn:''}`;
      } else if(buildResults.mode==='contains'){
        const m=buildResults.sc.pf.length, seg0=primeForm(pcs.slice(0,m)), fn=buildResults.sc.forte;
        ops.innerHTML=`<span class="gen-op alt">contains</span><span class="gen-op">${fn||'('+buildResults.sc.pf.map(pcTok).join('')+')'}</span>`;
        detail=`opens with (${seg0.map(pcTok).join('')})${fn?' '+fn:''}`;
      } else {
        ops.innerHTML=`<span class="gen-op alt">RI-symmetric</span>`;
        detail=`paired positions sum to ${r.c} (mod 12) \u2014 ${2*ROWLEN} distinct forms`;
      }
      item.appendChild(ops);
      const pcsEl=document.createElement('div'); pcsEl.className='gen-pcs'; pcsEl.textContent=pcs.map(genShow).join(' ');
      item.appendChild(pcsEl);
      const load=document.createElement('button'); load.className='gen-load'; load.textContent='Load into matrix';
      load.addEventListener('click',()=>buildLoad(pcs));
      item.appendChild(load);
      const d=document.createElement('div'); d.className='build-detail'; d.textContent=detail;
      item.appendChild(d);
      host.appendChild(item);
    });
  }

  // ---------- export: save / share ----------
  function expNote(msg){ const n=$('exp-note'); if(!n) return; n.textContent=msg; n.classList.add('show'); clearTimeout(expNote._t); expNote._t=setTimeout(()=>{ n.classList.remove('show'); n.textContent=''; },3600); }
  function dlBlob(filename,blob){ const u=URL.createObjectURL(blob); const a=document.createElement('a'); a.href=u; a.download=filename; document.body.appendChild(a); a.click(); setTimeout(()=>{ URL.revokeObjectURL(u); a.remove(); },120); }
  function dlText(filename,text){ dlBlob(filename,new Blob([text],{type:'text/plain;charset=utf-8'})); }
  function dlCsv(filename,text){ dlBlob(filename,new Blob(['\ufeff'+text],{type:'text/csv;charset=utf-8'})); }
  function csvCell(s){ s=String(s); return /[",\n\r]/.test(s)?'"'+s.replace(/"/g,'""')+'"':s; }
  function tabToCsv(txt){ return txt.split('\n').map(line=>line.split('\t').map(csvCell).join(',')).join('\r\n'); }
  function csvFooter(t){ const f=citeFooterText(t); if(!f) return ''; const lines=f.split('\n').map(s=>s.replace(/\r$/,'')).filter(s=>s.trim()); return lines.length?('\r\n\r\n'+lines.map(csvCell).join('\r\n')):''; }
  function gridTabText(t){ return (mode==='stravinsky') ? (STRAV_TXT['matrix']?STRAV_TXT['matrix']():'') : matrixText(); }
  function fallbackCopy(text){ const ta=document.createElement('textarea'); ta.value=text; ta.setAttribute('readonly',''); ta.style.position='fixed'; ta.style.top='-1000px'; ta.style.opacity='0'; document.body.appendChild(ta); ta.select(); try{ta.setSelectionRange(0,text.length);}catch(e){} let ok=false; try{ok=document.execCommand('copy');}catch(e){ok=false;} ta.remove(); return ok; }
  function copyText(text){
    const done=ok=>expNote(ok?'Copied successfully!':'Copy blocked by the browser — use Export \u2192 .txt instead.');
    if(navigator.clipboard&&navigator.clipboard.writeText){ navigator.clipboard.writeText(text).then(()=>done(true)).catch(()=>done(fallbackCopy(text))); }
    else done(fallbackCopy(text));
  }
  const esc=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');

  // ---------- citation ----------
  const CITE={author:'Ahmet Can K\u0131z\u0131lcan', authorRev:'K\u0131z\u0131lcan, Ahmet Can', authorInit:'K\u0131z\u0131lcan, A. C.', title:'Row, Row, Row Your Tone - Post-Tonal Music Analysis Tool', year:'2026', url:'https://ackc92.github.io/rowyourtone/'};
  const CITE_LABELS={apa:'APA (7th ed.)', mla:'MLA (9th ed.)', 'chicago-b':'Chicago (bibliography)', 'chicago-ad':'Chicago (author\u2013date)', harvard:'Harvard', ieee:'IEEE', bibtex:'BibTeX'};
  function retrievedDate(){
    const d=new Date(), day=d.getDate(), y=d.getFullYear(), mi=d.getMonth();
    const MON=['January','February','March','April','May','June','July','August','September','October','November','December'];
    const ABBR=['Jan.','Feb.','Mar.','Apr.','May','Jun.','Jul.','Aug.','Sep.','Oct.','Nov.','Dec.'];
    return { mdy:MON[mi]+' '+day+', '+y, dmy:day+' '+MON[mi]+' '+y, ieee:ABBR[mi]+' '+day+', '+y };
  }
  function citationText(fmt){
    const a=CITE, r=retrievedDate();
    switch(fmt){
      case 'apa':        return a.authorInit+' ('+a.year+'). '+a.title+' [Web-Browser App]. Retrieved '+r.mdy+', from '+a.url+'.';
      case 'mla':        return a.authorRev+'. '+a.title+'. '+a.year+'. Web-Browser App. '+a.url+'. Accessed '+r.dmy+'.';
      case 'chicago-b':  return a.authorRev+'. '+a.title+'. '+a.year+'. Web-Browser App. Accessed '+r.mdy+'. '+a.url+'.';
      case 'chicago-ad': return a.authorRev+'. '+a.year+'. '+a.title+'. Web-Browser App. Accessed '+r.mdy+'. '+a.url+'.';
      case 'harvard':    return a.authorInit+' ('+a.year+') '+a.title+'. [Web-Browser App]. Available at: '+a.url+' (Accessed: '+r.dmy+').';
      case 'ieee':       return 'A. C. K\u0131z\u0131lcan, '+a.title+'. ('+a.year+'). [Web-Browser App]. Accessed: '+r.ieee+'. [Online]. Available: '+a.url;
      case 'bibtex':     return '@software{kizilcan'+a.year+'twelvetone,\n  author = {'+a.author+'},\n  title  = {'+a.title+'},\n  year   = {'+a.year+'},\n  url    = {'+a.url+'},\n  note   = {Accessed '+r.dmy+'}\n}';
      default: return '';
    }
  }
  const citationOneLine=fmt=>citationText(fmt).replace(/\s*\n\s*/g,' ').replace(/\s{2,}/g,' ').trim();
  const citeFmtNow=()=>{ const cf=$('cite-fmt'); return cf?cf.value:''; };
  const citeFootLine=()=>{ const f=citeFmtNow(); return f?('Cited as: '+citationOneLine(f)):''; };
  const citeFooterText=(target)=>{ const f=citeFmtNow(); if(!f) return ''; const lead=(target==='analysis')?'\n\n\n\n':'\n\n'; return lead+'\u2500'.repeat(40)+'\nCite this tool ('+(CITE_LABELS[f]||f)+'):\n'+citationText(f)+'\n'; };

  function segInfo(k){
    const row=state.input, N=row.length, count=Math.floor(N/k), segs=[];
    for(let i=0;i<count;i++) segs.push(row.slice(i*k,(i+1)*k));
    const cards=segs.map(seg=>({pcs:seg, nf:normalForm(seg), pf:primeForm(seg), icv:icVector(seg), forte:forteName(seg), tonal:tonalName(seg), sym:symDegrees(seg)}));
    const distinct=[...new Set(segs.map(s=>primeForm(s).join(',')))];
    const rel=segs.map((si,i)=>segs.map((sj,j)=> i===j?null:segRelations(si,sj)));
    return {k,count,segs,cards,distinct,rel};
  }
  function rowSym(){
    const {p0}=state, P=n=>p0.map(x=>mod12(x+n)), I=n=>p0.map(x=>mod12(n-x));
    const forms=[]; for(let n=0;n<12;n++){forms.push(P(n));forms.push(I(n));forms.push(P(n).slice().reverse());forms.push(I(n).slice().reverse());}
    const distinct=new Set(forms.map(f=>f.join(','))).size, p0s=p0.join(','); let ri=false,r=false;
    for(let n=0;n<12;n++){ if(I(n).slice().reverse().join(',')===p0s) ri=true; if(P(n).slice().reverse().join(',')===p0s) r=true; }
    return {distinct,ri,r};
  }
  function summaryLine(info){
    const k=info.k;
    if(info.distinct.length===1){ const c=info.cards[0], tail='('+c.pf.map(pcTok).join('')+')'+(c.forte?' '+c.forte:'');
      if(k===2) return 'All '+info.count+' dyads share one interval class: '+tail+'.';
      if(info.count===2) return 'Both '+segWord(k)+'s belong to the same set class: '+tail+', ic vector ['+c.icv.join('')+'].';
      return 'All '+info.count+' '+segWord(k)+'s are one set class \u2014 a derived row: '+tail+'.';
    }
    return 'The '+info.count+' '+segWord(k)+'s use '+info.distinct.length+' distinct set classes: '+info.distinct.map(d=>{const a=d.split(',').map(Number),f=forteName(a);return '('+a.map(pcTok).join('')+')'+(f?' '+f:'');}).join(' \u00b7 ')+'.';
  }

  function matrixText(){
    const {M,inputRowIndex}=state, N=M.length, cell=(i,j)=>(i===inputRowIndex&&dispMode==='notes')?nameFor(entered[j]):showPc(M[i][j]), rows=[];
    rows.push((['', ...Array.from({length:N},(_,j)=>'I'+M[0][j]), '']).join('\t'));
    for(let i=0;i<N;i++){ const line=['P'+M[i][0]]; for(let j=0;j<N;j++) line.push(cell(i,j)); line.push('R'+M[i][0]); rows.push(line.join('\t')); }
    rows.push((['', ...Array.from({length:N},(_,j)=>'RI'+M[0][j]), '']).join('\t'));
    return rows.join('\n');
  }

  function rowHeaderLines(title){
    const {input,p0,firstPc}=state, mode=dispMode==='notes'?'note names':'integers', L=[];
    L.push(title); L.push('('+mode+')'); L.push('');
    L.push('Row  P'+firstPc+'  notes:     '+input.map(spellName).join(' '));
    L.push('Row  P'+firstPc+'  integers:  '+input.map(String).join(' '));
    L.push('P0 (matrix top):       '+p0.join(' '));
    const rs=rowSym(), kinds=[]; if(rs.ri)kinds.push('RI-symmetric'); if(rs.r)kinds.push('palindromic');
    L.push('Row symmetry:          '+rs.distinct+' distinct forms'+(kinds.length?' ('+kinds.join(', ')+')':''));
    return L;
  }
  // space-padded matrix grid (monospace-aligned) for text/PNG embedding
  function matrixGrid(){
    const {M,inputRowIndex}=state, N=M.length, tok=(i,j)=>(i===inputRowIndex&&dispMode==='notes')?nameFor(entered[j]):showPc(M[i][j]);
    const grid=[['', ...Array.from({length:N},(_,j)=>'I'+M[0][j]), '']];
    for(let i=0;i<N;i++){ const r=['P'+M[i][0]]; for(let j=0;j<N;j++) r.push(tok(i,j)); r.push('R'+M[i][0]); grid.push(r); }
    grid.push(['', ...Array.from({length:N},(_,j)=>'RI'+M[0][j]), '']);
    const w=new Array(N+2).fill(0);
    for(const r of grid) for(let c=0;c<N+2;c++) w[c]=Math.max(w[c],(r[c]||'').length);
    return grid.map(r=>r.map((c,i)=>(c||'').padEnd(w[i])).join('  ').replace(/\s+$/,''));
  }
  function formsLines(){
    const {p0}=state, P=n=>p0.map(x=>mod12(x+n)), I=n=>p0.map(x=>mod12(n-x)), L=['THE 48 ROW FORMS'];
    const fams=[['Prime','P',n=>P(n)],['Inversion','I',n=>I(n)],['Retrograde','R',n=>P(n).slice().reverse()],['Retrograde-Inversion','RI',n=>I(n).slice().reverse()]];
    for(const [nm,tag,fn] of fams){ L.push('  '+nm+':'); for(let n=0;n<12;n++) L.push('    '+(tag+n).padEnd(4)+'  '+fn(n).map(showPc).join(' ')); }
    return L;
  }
  function subsetLines(ks){
    ks = ks || [2,3,4,6];
    const L=['SUBSET ANALYSIS'];
    for(const k of ks){
      const info=segInfo(k), ab=segAbbr(k);
      L.push(''); L.push('  '+cap(segWord(k))+'s ('+info.count+'):');
      info.cards.forEach((c,idx)=>{ const cells=[(ab+'-'+(idx+1)).padEnd(5), c.pcs.map(showPc).join(' ').padEnd(17), (c.forte||'').padEnd(7), ('('+c.pf.map(pcTok).join('')+')').padEnd(9), 'ic['+c.icv.join('')+']'];
        if(c.tonal) cells.push('\u00b7 '+c.tonal); L.push(('    '+cells.join('  ')).replace(/\s+$/,'')); });
      L.push('    \u2192 '+summaryLine(info));
      const labs=info.segs.map((s,i)=>ab+'-'+(i+1));
      const grid=info.segs.map((si,i)=>info.segs.map((sj,j)=> i===j?'\u2014':(info.rel[i][j]&&info.rel[i][j].length?info.rel[i][j].join(' '):'\u00b7')));
      const colw=labs.map((lb,j)=>Math.max(lb.length, ...grid.map(r=>r[j].length))), rhw=Math.max(...labs.map(l=>l.length));
      L.push('    relationships (row \u2192 col):');
      L.push('      '+' '.repeat(rhw)+'  '+labs.map((lb,j)=>lb.padEnd(colw[j])).join('  '));
      grid.forEach((r,i)=>{ L.push('      '+labs[i].padEnd(rhw)+'  '+r.map((c,j)=>c.padEnd(colw[j])).join('  ')); });
    }
    L.push('');
    L.push('  Key:  Tn = transposition,  TnI = inversion (I = inversion).');
    L.push('        *  = ordered relationship (maps the segments note-for-note, in the same order).');
    L.push('        no * = unordered (same pitch-class set, order differs).   . = unrelated (different set class).');
    return L;
  }
  function analysisText(){ return [].concat(rowHeaderLines('TWELVE-TONE ANALYSIS'), [''], formsLines(), [''], subsetLines()).join('\n'); }
  function fullText(){
    const L=rowHeaderLines('TWELVE-TONE \u2014 FULL REPORT');
    L.push(''); L.push('MATRIX'); L.push('P left \u00b7 I top \u00b7 R right \u00b7 RI bottom'); L.push('');
    matrixGrid().forEach(l=>L.push('  '+l));
    return [].concat(L, [''], formsLines(), [''], subsetLines()).join('\n');
  }

  function matrixCanvas(){
    const {M,inputRowIndex}=state, ratio=Math.max(1,Math.min(2,window.devicePixelRatio||1));
    const N=M.length, cell=46, pad=22, titleH=64, footH=48, cols=N+2, rows=N+2, gridW=cols*cell, gridH=rows*cell;
    const citeStr=citeFootLine();
    const measW=document.createElement('canvas').getContext('2d'); measW.font='9.5px ui-monospace, Menlo, Consolas, monospace';
    const citeW=citeStr?measW.measureText(citeStr).width:0;
    const W=Math.max(gridW, Math.ceil(citeW))+pad*2, H=titleH+gridH+footH+pad;
    const cv=document.createElement('canvas'); cv.width=Math.round(W*ratio); cv.height=Math.round(H*ratio);
    const ctx=cv.getContext('2d'); ctx.scale(ratio,ratio);
    ctx.fillStyle='#ffffff'; ctx.fillRect(0,0,W,H);
    ctx.fillStyle='#15161a'; ctx.textBaseline='alphabetic'; ctx.textAlign='left';
    ctx.font='600 20px Georgia, "Times New Roman", serif'; ctx.fillText(repTitle('matrix'), pad, 30);
    ctx.fillStyle='#555'; ctx.font='12px ui-monospace, Menlo, Consolas, monospace';
    const rowStr=(dispMode==='notes'?state.input.map(spellName):state.input.map(String)).join('  ');
    ctx.fillText('P'+state.firstPc+':  '+rowStr, pad, 50);
    const ox=pad, oy=titleH, tok=(i,j)=>(i===inputRowIndex&&dispMode==='notes')?nameFor(entered[j]):showPc(M[i][j]);
    ctx.textAlign='center'; ctx.textBaseline='middle';
    for(let r=0;r<rows;r++) for(let c=0;c<cols;c++){
      const x=ox+c*cell, y=oy+r*cell; let bg='#ffffff', fg='#15161a', label=false, txt='';
      const corner=(r===0||r===N+1)&&(c===0||c===N+1);
      if(corner){ bg='#f4f4f1'; }
      else if(r===0){ txt='I'+M[0][c-1]; bg='#f4f4f1'; fg='#444'; label=true; }
      else if(r===N+1){ txt='RI'+M[0][c-1]; bg='#f4f4f1'; fg='#444'; label=true; }
      else if(c===0){ txt='P'+M[r-1][0]; bg='#f4f4f1'; fg='#444'; label=true; }
      else if(c===N+1){ txt='R'+M[r-1][0]; bg='#f4f4f1'; fg='#444'; label=true; }
      else { const i=r-1,j=c-1; txt=tok(i,j); if(i===inputRowIndex) bg='#fff6e9'; if(i===j) bg=(i===inputRowIndex)?'#e6e2ff':'#eceaff'; }
      ctx.fillStyle=bg; ctx.fillRect(x,y,cell,cell);
      ctx.strokeStyle='#e0e0db'; ctx.lineWidth=1; ctx.strokeRect(x+0.5,y+0.5,cell,cell);
      if(txt){ ctx.fillStyle=fg; ctx.font=(label?'600 12px':'13px')+' ui-monospace, Menlo, Consolas, monospace'; ctx.fillText(txt,x+cell/2,y+cell/2+1); }
    }
    ctx.strokeStyle='#9a9aa2'; ctx.lineWidth=1.5; ctx.strokeRect(ox+cell+0.5,oy+cell+0.5,cell*N,cell*N);
    ctx.fillStyle='#888'; ctx.textAlign='left'; ctx.textBaseline='alphabetic'; ctx.font='10px ui-monospace, Menlo, Consolas, monospace';
    ctx.fillText('P left \u00b7 I top \u00b7 R right \u00b7 RI bottom', pad, titleH+gridH+18);
    if(citeStr){ ctx.fillStyle='#9a9aa2'; ctx.font='9.5px ui-monospace, Menlo, Consolas, monospace'; ctx.fillText(citeStr, pad, titleH+gridH+36); }
    return cv;
  }
  function textCanvas(text, title, footer, footGap){
    const lines=text.split('\n');
    let start=0; if(lines[0]&&lines[0].trim()===lines[0].trim().toUpperCase()&&/[A-Z]/.test(lines[0])) start=1;
    const ratio=Math.max(1,Math.min(2,window.devicePixelRatio||1)), pad=24, titleH=46, lh=16, fp=12.5, fpf=10;
    const meas=document.createElement('canvas').getContext('2d');
    meas.font=fp+'px ui-monospace, Menlo, Consolas, monospace';
    let maxw=0; for(let i=start;i<lines.length;i++){ const w=meas.measureText(lines[i]).width; if(w>maxw)maxw=w; }
    meas.font='600 20px Georgia, "Times New Roman", serif'; maxw=Math.max(maxw, meas.measureText(title).width);
    if(footer){ meas.font=fpf+'px ui-monospace, Menlo, Consolas, monospace'; maxw=Math.max(maxw, meas.measureText(footer).width); }
    const footH = footer ? lh+10+(footGap||0) : 0;
    const W=Math.ceil(maxw)+pad*2, H=titleH+(lines.length-start)*lh+footH+pad;
    const cv=document.createElement('canvas'); cv.width=Math.round(W*ratio); cv.height=Math.round(H*ratio);
    const ctx=cv.getContext('2d'); ctx.scale(ratio,ratio);
    ctx.fillStyle='#ffffff'; ctx.fillRect(0,0,W,H);
    ctx.fillStyle='#15161a'; ctx.textBaseline='alphabetic'; ctx.textAlign='left';
    ctx.font='600 20px Georgia, "Times New Roman", serif'; ctx.fillText(title, pad, 30);
    let y=titleH+12;
    for(let i=start;i<lines.length;i++){ const ln=lines[i];
      const head=ln.length>4 && !/^\s/.test(ln) && ln===ln.toUpperCase() && /[A-Z]/.test(ln);
      ctx.fillStyle=head?'#4733e6':'#222'; ctx.font=(head?'600 ':'')+fp+'px ui-monospace, Menlo, Consolas, monospace';
      ctx.fillText(ln, pad, y); y+=lh;
    }
    if(footer){ ctx.fillStyle='#9a9aa2'; ctx.font=fpf+'px ui-monospace, Menlo, Consolas, monospace'; ctx.fillText(footer, pad, y+10+(footGap||0)); }
    return cv;
  }
  const analysisCanvas=()=>textCanvas(mode==='custom'?analysisTextC():analysisText(), repTitle('analysis'), citeFootLine(), 18);
  const fullCanvas    =()=>textCanvas(mode==='custom'?fullTextC():fullText(), repTitle('full'), citeFootLine());
  let pngWantCopy=false;
  function pngEmit(fn,b){
    const copy=pngWantCopy; pngWantCopy=false;
    if(!b){ expNote(copy?'Copy failed.':'PNG export failed.'); return; }
    if(copy){
      if(navigator.clipboard && window.ClipboardItem){
        try{ navigator.clipboard.write([new ClipboardItem({'image/png':b})]).then(()=>expNote('Image copied to clipboard'),()=>expNote('Copy blocked \u2014 use Export to save the .png')); }
        catch(e){ expNote('Copy blocked \u2014 use Export to save the .png'); }
      } else expNote('Image copy unsupported here \u2014 use Export to save the .png');
    } else { dlBlob(fn,b); expNote('Saved '+fn); }
  }
  function copyImage(){ pngWantCopy=true; exportPNG(); }
  function exportPNG(){
    const t=$('exp-target').value; let cv,fn;
    if(mode==='stravinsky'){
      if(t==='analysis'){ cv=textCanvas(stravAnalysisText(),'Stravinsky’s Array \u2014 Analysis', citeFootLine(), 18); fn='stravinsky-analysis.png'; }
      else if(t==='full'){ cv=textCanvas(stravFullText(),'Stravinsky’s Rotational Arrays \u2014 Full Report', citeFootLine()); fn='stravinsky-full-report.png'; }
      else { cv=textCanvas(stravArrayText(),'Stravinsky’s Rotational Array', citeFootLine(), 18); fn='stravinsky-array.png'; }
      cv.toBlob(b=>pngEmit(fn,b),'image/png'); return;
    }
    if(t==='analysis'){ cv=analysisCanvas(); fn=fnFor('analysis','png'); }
    else if(t==='full'){ cv=fullCanvas(); fn=fnFor('full','png'); }
    else { cv=matrixCanvas(); fn=fnFor('matrix','png'); }
    cv.toBlob(b=>pngEmit(fn,b),'image/png');
  }

  function matrixTableHTML(){
    const {M,inputRowIndex}=state, N=M.length, cell=(i,j)=>(i===inputRowIndex&&dispMode==='notes')?esc(nameFor(entered[j])):esc(showPc(M[i][j]));
    let h='<table class="mtx"><tr><th></th>'; for(let j=0;j<N;j++) h+='<th>I'+M[0][j]+'</th>'; h+='<th></th></tr>';
    for(let i=0;i<N;i++){ const inr=i===inputRowIndex; h+='<tr><th>P'+M[i][0]+'</th>';
      for(let j=0;j<N;j++){ const cls=[]; if(i===j)cls.push('diag'); if(inr)cls.push('inrow'); h+='<td'+(cls.length?' class="'+cls.join(' ')+'"':'')+'>'+cell(i,j)+'</td>'; }
      h+='<th>R'+M[i][0]+'</th></tr>'; }
    h+='<tr><th></th>'; for(let j=0;j<N;j++) h+='<th>RI'+M[0][j]+'</th>'; h+='<th></th></tr>'; return h+'</table>';
  }
  function formsHTML(){
    const {p0}=state, P=n=>p0.map(x=>mod12(x+n)), I=n=>p0.map(x=>mod12(n-x));
    const fams=[['Prime','P',n=>P(n)],['Inversion','I',n=>I(n)],['Retrograde','R',n=>P(n).slice().reverse()],['Retrograde-Inversion','RI',n=>I(n).slice().reverse()]];
    let h='<div class="forms4">'; for(const [nm,tag,fn] of fams){ h+='<div class="fcol"><h4>'+nm+'</h4>'; for(let n=0;n<12;n++) h+='<div class="fl"><span class="ft">'+tag+n+'</span>'+esc(fn(n).map(showPc).join(' '))+'</div>'; h+='</div>'; } return h+'</div>';
  }
  function combinHTML(){
    const {p0,input}=state, comp=new Set(input.slice(6)), P=n=>p0.map(x=>mod12(x+n)), I=n=>p0.map(x=>mod12(n-x));
    const fams={P:n=>P(n),I:n=>I(n),R:n=>P(n).slice().reverse(),RI:n=>I(n).slice().reverse()};
    const setEq=(a,b)=>{if(a.size!==b.size)return false;for(const x of a)if(!b.has(x))return false;return true;};
    const hits={P:[],I:[],R:[],RI:[]};
    for(const fam of ['P','I','R','RI'])for(let n=0;n<12;n++){const fh=new Set(fams[fam](n).slice(0,6));if(setEq(fh,comp))hits[fam].push(fam+n);}
    const present=['P','I','R','RI'].filter(f=>hits[f].length>0), meaningful=present.filter(f=>f!=='R');
    let headline; if(present.length===4)headline='All-combinatorial hexachord'; else if(meaningful.length===1)headline=meaningful[0]+'-combinatorial (semi-combinatorial)'; else if(meaningful.length>1)headline=meaningful.join(' & ')+'-combinatorial'; else headline='Not combinatorial (only the universal R)';
    let h='<div class="comb"><div class="comb-h">'+esc(headline)+'</div>';
    for(const f of ['P','I','R','RI']) h+='<div class="comb-l"><span>'+f+'-combinatorial</span><span>'+(hits[f].length?esc(hits[f].join(', ')):'\u2014')+'</span></div>';
    return h+'</div>';
  }
  function subsetHTML(ks, withCombin){
    ks = ks || [2,3,4,6]; if(withCombin===undefined) withCombin=true;
    let h='';
    for(const k of ks){
      const info=segInfo(k), ab=segAbbr(k);
      h+='<div class="block"><h3 class="sub-h">'+cap(segWord(k))+'s ('+info.count+')</h3>';
      h+='<table class="sc"><tr><th>seg</th><th>pcs</th><th>name</th><th>normal</th><th>prime</th><th>ic vector</th><th>symmetry</th></tr>';
      info.cards.forEach((c,idx)=>{ h+='<tr><td class="si">'+ab+'-'+(idx+1)+(c.forte?' <span class="fn">'+c.forte+'</span>':'')+'</td>'+
        '<td>'+esc(c.pcs.map(showPc).join(' '))+'</td><td>'+(c.tonal?esc(c.tonal):'\u2014')+'</td>'+
        '<td>['+c.nf.map(pcTok).join(',')+']</td><td>('+c.pf.map(pcTok).join('')+')</td><td>['+c.icv.join('')+']</td>'+
        '<td>'+symWord(c.sym)+' <span class="sy">T-'+c.sym.T+'\u00b7I-'+c.sym.I+'</span></td></tr>'; });
      h+='</table><div class="summ">'+esc(summaryLine(info))+'</div>';
      h+='<div class="clocks">';
      info.segs.forEach((seg,idx)=>{ const col=SEG_COLORS[idx%SEG_COLORS.length], tn=tonalName(seg);
        h+='<div class="clk"><div class="clab" style="color:'+col+'">'+ab+'-'+(idx+1)+'</div>'+clockSVG(seg,col)+'<div class="cpcs">'+esc(seg.map(showPc).join(' '))+'</div>'+(tn?'<div class="cnm" style="color:'+col+'">'+esc(tn)+'</div>':'')+'</div>'; });
      h+='</div>';
      h+='<table class="rel"><tr><th></th>'; info.segs.forEach((s,j)=>h+='<th>'+ab+'-'+(j+1)+'</th>'); h+='</tr>';
      info.segs.forEach((si,i)=>{ h+='<tr><th>'+ab+'-'+(i+1)+'</th>'; info.segs.forEach((sj,j)=>{ if(i===j){h+='<td class="d">\u2014</td>';return;} const r=info.rel[i][j]; h+='<td>'+(r&&r.length?esc(r.join(' ')):'\u00b7')+'</td>'; }); h+='</tr>'; });
      h+='</table>'; if(k===6 && withCombin) h+=combinHTML(); h+='</div>';
    }
    h+='<p style="color:#555;font-size:10px;margin:6px 0 0">Key: T<sub>n</sub> = transposition, T<sub>n</sub>I = inversion (the I denotes inversion). An asterisk (T<sub>n</sub>*) marks an <b>ordered</b> relationship \u2014 the operation maps the segments note-for-note, in the same order; operators without an asterisk relate the segments only as pitch-class sets (same collection, different order). <b>\u00b7</b> = unrelated.</p>';
    return h;
  }
  const REPORT_CSS='*{box-sizing:border-box}html,body{margin:0;padding:0}'
    +'body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;color:#15161a;font-size:11px;line-height:1.45;padding:18px}'
    +'h1{font-family:Georgia,"Times New Roman",serif;font-size:22px;margin:0 0 2px}'
    +'.sub{color:#666;font-size:11px;margin:0 0 14px}'
    +'h2{font-size:13px;letter-spacing:.05em;text-transform:uppercase;border-bottom:1px solid #ddd;padding-bottom:4px;margin:18px 0 10px}'
    +'h3.sub-h{font-size:12px;margin:14px 0 6px;color:#333}'
    +'.rowline{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px;margin:2px 0}'
    +'table{border-collapse:collapse;font-family:ui-monospace,Menlo,Consolas,monospace}'
    +'.mtx{font-size:11px;margin:6px 0 4px}.mtx th,.mtx td{width:24px;height:22px;text-align:center;border:1px solid #e2e2dd;padding:0}'
    +'.mtx th{color:#555;font-weight:600;background:#f4f4f1}.mtx td.diag{background:#eceaff}.mtx td.inrow{background:#fff6e9}.mtx td.diag.inrow{background:#e6e2ff}'
    +'.cap{color:#888;font-size:9.5px;font-family:ui-monospace,Menlo,Consolas,monospace;margin:2px 0 0}'
    +'.forms4{display:flex;gap:16px;flex-wrap:wrap}.fcol{flex:1;min-width:150px}.fcol h4{margin:0 0 4px;font-size:11px;color:#333}'
    +'.fl{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:10.5px;white-space:nowrap}.fl .ft{display:inline-block;width:30px;color:#888}'
    +'table.sc{width:100%;font-size:10px;margin:4px 0}table.sc th,table.sc td{border:1px solid #e2e2dd;padding:3px 6px;text-align:left}'
    +'table.sc th{background:#f4f4f1;color:#444;font-weight:600}table.sc .si{white-space:nowrap;font-weight:600}table.sc .fn{color:#4733e6}.sy{color:#888}'
    +'.summ{font-size:10.5px;margin:5px 0 8px;padding:6px 8px;background:#f7f7f4;border-left:3px solid #4733e6}'
    +'table.rel{font-size:10px;margin:4px 0}table.rel th,table.rel td{border:1px solid #e2e2dd;padding:3px 7px;text-align:center;min-width:30px}'
    +'table.rel th{background:#f4f4f1;color:#444}table.rel td.d{color:#aaa;background:#fafafa}'
    +'.comb{margin:8px 0;font-size:10.5px}.comb-h{font-weight:700;margin-bottom:4px}.comb-l{display:flex;gap:10px;font-family:ui-monospace,Menlo,Consolas,monospace}.comb-l span:first-child{width:150px;color:#555}'
    +'.clocks{display:flex;flex-wrap:wrap;gap:10px;margin:6px 0 10px}.clk{width:108px;text-align:center}.clk svg.clock-svg{width:104px;height:104px}.clk .clab{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:10px;font-weight:700;margin-bottom:2px}.clk .cpcs{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:9.5px;color:#555;margin-top:2px}.clk .cnm{font-size:9px;margin-top:1px}'
    +'.block{page-break-inside:avoid;break-inside:avoid}@page{margin:14mm}@media print{body{padding:0}}'
    +'.cite-foot{margin-top:22px;padding-top:8px;border-top:1px solid #ddd;font-size:9.5px;color:#777;font-family:ui-monospace,Menlo,Consolas,monospace}'
    +'.cite-foot.gap{margin-top:44px}';
  // ----- Custom Row Analyser export builders (N-aware; mirror the on-screen Custom views) -----
  function repTitle(kind){
    if(mode==='custom') return {matrix:'Custom Row \u2014 Matrix', analysis:'Custom Row \u2014 Analysis', full:'Custom Row \u2014 Full Report'}[kind];
    return {matrix:'Twelve-Tone Matrix', analysis:'Twelve-Tone Analysis', full:'Twelve-Tone \u2014 Full Report'}[kind];
  }
  function fnFor(kind,ext){
    const base = mode==='custom'
      ? ('custom-'+(state?state.input.length:customN)+'-note-'+kind)
      : ('twelve-tone-'+(kind==='full'?'full-report':kind));
    return base+'.'+ext;
  }
  function customSym(){
    const {M}=state, N=M.length, col=j=>M.map(r=>r[j]), all=[];
    for(let i=0;i<N;i++){ all.push(M[i].join(',')); all.push(M[i].slice().reverse().join(',')); }
    for(let j=0;j<N;j++){ const c=col(j); all.push(c.join(',')); all.push(c.slice().reverse().join(',')); }
    return {total:4*N, distinct:new Set(all).size};
  }
  // forms read off the N\u00d7N matrix (P=rows, I=columns, R=rows reversed, RI=columns reversed); labels use pc values
  function customFormsList(){
    const {M}=state, N=M.length, col=j=>M.map(r=>r[j]);
    return [
      ['Prime',                Array.from({length:N},(_,k)=>['P'+M[k][0],  M[k]])],
      ['Inversion',            Array.from({length:N},(_,k)=>['I'+M[0][k],  col(k)])],
      ['Retrograde',           Array.from({length:N},(_,k)=>['R'+M[k][0],  M[k].slice().reverse()])],
      ['Retrograde-Inversion', Array.from({length:N},(_,k)=>['RI'+M[0][k], col(k).slice().reverse()])]
    ];
  }
  function formsLinesC(){
    const {M}=state, N=M.length, L=['THE '+(4*N)+' ROW FORMS'];
    for(const [nm,items] of customFormsList()){ L.push('  '+nm+':'); items.forEach(([lab,seq])=>L.push('    '+lab.padEnd(5)+'  '+seq.map(showPc).join(' '))); }
    return L;
  }
  function formsHTMLC(){
    let h='<div class="forms4">';
    for(const [nm,items] of customFormsList()){ h+='<div class="fcol"><h4>'+esc(nm)+'</h4>'; items.forEach(([lab,seq])=>h+='<div class="fl"><span class="ft">'+lab+'</span>'+esc(seq.map(showPc).join(' '))+'</div>'); h+='</div>'; }
    return h+'</div>';
  }
  function rowHeaderLinesC(title){
    const {input,p0,firstPc}=state, dm=dispMode==='notes'?'note names':'integers', sym=customSym(), L=[];
    L.push(title); L.push('('+input.length+'-note row \u00b7 '+dm+')'); L.push('');
    L.push('Row  P'+firstPc+'  notes:     '+input.map(spellName).join(' '));
    L.push('Row  P'+firstPc+'  integers:  '+input.map(String).join(' '));
    L.push('P0 (matrix top):       '+p0.join(' '));
    L.push('Row forms:             '+sym.total+' total ('+sym.distinct+' distinct)');
    return L;
  }
  // uneven (prime-length) subset text: whole-set identity + each consecutive dyad/trichord layout
  function unevenLinesC(){
    const row=state.input, dom=[]; row.forEach(pc=>{ const m=mod12(pc); if(!dom.includes(m)) dom.push(m); });
    const N=dom.length, pf=primeForm(dom), fn=forteName(dom), v=icVector(dom), tn=tonalName(dom);
    const L=['SUBSET ANALYSIS (uneven)']; L.push('');
    L.push('  Set ('+N+' notes):  ('+pf.map(pcTok).join('')+')'+(fn?' '+fn:'')+(tn?' \u00b7 '+tn:'')+'   ic['+v.join('')+']');
    L.push('  No equal division into dyads / trichords / etc. \u2014 read as uneven.');
    L.push('  Pitch classes:  '+dom.map(showPc).join(' '));
    const layouts=unevenLayouts(N);
    if(!layouts.length){ L.push('  No dyad/trichord layout fits this length.'); return L; }
    L.push(''); L.push('  Subset layouts (each consecutive dyad / trichord grouping):');
    layouts.forEach(parts=>{
      L.push(''); L.push('    '+parts.map(p=>cap(segWord(p))).join(' + ')+':');
      let pos=0; const tc={};
      parts.forEach(p=>{ const seg=dom.slice(pos,pos+p); pos+=p; tc[p]=(tc[p]||0)+1;
        const nf=normalForm(seg), pf2=primeForm(seg), v2=icVector(seg), fn2=forteName(seg), tn2=tonalName(seg);
        const cells=[(segAbbr(p)+'-'+tc[p]).padEnd(6), seg.map(showPc).join(' ').padEnd(12), (fn2||'').padEnd(7), ('('+pf2.map(pcTok).join('')+')').padEnd(9), 'ic['+v2.join('')+']'];
        if(tn2) cells.push('\u00b7 '+tn2);
        L.push(('      '+cells.join('  ')).replace(/\s+$/,''));
      });
    });
    return L;
  }
  function subsetLinesC(){ const ks=divisorKs(state.input.length); return ks.length ? subsetLines(ks) : unevenLinesC(); }
  function unevenHTMLC(){
    const row=state.input, dom=[]; row.forEach(pc=>{ const m=mod12(pc); if(!dom.includes(m)) dom.push(m); });
    const N=dom.length, pf=primeForm(dom), fn=forteName(dom), v=icVector(dom), tn=tonalName(dom);
    let h='<div class="block"><h3 class="sub-h">Uneven set ('+N+' notes)</h3>';
    h+='<div class="summ">This '+N+'-note set is ('+pf.map(pcTok).join('')+')'+(fn?' '+esc(fn):'')+(tn?' \u00b7 '+esc(tn):'')+', ic vector ['+v.join('')+'] \u2014 no equal division, so it is read as uneven.</div>';
    h+='<div class="clocks"><div class="clk"><div class="clab">whole set</div>'+clockSVG(dom, SEG_COLORS[0])+'<div class="cpcs">'+esc(dom.map(showPc).join(' '))+'</div>'+(tn?'<div class="cnm">'+esc(tn)+'</div>':'')+'</div></div></div>';
    const layouts=unevenLayouts(N);
    if(!layouts.length){ return h.replace('</div></div>','</div><div class="summ">No dyad/trichord layout fits this length.</div></div>'); }
    layouts.forEach(parts=>{
      h+='<div class="block"><h3 class="sub-h">'+esc(parts.map(p=>cap(segWord(p))).join(' + '))+'</h3>';
      h+='<table class="sc"><tr><th>seg</th><th>pcs</th><th>name</th><th>normal</th><th>prime</th><th>ic vector</th><th>symmetry</th></tr>';
      let pos=0; const tc={};
      parts.forEach(p=>{ const seg=dom.slice(pos,pos+p); pos+=p; tc[p]=(tc[p]||0)+1;
        const nf=normalForm(seg), pf2=primeForm(seg), v2=icVector(seg), fn2=forteName(seg), tn2=tonalName(seg), sy=symDegrees(seg);
        h+='<tr><td class="si">'+segAbbr(p)+'-'+tc[p]+(fn2?' <span class="fn">'+fn2+'</span>':'')+'</td><td>'+esc(seg.map(showPc).join(' '))+'</td><td>'+(tn2?esc(tn2):'\u2014')+'</td><td>['+nf.map(pcTok).join(',')+']</td><td>('+pf2.map(pcTok).join('')+')</td><td>['+v2.join('')+']</td><td>'+symWord(sy)+' <span class="sy">T-'+sy.T+'\u00b7I-'+sy.I+'</span></td></tr>';
      });
      h+='</table></div>';
    });
    return h;
  }
  function subsetHTMLC(){ const ks=divisorKs(state.input.length); return ks.length ? subsetHTML(ks,false) : unevenHTMLC(); }
  function analysisTextC(){ return [].concat(rowHeaderLinesC('CUSTOM ROW \u2014 ANALYSIS'), [''], formsLinesC(), [''], subsetLinesC()).join('\n'); }
  function fullTextC(){
    const L=rowHeaderLinesC('CUSTOM ROW \u2014 FULL REPORT');
    L.push(''); L.push('MATRIX'); L.push('P left \u00b7 I top \u00b7 R right \u00b7 RI bottom'); L.push('');
    matrixGrid().forEach(l=>L.push('  '+l));
    return [].concat(L, [''], formsLinesC(), [''], subsetLinesC()).join('\n');
  }
  function txtBuild(t){ return (mode==='custom' ? {matrix:matrixText,analysis:analysisTextC,full:fullTextC} : {matrix:matrixText,analysis:analysisText,full:fullText})[t](); }
  function reportHTML(target){
    const {input,p0,firstPc}=state, isC=(mode==='custom'), title=repTitle(target);
    let symLine, subEl='Symmetry';
    if(isC){ const sym=customSym(); symLine=sym.total+' forms ('+sym.distinct+' distinct)'; subEl='Forms'; }
    else { const rs=rowSym(), kinds=[]; if(rs.ri)kinds.push('RI-symmetric'); if(rs.r)kinds.push('palindromic'); symLine=rs.distinct+' distinct forms'+(kinds.length?' ('+kinds.join(', ')+')':''); }
    const head='<h1>'+esc(title)+'</h1>'
      +'<div class="sub">'+(isC?('Custom row \u00b7 '+input.length+' notes \u00b7 '):('Prime row P'+firstPc+' \u00b7 '))+(dispMode==='notes'?'note names':'integers')+' \u00b7 generated '+esc(new Date().toLocaleString())+'</div>'
      +'<div class="rowline"><b>Notes</b>&nbsp;&nbsp;'+esc(input.map(spellName).join('  '))+'</div>'
      +'<div class="rowline"><b>Integers</b>&nbsp;&nbsp;'+input.map(String).join('  ')+'</div>'
      +'<div class="rowline"><b>P0</b>&nbsp;&nbsp;'+p0.join('  ')+'</div>'
      +'<div class="rowline"><b>'+subEl+'</b>&nbsp;&nbsp;'+symLine+'</div>';
    const mtx='<div class="block"><h2>Matrix</h2>'+matrixTableHTML()+'<div class="cap">P left \u00b7 I top \u00b7 R right \u00b7 RI bottom</div></div>';
    const formsTitle=isC?('The '+(4*input.length)+' row forms'):'The 48 row forms';
    const ana='<div class="block"><h2>'+formsTitle+'</h2>'+(isC?formsHTMLC():formsHTML())+'</div>'+'<h2>Subset analysis</h2>'+(isC?subsetHTMLC():subsetHTML());
    const body = target==='matrix' ? mtx : target==='analysis' ? ana : mtx+ana;
    const cf=citeFmtNow(), citeFoot = cf ? '<div class="cite-foot'+(target==='analysis'?' gap':'')+'">Cite this tool ('+esc(CITE_LABELS[cf]||cf)+'): '+esc(citationText(cf).replace(/\n/g,' '))+'</div>' : '';
    return '<!DOCTYPE html><html><head><meta charset="utf-8"><title>'+esc(title)+' \u2014 P'+firstPc+'</title><style>'+REPORT_CSS+'</style></head><body>'
      +head+body+citeFoot+'<scr'+'ipt>window.onload=function(){setTimeout(function(){try{window.print();}catch(e){}},300);};<\/scr'+'ipt></body></html>';
  }
  function openPDF(){
    const t=$('exp-target')?$('exp-target').value:'full';
    const w=window.open('','_blank'); if(!w){ expNote('Pop-up blocked \u2014 allow pop-ups for this page to export the PDF.'); return; }
    const html = mode==='stravinsky' ? stravReportHTML(t) : reportHTML(t);
    w.document.open(); w.document.write(html); w.document.close(); w.focus();
    expNote('Opening print dialog \u2014 choose \u201cSave as PDF\u201d as the destination.');
  }
  function updateExpButtons(){
    const on=!!state, tg=$('exp-target'), fm=$('exp-fmt');
    if(tg) tg.disabled=!on; if(fm) fm.disabled=!on;
    const cl=$('export-cluster'); if(cl) cl.classList.toggle('disabled',!on);
    document.body.classList.toggle('has-row', on); if(!on) document.body.classList.remove('exp-modal-open');
    const cp=$('exp-copy'); if(cp){ cp.disabled=!on; const _f=$('exp-fmt'); cp.textContent=(_f&&_f.value==='png')?'Copy image':'Copy to Clipboard'; }
    const run=$('exp-run'); if(run){ run.disabled = !on; run.title=''; }
    // warning only appears on a failed export attempt (set in the export handler); clear it once a format is chosen
    const w=$('exp-warn'); if(w && citeFmtNow()) w.classList.remove('show');
  }
  function renderExport(){ updateExpButtons(); }
  function expandSections(){ ['matrix-section','forms-section','subset-section'].forEach(id=>{ const s=$(id); if(s) s.classList.remove('collapsed'); }); document.querySelectorAll('.panel-head.collapsible').forEach(h=>h.setAttribute('aria-expanded','true')); }

  // ---------- mode gate ----------
  const LEDE_GATE='Three Modes in One Tool';
  const LEDE_TWELVE='Click notes to build a row. Enter all twelve for the full matrix \u2014 or stop at a 2-, 3-, 4-, or 6-note set and generate rows from its T / I / R / RI transformations. The matrix is normalized so the top row is P0; your row keeps its pitches and spelling and is identified by its transposition.';
  const LEDE_STRAV='Enter a six-note hexachord. Each row of the array rotates it one step and transposes back to its first pitch, so the first column stays constant \u2014 a centric note. Stravinsky read the columns (\u201cverticals\u201d) as harmonies, deriving arrays from four forms: P, I, R, and IR.';
  const LEDE_CUSTOM='Choose any row length — from a dyad up to eleven notes — then build the n×n matrix, read its P / I / R / RI forms, and analyse the row’s subsets: set classes, interval-class vectors, the pitch-class clock, and segment relationships, scaled to your row.';
  function applyHeader(m){
    const h1=$('app-h1'), lede=document.querySelector('.lede');
    if(m==='twelve'){ if(h1) h1.innerHTML='<span class="tt">Twelve-Tone</span> Row Analyser'; if(lede) lede.innerHTML=LEDE_TWELVE; }
    else if(m==='stravinsky'){ if(h1) h1.innerHTML='<span class="tt">Stravinsky’s</span> Rotational Array Analyser'; if(lede) lede.innerHTML=LEDE_STRAV; }
    else if(m==='custom'){ if(h1) h1.innerHTML='<span class="tt">Custom Row</span> Analyser'; if(lede) lede.innerHTML=LEDE_CUSTOM; }
    else { if(h1) h1.innerHTML='<span class="tt">Row, Row</span>, Row Your Tone'; if(lede) lede.innerHTML=LEDE_GATE; }
  }
  function saveActive(){ if(mode==='twelve'||mode==='stravinsky'||mode==='custom'){ modeStash[mode].entered=entered; modeStash[mode].state=state; } }
  function copyBtn(btn,txt){ if(!btn) return; const lbl=btn.dataset.lbl||btn.textContent; btn.dataset.lbl=lbl; const ok=()=>{btn.textContent='Copied!';}, no=()=>{btn.textContent='Copy failed';}; try{ if(navigator.clipboard&&navigator.clipboard.writeText){ navigator.clipboard.writeText(txt).then(ok,no); } else { const ta=document.createElement('textarea'); ta.value=txt; ta.style.position='fixed'; ta.style.opacity='0'; document.body.appendChild(ta); ta.select(); try{ document.execCommand('copy'); ok(); }catch(e){ no(); } document.body.removeChild(ta); } }catch(e){ no(); } clearTimeout(btn._t); btn._t=setTimeout(()=>{ btn.textContent=btn.dataset.lbl; },1500); }
// Self-contained QR encoder — byte mode, EC level M, versions 1..10, full mask selection.
// Implements ISO/IEC 18004 (standard algorithm). Returns {size, modules:[[0|1]], version, mask}.
const QR=(function(){
  // ---- GF(256), primitive 0x11D ----
  const EXP=new Array(512), LOG=new Array(256);
  (function(){ let x=1; for(let i=0;i<255;i++){ EXP[i]=x; LOG[x]=i; x<<=1; if(x&0x100) x^=0x11D; } for(let i=255;i<512;i++) EXP[i]=EXP[i-255]; })();
  function gmul(a,b){ return (a===0||b===0)?0:EXP[LOG[a]+LOG[b]]; }
  function rsDivisor(deg){ const r=new Array(deg).fill(0); r[deg-1]=1; let root=1; for(let i=0;i<deg;i++){ for(let j=0;j<deg;j++){ r[j]=gmul(r[j],root); if(j+1<deg) r[j]^=r[j+1]; } root=gmul(root,2); } return r; }
  function rsRemainder(data,div){ const r=new Array(div.length).fill(0); for(const b of data){ const factor=b ^ r[0]; r.shift(); r.push(0); for(let i=0;i<div.length;i++) r[i]^=gmul(div[i],factor); } return r; }
  // ---- level-M block table: version -> [ecPerBlock, [[blocks,dataCw],...]] ----
  const MT={1:[10,[[1,16]]],2:[16,[[1,28]]],3:[26,[[1,44]]],4:[18,[[2,32]]],5:[24,[[2,43]]],6:[16,[[4,27]]],7:[18,[[4,31]]],8:[22,[[2,38],[2,39]]],9:[22,[[3,36],[2,37]]],10:[26,[[4,43],[1,44]]]};
  const ALIGN={1:[],2:[6,18],3:[6,22],4:[6,26],5:[6,30],6:[6,34],7:[6,22,38],8:[6,24,42],9:[6,26,46],10:[6,28,50]};
  function getBit(x,i){ return (x>>>i)&1; }
  function utf8Bytes(str){ const e=encodeURIComponent(str), out=[]; for(let i=0;i<e.length;i++){ if(e[i]==='%'){ out.push(parseInt(e.substr(i+1,2),16)); i+=2; } else out.push(e.charCodeAt(i)); } return out; }

  function encode(text){
    const bytes=utf8Bytes(text);
    let version=0,ecPer=0,grp=null,dataCw=0;
    for(let v=1;v<=10;v++){ const [ec,g]=MT[v]; const dc=g.reduce((s,[b,c])=>s+b*c,0); const cb=v<=9?8:16; const cap=Math.floor((dc*8-4-cb)/8); if(bytes.length<=cap){ version=v; ecPer=ec; grp=g; dataCw=dc; break; } }
    if(!version) throw new Error('QR: data too long ('+bytes.length+' bytes)');
    // bit stream
    const bits=[]; const put=(val,len)=>{ for(let i=len-1;i>=0;i--) bits.push((val>>i)&1); };
    put(0b0100,4); put(bytes.length, version<=9?8:16); for(const b of bytes) put(b,8);
    const cap=dataCw*8; put(0, Math.min(4,cap-bits.length)); while(bits.length%8) bits.push(0);
    const pads=[0xEC,0x11]; let pi=0; while(bits.length<cap){ put(pads[pi&1],8); pi++; }
    // codewords
    const data=[]; for(let i=0;i<bits.length;i+=8){ let b=0; for(let j=0;j<8;j++) b=(b<<1)|bits[i+j]; data.push(b); }
    // blocks + ecc
    const dBlocks=[],eBlocks=[]; const div=rsDivisor(ecPer); let off=0;
    for(const [b,c] of grp){ for(let k=0;k<b;k++){ const blk=data.slice(off,off+c); off+=c; dBlocks.push(blk); eBlocks.push(rsRemainder(blk,div)); } }
    const out=[]; const maxD=Math.max(...dBlocks.map(d=>d.length));
    for(let i=0;i<maxD;i++) for(const blk of dBlocks) if(i<blk.length) out.push(blk[i]);
    for(let i=0;i<ecPer;i++) for(const blk of eBlocks) out.push(blk[i]);
    const fbits=[]; for(const cw of out) for(let i=7;i>=0;i--) fbits.push((cw>>i)&1);
    // ---- matrix ----
    const size=17+4*version;
    const M=Array.from({length:size},()=>new Array(size).fill(0));
    const R=Array.from({length:size},()=>new Array(size).fill(0));
    const set=(r,c,d)=>{ M[r][c]=d?1:0; R[r][c]=1; };
    const res=(r,c)=>{ R[r][c]=1; };
    function finder(r,c){ for(let dr=-1;dr<=7;dr++) for(let dc=-1;dc<=7;dc++){ const rr=r+dr,cc=c+dc; if(rr<0||cc<0||rr>=size||cc>=size) continue; const d=(dr>=0&&dr<=6&&(dc===0||dc===6))||(dc>=0&&dc<=6&&(dr===0||dr===6))||(dr>=2&&dr<=4&&dc>=2&&dc<=4); set(rr,cc,d); } }
    finder(0,0); finder(0,size-7); finder(size-7,0);
    for(let i=8;i<size-8;i++){ const d=(i%2===0); if(!R[6][i]) set(6,i,d); if(!R[i][6]) set(i,6,d); }
    const ap=ALIGN[version]; for(const r of ap) for(const c of ap){ if((r===6&&c===6)||(r===6&&c===size-7)||(r===size-7&&c===6)) continue; for(let dr=-2;dr<=2;dr++) for(let dc=-2;dc<=2;dc++){ set(r+dr,c+dc, Math.max(Math.abs(dr),Math.abs(dc))!==1); } }
    // reserve format + version areas
    for(let i=0;i<=5;i++) res(i,8); res(7,8); res(8,8); res(8,7); for(let i=9;i<=14;i++) res(8,14-i);
    for(let i=0;i<=7;i++) res(8,size-1-i); for(let i=8;i<=14;i++) res(size-15+i,8); res(size-8,8);
    if(version>=7){ for(let i=0;i<18;i++){ const a=size-11+i%3, b=Math.floor(i/3); res(b,a); res(a,b); } }
    // data
    { let i=0; for(let right=size-1; right>=1; right-=2){ if(right===6) right=5; for(let vert=0; vert<size; vert++){ for(let j=0;j<2;j++){ const col=right-j; const up=(((right+1)&2)===0); const row=up?(size-1-vert):vert; if(!R[row][col]){ M[row][col]=(i<fbits.length)?fbits[i]:0; i++; } } } } }
    // mask fns
    const maskFn=(m,r,c)=>{ switch(m){ case 0:return (r+c)%2===0; case 1:return r%2===0; case 2:return c%3===0; case 3:return (r+c)%3===0; case 4:return (Math.floor(r/2)+Math.floor(c/3))%2===0; case 5:return (r*c)%2+(r*c)%3===0; case 6:return ((r*c)%2+(r*c)%3)%2===0; case 7:return ((r+c)%2+(r*c)%3)%2===0; } };
    function fmtBits(mask){ let data=(0<<3)|mask; let rem=data; for(let i=0;i<10;i++) rem=(rem<<1)^(((rem>>9)&1)*0x537); return ((data<<10)|rem)^0x5412; }
    function verBits(v){ let rem=v; for(let i=0;i<12;i++) rem=(rem<<1)^(((rem>>11)&1)*0x1F25); return (v<<12)|rem; }
    function placeFormat(MM,bits){ for(let i=0;i<=5;i++) MM[i][8]=getBit(bits,i); MM[7][8]=getBit(bits,6); MM[8][8]=getBit(bits,7); MM[8][7]=getBit(bits,8); for(let i=9;i<=14;i++) MM[8][14-i]=getBit(bits,i); for(let i=0;i<=7;i++) MM[8][size-1-i]=getBit(bits,i); for(let i=8;i<=14;i++) MM[size-15+i][8]=getBit(bits,i); MM[size-8][8]=1; }
    function placeVersion(MM,v){ const bits=verBits(v); for(let i=0;i<18;i++){ const bit=getBit(bits,i); const a=size-11+i%3, b=Math.floor(i/3); MM[b][a]=bit; MM[a][b]=bit; } }
    function penalty(MM){ let p=0,n=size;
      for(let r=0;r<n;r++){ let col=MM[r][0],len=1; for(let c=1;c<n;c++){ if(MM[r][c]===col){ if(++len===5)p+=3; else if(len>5)p++; } else { col=MM[r][c]; len=1; } } }
      for(let c=0;c<n;c++){ let col=MM[0][c],len=1; for(let r=1;r<n;r++){ if(MM[r][c]===col){ if(++len===5)p+=3; else if(len>5)p++; } else { col=MM[r][c]; len=1; } } }
      for(let r=0;r<n-1;r++) for(let c=0;c<n-1;c++){ const v=MM[r][c]; if(v===MM[r][c+1]&&v===MM[r+1][c]&&v===MM[r+1][c+1]) p+=3; }
      const pa=[1,0,1,1,1,0,1,0,0,0,0], pb=[0,0,0,0,1,0,1,1,1,0,1];
      const mtch=(get,L,idx,pat)=>{ for(let k=0;k<pat.length;k++){ const x=idx+k; if(x<0||x>=L||get(x)!==pat[k]) return false; } return true; };
      for(let r=0;r<n;r++) for(let c=0;c<n;c++){ if(mtch(x=>MM[r][x],n,c,pa)||mtch(x=>MM[r][x],n,c,pb)) p+=40; }
      for(let c=0;c<n;c++) for(let r=0;r<n;r++){ if(mtch(x=>MM[x][c],n,r,pa)||mtch(x=>MM[x][c],n,r,pb)) p+=40; }
      let dark=0; for(let r=0;r<n;r++) for(let c=0;c<n;c++) dark+=MM[r][c]; const tot=n*n; const pct=dark*100/tot;
      const lo=Math.floor(pct/5)*5, hi=lo+5; p+=Math.min(Math.abs(lo-50),Math.abs(hi-50))/5*10;
      return p;
    }
    let best=null,bestP=Infinity,bestMask=0;
    for(let mask=0;mask<8;mask++){ const cand=M.map(row=>row.slice()); for(let r=0;r<size;r++) for(let c=0;c<size;c++){ if(!R[r][c] && maskFn(mask,r,c)) cand[r][c]^=1; } placeFormat(cand,fmtBits(mask)); if(version>=7) placeVersion(cand,version); const pen=penalty(cand); if(pen<bestP){ bestP=pen; best=cand; bestMask=mask; } }
    return {size,modules:best,version,mask:bestMask};
  }
  return {encode};
})();
  function qrSvg(text){ const q=QR.encode(text); const n=q.size, Q=4, dim=n+2*Q; let d=''; for(let r=0;r<n;r++){ let c=0; while(c<n){ if(q.modules[r][c]){ let run=1; while(c+run<n && q.modules[r][c+run]) run++; d+='M'+(c+Q)+' '+(r+Q)+'h'+run+'v1h-'+run+'z'; c+=run; } else c++; } } return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 '+dim+' '+dim+'" width="100%" height="100%" shape-rendering="crispEdges" role="img" aria-label="QR code linking to this row"><rect width="'+dim+'" height="'+dim+'" fill="#fff"/><path d="'+d+'" fill="#000"/></svg>'; }
  function showQR(){ if(!(mode && entered.length)) return; syncHash(); const url=location.href; let svg; try{ svg=qrSvg(url); }catch(e){ svg='<p class="qr-err">This link is too long to encode as a QR code.</p>'; } const h=$('qr-holder'); if(h) h.innerHTML=svg; const u=$('qr-url'); if(u) u.textContent=url; const m=$('qr-modal'); if(m) m.hidden=false; const cb=$('qr-close'); if(cb) cb.focus(); }
  function openMxIvModal(){
    if(!state) return;
    const M=state.M, N=M.length, r0=M[0][0];
    const P=M[0].slice(), I=M.map(rw=>rw[0]), R=P.slice().reverse(), RI=I.slice().reverse();
    const forms=[['Prime','P',P,'--fam-p'],['Retrograde','R',R,'--fam-r'],['Inversion','I',I,'--fam-i'],['Retrograde inversion','RI',RI,'--fam-ri']];
    let h='';
    for(const f of forms){
      const nm=f[0], tag=f[1], seq=f[2], col=f[3]; let row='';
      for(let k=0;k<seq.length;k++){ row+='<span class="mxiv-n">'+showPc(seq[k])+'</span>'; if(k<seq.length-1) row+='<span class="mxiv-i">'+mod12(seq[k+1]-seq[k])+'</span>'; }
      h+='<div class="mxiv-form"><div class="mxiv-lab" style="color:var('+col+')">'+nm+' <span class="mxiv-tag">'+tag+r0+'</span></div><div class="mxiv-seq">'+row+'</div></div>';
    }
    const bd=$('mxiv-body'); if(bd) bd.innerHTML=h;
    const mv=$('mxiv-modal'); if(mv) mv.hidden=false;
  }
  function closeQR(){ const m=$('qr-modal'); if(m) m.hidden=true; const sq=$('share-qr'); if(sq) sq.focus(); }
  function syncHash(){ let want=''; if(mode && entered.length){ want='#m='+mode+'&r='+entered.map(e=>e.pc).join(','); if(mode==='custom') want+='&n='+customN; } const cur=location.hash||''; if(want!==cur){ try{ history.replaceState(null,'', want || (location.pathname+location.search)); }catch(e){} } const sl=$('share-link'); if(sl) sl.disabled = !(mode && entered.length); const sq2=$('share-qr'); if(sq2) sq2.disabled = !(mode && entered.length); }
  function readHash(src){ try{ const h=(src!==undefined?src:(location.hash||'')).replace(/^#/,''); if(!h) return null; const p=new URLSearchParams(h); const m=p.get('m'), r=p.get('r'); if(!(m==='twelve'||m==='stravinsky'||m==='custom')||!r) return null; const pcs=r.split(',').map(x=>parseInt(x,10)).filter(x=>Number.isInteger(x)&&x>=0&&x<12); if(!pcs.length) return null; const np=p.get('n'); const n=np?parseInt(np,10):null; return {m,pcs,n}; }catch(e){ return null; } }
  function applyRestore(rs){ const m=rs.m; let rowlen; if(m==='custom'){ let n=rs.n; if(!(n>=2&&n<=11)) n=Math.min(11,Math.max(2,rs.pcs.length)); customN=n; rowlen=n; } else rowlen=(m==='stravinsky')?6:12; const pcs=rs.pcs.slice(0,rowlen); modeStash[m].entered=pcs.map(pc=>({pc,name:null})); modeStash[m].state=(pcs.length===rowlen)?buildState(pcs.slice(), m==='custom'?mod12(pcs[0]):0):null; enterMode(m); if(modeStash[m].state) expandSections(); }
  function showGate(){
    saveActive(); mode=null; applyHeader(null);
    $('mode-gate').hidden=false; $('mode-bar').hidden=true; $('workspace').hidden=true;
    document.body.classList.add('no-export');
    document.body.classList.remove('mode-twelve','mode-stravinsky','mode-custom','lede-open','exp-modal-open');
    window.scrollTo({top:0}); syncHash();
  }
  function enterMode(m){
    saveActive();
    mode=m; genPath=false; applyHeader(m); compareReset();
    $('mode-gate').hidden=true; $('mode-bar').hidden=false; const nm=$('mb-name'); if(nm) nm.textContent=({twelve:'Twelve-Tone Row Analyser',stravinsky:'Stravinsky\u2019s Rotational Array',custom:'Custom Row Analyser'})[m]||'';
    document.body.classList.remove('mode-twelve','mode-stravinsky','mode-custom','exp-modal-open'); document.body.classList.add('mode-'+m);
    if(m==='custom'){
      $('workspace').hidden=false;
      ROWLEN=customN; entered=(modeStash.custom.entered||[]).slice(); state=modeStash.custom.state||null;
      genResults=null; buildResults=null; stravForm='P'; stravPick={kind:'row',idx:0};
      document.body.classList.remove('no-export');
      const gen=$('generate'); if(gen) gen.textContent='Generate matrix';
      const t0=$('exp-target'); if(t0 && t0.options[0]) t0.options[0].textContent='Matrix';
      populateExCustom(); renderCustomLen(); renderAll(); window.scrollTo({top:0}); return;
    }
    $('workspace').hidden=false;
    ROWLEN = (m==='stravinsky') ? 6 : 12;
    entered = (modeStash[m].entered||[]).slice(); state = modeStash[m].state||null;
    if(m==='twelve' && state) state=buildState(state.input,0);   // twelve-tone always re-enters rooted on P0
    genResults=null; buildResults=null; stravForm='P'; stravPick={kind:'row',idx:0}; stravIvals=false;
    document.body.classList.toggle('no-export', !(m==='twelve'||m==='stravinsky'));
    { const t0=$('exp-target'); if(t0 && t0.options[0]) t0.options[0].textContent = (m==='stravinsky')?'Array':'Matrix'; }
    const gen=$('generate'); if(gen) gen.textContent = (m==='stravinsky') ? 'Build arrays' : 'Generate matrix';
    renderAll();
    window.scrollTo({top:0});
  }

  // ---------- Stravinsky rotational arrays ----------
  const ROMAN=['I','II','III','IV','V','VI','VII','VIII','IX','X','XI','XII'];
  function rotArray(hex){ const N=hex.length, rows=[]; for(let r=0;r<N;r++){ const rot=[]; for(let k=0;k<N;k++) rot.push(hex[(r+k)%N]); const t=mod12(hex[0]-rot[0]); rows.push({pcs:rot.map(x=>mod12(x+t)), t}); } return rows; }
  function stravFormHex(h,f){ if(f==='I') return h.map(x=>mod12(2*h[0]-x)); if(f==='R') return h.slice().reverse(); if(f==='IR'){ const R=h.slice().reverse(); return R.map(x=>mod12(2*R[0]-x)); } return h.slice(); }
  function renderStravinsky(){
    const sec=$('stravinsky-section'); if(!sec) return;
    if(mode!=='stravinsky' || !state){ sec.classList.add('hidden'); return; }
    sec.classList.remove('hidden');
    const body=$('strav-body'); if(!body) return;
    const h=state.input.slice();
    const nf=normalForm(h), pf=primeForm(h), v=icVector(h), fn=forteName(h), sy=symDegrees(h);
    const ivals=h.slice(1).map((x,i)=>mod12(x-h[i]));
    let html='<div class="strav-ident"><div class="si-row">'+
        `<span><span class="si-k">hexachord</span><span class="si-v">${h.map(showPc).join(' ')}</span></span>`+
        `<span><span class="si-k">prime</span><span class="si-v sc">(${pf.map(pcTok).join('')})${fn?' '+fn:''}</span></span>`+
        `<span><span class="si-k">ic vector</span><span class="si-v">[${v.join('')}]</span></span>`+
      '</div><div class="si-row">'+
        `<span><span class="si-k">normal</span><span class="si-v">[${nf.map(pcTok).join(',')}]</span></span>`+
        `<span><span class="si-k">intervals</span><span class="si-v">${ivals.join(' ')}</span></span>`+
        `<span><span class="si-k">symmetry</span><span class="si-v">T-${sy.T}\u00b7I-${sy.I}</span></span>`+
      '</div></div>';
    html+='<div class="strav-forms"><span class="sf-lbl">Form</span>'+
      ['P','I','R','IR'].map(f=>`<button type="button" class="sf-btn" data-sf="${f}" aria-pressed="${f===stravForm}">${f}</button>`).join('')+'</div>';
    const fh=stravFormHex(h,stravForm), arr=rotArray(fh), cen=fh[0], N=fh.length;
    html+=`<div class="arr-title"><h3>Array of the ${stravForm}-form hexachord</h3><span class="arr-sub">first column = ${showPc(cen)} (centric)</span></div>`;
    html+=`<button type="button" class="iv-toggle" id="iv-toggle" aria-pressed="${stravIvals}">Show Intervallic Distances</button>`;
    if(stravIvals){
      // interleaved grid: notes with horizontal intervals between columns and vertical intervals between rows
      let g='<div class="rot-grid" style="grid-template-columns:auto repeat('+(2*N-1)+',auto)">';
      g+='<div class="rg-corner"></div>';
      for(let j=0;j<N;j++){ const colpcs=arr.map(r=>r.pcs[j]); g+= j===0 ? `<div class="rg-head" title="v1 - centric pitch (same note in every row)">v1</div>` : `<div class="rg-head strav-play" data-pcs="${colpcs.join(',')}" title="Play vertical v${j+1}">v${j+1}</div>`; if(j<N-1) g+='<div class="rg-gap"></div>'; }
      arr.forEach((row,i)=>{
        g+=`<div class="rg-lab strav-play" data-pcs="${row.pcs.join(',')}" title="Play row ${ROMAN[i]}">${ROMAN[i]}<span class="tn">T${row.t}</span></div>`;
        row.pcs.forEach((pc,j)=>{
          g+=`<div class="rg-cell${j===0?' cen':''}">${showPc(pc)}</div>`;
          if(j<N-1){ const hi=mod12(row.pcs[j+1]-pc); g+=`<div class="rg-h">${hi}</div>`; }
        });
        if(i<N-1){
          g+='<div class="rg-lab"></div>';
          for(let j=0;j<N;j++){ if(j===0){ g+='<div class="rg-v"></div>'; } else { const vi=mod12(arr[i+1].pcs[j]-row.pcs[j]); g+=`<div class="rg-v">${vi}</div>`; } if(j<N-1) g+='<div class="rg-gap"></div>'; }
        }
      });
      g+='</div>';
      html+='<div class="rot-scroll">'+g+'</div>';
      html+='<div class="rg-legend">Gray numbers are directed intervals in semitones (mod 12): <b>between columns</b> = the melodic succession across each row; <b>between rows</b> = the voice-leading down each vertical.</div>';
    } else {
      html+='<div class="rot-scroll"><table class="rot"><tr><th></th>'+arr[0].pcs.map((_,j)=>{ const colpcs=arr.map(r=>r.pcs[j]); return j===0 ? `<th title="v1 - centric pitch (same note in every row)">v1</th>` : `<th class="strav-play" data-pcs="${colpcs.join(',')}" title="Play vertical v${j+1}">v${j+1}</th>`; }).join('')+'</tr>';
      arr.forEach((row,i)=>{ html+=`<tr><th class="rlab strav-play" data-pcs="${row.pcs.join(',')}" title="Play row ${ROMAN[i]}">${ROMAN[i]}<span class="tn">T${row.t}</span></th>`+row.pcs.map((pc,j)=>`<td class="${j===0?'cen':''}">${showPc(pc)}</td>`).join('')+'</tr>'; });
      html+='</table></div>';
    }
    html+='<p class="strav-note">Each row rotates the hexachord one place and transposes it back to begin on '+
      `<b>${showPc(cen)}</b>, so the first column is one constant pitch class \u2014 what Straus calls a <b>centric</b> note and axis of symmetry for the other verticals. `+
      'Reading the rows top to bottom composes-out the inversion of the hexachord (a six-voice canon); the columns are the verticals Stravinsky used as harmonies (analysed below). He derived such arrays from each hexachord of four untransposed forms: <b>P</b>, <b>I</b>, <b>R</b>, and <b>IR</b> (inversion of the retrograde).</p>';
    body.innerHTML=html;
    body.querySelectorAll('.sf-btn').forEach(b=>b.addEventListener('click',()=>{ stravForm=b.dataset.sf; renderStravinsky(); renderSubset(); renderCompare(); }));
    { const iv=$('iv-toggle'); if(iv) iv.addEventListener('click',()=>{ stravIvals=!stravIvals; renderStravinsky(); }); }
  }

  // ---------- Stravinsky exports (text · PNG via textCanvas · PDF report) ----------
  function stravIdentLines(){
    const h=state.input.slice(), nf=normalForm(h), pf=primeForm(h), v=icVector(h), fn=forteName(h), sy=symDegrees(h), iv=h.slice(1).map((x,i)=>mod12(x-h[i]));
    return ['Hexachord:  '+h.map(showPc).join(' '),
            'Prime:      ('+pf.map(pcTok).join('')+')'+(fn?'  '+fn:''),
            'Normal:     ['+nf.map(pcTok).join(',')+']',
            'IC vector:  ['+v.join('')+']',
            'Intervals:  '+iv.join(' ')+'   (directed, mod 12)',
            'Symmetry:   T-'+sy.T+'  I-'+sy.I];
  }
  function stravArrGrid(arr,N){
    const head=['', ...Array.from({length:N},(_,j)=>'v'+(j+1))];
    const all=[head, ...arr.map((row,i)=>[ROMAN[i]+' T'+row.t, ...row.pcs.map(showPc)])];
    const w=new Array(N+1).fill(0);
    for(const r of all) for(let c=0;c<=N;c++) w[c]=Math.max(w[c],(r[c]||'').length);
    return all.map(r=>r.map((c,i)=> i===0?(c||'').padEnd(w[0]):(c||'').padStart(w[i])).join('  ').replace(/\s+$/,''));
  }
  function stravVertLines(arr,N,cen){
    const L=[];
    for(let j=0;j<N;j++){ const col=arr.map(r=>r.pcs[j]);
      if(j===0) L.push('  v1  '+showPc(cen)+'   (centric, single pc)');
      else { const d=[...new Set(col)], pf=primeForm(d), fn=forteName(d); L.push('  v'+(j+1)+'  '+col.map(showPc).join(' ')+'   ('+pf.map(pcTok).join('')+')'+(fn?' '+fn:'')); }
    }
    return L;
  }
  function stravSubsetLines(){
    const N=state.input.length, L=['SUBSET ANALYSIS (of the hexachord)'];
    [2,3,4,5,6].filter(k=>N%k===0 && k<N).forEach(k=>{ const info=segInfo(k), ab=segAbbr(k);
      L.push(''); L.push('  '+cap(segWord(k))+'s ('+info.count+'):');
      info.cards.forEach((c,idx)=>{ const cells=[(ab+'-'+(idx+1)).padEnd(6), c.pcs.map(showPc).join(' ').padEnd(14), (c.forte||'').padEnd(7), ('('+c.pf.map(pcTok).join('')+')').padEnd(9), 'ic['+c.icv.join('')+']'];
        if(c.tonal) cells.push('\u00b7 '+c.tonal); L.push(('    '+cells.join('  ')).replace(/\s+$/,'')); });
      L.push('    \u2192 '+summaryLine(info));
    });
    return L;
  }
  const stravModeLine='Stravinsky derived rotational arrays from each hexachord of four untransposed forms \u2014 P, I, R, and IR (inversion of the retrograde). The constant first column is a centric pitch class and axis of symmetry; the columns are the verticals he used as harmonies.';
  function stravArrayText(){
    const h=state.input.slice(), fh=stravFormHex(h,stravForm), arr=rotArray(fh), N=fh.length, cen=fh[0];
    const L=['STRAVINSKY ROTATIONAL ARRAY','('+(dispMode==='notes'?'note names':'integers')+')',''].concat(stravIdentLines(),
      ['','ARRAY \u2014 '+stravForm+'-form   (first column = '+showPc(cen)+', centric)','']);
    stravArrGrid(arr,N).forEach(l=>L.push('  '+l));
    L.push(''); L.push('VERTICALS \u2014 columns as harmonies'); stravVertLines(arr,N,cen).forEach(l=>L.push(l));
    return L.join('\n');
  }
  function stravAnalysisText(){
    const h=state.input.slice(), fh=stravFormHex(h,stravForm), arr=rotArray(fh), N=fh.length, cen=fh[0];
    const L=['STRAVINSKY ROTATIONAL ARRAY \u2014 ANALYSIS','('+(dispMode==='notes'?'note names':'integers')+')',''].concat(stravIdentLines(),
      ['','VERTICALS \u2014 '+stravForm+'-form  (first column = '+showPc(cen)+', centric)']);
    stravVertLines(arr,N,cen).forEach(l=>L.push(l));
    L.push(''); stravSubsetLines().forEach(l=>L.push(l));
    return L.join('\n');
  }
  function stravFullText(){
    const h=state.input.slice();
    const L=['STRAVINSKY ROTATIONAL ARRAYS \u2014 FULL REPORT','('+(dispMode==='notes'?'note names':'integers')+')',''].concat(stravIdentLines(),['']);
    ['P','I','R','IR'].forEach(f=>{ const fh=stravFormHex(h,f), arr=rotArray(fh), N=fh.length, cen=fh[0];
      L.push('ARRAY \u2014 '+f+'-form   (first column = '+showPc(cen)+', centric)'); L.push('');
      stravArrGrid(arr,N).forEach(l=>L.push('  '+l));
      L.push(''); stravVertLines(arr,N,cen).forEach(l=>L.push(l)); L.push(''); });
    stravSubsetLines().forEach(l=>L.push(l));
    L.push(''); L.push(stravModeLine);
    return L.join('\n');
  }
  const STRAV_TXT={matrix:stravArrayText, analysis:stravAnalysisText, full:stravFullText};
  const STRAV_FN ={matrix:'stravinsky-array', analysis:'stravinsky-analysis', full:'stravinsky-full-report'};

  const STRAV_REPORT_CSS='table.rotx{font-size:11px;margin:6px 0}table.rotx th,table.rotx td{border:1px solid #e2e2dd;padding:3px 7px;text-align:center;min-width:26px}'
    +'table.rotx th{background:#f4f4f1;color:#555;font-weight:600}table.rotx th.rl{text-align:right;white-space:nowrap}table.rotx th.rl span{display:block;font-size:9px;color:#999;font-weight:400}'
    +'table.rotx td.cen{background:#eceaff;color:#4733e6;font-weight:700}table.rotx tr.ivr td{border:none;color:#aaa;font-size:9px;padding:1px 7px}table.rotx tr.ivr th{border:none;background:transparent}'
    +'table.vtab{font-size:10px;margin:6px 0 10px}table.vtab th,table.vtab td{border:1px solid #e2e2dd;padding:3px 7px;text-align:left}table.vtab th{background:#f4f4f1;color:#444;font-weight:600}';
  function stravArrTableHTML(arr,N,cen){
    let h='<table class="rotx"><tr><th></th>'; for(let j=0;j<N;j++) h+='<th>v'+(j+1)+'</th>'; h+='</tr>';
    arr.forEach((row,i)=>{ h+='<tr><th class="rl">'+ROMAN[i]+'<span>T'+row.t+'</span></th>'+row.pcs.map((pc,j)=>'<td class="'+(j===0?'cen':'')+'">'+esc(showPc(pc))+'</td>').join('')+'</tr>';
      if(i<N-1){ h+='<tr class="ivr"><th></th>'; for(let j=0;j<N;j++){ const vi=mod12(arr[i+1].pcs[j]-row.pcs[j]); h+='<td>'+vi+'</td>'; } h+='</tr>'; } });
    return h+'</table>';
  }
  function stravReportHTML(target){
    const h0=state.input.slice(), pf=primeForm(h0), v=icVector(h0), fn=forteName(h0), iv=h0.slice(1).map((x,i)=>mod12(x-h0[i]));
    const titles={matrix:'Stravinsky’s Rotational Array', analysis:'Stravinsky’s Array \u2014 Analysis', full:'Stravinsky’s Rotational Arrays \u2014 Full Report'}, title=titles[target]||titles.full;
    const head='<h1>'+esc(title)+'</h1>'
      +'<div class="sub">'+(dispMode==='notes'?'note names':'integers')+' \u00b7 generated '+esc(new Date().toLocaleString())+'</div>'
      +'<div class="rowline"><b>Hexachord</b>&nbsp;&nbsp;'+esc(h0.map(showPc).join('  '))+'</div>'
      +'<div class="rowline"><b>Prime</b>&nbsp;&nbsp;('+pf.map(pcTok).join('')+')'+(fn?'  '+esc(fn):'')+'&nbsp;&nbsp;\u00b7&nbsp;&nbsp;ic ['+v.join('')+']&nbsp;&nbsp;\u00b7&nbsp;&nbsp;intervals '+iv.join(' ')+'</div>';
    const forms = target==='full' ? ['P','I','R','IR'] : [stravForm];
    let arrs='';
    forms.forEach(f=>{ const fh=stravFormHex(h0,f), arr=rotArray(fh), N=fh.length, cen=fh[0];
      arrs+='<div class="block"><h2>Array \u2014 '+f+'-form (centric '+esc(showPc(cen))+')</h2>'+stravArrTableHTML(arr,N,cen)
        +'<div class="cap">rows between note rows = vertical intervals (semitones, mod 12)</div>'
        +'<table class="vtab"><tr><th>vertical</th><th>pitches</th><th>set class</th></tr>';
      for(let j=0;j<N;j++){ const col=arr.map(r=>r.pcs[j]);
        if(j===0) arrs+='<tr><td>v1</td><td>'+esc(showPc(cen))+'</td><td>centric (single pc)</td></tr>';
        else { const d=[...new Set(col)], cpf=primeForm(d), cfn=forteName(d); arrs+='<tr><td>v'+(j+1)+'</td><td>'+esc(col.map(showPc).join(' '))+'</td><td>('+cpf.map(pcTok).join('')+')'+(cfn?' '+esc(cfn):'')+'</td></tr>'; } }
      arrs+='</table></div>';
    });
    let sub='';
    if(target!=='matrix'){
      const N=h0.length; sub='<h2>Subset analysis (of the hexachord)</h2>';
      [2,3,4,5,6].filter(k=>N%k===0 && k<N).forEach(k=>{ const info=segInfo(k), ab=segAbbr(k);
        sub+='<div class="block"><h3 class="sub-h">'+cap(segWord(k))+'s ('+info.count+')</h3><table class="sc"><tr><th>seg</th><th>pcs</th><th>name</th><th>prime</th><th>ic vector</th></tr>';
        info.cards.forEach((c,idx)=>{ sub+='<tr><td class="si">'+ab+'-'+(idx+1)+(c.forte?' <span class="fn">'+c.forte+'</span>':'')+'</td><td>'+esc(c.pcs.map(showPc).join(' '))+'</td><td>'+(c.tonal?esc(c.tonal):'\u2014')+'</td><td>('+c.pf.map(pcTok).join('')+')</td><td>['+c.icv.join('')+']</td></tr>'; });
        sub+='</table><div class="summ">'+esc(summaryLine(info))+'</div></div>';
      });
      sub+='<p class="rowline" style="margin-top:10px;color:#555">'+esc(stravModeLine)+'</p>';
    }
    const body = target==='matrix' ? arrs : (arrs+sub);
    const cf=citeFmtNow(), citeFoot = cf ? '<div class="cite-foot">Cite this tool ('+esc(CITE_LABELS[cf]||cf)+'): '+esc(citationText(cf).replace(/\n/g,' '))+'</div>' : '';
    return '<!DOCTYPE html><html><head><meta charset="utf-8"><title>'+esc(title)+'</title><style>'+REPORT_CSS+STRAV_REPORT_CSS+'</style></head><body>'+head+body+citeFoot
      +'<scr'+'ipt>window.onload=function(){setTimeout(function(){try{window.print();}catch(e){}},300);};<\/scr'+'ipt></body></html>';
  }

  // ---------- Custom mode: row-length picker ----------
  function renderCustomLen(){
    const host=$('cl-btns'); if(!host) return; host.innerHTML='';
    for(let n=2;n<=11;n++){
      const b=document.createElement('button'); b.type='button';
      b.className='cl-btn'+(n===customN?' on':''); b.textContent=String(n);
      b.setAttribute('aria-pressed', String(n===customN));
      b.addEventListener('click',()=>{
        if(customN===n) return;
        customN=n; ROWLEN=n; entered=[]; state=null; genResults=null; buildResults=null;
        modeStash.custom.entered=[]; modeStash.custom.state=null;
        const ex=$('ex-note'); if(ex) ex.textContent='';
        populateExCustom(); renderCustomLen(); renderAll();
      });
      host.appendChild(b);
    }
  }

  // ---------- Custom mode: row forms read off the n×n matrix ----------
  function renderFormsCustom(){
    const {M,inputRowIndex}=state, N=M.length, col=j=>M.map(r=>r[j]), total=4*N;
    const h2=$('forms-h2'); if(h2) h2.textContent='The '+total+' row forms';
    const rs=$('row-sym');
    if(rs){
      const all=[];
      for(let i=0;i<N;i++){ all.push(M[i].join(',')); all.push(M[i].slice().reverse().join(',')); }
      for(let j=0;j<N;j++){ const c=col(j); all.push(c.join(',')); all.push(c.slice().reverse().join(',')); }
      const distinct=new Set(all).size;
      rs.innerHTML='<b>'+total+'</b> forms read off the '+N+'×'+N+' matrix — P (rows), I (columns), R (rows reversed), RI (columns reversed)'+
        (distinct<total ? ' — the row’s symmetry collapses these to <b>'+distinct+'</b> distinct.' : ' — all '+total+' are distinct.');
    }
    const wrap=$('forms-grid'); wrap.innerHTML='';
    [{name:'Prime',tag:'P'},{name:'Inversion',tag:'I'},{name:'Retrograde',tag:'R'},{name:'Retrograde-Inversion',tag:'RI'}].forEach(f=>{
      const box=document.createElement('div'); box.className='fam fam-'+f.tag.toLowerCase();
      box.innerHTML='<h3>'+f.name+' <span class="tag">'+f.tag+' ×'+N+'</span></h3>';
      for(let k=0;k<N;k++){
        let seq, lab;
        if(f.tag==='P'){ seq=M[k]; lab='P'+M[k][0]; }
        else if(f.tag==='I'){ seq=col(k); lab='I'+M[0][k]; }
        else if(f.tag==='R'){ seq=M[k].slice().reverse(); lab='R'+M[k][0]; }
        else { seq=col(k).slice().reverse(); lab='RI'+M[0][k]; }
        const line=document.createElement('div'); line.className='fline'+((f.tag==='P'&&k===inputRowIndex)?' mark':'');
        line.innerHTML='<span class="flab">'+lab+'</span><span class="fpc">'+seq.map(showPc).join(' ')+'</span>';
        line.dataset.pcs=seq.join(','); line.classList.add('playable');
        box.appendChild(line);
      }
      decorateFam(box, f.tag);
      wrap.appendChild(box);
    });
  }

  // ---------- Compare two rows ----------
  let compareSel={a:null,b:null,bTyped:false,typed:[]};
  function compareReset(){ compareSel={a:null,b:null,bTyped:false,typed:[]}; }
  function allFormsM(M){
    const N=M.length, col=j=>M.map(r=>r[j]), out=[];
    for(let i=0;i<N;i++) out.push({label:'P'+M[i][0], pcs:M[i].slice()});
    for(let j=0;j<N;j++) out.push({label:'I'+M[0][j], pcs:col(j)});
    for(let i=0;i<N;i++) out.push({label:'R'+M[i][0], pcs:M[i].slice().reverse()});
    for(let j=0;j<N;j++) out.push({label:'RI'+M[0][j], pcs:col(j).slice().reverse()});
    return out;
  }
  // ordered note-for-note transform A->B; returns 'T5','T5I','RT5','RT5I' or null.
  function orderedTransform(A,B){
    if(A.length!==B.length||!A.length) return null;
    const N=A.length, ra=A.slice().reverse();
    const cst=(base,inv)=>{ let k=null; for(let p=0;p<N;p++){ const w=inv?mod12(B[p]+base[p]):mod12(B[p]-base[p]); if(k===null)k=w; else if(k!==w) return null; } return k; };
    let k;
    if((k=cst(A,false))!==null) return 'T'+k;
    if((k=cst(A,true ))!==null) return 'T'+k+'I';
    if((k=cst(ra,false))!==null) return 'RT'+k;
    if((k=cst(ra,true ))!==null) return 'RT'+k+'I';
    return null;
  }
  function opGloss(lab){
    if(!lab) return '';
    const m=lab.match(/^(R?)T(\d+)(I?)$/); if(!m) return '';
    const retro=m[1]==='R', k=m[2], inv=m[3]==='I', t0=(k==='0');
    if(!retro&&!inv) return t0?'identical':'transposition by '+k;
    if(!retro&&inv)  return 'inversion (T'+k+'I)';
    if(retro&&!inv)  return t0?'retrograde (R)':'retrograde, then T'+k;
    return t0?'retrograde-inversion (RI)':'retrograde-inversion, then T'+k;
  }
  const cmpKey=seg=>uniqSort(seg).join(',');
  function cmpSegs(pcs,k){ const o=[]; for(let i=0;i+k<=pcs.length;i+=k) o.push(pcs.slice(i,i+k)); return o; }
  function cmpSetTok(key){ return '{'+key.split(',').map(x=>showPc(+x)).join(',')+'}'; }
  function stravForms(){
    if(!state) return [];
    const fh=stravFormHex(state.input.slice(), stravForm), arr=rotArray(fh), N=fh.length, out=[];
    for(let i=0;i<N;i++) out.push({label:ROMAN[i], pcs:arr[i].pcs.slice()});
    for(let j=0;j<N;j++){ const col=arr.map(r=>r.pcs[j]); if(new Set(col).size===N) out.push({label:'v'+(j+1), pcs:col}); }
    return out;
  }
  function renderCompare(){
    const sec=$('compare-section'); if(!sec) return;
    if(!state || (mode!=='twelve'&&mode!=='custom'&&mode!=='stravinsky')){ sec.classList.add('hidden'); return; }
    const forms = (mode==='stravinsky') ? stravForms() : allFormsM(state.M);
    if(!forms.length){ sec.classList.add('hidden'); return; }
    sec.classList.remove('hidden');
    const labels=forms.map(f=>f.label), labSet=new Set(labels);
    const fp=state.firstPc;
    const defA = (mode==='stravinsky') ? forms[0].label : (labSet.has('P'+fp)?('P'+fp):labels[0]);
    const defB = (mode==='stravinsky') ? (forms[1]||forms[0]).label : (labSet.has('R'+fp)?('R'+fp):labels[Math.min(1,labels.length-1)]);
    if(!labSet.has(compareSel.a)) compareSel.a = defA;
    if(!labSet.has(compareSel.b)) compareSel.b = defB;
    const selA=$('cmp-a'), selB=$('cmp-b');
    const opts=forms.map(f=>'<option value="'+f.label+'">'+f.label+'  '+f.pcs.map(showPc).join(' ')+'</option>').join('');
    if(selA){ selA.innerHTML=opts; selA.value=compareSel.a; }
    if(selB){ selB.innerHTML=opts; selB.value=compareSel.b; }
    const bForm=$('cmp-b-form'), bType=$('cmp-b-type'), bin=$('cmp-bin'), swap=$('cmp-swap');
    if(bForm) bForm.setAttribute('aria-pressed', String(!compareSel.bTyped));
    if(bType) bType.setAttribute('aria-pressed', String(compareSel.bTyped));
    if(selB) selB.style.display = compareSel.bTyped?'none':'';
    if(bin)  bin.style.display  = compareSel.bTyped?'':'none';
    if(swap) swap.disabled = compareSel.bTyped;
    const A = forms.find(f=>f.label===compareSel.a).pcs;
    const aLabel = compareSel.a;
    let B, bLabel;
    if(compareSel.bTyped){ B=compareSel.typed.slice(); bLabel='typed row'; }
    else { const fb=forms.find(f=>f.label===compareSel.b); B=fb.pcs; bLabel=fb.label; }
    const body=$('compare-body'); if(!body) return;
    if(compareSel.bTyped && (!B||!B.length)){
      body.innerHTML='<div class="cmp-foot">Type a row in the box above and press <b>Set</b> to compare it against form '+aLabel+'.</div>';
      return;
    }
    const m=Math.min(A.length,B.length);
    const inv=[]; for(let p=0;p<m;p++) if(A[p]===B[p]) inv.push(p);
    const invSet=new Set(inv);
    const sa=new Set(A), sb=new Set(B);
    const common=[...sa].filter(x=>sb.has(x)).sort((p,q)=>p-q);
    const aggBoth=(sa.size===12 && sb.size===12);
    const rel=orderedTransform(A,B);
    const lenNote = A.length!==B.length ? ' <span class="cmp-foot">(lengths differ: '+A.length+' vs '+B.length+'; positions compared over the first '+m+')</span>' : '';
    function sharedSeg(k){
      const aS=cmpSegs(A,k), bS=cmpSegs(B,k);
      const aK=aS.map(cmpKey), bK=bS.map(cmpKey), bset=new Set(bK);
      const sharedK=[...new Set(aK.filter(x=>bset.has(x)))];
      const mm=Math.min(aS.length,bS.length); const posSet=new Set();
      for(let i=0;i<mm;i++) if(aK[i]===bK[i]) posSet.add(aK[i]);
      return {sharedK, posSet};
    }
    const dy=sharedSeg(2), tri=sharedSeg(3);
    let h='';
    h+='<div class="cmp-rel">A &#8594; B&nbsp; <b>'+(rel||'\u2014')+'</b>'+(rel?'<span class="cmp-relgloss">'+opGloss(rel)+'</span>':'<span class="cmp-relgloss">not a single standard operation (the two are not transforms of one another)</span>')+'</div>';
    const Lmax=Math.max(A.length,B.length);
    const ruler='<div class="cmp-arow cmp-ruler"><span class="cmp-rlab"></span><div class="cmp-cells">'+Array.from({length:Lmax},(_,p)=>'<div class="cmp-cell">'+(p+1)+'</div>').join('')+'</div></div>';
    const rowHTML=(label,pcs)=>{
      let cells='';
      for(let p=0;p<Lmax;p++){
        if(p<pcs.length){ const hl=(p<m && invSet.has(p))?' cmp-inv':''; cells+='<div class="cmp-cell'+hl+'">'+showPc(pcs[p])+'</div>'; }
        else cells+='<div class="cmp-cell cmp-blank"></div>';
      }
      return '<div class="cmp-arow"><span class="cmp-rlab"><button class="cmp-play" data-pcs="'+pcs.join(',')+'" title="Play '+label+'">\u25b6</button><span class="flab">'+label+'</span></span><div class="cmp-cells">'+cells+'</div></div>';
    };
    h+='<div class="cmp-align">'+ruler+rowHTML(aLabel,A)+rowHTML(bLabel,B)+'</div>';
    h+='<div class="cmp-stats">';
    h+='<div class="cmp-stat"><span class="cs-lab">Order-position invariants</span>'+inv.length+(inv.length?': '+inv.map(p=>(p+1)+' (pc '+showPc(A[p])+')').join(', '):' \u2014 no position holds the same pitch class')+lenNote+'</div>';
    h+='<div class="cmp-stat"><span class="cs-lab">Common pitch classes</span>'+common.length+(common.length?': <span class="cmp-set">'+common.map(showPc).join(' ')+'</span>':'')+(aggBoth?'<div class="cmp-foot">Both forms are complete twelve-tone aggregates, so all 12 pitch classes are shared by definition &mdash; the order-position invariants above are the meaningful measure here.</div>':'')+'</div>';
    const segLine=(name,res)=>{
      const list=res.sharedK.map(key=>cmpSetTok(key)+(res.posSet.has(key)?'\u25cf':'')).join(', ');
      return '<div class="cmp-stat"><span class="cs-lab">Shared '+name+'</span>'+res.sharedK.length+(res.sharedK.length?': <span class="cmp-set">'+list+'</span>':'')+'</div>';
    };
    if(A.length>=2 && B.length>=2) h+=segLine('dyads',dy);
    if(A.length>=3 && B.length>=3) h+=segLine('trichords',tri);
    if(dy.posSet.size||tri.posSet.size) h+='<div class="cmp-foot">\u25cf = the segment also occupies the same position in both rows (a positional invariant).</div>';
    h+='</div>';
    body.innerHTML=h;
  }

  function renderAll(){ renderPalette(); renderSlots(); updateToggles(); renderStatus(); renderMatrix(); renderForms(); renderSubset(); renderCompare(); renderExport(); updateDeriveZone(); renderGenResults(); renderBuild(); renderStravinsky(); applyPath(); syncHash(); }

  // ---------- actions ----------
  $('generate').addEventListener('click',()=>{ if(entered.length!==ROWLEN) return; state=bs(enteredPcs()); if(mode==='stravinsky') stravIvals=false; expandSections(); renderAll(); });
  { const b=$('path-input-btn'); if(b) b.addEventListener('click',()=>{ if(!genPath) return; genPath=false; applyPath(); }); }
  { const b=$('path-gen-btn'); if(b) b.addEventListener('click',()=>{ if(genPath) return; genPath=true; applyPath(); }); }
  { const a=$('mx-prev');  if(a) a.addEventListener('click',()=>reRoot(-1)); }
  { const a=$('mx-next');  if(a) a.addEventListener('click',()=>reRoot(1)); }
  { const a=$('mx-reset'); if(a) a.addEventListener('click',()=>{ if(state) reRootTo(mode==='custom'?state.firstPc:0); }); }

  document.querySelectorAll('.panel-head.collapsible').forEach(h=>{
    const toggle=()=>{ const sec=h.closest('section'); if(!sec) return; const col=sec.classList.toggle('collapsed'); h.setAttribute('aria-expanded', String(!col)); };
    h.addEventListener('click',toggle);
    h.addEventListener('keydown',e=>{ if(e.key==='Enter'||e.key===' '){ e.preventDefault(); toggle(); } });
  });
  $('undo').addEventListener('click',()=>{ entered.pop(); state=null; genResults=null; renderAll(); });
  $('clear').addEventListener('click',()=>{ entered=[]; state=null; genResults=null; $('type-err').textContent=''; const ex=$('ex-note'); if(ex) ex.textContent=''; renderAll(); });

  $('exp-target').addEventListener('change',updateExpButtons);
  $('exp-fmt').addEventListener('change',updateExpButtons);
  $('exp-copy').addEventListener('click',()=>{ if(!state) return; if($('exp-fmt').value==='png'){ copyImage(); return; } const t=$('exp-target').value;
    const txt = mode==='stravinsky' ? (STRAV_TXT[t]?STRAV_TXT[t]():null) : txtBuild(t);
    if(txt!=null) copyText(txt); });
  $('exp-run').addEventListener('click',()=>{
    if(!state) return;
    if(!citeFmtNow()){ const w=$('exp-warn'); if(w) w.classList.add('show'); return; }
    const t=$('exp-target').value, f=$('exp-fmt').value;
    if(f==='pdf'){ openPDF(); return; }
    if(f==='png'){ exportPNG(); return; }
    if(f==='csv'){ const grid=gridTabText(t); if(grid){ const fn=(mode==='stravinsky')?((STRAV_FN[t]||'rotational-array')+'.csv'):fnFor(t,'csv'); dlCsv(fn, tabToCsv(grid)+csvFooter(t)); expNote('Saved '+fn); } return; }
    if(mode==='stravinsky'){ const gen=STRAV_TXT[t]; if(gen){ const fn=STRAV_FN[t]+'.txt'; dlText(fn,gen()+citeFooterText(t)); expNote('Saved '+fn); } return; }
    { const fn=fnFor(t,'txt'); dlText(fn, txtBuild(t)+citeFooterText(t)); expNote('Saved '+fn); }
  });

  // ----- citation preview modal -----
  function openCiteModal(){
    const fmt=citeFmtNow(), tx=$('cite-text'), fl=$('cite-modal-fmt'), cc=$('cite-copied');
    const foot=document.querySelector('#cite-modal .modal-foot');
    if(cc){ cc.classList.remove('show'); cc.textContent='Citation Successfully Copied!'; }
    if(fmt){ if(fl) fl.textContent=(CITE_LABELS[fmt]||fmt); if(tx) tx.textContent=citationText(fmt); if(foot) foot.style.display='flex'; }
    else { if(fl) fl.textContent=''; if(tx) tx.textContent='Choose a citation format, then press \u201cPreview citation\u201d.'; if(foot) foot.style.display='none'; }
    const ov=$('cite-modal'); if(ov) ov.hidden=false;
  }
  function closeCiteModal(){ const ov=$('cite-modal'); if(ov) ov.hidden=true; }
  $('cite-fmt').addEventListener('change',updateExpButtons);
  $('cite-preview').addEventListener('click',openCiteModal);
  (function(){ const ov=$('cite-modal'); if(ov) ov.addEventListener('click',e=>{ if(e.target===ov) closeCiteModal(); }); })();
  document.addEventListener('keydown',e=>{ if(e.key==='Escape'){ const ov=$('cite-modal'); if(ov && !ov.hidden) closeCiteModal(); } });
  $('cite-copy').addEventListener('click',()=>{
    const fmt=citeFmtNow(); if(!fmt) return; const text=citationText(fmt), cc=$('cite-copied');
    const done=ok=>{ if(!cc) return; cc.textContent= ok ? 'Citation Successfully Copied!' : 'Copy blocked \u2014 select the text to copy it manually.'; cc.classList.add('show'); };
    if(navigator.clipboard&&navigator.clipboard.writeText){ navigator.clipboard.writeText(text).then(()=>done(true)).catch(()=>done(fallbackCopy(text))); }
    else done(fallbackCopy(text));
  });
  { const _sb=$('subset-body'); if(_sb) _sb.addEventListener('click',e=>{ const btn=e.target.closest('.seg-play'); if(!btn) return; const pcs=(btn.dataset.pcs||'').split(',').filter(s=>s!=='').map(Number); if(!pcs.length) return; if(btn.dataset.pl==='chord') playChord(pcs, +(btn.dataset.inv||0)); else playSeq(pcs); }); }
  { const _ib=$('ss-imbricate'); if(_ib) _ib.addEventListener('click',()=>{ imbricate=!imbricate; renderSubset(); }); }
  function filledSlotEls(){ return Array.from($('slots').querySelectorAll('.slot.filled')); }
  function dropIndexAt(x){ const els=filledSlotEls(); for(let i=0;i<els.length;i++){ const r=els[i].getBoundingClientRect(); if(x < r.left + r.width/2) return i; } return els.length; }
  function clearDropMarker(){ const h=$('slots'); if(h) h.querySelectorAll('.drop-before,.drop-after').forEach(x=>x.classList.remove('drop-before','drop-after')); }
  function setDropMarker(t){ clearDropMarker(); const els=filledSlotEls(); if(!els.length) return; if(t<els.length) els[t].classList.add('drop-before'); else els[els.length-1].classList.add('drop-after'); }
  function reorderReset(){ state=null; genResults=null; const ex=$('ex-note'); if(ex) ex.textContent=''; }
  function moveEntered(from,to){ if(from<0||from>=entered.length) return; if(to<0)to=0; if(to>entered.length)to=entered.length; const it=entered.splice(from,1)[0]; let t=(to>from)?to-1:to; entered.splice(t,0,it); if(t!==from) reorderReset(); renderAll(); }
  { const sh=$('slots'); if(sh){
    sh.addEventListener('pointerdown', e=>{ const s=e.target.closest('.slot.filled'); if(!s) return; const i=+s.dataset.idx; if(isNaN(i)) return; dragIdx=i; dragArmed=true; dragSX=e.clientX; dragSY=e.clientY; dragGhost=null; try{ sh.setPointerCapture(e.pointerId);}catch(_){} });
    sh.addEventListener('pointermove', e=>{ if(dragIdx<0) return; if(!dragGhost){ if(!dragArmed) return; if(Math.abs(e.clientX-dragSX)+Math.abs(e.clientY-dragSY)<5) return; const orig=sh.querySelector('.slot.filled[data-idx="'+dragIdx+'"]'); if(!orig){ dragIdx=-1; return; } const r=orig.getBoundingClientRect(); dragGhost=orig.cloneNode(true); dragGhost.classList.add('slot-ghost'); dragGhost.classList.remove('dragging','drop-before','drop-after','next'); dragGhost.removeAttribute('id'); dragGhost.style.width=r.width+'px'; dragGhost.style.height=r.height+'px'; dragGhost._dx=dragSX-r.left; dragGhost._dy=dragSY-r.top; document.body.appendChild(dragGhost); orig.classList.add('dragging'); } e.preventDefault(); dragGhost.style.left=(e.clientX-dragGhost._dx)+'px'; dragGhost.style.top=(e.clientY-dragGhost._dy)+'px'; setDropMarker(dropIndexAt(e.clientX)); });
    const finish=e=>{ if(dragIdx<0){ dragArmed=false; return; } const started=!!dragGhost; const from=dragIdx; let to=from; if(started){ to=dropIndexAt(e.clientX); dragGhost.remove(); dragGhost=null; } clearDropMarker(); const ds=sh.querySelector('.slot.dragging'); if(ds) ds.classList.remove('dragging'); dragIdx=-1; dragArmed=false; if(started) moveEntered(from,to); };
    sh.addEventListener('pointerup', finish);
    sh.addEventListener('pointercancel', ()=>{ if(dragGhost){ dragGhost.remove(); dragGhost=null; } clearDropMarker(); const ds=sh.querySelector('.slot.dragging'); if(ds) ds.classList.remove('dragging'); dragIdx=-1; dragArmed=false; });
    sh.addEventListener('keydown', e=>{ const s=e.target.closest('.slot.filled'); if(!s) return; const i=+s.dataset.idx; if(isNaN(i)) return; let to=null; if(e.key==='ArrowLeft'||e.key==='ArrowUp') to=i-1; else if(e.key==='ArrowRight'||e.key==='ArrowDown') to=i+1; else return; e.preventDefault(); if(to<0||to>=entered.length) return; const a=entered[i]; entered[i]=entered[to]; entered[to]=a; reorderReset(); renderAll(); const els=$('slots').querySelectorAll('.slot.filled'); if(els[to]) els[to].focus(); });
  } }
  { const sq=$('share-qr'); if(sq) sq.addEventListener('click', showQR); const qc=$('qr-close'); if(qc) qc.addEventListener('click', closeQR); const qcp=$('qr-copy'); if(qcp) qcp.addEventListener('click', ()=>{ syncHash(); copyBtn(qcp, location.href); }); const qm=$('qr-modal'); if(qm) qm.addEventListener('click', e=>{ if(e.target===qm) closeQR(); }); document.addEventListener('keydown', e=>{ if(e.key==='Escape'){ const m=$('qr-modal'); if(m && !m.hidden) closeQR(); } }); }
  { const fg=$('forms-grid'); if(fg){ const PAIR={'P':'I','I':'P','R':'RI','RI':'R'}; const openFam=(tag,open)=>{ formOpen[tag]=open; const h=fg.querySelector('.fam-head[data-fam="'+tag+'"]'); const box=h?h.closest('.fam'):null; if(box) box.classList.toggle('collapsed',!open); if(h) h.setAttribute('aria-expanded',open?'true':'false'); }; const tog=h=>{ const tag=h.getAttribute('data-fam'); if(!tag) return; const next=!formOpen[tag]; openFam(tag,next); const partner=PAIR[tag]; if(partner && window.matchMedia('(min-width:761px)').matches) openFam(partner,next); }; fg.addEventListener('click', e=>{ const h=e.target.closest('.fam-head'); if(h) tog(h); }); fg.addEventListener('keydown', e=>{ if(e.key==='Enter'||e.key===' '){ const h=e.target.closest('.fam-head'); if(h){ e.preventDefault(); tog(h); } } }); } }
  { const ro=$('rowinfo-open'); if(ro) ro.addEventListener('click', ()=>{ const ov=$('rowinfo-modal'); if(ov) ov.hidden=false; }); const rov=$('rowinfo-modal'); if(rov) rov.addEventListener('click', e=>{ if(e.target===rov) rov.hidden=true; }); document.addEventListener('keydown', e=>{ if(e.key==='Escape'){ const ov=$('rowinfo-modal'); if(ov && !ov.hidden) ov.hidden=true; } }); }
  { const mv=$('mxiv-modal'); const cm=()=>{ if(mv) mv.hidden=true; const t=$('mx-iv-toggle'); if(t) t.focus(); }; if(mv) mv.addEventListener('click', e=>{ if(e.target===mv) cm(); }); const xc=$('mxiv-close'); if(xc) xc.addEventListener('click', cm); document.addEventListener('keydown', e=>{ if(e.key==='Escape' && mv && !mv.hidden) cm(); }); }
  { const eo=$('export-open'); if(eo) eo.addEventListener('click', ()=>document.body.classList.add('exp-modal-open')); const _xc=()=>document.body.classList.remove('exp-modal-open'); const ex=$('export-close'); if(ex) ex.addEventListener('click', _xc); const bk=$('export-backdrop'); if(bk) bk.addEventListener('click', _xc); document.addEventListener('keydown', e=>{ if(e.key==='Escape' && document.body.classList.contains('exp-modal-open') && !document.querySelector('.modal-overlay:not([hidden])')) _xc(); }, true); }
  const EXAMPLES=[
    {name:'Schoenberg — Suite, Op. 25',                 prop:'first 12-tone work',                 pcs:[4,5,7,1,6,3,8,2,11,0,9,10]},
    {name:'Schoenberg — Wind Quintet, Op. 26',          prop:'first large-scale work',             pcs:[3,7,9,11,1,0,10,2,4,6,8,5]},
    {name:'Schoenberg — Variations, Op. 31',            prop:'orchestral variations',              pcs:[10,4,6,3,5,9,2,1,7,8,11,0]},
    {name:'Schoenberg — Piano Piece, Op. 33a',          prop:'combinatorial (chordal)',            pcs:[10,5,0,11,9,6,1,3,7,8,2,4]},
    {name:'Schoenberg — String Quartet No. 4, Op. 37',  prop:'hexachordally combinatorial',        pcs:[2,1,9,10,5,3,4,0,8,7,6,11]},
    {name:'Berg — Lyric Suite',                         prop:'all-interval',                       pcs:[5,4,0,9,7,2,8,1,3,6,10,11]},
    {name:'Berg — Violin Concerto',                     prop:'triadic (stacked thirds)',           pcs:[7,10,2,6,9,0,4,8,11,1,3,5]},
    {name:'Berg — Lulu',                                prop:'derived character row',              pcs:[5,7,8,10,0,2,6,3,4,9,11,1]},
    {name:'Webern — Symphony, Op. 21',                  prop:'RI-symmetric (palindrome)',          pcs:[9,6,7,8,4,5,11,10,2,1,0,3]},
    {name:'Webern — Concerto, Op. 24',                  prop:'derived · trichordal (014)',         pcs:[11,10,2,3,7,6,8,4,5,0,1,9]},
    {name:'Webern — String Quartet, Op. 28',            prop:'derived · tetrachordal (BACH)',      pcs:[10,9,0,11,3,4,1,2,6,5,8,7]},
    {name:'Babbitt — Three Compositions for Piano',     prop:'all-combinatorial hexachord',        pcs:[10,3,5,2,0,1,7,11,6,9,8,4]},
    {name:'Dallapiccola — Quaderno musicale',           prop:'lyrical serialism',                  pcs:[0,1,5,8,10,4,3,7,9,2,11,6]},
    {name:'Nono — Il canto sospeso',                    prop:'all-interval · wedge',               pcs:[0,11,1,10,2,9,3,8,4,7,5,6]},
    {name:'Boulez — Structures Ia',                     prop:'integral serialism (Messiaen mode)', pcs:[0,11,6,5,4,3,1,10,9,7,2,8]}
  ];
  function randomRowPcs(){ const a=[0,1,2,3,4,5,6,7,8,9,10,11]; for(let i=11;i>0;i--){const j=Math.floor(Math.random()*(i+1)); const t=a[i];a[i]=a[j];a[j]=t;} return a; }
  function randomNSet(N){ const a=[0,1,2,3,4,5,6,7,8,9,10,11]; for(let i=11;i>0;i--){const j=Math.floor(Math.random()*(i+1)); const t=a[i];a[i]=a[j];a[j]=t;} return a.slice(0,N); }
  const CUSTOM_EX={
    2:[{name:'Perfect 5th',pcs:[0,7]},{name:'Perfect 4th',pcs:[0,5]},{name:'Major 3rd',pcs:[0,4]},{name:'Minor 3rd',pcs:[0,3]},{name:'Major 2nd',pcs:[0,2]},{name:'Tritone',pcs:[0,6]}],
    3:[{name:'Major triad',pcs:[0,4,7]},{name:'Minor triad',pcs:[0,3,7]},{name:'Diminished triad',pcs:[0,3,6]},{name:'Augmented triad',pcs:[0,4,8]},{name:'Sus4 triad',pcs:[0,5,7]}],
    4:[{name:'Dominant 7th',pcs:[0,4,7,10]},{name:'Major 7th',pcs:[0,4,7,11]},{name:'Minor 7th',pcs:[0,3,7,10]},{name:'Half-diminished 7th',pcs:[0,3,6,10]},{name:'Fully diminished 7th',pcs:[0,3,6,9]},{name:'Minor-major 7th',pcs:[0,3,7,11]}],
    5:[{name:'Major pentatonic',pcs:[0,2,4,7,9]},{name:'Minor pentatonic',pcs:[0,3,5,7,10]}],
    6:[{name:'Whole-tone scale',pcs:[0,2,4,6,8,10]},{name:'Blues scale',pcs:[0,3,5,6,7,10]},{name:'Hexatonic (augmented)',pcs:[0,1,4,5,8,9]}],
    7:[{name:'Major (diatonic)',pcs:[0,2,4,5,7,9,11]},{name:'Natural minor',pcs:[0,2,3,5,7,8,10]},{name:'Harmonic minor',pcs:[0,2,3,5,7,8,11]},{name:'Melodic minor',pcs:[0,2,3,5,7,9,11]},{name:'Harmonic major',pcs:[0,2,4,5,7,8,11]}],
    8:[{name:'Octatonic (diminished)',pcs:[0,1,3,4,6,7,9,10]},{name:'Bebop dominant',pcs:[0,2,4,5,7,9,10,11]},{name:'Bebop major',pcs:[0,2,4,5,7,8,9,11]}],
    9:[{name:'Messiaen mode 3',pcs:[0,2,3,4,6,7,8,10,11]}],
    10:[],11:[]
  };
  function populateExCustom(){ const sel=$('ex-custom'); if(!sel) return; const list=CUSTOM_EX[customN]||[];
    sel.innerHTML='<option value="" selected disabled>Load example\u2026</option>'+(list.length?(function(){const seen=new Set(); return list.map((e,i)=>{const k=e.name+'|'+e.pcs.join(','); if(seen.has(k)) return ''; seen.add(k); return '<option value="'+i+'">'+e.name+'</option>';}).join('');})():'<option value="" disabled>\u2014 no common chord / scale \u2014</option>'); }
  // populate the twelve-tone example dropdown from EXAMPLES
  { const grp=$('ex-12-grp'); if(grp){ grp.innerHTML=''; const seen=new Set(); EXAMPLES.forEach((e,i)=>{ const key=e.name+'|'+e.pcs.join(','); if(seen.has(key)) return; seen.add(key); const o=document.createElement('option'); o.value=String(i); o.textContent=(e.prop?e.name+' · '+e.prop:e.name); grp.appendChild(o); }); } }
  { const ex12=$('ex-12'); if(ex12) ex12.addEventListener('change',()=>{
      const v=ex12.value; if(!v) return;
      let pcs,name;
      if(v==='random'){ pcs=randomRowPcs(); name='random row'; }
      else { const e=EXAMPLES[+v]; if(!e) return; pcs=e.pcs.slice(); name=e.name; }
      entered=pcs.map(pc=>({pc,name:null})); state=null; genResults=null; renderAll();
      exNote('loaded: '+name);
      ex12.value=''; // reset so the same item can be chosen again
    });
  }
  { const sx=$('strav-ex'); if(sx) sx.addEventListener('change',()=>{
      const key=sx.value; if(!key) return;
      const def = key==='random' ? {pcs:randomHexPcs(), note:'random hexachord'} : STRAV_EX[key];
      if(!def) return;
      entered=def.pcs.map(pc=>({pc,name:null})); state=null; genResults=null; renderAll();
      exNote('loaded: '+def.note);
      sx.value=''; // reset so the same item can be chosen again
    });
  }
  function randomLoad(){
    let pcs, note;
    if(mode==='stravinsky'){ const listed=new Set(['6-1','6-20','6-32','6-35']); let g=0; do{ pcs=randomHexPcs(); g++; }while(listed.has(forteName(pcs)||'') && g<200); note='random hexachord'; }
    else if(mode==='custom'){ const N=ROWLEN, exPF=new Set((CUSTOM_EX[N]||[]).map(e=>primeForm(e.pcs).join(','))); let g=0; do{ pcs=randomNSet(N); g++; }while(exPF.has(primeForm(pcs).join(',')) && g<400); note='random '+N+'-note set'; }
    else { const exRows=new Set(EXAMPLES.map(e=>e.pcs.join(','))); let g=0; do{ pcs=randomRowPcs(); g++; }while(exRows.has(pcs.join(',')) && g<50); note='random row'; }
    entered=pcs.map(pc=>({pc,name:null})); state=null; genResults=null; buildResults=null; renderAll();
    exNote('loaded: '+note);
  }
  { const rb=$('rand-row'); if(rb) rb.addEventListener('click',randomLoad); }
  { const lt=$('lede-toggle'); if(lt) lt.addEventListener('click',()=>{ const o=!document.body.classList.contains('lede-open'); document.body.classList.toggle('lede-open',o); lt.setAttribute('aria-expanded',String(o)); }); }
  { const exc=$('ex-custom'); if(exc) exc.addEventListener('change',()=>{ const v=exc.value; if(v==='') return; const e=(CUSTOM_EX[customN]||[])[+v]; if(!e){ exc.value=''; return; } entered=e.pcs.map(pc=>({pc,name:null})); state=null; genResults=null; buildResults=null; renderAll(); exNote('loaded: '+e.name); exc.value=''; }); }
  $('set').addEventListener('click',()=>{
    const res=parseRow($('rowinput').value, inputMode);
    if(res.error){ $('type-err').textContent=res.error; return; }
    $('type-err').textContent=''; entered=res.entries; state=null; genResults=null; const ex=$('ex-note'); if(ex) ex.textContent=''; renderAll();
  });
  $('rowinput').addEventListener('keydown',e=>{ if(e.key==='Enter') $('set').click(); });

  // ---------- toggles ----------
  function setSeg(group,val){
    if(group==='in'){
      inputMode=val;
      $('in-notes').setAttribute('aria-pressed',val==='notes');
      $('in-int').setAttribute('aria-pressed',val==='int');
      $('rowinput').placeholder = val==='notes'
        ? 'e.g.  C  E  G  (a chord)  …  or a full 12-tone row  —  integers ok:  0, 4, 7  (t = 10, e = 11)'
        : 'e.g.  0, 4, 7  (a subset)  …  or twelve integers  —  t = 10, e = 11;  note names ok';
      renderPalette(); updateDeriveZone(); renderGenResults(); renderBuild();
    } else if(group==='sp'){
      if($('sp-sharp').disabled) return;
      spelling=val;
      $('sp-sharp').setAttribute('aria-pressed',val==='sharp');
      $('sp-flat').setAttribute('aria-pressed',val==='flat');
      renderSlots(); renderStatus(); renderMatrix(); renderForms(); renderSubset(); renderStravinsky();
    } else {
      if($('dp-notes').disabled) return;
      dispMode=val;
      $('dp-notes').setAttribute('aria-pressed',val==='notes');
      $('dp-int').setAttribute('aria-pressed',val==='int');
      renderSlots(); renderStatus(); renderMatrix(); renderForms(); renderSubset(); renderStravinsky();
    }
  }
  $('in-notes').addEventListener('click',()=>setSeg('in','notes'));
  $('in-int').addEventListener('click',  ()=>setSeg('in','int'));
  $('sp-sharp').addEventListener('click',()=>setSeg('sp','sharp'));
  $('sp-flat').addEventListener('click', ()=>setSeg('sp','flat'));
  $('dp-notes').addEventListener('click',()=>setSeg('dp','notes'));
  $('dp-int').addEventListener('click',  ()=>setSeg('dp','int'));
  ['2','3','4','5','6'].forEach(k=>$('ss-'+k).addEventListener('click',()=>{subsetK=+k; renderSubset();}));
  { const ub=$('ss-uneven'); if(ub) ub.addEventListener('click',()=>{ renderSubset(); }); }
  ['T','I','R','RI'].forEach(fam=>$('op-'+fam).addEventListener('click',()=>{ genOps[fam]=!genOps[fam]; $('op-'+fam).setAttribute('aria-pressed',String(genOps[fam])); genResults=null; updateDeriveZone(); renderGenResults(); }));
  $('gen-run').addEventListener('click',runGen);

  // Block 4 — constrained generation
  const BK=[['bk-allint','allint'],['bk-allcomb','allcomb'],['bk-risym','risym'],['bk-derived','derived'],['bk-contains','contains']];
  BK.forEach(([id,mode])=>$(id).addEventListener('click',()=>{
    buildMode=mode; BK.forEach(([i,m])=>$(i).setAttribute('aria-pressed',String(m===mode)));
    buildResults=null; renderBuild();
  }));
  const SRC_IDS=['any','6-1','6-7','6-8','6-20','6-32','6-35'];
  SRC_IDS.forEach(sid=>$('src-'+sid).addEventListener('click',()=>{
    combSource=sid; SRC_IDS.forEach(s=>$('src-'+s).setAttribute('aria-pressed',String(s===sid)));
    buildResults=null; renderBuild();
  }));
  $('der-sc').addEventListener('change',()=>{ derClass=$('der-sc').value; buildResults=null; renderBuild(); });
  $('con-input').addEventListener('input',()=>{
    containsSpec=$('con-input').value; const sc=resolveSC(containsSpec), rd=$('con-read');
    if(rd){ if(!containsSpec.trim()){ rd.className='con-read'; rd.innerHTML=''; }
      else if(sc){ rd.className='con-read'; rd.innerHTML=`= <b>${sc.forte||'set class'}</b> (${sc.pf.map(pcTok).join('')}) \u00b7 ${sc.pf.length} notes`; }
      else { rd.className='con-read bad'; rd.textContent='not a valid set class'; } }
    buildResults=null; renderBuild();
  });
  populateDerSC();
  $('build-run').addEventListener('click',runBuild);
  { const pb=$('play-row'); if(pb) pb.addEventListener('click', ev=>{ ev.stopPropagation(); togglePlayRow(); }); }
  { const fg=$('forms-grid'); if(fg) fg.addEventListener('click', ev=>{ const ln=ev.target.closest('.fline'); if(ln && ln.dataset.pcs) playSeq(ln.dataset.pcs.split(',').map(Number)); }); }
  { const sb=$('strav-body'); if(sb) sb.addEventListener('click', ev=>{ const el=ev.target.closest('.strav-play'); if(el && el.dataset.pcs) playSeq(el.dataset.pcs.split(',').map(Number)); }); }
  // ----- Compare controls -----
  { const a=$('cmp-a'); if(a) a.addEventListener('change',()=>{ compareSel.a=a.value; renderCompare(); }); }
  { const b=$('cmp-b'); if(b) b.addEventListener('change',()=>{ compareSel.b=b.value; renderCompare(); }); }
  { const sw=$('cmp-swap'); if(sw) sw.addEventListener('click',()=>{ if(compareSel.bTyped) return; const t=compareSel.a; compareSel.a=compareSel.b; compareSel.b=t; renderCompare(); }); }
  { const bf=$('cmp-b-form'); if(bf) bf.addEventListener('click',()=>{ compareSel.bTyped=false; renderCompare(); }); }
  { const bt=$('cmp-b-type'); if(bt) bt.addEventListener('click',()=>{ compareSel.bTyped=true; renderCompare(); }); }
  { const bs=$('cmp-b-set'); if(bs) bs.addEventListener('click',()=>{ const r=parseRow($('cmp-b-input').value, inputMode); const er=$('cmp-b-err'); if(r.error){ if(er) er.textContent=r.error; return; } if(er) er.textContent=''; compareSel.typed=r.entries.map(e=>e.pc); compareSel.bTyped=true; renderCompare(); }); }
  { const bi=$('cmp-b-input'); if(bi) bi.addEventListener('keydown',e=>{ if(e.key==='Enter'){ e.preventDefault(); const s=$('cmp-b-set'); if(s) s.click(); } }); }
  { const cb=$('compare-body'); if(cb) cb.addEventListener('click', ev=>{ const b=ev.target.closest('.cmp-play'); if(b && b.dataset.pcs) playSeq(b.dataset.pcs.split(',').map(Number)); }); }


  const __initHash=location.hash||'';
  renderAll();

  // ----- mode gate: wiring + start at the gate -----
  $('mode-twelve').addEventListener('click',()=>enterMode('twelve'));
  $('mode-stravinsky').addEventListener('click',()=>enterMode('stravinsky'));
  $('mode-custom').addEventListener('click',()=>enterMode('custom'));
  $('mode-change').addEventListener('click',showGate);
  { const sl=$('share-link'); if(sl) sl.addEventListener('click',()=>{ syncHash(); copyBtn(sl, location.href); }); }
  { const rs=readHash(__initHash); if(rs) applyRestore(rs); else showGate(); }
})();
