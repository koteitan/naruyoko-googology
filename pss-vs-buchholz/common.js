function Scanner(s){
  if (s instanceof Scanner) return s.clone();
  if (typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof Scanner)) return new Scanner(s);
  this.s=s;
  this.pos=0;
  this.length=s.length;
  return this;
}
Scanner.prototype.clone=function (){
  return new Scanner(this.s);
}
Scanner.prototype.next=function (){
  if (this.pos>=this.length) return null;
  var c=this.s.charAt(this.pos);
  ++this.pos;
  return c;
}
Scanner.prototype.nextNumber=function (){
  var s=this.s.substring(this.pos);
  var m=s.match(/^[0-9]+/);
  if (m) {
    this.pos+=m[0].length;
    return Number(m[0]);
  }
  return null;
}
Scanner.prototype.peek=function (length,offset){
  if (typeof length=="undefined") length=1;
  if (typeof offset=="undefined") offset=0;
  if (this.pos+offset>this.length) return null;
  return this.s.substring(this.pos+offset,this.pos+offset+length);
}
Scanner.prototype.move=function (n){
  this.pos+=n;
}
Scanner.prototype.hasNext=function (){
  return this.pos<this.length;
}
Scanner.prototype.finished=function (){
  return this.pos>=this.length;
}
Object.defineProperty(Scanner.prototype,"constructor",{
  value:Scanner,
  enumerable:false,
  writable:true
});

var integerRegex=/^\d+$/;
var pairSequenceRegex=/^(?:(?:\(\d+,\d+\))+|\((?:\(\d+,\d+\)(?:,\(\d+,\d+\))*)?\))/;
var buchholzRegex=/^(?:[ \dwω,+⊕*×\(\)]|[Dp]_?\d|[WΩ](?:_?\d)?)+$/;

/**
 * @typedef {[number,number][]} PairSequence
 */

/**
 * @param {string} s
 * @returns {PairSequence}
 */
function parsePair(s){
  return Array.from(s.matchAll(/\((\d+),(\d+)\)/g),function(m){
    /** @type {[number,number]} */
    var r=[+m[1],+m[2]];
    return r;
  });
}
/**
 * @param {PairSequence} M
 * @param {boolean=} writeCommon
 * @returns {string}
 */
function stringifyPair(M,writeCommon){
  if (typeof writeCommon=="undefined") writeCommon=false;
  return (writeCommon?"":"(")+M.map(function(c){return "("+c[0]+","+c[1]+")";}).join(writeCommon?"":",")+(writeCommon?"":")");
}
/**
 * @param {PairSequence} M
 * @param {PairSequence} N
 * @returns {boolean}
 */
function equalPair(M,N){
  return M===N||M.length==N.length&&M.every(function(c,i){return c[0]==N[i][0]&&c[1]==N[i][1];});
}
/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @returns {number}
 */
function getPair(M,i,j){
  return M[j][i];
}
/**
 * @param {PairSequence} M
 * @param {PairSequence} N
 * @returns {boolean}
 */
function lessThanPair(M,N){
  if (M===N) return false;
  for (var j=0;j<Math.min(M.length,N.length);j++){
    if (getPair(M,0,j)<getPair(N,0,j)) return true;
    else if (getPair(M,0,j)>getPair(N,0,j)) return false;
    else if (getPair(M,1,j)<getPair(N,1,j)) return true;
    else if (getPair(M,1,j)>getPair(N,1,j)) return false;
  }
  return M.length<N.length;
}

/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @param {number=} k
 * @returns {number}
 */
function findParent(M,i,j,k){
  if (typeof k=="undefined") k=0;
  if (j<0||j>=M.length) return -1;
  if (i==0||i==1){
    for (var j0=j;(j0=i==0?j0-1:findParent(M,0,j0,k))>=k;){
      if (getPair(M,i,j0)<getPair(M,i,j)) return j0;
    }
    return -1;
  }else return -1;
}
/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @param {number} k
 * @returns {boolean}
 */
function isParent(M,i,j,k){
  return k>=0&&k<M.length&&k==findParent(M,i,j,k);
}
/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @param {number=} k
 * @returns {number[]}
 */
function findAncestors(M,i,j,k){
  if (typeof k=="undefined") k=0;
  if (j<k||j>=M.length) return [];
  /** @type {number[]} */
  var a=[j];
  var j0=j;
  while ((j0=findParent(M,i,j0))>=k) a.push(j0);
  return a;
}
/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @param {number} k
 * @returns {boolean}
 */
function isAncestor(M,i,j,k){
  if (k<0||k>=M.length) return false;
  var j0=j;
  do{
    if (k==j0) return true;
  }while ((j0=findParent(M,i,j0,k))!=-1);
  return false;
}
/**
 * @param {PairSequence} M
 * @returns {PairSequence}
 */
function Pred(M){
  return M.length==1?M:M.slice(0,-1);
}
/**
 * @param {PairSequence} M
 * @returns {PairSequence}
 */
function Derp(M){
  return M.slice(1);
}
/**
 * @param {PairSequence} M
 * @param {number} n
 * @returns {PairSequence}
 */
function fundPair(M,n){
  var j1=M.length-1;
  if (j1==0) return M;
  if (getPair(M,0,j1)==0&&getPair(M,1,j1)==0) return Pred(M);
  var i1=getPair(M,1,j1)>0?1:0;
  var j0=findParent(M,i1,j1);
  if (j0==-1) return Pred(M);
  var r=Pred(M);
  var d0=i1==1?getPair(M,0,j1)-getPair(M,0,j0):0;
  for (var k=1;k<n;k++){
    for (var j=j0;j<j1;j++){
      r.push([getPair(M,0,j)+k*d0,getPair(M,1,j)]);
    }
  }
  return r;
}
/**
 * @param {PairSequence} M
 * @param {number=} i
 * @returns {PairSequence}
 */
function IncrFirst(M,i){
  if (typeof i=="undefined") i=1;
  return M.map(function(c){return [c[0]+i,c[1]];});
}
/**
 * @param {PairSequence} M
 * @returns {boolean}
 */
function isZeroPair(M){
  return M.length==1&&getPair(M,1,0)==0;
}
/**
 * @param {PairSequence} M
 * @returns {boolean}
 */
function isPrincipalPair(M){
  return !isZeroPair(M)&&isAncestor(M,0,M.length-1,0);
}
/**
 * @param {PairSequence} M
 * @returns {PairSequence[]}
 */
function PPair(M){
  /** @type {PairSequence[]} */
  var r=[];
  var j1=M.length-1;
  while (j1>=0){
    var ans=findAncestors(M,0,j1);
    var j0=ans[ans.length-1];
    r.unshift(M.slice(j0,j1+1));
    j1=j0-1;
  }
  return r;
}
/**
 * @param {PairSequence} M
 * @param {number} j
 * @returns {boolean}
 */
function isUnadmitted(M,j){
  return j>M.length||isParent(M,1,j,j-1)&&isParent(M,1,j+1,j);
}
/**
 * @param {PairSequence} M
 * @param {number} j
 * @returns {boolean}
 */
function isAdmitted(M,j){
  return !isUnadmitted(M,j);
}
/**
 * @param {PairSequence} M
 * @returns {number[]}
 */
function findAdmitted(M){
  /** @type {number[]} */
  var r=[];
  for (var j0=0;j0<=M.length;j0++){
    if (isAdmitted(M,j0)) r.push(j0);
  }
  return r;
}
/**
 * @param {PairSequence} M
 * @param {number} j
 * @returns {number}
 */
function Adm(M,j){
  for (var j0=j;j0>=0;j0--){
    if (isAdmitted(M,j0)) return j0;
  }
  throw Error("Something went wrong");
}
/**
 * @param {PairSequence} M
 * @param {number} m
 * @returns {boolean}
 */
function isMarkedPair(M,m){
  return isAdmitted(M,m)&&isAncestor(M,0,M.length-1,m);
}
/**
 * @param {PairSequence} M
 * @param {number} m
 * @returns {boolean}
 */
function isMarkedReduced(M,m){
  return isReduced(M)&&isMarkedPair(M,m);
}
/**
 * @param {PairSequence[]} Q
 * @returns {number[]}
 */
function IdxSum(Q){
  /** @type {number[]} */
  var r=[0];
  var j=0;
  for (var J=0;J<Q.length;J++){
    r.push(j+=Q[J].length);
  }
  return r;
}
/**
 * @param {PairSequence} M
 * @returns {number}
 */
function TrMax(M){
  if (!isPrincipalPair(M)) throw Error("Invalid argument: Only defined over PT_PS; given "+stringifyPair(M));
  for (var j=0;j<M.length;j++){
    if (!isParent(M,1,j+1,j)) return j;
  }
  return M.length-1;
}
/**
 * @param {PairSequence} M
 * @returns {PairSequence[]}
 */
function Br(M){
  if (!isPrincipalPair(M)) throw Error("Invalid argument: Only defined over PT_PS; given "+stringifyPair(M));
  return PPair(M.slice(TrMax(M)+1));
}
/**
 * @param {PairSequence} M
 * @returns {number[]}
 */
function FirstNodes(M){
  if (!isPrincipalPair(M)) throw Error("Invalid argument: Only defined over PT_PS; given "+stringifyPair(M));
  var d=TrMax(M)+1;
  return IdxSum(Br(M)).map(function(e){return d+e;});
}
/**
 * @param {PairSequence} M
 * @returns {number[]}
 */
function Joints(M){
  if (!isPrincipalPair(M)) throw Error("Invalid argument: Only defined over PT_PS; given "+stringifyPair(M));
  return FirstNodes(M).slice(0,-1).map(function(e){return findParent(M,0,e);});
}
/**
 * @param {number} j0
 * @param {number} j1
 * @returns {PairSequence}
 */
function jjSeq(j0,j1){
  /** @type {PairSequence} */
  var r=[];
  for (var j=j0;j<=j1;j++) r.push([j,j]);
  return r;
}
/**
 * @param {PairSequence} M
 * @returns {PairSequence}
 */
function Red(M){
  if (isZeroPair(M)) return [[0,0]];
  else if (isPrincipalPair(M)){
    var j1=M.length-1;
    if (getPair(M,0,0)==0&&getPair(M,1,0)==0){
      var j1p=TrMax(M);
      if (j1p==j1) return jjSeq(0,j1);
      var br=Br(M);
      var fn=FirstNodes(M);
      var jn=Joints(M);
      var J1=br.length-1;
      var r=jjSeq(0,j1p);
      for (var J=0;J<=J1;J++){
        var nJ=getPair(br[J],1,0)==0?-1:findParent(M,1,fn[J]);
        /** @type {PairSequence} */
        var NJ=[[jn[J]+1,nJ+1]];
        NJ=NJ.concat(Derp(br[J]));
        r=r.concat(IncrFirst(Red(NJ),jn[J]-nJ));
      }
      return r;
    }else{
      var M10=getPair(M,1,0);
      if (M10==0) return Red(IncrFirst(M,-getPair(M,0,0)));
      else{
        var N=Red(jjSeq(0,M10-1).concat(IncrFirst(M,M10)));
        var j1=N.length-1;
        if (M10<=j1&&isPrincipalPair(N.slice(M10))) return IncrFirst(N.slice(M10),-getPair(N,0,M10)+getPair(N,1,M10));
        else return M;
      }
    }
  }else return PPair(M).flatMap(Red);
}
/**
 * @param {PairSequence} M
 * @returns {boolean}
 */
function isReduced(M){
  return equalPair(Red(M),M);
}
/**
 * @param {PairSequence} M
 * @param {number=} k
 * @returns {boolean}
 */
function isStandardPair(M,k){
  if (M.length<1) return false;
  if (typeof k=="undefined") k=Infinity;
  /** @type {PairSequence} */
  var N=[];
  var M00=getPair(M,0,0);
  for (var j=0;N.push([j+M00,j+M00]),lessThanPair(N,M);j++){
    if (getPair(M,0,j)>j+M00||getPair(M,0,j)<M00||getPair(M,1,j)>j+M00||getPair(M,1,j)<M00) return false;
  }
  if (equalPair(M,N)) return true;
  var k0=0;
  while (true){
    var N1=Pred(N);
    for (var n=1;N1.length<M.length&&(n==1||N1.length<M.length)&&lessThanPair(N1,M);N1=fundPair(N,n)) n++;
    for (var j=0;j<Math.min(M.length,N1.length)&&getPair(M,0,j)==getPair(N1,0,j)&&getPair(M,1,j)==getPair(N1,1,j);j++) continue;
    k0+=N1.length-j;
    if (k0>k) return false;
    if (j==M.length) return true;
    if (j<Math.min(M.length,N1.length)&&(getPair(M,0,j)>getPair(N1,0,j)||getPair(M,0,j)==getPair(N1,0,j)&&getPair(M,1,j)>getPair(N1,1,j))) return false;
    N=N1.slice(0,j+1);
  }
}
/**
 * @param {PairSequence[]} Q
 * @returns {boolean}
 */
function isDescending(Q){
  for (var J=0;J<Q.length-1;J++){
    if (lessThanPair(Q[J],Q[J+1])) return false;
  }
  return true;
}

/**
 * @typedef {{sub:number,inner:BuchholzTerm}} BuchholzPTerm
 * @typedef {0|BuchholzPTerm|BuchholzPTerm[]} BuchholzTerm
 */

/**
 * @param {string|Scanner} s
 * @param {number=} context
 * @returns {BuchholzTerm}
 */
function parseBuchholz(s,context){
  /** @param {BuchholzTerm} term */
  function appendToRSum(term){
    if (state==START||state==PLUS) r.push(term);
    else throw Error("Wrong state when attempting to append as sum");
    state=CLOSEDTERM;
  }
  var scanner;
  if (typeof s=="string") scanner=new Scanner(s);
  else if (s instanceof Scanner) scanner=s;
  else throw Error("Invalid expression: "+s);
  var nums="0123456789";
  var symbols=",_+⊕*×()";
  var notword=nums+symbols;
  var NUMBER=0;
  var SYMBOL=1;
  var WORD=2;
  var symbolTypes=["NUMBER","SYMBOL","WORD"];
  /** @type {BuchholzTerm[]} */
  var r=[];
  var startpos=scanner.pos;
  var TOP=0;
  var PRINCIPALTERMINNER=1;
  var PARENTHESIS=2;
  var contextNames=["TOP","PRINCIPALTERMINNER","PARENTHESIS"];
  if (typeof context=="undefined") context=TOP;
  var START=0;
  var PLUS=1;
  var CLOSEDTERM=2;
  var EXIT=3;
  var stateNames=["START","PLUS","CLOSEDTERM","EXIT"];
  var state=START;
  while (scanner.hasNext()&&state!=EXIT){
    var scanpos=scanner.pos;
    var next=scanner.next();
    var nextWord=next;
    var symbolType;
    if (nums.indexOf(nextWord)!=-1){
      while (scanner.hasNext()&&nums.indexOf(scanner.peek())!=-1){
        nextWord+=scanner.next();
      }
      symbolType=NUMBER;
    }else if (symbols.indexOf(nextWord)!=-1){
      symbolType=SYMBOL;
    }else{
      while (scanner.hasNext()&&notword.indexOf(scanner.peek())==-1){
        nextWord+=scanner.next();
      }
      symbolType=WORD;
    }
    if (symbolType==NUMBER){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var num=+nextWord;
      if (num==0) appendToRSum(BUCHHOLZ_ZERO);
      else if (num==1) appendToRSum(BUCHHOLZ_ONE);
      else appendToRSum(Array(num).fill(BUCHHOLZ_ONE));
    }else if (nextWord=="ω"||nextWord=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(BUCHHOLZ_SMALLOMEGA);
    }else if (nextWord=="Ω"||nextWord=="W"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var sub=1;
      var peek=scanner.peek();
      if (scanner.hasNext()&&(peek=="_"&&nums.indexOf(scanner.peek(1,1))!=-1||nums.indexOf(peek)!=-1)){
        if (peek=="_") scanner.move(1);
        sub=scanner.nextNumber();
      }
      if (sub<1) throw Error("Ω_"+sub+" is not a valid abbreviation at position "+scanpos+" in expression "+scanner.s);
      appendToRSum({sub:sub,inner:BUCHHOLZ_ZERO});
    }else if (nextWord=="D"||nextWord=="p"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var peek=scanner.peek();
      if (peek=="_") scanner.move(1);
      var sub=scanner.nextNumber();
      var peek=scanner.peek();
      if (peek==" ") scanner.move(1);
      var innerterm=parseBuchholz(scanner,PRINCIPALTERMINNER);
      appendToRSum({sub:sub,inner:innerterm});
    }else if (nextWord=="⊕"||nextWord=="+"||nextWord==","){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="×"||nextWord=="*"){
      if (state==CLOSEDTERM){
        state=PLUS;
        appendToRSum(timesBuchholz(normalizeBuchholz(r.pop()),scanner.nextNumber()));
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="("){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character ( at position "+scanpos+" in expression "+scanner.s);
      var subterm;
      if (scanner.peek()==")"){
        scanner.move(1);
        subterm=BUCHHOLZ_ZERO;
      }else{
        subterm=parseBuchholz(scanner,PARENTHESIS);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      }
      appendToRSum(subterm);
    }else{
      throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
    }
    if (state==CLOSEDTERM){
      var peek=scanner.peek();
      if (context==PARENTHESIS&&peek==")"){
        state=EXIT;
      }else if (context==PRINCIPALTERMINNER&&(peek==","||peek==")"||peek=="+"||peek=="⊕"||peek=="*"||peek=="×")){
        state=EXIT;
      }
    }
  }
  var rr=r.reduce(function(a,e){return plusBuchholz(a,e);},BUCHHOLZ_ZERO);
  /** @type {BuchholzTerm} */
  /* var rr=[];
  for (var i=0;i<r.length;i++){
    var term=r[i];
    if (term instanceof Array) rr=rr.concat(term);
    else if (term instanceof Object) rr.push(term);
  } */
  if (context==TOP){
    if (scanner.hasNext()) throw Error("Something went wrong");
    if (state==START){}
    else if (state==PLUS) throw Error("Unexpected end of input");
    else if (state==CLOSEDTERM){}
    rr=normalizeBuchholz(rr);
  }else{
    if (state==START){}
    else if (state==PLUS) throw Error("Something went wrong");
    else if (state==CLOSEDTERM){}
  }
  return rr;
}
/**
 * @param {BuchholzTerm} a
 * @returns {BuchholzTerm}
 */
function normalizeBuchholz(a){
  if (a instanceof Array){
    for (var i=0;i<a.length;i++){
      var newTerm=normalizeBuchholz(a[i]);
      if (newTerm==BUCHHOLZ_ZERO) a.splice(i,1),i--;
      // @ts-ignore
      else if (newTerm instanceof Array) Array.prototype.splice.apply(a,[i,1].concat(newTerm));
    }
    if (a.length==0) return BUCHHOLZ_ZERO;
    else if (a.length==1) return a[0];
  }else if (a instanceof Object) a.inner=normalizeBuchholz(a.inner);
  return a;
}
/**
 * @param {BuchholzTerm} a
 * @param {boolean=} writeCommon
 * @returns {string}
 */
function stringifyBuchholz(a,writeCommon){
  if (typeof writeCommon=="undefined") writeCommon=false;
  if (a instanceof Array){
    if (writeCommon){
      var r="";
      for (var i=0;i<a.length;){
        for (var j=i+1;j<a.length&&equalBuchholz(a[i],a[j]);j++) continue;
        if (r) r+="+";
        if (equalBuchholz(a[i],BUCHHOLZ_ONE)) r+=j-i;
        else if (j-i>1) r+=stringifyBuchholz(a[i],writeCommon)+"×"+(j-i);
        else r+=stringifyBuchholz(a[i],writeCommon);
        i=j;
      }
      return r;
    }else return "("+a.map(function(e){return stringifyBuchholz(e,writeCommon);}).join(",")+")";
  }else if (a instanceof Object){
    if (writeCommon){
      if (equalBuchholz(a.inner,BUCHHOLZ_ZERO)) return a.sub==0?"1":"Ω_"+a.sub;
      else if (equalBuchholz(a,BUCHHOLZ_SMALLOMEGA)) return "ω";
      else if (a.inner instanceof Array&&a.inner.every(function(e){return equalBuchholz(e,BUCHHOLZ_ONE);})) return "D_"+a.sub+" "+a.inner.length;
      else if (a.inner instanceof Array) return "D_"+a.sub+"("+stringifyBuchholz(a.inner,writeCommon)+")";
      else return "D_"+a.sub+" "+stringifyBuchholz(a.inner,writeCommon);
    }else return "D_"+a.sub+" "+stringifyBuchholz(a.inner,writeCommon);
  }else return "0";
}

/** @type {BuchholzTerm} */
var BUCHHOLZ_ZERO=0;
/** @type {BuchholzPTerm} */
var BUCHHOLZ_ONE={sub:0,inner:BUCHHOLZ_ZERO};
/** @type {BuchholzPTerm} */
var BUCHHOLZ_SMALLOMEGA={sub:0,inner:BUCHHOLZ_ONE};

/**
 * @param {BuchholzTerm} a
 * @param {BuchholzTerm} b
 * @returns {boolean}
 */
function equalBuchholz(a,b){
  if (a===b) return true;
  if (a instanceof Array) return b instanceof Array&&a.length==b.length&&a.every(function(e,i){return equalBuchholz(e,b[i]);});
  else if (a instanceof Object) return !(b instanceof Array)&&b instanceof Object&&a.sub==b.sub&&equalBuchholz(a.inner,b.inner);
  else return false;
}
/**
 * @param {BuchholzTerm} a
 * @param {BuchholzTerm} b
 * @returns {boolean}
 */
function lessThanBuchholz(a,b){
  if (a===b) return false;
  if (a instanceof Array){
    if (b instanceof Array){
      for (var i=0;i<Math.min(a.length,b.length);i++){
        if (lessThanBuchholz(a[i],b[i])) return true;
        else if (lessThanBuchholz(b[i],a[i])) return false;
      }
      return a.length<b.length;
    }else if (b instanceof Object) return lessThanBuchholz(a[0],b);
    else return false;
  }else if (a instanceof Object){
    if (b instanceof Array) return !lessThanBuchholz(b[0],a);
    else if (b instanceof Object) return a.sub<b.sub||a.sub==b.sub&&lessThanBuchholz(a.inner,b.inner);
    else return false;
  }else return true;
}
/**
 * @param {BuchholzTerm} a
 * @returns {boolean}
 */
function isZeroBuchholz(a){
  return a==BUCHHOLZ_ZERO;
}
/**
 * @param {BuchholzTerm} a
 * @returns {boolean}
 */
function isPrincipalBuchholz(a){
  return !(a instanceof Array)&&a instanceof Object;
}
/**
 * @param {BuchholzTerm} a
 * @param {BuchholzTerm} b
 * @returns {BuchholzTerm}
 */
function plusBuchholz(a,b){
  if (a instanceof Array){
    if (b instanceof Array) return a.concat(b);
    else if (b instanceof Object) return a.concat([b]);
    else return a;
  }else if (a instanceof Object){
    if (b instanceof Array) return [a].concat(b);
    else if (b instanceof Object) return [a,b];
    else return a;
  }else return b;
}
/**
 * @param {BuchholzTerm} a
 * @param {number} n
 * @returns {BuchholzTerm}
 */
function timesBuchholz(a,n){
  var r=BUCHHOLZ_ZERO;
  for (var i=0;i<n;i++) r=plusBuchholz(r,a);
  return r;
}
/**
 * @param {BuchholzTerm} a
 * @param {number} u
 * @returns {BuchholzTerm[]}
 */
function G(a,u){
  if (a instanceof Array) return a.flatMap(function(e){return G(e,u);});
  else if (a instanceof Object) return u<=a.sub?[a.inner].concat(G(a.inner,u)):[];
  else return [];
}
/**
 * @param {BuchholzTerm} a
 * @returns {boolean}
 */
function isStandardBuchholz(a){
  if (a instanceof Array) return a.every(function(e,i){return !equalBuchholz(e,BUCHHOLZ_ZERO)&&isStandardBuchholz(e)&&(i==0||!lessThanBuchholz(a[i-1],e));});
  else if (a instanceof Object) return isStandardBuchholz(a.inner)&&G(a.inner,a.sub).every(function(e){return lessThanBuchholz(e,a.inner);});
  else return true;
}
/**
 * @param {BuchholzTerm|number} a
 * @returns {BuchholzTerm}
 */
function fromNumBuchholz(a){
  return a instanceof Object?a:a==0?BUCHHOLZ_ZERO:a==1?BUCHHOLZ_ONE:Array(a).fill(BUCHHOLZ_ONE);
}
/**
 * @param {BuchholzTerm|number} a
 * @returns {number}
 */
function toNumBuchholz(a){
  return a instanceof Array?a.length:a instanceof Object?1:a;
}
/**
 * @param {BuchholzTerm} a
 * @returns {BuchholzTerm}
 */
function domBuchholz(a){
  if (a instanceof Array) return domBuchholz(a[a.length-1]);
  else if (a instanceof Object){
    if (a.inner instanceof Object){
      var di=domBuchholz(a.inner);
      if (di instanceof Array||!(di instanceof Object)) throw Error("Unexpected error");
      if (equalBuchholz(di,BUCHHOLZ_ONE)) return BUCHHOLZ_SMALLOMEGA;
      else if (equalBuchholz(di,BUCHHOLZ_SMALLOMEGA)||di.sub<=a.sub) return di;
      else return BUCHHOLZ_SMALLOMEGA;
    }else return a;
  }else return a;
}
/**
 * @param {BuchholzTerm} a
 * @param {BuchholzTerm|number} z
 * @returns {BuchholzTerm}
 */
function fundBuchholz(a,z){
  if (a instanceof Array) return plusBuchholz(a.length==2?a[0]:a.slice(0,-1),fundBuchholz(a[a.length-1],z));
  else if (a instanceof Object){
    if (a.inner instanceof Object){
      var di=domBuchholz(a.inner);
      if (di instanceof Array||!(di instanceof Object)) throw Error("Unexpected error");
      if (equalBuchholz(di,BUCHHOLZ_ONE)) return timesBuchholz({sub:a.sub,inner:fundBuchholz(a.inner,0)},toNumBuchholz(z));
      else if (equalBuchholz(di,BUCHHOLZ_SMALLOMEGA)||di.sub<=a.sub) return {sub:a.sub,inner:fundBuchholz(a.inner,z)};
      else{
        var x=di.sub==1?BUCHHOLZ_SMALLOMEGA:{sub:di.sub-1,inner:BUCHHOLZ_ZERO};
        var n=toNumBuchholz(z);
        for (var i=0;i<n;i++) x={sub:di.sub-1,inner:fundBuchholz(a.inner,x)};
        return x;
      }
    }else return BUCHHOLZ_ZERO;
  }else throw Error("Undefined: 0[z]");
}
/**
 * @param {BuchholzTerm} t
 * @returns {BuchholzPTerm[]}
 */
function PBuchholz(t){
  if (t instanceof Array) return t;
  else if (t instanceof Object) return [t];
  else return [];
}
/**
 * @param {BuchholzTerm} t
 * @returns {number[]}
 */
function RightNodes(t){
  if (t instanceof Array) return RightNodes(t[t.length-1]);
  else if (t instanceof Object) return [t.sub].concat(RightNodes(t.inner));
  else return [];
}
/**
 * @param {BuchholzTerm} t
 * @param {string} s
 * @param {string|BuchholzTerm} c
 * @param {string} b
 * @returns {boolean}
 */
function isSCBDecomposition(t,s,c,b){
  if (!/^\)*$/.test(b)) return false;
  try{
    if (typeof c=="string") c=parseBuchholz(c);
  }catch(e){
    return false;
  }
  return isPrincipalBuchholz(c)&&stringifyBuchholz(t)==s+stringifyBuchholz(c)+b;
}
/**
 * @param {number[]} rn
 * @returns {boolean}
 */
function isType0SCBDecomposition_aux(rn){
  return rn.length==2&&rn[1]==0;
}
/**
 * @param {BuchholzTerm} c
 * @returns {boolean}
 */
function isType0SCBDecomposition_aux2(c){
  return isType0SCBDecomposition_aux(RightNodes(c));
}
/**
 * @param {BuchholzTerm} t
 * @param {string} s
 * @param {string|BuchholzTerm} c
 * @param {string} b
 * @returns {boolean}
 */
function isType0SCBDecomposition(t,s,c,b){
  try{
    if (typeof c=="string") c=parseBuchholz(c);
  }catch(e){
    return false;
  }
  return isSCBDecomposition(t,s,c,b)&&isType0SCBDecomposition_aux2(c);
}
/**
 * @param {number[]} rn
 * @returns {boolean}
 */
function isType1SCBDecomposition_aux(rn){
  var j1=rn.length-1;
  if (rn[0]>=rn[j1]) return false;
  for (var j=1;j<j1;j++){
    if (rn[j]<rn[j1]) return false;
  }
  return true;
}
/**
 * @param {BuchholzTerm} c
 * @returns {boolean}
 */
function isType1SCBDecomposition_aux2(c){
  return isType1SCBDecomposition_aux(RightNodes(c));
}
/**
 * @param {BuchholzTerm} t
 * @param {string} s
 * @param {string|BuchholzTerm} c
 * @param {string} b
 * @returns {boolean}
 */
function isType1SCBDecomposition(t,s,c,b){
  try{
    if (typeof c=="string") c=parseBuchholz(c);
  }catch(e){
    return false;
  }
  return isSCBDecomposition(t,s,c,b)&&isType1SCBDecomposition_aux2(c);
}
/**
 * @param {BuchholzTerm} t
 * @param {string|BuchholzTerm} c
 * @returns {[string,string]?}
 */
function SCBDecomposition(t,c){
  try{
    if (typeof c=="string") c=parseBuchholz(c);
  }catch(e){
    return null;
  }
  var tt=stringifyBuchholz(t);
  var cc=stringifyBuchholz(c);
  for (var i=tt.length;i>=0&&(i==tt.length||tt[i]==")");i--){
    if (tt.substring(i-cc.length,i)==cc) return [tt.substring(0,i-cc.length),tt.substring(i)];
  }
  return null;
}
/**
 * @param {BuchholzTerm} t
 * @param {string|BuchholzTerm} c
 * @param {string|BuchholzTerm} cc
 * @returns {BuchholzTerm?}
 */
function replaceSCBDecompositionMark(t,c,cc){
  try{
    if (typeof c=="string") c=parseBuchholz(c);
    if (typeof cc=="string") cc=parseBuchholz(cc);
  }catch(e){
    return null;
  }
  if (t instanceof Array){
    var tt=replaceSCBDecompositionMark(t[t.length-1],c,cc);
    // @ts-ignore
    return tt?t.slice(0,-1).concat([tt]):null;
  }else if (t instanceof Object){
    if (equalBuchholz(t,c)) return cc;
    var tt=replaceSCBDecompositionMark(t.inner,c,cc);
    return tt?{sub:t.sub,inner:tt}:null;
  }else return null;
}
/**
 * @param {BuchholzTerm} t
 * @returns {BuchholzTerm?}
 */
function nextMarkedBuchholz(t){
  if (t instanceof Array) return t[t.length-1];
  else if (t instanceof Object) return t.inner;
  else return null;
}
/**
 * @param {BuchholzTerm?} t
 * @param {BuchholzTerm} c
 * @returns {boolean}
 */
function isMarkedBuchholz(t,c){
  while (t!==null){
    if (equalBuchholz(t,c)) return true;
    t=nextMarkedBuchholz(t);
  }
  return false;
}
/**
 * @param {BuchholzTerm} c
 * @returns {-1|0|1}
 */
function isTypeNSCBDecompositionMark(c){
  var rn=RightNodes(c);
  if (isType0SCBDecomposition_aux(rn)) return 0;
  if (isType1SCBDecomposition_aux(rn)) return 1;
  return -1;
}
/**
 * @param {BuchholzTerm?} t
 * @returns {[0|1,BuchholzTerm]?}
 */
function typeNSCBDecompositionMark(t){
  while (t!==null){
    var type=isTypeNSCBDecompositionMark(t);
    if (type!=-1) return [type,t];
    t=nextMarkedBuchholz(t);
  }
  return null;
}
/**
 * @param {BuchholzTerm} t
 * @returns {-1|0|1}
 */
function isTypeNSCBDecomposable(t){
  var r=typeNSCBDecompositionMark(t);
  return r?r[0]:-1;
}
/**
 * @param {BuchholzTerm} t
 * @returns {boolean}
 */
function isType0SCBDecomposable(t){
  return isTypeNSCBDecomposable(t)==0;
}
/**
 * @param {BuchholzTerm} t
 * @returns {boolean}
 */
function isType1SCBDecomposable(t){
  return isTypeNSCBDecomposable(t)==1;
}
/**
 * @param {BuchholzTerm} t
 * @returns {[0|1,string,BuchholzTerm,string]?}
 */
function typeNSCBDecomposition(t){
  var r1=typeNSCBDecompositionMark(t);
  var r2=r1&&SCBDecomposition(t,r1[1]);
  return r2?[r1[0],r2[0],r1[1],r2[1]]:null;
}
/** @type {[Map<string,-3|-2|-1|0|1|2|3|4|5|6>,Map<string,BuchholzTerm>,Map<string,BuchholzTerm>]} */
var TransMemos=[new Map(),new Map(),new Map()];
function clearTransMemos(){
  return TransMemos.forEach(function(e){e.clear();});
}
/**
 * @param {PairSequence} M
 * @returns {-3|-2|-1|0|1|2|3|4|5|6}
 */
function TransType_internal(M){
  var j1=M.length-1;
  if (isReduced(M)){
    if (j1==0) return -1;
    else if (isPrincipalPair(M)){
      var t1=Trans(Pred(M));
      if (equalBuchholz(t1,BUCHHOLZ_ZERO)) return 0;
      else{
        var j0=findParent(M,0,j1);
        return getPair(M,1,j1)==0?isAdmitted(M,j0)?1:2:getPair(M,1,j0)>=getPair(M,1,j1)?isAdmitted(M,j0)?3:4:j0+1<j1?5:6;
      }
    }else return -2;
  }else return -3;
}
/**
 * @param {PairSequence} M
 * @returns {-3|-2|-1|0|1|2|3|4|5|6}
 */
function TransType(M){
  var id=stringifyPair(M);
  if (TransMemos[0].has(id)) return TransMemos[0].get(id);
  else{
    var r=TransType_internal(M);
    TransMemos[0].set(id,r);
    return r;
  }
}
/**
 * @param {PairSequence} M
 * @returns {BuchholzTerm}
 */
function Trans_internal(M){
  var j1=M.length-1;
  var type=TransType(M);
  if (type==-3) return Trans(Red(M));
  else if (type==-2) return PPair(M).reduce(function(a,e,i){return i==0?Trans(e):plusBuchholz(a,equalPair(e,[[0,0]])?BUCHHOLZ_ONE:Trans(e));},BUCHHOLZ_ZERO);
  else if (type==-1) return getPair(M,0,0)==0&&getPair(M,1,0)==0?BUCHHOLZ_ZERO:{sub:getPair(M,1,0),inner:BUCHHOLZ_ZERO};
  else if (type==0) return {sub:0,inner:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO}};
  else{
    var t1=Trans(Pred(M));
    var j0=findParent(M,0,j1);
    var jn1=Adm(M,j0);
    var c1=Mark(Pred(M),jn1);
    if (c1 instanceof Array||!(c1 instanceof Object)) throw Error("Unexpected error");
    var v=c1.sub;
    var t2=c1.inner;
    var Pt2=PBuchholz(t2);
    var J1=Pt2.length-1;
    var c2;
    if (type==1||type==3||type==5) c2={sub:v,inner:plusBuchholz(t2,{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO})};
    else if (type==2||type==4){
      if (equalBuchholz(t2,BUCHHOLZ_ZERO)) c2={sub:v,inner:{sub:getPair(M,1,j0),inner:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO}}};
      else{
        var t3,t4;
        if (Pt2[J1].sub==getPair(M,1,j0)){
          t3=J1==1?Pt2[0]:Pt2.slice(0,-1);
          t4=Pt2[J1].inner;
        }else t3=t4=t2;
        c2={sub:v,inner:plusBuchholz(t3,{sub:getPair(M,1,j0),inner:plusBuchholz(t4,{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO})})};
      }
    }else c2={sub:v,inner:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO}};
    return replaceSCBDecompositionMark(t1,c1,c2);
  }
}
/**
 * @param {PairSequence} M
 * @returns {BuchholzTerm}
 */
function Trans(M){
  var id=stringifyPair(M);
  if (TransMemos[1].has(id)) return TransMemos[1].get(id);
  else{
    var r=Trans_internal(M);
    TransMemos[1].set(id,r);
    return r;
  }
}
/**
 * @param {PairSequence} M
 * @param {number} m
 * @returns {BuchholzTerm}
 */
function Mark_internal(M,m){
  var j1=M.length-1;
  var type=TransType(M);
  if (type==-3) return Mark(Red(M),m);
  else if (type==-2){
    var PM=PPair(M);
    var J1=PM.length-1;
    var j0=j1-PM[J1].length+1;
    return equalPair(PM[J1],[[0,0]])?BUCHHOLZ_ONE:Mark(PM[J1],m-j0);
  }else if (type==-1) return getPair(M,0,0)==0&&getPair(M,1,0)==0?BUCHHOLZ_ZERO:{sub:getPair(M,1,0),inner:BUCHHOLZ_ZERO};
  else if (type==0) return m==0?{sub:0,inner:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO}}:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO};
  else{
    var j0=findParent(M,0,j1);
    var jn1=Adm(M,j0);
    var c1=Mark(Pred(M),jn1);
    if (c1 instanceof Array||!(c1 instanceof Object)) throw Error("Unexpected error");
    var v=c1.sub;
    var t2=c1.inner;
    var Pt2=PBuchholz(t2);
    var J1=Pt2.length-1;
    var c2;
    if (type==1||type==3||type==5) c2={sub:v,inner:plusBuchholz(t2,{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO})};
    else if (type==2||type==4){
      if (equalBuchholz(t2,BUCHHOLZ_ZERO)) c2={sub:v,inner:{sub:getPair(M,1,j0),inner:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO}}};
      else{
        var t3,t4;
        if (Pt2[J1].sub==getPair(M,1,j0)){
          t3=J1==1?Pt2[0]:Pt2.slice(0,-1);
          t4=Pt2[J1].inner;
        }else t3=t4=t2;
        c2={sub:v,inner:plusBuchholz(t3,{sub:getPair(M,1,j0),inner:plusBuchholz(t4,{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO})})};
      }
    }else c2={sub:v,inner:{sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO}};
    if (m<j1){
      var c0=Mark(Pred(M),m);
      if (isMarkedBuchholz(c0,c1)) return replaceSCBDecompositionMark(c0,c1,c2);
      else return {sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO};
    }else return {sub:getPair(M,1,j1),inner:BUCHHOLZ_ZERO};
  }
}
/**
 * @param {PairSequence} M
 * @param {number} m
 * @returns {BuchholzTerm}
 */
function Mark(M,m){
  var id=stringifyPair(M)+m;
  if (TransMemos[2].has(id)) return TransMemos[2].get(id);
  else{
    var r=Mark_internal(M,m);
    TransMemos[2].set(id,r);
    return r;
  }
}
/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @param {number=} k
 * @returns {number}
 */
function findNextAdm(M,i,j,k){
  if (typeof k=="undefined") k=0;
  var j0=j;
  while ((j0=findParent(M,i,j0,k))!=-1){
    if (isAdmitted(M,j0)) return j0;
  }
  return -1;
}
/**
 * @param {PairSequence} M
 * @param {number} i
 * @param {number} j
 * @param {number} k
 * @returns {boolean}
 */
function isNextAdm(M,i,j,k){
  return k>=0&&k<M.length&&k==findNextAdm(M,i,j,k);
}
/**
 * @param {PairSequence} M
 * @returns {number[]}
 */
function RightAnces(M){
  var j1=M.length-1;
  var type=TransType(M);
  if (type==-3) return RightAnces(Red(M));
  else if (type==-2){
    var PM=PPair(M);
    var J1=PM.length-1;
    return equalPair(PM[J1],[[0,0]])?[0]:RightAnces(PM[J1]);
  }else if (type==-1) return getPair(M,0,0)==0&&getPair(M,1,0)==0?[]:[getPair(M,1,0)];
  else if (type==0) return [0,getPair(M,1,j1)];
  else{
    var j0=findParent(M,0,j1);
    var jn1=Adm(M,j0);
    var a=isZeroPair(M.slice(0,jn1))?[0]:RightAnces(M.slice(0,jn1));
    if (type==1||type==3||type==5||type==6) return a.concat([getPair(M,1,j1)]);
    else return a.concat([getPair(M,1,j0),getPair(M,1,j1)])
  }
}
/**
 * @param {PairSequence} M
 * @returns {boolean}
 */
function isStronglyPrincipal(M){
  return isPrincipalPair(M)&&isDescending(Br(M))&&isReduced(M);
}
/**
 * @param {PairSequence} M
 * @returns {number}
 */
function LastStep(M){
  if (!isStronglyPrincipal(M)) throw Error("Invalid argument: Only defined over DT_PS; given "+stringifyPair(M));
  var br=Br(M);
  var J1=br.length-1;
  if (J1==0) return 0;
  else{
    if (getPair(br[J1],0,0)==getPair(br[J1],1,0)) return J1;
    else{
      for (var J=0;J<J1;J++){
        if (getPair(br[J1],0,0)==getPair(br[J],0,0)&&getPair(br[J],0,0)>getPair(br[J],1,0)) return J;
      }
      return J1;
    }
  }
}
/**
 * @param {BuchholzTerm} t
 * @returns {PairSequence}
 */
function TransRev(t){
  if (!lessThanBuchholz(t,{sub:1,inner:BUCHHOLZ_ZERO})||!isStandardBuchholz(t)) throw Error("Invalid argument: Only defined over {t|t∈OT_B∧t<D_0 D_ω 0}; given "+stringifyBuchholz(t));
  var o=0;
  var a;
  if (t instanceof Array) o=1,a=t[0].inner;
  else if (t instanceof Object) a=t.inner;
  else return [[0,0]];
  if (a instanceof Array) o=1,a=a[0];
  if (!a||a.sub==0||!equalBuchholz(a.inner,BUCHHOLZ_ZERO)) o=1;
  var N=jjSeq(0,a?a.sub+o:o);
  if (!o) return N;
  var k=stringifyBuchholz(t).length+5; //Very conservative estimate for maximum number of takes on a fundamental sequence
  while (true){
    var N1=Pred(N);
    var t1;
    for (var n=1;n<k&&lessThanBuchholz(t1=Trans(N1),t);N1=fundPair(N,n)) n++;
    if (n==k) throw Error("Failed finding fundamental sequence; target="+stringifyBuchholz(t)+", matrix="+stringifyPair(N)+", Trans(matrix)="+stringifyBuchholz(Trans(N)));
    if (equalBuchholz(t1,t)) return N1;
    N=N1;
  }
}