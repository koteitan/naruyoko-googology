var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ]/g;
window.onload=function (){
  console.clear();
  setupTestTerms();
  document.getElementById('input').onkeydown=handlekey;
  document.getElementById('input').onfocus=handlekey;
  document.getElementById('input').onmousedown=handlekey;
}

function normalizeAbbreviations(s){
  return (s instanceof Term?s:new Term(s+""))+"";
}
function abbreviate(s,abbreviate){
  return (s instanceof Term?s:new Term(s+"")).toString(typeof abbreviate=="object"?abbreviate:true);
}

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

/**
 * @constructor
 * @param {*} s
 * @returns {Term}
 */
function Term(s){
  if (s instanceof Term) return s.clone();
  else if (typeof s!="undefined"&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof Term)) return new Term(s);
  if (s) return Term.build(s);
  else return this;
}
/**
 * @param {Term|string|Scanner} s
 * @param {number=} context
 * @returns {Term}
 */
Term.build=function (s,context){
  if (s instanceof Term) return s.clone();
  function appendToRSum(term){
    if (state==START) r=term;
    else if (state==PLUS) r=SumTerm.buildNoClone([r,term]);
    else throw Error("Wrong state when attempting to append as sum");
    state=CLOSEDTERM;
  }
  var scanner;
  if (typeof s=="string") scanner=new Scanner(s);
  else if (s instanceof Scanner) scanner=s;
  else throw Error("Invalid expression: "+s);
  var nums="0123456789";
  var symbols="+(){}_,";
  var notword=nums+symbols;
  var NUMBER=0;
  var SYMBOL=1;
  var WORD=2;
  var symbolTypes=["NUMBER","SYMBOL","WORD"];
  /** @type {Term} */
  var r=null;
  var startpos=scanner.pos;
  var TOP=0;
  var PSITERMSUBSCRIPT=1;
  var PSITERMINNER=2;
  var BRACES=3;
  var contextNames=["TOP","PSITERMSUBSCRIPT","PSITERMINNER","BRACES"];
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
      if (num==0){
        appendToRSum(ZeroTerm.build());
      }else if (num==1){
        appendToRSum(Term.ONE.clone());
      }else{
        var decomposed=[];
        for (var i=0;i<num;i++){
          decomposed.push(Term.ONE.clone());
        }
        appendToRSum(SumTerm.buildNoClone(decomposed));
        state=CLOSEDTERM;
      }
    }else if (nextWord=="ω"||nextWord=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.SMALLOMEGA.clone());
    }else if (nextWord=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="{"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character { at position "+scanpos+" in expression "+scanner.s);
      var subterm=Term.build(scanner,BRACES);
      var nextnext=scanner.next();
      if (nextnext!="}") throw Error("Expected closing } at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      appendToRSum(subterm);
    }else if (nextWord=="ψ"||nextWord=="p"||nextWord=="psi"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var subterms=[];
      var nextnext=scanner.next();
      if (nextnext!="_"&&nextnext!="(") throw Error("Expected _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      if (nextnext=="_"){
        subterms.push(Term.build(scanner,PSITERMSUBSCRIPT));
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      }
      while (subterms.length<2){
        subterms.push(Term.build(scanner,PSITERMINNER));
        var nextnext=scanner.next();
        if (nextnext==","){
          if (subterms.length>=2) throw Error("Too many terms in ψ term at position "+scanpos+" in expression "+scanner.s);
        }else if (nextnext==")") break;
        else throw Error("Expected a comma or closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      }
      while (subterms.length<2) subterms.unshift(ZeroTerm.build());
      appendToRSum(PsiTerm.buildNoClone.apply(null,subterms));
    }else{
      throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
    }
    if (state==CLOSEDTERM){
      var peek=scanner.peek();
      if (context==BRACES&&peek=="}"){
        state=EXIT;
      }else if (context==PSITERMSUBSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==PSITERMINNER&&(peek==","||peek==")")){
        state=EXIT;
      }
    }
  }
  if (context==TOP){
    if (scanner.hasNext()) throw Error("Something went wrong");
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Unexpected end of input");
    else if (state==CLOSEDTERM){}
  }else{
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Something went wrong");
    else if (state==CLOSEDTERM){}
  }
  return r;
}
/** @returns {Term} */
Term.buildNoClone=function (){
  throw Error("Not implemented");
}
/** @returns {Term} */
Term.prototype.clone=function (){
  throw Error("Cloning undefined for this term type.");
}
/** @returns {string} */
Term.prototype.toString=function (abbreviate){
  throw Error("Stringification undefined for this term type.");
}
/**
 * @param {boolean} abbreviate
 * @returns {string}
 */
Term.prototype.toStringWithImplicitBrace=function (abbreviate){
  return this.toString(abbreviate);
}
/** @returns {boolean} */
Term.prototype.equal=function (other){
  throw Error("Equality undefined for this term type.");
}
Object.defineProperty(Term.prototype,"constructor",{
  value:Term,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s
 * @returns {NullTerm}
 */
function NullTerm(s){
  if (s instanceof NullTerm) return s.clone();
  else if (typeof s!="undefined"&&s!==null) throw Error("Invalid expression: "+s);
  if (!(this instanceof NullTerm)) return new NullTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof NullTerm)) throw Error("Invalid expression: "+s);
}
Object.assign(NullTerm,Term);
NullTerm.build=function (){
  var r=new NullTerm();
  return r;
}
NullTerm.buildNoClone=function (){
  var r=new NullTerm();
  return r;
}
NullTerm.prototype=Object.create(Term.prototype);
NullTerm.prototype.clone=function (){
  return NullTerm.build();
}
NullTerm.prototype.toString=function (abbreviate){
  return "";
}
NullTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof NullTerm;
}
Object.defineProperty(NullTerm.prototype,"constructor",{
  value:NullTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s
 * @returns {ZeroTerm}
 */
function ZeroTerm(s){
  if (s instanceof ZeroTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ZeroTerm)) return new ZeroTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof ZeroTerm)) throw Error("Invalid expression: "+s);
}
Object.assign(ZeroTerm,Term);
ZeroTerm.build=function (){
  var r=new ZeroTerm();
  return r;
}
ZeroTerm.buildNoClone=function (){
  var r=new ZeroTerm();
  return r;
}
ZeroTerm.prototype=Object.create(Term.prototype);
ZeroTerm.prototype.clone=function (){
  return ZeroTerm.build();
}
ZeroTerm.prototype.toString=function (abbreviate){
  return "0";
}
ZeroTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof ZeroTerm;
}
Object.defineProperty(ZeroTerm.prototype,"constructor",{
  value:ZeroTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s
 * @returns {PsiTerm}
 */
function PsiTerm(s){
  if (s instanceof PsiTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof PsiTerm)) return new PsiTerm(s);
  /** @type {PsiTerm} */
  Term.call(this,s);
  if (s&&!(this instanceof PsiTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term} */
  this.sub=null;
  /** @type {Term} */
  this.inner=null;
}
Object.assign(PsiTerm,Term);
PsiTerm.build=function (sub,inner){
  var r=new PsiTerm();
  r.sub=new Term(sub);
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} sub
 * @param {Term} inner
 * @returns {PsiTerm}
 */
PsiTerm.buildNoClone=function (sub,inner){
  var r=new PsiTerm();
  r.sub=sub;
  r.inner=inner;
  return r;
}
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.sub,this.inner);
}
/** @param {boolean} abbreviate */
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"])&&this.equal(Term.ONE)) return "1";
    else if ((abbreviate===true||abbreviate["ω"])&&this.equal(Term.SMALLOMEGA)) return "ω";
    else if ((abbreviate===true||abbreviate["1ψ"])&&this.sub.equal(Term.ZERO)) return "ψ("+this.inner.toString(abbreviate)+")";
    else if ((abbreviate===true||abbreviate["2ψ"])) return "ψ_"+this.sub.toString(abbreviate)+"("+this.inner.toString(abbreviate)+")";
  }
  return "ψ("+this.sub.toString(abbreviate)+","+this.inner.toString(abbreviate)+")";
}
PsiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof PsiTerm&&this.sub.equal(other.sub)&&this.inner.equal(other.inner);
}
Object.defineProperty(PsiTerm.prototype,"constructor",{
  value:PsiTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s
 * @returns {SumTerm}
 */
function SumTerm(s){
  if (s instanceof SumTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof SumTerm)) return new SumTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof SumTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term[]} */
  this.terms=null;
}
Object.assign(SumTerm,Term);
/** @param {*[]} terms */
SumTerm.build=function (terms){
  var r=new SumTerm();
  r.terms=[];
  for (var i=0;i<terms.length;i++){
    if (terms[i] instanceof SumTerm){
      r.terms=r.terms.concat(new Term(terms[i]).terms);
    }else{
      r.terms.push(new Term(terms[i]));
    }
  }
  return r;
}
/** @param {Term[]} terms */
SumTerm.buildNoClone=function (terms){
  var r=new SumTerm();
  r.terms=[];
  for (var i=0;i<terms.length;i++){
    if (terms[i] instanceof SumTerm){
      r.terms=r.terms.concat(terms[i].terms);
    }else{
      r.terms.push(terms[i]);
    }
  }
  return r;
}
SumTerm.prototype=Object.create(Term.prototype);
SumTerm.prototype.clone=function (){
  return SumTerm.build(this.terms);
}
/** @param {boolean} abbreviate */
SumTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    var strterms=this.terms.map(function (t){return t.toString(abbreviate);});
    if (abbreviate===true||abbreviate["1"]&&abbreviate["n"]){
      for (var i=0;i<strterms.length;i++){
        if (strterms[i]=="1"){
          for (var j=i;j<strterms.length&&strterms[j]=="1";j++);
          strterms.splice(i,j-i,(j-i)+"");
        }
      }
    }
    return strterms.join("+");
  }else{
    return this.terms.join("+");
  }
}
/** @param {boolean} abbreviate */
SumTerm.prototype.toStringWithImplicitBrace=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"]&&abbreviate["n"])&&isSumAndTermsSatisfy(this,equalFunc(Term.ONE))) return this.toString(abbreviate);
  }
  return "{"+this.toString(abbreviate)+"}";
}
SumTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof SumTerm
    ?this.terms.length==other.terms.length&&this.terms.every(function (e,i){return e.equal(other.terms[i]);})
    :this.terms.length==1&&this.terms[0].equal(other);
}
SumTerm.prototype.getLeft=function (){
  return this.terms[0];
}
/** @returns {Term} */
SumTerm.prototype.getNotLeft=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return this.terms[1];
  else return SumTerm.buildNoClone(this.terms.slice(1));
}
SumTerm.prototype.getRight=function (){
  return this.terms[this.terms.length-1];
}
/** @returns {Term} */
SumTerm.prototype.getNotRight=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return this.terms[0];
  else return SumTerm.buildNoClone(this.terms.slice(0,-1));
}
/**
 * @param {number} start
 * @param {number} end
 * @returns {Term}
 */
SumTerm.prototype.slice=function (start,end){
  if (start<0) start=this.terms.length+start;
  if (end===undefined) end=this.terms.length;
  if (end<0) end=this.terms.length+end;
  if (start>=end) return NullTerm.build();
  else if (end-start==1) return this.terms[start];
  else return SumTerm.buildNoClone(this.terms.slice(start,end));
}
Object.defineProperty(SumTerm.prototype,"constructor",{
  value:SumTerm,
  enumerable:false,
  writable:true
});

Term.ZERO=new Term("0");
Term.ONE=new Term("ψ_0(0)");
Term.SMALLOMEGA=new Term("ψ_0(1)");

/** @returns {boolean} */
function inT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true; //1
  if (t instanceof SumTerm) return t.terms.every(inPT); //2
  if (t instanceof PsiTerm) return inT(t.sub)&&inT(t.inner); //3
  return false;
}
function inPT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof PsiTerm) return inT(t.sub)&&inT(t.inner); //3
  return false;
}
/**
 * @param {Term} t
 * @param {(value:Term,index:number,array:Term[])=>boolean} f
 */
function isSumAndTermsSatisfy(t,f){
  return t instanceof SumTerm&&t.terms.every(f);
}
function isNat(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  return t instanceof Term&&(t.equal(Term.ZERO)||t.equal(Term.ONE)||isSumAndTermsSatisfy(t,equalFunc(Term.ONE)));
}
function toNat(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!isNat(X)) throw Error("Invalid argument: "+X);
  if (X instanceof ZeroTerm) return 0;
  if (X instanceof PsiTerm) return 1;
  if (X instanceof SumTerm) return X.terms.length;
  throw Error("This should be unreachable");
}
/**
 * @param {Term|string} X
 * @param {Term|string} Y
 */
function equal(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  return X.equal(Y);
}
/**
 * @param {Term|string} X
 */
function equalFunc(X){
  if (!(X instanceof Term)) X=new Term(X);
  return function(t){return equal(t,X);};
}
/**
 * @param {Term|string} X
 * @param {Term|string} Y
 */
function notEqual(X,Y){
  return !equal(X,Y);
}
/**
 * @param {Term|string} X
 */
function notEqualFunc(X){
  if (!(X instanceof Term)) X=new Term(X);
  return function(t){return notEqual(t,X);};
}
/**
 * @param {Term|string} S
 * @param {Term|string} T
 * @returns S<=T
 */
function lessThanOrEqual(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  return equal(S,T)||lessThan(S,T);
}
/**
 * @param {Term|string} S
 * @param {Term|string} T
 * @returns {boolean} S<T
 */
function lessThan(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (T instanceof ZeroTerm) return false; //1
  if (S instanceof ZeroTerm) return true; //2
  if (S instanceof SumTerm){ //3
    if (T instanceof SumTerm) //3.1
      return lessThan(S.getLeft(),T.getLeft()) //3.1.1
        ||equal(S.getLeft(),T.getLeft())&&lessThan(S.getNotLeft(),T.getNotLeft()); //3.1.2
    if (T instanceof PsiTerm) return lessThan(S.getLeft(),T); //3.2
  }
  if (S instanceof PsiTerm){ //4
    if (T instanceof SumTerm) return lessThanOrEqual(S,T.getLeft()); //4.1
    if (T instanceof PsiTerm) //4.2
      return lessThan(S.sub,T.sub) //4.2.1
        ||equal(S.sub,T.sub)&&lessThan(S.inner,T.inner); //4.2.2
  }
  throw Error("No rule to compute if "+S+"<"+T);
}
/**
 * @param {Term|string} S
 * @returns {string}
 */
function cp(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return cp(S.getRight()); //2
  if (S instanceof PsiTerm){ //3
    var cp_S_inner=cp(S.inner);
    var Term_cp_S_inner=new Term(cp_S_inner);
    if (equal(Term_cp_S_inner,Term.ZERO)){ //3.1
      var cp_S_sub=cp(S.sub);
      var Term_cp_S_sub=new Term(cp_S_sub);
      if (equal(Term_cp_S_sub,Term.ZERO)||equal(Term_cp_S_sub,Term.ONE)) return S+""; //3.1.1
      else return cp_S_sub; //3.1.2
    }else return cp_S_inner; //3.2
  }
  throw Error("No rule to compute cp("+S+")");
}
/**
 * @param {Term|string} G
 * @param {Term|string} tbp
 * @param {Term|string} abp
 * @returns {string}
 */
function bp(G,tbp,abp){
  if (!(G instanceof Term)) G=new Term(G);
  if (!(tbp instanceof Term)) tbp=new Term(tbp);
  if (!(abp instanceof Term)) abp=new Term(abp);
  if (!inT(G)||!inT(tbp)||!inT(abp)) throw Error("Invalid argument: "+G+","+tbp+","+abp);
  if (lessThan(tbp,abp)){ //1
    if (G instanceof SumTerm&&tbp instanceof SumTerm) return bp(G.getNotLeft(),tbp.getNotLeft(),abp); //1.1
    if (G instanceof PsiTerm&&tbp instanceof PsiTerm){ //1.2
      if (equal(tbp.inner,Term.ZERO)) return bp(G.sub,tbp.sub,abp); //1.2.1
      else return bp(G.inner,tbp.inner,abp); //1.2.2
    }
    return "0"; //1.3
  }else return G+""; //2
  throw Error("No rule to compute bp("+G+","+tbp+","+abp+")");
}
/**
 * @param {Term|string} S
 * @returns {string}
 */
function dom(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return dom(S.getRight()); //2
  if (S instanceof PsiTerm){ //3
    var dom_S_inner=dom(S.inner);
    var Term_dom_S_inner=new Term(dom_S_inner);
    if (equal(Term_dom_S_inner,Term.ZERO)){ //3.1
      var dom_S_sub=dom(S.sub);
      var Term_dom_S_sub=new Term(dom_S_sub);
      if (equal(Term_dom_S_sub,Term.ZERO)||equal(Term_dom_S_sub,Term.ONE)) return S+""; //3.1.1
      else return dom_S_sub; //3.2
    }else if (equal(Term_dom_S_inner,Term.ONE)) return Term.SMALLOMEGA+""; //3.2
    else{ //3.3
      if (lessThan(Term_dom_S_inner,S)) return dom_S_inner; //3.3.1
      else{ //3.3.2
        if (!(Term_dom_S_inner instanceof PsiTerm)) throw Error("Failed assertion");
        if (lessThan(Term_dom_S_inner.inner,S.inner)) return S+""; //3.3.2.1
        else return Term.SMALLOMEGA+""; //3.3.2.2
      }
    }
  }
  throw Error("No rule to compute dom("+S+")");
}
/**
 * @param {Term|string} S
 * @param {Term|number|string} T
 * @returns {string} S[T]
 */
function fund(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (typeof T=="number") T=String(T);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm){ //2
    var fund_S_getRight_T=fund(S.getRight(),T);
    var Term_fund_S_getRight_T=new Term(fund_S_getRight_T);
    if (equal(Term_fund_S_getRight_T,Term.ZERO)) return S.getNotRight()+""; //2.1
    else return S.getNotRight()+"+"+fund_S_getRight_T; //2.2
  }
  if (S instanceof PsiTerm){ //3
    var dom_S_inner=dom(S.inner);
    var Term_dom_S_inner=new Term(dom_S_inner);
    if (equal(Term_dom_S_inner,Term.ZERO)){ //3.1
      var dom_S_sub=dom(S.sub);
      var Term_dom_S_sub=new Term(dom_S_sub);
      if (equal(Term_dom_S_sub,Term.ZERO)||equal(Term_dom_S_sub,Term.ONE)) return T+""; //3.1.1
      else return "ψ("+fund(S.sub,T)+","+S.inner+")"; //3.1.2
    }else if (equal(Term_dom_S_inner,Term.ONE)){ //3.2
      var fund_T_0=fund(T,Term.ZERO);
      if (equal(T,fund_T_0+"+"+Term.ONE)) return fund(S,fund_T_0)+"+"+fund(S,Term.ONE); //3.2.1
      else return "ψ("+S.sub+","+fund(S.inner,Term.ZERO)+")"; //3.2.2
    }else{ //3.3
      if (!(Term_dom_S_inner instanceof PsiTerm)) throw Error("Assertion failed");
      if (lessThan(Term_dom_S_inner,S)) return "ψ("+S.sub+","+fund(S.inner,T)+")"; //3.3.1
      else{ //3.3.2
        if (!(Term_dom_S_inner instanceof PsiTerm)) throw Error("Failed assertion");
        var d=Term_dom_S_inner.inner;
        if (lessThan(d,S.inner)) return "ψ("+S.sub+","+fund(S.inner,T)+")"; //3.3.2.1
        else{ //3.3.2.2
          var cp_d=cp(d);
          var Term_cp_d=new Term(cp_d);
          if (!(Term_cp_d instanceof PsiTerm&&equal(Term_cp_d.inner,Term.ZERO))) throw Error("Failed assertion");
          var Term_fund_S_fund_T_0=null;
          if (equal(dom(T),Term.ONE)&&(Term_fund_S_fund_T_0=new Term(fund(S,fund(T,Term.ZERO)))) instanceof PsiTerm&&equal(Term_fund_S_fund_T_0.sub,S.sub)) return "ψ("+S.sub+","+fund(S.inner,"ψ("+fund(Term_cp_d.sub,Term.ZERO)+","+bp(Term_fund_S_fund_T_0.inner,S.inner,d)+")")+")"; //3.3.2.2.1
          else return "ψ("+S.sub+","+fund(S.inner,"ψ("+fund(Term_cp_d.sub,Term.ZERO)+",0)")+")"; //3.3.2.2.2
        }
      }
    }
  }
  throw Error("No rule to compute "+S+"["+T+"]");
}
/**
 * @param {Term|string} S
 * @param {number} m
 * @param {number} n
 * @returns {number}
 */
function FGH(S,m,n){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)||typeof m!="number"||typeof n!="number") throw Error("Invalid argument: "+S+","+m+","+n);
  if (m==0) return n; //1
  else if (m==1){ //2
    var dom_S=dom(S);
    var Term_dom_S=new Term(dom_S);
    if (equal(Term_dom_S,Term.ZERO)) return n+1; //2.1
    else if (equal(Term_dom_S,Term.ONE)) return FGH(fund(S,Term.ZERO),n,n); //2.2
    else return FGH(fund(S,n),1,n); //2.3
  }else return FGH(S,1,FGH(S,m-1,n)); //3
}
/**
 * @param {number} n
 * @returns {string} ψ(0,Λ(n))
 */
function limitOrd(n){
  return "ψ(0,ψ(0,"+"ψ(".repeat(n+1)+"0"+",0)".repeat(n+1)+"))";
}
function findOTPath(x,limit){
  if (!(x instanceof Term)) x=new Term(x);
  if (!inT(x)) throw Error("Invalid argument: "+x);
  if (typeof limit=="undefined"||limit==-1) limit=Infinity;
  if (equal(x,Term.ZERO)){
    return {isStandard:true,path:["0"],funds:[-1]};
  }else{
    var n=0;
    var t;
    while(n<=limit&&!(equal(x,t=limitOrd(n))||lessThan(x,t))){
      n++;
    };
    if (n>limit) return {isStandard:false,path:[],funds:[]};
    t=limitOrd(n);
    // console.log(t);
    var r={isStandard:false,path:[t],funds:[n]};
    while (!equal(x,t)){
      n=0;
      var nt;
      while (n<=limit&&lessThan(nt=fund(t,n),x)) n++;
      if (n>limit) return r;
      r.path.push(t=nt);
      r.funds.push(n);
      // console.log(nt);
    }
    r.isStandard=true;
    return r;
  }
}
function isStandard(x,limit){
  return findOTPath(x,limit).isStandard;
}
/**
 * @param {number} n
 * @returns {number}
 */
function largeFunction(n){
  if (typeof n!="number") throw Error("Invalid argument");
  return FGH(limitOrd(n),1,n);
}
function calculateN(){
  var r=1e100;
  for (var i=0;i<1e100;i++) r=largeFunction(r);
  return r;
}

/** @type {[string,number][]} */
var testTermsPre=[
  ["0",-1],
  ["1",-1],
  ["ω",3],
  ["ψ_0(2)",3],
  ["ψ_0(ω)",3],
  ["ψ_0(ψ_0(ω))",3],
  ["ψ_0(ψ_0(ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(0))+1)",3],
  ["ψ_0(ψ_0(ψ_1(0))+ψ_0(ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(0)+1))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_0(ψ_0(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_0(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_0(ψ_1(0)+ψ_0(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0))+ψ_0(ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0))+ψ_0(ψ_1(0)+ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0)+1))",-1],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0)+ψ_0(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0)+ψ_0(ψ_1(0)+ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0)+ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(0)+ψ_1(0)+ψ_1(0)+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_1(1)))",3],
  ["ψ_0(ψ_0(ψ_1(ω)))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_0(ψ_0(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_0(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(0)+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_0(ψ_1(0)))))",-1],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+1))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(0)+ψ_0(ψ_1(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_0(ψ_1(ψ_1(0))))))))",-1],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))))+ψ_0(ψ_1(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))))+ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))))+ψ_1(ψ_0(ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(0)+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(0)+ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))+ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(0)+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))))+ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))))+ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0))+ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_0(ψ_1(ψ_1(0))+ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)+1)))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)+ψ_0(ψ_0(ψ_1(ψ_1(0)))))))",-1],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)+ψ_0(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(0)+ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(1))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_0(ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(0)))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_0(ψ_1(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_0(ψ_1(ψ_1(ψ_1(0))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_1(ψ_0(ψ_1(ψ_1(ψ_1(0)))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_1(ψ_0(ψ_1(ψ_1(ψ_1(0)))))+ψ_0(ψ_1(ψ_1(ψ_1(0))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_1(0)))+ψ_0(ψ_1(ψ_1(ψ_0(ψ_1(ψ_1(ψ_1(0))))+ψ_0(ψ_1(ψ_1(ψ_1(0)))))))))",3],
  ["ψ_0(ψ_0(ψ_1(ψ_1(ψ_1(ψ_1(0))))))",-1],
  ["ψ_0(ψ_0(ψ_2(0)))",3],
  ["ψ_0(ψ_0(ψ_2(0))+ψ_0(ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_2(0))+ψ_0(ψ_1(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_2(0))+ψ_0(ψ_2(0)))",3],
  ["ψ_0(ψ_0(ψ_2(0)+1))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_0(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_0(ψ_2(0)))+ψ_1(ψ_0(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0))+ψ_0(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0))+ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0))+ψ_1(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0))+ψ_1(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0)+1))))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0)+ψ_0(ψ_1(0))))))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0)+ψ_0(ψ_1(ψ_2(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_0(ψ_2(0))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(0)+ψ_0(ψ_2(0)+ψ_0(ψ_2(0)+ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(0)+ψ_0(ψ_2(0)+ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(0)+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(1)))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_0(ψ_1(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_0(ψ_1(ψ_2(0)+ψ_1(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_0(ψ_1(ψ_2(0)+ψ_1(ψ_0(ψ_1(ψ_2(0)))))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_0(ψ_1(ψ_2(0)+ψ_1(ψ_0(ψ_1(ψ_2(0)+ψ_1(0)))))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_0(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_1(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_2(0))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_2(0)+ψ_1(ψ_1(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_1(ψ_2(0)+ψ_1(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_2(0)))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_2(0))))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_2(0)+ψ_1(ψ_1(ψ_2(0)+ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)))))",-1],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_1(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_2(0)+ψ_1(ψ_2(0)+ψ_1(ψ_2(0)+ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(1)))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_0(ψ_2(0))))))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_1(0)))))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_1(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_1(ψ_2(0))+ψ_0(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_1(ψ_2(0))+ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_1(ψ_2(0))+ψ_1(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)+ψ_0(ψ_1(ψ_2(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)+ψ_0(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)+ψ_1(ψ_1(ψ_2(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)+ψ_1(ψ_1(ψ_2(ψ_0(ψ_2(0)))))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)+ψ_1(ψ_2(0))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(0)+ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_0(ψ_2(1)))))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_1(0)))+ψ_0(ψ_2(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_1(0))+ψ_0(ψ_2(ψ_0(ψ_2(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_1(0))+ψ_0(ψ_2(ψ_1(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_1(0))+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_1(0)+ψ_1(0))))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_1(ψ_1(ψ_2(0))))))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_1(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_1(ψ_0(ψ_2(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_1(ψ_0(ψ_2(ψ_1(ψ_2(0))))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_1(ψ_0(ψ_2(ψ_2(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_2(ψ_0(ψ_2(ψ_1(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_2(ψ_0(ψ_2(ψ_1(ψ_2(0))))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_2(ψ_0(ψ_2(ψ_2(0)))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_0(ψ_2(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_2(0)))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_1(ψ_2(ψ_2(0))))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_1(ψ_2(ψ_2(0))))+ψ_2(ψ_1(ψ_2(ψ_2(0))))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_2(0))+ψ_1(ψ_2(ψ_1(ψ_2(ψ_2(0)))+ψ_1(ψ_2(ψ_2(0))))))))",3],
  ["ψ_0(ψ_0(ψ_2(ψ_2(0))+ψ_2(0)))",3],
  ["ψ_0(ψ_0(ψ_3(0)))",3],
  ["ψ_0(ψ_0(ψ_ω(0)))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_0(ψ_0(ψ_ω(0)))))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_0(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_0(ψ_1(ψ_ω(0)))))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_0(ψ_2(0))))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_0(ψ_ω(0))))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_1(0)))",3],
  ["ψ_0(ψ_0(ψ_ω(0)+ψ_ω(0)))",-1],
  ["ψ_0(ψ_0(ψ_ω(1)))",-1],
  ["ψ_0(ψ_0(ψ_ω(ψ_0(ψ_ω(0)))))",-1],
  ["ψ_0(ψ_0(ψ_ω(ψ_1(0))))",-1],
  ["ψ_0(ψ_0(ψ_ω(ψ_1(ψ_ω(0)))))",-1],
  ["ψ_0(ψ_0(ψ_ω(ψ_ω(0))))",-1],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_0(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_0(ψ_1(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_0(ψ_2(0))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_0(ψ_ω(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_1(ψ_0(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_1(ψ_1(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_1(ψ_2(0))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_1(ψ_ω(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_2(0)))",-1],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_ω(0)))",-1],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_ω(ψ_0(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_ω(ψ_ω(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_ω(ψ_{ω+1}(0))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(0)+ψ_{ω+1}(0)))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(1)))",-1],
  ["ψ_0(ψ_0(ψ_{ω+1}(ψ_1(0))))",-1],
  ["ψ_0(ψ_0(ψ_{ω+1}(ψ_1(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(ψ_ω(ψ_{ω+1}(0)))))",3],
  ["ψ_0(ψ_0(ψ_{ω+1}(ψ_{ω+1}(0))))",3],
  ["ψ_0(ψ_0(ψ_{ω+2}(0)))",-1],
  ["ψ_0(ψ_0(ψ_{ω+ω}(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(2)(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ω)(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_0(ψ_1(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_0(ψ_1(ψ_1(0))))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_0(ψ_ω(0)))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_0(ψ_{ω+1}(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0))+ψ_0(ψ_ψ_0(ψ_1(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0)+ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0)+ψ_0(ψ_1(0)+ψ_0(ψ_ψ_0(ψ_1(0))(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0)+ψ_0(ψ_ψ_0(ψ_1(0))(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(0)+ψ_1(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0))(1)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_0(ψ_1(0)+ψ_1(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_0(ψ_2(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_1(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_1(0))(0)+ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_1(0))(0)))))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_1(0))(0)+ψ_0(ψ_1(0)+ψ_0(ψ_ψ_0(ψ_1(0)+ψ_1(0))(0)))))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(0)+ψ_1(0)+ψ_1(0))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(1))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_1(ψ_1(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_2(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_2(0)+ψ_1(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_0(ψ_ω(0))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(0))+ψ_0(ψ_ψ_1(0)(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(0)+ψ_0(ψ_0(ψ_ψ_1(0)(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(0)+ψ_0(ψ_1(0)+ψ_0(ψ_ψ_1(0)(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(0)+ψ_0(ψ_ψ_1(0)(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_0(ψ_ψ_0(ψ_1(0))(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_0(ψ_ψ_1(0)(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_1(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_1(ψ_ψ_0(ψ_1(0))(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_1(ψ_ψ_1(0)(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_ψ_0(ψ_1(0))(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(0)(ψ_ψ_1(0)(0))))",3],
  ["ψ_0(ψ_0(ψ_{ψ_1(0)+1}(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(1)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_0(ψ_1(0)))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_0(ψ_2(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_0(ψ_ψ_1(0)(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_1(0))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_2(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_2(0))(0)+ψ_0(ψ_ψ_1(ψ_1(ψ_ψ_1(ψ_2(0))(0)))(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_2(0))(0)+ψ_0(ψ_ψ_1(ψ_2(0))(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_2(0))(0)+ψ_1(ψ_ψ_1(ψ_2(0))(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_1(ψ_2(ψ_2(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0))+ψ_0(ψ_ψ_2(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_0(ψ_ψ_2(0)(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_1(ψ_ψ_2(0)(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_2(ψ_ψ_2(0)(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_ψ_0(ψ_2(0))(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_ψ_0(ψ_ψ_2(0)(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_ψ_1(ψ_1(ψ_2(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_ψ_1(ψ_2(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_ψ_1(ψ_ψ_1(ψ_ψ_2(0)(0))(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(0)+ψ_ψ_1(ψ_ψ_2(0)(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(0)(ψ_1(ψ_ψ_2(0)(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(ψ_0(ψ_1(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(ψ_0(ψ_ψ_2(0)(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(ψ_1(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(ψ_1(ψ_ψ_2(0)(0)))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_2(ψ_2(0))(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_3(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ω(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(ψ_0(ψ_ψ_ψ_1(0)(0)(0)))))",3],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(ψ_1(0))))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(ψ_ψ_0(ψ_ψ_ψ_1(0)(0)(0))(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(ψ_ψ_1(0)(0))))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(ψ_ψ_ψ_0(ψ_ψ_ψ_1(0)(0)(0))(0)(0))))",3],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)(ψ_ψ_ψ_1(0)(0)(0))))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(0)(0)+1(0)))",3],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(ψ_0(ψ_ψ_ψ_1(0)(0)(0)))(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(ψ_1(0))(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(ψ_2(0))(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(ψ_ψ_1(0)(0))(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(ψ_ψ_2(0)(0))(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_1(ψ_ψ_ψ_1(0)(0)(0))(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_2(0)(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_ω(0)(0)(0)))",-1],
  ["ψ_0(ψ_0(ψ_ψ_ψ_ψ_1(0)(0)(0)(0)))",-1]
];
/** @type {string[]}} */
var testTerms;
function setupTestTerms(){
  document.getElementById('input').value=testTermsPre.filter(function (t){return t[1]>=0;}).map(function(t){return "fund "+t[0]+" "+t[1];}).join("\n");
  testTerms=testTermsPre.map(function (t){return t[0];});
}
/** @param {boolean} logInfoToConsole */
function testFunction(logInfoToConsole){
  var r={lessThan:[],inOT:[],errors:[]};
  for (var i=0;i<testTerms.length;i++){
    for (var j=0;j<testTerms.length;j++){
      if (logInfoToConsole) console.log("%cTesting: lessThan, "+testTerms[i]+", "+testTerms[j]+".","color:gold");
      var d=Date.now();
      var caught=false;
      var result;
      try{
        result=lessThan(testTerms[i],testTerms[j]);
      }catch(e){
        var diff=Date.now()-d;
        r.lessThan.push({arg0:testTerms[i],arg1:testTerms[j],result:e,time:diff});
        r.errors.push({test:"lessThan",arg0:testTerms[i],arg1:testTerms[j],name:"error",content:e});
        console.error(e);
        var caught=true;
      }finally{
        var diff=Date.now()-d;
        if (!caught){
          r.lessThan.push({arg0:testTerms[i],arg1:testTerms[j],result:result,time:diff});
          if (logInfoToConsole) console.log(diff);
          if (result!=(i<j)){
            r.errors.push({test:"lessThan",arg0:testTerms[i],arg1:testTerms[j],name:"fail"});
            console.error("Failed test: lessThan, "+testTerms[i]+", "+testTerms[j]+", expected "+(i<j)+".");
          }
        }
      }
    }
  }
  for (var i=0;i<testTerms.length;i++){
    if (logInfoToConsole) console.log("%cTesting: inOT, "+testTerms[i]+".","color:gold");
    var d=Date.now();
    var caught=false;
    var result;
    try{
      result=isStandard(testTerms[i],10);
    }catch(e){
      var diff=Date.now()-d;
      r.inOT.push({arg0:testTerms[i],result:e,time:diff});
      r.errors.push({test:"inOT",arg0:testTerms[i],name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.inOT.push({arg0:testTerms[i],result:result,time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"inOT",arg0:testTerms[i],name:"fail"});
          console.error("Failed test: inOT, "+testTerms[i]+".");
        }
      }
    }
  }
  return r;
}
function JSONStringifyWithError(obj){
  return JSON.stringify(obj,function replaceErrors(key,value){
    if (value instanceof Error){
      var error={};
      Object.getOwnPropertyNames(value).forEach(function (key){error[key]=value[key];});
      return error;
    }
    else return value;
  });
}
function downloadFile(data,filename,type){
  var file=new Blob([data],{type:type});
  var a=document.createElement("a");
  var url=URL.createObjectURL(file);
  a.href=url;
  a.download=filename;
  document.body.appendChild(a);
  a.click();
  setTimeout(function(){
    document.body.removeChild(a);
    window.URL.revokeObjectURL(url);
  },0);
}

var input="";
var options={
  abbreviate:undefined,
  detail:undefined
}
var optionList=[
  "abbreviate",
  "detail"
];
var abbreviateOptionList=[
  "1",
  "n",
  "ω",
  "2ψ",
  "1ψ"
];
function toggleOptions(){
  document.getElementById("options").style.display=document.getElementById("options").style.display=="none"?"block":"none";
}
var last=null;
function compute(){
  var inputChanged=false;
  var oldinput=input;
  inputChanged||=input!=document.getElementById("input").value;
  input=document.getElementById("input").value;
  inputChanged||=!!options.abbreviate!=document.getElementById("abbreviate").checked;
  options.abbreviate=document.getElementById("abbreviate").checked&&(options.abbreviate||{});
  inputChanged||=options.detail!=document.getElementById("detail").checked;
  options.detail=document.getElementById("detail").checked;
  if (options.abbreviate){
    abbreviateOptionList.forEach(function(option){
      var elem=document.getElementById("abbreviate"+option);
      inputChanged||=options.abbreviate[option]!=elem.checked;
      options.abbreviate[option]=elem.checked;
    });
  }
  if (!inputChanged) return;
  if (oldinput!=input) last=[];
  var output="";
  var lines=input.split(lineBreakRegex);
  function abbreviateIfEnabled(x){
    if (options.abbreviate) return abbreviate(x,options.abbreviate);
    else return normalizeAbbreviations(x);
  }
  for (var l=0;l<lines.length;l++){
    var line=lines[l];
    var args=line.split(itemSeparatorRegex);
    var cmd=args.shift();
    output+=line+"\n";
    var result;
    if (oldinput!=input){
      console.time(line);
      try{
        if (cmd=="normalize"||cmd=="norm"){
          result=normalizeAbbreviations(args[0]);
        }else if (cmd=="abbreviate"||cmd=="abbr"){
          result=null;
        }else if (cmd=="inT"){
          result=inT(args[0]);
        }else if (cmd=="inPT"){
          result=inPT(args[0]);
        }else if (cmd=="lessThanOrEqual"||cmd=="<="){
          result=lessThanOrEqual(args[0],args[1]);
        }else if (cmd=="lessThan"||cmd=="<"){
          result=lessThan(args[0],args[1]);
        }else if (cmd=="cp"){
          result=cp(args[0]);
        }else if (cmd=="bp"){
          result=bp(args[0],args[1],args[2]);
        }else if (cmd=="dom"){
          result=dom(args[0]);
        }else if (cmd=="fund"||cmd=="expand"){
          var t=normalizeAbbreviations(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,args[i]));
          }
        }else if (cmd=="inOT"||cmd=="isStandard"){
          result=findOTPath(args[0],args[1]||3);
        }else{
          result=null;
        }
      }catch(e){
        result=e;
        console.error(e);
      }
      last[l]=result;
      console.timeEnd(line);
    }else result=last[l];
    if (result instanceof Error){
      output+=result.stack?result.stack:result;
    }else if (cmd=="normalize"||cmd=="norm"){
      output+=result;
    }else if (cmd=="abbreviate"||cmd=="abbr"){
      output+=abbreviate(args[0],options.abbreviate||true);
    }else if (cmd=="inT"){
      output+=result;
    }else if (cmd=="inPT"){
      output+=result;
    }else if (cmd=="lessThanOrEqual"||cmd=="<="){
      output+=result;
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="cp"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="bp"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="dom"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="fund"||cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+=abbreviateIfEnabled(result[i-1])+"["+args[i]+"]="+abbreviateIfEnabled(result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=abbreviateIfEnabled(result[result.length-1]);
      }
    }else if (cmd=="inOT"||cmd=="isStandard"){
      if (options.detail){
        for (var i=1;i<result.path.length;i++){
          output+=abbreviateIfEnabled(result.path[i-1])+"["+result.funds[i]+"]="+abbreviateIfEnabled(result.path[i])+"\n";
        }
        if (result.isStandard) output+=abbreviateIfEnabled(args[0])+"∈OT";
        else output+=abbreviateIfEnabled(args[0])+"∉OT limited to n≦"+(args[1]||3);
      }else{
        output+=result.isStandard;
      }
    }else{
      output+="Unknown command "+cmd;
    }
    output+="\n\n";
  }
  document.getElementById("output").value=output;
}
var handlekey=function(e){}