"use strict";
var __haste_prog_id = '9413199c91eeeb08a6234aa9b1e9200d81964dc35ab35e6bfa8a2a31ff7e0e8c';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0/* compile_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(compile)");
}),
_1/* mappend */ = function(_2/* s374 */){
  return E(E(_2/* s374 */).b);
},
_3/* mempty */ = function(_4/* s36Z */){
  return E(E(_4/* s36Z */).a);
},
_5/* $fFoldableVar_$cfoldMap */ = function(_6/* s7AE */, _7/* s7AF */, _8/* s7AG */){
  var _9/* s7AH */ = E(_8/* s7AG */);
  if(!_9/* s7AH */._){
    return new F(function(){return A1(_7/* s7AF */,_9/* s7AH */.a);});
  }else{
    var _a/* s7AK */ = new T(function(){
      return B(_1/* GHC.Base.mappend */(_6/* s7AE */));
    }),
    _b/* s7AL */ = new T(function(){
      return B(_3/* GHC.Base.mempty */(_6/* s7AE */));
    }),
    _c/* s7AM */ = function(_d/* s7AN */){
      var _e/* s7AO */ = E(_d/* s7AN */);
      if(!_e/* s7AO */._){
        return E(_b/* s7AL */);
      }else{
        return new F(function(){return A2(_a/* s7AK */,new T(function(){
          return B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_6/* s7AE */, _7/* s7AF */, _e/* s7AO */.a));
        }), new T(function(){
          return B(_c/* s7AM */(_e/* s7AO */.b));
        }));});
      }
    };
    return new F(function(){return _c/* s7AM */(_9/* s7AH */.a);});
  }
},
_f/* ++ */ = function(_g/* s3hH */, _h/* s3hI */){
  var _i/* s3hJ */ = E(_g/* s3hH */);
  return (_i/* s3hJ */._==0) ? E(_h/* s3hI */) : new T2(1,_i/* s3hJ */.a,new T(function(){
    return B(_f/* GHC.Base.++ */(_i/* s3hJ */.b, _h/* s3hI */));
  }));
},
_j/* poly_go */ = function(_k/* s3nR */){
  var _l/* s3nS */ = E(_k/* s3nR */);
  if(!_l/* s3nS */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_l/* s3nS */.a, new T(function(){
      return B(_j/* GHC.Base.poly_go */(_l/* s3nS */.b));
    },1));});
  }
},
_m/* $fMonoid[]_$cmconcat */ = function(_n/* s3nW */){
  return new F(function(){return _j/* GHC.Base.poly_go */(_n/* s3nW */);});
},
_o/* [] */ = __Z/* EXTERNAL */,
_p/* $fMonoid[] */ = new T3(0,_o/* GHC.Types.[] */,_f/* GHC.Base.++ */,_m/* GHC.Base.$fMonoid[]_$cmconcat */),
_q/* $fFloatingVar30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(","));
}),
_r/* $fFloatingVar29 */ = new T1(0,_q/* Lib.Shader.$fFloatingVar30 */),
_s/* $fFloatingVar32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pow("));
}),
_t/* $fFloatingVar31 */ = new T1(0,_s/* Lib.Shader.$fFloatingVar32 */),
_u/* $c+2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_v/* $c+1 */ = new T1(0,_u/* Lib.Shader.$c+2 */),
_w/* gradStr3 */ = new T2(1,_v/* Lib.Shader.$c+1 */,_o/* GHC.Types.[] */),
_x/* $fFloatingVar_$c** */ = function(_y/* s7zP */, _z/* s7zQ */){
  return new T1(1,new T2(1,_t/* Lib.Shader.$fFloatingVar31 */,new T2(1,_y/* s7zP */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_z/* s7zQ */,_w/* Lib.Shader.gradStr3 */)))));
},
_A/* $fFloatingVar16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("acos("));
}),
_B/* $fFloatingVar15 */ = new T1(0,_A/* Lib.Shader.$fFloatingVar16 */),
_C/* $fFloatingVar_$cacos */ = function(_D/* s7zu */){
  return new T1(1,new T2(1,_B/* Lib.Shader.$fFloatingVar15 */,new T2(1,_D/* s7zu */,_w/* Lib.Shader.gradStr3 */)));
},
_E/* $fFloatingVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("acosh("));
}),
_F/* $fFloatingVar3 */ = new T1(0,_E/* Lib.Shader.$fFloatingVar4 */),
_G/* $fFloatingVar_$cacosh */ = function(_H/* s7zc */){
  return new T1(1,new T2(1,_F/* Lib.Shader.$fFloatingVar3 */,new T2(1,_H/* s7zc */,_w/* Lib.Shader.gradStr3 */)));
},
_I/* $fFloatingVar18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("asin("));
}),
_J/* $fFloatingVar17 */ = new T1(0,_I/* Lib.Shader.$fFloatingVar18 */),
_K/* $fFloatingVar_$casin */ = function(_L/* s7zx */){
  return new T1(1,new T2(1,_J/* Lib.Shader.$fFloatingVar17 */,new T2(1,_L/* s7zx */,_w/* Lib.Shader.gradStr3 */)));
},
_M/* $fFloatingVar6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("asinh("));
}),
_N/* $fFloatingVar5 */ = new T1(0,_M/* Lib.Shader.$fFloatingVar6 */),
_O/* $fFloatingVar_$casinh */ = function(_P/* s7zf */){
  return new T1(1,new T2(1,_N/* Lib.Shader.$fFloatingVar5 */,new T2(1,_P/* s7zf */,_w/* Lib.Shader.gradStr3 */)));
},
_Q/* $fFloatingVar14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("atan("));
}),
_R/* $fFloatingVar13 */ = new T1(0,_Q/* Lib.Shader.$fFloatingVar14 */),
_S/* $fFloatingVar_$catan */ = function(_T/* s7zr */){
  return new T1(1,new T2(1,_R/* Lib.Shader.$fFloatingVar13 */,new T2(1,_T/* s7zr */,_w/* Lib.Shader.gradStr3 */)));
},
_U/* $fFloatingVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("atanh("));
}),
_V/* $fFloatingVar1 */ = new T1(0,_U/* Lib.Shader.$fFloatingVar2 */),
_W/* $fFloatingVar_$catanh */ = function(_X/* s7z9 */){
  return new T1(1,new T2(1,_V/* Lib.Shader.$fFloatingVar1 */,new T2(1,_X/* s7z9 */,_w/* Lib.Shader.gradStr3 */)));
},
_Y/* $fFloatingVar22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("cos("));
}),
_Z/* $fFloatingVar21 */ = new T1(0,_Y/* Lib.Shader.$fFloatingVar22 */),
_10/* $fFloatingVar_$ccos */ = function(_11/* s7zD */){
  return new T1(1,new T2(1,_Z/* Lib.Shader.$fFloatingVar21 */,new T2(1,_11/* s7zD */,_w/* Lib.Shader.gradStr3 */)));
},
_12/* $fFloatingVar10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("cosh("));
}),
_13/* $fFloatingVar9 */ = new T1(0,_12/* Lib.Shader.$fFloatingVar10 */),
_14/* $fFloatingVar_$ccosh */ = function(_15/* s7zl */){
  return new T1(1,new T2(1,_13/* Lib.Shader.$fFloatingVar9 */,new T2(1,_15/* s7zl */,_w/* Lib.Shader.gradStr3 */)));
},
_16/* $fFloatingVar36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("exp("));
}),
_17/* $fFloatingVar35 */ = new T1(0,_16/* Lib.Shader.$fFloatingVar36 */),
_18/* $fFloatingVar_$cexp */ = function(_19/* s7A1 */){
  return new T1(1,new T2(1,_17/* Lib.Shader.$fFloatingVar35 */,new T2(1,_19/* s7A1 */,_w/* Lib.Shader.gradStr3 */)));
},
_1a/* $fFloatingVar28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("log("));
}),
_1b/* $fFloatingVar27 */ = new T1(0,_1a/* Lib.Shader.$fFloatingVar28 */),
_1c/* $fFloatingVar_$clog */ = function(_1d/* s7zY */){
  return new T1(1,new T2(1,_1b/* Lib.Shader.$fFloatingVar27 */,new T2(1,_1d/* s7zY */,_w/* Lib.Shader.gradStr3 */)));
},
_1e/* $fFloatingVar26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")/log("));
}),
_1f/* $fFloatingVar25 */ = new T1(0,_1e/* Lib.Shader.$fFloatingVar26 */),
_1g/* $fFloatingVar_$clogBase */ = function(_1h/* s7zJ */, _1i/* s7zK */){
  return new T1(1,new T2(1,_1b/* Lib.Shader.$fFloatingVar27 */,new T2(1,_1i/* s7zK */,new T2(1,_1f/* Lib.Shader.$fFloatingVar25 */,new T2(1,_1h/* s7zJ */,_w/* Lib.Shader.gradStr3 */)))));
},
_1j/* $fFloatingVar37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pi"));
}),
_1k/* $fFloatingVar_$cpi */ = new T1(0,_1j/* Lib.Shader.$fFloatingVar37 */),
_1l/* $fFloatingVar24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sin("));
}),
_1m/* $fFloatingVar23 */ = new T1(0,_1l/* Lib.Shader.$fFloatingVar24 */),
_1n/* $fFloatingVar_$csin */ = function(_1o/* s7zG */){
  return new T1(1,new T2(1,_1m/* Lib.Shader.$fFloatingVar23 */,new T2(1,_1o/* s7zG */,_w/* Lib.Shader.gradStr3 */)));
},
_1p/* $fFloatingVar12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sinh("));
}),
_1q/* $fFloatingVar11 */ = new T1(0,_1p/* Lib.Shader.$fFloatingVar12 */),
_1r/* $fFloatingVar_$csinh */ = function(_1s/* s7zo */){
  return new T1(1,new T2(1,_1q/* Lib.Shader.$fFloatingVar11 */,new T2(1,_1s/* s7zo */,_w/* Lib.Shader.gradStr3 */)));
},
_1t/* $fFloatingVar34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sqrt("));
}),
_1u/* $fFloatingVar33 */ = new T1(0,_1t/* Lib.Shader.$fFloatingVar34 */),
_1v/* $fFloatingVar_$csqrt */ = function(_1w/* s7zV */){
  return new T1(1,new T2(1,_1u/* Lib.Shader.$fFloatingVar33 */,new T2(1,_1w/* s7zV */,_w/* Lib.Shader.gradStr3 */)));
},
_1x/* $fFloatingVar20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tan("));
}),
_1y/* $fFloatingVar19 */ = new T1(0,_1x/* Lib.Shader.$fFloatingVar20 */),
_1z/* $fFloatingVar_$ctan */ = function(_1A/* s7zA */){
  return new T1(1,new T2(1,_1y/* Lib.Shader.$fFloatingVar19 */,new T2(1,_1A/* s7zA */,_w/* Lib.Shader.gradStr3 */)));
},
_1B/* $fFloatingVar8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tanh("));
}),
_1C/* $fFloatingVar7 */ = new T1(0,_1B/* Lib.Shader.$fFloatingVar8 */),
_1D/* $fFloatingVar_$ctanh */ = function(_1E/* s7zi */){
  return new T1(1,new T2(1,_1C/* Lib.Shader.$fFloatingVar7 */,new T2(1,_1E/* s7zi */,_w/* Lib.Shader.gradStr3 */)));
},
_1F/* $c+6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_1G/* $c+5 */ = new T1(0,_1F/* Lib.Shader.$c+6 */),
_1H/* $fFractionalVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")/("));
}),
_1I/* $fFractionalVar3 */ = new T1(0,_1H/* Lib.Shader.$fFractionalVar4 */),
_1J/* $fFractionalVar_$c/ */ = function(_1K/* s7z3 */, _1L/* s7z4 */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_1K/* s7z3 */,new T2(1,_1I/* Lib.Shader.$fFractionalVar3 */,new T2(1,_1L/* s7z4 */,_w/* Lib.Shader.gradStr3 */)))));
},
_1M/* $fRealDouble1 */ = new T1(0,1),
_1N/* compareInteger */ = function(_1O/* s1Hk */, _1P/* s1Hl */){
  var _1Q/* s1Hm */ = E(_1O/* s1Hk */);
  if(!_1Q/* s1Hm */._){
    var _1R/* s1Hn */ = _1Q/* s1Hm */.a,
    _1S/* s1Ho */ = E(_1P/* s1Hl */);
    if(!_1S/* s1Ho */._){
      var _1T/* s1Hp */ = _1S/* s1Ho */.a;
      return (_1R/* s1Hn */!=_1T/* s1Hp */) ? (_1R/* s1Hn */>_1T/* s1Hp */) ? 2 : 0 : 1;
    }else{
      var _1U/* s1Hw */ = I_compareInt/* EXTERNAL */(_1S/* s1Ho */.a, _1R/* s1Hn */);
      return (_1U/* s1Hw */<=0) ? (_1U/* s1Hw */>=0) ? 1 : 2 : 0;
    }
  }else{
    var _1V/* s1HB */ = _1Q/* s1Hm */.a,
    _1W/* s1HC */ = E(_1P/* s1Hl */);
    if(!_1W/* s1HC */._){
      var _1X/* s1HF */ = I_compareInt/* EXTERNAL */(_1V/* s1HB */, _1W/* s1HC */.a);
      return (_1X/* s1HF */>=0) ? (_1X/* s1HF */<=0) ? 1 : 2 : 0;
    }else{
      var _1Y/* s1HM */ = I_compare/* EXTERNAL */(_1V/* s1HB */, _1W/* s1HC */.a);
      return (_1Y/* s1HM */>=0) ? (_1Y/* s1HM */<=0) ? 1 : 2 : 0;
    }
  }
},
_1Z/* $fExceptionArithException_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_20/* $fExceptionArithException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.Exception"));
}),
_21/* $fExceptionArithException_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ArithException"));
}),
_22/* $fExceptionArithException_wild */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_1Z/* GHC.Exception.$fExceptionArithException_ww2 */,_20/* GHC.Exception.$fExceptionArithException_ww4 */,_21/* GHC.Exception.$fExceptionArithException_ww5 */),
_23/* $fExceptionArithException8 */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_22/* GHC.Exception.$fExceptionArithException_wild */,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_24/* $fExceptionArithException7 */ = function(_25/* s2VcG */){
  return E(_23/* GHC.Exception.$fExceptionArithException8 */);
},
_26/* $p1Exception */ = function(_27/* s2V9U */){
  return E(E(_27/* s2V9U */).a);
},
_28/* cast */ = function(_29/* s295g */, _2a/* s295h */, _2b/* s295i */){
  var _2c/* s295j */ = B(A1(_29/* s295g */,_/* EXTERNAL */)),
  _2d/* s295p */ = B(A1(_2a/* s295h */,_/* EXTERNAL */)),
  _2e/* s295w */ = hs_eqWord64/* EXTERNAL */(_2c/* s295j */.a, _2d/* s295p */.a);
  if(!_2e/* s295w */){
    return __Z/* EXTERNAL */;
  }else{
    var _2f/* s295B */ = hs_eqWord64/* EXTERNAL */(_2c/* s295j */.b, _2d/* s295p */.b);
    return (!_2f/* s295B */) ? __Z/* EXTERNAL */ : new T1(1,_2b/* s295i */);
  }
},
_2g/* $fExceptionArithException_$cfromException */ = function(_2h/* s2VcH */){
  var _2i/* s2VcI */ = E(_2h/* s2VcH */);
  return new F(function(){return _28/* Data.Typeable.cast */(B(_26/* GHC.Exception.$p1Exception */(_2i/* s2VcI */.a)), _24/* GHC.Exception.$fExceptionArithException7 */, _2i/* s2VcI */.b);});
},
_2j/* $fExceptionArithException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ratio has zero denominator"));
}),
_2k/* $fExceptionArithException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("denormal"));
}),
_2l/* $fExceptionArithException3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("divide by zero"));
}),
_2m/* $fExceptionArithException4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("loss of precision"));
}),
_2n/* $fExceptionArithException5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic underflow"));
}),
_2o/* $fExceptionArithException6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic overflow"));
}),
_2p/* $w$cshowsPrec */ = function(_2q/* s2VaQ */, _2r/* s2VaR */){
  switch(E(_2q/* s2VaQ */)){
    case 0:
      return new F(function(){return _f/* GHC.Base.++ */(_2o/* GHC.Exception.$fExceptionArithException6 */, _2r/* s2VaR */);});
      break;
    case 1:
      return new F(function(){return _f/* GHC.Base.++ */(_2n/* GHC.Exception.$fExceptionArithException5 */, _2r/* s2VaR */);});
      break;
    case 2:
      return new F(function(){return _f/* GHC.Base.++ */(_2m/* GHC.Exception.$fExceptionArithException4 */, _2r/* s2VaR */);});
      break;
    case 3:
      return new F(function(){return _f/* GHC.Base.++ */(_2l/* GHC.Exception.$fExceptionArithException3 */, _2r/* s2VaR */);});
      break;
    case 4:
      return new F(function(){return _f/* GHC.Base.++ */(_2k/* GHC.Exception.$fExceptionArithException2 */, _2r/* s2VaR */);});
      break;
    default:
      return new F(function(){return _f/* GHC.Base.++ */(_2j/* GHC.Exception.$fExceptionArithException1 */, _2r/* s2VaR */);});
  }
},
_2s/* $fExceptionArithException_$cshow */ = function(_2t/* s2VaY */){
  return new F(function(){return _2p/* GHC.Exception.$w$cshowsPrec */(_2t/* s2VaY */, _o/* GHC.Types.[] */);});
},
_2u/* $fExceptionArithException_$cshowsPrec */ = function(_2v/* s2VaT */, _2w/* s2VaU */, _2x/* s2VaV */){
  return new F(function(){return _2p/* GHC.Exception.$w$cshowsPrec */(_2w/* s2VaU */, _2x/* s2VaV */);});
},
_2y/* showList__1 */ = 44,
_2z/* showList__2 */ = 93,
_2A/* showList__3 */ = 91,
_2B/* showList__ */ = function(_2C/* sf7e */, _2D/* sf7f */, _2E/* sf7g */){
  var _2F/* sf7h */ = E(_2D/* sf7f */);
  if(!_2F/* sf7h */._){
    return new F(function(){return unAppCStr/* EXTERNAL */("[]", _2E/* sf7g */);});
  }else{
    var _2G/* sf7t */ = new T(function(){
      var _2H/* sf7s */ = new T(function(){
        var _2I/* sf7l */ = function(_2J/* sf7m */){
          var _2K/* sf7n */ = E(_2J/* sf7m */);
          if(!_2K/* sf7n */._){
            return E(new T2(1,_2z/* GHC.Show.showList__2 */,_2E/* sf7g */));
          }else{
            var _2L/* sf7r */ = new T(function(){
              return B(A2(_2C/* sf7e */,_2K/* sf7n */.a, new T(function(){
                return B(_2I/* sf7l */(_2K/* sf7n */.b));
              })));
            });
            return new T2(1,_2y/* GHC.Show.showList__1 */,_2L/* sf7r */);
          }
        };
        return B(_2I/* sf7l */(_2F/* sf7h */.b));
      });
      return B(A2(_2C/* sf7e */,_2F/* sf7h */.a, _2H/* sf7s */));
    });
    return new T2(1,_2A/* GHC.Show.showList__3 */,_2G/* sf7t */);
  }
},
_2M/* $fShowArithException_$cshowList */ = function(_2N/* s2VaW */, _2O/* s2VaX */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_2p/* GHC.Exception.$w$cshowsPrec */, _2N/* s2VaW */, _2O/* s2VaX */);});
},
_2P/* $fShowArithException */ = new T3(0,_2u/* GHC.Exception.$fExceptionArithException_$cshowsPrec */,_2s/* GHC.Exception.$fExceptionArithException_$cshow */,_2M/* GHC.Exception.$fShowArithException_$cshowList */),
_2Q/* $fExceptionArithException */ = new T(function(){
  return new T5(0,_24/* GHC.Exception.$fExceptionArithException7 */,_2P/* GHC.Exception.$fShowArithException */,_2R/* GHC.Exception.$fExceptionArithException_$ctoException */,_2g/* GHC.Exception.$fExceptionArithException_$cfromException */,_2s/* GHC.Exception.$fExceptionArithException_$cshow */);
}),
_2R/* $fExceptionArithException_$ctoException */ = function(_2S/* B1 */){
  return new T2(0,_2Q/* GHC.Exception.$fExceptionArithException */,_2S/* B1 */);
},
_2T/* DivideByZero */ = 3,
_2U/* divZeroException */ = new T(function(){
  return B(_2R/* GHC.Exception.$fExceptionArithException_$ctoException */(_2T/* GHC.Exception.DivideByZero */));
}),
_2V/* divZeroError */ = new T(function(){
  return die/* EXTERNAL */(_2U/* GHC.Exception.divZeroException */);
}),
_2W/* encodeDoubleInteger */ = function(_2X/* s1LC */, _2Y/* s1LD */){
  var _2Z/* s1LE */ = E(_2X/* s1LC */);
  return (_2Z/* s1LE */._==0) ? _2Z/* s1LE */.a*Math.pow/* EXTERNAL */(2, _2Y/* s1LD */) : I_toNumber/* EXTERNAL */(_2Z/* s1LE */.a)*Math.pow/* EXTERNAL */(2, _2Y/* s1LD */);
},
_30/* eqInteger */ = function(_31/* s1Fo */, _32/* s1Fp */){
  var _33/* s1Fq */ = E(_31/* s1Fo */);
  if(!_33/* s1Fq */._){
    var _34/* s1Fr */ = _33/* s1Fq */.a,
    _35/* s1Fs */ = E(_32/* s1Fp */);
    return (_35/* s1Fs */._==0) ? _34/* s1Fr */==_35/* s1Fs */.a : (I_compareInt/* EXTERNAL */(_35/* s1Fs */.a, _34/* s1Fr */)==0) ? true : false;
  }else{
    var _36/* s1Fy */ = _33/* s1Fq */.a,
    _37/* s1Fz */ = E(_32/* s1Fp */);
    return (_37/* s1Fz */._==0) ? (I_compareInt/* EXTERNAL */(_36/* s1Fy */, _37/* s1Fz */.a)==0) ? true : false : (I_compare/* EXTERNAL */(_36/* s1Fy */, _37/* s1Fz */.a)==0) ? true : false;
  }
},
_38/* integerToInt */ = function(_39/* s1Rv */){
  var _3a/* s1Rw */ = E(_39/* s1Rv */);
  if(!_3a/* s1Rw */._){
    return E(_3a/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_3a/* s1Rw */.a);});
  }
},
_3b/* plusInteger */ = function(_3c/* s1Qe */, _3d/* s1Qf */){
  while(1){
    var _3e/* s1Qg */ = E(_3c/* s1Qe */);
    if(!_3e/* s1Qg */._){
      var _3f/* s1Qh */ = _3e/* s1Qg */.a,
      _3g/* s1Qi */ = E(_3d/* s1Qf */);
      if(!_3g/* s1Qi */._){
        var _3h/* s1Qj */ = _3g/* s1Qi */.a,
        _3i/* s1Qk */ = addC/* EXTERNAL */(_3f/* s1Qh */, _3h/* s1Qj */);
        if(!E(_3i/* s1Qk */.b)){
          return new T1(0,_3i/* s1Qk */.a);
        }else{
          _3c/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_3f/* s1Qh */));
          _3d/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_3h/* s1Qj */));
          continue;
        }
      }else{
        _3c/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_3f/* s1Qh */));
        _3d/* s1Qf */ = _3g/* s1Qi */;
        continue;
      }
    }else{
      var _3j/* s1Qz */ = E(_3d/* s1Qf */);
      if(!_3j/* s1Qz */._){
        _3c/* s1Qe */ = _3e/* s1Qg */;
        _3d/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_3j/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_3e/* s1Qg */.a, _3j/* s1Qz */.a));
      }
    }
  }
},
_3k/* quotRemInteger */ = function(_3l/* s1Ma */, _3m/* s1Mb */){
  while(1){
    var _3n/* s1Mc */ = E(_3l/* s1Ma */);
    if(!_3n/* s1Mc */._){
      var _3o/* s1Me */ = E(_3n/* s1Mc */.a);
      if(_3o/* s1Me */==( -2147483648)){
        _3l/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _3p/* s1Mf */ = E(_3m/* s1Mb */);
        if(!_3p/* s1Mf */._){
          var _3q/* s1Mg */ = _3p/* s1Mf */.a;
          return new T2(0,new T1(0,quot/* EXTERNAL */(_3o/* s1Me */, _3q/* s1Mg */)),new T1(0,_3o/* s1Me */%_3q/* s1Mg */));
        }else{
          _3l/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(_3o/* s1Me */));
          _3m/* s1Mb */ = _3p/* s1Mf */;
          continue;
        }
      }
    }else{
      var _3r/* s1Mt */ = E(_3m/* s1Mb */);
      if(!_3r/* s1Mt */._){
        _3l/* s1Ma */ = _3n/* s1Mc */;
        _3m/* s1Mb */ = new T1(1,I_fromInt/* EXTERNAL */(_3r/* s1Mt */.a));
        continue;
      }else{
        var _3s/* s1MA */ = I_quotRem/* EXTERNAL */(_3n/* s1Mc */.a, _3r/* s1Mt */.a);
        return new T2(0,new T1(1,_3s/* s1MA */.a),new T1(1,_3s/* s1MA */.b));
      }
    }
  }
},
_3t/* rationalToDouble5 */ = new T1(0,0),
_3u/* shiftLInteger */ = function(_3v/* s1Jk */, _3w/* s1Jl */){
  while(1){
    var _3x/* s1Jm */ = E(_3v/* s1Jk */);
    if(!_3x/* s1Jm */._){
      _3v/* s1Jk */ = new T1(1,I_fromInt/* EXTERNAL */(_3x/* s1Jm */.a));
      continue;
    }else{
      return new T1(1,I_shiftLeft/* EXTERNAL */(_3x/* s1Jm */.a, _3w/* s1Jl */));
    }
  }
},
_3y/* $w$j1 */ = function(_3z/* s1kWp */, _3A/* s1kWq */, _3B/* s1kWr */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_3B/* s1kWr */, _3t/* GHC.Float.rationalToDouble5 */))){
    var _3C/* s1kWt */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_3A/* s1kWq */, _3B/* s1kWr */)),
    _3D/* s1kWu */ = _3C/* s1kWt */.a;
    switch(B(_1N/* GHC.Integer.Type.compareInteger */(B(_3u/* GHC.Integer.Type.shiftLInteger */(_3C/* s1kWt */.b, 1)), _3B/* s1kWr */))){
      case 0:
        return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_3D/* s1kWu */, _3z/* s1kWp */);});
        break;
      case 1:
        if(!(B(_38/* GHC.Integer.Type.integerToInt */(_3D/* s1kWu */))&1)){
          return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_3D/* s1kWu */, _3z/* s1kWp */);});
        }else{
          return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_3D/* s1kWu */, _1M/* GHC.Float.$fRealDouble1 */)), _3z/* s1kWp */);});
        }
        break;
      default:
        return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_3D/* s1kWu */, _1M/* GHC.Float.$fRealDouble1 */)), _3z/* s1kWp */);});
    }
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_3E/* gtInteger */ = function(_3F/* s1G1 */, _3G/* s1G2 */){
  var _3H/* s1G3 */ = E(_3F/* s1G1 */);
  if(!_3H/* s1G3 */._){
    var _3I/* s1G4 */ = _3H/* s1G3 */.a,
    _3J/* s1G5 */ = E(_3G/* s1G2 */);
    return (_3J/* s1G5 */._==0) ? _3I/* s1G4 */>_3J/* s1G5 */.a : I_compareInt/* EXTERNAL */(_3J/* s1G5 */.a, _3I/* s1G4 */)<0;
  }else{
    var _3K/* s1Gc */ = _3H/* s1G3 */.a,
    _3L/* s1Gd */ = E(_3G/* s1G2 */);
    return (_3L/* s1Gd */._==0) ? I_compareInt/* EXTERNAL */(_3K/* s1Gc */, _3L/* s1Gd */.a)>0 : I_compare/* EXTERNAL */(_3K/* s1Gc */, _3L/* s1Gd */.a)>0;
  }
},
_3M/* log2I1 */ = new T1(0,1),
_3N/* ltInteger */ = function(_3O/* s1GH */, _3P/* s1GI */){
  var _3Q/* s1GJ */ = E(_3O/* s1GH */);
  if(!_3Q/* s1GJ */._){
    var _3R/* s1GK */ = _3Q/* s1GJ */.a,
    _3S/* s1GL */ = E(_3P/* s1GI */);
    return (_3S/* s1GL */._==0) ? _3R/* s1GK */<_3S/* s1GL */.a : I_compareInt/* EXTERNAL */(_3S/* s1GL */.a, _3R/* s1GK */)>0;
  }else{
    var _3T/* s1GS */ = _3Q/* s1GJ */.a,
    _3U/* s1GT */ = E(_3P/* s1GI */);
    return (_3U/* s1GT */._==0) ? I_compareInt/* EXTERNAL */(_3T/* s1GS */, _3U/* s1GT */.a)<0 : I_compare/* EXTERNAL */(_3T/* s1GS */, _3U/* s1GT */.a)<0;
  }
},
_3V/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_3W/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_3X/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_3Y/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_3V/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_3W/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_3X/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_3Z/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_3Y/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_40/* $fExceptionPatternMatchFail1 */ = function(_41/* s4EcJ */){
  return E(_3Z/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_42/* $fExceptionPatternMatchFail_$cfromException */ = function(_43/* s4EcY */){
  var _44/* s4EcZ */ = E(_43/* s4EcY */);
  return new F(function(){return _28/* Data.Typeable.cast */(B(_26/* GHC.Exception.$p1Exception */(_44/* s4EcZ */.a)), _40/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _44/* s4EcZ */.b);});
},
_45/* $fExceptionPatternMatchFail_$cshow */ = function(_46/* s4EcV */){
  return E(E(_46/* s4EcV */).a);
},
_47/* $fExceptionPatternMatchFail_$ctoException */ = function(_48/* B1 */){
  return new T2(0,_49/* Control.Exception.Base.$fExceptionPatternMatchFail */,_48/* B1 */);
},
_4a/* $fShowPatternMatchFail1 */ = function(_4b/* s4EcP */, _4c/* s4EcQ */){
  return new F(function(){return _f/* GHC.Base.++ */(E(_4b/* s4EcP */).a, _4c/* s4EcQ */);});
},
_4d/* $fShowPatternMatchFail_$cshowList */ = function(_4e/* s4EcT */, _4f/* s4EcU */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_4a/* Control.Exception.Base.$fShowPatternMatchFail1 */, _4e/* s4EcT */, _4f/* s4EcU */);});
},
_4g/* $fShowPatternMatchFail_$cshowsPrec */ = function(_4h/* s4EcK */, _4i/* s4EcL */, _4j/* s4EcM */){
  return new F(function(){return _f/* GHC.Base.++ */(E(_4i/* s4EcL */).a, _4j/* s4EcM */);});
},
_4k/* $fShowPatternMatchFail */ = new T3(0,_4g/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_45/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_4d/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_49/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_40/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_4k/* Control.Exception.Base.$fShowPatternMatchFail */,_47/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_42/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_45/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_4l/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_4m/* toException */ = function(_4n/* s2Va8 */){
  return E(E(_4n/* s2Va8 */).c);
},
_4o/* lvl */ = function(_4p/* s2Vcp */, _4q/* s2Vcq */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_4m/* GHC.Exception.toException */,_4q/* s2Vcq */, _4p/* s2Vcp */));
  }));});
},
_4r/* throw1 */ = function(_4s/* B2 */, _2S/* B1 */){
  return new F(function(){return _4o/* GHC.Exception.lvl */(_4s/* B2 */, _2S/* B1 */);});
},
_4t/* $wspan */ = function(_4u/* sbH9 */, _4v/* sbHa */){
  var _4w/* sbHb */ = E(_4v/* sbHa */);
  if(!_4w/* sbHb */._){
    return new T2(0,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */);
  }else{
    var _4x/* sbHc */ = _4w/* sbHb */.a;
    if(!B(A1(_4u/* sbH9 */,_4x/* sbHc */))){
      return new T2(0,_o/* GHC.Types.[] */,_4w/* sbHb */);
    }else{
      var _4y/* sbHf */ = new T(function(){
        var _4z/* sbHg */ = B(_4t/* GHC.List.$wspan */(_4u/* sbH9 */, _4w/* sbHb */.b));
        return new T2(0,_4z/* sbHg */.a,_4z/* sbHg */.b);
      });
      return new T2(0,new T2(1,_4x/* sbHc */,new T(function(){
        return E(E(_4y/* sbHf */).a);
      })),new T(function(){
        return E(E(_4y/* sbHf */).b);
      }));
    }
  }
},
_4A/* untangle1 */ = 32,
_4B/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_4C/* untangle3 */ = function(_4D/* s3N7b */){
  return (E(_4D/* s3N7b */)==124) ? false : true;
},
_4E/* untangle */ = function(_4F/* s3N7f */, _4G/* s3N7g */){
  var _4H/* s3N7i */ = B(_4t/* GHC.List.$wspan */(_4C/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_4F/* s3N7f */)))),
  _4I/* s3N7j */ = _4H/* s3N7i */.a,
  _4J/* s3N7l */ = function(_4K/* s3N7m */, _4L/* s3N7n */){
    var _4M/* s3N7q */ = new T(function(){
      var _4N/* s3N7p */ = new T(function(){
        return B(_f/* GHC.Base.++ */(_4G/* s3N7g */, new T(function(){
          return B(_f/* GHC.Base.++ */(_4L/* s3N7n */, _4B/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _4N/* s3N7p */));
    },1);
    return new F(function(){return _f/* GHC.Base.++ */(_4K/* s3N7m */, _4M/* s3N7q */);});
  },
  _4O/* s3N7r */ = E(_4H/* s3N7i */.b);
  if(!_4O/* s3N7r */._){
    return new F(function(){return _4J/* s3N7l */(_4I/* s3N7j */, _o/* GHC.Types.[] */);});
  }else{
    if(E(_4O/* s3N7r */.a)==124){
      return new F(function(){return _4J/* s3N7l */(_4I/* s3N7j */, new T2(1,_4A/* GHC.IO.Exception.untangle1 */,_4O/* s3N7r */.b));});
    }else{
      return new F(function(){return _4J/* s3N7l */(_4I/* s3N7j */, _o/* GHC.Types.[] */);});
    }
  }
},
_4P/* patError */ = function(_4Q/* s4EiE */){
  return new F(function(){return _4r/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_4E/* GHC.IO.Exception.untangle */(_4Q/* s4EiE */, _4l/* Control.Exception.Base.lvl5 */));
  })), _49/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_4R/* log2I */ = function(_4S/* s1Ju */){
  var _4T/* s1Jv */ = function(_4U/* s1Jw */, _4V/* s1Jx */){
    while(1){
      if(!B(_3N/* GHC.Integer.Type.ltInteger */(_4U/* s1Jw */, _4S/* s1Ju */))){
        if(!B(_3E/* GHC.Integer.Type.gtInteger */(_4U/* s1Jw */, _4S/* s1Ju */))){
          if(!B(_30/* GHC.Integer.Type.eqInteger */(_4U/* s1Jw */, _4S/* s1Ju */))){
            return new F(function(){return _4P/* Control.Exception.Base.patError */("GHC\\Integer\\Type.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_4V/* s1Jx */);
          }
        }else{
          return _4V/* s1Jx */-1|0;
        }
      }else{
        var _4W/*  s1Jw */ = B(_3u/* GHC.Integer.Type.shiftLInteger */(_4U/* s1Jw */, 1)),
        _4X/*  s1Jx */ = _4V/* s1Jx */+1|0;
        _4U/* s1Jw */ = _4W/*  s1Jw */;
        _4V/* s1Jx */ = _4X/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _4T/* s1Jv */(_3M/* GHC.Integer.Type.log2I1 */, 0);});
},
_4Y/* integerLog2# */ = function(_4Z/* s1JD */){
  var _50/* s1JE */ = E(_4Z/* s1JD */);
  if(!_50/* s1JE */._){
    var _51/* s1JG */ = _50/* s1JE */.a>>>0;
    if(!_51/* s1JG */){
      return  -1;
    }else{
      var _52/* s1JH */ = function(_53/* s1JI */, _54/* s1JJ */){
        while(1){
          if(_53/* s1JI */>=_51/* s1JG */){
            if(_53/* s1JI */<=_51/* s1JG */){
              if(_53/* s1JI */!=_51/* s1JG */){
                return new F(function(){return _4P/* Control.Exception.Base.patError */("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_54/* s1JJ */);
              }
            }else{
              return _54/* s1JJ */-1|0;
            }
          }else{
            var _55/*  s1JI */ = imul/* EXTERNAL */(_53/* s1JI */, 2)>>>0,
            _56/*  s1JJ */ = _54/* s1JJ */+1|0;
            _53/* s1JI */ = _55/*  s1JI */;
            _54/* s1JJ */ = _56/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _52/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _4R/* GHC.Integer.Type.log2I */(_50/* s1JE */);});
  }
},
_57/* integerLog2IsPowerOf2# */ = function(_58/* s1JT */){
  var _59/* s1JU */ = E(_58/* s1JT */);
  if(!_59/* s1JU */._){
    var _5a/* s1JW */ = _59/* s1JU */.a>>>0;
    if(!_5a/* s1JW */){
      return new T2(0, -1,0);
    }else{
      var _5b/* s1JX */ = function(_5c/* s1JY */, _5d/* s1JZ */){
        while(1){
          if(_5c/* s1JY */>=_5a/* s1JW */){
            if(_5c/* s1JY */<=_5a/* s1JW */){
              if(_5c/* s1JY */!=_5a/* s1JW */){
                return new F(function(){return _4P/* Control.Exception.Base.patError */("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_5d/* s1JZ */);
              }
            }else{
              return _5d/* s1JZ */-1|0;
            }
          }else{
            var _5e/*  s1JY */ = imul/* EXTERNAL */(_5c/* s1JY */, 2)>>>0,
            _5f/*  s1JZ */ = _5d/* s1JZ */+1|0;
            _5c/* s1JY */ = _5e/*  s1JY */;
            _5d/* s1JZ */ = _5f/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_5b/* s1JX */(1, 0)),(_5a/* s1JW */&_5a/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _5g/* s1Kc */ = _59/* s1JU */.a;
    return new T2(0,B(_4Y/* GHC.Integer.Type.integerLog2# */(_59/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_5g/* s1Kc */, I_sub/* EXTERNAL */(_5g/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_5h/* leInteger */ = function(_5i/* s1Gm */, _5j/* s1Gn */){
  var _5k/* s1Go */ = E(_5i/* s1Gm */);
  if(!_5k/* s1Go */._){
    var _5l/* s1Gp */ = _5k/* s1Go */.a,
    _5m/* s1Gq */ = E(_5j/* s1Gn */);
    return (_5m/* s1Gq */._==0) ? _5l/* s1Gp */<=_5m/* s1Gq */.a : I_compareInt/* EXTERNAL */(_5m/* s1Gq */.a, _5l/* s1Gp */)>=0;
  }else{
    var _5n/* s1Gx */ = _5k/* s1Go */.a,
    _5o/* s1Gy */ = E(_5j/* s1Gn */);
    return (_5o/* s1Gy */._==0) ? I_compareInt/* EXTERNAL */(_5n/* s1Gx */, _5o/* s1Gy */.a)<=0 : I_compare/* EXTERNAL */(_5n/* s1Gx */, _5o/* s1Gy */.a)<=0;
  }
},
_5p/* andInteger */ = function(_5q/* s1Lf */, _5r/* s1Lg */){
  while(1){
    var _5s/* s1Lh */ = E(_5q/* s1Lf */);
    if(!_5s/* s1Lh */._){
      var _5t/* s1Li */ = _5s/* s1Lh */.a,
      _5u/* s1Lj */ = E(_5r/* s1Lg */);
      if(!_5u/* s1Lj */._){
        return new T1(0,(_5t/* s1Li */>>>0&_5u/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _5q/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_5t/* s1Li */));
        _5r/* s1Lg */ = _5u/* s1Lj */;
        continue;
      }
    }else{
      var _5v/* s1Lu */ = E(_5r/* s1Lg */);
      if(!_5v/* s1Lu */._){
        _5q/* s1Lf */ = _5s/* s1Lh */;
        _5r/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_5v/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_5s/* s1Lh */.a, _5v/* s1Lu */.a));
      }
    }
  }
},
_5w/* minusInteger */ = function(_5x/* s1P0 */, _5y/* s1P1 */){
  while(1){
    var _5z/* s1P2 */ = E(_5x/* s1P0 */);
    if(!_5z/* s1P2 */._){
      var _5A/* s1P3 */ = _5z/* s1P2 */.a,
      _5B/* s1P4 */ = E(_5y/* s1P1 */);
      if(!_5B/* s1P4 */._){
        var _5C/* s1P5 */ = _5B/* s1P4 */.a,
        _5D/* s1P6 */ = subC/* EXTERNAL */(_5A/* s1P3 */, _5C/* s1P5 */);
        if(!E(_5D/* s1P6 */.b)){
          return new T1(0,_5D/* s1P6 */.a);
        }else{
          _5x/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_5A/* s1P3 */));
          _5y/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_5C/* s1P5 */));
          continue;
        }
      }else{
        _5x/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_5A/* s1P3 */));
        _5y/* s1P1 */ = _5B/* s1P4 */;
        continue;
      }
    }else{
      var _5E/* s1Pl */ = E(_5y/* s1P1 */);
      if(!_5E/* s1Pl */._){
        _5x/* s1P0 */ = _5z/* s1P2 */;
        _5y/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_5E/* s1Pl */.a));
        continue;
      }else{
        return new T1(1,I_sub/* EXTERNAL */(_5z/* s1P2 */.a, _5E/* s1Pl */.a));
      }
    }
  }
},
_5F/* roundingMode#1 */ = new T1(0,2),
_5G/* roundingMode# */ = function(_5H/* s1Pt */, _5I/* s1Pu */){
  var _5J/* s1Pv */ = E(_5H/* s1Pt */);
  if(!_5J/* s1Pv */._){
    var _5K/* s1Px */ = (_5J/* s1Pv */.a>>>0&(2<<_5I/* s1Pu */>>>0)-1>>>0)>>>0,
    _5L/* s1PB */ = 1<<_5I/* s1Pu */>>>0;
    return (_5L/* s1PB */<=_5K/* s1Px */) ? (_5L/* s1PB */>=_5K/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _5M/* s1PH */ = B(_5p/* GHC.Integer.Type.andInteger */(_5J/* s1Pv */, B(_5w/* GHC.Integer.Type.minusInteger */(B(_3u/* GHC.Integer.Type.shiftLInteger */(_5F/* GHC.Integer.Type.roundingMode#1 */, _5I/* s1Pu */)), _3M/* GHC.Integer.Type.log2I1 */)))),
    _5N/* s1PK */ = B(_3u/* GHC.Integer.Type.shiftLInteger */(_3M/* GHC.Integer.Type.log2I1 */, _5I/* s1Pu */));
    return (!B(_3E/* GHC.Integer.Type.gtInteger */(_5N/* s1PK */, _5M/* s1PH */))) ? (!B(_3N/* GHC.Integer.Type.ltInteger */(_5N/* s1PK */, _5M/* s1PH */))) ? 1 : 2 : 0;
  }
},
_5O/* shiftRInteger */ = function(_5P/* s1Ja */, _5Q/* s1Jb */){
  while(1){
    var _5R/* s1Jc */ = E(_5P/* s1Ja */);
    if(!_5R/* s1Jc */._){
      _5P/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_5R/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_5R/* s1Jc */.a, _5Q/* s1Jb */));
    }
  }
},
_5S/* $w$sfromRat'' */ = function(_5T/* s1kWD */, _5U/* s1kWE */, _5V/* s1kWF */, _5W/* s1kWG */){
  var _5X/* s1kWH */ = B(_57/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_5W/* s1kWG */)),
  _5Y/* s1kWI */ = _5X/* s1kWH */.a;
  if(!E(_5X/* s1kWH */.b)){
    var _5Z/* s1kX8 */ = B(_4Y/* GHC.Integer.Type.integerLog2# */(_5V/* s1kWF */));
    if(_5Z/* s1kX8 */<((_5Y/* s1kWI */+_5T/* s1kWD */|0)-1|0)){
      var _60/* s1kXd */ = _5Y/* s1kWI */+(_5T/* s1kWD */-_5U/* s1kWE */|0)|0;
      if(_60/* s1kXd */>0){
        if(_60/* s1kXd */>_5Z/* s1kX8 */){
          if(_60/* s1kXd */<=(_5Z/* s1kX8 */+1|0)){
            if(!E(B(_57/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_5V/* s1kWF */)).b)){
              return 0;
            }else{
              return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_1M/* GHC.Float.$fRealDouble1 */, _5T/* s1kWD */-_5U/* s1kWE */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _61/* s1kXr */ = B(_5O/* GHC.Integer.Type.shiftRInteger */(_5V/* s1kWF */, _60/* s1kXd */));
          switch(B(_5G/* GHC.Integer.Type.roundingMode# */(_5V/* s1kWF */, _60/* s1kXd */-1|0))){
            case 0:
              return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_61/* s1kXr */, _5T/* s1kWD */-_5U/* s1kWE */|0);});
              break;
            case 1:
              if(!(B(_38/* GHC.Integer.Type.integerToInt */(_61/* s1kXr */))&1)){
                return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_61/* s1kXr */, _5T/* s1kWD */-_5U/* s1kWE */|0);});
              }else{
                return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_61/* s1kXr */, _1M/* GHC.Float.$fRealDouble1 */)), _5T/* s1kWD */-_5U/* s1kWE */|0);});
              }
              break;
            default:
              return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_61/* s1kXr */, _1M/* GHC.Float.$fRealDouble1 */)), _5T/* s1kWD */-_5U/* s1kWE */|0);});
          }
        }
      }else{
        return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_5V/* s1kWF */, (_5T/* s1kWD */-_5U/* s1kWE */|0)-_60/* s1kXd */|0);});
      }
    }else{
      if(_5Z/* s1kX8 */>=_5U/* s1kWE */){
        var _62/* s1kXG */ = B(_5O/* GHC.Integer.Type.shiftRInteger */(_5V/* s1kWF */, (_5Z/* s1kX8 */+1|0)-_5U/* s1kWE */|0));
        switch(B(_5G/* GHC.Integer.Type.roundingMode# */(_5V/* s1kWF */, _5Z/* s1kX8 */-_5U/* s1kWE */|0))){
          case 0:
            return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_62/* s1kXG */, ((_5Z/* s1kX8 */-_5Y/* s1kWI */|0)+1|0)-_5U/* s1kWE */|0);});
            break;
          case 2:
            return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_62/* s1kXG */, _1M/* GHC.Float.$fRealDouble1 */)), ((_5Z/* s1kX8 */-_5Y/* s1kWI */|0)+1|0)-_5U/* s1kWE */|0);});
            break;
          default:
            if(!(B(_38/* GHC.Integer.Type.integerToInt */(_62/* s1kXG */))&1)){
              return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_62/* s1kXG */, ((_5Z/* s1kX8 */-_5Y/* s1kWI */|0)+1|0)-_5U/* s1kWE */|0);});
            }else{
              return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_62/* s1kXG */, _1M/* GHC.Float.$fRealDouble1 */)), ((_5Z/* s1kX8 */-_5Y/* s1kWI */|0)+1|0)-_5U/* s1kWE */|0);});
            }
        }
      }else{
        return new F(function(){return _2W/* GHC.Integer.Type.encodeDoubleInteger */(_5V/* s1kWF */,  -_5Y/* s1kWI */);});
      }
    }
  }else{
    var _63/* s1kWM */ = B(_4Y/* GHC.Integer.Type.integerLog2# */(_5V/* s1kWF */))-_5Y/* s1kWI */|0,
    _64/* s1kWN */ = function(_65/* s1kWO */){
      var _66/* s1kWP */ = function(_67/* s1kWQ */, _68/* s1kWR */){
        if(!B(_5h/* GHC.Integer.Type.leInteger */(B(_3u/* GHC.Integer.Type.shiftLInteger */(_68/* s1kWR */, _5U/* s1kWE */)), _67/* s1kWQ */))){
          return new F(function(){return _3y/* GHC.Float.$w$j1 */(_65/* s1kWO */-_5U/* s1kWE */|0, _67/* s1kWQ */, _68/* s1kWR */);});
        }else{
          return new F(function(){return _3y/* GHC.Float.$w$j1 */((_65/* s1kWO */-_5U/* s1kWE */|0)+1|0, _67/* s1kWQ */, B(_3u/* GHC.Integer.Type.shiftLInteger */(_68/* s1kWR */, 1)));});
        }
      };
      if(_65/* s1kWO */>=_5U/* s1kWE */){
        if(_65/* s1kWO */!=_5U/* s1kWE */){
          return new F(function(){return _66/* s1kWP */(_5V/* s1kWF */, new T(function(){
            return B(_3u/* GHC.Integer.Type.shiftLInteger */(_5W/* s1kWG */, _65/* s1kWO */-_5U/* s1kWE */|0));
          }));});
        }else{
          return new F(function(){return _66/* s1kWP */(_5V/* s1kWF */, _5W/* s1kWG */);});
        }
      }else{
        return new F(function(){return _66/* s1kWP */(new T(function(){
          return B(_3u/* GHC.Integer.Type.shiftLInteger */(_5V/* s1kWF */, _5U/* s1kWE */-_65/* s1kWO */|0));
        }), _5W/* s1kWG */);});
      }
    };
    if(_5T/* s1kWD */>_63/* s1kWM */){
      return new F(function(){return _64/* s1kWN */(_5T/* s1kWD */);});
    }else{
      return new F(function(){return _64/* s1kWN */(_63/* s1kWM */);});
    }
  }
},
_69/* lvl2 */ = new T1(0,2147483647),
_6a/* lvl3 */ = new T(function(){
  return B(_3b/* GHC.Integer.Type.plusInteger */(_69/* GHC.Integer.Type.lvl2 */, _3M/* GHC.Integer.Type.log2I1 */));
}),
_6b/* negateInteger */ = function(_6c/* s1QH */){
  var _6d/* s1QI */ = E(_6c/* s1QH */);
  if(!_6d/* s1QI */._){
    var _6e/* s1QK */ = E(_6d/* s1QI */.a);
    return (_6e/* s1QK */==( -2147483648)) ? E(_6a/* GHC.Integer.Type.lvl3 */) : new T1(0, -_6e/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_6d/* s1QI */.a));
  }
},
_6f/* rationalToDouble1 */ = new T(function(){
  return 0/0;
}),
_6g/* rationalToDouble2 */ = new T(function(){
  return  -1/0;
}),
_6h/* rationalToDouble3 */ = new T(function(){
  return 1/0;
}),
_6i/* rationalToDouble4 */ = 0,
_6j/* rationalToDouble */ = function(_6k/* s1ldn */, _6l/* s1ldo */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_6l/* s1ldo */, _3t/* GHC.Float.rationalToDouble5 */))){
    if(!B(_30/* GHC.Integer.Type.eqInteger */(_6k/* s1ldn */, _3t/* GHC.Float.rationalToDouble5 */))){
      if(!B(_3N/* GHC.Integer.Type.ltInteger */(_6k/* s1ldn */, _3t/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _5S/* GHC.Float.$w$sfromRat'' */( -1021, 53, _6k/* s1ldn */, _6l/* s1ldo */);});
      }else{
        return  -B(_5S/* GHC.Float.$w$sfromRat'' */( -1021, 53, B(_6b/* GHC.Integer.Type.negateInteger */(_6k/* s1ldn */)), _6l/* s1ldo */));
      }
    }else{
      return E(_6i/* GHC.Float.rationalToDouble4 */);
    }
  }else{
    return (!B(_30/* GHC.Integer.Type.eqInteger */(_6k/* s1ldn */, _3t/* GHC.Float.rationalToDouble5 */))) ? (!B(_3N/* GHC.Integer.Type.ltInteger */(_6k/* s1ldn */, _3t/* GHC.Float.rationalToDouble5 */))) ? E(_6h/* GHC.Float.rationalToDouble3 */) : E(_6g/* GHC.Float.rationalToDouble2 */) : E(_6f/* GHC.Float.rationalToDouble1 */);
  }
},
_6m/* $fFractionalVar_$cfromRational */ = function(_6n/* s7yO */){
  return new T1(0,new T(function(){
    var _6o/* s7yP */ = E(_6n/* s7yO */),
    _6p/* s7yV */ = jsShow/* EXTERNAL */(B(_6j/* GHC.Float.rationalToDouble */(_6o/* s7yP */.a, _6o/* s7yP */.b)));
    return fromJSStr/* EXTERNAL */(_6p/* s7yV */);
  }));
},
_6q/* $fFractionalVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1./("));
}),
_6r/* $fFractionalVar1 */ = new T1(0,_6q/* Lib.Shader.$fFractionalVar2 */),
_6s/* $fFractionalVar_$crecip */ = function(_6t/* s7z0 */){
  return new T1(1,new T2(1,_6r/* Lib.Shader.$fFractionalVar1 */,new T2(1,_6t/* s7z0 */,_w/* Lib.Shader.gradStr3 */)));
},
_6u/* $c+4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")+("));
}),
_6v/* $c+3 */ = new T1(0,_6u/* Lib.Shader.$c+4 */),
_6w/* $c+ */ = function(_6x/* s7yF */, _6y/* s7yG */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_6x/* s7yF */,new T2(1,_6v/* Lib.Shader.$c+3 */,new T2(1,_6y/* s7yG */,_w/* Lib.Shader.gradStr3 */)))));
},
_6z/* $cnegate2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("-("));
}),
_6A/* $cnegate1 */ = new T1(0,_6z/* Lib.Shader.$cnegate2 */),
_6B/* $cnegate */ = function(_6C/* s7yw */){
  return new T1(1,new T2(1,_6A/* Lib.Shader.$cnegate1 */,new T2(1,_6C/* s7yw */,_w/* Lib.Shader.gradStr3 */)));
},
_6D/* $fNumVar6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")*("));
}),
_6E/* $fNumVar5 */ = new T1(0,_6D/* Lib.Shader.$fNumVar6 */),
_6F/* $fNumVar_$c* */ = function(_6G/* s7yz */, _6H/* s7yA */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_6G/* s7yz */,new T2(1,_6E/* Lib.Shader.$fNumVar5 */,new T2(1,_6H/* s7yA */,_w/* Lib.Shader.gradStr3 */)))));
},
_6I/* + */ = function(_6J/* s6Fw */){
  return E(E(_6J/* s6Fw */).a);
},
_6K/* negate */ = function(_6L/* s6FX */){
  return E(E(_6L/* s6FX */).d);
},
_6M/* $fNumVar_$c- */ = function(_6N/* s7yL */, _6O/* s7yM */){
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_6P/* Lib.Shader.$fNumVar */, _6N/* s7yL */, new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_6P/* Lib.Shader.$fNumVar */, _6O/* s7yM */));
  }));});
},
_6Q/* $fNumVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("abs("));
}),
_6R/* $fNumVar3 */ = new T1(0,_6Q/* Lib.Shader.$fNumVar4 */),
_6S/* $fNumVar_$cabs */ = function(_6T/* s7yt */){
  return new T1(1,new T2(1,_6R/* Lib.Shader.$fNumVar3 */,new T2(1,_6T/* s7yt */,_w/* Lib.Shader.gradStr3 */)));
},
_6U/* integerToJSString */ = function(_6V/* s1Ii */){
  while(1){
    var _6W/* s1Ij */ = E(_6V/* s1Ii */);
    if(!_6W/* s1Ij */._){
      _6V/* s1Ii */ = new T1(1,I_fromInt/* EXTERNAL */(_6W/* s1Ij */.a));
      continue;
    }else{
      return new F(function(){return I_toString/* EXTERNAL */(_6W/* s1Ij */.a);});
    }
  }
},
_6X/* integerToString */ = function(_6Y/* sf6p */, _6Z/* sf6q */){
  return new F(function(){return _f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_6U/* GHC.Integer.Type.integerToJSString */(_6Y/* sf6p */))), _6Z/* sf6q */);});
},
_70/* shows7 */ = 41,
_71/* shows8 */ = 40,
_72/* shows9 */ = new T1(0,0),
_73/* $w$cshowsPrec1 */ = function(_74/* sf7E */, _75/* sf7F */, _76/* sf7G */){
  if(_74/* sf7E */<=6){
    return new F(function(){return _6X/* GHC.Show.integerToString */(_75/* sf7F */, _76/* sf7G */);});
  }else{
    if(!B(_3N/* GHC.Integer.Type.ltInteger */(_75/* sf7F */, _72/* GHC.Show.shows9 */))){
      return new F(function(){return _6X/* GHC.Show.integerToString */(_75/* sf7F */, _76/* sf7G */);});
    }else{
      return new T2(1,_71/* GHC.Show.shows8 */,new T(function(){
        return B(_f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(B(_6U/* GHC.Integer.Type.integerToJSString */(_75/* sf7F */))), new T2(1,_70/* GHC.Show.shows7 */,_76/* sf7G */)));
      }));
    }
  }
},
_77/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("."));
}),
_78/* $fNumVar_$cfromInteger */ = function(_79/* s7yn */){
  return new T1(0,new T(function(){
    return B(_f/* GHC.Base.++ */(B(_73/* GHC.Show.$w$cshowsPrec1 */(0, _79/* s7yn */, _o/* GHC.Types.[] */)), _77/* Lib.Shader.lvl4 */));
  }));
},
_7a/* $fNumVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sign("));
}),
_7b/* $fNumVar1 */ = new T1(0,_7a/* Lib.Shader.$fNumVar2 */),
_7c/* $fNumVar_$csignum */ = function(_7d/* s7yq */){
  return new T1(1,new T2(1,_7b/* Lib.Shader.$fNumVar1 */,new T2(1,_7d/* s7yq */,_w/* Lib.Shader.gradStr3 */)));
},
_6P/* $fNumVar */ = new T(function(){
  return {_:0,a:_6w/* Lib.Shader.$c+ */,b:_6M/* Lib.Shader.$fNumVar_$c- */,c:_6F/* Lib.Shader.$fNumVar_$c* */,d:_6B/* Lib.Shader.$cnegate */,e:_6S/* Lib.Shader.$fNumVar_$cabs */,f:_7c/* Lib.Shader.$fNumVar_$csignum */,g:_78/* Lib.Shader.$fNumVar_$cfromInteger */};
}),
_7e/* $fFractionalVar */ = new T4(0,_6P/* Lib.Shader.$fNumVar */,_1J/* Lib.Shader.$fFractionalVar_$c/ */,_6s/* Lib.Shader.$fFractionalVar_$crecip */,_6m/* Lib.Shader.$fFractionalVar_$cfromRational */),
_7f/* $fFloatingVar */ = {_:0,a:_7e/* Lib.Shader.$fFractionalVar */,b:_1k/* Lib.Shader.$fFloatingVar_$cpi */,c:_18/* Lib.Shader.$fFloatingVar_$cexp */,d:_1c/* Lib.Shader.$fFloatingVar_$clog */,e:_1v/* Lib.Shader.$fFloatingVar_$csqrt */,f:_x/* Lib.Shader.$fFloatingVar_$c** */,g:_1g/* Lib.Shader.$fFloatingVar_$clogBase */,h:_1n/* Lib.Shader.$fFloatingVar_$csin */,i:_10/* Lib.Shader.$fFloatingVar_$ccos */,j:_1z/* Lib.Shader.$fFloatingVar_$ctan */,k:_K/* Lib.Shader.$fFloatingVar_$casin */,l:_C/* Lib.Shader.$fFloatingVar_$cacos */,m:_S/* Lib.Shader.$fFloatingVar_$catan */,n:_1r/* Lib.Shader.$fFloatingVar_$csinh */,o:_14/* Lib.Shader.$fFloatingVar_$ccosh */,p:_1D/* Lib.Shader.$fFloatingVar_$ctanh */,q:_O/* Lib.Shader.$fFloatingVar_$casinh */,r:_G/* Lib.Shader.$fFloatingVar_$cacosh */,s:_W/* Lib.Shader.$fFloatingVar_$catanh */},
_7g/* $p1Floating */ = function(_7h/* s1knr */){
  return E(E(_7h/* s1knr */).a);
},
_7i/* $p1Fractional */ = function(_7j/* sv9v */){
  return E(E(_7j/* sv9v */).a);
},
_7k/* * */ = function(_7l/* s6FO */){
  return E(E(_7l/* s6FO */).c);
},
_7m/* - */ = function(_7n/* s6FF */){
  return E(E(_7n/* s6FF */).b);
},
_7o/* fromRational */ = function(_7p/* sv9N */){
  return E(E(_7p/* sv9N */).d);
},
_7q/* $fArithWorld2 */ = new T1(0,1),
_7r/* gradient2 */ = new T1(0,2),
_7s/* gradient1 */ = new T2(0,E(_7q/* Lib.World.$fArithWorld2 */),E(_7r/* Lib.World.gradient2 */)),
_7t/* gradient4 */ = new T1(0,5),
_7u/* gradient5 */ = new T1(0,4),
_7v/* gradient3 */ = new T2(0,E(_7u/* Lib.World.gradient5 */),E(_7t/* Lib.World.gradient4 */)),
_7w/* sqrt */ = function(_7x/* s1koN */){
  return E(E(_7x/* s1koN */).e);
},
_7y/* $wfield */ = function(_7z/* s55o */, _7A/* s55p */, _7B/* s55q */, _7C/* s55r */){
  var _7D/* s55s */ = B(_7g/* GHC.Float.$p1Floating */(_7z/* s55o */)),
  _7E/* s55t */ = B(_7i/* GHC.Real.$p1Fractional */(_7D/* s55s */)),
  _7F/* s55D */ = new T(function(){
    var _7G/* s55C */ = new T(function(){
      var _7H/* s55A */ = new T(function(){
        var _7I/* s55u */ = new T(function(){
          var _7J/* s55y */ = new T(function(){
            var _7K/* s55x */ = new T(function(){
              return B(A3(_6I/* GHC.Num.+ */,_7E/* s55t */, new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_7E/* s55t */, _7A/* s55p */, _7A/* s55p */));
              }), new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_7E/* s55t */, _7C/* s55r */, _7C/* s55r */));
              })));
            });
            return B(A2(_7w/* GHC.Float.sqrt */,_7z/* s55o */, _7K/* s55x */));
          });
          return B(A3(_7m/* GHC.Num.- */,_7E/* s55t */, _7J/* s55y */, new T(function(){
            return B(A2(_7o/* GHC.Real.fromRational */,_7D/* s55s */, _7v/* Lib.World.gradient3 */));
          })));
        });
        return B(A3(_7k/* GHC.Num.* */,_7E/* s55t */, _7I/* s55u */, _7I/* s55u */));
      });
      return B(A3(_6I/* GHC.Num.+ */,_7E/* s55t */, _7H/* s55A */, new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_7E/* s55t */, _7B/* s55q */, _7B/* s55q */));
      })));
    });
    return B(A2(_7w/* GHC.Float.sqrt */,_7z/* s55o */, _7G/* s55C */));
  });
  return new F(function(){return A3(_7m/* GHC.Num.- */,_7E/* s55t */, _7F/* s55D */, new T(function(){
    return B(A2(_7o/* GHC.Real.fromRational */,_7D/* s55s */, _7s/* Lib.World.gradient1 */));
  }));});
},
_7L/* fieldStr4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("x"));
}),
_7M/* fieldStr_dt */ = new T1(0,_7L/* Lib.Shader.fieldStr4 */),
_7N/* fieldStr3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("y"));
}),
_7O/* fieldStr_dt1 */ = new T1(0,_7N/* Lib.Shader.fieldStr3 */),
_7P/* fieldStr2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("z"));
}),
_7Q/* fieldStr_dt2 */ = new T1(0,_7P/* Lib.Shader.fieldStr2 */),
_7R/* fieldStr1 */ = new T(function(){
  return B(_7y/* Lib.World.$wfield */(_7f/* Lib.Shader.$fFloatingVar */, _7M/* Lib.Shader.fieldStr_dt */, _7O/* Lib.Shader.fieldStr_dt1 */, _7Q/* Lib.Shader.fieldStr_dt2 */));
}),
_7S/* id */ = function(_7T/* s3aG */){
  return E(_7T/* s3aG */);
},
_7U/* fieldStr */ = new T(function(){
  return toJSStr/* EXTERNAL */(B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_p/* GHC.Base.$fMonoid[] */, _7S/* GHC.Base.id */, _7R/* Lib.Shader.fieldStr1 */)));
}),
_7V/* $fFoldableVar_$s$cfoldMap */ = function(_7W/* s7As */, _7X/* s7At */, _7Y/* s7Au */){
  var _7Z/* s7Av */ = new T(function(){
    return B(_1/* GHC.Base.mappend */(_7W/* s7As */));
  }),
  _80/* s7Aw */ = new T(function(){
    return B(_3/* GHC.Base.mempty */(_7W/* s7As */));
  }),
  _81/* s7Ax */ = function(_82/* s7Ay */){
    var _83/* s7Az */ = E(_82/* s7Ay */);
    if(!_83/* s7Az */._){
      return E(_80/* s7Aw */);
    }else{
      return new F(function(){return A2(_7Z/* s7Av */,new T(function(){
        return B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_7W/* s7As */, _7X/* s7At */, _83/* s7Az */.a));
      }), new T(function(){
        return B(_81/* s7Ax */(_83/* s7Az */.b));
      }));});
    }
  };
  return new F(function(){return _81/* s7Ax */(_7Y/* s7Au */);});
},
_84/* argument */ = new T3(0,E(_7M/* Lib.Shader.fieldStr_dt */),E(_7O/* Lib.Shader.fieldStr_dt1 */),E(_7Q/* Lib.Shader.fieldStr_dt2 */)),
_85/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(/=) is not defined"));
}),
_86/* $fEqVar_$c/= */ = new T(function(){
  return B(err/* EXTERNAL */(_85/* Lib.Shader.lvl5 */));
}),
_87/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(==) is not defined"));
}),
_88/* $fEqVar_$c== */ = new T(function(){
  return B(err/* EXTERNAL */(_87/* Lib.Shader.lvl6 */));
}),
_89/* $fEqVar */ = new T2(0,_88/* Lib.Shader.$fEqVar_$c== */,_86/* Lib.Shader.$fEqVar_$c/= */),
_8a/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(<) is not defined"));
}),
_8b/* $fOrdVar_$c< */ = new T(function(){
  return B(err/* EXTERNAL */(_8a/* Lib.Shader.lvl10 */));
}),
_8c/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(<=) is not defined"));
}),
_8d/* $fOrdVar_$c<= */ = new T(function(){
  return B(err/* EXTERNAL */(_8c/* Lib.Shader.lvl9 */));
}),
_8e/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(>) is not defined"));
}),
_8f/* $fOrdVar_$c> */ = new T(function(){
  return B(err/* EXTERNAL */(_8e/* Lib.Shader.lvl8 */));
}),
_8g/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(>=) is not defined"));
}),
_8h/* $fOrdVar_$c>= */ = new T(function(){
  return B(err/* EXTERNAL */(_8g/* Lib.Shader.lvl7 */));
}),
_8i/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("compare is not defined"));
}),
_8j/* $fOrdVar_$ccompare */ = new T(function(){
  return B(err/* EXTERNAL */(_8i/* Lib.Shader.lvl11 */));
}),
_8k/* $fOrdVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("max("));
}),
_8l/* $fOrdVar3 */ = new T1(0,_8k/* Lib.Shader.$fOrdVar4 */),
_8m/* $fOrdVar_$cmax */ = function(_8n/* s7Aa */, _8o/* s7Ab */){
  return new T1(1,new T2(1,_8l/* Lib.Shader.$fOrdVar3 */,new T2(1,_8n/* s7Aa */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_8o/* s7Ab */,_w/* Lib.Shader.gradStr3 */)))));
},
_8p/* $fOrdVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("min("));
}),
_8q/* $fOrdVar1 */ = new T1(0,_8p/* Lib.Shader.$fOrdVar2 */),
_8r/* $fOrdVar_$cmin */ = function(_8s/* s7A4 */, _8t/* s7A5 */){
  return new T1(1,new T2(1,_8q/* Lib.Shader.$fOrdVar1 */,new T2(1,_8s/* s7A4 */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_8t/* s7A5 */,_w/* Lib.Shader.gradStr3 */)))));
},
_8u/* $fOrdVar */ = {_:0,a:_89/* Lib.Shader.$fEqVar */,b:_8j/* Lib.Shader.$fOrdVar_$ccompare */,c:_8b/* Lib.Shader.$fOrdVar_$c< */,d:_8d/* Lib.Shader.$fOrdVar_$c<= */,e:_8f/* Lib.Shader.$fOrdVar_$c> */,f:_8h/* Lib.Shader.$fOrdVar_$c>= */,g:_8m/* Lib.Shader.$fOrdVar_$cmax */,h:_8r/* Lib.Shader.$fOrdVar_$cmin */},
_8v/* gradStr7 */ = new T2(0,_7f/* Lib.Shader.$fFloatingVar */,_8u/* Lib.Shader.$fOrdVar */),
_8w/* $fApplicativeWorld_$c*> */ = function(_8x/* s5dt */, _8y/* s5du */){
  var _8z/* s5dv */ = E(_8x/* s5dt */);
  return E(_8y/* s5du */);
},
_8A/* $fApplicativeWorld_$c<* */ = function(_8B/* s561 */, _8C/* s562 */){
  var _8D/* s567 */ = E(_8C/* s562 */);
  return E(_8B/* s561 */);
},
_8E/* $fApplicativeWorld_$c<*> */ = function(_8F/* s55O */, _8G/* s55P */){
  var _8H/* s55Q */ = E(_8F/* s55O */),
  _8I/* s55U */ = E(_8G/* s55P */);
  return new T3(0,E(B(A1(_8H/* s55Q */.a,_8I/* s55U */.a))),E(B(A1(_8H/* s55Q */.b,_8I/* s55U */.b))),E(B(A1(_8H/* s55Q */.c,_8I/* s55U */.c))));
},
_8J/* $WWorld */ = function(_8K/* s54z */, _8L/* s54A */, _8M/* s54B */){
  return new T3(0,E(_8K/* s54z */),E(_8L/* s54A */),E(_8M/* s54B */));
},
_8N/* $fApplicativeWorld_$cpure */ = function(_8O/* s56b */){
  return new F(function(){return _8J/* Lib.World.$WWorld */(_8O/* s56b */, _8O/* s56b */, _8O/* s56b */);});
},
_8P/* $fFunctorWorld_$c<$ */ = function(_8Q/* s5dm */, _8R/* s5dn */){
  var _8S/* s5do */ = E(_8R/* s5dn */),
  _8T/* s5ds */ = E(_8Q/* s5dm */);
  return new T3(0,E(_8T/* s5ds */),E(_8T/* s5ds */),E(_8T/* s5ds */));
},
_8U/* $fFunctorWorld_$cfmap */ = function(_8V/* s5dz */, _8W/* s5dA */){
  var _8X/* s5dB */ = E(_8W/* s5dA */);
  return new T3(0,E(B(A1(_8V/* s5dz */,_8X/* s5dB */.a))),E(B(A1(_8V/* s5dz */,_8X/* s5dB */.b))),E(B(A1(_8V/* s5dz */,_8X/* s5dB */.c))));
},
_8Y/* $fFunctorWorld */ = new T2(0,_8U/* Lib.World.$fFunctorWorld_$cfmap */,_8P/* Lib.World.$fFunctorWorld_$c<$ */),
_8Z/* $fApplicativeWorld */ = new T5(0,_8Y/* Lib.World.$fFunctorWorld */,_8N/* Lib.World.$fApplicativeWorld_$cpure */,_8E/* Lib.World.$fApplicativeWorld_$c<*> */,_8w/* Lib.World.$fApplicativeWorld_$c*> */,_8A/* Lib.World.$fApplicativeWorld_$c<* */),
_90/* $fArithWorld1 */ = new T1(0,0),
_91/* fromInteger */ = function(_92/* s6Go */){
  return E(E(_92/* s6Go */).g);
},
_93/* $fArithWorld_$cbasis */ = function(_94/* s57b */){
  var _95/* s57c */ = B(A2(_91/* GHC.Num.fromInteger */,_94/* s57b */, _7q/* Lib.World.$fArithWorld2 */)),
  _96/* s57d */ = B(A2(_91/* GHC.Num.fromInteger */,_94/* s57b */, _90/* Lib.World.$fArithWorld1 */));
  return new T3(0,E(new T3(0,E(_95/* s57c */),E(_96/* s57d */),E(_96/* s57d */))),E(new T3(0,E(_96/* s57d */),E(_95/* s57c */),E(_96/* s57d */))),E(new T3(0,E(_96/* s57d */),E(_96/* s57d */),E(_95/* s57c */))));
},
_97/* $p1Applicative */ = function(_98/* s35t */){
  return E(E(_98/* s35t */).a);
},
_99/* ** */ = function(_9a/* s1kp8 */){
  return E(E(_9a/* s1kp8 */).f);
},
_9b/* / */ = function(_9c/* sv9B */){
  return E(E(_9c/* sv9B */).b);
},
_9d/* <*> */ = function(_9e/* s35H */){
  return E(E(_9e/* s35H */).c);
},
_9f/* fmap */ = function(_9g/* s35l */){
  return E(E(_9g/* s35l */).a);
},
_9h/* log */ = function(_9i/* s1kos */){
  return E(E(_9i/* s1kos */).d);
},
_9j/* $w$c** */ = function(_9k/* s9MH */, _9l/* s9MI */, _9m/* s9MJ */, _9n/* s9MK */, _9o/* s9ML */){
  var _9p/* s9MM */ = new T(function(){
    return E(E(E(_9k/* s9MH */).c).a);
  }),
  _9q/* s9Nc */ = new T(function(){
    var _9r/* s9MW */ = E(_9k/* s9MH */).a,
    _9s/* s9Nb */ = new T(function(){
      var _9t/* s9MZ */ = new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_9p/* s9MM */));
      }),
      _9u/* s9N0 */ = new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(_9t/* s9MZ */));
      }),
      _9v/* s9N1 */ = new T(function(){
        return B(A2(_9h/* GHC.Float.log */,_9p/* s9MM */, _9l/* s9MI */));
      }),
      _9w/* s9N2 */ = new T(function(){
        return B(A3(_99/* GHC.Float.** */,_9p/* s9MM */, _9l/* s9MI */, _9n/* s9MK */));
      }),
      _9x/* s9Na */ = function(_9y/* s9N4 */, _9z/* s9N5 */){
        var _9A/* s9N9 */ = new T(function(){
          var _9B/* s9N7 */ = new T(function(){
            return B(A3(_9b/* GHC.Real./ */,_9t/* s9MZ */, new T(function(){
              return B(A3(_7k/* GHC.Num.* */,_9u/* s9N0 */, _9n/* s9MK */, _9y/* s9N4 */));
            }), _9l/* s9MI */));
          });
          return B(A3(_6I/* GHC.Num.+ */,_9u/* s9N0 */, _9B/* s9N7 */, new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_9u/* s9N0 */, _9z/* s9N5 */, _9v/* s9N1 */));
          })));
        });
        return new F(function(){return A3(_7k/* GHC.Num.* */,_9u/* s9N0 */, _9w/* s9N2 */, _9A/* s9N9 */);});
      };
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_9r/* s9MW */)), _9x/* s9Na */, _9m/* s9MJ */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_9r/* s9MW */, _9s/* s9Nb */, _9o/* s9ML */));
  });
  return new T2(0,new T(function(){
    return B(A3(_99/* GHC.Float.** */,_9p/* s9MM */, _9l/* s9MI */, _9n/* s9MK */));
  }),_9q/* s9Nc */);
},
_9C/* $fFloatingExpr_$c** */ = function(_9D/* s9Nd */, _9E/* s9Ne */, _9F/* s9Nf */, _9G/* s9Ng */){
  var _9H/* s9Nh */ = E(_9F/* s9Nf */),
  _9I/* s9Nk */ = E(_9G/* s9Ng */),
  _9J/* s9Nn */ = B(_9j/* Lib.AD.$w$c** */(_9E/* s9Ne */, _9H/* s9Nh */.a, _9H/* s9Nh */.b, _9I/* s9Nk */.a, _9I/* s9Nk */.b));
  return new T2(0,_9J/* s9Nn */.a,_9J/* s9Nn */.b);
},
_9K/* $fFloatingExpr1 */ = new T1(0,1),
_9L/* acos */ = function(_9M/* s1kra */){
  return E(E(_9M/* s1kra */).l);
},
_9N/* $w$cacos */ = function(_9O/* s9JY */, _9P/* s9JZ */, _9Q/* s9K0 */){
  var _9R/* s9K1 */ = new T(function(){
    return E(E(E(_9O/* s9JY */).c).a);
  }),
  _9S/* s9Ko */ = new T(function(){
    var _9T/* s9Kf */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_9R/* s9K1 */));
    }),
    _9U/* s9Kg */ = new T(function(){
      var _9V/* s9Kh */ = B(_7i/* GHC.Real.$p1Fractional */(_9T/* s9Kf */)),
      _9W/* s9Kl */ = new T(function(){
        var _9X/* s9Kk */ = new T(function(){
          return B(A3(_7m/* GHC.Num.- */,_9V/* s9Kh */, new T(function(){
            return B(A2(_91/* GHC.Num.fromInteger */,_9V/* s9Kh */, _9K/* Lib.AD.$fFloatingExpr1 */));
          }), new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_9V/* s9Kh */, _9P/* s9JZ */, _9P/* s9JZ */));
          })));
        });
        return B(A2(_7w/* GHC.Float.sqrt */,_9R/* s9K1 */, _9X/* s9Kk */));
      });
      return B(A2(_6K/* GHC.Num.negate */,_9V/* s9Kh */, _9W/* s9Kl */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_9O/* s9JY */).a)), function(_9Y/* s9Km */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_9T/* s9Kf */, _9Y/* s9Km */, _9U/* s9Kg */);});
    }, _9Q/* s9K0 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_9L/* GHC.Float.acos */,_9R/* s9K1 */, _9P/* s9JZ */));
  }),_9S/* s9Ko */);
},
_9Z/* $fFloatingExpr_$cacos */ = function(_a0/* s9Kp */, _a1/* s9Kq */, _a2/* s9Kr */){
  var _a3/* s9Ks */ = E(_a2/* s9Kr */),
  _a4/* s9Kv */ = B(_9N/* Lib.AD.$w$cacos */(_a1/* s9Kq */, _a3/* s9Ks */.a, _a3/* s9Ks */.b));
  return new T2(0,_a4/* s9Kv */.a,_a4/* s9Kv */.b);
},
_a5/* acosh */ = function(_a6/* s1ktc */){
  return E(E(_a6/* s1ktc */).r);
},
_a7/* $w$cacosh */ = function(_a8/* s9GJ */, _a9/* s9GK */, _aa/* s9GL */){
  var _ab/* s9GM */ = new T(function(){
    return E(E(E(_a8/* s9GJ */).c).a);
  }),
  _ac/* s9H8 */ = new T(function(){
    var _ad/* s9H0 */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_ab/* s9GM */));
    }),
    _ae/* s9H1 */ = new T(function(){
      var _af/* s9H5 */ = new T(function(){
        var _ag/* s9H2 */ = B(_7i/* GHC.Real.$p1Fractional */(_ad/* s9H0 */));
        return B(A3(_7m/* GHC.Num.- */,_ag/* s9H2 */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_ag/* s9H2 */, _a9/* s9GK */, _a9/* s9GK */));
        }), new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_ag/* s9H2 */, _9K/* Lib.AD.$fFloatingExpr1 */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_ab/* s9GM */, _af/* s9H5 */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_a8/* s9GJ */).a)), function(_ah/* s9H6 */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_ad/* s9H0 */, _ah/* s9H6 */, _ae/* s9H1 */);});
    }, _aa/* s9GL */));
  });
  return new T2(0,new T(function(){
    return B(A2(_a5/* GHC.Float.acosh */,_ab/* s9GM */, _a9/* s9GK */));
  }),_ac/* s9H8 */);
},
_ai/* $fFloatingExpr_$cacosh */ = function(_aj/* s9H9 */, _ak/* s9Ha */, _al/* s9Hb */){
  var _am/* s9Hc */ = E(_al/* s9Hb */),
  _an/* s9Hf */ = B(_a7/* Lib.AD.$w$cacosh */(_ak/* s9Ha */, _am/* s9Hc */.a, _am/* s9Hc */.b));
  return new T2(0,_an/* s9Hf */.a,_an/* s9Hf */.b);
},
_ao/* asin */ = function(_ap/* s1kqP */){
  return E(E(_ap/* s1kqP */).k);
},
_aq/* $w$casin */ = function(_ar/* s9Ky */, _as/* s9Kz */, _at/* s9KA */){
  var _au/* s9KB */ = new T(function(){
    return E(E(E(_ar/* s9Ky */).c).a);
  }),
  _av/* s9KX */ = new T(function(){
    var _aw/* s9KP */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_au/* s9KB */));
    }),
    _ax/* s9KQ */ = new T(function(){
      var _ay/* s9KU */ = new T(function(){
        var _az/* s9KR */ = B(_7i/* GHC.Real.$p1Fractional */(_aw/* s9KP */));
        return B(A3(_7m/* GHC.Num.- */,_az/* s9KR */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_az/* s9KR */, _9K/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_az/* s9KR */, _as/* s9Kz */, _as/* s9Kz */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_au/* s9KB */, _ay/* s9KU */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_ar/* s9Ky */).a)), function(_aA/* s9KV */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_aw/* s9KP */, _aA/* s9KV */, _ax/* s9KQ */);});
    }, _at/* s9KA */));
  });
  return new T2(0,new T(function(){
    return B(A2(_ao/* GHC.Float.asin */,_au/* s9KB */, _as/* s9Kz */));
  }),_av/* s9KX */);
},
_aB/* $fFloatingExpr_$casin */ = function(_aC/* s9KY */, _aD/* s9KZ */, _aE/* s9L0 */){
  var _aF/* s9L1 */ = E(_aE/* s9L0 */),
  _aG/* s9L4 */ = B(_aq/* Lib.AD.$w$casin */(_aD/* s9KZ */, _aF/* s9L1 */.a, _aF/* s9L1 */.b));
  return new T2(0,_aG/* s9L4 */.a,_aG/* s9L4 */.b);
},
_aH/* asinh */ = function(_aI/* s1ksR */){
  return E(E(_aI/* s1ksR */).q);
},
_aJ/* $w$casinh */ = function(_aK/* s9Hi */, _aL/* s9Hj */, _aM/* s9Hk */){
  var _aN/* s9Hl */ = new T(function(){
    return E(E(E(_aK/* s9Hi */).c).a);
  }),
  _aO/* s9HH */ = new T(function(){
    var _aP/* s9Hz */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_aN/* s9Hl */));
    }),
    _aQ/* s9HA */ = new T(function(){
      var _aR/* s9HE */ = new T(function(){
        var _aS/* s9HB */ = B(_7i/* GHC.Real.$p1Fractional */(_aP/* s9Hz */));
        return B(A3(_6I/* GHC.Num.+ */,_aS/* s9HB */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_aS/* s9HB */, _aL/* s9Hj */, _aL/* s9Hj */));
        }), new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_aS/* s9HB */, _9K/* Lib.AD.$fFloatingExpr1 */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_aN/* s9Hl */, _aR/* s9HE */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_aK/* s9Hi */).a)), function(_aT/* s9HF */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_aP/* s9Hz */, _aT/* s9HF */, _aQ/* s9HA */);});
    }, _aM/* s9Hk */));
  });
  return new T2(0,new T(function(){
    return B(A2(_aH/* GHC.Float.asinh */,_aN/* s9Hl */, _aL/* s9Hj */));
  }),_aO/* s9HH */);
},
_aU/* $fFloatingExpr_$casinh */ = function(_aV/* s9HI */, _aW/* s9HJ */, _aX/* s9HK */){
  var _aY/* s9HL */ = E(_aX/* s9HK */),
  _aZ/* s9HO */ = B(_aJ/* Lib.AD.$w$casinh */(_aW/* s9HJ */, _aY/* s9HL */.a, _aY/* s9HL */.b));
  return new T2(0,_aZ/* s9HO */.a,_aZ/* s9HO */.b);
},
_b0/* atan */ = function(_b1/* s1krv */){
  return E(E(_b1/* s1krv */).m);
},
_b2/* $w$catan */ = function(_b3/* s9Jq */, _b4/* s9Jr */, _b5/* s9Js */){
  var _b6/* s9Jt */ = new T(function(){
    return E(E(E(_b3/* s9Jq */).c).a);
  }),
  _b7/* s9JO */ = new T(function(){
    var _b8/* s9JH */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_b6/* s9Jt */));
    }),
    _b9/* s9JI */ = new T(function(){
      var _ba/* s9JJ */ = B(_7i/* GHC.Real.$p1Fractional */(_b8/* s9JH */));
      return B(A3(_6I/* GHC.Num.+ */,_ba/* s9JJ */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_ba/* s9JJ */, _9K/* Lib.AD.$fFloatingExpr1 */));
      }), new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_ba/* s9JJ */, _b4/* s9Jr */, _b4/* s9Jr */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_b3/* s9Jq */).a)), function(_bb/* s9JM */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_b8/* s9JH */, _bb/* s9JM */, _b9/* s9JI */);});
    }, _b5/* s9Js */));
  });
  return new T2(0,new T(function(){
    return B(A2(_b0/* GHC.Float.atan */,_b6/* s9Jt */, _b4/* s9Jr */));
  }),_b7/* s9JO */);
},
_bc/* $fFloatingExpr_$catan */ = function(_bd/* s9JP */, _be/* s9JQ */, _bf/* s9JR */){
  var _bg/* s9JS */ = E(_bf/* s9JR */),
  _bh/* s9JV */ = B(_b2/* Lib.AD.$w$catan */(_be/* s9JQ */, _bg/* s9JS */.a, _bg/* s9JS */.b));
  return new T2(0,_bh/* s9JV */.a,_bh/* s9JV */.b);
},
_bi/* atanh */ = function(_bj/* s1ktx */){
  return E(E(_bj/* s1ktx */).s);
},
_bk/* $w$catanh */ = function(_bl/* s9Gb */, _bm/* s9Gc */, _bn/* s9Gd */){
  var _bo/* s9Ge */ = new T(function(){
    return E(E(E(_bl/* s9Gb */).c).a);
  }),
  _bp/* s9Gz */ = new T(function(){
    var _bq/* s9Gs */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_bo/* s9Ge */));
    }),
    _br/* s9Gt */ = new T(function(){
      var _bs/* s9Gu */ = B(_7i/* GHC.Real.$p1Fractional */(_bq/* s9Gs */));
      return B(A3(_7m/* GHC.Num.- */,_bs/* s9Gu */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_bs/* s9Gu */, _9K/* Lib.AD.$fFloatingExpr1 */));
      }), new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_bs/* s9Gu */, _bm/* s9Gc */, _bm/* s9Gc */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_bl/* s9Gb */).a)), function(_bt/* s9Gx */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_bq/* s9Gs */, _bt/* s9Gx */, _br/* s9Gt */);});
    }, _bn/* s9Gd */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bi/* GHC.Float.atanh */,_bo/* s9Ge */, _bm/* s9Gc */));
  }),_bp/* s9Gz */);
},
_bu/* $fFloatingExpr_$catanh */ = function(_bv/* s9GA */, _bw/* s9GB */, _bx/* s9GC */){
  var _by/* s9GD */ = E(_bx/* s9GC */),
  _bz/* s9GG */ = B(_bk/* Lib.AD.$w$catanh */(_bw/* s9GB */, _by/* s9GD */.a, _by/* s9GD */.b));
  return new T2(0,_bz/* s9GG */.a,_bz/* s9GG */.b);
},
_bA/* cos */ = function(_bB/* s1kq9 */){
  return E(E(_bB/* s1kq9 */).i);
},
_bC/* sin */ = function(_bD/* s1kpO */){
  return E(E(_bD/* s1kpO */).h);
},
_bE/* $w$ccos */ = function(_bF/* s9LE */, _bG/* s9LF */, _bH/* s9LG */){
  var _bI/* s9LH */ = new T(function(){
    return E(E(E(_bF/* s9LE */).c).a);
  }),
  _bJ/* s9M1 */ = new T(function(){
    var _bK/* s9LW */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_bI/* s9LH */));
      })));
    }),
    _bL/* s9LX */ = new T(function(){
      return B(A2(_6K/* GHC.Num.negate */,_bK/* s9LW */, new T(function(){
        return B(A2(_bC/* GHC.Float.sin */,_bI/* s9LH */, _bG/* s9LF */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_bF/* s9LE */).a)), function(_bM/* s9LZ */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_bK/* s9LW */, _bM/* s9LZ */, _bL/* s9LX */);});
    }, _bH/* s9LG */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bA/* GHC.Float.cos */,_bI/* s9LH */, _bG/* s9LF */));
  }),_bJ/* s9M1 */);
},
_bN/* $fFloatingExpr_$ccos */ = function(_bO/* s9M2 */, _bP/* s9M3 */, _bQ/* s9M4 */){
  var _bR/* s9M5 */ = E(_bQ/* s9M4 */),
  _bS/* s9M8 */ = B(_bE/* Lib.AD.$w$ccos */(_bP/* s9M3 */, _bR/* s9M5 */.a, _bR/* s9M5 */.b));
  return new T2(0,_bS/* s9M8 */.a,_bS/* s9M8 */.b);
},
_bT/* cosh */ = function(_bU/* s1ksb */){
  return E(E(_bU/* s1ksb */).o);
},
_bV/* sinh */ = function(_bW/* s1krQ */){
  return E(E(_bW/* s1krQ */).n);
},
_bX/* $w$ccosh */ = function(_bY/* s9Io */, _bZ/* s9Ip */, _c0/* s9Iq */){
  var _c1/* s9Ir */ = new T(function(){
    return E(E(E(_bY/* s9Io */).c).a);
  }),
  _c2/* s9IK */ = new T(function(){
    var _c3/* s9IG */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_c1/* s9Ir */));
      })));
    }),
    _c4/* s9IH */ = new T(function(){
      return B(A2(_bV/* GHC.Float.sinh */,_c1/* s9Ir */, _bZ/* s9Ip */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_bY/* s9Io */).a)), function(_c5/* s9II */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_c3/* s9IG */, _c5/* s9II */, _c4/* s9IH */);});
    }, _c0/* s9Iq */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bT/* GHC.Float.cosh */,_c1/* s9Ir */, _bZ/* s9Ip */));
  }),_c2/* s9IK */);
},
_c6/* $fFloatingExpr_$ccosh */ = function(_c7/* s9IL */, _c8/* s9IM */, _c9/* s9IN */){
  var _ca/* s9IO */ = E(_c9/* s9IN */),
  _cb/* s9IR */ = B(_bX/* Lib.AD.$w$ccosh */(_c8/* s9IM */, _ca/* s9IO */.a, _ca/* s9IO */.b));
  return new T2(0,_cb/* s9IR */.a,_cb/* s9IR */.b);
},
_cc/* exp */ = function(_cd/* s1ko7 */){
  return E(E(_cd/* s1ko7 */).c);
},
_ce/* $w$cexp */ = function(_cf/* s9Ox */, _cg/* s9Oy */, _ch/* s9Oz */){
  var _ci/* s9OA */ = new T(function(){
    return E(E(E(_cf/* s9Ox */).c).a);
  }),
  _cj/* s9OT */ = new T(function(){
    var _ck/* s9OP */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_ci/* s9OA */));
      })));
    }),
    _cl/* s9OQ */ = new T(function(){
      return B(A2(_cc/* GHC.Float.exp */,_ci/* s9OA */, _cg/* s9Oy */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_cf/* s9Ox */).a)), function(_cm/* s9OR */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_ck/* s9OP */, _cm/* s9OR */, _cl/* s9OQ */);});
    }, _ch/* s9Oz */));
  });
  return new T2(0,new T(function(){
    return B(A2(_cc/* GHC.Float.exp */,_ci/* s9OA */, _cg/* s9Oy */));
  }),_cj/* s9OT */);
},
_cn/* $fFloatingExpr_$cexp */ = function(_co/* s9OU */, _cp/* s9OV */, _cq/* s9OW */){
  var _cr/* s9OX */ = E(_cq/* s9OW */),
  _cs/* s9P0 */ = B(_ce/* Lib.AD.$w$cexp */(_cp/* s9OV */, _cr/* s9OX */.a, _cr/* s9OX */.b));
  return new T2(0,_cs/* s9P0 */.a,_cs/* s9P0 */.b);
},
_ct/* $w$clog */ = function(_cu/* s9O0 */, _cv/* s9O1 */, _cw/* s9O2 */){
  var _cx/* s9O3 */ = new T(function(){
    return E(E(E(_cu/* s9O0 */).c).a);
  }),
  _cy/* s9On */ = new T(function(){
    var _cz/* s9Oh */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_cx/* s9O3 */));
    }),
    _cA/* s9Oi */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_cz/* s9Oh */));
    }),
    _cB/* s9Oj */ = new T(function(){
      return B(A3(_9b/* GHC.Real./ */,_cz/* s9Oh */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_cA/* s9Oi */, _9K/* Lib.AD.$fFloatingExpr1 */));
      }), _cv/* s9O1 */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_cu/* s9O0 */).a)), function(_cC/* s9Ol */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_cA/* s9Oi */, _cC/* s9Ol */, _cB/* s9Oj */);});
    }, _cw/* s9O2 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_9h/* GHC.Float.log */,_cx/* s9O3 */, _cv/* s9O1 */));
  }),_cy/* s9On */);
},
_cD/* $fFloatingExpr_$clog */ = function(_cE/* s9Oo */, _cF/* s9Op */, _cG/* s9Oq */){
  var _cH/* s9Or */ = E(_cG/* s9Oq */),
  _cI/* s9Ou */ = B(_ct/* Lib.AD.$w$clog */(_cF/* s9Op */, _cH/* s9Or */.a, _cH/* s9Or */.b));
  return new T2(0,_cI/* s9Ou */.a,_cI/* s9Ou */.b);
},
_cJ/* $fFloatingExpr_$clogBase */ = function(_cK/* s9Pq */, _cL/* s9Pr */, _cM/* s9Ps */, _cN/* s9Pt */){
  var _cO/* s9Pu */ = new T(function(){
    return E(E(_cL/* s9Pr */).c);
  }),
  _cP/* s9PS */ = new T3(0,new T(function(){
    return E(E(_cL/* s9Pr */).a);
  }),new T(function(){
    return E(E(_cL/* s9Pr */).b);
  }),new T2(0,new T(function(){
    return E(E(_cO/* s9Pu */).a);
  }),new T(function(){
    return E(E(_cO/* s9Pu */).b);
  })));
  return new F(function(){return A3(_9b/* GHC.Real./ */,_cK/* s9Pq */, new T(function(){
    var _cQ/* s9PT */ = E(_cN/* s9Pt */),
    _cR/* s9PW */ = B(_ct/* Lib.AD.$w$clog */(_cP/* s9PS */, _cQ/* s9PT */.a, _cQ/* s9PT */.b));
    return new T2(0,_cR/* s9PW */.a,_cR/* s9PW */.b);
  }), new T(function(){
    var _cS/* s9Q0 */ = E(_cM/* s9Ps */),
    _cT/* s9Q3 */ = B(_ct/* Lib.AD.$w$clog */(_cP/* s9PS */, _cS/* s9Q0 */.a, _cS/* s9Q0 */.b));
    return new T2(0,_cT/* s9Q3 */.a,_cT/* s9Q3 */.b);
  }));});
},
_cU/* $fFloatingExpr3 */ = new T1(0,0),
_cV/* pi */ = function(_cW/* s1knM */){
  return E(E(_cW/* s1knM */).b);
},
_cX/* pure */ = function(_cY/* s35A */){
  return E(E(_cY/* s35A */).b);
},
_cZ/* $w$cpi */ = function(_d0/* s9P3 */){
  var _d1/* s9P4 */ = new T(function(){
    return E(E(E(_d0/* s9P3 */).c).a);
  }),
  _d2/* s9Pk */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_d0/* s9P3 */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_d1/* s9P4 */)))), _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(_cV/* GHC.Float.pi */(_d1/* s9P4 */));
  }),_d2/* s9Pk */);
},
_d3/* $fFloatingExpr_$cpi */ = function(_d4/* s9Pl */, _d5/* s9Pm */){
  var _d6/* s9Pn */ = B(_cZ/* Lib.AD.$w$cpi */(_d5/* s9Pm */));
  return new T2(0,_d6/* s9Pn */.a,_d6/* s9Pn */.b);
},
_d7/* $w$csin */ = function(_d8/* s9Mb */, _d9/* s9Mc */, _da/* s9Md */){
  var _db/* s9Me */ = new T(function(){
    return E(E(E(_d8/* s9Mb */).c).a);
  }),
  _dc/* s9Mx */ = new T(function(){
    var _dd/* s9Mt */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_db/* s9Me */));
      })));
    }),
    _de/* s9Mu */ = new T(function(){
      return B(A2(_bA/* GHC.Float.cos */,_db/* s9Me */, _d9/* s9Mc */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_d8/* s9Mb */).a)), function(_df/* s9Mv */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_dd/* s9Mt */, _df/* s9Mv */, _de/* s9Mu */);});
    }, _da/* s9Md */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bC/* GHC.Float.sin */,_db/* s9Me */, _d9/* s9Mc */));
  }),_dc/* s9Mx */);
},
_dg/* $fFloatingExpr_$csin */ = function(_dh/* s9My */, _di/* s9Mz */, _dj/* s9MA */){
  var _dk/* s9MB */ = E(_dj/* s9MA */),
  _dl/* s9ME */ = B(_d7/* Lib.AD.$w$csin */(_di/* s9Mz */, _dk/* s9MB */.a, _dk/* s9MB */.b));
  return new T2(0,_dl/* s9ME */.a,_dl/* s9ME */.b);
},
_dm/* $w$csinh */ = function(_dn/* s9IU */, _do/* s9IV */, _dp/* s9IW */){
  var _dq/* s9IX */ = new T(function(){
    return E(E(E(_dn/* s9IU */).c).a);
  }),
  _dr/* s9Jg */ = new T(function(){
    var _ds/* s9Jc */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_dq/* s9IX */));
      })));
    }),
    _dt/* s9Jd */ = new T(function(){
      return B(A2(_bT/* GHC.Float.cosh */,_dq/* s9IX */, _do/* s9IV */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_dn/* s9IU */).a)), function(_du/* s9Je */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_ds/* s9Jc */, _du/* s9Je */, _dt/* s9Jd */);});
    }, _dp/* s9IW */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bV/* GHC.Float.sinh */,_dq/* s9IX */, _do/* s9IV */));
  }),_dr/* s9Jg */);
},
_dv/* $fFloatingExpr_$csinh */ = function(_dw/* s9Jh */, _dx/* s9Ji */, _dy/* s9Jj */){
  var _dz/* s9Jk */ = E(_dy/* s9Jj */),
  _dA/* s9Jn */ = B(_dm/* Lib.AD.$w$csinh */(_dx/* s9Ji */, _dz/* s9Jk */.a, _dz/* s9Jk */.b));
  return new T2(0,_dA/* s9Jn */.a,_dA/* s9Jn */.b);
},
_dB/* $fFloatingExpr2 */ = new T1(0,2),
_dC/* $w$csqrt */ = function(_dD/* s9Nq */, _dE/* s9Nr */, _dF/* s9Ns */){
  var _dG/* s9Nt */ = new T(function(){
    return E(E(E(_dD/* s9Nq */).c).a);
  }),
  _dH/* s9NQ */ = new T(function(){
    var _dI/* s9NH */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_dG/* s9Nt */));
    }),
    _dJ/* s9NI */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_dI/* s9NH */));
    }),
    _dK/* s9NJ */ = new T(function(){
      var _dL/* s9NM */ = new T(function(){
        return B(A3(_9b/* GHC.Real./ */,_dI/* s9NH */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_dJ/* s9NI */, _9K/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_dJ/* s9NI */, _dB/* Lib.AD.$fFloatingExpr2 */));
        })));
      });
      return B(A3(_9b/* GHC.Real./ */,_dI/* s9NH */, _dL/* s9NM */, new T(function(){
        return B(A2(_7w/* GHC.Float.sqrt */,_dG/* s9Nt */, _dE/* s9Nr */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_dD/* s9Nq */).a)), function(_dM/* s9NO */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_dJ/* s9NI */, _dM/* s9NO */, _dK/* s9NJ */);});
    }, _dF/* s9Ns */));
  });
  return new T2(0,new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_dG/* s9Nt */, _dE/* s9Nr */));
  }),_dH/* s9NQ */);
},
_dN/* $fFloatingExpr_$csqrt */ = function(_dO/* s9NR */, _dP/* s9NS */, _dQ/* s9NT */){
  var _dR/* s9NU */ = E(_dQ/* s9NT */),
  _dS/* s9NX */ = B(_dC/* Lib.AD.$w$csqrt */(_dP/* s9NS */, _dR/* s9NU */.a, _dR/* s9NU */.b));
  return new T2(0,_dS/* s9NX */.a,_dS/* s9NX */.b);
},
_dT/* tan */ = function(_dU/* s1kqu */){
  return E(E(_dU/* s1kqu */).j);
},
_dV/* $w$ctan */ = function(_dW/* s9L7 */, _dX/* s9L8 */, _dY/* s9L9 */){
  var _dZ/* s9La */ = new T(function(){
    return E(E(E(_dW/* s9L7 */).c).a);
  }),
  _e0/* s9Lu */ = new T(function(){
    var _e1/* s9Lo */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_dZ/* s9La */));
    }),
    _e2/* s9Lp */ = new T(function(){
      var _e3/* s9Lq */ = new T(function(){
        return B(A2(_bA/* GHC.Float.cos */,_dZ/* s9La */, _dX/* s9L8 */));
      });
      return B(A3(_7k/* GHC.Num.* */,B(_7i/* GHC.Real.$p1Fractional */(_e1/* s9Lo */)), _e3/* s9Lq */, _e3/* s9Lq */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_dW/* s9L7 */).a)), function(_e4/* s9Ls */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_e1/* s9Lo */, _e4/* s9Ls */, _e2/* s9Lp */);});
    }, _dY/* s9L9 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_dT/* GHC.Float.tan */,_dZ/* s9La */, _dX/* s9L8 */));
  }),_e0/* s9Lu */);
},
_e5/* $fFloatingExpr_$ctan */ = function(_e6/* s9Lv */, _e7/* s9Lw */, _e8/* s9Lx */){
  var _e9/* s9Ly */ = E(_e8/* s9Lx */),
  _ea/* s9LB */ = B(_dV/* Lib.AD.$w$ctan */(_e7/* s9Lw */, _e9/* s9Ly */.a, _e9/* s9Ly */.b));
  return new T2(0,_ea/* s9LB */.a,_ea/* s9LB */.b);
},
_eb/* tanh */ = function(_ec/* s1ksw */){
  return E(E(_ec/* s1ksw */).p);
},
_ed/* $w$ctanh */ = function(_ee/* s9HR */, _ef/* s9HS */, _eg/* s9HT */){
  var _eh/* s9HU */ = new T(function(){
    return E(E(E(_ee/* s9HR */).c).a);
  }),
  _ei/* s9Ie */ = new T(function(){
    var _ej/* s9I8 */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_eh/* s9HU */));
    }),
    _ek/* s9I9 */ = new T(function(){
      var _el/* s9Ia */ = new T(function(){
        return B(A2(_bT/* GHC.Float.cosh */,_eh/* s9HU */, _ef/* s9HS */));
      });
      return B(A3(_7k/* GHC.Num.* */,B(_7i/* GHC.Real.$p1Fractional */(_ej/* s9I8 */)), _el/* s9Ia */, _el/* s9Ia */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_ee/* s9HR */).a)), function(_em/* s9Ic */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_ej/* s9I8 */, _em/* s9Ic */, _ek/* s9I9 */);});
    }, _eg/* s9HT */));
  });
  return new T2(0,new T(function(){
    return B(A2(_eb/* GHC.Float.tanh */,_eh/* s9HU */, _ef/* s9HS */));
  }),_ei/* s9Ie */);
},
_en/* $fFloatingExpr_$ctanh */ = function(_eo/* s9If */, _ep/* s9Ig */, _eq/* s9Ih */){
  var _er/* s9Ii */ = E(_eq/* s9Ih */),
  _es/* s9Il */ = B(_ed/* Lib.AD.$w$ctanh */(_ep/* s9Ig */, _er/* s9Ii */.a, _er/* s9Ii */.b));
  return new T2(0,_es/* s9Il */.a,_es/* s9Il */.b);
},
_et/* $fFloatingExpr */ = function(_eu/* s9Q7 */, _ev/* s9Q8 */){
  return {_:0,a:_eu/* s9Q7 */,b:new T(function(){
    return B(_d3/* Lib.AD.$fFloatingExpr_$cpi */(_eu/* s9Q7 */, _ev/* s9Q8 */));
  }),c:function(_ew/* B1 */){
    return new F(function(){return _cn/* Lib.AD.$fFloatingExpr_$cexp */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },d:function(_ew/* B1 */){
    return new F(function(){return _cD/* Lib.AD.$fFloatingExpr_$clog */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },e:function(_ew/* B1 */){
    return new F(function(){return _dN/* Lib.AD.$fFloatingExpr_$csqrt */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },f:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _9C/* Lib.AD.$fFloatingExpr_$c** */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ex/* B2 */, _ew/* B1 */);});
  },g:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _cJ/* Lib.AD.$fFloatingExpr_$clogBase */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ex/* B2 */, _ew/* B1 */);});
  },h:function(_ew/* B1 */){
    return new F(function(){return _dg/* Lib.AD.$fFloatingExpr_$csin */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },i:function(_ew/* B1 */){
    return new F(function(){return _bN/* Lib.AD.$fFloatingExpr_$ccos */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },j:function(_ew/* B1 */){
    return new F(function(){return _e5/* Lib.AD.$fFloatingExpr_$ctan */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },k:function(_ew/* B1 */){
    return new F(function(){return _aB/* Lib.AD.$fFloatingExpr_$casin */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },l:function(_ew/* B1 */){
    return new F(function(){return _9Z/* Lib.AD.$fFloatingExpr_$cacos */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },m:function(_ew/* B1 */){
    return new F(function(){return _bc/* Lib.AD.$fFloatingExpr_$catan */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },n:function(_ew/* B1 */){
    return new F(function(){return _dv/* Lib.AD.$fFloatingExpr_$csinh */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },o:function(_ew/* B1 */){
    return new F(function(){return _c6/* Lib.AD.$fFloatingExpr_$ccosh */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },p:function(_ew/* B1 */){
    return new F(function(){return _en/* Lib.AD.$fFloatingExpr_$ctanh */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },q:function(_ew/* B1 */){
    return new F(function(){return _aU/* Lib.AD.$fFloatingExpr_$casinh */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },r:function(_ew/* B1 */){
    return new F(function(){return _ai/* Lib.AD.$fFloatingExpr_$cacosh */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  },s:function(_ew/* B1 */){
    return new F(function(){return _bu/* Lib.AD.$fFloatingExpr_$catanh */(_eu/* s9Q7 */, _ev/* s9Q8 */, _ew/* B1 */);});
  }};
},
_ey/* $w$c/ */ = function(_ez/* s9Fp */, _eA/* s9Fq */, _eB/* s9Fr */, _eC/* s9Fs */, _eD/* s9Ft */){
  var _eE/* s9FC */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_ez/* s9Fp */).c).a);
    })));
  }),
  _eF/* s9FS */ = new T(function(){
    var _eG/* s9FF */ = E(_ez/* s9Fp */).a,
    _eH/* s9FR */ = new T(function(){
      var _eI/* s9FI */ = new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(_eE/* s9FC */));
      }),
      _eJ/* s9FJ */ = new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_eI/* s9FI */, _eC/* s9Fs */, _eC/* s9Fs */));
      }),
      _eK/* s9FQ */ = function(_eL/* s9FL */, _eM/* s9FM */){
        var _eN/* s9FP */ = new T(function(){
          return B(A3(_7m/* GHC.Num.- */,_eI/* s9FI */, new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_eI/* s9FI */, _eL/* s9FL */, _eC/* s9Fs */));
          }), new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_eI/* s9FI */, _eA/* s9Fq */, _eM/* s9FM */));
          })));
        });
        return new F(function(){return A3(_9b/* GHC.Real./ */,_eE/* s9FC */, _eN/* s9FP */, _eJ/* s9FJ */);});
      };
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_eG/* s9FF */)), _eK/* s9FQ */, _eB/* s9Fr */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_eG/* s9FF */, _eH/* s9FR */, _eD/* s9Ft */));
  });
  return new T2(0,new T(function(){
    return B(A3(_9b/* GHC.Real./ */,_eE/* s9FC */, _eA/* s9Fq */, _eC/* s9Fs */));
  }),_eF/* s9FS */);
},
_eO/* $fFractionalExpr_$c/ */ = function(_eP/* s9FT */, _eQ/* s9FU */, _eR/* s9FV */, _eS/* s9FW */){
  var _eT/* s9FX */ = E(_eR/* s9FV */),
  _eU/* s9G0 */ = E(_eS/* s9FW */),
  _eV/* s9G3 */ = B(_ey/* Lib.AD.$w$c/ */(_eQ/* s9FU */, _eT/* s9FX */.a, _eT/* s9FX */.b, _eU/* s9G0 */.a, _eU/* s9G0 */.b));
  return new T2(0,_eV/* s9G3 */.a,_eV/* s9G3 */.b);
},
_eW/* $w$cfromRational */ = function(_eX/* s9Eq */, _eY/* s9Er */){
  var _eZ/* s9EA */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_eX/* s9Eq */).c).a);
    })));
  }),
  _f0/* s9EI */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_eX/* s9Eq */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(_eZ/* s9EA */)), _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_7o/* GHC.Real.fromRational */,_eZ/* s9EA */, _eY/* s9Er */));
  }),_f0/* s9EI */);
},
_f1/* $fFractionalExpr_$cfromRational */ = function(_f2/* s9EJ */, _f3/* s9EK */, _f4/* s9EL */){
  var _f5/* s9EM */ = B(_eW/* Lib.AD.$w$cfromRational */(_f3/* s9EK */, _f4/* s9EL */));
  return new T2(0,_f5/* s9EM */.a,_f5/* s9EM */.b);
},
_f6/* $w$crecip */ = function(_f7/* s9EP */, _f8/* s9EQ */, _f9/* s9ER */){
  var _fa/* s9F0 */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_f7/* s9EP */).c).a);
    })));
  }),
  _fb/* s9F1 */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(_fa/* s9F0 */));
  }),
  _fc/* s9Ff */ = new T(function(){
    var _fd/* s9F9 */ = new T(function(){
      var _fe/* s9Fc */ = new T(function(){
        return B(A3(_9b/* GHC.Real./ */,_fa/* s9F0 */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_fb/* s9F1 */, _9K/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_fb/* s9F1 */, _f8/* s9EQ */, _f8/* s9EQ */));
        })));
      });
      return B(A2(_6K/* GHC.Num.negate */,_fb/* s9F1 */, _fe/* s9Fc */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_f7/* s9EP */).a)), function(_ff/* s9Fd */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_fb/* s9F1 */, _ff/* s9Fd */, _fd/* s9F9 */);});
    }, _f9/* s9ER */));
  }),
  _fg/* s9F3 */ = new T(function(){
    return B(A3(_9b/* GHC.Real./ */,_fa/* s9F0 */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_fb/* s9F1 */, _9K/* Lib.AD.$fFloatingExpr1 */));
    }), _f8/* s9EQ */));
  });
  return new T2(0,_fg/* s9F3 */,_fc/* s9Ff */);
},
_fh/* $fFractionalExpr_$crecip */ = function(_fi/* s9Fg */, _fj/* s9Fh */, _fk/* s9Fi */){
  var _fl/* s9Fj */ = E(_fk/* s9Fi */),
  _fm/* s9Fm */ = B(_f6/* Lib.AD.$w$crecip */(_fj/* s9Fh */, _fl/* s9Fj */.a, _fl/* s9Fj */.b));
  return new T2(0,_fm/* s9Fm */.a,_fm/* s9Fm */.b);
},
_fn/* $fFractionalExpr */ = function(_fo/* s9G6 */, _fp/* s9G7 */){
  return new T4(0,_fo/* s9G6 */,function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _eO/* Lib.AD.$fFractionalExpr_$c/ */(_fo/* s9G6 */, _fp/* s9G7 */, _ex/* B2 */, _ew/* B1 */);});
  },function(_ew/* B1 */){
    return new F(function(){return _fh/* Lib.AD.$fFractionalExpr_$crecip */(_fo/* s9G6 */, _fp/* s9G7 */, _ew/* B1 */);});
  },function(_ew/* B1 */){
    return new F(function(){return _f1/* Lib.AD.$fFractionalExpr_$cfromRational */(_fo/* s9G6 */, _fp/* s9G7 */, _ew/* B1 */);});
  });
},
_fq/* $w$c* */ = function(_fr/* s9CZ */, _fs/* s9D0 */, _ft/* s9D1 */, _fu/* s9D2 */, _fv/* s9D3 */){
  var _fw/* s9Dd */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_fr/* s9CZ */).c).a);
      })));
    })));
  }),
  _fx/* s9Dq */ = new T(function(){
    var _fy/* s9Dg */ = E(_fr/* s9CZ */).a,
    _fz/* s9Dp */ = new T(function(){
      var _fA/* s9Do */ = function(_fB/* s9Dk */, _fC/* s9Dl */){
        return new F(function(){return A3(_6I/* GHC.Num.+ */,_fw/* s9Dd */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_fw/* s9Dd */, _fs/* s9D0 */, _fC/* s9Dl */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_fw/* s9Dd */, _fB/* s9Dk */, _fu/* s9D2 */));
        }));});
      };
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_fy/* s9Dg */)), _fA/* s9Do */, _ft/* s9D1 */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_fy/* s9Dg */, _fz/* s9Dp */, _fv/* s9D3 */));
  });
  return new T2(0,new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_fw/* s9Dd */, _fs/* s9D0 */, _fu/* s9D2 */));
  }),_fx/* s9Dq */);
},
_fD/* $fNumExpr_$c* */ = function(_fE/* s9Dr */, _fF/* s9Ds */, _fG/* s9Dt */){
  var _fH/* s9Du */ = E(_fF/* s9Ds */),
  _fI/* s9Dx */ = E(_fG/* s9Dt */),
  _fJ/* s9DA */ = B(_fq/* Lib.AD.$w$c* */(_fE/* s9Dr */, _fH/* s9Du */.a, _fH/* s9Du */.b, _fI/* s9Dx */.a, _fI/* s9Dx */.b));
  return new T2(0,_fJ/* s9DA */.a,_fJ/* s9DA */.b);
},
_fK/* $w$c+ */ = function(_fL/* s9DD */, _fM/* s9DE */, _fN/* s9DF */, _fO/* s9DG */, _fP/* s9DH */){
  var _fQ/* s9DR */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_fL/* s9DD */).c).a);
      })));
    })));
  }),
  _fR/* s9E0 */ = new T(function(){
    var _fS/* s9DU */ = E(_fL/* s9DD */).a,
    _fT/* s9DZ */ = new T(function(){
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_fS/* s9DU */)), new T(function(){
        return B(_6I/* GHC.Num.+ */(_fQ/* s9DR */));
      }), _fN/* s9DF */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_fS/* s9DU */, _fT/* s9DZ */, _fP/* s9DH */));
  });
  return new T2(0,new T(function(){
    return B(A3(_6I/* GHC.Num.+ */,_fQ/* s9DR */, _fM/* s9DE */, _fO/* s9DG */));
  }),_fR/* s9E0 */);
},
_fU/* $fNumExpr_$c+ */ = function(_fV/* s9E1 */, _fW/* s9E2 */, _fX/* s9E3 */){
  var _fY/* s9E4 */ = E(_fW/* s9E2 */),
  _fZ/* s9E7 */ = E(_fX/* s9E3 */),
  _g0/* s9Ea */ = B(_fK/* Lib.AD.$w$c+ */(_fV/* s9E1 */, _fY/* s9E4 */.a, _fY/* s9E4 */.b, _fZ/* s9E7 */.a, _fZ/* s9E7 */.b));
  return new T2(0,_g0/* s9Ea */.a,_g0/* s9Ea */.b);
},
_g1/* $fNumExpr_$c- */ = function(_g2/* s9Ed */, _g3/* s9Ee */, _g4/* s9Ef */){
  var _g5/* s9Eg */ = B(_g6/* Lib.AD.$fNumExpr */(_g2/* s9Ed */));
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_g5/* s9Eg */, _g3/* s9Ee */, new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_g5/* s9Eg */, _g4/* s9Ef */));
  }));});
},
_g7/* abs */ = function(_g8/* s6G6 */){
  return E(E(_g8/* s6G6 */).e);
},
_g9/* signum */ = function(_ga/* s6Gf */){
  return E(E(_ga/* s6Gf */).f);
},
_gb/* $w$cabs */ = function(_gc/* s9C1 */, _gd/* s9C2 */, _ge/* s9C3 */){
  var _gf/* s9Cd */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gc/* s9C1 */).c).a);
      })));
    })));
  }),
  _gg/* s9Cn */ = new T(function(){
    var _gh/* s9Ck */ = new T(function(){
      return B(A2(_g9/* GHC.Num.signum */,_gf/* s9Cd */, _gd/* s9C2 */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_gc/* s9C1 */).a)), function(_gi/* s9Cl */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_gf/* s9Cd */, _gi/* s9Cl */, _gh/* s9Ck */);});
    }, _ge/* s9C3 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_g7/* GHC.Num.abs */,_gf/* s9Cd */, _gd/* s9C2 */));
  }),_gg/* s9Cn */);
},
_gj/* $fNumExpr_$cabs */ = function(_gk/* s9Co */, _gl/* s9Cp */){
  var _gm/* s9Cq */ = E(_gl/* s9Cp */),
  _gn/* s9Ct */ = B(_gb/* Lib.AD.$w$cabs */(_gk/* s9Co */, _gm/* s9Cq */.a, _gm/* s9Cq */.b));
  return new T2(0,_gn/* s9Ct */.a,_gn/* s9Ct */.b);
},
_go/* $w$cfromInteger */ = function(_gp/* s9Bc */, _gq/* s9Bd */){
  var _gr/* s9Bn */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gp/* s9Bc */).c).a);
      })));
    })));
  }),
  _gs/* s9Bu */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_gp/* s9Bc */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_gr/* s9Bn */, _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,_gr/* s9Bn */, _gq/* s9Bd */));
  }),_gs/* s9Bu */);
},
_gt/* $fNumExpr_$cfromInteger */ = function(_gu/* s9Bv */, _gv/* s9Bw */){
  var _gw/* s9Bx */ = B(_go/* Lib.AD.$w$cfromInteger */(_gu/* s9Bv */, _gv/* s9Bw */));
  return new T2(0,_gw/* s9Bx */.a,_gw/* s9Bx */.b);
},
_gx/* $w$cnegate */ = function(_gy/* s9Cw */, _gz/* s9Cx */, _gA/* s9Cy */){
  var _gB/* s9CI */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gy/* s9Cw */).c).a);
      })));
    })));
  }),
  _gC/* s9CQ */ = new T(function(){
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_gy/* s9Cw */).a)), new T(function(){
      return B(_6K/* GHC.Num.negate */(_gB/* s9CI */));
    }), _gA/* s9Cy */));
  });
  return new T2(0,new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_gB/* s9CI */, _gz/* s9Cx */));
  }),_gC/* s9CQ */);
},
_gD/* $fNumExpr_$cnegate */ = function(_gE/* s9CR */, _gF/* s9CS */){
  var _gG/* s9CT */ = E(_gF/* s9CS */),
  _gH/* s9CW */ = B(_gx/* Lib.AD.$w$cnegate */(_gE/* s9CR */, _gG/* s9CT */.a, _gG/* s9CT */.b));
  return new T2(0,_gH/* s9CW */.a,_gH/* s9CW */.b);
},
_gI/* $w$csignum */ = function(_gJ/* s9BA */, _gK/* s9BB */){
  var _gL/* s9BL */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gJ/* s9BA */).c).a);
      })));
    })));
  }),
  _gM/* s9BS */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_gJ/* s9BA */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_gL/* s9BL */, _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_g9/* GHC.Num.signum */,_gL/* s9BL */, _gK/* s9BB */));
  }),_gM/* s9BS */);
},
_gN/* $fNumExpr_$csignum */ = function(_gO/* s9BT */, _gP/* s9BU */){
  var _gQ/* s9BY */ = B(_gI/* Lib.AD.$w$csignum */(_gO/* s9BT */, E(_gP/* s9BU */).a));
  return new T2(0,_gQ/* s9BY */.a,_gQ/* s9BY */.b);
},
_g6/* $fNumExpr */ = function(_gR/* s9Ei */){
  return {_:0,a:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _fU/* Lib.AD.$fNumExpr_$c+ */(_gR/* s9Ei */, _ex/* B2 */, _ew/* B1 */);});
  },b:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _g1/* Lib.AD.$fNumExpr_$c- */(_gR/* s9Ei */, _ex/* B2 */, _ew/* B1 */);});
  },c:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _fD/* Lib.AD.$fNumExpr_$c* */(_gR/* s9Ei */, _ex/* B2 */, _ew/* B1 */);});
  },d:function(_ew/* B1 */){
    return new F(function(){return _gD/* Lib.AD.$fNumExpr_$cnegate */(_gR/* s9Ei */, _ew/* B1 */);});
  },e:function(_ew/* B1 */){
    return new F(function(){return _gj/* Lib.AD.$fNumExpr_$cabs */(_gR/* s9Ei */, _ew/* B1 */);});
  },f:function(_ew/* B1 */){
    return new F(function(){return _gN/* Lib.AD.$fNumExpr_$csignum */(_gR/* s9Ei */, _ew/* B1 */);});
  },g:function(_ew/* B1 */){
    return new F(function(){return _gt/* Lib.AD.$fNumExpr_$cfromInteger */(_gR/* s9Ei */, _ew/* B1 */);});
  }};
},
_gS/* gradient */ = function(_gT/* s5ep */){
  var _gU/* s5eq */ = new T(function(){
    return E(E(_gT/* s5ep */).a);
  }),
  _gV/* s5ez */ = new T3(0,_8Z/* Lib.World.$fApplicativeWorld */,_93/* Lib.World.$fArithWorld_$cbasis */,new T2(0,_gU/* s5eq */,new T(function(){
    return E(E(_gT/* s5ep */).b);
  }))),
  _gW/* s5eC */ = new T(function(){
    return B(_et/* Lib.AD.$fFloatingExpr */(new T(function(){
      return B(_fn/* Lib.AD.$fFractionalExpr */(new T(function(){
        return B(_g6/* Lib.AD.$fNumExpr */(_gV/* s5ez */));
      }), _gV/* s5ez */));
    }), _gV/* s5ez */));
  }),
  _gX/* s5eE */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_gU/* s5eq */));
    })));
  });
  return function(_gY/* s5eF */){
    var _gZ/* s5eG */ = E(_gY/* s5eF */),
    _h0/* s5eK */ = B(A2(_91/* GHC.Num.fromInteger */,_gX/* s5eE */, _7q/* Lib.World.$fArithWorld2 */)),
    _h1/* s5eL */ = B(A2(_91/* GHC.Num.fromInteger */,_gX/* s5eE */, _90/* Lib.World.$fArithWorld1 */));
    return E(B(_7y/* Lib.World.$wfield */(_gW/* s5eC */, new T2(0,_gZ/* s5eG */.a,new T3(0,E(_h0/* s5eK */),E(_h1/* s5eL */),E(_h1/* s5eL */))), new T2(0,_gZ/* s5eG */.b,new T3(0,E(_h1/* s5eL */),E(_h0/* s5eK */),E(_h1/* s5eL */))), new T2(0,_gZ/* s5eG */.c,new T3(0,E(_h1/* s5eL */),E(_h1/* s5eL */),E(_h0/* s5eK */))))).b);
  };
},
_h2/* gradStr6 */ = new T(function(){
  return B(_gS/* Lib.World.gradient */(_8v/* Lib.Shader.gradStr7 */));
}),
_h3/* prependToAll */ = function(_h4/* s1ZGt */, _h5/* s1ZGu */){
  var _h6/* s1ZGv */ = E(_h5/* s1ZGu */);
  return (_h6/* s1ZGv */._==0) ? __Z/* EXTERNAL */ : new T2(1,_h4/* s1ZGt */,new T2(1,_h6/* s1ZGv */.a,new T(function(){
    return B(_h3/* Data.OldList.prependToAll */(_h4/* s1ZGt */, _h6/* s1ZGv */.b));
  })));
},
_h7/* gradStr5 */ = new T(function(){
  var _h8/* s7C5 */ = B(A1(_h2/* Lib.Shader.gradStr6 */,_84/* Lib.Shader.argument */));
  return new T2(1,_h8/* s7C5 */.a,new T(function(){
    return B(_h3/* Data.OldList.prependToAll */(_r/* Lib.Shader.$fFloatingVar29 */, new T2(1,_h8/* s7C5 */.b,new T2(1,_h8/* s7C5 */.c,_o/* GHC.Types.[] */))));
  }));
}),
_h9/* gradStr4 */ = new T1(1,_h7/* Lib.Shader.gradStr5 */),
_ha/* gradStr2 */ = new T2(1,_h9/* Lib.Shader.gradStr4 */,_w/* Lib.Shader.gradStr3 */),
_hb/* gradStr9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("vec3("));
}),
_hc/* gradStr8 */ = new T1(0,_hb/* Lib.Shader.gradStr9 */),
_hd/* gradStr1 */ = new T2(1,_hc/* Lib.Shader.gradStr8 */,_ha/* Lib.Shader.gradStr2 */),
_he/* gradStr */ = new T(function(){
  return toJSStr/* EXTERNAL */(B(_7V/* Lib.Shader.$fFoldableVar_$s$cfoldMap */(_p/* GHC.Base.$fMonoid[] */, _7S/* GHC.Base.id */, _hd/* Lib.Shader.gradStr1 */)));
}),
_hf/* $wlenAcc */ = function(_hg/* sbMs */, _hh/* sbMt */){
  while(1){
    var _hi/* sbMu */ = E(_hg/* sbMs */);
    if(!_hi/* sbMu */._){
      return E(_hh/* sbMt */);
    }else{
      var _hj/*  sbMt */ = _hh/* sbMt */+1|0;
      _hg/* sbMs */ = _hi/* sbMu */.b;
      _hh/* sbMt */ = _hj/*  sbMt */;
      continue;
    }
  }
},
_hk/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(Array.!): undefined array element"));
}),
_hl/* arrEleBottom */ = new T(function(){
  return B(err/* EXTERNAL */(_hk/* GHC.Arr.lvl37 */));
}),
_hm/* $fNumPos1 */ = 0,
_hn/* $fNumPos2 */ = new T3(0,E(_hm/* Lib.Object.$fNumPos1 */),E(_hm/* Lib.Object.$fNumPos1 */),E(_hm/* Lib.Object.$fNumPos1 */)),
_ho/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_hp/* $s^1 */ = new T(function(){
  return B(err/* EXTERNAL */(_ho/* Lib.Object.lvl10 */));
}),
_hq/* $wg1 */ = function(_hr/* sfnA */, _hs/* sfnB */, _ht/* sfnC */){
  while(1){
    if(!(_hs/* sfnB */%2)){
      var _hu/*  sfnA */ = _hr/* sfnA */*_hr/* sfnA */,
      _hv/*  sfnB */ = quot/* EXTERNAL */(_hs/* sfnB */, 2);
      _hr/* sfnA */ = _hu/*  sfnA */;
      _hs/* sfnB */ = _hv/*  sfnB */;
      continue;
    }else{
      var _hw/* sfnE */ = E(_hs/* sfnB */);
      if(_hw/* sfnE */==1){
        return _hr/* sfnA */*_ht/* sfnC */;
      }else{
        var _hu/*  sfnA */ = _hr/* sfnA */*_hr/* sfnA */,
        _hx/*  sfnC */ = _hr/* sfnA */*_ht/* sfnC */;
        _hr/* sfnA */ = _hu/*  sfnA */;
        _hs/* sfnB */ = quot/* EXTERNAL */(_hw/* sfnE */-1|0, 2);
        _ht/* sfnC */ = _hx/*  sfnC */;
        continue;
      }
    }
  }
},
_hy/* $wf */ = function(_hz/* sfnL */, _hA/* sfnM */){
  while(1){
    if(!(_hA/* sfnM */%2)){
      var _hB/*  sfnL */ = _hz/* sfnL */*_hz/* sfnL */,
      _hC/*  sfnM */ = quot/* EXTERNAL */(_hA/* sfnM */, 2);
      _hz/* sfnL */ = _hB/*  sfnL */;
      _hA/* sfnM */ = _hC/*  sfnM */;
      continue;
    }else{
      var _hD/* sfnO */ = E(_hA/* sfnM */);
      if(_hD/* sfnO */==1){
        return E(_hz/* sfnL */);
      }else{
        return new F(function(){return _hq/* Lib.Object.$wg1 */(_hz/* sfnL */*_hz/* sfnL */, quot/* EXTERNAL */(_hD/* sfnO */-1|0, 2), _hz/* sfnL */);});
      }
    }
  }
},
_hE/* $fFloatingDouble_$cacosh */ = function(_hF/* s1l7h */){
  var _hG/* s1l7i */ = E(_hF/* s1l7h */);
  return new F(function(){return Math.log/* EXTERNAL */(_hG/* s1l7i */+(_hG/* s1l7i */+1)*Math.sqrt/* EXTERNAL */((_hG/* s1l7i */-1)/(_hG/* s1l7i */+1)));});
},
_hH/* $fFloatingDouble_$casinh */ = function(_hI/* s1l7s */){
  var _hJ/* s1l7t */ = E(_hI/* s1l7s */);
  return new F(function(){return Math.log/* EXTERNAL */(_hJ/* s1l7t */+Math.sqrt/* EXTERNAL */(1+_hJ/* s1l7t */*_hJ/* s1l7t */));});
},
_hK/* $fFloatingDouble_$catanh */ = function(_hL/* s1l79 */){
  var _hM/* s1l7a */ = E(_hL/* s1l79 */);
  return 0.5*Math.log/* EXTERNAL */((1+_hM/* s1l7a */)/(1-_hM/* s1l7a */));
},
_hN/* $fFloatingDouble_$clogBase */ = function(_hO/* s1l7A */, _hP/* s1l7B */){
  return Math.log/* EXTERNAL */(E(_hP/* s1l7B */))/Math.log/* EXTERNAL */(E(_hO/* s1l7A */));
},
_hQ/* $fFloatingDouble_$cpi */ = 3.141592653589793,
_hR/* $fFractionalDouble_$cfromRational */ = function(_hS/* s1ldy */){
  var _hT/* s1ldz */ = E(_hS/* s1ldy */);
  return new F(function(){return _6j/* GHC.Float.rationalToDouble */(_hT/* s1ldz */.a, _hT/* s1ldz */.b);});
},
_hU/* $fFractionalDouble_$crecip */ = function(_hV/* s1l75 */){
  return 1/E(_hV/* s1l75 */);
},
_hW/* $fNumDouble_$cabs */ = function(_hX/* s1l6w */){
  var _hY/* s1l6x */ = E(_hX/* s1l6w */),
  _hZ/* s1l6z */ = E(_hY/* s1l6x */);
  return (_hZ/* s1l6z */==0) ? E(_6i/* GHC.Float.rationalToDouble4 */) : (_hZ/* s1l6z */<=0) ?  -_hZ/* s1l6z */ : E(_hY/* s1l6x */);
},
_i0/* doubleFromInteger */ = function(_i1/* s1M0 */){
  var _i2/* s1M1 */ = E(_i1/* s1M0 */);
  if(!_i2/* s1M1 */._){
    return _i2/* s1M1 */.a;
  }else{
    return new F(function(){return I_toNumber/* EXTERNAL */(_i2/* s1M1 */.a);});
  }
},
_i3/* $fNumDouble_$cfromInteger */ = function(_i4/* s1l6n */){
  return new F(function(){return _i0/* GHC.Integer.Type.doubleFromInteger */(_i4/* s1l6n */);});
},
_i5/* $fNumDouble1 */ = 1,
_i6/* $fNumDouble2 */ =  -1,
_i7/* $fNumDouble_$csignum */ = function(_i8/* s1l6p */){
  var _i9/* s1l6q */ = E(_i8/* s1l6p */);
  return (_i9/* s1l6q */<=0) ? (_i9/* s1l6q */>=0) ? E(_i9/* s1l6q */) : E(_i6/* GHC.Float.$fNumDouble2 */) : E(_i5/* GHC.Float.$fNumDouble1 */);
},
_ia/* minusDouble */ = function(_ib/* s1kEA */, _ic/* s1kEB */){
  return E(_ib/* s1kEA */)-E(_ic/* s1kEB */);
},
_id/* negateDouble */ = function(_ie/* s1kEi */){
  return  -E(_ie/* s1kEi */);
},
_if/* plusDouble */ = function(_ig/* s1kEH */, _ih/* s1kEI */){
  return E(_ig/* s1kEH */)+E(_ih/* s1kEI */);
},
_ii/* timesDouble */ = function(_ij/* s1kEt */, _ik/* s1kEu */){
  return E(_ij/* s1kEt */)*E(_ik/* s1kEu */);
},
_il/* $fNumDouble */ = {_:0,a:_if/* GHC.Float.plusDouble */,b:_ia/* GHC.Float.minusDouble */,c:_ii/* GHC.Float.timesDouble */,d:_id/* GHC.Float.negateDouble */,e:_hW/* GHC.Float.$fNumDouble_$cabs */,f:_i7/* GHC.Float.$fNumDouble_$csignum */,g:_i3/* GHC.Float.$fNumDouble_$cfromInteger */},
_im/* divideDouble */ = function(_in/* s1kEm */, _io/* s1kEn */){
  return E(_in/* s1kEm */)/E(_io/* s1kEn */);
},
_ip/* $fFractionalDouble */ = new T4(0,_il/* GHC.Float.$fNumDouble */,_im/* GHC.Float.divideDouble */,_hU/* GHC.Float.$fFractionalDouble_$crecip */,_hR/* GHC.Float.$fFractionalDouble_$cfromRational */),
_iq/* acosDouble */ = function(_ir/* s1kCY */){
  return new F(function(){return Math.acos/* EXTERNAL */(E(_ir/* s1kCY */));});
},
_is/* asinDouble */ = function(_it/* s1kD2 */){
  return new F(function(){return Math.asin/* EXTERNAL */(E(_it/* s1kD2 */));});
},
_iu/* atanDouble */ = function(_iv/* s1kCU */){
  return new F(function(){return Math.atan/* EXTERNAL */(E(_iv/* s1kCU */));});
},
_iw/* cosDouble */ = function(_ix/* s1kDa */){
  return new F(function(){return Math.cos/* EXTERNAL */(E(_ix/* s1kDa */));});
},
_iy/* coshDouble */ = function(_iz/* s1kCM */){
  return new F(function(){return cosh/* EXTERNAL */(E(_iz/* s1kCM */));});
},
_iA/* expDouble */ = function(_iB/* s1kDq */){
  return new F(function(){return Math.exp/* EXTERNAL */(E(_iB/* s1kDq */));});
},
_iC/* logDouble */ = function(_iD/* s1kDm */){
  return new F(function(){return Math.log/* EXTERNAL */(E(_iD/* s1kDm */));});
},
_iE/* powerDouble */ = function(_iF/* s1kCB */, _iG/* s1kCC */){
  return new F(function(){return Math.pow/* EXTERNAL */(E(_iF/* s1kCB */), E(_iG/* s1kCC */));});
},
_iH/* sinDouble */ = function(_iI/* s1kDe */){
  return new F(function(){return Math.sin/* EXTERNAL */(E(_iI/* s1kDe */));});
},
_iJ/* sinhDouble */ = function(_iK/* s1kCQ */){
  return new F(function(){return sinh/* EXTERNAL */(E(_iK/* s1kCQ */));});
},
_iL/* sqrtDouble */ = function(_iM/* s1kDi */){
  return new F(function(){return Math.sqrt/* EXTERNAL */(E(_iM/* s1kDi */));});
},
_iN/* tanDouble */ = function(_iO/* s1kD6 */){
  return new F(function(){return Math.tan/* EXTERNAL */(E(_iO/* s1kD6 */));});
},
_iP/* tanhDouble */ = function(_iQ/* s1kCI */){
  return new F(function(){return tanh/* EXTERNAL */(E(_iQ/* s1kCI */));});
},
_iR/* $fFloatingDouble */ = {_:0,a:_ip/* GHC.Float.$fFractionalDouble */,b:_hQ/* GHC.Float.$fFloatingDouble_$cpi */,c:_iA/* GHC.Float.expDouble */,d:_iC/* GHC.Float.logDouble */,e:_iL/* GHC.Float.sqrtDouble */,f:_iE/* GHC.Float.powerDouble */,g:_hN/* GHC.Float.$fFloatingDouble_$clogBase */,h:_iH/* GHC.Float.sinDouble */,i:_iw/* GHC.Float.cosDouble */,j:_iN/* GHC.Float.tanDouble */,k:_is/* GHC.Float.asinDouble */,l:_iq/* GHC.Float.acosDouble */,m:_iu/* GHC.Float.atanDouble */,n:_iJ/* GHC.Float.sinhDouble */,o:_iy/* GHC.Float.coshDouble */,p:_iP/* GHC.Float.tanhDouble */,q:_hH/* GHC.Float.$fFloatingDouble_$casinh */,r:_hE/* GHC.Float.$fFloatingDouble_$cacosh */,s:_hK/* GHC.Float.$fFloatingDouble_$catanh */},
_iS/* $fEqDouble_$c/= */ = function(_iT/* scFY */, _iU/* scFZ */){
  return (E(_iT/* scFY */)!=E(_iU/* scFZ */)) ? true : false;
},
_iV/* $fEqDouble_$c== */ = function(_iW/* scFR */, _iX/* scFS */){
  return E(_iW/* scFR */)==E(_iX/* scFS */);
},
_iY/* $fEqDouble */ = new T2(0,_iV/* GHC.Classes.$fEqDouble_$c== */,_iS/* GHC.Classes.$fEqDouble_$c/= */),
_iZ/* $fOrdDouble_$c< */ = function(_j0/* scIb */, _j1/* scIc */){
  return E(_j0/* scIb */)<E(_j1/* scIc */);
},
_j2/* $fOrdDouble_$c<= */ = function(_j3/* scI4 */, _j4/* scI5 */){
  return E(_j3/* scI4 */)<=E(_j4/* scI5 */);
},
_j5/* $fOrdDouble_$c> */ = function(_j6/* scHX */, _j7/* scHY */){
  return E(_j6/* scHX */)>E(_j7/* scHY */);
},
_j8/* $fOrdDouble_$c>= */ = function(_j9/* scHQ */, _ja/* scHR */){
  return E(_j9/* scHQ */)>=E(_ja/* scHR */);
},
_jb/* $fOrdDouble_$ccompare */ = function(_jc/* scIi */, _jd/* scIj */){
  var _je/* scIk */ = E(_jc/* scIi */),
  _jf/* scIm */ = E(_jd/* scIj */);
  return (_je/* scIk */>=_jf/* scIm */) ? (_je/* scIk */!=_jf/* scIm */) ? 2 : 1 : 0;
},
_jg/* $fOrdDouble_$cmax */ = function(_jh/* scIA */, _ji/* scIB */){
  var _jj/* scIC */ = E(_jh/* scIA */),
  _jk/* scIE */ = E(_ji/* scIB */);
  return (_jj/* scIC */>_jk/* scIE */) ? E(_jj/* scIC */) : E(_jk/* scIE */);
},
_jl/* $fOrdDouble_$cmin */ = function(_jm/* scIs */, _jn/* scIt */){
  var _jo/* scIu */ = E(_jm/* scIs */),
  _jp/* scIw */ = E(_jn/* scIt */);
  return (_jo/* scIu */>_jp/* scIw */) ? E(_jp/* scIw */) : E(_jo/* scIu */);
},
_jq/* $fOrdDouble */ = {_:0,a:_iY/* GHC.Classes.$fEqDouble */,b:_jb/* GHC.Classes.$fOrdDouble_$ccompare */,c:_iZ/* GHC.Classes.$fOrdDouble_$c< */,d:_j2/* GHC.Classes.$fOrdDouble_$c<= */,e:_j5/* GHC.Classes.$fOrdDouble_$c> */,f:_j8/* GHC.Classes.$fOrdDouble_$c>= */,g:_jg/* GHC.Classes.$fOrdDouble_$cmax */,h:_jl/* GHC.Classes.$fOrdDouble_$cmin */},
_jr/* $sfitP1 */ = new T2(0,_iR/* GHC.Float.$fFloatingDouble */,_jq/* GHC.Classes.$fOrdDouble */),
_js/* $w$cdot */ = function(_jt/* s57h */, _ju/* s57i */, _jv/* s57j */, _jw/* s57k */, _jx/* s57l */, _jy/* s57m */, _jz/* s57n */){
  var _jA/* s57p */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_jt/* s57h */)))),
  _jB/* s57s */ = new T(function(){
    return B(A3(_6I/* GHC.Num.+ */,_jA/* s57p */, new T(function(){
      return B(A3(_7k/* GHC.Num.* */,_jA/* s57p */, _ju/* s57i */, _jx/* s57l */));
    }), new T(function(){
      return B(A3(_7k/* GHC.Num.* */,_jA/* s57p */, _jv/* s57j */, _jy/* s57m */));
    })));
  });
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_jA/* s57p */, _jB/* s57s */, new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_jA/* s57p */, _jw/* s57k */, _jz/* s57n */));
  }));});
},
_jC/* $w$cnormalize */ = function(_jD/* s583 */, _jE/* s584 */, _jF/* s585 */, _jG/* s586 */){
  var _jH/* s587 */ = B(_7g/* GHC.Float.$p1Floating */(_jD/* s583 */)),
  _jI/* s588 */ = new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_jD/* s583 */, new T(function(){
      return B(_js/* Lib.World.$w$cdot */(_jD/* s583 */, _jE/* s584 */, _jF/* s585 */, _jG/* s586 */, _jE/* s584 */, _jF/* s585 */, _jG/* s586 */));
    })));
  });
  return new T3(0,B(A3(_9b/* GHC.Real./ */,_jH/* s587 */, _jE/* s584 */, _jI/* s588 */)),B(A3(_9b/* GHC.Real./ */,_jH/* s587 */, _jF/* s585 */, _jI/* s588 */)),B(A3(_9b/* GHC.Real./ */,_jH/* s587 */, _jG/* s586 */, _jI/* s588 */)));
},
_jJ/* $w$c* */ = function(_jK/* s56f */, _jL/* s56g */, _jM/* s56h */, _jN/* s56i */, _jO/* s56j */, _jP/* s56k */, _jQ/* s56l */){
  var _jR/* s56m */ = B(_7k/* GHC.Num.* */(_jK/* s56f */));
  return new T3(0,B(A1(B(A1(_jR/* s56m */,_jL/* s56g */)),_jO/* s56j */)),B(A1(B(A1(_jR/* s56m */,_jM/* s56h */)),_jP/* s56k */)),B(A1(B(A1(_jR/* s56m */,_jN/* s56i */)),_jQ/* s56l */)));
},
_jS/* $w$c+ */ = function(_jT/* s56I */, _jU/* s56J */, _jV/* s56K */, _jW/* s56L */, _jX/* s56M */, _jY/* s56N */, _jZ/* s56O */){
  var _k0/* s56P */ = B(_6I/* GHC.Num.+ */(_jT/* s56I */));
  return new T3(0,B(A1(B(A1(_k0/* s56P */,_jU/* s56J */)),_jX/* s56M */)),B(A1(B(A1(_k0/* s56P */,_jV/* s56K */)),_jY/* s56N */)),B(A1(B(A1(_k0/* s56P */,_jW/* s56L */)),_jZ/* s56O */)));
},
_k1/* $wfitP */ = function(_k2/* s5f9 */, _k3/* s5fa */){
  var _k4/* s5fb */ = new T(function(){
    return E(E(_k2/* s5f9 */).a);
  }),
  _k5/* s5ff */ = new T(function(){
    return B(A2(_gS/* Lib.World.gradient */,new T2(0,_k4/* s5fb */,new T(function(){
      return E(E(_k2/* s5f9 */).b);
    })), _k3/* s5fa */));
  }),
  _k6/* s5fl */ = new T(function(){
    var _k7/* s5fm */ = E(_k5/* s5ff */),
    _k8/* s5fq */ = B(_jC/* Lib.World.$w$cnormalize */(_k4/* s5fb */, _k7/* s5fm */.a, _k7/* s5fm */.b, _k7/* s5fm */.c));
    return new T3(0,E(_k8/* s5fq */.a),E(_k8/* s5fq */.b),E(_k8/* s5fq */.c));
  }),
  _k9/* s5fY */ = new T(function(){
    var _ka/* s5fu */ = E(_k3/* s5fa */),
    _kb/* s5fv */ = _ka/* s5fu */.a,
    _kc/* s5fw */ = _ka/* s5fu */.b,
    _kd/* s5fx */ = _ka/* s5fu */.c,
    _ke/* s5fy */ = E(_k6/* s5fl */),
    _kf/* s5fC */ = B(_7g/* GHC.Float.$p1Floating */(_k4/* s5fb */)),
    _kg/* s5fJ */ = new T(function(){
      return B(A2(_7w/* GHC.Float.sqrt */,_k4/* s5fb */, new T(function(){
        var _kh/* s5fE */ = E(_k5/* s5ff */),
        _ki/* s5fF */ = _kh/* s5fE */.a,
        _kj/* s5fG */ = _kh/* s5fE */.b,
        _kk/* s5fH */ = _kh/* s5fE */.c;
        return B(_js/* Lib.World.$w$cdot */(_k4/* s5fb */, _ki/* s5fF */, _kj/* s5fG */, _kk/* s5fH */, _ki/* s5fF */, _kj/* s5fG */, _kk/* s5fH */));
      })));
    }),
    _kl/* s5fK */ = B(A3(_9b/* GHC.Real./ */,_kf/* s5fC */, new T(function(){
      return B(_7y/* Lib.World.$wfield */(_k4/* s5fb */, _kb/* s5fv */, _kc/* s5fw */, _kd/* s5fx */));
    }), _kg/* s5fJ */)),
    _km/* s5fL */ = B(_7i/* GHC.Real.$p1Fractional */(_kf/* s5fC */)),
    _kn/* s5fM */ = B(_jJ/* Lib.World.$w$c* */(_km/* s5fL */, _ke/* s5fy */.a, _ke/* s5fy */.b, _ke/* s5fy */.c, _kl/* s5fK */, _kl/* s5fK */, _kl/* s5fK */)),
    _ko/* s5fQ */ = B(_6K/* GHC.Num.negate */(_km/* s5fL */)),
    _kp/* s5fU */ = B(_jS/* Lib.World.$w$c+ */(_km/* s5fL */, _kb/* s5fv */, _kc/* s5fw */, _kd/* s5fx */, B(A1(_ko/* s5fQ */,_kn/* s5fM */.a)), B(A1(_ko/* s5fQ */,_kn/* s5fM */.b)), B(A1(_ko/* s5fQ */,_kn/* s5fM */.c))));
    return new T3(0,E(_kp/* s5fU */.a),E(_kp/* s5fU */.b),E(_kp/* s5fU */.c));
  });
  return new T2(0,_k9/* s5fY */,_k6/* s5fl */);
},
_kq/* $p1Ord */ = function(_kr/* scBS */){
  return E(E(_kr/* scBS */).a);
},
_ks/* $wperpTo */ = function(_kt/* s58q */, _ku/* s58r */, _kv/* s58s */, _kw/* s58t */, _kx/* s58u */, _ky/* s58v */, _kz/* s58w */){
  var _kA/* s58x */ = B(_js/* Lib.World.$w$cdot */(_kt/* s58q */, _kx/* s58u */, _ky/* s58v */, _kz/* s58w */, _ku/* s58r */, _kv/* s58s */, _kw/* s58t */)),
  _kB/* s58z */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_kt/* s58q */)))),
  _kC/* s58A */ = B(_jJ/* Lib.World.$w$c* */(_kB/* s58z */, _kx/* s58u */, _ky/* s58v */, _kz/* s58w */, _kA/* s58x */, _kA/* s58x */, _kA/* s58x */)),
  _kD/* s58E */ = B(_6K/* GHC.Num.negate */(_kB/* s58z */));
  return new F(function(){return _jS/* Lib.World.$w$c+ */(_kB/* s58z */, _ku/* s58r */, _kv/* s58s */, _kw/* s58t */, B(A1(_kD/* s58E */,_kC/* s58A */.a)), B(A1(_kD/* s58E */,_kC/* s58A */.b)), B(A1(_kD/* s58E */,_kC/* s58A */.c)));});
},
_kE/* == */ = function(_kF/* scBK */){
  return E(E(_kF/* scBK */).a);
},
_kG/* $wfitV */ = function(_kH/* s590 */, _kI/* s591 */, _kJ/* s592 */, _kK/* s593 */){
  var _kL/* s594 */ = new T(function(){
    var _kM/* s595 */ = E(_kK/* s593 */),
    _kN/* s599 */ = E(_kJ/* s592 */),
    _kO/* s59d */ = B(_ks/* Lib.World.$wperpTo */(_kH/* s590 */, _kM/* s595 */.a, _kM/* s595 */.b, _kM/* s595 */.c, _kN/* s599 */.a, _kN/* s599 */.b, _kN/* s599 */.c));
    return new T3(0,E(_kO/* s59d */.a),E(_kO/* s59d */.b),E(_kO/* s59d */.c));
  }),
  _kP/* s59n */ = new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_kH/* s590 */, new T(function(){
      var _kQ/* s59i */ = E(_kL/* s594 */),
      _kR/* s59j */ = _kQ/* s59i */.a,
      _kS/* s59k */ = _kQ/* s59i */.b,
      _kT/* s59l */ = _kQ/* s59i */.c;
      return B(_js/* Lib.World.$w$cdot */(_kH/* s590 */, _kR/* s59j */, _kS/* s59k */, _kT/* s59l */, _kR/* s59j */, _kS/* s59k */, _kT/* s59l */));
    })));
  });
  if(!B(A3(_kE/* GHC.Classes.== */,B(_kq/* GHC.Classes.$p1Ord */(_kI/* s591 */)), _kP/* s59n */, new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_kH/* s590 */)))), _90/* Lib.World.$fArithWorld1 */));
  })))){
    var _kU/* s59s */ = E(_kL/* s594 */),
    _kV/* s59w */ = B(_jC/* Lib.World.$w$cnormalize */(_kH/* s590 */, _kU/* s59s */.a, _kU/* s59s */.b, _kU/* s59s */.c)),
    _kW/* s59F */ = B(A2(_7w/* GHC.Float.sqrt */,_kH/* s590 */, new T(function(){
      var _kX/* s59A */ = E(_kK/* s593 */),
      _kY/* s59B */ = _kX/* s59A */.a,
      _kZ/* s59C */ = _kX/* s59A */.b,
      _l0/* s59D */ = _kX/* s59A */.c;
      return B(_js/* Lib.World.$w$cdot */(_kH/* s590 */, _kY/* s59B */, _kZ/* s59C */, _l0/* s59D */, _kY/* s59B */, _kZ/* s59C */, _l0/* s59D */));
    }))),
    _l1/* s59I */ = B(_7k/* GHC.Num.* */(new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_kH/* s590 */));
      })));
    })));
    return new T3(0,B(A1(B(A1(_l1/* s59I */,_kV/* s59w */.a)),_kW/* s59F */)),B(A1(B(A1(_l1/* s59I */,_kV/* s59w */.b)),_kW/* s59F */)),B(A1(B(A1(_l1/* s59I */,_kV/* s59w */.c)),_kW/* s59F */)));
  }else{
    var _l2/* s59R */ = B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_kH/* s590 */)))), _90/* Lib.World.$fArithWorld1 */));
    return new T3(0,_l2/* s59R */,_l2/* s59R */,_l2/* s59R */);
  }
},
_l3/* angleCount */ = new T(function(){
  var _l4/* s6nL */ = eval/* EXTERNAL */("angleCount"),
  _l5/* s6nP */ = Number/* EXTERNAL */(_l4/* s6nL */);
  return jsTrunc/* EXTERNAL */(_l5/* s6nP */);
}),
_l6/* aN */ = new T(function(){
  return E(_l3/* Lib.Util.angleCount */);
}),
_l7/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_l8/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_l9/* errorEmptyList */ = function(_la/* sbDG */){
  return new F(function(){return err/* EXTERNAL */(B(_f/* GHC.Base.++ */(_l8/* GHC.List.prel_list_str */, new T(function(){
    return B(_f/* GHC.Base.++ */(_la/* sbDG */, _l7/* GHC.List.lvl */));
  },1))));});
},
_lb/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("head"));
}),
_lc/* badHead */ = new T(function(){
  return B(_l9/* GHC.List.errorEmptyList */(_lb/* GHC.List.lvl18 */));
}),
_ld/* go1 */ = function(_le/* sfzE */, _lf/* sfzF */, _lg/* sfzG */){
  var _lh/* sfzH */ = E(_le/* sfzE */);
  if(!_lh/* sfzH */._){
    return __Z/* EXTERNAL */;
  }else{
    var _li/* sfzK */ = E(_lf/* sfzF */);
    if(!_li/* sfzK */._){
      return __Z/* EXTERNAL */;
    }else{
      var _lj/* sfzL */ = _li/* sfzK */.a,
      _lk/* sfzN */ = E(_lg/* sfzG */);
      if(!_lk/* sfzN */._){
        return __Z/* EXTERNAL */;
      }else{
        var _ll/* sfzQ */ = E(_lk/* sfzN */.a),
        _lm/* sfzR */ = _ll/* sfzQ */.a;
        return new F(function(){return _f/* GHC.Base.++ */(new T2(1,new T(function(){
          return new T3(0,E(_lh/* sfzH */.a),E(_lj/* sfzL */),E(_lm/* sfzR */));
        }),new T2(1,new T(function(){
          return new T3(0,E(_lj/* sfzL */),E(_lm/* sfzR */),E(_ll/* sfzQ */.b));
        }),_o/* GHC.Types.[] */)), new T(function(){
          return B(_ld/* Lib.Object.go1 */(_lh/* sfzH */.b, _li/* sfzK */.b, _lk/* sfzN */.b));
        },1));});
      }
    }
  }
},
_ln/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tail"));
}),
_lo/* tail1 */ = new T(function(){
  return B(_l9/* GHC.List.errorEmptyList */(_ln/* GHC.List.lvl17 */));
}),
_lp/* zip */ = function(_lq/* sbOD */, _lr/* sbOE */){
  var _ls/* sbOF */ = E(_lq/* sbOD */);
  if(!_ls/* sbOF */._){
    return __Z/* EXTERNAL */;
  }else{
    var _lt/* sbOI */ = E(_lr/* sbOE */);
    return (_lt/* sbOI */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T2(0,_ls/* sbOF */.a,_lt/* sbOI */.a),new T(function(){
      return B(_lp/* GHC.List.zip */(_ls/* sbOF */.b, _lt/* sbOI */.b));
    }));
  }
},
_lu/* go2 */ = function(_lv/* sfAm */, _lw/* sfAn */){
  var _lx/* sfAo */ = E(_lv/* sfAm */);
  if(!_lx/* sfAo */._){
    return __Z/* EXTERNAL */;
  }else{
    var _ly/* sfAr */ = E(_lw/* sfAn */);
    if(!_ly/* sfAr */._){
      return __Z/* EXTERNAL */;
    }else{
      var _lz/* sfAu */ = E(_lx/* sfAo */.a),
      _lA/* sfAw */ = _lz/* sfAu */.b,
      _lB/* sfAz */ = E(_ly/* sfAr */.a).b,
      _lC/* sfB4 */ = new T(function(){
        var _lD/* sfB3 */ = new T(function(){
          return B(_lp/* GHC.List.zip */(_lB/* sfAz */, new T(function(){
            var _lE/* sfAZ */ = E(_lB/* sfAz */);
            if(!_lE/* sfAZ */._){
              return E(_lo/* GHC.List.tail1 */);
            }else{
              return E(_lE/* sfAZ */.b);
            }
          },1)));
        },1);
        return B(_ld/* Lib.Object.go1 */(_lA/* sfAw */, new T(function(){
          var _lF/* sfAV */ = E(_lA/* sfAw */);
          if(!_lF/* sfAV */._){
            return E(_lo/* GHC.List.tail1 */);
          }else{
            return E(_lF/* sfAV */.b);
          }
        },1), _lD/* sfB3 */));
      });
      return new F(function(){return _f/* GHC.Base.++ */(new T2(1,new T(function(){
        var _lG/* sfAE */ = E(_lA/* sfAw */);
        if(!_lG/* sfAE */._){
          return E(_lc/* GHC.List.badHead */);
        }else{
          var _lH/* sfAM */ = E(_lB/* sfAz */);
          if(!_lH/* sfAM */._){
            return E(_lc/* GHC.List.badHead */);
          }else{
            return new T3(0,E(_lz/* sfAu */.a),E(_lG/* sfAE */.a),E(_lH/* sfAM */.a));
          }
        }
      }),_lC/* sfB4 */), new T(function(){
        return B(_lu/* Lib.Object.go2 */(_lx/* sfAo */.b, _ly/* sfAr */.b));
      },1));});
    }
  }
},
_lI/* lvl2 */ = new T(function(){
  return E(_l6/* Lib.Object.aN */)-1;
}),
_lJ/* $fEnumRatio1 */ = new T1(0,1),
_lK/* $wnumericEnumFrom */ = function(_lL/* svpc */, _lM/* svpd */){
  var _lN/* svpe */ = E(_lM/* svpd */),
  _lO/* svpl */ = new T(function(){
    var _lP/* svpf */ = B(_7i/* GHC.Real.$p1Fractional */(_lL/* svpc */)),
    _lQ/* svpi */ = B(_lK/* GHC.Real.$wnumericEnumFrom */(_lL/* svpc */, B(A3(_6I/* GHC.Num.+ */,_lP/* svpf */, _lN/* svpe */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_lP/* svpf */, _lJ/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_lQ/* svpi */.a,_lQ/* svpi */.b);
  });
  return new T2(0,_lN/* svpe */,_lO/* svpl */);
},
_lR/* <= */ = function(_lS/* scCm */){
  return E(E(_lS/* scCm */).d);
},
_lT/* even2 */ = new T1(0,2),
_lU/* takeWhile */ = function(_lV/* sbJ5 */, _lW/* sbJ6 */){
  var _lX/* sbJ7 */ = E(_lW/* sbJ6 */);
  if(!_lX/* sbJ7 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _lY/* sbJ8 */ = _lX/* sbJ7 */.a;
    return (!B(A1(_lV/* sbJ5 */,_lY/* sbJ8 */))) ? __Z/* EXTERNAL */ : new T2(1,_lY/* sbJ8 */,new T(function(){
      return B(_lU/* GHC.List.takeWhile */(_lV/* sbJ5 */, _lX/* sbJ7 */.b));
    }));
  }
},
_lZ/* numericEnumFromTo */ = function(_m0/* svpS */, _m1/* svpT */, _m2/* svpU */, _m3/* svpV */){
  var _m4/* svpW */ = B(_lK/* GHC.Real.$wnumericEnumFrom */(_m1/* svpT */, _m2/* svpU */)),
  _m5/* svpZ */ = new T(function(){
    var _m6/* svq0 */ = B(_7i/* GHC.Real.$p1Fractional */(_m1/* svpT */)),
    _m7/* svq3 */ = new T(function(){
      return B(A3(_9b/* GHC.Real./ */,_m1/* svpT */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_m6/* svq0 */, _lJ/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_m6/* svq0 */, _lT/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_6I/* GHC.Num.+ */,_m6/* svq0 */, _m3/* svpV */, _m7/* svq3 */));
  });
  return new F(function(){return _lU/* GHC.List.takeWhile */(function(_m8/* svq4 */){
    return new F(function(){return A3(_lR/* GHC.Classes.<= */,_m0/* svpS */, _m8/* svq4 */, _m5/* svpZ */);});
  }, new T2(1,_m4/* svpW */.a,_m4/* svpW */.b));});
},
_m9/* lvl3 */ = new T(function(){
  return B(_lZ/* GHC.Real.numericEnumFromTo */(_jq/* GHC.Classes.$fOrdDouble */, _ip/* GHC.Float.$fFractionalDouble */, _hm/* Lib.Object.$fNumPos1 */, _lI/* Lib.Object.lvl2 */));
}),
_ma/* go */ = function(_mb/* sfko */, _mc/* sfkp */){
  while(1){
    var _md/* sfkq */ = E(_mb/* sfko */);
    if(!_md/* sfkq */._){
      return E(_mc/* sfkp */);
    }else{
      _mb/* sfko */ = _md/* sfkq */.b;
      _mc/* sfkp */ = _md/* sfkq */.a;
      continue;
    }
  }
},
_me/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_mf/* last1 */ = new T(function(){
  return B(_l9/* GHC.List.errorEmptyList */(_me/* GHC.List.lvl16 */));
}),
_mg/* $wlvl */ = function(_mh/* sfkt */){
  return new F(function(){return _ma/* Lib.Object.go */(_mh/* sfkt */, _mf/* GHC.List.last1 */);});
},
_mi/* lvl4 */ = function(_mj/* sfku */){
  return new F(function(){return _mg/* Lib.Object.$wlvl */(E(_mj/* sfku */).b);});
},
_mk/* map */ = function(_ml/* s3hr */, _mm/* s3hs */){
  var _mn/* s3ht */ = E(_mm/* s3hs */);
  return (_mn/* s3ht */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T(function(){
    return B(A1(_ml/* s3hr */,_mn/* s3ht */.a));
  }),new T(function(){
    return B(_mk/* GHC.Base.map */(_ml/* s3hr */, _mn/* s3ht */.b));
  }));
},
_mo/* proceedCount */ = new T(function(){
  var _mp/* s6nZ */ = eval/* EXTERNAL */("proceedCount"),
  _mq/* s6o3 */ = Number/* EXTERNAL */(_mp/* s6nZ */);
  return jsTrunc/* EXTERNAL */(_mq/* s6o3 */);
}),
_mr/* pC */ = new T(function(){
  return E(_mo/* Lib.Util.proceedCount */);
}),
_ms/* $s^2 */ = 1,
_mt/* x */ = new T(function(){
  return B(_lZ/* GHC.Real.numericEnumFromTo */(_jq/* GHC.Classes.$fOrdDouble */, _ip/* GHC.Float.$fFractionalDouble */, _ms/* Lib.Object.$s^2 */, _mr/* Lib.Object.pC */));
}),
_mu/* $wgeneratePolygon */ = function(_mv/* sfB7 */, _mw/* sfB8 */, _mx/* sfB9 */, _my/* sfBa */, _mz/* sfBb */, _mA/* sfBc */, _mB/* sfBd */, _mC/* sfBe */, _mD/* sfBf */, _mE/* sfBg */, _mF/* sfBh */, _mG/* sfBi */, _mH/* sfBj */, _mI/* sfBk */, _mJ/* sfBl */, _mK/* sfBm */){
  var _mL/* sfBn */ = new T(function(){
    var _mM/* sfBo */ = new T(function(){
      var _mN/* sfBp */ = E(_mE/* sfBg */),
      _mO/* sfBr */ = E(_mI/* sfBk */),
      _mP/* sfBt */ = E(_mH/* sfBj */),
      _mQ/* sfBv */ = E(_mF/* sfBh */),
      _mR/* sfBx */ = E(_mG/* sfBi */),
      _mS/* sfBz */ = E(_mD/* sfBf */);
      return new T3(0,_mN/* sfBp */*_mO/* sfBr */-_mP/* sfBt */*_mQ/* sfBv */,_mQ/* sfBv */*_mR/* sfBx */-_mO/* sfBr */*_mS/* sfBz */,_mS/* sfBz */*_mP/* sfBt */-_mR/* sfBx */*_mN/* sfBp */);
    }),
    _mT/* sfGi */ = function(_mU/* sfBO */){
      var _mV/* sfBP */ = new T(function(){
        var _mW/* sfBU */ = E(_mU/* sfBO */)/E(_l6/* Lib.Object.aN */);
        return (_mW/* sfBU */+_mW/* sfBU */)*3.141592653589793;
      }),
      _mX/* sfBX */ = new T(function(){
        return B(A1(_mv/* sfB7 */,_mV/* sfBP */));
      }),
      _mY/* sfGh */ = new T(function(){
        var _mZ/* sfC4 */ = new T(function(){
          var _n0/* sfC9 */ = E(_mX/* sfBX */)/E(_mr/* Lib.Object.pC */);
          return new T3(0,E(_n0/* sfC9 */),E(_n0/* sfC9 */),E(_n0/* sfC9 */));
        }),
        _n1/* sfCc */ = function(_n2/* sfDU */, _n3/* sfDV */){
          var _n4/* sfDW */ = E(_n2/* sfDU */);
          if(!_n4/* sfDW */._){
            return new T2(0,_o/* GHC.Types.[] */,_n3/* sfDV */);
          }else{
            var _n5/* sfDZ */ = new T(function(){
              var _n6/* sfEH */ = B(_k1/* Lib.World.$wfitP */(_jr/* Lib.Object.$sfitP1 */, new T(function(){
                var _n7/* sfE0 */ = E(_n3/* sfDV */),
                _n8/* sfE3 */ = E(_n7/* sfE0 */.a),
                _n9/* sfEd */ = E(_n7/* sfE0 */.b),
                _na/* sfEn */ = E(_mZ/* sfC4 */);
                return new T3(0,E(_n8/* sfE3 */.a)+E(_n9/* sfEd */.a)*E(_na/* sfEn */.a),E(_n8/* sfE3 */.b)+E(_n9/* sfEd */.b)*E(_na/* sfEn */.b),E(_n8/* sfE3 */.c)+E(_n9/* sfEd */.c)*E(_na/* sfEn */.c));
              }))),
              _nb/* sfEI */ = _n6/* sfEH */.a;
              return new T2(0,new T(function(){
                var _nc/* sfES */ = E(_mX/* sfBX */),
                _nd/* sfEU */ = E(_mV/* sfBP */);
                return new T3(0,E(_nb/* sfEI */),E(new T2(0,E(_n4/* sfDW */.a)/E(_mr/* Lib.Object.pC */),E(_nc/* sfES */))),E(_nd/* sfEU */));
              }),new T2(0,_nb/* sfEI */,new T(function(){
                var _ne/* sfF3 */ = E(_n6/* sfEH */.b),
                _nf/* sfF7 */ = E(E(_n3/* sfDV */).b),
                _ng/* sfFb */ = B(_ks/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _nf/* sfF7 */.a, _nf/* sfF7 */.b, _nf/* sfF7 */.c, _ne/* sfF3 */.a, _ne/* sfF3 */.b, _ne/* sfF3 */.c)),
                _nh/* sfFf */ = B(_jC/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _ng/* sfFb */.a, _ng/* sfFb */.b, _ng/* sfFb */.c));
                return new T3(0,E(_nh/* sfFf */.a),E(_nh/* sfFf */.b),E(_nh/* sfFf */.c));
              })));
            }),
            _ni/* sfFl */ = new T(function(){
              var _nj/* sfFq */ = B(_n1/* sfCc */(_n4/* sfDW */.b, new T(function(){
                return E(E(_n5/* sfDZ */).b);
              })));
              return new T2(0,_nj/* sfFq */.a,_nj/* sfFq */.b);
            });
            return new T2(0,new T2(1,new T(function(){
              return E(E(_n5/* sfDZ */).a);
            }),new T(function(){
              return E(E(_ni/* sfFl */).a);
            })),new T(function(){
              return E(E(_ni/* sfFl */).b);
            }));
          }
        },
        _nk/* sfCb */ = function(_nl/* sfCd */, _nm/* sfCe */, _nn/* sfCf */, _no/* sfCg */, _np/* sfCh */){
          var _nq/* sfCi */ = E(_nl/* sfCd */);
          if(!_nq/* sfCi */._){
            return new T2(0,_o/* GHC.Types.[] */,new T2(0,new T3(0,E(_nm/* sfCe */),E(_nn/* sfCf */),E(_no/* sfCg */)),_np/* sfCh */));
          }else{
            var _nr/* sfCn */ = new T(function(){
              var _ns/* sfCY */ = B(_k1/* Lib.World.$wfitP */(_jr/* Lib.Object.$sfitP1 */, new T(function(){
                var _nt/* sfCu */ = E(_np/* sfCh */),
                _nu/* sfCE */ = E(_mZ/* sfC4 */);
                return new T3(0,E(_nm/* sfCe */)+E(_nt/* sfCu */.a)*E(_nu/* sfCE */.a),E(_nn/* sfCf */)+E(_nt/* sfCu */.b)*E(_nu/* sfCE */.b),E(_no/* sfCg */)+E(_nt/* sfCu */.c)*E(_nu/* sfCE */.c));
              }))),
              _nv/* sfCZ */ = _ns/* sfCY */.a;
              return new T2(0,new T(function(){
                var _nw/* sfD9 */ = E(_mX/* sfBX */),
                _nx/* sfDb */ = E(_mV/* sfBP */);
                return new T3(0,E(_nv/* sfCZ */),E(new T2(0,E(_nq/* sfCi */.a)/E(_mr/* Lib.Object.pC */),E(_nw/* sfD9 */))),E(_nx/* sfDb */));
              }),new T2(0,_nv/* sfCZ */,new T(function(){
                var _ny/* sfDh */ = E(_ns/* sfCY */.b),
                _nz/* sfDl */ = E(_np/* sfCh */),
                _nA/* sfDp */ = B(_ks/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _nz/* sfDl */.a, _nz/* sfDl */.b, _nz/* sfDl */.c, _ny/* sfDh */.a, _ny/* sfDh */.b, _ny/* sfDh */.c)),
                _nB/* sfDt */ = B(_jC/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _nA/* sfDp */.a, _nA/* sfDp */.b, _nA/* sfDp */.c));
                return new T3(0,E(_nB/* sfDt */.a),E(_nB/* sfDt */.b),E(_nB/* sfDt */.c));
              })));
            }),
            _nC/* sfDz */ = new T(function(){
              var _nD/* sfDE */ = B(_n1/* sfCc */(_nq/* sfCi */.b, new T(function(){
                return E(E(_nr/* sfCn */).b);
              })));
              return new T2(0,_nD/* sfDE */.a,_nD/* sfDE */.b);
            });
            return new T2(0,new T2(1,new T(function(){
              return E(E(_nr/* sfCn */).a);
            }),new T(function(){
              return E(E(_nC/* sfDz */).a);
            })),new T(function(){
              return E(E(_nC/* sfDz */).b);
            }));
          }
        };
        return E(B(_nk/* sfCb */(_mt/* Lib.Object.x */, _my/* sfBa */, _mz/* sfBb */, _mA/* sfBc */, new T(function(){
          var _nE/* sfFO */ = E(_mM/* sfBo */),
          _nF/* sfFY */ = E(_mV/* sfBP */)+_mB/* sfBd */,
          _nG/* sfFZ */ = Math.cos/* EXTERNAL */(_nF/* sfFY */),
          _nH/* sfG0 */ = Math.sin/* EXTERNAL */(_nF/* sfFY */);
          return new T3(0,E(_mD/* sfBf */)*_nG/* sfFZ */+E(_nE/* sfFO */.a)*_nH/* sfG0 */,E(_mE/* sfBg */)*_nG/* sfFZ */+E(_nE/* sfFO */.b)*_nH/* sfG0 */,E(_mF/* sfBh */)*_nG/* sfFZ */+E(_nE/* sfFO */.c)*_nH/* sfG0 */);
        }))).a);
      });
      return new T2(0,new T(function(){
        var _nI/* sfBY */ = E(_mX/* sfBX */),
        _nJ/* sfC0 */ = E(_mV/* sfBP */);
        return new T3(0,E(new T3(0,E(_my/* sfBa */),E(_mz/* sfBb */),E(_mA/* sfBc */))),E(new T2(0,E(_hm/* Lib.Object.$fNumPos1 */),E(_nI/* sfBY */))),E(_nJ/* sfC0 */));
      }),_mY/* sfGh */);
    };
    return B(_mk/* GHC.Base.map */(_mT/* sfGi */, _m9/* Lib.Object.lvl3 */));
  }),
  _nK/* sfGs */ = new T(function(){
    var _nL/* sfGr */ = new T(function(){
      var _nM/* sfGo */ = B(_f/* GHC.Base.++ */(_mL/* sfBn */, new T2(1,new T(function(){
        var _nN/* sfGj */ = E(_mL/* sfBn */);
        if(!_nN/* sfGj */._){
          return E(_lc/* GHC.List.badHead */);
        }else{
          return E(_nN/* sfGj */.a);
        }
      }),_o/* GHC.Types.[] */)));
      if(!_nM/* sfGo */._){
        return E(_lo/* GHC.List.tail1 */);
      }else{
        return E(_nM/* sfGo */.b);
      }
    },1);
    return B(_lu/* Lib.Object.go2 */(_mL/* sfBn */, _nL/* sfGr */));
  });
  return new T2(0,_nK/* sfGs */,new T(function(){
    return B(_mk/* GHC.Base.map */(_mi/* Lib.Object.lvl4 */, _mL/* sfBn */));
  }));
},
_nO/* $wfitO */ = function(_nP/* sfGZ */, _nQ/* sfH0 */, _nR/* sfH1 */, _nS/* sfH2 */, _nT/* sfH3 */, _nU/* sfH4 */, _nV/* sfH5 */, _nW/* sfH6 */, _nX/* sfH7 */, _nY/* sfH8 */, _nZ/* sfH9 */, _o0/* sfHa */, _o1/* sfHb */, _o2/* sfHc */, _o3/* sfHd */, _o4/* sfHe */, _o5/* sfHf */){
  var _o6/* sfHh */ = B(_k1/* Lib.World.$wfitP */(_jr/* Lib.Object.$sfitP1 */, new T3(0,E(_nS/* sfH2 */),E(_nT/* sfH3 */),E(_nU/* sfH4 */)))),
  _o7/* sfHj */ = _o6/* sfHh */.b,
  _o8/* sfHk */ = E(_o6/* sfHh */.a),
  _o9/* sfHp */ = B(_kG/* Lib.World.$wfitV */(_iR/* GHC.Float.$fFloatingDouble */, _jq/* GHC.Classes.$fOrdDouble */, _o7/* sfHj */, new T3(0,E(_nW/* sfH6 */),E(_nX/* sfH7 */),E(_nY/* sfH8 */)))),
  _oa/* sfHt */ = E(_o7/* sfHj */),
  _ob/* sfHu */ = _oa/* sfHt */.a,
  _oc/* sfHv */ = _oa/* sfHt */.b,
  _od/* sfHw */ = _oa/* sfHt */.c,
  _oe/* sfHx */ = B(_ks/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _o0/* sfHa */, _o1/* sfHb */, _o2/* sfHc */, _ob/* sfHu */, _oc/* sfHv */, _od/* sfHw */)),
  _of/* sfHB */ = B(_jC/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _oe/* sfHx */.a, _oe/* sfHx */.b, _oe/* sfHx */.c)),
  _og/* sfHC */ = _of/* sfHB */.a,
  _oh/* sfHD */ = _of/* sfHB */.b,
  _oi/* sfHE */ = _of/* sfHB */.c,
  _oj/* sfHF */ = E(_nV/* sfH5 */),
  _ok/* sfHI */ = new T2(0,E(new T3(0,E(_o9/* sfHp */.a),E(_o9/* sfHp */.b),E(_o9/* sfHp */.c))),E(_nZ/* sfH9 */)),
  _ol/* sfHJ */ = B(_mu/* Lib.Object.$wgeneratePolygon */(_nP/* sfGZ */, _nQ/* sfH0 */, _nR/* sfH1 */, _o8/* sfHk */.a, _o8/* sfHk */.b, _o8/* sfHk */.c, _oj/* sfHF */, _ok/* sfHI */, _og/* sfHC */, _oh/* sfHD */, _oi/* sfHE */, _ob/* sfHu */, _oc/* sfHv */, _od/* sfHw */, _o4/* sfHe */, _o5/* sfHf */));
  return {_:0,a:_nP/* sfGZ */,b:_nQ/* sfH0 */,c:_nR/* sfH1 */,d:new T2(0,E(_o8/* sfHk */),E(_oj/* sfHF */)),e:_ok/* sfHI */,f:new T3(0,E(_og/* sfHC */),E(_oh/* sfHD */),E(_oi/* sfHE */)),g:_oa/* sfHt */,h:E(_ol/* sfHJ */.a),i:E(_ol/* sfHJ */.b)};
},
_om/* lvl1 */ = new T(function(){
  return 6.283185307179586/E(_l6/* Lib.Object.aN */);
}),
_on/* dt */ =  -1,
_oo/* dt1 */ = 0.5,
_op/* lvl26 */ = new T3(0,E(_hm/* Lib.Object.$fNumPos1 */),E(_oo/* Lib.Object.dt1 */),E(_on/* Lib.Object.dt */)),
_oq/* $wmake */ = function(_or/* sg1f */, _os/* sg1g */, _ot/* sg1h */, _ou/* sg1i */, _ov/* sg1j */, _ow/* sg1k */, _ox/* sg1l */, _oy/* sg1m */, _oz/* sg1n */, _oA/* sg1o */, _oB/* sg1p */, _oC/* sg1q */, _oD/* sg1r */){
  var _oE/* sg1s */ = function(_oF/* sg1t */){
    var _oG/* sg1u */ = E(_om/* Lib.Object.lvl1 */),
    _oH/* sg1w */ = 2+_oF/* sg1t */|0,
    _oI/* sg1y */ = _oH/* sg1w */-1|0,
    _oJ/* sg1z */ = (2+_oF/* sg1t */)*(1+_oF/* sg1t */),
    _oK/* sg1E */ = E(_m9/* Lib.Object.lvl3 */);
    if(!_oK/* sg1E */._){
      return _oG/* sg1u */*0;
    }else{
      var _oL/* sg1F */ = _oK/* sg1E */.a,
      _oM/* sg1G */ = _oK/* sg1E */.b,
      _oN/* sg1O */ = B(A1(_or/* sg1f */,new T(function(){
        return 6.283185307179586*E(_oL/* sg1F */)/E(_l6/* Lib.Object.aN */);
      }))),
      _oO/* sg1Y */ = B(A1(_or/* sg1f */,new T(function(){
        return 6.283185307179586*(E(_oL/* sg1F */)+1)/E(_l6/* Lib.Object.aN */);
      })));
      if(_oN/* sg1O */!=_oO/* sg1Y */){
        if(_oH/* sg1w */>=0){
          var _oP/* sg24 */ = E(_oH/* sg1w */);
          if(!_oP/* sg24 */){
            var _oQ/* sg30 */ = function(_oR/*  sg31 */, _oS/*  sg32 */){
              while(1){
                var _oT/*  sg30 */ = B((function(_oU/* sg31 */, _oV/* sg32 */){
                  var _oW/* sg33 */ = E(_oU/* sg31 */);
                  if(!_oW/* sg33 */._){
                    return E(_oV/* sg32 */);
                  }else{
                    var _oX/* sg34 */ = _oW/* sg33 */.a,
                    _oY/* sg35 */ = _oW/* sg33 */.b,
                    _oZ/* sg3d */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*E(_oX/* sg34 */)/E(_l6/* Lib.Object.aN */);
                    }))),
                    _p0/* sg3n */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*(E(_oX/* sg34 */)+1)/E(_l6/* Lib.Object.aN */);
                    })));
                    if(_oZ/* sg3d */!=_p0/* sg3n */){
                      var _p1/*   sg32 */ = _oV/* sg32 */+0/(_oZ/* sg3d */-_p0/* sg3n */)/_oJ/* sg1z */;
                      _oR/*  sg31 */ = _oY/* sg35 */;
                      _oS/*  sg32 */ = _p1/*   sg32 */;
                      return __continue/* EXTERNAL */;
                    }else{
                      if(_oI/* sg1y */>=0){
                        var _p2/* sg3x */ = E(_oI/* sg1y */);
                        if(!_p2/* sg3x */){
                          var _p1/*   sg32 */ = _oV/* sg32 */+_oH/* sg1w *//_oJ/* sg1z */;
                          _oR/*  sg31 */ = _oY/* sg35 */;
                          _oS/*  sg32 */ = _p1/*   sg32 */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _p1/*   sg32 */ = _oV/* sg32 */+_oH/* sg1w */*B(_hy/* Lib.Object.$wf */(_oZ/* sg3d */, _p2/* sg3x */))/_oJ/* sg1z */;
                          _oR/*  sg31 */ = _oY/* sg35 */;
                          _oS/*  sg32 */ = _p1/*   sg32 */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_oR/*  sg31 */, _oS/*  sg32 */));
                if(_oT/*  sg30 */!=__continue/* EXTERNAL */){
                  return _oT/*  sg30 */;
                }
              }
            };
            return _oG/* sg1u */*B(_oQ/* sg30 */(_oM/* sg1G */, 0/(_oN/* sg1O */-_oO/* sg1Y */)/_oJ/* sg1z */));
          }else{
            var _p3/* sg2b */ = function(_p4/*  sg2c */, _p5/*  sg2d */){
              while(1){
                var _p6/*  sg2b */ = B((function(_p7/* sg2c */, _p8/* sg2d */){
                  var _p9/* sg2e */ = E(_p7/* sg2c */);
                  if(!_p9/* sg2e */._){
                    return E(_p8/* sg2d */);
                  }else{
                    var _pa/* sg2f */ = _p9/* sg2e */.a,
                    _pb/* sg2g */ = _p9/* sg2e */.b,
                    _pc/* sg2o */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*E(_pa/* sg2f */)/E(_l6/* Lib.Object.aN */);
                    }))),
                    _pd/* sg2y */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*(E(_pa/* sg2f */)+1)/E(_l6/* Lib.Object.aN */);
                    })));
                    if(_pc/* sg2o */!=_pd/* sg2y */){
                      if(_oP/* sg24 */>=0){
                        var _pe/*   sg2d */ = _p8/* sg2d */+(B(_hy/* Lib.Object.$wf */(_pc/* sg2o */, _oP/* sg24 */))-B(_hy/* Lib.Object.$wf */(_pd/* sg2y */, _oP/* sg24 */)))/(_pc/* sg2o */-_pd/* sg2y */)/_oJ/* sg1z */;
                        _p4/*  sg2c */ = _pb/* sg2g */;
                        _p5/*  sg2d */ = _pe/*   sg2d */;
                        return __continue/* EXTERNAL */;
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }else{
                      if(_oI/* sg1y */>=0){
                        var _pf/* sg2O */ = E(_oI/* sg1y */);
                        if(!_pf/* sg2O */){
                          var _pe/*   sg2d */ = _p8/* sg2d */+_oH/* sg1w *//_oJ/* sg1z */;
                          _p4/*  sg2c */ = _pb/* sg2g */;
                          _p5/*  sg2d */ = _pe/*   sg2d */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _pe/*   sg2d */ = _p8/* sg2d */+_oH/* sg1w */*B(_hy/* Lib.Object.$wf */(_pc/* sg2o */, _pf/* sg2O */))/_oJ/* sg1z */;
                          _p4/*  sg2c */ = _pb/* sg2g */;
                          _p5/*  sg2d */ = _pe/*   sg2d */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_p4/*  sg2c */, _p5/*  sg2d */));
                if(_p6/*  sg2b */!=__continue/* EXTERNAL */){
                  return _p6/*  sg2b */;
                }
              }
            };
            return _oG/* sg1u */*B(_p3/* sg2b */(_oM/* sg1G */, (B(_hy/* Lib.Object.$wf */(_oN/* sg1O */, _oP/* sg24 */))-B(_hy/* Lib.Object.$wf */(_oO/* sg1Y */, _oP/* sg24 */)))/(_oN/* sg1O */-_oO/* sg1Y */)/_oJ/* sg1z */));
          }
        }else{
          return E(_hp/* Lib.Object.$s^1 */);
        }
      }else{
        if(_oI/* sg1y */>=0){
          var _pg/* sg3J */ = E(_oI/* sg1y */);
          if(!_pg/* sg3J */){
            var _ph/* sg4C */ = function(_pi/*  sg4D */, _pj/*  sg4E */){
              while(1){
                var _pk/*  sg4C */ = B((function(_pl/* sg4D */, _pm/* sg4E */){
                  var _pn/* sg4F */ = E(_pl/* sg4D */);
                  if(!_pn/* sg4F */._){
                    return E(_pm/* sg4E */);
                  }else{
                    var _po/* sg4G */ = _pn/* sg4F */.a,
                    _pp/* sg4H */ = _pn/* sg4F */.b,
                    _pq/* sg4P */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*E(_po/* sg4G */)/E(_l6/* Lib.Object.aN */);
                    }))),
                    _pr/* sg4Z */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*(E(_po/* sg4G */)+1)/E(_l6/* Lib.Object.aN */);
                    })));
                    if(_pq/* sg4P */!=_pr/* sg4Z */){
                      if(_oH/* sg1w */>=0){
                        var _ps/* sg55 */ = E(_oH/* sg1w */);
                        if(!_ps/* sg55 */){
                          var _pt/*   sg4E */ = _pm/* sg4E */+0/(_pq/* sg4P */-_pr/* sg4Z */)/_oJ/* sg1z */;
                          _pi/*  sg4D */ = _pp/* sg4H */;
                          _pj/*  sg4E */ = _pt/*   sg4E */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _pt/*   sg4E */ = _pm/* sg4E */+(B(_hy/* Lib.Object.$wf */(_pq/* sg4P */, _ps/* sg55 */))-B(_hy/* Lib.Object.$wf */(_pr/* sg4Z */, _ps/* sg55 */)))/(_pq/* sg4P */-_pr/* sg4Z */)/_oJ/* sg1z */;
                          _pi/*  sg4D */ = _pp/* sg4H */;
                          _pj/*  sg4E */ = _pt/*   sg4E */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }else{
                      var _pt/*   sg4E */ = _pm/* sg4E */+_oH/* sg1w *//_oJ/* sg1z */;
                      _pi/*  sg4D */ = _pp/* sg4H */;
                      _pj/*  sg4E */ = _pt/*   sg4E */;
                      return __continue/* EXTERNAL */;
                    }
                  }
                })(_pi/*  sg4D */, _pj/*  sg4E */));
                if(_pk/*  sg4C */!=__continue/* EXTERNAL */){
                  return _pk/*  sg4C */;
                }
              }
            };
            return _oG/* sg1u */*B(_ph/* sg4C */(_oM/* sg1G */, _oH/* sg1w *//_oJ/* sg1z */));
          }else{
            var _pu/* sg3N */ = function(_pv/*  sg3O */, _pw/*  sg3P */){
              while(1){
                var _px/*  sg3N */ = B((function(_py/* sg3O */, _pz/* sg3P */){
                  var _pA/* sg3Q */ = E(_py/* sg3O */);
                  if(!_pA/* sg3Q */._){
                    return E(_pz/* sg3P */);
                  }else{
                    var _pB/* sg3R */ = _pA/* sg3Q */.a,
                    _pC/* sg3S */ = _pA/* sg3Q */.b,
                    _pD/* sg40 */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*E(_pB/* sg3R */)/E(_l6/* Lib.Object.aN */);
                    }))),
                    _pE/* sg4a */ = B(A1(_or/* sg1f */,new T(function(){
                      return 6.283185307179586*(E(_pB/* sg3R */)+1)/E(_l6/* Lib.Object.aN */);
                    })));
                    if(_pD/* sg40 */!=_pE/* sg4a */){
                      if(_oH/* sg1w */>=0){
                        var _pF/* sg4g */ = E(_oH/* sg1w */);
                        if(!_pF/* sg4g */){
                          var _pG/*   sg3P */ = _pz/* sg3P */+0/(_pD/* sg40 */-_pE/* sg4a */)/_oJ/* sg1z */;
                          _pv/*  sg3O */ = _pC/* sg3S */;
                          _pw/*  sg3P */ = _pG/*   sg3P */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _pG/*   sg3P */ = _pz/* sg3P */+(B(_hy/* Lib.Object.$wf */(_pD/* sg40 */, _pF/* sg4g */))-B(_hy/* Lib.Object.$wf */(_pE/* sg4a */, _pF/* sg4g */)))/(_pD/* sg40 */-_pE/* sg4a */)/_oJ/* sg1z */;
                          _pv/*  sg3O */ = _pC/* sg3S */;
                          _pw/*  sg3P */ = _pG/*   sg3P */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }else{
                      if(_pg/* sg3J */>=0){
                        var _pG/*   sg3P */ = _pz/* sg3P */+_oH/* sg1w */*B(_hy/* Lib.Object.$wf */(_pD/* sg40 */, _pg/* sg3J */))/_oJ/* sg1z */;
                        _pv/*  sg3O */ = _pC/* sg3S */;
                        _pw/*  sg3P */ = _pG/*   sg3P */;
                        return __continue/* EXTERNAL */;
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_pv/*  sg3O */, _pw/*  sg3P */));
                if(_px/*  sg3N */!=__continue/* EXTERNAL */){
                  return _px/*  sg3N */;
                }
              }
            };
            return _oG/* sg1u */*B(_pu/* sg3N */(_oM/* sg1G */, _oH/* sg1w */*B(_hy/* Lib.Object.$wf */(_oN/* sg1O */, _pg/* sg3J */))/_oJ/* sg1z */));
          }
        }else{
          return E(_hp/* Lib.Object.$s^1 */);
        }
      }
    }
  },
  _pH/* sg5p */ = 1/(B(_oE/* sg1s */(1))*_os/* sg1g */);
  return new F(function(){return _nO/* Lib.Object.$wfitO */(_or/* sg1f */, _op/* Lib.Object.lvl26 */, new T2(0,E(new T3(0,E(_pH/* sg5p */),E(_pH/* sg5p */),E(_pH/* sg5p */))),1/(B(_oE/* sg1s */(3))*_os/* sg1g */)), _ot/* sg1h */, _ou/* sg1i */, _ov/* sg1j */, _ow/* sg1k */, _ox/* sg1l */, _oy/* sg1m */, _oz/* sg1n */, _oA/* sg1o */, _oB/* sg1p */, _oC/* sg1q */, _oD/* sg1r */, _hn/* Lib.Object.$fNumPos2 */, _o/* GHC.Types.[] */, _o/* GHC.Types.[] */);});
},
_pI/* initial11 */ = 0,
_pJ/* initial15 */ =  -0.2,
_pK/* initial16 */ = 0.5,
_pL/* initial17 */ =  -0.8,
_pM/* initial_r */ = 0.2,
_pN/* initial18 */ = function(_pO/* sBQ2 */){
  return E(_pM/* Main.initial_r */);
},
_pP/* initial7 */ = 1,
_pQ/* initial14 */ = new T(function(){
  var _pR/* sBQ3 */ = B(_oq/* Lib.Object.$wmake */(_pN/* Main.initial18 */, 1.2, _pL/* Main.initial17 */, _pK/* Main.initial16 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pJ/* Main.initial15 */, _pI/* Main.initial11 */, _pP/* Main.initial7 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pP/* Main.initial7 */));
  return {_:0,a:E(_pR/* sBQ3 */.a),b:E(_pR/* sBQ3 */.b),c:E(_pR/* sBQ3 */.c),d:E(_pR/* sBQ3 */.d),e:E(_pR/* sBQ3 */.e),f:E(_pR/* sBQ3 */.f),g:E(_pR/* sBQ3 */.g),h:E(_pR/* sBQ3 */.h),i:E(_pR/* sBQ3 */.i)};
}),
_pS/* initial4 */ = 0,
_pT/* initial10 */ =  -0.1,
_pU/* initial12 */ = 1.3,
_pV/* decodeDoubleInteger */ = function(_pW/* s1ID */){
  var _pX/* s1IF */ = I_decodeDouble/* EXTERNAL */(_pW/* s1ID */);
  return new T2(0,new T1(1,_pX/* s1IF */.b),_pX/* s1IF */.a);
},
_pY/* smallInteger */ = function(_pZ/* B1 */){
  return new T1(0,_pZ/* B1 */);
},
_q0/* int64ToInteger */ = function(_q1/* s1RA */){
  var _q2/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _q3/* s1RG */ = hs_leInt64/* EXTERNAL */(_q1/* s1RA */, _q2/* s1RC */);
  if(!_q3/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_q1/* s1RA */));
  }else{
    var _q4/* s1RN */ = hs_intToInt64/* EXTERNAL */( -2147483648),
    _q5/* s1RR */ = hs_geInt64/* EXTERNAL */(_q1/* s1RA */, _q4/* s1RN */);
    if(!_q5/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_q1/* s1RA */));
    }else{
      var _q6/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_q1/* s1RA */);
      return new F(function(){return _pY/* GHC.Integer.Type.smallInteger */(_q6/* s1RY */);});
    }
  }
},
_q7/* zeroCountArr */ = new T(function(){
  var _q8/* s9bR */ = newByteArr/* EXTERNAL */(256),
  _q9/* s9bT */ = _q8/* s9bR */,
  _/* EXTERNAL */ = _q9/* s9bT */["v"]["i8"][0] = 8,
  _qa/* s9bV */ = function(_qb/* s9bW */, _qc/* s9bX */, _qd/* s9bY */, _/* EXTERNAL */){
    while(1){
      if(_qd/* s9bY */>=256){
        if(_qb/* s9bW */>=256){
          return E(_/* EXTERNAL */);
        }else{
          var _qe/*  s9bW */ = imul/* EXTERNAL */(2, _qb/* s9bW */)|0,
          _qf/*  s9bX */ = _qc/* s9bX */+1|0,
          _qg/*  s9bY */ = _qb/* s9bW */;
          _qb/* s9bW */ = _qe/*  s9bW */;
          _qc/* s9bX */ = _qf/*  s9bX */;
          _qd/* s9bY */ = _qg/*  s9bY */;
          continue;
        }
      }else{
        var _/* EXTERNAL */ = _q9/* s9bT */["v"]["i8"][_qd/* s9bY */] = _qc/* s9bX */,
        _qg/*  s9bY */ = _qd/* s9bY */+_qb/* s9bW */|0;
        _qd/* s9bY */ = _qg/*  s9bY */;
        continue;
      }
    }
  },
  _/* EXTERNAL */ = B(_qa/* s9bV */(2, 0, 1, _/* EXTERNAL */));
  return _q9/* s9bT */;
}),
_qh/* elim64# */ = function(_qi/* s9cN */, _qj/* s9cO */){
  var _qk/* s9cQ */ = hs_int64ToInt/* EXTERNAL */(_qi/* s9cN */),
  _ql/* s9cT */ = E(_q7/* GHC.Float.ConversionUtils.zeroCountArr */),
  _qm/* s9cY */ = _ql/* s9cT */["v"]["i8"][(255&_qk/* s9cQ */>>>0)>>>0&4294967295];
  if(_qj/* s9cO */>_qm/* s9cY */){
    if(_qm/* s9cY */>=8){
      var _qn/* s9d4 */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_qi/* s9cN */, 8),
      _qo/* s9d7 */ = function(_qp/*  s9d8 */, _qq/*  s9d9 */){
        while(1){
          var _qr/*  s9d7 */ = B((function(_qs/* s9d8 */, _qt/* s9d9 */){
            var _qu/* s9db */ = hs_int64ToInt/* EXTERNAL */(_qs/* s9d8 */),
            _qv/* s9dh */ = _ql/* s9cT */["v"]["i8"][(255&_qu/* s9db */>>>0)>>>0&4294967295];
            if(_qt/* s9d9 */>_qv/* s9dh */){
              if(_qv/* s9dh */>=8){
                var _qw/* s9dn */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_qs/* s9d8 */, 8),
                _qx/*   s9d9 */ = _qt/* s9d9 */-8|0;
                _qp/*  s9d8 */ = _qw/* s9dn */;
                _qq/*  s9d9 */ = _qx/*   s9d9 */;
                return __continue/* EXTERNAL */;
              }else{
                return new T2(0,new T(function(){
                  var _qy/* s9ds */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_qs/* s9d8 */, _qv/* s9dh */);
                  return B(_q0/* GHC.Integer.Type.int64ToInteger */(_qy/* s9ds */));
                }),_qt/* s9d9 */-_qv/* s9dh */|0);
              }
            }else{
              return new T2(0,new T(function(){
                var _qz/* s9dy */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_qs/* s9d8 */, _qt/* s9d9 */);
                return B(_q0/* GHC.Integer.Type.int64ToInteger */(_qz/* s9dy */));
              }),0);
            }
          })(_qp/*  s9d8 */, _qq/*  s9d9 */));
          if(_qr/*  s9d7 */!=__continue/* EXTERNAL */){
            return _qr/*  s9d7 */;
          }
        }
      };
      return new F(function(){return _qo/* s9d7 */(_qn/* s9d4 */, _qj/* s9cO */-8|0);});
    }else{
      return new T2(0,new T(function(){
        var _qA/* s9dE */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_qi/* s9cN */, _qm/* s9cY */);
        return B(_q0/* GHC.Integer.Type.int64ToInteger */(_qA/* s9dE */));
      }),_qj/* s9cO */-_qm/* s9cY */|0);
    }
  }else{
    return new T2(0,new T(function(){
      var _qB/* s9dK */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_qi/* s9cN */, _qj/* s9cO */);
      return B(_q0/* GHC.Integer.Type.int64ToInteger */(_qB/* s9dK */));
    }),0);
  }
},
_qC/* intToInt64# */ = function(_qD/* sf6 */){
  var _qE/* sf8 */ = hs_intToInt64/* EXTERNAL */(_qD/* sf6 */);
  return E(_qE/* sf8 */);
},
_qF/* integerToInt64 */ = function(_qG/* s1S1 */){
  var _qH/* s1S2 */ = E(_qG/* s1S1 */);
  if(!_qH/* s1S2 */._){
    return new F(function(){return _qC/* GHC.IntWord64.intToInt64# */(_qH/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_qH/* s1S2 */.a);});
  }
},
_qI/* integer2Word# */ = function(_qJ/* s2C */){
  return I_toInt/* EXTERNAL */(_qJ/* s2C */)>>>0;
},
_qK/* integerToWord */ = function(_qL/* s1Rr */){
  var _qM/* s1Rs */ = E(_qL/* s1Rr */);
  if(!_qM/* s1Rs */._){
    return _qM/* s1Rs */.a>>>0;
  }else{
    return new F(function(){return _qI/* GHC.Integer.GMP.Prim.integer2Word# */(_qM/* s1Rs */.a);});
  }
},
_qN/* $w$ctoRational */ = function(_qO/* s1l6D */){
  var _qP/* s1l6E */ = B(_pV/* GHC.Integer.Type.decodeDoubleInteger */(_qO/* s1l6D */)),
  _qQ/* s1l6F */ = _qP/* s1l6E */.a,
  _qR/* s1l6G */ = _qP/* s1l6E */.b;
  if(_qR/* s1l6G */<0){
    var _qS/* s1l6K */ = function(_qT/* s1l6L */){
      if(!_qT/* s1l6L */){
        return new T2(0,E(_qQ/* s1l6F */),B(_3u/* GHC.Integer.Type.shiftLInteger */(_1M/* GHC.Float.$fRealDouble1 */,  -_qR/* s1l6G */)));
      }else{
        var _qU/* s1l6S */ = B(_qh/* GHC.Float.ConversionUtils.elim64# */(B(_qF/* GHC.Integer.Type.integerToInt64 */(_qQ/* s1l6F */)),  -_qR/* s1l6G */));
        return new T2(0,E(_qU/* s1l6S */.a),B(_3u/* GHC.Integer.Type.shiftLInteger */(_1M/* GHC.Float.$fRealDouble1 */, _qU/* s1l6S */.b)));
      }
    };
    if(!((B(_qK/* GHC.Integer.Type.integerToWord */(_qQ/* s1l6F */))&1)>>>0)){
      return new F(function(){return _qS/* s1l6K */(1);});
    }else{
      return new F(function(){return _qS/* s1l6K */(0);});
    }
  }else{
    return new T2(0,B(_3u/* GHC.Integer.Type.shiftLInteger */(_qQ/* s1l6F */, _qR/* s1l6G */)),_1M/* GHC.Float.$fRealDouble1 */);
  }
},
_qV/* $fRealDouble_$ctoRational */ = function(_qW/* s1l6Z */){
  var _qX/* s1l72 */ = B(_qN/* GHC.Float.$w$ctoRational */(E(_qW/* s1l6Z */)));
  return new T2(0,E(_qX/* s1l72 */.a),E(_qX/* s1l72 */.b));
},
_qY/* $fRealDouble */ = new T3(0,_il/* GHC.Float.$fNumDouble */,_jq/* GHC.Classes.$fOrdDouble */,_qV/* GHC.Float.$fRealDouble_$ctoRational */),
_qZ/* $p1Integral */ = function(_r0/* sv9T */){
  return E(E(_r0/* sv9T */).a);
},
_r1/* $p1Real */ = function(_r2/* svbu */){
  return E(E(_r2/* svbu */).a);
},
_r3/* eftInt */ = function(_r4/* smlE */, _r5/* smlF */){
  if(_r4/* smlE */<=_r5/* smlF */){
    var _r6/* smlI */ = function(_r7/* smlJ */){
      return new T2(1,_r7/* smlJ */,new T(function(){
        if(_r7/* smlJ */!=_r5/* smlF */){
          return B(_r6/* smlI */(_r7/* smlJ */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _r6/* smlI */(_r4/* smlE */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_r8/* $fEnumInt_$cenumFrom */ = function(_r9/* smzP */){
  return new F(function(){return _r3/* GHC.Enum.eftInt */(E(_r9/* smzP */), 2147483647);});
},
_ra/* efdtIntDn */ = function(_rb/* smkb */, _rc/* smkc */, _rd/* smkd */){
  if(_rd/* smkd */<=_rc/* smkc */){
    var _re/* smkr */ = new T(function(){
      var _rf/* smkh */ = _rc/* smkc */-_rb/* smkb */|0,
      _rg/* smkj */ = function(_rh/* smkk */){
        return (_rh/* smkk */>=(_rd/* smkd */-_rf/* smkh */|0)) ? new T2(1,_rh/* smkk */,new T(function(){
          return B(_rg/* smkj */(_rh/* smkk */+_rf/* smkh */|0));
        })) : new T2(1,_rh/* smkk */,_o/* GHC.Types.[] */);
      };
      return B(_rg/* smkj */(_rc/* smkc */));
    });
    return new T2(1,_rb/* smkb */,_re/* smkr */);
  }else{
    return (_rd/* smkd */<=_rb/* smkb */) ? new T2(1,_rb/* smkb */,_o/* GHC.Types.[] */) : __Z/* EXTERNAL */;
  }
},
_ri/* efdtIntUp */ = function(_rj/* smkR */, _rk/* smkS */, _rl/* smkT */){
  if(_rl/* smkT */>=_rk/* smkS */){
    var _rm/* sml7 */ = new T(function(){
      var _rn/* smkX */ = _rk/* smkS */-_rj/* smkR */|0,
      _ro/* smkZ */ = function(_rp/* sml0 */){
        return (_rp/* sml0 */<=(_rl/* smkT */-_rn/* smkX */|0)) ? new T2(1,_rp/* sml0 */,new T(function(){
          return B(_ro/* smkZ */(_rp/* sml0 */+_rn/* smkX */|0));
        })) : new T2(1,_rp/* sml0 */,_o/* GHC.Types.[] */);
      };
      return B(_ro/* smkZ */(_rk/* smkS */));
    });
    return new T2(1,_rj/* smkR */,_rm/* sml7 */);
  }else{
    return (_rl/* smkT */>=_rj/* smkR */) ? new T2(1,_rj/* smkR */,_o/* GHC.Types.[] */) : __Z/* EXTERNAL */;
  }
},
_rq/* efdInt */ = function(_rr/* smln */, _rs/* smlo */){
  if(_rs/* smlo */<_rr/* smln */){
    return new F(function(){return _ra/* GHC.Enum.efdtIntDn */(_rr/* smln */, _rs/* smlo */,  -2147483648);});
  }else{
    return new F(function(){return _ri/* GHC.Enum.efdtIntUp */(_rr/* smln */, _rs/* smlo */, 2147483647);});
  }
},
_rt/* $fEnumInt_$cenumFromThen */ = function(_ru/* smzJ */, _rv/* smzK */){
  return new F(function(){return _rq/* GHC.Enum.efdInt */(E(_ru/* smzJ */), E(_rv/* smzK */));});
},
_rw/* efdtInt */ = function(_rx/* smli */, _ry/* smlj */, _rz/* smlk */){
  if(_ry/* smlj */<_rx/* smli */){
    return new F(function(){return _ra/* GHC.Enum.efdtIntDn */(_rx/* smli */, _ry/* smlj */, _rz/* smlk */);});
  }else{
    return new F(function(){return _ri/* GHC.Enum.efdtIntUp */(_rx/* smli */, _ry/* smlj */, _rz/* smlk */);});
  }
},
_rA/* $fEnumInt_$cenumFromThenTo */ = function(_rB/* smzu */, _rC/* smzv */, _rD/* smzw */){
  return new F(function(){return _rw/* GHC.Enum.efdtInt */(E(_rB/* smzu */), E(_rC/* smzv */), E(_rD/* smzw */));});
},
_rE/* $fEnumInt_$cenumFromTo */ = function(_rF/* smzD */, _rG/* smzE */){
  return new F(function(){return _r3/* GHC.Enum.eftInt */(E(_rF/* smzD */), E(_rG/* smzE */));});
},
_rH/* $fEnumInt_$cfromEnum */ = function(_rI/* smzS */){
  return E(_rI/* smzS */);
},
_rJ/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));
}),
_rK/* $fEnumInt1 */ = new T(function(){
  return B(err/* EXTERNAL */(_rJ/* GHC.Enum.lvl28 */));
}),
_rL/* $fEnumInt_$cpred */ = function(_rM/* smAv */){
  var _rN/* smAy */ = E(_rM/* smAv */);
  return (_rN/* smAy */==( -2147483648)) ? E(_rK/* GHC.Enum.$fEnumInt1 */) : _rN/* smAy */-1|0;
},
_rO/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));
}),
_rP/* $fEnumInt2 */ = new T(function(){
  return B(err/* EXTERNAL */(_rO/* GHC.Enum.lvl27 */));
}),
_rQ/* $fEnumInt_$csucc */ = function(_rR/* smAq */){
  var _rS/* smAt */ = E(_rR/* smAq */);
  return (_rS/* smAt */==2147483647) ? E(_rP/* GHC.Enum.$fEnumInt2 */) : _rS/* smAt */+1|0;
},
_rT/* $fEnumInt */ = {_:0,a:_rQ/* GHC.Enum.$fEnumInt_$csucc */,b:_rL/* GHC.Enum.$fEnumInt_$cpred */,c:_rH/* GHC.Enum.$fEnumInt_$cfromEnum */,d:_rH/* GHC.Enum.$fEnumInt_$cfromEnum */,e:_r8/* GHC.Enum.$fEnumInt_$cenumFrom */,f:_rt/* GHC.Enum.$fEnumInt_$cenumFromThen */,g:_rE/* GHC.Enum.$fEnumInt_$cenumFromTo */,h:_rA/* GHC.Enum.$fEnumInt_$cenumFromThenTo */},
_rU/* divInt# */ = function(_rV/* scDT */, _rW/* scDU */){
  if(_rV/* scDT */<=0){
    if(_rV/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_rV/* scDT */, _rW/* scDU */);});
    }else{
      if(_rW/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_rV/* scDT */, _rW/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_rV/* scDT */+1|0, _rW/* scDU */)-1|0;
      }
    }
  }else{
    if(_rW/* scDU */>=0){
      if(_rV/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_rV/* scDT */, _rW/* scDU */);});
      }else{
        if(_rW/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_rV/* scDT */, _rW/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_rV/* scDT */+1|0, _rW/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_rV/* scDT */-1|0, _rW/* scDU */)-1|0;
    }
  }
},
_rX/* Overflow */ = 0,
_rY/* overflowException */ = new T(function(){
  return B(_2R/* GHC.Exception.$fExceptionArithException_$ctoException */(_rX/* GHC.Exception.Overflow */));
}),
_rZ/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_rY/* GHC.Exception.overflowException */);
}),
_s0/* $w$cdiv */ = function(_s1/* svjX */, _s2/* svjY */){
  var _s3/* svjZ */ = E(_s2/* svjY */);
  switch(_s3/* svjZ */){
    case  -1:
      var _s4/* svk0 */ = E(_s1/* svjX */);
      if(_s4/* svk0 */==( -2147483648)){
        return E(_rZ/* GHC.Real.overflowError */);
      }else{
        return new F(function(){return _rU/* GHC.Classes.divInt# */(_s4/* svk0 */,  -1);});
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return _rU/* GHC.Classes.divInt# */(_s1/* svjX */, _s3/* svjZ */);});
  }
},
_s5/* $fIntegralInt_$cdiv */ = function(_s6/* svk3 */, _s7/* svk4 */){
  return new F(function(){return _s0/* GHC.Real.$w$cdiv */(E(_s6/* svk3 */), E(_s7/* svk4 */));});
},
_s8/* $fIntegralInt1 */ = 0,
_s9/* lvl2 */ = new T2(0,_rZ/* GHC.Real.overflowError */,_s8/* GHC.Real.$fIntegralInt1 */),
_sa/* $fIntegralInt_$cdivMod */ = function(_sb/* svi2 */, _sc/* svi3 */){
  var _sd/* svi4 */ = E(_sb/* svi2 */),
  _se/* svi8 */ = E(_sc/* svi3 */);
  switch(_se/* svi8 */){
    case  -1:
      var _sf/* svj6 */ = E(_sd/* svi4 */);
      if(_sf/* svj6 */==( -2147483648)){
        return E(_s9/* GHC.Real.lvl2 */);
      }else{
        if(_sf/* svj6 */<=0){
          if(_sf/* svj6 */>=0){
            var _sg/* svjb */ = quotRemI/* EXTERNAL */(_sf/* svj6 */,  -1);
            return new T2(0,_sg/* svjb */.a,_sg/* svjb */.b);
          }else{
            var _sh/* svjg */ = quotRemI/* EXTERNAL */(_sf/* svj6 */,  -1);
            return new T2(0,_sh/* svjg */.a,_sh/* svjg */.b);
          }
        }else{
          var _si/* svjm */ = quotRemI/* EXTERNAL */(_sf/* svj6 */-1|0,  -1);
          return new T2(0,_si/* svjm */.a-1|0,(_si/* svjm */.b+( -1)|0)+1|0);
        }
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      if(_sd/* svi4 */<=0){
        if(_sd/* svi4 */>=0){
          var _sj/* svid */ = quotRemI/* EXTERNAL */(_sd/* svi4 */, _se/* svi8 */);
          return new T2(0,_sj/* svid */.a,_sj/* svid */.b);
        }else{
          if(_se/* svi8 */<=0){
            var _sk/* svik */ = quotRemI/* EXTERNAL */(_sd/* svi4 */, _se/* svi8 */);
            return new T2(0,_sk/* svik */.a,_sk/* svik */.b);
          }else{
            var _sl/* sviq */ = quotRemI/* EXTERNAL */(_sd/* svi4 */+1|0, _se/* svi8 */);
            return new T2(0,_sl/* sviq */.a-1|0,(_sl/* sviq */.b+_se/* svi8 */|0)-1|0);
          }
        }
      }else{
        if(_se/* svi8 */>=0){
          if(_sd/* svi4 */>=0){
            var _sm/* sviC */ = quotRemI/* EXTERNAL */(_sd/* svi4 */, _se/* svi8 */);
            return new T2(0,_sm/* sviC */.a,_sm/* sviC */.b);
          }else{
            if(_se/* svi8 */<=0){
              var _sn/* sviJ */ = quotRemI/* EXTERNAL */(_sd/* svi4 */, _se/* svi8 */);
              return new T2(0,_sn/* sviJ */.a,_sn/* sviJ */.b);
            }else{
              var _so/* sviP */ = quotRemI/* EXTERNAL */(_sd/* svi4 */+1|0, _se/* svi8 */);
              return new T2(0,_so/* sviP */.a-1|0,(_so/* sviP */.b+_se/* svi8 */|0)-1|0);
            }
          }
        }else{
          var _sp/* sviY */ = quotRemI/* EXTERNAL */(_sd/* svi4 */-1|0, _se/* svi8 */);
          return new T2(0,_sp/* sviY */.a-1|0,(_sp/* sviY */.b+_se/* svi8 */|0)+1|0);
        }
      }
  }
},
_sq/* modInt# */ = function(_sr/* scF6 */, _ss/* scF7 */){
  var _st/* scF8 */ = _sr/* scF6 */%_ss/* scF7 */;
  if(_sr/* scF6 */<=0){
    if(_sr/* scF6 */>=0){
      return E(_st/* scF8 */);
    }else{
      if(_ss/* scF7 */<=0){
        return E(_st/* scF8 */);
      }else{
        var _su/* scFf */ = E(_st/* scF8 */);
        return (_su/* scFf */==0) ? 0 : _su/* scFf */+_ss/* scF7 */|0;
      }
    }
  }else{
    if(_ss/* scF7 */>=0){
      if(_sr/* scF6 */>=0){
        return E(_st/* scF8 */);
      }else{
        if(_ss/* scF7 */<=0){
          return E(_st/* scF8 */);
        }else{
          var _sv/* scFm */ = E(_st/* scF8 */);
          return (_sv/* scFm */==0) ? 0 : _sv/* scFm */+_ss/* scF7 */|0;
        }
      }
    }else{
      var _sw/* scFn */ = E(_st/* scF8 */);
      return (_sw/* scFn */==0) ? 0 : _sw/* scFn */+_ss/* scF7 */|0;
    }
  }
},
_sx/* $fIntegralInt_$cmod */ = function(_sy/* svjO */, _sz/* svjP */){
  var _sA/* svjS */ = E(_sz/* svjP */);
  switch(_sA/* svjS */){
    case  -1:
      return E(_s8/* GHC.Real.$fIntegralInt1 */);
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return _sq/* GHC.Classes.modInt# */(E(_sy/* svjO */), _sA/* svjS */);});
  }
},
_sB/* $fIntegralInt_$cquot */ = function(_sC/* svki */, _sD/* svkj */){
  var _sE/* svkk */ = E(_sC/* svki */),
  _sF/* svko */ = E(_sD/* svkj */);
  switch(_sF/* svko */){
    case  -1:
      var _sG/* svkq */ = E(_sE/* svkk */);
      if(_sG/* svkq */==( -2147483648)){
        return E(_rZ/* GHC.Real.overflowError */);
      }else{
        return new F(function(){return quot/* EXTERNAL */(_sG/* svkq */,  -1);});
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return quot/* EXTERNAL */(_sE/* svkk */, _sF/* svko */);});
  }
},
_sH/* $fIntegralInt_$cquotRem */ = function(_sI/* svjv */, _sJ/* svjw */){
  var _sK/* svjx */ = E(_sI/* svjv */),
  _sL/* svjB */ = E(_sJ/* svjw */);
  switch(_sL/* svjB */){
    case  -1:
      var _sM/* svjH */ = E(_sK/* svjx */);
      if(_sM/* svjH */==( -2147483648)){
        return E(_s9/* GHC.Real.lvl2 */);
      }else{
        var _sN/* svjI */ = quotRemI/* EXTERNAL */(_sM/* svjH */,  -1);
        return new T2(0,_sN/* svjI */.a,_sN/* svjI */.b);
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      var _sO/* svjC */ = quotRemI/* EXTERNAL */(_sK/* svjx */, _sL/* svjB */);
      return new T2(0,_sO/* svjC */.a,_sO/* svjC */.b);
  }
},
_sP/* $fIntegralInt_$crem */ = function(_sQ/* svka */, _sR/* svkb */){
  var _sS/* svke */ = E(_sR/* svkb */);
  switch(_sS/* svke */){
    case  -1:
      return E(_s8/* GHC.Real.$fIntegralInt1 */);
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return E(_sQ/* svka */)%_sS/* svke */;
  }
},
_sT/* $fIntegralInt_$ctoInteger */ = function(_sU/* svhV */){
  return new F(function(){return _pY/* GHC.Integer.Type.smallInteger */(E(_sU/* svhV */));});
},
_sV/* $fEnumRatio_$ctoRational */ = function(_sW/* svhY */){
  return new T2(0,E(B(_pY/* GHC.Integer.Type.smallInteger */(E(_sW/* svhY */)))),E(_lJ/* GHC.Real.$fEnumRatio1 */));
},
_sX/* $fNumInt_$c* */ = function(_sY/* s6GN */, _sZ/* s6GO */){
  return imul/* EXTERNAL */(E(_sY/* s6GN */), E(_sZ/* s6GO */))|0;
},
_t0/* $fNumInt_$c+ */ = function(_t1/* s6H1 */, _t2/* s6H2 */){
  return E(_t1/* s6H1 */)+E(_t2/* s6H2 */)|0;
},
_t3/* $fNumInt_$c- */ = function(_t4/* s6GU */, _t5/* s6GV */){
  return E(_t4/* s6GU */)-E(_t5/* s6GV */)|0;
},
_t6/* $fNumInt_$cabs */ = function(_t7/* s6He */){
  var _t8/* s6Hf */ = E(_t7/* s6He */);
  return (_t8/* s6Hf */<0) ?  -_t8/* s6Hf */ : E(_t8/* s6Hf */);
},
_t9/* $fNumInt_$cfromInteger */ = function(_ta/* s6GH */){
  return new F(function(){return _38/* GHC.Integer.Type.integerToInt */(_ta/* s6GH */);});
},
_tb/* $fNumInt_$cnegate */ = function(_tc/* s6GJ */){
  return  -E(_tc/* s6GJ */);
},
_td/* $fNumInt1 */ =  -1,
_te/* $fNumInt2 */ = 0,
_tf/* $fNumInt3 */ = 1,
_tg/* $fNumInt_$csignum */ = function(_th/* s6H8 */){
  var _ti/* s6H9 */ = E(_th/* s6H8 */);
  return (_ti/* s6H9 */>=0) ? (E(_ti/* s6H9 */)==0) ? E(_te/* GHC.Num.$fNumInt2 */) : E(_tf/* GHC.Num.$fNumInt3 */) : E(_td/* GHC.Num.$fNumInt1 */);
},
_tj/* $fNumInt */ = {_:0,a:_t0/* GHC.Num.$fNumInt_$c+ */,b:_t3/* GHC.Num.$fNumInt_$c- */,c:_sX/* GHC.Num.$fNumInt_$c* */,d:_tb/* GHC.Num.$fNumInt_$cnegate */,e:_t6/* GHC.Num.$fNumInt_$cabs */,f:_tg/* GHC.Num.$fNumInt_$csignum */,g:_t9/* GHC.Num.$fNumInt_$cfromInteger */},
_tk/* eqInt */ = function(_tl/* scEd */, _tm/* scEe */){
  return E(_tl/* scEd */)==E(_tm/* scEe */);
},
_tn/* neInt */ = function(_to/* scEM */, _tp/* scEN */){
  return E(_to/* scEM */)!=E(_tp/* scEN */);
},
_tq/* $fEqInt */ = new T2(0,_tk/* GHC.Classes.eqInt */,_tn/* GHC.Classes.neInt */),
_tr/* $fOrdInt_$cmax */ = function(_ts/* scK3 */, _tt/* scK4 */){
  var _tu/* scK5 */ = E(_ts/* scK3 */),
  _tv/* scK7 */ = E(_tt/* scK4 */);
  return (_tu/* scK5 */>_tv/* scK7 */) ? E(_tu/* scK5 */) : E(_tv/* scK7 */);
},
_tw/* $fOrdInt_$cmin */ = function(_tx/* scJV */, _ty/* scJW */){
  var _tz/* scJX */ = E(_tx/* scJV */),
  _tA/* scJZ */ = E(_ty/* scJW */);
  return (_tz/* scJX */>_tA/* scJZ */) ? E(_tA/* scJZ */) : E(_tz/* scJX */);
},
_tB/* compareInt# */ = function(_tC/* scDH */, _tD/* scDI */){
  return (_tC/* scDH */>=_tD/* scDI */) ? (_tC/* scDH */!=_tD/* scDI */) ? 2 : 1 : 0;
},
_tE/* compareInt */ = function(_tF/* scDN */, _tG/* scDO */){
  return new F(function(){return _tB/* GHC.Classes.compareInt# */(E(_tF/* scDN */), E(_tG/* scDO */));});
},
_tH/* geInt */ = function(_tI/* scEk */, _tJ/* scEl */){
  return E(_tI/* scEk */)>=E(_tJ/* scEl */);
},
_tK/* gtInt */ = function(_tL/* scEr */, _tM/* scEs */){
  return E(_tL/* scEr */)>E(_tM/* scEs */);
},
_tN/* leInt */ = function(_tO/* scEy */, _tP/* scEz */){
  return E(_tO/* scEy */)<=E(_tP/* scEz */);
},
_tQ/* ltInt */ = function(_tR/* scEF */, _tS/* scEG */){
  return E(_tR/* scEF */)<E(_tS/* scEG */);
},
_tT/* $fOrdInt */ = {_:0,a:_tq/* GHC.Classes.$fEqInt */,b:_tE/* GHC.Classes.compareInt */,c:_tQ/* GHC.Classes.ltInt */,d:_tN/* GHC.Classes.leInt */,e:_tK/* GHC.Classes.gtInt */,f:_tH/* GHC.Classes.geInt */,g:_tr/* GHC.Classes.$fOrdInt_$cmax */,h:_tw/* GHC.Classes.$fOrdInt_$cmin */},
_tU/* $fRealInt */ = new T3(0,_tj/* GHC.Num.$fNumInt */,_tT/* GHC.Classes.$fOrdInt */,_sV/* GHC.Real.$fEnumRatio_$ctoRational */),
_tV/* $fIntegralInt */ = {_:0,a:_tU/* GHC.Real.$fRealInt */,b:_rT/* GHC.Enum.$fEnumInt */,c:_sB/* GHC.Real.$fIntegralInt_$cquot */,d:_sP/* GHC.Real.$fIntegralInt_$crem */,e:_s5/* GHC.Real.$fIntegralInt_$cdiv */,f:_sx/* GHC.Real.$fIntegralInt_$cmod */,g:_sH/* GHC.Real.$fIntegralInt_$cquotRem */,h:_sa/* GHC.Real.$fIntegralInt_$cdivMod */,i:_sT/* GHC.Real.$fIntegralInt_$ctoInteger */},
_tW/* $fRealFloatDouble5 */ = new T1(0,2),
_tX/* timesInteger */ = function(_tY/* s1PN */, _tZ/* s1PO */){
  while(1){
    var _u0/* s1PP */ = E(_tY/* s1PN */);
    if(!_u0/* s1PP */._){
      var _u1/* s1PQ */ = _u0/* s1PP */.a,
      _u2/* s1PR */ = E(_tZ/* s1PO */);
      if(!_u2/* s1PR */._){
        var _u3/* s1PS */ = _u2/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_u1/* s1PQ */, _u3/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_u1/* s1PQ */, _u3/* s1PS */)|0);
        }else{
          _tY/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_u1/* s1PQ */));
          _tZ/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_u3/* s1PS */));
          continue;
        }
      }else{
        _tY/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_u1/* s1PQ */));
        _tZ/* s1PO */ = _u2/* s1PR */;
        continue;
      }
    }else{
      var _u4/* s1Q6 */ = E(_tZ/* s1PO */);
      if(!_u4/* s1Q6 */._){
        _tY/* s1PN */ = _u0/* s1PP */;
        _tZ/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_u4/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_u0/* s1PP */.a, _u4/* s1Q6 */.a));
      }
    }
  }
},
_u5/* $wg1 */ = function(_u6/* svGB */, _u7/* svGC */, _u8/* svGD */){
  while(1){
    if(!(_u7/* svGC */%2)){
      var _u9/*  svGB */ = B(_tX/* GHC.Integer.Type.timesInteger */(_u6/* svGB */, _u6/* svGB */)),
      _ua/*  svGC */ = quot/* EXTERNAL */(_u7/* svGC */, 2);
      _u6/* svGB */ = _u9/*  svGB */;
      _u7/* svGC */ = _ua/*  svGC */;
      continue;
    }else{
      var _ub/* svGF */ = E(_u7/* svGC */);
      if(_ub/* svGF */==1){
        return new F(function(){return _tX/* GHC.Integer.Type.timesInteger */(_u6/* svGB */, _u8/* svGD */);});
      }else{
        var _u9/*  svGB */ = B(_tX/* GHC.Integer.Type.timesInteger */(_u6/* svGB */, _u6/* svGB */)),
        _uc/*  svGD */ = B(_tX/* GHC.Integer.Type.timesInteger */(_u6/* svGB */, _u8/* svGD */));
        _u6/* svGB */ = _u9/*  svGB */;
        _u7/* svGC */ = quot/* EXTERNAL */(_ub/* svGF */-1|0, 2);
        _u8/* svGD */ = _uc/*  svGD */;
        continue;
      }
    }
  }
},
_ud/* $wf */ = function(_ue/* svGM */, _uf/* svGN */){
  while(1){
    if(!(_uf/* svGN */%2)){
      var _ug/*  svGM */ = B(_tX/* GHC.Integer.Type.timesInteger */(_ue/* svGM */, _ue/* svGM */)),
      _uh/*  svGN */ = quot/* EXTERNAL */(_uf/* svGN */, 2);
      _ue/* svGM */ = _ug/*  svGM */;
      _uf/* svGN */ = _uh/*  svGN */;
      continue;
    }else{
      var _ui/* svGP */ = E(_uf/* svGN */);
      if(_ui/* svGP */==1){
        return E(_ue/* svGM */);
      }else{
        return new F(function(){return _u5/* GHC.Real.$wg1 */(B(_tX/* GHC.Integer.Type.timesInteger */(_ue/* svGM */, _ue/* svGM */)), quot/* EXTERNAL */(_ui/* svGP */-1|0, 2), _ue/* svGM */);});
      }
    }
  }
},
_uj/* $p2Real */ = function(_uk/* svbz */){
  return E(E(_uk/* svbz */).b);
},
_ul/* < */ = function(_um/* scCc */){
  return E(E(_um/* scCc */).c);
},
_un/* even1 */ = new T1(0,0),
_uo/* rem */ = function(_up/* svaq */){
  return E(E(_up/* svaq */).d);
},
_uq/* even */ = function(_ur/* svAV */, _us/* svAW */){
  var _ut/* svAX */ = B(_qZ/* GHC.Real.$p1Integral */(_ur/* svAV */)),
  _uu/* svAY */ = new T(function(){
    return B(_r1/* GHC.Real.$p1Real */(_ut/* svAX */));
  }),
  _uv/* svB2 */ = new T(function(){
    return B(A3(_uo/* GHC.Real.rem */,_ur/* svAV */, _us/* svAW */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_uu/* svAY */, _lT/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_kE/* GHC.Classes.== */,B(_kq/* GHC.Classes.$p1Ord */(B(_uj/* GHC.Real.$p2Real */(_ut/* svAX */)))), _uv/* svB2 */, new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,_uu/* svAY */, _un/* GHC.Real.even1 */));
  }));});
},
_uw/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_ux/* lvl11 */ = new T(function(){
  return B(err/* EXTERNAL */(_uw/* GHC.Real.lvl5 */));
}),
_uy/* quot */ = function(_uz/* svaf */){
  return E(E(_uz/* svaf */).c);
},
_uA/* ^ */ = function(_uB/* svH6 */, _uC/* svH7 */, _uD/* svH8 */, _uE/* svH9 */){
  var _uF/* svHa */ = B(_qZ/* GHC.Real.$p1Integral */(_uC/* svH7 */)),
  _uG/* svHb */ = new T(function(){
    return B(_r1/* GHC.Real.$p1Real */(_uF/* svHa */));
  }),
  _uH/* svHc */ = B(_uj/* GHC.Real.$p2Real */(_uF/* svHa */));
  if(!B(A3(_ul/* GHC.Classes.< */,_uH/* svHc */, _uE/* svH9 */, new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,_uG/* svHb */, _un/* GHC.Real.even1 */));
  })))){
    if(!B(A3(_kE/* GHC.Classes.== */,B(_kq/* GHC.Classes.$p1Ord */(_uH/* svHc */)), _uE/* svH9 */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_uG/* svHb */, _un/* GHC.Real.even1 */));
    })))){
      var _uI/* svHi */ = new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_uG/* svHb */, _lT/* GHC.Real.even2 */));
      }),
      _uJ/* svHj */ = new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_uG/* svHb */, _lJ/* GHC.Real.$fEnumRatio1 */));
      }),
      _uK/* svHk */ = B(_kq/* GHC.Classes.$p1Ord */(_uH/* svHc */)),
      _uL/* svHl */ = function(_uM/*  svHm */, _uN/*  svHn */, _uO/*  svHo */){
        while(1){
          var _uP/*  svHl */ = B((function(_uQ/* svHm */, _uR/* svHn */, _uS/* svHo */){
            if(!B(_uq/* GHC.Real.even */(_uC/* svH7 */, _uR/* svHn */))){
              if(!B(A3(_kE/* GHC.Classes.== */,_uK/* svHk */, _uR/* svHn */, _uJ/* svHj */))){
                var _uT/* svHt */ = new T(function(){
                  return B(A3(_uy/* GHC.Real.quot */,_uC/* svH7 */, new T(function(){
                    return B(A3(_7m/* GHC.Num.- */,_uG/* svHb */, _uR/* svHn */, _uJ/* svHj */));
                  }), _uI/* svHi */));
                });
                _uM/*  svHm */ = new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_uB/* svH6 */, _uQ/* svHm */, _uQ/* svHm */));
                });
                _uN/*  svHn */ = _uT/* svHt */;
                _uO/*  svHo */ = new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_uB/* svH6 */, _uQ/* svHm */, _uS/* svHo */));
                });
                return __continue/* EXTERNAL */;
              }else{
                return new F(function(){return A3(_7k/* GHC.Num.* */,_uB/* svH6 */, _uQ/* svHm */, _uS/* svHo */);});
              }
            }else{
              var _uU/*   svHo */ = _uS/* svHo */;
              _uM/*  svHm */ = new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_uB/* svH6 */, _uQ/* svHm */, _uQ/* svHm */));
              });
              _uN/*  svHn */ = new T(function(){
                return B(A3(_uy/* GHC.Real.quot */,_uC/* svH7 */, _uR/* svHn */, _uI/* svHi */));
              });
              _uO/*  svHo */ = _uU/*   svHo */;
              return __continue/* EXTERNAL */;
            }
          })(_uM/*  svHm */, _uN/*  svHn */, _uO/*  svHo */));
          if(_uP/*  svHl */!=__continue/* EXTERNAL */){
            return _uP/*  svHl */;
          }
        }
      },
      _uV/* svHx */ = function(_uW/*  svHy */, _uX/*  svHz */){
        while(1){
          var _uY/*  svHx */ = B((function(_uZ/* svHy */, _v0/* svHz */){
            if(!B(_uq/* GHC.Real.even */(_uC/* svH7 */, _v0/* svHz */))){
              if(!B(A3(_kE/* GHC.Classes.== */,_uK/* svHk */, _v0/* svHz */, _uJ/* svHj */))){
                var _v1/* svHE */ = new T(function(){
                  return B(A3(_uy/* GHC.Real.quot */,_uC/* svH7 */, new T(function(){
                    return B(A3(_7m/* GHC.Num.- */,_uG/* svHb */, _v0/* svHz */, _uJ/* svHj */));
                  }), _uI/* svHi */));
                });
                return new F(function(){return _uL/* svHl */(new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_uB/* svH6 */, _uZ/* svHy */, _uZ/* svHy */));
                }), _v1/* svHE */, _uZ/* svHy */);});
              }else{
                return E(_uZ/* svHy */);
              }
            }else{
              _uW/*  svHy */ = new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_uB/* svH6 */, _uZ/* svHy */, _uZ/* svHy */));
              });
              _uX/*  svHz */ = new T(function(){
                return B(A3(_uy/* GHC.Real.quot */,_uC/* svH7 */, _v0/* svHz */, _uI/* svHi */));
              });
              return __continue/* EXTERNAL */;
            }
          })(_uW/*  svHy */, _uX/*  svHz */));
          if(_uY/*  svHx */!=__continue/* EXTERNAL */){
            return _uY/*  svHx */;
          }
        }
      };
      return new F(function(){return _uV/* svHx */(_uD/* svH8 */, _uE/* svH9 */);});
    }else{
      return new F(function(){return A2(_91/* GHC.Num.fromInteger */,_uB/* svH6 */, _lJ/* GHC.Real.$fEnumRatio1 */);});
    }
  }else{
    return E(_ux/* GHC.Real.lvl11 */);
  }
},
_v2/* ^1 */ = new T(function(){
  return B(err/* EXTERNAL */(_uw/* GHC.Real.lvl5 */));
}),
_v3/* $w$cproperFraction */ = function(_v4/* s1l7J */, _v5/* s1l7K */){
  var _v6/* s1l7L */ = B(_pV/* GHC.Integer.Type.decodeDoubleInteger */(_v5/* s1l7K */)),
  _v7/* s1l7M */ = _v6/* s1l7L */.a,
  _v8/* s1l7N */ = _v6/* s1l7L */.b,
  _v9/* s1l7P */ = new T(function(){
    return B(_r1/* GHC.Real.$p1Real */(new T(function(){
      return B(_qZ/* GHC.Real.$p1Integral */(_v4/* s1l7J */));
    })));
  });
  if(_v8/* s1l7N */<0){
    var _va/* s1l7S */ =  -_v8/* s1l7N */;
    if(_va/* s1l7S */>=0){
      var _vb/* s1l7W */ = E(_va/* s1l7S */);
      if(!_vb/* s1l7W */){
        var _vc/* s1l7W#result */ = E(_lJ/* GHC.Real.$fEnumRatio1 */);
      }else{
        var _vc/* s1l7W#result */ = B(_ud/* GHC.Real.$wf */(_tW/* GHC.Float.$fRealFloatDouble5 */, _vb/* s1l7W */));
      }
      if(!B(_30/* GHC.Integer.Type.eqInteger */(_vc/* s1l7W#result */, _3t/* GHC.Float.rationalToDouble5 */))){
        var _vd/* s1l7Y */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_v7/* s1l7M */, _vc/* s1l7W#result */));
        return new T2(0,new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_v9/* s1l7P */, _vd/* s1l7Y */.a));
        }),new T(function(){
          return B(_2W/* GHC.Integer.Type.encodeDoubleInteger */(_vd/* s1l7Y */.b, _v8/* s1l7N */));
        }));
      }else{
        return E(_2V/* GHC.Real.divZeroError */);
      }
    }else{
      return E(_v2/* GHC.Real.^1 */);
    }
  }else{
    var _ve/* s1l8a */ = new T(function(){
      var _vf/* s1l89 */ = new T(function(){
        return B(_uA/* GHC.Real.^ */(_v9/* s1l7P */, _tV/* GHC.Real.$fIntegralInt */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_v9/* s1l7P */, _tW/* GHC.Float.$fRealFloatDouble5 */));
        }), _v8/* s1l7N */));
      });
      return B(A3(_7k/* GHC.Num.* */,_v9/* s1l7P */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_v9/* s1l7P */, _v7/* s1l7M */));
      }), _vf/* s1l89 */));
    });
    return new T2(0,_ve/* s1l8a */,_6i/* GHC.Float.rationalToDouble4 */);
  }
},
_vg/* $fRealFracDouble_$cceiling */ = function(_vh/* s1l8X */, _vi/* s1l8Y */){
  var _vj/* s1l91 */ = B(_v3/* GHC.Float.$w$cproperFraction */(_vh/* s1l8X */, E(_vi/* s1l8Y */))),
  _vk/* s1l92 */ = _vj/* s1l91 */.a;
  if(E(_vj/* s1l91 */.b)<=0){
    return E(_vk/* s1l92 */);
  }else{
    var _vl/* s1l99 */ = B(_r1/* GHC.Real.$p1Real */(B(_qZ/* GHC.Real.$p1Integral */(_vh/* s1l8X */))));
    return new F(function(){return A3(_6I/* GHC.Num.+ */,_vl/* s1l99 */, _vk/* s1l92 */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_vl/* s1l99 */, _1M/* GHC.Float.$fRealDouble1 */));
    }));});
  }
},
_vm/* $fRealFracDouble_$cfloor */ = function(_vn/* s1l9b */, _vo/* s1l9c */){
  var _vp/* s1l9f */ = B(_v3/* GHC.Float.$w$cproperFraction */(_vn/* s1l9b */, E(_vo/* s1l9c */))),
  _vq/* s1l9g */ = _vp/* s1l9f */.a;
  if(E(_vp/* s1l9f */.b)>=0){
    return E(_vq/* s1l9g */);
  }else{
    var _vr/* s1l9n */ = B(_r1/* GHC.Real.$p1Real */(B(_qZ/* GHC.Real.$p1Integral */(_vn/* s1l9b */))));
    return new F(function(){return A3(_7m/* GHC.Num.- */,_vr/* s1l9n */, _vq/* s1l9g */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_vr/* s1l9n */, _1M/* GHC.Float.$fRealDouble1 */));
    }));});
  }
},
_vs/* $fRealFracDouble_$cproperFraction */ = function(_vt/* s1l8b */, _vu/* s1l8c */){
  var _vv/* s1l8f */ = B(_v3/* GHC.Float.$w$cproperFraction */(_vt/* s1l8b */, E(_vu/* s1l8c */)));
  return new T2(0,_vv/* s1l8f */.a,_vv/* s1l8f */.b);
},
_vw/* $w$cround */ = function(_vx/* s1l8p */, _vy/* s1l8q */){
  var _vz/* s1l8r */ = B(_v3/* GHC.Float.$w$cproperFraction */(_vx/* s1l8p */, _vy/* s1l8q */)),
  _vA/* s1l8s */ = _vz/* s1l8r */.a,
  _vB/* s1l8u */ = E(_vz/* s1l8r */.b),
  _vC/* s1l8w */ = new T(function(){
    var _vD/* s1l8y */ = B(_r1/* GHC.Real.$p1Real */(B(_qZ/* GHC.Real.$p1Integral */(_vx/* s1l8p */))));
    if(_vB/* s1l8u */>=0){
      return B(A3(_6I/* GHC.Num.+ */,_vD/* s1l8y */, _vA/* s1l8s */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_vD/* s1l8y */, _1M/* GHC.Float.$fRealDouble1 */));
      })));
    }else{
      return B(A3(_7m/* GHC.Num.- */,_vD/* s1l8y */, _vA/* s1l8s */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_vD/* s1l8y */, _1M/* GHC.Float.$fRealDouble1 */));
      })));
    }
  }),
  _vE/* s1l8D */ = function(_vF/* s1l8E */){
    var _vG/* s1l8F */ = _vF/* s1l8E */-0.5;
    return (_vG/* s1l8F */>=0) ? (E(_vG/* s1l8F */)==0) ? (!B(_uq/* GHC.Real.even */(_vx/* s1l8p */, _vA/* s1l8s */))) ? E(_vC/* s1l8w */) : E(_vA/* s1l8s */) : E(_vC/* s1l8w */) : E(_vA/* s1l8s */);
  },
  _vH/* s1l8K */ = E(_vB/* s1l8u */);
  if(!_vH/* s1l8K */){
    return new F(function(){return _vE/* s1l8D */(0);});
  }else{
    if(_vH/* s1l8K */<=0){
      var _vI/* s1l8N */ =  -_vH/* s1l8K */-0.5;
      return (_vI/* s1l8N */>=0) ? (E(_vI/* s1l8N */)==0) ? (!B(_uq/* GHC.Real.even */(_vx/* s1l8p */, _vA/* s1l8s */))) ? E(_vC/* s1l8w */) : E(_vA/* s1l8s */) : E(_vC/* s1l8w */) : E(_vA/* s1l8s */);
    }else{
      return new F(function(){return _vE/* s1l8D */(_vH/* s1l8K */);});
    }
  }
},
_vJ/* $fRealFracDouble_$cround */ = function(_vK/* s1l8T */, _vL/* s1l8U */){
  return new F(function(){return _vw/* GHC.Float.$w$cround */(_vK/* s1l8T */, E(_vL/* s1l8U */));});
},
_vM/* $fRealFracDouble_$ctruncate */ = function(_vN/* s1l8i */, _vO/* s1l8j */){
  return E(B(_v3/* GHC.Float.$w$cproperFraction */(_vN/* s1l8i */, E(_vO/* s1l8j */))).a);
},
_vP/* $fRealFracDouble */ = {_:0,a:_qY/* GHC.Float.$fRealDouble */,b:_ip/* GHC.Float.$fFractionalDouble */,c:_vs/* GHC.Float.$fRealFracDouble_$cproperFraction */,d:_vM/* GHC.Float.$fRealFracDouble_$ctruncate */,e:_vJ/* GHC.Float.$fRealFracDouble_$cround */,f:_vg/* GHC.Float.$fRealFracDouble_$cceiling */,g:_vm/* GHC.Float.$fRealFracDouble_$cfloor */},
_vQ/* $fEnumInteger2 */ = new T1(0,1),
_vR/* $wenumDeltaInteger */ = function(_vS/* smF4 */, _vT/* smF5 */){
  var _vU/* smF6 */ = E(_vS/* smF4 */);
  return new T2(0,_vU/* smF6 */,new T(function(){
    var _vV/* smF8 */ = B(_vR/* GHC.Enum.$wenumDeltaInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_vU/* smF6 */, _vT/* smF5 */)), _vT/* smF5 */));
    return new T2(1,_vV/* smF8 */.a,_vV/* smF8 */.b);
  }));
},
_vW/* $fEnumInteger_$cenumFrom */ = function(_vX/* smFn */){
  var _vY/* smFo */ = B(_vR/* GHC.Enum.$wenumDeltaInteger */(_vX/* smFn */, _vQ/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_vY/* smFo */.a,_vY/* smFo */.b);
},
_vZ/* $fEnumInteger_$cenumFromThen */ = function(_w0/* smFr */, _w1/* smFs */){
  var _w2/* smFu */ = B(_vR/* GHC.Enum.$wenumDeltaInteger */(_w0/* smFr */, new T(function(){
    return B(_5w/* GHC.Integer.Type.minusInteger */(_w1/* smFs */, _w0/* smFr */));
  })));
  return new T2(1,_w2/* smFu */.a,_w2/* smFu */.b);
},
_w3/* $fEnumInteger1 */ = new T1(0,0),
_w4/* geInteger */ = function(_w5/* s1FG */, _w6/* s1FH */){
  var _w7/* s1FI */ = E(_w5/* s1FG */);
  if(!_w7/* s1FI */._){
    var _w8/* s1FJ */ = _w7/* s1FI */.a,
    _w9/* s1FK */ = E(_w6/* s1FH */);
    return (_w9/* s1FK */._==0) ? _w8/* s1FJ */>=_w9/* s1FK */.a : I_compareInt/* EXTERNAL */(_w9/* s1FK */.a, _w8/* s1FJ */)<=0;
  }else{
    var _wa/* s1FR */ = _w7/* s1FI */.a,
    _wb/* s1FS */ = E(_w6/* s1FH */);
    return (_wb/* s1FS */._==0) ? I_compareInt/* EXTERNAL */(_wa/* s1FR */, _wb/* s1FS */.a)>=0 : I_compare/* EXTERNAL */(_wa/* s1FR */, _wb/* s1FS */.a)>=0;
  }
},
_wc/* enumDeltaToInteger */ = function(_wd/* smFx */, _we/* smFy */, _wf/* smFz */){
  if(!B(_w4/* GHC.Integer.Type.geInteger */(_we/* smFy */, _w3/* GHC.Enum.$fEnumInteger1 */))){
    var _wg/* smFB */ = function(_wh/* smFC */){
      return (!B(_3N/* GHC.Integer.Type.ltInteger */(_wh/* smFC */, _wf/* smFz */))) ? new T2(1,_wh/* smFC */,new T(function(){
        return B(_wg/* smFB */(B(_3b/* GHC.Integer.Type.plusInteger */(_wh/* smFC */, _we/* smFy */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _wg/* smFB */(_wd/* smFx */);});
  }else{
    var _wi/* smFG */ = function(_wj/* smFH */){
      return (!B(_3E/* GHC.Integer.Type.gtInteger */(_wj/* smFH */, _wf/* smFz */))) ? new T2(1,_wj/* smFH */,new T(function(){
        return B(_wi/* smFG */(B(_3b/* GHC.Integer.Type.plusInteger */(_wj/* smFH */, _we/* smFy */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _wi/* smFG */(_wd/* smFx */);});
  }
},
_wk/* $fEnumInteger_$cenumFromThenTo */ = function(_wl/* smFY */, _wm/* smFZ */, _wn/* smG0 */){
  return new F(function(){return _wc/* GHC.Enum.enumDeltaToInteger */(_wl/* smFY */, B(_5w/* GHC.Integer.Type.minusInteger */(_wm/* smFZ */, _wl/* smFY */)), _wn/* smG0 */);});
},
_wo/* $fEnumInteger_$cenumFromTo */ = function(_wp/* smFW */, _wq/* smFX */){
  return new F(function(){return _wc/* GHC.Enum.enumDeltaToInteger */(_wp/* smFW */, _vQ/* GHC.Enum.$fEnumInteger2 */, _wq/* smFX */);});
},
_wr/* $fEnumInteger_$cfromEnum */ = function(_ws/* smEX */){
  return new F(function(){return _38/* GHC.Integer.Type.integerToInt */(_ws/* smEX */);});
},
_wt/* $fEnumInteger_$cpred */ = function(_wu/* smF3 */){
  return new F(function(){return _5w/* GHC.Integer.Type.minusInteger */(_wu/* smF3 */, _vQ/* GHC.Enum.$fEnumInteger2 */);});
},
_wv/* $fEnumInteger_$csucc */ = function(_ww/* smF2 */){
  return new F(function(){return _3b/* GHC.Integer.Type.plusInteger */(_ww/* smF2 */, _vQ/* GHC.Enum.$fEnumInteger2 */);});
},
_wx/* $fEnumInteger_$ctoEnum */ = function(_wy/* smEZ */){
  return new F(function(){return _pY/* GHC.Integer.Type.smallInteger */(E(_wy/* smEZ */));});
},
_wz/* $fEnumInteger */ = {_:0,a:_wv/* GHC.Enum.$fEnumInteger_$csucc */,b:_wt/* GHC.Enum.$fEnumInteger_$cpred */,c:_wx/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_wr/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_vW/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_vZ/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_wo/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_wk/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_wA/* divInteger */ = function(_wB/* s1Nz */, _wC/* s1NA */){
  while(1){
    var _wD/* s1NB */ = E(_wB/* s1Nz */);
    if(!_wD/* s1NB */._){
      var _wE/* s1ND */ = E(_wD/* s1NB */.a);
      if(_wE/* s1ND */==( -2147483648)){
        _wB/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _wF/* s1NE */ = E(_wC/* s1NA */);
        if(!_wF/* s1NE */._){
          return new T1(0,B(_rU/* GHC.Classes.divInt# */(_wE/* s1ND */, _wF/* s1NE */.a)));
        }else{
          _wB/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_wE/* s1ND */));
          _wC/* s1NA */ = _wF/* s1NE */;
          continue;
        }
      }
    }else{
      var _wG/* s1NO */ = _wD/* s1NB */.a,
      _wH/* s1NP */ = E(_wC/* s1NA */);
      return (_wH/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_wG/* s1NO */, I_fromInt/* EXTERNAL */(_wH/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_wG/* s1NO */, _wH/* s1NP */.a));
    }
  }
},
_wI/* $fIntegralInteger_$cdiv */ = function(_wJ/* svkR */, _wK/* svkS */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wK/* svkS */, _un/* GHC.Real.even1 */))){
    return new F(function(){return _wA/* GHC.Integer.Type.divInteger */(_wJ/* svkR */, _wK/* svkS */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wL/* divModInteger */ = function(_wM/* s1MF */, _wN/* s1MG */){
  while(1){
    var _wO/* s1MH */ = E(_wM/* s1MF */);
    if(!_wO/* s1MH */._){
      var _wP/* s1MJ */ = E(_wO/* s1MH */.a);
      if(_wP/* s1MJ */==( -2147483648)){
        _wM/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _wQ/* s1MK */ = E(_wN/* s1MG */);
        if(!_wQ/* s1MK */._){
          var _wR/* s1ML */ = _wQ/* s1MK */.a;
          return new T2(0,new T1(0,B(_rU/* GHC.Classes.divInt# */(_wP/* s1MJ */, _wR/* s1ML */))),new T1(0,B(_sq/* GHC.Classes.modInt# */(_wP/* s1MJ */, _wR/* s1ML */))));
        }else{
          _wM/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_wP/* s1MJ */));
          _wN/* s1MG */ = _wQ/* s1MK */;
          continue;
        }
      }
    }else{
      var _wS/* s1MY */ = E(_wN/* s1MG */);
      if(!_wS/* s1MY */._){
        _wM/* s1MF */ = _wO/* s1MH */;
        _wN/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_wS/* s1MY */.a));
        continue;
      }else{
        var _wT/* s1N5 */ = I_divMod/* EXTERNAL */(_wO/* s1MH */.a, _wS/* s1MY */.a);
        return new T2(0,new T1(1,_wT/* s1N5 */.a),new T1(1,_wT/* s1N5 */.b));
      }
    }
  }
},
_wU/* $fIntegralInteger_$cdivMod */ = function(_wV/* svkC */, _wW/* svkD */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wW/* svkD */, _un/* GHC.Real.even1 */))){
    var _wX/* svkF */ = B(_wL/* GHC.Integer.Type.divModInteger */(_wV/* svkC */, _wW/* svkD */));
    return new T2(0,_wX/* svkF */.a,_wX/* svkF */.b);
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wY/* modInteger */ = function(_wZ/* s1Na */, _x0/* s1Nb */){
  while(1){
    var _x1/* s1Nc */ = E(_wZ/* s1Na */);
    if(!_x1/* s1Nc */._){
      var _x2/* s1Ne */ = E(_x1/* s1Nc */.a);
      if(_x2/* s1Ne */==( -2147483648)){
        _wZ/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _x3/* s1Nf */ = E(_x0/* s1Nb */);
        if(!_x3/* s1Nf */._){
          return new T1(0,B(_sq/* GHC.Classes.modInt# */(_x2/* s1Ne */, _x3/* s1Nf */.a)));
        }else{
          _wZ/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_x2/* s1Ne */));
          _x0/* s1Nb */ = _x3/* s1Nf */;
          continue;
        }
      }
    }else{
      var _x4/* s1Np */ = _x1/* s1Nc */.a,
      _x5/* s1Nq */ = E(_x0/* s1Nb */);
      return (_x5/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_x4/* s1Np */, I_fromInt/* EXTERNAL */(_x5/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_x4/* s1Np */, _x5/* s1Nq */.a));
    }
  }
},
_x6/* $fIntegralInteger_$cmod */ = function(_x7/* svkO */, _x8/* svkP */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_x8/* svkP */, _un/* GHC.Real.even1 */))){
    return new F(function(){return _wY/* GHC.Integer.Type.modInteger */(_x7/* svkO */, _x8/* svkP */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_x9/* quotInteger */ = function(_xa/* s1On */, _xb/* s1Oo */){
  while(1){
    var _xc/* s1Op */ = E(_xa/* s1On */);
    if(!_xc/* s1Op */._){
      var _xd/* s1Or */ = E(_xc/* s1Op */.a);
      if(_xd/* s1Or */==( -2147483648)){
        _xa/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _xe/* s1Os */ = E(_xb/* s1Oo */);
        if(!_xe/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_xd/* s1Or */, _xe/* s1Os */.a));
        }else{
          _xa/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_xd/* s1Or */));
          _xb/* s1Oo */ = _xe/* s1Os */;
          continue;
        }
      }
    }else{
      var _xf/* s1OC */ = _xc/* s1Op */.a,
      _xg/* s1OD */ = E(_xb/* s1Oo */);
      return (_xg/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_xf/* s1OC */, I_fromInt/* EXTERNAL */(_xg/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_xf/* s1OC */, _xg/* s1OD */.a));
    }
  }
},
_xh/* $fIntegralInteger_$cquot */ = function(_xi/* svkX */, _xj/* svkY */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_xj/* svkY */, _un/* GHC.Real.even1 */))){
    return new F(function(){return _x9/* GHC.Integer.Type.quotInteger */(_xi/* svkX */, _xj/* svkY */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xk/* $fIntegralInteger_$cquotRem */ = function(_xl/* svkI */, _xm/* svkJ */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_xm/* svkJ */, _un/* GHC.Real.even1 */))){
    var _xn/* svkL */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_xl/* svkI */, _xm/* svkJ */));
    return new T2(0,_xn/* svkL */.a,_xn/* svkL */.b);
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xo/* remInteger */ = function(_xp/* s1NY */, _xq/* s1NZ */){
  while(1){
    var _xr/* s1O0 */ = E(_xp/* s1NY */);
    if(!_xr/* s1O0 */._){
      var _xs/* s1O2 */ = E(_xr/* s1O0 */.a);
      if(_xs/* s1O2 */==( -2147483648)){
        _xp/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _xt/* s1O3 */ = E(_xq/* s1NZ */);
        if(!_xt/* s1O3 */._){
          return new T1(0,_xs/* s1O2 */%_xt/* s1O3 */.a);
        }else{
          _xp/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_xs/* s1O2 */));
          _xq/* s1NZ */ = _xt/* s1O3 */;
          continue;
        }
      }
    }else{
      var _xu/* s1Od */ = _xr/* s1O0 */.a,
      _xv/* s1Oe */ = E(_xq/* s1NZ */);
      return (_xv/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_xu/* s1Od */, I_fromInt/* EXTERNAL */(_xv/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_xu/* s1Od */, _xv/* s1Oe */.a));
    }
  }
},
_xw/* $fIntegralInteger_$crem */ = function(_xx/* svkU */, _xy/* svkV */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_xy/* svkV */, _un/* GHC.Real.even1 */))){
    return new F(function(){return _xo/* GHC.Integer.Type.remInteger */(_xx/* svkU */, _xy/* svkV */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xz/* $fIntegralInteger_$ctoInteger */ = function(_xA/* svkB */){
  return E(_xA/* svkB */);
},
_xB/* $fNumInteger_$cfromInteger */ = function(_xC/* s6HS */){
  return E(_xC/* s6HS */);
},
_xD/* absInteger */ = function(_xE/* s1QP */){
  var _xF/* s1QQ */ = E(_xE/* s1QP */);
  if(!_xF/* s1QQ */._){
    var _xG/* s1QS */ = E(_xF/* s1QQ */.a);
    return (_xG/* s1QS */==( -2147483648)) ? E(_6a/* GHC.Integer.Type.lvl3 */) : (_xG/* s1QS */<0) ? new T1(0, -_xG/* s1QS */) : E(_xF/* s1QQ */);
  }else{
    var _xH/* s1QW */ = _xF/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_xH/* s1QW */, 0)>=0) ? E(_xF/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_xH/* s1QW */));
  }
},
_xI/* lvl */ = new T1(0,0),
_xJ/* lvl1 */ = new T1(0, -1),
_xK/* signumInteger */ = function(_xL/* s1OO */){
  var _xM/* s1OP */ = E(_xL/* s1OO */);
  if(!_xM/* s1OP */._){
    var _xN/* s1OQ */ = _xM/* s1OP */.a;
    return (_xN/* s1OQ */>=0) ? (E(_xN/* s1OQ */)==0) ? E(_xI/* GHC.Integer.Type.lvl */) : E(_3M/* GHC.Integer.Type.log2I1 */) : E(_xJ/* GHC.Integer.Type.lvl1 */);
  }else{
    var _xO/* s1OW */ = I_compareInt/* EXTERNAL */(_xM/* s1OP */.a, 0);
    return (_xO/* s1OW */<=0) ? (E(_xO/* s1OW */)==0) ? E(_xI/* GHC.Integer.Type.lvl */) : E(_xJ/* GHC.Integer.Type.lvl1 */) : E(_3M/* GHC.Integer.Type.log2I1 */);
  }
},
_xP/* $fNumInteger */ = {_:0,a:_3b/* GHC.Integer.Type.plusInteger */,b:_5w/* GHC.Integer.Type.minusInteger */,c:_tX/* GHC.Integer.Type.timesInteger */,d:_6b/* GHC.Integer.Type.negateInteger */,e:_xD/* GHC.Integer.Type.absInteger */,f:_xK/* GHC.Integer.Type.signumInteger */,g:_xB/* GHC.Num.$fNumInteger_$cfromInteger */},
_xQ/* neqInteger */ = function(_xR/* s1H2 */, _xS/* s1H3 */){
  var _xT/* s1H4 */ = E(_xR/* s1H2 */);
  if(!_xT/* s1H4 */._){
    var _xU/* s1H5 */ = _xT/* s1H4 */.a,
    _xV/* s1H6 */ = E(_xS/* s1H3 */);
    return (_xV/* s1H6 */._==0) ? _xU/* s1H5 */!=_xV/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_xV/* s1H6 */.a, _xU/* s1H5 */)==0) ? false : true;
  }else{
    var _xW/* s1Hc */ = _xT/* s1H4 */.a,
    _xX/* s1Hd */ = E(_xS/* s1H3 */);
    return (_xX/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_xW/* s1Hc */, _xX/* s1Hd */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_xW/* s1Hc */, _xX/* s1Hd */.a)==0) ? false : true;
  }
},
_xY/* $fEqInteger */ = new T2(0,_30/* GHC.Integer.Type.eqInteger */,_xQ/* GHC.Integer.Type.neqInteger */),
_xZ/* $fOrdInteger_$cmax */ = function(_y0/* s1HU */, _y1/* s1HV */){
  return (!B(_5h/* GHC.Integer.Type.leInteger */(_y0/* s1HU */, _y1/* s1HV */))) ? E(_y0/* s1HU */) : E(_y1/* s1HV */);
},
_y2/* $fOrdInteger_$cmin */ = function(_y3/* s1HR */, _y4/* s1HS */){
  return (!B(_5h/* GHC.Integer.Type.leInteger */(_y3/* s1HR */, _y4/* s1HS */))) ? E(_y4/* s1HS */) : E(_y3/* s1HR */);
},
_y5/* $fOrdInteger */ = {_:0,a:_xY/* GHC.Integer.Type.$fEqInteger */,b:_1N/* GHC.Integer.Type.compareInteger */,c:_3N/* GHC.Integer.Type.ltInteger */,d:_5h/* GHC.Integer.Type.leInteger */,e:_3E/* GHC.Integer.Type.gtInteger */,f:_w4/* GHC.Integer.Type.geInteger */,g:_xZ/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_y2/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_y6/* $fRealInteger_$s$cfromInteger */ = function(_y7/* svhv */){
  return new T2(0,E(_y7/* svhv */),E(_lJ/* GHC.Real.$fEnumRatio1 */));
},
_y8/* $fRealInteger */ = new T3(0,_xP/* GHC.Num.$fNumInteger */,_y5/* GHC.Integer.Type.$fOrdInteger */,_y6/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_y9/* $fIntegralInteger */ = {_:0,a:_y8/* GHC.Real.$fRealInteger */,b:_wz/* GHC.Enum.$fEnumInteger */,c:_xh/* GHC.Real.$fIntegralInteger_$cquot */,d:_xw/* GHC.Real.$fIntegralInteger_$crem */,e:_wI/* GHC.Real.$fIntegralInteger_$cdiv */,f:_x6/* GHC.Real.$fIntegralInteger_$cmod */,g:_xk/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_wU/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_xz/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_ya/* $p2RealFrac */ = function(_yb/* svbS */){
  return E(E(_yb/* svbS */).b);
},
_yc/* floor */ = function(_yd/* svcB */){
  return E(E(_yd/* svcB */).g);
},
_ye/* fmod1 */ = new T1(0,1),
_yf/* fmod */ = function(_yg/* s6np */, _yh/* s6nq */, _yi/* s6nr */){
  var _yj/* s6ns */ = B(_ya/* GHC.Real.$p2RealFrac */(_yg/* s6np */)),
  _yk/* s6nt */ = B(_7i/* GHC.Real.$p1Fractional */(_yj/* s6ns */)),
  _yl/* s6nA */ = new T(function(){
    var _ym/* s6nz */ = new T(function(){
      var _yn/* s6ny */ = new T(function(){
        var _yo/* s6nx */ = new T(function(){
          return B(A3(_yc/* GHC.Real.floor */,_yg/* s6np */, _y9/* GHC.Real.$fIntegralInteger */, new T(function(){
            return B(A3(_9b/* GHC.Real./ */,_yj/* s6ns */, _yh/* s6nq */, _yi/* s6nr */));
          })));
        });
        return B(A2(_91/* GHC.Num.fromInteger */,_yk/* s6nt */, _yo/* s6nx */));
      }),
      _yp/* s6nv */ = new T(function(){
        return B(A2(_6K/* GHC.Num.negate */,_yk/* s6nt */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_yk/* s6nt */, _ye/* Lib.Util.fmod1 */));
        })));
      });
      return B(A3(_7k/* GHC.Num.* */,_yk/* s6nt */, _yp/* s6nv */, _yn/* s6ny */));
    });
    return B(A3(_7k/* GHC.Num.* */,_yk/* s6nt */, _ym/* s6nz */, _yi/* s6nr */));
  });
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_yk/* s6nt */, _yh/* s6nq */, _yl/* s6nA */);});
},
_yq/* square2 */ = 1.5707963267948966,
_yr/* initial13 */ = function(_ys/* sBQd */){
  return 0.2/Math.cos/* EXTERNAL */(B(_yf/* Lib.Util.fmod */(_vP/* GHC.Float.$fRealFracDouble */, _ys/* sBQd */, _yq/* Lib.Object.square2 */))-0.7853981633974483);
},
_yt/* initial8 */ = 2,
_yu/* initial9 */ = 0.3,
_yv/* initial6 */ = new T(function(){
  var _yw/* sBQj */ = B(_oq/* Lib.Object.$wmake */(_yr/* Main.initial13 */, 1.2, _pU/* Main.initial12 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pT/* Main.initial10 */, _yu/* Main.initial9 */, _yt/* Main.initial8 */, _pI/* Main.initial11 */, _pI/* Main.initial11 */, _pP/* Main.initial7 */));
  return {_:0,a:E(_yw/* sBQj */.a),b:E(_yw/* sBQj */.b),c:E(_yw/* sBQj */.c),d:E(_yw/* sBQj */.d),e:E(_yw/* sBQj */.e),f:E(_yw/* sBQj */.f),g:E(_yw/* sBQj */.g),h:E(_yw/* sBQj */.h),i:E(_yw/* sBQj */.i)};
}),
_yx/* initial5 */ = new T2(1,_yv/* Main.initial6 */,_o/* GHC.Types.[] */),
_yy/* initial_ls */ = new T2(1,_pQ/* Main.initial14 */,_yx/* Main.initial5 */),
_yz/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative range size"));
}),
_yA/* negRange */ = new T(function(){
  return B(err/* EXTERNAL */(_yz/* GHC.Arr.lvl36 */));
}),
_yB/* initial3 */ = function(_/* EXTERNAL */){
  var _yC/* sBQv */ = B(_hf/* GHC.List.$wlenAcc */(_yy/* Main.initial_ls */, 0))-1|0,
  _yD/* sBQw */ = function(_yE/* sBQx */){
    if(_yE/* sBQx */>=0){
      var _yF/* sBQA */ = newArr/* EXTERNAL */(_yE/* sBQx */, _hl/* GHC.Arr.arrEleBottom */),
      _yG/* sBQC */ = _yF/* sBQA */,
      _yH/* sBQD */ = E(_yE/* sBQx */);
      if(!_yH/* sBQD */){
        return new T4(0,E(_pS/* Main.initial4 */),E(_yC/* sBQv */),0,_yG/* sBQC */);
      }else{
        var _yI/* sBQF */ = function(_yJ/* sBQP */, _yK/* sBQQ */, _/* EXTERNAL */){
          while(1){
            var _yL/* sBQS */ = E(_yJ/* sBQP */);
            if(!_yL/* sBQS */._){
              return E(_/* EXTERNAL */);
            }else{
              var _/* EXTERNAL */ = _yG/* sBQC */[_yK/* sBQQ */] = _yL/* sBQS */.a;
              if(_yK/* sBQQ */!=(_yH/* sBQD */-1|0)){
                var _yM/*  sBQQ */ = _yK/* sBQQ */+1|0;
                _yJ/* sBQP */ = _yL/* sBQS */.b;
                _yK/* sBQQ */ = _yM/*  sBQQ */;
                continue;
              }else{
                return E(_/* EXTERNAL */);
              }
            }
          }
        },
        _/* EXTERNAL */ = B((function(_yN/* sBQG */, _yO/* sBQH */, _yP/* sBQI */, _/* EXTERNAL */){
          var _/* EXTERNAL */ = _yG/* sBQC */[_yP/* sBQI */] = _yN/* sBQG */;
          if(_yP/* sBQI */!=(_yH/* sBQD */-1|0)){
            return new F(function(){return _yI/* sBQF */(_yO/* sBQH */, _yP/* sBQI */+1|0, _/* EXTERNAL */);});
          }else{
            return E(_/* EXTERNAL */);
          }
        })(_pQ/* Main.initial14 */, _yx/* Main.initial5 */, 0, _/* EXTERNAL */));
        return new T4(0,E(_pS/* Main.initial4 */),E(_yC/* sBQv */),_yH/* sBQD */,_yG/* sBQC */);
      }
    }else{
      return E(_yA/* GHC.Arr.negRange */);
    }
  };
  if(0>_yC/* sBQv */){
    return new F(function(){return _yD/* sBQw */(0);});
  }else{
    return new F(function(){return _yD/* sBQw */(_yC/* sBQv */+1|0);});
  }
},
_yQ/* runSTRep */ = function(_yR/* sjpo */){
  var _yS/* sjpp */ = B(A1(_yR/* sjpo */,_/* EXTERNAL */));
  return E(_yS/* sjpp */);
},
_yT/* initial2 */ = new T(function(){
  return B(_yQ/* GHC.ST.runSTRep */(_yB/* Main.initial3 */));
}),
_yU/* $fApplicativeIO1 */ = function(_yV/* s3he */, _yW/* s3hf */, _/* EXTERNAL */){
  var _yX/* s3hh */ = B(A1(_yV/* s3he */,_/* EXTERNAL */)),
  _yY/* s3hk */ = B(A1(_yW/* s3hf */,_/* EXTERNAL */));
  return _yX/* s3hh */;
},
_yZ/* $fApplicativeIO2 */ = function(_z0/* s3gs */, _z1/* s3gt */, _/* EXTERNAL */){
  var _z2/* s3gv */ = B(A1(_z0/* s3gs */,_/* EXTERNAL */)),
  _z3/* s3gy */ = B(A1(_z1/* s3gt */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_z2/* s3gv */,_z3/* s3gy */));
  });
},
_z4/* $fFunctorIO1 */ = function(_z5/* s3gX */, _z6/* s3gY */, _/* EXTERNAL */){
  var _z7/* s3h0 */ = B(A1(_z6/* s3gY */,_/* EXTERNAL */));
  return _z5/* s3gX */;
},
_z8/* $fFunctorIO2 */ = function(_z9/* s3gQ */, _za/* s3gR */, _/* EXTERNAL */){
  var _zb/* s3gT */ = B(A1(_za/* s3gR */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_z9/* s3gQ */,_zb/* s3gT */));
  });
},
_zc/* $fFunctorIO */ = new T2(0,_z8/* GHC.Base.$fFunctorIO2 */,_z4/* GHC.Base.$fFunctorIO1 */),
_zd/* returnIO1 */ = function(_ze/* s3g5 */, _/* EXTERNAL */){
  return _ze/* s3g5 */;
},
_zf/* thenIO1 */ = function(_zg/* s3fZ */, _zh/* s3g0 */, _/* EXTERNAL */){
  var _zi/* s3g2 */ = B(A1(_zg/* s3fZ */,_/* EXTERNAL */));
  return new F(function(){return A1(_zh/* s3g0 */,_/* EXTERNAL */);});
},
_zj/* $fApplicativeIO */ = new T5(0,_zc/* GHC.Base.$fFunctorIO */,_zd/* GHC.Base.returnIO1 */,_yZ/* GHC.Base.$fApplicativeIO2 */,_zf/* GHC.Base.thenIO1 */,_yU/* GHC.Base.$fApplicativeIO1 */),
_zk/* $fIx(,)_$cunsafeRangeSize */ = function(_zl/* sLFI */){
  var _zm/* sLFJ */ = E(_zl/* sLFI */);
  return (E(_zm/* sLFJ */.b)-E(_zm/* sLFJ */.a)|0)+1|0;
},
_zn/* $fIxInt_$cinRange */ = function(_zo/* sLHc */, _zp/* sLHd */){
  var _zq/* sLHe */ = E(_zo/* sLHc */),
  _zr/* sLHl */ = E(_zp/* sLHd */);
  return (E(_zq/* sLHe */.a)>_zr/* sLHl */) ? false : _zr/* sLHl */<=E(_zq/* sLHe */.b);
},
_zs/* itos */ = function(_zt/* sf6u */, _zu/* sf6v */){
  var _zv/* sf6x */ = jsShowI/* EXTERNAL */(_zt/* sf6u */);
  return new F(function(){return _f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_zv/* sf6x */), _zu/* sf6v */);});
},
_zw/* $wshowSignedInt */ = function(_zx/* sf6C */, _zy/* sf6D */, _zz/* sf6E */){
  if(_zy/* sf6D */>=0){
    return new F(function(){return _zs/* GHC.Show.itos */(_zy/* sf6D */, _zz/* sf6E */);});
  }else{
    if(_zx/* sf6C */<=6){
      return new F(function(){return _zs/* GHC.Show.itos */(_zy/* sf6D */, _zz/* sf6E */);});
    }else{
      return new T2(1,_71/* GHC.Show.shows8 */,new T(function(){
        var _zA/* sf6K */ = jsShowI/* EXTERNAL */(_zy/* sf6D */);
        return B(_f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_zA/* sf6K */), new T2(1,_70/* GHC.Show.shows7 */,_zz/* sf6E */)));
      }));
    }
  }
},
_zB/* $fShowInt_$cshow */ = function(_zC/* sfaP */){
  return new F(function(){return _zw/* GHC.Show.$wshowSignedInt */(0, E(_zC/* sfaP */), _o/* GHC.Types.[] */);});
},
_zD/* showSignedInt */ = function(_zE/* sf6R */, _zF/* sf6S */, _zG/* sf6T */){
  return new F(function(){return _zw/* GHC.Show.$wshowSignedInt */(E(_zE/* sf6R */), E(_zF/* sf6S */), _zG/* sf6T */);});
},
_zH/* shows6 */ = function(_zI/* sf9f */, _zJ/* sf9g */){
  return new F(function(){return _zw/* GHC.Show.$wshowSignedInt */(0, E(_zI/* sf9f */), _zJ/* sf9g */);});
},
_zK/* shows_$cshowList1 */ = function(_zL/* sfaI */, _zM/* sfaJ */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_zH/* GHC.Show.shows6 */, _zL/* sfaI */, _zM/* sfaJ */);});
},
_zN/* $fShowInt */ = new T3(0,_zD/* GHC.Show.showSignedInt */,_zB/* GHC.Show.$fShowInt_$cshow */,_zK/* GHC.Show.shows_$cshowList1 */),
_zO/* $fIxChar1 */ = 0,
_zP/* $fShow(,)1 */ = function(_zQ/* sfbb */, _zR/* sfbc */, _zS/* sfbd */){
  return new F(function(){return A1(_zQ/* sfbb */,new T2(1,_2y/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_zR/* sfbc */,_zS/* sfbd */));
  })));});
},
_zT/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_zU/* lvl8 */ = new T(function(){
  return B(_l9/* GHC.List.errorEmptyList */(_zT/* GHC.List.lvl7 */));
}),
_zV/* foldr1 */ = function(_zW/* sbKQ */, _zX/* sbKR */){
  var _zY/* sbKS */ = E(_zX/* sbKR */);
  if(!_zY/* sbKS */._){
    return E(_zU/* GHC.List.lvl8 */);
  }else{
    var _zZ/* sbKT */ = _zY/* sbKS */.a,
    _A0/* sbKV */ = E(_zY/* sbKS */.b);
    if(!_A0/* sbKV */._){
      return E(_zZ/* sbKT */);
    }else{
      return new F(function(){return A2(_zW/* sbKQ */,_zZ/* sbKT */, new T(function(){
        return B(_zV/* GHC.List.foldr1 */(_zW/* sbKQ */, _A0/* sbKV */));
      }));});
    }
  }
},
_A1/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" out of range "));
}),
_A2/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}.index: Index "));
}),
_A3/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ix{"));
}),
_A4/* lvl16 */ = new T2(1,_70/* GHC.Show.shows7 */,_o/* GHC.Types.[] */),
_A5/* lvl17 */ = new T2(1,_70/* GHC.Show.shows7 */,_A4/* GHC.Arr.lvl16 */),
_A6/* shows14 */ = 0,
_A7/* showsPrec */ = function(_A8/* sf65 */){
  return E(E(_A8/* sf65 */).a);
},
_A9/* lvl18 */ = function(_Aa/* sL5Y */, _Ab/* sL5Z */, _Ac/* sL60 */, _Ad/* sL61 */, _Ae/* sL62 */){
  var _Af/* sL6f */ = new T(function(){
    var _Ag/* sL6e */ = new T(function(){
      var _Ah/* sL6c */ = new T(function(){
        var _Ai/* sL6a */ = new T(function(){
          var _Aj/* sL67 */ = new T(function(){
            return B(A3(_zV/* GHC.List.foldr1 */,_zP/* GHC.Show.$fShow(,)1 */, new T2(1,new T(function(){
              return B(A3(_A7/* GHC.Show.showsPrec */,_Ac/* sL60 */, _A6/* GHC.Show.shows14 */, _Ad/* sL61 */));
            }),new T2(1,new T(function(){
              return B(A3(_A7/* GHC.Show.showsPrec */,_Ac/* sL60 */, _A6/* GHC.Show.shows14 */, _Ae/* sL62 */));
            }),_o/* GHC.Types.[] */)), _A5/* GHC.Arr.lvl17 */));
          });
          return B(_f/* GHC.Base.++ */(_A1/* GHC.Arr.lvl13 */, new T2(1,_71/* GHC.Show.shows8 */,new T2(1,_71/* GHC.Show.shows8 */,_Aj/* sL67 */))));
        });
        return B(A(_A7/* GHC.Show.showsPrec */,[_Ac/* sL60 */, _zO/* GHC.Arr.$fIxChar1 */, _Ab/* sL5Z */, new T2(1,_70/* GHC.Show.shows7 */,_Ai/* sL6a */)]));
      });
      return B(_f/* GHC.Base.++ */(_A2/* GHC.Arr.lvl14 */, new T2(1,_71/* GHC.Show.shows8 */,_Ah/* sL6c */)));
    },1);
    return B(_f/* GHC.Base.++ */(_Aa/* sL5Y */, _Ag/* sL6e */));
  },1);
  return new F(function(){return err/* EXTERNAL */(B(_f/* GHC.Base.++ */(_A3/* GHC.Arr.lvl15 */, _Af/* sL6f */)));});
},
_Ak/* $wlvl4 */ = function(_Al/* sL6h */, _Am/* sL6i */, _An/* sL6j */, _Ao/* sL6k */, _Ap/* sL6l */){
  return new F(function(){return _A9/* GHC.Arr.lvl18 */(_Al/* sL6h */, _Am/* sL6i */, _Ap/* sL6l */, _An/* sL6j */, _Ao/* sL6k */);});
},
_Aq/* lvl19 */ = function(_Ar/* sL6m */, _As/* sL6n */, _At/* sL6o */, _Au/* sL6p */){
  var _Av/* sL6q */ = E(_At/* sL6o */);
  return new F(function(){return _Ak/* GHC.Arr.$wlvl4 */(_Ar/* sL6m */, _As/* sL6n */, _Av/* sL6q */.a, _Av/* sL6q */.b, _Au/* sL6p */);});
},
_Aw/* indexError */ = function(_Ax/* sLxR */, _Ay/* sLxS */, _Az/* sLxT */, _AA/* sLxU */){
  return new F(function(){return _Aq/* GHC.Arr.lvl19 */(_AA/* sLxU */, _Az/* sLxT */, _Ay/* sLxS */, _Ax/* sLxR */);});
},
_AB/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int"));
}),
_AC/* lvl40 */ = function(_AD/* sLHv */, _AE/* sLHw */){
  return new F(function(){return _Aw/* GHC.Arr.indexError */(_zN/* GHC.Show.$fShowInt */, _AD/* sLHv */, _AE/* sLHw */, _AB/* GHC.Arr.lvl20 */);});
},
_AF/* $fIxInt_$cindex */ = function(_AG/* sLHx */, _AH/* sLHy */){
  var _AI/* sLHz */ = E(_AG/* sLHx */),
  _AJ/* sLHC */ = E(_AI/* sLHz */.a),
  _AK/* sLHG */ = E(_AH/* sLHy */);
  if(_AJ/* sLHC */>_AK/* sLHG */){
    return new F(function(){return _AC/* GHC.Arr.lvl40 */(_AI/* sLHz */, _AK/* sLHG */);});
  }else{
    if(_AK/* sLHG */>E(_AI/* sLHz */.b)){
      return new F(function(){return _AC/* GHC.Arr.lvl40 */(_AI/* sLHz */, _AK/* sLHG */);});
    }else{
      return _AK/* sLHG */-_AJ/* sLHC */|0;
    }
  }
},
_AL/* $fIxInt_$crange */ = function(_AM/* sLHN */){
  var _AN/* sLHO */ = E(_AM/* sLHN */);
  return new F(function(){return _rE/* GHC.Enum.$fEnumInt_$cenumFromTo */(_AN/* sLHO */.a, _AN/* sLHO */.b);});
},
_AO/* $fIxInt_$crangeSize */ = function(_AP/* sLH0 */){
  var _AQ/* sLH1 */ = E(_AP/* sLH0 */),
  _AR/* sLH4 */ = E(_AQ/* sLH1 */.a),
  _AS/* sLH6 */ = E(_AQ/* sLH1 */.b);
  return (_AR/* sLH4 */>_AS/* sLH6 */) ? E(_zO/* GHC.Arr.$fIxChar1 */) : (_AS/* sLH6 */-_AR/* sLH4 */|0)+1|0;
},
_AT/* $fIxInt_$cunsafeIndex */ = function(_AU/* sLHq */, _AV/* sLHr */){
  return new F(function(){return _t3/* GHC.Num.$fNumInt_$c- */(_AV/* sLHr */, E(_AU/* sLHq */).a);});
},
_AW/* $fIxInt */ = {_:0,a:_tT/* GHC.Classes.$fOrdInt */,b:_AL/* GHC.Arr.$fIxInt_$crange */,c:_AF/* GHC.Arr.$fIxInt_$cindex */,d:_AT/* GHC.Arr.$fIxInt_$cunsafeIndex */,e:_zn/* GHC.Arr.$fIxInt_$cinRange */,f:_AO/* GHC.Arr.$fIxInt_$crangeSize */,g:_zk/* GHC.Arr.$fIx(,)_$cunsafeRangeSize */},
_AX/* : */ = function(_AY/* B2 */, _AZ/* B1 */){
  return new T2(1,_AY/* B2 */,_AZ/* B1 */);
},
_B0/* bounds */ = function(_B1/* sLl6 */, _B2/* sLl7 */){
  var _B3/* sLl8 */ = E(_B2/* sLl7 */);
  return new T2(0,_B3/* sLl8 */.a,_B3/* sLl8 */.b);
},
_B4/* rangeSize */ = function(_B5/* sL3K */){
  return E(E(_B5/* sL3K */).f);
},
_B6/* listArray */ = function(_B7/* sLrT */, _B8/* sLrU */, _B9/* sLrV */){
  var _Ba/* sLrW */ = E(_B8/* sLrU */),
  _Bb/* sLrX */ = _Ba/* sLrW */.a,
  _Bc/* sLrY */ = _Ba/* sLrW */.b,
  _Bd/* sLsy */ = function(_/* EXTERNAL */){
    var _Be/* sLs0 */ = B(A2(_B4/* GHC.Arr.rangeSize */,_B7/* sLrT */, _Ba/* sLrW */));
    if(_Be/* sLs0 */>=0){
      var _Bf/* sLs4 */ = newArr/* EXTERNAL */(_Be/* sLs0 */, _hl/* GHC.Arr.arrEleBottom */),
      _Bg/* sLs6 */ = _Bf/* sLs4 */,
      _Bh/* sLs7 */ = E(_Be/* sLs0 */);
      if(!_Bh/* sLs7 */){
        return new T(function(){
          return new T4(0,E(_Bb/* sLrX */),E(_Bc/* sLrY */),0,_Bg/* sLs6 */);
        });
      }else{
        var _Bi/* sLs8 */ = function(_Bj/* sLs9 */, _Bk/* sLsa */, _/* EXTERNAL */){
          while(1){
            var _Bl/* sLsc */ = E(_Bj/* sLs9 */);
            if(!_Bl/* sLsc */._){
              return E(_/* EXTERNAL */);
            }else{
              var _/* EXTERNAL */ = _Bg/* sLs6 */[_Bk/* sLsa */] = _Bl/* sLsc */.a;
              if(_Bk/* sLsa */!=(_Bh/* sLs7 */-1|0)){
                var _Bm/*  sLsa */ = _Bk/* sLsa */+1|0;
                _Bj/* sLs9 */ = _Bl/* sLsc */.b;
                _Bk/* sLsa */ = _Bm/*  sLsa */;
                continue;
              }else{
                return E(_/* EXTERNAL */);
              }
            }
          }
        },
        _/* EXTERNAL */ = B(_Bi/* sLs8 */(_B9/* sLrV */, 0, _/* EXTERNAL */));
        return new T(function(){
          return new T4(0,E(_Bb/* sLrX */),E(_Bc/* sLrY */),_Bh/* sLs7 */,_Bg/* sLs6 */);
        });
      }
    }else{
      return E(_yA/* GHC.Arr.negRange */);
    }
  };
  return new F(function(){return _yQ/* GHC.ST.runSTRep */(_Bd/* sLsy */);});
},
_Bn/* $w$ctraverse */ = function(_Bo/* s5AkJ */, _Bp/* s5AkK */, _Bq/* s5AkL */, _Br/* s5AkM */){
  var _Bs/* s5Alb */ = new T(function(){
    var _Bt/* s5AkQ */ = E(_Br/* s5AkM */),
    _Bu/* s5AkV */ = _Bt/* s5AkQ */.c-1|0,
    _Bv/* s5AkW */ = new T(function(){
      return B(A2(_cX/* GHC.Base.pure */,_Bp/* s5AkK */, _o/* GHC.Types.[] */));
    });
    if(0<=_Bu/* s5AkV */){
      var _Bw/* s5AkZ */ = new T(function(){
        return B(_97/* GHC.Base.$p1Applicative */(_Bp/* s5AkK */));
      }),
      _Bx/* s5Al0 */ = function(_By/* s5Al1 */){
        var _Bz/* s5Al6 */ = new T(function(){
          var _BA/* s5Al5 */ = new T(function(){
            return B(A1(_Bq/* s5AkL */,new T(function(){
              return E(_Bt/* s5AkQ */.d[_By/* s5Al1 */]);
            })));
          });
          return B(A3(_9f/* GHC.Base.fmap */,_Bw/* s5AkZ */, _AX/* GHC.Types.: */, _BA/* s5Al5 */));
        });
        return new F(function(){return A3(_9d/* GHC.Base.<*> */,_Bp/* s5AkK */, _Bz/* s5Al6 */, new T(function(){
          if(_By/* s5Al1 */!=_Bu/* s5AkV */){
            return B(_Bx/* s5Al0 */(_By/* s5Al1 */+1|0));
          }else{
            return E(_Bv/* s5AkW */);
          }
        }));});
      };
      return B(_Bx/* s5Al0 */(0));
    }else{
      return E(_Bv/* s5AkW */);
    }
  }),
  _BB/* s5AkO */ = new T(function(){
    return B(_B0/* GHC.Arr.bounds */(_Bo/* s5AkJ */, _Br/* s5AkM */));
  });
  return new F(function(){return A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_Bp/* s5AkK */)), function(_BC/* B1 */){
    return new F(function(){return _B6/* GHC.Arr.listArray */(_Bo/* s5AkJ */, _BB/* s5AkO */, _BC/* B1 */);});
  }, _Bs/* s5Alb */);});
},
_BD/* () */ = 0,
_BE/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _BD/* GHC.Tuple.() */;
},
_BF/* drawTriangles_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(drawTriangles)");
}),
_BG/* drawTriangles1 */ = function(_/* EXTERNAL */){
  var _BH/* s4h1 */ = __app0/* EXTERNAL */(E(_BF/* Lib.Screen.drawTriangles_f1 */));
  return new F(function(){return _BE/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_BI/* vertex_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(vertex)");
}),
_BJ/* $wa */ = function(_BK/* sfkK */, _BL/* sfkL */, _BM/* sfkM */, _BN/* sfkN */, _BO/* sfkO */, _BP/* sfkP */, _BQ/* sfkQ */, _BR/* sfkR */, _BS/* sfkS */, _/* EXTERNAL */){
  var _BT/* sfkU */ = E(_BR/* sfkR */);
  if(!_BT/* sfkU */._){
    return new F(function(){return _BG/* Lib.Screen.drawTriangles1 */(_/* EXTERNAL */);});
  }else{
    var _BU/* sfkX */ = E(_BT/* sfkU */.a),
    _BV/* sfl1 */ = E(_BU/* sfkX */.a),
    _BW/* sfl5 */ = E(_BV/* sfl1 */.a),
    _BX/* sfl9 */ = E(_BV/* sfl1 */.b),
    _BY/* sflj */ = E(_BU/* sfkX */.b),
    _BZ/* sfln */ = E(_BY/* sflj */.a),
    _C0/* sflr */ = E(_BY/* sflj */.b),
    _C1/* sflB */ = E(_BU/* sfkX */.c),
    _C2/* sflF */ = E(_C1/* sflB */.a),
    _C3/* sflJ */ = E(_C1/* sflB */.b),
    _C4/* sflT */ = E(_BI/* Lib.Screen.vertex_f1 */),
    _C5/* sflW */ = __apply/* EXTERNAL */(_C4/* sflT */, new T2(1,_BV/* sfl1 */.c,new T2(1,_BX/* sfl9 */.b,new T2(1,_BX/* sfl9 */.a,new T2(1,_BW/* sfl5 */.c,new T2(1,_BW/* sfl5 */.b,new T2(1,_BW/* sfl5 */.a,_o/* GHC.Types.[] */))))))),
    _C6/* sfm0 */ = __apply/* EXTERNAL */(_C4/* sflT */, new T2(1,_BY/* sflj */.c,new T2(1,_C0/* sflr */.b,new T2(1,_C0/* sflr */.a,new T2(1,_BZ/* sfln */.c,new T2(1,_BZ/* sfln */.b,new T2(1,_BZ/* sfln */.a,_o/* GHC.Types.[] */))))))),
    _C7/* sfm4 */ = __apply/* EXTERNAL */(_C4/* sflT */, new T2(1,_C1/* sflB */.c,new T2(1,_C3/* sflJ */.b,new T2(1,_C3/* sflJ */.a,new T2(1,_C2/* sflF */.c,new T2(1,_C2/* sflF */.b,new T2(1,_C2/* sflF */.a,_o/* GHC.Types.[] */))))))),
    _C8/* sfm7 */ = function(_C9/* sfm8 */, _/* EXTERNAL */){
      while(1){
        var _Ca/* sfma */ = E(_C9/* sfm8 */);
        if(!_Ca/* sfma */._){
          return _BD/* GHC.Tuple.() */;
        }else{
          var _Cb/* sfmd */ = E(_Ca/* sfma */.a),
          _Cc/* sfmh */ = E(_Cb/* sfmd */.a),
          _Cd/* sfml */ = E(_Cc/* sfmh */.a),
          _Ce/* sfmp */ = E(_Cc/* sfmh */.b),
          _Cf/* sfmz */ = E(_Cb/* sfmd */.b),
          _Cg/* sfmD */ = E(_Cf/* sfmz */.a),
          _Ch/* sfmH */ = E(_Cf/* sfmz */.b),
          _Ci/* sfmR */ = E(_Cb/* sfmd */.c),
          _Cj/* sfmV */ = E(_Ci/* sfmR */.a),
          _Ck/* sfmZ */ = E(_Ci/* sfmR */.b),
          _Cl/* sfna */ = __apply/* EXTERNAL */(_C4/* sflT */, new T2(1,_Cc/* sfmh */.c,new T2(1,_Ce/* sfmp */.b,new T2(1,_Ce/* sfmp */.a,new T2(1,_Cd/* sfml */.c,new T2(1,_Cd/* sfml */.b,new T2(1,_Cd/* sfml */.a,_o/* GHC.Types.[] */))))))),
          _Cm/* sfne */ = __apply/* EXTERNAL */(_C4/* sflT */, new T2(1,_Cf/* sfmz */.c,new T2(1,_Ch/* sfmH */.b,new T2(1,_Ch/* sfmH */.a,new T2(1,_Cg/* sfmD */.c,new T2(1,_Cg/* sfmD */.b,new T2(1,_Cg/* sfmD */.a,_o/* GHC.Types.[] */))))))),
          _Cn/* sfni */ = __apply/* EXTERNAL */(_C4/* sflT */, new T2(1,_Ci/* sfmR */.c,new T2(1,_Ck/* sfmZ */.b,new T2(1,_Ck/* sfmZ */.a,new T2(1,_Cj/* sfmV */.c,new T2(1,_Cj/* sfmV */.b,new T2(1,_Cj/* sfmV */.a,_o/* GHC.Types.[] */)))))));
          _C9/* sfm8 */ = _Ca/* sfma */.b;
          continue;
        }
      }
    },
    _Co/* sfnl */ = B(_C8/* sfm7 */(_BT/* sfkU */.b, _/* EXTERNAL */));
    return new F(function(){return _BG/* Lib.Screen.drawTriangles1 */(_/* EXTERNAL */);});
  }
},
_Cp/* drawObject1 */ = function(_Cq/* sfno */, _/* EXTERNAL */){
  var _Cr/* sfnq */ = E(_Cq/* sfno */);
  return new F(function(){return _BJ/* Lib.Object.$wa */(_Cr/* sfnq */.a, _Cr/* sfnq */.b, _Cr/* sfnq */.c, _Cr/* sfnq */.d, _Cr/* sfnq */.e, _Cr/* sfnq */.f, _Cr/* sfnq */.g, _Cr/* sfnq */.h, _Cr/* sfnq */.i, _/* EXTERNAL */);});
},
_Cs/* draw_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(draw)");
}),
_Ct/* $fApplicativeIdentity2 */ = function(_Cu/* s6Rmj */){
  return E(_Cu/* s6Rmj */);
},
_Cv/* $fApplicativeIdentity3 */ = function(_Cw/* s6RlP */){
  return E(_Cw/* s6RlP */);
},
_Cx/* $fApplicativeIdentity_$c*> */ = function(_Cy/* s6Ro6 */, _Cz/* s6Ro7 */){
  return E(_Cz/* s6Ro7 */);
},
_CA/* $fFunctorIdentity1 */ = function(_CB/* s6RlM */, _CC/* s6RlN */){
  return E(_CB/* s6RlM */);
},
_CD/* $fFunctorIdentity2 */ = function(_CE/* s6Rmk */){
  return E(_CE/* s6Rmk */);
},
_CF/* $fFunctorIdentity */ = new T2(0,_CD/* Data.Functor.Identity.$fFunctorIdentity2 */,_CA/* Data.Functor.Identity.$fFunctorIdentity1 */),
_CG/* a1 */ = function(_CH/* s6Ro8 */, _CI/* s6Ro9 */){
  return E(_CH/* s6Ro8 */);
},
_CJ/* $fApplicativeIdentity */ = new T5(0,_CF/* Data.Functor.Identity.$fFunctorIdentity */,_Cv/* Data.Functor.Identity.$fApplicativeIdentity3 */,_Ct/* Data.Functor.Identity.$fApplicativeIdentity2 */,_Cx/* Data.Functor.Identity.$fApplicativeIdentity_$c*> */,_CG/* Data.Functor.Identity.a1 */),
_CK/* $fShowDouble_$cshow */ = function(_CL/* s1lc7 */){
  var _CM/* s1lcb */ = jsShow/* EXTERNAL */(E(_CL/* s1lc7 */));
  return new F(function(){return fromJSStr/* EXTERNAL */(_CM/* s1lcb */);});
},
_CN/* jsShowD1 */ = function(_CO/* s7sI */){
  var _CP/* s7sM */ = jsShow/* EXTERNAL */(E(_CO/* s7sI */));
  return new F(function(){return fromJSStr/* EXTERNAL */(_CP/* s7sM */);});
},
_CQ/* $fShowDouble1 */ = function(_CR/* s1kz8 */){
  var _CS/* s1kz9 */ = new T(function(){
    return B(_CN/* GHC.HastePrim.jsShowD1 */(_CR/* s1kz8 */));
  });
  return function(_CT/* _fa_1 */){
    return new F(function(){return _f/* GHC.Base.++ */(_CS/* s1kz9 */, _CT/* _fa_1 */);});
  };
},
_CU/* $fShowDouble_$cshowList */ = function(_CV/* B2 */, _CW/* B1 */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_CQ/* GHC.Float.$fShowDouble1 */, _CV/* B2 */, _CW/* B1 */);});
},
_CX/* $fShowDouble_$cshowsPrec */ = function(_CY/* s1lcf */, _CZ/* s1lcg */){
  var _D0/* s1lch */ = new T(function(){
    return B(_CN/* GHC.HastePrim.jsShowD1 */(_CZ/* s1lcg */));
  });
  return function(_CT/* _fa_1 */){
    return new F(function(){return _f/* GHC.Base.++ */(_D0/* s1lch */, _CT/* _fa_1 */);});
  };
},
_D1/* $fShowDouble */ = new T3(0,_CX/* GHC.Float.$fShowDouble_$cshowsPrec */,_CK/* GHC.Float.$fShowDouble_$cshow */,_CU/* GHC.Float.$fShowDouble_$cshowList */),
_D2/* $fShowWorld2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World "));
}),
_D3/* $fShowWorld3 */ = 11,
_D4/* showSpace1 */ = 32,
_D5/* $w$cshowsPrec */ = function(_D6/* s5go */, _D7/* s5gp */, _D8/* s5gq */, _D9/* s5gr */, _Da/* s5gs */){
  var _Db/* s5gt */ = new T(function(){
    return B(A3(_A7/* GHC.Show.showsPrec */,_D6/* s5go */, _D3/* Lib.World.$fShowWorld3 */, _D8/* s5gq */));
  }),
  _Dc/* s5gu */ = new T(function(){
    return B(A3(_A7/* GHC.Show.showsPrec */,_D6/* s5go */, _D3/* Lib.World.$fShowWorld3 */, _D9/* s5gr */));
  }),
  _Dd/* s5gv */ = new T(function(){
    return B(A3(_A7/* GHC.Show.showsPrec */,_D6/* s5go */, _D3/* Lib.World.$fShowWorld3 */, _Da/* s5gs */));
  }),
  _De/* s5gw */ = function(_Df/* s5gx */){
    var _Dg/* s5gC */ = new T(function(){
      var _Dh/* s5gA */ = new T(function(){
        return B(A1(_Dc/* s5gu */,new T2(1,_D4/* GHC.Show.showSpace1 */,new T(function(){
          return B(A1(_Dd/* s5gv */,_Df/* s5gx */));
        }))));
      });
      return B(A1(_Db/* s5gt */,new T2(1,_D4/* GHC.Show.showSpace1 */,_Dh/* s5gA */)));
    },1);
    return new F(function(){return _f/* GHC.Base.++ */(_D2/* Lib.World.$fShowWorld2 */, _Dg/* s5gC */);});
  };
  if(_D7/* s5gp */<11){
    return E(_De/* s5gw */);
  }else{
    var _Di/* s5gI */ = function(_Dj/* s5gF */){
      return new T2(1,_71/* GHC.Show.shows8 */,new T(function(){
        return B(_De/* s5gw */(new T2(1,_70/* GHC.Show.shows7 */,_Dj/* s5gF */)));
      }));
    };
    return E(_Di/* s5gI */);
  }
},
_Dk/* $fShowContactPoint9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Local "));
}),
_Dl/* $fShowLocal2 */ = 11,
_Dm/* $w$cshowsPrec1 */ = function(_Dn/* snbU */, _Do/* snbV */, _Dp/* snbW */, _Dq/* snbX */){
  var _Dr/* snbY */ = new T(function(){
    return B(A3(_A7/* GHC.Show.showsPrec */,_Dn/* snbU */, _Dl/* Lib.Constraint.$fShowLocal2 */, _Dp/* snbW */));
  }),
  _Ds/* snbZ */ = new T(function(){
    return B(A3(_A7/* GHC.Show.showsPrec */,_Dn/* snbU */, _Dl/* Lib.Constraint.$fShowLocal2 */, _Dq/* snbX */));
  });
  if(_Do/* snbV */<11){
    var _Dt/* snc6 */ = function(_Du/* snc2 */){
      var _Dv/* snc5 */ = new T(function(){
        return B(A1(_Dr/* snbY */,new T2(1,_D4/* GHC.Show.showSpace1 */,new T(function(){
          return B(A1(_Ds/* snbZ */,_Du/* snc2 */));
        }))));
      },1);
      return new F(function(){return _f/* GHC.Base.++ */(_Dk/* Lib.Constraint.$fShowContactPoint9 */, _Dv/* snc5 */);});
    };
    return E(_Dt/* snc6 */);
  }else{
    var _Dw/* sncd */ = function(_Dx/* snc7 */){
      var _Dy/* sncc */ = new T(function(){
        var _Dz/* sncb */ = new T(function(){
          return B(A1(_Dr/* snbY */,new T2(1,_D4/* GHC.Show.showSpace1 */,new T(function(){
            return B(A1(_Ds/* snbZ */,new T2(1,_70/* GHC.Show.shows7 */,_Dx/* snc7 */)));
          }))));
        },1);
        return B(_f/* GHC.Base.++ */(_Dk/* Lib.Constraint.$fShowContactPoint9 */, _Dz/* sncb */));
      });
      return new T2(1,_71/* GHC.Show.shows8 */,_Dy/* sncc */);
    };
    return E(_Dw/* sncd */);
  }
},
_DA/* $wlvl8 */ = function(_DB/* sypP */, _DC/* sypQ */, _DD/* sypR */){
  var _DE/* syq4 */ = new T(function(){
    return B(A3(_zV/* GHC.List.foldr1 */,_zP/* GHC.Show.$fShow(,)1 */, new T2(1,new T(function(){
      var _DF/* sypS */ = E(_DB/* sypP */);
      return B(_D5/* Lib.World.$w$cshowsPrec */(_D1/* GHC.Float.$fShowDouble */, 0, _DF/* sypS */.a, _DF/* sypS */.b, _DF/* sypS */.c));
    }),new T2(1,new T(function(){
      var _DG/* sypX */ = E(_DC/* sypQ */);
      return B(_Dm/* Lib.Constraint.$w$cshowsPrec1 */(_D1/* GHC.Float.$fShowDouble */, 0, _DG/* sypX */.a, _DG/* sypX */.b));
    }),_o/* GHC.Types.[] */)), new T2(1,_70/* GHC.Show.shows7 */,_DD/* sypR */)));
  });
  return new T2(0,_71/* GHC.Show.shows8 */,_DE/* syq4 */);
},
_DH/* lvl27 */ = function(_DI/* syq5 */, _DJ/* syq6 */){
  var _DK/* syq7 */ = E(_DI/* syq5 */),
  _DL/* syqa */ = B(_DA/* Lib.Physics.$wlvl8 */(_DK/* syq7 */.a, _DK/* syq7 */.b, _DJ/* syq6 */));
  return new T2(1,_DL/* syqa */.a,_DL/* syqa */.b);
},
_DM/* $s$fShow(,)_$s$fShow(,)_$cshowList */ = function(_DN/* syxJ */, _DO/* syxK */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_DH/* Lib.Physics.lvl27 */, _DN/* syxJ */, _DO/* syxK */);});
},
_DP/* $w$c* */ = function(_DQ/* sfMn */, _DR/* sfMo */, _DS/* sfMp */, _DT/* sfMq */, _DU/* sfMr */, _DV/* sfMs */, _DW/* sfMt */, _DX/* sfMu */, _DY/* sfMv */){
  var _DZ/* sfMw */ = B(_7k/* GHC.Num.* */(_DQ/* sfMn */));
  return new T2(0,new T3(0,E(B(A1(B(A1(_DZ/* sfMw */,_DR/* sfMo */)),_DV/* sfMs */))),E(B(A1(B(A1(_DZ/* sfMw */,_DS/* sfMp */)),_DW/* sfMt */))),E(B(A1(B(A1(_DZ/* sfMw */,_DT/* sfMq */)),_DX/* sfMu */)))),B(A1(B(A1(_DZ/* sfMw */,_DU/* sfMr */)),_DY/* sfMv */)));
},
_E0/* $w$c+ */ = function(_E1/* sfN0 */, _E2/* sfN1 */, _E3/* sfN2 */, _E4/* sfN3 */, _E5/* sfN4 */, _E6/* sfN5 */, _E7/* sfN6 */, _E8/* sfN7 */, _E9/* sfN8 */){
  var _Ea/* sfN9 */ = B(_6I/* GHC.Num.+ */(_E1/* sfN0 */));
  return new T2(0,new T3(0,E(B(A1(B(A1(_Ea/* sfN9 */,_E2/* sfN1 */)),_E6/* sfN5 */))),E(B(A1(B(A1(_Ea/* sfN9 */,_E3/* sfN2 */)),_E7/* sfN6 */))),E(B(A1(B(A1(_Ea/* sfN9 */,_E4/* sfN3 */)),_E8/* sfN7 */)))),B(A1(B(A1(_Ea/* sfN9 */,_E5/* sfN4 */)),_E9/* sfN8 */)));
},
_Eb/* dt */ = 5.0e-2,
_Ec/* $wa */ = function(_Ed/* sywB */, _Ee/* sywC */, _Ef/* sywD */, _Eg/* sywE */, _Eh/* sywF */, _Ei/* sywG */, _Ej/* sywH */, _Ek/* sywI */, _El/* sywJ */, _Em/* sywK */, _En/* sywL */, _Eo/* sywM */, _Ep/* sywN */, _Eq/* sywO */, _Er/* sywP */, _Es/* sywQ */, _Et/* sywR */){
  var _Eu/* sywS */ = B(_DP/* Lib.Object.$w$c* */(_il/* GHC.Float.$fNumDouble */, _Ek/* sywI */, _El/* sywJ */, _Em/* sywK */, _En/* sywL */, _Eb/* Lib.Physics.dt */, _Eb/* Lib.Physics.dt */, _Eb/* Lib.Physics.dt */, _Eb/* Lib.Physics.dt */)),
  _Ev/* sywV */ = E(_Eu/* sywS */.a),
  _Ew/* sywZ */ = B(_E0/* Lib.Object.$w$c+ */(_il/* GHC.Float.$fNumDouble */, _Eg/* sywE */, _Eh/* sywF */, _Ei/* sywG */, _Ej/* sywH */, _Ev/* sywV */.a, _Ev/* sywV */.b, _Ev/* sywV */.c, _Eu/* sywS */.b)),
  _Ex/* syx2 */ = E(_Ew/* sywZ */.a);
  return new F(function(){return _nO/* Lib.Object.$wfitO */(_Ed/* sywB */, _Ee/* sywC */, _Ef/* sywD */, _Ex/* syx2 */.a, _Ex/* syx2 */.b, _Ex/* syx2 */.c, _Ew/* sywZ */.b, _Ek/* sywI */, _El/* sywJ */, _Em/* sywK */, _En/* sywL */, _Eo/* sywM */, _Ep/* sywN */, _Eq/* sywO */, _Er/* sywP */, _Es/* sywQ */, _Et/* sywR */);});
},
_Ey/* go */ = function(_Ez/* syqj */){
  while(1){
    var _EA/* syqk */ = E(_Ez/* syqj */);
    if(!_EA/* syqk */._){
      return true;
    }else{
      if(E(_EA/* syqk */.a)<0){
        return false;
      }else{
        _Ez/* syqj */ = _EA/* syqk */.b;
        continue;
      }
    }
  }
},
_EB/* $sgo */ = function(_EC/* syqd */, _ED/* syqe */){
  if(E(_EC/* syqd */)<0){
    return false;
  }else{
    return new F(function(){return _Ey/* Lib.Physics.go */(_ED/* syqe */);});
  }
},
_EE/* $w$cdot */ = function(_EF/* sn6T */, _EG/* sn6U */, _EH/* sn6V */, _EI/* sn6W */, _EJ/* sn6X */){
  var _EK/* sn6Z */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_EF/* sn6T */))));
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_EK/* sn6Z */, new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_EK/* sn6Z */, _EG/* sn6U */, _EI/* sn6W */));
  }), new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_EK/* sn6Z */, _EH/* sn6V */, _EJ/* sn6X */));
  }));});
},
_EL/* $wtoLocal */ = function(_EM/* sn4x */, _EN/* sn4y */){
  var _EO/* sn4z */ = new T(function(){
    return E(E(_EN/* sn4y */).c);
  }),
  _EP/* sn4F */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_EM/* sn4x */)))),
  _EQ/* sn4G */ = new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_EP/* sn4F */, new T(function(){
      return E(E(E(_EN/* sn4y */).b).b);
    }), new T(function(){
      return E(E(E(_EN/* sn4y */).b).a);
    })));
  });
  return new T2(0,B(A3(_7k/* GHC.Num.* */,_EP/* sn4F */, _EQ/* sn4G */, new T(function(){
    return B(A2(_bA/* GHC.Float.cos */,_EM/* sn4x */, _EO/* sn4z */));
  }))),B(A3(_7k/* GHC.Num.* */,_EP/* sn4F */, _EQ/* sn4G */, new T(function(){
    return B(A2(_bC/* GHC.Float.sin */,_EM/* sn4x */, _EO/* sn4z */));
  }))));
},
_ER/* catMaybes1 */ = function(_ES/*  s9C1 */){
  while(1){
    var _ET/*  catMaybes1 */ = B((function(_EU/* s9C1 */){
      var _EV/* s9C2 */ = E(_EU/* s9C1 */);
      if(!_EV/* s9C2 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _EW/* s9C4 */ = _EV/* s9C2 */.b,
        _EX/* s9C5 */ = E(_EV/* s9C2 */.a);
        if(!_EX/* s9C5 */._){
          _ES/*  s9C1 */ = _EW/* s9C4 */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_EX/* s9C5 */.a,new T(function(){
            return B(_ER/* Data.Maybe.catMaybes1 */(_EW/* s9C4 */));
          }));
        }
      }
    })(_ES/*  s9C1 */));
    if(_ET/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _ET/*  catMaybes1 */;
    }
  }
},
_EY/* $wintersect */ = function(_EZ/* syqr */, _F0/* syqs */, _F1/* syqt */, _F2/* syqu */, _F3/* syqv */, _F4/* syqw */, _F5/* syqx */, _F6/* syqy */, _F7/* syqz */, _F8/* syqA */){
  var _F9/* syqB */ = function(_Fa/* syqC */, _Fb/* syqD */){
    var _Fc/* syqE */ = E(_Fa/* syqC */);
    if(!_Fc/* syqE */._){
      return E(_Fb/* syqD */);
    }else{
      var _Fd/* syqF */ = _Fc/* syqE */.a,
      _Fe/* syvH */ = new T(function(){
        var _Ff/* syqH */ = function(_Fg/*  syqI */){
          while(1){
            var _Fh/*  syqH */ = B((function(_Fi/* syqI */){
              var _Fj/* syqJ */ = E(_Fi/* syqI */);
              if(!_Fj/* syqJ */._){
                return __Z/* EXTERNAL */;
              }else{
                var _Fk/* syqL */ = _Fj/* syqJ */.b,
                _Fl/* syqQ */ = E(E(_Fd/* syqF */).a),
                _Fm/* syqU */ = E(_Fl/* syqQ */.a),
                _Fn/* syqW */ = E(_Fl/* syqQ */.b),
                _Fo/* syqY */ = E(_Fl/* syqQ */.c),
                _Fp/* syr0 */ = E(_Fj/* syqJ */.a),
                _Fq/* syr4 */ = E(_Fp/* syr0 */.a),
                _Fr/* syr8 */ = E(_Fq/* syr4 */.a),
                _Fs/* syrc */ = E(_Fr/* syr8 */.a),
                _Ft/* syre */ = E(_Fr/* syr8 */.b),
                _Fu/* syrg */ = E(_Fr/* syr8 */.c),
                _Fv/* syri */ = E(_Fp/* syr0 */.c),
                _Fw/* syrm */ = E(_Fv/* syri */.a),
                _Fx/* syrq */ = E(_Fw/* syrm */.a),
                _Fy/* syrs */ = E(_Fw/* syrm */.b),
                _Fz/* syru */ = E(_Fw/* syrm */.c),
                _FA/* syrw */ = E(_Fp/* syr0 */.b),
                _FB/* syrA */ = E(_FA/* syrw */.a),
                _FC/* syrE */ = E(_FB/* syrA */.a),
                _FD/* syrG */ = E(_FB/* syrA */.b),
                _FE/* syrI */ = E(_FB/* syrA */.c),
                _FF/* syrK */ = E(_Fq/* syr4 */.b),
                _FG/* syrR */ = E(_Fq/* syr4 */.c),
                _FH/* syrT */ = E(_FA/* syrw */.b),
                _FI/* sys0 */ = E(_FA/* syrw */.c),
                _FJ/* sys2 */ = E(_Fv/* syri */.b),
                _FK/* sys9 */ = E(_Fv/* syri */.c),
                _FL/* sysb */ = _Fx/* syrq */+ -_Fs/* syrc */,
                _FM/* sysd */ = _Fy/* syrs */+ -_Ft/* syre */,
                _FN/* sysf */ = _Fz/* syru */+ -_Fu/* syrg */,
                _FO/* sysh */ = _Fx/* syrq */+ -_FC/* syrE */,
                _FP/* sysj */ = _Fy/* syrs */+ -_FD/* syrG */,
                _FQ/* sysl */ = _Fz/* syru */+ -_FE/* syrI */,
                _FR/* sysz */ = B(_jC/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _FM/* sysd */*_FQ/* sysl */-_FP/* sysj */*_FN/* sysf */, _FN/* sysf */*_FO/* sysh */-_FQ/* sysl */*_FL/* sysb */, _FL/* sysb */*_FP/* sysj */-_FO/* sysh */*_FM/* sysd */)),
                _FS/* sysA */ = _FR/* sysz */.a,
                _FT/* sysB */ = _FR/* sysz */.b,
                _FU/* sysC */ = _FR/* sysz */.c,
                _FV/* sysM */ = B(_js/* Lib.World.$w$cdot */(_iR/* GHC.Float.$fFloatingDouble */, _Fm/* syqU */+ -_Fs/* syrc */, _Fn/* syqW */+ -_Ft/* syre */, _Fo/* syqY */+ -_Fu/* syrg */, _FS/* sysA */, _FT/* sysB */, _FU/* sysC */)),
                _FW/* sysO */ = function(_FX/* sysP */){
                  if(_FX/* sysP */>=0.1){
                    return __Z/* EXTERNAL */;
                  }else{
                    var _FY/* sysS */ = new T(function(){
                      return new T3(0,_Fm/* syqU */+ -(E(_FS/* sysA */)*_FV/* sysM */),_Fn/* syqW */+ -(E(_FT/* sysB */)*_FV/* sysM */),_Fo/* syqY */+ -(E(_FU/* sysC */)*_FV/* sysM */));
                    }),
                    _FZ/* sytb */ = function(_G0/* sytc */, _G1/* sytd */, _G2/* syte */, _G3/* sytf */, _G4/* sytg */, _G5/* syth */, _G6/* syti */, _G7/* sytj */, _G8/* sytk */){
                      var _G9/* sytl */ = E(_FY/* sysS */),
                      _Ga/* sytv */ = E(_FT/* sysB */),
                      _Gb/* sytx */ = E(_FU/* sysC */),
                      _Gc/* sytz */ = E(_FS/* sysA */),
                      _Gd/* sytB */ = _G6/* syti */+ -_G3/* sytf */,
                      _Ge/* sytD */ = _G7/* sytj */+ -_G4/* sytg */,
                      _Gf/* sytF */ = _G8/* sytk */+ -_G5/* syth */,
                      _Gg/* sytT */ = B(_jC/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _Ga/* sytv */*_Gf/* sytF */-_Ge/* sytD */*_Gb/* sytx */, _Gb/* sytx */*_Gd/* sytB */-_Gf/* sytF */*_Gc/* sytz */, _Gc/* sytz */*_Ge/* sytD */-_Gd/* sytB */*_Ga/* sytv */)),
                      _Gh/* sytU */ = _Gg/* sytT */.a,
                      _Gi/* sytV */ = _Gg/* sytT */.b,
                      _Gj/* sytW */ = _Gg/* sytT */.c;
                      return B(_js/* Lib.World.$w$cdot */(_iR/* GHC.Float.$fFloatingDouble */, E(_G9/* sytl */.a)+ -_G3/* sytf */, E(_G9/* sytl */.b)+ -_G4/* sytg */, E(_G9/* sytl */.c)+ -_G5/* syth */, _Gh/* sytU */, _Gi/* sytV */, _Gj/* sytW */))/B(_js/* Lib.World.$w$cdot */(_iR/* GHC.Float.$fFloatingDouble */, _G0/* sytc */+ -_G3/* sytf */, _G1/* sytd */+ -_G4/* sytg */, _G2/* syte */+ -_G5/* syth */, _Gh/* sytU */, _Gi/* sytV */, _Gj/* sytW */));
                    },
                    _Gk/* syuj */ = new T(function(){
                      return B(_FZ/* sytb */(_Fs/* syrc */, _Ft/* syre */, _Fu/* syrg */, _FC/* syrE */, _FD/* syrG */, _FE/* syrI */, _Fx/* syrq */, _Fy/* syrs */, _Fz/* syru */));
                    }),
                    _Gl/* syul */ = new T(function(){
                      return B(_FZ/* sytb */(_FC/* syrE */, _FD/* syrG */, _FE/* syrI */, _Fx/* syrq */, _Fy/* syrs */, _Fz/* syru */, _Fs/* syrc */, _Ft/* syre */, _Fu/* syrg */));
                    }),
                    _Gm/* syun */ = new T(function(){
                      return B(_FZ/* sytb */(_Fx/* syrq */, _Fy/* syrs */, _Fz/* syru */, _Fs/* syrc */, _Ft/* syre */, _Fu/* syrg */, _FC/* syrE */, _FD/* syrG */, _FE/* syrI */));
                    });
                    return (!B(_EB/* Lib.Physics.$sgo */(_Gk/* syuj */, new T2(1,_Gl/* syul */,new T2(1,_Gm/* syun */,_o/* GHC.Types.[] */))))) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
                      var _Gn/* syus */ = E(_Gk/* syuj */),
                      _Go/* syuu */ = E(_Gl/* syul */),
                      _Gp/* syuw */ = E(_Gm/* syun */),
                      _Gq/* syuy */ = E(_FJ/* sys2 */.b)*E(_FJ/* sys2 */.a),
                      _Gr/* syuz */ = E(_FH/* syrT */.b)*E(_FH/* syrT */.a),
                      _Gs/* syuA */ = E(_FF/* syrK */.b)*E(_FF/* syrK */.a);
                      return new T2(0,_Gs/* syuA */*Math.cos/* EXTERNAL */(_FG/* syrR */)*_Gn/* syus */+_Gr/* syuz */*Math.cos/* EXTERNAL */(_FI/* sys0 */)*_Go/* syuu */+_Gq/* syuy */*Math.cos/* EXTERNAL */(_FK/* sys9 */)*_Gp/* syuw */,_Gs/* syuA */*Math.sin/* EXTERNAL */(_FG/* syrR */)*_Gn/* syus */+_Gr/* syuz */*Math.sin/* EXTERNAL */(_FI/* sys0 */)*_Go/* syuu */+_Gq/* syuy */*Math.sin/* EXTERNAL */(_FK/* sys9 */)*_Gp/* syuw */);
                    }));
                  }
                },
                _Gt/* syv0 */ = E(_FV/* sysM */);
                if(!_Gt/* syv0 */){
                  var _Gu/* syv8 */ = B(_FW/* sysO */(0));
                  if(!_Gu/* syv8 */._){
                    _Fg/*  syqI */ = _Fk/* syqL */;
                    return __continue/* EXTERNAL */;
                  }else{
                    return E(_Gu/* syv8 */);
                  }
                }else{
                  if(_Gt/* syv0 */<=0){
                    var _Gv/* syv4 */ = B(_FW/* sysO */( -_Gt/* syv0 */));
                    if(!_Gv/* syv4 */._){
                      _Fg/*  syqI */ = _Fk/* syqL */;
                      return __continue/* EXTERNAL */;
                    }else{
                      return E(_Gv/* syv4 */);
                    }
                  }else{
                    var _Gw/* syv6 */ = B(_FW/* sysO */(_Gt/* syv0 */));
                    if(!_Gw/* syv6 */._){
                      _Fg/*  syqI */ = _Fk/* syqL */;
                      return __continue/* EXTERNAL */;
                    }else{
                      return E(_Gw/* syv6 */);
                    }
                  }
                }
              }
            })(_Fg/*  syqI */));
            if(_Fh/*  syqH */!=__continue/* EXTERNAL */){
              return _Fh/*  syqH */;
            }
          }
        },
        _Gx/* syva */ = B(_Ff/* syqH */(_F8/* syqA */));
        if(!_Gx/* syva */._){
          return __Z/* EXTERNAL */;
        }else{
          var _Gy/* syvc */ = E(_Gx/* syva */.a),
          _Gz/* syvj */ = B(_EL/* Lib.Constraint.$wtoLocal */(_iR/* GHC.Float.$fFloatingDouble */, _Fd/* syqF */)),
          _GA/* syvq */ = E(_Gy/* syvc */.a)+ -E(_Gz/* syvj */.a),
          _GB/* syvt */ = E(_Gy/* syvc */.b)+ -E(_Gz/* syvj */.b);
          if(Math.sqrt/* EXTERNAL */(B(_EE/* Lib.Constraint.$w$cdot */(_iR/* GHC.Float.$fFloatingDouble */, _GA/* syvq */, _GB/* syvt */, _GA/* syvq */, _GB/* syvt */)))<1.0e-4){
            return __Z/* EXTERNAL */;
          }else{
            return new T1(1,new T2(0,new T(function(){
              return E(E(_Fd/* syqF */).a);
            }),_Gy/* syvc */));
          }
        }
      });
      return new T2(1,_Fe/* syvH */,new T(function(){
        return B(_F9/* syqB */(_Fc/* syqE */.b, _Fb/* syqD */));
      }));
    }
  };
  return new F(function(){return _ER/* Data.Maybe.catMaybes1 */(B(_F9/* syqB */(_F7/* syqz */, _o/* GHC.Types.[] */)));});
},
_GC/* a17 */ = function(_GD/* syvK */){
  var _GE/* syvL */ = E(_GD/* syvK */),
  _GF/* syvV */ = E(_GE/* syvL */.b),
  _GG/* syvZ */ = E(_GE/* syvL */.e),
  _GH/* syw2 */ = E(_GG/* syvZ */.a),
  _GI/* sywc */ = E(_GE/* syvL */.g),
  _GJ/* sywg */ = B(_ks/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _GF/* syvV */.a, _GF/* syvV */.b, _GF/* syvV */.c, _GI/* sywc */.a, _GI/* sywc */.b, _GI/* sywc */.c));
  return {_:0,a:E(_GE/* syvL */.a),b:E(_GF/* syvV */),c:E(_GE/* syvL */.c),d:E(_GE/* syvL */.d),e:E(new T2(0,E(new T3(0,E(_GH/* syw2 */.a)+E(_GJ/* sywg */.a)*5.0e-2,E(_GH/* syw2 */.b)+E(_GJ/* sywg */.b)*5.0e-2,E(_GH/* syw2 */.c)+E(_GJ/* sywg */.c)*5.0e-2)),E(_GG/* syvZ */.b))),f:E(_GE/* syvL */.f),g:E(_GI/* sywc */),h:E(_GE/* syvL */.h),i:E(_GE/* syvL */.i)};
},
_GK/* a18 */ = function(_GL/* syx6 */){
  var _GM/* syx7 */ = E(_GL/* syx6 */),
  _GN/* syxh */ = E(_GM/* syx7 */.d),
  _GO/* syxk */ = E(_GN/* syxh */.a),
  _GP/* syxo */ = E(_GM/* syx7 */.e),
  _GQ/* syxr */ = E(_GP/* syxo */.a),
  _GR/* syxv */ = E(_GM/* syx7 */.f),
  _GS/* syxz */ = B(_Ec/* Lib.Physics.$wa */(_GM/* syx7 */.a, _GM/* syx7 */.b, _GM/* syx7 */.c, _GO/* syxk */.a, _GO/* syxk */.b, _GO/* syxk */.c, _GN/* syxh */.b, _GQ/* syxr */.a, _GQ/* syxr */.b, _GQ/* syxr */.c, _GP/* syxo */.b, _GR/* syxv */.a, _GR/* syxv */.b, _GR/* syxv */.c, _GM/* syx7 */.g, _GM/* syx7 */.h, _GM/* syx7 */.i));
  return {_:0,a:E(_GS/* syxz */.a),b:E(_GS/* syxz */.b),c:E(_GS/* syxz */.c),d:E(_GS/* syxz */.d),e:E(_GS/* syxz */.e),f:E(_GS/* syxz */.f),g:E(_GS/* syxz */.g),h:E(_GS/* syxz */.h),i:E(_GS/* syxz */.i)};
},
_GT/* go1 */ = function(_GU/* syxL */){
  var _GV/* syxM */ = E(_GU/* syxL */);
  if(!_GV/* syxM */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_GV/* syxM */.a, new T(function(){
      return B(_GT/* Lib.Physics.go1 */(_GV/* syxM */.b));
    },1));});
  }
},
_GW/* lvl29 */ = new T2(1,_70/* GHC.Show.shows7 */,_o/* GHC.Types.[] */),
_GX/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_GY/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_GZ/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_H0/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_GX/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_GY/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_GZ/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_H1/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_H0/* GHC.IO.Exception.$fExceptionIOException_wild */,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_H2/* $fExceptionIOException3 */ = function(_H3/* s3MW8 */){
  return E(_H1/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_H4/* $fExceptionIOException_$cfromException */ = function(_H5/* s3N1e */){
  var _H6/* s3N1f */ = E(_H5/* s3N1e */);
  return new F(function(){return _28/* Data.Typeable.cast */(B(_26/* GHC.Exception.$p1Exception */(_H6/* s3N1f */.a)), _H2/* GHC.IO.Exception.$fExceptionIOException3 */, _H6/* s3N1f */.b);});
},
_H7/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_H8/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_H9/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_Ha/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_Hb/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_Hc/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_Hd/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_He/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_Hf/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_Hg/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_Hh/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_Hi/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_Hj/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_Hk/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_Hl/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_Hm/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_Hn/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_Ho/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_Hp/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_Hq/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_Hr/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_Hs/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_Ht/* $w$cshowsPrec3 */ = function(_Hu/* s3N03 */, _Hv/* s3N04 */){
  switch(E(_Hu/* s3N03 */)){
    case 0:
      return new F(function(){return _f/* GHC.Base.++ */(_Hk/* GHC.IO.Exception.lvl18 */, _Hv/* s3N04 */);});
      break;
    case 1:
      return new F(function(){return _f/* GHC.Base.++ */(_Hj/* GHC.IO.Exception.lvl17 */, _Hv/* s3N04 */);});
      break;
    case 2:
      return new F(function(){return _f/* GHC.Base.++ */(_Hi/* GHC.IO.Exception.lvl16 */, _Hv/* s3N04 */);});
      break;
    case 3:
      return new F(function(){return _f/* GHC.Base.++ */(_Hh/* GHC.IO.Exception.lvl15 */, _Hv/* s3N04 */);});
      break;
    case 4:
      return new F(function(){return _f/* GHC.Base.++ */(_Hg/* GHC.IO.Exception.lvl14 */, _Hv/* s3N04 */);});
      break;
    case 5:
      return new F(function(){return _f/* GHC.Base.++ */(_Hf/* GHC.IO.Exception.lvl13 */, _Hv/* s3N04 */);});
      break;
    case 6:
      return new F(function(){return _f/* GHC.Base.++ */(_He/* GHC.IO.Exception.lvl12 */, _Hv/* s3N04 */);});
      break;
    case 7:
      return new F(function(){return _f/* GHC.Base.++ */(_Hd/* GHC.IO.Exception.lvl11 */, _Hv/* s3N04 */);});
      break;
    case 8:
      return new F(function(){return _f/* GHC.Base.++ */(_Hc/* GHC.IO.Exception.lvl10 */, _Hv/* s3N04 */);});
      break;
    case 9:
      return new F(function(){return _f/* GHC.Base.++ */(_Hs/* GHC.IO.Exception.lvl9 */, _Hv/* s3N04 */);});
      break;
    case 10:
      return new F(function(){return _f/* GHC.Base.++ */(_Hr/* GHC.IO.Exception.lvl8 */, _Hv/* s3N04 */);});
      break;
    case 11:
      return new F(function(){return _f/* GHC.Base.++ */(_Hq/* GHC.IO.Exception.lvl7 */, _Hv/* s3N04 */);});
      break;
    case 12:
      return new F(function(){return _f/* GHC.Base.++ */(_Hp/* GHC.IO.Exception.lvl6 */, _Hv/* s3N04 */);});
      break;
    case 13:
      return new F(function(){return _f/* GHC.Base.++ */(_Ho/* GHC.IO.Exception.lvl5 */, _Hv/* s3N04 */);});
      break;
    case 14:
      return new F(function(){return _f/* GHC.Base.++ */(_Hn/* GHC.IO.Exception.lvl4 */, _Hv/* s3N04 */);});
      break;
    case 15:
      return new F(function(){return _f/* GHC.Base.++ */(_Hm/* GHC.IO.Exception.lvl3 */, _Hv/* s3N04 */);});
      break;
    case 16:
      return new F(function(){return _f/* GHC.Base.++ */(_Hl/* GHC.IO.Exception.lvl2 */, _Hv/* s3N04 */);});
      break;
    case 17:
      return new F(function(){return _f/* GHC.Base.++ */(_Hb/* GHC.IO.Exception.lvl1 */, _Hv/* s3N04 */);});
      break;
    default:
      return new F(function(){return _f/* GHC.Base.++ */(_Ha/* GHC.IO.Exception.lvl */, _Hv/* s3N04 */);});
  }
},
_Hw/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_Hx/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_Hy/* $w$cshowsPrec2 */ = function(_Hz/* s3N0c */, _HA/* s3N0d */, _HB/* s3N0e */, _HC/* s3N0f */, _HD/* s3N0g */, _HE/* s3N0h */){
  var _HF/* s3N0i */ = new T(function(){
    var _HG/* s3N0j */ = new T(function(){
      var _HH/* s3N0p */ = new T(function(){
        var _HI/* s3N0k */ = E(_HC/* s3N0f */);
        if(!_HI/* s3N0k */._){
          return E(_HE/* s3N0h */);
        }else{
          var _HJ/* s3N0o */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_HI/* s3N0k */, new T(function(){
              return B(_f/* GHC.Base.++ */(_H8/* GHC.IO.Exception.$fExceptionIOException1 */, _HE/* s3N0h */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_H9/* GHC.IO.Exception.$fExceptionIOException2 */, _HJ/* s3N0o */));
        }
      },1);
      return B(_Ht/* GHC.IO.Exception.$w$cshowsPrec3 */(_HA/* s3N0d */, _HH/* s3N0p */));
    }),
    _HK/* s3N0q */ = E(_HB/* s3N0e */);
    if(!_HK/* s3N0q */._){
      return E(_HG/* s3N0j */);
    }else{
      return B(_f/* GHC.Base.++ */(_HK/* s3N0q */, new T(function(){
        return B(_f/* GHC.Base.++ */(_H7/* GHC.IO.Exception.$fExceptionArrayException2 */, _HG/* s3N0j */));
      },1)));
    }
  }),
  _HL/* s3N0u */ = E(_HD/* s3N0g */);
  if(!_HL/* s3N0u */._){
    var _HM/* s3N0v */ = E(_Hz/* s3N0c */);
    if(!_HM/* s3N0v */._){
      return E(_HF/* s3N0i */);
    }else{
      var _HN/* s3N0x */ = E(_HM/* s3N0v */.a);
      if(!_HN/* s3N0x */._){
        var _HO/* s3N0C */ = new T(function(){
          var _HP/* s3N0B */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_Hw/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_f/* GHC.Base.++ */(_H7/* GHC.IO.Exception.$fExceptionArrayException2 */, _HF/* s3N0i */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_HN/* s3N0x */.a, _HP/* s3N0B */));
        },1);
        return new F(function(){return _f/* GHC.Base.++ */(_Hx/* GHC.IO.Handle.Types.showHandle2 */, _HO/* s3N0C */);});
      }else{
        var _HQ/* s3N0I */ = new T(function(){
          var _HR/* s3N0H */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_Hw/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_f/* GHC.Base.++ */(_H7/* GHC.IO.Exception.$fExceptionArrayException2 */, _HF/* s3N0i */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_HN/* s3N0x */.a, _HR/* s3N0H */));
        },1);
        return new F(function(){return _f/* GHC.Base.++ */(_Hx/* GHC.IO.Handle.Types.showHandle2 */, _HQ/* s3N0I */);});
      }
    }
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_HL/* s3N0u */.a, new T(function(){
      return B(_f/* GHC.Base.++ */(_H7/* GHC.IO.Exception.$fExceptionArrayException2 */, _HF/* s3N0i */));
    },1));});
  }
},
_HS/* $fExceptionIOException_$cshow */ = function(_HT/* s3N16 */){
  var _HU/* s3N17 */ = E(_HT/* s3N16 */);
  return new F(function(){return _Hy/* GHC.IO.Exception.$w$cshowsPrec2 */(_HU/* s3N17 */.a, _HU/* s3N17 */.b, _HU/* s3N17 */.c, _HU/* s3N17 */.d, _HU/* s3N17 */.f, _o/* GHC.Types.[] */);});
},
_HV/* $fExceptionIOException_$cshowsPrec */ = function(_HW/* s3N0L */, _HX/* s3N0M */, _HY/* s3N0N */){
  var _HZ/* s3N0O */ = E(_HX/* s3N0M */);
  return new F(function(){return _Hy/* GHC.IO.Exception.$w$cshowsPrec2 */(_HZ/* s3N0O */.a, _HZ/* s3N0O */.b, _HZ/* s3N0O */.c, _HZ/* s3N0O */.d, _HZ/* s3N0O */.f, _HY/* s3N0N */);});
},
_I0/* $s$dmshow9 */ = function(_I1/* s3N0V */, _I2/* s3N0W */){
  var _I3/* s3N0X */ = E(_I1/* s3N0V */);
  return new F(function(){return _Hy/* GHC.IO.Exception.$w$cshowsPrec2 */(_I3/* s3N0X */.a, _I3/* s3N0X */.b, _I3/* s3N0X */.c, _I3/* s3N0X */.d, _I3/* s3N0X */.f, _I2/* s3N0W */);});
},
_I4/* $fShowIOException_$cshowList */ = function(_I5/* s3N14 */, _I6/* s3N15 */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_I0/* GHC.IO.Exception.$s$dmshow9 */, _I5/* s3N14 */, _I6/* s3N15 */);});
},
_I7/* $fShowIOException */ = new T3(0,_HV/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_HS/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_I4/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_I8/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_H2/* GHC.IO.Exception.$fExceptionIOException3 */,_I7/* GHC.IO.Exception.$fShowIOException */,_I9/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_H4/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_HS/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_I9/* $fExceptionIOException_$ctoException */ = function(_Ia/* B1 */){
  return new T2(0,_I8/* GHC.IO.Exception.$fExceptionIOException */,_Ia/* B1 */);
},
_Ib/* Nothing */ = __Z/* EXTERNAL */,
_Ic/* UserError */ = 7,
_Id/* str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at Lib\\Physics.hs:85:7-13"));
}),
_Ie/* lvl32 */ = new T6(0,_Ib/* GHC.Base.Nothing */,_Ic/* GHC.IO.Exception.UserError */,_o/* GHC.Types.[] */,_Id/* Lib.Physics.str */,_Ib/* GHC.Base.Nothing */,_Ib/* GHC.Base.Nothing */),
_If/* lvl33 */ = new T(function(){
  return B(_I9/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_Ie/* Lib.Physics.lvl32 */));
}),
_Ig/* str1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at Lib\\Physics.hs:86:7-13"));
}),
_Ih/* lvl34 */ = new T6(0,_Ib/* GHC.Base.Nothing */,_Ic/* GHC.IO.Exception.UserError */,_o/* GHC.Types.[] */,_Ig/* Lib.Physics.str1 */,_Ib/* GHC.Base.Nothing */,_Ib/* GHC.Base.Nothing */),
_Ii/* lvl35 */ = new T(function(){
  return B(_I9/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_Ih/* Lib.Physics.lvl34 */));
}),
_Ij/* lvl36 */ = new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_Ik/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_Il/* lvl38 */ = function(_Im/* syxQ */, _In/* syxR */){
  var _Io/* syxW */ = new T(function(){
    var _Ip/* syxV */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */(" not in range [0..", new T(function(){
        return B(_f/* GHC.Base.++ */(B(_zw/* GHC.Show.$wshowSignedInt */(0, _In/* syxR */, _o/* GHC.Types.[] */)), _Ik/* Lib.Physics.lvl37 */));
      })));
    },1);
    return B(_f/* GHC.Base.++ */(B(_zw/* GHC.Show.$wshowSignedInt */(0, _Im/* syxQ */, _o/* GHC.Types.[] */)), _Ip/* syxV */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Error in array index; ", _Io/* syxW */)));});
},
_Iq/* nextFrame1 */ = function(_Ir/* syxY */, _/* EXTERNAL */){
  var _Is/* syy0 */ = B(_Bn/* Data.Traversable.$w$ctraverse */(_AW/* GHC.Arr.$fIxInt */, _CJ/* Data.Functor.Identity.$fApplicativeIdentity */, _GC/* Lib.Physics.a17 */, _Ir/* syxY */)),
  _It/* syy3 */ = _Is/* syy0 */.c,
  _Iu/* syy4 */ = _Is/* syy0 */.d,
  _Iv/* syy5 */ = E(_Is/* syy0 */.a),
  _Iw/* syy7 */ = E(_Is/* syy0 */.b);
  if(_Iv/* syy5 */<=_Iw/* syy7 */){
    var _Ix/* syyc */ = function(_Iy/* syB5 */, _Iz/* syB6 */, _/* EXTERNAL */){
      if(_Iy/* syB5 */<=_Iw/* syy7 */){
        var _IA/* syBa */ = E(_Iz/* syB6 */),
        _IB/* syBj */ = function(_IC/* syBk */, _ID/* syBl */, _IE/* syBm */, _IF/* syBn */, _IG/* syBo */, _/* EXTERNAL */){
          if(_ID/* syBl */>_Iy/* syB5 */){
            return new F(function(){return die/* EXTERNAL */(_If/* Lib.Physics.lvl33 */);});
          }else{
            if(_Iy/* syB5 */>_IE/* syBm */){
              return new F(function(){return die/* EXTERNAL */(_If/* Lib.Physics.lvl33 */);});
            }else{
              if(_ID/* syBl */>_IC/* syBk */){
                return new F(function(){return die/* EXTERNAL */(_Ii/* Lib.Physics.lvl35 */);});
              }else{
                if(_IC/* syBk */>_IE/* syBm */){
                  return new F(function(){return die/* EXTERNAL */(_Ii/* Lib.Physics.lvl35 */);});
                }else{
                  var _IH/* syCK */ = new T(function(){
                    var _II/* syBC */ = new T(function(){
                      var _IJ/* syBD */ = _Iy/* syB5 */-_ID/* syBl */|0;
                      if(0>_IJ/* syBD */){
                        return B(_Il/* Lib.Physics.lvl38 */(_IJ/* syBD */, _IF/* syBn */));
                      }else{
                        if(_IJ/* syBD */>=_IF/* syBn */){
                          return B(_Il/* Lib.Physics.lvl38 */(_IJ/* syBD */, _IF/* syBn */));
                        }else{
                          return E(_IG/* syBo */[_IJ/* syBD */]);
                        }
                      }
                    }),
                    _IK/* syBM */ = new T(function(){
                      var _IL/* syBN */ = _IC/* syBk */-_ID/* syBl */|0;
                      if(0>_IL/* syBN */){
                        return B(_Il/* Lib.Physics.lvl38 */(_IL/* syBN */, _IF/* syBn */));
                      }else{
                        if(_IL/* syBN */>=_IF/* syBn */){
                          return B(_Il/* Lib.Physics.lvl38 */(_IL/* syBN */, _IF/* syBn */));
                        }else{
                          return E(_IG/* syBo */[_IL/* syBN */]);
                        }
                      }
                    }),
                    _IM/* syCk */ = new T(function(){
                      var _IN/* syCl */ = E(_IK/* syBM */);
                      return B(_EY/* Lib.Physics.$wintersect */(_IN/* syCl */.a, _IN/* syCl */.b, _IN/* syCl */.c, _IN/* syCl */.d, _IN/* syCl */.e, _IN/* syCl */.f, _IN/* syCl */.g, _IN/* syCl */.h, _IN/* syCl */.i, new T(function(){
                        return E(E(_II/* syBC */).h);
                      })));
                    }),
                    _IO/* syBW */ = new T(function(){
                      var _IP/* syBX */ = E(_II/* syBC */);
                      return B(_EY/* Lib.Physics.$wintersect */(_IP/* syBX */.a, _IP/* syBX */.b, _IP/* syBX */.c, _IP/* syBX */.d, _IP/* syBX */.e, _IP/* syBX */.f, _IP/* syBX */.g, _IP/* syBX */.h, _IP/* syBX */.i, new T(function(){
                        return E(E(_IK/* syBM */).h);
                      })));
                    });
                    return B(A3(_zV/* GHC.List.foldr1 */,_zP/* GHC.Show.$fShow(,)1 */, new T2(1,function(_IQ/* syCi */){
                      return new F(function(){return _DM/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_IO/* syBW */, _IQ/* syCi */);});
                    },new T2(1,function(_IR/* syCG */){
                      return new F(function(){return _DM/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_IM/* syCk */, _IR/* syCG */);});
                    },_o/* GHC.Types.[] */)), _GW/* Lib.Physics.lvl29 */));
                  }),
                  _IS/* syCM */ = B(_hf/* GHC.List.$wlenAcc */(new T2(1,_71/* GHC.Show.shows8 */,_IH/* syCK */), 0));
                  if(_IC/* syBk */!=_Iw/* syy7 */){
                    var _IT/* syCQ */ = B(_IB/* syBj */(_IC/* syBk */+1|0, _ID/* syBl */, _IE/* syBm */, _IF/* syBn */, _IG/* syBo */, _/* EXTERNAL */));
                    return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
                      return E(E(_IT/* syCQ */).a);
                    })),new T(function(){
                      return E(E(_IT/* syCQ */).b);
                    }));
                  }else{
                    return new T2(0,_Ij/* Lib.Physics.lvl36 */,new T4(0,E(_ID/* syBl */),E(_IE/* syBm */),_IF/* syBn */,_IG/* syBo */));
                  }
                }
              }
            }
          }
        },
        _IU/* syD7 */ = B(_IB/* syBj */(_Iy/* syB5 */, E(_IA/* syBa */.a), E(_IA/* syBa */.b), _IA/* syBa */.c, _IA/* syBa */.d, _/* EXTERNAL */));
        if(_Iy/* syB5 */!=_Iw/* syy7 */){
          var _IV/* syDh */ = B(_Ix/* syyc */(_Iy/* syB5 */+1|0, new T(function(){
            return E(E(_IU/* syD7 */).b);
          },1), _/* EXTERNAL */));
          return new T2(0,new T2(1,new T(function(){
            return B(_GT/* Lib.Physics.go1 */(E(_IU/* syD7 */).a));
          }),new T(function(){
            return E(E(_IV/* syDh */).a);
          })),new T(function(){
            return E(E(_IV/* syDh */).b);
          }));
        }else{
          return new T2(0,new T2(1,new T(function(){
            return B(_GT/* Lib.Physics.go1 */(E(_IU/* syD7 */).a));
          }),_o/* GHC.Types.[] */),new T(function(){
            return E(E(_IU/* syD7 */).b);
          }));
        }
      }else{
        if(_Iy/* syB5 */!=_Iw/* syy7 */){
          var _IW/* syDL */ = B(_Ix/* syyc */(_Iy/* syB5 */+1|0, _Iz/* syB6 */, _/* EXTERNAL */));
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
            return E(E(_IW/* syDL */).a);
          })),new T(function(){
            return E(E(_IW/* syDL */).b);
          }));
        }else{
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),_Iz/* syB6 */);
        }
      }
    },
    _IX/* syyb */ = function(_IY/* syyd */, _IZ/* syye */, _J0/* syyf */, _J1/* syyg */, _J2/* syyh */, _/* EXTERNAL */){
      if(_IY/* syyd */<=_Iw/* syy7 */){
        var _J3/* syyl */ = function(_J4/* syym */, _J5/* syyn */, _J6/* syyo */, _J7/* syyp */, _J8/* syyq */, _/* EXTERNAL */){
          if(_J5/* syyn */>_IY/* syyd */){
            return new F(function(){return die/* EXTERNAL */(_If/* Lib.Physics.lvl33 */);});
          }else{
            if(_IY/* syyd */>_J6/* syyo */){
              return new F(function(){return die/* EXTERNAL */(_If/* Lib.Physics.lvl33 */);});
            }else{
              if(_J5/* syyn */>_J4/* syym */){
                return new F(function(){return die/* EXTERNAL */(_Ii/* Lib.Physics.lvl35 */);});
              }else{
                if(_J4/* syym */>_J6/* syyo */){
                  return new F(function(){return die/* EXTERNAL */(_Ii/* Lib.Physics.lvl35 */);});
                }else{
                  var _J9/* syzM */ = new T(function(){
                    var _Ja/* syyE */ = new T(function(){
                      var _Jb/* syyF */ = _IY/* syyd */-_J5/* syyn */|0;
                      if(0>_Jb/* syyF */){
                        return B(_Il/* Lib.Physics.lvl38 */(_Jb/* syyF */, _J7/* syyp */));
                      }else{
                        if(_Jb/* syyF */>=_J7/* syyp */){
                          return B(_Il/* Lib.Physics.lvl38 */(_Jb/* syyF */, _J7/* syyp */));
                        }else{
                          return E(_J8/* syyq */[_Jb/* syyF */]);
                        }
                      }
                    }),
                    _Jc/* syyO */ = new T(function(){
                      var _Jd/* syyP */ = _J4/* syym */-_J5/* syyn */|0;
                      if(0>_Jd/* syyP */){
                        return B(_Il/* Lib.Physics.lvl38 */(_Jd/* syyP */, _J7/* syyp */));
                      }else{
                        if(_Jd/* syyP */>=_J7/* syyp */){
                          return B(_Il/* Lib.Physics.lvl38 */(_Jd/* syyP */, _J7/* syyp */));
                        }else{
                          return E(_J8/* syyq */[_Jd/* syyP */]);
                        }
                      }
                    }),
                    _Je/* syzm */ = new T(function(){
                      var _Jf/* syzn */ = E(_Jc/* syyO */);
                      return B(_EY/* Lib.Physics.$wintersect */(_Jf/* syzn */.a, _Jf/* syzn */.b, _Jf/* syzn */.c, _Jf/* syzn */.d, _Jf/* syzn */.e, _Jf/* syzn */.f, _Jf/* syzn */.g, _Jf/* syzn */.h, _Jf/* syzn */.i, new T(function(){
                        return E(E(_Ja/* syyE */).h);
                      })));
                    }),
                    _Jg/* syyY */ = new T(function(){
                      var _Jh/* syyZ */ = E(_Ja/* syyE */);
                      return B(_EY/* Lib.Physics.$wintersect */(_Jh/* syyZ */.a, _Jh/* syyZ */.b, _Jh/* syyZ */.c, _Jh/* syyZ */.d, _Jh/* syyZ */.e, _Jh/* syyZ */.f, _Jh/* syyZ */.g, _Jh/* syyZ */.h, _Jh/* syyZ */.i, new T(function(){
                        return E(E(_Jc/* syyO */).h);
                      })));
                    });
                    return B(A3(_zV/* GHC.List.foldr1 */,_zP/* GHC.Show.$fShow(,)1 */, new T2(1,function(_Ji/* syzk */){
                      return new F(function(){return _DM/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_Jg/* syyY */, _Ji/* syzk */);});
                    },new T2(1,function(_Jj/* syzI */){
                      return new F(function(){return _DM/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_Je/* syzm */, _Jj/* syzI */);});
                    },_o/* GHC.Types.[] */)), _GW/* Lib.Physics.lvl29 */));
                  }),
                  _Jk/* syzO */ = B(_hf/* GHC.List.$wlenAcc */(new T2(1,_71/* GHC.Show.shows8 */,_J9/* syzM */), 0));
                  if(_J4/* syym */!=_Iw/* syy7 */){
                    var _Jl/* syzS */ = B(_J3/* syyl */(_J4/* syym */+1|0, _J5/* syyn */, _J6/* syyo */, _J7/* syyp */, _J8/* syyq */, _/* EXTERNAL */));
                    return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
                      return E(E(_Jl/* syzS */).a);
                    })),new T(function(){
                      return E(E(_Jl/* syzS */).b);
                    }));
                  }else{
                    return new T2(0,_Ij/* Lib.Physics.lvl36 */,new T4(0,E(_J5/* syyn */),E(_J6/* syyo */),_J7/* syyp */,_J8/* syyq */));
                  }
                }
              }
            }
          }
        },
        _Jm/* syA9 */ = B(_J3/* syyl */(_IY/* syyd */, _IZ/* syye */, _J0/* syyf */, _J1/* syyg */, _J2/* syyh */, _/* EXTERNAL */));
        if(_IY/* syyd */!=_Iw/* syy7 */){
          var _Jn/* syAj */ = B(_Ix/* syyc */(_IY/* syyd */+1|0, new T(function(){
            return E(E(_Jm/* syA9 */).b);
          },1), _/* EXTERNAL */));
          return new T2(0,new T2(1,new T(function(){
            return B(_GT/* Lib.Physics.go1 */(E(_Jm/* syA9 */).a));
          }),new T(function(){
            return E(E(_Jn/* syAj */).a);
          })),new T(function(){
            return E(E(_Jn/* syAj */).b);
          }));
        }else{
          return new T2(0,new T2(1,new T(function(){
            return B(_GT/* Lib.Physics.go1 */(E(_Jm/* syA9 */).a));
          }),_o/* GHC.Types.[] */),new T(function(){
            return E(E(_Jm/* syA9 */).b);
          }));
        }
      }else{
        if(_IY/* syyd */!=_Iw/* syy7 */){
          var _Jo/* syAN */ = B(_IX/* syyb */(_IY/* syyd */+1|0, _IZ/* syye */, _J0/* syyf */, _J1/* syyg */, _J2/* syyh */, _/* EXTERNAL */));
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
            return E(E(_Jo/* syAN */).a);
          })),new T(function(){
            return E(E(_Jo/* syAN */).b);
          }));
        }else{
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),new T4(0,E(_IZ/* syye */),E(_J0/* syyf */),_J1/* syyg */,_J2/* syyh */));
        }
      }
    },
    _Jp/* syE0 */ = B(_IX/* syyb */(_Iv/* syy5 */, _Iv/* syy5 */, _Iw/* syy7 */, _It/* syy3 */, _Iu/* syy4 */, _/* EXTERNAL */)),
    _Jq/* syE7 */ = new T(function(){
      return B(_Bn/* Data.Traversable.$w$ctraverse */(_AW/* GHC.Arr.$fIxInt */, _CJ/* Data.Functor.Identity.$fApplicativeIdentity */, _GK/* Lib.Physics.a18 */, new T(function(){
        return E(E(_Jp/* syE0 */).b);
      })));
    });
    return new T2(0,_BD/* GHC.Tuple.() */,_Jq/* syE7 */);
  }else{
    var _Jr/* syFF */ = new T(function(){
      var _Js/* syFE */ = function(_/* EXTERNAL */){
        var _Jt/* syEa */ = function(_Ju/* syEb */){
          if(_Ju/* syEb */>=0){
            var _Jv/* syEe */ = newArr/* EXTERNAL */(_Ju/* syEb */, _hl/* GHC.Arr.arrEleBottom */),
            _Jw/* syEg */ = _Jv/* syEe */,
            _Jx/* syEh */ = E(_Ju/* syEb */);
            if(!_Jx/* syEh */){
              return new T4(0,E(_Iv/* syy5 */),E(_Iw/* syy7 */),0,_Jw/* syEg */);
            }else{
              var _Jy/* syEi */ = _It/* syy3 */-1|0,
              _Jz/* syEm */ = function(_JA/* syEn */, _JB/* syEo */, _/* EXTERNAL */){
                while(1){
                  var _JC/* syEq */ = E(_JA/* syEn */);
                  if(!_JC/* syEq */._){
                    return E(_/* EXTERNAL */);
                  }else{
                    var _/* EXTERNAL */ = _Jw/* syEg */[_JB/* syEo */] = _JC/* syEq */.a;
                    if(_JB/* syEo */!=(_Jx/* syEh */-1|0)){
                      var _JD/*  syEo */ = _JB/* syEo */+1|0;
                      _JA/* syEn */ = _JC/* syEq */.b;
                      _JB/* syEo */ = _JD/*  syEo */;
                      continue;
                    }else{
                      return E(_/* EXTERNAL */);
                    }
                  }
                }
              };
              if(0<=_Jy/* syEi */){
                var _JE/* syEA */ = function(_JF/* syEB */){
                  return new T2(1,new T(function(){
                    var _JG/* syEE */ = E(_Iu/* syy4 */[_JF/* syEB */]),
                    _JH/* syEO */ = E(_JG/* syEE */.d),
                    _JI/* syER */ = E(_JH/* syEO */.a),
                    _JJ/* syEV */ = E(_JG/* syEE */.e),
                    _JK/* syEY */ = E(_JJ/* syEV */.a),
                    _JL/* syF2 */ = E(_JG/* syEE */.f),
                    _JM/* syF6 */ = B(_Ec/* Lib.Physics.$wa */(_JG/* syEE */.a, _JG/* syEE */.b, _JG/* syEE */.c, _JI/* syER */.a, _JI/* syER */.b, _JI/* syER */.c, _JH/* syEO */.b, _JK/* syEY */.a, _JK/* syEY */.b, _JK/* syEY */.c, _JJ/* syEV */.b, _JL/* syF2 */.a, _JL/* syF2 */.b, _JL/* syF2 */.c, _JG/* syEE */.g, _JG/* syEE */.h, _JG/* syEE */.i));
                    return {_:0,a:E(_JM/* syF6 */.a),b:E(_JM/* syF6 */.b),c:E(_JM/* syF6 */.c),d:E(_JM/* syF6 */.d),e:E(_JM/* syF6 */.e),f:E(_JM/* syF6 */.f),g:E(_JM/* syF6 */.g),h:E(_JM/* syF6 */.h),i:E(_JM/* syF6 */.i)};
                  }),new T(function(){
                    if(_JF/* syEB */!=_Jy/* syEi */){
                      return B(_JE/* syEA */(_JF/* syEB */+1|0));
                    }else{
                      return __Z/* EXTERNAL */;
                    }
                  }));
                },
                _/* EXTERNAL */ = B(_Jz/* syEm */(B(_JE/* syEA */(0)), 0, _/* EXTERNAL */));
                return new T4(0,E(_Iv/* syy5 */),E(_Iw/* syy7 */),_Jx/* syEh */,_Jw/* syEg */);
              }else{
                return new T4(0,E(_Iv/* syy5 */),E(_Iw/* syy7 */),_Jx/* syEh */,_Jw/* syEg */);
              }
            }
          }else{
            return E(_yA/* GHC.Arr.negRange */);
          }
        };
        if(_Iv/* syy5 */>_Iw/* syy7 */){
          return new F(function(){return _Jt/* syEa */(0);});
        }else{
          return new F(function(){return _Jt/* syEa */((_Iw/* syy7 */-_Iv/* syy5 */|0)+1|0);});
        }
      };
      return B(_yQ/* GHC.ST.runSTRep */(_Js/* syFE */));
    });
    return new T2(0,_BD/* GHC.Tuple.() */,_Jr/* syFF */);
  }
},
_JN/* refresh_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(refresh)");
}),
_JO/* main2 */ = function(_JP/* sBRg */, _/* EXTERNAL */){
  var _JQ/* sBRl */ = __app0/* EXTERNAL */(E(_JN/* Lib.Screen.refresh_f1 */)),
  _JR/* sBRr */ = __app0/* EXTERNAL */(E(_Cs/* Lib.Screen.draw_f1 */)),
  _JS/* sBRu */ = B(A(_Bn/* Data.Traversable.$w$ctraverse */,[_AW/* GHC.Arr.$fIxInt */, _zj/* GHC.Base.$fApplicativeIO */, _Cp/* Lib.Object.drawObject1 */, _JP/* sBRg */, _/* EXTERNAL */])),
  _JT/* sBRx */ = B(_Iq/* Lib.Physics.nextFrame1 */(_JP/* sBRg */, _/* EXTERNAL */));
  return new T(function(){
    return E(E(_JT/* sBRx */).b);
  });
},
_JU/* a1 */ = function(_JV/* snHB */, _/* EXTERNAL */){
  while(1){
    var _JW/* snHD */ = E(_JV/* snHB */);
    if(!_JW/* snHD */._){
      return _BD/* GHC.Tuple.() */;
    }else{
      var _JX/* snHF */ = _JW/* snHD */.b,
      _JY/* snHG */ = E(_JW/* snHD */.a);
      switch(_JY/* snHG */._){
        case 0:
          var _JZ/* snHI */ = B(A1(_JY/* snHG */.a,_/* EXTERNAL */));
          _JV/* snHB */ = B(_f/* GHC.Base.++ */(_JX/* snHF */, new T2(1,_JZ/* snHI */,_o/* GHC.Types.[] */)));
          continue;
        case 1:
          _JV/* snHB */ = B(_f/* GHC.Base.++ */(_JX/* snHF */, _JY/* snHG */.a));
          continue;
        default:
          _JV/* snHB */ = _JX/* snHF */;
          continue;
      }
    }
  }
},
_K0/* $fMonadEventCIO_$sa */ = function(_K1/* snHp */, _K2/* snHq */, _/* EXTERNAL */){
  var _K3/* snHs */ = E(_K1/* snHp */);
  switch(_K3/* snHs */._){
    case 0:
      var _K4/* snHu */ = B(A1(_K3/* snHs */.a,_/* EXTERNAL */));
      return new F(function(){return _JU/* Haste.Concurrent.Monad.a1 */(B(_f/* GHC.Base.++ */(_K2/* snHq */, new T2(1,_K4/* snHu */,_o/* GHC.Types.[] */))), _/* EXTERNAL */);});
      break;
    case 1:
      return new F(function(){return _JU/* Haste.Concurrent.Monad.a1 */(B(_f/* GHC.Base.++ */(_K2/* snHq */, _K3/* snHs */.a)), _/* EXTERNAL */);});
      break;
    default:
      return new F(function(){return _JU/* Haste.Concurrent.Monad.a1 */(_K2/* snHq */, _/* EXTERNAL */);});
  }
},
_K5/* $c>>=1 */ = function(_K6/* snHc */, _K7/* snHd */, _K8/* snHe */){
  return new F(function(){return A1(_K6/* snHc */,function(_K9/* snHf */){
    return new F(function(){return A2(_K7/* snHd */,_K9/* snHf */, _K8/* snHe */);});
  });});
},
_Ka/* $fApplicativeCIO1 */ = function(_Kb/* snLu */, _Kc/* snLv */, _Kd/* snLw */){
  var _Ke/* snLB */ = function(_Kf/* snLx */){
    var _Kg/* snLy */ = new T(function(){
      return B(A1(_Kd/* snLw */,_Kf/* snLx */));
    });
    return new F(function(){return A1(_Kc/* snLv */,function(_Kh/* snLz */){
      return E(_Kg/* snLy */);
    });});
  };
  return new F(function(){return A1(_Kb/* snLu */,_Ke/* snLB */);});
},
_Ki/* $fApplicativeCIO2 */ = function(_Kj/* snLm */, _Kk/* snLn */, _Kl/* snLo */){
  var _Km/* snLp */ = new T(function(){
    return B(A1(_Kk/* snLn */,function(_Kn/* snLq */){
      return new F(function(){return A1(_Kl/* snLo */,_Kn/* snLq */);});
    }));
  });
  return new F(function(){return A1(_Kj/* snLm */,function(_Ko/* snLs */){
    return E(_Km/* snLp */);
  });});
},
_Kp/* $fApplicativeCIO3 */ = function(_Kq/* snHP */, _Kr/* snHQ */, _Ks/* snHR */){
  var _Kt/* snHW */ = function(_Ku/* snHS */){
    var _Kv/* snHV */ = function(_Kw/* snHT */){
      return new F(function(){return A1(_Ks/* snHR */,new T(function(){
        return B(A1(_Ku/* snHS */,_Kw/* snHT */));
      }));});
    };
    return new F(function(){return A1(_Kr/* snHQ */,_Kv/* snHV */);});
  };
  return new F(function(){return A1(_Kq/* snHP */,_Kt/* snHW */);});
},
_Kx/* $fApplicativeCIO4 */ = function(_Ky/* snHh */, _Kz/* snHi */){
  return new F(function(){return A1(_Kz/* snHi */,_Ky/* snHh */);});
},
_KA/* $fFunctorCIO1 */ = function(_KB/* snLg */, _KC/* snLh */, _KD/* snLi */){
  var _KE/* snLj */ = new T(function(){
    return B(A1(_KD/* snLi */,_KB/* snLg */));
  });
  return new F(function(){return A1(_KC/* snLh */,function(_KF/* snLk */){
    return E(_KE/* snLj */);
  });});
},
_KG/* $fFunctorCIO2 */ = function(_KH/* snH6 */, _KI/* snH7 */, _KJ/* snH8 */){
  var _KK/* snHb */ = function(_KL/* snH9 */){
    return new F(function(){return A1(_KJ/* snH8 */,new T(function(){
      return B(A1(_KH/* snH6 */,_KL/* snH9 */));
    }));});
  };
  return new F(function(){return A1(_KI/* snH7 */,_KK/* snHb */);});
},
_KM/* $fFunctorCIO */ = new T2(0,_KG/* Haste.Concurrent.Monad.$fFunctorCIO2 */,_KA/* Haste.Concurrent.Monad.$fFunctorCIO1 */),
_KN/* $fApplicativeCIO */ = new T5(0,_KM/* Haste.Concurrent.Monad.$fFunctorCIO */,_Kx/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_Kp/* Haste.Concurrent.Monad.$fApplicativeCIO3 */,_Ki/* Haste.Concurrent.Monad.$fApplicativeCIO2 */,_Ka/* Haste.Concurrent.Monad.$fApplicativeCIO1 */),
_KO/* >>= */ = function(_KP/* s34T */){
  return E(E(_KP/* s34T */).b);
},
_KQ/* $fMonadCIO_$c>> */ = function(_KR/* snLD */, _KS/* snLE */){
  return new F(function(){return A3(_KO/* GHC.Base.>>= */,_KT/* Haste.Concurrent.Monad.$fMonadCIO */, _KR/* snLD */, function(_KU/* snLF */){
    return E(_KS/* snLE */);
  });});
},
_KV/* a5 */ = function(_KW/* snLC */){
  return new F(function(){return err/* EXTERNAL */(_KW/* snLC */);});
},
_KT/* $fMonadCIO */ = new T(function(){
  return new T5(0,_KN/* Haste.Concurrent.Monad.$fApplicativeCIO */,_K5/* Haste.Concurrent.Monad.$c>>=1 */,_KQ/* Haste.Concurrent.Monad.$fMonadCIO_$c>> */,_Kx/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_KV/* Haste.Concurrent.Monad.a5 */);
}),
_KX/* $fMonadIOCIO1 */ = function(_KY/* snH3 */, _KZ/* snH4 */){
  return new T1(0,function(_/* EXTERNAL */){
    return new F(function(){return _z8/* GHC.Base.$fFunctorIO2 */(_KZ/* snH4 */, _KY/* snH3 */, _/* EXTERNAL */);});
  });
},
_L0/* $fMonadIOCIO */ = new T2(0,_KT/* Haste.Concurrent.Monad.$fMonadCIO */,_KX/* Haste.Concurrent.Monad.$fMonadIOCIO1 */),
_L1/* forkIO1 */ = function(_L2/* snHj */){
  return new T0(2);
},
_L3/* forkIO */ = function(_L4/* snKc */){
  var _L5/* snKd */ = new T(function(){
    return B(A1(_L4/* snKc */,_L1/* Haste.Concurrent.Monad.forkIO1 */));
  }),
  _L6/* snKi */ = function(_L7/* snKf */){
    return new T1(1,new T2(1,new T(function(){
      return B(A1(_L7/* snKf */,_BD/* GHC.Tuple.() */));
    }),new T2(1,_L5/* snKd */,_o/* GHC.Types.[] */)));
  };
  return E(_L6/* snKi */);
},
_L8/* $fMonadConcCIO */ = new T3(0,_L0/* Haste.Concurrent.Monad.$fMonadIOCIO */,_7S/* GHC.Base.id */,_L3/* Haste.Concurrent.Monad.forkIO */),
_L9/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_La/* unsafeDupablePerformIO */ = function(_Lb/* s2YSa */){
  var _Lc/* s2YSb */ = B(A1(_Lb/* s2YSa */,_/* EXTERNAL */));
  return E(_Lc/* s2YSb */);
},
_Ld/* nullValue */ = new T(function(){
  return B(_La/* GHC.IO.unsafeDupablePerformIO */(_L9/* Haste.Prim.Any.lvl2 */));
}),
_Le/* jsNull */ = new T(function(){
  return E(_Ld/* Haste.Prim.Any.nullValue */);
}),
_Lf/* Stop */ = new T0(2),
_Lg/* liftCIO */ = function(_Lh/* snGT */){
  return E(E(_Lh/* snGT */).b);
},
_Li/* putMVar */ = function(_Lj/* snKj */, _Lk/* snKk */, _Ll/* snKl */){
  var _Lm/* snKT */ = function(_Ln/* snKn */){
    var _Lo/* snKS */ = function(_/* EXTERNAL */){
      var _Lp/* snKp */ = E(_Lk/* snKk */),
      _Lq/* snKr */ = rMV/* EXTERNAL */(_Lp/* snKp */),
      _Lr/* snKu */ = E(_Lq/* snKr */);
      if(!_Lr/* snKu */._){
        var _Ls/* snKC */ = new T(function(){
          var _Lt/* snKx */ = new T(function(){
            return B(A1(_Ln/* snKn */,_BD/* GHC.Tuple.() */));
          });
          return B(_f/* GHC.Base.++ */(_Lr/* snKu */.b, new T2(1,new T2(0,_Ll/* snKl */,function(_Lu/* snKy */){
            return E(_Lt/* snKx */);
          }),_o/* GHC.Types.[] */)));
        }),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_Lp/* snKp */, new T2(0,_Lr/* snKu */.a,_Ls/* snKC */));
        return _Lf/* Haste.Concurrent.Monad.Stop */;
      }else{
        var _Lv/* snKG */ = E(_Lr/* snKu */.a);
        if(!_Lv/* snKG */._){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_Lp/* snKp */, new T2(0,_Ll/* snKl */,_o/* GHC.Types.[] */));
          return new T(function(){
            return B(A1(_Ln/* snKn */,_BD/* GHC.Tuple.() */));
          });
        }else{
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_Lp/* snKp */, new T1(1,_Lv/* snKG */.b));
          return new T1(1,new T2(1,new T(function(){
            return B(A1(_Ln/* snKn */,_BD/* GHC.Tuple.() */));
          }),new T2(1,new T(function(){
            return B(A2(_Lv/* snKG */.a,_Ll/* snKl */, _L1/* Haste.Concurrent.Monad.forkIO1 */));
          }),_o/* GHC.Types.[] */)));
        }
      }
    };
    return new T1(0,_Lo/* snKS */);
  };
  return new F(function(){return A2(_Lg/* Haste.Concurrent.Monad.liftCIO */,_Lj/* snKj */, _Lm/* snKT */);});
},
_Lw/* requestAnimationFrame_f1 */ = new T(function(){
  return eval/* EXTERNAL */("window.requestAnimationFrame");
}),
_Lx/* takeMVar1 */ = new T1(1,_o/* GHC.Types.[] */),
_Ly/* takeMVar */ = function(_Lz/* snJ3 */, _LA/* snJ4 */){
  var _LB/* snJF */ = function(_LC/* snJ5 */){
    var _LD/* snJE */ = function(_/* EXTERNAL */){
      var _LE/* snJ7 */ = E(_LA/* snJ4 */),
      _LF/* snJ9 */ = rMV/* EXTERNAL */(_LE/* snJ7 */),
      _LG/* snJc */ = E(_LF/* snJ9 */);
      if(!_LG/* snJc */._){
        var _LH/* snJd */ = _LG/* snJc */.a,
        _LI/* snJf */ = E(_LG/* snJc */.b);
        if(!_LI/* snJf */._){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_LE/* snJ7 */, _Lx/* Haste.Concurrent.Monad.takeMVar1 */);
          return new T(function(){
            return B(A1(_LC/* snJ5 */,_LH/* snJd */));
          });
        }else{
          var _LJ/* snJk */ = E(_LI/* snJf */.a),
          _/* EXTERNAL */ = wMV/* EXTERNAL */(_LE/* snJ7 */, new T2(0,_LJ/* snJk */.a,_LI/* snJf */.b));
          return new T1(1,new T2(1,new T(function(){
            return B(A1(_LC/* snJ5 */,_LH/* snJd */));
          }),new T2(1,new T(function(){
            return B(A1(_LJ/* snJk */.b,_L1/* Haste.Concurrent.Monad.forkIO1 */));
          }),_o/* GHC.Types.[] */)));
        }
      }else{
        var _LK/* snJB */ = new T(function(){
          var _LL/* snJz */ = function(_LM/* snJv */){
            var _LN/* snJw */ = new T(function(){
              return B(A1(_LC/* snJ5 */,_LM/* snJv */));
            });
            return function(_LO/* snJx */){
              return E(_LN/* snJw */);
            };
          };
          return B(_f/* GHC.Base.++ */(_LG/* snJc */.a, new T2(1,_LL/* snJz */,_o/* GHC.Types.[] */)));
        }),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_LE/* snJ7 */, new T1(1,_LK/* snJB */));
        return _Lf/* Haste.Concurrent.Monad.Stop */;
      }
    };
    return new T1(0,_LD/* snJE */);
  };
  return new F(function(){return A2(_Lg/* Haste.Concurrent.Monad.liftCIO */,_Lz/* snJ3 */, _LB/* snJF */);});
},
_LP/* $wa */ = function(_LQ/* s4hS */, _LR/* s4hT */){
  var _LS/* s4hU */ = new T(function(){
    return B(A(_Li/* Haste.Concurrent.Monad.putMVar */,[_L8/* Haste.Concurrent.Monad.$fMonadConcCIO */, _LQ/* s4hS */, _BD/* GHC.Tuple.() */, _L1/* Haste.Concurrent.Monad.forkIO1 */]));
  });
  return function(_/* EXTERNAL */){
    var _LT/* s4i5 */ = __createJSFunc/* EXTERNAL */(2, function(_LU/* s4hW */, _/* EXTERNAL */){
      var _LV/* s4hY */ = B(_K0/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_LS/* s4hU */, _o/* GHC.Types.[] */, _/* EXTERNAL */));
      return _Le/* Haste.Prim.Any.jsNull */;
    }),
    _LW/* s4ib */ = __app1/* EXTERNAL */(E(_Lw/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _LT/* s4i5 */);
    return new T(function(){
      return B(A3(_Ly/* Haste.Concurrent.Monad.takeMVar */,_L8/* Haste.Concurrent.Monad.$fMonadConcCIO */, _LQ/* s4hS */, _LR/* s4hT */));
    });
  };
},
_LX/* run2 */ = new T1(1,_o/* GHC.Types.[] */),
_LY/* run1 */ = function(_LZ/* s4iu */, _M0/* s4iv */, _/* EXTERNAL */){
  var _M1/* s4j1 */ = function(_/* EXTERNAL */){
    var _M2/* s4iy */ = nMV/* EXTERNAL */(_LZ/* s4iu */),
    _M3/* s4iA */ = _M2/* s4iy */;
    return new T(function(){
      var _M4/* s4iB */ = new T(function(){
        return B(_M5/* s4iE */(_/* EXTERNAL */));
      }),
      _M6/* s4iC */ = function(_/* EXTERNAL */){
        var _M7/* s4iG */ = rMV/* EXTERNAL */(_M3/* s4iA */),
        _M8/* s4iJ */ = B(A2(_M0/* s4iv */,_M7/* s4iG */, _/* EXTERNAL */)),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_M3/* s4iA */, _M8/* s4iJ */),
        _M9/* s4iX */ = function(_/* EXTERNAL */){
          var _Ma/* s4iO */ = nMV/* EXTERNAL */(_LX/* Lib.Screen.run2 */);
          return new T(function(){
            return new T1(0,B(_LP/* Lib.Screen.$wa */(_Ma/* s4iO */, function(_Mb/* s4iS */){
              return E(_M4/* s4iB */);
            })));
          });
        };
        return new T1(0,_M9/* s4iX */);
      },
      _Mc/* s4iD */ = new T(function(){
        return new T1(0,_M6/* s4iC */);
      }),
      _M5/* s4iE */ = function(_Md/* s4iZ */){
        return E(_Mc/* s4iD */);
      };
      return B(_M5/* s4iE */(_/* EXTERNAL */));
    });
  };
  return new F(function(){return _K0/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T1(0,_M1/* s4j1 */), _o/* GHC.Types.[] */, _/* EXTERNAL */);});
},
_Me/* main1 */ = function(_/* EXTERNAL */){
  var _Mf/* sBRM */ = __app2/* EXTERNAL */(E(_0/* Lib.Screen.compile_f1 */), E(_7U/* Lib.Shader.fieldStr */), E(_he/* Lib.Shader.gradStr */));
  return new F(function(){return _LY/* Lib.Screen.run1 */(_yT/* Main.initial2 */, _JO/* Main.main2 */, _/* EXTERNAL */);});
},
_Mg/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _Me/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_Mg, [0]));};window.onload = hasteMain;