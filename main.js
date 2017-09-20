"use strict";
var __haste_prog_id = 'e117d8b23785578f75fa71fb6df4b4b0409654b808120e37eb95d03e15cc9fe0';
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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==( -2147483648)){_3l=new T1(1,I_fromInt( -2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return  -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0, -1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==( -2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return  -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S( -1021,53,_6k,_6l);});}else{return  -B(_5S( -1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=function(_7h){return E(E(_7h).a);},_7i=function(_7j){return E(E(_7j).a);},_7k=function(_7l){return E(E(_7l).c);},_7m=function(_7n){return E(E(_7n).b);},_7o=function(_7p){return E(E(_7p).d);},_7q=new T1(0,1),_7r=new T1(0,2),_7s=new T2(0,E(_7q),E(_7r)),_7t=new T1(0,5),_7u=new T1(0,4),_7v=new T2(0,E(_7u),E(_7t)),_7w=function(_7x){return E(E(_7x).e);},_7y=function(_7z,_7A,_7B,_7C){var _7D=B(_7g(_7z)),_7E=B(_7i(_7D)),_7F=new T(function(){var _7G=new T(function(){var _7H=new T(function(){var _7I=new T(function(){var _7J=new T(function(){var _7K=new T(function(){return B(A3(_6I,_7E,new T(function(){return B(A3(_7k,_7E,_7A,_7A));}),new T(function(){return B(A3(_7k,_7E,_7C,_7C));})));});return B(A2(_7w,_7z,_7K));});return B(A3(_7m,_7E,_7J,new T(function(){return B(A2(_7o,_7D,_7v));})));});return B(A3(_7k,_7E,_7I,_7I));});return B(A3(_6I,_7E,_7H,new T(function(){return B(A3(_7k,_7E,_7B,_7B));})));});return B(A2(_7w,_7z,_7G));});return new F(function(){return A3(_7m,_7E,_7F,new T(function(){return B(A2(_7o,_7D,_7s));}));});},_7L=new T(function(){return B(unCStr("x"));}),_7M=new T1(0,_7L),_7N=new T(function(){return B(unCStr("y"));}),_7O=new T1(0,_7N),_7P=new T(function(){return B(unCStr("z"));}),_7Q=new T1(0,_7P),_7R=new T(function(){return B(_7y(_7f,_7M,_7O,_7Q));}),_7S=function(_7T){return E(_7T);},_7U=new T(function(){return toJSStr(B(_5(_p,_7S,_7R)));}),_7V=function(_7W,_7X,_7Y){var _7Z=new T(function(){return B(_1(_7W));}),_80=new T(function(){return B(_3(_7W));}),_81=function(_82){var _83=E(_82);if(!_83._){return E(_80);}else{return new F(function(){return A2(_7Z,new T(function(){return B(_5(_7W,_7X,_83.a));}),new T(function(){return B(_81(_83.b));}));});}};return new F(function(){return _81(_7Y);});},_84=new T3(0,E(_7M),E(_7O),E(_7Q)),_85=new T(function(){return B(unCStr("(/=) is not defined"));}),_86=new T(function(){return B(err(_85));}),_87=new T(function(){return B(unCStr("(==) is not defined"));}),_88=new T(function(){return B(err(_87));}),_89=new T2(0,_88,_86),_8a=new T(function(){return B(unCStr("(<) is not defined"));}),_8b=new T(function(){return B(err(_8a));}),_8c=new T(function(){return B(unCStr("(<=) is not defined"));}),_8d=new T(function(){return B(err(_8c));}),_8e=new T(function(){return B(unCStr("(>) is not defined"));}),_8f=new T(function(){return B(err(_8e));}),_8g=new T(function(){return B(unCStr("(>=) is not defined"));}),_8h=new T(function(){return B(err(_8g));}),_8i=new T(function(){return B(unCStr("compare is not defined"));}),_8j=new T(function(){return B(err(_8i));}),_8k=new T(function(){return B(unCStr("max("));}),_8l=new T1(0,_8k),_8m=function(_8n,_8o){return new T1(1,new T2(1,_8l,new T2(1,_8n,new T2(1,_r,new T2(1,_8o,_w)))));},_8p=new T(function(){return B(unCStr("min("));}),_8q=new T1(0,_8p),_8r=function(_8s,_8t){return new T1(1,new T2(1,_8q,new T2(1,_8s,new T2(1,_r,new T2(1,_8t,_w)))));},_8u={_:0,a:_89,b:_8j,c:_8b,d:_8d,e:_8f,f:_8h,g:_8m,h:_8r},_8v=new T2(0,_7f,_8u),_8w=function(_8x,_8y){var _8z=E(_8x);return E(_8y);},_8A=function(_8B,_8C){var _8D=E(_8C);return E(_8B);},_8E=function(_8F,_8G){var _8H=E(_8F),_8I=E(_8G);return new T3(0,E(B(A1(_8H.a,_8I.a))),E(B(A1(_8H.b,_8I.b))),E(B(A1(_8H.c,_8I.c))));},_8J=function(_8K,_8L,_8M){return new T3(0,E(_8K),E(_8L),E(_8M));},_8N=function(_8O){return new F(function(){return _8J(_8O,_8O,_8O);});},_8P=function(_8Q,_8R){var _8S=E(_8R),_8T=E(_8Q);return new T3(0,E(_8T),E(_8T),E(_8T));},_8U=function(_8V,_8W){var _8X=E(_8W);return new T3(0,E(B(A1(_8V,_8X.a))),E(B(A1(_8V,_8X.b))),E(B(A1(_8V,_8X.c))));},_8Y=new T2(0,_8U,_8P),_8Z=new T5(0,_8Y,_8N,_8E,_8w,_8A),_90=new T1(0,0),_91=function(_92){return E(E(_92).g);},_93=function(_94){var _95=B(A2(_91,_94,_7q)),_96=B(A2(_91,_94,_90));return new T3(0,E(new T3(0,E(_95),E(_96),E(_96))),E(new T3(0,E(_96),E(_95),E(_96))),E(new T3(0,E(_96),E(_96),E(_95))));},_97=function(_98){return E(E(_98).a);},_99=function(_9a){return E(E(_9a).f);},_9b=function(_9c){return E(E(_9c).b);},_9d=function(_9e){return E(E(_9e).c);},_9f=function(_9g){return E(E(_9g).a);},_9h=function(_9i){return E(E(_9i).d);},_9j=function(_9k,_9l,_9m,_9n,_9o){var _9p=new T(function(){return E(E(E(_9k).c).a);}),_9q=new T(function(){var _9r=E(_9k).a,_9s=new T(function(){var _9t=new T(function(){return B(_7g(_9p));}),_9u=new T(function(){return B(_7i(_9t));}),_9v=new T(function(){return B(A2(_9h,_9p,_9l));}),_9w=new T(function(){return B(A3(_99,_9p,_9l,_9n));}),_9x=function(_9y,_9z){var _9A=new T(function(){var _9B=new T(function(){return B(A3(_9b,_9t,new T(function(){return B(A3(_7k,_9u,_9n,_9y));}),_9l));});return B(A3(_6I,_9u,_9B,new T(function(){return B(A3(_7k,_9u,_9z,_9v));})));});return new F(function(){return A3(_7k,_9u,_9w,_9A);});};return B(A3(_9f,B(_97(_9r)),_9x,_9m));});return B(A3(_9d,_9r,_9s,_9o));});return new T2(0,new T(function(){return B(A3(_99,_9p,_9l,_9n));}),_9q);},_9C=function(_9D,_9E,_9F,_9G){var _9H=E(_9F),_9I=E(_9G),_9J=B(_9j(_9E,_9H.a,_9H.b,_9I.a,_9I.b));return new T2(0,_9J.a,_9J.b);},_9K=new T1(0,1),_9L=function(_9M){return E(E(_9M).l);},_9N=function(_9O,_9P,_9Q){var _9R=new T(function(){return E(E(E(_9O).c).a);}),_9S=new T(function(){var _9T=new T(function(){return B(_7g(_9R));}),_9U=new T(function(){var _9V=B(_7i(_9T)),_9W=new T(function(){var _9X=new T(function(){return B(A3(_7m,_9V,new T(function(){return B(A2(_91,_9V,_9K));}),new T(function(){return B(A3(_7k,_9V,_9P,_9P));})));});return B(A2(_7w,_9R,_9X));});return B(A2(_6K,_9V,_9W));});return B(A3(_9f,B(_97(E(_9O).a)),function(_9Y){return new F(function(){return A3(_9b,_9T,_9Y,_9U);});},_9Q));});return new T2(0,new T(function(){return B(A2(_9L,_9R,_9P));}),_9S);},_9Z=function(_a0,_a1,_a2){var _a3=E(_a2),_a4=B(_9N(_a1,_a3.a,_a3.b));return new T2(0,_a4.a,_a4.b);},_a5=function(_a6){return E(E(_a6).r);},_a7=function(_a8,_a9,_aa){var _ab=new T(function(){return E(E(E(_a8).c).a);}),_ac=new T(function(){var _ad=new T(function(){return B(_7g(_ab));}),_ae=new T(function(){var _af=new T(function(){var _ag=B(_7i(_ad));return B(A3(_7m,_ag,new T(function(){return B(A3(_7k,_ag,_a9,_a9));}),new T(function(){return B(A2(_91,_ag,_9K));})));});return B(A2(_7w,_ab,_af));});return B(A3(_9f,B(_97(E(_a8).a)),function(_ah){return new F(function(){return A3(_9b,_ad,_ah,_ae);});},_aa));});return new T2(0,new T(function(){return B(A2(_a5,_ab,_a9));}),_ac);},_ai=function(_aj,_ak,_al){var _am=E(_al),_an=B(_a7(_ak,_am.a,_am.b));return new T2(0,_an.a,_an.b);},_ao=function(_ap){return E(E(_ap).k);},_aq=function(_ar,_as,_at){var _au=new T(function(){return E(E(E(_ar).c).a);}),_av=new T(function(){var _aw=new T(function(){return B(_7g(_au));}),_ax=new T(function(){var _ay=new T(function(){var _az=B(_7i(_aw));return B(A3(_7m,_az,new T(function(){return B(A2(_91,_az,_9K));}),new T(function(){return B(A3(_7k,_az,_as,_as));})));});return B(A2(_7w,_au,_ay));});return B(A3(_9f,B(_97(E(_ar).a)),function(_aA){return new F(function(){return A3(_9b,_aw,_aA,_ax);});},_at));});return new T2(0,new T(function(){return B(A2(_ao,_au,_as));}),_av);},_aB=function(_aC,_aD,_aE){var _aF=E(_aE),_aG=B(_aq(_aD,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=function(_aI){return E(E(_aI).q);},_aJ=function(_aK,_aL,_aM){var _aN=new T(function(){return E(E(E(_aK).c).a);}),_aO=new T(function(){var _aP=new T(function(){return B(_7g(_aN));}),_aQ=new T(function(){var _aR=new T(function(){var _aS=B(_7i(_aP));return B(A3(_6I,_aS,new T(function(){return B(A3(_7k,_aS,_aL,_aL));}),new T(function(){return B(A2(_91,_aS,_9K));})));});return B(A2(_7w,_aN,_aR));});return B(A3(_9f,B(_97(E(_aK).a)),function(_aT){return new F(function(){return A3(_9b,_aP,_aT,_aQ);});},_aM));});return new T2(0,new T(function(){return B(A2(_aH,_aN,_aL));}),_aO);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aJ(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).m);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_7g(_b6));}),_b9=new T(function(){var _ba=B(_7i(_b8));return B(A3(_6I,_ba,new T(function(){return B(A2(_91,_ba,_9K));}),new T(function(){return B(A3(_7k,_ba,_b4,_b4));})));});return B(A3(_9f,B(_97(E(_b3).a)),function(_bb){return new F(function(){return A3(_9b,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).s);},_bk=function(_bl,_bm,_bn){var _bo=new T(function(){return E(E(E(_bl).c).a);}),_bp=new T(function(){var _bq=new T(function(){return B(_7g(_bo));}),_br=new T(function(){var _bs=B(_7i(_bq));return B(A3(_7m,_bs,new T(function(){return B(A2(_91,_bs,_9K));}),new T(function(){return B(A3(_7k,_bs,_bm,_bm));})));});return B(A3(_9f,B(_97(E(_bl).a)),function(_bt){return new F(function(){return A3(_9b,_bq,_bt,_br);});},_bn));});return new T2(0,new T(function(){return B(A2(_bi,_bo,_bm));}),_bp);},_bu=function(_bv,_bw,_bx){var _by=E(_bx),_bz=B(_bk(_bw,_by.a,_by.b));return new T2(0,_bz.a,_bz.b);},_bA=function(_bB){return E(E(_bB).i);},_bC=function(_bD){return E(E(_bD).h);},_bE=function(_bF,_bG,_bH){var _bI=new T(function(){return E(E(E(_bF).c).a);}),_bJ=new T(function(){var _bK=new T(function(){return B(_7i(new T(function(){return B(_7g(_bI));})));}),_bL=new T(function(){return B(A2(_6K,_bK,new T(function(){return B(A2(_bC,_bI,_bG));})));});return B(A3(_9f,B(_97(E(_bF).a)),function(_bM){return new F(function(){return A3(_7k,_bK,_bM,_bL);});},_bH));});return new T2(0,new T(function(){return B(A2(_bA,_bI,_bG));}),_bJ);},_bN=function(_bO,_bP,_bQ){var _bR=E(_bQ),_bS=B(_bE(_bP,_bR.a,_bR.b));return new T2(0,_bS.a,_bS.b);},_bT=function(_bU){return E(E(_bU).o);},_bV=function(_bW){return E(E(_bW).n);},_bX=function(_bY,_bZ,_c0){var _c1=new T(function(){return E(E(E(_bY).c).a);}),_c2=new T(function(){var _c3=new T(function(){return B(_7i(new T(function(){return B(_7g(_c1));})));}),_c4=new T(function(){return B(A2(_bV,_c1,_bZ));});return B(A3(_9f,B(_97(E(_bY).a)),function(_c5){return new F(function(){return A3(_7k,_c3,_c5,_c4);});},_c0));});return new T2(0,new T(function(){return B(A2(_bT,_c1,_bZ));}),_c2);},_c6=function(_c7,_c8,_c9){var _ca=E(_c9),_cb=B(_bX(_c8,_ca.a,_ca.b));return new T2(0,_cb.a,_cb.b);},_cc=function(_cd){return E(E(_cd).c);},_ce=function(_cf,_cg,_ch){var _ci=new T(function(){return E(E(E(_cf).c).a);}),_cj=new T(function(){var _ck=new T(function(){return B(_7i(new T(function(){return B(_7g(_ci));})));}),_cl=new T(function(){return B(A2(_cc,_ci,_cg));});return B(A3(_9f,B(_97(E(_cf).a)),function(_cm){return new F(function(){return A3(_7k,_ck,_cm,_cl);});},_ch));});return new T2(0,new T(function(){return B(A2(_cc,_ci,_cg));}),_cj);},_cn=function(_co,_cp,_cq){var _cr=E(_cq),_cs=B(_ce(_cp,_cr.a,_cr.b));return new T2(0,_cs.a,_cs.b);},_ct=function(_cu,_cv,_cw){var _cx=new T(function(){return E(E(E(_cu).c).a);}),_cy=new T(function(){var _cz=new T(function(){return B(_7g(_cx));}),_cA=new T(function(){return B(_7i(_cz));}),_cB=new T(function(){return B(A3(_9b,_cz,new T(function(){return B(A2(_91,_cA,_9K));}),_cv));});return B(A3(_9f,B(_97(E(_cu).a)),function(_cC){return new F(function(){return A3(_7k,_cA,_cC,_cB);});},_cw));});return new T2(0,new T(function(){return B(A2(_9h,_cx,_cv));}),_cy);},_cD=function(_cE,_cF,_cG){var _cH=E(_cG),_cI=B(_ct(_cF,_cH.a,_cH.b));return new T2(0,_cI.a,_cI.b);},_cJ=function(_cK,_cL,_cM,_cN){var _cO=new T(function(){return E(E(_cL).c);}),_cP=new T3(0,new T(function(){return E(E(_cL).a);}),new T(function(){return E(E(_cL).b);}),new T2(0,new T(function(){return E(E(_cO).a);}),new T(function(){return E(E(_cO).b);})));return new F(function(){return A3(_9b,_cK,new T(function(){var _cQ=E(_cN),_cR=B(_ct(_cP,_cQ.a,_cQ.b));return new T2(0,_cR.a,_cR.b);}),new T(function(){var _cS=E(_cM),_cT=B(_ct(_cP,_cS.a,_cS.b));return new T2(0,_cT.a,_cT.b);}));});},_cU=new T1(0,0),_cV=function(_cW){return E(E(_cW).b);},_cX=function(_cY){return E(E(_cY).b);},_cZ=function(_d0){var _d1=new T(function(){return E(E(E(_d0).c).a);}),_d2=new T(function(){return B(A2(_cX,E(_d0).a,new T(function(){return B(A2(_91,B(_7i(B(_7g(_d1)))),_cU));})));});return new T2(0,new T(function(){return B(_cV(_d1));}),_d2);},_d3=function(_d4,_d5){var _d6=B(_cZ(_d5));return new T2(0,_d6.a,_d6.b);},_d7=function(_d8,_d9,_da){var _db=new T(function(){return E(E(E(_d8).c).a);}),_dc=new T(function(){var _dd=new T(function(){return B(_7i(new T(function(){return B(_7g(_db));})));}),_de=new T(function(){return B(A2(_bA,_db,_d9));});return B(A3(_9f,B(_97(E(_d8).a)),function(_df){return new F(function(){return A3(_7k,_dd,_df,_de);});},_da));});return new T2(0,new T(function(){return B(A2(_bC,_db,_d9));}),_dc);},_dg=function(_dh,_di,_dj){var _dk=E(_dj),_dl=B(_d7(_di,_dk.a,_dk.b));return new T2(0,_dl.a,_dl.b);},_dm=function(_dn,_do,_dp){var _dq=new T(function(){return E(E(E(_dn).c).a);}),_dr=new T(function(){var _ds=new T(function(){return B(_7i(new T(function(){return B(_7g(_dq));})));}),_dt=new T(function(){return B(A2(_bT,_dq,_do));});return B(A3(_9f,B(_97(E(_dn).a)),function(_du){return new F(function(){return A3(_7k,_ds,_du,_dt);});},_dp));});return new T2(0,new T(function(){return B(A2(_bV,_dq,_do));}),_dr);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dm(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=new T1(0,2),_dC=function(_dD,_dE,_dF){var _dG=new T(function(){return E(E(E(_dD).c).a);}),_dH=new T(function(){var _dI=new T(function(){return B(_7g(_dG));}),_dJ=new T(function(){return B(_7i(_dI));}),_dK=new T(function(){var _dL=new T(function(){return B(A3(_9b,_dI,new T(function(){return B(A2(_91,_dJ,_9K));}),new T(function(){return B(A2(_91,_dJ,_dB));})));});return B(A3(_9b,_dI,_dL,new T(function(){return B(A2(_7w,_dG,_dE));})));});return B(A3(_9f,B(_97(E(_dD).a)),function(_dM){return new F(function(){return A3(_7k,_dJ,_dM,_dK);});},_dF));});return new T2(0,new T(function(){return B(A2(_7w,_dG,_dE));}),_dH);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dC(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).j);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_7g(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bA,_dZ,_dX));});return B(A3(_7k,B(_7i(_e1)),_e3,_e3));});return B(A3(_9f,B(_97(E(_dW).a)),function(_e4){return new F(function(){return A3(_9b,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec){return E(E(_ec).p);},_ed=function(_ee,_ef,_eg){var _eh=new T(function(){return E(E(E(_ee).c).a);}),_ei=new T(function(){var _ej=new T(function(){return B(_7g(_eh));}),_ek=new T(function(){var _el=new T(function(){return B(A2(_bT,_eh,_ef));});return B(A3(_7k,B(_7i(_ej)),_el,_el));});return B(A3(_9f,B(_97(E(_ee).a)),function(_em){return new F(function(){return A3(_9b,_ej,_em,_ek);});},_eg));});return new T2(0,new T(function(){return B(A2(_eb,_eh,_ef));}),_ei);},_en=function(_eo,_ep,_eq){var _er=E(_eq),_es=B(_ed(_ep,_er.a,_er.b));return new T2(0,_es.a,_es.b);},_et=function(_eu,_ev){return {_:0,a:_eu,b:new T(function(){return B(_d3(_eu,_ev));}),c:function(_ew){return new F(function(){return _cn(_eu,_ev,_ew);});},d:function(_ew){return new F(function(){return _cD(_eu,_ev,_ew);});},e:function(_ew){return new F(function(){return _dN(_eu,_ev,_ew);});},f:function(_ex,_ew){return new F(function(){return _9C(_eu,_ev,_ex,_ew);});},g:function(_ex,_ew){return new F(function(){return _cJ(_eu,_ev,_ex,_ew);});},h:function(_ew){return new F(function(){return _dg(_eu,_ev,_ew);});},i:function(_ew){return new F(function(){return _bN(_eu,_ev,_ew);});},j:function(_ew){return new F(function(){return _e5(_eu,_ev,_ew);});},k:function(_ew){return new F(function(){return _aB(_eu,_ev,_ew);});},l:function(_ew){return new F(function(){return _9Z(_eu,_ev,_ew);});},m:function(_ew){return new F(function(){return _bc(_eu,_ev,_ew);});},n:function(_ew){return new F(function(){return _dv(_eu,_ev,_ew);});},o:function(_ew){return new F(function(){return _c6(_eu,_ev,_ew);});},p:function(_ew){return new F(function(){return _en(_eu,_ev,_ew);});},q:function(_ew){return new F(function(){return _aU(_eu,_ev,_ew);});},r:function(_ew){return new F(function(){return _ai(_eu,_ev,_ew);});},s:function(_ew){return new F(function(){return _bu(_eu,_ev,_ew);});}};},_ey=function(_ez,_eA,_eB,_eC,_eD){var _eE=new T(function(){return B(_7g(new T(function(){return E(E(E(_ez).c).a);})));}),_eF=new T(function(){var _eG=E(_ez).a,_eH=new T(function(){var _eI=new T(function(){return B(_7i(_eE));}),_eJ=new T(function(){return B(A3(_7k,_eI,_eC,_eC));}),_eK=function(_eL,_eM){var _eN=new T(function(){return B(A3(_7m,_eI,new T(function(){return B(A3(_7k,_eI,_eL,_eC));}),new T(function(){return B(A3(_7k,_eI,_eA,_eM));})));});return new F(function(){return A3(_9b,_eE,_eN,_eJ);});};return B(A3(_9f,B(_97(_eG)),_eK,_eB));});return B(A3(_9d,_eG,_eH,_eD));});return new T2(0,new T(function(){return B(A3(_9b,_eE,_eA,_eC));}),_eF);},_eO=function(_eP,_eQ,_eR,_eS){var _eT=E(_eR),_eU=E(_eS),_eV=B(_ey(_eQ,_eT.a,_eT.b,_eU.a,_eU.b));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX,_eY){var _eZ=new T(function(){return B(_7g(new T(function(){return E(E(E(_eX).c).a);})));}),_f0=new T(function(){return B(A2(_cX,E(_eX).a,new T(function(){return B(A2(_91,B(_7i(_eZ)),_cU));})));});return new T2(0,new T(function(){return B(A2(_7o,_eZ,_eY));}),_f0);},_f1=function(_f2,_f3,_f4){var _f5=B(_eW(_f3,_f4));return new T2(0,_f5.a,_f5.b);},_f6=function(_f7,_f8,_f9){var _fa=new T(function(){return B(_7g(new T(function(){return E(E(E(_f7).c).a);})));}),_fb=new T(function(){return B(_7i(_fa));}),_fc=new T(function(){var _fd=new T(function(){var _fe=new T(function(){return B(A3(_9b,_fa,new T(function(){return B(A2(_91,_fb,_9K));}),new T(function(){return B(A3(_7k,_fb,_f8,_f8));})));});return B(A2(_6K,_fb,_fe));});return B(A3(_9f,B(_97(E(_f7).a)),function(_ff){return new F(function(){return A3(_7k,_fb,_ff,_fd);});},_f9));}),_fg=new T(function(){return B(A3(_9b,_fa,new T(function(){return B(A2(_91,_fb,_9K));}),_f8));});return new T2(0,_fg,_fc);},_fh=function(_fi,_fj,_fk){var _fl=E(_fk),_fm=B(_f6(_fj,_fl.a,_fl.b));return new T2(0,_fm.a,_fm.b);},_fn=function(_fo,_fp){return new T4(0,_fo,function(_ex,_ew){return new F(function(){return _eO(_fo,_fp,_ex,_ew);});},function(_ew){return new F(function(){return _fh(_fo,_fp,_ew);});},function(_ew){return new F(function(){return _f1(_fo,_fp,_ew);});});},_fq=function(_fr,_fs,_ft,_fu,_fv){var _fw=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fr).c).a);})));})));}),_fx=new T(function(){var _fy=E(_fr).a,_fz=new T(function(){var _fA=function(_fB,_fC){return new F(function(){return A3(_6I,_fw,new T(function(){return B(A3(_7k,_fw,_fs,_fC));}),new T(function(){return B(A3(_7k,_fw,_fB,_fu));}));});};return B(A3(_9f,B(_97(_fy)),_fA,_ft));});return B(A3(_9d,_fy,_fz,_fv));});return new T2(0,new T(function(){return B(A3(_7k,_fw,_fs,_fu));}),_fx);},_fD=function(_fE,_fF,_fG){var _fH=E(_fF),_fI=E(_fG),_fJ=B(_fq(_fE,_fH.a,_fH.b,_fI.a,_fI.b));return new T2(0,_fJ.a,_fJ.b);},_fK=function(_fL,_fM,_fN,_fO,_fP){var _fQ=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fL).c).a);})));})));}),_fR=new T(function(){var _fS=E(_fL).a,_fT=new T(function(){return B(A3(_9f,B(_97(_fS)),new T(function(){return B(_6I(_fQ));}),_fN));});return B(A3(_9d,_fS,_fT,_fP));});return new T2(0,new T(function(){return B(A3(_6I,_fQ,_fM,_fO));}),_fR);},_fU=function(_fV,_fW,_fX){var _fY=E(_fW),_fZ=E(_fX),_g0=B(_fK(_fV,_fY.a,_fY.b,_fZ.a,_fZ.b));return new T2(0,_g0.a,_g0.b);},_g1=function(_g2,_g3,_g4){var _g5=B(_g6(_g2));return new F(function(){return A3(_6I,_g5,_g3,new T(function(){return B(A2(_6K,_g5,_g4));}));});},_g7=function(_g8){return E(E(_g8).e);},_g9=function(_ga){return E(E(_ga).f);},_gb=function(_gc,_gd,_ge){var _gf=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gc).c).a);})));})));}),_gg=new T(function(){var _gh=new T(function(){return B(A2(_g9,_gf,_gd));});return B(A3(_9f,B(_97(E(_gc).a)),function(_gi){return new F(function(){return A3(_7k,_gf,_gi,_gh);});},_ge));});return new T2(0,new T(function(){return B(A2(_g7,_gf,_gd));}),_gg);},_gj=function(_gk,_gl){var _gm=E(_gl),_gn=B(_gb(_gk,_gm.a,_gm.b));return new T2(0,_gn.a,_gn.b);},_go=function(_gp,_gq){var _gr=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gs=new T(function(){return B(A2(_cX,E(_gp).a,new T(function(){return B(A2(_91,_gr,_cU));})));});return new T2(0,new T(function(){return B(A2(_91,_gr,_gq));}),_gs);},_gt=function(_gu,_gv){var _gw=B(_go(_gu,_gv));return new T2(0,_gw.a,_gw.b);},_gx=function(_gy,_gz,_gA){var _gB=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gy).c).a);})));})));}),_gC=new T(function(){return B(A3(_9f,B(_97(E(_gy).a)),new T(function(){return B(_6K(_gB));}),_gA));});return new T2(0,new T(function(){return B(A2(_6K,_gB,_gz));}),_gC);},_gD=function(_gE,_gF){var _gG=E(_gF),_gH=B(_gx(_gE,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK){var _gL=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gM=new T(function(){return B(A2(_cX,E(_gJ).a,new T(function(){return B(A2(_91,_gL,_cU));})));});return new T2(0,new T(function(){return B(A2(_g9,_gL,_gK));}),_gM);},_gN=function(_gO,_gP){var _gQ=B(_gI(_gO,E(_gP).a));return new T2(0,_gQ.a,_gQ.b);},_g6=function(_gR){return {_:0,a:function(_ex,_ew){return new F(function(){return _fU(_gR,_ex,_ew);});},b:function(_ex,_ew){return new F(function(){return _g1(_gR,_ex,_ew);});},c:function(_ex,_ew){return new F(function(){return _fD(_gR,_ex,_ew);});},d:function(_ew){return new F(function(){return _gD(_gR,_ew);});},e:function(_ew){return new F(function(){return _gj(_gR,_ew);});},f:function(_ew){return new F(function(){return _gN(_gR,_ew);});},g:function(_ew){return new F(function(){return _gt(_gR,_ew);});}};},_gS=function(_gT){var _gU=new T(function(){return E(E(_gT).a);}),_gV=new T3(0,_8Z,_93,new T2(0,_gU,new T(function(){return E(E(_gT).b);}))),_gW=new T(function(){return B(_et(new T(function(){return B(_fn(new T(function(){return B(_g6(_gV));}),_gV));}),_gV));}),_gX=new T(function(){return B(_7i(new T(function(){return B(_7g(_gU));})));});return function(_gY){var _gZ=E(_gY),_h0=B(A2(_91,_gX,_7q)),_h1=B(A2(_91,_gX,_90));return E(B(_7y(_gW,new T2(0,_gZ.a,new T3(0,E(_h0),E(_h1),E(_h1))),new T2(0,_gZ.b,new T3(0,E(_h1),E(_h0),E(_h1))),new T2(0,_gZ.c,new T3(0,E(_h1),E(_h1),E(_h0))))).b);};},_h2=new T(function(){return B(_gS(_8v));}),_h3=function(_h4,_h5){var _h6=E(_h5);return (_h6._==0)?__Z:new T2(1,_h4,new T2(1,_h6.a,new T(function(){return B(_h3(_h4,_h6.b));})));},_h7=new T(function(){var _h8=B(A1(_h2,_84));return new T2(1,_h8.a,new T(function(){return B(_h3(_r,new T2(1,_h8.b,new T2(1,_h8.c,_o))));}));}),_h9=new T1(1,_h7),_ha=new T2(1,_h9,_w),_hb=new T(function(){return B(unCStr("vec3("));}),_hc=new T1(0,_hb),_hd=new T2(1,_hc,_ha),_he=new T(function(){return toJSStr(B(_7V(_p,_7S,_hd)));}),_hf=function(_hg,_hh){while(1){var _hi=E(_hg);if(!_hi._){return E(_hh);}else{var _hj=_hh+1|0;_hg=_hi.b;_hh=_hj;continue;}}},_hk=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hl=new T(function(){return B(err(_hk));}),_hm=0,_hn=new T3(0,E(_hm),E(_hm),E(_hm)),_ho=new T(function(){return B(unCStr("Negative exponent"));}),_hp=new T(function(){return B(err(_ho));}),_hq=function(_hr,_hs,_ht){while(1){if(!(_hs%2)){var _hu=_hr*_hr,_hv=quot(_hs,2);_hr=_hu;_hs=_hv;continue;}else{var _hw=E(_hs);if(_hw==1){return _hr*_ht;}else{var _hu=_hr*_hr,_hx=_hr*_ht;_hr=_hu;_hs=quot(_hw-1|0,2);_ht=_hx;continue;}}}},_hy=function(_hz,_hA){while(1){if(!(_hA%2)){var _hB=_hz*_hz,_hC=quot(_hA,2);_hz=_hB;_hA=_hC;continue;}else{var _hD=E(_hA);if(_hD==1){return E(_hz);}else{return new F(function(){return _hq(_hz*_hz,quot(_hD-1|0,2),_hz);});}}}},_hE=function(_hF){var _hG=E(_hF);return new F(function(){return Math.log(_hG+(_hG+1)*Math.sqrt((_hG-1)/(_hG+1)));});},_hH=function(_hI){var _hJ=E(_hI);return new F(function(){return Math.log(_hJ+Math.sqrt(1+_hJ*_hJ));});},_hK=function(_hL){var _hM=E(_hL);return 0.5*Math.log((1+_hM)/(1-_hM));},_hN=function(_hO,_hP){return Math.log(E(_hP))/Math.log(E(_hO));},_hQ=3.141592653589793,_hR=function(_hS){var _hT=E(_hS);return new F(function(){return _6j(_hT.a,_hT.b);});},_hU=function(_hV){return 1/E(_hV);},_hW=function(_hX){var _hY=E(_hX),_hZ=E(_hY);return (_hZ==0)?E(_6i):(_hZ<=0)? -_hZ:E(_hY);},_i0=function(_i1){var _i2=E(_i1);if(!_i2._){return _i2.a;}else{return new F(function(){return I_toNumber(_i2.a);});}},_i3=function(_i4){return new F(function(){return _i0(_i4);});},_i5=1,_i6= -1,_i7=function(_i8){var _i9=E(_i8);return (_i9<=0)?(_i9>=0)?E(_i9):E(_i6):E(_i5);},_ia=function(_ib,_ic){return E(_ib)-E(_ic);},_id=function(_ie){return  -E(_ie);},_if=function(_ig,_ih){return E(_ig)+E(_ih);},_ii=function(_ij,_ik){return E(_ij)*E(_ik);},_il={_:0,a:_if,b:_ia,c:_ii,d:_id,e:_hW,f:_i7,g:_i3},_im=function(_in,_io){return E(_in)/E(_io);},_ip=new T4(0,_il,_im,_hU,_hR),_iq=function(_ir){return new F(function(){return Math.acos(E(_ir));});},_is=function(_it){return new F(function(){return Math.asin(E(_it));});},_iu=function(_iv){return new F(function(){return Math.atan(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.cos(E(_ix));});},_iy=function(_iz){return new F(function(){return cosh(E(_iz));});},_iA=function(_iB){return new F(function(){return Math.exp(E(_iB));});},_iC=function(_iD){return new F(function(){return Math.log(E(_iD));});},_iE=function(_iF,_iG){return new F(function(){return Math.pow(E(_iF),E(_iG));});},_iH=function(_iI){return new F(function(){return Math.sin(E(_iI));});},_iJ=function(_iK){return new F(function(){return sinh(E(_iK));});},_iL=function(_iM){return new F(function(){return Math.sqrt(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.tan(E(_iO));});},_iP=function(_iQ){return new F(function(){return tanh(E(_iQ));});},_iR={_:0,a:_ip,b:_hQ,c:_iA,d:_iC,e:_iL,f:_iE,g:_hN,h:_iH,i:_iw,j:_iN,k:_is,l:_iq,m:_iu,n:_iJ,o:_iy,p:_iP,q:_hH,r:_hE,s:_hK},_iS=function(_iT,_iU){return (E(_iT)!=E(_iU))?true:false;},_iV=function(_iW,_iX){return E(_iW)==E(_iX);},_iY=new T2(0,_iV,_iS),_iZ=function(_j0,_j1){return E(_j0)<E(_j1);},_j2=function(_j3,_j4){return E(_j3)<=E(_j4);},_j5=function(_j6,_j7){return E(_j6)>E(_j7);},_j8=function(_j9,_ja){return E(_j9)>=E(_ja);},_jb=function(_jc,_jd){var _je=E(_jc),_jf=E(_jd);return (_je>=_jf)?(_je!=_jf)?2:1:0;},_jg=function(_jh,_ji){var _jj=E(_jh),_jk=E(_ji);return (_jj>_jk)?E(_jj):E(_jk);},_jl=function(_jm,_jn){var _jo=E(_jm),_jp=E(_jn);return (_jo>_jp)?E(_jp):E(_jo);},_jq={_:0,a:_iY,b:_jb,c:_iZ,d:_j2,e:_j5,f:_j8,g:_jg,h:_jl},_jr=new T2(0,_iR,_jq),_js=function(_jt,_ju,_jv,_jw,_jx,_jy,_jz){var _jA=B(_7i(B(_7g(_jt)))),_jB=new T(function(){return B(A3(_6I,_jA,new T(function(){return B(A3(_7k,_jA,_ju,_jx));}),new T(function(){return B(A3(_7k,_jA,_jv,_jy));})));});return new F(function(){return A3(_6I,_jA,_jB,new T(function(){return B(A3(_7k,_jA,_jw,_jz));}));});},_jC=function(_jD,_jE,_jF,_jG){var _jH=B(_7g(_jD)),_jI=new T(function(){return B(A2(_7w,_jD,new T(function(){return B(_js(_jD,_jE,_jF,_jG,_jE,_jF,_jG));})));});return new T3(0,B(A3(_9b,_jH,_jE,_jI)),B(A3(_9b,_jH,_jF,_jI)),B(A3(_9b,_jH,_jG,_jI)));},_jJ=function(_jK,_jL,_jM,_jN,_jO,_jP,_jQ){var _jR=B(_7k(_jK));return new T3(0,B(A1(B(A1(_jR,_jL)),_jO)),B(A1(B(A1(_jR,_jM)),_jP)),B(A1(B(A1(_jR,_jN)),_jQ)));},_jS=function(_jT,_jU,_jV,_jW,_jX,_jY,_jZ){var _k0=B(_6I(_jT));return new T3(0,B(A1(B(A1(_k0,_jU)),_jX)),B(A1(B(A1(_k0,_jV)),_jY)),B(A1(B(A1(_k0,_jW)),_jZ)));},_k1=function(_k2,_k3){var _k4=new T(function(){return E(E(_k2).a);}),_k5=new T(function(){return B(A2(_gS,new T2(0,_k4,new T(function(){return E(E(_k2).b);})),_k3));}),_k6=new T(function(){var _k7=E(_k5),_k8=B(_jC(_k4,_k7.a,_k7.b,_k7.c));return new T3(0,E(_k8.a),E(_k8.b),E(_k8.c));}),_k9=new T(function(){var _ka=E(_k3),_kb=_ka.a,_kc=_ka.b,_kd=_ka.c,_ke=E(_k6),_kf=B(_7g(_k4)),_kg=new T(function(){return B(A2(_7w,_k4,new T(function(){var _kh=E(_k5),_ki=_kh.a,_kj=_kh.b,_kk=_kh.c;return B(_js(_k4,_ki,_kj,_kk,_ki,_kj,_kk));})));}),_kl=B(A3(_9b,_kf,new T(function(){return B(_7y(_k4,_kb,_kc,_kd));}),_kg)),_km=B(_7i(_kf)),_kn=B(_jJ(_km,_ke.a,_ke.b,_ke.c,_kl,_kl,_kl)),_ko=B(_6K(_km)),_kp=B(_jS(_km,_kb,_kc,_kd,B(A1(_ko,_kn.a)),B(A1(_ko,_kn.b)),B(A1(_ko,_kn.c))));return new T3(0,E(_kp.a),E(_kp.b),E(_kp.c));});return new T2(0,_k9,_k6);},_kq=function(_kr){return E(E(_kr).a);},_ks=function(_kt,_ku,_kv,_kw,_kx,_ky,_kz){var _kA=B(_js(_kt,_kx,_ky,_kz,_ku,_kv,_kw)),_kB=B(_7i(B(_7g(_kt)))),_kC=B(_jJ(_kB,_kx,_ky,_kz,_kA,_kA,_kA)),_kD=B(_6K(_kB));return new F(function(){return _jS(_kB,_ku,_kv,_kw,B(A1(_kD,_kC.a)),B(A1(_kD,_kC.b)),B(A1(_kD,_kC.c)));});},_kE=function(_kF){return E(E(_kF).a);},_kG=function(_kH,_kI,_kJ,_kK){var _kL=new T(function(){var _kM=E(_kK),_kN=E(_kJ),_kO=B(_ks(_kH,_kM.a,_kM.b,_kM.c,_kN.a,_kN.b,_kN.c));return new T3(0,E(_kO.a),E(_kO.b),E(_kO.c));}),_kP=new T(function(){return B(A2(_7w,_kH,new T(function(){var _kQ=E(_kL),_kR=_kQ.a,_kS=_kQ.b,_kT=_kQ.c;return B(_js(_kH,_kR,_kS,_kT,_kR,_kS,_kT));})));});if(!B(A3(_kE,B(_kq(_kI)),_kP,new T(function(){return B(A2(_91,B(_7i(B(_7g(_kH)))),_90));})))){var _kU=E(_kL),_kV=B(_jC(_kH,_kU.a,_kU.b,_kU.c)),_kW=B(A2(_7w,_kH,new T(function(){var _kX=E(_kK),_kY=_kX.a,_kZ=_kX.b,_l0=_kX.c;return B(_js(_kH,_kY,_kZ,_l0,_kY,_kZ,_l0));}))),_l1=B(_7k(new T(function(){return B(_7i(new T(function(){return B(_7g(_kH));})));})));return new T3(0,B(A1(B(A1(_l1,_kV.a)),_kW)),B(A1(B(A1(_l1,_kV.b)),_kW)),B(A1(B(A1(_l1,_kV.c)),_kW)));}else{var _l2=B(A2(_91,B(_7i(B(_7g(_kH)))),_90));return new T3(0,_l2,_l2,_l2);}},_l3=new T(function(){var _l4=eval("angleCount"),_l5=Number(_l4);return jsTrunc(_l5);}),_l6=new T(function(){return E(_l3);}),_l7=new T(function(){return B(unCStr(": empty list"));}),_l8=new T(function(){return B(unCStr("Prelude."));}),_l9=function(_la){return new F(function(){return err(B(_f(_l8,new T(function(){return B(_f(_la,_l7));},1))));});},_lb=new T(function(){return B(unCStr("head"));}),_lc=new T(function(){return B(_l9(_lb));}),_ld=function(_le,_lf,_lg){var _lh=E(_le);if(!_lh._){return __Z;}else{var _li=E(_lf);if(!_li._){return __Z;}else{var _lj=_li.a,_lk=E(_lg);if(!_lk._){return __Z;}else{var _ll=E(_lk.a),_lm=_ll.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_lh.a),E(_lj),E(_lm));}),new T2(1,new T(function(){return new T3(0,E(_lj),E(_lm),E(_ll.b));}),_o)),new T(function(){return B(_ld(_lh.b,_li.b,_lk.b));},1));});}}}},_ln=new T(function(){return B(unCStr("tail"));}),_lo=new T(function(){return B(_l9(_ln));}),_lp=function(_lq,_lr){var _ls=E(_lq);if(!_ls._){return __Z;}else{var _lt=E(_lr);return (_lt._==0)?__Z:new T2(1,new T2(0,_ls.a,_lt.a),new T(function(){return B(_lp(_ls.b,_lt.b));}));}},_lu=function(_lv,_lw){var _lx=E(_lv);if(!_lx._){return __Z;}else{var _ly=E(_lw);if(!_ly._){return __Z;}else{var _lz=E(_lx.a),_lA=_lz.b,_lB=E(_ly.a).b,_lC=new T(function(){var _lD=new T(function(){return B(_lp(_lB,new T(function(){var _lE=E(_lB);if(!_lE._){return E(_lo);}else{return E(_lE.b);}},1)));},1);return B(_ld(_lA,new T(function(){var _lF=E(_lA);if(!_lF._){return E(_lo);}else{return E(_lF.b);}},1),_lD));});return new F(function(){return _f(new T2(1,new T(function(){var _lG=E(_lA);if(!_lG._){return E(_lc);}else{var _lH=E(_lB);if(!_lH._){return E(_lc);}else{return new T3(0,E(_lz.a),E(_lG.a),E(_lH.a));}}}),_lC),new T(function(){return B(_lu(_lx.b,_ly.b));},1));});}}},_lI=new T(function(){return E(_l6)-1;}),_lJ=new T1(0,1),_lK=function(_lL,_lM){var _lN=E(_lM),_lO=new T(function(){var _lP=B(_7i(_lL)),_lQ=B(_lK(_lL,B(A3(_6I,_lP,_lN,new T(function(){return B(A2(_91,_lP,_lJ));})))));return new T2(1,_lQ.a,_lQ.b);});return new T2(0,_lN,_lO);},_lR=function(_lS){return E(E(_lS).d);},_lT=new T1(0,2),_lU=function(_lV,_lW){var _lX=E(_lW);if(!_lX._){return __Z;}else{var _lY=_lX.a;return (!B(A1(_lV,_lY)))?__Z:new T2(1,_lY,new T(function(){return B(_lU(_lV,_lX.b));}));}},_lZ=function(_m0,_m1,_m2,_m3){var _m4=B(_lK(_m1,_m2)),_m5=new T(function(){var _m6=B(_7i(_m1)),_m7=new T(function(){return B(A3(_9b,_m1,new T(function(){return B(A2(_91,_m6,_lJ));}),new T(function(){return B(A2(_91,_m6,_lT));})));});return B(A3(_6I,_m6,_m3,_m7));});return new F(function(){return _lU(function(_m8){return new F(function(){return A3(_lR,_m0,_m8,_m5);});},new T2(1,_m4.a,_m4.b));});},_m9=new T(function(){return B(_lZ(_jq,_ip,_hm,_lI));}),_ma=function(_mb,_mc){while(1){var _md=E(_mb);if(!_md._){return E(_mc);}else{_mb=_md.b;_mc=_md.a;continue;}}},_me=new T(function(){return B(unCStr("last"));}),_mf=new T(function(){return B(_l9(_me));}),_mg=function(_mh){return new F(function(){return _ma(_mh,_mf);});},_mi=function(_mj){return new F(function(){return _mg(E(_mj).b);});},_mk=function(_ml,_mm){var _mn=E(_mm);return (_mn._==0)?__Z:new T2(1,new T(function(){return B(A1(_ml,_mn.a));}),new T(function(){return B(_mk(_ml,_mn.b));}));},_mo=new T(function(){var _mp=eval("proceedCount"),_mq=Number(_mp);return jsTrunc(_mq);}),_mr=new T(function(){return E(_mo);}),_ms=1,_mt=new T(function(){return B(_lZ(_jq,_ip,_ms,_mr));}),_mu=function(_mv,_mw,_mx,_my,_mz,_mA,_mB,_mC,_mD,_mE,_mF,_mG,_mH,_mI,_mJ,_mK){var _mL=new T(function(){var _mM=new T(function(){var _mN=E(_mE),_mO=E(_mI),_mP=E(_mH),_mQ=E(_mF),_mR=E(_mG),_mS=E(_mD);return new T3(0,_mN*_mO-_mP*_mQ,_mQ*_mR-_mO*_mS,_mS*_mP-_mR*_mN);}),_mT=function(_mU){var _mV=new T(function(){var _mW=E(_mU)/E(_l6);return (_mW+_mW)*3.141592653589793;}),_mX=new T(function(){return B(A1(_mv,_mV));}),_mY=new T(function(){var _mZ=new T(function(){var _n0=E(_mX)/E(_mr);return new T3(0,E(_n0),E(_n0),E(_n0));}),_n1=function(_n2,_n3){var _n4=E(_n2);if(!_n4._){return new T2(0,_o,_n3);}else{var _n5=new T(function(){var _n6=B(_k1(_jr,new T(function(){var _n7=E(_n3),_n8=E(_n7.a),_n9=E(_n7.b),_na=E(_mZ);return new T3(0,E(_n8.a)+E(_n9.a)*E(_na.a),E(_n8.b)+E(_n9.b)*E(_na.b),E(_n8.c)+E(_n9.c)*E(_na.c));}))),_nb=_n6.a;return new T2(0,new T(function(){var _nc=E(_mX),_nd=E(_mV);return new T3(0,E(_nb),E(new T2(0,E(_n4.a)/E(_mr),E(_nc))),E(_nd));}),new T2(0,_nb,new T(function(){var _ne=E(_n6.b),_nf=E(E(_n3).b),_ng=B(_ks(_iR,_nf.a,_nf.b,_nf.c,_ne.a,_ne.b,_ne.c)),_nh=B(_jC(_iR,_ng.a,_ng.b,_ng.c));return new T3(0,E(_nh.a),E(_nh.b),E(_nh.c));})));}),_ni=new T(function(){var _nj=B(_n1(_n4.b,new T(function(){return E(E(_n5).b);})));return new T2(0,_nj.a,_nj.b);});return new T2(0,new T2(1,new T(function(){return E(E(_n5).a);}),new T(function(){return E(E(_ni).a);})),new T(function(){return E(E(_ni).b);}));}},_nk=function(_nl,_nm,_nn,_no,_np){var _nq=E(_nl);if(!_nq._){return new T2(0,_o,new T2(0,new T3(0,E(_nm),E(_nn),E(_no)),_np));}else{var _nr=new T(function(){var _ns=B(_k1(_jr,new T(function(){var _nt=E(_np),_nu=E(_mZ);return new T3(0,E(_nm)+E(_nt.a)*E(_nu.a),E(_nn)+E(_nt.b)*E(_nu.b),E(_no)+E(_nt.c)*E(_nu.c));}))),_nv=_ns.a;return new T2(0,new T(function(){var _nw=E(_mX),_nx=E(_mV);return new T3(0,E(_nv),E(new T2(0,E(_nq.a)/E(_mr),E(_nw))),E(_nx));}),new T2(0,_nv,new T(function(){var _ny=E(_ns.b),_nz=E(_np),_nA=B(_ks(_iR,_nz.a,_nz.b,_nz.c,_ny.a,_ny.b,_ny.c)),_nB=B(_jC(_iR,_nA.a,_nA.b,_nA.c));return new T3(0,E(_nB.a),E(_nB.b),E(_nB.c));})));}),_nC=new T(function(){var _nD=B(_n1(_nq.b,new T(function(){return E(E(_nr).b);})));return new T2(0,_nD.a,_nD.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nr).a);}),new T(function(){return E(E(_nC).a);})),new T(function(){return E(E(_nC).b);}));}};return E(B(_nk(_mt,_my,_mz,_mA,new T(function(){var _nE=E(_mM),_nF=E(_mV)+_mB,_nG=Math.cos(_nF),_nH=Math.sin(_nF);return new T3(0,E(_mD)*_nG+E(_nE.a)*_nH,E(_mE)*_nG+E(_nE.b)*_nH,E(_mF)*_nG+E(_nE.c)*_nH);}))).a);});return new T2(0,new T(function(){var _nI=E(_mX),_nJ=E(_mV);return new T3(0,E(new T3(0,E(_my),E(_mz),E(_mA))),E(new T2(0,E(_hm),E(_nI))),E(_nJ));}),_mY);};return B(_mk(_mT,_m9));}),_nK=new T(function(){var _nL=new T(function(){var _nM=B(_f(_mL,new T2(1,new T(function(){var _nN=E(_mL);if(!_nN._){return E(_lc);}else{return E(_nN.a);}}),_o)));if(!_nM._){return E(_lo);}else{return E(_nM.b);}},1);return B(_lu(_mL,_nL));});return new T2(0,_nK,new T(function(){return B(_mk(_mi,_mL));}));},_nO=function(_nP,_nQ,_nR,_nS,_nT,_nU,_nV,_nW,_nX,_nY,_nZ,_o0,_o1,_o2,_o3,_o4,_o5){var _o6=B(_k1(_jr,new T3(0,E(_nS),E(_nT),E(_nU)))),_o7=_o6.b,_o8=E(_o6.a),_o9=B(_kG(_iR,_jq,_o7,new T3(0,E(_nW),E(_nX),E(_nY)))),_oa=E(_o7),_ob=_oa.a,_oc=_oa.b,_od=_oa.c,_oe=B(_ks(_iR,_o0,_o1,_o2,_ob,_oc,_od)),_of=B(_jC(_iR,_oe.a,_oe.b,_oe.c)),_og=_of.a,_oh=_of.b,_oi=_of.c,_oj=E(_nV),_ok=new T2(0,E(new T3(0,E(_o9.a),E(_o9.b),E(_o9.c))),E(_nZ)),_ol=B(_mu(_nP,_nQ,_nR,_o8.a,_o8.b,_o8.c,_oj,_ok,_og,_oh,_oi,_ob,_oc,_od,_o4,_o5));return {_:0,a:_nP,b:_nQ,c:_nR,d:new T2(0,E(_o8),E(_oj)),e:_ok,f:new T3(0,E(_og),E(_oh),E(_oi)),g:_oa,h:E(_ol.a),i:E(_ol.b)};},_om=new T(function(){return 6.283185307179586/E(_l6);}),_on= -1,_oo=0.5,_op=new T3(0,E(_hm),E(_oo),E(_on)),_oq=function(_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD){var _oE=function(_oF){var _oG=E(_om),_oH=2+_oF|0,_oI=_oH-1|0,_oJ=(2+_oF)*(1+_oF),_oK=E(_m9);if(!_oK._){return _oG*0;}else{var _oL=_oK.a,_oM=_oK.b,_oN=B(A1(_or,new T(function(){return 6.283185307179586*E(_oL)/E(_l6);}))),_oO=B(A1(_or,new T(function(){return 6.283185307179586*(E(_oL)+1)/E(_l6);})));if(_oN!=_oO){if(_oH>=0){var _oP=E(_oH);if(!_oP){var _oQ=function(_oR,_oS){while(1){var _oT=B((function(_oU,_oV){var _oW=E(_oU);if(!_oW._){return E(_oV);}else{var _oX=_oW.a,_oY=_oW.b,_oZ=B(A1(_or,new T(function(){return 6.283185307179586*E(_oX)/E(_l6);}))),_p0=B(A1(_or,new T(function(){return 6.283185307179586*(E(_oX)+1)/E(_l6);})));if(_oZ!=_p0){var _p1=_oV+0/(_oZ-_p0)/_oJ;_oR=_oY;_oS=_p1;return __continue;}else{if(_oI>=0){var _p2=E(_oI);if(!_p2){var _p1=_oV+_oH/_oJ;_oR=_oY;_oS=_p1;return __continue;}else{var _p1=_oV+_oH*B(_hy(_oZ,_p2))/_oJ;_oR=_oY;_oS=_p1;return __continue;}}else{return E(_hp);}}}})(_oR,_oS));if(_oT!=__continue){return _oT;}}};return _oG*B(_oQ(_oM,0/(_oN-_oO)/_oJ));}else{var _p3=function(_p4,_p5){while(1){var _p6=B((function(_p7,_p8){var _p9=E(_p7);if(!_p9._){return E(_p8);}else{var _pa=_p9.a,_pb=_p9.b,_pc=B(A1(_or,new T(function(){return 6.283185307179586*E(_pa)/E(_l6);}))),_pd=B(A1(_or,new T(function(){return 6.283185307179586*(E(_pa)+1)/E(_l6);})));if(_pc!=_pd){if(_oP>=0){var _pe=_p8+(B(_hy(_pc,_oP))-B(_hy(_pd,_oP)))/(_pc-_pd)/_oJ;_p4=_pb;_p5=_pe;return __continue;}else{return E(_hp);}}else{if(_oI>=0){var _pf=E(_oI);if(!_pf){var _pe=_p8+_oH/_oJ;_p4=_pb;_p5=_pe;return __continue;}else{var _pe=_p8+_oH*B(_hy(_pc,_pf))/_oJ;_p4=_pb;_p5=_pe;return __continue;}}else{return E(_hp);}}}})(_p4,_p5));if(_p6!=__continue){return _p6;}}};return _oG*B(_p3(_oM,(B(_hy(_oN,_oP))-B(_hy(_oO,_oP)))/(_oN-_oO)/_oJ));}}else{return E(_hp);}}else{if(_oI>=0){var _pg=E(_oI);if(!_pg){var _ph=function(_pi,_pj){while(1){var _pk=B((function(_pl,_pm){var _pn=E(_pl);if(!_pn._){return E(_pm);}else{var _po=_pn.a,_pp=_pn.b,_pq=B(A1(_or,new T(function(){return 6.283185307179586*E(_po)/E(_l6);}))),_pr=B(A1(_or,new T(function(){return 6.283185307179586*(E(_po)+1)/E(_l6);})));if(_pq!=_pr){if(_oH>=0){var _ps=E(_oH);if(!_ps){var _pt=_pm+0/(_pq-_pr)/_oJ;_pi=_pp;_pj=_pt;return __continue;}else{var _pt=_pm+(B(_hy(_pq,_ps))-B(_hy(_pr,_ps)))/(_pq-_pr)/_oJ;_pi=_pp;_pj=_pt;return __continue;}}else{return E(_hp);}}else{var _pt=_pm+_oH/_oJ;_pi=_pp;_pj=_pt;return __continue;}}})(_pi,_pj));if(_pk!=__continue){return _pk;}}};return _oG*B(_ph(_oM,_oH/_oJ));}else{var _pu=function(_pv,_pw){while(1){var _px=B((function(_py,_pz){var _pA=E(_py);if(!_pA._){return E(_pz);}else{var _pB=_pA.a,_pC=_pA.b,_pD=B(A1(_or,new T(function(){return 6.283185307179586*E(_pB)/E(_l6);}))),_pE=B(A1(_or,new T(function(){return 6.283185307179586*(E(_pB)+1)/E(_l6);})));if(_pD!=_pE){if(_oH>=0){var _pF=E(_oH);if(!_pF){var _pG=_pz+0/(_pD-_pE)/_oJ;_pv=_pC;_pw=_pG;return __continue;}else{var _pG=_pz+(B(_hy(_pD,_pF))-B(_hy(_pE,_pF)))/(_pD-_pE)/_oJ;_pv=_pC;_pw=_pG;return __continue;}}else{return E(_hp);}}else{if(_pg>=0){var _pG=_pz+_oH*B(_hy(_pD,_pg))/_oJ;_pv=_pC;_pw=_pG;return __continue;}else{return E(_hp);}}}})(_pv,_pw));if(_px!=__continue){return _px;}}};return _oG*B(_pu(_oM,_oH*B(_hy(_oN,_pg))/_oJ));}}else{return E(_hp);}}}},_pH=1/(B(_oE(1))*_os);return new F(function(){return _nO(_or,_op,new T2(0,E(new T3(0,E(_pH),E(_pH),E(_pH))),1/(B(_oE(3))*_os)),_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD,_hn,_o,_o);});},_pI=0,_pJ= -0.2,_pK=0.5,_pL= -0.8,_pM=0.2,_pN=function(_pO){return E(_pM);},_pP=1,_pQ=new T(function(){var _pR=B(_oq(_pN,1.2,_pL,_pK,_pI,_pI,_pJ,_pI,_pP,_pI,_pI,_pI,_pP));return {_:0,a:E(_pR.a),b:E(_pR.b),c:E(_pR.c),d:E(_pR.d),e:E(_pR.e),f:E(_pR.f),g:E(_pR.g),h:E(_pR.h),i:E(_pR.i)};}),_pS=0,_pT= -0.1,_pU=1.3,_pV=function(_pW){var _pX=I_decodeDouble(_pW);return new T2(0,new T1(1,_pX.b),_pX.a);},_pY=function(_pZ){return new T1(0,_pZ);},_q0=function(_q1){var _q2=hs_intToInt64(2147483647),_q3=hs_leInt64(_q1,_q2);if(!_q3){return new T1(1,I_fromInt64(_q1));}else{var _q4=hs_intToInt64( -2147483648),_q5=hs_geInt64(_q1,_q4);if(!_q5){return new T1(1,I_fromInt64(_q1));}else{var _q6=hs_int64ToInt(_q1);return new F(function(){return _pY(_q6);});}}},_q7=new T(function(){var _q8=newByteArr(256),_q9=_q8,_=_q9["v"]["i8"][0]=8,_qa=function(_qb,_qc,_qd,_){while(1){if(_qd>=256){if(_qb>=256){return E(_);}else{var _qe=imul(2,_qb)|0,_qf=_qc+1|0,_qg=_qb;_qb=_qe;_qc=_qf;_qd=_qg;continue;}}else{var _=_q9["v"]["i8"][_qd]=_qc,_qg=_qd+_qb|0;_qd=_qg;continue;}}},_=B(_qa(2,0,1,_));return _q9;}),_qh=function(_qi,_qj){var _qk=hs_int64ToInt(_qi),_ql=E(_q7),_qm=_ql["v"]["i8"][(255&_qk>>>0)>>>0&4294967295];if(_qj>_qm){if(_qm>=8){var _qn=hs_uncheckedIShiftRA64(_qi,8),_qo=function(_qp,_qq){while(1){var _qr=B((function(_qs,_qt){var _qu=hs_int64ToInt(_qs),_qv=_ql["v"]["i8"][(255&_qu>>>0)>>>0&4294967295];if(_qt>_qv){if(_qv>=8){var _qw=hs_uncheckedIShiftRA64(_qs,8),_qx=_qt-8|0;_qp=_qw;_qq=_qx;return __continue;}else{return new T2(0,new T(function(){var _qy=hs_uncheckedIShiftRA64(_qs,_qv);return B(_q0(_qy));}),_qt-_qv|0);}}else{return new T2(0,new T(function(){var _qz=hs_uncheckedIShiftRA64(_qs,_qt);return B(_q0(_qz));}),0);}})(_qp,_qq));if(_qr!=__continue){return _qr;}}};return new F(function(){return _qo(_qn,_qj-8|0);});}else{return new T2(0,new T(function(){var _qA=hs_uncheckedIShiftRA64(_qi,_qm);return B(_q0(_qA));}),_qj-_qm|0);}}else{return new T2(0,new T(function(){var _qB=hs_uncheckedIShiftRA64(_qi,_qj);return B(_q0(_qB));}),0);}},_qC=function(_qD){var _qE=hs_intToInt64(_qD);return E(_qE);},_qF=function(_qG){var _qH=E(_qG);if(!_qH._){return new F(function(){return _qC(_qH.a);});}else{return new F(function(){return I_toInt64(_qH.a);});}},_qI=function(_qJ){return I_toInt(_qJ)>>>0;},_qK=function(_qL){var _qM=E(_qL);if(!_qM._){return _qM.a>>>0;}else{return new F(function(){return _qI(_qM.a);});}},_qN=function(_qO){var _qP=B(_pV(_qO)),_qQ=_qP.a,_qR=_qP.b;if(_qR<0){var _qS=function(_qT){if(!_qT){return new T2(0,E(_qQ),B(_3u(_1M, -_qR)));}else{var _qU=B(_qh(B(_qF(_qQ)), -_qR));return new T2(0,E(_qU.a),B(_3u(_1M,_qU.b)));}};if(!((B(_qK(_qQ))&1)>>>0)){return new F(function(){return _qS(1);});}else{return new F(function(){return _qS(0);});}}else{return new T2(0,B(_3u(_qQ,_qR)),_1M);}},_qV=function(_qW){var _qX=B(_qN(E(_qW)));return new T2(0,E(_qX.a),E(_qX.b));},_qY=new T3(0,_il,_jq,_qV),_qZ=function(_r0){return E(E(_r0).a);},_r1=function(_r2){return E(E(_r2).a);},_r3=function(_r4,_r5){if(_r4<=_r5){var _r6=function(_r7){return new T2(1,_r7,new T(function(){if(_r7!=_r5){return B(_r6(_r7+1|0));}else{return __Z;}}));};return new F(function(){return _r6(_r4);});}else{return __Z;}},_r8=function(_r9){return new F(function(){return _r3(E(_r9),2147483647);});},_ra=function(_rb,_rc,_rd){if(_rd<=_rc){var _re=new T(function(){var _rf=_rc-_rb|0,_rg=function(_rh){return (_rh>=(_rd-_rf|0))?new T2(1,_rh,new T(function(){return B(_rg(_rh+_rf|0));})):new T2(1,_rh,_o);};return B(_rg(_rc));});return new T2(1,_rb,_re);}else{return (_rd<=_rb)?new T2(1,_rb,_o):__Z;}},_ri=function(_rj,_rk,_rl){if(_rl>=_rk){var _rm=new T(function(){var _rn=_rk-_rj|0,_ro=function(_rp){return (_rp<=(_rl-_rn|0))?new T2(1,_rp,new T(function(){return B(_ro(_rp+_rn|0));})):new T2(1,_rp,_o);};return B(_ro(_rk));});return new T2(1,_rj,_rm);}else{return (_rl>=_rj)?new T2(1,_rj,_o):__Z;}},_rq=function(_rr,_rs){if(_rs<_rr){return new F(function(){return _ra(_rr,_rs, -2147483648);});}else{return new F(function(){return _ri(_rr,_rs,2147483647);});}},_rt=function(_ru,_rv){return new F(function(){return _rq(E(_ru),E(_rv));});},_rw=function(_rx,_ry,_rz){if(_ry<_rx){return new F(function(){return _ra(_rx,_ry,_rz);});}else{return new F(function(){return _ri(_rx,_ry,_rz);});}},_rA=function(_rB,_rC,_rD){return new F(function(){return _rw(E(_rB),E(_rC),E(_rD));});},_rE=function(_rF,_rG){return new F(function(){return _r3(E(_rF),E(_rG));});},_rH=function(_rI){return E(_rI);},_rJ=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_rK=new T(function(){return B(err(_rJ));}),_rL=function(_rM){var _rN=E(_rM);return (_rN==( -2147483648))?E(_rK):_rN-1|0;},_rO=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_rP=new T(function(){return B(err(_rO));}),_rQ=function(_rR){var _rS=E(_rR);return (_rS==2147483647)?E(_rP):_rS+1|0;},_rT={_:0,a:_rQ,b:_rL,c:_rH,d:_rH,e:_r8,f:_rt,g:_rE,h:_rA},_rU=function(_rV,_rW){if(_rV<=0){if(_rV>=0){return new F(function(){return quot(_rV,_rW);});}else{if(_rW<=0){return new F(function(){return quot(_rV,_rW);});}else{return quot(_rV+1|0,_rW)-1|0;}}}else{if(_rW>=0){if(_rV>=0){return new F(function(){return quot(_rV,_rW);});}else{if(_rW<=0){return new F(function(){return quot(_rV,_rW);});}else{return quot(_rV+1|0,_rW)-1|0;}}}else{return quot(_rV-1|0,_rW)-1|0;}}},_rX=0,_rY=new T(function(){return B(_2R(_rX));}),_rZ=new T(function(){return die(_rY);}),_s0=function(_s1,_s2){var _s3=E(_s2);switch(_s3){case  -1:var _s4=E(_s1);if(_s4==( -2147483648)){return E(_rZ);}else{return new F(function(){return _rU(_s4, -1);});}break;case 0:return E(_2V);default:return new F(function(){return _rU(_s1,_s3);});}},_s5=function(_s6,_s7){return new F(function(){return _s0(E(_s6),E(_s7));});},_s8=0,_s9=new T2(0,_rZ,_s8),_sa=function(_sb,_sc){var _sd=E(_sb),_se=E(_sc);switch(_se){case  -1:var _sf=E(_sd);if(_sf==( -2147483648)){return E(_s9);}else{if(_sf<=0){if(_sf>=0){var _sg=quotRemI(_sf, -1);return new T2(0,_sg.a,_sg.b);}else{var _sh=quotRemI(_sf, -1);return new T2(0,_sh.a,_sh.b);}}else{var _si=quotRemI(_sf-1|0, -1);return new T2(0,_si.a-1|0,(_si.b+( -1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_sd<=0){if(_sd>=0){var _sj=quotRemI(_sd,_se);return new T2(0,_sj.a,_sj.b);}else{if(_se<=0){var _sk=quotRemI(_sd,_se);return new T2(0,_sk.a,_sk.b);}else{var _sl=quotRemI(_sd+1|0,_se);return new T2(0,_sl.a-1|0,(_sl.b+_se|0)-1|0);}}}else{if(_se>=0){if(_sd>=0){var _sm=quotRemI(_sd,_se);return new T2(0,_sm.a,_sm.b);}else{if(_se<=0){var _sn=quotRemI(_sd,_se);return new T2(0,_sn.a,_sn.b);}else{var _so=quotRemI(_sd+1|0,_se);return new T2(0,_so.a-1|0,(_so.b+_se|0)-1|0);}}}else{var _sp=quotRemI(_sd-1|0,_se);return new T2(0,_sp.a-1|0,(_sp.b+_se|0)+1|0);}}}},_sq=function(_sr,_ss){var _st=_sr%_ss;if(_sr<=0){if(_sr>=0){return E(_st);}else{if(_ss<=0){return E(_st);}else{var _su=E(_st);return (_su==0)?0:_su+_ss|0;}}}else{if(_ss>=0){if(_sr>=0){return E(_st);}else{if(_ss<=0){return E(_st);}else{var _sv=E(_st);return (_sv==0)?0:_sv+_ss|0;}}}else{var _sw=E(_st);return (_sw==0)?0:_sw+_ss|0;}}},_sx=function(_sy,_sz){var _sA=E(_sz);switch(_sA){case  -1:return E(_s8);case 0:return E(_2V);default:return new F(function(){return _sq(E(_sy),_sA);});}},_sB=function(_sC,_sD){var _sE=E(_sC),_sF=E(_sD);switch(_sF){case  -1:var _sG=E(_sE);if(_sG==( -2147483648)){return E(_rZ);}else{return new F(function(){return quot(_sG, -1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_sE,_sF);});}},_sH=function(_sI,_sJ){var _sK=E(_sI),_sL=E(_sJ);switch(_sL){case  -1:var _sM=E(_sK);if(_sM==( -2147483648)){return E(_s9);}else{var _sN=quotRemI(_sM, -1);return new T2(0,_sN.a,_sN.b);}break;case 0:return E(_2V);default:var _sO=quotRemI(_sK,_sL);return new T2(0,_sO.a,_sO.b);}},_sP=function(_sQ,_sR){var _sS=E(_sR);switch(_sS){case  -1:return E(_s8);case 0:return E(_2V);default:return E(_sQ)%_sS;}},_sT=function(_sU){return new F(function(){return _pY(E(_sU));});},_sV=function(_sW){return new T2(0,E(B(_pY(E(_sW)))),E(_lJ));},_sX=function(_sY,_sZ){return imul(E(_sY),E(_sZ))|0;},_t0=function(_t1,_t2){return E(_t1)+E(_t2)|0;},_t3=function(_t4,_t5){return E(_t4)-E(_t5)|0;},_t6=function(_t7){var _t8=E(_t7);return (_t8<0)? -_t8:E(_t8);},_t9=function(_ta){return new F(function(){return _38(_ta);});},_tb=function(_tc){return  -E(_tc);},_td= -1,_te=0,_tf=1,_tg=function(_th){var _ti=E(_th);return (_ti>=0)?(E(_ti)==0)?E(_te):E(_tf):E(_td);},_tj={_:0,a:_t0,b:_t3,c:_sX,d:_tb,e:_t6,f:_tg,g:_t9},_tk=function(_tl,_tm){return E(_tl)==E(_tm);},_tn=function(_to,_tp){return E(_to)!=E(_tp);},_tq=new T2(0,_tk,_tn),_tr=function(_ts,_tt){var _tu=E(_ts),_tv=E(_tt);return (_tu>_tv)?E(_tu):E(_tv);},_tw=function(_tx,_ty){var _tz=E(_tx),_tA=E(_ty);return (_tz>_tA)?E(_tA):E(_tz);},_tB=function(_tC,_tD){return (_tC>=_tD)?(_tC!=_tD)?2:1:0;},_tE=function(_tF,_tG){return new F(function(){return _tB(E(_tF),E(_tG));});},_tH=function(_tI,_tJ){return E(_tI)>=E(_tJ);},_tK=function(_tL,_tM){return E(_tL)>E(_tM);},_tN=function(_tO,_tP){return E(_tO)<=E(_tP);},_tQ=function(_tR,_tS){return E(_tR)<E(_tS);},_tT={_:0,a:_tq,b:_tE,c:_tQ,d:_tN,e:_tK,f:_tH,g:_tr,h:_tw},_tU=new T3(0,_tj,_tT,_sV),_tV={_:0,a:_tU,b:_rT,c:_sB,d:_sP,e:_s5,f:_sx,g:_sH,h:_sa,i:_sT},_tW=new T1(0,2),_tX=function(_tY,_tZ){while(1){var _u0=E(_tY);if(!_u0._){var _u1=_u0.a,_u2=E(_tZ);if(!_u2._){var _u3=_u2.a;if(!(imul(_u1,_u3)|0)){return new T1(0,imul(_u1,_u3)|0);}else{_tY=new T1(1,I_fromInt(_u1));_tZ=new T1(1,I_fromInt(_u3));continue;}}else{_tY=new T1(1,I_fromInt(_u1));_tZ=_u2;continue;}}else{var _u4=E(_tZ);if(!_u4._){_tY=_u0;_tZ=new T1(1,I_fromInt(_u4.a));continue;}else{return new T1(1,I_mul(_u0.a,_u4.a));}}}},_u5=function(_u6,_u7,_u8){while(1){if(!(_u7%2)){var _u9=B(_tX(_u6,_u6)),_ua=quot(_u7,2);_u6=_u9;_u7=_ua;continue;}else{var _ub=E(_u7);if(_ub==1){return new F(function(){return _tX(_u6,_u8);});}else{var _u9=B(_tX(_u6,_u6)),_uc=B(_tX(_u6,_u8));_u6=_u9;_u7=quot(_ub-1|0,2);_u8=_uc;continue;}}}},_ud=function(_ue,_uf){while(1){if(!(_uf%2)){var _ug=B(_tX(_ue,_ue)),_uh=quot(_uf,2);_ue=_ug;_uf=_uh;continue;}else{var _ui=E(_uf);if(_ui==1){return E(_ue);}else{return new F(function(){return _u5(B(_tX(_ue,_ue)),quot(_ui-1|0,2),_ue);});}}}},_uj=function(_uk){return E(E(_uk).b);},_ul=function(_um){return E(E(_um).c);},_un=new T1(0,0),_uo=function(_up){return E(E(_up).d);},_uq=function(_ur,_us){var _ut=B(_qZ(_ur)),_uu=new T(function(){return B(_r1(_ut));}),_uv=new T(function(){return B(A3(_uo,_ur,_us,new T(function(){return B(A2(_91,_uu,_lT));})));});return new F(function(){return A3(_kE,B(_kq(B(_uj(_ut)))),_uv,new T(function(){return B(A2(_91,_uu,_un));}));});},_uw=new T(function(){return B(unCStr("Negative exponent"));}),_ux=new T(function(){return B(err(_uw));}),_uy=function(_uz){return E(E(_uz).c);},_uA=function(_uB,_uC,_uD,_uE){var _uF=B(_qZ(_uC)),_uG=new T(function(){return B(_r1(_uF));}),_uH=B(_uj(_uF));if(!B(A3(_ul,_uH,_uE,new T(function(){return B(A2(_91,_uG,_un));})))){if(!B(A3(_kE,B(_kq(_uH)),_uE,new T(function(){return B(A2(_91,_uG,_un));})))){var _uI=new T(function(){return B(A2(_91,_uG,_lT));}),_uJ=new T(function(){return B(A2(_91,_uG,_lJ));}),_uK=B(_kq(_uH)),_uL=function(_uM,_uN,_uO){while(1){var _uP=B((function(_uQ,_uR,_uS){if(!B(_uq(_uC,_uR))){if(!B(A3(_kE,_uK,_uR,_uJ))){var _uT=new T(function(){return B(A3(_uy,_uC,new T(function(){return B(A3(_7m,_uG,_uR,_uJ));}),_uI));});_uM=new T(function(){return B(A3(_7k,_uB,_uQ,_uQ));});_uN=_uT;_uO=new T(function(){return B(A3(_7k,_uB,_uQ,_uS));});return __continue;}else{return new F(function(){return A3(_7k,_uB,_uQ,_uS);});}}else{var _uU=_uS;_uM=new T(function(){return B(A3(_7k,_uB,_uQ,_uQ));});_uN=new T(function(){return B(A3(_uy,_uC,_uR,_uI));});_uO=_uU;return __continue;}})(_uM,_uN,_uO));if(_uP!=__continue){return _uP;}}},_uV=function(_uW,_uX){while(1){var _uY=B((function(_uZ,_v0){if(!B(_uq(_uC,_v0))){if(!B(A3(_kE,_uK,_v0,_uJ))){var _v1=new T(function(){return B(A3(_uy,_uC,new T(function(){return B(A3(_7m,_uG,_v0,_uJ));}),_uI));});return new F(function(){return _uL(new T(function(){return B(A3(_7k,_uB,_uZ,_uZ));}),_v1,_uZ);});}else{return E(_uZ);}}else{_uW=new T(function(){return B(A3(_7k,_uB,_uZ,_uZ));});_uX=new T(function(){return B(A3(_uy,_uC,_v0,_uI));});return __continue;}})(_uW,_uX));if(_uY!=__continue){return _uY;}}};return new F(function(){return _uV(_uD,_uE);});}else{return new F(function(){return A2(_91,_uB,_lJ);});}}else{return E(_ux);}},_v2=new T(function(){return B(err(_uw));}),_v3=function(_v4,_v5){var _v6=B(_pV(_v5)),_v7=_v6.a,_v8=_v6.b,_v9=new T(function(){return B(_r1(new T(function(){return B(_qZ(_v4));})));});if(_v8<0){var _va= -_v8;if(_va>=0){var _vb=E(_va);if(!_vb){var _vc=E(_lJ);}else{var _vc=B(_ud(_tW,_vb));}if(!B(_30(_vc,_3t))){var _vd=B(_3k(_v7,_vc));return new T2(0,new T(function(){return B(A2(_91,_v9,_vd.a));}),new T(function(){return B(_2W(_vd.b,_v8));}));}else{return E(_2V);}}else{return E(_v2);}}else{var _ve=new T(function(){var _vf=new T(function(){return B(_uA(_v9,_tV,new T(function(){return B(A2(_91,_v9,_tW));}),_v8));});return B(A3(_7k,_v9,new T(function(){return B(A2(_91,_v9,_v7));}),_vf));});return new T2(0,_ve,_6i);}},_vg=function(_vh,_vi){var _vj=B(_v3(_vh,E(_vi))),_vk=_vj.a;if(E(_vj.b)<=0){return E(_vk);}else{var _vl=B(_r1(B(_qZ(_vh))));return new F(function(){return A3(_6I,_vl,_vk,new T(function(){return B(A2(_91,_vl,_1M));}));});}},_vm=function(_vn,_vo){var _vp=B(_v3(_vn,E(_vo))),_vq=_vp.a;if(E(_vp.b)>=0){return E(_vq);}else{var _vr=B(_r1(B(_qZ(_vn))));return new F(function(){return A3(_7m,_vr,_vq,new T(function(){return B(A2(_91,_vr,_1M));}));});}},_vs=function(_vt,_vu){var _vv=B(_v3(_vt,E(_vu)));return new T2(0,_vv.a,_vv.b);},_vw=function(_vx,_vy){var _vz=B(_v3(_vx,_vy)),_vA=_vz.a,_vB=E(_vz.b),_vC=new T(function(){var _vD=B(_r1(B(_qZ(_vx))));if(_vB>=0){return B(A3(_6I,_vD,_vA,new T(function(){return B(A2(_91,_vD,_1M));})));}else{return B(A3(_7m,_vD,_vA,new T(function(){return B(A2(_91,_vD,_1M));})));}}),_vE=function(_vF){var _vG=_vF-0.5;return (_vG>=0)?(E(_vG)==0)?(!B(_uq(_vx,_vA)))?E(_vC):E(_vA):E(_vC):E(_vA);},_vH=E(_vB);if(!_vH){return new F(function(){return _vE(0);});}else{if(_vH<=0){var _vI= -_vH-0.5;return (_vI>=0)?(E(_vI)==0)?(!B(_uq(_vx,_vA)))?E(_vC):E(_vA):E(_vC):E(_vA);}else{return new F(function(){return _vE(_vH);});}}},_vJ=function(_vK,_vL){return new F(function(){return _vw(_vK,E(_vL));});},_vM=function(_vN,_vO){return E(B(_v3(_vN,E(_vO))).a);},_vP={_:0,a:_qY,b:_ip,c:_vs,d:_vM,e:_vJ,f:_vg,g:_vm},_vQ=new T1(0,1),_vR=function(_vS,_vT){var _vU=E(_vS);return new T2(0,_vU,new T(function(){var _vV=B(_vR(B(_3b(_vU,_vT)),_vT));return new T2(1,_vV.a,_vV.b);}));},_vW=function(_vX){var _vY=B(_vR(_vX,_vQ));return new T2(1,_vY.a,_vY.b);},_vZ=function(_w0,_w1){var _w2=B(_vR(_w0,new T(function(){return B(_5w(_w1,_w0));})));return new T2(1,_w2.a,_w2.b);},_w3=new T1(0,0),_w4=function(_w5,_w6){var _w7=E(_w5);if(!_w7._){var _w8=_w7.a,_w9=E(_w6);return (_w9._==0)?_w8>=_w9.a:I_compareInt(_w9.a,_w8)<=0;}else{var _wa=_w7.a,_wb=E(_w6);return (_wb._==0)?I_compareInt(_wa,_wb.a)>=0:I_compare(_wa,_wb.a)>=0;}},_wc=function(_wd,_we,_wf){if(!B(_w4(_we,_w3))){var _wg=function(_wh){return (!B(_3N(_wh,_wf)))?new T2(1,_wh,new T(function(){return B(_wg(B(_3b(_wh,_we))));})):__Z;};return new F(function(){return _wg(_wd);});}else{var _wi=function(_wj){return (!B(_3E(_wj,_wf)))?new T2(1,_wj,new T(function(){return B(_wi(B(_3b(_wj,_we))));})):__Z;};return new F(function(){return _wi(_wd);});}},_wk=function(_wl,_wm,_wn){return new F(function(){return _wc(_wl,B(_5w(_wm,_wl)),_wn);});},_wo=function(_wp,_wq){return new F(function(){return _wc(_wp,_vQ,_wq);});},_wr=function(_ws){return new F(function(){return _38(_ws);});},_wt=function(_wu){return new F(function(){return _5w(_wu,_vQ);});},_wv=function(_ww){return new F(function(){return _3b(_ww,_vQ);});},_wx=function(_wy){return new F(function(){return _pY(E(_wy));});},_wz={_:0,a:_wv,b:_wt,c:_wx,d:_wr,e:_vW,f:_vZ,g:_wo,h:_wk},_wA=function(_wB,_wC){while(1){var _wD=E(_wB);if(!_wD._){var _wE=E(_wD.a);if(_wE==( -2147483648)){_wB=new T1(1,I_fromInt( -2147483648));continue;}else{var _wF=E(_wC);if(!_wF._){return new T1(0,B(_rU(_wE,_wF.a)));}else{_wB=new T1(1,I_fromInt(_wE));_wC=_wF;continue;}}}else{var _wG=_wD.a,_wH=E(_wC);return (_wH._==0)?new T1(1,I_div(_wG,I_fromInt(_wH.a))):new T1(1,I_div(_wG,_wH.a));}}},_wI=function(_wJ,_wK){if(!B(_30(_wK,_un))){return new F(function(){return _wA(_wJ,_wK);});}else{return E(_2V);}},_wL=function(_wM,_wN){while(1){var _wO=E(_wM);if(!_wO._){var _wP=E(_wO.a);if(_wP==( -2147483648)){_wM=new T1(1,I_fromInt( -2147483648));continue;}else{var _wQ=E(_wN);if(!_wQ._){var _wR=_wQ.a;return new T2(0,new T1(0,B(_rU(_wP,_wR))),new T1(0,B(_sq(_wP,_wR))));}else{_wM=new T1(1,I_fromInt(_wP));_wN=_wQ;continue;}}}else{var _wS=E(_wN);if(!_wS._){_wM=_wO;_wN=new T1(1,I_fromInt(_wS.a));continue;}else{var _wT=I_divMod(_wO.a,_wS.a);return new T2(0,new T1(1,_wT.a),new T1(1,_wT.b));}}}},_wU=function(_wV,_wW){if(!B(_30(_wW,_un))){var _wX=B(_wL(_wV,_wW));return new T2(0,_wX.a,_wX.b);}else{return E(_2V);}},_wY=function(_wZ,_x0){while(1){var _x1=E(_wZ);if(!_x1._){var _x2=E(_x1.a);if(_x2==( -2147483648)){_wZ=new T1(1,I_fromInt( -2147483648));continue;}else{var _x3=E(_x0);if(!_x3._){return new T1(0,B(_sq(_x2,_x3.a)));}else{_wZ=new T1(1,I_fromInt(_x2));_x0=_x3;continue;}}}else{var _x4=_x1.a,_x5=E(_x0);return (_x5._==0)?new T1(1,I_mod(_x4,I_fromInt(_x5.a))):new T1(1,I_mod(_x4,_x5.a));}}},_x6=function(_x7,_x8){if(!B(_30(_x8,_un))){return new F(function(){return _wY(_x7,_x8);});}else{return E(_2V);}},_x9=function(_xa,_xb){while(1){var _xc=E(_xa);if(!_xc._){var _xd=E(_xc.a);if(_xd==( -2147483648)){_xa=new T1(1,I_fromInt( -2147483648));continue;}else{var _xe=E(_xb);if(!_xe._){return new T1(0,quot(_xd,_xe.a));}else{_xa=new T1(1,I_fromInt(_xd));_xb=_xe;continue;}}}else{var _xf=_xc.a,_xg=E(_xb);return (_xg._==0)?new T1(0,I_toInt(I_quot(_xf,I_fromInt(_xg.a)))):new T1(1,I_quot(_xf,_xg.a));}}},_xh=function(_xi,_xj){if(!B(_30(_xj,_un))){return new F(function(){return _x9(_xi,_xj);});}else{return E(_2V);}},_xk=function(_xl,_xm){if(!B(_30(_xm,_un))){var _xn=B(_3k(_xl,_xm));return new T2(0,_xn.a,_xn.b);}else{return E(_2V);}},_xo=function(_xp,_xq){while(1){var _xr=E(_xp);if(!_xr._){var _xs=E(_xr.a);if(_xs==( -2147483648)){_xp=new T1(1,I_fromInt( -2147483648));continue;}else{var _xt=E(_xq);if(!_xt._){return new T1(0,_xs%_xt.a);}else{_xp=new T1(1,I_fromInt(_xs));_xq=_xt;continue;}}}else{var _xu=_xr.a,_xv=E(_xq);return (_xv._==0)?new T1(1,I_rem(_xu,I_fromInt(_xv.a))):new T1(1,I_rem(_xu,_xv.a));}}},_xw=function(_xx,_xy){if(!B(_30(_xy,_un))){return new F(function(){return _xo(_xx,_xy);});}else{return E(_2V);}},_xz=function(_xA){return E(_xA);},_xB=function(_xC){return E(_xC);},_xD=function(_xE){var _xF=E(_xE);if(!_xF._){var _xG=E(_xF.a);return (_xG==( -2147483648))?E(_6a):(_xG<0)?new T1(0, -_xG):E(_xF);}else{var _xH=_xF.a;return (I_compareInt(_xH,0)>=0)?E(_xF):new T1(1,I_negate(_xH));}},_xI=new T1(0,0),_xJ=new T1(0, -1),_xK=function(_xL){var _xM=E(_xL);if(!_xM._){var _xN=_xM.a;return (_xN>=0)?(E(_xN)==0)?E(_xI):E(_3M):E(_xJ);}else{var _xO=I_compareInt(_xM.a,0);return (_xO<=0)?(E(_xO)==0)?E(_xI):E(_xJ):E(_3M);}},_xP={_:0,a:_3b,b:_5w,c:_tX,d:_6b,e:_xD,f:_xK,g:_xB},_xQ=function(_xR,_xS){var _xT=E(_xR);if(!_xT._){var _xU=_xT.a,_xV=E(_xS);return (_xV._==0)?_xU!=_xV.a:(I_compareInt(_xV.a,_xU)==0)?false:true;}else{var _xW=_xT.a,_xX=E(_xS);return (_xX._==0)?(I_compareInt(_xW,_xX.a)==0)?false:true:(I_compare(_xW,_xX.a)==0)?false:true;}},_xY=new T2(0,_30,_xQ),_xZ=function(_y0,_y1){return (!B(_5h(_y0,_y1)))?E(_y0):E(_y1);},_y2=function(_y3,_y4){return (!B(_5h(_y3,_y4)))?E(_y4):E(_y3);},_y5={_:0,a:_xY,b:_1N,c:_3N,d:_5h,e:_3E,f:_w4,g:_xZ,h:_y2},_y6=function(_y7){return new T2(0,E(_y7),E(_lJ));},_y8=new T3(0,_xP,_y5,_y6),_y9={_:0,a:_y8,b:_wz,c:_xh,d:_xw,e:_wI,f:_x6,g:_xk,h:_wU,i:_xz},_ya=function(_yb){return E(E(_yb).b);},_yc=function(_yd){return E(E(_yd).g);},_ye=new T1(0,1),_yf=function(_yg,_yh,_yi){var _yj=B(_ya(_yg)),_yk=B(_7i(_yj)),_yl=new T(function(){var _ym=new T(function(){var _yn=new T(function(){var _yo=new T(function(){return B(A3(_yc,_yg,_y9,new T(function(){return B(A3(_9b,_yj,_yh,_yi));})));});return B(A2(_91,_yk,_yo));}),_yp=new T(function(){return B(A2(_6K,_yk,new T(function(){return B(A2(_91,_yk,_ye));})));});return B(A3(_7k,_yk,_yp,_yn));});return B(A3(_7k,_yk,_ym,_yi));});return new F(function(){return A3(_6I,_yk,_yh,_yl);});},_yq=1.5707963267948966,_yr=function(_ys){return 0.2/Math.cos(B(_yf(_vP,_ys,_yq))-0.7853981633974483);},_yt=2,_yu=0.3,_yv=new T(function(){var _yw=B(_oq(_yr,1.2,_pU,_pI,_pI,_pI,_pI,_pT,_yu,_yt,_pI,_pI,_pP));return {_:0,a:E(_yw.a),b:E(_yw.b),c:E(_yw.c),d:E(_yw.d),e:E(_yw.e),f:E(_yw.f),g:E(_yw.g),h:E(_yw.h),i:E(_yw.i)};}),_yx=new T2(1,_yv,_o),_yy=new T2(1,_pQ,_yx),_yz=new T(function(){return B(unCStr("Negative range size"));}),_yA=new T(function(){return B(err(_yz));}),_yB=function(_){var _yC=B(_hf(_yy,0))-1|0,_yD=function(_yE){if(_yE>=0){var _yF=newArr(_yE,_hl),_yG=_yF,_yH=E(_yE);if(!_yH){return new T4(0,E(_pS),E(_yC),0,_yG);}else{var _yI=function(_yJ,_yK,_){while(1){var _yL=E(_yJ);if(!_yL._){return E(_);}else{var _=_yG[_yK]=_yL.a;if(_yK!=(_yH-1|0)){var _yM=_yK+1|0;_yJ=_yL.b;_yK=_yM;continue;}else{return E(_);}}}},_=B((function(_yN,_yO,_yP,_){var _=_yG[_yP]=_yN;if(_yP!=(_yH-1|0)){return new F(function(){return _yI(_yO,_yP+1|0,_);});}else{return E(_);}})(_pQ,_yx,0,_));return new T4(0,E(_pS),E(_yC),_yH,_yG);}}else{return E(_yA);}};if(0>_yC){return new F(function(){return _yD(0);});}else{return new F(function(){return _yD(_yC+1|0);});}},_yQ=function(_yR){var _yS=B(A1(_yR,_));return E(_yS);},_yT=new T(function(){return B(_yQ(_yB));}),_yU=function(_yV,_yW,_){var _yX=B(A1(_yV,_)),_yY=B(A1(_yW,_));return _yX;},_yZ=function(_z0,_z1,_){var _z2=B(A1(_z0,_)),_z3=B(A1(_z1,_));return new T(function(){return B(A1(_z2,_z3));});},_z4=function(_z5,_z6,_){var _z7=B(A1(_z6,_));return _z5;},_z8=function(_z9,_za,_){var _zb=B(A1(_za,_));return new T(function(){return B(A1(_z9,_zb));});},_zc=new T2(0,_z8,_z4),_zd=function(_ze,_){return _ze;},_zf=function(_zg,_zh,_){var _zi=B(A1(_zg,_));return new F(function(){return A1(_zh,_);});},_zj=new T5(0,_zc,_zd,_yZ,_zf,_yU),_zk=function(_zl){var _zm=E(_zl);return (E(_zm.b)-E(_zm.a)|0)+1|0;},_zn=function(_zo,_zp){var _zq=E(_zo),_zr=E(_zp);return (E(_zq.a)>_zr)?false:_zr<=E(_zq.b);},_zs=function(_zt,_zu){var _zv=jsShowI(_zt);return new F(function(){return _f(fromJSStr(_zv),_zu);});},_zw=function(_zx,_zy,_zz){if(_zy>=0){return new F(function(){return _zs(_zy,_zz);});}else{if(_zx<=6){return new F(function(){return _zs(_zy,_zz);});}else{return new T2(1,_71,new T(function(){var _zA=jsShowI(_zy);return B(_f(fromJSStr(_zA),new T2(1,_70,_zz)));}));}}},_zB=function(_zC){return new F(function(){return _zw(0,E(_zC),_o);});},_zD=function(_zE,_zF,_zG){return new F(function(){return _zw(E(_zE),E(_zF),_zG);});},_zH=function(_zI,_zJ){return new F(function(){return _zw(0,E(_zI),_zJ);});},_zK=function(_zL,_zM){return new F(function(){return _2B(_zH,_zL,_zM);});},_zN=new T3(0,_zD,_zB,_zK),_zO=0,_zP=function(_zQ,_zR,_zS){return new F(function(){return A1(_zQ,new T2(1,_2y,new T(function(){return B(A1(_zR,_zS));})));});},_zT=new T(function(){return B(unCStr("foldr1"));}),_zU=new T(function(){return B(_l9(_zT));}),_zV=function(_zW,_zX){var _zY=E(_zX);if(!_zY._){return E(_zU);}else{var _zZ=_zY.a,_A0=E(_zY.b);if(!_A0._){return E(_zZ);}else{return new F(function(){return A2(_zW,_zZ,new T(function(){return B(_zV(_zW,_A0));}));});}}},_A1=new T(function(){return B(unCStr(" out of range "));}),_A2=new T(function(){return B(unCStr("}.index: Index "));}),_A3=new T(function(){return B(unCStr("Ix{"));}),_A4=new T2(1,_70,_o),_A5=new T2(1,_70,_A4),_A6=0,_A7=function(_A8){return E(E(_A8).a);},_A9=function(_Aa,_Ab,_Ac,_Ad,_Ae){var _Af=new T(function(){var _Ag=new T(function(){var _Ah=new T(function(){var _Ai=new T(function(){var _Aj=new T(function(){return B(A3(_zV,_zP,new T2(1,new T(function(){return B(A3(_A7,_Ac,_A6,_Ad));}),new T2(1,new T(function(){return B(A3(_A7,_Ac,_A6,_Ae));}),_o)),_A5));});return B(_f(_A1,new T2(1,_71,new T2(1,_71,_Aj))));});return B(A(_A7,[_Ac,_zO,_Ab,new T2(1,_70,_Ai)]));});return B(_f(_A2,new T2(1,_71,_Ah)));},1);return B(_f(_Aa,_Ag));},1);return new F(function(){return err(B(_f(_A3,_Af)));});},_Ak=function(_Al,_Am,_An,_Ao,_Ap){return new F(function(){return _A9(_Al,_Am,_Ap,_An,_Ao);});},_Aq=function(_Ar,_As,_At,_Au){var _Av=E(_At);return new F(function(){return _Ak(_Ar,_As,_Av.a,_Av.b,_Au);});},_Aw=function(_Ax,_Ay,_Az,_AA){return new F(function(){return _Aq(_AA,_Az,_Ay,_Ax);});},_AB=new T(function(){return B(unCStr("Int"));}),_AC=function(_AD,_AE){return new F(function(){return _Aw(_zN,_AD,_AE,_AB);});},_AF=function(_AG,_AH){var _AI=E(_AG),_AJ=E(_AI.a),_AK=E(_AH);if(_AJ>_AK){return new F(function(){return _AC(_AI,_AK);});}else{if(_AK>E(_AI.b)){return new F(function(){return _AC(_AI,_AK);});}else{return _AK-_AJ|0;}}},_AL=function(_AM){var _AN=E(_AM);return new F(function(){return _rE(_AN.a,_AN.b);});},_AO=function(_AP){var _AQ=E(_AP),_AR=E(_AQ.a),_AS=E(_AQ.b);return (_AR>_AS)?E(_zO):(_AS-_AR|0)+1|0;},_AT=function(_AU,_AV){return new F(function(){return _t3(_AV,E(_AU).a);});},_AW={_:0,a:_tT,b:_AL,c:_AF,d:_AT,e:_zn,f:_AO,g:_zk},_AX=function(_AY,_AZ){return new T2(1,_AY,_AZ);},_B0=function(_B1,_B2){var _B3=E(_B2);return new T2(0,_B3.a,_B3.b);},_B4=function(_B5){return E(E(_B5).f);},_B6=function(_B7,_B8,_B9){var _Ba=E(_B8),_Bb=_Ba.a,_Bc=_Ba.b,_Bd=function(_){var _Be=B(A2(_B4,_B7,_Ba));if(_Be>=0){var _Bf=newArr(_Be,_hl),_Bg=_Bf,_Bh=E(_Be);if(!_Bh){return new T(function(){return new T4(0,E(_Bb),E(_Bc),0,_Bg);});}else{var _Bi=function(_Bj,_Bk,_){while(1){var _Bl=E(_Bj);if(!_Bl._){return E(_);}else{var _=_Bg[_Bk]=_Bl.a;if(_Bk!=(_Bh-1|0)){var _Bm=_Bk+1|0;_Bj=_Bl.b;_Bk=_Bm;continue;}else{return E(_);}}}},_=B(_Bi(_B9,0,_));return new T(function(){return new T4(0,E(_Bb),E(_Bc),_Bh,_Bg);});}}else{return E(_yA);}};return new F(function(){return _yQ(_Bd);});},_Bn=function(_Bo,_Bp,_Bq,_Br){var _Bs=new T(function(){var _Bt=E(_Br),_Bu=_Bt.c-1|0,_Bv=new T(function(){return B(A2(_cX,_Bp,_o));});if(0<=_Bu){var _Bw=new T(function(){return B(_97(_Bp));}),_Bx=function(_By){var _Bz=new T(function(){var _BA=new T(function(){return B(A1(_Bq,new T(function(){return E(_Bt.d[_By]);})));});return B(A3(_9f,_Bw,_AX,_BA));});return new F(function(){return A3(_9d,_Bp,_Bz,new T(function(){if(_By!=_Bu){return B(_Bx(_By+1|0));}else{return E(_Bv);}}));});};return B(_Bx(0));}else{return E(_Bv);}}),_BB=new T(function(){return B(_B0(_Bo,_Br));});return new F(function(){return A3(_9f,B(_97(_Bp)),function(_BC){return new F(function(){return _B6(_Bo,_BB,_BC);});},_Bs);});},_BD=0,_BE=function(_){return _BD;},_BF=new T(function(){return eval("__strict(drawTriangles)");}),_BG=function(_){var _BH=__app0(E(_BF));return new F(function(){return _BE(_);});},_BI=new T(function(){return eval("__strict(vertex)");}),_BJ=function(_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_){var _BT=E(_BR);if(!_BT._){return new F(function(){return _BG(_);});}else{var _BU=E(_BT.a),_BV=E(_BU.a),_BW=E(_BV.a),_BX=E(_BV.b),_BY=E(_BU.b),_BZ=E(_BY.a),_C0=E(_BY.b),_C1=E(_BU.c),_C2=E(_C1.a),_C3=E(_C1.b),_C4=E(_BI),_C5=__apply(_C4,new T2(1,_BV.c,new T2(1,_BX.b,new T2(1,_BX.a,new T2(1,_BW.c,new T2(1,_BW.b,new T2(1,_BW.a,_o))))))),_C6=__apply(_C4,new T2(1,_BY.c,new T2(1,_C0.b,new T2(1,_C0.a,new T2(1,_BZ.c,new T2(1,_BZ.b,new T2(1,_BZ.a,_o))))))),_C7=__apply(_C4,new T2(1,_C1.c,new T2(1,_C3.b,new T2(1,_C3.a,new T2(1,_C2.c,new T2(1,_C2.b,new T2(1,_C2.a,_o))))))),_C8=function(_C9,_){while(1){var _Ca=E(_C9);if(!_Ca._){return _BD;}else{var _Cb=E(_Ca.a),_Cc=E(_Cb.a),_Cd=E(_Cc.a),_Ce=E(_Cc.b),_Cf=E(_Cb.b),_Cg=E(_Cf.a),_Ch=E(_Cf.b),_Ci=E(_Cb.c),_Cj=E(_Ci.a),_Ck=E(_Ci.b),_Cl=__apply(_C4,new T2(1,_Cc.c,new T2(1,_Ce.b,new T2(1,_Ce.a,new T2(1,_Cd.c,new T2(1,_Cd.b,new T2(1,_Cd.a,_o))))))),_Cm=__apply(_C4,new T2(1,_Cf.c,new T2(1,_Ch.b,new T2(1,_Ch.a,new T2(1,_Cg.c,new T2(1,_Cg.b,new T2(1,_Cg.a,_o))))))),_Cn=__apply(_C4,new T2(1,_Ci.c,new T2(1,_Ck.b,new T2(1,_Ck.a,new T2(1,_Cj.c,new T2(1,_Cj.b,new T2(1,_Cj.a,_o)))))));_C9=_Ca.b;continue;}}},_Co=B(_C8(_BT.b,_));return new F(function(){return _BG(_);});}},_Cp=function(_Cq,_){var _Cr=E(_Cq);return new F(function(){return _BJ(_Cr.a,_Cr.b,_Cr.c,_Cr.d,_Cr.e,_Cr.f,_Cr.g,_Cr.h,_Cr.i,_);});},_Cs=new T(function(){return eval("__strict(draw)");}),_Ct=function(_Cu){return E(_Cu);},_Cv=function(_Cw){return E(_Cw);},_Cx=function(_Cy,_Cz){return E(_Cz);},_CA=function(_CB,_CC){return E(_CB);},_CD=function(_CE){return E(_CE);},_CF=new T2(0,_CD,_CA),_CG=function(_CH,_CI){return E(_CH);},_CJ=new T5(0,_CF,_Cv,_Ct,_Cx,_CG),_CK="c2y",_CL="c2x",_CM="c1y",_CN="c1x",_CO="n2z",_CP="n2y",_CQ="n2x",_CR="n1z",_CS="n1y",_CT="n1x",_CU=function(_CV,_){var _CW=__get(_CV,E(_CN)),_CX=__get(_CV,E(_CM)),_CY=__get(_CV,E(_CL)),_CZ=__get(_CV,E(_CK)),_D0=__get(_CV,E(_CT)),_D1=__get(_CV,E(_CS)),_D2=__get(_CV,E(_CR)),_D3=__get(_CV,E(_CQ)),_D4=__get(_CV,E(_CP)),_D5=__get(_CV,E(_CO));return new T4(0,E(new T2(0,E(_CW),E(_CX))),E(new T2(0,E(_CY),E(_CZ))),E(new T3(0,E(_D0),E(_D1),E(_D2))),E(new T3(0,E(_D3),E(_D4),E(_D5))));},_D6=function(_D7,_){var _D8=E(_D7);if(!_D8._){return _o;}else{var _D9=B(_CU(E(_D8.a),_)),_Da=B(_D6(_D8.b,_));return new T2(1,_D9,_Da);}},_Db=function(_Dc){var _Dd=E(_Dc);if(!_Dd._){return __Z;}else{return new F(function(){return _f(_Dd.a,new T(function(){return B(_Db(_Dd.b));},1));});}},_De=function(_Df,_Dg){return new F(function(){return _f(_Df,new T(function(){return B(_Db(_Dg));},1));});},_Dh="outline",_Di="polygon",_Dj="ly",_Dk="lx",_Dl="wz",_Dm="wy",_Dn="wx",_Do=function(_Dp){var _Dq=__new(),_Dr=_Dq,_Ds=function(_Dt,_){while(1){var _Du=E(_Dt);if(!_Du._){return _BD;}else{var _Dv=E(_Du.a),_Dw=__set(_Dr,E(_Dv.a),E(_Dv.b));_Dt=_Du.b;continue;}}},_Dx=B(_Ds(_Dp,_));return E(_Dr);},_Dy=function(_Dz,_DA,_DB,_DC,_DD,_DE){return new F(function(){return _Do(new T2(1,new T2(0,_Dn,_Dz),new T2(1,new T2(0,_Dm,_DA),new T2(1,new T2(0,_Dl,_DB),new T2(1,new T2(0,_Dk,_DC*_DD*Math.cos(_DE)),new T2(1,new T2(0,_Dj,_DC*_DD*Math.sin(_DE)),_o))))));});},_DF=function(_DG){var _DH=E(_DG),_DI=E(_DH.a),_DJ=E(_DH.b);return new F(function(){return _Dy(_DI.a,_DI.b,_DI.c,E(_DJ.a),E(_DJ.b),E(_DH.c));});},_DK=function(_DL,_DM,_DN){var _DO=__lst2arr(B(_mk(_DF,new T2(1,_DL,new T2(1,_DM,new T2(1,_DN,_o))))));return E(_DO);},_DP=function(_DQ){var _DR=E(_DQ);return new F(function(){return _DK(_DR.a,_DR.b,_DR.c);});},_DS=function(_DT){return new F(function(){return _Do(new T2(1,new T2(0,_Di,new T(function(){return __lst2arr(B(_mk(_DP,E(_DT).h)));})),new T2(1,new T2(0,_Dh,new T(function(){return __lst2arr(B(_mk(_DF,E(_DT).i)));})),_o)));});},_DU=function(_DV,_DW,_DX,_DY,_DZ,_E0,_E1,_E2,_E3){var _E4=B(_7k(_DV));return new T2(0,new T3(0,E(B(A1(B(A1(_E4,_DW)),_E0))),E(B(A1(B(A1(_E4,_DX)),_E1))),E(B(A1(B(A1(_E4,_DY)),_E2)))),B(A1(B(A1(_E4,_DZ)),_E3)));},_E5=function(_E6,_E7,_E8,_E9,_Ea,_Eb,_Ec,_Ed,_Ee){var _Ef=B(_6I(_E6));return new T2(0,new T3(0,E(B(A1(B(A1(_Ef,_E7)),_Eb))),E(B(A1(B(A1(_Ef,_E8)),_Ec))),E(B(A1(B(A1(_Ef,_E9)),_Ed)))),B(A1(B(A1(_Ef,_Ea)),_Ee)));},_Eg=5.0e-2,_Eh=function(_Ei,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew,_Ex,_Ey){var _Ez=B(_DU(_il,_Ep,_Eq,_Er,_Es,_Eg,_Eg,_Eg,_Eg)),_EA=E(_Ez.a),_EB=B(_E5(_il,_El,_Em,_En,_Eo,_EA.a,_EA.b,_EA.c,_Ez.b)),_EC=E(_EB.a);return new F(function(){return _nO(_Ei,_Ej,_Ek,_EC.a,_EC.b,_EC.c,_EB.b,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew,_Ex,_Ey);});},_ED=function(_EE){var _EF=E(_EE),_EG=E(_EF.b),_EH=E(_EF.e),_EI=E(_EH.a),_EJ=E(_EF.g),_EK=B(_ks(_iR,_EG.a,_EG.b,_EG.c,_EJ.a,_EJ.b,_EJ.c));return {_:0,a:E(_EF.a),b:E(_EG),c:E(_EF.c),d:E(_EF.d),e:E(new T2(0,E(new T3(0,E(_EI.a)+E(_EK.a)*5.0e-2,E(_EI.b)+E(_EK.b)*5.0e-2,E(_EI.c)+E(_EK.c)*5.0e-2)),E(_EH.b))),f:E(_EF.f),g:E(_EJ),h:E(_EF.h),i:E(_EF.i)};},_EL=function(_EM){var _EN=E(_EM),_EO=E(_EN.d),_EP=E(_EO.a),_EQ=E(_EN.e),_ER=E(_EQ.a),_ES=E(_EN.f),_ET=B(_Eh(_EN.a,_EN.b,_EN.c,_EP.a,_EP.b,_EP.c,_EO.b,_ER.a,_ER.b,_ER.c,_EQ.b,_ES.a,_ES.b,_ES.c,_EN.g,_EN.h,_EN.i));return {_:0,a:E(_ET.a),b:E(_ET.b),c:E(_ET.c),d:E(_ET.d),e:E(_ET.e),f:E(_ET.f),g:E(_ET.g),h:E(_ET.h),i:E(_ET.i)};},_EU=function(_EV,_EW,_){var _EX=E(_EV);if(!_EX._){return new T2(0,_o,_EW);}else{var _EY=E(_EX.a),_EZ=B(_EU(_EX.b,_EW,_));return new T2(0,new T2(1,_BD,new T(function(){return E(E(_EZ).a);})),new T(function(){return E(E(_EZ).b);}));}},_F0=new T(function(){return eval("collide");}),_F1=new T(function(){return B(unCStr("base"));}),_F2=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_F3=new T(function(){return B(unCStr("IOException"));}),_F4=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_F1,_F2,_F3),_F5=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_F4,_o,_o),_F6=function(_F7){return E(_F5);},_F8=function(_F9){var _Fa=E(_F9);return new F(function(){return _28(B(_26(_Fa.a)),_F6,_Fa.b);});},_Fb=new T(function(){return B(unCStr(": "));}),_Fc=new T(function(){return B(unCStr(")"));}),_Fd=new T(function(){return B(unCStr(" ("));}),_Fe=new T(function(){return B(unCStr("interrupted"));}),_Ff=new T(function(){return B(unCStr("resource vanished"));}),_Fg=new T(function(){return B(unCStr("unsatisified constraints"));}),_Fh=new T(function(){return B(unCStr("user error"));}),_Fi=new T(function(){return B(unCStr("permission denied"));}),_Fj=new T(function(){return B(unCStr("illegal operation"));}),_Fk=new T(function(){return B(unCStr("end of file"));}),_Fl=new T(function(){return B(unCStr("resource exhausted"));}),_Fm=new T(function(){return B(unCStr("resource busy"));}),_Fn=new T(function(){return B(unCStr("does not exist"));}),_Fo=new T(function(){return B(unCStr("already exists"));}),_Fp=new T(function(){return B(unCStr("timeout"));}),_Fq=new T(function(){return B(unCStr("unsupported operation"));}),_Fr=new T(function(){return B(unCStr("hardware fault"));}),_Fs=new T(function(){return B(unCStr("inappropriate type"));}),_Ft=new T(function(){return B(unCStr("invalid argument"));}),_Fu=new T(function(){return B(unCStr("failed"));}),_Fv=new T(function(){return B(unCStr("protocol error"));}),_Fw=new T(function(){return B(unCStr("system error"));}),_Fx=function(_Fy,_Fz){switch(E(_Fy)){case 0:return new F(function(){return _f(_Fo,_Fz);});break;case 1:return new F(function(){return _f(_Fn,_Fz);});break;case 2:return new F(function(){return _f(_Fm,_Fz);});break;case 3:return new F(function(){return _f(_Fl,_Fz);});break;case 4:return new F(function(){return _f(_Fk,_Fz);});break;case 5:return new F(function(){return _f(_Fj,_Fz);});break;case 6:return new F(function(){return _f(_Fi,_Fz);});break;case 7:return new F(function(){return _f(_Fh,_Fz);});break;case 8:return new F(function(){return _f(_Fg,_Fz);});break;case 9:return new F(function(){return _f(_Fw,_Fz);});break;case 10:return new F(function(){return _f(_Fv,_Fz);});break;case 11:return new F(function(){return _f(_Fu,_Fz);});break;case 12:return new F(function(){return _f(_Ft,_Fz);});break;case 13:return new F(function(){return _f(_Fs,_Fz);});break;case 14:return new F(function(){return _f(_Fr,_Fz);});break;case 15:return new F(function(){return _f(_Fq,_Fz);});break;case 16:return new F(function(){return _f(_Fp,_Fz);});break;case 17:return new F(function(){return _f(_Ff,_Fz);});break;default:return new F(function(){return _f(_Fe,_Fz);});}},_FA=new T(function(){return B(unCStr("}"));}),_FB=new T(function(){return B(unCStr("{handle: "));}),_FC=function(_FD,_FE,_FF,_FG,_FH,_FI){var _FJ=new T(function(){var _FK=new T(function(){var _FL=new T(function(){var _FM=E(_FG);if(!_FM._){return E(_FI);}else{var _FN=new T(function(){return B(_f(_FM,new T(function(){return B(_f(_Fc,_FI));},1)));},1);return B(_f(_Fd,_FN));}},1);return B(_Fx(_FE,_FL));}),_FO=E(_FF);if(!_FO._){return E(_FK);}else{return B(_f(_FO,new T(function(){return B(_f(_Fb,_FK));},1)));}}),_FP=E(_FH);if(!_FP._){var _FQ=E(_FD);if(!_FQ._){return E(_FJ);}else{var _FR=E(_FQ.a);if(!_FR._){var _FS=new T(function(){var _FT=new T(function(){return B(_f(_FA,new T(function(){return B(_f(_Fb,_FJ));},1)));},1);return B(_f(_FR.a,_FT));},1);return new F(function(){return _f(_FB,_FS);});}else{var _FU=new T(function(){var _FV=new T(function(){return B(_f(_FA,new T(function(){return B(_f(_Fb,_FJ));},1)));},1);return B(_f(_FR.a,_FV));},1);return new F(function(){return _f(_FB,_FU);});}}}else{return new F(function(){return _f(_FP.a,new T(function(){return B(_f(_Fb,_FJ));},1));});}},_FW=function(_FX){var _FY=E(_FX);return new F(function(){return _FC(_FY.a,_FY.b,_FY.c,_FY.d,_FY.f,_o);});},_FZ=function(_G0,_G1,_G2){var _G3=E(_G1);return new F(function(){return _FC(_G3.a,_G3.b,_G3.c,_G3.d,_G3.f,_G2);});},_G4=function(_G5,_G6){var _G7=E(_G5);return new F(function(){return _FC(_G7.a,_G7.b,_G7.c,_G7.d,_G7.f,_G6);});},_G8=function(_G9,_Ga){return new F(function(){return _2B(_G4,_G9,_Ga);});},_Gb=new T3(0,_FZ,_FW,_G8),_Gc=new T(function(){return new T5(0,_F6,_Gb,_Gd,_F8,_FW);}),_Gd=function(_Ge){return new T2(0,_Gc,_Ge);},_Gf=__Z,_Gg=7,_Gh=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_Gi=new T6(0,_Gf,_Gg,_o,_Gh,_Gf,_Gf),_Gj=new T(function(){return B(_Gd(_Gi));}),_Gk=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));}),_Gl=new T6(0,_Gf,_Gg,_o,_Gk,_Gf,_Gf),_Gm=new T(function(){return B(_Gd(_Gl));}),_Gn=new T(function(){return B(unCStr(")"));}),_Go=function(_Gp,_Gq){var _Gr=new T(function(){var _Gs=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zw(0,_Gq,_o)),_Gn));})));},1);return B(_f(B(_zw(0,_Gp,_o)),_Gs));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Gr)));});},_Gt=function(_Gu,_){var _Gv=B(_Bn(_AW,_CJ,_ED,_Gu)),_Gw=_Gv.c,_Gx=_Gv.d,_Gy=E(_Gv.a),_Gz=E(_Gv.b);if(_Gy<=_Gz){var _GA=function(_GB,_GC,_){if(_GB<=_Gz){var _GD=E(_GC),_GE=_GD.c,_GF=_GD.d,_GG=E(_GD.a),_GH=E(_GD.b);if(_GG>_GB){return new F(function(){return die(_Gj);});}else{if(_GB>_GH){return new F(function(){return die(_Gj);});}else{if(_GG>_GB){return new F(function(){return die(_Gm);});}else{if(_GB>_GH){return new F(function(){return die(_Gm);});}else{var _GI=_GB-_GG|0;if(0>_GI){return new F(function(){return _Go(_GI,_GE);});}else{if(_GI>=_GE){return new F(function(){return _Go(_GI,_GE);});}else{var _GJ=_GB-_GG|0;if(0>_GJ){return new F(function(){return _Go(_GJ,_GE);});}else{if(_GJ>=_GE){return new F(function(){return _Go(_GJ,_GE);});}else{var _GK=E(_F0),_GL=__app2(_GK,B(_DS(E(_GF[_GI]))),B(_DS(E(_GF[_GJ])))),_GM=__arr2lst(0,_GL),_GN=B(_D6(_GM,_)),_GO=B(_EU(_GN,new T4(0,E(_GG),E(_GH),_GE,_GF),_));if(_GB!=_Gz){var _GP=E(_GO),_GQ=_GP.a,_GR=E(_GP.b),_GS=function(_GT,_GU,_GV,_GW,_GX,_){if(_GU>_GB){return new F(function(){return die(_Gj);});}else{if(_GB>_GV){return new F(function(){return die(_Gj);});}else{if(_GU>_GT){return new F(function(){return die(_Gm);});}else{if(_GT>_GV){return new F(function(){return die(_Gm);});}else{var _GY=_GB-_GU|0;if(0>_GY){return new F(function(){return _Go(_GY,_GW);});}else{if(_GY>=_GW){return new F(function(){return _Go(_GY,_GW);});}else{var _GZ=_GT-_GU|0;if(0>_GZ){return new F(function(){return _Go(_GZ,_GW);});}else{if(_GZ>=_GW){return new F(function(){return _Go(_GZ,_GW);});}else{var _H0=__app2(_GK,B(_DS(E(_GX[_GY]))),B(_DS(E(_GX[_GZ])))),_H1=__arr2lst(0,_H0),_H2=B(_D6(_H1,_)),_H3=B(_EU(_H2,new T4(0,E(_GU),E(_GV),_GW,_GX),_));if(_GT!=_Gz){var _H4=E(_H3),_H5=E(_H4.b),_H6=B(_GS(_GT+1|0,E(_H5.a),E(_H5.b),_H5.c,_H5.d,_));return new T2(0,new T2(1,_H4.a,new T(function(){return E(E(_H6).a);})),new T(function(){return E(E(_H6).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_H3).a);}),_o),new T(function(){return E(E(_H3).b);}));}}}}}}}}}},_H7=B(_GS(_GB+1|0,E(_GR.a),E(_GR.b),_GR.c,_GR.d,_));if(_GB!=_Gz){var _H8=B(_GA(_GB+1|0,new T(function(){return E(E(_H7).b);},1),_)),_H9=new T(function(){return B(_De(_GQ,new T(function(){return E(E(_H7).a);})));});return new T2(0,new T2(1,_H9,new T(function(){return E(E(_H8).a);})),new T(function(){return E(E(_H8).b);}));}else{var _Ha=new T(function(){return B(_De(_GQ,new T(function(){return E(E(_H7).a);})));});return new T2(0,new T2(1,_Ha,_o),new T(function(){return E(E(_H7).b);}));}}else{if(_GB!=_Gz){var _Hb=B(_GA(_GB+1|0,new T(function(){return E(E(_GO).b);},1),_)),_Hc=new T(function(){return B(_De(new T(function(){return E(E(_GO).a);}),_o));});return new T2(0,new T2(1,_Hc,new T(function(){return E(E(_Hb).a);})),new T(function(){return E(E(_Hb).b);}));}else{var _Hd=new T(function(){return B(_De(new T(function(){return E(E(_GO).a);}),_o));});return new T2(0,new T2(1,_Hd,_o),new T(function(){return E(E(_GO).b);}));}}}}}}}}}}}else{if(_GB!=_Gz){var _He=B(_GA(_GB+1|0,_GC,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_He).a);})),new T(function(){return E(E(_He).b);}));}else{return new T2(0,new T2(1,_o,_o),_GC);}}},_Hf=function(_Hg,_Hh,_Hi,_Hj,_Hk,_){if(_Hg<=_Gz){if(_Hh>_Hg){return new F(function(){return die(_Gj);});}else{if(_Hg>_Hi){return new F(function(){return die(_Gj);});}else{if(_Hh>_Hg){return new F(function(){return die(_Gm);});}else{if(_Hg>_Hi){return new F(function(){return die(_Gm);});}else{var _Hl=_Hg-_Hh|0;if(0>_Hl){return new F(function(){return _Go(_Hl,_Hj);});}else{if(_Hl>=_Hj){return new F(function(){return _Go(_Hl,_Hj);});}else{var _Hm=_Hg-_Hh|0;if(0>_Hm){return new F(function(){return _Go(_Hm,_Hj);});}else{if(_Hm>=_Hj){return new F(function(){return _Go(_Hm,_Hj);});}else{var _Hn=E(_F0),_Ho=__app2(_Hn,B(_DS(E(_Hk[_Hl]))),B(_DS(E(_Hk[_Hm])))),_Hp=__arr2lst(0,_Ho),_Hq=B(_D6(_Hp,_)),_Hr=B(_EU(_Hq,new T4(0,E(_Hh),E(_Hi),_Hj,_Hk),_));if(_Hg!=_Gz){var _Hs=E(_Hr),_Ht=_Hs.a,_Hu=E(_Hs.b),_Hv=function(_Hw,_Hx,_Hy,_Hz,_HA,_){if(_Hx>_Hg){return new F(function(){return die(_Gj);});}else{if(_Hg>_Hy){return new F(function(){return die(_Gj);});}else{if(_Hx>_Hw){return new F(function(){return die(_Gm);});}else{if(_Hw>_Hy){return new F(function(){return die(_Gm);});}else{var _HB=_Hg-_Hx|0;if(0>_HB){return new F(function(){return _Go(_HB,_Hz);});}else{if(_HB>=_Hz){return new F(function(){return _Go(_HB,_Hz);});}else{var _HC=_Hw-_Hx|0;if(0>_HC){return new F(function(){return _Go(_HC,_Hz);});}else{if(_HC>=_Hz){return new F(function(){return _Go(_HC,_Hz);});}else{var _HD=__app2(_Hn,B(_DS(E(_HA[_HB]))),B(_DS(E(_HA[_HC])))),_HE=__arr2lst(0,_HD),_HF=B(_D6(_HE,_)),_HG=B(_EU(_HF,new T4(0,E(_Hx),E(_Hy),_Hz,_HA),_));if(_Hw!=_Gz){var _HH=E(_HG),_HI=E(_HH.b),_HJ=B(_Hv(_Hw+1|0,E(_HI.a),E(_HI.b),_HI.c,_HI.d,_));return new T2(0,new T2(1,_HH.a,new T(function(){return E(E(_HJ).a);})),new T(function(){return E(E(_HJ).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_HG).a);}),_o),new T(function(){return E(E(_HG).b);}));}}}}}}}}}},_HK=B(_Hv(_Hg+1|0,E(_Hu.a),E(_Hu.b),_Hu.c,_Hu.d,_));if(_Hg!=_Gz){var _HL=B(_GA(_Hg+1|0,new T(function(){return E(E(_HK).b);},1),_)),_HM=new T(function(){return B(_De(_Ht,new T(function(){return E(E(_HK).a);})));});return new T2(0,new T2(1,_HM,new T(function(){return E(E(_HL).a);})),new T(function(){return E(E(_HL).b);}));}else{var _HN=new T(function(){return B(_De(_Ht,new T(function(){return E(E(_HK).a);})));});return new T2(0,new T2(1,_HN,_o),new T(function(){return E(E(_HK).b);}));}}else{if(_Hg!=_Gz){var _HO=B(_GA(_Hg+1|0,new T(function(){return E(E(_Hr).b);},1),_)),_HP=new T(function(){return B(_De(new T(function(){return E(E(_Hr).a);}),_o));});return new T2(0,new T2(1,_HP,new T(function(){return E(E(_HO).a);})),new T(function(){return E(E(_HO).b);}));}else{var _HQ=new T(function(){return B(_De(new T(function(){return E(E(_Hr).a);}),_o));});return new T2(0,new T2(1,_HQ,_o),new T(function(){return E(E(_Hr).b);}));}}}}}}}}}}}else{if(_Hg!=_Gz){var _HR=B(_Hf(_Hg+1|0,_Hh,_Hi,_Hj,_Hk,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_HR).a);})),new T(function(){return E(E(_HR).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_Hh),E(_Hi),_Hj,_Hk));}}},_HS=B(_Hf(_Gy,_Gy,_Gz,_Gw,_Gx,_)),_HT=new T(function(){return B(_Bn(_AW,_CJ,_EL,new T(function(){return E(E(_HS).b);})));});return new T2(0,_BD,_HT);}else{var _HU=new T(function(){var _HV=function(_){var _HW=function(_HX){if(_HX>=0){var _HY=newArr(_HX,_hl),_HZ=_HY,_I0=E(_HX);if(!_I0){return new T4(0,E(_Gy),E(_Gz),0,_HZ);}else{var _I1=_Gw-1|0,_I2=function(_I3,_I4,_){while(1){var _I5=E(_I3);if(!_I5._){return E(_);}else{var _=_HZ[_I4]=_I5.a;if(_I4!=(_I0-1|0)){var _I6=_I4+1|0;_I3=_I5.b;_I4=_I6;continue;}else{return E(_);}}}};if(0<=_I1){var _I7=function(_I8){return new T2(1,new T(function(){var _I9=E(_Gx[_I8]),_Ia=E(_I9.d),_Ib=E(_Ia.a),_Ic=E(_I9.e),_Id=E(_Ic.a),_Ie=E(_I9.f),_If=B(_Eh(_I9.a,_I9.b,_I9.c,_Ib.a,_Ib.b,_Ib.c,_Ia.b,_Id.a,_Id.b,_Id.c,_Ic.b,_Ie.a,_Ie.b,_Ie.c,_I9.g,_I9.h,_I9.i));return {_:0,a:E(_If.a),b:E(_If.b),c:E(_If.c),d:E(_If.d),e:E(_If.e),f:E(_If.f),g:E(_If.g),h:E(_If.h),i:E(_If.i)};}),new T(function(){if(_I8!=_I1){return B(_I7(_I8+1|0));}else{return __Z;}}));},_=B(_I2(B(_I7(0)),0,_));return new T4(0,E(_Gy),E(_Gz),_I0,_HZ);}else{return new T4(0,E(_Gy),E(_Gz),_I0,_HZ);}}}else{return E(_yA);}};if(_Gy>_Gz){return new F(function(){return _HW(0);});}else{return new F(function(){return _HW((_Gz-_Gy|0)+1|0);});}};return B(_yQ(_HV));});return new T2(0,_BD,_HU);}},_Ig=new T(function(){return eval("__strict(refresh)");}),_Ih=function(_Ii,_){var _Ij=__app0(E(_Ig)),_Ik=__app0(E(_Cs)),_Il=B(A(_Bn,[_AW,_zj,_Cp,_Ii,_])),_Im=B(_Gt(_Ii,_));return new T(function(){return E(E(_Im).b);});},_In=function(_Io,_){while(1){var _Ip=E(_Io);if(!_Ip._){return _BD;}else{var _Iq=_Ip.b,_Ir=E(_Ip.a);switch(_Ir._){case 0:var _Is=B(A1(_Ir.a,_));_Io=B(_f(_Iq,new T2(1,_Is,_o)));continue;case 1:_Io=B(_f(_Iq,_Ir.a));continue;default:_Io=_Iq;continue;}}}},_It=function(_Iu,_Iv,_){var _Iw=E(_Iu);switch(_Iw._){case 0:var _Ix=B(A1(_Iw.a,_));return new F(function(){return _In(B(_f(_Iv,new T2(1,_Ix,_o))),_);});break;case 1:return new F(function(){return _In(B(_f(_Iv,_Iw.a)),_);});break;default:return new F(function(){return _In(_Iv,_);});}},_Iy=function(_Iz,_IA,_IB){return new F(function(){return A1(_Iz,function(_IC){return new F(function(){return A2(_IA,_IC,_IB);});});});},_ID=function(_IE,_IF,_IG){var _IH=function(_II){var _IJ=new T(function(){return B(A1(_IG,_II));});return new F(function(){return A1(_IF,function(_IK){return E(_IJ);});});};return new F(function(){return A1(_IE,_IH);});},_IL=function(_IM,_IN,_IO){var _IP=new T(function(){return B(A1(_IN,function(_IQ){return new F(function(){return A1(_IO,_IQ);});}));});return new F(function(){return A1(_IM,function(_IR){return E(_IP);});});},_IS=function(_IT,_IU,_IV){var _IW=function(_IX){var _IY=function(_IZ){return new F(function(){return A1(_IV,new T(function(){return B(A1(_IX,_IZ));}));});};return new F(function(){return A1(_IU,_IY);});};return new F(function(){return A1(_IT,_IW);});},_J0=function(_J1,_J2){return new F(function(){return A1(_J2,_J1);});},_J3=function(_J4,_J5,_J6){var _J7=new T(function(){return B(A1(_J6,_J4));});return new F(function(){return A1(_J5,function(_J8){return E(_J7);});});},_J9=function(_Ja,_Jb,_Jc){var _Jd=function(_Je){return new F(function(){return A1(_Jc,new T(function(){return B(A1(_Ja,_Je));}));});};return new F(function(){return A1(_Jb,_Jd);});},_Jf=new T2(0,_J9,_J3),_Jg=new T5(0,_Jf,_J0,_IS,_IL,_ID),_Jh=function(_Ji){return E(E(_Ji).b);},_Jj=function(_Jk,_Jl){return new F(function(){return A3(_Jh,_Jm,_Jk,function(_Jn){return E(_Jl);});});},_Jo=function(_Jp){return new F(function(){return err(_Jp);});},_Jm=new T(function(){return new T5(0,_Jg,_Iy,_Jj,_J0,_Jo);}),_Jq=function(_Jr,_Js){return new T1(0,function(_){return new F(function(){return _z8(_Js,_Jr,_);});});},_Jt=new T2(0,_Jm,_Jq),_Ju=function(_Jv){return new T0(2);},_Jw=function(_Jx){var _Jy=new T(function(){return B(A1(_Jx,_Ju));}),_Jz=function(_JA){return new T1(1,new T2(1,new T(function(){return B(A1(_JA,_BD));}),new T2(1,_Jy,_o)));};return E(_Jz);},_JB=new T3(0,_Jt,_7S,_Jw),_JC=function(_){return new F(function(){return __jsNull();});},_JD=function(_JE){var _JF=B(A1(_JE,_));return E(_JF);},_JG=new T(function(){return B(_JD(_JC));}),_JH=new T(function(){return E(_JG);}),_JI=new T0(2),_JJ=function(_JK){return E(E(_JK).b);},_JL=function(_JM,_JN,_JO){var _JP=function(_JQ){var _JR=function(_){var _JS=E(_JN),_JT=rMV(_JS),_JU=E(_JT);if(!_JU._){var _JV=new T(function(){var _JW=new T(function(){return B(A1(_JQ,_BD));});return B(_f(_JU.b,new T2(1,new T2(0,_JO,function(_JX){return E(_JW);}),_o)));}),_=wMV(_JS,new T2(0,_JU.a,_JV));return _JI;}else{var _JY=E(_JU.a);if(!_JY._){var _=wMV(_JS,new T2(0,_JO,_o));return new T(function(){return B(A1(_JQ,_BD));});}else{var _=wMV(_JS,new T1(1,_JY.b));return new T1(1,new T2(1,new T(function(){return B(A1(_JQ,_BD));}),new T2(1,new T(function(){return B(A2(_JY.a,_JO,_Ju));}),_o)));}}};return new T1(0,_JR);};return new F(function(){return A2(_JJ,_JM,_JP);});},_JZ=new T(function(){return eval("window.requestAnimationFrame");}),_K0=new T1(1,_o),_K1=function(_K2,_K3){var _K4=function(_K5){var _K6=function(_){var _K7=E(_K3),_K8=rMV(_K7),_K9=E(_K8);if(!_K9._){var _Ka=_K9.a,_Kb=E(_K9.b);if(!_Kb._){var _=wMV(_K7,_K0);return new T(function(){return B(A1(_K5,_Ka));});}else{var _Kc=E(_Kb.a),_=wMV(_K7,new T2(0,_Kc.a,_Kb.b));return new T1(1,new T2(1,new T(function(){return B(A1(_K5,_Ka));}),new T2(1,new T(function(){return B(A1(_Kc.b,_Ju));}),_o)));}}else{var _Kd=new T(function(){var _Ke=function(_Kf){var _Kg=new T(function(){return B(A1(_K5,_Kf));});return function(_Kh){return E(_Kg);};};return B(_f(_K9.a,new T2(1,_Ke,_o)));}),_=wMV(_K7,new T1(1,_Kd));return _JI;}};return new T1(0,_K6);};return new F(function(){return A2(_JJ,_K2,_K4);});},_Ki=function(_Kj,_Kk){var _Kl=new T(function(){return B(A(_JL,[_JB,_Kj,_BD,_Ju]));});return function(_){var _Km=__createJSFunc(2,function(_Kn,_){var _Ko=B(_It(_Kl,_o,_));return _JH;}),_Kp=__app1(E(_JZ),_Km);return new T(function(){return B(A3(_K1,_JB,_Kj,_Kk));});};},_Kq=new T1(1,_o),_Kr=function(_Ks,_Kt,_){var _Ku=function(_){var _Kv=nMV(_Ks),_Kw=_Kv;return new T(function(){var _Kx=new T(function(){return B(_Ky(_));}),_Kz=function(_){var _KA=rMV(_Kw),_KB=B(A2(_Kt,_KA,_)),_=wMV(_Kw,_KB),_KC=function(_){var _KD=nMV(_Kq);return new T(function(){return new T1(0,B(_Ki(_KD,function(_KE){return E(_Kx);})));});};return new T1(0,_KC);},_KF=new T(function(){return new T1(0,_Kz);}),_Ky=function(_KG){return E(_KF);};return B(_Ky(_));});};return new F(function(){return _It(new T1(0,_Ku),_o,_);});},_KH=function(_){var _KI=__app2(E(_0),E(_7U),E(_he));return new F(function(){return _Kr(_yT,_Ih,_);});},_KJ=function(_){return new F(function(){return _KH(_);});};
var hasteMain = function() {B(A(_KJ, [0]));};window.onload = hasteMain;