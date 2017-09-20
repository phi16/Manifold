"use strict";
var __haste_prog_id = 'f9c691b15a2fbd5fec62ed151cfce88d3a0d22f07274709a1f1151d1a44cd8ec';
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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==( -2147483648)){_3l=new T1(1,I_fromInt( -2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return  -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0, -1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==( -2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return  -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S( -1021,53,_6k,_6l);});}else{return  -B(_5S( -1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=new T1(0,1),_7h=function(_7i){return E(E(_7i).a);},_7j=function(_7k){return E(E(_7k).a);},_7l=function(_7m){return E(E(_7m).c);},_7n=function(_7o,_7p,_7q,_7r,_7s,_7t,_7u){var _7v=B(_7j(B(_7h(_7o)))),_7w=new T(function(){return B(A3(_6I,_7v,new T(function(){return B(A3(_7l,_7v,_7p,_7s));}),new T(function(){return B(A3(_7l,_7v,_7q,_7t));})));});return new F(function(){return A3(_6I,_7v,_7w,new T(function(){return B(A3(_7l,_7v,_7r,_7u));}));});},_7x=function(_7y){return E(E(_7y).b);},_7z=function(_7A){return E(E(_7A).g);},_7B=function(_7C){return E(E(_7C).e);},_7D=function(_7E,_7F){var _7G=B(_7j(B(_7h(_7E)))),_7H=new T(function(){return B(A2(_7B,_7E,new T(function(){var _7I=E(_7F),_7J=_7I.a,_7K=_7I.b,_7L=_7I.c;return B(_7n(_7E,_7J,_7K,_7L,_7J,_7K,_7L));})));});return new F(function(){return A3(_7x,_7G,_7H,new T(function(){return B(A2(_7z,_7G,_7g));}));});},_7M=new T(function(){return B(unCStr("x"));}),_7N=new T1(0,_7M),_7O=new T(function(){return B(unCStr("y"));}),_7P=new T1(0,_7O),_7Q=new T(function(){return B(unCStr("z"));}),_7R=new T1(0,_7Q),_7S=new T3(0,E(_7N),E(_7P),E(_7R)),_7T=new T(function(){return B(_7D(_7f,_7S));}),_7U=function(_7V){return E(_7V);},_7W=new T(function(){return toJSStr(B(_5(_p,_7U,_7T)));}),_7X=function(_7Y,_7Z,_80){var _81=new T(function(){return B(_1(_7Y));}),_82=new T(function(){return B(_3(_7Y));}),_83=function(_84){var _85=E(_84);if(!_85._){return E(_82);}else{return new F(function(){return A2(_81,new T(function(){return B(_5(_7Y,_7Z,_85.a));}),new T(function(){return B(_83(_85.b));}));});}};return new F(function(){return _83(_80);});},_86=new T(function(){return B(unCStr("(/=) is not defined"));}),_87=new T(function(){return B(err(_86));}),_88=new T(function(){return B(unCStr("(==) is not defined"));}),_89=new T(function(){return B(err(_88));}),_8a=new T2(0,_89,_87),_8b=new T(function(){return B(unCStr("(<) is not defined"));}),_8c=new T(function(){return B(err(_8b));}),_8d=new T(function(){return B(unCStr("(<=) is not defined"));}),_8e=new T(function(){return B(err(_8d));}),_8f=new T(function(){return B(unCStr("(>) is not defined"));}),_8g=new T(function(){return B(err(_8f));}),_8h=new T(function(){return B(unCStr("(>=) is not defined"));}),_8i=new T(function(){return B(err(_8h));}),_8j=new T(function(){return B(unCStr("compare is not defined"));}),_8k=new T(function(){return B(err(_8j));}),_8l=new T(function(){return B(unCStr("max("));}),_8m=new T1(0,_8l),_8n=function(_8o,_8p){return new T1(1,new T2(1,_8m,new T2(1,_8o,new T2(1,_r,new T2(1,_8p,_w)))));},_8q=new T(function(){return B(unCStr("min("));}),_8r=new T1(0,_8q),_8s=function(_8t,_8u){return new T1(1,new T2(1,_8r,new T2(1,_8t,new T2(1,_r,new T2(1,_8u,_w)))));},_8v={_:0,a:_8a,b:_8k,c:_8c,d:_8e,e:_8g,f:_8i,g:_8n,h:_8s},_8w=new T2(0,_7f,_8v),_8x=function(_8y,_8z){var _8A=E(_8y);return E(_8z);},_8B=function(_8C,_8D){var _8E=E(_8D);return E(_8C);},_8F=function(_8G,_8H){var _8I=E(_8G),_8J=E(_8H);return new T3(0,E(B(A1(_8I.a,_8J.a))),E(B(A1(_8I.b,_8J.b))),E(B(A1(_8I.c,_8J.c))));},_8K=function(_8L,_8M,_8N){return new T3(0,E(_8L),E(_8M),E(_8N));},_8O=function(_8P){return new F(function(){return _8K(_8P,_8P,_8P);});},_8Q=function(_8R,_8S){var _8T=E(_8S),_8U=E(_8R);return new T3(0,E(_8U),E(_8U),E(_8U));},_8V=function(_8W,_8X){var _8Y=E(_8X);return new T3(0,E(B(A1(_8W,_8Y.a))),E(B(A1(_8W,_8Y.b))),E(B(A1(_8W,_8Y.c))));},_8Z=new T2(0,_8V,_8Q),_90=new T5(0,_8Z,_8O,_8F,_8x,_8B),_91=new T1(0,0),_92=function(_93){var _94=B(A2(_7z,_93,_7g)),_95=B(A2(_7z,_93,_91));return new T3(0,E(new T3(0,E(_94),E(_95),E(_95))),E(new T3(0,E(_95),E(_94),E(_95))),E(new T3(0,E(_95),E(_95),E(_94))));},_96=function(_97){return E(E(_97).a);},_98=function(_99){return E(E(_99).f);},_9a=function(_9b){return E(E(_9b).b);},_9c=function(_9d){return E(E(_9d).c);},_9e=function(_9f){return E(E(_9f).a);},_9g=function(_9h){return E(E(_9h).d);},_9i=function(_9j,_9k,_9l,_9m,_9n){var _9o=new T(function(){return E(E(E(_9j).c).a);}),_9p=new T(function(){var _9q=E(_9j).a,_9r=new T(function(){var _9s=new T(function(){return B(_7h(_9o));}),_9t=new T(function(){return B(_7j(_9s));}),_9u=new T(function(){return B(A2(_9g,_9o,_9k));}),_9v=new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9w=function(_9x,_9y){var _9z=new T(function(){var _9A=new T(function(){return B(A3(_9a,_9s,new T(function(){return B(A3(_7l,_9t,_9m,_9x));}),_9k));});return B(A3(_6I,_9t,_9A,new T(function(){return B(A3(_7l,_9t,_9y,_9u));})));});return new F(function(){return A3(_7l,_9t,_9v,_9z);});};return B(A3(_9e,B(_96(_9q)),_9w,_9l));});return B(A3(_9c,_9q,_9r,_9n));});return new T2(0,new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9p);},_9B=function(_9C,_9D,_9E,_9F){var _9G=E(_9E),_9H=E(_9F),_9I=B(_9i(_9D,_9G.a,_9G.b,_9H.a,_9H.b));return new T2(0,_9I.a,_9I.b);},_9J=new T1(0,1),_9K=function(_9L){return E(E(_9L).l);},_9M=function(_9N,_9O,_9P){var _9Q=new T(function(){return E(E(E(_9N).c).a);}),_9R=new T(function(){var _9S=new T(function(){return B(_7h(_9Q));}),_9T=new T(function(){var _9U=B(_7j(_9S)),_9V=new T(function(){var _9W=new T(function(){return B(A3(_7x,_9U,new T(function(){return B(A2(_7z,_9U,_9J));}),new T(function(){return B(A3(_7l,_9U,_9O,_9O));})));});return B(A2(_7B,_9Q,_9W));});return B(A2(_6K,_9U,_9V));});return B(A3(_9e,B(_96(E(_9N).a)),function(_9X){return new F(function(){return A3(_9a,_9S,_9X,_9T);});},_9P));});return new T2(0,new T(function(){return B(A2(_9K,_9Q,_9O));}),_9R);},_9Y=function(_9Z,_a0,_a1){var _a2=E(_a1),_a3=B(_9M(_a0,_a2.a,_a2.b));return new T2(0,_a3.a,_a3.b);},_a4=function(_a5){return E(E(_a5).r);},_a6=function(_a7,_a8,_a9){var _aa=new T(function(){return E(E(E(_a7).c).a);}),_ab=new T(function(){var _ac=new T(function(){return B(_7h(_aa));}),_ad=new T(function(){var _ae=new T(function(){var _af=B(_7j(_ac));return B(A3(_7x,_af,new T(function(){return B(A3(_7l,_af,_a8,_a8));}),new T(function(){return B(A2(_7z,_af,_9J));})));});return B(A2(_7B,_aa,_ae));});return B(A3(_9e,B(_96(E(_a7).a)),function(_ag){return new F(function(){return A3(_9a,_ac,_ag,_ad);});},_a9));});return new T2(0,new T(function(){return B(A2(_a4,_aa,_a8));}),_ab);},_ah=function(_ai,_aj,_ak){var _al=E(_ak),_am=B(_a6(_aj,_al.a,_al.b));return new T2(0,_am.a,_am.b);},_an=function(_ao){return E(E(_ao).k);},_ap=function(_aq,_ar,_as){var _at=new T(function(){return E(E(E(_aq).c).a);}),_au=new T(function(){var _av=new T(function(){return B(_7h(_at));}),_aw=new T(function(){var _ax=new T(function(){var _ay=B(_7j(_av));return B(A3(_7x,_ay,new T(function(){return B(A2(_7z,_ay,_9J));}),new T(function(){return B(A3(_7l,_ay,_ar,_ar));})));});return B(A2(_7B,_at,_ax));});return B(A3(_9e,B(_96(E(_aq).a)),function(_az){return new F(function(){return A3(_9a,_av,_az,_aw);});},_as));});return new T2(0,new T(function(){return B(A2(_an,_at,_ar));}),_au);},_aA=function(_aB,_aC,_aD){var _aE=E(_aD),_aF=B(_ap(_aC,_aE.a,_aE.b));return new T2(0,_aF.a,_aF.b);},_aG=function(_aH){return E(E(_aH).q);},_aI=function(_aJ,_aK,_aL){var _aM=new T(function(){return E(E(E(_aJ).c).a);}),_aN=new T(function(){var _aO=new T(function(){return B(_7h(_aM));}),_aP=new T(function(){var _aQ=new T(function(){var _aR=B(_7j(_aO));return B(A3(_6I,_aR,new T(function(){return B(A3(_7l,_aR,_aK,_aK));}),new T(function(){return B(A2(_7z,_aR,_9J));})));});return B(A2(_7B,_aM,_aQ));});return B(A3(_9e,B(_96(E(_aJ).a)),function(_aS){return new F(function(){return A3(_9a,_aO,_aS,_aP);});},_aL));});return new T2(0,new T(function(){return B(A2(_aG,_aM,_aK));}),_aN);},_aT=function(_aU,_aV,_aW){var _aX=E(_aW),_aY=B(_aI(_aV,_aX.a,_aX.b));return new T2(0,_aY.a,_aY.b);},_aZ=function(_b0){return E(E(_b0).m);},_b1=function(_b2,_b3,_b4){var _b5=new T(function(){return E(E(E(_b2).c).a);}),_b6=new T(function(){var _b7=new T(function(){return B(_7h(_b5));}),_b8=new T(function(){var _b9=B(_7j(_b7));return B(A3(_6I,_b9,new T(function(){return B(A2(_7z,_b9,_9J));}),new T(function(){return B(A3(_7l,_b9,_b3,_b3));})));});return B(A3(_9e,B(_96(E(_b2).a)),function(_ba){return new F(function(){return A3(_9a,_b7,_ba,_b8);});},_b4));});return new T2(0,new T(function(){return B(A2(_aZ,_b5,_b3));}),_b6);},_bb=function(_bc,_bd,_be){var _bf=E(_be),_bg=B(_b1(_bd,_bf.a,_bf.b));return new T2(0,_bg.a,_bg.b);},_bh=function(_bi){return E(E(_bi).s);},_bj=function(_bk,_bl,_bm){var _bn=new T(function(){return E(E(E(_bk).c).a);}),_bo=new T(function(){var _bp=new T(function(){return B(_7h(_bn));}),_bq=new T(function(){var _br=B(_7j(_bp));return B(A3(_7x,_br,new T(function(){return B(A2(_7z,_br,_9J));}),new T(function(){return B(A3(_7l,_br,_bl,_bl));})));});return B(A3(_9e,B(_96(E(_bk).a)),function(_bs){return new F(function(){return A3(_9a,_bp,_bs,_bq);});},_bm));});return new T2(0,new T(function(){return B(A2(_bh,_bn,_bl));}),_bo);},_bt=function(_bu,_bv,_bw){var _bx=E(_bw),_by=B(_bj(_bv,_bx.a,_bx.b));return new T2(0,_by.a,_by.b);},_bz=function(_bA){return E(E(_bA).i);},_bB=function(_bC){return E(E(_bC).h);},_bD=function(_bE,_bF,_bG){var _bH=new T(function(){return E(E(E(_bE).c).a);}),_bI=new T(function(){var _bJ=new T(function(){return B(_7j(new T(function(){return B(_7h(_bH));})));}),_bK=new T(function(){return B(A2(_6K,_bJ,new T(function(){return B(A2(_bB,_bH,_bF));})));});return B(A3(_9e,B(_96(E(_bE).a)),function(_bL){return new F(function(){return A3(_7l,_bJ,_bL,_bK);});},_bG));});return new T2(0,new T(function(){return B(A2(_bz,_bH,_bF));}),_bI);},_bM=function(_bN,_bO,_bP){var _bQ=E(_bP),_bR=B(_bD(_bO,_bQ.a,_bQ.b));return new T2(0,_bR.a,_bR.b);},_bS=function(_bT){return E(E(_bT).o);},_bU=function(_bV){return E(E(_bV).n);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_7j(new T(function(){return B(_7h(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_9e,B(_96(E(_bX).a)),function(_c4){return new F(function(){return A3(_7l,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bS,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc){return E(E(_cc).c);},_cd=function(_ce,_cf,_cg){var _ch=new T(function(){return E(E(E(_ce).c).a);}),_ci=new T(function(){var _cj=new T(function(){return B(_7j(new T(function(){return B(_7h(_ch));})));}),_ck=new T(function(){return B(A2(_cb,_ch,_cf));});return B(A3(_9e,B(_96(E(_ce).a)),function(_cl){return new F(function(){return A3(_7l,_cj,_cl,_ck);});},_cg));});return new T2(0,new T(function(){return B(A2(_cb,_ch,_cf));}),_ci);},_cm=function(_cn,_co,_cp){var _cq=E(_cp),_cr=B(_cd(_co,_cq.a,_cq.b));return new T2(0,_cr.a,_cr.b);},_cs=function(_ct,_cu,_cv){var _cw=new T(function(){return E(E(E(_ct).c).a);}),_cx=new T(function(){var _cy=new T(function(){return B(_7h(_cw));}),_cz=new T(function(){return B(_7j(_cy));}),_cA=new T(function(){return B(A3(_9a,_cy,new T(function(){return B(A2(_7z,_cz,_9J));}),_cu));});return B(A3(_9e,B(_96(E(_ct).a)),function(_cB){return new F(function(){return A3(_7l,_cz,_cB,_cA);});},_cv));});return new T2(0,new T(function(){return B(A2(_9g,_cw,_cu));}),_cx);},_cC=function(_cD,_cE,_cF){var _cG=E(_cF),_cH=B(_cs(_cE,_cG.a,_cG.b));return new T2(0,_cH.a,_cH.b);},_cI=function(_cJ,_cK,_cL,_cM){var _cN=new T(function(){return E(E(_cK).c);}),_cO=new T3(0,new T(function(){return E(E(_cK).a);}),new T(function(){return E(E(_cK).b);}),new T2(0,new T(function(){return E(E(_cN).a);}),new T(function(){return E(E(_cN).b);})));return new F(function(){return A3(_9a,_cJ,new T(function(){var _cP=E(_cM),_cQ=B(_cs(_cO,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);}),new T(function(){var _cR=E(_cL),_cS=B(_cs(_cO,_cR.a,_cR.b));return new T2(0,_cS.a,_cS.b);}));});},_cT=new T1(0,0),_cU=function(_cV){return E(E(_cV).b);},_cW=function(_cX){return E(E(_cX).b);},_cY=function(_cZ){var _d0=new T(function(){return E(E(E(_cZ).c).a);}),_d1=new T(function(){return B(A2(_cW,E(_cZ).a,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_d0)))),_cT));})));});return new T2(0,new T(function(){return B(_cU(_d0));}),_d1);},_d2=function(_d3,_d4){var _d5=B(_cY(_d4));return new T2(0,_d5.a,_d5.b);},_d6=function(_d7,_d8,_d9){var _da=new T(function(){return E(E(E(_d7).c).a);}),_db=new T(function(){var _dc=new T(function(){return B(_7j(new T(function(){return B(_7h(_da));})));}),_dd=new T(function(){return B(A2(_bz,_da,_d8));});return B(A3(_9e,B(_96(E(_d7).a)),function(_de){return new F(function(){return A3(_7l,_dc,_de,_dd);});},_d9));});return new T2(0,new T(function(){return B(A2(_bB,_da,_d8));}),_db);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d6(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm,_dn,_do){var _dp=new T(function(){return E(E(E(_dm).c).a);}),_dq=new T(function(){var _dr=new T(function(){return B(_7j(new T(function(){return B(_7h(_dp));})));}),_ds=new T(function(){return B(A2(_bS,_dp,_dn));});return B(A3(_9e,B(_96(E(_dm).a)),function(_dt){return new F(function(){return A3(_7l,_dr,_dt,_ds);});},_do));});return new T2(0,new T(function(){return B(A2(_bU,_dp,_dn));}),_dq);},_du=function(_dv,_dw,_dx){var _dy=E(_dx),_dz=B(_dl(_dw,_dy.a,_dy.b));return new T2(0,_dz.a,_dz.b);},_dA=new T1(0,2),_dB=function(_dC,_dD,_dE){var _dF=new T(function(){return E(E(E(_dC).c).a);}),_dG=new T(function(){var _dH=new T(function(){return B(_7h(_dF));}),_dI=new T(function(){return B(_7j(_dH));}),_dJ=new T(function(){var _dK=new T(function(){return B(A3(_9a,_dH,new T(function(){return B(A2(_7z,_dI,_9J));}),new T(function(){return B(A2(_7z,_dI,_dA));})));});return B(A3(_9a,_dH,_dK,new T(function(){return B(A2(_7B,_dF,_dD));})));});return B(A3(_9e,B(_96(E(_dC).a)),function(_dL){return new F(function(){return A3(_7l,_dI,_dL,_dJ);});},_dE));});return new T2(0,new T(function(){return B(A2(_7B,_dF,_dD));}),_dG);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dP),_dR=B(_dB(_dO,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);},_dS=function(_dT){return E(E(_dT).j);},_dU=function(_dV,_dW,_dX){var _dY=new T(function(){return E(E(E(_dV).c).a);}),_dZ=new T(function(){var _e0=new T(function(){return B(_7h(_dY));}),_e1=new T(function(){var _e2=new T(function(){return B(A2(_bz,_dY,_dW));});return B(A3(_7l,B(_7j(_e0)),_e2,_e2));});return B(A3(_9e,B(_96(E(_dV).a)),function(_e3){return new F(function(){return A3(_9a,_e0,_e3,_e1);});},_dX));});return new T2(0,new T(function(){return B(A2(_dS,_dY,_dW));}),_dZ);},_e4=function(_e5,_e6,_e7){var _e8=E(_e7),_e9=B(_dU(_e6,_e8.a,_e8.b));return new T2(0,_e9.a,_e9.b);},_ea=function(_eb){return E(E(_eb).p);},_ec=function(_ed,_ee,_ef){var _eg=new T(function(){return E(E(E(_ed).c).a);}),_eh=new T(function(){var _ei=new T(function(){return B(_7h(_eg));}),_ej=new T(function(){var _ek=new T(function(){return B(A2(_bS,_eg,_ee));});return B(A3(_7l,B(_7j(_ei)),_ek,_ek));});return B(A3(_9e,B(_96(E(_ed).a)),function(_el){return new F(function(){return A3(_9a,_ei,_el,_ej);});},_ef));});return new T2(0,new T(function(){return B(A2(_ea,_eg,_ee));}),_eh);},_em=function(_en,_eo,_ep){var _eq=E(_ep),_er=B(_ec(_eo,_eq.a,_eq.b));return new T2(0,_er.a,_er.b);},_es=function(_et,_eu){return {_:0,a:_et,b:new T(function(){return B(_d2(_et,_eu));}),c:function(_ev){return new F(function(){return _cm(_et,_eu,_ev);});},d:function(_ev){return new F(function(){return _cC(_et,_eu,_ev);});},e:function(_ev){return new F(function(){return _dM(_et,_eu,_ev);});},f:function(_ew,_ev){return new F(function(){return _9B(_et,_eu,_ew,_ev);});},g:function(_ew,_ev){return new F(function(){return _cI(_et,_eu,_ew,_ev);});},h:function(_ev){return new F(function(){return _df(_et,_eu,_ev);});},i:function(_ev){return new F(function(){return _bM(_et,_eu,_ev);});},j:function(_ev){return new F(function(){return _e4(_et,_eu,_ev);});},k:function(_ev){return new F(function(){return _aA(_et,_eu,_ev);});},l:function(_ev){return new F(function(){return _9Y(_et,_eu,_ev);});},m:function(_ev){return new F(function(){return _bb(_et,_eu,_ev);});},n:function(_ev){return new F(function(){return _du(_et,_eu,_ev);});},o:function(_ev){return new F(function(){return _c5(_et,_eu,_ev);});},p:function(_ev){return new F(function(){return _em(_et,_eu,_ev);});},q:function(_ev){return new F(function(){return _aT(_et,_eu,_ev);});},r:function(_ev){return new F(function(){return _ah(_et,_eu,_ev);});},s:function(_ev){return new F(function(){return _bt(_et,_eu,_ev);});}};},_ex=function(_ey,_ez,_eA,_eB,_eC){var _eD=new T(function(){return B(_7h(new T(function(){return E(E(E(_ey).c).a);})));}),_eE=new T(function(){var _eF=E(_ey).a,_eG=new T(function(){var _eH=new T(function(){return B(_7j(_eD));}),_eI=new T(function(){return B(A3(_7l,_eH,_eB,_eB));}),_eJ=function(_eK,_eL){var _eM=new T(function(){return B(A3(_7x,_eH,new T(function(){return B(A3(_7l,_eH,_eK,_eB));}),new T(function(){return B(A3(_7l,_eH,_ez,_eL));})));});return new F(function(){return A3(_9a,_eD,_eM,_eI);});};return B(A3(_9e,B(_96(_eF)),_eJ,_eA));});return B(A3(_9c,_eF,_eG,_eC));});return new T2(0,new T(function(){return B(A3(_9a,_eD,_ez,_eB));}),_eE);},_eN=function(_eO,_eP,_eQ,_eR){var _eS=E(_eQ),_eT=E(_eR),_eU=B(_ex(_eP,_eS.a,_eS.b,_eT.a,_eT.b));return new T2(0,_eU.a,_eU.b);},_eV=function(_eW){return E(E(_eW).d);},_eX=function(_eY,_eZ){var _f0=new T(function(){return B(_7h(new T(function(){return E(E(E(_eY).c).a);})));}),_f1=new T(function(){return B(A2(_cW,E(_eY).a,new T(function(){return B(A2(_7z,B(_7j(_f0)),_cT));})));});return new T2(0,new T(function(){return B(A2(_eV,_f0,_eZ));}),_f1);},_f2=function(_f3,_f4,_f5){var _f6=B(_eX(_f4,_f5));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return B(_7h(new T(function(){return E(E(E(_f8).c).a);})));}),_fc=new T(function(){return B(_7j(_fb));}),_fd=new T(function(){var _fe=new T(function(){var _ff=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),new T(function(){return B(A3(_7l,_fc,_f9,_f9));})));});return B(A2(_6K,_fc,_ff));});return B(A3(_9e,B(_96(E(_f8).a)),function(_fg){return new F(function(){return A3(_7l,_fc,_fg,_fe);});},_fa));}),_fh=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),_f9));});return new T2(0,_fh,_fd);},_fi=function(_fj,_fk,_fl){var _fm=E(_fl),_fn=B(_f7(_fk,_fm.a,_fm.b));return new T2(0,_fn.a,_fn.b);},_fo=function(_fp,_fq){return new T4(0,_fp,function(_ew,_ev){return new F(function(){return _eN(_fp,_fq,_ew,_ev);});},function(_ev){return new F(function(){return _fi(_fp,_fq,_ev);});},function(_ev){return new F(function(){return _f2(_fp,_fq,_ev);});});},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fs).c).a);})));})));}),_fy=new T(function(){var _fz=E(_fs).a,_fA=new T(function(){var _fB=function(_fC,_fD){return new F(function(){return A3(_6I,_fx,new T(function(){return B(A3(_7l,_fx,_ft,_fD));}),new T(function(){return B(A3(_7l,_fx,_fC,_fv));}));});};return B(A3(_9e,B(_96(_fz)),_fB,_fu));});return B(A3(_9c,_fz,_fA,_fw));});return new T2(0,new T(function(){return B(A3(_7l,_fx,_ft,_fv));}),_fy);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fr(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO,_fP,_fQ){var _fR=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fM).c).a);})));})));}),_fS=new T(function(){var _fT=E(_fM).a,_fU=new T(function(){return B(A3(_9e,B(_96(_fT)),new T(function(){return B(_6I(_fR));}),_fO));});return B(A3(_9c,_fT,_fU,_fQ));});return new T2(0,new T(function(){return B(A3(_6I,_fR,_fN,_fP));}),_fS);},_fV=function(_fW,_fX,_fY){var _fZ=E(_fX),_g0=E(_fY),_g1=B(_fL(_fW,_fZ.a,_fZ.b,_g0.a,_g0.b));return new T2(0,_g1.a,_g1.b);},_g2=function(_g3,_g4,_g5){var _g6=B(_g7(_g3));return new F(function(){return A3(_6I,_g6,_g4,new T(function(){return B(A2(_6K,_g6,_g5));}));});},_g8=function(_g9){return E(E(_g9).e);},_ga=function(_gb){return E(E(_gb).f);},_gc=function(_gd,_ge,_gf){var _gg=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gd).c).a);})));})));}),_gh=new T(function(){var _gi=new T(function(){return B(A2(_ga,_gg,_ge));});return B(A3(_9e,B(_96(E(_gd).a)),function(_gj){return new F(function(){return A3(_7l,_gg,_gj,_gi);});},_gf));});return new T2(0,new T(function(){return B(A2(_g8,_gg,_ge));}),_gh);},_gk=function(_gl,_gm){var _gn=E(_gm),_go=B(_gc(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr){var _gs=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gq).c).a);})));})));}),_gt=new T(function(){return B(A2(_cW,E(_gq).a,new T(function(){return B(A2(_7z,_gs,_cT));})));});return new T2(0,new T(function(){return B(A2(_7z,_gs,_gr));}),_gt);},_gu=function(_gv,_gw){var _gx=B(_gp(_gv,_gw));return new T2(0,_gx.a,_gx.b);},_gy=function(_gz,_gA,_gB){var _gC=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gz).c).a);})));})));}),_gD=new T(function(){return B(A3(_9e,B(_96(E(_gz).a)),new T(function(){return B(_6K(_gC));}),_gB));});return new T2(0,new T(function(){return B(A2(_6K,_gC,_gA));}),_gD);},_gE=function(_gF,_gG){var _gH=E(_gG),_gI=B(_gy(_gF,_gH.a,_gH.b));return new T2(0,_gI.a,_gI.b);},_gJ=function(_gK,_gL){var _gM=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gK).c).a);})));})));}),_gN=new T(function(){return B(A2(_cW,E(_gK).a,new T(function(){return B(A2(_7z,_gM,_cT));})));});return new T2(0,new T(function(){return B(A2(_ga,_gM,_gL));}),_gN);},_gO=function(_gP,_gQ){var _gR=B(_gJ(_gP,E(_gQ).a));return new T2(0,_gR.a,_gR.b);},_g7=function(_gS){return {_:0,a:function(_ew,_ev){return new F(function(){return _fV(_gS,_ew,_ev);});},b:function(_ew,_ev){return new F(function(){return _g2(_gS,_ew,_ev);});},c:function(_ew,_ev){return new F(function(){return _fE(_gS,_ew,_ev);});},d:function(_ev){return new F(function(){return _gE(_gS,_ev);});},e:function(_ev){return new F(function(){return _gk(_gS,_ev);});},f:function(_ev){return new F(function(){return _gO(_gS,_ev);});},g:function(_ev){return new F(function(){return _gu(_gS,_ev);});}};},_gT=function(_gU){var _gV=new T(function(){return E(E(_gU).a);}),_gW=new T3(0,_90,_92,new T2(0,_gV,new T(function(){return E(E(_gU).b);}))),_gX=new T(function(){return B(_es(new T(function(){return B(_fo(new T(function(){return B(_g7(_gW));}),_gW));}),_gW));}),_gY=new T(function(){return B(_7j(new T(function(){return B(_7h(_gV));})));}),_gZ=function(_h0){return E(B(_7D(_gX,new T(function(){var _h1=E(_h0),_h2=B(A2(_7z,_gY,_7g)),_h3=B(A2(_7z,_gY,_91));return new T3(0,E(new T2(0,_h1.a,new T3(0,E(_h2),E(_h3),E(_h3)))),E(new T2(0,_h1.b,new T3(0,E(_h3),E(_h2),E(_h3)))),E(new T2(0,_h1.c,new T3(0,E(_h3),E(_h3),E(_h2)))));}))).b);};return E(_gZ);},_h4=new T(function(){return B(_gT(_8w));}),_h5=function(_h6,_h7){var _h8=E(_h7);return (_h8._==0)?__Z:new T2(1,_h6,new T2(1,_h8.a,new T(function(){return B(_h5(_h6,_h8.b));})));},_h9=new T(function(){var _ha=B(A1(_h4,_7S));return new T2(1,_ha.a,new T(function(){return B(_h5(_r,new T2(1,_ha.b,new T2(1,_ha.c,_o))));}));}),_hb=new T1(1,_h9),_hc=new T2(1,_hb,_w),_hd=new T(function(){return B(unCStr("vec3("));}),_he=new T1(0,_hd),_hf=new T2(1,_he,_hc),_hg=new T(function(){return toJSStr(B(_7X(_p,_7U,_hf)));}),_hh=function(_hi,_hj){while(1){var _hk=E(_hi);if(!_hk._){return E(_hj);}else{var _hl=_hj+1|0;_hi=_hk.b;_hj=_hl;continue;}}},_hm=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hn=new T(function(){return B(err(_hm));}),_ho=0,_hp=new T3(0,E(_ho),E(_ho),E(_ho)),_hq=new T(function(){return B(unCStr("Negative exponent"));}),_hr=new T(function(){return B(err(_hq));}),_hs=function(_ht,_hu,_hv){while(1){if(!(_hu%2)){var _hw=_ht*_ht,_hx=quot(_hu,2);_ht=_hw;_hu=_hx;continue;}else{var _hy=E(_hu);if(_hy==1){return _ht*_hv;}else{var _hw=_ht*_ht,_hz=_ht*_hv;_ht=_hw;_hu=quot(_hy-1|0,2);_hv=_hz;continue;}}}},_hA=function(_hB,_hC){while(1){if(!(_hC%2)){var _hD=_hB*_hB,_hE=quot(_hC,2);_hB=_hD;_hC=_hE;continue;}else{var _hF=E(_hC);if(_hF==1){return E(_hB);}else{return new F(function(){return _hs(_hB*_hB,quot(_hF-1|0,2),_hB);});}}}},_hG=function(_hH){var _hI=E(_hH);return new F(function(){return Math.log(_hI+(_hI+1)*Math.sqrt((_hI-1)/(_hI+1)));});},_hJ=function(_hK){var _hL=E(_hK);return new F(function(){return Math.log(_hL+Math.sqrt(1+_hL*_hL));});},_hM=function(_hN){var _hO=E(_hN);return 0.5*Math.log((1+_hO)/(1-_hO));},_hP=function(_hQ,_hR){return Math.log(E(_hR))/Math.log(E(_hQ));},_hS=3.141592653589793,_hT=function(_hU){var _hV=E(_hU);return new F(function(){return _6j(_hV.a,_hV.b);});},_hW=function(_hX){return 1/E(_hX);},_hY=function(_hZ){var _i0=E(_hZ),_i1=E(_i0);return (_i1==0)?E(_6i):(_i1<=0)? -_i1:E(_i0);},_i2=function(_i3){var _i4=E(_i3);if(!_i4._){return _i4.a;}else{return new F(function(){return I_toNumber(_i4.a);});}},_i5=function(_i6){return new F(function(){return _i2(_i6);});},_i7=1,_i8= -1,_i9=function(_ia){var _ib=E(_ia);return (_ib<=0)?(_ib>=0)?E(_ib):E(_i8):E(_i7);},_ic=function(_id,_ie){return E(_id)-E(_ie);},_if=function(_ig){return  -E(_ig);},_ih=function(_ii,_ij){return E(_ii)+E(_ij);},_ik=function(_il,_im){return E(_il)*E(_im);},_in={_:0,a:_ih,b:_ic,c:_ik,d:_if,e:_hY,f:_i9,g:_i5},_io=function(_ip,_iq){return E(_ip)/E(_iq);},_ir=new T4(0,_in,_io,_hW,_hT),_is=function(_it){return new F(function(){return Math.acos(E(_it));});},_iu=function(_iv){return new F(function(){return Math.asin(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.atan(E(_ix));});},_iy=function(_iz){return new F(function(){return Math.cos(E(_iz));});},_iA=function(_iB){return new F(function(){return cosh(E(_iB));});},_iC=function(_iD){return new F(function(){return Math.exp(E(_iD));});},_iE=function(_iF){return new F(function(){return Math.log(E(_iF));});},_iG=function(_iH,_iI){return new F(function(){return Math.pow(E(_iH),E(_iI));});},_iJ=function(_iK){return new F(function(){return Math.sin(E(_iK));});},_iL=function(_iM){return new F(function(){return sinh(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.sqrt(E(_iO));});},_iP=function(_iQ){return new F(function(){return Math.tan(E(_iQ));});},_iR=function(_iS){return new F(function(){return tanh(E(_iS));});},_iT={_:0,a:_ir,b:_hS,c:_iC,d:_iE,e:_iN,f:_iG,g:_hP,h:_iJ,i:_iy,j:_iP,k:_iu,l:_is,m:_iw,n:_iL,o:_iA,p:_iR,q:_hJ,r:_hG,s:_hM},_iU=function(_iV,_iW){return (E(_iV)!=E(_iW))?true:false;},_iX=function(_iY,_iZ){return E(_iY)==E(_iZ);},_j0=new T2(0,_iX,_iU),_j1=function(_j2,_j3){return E(_j2)<E(_j3);},_j4=function(_j5,_j6){return E(_j5)<=E(_j6);},_j7=function(_j8,_j9){return E(_j8)>E(_j9);},_ja=function(_jb,_jc){return E(_jb)>=E(_jc);},_jd=function(_je,_jf){var _jg=E(_je),_jh=E(_jf);return (_jg>=_jh)?(_jg!=_jh)?2:1:0;},_ji=function(_jj,_jk){var _jl=E(_jj),_jm=E(_jk);return (_jl>_jm)?E(_jl):E(_jm);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=E(_jp);return (_jq>_jr)?E(_jr):E(_jq);},_js={_:0,a:_j0,b:_jd,c:_j1,d:_j4,e:_j7,f:_ja,g:_ji,h:_jn},_jt="t",_ju="a",_jv="r",_jw="ly",_jx="lx",_jy="wz",_jz="wy",_jA="wx",_jB=0,_jC=function(_jD){var _jE=__new(),_jF=_jE,_jG=function(_jH,_){while(1){var _jI=E(_jH);if(!_jI._){return _jB;}else{var _jJ=E(_jI.a),_jK=__set(_jF,E(_jJ.a),E(_jJ.b));_jH=_jI.b;continue;}}},_jL=B(_jG(_jD,_));return E(_jF);},_jM=function(_jN,_jO,_jP,_jQ,_jR,_jS){return new F(function(){return _jC(new T2(1,new T2(0,_jA,_jN),new T2(1,new T2(0,_jz,_jO),new T2(1,new T2(0,_jy,_jP),new T2(1,new T2(0,_jx,_jQ*_jR*Math.cos(_jS)),new T2(1,new T2(0,_jw,_jQ*_jR*Math.sin(_jS)),new T2(1,new T2(0,_jv,_jQ),new T2(1,new T2(0,_ju,_jR),new T2(1,new T2(0,_jt,_jS),_o)))))))));});},_jT=function(_jU){var _jV=E(_jU),_jW=E(_jV.a),_jX=E(_jV.b);return new F(function(){return _jM(_jW.a,_jW.b,_jW.c,E(_jX.a),E(_jX.b),E(_jV.c));});},_jY=function(_jZ,_k0){var _k1=E(_k0);return (_k1._==0)?__Z:new T2(1,new T(function(){return B(A1(_jZ,_k1.a));}),new T(function(){return B(_jY(_jZ,_k1.b));}));},_k2=function(_k3,_k4,_k5){var _k6=__lst2arr(B(_jY(_jT,new T2(1,_k3,new T2(1,_k4,new T2(1,_k5,_o))))));return E(_k6);},_k7=function(_k8){var _k9=E(_k8);return new F(function(){return _k2(_k9.a,_k9.b,_k9.c);});},_ka=new T2(0,_iT,_js),_kb=function(_kc,_kd,_ke,_kf){var _kg=B(_7h(_kc)),_kh=new T(function(){return B(A2(_7B,_kc,new T(function(){return B(_7n(_kc,_kd,_ke,_kf,_kd,_ke,_kf));})));});return new T3(0,B(A3(_9a,_kg,_kd,_kh)),B(A3(_9a,_kg,_ke,_kh)),B(A3(_9a,_kg,_kf,_kh)));},_ki=function(_kj,_kk,_kl,_km,_kn,_ko,_kp){var _kq=B(_7l(_kj));return new T3(0,B(A1(B(A1(_kq,_kk)),_kn)),B(A1(B(A1(_kq,_kl)),_ko)),B(A1(B(A1(_kq,_km)),_kp)));},_kr=function(_ks,_kt,_ku,_kv,_kw,_kx,_ky){var _kz=B(_6I(_ks));return new T3(0,B(A1(B(A1(_kz,_kt)),_kw)),B(A1(B(A1(_kz,_ku)),_kx)),B(A1(B(A1(_kz,_kv)),_ky)));},_kA=function(_kB,_kC){var _kD=new T(function(){return E(E(_kB).a);}),_kE=new T(function(){return B(A2(_gT,new T2(0,_kD,new T(function(){return E(E(_kB).b);})),_kC));}),_kF=new T(function(){var _kG=E(_kE),_kH=B(_kb(_kD,_kG.a,_kG.b,_kG.c));return new T3(0,E(_kH.a),E(_kH.b),E(_kH.c));}),_kI=new T(function(){var _kJ=E(_kC),_kK=E(_kF),_kL=B(_7h(_kD)),_kM=new T(function(){return B(A2(_7B,_kD,new T(function(){var _kN=E(_kE),_kO=_kN.a,_kP=_kN.b,_kQ=_kN.c;return B(_7n(_kD,_kO,_kP,_kQ,_kO,_kP,_kQ));})));}),_kR=B(A3(_9a,_kL,new T(function(){return B(_7D(_kD,_kJ));}),_kM)),_kS=B(_7j(_kL)),_kT=B(_ki(_kS,_kK.a,_kK.b,_kK.c,_kR,_kR,_kR)),_kU=B(_6K(_kS)),_kV=B(_kr(_kS,_kJ.a,_kJ.b,_kJ.c,B(A1(_kU,_kT.a)),B(A1(_kU,_kT.b)),B(A1(_kU,_kT.c))));return new T3(0,E(_kV.a),E(_kV.b),E(_kV.c));});return new T2(0,_kI,_kF);},_kW=function(_kX){return E(E(_kX).a);},_kY=function(_kZ,_l0,_l1,_l2,_l3,_l4,_l5){var _l6=B(_7n(_kZ,_l3,_l4,_l5,_l0,_l1,_l2)),_l7=B(_7j(B(_7h(_kZ)))),_l8=B(_ki(_l7,_l3,_l4,_l5,_l6,_l6,_l6)),_l9=B(_6K(_l7));return new F(function(){return _kr(_l7,_l0,_l1,_l2,B(A1(_l9,_l8.a)),B(A1(_l9,_l8.b)),B(A1(_l9,_l8.c)));});},_la=function(_lb){return E(E(_lb).a);},_lc=function(_ld,_le,_lf,_lg){var _lh=new T(function(){var _li=E(_lg),_lj=E(_lf),_lk=B(_kY(_ld,_li.a,_li.b,_li.c,_lj.a,_lj.b,_lj.c));return new T3(0,E(_lk.a),E(_lk.b),E(_lk.c));}),_ll=new T(function(){return B(A2(_7B,_ld,new T(function(){var _lm=E(_lh),_ln=_lm.a,_lo=_lm.b,_lp=_lm.c;return B(_7n(_ld,_ln,_lo,_lp,_ln,_lo,_lp));})));});if(!B(A3(_la,B(_kW(_le)),_ll,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_ld)))),_91));})))){var _lq=E(_lh),_lr=B(_kb(_ld,_lq.a,_lq.b,_lq.c)),_ls=B(A2(_7B,_ld,new T(function(){var _lt=E(_lg),_lu=_lt.a,_lv=_lt.b,_lw=_lt.c;return B(_7n(_ld,_lu,_lv,_lw,_lu,_lv,_lw));}))),_lx=B(_7l(new T(function(){return B(_7j(new T(function(){return B(_7h(_ld));})));})));return new T3(0,B(A1(B(A1(_lx,_lr.a)),_ls)),B(A1(B(A1(_lx,_lr.b)),_ls)),B(A1(B(A1(_lx,_lr.c)),_ls)));}else{var _ly=B(A2(_7z,B(_7j(B(_7h(_ld)))),_91));return new T3(0,_ly,_ly,_ly);}},_lz=new T(function(){var _lA=eval("angleCount"),_lB=Number(_lA);return jsTrunc(_lB);}),_lC=new T(function(){return E(_lz);}),_lD=new T(function(){return B(unCStr(": empty list"));}),_lE=new T(function(){return B(unCStr("Prelude."));}),_lF=function(_lG){return new F(function(){return err(B(_f(_lE,new T(function(){return B(_f(_lG,_lD));},1))));});},_lH=new T(function(){return B(unCStr("head"));}),_lI=new T(function(){return B(_lF(_lH));}),_lJ=function(_lK,_lL,_lM){var _lN=E(_lK);if(!_lN._){return __Z;}else{var _lO=E(_lL);if(!_lO._){return __Z;}else{var _lP=_lO.a,_lQ=E(_lM);if(!_lQ._){return __Z;}else{var _lR=E(_lQ.a),_lS=_lR.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_lN.a),E(_lP),E(_lS));}),new T2(1,new T(function(){return new T3(0,E(_lP),E(_lS),E(_lR.b));}),_o)),new T(function(){return B(_lJ(_lN.b,_lO.b,_lQ.b));},1));});}}}},_lT=new T(function(){return B(unCStr("tail"));}),_lU=new T(function(){return B(_lF(_lT));}),_lV=function(_lW,_lX){var _lY=E(_lW);if(!_lY._){return __Z;}else{var _lZ=E(_lX);return (_lZ._==0)?__Z:new T2(1,new T2(0,_lY.a,_lZ.a),new T(function(){return B(_lV(_lY.b,_lZ.b));}));}},_m0=function(_m1,_m2){var _m3=E(_m1);if(!_m3._){return __Z;}else{var _m4=E(_m2);if(!_m4._){return __Z;}else{var _m5=E(_m3.a),_m6=_m5.b,_m7=E(_m4.a).b,_m8=new T(function(){var _m9=new T(function(){return B(_lV(_m7,new T(function(){var _ma=E(_m7);if(!_ma._){return E(_lU);}else{return E(_ma.b);}},1)));},1);return B(_lJ(_m6,new T(function(){var _mb=E(_m6);if(!_mb._){return E(_lU);}else{return E(_mb.b);}},1),_m9));});return new F(function(){return _f(new T2(1,new T(function(){var _mc=E(_m6);if(!_mc._){return E(_lI);}else{var _md=E(_m7);if(!_md._){return E(_lI);}else{return new T3(0,E(_m5.a),E(_mc.a),E(_md.a));}}}),_m8),new T(function(){return B(_m0(_m3.b,_m4.b));},1));});}}},_me=new T(function(){return E(_lC)-1;}),_mf=new T1(0,1),_mg=function(_mh,_mi){var _mj=E(_mi),_mk=new T(function(){var _ml=B(_7j(_mh)),_mm=B(_mg(_mh,B(A3(_6I,_ml,_mj,new T(function(){return B(A2(_7z,_ml,_mf));})))));return new T2(1,_mm.a,_mm.b);});return new T2(0,_mj,_mk);},_mn=function(_mo){return E(E(_mo).d);},_mp=new T1(0,2),_mq=function(_mr,_ms){var _mt=E(_ms);if(!_mt._){return __Z;}else{var _mu=_mt.a;return (!B(A1(_mr,_mu)))?__Z:new T2(1,_mu,new T(function(){return B(_mq(_mr,_mt.b));}));}},_mv=function(_mw,_mx,_my,_mz){var _mA=B(_mg(_mx,_my)),_mB=new T(function(){var _mC=B(_7j(_mx)),_mD=new T(function(){return B(A3(_9a,_mx,new T(function(){return B(A2(_7z,_mC,_mf));}),new T(function(){return B(A2(_7z,_mC,_mp));})));});return B(A3(_6I,_mC,_mz,_mD));});return new F(function(){return _mq(function(_mE){return new F(function(){return A3(_mn,_mw,_mE,_mB);});},new T2(1,_mA.a,_mA.b));});},_mF=new T(function(){return B(_mv(_js,_ir,_ho,_me));}),_mG=function(_mH,_mI){while(1){var _mJ=E(_mH);if(!_mJ._){return E(_mI);}else{_mH=_mJ.b;_mI=_mJ.a;continue;}}},_mK=new T(function(){return B(unCStr("last"));}),_mL=new T(function(){return B(_lF(_mK));}),_mM=function(_mN){return new F(function(){return _mG(_mN,_mL);});},_mO=function(_mP){return new F(function(){return _mM(E(_mP).b);});},_mQ=new T(function(){var _mR=eval("proceedCount"),_mS=Number(_mR);return jsTrunc(_mS);}),_mT=new T(function(){return E(_mQ);}),_mU=1,_mV=new T(function(){return B(_mv(_js,_ir,_mU,_mT));}),_mW=function(_mX,_mY,_mZ,_n0,_n1,_n2,_n3,_n4,_n5,_n6,_n7,_n8,_n9,_na){var _nb=new T(function(){var _nc=new T(function(){var _nd=E(_n6),_ne=E(_na),_nf=E(_n9),_ng=E(_n7),_nh=E(_n8),_ni=E(_n5);return new T3(0,_nd*_ne-_nf*_ng,_ng*_nh-_ne*_ni,_ni*_nf-_nh*_nd);}),_nj=function(_nk){var _nl=new T(function(){var _nm=E(_nk)/E(_lC);return (_nm+_nm)*3.141592653589793;}),_nn=new T(function(){return B(A1(_mX,_nl));}),_no=new T(function(){var _np=new T(function(){var _nq=E(_nn)/E(_mT);return new T3(0,E(_nq),E(_nq),E(_nq));}),_nr=function(_ns,_nt){var _nu=E(_ns);if(!_nu._){return new T2(0,_o,_nt);}else{var _nv=new T(function(){var _nw=B(_kA(_ka,new T(function(){var _nx=E(_nt),_ny=E(_nx.a),_nz=E(_nx.b),_nA=E(_np);return new T3(0,E(_ny.a)+E(_nz.a)*E(_nA.a),E(_ny.b)+E(_nz.b)*E(_nA.b),E(_ny.c)+E(_nz.c)*E(_nA.c));}))),_nB=_nw.a;return new T2(0,new T(function(){var _nC=E(_nn),_nD=E(_nl);return new T3(0,E(_nB),E(new T2(0,E(_nu.a)/E(_mT),E(_nC))),E(_nD));}),new T2(0,_nB,new T(function(){var _nE=E(_nw.b),_nF=E(E(_nt).b),_nG=B(_kY(_iT,_nF.a,_nF.b,_nF.c,_nE.a,_nE.b,_nE.c)),_nH=B(_kb(_iT,_nG.a,_nG.b,_nG.c));return new T3(0,E(_nH.a),E(_nH.b),E(_nH.c));})));}),_nI=new T(function(){var _nJ=B(_nr(_nu.b,new T(function(){return E(E(_nv).b);})));return new T2(0,_nJ.a,_nJ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nv).a);}),new T(function(){return E(E(_nI).a);})),new T(function(){return E(E(_nI).b);}));}},_nK=function(_nL,_nM,_nN,_nO,_nP){var _nQ=E(_nL);if(!_nQ._){return new T2(0,_o,new T2(0,new T3(0,E(_nM),E(_nN),E(_nO)),_nP));}else{var _nR=new T(function(){var _nS=B(_kA(_ka,new T(function(){var _nT=E(_nP),_nU=E(_np);return new T3(0,E(_nM)+E(_nT.a)*E(_nU.a),E(_nN)+E(_nT.b)*E(_nU.b),E(_nO)+E(_nT.c)*E(_nU.c));}))),_nV=_nS.a;return new T2(0,new T(function(){var _nW=E(_nn),_nX=E(_nl);return new T3(0,E(_nV),E(new T2(0,E(_nQ.a)/E(_mT),E(_nW))),E(_nX));}),new T2(0,_nV,new T(function(){var _nY=E(_nS.b),_nZ=E(_nP),_o0=B(_kY(_iT,_nZ.a,_nZ.b,_nZ.c,_nY.a,_nY.b,_nY.c)),_o1=B(_kb(_iT,_o0.a,_o0.b,_o0.c));return new T3(0,E(_o1.a),E(_o1.b),E(_o1.c));})));}),_o2=new T(function(){var _o3=B(_nr(_nQ.b,new T(function(){return E(E(_nR).b);})));return new T2(0,_o3.a,_o3.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nR).a);}),new T(function(){return E(E(_o2).a);})),new T(function(){return E(E(_o2).b);}));}};return E(B(_nK(_mV,_n0,_n1,_n2,new T(function(){var _o4=E(_nc),_o5=E(_nl)+_n3,_o6=Math.cos(_o5),_o7=Math.sin(_o5);return new T3(0,E(_n5)*_o6+E(_o4.a)*_o7,E(_n6)*_o6+E(_o4.b)*_o7,E(_n7)*_o6+E(_o4.c)*_o7);}))).a);});return new T2(0,new T(function(){var _o8=E(_nn),_o9=E(_nl);return new T3(0,E(new T3(0,E(_n0),E(_n1),E(_n2))),E(new T2(0,E(_ho),E(_o8))),E(_o9));}),_no);};return B(_jY(_nj,_mF));}),_oa=new T(function(){var _ob=new T(function(){var _oc=B(_f(_nb,new T2(1,new T(function(){var _od=E(_nb);if(!_od._){return E(_lI);}else{return E(_od.a);}}),_o)));if(!_oc._){return E(_lU);}else{return E(_oc.b);}},1);return B(_m0(_nb,_ob));});return new T2(0,_oa,new T(function(){return B(_jY(_mO,_nb));}));},_oe=function(_of,_og,_oh,_oi,_oj,_ok,_ol,_om,_on,_oo,_op,_oq,_or,_os,_ot,_ou,_ov){var _ow=B(_kA(_ka,new T3(0,E(_oi),E(_oj),E(_ok)))),_ox=_ow.b,_oy=E(_ow.a),_oz=B(_lc(_iT,_js,_ox,new T3(0,E(_om),E(_on),E(_oo)))),_oA=E(_ox),_oB=_oA.a,_oC=_oA.b,_oD=_oA.c,_oE=B(_kY(_iT,_oq,_or,_os,_oB,_oC,_oD)),_oF=B(_kb(_iT,_oE.a,_oE.b,_oE.c)),_oG=_oF.a,_oH=_oF.b,_oI=_oF.c,_oJ=E(_ol),_oK=new T2(0,E(new T3(0,E(_oz.a),E(_oz.b),E(_oz.c))),E(_op)),_oL=B(_mW(_of,_og,_oh,_oy.a,_oy.b,_oy.c,_oJ,_oK,_oG,_oH,_oI,_oB,_oC,_oD)),_oM=__lst2arr(B(_jY(_k7,_oL.a))),_oN=__lst2arr(B(_jY(_jT,_oL.b)));return {_:0,a:_of,b:_og,c:_oh,d:new T2(0,E(_oy),E(_oJ)),e:_oK,f:new T3(0,E(_oG),E(_oH),E(_oI)),g:_oA,h:_oM,i:_oN};},_oO=new T(function(){return 6.283185307179586/E(_lC);}),_oP= -1,_oQ=0.5,_oR=new T3(0,E(_ho),E(_oQ),E(_oP)),_oS=function(_){return new F(function(){return __jsNull();});},_oT=function(_oU){var _oV=B(A1(_oU,_));return E(_oV);},_oW=new T(function(){return B(_oT(_oS));}),_oX=function(_oY,_oZ,_p0,_p1,_p2,_p3,_p4,_p5,_p6,_p7,_p8,_p9,_pa){var _pb=function(_pc){var _pd=E(_oO),_pe=2+_pc|0,_pf=_pe-1|0,_pg=(2+_pc)*(1+_pc),_ph=E(_mF);if(!_ph._){return _pd*0;}else{var _pi=_ph.a,_pj=_ph.b,_pk=B(A1(_oY,new T(function(){return 6.283185307179586*E(_pi)/E(_lC);}))),_pl=B(A1(_oY,new T(function(){return 6.283185307179586*(E(_pi)+1)/E(_lC);})));if(_pk!=_pl){if(_pe>=0){var _pm=E(_pe);if(!_pm){var _pn=function(_po,_pp){while(1){var _pq=B((function(_pr,_ps){var _pt=E(_pr);if(!_pt._){return E(_ps);}else{var _pu=_pt.a,_pv=_pt.b,_pw=B(A1(_oY,new T(function(){return 6.283185307179586*E(_pu)/E(_lC);}))),_px=B(A1(_oY,new T(function(){return 6.283185307179586*(E(_pu)+1)/E(_lC);})));if(_pw!=_px){var _py=_ps+0/(_pw-_px)/_pg;_po=_pv;_pp=_py;return __continue;}else{if(_pf>=0){var _pz=E(_pf);if(!_pz){var _py=_ps+_pe/_pg;_po=_pv;_pp=_py;return __continue;}else{var _py=_ps+_pe*B(_hA(_pw,_pz))/_pg;_po=_pv;_pp=_py;return __continue;}}else{return E(_hr);}}}})(_po,_pp));if(_pq!=__continue){return _pq;}}};return _pd*B(_pn(_pj,0/(_pk-_pl)/_pg));}else{var _pA=function(_pB,_pC){while(1){var _pD=B((function(_pE,_pF){var _pG=E(_pE);if(!_pG._){return E(_pF);}else{var _pH=_pG.a,_pI=_pG.b,_pJ=B(A1(_oY,new T(function(){return 6.283185307179586*E(_pH)/E(_lC);}))),_pK=B(A1(_oY,new T(function(){return 6.283185307179586*(E(_pH)+1)/E(_lC);})));if(_pJ!=_pK){if(_pm>=0){var _pL=_pF+(B(_hA(_pJ,_pm))-B(_hA(_pK,_pm)))/(_pJ-_pK)/_pg;_pB=_pI;_pC=_pL;return __continue;}else{return E(_hr);}}else{if(_pf>=0){var _pM=E(_pf);if(!_pM){var _pL=_pF+_pe/_pg;_pB=_pI;_pC=_pL;return __continue;}else{var _pL=_pF+_pe*B(_hA(_pJ,_pM))/_pg;_pB=_pI;_pC=_pL;return __continue;}}else{return E(_hr);}}}})(_pB,_pC));if(_pD!=__continue){return _pD;}}};return _pd*B(_pA(_pj,(B(_hA(_pk,_pm))-B(_hA(_pl,_pm)))/(_pk-_pl)/_pg));}}else{return E(_hr);}}else{if(_pf>=0){var _pN=E(_pf);if(!_pN){var _pO=function(_pP,_pQ){while(1){var _pR=B((function(_pS,_pT){var _pU=E(_pS);if(!_pU._){return E(_pT);}else{var _pV=_pU.a,_pW=_pU.b,_pX=B(A1(_oY,new T(function(){return 6.283185307179586*E(_pV)/E(_lC);}))),_pY=B(A1(_oY,new T(function(){return 6.283185307179586*(E(_pV)+1)/E(_lC);})));if(_pX!=_pY){if(_pe>=0){var _pZ=E(_pe);if(!_pZ){var _q0=_pT+0/(_pX-_pY)/_pg;_pP=_pW;_pQ=_q0;return __continue;}else{var _q0=_pT+(B(_hA(_pX,_pZ))-B(_hA(_pY,_pZ)))/(_pX-_pY)/_pg;_pP=_pW;_pQ=_q0;return __continue;}}else{return E(_hr);}}else{var _q0=_pT+_pe/_pg;_pP=_pW;_pQ=_q0;return __continue;}}})(_pP,_pQ));if(_pR!=__continue){return _pR;}}};return _pd*B(_pO(_pj,_pe/_pg));}else{var _q1=function(_q2,_q3){while(1){var _q4=B((function(_q5,_q6){var _q7=E(_q5);if(!_q7._){return E(_q6);}else{var _q8=_q7.a,_q9=_q7.b,_qa=B(A1(_oY,new T(function(){return 6.283185307179586*E(_q8)/E(_lC);}))),_qb=B(A1(_oY,new T(function(){return 6.283185307179586*(E(_q8)+1)/E(_lC);})));if(_qa!=_qb){if(_pe>=0){var _qc=E(_pe);if(!_qc){var _qd=_q6+0/(_qa-_qb)/_pg;_q2=_q9;_q3=_qd;return __continue;}else{var _qd=_q6+(B(_hA(_qa,_qc))-B(_hA(_qb,_qc)))/(_qa-_qb)/_pg;_q2=_q9;_q3=_qd;return __continue;}}else{return E(_hr);}}else{if(_pN>=0){var _qd=_q6+_pe*B(_hA(_qa,_pN))/_pg;_q2=_q9;_q3=_qd;return __continue;}else{return E(_hr);}}}})(_q2,_q3));if(_q4!=__continue){return _q4;}}};return _pd*B(_q1(_pj,_pe*B(_hA(_pk,_pN))/_pg));}}else{return E(_hr);}}}},_qe=E(_oW),_qf=1/(B(_pb(1))*_oZ);return new F(function(){return _oe(_oY,_oR,new T2(0,E(new T3(0,E(_qf),E(_qf),E(_qf))),1/(B(_pb(3))*_oZ)),_p0,_p1,_p2,_p3,_p4,_p5,_p6,_p7,_p8,_p9,_pa,_hp,_qe,_qe);});},_qg=0,_qh= -0.5,_qi=0.5,_qj=0.2,_qk=function(_ql){return E(_qj);},_qm=1,_qn=0.3,_qo=new T(function(){var _qp=B(_oX(_qk,1.2,_qg,_qi,_qh,_qg,_qg,_qg,_qn,_qg,_qg,_qg,_qm));return {_:0,a:E(_qp.a),b:E(_qp.b),c:E(_qp.c),d:E(_qp.d),e:E(_qp.e),f:E(_qp.f),g:E(_qp.g),h:_qp.h,i:_qp.i};}),_qq=0,_qr= -0.1,_qs=0.4,_qt=function(_qu){var _qv=I_decodeDouble(_qu);return new T2(0,new T1(1,_qv.b),_qv.a);},_qw=function(_qx){return new T1(0,_qx);},_qy=function(_qz){var _qA=hs_intToInt64(2147483647),_qB=hs_leInt64(_qz,_qA);if(!_qB){return new T1(1,I_fromInt64(_qz));}else{var _qC=hs_intToInt64( -2147483648),_qD=hs_geInt64(_qz,_qC);if(!_qD){return new T1(1,I_fromInt64(_qz));}else{var _qE=hs_int64ToInt(_qz);return new F(function(){return _qw(_qE);});}}},_qF=new T(function(){var _qG=newByteArr(256),_qH=_qG,_=_qH["v"]["i8"][0]=8,_qI=function(_qJ,_qK,_qL,_){while(1){if(_qL>=256){if(_qJ>=256){return E(_);}else{var _qM=imul(2,_qJ)|0,_qN=_qK+1|0,_qO=_qJ;_qJ=_qM;_qK=_qN;_qL=_qO;continue;}}else{var _=_qH["v"]["i8"][_qL]=_qK,_qO=_qL+_qJ|0;_qL=_qO;continue;}}},_=B(_qI(2,0,1,_));return _qH;}),_qP=function(_qQ,_qR){var _qS=hs_int64ToInt(_qQ),_qT=E(_qF),_qU=_qT["v"]["i8"][(255&_qS>>>0)>>>0&4294967295];if(_qR>_qU){if(_qU>=8){var _qV=hs_uncheckedIShiftRA64(_qQ,8),_qW=function(_qX,_qY){while(1){var _qZ=B((function(_r0,_r1){var _r2=hs_int64ToInt(_r0),_r3=_qT["v"]["i8"][(255&_r2>>>0)>>>0&4294967295];if(_r1>_r3){if(_r3>=8){var _r4=hs_uncheckedIShiftRA64(_r0,8),_r5=_r1-8|0;_qX=_r4;_qY=_r5;return __continue;}else{return new T2(0,new T(function(){var _r6=hs_uncheckedIShiftRA64(_r0,_r3);return B(_qy(_r6));}),_r1-_r3|0);}}else{return new T2(0,new T(function(){var _r7=hs_uncheckedIShiftRA64(_r0,_r1);return B(_qy(_r7));}),0);}})(_qX,_qY));if(_qZ!=__continue){return _qZ;}}};return new F(function(){return _qW(_qV,_qR-8|0);});}else{return new T2(0,new T(function(){var _r8=hs_uncheckedIShiftRA64(_qQ,_qU);return B(_qy(_r8));}),_qR-_qU|0);}}else{return new T2(0,new T(function(){var _r9=hs_uncheckedIShiftRA64(_qQ,_qR);return B(_qy(_r9));}),0);}},_ra=function(_rb){var _rc=hs_intToInt64(_rb);return E(_rc);},_rd=function(_re){var _rf=E(_re);if(!_rf._){return new F(function(){return _ra(_rf.a);});}else{return new F(function(){return I_toInt64(_rf.a);});}},_rg=function(_rh){return I_toInt(_rh)>>>0;},_ri=function(_rj){var _rk=E(_rj);if(!_rk._){return _rk.a>>>0;}else{return new F(function(){return _rg(_rk.a);});}},_rl=function(_rm){var _rn=B(_qt(_rm)),_ro=_rn.a,_rp=_rn.b;if(_rp<0){var _rq=function(_rr){if(!_rr){return new T2(0,E(_ro),B(_3u(_1M, -_rp)));}else{var _rs=B(_qP(B(_rd(_ro)), -_rp));return new T2(0,E(_rs.a),B(_3u(_1M,_rs.b)));}};if(!((B(_ri(_ro))&1)>>>0)){return new F(function(){return _rq(1);});}else{return new F(function(){return _rq(0);});}}else{return new T2(0,B(_3u(_ro,_rp)),_1M);}},_rt=function(_ru){var _rv=B(_rl(E(_ru)));return new T2(0,E(_rv.a),E(_rv.b));},_rw=new T3(0,_in,_js,_rt),_rx=function(_ry){return E(E(_ry).a);},_rz=function(_rA){return E(E(_rA).a);},_rB=function(_rC,_rD){if(_rC<=_rD){var _rE=function(_rF){return new T2(1,_rF,new T(function(){if(_rF!=_rD){return B(_rE(_rF+1|0));}else{return __Z;}}));};return new F(function(){return _rE(_rC);});}else{return __Z;}},_rG=function(_rH){return new F(function(){return _rB(E(_rH),2147483647);});},_rI=function(_rJ,_rK,_rL){if(_rL<=_rK){var _rM=new T(function(){var _rN=_rK-_rJ|0,_rO=function(_rP){return (_rP>=(_rL-_rN|0))?new T2(1,_rP,new T(function(){return B(_rO(_rP+_rN|0));})):new T2(1,_rP,_o);};return B(_rO(_rK));});return new T2(1,_rJ,_rM);}else{return (_rL<=_rJ)?new T2(1,_rJ,_o):__Z;}},_rQ=function(_rR,_rS,_rT){if(_rT>=_rS){var _rU=new T(function(){var _rV=_rS-_rR|0,_rW=function(_rX){return (_rX<=(_rT-_rV|0))?new T2(1,_rX,new T(function(){return B(_rW(_rX+_rV|0));})):new T2(1,_rX,_o);};return B(_rW(_rS));});return new T2(1,_rR,_rU);}else{return (_rT>=_rR)?new T2(1,_rR,_o):__Z;}},_rY=function(_rZ,_s0){if(_s0<_rZ){return new F(function(){return _rI(_rZ,_s0, -2147483648);});}else{return new F(function(){return _rQ(_rZ,_s0,2147483647);});}},_s1=function(_s2,_s3){return new F(function(){return _rY(E(_s2),E(_s3));});},_s4=function(_s5,_s6,_s7){if(_s6<_s5){return new F(function(){return _rI(_s5,_s6,_s7);});}else{return new F(function(){return _rQ(_s5,_s6,_s7);});}},_s8=function(_s9,_sa,_sb){return new F(function(){return _s4(E(_s9),E(_sa),E(_sb));});},_sc=function(_sd,_se){return new F(function(){return _rB(E(_sd),E(_se));});},_sf=function(_sg){return E(_sg);},_sh=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_si=new T(function(){return B(err(_sh));}),_sj=function(_sk){var _sl=E(_sk);return (_sl==( -2147483648))?E(_si):_sl-1|0;},_sm=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_sn=new T(function(){return B(err(_sm));}),_so=function(_sp){var _sq=E(_sp);return (_sq==2147483647)?E(_sn):_sq+1|0;},_sr={_:0,a:_so,b:_sj,c:_sf,d:_sf,e:_rG,f:_s1,g:_sc,h:_s8},_ss=function(_st,_su){if(_st<=0){if(_st>=0){return new F(function(){return quot(_st,_su);});}else{if(_su<=0){return new F(function(){return quot(_st,_su);});}else{return quot(_st+1|0,_su)-1|0;}}}else{if(_su>=0){if(_st>=0){return new F(function(){return quot(_st,_su);});}else{if(_su<=0){return new F(function(){return quot(_st,_su);});}else{return quot(_st+1|0,_su)-1|0;}}}else{return quot(_st-1|0,_su)-1|0;}}},_sv=0,_sw=new T(function(){return B(_2R(_sv));}),_sx=new T(function(){return die(_sw);}),_sy=function(_sz,_sA){var _sB=E(_sA);switch(_sB){case  -1:var _sC=E(_sz);if(_sC==( -2147483648)){return E(_sx);}else{return new F(function(){return _ss(_sC, -1);});}break;case 0:return E(_2V);default:return new F(function(){return _ss(_sz,_sB);});}},_sD=function(_sE,_sF){return new F(function(){return _sy(E(_sE),E(_sF));});},_sG=0,_sH=new T2(0,_sx,_sG),_sI=function(_sJ,_sK){var _sL=E(_sJ),_sM=E(_sK);switch(_sM){case  -1:var _sN=E(_sL);if(_sN==( -2147483648)){return E(_sH);}else{if(_sN<=0){if(_sN>=0){var _sO=quotRemI(_sN, -1);return new T2(0,_sO.a,_sO.b);}else{var _sP=quotRemI(_sN, -1);return new T2(0,_sP.a,_sP.b);}}else{var _sQ=quotRemI(_sN-1|0, -1);return new T2(0,_sQ.a-1|0,(_sQ.b+( -1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_sL<=0){if(_sL>=0){var _sR=quotRemI(_sL,_sM);return new T2(0,_sR.a,_sR.b);}else{if(_sM<=0){var _sS=quotRemI(_sL,_sM);return new T2(0,_sS.a,_sS.b);}else{var _sT=quotRemI(_sL+1|0,_sM);return new T2(0,_sT.a-1|0,(_sT.b+_sM|0)-1|0);}}}else{if(_sM>=0){if(_sL>=0){var _sU=quotRemI(_sL,_sM);return new T2(0,_sU.a,_sU.b);}else{if(_sM<=0){var _sV=quotRemI(_sL,_sM);return new T2(0,_sV.a,_sV.b);}else{var _sW=quotRemI(_sL+1|0,_sM);return new T2(0,_sW.a-1|0,(_sW.b+_sM|0)-1|0);}}}else{var _sX=quotRemI(_sL-1|0,_sM);return new T2(0,_sX.a-1|0,(_sX.b+_sM|0)+1|0);}}}},_sY=function(_sZ,_t0){var _t1=_sZ%_t0;if(_sZ<=0){if(_sZ>=0){return E(_t1);}else{if(_t0<=0){return E(_t1);}else{var _t2=E(_t1);return (_t2==0)?0:_t2+_t0|0;}}}else{if(_t0>=0){if(_sZ>=0){return E(_t1);}else{if(_t0<=0){return E(_t1);}else{var _t3=E(_t1);return (_t3==0)?0:_t3+_t0|0;}}}else{var _t4=E(_t1);return (_t4==0)?0:_t4+_t0|0;}}},_t5=function(_t6,_t7){var _t8=E(_t7);switch(_t8){case  -1:return E(_sG);case 0:return E(_2V);default:return new F(function(){return _sY(E(_t6),_t8);});}},_t9=function(_ta,_tb){var _tc=E(_ta),_td=E(_tb);switch(_td){case  -1:var _te=E(_tc);if(_te==( -2147483648)){return E(_sx);}else{return new F(function(){return quot(_te, -1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_tc,_td);});}},_tf=function(_tg,_th){var _ti=E(_tg),_tj=E(_th);switch(_tj){case  -1:var _tk=E(_ti);if(_tk==( -2147483648)){return E(_sH);}else{var _tl=quotRemI(_tk, -1);return new T2(0,_tl.a,_tl.b);}break;case 0:return E(_2V);default:var _tm=quotRemI(_ti,_tj);return new T2(0,_tm.a,_tm.b);}},_tn=function(_to,_tp){var _tq=E(_tp);switch(_tq){case  -1:return E(_sG);case 0:return E(_2V);default:return E(_to)%_tq;}},_tr=function(_ts){return new F(function(){return _qw(E(_ts));});},_tt=function(_tu){return new T2(0,E(B(_qw(E(_tu)))),E(_mf));},_tv=function(_tw,_tx){return imul(E(_tw),E(_tx))|0;},_ty=function(_tz,_tA){return E(_tz)+E(_tA)|0;},_tB=function(_tC,_tD){return E(_tC)-E(_tD)|0;},_tE=function(_tF){var _tG=E(_tF);return (_tG<0)? -_tG:E(_tG);},_tH=function(_tI){return new F(function(){return _38(_tI);});},_tJ=function(_tK){return  -E(_tK);},_tL= -1,_tM=0,_tN=1,_tO=function(_tP){var _tQ=E(_tP);return (_tQ>=0)?(E(_tQ)==0)?E(_tM):E(_tN):E(_tL);},_tR={_:0,a:_ty,b:_tB,c:_tv,d:_tJ,e:_tE,f:_tO,g:_tH},_tS=function(_tT,_tU){return E(_tT)==E(_tU);},_tV=function(_tW,_tX){return E(_tW)!=E(_tX);},_tY=new T2(0,_tS,_tV),_tZ=function(_u0,_u1){var _u2=E(_u0),_u3=E(_u1);return (_u2>_u3)?E(_u2):E(_u3);},_u4=function(_u5,_u6){var _u7=E(_u5),_u8=E(_u6);return (_u7>_u8)?E(_u8):E(_u7);},_u9=function(_ua,_ub){return (_ua>=_ub)?(_ua!=_ub)?2:1:0;},_uc=function(_ud,_ue){return new F(function(){return _u9(E(_ud),E(_ue));});},_uf=function(_ug,_uh){return E(_ug)>=E(_uh);},_ui=function(_uj,_uk){return E(_uj)>E(_uk);},_ul=function(_um,_un){return E(_um)<=E(_un);},_uo=function(_up,_uq){return E(_up)<E(_uq);},_ur={_:0,a:_tY,b:_uc,c:_uo,d:_ul,e:_ui,f:_uf,g:_tZ,h:_u4},_us=new T3(0,_tR,_ur,_tt),_ut={_:0,a:_us,b:_sr,c:_t9,d:_tn,e:_sD,f:_t5,g:_tf,h:_sI,i:_tr},_uu=new T1(0,2),_uv=function(_uw,_ux){while(1){var _uy=E(_uw);if(!_uy._){var _uz=_uy.a,_uA=E(_ux);if(!_uA._){var _uB=_uA.a;if(!(imul(_uz,_uB)|0)){return new T1(0,imul(_uz,_uB)|0);}else{_uw=new T1(1,I_fromInt(_uz));_ux=new T1(1,I_fromInt(_uB));continue;}}else{_uw=new T1(1,I_fromInt(_uz));_ux=_uA;continue;}}else{var _uC=E(_ux);if(!_uC._){_uw=_uy;_ux=new T1(1,I_fromInt(_uC.a));continue;}else{return new T1(1,I_mul(_uy.a,_uC.a));}}}},_uD=function(_uE,_uF,_uG){while(1){if(!(_uF%2)){var _uH=B(_uv(_uE,_uE)),_uI=quot(_uF,2);_uE=_uH;_uF=_uI;continue;}else{var _uJ=E(_uF);if(_uJ==1){return new F(function(){return _uv(_uE,_uG);});}else{var _uH=B(_uv(_uE,_uE)),_uK=B(_uv(_uE,_uG));_uE=_uH;_uF=quot(_uJ-1|0,2);_uG=_uK;continue;}}}},_uL=function(_uM,_uN){while(1){if(!(_uN%2)){var _uO=B(_uv(_uM,_uM)),_uP=quot(_uN,2);_uM=_uO;_uN=_uP;continue;}else{var _uQ=E(_uN);if(_uQ==1){return E(_uM);}else{return new F(function(){return _uD(B(_uv(_uM,_uM)),quot(_uQ-1|0,2),_uM);});}}}},_uR=function(_uS){return E(E(_uS).b);},_uT=function(_uU){return E(E(_uU).c);},_uV=new T1(0,0),_uW=function(_uX){return E(E(_uX).d);},_uY=function(_uZ,_v0){var _v1=B(_rx(_uZ)),_v2=new T(function(){return B(_rz(_v1));}),_v3=new T(function(){return B(A3(_uW,_uZ,_v0,new T(function(){return B(A2(_7z,_v2,_mp));})));});return new F(function(){return A3(_la,B(_kW(B(_uR(_v1)))),_v3,new T(function(){return B(A2(_7z,_v2,_uV));}));});},_v4=new T(function(){return B(unCStr("Negative exponent"));}),_v5=new T(function(){return B(err(_v4));}),_v6=function(_v7){return E(E(_v7).c);},_v8=function(_v9,_va,_vb,_vc){var _vd=B(_rx(_va)),_ve=new T(function(){return B(_rz(_vd));}),_vf=B(_uR(_vd));if(!B(A3(_uT,_vf,_vc,new T(function(){return B(A2(_7z,_ve,_uV));})))){if(!B(A3(_la,B(_kW(_vf)),_vc,new T(function(){return B(A2(_7z,_ve,_uV));})))){var _vg=new T(function(){return B(A2(_7z,_ve,_mp));}),_vh=new T(function(){return B(A2(_7z,_ve,_mf));}),_vi=B(_kW(_vf)),_vj=function(_vk,_vl,_vm){while(1){var _vn=B((function(_vo,_vp,_vq){if(!B(_uY(_va,_vp))){if(!B(A3(_la,_vi,_vp,_vh))){var _vr=new T(function(){return B(A3(_v6,_va,new T(function(){return B(A3(_7x,_ve,_vp,_vh));}),_vg));});_vk=new T(function(){return B(A3(_7l,_v9,_vo,_vo));});_vl=_vr;_vm=new T(function(){return B(A3(_7l,_v9,_vo,_vq));});return __continue;}else{return new F(function(){return A3(_7l,_v9,_vo,_vq);});}}else{var _vs=_vq;_vk=new T(function(){return B(A3(_7l,_v9,_vo,_vo));});_vl=new T(function(){return B(A3(_v6,_va,_vp,_vg));});_vm=_vs;return __continue;}})(_vk,_vl,_vm));if(_vn!=__continue){return _vn;}}},_vt=function(_vu,_vv){while(1){var _vw=B((function(_vx,_vy){if(!B(_uY(_va,_vy))){if(!B(A3(_la,_vi,_vy,_vh))){var _vz=new T(function(){return B(A3(_v6,_va,new T(function(){return B(A3(_7x,_ve,_vy,_vh));}),_vg));});return new F(function(){return _vj(new T(function(){return B(A3(_7l,_v9,_vx,_vx));}),_vz,_vx);});}else{return E(_vx);}}else{_vu=new T(function(){return B(A3(_7l,_v9,_vx,_vx));});_vv=new T(function(){return B(A3(_v6,_va,_vy,_vg));});return __continue;}})(_vu,_vv));if(_vw!=__continue){return _vw;}}};return new F(function(){return _vt(_vb,_vc);});}else{return new F(function(){return A2(_7z,_v9,_mf);});}}else{return E(_v5);}},_vA=new T(function(){return B(err(_v4));}),_vB=function(_vC,_vD){var _vE=B(_qt(_vD)),_vF=_vE.a,_vG=_vE.b,_vH=new T(function(){return B(_rz(new T(function(){return B(_rx(_vC));})));});if(_vG<0){var _vI= -_vG;if(_vI>=0){var _vJ=E(_vI);if(!_vJ){var _vK=E(_mf);}else{var _vK=B(_uL(_uu,_vJ));}if(!B(_30(_vK,_3t))){var _vL=B(_3k(_vF,_vK));return new T2(0,new T(function(){return B(A2(_7z,_vH,_vL.a));}),new T(function(){return B(_2W(_vL.b,_vG));}));}else{return E(_2V);}}else{return E(_vA);}}else{var _vM=new T(function(){var _vN=new T(function(){return B(_v8(_vH,_ut,new T(function(){return B(A2(_7z,_vH,_uu));}),_vG));});return B(A3(_7l,_vH,new T(function(){return B(A2(_7z,_vH,_vF));}),_vN));});return new T2(0,_vM,_6i);}},_vO=function(_vP,_vQ){var _vR=B(_vB(_vP,E(_vQ))),_vS=_vR.a;if(E(_vR.b)<=0){return E(_vS);}else{var _vT=B(_rz(B(_rx(_vP))));return new F(function(){return A3(_6I,_vT,_vS,new T(function(){return B(A2(_7z,_vT,_1M));}));});}},_vU=function(_vV,_vW){var _vX=B(_vB(_vV,E(_vW))),_vY=_vX.a;if(E(_vX.b)>=0){return E(_vY);}else{var _vZ=B(_rz(B(_rx(_vV))));return new F(function(){return A3(_7x,_vZ,_vY,new T(function(){return B(A2(_7z,_vZ,_1M));}));});}},_w0=function(_w1,_w2){var _w3=B(_vB(_w1,E(_w2)));return new T2(0,_w3.a,_w3.b);},_w4=function(_w5,_w6){var _w7=B(_vB(_w5,_w6)),_w8=_w7.a,_w9=E(_w7.b),_wa=new T(function(){var _wb=B(_rz(B(_rx(_w5))));if(_w9>=0){return B(A3(_6I,_wb,_w8,new T(function(){return B(A2(_7z,_wb,_1M));})));}else{return B(A3(_7x,_wb,_w8,new T(function(){return B(A2(_7z,_wb,_1M));})));}}),_wc=function(_wd){var _we=_wd-0.5;return (_we>=0)?(E(_we)==0)?(!B(_uY(_w5,_w8)))?E(_wa):E(_w8):E(_wa):E(_w8);},_wf=E(_w9);if(!_wf){return new F(function(){return _wc(0);});}else{if(_wf<=0){var _wg= -_wf-0.5;return (_wg>=0)?(E(_wg)==0)?(!B(_uY(_w5,_w8)))?E(_wa):E(_w8):E(_wa):E(_w8);}else{return new F(function(){return _wc(_wf);});}}},_wh=function(_wi,_wj){return new F(function(){return _w4(_wi,E(_wj));});},_wk=function(_wl,_wm){return E(B(_vB(_wl,E(_wm))).a);},_wn={_:0,a:_rw,b:_ir,c:_w0,d:_wk,e:_wh,f:_vO,g:_vU},_wo=new T1(0,1),_wp=function(_wq,_wr){var _ws=E(_wq);return new T2(0,_ws,new T(function(){var _wt=B(_wp(B(_3b(_ws,_wr)),_wr));return new T2(1,_wt.a,_wt.b);}));},_wu=function(_wv){var _ww=B(_wp(_wv,_wo));return new T2(1,_ww.a,_ww.b);},_wx=function(_wy,_wz){var _wA=B(_wp(_wy,new T(function(){return B(_5w(_wz,_wy));})));return new T2(1,_wA.a,_wA.b);},_wB=new T1(0,0),_wC=function(_wD,_wE){var _wF=E(_wD);if(!_wF._){var _wG=_wF.a,_wH=E(_wE);return (_wH._==0)?_wG>=_wH.a:I_compareInt(_wH.a,_wG)<=0;}else{var _wI=_wF.a,_wJ=E(_wE);return (_wJ._==0)?I_compareInt(_wI,_wJ.a)>=0:I_compare(_wI,_wJ.a)>=0;}},_wK=function(_wL,_wM,_wN){if(!B(_wC(_wM,_wB))){var _wO=function(_wP){return (!B(_3N(_wP,_wN)))?new T2(1,_wP,new T(function(){return B(_wO(B(_3b(_wP,_wM))));})):__Z;};return new F(function(){return _wO(_wL);});}else{var _wQ=function(_wR){return (!B(_3E(_wR,_wN)))?new T2(1,_wR,new T(function(){return B(_wQ(B(_3b(_wR,_wM))));})):__Z;};return new F(function(){return _wQ(_wL);});}},_wS=function(_wT,_wU,_wV){return new F(function(){return _wK(_wT,B(_5w(_wU,_wT)),_wV);});},_wW=function(_wX,_wY){return new F(function(){return _wK(_wX,_wo,_wY);});},_wZ=function(_x0){return new F(function(){return _38(_x0);});},_x1=function(_x2){return new F(function(){return _5w(_x2,_wo);});},_x3=function(_x4){return new F(function(){return _3b(_x4,_wo);});},_x5=function(_x6){return new F(function(){return _qw(E(_x6));});},_x7={_:0,a:_x3,b:_x1,c:_x5,d:_wZ,e:_wu,f:_wx,g:_wW,h:_wS},_x8=function(_x9,_xa){while(1){var _xb=E(_x9);if(!_xb._){var _xc=E(_xb.a);if(_xc==( -2147483648)){_x9=new T1(1,I_fromInt( -2147483648));continue;}else{var _xd=E(_xa);if(!_xd._){return new T1(0,B(_ss(_xc,_xd.a)));}else{_x9=new T1(1,I_fromInt(_xc));_xa=_xd;continue;}}}else{var _xe=_xb.a,_xf=E(_xa);return (_xf._==0)?new T1(1,I_div(_xe,I_fromInt(_xf.a))):new T1(1,I_div(_xe,_xf.a));}}},_xg=function(_xh,_xi){if(!B(_30(_xi,_uV))){return new F(function(){return _x8(_xh,_xi);});}else{return E(_2V);}},_xj=function(_xk,_xl){while(1){var _xm=E(_xk);if(!_xm._){var _xn=E(_xm.a);if(_xn==( -2147483648)){_xk=new T1(1,I_fromInt( -2147483648));continue;}else{var _xo=E(_xl);if(!_xo._){var _xp=_xo.a;return new T2(0,new T1(0,B(_ss(_xn,_xp))),new T1(0,B(_sY(_xn,_xp))));}else{_xk=new T1(1,I_fromInt(_xn));_xl=_xo;continue;}}}else{var _xq=E(_xl);if(!_xq._){_xk=_xm;_xl=new T1(1,I_fromInt(_xq.a));continue;}else{var _xr=I_divMod(_xm.a,_xq.a);return new T2(0,new T1(1,_xr.a),new T1(1,_xr.b));}}}},_xs=function(_xt,_xu){if(!B(_30(_xu,_uV))){var _xv=B(_xj(_xt,_xu));return new T2(0,_xv.a,_xv.b);}else{return E(_2V);}},_xw=function(_xx,_xy){while(1){var _xz=E(_xx);if(!_xz._){var _xA=E(_xz.a);if(_xA==( -2147483648)){_xx=new T1(1,I_fromInt( -2147483648));continue;}else{var _xB=E(_xy);if(!_xB._){return new T1(0,B(_sY(_xA,_xB.a)));}else{_xx=new T1(1,I_fromInt(_xA));_xy=_xB;continue;}}}else{var _xC=_xz.a,_xD=E(_xy);return (_xD._==0)?new T1(1,I_mod(_xC,I_fromInt(_xD.a))):new T1(1,I_mod(_xC,_xD.a));}}},_xE=function(_xF,_xG){if(!B(_30(_xG,_uV))){return new F(function(){return _xw(_xF,_xG);});}else{return E(_2V);}},_xH=function(_xI,_xJ){while(1){var _xK=E(_xI);if(!_xK._){var _xL=E(_xK.a);if(_xL==( -2147483648)){_xI=new T1(1,I_fromInt( -2147483648));continue;}else{var _xM=E(_xJ);if(!_xM._){return new T1(0,quot(_xL,_xM.a));}else{_xI=new T1(1,I_fromInt(_xL));_xJ=_xM;continue;}}}else{var _xN=_xK.a,_xO=E(_xJ);return (_xO._==0)?new T1(0,I_toInt(I_quot(_xN,I_fromInt(_xO.a)))):new T1(1,I_quot(_xN,_xO.a));}}},_xP=function(_xQ,_xR){if(!B(_30(_xR,_uV))){return new F(function(){return _xH(_xQ,_xR);});}else{return E(_2V);}},_xS=function(_xT,_xU){if(!B(_30(_xU,_uV))){var _xV=B(_3k(_xT,_xU));return new T2(0,_xV.a,_xV.b);}else{return E(_2V);}},_xW=function(_xX,_xY){while(1){var _xZ=E(_xX);if(!_xZ._){var _y0=E(_xZ.a);if(_y0==( -2147483648)){_xX=new T1(1,I_fromInt( -2147483648));continue;}else{var _y1=E(_xY);if(!_y1._){return new T1(0,_y0%_y1.a);}else{_xX=new T1(1,I_fromInt(_y0));_xY=_y1;continue;}}}else{var _y2=_xZ.a,_y3=E(_xY);return (_y3._==0)?new T1(1,I_rem(_y2,I_fromInt(_y3.a))):new T1(1,I_rem(_y2,_y3.a));}}},_y4=function(_y5,_y6){if(!B(_30(_y6,_uV))){return new F(function(){return _xW(_y5,_y6);});}else{return E(_2V);}},_y7=function(_y8){return E(_y8);},_y9=function(_ya){return E(_ya);},_yb=function(_yc){var _yd=E(_yc);if(!_yd._){var _ye=E(_yd.a);return (_ye==( -2147483648))?E(_6a):(_ye<0)?new T1(0, -_ye):E(_yd);}else{var _yf=_yd.a;return (I_compareInt(_yf,0)>=0)?E(_yd):new T1(1,I_negate(_yf));}},_yg=new T1(0,0),_yh=new T1(0, -1),_yi=function(_yj){var _yk=E(_yj);if(!_yk._){var _yl=_yk.a;return (_yl>=0)?(E(_yl)==0)?E(_yg):E(_3M):E(_yh);}else{var _ym=I_compareInt(_yk.a,0);return (_ym<=0)?(E(_ym)==0)?E(_yg):E(_yh):E(_3M);}},_yn={_:0,a:_3b,b:_5w,c:_uv,d:_6b,e:_yb,f:_yi,g:_y9},_yo=function(_yp,_yq){var _yr=E(_yp);if(!_yr._){var _ys=_yr.a,_yt=E(_yq);return (_yt._==0)?_ys!=_yt.a:(I_compareInt(_yt.a,_ys)==0)?false:true;}else{var _yu=_yr.a,_yv=E(_yq);return (_yv._==0)?(I_compareInt(_yu,_yv.a)==0)?false:true:(I_compare(_yu,_yv.a)==0)?false:true;}},_yw=new T2(0,_30,_yo),_yx=function(_yy,_yz){return (!B(_5h(_yy,_yz)))?E(_yy):E(_yz);},_yA=function(_yB,_yC){return (!B(_5h(_yB,_yC)))?E(_yC):E(_yB);},_yD={_:0,a:_yw,b:_1N,c:_3N,d:_5h,e:_3E,f:_wC,g:_yx,h:_yA},_yE=function(_yF){return new T2(0,E(_yF),E(_mf));},_yG=new T3(0,_yn,_yD,_yE),_yH={_:0,a:_yG,b:_x7,c:_xP,d:_y4,e:_xg,f:_xE,g:_xS,h:_xs,i:_y7},_yI=function(_yJ){return E(E(_yJ).b);},_yK=function(_yL){return E(E(_yL).g);},_yM=new T1(0,1),_yN=function(_yO,_yP,_yQ){var _yR=B(_yI(_yO)),_yS=B(_7j(_yR)),_yT=new T(function(){var _yU=new T(function(){var _yV=new T(function(){var _yW=new T(function(){return B(A3(_yK,_yO,_yH,new T(function(){return B(A3(_9a,_yR,_yP,_yQ));})));});return B(A2(_7z,_yS,_yW));}),_yX=new T(function(){return B(A2(_6K,_yS,new T(function(){return B(A2(_7z,_yS,_yM));})));});return B(A3(_7l,_yS,_yX,_yV));});return B(A3(_7l,_yS,_yU,_yQ));});return new F(function(){return A3(_6I,_yS,_yP,_yT);});},_yY=1.5707963267948966,_yZ=function(_z0){return 0.2/Math.cos(B(_yN(_wn,_z0,_yY))-0.7853981633974483);},_z1=2,_z2=new T(function(){var _z3=B(_oX(_yZ,1.2,_qs,_qg,_qg,_qg,_qg,_qr,_qn,_z1,_qg,_qg,_qm));return {_:0,a:E(_z3.a),b:E(_z3.b),c:E(_z3.c),d:E(_z3.d),e:E(_z3.e),f:E(_z3.f),g:E(_z3.g),h:_z3.h,i:_z3.i};}),_z4=new T2(1,_z2,_o),_z5=new T2(1,_qo,_z4),_z6=new T(function(){return B(unCStr("Negative range size"));}),_z7=new T(function(){return B(err(_z6));}),_z8=function(_){var _z9=B(_hh(_z5,0))-1|0,_za=function(_zb){if(_zb>=0){var _zc=newArr(_zb,_hn),_zd=_zc,_ze=E(_zb);if(!_ze){return new T4(0,E(_qq),E(_z9),0,_zd);}else{var _zf=function(_zg,_zh,_){while(1){var _zi=E(_zg);if(!_zi._){return E(_);}else{var _=_zd[_zh]=_zi.a;if(_zh!=(_ze-1|0)){var _zj=_zh+1|0;_zg=_zi.b;_zh=_zj;continue;}else{return E(_);}}}},_=B((function(_zk,_zl,_zm,_){var _=_zd[_zm]=_zk;if(_zm!=(_ze-1|0)){return new F(function(){return _zf(_zl,_zm+1|0,_);});}else{return E(_);}})(_qo,_z4,0,_));return new T4(0,E(_qq),E(_z9),_ze,_zd);}}else{return E(_z7);}};if(0>_z9){return new F(function(){return _za(0);});}else{return new F(function(){return _za(_z9+1|0);});}},_zn=function(_zo){var _zp=B(A1(_zo,_));return E(_zp);},_zq=new T(function(){return B(_zn(_z8));}),_zr=function(_zs,_zt,_){var _zu=B(A1(_zs,_)),_zv=B(A1(_zt,_));return _zu;},_zw=function(_zx,_zy,_){var _zz=B(A1(_zx,_)),_zA=B(A1(_zy,_));return new T(function(){return B(A1(_zz,_zA));});},_zB=function(_zC,_zD,_){var _zE=B(A1(_zD,_));return _zC;},_zF=function(_zG,_zH,_){var _zI=B(A1(_zH,_));return new T(function(){return B(A1(_zG,_zI));});},_zJ=new T2(0,_zF,_zB),_zK=function(_zL,_){return _zL;},_zM=function(_zN,_zO,_){var _zP=B(A1(_zN,_));return new F(function(){return A1(_zO,_);});},_zQ=new T5(0,_zJ,_zK,_zw,_zM,_zr),_zR=function(_zS){var _zT=E(_zS);return (E(_zT.b)-E(_zT.a)|0)+1|0;},_zU=function(_zV,_zW){var _zX=E(_zV),_zY=E(_zW);return (E(_zX.a)>_zY)?false:_zY<=E(_zX.b);},_zZ=function(_A0,_A1){var _A2=jsShowI(_A0);return new F(function(){return _f(fromJSStr(_A2),_A1);});},_A3=function(_A4,_A5,_A6){if(_A5>=0){return new F(function(){return _zZ(_A5,_A6);});}else{if(_A4<=6){return new F(function(){return _zZ(_A5,_A6);});}else{return new T2(1,_71,new T(function(){var _A7=jsShowI(_A5);return B(_f(fromJSStr(_A7),new T2(1,_70,_A6)));}));}}},_A8=function(_A9){return new F(function(){return _A3(0,E(_A9),_o);});},_Aa=function(_Ab,_Ac,_Ad){return new F(function(){return _A3(E(_Ab),E(_Ac),_Ad);});},_Ae=function(_Af,_Ag){return new F(function(){return _A3(0,E(_Af),_Ag);});},_Ah=function(_Ai,_Aj){return new F(function(){return _2B(_Ae,_Ai,_Aj);});},_Ak=new T3(0,_Aa,_A8,_Ah),_Al=0,_Am=function(_An,_Ao,_Ap){return new F(function(){return A1(_An,new T2(1,_2y,new T(function(){return B(A1(_Ao,_Ap));})));});},_Aq=new T(function(){return B(unCStr("foldr1"));}),_Ar=new T(function(){return B(_lF(_Aq));}),_As=function(_At,_Au){var _Av=E(_Au);if(!_Av._){return E(_Ar);}else{var _Aw=_Av.a,_Ax=E(_Av.b);if(!_Ax._){return E(_Aw);}else{return new F(function(){return A2(_At,_Aw,new T(function(){return B(_As(_At,_Ax));}));});}}},_Ay=new T(function(){return B(unCStr(" out of range "));}),_Az=new T(function(){return B(unCStr("}.index: Index "));}),_AA=new T(function(){return B(unCStr("Ix{"));}),_AB=new T2(1,_70,_o),_AC=new T2(1,_70,_AB),_AD=0,_AE=function(_AF){return E(E(_AF).a);},_AG=function(_AH,_AI,_AJ,_AK,_AL){var _AM=new T(function(){var _AN=new T(function(){var _AO=new T(function(){var _AP=new T(function(){var _AQ=new T(function(){return B(A3(_As,_Am,new T2(1,new T(function(){return B(A3(_AE,_AJ,_AD,_AK));}),new T2(1,new T(function(){return B(A3(_AE,_AJ,_AD,_AL));}),_o)),_AC));});return B(_f(_Ay,new T2(1,_71,new T2(1,_71,_AQ))));});return B(A(_AE,[_AJ,_Al,_AI,new T2(1,_70,_AP)]));});return B(_f(_Az,new T2(1,_71,_AO)));},1);return B(_f(_AH,_AN));},1);return new F(function(){return err(B(_f(_AA,_AM)));});},_AR=function(_AS,_AT,_AU,_AV,_AW){return new F(function(){return _AG(_AS,_AT,_AW,_AU,_AV);});},_AX=function(_AY,_AZ,_B0,_B1){var _B2=E(_B0);return new F(function(){return _AR(_AY,_AZ,_B2.a,_B2.b,_B1);});},_B3=function(_B4,_B5,_B6,_B7){return new F(function(){return _AX(_B7,_B6,_B5,_B4);});},_B8=new T(function(){return B(unCStr("Int"));}),_B9=function(_Ba,_Bb){return new F(function(){return _B3(_Ak,_Ba,_Bb,_B8);});},_Bc=function(_Bd,_Be){var _Bf=E(_Bd),_Bg=E(_Bf.a),_Bh=E(_Be);if(_Bg>_Bh){return new F(function(){return _B9(_Bf,_Bh);});}else{if(_Bh>E(_Bf.b)){return new F(function(){return _B9(_Bf,_Bh);});}else{return _Bh-_Bg|0;}}},_Bi=function(_Bj){var _Bk=E(_Bj);return new F(function(){return _sc(_Bk.a,_Bk.b);});},_Bl=function(_Bm){var _Bn=E(_Bm),_Bo=E(_Bn.a),_Bp=E(_Bn.b);return (_Bo>_Bp)?E(_Al):(_Bp-_Bo|0)+1|0;},_Bq=function(_Br,_Bs){return new F(function(){return _tB(_Bs,E(_Br).a);});},_Bt={_:0,a:_ur,b:_Bi,c:_Bc,d:_Bq,e:_zU,f:_Bl,g:_zR},_Bu=function(_Bv,_Bw){return new T2(1,_Bv,_Bw);},_Bx=function(_By,_Bz){var _BA=E(_Bz);return new T2(0,_BA.a,_BA.b);},_BB=function(_BC){return E(E(_BC).f);},_BD=function(_BE,_BF,_BG){var _BH=E(_BF),_BI=_BH.a,_BJ=_BH.b,_BK=function(_){var _BL=B(A2(_BB,_BE,_BH));if(_BL>=0){var _BM=newArr(_BL,_hn),_BN=_BM,_BO=E(_BL);if(!_BO){return new T(function(){return new T4(0,E(_BI),E(_BJ),0,_BN);});}else{var _BP=function(_BQ,_BR,_){while(1){var _BS=E(_BQ);if(!_BS._){return E(_);}else{var _=_BN[_BR]=_BS.a;if(_BR!=(_BO-1|0)){var _BT=_BR+1|0;_BQ=_BS.b;_BR=_BT;continue;}else{return E(_);}}}},_=B(_BP(_BG,0,_));return new T(function(){return new T4(0,E(_BI),E(_BJ),_BO,_BN);});}}else{return E(_z7);}};return new F(function(){return _zn(_BK);});},_BU=function(_BV,_BW,_BX,_BY){var _BZ=new T(function(){var _C0=E(_BY),_C1=_C0.c-1|0,_C2=new T(function(){return B(A2(_cW,_BW,_o));});if(0<=_C1){var _C3=new T(function(){return B(_96(_BW));}),_C4=function(_C5){var _C6=new T(function(){var _C7=new T(function(){return B(A1(_BX,new T(function(){return E(_C0.d[_C5]);})));});return B(A3(_9e,_C3,_Bu,_C7));});return new F(function(){return A3(_9c,_BW,_C6,new T(function(){if(_C5!=_C1){return B(_C4(_C5+1|0));}else{return E(_C2);}}));});};return B(_C4(0));}else{return E(_C2);}}),_C8=new T(function(){return B(_Bx(_BV,_BY));});return new F(function(){return A3(_9e,B(_96(_BW)),function(_C9){return new F(function(){return _BD(_BV,_C8,_C9);});},_BZ);});},_Ca=function(_Cb){return E(E(_Cb).a);},_Cc=function(_Cd,_Ce,_Cf,_Cg,_Ch){var _Ci=B(A2(_Ca,_Cd,E(_Ch)));return new F(function(){return A2(_Ce,_Cf,new T2(1,_Ci,E(_Cg)));});},_Cj="outline",_Ck="polygon",_Cl=function(_Cm){return new F(function(){return _jC(new T2(1,new T2(0,_Ck,new T(function(){return E(_Cm).h;})),new T2(1,new T2(0,_Cj,new T(function(){return E(_Cm).i;})),_o)));});},_Cn=function(_Co){return new F(function(){return _Cl(_Co);});},_Cp=function(_Cq){return new F(function(){return __lst2arr(B(_jY(_Cn,_Cq)));});},_Cr=new T2(0,_Cn,_Cp),_Cs=function(_Ct,_){var _Cu=E(_Ct);if(!_Cu._){return _o;}else{var _Cv=B(_Cs(_Cu.b,_));return new T2(1,_jB,_Cv);}},_Cw=function(_Cx,_){var _Cy=__arr2lst(0,_Cx);return new F(function(){return _Cs(_Cy,_);});},_Cz=function(_CA,_){return new F(function(){return _Cw(E(_CA),_);});},_CB=function(_){return _jB;},_CC=function(_CD,_){return new F(function(){return _CB(_);});},_CE=new T2(0,_CC,_Cz),_CF=function(_CG){return E(E(_CG).a);},_CH=function(_CI,_CJ,_CK,_){var _CL=__apply(_CJ,E(_CK));return new F(function(){return A3(_CF,_CI,_CL,_);});},_CM=function(_CN,_CO,_CP,_){return new F(function(){return _CH(_CN,E(_CO),_CP,_);});},_CQ=function(_CR,_CS,_CT,_){return new F(function(){return _CM(_CR,_CS,_CT,_);});},_CU=function(_CV,_CW,_){return new F(function(){return _CQ(_CE,_CV,_CW,_);});},_CX=new T(function(){return eval("drawObject");}),_CY=function(_CZ){return new F(function(){return _Cc(_Cr,_CU,_CX,_o,_CZ);});},_D0=new T(function(){return eval("__strict(draw)");}),_D1=function(_D2){return E(_D2);},_D3=function(_D4){return E(_D4);},_D5=function(_D6,_D7){return E(_D7);},_D8=function(_D9,_Da){return E(_D9);},_Db=function(_Dc){return E(_Dc);},_Dd=new T2(0,_Db,_D8),_De=function(_Df,_Dg){return E(_Df);},_Dh=new T5(0,_Dd,_D3,_D1,_D5,_De),_Di="w2x",_Dj="w1z",_Dk="w1y",_Dl="w1x",_Dm="c2y",_Dn="c2x",_Do="c1y",_Dp="c1x",_Dq="w2z",_Dr="w2y",_Ds=function(_Dt,_){var _Du=__get(_Dt,E(_Dl)),_Dv=__get(_Dt,E(_Dk)),_Dw=__get(_Dt,E(_Dj)),_Dx=__get(_Dt,E(_Di)),_Dy=__get(_Dt,E(_Dr)),_Dz=__get(_Dt,E(_Dq)),_DA=__get(_Dt,E(_Dp)),_DB=__get(_Dt,E(_Do)),_DC=__get(_Dt,E(_Dn)),_DD=__get(_Dt,E(_Dm));return new T4(0,E(new T3(0,E(_Du),E(_Dv),E(_Dw))),E(new T3(0,E(_Dx),E(_Dy),E(_Dz))),E(new T2(0,E(_DA),E(_DB))),E(new T2(0,E(_DC),E(_DD))));},_DE=function(_DF,_){var _DG=E(_DF);if(!_DG._){return _o;}else{var _DH=B(_Ds(E(_DG.a),_)),_DI=B(_DE(_DG.b,_));return new T2(1,_DH,_DI);}},_DJ=function(_DK,_DL,_){while(1){var _DM=B((function(_DN,_DO,_){var _DP=E(_DN);if(!_DP._){return new T2(0,_jB,_DO);}else{var _DQ=B(A2(_DP.a,_DO,_));_DK=_DP.b;_DL=new T(function(){return E(E(_DQ).b);});return __continue;}})(_DK,_DL,_));if(_DM!=__continue){return _DM;}}},_DR=function(_DS,_DT,_DU,_DV,_DW,_DX,_DY,_DZ,_E0){var _E1=B(_7l(_DS));return new T2(0,new T3(0,E(B(A1(B(A1(_E1,_DT)),_DX))),E(B(A1(B(A1(_E1,_DU)),_DY))),E(B(A1(B(A1(_E1,_DV)),_DZ)))),B(A1(B(A1(_E1,_DW)),_E0)));},_E2=function(_E3,_E4,_E5,_E6,_E7,_E8,_E9,_Ea,_Eb){var _Ec=B(_6I(_E3));return new T2(0,new T3(0,E(B(A1(B(A1(_Ec,_E4)),_E8))),E(B(A1(B(A1(_Ec,_E5)),_E9))),E(B(A1(B(A1(_Ec,_E6)),_Ea)))),B(A1(B(A1(_Ec,_E7)),_Eb)));},_Ed=1.0e-2,_Ee=function(_Ef,_Eg,_Eh,_Ei,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev){var _Ew=B(_DR(_in,_Em,_En,_Eo,_Ep,_Ed,_Ed,_Ed,_Ed)),_Ex=E(_Ew.a),_Ey=B(_E2(_in,_Ei,_Ej,_Ek,_El,_Ex.a,_Ex.b,_Ex.c,_Ew.b)),_Ez=E(_Ey.a);return new F(function(){return _oe(_Ef,_Eg,_Eh,_Ez.a,_Ez.b,_Ez.c,_Ey.b,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev);});},_EA=function(_EB){var _EC=E(_EB),_ED=E(_EC.d),_EE=E(_ED.a),_EF=E(_EC.e),_EG=E(_EF.a),_EH=E(_EC.f),_EI=B(_Ee(_EC.a,_EC.b,_EC.c,_EE.a,_EE.b,_EE.c,_ED.b,_EG.a,_EG.b,_EG.c,_EF.b,_EH.a,_EH.b,_EH.c,_EC.g,_EC.h,_EC.i));return {_:0,a:E(_EI.a),b:E(_EI.b),c:E(_EI.c),d:E(_EI.d),e:E(_EI.e),f:E(_EI.f),g:E(_EI.g),h:_EI.h,i:_EI.i};},_EJ=function(_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES){var _ET=B(_7j(B(_7h(_EK))));return new F(function(){return A3(_6I,_ET,new T(function(){return B(_7n(_EK,_EL,_EM,_EN,_EP,_EQ,_ER));}),new T(function(){return B(A3(_7l,_ET,_EO,_ES));}));});},_EU=function(_EV,_){return new T2(0,_o,_EV);},_EW=0.6,_EX=1,_EY=new T(function(){return B(unCStr(")"));}),_EZ=function(_F0,_F1){var _F2=new T(function(){var _F3=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_A3(0,_F0,_o)),_EY));})));},1);return B(_f(B(_A3(0,_F1,_o)),_F3));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_F2)));});},_F4=function(_F5,_F6){var _F7=new T(function(){var _F8=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_A3(0,_F6,_o)),_EY));})));},1);return B(_f(B(_A3(0,_F5,_o)),_F8));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_F7)));});},_F9=new T(function(){return B(unCStr("base"));}),_Fa=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fb=new T(function(){return B(unCStr("IOException"));}),_Fc=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_F9,_Fa,_Fb),_Fd=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fc,_o,_o),_Fe=function(_Ff){return E(_Fd);},_Fg=function(_Fh){var _Fi=E(_Fh);return new F(function(){return _28(B(_26(_Fi.a)),_Fe,_Fi.b);});},_Fj=new T(function(){return B(unCStr(": "));}),_Fk=new T(function(){return B(unCStr(")"));}),_Fl=new T(function(){return B(unCStr(" ("));}),_Fm=new T(function(){return B(unCStr("interrupted"));}),_Fn=new T(function(){return B(unCStr("resource vanished"));}),_Fo=new T(function(){return B(unCStr("unsatisified constraints"));}),_Fp=new T(function(){return B(unCStr("user error"));}),_Fq=new T(function(){return B(unCStr("permission denied"));}),_Fr=new T(function(){return B(unCStr("illegal operation"));}),_Fs=new T(function(){return B(unCStr("end of file"));}),_Ft=new T(function(){return B(unCStr("resource exhausted"));}),_Fu=new T(function(){return B(unCStr("resource busy"));}),_Fv=new T(function(){return B(unCStr("does not exist"));}),_Fw=new T(function(){return B(unCStr("already exists"));}),_Fx=new T(function(){return B(unCStr("timeout"));}),_Fy=new T(function(){return B(unCStr("unsupported operation"));}),_Fz=new T(function(){return B(unCStr("hardware fault"));}),_FA=new T(function(){return B(unCStr("inappropriate type"));}),_FB=new T(function(){return B(unCStr("invalid argument"));}),_FC=new T(function(){return B(unCStr("failed"));}),_FD=new T(function(){return B(unCStr("protocol error"));}),_FE=new T(function(){return B(unCStr("system error"));}),_FF=function(_FG,_FH){switch(E(_FG)){case 0:return new F(function(){return _f(_Fw,_FH);});break;case 1:return new F(function(){return _f(_Fv,_FH);});break;case 2:return new F(function(){return _f(_Fu,_FH);});break;case 3:return new F(function(){return _f(_Ft,_FH);});break;case 4:return new F(function(){return _f(_Fs,_FH);});break;case 5:return new F(function(){return _f(_Fr,_FH);});break;case 6:return new F(function(){return _f(_Fq,_FH);});break;case 7:return new F(function(){return _f(_Fp,_FH);});break;case 8:return new F(function(){return _f(_Fo,_FH);});break;case 9:return new F(function(){return _f(_FE,_FH);});break;case 10:return new F(function(){return _f(_FD,_FH);});break;case 11:return new F(function(){return _f(_FC,_FH);});break;case 12:return new F(function(){return _f(_FB,_FH);});break;case 13:return new F(function(){return _f(_FA,_FH);});break;case 14:return new F(function(){return _f(_Fz,_FH);});break;case 15:return new F(function(){return _f(_Fy,_FH);});break;case 16:return new F(function(){return _f(_Fx,_FH);});break;case 17:return new F(function(){return _f(_Fn,_FH);});break;default:return new F(function(){return _f(_Fm,_FH);});}},_FI=new T(function(){return B(unCStr("}"));}),_FJ=new T(function(){return B(unCStr("{handle: "));}),_FK=function(_FL,_FM,_FN,_FO,_FP,_FQ){var _FR=new T(function(){var _FS=new T(function(){var _FT=new T(function(){var _FU=E(_FO);if(!_FU._){return E(_FQ);}else{var _FV=new T(function(){return B(_f(_FU,new T(function(){return B(_f(_Fk,_FQ));},1)));},1);return B(_f(_Fl,_FV));}},1);return B(_FF(_FM,_FT));}),_FW=E(_FN);if(!_FW._){return E(_FS);}else{return B(_f(_FW,new T(function(){return B(_f(_Fj,_FS));},1)));}}),_FX=E(_FP);if(!_FX._){var _FY=E(_FL);if(!_FY._){return E(_FR);}else{var _FZ=E(_FY.a);if(!_FZ._){var _G0=new T(function(){var _G1=new T(function(){return B(_f(_FI,new T(function(){return B(_f(_Fj,_FR));},1)));},1);return B(_f(_FZ.a,_G1));},1);return new F(function(){return _f(_FJ,_G0);});}else{var _G2=new T(function(){var _G3=new T(function(){return B(_f(_FI,new T(function(){return B(_f(_Fj,_FR));},1)));},1);return B(_f(_FZ.a,_G3));},1);return new F(function(){return _f(_FJ,_G2);});}}}else{return new F(function(){return _f(_FX.a,new T(function(){return B(_f(_Fj,_FR));},1));});}},_G4=function(_G5){var _G6=E(_G5);return new F(function(){return _FK(_G6.a,_G6.b,_G6.c,_G6.d,_G6.f,_o);});},_G7=function(_G8,_G9,_Ga){var _Gb=E(_G9);return new F(function(){return _FK(_Gb.a,_Gb.b,_Gb.c,_Gb.d,_Gb.f,_Ga);});},_Gc=function(_Gd,_Ge){var _Gf=E(_Gd);return new F(function(){return _FK(_Gf.a,_Gf.b,_Gf.c,_Gf.d,_Gf.f,_Ge);});},_Gg=function(_Gh,_Gi){return new F(function(){return _2B(_Gc,_Gh,_Gi);});},_Gj=new T3(0,_G7,_G4,_Gg),_Gk=new T(function(){return new T5(0,_Fe,_Gj,_Gl,_Fg,_G4);}),_Gl=function(_Gm){return new T2(0,_Gk,_Gm);},_Gn=__Z,_Go=7,_Gp=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:68:3-9"));}),_Gq=new T6(0,_Gn,_Go,_o,_Gp,_Gn,_Gn),_Gr=new T(function(){return B(_Gl(_Gq));}),_Gs=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:67:3-9"));}),_Gt=new T6(0,_Gn,_Go,_o,_Gs,_Gn,_Gn),_Gu=new T(function(){return B(_Gl(_Gt));}),_Gv=function(_Gw){var _Gx=E(_Gw);if(!_Gx._){return E(_EU);}else{var _Gy=new T(function(){return B(_Gv(_Gx.b));}),_Gz=function(_GA){var _GB=E(_GA);if(!_GB._){return E(_Gy);}else{var _GC=_GB.a,_GD=new T(function(){return B(_Gz(_GB.b));}),_GE=new T(function(){return 0.1*E(E(_GC).e)/1.0e-2;}),_GF=new T(function(){var _GG=E(_GC);if(_GG.a!=_GG.b){return E(_EX);}else{return E(_EW);}}),_GH=function(_GI,_){var _GJ=E(_GI),_GK=_GJ.c,_GL=_GJ.d,_GM=E(_GJ.a),_GN=E(_GJ.b),_GO=E(_GC),_GP=_GO.a,_GQ=_GO.b,_GR=E(_GO.c),_GS=_GR.b,_GT=E(_GR.a),_GU=_GT.a,_GV=_GT.b,_GW=_GT.c,_GX=E(_GO.d),_GY=_GX.b,_GZ=E(_GX.a),_H0=_GZ.a,_H1=_GZ.b,_H2=_GZ.c;if(_GM>_GP){return new F(function(){return die(_Gu);});}else{if(_GP>_GN){return new F(function(){return die(_Gu);});}else{if(_GM>_GQ){return new F(function(){return die(_Gr);});}else{if(_GQ>_GN){return new F(function(){return die(_Gr);});}else{var _H3=_GP-_GM|0;if(0>_H3){return new F(function(){return _EZ(_GK,_H3);});}else{if(_H3>=_GK){return new F(function(){return _EZ(_GK,_H3);});}else{var _H4=E(_GL[_H3]),_H5=E(_H4.c),_H6=_H5.b,_H7=E(_H5.a),_H8=_H7.a,_H9=_H7.b,_Ha=_H7.c,_Hb=E(_H4.e),_Hc=_Hb.b,_Hd=E(_Hb.a),_He=_Hd.a,_Hf=_Hd.b,_Hg=_Hd.c,_Hh=B(_DR(_in,_GU,_GV,_GW,_GS,_H8,_H9,_Ha,_H6)),_Hi=E(_Hh.a),_Hj=B(_DR(_in,_Hi.a,_Hi.b,_Hi.c,_Hh.b,_GU,_GV,_GW,_GS)),_Hk=E(_Hj.a),_Hl=_GQ-_GM|0;if(0>_Hl){return new F(function(){return _F4(_Hl,_GK);});}else{if(_Hl>=_GK){return new F(function(){return _F4(_Hl,_GK);});}else{var _Hm=E(_GL[_Hl]),_Hn=E(_Hm.c),_Ho=_Hn.b,_Hp=E(_Hn.a),_Hq=_Hp.a,_Hr=_Hp.b,_Hs=_Hp.c,_Ht=E(_Hm.e),_Hu=E(_Ht.a),_Hv=B(_DR(_in,_H0,_H1,_H2,_GY,_Hq,_Hr,_Hs,_Ho)),_Hw=E(_Hv.a),_Hx=B(_DR(_in,_Hw.a,_Hw.b,_Hw.c,_Hv.b,_H0,_H1,_H2,_GY)),_Hy=E(_Hx.a),_Hz=E(_Hk.a)+E(_Hk.b)+E(_Hk.c)+E(_Hj.b)+E(_Hy.a)+E(_Hy.b)+E(_Hy.c)+E(_Hx.b);if(!_Hz){var _HA=B(A2(_GD,_GJ,_));return new T2(0,new T2(1,_jB,new T(function(){return E(E(_HA).a);})),new T(function(){return E(E(_HA).b);}));}else{var _HB= -((B(_EJ(_iT,_He,_Hf,_Hg,_Hc,_GU,_GV,_GW,_GS))-B(_EJ(_iT,_Hu.a,_Hu.b,_Hu.c,_Ht.b,_H0,_H1,_H2,_GY))-E(_GE))/_Hz);if(_HB<0){var _HC=B(A2(_GD,_GJ,_));return new T2(0,new T2(1,_jB,new T(function(){return E(E(_HC).a);})),new T(function(){return E(E(_HC).b);}));}else{var _HD=new T(function(){var _HE=function(_){var _HF=newArr(_GK,_hn),_HG=_HF,_HH=function(_HI,_){while(1){if(_HI!=_GK){var _=_HG[_HI]=_GL[_HI],_HJ=_HI+1|0;_HI=_HJ;continue;}else{return E(_);}}},_=B(_HH(0,_)),_=_HG[_H3]=new T(function(){var _HK=B(_DR(_in,_H8,_H9,_Ha,_H6,_GU,_GV,_GW,_GS)),_HL=E(_HK.a),_HM=_HB*E(_GF),_HN=B(_DR(_in,_HL.a,_HL.b,_HL.c,_HK.b,_HM,_HM,_HM,_HM)),_HO=E(_HN.a),_HP=B(_E2(_in,_He,_Hf,_Hg,_Hc,_HO.a,_HO.b,_HO.c,_HN.b));return {_:0,a:E(_H4.a),b:E(_H4.b),c:E(_H5),d:E(_H4.d),e:E(new T2(0,E(_HP.a),E(_HP.b))),f:E(_H4.f),g:E(_H4.g),h:_H4.h,i:_H4.i};});return new T4(0,E(_GM),E(_GN),_GK,_HG);},_HQ=B(_zn(_HE)),_HR=_HQ.c,_HS=_HQ.d,_HT=E(_HQ.a),_HU=E(_HQ.b);if(_HT>_GQ){return E(_HQ);}else{if(_GQ>_HU){return E(_HQ);}else{var _HV=function(_){var _HW=newArr(_HR,_hn),_HX=_HW,_HY=function(_HZ,_){while(1){if(_HZ!=_HR){var _=_HX[_HZ]=_HS[_HZ],_I0=_HZ+1|0;_HZ=_I0;continue;}else{return E(_);}}},_=B(_HY(0,_)),_I1=_GQ-_HT|0;if(0>_I1){return new F(function(){return _F4(_I1,_HR);});}else{if(_I1>=_HR){return new F(function(){return _F4(_I1,_HR);});}else{var _=_HX[_I1]=new T(function(){var _I2=E(_HS[_I1]),_I3=E(_I2.e),_I4=E(_I3.a),_I5=B(_DR(_in,_Hq,_Hr,_Hs,_Ho,_H0,_H1,_H2,_GY)),_I6=E(_I5.a),_I7=_HB*E(_GF),_I8=B(_DR(_in,_I6.a,_I6.b,_I6.c,_I5.b,_I7,_I7,_I7,_I7)),_I9=E(_I8.a),_Ia=B(_E2(_in,_I4.a,_I4.b,_I4.c,_I3.b, -E(_I9.a), -E(_I9.b), -E(_I9.c), -E(_I8.b)));return {_:0,a:E(_I2.a),b:E(_I2.b),c:E(_I2.c),d:E(_I2.d),e:E(new T2(0,E(_Ia.a),E(_Ia.b))),f:E(_I2.f),g:E(_I2.g),h:_I2.h,i:_I2.i};});return new T4(0,E(_HT),E(_HU),_HR,_HX);}}};return B(_zn(_HV));}}}),_Ib=B(A2(_GD,_HD,_));return new T2(0,new T2(1,_jB,new T(function(){return E(E(_Ib).a);})),new T(function(){return E(E(_Ib).b);}));}}}}}}}}}}};return E(_GH);}};return new F(function(){return _Gz(_Gx.a);});}},_Ic=function(_,_Id){var _Ie=new T(function(){return B(_Gv(E(_Id).a));}),_If=function(_Ig){var _Ih=E(_Ig);return (_Ih==1)?E(new T2(1,_Ie,_o)):new T2(1,_Ie,new T(function(){return B(_If(_Ih-1|0));}));},_Ii=B(_DJ(B(_If(5)),new T(function(){return E(E(_Id).b);}),_)),_Ij=new T(function(){return B(_BU(_Bt,_Dh,_EA,new T(function(){return E(E(_Ii).b);})));});return new T2(0,_jB,_Ij);},_Ik=function(_Il){var _Im=E(_Il),_In=E(_Im.b),_Io=E(_Im.e),_Ip=E(_Io.a),_Iq=E(_Im.g),_Ir=B(_kY(_iT,_In.a,_In.b,_In.c,_Iq.a,_Iq.b,_Iq.c));return {_:0,a:E(_Im.a),b:E(_In),c:E(_Im.c),d:E(_Im.d),e:E(new T2(0,E(new T3(0,E(_Ip.a)+E(_Ir.a)*1.0e-2,E(_Ip.b)+E(_Ir.b)*1.0e-2,E(_Ip.c)+E(_Ir.c)*1.0e-2)),E(_Io.b))),f:E(_Im.f),g:E(_Iq),h:_Im.h,i:_Im.i};},_Is=0,_It=new T(function(){return eval("collide");}),_Iu=function(_Iv){var _Iw=E(_Iv);if(!_Iw._){return __Z;}else{return new F(function(){return _f(_Iw.a,new T(function(){return B(_Iu(_Iw.b));},1));});}},_Ix=new T2(0,_iT,_js),_Iy=new T(function(){return B(_gT(_Ix));}),_Iz=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_IA=new T6(0,_Gn,_Go,_o,_Iz,_Gn,_Gn),_IB=new T(function(){return B(_Gl(_IA));}),_IC=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));}),_ID=new T6(0,_Gn,_Go,_o,_IC,_Gn,_Gn),_IE=new T(function(){return B(_Gl(_ID));}),_IF=function(_IG,_){var _IH=B(_BU(_Bt,_Dh,_Ik,_IG)),_II=E(_IH.a),_IJ=E(_IH.b);if(_II<=_IJ){var _IK=function(_IL,_IM,_){if(_IL<=_IJ){var _IN=E(_IM),_IO=function(_IP,_IQ,_IR,_IS,_IT,_){if(_IQ>_IL){return new F(function(){return die(_IB);});}else{if(_IL>_IR){return new F(function(){return die(_IB);});}else{if(_IQ>_IP){return new F(function(){return die(_IE);});}else{if(_IP>_IR){return new F(function(){return die(_IE);});}else{var _IU=_IL-_IQ|0;if(0>_IU){return new F(function(){return _F4(_IU,_IS);});}else{if(_IU>=_IS){return new F(function(){return _F4(_IU,_IS);});}else{var _IV=E(_IT[_IU]),_IW=_IP-_IQ|0;if(0>_IW){return new F(function(){return _F4(_IW,_IS);});}else{if(_IW>=_IS){return new F(function(){return _F4(_IW,_IS);});}else{var _IX=E(_IT[_IW]),_IY=__app2(E(_It),B(_jC(new T2(1,new T2(0,_Ck,_IV.h),new T2(1,new T2(0,_Cj,_IV.i),_o)))),B(_jC(new T2(1,new T2(0,_Ck,_IX.h),new T2(1,new T2(0,_Cj,_IX.i),_o))))),_IZ=__arr2lst(0,_IY),_J0=B(_DE(_IZ,_)),_J1=function(_J2,_J3,_){var _J4=E(_J2);if(!_J4._){return new T2(0,_o,_J3);}else{var _J5=E(_J4.a),_J6=E(_J5.b),_J7=E(_J5.a),_J8=B(_J1(_J4.b,_J3,_));return new T2(0,new T2(1,new T(function(){var _J9=E(_J6.a)+ -E(_J7.a),_Ja=E(_J6.b)+ -E(_J7.b),_Jb=E(_J6.c)+ -E(_J7.c),_Jc=B(A1(_Iy,_J7)),_Jd=_Jc.a,_Je=_Jc.b,_Jf=_Jc.c,_Jg=B(_kb(_iT,_Jd,_Je,_Jf)),_Jh=Math.sqrt(B(_7n(_iT,_J9,_Ja,_Jb,_J9,_Ja,_Jb))),_Ji=1/_Jh,_Jj=_J9*_Ji,_Jk=_Ja*_Ji,_Jl=_Jb*_Ji,_Jm=B(_kY(_iT,_Jj,_Jk,_Jl,_Jg.a,_Jg.b,_Jg.c)),_Jn=B(_kb(_iT,_Jd,_Je,_Jf)),_Jo=B(_kY(_iT,_Jj,_Jk,_Jl,_Jn.a,_Jn.b,_Jn.c));return new T5(0,_IL,_IP,E(new T2(0,E(new T3(0,E(_Jm.a),E(_Jm.b),E(_Jm.c))),E(_Is))),E(new T2(0,E(new T3(0,E(_Jo.a),E(_Jo.b),E(_Jo.c))),E(_Is))),_Jh);}),new T(function(){return E(E(_J8).a);})),new T(function(){return E(E(_J8).b);}));}},_Jp=B(_J1(_J0,new T4(0,E(_IQ),E(_IR),_IS,_IT),_));if(_IP!=_IJ){var _Jq=E(_Jp),_Jr=E(_Jq.b),_Js=B(_IO(_IP+1|0,E(_Jr.a),E(_Jr.b),_Jr.c,_Jr.d,_));return new T2(0,new T2(1,_Jq.a,new T(function(){return E(E(_Js).a);})),new T(function(){return E(E(_Js).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_Jp).a);}),_o),new T(function(){return E(E(_Jp).b);}));}}}}}}}}}},_Jt=B(_IO(_IL,E(_IN.a),E(_IN.b),_IN.c,_IN.d,_));if(_IL!=_IJ){var _Ju=B(_IK(_IL+1|0,new T(function(){return E(E(_Jt).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Iu(E(_Jt).a));}),new T(function(){return E(E(_Ju).a);})),new T(function(){return E(E(_Ju).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Iu(E(_Jt).a));}),_o),new T(function(){return E(E(_Jt).b);}));}}else{if(_IL!=_IJ){var _Jv=B(_IK(_IL+1|0,_IM,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Jv).a);})),new T(function(){return E(E(_Jv).b);}));}else{return new T2(0,new T2(1,_o,_o),_IM);}}},_Jw=function(_Jx,_Jy,_Jz,_JA,_JB,_){if(_Jx<=_IJ){var _JC=function(_JD,_JE,_JF,_JG,_JH,_){if(_JE>_Jx){return new F(function(){return die(_IB);});}else{if(_Jx>_JF){return new F(function(){return die(_IB);});}else{if(_JE>_JD){return new F(function(){return die(_IE);});}else{if(_JD>_JF){return new F(function(){return die(_IE);});}else{var _JI=_Jx-_JE|0;if(0>_JI){return new F(function(){return _F4(_JI,_JG);});}else{if(_JI>=_JG){return new F(function(){return _F4(_JI,_JG);});}else{var _JJ=E(_JH[_JI]),_JK=_JD-_JE|0;if(0>_JK){return new F(function(){return _F4(_JK,_JG);});}else{if(_JK>=_JG){return new F(function(){return _F4(_JK,_JG);});}else{var _JL=E(_JH[_JK]),_JM=__app2(E(_It),B(_jC(new T2(1,new T2(0,_Ck,_JJ.h),new T2(1,new T2(0,_Cj,_JJ.i),_o)))),B(_jC(new T2(1,new T2(0,_Ck,_JL.h),new T2(1,new T2(0,_Cj,_JL.i),_o))))),_JN=__arr2lst(0,_JM),_JO=B(_DE(_JN,_)),_JP=function(_JQ,_JR,_){var _JS=E(_JQ);if(!_JS._){return new T2(0,_o,_JR);}else{var _JT=E(_JS.a),_JU=E(_JT.b),_JV=E(_JT.a),_JW=B(_JP(_JS.b,_JR,_));return new T2(0,new T2(1,new T(function(){var _JX=E(_JU.a)+ -E(_JV.a),_JY=E(_JU.b)+ -E(_JV.b),_JZ=E(_JU.c)+ -E(_JV.c),_K0=B(A1(_Iy,_JV)),_K1=_K0.a,_K2=_K0.b,_K3=_K0.c,_K4=B(_kb(_iT,_K1,_K2,_K3)),_K5=Math.sqrt(B(_7n(_iT,_JX,_JY,_JZ,_JX,_JY,_JZ))),_K6=1/_K5,_K7=_JX*_K6,_K8=_JY*_K6,_K9=_JZ*_K6,_Ka=B(_kY(_iT,_K7,_K8,_K9,_K4.a,_K4.b,_K4.c)),_Kb=B(_kb(_iT,_K1,_K2,_K3)),_Kc=B(_kY(_iT,_K7,_K8,_K9,_Kb.a,_Kb.b,_Kb.c));return new T5(0,_Jx,_JD,E(new T2(0,E(new T3(0,E(_Ka.a),E(_Ka.b),E(_Ka.c))),E(_Is))),E(new T2(0,E(new T3(0,E(_Kc.a),E(_Kc.b),E(_Kc.c))),E(_Is))),_K5);}),new T(function(){return E(E(_JW).a);})),new T(function(){return E(E(_JW).b);}));}},_Kd=B(_JP(_JO,new T4(0,E(_JE),E(_JF),_JG,_JH),_));if(_JD!=_IJ){var _Ke=E(_Kd),_Kf=E(_Ke.b),_Kg=B(_JC(_JD+1|0,E(_Kf.a),E(_Kf.b),_Kf.c,_Kf.d,_));return new T2(0,new T2(1,_Ke.a,new T(function(){return E(E(_Kg).a);})),new T(function(){return E(E(_Kg).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_Kd).a);}),_o),new T(function(){return E(E(_Kd).b);}));}}}}}}}}}},_Kh=B(_JC(_Jx,_Jy,_Jz,_JA,_JB,_));if(_Jx!=_IJ){var _Ki=B(_IK(_Jx+1|0,new T(function(){return E(E(_Kh).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Iu(E(_Kh).a));}),new T(function(){return E(E(_Ki).a);})),new T(function(){return E(E(_Ki).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Iu(E(_Kh).a));}),_o),new T(function(){return E(E(_Kh).b);}));}}else{if(_Jx!=_IJ){var _Kj=B(_Jw(_Jx+1|0,_Jy,_Jz,_JA,_JB,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Kj).a);})),new T(function(){return E(E(_Kj).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_Jy),E(_Jz),_JA,_JB));}}},_Kk=B(_Jw(_II,_II,_IJ,_IH.c,_IH.d,_));return new F(function(){return _Ic(_,_Kk);});}else{return new F(function(){return _Ic(_,new T2(0,_o,_IH));});}},_Kl=new T(function(){return eval("__strict(refresh)");}),_Km=function(_Kn,_){var _Ko=__app0(E(_Kl)),_Kp=__app0(E(_D0)),_Kq=B(A(_BU,[_Bt,_zQ,_CY,_Kn,_])),_Kr=B(_IF(_Kn,_));return new T(function(){return E(E(_Kr).b);});},_Ks=function(_Kt,_){while(1){var _Ku=E(_Kt);if(!_Ku._){return _jB;}else{var _Kv=_Ku.b,_Kw=E(_Ku.a);switch(_Kw._){case 0:var _Kx=B(A1(_Kw.a,_));_Kt=B(_f(_Kv,new T2(1,_Kx,_o)));continue;case 1:_Kt=B(_f(_Kv,_Kw.a));continue;default:_Kt=_Kv;continue;}}}},_Ky=function(_Kz,_KA,_){var _KB=E(_Kz);switch(_KB._){case 0:var _KC=B(A1(_KB.a,_));return new F(function(){return _Ks(B(_f(_KA,new T2(1,_KC,_o))),_);});break;case 1:return new F(function(){return _Ks(B(_f(_KA,_KB.a)),_);});break;default:return new F(function(){return _Ks(_KA,_);});}},_KD=function(_KE,_KF,_KG){return new F(function(){return A1(_KE,function(_KH){return new F(function(){return A2(_KF,_KH,_KG);});});});},_KI=function(_KJ,_KK,_KL){var _KM=function(_KN){var _KO=new T(function(){return B(A1(_KL,_KN));});return new F(function(){return A1(_KK,function(_KP){return E(_KO);});});};return new F(function(){return A1(_KJ,_KM);});},_KQ=function(_KR,_KS,_KT){var _KU=new T(function(){return B(A1(_KS,function(_KV){return new F(function(){return A1(_KT,_KV);});}));});return new F(function(){return A1(_KR,function(_KW){return E(_KU);});});},_KX=function(_KY,_KZ,_L0){var _L1=function(_L2){var _L3=function(_L4){return new F(function(){return A1(_L0,new T(function(){return B(A1(_L2,_L4));}));});};return new F(function(){return A1(_KZ,_L3);});};return new F(function(){return A1(_KY,_L1);});},_L5=function(_L6,_L7){return new F(function(){return A1(_L7,_L6);});},_L8=function(_L9,_La,_Lb){var _Lc=new T(function(){return B(A1(_Lb,_L9));});return new F(function(){return A1(_La,function(_Ld){return E(_Lc);});});},_Le=function(_Lf,_Lg,_Lh){var _Li=function(_Lj){return new F(function(){return A1(_Lh,new T(function(){return B(A1(_Lf,_Lj));}));});};return new F(function(){return A1(_Lg,_Li);});},_Lk=new T2(0,_Le,_L8),_Ll=new T5(0,_Lk,_L5,_KX,_KQ,_KI),_Lm=function(_Ln){return E(E(_Ln).b);},_Lo=function(_Lp,_Lq){return new F(function(){return A3(_Lm,_Lr,_Lp,function(_Ls){return E(_Lq);});});},_Lt=function(_Lu){return new F(function(){return err(_Lu);});},_Lr=new T(function(){return new T5(0,_Ll,_KD,_Lo,_L5,_Lt);}),_Lv=function(_Lw,_Lx){return new T1(0,function(_){return new F(function(){return _zF(_Lx,_Lw,_);});});},_Ly=new T2(0,_Lr,_Lv),_Lz=function(_LA){return new T0(2);},_LB=function(_LC){var _LD=new T(function(){return B(A1(_LC,_Lz));}),_LE=function(_LF){return new T1(1,new T2(1,new T(function(){return B(A1(_LF,_jB));}),new T2(1,_LD,_o)));};return E(_LE);},_LG=new T3(0,_Ly,_7U,_LB),_LH=new T(function(){return E(_oW);}),_LI=new T0(2),_LJ=function(_LK){return E(E(_LK).b);},_LL=function(_LM,_LN,_LO){var _LP=function(_LQ){var _LR=function(_){var _LS=E(_LN),_LT=rMV(_LS),_LU=E(_LT);if(!_LU._){var _LV=new T(function(){var _LW=new T(function(){return B(A1(_LQ,_jB));});return B(_f(_LU.b,new T2(1,new T2(0,_LO,function(_LX){return E(_LW);}),_o)));}),_=wMV(_LS,new T2(0,_LU.a,_LV));return _LI;}else{var _LY=E(_LU.a);if(!_LY._){var _=wMV(_LS,new T2(0,_LO,_o));return new T(function(){return B(A1(_LQ,_jB));});}else{var _=wMV(_LS,new T1(1,_LY.b));return new T1(1,new T2(1,new T(function(){return B(A1(_LQ,_jB));}),new T2(1,new T(function(){return B(A2(_LY.a,_LO,_Lz));}),_o)));}}};return new T1(0,_LR);};return new F(function(){return A2(_LJ,_LM,_LP);});},_LZ=new T(function(){return eval("window.requestAnimationFrame");}),_M0=new T1(1,_o),_M1=function(_M2,_M3){var _M4=function(_M5){var _M6=function(_){var _M7=E(_M3),_M8=rMV(_M7),_M9=E(_M8);if(!_M9._){var _Ma=_M9.a,_Mb=E(_M9.b);if(!_Mb._){var _=wMV(_M7,_M0);return new T(function(){return B(A1(_M5,_Ma));});}else{var _Mc=E(_Mb.a),_=wMV(_M7,new T2(0,_Mc.a,_Mb.b));return new T1(1,new T2(1,new T(function(){return B(A1(_M5,_Ma));}),new T2(1,new T(function(){return B(A1(_Mc.b,_Lz));}),_o)));}}else{var _Md=new T(function(){var _Me=function(_Mf){var _Mg=new T(function(){return B(A1(_M5,_Mf));});return function(_Mh){return E(_Mg);};};return B(_f(_M9.a,new T2(1,_Me,_o)));}),_=wMV(_M7,new T1(1,_Md));return _LI;}};return new T1(0,_M6);};return new F(function(){return A2(_LJ,_M2,_M4);});},_Mi=function(_Mj,_Mk){var _Ml=new T(function(){return B(A(_LL,[_LG,_Mj,_jB,_Lz]));});return function(_){var _Mm=__createJSFunc(2,function(_Mn,_){var _Mo=B(_Ky(_Ml,_o,_));return _LH;}),_Mp=__app1(E(_LZ),_Mm);return new T(function(){return B(A3(_M1,_LG,_Mj,_Mk));});};},_Mq=new T1(1,_o),_Mr=function(_Ms,_Mt,_){var _Mu=function(_){var _Mv=nMV(_Ms),_Mw=_Mv;return new T(function(){var _Mx=new T(function(){return B(_My(_));}),_Mz=function(_){var _MA=rMV(_Mw),_MB=B(A2(_Mt,_MA,_)),_=wMV(_Mw,_MB),_MC=function(_){var _MD=nMV(_Mq);return new T(function(){return new T1(0,B(_Mi(_MD,function(_ME){return E(_Mx);})));});};return new T1(0,_MC);},_MF=new T(function(){return new T1(0,_Mz);}),_My=function(_MG){return E(_MF);};return B(_My(_));});};return new F(function(){return _Ky(new T1(0,_Mu),_o,_);});},_MH=function(_){var _MI=__app2(E(_0),E(_7W),E(_hg));return new F(function(){return _Mr(_zq,_Km,_);});},_MJ=function(_){return new F(function(){return _MH(_);});};
var hasteMain = function() {B(A(_MJ, [0]));};window.onload = hasteMain;