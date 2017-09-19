"use strict";
var __haste_prog_id = 'ad77ac448707fa3153371c3261d6e53380a9d8ba46dc38c97486a0f130605862';
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

var _0=new T(function(){return eval("compile");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==( -2147483648)){_3l=new T1(1,I_fromInt( -2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return  -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0, -1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHC\\Integer\\Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==( -2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return  -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S( -1021,53,_6k,_6l);});}else{return  -B(_5S( -1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=function(_7h){return E(E(_7h).a);},_7i=function(_7j){return E(E(_7j).a);},_7k=function(_7l){return E(E(_7l).c);},_7m=function(_7n){return E(E(_7n).b);},_7o=function(_7p){return E(E(_7p).d);},_7q=new T1(0,1),_7r=new T1(0,2),_7s=new T2(0,E(_7q),E(_7r)),_7t=new T1(0,5),_7u=new T1(0,4),_7v=new T2(0,E(_7u),E(_7t)),_7w=function(_7x){return E(E(_7x).e);},_7y=function(_7z,_7A,_7B,_7C){var _7D=B(_7g(_7z)),_7E=B(_7i(_7D)),_7F=new T(function(){var _7G=new T(function(){var _7H=new T(function(){var _7I=new T(function(){var _7J=new T(function(){var _7K=new T(function(){return B(A3(_6I,_7E,new T(function(){return B(A3(_7k,_7E,_7A,_7A));}),new T(function(){return B(A3(_7k,_7E,_7C,_7C));})));});return B(A2(_7w,_7z,_7K));});return B(A3(_7m,_7E,_7J,new T(function(){return B(A2(_7o,_7D,_7v));})));});return B(A3(_7k,_7E,_7I,_7I));});return B(A3(_6I,_7E,_7H,new T(function(){return B(A3(_7k,_7E,_7B,_7B));})));});return B(A2(_7w,_7z,_7G));});return new F(function(){return A3(_7m,_7E,_7F,new T(function(){return B(A2(_7o,_7D,_7s));}));});},_7L=new T(function(){return B(unCStr("z"));}),_7M=new T1(0,_7L),_7N=new T(function(){return B(unCStr("y"));}),_7O=new T1(0,_7N),_7P=new T(function(){return B(unCStr("x"));}),_7Q=new T1(0,_7P),_7R=new T(function(){return B(_7y(_7f,_7Q,_7O,_7M));}),_7S=function(_7T){return E(_7T);},_7U=new T(function(){return toJSStr(B(_5(_p,_7S,_7R)));}),_7V=function(_7W,_7X,_7Y){var _7Z=new T(function(){return B(_1(_7W));}),_80=new T(function(){return B(_3(_7W));}),_81=function(_82){var _83=E(_82);if(!_83._){return E(_80);}else{return new F(function(){return A2(_7Z,new T(function(){return B(_5(_7W,_7X,_83.a));}),new T(function(){return B(_81(_83.b));}));});}};return new F(function(){return _81(_7Y);});},_84=new T3(0,_7Q,_7O,_7M),_85=new T(function(){return B(unCStr("(/=) is not defined"));}),_86=new T(function(){return B(err(_85));}),_87=new T(function(){return B(unCStr("(==) is not defined"));}),_88=new T(function(){return B(err(_87));}),_89=new T2(0,_88,_86),_8a=new T(function(){return B(unCStr("(<) is not defined"));}),_8b=new T(function(){return B(err(_8a));}),_8c=new T(function(){return B(unCStr("(<=) is not defined"));}),_8d=new T(function(){return B(err(_8c));}),_8e=new T(function(){return B(unCStr("(>) is not defined"));}),_8f=new T(function(){return B(err(_8e));}),_8g=new T(function(){return B(unCStr("(>=) is not defined"));}),_8h=new T(function(){return B(err(_8g));}),_8i=new T(function(){return B(unCStr("compare is not defined"));}),_8j=new T(function(){return B(err(_8i));}),_8k=new T(function(){return B(unCStr("max("));}),_8l=new T1(0,_8k),_8m=function(_8n,_8o){return new T1(1,new T2(1,_8l,new T2(1,_8n,new T2(1,_r,new T2(1,_8o,_w)))));},_8p=new T(function(){return B(unCStr("min("));}),_8q=new T1(0,_8p),_8r=function(_8s,_8t){return new T1(1,new T2(1,_8q,new T2(1,_8s,new T2(1,_r,new T2(1,_8t,_w)))));},_8u={_:0,a:_89,b:_8j,c:_8b,d:_8d,e:_8f,f:_8h,g:_8m,h:_8r},_8v=new T2(0,_7f,_8u),_8w=function(_8x,_8y){var _8z=E(_8x);return E(_8y);},_8A=function(_8B,_8C){var _8D=E(_8B),_8E=E(_8C);return new T3(0,new T(function(){return B(A1(_8D.a,_8E.a));}),new T(function(){return B(A1(_8D.b,_8E.b));}),new T(function(){return B(A1(_8D.c,_8E.c));}));},_8F=function(_8G){return new T3(0,_8G,_8G,_8G);},_8H=function(_8I,_8J){var _8K=E(_8J);return new T3(0,_8I,_8I,_8I);},_8L=function(_8M,_8N){var _8O=E(_8N);return new T3(0,new T(function(){return B(A1(_8M,_8O.a));}),new T(function(){return B(A1(_8M,_8O.b));}),new T(function(){return B(A1(_8M,_8O.c));}));},_8P=new T2(0,_8L,_8H),_8Q=function(_8R,_8S){var _8T=E(_8R),_8U=E(_8S);return new T3(0,_8T.a,_8T.b,_8T.c);},_8V=new T5(0,_8P,_8F,_8A,_8w,_8Q),_8W=new T1(0,0),_8X=function(_8Y){return E(E(_8Y).g);},_8Z=function(_90){return new T3(0,new T3(0,new T(function(){return B(A2(_8X,_90,_7q));}),new T(function(){return B(A2(_8X,_90,_8W));}),new T(function(){return B(A2(_8X,_90,_8W));})),new T3(0,new T(function(){return B(A2(_8X,_90,_8W));}),new T(function(){return B(A2(_8X,_90,_7q));}),new T(function(){return B(A2(_8X,_90,_8W));})),new T3(0,new T(function(){return B(A2(_8X,_90,_8W));}),new T(function(){return B(A2(_8X,_90,_8W));}),new T(function(){return B(A2(_8X,_90,_7q));})));},_91=function(_92){var _93=B(_8Z(_92));return new T3(0,_93.a,_93.b,_93.c);},_94=function(_95){return E(E(_95).a);},_96=function(_97){return E(E(_97).f);},_98=function(_99){return E(E(_99).b);},_9a=function(_9b){return E(E(_9b).c);},_9c=function(_9d){return E(E(_9d).a);},_9e=function(_9f){return E(E(_9f).d);},_9g=function(_9h,_9i,_9j,_9k,_9l){var _9m=new T(function(){return E(E(E(_9h).c).a);}),_9n=new T(function(){var _9o=E(_9h).a,_9p=new T(function(){var _9q=new T(function(){return B(_7g(_9m));}),_9r=new T(function(){return B(_7i(_9q));}),_9s=new T(function(){return B(A2(_9e,_9m,_9i));}),_9t=new T(function(){return B(A3(_96,_9m,_9i,_9k));}),_9u=function(_9v,_9w){var _9x=new T(function(){var _9y=new T(function(){return B(A3(_98,_9q,new T(function(){return B(A3(_7k,_9r,_9k,_9v));}),_9i));});return B(A3(_6I,_9r,_9y,new T(function(){return B(A3(_7k,_9r,_9w,_9s));})));});return new F(function(){return A3(_7k,_9r,_9t,_9x);});};return B(A3(_9c,B(_94(_9o)),_9u,_9j));});return B(A3(_9a,_9o,_9p,_9l));});return new T2(0,new T(function(){return B(A3(_96,_9m,_9i,_9k));}),_9n);},_9z=function(_9A,_9B,_9C,_9D){var _9E=E(_9C),_9F=E(_9D),_9G=B(_9g(_9B,_9E.a,_9E.b,_9F.a,_9F.b));return new T2(0,_9G.a,_9G.b);},_9H=new T1(0,1),_9I=function(_9J){return E(E(_9J).l);},_9K=function(_9L,_9M,_9N){var _9O=new T(function(){return E(E(E(_9L).c).a);}),_9P=new T(function(){var _9Q=new T(function(){return B(_7g(_9O));}),_9R=new T(function(){var _9S=B(_7i(_9Q)),_9T=new T(function(){var _9U=new T(function(){return B(A3(_7m,_9S,new T(function(){return B(A2(_8X,_9S,_9H));}),new T(function(){return B(A3(_7k,_9S,_9M,_9M));})));});return B(A2(_7w,_9O,_9U));});return B(A2(_6K,_9S,_9T));});return B(A3(_9c,B(_94(E(_9L).a)),function(_9V){return new F(function(){return A3(_98,_9Q,_9V,_9R);});},_9N));});return new T2(0,new T(function(){return B(A2(_9I,_9O,_9M));}),_9P);},_9W=function(_9X,_9Y,_9Z){var _a0=E(_9Z),_a1=B(_9K(_9Y,_a0.a,_a0.b));return new T2(0,_a1.a,_a1.b);},_a2=function(_a3){return E(E(_a3).r);},_a4=function(_a5,_a6,_a7){var _a8=new T(function(){return E(E(E(_a5).c).a);}),_a9=new T(function(){var _aa=new T(function(){return B(_7g(_a8));}),_ab=new T(function(){var _ac=new T(function(){var _ad=B(_7i(_aa));return B(A3(_7m,_ad,new T(function(){return B(A3(_7k,_ad,_a6,_a6));}),new T(function(){return B(A2(_8X,_ad,_9H));})));});return B(A2(_7w,_a8,_ac));});return B(A3(_9c,B(_94(E(_a5).a)),function(_ae){return new F(function(){return A3(_98,_aa,_ae,_ab);});},_a7));});return new T2(0,new T(function(){return B(A2(_a2,_a8,_a6));}),_a9);},_af=function(_ag,_ah,_ai){var _aj=E(_ai),_ak=B(_a4(_ah,_aj.a,_aj.b));return new T2(0,_ak.a,_ak.b);},_al=function(_am){return E(E(_am).k);},_an=function(_ao,_ap,_aq){var _ar=new T(function(){return E(E(E(_ao).c).a);}),_as=new T(function(){var _at=new T(function(){return B(_7g(_ar));}),_au=new T(function(){var _av=new T(function(){var _aw=B(_7i(_at));return B(A3(_7m,_aw,new T(function(){return B(A2(_8X,_aw,_9H));}),new T(function(){return B(A3(_7k,_aw,_ap,_ap));})));});return B(A2(_7w,_ar,_av));});return B(A3(_9c,B(_94(E(_ao).a)),function(_ax){return new F(function(){return A3(_98,_at,_ax,_au);});},_aq));});return new T2(0,new T(function(){return B(A2(_al,_ar,_ap));}),_as);},_ay=function(_az,_aA,_aB){var _aC=E(_aB),_aD=B(_an(_aA,_aC.a,_aC.b));return new T2(0,_aD.a,_aD.b);},_aE=function(_aF){return E(E(_aF).q);},_aG=function(_aH,_aI,_aJ){var _aK=new T(function(){return E(E(E(_aH).c).a);}),_aL=new T(function(){var _aM=new T(function(){return B(_7g(_aK));}),_aN=new T(function(){var _aO=new T(function(){var _aP=B(_7i(_aM));return B(A3(_6I,_aP,new T(function(){return B(A3(_7k,_aP,_aI,_aI));}),new T(function(){return B(A2(_8X,_aP,_9H));})));});return B(A2(_7w,_aK,_aO));});return B(A3(_9c,B(_94(E(_aH).a)),function(_aQ){return new F(function(){return A3(_98,_aM,_aQ,_aN);});},_aJ));});return new T2(0,new T(function(){return B(A2(_aE,_aK,_aI));}),_aL);},_aR=function(_aS,_aT,_aU){var _aV=E(_aU),_aW=B(_aG(_aT,_aV.a,_aV.b));return new T2(0,_aW.a,_aW.b);},_aX=function(_aY){return E(E(_aY).m);},_aZ=function(_b0,_b1,_b2){var _b3=new T(function(){return E(E(E(_b0).c).a);}),_b4=new T(function(){var _b5=new T(function(){return B(_7g(_b3));}),_b6=new T(function(){var _b7=B(_7i(_b5));return B(A3(_6I,_b7,new T(function(){return B(A2(_8X,_b7,_9H));}),new T(function(){return B(A3(_7k,_b7,_b1,_b1));})));});return B(A3(_9c,B(_94(E(_b0).a)),function(_b8){return new F(function(){return A3(_98,_b5,_b8,_b6);});},_b2));});return new T2(0,new T(function(){return B(A2(_aX,_b3,_b1));}),_b4);},_b9=function(_ba,_bb,_bc){var _bd=E(_bc),_be=B(_aZ(_bb,_bd.a,_bd.b));return new T2(0,_be.a,_be.b);},_bf=function(_bg){return E(E(_bg).s);},_bh=function(_bi,_bj,_bk){var _bl=new T(function(){return E(E(E(_bi).c).a);}),_bm=new T(function(){var _bn=new T(function(){return B(_7g(_bl));}),_bo=new T(function(){var _bp=B(_7i(_bn));return B(A3(_7m,_bp,new T(function(){return B(A2(_8X,_bp,_9H));}),new T(function(){return B(A3(_7k,_bp,_bj,_bj));})));});return B(A3(_9c,B(_94(E(_bi).a)),function(_bq){return new F(function(){return A3(_98,_bn,_bq,_bo);});},_bk));});return new T2(0,new T(function(){return B(A2(_bf,_bl,_bj));}),_bm);},_br=function(_bs,_bt,_bu){var _bv=E(_bu),_bw=B(_bh(_bt,_bv.a,_bv.b));return new T2(0,_bw.a,_bw.b);},_bx=function(_by){return E(E(_by).i);},_bz=function(_bA){return E(E(_bA).h);},_bB=function(_bC,_bD,_bE){var _bF=new T(function(){return E(E(E(_bC).c).a);}),_bG=new T(function(){var _bH=new T(function(){return B(_7i(new T(function(){return B(_7g(_bF));})));}),_bI=new T(function(){return B(A2(_6K,_bH,new T(function(){return B(A2(_bz,_bF,_bD));})));});return B(A3(_9c,B(_94(E(_bC).a)),function(_bJ){return new F(function(){return A3(_7k,_bH,_bJ,_bI);});},_bE));});return new T2(0,new T(function(){return B(A2(_bx,_bF,_bD));}),_bG);},_bK=function(_bL,_bM,_bN){var _bO=E(_bN),_bP=B(_bB(_bM,_bO.a,_bO.b));return new T2(0,_bP.a,_bP.b);},_bQ=function(_bR){return E(E(_bR).o);},_bS=function(_bT){return E(E(_bT).n);},_bU=function(_bV,_bW,_bX){var _bY=new T(function(){return E(E(E(_bV).c).a);}),_bZ=new T(function(){var _c0=new T(function(){return B(_7i(new T(function(){return B(_7g(_bY));})));}),_c1=new T(function(){return B(A2(_bS,_bY,_bW));});return B(A3(_9c,B(_94(E(_bV).a)),function(_c2){return new F(function(){return A3(_7k,_c0,_c2,_c1);});},_bX));});return new T2(0,new T(function(){return B(A2(_bQ,_bY,_bW));}),_bZ);},_c3=function(_c4,_c5,_c6){var _c7=E(_c6),_c8=B(_bU(_c5,_c7.a,_c7.b));return new T2(0,_c8.a,_c8.b);},_c9=function(_ca){return E(E(_ca).c);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_7i(new T(function(){return B(_7g(_cf));})));}),_ci=new T(function(){return B(A2(_c9,_cf,_cd));});return B(A3(_9c,B(_94(E(_cc).a)),function(_cj){return new F(function(){return A3(_7k,_ch,_cj,_ci);});},_ce));});return new T2(0,new T(function(){return B(A2(_c9,_cf,_cd));}),_cg);},_ck=function(_cl,_cm,_cn){var _co=E(_cn),_cp=B(_cb(_cm,_co.a,_co.b));return new T2(0,_cp.a,_cp.b);},_cq=function(_cr,_cs,_ct){var _cu=new T(function(){return E(E(E(_cr).c).a);}),_cv=new T(function(){var _cw=new T(function(){return B(_7g(_cu));}),_cx=new T(function(){return B(_7i(_cw));}),_cy=new T(function(){return B(A3(_98,_cw,new T(function(){return B(A2(_8X,_cx,_9H));}),_cs));});return B(A3(_9c,B(_94(E(_cr).a)),function(_cz){return new F(function(){return A3(_7k,_cx,_cz,_cy);});},_ct));});return new T2(0,new T(function(){return B(A2(_9e,_cu,_cs));}),_cv);},_cA=function(_cB,_cC,_cD){var _cE=E(_cD),_cF=B(_cq(_cC,_cE.a,_cE.b));return new T2(0,_cF.a,_cF.b);},_cG=function(_cH,_cI,_cJ,_cK){var _cL=new T(function(){return E(E(_cI).c);}),_cM=new T3(0,new T(function(){return E(E(_cI).a);}),new T(function(){return E(E(_cI).b);}),new T2(0,new T(function(){return E(E(_cL).a);}),new T(function(){return E(E(_cL).b);})));return new F(function(){return A3(_98,_cH,new T(function(){var _cN=E(_cK),_cO=B(_cq(_cM,_cN.a,_cN.b));return new T2(0,_cO.a,_cO.b);}),new T(function(){var _cP=E(_cJ),_cQ=B(_cq(_cM,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);}));});},_cR=new T1(0,0),_cS=function(_cT){return E(E(_cT).b);},_cU=function(_cV){return E(E(_cV).b);},_cW=function(_cX){var _cY=new T(function(){return E(E(E(_cX).c).a);}),_cZ=new T(function(){return B(A2(_cU,E(_cX).a,new T(function(){return B(A2(_8X,B(_7i(B(_7g(_cY)))),_cR));})));});return new T2(0,new T(function(){return B(_cS(_cY));}),_cZ);},_d0=function(_d1,_d2){var _d3=B(_cW(_d2));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_7i(new T(function(){return B(_7g(_d8));})));}),_db=new T(function(){return B(A2(_bx,_d8,_d6));});return B(A3(_9c,B(_94(E(_d5).a)),function(_dc){return new F(function(){return A3(_7k,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bz,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=function(_dk,_dl,_dm){var _dn=new T(function(){return E(E(E(_dk).c).a);}),_do=new T(function(){var _dp=new T(function(){return B(_7i(new T(function(){return B(_7g(_dn));})));}),_dq=new T(function(){return B(A2(_bQ,_dn,_dl));});return B(A3(_9c,B(_94(E(_dk).a)),function(_dr){return new F(function(){return A3(_7k,_dp,_dr,_dq);});},_dm));});return new T2(0,new T(function(){return B(A2(_bS,_dn,_dl));}),_do);},_ds=function(_dt,_du,_dv){var _dw=E(_dv),_dx=B(_dj(_du,_dw.a,_dw.b));return new T2(0,_dx.a,_dx.b);},_dy=new T1(0,2),_dz=function(_dA,_dB,_dC){var _dD=new T(function(){return E(E(E(_dA).c).a);}),_dE=new T(function(){var _dF=new T(function(){return B(_7g(_dD));}),_dG=new T(function(){return B(_7i(_dF));}),_dH=new T(function(){var _dI=new T(function(){return B(A3(_98,_dF,new T(function(){return B(A2(_8X,_dG,_9H));}),new T(function(){return B(A2(_8X,_dG,_dy));})));});return B(A3(_98,_dF,_dI,new T(function(){return B(A2(_7w,_dD,_dB));})));});return B(A3(_9c,B(_94(E(_dA).a)),function(_dJ){return new F(function(){return A3(_7k,_dG,_dJ,_dH);});},_dC));});return new T2(0,new T(function(){return B(A2(_7w,_dD,_dB));}),_dE);},_dK=function(_dL,_dM,_dN){var _dO=E(_dN),_dP=B(_dz(_dM,_dO.a,_dO.b));return new T2(0,_dP.a,_dP.b);},_dQ=function(_dR){return E(E(_dR).j);},_dS=function(_dT,_dU,_dV){var _dW=new T(function(){return E(E(E(_dT).c).a);}),_dX=new T(function(){var _dY=new T(function(){return B(_7g(_dW));}),_dZ=new T(function(){var _e0=new T(function(){return B(A2(_bx,_dW,_dU));});return B(A3(_7k,B(_7i(_dY)),_e0,_e0));});return B(A3(_9c,B(_94(E(_dT).a)),function(_e1){return new F(function(){return A3(_98,_dY,_e1,_dZ);});},_dV));});return new T2(0,new T(function(){return B(A2(_dQ,_dW,_dU));}),_dX);},_e2=function(_e3,_e4,_e5){var _e6=E(_e5),_e7=B(_dS(_e4,_e6.a,_e6.b));return new T2(0,_e7.a,_e7.b);},_e8=function(_e9){return E(E(_e9).p);},_ea=function(_eb,_ec,_ed){var _ee=new T(function(){return E(E(E(_eb).c).a);}),_ef=new T(function(){var _eg=new T(function(){return B(_7g(_ee));}),_eh=new T(function(){var _ei=new T(function(){return B(A2(_bQ,_ee,_ec));});return B(A3(_7k,B(_7i(_eg)),_ei,_ei));});return B(A3(_9c,B(_94(E(_eb).a)),function(_ej){return new F(function(){return A3(_98,_eg,_ej,_eh);});},_ed));});return new T2(0,new T(function(){return B(A2(_e8,_ee,_ec));}),_ef);},_ek=function(_el,_em,_en){var _eo=E(_en),_ep=B(_ea(_em,_eo.a,_eo.b));return new T2(0,_ep.a,_ep.b);},_eq=function(_er,_es){return {_:0,a:_er,b:new T(function(){return B(_d0(_er,_es));}),c:function(_et){return new F(function(){return _ck(_er,_es,_et);});},d:function(_et){return new F(function(){return _cA(_er,_es,_et);});},e:function(_et){return new F(function(){return _dK(_er,_es,_et);});},f:function(_eu,_et){return new F(function(){return _9z(_er,_es,_eu,_et);});},g:function(_eu,_et){return new F(function(){return _cG(_er,_es,_eu,_et);});},h:function(_et){return new F(function(){return _dd(_er,_es,_et);});},i:function(_et){return new F(function(){return _bK(_er,_es,_et);});},j:function(_et){return new F(function(){return _e2(_er,_es,_et);});},k:function(_et){return new F(function(){return _ay(_er,_es,_et);});},l:function(_et){return new F(function(){return _9W(_er,_es,_et);});},m:function(_et){return new F(function(){return _b9(_er,_es,_et);});},n:function(_et){return new F(function(){return _ds(_er,_es,_et);});},o:function(_et){return new F(function(){return _c3(_er,_es,_et);});},p:function(_et){return new F(function(){return _ek(_er,_es,_et);});},q:function(_et){return new F(function(){return _aR(_er,_es,_et);});},r:function(_et){return new F(function(){return _af(_er,_es,_et);});},s:function(_et){return new F(function(){return _br(_er,_es,_et);});}};},_ev=function(_ew,_ex,_ey,_ez,_eA){var _eB=new T(function(){return B(_7g(new T(function(){return E(E(E(_ew).c).a);})));}),_eC=new T(function(){var _eD=E(_ew).a,_eE=new T(function(){var _eF=new T(function(){return B(_7i(_eB));}),_eG=new T(function(){return B(A3(_7k,_eF,_ez,_ez));}),_eH=function(_eI,_eJ){var _eK=new T(function(){return B(A3(_7m,_eF,new T(function(){return B(A3(_7k,_eF,_eI,_ez));}),new T(function(){return B(A3(_7k,_eF,_ex,_eJ));})));});return new F(function(){return A3(_98,_eB,_eK,_eG);});};return B(A3(_9c,B(_94(_eD)),_eH,_ey));});return B(A3(_9a,_eD,_eE,_eA));});return new T2(0,new T(function(){return B(A3(_98,_eB,_ex,_ez));}),_eC);},_eL=function(_eM,_eN,_eO,_eP){var _eQ=E(_eO),_eR=E(_eP),_eS=B(_ev(_eN,_eQ.a,_eQ.b,_eR.a,_eR.b));return new T2(0,_eS.a,_eS.b);},_eT=function(_eU,_eV){var _eW=new T(function(){return B(_7g(new T(function(){return E(E(E(_eU).c).a);})));}),_eX=new T(function(){return B(A2(_cU,E(_eU).a,new T(function(){return B(A2(_8X,B(_7i(_eW)),_cR));})));});return new T2(0,new T(function(){return B(A2(_7o,_eW,_eV));}),_eX);},_eY=function(_eZ,_f0,_f1){var _f2=B(_eT(_f0,_f1));return new T2(0,_f2.a,_f2.b);},_f3=function(_f4,_f5,_f6){var _f7=new T(function(){return B(_7g(new T(function(){return E(E(E(_f4).c).a);})));}),_f8=new T(function(){return B(_7i(_f7));}),_f9=new T(function(){var _fa=new T(function(){var _fb=new T(function(){return B(A3(_98,_f7,new T(function(){return B(A2(_8X,_f8,_9H));}),new T(function(){return B(A3(_7k,_f8,_f5,_f5));})));});return B(A2(_6K,_f8,_fb));});return B(A3(_9c,B(_94(E(_f4).a)),function(_fc){return new F(function(){return A3(_7k,_f8,_fc,_fa);});},_f6));}),_fd=new T(function(){return B(A3(_98,_f7,new T(function(){return B(A2(_8X,_f8,_9H));}),_f5));});return new T2(0,_fd,_f9);},_fe=function(_ff,_fg,_fh){var _fi=E(_fh),_fj=B(_f3(_fg,_fi.a,_fi.b));return new T2(0,_fj.a,_fj.b);},_fk=function(_fl,_fm){return new T4(0,_fl,function(_eu,_et){return new F(function(){return _eL(_fl,_fm,_eu,_et);});},function(_et){return new F(function(){return _fe(_fl,_fm,_et);});},function(_et){return new F(function(){return _eY(_fl,_fm,_et);});});},_fn=function(_fo,_fp,_fq,_fr,_fs){var _ft=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fo).c).a);})));})));}),_fu=new T(function(){var _fv=E(_fo).a,_fw=new T(function(){var _fx=function(_fy,_fz){return new F(function(){return A3(_6I,_ft,new T(function(){return B(A3(_7k,_ft,_fp,_fz));}),new T(function(){return B(A3(_7k,_ft,_fy,_fr));}));});};return B(A3(_9c,B(_94(_fv)),_fx,_fq));});return B(A3(_9a,_fv,_fw,_fs));});return new T2(0,new T(function(){return B(A3(_7k,_ft,_fp,_fr));}),_fu);},_fA=function(_fB,_fC,_fD){var _fE=E(_fC),_fF=E(_fD),_fG=B(_fn(_fB,_fE.a,_fE.b,_fF.a,_fF.b));return new T2(0,_fG.a,_fG.b);},_fH=function(_fI,_fJ,_fK,_fL,_fM){var _fN=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fI).c).a);})));})));}),_fO=new T(function(){var _fP=E(_fI).a,_fQ=new T(function(){return B(A3(_9c,B(_94(_fP)),new T(function(){return B(_6I(_fN));}),_fK));});return B(A3(_9a,_fP,_fQ,_fM));});return new T2(0,new T(function(){return B(A3(_6I,_fN,_fJ,_fL));}),_fO);},_fR=function(_fS,_fT,_fU){var _fV=E(_fT),_fW=E(_fU),_fX=B(_fH(_fS,_fV.a,_fV.b,_fW.a,_fW.b));return new T2(0,_fX.a,_fX.b);},_fY=function(_fZ,_g0,_g1){var _g2=B(_g3(_fZ));return new F(function(){return A3(_6I,_g2,_g0,new T(function(){return B(A2(_6K,_g2,_g1));}));});},_g4=function(_g5){return E(E(_g5).e);},_g6=function(_g7){return E(E(_g7).f);},_g8=function(_g9,_ga,_gb){var _gc=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gd=new T(function(){var _ge=new T(function(){return B(A2(_g6,_gc,_ga));});return B(A3(_9c,B(_94(E(_g9).a)),function(_gf){return new F(function(){return A3(_7k,_gc,_gf,_ge);});},_gb));});return new T2(0,new T(function(){return B(A2(_g4,_gc,_ga));}),_gd);},_gg=function(_gh,_gi){var _gj=E(_gi),_gk=B(_g8(_gh,_gj.a,_gj.b));return new T2(0,_gk.a,_gk.b);},_gl=function(_gm,_gn){var _go=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gm).c).a);})));})));}),_gp=new T(function(){return B(A2(_cU,E(_gm).a,new T(function(){return B(A2(_8X,_go,_cR));})));});return new T2(0,new T(function(){return B(A2(_8X,_go,_gn));}),_gp);},_gq=function(_gr,_gs){var _gt=B(_gl(_gr,_gs));return new T2(0,_gt.a,_gt.b);},_gu=function(_gv,_gw,_gx){var _gy=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gv).c).a);})));})));}),_gz=new T(function(){return B(A3(_9c,B(_94(E(_gv).a)),new T(function(){return B(_6K(_gy));}),_gx));});return new T2(0,new T(function(){return B(A2(_6K,_gy,_gw));}),_gz);},_gA=function(_gB,_gC){var _gD=E(_gC),_gE=B(_gu(_gB,_gD.a,_gD.b));return new T2(0,_gE.a,_gE.b);},_gF=function(_gG,_gH){var _gI=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gG).c).a);})));})));}),_gJ=new T(function(){return B(A2(_cU,E(_gG).a,new T(function(){return B(A2(_8X,_gI,_cR));})));});return new T2(0,new T(function(){return B(A2(_g6,_gI,_gH));}),_gJ);},_gK=function(_gL,_gM){var _gN=B(_gF(_gL,E(_gM).a));return new T2(0,_gN.a,_gN.b);},_g3=function(_gO){return {_:0,a:function(_eu,_et){return new F(function(){return _fR(_gO,_eu,_et);});},b:function(_eu,_et){return new F(function(){return _fY(_gO,_eu,_et);});},c:function(_eu,_et){return new F(function(){return _fA(_gO,_eu,_et);});},d:function(_et){return new F(function(){return _gA(_gO,_et);});},e:function(_et){return new F(function(){return _gg(_gO,_et);});},f:function(_et){return new F(function(){return _gK(_gO,_et);});},g:function(_et){return new F(function(){return _gq(_gO,_et);});}};},_gP=function(_gQ){var _gR=new T(function(){return E(E(_gQ).a);}),_gS=new T3(0,_8V,_91,new T2(0,_gR,new T(function(){return E(E(_gQ).b);}))),_gT=new T(function(){return B(_eq(new T(function(){return B(_fk(new T(function(){return B(_g3(_gS));}),_gS));}),_gS));}),_gU=new T(function(){return B(_7i(new T(function(){return B(_7g(_gR));})));});return function(_gV){var _gW=E(_gV),_gX=B(_8Z(_gU));return E(B(_7y(_gT,new T2(0,_gW.a,_gX.a),new T2(0,_gW.b,_gX.b),new T2(0,_gW.c,_gX.c))).b);};},_gY=new T(function(){return B(_gP(_8v));}),_gZ=function(_h0,_h1){var _h2=E(_h1);return (_h2._==0)?__Z:new T2(1,_h0,new T2(1,_h2.a,new T(function(){return B(_gZ(_h0,_h2.b));})));},_h3=new T(function(){var _h4=B(A1(_gY,_84));return new T2(1,_h4.a,new T(function(){return B(_gZ(_r,new T2(1,_h4.b,new T2(1,_h4.c,_o))));}));}),_h5=new T1(1,_h3),_h6=new T2(1,_h5,_w),_h7=new T(function(){return B(unCStr("vec3("));}),_h8=new T1(0,_h7),_h9=new T2(1,_h8,_h6),_ha=new T(function(){return toJSStr(B(_7V(_p,_7S,_h9)));}),_hb=function(_hc,_hd){while(1){var _he=E(_hc);if(!_he._){return E(_hd);}else{var _hf=_hd+1|0;_hc=_he.b;_hd=_hf;continue;}}},_hg=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hh=new T(function(){return B(err(_hg));}),_hi=new T(function(){return B(unCStr("Negative exponent"));}),_hj=new T(function(){return B(err(_hi));}),_hk=function(_hl,_hm,_hn){while(1){if(!(_hm%2)){var _ho=_hl*_hl,_hp=quot(_hm,2);_hl=_ho;_hm=_hp;continue;}else{var _hq=E(_hm);if(_hq==1){return _hl*_hn;}else{var _ho=_hl*_hl,_hr=_hl*_hn;_hl=_ho;_hm=quot(_hq-1|0,2);_hn=_hr;continue;}}}},_hs=function(_ht,_hu){while(1){if(!(_hu%2)){var _hv=_ht*_ht,_hw=quot(_hu,2);_ht=_hv;_hu=_hw;continue;}else{var _hx=E(_hu);if(_hx==1){return E(_ht);}else{return new F(function(){return _hk(_ht*_ht,quot(_hx-1|0,2),_ht);});}}}},_hy=function(_hz){var _hA=E(_hz);return new F(function(){return Math.log(_hA+(_hA+1)*Math.sqrt((_hA-1)/(_hA+1)));});},_hB=function(_hC){var _hD=E(_hC);return new F(function(){return Math.log(_hD+Math.sqrt(1+_hD*_hD));});},_hE=function(_hF){var _hG=E(_hF);return 0.5*Math.log((1+_hG)/(1-_hG));},_hH=function(_hI,_hJ){return Math.log(E(_hJ))/Math.log(E(_hI));},_hK=3.141592653589793,_hL=function(_hM){var _hN=E(_hM);return new F(function(){return _6j(_hN.a,_hN.b);});},_hO=function(_hP){return 1/E(_hP);},_hQ=function(_hR){var _hS=E(_hR),_hT=E(_hS);return (_hT==0)?E(_6i):(_hT<=0)? -_hT:E(_hS);},_hU=function(_hV){var _hW=E(_hV);if(!_hW._){return _hW.a;}else{return new F(function(){return I_toNumber(_hW.a);});}},_hX=function(_hY){return new F(function(){return _hU(_hY);});},_hZ=1,_i0= -1,_i1=function(_i2){var _i3=E(_i2);return (_i3<=0)?(_i3>=0)?E(_i3):E(_i0):E(_hZ);},_i4=function(_i5,_i6){return E(_i5)-E(_i6);},_i7=function(_i8){return  -E(_i8);},_i9=function(_ia,_ib){return E(_ia)+E(_ib);},_ic=function(_id,_ie){return E(_id)*E(_ie);},_if={_:0,a:_i9,b:_i4,c:_ic,d:_i7,e:_hQ,f:_i1,g:_hX},_ig=function(_ih,_ii){return E(_ih)/E(_ii);},_ij=new T4(0,_if,_ig,_hO,_hL),_ik=function(_il){return new F(function(){return Math.acos(E(_il));});},_im=function(_in){return new F(function(){return Math.asin(E(_in));});},_io=function(_ip){return new F(function(){return Math.atan(E(_ip));});},_iq=function(_ir){return new F(function(){return Math.cos(E(_ir));});},_is=function(_it){return new F(function(){return cosh(E(_it));});},_iu=function(_iv){return new F(function(){return Math.exp(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.log(E(_ix));});},_iy=function(_iz,_iA){return new F(function(){return Math.pow(E(_iz),E(_iA));});},_iB=function(_iC){return new F(function(){return Math.sin(E(_iC));});},_iD=function(_iE){return new F(function(){return sinh(E(_iE));});},_iF=function(_iG){return new F(function(){return Math.sqrt(E(_iG));});},_iH=function(_iI){return new F(function(){return Math.tan(E(_iI));});},_iJ=function(_iK){return new F(function(){return tanh(E(_iK));});},_iL={_:0,a:_ij,b:_hK,c:_iu,d:_iw,e:_iF,f:_iy,g:_hH,h:_iB,i:_iq,j:_iH,k:_im,l:_ik,m:_io,n:_iD,o:_is,p:_iJ,q:_hB,r:_hy,s:_hE},_iM=function(_iN,_iO){return (E(_iN)!=E(_iO))?true:false;},_iP=function(_iQ,_iR){return E(_iQ)==E(_iR);},_iS=new T2(0,_iP,_iM),_iT=function(_iU,_iV){return E(_iU)<E(_iV);},_iW=function(_iX,_iY){return E(_iX)<=E(_iY);},_iZ=function(_j0,_j1){return E(_j0)>E(_j1);},_j2=function(_j3,_j4){return E(_j3)>=E(_j4);},_j5=function(_j6,_j7){var _j8=E(_j6),_j9=E(_j7);return (_j8>=_j9)?(_j8!=_j9)?2:1:0;},_ja=function(_jb,_jc){var _jd=E(_jb),_je=E(_jc);return (_jd>_je)?E(_jd):E(_je);},_jf=function(_jg,_jh){var _ji=E(_jg),_jj=E(_jh);return (_ji>_jj)?E(_jj):E(_ji);},_jk={_:0,a:_iS,b:_j5,c:_iT,d:_iW,e:_iZ,f:_j2,g:_ja,h:_jf},_jl=new T2(0,_iL,_jk),_jm=function(_jn,_jo,_jp,_jq,_jr,_js,_jt){var _ju=B(_7i(B(_7g(_jn)))),_jv=new T(function(){return B(A3(_6I,_ju,new T(function(){return B(A3(_7k,_ju,_jo,_jr));}),new T(function(){return B(A3(_7k,_ju,_jp,_js));})));});return new F(function(){return A3(_6I,_ju,_jv,new T(function(){return B(A3(_7k,_ju,_jq,_jt));}));});},_jw=function(_jx,_jy,_jz,_jA){var _jB=new T(function(){return E(E(_jx).a);}),_jC=new T(function(){return B(_7g(_jB));}),_jD=new T(function(){return B(A2(_7w,_jB,new T(function(){return B(_jm(_jB,_jy,_jz,_jA,_jy,_jz,_jA));})));});return new T3(0,new T(function(){return B(A3(_98,_jC,_jy,_jD));}),new T(function(){return B(A3(_98,_jC,_jz,_jD));}),new T(function(){return B(A3(_98,_jC,_jA,_jD));}));},_jE=function(_jF,_jG){var _jH=new T(function(){return E(E(_jF).a);}),_jI=new T(function(){return E(E(_jF).b);}),_jJ=new T(function(){return B(A2(_gP,new T2(0,_jH,_jI),_jG));}),_jK=new T(function(){var _jL=E(_jJ),_jM=B(_jw(new T2(0,_jH,_jI),_jL.a,_jL.b,_jL.c));return new T3(0,_jM.a,_jM.b,_jM.c);}),_jN=new T(function(){var _jO=E(_jG),_jP=_jO.a,_jQ=_jO.b,_jR=_jO.c,_jS=E(_jK),_jT=new T(function(){return B(_7g(_jH));}),_jU=new T(function(){return B(_7i(_jT));}),_jV=new T(function(){return B(_6I(_jU));}),_jW=new T(function(){return B(_6K(_jU));}),_jX=new T(function(){return B(_7k(_jU));}),_jY=new T(function(){var _jZ=new T(function(){return B(A2(_7w,_jH,new T(function(){var _k0=E(_jJ),_k1=_k0.a,_k2=_k0.b,_k3=_k0.c;return B(_jm(_jH,_k1,_k2,_k3,_k1,_k2,_k3));})));});return B(A3(_98,_jT,new T(function(){return B(_7y(_jH,_jP,_jQ,_jR));}),_jZ));}),_k4=new T(function(){var _k5=new T(function(){return B(A1(_jW,new T(function(){return B(A2(_jX,_jS.c,_jY));})));});return B(A2(_jV,_jR,_k5));}),_k6=new T(function(){var _k7=new T(function(){return B(A1(_jW,new T(function(){return B(A2(_jX,_jS.b,_jY));})));});return B(A2(_jV,_jQ,_k7));}),_k8=new T(function(){var _k9=new T(function(){return B(A1(_jW,new T(function(){return B(A2(_jX,_jS.a,_jY));})));});return B(A2(_jV,_jP,_k9));});return new T3(0,_k8,_k6,_k4);});return new T2(0,_jN,_jK);},_ka=function(_kb,_kc,_kd,_ke,_kf,_kg,_kh){var _ki=new T(function(){return E(E(_kb).a);}),_kj=new T(function(){return B(_7i(new T(function(){return B(_7g(_ki));})));}),_kk=new T(function(){return B(_6I(_kj));}),_kl=new T(function(){return B(_6K(_kj));}),_km=new T(function(){return B(_7k(_kj));}),_kn=new T(function(){return B(_jm(_ki,_kf,_kg,_kh,_kc,_kd,_ke));}),_ko=new T(function(){var _kp=new T(function(){return B(A1(_kl,new T(function(){return B(A2(_km,_kh,_kn));})));});return B(A2(_kk,_ke,_kp));}),_kq=new T(function(){var _kr=new T(function(){return B(A1(_kl,new T(function(){return B(A2(_km,_kg,_kn));})));});return B(A2(_kk,_kd,_kr));}),_ks=new T(function(){var _kt=new T(function(){return B(A1(_kl,new T(function(){return B(A2(_km,_kf,_kn));})));});return B(A2(_kk,_kc,_kt));});return new T3(0,_ks,_kq,_ko);},_ku=function(_kv){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_kv));}))));});},_kw=new T(function(){return B(_ku("$dOrd_s9EN Ord a"));}),_kx=function(_ky,_kz,_kA,_kB,_kC,_kD,_kE){var _kF=new T(function(){return E(E(_ky).a);}),_kG=B(_ka(new T2(0,_kF,_kw),_kC,_kD,_kE,_kz,_kA,_kB));return new F(function(){return _jw(new T2(0,_kF,_kw),_kG.a,_kG.b,_kG.c);});},_kH=function(_kI){return E(E(_kI).a);},_kJ=function(_kK){return E(E(_kK).a);},_kL=function(_kM,_kN,_kO,_kP){var _kQ=new T(function(){var _kR=E(_kP),_kS=E(_kO),_kT=B(_ka(new T2(0,_kM,_kN),_kR.a,_kR.b,_kR.c,_kS.a,_kS.b,_kS.c));return new T3(0,_kT.a,_kT.b,_kT.c);}),_kU=new T(function(){return B(A2(_7w,_kM,new T(function(){var _kV=E(_kQ),_kW=_kV.a,_kX=_kV.b,_kY=_kV.c;return B(_jm(_kM,_kW,_kX,_kY,_kW,_kX,_kY));})));});if(!B(A3(_kJ,B(_kH(_kN)),_kU,new T(function(){return B(A2(_8X,B(_7i(B(_7g(_kM)))),_8W));})))){var _kZ=E(_kQ),_l0=B(_jw(new T2(0,_kM,_kN),_kZ.a,_kZ.b,_kZ.c)),_l1=new T(function(){return B(_7k(new T(function(){return B(_7i(new T(function(){return B(_7g(_kM));})));})));}),_l2=new T(function(){return B(A2(_7w,_kM,new T(function(){var _l3=E(_kP),_l4=_l3.a,_l5=_l3.b,_l6=_l3.c;return B(_jm(_kM,_l4,_l5,_l6,_l4,_l5,_l6));})));});return new T3(0,new T(function(){return B(A2(_l1,_l0.a,_l2));}),new T(function(){return B(A2(_l1,_l0.b,_l2));}),new T(function(){return B(A2(_l1,_l0.c,_l2));}));}else{var _l7=new T(function(){return B(A2(_8X,B(_7i(B(_7g(_kM)))),_8W));});return new T3(0,_l7,_l7,_l7);}},_l8=0,_l9=new T(function(){var _la=eval("angleCount"),_lb=Number(_la);return jsTrunc(_lb);}),_lc=new T(function(){return E(_l9);}),_ld=new T(function(){return B(unCStr(": empty list"));}),_le=new T(function(){return B(unCStr("Prelude."));}),_lf=function(_lg){return new F(function(){return err(B(_f(_le,new T(function(){return B(_f(_lg,_ld));},1))));});},_lh=new T(function(){return B(unCStr("head"));}),_li=new T(function(){return B(_lf(_lh));}),_lj=function(_lk,_ll,_lm){var _ln=E(_lk);if(!_ln._){return __Z;}else{var _lo=E(_ll);if(!_lo._){return __Z;}else{var _lp=_lo.a,_lq=E(_lm);if(!_lq._){return __Z;}else{var _lr=E(_lq.a),_ls=_lr.a;return new F(function(){return _f(new T2(1,new T3(0,_ln.a,_lp,_ls),new T2(1,new T3(0,_lp,_ls,_lr.b),_o)),new T(function(){return B(_lj(_ln.b,_lo.b,_lq.b));},1));});}}}},_lt=new T(function(){return B(unCStr("tail"));}),_lu=new T(function(){return B(_lf(_lt));}),_lv=function(_lw,_lx){var _ly=E(_lw);if(!_ly._){return __Z;}else{var _lz=E(_lx);return (_lz._==0)?__Z:new T2(1,new T2(0,_ly.a,_lz.a),new T(function(){return B(_lv(_ly.b,_lz.b));}));}},_lA=function(_lB,_lC){var _lD=E(_lB);if(!_lD._){return __Z;}else{var _lE=E(_lC);if(!_lE._){return __Z;}else{var _lF=E(_lD.a),_lG=_lF.b,_lH=E(_lE.a).b,_lI=new T(function(){var _lJ=new T(function(){return B(_lv(_lH,new T(function(){var _lK=E(_lH);if(!_lK._){return E(_lu);}else{return E(_lK.b);}},1)));},1);return B(_lj(_lG,new T(function(){var _lL=E(_lG);if(!_lL._){return E(_lu);}else{return E(_lL.b);}},1),_lJ));});return new F(function(){return _f(new T2(1,new T3(0,_lF.a,new T(function(){var _lM=E(_lG);if(!_lM._){return E(_li);}else{return E(_lM.a);}}),new T(function(){var _lN=E(_lH);if(!_lN._){return E(_li);}else{return E(_lN.a);}})),_lI),new T(function(){return B(_lA(_lD.b,_lE.b));},1));});}}},_lO=new T(function(){return E(_lc)-1;}),_lP=new T1(0,1),_lQ=function(_lR,_lS){var _lT=E(_lS),_lU=new T(function(){var _lV=B(_7i(_lR)),_lW=B(_lQ(_lR,B(A3(_6I,_lV,_lT,new T(function(){return B(A2(_8X,_lV,_lP));})))));return new T2(1,_lW.a,_lW.b);});return new T2(0,_lT,_lU);},_lX=function(_lY){return E(E(_lY).d);},_lZ=new T1(0,2),_m0=function(_m1,_m2){var _m3=E(_m2);if(!_m3._){return __Z;}else{var _m4=_m3.a;return (!B(A1(_m1,_m4)))?__Z:new T2(1,_m4,new T(function(){return B(_m0(_m1,_m3.b));}));}},_m5=function(_m6,_m7,_m8,_m9){var _ma=B(_lQ(_m7,_m8)),_mb=new T(function(){var _mc=B(_7i(_m7)),_md=new T(function(){return B(A3(_98,_m7,new T(function(){return B(A2(_8X,_mc,_lP));}),new T(function(){return B(A2(_8X,_mc,_lZ));})));});return B(A3(_6I,_mc,_m9,_md));});return new F(function(){return _m0(function(_me){return new F(function(){return A3(_lX,_m6,_me,_mb);});},new T2(1,_ma.a,_ma.b));});},_mf=new T(function(){return B(_m5(_jk,_ij,_l8,_lO));}),_mg=function(_mh,_mi){while(1){var _mj=E(_mh);if(!_mj._){return E(_mi);}else{_mh=_mj.b;_mi=_mj.a;continue;}}},_mk=new T(function(){return B(unCStr("last"));}),_ml=new T(function(){return B(_lf(_mk));}),_mm=function(_mn){return new F(function(){return _mg(_mn,_ml);});},_mo=function(_mp){return new F(function(){return _mm(E(_mp).b);});},_mq=function(_mr,_ms){var _mt=E(_ms);return (_mt._==0)?__Z:new T2(1,new T(function(){return B(A1(_mr,_mt.a));}),new T(function(){return B(_mq(_mr,_mt.b));}));},_mu=new T(function(){var _mv=eval("proceedCount"),_mw=Number(_mv);return jsTrunc(_mw);}),_mx=new T(function(){return E(_mu);}),_my=1,_mz=new T(function(){return B(_m5(_jk,_ij,_my,_mx));}),_mA=function(_mB,_mC,_mD,_mE,_mF){var _mG=new T(function(){var _mH=new T(function(){var _mI=E(_mE),_mJ=_mI.a,_mK=_mI.b,_mL=_mI.c,_mM=E(_mF),_mN=_mM.a,_mO=_mM.b,_mP=_mM.c;return new T3(0,new T(function(){return E(_mK)*E(_mP)-E(_mO)*E(_mL);}),new T(function(){return E(_mL)*E(_mN)-E(_mP)*E(_mJ);}),new T(function(){return E(_mJ)*E(_mO)-E(_mN)*E(_mK);}));}),_mQ=function(_mR){var _mS=new T(function(){var _mT=E(_mR)/E(_lc);return (_mT+_mT)*3.141592653589793;}),_mU=new T(function(){return B(A1(_mB,_mS));}),_mV=new T(function(){var _mW=new T(function(){return E(_mS)+E(_mD);}),_mX=new T(function(){return E(_mU)/E(_mx);}),_mY=function(_mZ,_n0){var _n1=E(_mZ);if(!_n1._){return new T2(0,_o,_n0);}else{var _n2=new T(function(){var _n3=new T(function(){var _n4=E(_n0),_n5=E(_n4.a),_n6=E(_n4.b);return new T3(0,new T(function(){return E(_n5.a)+E(_n6.a)*E(_mX);}),new T(function(){return E(_n5.b)+E(_n6.b)*E(_mX);}),new T(function(){return E(_n5.c)+E(_n6.c)*E(_mX);}));}),_n7=B(_jE(_jl,_n3)),_n8=_n7.a;return new T2(0,new T3(0,_n8,new T2(0,new T(function(){return E(_n1.a)/E(_mx);}),_mU),_mS),new T2(0,_n8,new T(function(){var _n9=E(_n7.b),_na=E(E(_n0).b),_nb=B(_kx(_jl,_n9.a,_n9.b,_n9.c,_na.a,_na.b,_na.c));return new T3(0,_nb.a,_nb.b,_nb.c);})));}),_nc=new T(function(){var _nd=B(_mY(_n1.b,new T(function(){return E(E(_n2).b);})));return new T2(0,_nd.a,_nd.b);});return new T2(0,new T2(1,new T(function(){return E(E(_n2).a);}),new T(function(){return E(E(_nc).a);})),new T(function(){return E(E(_nc).b);}));}},_ne=function(_nf,_ng,_nh){var _ni=E(_nf);if(!_ni._){return new T2(0,_o,new T2(0,_ng,_nh));}else{var _nj=new T(function(){var _nk=new T(function(){var _nl=E(_ng),_nm=E(_nh);return new T3(0,new T(function(){return E(_nl.a)+E(_nm.a)*E(_mX);}),new T(function(){return E(_nl.b)+E(_nm.b)*E(_mX);}),new T(function(){return E(_nl.c)+E(_nm.c)*E(_mX);}));}),_nn=B(_jE(_jl,_nk)),_no=_nn.a;return new T2(0,new T3(0,_no,new T2(0,new T(function(){return E(_ni.a)/E(_mx);}),_mU),_mS),new T2(0,_no,new T(function(){var _np=E(_nn.b),_nq=E(_nh),_nr=B(_kx(_jl,_np.a,_np.b,_np.c,_nq.a,_nq.b,_nq.c));return new T3(0,_nr.a,_nr.b,_nr.c);})));}),_ns=new T(function(){var _nt=B(_mY(_ni.b,new T(function(){return E(E(_nj).b);})));return new T2(0,_nt.a,_nt.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nj).a);}),new T(function(){return E(E(_ns).a);})),new T(function(){return E(E(_ns).b);}));}},_nu=new T(function(){var _nv=E(_mE),_nw=E(_mH),_nx=new T(function(){return Math.cos(E(_mW));}),_ny=new T(function(){return Math.sin(E(_mW));});return new T3(0,new T(function(){return E(_nv.a)*E(_nx)+E(_nw.a)*E(_ny);}),new T(function(){return E(_nv.b)*E(_nx)+E(_nw.b)*E(_ny);}),new T(function(){return E(_nv.c)*E(_nx)+E(_nw.c)*E(_ny);}));});return E(B(_ne(_mz,_mC,_nu)).a);});return new T2(0,new T3(0,_mC,new T2(0,_l8,_mU),_mS),_mV);};return B(_mq(_mQ,_mf));}),_nz=new T(function(){var _nA=new T(function(){var _nB=B(_f(_mG,new T2(1,new T(function(){var _nC=E(_mG);if(!_nC._){return E(_li);}else{return E(_nC.a);}}),_o)));if(!_nB._){return E(_lu);}else{return E(_nB.b);}},1);return B(_lA(_mG,_nA));});return new T2(0,_nz,new T(function(){return B(_mq(_mo,_mG));}));},_nD=function(_nE,_nF,_nG,_nH,_nI,_nJ){var _nK=new T(function(){var _nL=B(_jE(_jl,new T(function(){return E(E(_nH).a);})));return new T2(0,_nL.a,_nL.b);}),_nM=new T(function(){return E(E(_nK).b);}),_nN=new T(function(){var _nO=E(_nM),_nP=E(_nJ),_nQ=B(_kx(_jl,_nO.a,_nO.b,_nO.c,_nP.a,_nP.b,_nP.c));return new T3(0,_nQ.a,_nQ.b,_nQ.c);}),_nR=new T(function(){return new T2(0,new T(function(){return E(E(_nK).a);}),E(_nH).b);}),_nS=new T(function(){var _nT=E(_nR),_nU=B(_mA(_nE,_nT.a,_nT.b,_nN,_nM));return new T2(0,_nU.a,_nU.b);}),_nV=new T(function(){var _nW=E(_nI);return new T2(0,new T(function(){var _nX=B(_kL(_iL,_jk,_nM,_nW.a));return new T3(0,_nX.a,_nX.b,_nX.c);}),_nW.b);});return {_:0,a:_nE,b:_nF,c:_nG,d:_nR,e:_nV,f:_nN,g:_nM,h:new T(function(){return E(E(_nS).a);}),i:new T(function(){return E(E(_nS).b);})};},_nY= -1,_nZ=0.5,_o0=new T3(0,_l8,_nZ,_nY),_o1=new T(function(){return 6.283185307179586/E(_lc);}),_o2=function(_o3,_o4,_o5,_o6,_o7){var _o8=function(_o9){var _oa=E(_o1),_ob=2+_o9|0,_oc=_ob-1|0,_od=(2+_o9)*(1+_o9),_oe=E(_mf);if(!_oe._){return _oa*0;}else{var _of=_oe.a,_og=_oe.b,_oh=B(A1(_o3,new T(function(){return 6.283185307179586*E(_of)/E(_lc);}))),_oi=B(A1(_o3,new T(function(){return 6.283185307179586*(E(_of)+1)/E(_lc);})));if(_oh!=_oi){if(_ob>=0){var _oj=E(_ob);if(!_oj){var _ok=function(_ol,_om){while(1){var _on=B((function(_oo,_op){var _oq=E(_oo);if(!_oq._){return E(_op);}else{var _or=_oq.a,_os=_oq.b,_ot=B(A1(_o3,new T(function(){return 6.283185307179586*E(_or)/E(_lc);}))),_ou=B(A1(_o3,new T(function(){return 6.283185307179586*(E(_or)+1)/E(_lc);})));if(_ot!=_ou){var _ov=_op+0/(_ot-_ou)/_od;_ol=_os;_om=_ov;return __continue;}else{if(_oc>=0){var _ow=E(_oc);if(!_ow){var _ov=_op+_ob/_od;_ol=_os;_om=_ov;return __continue;}else{var _ov=_op+_ob*B(_hs(_ot,_ow))/_od;_ol=_os;_om=_ov;return __continue;}}else{return E(_hj);}}}})(_ol,_om));if(_on!=__continue){return _on;}}};return _oa*B(_ok(_og,0/(_oh-_oi)/_od));}else{var _ox=function(_oy,_oz){while(1){var _oA=B((function(_oB,_oC){var _oD=E(_oB);if(!_oD._){return E(_oC);}else{var _oE=_oD.a,_oF=_oD.b,_oG=B(A1(_o3,new T(function(){return 6.283185307179586*E(_oE)/E(_lc);}))),_oH=B(A1(_o3,new T(function(){return 6.283185307179586*(E(_oE)+1)/E(_lc);})));if(_oG!=_oH){if(_oj>=0){var _oI=_oC+(B(_hs(_oG,_oj))-B(_hs(_oH,_oj)))/(_oG-_oH)/_od;_oy=_oF;_oz=_oI;return __continue;}else{return E(_hj);}}else{if(_oc>=0){var _oJ=E(_oc);if(!_oJ){var _oI=_oC+_ob/_od;_oy=_oF;_oz=_oI;return __continue;}else{var _oI=_oC+_ob*B(_hs(_oG,_oJ))/_od;_oy=_oF;_oz=_oI;return __continue;}}else{return E(_hj);}}}})(_oy,_oz));if(_oA!=__continue){return _oA;}}};return _oa*B(_ox(_og,(B(_hs(_oh,_oj))-B(_hs(_oi,_oj)))/(_oh-_oi)/_od));}}else{return E(_hj);}}else{if(_oc>=0){var _oK=E(_oc);if(!_oK){var _oL=function(_oM,_oN){while(1){var _oO=B((function(_oP,_oQ){var _oR=E(_oP);if(!_oR._){return E(_oQ);}else{var _oS=_oR.a,_oT=_oR.b,_oU=B(A1(_o3,new T(function(){return 6.283185307179586*E(_oS)/E(_lc);}))),_oV=B(A1(_o3,new T(function(){return 6.283185307179586*(E(_oS)+1)/E(_lc);})));if(_oU!=_oV){if(_ob>=0){var _oW=E(_ob);if(!_oW){var _oX=_oQ+0/(_oU-_oV)/_od;_oM=_oT;_oN=_oX;return __continue;}else{var _oX=_oQ+(B(_hs(_oU,_oW))-B(_hs(_oV,_oW)))/(_oU-_oV)/_od;_oM=_oT;_oN=_oX;return __continue;}}else{return E(_hj);}}else{var _oX=_oQ+_ob/_od;_oM=_oT;_oN=_oX;return __continue;}}})(_oM,_oN));if(_oO!=__continue){return _oO;}}};return _oa*B(_oL(_og,_ob/_od));}else{var _oY=function(_oZ,_p0){while(1){var _p1=B((function(_p2,_p3){var _p4=E(_p2);if(!_p4._){return E(_p3);}else{var _p5=_p4.a,_p6=_p4.b,_p7=B(A1(_o3,new T(function(){return 6.283185307179586*E(_p5)/E(_lc);}))),_p8=B(A1(_o3,new T(function(){return 6.283185307179586*(E(_p5)+1)/E(_lc);})));if(_p7!=_p8){if(_ob>=0){var _p9=E(_ob);if(!_p9){var _pa=_p3+0/(_p7-_p8)/_od;_oZ=_p6;_p0=_pa;return __continue;}else{var _pa=_p3+(B(_hs(_p7,_p9))-B(_hs(_p8,_p9)))/(_p7-_p8)/_od;_oZ=_p6;_p0=_pa;return __continue;}}else{return E(_hj);}}else{if(_oK>=0){var _pa=_p3+_ob*B(_hs(_p7,_oK))/_od;_oZ=_p6;_p0=_pa;return __continue;}else{return E(_hj);}}}})(_oZ,_p0));if(_p1!=__continue){return _p1;}}};return _oa*B(_oY(_og,_ob*B(_hs(_oh,_oK))/_od));}}else{return E(_hj);}}}},_pb=new T(function(){return 1/(B(_o8(1))*E(_o4));});return new F(function(){return _nD(_o3,_o0,new T2(0,new T3(0,_pb,_pb,_pb),new T(function(){return 1/(B(_o8(3))*E(_o4));})),_o5,_o6,_o7);});},_pc=1.2,_pd= -0.2,_pe=1,_pf=0,_pg=new T3(0,_pd,_pf,_pe),_ph=new T2(0,_pg,_pf),_pi=0.5,_pj= -0.8,_pk=new T3(0,_pj,_pi,_pf),_pl=new T2(0,_pk,_pf),_pm=0.2,_pn=function(_po){return E(_pm);},_pp=new T3(0,_pf,_pf,_pe),_pq=new T(function(){var _pr=B(_o2(_pn,_pc,_pl,_ph,_pp));return {_:0,a:_pr.a,b:_pr.b,c:_pr.c,d:_pr.d,e:_pr.e,f:_pr.f,g:_pr.g,h:_pr.h,i:_pr.i};}),_ps=0,_pt=1.3,_pu=new T3(0,_pt,_pf,_pf),_pv=new T2(0,_pu,_pf),_pw=function(_px){var _py=I_decodeDouble(_px);return new T2(0,new T1(1,_py.b),_py.a);},_pz=function(_pA){return new T1(0,_pA);},_pB=function(_pC){var _pD=hs_intToInt64(2147483647),_pE=hs_leInt64(_pC,_pD);if(!_pE){return new T1(1,I_fromInt64(_pC));}else{var _pF=hs_intToInt64( -2147483648),_pG=hs_geInt64(_pC,_pF);if(!_pG){return new T1(1,I_fromInt64(_pC));}else{var _pH=hs_int64ToInt(_pC);return new F(function(){return _pz(_pH);});}}},_pI=new T(function(){var _pJ=newByteArr(256),_pK=_pJ,_=_pK["v"]["i8"][0]=8,_pL=function(_pM,_pN,_pO,_){while(1){if(_pO>=256){if(_pM>=256){return E(_);}else{var _pP=imul(2,_pM)|0,_pQ=_pN+1|0,_pR=_pM;_pM=_pP;_pN=_pQ;_pO=_pR;continue;}}else{var _=_pK["v"]["i8"][_pO]=_pN,_pR=_pO+_pM|0;_pO=_pR;continue;}}},_=B(_pL(2,0,1,_));return _pK;}),_pS=function(_pT,_pU){var _pV=hs_int64ToInt(_pT),_pW=E(_pI),_pX=_pW["v"]["i8"][(255&_pV>>>0)>>>0&4294967295];if(_pU>_pX){if(_pX>=8){var _pY=hs_uncheckedIShiftRA64(_pT,8),_pZ=function(_q0,_q1){while(1){var _q2=B((function(_q3,_q4){var _q5=hs_int64ToInt(_q3),_q6=_pW["v"]["i8"][(255&_q5>>>0)>>>0&4294967295];if(_q4>_q6){if(_q6>=8){var _q7=hs_uncheckedIShiftRA64(_q3,8),_q8=_q4-8|0;_q0=_q7;_q1=_q8;return __continue;}else{return new T2(0,new T(function(){var _q9=hs_uncheckedIShiftRA64(_q3,_q6);return B(_pB(_q9));}),_q4-_q6|0);}}else{return new T2(0,new T(function(){var _qa=hs_uncheckedIShiftRA64(_q3,_q4);return B(_pB(_qa));}),0);}})(_q0,_q1));if(_q2!=__continue){return _q2;}}};return new F(function(){return _pZ(_pY,_pU-8|0);});}else{return new T2(0,new T(function(){var _qb=hs_uncheckedIShiftRA64(_pT,_pX);return B(_pB(_qb));}),_pU-_pX|0);}}else{return new T2(0,new T(function(){var _qc=hs_uncheckedIShiftRA64(_pT,_pU);return B(_pB(_qc));}),0);}},_qd=function(_qe){var _qf=hs_intToInt64(_qe);return E(_qf);},_qg=function(_qh){var _qi=E(_qh);if(!_qi._){return new F(function(){return _qd(_qi.a);});}else{return new F(function(){return I_toInt64(_qi.a);});}},_qj=function(_qk){return I_toInt(_qk)>>>0;},_ql=function(_qm){var _qn=E(_qm);if(!_qn._){return _qn.a>>>0;}else{return new F(function(){return _qj(_qn.a);});}},_qo=function(_qp){var _qq=B(_pw(_qp)),_qr=_qq.a,_qs=_qq.b;if(_qs<0){var _qt=function(_qu){if(!_qu){return new T2(0,E(_qr),B(_3u(_1M, -_qs)));}else{var _qv=B(_pS(B(_qg(_qr)), -_qs));return new T2(0,E(_qv.a),B(_3u(_1M,_qv.b)));}};if(!((B(_ql(_qr))&1)>>>0)){return new F(function(){return _qt(1);});}else{return new F(function(){return _qt(0);});}}else{return new T2(0,B(_3u(_qr,_qs)),_1M);}},_qw=function(_qx){var _qy=B(_qo(E(_qx)));return new T2(0,E(_qy.a),E(_qy.b));},_qz=new T3(0,_if,_jk,_qw),_qA=function(_qB){return E(E(_qB).a);},_qC=function(_qD){return E(E(_qD).a);},_qE=function(_qF,_qG){if(_qF<=_qG){var _qH=function(_qI){return new T2(1,_qI,new T(function(){if(_qI!=_qG){return B(_qH(_qI+1|0));}else{return __Z;}}));};return new F(function(){return _qH(_qF);});}else{return __Z;}},_qJ=function(_qK){return new F(function(){return _qE(E(_qK),2147483647);});},_qL=function(_qM,_qN,_qO){if(_qO<=_qN){var _qP=new T(function(){var _qQ=_qN-_qM|0,_qR=function(_qS){return (_qS>=(_qO-_qQ|0))?new T2(1,_qS,new T(function(){return B(_qR(_qS+_qQ|0));})):new T2(1,_qS,_o);};return B(_qR(_qN));});return new T2(1,_qM,_qP);}else{return (_qO<=_qM)?new T2(1,_qM,_o):__Z;}},_qT=function(_qU,_qV,_qW){if(_qW>=_qV){var _qX=new T(function(){var _qY=_qV-_qU|0,_qZ=function(_r0){return (_r0<=(_qW-_qY|0))?new T2(1,_r0,new T(function(){return B(_qZ(_r0+_qY|0));})):new T2(1,_r0,_o);};return B(_qZ(_qV));});return new T2(1,_qU,_qX);}else{return (_qW>=_qU)?new T2(1,_qU,_o):__Z;}},_r1=function(_r2,_r3){if(_r3<_r2){return new F(function(){return _qL(_r2,_r3, -2147483648);});}else{return new F(function(){return _qT(_r2,_r3,2147483647);});}},_r4=function(_r5,_r6){return new F(function(){return _r1(E(_r5),E(_r6));});},_r7=function(_r8,_r9,_ra){if(_r9<_r8){return new F(function(){return _qL(_r8,_r9,_ra);});}else{return new F(function(){return _qT(_r8,_r9,_ra);});}},_rb=function(_rc,_rd,_re){return new F(function(){return _r7(E(_rc),E(_rd),E(_re));});},_rf=function(_rg,_rh){return new F(function(){return _qE(E(_rg),E(_rh));});},_ri=function(_rj){return E(_rj);},_rk=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_rl=new T(function(){return B(err(_rk));}),_rm=function(_rn){var _ro=E(_rn);return (_ro==( -2147483648))?E(_rl):_ro-1|0;},_rp=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_rq=new T(function(){return B(err(_rp));}),_rr=function(_rs){var _rt=E(_rs);return (_rt==2147483647)?E(_rq):_rt+1|0;},_ru={_:0,a:_rr,b:_rm,c:_ri,d:_ri,e:_qJ,f:_r4,g:_rf,h:_rb},_rv=function(_rw,_rx){if(_rw<=0){if(_rw>=0){return new F(function(){return quot(_rw,_rx);});}else{if(_rx<=0){return new F(function(){return quot(_rw,_rx);});}else{return quot(_rw+1|0,_rx)-1|0;}}}else{if(_rx>=0){if(_rw>=0){return new F(function(){return quot(_rw,_rx);});}else{if(_rx<=0){return new F(function(){return quot(_rw,_rx);});}else{return quot(_rw+1|0,_rx)-1|0;}}}else{return quot(_rw-1|0,_rx)-1|0;}}},_ry=0,_rz=new T(function(){return B(_2R(_ry));}),_rA=new T(function(){return die(_rz);}),_rB=function(_rC,_rD){var _rE=E(_rD);switch(_rE){case  -1:var _rF=E(_rC);if(_rF==( -2147483648)){return E(_rA);}else{return new F(function(){return _rv(_rF, -1);});}break;case 0:return E(_2V);default:return new F(function(){return _rv(_rC,_rE);});}},_rG=function(_rH,_rI){return new F(function(){return _rB(E(_rH),E(_rI));});},_rJ=0,_rK=new T2(0,_rA,_rJ),_rL=function(_rM,_rN){var _rO=E(_rM),_rP=E(_rN);switch(_rP){case  -1:var _rQ=E(_rO);if(_rQ==( -2147483648)){return E(_rK);}else{if(_rQ<=0){if(_rQ>=0){var _rR=quotRemI(_rQ, -1);return new T2(0,_rR.a,_rR.b);}else{var _rS=quotRemI(_rQ, -1);return new T2(0,_rS.a,_rS.b);}}else{var _rT=quotRemI(_rQ-1|0, -1);return new T2(0,_rT.a-1|0,(_rT.b+( -1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_rO<=0){if(_rO>=0){var _rU=quotRemI(_rO,_rP);return new T2(0,_rU.a,_rU.b);}else{if(_rP<=0){var _rV=quotRemI(_rO,_rP);return new T2(0,_rV.a,_rV.b);}else{var _rW=quotRemI(_rO+1|0,_rP);return new T2(0,_rW.a-1|0,(_rW.b+_rP|0)-1|0);}}}else{if(_rP>=0){if(_rO>=0){var _rX=quotRemI(_rO,_rP);return new T2(0,_rX.a,_rX.b);}else{if(_rP<=0){var _rY=quotRemI(_rO,_rP);return new T2(0,_rY.a,_rY.b);}else{var _rZ=quotRemI(_rO+1|0,_rP);return new T2(0,_rZ.a-1|0,(_rZ.b+_rP|0)-1|0);}}}else{var _s0=quotRemI(_rO-1|0,_rP);return new T2(0,_s0.a-1|0,(_s0.b+_rP|0)+1|0);}}}},_s1=function(_s2,_s3){var _s4=_s2%_s3;if(_s2<=0){if(_s2>=0){return E(_s4);}else{if(_s3<=0){return E(_s4);}else{var _s5=E(_s4);return (_s5==0)?0:_s5+_s3|0;}}}else{if(_s3>=0){if(_s2>=0){return E(_s4);}else{if(_s3<=0){return E(_s4);}else{var _s6=E(_s4);return (_s6==0)?0:_s6+_s3|0;}}}else{var _s7=E(_s4);return (_s7==0)?0:_s7+_s3|0;}}},_s8=function(_s9,_sa){var _sb=E(_sa);switch(_sb){case  -1:return E(_rJ);case 0:return E(_2V);default:return new F(function(){return _s1(E(_s9),_sb);});}},_sc=function(_sd,_se){var _sf=E(_sd),_sg=E(_se);switch(_sg){case  -1:var _sh=E(_sf);if(_sh==( -2147483648)){return E(_rA);}else{return new F(function(){return quot(_sh, -1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_sf,_sg);});}},_si=function(_sj,_sk){var _sl=E(_sj),_sm=E(_sk);switch(_sm){case  -1:var _sn=E(_sl);if(_sn==( -2147483648)){return E(_rK);}else{var _so=quotRemI(_sn, -1);return new T2(0,_so.a,_so.b);}break;case 0:return E(_2V);default:var _sp=quotRemI(_sl,_sm);return new T2(0,_sp.a,_sp.b);}},_sq=function(_sr,_ss){var _st=E(_ss);switch(_st){case  -1:return E(_rJ);case 0:return E(_2V);default:return E(_sr)%_st;}},_su=function(_sv){return new F(function(){return _pz(E(_sv));});},_sw=function(_sx){return new T2(0,E(B(_pz(E(_sx)))),E(_lP));},_sy=function(_sz,_sA){return imul(E(_sz),E(_sA))|0;},_sB=function(_sC,_sD){return E(_sC)+E(_sD)|0;},_sE=function(_sF,_sG){return E(_sF)-E(_sG)|0;},_sH=function(_sI){var _sJ=E(_sI);return (_sJ<0)? -_sJ:E(_sJ);},_sK=function(_sL){return new F(function(){return _38(_sL);});},_sM=function(_sN){return  -E(_sN);},_sO= -1,_sP=0,_sQ=1,_sR=function(_sS){var _sT=E(_sS);return (_sT>=0)?(E(_sT)==0)?E(_sP):E(_sQ):E(_sO);},_sU={_:0,a:_sB,b:_sE,c:_sy,d:_sM,e:_sH,f:_sR,g:_sK},_sV=function(_sW,_sX){return E(_sW)==E(_sX);},_sY=function(_sZ,_t0){return E(_sZ)!=E(_t0);},_t1=new T2(0,_sV,_sY),_t2=function(_t3,_t4){var _t5=E(_t3),_t6=E(_t4);return (_t5>_t6)?E(_t5):E(_t6);},_t7=function(_t8,_t9){var _ta=E(_t8),_tb=E(_t9);return (_ta>_tb)?E(_tb):E(_ta);},_tc=function(_td,_te){return (_td>=_te)?(_td!=_te)?2:1:0;},_tf=function(_tg,_th){return new F(function(){return _tc(E(_tg),E(_th));});},_ti=function(_tj,_tk){return E(_tj)>=E(_tk);},_tl=function(_tm,_tn){return E(_tm)>E(_tn);},_to=function(_tp,_tq){return E(_tp)<=E(_tq);},_tr=function(_ts,_tt){return E(_ts)<E(_tt);},_tu={_:0,a:_t1,b:_tf,c:_tr,d:_to,e:_tl,f:_ti,g:_t2,h:_t7},_tv=new T3(0,_sU,_tu,_sw),_tw={_:0,a:_tv,b:_ru,c:_sc,d:_sq,e:_rG,f:_s8,g:_si,h:_rL,i:_su},_tx=new T1(0,2),_ty=function(_tz,_tA){while(1){var _tB=E(_tz);if(!_tB._){var _tC=_tB.a,_tD=E(_tA);if(!_tD._){var _tE=_tD.a;if(!(imul(_tC,_tE)|0)){return new T1(0,imul(_tC,_tE)|0);}else{_tz=new T1(1,I_fromInt(_tC));_tA=new T1(1,I_fromInt(_tE));continue;}}else{_tz=new T1(1,I_fromInt(_tC));_tA=_tD;continue;}}else{var _tF=E(_tA);if(!_tF._){_tz=_tB;_tA=new T1(1,I_fromInt(_tF.a));continue;}else{return new T1(1,I_mul(_tB.a,_tF.a));}}}},_tG=function(_tH,_tI,_tJ){while(1){if(!(_tI%2)){var _tK=B(_ty(_tH,_tH)),_tL=quot(_tI,2);_tH=_tK;_tI=_tL;continue;}else{var _tM=E(_tI);if(_tM==1){return new F(function(){return _ty(_tH,_tJ);});}else{var _tK=B(_ty(_tH,_tH)),_tN=B(_ty(_tH,_tJ));_tH=_tK;_tI=quot(_tM-1|0,2);_tJ=_tN;continue;}}}},_tO=function(_tP,_tQ){while(1){if(!(_tQ%2)){var _tR=B(_ty(_tP,_tP)),_tS=quot(_tQ,2);_tP=_tR;_tQ=_tS;continue;}else{var _tT=E(_tQ);if(_tT==1){return E(_tP);}else{return new F(function(){return _tG(B(_ty(_tP,_tP)),quot(_tT-1|0,2),_tP);});}}}},_tU=function(_tV){return E(E(_tV).b);},_tW=function(_tX){return E(E(_tX).c);},_tY=new T1(0,0),_tZ=function(_u0){return E(E(_u0).d);},_u1=function(_u2,_u3){var _u4=B(_qA(_u2)),_u5=new T(function(){return B(_qC(_u4));}),_u6=new T(function(){return B(A3(_tZ,_u2,_u3,new T(function(){return B(A2(_8X,_u5,_lZ));})));});return new F(function(){return A3(_kJ,B(_kH(B(_tU(_u4)))),_u6,new T(function(){return B(A2(_8X,_u5,_tY));}));});},_u7=new T(function(){return B(unCStr("Negative exponent"));}),_u8=new T(function(){return B(err(_u7));}),_u9=function(_ua){return E(E(_ua).c);},_ub=function(_uc,_ud,_ue,_uf){var _ug=B(_qA(_ud)),_uh=new T(function(){return B(_qC(_ug));}),_ui=B(_tU(_ug));if(!B(A3(_tW,_ui,_uf,new T(function(){return B(A2(_8X,_uh,_tY));})))){if(!B(A3(_kJ,B(_kH(_ui)),_uf,new T(function(){return B(A2(_8X,_uh,_tY));})))){var _uj=new T(function(){return B(A2(_8X,_uh,_lZ));}),_uk=new T(function(){return B(A2(_8X,_uh,_lP));}),_ul=B(_kH(_ui)),_um=function(_un,_uo,_up){while(1){var _uq=B((function(_ur,_us,_ut){if(!B(_u1(_ud,_us))){if(!B(A3(_kJ,_ul,_us,_uk))){var _uu=new T(function(){return B(A3(_u9,_ud,new T(function(){return B(A3(_7m,_uh,_us,_uk));}),_uj));});_un=new T(function(){return B(A3(_7k,_uc,_ur,_ur));});_uo=_uu;_up=new T(function(){return B(A3(_7k,_uc,_ur,_ut));});return __continue;}else{return new F(function(){return A3(_7k,_uc,_ur,_ut);});}}else{var _uv=_ut;_un=new T(function(){return B(A3(_7k,_uc,_ur,_ur));});_uo=new T(function(){return B(A3(_u9,_ud,_us,_uj));});_up=_uv;return __continue;}})(_un,_uo,_up));if(_uq!=__continue){return _uq;}}},_uw=function(_ux,_uy){while(1){var _uz=B((function(_uA,_uB){if(!B(_u1(_ud,_uB))){if(!B(A3(_kJ,_ul,_uB,_uk))){var _uC=new T(function(){return B(A3(_u9,_ud,new T(function(){return B(A3(_7m,_uh,_uB,_uk));}),_uj));});return new F(function(){return _um(new T(function(){return B(A3(_7k,_uc,_uA,_uA));}),_uC,_uA);});}else{return E(_uA);}}else{_ux=new T(function(){return B(A3(_7k,_uc,_uA,_uA));});_uy=new T(function(){return B(A3(_u9,_ud,_uB,_uj));});return __continue;}})(_ux,_uy));if(_uz!=__continue){return _uz;}}};return new F(function(){return _uw(_ue,_uf);});}else{return new F(function(){return A2(_8X,_uc,_lP);});}}else{return E(_u8);}},_uD=new T(function(){return B(err(_u7));}),_uE=function(_uF,_uG){var _uH=B(_pw(_uG)),_uI=_uH.a,_uJ=_uH.b,_uK=new T(function(){return B(_qC(new T(function(){return B(_qA(_uF));})));});if(_uJ<0){var _uL= -_uJ;if(_uL>=0){var _uM=E(_uL);if(!_uM){var _uN=E(_lP);}else{var _uN=B(_tO(_tx,_uM));}if(!B(_30(_uN,_3t))){var _uO=B(_3k(_uI,_uN));return new T2(0,new T(function(){return B(A2(_8X,_uK,_uO.a));}),new T(function(){return B(_2W(_uO.b,_uJ));}));}else{return E(_2V);}}else{return E(_uD);}}else{var _uP=new T(function(){var _uQ=new T(function(){return B(_ub(_uK,_tw,new T(function(){return B(A2(_8X,_uK,_tx));}),_uJ));});return B(A3(_7k,_uK,new T(function(){return B(A2(_8X,_uK,_uI));}),_uQ));});return new T2(0,_uP,_6i);}},_uR=function(_uS,_uT){var _uU=B(_uE(_uS,E(_uT))),_uV=_uU.a;if(E(_uU.b)<=0){return E(_uV);}else{var _uW=B(_qC(B(_qA(_uS))));return new F(function(){return A3(_6I,_uW,_uV,new T(function(){return B(A2(_8X,_uW,_1M));}));});}},_uX=function(_uY,_uZ){var _v0=B(_uE(_uY,E(_uZ))),_v1=_v0.a;if(E(_v0.b)>=0){return E(_v1);}else{var _v2=B(_qC(B(_qA(_uY))));return new F(function(){return A3(_7m,_v2,_v1,new T(function(){return B(A2(_8X,_v2,_1M));}));});}},_v3=function(_v4,_v5){var _v6=B(_uE(_v4,E(_v5)));return new T2(0,_v6.a,_v6.b);},_v7=function(_v8,_v9){var _va=B(_uE(_v8,_v9)),_vb=_va.a,_vc=E(_va.b),_vd=new T(function(){var _ve=B(_qC(B(_qA(_v8))));if(_vc>=0){return B(A3(_6I,_ve,_vb,new T(function(){return B(A2(_8X,_ve,_1M));})));}else{return B(A3(_7m,_ve,_vb,new T(function(){return B(A2(_8X,_ve,_1M));})));}}),_vf=function(_vg){var _vh=_vg-0.5;return (_vh>=0)?(E(_vh)==0)?(!B(_u1(_v8,_vb)))?E(_vd):E(_vb):E(_vd):E(_vb);},_vi=E(_vc);if(!_vi){return new F(function(){return _vf(0);});}else{if(_vi<=0){var _vj= -_vi-0.5;return (_vj>=0)?(E(_vj)==0)?(!B(_u1(_v8,_vb)))?E(_vd):E(_vb):E(_vd):E(_vb);}else{return new F(function(){return _vf(_vi);});}}},_vk=function(_vl,_vm){return new F(function(){return _v7(_vl,E(_vm));});},_vn=function(_vo,_vp){return E(B(_uE(_vo,E(_vp))).a);},_vq={_:0,a:_qz,b:_ij,c:_v3,d:_vn,e:_vk,f:_uR,g:_uX},_vr=new T1(0,1),_vs=function(_vt,_vu){var _vv=E(_vt);return new T2(0,_vv,new T(function(){var _vw=B(_vs(B(_3b(_vv,_vu)),_vu));return new T2(1,_vw.a,_vw.b);}));},_vx=function(_vy){var _vz=B(_vs(_vy,_vr));return new T2(1,_vz.a,_vz.b);},_vA=function(_vB,_vC){var _vD=B(_vs(_vB,new T(function(){return B(_5w(_vC,_vB));})));return new T2(1,_vD.a,_vD.b);},_vE=new T1(0,0),_vF=function(_vG,_vH){var _vI=E(_vG);if(!_vI._){var _vJ=_vI.a,_vK=E(_vH);return (_vK._==0)?_vJ>=_vK.a:I_compareInt(_vK.a,_vJ)<=0;}else{var _vL=_vI.a,_vM=E(_vH);return (_vM._==0)?I_compareInt(_vL,_vM.a)>=0:I_compare(_vL,_vM.a)>=0;}},_vN=function(_vO,_vP,_vQ){if(!B(_vF(_vP,_vE))){var _vR=function(_vS){return (!B(_3N(_vS,_vQ)))?new T2(1,_vS,new T(function(){return B(_vR(B(_3b(_vS,_vP))));})):__Z;};return new F(function(){return _vR(_vO);});}else{var _vT=function(_vU){return (!B(_3E(_vU,_vQ)))?new T2(1,_vU,new T(function(){return B(_vT(B(_3b(_vU,_vP))));})):__Z;};return new F(function(){return _vT(_vO);});}},_vV=function(_vW,_vX,_vY){return new F(function(){return _vN(_vW,B(_5w(_vX,_vW)),_vY);});},_vZ=function(_w0,_w1){return new F(function(){return _vN(_w0,_vr,_w1);});},_w2=function(_w3){return new F(function(){return _38(_w3);});},_w4=function(_w5){return new F(function(){return _5w(_w5,_vr);});},_w6=function(_w7){return new F(function(){return _3b(_w7,_vr);});},_w8=function(_w9){return new F(function(){return _pz(E(_w9));});},_wa={_:0,a:_w6,b:_w4,c:_w8,d:_w2,e:_vx,f:_vA,g:_vZ,h:_vV},_wb=function(_wc,_wd){while(1){var _we=E(_wc);if(!_we._){var _wf=E(_we.a);if(_wf==( -2147483648)){_wc=new T1(1,I_fromInt( -2147483648));continue;}else{var _wg=E(_wd);if(!_wg._){return new T1(0,B(_rv(_wf,_wg.a)));}else{_wc=new T1(1,I_fromInt(_wf));_wd=_wg;continue;}}}else{var _wh=_we.a,_wi=E(_wd);return (_wi._==0)?new T1(1,I_div(_wh,I_fromInt(_wi.a))):new T1(1,I_div(_wh,_wi.a));}}},_wj=function(_wk,_wl){if(!B(_30(_wl,_tY))){return new F(function(){return _wb(_wk,_wl);});}else{return E(_2V);}},_wm=function(_wn,_wo){while(1){var _wp=E(_wn);if(!_wp._){var _wq=E(_wp.a);if(_wq==( -2147483648)){_wn=new T1(1,I_fromInt( -2147483648));continue;}else{var _wr=E(_wo);if(!_wr._){var _ws=_wr.a;return new T2(0,new T1(0,B(_rv(_wq,_ws))),new T1(0,B(_s1(_wq,_ws))));}else{_wn=new T1(1,I_fromInt(_wq));_wo=_wr;continue;}}}else{var _wt=E(_wo);if(!_wt._){_wn=_wp;_wo=new T1(1,I_fromInt(_wt.a));continue;}else{var _wu=I_divMod(_wp.a,_wt.a);return new T2(0,new T1(1,_wu.a),new T1(1,_wu.b));}}}},_wv=function(_ww,_wx){if(!B(_30(_wx,_tY))){var _wy=B(_wm(_ww,_wx));return new T2(0,_wy.a,_wy.b);}else{return E(_2V);}},_wz=function(_wA,_wB){while(1){var _wC=E(_wA);if(!_wC._){var _wD=E(_wC.a);if(_wD==( -2147483648)){_wA=new T1(1,I_fromInt( -2147483648));continue;}else{var _wE=E(_wB);if(!_wE._){return new T1(0,B(_s1(_wD,_wE.a)));}else{_wA=new T1(1,I_fromInt(_wD));_wB=_wE;continue;}}}else{var _wF=_wC.a,_wG=E(_wB);return (_wG._==0)?new T1(1,I_mod(_wF,I_fromInt(_wG.a))):new T1(1,I_mod(_wF,_wG.a));}}},_wH=function(_wI,_wJ){if(!B(_30(_wJ,_tY))){return new F(function(){return _wz(_wI,_wJ);});}else{return E(_2V);}},_wK=function(_wL,_wM){while(1){var _wN=E(_wL);if(!_wN._){var _wO=E(_wN.a);if(_wO==( -2147483648)){_wL=new T1(1,I_fromInt( -2147483648));continue;}else{var _wP=E(_wM);if(!_wP._){return new T1(0,quot(_wO,_wP.a));}else{_wL=new T1(1,I_fromInt(_wO));_wM=_wP;continue;}}}else{var _wQ=_wN.a,_wR=E(_wM);return (_wR._==0)?new T1(0,I_toInt(I_quot(_wQ,I_fromInt(_wR.a)))):new T1(1,I_quot(_wQ,_wR.a));}}},_wS=function(_wT,_wU){if(!B(_30(_wU,_tY))){return new F(function(){return _wK(_wT,_wU);});}else{return E(_2V);}},_wV=function(_wW,_wX){if(!B(_30(_wX,_tY))){var _wY=B(_3k(_wW,_wX));return new T2(0,_wY.a,_wY.b);}else{return E(_2V);}},_wZ=function(_x0,_x1){while(1){var _x2=E(_x0);if(!_x2._){var _x3=E(_x2.a);if(_x3==( -2147483648)){_x0=new T1(1,I_fromInt( -2147483648));continue;}else{var _x4=E(_x1);if(!_x4._){return new T1(0,_x3%_x4.a);}else{_x0=new T1(1,I_fromInt(_x3));_x1=_x4;continue;}}}else{var _x5=_x2.a,_x6=E(_x1);return (_x6._==0)?new T1(1,I_rem(_x5,I_fromInt(_x6.a))):new T1(1,I_rem(_x5,_x6.a));}}},_x7=function(_x8,_x9){if(!B(_30(_x9,_tY))){return new F(function(){return _wZ(_x8,_x9);});}else{return E(_2V);}},_xa=function(_xb){return E(_xb);},_xc=function(_xd){return E(_xd);},_xe=function(_xf){var _xg=E(_xf);if(!_xg._){var _xh=E(_xg.a);return (_xh==( -2147483648))?E(_6a):(_xh<0)?new T1(0, -_xh):E(_xg);}else{var _xi=_xg.a;return (I_compareInt(_xi,0)>=0)?E(_xg):new T1(1,I_negate(_xi));}},_xj=new T1(0,0),_xk=new T1(0, -1),_xl=function(_xm){var _xn=E(_xm);if(!_xn._){var _xo=_xn.a;return (_xo>=0)?(E(_xo)==0)?E(_xj):E(_3M):E(_xk);}else{var _xp=I_compareInt(_xn.a,0);return (_xp<=0)?(E(_xp)==0)?E(_xj):E(_xk):E(_3M);}},_xq={_:0,a:_3b,b:_5w,c:_ty,d:_6b,e:_xe,f:_xl,g:_xc},_xr=function(_xs,_xt){var _xu=E(_xs);if(!_xu._){var _xv=_xu.a,_xw=E(_xt);return (_xw._==0)?_xv!=_xw.a:(I_compareInt(_xw.a,_xv)==0)?false:true;}else{var _xx=_xu.a,_xy=E(_xt);return (_xy._==0)?(I_compareInt(_xx,_xy.a)==0)?false:true:(I_compare(_xx,_xy.a)==0)?false:true;}},_xz=new T2(0,_30,_xr),_xA=function(_xB,_xC){return (!B(_5h(_xB,_xC)))?E(_xB):E(_xC);},_xD=function(_xE,_xF){return (!B(_5h(_xE,_xF)))?E(_xF):E(_xE);},_xG={_:0,a:_xz,b:_1N,c:_3N,d:_5h,e:_3E,f:_vF,g:_xA,h:_xD},_xH=function(_xI){return new T2(0,E(_xI),E(_lP));},_xJ=new T3(0,_xq,_xG,_xH),_xK={_:0,a:_xJ,b:_wa,c:_wS,d:_x7,e:_wj,f:_wH,g:_wV,h:_wv,i:_xa},_xL=function(_xM){return E(E(_xM).b);},_xN=function(_xO){return E(E(_xO).g);},_xP=new T1(0,1),_xQ=function(_xR,_xS,_xT){var _xU=B(_xL(_xR)),_xV=B(_7i(_xU)),_xW=new T(function(){var _xX=new T(function(){var _xY=new T(function(){var _xZ=new T(function(){return B(A3(_xN,_xR,_xK,new T(function(){return B(A3(_98,_xU,_xS,_xT));})));});return B(A2(_8X,_xV,_xZ));}),_y0=new T(function(){return B(A2(_6K,_xV,new T(function(){return B(A2(_8X,_xV,_xP));})));});return B(A3(_7k,_xV,_y0,_xY));});return B(A3(_7k,_xV,_xX,_xT));});return new F(function(){return A3(_6I,_xV,_xS,_xW);});},_y1=1.5707963267948966,_y2=function(_y3){return 0.2/Math.cos(B(_xQ(_vq,_y3,_y1))-0.7853981633974483);},_y4=2,_y5=0.3,_y6= -0.1,_y7=new T3(0,_pf,_y6,_y5),_y8=new T2(0,_y7,_y4),_y9=new T(function(){var _ya=B(_o2(_y2,_pc,_pv,_y8,_pp));return {_:0,a:_ya.a,b:_ya.b,c:_ya.c,d:_ya.d,e:_ya.e,f:_ya.f,g:_ya.g,h:_ya.h,i:_ya.i};}),_yb=new T2(1,_y9,_o),_yc=new T2(1,_pq,_yb),_yd=new T(function(){return B(unCStr("Negative range size"));}),_ye=new T(function(){return B(err(_yd));}),_yf=function(_){var _yg=B(_hb(_yc,0))-1|0,_yh=function(_yi){if(_yi>=0){var _yj=newArr(_yi,_hh),_yk=_yj,_yl=E(_yi);if(!_yl){return new T4(0,E(_ps),E(_yg),0,_yk);}else{var _ym=function(_yn,_yo,_){while(1){var _yp=E(_yn);if(!_yp._){return E(_);}else{var _=_yk[_yo]=_yp.a;if(_yo!=(_yl-1|0)){var _yq=_yo+1|0;_yn=_yp.b;_yo=_yq;continue;}else{return E(_);}}}},_=B((function(_yr,_ys,_yt,_){var _=_yk[_yt]=_yr;if(_yt!=(_yl-1|0)){return new F(function(){return _ym(_ys,_yt+1|0,_);});}else{return E(_);}})(_pq,_yb,0,_));return new T4(0,E(_ps),E(_yg),_yl,_yk);}}else{return E(_ye);}};if(0>_yg){return new F(function(){return _yh(0);});}else{return new F(function(){return _yh(_yg+1|0);});}},_yu=function(_yv){var _yw=B(A1(_yv,_));return E(_yw);},_yx=new T(function(){return B(_yu(_yf));}),_yy=function(_yz,_yA,_){var _yB=B(A1(_yz,_)),_yC=B(A1(_yA,_));return _yB;},_yD=function(_yE,_yF,_){var _yG=B(A1(_yE,_)),_yH=B(A1(_yF,_));return new T(function(){return B(A1(_yG,_yH));});},_yI=function(_yJ,_yK,_){var _yL=B(A1(_yK,_));return _yJ;},_yM=function(_yN,_yO,_){var _yP=B(A1(_yO,_));return new T(function(){return B(A1(_yN,_yP));});},_yQ=new T2(0,_yM,_yI),_yR=function(_yS,_){return _yS;},_yT=function(_yU,_yV,_){var _yW=B(A1(_yU,_));return new F(function(){return A1(_yV,_);});},_yX=new T5(0,_yQ,_yR,_yD,_yT,_yy),_yY=function(_yZ){var _z0=E(_yZ);return (E(_z0.b)-E(_z0.a)|0)+1|0;},_z1=function(_z2,_z3){var _z4=E(_z2),_z5=E(_z3);return (E(_z4.a)>_z5)?false:_z5<=E(_z4.b);},_z6=function(_z7,_z8){var _z9=jsShowI(_z7);return new F(function(){return _f(fromJSStr(_z9),_z8);});},_za=function(_zb,_zc,_zd){if(_zc>=0){return new F(function(){return _z6(_zc,_zd);});}else{if(_zb<=6){return new F(function(){return _z6(_zc,_zd);});}else{return new T2(1,_71,new T(function(){var _ze=jsShowI(_zc);return B(_f(fromJSStr(_ze),new T2(1,_70,_zd)));}));}}},_zf=function(_zg){return new F(function(){return _za(0,E(_zg),_o);});},_zh=function(_zi,_zj,_zk){return new F(function(){return _za(E(_zi),E(_zj),_zk);});},_zl=function(_zm,_zn){return new F(function(){return _za(0,E(_zm),_zn);});},_zo=function(_zp,_zq){return new F(function(){return _2B(_zl,_zp,_zq);});},_zr=new T3(0,_zh,_zf,_zo),_zs=0,_zt=function(_zu,_zv,_zw){return new F(function(){return A1(_zu,new T2(1,_2y,new T(function(){return B(A1(_zv,_zw));})));});},_zx=new T(function(){return B(unCStr("foldr1"));}),_zy=new T(function(){return B(_lf(_zx));}),_zz=function(_zA,_zB){var _zC=E(_zB);if(!_zC._){return E(_zy);}else{var _zD=_zC.a,_zE=E(_zC.b);if(!_zE._){return E(_zD);}else{return new F(function(){return A2(_zA,_zD,new T(function(){return B(_zz(_zA,_zE));}));});}}},_zF=new T(function(){return B(unCStr(" out of range "));}),_zG=new T(function(){return B(unCStr("}.index: Index "));}),_zH=new T(function(){return B(unCStr("Ix{"));}),_zI=new T2(1,_70,_o),_zJ=new T2(1,_70,_zI),_zK=0,_zL=function(_zM){return E(E(_zM).a);},_zN=function(_zO,_zP,_zQ,_zR,_zS){var _zT=new T(function(){var _zU=new T(function(){var _zV=new T(function(){var _zW=new T(function(){var _zX=new T(function(){return B(A3(_zz,_zt,new T2(1,new T(function(){return B(A3(_zL,_zQ,_zK,_zR));}),new T2(1,new T(function(){return B(A3(_zL,_zQ,_zK,_zS));}),_o)),_zJ));});return B(_f(_zF,new T2(1,_71,new T2(1,_71,_zX))));});return B(A(_zL,[_zQ,_zs,_zP,new T2(1,_70,_zW)]));});return B(_f(_zG,new T2(1,_71,_zV)));},1);return B(_f(_zO,_zU));},1);return new F(function(){return err(B(_f(_zH,_zT)));});},_zY=function(_zZ,_A0,_A1,_A2,_A3){return new F(function(){return _zN(_zZ,_A0,_A3,_A1,_A2);});},_A4=function(_A5,_A6,_A7,_A8){var _A9=E(_A7);return new F(function(){return _zY(_A5,_A6,_A9.a,_A9.b,_A8);});},_Aa=function(_Ab,_Ac,_Ad,_Ae){return new F(function(){return _A4(_Ae,_Ad,_Ac,_Ab);});},_Af=new T(function(){return B(unCStr("Int"));}),_Ag=function(_Ah,_Ai){return new F(function(){return _Aa(_zr,_Ah,_Ai,_Af);});},_Aj=function(_Ak,_Al){var _Am=E(_Ak),_An=E(_Am.a),_Ao=E(_Al);if(_An>_Ao){return new F(function(){return _Ag(_Am,_Ao);});}else{if(_Ao>E(_Am.b)){return new F(function(){return _Ag(_Am,_Ao);});}else{return _Ao-_An|0;}}},_Ap=function(_Aq){var _Ar=E(_Aq);return new F(function(){return _rf(_Ar.a,_Ar.b);});},_As=function(_At){var _Au=E(_At),_Av=E(_Au.a),_Aw=E(_Au.b);return (_Av>_Aw)?E(_zs):(_Aw-_Av|0)+1|0;},_Ax=function(_Ay,_Az){return new F(function(){return _sE(_Az,E(_Ay).a);});},_AA={_:0,a:_tu,b:_Ap,c:_Aj,d:_Ax,e:_z1,f:_As,g:_yY},_AB=function(_AC,_AD){return new T2(1,_AC,_AD);},_AE=function(_AF,_AG){var _AH=E(_AG);return new T2(0,_AH.a,_AH.b);},_AI=function(_AJ){return E(E(_AJ).f);},_AK=function(_AL,_AM,_AN){var _AO=E(_AM),_AP=_AO.a,_AQ=_AO.b,_AR=function(_){var _AS=B(A2(_AI,_AL,_AO));if(_AS>=0){var _AT=newArr(_AS,_hh),_AU=_AT,_AV=E(_AS);if(!_AV){return new T(function(){return new T4(0,E(_AP),E(_AQ),0,_AU);});}else{var _AW=function(_AX,_AY,_){while(1){var _AZ=E(_AX);if(!_AZ._){return E(_);}else{var _=_AU[_AY]=_AZ.a;if(_AY!=(_AV-1|0)){var _B0=_AY+1|0;_AX=_AZ.b;_AY=_B0;continue;}else{return E(_);}}}},_=B(_AW(_AN,0,_));return new T(function(){return new T4(0,E(_AP),E(_AQ),_AV,_AU);});}}else{return E(_ye);}};return new F(function(){return _yu(_AR);});},_B1=function(_B2,_B3,_B4,_B5){var _B6=new T(function(){var _B7=E(_B5),_B8=_B7.c-1|0,_B9=new T(function(){return B(A2(_cU,_B3,_o));});if(0<=_B8){var _Ba=new T(function(){return B(_94(_B3));}),_Bb=function(_Bc){var _Bd=new T(function(){var _Be=new T(function(){return B(A1(_B4,new T(function(){return E(_B7.d[_Bc]);})));});return B(A3(_9c,_Ba,_AB,_Be));});return new F(function(){return A3(_9a,_B3,_Bd,new T(function(){if(_Bc!=_B8){return B(_Bb(_Bc+1|0));}else{return E(_B9);}}));});};return B(_Bb(0));}else{return E(_B9);}}),_Bf=new T(function(){return B(_AE(_B2,_B5));});return new F(function(){return A3(_9c,B(_94(_B3)),function(_Bg){return new F(function(){return _AK(_B2,_Bf,_Bg);});},_B6);});},_Bh=0,_Bi=function(_){return _Bh;},_Bj=new T(function(){return eval("vertex");}),_Bk=function(_Bl,_Bm,_Bn,_Bo,_Bp,_Bq,_){var _Br=__apply(E(_Bj),new T2(1,_Bq,new T2(1,_Bp,new T2(1,_Bo,new T2(1,_Bn,new T2(1,_Bm,new T2(1,_Bl,_o)))))));return new F(function(){return _Bi(_);});},_Bs=function(_Bt,_){while(1){var _Bu=E(_Bt);if(!_Bu._){return _Bh;}else{var _Bv=E(_Bu.a),_Bw=E(_Bv.a),_Bx=E(_Bw.a),_By=E(_Bw.b),_Bz=B(_Bk(E(_Bx.a),E(_Bx.b),E(_Bx.c),E(_By.a),E(_By.b),E(_Bw.c),_)),_BA=E(_Bv.b),_BB=E(_BA.a),_BC=E(_BA.b),_BD=B(_Bk(E(_BB.a),E(_BB.b),E(_BB.c),E(_BC.a),E(_BC.b),E(_BA.c),_)),_BE=E(_Bv.c),_BF=E(_BE.a),_BG=E(_BE.b),_BH=B(_Bk(E(_BF.a),E(_BF.b),E(_BF.c),E(_BG.a),E(_BG.b),E(_BE.c),_));_Bt=_Bu.b;continue;}}},_BI=new T(function(){return eval("drawTriangles");}),_BJ=function(_){var _BK=__app0(E(_BI));return new F(function(){return _Bi(_);});},_BL=function(_BM,_){var _BN=B(_Bs(_BM,_));return new F(function(){return _BJ(_);});},_BO=function(_BP,_){return new F(function(){return _BL(E(_BP).h,_);});},_BQ=new T(function(){return eval("draw");}),_BR=function(_BS){return E(_BS);},_BT=function(_BU){return E(_BU);},_BV=function(_BW,_BX){return E(_BX);},_BY=function(_BZ,_C0){return E(_BZ);},_C1=function(_C2){return E(_C2);},_C3=new T2(0,_C1,_BY),_C4=function(_C5,_C6){return E(_C5);},_C7=new T5(0,_C3,_BT,_BR,_BV,_C4),_C8=function(_C9){var _Ca=jsShow(E(_C9));return new F(function(){return fromJSStr(_Ca);});},_Cb=function(_Cc){var _Cd=jsShow(E(_Cc));return new F(function(){return fromJSStr(_Cd);});},_Ce=function(_Cf){var _Cg=new T(function(){return B(_Cb(_Cf));});return function(_Ch){return new F(function(){return _f(_Cg,_Ch);});};},_Ci=function(_Cj,_Ck){return new F(function(){return _2B(_Ce,_Cj,_Ck);});},_Cl=function(_Cm,_Cn){var _Co=new T(function(){return B(_Cb(_Cn));});return function(_Ch){return new F(function(){return _f(_Co,_Ch);});};},_Cp=new T3(0,_Cl,_C8,_Ci),_Cq=new T(function(){return B(unCStr("World "));}),_Cr=11,_Cs=32,_Ct=function(_Cu,_Cv,_Cw,_Cx,_Cy){var _Cz=new T(function(){return B(A3(_zL,_Cu,_Cr,_Cw));}),_CA=new T(function(){return B(A3(_zL,_Cu,_Cr,_Cx));}),_CB=new T(function(){return B(A3(_zL,_Cu,_Cr,_Cy));}),_CC=function(_CD){var _CE=new T(function(){var _CF=new T(function(){return B(A1(_CA,new T2(1,_Cs,new T(function(){return B(A1(_CB,_CD));}))));});return B(A1(_Cz,new T2(1,_Cs,_CF)));},1);return new F(function(){return _f(_Cq,_CE);});};if(_Cv<11){return E(_CC);}else{var _CG=function(_CH){return new T2(1,_71,new T(function(){return B(_CC(new T2(1,_70,_CH)));}));};return E(_CG);}},_CI=new T(function(){return B(unCStr("Local "));}),_CJ=11,_CK=function(_CL,_CM,_CN,_CO){var _CP=new T(function(){return B(A3(_zL,_CL,_CJ,_CN));}),_CQ=new T(function(){return B(A3(_zL,_CL,_CJ,_CO));});if(_CM<11){var _CR=function(_CS){var _CT=new T(function(){return B(A1(_CP,new T2(1,_Cs,new T(function(){return B(A1(_CQ,_CS));}))));},1);return new F(function(){return _f(_CI,_CT);});};return E(_CR);}else{var _CU=function(_CV){var _CW=new T(function(){var _CX=new T(function(){return B(A1(_CP,new T2(1,_Cs,new T(function(){return B(A1(_CQ,new T2(1,_70,_CV)));}))));},1);return B(_f(_CI,_CX));});return new T2(1,_71,_CW);};return E(_CU);}},_CY=function(_CZ,_D0,_D1){var _D2=new T(function(){return B(A3(_zz,_zt,new T2(1,new T(function(){var _D3=E(_CZ);return B(_Ct(_Cp,0,_D3.a,_D3.b,_D3.c));}),new T2(1,new T(function(){var _D4=E(_D0);return B(_CK(_Cp,0,_D4.a,_D4.b));}),_o)),new T2(1,_70,_D1)));});return new T2(0,_71,_D2);},_D5=function(_D6,_D7){var _D8=E(_D6),_D9=B(_CY(_D8.a,_D8.b,_D7));return new T2(1,_D9.a,_D9.b);},_Da=function(_Db,_Dc){return new F(function(){return _2B(_D5,_Db,_Dc);});},_Dd=function(_De,_Df,_Dg,_Dh,_Di,_Dj){var _Dk=new T(function(){var _Dl=E(_Dh),_Dm=E(_Di),_Dn=new T(function(){var _Do=E(_Dl.a),_Dp=E(_Dm.a);return new T3(0,new T(function(){return E(_Do.a)+E(_Dp.a)*5.0e-2;}),new T(function(){return E(_Do.b)+E(_Dp.b)*5.0e-2;}),new T(function(){return E(_Do.c)+E(_Dp.c)*5.0e-2;}));});return new T2(0,_Dn,new T(function(){return E(_Dl.b)+E(_Dm.b)*5.0e-2;}));});return new F(function(){return _nD(_De,_Df,_Dg,_Dk,_Di,_Dj);});},_Dq=new T2(0,_iL,_jk),_Dr=function(_Ds){while(1){var _Dt=E(_Ds);if(!_Dt._){return true;}else{if(E(_Dt.a)<0){return false;}else{_Ds=_Dt.b;continue;}}}},_Du=function(_Dv,_Dw){if(E(_Dv)<0){return false;}else{return new F(function(){return _Dr(_Dw);});}},_Dx=function(_Dy,_Dz,_DA,_DB,_DC){var _DD=B(_7i(B(_7g(_Dy))));return new F(function(){return A3(_6I,_DD,new T(function(){return B(A3(_7k,_DD,_Dz,_DB));}),new T(function(){return B(A3(_7k,_DD,_DA,_DC));}));});},_DE=function(_DF,_DG){var _DH=new T(function(){return E(E(_DG).c);}),_DI=new T(function(){return E(E(_DF).a);}),_DJ=new T(function(){return B(_7i(new T(function(){return B(_7g(_DI));})));}),_DK=new T(function(){return B(A3(_7k,_DJ,new T(function(){return E(E(E(_DG).b).b);}),new T(function(){return E(E(E(_DG).b).a);})));}),_DL=new T(function(){return B(A3(_7k,_DJ,_DK,new T(function(){return B(A2(_bz,_DI,_DH));})));}),_DM=new T(function(){return B(A3(_7k,_DJ,_DK,new T(function(){return B(A2(_bx,_DI,_DH));})));});return new T2(0,_DM,_DL);},_DN=function(_DO){while(1){var _DP=B((function(_DQ){var _DR=E(_DQ);if(!_DR._){return __Z;}else{var _DS=_DR.b,_DT=E(_DR.a);if(!_DT._){_DO=_DS;return __continue;}else{return new T2(1,_DT.a,new T(function(){return B(_DN(_DS));}));}}})(_DO));if(_DP!=__continue){return _DP;}}},_DU=function(_DV,_DW){var _DX=function(_DY,_DZ){var _E0=E(_DY);if(!_E0._){return E(_DZ);}else{var _E1=_E0.a,_E2=new T(function(){var _E3=function(_E4){while(1){var _E5=B((function(_E6){var _E7=E(_E6);if(!_E7._){return __Z;}else{var _E8=_E7.b,_E9=E(E(_E1).a),_Ea=_E9.a,_Eb=_E9.b,_Ec=_E9.c,_Ed=E(_E7.a),_Ee=E(_Ed.a),_Ef=E(_Ee.a),_Eg=_Ef.a,_Eh=_Ef.b,_Ei=_Ef.c,_Ej=E(_Ed.c),_Ek=E(_Ej.a),_El=_Ek.a,_Em=_Ek.b,_En=_Ek.c,_Eo=E(_Ed.b),_Ep=E(_Eo.a),_Eq=_Ep.a,_Er=_Ep.b,_Es=_Ep.c,_Et=new T(function(){return E(_El)+ -E(_Eg);}),_Eu=new T(function(){return E(_Em)+ -E(_Eh);}),_Ev=new T(function(){return E(_En)+ -E(_Ei);}),_Ew=new T(function(){return E(_El)+ -E(_Eq);}),_Ex=new T(function(){return E(_Em)+ -E(_Er);}),_Ey=new T(function(){return E(_En)+ -E(_Es);}),_Ez=B(_jw(_Dq,new T(function(){return E(_Eu)*E(_Ey)-E(_Ex)*E(_Ev);}),new T(function(){return E(_Ev)*E(_Ew)-E(_Ey)*E(_Et);}),new T(function(){return E(_Et)*E(_Ex)-E(_Ew)*E(_Eu);}))),_EA=_Ez.a,_EB=_Ez.b,_EC=_Ez.c,_ED=B(_jm(_iL,new T(function(){return E(_Ea)+ -E(_Eg);}),new T(function(){return E(_Eb)+ -E(_Eh);}),new T(function(){return E(_Ec)+ -E(_Ei);}),_EA,_EB,_EC)),_EE=function(_EF){if(_EF>=0.1){return __Z;}else{var _EG=new T(function(){return E(_Ea)+ -(E(_EA)*_ED);}),_EH=new T(function(){return E(_Eb)+ -(E(_EB)*_ED);}),_EI=new T(function(){return E(_Ec)+ -(E(_EC)*_ED);}),_EJ=function(_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES){var _ET=new T(function(){return E(_EQ)+ -E(_EN);}),_EU=new T(function(){return E(_ER)+ -E(_EO);}),_EV=new T(function(){return E(_ES)+ -E(_EP);}),_EW=B(_jw(_Dq,new T(function(){return E(_EB)*E(_EV)-E(_EU)*E(_EC);}),new T(function(){return E(_EC)*E(_ET)-E(_EV)*E(_EA);}),new T(function(){return E(_EA)*E(_EU)-E(_ET)*E(_EB);}))),_EX=_EW.a,_EY=_EW.b,_EZ=_EW.c;return B(_jm(_iL,new T(function(){return E(_EG)+ -E(_EN);}),new T(function(){return E(_EH)+ -E(_EO);}),new T(function(){return E(_EI)+ -E(_EP);}),_EX,_EY,_EZ))/B(_jm(_iL,new T(function(){return E(_EK)+ -E(_EN);}),new T(function(){return E(_EL)+ -E(_EO);}),new T(function(){return E(_EM)+ -E(_EP);}),_EX,_EY,_EZ));},_F0=new T(function(){return B(_EJ(_Eg,_Eh,_Ei,_Eq,_Er,_Es,_El,_Em,_En));}),_F1=new T(function(){return B(_EJ(_Eq,_Er,_Es,_El,_Em,_En,_Eg,_Eh,_Ei));}),_F2=new T(function(){return B(_EJ(_El,_Em,_En,_Eg,_Eh,_Ei,_Eq,_Er,_Es));});if(!B(_Du(_F0,new T2(1,_F1,new T2(1,_F2,_o))))){return __Z;}else{var _F3=new T(function(){var _F4=B(_DE(_Dq,_Ee)),_F5=B(_DE(_Dq,_Eo)),_F6=B(_DE(_Dq,_Ej));return new T2(0,new T(function(){return E(_F4.a)*E(_F0)+E(_F5.a)*E(_F1)+E(_F6.a)*E(_F2);}),new T(function(){return E(_F4.b)*E(_F0)+E(_F5.b)*E(_F1)+E(_F6.b)*E(_F2);}));});return new T1(1,_F3);}}},_F7=E(_ED);if(!_F7){var _F8=B(_EE(0));if(!_F8._){_E4=_E8;return __continue;}else{return E(_F8);}}else{if(_F7<=0){var _F9=B(_EE( -_F7));if(!_F9._){_E4=_E8;return __continue;}else{return E(_F9);}}else{var _Fa=B(_EE(_F7));if(!_Fa._){_E4=_E8;return __continue;}else{return E(_Fa);}}}}})(_E4));if(_E5!=__continue){return _E5;}}},_Fb=B(_E3(_DW));if(!_Fb._){return __Z;}else{var _Fc=B(_DE(_Dq,_E1)),_Fd=E(_Fb.a),_Fe=new T(function(){return E(_Fd.a)+ -E(_Fc.a);}),_Ff=new T(function(){return E(_Fd.b)+ -E(_Fc.b);});if(Math.sqrt(B(_Dx(_iL,_Fe,_Ff,_Fe,_Ff)))<1.0e-4){return __Z;}else{return new T1(1,new T2(0,new T(function(){return E(E(_E1).a);}),_Fd));}}});return new T2(1,_E2,new T(function(){return B(_DX(_E0.b,_DZ));}));}};return new F(function(){return _DN(B(_DX(_DV,_o)));});},_Fg=function(_Fh){var _Fi=E(_Fh),_Fj=_Fi.b,_Fk=_Fi.g,_Fl=new T(function(){var _Fm=E(_Fi.e),_Fn=new T(function(){var _Fo=E(_Fm.a),_Fp=E(_Fj),_Fq=E(_Fk),_Fr=B(_ka(_Dq,_Fp.a,_Fp.b,_Fp.c,_Fq.a,_Fq.b,_Fq.c));return new T3(0,new T(function(){return E(_Fo.a)+E(_Fr.a)*5.0e-2;}),new T(function(){return E(_Fo.b)+E(_Fr.b)*5.0e-2;}),new T(function(){return E(_Fo.c)+E(_Fr.c)*5.0e-2;}));});return new T2(0,_Fn,_Fm.b);});return {_:0,a:_Fi.a,b:_Fj,c:_Fi.c,d:_Fi.d,e:_Fl,f:_Fi.f,g:_Fk,h:_Fi.h,i:_Fi.i};},_Fs=function(_Ft){var _Fu=E(_Ft),_Fv=B(_Dd(_Fu.a,_Fu.b,_Fu.c,_Fu.d,_Fu.e,_Fu.f));return {_:0,a:_Fv.a,b:_Fv.b,c:_Fv.c,d:_Fv.d,e:_Fv.e,f:_Fv.f,g:_Fv.g,h:_Fv.h,i:_Fv.i};},_Fw=function(_Fx){var _Fy=E(_Fx);if(!_Fy._){return __Z;}else{return new F(function(){return _f(_Fy.a,new T(function(){return B(_Fw(_Fy.b));},1));});}},_Fz=new T2(1,_70,_o),_FA=new T(function(){return B(unCStr("base"));}),_FB=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_FC=new T(function(){return B(unCStr("IOException"));}),_FD=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FA,_FB,_FC),_FE=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FD,_o,_o),_FF=function(_FG){return E(_FE);},_FH=function(_FI){var _FJ=E(_FI);return new F(function(){return _28(B(_26(_FJ.a)),_FF,_FJ.b);});},_FK=new T(function(){return B(unCStr(": "));}),_FL=new T(function(){return B(unCStr(")"));}),_FM=new T(function(){return B(unCStr(" ("));}),_FN=new T(function(){return B(unCStr("interrupted"));}),_FO=new T(function(){return B(unCStr("resource vanished"));}),_FP=new T(function(){return B(unCStr("unsatisified constraints"));}),_FQ=new T(function(){return B(unCStr("user error"));}),_FR=new T(function(){return B(unCStr("permission denied"));}),_FS=new T(function(){return B(unCStr("illegal operation"));}),_FT=new T(function(){return B(unCStr("end of file"));}),_FU=new T(function(){return B(unCStr("resource exhausted"));}),_FV=new T(function(){return B(unCStr("resource busy"));}),_FW=new T(function(){return B(unCStr("does not exist"));}),_FX=new T(function(){return B(unCStr("already exists"));}),_FY=new T(function(){return B(unCStr("timeout"));}),_FZ=new T(function(){return B(unCStr("unsupported operation"));}),_G0=new T(function(){return B(unCStr("hardware fault"));}),_G1=new T(function(){return B(unCStr("inappropriate type"));}),_G2=new T(function(){return B(unCStr("invalid argument"));}),_G3=new T(function(){return B(unCStr("failed"));}),_G4=new T(function(){return B(unCStr("protocol error"));}),_G5=new T(function(){return B(unCStr("system error"));}),_G6=function(_G7,_G8){switch(E(_G7)){case 0:return new F(function(){return _f(_FX,_G8);});break;case 1:return new F(function(){return _f(_FW,_G8);});break;case 2:return new F(function(){return _f(_FV,_G8);});break;case 3:return new F(function(){return _f(_FU,_G8);});break;case 4:return new F(function(){return _f(_FT,_G8);});break;case 5:return new F(function(){return _f(_FS,_G8);});break;case 6:return new F(function(){return _f(_FR,_G8);});break;case 7:return new F(function(){return _f(_FQ,_G8);});break;case 8:return new F(function(){return _f(_FP,_G8);});break;case 9:return new F(function(){return _f(_G5,_G8);});break;case 10:return new F(function(){return _f(_G4,_G8);});break;case 11:return new F(function(){return _f(_G3,_G8);});break;case 12:return new F(function(){return _f(_G2,_G8);});break;case 13:return new F(function(){return _f(_G1,_G8);});break;case 14:return new F(function(){return _f(_G0,_G8);});break;case 15:return new F(function(){return _f(_FZ,_G8);});break;case 16:return new F(function(){return _f(_FY,_G8);});break;case 17:return new F(function(){return _f(_FO,_G8);});break;default:return new F(function(){return _f(_FN,_G8);});}},_G9=new T(function(){return B(unCStr("}"));}),_Ga=new T(function(){return B(unCStr("{handle: "));}),_Gb=function(_Gc,_Gd,_Ge,_Gf,_Gg,_Gh){var _Gi=new T(function(){var _Gj=new T(function(){var _Gk=new T(function(){var _Gl=E(_Gf);if(!_Gl._){return E(_Gh);}else{var _Gm=new T(function(){return B(_f(_Gl,new T(function(){return B(_f(_FL,_Gh));},1)));},1);return B(_f(_FM,_Gm));}},1);return B(_G6(_Gd,_Gk));}),_Gn=E(_Ge);if(!_Gn._){return E(_Gj);}else{return B(_f(_Gn,new T(function(){return B(_f(_FK,_Gj));},1)));}}),_Go=E(_Gg);if(!_Go._){var _Gp=E(_Gc);if(!_Gp._){return E(_Gi);}else{var _Gq=E(_Gp.a);if(!_Gq._){var _Gr=new T(function(){var _Gs=new T(function(){return B(_f(_G9,new T(function(){return B(_f(_FK,_Gi));},1)));},1);return B(_f(_Gq.a,_Gs));},1);return new F(function(){return _f(_Ga,_Gr);});}else{var _Gt=new T(function(){var _Gu=new T(function(){return B(_f(_G9,new T(function(){return B(_f(_FK,_Gi));},1)));},1);return B(_f(_Gq.a,_Gu));},1);return new F(function(){return _f(_Ga,_Gt);});}}}else{return new F(function(){return _f(_Go.a,new T(function(){return B(_f(_FK,_Gi));},1));});}},_Gv=function(_Gw){var _Gx=E(_Gw);return new F(function(){return _Gb(_Gx.a,_Gx.b,_Gx.c,_Gx.d,_Gx.f,_o);});},_Gy=function(_Gz,_GA,_GB){var _GC=E(_GA);return new F(function(){return _Gb(_GC.a,_GC.b,_GC.c,_GC.d,_GC.f,_GB);});},_GD=function(_GE,_GF){var _GG=E(_GE);return new F(function(){return _Gb(_GG.a,_GG.b,_GG.c,_GG.d,_GG.f,_GF);});},_GH=function(_GI,_GJ){return new F(function(){return _2B(_GD,_GI,_GJ);});},_GK=new T3(0,_Gy,_Gv,_GH),_GL=new T(function(){return new T5(0,_FF,_GK,_GM,_FH,_Gv);}),_GM=function(_GN){return new T2(0,_GL,_GN);},_GO=__Z,_GP=7,_GQ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:85:7-13"));}),_GR=new T6(0,_GO,_GP,_o,_GQ,_GO,_GO),_GS=new T(function(){return B(_GM(_GR));}),_GT=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:86:7-13"));}),_GU=new T6(0,_GO,_GP,_o,_GT,_GO,_GO),_GV=new T(function(){return B(_GM(_GU));}),_GW=new T2(1,_o,_o),_GX=new T(function(){return B(unCStr(")"));}),_GY=function(_GZ,_H0){var _H1=new T(function(){var _H2=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_za(0,_H0,_o)),_GX));})));},1);return B(_f(B(_za(0,_GZ,_o)),_H2));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_H1)));});},_H3=function(_H4,_){var _H5=B(_B1(_AA,_C7,_Fg,_H4)),_H6=_H5.c,_H7=_H5.d,_H8=E(_H5.a),_H9=E(_H5.b);if(_H8<=_H9){var _Ha=function(_Hb,_Hc,_){if(_Hb<=_H9){var _Hd=E(_Hc),_He=function(_Hf,_Hg,_Hh,_Hi,_Hj,_){if(_Hg>_Hb){return new F(function(){return die(_GS);});}else{if(_Hb>_Hh){return new F(function(){return die(_GS);});}else{if(_Hg>_Hf){return new F(function(){return die(_GV);});}else{if(_Hf>_Hh){return new F(function(){return die(_GV);});}else{var _Hk=new T(function(){var _Hl=new T(function(){var _Hm=_Hb-_Hg|0;if(0>_Hm){return B(_GY(_Hm,_Hi));}else{if(_Hm>=_Hi){return B(_GY(_Hm,_Hi));}else{return E(_Hj[_Hm]);}}}),_Hn=new T(function(){var _Ho=_Hf-_Hg|0;if(0>_Ho){return B(_GY(_Ho,_Hi));}else{if(_Ho>=_Hi){return B(_GY(_Ho,_Hi));}else{return E(_Hj[_Ho]);}}}),_Hp=new T(function(){return B(_DU(E(_Hn).i,new T(function(){return E(E(_Hl).h);})));}),_Hq=new T(function(){return B(_DU(E(_Hl).i,new T(function(){return E(E(_Hn).h);})));});return B(A3(_zz,_zt,new T2(1,function(_Hr){return new F(function(){return _Da(_Hq,_Hr);});},new T2(1,function(_Hs){return new F(function(){return _Da(_Hp,_Hs);});},_o)),_Fz));}),_Ht=B(_hb(new T2(1,_71,_Hk),0));if(_Hf!=_H9){var _Hu=B(_He(_Hf+1|0,_Hg,_Hh,_Hi,_Hj,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Hu).a);})),new T(function(){return E(E(_Hu).b);}));}else{return new T2(0,_GW,new T4(0,E(_Hg),E(_Hh),_Hi,_Hj));}}}}}},_Hv=B(_He(_Hb,E(_Hd.a),E(_Hd.b),_Hd.c,_Hd.d,_));if(_Hb!=_H9){var _Hw=B(_Ha(_Hb+1|0,new T(function(){return E(E(_Hv).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Fw(E(_Hv).a));}),new T(function(){return E(E(_Hw).a);})),new T(function(){return E(E(_Hw).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Fw(E(_Hv).a));}),_o),new T(function(){return E(E(_Hv).b);}));}}else{if(_Hb!=_H9){var _Hx=B(_Ha(_Hb+1|0,_Hc,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Hx).a);})),new T(function(){return E(E(_Hx).b);}));}else{return new T2(0,new T2(1,_o,_o),_Hc);}}},_Hy=function(_Hz,_HA,_HB,_HC,_HD,_){if(_Hz<=_H9){var _HE=function(_HF,_HG,_HH,_HI,_HJ,_){if(_HG>_Hz){return new F(function(){return die(_GS);});}else{if(_Hz>_HH){return new F(function(){return die(_GS);});}else{if(_HG>_HF){return new F(function(){return die(_GV);});}else{if(_HF>_HH){return new F(function(){return die(_GV);});}else{var _HK=new T(function(){var _HL=new T(function(){var _HM=_Hz-_HG|0;if(0>_HM){return B(_GY(_HM,_HI));}else{if(_HM>=_HI){return B(_GY(_HM,_HI));}else{return E(_HJ[_HM]);}}}),_HN=new T(function(){var _HO=_HF-_HG|0;if(0>_HO){return B(_GY(_HO,_HI));}else{if(_HO>=_HI){return B(_GY(_HO,_HI));}else{return E(_HJ[_HO]);}}}),_HP=new T(function(){return B(_DU(E(_HN).i,new T(function(){return E(E(_HL).h);})));}),_HQ=new T(function(){return B(_DU(E(_HL).i,new T(function(){return E(E(_HN).h);})));});return B(A3(_zz,_zt,new T2(1,function(_HR){return new F(function(){return _Da(_HQ,_HR);});},new T2(1,function(_HS){return new F(function(){return _Da(_HP,_HS);});},_o)),_Fz));}),_HT=B(_hb(new T2(1,_71,_HK),0));if(_HF!=_H9){var _HU=B(_HE(_HF+1|0,_HG,_HH,_HI,_HJ,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_HU).a);})),new T(function(){return E(E(_HU).b);}));}else{return new T2(0,_GW,new T4(0,E(_HG),E(_HH),_HI,_HJ));}}}}}},_HV=B(_HE(_Hz,_HA,_HB,_HC,_HD,_));if(_Hz!=_H9){var _HW=B(_Ha(_Hz+1|0,new T(function(){return E(E(_HV).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Fw(E(_HV).a));}),new T(function(){return E(E(_HW).a);})),new T(function(){return E(E(_HW).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Fw(E(_HV).a));}),_o),new T(function(){return E(E(_HV).b);}));}}else{if(_Hz!=_H9){var _HX=B(_Hy(_Hz+1|0,_HA,_HB,_HC,_HD,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_HX).a);})),new T(function(){return E(E(_HX).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_HA),E(_HB),_HC,_HD));}}},_HY=B(_Hy(_H8,_H8,_H9,_H6,_H7,_)),_HZ=new T(function(){return B(_B1(_AA,_C7,_Fs,new T(function(){return E(E(_HY).b);})));});return new T2(0,_Bh,_HZ);}else{var _I0=new T(function(){var _I1=function(_){var _I2=function(_I3){if(_I3>=0){var _I4=newArr(_I3,_hh),_I5=_I4,_I6=E(_I3);if(!_I6){return new T4(0,E(_H8),E(_H9),0,_I5);}else{var _I7=_H6-1|0,_I8=function(_I9,_Ia,_){while(1){var _Ib=E(_I9);if(!_Ib._){return E(_);}else{var _=_I5[_Ia]=_Ib.a;if(_Ia!=(_I6-1|0)){var _Ic=_Ia+1|0;_I9=_Ib.b;_Ia=_Ic;continue;}else{return E(_);}}}};if(0<=_I7){var _Id=function(_Ie){return new T2(1,new T(function(){var _If=E(_H7[_Ie]),_Ig=B(_Dd(_If.a,_If.b,_If.c,_If.d,_If.e,_If.f));return {_:0,a:_Ig.a,b:_Ig.b,c:_Ig.c,d:_Ig.d,e:_Ig.e,f:_Ig.f,g:_Ig.g,h:_Ig.h,i:_Ig.i};}),new T(function(){if(_Ie!=_I7){return B(_Id(_Ie+1|0));}else{return __Z;}}));},_=B(_I8(B(_Id(0)),0,_));return new T4(0,E(_H8),E(_H9),_I6,_I5);}else{return new T4(0,E(_H8),E(_H9),_I6,_I5);}}}else{return E(_ye);}};if(_H8>_H9){return new F(function(){return _I2(0);});}else{return new F(function(){return _I2((_H9-_H8|0)+1|0);});}};return B(_yu(_I1));});return new T2(0,_Bh,_I0);}},_Ih=new T(function(){return eval("refresh");}),_Ii=function(_Ij,_){var _Ik=__app0(E(_Ih)),_Il=__app0(E(_BQ)),_Im=B(A(_B1,[_AA,_yX,_BO,_Ij,_])),_In=B(_H3(_Ij,_));return new T(function(){return E(E(_In).b);});},_Io=function(_Ip,_){while(1){var _Iq=E(_Ip);if(!_Iq._){return _Bh;}else{var _Ir=_Iq.b,_Is=E(_Iq.a);switch(_Is._){case 0:var _It=B(A1(_Is.a,_));_Ip=B(_f(_Ir,new T2(1,_It,_o)));continue;case 1:_Ip=B(_f(_Ir,_Is.a));continue;default:_Ip=_Ir;continue;}}}},_Iu=function(_Iv,_Iw,_){var _Ix=E(_Iv);switch(_Ix._){case 0:var _Iy=B(A1(_Ix.a,_));return new F(function(){return _Io(B(_f(_Iw,new T2(1,_Iy,_o))),_);});break;case 1:return new F(function(){return _Io(B(_f(_Iw,_Ix.a)),_);});break;default:return new F(function(){return _Io(_Iw,_);});}},_Iz=function(_IA,_IB,_IC){return new F(function(){return A1(_IA,function(_ID){return new F(function(){return A2(_IB,_ID,_IC);});});});},_IE=function(_IF,_IG,_IH){var _II=function(_IJ){var _IK=new T(function(){return B(A1(_IH,_IJ));});return new F(function(){return A1(_IG,function(_IL){return E(_IK);});});};return new F(function(){return A1(_IF,_II);});},_IM=function(_IN,_IO,_IP){var _IQ=new T(function(){return B(A1(_IO,function(_IR){return new F(function(){return A1(_IP,_IR);});}));});return new F(function(){return A1(_IN,function(_IS){return E(_IQ);});});},_IT=function(_IU,_IV,_IW){var _IX=function(_IY){var _IZ=function(_J0){return new F(function(){return A1(_IW,new T(function(){return B(A1(_IY,_J0));}));});};return new F(function(){return A1(_IV,_IZ);});};return new F(function(){return A1(_IU,_IX);});},_J1=function(_J2,_J3){return new F(function(){return A1(_J3,_J2);});},_J4=function(_J5,_J6,_J7){var _J8=new T(function(){return B(A1(_J7,_J5));});return new F(function(){return A1(_J6,function(_J9){return E(_J8);});});},_Ja=function(_Jb,_Jc,_Jd){var _Je=function(_Jf){return new F(function(){return A1(_Jd,new T(function(){return B(A1(_Jb,_Jf));}));});};return new F(function(){return A1(_Jc,_Je);});},_Jg=new T2(0,_Ja,_J4),_Jh=new T5(0,_Jg,_J1,_IT,_IM,_IE),_Ji=function(_Jj){return E(E(_Jj).b);},_Jk=function(_Jl,_Jm){return new F(function(){return A3(_Ji,_Jn,_Jl,function(_Jo){return E(_Jm);});});},_Jp=function(_Jq){return new F(function(){return err(_Jq);});},_Jn=new T(function(){return new T5(0,_Jh,_Iz,_Jk,_J1,_Jp);}),_Jr=function(_Js,_Jt){return new T1(0,function(_){return new F(function(){return _yM(_Jt,_Js,_);});});},_Ju=new T2(0,_Jn,_Jr),_Jv=function(_Jw){return new T0(2);},_Jx=function(_Jy){var _Jz=new T(function(){return B(A1(_Jy,_Jv));}),_JA=function(_JB){return new T1(1,new T2(1,new T(function(){return B(A1(_JB,_Bh));}),new T2(1,_Jz,_o)));};return E(_JA);},_JC=new T3(0,_Ju,_7S,_Jx),_JD=function(_){return new F(function(){return __jsNull();});},_JE=function(_JF){var _JG=B(A1(_JF,_));return E(_JG);},_JH=new T(function(){return B(_JE(_JD));}),_JI=new T(function(){return E(_JH);}),_JJ=new T0(2),_JK=function(_JL){return E(E(_JL).b);},_JM=function(_JN,_JO,_JP){var _JQ=function(_JR){var _JS=function(_){var _JT=E(_JO),_JU=rMV(_JT),_JV=E(_JU);if(!_JV._){var _JW=new T(function(){var _JX=new T(function(){return B(A1(_JR,_Bh));});return B(_f(_JV.b,new T2(1,new T2(0,_JP,function(_JY){return E(_JX);}),_o)));}),_=wMV(_JT,new T2(0,_JV.a,_JW));return _JJ;}else{var _JZ=E(_JV.a);if(!_JZ._){var _=wMV(_JT,new T2(0,_JP,_o));return new T(function(){return B(A1(_JR,_Bh));});}else{var _=wMV(_JT,new T1(1,_JZ.b));return new T1(1,new T2(1,new T(function(){return B(A1(_JR,_Bh));}),new T2(1,new T(function(){return B(A2(_JZ.a,_JP,_Jv));}),_o)));}}};return new T1(0,_JS);};return new F(function(){return A2(_JK,_JN,_JQ);});},_K0=new T(function(){return eval("window.requestAnimationFrame");}),_K1=new T1(1,_o),_K2=function(_K3,_K4){var _K5=function(_K6){var _K7=function(_){var _K8=E(_K4),_K9=rMV(_K8),_Ka=E(_K9);if(!_Ka._){var _Kb=_Ka.a,_Kc=E(_Ka.b);if(!_Kc._){var _=wMV(_K8,_K1);return new T(function(){return B(A1(_K6,_Kb));});}else{var _Kd=E(_Kc.a),_=wMV(_K8,new T2(0,_Kd.a,_Kc.b));return new T1(1,new T2(1,new T(function(){return B(A1(_K6,_Kb));}),new T2(1,new T(function(){return B(A1(_Kd.b,_Jv));}),_o)));}}else{var _Ke=new T(function(){var _Kf=function(_Kg){var _Kh=new T(function(){return B(A1(_K6,_Kg));});return function(_Ki){return E(_Kh);};};return B(_f(_Ka.a,new T2(1,_Kf,_o)));}),_=wMV(_K8,new T1(1,_Ke));return _JJ;}};return new T1(0,_K7);};return new F(function(){return A2(_JK,_K3,_K5);});},_Kj=function(_Kk,_Kl){var _Km=new T(function(){return B(A(_JM,[_JC,_Kk,_Bh,_Jv]));});return function(_){var _Kn=__createJSFunc(2,function(_Ko,_){var _Kp=B(_Iu(_Km,_o,_));return _JI;}),_Kq=__app1(E(_K0),_Kn);return new T(function(){return B(A3(_K2,_JC,_Kk,_Kl));});};},_Kr=new T1(1,_o),_Ks=function(_Kt,_Ku,_){var _Kv=function(_){var _Kw=nMV(_Kt),_Kx=_Kw;return new T(function(){var _Ky=new T(function(){return B(_Kz(_));}),_KA=function(_){var _KB=rMV(_Kx),_KC=B(A2(_Ku,_KB,_)),_=wMV(_Kx,_KC),_KD=function(_){var _KE=nMV(_Kr);return new T(function(){return new T1(0,B(_Kj(_KE,function(_KF){return E(_Ky);})));});};return new T1(0,_KD);},_KG=new T(function(){return new T1(0,_KA);}),_Kz=function(_KH){return E(_KG);};return B(_Kz(_));});};return new F(function(){return _Iu(new T1(0,_Kv),_o,_);});},_KI=function(_){var _KJ=__app2(E(_0),E(_7U),E(_ha));return new F(function(){return _Ks(_yx,_Ii,_);});},_KK=function(_){return new F(function(){return _KI(_);});};
var hasteMain = function() {B(A(_KK, [0]));};window.onload = hasteMain;