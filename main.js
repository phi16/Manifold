"use strict";
var __haste_prog_id = '18473cef95324e30040085b51bc98c81e939bee61ad57625a7de0140a4f60d70';
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
  return eval/* EXTERNAL */("compile");
}),
_1/* mappend */ = function(_2/* s374 */){
  return E(E(_2/* s374 */).b);
},
_3/* mempty */ = function(_4/* s36Z */){
  return E(E(_4/* s36Z */).a);
},
_5/* $fFoldableVar_$cfoldMap */ = function(_6/* s4vX */, _7/* s4vY */, _8/* s4vZ */){
  var _9/* s4w0 */ = E(_8/* s4vZ */);
  if(!_9/* s4w0 */._){
    return new F(function(){return A1(_7/* s4vY */,_9/* s4w0 */.a);});
  }else{
    var _a/* s4w3 */ = new T(function(){
      return B(_1/* GHC.Base.mappend */(_6/* s4vX */));
    }),
    _b/* s4w4 */ = new T(function(){
      return B(_3/* GHC.Base.mempty */(_6/* s4vX */));
    }),
    _c/* s4w5 */ = function(_d/* s4w6 */){
      var _e/* s4w7 */ = E(_d/* s4w6 */);
      if(!_e/* s4w7 */._){
        return E(_b/* s4w4 */);
      }else{
        return new F(function(){return A2(_a/* s4w3 */,new T(function(){
          return B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_6/* s4vX */, _7/* s4vY */, _e/* s4w7 */.a));
        }), new T(function(){
          return B(_c/* s4w5 */(_e/* s4w7 */.b));
        }));});
      }
    };
    return new F(function(){return _c/* s4w5 */(_9/* s4w0 */.a);});
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
_x/* $fFloatingVar_$c** */ = function(_y/* s4v8 */, _z/* s4v9 */){
  return new T1(1,new T2(1,_t/* Lib.Shader.$fFloatingVar31 */,new T2(1,_y/* s4v8 */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_z/* s4v9 */,_w/* Lib.Shader.gradStr3 */)))));
},
_A/* $fFloatingVar16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("acos("));
}),
_B/* $fFloatingVar15 */ = new T1(0,_A/* Lib.Shader.$fFloatingVar16 */),
_C/* $fFloatingVar_$cacos */ = function(_D/* s4uN */){
  return new T1(1,new T2(1,_B/* Lib.Shader.$fFloatingVar15 */,new T2(1,_D/* s4uN */,_w/* Lib.Shader.gradStr3 */)));
},
_E/* $fFloatingVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("acosh("));
}),
_F/* $fFloatingVar3 */ = new T1(0,_E/* Lib.Shader.$fFloatingVar4 */),
_G/* $fFloatingVar_$cacosh */ = function(_H/* s4uv */){
  return new T1(1,new T2(1,_F/* Lib.Shader.$fFloatingVar3 */,new T2(1,_H/* s4uv */,_w/* Lib.Shader.gradStr3 */)));
},
_I/* $fFloatingVar18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("asin("));
}),
_J/* $fFloatingVar17 */ = new T1(0,_I/* Lib.Shader.$fFloatingVar18 */),
_K/* $fFloatingVar_$casin */ = function(_L/* s4uQ */){
  return new T1(1,new T2(1,_J/* Lib.Shader.$fFloatingVar17 */,new T2(1,_L/* s4uQ */,_w/* Lib.Shader.gradStr3 */)));
},
_M/* $fFloatingVar6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("asinh("));
}),
_N/* $fFloatingVar5 */ = new T1(0,_M/* Lib.Shader.$fFloatingVar6 */),
_O/* $fFloatingVar_$casinh */ = function(_P/* s4uy */){
  return new T1(1,new T2(1,_N/* Lib.Shader.$fFloatingVar5 */,new T2(1,_P/* s4uy */,_w/* Lib.Shader.gradStr3 */)));
},
_Q/* $fFloatingVar14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("atan("));
}),
_R/* $fFloatingVar13 */ = new T1(0,_Q/* Lib.Shader.$fFloatingVar14 */),
_S/* $fFloatingVar_$catan */ = function(_T/* s4uK */){
  return new T1(1,new T2(1,_R/* Lib.Shader.$fFloatingVar13 */,new T2(1,_T/* s4uK */,_w/* Lib.Shader.gradStr3 */)));
},
_U/* $fFloatingVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("atanh("));
}),
_V/* $fFloatingVar1 */ = new T1(0,_U/* Lib.Shader.$fFloatingVar2 */),
_W/* $fFloatingVar_$catanh */ = function(_X/* s4us */){
  return new T1(1,new T2(1,_V/* Lib.Shader.$fFloatingVar1 */,new T2(1,_X/* s4us */,_w/* Lib.Shader.gradStr3 */)));
},
_Y/* $fFloatingVar22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("cos("));
}),
_Z/* $fFloatingVar21 */ = new T1(0,_Y/* Lib.Shader.$fFloatingVar22 */),
_10/* $fFloatingVar_$ccos */ = function(_11/* s4uW */){
  return new T1(1,new T2(1,_Z/* Lib.Shader.$fFloatingVar21 */,new T2(1,_11/* s4uW */,_w/* Lib.Shader.gradStr3 */)));
},
_12/* $fFloatingVar10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("cosh("));
}),
_13/* $fFloatingVar9 */ = new T1(0,_12/* Lib.Shader.$fFloatingVar10 */),
_14/* $fFloatingVar_$ccosh */ = function(_15/* s4uE */){
  return new T1(1,new T2(1,_13/* Lib.Shader.$fFloatingVar9 */,new T2(1,_15/* s4uE */,_w/* Lib.Shader.gradStr3 */)));
},
_16/* $fFloatingVar36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("exp("));
}),
_17/* $fFloatingVar35 */ = new T1(0,_16/* Lib.Shader.$fFloatingVar36 */),
_18/* $fFloatingVar_$cexp */ = function(_19/* s4vk */){
  return new T1(1,new T2(1,_17/* Lib.Shader.$fFloatingVar35 */,new T2(1,_19/* s4vk */,_w/* Lib.Shader.gradStr3 */)));
},
_1a/* $fFloatingVar28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("log("));
}),
_1b/* $fFloatingVar27 */ = new T1(0,_1a/* Lib.Shader.$fFloatingVar28 */),
_1c/* $fFloatingVar_$clog */ = function(_1d/* s4vh */){
  return new T1(1,new T2(1,_1b/* Lib.Shader.$fFloatingVar27 */,new T2(1,_1d/* s4vh */,_w/* Lib.Shader.gradStr3 */)));
},
_1e/* $fFloatingVar26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")/log("));
}),
_1f/* $fFloatingVar25 */ = new T1(0,_1e/* Lib.Shader.$fFloatingVar26 */),
_1g/* $fFloatingVar_$clogBase */ = function(_1h/* s4v2 */, _1i/* s4v3 */){
  return new T1(1,new T2(1,_1b/* Lib.Shader.$fFloatingVar27 */,new T2(1,_1i/* s4v3 */,new T2(1,_1f/* Lib.Shader.$fFloatingVar25 */,new T2(1,_1h/* s4v2 */,_w/* Lib.Shader.gradStr3 */)))));
},
_1j/* $fFloatingVar37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pi"));
}),
_1k/* $fFloatingVar_$cpi */ = new T1(0,_1j/* Lib.Shader.$fFloatingVar37 */),
_1l/* $fFloatingVar24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sin("));
}),
_1m/* $fFloatingVar23 */ = new T1(0,_1l/* Lib.Shader.$fFloatingVar24 */),
_1n/* $fFloatingVar_$csin */ = function(_1o/* s4uZ */){
  return new T1(1,new T2(1,_1m/* Lib.Shader.$fFloatingVar23 */,new T2(1,_1o/* s4uZ */,_w/* Lib.Shader.gradStr3 */)));
},
_1p/* $fFloatingVar12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sinh("));
}),
_1q/* $fFloatingVar11 */ = new T1(0,_1p/* Lib.Shader.$fFloatingVar12 */),
_1r/* $fFloatingVar_$csinh */ = function(_1s/* s4uH */){
  return new T1(1,new T2(1,_1q/* Lib.Shader.$fFloatingVar11 */,new T2(1,_1s/* s4uH */,_w/* Lib.Shader.gradStr3 */)));
},
_1t/* $fFloatingVar34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sqrt("));
}),
_1u/* $fFloatingVar33 */ = new T1(0,_1t/* Lib.Shader.$fFloatingVar34 */),
_1v/* $fFloatingVar_$csqrt */ = function(_1w/* s4ve */){
  return new T1(1,new T2(1,_1u/* Lib.Shader.$fFloatingVar33 */,new T2(1,_1w/* s4ve */,_w/* Lib.Shader.gradStr3 */)));
},
_1x/* $fFloatingVar20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tan("));
}),
_1y/* $fFloatingVar19 */ = new T1(0,_1x/* Lib.Shader.$fFloatingVar20 */),
_1z/* $fFloatingVar_$ctan */ = function(_1A/* s4uT */){
  return new T1(1,new T2(1,_1y/* Lib.Shader.$fFloatingVar19 */,new T2(1,_1A/* s4uT */,_w/* Lib.Shader.gradStr3 */)));
},
_1B/* $fFloatingVar8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tanh("));
}),
_1C/* $fFloatingVar7 */ = new T1(0,_1B/* Lib.Shader.$fFloatingVar8 */),
_1D/* $fFloatingVar_$ctanh */ = function(_1E/* s4uB */){
  return new T1(1,new T2(1,_1C/* Lib.Shader.$fFloatingVar7 */,new T2(1,_1E/* s4uB */,_w/* Lib.Shader.gradStr3 */)));
},
_1F/* $c+6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_1G/* $c+5 */ = new T1(0,_1F/* Lib.Shader.$c+6 */),
_1H/* $fFractionalVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")/("));
}),
_1I/* $fFractionalVar3 */ = new T1(0,_1H/* Lib.Shader.$fFractionalVar4 */),
_1J/* $fFractionalVar_$c/ */ = function(_1K/* s4um */, _1L/* s4un */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_1K/* s4um */,new T2(1,_1I/* Lib.Shader.$fFractionalVar3 */,new T2(1,_1L/* s4un */,_w/* Lib.Shader.gradStr3 */)))));
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
_6m/* $fFractionalVar_$cfromRational */ = function(_6n/* s4u7 */){
  return new T1(0,new T(function(){
    var _6o/* s4u8 */ = E(_6n/* s4u7 */),
    _6p/* s4ue */ = jsShow/* EXTERNAL */(B(_6j/* GHC.Float.rationalToDouble */(_6o/* s4u8 */.a, _6o/* s4u8 */.b)));
    return fromJSStr/* EXTERNAL */(_6p/* s4ue */);
  }));
},
_6q/* $fFractionalVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1./("));
}),
_6r/* $fFractionalVar1 */ = new T1(0,_6q/* Lib.Shader.$fFractionalVar2 */),
_6s/* $fFractionalVar_$crecip */ = function(_6t/* s4uj */){
  return new T1(1,new T2(1,_6r/* Lib.Shader.$fFractionalVar1 */,new T2(1,_6t/* s4uj */,_w/* Lib.Shader.gradStr3 */)));
},
_6u/* $c+4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")+("));
}),
_6v/* $c+3 */ = new T1(0,_6u/* Lib.Shader.$c+4 */),
_6w/* $c+ */ = function(_6x/* s4tY */, _6y/* s4tZ */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_6x/* s4tY */,new T2(1,_6v/* Lib.Shader.$c+3 */,new T2(1,_6y/* s4tZ */,_w/* Lib.Shader.gradStr3 */)))));
},
_6z/* $cnegate2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("-("));
}),
_6A/* $cnegate1 */ = new T1(0,_6z/* Lib.Shader.$cnegate2 */),
_6B/* $cnegate */ = function(_6C/* s4tP */){
  return new T1(1,new T2(1,_6A/* Lib.Shader.$cnegate1 */,new T2(1,_6C/* s4tP */,_w/* Lib.Shader.gradStr3 */)));
},
_6D/* $fNumVar6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")*("));
}),
_6E/* $fNumVar5 */ = new T1(0,_6D/* Lib.Shader.$fNumVar6 */),
_6F/* $fNumVar_$c* */ = function(_6G/* s4tS */, _6H/* s4tT */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_6G/* s4tS */,new T2(1,_6E/* Lib.Shader.$fNumVar5 */,new T2(1,_6H/* s4tT */,_w/* Lib.Shader.gradStr3 */)))));
},
_6I/* + */ = function(_6J/* s6Fw */){
  return E(E(_6J/* s6Fw */).a);
},
_6K/* negate */ = function(_6L/* s6FX */){
  return E(E(_6L/* s6FX */).d);
},
_6M/* $fNumVar_$c- */ = function(_6N/* s4u4 */, _6O/* s4u5 */){
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_6P/* Lib.Shader.$fNumVar */, _6N/* s4u4 */, new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_6P/* Lib.Shader.$fNumVar */, _6O/* s4u5 */));
  }));});
},
_6Q/* $fNumVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("abs("));
}),
_6R/* $fNumVar3 */ = new T1(0,_6Q/* Lib.Shader.$fNumVar4 */),
_6S/* $fNumVar_$cabs */ = function(_6T/* s4tM */){
  return new T1(1,new T2(1,_6R/* Lib.Shader.$fNumVar3 */,new T2(1,_6T/* s4tM */,_w/* Lib.Shader.gradStr3 */)));
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
_78/* $fNumVar_$cfromInteger */ = function(_79/* s4tG */){
  return new T1(0,new T(function(){
    return B(_f/* GHC.Base.++ */(B(_73/* GHC.Show.$w$cshowsPrec1 */(0, _79/* s4tG */, _o/* GHC.Types.[] */)), _77/* Lib.Shader.lvl4 */));
  }));
},
_7a/* $fNumVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sign("));
}),
_7b/* $fNumVar1 */ = new T1(0,_7a/* Lib.Shader.$fNumVar2 */),
_7c/* $fNumVar_$csignum */ = function(_7d/* s4tJ */){
  return new T1(1,new T2(1,_7b/* Lib.Shader.$fNumVar1 */,new T2(1,_7d/* s4tJ */,_w/* Lib.Shader.gradStr3 */)));
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
_7y/* $wfield */ = function(_7z/* sayW */, _7A/* sayX */, _7B/* sayY */, _7C/* sayZ */){
  var _7D/* saz0 */ = B(_7g/* GHC.Float.$p1Floating */(_7z/* sayW */)),
  _7E/* saz1 */ = B(_7i/* GHC.Real.$p1Fractional */(_7D/* saz0 */)),
  _7F/* sazb */ = new T(function(){
    var _7G/* saza */ = new T(function(){
      var _7H/* saz8 */ = new T(function(){
        var _7I/* saz2 */ = new T(function(){
          var _7J/* saz6 */ = new T(function(){
            var _7K/* saz5 */ = new T(function(){
              return B(A3(_6I/* GHC.Num.+ */,_7E/* saz1 */, new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_7E/* saz1 */, _7A/* sayX */, _7A/* sayX */));
              }), new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_7E/* saz1 */, _7C/* sayZ */, _7C/* sayZ */));
              })));
            });
            return B(A2(_7w/* GHC.Float.sqrt */,_7z/* sayW */, _7K/* saz5 */));
          });
          return B(A3(_7m/* GHC.Num.- */,_7E/* saz1 */, _7J/* saz6 */, new T(function(){
            return B(A2(_7o/* GHC.Real.fromRational */,_7D/* saz0 */, _7v/* Lib.World.gradient3 */));
          })));
        });
        return B(A3(_7k/* GHC.Num.* */,_7E/* saz1 */, _7I/* saz2 */, _7I/* saz2 */));
      });
      return B(A3(_6I/* GHC.Num.+ */,_7E/* saz1 */, _7H/* saz8 */, new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_7E/* saz1 */, _7B/* sayY */, _7B/* sayY */));
      })));
    });
    return B(A2(_7w/* GHC.Float.sqrt */,_7z/* sayW */, _7G/* saza */));
  });
  return new F(function(){return A3(_7m/* GHC.Num.- */,_7E/* saz1 */, _7F/* sazb */, new T(function(){
    return B(A2(_7o/* GHC.Real.fromRational */,_7D/* saz0 */, _7s/* Lib.World.gradient1 */));
  }));});
},
_7L/* fieldStr3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("z"));
}),
_7M/* fieldStr2 */ = new T1(0,_7L/* Lib.Shader.fieldStr3 */),
_7N/* fieldStr5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("y"));
}),
_7O/* fieldStr4 */ = new T1(0,_7N/* Lib.Shader.fieldStr5 */),
_7P/* fieldStr7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("x"));
}),
_7Q/* fieldStr6 */ = new T1(0,_7P/* Lib.Shader.fieldStr7 */),
_7R/* fieldStr1 */ = new T(function(){
  return B(_7y/* Lib.World.$wfield */(_7f/* Lib.Shader.$fFloatingVar */, _7Q/* Lib.Shader.fieldStr6 */, _7O/* Lib.Shader.fieldStr4 */, _7M/* Lib.Shader.fieldStr2 */));
}),
_7S/* id */ = function(_7T/* s3aG */){
  return E(_7T/* s3aG */);
},
_7U/* fieldStr */ = new T(function(){
  return toJSStr/* EXTERNAL */(B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_p/* GHC.Base.$fMonoid[] */, _7S/* GHC.Base.id */, _7R/* Lib.Shader.fieldStr1 */)));
}),
_7V/* $fFoldableVar_$s$cfoldMap */ = function(_7W/* s4vL */, _7X/* s4vM */, _7Y/* s4vN */){
  var _7Z/* s4vO */ = new T(function(){
    return B(_1/* GHC.Base.mappend */(_7W/* s4vL */));
  }),
  _80/* s4vP */ = new T(function(){
    return B(_3/* GHC.Base.mempty */(_7W/* s4vL */));
  }),
  _81/* s4vQ */ = function(_82/* s4vR */){
    var _83/* s4vS */ = E(_82/* s4vR */);
    if(!_83/* s4vS */._){
      return E(_80/* s4vP */);
    }else{
      return new F(function(){return A2(_7Z/* s4vO */,new T(function(){
        return B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_7W/* s4vL */, _7X/* s4vM */, _83/* s4vS */.a));
      }), new T(function(){
        return B(_81/* s4vQ */(_83/* s4vS */.b));
      }));});
    }
  };
  return new F(function(){return _81/* s4vQ */(_7Y/* s4vN */);});
},
_84/* argument */ = new T3(0,_7Q/* Lib.Shader.fieldStr6 */,_7O/* Lib.Shader.fieldStr4 */,_7M/* Lib.Shader.fieldStr2 */),
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
_8m/* $fOrdVar_$cmax */ = function(_8n/* s4vt */, _8o/* s4vu */){
  return new T1(1,new T2(1,_8l/* Lib.Shader.$fOrdVar3 */,new T2(1,_8n/* s4vt */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_8o/* s4vu */,_w/* Lib.Shader.gradStr3 */)))));
},
_8p/* $fOrdVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("min("));
}),
_8q/* $fOrdVar1 */ = new T1(0,_8p/* Lib.Shader.$fOrdVar2 */),
_8r/* $fOrdVar_$cmin */ = function(_8s/* s4vn */, _8t/* s4vo */){
  return new T1(1,new T2(1,_8q/* Lib.Shader.$fOrdVar1 */,new T2(1,_8s/* s4vn */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_8t/* s4vo */,_w/* Lib.Shader.gradStr3 */)))));
},
_8u/* $fOrdVar */ = {_:0,a:_89/* Lib.Shader.$fEqVar */,b:_8j/* Lib.Shader.$fOrdVar_$ccompare */,c:_8b/* Lib.Shader.$fOrdVar_$c< */,d:_8d/* Lib.Shader.$fOrdVar_$c<= */,e:_8f/* Lib.Shader.$fOrdVar_$c> */,f:_8h/* Lib.Shader.$fOrdVar_$c>= */,g:_8m/* Lib.Shader.$fOrdVar_$cmax */,h:_8r/* Lib.Shader.$fOrdVar_$cmin */},
_8v/* gradStr7 */ = new T2(0,_7f/* Lib.Shader.$fFloatingVar */,_8u/* Lib.Shader.$fOrdVar */),
_8w/* $fApplicativeWorld_$c*> */ = function(_8x/* saHD */, _8y/* saHE */){
  var _8z/* saHF */ = E(_8x/* saHD */);
  return E(_8y/* saHE */);
},
_8A/* $fApplicativeWorld_$c<*> */ = function(_8B/* sazm */, _8C/* sazn */){
  var _8D/* sazo */ = E(_8B/* sazm */),
  _8E/* sazs */ = E(_8C/* sazn */);
  return new T3(0,new T(function(){
    return B(A1(_8D/* sazo */.a,_8E/* sazs */.a));
  }),new T(function(){
    return B(A1(_8D/* sazo */.b,_8E/* sazs */.b));
  }),new T(function(){
    return B(A1(_8D/* sazo */.c,_8E/* sazs */.c));
  }));
},
_8F/* $fApplicativeWorld_$cpure */ = function(_8G/* sazz */){
  return new T3(0,_8G/* sazz */,_8G/* sazz */,_8G/* sazz */);
},
_8H/* $fFunctorWorld_$c<$ */ = function(_8I/* saHx */, _8J/* saHy */){
  var _8K/* saHz */ = E(_8J/* saHy */);
  return new T3(0,_8I/* saHx */,_8I/* saHx */,_8I/* saHx */);
},
_8L/* $fFunctorWorld_$cfmap */ = function(_8M/* saHJ */, _8N/* saHK */){
  var _8O/* saHL */ = E(_8N/* saHK */);
  return new T3(0,new T(function(){
    return B(A1(_8M/* saHJ */,_8O/* saHL */.a));
  }),new T(function(){
    return B(A1(_8M/* saHJ */,_8O/* saHL */.b));
  }),new T(function(){
    return B(A1(_8M/* saHJ */,_8O/* saHL */.c));
  }));
},
_8P/* $fFunctorWorld */ = new T2(0,_8L/* Lib.World.$fFunctorWorld_$cfmap */,_8H/* Lib.World.$fFunctorWorld_$c<$ */),
_8Q/* a1 */ = function(_8R/* saHS */, _8S/* saHT */){
  var _8T/* saHU */ = E(_8R/* saHS */),
  _8U/* saHY */ = E(_8S/* saHT */);
  return new T3(0,_8T/* saHU */.a,_8T/* saHU */.b,_8T/* saHU */.c);
},
_8V/* $fApplicativeWorld */ = new T5(0,_8P/* Lib.World.$fFunctorWorld */,_8F/* Lib.World.$fApplicativeWorld_$cpure */,_8A/* Lib.World.$fApplicativeWorld_$c<*> */,_8w/* Lib.World.$fApplicativeWorld_$c*> */,_8Q/* Lib.World.a1 */),
_8W/* $fArithWorld1 */ = new T1(0,0),
_8X/* fromInteger */ = function(_8Y/* s6Go */){
  return E(E(_8Y/* s6Go */).g);
},
_8Z/* $w$cbasis */ = function(_90/* saAO */){
  return new T3(0,new T3(0,new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _7q/* Lib.World.$fArithWorld2 */));
  }),new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _8W/* Lib.World.$fArithWorld1 */));
  }),new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _8W/* Lib.World.$fArithWorld1 */));
  })),new T3(0,new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _8W/* Lib.World.$fArithWorld1 */));
  }),new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _7q/* Lib.World.$fArithWorld2 */));
  }),new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _8W/* Lib.World.$fArithWorld1 */));
  })),new T3(0,new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _8W/* Lib.World.$fArithWorld1 */));
  }),new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _8W/* Lib.World.$fArithWorld1 */));
  }),new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_90/* saAO */, _7q/* Lib.World.$fArithWorld2 */));
  })));
},
_91/* $fArithWorld_$cbasis */ = function(_92/* saB1 */){
  var _93/* saB2 */ = B(_8Z/* Lib.World.$w$cbasis */(_92/* saB1 */));
  return new T3(0,_93/* saB2 */.a,_93/* saB2 */.b,_93/* saB2 */.c);
},
_94/* $p1Applicative */ = function(_95/* s35t */){
  return E(E(_95/* s35t */).a);
},
_96/* ** */ = function(_97/* s1kp8 */){
  return E(E(_97/* s1kp8 */).f);
},
_98/* / */ = function(_99/* sv9B */){
  return E(E(_99/* sv9B */).b);
},
_9a/* <*> */ = function(_9b/* s35H */){
  return E(E(_9b/* s35H */).c);
},
_9c/* fmap */ = function(_9d/* s35l */){
  return E(E(_9d/* s35l */).a);
},
_9e/* log */ = function(_9f/* s1kos */){
  return E(E(_9f/* s1kos */).d);
},
_9g/* $w$c** */ = function(_9h/* s5RP */, _9i/* s5RQ */, _9j/* s5RR */, _9k/* s5RS */, _9l/* s5RT */){
  var _9m/* s5RU */ = new T(function(){
    return E(E(E(_9h/* s5RP */).c).a);
  }),
  _9n/* s5Sk */ = new T(function(){
    var _9o/* s5S4 */ = E(_9h/* s5RP */).a,
    _9p/* s5Sj */ = new T(function(){
      var _9q/* s5S7 */ = new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_9m/* s5RU */));
      }),
      _9r/* s5S8 */ = new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(_9q/* s5S7 */));
      }),
      _9s/* s5S9 */ = new T(function(){
        return B(A2(_9e/* GHC.Float.log */,_9m/* s5RU */, _9i/* s5RQ */));
      }),
      _9t/* s5Sa */ = new T(function(){
        return B(A3(_96/* GHC.Float.** */,_9m/* s5RU */, _9i/* s5RQ */, _9k/* s5RS */));
      }),
      _9u/* s5Si */ = function(_9v/* s5Sc */, _9w/* s5Sd */){
        var _9x/* s5Sh */ = new T(function(){
          var _9y/* s5Sf */ = new T(function(){
            return B(A3(_98/* GHC.Real./ */,_9q/* s5S7 */, new T(function(){
              return B(A3(_7k/* GHC.Num.* */,_9r/* s5S8 */, _9k/* s5RS */, _9v/* s5Sc */));
            }), _9i/* s5RQ */));
          });
          return B(A3(_6I/* GHC.Num.+ */,_9r/* s5S8 */, _9y/* s5Sf */, new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_9r/* s5S8 */, _9w/* s5Sd */, _9s/* s5S9 */));
          })));
        });
        return new F(function(){return A3(_7k/* GHC.Num.* */,_9r/* s5S8 */, _9t/* s5Sa */, _9x/* s5Sh */);});
      };
      return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(_9o/* s5S4 */)), _9u/* s5Si */, _9j/* s5RR */));
    });
    return B(A3(_9a/* GHC.Base.<*> */,_9o/* s5S4 */, _9p/* s5Sj */, _9l/* s5RT */));
  });
  return new T2(0,new T(function(){
    return B(A3(_96/* GHC.Float.** */,_9m/* s5RU */, _9i/* s5RQ */, _9k/* s5RS */));
  }),_9n/* s5Sk */);
},
_9z/* $fFloatingExpr_$c** */ = function(_9A/* s5Sl */, _9B/* s5Sm */, _9C/* s5Sn */, _9D/* s5So */){
  var _9E/* s5Sp */ = E(_9C/* s5Sn */),
  _9F/* s5Ss */ = E(_9D/* s5So */),
  _9G/* s5Sv */ = B(_9g/* Lib.AD.$w$c** */(_9B/* s5Sm */, _9E/* s5Sp */.a, _9E/* s5Sp */.b, _9F/* s5Ss */.a, _9F/* s5Ss */.b));
  return new T2(0,_9G/* s5Sv */.a,_9G/* s5Sv */.b);
},
_9H/* $fFloatingExpr1 */ = new T1(0,1),
_9I/* acos */ = function(_9J/* s1kra */){
  return E(E(_9J/* s1kra */).l);
},
_9K/* $w$cacos */ = function(_9L/* s5P6 */, _9M/* s5P7 */, _9N/* s5P8 */){
  var _9O/* s5P9 */ = new T(function(){
    return E(E(E(_9L/* s5P6 */).c).a);
  }),
  _9P/* s5Pw */ = new T(function(){
    var _9Q/* s5Pn */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_9O/* s5P9 */));
    }),
    _9R/* s5Po */ = new T(function(){
      var _9S/* s5Pp */ = B(_7i/* GHC.Real.$p1Fractional */(_9Q/* s5Pn */)),
      _9T/* s5Pt */ = new T(function(){
        var _9U/* s5Ps */ = new T(function(){
          return B(A3(_7m/* GHC.Num.- */,_9S/* s5Pp */, new T(function(){
            return B(A2(_8X/* GHC.Num.fromInteger */,_9S/* s5Pp */, _9H/* Lib.AD.$fFloatingExpr1 */));
          }), new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_9S/* s5Pp */, _9M/* s5P7 */, _9M/* s5P7 */));
          })));
        });
        return B(A2(_7w/* GHC.Float.sqrt */,_9O/* s5P9 */, _9U/* s5Ps */));
      });
      return B(A2(_6K/* GHC.Num.negate */,_9S/* s5Pp */, _9T/* s5Pt */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_9L/* s5P6 */).a)), function(_9V/* s5Pu */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_9Q/* s5Pn */, _9V/* s5Pu */, _9R/* s5Po */);});
    }, _9N/* s5P8 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_9I/* GHC.Float.acos */,_9O/* s5P9 */, _9M/* s5P7 */));
  }),_9P/* s5Pw */);
},
_9W/* $fFloatingExpr_$cacos */ = function(_9X/* s5Px */, _9Y/* s5Py */, _9Z/* s5Pz */){
  var _a0/* s5PA */ = E(_9Z/* s5Pz */),
  _a1/* s5PD */ = B(_9K/* Lib.AD.$w$cacos */(_9Y/* s5Py */, _a0/* s5PA */.a, _a0/* s5PA */.b));
  return new T2(0,_a1/* s5PD */.a,_a1/* s5PD */.b);
},
_a2/* acosh */ = function(_a3/* s1ktc */){
  return E(E(_a3/* s1ktc */).r);
},
_a4/* $w$cacosh */ = function(_a5/* s5LR */, _a6/* s5LS */, _a7/* s5LT */){
  var _a8/* s5LU */ = new T(function(){
    return E(E(E(_a5/* s5LR */).c).a);
  }),
  _a9/* s5Mg */ = new T(function(){
    var _aa/* s5M8 */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_a8/* s5LU */));
    }),
    _ab/* s5M9 */ = new T(function(){
      var _ac/* s5Md */ = new T(function(){
        var _ad/* s5Ma */ = B(_7i/* GHC.Real.$p1Fractional */(_aa/* s5M8 */));
        return B(A3(_7m/* GHC.Num.- */,_ad/* s5Ma */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_ad/* s5Ma */, _a6/* s5LS */, _a6/* s5LS */));
        }), new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_ad/* s5Ma */, _9H/* Lib.AD.$fFloatingExpr1 */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_a8/* s5LU */, _ac/* s5Md */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_a5/* s5LR */).a)), function(_ae/* s5Me */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_aa/* s5M8 */, _ae/* s5Me */, _ab/* s5M9 */);});
    }, _a7/* s5LT */));
  });
  return new T2(0,new T(function(){
    return B(A2(_a2/* GHC.Float.acosh */,_a8/* s5LU */, _a6/* s5LS */));
  }),_a9/* s5Mg */);
},
_af/* $fFloatingExpr_$cacosh */ = function(_ag/* s5Mh */, _ah/* s5Mi */, _ai/* s5Mj */){
  var _aj/* s5Mk */ = E(_ai/* s5Mj */),
  _ak/* s5Mn */ = B(_a4/* Lib.AD.$w$cacosh */(_ah/* s5Mi */, _aj/* s5Mk */.a, _aj/* s5Mk */.b));
  return new T2(0,_ak/* s5Mn */.a,_ak/* s5Mn */.b);
},
_al/* asin */ = function(_am/* s1kqP */){
  return E(E(_am/* s1kqP */).k);
},
_an/* $w$casin */ = function(_ao/* s5PG */, _ap/* s5PH */, _aq/* s5PI */){
  var _ar/* s5PJ */ = new T(function(){
    return E(E(E(_ao/* s5PG */).c).a);
  }),
  _as/* s5Q5 */ = new T(function(){
    var _at/* s5PX */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_ar/* s5PJ */));
    }),
    _au/* s5PY */ = new T(function(){
      var _av/* s5Q2 */ = new T(function(){
        var _aw/* s5PZ */ = B(_7i/* GHC.Real.$p1Fractional */(_at/* s5PX */));
        return B(A3(_7m/* GHC.Num.- */,_aw/* s5PZ */, new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_aw/* s5PZ */, _9H/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_aw/* s5PZ */, _ap/* s5PH */, _ap/* s5PH */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_ar/* s5PJ */, _av/* s5Q2 */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_ao/* s5PG */).a)), function(_ax/* s5Q3 */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_at/* s5PX */, _ax/* s5Q3 */, _au/* s5PY */);});
    }, _aq/* s5PI */));
  });
  return new T2(0,new T(function(){
    return B(A2(_al/* GHC.Float.asin */,_ar/* s5PJ */, _ap/* s5PH */));
  }),_as/* s5Q5 */);
},
_ay/* $fFloatingExpr_$casin */ = function(_az/* s5Q6 */, _aA/* s5Q7 */, _aB/* s5Q8 */){
  var _aC/* s5Q9 */ = E(_aB/* s5Q8 */),
  _aD/* s5Qc */ = B(_an/* Lib.AD.$w$casin */(_aA/* s5Q7 */, _aC/* s5Q9 */.a, _aC/* s5Q9 */.b));
  return new T2(0,_aD/* s5Qc */.a,_aD/* s5Qc */.b);
},
_aE/* asinh */ = function(_aF/* s1ksR */){
  return E(E(_aF/* s1ksR */).q);
},
_aG/* $w$casinh */ = function(_aH/* s5Mq */, _aI/* s5Mr */, _aJ/* s5Ms */){
  var _aK/* s5Mt */ = new T(function(){
    return E(E(E(_aH/* s5Mq */).c).a);
  }),
  _aL/* s5MP */ = new T(function(){
    var _aM/* s5MH */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_aK/* s5Mt */));
    }),
    _aN/* s5MI */ = new T(function(){
      var _aO/* s5MM */ = new T(function(){
        var _aP/* s5MJ */ = B(_7i/* GHC.Real.$p1Fractional */(_aM/* s5MH */));
        return B(A3(_6I/* GHC.Num.+ */,_aP/* s5MJ */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_aP/* s5MJ */, _aI/* s5Mr */, _aI/* s5Mr */));
        }), new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_aP/* s5MJ */, _9H/* Lib.AD.$fFloatingExpr1 */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_aK/* s5Mt */, _aO/* s5MM */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_aH/* s5Mq */).a)), function(_aQ/* s5MN */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_aM/* s5MH */, _aQ/* s5MN */, _aN/* s5MI */);});
    }, _aJ/* s5Ms */));
  });
  return new T2(0,new T(function(){
    return B(A2(_aE/* GHC.Float.asinh */,_aK/* s5Mt */, _aI/* s5Mr */));
  }),_aL/* s5MP */);
},
_aR/* $fFloatingExpr_$casinh */ = function(_aS/* s5MQ */, _aT/* s5MR */, _aU/* s5MS */){
  var _aV/* s5MT */ = E(_aU/* s5MS */),
  _aW/* s5MW */ = B(_aG/* Lib.AD.$w$casinh */(_aT/* s5MR */, _aV/* s5MT */.a, _aV/* s5MT */.b));
  return new T2(0,_aW/* s5MW */.a,_aW/* s5MW */.b);
},
_aX/* atan */ = function(_aY/* s1krv */){
  return E(E(_aY/* s1krv */).m);
},
_aZ/* $w$catan */ = function(_b0/* s5Oy */, _b1/* s5Oz */, _b2/* s5OA */){
  var _b3/* s5OB */ = new T(function(){
    return E(E(E(_b0/* s5Oy */).c).a);
  }),
  _b4/* s5OW */ = new T(function(){
    var _b5/* s5OP */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_b3/* s5OB */));
    }),
    _b6/* s5OQ */ = new T(function(){
      var _b7/* s5OR */ = B(_7i/* GHC.Real.$p1Fractional */(_b5/* s5OP */));
      return B(A3(_6I/* GHC.Num.+ */,_b7/* s5OR */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_b7/* s5OR */, _9H/* Lib.AD.$fFloatingExpr1 */));
      }), new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_b7/* s5OR */, _b1/* s5Oz */, _b1/* s5Oz */));
      })));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_b0/* s5Oy */).a)), function(_b8/* s5OU */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_b5/* s5OP */, _b8/* s5OU */, _b6/* s5OQ */);});
    }, _b2/* s5OA */));
  });
  return new T2(0,new T(function(){
    return B(A2(_aX/* GHC.Float.atan */,_b3/* s5OB */, _b1/* s5Oz */));
  }),_b4/* s5OW */);
},
_b9/* $fFloatingExpr_$catan */ = function(_ba/* s5OX */, _bb/* s5OY */, _bc/* s5OZ */){
  var _bd/* s5P0 */ = E(_bc/* s5OZ */),
  _be/* s5P3 */ = B(_aZ/* Lib.AD.$w$catan */(_bb/* s5OY */, _bd/* s5P0 */.a, _bd/* s5P0 */.b));
  return new T2(0,_be/* s5P3 */.a,_be/* s5P3 */.b);
},
_bf/* atanh */ = function(_bg/* s1ktx */){
  return E(E(_bg/* s1ktx */).s);
},
_bh/* $w$catanh */ = function(_bi/* s5Lj */, _bj/* s5Lk */, _bk/* s5Ll */){
  var _bl/* s5Lm */ = new T(function(){
    return E(E(E(_bi/* s5Lj */).c).a);
  }),
  _bm/* s5LH */ = new T(function(){
    var _bn/* s5LA */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_bl/* s5Lm */));
    }),
    _bo/* s5LB */ = new T(function(){
      var _bp/* s5LC */ = B(_7i/* GHC.Real.$p1Fractional */(_bn/* s5LA */));
      return B(A3(_7m/* GHC.Num.- */,_bp/* s5LC */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_bp/* s5LC */, _9H/* Lib.AD.$fFloatingExpr1 */));
      }), new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_bp/* s5LC */, _bj/* s5Lk */, _bj/* s5Lk */));
      })));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_bi/* s5Lj */).a)), function(_bq/* s5LF */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_bn/* s5LA */, _bq/* s5LF */, _bo/* s5LB */);});
    }, _bk/* s5Ll */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bf/* GHC.Float.atanh */,_bl/* s5Lm */, _bj/* s5Lk */));
  }),_bm/* s5LH */);
},
_br/* $fFloatingExpr_$catanh */ = function(_bs/* s5LI */, _bt/* s5LJ */, _bu/* s5LK */){
  var _bv/* s5LL */ = E(_bu/* s5LK */),
  _bw/* s5LO */ = B(_bh/* Lib.AD.$w$catanh */(_bt/* s5LJ */, _bv/* s5LL */.a, _bv/* s5LL */.b));
  return new T2(0,_bw/* s5LO */.a,_bw/* s5LO */.b);
},
_bx/* cos */ = function(_by/* s1kq9 */){
  return E(E(_by/* s1kq9 */).i);
},
_bz/* sin */ = function(_bA/* s1kpO */){
  return E(E(_bA/* s1kpO */).h);
},
_bB/* $w$ccos */ = function(_bC/* s5QM */, _bD/* s5QN */, _bE/* s5QO */){
  var _bF/* s5QP */ = new T(function(){
    return E(E(E(_bC/* s5QM */).c).a);
  }),
  _bG/* s5R9 */ = new T(function(){
    var _bH/* s5R4 */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_bF/* s5QP */));
      })));
    }),
    _bI/* s5R5 */ = new T(function(){
      return B(A2(_6K/* GHC.Num.negate */,_bH/* s5R4 */, new T(function(){
        return B(A2(_bz/* GHC.Float.sin */,_bF/* s5QP */, _bD/* s5QN */));
      })));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_bC/* s5QM */).a)), function(_bJ/* s5R7 */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_bH/* s5R4 */, _bJ/* s5R7 */, _bI/* s5R5 */);});
    }, _bE/* s5QO */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bx/* GHC.Float.cos */,_bF/* s5QP */, _bD/* s5QN */));
  }),_bG/* s5R9 */);
},
_bK/* $fFloatingExpr_$ccos */ = function(_bL/* s5Ra */, _bM/* s5Rb */, _bN/* s5Rc */){
  var _bO/* s5Rd */ = E(_bN/* s5Rc */),
  _bP/* s5Rg */ = B(_bB/* Lib.AD.$w$ccos */(_bM/* s5Rb */, _bO/* s5Rd */.a, _bO/* s5Rd */.b));
  return new T2(0,_bP/* s5Rg */.a,_bP/* s5Rg */.b);
},
_bQ/* cosh */ = function(_bR/* s1ksb */){
  return E(E(_bR/* s1ksb */).o);
},
_bS/* sinh */ = function(_bT/* s1krQ */){
  return E(E(_bT/* s1krQ */).n);
},
_bU/* $w$ccosh */ = function(_bV/* s5Nw */, _bW/* s5Nx */, _bX/* s5Ny */){
  var _bY/* s5Nz */ = new T(function(){
    return E(E(E(_bV/* s5Nw */).c).a);
  }),
  _bZ/* s5NS */ = new T(function(){
    var _c0/* s5NO */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_bY/* s5Nz */));
      })));
    }),
    _c1/* s5NP */ = new T(function(){
      return B(A2(_bS/* GHC.Float.sinh */,_bY/* s5Nz */, _bW/* s5Nx */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_bV/* s5Nw */).a)), function(_c2/* s5NQ */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_c0/* s5NO */, _c2/* s5NQ */, _c1/* s5NP */);});
    }, _bX/* s5Ny */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bQ/* GHC.Float.cosh */,_bY/* s5Nz */, _bW/* s5Nx */));
  }),_bZ/* s5NS */);
},
_c3/* $fFloatingExpr_$ccosh */ = function(_c4/* s5NT */, _c5/* s5NU */, _c6/* s5NV */){
  var _c7/* s5NW */ = E(_c6/* s5NV */),
  _c8/* s5NZ */ = B(_bU/* Lib.AD.$w$ccosh */(_c5/* s5NU */, _c7/* s5NW */.a, _c7/* s5NW */.b));
  return new T2(0,_c8/* s5NZ */.a,_c8/* s5NZ */.b);
},
_c9/* exp */ = function(_ca/* s1ko7 */){
  return E(E(_ca/* s1ko7 */).c);
},
_cb/* $w$cexp */ = function(_cc/* s5TF */, _cd/* s5TG */, _ce/* s5TH */){
  var _cf/* s5TI */ = new T(function(){
    return E(E(E(_cc/* s5TF */).c).a);
  }),
  _cg/* s5U1 */ = new T(function(){
    var _ch/* s5TX */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_cf/* s5TI */));
      })));
    }),
    _ci/* s5TY */ = new T(function(){
      return B(A2(_c9/* GHC.Float.exp */,_cf/* s5TI */, _cd/* s5TG */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_cc/* s5TF */).a)), function(_cj/* s5TZ */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_ch/* s5TX */, _cj/* s5TZ */, _ci/* s5TY */);});
    }, _ce/* s5TH */));
  });
  return new T2(0,new T(function(){
    return B(A2(_c9/* GHC.Float.exp */,_cf/* s5TI */, _cd/* s5TG */));
  }),_cg/* s5U1 */);
},
_ck/* $fFloatingExpr_$cexp */ = function(_cl/* s5U2 */, _cm/* s5U3 */, _cn/* s5U4 */){
  var _co/* s5U5 */ = E(_cn/* s5U4 */),
  _cp/* s5U8 */ = B(_cb/* Lib.AD.$w$cexp */(_cm/* s5U3 */, _co/* s5U5 */.a, _co/* s5U5 */.b));
  return new T2(0,_cp/* s5U8 */.a,_cp/* s5U8 */.b);
},
_cq/* $w$clog */ = function(_cr/* s5T8 */, _cs/* s5T9 */, _ct/* s5Ta */){
  var _cu/* s5Tb */ = new T(function(){
    return E(E(E(_cr/* s5T8 */).c).a);
  }),
  _cv/* s5Tv */ = new T(function(){
    var _cw/* s5Tp */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_cu/* s5Tb */));
    }),
    _cx/* s5Tq */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_cw/* s5Tp */));
    }),
    _cy/* s5Tr */ = new T(function(){
      return B(A3(_98/* GHC.Real./ */,_cw/* s5Tp */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_cx/* s5Tq */, _9H/* Lib.AD.$fFloatingExpr1 */));
      }), _cs/* s5T9 */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_cr/* s5T8 */).a)), function(_cz/* s5Tt */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_cx/* s5Tq */, _cz/* s5Tt */, _cy/* s5Tr */);});
    }, _ct/* s5Ta */));
  });
  return new T2(0,new T(function(){
    return B(A2(_9e/* GHC.Float.log */,_cu/* s5Tb */, _cs/* s5T9 */));
  }),_cv/* s5Tv */);
},
_cA/* $fFloatingExpr_$clog */ = function(_cB/* s5Tw */, _cC/* s5Tx */, _cD/* s5Ty */){
  var _cE/* s5Tz */ = E(_cD/* s5Ty */),
  _cF/* s5TC */ = B(_cq/* Lib.AD.$w$clog */(_cC/* s5Tx */, _cE/* s5Tz */.a, _cE/* s5Tz */.b));
  return new T2(0,_cF/* s5TC */.a,_cF/* s5TC */.b);
},
_cG/* $fFloatingExpr_$clogBase */ = function(_cH/* s5Uy */, _cI/* s5Uz */, _cJ/* s5UA */, _cK/* s5UB */){
  var _cL/* s5UC */ = new T(function(){
    return E(E(_cI/* s5Uz */).c);
  }),
  _cM/* s5V0 */ = new T3(0,new T(function(){
    return E(E(_cI/* s5Uz */).a);
  }),new T(function(){
    return E(E(_cI/* s5Uz */).b);
  }),new T2(0,new T(function(){
    return E(E(_cL/* s5UC */).a);
  }),new T(function(){
    return E(E(_cL/* s5UC */).b);
  })));
  return new F(function(){return A3(_98/* GHC.Real./ */,_cH/* s5Uy */, new T(function(){
    var _cN/* s5V1 */ = E(_cK/* s5UB */),
    _cO/* s5V4 */ = B(_cq/* Lib.AD.$w$clog */(_cM/* s5V0 */, _cN/* s5V1 */.a, _cN/* s5V1 */.b));
    return new T2(0,_cO/* s5V4 */.a,_cO/* s5V4 */.b);
  }), new T(function(){
    var _cP/* s5V8 */ = E(_cJ/* s5UA */),
    _cQ/* s5Vb */ = B(_cq/* Lib.AD.$w$clog */(_cM/* s5V0 */, _cP/* s5V8 */.a, _cP/* s5V8 */.b));
    return new T2(0,_cQ/* s5Vb */.a,_cQ/* s5Vb */.b);
  }));});
},
_cR/* $fFloatingExpr3 */ = new T1(0,0),
_cS/* pi */ = function(_cT/* s1knM */){
  return E(E(_cT/* s1knM */).b);
},
_cU/* pure */ = function(_cV/* s35A */){
  return E(E(_cV/* s35A */).b);
},
_cW/* $w$cpi */ = function(_cX/* s5Ub */){
  var _cY/* s5Uc */ = new T(function(){
    return E(E(E(_cX/* s5Ub */).c).a);
  }),
  _cZ/* s5Us */ = new T(function(){
    return B(A2(_cU/* GHC.Base.pure */,E(_cX/* s5Ub */).a, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_cY/* s5Uc */)))), _cR/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(_cS/* GHC.Float.pi */(_cY/* s5Uc */));
  }),_cZ/* s5Us */);
},
_d0/* $fFloatingExpr_$cpi */ = function(_d1/* s5Ut */, _d2/* s5Uu */){
  var _d3/* s5Uv */ = B(_cW/* Lib.AD.$w$cpi */(_d2/* s5Uu */));
  return new T2(0,_d3/* s5Uv */.a,_d3/* s5Uv */.b);
},
_d4/* $w$csin */ = function(_d5/* s5Rj */, _d6/* s5Rk */, _d7/* s5Rl */){
  var _d8/* s5Rm */ = new T(function(){
    return E(E(E(_d5/* s5Rj */).c).a);
  }),
  _d9/* s5RF */ = new T(function(){
    var _da/* s5RB */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_d8/* s5Rm */));
      })));
    }),
    _db/* s5RC */ = new T(function(){
      return B(A2(_bx/* GHC.Float.cos */,_d8/* s5Rm */, _d6/* s5Rk */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_d5/* s5Rj */).a)), function(_dc/* s5RD */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_da/* s5RB */, _dc/* s5RD */, _db/* s5RC */);});
    }, _d7/* s5Rl */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bz/* GHC.Float.sin */,_d8/* s5Rm */, _d6/* s5Rk */));
  }),_d9/* s5RF */);
},
_dd/* $fFloatingExpr_$csin */ = function(_de/* s5RG */, _df/* s5RH */, _dg/* s5RI */){
  var _dh/* s5RJ */ = E(_dg/* s5RI */),
  _di/* s5RM */ = B(_d4/* Lib.AD.$w$csin */(_df/* s5RH */, _dh/* s5RJ */.a, _dh/* s5RJ */.b));
  return new T2(0,_di/* s5RM */.a,_di/* s5RM */.b);
},
_dj/* $w$csinh */ = function(_dk/* s5O2 */, _dl/* s5O3 */, _dm/* s5O4 */){
  var _dn/* s5O5 */ = new T(function(){
    return E(E(E(_dk/* s5O2 */).c).a);
  }),
  _do/* s5Oo */ = new T(function(){
    var _dp/* s5Ok */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_dn/* s5O5 */));
      })));
    }),
    _dq/* s5Ol */ = new T(function(){
      return B(A2(_bQ/* GHC.Float.cosh */,_dn/* s5O5 */, _dl/* s5O3 */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_dk/* s5O2 */).a)), function(_dr/* s5Om */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_dp/* s5Ok */, _dr/* s5Om */, _dq/* s5Ol */);});
    }, _dm/* s5O4 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bS/* GHC.Float.sinh */,_dn/* s5O5 */, _dl/* s5O3 */));
  }),_do/* s5Oo */);
},
_ds/* $fFloatingExpr_$csinh */ = function(_dt/* s5Op */, _du/* s5Oq */, _dv/* s5Or */){
  var _dw/* s5Os */ = E(_dv/* s5Or */),
  _dx/* s5Ov */ = B(_dj/* Lib.AD.$w$csinh */(_du/* s5Oq */, _dw/* s5Os */.a, _dw/* s5Os */.b));
  return new T2(0,_dx/* s5Ov */.a,_dx/* s5Ov */.b);
},
_dy/* $fFloatingExpr2 */ = new T1(0,2),
_dz/* $w$csqrt */ = function(_dA/* s5Sy */, _dB/* s5Sz */, _dC/* s5SA */){
  var _dD/* s5SB */ = new T(function(){
    return E(E(E(_dA/* s5Sy */).c).a);
  }),
  _dE/* s5SY */ = new T(function(){
    var _dF/* s5SP */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_dD/* s5SB */));
    }),
    _dG/* s5SQ */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_dF/* s5SP */));
    }),
    _dH/* s5SR */ = new T(function(){
      var _dI/* s5SU */ = new T(function(){
        return B(A3(_98/* GHC.Real./ */,_dF/* s5SP */, new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_dG/* s5SQ */, _9H/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_dG/* s5SQ */, _dy/* Lib.AD.$fFloatingExpr2 */));
        })));
      });
      return B(A3(_98/* GHC.Real./ */,_dF/* s5SP */, _dI/* s5SU */, new T(function(){
        return B(A2(_7w/* GHC.Float.sqrt */,_dD/* s5SB */, _dB/* s5Sz */));
      })));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_dA/* s5Sy */).a)), function(_dJ/* s5SW */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_dG/* s5SQ */, _dJ/* s5SW */, _dH/* s5SR */);});
    }, _dC/* s5SA */));
  });
  return new T2(0,new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_dD/* s5SB */, _dB/* s5Sz */));
  }),_dE/* s5SY */);
},
_dK/* $fFloatingExpr_$csqrt */ = function(_dL/* s5SZ */, _dM/* s5T0 */, _dN/* s5T1 */){
  var _dO/* s5T2 */ = E(_dN/* s5T1 */),
  _dP/* s5T5 */ = B(_dz/* Lib.AD.$w$csqrt */(_dM/* s5T0 */, _dO/* s5T2 */.a, _dO/* s5T2 */.b));
  return new T2(0,_dP/* s5T5 */.a,_dP/* s5T5 */.b);
},
_dQ/* tan */ = function(_dR/* s1kqu */){
  return E(E(_dR/* s1kqu */).j);
},
_dS/* $w$ctan */ = function(_dT/* s5Qf */, _dU/* s5Qg */, _dV/* s5Qh */){
  var _dW/* s5Qi */ = new T(function(){
    return E(E(E(_dT/* s5Qf */).c).a);
  }),
  _dX/* s5QC */ = new T(function(){
    var _dY/* s5Qw */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_dW/* s5Qi */));
    }),
    _dZ/* s5Qx */ = new T(function(){
      var _e0/* s5Qy */ = new T(function(){
        return B(A2(_bx/* GHC.Float.cos */,_dW/* s5Qi */, _dU/* s5Qg */));
      });
      return B(A3(_7k/* GHC.Num.* */,B(_7i/* GHC.Real.$p1Fractional */(_dY/* s5Qw */)), _e0/* s5Qy */, _e0/* s5Qy */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_dT/* s5Qf */).a)), function(_e1/* s5QA */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_dY/* s5Qw */, _e1/* s5QA */, _dZ/* s5Qx */);});
    }, _dV/* s5Qh */));
  });
  return new T2(0,new T(function(){
    return B(A2(_dQ/* GHC.Float.tan */,_dW/* s5Qi */, _dU/* s5Qg */));
  }),_dX/* s5QC */);
},
_e2/* $fFloatingExpr_$ctan */ = function(_e3/* s5QD */, _e4/* s5QE */, _e5/* s5QF */){
  var _e6/* s5QG */ = E(_e5/* s5QF */),
  _e7/* s5QJ */ = B(_dS/* Lib.AD.$w$ctan */(_e4/* s5QE */, _e6/* s5QG */.a, _e6/* s5QG */.b));
  return new T2(0,_e7/* s5QJ */.a,_e7/* s5QJ */.b);
},
_e8/* tanh */ = function(_e9/* s1ksw */){
  return E(E(_e9/* s1ksw */).p);
},
_ea/* $w$ctanh */ = function(_eb/* s5MZ */, _ec/* s5N0 */, _ed/* s5N1 */){
  var _ee/* s5N2 */ = new T(function(){
    return E(E(E(_eb/* s5MZ */).c).a);
  }),
  _ef/* s5Nm */ = new T(function(){
    var _eg/* s5Ng */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_ee/* s5N2 */));
    }),
    _eh/* s5Nh */ = new T(function(){
      var _ei/* s5Ni */ = new T(function(){
        return B(A2(_bQ/* GHC.Float.cosh */,_ee/* s5N2 */, _ec/* s5N0 */));
      });
      return B(A3(_7k/* GHC.Num.* */,B(_7i/* GHC.Real.$p1Fractional */(_eg/* s5Ng */)), _ei/* s5Ni */, _ei/* s5Ni */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_eb/* s5MZ */).a)), function(_ej/* s5Nk */){
      return new F(function(){return A3(_98/* GHC.Real./ */,_eg/* s5Ng */, _ej/* s5Nk */, _eh/* s5Nh */);});
    }, _ed/* s5N1 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_e8/* GHC.Float.tanh */,_ee/* s5N2 */, _ec/* s5N0 */));
  }),_ef/* s5Nm */);
},
_ek/* $fFloatingExpr_$ctanh */ = function(_el/* s5Nn */, _em/* s5No */, _en/* s5Np */){
  var _eo/* s5Nq */ = E(_en/* s5Np */),
  _ep/* s5Nt */ = B(_ea/* Lib.AD.$w$ctanh */(_em/* s5No */, _eo/* s5Nq */.a, _eo/* s5Nq */.b));
  return new T2(0,_ep/* s5Nt */.a,_ep/* s5Nt */.b);
},
_eq/* $fFloatingExpr */ = function(_er/* s5Vf */, _es/* s5Vg */){
  return {_:0,a:_er/* s5Vf */,b:new T(function(){
    return B(_d0/* Lib.AD.$fFloatingExpr_$cpi */(_er/* s5Vf */, _es/* s5Vg */));
  }),c:function(_et/* B1 */){
    return new F(function(){return _ck/* Lib.AD.$fFloatingExpr_$cexp */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },d:function(_et/* B1 */){
    return new F(function(){return _cA/* Lib.AD.$fFloatingExpr_$clog */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },e:function(_et/* B1 */){
    return new F(function(){return _dK/* Lib.AD.$fFloatingExpr_$csqrt */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },f:function(_eu/* B2 */, _et/* B1 */){
    return new F(function(){return _9z/* Lib.AD.$fFloatingExpr_$c** */(_er/* s5Vf */, _es/* s5Vg */, _eu/* B2 */, _et/* B1 */);});
  },g:function(_eu/* B2 */, _et/* B1 */){
    return new F(function(){return _cG/* Lib.AD.$fFloatingExpr_$clogBase */(_er/* s5Vf */, _es/* s5Vg */, _eu/* B2 */, _et/* B1 */);});
  },h:function(_et/* B1 */){
    return new F(function(){return _dd/* Lib.AD.$fFloatingExpr_$csin */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },i:function(_et/* B1 */){
    return new F(function(){return _bK/* Lib.AD.$fFloatingExpr_$ccos */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },j:function(_et/* B1 */){
    return new F(function(){return _e2/* Lib.AD.$fFloatingExpr_$ctan */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },k:function(_et/* B1 */){
    return new F(function(){return _ay/* Lib.AD.$fFloatingExpr_$casin */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },l:function(_et/* B1 */){
    return new F(function(){return _9W/* Lib.AD.$fFloatingExpr_$cacos */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },m:function(_et/* B1 */){
    return new F(function(){return _b9/* Lib.AD.$fFloatingExpr_$catan */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },n:function(_et/* B1 */){
    return new F(function(){return _ds/* Lib.AD.$fFloatingExpr_$csinh */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },o:function(_et/* B1 */){
    return new F(function(){return _c3/* Lib.AD.$fFloatingExpr_$ccosh */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },p:function(_et/* B1 */){
    return new F(function(){return _ek/* Lib.AD.$fFloatingExpr_$ctanh */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },q:function(_et/* B1 */){
    return new F(function(){return _aR/* Lib.AD.$fFloatingExpr_$casinh */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },r:function(_et/* B1 */){
    return new F(function(){return _af/* Lib.AD.$fFloatingExpr_$cacosh */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  },s:function(_et/* B1 */){
    return new F(function(){return _br/* Lib.AD.$fFloatingExpr_$catanh */(_er/* s5Vf */, _es/* s5Vg */, _et/* B1 */);});
  }};
},
_ev/* $w$c/ */ = function(_ew/* s5Kx */, _ex/* s5Ky */, _ey/* s5Kz */, _ez/* s5KA */, _eA/* s5KB */){
  var _eB/* s5KK */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_ew/* s5Kx */).c).a);
    })));
  }),
  _eC/* s5L0 */ = new T(function(){
    var _eD/* s5KN */ = E(_ew/* s5Kx */).a,
    _eE/* s5KZ */ = new T(function(){
      var _eF/* s5KQ */ = new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(_eB/* s5KK */));
      }),
      _eG/* s5KR */ = new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_eF/* s5KQ */, _ez/* s5KA */, _ez/* s5KA */));
      }),
      _eH/* s5KY */ = function(_eI/* s5KT */, _eJ/* s5KU */){
        var _eK/* s5KX */ = new T(function(){
          return B(A3(_7m/* GHC.Num.- */,_eF/* s5KQ */, new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_eF/* s5KQ */, _eI/* s5KT */, _ez/* s5KA */));
          }), new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_eF/* s5KQ */, _ex/* s5Ky */, _eJ/* s5KU */));
          })));
        });
        return new F(function(){return A3(_98/* GHC.Real./ */,_eB/* s5KK */, _eK/* s5KX */, _eG/* s5KR */);});
      };
      return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(_eD/* s5KN */)), _eH/* s5KY */, _ey/* s5Kz */));
    });
    return B(A3(_9a/* GHC.Base.<*> */,_eD/* s5KN */, _eE/* s5KZ */, _eA/* s5KB */));
  });
  return new T2(0,new T(function(){
    return B(A3(_98/* GHC.Real./ */,_eB/* s5KK */, _ex/* s5Ky */, _ez/* s5KA */));
  }),_eC/* s5L0 */);
},
_eL/* $fFractionalExpr_$c/ */ = function(_eM/* s5L1 */, _eN/* s5L2 */, _eO/* s5L3 */, _eP/* s5L4 */){
  var _eQ/* s5L5 */ = E(_eO/* s5L3 */),
  _eR/* s5L8 */ = E(_eP/* s5L4 */),
  _eS/* s5Lb */ = B(_ev/* Lib.AD.$w$c/ */(_eN/* s5L2 */, _eQ/* s5L5 */.a, _eQ/* s5L5 */.b, _eR/* s5L8 */.a, _eR/* s5L8 */.b));
  return new T2(0,_eS/* s5Lb */.a,_eS/* s5Lb */.b);
},
_eT/* $w$cfromRational */ = function(_eU/* s5Jy */, _eV/* s5Jz */){
  var _eW/* s5JI */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_eU/* s5Jy */).c).a);
    })));
  }),
  _eX/* s5JQ */ = new T(function(){
    return B(A2(_cU/* GHC.Base.pure */,E(_eU/* s5Jy */).a, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(_eW/* s5JI */)), _cR/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_7o/* GHC.Real.fromRational */,_eW/* s5JI */, _eV/* s5Jz */));
  }),_eX/* s5JQ */);
},
_eY/* $fFractionalExpr_$cfromRational */ = function(_eZ/* s5JR */, _f0/* s5JS */, _f1/* s5JT */){
  var _f2/* s5JU */ = B(_eT/* Lib.AD.$w$cfromRational */(_f0/* s5JS */, _f1/* s5JT */));
  return new T2(0,_f2/* s5JU */.a,_f2/* s5JU */.b);
},
_f3/* $w$crecip */ = function(_f4/* s5JX */, _f5/* s5JY */, _f6/* s5JZ */){
  var _f7/* s5K8 */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_f4/* s5JX */).c).a);
    })));
  }),
  _f8/* s5K9 */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(_f7/* s5K8 */));
  }),
  _f9/* s5Kn */ = new T(function(){
    var _fa/* s5Kh */ = new T(function(){
      var _fb/* s5Kk */ = new T(function(){
        return B(A3(_98/* GHC.Real./ */,_f7/* s5K8 */, new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_f8/* s5K9 */, _9H/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_f8/* s5K9 */, _f5/* s5JY */, _f5/* s5JY */));
        })));
      });
      return B(A2(_6K/* GHC.Num.negate */,_f8/* s5K9 */, _fb/* s5Kk */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_f4/* s5JX */).a)), function(_fc/* s5Kl */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_f8/* s5K9 */, _fc/* s5Kl */, _fa/* s5Kh */);});
    }, _f6/* s5JZ */));
  }),
  _fd/* s5Kb */ = new T(function(){
    return B(A3(_98/* GHC.Real./ */,_f7/* s5K8 */, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_f8/* s5K9 */, _9H/* Lib.AD.$fFloatingExpr1 */));
    }), _f5/* s5JY */));
  });
  return new T2(0,_fd/* s5Kb */,_f9/* s5Kn */);
},
_fe/* $fFractionalExpr_$crecip */ = function(_ff/* s5Ko */, _fg/* s5Kp */, _fh/* s5Kq */){
  var _fi/* s5Kr */ = E(_fh/* s5Kq */),
  _fj/* s5Ku */ = B(_f3/* Lib.AD.$w$crecip */(_fg/* s5Kp */, _fi/* s5Kr */.a, _fi/* s5Kr */.b));
  return new T2(0,_fj/* s5Ku */.a,_fj/* s5Ku */.b);
},
_fk/* $fFractionalExpr */ = function(_fl/* s5Le */, _fm/* s5Lf */){
  return new T4(0,_fl/* s5Le */,function(_eu/* B2 */, _et/* B1 */){
    return new F(function(){return _eL/* Lib.AD.$fFractionalExpr_$c/ */(_fl/* s5Le */, _fm/* s5Lf */, _eu/* B2 */, _et/* B1 */);});
  },function(_et/* B1 */){
    return new F(function(){return _fe/* Lib.AD.$fFractionalExpr_$crecip */(_fl/* s5Le */, _fm/* s5Lf */, _et/* B1 */);});
  },function(_et/* B1 */){
    return new F(function(){return _eY/* Lib.AD.$fFractionalExpr_$cfromRational */(_fl/* s5Le */, _fm/* s5Lf */, _et/* B1 */);});
  });
},
_fn/* $w$c* */ = function(_fo/* s5I7 */, _fp/* s5I8 */, _fq/* s5I9 */, _fr/* s5Ia */, _fs/* s5Ib */){
  var _ft/* s5Il */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_fo/* s5I7 */).c).a);
      })));
    })));
  }),
  _fu/* s5Iy */ = new T(function(){
    var _fv/* s5Io */ = E(_fo/* s5I7 */).a,
    _fw/* s5Ix */ = new T(function(){
      var _fx/* s5Iw */ = function(_fy/* s5Is */, _fz/* s5It */){
        return new F(function(){return A3(_6I/* GHC.Num.+ */,_ft/* s5Il */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_ft/* s5Il */, _fp/* s5I8 */, _fz/* s5It */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_ft/* s5Il */, _fy/* s5Is */, _fr/* s5Ia */));
        }));});
      };
      return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(_fv/* s5Io */)), _fx/* s5Iw */, _fq/* s5I9 */));
    });
    return B(A3(_9a/* GHC.Base.<*> */,_fv/* s5Io */, _fw/* s5Ix */, _fs/* s5Ib */));
  });
  return new T2(0,new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_ft/* s5Il */, _fp/* s5I8 */, _fr/* s5Ia */));
  }),_fu/* s5Iy */);
},
_fA/* $fNumExpr_$c* */ = function(_fB/* s5Iz */, _fC/* s5IA */, _fD/* s5IB */){
  var _fE/* s5IC */ = E(_fC/* s5IA */),
  _fF/* s5IF */ = E(_fD/* s5IB */),
  _fG/* s5II */ = B(_fn/* Lib.AD.$w$c* */(_fB/* s5Iz */, _fE/* s5IC */.a, _fE/* s5IC */.b, _fF/* s5IF */.a, _fF/* s5IF */.b));
  return new T2(0,_fG/* s5II */.a,_fG/* s5II */.b);
},
_fH/* $w$c+ */ = function(_fI/* s5IL */, _fJ/* s5IM */, _fK/* s5IN */, _fL/* s5IO */, _fM/* s5IP */){
  var _fN/* s5IZ */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_fI/* s5IL */).c).a);
      })));
    })));
  }),
  _fO/* s5J8 */ = new T(function(){
    var _fP/* s5J2 */ = E(_fI/* s5IL */).a,
    _fQ/* s5J7 */ = new T(function(){
      return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(_fP/* s5J2 */)), new T(function(){
        return B(_6I/* GHC.Num.+ */(_fN/* s5IZ */));
      }), _fK/* s5IN */));
    });
    return B(A3(_9a/* GHC.Base.<*> */,_fP/* s5J2 */, _fQ/* s5J7 */, _fM/* s5IP */));
  });
  return new T2(0,new T(function(){
    return B(A3(_6I/* GHC.Num.+ */,_fN/* s5IZ */, _fJ/* s5IM */, _fL/* s5IO */));
  }),_fO/* s5J8 */);
},
_fR/* $fNumExpr_$c+ */ = function(_fS/* s5J9 */, _fT/* s5Ja */, _fU/* s5Jb */){
  var _fV/* s5Jc */ = E(_fT/* s5Ja */),
  _fW/* s5Jf */ = E(_fU/* s5Jb */),
  _fX/* s5Ji */ = B(_fH/* Lib.AD.$w$c+ */(_fS/* s5J9 */, _fV/* s5Jc */.a, _fV/* s5Jc */.b, _fW/* s5Jf */.a, _fW/* s5Jf */.b));
  return new T2(0,_fX/* s5Ji */.a,_fX/* s5Ji */.b);
},
_fY/* $fNumExpr_$c- */ = function(_fZ/* s5Jl */, _g0/* s5Jm */, _g1/* s5Jn */){
  var _g2/* s5Jo */ = B(_g3/* Lib.AD.$fNumExpr */(_fZ/* s5Jl */));
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_g2/* s5Jo */, _g0/* s5Jm */, new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_g2/* s5Jo */, _g1/* s5Jn */));
  }));});
},
_g4/* abs */ = function(_g5/* s6G6 */){
  return E(E(_g5/* s6G6 */).e);
},
_g6/* signum */ = function(_g7/* s6Gf */){
  return E(E(_g7/* s6Gf */).f);
},
_g8/* $w$cabs */ = function(_g9/* s5H9 */, _ga/* s5Ha */, _gb/* s5Hb */){
  var _gc/* s5Hl */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_g9/* s5H9 */).c).a);
      })));
    })));
  }),
  _gd/* s5Hv */ = new T(function(){
    var _ge/* s5Hs */ = new T(function(){
      return B(A2(_g6/* GHC.Num.signum */,_gc/* s5Hl */, _ga/* s5Ha */));
    });
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_g9/* s5H9 */).a)), function(_gf/* s5Ht */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_gc/* s5Hl */, _gf/* s5Ht */, _ge/* s5Hs */);});
    }, _gb/* s5Hb */));
  });
  return new T2(0,new T(function(){
    return B(A2(_g4/* GHC.Num.abs */,_gc/* s5Hl */, _ga/* s5Ha */));
  }),_gd/* s5Hv */);
},
_gg/* $fNumExpr_$cabs */ = function(_gh/* s5Hw */, _gi/* s5Hx */){
  var _gj/* s5Hy */ = E(_gi/* s5Hx */),
  _gk/* s5HB */ = B(_g8/* Lib.AD.$w$cabs */(_gh/* s5Hw */, _gj/* s5Hy */.a, _gj/* s5Hy */.b));
  return new T2(0,_gk/* s5HB */.a,_gk/* s5HB */.b);
},
_gl/* $w$cfromInteger */ = function(_gm/* s5Gk */, _gn/* s5Gl */){
  var _go/* s5Gv */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gm/* s5Gk */).c).a);
      })));
    })));
  }),
  _gp/* s5GC */ = new T(function(){
    return B(A2(_cU/* GHC.Base.pure */,E(_gm/* s5Gk */).a, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_go/* s5Gv */, _cR/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_go/* s5Gv */, _gn/* s5Gl */));
  }),_gp/* s5GC */);
},
_gq/* $fNumExpr_$cfromInteger */ = function(_gr/* s5GD */, _gs/* s5GE */){
  var _gt/* s5GF */ = B(_gl/* Lib.AD.$w$cfromInteger */(_gr/* s5GD */, _gs/* s5GE */));
  return new T2(0,_gt/* s5GF */.a,_gt/* s5GF */.b);
},
_gu/* $w$cnegate */ = function(_gv/* s5HE */, _gw/* s5HF */, _gx/* s5HG */){
  var _gy/* s5HQ */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gv/* s5HE */).c).a);
      })));
    })));
  }),
  _gz/* s5HY */ = new T(function(){
    return B(A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(E(_gv/* s5HE */).a)), new T(function(){
      return B(_6K/* GHC.Num.negate */(_gy/* s5HQ */));
    }), _gx/* s5HG */));
  });
  return new T2(0,new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_gy/* s5HQ */, _gw/* s5HF */));
  }),_gz/* s5HY */);
},
_gA/* $fNumExpr_$cnegate */ = function(_gB/* s5HZ */, _gC/* s5I0 */){
  var _gD/* s5I1 */ = E(_gC/* s5I0 */),
  _gE/* s5I4 */ = B(_gu/* Lib.AD.$w$cnegate */(_gB/* s5HZ */, _gD/* s5I1 */.a, _gD/* s5I1 */.b));
  return new T2(0,_gE/* s5I4 */.a,_gE/* s5I4 */.b);
},
_gF/* $w$csignum */ = function(_gG/* s5GI */, _gH/* s5GJ */){
  var _gI/* s5GT */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gG/* s5GI */).c).a);
      })));
    })));
  }),
  _gJ/* s5H0 */ = new T(function(){
    return B(A2(_cU/* GHC.Base.pure */,E(_gG/* s5GI */).a, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_gI/* s5GT */, _cR/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_g6/* GHC.Num.signum */,_gI/* s5GT */, _gH/* s5GJ */));
  }),_gJ/* s5H0 */);
},
_gK/* $fNumExpr_$csignum */ = function(_gL/* s5H1 */, _gM/* s5H2 */){
  var _gN/* s5H6 */ = B(_gF/* Lib.AD.$w$csignum */(_gL/* s5H1 */, E(_gM/* s5H2 */).a));
  return new T2(0,_gN/* s5H6 */.a,_gN/* s5H6 */.b);
},
_g3/* $fNumExpr */ = function(_gO/* s5Jq */){
  return {_:0,a:function(_eu/* B2 */, _et/* B1 */){
    return new F(function(){return _fR/* Lib.AD.$fNumExpr_$c+ */(_gO/* s5Jq */, _eu/* B2 */, _et/* B1 */);});
  },b:function(_eu/* B2 */, _et/* B1 */){
    return new F(function(){return _fY/* Lib.AD.$fNumExpr_$c- */(_gO/* s5Jq */, _eu/* B2 */, _et/* B1 */);});
  },c:function(_eu/* B2 */, _et/* B1 */){
    return new F(function(){return _fA/* Lib.AD.$fNumExpr_$c* */(_gO/* s5Jq */, _eu/* B2 */, _et/* B1 */);});
  },d:function(_et/* B1 */){
    return new F(function(){return _gA/* Lib.AD.$fNumExpr_$cnegate */(_gO/* s5Jq */, _et/* B1 */);});
  },e:function(_et/* B1 */){
    return new F(function(){return _gg/* Lib.AD.$fNumExpr_$cabs */(_gO/* s5Jq */, _et/* B1 */);});
  },f:function(_et/* B1 */){
    return new F(function(){return _gK/* Lib.AD.$fNumExpr_$csignum */(_gO/* s5Jq */, _et/* B1 */);});
  },g:function(_et/* B1 */){
    return new F(function(){return _gq/* Lib.AD.$fNumExpr_$cfromInteger */(_gO/* s5Jq */, _et/* B1 */);});
  }};
},
_gP/* gradient */ = function(_gQ/* saI2 */){
  var _gR/* saI3 */ = new T(function(){
    return E(E(_gQ/* saI2 */).a);
  }),
  _gS/* saIc */ = new T3(0,_8V/* Lib.World.$fApplicativeWorld */,_91/* Lib.World.$fArithWorld_$cbasis */,new T2(0,_gR/* saI3 */,new T(function(){
    return E(E(_gQ/* saI2 */).b);
  }))),
  _gT/* saIf */ = new T(function(){
    return B(_eq/* Lib.AD.$fFloatingExpr */(new T(function(){
      return B(_fk/* Lib.AD.$fFractionalExpr */(new T(function(){
        return B(_g3/* Lib.AD.$fNumExpr */(_gS/* saIc */));
      }), _gS/* saIc */));
    }), _gS/* saIc */));
  }),
  _gU/* saIh */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_gR/* saI3 */));
    })));
  });
  return function(_gV/* saIi */){
    var _gW/* saIj */ = E(_gV/* saIi */),
    _gX/* saIn */ = B(_8Z/* Lib.World.$w$cbasis */(_gU/* saIh */));
    return E(B(_7y/* Lib.World.$wfield */(_gT/* saIf */, new T2(0,_gW/* saIj */.a,_gX/* saIn */.a), new T2(0,_gW/* saIj */.b,_gX/* saIn */.b), new T2(0,_gW/* saIj */.c,_gX/* saIn */.c))).b);
  };
},
_gY/* gradStr6 */ = new T(function(){
  return B(_gP/* Lib.World.gradient */(_8v/* Lib.Shader.gradStr7 */));
}),
_gZ/* prependToAll */ = function(_h0/* s1ZGt */, _h1/* s1ZGu */){
  var _h2/* s1ZGv */ = E(_h1/* s1ZGu */);
  return (_h2/* s1ZGv */._==0) ? __Z/* EXTERNAL */ : new T2(1,_h0/* s1ZGt */,new T2(1,_h2/* s1ZGv */.a,new T(function(){
    return B(_gZ/* Data.OldList.prependToAll */(_h0/* s1ZGt */, _h2/* s1ZGv */.b));
  })));
},
_h3/* gradStr5 */ = new T(function(){
  var _h4/* s4xo */ = B(A1(_gY/* Lib.Shader.gradStr6 */,_84/* Lib.Shader.argument */));
  return new T2(1,_h4/* s4xo */.a,new T(function(){
    return B(_gZ/* Data.OldList.prependToAll */(_r/* Lib.Shader.$fFloatingVar29 */, new T2(1,_h4/* s4xo */.b,new T2(1,_h4/* s4xo */.c,_o/* GHC.Types.[] */))));
  }));
}),
_h5/* gradStr4 */ = new T1(1,_h3/* Lib.Shader.gradStr5 */),
_h6/* gradStr2 */ = new T2(1,_h5/* Lib.Shader.gradStr4 */,_w/* Lib.Shader.gradStr3 */),
_h7/* gradStr9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("vec3("));
}),
_h8/* gradStr8 */ = new T1(0,_h7/* Lib.Shader.gradStr9 */),
_h9/* gradStr1 */ = new T2(1,_h8/* Lib.Shader.gradStr8 */,_h6/* Lib.Shader.gradStr2 */),
_ha/* gradStr */ = new T(function(){
  return toJSStr/* EXTERNAL */(B(_7V/* Lib.Shader.$fFoldableVar_$s$cfoldMap */(_p/* GHC.Base.$fMonoid[] */, _7S/* GHC.Base.id */, _h9/* Lib.Shader.gradStr1 */)));
}),
_hb/* $wlenAcc */ = function(_hc/* sbMs */, _hd/* sbMt */){
  while(1){
    var _he/* sbMu */ = E(_hc/* sbMs */);
    if(!_he/* sbMu */._){
      return E(_hd/* sbMt */);
    }else{
      var _hf/*  sbMt */ = _hd/* sbMt */+1|0;
      _hc/* sbMs */ = _he/* sbMu */.b;
      _hd/* sbMt */ = _hf/*  sbMt */;
      continue;
    }
  }
},
_hg/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(Array.!): undefined array element"));
}),
_hh/* arrEleBottom */ = new T(function(){
  return B(err/* EXTERNAL */(_hg/* GHC.Arr.lvl37 */));
}),
_hi/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_hj/* $s^1 */ = new T(function(){
  return B(err/* EXTERNAL */(_hi/* Lib.Object.lvl13 */));
}),
_hk/* $wg1 */ = function(_hl/* smLe */, _hm/* smLf */, _hn/* smLg */){
  while(1){
    if(!(_hm/* smLf */%2)){
      var _ho/*  smLe */ = _hl/* smLe */*_hl/* smLe */,
      _hp/*  smLf */ = quot/* EXTERNAL */(_hm/* smLf */, 2);
      _hl/* smLe */ = _ho/*  smLe */;
      _hm/* smLf */ = _hp/*  smLf */;
      continue;
    }else{
      var _hq/* smLi */ = E(_hm/* smLf */);
      if(_hq/* smLi */==1){
        return _hl/* smLe */*_hn/* smLg */;
      }else{
        var _ho/*  smLe */ = _hl/* smLe */*_hl/* smLe */,
        _hr/*  smLg */ = _hl/* smLe */*_hn/* smLg */;
        _hl/* smLe */ = _ho/*  smLe */;
        _hm/* smLf */ = quot/* EXTERNAL */(_hq/* smLi */-1|0, 2);
        _hn/* smLg */ = _hr/*  smLg */;
        continue;
      }
    }
  }
},
_hs/* $wf */ = function(_ht/* smLp */, _hu/* smLq */){
  while(1){
    if(!(_hu/* smLq */%2)){
      var _hv/*  smLp */ = _ht/* smLp */*_ht/* smLp */,
      _hw/*  smLq */ = quot/* EXTERNAL */(_hu/* smLq */, 2);
      _ht/* smLp */ = _hv/*  smLp */;
      _hu/* smLq */ = _hw/*  smLq */;
      continue;
    }else{
      var _hx/* smLs */ = E(_hu/* smLq */);
      if(_hx/* smLs */==1){
        return E(_ht/* smLp */);
      }else{
        return new F(function(){return _hk/* Lib.Object.$wg1 */(_ht/* smLp */*_ht/* smLp */, quot/* EXTERNAL */(_hx/* smLs */-1|0, 2), _ht/* smLp */);});
      }
    }
  }
},
_hy/* $fFloatingDouble_$cacosh */ = function(_hz/* s1l7h */){
  var _hA/* s1l7i */ = E(_hz/* s1l7h */);
  return new F(function(){return Math.log/* EXTERNAL */(_hA/* s1l7i */+(_hA/* s1l7i */+1)*Math.sqrt/* EXTERNAL */((_hA/* s1l7i */-1)/(_hA/* s1l7i */+1)));});
},
_hB/* $fFloatingDouble_$casinh */ = function(_hC/* s1l7s */){
  var _hD/* s1l7t */ = E(_hC/* s1l7s */);
  return new F(function(){return Math.log/* EXTERNAL */(_hD/* s1l7t */+Math.sqrt/* EXTERNAL */(1+_hD/* s1l7t */*_hD/* s1l7t */));});
},
_hE/* $fFloatingDouble_$catanh */ = function(_hF/* s1l79 */){
  var _hG/* s1l7a */ = E(_hF/* s1l79 */);
  return 0.5*Math.log/* EXTERNAL */((1+_hG/* s1l7a */)/(1-_hG/* s1l7a */));
},
_hH/* $fFloatingDouble_$clogBase */ = function(_hI/* s1l7A */, _hJ/* s1l7B */){
  return Math.log/* EXTERNAL */(E(_hJ/* s1l7B */))/Math.log/* EXTERNAL */(E(_hI/* s1l7A */));
},
_hK/* $fFloatingDouble_$cpi */ = 3.141592653589793,
_hL/* $fFractionalDouble_$cfromRational */ = function(_hM/* s1ldy */){
  var _hN/* s1ldz */ = E(_hM/* s1ldy */);
  return new F(function(){return _6j/* GHC.Float.rationalToDouble */(_hN/* s1ldz */.a, _hN/* s1ldz */.b);});
},
_hO/* $fFractionalDouble_$crecip */ = function(_hP/* s1l75 */){
  return 1/E(_hP/* s1l75 */);
},
_hQ/* $fNumDouble_$cabs */ = function(_hR/* s1l6w */){
  var _hS/* s1l6x */ = E(_hR/* s1l6w */),
  _hT/* s1l6z */ = E(_hS/* s1l6x */);
  return (_hT/* s1l6z */==0) ? E(_6i/* GHC.Float.rationalToDouble4 */) : (_hT/* s1l6z */<=0) ?  -_hT/* s1l6z */ : E(_hS/* s1l6x */);
},
_hU/* doubleFromInteger */ = function(_hV/* s1M0 */){
  var _hW/* s1M1 */ = E(_hV/* s1M0 */);
  if(!_hW/* s1M1 */._){
    return _hW/* s1M1 */.a;
  }else{
    return new F(function(){return I_toNumber/* EXTERNAL */(_hW/* s1M1 */.a);});
  }
},
_hX/* $fNumDouble_$cfromInteger */ = function(_hY/* s1l6n */){
  return new F(function(){return _hU/* GHC.Integer.Type.doubleFromInteger */(_hY/* s1l6n */);});
},
_hZ/* $fNumDouble1 */ = 1,
_i0/* $fNumDouble2 */ =  -1,
_i1/* $fNumDouble_$csignum */ = function(_i2/* s1l6p */){
  var _i3/* s1l6q */ = E(_i2/* s1l6p */);
  return (_i3/* s1l6q */<=0) ? (_i3/* s1l6q */>=0) ? E(_i3/* s1l6q */) : E(_i0/* GHC.Float.$fNumDouble2 */) : E(_hZ/* GHC.Float.$fNumDouble1 */);
},
_i4/* minusDouble */ = function(_i5/* s1kEA */, _i6/* s1kEB */){
  return E(_i5/* s1kEA */)-E(_i6/* s1kEB */);
},
_i7/* negateDouble */ = function(_i8/* s1kEi */){
  return  -E(_i8/* s1kEi */);
},
_i9/* plusDouble */ = function(_ia/* s1kEH */, _ib/* s1kEI */){
  return E(_ia/* s1kEH */)+E(_ib/* s1kEI */);
},
_ic/* timesDouble */ = function(_id/* s1kEt */, _ie/* s1kEu */){
  return E(_id/* s1kEt */)*E(_ie/* s1kEu */);
},
_if/* $fNumDouble */ = {_:0,a:_i9/* GHC.Float.plusDouble */,b:_i4/* GHC.Float.minusDouble */,c:_ic/* GHC.Float.timesDouble */,d:_i7/* GHC.Float.negateDouble */,e:_hQ/* GHC.Float.$fNumDouble_$cabs */,f:_i1/* GHC.Float.$fNumDouble_$csignum */,g:_hX/* GHC.Float.$fNumDouble_$cfromInteger */},
_ig/* divideDouble */ = function(_ih/* s1kEm */, _ii/* s1kEn */){
  return E(_ih/* s1kEm */)/E(_ii/* s1kEn */);
},
_ij/* $fFractionalDouble */ = new T4(0,_if/* GHC.Float.$fNumDouble */,_ig/* GHC.Float.divideDouble */,_hO/* GHC.Float.$fFractionalDouble_$crecip */,_hL/* GHC.Float.$fFractionalDouble_$cfromRational */),
_ik/* acosDouble */ = function(_il/* s1kCY */){
  return new F(function(){return Math.acos/* EXTERNAL */(E(_il/* s1kCY */));});
},
_im/* asinDouble */ = function(_in/* s1kD2 */){
  return new F(function(){return Math.asin/* EXTERNAL */(E(_in/* s1kD2 */));});
},
_io/* atanDouble */ = function(_ip/* s1kCU */){
  return new F(function(){return Math.atan/* EXTERNAL */(E(_ip/* s1kCU */));});
},
_iq/* cosDouble */ = function(_ir/* s1kDa */){
  return new F(function(){return Math.cos/* EXTERNAL */(E(_ir/* s1kDa */));});
},
_is/* coshDouble */ = function(_it/* s1kCM */){
  return new F(function(){return cosh/* EXTERNAL */(E(_it/* s1kCM */));});
},
_iu/* expDouble */ = function(_iv/* s1kDq */){
  return new F(function(){return Math.exp/* EXTERNAL */(E(_iv/* s1kDq */));});
},
_iw/* logDouble */ = function(_ix/* s1kDm */){
  return new F(function(){return Math.log/* EXTERNAL */(E(_ix/* s1kDm */));});
},
_iy/* powerDouble */ = function(_iz/* s1kCB */, _iA/* s1kCC */){
  return new F(function(){return Math.pow/* EXTERNAL */(E(_iz/* s1kCB */), E(_iA/* s1kCC */));});
},
_iB/* sinDouble */ = function(_iC/* s1kDe */){
  return new F(function(){return Math.sin/* EXTERNAL */(E(_iC/* s1kDe */));});
},
_iD/* sinhDouble */ = function(_iE/* s1kCQ */){
  return new F(function(){return sinh/* EXTERNAL */(E(_iE/* s1kCQ */));});
},
_iF/* sqrtDouble */ = function(_iG/* s1kDi */){
  return new F(function(){return Math.sqrt/* EXTERNAL */(E(_iG/* s1kDi */));});
},
_iH/* tanDouble */ = function(_iI/* s1kD6 */){
  return new F(function(){return Math.tan/* EXTERNAL */(E(_iI/* s1kD6 */));});
},
_iJ/* tanhDouble */ = function(_iK/* s1kCI */){
  return new F(function(){return tanh/* EXTERNAL */(E(_iK/* s1kCI */));});
},
_iL/* $fFloatingDouble */ = {_:0,a:_ij/* GHC.Float.$fFractionalDouble */,b:_hK/* GHC.Float.$fFloatingDouble_$cpi */,c:_iu/* GHC.Float.expDouble */,d:_iw/* GHC.Float.logDouble */,e:_iF/* GHC.Float.sqrtDouble */,f:_iy/* GHC.Float.powerDouble */,g:_hH/* GHC.Float.$fFloatingDouble_$clogBase */,h:_iB/* GHC.Float.sinDouble */,i:_iq/* GHC.Float.cosDouble */,j:_iH/* GHC.Float.tanDouble */,k:_im/* GHC.Float.asinDouble */,l:_ik/* GHC.Float.acosDouble */,m:_io/* GHC.Float.atanDouble */,n:_iD/* GHC.Float.sinhDouble */,o:_is/* GHC.Float.coshDouble */,p:_iJ/* GHC.Float.tanhDouble */,q:_hB/* GHC.Float.$fFloatingDouble_$casinh */,r:_hy/* GHC.Float.$fFloatingDouble_$cacosh */,s:_hE/* GHC.Float.$fFloatingDouble_$catanh */},
_iM/* $fEqDouble_$c/= */ = function(_iN/* scFY */, _iO/* scFZ */){
  return (E(_iN/* scFY */)!=E(_iO/* scFZ */)) ? true : false;
},
_iP/* $fEqDouble_$c== */ = function(_iQ/* scFR */, _iR/* scFS */){
  return E(_iQ/* scFR */)==E(_iR/* scFS */);
},
_iS/* $fEqDouble */ = new T2(0,_iP/* GHC.Classes.$fEqDouble_$c== */,_iM/* GHC.Classes.$fEqDouble_$c/= */),
_iT/* $fOrdDouble_$c< */ = function(_iU/* scIb */, _iV/* scIc */){
  return E(_iU/* scIb */)<E(_iV/* scIc */);
},
_iW/* $fOrdDouble_$c<= */ = function(_iX/* scI4 */, _iY/* scI5 */){
  return E(_iX/* scI4 */)<=E(_iY/* scI5 */);
},
_iZ/* $fOrdDouble_$c> */ = function(_j0/* scHX */, _j1/* scHY */){
  return E(_j0/* scHX */)>E(_j1/* scHY */);
},
_j2/* $fOrdDouble_$c>= */ = function(_j3/* scHQ */, _j4/* scHR */){
  return E(_j3/* scHQ */)>=E(_j4/* scHR */);
},
_j5/* $fOrdDouble_$ccompare */ = function(_j6/* scIi */, _j7/* scIj */){
  var _j8/* scIk */ = E(_j6/* scIi */),
  _j9/* scIm */ = E(_j7/* scIj */);
  return (_j8/* scIk */>=_j9/* scIm */) ? (_j8/* scIk */!=_j9/* scIm */) ? 2 : 1 : 0;
},
_ja/* $fOrdDouble_$cmax */ = function(_jb/* scIA */, _jc/* scIB */){
  var _jd/* scIC */ = E(_jb/* scIA */),
  _je/* scIE */ = E(_jc/* scIB */);
  return (_jd/* scIC */>_je/* scIE */) ? E(_jd/* scIC */) : E(_je/* scIE */);
},
_jf/* $fOrdDouble_$cmin */ = function(_jg/* scIs */, _jh/* scIt */){
  var _ji/* scIu */ = E(_jg/* scIs */),
  _jj/* scIw */ = E(_jh/* scIt */);
  return (_ji/* scIu */>_jj/* scIw */) ? E(_jj/* scIw */) : E(_ji/* scIu */);
},
_jk/* $fOrdDouble */ = {_:0,a:_iS/* GHC.Classes.$fEqDouble */,b:_j5/* GHC.Classes.$fOrdDouble_$ccompare */,c:_iT/* GHC.Classes.$fOrdDouble_$c< */,d:_iW/* GHC.Classes.$fOrdDouble_$c<= */,e:_iZ/* GHC.Classes.$fOrdDouble_$c> */,f:_j2/* GHC.Classes.$fOrdDouble_$c>= */,g:_ja/* GHC.Classes.$fOrdDouble_$cmax */,h:_jf/* GHC.Classes.$fOrdDouble_$cmin */},
_jl/* $sfitP1 */ = new T2(0,_iL/* GHC.Float.$fFloatingDouble */,_jk/* GHC.Classes.$fOrdDouble */),
_jm/* $w$cdot */ = function(_jn/* saB6 */, _jo/* saB7 */, _jp/* saB8 */, _jq/* saB9 */, _jr/* saBa */, _js/* saBb */, _jt/* saBc */){
  var _ju/* saBe */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_jn/* saB6 */)))),
  _jv/* saBh */ = new T(function(){
    return B(A3(_6I/* GHC.Num.+ */,_ju/* saBe */, new T(function(){
      return B(A3(_7k/* GHC.Num.* */,_ju/* saBe */, _jo/* saB7 */, _jr/* saBa */));
    }), new T(function(){
      return B(A3(_7k/* GHC.Num.* */,_ju/* saBe */, _jp/* saB8 */, _js/* saBb */));
    })));
  });
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_ju/* saBe */, _jv/* saBh */, new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_ju/* saBe */, _jq/* saB9 */, _jt/* saBc */));
  }));});
},
_jw/* $w$cnormalize */ = function(_jx/* saBS */, _jy/* saBT */, _jz/* saBU */, _jA/* saBV */){
  var _jB/* saBW */ = new T(function(){
    return E(E(_jx/* saBS */).a);
  }),
  _jC/* saC0 */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(_jB/* saBW */));
  }),
  _jD/* saC1 */ = new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_jB/* saBW */, new T(function(){
      return B(_jm/* Lib.World.$w$cdot */(_jB/* saBW */, _jy/* saBT */, _jz/* saBU */, _jA/* saBV */, _jy/* saBT */, _jz/* saBU */, _jA/* saBV */));
    })));
  });
  return new T3(0,new T(function(){
    return B(A3(_98/* GHC.Real./ */,_jC/* saC0 */, _jy/* saBT */, _jD/* saC1 */));
  }),new T(function(){
    return B(A3(_98/* GHC.Real./ */,_jC/* saC0 */, _jz/* saBU */, _jD/* saC1 */));
  }),new T(function(){
    return B(A3(_98/* GHC.Real./ */,_jC/* saC0 */, _jA/* saBV */, _jD/* saC1 */));
  }));
},
_jE/* $wfitP */ = function(_jF/* saJe */, _jG/* saJf */){
  var _jH/* saJg */ = new T(function(){
    return E(E(_jF/* saJe */).a);
  }),
  _jI/* saJk */ = new T(function(){
    return E(E(_jF/* saJe */).b);
  }),
  _jJ/* saJo */ = new T(function(){
    return B(A2(_gP/* Lib.World.gradient */,new T2(0,_jH/* saJg */,_jI/* saJk */), _jG/* saJf */));
  }),
  _jK/* saJq */ = new T(function(){
    var _jL/* saJr */ = E(_jJ/* saJo */),
    _jM/* saJw */ = B(_jw/* Lib.World.$w$cnormalize */(new T2(0,_jH/* saJg */,_jI/* saJk */), _jL/* saJr */.a, _jL/* saJr */.b, _jL/* saJr */.c));
    return new T3(0,_jM/* saJw */.a,_jM/* saJw */.b,_jM/* saJw */.c);
  }),
  _jN/* saK4 */ = new T(function(){
    var _jO/* saJA */ = E(_jG/* saJf */),
    _jP/* saJB */ = _jO/* saJA */.a,
    _jQ/* saJC */ = _jO/* saJA */.b,
    _jR/* saJD */ = _jO/* saJA */.c,
    _jS/* saJE */ = E(_jK/* saJq */),
    _jT/* saJI */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_jH/* saJg */));
    }),
    _jU/* saJJ */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_jT/* saJI */));
    }),
    _jV/* saJK */ = new T(function(){
      return B(_6I/* GHC.Num.+ */(_jU/* saJJ */));
    }),
    _jW/* saJL */ = new T(function(){
      return B(_6K/* GHC.Num.negate */(_jU/* saJJ */));
    }),
    _jX/* saJM */ = new T(function(){
      return B(_7k/* GHC.Num.* */(_jU/* saJJ */));
    }),
    _jY/* saJN */ = new T(function(){
      var _jZ/* saJU */ = new T(function(){
        return B(A2(_7w/* GHC.Float.sqrt */,_jH/* saJg */, new T(function(){
          var _k0/* saJP */ = E(_jJ/* saJo */),
          _k1/* saJQ */ = _k0/* saJP */.a,
          _k2/* saJR */ = _k0/* saJP */.b,
          _k3/* saJS */ = _k0/* saJP */.c;
          return B(_jm/* Lib.World.$w$cdot */(_jH/* saJg */, _k1/* saJQ */, _k2/* saJR */, _k3/* saJS */, _k1/* saJQ */, _k2/* saJR */, _k3/* saJS */));
        })));
      });
      return B(A3(_98/* GHC.Real./ */,_jT/* saJI */, new T(function(){
        return B(_7y/* Lib.World.$wfield */(_jH/* saJg */, _jP/* saJB */, _jQ/* saJC */, _jR/* saJD */));
      }), _jZ/* saJU */));
    }),
    _k4/* saK3 */ = new T(function(){
      var _k5/* saK2 */ = new T(function(){
        return B(A1(_jW/* saJL */,new T(function(){
          return B(A2(_jX/* saJM */,_jS/* saJE */.c, _jY/* saJN */));
        })));
      });
      return B(A2(_jV/* saJK */,_jR/* saJD */, _k5/* saK2 */));
    }),
    _k6/* saK0 */ = new T(function(){
      var _k7/* saJZ */ = new T(function(){
        return B(A1(_jW/* saJL */,new T(function(){
          return B(A2(_jX/* saJM */,_jS/* saJE */.b, _jY/* saJN */));
        })));
      });
      return B(A2(_jV/* saJK */,_jQ/* saJC */, _k7/* saJZ */));
    }),
    _k8/* saJX */ = new T(function(){
      var _k9/* saJW */ = new T(function(){
        return B(A1(_jW/* saJL */,new T(function(){
          return B(A2(_jX/* saJM */,_jS/* saJE */.a, _jY/* saJN */));
        })));
      });
      return B(A2(_jV/* saJK */,_jP/* saJB */, _k9/* saJW */));
    });
    return new T3(0,_k8/* saJX */,_k6/* saK0 */,_k4/* saK3 */);
  });
  return new T2(0,_jN/* saK4 */,_jK/* saJq */);
},
_ka/* $wperpTo */ = function(_kb/* saCg */, _kc/* saCh */, _kd/* saCi */, _ke/* saCj */, _kf/* saCk */, _kg/* saCl */, _kh/* saCm */){
  var _ki/* saCn */ = new T(function(){
    return E(E(_kb/* saCg */).a);
  }),
  _kj/* saCs */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_ki/* saCn */));
    })));
  }),
  _kk/* saCt */ = new T(function(){
    return B(_6I/* GHC.Num.+ */(_kj/* saCs */));
  }),
  _kl/* saCu */ = new T(function(){
    return B(_6K/* GHC.Num.negate */(_kj/* saCs */));
  }),
  _km/* saCv */ = new T(function(){
    return B(_7k/* GHC.Num.* */(_kj/* saCs */));
  }),
  _kn/* saCw */ = new T(function(){
    return B(_jm/* Lib.World.$w$cdot */(_ki/* saCn */, _kf/* saCk */, _kg/* saCl */, _kh/* saCm */, _kc/* saCh */, _kd/* saCi */, _ke/* saCj */));
  }),
  _ko/* saCF */ = new T(function(){
    var _kp/* saCE */ = new T(function(){
      return B(A1(_kl/* saCu */,new T(function(){
        return B(A2(_km/* saCv */,_kh/* saCm */, _kn/* saCw */));
      })));
    });
    return B(A2(_kk/* saCt */,_ke/* saCj */, _kp/* saCE */));
  }),
  _kq/* saCC */ = new T(function(){
    var _kr/* saCB */ = new T(function(){
      return B(A1(_kl/* saCu */,new T(function(){
        return B(A2(_km/* saCv */,_kg/* saCl */, _kn/* saCw */));
      })));
    });
    return B(A2(_kk/* saCt */,_kd/* saCi */, _kr/* saCB */));
  }),
  _ks/* saCz */ = new T(function(){
    var _kt/* saCy */ = new T(function(){
      return B(A1(_kl/* saCu */,new T(function(){
        return B(A2(_km/* saCv */,_kf/* saCk */, _kn/* saCw */));
      })));
    });
    return B(A2(_kk/* saCt */,_kc/* saCh */, _kt/* saCy */));
  });
  return new T3(0,_ks/* saCz */,_kq/* saCC */,_ko/* saCF */);
},
_ku/* absentError */ = function(_kv/* s4EiW */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Oops!  Entered absent arg ", new T(function(){
    return B(unCStr/* EXTERNAL */(_kv/* s4EiW */));
  }))));});
},
_kw/* fitR1 */ = new T(function(){
  return B(_ku/* Control.Exception.Base.absentError */("$dOrd_s9EN Ord a"));
}),
_kx/* $wfitR */ = function(_ky/* saDX */, _kz/* saDY */, _kA/* saDZ */, _kB/* saE0 */, _kC/* saE1 */, _kD/* saE2 */, _kE/* saE3 */){
  var _kF/* saE4 */ = new T(function(){
    return E(E(_ky/* saDX */).a);
  }),
  _kG/* saE9 */ = B(_ka/* Lib.World.$wperpTo */(new T2(0,_kF/* saE4 */,_kw/* Lib.World.fitR1 */), _kC/* saE1 */, _kD/* saE2 */, _kE/* saE3 */, _kz/* saDY */, _kA/* saDZ */, _kB/* saE0 */));
  return new F(function(){return _jw/* Lib.World.$w$cnormalize */(new T2(0,_kF/* saE4 */,_kw/* Lib.World.fitR1 */), _kG/* saE9 */.a, _kG/* saE9 */.b, _kG/* saE9 */.c);});
},
_kH/* $p1Ord */ = function(_kI/* scBS */){
  return E(E(_kI/* scBS */).a);
},
_kJ/* == */ = function(_kK/* scBK */){
  return E(E(_kK/* scBK */).a);
},
_kL/* $wfitV */ = function(_kM/* saCV */, _kN/* saCW */, _kO/* saCX */, _kP/* saCY */){
  var _kQ/* saCZ */ = new T(function(){
    var _kR/* saD0 */ = E(_kP/* saCY */),
    _kS/* saD4 */ = E(_kO/* saCX */),
    _kT/* saD9 */ = B(_ka/* Lib.World.$wperpTo */(new T2(0,_kM/* saCV */,_kN/* saCW */), _kR/* saD0 */.a, _kR/* saD0 */.b, _kR/* saD0 */.c, _kS/* saD4 */.a, _kS/* saD4 */.b, _kS/* saD4 */.c));
    return new T3(0,_kT/* saD9 */.a,_kT/* saD9 */.b,_kT/* saD9 */.c);
  }),
  _kU/* saDj */ = new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_kM/* saCV */, new T(function(){
      var _kV/* saDe */ = E(_kQ/* saCZ */),
      _kW/* saDf */ = _kV/* saDe */.a,
      _kX/* saDg */ = _kV/* saDe */.b,
      _kY/* saDh */ = _kV/* saDe */.c;
      return B(_jm/* Lib.World.$w$cdot */(_kM/* saCV */, _kW/* saDf */, _kX/* saDg */, _kY/* saDh */, _kW/* saDf */, _kX/* saDg */, _kY/* saDh */));
    })));
  });
  if(!B(A3(_kJ/* GHC.Classes.== */,B(_kH/* GHC.Classes.$p1Ord */(_kN/* saCW */)), _kU/* saDj */, new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_kM/* saCV */)))), _8W/* Lib.World.$fArithWorld1 */));
  })))){
    var _kZ/* saDo */ = E(_kQ/* saCZ */),
    _l0/* saDt */ = B(_jw/* Lib.World.$w$cnormalize */(new T2(0,_kM/* saCV */,_kN/* saCW */), _kZ/* saDo */.a, _kZ/* saDo */.b, _kZ/* saDo */.c)),
    _l1/* saDz */ = new T(function(){
      return B(_7k/* GHC.Num.* */(new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
          return B(_7g/* GHC.Float.$p1Floating */(_kM/* saCV */));
        })));
      })));
    }),
    _l2/* saDA */ = new T(function(){
      return B(A2(_7w/* GHC.Float.sqrt */,_kM/* saCV */, new T(function(){
        var _l3/* saDB */ = E(_kP/* saCY */),
        _l4/* saDC */ = _l3/* saDB */.a,
        _l5/* saDD */ = _l3/* saDB */.b,
        _l6/* saDE */ = _l3/* saDB */.c;
        return B(_jm/* Lib.World.$w$cdot */(_kM/* saCV */, _l4/* saDC */, _l5/* saDD */, _l6/* saDE */, _l4/* saDC */, _l5/* saDD */, _l6/* saDE */));
      })));
    });
    return new T3(0,new T(function(){
      return B(A2(_l1/* saDz */,_l0/* saDt */.a, _l2/* saDA */));
    }),new T(function(){
      return B(A2(_l1/* saDz */,_l0/* saDt */.b, _l2/* saDA */));
    }),new T(function(){
      return B(A2(_l1/* saDz */,_l0/* saDt */.c, _l2/* saDA */));
    }));
  }else{
    var _l7/* saDJ */ = new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_kM/* saCV */)))), _8W/* Lib.World.$fArithWorld1 */));
    });
    return new T3(0,_l7/* saDJ */,_l7/* saDJ */,_l7/* saDJ */);
  }
},
_l8/* $fNumPos_s */ = 0,
_l9/* angleCount */ = new T(function(){
  var _la/* s6nL */ = eval/* EXTERNAL */("angleCount"),
  _lb/* s6nP */ = Number/* EXTERNAL */(_la/* s6nL */);
  return jsTrunc/* EXTERNAL */(_lb/* s6nP */);
}),
_lc/* aN */ = new T(function(){
  return E(_l9/* Lib.Util.angleCount */);
}),
_ld/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_le/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_lf/* errorEmptyList */ = function(_lg/* sbDG */){
  return new F(function(){return err/* EXTERNAL */(B(_f/* GHC.Base.++ */(_le/* GHC.List.prel_list_str */, new T(function(){
    return B(_f/* GHC.Base.++ */(_lg/* sbDG */, _ld/* GHC.List.lvl */));
  },1))));});
},
_lh/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("head"));
}),
_li/* badHead */ = new T(function(){
  return B(_lf/* GHC.List.errorEmptyList */(_lh/* GHC.List.lvl18 */));
}),
_lj/* go1 */ = function(_lk/* smWh */, _ll/* smWi */, _lm/* smWj */){
  var _ln/* smWk */ = E(_lk/* smWh */);
  if(!_ln/* smWk */._){
    return __Z/* EXTERNAL */;
  }else{
    var _lo/* smWn */ = E(_ll/* smWi */);
    if(!_lo/* smWn */._){
      return __Z/* EXTERNAL */;
    }else{
      var _lp/* smWo */ = _lo/* smWn */.a,
      _lq/* smWq */ = E(_lm/* smWj */);
      if(!_lq/* smWq */._){
        return __Z/* EXTERNAL */;
      }else{
        var _lr/* smWt */ = E(_lq/* smWq */.a),
        _ls/* smWu */ = _lr/* smWt */.a;
        return new F(function(){return _f/* GHC.Base.++ */(new T2(1,new T3(0,_ln/* smWk */.a,_lp/* smWo */,_ls/* smWu */),new T2(1,new T3(0,_lp/* smWo */,_ls/* smWu */,_lr/* smWt */.b),_o/* GHC.Types.[] */)), new T(function(){
          return B(_lj/* Lib.Object.go1 */(_ln/* smWk */.b, _lo/* smWn */.b, _lq/* smWq */.b));
        },1));});
      }
    }
  }
},
_lt/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tail"));
}),
_lu/* tail1 */ = new T(function(){
  return B(_lf/* GHC.List.errorEmptyList */(_lt/* GHC.List.lvl17 */));
}),
_lv/* zip */ = function(_lw/* sbOD */, _lx/* sbOE */){
  var _ly/* sbOF */ = E(_lw/* sbOD */);
  if(!_ly/* sbOF */._){
    return __Z/* EXTERNAL */;
  }else{
    var _lz/* sbOI */ = E(_lx/* sbOE */);
    return (_lz/* sbOI */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T2(0,_ly/* sbOF */.a,_lz/* sbOI */.a),new T(function(){
      return B(_lv/* GHC.List.zip */(_ly/* sbOF */.b, _lz/* sbOI */.b));
    }));
  }
},
_lA/* go2 */ = function(_lB/* smWB */, _lC/* smWC */){
  var _lD/* smWD */ = E(_lB/* smWB */);
  if(!_lD/* smWD */._){
    return __Z/* EXTERNAL */;
  }else{
    var _lE/* smWG */ = E(_lC/* smWC */);
    if(!_lE/* smWG */._){
      return __Z/* EXTERNAL */;
    }else{
      var _lF/* smWJ */ = E(_lD/* smWD */.a),
      _lG/* smWL */ = _lF/* smWJ */.b,
      _lH/* smWO */ = E(_lE/* smWG */.a).b,
      _lI/* smX7 */ = new T(function(){
        var _lJ/* smX6 */ = new T(function(){
          return B(_lv/* GHC.List.zip */(_lH/* smWO */, new T(function(){
            var _lK/* smX2 */ = E(_lH/* smWO */);
            if(!_lK/* smX2 */._){
              return E(_lu/* GHC.List.tail1 */);
            }else{
              return E(_lK/* smX2 */.b);
            }
          },1)));
        },1);
        return B(_lj/* Lib.Object.go1 */(_lG/* smWL */, new T(function(){
          var _lL/* smWY */ = E(_lG/* smWL */);
          if(!_lL/* smWY */._){
            return E(_lu/* GHC.List.tail1 */);
          }else{
            return E(_lL/* smWY */.b);
          }
        },1), _lJ/* smX6 */));
      });
      return new F(function(){return _f/* GHC.Base.++ */(new T2(1,new T3(0,_lF/* smWJ */.a,new T(function(){
        var _lM/* smWP */ = E(_lG/* smWL */);
        if(!_lM/* smWP */._){
          return E(_li/* GHC.List.badHead */);
        }else{
          return E(_lM/* smWP */.a);
        }
      }),new T(function(){
        var _lN/* smWT */ = E(_lH/* smWO */);
        if(!_lN/* smWT */._){
          return E(_li/* GHC.List.badHead */);
        }else{
          return E(_lN/* smWT */.a);
        }
      })),_lI/* smX7 */), new T(function(){
        return B(_lA/* Lib.Object.go2 */(_lD/* smWD */.b, _lE/* smWG */.b));
      },1));});
    }
  }
},
_lO/* lvl5 */ = new T(function(){
  return E(_lc/* Lib.Object.aN */)-1;
}),
_lP/* $fEnumRatio1 */ = new T1(0,1),
_lQ/* $wnumericEnumFrom */ = function(_lR/* svpc */, _lS/* svpd */){
  var _lT/* svpe */ = E(_lS/* svpd */),
  _lU/* svpl */ = new T(function(){
    var _lV/* svpf */ = B(_7i/* GHC.Real.$p1Fractional */(_lR/* svpc */)),
    _lW/* svpi */ = B(_lQ/* GHC.Real.$wnumericEnumFrom */(_lR/* svpc */, B(A3(_6I/* GHC.Num.+ */,_lV/* svpf */, _lT/* svpe */, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_lV/* svpf */, _lP/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_lW/* svpi */.a,_lW/* svpi */.b);
  });
  return new T2(0,_lT/* svpe */,_lU/* svpl */);
},
_lX/* <= */ = function(_lY/* scCm */){
  return E(E(_lY/* scCm */).d);
},
_lZ/* even2 */ = new T1(0,2),
_m0/* takeWhile */ = function(_m1/* sbJ5 */, _m2/* sbJ6 */){
  var _m3/* sbJ7 */ = E(_m2/* sbJ6 */);
  if(!_m3/* sbJ7 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _m4/* sbJ8 */ = _m3/* sbJ7 */.a;
    return (!B(A1(_m1/* sbJ5 */,_m4/* sbJ8 */))) ? __Z/* EXTERNAL */ : new T2(1,_m4/* sbJ8 */,new T(function(){
      return B(_m0/* GHC.List.takeWhile */(_m1/* sbJ5 */, _m3/* sbJ7 */.b));
    }));
  }
},
_m5/* numericEnumFromTo */ = function(_m6/* svpS */, _m7/* svpT */, _m8/* svpU */, _m9/* svpV */){
  var _ma/* svpW */ = B(_lQ/* GHC.Real.$wnumericEnumFrom */(_m7/* svpT */, _m8/* svpU */)),
  _mb/* svpZ */ = new T(function(){
    var _mc/* svq0 */ = B(_7i/* GHC.Real.$p1Fractional */(_m7/* svpT */)),
    _md/* svq3 */ = new T(function(){
      return B(A3(_98/* GHC.Real./ */,_m7/* svpT */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_mc/* svq0 */, _lP/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_mc/* svq0 */, _lZ/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_6I/* GHC.Num.+ */,_mc/* svq0 */, _m9/* svpV */, _md/* svq3 */));
  });
  return new F(function(){return _m0/* GHC.List.takeWhile */(function(_me/* svq4 */){
    return new F(function(){return A3(_lX/* GHC.Classes.<= */,_m6/* svpS */, _me/* svq4 */, _mb/* svpZ */);});
  }, new T2(1,_ma/* svpW */.a,_ma/* svpW */.b));});
},
_mf/* lvl6 */ = new T(function(){
  return B(_m5/* GHC.Real.numericEnumFromTo */(_jk/* GHC.Classes.$fOrdDouble */, _ij/* GHC.Float.$fFractionalDouble */, _l8/* Lib.Object.$fNumPos_s */, _lO/* Lib.Object.lvl5 */));
}),
_mg/* go */ = function(_mh/* smIM */, _mi/* smIN */){
  while(1){
    var _mj/* smIO */ = E(_mh/* smIM */);
    if(!_mj/* smIO */._){
      return E(_mi/* smIN */);
    }else{
      _mh/* smIM */ = _mj/* smIO */.b;
      _mi/* smIN */ = _mj/* smIO */.a;
      continue;
    }
  }
},
_mk/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_ml/* last1 */ = new T(function(){
  return B(_lf/* GHC.List.errorEmptyList */(_mk/* GHC.List.lvl16 */));
}),
_mm/* $wlvl */ = function(_mn/* smIR */){
  return new F(function(){return _mg/* Lib.Object.go */(_mn/* smIR */, _ml/* GHC.List.last1 */);});
},
_mo/* lvl7 */ = function(_mp/* smIS */){
  return new F(function(){return _mm/* Lib.Object.$wlvl */(E(_mp/* smIS */).b);});
},
_mq/* map */ = function(_mr/* s3hr */, _ms/* s3hs */){
  var _mt/* s3ht */ = E(_ms/* s3hs */);
  return (_mt/* s3ht */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T(function(){
    return B(A1(_mr/* s3hr */,_mt/* s3ht */.a));
  }),new T(function(){
    return B(_mq/* GHC.Base.map */(_mr/* s3hr */, _mt/* s3ht */.b));
  }));
},
_mu/* proceedCount */ = new T(function(){
  var _mv/* s6nZ */ = eval/* EXTERNAL */("proceedCount"),
  _mw/* s6o3 */ = Number/* EXTERNAL */(_mv/* s6nZ */);
  return jsTrunc/* EXTERNAL */(_mw/* s6o3 */);
}),
_mx/* pC */ = new T(function(){
  return E(_mu/* Lib.Util.proceedCount */);
}),
_my/* $s^2 */ = 1,
_mz/* x */ = new T(function(){
  return B(_m5/* GHC.Real.numericEnumFromTo */(_jk/* GHC.Classes.$fOrdDouble */, _ij/* GHC.Float.$fFractionalDouble */, _my/* Lib.Object.$s^2 */, _mx/* Lib.Object.pC */));
}),
_mA/* $wgeneratePolygon */ = function(_mB/* smXa */, _mC/* smXb */, _mD/* smXc */, _mE/* smXd */, _mF/* smXe */){
  var _mG/* smXf */ = new T(function(){
    var _mH/* smXg */ = new T(function(){
      var _mI/* smXh */ = E(_mE/* smXd */),
      _mJ/* smXi */ = _mI/* smXh */.a,
      _mK/* smXj */ = _mI/* smXh */.b,
      _mL/* smXk */ = _mI/* smXh */.c,
      _mM/* smXl */ = E(_mF/* smXe */),
      _mN/* smXm */ = _mM/* smXl */.a,
      _mO/* smXn */ = _mM/* smXl */.b,
      _mP/* smXo */ = _mM/* smXl */.c;
      return new T3(0,new T(function(){
        return E(_mK/* smXj */)*E(_mP/* smXo */)-E(_mO/* smXn */)*E(_mL/* smXk */);
      }),new T(function(){
        return E(_mL/* smXk */)*E(_mN/* smXm */)-E(_mP/* smXo */)*E(_mJ/* smXi */);
      }),new T(function(){
        return E(_mJ/* smXi */)*E(_mO/* smXn */)-E(_mN/* smXm */)*E(_mK/* smXj */);
      }));
    }),
    _mQ/* sn2i */ = function(_mR/* smXZ */){
      var _mS/* smY0 */ = new T(function(){
        var _mT/* smY5 */ = E(_mR/* smXZ */)/E(_lc/* Lib.Object.aN */);
        return (_mT/* smY5 */+_mT/* smY5 */)*3.141592653589793;
      }),
      _mU/* smY8 */ = new T(function(){
        return B(A1(_mB/* smXa */,_mS/* smY0 */));
      }),
      _mV/* sn2h */ = new T(function(){
        var _mW/* smYb */ = new T(function(){
          return E(_mS/* smY0 */)+E(_mD/* smXc */);
        }),
        _mX/* smYh */ = new T(function(){
          return E(_mU/* smY8 */)/E(_mx/* Lib.Object.pC */);
        }),
        _mY/* smYo */ = function(_mZ/* smZR */, _n0/* smZS */){
          var _n1/* smZT */ = E(_mZ/* smZR */);
          if(!_n1/* smZT */._){
            return new T2(0,_o/* GHC.Types.[] */,_n0/* smZS */);
          }else{
            var _n2/* smZW */ = new T(function(){
              var _n3/* sn0z */ = new T(function(){
                var _n4/* smZX */ = E(_n0/* smZS */),
                _n5/* sn00 */ = E(_n4/* smZX */.a),
                _n6/* sn04 */ = E(_n4/* smZX */.b);
                return new T3(0,new T(function(){
                  return E(_n5/* sn00 */.a)+E(_n6/* sn04 */.a)*E(_mX/* smYh */);
                }),new T(function(){
                  return E(_n5/* sn00 */.b)+E(_n6/* sn04 */.b)*E(_mX/* smYh */);
                }),new T(function(){
                  return E(_n5/* sn00 */.c)+E(_n6/* sn04 */.c)*E(_mX/* smYh */);
                }));
              }),
              _n7/* sn0A */ = B(_jE/* Lib.World.$wfitP */(_jl/* Lib.Object.$sfitP1 */, _n3/* sn0z */)),
              _n8/* sn0B */ = _n7/* sn0A */.a;
              return new T2(0,new T3(0,_n8/* sn0B */,new T2(0,new T(function(){
                return E(_n1/* smZT */.a)/E(_mx/* Lib.Object.pC */);
              }),_mU/* smY8 */),_mS/* smY0 */),new T2(0,_n8/* sn0B */,new T(function(){
                var _n9/* sn0O */ = E(_n7/* sn0A */.b),
                _na/* sn0S */ = E(E(_n0/* smZS */).b),
                _nb/* sn0W */ = B(_kx/* Lib.World.$wfitR */(_jl/* Lib.Object.$sfitP1 */, _n9/* sn0O */.a, _n9/* sn0O */.b, _n9/* sn0O */.c, _na/* sn0S */.a, _na/* sn0S */.b, _na/* sn0S */.c));
                return new T3(0,_nb/* sn0W */.a,_nb/* sn0W */.b,_nb/* sn0W */.c);
              })));
            }),
            _nc/* sn12 */ = new T(function(){
              var _nd/* sn17 */ = B(_mY/* smYo */(_n1/* smZT */.b, new T(function(){
                return E(E(_n2/* smZW */).b);
              })));
              return new T2(0,_nd/* sn17 */.a,_nd/* sn17 */.b);
            });
            return new T2(0,new T2(1,new T(function(){
              return E(E(_n2/* smZW */).a);
            }),new T(function(){
              return E(E(_nc/* sn12 */).a);
            })),new T(function(){
              return E(E(_nc/* sn12 */).b);
            }));
          }
        },
        _ne/* smYn */ = function(_nf/* smYp */, _ng/* smYq */, _nh/* smYr */){
          var _ni/* smYs */ = E(_nf/* smYp */);
          if(!_ni/* smYs */._){
            return new T2(0,_o/* GHC.Types.[] */,new T2(0,_ng/* smYq */,_nh/* smYr */));
          }else{
            var _nj/* smYw */ = new T(function(){
              var _nk/* smZ6 */ = new T(function(){
                var _nl/* smYx */ = E(_ng/* smYq */),
                _nm/* smYB */ = E(_nh/* smYr */);
                return new T3(0,new T(function(){
                  return E(_nl/* smYx */.a)+E(_nm/* smYB */.a)*E(_mX/* smYh */);
                }),new T(function(){
                  return E(_nl/* smYx */.b)+E(_nm/* smYB */.b)*E(_mX/* smYh */);
                }),new T(function(){
                  return E(_nl/* smYx */.c)+E(_nm/* smYB */.c)*E(_mX/* smYh */);
                }));
              }),
              _nn/* smZ7 */ = B(_jE/* Lib.World.$wfitP */(_jl/* Lib.Object.$sfitP1 */, _nk/* smZ6 */)),
              _no/* smZ8 */ = _nn/* smZ7 */.a;
              return new T2(0,new T3(0,_no/* smZ8 */,new T2(0,new T(function(){
                return E(_ni/* smYs */.a)/E(_mx/* Lib.Object.pC */);
              }),_mU/* smY8 */),_mS/* smY0 */),new T2(0,_no/* smZ8 */,new T(function(){
                var _np/* smZi */ = E(_nn/* smZ7 */.b),
                _nq/* smZm */ = E(_nh/* smYr */),
                _nr/* smZq */ = B(_kx/* Lib.World.$wfitR */(_jl/* Lib.Object.$sfitP1 */, _np/* smZi */.a, _np/* smZi */.b, _np/* smZi */.c, _nq/* smZm */.a, _nq/* smZm */.b, _nq/* smZm */.c));
                return new T3(0,_nr/* smZq */.a,_nr/* smZq */.b,_nr/* smZq */.c);
              })));
            }),
            _ns/* smZw */ = new T(function(){
              var _nt/* smZB */ = B(_mY/* smYo */(_ni/* smYs */.b, new T(function(){
                return E(E(_nj/* smYw */).b);
              })));
              return new T2(0,_nt/* smZB */.a,_nt/* smZB */.b);
            });
            return new T2(0,new T2(1,new T(function(){
              return E(E(_nj/* smYw */).a);
            }),new T(function(){
              return E(E(_ns/* smZw */).a);
            })),new T(function(){
              return E(E(_ns/* smZw */).b);
            }));
          }
        },
        _nu/* sn2d */ = new T(function(){
          var _nv/* sn1n */ = E(_mE/* smXd */),
          _nw/* sn1r */ = E(_mH/* smXg */),
          _nx/* sn1v */ = new T(function(){
            return Math.cos/* EXTERNAL */(E(_mW/* smYb */));
          }),
          _ny/* sn1z */ = new T(function(){
            return Math.sin/* EXTERNAL */(E(_mW/* smYb */));
          });
          return new T3(0,new T(function(){
            return E(_nv/* sn1n */.a)*E(_nx/* sn1v */)+E(_nw/* sn1r */.a)*E(_ny/* sn1z */);
          }),new T(function(){
            return E(_nv/* sn1n */.b)*E(_nx/* sn1v */)+E(_nw/* sn1r */.b)*E(_ny/* sn1z */);
          }),new T(function(){
            return E(_nv/* sn1n */.c)*E(_nx/* sn1v */)+E(_nw/* sn1r */.c)*E(_ny/* sn1z */);
          }));
        });
        return E(B(_ne/* smYn */(_mz/* Lib.Object.x */, _mC/* smXb */, _nu/* sn2d */)).a);
      });
      return new T2(0,new T3(0,_mC/* smXb */,new T2(0,_l8/* Lib.Object.$fNumPos_s */,_mU/* smY8 */),_mS/* smY0 */),_mV/* sn2h */);
    };
    return B(_mq/* GHC.Base.map */(_mQ/* sn2i */, _mf/* Lib.Object.lvl6 */));
  }),
  _nz/* sn2s */ = new T(function(){
    var _nA/* sn2r */ = new T(function(){
      var _nB/* sn2o */ = B(_f/* GHC.Base.++ */(_mG/* smXf */, new T2(1,new T(function(){
        var _nC/* sn2j */ = E(_mG/* smXf */);
        if(!_nC/* sn2j */._){
          return E(_li/* GHC.List.badHead */);
        }else{
          return E(_nC/* sn2j */.a);
        }
      }),_o/* GHC.Types.[] */)));
      if(!_nB/* sn2o */._){
        return E(_lu/* GHC.List.tail1 */);
      }else{
        return E(_nB/* sn2o */.b);
      }
    },1);
    return B(_lA/* Lib.Object.go2 */(_mG/* smXf */, _nA/* sn2r */));
  });
  return new T2(0,_nz/* sn2s */,new T(function(){
    return B(_mq/* GHC.Base.map */(_mo/* Lib.Object.lvl7 */, _mG/* smXf */));
  }));
},
_nD/* $wfitO */ = function(_nE/* sn2L */, _nF/* sn2M */, _nG/* sn2N */, _nH/* sn2O */, _nI/* sn2P */, _nJ/* sn2Q */){
  var _nK/* sn2R */ = new T(function(){
    var _nL/* sn2W */ = B(_jE/* Lib.World.$wfitP */(_jl/* Lib.Object.$sfitP1 */, new T(function(){
      return E(E(_nH/* sn2O */).a);
    })));
    return new T2(0,_nL/* sn2W */.a,_nL/* sn2W */.b);
  }),
  _nM/* sn2Z */ = new T(function(){
    return E(E(_nK/* sn2R */).b);
  }),
  _nN/* sn33 */ = new T(function(){
    var _nO/* sn34 */ = E(_nM/* sn2Z */),
    _nP/* sn38 */ = E(_nJ/* sn2Q */),
    _nQ/* sn3c */ = B(_kx/* Lib.World.$wfitR */(_jl/* Lib.Object.$sfitP1 */, _nO/* sn34 */.a, _nO/* sn34 */.b, _nO/* sn34 */.c, _nP/* sn38 */.a, _nP/* sn38 */.b, _nP/* sn38 */.c));
    return new T3(0,_nQ/* sn3c */.a,_nQ/* sn3c */.b,_nQ/* sn3c */.c);
  }),
  _nR/* sn3g */ = new T(function(){
    return new T2(0,new T(function(){
      return E(E(_nK/* sn2R */).a);
    }),E(_nH/* sn2O */).b);
  }),
  _nS/* sn3o */ = new T(function(){
    var _nT/* sn3p */ = E(_nR/* sn3g */),
    _nU/* sn3s */ = B(_mA/* Lib.Object.$wgeneratePolygon */(_nE/* sn2L */, _nT/* sn3p */.a, _nT/* sn3p */.b, _nN/* sn33 */, _nM/* sn2Z */));
    return new T2(0,_nU/* sn3s */.a,_nU/* sn3s */.b);
  }),
  _nV/* sn3D */ = new T(function(){
    var _nW/* sn3v */ = E(_nI/* sn2P */);
    return new T2(0,new T(function(){
      var _nX/* sn3y */ = B(_kL/* Lib.World.$wfitV */(_iL/* GHC.Float.$fFloatingDouble */, _jk/* GHC.Classes.$fOrdDouble */, _nM/* sn2Z */, _nW/* sn3v */.a));
      return new T3(0,_nX/* sn3y */.a,_nX/* sn3y */.b,_nX/* sn3y */.c);
    }),_nW/* sn3v */.b);
  });
  return {_:0,a:_nE/* sn2L */,b:_nF/* sn2M */,c:_nG/* sn2N */,d:_nR/* sn3g */,e:_nV/* sn3D */,f:_nN/* sn33 */,g:_nM/* sn2Z */,h:new T(function(){
    return E(E(_nS/* sn3o */).a);
  }),i:new T(function(){
    return E(E(_nS/* sn3o */).b);
  })};
},
_nY/* lvl1 */ =  -1,
_nZ/* lvl2 */ = 0.5,
_o0/* lvl3 */ = new T3(0,_l8/* Lib.Object.$fNumPos_s */,_nZ/* Lib.Object.lvl2 */,_nY/* Lib.Object.lvl1 */),
_o1/* lvl4 */ = new T(function(){
  return 6.283185307179586/E(_lc/* Lib.Object.aN */);
}),
_o2/* $wmake */ = function(_o3/* sn47 */, _o4/* sn48 */, _o5/* sn49 */, _o6/* sn4a */, _o7/* sn4b */){
  var _o8/* sn4c */ = function(_o9/* sn4d */){
    var _oa/* sn4e */ = E(_o1/* Lib.Object.lvl4 */),
    _ob/* sn4g */ = 2+_o9/* sn4d */|0,
    _oc/* sn4i */ = _ob/* sn4g */-1|0,
    _od/* sn4j */ = (2+_o9/* sn4d */)*(1+_o9/* sn4d */),
    _oe/* sn4o */ = E(_mf/* Lib.Object.lvl6 */);
    if(!_oe/* sn4o */._){
      return _oa/* sn4e */*0;
    }else{
      var _of/* sn4p */ = _oe/* sn4o */.a,
      _og/* sn4q */ = _oe/* sn4o */.b,
      _oh/* sn4y */ = B(A1(_o3/* sn47 */,new T(function(){
        return 6.283185307179586*E(_of/* sn4p */)/E(_lc/* Lib.Object.aN */);
      }))),
      _oi/* sn4I */ = B(A1(_o3/* sn47 */,new T(function(){
        return 6.283185307179586*(E(_of/* sn4p */)+1)/E(_lc/* Lib.Object.aN */);
      })));
      if(_oh/* sn4y */!=_oi/* sn4I */){
        if(_ob/* sn4g */>=0){
          var _oj/* sn4O */ = E(_ob/* sn4g */);
          if(!_oj/* sn4O */){
            var _ok/* sn5K */ = function(_ol/*  sn5L */, _om/*  sn5M */){
              while(1){
                var _on/*  sn5K */ = B((function(_oo/* sn5L */, _op/* sn5M */){
                  var _oq/* sn5N */ = E(_oo/* sn5L */);
                  if(!_oq/* sn5N */._){
                    return E(_op/* sn5M */);
                  }else{
                    var _or/* sn5O */ = _oq/* sn5N */.a,
                    _os/* sn5P */ = _oq/* sn5N */.b,
                    _ot/* sn5X */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*E(_or/* sn5O */)/E(_lc/* Lib.Object.aN */);
                    }))),
                    _ou/* sn67 */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*(E(_or/* sn5O */)+1)/E(_lc/* Lib.Object.aN */);
                    })));
                    if(_ot/* sn5X */!=_ou/* sn67 */){
                      var _ov/*   sn5M */ = _op/* sn5M */+0/(_ot/* sn5X */-_ou/* sn67 */)/_od/* sn4j */;
                      _ol/*  sn5L */ = _os/* sn5P */;
                      _om/*  sn5M */ = _ov/*   sn5M */;
                      return __continue/* EXTERNAL */;
                    }else{
                      if(_oc/* sn4i */>=0){
                        var _ow/* sn6h */ = E(_oc/* sn4i */);
                        if(!_ow/* sn6h */){
                          var _ov/*   sn5M */ = _op/* sn5M */+_ob/* sn4g *//_od/* sn4j */;
                          _ol/*  sn5L */ = _os/* sn5P */;
                          _om/*  sn5M */ = _ov/*   sn5M */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _ov/*   sn5M */ = _op/* sn5M */+_ob/* sn4g */*B(_hs/* Lib.Object.$wf */(_ot/* sn5X */, _ow/* sn6h */))/_od/* sn4j */;
                          _ol/*  sn5L */ = _os/* sn5P */;
                          _om/*  sn5M */ = _ov/*   sn5M */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hj/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_ol/*  sn5L */, _om/*  sn5M */));
                if(_on/*  sn5K */!=__continue/* EXTERNAL */){
                  return _on/*  sn5K */;
                }
              }
            };
            return _oa/* sn4e */*B(_ok/* sn5K */(_og/* sn4q */, 0/(_oh/* sn4y */-_oi/* sn4I */)/_od/* sn4j */));
          }else{
            var _ox/* sn4V */ = function(_oy/*  sn4W */, _oz/*  sn4X */){
              while(1){
                var _oA/*  sn4V */ = B((function(_oB/* sn4W */, _oC/* sn4X */){
                  var _oD/* sn4Y */ = E(_oB/* sn4W */);
                  if(!_oD/* sn4Y */._){
                    return E(_oC/* sn4X */);
                  }else{
                    var _oE/* sn4Z */ = _oD/* sn4Y */.a,
                    _oF/* sn50 */ = _oD/* sn4Y */.b,
                    _oG/* sn58 */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*E(_oE/* sn4Z */)/E(_lc/* Lib.Object.aN */);
                    }))),
                    _oH/* sn5i */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*(E(_oE/* sn4Z */)+1)/E(_lc/* Lib.Object.aN */);
                    })));
                    if(_oG/* sn58 */!=_oH/* sn5i */){
                      if(_oj/* sn4O */>=0){
                        var _oI/*   sn4X */ = _oC/* sn4X */+(B(_hs/* Lib.Object.$wf */(_oG/* sn58 */, _oj/* sn4O */))-B(_hs/* Lib.Object.$wf */(_oH/* sn5i */, _oj/* sn4O */)))/(_oG/* sn58 */-_oH/* sn5i */)/_od/* sn4j */;
                        _oy/*  sn4W */ = _oF/* sn50 */;
                        _oz/*  sn4X */ = _oI/*   sn4X */;
                        return __continue/* EXTERNAL */;
                      }else{
                        return E(_hj/* Lib.Object.$s^1 */);
                      }
                    }else{
                      if(_oc/* sn4i */>=0){
                        var _oJ/* sn5y */ = E(_oc/* sn4i */);
                        if(!_oJ/* sn5y */){
                          var _oI/*   sn4X */ = _oC/* sn4X */+_ob/* sn4g *//_od/* sn4j */;
                          _oy/*  sn4W */ = _oF/* sn50 */;
                          _oz/*  sn4X */ = _oI/*   sn4X */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _oI/*   sn4X */ = _oC/* sn4X */+_ob/* sn4g */*B(_hs/* Lib.Object.$wf */(_oG/* sn58 */, _oJ/* sn5y */))/_od/* sn4j */;
                          _oy/*  sn4W */ = _oF/* sn50 */;
                          _oz/*  sn4X */ = _oI/*   sn4X */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hj/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_oy/*  sn4W */, _oz/*  sn4X */));
                if(_oA/*  sn4V */!=__continue/* EXTERNAL */){
                  return _oA/*  sn4V */;
                }
              }
            };
            return _oa/* sn4e */*B(_ox/* sn4V */(_og/* sn4q */, (B(_hs/* Lib.Object.$wf */(_oh/* sn4y */, _oj/* sn4O */))-B(_hs/* Lib.Object.$wf */(_oi/* sn4I */, _oj/* sn4O */)))/(_oh/* sn4y */-_oi/* sn4I */)/_od/* sn4j */));
          }
        }else{
          return E(_hj/* Lib.Object.$s^1 */);
        }
      }else{
        if(_oc/* sn4i */>=0){
          var _oK/* sn6t */ = E(_oc/* sn4i */);
          if(!_oK/* sn6t */){
            var _oL/* sn7m */ = function(_oM/*  sn7n */, _oN/*  sn7o */){
              while(1){
                var _oO/*  sn7m */ = B((function(_oP/* sn7n */, _oQ/* sn7o */){
                  var _oR/* sn7p */ = E(_oP/* sn7n */);
                  if(!_oR/* sn7p */._){
                    return E(_oQ/* sn7o */);
                  }else{
                    var _oS/* sn7q */ = _oR/* sn7p */.a,
                    _oT/* sn7r */ = _oR/* sn7p */.b,
                    _oU/* sn7z */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*E(_oS/* sn7q */)/E(_lc/* Lib.Object.aN */);
                    }))),
                    _oV/* sn7J */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*(E(_oS/* sn7q */)+1)/E(_lc/* Lib.Object.aN */);
                    })));
                    if(_oU/* sn7z */!=_oV/* sn7J */){
                      if(_ob/* sn4g */>=0){
                        var _oW/* sn7P */ = E(_ob/* sn4g */);
                        if(!_oW/* sn7P */){
                          var _oX/*   sn7o */ = _oQ/* sn7o */+0/(_oU/* sn7z */-_oV/* sn7J */)/_od/* sn4j */;
                          _oM/*  sn7n */ = _oT/* sn7r */;
                          _oN/*  sn7o */ = _oX/*   sn7o */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _oX/*   sn7o */ = _oQ/* sn7o */+(B(_hs/* Lib.Object.$wf */(_oU/* sn7z */, _oW/* sn7P */))-B(_hs/* Lib.Object.$wf */(_oV/* sn7J */, _oW/* sn7P */)))/(_oU/* sn7z */-_oV/* sn7J */)/_od/* sn4j */;
                          _oM/*  sn7n */ = _oT/* sn7r */;
                          _oN/*  sn7o */ = _oX/*   sn7o */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hj/* Lib.Object.$s^1 */);
                      }
                    }else{
                      var _oX/*   sn7o */ = _oQ/* sn7o */+_ob/* sn4g *//_od/* sn4j */;
                      _oM/*  sn7n */ = _oT/* sn7r */;
                      _oN/*  sn7o */ = _oX/*   sn7o */;
                      return __continue/* EXTERNAL */;
                    }
                  }
                })(_oM/*  sn7n */, _oN/*  sn7o */));
                if(_oO/*  sn7m */!=__continue/* EXTERNAL */){
                  return _oO/*  sn7m */;
                }
              }
            };
            return _oa/* sn4e */*B(_oL/* sn7m */(_og/* sn4q */, _ob/* sn4g *//_od/* sn4j */));
          }else{
            var _oY/* sn6x */ = function(_oZ/*  sn6y */, _p0/*  sn6z */){
              while(1){
                var _p1/*  sn6x */ = B((function(_p2/* sn6y */, _p3/* sn6z */){
                  var _p4/* sn6A */ = E(_p2/* sn6y */);
                  if(!_p4/* sn6A */._){
                    return E(_p3/* sn6z */);
                  }else{
                    var _p5/* sn6B */ = _p4/* sn6A */.a,
                    _p6/* sn6C */ = _p4/* sn6A */.b,
                    _p7/* sn6K */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*E(_p5/* sn6B */)/E(_lc/* Lib.Object.aN */);
                    }))),
                    _p8/* sn6U */ = B(A1(_o3/* sn47 */,new T(function(){
                      return 6.283185307179586*(E(_p5/* sn6B */)+1)/E(_lc/* Lib.Object.aN */);
                    })));
                    if(_p7/* sn6K */!=_p8/* sn6U */){
                      if(_ob/* sn4g */>=0){
                        var _p9/* sn70 */ = E(_ob/* sn4g */);
                        if(!_p9/* sn70 */){
                          var _pa/*   sn6z */ = _p3/* sn6z */+0/(_p7/* sn6K */-_p8/* sn6U */)/_od/* sn4j */;
                          _oZ/*  sn6y */ = _p6/* sn6C */;
                          _p0/*  sn6z */ = _pa/*   sn6z */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _pa/*   sn6z */ = _p3/* sn6z */+(B(_hs/* Lib.Object.$wf */(_p7/* sn6K */, _p9/* sn70 */))-B(_hs/* Lib.Object.$wf */(_p8/* sn6U */, _p9/* sn70 */)))/(_p7/* sn6K */-_p8/* sn6U */)/_od/* sn4j */;
                          _oZ/*  sn6y */ = _p6/* sn6C */;
                          _p0/*  sn6z */ = _pa/*   sn6z */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hj/* Lib.Object.$s^1 */);
                      }
                    }else{
                      if(_oK/* sn6t */>=0){
                        var _pa/*   sn6z */ = _p3/* sn6z */+_ob/* sn4g */*B(_hs/* Lib.Object.$wf */(_p7/* sn6K */, _oK/* sn6t */))/_od/* sn4j */;
                        _oZ/*  sn6y */ = _p6/* sn6C */;
                        _p0/*  sn6z */ = _pa/*   sn6z */;
                        return __continue/* EXTERNAL */;
                      }else{
                        return E(_hj/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_oZ/*  sn6y */, _p0/*  sn6z */));
                if(_p1/*  sn6x */!=__continue/* EXTERNAL */){
                  return _p1/*  sn6x */;
                }
              }
            };
            return _oa/* sn4e */*B(_oY/* sn6x */(_og/* sn4q */, _ob/* sn4g */*B(_hs/* Lib.Object.$wf */(_oh/* sn4y */, _oK/* sn6t */))/_od/* sn4j */));
          }
        }else{
          return E(_hj/* Lib.Object.$s^1 */);
        }
      }
    }
  },
  _pb/* sn86 */ = new T(function(){
    return 1/(B(_o8/* sn4c */(1))*E(_o4/* sn48 */));
  });
  return new F(function(){return _nD/* Lib.Object.$wfitO */(_o3/* sn47 */, _o0/* Lib.Object.lvl3 */, new T2(0,new T3(0,_pb/* sn86 */,_pb/* sn86 */,_pb/* sn86 */),new T(function(){
    return 1/(B(_o8/* sn4c */(3))*E(_o4/* sn48 */));
  })), _o5/* sn49 */, _o6/* sn4a */, _o7/* sn4b */);});
},
_pc/* initial17 */ = 1.2,
_pd/* initial22 */ =  -0.2,
_pe/* initial7 */ = 1,
_pf/* initial8 */ = 0,
_pg/* initial21 */ = new T3(0,_pd/* Main.initial22 */,_pf/* Main.initial8 */,_pe/* Main.initial7 */),
_ph/* initial20 */ = new T2(0,_pg/* Main.initial21 */,_pf/* Main.initial8 */),
_pi/* initial25 */ = 0.5,
_pj/* initial26 */ =  -0.8,
_pk/* initial24 */ = new T3(0,_pj/* Main.initial26 */,_pi/* Main.initial25 */,_pf/* Main.initial8 */),
_pl/* initial23 */ = new T2(0,_pk/* Main.initial24 */,_pf/* Main.initial8 */),
_pm/* initial_r */ = 0.2,
_pn/* initial27 */ = function(_po/* s5gK */){
  return E(_pm/* Main.initial_r */);
},
_pp/* initial_ra */ = new T3(0,_pf/* Main.initial8 */,_pf/* Main.initial8 */,_pe/* Main.initial7 */),
_pq/* initial19 */ = new T(function(){
  var _pr/* s5gL */ = B(_o2/* Lib.Object.$wmake */(_pn/* Main.initial27 */, _pc/* Main.initial17 */, _pl/* Main.initial23 */, _ph/* Main.initial20 */, _pp/* Main.initial_ra */));
  return {_:0,a:_pr/* s5gL */.a,b:_pr/* s5gL */.b,c:_pr/* s5gL */.c,d:_pr/* s5gL */.d,e:_pr/* s5gL */.e,f:_pr/* s5gL */.f,g:_pr/* s5gL */.g,h:_pr/* s5gL */.h,i:_pr/* s5gL */.i};
}),
_ps/* initial4 */ = 0,
_pt/* initial16 */ = 1.3,
_pu/* initial15 */ = new T3(0,_pt/* Main.initial16 */,_pf/* Main.initial8 */,_pf/* Main.initial8 */),
_pv/* initial14 */ = new T2(0,_pu/* Main.initial15 */,_pf/* Main.initial8 */),
_pw/* decodeDoubleInteger */ = function(_px/* s1ID */){
  var _py/* s1IF */ = I_decodeDouble/* EXTERNAL */(_px/* s1ID */);
  return new T2(0,new T1(1,_py/* s1IF */.b),_py/* s1IF */.a);
},
_pz/* smallInteger */ = function(_pA/* B1 */){
  return new T1(0,_pA/* B1 */);
},
_pB/* int64ToInteger */ = function(_pC/* s1RA */){
  var _pD/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _pE/* s1RG */ = hs_leInt64/* EXTERNAL */(_pC/* s1RA */, _pD/* s1RC */);
  if(!_pE/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_pC/* s1RA */));
  }else{
    var _pF/* s1RN */ = hs_intToInt64/* EXTERNAL */( -2147483648),
    _pG/* s1RR */ = hs_geInt64/* EXTERNAL */(_pC/* s1RA */, _pF/* s1RN */);
    if(!_pG/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_pC/* s1RA */));
    }else{
      var _pH/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_pC/* s1RA */);
      return new F(function(){return _pz/* GHC.Integer.Type.smallInteger */(_pH/* s1RY */);});
    }
  }
},
_pI/* zeroCountArr */ = new T(function(){
  var _pJ/* s9bR */ = newByteArr/* EXTERNAL */(256),
  _pK/* s9bT */ = _pJ/* s9bR */,
  _/* EXTERNAL */ = _pK/* s9bT */["v"]["i8"][0] = 8,
  _pL/* s9bV */ = function(_pM/* s9bW */, _pN/* s9bX */, _pO/* s9bY */, _/* EXTERNAL */){
    while(1){
      if(_pO/* s9bY */>=256){
        if(_pM/* s9bW */>=256){
          return E(_/* EXTERNAL */);
        }else{
          var _pP/*  s9bW */ = imul/* EXTERNAL */(2, _pM/* s9bW */)|0,
          _pQ/*  s9bX */ = _pN/* s9bX */+1|0,
          _pR/*  s9bY */ = _pM/* s9bW */;
          _pM/* s9bW */ = _pP/*  s9bW */;
          _pN/* s9bX */ = _pQ/*  s9bX */;
          _pO/* s9bY */ = _pR/*  s9bY */;
          continue;
        }
      }else{
        var _/* EXTERNAL */ = _pK/* s9bT */["v"]["i8"][_pO/* s9bY */] = _pN/* s9bX */,
        _pR/*  s9bY */ = _pO/* s9bY */+_pM/* s9bW */|0;
        _pO/* s9bY */ = _pR/*  s9bY */;
        continue;
      }
    }
  },
  _/* EXTERNAL */ = B(_pL/* s9bV */(2, 0, 1, _/* EXTERNAL */));
  return _pK/* s9bT */;
}),
_pS/* elim64# */ = function(_pT/* s9cN */, _pU/* s9cO */){
  var _pV/* s9cQ */ = hs_int64ToInt/* EXTERNAL */(_pT/* s9cN */),
  _pW/* s9cT */ = E(_pI/* GHC.Float.ConversionUtils.zeroCountArr */),
  _pX/* s9cY */ = _pW/* s9cT */["v"]["i8"][(255&_pV/* s9cQ */>>>0)>>>0&4294967295];
  if(_pU/* s9cO */>_pX/* s9cY */){
    if(_pX/* s9cY */>=8){
      var _pY/* s9d4 */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_pT/* s9cN */, 8),
      _pZ/* s9d7 */ = function(_q0/*  s9d8 */, _q1/*  s9d9 */){
        while(1){
          var _q2/*  s9d7 */ = B((function(_q3/* s9d8 */, _q4/* s9d9 */){
            var _q5/* s9db */ = hs_int64ToInt/* EXTERNAL */(_q3/* s9d8 */),
            _q6/* s9dh */ = _pW/* s9cT */["v"]["i8"][(255&_q5/* s9db */>>>0)>>>0&4294967295];
            if(_q4/* s9d9 */>_q6/* s9dh */){
              if(_q6/* s9dh */>=8){
                var _q7/* s9dn */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_q3/* s9d8 */, 8),
                _q8/*   s9d9 */ = _q4/* s9d9 */-8|0;
                _q0/*  s9d8 */ = _q7/* s9dn */;
                _q1/*  s9d9 */ = _q8/*   s9d9 */;
                return __continue/* EXTERNAL */;
              }else{
                return new T2(0,new T(function(){
                  var _q9/* s9ds */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_q3/* s9d8 */, _q6/* s9dh */);
                  return B(_pB/* GHC.Integer.Type.int64ToInteger */(_q9/* s9ds */));
                }),_q4/* s9d9 */-_q6/* s9dh */|0);
              }
            }else{
              return new T2(0,new T(function(){
                var _qa/* s9dy */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_q3/* s9d8 */, _q4/* s9d9 */);
                return B(_pB/* GHC.Integer.Type.int64ToInteger */(_qa/* s9dy */));
              }),0);
            }
          })(_q0/*  s9d8 */, _q1/*  s9d9 */));
          if(_q2/*  s9d7 */!=__continue/* EXTERNAL */){
            return _q2/*  s9d7 */;
          }
        }
      };
      return new F(function(){return _pZ/* s9d7 */(_pY/* s9d4 */, _pU/* s9cO */-8|0);});
    }else{
      return new T2(0,new T(function(){
        var _qb/* s9dE */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_pT/* s9cN */, _pX/* s9cY */);
        return B(_pB/* GHC.Integer.Type.int64ToInteger */(_qb/* s9dE */));
      }),_pU/* s9cO */-_pX/* s9cY */|0);
    }
  }else{
    return new T2(0,new T(function(){
      var _qc/* s9dK */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_pT/* s9cN */, _pU/* s9cO */);
      return B(_pB/* GHC.Integer.Type.int64ToInteger */(_qc/* s9dK */));
    }),0);
  }
},
_qd/* intToInt64# */ = function(_qe/* sf6 */){
  var _qf/* sf8 */ = hs_intToInt64/* EXTERNAL */(_qe/* sf6 */);
  return E(_qf/* sf8 */);
},
_qg/* integerToInt64 */ = function(_qh/* s1S1 */){
  var _qi/* s1S2 */ = E(_qh/* s1S1 */);
  if(!_qi/* s1S2 */._){
    return new F(function(){return _qd/* GHC.IntWord64.intToInt64# */(_qi/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_qi/* s1S2 */.a);});
  }
},
_qj/* integer2Word# */ = function(_qk/* s2C */){
  return I_toInt/* EXTERNAL */(_qk/* s2C */)>>>0;
},
_ql/* integerToWord */ = function(_qm/* s1Rr */){
  var _qn/* s1Rs */ = E(_qm/* s1Rr */);
  if(!_qn/* s1Rs */._){
    return _qn/* s1Rs */.a>>>0;
  }else{
    return new F(function(){return _qj/* GHC.Integer.GMP.Prim.integer2Word# */(_qn/* s1Rs */.a);});
  }
},
_qo/* $w$ctoRational */ = function(_qp/* s1l6D */){
  var _qq/* s1l6E */ = B(_pw/* GHC.Integer.Type.decodeDoubleInteger */(_qp/* s1l6D */)),
  _qr/* s1l6F */ = _qq/* s1l6E */.a,
  _qs/* s1l6G */ = _qq/* s1l6E */.b;
  if(_qs/* s1l6G */<0){
    var _qt/* s1l6K */ = function(_qu/* s1l6L */){
      if(!_qu/* s1l6L */){
        return new T2(0,E(_qr/* s1l6F */),B(_3u/* GHC.Integer.Type.shiftLInteger */(_1M/* GHC.Float.$fRealDouble1 */,  -_qs/* s1l6G */)));
      }else{
        var _qv/* s1l6S */ = B(_pS/* GHC.Float.ConversionUtils.elim64# */(B(_qg/* GHC.Integer.Type.integerToInt64 */(_qr/* s1l6F */)),  -_qs/* s1l6G */));
        return new T2(0,E(_qv/* s1l6S */.a),B(_3u/* GHC.Integer.Type.shiftLInteger */(_1M/* GHC.Float.$fRealDouble1 */, _qv/* s1l6S */.b)));
      }
    };
    if(!((B(_ql/* GHC.Integer.Type.integerToWord */(_qr/* s1l6F */))&1)>>>0)){
      return new F(function(){return _qt/* s1l6K */(1);});
    }else{
      return new F(function(){return _qt/* s1l6K */(0);});
    }
  }else{
    return new T2(0,B(_3u/* GHC.Integer.Type.shiftLInteger */(_qr/* s1l6F */, _qs/* s1l6G */)),_1M/* GHC.Float.$fRealDouble1 */);
  }
},
_qw/* $fRealDouble_$ctoRational */ = function(_qx/* s1l6Z */){
  var _qy/* s1l72 */ = B(_qo/* GHC.Float.$w$ctoRational */(E(_qx/* s1l6Z */)));
  return new T2(0,E(_qy/* s1l72 */.a),E(_qy/* s1l72 */.b));
},
_qz/* $fRealDouble */ = new T3(0,_if/* GHC.Float.$fNumDouble */,_jk/* GHC.Classes.$fOrdDouble */,_qw/* GHC.Float.$fRealDouble_$ctoRational */),
_qA/* $p1Integral */ = function(_qB/* sv9T */){
  return E(E(_qB/* sv9T */).a);
},
_qC/* $p1Real */ = function(_qD/* svbu */){
  return E(E(_qD/* svbu */).a);
},
_qE/* eftInt */ = function(_qF/* smlE */, _qG/* smlF */){
  if(_qF/* smlE */<=_qG/* smlF */){
    var _qH/* smlI */ = function(_qI/* smlJ */){
      return new T2(1,_qI/* smlJ */,new T(function(){
        if(_qI/* smlJ */!=_qG/* smlF */){
          return B(_qH/* smlI */(_qI/* smlJ */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _qH/* smlI */(_qF/* smlE */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_qJ/* $fEnumInt_$cenumFrom */ = function(_qK/* smzP */){
  return new F(function(){return _qE/* GHC.Enum.eftInt */(E(_qK/* smzP */), 2147483647);});
},
_qL/* efdtIntDn */ = function(_qM/* smkb */, _qN/* smkc */, _qO/* smkd */){
  if(_qO/* smkd */<=_qN/* smkc */){
    var _qP/* smkr */ = new T(function(){
      var _qQ/* smkh */ = _qN/* smkc */-_qM/* smkb */|0,
      _qR/* smkj */ = function(_qS/* smkk */){
        return (_qS/* smkk */>=(_qO/* smkd */-_qQ/* smkh */|0)) ? new T2(1,_qS/* smkk */,new T(function(){
          return B(_qR/* smkj */(_qS/* smkk */+_qQ/* smkh */|0));
        })) : new T2(1,_qS/* smkk */,_o/* GHC.Types.[] */);
      };
      return B(_qR/* smkj */(_qN/* smkc */));
    });
    return new T2(1,_qM/* smkb */,_qP/* smkr */);
  }else{
    return (_qO/* smkd */<=_qM/* smkb */) ? new T2(1,_qM/* smkb */,_o/* GHC.Types.[] */) : __Z/* EXTERNAL */;
  }
},
_qT/* efdtIntUp */ = function(_qU/* smkR */, _qV/* smkS */, _qW/* smkT */){
  if(_qW/* smkT */>=_qV/* smkS */){
    var _qX/* sml7 */ = new T(function(){
      var _qY/* smkX */ = _qV/* smkS */-_qU/* smkR */|0,
      _qZ/* smkZ */ = function(_r0/* sml0 */){
        return (_r0/* sml0 */<=(_qW/* smkT */-_qY/* smkX */|0)) ? new T2(1,_r0/* sml0 */,new T(function(){
          return B(_qZ/* smkZ */(_r0/* sml0 */+_qY/* smkX */|0));
        })) : new T2(1,_r0/* sml0 */,_o/* GHC.Types.[] */);
      };
      return B(_qZ/* smkZ */(_qV/* smkS */));
    });
    return new T2(1,_qU/* smkR */,_qX/* sml7 */);
  }else{
    return (_qW/* smkT */>=_qU/* smkR */) ? new T2(1,_qU/* smkR */,_o/* GHC.Types.[] */) : __Z/* EXTERNAL */;
  }
},
_r1/* efdInt */ = function(_r2/* smln */, _r3/* smlo */){
  if(_r3/* smlo */<_r2/* smln */){
    return new F(function(){return _qL/* GHC.Enum.efdtIntDn */(_r2/* smln */, _r3/* smlo */,  -2147483648);});
  }else{
    return new F(function(){return _qT/* GHC.Enum.efdtIntUp */(_r2/* smln */, _r3/* smlo */, 2147483647);});
  }
},
_r4/* $fEnumInt_$cenumFromThen */ = function(_r5/* smzJ */, _r6/* smzK */){
  return new F(function(){return _r1/* GHC.Enum.efdInt */(E(_r5/* smzJ */), E(_r6/* smzK */));});
},
_r7/* efdtInt */ = function(_r8/* smli */, _r9/* smlj */, _ra/* smlk */){
  if(_r9/* smlj */<_r8/* smli */){
    return new F(function(){return _qL/* GHC.Enum.efdtIntDn */(_r8/* smli */, _r9/* smlj */, _ra/* smlk */);});
  }else{
    return new F(function(){return _qT/* GHC.Enum.efdtIntUp */(_r8/* smli */, _r9/* smlj */, _ra/* smlk */);});
  }
},
_rb/* $fEnumInt_$cenumFromThenTo */ = function(_rc/* smzu */, _rd/* smzv */, _re/* smzw */){
  return new F(function(){return _r7/* GHC.Enum.efdtInt */(E(_rc/* smzu */), E(_rd/* smzv */), E(_re/* smzw */));});
},
_rf/* $fEnumInt_$cenumFromTo */ = function(_rg/* smzD */, _rh/* smzE */){
  return new F(function(){return _qE/* GHC.Enum.eftInt */(E(_rg/* smzD */), E(_rh/* smzE */));});
},
_ri/* $fEnumInt_$cfromEnum */ = function(_rj/* smzS */){
  return E(_rj/* smzS */);
},
_rk/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));
}),
_rl/* $fEnumInt1 */ = new T(function(){
  return B(err/* EXTERNAL */(_rk/* GHC.Enum.lvl28 */));
}),
_rm/* $fEnumInt_$cpred */ = function(_rn/* smAv */){
  var _ro/* smAy */ = E(_rn/* smAv */);
  return (_ro/* smAy */==( -2147483648)) ? E(_rl/* GHC.Enum.$fEnumInt1 */) : _ro/* smAy */-1|0;
},
_rp/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));
}),
_rq/* $fEnumInt2 */ = new T(function(){
  return B(err/* EXTERNAL */(_rp/* GHC.Enum.lvl27 */));
}),
_rr/* $fEnumInt_$csucc */ = function(_rs/* smAq */){
  var _rt/* smAt */ = E(_rs/* smAq */);
  return (_rt/* smAt */==2147483647) ? E(_rq/* GHC.Enum.$fEnumInt2 */) : _rt/* smAt */+1|0;
},
_ru/* $fEnumInt */ = {_:0,a:_rr/* GHC.Enum.$fEnumInt_$csucc */,b:_rm/* GHC.Enum.$fEnumInt_$cpred */,c:_ri/* GHC.Enum.$fEnumInt_$cfromEnum */,d:_ri/* GHC.Enum.$fEnumInt_$cfromEnum */,e:_qJ/* GHC.Enum.$fEnumInt_$cenumFrom */,f:_r4/* GHC.Enum.$fEnumInt_$cenumFromThen */,g:_rf/* GHC.Enum.$fEnumInt_$cenumFromTo */,h:_rb/* GHC.Enum.$fEnumInt_$cenumFromThenTo */},
_rv/* divInt# */ = function(_rw/* scDT */, _rx/* scDU */){
  if(_rw/* scDT */<=0){
    if(_rw/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_rw/* scDT */, _rx/* scDU */);});
    }else{
      if(_rx/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_rw/* scDT */, _rx/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_rw/* scDT */+1|0, _rx/* scDU */)-1|0;
      }
    }
  }else{
    if(_rx/* scDU */>=0){
      if(_rw/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_rw/* scDT */, _rx/* scDU */);});
      }else{
        if(_rx/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_rw/* scDT */, _rx/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_rw/* scDT */+1|0, _rx/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_rw/* scDT */-1|0, _rx/* scDU */)-1|0;
    }
  }
},
_ry/* Overflow */ = 0,
_rz/* overflowException */ = new T(function(){
  return B(_2R/* GHC.Exception.$fExceptionArithException_$ctoException */(_ry/* GHC.Exception.Overflow */));
}),
_rA/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_rz/* GHC.Exception.overflowException */);
}),
_rB/* $w$cdiv */ = function(_rC/* svjX */, _rD/* svjY */){
  var _rE/* svjZ */ = E(_rD/* svjY */);
  switch(_rE/* svjZ */){
    case  -1:
      var _rF/* svk0 */ = E(_rC/* svjX */);
      if(_rF/* svk0 */==( -2147483648)){
        return E(_rA/* GHC.Real.overflowError */);
      }else{
        return new F(function(){return _rv/* GHC.Classes.divInt# */(_rF/* svk0 */,  -1);});
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return _rv/* GHC.Classes.divInt# */(_rC/* svjX */, _rE/* svjZ */);});
  }
},
_rG/* $fIntegralInt_$cdiv */ = function(_rH/* svk3 */, _rI/* svk4 */){
  return new F(function(){return _rB/* GHC.Real.$w$cdiv */(E(_rH/* svk3 */), E(_rI/* svk4 */));});
},
_rJ/* $fIntegralInt1 */ = 0,
_rK/* lvl2 */ = new T2(0,_rA/* GHC.Real.overflowError */,_rJ/* GHC.Real.$fIntegralInt1 */),
_rL/* $fIntegralInt_$cdivMod */ = function(_rM/* svi2 */, _rN/* svi3 */){
  var _rO/* svi4 */ = E(_rM/* svi2 */),
  _rP/* svi8 */ = E(_rN/* svi3 */);
  switch(_rP/* svi8 */){
    case  -1:
      var _rQ/* svj6 */ = E(_rO/* svi4 */);
      if(_rQ/* svj6 */==( -2147483648)){
        return E(_rK/* GHC.Real.lvl2 */);
      }else{
        if(_rQ/* svj6 */<=0){
          if(_rQ/* svj6 */>=0){
            var _rR/* svjb */ = quotRemI/* EXTERNAL */(_rQ/* svj6 */,  -1);
            return new T2(0,_rR/* svjb */.a,_rR/* svjb */.b);
          }else{
            var _rS/* svjg */ = quotRemI/* EXTERNAL */(_rQ/* svj6 */,  -1);
            return new T2(0,_rS/* svjg */.a,_rS/* svjg */.b);
          }
        }else{
          var _rT/* svjm */ = quotRemI/* EXTERNAL */(_rQ/* svj6 */-1|0,  -1);
          return new T2(0,_rT/* svjm */.a-1|0,(_rT/* svjm */.b+( -1)|0)+1|0);
        }
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      if(_rO/* svi4 */<=0){
        if(_rO/* svi4 */>=0){
          var _rU/* svid */ = quotRemI/* EXTERNAL */(_rO/* svi4 */, _rP/* svi8 */);
          return new T2(0,_rU/* svid */.a,_rU/* svid */.b);
        }else{
          if(_rP/* svi8 */<=0){
            var _rV/* svik */ = quotRemI/* EXTERNAL */(_rO/* svi4 */, _rP/* svi8 */);
            return new T2(0,_rV/* svik */.a,_rV/* svik */.b);
          }else{
            var _rW/* sviq */ = quotRemI/* EXTERNAL */(_rO/* svi4 */+1|0, _rP/* svi8 */);
            return new T2(0,_rW/* sviq */.a-1|0,(_rW/* sviq */.b+_rP/* svi8 */|0)-1|0);
          }
        }
      }else{
        if(_rP/* svi8 */>=0){
          if(_rO/* svi4 */>=0){
            var _rX/* sviC */ = quotRemI/* EXTERNAL */(_rO/* svi4 */, _rP/* svi8 */);
            return new T2(0,_rX/* sviC */.a,_rX/* sviC */.b);
          }else{
            if(_rP/* svi8 */<=0){
              var _rY/* sviJ */ = quotRemI/* EXTERNAL */(_rO/* svi4 */, _rP/* svi8 */);
              return new T2(0,_rY/* sviJ */.a,_rY/* sviJ */.b);
            }else{
              var _rZ/* sviP */ = quotRemI/* EXTERNAL */(_rO/* svi4 */+1|0, _rP/* svi8 */);
              return new T2(0,_rZ/* sviP */.a-1|0,(_rZ/* sviP */.b+_rP/* svi8 */|0)-1|0);
            }
          }
        }else{
          var _s0/* sviY */ = quotRemI/* EXTERNAL */(_rO/* svi4 */-1|0, _rP/* svi8 */);
          return new T2(0,_s0/* sviY */.a-1|0,(_s0/* sviY */.b+_rP/* svi8 */|0)+1|0);
        }
      }
  }
},
_s1/* modInt# */ = function(_s2/* scF6 */, _s3/* scF7 */){
  var _s4/* scF8 */ = _s2/* scF6 */%_s3/* scF7 */;
  if(_s2/* scF6 */<=0){
    if(_s2/* scF6 */>=0){
      return E(_s4/* scF8 */);
    }else{
      if(_s3/* scF7 */<=0){
        return E(_s4/* scF8 */);
      }else{
        var _s5/* scFf */ = E(_s4/* scF8 */);
        return (_s5/* scFf */==0) ? 0 : _s5/* scFf */+_s3/* scF7 */|0;
      }
    }
  }else{
    if(_s3/* scF7 */>=0){
      if(_s2/* scF6 */>=0){
        return E(_s4/* scF8 */);
      }else{
        if(_s3/* scF7 */<=0){
          return E(_s4/* scF8 */);
        }else{
          var _s6/* scFm */ = E(_s4/* scF8 */);
          return (_s6/* scFm */==0) ? 0 : _s6/* scFm */+_s3/* scF7 */|0;
        }
      }
    }else{
      var _s7/* scFn */ = E(_s4/* scF8 */);
      return (_s7/* scFn */==0) ? 0 : _s7/* scFn */+_s3/* scF7 */|0;
    }
  }
},
_s8/* $fIntegralInt_$cmod */ = function(_s9/* svjO */, _sa/* svjP */){
  var _sb/* svjS */ = E(_sa/* svjP */);
  switch(_sb/* svjS */){
    case  -1:
      return E(_rJ/* GHC.Real.$fIntegralInt1 */);
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return _s1/* GHC.Classes.modInt# */(E(_s9/* svjO */), _sb/* svjS */);});
  }
},
_sc/* $fIntegralInt_$cquot */ = function(_sd/* svki */, _se/* svkj */){
  var _sf/* svkk */ = E(_sd/* svki */),
  _sg/* svko */ = E(_se/* svkj */);
  switch(_sg/* svko */){
    case  -1:
      var _sh/* svkq */ = E(_sf/* svkk */);
      if(_sh/* svkq */==( -2147483648)){
        return E(_rA/* GHC.Real.overflowError */);
      }else{
        return new F(function(){return quot/* EXTERNAL */(_sh/* svkq */,  -1);});
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return quot/* EXTERNAL */(_sf/* svkk */, _sg/* svko */);});
  }
},
_si/* $fIntegralInt_$cquotRem */ = function(_sj/* svjv */, _sk/* svjw */){
  var _sl/* svjx */ = E(_sj/* svjv */),
  _sm/* svjB */ = E(_sk/* svjw */);
  switch(_sm/* svjB */){
    case  -1:
      var _sn/* svjH */ = E(_sl/* svjx */);
      if(_sn/* svjH */==( -2147483648)){
        return E(_rK/* GHC.Real.lvl2 */);
      }else{
        var _so/* svjI */ = quotRemI/* EXTERNAL */(_sn/* svjH */,  -1);
        return new T2(0,_so/* svjI */.a,_so/* svjI */.b);
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      var _sp/* svjC */ = quotRemI/* EXTERNAL */(_sl/* svjx */, _sm/* svjB */);
      return new T2(0,_sp/* svjC */.a,_sp/* svjC */.b);
  }
},
_sq/* $fIntegralInt_$crem */ = function(_sr/* svka */, _ss/* svkb */){
  var _st/* svke */ = E(_ss/* svkb */);
  switch(_st/* svke */){
    case  -1:
      return E(_rJ/* GHC.Real.$fIntegralInt1 */);
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return E(_sr/* svka */)%_st/* svke */;
  }
},
_su/* $fIntegralInt_$ctoInteger */ = function(_sv/* svhV */){
  return new F(function(){return _pz/* GHC.Integer.Type.smallInteger */(E(_sv/* svhV */));});
},
_sw/* $fEnumRatio_$ctoRational */ = function(_sx/* svhY */){
  return new T2(0,E(B(_pz/* GHC.Integer.Type.smallInteger */(E(_sx/* svhY */)))),E(_lP/* GHC.Real.$fEnumRatio1 */));
},
_sy/* $fNumInt_$c* */ = function(_sz/* s6GN */, _sA/* s6GO */){
  return imul/* EXTERNAL */(E(_sz/* s6GN */), E(_sA/* s6GO */))|0;
},
_sB/* $fNumInt_$c+ */ = function(_sC/* s6H1 */, _sD/* s6H2 */){
  return E(_sC/* s6H1 */)+E(_sD/* s6H2 */)|0;
},
_sE/* $fNumInt_$c- */ = function(_sF/* s6GU */, _sG/* s6GV */){
  return E(_sF/* s6GU */)-E(_sG/* s6GV */)|0;
},
_sH/* $fNumInt_$cabs */ = function(_sI/* s6He */){
  var _sJ/* s6Hf */ = E(_sI/* s6He */);
  return (_sJ/* s6Hf */<0) ?  -_sJ/* s6Hf */ : E(_sJ/* s6Hf */);
},
_sK/* $fNumInt_$cfromInteger */ = function(_sL/* s6GH */){
  return new F(function(){return _38/* GHC.Integer.Type.integerToInt */(_sL/* s6GH */);});
},
_sM/* $fNumInt_$cnegate */ = function(_sN/* s6GJ */){
  return  -E(_sN/* s6GJ */);
},
_sO/* $fNumInt1 */ =  -1,
_sP/* $fNumInt2 */ = 0,
_sQ/* $fNumInt3 */ = 1,
_sR/* $fNumInt_$csignum */ = function(_sS/* s6H8 */){
  var _sT/* s6H9 */ = E(_sS/* s6H8 */);
  return (_sT/* s6H9 */>=0) ? (E(_sT/* s6H9 */)==0) ? E(_sP/* GHC.Num.$fNumInt2 */) : E(_sQ/* GHC.Num.$fNumInt3 */) : E(_sO/* GHC.Num.$fNumInt1 */);
},
_sU/* $fNumInt */ = {_:0,a:_sB/* GHC.Num.$fNumInt_$c+ */,b:_sE/* GHC.Num.$fNumInt_$c- */,c:_sy/* GHC.Num.$fNumInt_$c* */,d:_sM/* GHC.Num.$fNumInt_$cnegate */,e:_sH/* GHC.Num.$fNumInt_$cabs */,f:_sR/* GHC.Num.$fNumInt_$csignum */,g:_sK/* GHC.Num.$fNumInt_$cfromInteger */},
_sV/* eqInt */ = function(_sW/* scEd */, _sX/* scEe */){
  return E(_sW/* scEd */)==E(_sX/* scEe */);
},
_sY/* neInt */ = function(_sZ/* scEM */, _t0/* scEN */){
  return E(_sZ/* scEM */)!=E(_t0/* scEN */);
},
_t1/* $fEqInt */ = new T2(0,_sV/* GHC.Classes.eqInt */,_sY/* GHC.Classes.neInt */),
_t2/* $fOrdInt_$cmax */ = function(_t3/* scK3 */, _t4/* scK4 */){
  var _t5/* scK5 */ = E(_t3/* scK3 */),
  _t6/* scK7 */ = E(_t4/* scK4 */);
  return (_t5/* scK5 */>_t6/* scK7 */) ? E(_t5/* scK5 */) : E(_t6/* scK7 */);
},
_t7/* $fOrdInt_$cmin */ = function(_t8/* scJV */, _t9/* scJW */){
  var _ta/* scJX */ = E(_t8/* scJV */),
  _tb/* scJZ */ = E(_t9/* scJW */);
  return (_ta/* scJX */>_tb/* scJZ */) ? E(_tb/* scJZ */) : E(_ta/* scJX */);
},
_tc/* compareInt# */ = function(_td/* scDH */, _te/* scDI */){
  return (_td/* scDH */>=_te/* scDI */) ? (_td/* scDH */!=_te/* scDI */) ? 2 : 1 : 0;
},
_tf/* compareInt */ = function(_tg/* scDN */, _th/* scDO */){
  return new F(function(){return _tc/* GHC.Classes.compareInt# */(E(_tg/* scDN */), E(_th/* scDO */));});
},
_ti/* geInt */ = function(_tj/* scEk */, _tk/* scEl */){
  return E(_tj/* scEk */)>=E(_tk/* scEl */);
},
_tl/* gtInt */ = function(_tm/* scEr */, _tn/* scEs */){
  return E(_tm/* scEr */)>E(_tn/* scEs */);
},
_to/* leInt */ = function(_tp/* scEy */, _tq/* scEz */){
  return E(_tp/* scEy */)<=E(_tq/* scEz */);
},
_tr/* ltInt */ = function(_ts/* scEF */, _tt/* scEG */){
  return E(_ts/* scEF */)<E(_tt/* scEG */);
},
_tu/* $fOrdInt */ = {_:0,a:_t1/* GHC.Classes.$fEqInt */,b:_tf/* GHC.Classes.compareInt */,c:_tr/* GHC.Classes.ltInt */,d:_to/* GHC.Classes.leInt */,e:_tl/* GHC.Classes.gtInt */,f:_ti/* GHC.Classes.geInt */,g:_t2/* GHC.Classes.$fOrdInt_$cmax */,h:_t7/* GHC.Classes.$fOrdInt_$cmin */},
_tv/* $fRealInt */ = new T3(0,_sU/* GHC.Num.$fNumInt */,_tu/* GHC.Classes.$fOrdInt */,_sw/* GHC.Real.$fEnumRatio_$ctoRational */),
_tw/* $fIntegralInt */ = {_:0,a:_tv/* GHC.Real.$fRealInt */,b:_ru/* GHC.Enum.$fEnumInt */,c:_sc/* GHC.Real.$fIntegralInt_$cquot */,d:_sq/* GHC.Real.$fIntegralInt_$crem */,e:_rG/* GHC.Real.$fIntegralInt_$cdiv */,f:_s8/* GHC.Real.$fIntegralInt_$cmod */,g:_si/* GHC.Real.$fIntegralInt_$cquotRem */,h:_rL/* GHC.Real.$fIntegralInt_$cdivMod */,i:_su/* GHC.Real.$fIntegralInt_$ctoInteger */},
_tx/* $fRealFloatDouble5 */ = new T1(0,2),
_ty/* timesInteger */ = function(_tz/* s1PN */, _tA/* s1PO */){
  while(1){
    var _tB/* s1PP */ = E(_tz/* s1PN */);
    if(!_tB/* s1PP */._){
      var _tC/* s1PQ */ = _tB/* s1PP */.a,
      _tD/* s1PR */ = E(_tA/* s1PO */);
      if(!_tD/* s1PR */._){
        var _tE/* s1PS */ = _tD/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_tC/* s1PQ */, _tE/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_tC/* s1PQ */, _tE/* s1PS */)|0);
        }else{
          _tz/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_tC/* s1PQ */));
          _tA/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_tE/* s1PS */));
          continue;
        }
      }else{
        _tz/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_tC/* s1PQ */));
        _tA/* s1PO */ = _tD/* s1PR */;
        continue;
      }
    }else{
      var _tF/* s1Q6 */ = E(_tA/* s1PO */);
      if(!_tF/* s1Q6 */._){
        _tz/* s1PN */ = _tB/* s1PP */;
        _tA/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_tF/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_tB/* s1PP */.a, _tF/* s1Q6 */.a));
      }
    }
  }
},
_tG/* $wg1 */ = function(_tH/* svGB */, _tI/* svGC */, _tJ/* svGD */){
  while(1){
    if(!(_tI/* svGC */%2)){
      var _tK/*  svGB */ = B(_ty/* GHC.Integer.Type.timesInteger */(_tH/* svGB */, _tH/* svGB */)),
      _tL/*  svGC */ = quot/* EXTERNAL */(_tI/* svGC */, 2);
      _tH/* svGB */ = _tK/*  svGB */;
      _tI/* svGC */ = _tL/*  svGC */;
      continue;
    }else{
      var _tM/* svGF */ = E(_tI/* svGC */);
      if(_tM/* svGF */==1){
        return new F(function(){return _ty/* GHC.Integer.Type.timesInteger */(_tH/* svGB */, _tJ/* svGD */);});
      }else{
        var _tK/*  svGB */ = B(_ty/* GHC.Integer.Type.timesInteger */(_tH/* svGB */, _tH/* svGB */)),
        _tN/*  svGD */ = B(_ty/* GHC.Integer.Type.timesInteger */(_tH/* svGB */, _tJ/* svGD */));
        _tH/* svGB */ = _tK/*  svGB */;
        _tI/* svGC */ = quot/* EXTERNAL */(_tM/* svGF */-1|0, 2);
        _tJ/* svGD */ = _tN/*  svGD */;
        continue;
      }
    }
  }
},
_tO/* $wf */ = function(_tP/* svGM */, _tQ/* svGN */){
  while(1){
    if(!(_tQ/* svGN */%2)){
      var _tR/*  svGM */ = B(_ty/* GHC.Integer.Type.timesInteger */(_tP/* svGM */, _tP/* svGM */)),
      _tS/*  svGN */ = quot/* EXTERNAL */(_tQ/* svGN */, 2);
      _tP/* svGM */ = _tR/*  svGM */;
      _tQ/* svGN */ = _tS/*  svGN */;
      continue;
    }else{
      var _tT/* svGP */ = E(_tQ/* svGN */);
      if(_tT/* svGP */==1){
        return E(_tP/* svGM */);
      }else{
        return new F(function(){return _tG/* GHC.Real.$wg1 */(B(_ty/* GHC.Integer.Type.timesInteger */(_tP/* svGM */, _tP/* svGM */)), quot/* EXTERNAL */(_tT/* svGP */-1|0, 2), _tP/* svGM */);});
      }
    }
  }
},
_tU/* $p2Real */ = function(_tV/* svbz */){
  return E(E(_tV/* svbz */).b);
},
_tW/* < */ = function(_tX/* scCc */){
  return E(E(_tX/* scCc */).c);
},
_tY/* even1 */ = new T1(0,0),
_tZ/* rem */ = function(_u0/* svaq */){
  return E(E(_u0/* svaq */).d);
},
_u1/* even */ = function(_u2/* svAV */, _u3/* svAW */){
  var _u4/* svAX */ = B(_qA/* GHC.Real.$p1Integral */(_u2/* svAV */)),
  _u5/* svAY */ = new T(function(){
    return B(_qC/* GHC.Real.$p1Real */(_u4/* svAX */));
  }),
  _u6/* svB2 */ = new T(function(){
    return B(A3(_tZ/* GHC.Real.rem */,_u2/* svAV */, _u3/* svAW */, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_u5/* svAY */, _lZ/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_kJ/* GHC.Classes.== */,B(_kH/* GHC.Classes.$p1Ord */(B(_tU/* GHC.Real.$p2Real */(_u4/* svAX */)))), _u6/* svB2 */, new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_u5/* svAY */, _tY/* GHC.Real.even1 */));
  }));});
},
_u7/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_u8/* lvl11 */ = new T(function(){
  return B(err/* EXTERNAL */(_u7/* GHC.Real.lvl5 */));
}),
_u9/* quot */ = function(_ua/* svaf */){
  return E(E(_ua/* svaf */).c);
},
_ub/* ^ */ = function(_uc/* svH6 */, _ud/* svH7 */, _ue/* svH8 */, _uf/* svH9 */){
  var _ug/* svHa */ = B(_qA/* GHC.Real.$p1Integral */(_ud/* svH7 */)),
  _uh/* svHb */ = new T(function(){
    return B(_qC/* GHC.Real.$p1Real */(_ug/* svHa */));
  }),
  _ui/* svHc */ = B(_tU/* GHC.Real.$p2Real */(_ug/* svHa */));
  if(!B(A3(_tW/* GHC.Classes.< */,_ui/* svHc */, _uf/* svH9 */, new T(function(){
    return B(A2(_8X/* GHC.Num.fromInteger */,_uh/* svHb */, _tY/* GHC.Real.even1 */));
  })))){
    if(!B(A3(_kJ/* GHC.Classes.== */,B(_kH/* GHC.Classes.$p1Ord */(_ui/* svHc */)), _uf/* svH9 */, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_uh/* svHb */, _tY/* GHC.Real.even1 */));
    })))){
      var _uj/* svHi */ = new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_uh/* svHb */, _lZ/* GHC.Real.even2 */));
      }),
      _uk/* svHj */ = new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_uh/* svHb */, _lP/* GHC.Real.$fEnumRatio1 */));
      }),
      _ul/* svHk */ = B(_kH/* GHC.Classes.$p1Ord */(_ui/* svHc */)),
      _um/* svHl */ = function(_un/*  svHm */, _uo/*  svHn */, _up/*  svHo */){
        while(1){
          var _uq/*  svHl */ = B((function(_ur/* svHm */, _us/* svHn */, _ut/* svHo */){
            if(!B(_u1/* GHC.Real.even */(_ud/* svH7 */, _us/* svHn */))){
              if(!B(A3(_kJ/* GHC.Classes.== */,_ul/* svHk */, _us/* svHn */, _uk/* svHj */))){
                var _uu/* svHt */ = new T(function(){
                  return B(A3(_u9/* GHC.Real.quot */,_ud/* svH7 */, new T(function(){
                    return B(A3(_7m/* GHC.Num.- */,_uh/* svHb */, _us/* svHn */, _uk/* svHj */));
                  }), _uj/* svHi */));
                });
                _un/*  svHm */ = new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_uc/* svH6 */, _ur/* svHm */, _ur/* svHm */));
                });
                _uo/*  svHn */ = _uu/* svHt */;
                _up/*  svHo */ = new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_uc/* svH6 */, _ur/* svHm */, _ut/* svHo */));
                });
                return __continue/* EXTERNAL */;
              }else{
                return new F(function(){return A3(_7k/* GHC.Num.* */,_uc/* svH6 */, _ur/* svHm */, _ut/* svHo */);});
              }
            }else{
              var _uv/*   svHo */ = _ut/* svHo */;
              _un/*  svHm */ = new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_uc/* svH6 */, _ur/* svHm */, _ur/* svHm */));
              });
              _uo/*  svHn */ = new T(function(){
                return B(A3(_u9/* GHC.Real.quot */,_ud/* svH7 */, _us/* svHn */, _uj/* svHi */));
              });
              _up/*  svHo */ = _uv/*   svHo */;
              return __continue/* EXTERNAL */;
            }
          })(_un/*  svHm */, _uo/*  svHn */, _up/*  svHo */));
          if(_uq/*  svHl */!=__continue/* EXTERNAL */){
            return _uq/*  svHl */;
          }
        }
      },
      _uw/* svHx */ = function(_ux/*  svHy */, _uy/*  svHz */){
        while(1){
          var _uz/*  svHx */ = B((function(_uA/* svHy */, _uB/* svHz */){
            if(!B(_u1/* GHC.Real.even */(_ud/* svH7 */, _uB/* svHz */))){
              if(!B(A3(_kJ/* GHC.Classes.== */,_ul/* svHk */, _uB/* svHz */, _uk/* svHj */))){
                var _uC/* svHE */ = new T(function(){
                  return B(A3(_u9/* GHC.Real.quot */,_ud/* svH7 */, new T(function(){
                    return B(A3(_7m/* GHC.Num.- */,_uh/* svHb */, _uB/* svHz */, _uk/* svHj */));
                  }), _uj/* svHi */));
                });
                return new F(function(){return _um/* svHl */(new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_uc/* svH6 */, _uA/* svHy */, _uA/* svHy */));
                }), _uC/* svHE */, _uA/* svHy */);});
              }else{
                return E(_uA/* svHy */);
              }
            }else{
              _ux/*  svHy */ = new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_uc/* svH6 */, _uA/* svHy */, _uA/* svHy */));
              });
              _uy/*  svHz */ = new T(function(){
                return B(A3(_u9/* GHC.Real.quot */,_ud/* svH7 */, _uB/* svHz */, _uj/* svHi */));
              });
              return __continue/* EXTERNAL */;
            }
          })(_ux/*  svHy */, _uy/*  svHz */));
          if(_uz/*  svHx */!=__continue/* EXTERNAL */){
            return _uz/*  svHx */;
          }
        }
      };
      return new F(function(){return _uw/* svHx */(_ue/* svH8 */, _uf/* svH9 */);});
    }else{
      return new F(function(){return A2(_8X/* GHC.Num.fromInteger */,_uc/* svH6 */, _lP/* GHC.Real.$fEnumRatio1 */);});
    }
  }else{
    return E(_u8/* GHC.Real.lvl11 */);
  }
},
_uD/* ^1 */ = new T(function(){
  return B(err/* EXTERNAL */(_u7/* GHC.Real.lvl5 */));
}),
_uE/* $w$cproperFraction */ = function(_uF/* s1l7J */, _uG/* s1l7K */){
  var _uH/* s1l7L */ = B(_pw/* GHC.Integer.Type.decodeDoubleInteger */(_uG/* s1l7K */)),
  _uI/* s1l7M */ = _uH/* s1l7L */.a,
  _uJ/* s1l7N */ = _uH/* s1l7L */.b,
  _uK/* s1l7P */ = new T(function(){
    return B(_qC/* GHC.Real.$p1Real */(new T(function(){
      return B(_qA/* GHC.Real.$p1Integral */(_uF/* s1l7J */));
    })));
  });
  if(_uJ/* s1l7N */<0){
    var _uL/* s1l7S */ =  -_uJ/* s1l7N */;
    if(_uL/* s1l7S */>=0){
      var _uM/* s1l7W */ = E(_uL/* s1l7S */);
      if(!_uM/* s1l7W */){
        var _uN/* s1l7W#result */ = E(_lP/* GHC.Real.$fEnumRatio1 */);
      }else{
        var _uN/* s1l7W#result */ = B(_tO/* GHC.Real.$wf */(_tx/* GHC.Float.$fRealFloatDouble5 */, _uM/* s1l7W */));
      }
      if(!B(_30/* GHC.Integer.Type.eqInteger */(_uN/* s1l7W#result */, _3t/* GHC.Float.rationalToDouble5 */))){
        var _uO/* s1l7Y */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_uI/* s1l7M */, _uN/* s1l7W#result */));
        return new T2(0,new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_uK/* s1l7P */, _uO/* s1l7Y */.a));
        }),new T(function(){
          return B(_2W/* GHC.Integer.Type.encodeDoubleInteger */(_uO/* s1l7Y */.b, _uJ/* s1l7N */));
        }));
      }else{
        return E(_2V/* GHC.Real.divZeroError */);
      }
    }else{
      return E(_uD/* GHC.Real.^1 */);
    }
  }else{
    var _uP/* s1l8a */ = new T(function(){
      var _uQ/* s1l89 */ = new T(function(){
        return B(_ub/* GHC.Real.^ */(_uK/* s1l7P */, _tw/* GHC.Real.$fIntegralInt */, new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_uK/* s1l7P */, _tx/* GHC.Float.$fRealFloatDouble5 */));
        }), _uJ/* s1l7N */));
      });
      return B(A3(_7k/* GHC.Num.* */,_uK/* s1l7P */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_uK/* s1l7P */, _uI/* s1l7M */));
      }), _uQ/* s1l89 */));
    });
    return new T2(0,_uP/* s1l8a */,_6i/* GHC.Float.rationalToDouble4 */);
  }
},
_uR/* $fRealFracDouble_$cceiling */ = function(_uS/* s1l8X */, _uT/* s1l8Y */){
  var _uU/* s1l91 */ = B(_uE/* GHC.Float.$w$cproperFraction */(_uS/* s1l8X */, E(_uT/* s1l8Y */))),
  _uV/* s1l92 */ = _uU/* s1l91 */.a;
  if(E(_uU/* s1l91 */.b)<=0){
    return E(_uV/* s1l92 */);
  }else{
    var _uW/* s1l99 */ = B(_qC/* GHC.Real.$p1Real */(B(_qA/* GHC.Real.$p1Integral */(_uS/* s1l8X */))));
    return new F(function(){return A3(_6I/* GHC.Num.+ */,_uW/* s1l99 */, _uV/* s1l92 */, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_uW/* s1l99 */, _1M/* GHC.Float.$fRealDouble1 */));
    }));});
  }
},
_uX/* $fRealFracDouble_$cfloor */ = function(_uY/* s1l9b */, _uZ/* s1l9c */){
  var _v0/* s1l9f */ = B(_uE/* GHC.Float.$w$cproperFraction */(_uY/* s1l9b */, E(_uZ/* s1l9c */))),
  _v1/* s1l9g */ = _v0/* s1l9f */.a;
  if(E(_v0/* s1l9f */.b)>=0){
    return E(_v1/* s1l9g */);
  }else{
    var _v2/* s1l9n */ = B(_qC/* GHC.Real.$p1Real */(B(_qA/* GHC.Real.$p1Integral */(_uY/* s1l9b */))));
    return new F(function(){return A3(_7m/* GHC.Num.- */,_v2/* s1l9n */, _v1/* s1l9g */, new T(function(){
      return B(A2(_8X/* GHC.Num.fromInteger */,_v2/* s1l9n */, _1M/* GHC.Float.$fRealDouble1 */));
    }));});
  }
},
_v3/* $fRealFracDouble_$cproperFraction */ = function(_v4/* s1l8b */, _v5/* s1l8c */){
  var _v6/* s1l8f */ = B(_uE/* GHC.Float.$w$cproperFraction */(_v4/* s1l8b */, E(_v5/* s1l8c */)));
  return new T2(0,_v6/* s1l8f */.a,_v6/* s1l8f */.b);
},
_v7/* $w$cround */ = function(_v8/* s1l8p */, _v9/* s1l8q */){
  var _va/* s1l8r */ = B(_uE/* GHC.Float.$w$cproperFraction */(_v8/* s1l8p */, _v9/* s1l8q */)),
  _vb/* s1l8s */ = _va/* s1l8r */.a,
  _vc/* s1l8u */ = E(_va/* s1l8r */.b),
  _vd/* s1l8w */ = new T(function(){
    var _ve/* s1l8y */ = B(_qC/* GHC.Real.$p1Real */(B(_qA/* GHC.Real.$p1Integral */(_v8/* s1l8p */))));
    if(_vc/* s1l8u */>=0){
      return B(A3(_6I/* GHC.Num.+ */,_ve/* s1l8y */, _vb/* s1l8s */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_ve/* s1l8y */, _1M/* GHC.Float.$fRealDouble1 */));
      })));
    }else{
      return B(A3(_7m/* GHC.Num.- */,_ve/* s1l8y */, _vb/* s1l8s */, new T(function(){
        return B(A2(_8X/* GHC.Num.fromInteger */,_ve/* s1l8y */, _1M/* GHC.Float.$fRealDouble1 */));
      })));
    }
  }),
  _vf/* s1l8D */ = function(_vg/* s1l8E */){
    var _vh/* s1l8F */ = _vg/* s1l8E */-0.5;
    return (_vh/* s1l8F */>=0) ? (E(_vh/* s1l8F */)==0) ? (!B(_u1/* GHC.Real.even */(_v8/* s1l8p */, _vb/* s1l8s */))) ? E(_vd/* s1l8w */) : E(_vb/* s1l8s */) : E(_vd/* s1l8w */) : E(_vb/* s1l8s */);
  },
  _vi/* s1l8K */ = E(_vc/* s1l8u */);
  if(!_vi/* s1l8K */){
    return new F(function(){return _vf/* s1l8D */(0);});
  }else{
    if(_vi/* s1l8K */<=0){
      var _vj/* s1l8N */ =  -_vi/* s1l8K */-0.5;
      return (_vj/* s1l8N */>=0) ? (E(_vj/* s1l8N */)==0) ? (!B(_u1/* GHC.Real.even */(_v8/* s1l8p */, _vb/* s1l8s */))) ? E(_vd/* s1l8w */) : E(_vb/* s1l8s */) : E(_vd/* s1l8w */) : E(_vb/* s1l8s */);
    }else{
      return new F(function(){return _vf/* s1l8D */(_vi/* s1l8K */);});
    }
  }
},
_vk/* $fRealFracDouble_$cround */ = function(_vl/* s1l8T */, _vm/* s1l8U */){
  return new F(function(){return _v7/* GHC.Float.$w$cround */(_vl/* s1l8T */, E(_vm/* s1l8U */));});
},
_vn/* $fRealFracDouble_$ctruncate */ = function(_vo/* s1l8i */, _vp/* s1l8j */){
  return E(B(_uE/* GHC.Float.$w$cproperFraction */(_vo/* s1l8i */, E(_vp/* s1l8j */))).a);
},
_vq/* $fRealFracDouble */ = {_:0,a:_qz/* GHC.Float.$fRealDouble */,b:_ij/* GHC.Float.$fFractionalDouble */,c:_v3/* GHC.Float.$fRealFracDouble_$cproperFraction */,d:_vn/* GHC.Float.$fRealFracDouble_$ctruncate */,e:_vk/* GHC.Float.$fRealFracDouble_$cround */,f:_uR/* GHC.Float.$fRealFracDouble_$cceiling */,g:_uX/* GHC.Float.$fRealFracDouble_$cfloor */},
_vr/* $fEnumInteger2 */ = new T1(0,1),
_vs/* $wenumDeltaInteger */ = function(_vt/* smF4 */, _vu/* smF5 */){
  var _vv/* smF6 */ = E(_vt/* smF4 */);
  return new T2(0,_vv/* smF6 */,new T(function(){
    var _vw/* smF8 */ = B(_vs/* GHC.Enum.$wenumDeltaInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_vv/* smF6 */, _vu/* smF5 */)), _vu/* smF5 */));
    return new T2(1,_vw/* smF8 */.a,_vw/* smF8 */.b);
  }));
},
_vx/* $fEnumInteger_$cenumFrom */ = function(_vy/* smFn */){
  var _vz/* smFo */ = B(_vs/* GHC.Enum.$wenumDeltaInteger */(_vy/* smFn */, _vr/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_vz/* smFo */.a,_vz/* smFo */.b);
},
_vA/* $fEnumInteger_$cenumFromThen */ = function(_vB/* smFr */, _vC/* smFs */){
  var _vD/* smFu */ = B(_vs/* GHC.Enum.$wenumDeltaInteger */(_vB/* smFr */, new T(function(){
    return B(_5w/* GHC.Integer.Type.minusInteger */(_vC/* smFs */, _vB/* smFr */));
  })));
  return new T2(1,_vD/* smFu */.a,_vD/* smFu */.b);
},
_vE/* $fEnumInteger1 */ = new T1(0,0),
_vF/* geInteger */ = function(_vG/* s1FG */, _vH/* s1FH */){
  var _vI/* s1FI */ = E(_vG/* s1FG */);
  if(!_vI/* s1FI */._){
    var _vJ/* s1FJ */ = _vI/* s1FI */.a,
    _vK/* s1FK */ = E(_vH/* s1FH */);
    return (_vK/* s1FK */._==0) ? _vJ/* s1FJ */>=_vK/* s1FK */.a : I_compareInt/* EXTERNAL */(_vK/* s1FK */.a, _vJ/* s1FJ */)<=0;
  }else{
    var _vL/* s1FR */ = _vI/* s1FI */.a,
    _vM/* s1FS */ = E(_vH/* s1FH */);
    return (_vM/* s1FS */._==0) ? I_compareInt/* EXTERNAL */(_vL/* s1FR */, _vM/* s1FS */.a)>=0 : I_compare/* EXTERNAL */(_vL/* s1FR */, _vM/* s1FS */.a)>=0;
  }
},
_vN/* enumDeltaToInteger */ = function(_vO/* smFx */, _vP/* smFy */, _vQ/* smFz */){
  if(!B(_vF/* GHC.Integer.Type.geInteger */(_vP/* smFy */, _vE/* GHC.Enum.$fEnumInteger1 */))){
    var _vR/* smFB */ = function(_vS/* smFC */){
      return (!B(_3N/* GHC.Integer.Type.ltInteger */(_vS/* smFC */, _vQ/* smFz */))) ? new T2(1,_vS/* smFC */,new T(function(){
        return B(_vR/* smFB */(B(_3b/* GHC.Integer.Type.plusInteger */(_vS/* smFC */, _vP/* smFy */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _vR/* smFB */(_vO/* smFx */);});
  }else{
    var _vT/* smFG */ = function(_vU/* smFH */){
      return (!B(_3E/* GHC.Integer.Type.gtInteger */(_vU/* smFH */, _vQ/* smFz */))) ? new T2(1,_vU/* smFH */,new T(function(){
        return B(_vT/* smFG */(B(_3b/* GHC.Integer.Type.plusInteger */(_vU/* smFH */, _vP/* smFy */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _vT/* smFG */(_vO/* smFx */);});
  }
},
_vV/* $fEnumInteger_$cenumFromThenTo */ = function(_vW/* smFY */, _vX/* smFZ */, _vY/* smG0 */){
  return new F(function(){return _vN/* GHC.Enum.enumDeltaToInteger */(_vW/* smFY */, B(_5w/* GHC.Integer.Type.minusInteger */(_vX/* smFZ */, _vW/* smFY */)), _vY/* smG0 */);});
},
_vZ/* $fEnumInteger_$cenumFromTo */ = function(_w0/* smFW */, _w1/* smFX */){
  return new F(function(){return _vN/* GHC.Enum.enumDeltaToInteger */(_w0/* smFW */, _vr/* GHC.Enum.$fEnumInteger2 */, _w1/* smFX */);});
},
_w2/* $fEnumInteger_$cfromEnum */ = function(_w3/* smEX */){
  return new F(function(){return _38/* GHC.Integer.Type.integerToInt */(_w3/* smEX */);});
},
_w4/* $fEnumInteger_$cpred */ = function(_w5/* smF3 */){
  return new F(function(){return _5w/* GHC.Integer.Type.minusInteger */(_w5/* smF3 */, _vr/* GHC.Enum.$fEnumInteger2 */);});
},
_w6/* $fEnumInteger_$csucc */ = function(_w7/* smF2 */){
  return new F(function(){return _3b/* GHC.Integer.Type.plusInteger */(_w7/* smF2 */, _vr/* GHC.Enum.$fEnumInteger2 */);});
},
_w8/* $fEnumInteger_$ctoEnum */ = function(_w9/* smEZ */){
  return new F(function(){return _pz/* GHC.Integer.Type.smallInteger */(E(_w9/* smEZ */));});
},
_wa/* $fEnumInteger */ = {_:0,a:_w6/* GHC.Enum.$fEnumInteger_$csucc */,b:_w4/* GHC.Enum.$fEnumInteger_$cpred */,c:_w8/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_w2/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_vx/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_vA/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_vZ/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_vV/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_wb/* divInteger */ = function(_wc/* s1Nz */, _wd/* s1NA */){
  while(1){
    var _we/* s1NB */ = E(_wc/* s1Nz */);
    if(!_we/* s1NB */._){
      var _wf/* s1ND */ = E(_we/* s1NB */.a);
      if(_wf/* s1ND */==( -2147483648)){
        _wc/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _wg/* s1NE */ = E(_wd/* s1NA */);
        if(!_wg/* s1NE */._){
          return new T1(0,B(_rv/* GHC.Classes.divInt# */(_wf/* s1ND */, _wg/* s1NE */.a)));
        }else{
          _wc/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_wf/* s1ND */));
          _wd/* s1NA */ = _wg/* s1NE */;
          continue;
        }
      }
    }else{
      var _wh/* s1NO */ = _we/* s1NB */.a,
      _wi/* s1NP */ = E(_wd/* s1NA */);
      return (_wi/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_wh/* s1NO */, I_fromInt/* EXTERNAL */(_wi/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_wh/* s1NO */, _wi/* s1NP */.a));
    }
  }
},
_wj/* $fIntegralInteger_$cdiv */ = function(_wk/* svkR */, _wl/* svkS */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wl/* svkS */, _tY/* GHC.Real.even1 */))){
    return new F(function(){return _wb/* GHC.Integer.Type.divInteger */(_wk/* svkR */, _wl/* svkS */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wm/* divModInteger */ = function(_wn/* s1MF */, _wo/* s1MG */){
  while(1){
    var _wp/* s1MH */ = E(_wn/* s1MF */);
    if(!_wp/* s1MH */._){
      var _wq/* s1MJ */ = E(_wp/* s1MH */.a);
      if(_wq/* s1MJ */==( -2147483648)){
        _wn/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _wr/* s1MK */ = E(_wo/* s1MG */);
        if(!_wr/* s1MK */._){
          var _ws/* s1ML */ = _wr/* s1MK */.a;
          return new T2(0,new T1(0,B(_rv/* GHC.Classes.divInt# */(_wq/* s1MJ */, _ws/* s1ML */))),new T1(0,B(_s1/* GHC.Classes.modInt# */(_wq/* s1MJ */, _ws/* s1ML */))));
        }else{
          _wn/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_wq/* s1MJ */));
          _wo/* s1MG */ = _wr/* s1MK */;
          continue;
        }
      }
    }else{
      var _wt/* s1MY */ = E(_wo/* s1MG */);
      if(!_wt/* s1MY */._){
        _wn/* s1MF */ = _wp/* s1MH */;
        _wo/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_wt/* s1MY */.a));
        continue;
      }else{
        var _wu/* s1N5 */ = I_divMod/* EXTERNAL */(_wp/* s1MH */.a, _wt/* s1MY */.a);
        return new T2(0,new T1(1,_wu/* s1N5 */.a),new T1(1,_wu/* s1N5 */.b));
      }
    }
  }
},
_wv/* $fIntegralInteger_$cdivMod */ = function(_ww/* svkC */, _wx/* svkD */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wx/* svkD */, _tY/* GHC.Real.even1 */))){
    var _wy/* svkF */ = B(_wm/* GHC.Integer.Type.divModInteger */(_ww/* svkC */, _wx/* svkD */));
    return new T2(0,_wy/* svkF */.a,_wy/* svkF */.b);
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wz/* modInteger */ = function(_wA/* s1Na */, _wB/* s1Nb */){
  while(1){
    var _wC/* s1Nc */ = E(_wA/* s1Na */);
    if(!_wC/* s1Nc */._){
      var _wD/* s1Ne */ = E(_wC/* s1Nc */.a);
      if(_wD/* s1Ne */==( -2147483648)){
        _wA/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _wE/* s1Nf */ = E(_wB/* s1Nb */);
        if(!_wE/* s1Nf */._){
          return new T1(0,B(_s1/* GHC.Classes.modInt# */(_wD/* s1Ne */, _wE/* s1Nf */.a)));
        }else{
          _wA/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_wD/* s1Ne */));
          _wB/* s1Nb */ = _wE/* s1Nf */;
          continue;
        }
      }
    }else{
      var _wF/* s1Np */ = _wC/* s1Nc */.a,
      _wG/* s1Nq */ = E(_wB/* s1Nb */);
      return (_wG/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_wF/* s1Np */, I_fromInt/* EXTERNAL */(_wG/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_wF/* s1Np */, _wG/* s1Nq */.a));
    }
  }
},
_wH/* $fIntegralInteger_$cmod */ = function(_wI/* svkO */, _wJ/* svkP */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wJ/* svkP */, _tY/* GHC.Real.even1 */))){
    return new F(function(){return _wz/* GHC.Integer.Type.modInteger */(_wI/* svkO */, _wJ/* svkP */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wK/* quotInteger */ = function(_wL/* s1On */, _wM/* s1Oo */){
  while(1){
    var _wN/* s1Op */ = E(_wL/* s1On */);
    if(!_wN/* s1Op */._){
      var _wO/* s1Or */ = E(_wN/* s1Op */.a);
      if(_wO/* s1Or */==( -2147483648)){
        _wL/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _wP/* s1Os */ = E(_wM/* s1Oo */);
        if(!_wP/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_wO/* s1Or */, _wP/* s1Os */.a));
        }else{
          _wL/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_wO/* s1Or */));
          _wM/* s1Oo */ = _wP/* s1Os */;
          continue;
        }
      }
    }else{
      var _wQ/* s1OC */ = _wN/* s1Op */.a,
      _wR/* s1OD */ = E(_wM/* s1Oo */);
      return (_wR/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_wQ/* s1OC */, I_fromInt/* EXTERNAL */(_wR/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_wQ/* s1OC */, _wR/* s1OD */.a));
    }
  }
},
_wS/* $fIntegralInteger_$cquot */ = function(_wT/* svkX */, _wU/* svkY */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wU/* svkY */, _tY/* GHC.Real.even1 */))){
    return new F(function(){return _wK/* GHC.Integer.Type.quotInteger */(_wT/* svkX */, _wU/* svkY */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wV/* $fIntegralInteger_$cquotRem */ = function(_wW/* svkI */, _wX/* svkJ */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_wX/* svkJ */, _tY/* GHC.Real.even1 */))){
    var _wY/* svkL */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_wW/* svkI */, _wX/* svkJ */));
    return new T2(0,_wY/* svkL */.a,_wY/* svkL */.b);
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_wZ/* remInteger */ = function(_x0/* s1NY */, _x1/* s1NZ */){
  while(1){
    var _x2/* s1O0 */ = E(_x0/* s1NY */);
    if(!_x2/* s1O0 */._){
      var _x3/* s1O2 */ = E(_x2/* s1O0 */.a);
      if(_x3/* s1O2 */==( -2147483648)){
        _x0/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _x4/* s1O3 */ = E(_x1/* s1NZ */);
        if(!_x4/* s1O3 */._){
          return new T1(0,_x3/* s1O2 */%_x4/* s1O3 */.a);
        }else{
          _x0/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_x3/* s1O2 */));
          _x1/* s1NZ */ = _x4/* s1O3 */;
          continue;
        }
      }
    }else{
      var _x5/* s1Od */ = _x2/* s1O0 */.a,
      _x6/* s1Oe */ = E(_x1/* s1NZ */);
      return (_x6/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_x5/* s1Od */, I_fromInt/* EXTERNAL */(_x6/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_x5/* s1Od */, _x6/* s1Oe */.a));
    }
  }
},
_x7/* $fIntegralInteger_$crem */ = function(_x8/* svkU */, _x9/* svkV */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_x9/* svkV */, _tY/* GHC.Real.even1 */))){
    return new F(function(){return _wZ/* GHC.Integer.Type.remInteger */(_x8/* svkU */, _x9/* svkV */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xa/* $fIntegralInteger_$ctoInteger */ = function(_xb/* svkB */){
  return E(_xb/* svkB */);
},
_xc/* $fNumInteger_$cfromInteger */ = function(_xd/* s6HS */){
  return E(_xd/* s6HS */);
},
_xe/* absInteger */ = function(_xf/* s1QP */){
  var _xg/* s1QQ */ = E(_xf/* s1QP */);
  if(!_xg/* s1QQ */._){
    var _xh/* s1QS */ = E(_xg/* s1QQ */.a);
    return (_xh/* s1QS */==( -2147483648)) ? E(_6a/* GHC.Integer.Type.lvl3 */) : (_xh/* s1QS */<0) ? new T1(0, -_xh/* s1QS */) : E(_xg/* s1QQ */);
  }else{
    var _xi/* s1QW */ = _xg/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_xi/* s1QW */, 0)>=0) ? E(_xg/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_xi/* s1QW */));
  }
},
_xj/* lvl */ = new T1(0,0),
_xk/* lvl1 */ = new T1(0, -1),
_xl/* signumInteger */ = function(_xm/* s1OO */){
  var _xn/* s1OP */ = E(_xm/* s1OO */);
  if(!_xn/* s1OP */._){
    var _xo/* s1OQ */ = _xn/* s1OP */.a;
    return (_xo/* s1OQ */>=0) ? (E(_xo/* s1OQ */)==0) ? E(_xj/* GHC.Integer.Type.lvl */) : E(_3M/* GHC.Integer.Type.log2I1 */) : E(_xk/* GHC.Integer.Type.lvl1 */);
  }else{
    var _xp/* s1OW */ = I_compareInt/* EXTERNAL */(_xn/* s1OP */.a, 0);
    return (_xp/* s1OW */<=0) ? (E(_xp/* s1OW */)==0) ? E(_xj/* GHC.Integer.Type.lvl */) : E(_xk/* GHC.Integer.Type.lvl1 */) : E(_3M/* GHC.Integer.Type.log2I1 */);
  }
},
_xq/* $fNumInteger */ = {_:0,a:_3b/* GHC.Integer.Type.plusInteger */,b:_5w/* GHC.Integer.Type.minusInteger */,c:_ty/* GHC.Integer.Type.timesInteger */,d:_6b/* GHC.Integer.Type.negateInteger */,e:_xe/* GHC.Integer.Type.absInteger */,f:_xl/* GHC.Integer.Type.signumInteger */,g:_xc/* GHC.Num.$fNumInteger_$cfromInteger */},
_xr/* neqInteger */ = function(_xs/* s1H2 */, _xt/* s1H3 */){
  var _xu/* s1H4 */ = E(_xs/* s1H2 */);
  if(!_xu/* s1H4 */._){
    var _xv/* s1H5 */ = _xu/* s1H4 */.a,
    _xw/* s1H6 */ = E(_xt/* s1H3 */);
    return (_xw/* s1H6 */._==0) ? _xv/* s1H5 */!=_xw/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_xw/* s1H6 */.a, _xv/* s1H5 */)==0) ? false : true;
  }else{
    var _xx/* s1Hc */ = _xu/* s1H4 */.a,
    _xy/* s1Hd */ = E(_xt/* s1H3 */);
    return (_xy/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_xx/* s1Hc */, _xy/* s1Hd */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_xx/* s1Hc */, _xy/* s1Hd */.a)==0) ? false : true;
  }
},
_xz/* $fEqInteger */ = new T2(0,_30/* GHC.Integer.Type.eqInteger */,_xr/* GHC.Integer.Type.neqInteger */),
_xA/* $fOrdInteger_$cmax */ = function(_xB/* s1HU */, _xC/* s1HV */){
  return (!B(_5h/* GHC.Integer.Type.leInteger */(_xB/* s1HU */, _xC/* s1HV */))) ? E(_xB/* s1HU */) : E(_xC/* s1HV */);
},
_xD/* $fOrdInteger_$cmin */ = function(_xE/* s1HR */, _xF/* s1HS */){
  return (!B(_5h/* GHC.Integer.Type.leInteger */(_xE/* s1HR */, _xF/* s1HS */))) ? E(_xF/* s1HS */) : E(_xE/* s1HR */);
},
_xG/* $fOrdInteger */ = {_:0,a:_xz/* GHC.Integer.Type.$fEqInteger */,b:_1N/* GHC.Integer.Type.compareInteger */,c:_3N/* GHC.Integer.Type.ltInteger */,d:_5h/* GHC.Integer.Type.leInteger */,e:_3E/* GHC.Integer.Type.gtInteger */,f:_vF/* GHC.Integer.Type.geInteger */,g:_xA/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_xD/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_xH/* $fRealInteger_$s$cfromInteger */ = function(_xI/* svhv */){
  return new T2(0,E(_xI/* svhv */),E(_lP/* GHC.Real.$fEnumRatio1 */));
},
_xJ/* $fRealInteger */ = new T3(0,_xq/* GHC.Num.$fNumInteger */,_xG/* GHC.Integer.Type.$fOrdInteger */,_xH/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_xK/* $fIntegralInteger */ = {_:0,a:_xJ/* GHC.Real.$fRealInteger */,b:_wa/* GHC.Enum.$fEnumInteger */,c:_wS/* GHC.Real.$fIntegralInteger_$cquot */,d:_x7/* GHC.Real.$fIntegralInteger_$crem */,e:_wj/* GHC.Real.$fIntegralInteger_$cdiv */,f:_wH/* GHC.Real.$fIntegralInteger_$cmod */,g:_wV/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_wv/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_xa/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_xL/* $p2RealFrac */ = function(_xM/* svbS */){
  return E(E(_xM/* svbS */).b);
},
_xN/* floor */ = function(_xO/* svcB */){
  return E(E(_xO/* svcB */).g);
},
_xP/* fmod1 */ = new T1(0,1),
_xQ/* fmod */ = function(_xR/* s6nv */, _xS/* s6nw */, _xT/* s6nx */){
  var _xU/* s6ny */ = B(_xL/* GHC.Real.$p2RealFrac */(_xR/* s6nv */)),
  _xV/* s6nz */ = B(_7i/* GHC.Real.$p1Fractional */(_xU/* s6ny */)),
  _xW/* s6nG */ = new T(function(){
    var _xX/* s6nF */ = new T(function(){
      var _xY/* s6nE */ = new T(function(){
        var _xZ/* s6nD */ = new T(function(){
          return B(A3(_xN/* GHC.Real.floor */,_xR/* s6nv */, _xK/* GHC.Real.$fIntegralInteger */, new T(function(){
            return B(A3(_98/* GHC.Real./ */,_xU/* s6ny */, _xS/* s6nw */, _xT/* s6nx */));
          })));
        });
        return B(A2(_8X/* GHC.Num.fromInteger */,_xV/* s6nz */, _xZ/* s6nD */));
      }),
      _y0/* s6nB */ = new T(function(){
        return B(A2(_6K/* GHC.Num.negate */,_xV/* s6nz */, new T(function(){
          return B(A2(_8X/* GHC.Num.fromInteger */,_xV/* s6nz */, _xP/* Lib.Util.fmod1 */));
        })));
      });
      return B(A3(_7k/* GHC.Num.* */,_xV/* s6nz */, _y0/* s6nB */, _xY/* s6nE */));
    });
    return B(A3(_7k/* GHC.Num.* */,_xV/* s6nz */, _xX/* s6nF */, _xT/* s6nx */));
  });
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_xV/* s6nz */, _xS/* s6nw */, _xW/* s6nG */);});
},
_y1/* square2 */ = 1.5707963267948966,
_y2/* initial18 */ = function(_y3/* s5gV */){
  return 0.2/Math.cos/* EXTERNAL */(B(_xQ/* Lib.Util.fmod */(_vq/* GHC.Float.$fRealFracDouble */, _y3/* s5gV */, _y1/* Lib.Object.square2 */))-0.7853981633974483);
},
_y4/* initial10 */ = 2,
_y5/* initial12 */ = 0.3,
_y6/* initial13 */ =  -0.1,
_y7/* initial11 */ = new T3(0,_pf/* Main.initial8 */,_y6/* Main.initial13 */,_y5/* Main.initial12 */),
_y8/* initial9 */ = new T2(0,_y7/* Main.initial11 */,_y4/* Main.initial10 */),
_y9/* initial6 */ = new T(function(){
  var _ya/* s5h1 */ = B(_o2/* Lib.Object.$wmake */(_y2/* Main.initial18 */, _pc/* Main.initial17 */, _pv/* Main.initial14 */, _y8/* Main.initial9 */, _pp/* Main.initial_ra */));
  return {_:0,a:_ya/* s5h1 */.a,b:_ya/* s5h1 */.b,c:_ya/* s5h1 */.c,d:_ya/* s5h1 */.d,e:_ya/* s5h1 */.e,f:_ya/* s5h1 */.f,g:_ya/* s5h1 */.g,h:_ya/* s5h1 */.h,i:_ya/* s5h1 */.i};
}),
_yb/* initial5 */ = new T2(1,_y9/* Main.initial6 */,_o/* GHC.Types.[] */),
_yc/* initial_ls */ = new T2(1,_pq/* Main.initial19 */,_yb/* Main.initial5 */),
_yd/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative range size"));
}),
_ye/* negRange */ = new T(function(){
  return B(err/* EXTERNAL */(_yd/* GHC.Arr.lvl36 */));
}),
_yf/* initial3 */ = function(_/* EXTERNAL */){
  var _yg/* s5hd */ = B(_hb/* GHC.List.$wlenAcc */(_yc/* Main.initial_ls */, 0))-1|0,
  _yh/* s5he */ = function(_yi/* s5hf */){
    if(_yi/* s5hf */>=0){
      var _yj/* s5hi */ = newArr/* EXTERNAL */(_yi/* s5hf */, _hh/* GHC.Arr.arrEleBottom */),
      _yk/* s5hk */ = _yj/* s5hi */,
      _yl/* s5hl */ = E(_yi/* s5hf */);
      if(!_yl/* s5hl */){
        return new T4(0,E(_ps/* Main.initial4 */),E(_yg/* s5hd */),0,_yk/* s5hk */);
      }else{
        var _ym/* s5hn */ = function(_yn/* s5hx */, _yo/* s5hy */, _/* EXTERNAL */){
          while(1){
            var _yp/* s5hA */ = E(_yn/* s5hx */);
            if(!_yp/* s5hA */._){
              return E(_/* EXTERNAL */);
            }else{
              var _/* EXTERNAL */ = _yk/* s5hk */[_yo/* s5hy */] = _yp/* s5hA */.a;
              if(_yo/* s5hy */!=(_yl/* s5hl */-1|0)){
                var _yq/*  s5hy */ = _yo/* s5hy */+1|0;
                _yn/* s5hx */ = _yp/* s5hA */.b;
                _yo/* s5hy */ = _yq/*  s5hy */;
                continue;
              }else{
                return E(_/* EXTERNAL */);
              }
            }
          }
        },
        _/* EXTERNAL */ = B((function(_yr/* s5ho */, _ys/* s5hp */, _yt/* s5hq */, _/* EXTERNAL */){
          var _/* EXTERNAL */ = _yk/* s5hk */[_yt/* s5hq */] = _yr/* s5ho */;
          if(_yt/* s5hq */!=(_yl/* s5hl */-1|0)){
            return new F(function(){return _ym/* s5hn */(_ys/* s5hp */, _yt/* s5hq */+1|0, _/* EXTERNAL */);});
          }else{
            return E(_/* EXTERNAL */);
          }
        })(_pq/* Main.initial19 */, _yb/* Main.initial5 */, 0, _/* EXTERNAL */));
        return new T4(0,E(_ps/* Main.initial4 */),E(_yg/* s5hd */),_yl/* s5hl */,_yk/* s5hk */);
      }
    }else{
      return E(_ye/* GHC.Arr.negRange */);
    }
  };
  if(0>_yg/* s5hd */){
    return new F(function(){return _yh/* s5he */(0);});
  }else{
    return new F(function(){return _yh/* s5he */(_yg/* s5hd */+1|0);});
  }
},
_yu/* runSTRep */ = function(_yv/* sjpo */){
  var _yw/* sjpp */ = B(A1(_yv/* sjpo */,_/* EXTERNAL */));
  return E(_yw/* sjpp */);
},
_yx/* initial2 */ = new T(function(){
  return B(_yu/* GHC.ST.runSTRep */(_yf/* Main.initial3 */));
}),
_yy/* $fApplicativeIO1 */ = function(_yz/* s3he */, _yA/* s3hf */, _/* EXTERNAL */){
  var _yB/* s3hh */ = B(A1(_yz/* s3he */,_/* EXTERNAL */)),
  _yC/* s3hk */ = B(A1(_yA/* s3hf */,_/* EXTERNAL */));
  return _yB/* s3hh */;
},
_yD/* $fApplicativeIO2 */ = function(_yE/* s3gs */, _yF/* s3gt */, _/* EXTERNAL */){
  var _yG/* s3gv */ = B(A1(_yE/* s3gs */,_/* EXTERNAL */)),
  _yH/* s3gy */ = B(A1(_yF/* s3gt */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_yG/* s3gv */,_yH/* s3gy */));
  });
},
_yI/* $fFunctorIO1 */ = function(_yJ/* s3gX */, _yK/* s3gY */, _/* EXTERNAL */){
  var _yL/* s3h0 */ = B(A1(_yK/* s3gY */,_/* EXTERNAL */));
  return _yJ/* s3gX */;
},
_yM/* $fFunctorIO2 */ = function(_yN/* s3gQ */, _yO/* s3gR */, _/* EXTERNAL */){
  var _yP/* s3gT */ = B(A1(_yO/* s3gR */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_yN/* s3gQ */,_yP/* s3gT */));
  });
},
_yQ/* $fFunctorIO */ = new T2(0,_yM/* GHC.Base.$fFunctorIO2 */,_yI/* GHC.Base.$fFunctorIO1 */),
_yR/* returnIO1 */ = function(_yS/* s3g5 */, _/* EXTERNAL */){
  return _yS/* s3g5 */;
},
_yT/* thenIO1 */ = function(_yU/* s3fZ */, _yV/* s3g0 */, _/* EXTERNAL */){
  var _yW/* s3g2 */ = B(A1(_yU/* s3fZ */,_/* EXTERNAL */));
  return new F(function(){return A1(_yV/* s3g0 */,_/* EXTERNAL */);});
},
_yX/* $fApplicativeIO */ = new T5(0,_yQ/* GHC.Base.$fFunctorIO */,_yR/* GHC.Base.returnIO1 */,_yD/* GHC.Base.$fApplicativeIO2 */,_yT/* GHC.Base.thenIO1 */,_yy/* GHC.Base.$fApplicativeIO1 */),
_yY/* $fIx(,)_$cunsafeRangeSize */ = function(_yZ/* sLFI */){
  var _z0/* sLFJ */ = E(_yZ/* sLFI */);
  return (E(_z0/* sLFJ */.b)-E(_z0/* sLFJ */.a)|0)+1|0;
},
_z1/* $fIxInt_$cinRange */ = function(_z2/* sLHc */, _z3/* sLHd */){
  var _z4/* sLHe */ = E(_z2/* sLHc */),
  _z5/* sLHl */ = E(_z3/* sLHd */);
  return (E(_z4/* sLHe */.a)>_z5/* sLHl */) ? false : _z5/* sLHl */<=E(_z4/* sLHe */.b);
},
_z6/* itos */ = function(_z7/* sf6u */, _z8/* sf6v */){
  var _z9/* sf6x */ = jsShowI/* EXTERNAL */(_z7/* sf6u */);
  return new F(function(){return _f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_z9/* sf6x */), _z8/* sf6v */);});
},
_za/* $wshowSignedInt */ = function(_zb/* sf6C */, _zc/* sf6D */, _zd/* sf6E */){
  if(_zc/* sf6D */>=0){
    return new F(function(){return _z6/* GHC.Show.itos */(_zc/* sf6D */, _zd/* sf6E */);});
  }else{
    if(_zb/* sf6C */<=6){
      return new F(function(){return _z6/* GHC.Show.itos */(_zc/* sf6D */, _zd/* sf6E */);});
    }else{
      return new T2(1,_71/* GHC.Show.shows8 */,new T(function(){
        var _ze/* sf6K */ = jsShowI/* EXTERNAL */(_zc/* sf6D */);
        return B(_f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_ze/* sf6K */), new T2(1,_70/* GHC.Show.shows7 */,_zd/* sf6E */)));
      }));
    }
  }
},
_zf/* $fShowInt_$cshow */ = function(_zg/* sfaP */){
  return new F(function(){return _za/* GHC.Show.$wshowSignedInt */(0, E(_zg/* sfaP */), _o/* GHC.Types.[] */);});
},
_zh/* showSignedInt */ = function(_zi/* sf6R */, _zj/* sf6S */, _zk/* sf6T */){
  return new F(function(){return _za/* GHC.Show.$wshowSignedInt */(E(_zi/* sf6R */), E(_zj/* sf6S */), _zk/* sf6T */);});
},
_zl/* shows6 */ = function(_zm/* sf9f */, _zn/* sf9g */){
  return new F(function(){return _za/* GHC.Show.$wshowSignedInt */(0, E(_zm/* sf9f */), _zn/* sf9g */);});
},
_zo/* shows_$cshowList1 */ = function(_zp/* sfaI */, _zq/* sfaJ */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_zl/* GHC.Show.shows6 */, _zp/* sfaI */, _zq/* sfaJ */);});
},
_zr/* $fShowInt */ = new T3(0,_zh/* GHC.Show.showSignedInt */,_zf/* GHC.Show.$fShowInt_$cshow */,_zo/* GHC.Show.shows_$cshowList1 */),
_zs/* $fIxChar1 */ = 0,
_zt/* $fShow(,)1 */ = function(_zu/* sfbb */, _zv/* sfbc */, _zw/* sfbd */){
  return new F(function(){return A1(_zu/* sfbb */,new T2(1,_2y/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_zv/* sfbc */,_zw/* sfbd */));
  })));});
},
_zx/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_zy/* lvl8 */ = new T(function(){
  return B(_lf/* GHC.List.errorEmptyList */(_zx/* GHC.List.lvl7 */));
}),
_zz/* foldr1 */ = function(_zA/* sbKQ */, _zB/* sbKR */){
  var _zC/* sbKS */ = E(_zB/* sbKR */);
  if(!_zC/* sbKS */._){
    return E(_zy/* GHC.List.lvl8 */);
  }else{
    var _zD/* sbKT */ = _zC/* sbKS */.a,
    _zE/* sbKV */ = E(_zC/* sbKS */.b);
    if(!_zE/* sbKV */._){
      return E(_zD/* sbKT */);
    }else{
      return new F(function(){return A2(_zA/* sbKQ */,_zD/* sbKT */, new T(function(){
        return B(_zz/* GHC.List.foldr1 */(_zA/* sbKQ */, _zE/* sbKV */));
      }));});
    }
  }
},
_zF/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" out of range "));
}),
_zG/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}.index: Index "));
}),
_zH/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ix{"));
}),
_zI/* lvl16 */ = new T2(1,_70/* GHC.Show.shows7 */,_o/* GHC.Types.[] */),
_zJ/* lvl17 */ = new T2(1,_70/* GHC.Show.shows7 */,_zI/* GHC.Arr.lvl16 */),
_zK/* shows14 */ = 0,
_zL/* showsPrec */ = function(_zM/* sf65 */){
  return E(E(_zM/* sf65 */).a);
},
_zN/* lvl18 */ = function(_zO/* sL5Y */, _zP/* sL5Z */, _zQ/* sL60 */, _zR/* sL61 */, _zS/* sL62 */){
  var _zT/* sL6f */ = new T(function(){
    var _zU/* sL6e */ = new T(function(){
      var _zV/* sL6c */ = new T(function(){
        var _zW/* sL6a */ = new T(function(){
          var _zX/* sL67 */ = new T(function(){
            return B(A3(_zz/* GHC.List.foldr1 */,_zt/* GHC.Show.$fShow(,)1 */, new T2(1,new T(function(){
              return B(A3(_zL/* GHC.Show.showsPrec */,_zQ/* sL60 */, _zK/* GHC.Show.shows14 */, _zR/* sL61 */));
            }),new T2(1,new T(function(){
              return B(A3(_zL/* GHC.Show.showsPrec */,_zQ/* sL60 */, _zK/* GHC.Show.shows14 */, _zS/* sL62 */));
            }),_o/* GHC.Types.[] */)), _zJ/* GHC.Arr.lvl17 */));
          });
          return B(_f/* GHC.Base.++ */(_zF/* GHC.Arr.lvl13 */, new T2(1,_71/* GHC.Show.shows8 */,new T2(1,_71/* GHC.Show.shows8 */,_zX/* sL67 */))));
        });
        return B(A(_zL/* GHC.Show.showsPrec */,[_zQ/* sL60 */, _zs/* GHC.Arr.$fIxChar1 */, _zP/* sL5Z */, new T2(1,_70/* GHC.Show.shows7 */,_zW/* sL6a */)]));
      });
      return B(_f/* GHC.Base.++ */(_zG/* GHC.Arr.lvl14 */, new T2(1,_71/* GHC.Show.shows8 */,_zV/* sL6c */)));
    },1);
    return B(_f/* GHC.Base.++ */(_zO/* sL5Y */, _zU/* sL6e */));
  },1);
  return new F(function(){return err/* EXTERNAL */(B(_f/* GHC.Base.++ */(_zH/* GHC.Arr.lvl15 */, _zT/* sL6f */)));});
},
_zY/* $wlvl4 */ = function(_zZ/* sL6h */, _A0/* sL6i */, _A1/* sL6j */, _A2/* sL6k */, _A3/* sL6l */){
  return new F(function(){return _zN/* GHC.Arr.lvl18 */(_zZ/* sL6h */, _A0/* sL6i */, _A3/* sL6l */, _A1/* sL6j */, _A2/* sL6k */);});
},
_A4/* lvl19 */ = function(_A5/* sL6m */, _A6/* sL6n */, _A7/* sL6o */, _A8/* sL6p */){
  var _A9/* sL6q */ = E(_A7/* sL6o */);
  return new F(function(){return _zY/* GHC.Arr.$wlvl4 */(_A5/* sL6m */, _A6/* sL6n */, _A9/* sL6q */.a, _A9/* sL6q */.b, _A8/* sL6p */);});
},
_Aa/* indexError */ = function(_Ab/* sLxR */, _Ac/* sLxS */, _Ad/* sLxT */, _Ae/* sLxU */){
  return new F(function(){return _A4/* GHC.Arr.lvl19 */(_Ae/* sLxU */, _Ad/* sLxT */, _Ac/* sLxS */, _Ab/* sLxR */);});
},
_Af/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int"));
}),
_Ag/* lvl40 */ = function(_Ah/* sLHv */, _Ai/* sLHw */){
  return new F(function(){return _Aa/* GHC.Arr.indexError */(_zr/* GHC.Show.$fShowInt */, _Ah/* sLHv */, _Ai/* sLHw */, _Af/* GHC.Arr.lvl20 */);});
},
_Aj/* $fIxInt_$cindex */ = function(_Ak/* sLHx */, _Al/* sLHy */){
  var _Am/* sLHz */ = E(_Ak/* sLHx */),
  _An/* sLHC */ = E(_Am/* sLHz */.a),
  _Ao/* sLHG */ = E(_Al/* sLHy */);
  if(_An/* sLHC */>_Ao/* sLHG */){
    return new F(function(){return _Ag/* GHC.Arr.lvl40 */(_Am/* sLHz */, _Ao/* sLHG */);});
  }else{
    if(_Ao/* sLHG */>E(_Am/* sLHz */.b)){
      return new F(function(){return _Ag/* GHC.Arr.lvl40 */(_Am/* sLHz */, _Ao/* sLHG */);});
    }else{
      return _Ao/* sLHG */-_An/* sLHC */|0;
    }
  }
},
_Ap/* $fIxInt_$crange */ = function(_Aq/* sLHN */){
  var _Ar/* sLHO */ = E(_Aq/* sLHN */);
  return new F(function(){return _rf/* GHC.Enum.$fEnumInt_$cenumFromTo */(_Ar/* sLHO */.a, _Ar/* sLHO */.b);});
},
_As/* $fIxInt_$crangeSize */ = function(_At/* sLH0 */){
  var _Au/* sLH1 */ = E(_At/* sLH0 */),
  _Av/* sLH4 */ = E(_Au/* sLH1 */.a),
  _Aw/* sLH6 */ = E(_Au/* sLH1 */.b);
  return (_Av/* sLH4 */>_Aw/* sLH6 */) ? E(_zs/* GHC.Arr.$fIxChar1 */) : (_Aw/* sLH6 */-_Av/* sLH4 */|0)+1|0;
},
_Ax/* $fIxInt_$cunsafeIndex */ = function(_Ay/* sLHq */, _Az/* sLHr */){
  return new F(function(){return _sE/* GHC.Num.$fNumInt_$c- */(_Az/* sLHr */, E(_Ay/* sLHq */).a);});
},
_AA/* $fIxInt */ = {_:0,a:_tu/* GHC.Classes.$fOrdInt */,b:_Ap/* GHC.Arr.$fIxInt_$crange */,c:_Aj/* GHC.Arr.$fIxInt_$cindex */,d:_Ax/* GHC.Arr.$fIxInt_$cunsafeIndex */,e:_z1/* GHC.Arr.$fIxInt_$cinRange */,f:_As/* GHC.Arr.$fIxInt_$crangeSize */,g:_yY/* GHC.Arr.$fIx(,)_$cunsafeRangeSize */},
_AB/* : */ = function(_AC/* B2 */, _AD/* B1 */){
  return new T2(1,_AC/* B2 */,_AD/* B1 */);
},
_AE/* bounds */ = function(_AF/* sLl6 */, _AG/* sLl7 */){
  var _AH/* sLl8 */ = E(_AG/* sLl7 */);
  return new T2(0,_AH/* sLl8 */.a,_AH/* sLl8 */.b);
},
_AI/* rangeSize */ = function(_AJ/* sL3K */){
  return E(E(_AJ/* sL3K */).f);
},
_AK/* listArray */ = function(_AL/* sLrT */, _AM/* sLrU */, _AN/* sLrV */){
  var _AO/* sLrW */ = E(_AM/* sLrU */),
  _AP/* sLrX */ = _AO/* sLrW */.a,
  _AQ/* sLrY */ = _AO/* sLrW */.b,
  _AR/* sLsy */ = function(_/* EXTERNAL */){
    var _AS/* sLs0 */ = B(A2(_AI/* GHC.Arr.rangeSize */,_AL/* sLrT */, _AO/* sLrW */));
    if(_AS/* sLs0 */>=0){
      var _AT/* sLs4 */ = newArr/* EXTERNAL */(_AS/* sLs0 */, _hh/* GHC.Arr.arrEleBottom */),
      _AU/* sLs6 */ = _AT/* sLs4 */,
      _AV/* sLs7 */ = E(_AS/* sLs0 */);
      if(!_AV/* sLs7 */){
        return new T(function(){
          return new T4(0,E(_AP/* sLrX */),E(_AQ/* sLrY */),0,_AU/* sLs6 */);
        });
      }else{
        var _AW/* sLs8 */ = function(_AX/* sLs9 */, _AY/* sLsa */, _/* EXTERNAL */){
          while(1){
            var _AZ/* sLsc */ = E(_AX/* sLs9 */);
            if(!_AZ/* sLsc */._){
              return E(_/* EXTERNAL */);
            }else{
              var _/* EXTERNAL */ = _AU/* sLs6 */[_AY/* sLsa */] = _AZ/* sLsc */.a;
              if(_AY/* sLsa */!=(_AV/* sLs7 */-1|0)){
                var _B0/*  sLsa */ = _AY/* sLsa */+1|0;
                _AX/* sLs9 */ = _AZ/* sLsc */.b;
                _AY/* sLsa */ = _B0/*  sLsa */;
                continue;
              }else{
                return E(_/* EXTERNAL */);
              }
            }
          }
        },
        _/* EXTERNAL */ = B(_AW/* sLs8 */(_AN/* sLrV */, 0, _/* EXTERNAL */));
        return new T(function(){
          return new T4(0,E(_AP/* sLrX */),E(_AQ/* sLrY */),_AV/* sLs7 */,_AU/* sLs6 */);
        });
      }
    }else{
      return E(_ye/* GHC.Arr.negRange */);
    }
  };
  return new F(function(){return _yu/* GHC.ST.runSTRep */(_AR/* sLsy */);});
},
_B1/* $w$ctraverse */ = function(_B2/* s5AkJ */, _B3/* s5AkK */, _B4/* s5AkL */, _B5/* s5AkM */){
  var _B6/* s5Alb */ = new T(function(){
    var _B7/* s5AkQ */ = E(_B5/* s5AkM */),
    _B8/* s5AkV */ = _B7/* s5AkQ */.c-1|0,
    _B9/* s5AkW */ = new T(function(){
      return B(A2(_cU/* GHC.Base.pure */,_B3/* s5AkK */, _o/* GHC.Types.[] */));
    });
    if(0<=_B8/* s5AkV */){
      var _Ba/* s5AkZ */ = new T(function(){
        return B(_94/* GHC.Base.$p1Applicative */(_B3/* s5AkK */));
      }),
      _Bb/* s5Al0 */ = function(_Bc/* s5Al1 */){
        var _Bd/* s5Al6 */ = new T(function(){
          var _Be/* s5Al5 */ = new T(function(){
            return B(A1(_B4/* s5AkL */,new T(function(){
              return E(_B7/* s5AkQ */.d[_Bc/* s5Al1 */]);
            })));
          });
          return B(A3(_9c/* GHC.Base.fmap */,_Ba/* s5AkZ */, _AB/* GHC.Types.: */, _Be/* s5Al5 */));
        });
        return new F(function(){return A3(_9a/* GHC.Base.<*> */,_B3/* s5AkK */, _Bd/* s5Al6 */, new T(function(){
          if(_Bc/* s5Al1 */!=_B8/* s5AkV */){
            return B(_Bb/* s5Al0 */(_Bc/* s5Al1 */+1|0));
          }else{
            return E(_B9/* s5AkW */);
          }
        }));});
      };
      return B(_Bb/* s5Al0 */(0));
    }else{
      return E(_B9/* s5AkW */);
    }
  }),
  _Bf/* s5AkO */ = new T(function(){
    return B(_AE/* GHC.Arr.bounds */(_B2/* s5AkJ */, _B5/* s5AkM */));
  });
  return new F(function(){return A3(_9c/* GHC.Base.fmap */,B(_94/* GHC.Base.$p1Applicative */(_B3/* s5AkK */)), function(_Bg/* B1 */){
    return new F(function(){return _AK/* GHC.Arr.listArray */(_B2/* s5AkJ */, _Bf/* s5AkO */, _Bg/* B1 */);});
  }, _B6/* s5Alb */);});
},
_Bh/* () */ = 0,
_Bi/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _Bh/* GHC.Tuple.() */;
},
_Bj/* vertex_f1 */ = new T(function(){
  return eval/* EXTERNAL */("vertex");
}),
_Bk/* $wa1 */ = function(_Bl/* smJ8 */, _Bm/* smJ9 */, _Bn/* smJa */, _Bo/* smJb */, _Bp/* smJc */, _Bq/* smJd */, _/* EXTERNAL */){
  var _Br/* smJv */ = __apply/* EXTERNAL */(E(_Bj/* Lib.Screen.vertex_f1 */), new T2(1,_Bq/* smJd */,new T2(1,_Bp/* smJc */,new T2(1,_Bo/* smJb */,new T2(1,_Bn/* smJa */,new T2(1,_Bm/* smJ9 */,new T2(1,_Bl/* smJ8 */,_o/* GHC.Types.[] */)))))));
  return new F(function(){return _Bi/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_Bs/* drawObject2 */ = function(_Bt/* smJy */, _/* EXTERNAL */){
  while(1){
    var _Bu/* smJA */ = E(_Bt/* smJy */);
    if(!_Bu/* smJA */._){
      return _Bh/* GHC.Tuple.() */;
    }else{
      var _Bv/* smJD */ = E(_Bu/* smJA */.a),
      _Bw/* smJH */ = E(_Bv/* smJD */.a),
      _Bx/* smJL */ = E(_Bw/* smJH */.a),
      _By/* smJV */ = E(_Bw/* smJH */.b),
      _Bz/* smK4 */ = B(_Bk/* Lib.Object.$wa1 */(E(_Bx/* smJL */.a), E(_Bx/* smJL */.b), E(_Bx/* smJL */.c), E(_By/* smJV */.a), E(_By/* smJV */.b), E(_Bw/* smJH */.c), _/* EXTERNAL */)),
      _BA/* smK7 */ = E(_Bv/* smJD */.b),
      _BB/* smKb */ = E(_BA/* smK7 */.a),
      _BC/* smKl */ = E(_BA/* smK7 */.b),
      _BD/* smKu */ = B(_Bk/* Lib.Object.$wa1 */(E(_BB/* smKb */.a), E(_BB/* smKb */.b), E(_BB/* smKb */.c), E(_BC/* smKl */.a), E(_BC/* smKl */.b), E(_BA/* smK7 */.c), _/* EXTERNAL */)),
      _BE/* smKx */ = E(_Bv/* smJD */.c),
      _BF/* smKB */ = E(_BE/* smKx */.a),
      _BG/* smKL */ = E(_BE/* smKx */.b),
      _BH/* smKU */ = B(_Bk/* Lib.Object.$wa1 */(E(_BF/* smKB */.a), E(_BF/* smKB */.b), E(_BF/* smKB */.c), E(_BG/* smKL */.a), E(_BG/* smKL */.b), E(_BE/* smKx */.c), _/* EXTERNAL */));
      _Bt/* smJy */ = _Bu/* smJA */.b;
      continue;
    }
  }
},
_BI/* drawTriangles_f1 */ = new T(function(){
  return eval/* EXTERNAL */("drawTriangles");
}),
_BJ/* drawTriangles1 */ = function(_/* EXTERNAL */){
  var _BK/* s3sw */ = __app0/* EXTERNAL */(E(_BI/* Lib.Screen.drawTriangles_f1 */));
  return new F(function(){return _Bi/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_BL/* $wa */ = function(_BM/* smKX */, _/* EXTERNAL */){
  var _BN/* smKZ */ = B(_Bs/* Lib.Object.drawObject2 */(_BM/* smKX */, _/* EXTERNAL */));
  return new F(function(){return _BJ/* Lib.Screen.drawTriangles1 */(_/* EXTERNAL */);});
},
_BO/* drawObject1 */ = function(_BP/* smL2 */, _/* EXTERNAL */){
  return new F(function(){return _BL/* Lib.Object.$wa */(E(_BP/* smL2 */).h, _/* EXTERNAL */);});
},
_BQ/* draw_f1 */ = new T(function(){
  return eval/* EXTERNAL */("draw");
}),
_BR/* $fApplicativeIdentity2 */ = function(_BS/* s6Rmj */){
  return E(_BS/* s6Rmj */);
},
_BT/* $fApplicativeIdentity3 */ = function(_BU/* s6RlP */){
  return E(_BU/* s6RlP */);
},
_BV/* $fApplicativeIdentity_$c*> */ = function(_BW/* s6Ro6 */, _BX/* s6Ro7 */){
  return E(_BX/* s6Ro7 */);
},
_BY/* $fFunctorIdentity1 */ = function(_BZ/* s6RlM */, _C0/* s6RlN */){
  return E(_BZ/* s6RlM */);
},
_C1/* $fFunctorIdentity2 */ = function(_C2/* s6Rmk */){
  return E(_C2/* s6Rmk */);
},
_C3/* $fFunctorIdentity */ = new T2(0,_C1/* Data.Functor.Identity.$fFunctorIdentity2 */,_BY/* Data.Functor.Identity.$fFunctorIdentity1 */),
_C4/* a1 */ = function(_C5/* s6Ro8 */, _C6/* s6Ro9 */){
  return E(_C5/* s6Ro8 */);
},
_C7/* $fApplicativeIdentity */ = new T5(0,_C3/* Data.Functor.Identity.$fFunctorIdentity */,_BT/* Data.Functor.Identity.$fApplicativeIdentity3 */,_BR/* Data.Functor.Identity.$fApplicativeIdentity2 */,_BV/* Data.Functor.Identity.$fApplicativeIdentity_$c*> */,_C4/* Data.Functor.Identity.a1 */),
_C8/* $fShowDouble_$cshow */ = function(_C9/* s1lc7 */){
  var _Ca/* s1lcb */ = jsShow/* EXTERNAL */(E(_C9/* s1lc7 */));
  return new F(function(){return fromJSStr/* EXTERNAL */(_Ca/* s1lcb */);});
},
_Cb/* jsShowD1 */ = function(_Cc/* s7sI */){
  var _Cd/* s7sM */ = jsShow/* EXTERNAL */(E(_Cc/* s7sI */));
  return new F(function(){return fromJSStr/* EXTERNAL */(_Cd/* s7sM */);});
},
_Ce/* $fShowDouble1 */ = function(_Cf/* s1kz8 */){
  var _Cg/* s1kz9 */ = new T(function(){
    return B(_Cb/* GHC.HastePrim.jsShowD1 */(_Cf/* s1kz8 */));
  });
  return function(_Ch/* _fa_1 */){
    return new F(function(){return _f/* GHC.Base.++ */(_Cg/* s1kz9 */, _Ch/* _fa_1 */);});
  };
},
_Ci/* $fShowDouble_$cshowList */ = function(_Cj/* B2 */, _Ck/* B1 */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_Ce/* GHC.Float.$fShowDouble1 */, _Cj/* B2 */, _Ck/* B1 */);});
},
_Cl/* $fShowDouble_$cshowsPrec */ = function(_Cm/* s1lcf */, _Cn/* s1lcg */){
  var _Co/* s1lch */ = new T(function(){
    return B(_Cb/* GHC.HastePrim.jsShowD1 */(_Cn/* s1lcg */));
  });
  return function(_Ch/* _fa_1 */){
    return new F(function(){return _f/* GHC.Base.++ */(_Co/* s1lch */, _Ch/* _fa_1 */);});
  };
},
_Cp/* $fShowDouble */ = new T3(0,_Cl/* GHC.Float.$fShowDouble_$cshowsPrec */,_C8/* GHC.Float.$fShowDouble_$cshow */,_Ci/* GHC.Float.$fShowDouble_$cshowList */),
_Cq/* $fShowWorld2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World "));
}),
_Cr/* $fShowWorld3 */ = 11,
_Cs/* showSpace1 */ = 32,
_Ct/* $w$cshowsPrec */ = function(_Cu/* saKa */, _Cv/* saKb */, _Cw/* saKc */, _Cx/* saKd */, _Cy/* saKe */){
  var _Cz/* saKf */ = new T(function(){
    return B(A3(_zL/* GHC.Show.showsPrec */,_Cu/* saKa */, _Cr/* Lib.World.$fShowWorld3 */, _Cw/* saKc */));
  }),
  _CA/* saKg */ = new T(function(){
    return B(A3(_zL/* GHC.Show.showsPrec */,_Cu/* saKa */, _Cr/* Lib.World.$fShowWorld3 */, _Cx/* saKd */));
  }),
  _CB/* saKh */ = new T(function(){
    return B(A3(_zL/* GHC.Show.showsPrec */,_Cu/* saKa */, _Cr/* Lib.World.$fShowWorld3 */, _Cy/* saKe */));
  }),
  _CC/* saKi */ = function(_CD/* saKj */){
    var _CE/* saKo */ = new T(function(){
      var _CF/* saKm */ = new T(function(){
        return B(A1(_CA/* saKg */,new T2(1,_Cs/* GHC.Show.showSpace1 */,new T(function(){
          return B(A1(_CB/* saKh */,_CD/* saKj */));
        }))));
      });
      return B(A1(_Cz/* saKf */,new T2(1,_Cs/* GHC.Show.showSpace1 */,_CF/* saKm */)));
    },1);
    return new F(function(){return _f/* GHC.Base.++ */(_Cq/* Lib.World.$fShowWorld2 */, _CE/* saKo */);});
  };
  if(_Cv/* saKb */<11){
    return E(_CC/* saKi */);
  }else{
    var _CG/* saKu */ = function(_CH/* saKr */){
      return new T2(1,_71/* GHC.Show.shows8 */,new T(function(){
        return B(_CC/* saKi */(new T2(1,_70/* GHC.Show.shows7 */,_CH/* saKr */)));
      }));
    };
    return E(_CG/* saKu */);
  }
},
_CI/* $fShowContactPoint9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Local "));
}),
_CJ/* $fShowLocal2 */ = 11,
_CK/* $w$cshowsPrec1 */ = function(_CL/* stHK */, _CM/* stHL */, _CN/* stHM */, _CO/* stHN */){
  var _CP/* stHO */ = new T(function(){
    return B(A3(_zL/* GHC.Show.showsPrec */,_CL/* stHK */, _CJ/* Lib.Constraint.$fShowLocal2 */, _CN/* stHM */));
  }),
  _CQ/* stHP */ = new T(function(){
    return B(A3(_zL/* GHC.Show.showsPrec */,_CL/* stHK */, _CJ/* Lib.Constraint.$fShowLocal2 */, _CO/* stHN */));
  });
  if(_CM/* stHL */<11){
    var _CR/* stHW */ = function(_CS/* stHS */){
      var _CT/* stHV */ = new T(function(){
        return B(A1(_CP/* stHO */,new T2(1,_Cs/* GHC.Show.showSpace1 */,new T(function(){
          return B(A1(_CQ/* stHP */,_CS/* stHS */));
        }))));
      },1);
      return new F(function(){return _f/* GHC.Base.++ */(_CI/* Lib.Constraint.$fShowContactPoint9 */, _CT/* stHV */);});
    };
    return E(_CR/* stHW */);
  }else{
    var _CU/* stI3 */ = function(_CV/* stHX */){
      var _CW/* stI2 */ = new T(function(){
        var _CX/* stI1 */ = new T(function(){
          return B(A1(_CP/* stHO */,new T2(1,_Cs/* GHC.Show.showSpace1 */,new T(function(){
            return B(A1(_CQ/* stHP */,new T2(1,_70/* GHC.Show.shows7 */,_CV/* stHX */)));
          }))));
        },1);
        return B(_f/* GHC.Base.++ */(_CI/* Lib.Constraint.$fShowContactPoint9 */, _CX/* stI1 */));
      });
      return new T2(1,_71/* GHC.Show.shows8 */,_CW/* stI2 */);
    };
    return E(_CU/* stI3 */);
  }
},
_CY/* $wlvl4 */ = function(_CZ/* se0u */, _D0/* se0v */, _D1/* se0w */){
  var _D2/* se0J */ = new T(function(){
    return B(A3(_zz/* GHC.List.foldr1 */,_zt/* GHC.Show.$fShow(,)1 */, new T2(1,new T(function(){
      var _D3/* se0x */ = E(_CZ/* se0u */);
      return B(_Ct/* Lib.World.$w$cshowsPrec */(_Cp/* GHC.Float.$fShowDouble */, 0, _D3/* se0x */.a, _D3/* se0x */.b, _D3/* se0x */.c));
    }),new T2(1,new T(function(){
      var _D4/* se0C */ = E(_D0/* se0v */);
      return B(_CK/* Lib.Constraint.$w$cshowsPrec1 */(_Cp/* GHC.Float.$fShowDouble */, 0, _D4/* se0C */.a, _D4/* se0C */.b));
    }),_o/* GHC.Types.[] */)), new T2(1,_70/* GHC.Show.shows7 */,_D1/* se0w */)));
  });
  return new T2(0,_71/* GHC.Show.shows8 */,_D2/* se0J */);
},
_D5/* lvl27 */ = function(_D6/* se0K */, _D7/* se0L */){
  var _D8/* se0M */ = E(_D6/* se0K */),
  _D9/* se0P */ = B(_CY/* Lib.Physics.$wlvl4 */(_D8/* se0M */.a, _D8/* se0M */.b, _D7/* se0L */));
  return new T2(1,_D9/* se0P */.a,_D9/* se0P */.b);
},
_Da/* $s$fShow(,)_$s$fShow(,)_$cshowList */ = function(_Db/* se9y */, _Dc/* se9z */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_D5/* Lib.Physics.lvl27 */, _Db/* se9y */, _Dc/* se9z */);});
},
_Dd/* $wa */ = function(_De/* se8p */, _Df/* se8q */, _Dg/* se8r */, _Dh/* se8s */, _Di/* se8t */, _Dj/* se8u */){
  var _Dk/* se9c */ = new T(function(){
    var _Dl/* se8v */ = E(_Dh/* se8s */),
    _Dm/* se8y */ = E(_Di/* se8t */),
    _Dn/* se94 */ = new T(function(){
      var _Do/* se8B */ = E(_Dl/* se8v */.a),
      _Dp/* se8F */ = E(_Dm/* se8y */.a);
      return new T3(0,new T(function(){
        return E(_Do/* se8B */.a)+E(_Dp/* se8F */.a)*5.0e-2;
      }),new T(function(){
        return E(_Do/* se8B */.b)+E(_Dp/* se8F */.b)*5.0e-2;
      }),new T(function(){
        return E(_Do/* se8B */.c)+E(_Dp/* se8F */.c)*5.0e-2;
      }));
    });
    return new T2(0,_Dn/* se94 */,new T(function(){
      return E(_Dl/* se8v */.b)+E(_Dm/* se8y */.b)*5.0e-2;
    }));
  });
  return new F(function(){return _nD/* Lib.Object.$wfitO */(_De/* se8p */, _Df/* se8q */, _Dg/* se8r */, _Dk/* se9c */, _Di/* se8t */, _Dj/* se8u */);});
},
_Dq/* $s$fArithWorld_$cnormalize1 */ = new T2(0,_iL/* GHC.Float.$fFloatingDouble */,_jk/* GHC.Classes.$fOrdDouble */),
_Dr/* go */ = function(_Ds/* se0Y */){
  while(1){
    var _Dt/* se0Z */ = E(_Ds/* se0Y */);
    if(!_Dt/* se0Z */._){
      return true;
    }else{
      if(E(_Dt/* se0Z */.a)<0){
        return false;
      }else{
        _Ds/* se0Y */ = _Dt/* se0Z */.b;
        continue;
      }
    }
  }
},
_Du/* $sgo */ = function(_Dv/* se0S */, _Dw/* se0T */){
  if(E(_Dv/* se0S */)<0){
    return false;
  }else{
    return new F(function(){return _Dr/* Lib.Physics.go */(_Dw/* se0T */);});
  }
},
_Dx/* $w$cdot */ = function(_Dy/* stDr */, _Dz/* stDs */, _DA/* stDt */, _DB/* stDu */, _DC/* stDv */){
  var _DD/* stDx */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_Dy/* stDr */))));
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_DD/* stDx */, new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_DD/* stDx */, _Dz/* stDs */, _DB/* stDu */));
  }), new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_DD/* stDx */, _DA/* stDt */, _DC/* stDv */));
  }));});
},
_DE/* $wtoLocal */ = function(_DF/* stB2 */, _DG/* stB3 */){
  var _DH/* stB4 */ = new T(function(){
    return E(E(_DG/* stB3 */).c);
  }),
  _DI/* stB9 */ = new T(function(){
    return E(E(_DF/* stB2 */).a);
  }),
  _DJ/* stBe */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_DI/* stB9 */));
    })));
  }),
  _DK/* stBf */ = new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_DJ/* stBe */, new T(function(){
      return E(E(E(_DG/* stB3 */).b).b);
    }), new T(function(){
      return E(E(E(_DG/* stB3 */).b).a);
    })));
  }),
  _DL/* stBz */ = new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_DJ/* stBe */, _DK/* stBf */, new T(function(){
      return B(A2(_bz/* GHC.Float.sin */,_DI/* stB9 */, _DH/* stB4 */));
    })));
  }),
  _DM/* stBx */ = new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_DJ/* stBe */, _DK/* stBf */, new T(function(){
      return B(A2(_bx/* GHC.Float.cos */,_DI/* stB9 */, _DH/* stB4 */));
    })));
  });
  return new T2(0,_DM/* stBx */,_DL/* stBz */);
},
_DN/* catMaybes1 */ = function(_DO/*  s9C1 */){
  while(1){
    var _DP/*  catMaybes1 */ = B((function(_DQ/* s9C1 */){
      var _DR/* s9C2 */ = E(_DQ/* s9C1 */);
      if(!_DR/* s9C2 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _DS/* s9C4 */ = _DR/* s9C2 */.b,
        _DT/* s9C5 */ = E(_DR/* s9C2 */.a);
        if(!_DT/* s9C5 */._){
          _DO/*  s9C1 */ = _DS/* s9C4 */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_DT/* s9C5 */.a,new T(function(){
            return B(_DN/* Data.Maybe.catMaybes1 */(_DS/* s9C4 */));
          }));
        }
      }
    })(_DO/*  s9C1 */));
    if(_DP/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _DP/*  catMaybes1 */;
    }
  }
},
_DU/* $wintersect */ = function(_DV/* se16 */, _DW/* se17 */){
  var _DX/* se18 */ = function(_DY/* se19 */, _DZ/* se1a */){
    var _E0/* se1b */ = E(_DY/* se19 */);
    if(!_E0/* se1b */._){
      return E(_DZ/* se1a */);
    }else{
      var _E1/* se1c */ = _E0/* se1b */.a,
      _E2/* se7v */ = new T(function(){
        var _E3/* se1e */ = function(_E4/*  se1f */){
          while(1){
            var _E5/*  se1e */ = B((function(_E6/* se1f */){
              var _E7/* se1g */ = E(_E6/* se1f */);
              if(!_E7/* se1g */._){
                return __Z/* EXTERNAL */;
              }else{
                var _E8/* se1i */ = _E7/* se1g */.b,
                _E9/* se1n */ = E(E(_E1/* se1c */).a),
                _Ea/* se1o */ = _E9/* se1n */.a,
                _Eb/* se1p */ = _E9/* se1n */.b,
                _Ec/* se1q */ = _E9/* se1n */.c,
                _Ed/* se1r */ = E(_E7/* se1g */.a),
                _Ee/* se1v */ = E(_Ed/* se1r */.a),
                _Ef/* se1z */ = E(_Ee/* se1v */.a),
                _Eg/* se1A */ = _Ef/* se1z */.a,
                _Eh/* se1B */ = _Ef/* se1z */.b,
                _Ei/* se1C */ = _Ef/* se1z */.c,
                _Ej/* se1D */ = E(_Ed/* se1r */.c),
                _Ek/* se1H */ = E(_Ej/* se1D */.a),
                _El/* se1I */ = _Ek/* se1H */.a,
                _Em/* se1J */ = _Ek/* se1H */.b,
                _En/* se1K */ = _Ek/* se1H */.c,
                _Eo/* se1L */ = E(_Ed/* se1r */.b),
                _Ep/* se1P */ = E(_Eo/* se1L */.a),
                _Eq/* se1Q */ = _Ep/* se1P */.a,
                _Er/* se1R */ = _Ep/* se1P */.b,
                _Es/* se1S */ = _Ep/* se1P */.c,
                _Et/* se1T */ = new T(function(){
                  return E(_El/* se1I */)+ -E(_Eg/* se1A */);
                }),
                _Eu/* se20 */ = new T(function(){
                  return E(_Em/* se1J */)+ -E(_Eh/* se1B */);
                }),
                _Ev/* se27 */ = new T(function(){
                  return E(_En/* se1K */)+ -E(_Ei/* se1C */);
                }),
                _Ew/* se2e */ = new T(function(){
                  return E(_El/* se1I */)+ -E(_Eq/* se1Q */);
                }),
                _Ex/* se2l */ = new T(function(){
                  return E(_Em/* se1J */)+ -E(_Er/* se1R */);
                }),
                _Ey/* se2s */ = new T(function(){
                  return E(_En/* se1K */)+ -E(_Es/* se1S */);
                }),
                _Ez/* se39 */ = B(_jw/* Lib.World.$w$cnormalize */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, new T(function(){
                  return E(_Eu/* se20 */)*E(_Ey/* se2s */)-E(_Ex/* se2l */)*E(_Ev/* se27 */);
                }), new T(function(){
                  return E(_Ev/* se27 */)*E(_Ew/* se2e */)-E(_Ey/* se2s */)*E(_Et/* se1T */);
                }), new T(function(){
                  return E(_Et/* se1T */)*E(_Ex/* se2l */)-E(_Ew/* se2e */)*E(_Eu/* se20 */);
                }))),
                _EA/* se3a */ = _Ez/* se39 */.a,
                _EB/* se3b */ = _Ez/* se39 */.b,
                _EC/* se3c */ = _Ez/* se39 */.c,
                _ED/* se3y */ = B(_jm/* Lib.World.$w$cdot */(_iL/* GHC.Float.$fFloatingDouble */, new T(function(){
                  return E(_Ea/* se1o */)+ -E(_Eg/* se1A */);
                }), new T(function(){
                  return E(_Eb/* se1p */)+ -E(_Eh/* se1B */);
                }), new T(function(){
                  return E(_Ec/* se1q */)+ -E(_Ei/* se1C */);
                }), _EA/* se3a */, _EB/* se3b */, _EC/* se3c */)),
                _EE/* se3A */ = function(_EF/* se3B */){
                  if(_EF/* se3B */>=0.1){
                    return __Z/* EXTERNAL */;
                  }else{
                    var _EG/* se3E */ = new T(function(){
                      return E(_Ea/* se1o */)+ -(E(_EA/* se3a */)*_ED/* se3y */);
                    }),
                    _EH/* se3M */ = new T(function(){
                      return E(_Eb/* se1p */)+ -(E(_EB/* se3b */)*_ED/* se3y */);
                    }),
                    _EI/* se3U */ = new T(function(){
                      return E(_Ec/* se1q */)+ -(E(_EC/* se3c */)*_ED/* se3y */);
                    }),
                    _EJ/* se42 */ = function(_EK/* se43 */, _EL/* se44 */, _EM/* se45 */, _EN/* se46 */, _EO/* se47 */, _EP/* se48 */, _EQ/* se49 */, _ER/* se4a */, _ES/* se4b */){
                      var _ET/* se4c */ = new T(function(){
                        return E(_EQ/* se49 */)+ -E(_EN/* se46 */);
                      }),
                      _EU/* se4j */ = new T(function(){
                        return E(_ER/* se4a */)+ -E(_EO/* se47 */);
                      }),
                      _EV/* se4q */ = new T(function(){
                        return E(_ES/* se4b */)+ -E(_EP/* se48 */);
                      }),
                      _EW/* se57 */ = B(_jw/* Lib.World.$w$cnormalize */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, new T(function(){
                        return E(_EB/* se3b */)*E(_EV/* se4q */)-E(_EU/* se4j */)*E(_EC/* se3c */);
                      }), new T(function(){
                        return E(_EC/* se3c */)*E(_ET/* se4c */)-E(_EV/* se4q */)*E(_EA/* se3a */);
                      }), new T(function(){
                        return E(_EA/* se3a */)*E(_EU/* se4j */)-E(_ET/* se4c */)*E(_EB/* se3b */);
                      }))),
                      _EX/* se58 */ = _EW/* se57 */.a,
                      _EY/* se59 */ = _EW/* se57 */.b,
                      _EZ/* se5a */ = _EW/* se57 */.c;
                      return B(_jm/* Lib.World.$w$cdot */(_iL/* GHC.Float.$fFloatingDouble */, new T(function(){
                        return E(_EG/* se3E */)+ -E(_EN/* se46 */);
                      }), new T(function(){
                        return E(_EH/* se3M */)+ -E(_EO/* se47 */);
                      }), new T(function(){
                        return E(_EI/* se3U */)+ -E(_EP/* se48 */);
                      }), _EX/* se58 */, _EY/* se59 */, _EZ/* se5a */))/B(_jm/* Lib.World.$w$cdot */(_iL/* GHC.Float.$fFloatingDouble */, new T(function(){
                        return E(_EK/* se43 */)+ -E(_EN/* se46 */);
                      }), new T(function(){
                        return E(_EL/* se44 */)+ -E(_EO/* se47 */);
                      }), new T(function(){
                        return E(_EM/* se45 */)+ -E(_EP/* se48 */);
                      }), _EX/* se58 */, _EY/* se59 */, _EZ/* se5a */));
                    },
                    _F0/* se5V */ = new T(function(){
                      return B(_EJ/* se42 */(_Eg/* se1A */, _Eh/* se1B */, _Ei/* se1C */, _Eq/* se1Q */, _Er/* se1R */, _Es/* se1S */, _El/* se1I */, _Em/* se1J */, _En/* se1K */));
                    }),
                    _F1/* se5X */ = new T(function(){
                      return B(_EJ/* se42 */(_Eq/* se1Q */, _Er/* se1R */, _Es/* se1S */, _El/* se1I */, _Em/* se1J */, _En/* se1K */, _Eg/* se1A */, _Eh/* se1B */, _Ei/* se1C */));
                    }),
                    _F2/* se5Z */ = new T(function(){
                      return B(_EJ/* se42 */(_El/* se1I */, _Em/* se1J */, _En/* se1K */, _Eg/* se1A */, _Eh/* se1B */, _Ei/* se1C */, _Eq/* se1Q */, _Er/* se1R */, _Es/* se1S */));
                    });
                    if(!B(_Du/* Lib.Physics.$sgo */(_F0/* se5V */, new T2(1,_F1/* se5X */,new T2(1,_F2/* se5Z */,_o/* GHC.Types.[] */))))){
                      return __Z/* EXTERNAL */;
                    }else{
                      var _F3/* se6N */ = new T(function(){
                        var _F4/* se64 */ = B(_DE/* Lib.Constraint.$wtoLocal */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, _Ee/* se1v */)),
                        _F5/* se67 */ = B(_DE/* Lib.Constraint.$wtoLocal */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, _Eo/* se1L */)),
                        _F6/* se6a */ = B(_DE/* Lib.Constraint.$wtoLocal */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, _Ej/* se1D */));
                        return new T2(0,new T(function(){
                          return E(_F4/* se64 */.a)*E(_F0/* se5V */)+E(_F5/* se67 */.a)*E(_F1/* se5X */)+E(_F6/* se6a */.a)*E(_F2/* se5Z */);
                        }),new T(function(){
                          return E(_F4/* se64 */.b)*E(_F0/* se5V */)+E(_F5/* se67 */.b)*E(_F1/* se5X */)+E(_F6/* se6a */.b)*E(_F2/* se5Z */);
                        }));
                      });
                      return new T1(1,_F3/* se6N */);
                    }
                  }
                },
                _F7/* se6O */ = E(_ED/* se3y */);
                if(!_F7/* se6O */){
                  var _F8/* se6W */ = B(_EE/* se3A */(0));
                  if(!_F8/* se6W */._){
                    _E4/*  se1f */ = _E8/* se1i */;
                    return __continue/* EXTERNAL */;
                  }else{
                    return E(_F8/* se6W */);
                  }
                }else{
                  if(_F7/* se6O */<=0){
                    var _F9/* se6S */ = B(_EE/* se3A */( -_F7/* se6O */));
                    if(!_F9/* se6S */._){
                      _E4/*  se1f */ = _E8/* se1i */;
                      return __continue/* EXTERNAL */;
                    }else{
                      return E(_F9/* se6S */);
                    }
                  }else{
                    var _Fa/* se6U */ = B(_EE/* se3A */(_F7/* se6O */));
                    if(!_Fa/* se6U */._){
                      _E4/*  se1f */ = _E8/* se1i */;
                      return __continue/* EXTERNAL */;
                    }else{
                      return E(_Fa/* se6U */);
                    }
                  }
                }
              }
            })(_E4/*  se1f */));
            if(_E5/*  se1e */!=__continue/* EXTERNAL */){
              return _E5/*  se1e */;
            }
          }
        },
        _Fb/* se6Y */ = B(_E3/* se1e */(_DW/* se17 */));
        if(!_Fb/* se6Y */._){
          return __Z/* EXTERNAL */;
        }else{
          var _Fc/* se70 */ = B(_DE/* Lib.Constraint.$wtoLocal */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, _E1/* se1c */)),
          _Fd/* se73 */ = E(_Fb/* se6Y */.a),
          _Fe/* se76 */ = new T(function(){
            return E(_Fd/* se73 */.a)+ -E(_Fc/* se70 */.a);
          }),
          _Ff/* se7d */ = new T(function(){
            return E(_Fd/* se73 */.b)+ -E(_Fc/* se70 */.b);
          });
          if(Math.sqrt/* EXTERNAL */(B(_Dx/* Lib.Constraint.$w$cdot */(_iL/* GHC.Float.$fFloatingDouble */, _Fe/* se76 */, _Ff/* se7d */, _Fe/* se76 */, _Ff/* se7d */)))<1.0e-4){
            return __Z/* EXTERNAL */;
          }else{
            return new T1(1,new T2(0,new T(function(){
              return E(E(_E1/* se1c */).a);
            }),_Fd/* se73 */));
          }
        }
      });
      return new T2(1,_E2/* se7v */,new T(function(){
        return B(_DX/* se18 */(_E0/* se1b */.b, _DZ/* se1a */));
      }));
    }
  };
  return new F(function(){return _DN/* Data.Maybe.catMaybes1 */(B(_DX/* se18 */(_DV/* se16 */, _o/* GHC.Types.[] */)));});
},
_Fg/* a25 */ = function(_Fh/* se7y */){
  var _Fi/* se7z */ = E(_Fh/* se7y */),
  _Fj/* se7B */ = _Fi/* se7z */.b,
  _Fk/* se7G */ = _Fi/* se7z */.g,
  _Fl/* se8o */ = new T(function(){
    var _Fm/* se7J */ = E(_Fi/* se7z */.e),
    _Fn/* se8n */ = new T(function(){
      var _Fo/* se7M */ = E(_Fm/* se7J */.a),
      _Fp/* se7Q */ = E(_Fj/* se7B */),
      _Fq/* se7U */ = E(_Fk/* se7G */),
      _Fr/* se7Y */ = B(_ka/* Lib.World.$wperpTo */(_Dq/* Lib.Physics.$s$fArithWorld_$cnormalize1 */, _Fp/* se7Q */.a, _Fp/* se7Q */.b, _Fp/* se7Q */.c, _Fq/* se7U */.a, _Fq/* se7U */.b, _Fq/* se7U */.c));
      return new T3(0,new T(function(){
        return E(_Fo/* se7M */.a)+E(_Fr/* se7Y */.a)*5.0e-2;
      }),new T(function(){
        return E(_Fo/* se7M */.b)+E(_Fr/* se7Y */.b)*5.0e-2;
      }),new T(function(){
        return E(_Fo/* se7M */.c)+E(_Fr/* se7Y */.c)*5.0e-2;
      }));
    });
    return new T2(0,_Fn/* se8n */,_Fm/* se7J */.b);
  });
  return {_:0,a:_Fi/* se7z */.a,b:_Fj/* se7B */,c:_Fi/* se7z */.c,d:_Fi/* se7z */.d,e:_Fl/* se8o */,f:_Fi/* se7z */.f,g:_Fk/* se7G */,h:_Fi/* se7z */.h,i:_Fi/* se7z */.i};
},
_Fs/* a26 */ = function(_Ft/* se9d */){
  var _Fu/* se9e */ = E(_Ft/* se9d */),
  _Fv/* se9o */ = B(_Dd/* Lib.Physics.$wa */(_Fu/* se9e */.a, _Fu/* se9e */.b, _Fu/* se9e */.c, _Fu/* se9e */.d, _Fu/* se9e */.e, _Fu/* se9e */.f));
  return {_:0,a:_Fv/* se9o */.a,b:_Fv/* se9o */.b,c:_Fv/* se9o */.c,d:_Fv/* se9o */.d,e:_Fv/* se9o */.e,f:_Fv/* se9o */.f,g:_Fv/* se9o */.g,h:_Fv/* se9o */.h,i:_Fv/* se9o */.i};
},
_Fw/* go1 */ = function(_Fx/* se9A */){
  var _Fy/* se9B */ = E(_Fx/* se9A */);
  if(!_Fy/* se9B */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_Fy/* se9B */.a, new T(function(){
      return B(_Fw/* Lib.Physics.go1 */(_Fy/* se9B */.b));
    },1));});
  }
},
_Fz/* lvl29 */ = new T2(1,_70/* GHC.Show.shows7 */,_o/* GHC.Types.[] */),
_FA/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_FB/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_FC/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_FD/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_FA/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_FB/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_FC/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_FE/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_FD/* GHC.IO.Exception.$fExceptionIOException_wild */,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_FF/* $fExceptionIOException3 */ = function(_FG/* s3MW8 */){
  return E(_FE/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_FH/* $fExceptionIOException_$cfromException */ = function(_FI/* s3N1e */){
  var _FJ/* s3N1f */ = E(_FI/* s3N1e */);
  return new F(function(){return _28/* Data.Typeable.cast */(B(_26/* GHC.Exception.$p1Exception */(_FJ/* s3N1f */.a)), _FF/* GHC.IO.Exception.$fExceptionIOException3 */, _FJ/* s3N1f */.b);});
},
_FK/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_FL/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_FM/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_FN/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_FO/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_FP/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_FQ/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_FR/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_FS/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_FT/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_FU/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_FV/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_FW/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_FX/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_FY/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_FZ/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_G0/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_G1/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_G2/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_G3/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_G4/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_G5/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_G6/* $w$cshowsPrec3 */ = function(_G7/* s3N03 */, _G8/* s3N04 */){
  switch(E(_G7/* s3N03 */)){
    case 0:
      return new F(function(){return _f/* GHC.Base.++ */(_FX/* GHC.IO.Exception.lvl18 */, _G8/* s3N04 */);});
      break;
    case 1:
      return new F(function(){return _f/* GHC.Base.++ */(_FW/* GHC.IO.Exception.lvl17 */, _G8/* s3N04 */);});
      break;
    case 2:
      return new F(function(){return _f/* GHC.Base.++ */(_FV/* GHC.IO.Exception.lvl16 */, _G8/* s3N04 */);});
      break;
    case 3:
      return new F(function(){return _f/* GHC.Base.++ */(_FU/* GHC.IO.Exception.lvl15 */, _G8/* s3N04 */);});
      break;
    case 4:
      return new F(function(){return _f/* GHC.Base.++ */(_FT/* GHC.IO.Exception.lvl14 */, _G8/* s3N04 */);});
      break;
    case 5:
      return new F(function(){return _f/* GHC.Base.++ */(_FS/* GHC.IO.Exception.lvl13 */, _G8/* s3N04 */);});
      break;
    case 6:
      return new F(function(){return _f/* GHC.Base.++ */(_FR/* GHC.IO.Exception.lvl12 */, _G8/* s3N04 */);});
      break;
    case 7:
      return new F(function(){return _f/* GHC.Base.++ */(_FQ/* GHC.IO.Exception.lvl11 */, _G8/* s3N04 */);});
      break;
    case 8:
      return new F(function(){return _f/* GHC.Base.++ */(_FP/* GHC.IO.Exception.lvl10 */, _G8/* s3N04 */);});
      break;
    case 9:
      return new F(function(){return _f/* GHC.Base.++ */(_G5/* GHC.IO.Exception.lvl9 */, _G8/* s3N04 */);});
      break;
    case 10:
      return new F(function(){return _f/* GHC.Base.++ */(_G4/* GHC.IO.Exception.lvl8 */, _G8/* s3N04 */);});
      break;
    case 11:
      return new F(function(){return _f/* GHC.Base.++ */(_G3/* GHC.IO.Exception.lvl7 */, _G8/* s3N04 */);});
      break;
    case 12:
      return new F(function(){return _f/* GHC.Base.++ */(_G2/* GHC.IO.Exception.lvl6 */, _G8/* s3N04 */);});
      break;
    case 13:
      return new F(function(){return _f/* GHC.Base.++ */(_G1/* GHC.IO.Exception.lvl5 */, _G8/* s3N04 */);});
      break;
    case 14:
      return new F(function(){return _f/* GHC.Base.++ */(_G0/* GHC.IO.Exception.lvl4 */, _G8/* s3N04 */);});
      break;
    case 15:
      return new F(function(){return _f/* GHC.Base.++ */(_FZ/* GHC.IO.Exception.lvl3 */, _G8/* s3N04 */);});
      break;
    case 16:
      return new F(function(){return _f/* GHC.Base.++ */(_FY/* GHC.IO.Exception.lvl2 */, _G8/* s3N04 */);});
      break;
    case 17:
      return new F(function(){return _f/* GHC.Base.++ */(_FO/* GHC.IO.Exception.lvl1 */, _G8/* s3N04 */);});
      break;
    default:
      return new F(function(){return _f/* GHC.Base.++ */(_FN/* GHC.IO.Exception.lvl */, _G8/* s3N04 */);});
  }
},
_G9/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_Ga/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_Gb/* $w$cshowsPrec2 */ = function(_Gc/* s3N0c */, _Gd/* s3N0d */, _Ge/* s3N0e */, _Gf/* s3N0f */, _Gg/* s3N0g */, _Gh/* s3N0h */){
  var _Gi/* s3N0i */ = new T(function(){
    var _Gj/* s3N0j */ = new T(function(){
      var _Gk/* s3N0p */ = new T(function(){
        var _Gl/* s3N0k */ = E(_Gf/* s3N0f */);
        if(!_Gl/* s3N0k */._){
          return E(_Gh/* s3N0h */);
        }else{
          var _Gm/* s3N0o */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_Gl/* s3N0k */, new T(function(){
              return B(_f/* GHC.Base.++ */(_FL/* GHC.IO.Exception.$fExceptionIOException1 */, _Gh/* s3N0h */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_FM/* GHC.IO.Exception.$fExceptionIOException2 */, _Gm/* s3N0o */));
        }
      },1);
      return B(_G6/* GHC.IO.Exception.$w$cshowsPrec3 */(_Gd/* s3N0d */, _Gk/* s3N0p */));
    }),
    _Gn/* s3N0q */ = E(_Ge/* s3N0e */);
    if(!_Gn/* s3N0q */._){
      return E(_Gj/* s3N0j */);
    }else{
      return B(_f/* GHC.Base.++ */(_Gn/* s3N0q */, new T(function(){
        return B(_f/* GHC.Base.++ */(_FK/* GHC.IO.Exception.$fExceptionArrayException2 */, _Gj/* s3N0j */));
      },1)));
    }
  }),
  _Go/* s3N0u */ = E(_Gg/* s3N0g */);
  if(!_Go/* s3N0u */._){
    var _Gp/* s3N0v */ = E(_Gc/* s3N0c */);
    if(!_Gp/* s3N0v */._){
      return E(_Gi/* s3N0i */);
    }else{
      var _Gq/* s3N0x */ = E(_Gp/* s3N0v */.a);
      if(!_Gq/* s3N0x */._){
        var _Gr/* s3N0C */ = new T(function(){
          var _Gs/* s3N0B */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_G9/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_f/* GHC.Base.++ */(_FK/* GHC.IO.Exception.$fExceptionArrayException2 */, _Gi/* s3N0i */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_Gq/* s3N0x */.a, _Gs/* s3N0B */));
        },1);
        return new F(function(){return _f/* GHC.Base.++ */(_Ga/* GHC.IO.Handle.Types.showHandle2 */, _Gr/* s3N0C */);});
      }else{
        var _Gt/* s3N0I */ = new T(function(){
          var _Gu/* s3N0H */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_G9/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_f/* GHC.Base.++ */(_FK/* GHC.IO.Exception.$fExceptionArrayException2 */, _Gi/* s3N0i */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_Gq/* s3N0x */.a, _Gu/* s3N0H */));
        },1);
        return new F(function(){return _f/* GHC.Base.++ */(_Ga/* GHC.IO.Handle.Types.showHandle2 */, _Gt/* s3N0I */);});
      }
    }
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_Go/* s3N0u */.a, new T(function(){
      return B(_f/* GHC.Base.++ */(_FK/* GHC.IO.Exception.$fExceptionArrayException2 */, _Gi/* s3N0i */));
    },1));});
  }
},
_Gv/* $fExceptionIOException_$cshow */ = function(_Gw/* s3N16 */){
  var _Gx/* s3N17 */ = E(_Gw/* s3N16 */);
  return new F(function(){return _Gb/* GHC.IO.Exception.$w$cshowsPrec2 */(_Gx/* s3N17 */.a, _Gx/* s3N17 */.b, _Gx/* s3N17 */.c, _Gx/* s3N17 */.d, _Gx/* s3N17 */.f, _o/* GHC.Types.[] */);});
},
_Gy/* $fExceptionIOException_$cshowsPrec */ = function(_Gz/* s3N0L */, _GA/* s3N0M */, _GB/* s3N0N */){
  var _GC/* s3N0O */ = E(_GA/* s3N0M */);
  return new F(function(){return _Gb/* GHC.IO.Exception.$w$cshowsPrec2 */(_GC/* s3N0O */.a, _GC/* s3N0O */.b, _GC/* s3N0O */.c, _GC/* s3N0O */.d, _GC/* s3N0O */.f, _GB/* s3N0N */);});
},
_GD/* $s$dmshow9 */ = function(_GE/* s3N0V */, _GF/* s3N0W */){
  var _GG/* s3N0X */ = E(_GE/* s3N0V */);
  return new F(function(){return _Gb/* GHC.IO.Exception.$w$cshowsPrec2 */(_GG/* s3N0X */.a, _GG/* s3N0X */.b, _GG/* s3N0X */.c, _GG/* s3N0X */.d, _GG/* s3N0X */.f, _GF/* s3N0W */);});
},
_GH/* $fShowIOException_$cshowList */ = function(_GI/* s3N14 */, _GJ/* s3N15 */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_GD/* GHC.IO.Exception.$s$dmshow9 */, _GI/* s3N14 */, _GJ/* s3N15 */);});
},
_GK/* $fShowIOException */ = new T3(0,_Gy/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_Gv/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_GH/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_GL/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_FF/* GHC.IO.Exception.$fExceptionIOException3 */,_GK/* GHC.IO.Exception.$fShowIOException */,_GM/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_FH/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_Gv/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_GM/* $fExceptionIOException_$ctoException */ = function(_GN/* B1 */){
  return new T2(0,_GL/* GHC.IO.Exception.$fExceptionIOException */,_GN/* B1 */);
},
_GO/* Nothing */ = __Z/* EXTERNAL */,
_GP/* UserError */ = 7,
_GQ/* str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at Lib\\Physics.hs:85:7-13"));
}),
_GR/* lvl32 */ = new T6(0,_GO/* GHC.Base.Nothing */,_GP/* GHC.IO.Exception.UserError */,_o/* GHC.Types.[] */,_GQ/* Lib.Physics.str */,_GO/* GHC.Base.Nothing */,_GO/* GHC.Base.Nothing */),
_GS/* lvl33 */ = new T(function(){
  return B(_GM/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_GR/* Lib.Physics.lvl32 */));
}),
_GT/* str1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at Lib\\Physics.hs:86:7-13"));
}),
_GU/* lvl34 */ = new T6(0,_GO/* GHC.Base.Nothing */,_GP/* GHC.IO.Exception.UserError */,_o/* GHC.Types.[] */,_GT/* Lib.Physics.str1 */,_GO/* GHC.Base.Nothing */,_GO/* GHC.Base.Nothing */),
_GV/* lvl35 */ = new T(function(){
  return B(_GM/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_GU/* Lib.Physics.lvl34 */));
}),
_GW/* lvl36 */ = new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_GX/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_GY/* lvl38 */ = function(_GZ/* se9F */, _H0/* se9G */){
  var _H1/* se9L */ = new T(function(){
    var _H2/* se9K */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */(" not in range [0..", new T(function(){
        return B(_f/* GHC.Base.++ */(B(_za/* GHC.Show.$wshowSignedInt */(0, _H0/* se9G */, _o/* GHC.Types.[] */)), _GX/* Lib.Physics.lvl37 */));
      })));
    },1);
    return B(_f/* GHC.Base.++ */(B(_za/* GHC.Show.$wshowSignedInt */(0, _GZ/* se9F */, _o/* GHC.Types.[] */)), _H2/* se9K */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Error in array index; ", _H1/* se9L */)));});
},
_H3/* nextFrame1 */ = function(_H4/* se9N */, _/* EXTERNAL */){
  var _H5/* se9P */ = B(_B1/* Data.Traversable.$w$ctraverse */(_AA/* GHC.Arr.$fIxInt */, _C7/* Data.Functor.Identity.$fApplicativeIdentity */, _Fg/* Lib.Physics.a25 */, _H4/* se9N */)),
  _H6/* se9S */ = _H5/* se9P */.c,
  _H7/* se9T */ = _H5/* se9P */.d,
  _H8/* se9U */ = E(_H5/* se9P */.a),
  _H9/* se9W */ = E(_H5/* se9P */.b);
  if(_H8/* se9U */<=_H9/* se9W */){
    var _Ha/* sea1 */ = function(_Hb/* secU */, _Hc/* secV */, _/* EXTERNAL */){
      if(_Hb/* secU */<=_H9/* se9W */){
        var _Hd/* secZ */ = E(_Hc/* secV */),
        _He/* sed8 */ = function(_Hf/* sed9 */, _Hg/* seda */, _Hh/* sedb */, _Hi/* sedc */, _Hj/* sedd */, _/* EXTERNAL */){
          if(_Hg/* seda */>_Hb/* secU */){
            return new F(function(){return die/* EXTERNAL */(_GS/* Lib.Physics.lvl33 */);});
          }else{
            if(_Hb/* secU */>_Hh/* sedb */){
              return new F(function(){return die/* EXTERNAL */(_GS/* Lib.Physics.lvl33 */);});
            }else{
              if(_Hg/* seda */>_Hf/* sed9 */){
                return new F(function(){return die/* EXTERNAL */(_GV/* Lib.Physics.lvl35 */);});
              }else{
                if(_Hf/* sed9 */>_Hh/* sedb */){
                  return new F(function(){return die/* EXTERNAL */(_GV/* Lib.Physics.lvl35 */);});
                }else{
                  var _Hk/* seez */ = new T(function(){
                    var _Hl/* sedr */ = new T(function(){
                      var _Hm/* seds */ = _Hb/* secU */-_Hg/* seda */|0;
                      if(0>_Hm/* seds */){
                        return B(_GY/* Lib.Physics.lvl38 */(_Hm/* seds */, _Hi/* sedc */));
                      }else{
                        if(_Hm/* seds */>=_Hi/* sedc */){
                          return B(_GY/* Lib.Physics.lvl38 */(_Hm/* seds */, _Hi/* sedc */));
                        }else{
                          return E(_Hj/* sedd */[_Hm/* seds */]);
                        }
                      }
                    }),
                    _Hn/* sedB */ = new T(function(){
                      var _Ho/* sedC */ = _Hf/* sed9 */-_Hg/* seda */|0;
                      if(0>_Ho/* sedC */){
                        return B(_GY/* Lib.Physics.lvl38 */(_Ho/* sedC */, _Hi/* sedc */));
                      }else{
                        if(_Ho/* sedC */>=_Hi/* sedc */){
                          return B(_GY/* Lib.Physics.lvl38 */(_Ho/* sedC */, _Hi/* sedc */));
                        }else{
                          return E(_Hj/* sedd */[_Ho/* sedC */]);
                        }
                      }
                    }),
                    _Hp/* see9 */ = new T(function(){
                      return B(_DU/* Lib.Physics.$wintersect */(E(_Hn/* sedB */).i, new T(function(){
                        return E(E(_Hl/* sedr */).h);
                      })));
                    }),
                    _Hq/* sedL */ = new T(function(){
                      return B(_DU/* Lib.Physics.$wintersect */(E(_Hl/* sedr */).i, new T(function(){
                        return E(E(_Hn/* sedB */).h);
                      })));
                    });
                    return B(A3(_zz/* GHC.List.foldr1 */,_zt/* GHC.Show.$fShow(,)1 */, new T2(1,function(_Hr/* see7 */){
                      return new F(function(){return _Da/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_Hq/* sedL */, _Hr/* see7 */);});
                    },new T2(1,function(_Hs/* seev */){
                      return new F(function(){return _Da/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_Hp/* see9 */, _Hs/* seev */);});
                    },_o/* GHC.Types.[] */)), _Fz/* Lib.Physics.lvl29 */));
                  }),
                  _Ht/* seeB */ = B(_hb/* GHC.List.$wlenAcc */(new T2(1,_71/* GHC.Show.shows8 */,_Hk/* seez */), 0));
                  if(_Hf/* sed9 */!=_H9/* se9W */){
                    var _Hu/* seeF */ = B(_He/* sed8 */(_Hf/* sed9 */+1|0, _Hg/* seda */, _Hh/* sedb */, _Hi/* sedc */, _Hj/* sedd */, _/* EXTERNAL */));
                    return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
                      return E(E(_Hu/* seeF */).a);
                    })),new T(function(){
                      return E(E(_Hu/* seeF */).b);
                    }));
                  }else{
                    return new T2(0,_GW/* Lib.Physics.lvl36 */,new T4(0,E(_Hg/* seda */),E(_Hh/* sedb */),_Hi/* sedc */,_Hj/* sedd */));
                  }
                }
              }
            }
          }
        },
        _Hv/* seeW */ = B(_He/* sed8 */(_Hb/* secU */, E(_Hd/* secZ */.a), E(_Hd/* secZ */.b), _Hd/* secZ */.c, _Hd/* secZ */.d, _/* EXTERNAL */));
        if(_Hb/* secU */!=_H9/* se9W */){
          var _Hw/* sef6 */ = B(_Ha/* sea1 */(_Hb/* secU */+1|0, new T(function(){
            return E(E(_Hv/* seeW */).b);
          },1), _/* EXTERNAL */));
          return new T2(0,new T2(1,new T(function(){
            return B(_Fw/* Lib.Physics.go1 */(E(_Hv/* seeW */).a));
          }),new T(function(){
            return E(E(_Hw/* sef6 */).a);
          })),new T(function(){
            return E(E(_Hw/* sef6 */).b);
          }));
        }else{
          return new T2(0,new T2(1,new T(function(){
            return B(_Fw/* Lib.Physics.go1 */(E(_Hv/* seeW */).a));
          }),_o/* GHC.Types.[] */),new T(function(){
            return E(E(_Hv/* seeW */).b);
          }));
        }
      }else{
        if(_Hb/* secU */!=_H9/* se9W */){
          var _Hx/* sefA */ = B(_Ha/* sea1 */(_Hb/* secU */+1|0, _Hc/* secV */, _/* EXTERNAL */));
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
            return E(E(_Hx/* sefA */).a);
          })),new T(function(){
            return E(E(_Hx/* sefA */).b);
          }));
        }else{
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),_Hc/* secV */);
        }
      }
    },
    _Hy/* sea0 */ = function(_Hz/* sea2 */, _HA/* sea3 */, _HB/* sea4 */, _HC/* sea5 */, _HD/* sea6 */, _/* EXTERNAL */){
      if(_Hz/* sea2 */<=_H9/* se9W */){
        var _HE/* seaa */ = function(_HF/* seab */, _HG/* seac */, _HH/* sead */, _HI/* seae */, _HJ/* seaf */, _/* EXTERNAL */){
          if(_HG/* seac */>_Hz/* sea2 */){
            return new F(function(){return die/* EXTERNAL */(_GS/* Lib.Physics.lvl33 */);});
          }else{
            if(_Hz/* sea2 */>_HH/* sead */){
              return new F(function(){return die/* EXTERNAL */(_GS/* Lib.Physics.lvl33 */);});
            }else{
              if(_HG/* seac */>_HF/* seab */){
                return new F(function(){return die/* EXTERNAL */(_GV/* Lib.Physics.lvl35 */);});
              }else{
                if(_HF/* seab */>_HH/* sead */){
                  return new F(function(){return die/* EXTERNAL */(_GV/* Lib.Physics.lvl35 */);});
                }else{
                  var _HK/* sebB */ = new T(function(){
                    var _HL/* seat */ = new T(function(){
                      var _HM/* seau */ = _Hz/* sea2 */-_HG/* seac */|0;
                      if(0>_HM/* seau */){
                        return B(_GY/* Lib.Physics.lvl38 */(_HM/* seau */, _HI/* seae */));
                      }else{
                        if(_HM/* seau */>=_HI/* seae */){
                          return B(_GY/* Lib.Physics.lvl38 */(_HM/* seau */, _HI/* seae */));
                        }else{
                          return E(_HJ/* seaf */[_HM/* seau */]);
                        }
                      }
                    }),
                    _HN/* seaD */ = new T(function(){
                      var _HO/* seaE */ = _HF/* seab */-_HG/* seac */|0;
                      if(0>_HO/* seaE */){
                        return B(_GY/* Lib.Physics.lvl38 */(_HO/* seaE */, _HI/* seae */));
                      }else{
                        if(_HO/* seaE */>=_HI/* seae */){
                          return B(_GY/* Lib.Physics.lvl38 */(_HO/* seaE */, _HI/* seae */));
                        }else{
                          return E(_HJ/* seaf */[_HO/* seaE */]);
                        }
                      }
                    }),
                    _HP/* sebb */ = new T(function(){
                      return B(_DU/* Lib.Physics.$wintersect */(E(_HN/* seaD */).i, new T(function(){
                        return E(E(_HL/* seat */).h);
                      })));
                    }),
                    _HQ/* seaN */ = new T(function(){
                      return B(_DU/* Lib.Physics.$wintersect */(E(_HL/* seat */).i, new T(function(){
                        return E(E(_HN/* seaD */).h);
                      })));
                    });
                    return B(A3(_zz/* GHC.List.foldr1 */,_zt/* GHC.Show.$fShow(,)1 */, new T2(1,function(_HR/* seb9 */){
                      return new F(function(){return _Da/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_HQ/* seaN */, _HR/* seb9 */);});
                    },new T2(1,function(_HS/* sebx */){
                      return new F(function(){return _Da/* Lib.Physics.$s$fShow(,)_$s$fShow(,)_$cshowList */(_HP/* sebb */, _HS/* sebx */);});
                    },_o/* GHC.Types.[] */)), _Fz/* Lib.Physics.lvl29 */));
                  }),
                  _HT/* sebD */ = B(_hb/* GHC.List.$wlenAcc */(new T2(1,_71/* GHC.Show.shows8 */,_HK/* sebB */), 0));
                  if(_HF/* seab */!=_H9/* se9W */){
                    var _HU/* sebH */ = B(_HE/* seaa */(_HF/* seab */+1|0, _HG/* seac */, _HH/* sead */, _HI/* seae */, _HJ/* seaf */, _/* EXTERNAL */));
                    return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
                      return E(E(_HU/* sebH */).a);
                    })),new T(function(){
                      return E(E(_HU/* sebH */).b);
                    }));
                  }else{
                    return new T2(0,_GW/* Lib.Physics.lvl36 */,new T4(0,E(_HG/* seac */),E(_HH/* sead */),_HI/* seae */,_HJ/* seaf */));
                  }
                }
              }
            }
          }
        },
        _HV/* sebY */ = B(_HE/* seaa */(_Hz/* sea2 */, _HA/* sea3 */, _HB/* sea4 */, _HC/* sea5 */, _HD/* sea6 */, _/* EXTERNAL */));
        if(_Hz/* sea2 */!=_H9/* se9W */){
          var _HW/* sec8 */ = B(_Ha/* sea1 */(_Hz/* sea2 */+1|0, new T(function(){
            return E(E(_HV/* sebY */).b);
          },1), _/* EXTERNAL */));
          return new T2(0,new T2(1,new T(function(){
            return B(_Fw/* Lib.Physics.go1 */(E(_HV/* sebY */).a));
          }),new T(function(){
            return E(E(_HW/* sec8 */).a);
          })),new T(function(){
            return E(E(_HW/* sec8 */).b);
          }));
        }else{
          return new T2(0,new T2(1,new T(function(){
            return B(_Fw/* Lib.Physics.go1 */(E(_HV/* sebY */).a));
          }),_o/* GHC.Types.[] */),new T(function(){
            return E(E(_HV/* sebY */).b);
          }));
        }
      }else{
        if(_Hz/* sea2 */!=_H9/* se9W */){
          var _HX/* secC */ = B(_Hy/* sea0 */(_Hz/* sea2 */+1|0, _HA/* sea3 */, _HB/* sea4 */, _HC/* sea5 */, _HD/* sea6 */, _/* EXTERNAL */));
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
            return E(E(_HX/* secC */).a);
          })),new T(function(){
            return E(E(_HX/* secC */).b);
          }));
        }else{
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),new T4(0,E(_HA/* sea3 */),E(_HB/* sea4 */),_HC/* sea5 */,_HD/* sea6 */));
        }
      }
    },
    _HY/* sefP */ = B(_Hy/* sea0 */(_H8/* se9U */, _H8/* se9U */, _H9/* se9W */, _H6/* se9S */, _H7/* se9T */, _/* EXTERNAL */)),
    _HZ/* sefW */ = new T(function(){
      return B(_B1/* Data.Traversable.$w$ctraverse */(_AA/* GHC.Arr.$fIxInt */, _C7/* Data.Functor.Identity.$fApplicativeIdentity */, _Fs/* Lib.Physics.a26 */, new T(function(){
        return E(E(_HY/* sefP */).b);
      })));
    });
    return new T2(0,_Bh/* GHC.Tuple.() */,_HZ/* sefW */);
  }else{
    var _I0/* sehc */ = new T(function(){
      var _I1/* sehb */ = function(_/* EXTERNAL */){
        var _I2/* sefZ */ = function(_I3/* seg0 */){
          if(_I3/* seg0 */>=0){
            var _I4/* seg3 */ = newArr/* EXTERNAL */(_I3/* seg0 */, _hh/* GHC.Arr.arrEleBottom */),
            _I5/* seg5 */ = _I4/* seg3 */,
            _I6/* seg6 */ = E(_I3/* seg0 */);
            if(!_I6/* seg6 */){
              return new T4(0,E(_H8/* se9U */),E(_H9/* se9W */),0,_I5/* seg5 */);
            }else{
              var _I7/* seg7 */ = _H6/* se9S */-1|0,
              _I8/* segb */ = function(_I9/* segc */, _Ia/* segd */, _/* EXTERNAL */){
                while(1){
                  var _Ib/* segf */ = E(_I9/* segc */);
                  if(!_Ib/* segf */._){
                    return E(_/* EXTERNAL */);
                  }else{
                    var _/* EXTERNAL */ = _I5/* seg5 */[_Ia/* segd */] = _Ib/* segf */.a;
                    if(_Ia/* segd */!=(_I6/* seg6 */-1|0)){
                      var _Ic/*  segd */ = _Ia/* segd */+1|0;
                      _I9/* segc */ = _Ib/* segf */.b;
                      _Ia/* segd */ = _Ic/*  segd */;
                      continue;
                    }else{
                      return E(_/* EXTERNAL */);
                    }
                  }
                }
              };
              if(0<=_I7/* seg7 */){
                var _Id/* segp */ = function(_Ie/* segq */){
                  return new T2(1,new T(function(){
                    var _If/* segt */ = E(_H7/* se9T */[_Ie/* segq */]),
                    _Ig/* segD */ = B(_Dd/* Lib.Physics.$wa */(_If/* segt */.a, _If/* segt */.b, _If/* segt */.c, _If/* segt */.d, _If/* segt */.e, _If/* segt */.f));
                    return {_:0,a:_Ig/* segD */.a,b:_Ig/* segD */.b,c:_Ig/* segD */.c,d:_Ig/* segD */.d,e:_Ig/* segD */.e,f:_Ig/* segD */.f,g:_Ig/* segD */.g,h:_Ig/* segD */.h,i:_Ig/* segD */.i};
                  }),new T(function(){
                    if(_Ie/* segq */!=_I7/* seg7 */){
                      return B(_Id/* segp */(_Ie/* segq */+1|0));
                    }else{
                      return __Z/* EXTERNAL */;
                    }
                  }));
                },
                _/* EXTERNAL */ = B(_I8/* segb */(B(_Id/* segp */(0)), 0, _/* EXTERNAL */));
                return new T4(0,E(_H8/* se9U */),E(_H9/* se9W */),_I6/* seg6 */,_I5/* seg5 */);
              }else{
                return new T4(0,E(_H8/* se9U */),E(_H9/* se9W */),_I6/* seg6 */,_I5/* seg5 */);
              }
            }
          }else{
            return E(_ye/* GHC.Arr.negRange */);
          }
        };
        if(_H8/* se9U */>_H9/* se9W */){
          return new F(function(){return _I2/* sefZ */(0);});
        }else{
          return new F(function(){return _I2/* sefZ */((_H9/* se9W */-_H8/* se9U */|0)+1|0);});
        }
      };
      return B(_yu/* GHC.ST.runSTRep */(_I1/* sehb */));
    });
    return new T2(0,_Bh/* GHC.Tuple.() */,_I0/* sehc */);
  }
},
_Ih/* refresh_f1 */ = new T(function(){
  return eval/* EXTERNAL */("refresh");
}),
_Ii/* main2 */ = function(_Ij/* s5hY */, _/* EXTERNAL */){
  var _Ik/* s5i3 */ = __app0/* EXTERNAL */(E(_Ih/* Lib.Screen.refresh_f1 */)),
  _Il/* s5i9 */ = __app0/* EXTERNAL */(E(_BQ/* Lib.Screen.draw_f1 */)),
  _Im/* s5ic */ = B(A(_B1/* Data.Traversable.$w$ctraverse */,[_AA/* GHC.Arr.$fIxInt */, _yX/* GHC.Base.$fApplicativeIO */, _BO/* Lib.Object.drawObject1 */, _Ij/* s5hY */, _/* EXTERNAL */])),
  _In/* s5if */ = B(_H3/* Lib.Physics.nextFrame1 */(_Ij/* s5hY */, _/* EXTERNAL */));
  return new T(function(){
    return E(E(_In/* s5if */).b);
  });
},
_Io/* a1 */ = function(_Ip/* snHB */, _/* EXTERNAL */){
  while(1){
    var _Iq/* snHD */ = E(_Ip/* snHB */);
    if(!_Iq/* snHD */._){
      return _Bh/* GHC.Tuple.() */;
    }else{
      var _Ir/* snHF */ = _Iq/* snHD */.b,
      _Is/* snHG */ = E(_Iq/* snHD */.a);
      switch(_Is/* snHG */._){
        case 0:
          var _It/* snHI */ = B(A1(_Is/* snHG */.a,_/* EXTERNAL */));
          _Ip/* snHB */ = B(_f/* GHC.Base.++ */(_Ir/* snHF */, new T2(1,_It/* snHI */,_o/* GHC.Types.[] */)));
          continue;
        case 1:
          _Ip/* snHB */ = B(_f/* GHC.Base.++ */(_Ir/* snHF */, _Is/* snHG */.a));
          continue;
        default:
          _Ip/* snHB */ = _Ir/* snHF */;
          continue;
      }
    }
  }
},
_Iu/* $fMonadEventCIO_$sa */ = function(_Iv/* snHp */, _Iw/* snHq */, _/* EXTERNAL */){
  var _Ix/* snHs */ = E(_Iv/* snHp */);
  switch(_Ix/* snHs */._){
    case 0:
      var _Iy/* snHu */ = B(A1(_Ix/* snHs */.a,_/* EXTERNAL */));
      return new F(function(){return _Io/* Haste.Concurrent.Monad.a1 */(B(_f/* GHC.Base.++ */(_Iw/* snHq */, new T2(1,_Iy/* snHu */,_o/* GHC.Types.[] */))), _/* EXTERNAL */);});
      break;
    case 1:
      return new F(function(){return _Io/* Haste.Concurrent.Monad.a1 */(B(_f/* GHC.Base.++ */(_Iw/* snHq */, _Ix/* snHs */.a)), _/* EXTERNAL */);});
      break;
    default:
      return new F(function(){return _Io/* Haste.Concurrent.Monad.a1 */(_Iw/* snHq */, _/* EXTERNAL */);});
  }
},
_Iz/* $c>>=1 */ = function(_IA/* snHc */, _IB/* snHd */, _IC/* snHe */){
  return new F(function(){return A1(_IA/* snHc */,function(_ID/* snHf */){
    return new F(function(){return A2(_IB/* snHd */,_ID/* snHf */, _IC/* snHe */);});
  });});
},
_IE/* $fApplicativeCIO1 */ = function(_IF/* snLu */, _IG/* snLv */, _IH/* snLw */){
  var _II/* snLB */ = function(_IJ/* snLx */){
    var _IK/* snLy */ = new T(function(){
      return B(A1(_IH/* snLw */,_IJ/* snLx */));
    });
    return new F(function(){return A1(_IG/* snLv */,function(_IL/* snLz */){
      return E(_IK/* snLy */);
    });});
  };
  return new F(function(){return A1(_IF/* snLu */,_II/* snLB */);});
},
_IM/* $fApplicativeCIO2 */ = function(_IN/* snLm */, _IO/* snLn */, _IP/* snLo */){
  var _IQ/* snLp */ = new T(function(){
    return B(A1(_IO/* snLn */,function(_IR/* snLq */){
      return new F(function(){return A1(_IP/* snLo */,_IR/* snLq */);});
    }));
  });
  return new F(function(){return A1(_IN/* snLm */,function(_IS/* snLs */){
    return E(_IQ/* snLp */);
  });});
},
_IT/* $fApplicativeCIO3 */ = function(_IU/* snHP */, _IV/* snHQ */, _IW/* snHR */){
  var _IX/* snHW */ = function(_IY/* snHS */){
    var _IZ/* snHV */ = function(_J0/* snHT */){
      return new F(function(){return A1(_IW/* snHR */,new T(function(){
        return B(A1(_IY/* snHS */,_J0/* snHT */));
      }));});
    };
    return new F(function(){return A1(_IV/* snHQ */,_IZ/* snHV */);});
  };
  return new F(function(){return A1(_IU/* snHP */,_IX/* snHW */);});
},
_J1/* $fApplicativeCIO4 */ = function(_J2/* snHh */, _J3/* snHi */){
  return new F(function(){return A1(_J3/* snHi */,_J2/* snHh */);});
},
_J4/* $fFunctorCIO1 */ = function(_J5/* snLg */, _J6/* snLh */, _J7/* snLi */){
  var _J8/* snLj */ = new T(function(){
    return B(A1(_J7/* snLi */,_J5/* snLg */));
  });
  return new F(function(){return A1(_J6/* snLh */,function(_J9/* snLk */){
    return E(_J8/* snLj */);
  });});
},
_Ja/* $fFunctorCIO2 */ = function(_Jb/* snH6 */, _Jc/* snH7 */, _Jd/* snH8 */){
  var _Je/* snHb */ = function(_Jf/* snH9 */){
    return new F(function(){return A1(_Jd/* snH8 */,new T(function(){
      return B(A1(_Jb/* snH6 */,_Jf/* snH9 */));
    }));});
  };
  return new F(function(){return A1(_Jc/* snH7 */,_Je/* snHb */);});
},
_Jg/* $fFunctorCIO */ = new T2(0,_Ja/* Haste.Concurrent.Monad.$fFunctorCIO2 */,_J4/* Haste.Concurrent.Monad.$fFunctorCIO1 */),
_Jh/* $fApplicativeCIO */ = new T5(0,_Jg/* Haste.Concurrent.Monad.$fFunctorCIO */,_J1/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_IT/* Haste.Concurrent.Monad.$fApplicativeCIO3 */,_IM/* Haste.Concurrent.Monad.$fApplicativeCIO2 */,_IE/* Haste.Concurrent.Monad.$fApplicativeCIO1 */),
_Ji/* >>= */ = function(_Jj/* s34T */){
  return E(E(_Jj/* s34T */).b);
},
_Jk/* $fMonadCIO_$c>> */ = function(_Jl/* snLD */, _Jm/* snLE */){
  return new F(function(){return A3(_Ji/* GHC.Base.>>= */,_Jn/* Haste.Concurrent.Monad.$fMonadCIO */, _Jl/* snLD */, function(_Jo/* snLF */){
    return E(_Jm/* snLE */);
  });});
},
_Jp/* a5 */ = function(_Jq/* snLC */){
  return new F(function(){return err/* EXTERNAL */(_Jq/* snLC */);});
},
_Jn/* $fMonadCIO */ = new T(function(){
  return new T5(0,_Jh/* Haste.Concurrent.Monad.$fApplicativeCIO */,_Iz/* Haste.Concurrent.Monad.$c>>=1 */,_Jk/* Haste.Concurrent.Monad.$fMonadCIO_$c>> */,_J1/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_Jp/* Haste.Concurrent.Monad.a5 */);
}),
_Jr/* $fMonadIOCIO1 */ = function(_Js/* snH3 */, _Jt/* snH4 */){
  return new T1(0,function(_/* EXTERNAL */){
    return new F(function(){return _yM/* GHC.Base.$fFunctorIO2 */(_Jt/* snH4 */, _Js/* snH3 */, _/* EXTERNAL */);});
  });
},
_Ju/* $fMonadIOCIO */ = new T2(0,_Jn/* Haste.Concurrent.Monad.$fMonadCIO */,_Jr/* Haste.Concurrent.Monad.$fMonadIOCIO1 */),
_Jv/* forkIO1 */ = function(_Jw/* snHj */){
  return new T0(2);
},
_Jx/* forkIO */ = function(_Jy/* snKc */){
  var _Jz/* snKd */ = new T(function(){
    return B(A1(_Jy/* snKc */,_Jv/* Haste.Concurrent.Monad.forkIO1 */));
  }),
  _JA/* snKi */ = function(_JB/* snKf */){
    return new T1(1,new T2(1,new T(function(){
      return B(A1(_JB/* snKf */,_Bh/* GHC.Tuple.() */));
    }),new T2(1,_Jz/* snKd */,_o/* GHC.Types.[] */)));
  };
  return E(_JA/* snKi */);
},
_JC/* $fMonadConcCIO */ = new T3(0,_Ju/* Haste.Concurrent.Monad.$fMonadIOCIO */,_7S/* GHC.Base.id */,_Jx/* Haste.Concurrent.Monad.forkIO */),
_JD/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_JE/* unsafeDupablePerformIO */ = function(_JF/* s2YSa */){
  var _JG/* s2YSb */ = B(A1(_JF/* s2YSa */,_/* EXTERNAL */));
  return E(_JG/* s2YSb */);
},
_JH/* nullValue */ = new T(function(){
  return B(_JE/* GHC.IO.unsafeDupablePerformIO */(_JD/* Haste.Prim.Any.lvl2 */));
}),
_JI/* jsNull */ = new T(function(){
  return E(_JH/* Haste.Prim.Any.nullValue */);
}),
_JJ/* Stop */ = new T0(2),
_JK/* liftCIO */ = function(_JL/* snGT */){
  return E(E(_JL/* snGT */).b);
},
_JM/* putMVar */ = function(_JN/* snKj */, _JO/* snKk */, _JP/* snKl */){
  var _JQ/* snKT */ = function(_JR/* snKn */){
    var _JS/* snKS */ = function(_/* EXTERNAL */){
      var _JT/* snKp */ = E(_JO/* snKk */),
      _JU/* snKr */ = rMV/* EXTERNAL */(_JT/* snKp */),
      _JV/* snKu */ = E(_JU/* snKr */);
      if(!_JV/* snKu */._){
        var _JW/* snKC */ = new T(function(){
          var _JX/* snKx */ = new T(function(){
            return B(A1(_JR/* snKn */,_Bh/* GHC.Tuple.() */));
          });
          return B(_f/* GHC.Base.++ */(_JV/* snKu */.b, new T2(1,new T2(0,_JP/* snKl */,function(_JY/* snKy */){
            return E(_JX/* snKx */);
          }),_o/* GHC.Types.[] */)));
        }),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_JT/* snKp */, new T2(0,_JV/* snKu */.a,_JW/* snKC */));
        return _JJ/* Haste.Concurrent.Monad.Stop */;
      }else{
        var _JZ/* snKG */ = E(_JV/* snKu */.a);
        if(!_JZ/* snKG */._){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_JT/* snKp */, new T2(0,_JP/* snKl */,_o/* GHC.Types.[] */));
          return new T(function(){
            return B(A1(_JR/* snKn */,_Bh/* GHC.Tuple.() */));
          });
        }else{
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_JT/* snKp */, new T1(1,_JZ/* snKG */.b));
          return new T1(1,new T2(1,new T(function(){
            return B(A1(_JR/* snKn */,_Bh/* GHC.Tuple.() */));
          }),new T2(1,new T(function(){
            return B(A2(_JZ/* snKG */.a,_JP/* snKl */, _Jv/* Haste.Concurrent.Monad.forkIO1 */));
          }),_o/* GHC.Types.[] */)));
        }
      }
    };
    return new T1(0,_JS/* snKS */);
  };
  return new F(function(){return A2(_JK/* Haste.Concurrent.Monad.liftCIO */,_JN/* snKj */, _JQ/* snKT */);});
},
_K0/* requestAnimationFrame_f1 */ = new T(function(){
  return eval/* EXTERNAL */("window.requestAnimationFrame");
}),
_K1/* takeMVar1 */ = new T1(1,_o/* GHC.Types.[] */),
_K2/* takeMVar */ = function(_K3/* snJ3 */, _K4/* snJ4 */){
  var _K5/* snJF */ = function(_K6/* snJ5 */){
    var _K7/* snJE */ = function(_/* EXTERNAL */){
      var _K8/* snJ7 */ = E(_K4/* snJ4 */),
      _K9/* snJ9 */ = rMV/* EXTERNAL */(_K8/* snJ7 */),
      _Ka/* snJc */ = E(_K9/* snJ9 */);
      if(!_Ka/* snJc */._){
        var _Kb/* snJd */ = _Ka/* snJc */.a,
        _Kc/* snJf */ = E(_Ka/* snJc */.b);
        if(!_Kc/* snJf */._){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_K8/* snJ7 */, _K1/* Haste.Concurrent.Monad.takeMVar1 */);
          return new T(function(){
            return B(A1(_K6/* snJ5 */,_Kb/* snJd */));
          });
        }else{
          var _Kd/* snJk */ = E(_Kc/* snJf */.a),
          _/* EXTERNAL */ = wMV/* EXTERNAL */(_K8/* snJ7 */, new T2(0,_Kd/* snJk */.a,_Kc/* snJf */.b));
          return new T1(1,new T2(1,new T(function(){
            return B(A1(_K6/* snJ5 */,_Kb/* snJd */));
          }),new T2(1,new T(function(){
            return B(A1(_Kd/* snJk */.b,_Jv/* Haste.Concurrent.Monad.forkIO1 */));
          }),_o/* GHC.Types.[] */)));
        }
      }else{
        var _Ke/* snJB */ = new T(function(){
          var _Kf/* snJz */ = function(_Kg/* snJv */){
            var _Kh/* snJw */ = new T(function(){
              return B(A1(_K6/* snJ5 */,_Kg/* snJv */));
            });
            return function(_Ki/* snJx */){
              return E(_Kh/* snJw */);
            };
          };
          return B(_f/* GHC.Base.++ */(_Ka/* snJc */.a, new T2(1,_Kf/* snJz */,_o/* GHC.Types.[] */)));
        }),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_K8/* snJ7 */, new T1(1,_Ke/* snJB */));
        return _JJ/* Haste.Concurrent.Monad.Stop */;
      }
    };
    return new T1(0,_K7/* snJE */);
  };
  return new F(function(){return A2(_JK/* Haste.Concurrent.Monad.liftCIO */,_K3/* snJ3 */, _K5/* snJF */);});
},
_Kj/* $wa */ = function(_Kk/* s3tn */, _Kl/* s3to */){
  var _Km/* s3tp */ = new T(function(){
    return B(A(_JM/* Haste.Concurrent.Monad.putMVar */,[_JC/* Haste.Concurrent.Monad.$fMonadConcCIO */, _Kk/* s3tn */, _Bh/* GHC.Tuple.() */, _Jv/* Haste.Concurrent.Monad.forkIO1 */]));
  });
  return function(_/* EXTERNAL */){
    var _Kn/* s3tA */ = __createJSFunc/* EXTERNAL */(2, function(_Ko/* s3tr */, _/* EXTERNAL */){
      var _Kp/* s3tt */ = B(_Iu/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_Km/* s3tp */, _o/* GHC.Types.[] */, _/* EXTERNAL */));
      return _JI/* Haste.Prim.Any.jsNull */;
    }),
    _Kq/* s3tG */ = __app1/* EXTERNAL */(E(_K0/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _Kn/* s3tA */);
    return new T(function(){
      return B(A3(_K2/* Haste.Concurrent.Monad.takeMVar */,_JC/* Haste.Concurrent.Monad.$fMonadConcCIO */, _Kk/* s3tn */, _Kl/* s3to */));
    });
  };
},
_Kr/* run2 */ = new T1(1,_o/* GHC.Types.[] */),
_Ks/* run1 */ = function(_Kt/* s3tZ */, _Ku/* s3u0 */, _/* EXTERNAL */){
  var _Kv/* s3uw */ = function(_/* EXTERNAL */){
    var _Kw/* s3u3 */ = nMV/* EXTERNAL */(_Kt/* s3tZ */),
    _Kx/* s3u5 */ = _Kw/* s3u3 */;
    return new T(function(){
      var _Ky/* s3u6 */ = new T(function(){
        return B(_Kz/* s3u9 */(_/* EXTERNAL */));
      }),
      _KA/* s3u7 */ = function(_/* EXTERNAL */){
        var _KB/* s3ub */ = rMV/* EXTERNAL */(_Kx/* s3u5 */),
        _KC/* s3ue */ = B(A2(_Ku/* s3u0 */,_KB/* s3ub */, _/* EXTERNAL */)),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_Kx/* s3u5 */, _KC/* s3ue */),
        _KD/* s3us */ = function(_/* EXTERNAL */){
          var _KE/* s3uj */ = nMV/* EXTERNAL */(_Kr/* Lib.Screen.run2 */);
          return new T(function(){
            return new T1(0,B(_Kj/* Lib.Screen.$wa */(_KE/* s3uj */, function(_KF/* s3un */){
              return E(_Ky/* s3u6 */);
            })));
          });
        };
        return new T1(0,_KD/* s3us */);
      },
      _KG/* s3u8 */ = new T(function(){
        return new T1(0,_KA/* s3u7 */);
      }),
      _Kz/* s3u9 */ = function(_KH/* s3uu */){
        return E(_KG/* s3u8 */);
      };
      return B(_Kz/* s3u9 */(_/* EXTERNAL */));
    });
  };
  return new F(function(){return _Iu/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T1(0,_Kv/* s3uw */), _o/* GHC.Types.[] */, _/* EXTERNAL */);});
},
_KI/* main1 */ = function(_/* EXTERNAL */){
  var _KJ/* s5iu */ = __app2/* EXTERNAL */(E(_0/* Lib.Screen.compile_f1 */), E(_7U/* Lib.Shader.fieldStr */), E(_ha/* Lib.Shader.gradStr */));
  return new F(function(){return _Ks/* Lib.Screen.run1 */(_yx/* Main.initial2 */, _Ii/* Main.main2 */, _/* EXTERNAL */);});
},
_KK/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _KI/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_KK, [0]));};window.onload = hasteMain;