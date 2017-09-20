"use strict";
var __haste_prog_id = '2ab2bc903793510fd9a87da42bedbee915991d6654a00b25bcb20ee2525e6403';
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
_5/* $fFoldableVar_$cfoldMap */ = function(_6/* sgTq */, _7/* sgTr */, _8/* sgTs */){
  var _9/* sgTt */ = E(_8/* sgTs */);
  if(!_9/* sgTt */._){
    return new F(function(){return A1(_7/* sgTr */,_9/* sgTt */.a);});
  }else{
    var _a/* sgTw */ = new T(function(){
      return B(_1/* GHC.Base.mappend */(_6/* sgTq */));
    }),
    _b/* sgTx */ = new T(function(){
      return B(_3/* GHC.Base.mempty */(_6/* sgTq */));
    }),
    _c/* sgTy */ = function(_d/* sgTz */){
      var _e/* sgTA */ = E(_d/* sgTz */);
      if(!_e/* sgTA */._){
        return E(_b/* sgTx */);
      }else{
        return new F(function(){return A2(_a/* sgTw */,new T(function(){
          return B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_6/* sgTq */, _7/* sgTr */, _e/* sgTA */.a));
        }), new T(function(){
          return B(_c/* sgTy */(_e/* sgTA */.b));
        }));});
      }
    };
    return new F(function(){return _c/* sgTy */(_9/* sgTt */.a);});
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
_x/* $fFloatingVar_$c** */ = function(_y/* sgSB */, _z/* sgSC */){
  return new T1(1,new T2(1,_t/* Lib.Shader.$fFloatingVar31 */,new T2(1,_y/* sgSB */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_z/* sgSC */,_w/* Lib.Shader.gradStr3 */)))));
},
_A/* $fFloatingVar16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("acos("));
}),
_B/* $fFloatingVar15 */ = new T1(0,_A/* Lib.Shader.$fFloatingVar16 */),
_C/* $fFloatingVar_$cacos */ = function(_D/* sgSg */){
  return new T1(1,new T2(1,_B/* Lib.Shader.$fFloatingVar15 */,new T2(1,_D/* sgSg */,_w/* Lib.Shader.gradStr3 */)));
},
_E/* $fFloatingVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("acosh("));
}),
_F/* $fFloatingVar3 */ = new T1(0,_E/* Lib.Shader.$fFloatingVar4 */),
_G/* $fFloatingVar_$cacosh */ = function(_H/* sgRY */){
  return new T1(1,new T2(1,_F/* Lib.Shader.$fFloatingVar3 */,new T2(1,_H/* sgRY */,_w/* Lib.Shader.gradStr3 */)));
},
_I/* $fFloatingVar18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("asin("));
}),
_J/* $fFloatingVar17 */ = new T1(0,_I/* Lib.Shader.$fFloatingVar18 */),
_K/* $fFloatingVar_$casin */ = function(_L/* sgSj */){
  return new T1(1,new T2(1,_J/* Lib.Shader.$fFloatingVar17 */,new T2(1,_L/* sgSj */,_w/* Lib.Shader.gradStr3 */)));
},
_M/* $fFloatingVar6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("asinh("));
}),
_N/* $fFloatingVar5 */ = new T1(0,_M/* Lib.Shader.$fFloatingVar6 */),
_O/* $fFloatingVar_$casinh */ = function(_P/* sgS1 */){
  return new T1(1,new T2(1,_N/* Lib.Shader.$fFloatingVar5 */,new T2(1,_P/* sgS1 */,_w/* Lib.Shader.gradStr3 */)));
},
_Q/* $fFloatingVar14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("atan("));
}),
_R/* $fFloatingVar13 */ = new T1(0,_Q/* Lib.Shader.$fFloatingVar14 */),
_S/* $fFloatingVar_$catan */ = function(_T/* sgSd */){
  return new T1(1,new T2(1,_R/* Lib.Shader.$fFloatingVar13 */,new T2(1,_T/* sgSd */,_w/* Lib.Shader.gradStr3 */)));
},
_U/* $fFloatingVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("atanh("));
}),
_V/* $fFloatingVar1 */ = new T1(0,_U/* Lib.Shader.$fFloatingVar2 */),
_W/* $fFloatingVar_$catanh */ = function(_X/* sgRV */){
  return new T1(1,new T2(1,_V/* Lib.Shader.$fFloatingVar1 */,new T2(1,_X/* sgRV */,_w/* Lib.Shader.gradStr3 */)));
},
_Y/* $fFloatingVar22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("cos("));
}),
_Z/* $fFloatingVar21 */ = new T1(0,_Y/* Lib.Shader.$fFloatingVar22 */),
_10/* $fFloatingVar_$ccos */ = function(_11/* sgSp */){
  return new T1(1,new T2(1,_Z/* Lib.Shader.$fFloatingVar21 */,new T2(1,_11/* sgSp */,_w/* Lib.Shader.gradStr3 */)));
},
_12/* $fFloatingVar10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("cosh("));
}),
_13/* $fFloatingVar9 */ = new T1(0,_12/* Lib.Shader.$fFloatingVar10 */),
_14/* $fFloatingVar_$ccosh */ = function(_15/* sgS7 */){
  return new T1(1,new T2(1,_13/* Lib.Shader.$fFloatingVar9 */,new T2(1,_15/* sgS7 */,_w/* Lib.Shader.gradStr3 */)));
},
_16/* $fFloatingVar36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("exp("));
}),
_17/* $fFloatingVar35 */ = new T1(0,_16/* Lib.Shader.$fFloatingVar36 */),
_18/* $fFloatingVar_$cexp */ = function(_19/* sgSN */){
  return new T1(1,new T2(1,_17/* Lib.Shader.$fFloatingVar35 */,new T2(1,_19/* sgSN */,_w/* Lib.Shader.gradStr3 */)));
},
_1a/* $fFloatingVar28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("log("));
}),
_1b/* $fFloatingVar27 */ = new T1(0,_1a/* Lib.Shader.$fFloatingVar28 */),
_1c/* $fFloatingVar_$clog */ = function(_1d/* sgSK */){
  return new T1(1,new T2(1,_1b/* Lib.Shader.$fFloatingVar27 */,new T2(1,_1d/* sgSK */,_w/* Lib.Shader.gradStr3 */)));
},
_1e/* $fFloatingVar26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")/log("));
}),
_1f/* $fFloatingVar25 */ = new T1(0,_1e/* Lib.Shader.$fFloatingVar26 */),
_1g/* $fFloatingVar_$clogBase */ = function(_1h/* sgSv */, _1i/* sgSw */){
  return new T1(1,new T2(1,_1b/* Lib.Shader.$fFloatingVar27 */,new T2(1,_1i/* sgSw */,new T2(1,_1f/* Lib.Shader.$fFloatingVar25 */,new T2(1,_1h/* sgSv */,_w/* Lib.Shader.gradStr3 */)))));
},
_1j/* $fFloatingVar37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pi"));
}),
_1k/* $fFloatingVar_$cpi */ = new T1(0,_1j/* Lib.Shader.$fFloatingVar37 */),
_1l/* $fFloatingVar24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sin("));
}),
_1m/* $fFloatingVar23 */ = new T1(0,_1l/* Lib.Shader.$fFloatingVar24 */),
_1n/* $fFloatingVar_$csin */ = function(_1o/* sgSs */){
  return new T1(1,new T2(1,_1m/* Lib.Shader.$fFloatingVar23 */,new T2(1,_1o/* sgSs */,_w/* Lib.Shader.gradStr3 */)));
},
_1p/* $fFloatingVar12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sinh("));
}),
_1q/* $fFloatingVar11 */ = new T1(0,_1p/* Lib.Shader.$fFloatingVar12 */),
_1r/* $fFloatingVar_$csinh */ = function(_1s/* sgSa */){
  return new T1(1,new T2(1,_1q/* Lib.Shader.$fFloatingVar11 */,new T2(1,_1s/* sgSa */,_w/* Lib.Shader.gradStr3 */)));
},
_1t/* $fFloatingVar34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sqrt("));
}),
_1u/* $fFloatingVar33 */ = new T1(0,_1t/* Lib.Shader.$fFloatingVar34 */),
_1v/* $fFloatingVar_$csqrt */ = function(_1w/* sgSH */){
  return new T1(1,new T2(1,_1u/* Lib.Shader.$fFloatingVar33 */,new T2(1,_1w/* sgSH */,_w/* Lib.Shader.gradStr3 */)));
},
_1x/* $fFloatingVar20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tan("));
}),
_1y/* $fFloatingVar19 */ = new T1(0,_1x/* Lib.Shader.$fFloatingVar20 */),
_1z/* $fFloatingVar_$ctan */ = function(_1A/* sgSm */){
  return new T1(1,new T2(1,_1y/* Lib.Shader.$fFloatingVar19 */,new T2(1,_1A/* sgSm */,_w/* Lib.Shader.gradStr3 */)));
},
_1B/* $fFloatingVar8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tanh("));
}),
_1C/* $fFloatingVar7 */ = new T1(0,_1B/* Lib.Shader.$fFloatingVar8 */),
_1D/* $fFloatingVar_$ctanh */ = function(_1E/* sgS4 */){
  return new T1(1,new T2(1,_1C/* Lib.Shader.$fFloatingVar7 */,new T2(1,_1E/* sgS4 */,_w/* Lib.Shader.gradStr3 */)));
},
_1F/* $c+6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_1G/* $c+5 */ = new T1(0,_1F/* Lib.Shader.$c+6 */),
_1H/* $fFractionalVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")/("));
}),
_1I/* $fFractionalVar3 */ = new T1(0,_1H/* Lib.Shader.$fFractionalVar4 */),
_1J/* $fFractionalVar_$c/ */ = function(_1K/* sgRP */, _1L/* sgRQ */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_1K/* sgRP */,new T2(1,_1I/* Lib.Shader.$fFractionalVar3 */,new T2(1,_1L/* sgRQ */,_w/* Lib.Shader.gradStr3 */)))));
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
_6m/* $fFractionalVar_$cfromRational */ = function(_6n/* sgRA */){
  return new T1(0,new T(function(){
    var _6o/* sgRB */ = E(_6n/* sgRA */),
    _6p/* sgRH */ = jsShow/* EXTERNAL */(B(_6j/* GHC.Float.rationalToDouble */(_6o/* sgRB */.a, _6o/* sgRB */.b)));
    return fromJSStr/* EXTERNAL */(_6p/* sgRH */);
  }));
},
_6q/* $fFractionalVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1./("));
}),
_6r/* $fFractionalVar1 */ = new T1(0,_6q/* Lib.Shader.$fFractionalVar2 */),
_6s/* $fFractionalVar_$crecip */ = function(_6t/* sgRM */){
  return new T1(1,new T2(1,_6r/* Lib.Shader.$fFractionalVar1 */,new T2(1,_6t/* sgRM */,_w/* Lib.Shader.gradStr3 */)));
},
_6u/* $c+4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")+("));
}),
_6v/* $c+3 */ = new T1(0,_6u/* Lib.Shader.$c+4 */),
_6w/* $c+ */ = function(_6x/* sgRr */, _6y/* sgRs */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_6x/* sgRr */,new T2(1,_6v/* Lib.Shader.$c+3 */,new T2(1,_6y/* sgRs */,_w/* Lib.Shader.gradStr3 */)))));
},
_6z/* $cnegate2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("-("));
}),
_6A/* $cnegate1 */ = new T1(0,_6z/* Lib.Shader.$cnegate2 */),
_6B/* $cnegate */ = function(_6C/* sgRi */){
  return new T1(1,new T2(1,_6A/* Lib.Shader.$cnegate1 */,new T2(1,_6C/* sgRi */,_w/* Lib.Shader.gradStr3 */)));
},
_6D/* $fNumVar6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")*("));
}),
_6E/* $fNumVar5 */ = new T1(0,_6D/* Lib.Shader.$fNumVar6 */),
_6F/* $fNumVar_$c* */ = function(_6G/* sgRl */, _6H/* sgRm */){
  return new T1(1,new T2(1,_1G/* Lib.Shader.$c+5 */,new T2(1,_6G/* sgRl */,new T2(1,_6E/* Lib.Shader.$fNumVar5 */,new T2(1,_6H/* sgRm */,_w/* Lib.Shader.gradStr3 */)))));
},
_6I/* + */ = function(_6J/* s6Fw */){
  return E(E(_6J/* s6Fw */).a);
},
_6K/* negate */ = function(_6L/* s6FX */){
  return E(E(_6L/* s6FX */).d);
},
_6M/* $fNumVar_$c- */ = function(_6N/* sgRx */, _6O/* sgRy */){
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_6P/* Lib.Shader.$fNumVar */, _6N/* sgRx */, new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_6P/* Lib.Shader.$fNumVar */, _6O/* sgRy */));
  }));});
},
_6Q/* $fNumVar4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("abs("));
}),
_6R/* $fNumVar3 */ = new T1(0,_6Q/* Lib.Shader.$fNumVar4 */),
_6S/* $fNumVar_$cabs */ = function(_6T/* sgRf */){
  return new T1(1,new T2(1,_6R/* Lib.Shader.$fNumVar3 */,new T2(1,_6T/* sgRf */,_w/* Lib.Shader.gradStr3 */)));
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
_78/* $fNumVar_$cfromInteger */ = function(_79/* sgR9 */){
  return new T1(0,new T(function(){
    return B(_f/* GHC.Base.++ */(B(_73/* GHC.Show.$w$cshowsPrec1 */(0, _79/* sgR9 */, _o/* GHC.Types.[] */)), _77/* Lib.Shader.lvl4 */));
  }));
},
_7a/* $fNumVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sign("));
}),
_7b/* $fNumVar1 */ = new T1(0,_7a/* Lib.Shader.$fNumVar2 */),
_7c/* $fNumVar_$csignum */ = function(_7d/* sgRc */){
  return new T1(1,new T2(1,_7b/* Lib.Shader.$fNumVar1 */,new T2(1,_7d/* sgRc */,_w/* Lib.Shader.gradStr3 */)));
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
_7y/* $wfield */ = function(_7z/* seqq */, _7A/* seqr */, _7B/* seqs */, _7C/* seqt */){
  var _7D/* sequ */ = B(_7g/* GHC.Float.$p1Floating */(_7z/* seqq */)),
  _7E/* seqv */ = B(_7i/* GHC.Real.$p1Fractional */(_7D/* sequ */)),
  _7F/* seqF */ = new T(function(){
    var _7G/* seqE */ = new T(function(){
      var _7H/* seqC */ = new T(function(){
        var _7I/* seqw */ = new T(function(){
          var _7J/* seqA */ = new T(function(){
            var _7K/* seqz */ = new T(function(){
              return B(A3(_6I/* GHC.Num.+ */,_7E/* seqv */, new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_7E/* seqv */, _7A/* seqr */, _7A/* seqr */));
              }), new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_7E/* seqv */, _7C/* seqt */, _7C/* seqt */));
              })));
            });
            return B(A2(_7w/* GHC.Float.sqrt */,_7z/* seqq */, _7K/* seqz */));
          });
          return B(A3(_7m/* GHC.Num.- */,_7E/* seqv */, _7J/* seqA */, new T(function(){
            return B(A2(_7o/* GHC.Real.fromRational */,_7D/* sequ */, _7v/* Lib.World.gradient3 */));
          })));
        });
        return B(A3(_7k/* GHC.Num.* */,_7E/* seqv */, _7I/* seqw */, _7I/* seqw */));
      });
      return B(A3(_6I/* GHC.Num.+ */,_7E/* seqv */, _7H/* seqC */, new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_7E/* seqv */, _7B/* seqs */, _7B/* seqs */));
      })));
    });
    return B(A2(_7w/* GHC.Float.sqrt */,_7z/* seqq */, _7G/* seqE */));
  });
  return new F(function(){return A3(_7m/* GHC.Num.- */,_7E/* seqv */, _7F/* seqF */, new T(function(){
    return B(A2(_7o/* GHC.Real.fromRational */,_7D/* sequ */, _7s/* Lib.World.gradient1 */));
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
_7V/* $fFoldableVar_$s$cfoldMap */ = function(_7W/* sgTe */, _7X/* sgTf */, _7Y/* sgTg */){
  var _7Z/* sgTh */ = new T(function(){
    return B(_1/* GHC.Base.mappend */(_7W/* sgTe */));
  }),
  _80/* sgTi */ = new T(function(){
    return B(_3/* GHC.Base.mempty */(_7W/* sgTe */));
  }),
  _81/* sgTj */ = function(_82/* sgTk */){
    var _83/* sgTl */ = E(_82/* sgTk */);
    if(!_83/* sgTl */._){
      return E(_80/* sgTi */);
    }else{
      return new F(function(){return A2(_7Z/* sgTh */,new T(function(){
        return B(_5/* Lib.Shader.$fFoldableVar_$cfoldMap */(_7W/* sgTe */, _7X/* sgTf */, _83/* sgTl */.a));
      }), new T(function(){
        return B(_81/* sgTj */(_83/* sgTl */.b));
      }));});
    }
  };
  return new F(function(){return _81/* sgTj */(_7Y/* sgTg */);});
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
_8m/* $fOrdVar_$cmax */ = function(_8n/* sgSW */, _8o/* sgSX */){
  return new T1(1,new T2(1,_8l/* Lib.Shader.$fOrdVar3 */,new T2(1,_8n/* sgSW */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_8o/* sgSX */,_w/* Lib.Shader.gradStr3 */)))));
},
_8p/* $fOrdVar2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("min("));
}),
_8q/* $fOrdVar1 */ = new T1(0,_8p/* Lib.Shader.$fOrdVar2 */),
_8r/* $fOrdVar_$cmin */ = function(_8s/* sgSQ */, _8t/* sgSR */){
  return new T1(1,new T2(1,_8q/* Lib.Shader.$fOrdVar1 */,new T2(1,_8s/* sgSQ */,new T2(1,_r/* Lib.Shader.$fFloatingVar29 */,new T2(1,_8t/* sgSR */,_w/* Lib.Shader.gradStr3 */)))));
},
_8u/* $fOrdVar */ = {_:0,a:_89/* Lib.Shader.$fEqVar */,b:_8j/* Lib.Shader.$fOrdVar_$ccompare */,c:_8b/* Lib.Shader.$fOrdVar_$c< */,d:_8d/* Lib.Shader.$fOrdVar_$c<= */,e:_8f/* Lib.Shader.$fOrdVar_$c> */,f:_8h/* Lib.Shader.$fOrdVar_$c>= */,g:_8m/* Lib.Shader.$fOrdVar_$cmax */,h:_8r/* Lib.Shader.$fOrdVar_$cmin */},
_8v/* gradStr7 */ = new T2(0,_7f/* Lib.Shader.$fFloatingVar */,_8u/* Lib.Shader.$fOrdVar */),
_8w/* $fApplicativeWorld_$c*> */ = function(_8x/* seyv */, _8y/* seyw */){
  var _8z/* seyx */ = E(_8x/* seyv */);
  return E(_8y/* seyw */);
},
_8A/* $fApplicativeWorld_$c<* */ = function(_8B/* ser3 */, _8C/* ser4 */){
  var _8D/* ser9 */ = E(_8C/* ser4 */);
  return E(_8B/* ser3 */);
},
_8E/* $fApplicativeWorld_$c<*> */ = function(_8F/* seqQ */, _8G/* seqR */){
  var _8H/* seqS */ = E(_8F/* seqQ */),
  _8I/* seqW */ = E(_8G/* seqR */);
  return new T3(0,E(B(A1(_8H/* seqS */.a,_8I/* seqW */.a))),E(B(A1(_8H/* seqS */.b,_8I/* seqW */.b))),E(B(A1(_8H/* seqS */.c,_8I/* seqW */.c))));
},
_8J/* $WWorld */ = function(_8K/* sepB */, _8L/* sepC */, _8M/* sepD */){
  return new T3(0,E(_8K/* sepB */),E(_8L/* sepC */),E(_8M/* sepD */));
},
_8N/* $fApplicativeWorld_$cpure */ = function(_8O/* serd */){
  return new F(function(){return _8J/* Lib.World.$WWorld */(_8O/* serd */, _8O/* serd */, _8O/* serd */);});
},
_8P/* $fFunctorWorld_$c<$ */ = function(_8Q/* seyo */, _8R/* seyp */){
  var _8S/* seyq */ = E(_8R/* seyp */),
  _8T/* seyu */ = E(_8Q/* seyo */);
  return new T3(0,E(_8T/* seyu */),E(_8T/* seyu */),E(_8T/* seyu */));
},
_8U/* $fFunctorWorld_$cfmap */ = function(_8V/* seyB */, _8W/* seyC */){
  var _8X/* seyD */ = E(_8W/* seyC */);
  return new T3(0,E(B(A1(_8V/* seyB */,_8X/* seyD */.a))),E(B(A1(_8V/* seyB */,_8X/* seyD */.b))),E(B(A1(_8V/* seyB */,_8X/* seyD */.c))));
},
_8Y/* $fFunctorWorld */ = new T2(0,_8U/* Lib.World.$fFunctorWorld_$cfmap */,_8P/* Lib.World.$fFunctorWorld_$c<$ */),
_8Z/* $fApplicativeWorld */ = new T5(0,_8Y/* Lib.World.$fFunctorWorld */,_8N/* Lib.World.$fApplicativeWorld_$cpure */,_8E/* Lib.World.$fApplicativeWorld_$c<*> */,_8w/* Lib.World.$fApplicativeWorld_$c*> */,_8A/* Lib.World.$fApplicativeWorld_$c<* */),
_90/* $fArithWorld1 */ = new T1(0,0),
_91/* fromInteger */ = function(_92/* s6Go */){
  return E(E(_92/* s6Go */).g);
},
_93/* $fArithWorld_$cbasis */ = function(_94/* sesd */){
  var _95/* sese */ = B(A2(_91/* GHC.Num.fromInteger */,_94/* sesd */, _7q/* Lib.World.$fArithWorld2 */)),
  _96/* sesf */ = B(A2(_91/* GHC.Num.fromInteger */,_94/* sesd */, _90/* Lib.World.$fArithWorld1 */));
  return new T3(0,E(new T3(0,E(_95/* sese */),E(_96/* sesf */),E(_96/* sesf */))),E(new T3(0,E(_96/* sesf */),E(_95/* sese */),E(_96/* sesf */))),E(new T3(0,E(_96/* sesf */),E(_96/* sesf */),E(_95/* sese */))));
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
_9j/* $w$c** */ = function(_9k/* sa9m */, _9l/* sa9n */, _9m/* sa9o */, _9n/* sa9p */, _9o/* sa9q */){
  var _9p/* sa9r */ = new T(function(){
    return E(E(E(_9k/* sa9m */).c).a);
  }),
  _9q/* sa9R */ = new T(function(){
    var _9r/* sa9B */ = E(_9k/* sa9m */).a,
    _9s/* sa9Q */ = new T(function(){
      var _9t/* sa9E */ = new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_9p/* sa9r */));
      }),
      _9u/* sa9F */ = new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(_9t/* sa9E */));
      }),
      _9v/* sa9G */ = new T(function(){
        return B(A2(_9h/* GHC.Float.log */,_9p/* sa9r */, _9l/* sa9n */));
      }),
      _9w/* sa9H */ = new T(function(){
        return B(A3(_99/* GHC.Float.** */,_9p/* sa9r */, _9l/* sa9n */, _9n/* sa9p */));
      }),
      _9x/* sa9P */ = function(_9y/* sa9J */, _9z/* sa9K */){
        var _9A/* sa9O */ = new T(function(){
          var _9B/* sa9M */ = new T(function(){
            return B(A3(_9b/* GHC.Real./ */,_9t/* sa9E */, new T(function(){
              return B(A3(_7k/* GHC.Num.* */,_9u/* sa9F */, _9n/* sa9p */, _9y/* sa9J */));
            }), _9l/* sa9n */));
          });
          return B(A3(_6I/* GHC.Num.+ */,_9u/* sa9F */, _9B/* sa9M */, new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_9u/* sa9F */, _9z/* sa9K */, _9v/* sa9G */));
          })));
        });
        return new F(function(){return A3(_7k/* GHC.Num.* */,_9u/* sa9F */, _9w/* sa9H */, _9A/* sa9O */);});
      };
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_9r/* sa9B */)), _9x/* sa9P */, _9m/* sa9o */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_9r/* sa9B */, _9s/* sa9Q */, _9o/* sa9q */));
  });
  return new T2(0,new T(function(){
    return B(A3(_99/* GHC.Float.** */,_9p/* sa9r */, _9l/* sa9n */, _9n/* sa9p */));
  }),_9q/* sa9R */);
},
_9C/* $fFloatingExpr_$c** */ = function(_9D/* sa9S */, _9E/* sa9T */, _9F/* sa9U */, _9G/* sa9V */){
  var _9H/* sa9W */ = E(_9F/* sa9U */),
  _9I/* sa9Z */ = E(_9G/* sa9V */),
  _9J/* saa2 */ = B(_9j/* Lib.AD.$w$c** */(_9E/* sa9T */, _9H/* sa9W */.a, _9H/* sa9W */.b, _9I/* sa9Z */.a, _9I/* sa9Z */.b));
  return new T2(0,_9J/* saa2 */.a,_9J/* saa2 */.b);
},
_9K/* $fFloatingExpr1 */ = new T1(0,1),
_9L/* acos */ = function(_9M/* s1kra */){
  return E(E(_9M/* s1kra */).l);
},
_9N/* $w$cacos */ = function(_9O/* sa6D */, _9P/* sa6E */, _9Q/* sa6F */){
  var _9R/* sa6G */ = new T(function(){
    return E(E(E(_9O/* sa6D */).c).a);
  }),
  _9S/* sa73 */ = new T(function(){
    var _9T/* sa6U */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_9R/* sa6G */));
    }),
    _9U/* sa6V */ = new T(function(){
      var _9V/* sa6W */ = B(_7i/* GHC.Real.$p1Fractional */(_9T/* sa6U */)),
      _9W/* sa70 */ = new T(function(){
        var _9X/* sa6Z */ = new T(function(){
          return B(A3(_7m/* GHC.Num.- */,_9V/* sa6W */, new T(function(){
            return B(A2(_91/* GHC.Num.fromInteger */,_9V/* sa6W */, _9K/* Lib.AD.$fFloatingExpr1 */));
          }), new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_9V/* sa6W */, _9P/* sa6E */, _9P/* sa6E */));
          })));
        });
        return B(A2(_7w/* GHC.Float.sqrt */,_9R/* sa6G */, _9X/* sa6Z */));
      });
      return B(A2(_6K/* GHC.Num.negate */,_9V/* sa6W */, _9W/* sa70 */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_9O/* sa6D */).a)), function(_9Y/* sa71 */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_9T/* sa6U */, _9Y/* sa71 */, _9U/* sa6V */);});
    }, _9Q/* sa6F */));
  });
  return new T2(0,new T(function(){
    return B(A2(_9L/* GHC.Float.acos */,_9R/* sa6G */, _9P/* sa6E */));
  }),_9S/* sa73 */);
},
_9Z/* $fFloatingExpr_$cacos */ = function(_a0/* sa74 */, _a1/* sa75 */, _a2/* sa76 */){
  var _a3/* sa77 */ = E(_a2/* sa76 */),
  _a4/* sa7a */ = B(_9N/* Lib.AD.$w$cacos */(_a1/* sa75 */, _a3/* sa77 */.a, _a3/* sa77 */.b));
  return new T2(0,_a4/* sa7a */.a,_a4/* sa7a */.b);
},
_a5/* acosh */ = function(_a6/* s1ktc */){
  return E(E(_a6/* s1ktc */).r);
},
_a7/* $w$cacosh */ = function(_a8/* sa3o */, _a9/* sa3p */, _aa/* sa3q */){
  var _ab/* sa3r */ = new T(function(){
    return E(E(E(_a8/* sa3o */).c).a);
  }),
  _ac/* sa3N */ = new T(function(){
    var _ad/* sa3F */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_ab/* sa3r */));
    }),
    _ae/* sa3G */ = new T(function(){
      var _af/* sa3K */ = new T(function(){
        var _ag/* sa3H */ = B(_7i/* GHC.Real.$p1Fractional */(_ad/* sa3F */));
        return B(A3(_7m/* GHC.Num.- */,_ag/* sa3H */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_ag/* sa3H */, _a9/* sa3p */, _a9/* sa3p */));
        }), new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_ag/* sa3H */, _9K/* Lib.AD.$fFloatingExpr1 */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_ab/* sa3r */, _af/* sa3K */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_a8/* sa3o */).a)), function(_ah/* sa3L */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_ad/* sa3F */, _ah/* sa3L */, _ae/* sa3G */);});
    }, _aa/* sa3q */));
  });
  return new T2(0,new T(function(){
    return B(A2(_a5/* GHC.Float.acosh */,_ab/* sa3r */, _a9/* sa3p */));
  }),_ac/* sa3N */);
},
_ai/* $fFloatingExpr_$cacosh */ = function(_aj/* sa3O */, _ak/* sa3P */, _al/* sa3Q */){
  var _am/* sa3R */ = E(_al/* sa3Q */),
  _an/* sa3U */ = B(_a7/* Lib.AD.$w$cacosh */(_ak/* sa3P */, _am/* sa3R */.a, _am/* sa3R */.b));
  return new T2(0,_an/* sa3U */.a,_an/* sa3U */.b);
},
_ao/* asin */ = function(_ap/* s1kqP */){
  return E(E(_ap/* s1kqP */).k);
},
_aq/* $w$casin */ = function(_ar/* sa7d */, _as/* sa7e */, _at/* sa7f */){
  var _au/* sa7g */ = new T(function(){
    return E(E(E(_ar/* sa7d */).c).a);
  }),
  _av/* sa7C */ = new T(function(){
    var _aw/* sa7u */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_au/* sa7g */));
    }),
    _ax/* sa7v */ = new T(function(){
      var _ay/* sa7z */ = new T(function(){
        var _az/* sa7w */ = B(_7i/* GHC.Real.$p1Fractional */(_aw/* sa7u */));
        return B(A3(_7m/* GHC.Num.- */,_az/* sa7w */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_az/* sa7w */, _9K/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_az/* sa7w */, _as/* sa7e */, _as/* sa7e */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_au/* sa7g */, _ay/* sa7z */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_ar/* sa7d */).a)), function(_aA/* sa7A */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_aw/* sa7u */, _aA/* sa7A */, _ax/* sa7v */);});
    }, _at/* sa7f */));
  });
  return new T2(0,new T(function(){
    return B(A2(_ao/* GHC.Float.asin */,_au/* sa7g */, _as/* sa7e */));
  }),_av/* sa7C */);
},
_aB/* $fFloatingExpr_$casin */ = function(_aC/* sa7D */, _aD/* sa7E */, _aE/* sa7F */){
  var _aF/* sa7G */ = E(_aE/* sa7F */),
  _aG/* sa7J */ = B(_aq/* Lib.AD.$w$casin */(_aD/* sa7E */, _aF/* sa7G */.a, _aF/* sa7G */.b));
  return new T2(0,_aG/* sa7J */.a,_aG/* sa7J */.b);
},
_aH/* asinh */ = function(_aI/* s1ksR */){
  return E(E(_aI/* s1ksR */).q);
},
_aJ/* $w$casinh */ = function(_aK/* sa3X */, _aL/* sa3Y */, _aM/* sa3Z */){
  var _aN/* sa40 */ = new T(function(){
    return E(E(E(_aK/* sa3X */).c).a);
  }),
  _aO/* sa4m */ = new T(function(){
    var _aP/* sa4e */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_aN/* sa40 */));
    }),
    _aQ/* sa4f */ = new T(function(){
      var _aR/* sa4j */ = new T(function(){
        var _aS/* sa4g */ = B(_7i/* GHC.Real.$p1Fractional */(_aP/* sa4e */));
        return B(A3(_6I/* GHC.Num.+ */,_aS/* sa4g */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_aS/* sa4g */, _aL/* sa3Y */, _aL/* sa3Y */));
        }), new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_aS/* sa4g */, _9K/* Lib.AD.$fFloatingExpr1 */));
        })));
      });
      return B(A2(_7w/* GHC.Float.sqrt */,_aN/* sa40 */, _aR/* sa4j */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_aK/* sa3X */).a)), function(_aT/* sa4k */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_aP/* sa4e */, _aT/* sa4k */, _aQ/* sa4f */);});
    }, _aM/* sa3Z */));
  });
  return new T2(0,new T(function(){
    return B(A2(_aH/* GHC.Float.asinh */,_aN/* sa40 */, _aL/* sa3Y */));
  }),_aO/* sa4m */);
},
_aU/* $fFloatingExpr_$casinh */ = function(_aV/* sa4n */, _aW/* sa4o */, _aX/* sa4p */){
  var _aY/* sa4q */ = E(_aX/* sa4p */),
  _aZ/* sa4t */ = B(_aJ/* Lib.AD.$w$casinh */(_aW/* sa4o */, _aY/* sa4q */.a, _aY/* sa4q */.b));
  return new T2(0,_aZ/* sa4t */.a,_aZ/* sa4t */.b);
},
_b0/* atan */ = function(_b1/* s1krv */){
  return E(E(_b1/* s1krv */).m);
},
_b2/* $w$catan */ = function(_b3/* sa65 */, _b4/* sa66 */, _b5/* sa67 */){
  var _b6/* sa68 */ = new T(function(){
    return E(E(E(_b3/* sa65 */).c).a);
  }),
  _b7/* sa6t */ = new T(function(){
    var _b8/* sa6m */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_b6/* sa68 */));
    }),
    _b9/* sa6n */ = new T(function(){
      var _ba/* sa6o */ = B(_7i/* GHC.Real.$p1Fractional */(_b8/* sa6m */));
      return B(A3(_6I/* GHC.Num.+ */,_ba/* sa6o */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_ba/* sa6o */, _9K/* Lib.AD.$fFloatingExpr1 */));
      }), new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_ba/* sa6o */, _b4/* sa66 */, _b4/* sa66 */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_b3/* sa65 */).a)), function(_bb/* sa6r */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_b8/* sa6m */, _bb/* sa6r */, _b9/* sa6n */);});
    }, _b5/* sa67 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_b0/* GHC.Float.atan */,_b6/* sa68 */, _b4/* sa66 */));
  }),_b7/* sa6t */);
},
_bc/* $fFloatingExpr_$catan */ = function(_bd/* sa6u */, _be/* sa6v */, _bf/* sa6w */){
  var _bg/* sa6x */ = E(_bf/* sa6w */),
  _bh/* sa6A */ = B(_b2/* Lib.AD.$w$catan */(_be/* sa6v */, _bg/* sa6x */.a, _bg/* sa6x */.b));
  return new T2(0,_bh/* sa6A */.a,_bh/* sa6A */.b);
},
_bi/* atanh */ = function(_bj/* s1ktx */){
  return E(E(_bj/* s1ktx */).s);
},
_bk/* $w$catanh */ = function(_bl/* sa2Q */, _bm/* sa2R */, _bn/* sa2S */){
  var _bo/* sa2T */ = new T(function(){
    return E(E(E(_bl/* sa2Q */).c).a);
  }),
  _bp/* sa3e */ = new T(function(){
    var _bq/* sa37 */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_bo/* sa2T */));
    }),
    _br/* sa38 */ = new T(function(){
      var _bs/* sa39 */ = B(_7i/* GHC.Real.$p1Fractional */(_bq/* sa37 */));
      return B(A3(_7m/* GHC.Num.- */,_bs/* sa39 */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_bs/* sa39 */, _9K/* Lib.AD.$fFloatingExpr1 */));
      }), new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_bs/* sa39 */, _bm/* sa2R */, _bm/* sa2R */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_bl/* sa2Q */).a)), function(_bt/* sa3c */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_bq/* sa37 */, _bt/* sa3c */, _br/* sa38 */);});
    }, _bn/* sa2S */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bi/* GHC.Float.atanh */,_bo/* sa2T */, _bm/* sa2R */));
  }),_bp/* sa3e */);
},
_bu/* $fFloatingExpr_$catanh */ = function(_bv/* sa3f */, _bw/* sa3g */, _bx/* sa3h */){
  var _by/* sa3i */ = E(_bx/* sa3h */),
  _bz/* sa3l */ = B(_bk/* Lib.AD.$w$catanh */(_bw/* sa3g */, _by/* sa3i */.a, _by/* sa3i */.b));
  return new T2(0,_bz/* sa3l */.a,_bz/* sa3l */.b);
},
_bA/* cos */ = function(_bB/* s1kq9 */){
  return E(E(_bB/* s1kq9 */).i);
},
_bC/* sin */ = function(_bD/* s1kpO */){
  return E(E(_bD/* s1kpO */).h);
},
_bE/* $w$ccos */ = function(_bF/* sa8j */, _bG/* sa8k */, _bH/* sa8l */){
  var _bI/* sa8m */ = new T(function(){
    return E(E(E(_bF/* sa8j */).c).a);
  }),
  _bJ/* sa8G */ = new T(function(){
    var _bK/* sa8B */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_bI/* sa8m */));
      })));
    }),
    _bL/* sa8C */ = new T(function(){
      return B(A2(_6K/* GHC.Num.negate */,_bK/* sa8B */, new T(function(){
        return B(A2(_bC/* GHC.Float.sin */,_bI/* sa8m */, _bG/* sa8k */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_bF/* sa8j */).a)), function(_bM/* sa8E */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_bK/* sa8B */, _bM/* sa8E */, _bL/* sa8C */);});
    }, _bH/* sa8l */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bA/* GHC.Float.cos */,_bI/* sa8m */, _bG/* sa8k */));
  }),_bJ/* sa8G */);
},
_bN/* $fFloatingExpr_$ccos */ = function(_bO/* sa8H */, _bP/* sa8I */, _bQ/* sa8J */){
  var _bR/* sa8K */ = E(_bQ/* sa8J */),
  _bS/* sa8N */ = B(_bE/* Lib.AD.$w$ccos */(_bP/* sa8I */, _bR/* sa8K */.a, _bR/* sa8K */.b));
  return new T2(0,_bS/* sa8N */.a,_bS/* sa8N */.b);
},
_bT/* cosh */ = function(_bU/* s1ksb */){
  return E(E(_bU/* s1ksb */).o);
},
_bV/* sinh */ = function(_bW/* s1krQ */){
  return E(E(_bW/* s1krQ */).n);
},
_bX/* $w$ccosh */ = function(_bY/* sa53 */, _bZ/* sa54 */, _c0/* sa55 */){
  var _c1/* sa56 */ = new T(function(){
    return E(E(E(_bY/* sa53 */).c).a);
  }),
  _c2/* sa5p */ = new T(function(){
    var _c3/* sa5l */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_c1/* sa56 */));
      })));
    }),
    _c4/* sa5m */ = new T(function(){
      return B(A2(_bV/* GHC.Float.sinh */,_c1/* sa56 */, _bZ/* sa54 */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_bY/* sa53 */).a)), function(_c5/* sa5n */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_c3/* sa5l */, _c5/* sa5n */, _c4/* sa5m */);});
    }, _c0/* sa55 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bT/* GHC.Float.cosh */,_c1/* sa56 */, _bZ/* sa54 */));
  }),_c2/* sa5p */);
},
_c6/* $fFloatingExpr_$ccosh */ = function(_c7/* sa5q */, _c8/* sa5r */, _c9/* sa5s */){
  var _ca/* sa5t */ = E(_c9/* sa5s */),
  _cb/* sa5w */ = B(_bX/* Lib.AD.$w$ccosh */(_c8/* sa5r */, _ca/* sa5t */.a, _ca/* sa5t */.b));
  return new T2(0,_cb/* sa5w */.a,_cb/* sa5w */.b);
},
_cc/* exp */ = function(_cd/* s1ko7 */){
  return E(E(_cd/* s1ko7 */).c);
},
_ce/* $w$cexp */ = function(_cf/* sabc */, _cg/* sabd */, _ch/* sabe */){
  var _ci/* sabf */ = new T(function(){
    return E(E(E(_cf/* sabc */).c).a);
  }),
  _cj/* saby */ = new T(function(){
    var _ck/* sabu */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_ci/* sabf */));
      })));
    }),
    _cl/* sabv */ = new T(function(){
      return B(A2(_cc/* GHC.Float.exp */,_ci/* sabf */, _cg/* sabd */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_cf/* sabc */).a)), function(_cm/* sabw */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_ck/* sabu */, _cm/* sabw */, _cl/* sabv */);});
    }, _ch/* sabe */));
  });
  return new T2(0,new T(function(){
    return B(A2(_cc/* GHC.Float.exp */,_ci/* sabf */, _cg/* sabd */));
  }),_cj/* saby */);
},
_cn/* $fFloatingExpr_$cexp */ = function(_co/* sabz */, _cp/* sabA */, _cq/* sabB */){
  var _cr/* sabC */ = E(_cq/* sabB */),
  _cs/* sabF */ = B(_ce/* Lib.AD.$w$cexp */(_cp/* sabA */, _cr/* sabC */.a, _cr/* sabC */.b));
  return new T2(0,_cs/* sabF */.a,_cs/* sabF */.b);
},
_ct/* $w$clog */ = function(_cu/* saaF */, _cv/* saaG */, _cw/* saaH */){
  var _cx/* saaI */ = new T(function(){
    return E(E(E(_cu/* saaF */).c).a);
  }),
  _cy/* sab2 */ = new T(function(){
    var _cz/* saaW */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_cx/* saaI */));
    }),
    _cA/* saaX */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_cz/* saaW */));
    }),
    _cB/* saaY */ = new T(function(){
      return B(A3(_9b/* GHC.Real./ */,_cz/* saaW */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_cA/* saaX */, _9K/* Lib.AD.$fFloatingExpr1 */));
      }), _cv/* saaG */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_cu/* saaF */).a)), function(_cC/* sab0 */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_cA/* saaX */, _cC/* sab0 */, _cB/* saaY */);});
    }, _cw/* saaH */));
  });
  return new T2(0,new T(function(){
    return B(A2(_9h/* GHC.Float.log */,_cx/* saaI */, _cv/* saaG */));
  }),_cy/* sab2 */);
},
_cD/* $fFloatingExpr_$clog */ = function(_cE/* sab3 */, _cF/* sab4 */, _cG/* sab5 */){
  var _cH/* sab6 */ = E(_cG/* sab5 */),
  _cI/* sab9 */ = B(_ct/* Lib.AD.$w$clog */(_cF/* sab4 */, _cH/* sab6 */.a, _cH/* sab6 */.b));
  return new T2(0,_cI/* sab9 */.a,_cI/* sab9 */.b);
},
_cJ/* $fFloatingExpr_$clogBase */ = function(_cK/* sac5 */, _cL/* sac6 */, _cM/* sac7 */, _cN/* sac8 */){
  var _cO/* sac9 */ = new T(function(){
    return E(E(_cL/* sac6 */).c);
  }),
  _cP/* sacx */ = new T3(0,new T(function(){
    return E(E(_cL/* sac6 */).a);
  }),new T(function(){
    return E(E(_cL/* sac6 */).b);
  }),new T2(0,new T(function(){
    return E(E(_cO/* sac9 */).a);
  }),new T(function(){
    return E(E(_cO/* sac9 */).b);
  })));
  return new F(function(){return A3(_9b/* GHC.Real./ */,_cK/* sac5 */, new T(function(){
    var _cQ/* sacy */ = E(_cN/* sac8 */),
    _cR/* sacB */ = B(_ct/* Lib.AD.$w$clog */(_cP/* sacx */, _cQ/* sacy */.a, _cQ/* sacy */.b));
    return new T2(0,_cR/* sacB */.a,_cR/* sacB */.b);
  }), new T(function(){
    var _cS/* sacF */ = E(_cM/* sac7 */),
    _cT/* sacI */ = B(_ct/* Lib.AD.$w$clog */(_cP/* sacx */, _cS/* sacF */.a, _cS/* sacF */.b));
    return new T2(0,_cT/* sacI */.a,_cT/* sacI */.b);
  }));});
},
_cU/* $fFloatingExpr3 */ = new T1(0,0),
_cV/* pi */ = function(_cW/* s1knM */){
  return E(E(_cW/* s1knM */).b);
},
_cX/* pure */ = function(_cY/* s35A */){
  return E(E(_cY/* s35A */).b);
},
_cZ/* $w$cpi */ = function(_d0/* sabI */){
  var _d1/* sabJ */ = new T(function(){
    return E(E(E(_d0/* sabI */).c).a);
  }),
  _d2/* sabZ */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_d0/* sabI */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_d1/* sabJ */)))), _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(_cV/* GHC.Float.pi */(_d1/* sabJ */));
  }),_d2/* sabZ */);
},
_d3/* $fFloatingExpr_$cpi */ = function(_d4/* sac0 */, _d5/* sac1 */){
  var _d6/* sac2 */ = B(_cZ/* Lib.AD.$w$cpi */(_d5/* sac1 */));
  return new T2(0,_d6/* sac2 */.a,_d6/* sac2 */.b);
},
_d7/* $w$csin */ = function(_d8/* sa8Q */, _d9/* sa8R */, _da/* sa8S */){
  var _db/* sa8T */ = new T(function(){
    return E(E(E(_d8/* sa8Q */).c).a);
  }),
  _dc/* sa9c */ = new T(function(){
    var _dd/* sa98 */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_db/* sa8T */));
      })));
    }),
    _de/* sa99 */ = new T(function(){
      return B(A2(_bA/* GHC.Float.cos */,_db/* sa8T */, _d9/* sa8R */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_d8/* sa8Q */).a)), function(_df/* sa9a */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_dd/* sa98 */, _df/* sa9a */, _de/* sa99 */);});
    }, _da/* sa8S */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bC/* GHC.Float.sin */,_db/* sa8T */, _d9/* sa8R */));
  }),_dc/* sa9c */);
},
_dg/* $fFloatingExpr_$csin */ = function(_dh/* sa9d */, _di/* sa9e */, _dj/* sa9f */){
  var _dk/* sa9g */ = E(_dj/* sa9f */),
  _dl/* sa9j */ = B(_d7/* Lib.AD.$w$csin */(_di/* sa9e */, _dk/* sa9g */.a, _dk/* sa9g */.b));
  return new T2(0,_dl/* sa9j */.a,_dl/* sa9j */.b);
},
_dm/* $w$csinh */ = function(_dn/* sa5z */, _do/* sa5A */, _dp/* sa5B */){
  var _dq/* sa5C */ = new T(function(){
    return E(E(E(_dn/* sa5z */).c).a);
  }),
  _dr/* sa5V */ = new T(function(){
    var _ds/* sa5R */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_dq/* sa5C */));
      })));
    }),
    _dt/* sa5S */ = new T(function(){
      return B(A2(_bT/* GHC.Float.cosh */,_dq/* sa5C */, _do/* sa5A */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_dn/* sa5z */).a)), function(_du/* sa5T */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_ds/* sa5R */, _du/* sa5T */, _dt/* sa5S */);});
    }, _dp/* sa5B */));
  });
  return new T2(0,new T(function(){
    return B(A2(_bV/* GHC.Float.sinh */,_dq/* sa5C */, _do/* sa5A */));
  }),_dr/* sa5V */);
},
_dv/* $fFloatingExpr_$csinh */ = function(_dw/* sa5W */, _dx/* sa5X */, _dy/* sa5Y */){
  var _dz/* sa5Z */ = E(_dy/* sa5Y */),
  _dA/* sa62 */ = B(_dm/* Lib.AD.$w$csinh */(_dx/* sa5X */, _dz/* sa5Z */.a, _dz/* sa5Z */.b));
  return new T2(0,_dA/* sa62 */.a,_dA/* sa62 */.b);
},
_dB/* $fFloatingExpr2 */ = new T1(0,2),
_dC/* $w$csqrt */ = function(_dD/* saa5 */, _dE/* saa6 */, _dF/* saa7 */){
  var _dG/* saa8 */ = new T(function(){
    return E(E(E(_dD/* saa5 */).c).a);
  }),
  _dH/* saav */ = new T(function(){
    var _dI/* saam */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_dG/* saa8 */));
    }),
    _dJ/* saan */ = new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(_dI/* saam */));
    }),
    _dK/* saao */ = new T(function(){
      var _dL/* saar */ = new T(function(){
        return B(A3(_9b/* GHC.Real./ */,_dI/* saam */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_dJ/* saan */, _9K/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_dJ/* saan */, _dB/* Lib.AD.$fFloatingExpr2 */));
        })));
      });
      return B(A3(_9b/* GHC.Real./ */,_dI/* saam */, _dL/* saar */, new T(function(){
        return B(A2(_7w/* GHC.Float.sqrt */,_dG/* saa8 */, _dE/* saa6 */));
      })));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_dD/* saa5 */).a)), function(_dM/* saat */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_dJ/* saan */, _dM/* saat */, _dK/* saao */);});
    }, _dF/* saa7 */));
  });
  return new T2(0,new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_dG/* saa8 */, _dE/* saa6 */));
  }),_dH/* saav */);
},
_dN/* $fFloatingExpr_$csqrt */ = function(_dO/* saaw */, _dP/* saax */, _dQ/* saay */){
  var _dR/* saaz */ = E(_dQ/* saay */),
  _dS/* saaC */ = B(_dC/* Lib.AD.$w$csqrt */(_dP/* saax */, _dR/* saaz */.a, _dR/* saaz */.b));
  return new T2(0,_dS/* saaC */.a,_dS/* saaC */.b);
},
_dT/* tan */ = function(_dU/* s1kqu */){
  return E(E(_dU/* s1kqu */).j);
},
_dV/* $w$ctan */ = function(_dW/* sa7M */, _dX/* sa7N */, _dY/* sa7O */){
  var _dZ/* sa7P */ = new T(function(){
    return E(E(E(_dW/* sa7M */).c).a);
  }),
  _e0/* sa89 */ = new T(function(){
    var _e1/* sa83 */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_dZ/* sa7P */));
    }),
    _e2/* sa84 */ = new T(function(){
      var _e3/* sa85 */ = new T(function(){
        return B(A2(_bA/* GHC.Float.cos */,_dZ/* sa7P */, _dX/* sa7N */));
      });
      return B(A3(_7k/* GHC.Num.* */,B(_7i/* GHC.Real.$p1Fractional */(_e1/* sa83 */)), _e3/* sa85 */, _e3/* sa85 */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_dW/* sa7M */).a)), function(_e4/* sa87 */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_e1/* sa83 */, _e4/* sa87 */, _e2/* sa84 */);});
    }, _dY/* sa7O */));
  });
  return new T2(0,new T(function(){
    return B(A2(_dT/* GHC.Float.tan */,_dZ/* sa7P */, _dX/* sa7N */));
  }),_e0/* sa89 */);
},
_e5/* $fFloatingExpr_$ctan */ = function(_e6/* sa8a */, _e7/* sa8b */, _e8/* sa8c */){
  var _e9/* sa8d */ = E(_e8/* sa8c */),
  _ea/* sa8g */ = B(_dV/* Lib.AD.$w$ctan */(_e7/* sa8b */, _e9/* sa8d */.a, _e9/* sa8d */.b));
  return new T2(0,_ea/* sa8g */.a,_ea/* sa8g */.b);
},
_eb/* tanh */ = function(_ec/* s1ksw */){
  return E(E(_ec/* s1ksw */).p);
},
_ed/* $w$ctanh */ = function(_ee/* sa4w */, _ef/* sa4x */, _eg/* sa4y */){
  var _eh/* sa4z */ = new T(function(){
    return E(E(E(_ee/* sa4w */).c).a);
  }),
  _ei/* sa4T */ = new T(function(){
    var _ej/* sa4N */ = new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_eh/* sa4z */));
    }),
    _ek/* sa4O */ = new T(function(){
      var _el/* sa4P */ = new T(function(){
        return B(A2(_bT/* GHC.Float.cosh */,_eh/* sa4z */, _ef/* sa4x */));
      });
      return B(A3(_7k/* GHC.Num.* */,B(_7i/* GHC.Real.$p1Fractional */(_ej/* sa4N */)), _el/* sa4P */, _el/* sa4P */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_ee/* sa4w */).a)), function(_em/* sa4R */){
      return new F(function(){return A3(_9b/* GHC.Real./ */,_ej/* sa4N */, _em/* sa4R */, _ek/* sa4O */);});
    }, _eg/* sa4y */));
  });
  return new T2(0,new T(function(){
    return B(A2(_eb/* GHC.Float.tanh */,_eh/* sa4z */, _ef/* sa4x */));
  }),_ei/* sa4T */);
},
_en/* $fFloatingExpr_$ctanh */ = function(_eo/* sa4U */, _ep/* sa4V */, _eq/* sa4W */){
  var _er/* sa4X */ = E(_eq/* sa4W */),
  _es/* sa50 */ = B(_ed/* Lib.AD.$w$ctanh */(_ep/* sa4V */, _er/* sa4X */.a, _er/* sa4X */.b));
  return new T2(0,_es/* sa50 */.a,_es/* sa50 */.b);
},
_et/* $fFloatingExpr */ = function(_eu/* sacM */, _ev/* sacN */){
  return {_:0,a:_eu/* sacM */,b:new T(function(){
    return B(_d3/* Lib.AD.$fFloatingExpr_$cpi */(_eu/* sacM */, _ev/* sacN */));
  }),c:function(_ew/* B1 */){
    return new F(function(){return _cn/* Lib.AD.$fFloatingExpr_$cexp */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },d:function(_ew/* B1 */){
    return new F(function(){return _cD/* Lib.AD.$fFloatingExpr_$clog */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },e:function(_ew/* B1 */){
    return new F(function(){return _dN/* Lib.AD.$fFloatingExpr_$csqrt */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },f:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _9C/* Lib.AD.$fFloatingExpr_$c** */(_eu/* sacM */, _ev/* sacN */, _ex/* B2 */, _ew/* B1 */);});
  },g:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _cJ/* Lib.AD.$fFloatingExpr_$clogBase */(_eu/* sacM */, _ev/* sacN */, _ex/* B2 */, _ew/* B1 */);});
  },h:function(_ew/* B1 */){
    return new F(function(){return _dg/* Lib.AD.$fFloatingExpr_$csin */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },i:function(_ew/* B1 */){
    return new F(function(){return _bN/* Lib.AD.$fFloatingExpr_$ccos */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },j:function(_ew/* B1 */){
    return new F(function(){return _e5/* Lib.AD.$fFloatingExpr_$ctan */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },k:function(_ew/* B1 */){
    return new F(function(){return _aB/* Lib.AD.$fFloatingExpr_$casin */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },l:function(_ew/* B1 */){
    return new F(function(){return _9Z/* Lib.AD.$fFloatingExpr_$cacos */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },m:function(_ew/* B1 */){
    return new F(function(){return _bc/* Lib.AD.$fFloatingExpr_$catan */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },n:function(_ew/* B1 */){
    return new F(function(){return _dv/* Lib.AD.$fFloatingExpr_$csinh */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },o:function(_ew/* B1 */){
    return new F(function(){return _c6/* Lib.AD.$fFloatingExpr_$ccosh */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },p:function(_ew/* B1 */){
    return new F(function(){return _en/* Lib.AD.$fFloatingExpr_$ctanh */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },q:function(_ew/* B1 */){
    return new F(function(){return _aU/* Lib.AD.$fFloatingExpr_$casinh */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },r:function(_ew/* B1 */){
    return new F(function(){return _ai/* Lib.AD.$fFloatingExpr_$cacosh */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  },s:function(_ew/* B1 */){
    return new F(function(){return _bu/* Lib.AD.$fFloatingExpr_$catanh */(_eu/* sacM */, _ev/* sacN */, _ew/* B1 */);});
  }};
},
_ey/* $w$c/ */ = function(_ez/* sa24 */, _eA/* sa25 */, _eB/* sa26 */, _eC/* sa27 */, _eD/* sa28 */){
  var _eE/* sa2h */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_ez/* sa24 */).c).a);
    })));
  }),
  _eF/* sa2x */ = new T(function(){
    var _eG/* sa2k */ = E(_ez/* sa24 */).a,
    _eH/* sa2w */ = new T(function(){
      var _eI/* sa2n */ = new T(function(){
        return B(_7i/* GHC.Real.$p1Fractional */(_eE/* sa2h */));
      }),
      _eJ/* sa2o */ = new T(function(){
        return B(A3(_7k/* GHC.Num.* */,_eI/* sa2n */, _eC/* sa27 */, _eC/* sa27 */));
      }),
      _eK/* sa2v */ = function(_eL/* sa2q */, _eM/* sa2r */){
        var _eN/* sa2u */ = new T(function(){
          return B(A3(_7m/* GHC.Num.- */,_eI/* sa2n */, new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_eI/* sa2n */, _eL/* sa2q */, _eC/* sa27 */));
          }), new T(function(){
            return B(A3(_7k/* GHC.Num.* */,_eI/* sa2n */, _eA/* sa25 */, _eM/* sa2r */));
          })));
        });
        return new F(function(){return A3(_9b/* GHC.Real./ */,_eE/* sa2h */, _eN/* sa2u */, _eJ/* sa2o */);});
      };
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_eG/* sa2k */)), _eK/* sa2v */, _eB/* sa26 */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_eG/* sa2k */, _eH/* sa2w */, _eD/* sa28 */));
  });
  return new T2(0,new T(function(){
    return B(A3(_9b/* GHC.Real./ */,_eE/* sa2h */, _eA/* sa25 */, _eC/* sa27 */));
  }),_eF/* sa2x */);
},
_eO/* $fFractionalExpr_$c/ */ = function(_eP/* sa2y */, _eQ/* sa2z */, _eR/* sa2A */, _eS/* sa2B */){
  var _eT/* sa2C */ = E(_eR/* sa2A */),
  _eU/* sa2F */ = E(_eS/* sa2B */),
  _eV/* sa2I */ = B(_ey/* Lib.AD.$w$c/ */(_eQ/* sa2z */, _eT/* sa2C */.a, _eT/* sa2C */.b, _eU/* sa2F */.a, _eU/* sa2F */.b));
  return new T2(0,_eV/* sa2I */.a,_eV/* sa2I */.b);
},
_eW/* $w$cfromRational */ = function(_eX/* sa15 */, _eY/* sa16 */){
  var _eZ/* sa1f */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_eX/* sa15 */).c).a);
    })));
  }),
  _f0/* sa1n */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_eX/* sa15 */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(_eZ/* sa1f */)), _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_7o/* GHC.Real.fromRational */,_eZ/* sa1f */, _eY/* sa16 */));
  }),_f0/* sa1n */);
},
_f1/* $fFractionalExpr_$cfromRational */ = function(_f2/* sa1o */, _f3/* sa1p */, _f4/* sa1q */){
  var _f5/* sa1r */ = B(_eW/* Lib.AD.$w$cfromRational */(_f3/* sa1p */, _f4/* sa1q */));
  return new T2(0,_f5/* sa1r */.a,_f5/* sa1r */.b);
},
_f6/* $w$crecip */ = function(_f7/* sa1u */, _f8/* sa1v */, _f9/* sa1w */){
  var _fa/* sa1F */ = new T(function(){
    return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
      return E(E(E(_f7/* sa1u */).c).a);
    })));
  }),
  _fb/* sa1G */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(_fa/* sa1F */));
  }),
  _fc/* sa1U */ = new T(function(){
    var _fd/* sa1O */ = new T(function(){
      var _fe/* sa1R */ = new T(function(){
        return B(A3(_9b/* GHC.Real./ */,_fa/* sa1F */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_fb/* sa1G */, _9K/* Lib.AD.$fFloatingExpr1 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_fb/* sa1G */, _f8/* sa1v */, _f8/* sa1v */));
        })));
      });
      return B(A2(_6K/* GHC.Num.negate */,_fb/* sa1G */, _fe/* sa1R */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_f7/* sa1u */).a)), function(_ff/* sa1S */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_fb/* sa1G */, _ff/* sa1S */, _fd/* sa1O */);});
    }, _f9/* sa1w */));
  }),
  _fg/* sa1I */ = new T(function(){
    return B(A3(_9b/* GHC.Real./ */,_fa/* sa1F */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_fb/* sa1G */, _9K/* Lib.AD.$fFloatingExpr1 */));
    }), _f8/* sa1v */));
  });
  return new T2(0,_fg/* sa1I */,_fc/* sa1U */);
},
_fh/* $fFractionalExpr_$crecip */ = function(_fi/* sa1V */, _fj/* sa1W */, _fk/* sa1X */){
  var _fl/* sa1Y */ = E(_fk/* sa1X */),
  _fm/* sa21 */ = B(_f6/* Lib.AD.$w$crecip */(_fj/* sa1W */, _fl/* sa1Y */.a, _fl/* sa1Y */.b));
  return new T2(0,_fm/* sa21 */.a,_fm/* sa21 */.b);
},
_fn/* $fFractionalExpr */ = function(_fo/* sa2L */, _fp/* sa2M */){
  return new T4(0,_fo/* sa2L */,function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _eO/* Lib.AD.$fFractionalExpr_$c/ */(_fo/* sa2L */, _fp/* sa2M */, _ex/* B2 */, _ew/* B1 */);});
  },function(_ew/* B1 */){
    return new F(function(){return _fh/* Lib.AD.$fFractionalExpr_$crecip */(_fo/* sa2L */, _fp/* sa2M */, _ew/* B1 */);});
  },function(_ew/* B1 */){
    return new F(function(){return _f1/* Lib.AD.$fFractionalExpr_$cfromRational */(_fo/* sa2L */, _fp/* sa2M */, _ew/* B1 */);});
  });
},
_fq/* $w$c* */ = function(_fr/* s9ZE */, _fs/* s9ZF */, _ft/* s9ZG */, _fu/* s9ZH */, _fv/* s9ZI */){
  var _fw/* s9ZS */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_fr/* s9ZE */).c).a);
      })));
    })));
  }),
  _fx/* sa05 */ = new T(function(){
    var _fy/* s9ZV */ = E(_fr/* s9ZE */).a,
    _fz/* sa04 */ = new T(function(){
      var _fA/* sa03 */ = function(_fB/* s9ZZ */, _fC/* sa00 */){
        return new F(function(){return A3(_6I/* GHC.Num.+ */,_fw/* s9ZS */, new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_fw/* s9ZS */, _fs/* s9ZF */, _fC/* sa00 */));
        }), new T(function(){
          return B(A3(_7k/* GHC.Num.* */,_fw/* s9ZS */, _fB/* s9ZZ */, _fu/* s9ZH */));
        }));});
      };
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_fy/* s9ZV */)), _fA/* sa03 */, _ft/* s9ZG */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_fy/* s9ZV */, _fz/* sa04 */, _fv/* s9ZI */));
  });
  return new T2(0,new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_fw/* s9ZS */, _fs/* s9ZF */, _fu/* s9ZH */));
  }),_fx/* sa05 */);
},
_fD/* $fNumExpr_$c* */ = function(_fE/* sa06 */, _fF/* sa07 */, _fG/* sa08 */){
  var _fH/* sa09 */ = E(_fF/* sa07 */),
  _fI/* sa0c */ = E(_fG/* sa08 */),
  _fJ/* sa0f */ = B(_fq/* Lib.AD.$w$c* */(_fE/* sa06 */, _fH/* sa09 */.a, _fH/* sa09 */.b, _fI/* sa0c */.a, _fI/* sa0c */.b));
  return new T2(0,_fJ/* sa0f */.a,_fJ/* sa0f */.b);
},
_fK/* $w$c+ */ = function(_fL/* sa0i */, _fM/* sa0j */, _fN/* sa0k */, _fO/* sa0l */, _fP/* sa0m */){
  var _fQ/* sa0w */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_fL/* sa0i */).c).a);
      })));
    })));
  }),
  _fR/* sa0F */ = new T(function(){
    var _fS/* sa0z */ = E(_fL/* sa0i */).a,
    _fT/* sa0E */ = new T(function(){
      return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_fS/* sa0z */)), new T(function(){
        return B(_6I/* GHC.Num.+ */(_fQ/* sa0w */));
      }), _fN/* sa0k */));
    });
    return B(A3(_9d/* GHC.Base.<*> */,_fS/* sa0z */, _fT/* sa0E */, _fP/* sa0m */));
  });
  return new T2(0,new T(function(){
    return B(A3(_6I/* GHC.Num.+ */,_fQ/* sa0w */, _fM/* sa0j */, _fO/* sa0l */));
  }),_fR/* sa0F */);
},
_fU/* $fNumExpr_$c+ */ = function(_fV/* sa0G */, _fW/* sa0H */, _fX/* sa0I */){
  var _fY/* sa0J */ = E(_fW/* sa0H */),
  _fZ/* sa0M */ = E(_fX/* sa0I */),
  _g0/* sa0P */ = B(_fK/* Lib.AD.$w$c+ */(_fV/* sa0G */, _fY/* sa0J */.a, _fY/* sa0J */.b, _fZ/* sa0M */.a, _fZ/* sa0M */.b));
  return new T2(0,_g0/* sa0P */.a,_g0/* sa0P */.b);
},
_g1/* $fNumExpr_$c- */ = function(_g2/* sa0S */, _g3/* sa0T */, _g4/* sa0U */){
  var _g5/* sa0V */ = B(_g6/* Lib.AD.$fNumExpr */(_g2/* sa0S */));
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_g5/* sa0V */, _g3/* sa0T */, new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_g5/* sa0V */, _g4/* sa0U */));
  }));});
},
_g7/* abs */ = function(_g8/* s6G6 */){
  return E(E(_g8/* s6G6 */).e);
},
_g9/* signum */ = function(_ga/* s6Gf */){
  return E(E(_ga/* s6Gf */).f);
},
_gb/* $w$cabs */ = function(_gc/* s9YG */, _gd/* s9YH */, _ge/* s9YI */){
  var _gf/* s9YS */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gc/* s9YG */).c).a);
      })));
    })));
  }),
  _gg/* s9Z2 */ = new T(function(){
    var _gh/* s9YZ */ = new T(function(){
      return B(A2(_g9/* GHC.Num.signum */,_gf/* s9YS */, _gd/* s9YH */));
    });
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_gc/* s9YG */).a)), function(_gi/* s9Z0 */){
      return new F(function(){return A3(_7k/* GHC.Num.* */,_gf/* s9YS */, _gi/* s9Z0 */, _gh/* s9YZ */);});
    }, _ge/* s9YI */));
  });
  return new T2(0,new T(function(){
    return B(A2(_g7/* GHC.Num.abs */,_gf/* s9YS */, _gd/* s9YH */));
  }),_gg/* s9Z2 */);
},
_gj/* $fNumExpr_$cabs */ = function(_gk/* s9Z3 */, _gl/* s9Z4 */){
  var _gm/* s9Z5 */ = E(_gl/* s9Z4 */),
  _gn/* s9Z8 */ = B(_gb/* Lib.AD.$w$cabs */(_gk/* s9Z3 */, _gm/* s9Z5 */.a, _gm/* s9Z5 */.b));
  return new T2(0,_gn/* s9Z8 */.a,_gn/* s9Z8 */.b);
},
_go/* $w$cfromInteger */ = function(_gp/* s9XR */, _gq/* s9XS */){
  var _gr/* s9Y2 */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gp/* s9XR */).c).a);
      })));
    })));
  }),
  _gs/* s9Y9 */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_gp/* s9XR */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_gr/* s9Y2 */, _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,_gr/* s9Y2 */, _gq/* s9XS */));
  }),_gs/* s9Y9 */);
},
_gt/* $fNumExpr_$cfromInteger */ = function(_gu/* s9Ya */, _gv/* s9Yb */){
  var _gw/* s9Yc */ = B(_go/* Lib.AD.$w$cfromInteger */(_gu/* s9Ya */, _gv/* s9Yb */));
  return new T2(0,_gw/* s9Yc */.a,_gw/* s9Yc */.b);
},
_gx/* $w$cnegate */ = function(_gy/* s9Zb */, _gz/* s9Zc */, _gA/* s9Zd */){
  var _gB/* s9Zn */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gy/* s9Zb */).c).a);
      })));
    })));
  }),
  _gC/* s9Zv */ = new T(function(){
    return B(A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(E(_gy/* s9Zb */).a)), new T(function(){
      return B(_6K/* GHC.Num.negate */(_gB/* s9Zn */));
    }), _gA/* s9Zd */));
  });
  return new T2(0,new T(function(){
    return B(A2(_6K/* GHC.Num.negate */,_gB/* s9Zn */, _gz/* s9Zc */));
  }),_gC/* s9Zv */);
},
_gD/* $fNumExpr_$cnegate */ = function(_gE/* s9Zw */, _gF/* s9Zx */){
  var _gG/* s9Zy */ = E(_gF/* s9Zx */),
  _gH/* s9ZB */ = B(_gx/* Lib.AD.$w$cnegate */(_gE/* s9Zw */, _gG/* s9Zy */.a, _gG/* s9Zy */.b));
  return new T2(0,_gH/* s9ZB */.a,_gH/* s9ZB */.b);
},
_gI/* $w$csignum */ = function(_gJ/* s9Yf */, _gK/* s9Yg */){
  var _gL/* s9Yq */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(new T(function(){
        return E(E(E(_gJ/* s9Yf */).c).a);
      })));
    })));
  }),
  _gM/* s9Yx */ = new T(function(){
    return B(A2(_cX/* GHC.Base.pure */,E(_gJ/* s9Yf */).a, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_gL/* s9Yq */, _cU/* Lib.AD.$fFloatingExpr3 */));
    })));
  });
  return new T2(0,new T(function(){
    return B(A2(_g9/* GHC.Num.signum */,_gL/* s9Yq */, _gK/* s9Yg */));
  }),_gM/* s9Yx */);
},
_gN/* $fNumExpr_$csignum */ = function(_gO/* s9Yy */, _gP/* s9Yz */){
  var _gQ/* s9YD */ = B(_gI/* Lib.AD.$w$csignum */(_gO/* s9Yy */, E(_gP/* s9Yz */).a));
  return new T2(0,_gQ/* s9YD */.a,_gQ/* s9YD */.b);
},
_g6/* $fNumExpr */ = function(_gR/* sa0X */){
  return {_:0,a:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _fU/* Lib.AD.$fNumExpr_$c+ */(_gR/* sa0X */, _ex/* B2 */, _ew/* B1 */);});
  },b:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _g1/* Lib.AD.$fNumExpr_$c- */(_gR/* sa0X */, _ex/* B2 */, _ew/* B1 */);});
  },c:function(_ex/* B2 */, _ew/* B1 */){
    return new F(function(){return _fD/* Lib.AD.$fNumExpr_$c* */(_gR/* sa0X */, _ex/* B2 */, _ew/* B1 */);});
  },d:function(_ew/* B1 */){
    return new F(function(){return _gD/* Lib.AD.$fNumExpr_$cnegate */(_gR/* sa0X */, _ew/* B1 */);});
  },e:function(_ew/* B1 */){
    return new F(function(){return _gj/* Lib.AD.$fNumExpr_$cabs */(_gR/* sa0X */, _ew/* B1 */);});
  },f:function(_ew/* B1 */){
    return new F(function(){return _gN/* Lib.AD.$fNumExpr_$csignum */(_gR/* sa0X */, _ew/* B1 */);});
  },g:function(_ew/* B1 */){
    return new F(function(){return _gt/* Lib.AD.$fNumExpr_$cfromInteger */(_gR/* sa0X */, _ew/* B1 */);});
  }};
},
_gS/* gradient */ = function(_gT/* sezr */){
  var _gU/* sezs */ = new T(function(){
    return E(E(_gT/* sezr */).a);
  }),
  _gV/* sezB */ = new T3(0,_8Z/* Lib.World.$fApplicativeWorld */,_93/* Lib.World.$fArithWorld_$cbasis */,new T2(0,_gU/* sezs */,new T(function(){
    return E(E(_gT/* sezr */).b);
  }))),
  _gW/* sezE */ = new T(function(){
    return B(_et/* Lib.AD.$fFloatingExpr */(new T(function(){
      return B(_fn/* Lib.AD.$fFractionalExpr */(new T(function(){
        return B(_g6/* Lib.AD.$fNumExpr */(_gV/* sezB */));
      }), _gV/* sezB */));
    }), _gV/* sezB */));
  }),
  _gX/* sezG */ = new T(function(){
    return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
      return B(_7g/* GHC.Float.$p1Floating */(_gU/* sezs */));
    })));
  });
  return function(_gY/* sezH */){
    var _gZ/* sezI */ = E(_gY/* sezH */),
    _h0/* sezM */ = B(A2(_91/* GHC.Num.fromInteger */,_gX/* sezG */, _7q/* Lib.World.$fArithWorld2 */)),
    _h1/* sezN */ = B(A2(_91/* GHC.Num.fromInteger */,_gX/* sezG */, _90/* Lib.World.$fArithWorld1 */));
    return E(B(_7y/* Lib.World.$wfield */(_gW/* sezE */, new T2(0,_gZ/* sezI */.a,new T3(0,E(_h0/* sezM */),E(_h1/* sezN */),E(_h1/* sezN */))), new T2(0,_gZ/* sezI */.b,new T3(0,E(_h1/* sezN */),E(_h0/* sezM */),E(_h1/* sezN */))), new T2(0,_gZ/* sezI */.c,new T3(0,E(_h1/* sezN */),E(_h1/* sezN */),E(_h0/* sezM */))))).b);
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
  var _h8/* sgUR */ = B(A1(_h2/* Lib.Shader.gradStr6 */,_84/* Lib.Shader.argument */));
  return new T2(1,_h8/* sgUR */.a,new T(function(){
    return B(_h3/* Data.OldList.prependToAll */(_r/* Lib.Shader.$fFloatingVar29 */, new T2(1,_h8/* sgUR */.b,new T2(1,_h8/* sgUR */.c,_o/* GHC.Types.[] */))));
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
_hq/* $wg1 */ = function(_hr/* sfWn */, _hs/* sfWo */, _ht/* sfWp */){
  while(1){
    if(!(_hs/* sfWo */%2)){
      var _hu/*  sfWn */ = _hr/* sfWn */*_hr/* sfWn */,
      _hv/*  sfWo */ = quot/* EXTERNAL */(_hs/* sfWo */, 2);
      _hr/* sfWn */ = _hu/*  sfWn */;
      _hs/* sfWo */ = _hv/*  sfWo */;
      continue;
    }else{
      var _hw/* sfWr */ = E(_hs/* sfWo */);
      if(_hw/* sfWr */==1){
        return _hr/* sfWn */*_ht/* sfWp */;
      }else{
        var _hu/*  sfWn */ = _hr/* sfWn */*_hr/* sfWn */,
        _hx/*  sfWp */ = _hr/* sfWn */*_ht/* sfWp */;
        _hr/* sfWn */ = _hu/*  sfWn */;
        _hs/* sfWo */ = quot/* EXTERNAL */(_hw/* sfWr */-1|0, 2);
        _ht/* sfWp */ = _hx/*  sfWp */;
        continue;
      }
    }
  }
},
_hy/* $wf */ = function(_hz/* sfWy */, _hA/* sfWz */){
  while(1){
    if(!(_hA/* sfWz */%2)){
      var _hB/*  sfWy */ = _hz/* sfWy */*_hz/* sfWy */,
      _hC/*  sfWz */ = quot/* EXTERNAL */(_hA/* sfWz */, 2);
      _hz/* sfWy */ = _hB/*  sfWy */;
      _hA/* sfWz */ = _hC/*  sfWz */;
      continue;
    }else{
      var _hD/* sfWB */ = E(_hA/* sfWz */);
      if(_hD/* sfWB */==1){
        return E(_hz/* sfWy */);
      }else{
        return new F(function(){return _hq/* Lib.Object.$wg1 */(_hz/* sfWy */*_hz/* sfWy */, quot/* EXTERNAL */(_hD/* sfWB */-1|0, 2), _hz/* sfWy */);});
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
_jr/* $fToAnyPolygon1 */ = "t",
_js/* $fToAnyPolygon2 */ = "a",
_jt/* $fToAnyPolygon3 */ = "r",
_ju/* $fToAnyPolygon4 */ = "ly",
_jv/* $fToAnyPolygon5 */ = "lx",
_jw/* $fToAnyPolygon6 */ = "wz",
_jx/* $fToAnyPolygon7 */ = "wy",
_jy/* $fToAnyPolygon8 */ = "wx",
_jz/* () */ = 0,
_jA/* $wtoObject */ = function(_jB/* sbWw */){
  var _jC/* sbWy */ = __new/* EXTERNAL */(),
  _jD/* sbWA */ = _jC/* sbWy */,
  _jE/* sbWB */ = function(_jF/* sbWC */, _/* EXTERNAL */){
    while(1){
      var _jG/* sbWE */ = E(_jF/* sbWC */);
      if(!_jG/* sbWE */._){
        return _jz/* GHC.Tuple.() */;
      }else{
        var _jH/* sbWH */ = E(_jG/* sbWE */.a),
        _jI/* sbWP */ = __set/* EXTERNAL */(_jD/* sbWA */, E(_jH/* sbWH */.a), E(_jH/* sbWH */.b));
        _jF/* sbWC */ = _jG/* sbWE */.b;
        continue;
      }
    }
  },
  _jJ/* sbWR */ = B(_jE/* sbWB */(_jB/* sbWw */, _/* EXTERNAL */));
  return E(_jD/* sbWA */);
},
_jK/* $w$ctoAny2 */ = function(_jL/* sgl7 */, _jM/* sgl8 */, _jN/* sgl9 */, _jO/* sgla */, _jP/* sglb */, _jQ/* sglc */){
  return new F(function(){return _jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_jy/* Lib.Object.$fToAnyPolygon8 */,_jL/* sgl7 */),new T2(1,new T2(0,_jx/* Lib.Object.$fToAnyPolygon7 */,_jM/* sgl8 */),new T2(1,new T2(0,_jw/* Lib.Object.$fToAnyPolygon6 */,_jN/* sgl9 */),new T2(1,new T2(0,_jv/* Lib.Object.$fToAnyPolygon5 */,_jO/* sgla */*_jP/* sglb */*Math.cos/* EXTERNAL */(_jQ/* sglc */)),new T2(1,new T2(0,_ju/* Lib.Object.$fToAnyPolygon4 */,_jO/* sgla */*_jP/* sglb */*Math.sin/* EXTERNAL */(_jQ/* sglc */)),new T2(1,new T2(0,_jt/* Lib.Object.$fToAnyPolygon3 */,_jO/* sgla */),new T2(1,new T2(0,_js/* Lib.Object.$fToAnyPolygon2 */,_jP/* sglb */),new T2(1,new T2(0,_jr/* Lib.Object.$fToAnyPolygon1 */,_jQ/* sglc */),_o/* GHC.Types.[] */)))))))));});
},
_jR/* $fToAnyPolygon_$ctoAny1 */ = function(_jS/* sglE */){
  var _jT/* sglF */ = E(_jS/* sglE */),
  _jU/* sglJ */ = E(_jT/* sglF */.a),
  _jV/* sglN */ = E(_jT/* sglF */.b);
  return new F(function(){return _jK/* Lib.Object.$w$ctoAny2 */(_jU/* sglJ */.a, _jU/* sglJ */.b, _jU/* sglJ */.c, E(_jV/* sglN */.a), E(_jV/* sglN */.b), E(_jT/* sglF */.c));});
},
_jW/* map */ = function(_jX/* s3hr */, _jY/* s3hs */){
  var _jZ/* s3ht */ = E(_jY/* s3hs */);
  return (_jZ/* s3ht */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T(function(){
    return B(A1(_jX/* s3hr */,_jZ/* s3ht */.a));
  }),new T(function(){
    return B(_jW/* GHC.Base.map */(_jX/* s3hr */, _jZ/* s3ht */.b));
  }));
},
_k0/* $w$ctoAny1 */ = function(_k1/* sgn5 */, _k2/* sgn6 */, _k3/* sgn7 */){
  var _k4/* sgne */ = __lst2arr/* EXTERNAL */(B(_jW/* GHC.Base.map */(_jR/* Lib.Object.$fToAnyPolygon_$ctoAny1 */, new T2(1,_k1/* sgn5 */,new T2(1,_k2/* sgn6 */,new T2(1,_k3/* sgn7 */,_o/* GHC.Types.[] */))))));
  return E(_k4/* sgne */);
},
_k5/* $fToAnyPolygon_$ctoAny */ = function(_k6/* sgnh */){
  var _k7/* sgni */ = E(_k6/* sgnh */);
  return new F(function(){return _k0/* Lib.Object.$w$ctoAny1 */(_k7/* sgni */.a, _k7/* sgni */.b, _k7/* sgni */.c);});
},
_k8/* $sfitP1 */ = new T2(0,_iR/* GHC.Float.$fFloatingDouble */,_jq/* GHC.Classes.$fOrdDouble */),
_k9/* $w$cdot */ = function(_ka/* sesj */, _kb/* sesk */, _kc/* sesl */, _kd/* sesm */, _ke/* sesn */, _kf/* seso */, _kg/* sesp */){
  var _kh/* sesr */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_ka/* sesj */)))),
  _ki/* sesu */ = new T(function(){
    return B(A3(_6I/* GHC.Num.+ */,_kh/* sesr */, new T(function(){
      return B(A3(_7k/* GHC.Num.* */,_kh/* sesr */, _kb/* sesk */, _ke/* sesn */));
    }), new T(function(){
      return B(A3(_7k/* GHC.Num.* */,_kh/* sesr */, _kc/* sesl */, _kf/* seso */));
    })));
  });
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_kh/* sesr */, _ki/* sesu */, new T(function(){
    return B(A3(_7k/* GHC.Num.* */,_kh/* sesr */, _kd/* sesm */, _kg/* sesp */));
  }));});
},
_kj/* $w$cnormalize */ = function(_kk/* set5 */, _kl/* set6 */, _km/* set7 */, _kn/* set8 */){
  var _ko/* set9 */ = B(_7g/* GHC.Float.$p1Floating */(_kk/* set5 */)),
  _kp/* seta */ = new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_kk/* set5 */, new T(function(){
      return B(_k9/* Lib.World.$w$cdot */(_kk/* set5 */, _kl/* set6 */, _km/* set7 */, _kn/* set8 */, _kl/* set6 */, _km/* set7 */, _kn/* set8 */));
    })));
  });
  return new T3(0,B(A3(_9b/* GHC.Real./ */,_ko/* set9 */, _kl/* set6 */, _kp/* seta */)),B(A3(_9b/* GHC.Real./ */,_ko/* set9 */, _km/* set7 */, _kp/* seta */)),B(A3(_9b/* GHC.Real./ */,_ko/* set9 */, _kn/* set8 */, _kp/* seta */)));
},
_kq/* $w$c* */ = function(_kr/* serh */, _ks/* seri */, _kt/* serj */, _ku/* serk */, _kv/* serl */, _kw/* serm */, _kx/* sern */){
  var _ky/* sero */ = B(_7k/* GHC.Num.* */(_kr/* serh */));
  return new T3(0,B(A1(B(A1(_ky/* sero */,_ks/* seri */)),_kv/* serl */)),B(A1(B(A1(_ky/* sero */,_kt/* serj */)),_kw/* serm */)),B(A1(B(A1(_ky/* sero */,_ku/* serk */)),_kx/* sern */)));
},
_kz/* $w$c+ */ = function(_kA/* serK */, _kB/* serL */, _kC/* serM */, _kD/* serN */, _kE/* serO */, _kF/* serP */, _kG/* serQ */){
  var _kH/* serR */ = B(_6I/* GHC.Num.+ */(_kA/* serK */));
  return new T3(0,B(A1(B(A1(_kH/* serR */,_kB/* serL */)),_kE/* serO */)),B(A1(B(A1(_kH/* serR */,_kC/* serM */)),_kF/* serP */)),B(A1(B(A1(_kH/* serR */,_kD/* serN */)),_kG/* serQ */)));
},
_kI/* $wfitP */ = function(_kJ/* seAb */, _kK/* seAc */){
  var _kL/* seAd */ = new T(function(){
    return E(E(_kJ/* seAb */).a);
  }),
  _kM/* seAh */ = new T(function(){
    return B(A2(_gS/* Lib.World.gradient */,new T2(0,_kL/* seAd */,new T(function(){
      return E(E(_kJ/* seAb */).b);
    })), _kK/* seAc */));
  }),
  _kN/* seAn */ = new T(function(){
    var _kO/* seAo */ = E(_kM/* seAh */),
    _kP/* seAs */ = B(_kj/* Lib.World.$w$cnormalize */(_kL/* seAd */, _kO/* seAo */.a, _kO/* seAo */.b, _kO/* seAo */.c));
    return new T3(0,E(_kP/* seAs */.a),E(_kP/* seAs */.b),E(_kP/* seAs */.c));
  }),
  _kQ/* seB0 */ = new T(function(){
    var _kR/* seAw */ = E(_kK/* seAc */),
    _kS/* seAx */ = _kR/* seAw */.a,
    _kT/* seAy */ = _kR/* seAw */.b,
    _kU/* seAz */ = _kR/* seAw */.c,
    _kV/* seAA */ = E(_kN/* seAn */),
    _kW/* seAE */ = B(_7g/* GHC.Float.$p1Floating */(_kL/* seAd */)),
    _kX/* seAL */ = new T(function(){
      return B(A2(_7w/* GHC.Float.sqrt */,_kL/* seAd */, new T(function(){
        var _kY/* seAG */ = E(_kM/* seAh */),
        _kZ/* seAH */ = _kY/* seAG */.a,
        _l0/* seAI */ = _kY/* seAG */.b,
        _l1/* seAJ */ = _kY/* seAG */.c;
        return B(_k9/* Lib.World.$w$cdot */(_kL/* seAd */, _kZ/* seAH */, _l0/* seAI */, _l1/* seAJ */, _kZ/* seAH */, _l0/* seAI */, _l1/* seAJ */));
      })));
    }),
    _l2/* seAM */ = B(A3(_9b/* GHC.Real./ */,_kW/* seAE */, new T(function(){
      return B(_7y/* Lib.World.$wfield */(_kL/* seAd */, _kS/* seAx */, _kT/* seAy */, _kU/* seAz */));
    }), _kX/* seAL */)),
    _l3/* seAN */ = B(_7i/* GHC.Real.$p1Fractional */(_kW/* seAE */)),
    _l4/* seAO */ = B(_kq/* Lib.World.$w$c* */(_l3/* seAN */, _kV/* seAA */.a, _kV/* seAA */.b, _kV/* seAA */.c, _l2/* seAM */, _l2/* seAM */, _l2/* seAM */)),
    _l5/* seAS */ = B(_6K/* GHC.Num.negate */(_l3/* seAN */)),
    _l6/* seAW */ = B(_kz/* Lib.World.$w$c+ */(_l3/* seAN */, _kS/* seAx */, _kT/* seAy */, _kU/* seAz */, B(A1(_l5/* seAS */,_l4/* seAO */.a)), B(A1(_l5/* seAS */,_l4/* seAO */.b)), B(A1(_l5/* seAS */,_l4/* seAO */.c))));
    return new T3(0,E(_l6/* seAW */.a),E(_l6/* seAW */.b),E(_l6/* seAW */.c));
  });
  return new T2(0,_kQ/* seB0 */,_kN/* seAn */);
},
_l7/* $p1Ord */ = function(_l8/* scBS */){
  return E(E(_l8/* scBS */).a);
},
_l9/* $wperpTo */ = function(_la/* sets */, _lb/* sett */, _lc/* setu */, _ld/* setv */, _le/* setw */, _lf/* setx */, _lg/* sety */){
  var _lh/* setz */ = B(_k9/* Lib.World.$w$cdot */(_la/* sets */, _le/* setw */, _lf/* setx */, _lg/* sety */, _lb/* sett */, _lc/* setu */, _ld/* setv */)),
  _li/* setB */ = B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_la/* sets */)))),
  _lj/* setC */ = B(_kq/* Lib.World.$w$c* */(_li/* setB */, _le/* setw */, _lf/* setx */, _lg/* sety */, _lh/* setz */, _lh/* setz */, _lh/* setz */)),
  _lk/* setG */ = B(_6K/* GHC.Num.negate */(_li/* setB */));
  return new F(function(){return _kz/* Lib.World.$w$c+ */(_li/* setB */, _lb/* sett */, _lc/* setu */, _ld/* setv */, B(A1(_lk/* setG */,_lj/* setC */.a)), B(A1(_lk/* setG */,_lj/* setC */.b)), B(A1(_lk/* setG */,_lj/* setC */.c)));});
},
_ll/* == */ = function(_lm/* scBK */){
  return E(E(_lm/* scBK */).a);
},
_ln/* $wfitV */ = function(_lo/* seu2 */, _lp/* seu3 */, _lq/* seu4 */, _lr/* seu5 */){
  var _ls/* seu6 */ = new T(function(){
    var _lt/* seu7 */ = E(_lr/* seu5 */),
    _lu/* seub */ = E(_lq/* seu4 */),
    _lv/* seuf */ = B(_l9/* Lib.World.$wperpTo */(_lo/* seu2 */, _lt/* seu7 */.a, _lt/* seu7 */.b, _lt/* seu7 */.c, _lu/* seub */.a, _lu/* seub */.b, _lu/* seub */.c));
    return new T3(0,E(_lv/* seuf */.a),E(_lv/* seuf */.b),E(_lv/* seuf */.c));
  }),
  _lw/* seup */ = new T(function(){
    return B(A2(_7w/* GHC.Float.sqrt */,_lo/* seu2 */, new T(function(){
      var _lx/* seuk */ = E(_ls/* seu6 */),
      _ly/* seul */ = _lx/* seuk */.a,
      _lz/* seum */ = _lx/* seuk */.b,
      _lA/* seun */ = _lx/* seuk */.c;
      return B(_k9/* Lib.World.$w$cdot */(_lo/* seu2 */, _ly/* seul */, _lz/* seum */, _lA/* seun */, _ly/* seul */, _lz/* seum */, _lA/* seun */));
    })));
  });
  if(!B(A3(_ll/* GHC.Classes.== */,B(_l7/* GHC.Classes.$p1Ord */(_lp/* seu3 */)), _lw/* seup */, new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_lo/* seu2 */)))), _90/* Lib.World.$fArithWorld1 */));
  })))){
    var _lB/* seuu */ = E(_ls/* seu6 */),
    _lC/* seuy */ = B(_kj/* Lib.World.$w$cnormalize */(_lo/* seu2 */, _lB/* seuu */.a, _lB/* seuu */.b, _lB/* seuu */.c)),
    _lD/* seuH */ = B(A2(_7w/* GHC.Float.sqrt */,_lo/* seu2 */, new T(function(){
      var _lE/* seuC */ = E(_lr/* seu5 */),
      _lF/* seuD */ = _lE/* seuC */.a,
      _lG/* seuE */ = _lE/* seuC */.b,
      _lH/* seuF */ = _lE/* seuC */.c;
      return B(_k9/* Lib.World.$w$cdot */(_lo/* seu2 */, _lF/* seuD */, _lG/* seuE */, _lH/* seuF */, _lF/* seuD */, _lG/* seuE */, _lH/* seuF */));
    }))),
    _lI/* seuK */ = B(_7k/* GHC.Num.* */(new T(function(){
      return B(_7i/* GHC.Real.$p1Fractional */(new T(function(){
        return B(_7g/* GHC.Float.$p1Floating */(_lo/* seu2 */));
      })));
    })));
    return new T3(0,B(A1(B(A1(_lI/* seuK */,_lC/* seuy */.a)),_lD/* seuH */)),B(A1(B(A1(_lI/* seuK */,_lC/* seuy */.b)),_lD/* seuH */)),B(A1(B(A1(_lI/* seuK */,_lC/* seuy */.c)),_lD/* seuH */)));
  }else{
    var _lJ/* seuT */ = B(A2(_91/* GHC.Num.fromInteger */,B(_7i/* GHC.Real.$p1Fractional */(B(_7g/* GHC.Float.$p1Floating */(_lo/* seu2 */)))), _90/* Lib.World.$fArithWorld1 */));
    return new T3(0,_lJ/* seuT */,_lJ/* seuT */,_lJ/* seuT */);
  }
},
_lK/* angleCount */ = new T(function(){
  var _lL/* s6PE */ = eval/* EXTERNAL */("angleCount"),
  _lM/* s6PI */ = Number/* EXTERNAL */(_lL/* s6PE */);
  return jsTrunc/* EXTERNAL */(_lM/* s6PI */);
}),
_lN/* aN */ = new T(function(){
  return E(_lK/* Lib.Util.angleCount */);
}),
_lO/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_lP/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_lQ/* errorEmptyList */ = function(_lR/* sbDG */){
  return new F(function(){return err/* EXTERNAL */(B(_f/* GHC.Base.++ */(_lP/* GHC.List.prel_list_str */, new T(function(){
    return B(_f/* GHC.Base.++ */(_lR/* sbDG */, _lO/* GHC.List.lvl */));
  },1))));});
},
_lS/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("head"));
}),
_lT/* badHead */ = new T(function(){
  return B(_lQ/* GHC.List.errorEmptyList */(_lS/* GHC.List.lvl18 */));
}),
_lU/* go1 */ = function(_lV/* sg6A */, _lW/* sg6B */, _lX/* sg6C */){
  var _lY/* sg6D */ = E(_lV/* sg6A */);
  if(!_lY/* sg6D */._){
    return __Z/* EXTERNAL */;
  }else{
    var _lZ/* sg6G */ = E(_lW/* sg6B */);
    if(!_lZ/* sg6G */._){
      return __Z/* EXTERNAL */;
    }else{
      var _m0/* sg6H */ = _lZ/* sg6G */.a,
      _m1/* sg6J */ = E(_lX/* sg6C */);
      if(!_m1/* sg6J */._){
        return __Z/* EXTERNAL */;
      }else{
        var _m2/* sg6M */ = E(_m1/* sg6J */.a),
        _m3/* sg6N */ = _m2/* sg6M */.a;
        return new F(function(){return _f/* GHC.Base.++ */(new T2(1,new T(function(){
          return new T3(0,E(_lY/* sg6D */.a),E(_m0/* sg6H */),E(_m3/* sg6N */));
        }),new T2(1,new T(function(){
          return new T3(0,E(_m0/* sg6H */),E(_m3/* sg6N */),E(_m2/* sg6M */.b));
        }),_o/* GHC.Types.[] */)), new T(function(){
          return B(_lU/* Lib.Object.go1 */(_lY/* sg6D */.b, _lZ/* sg6G */.b, _m1/* sg6J */.b));
        },1));});
      }
    }
  }
},
_m4/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tail"));
}),
_m5/* tail1 */ = new T(function(){
  return B(_lQ/* GHC.List.errorEmptyList */(_m4/* GHC.List.lvl17 */));
}),
_m6/* zip */ = function(_m7/* sbOD */, _m8/* sbOE */){
  var _m9/* sbOF */ = E(_m7/* sbOD */);
  if(!_m9/* sbOF */._){
    return __Z/* EXTERNAL */;
  }else{
    var _ma/* sbOI */ = E(_m8/* sbOE */);
    return (_ma/* sbOI */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T2(0,_m9/* sbOF */.a,_ma/* sbOI */.a),new T(function(){
      return B(_m6/* GHC.List.zip */(_m9/* sbOF */.b, _ma/* sbOI */.b));
    }));
  }
},
_mb/* go2 */ = function(_mc/* sg7i */, _md/* sg7j */){
  var _me/* sg7k */ = E(_mc/* sg7i */);
  if(!_me/* sg7k */._){
    return __Z/* EXTERNAL */;
  }else{
    var _mf/* sg7n */ = E(_md/* sg7j */);
    if(!_mf/* sg7n */._){
      return __Z/* EXTERNAL */;
    }else{
      var _mg/* sg7q */ = E(_me/* sg7k */.a),
      _mh/* sg7s */ = _mg/* sg7q */.b,
      _mi/* sg7v */ = E(_mf/* sg7n */.a).b,
      _mj/* sg80 */ = new T(function(){
        var _mk/* sg7Z */ = new T(function(){
          return B(_m6/* GHC.List.zip */(_mi/* sg7v */, new T(function(){
            var _ml/* sg7V */ = E(_mi/* sg7v */);
            if(!_ml/* sg7V */._){
              return E(_m5/* GHC.List.tail1 */);
            }else{
              return E(_ml/* sg7V */.b);
            }
          },1)));
        },1);
        return B(_lU/* Lib.Object.go1 */(_mh/* sg7s */, new T(function(){
          var _mm/* sg7R */ = E(_mh/* sg7s */);
          if(!_mm/* sg7R */._){
            return E(_m5/* GHC.List.tail1 */);
          }else{
            return E(_mm/* sg7R */.b);
          }
        },1), _mk/* sg7Z */));
      });
      return new F(function(){return _f/* GHC.Base.++ */(new T2(1,new T(function(){
        var _mn/* sg7A */ = E(_mh/* sg7s */);
        if(!_mn/* sg7A */._){
          return E(_lT/* GHC.List.badHead */);
        }else{
          var _mo/* sg7I */ = E(_mi/* sg7v */);
          if(!_mo/* sg7I */._){
            return E(_lT/* GHC.List.badHead */);
          }else{
            return new T3(0,E(_mg/* sg7q */.a),E(_mn/* sg7A */.a),E(_mo/* sg7I */.a));
          }
        }
      }),_mj/* sg80 */), new T(function(){
        return B(_mb/* Lib.Object.go2 */(_me/* sg7k */.b, _mf/* sg7n */.b));
      },1));});
    }
  }
},
_mp/* lvl2 */ = new T(function(){
  return E(_lN/* Lib.Object.aN */)-1;
}),
_mq/* $fEnumRatio1 */ = new T1(0,1),
_mr/* $wnumericEnumFrom */ = function(_ms/* svpc */, _mt/* svpd */){
  var _mu/* svpe */ = E(_mt/* svpd */),
  _mv/* svpl */ = new T(function(){
    var _mw/* svpf */ = B(_7i/* GHC.Real.$p1Fractional */(_ms/* svpc */)),
    _mx/* svpi */ = B(_mr/* GHC.Real.$wnumericEnumFrom */(_ms/* svpc */, B(A3(_6I/* GHC.Num.+ */,_mw/* svpf */, _mu/* svpe */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_mw/* svpf */, _mq/* GHC.Real.$fEnumRatio1 */));
    })))));
    return new T2(1,_mx/* svpi */.a,_mx/* svpi */.b);
  });
  return new T2(0,_mu/* svpe */,_mv/* svpl */);
},
_my/* <= */ = function(_mz/* scCm */){
  return E(E(_mz/* scCm */).d);
},
_mA/* even2 */ = new T1(0,2),
_mB/* takeWhile */ = function(_mC/* sbJ5 */, _mD/* sbJ6 */){
  var _mE/* sbJ7 */ = E(_mD/* sbJ6 */);
  if(!_mE/* sbJ7 */._){
    return __Z/* EXTERNAL */;
  }else{
    var _mF/* sbJ8 */ = _mE/* sbJ7 */.a;
    return (!B(A1(_mC/* sbJ5 */,_mF/* sbJ8 */))) ? __Z/* EXTERNAL */ : new T2(1,_mF/* sbJ8 */,new T(function(){
      return B(_mB/* GHC.List.takeWhile */(_mC/* sbJ5 */, _mE/* sbJ7 */.b));
    }));
  }
},
_mG/* numericEnumFromTo */ = function(_mH/* svpS */, _mI/* svpT */, _mJ/* svpU */, _mK/* svpV */){
  var _mL/* svpW */ = B(_mr/* GHC.Real.$wnumericEnumFrom */(_mI/* svpT */, _mJ/* svpU */)),
  _mM/* svpZ */ = new T(function(){
    var _mN/* svq0 */ = B(_7i/* GHC.Real.$p1Fractional */(_mI/* svpT */)),
    _mO/* svq3 */ = new T(function(){
      return B(A3(_9b/* GHC.Real./ */,_mI/* svpT */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_mN/* svq0 */, _mq/* GHC.Real.$fEnumRatio1 */));
      }), new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_mN/* svq0 */, _mA/* GHC.Real.even2 */));
      })));
    });
    return B(A3(_6I/* GHC.Num.+ */,_mN/* svq0 */, _mK/* svpV */, _mO/* svq3 */));
  });
  return new F(function(){return _mB/* GHC.List.takeWhile */(function(_mP/* svq4 */){
    return new F(function(){return A3(_my/* GHC.Classes.<= */,_mH/* svpS */, _mP/* svq4 */, _mM/* svpZ */);});
  }, new T2(1,_mL/* svpW */.a,_mL/* svpW */.b));});
},
_mQ/* lvl3 */ = new T(function(){
  return B(_mG/* GHC.Real.numericEnumFromTo */(_jq/* GHC.Classes.$fOrdDouble */, _ip/* GHC.Float.$fFractionalDouble */, _hm/* Lib.Object.$fNumPos1 */, _mp/* Lib.Object.lvl2 */));
}),
_mR/* go */ = function(_mS/* sfW1 */, _mT/* sfW2 */){
  while(1){
    var _mU/* sfW3 */ = E(_mS/* sfW1 */);
    if(!_mU/* sfW3 */._){
      return E(_mT/* sfW2 */);
    }else{
      _mS/* sfW1 */ = _mU/* sfW3 */.b;
      _mT/* sfW2 */ = _mU/* sfW3 */.a;
      continue;
    }
  }
},
_mV/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_mW/* last1 */ = new T(function(){
  return B(_lQ/* GHC.List.errorEmptyList */(_mV/* GHC.List.lvl16 */));
}),
_mX/* $wlvl */ = function(_mY/* sfW6 */){
  return new F(function(){return _mR/* Lib.Object.go */(_mY/* sfW6 */, _mW/* GHC.List.last1 */);});
},
_mZ/* lvl4 */ = function(_n0/* sfW7 */){
  return new F(function(){return _mX/* Lib.Object.$wlvl */(E(_n0/* sfW7 */).b);});
},
_n1/* proceedCount */ = new T(function(){
  var _n2/* s6PS */ = eval/* EXTERNAL */("proceedCount"),
  _n3/* s6PW */ = Number/* EXTERNAL */(_n2/* s6PS */);
  return jsTrunc/* EXTERNAL */(_n3/* s6PW */);
}),
_n4/* pC */ = new T(function(){
  return E(_n1/* Lib.Util.proceedCount */);
}),
_n5/* $s^2 */ = 1,
_n6/* x */ = new T(function(){
  return B(_mG/* GHC.Real.numericEnumFromTo */(_jq/* GHC.Classes.$fOrdDouble */, _ip/* GHC.Float.$fFractionalDouble */, _n5/* Lib.Object.$s^2 */, _n4/* Lib.Object.pC */));
}),
_n7/* $wgeneratePolygon */ = function(_n8/* sg83 */, _n9/* sg84 */, _na/* sg85 */, _nb/* sg86 */, _nc/* sg87 */, _nd/* sg88 */, _ne/* sg89 */, _nf/* sg8a */, _ng/* sg8b */, _nh/* sg8c */, _ni/* sg8d */, _nj/* sg8e */, _nk/* sg8f */, _nl/* sg8g */){
  var _nm/* sg8h */ = new T(function(){
    var _nn/* sg8i */ = new T(function(){
      var _no/* sg8j */ = E(_nh/* sg8c */),
      _np/* sg8l */ = E(_nl/* sg8g */),
      _nq/* sg8n */ = E(_nk/* sg8f */),
      _nr/* sg8p */ = E(_ni/* sg8d */),
      _ns/* sg8r */ = E(_nj/* sg8e */),
      _nt/* sg8t */ = E(_ng/* sg8b */);
      return new T3(0,_no/* sg8j */*_np/* sg8l */-_nq/* sg8n */*_nr/* sg8p */,_nr/* sg8p */*_ns/* sg8r */-_np/* sg8l */*_nt/* sg8t */,_nt/* sg8t */*_nq/* sg8n */-_ns/* sg8r */*_no/* sg8j */);
    }),
    _nu/* sgdc */ = function(_nv/* sg8I */){
      var _nw/* sg8J */ = new T(function(){
        var _nx/* sg8O */ = E(_nv/* sg8I */)/E(_lN/* Lib.Object.aN */);
        return (_nx/* sg8O */+_nx/* sg8O */)*3.141592653589793;
      }),
      _ny/* sg8R */ = new T(function(){
        return B(A1(_n8/* sg83 */,_nw/* sg8J */));
      }),
      _nz/* sgdb */ = new T(function(){
        var _nA/* sg8Y */ = new T(function(){
          var _nB/* sg93 */ = E(_ny/* sg8R */)/E(_n4/* Lib.Object.pC */);
          return new T3(0,E(_nB/* sg93 */),E(_nB/* sg93 */),E(_nB/* sg93 */));
        }),
        _nC/* sg96 */ = function(_nD/* sgaO */, _nE/* sgaP */){
          var _nF/* sgaQ */ = E(_nD/* sgaO */);
          if(!_nF/* sgaQ */._){
            return new T2(0,_o/* GHC.Types.[] */,_nE/* sgaP */);
          }else{
            var _nG/* sgaT */ = new T(function(){
              var _nH/* sgbB */ = B(_kI/* Lib.World.$wfitP */(_k8/* Lib.Object.$sfitP1 */, new T(function(){
                var _nI/* sgaU */ = E(_nE/* sgaP */),
                _nJ/* sgaX */ = E(_nI/* sgaU */.a),
                _nK/* sgb7 */ = E(_nI/* sgaU */.b),
                _nL/* sgbh */ = E(_nA/* sg8Y */);
                return new T3(0,E(_nJ/* sgaX */.a)+E(_nK/* sgb7 */.a)*E(_nL/* sgbh */.a),E(_nJ/* sgaX */.b)+E(_nK/* sgb7 */.b)*E(_nL/* sgbh */.b),E(_nJ/* sgaX */.c)+E(_nK/* sgb7 */.c)*E(_nL/* sgbh */.c));
              }))),
              _nM/* sgbC */ = _nH/* sgbB */.a;
              return new T2(0,new T(function(){
                var _nN/* sgbM */ = E(_ny/* sg8R */),
                _nO/* sgbO */ = E(_nw/* sg8J */);
                return new T3(0,E(_nM/* sgbC */),E(new T2(0,E(_nF/* sgaQ */.a)/E(_n4/* Lib.Object.pC */),E(_nN/* sgbM */))),E(_nO/* sgbO */));
              }),new T2(0,_nM/* sgbC */,new T(function(){
                var _nP/* sgbX */ = E(_nH/* sgbB */.b),
                _nQ/* sgc1 */ = E(E(_nE/* sgaP */).b),
                _nR/* sgc5 */ = B(_l9/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _nQ/* sgc1 */.a, _nQ/* sgc1 */.b, _nQ/* sgc1 */.c, _nP/* sgbX */.a, _nP/* sgbX */.b, _nP/* sgbX */.c)),
                _nS/* sgc9 */ = B(_kj/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _nR/* sgc5 */.a, _nR/* sgc5 */.b, _nR/* sgc5 */.c));
                return new T3(0,E(_nS/* sgc9 */.a),E(_nS/* sgc9 */.b),E(_nS/* sgc9 */.c));
              })));
            }),
            _nT/* sgcf */ = new T(function(){
              var _nU/* sgck */ = B(_nC/* sg96 */(_nF/* sgaQ */.b, new T(function(){
                return E(E(_nG/* sgaT */).b);
              })));
              return new T2(0,_nU/* sgck */.a,_nU/* sgck */.b);
            });
            return new T2(0,new T2(1,new T(function(){
              return E(E(_nG/* sgaT */).a);
            }),new T(function(){
              return E(E(_nT/* sgcf */).a);
            })),new T(function(){
              return E(E(_nT/* sgcf */).b);
            }));
          }
        },
        _nV/* sg95 */ = function(_nW/* sg97 */, _nX/* sg98 */, _nY/* sg99 */, _nZ/* sg9a */, _o0/* sg9b */){
          var _o1/* sg9c */ = E(_nW/* sg97 */);
          if(!_o1/* sg9c */._){
            return new T2(0,_o/* GHC.Types.[] */,new T2(0,new T3(0,E(_nX/* sg98 */),E(_nY/* sg99 */),E(_nZ/* sg9a */)),_o0/* sg9b */));
          }else{
            var _o2/* sg9h */ = new T(function(){
              var _o3/* sg9S */ = B(_kI/* Lib.World.$wfitP */(_k8/* Lib.Object.$sfitP1 */, new T(function(){
                var _o4/* sg9o */ = E(_o0/* sg9b */),
                _o5/* sg9y */ = E(_nA/* sg8Y */);
                return new T3(0,E(_nX/* sg98 */)+E(_o4/* sg9o */.a)*E(_o5/* sg9y */.a),E(_nY/* sg99 */)+E(_o4/* sg9o */.b)*E(_o5/* sg9y */.b),E(_nZ/* sg9a */)+E(_o4/* sg9o */.c)*E(_o5/* sg9y */.c));
              }))),
              _o6/* sg9T */ = _o3/* sg9S */.a;
              return new T2(0,new T(function(){
                var _o7/* sga3 */ = E(_ny/* sg8R */),
                _o8/* sga5 */ = E(_nw/* sg8J */);
                return new T3(0,E(_o6/* sg9T */),E(new T2(0,E(_o1/* sg9c */.a)/E(_n4/* Lib.Object.pC */),E(_o7/* sga3 */))),E(_o8/* sga5 */));
              }),new T2(0,_o6/* sg9T */,new T(function(){
                var _o9/* sgab */ = E(_o3/* sg9S */.b),
                _oa/* sgaf */ = E(_o0/* sg9b */),
                _ob/* sgaj */ = B(_l9/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _oa/* sgaf */.a, _oa/* sgaf */.b, _oa/* sgaf */.c, _o9/* sgab */.a, _o9/* sgab */.b, _o9/* sgab */.c)),
                _oc/* sgan */ = B(_kj/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _ob/* sgaj */.a, _ob/* sgaj */.b, _ob/* sgaj */.c));
                return new T3(0,E(_oc/* sgan */.a),E(_oc/* sgan */.b),E(_oc/* sgan */.c));
              })));
            }),
            _od/* sgat */ = new T(function(){
              var _oe/* sgay */ = B(_nC/* sg96 */(_o1/* sg9c */.b, new T(function(){
                return E(E(_o2/* sg9h */).b);
              })));
              return new T2(0,_oe/* sgay */.a,_oe/* sgay */.b);
            });
            return new T2(0,new T2(1,new T(function(){
              return E(E(_o2/* sg9h */).a);
            }),new T(function(){
              return E(E(_od/* sgat */).a);
            })),new T(function(){
              return E(E(_od/* sgat */).b);
            }));
          }
        };
        return E(B(_nV/* sg95 */(_n6/* Lib.Object.x */, _nb/* sg86 */, _nc/* sg87 */, _nd/* sg88 */, new T(function(){
          var _of/* sgcI */ = E(_nn/* sg8i */),
          _og/* sgcS */ = E(_nw/* sg8J */)+_ne/* sg89 */,
          _oh/* sgcT */ = Math.cos/* EXTERNAL */(_og/* sgcS */),
          _oi/* sgcU */ = Math.sin/* EXTERNAL */(_og/* sgcS */);
          return new T3(0,E(_ng/* sg8b */)*_oh/* sgcT */+E(_of/* sgcI */.a)*_oi/* sgcU */,E(_nh/* sg8c */)*_oh/* sgcT */+E(_of/* sgcI */.b)*_oi/* sgcU */,E(_ni/* sg8d */)*_oh/* sgcT */+E(_of/* sgcI */.c)*_oi/* sgcU */);
        }))).a);
      });
      return new T2(0,new T(function(){
        var _oj/* sg8S */ = E(_ny/* sg8R */),
        _ok/* sg8U */ = E(_nw/* sg8J */);
        return new T3(0,E(new T3(0,E(_nb/* sg86 */),E(_nc/* sg87 */),E(_nd/* sg88 */))),E(new T2(0,E(_hm/* Lib.Object.$fNumPos1 */),E(_oj/* sg8S */))),E(_ok/* sg8U */));
      }),_nz/* sgdb */);
    };
    return B(_jW/* GHC.Base.map */(_nu/* sgdc */, _mQ/* Lib.Object.lvl3 */));
  }),
  _ol/* sgdm */ = new T(function(){
    var _om/* sgdl */ = new T(function(){
      var _on/* sgdi */ = B(_f/* GHC.Base.++ */(_nm/* sg8h */, new T2(1,new T(function(){
        var _oo/* sgdd */ = E(_nm/* sg8h */);
        if(!_oo/* sgdd */._){
          return E(_lT/* GHC.List.badHead */);
        }else{
          return E(_oo/* sgdd */.a);
        }
      }),_o/* GHC.Types.[] */)));
      if(!_on/* sgdi */._){
        return E(_m5/* GHC.List.tail1 */);
      }else{
        return E(_on/* sgdi */.b);
      }
    },1);
    return B(_mb/* Lib.Object.go2 */(_nm/* sg8h */, _om/* sgdl */));
  });
  return new T2(0,_ol/* sgdm */,new T(function(){
    return B(_jW/* GHC.Base.map */(_mZ/* Lib.Object.lvl4 */, _nm/* sg8h */));
  }));
},
_op/* $wfitO */ = function(_oq/* sgnu */, _or/* sgnv */, _os/* sgnw */, _ot/* sgnx */, _ou/* sgny */, _ov/* sgnz */, _ow/* sgnA */, _ox/* sgnB */, _oy/* sgnC */, _oz/* sgnD */, _oA/* sgnE */, _oB/* sgnF */, _oC/* sgnG */, _oD/* sgnH */, _oE/* sgnI */, _oF/* sgnJ */, _oG/* sgnK */){
  var _oH/* sgnM */ = B(_kI/* Lib.World.$wfitP */(_k8/* Lib.Object.$sfitP1 */, new T3(0,E(_ot/* sgnx */),E(_ou/* sgny */),E(_ov/* sgnz */)))),
  _oI/* sgnO */ = _oH/* sgnM */.b,
  _oJ/* sgnP */ = E(_oH/* sgnM */.a),
  _oK/* sgnU */ = B(_ln/* Lib.World.$wfitV */(_iR/* GHC.Float.$fFloatingDouble */, _jq/* GHC.Classes.$fOrdDouble */, _oI/* sgnO */, new T3(0,E(_ox/* sgnB */),E(_oy/* sgnC */),E(_oz/* sgnD */)))),
  _oL/* sgnY */ = E(_oI/* sgnO */),
  _oM/* sgnZ */ = _oL/* sgnY */.a,
  _oN/* sgo0 */ = _oL/* sgnY */.b,
  _oO/* sgo1 */ = _oL/* sgnY */.c,
  _oP/* sgo2 */ = B(_l9/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _oB/* sgnF */, _oC/* sgnG */, _oD/* sgnH */, _oM/* sgnZ */, _oN/* sgo0 */, _oO/* sgo1 */)),
  _oQ/* sgo6 */ = B(_kj/* Lib.World.$w$cnormalize */(_iR/* GHC.Float.$fFloatingDouble */, _oP/* sgo2 */.a, _oP/* sgo2 */.b, _oP/* sgo2 */.c)),
  _oR/* sgo7 */ = _oQ/* sgo6 */.a,
  _oS/* sgo8 */ = _oQ/* sgo6 */.b,
  _oT/* sgo9 */ = _oQ/* sgo6 */.c,
  _oU/* sgoa */ = E(_ow/* sgnA */),
  _oV/* sgod */ = new T2(0,E(new T3(0,E(_oK/* sgnU */.a),E(_oK/* sgnU */.b),E(_oK/* sgnU */.c))),E(_oA/* sgnE */)),
  _oW/* sgoe */ = B(_n7/* Lib.Object.$wgeneratePolygon */(_oq/* sgnu */, _or/* sgnv */, _os/* sgnw */, _oJ/* sgnP */.a, _oJ/* sgnP */.b, _oJ/* sgnP */.c, _oU/* sgoa */, _oV/* sgod */, _oR/* sgo7 */, _oS/* sgo8 */, _oT/* sgo9 */, _oM/* sgnZ */, _oN/* sgo0 */, _oO/* sgo1 */)),
  _oX/* sgok */ = __lst2arr/* EXTERNAL */(B(_jW/* GHC.Base.map */(_k5/* Lib.Object.$fToAnyPolygon_$ctoAny */, _oW/* sgoe */.a))),
  _oY/* sgoq */ = __lst2arr/* EXTERNAL */(B(_jW/* GHC.Base.map */(_jR/* Lib.Object.$fToAnyPolygon_$ctoAny1 */, _oW/* sgoe */.b)));
  return {_:0,a:_oq/* sgnu */,b:_or/* sgnv */,c:_os/* sgnw */,d:new T2(0,E(_oJ/* sgnP */),E(_oU/* sgoa */)),e:_oV/* sgod */,f:new T3(0,E(_oR/* sgo7 */),E(_oS/* sgo8 */),E(_oT/* sgo9 */)),g:_oL/* sgnY */,h:_oX/* sgok */,i:_oY/* sgoq */};
},
_oZ/* lvl1 */ = new T(function(){
  return 6.283185307179586/E(_lN/* Lib.Object.aN */);
}),
_p0/* dt */ =  -1,
_p1/* dt1 */ = 0.5,
_p2/* lvl26 */ = new T3(0,E(_hm/* Lib.Object.$fNumPos1 */),E(_p1/* Lib.Object.dt1 */),E(_p0/* Lib.Object.dt */)),
_p3/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_p4/* unsafeDupablePerformIO */ = function(_p5/* s2YSa */){
  var _p6/* s2YSb */ = B(A1(_p5/* s2YSa */,_/* EXTERNAL */));
  return E(_p6/* s2YSb */);
},
_p7/* nullValue */ = new T(function(){
  return B(_p4/* GHC.IO.unsafeDupablePerformIO */(_p3/* Haste.Prim.Any.lvl2 */));
}),
_p8/* $wmake */ = function(_p9/* sgz0 */, _pa/* sgz1 */, _pb/* sgz2 */, _pc/* sgz3 */, _pd/* sgz4 */, _pe/* sgz5 */, _pf/* sgz6 */, _pg/* sgz7 */, _ph/* sgz8 */, _pi/* sgz9 */, _pj/* sgza */, _pk/* sgzb */, _pl/* sgzc */){
  var _pm/* sgzd */ = function(_pn/* sgze */){
    var _po/* sgzf */ = E(_oZ/* Lib.Object.lvl1 */),
    _pp/* sgzh */ = 2+_pn/* sgze */|0,
    _pq/* sgzj */ = _pp/* sgzh */-1|0,
    _pr/* sgzk */ = (2+_pn/* sgze */)*(1+_pn/* sgze */),
    _ps/* sgzp */ = E(_mQ/* Lib.Object.lvl3 */);
    if(!_ps/* sgzp */._){
      return _po/* sgzf */*0;
    }else{
      var _pt/* sgzq */ = _ps/* sgzp */.a,
      _pu/* sgzr */ = _ps/* sgzp */.b,
      _pv/* sgzz */ = B(A1(_p9/* sgz0 */,new T(function(){
        return 6.283185307179586*E(_pt/* sgzq */)/E(_lN/* Lib.Object.aN */);
      }))),
      _pw/* sgzJ */ = B(A1(_p9/* sgz0 */,new T(function(){
        return 6.283185307179586*(E(_pt/* sgzq */)+1)/E(_lN/* Lib.Object.aN */);
      })));
      if(_pv/* sgzz */!=_pw/* sgzJ */){
        if(_pp/* sgzh */>=0){
          var _px/* sgzP */ = E(_pp/* sgzh */);
          if(!_px/* sgzP */){
            var _py/* sgAL */ = function(_pz/*  sgAM */, _pA/*  sgAN */){
              while(1){
                var _pB/*  sgAL */ = B((function(_pC/* sgAM */, _pD/* sgAN */){
                  var _pE/* sgAO */ = E(_pC/* sgAM */);
                  if(!_pE/* sgAO */._){
                    return E(_pD/* sgAN */);
                  }else{
                    var _pF/* sgAP */ = _pE/* sgAO */.a,
                    _pG/* sgAQ */ = _pE/* sgAO */.b,
                    _pH/* sgAY */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*E(_pF/* sgAP */)/E(_lN/* Lib.Object.aN */);
                    }))),
                    _pI/* sgB8 */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*(E(_pF/* sgAP */)+1)/E(_lN/* Lib.Object.aN */);
                    })));
                    if(_pH/* sgAY */!=_pI/* sgB8 */){
                      var _pJ/*   sgAN */ = _pD/* sgAN */+0/(_pH/* sgAY */-_pI/* sgB8 */)/_pr/* sgzk */;
                      _pz/*  sgAM */ = _pG/* sgAQ */;
                      _pA/*  sgAN */ = _pJ/*   sgAN */;
                      return __continue/* EXTERNAL */;
                    }else{
                      if(_pq/* sgzj */>=0){
                        var _pK/* sgBi */ = E(_pq/* sgzj */);
                        if(!_pK/* sgBi */){
                          var _pJ/*   sgAN */ = _pD/* sgAN */+_pp/* sgzh *//_pr/* sgzk */;
                          _pz/*  sgAM */ = _pG/* sgAQ */;
                          _pA/*  sgAN */ = _pJ/*   sgAN */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _pJ/*   sgAN */ = _pD/* sgAN */+_pp/* sgzh */*B(_hy/* Lib.Object.$wf */(_pH/* sgAY */, _pK/* sgBi */))/_pr/* sgzk */;
                          _pz/*  sgAM */ = _pG/* sgAQ */;
                          _pA/*  sgAN */ = _pJ/*   sgAN */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_pz/*  sgAM */, _pA/*  sgAN */));
                if(_pB/*  sgAL */!=__continue/* EXTERNAL */){
                  return _pB/*  sgAL */;
                }
              }
            };
            return _po/* sgzf */*B(_py/* sgAL */(_pu/* sgzr */, 0/(_pv/* sgzz */-_pw/* sgzJ */)/_pr/* sgzk */));
          }else{
            var _pL/* sgzW */ = function(_pM/*  sgzX */, _pN/*  sgzY */){
              while(1){
                var _pO/*  sgzW */ = B((function(_pP/* sgzX */, _pQ/* sgzY */){
                  var _pR/* sgzZ */ = E(_pP/* sgzX */);
                  if(!_pR/* sgzZ */._){
                    return E(_pQ/* sgzY */);
                  }else{
                    var _pS/* sgA0 */ = _pR/* sgzZ */.a,
                    _pT/* sgA1 */ = _pR/* sgzZ */.b,
                    _pU/* sgA9 */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*E(_pS/* sgA0 */)/E(_lN/* Lib.Object.aN */);
                    }))),
                    _pV/* sgAj */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*(E(_pS/* sgA0 */)+1)/E(_lN/* Lib.Object.aN */);
                    })));
                    if(_pU/* sgA9 */!=_pV/* sgAj */){
                      if(_px/* sgzP */>=0){
                        var _pW/*   sgzY */ = _pQ/* sgzY */+(B(_hy/* Lib.Object.$wf */(_pU/* sgA9 */, _px/* sgzP */))-B(_hy/* Lib.Object.$wf */(_pV/* sgAj */, _px/* sgzP */)))/(_pU/* sgA9 */-_pV/* sgAj */)/_pr/* sgzk */;
                        _pM/*  sgzX */ = _pT/* sgA1 */;
                        _pN/*  sgzY */ = _pW/*   sgzY */;
                        return __continue/* EXTERNAL */;
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }else{
                      if(_pq/* sgzj */>=0){
                        var _pX/* sgAz */ = E(_pq/* sgzj */);
                        if(!_pX/* sgAz */){
                          var _pW/*   sgzY */ = _pQ/* sgzY */+_pp/* sgzh *//_pr/* sgzk */;
                          _pM/*  sgzX */ = _pT/* sgA1 */;
                          _pN/*  sgzY */ = _pW/*   sgzY */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _pW/*   sgzY */ = _pQ/* sgzY */+_pp/* sgzh */*B(_hy/* Lib.Object.$wf */(_pU/* sgA9 */, _pX/* sgAz */))/_pr/* sgzk */;
                          _pM/*  sgzX */ = _pT/* sgA1 */;
                          _pN/*  sgzY */ = _pW/*   sgzY */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_pM/*  sgzX */, _pN/*  sgzY */));
                if(_pO/*  sgzW */!=__continue/* EXTERNAL */){
                  return _pO/*  sgzW */;
                }
              }
            };
            return _po/* sgzf */*B(_pL/* sgzW */(_pu/* sgzr */, (B(_hy/* Lib.Object.$wf */(_pv/* sgzz */, _px/* sgzP */))-B(_hy/* Lib.Object.$wf */(_pw/* sgzJ */, _px/* sgzP */)))/(_pv/* sgzz */-_pw/* sgzJ */)/_pr/* sgzk */));
          }
        }else{
          return E(_hp/* Lib.Object.$s^1 */);
        }
      }else{
        if(_pq/* sgzj */>=0){
          var _pY/* sgBu */ = E(_pq/* sgzj */);
          if(!_pY/* sgBu */){
            var _pZ/* sgCn */ = function(_q0/*  sgCo */, _q1/*  sgCp */){
              while(1){
                var _q2/*  sgCn */ = B((function(_q3/* sgCo */, _q4/* sgCp */){
                  var _q5/* sgCq */ = E(_q3/* sgCo */);
                  if(!_q5/* sgCq */._){
                    return E(_q4/* sgCp */);
                  }else{
                    var _q6/* sgCr */ = _q5/* sgCq */.a,
                    _q7/* sgCs */ = _q5/* sgCq */.b,
                    _q8/* sgCA */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*E(_q6/* sgCr */)/E(_lN/* Lib.Object.aN */);
                    }))),
                    _q9/* sgCK */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*(E(_q6/* sgCr */)+1)/E(_lN/* Lib.Object.aN */);
                    })));
                    if(_q8/* sgCA */!=_q9/* sgCK */){
                      if(_pp/* sgzh */>=0){
                        var _qa/* sgCQ */ = E(_pp/* sgzh */);
                        if(!_qa/* sgCQ */){
                          var _qb/*   sgCp */ = _q4/* sgCp */+0/(_q8/* sgCA */-_q9/* sgCK */)/_pr/* sgzk */;
                          _q0/*  sgCo */ = _q7/* sgCs */;
                          _q1/*  sgCp */ = _qb/*   sgCp */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _qb/*   sgCp */ = _q4/* sgCp */+(B(_hy/* Lib.Object.$wf */(_q8/* sgCA */, _qa/* sgCQ */))-B(_hy/* Lib.Object.$wf */(_q9/* sgCK */, _qa/* sgCQ */)))/(_q8/* sgCA */-_q9/* sgCK */)/_pr/* sgzk */;
                          _q0/*  sgCo */ = _q7/* sgCs */;
                          _q1/*  sgCp */ = _qb/*   sgCp */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }else{
                      var _qb/*   sgCp */ = _q4/* sgCp */+_pp/* sgzh *//_pr/* sgzk */;
                      _q0/*  sgCo */ = _q7/* sgCs */;
                      _q1/*  sgCp */ = _qb/*   sgCp */;
                      return __continue/* EXTERNAL */;
                    }
                  }
                })(_q0/*  sgCo */, _q1/*  sgCp */));
                if(_q2/*  sgCn */!=__continue/* EXTERNAL */){
                  return _q2/*  sgCn */;
                }
              }
            };
            return _po/* sgzf */*B(_pZ/* sgCn */(_pu/* sgzr */, _pp/* sgzh *//_pr/* sgzk */));
          }else{
            var _qc/* sgBy */ = function(_qd/*  sgBz */, _qe/*  sgBA */){
              while(1){
                var _qf/*  sgBy */ = B((function(_qg/* sgBz */, _qh/* sgBA */){
                  var _qi/* sgBB */ = E(_qg/* sgBz */);
                  if(!_qi/* sgBB */._){
                    return E(_qh/* sgBA */);
                  }else{
                    var _qj/* sgBC */ = _qi/* sgBB */.a,
                    _qk/* sgBD */ = _qi/* sgBB */.b,
                    _ql/* sgBL */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*E(_qj/* sgBC */)/E(_lN/* Lib.Object.aN */);
                    }))),
                    _qm/* sgBV */ = B(A1(_p9/* sgz0 */,new T(function(){
                      return 6.283185307179586*(E(_qj/* sgBC */)+1)/E(_lN/* Lib.Object.aN */);
                    })));
                    if(_ql/* sgBL */!=_qm/* sgBV */){
                      if(_pp/* sgzh */>=0){
                        var _qn/* sgC1 */ = E(_pp/* sgzh */);
                        if(!_qn/* sgC1 */){
                          var _qo/*   sgBA */ = _qh/* sgBA */+0/(_ql/* sgBL */-_qm/* sgBV */)/_pr/* sgzk */;
                          _qd/*  sgBz */ = _qk/* sgBD */;
                          _qe/*  sgBA */ = _qo/*   sgBA */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _qo/*   sgBA */ = _qh/* sgBA */+(B(_hy/* Lib.Object.$wf */(_ql/* sgBL */, _qn/* sgC1 */))-B(_hy/* Lib.Object.$wf */(_qm/* sgBV */, _qn/* sgC1 */)))/(_ql/* sgBL */-_qm/* sgBV */)/_pr/* sgzk */;
                          _qd/*  sgBz */ = _qk/* sgBD */;
                          _qe/*  sgBA */ = _qo/*   sgBA */;
                          return __continue/* EXTERNAL */;
                        }
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }else{
                      if(_pY/* sgBu */>=0){
                        var _qo/*   sgBA */ = _qh/* sgBA */+_pp/* sgzh */*B(_hy/* Lib.Object.$wf */(_ql/* sgBL */, _pY/* sgBu */))/_pr/* sgzk */;
                        _qd/*  sgBz */ = _qk/* sgBD */;
                        _qe/*  sgBA */ = _qo/*   sgBA */;
                        return __continue/* EXTERNAL */;
                      }else{
                        return E(_hp/* Lib.Object.$s^1 */);
                      }
                    }
                  }
                })(_qd/*  sgBz */, _qe/*  sgBA */));
                if(_qf/*  sgBy */!=__continue/* EXTERNAL */){
                  return _qf/*  sgBy */;
                }
              }
            };
            return _po/* sgzf */*B(_qc/* sgBy */(_pu/* sgzr */, _pp/* sgzh */*B(_hy/* Lib.Object.$wf */(_pv/* sgzz */, _pY/* sgBu */))/_pr/* sgzk */));
          }
        }else{
          return E(_hp/* Lib.Object.$s^1 */);
        }
      }
    }
  },
  _qp/* sgD9 */ = E(_p7/* Haste.Prim.Any.nullValue */),
  _qq/* sgDc */ = 1/(B(_pm/* sgzd */(1))*_pa/* sgz1 */);
  return new F(function(){return _op/* Lib.Object.$wfitO */(_p9/* sgz0 */, _p2/* Lib.Object.lvl26 */, new T2(0,E(new T3(0,E(_qq/* sgDc */),E(_qq/* sgDc */),E(_qq/* sgDc */))),1/(B(_pm/* sgzd */(3))*_pa/* sgz1 */)), _pb/* sgz2 */, _pc/* sgz3 */, _pd/* sgz4 */, _pe/* sgz5 */, _pf/* sgz6 */, _pg/* sgz7 */, _ph/* sgz8 */, _pi/* sgz9 */, _pj/* sgza */, _pk/* sgzb */, _pl/* sgzc */, _hn/* Lib.Object.$fNumPos2 */, _qp/* sgD9 */, _qp/* sgD9 */);});
},
_qr/* initial11 */ = 0,
_qs/* initial15 */ =  -0.2,
_qt/* initial16 */ = 0.5,
_qu/* initial17 */ =  -0.8,
_qv/* initial_r */ = 0.2,
_qw/* initial18 */ = function(_qx/* szce */){
  return E(_qv/* Main.initial_r */);
},
_qy/* initial7 */ = 1,
_qz/* initial14 */ = new T(function(){
  var _qA/* szcf */ = B(_p8/* Lib.Object.$wmake */(_qw/* Main.initial18 */, 1.2, _qu/* Main.initial17 */, _qt/* Main.initial16 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qs/* Main.initial15 */, _qr/* Main.initial11 */, _qy/* Main.initial7 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qy/* Main.initial7 */));
  return {_:0,a:E(_qA/* szcf */.a),b:E(_qA/* szcf */.b),c:E(_qA/* szcf */.c),d:E(_qA/* szcf */.d),e:E(_qA/* szcf */.e),f:E(_qA/* szcf */.f),g:E(_qA/* szcf */.g),h:_qA/* szcf */.h,i:_qA/* szcf */.i};
}),
_qB/* initial4 */ = 0,
_qC/* initial10 */ =  -0.1,
_qD/* initial12 */ = 1.3,
_qE/* decodeDoubleInteger */ = function(_qF/* s1ID */){
  var _qG/* s1IF */ = I_decodeDouble/* EXTERNAL */(_qF/* s1ID */);
  return new T2(0,new T1(1,_qG/* s1IF */.b),_qG/* s1IF */.a);
},
_qH/* smallInteger */ = function(_qI/* B1 */){
  return new T1(0,_qI/* B1 */);
},
_qJ/* int64ToInteger */ = function(_qK/* s1RA */){
  var _qL/* s1RC */ = hs_intToInt64/* EXTERNAL */(2147483647),
  _qM/* s1RG */ = hs_leInt64/* EXTERNAL */(_qK/* s1RA */, _qL/* s1RC */);
  if(!_qM/* s1RG */){
    return new T1(1,I_fromInt64/* EXTERNAL */(_qK/* s1RA */));
  }else{
    var _qN/* s1RN */ = hs_intToInt64/* EXTERNAL */( -2147483648),
    _qO/* s1RR */ = hs_geInt64/* EXTERNAL */(_qK/* s1RA */, _qN/* s1RN */);
    if(!_qO/* s1RR */){
      return new T1(1,I_fromInt64/* EXTERNAL */(_qK/* s1RA */));
    }else{
      var _qP/* s1RY */ = hs_int64ToInt/* EXTERNAL */(_qK/* s1RA */);
      return new F(function(){return _qH/* GHC.Integer.Type.smallInteger */(_qP/* s1RY */);});
    }
  }
},
_qQ/* zeroCountArr */ = new T(function(){
  var _qR/* s9bR */ = newByteArr/* EXTERNAL */(256),
  _qS/* s9bT */ = _qR/* s9bR */,
  _/* EXTERNAL */ = _qS/* s9bT */["v"]["i8"][0] = 8,
  _qT/* s9bV */ = function(_qU/* s9bW */, _qV/* s9bX */, _qW/* s9bY */, _/* EXTERNAL */){
    while(1){
      if(_qW/* s9bY */>=256){
        if(_qU/* s9bW */>=256){
          return E(_/* EXTERNAL */);
        }else{
          var _qX/*  s9bW */ = imul/* EXTERNAL */(2, _qU/* s9bW */)|0,
          _qY/*  s9bX */ = _qV/* s9bX */+1|0,
          _qZ/*  s9bY */ = _qU/* s9bW */;
          _qU/* s9bW */ = _qX/*  s9bW */;
          _qV/* s9bX */ = _qY/*  s9bX */;
          _qW/* s9bY */ = _qZ/*  s9bY */;
          continue;
        }
      }else{
        var _/* EXTERNAL */ = _qS/* s9bT */["v"]["i8"][_qW/* s9bY */] = _qV/* s9bX */,
        _qZ/*  s9bY */ = _qW/* s9bY */+_qU/* s9bW */|0;
        _qW/* s9bY */ = _qZ/*  s9bY */;
        continue;
      }
    }
  },
  _/* EXTERNAL */ = B(_qT/* s9bV */(2, 0, 1, _/* EXTERNAL */));
  return _qS/* s9bT */;
}),
_r0/* elim64# */ = function(_r1/* s9cN */, _r2/* s9cO */){
  var _r3/* s9cQ */ = hs_int64ToInt/* EXTERNAL */(_r1/* s9cN */),
  _r4/* s9cT */ = E(_qQ/* GHC.Float.ConversionUtils.zeroCountArr */),
  _r5/* s9cY */ = _r4/* s9cT */["v"]["i8"][(255&_r3/* s9cQ */>>>0)>>>0&4294967295];
  if(_r2/* s9cO */>_r5/* s9cY */){
    if(_r5/* s9cY */>=8){
      var _r6/* s9d4 */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_r1/* s9cN */, 8),
      _r7/* s9d7 */ = function(_r8/*  s9d8 */, _r9/*  s9d9 */){
        while(1){
          var _ra/*  s9d7 */ = B((function(_rb/* s9d8 */, _rc/* s9d9 */){
            var _rd/* s9db */ = hs_int64ToInt/* EXTERNAL */(_rb/* s9d8 */),
            _re/* s9dh */ = _r4/* s9cT */["v"]["i8"][(255&_rd/* s9db */>>>0)>>>0&4294967295];
            if(_rc/* s9d9 */>_re/* s9dh */){
              if(_re/* s9dh */>=8){
                var _rf/* s9dn */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_rb/* s9d8 */, 8),
                _rg/*   s9d9 */ = _rc/* s9d9 */-8|0;
                _r8/*  s9d8 */ = _rf/* s9dn */;
                _r9/*  s9d9 */ = _rg/*   s9d9 */;
                return __continue/* EXTERNAL */;
              }else{
                return new T2(0,new T(function(){
                  var _rh/* s9ds */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_rb/* s9d8 */, _re/* s9dh */);
                  return B(_qJ/* GHC.Integer.Type.int64ToInteger */(_rh/* s9ds */));
                }),_rc/* s9d9 */-_re/* s9dh */|0);
              }
            }else{
              return new T2(0,new T(function(){
                var _ri/* s9dy */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_rb/* s9d8 */, _rc/* s9d9 */);
                return B(_qJ/* GHC.Integer.Type.int64ToInteger */(_ri/* s9dy */));
              }),0);
            }
          })(_r8/*  s9d8 */, _r9/*  s9d9 */));
          if(_ra/*  s9d7 */!=__continue/* EXTERNAL */){
            return _ra/*  s9d7 */;
          }
        }
      };
      return new F(function(){return _r7/* s9d7 */(_r6/* s9d4 */, _r2/* s9cO */-8|0);});
    }else{
      return new T2(0,new T(function(){
        var _rj/* s9dE */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_r1/* s9cN */, _r5/* s9cY */);
        return B(_qJ/* GHC.Integer.Type.int64ToInteger */(_rj/* s9dE */));
      }),_r2/* s9cO */-_r5/* s9cY */|0);
    }
  }else{
    return new T2(0,new T(function(){
      var _rk/* s9dK */ = hs_uncheckedIShiftRA64/* EXTERNAL */(_r1/* s9cN */, _r2/* s9cO */);
      return B(_qJ/* GHC.Integer.Type.int64ToInteger */(_rk/* s9dK */));
    }),0);
  }
},
_rl/* intToInt64# */ = function(_rm/* sf6 */){
  var _rn/* sf8 */ = hs_intToInt64/* EXTERNAL */(_rm/* sf6 */);
  return E(_rn/* sf8 */);
},
_ro/* integerToInt64 */ = function(_rp/* s1S1 */){
  var _rq/* s1S2 */ = E(_rp/* s1S1 */);
  if(!_rq/* s1S2 */._){
    return new F(function(){return _rl/* GHC.IntWord64.intToInt64# */(_rq/* s1S2 */.a);});
  }else{
    return new F(function(){return I_toInt64/* EXTERNAL */(_rq/* s1S2 */.a);});
  }
},
_rr/* integer2Word# */ = function(_rs/* s2C */){
  return I_toInt/* EXTERNAL */(_rs/* s2C */)>>>0;
},
_rt/* integerToWord */ = function(_ru/* s1Rr */){
  var _rv/* s1Rs */ = E(_ru/* s1Rr */);
  if(!_rv/* s1Rs */._){
    return _rv/* s1Rs */.a>>>0;
  }else{
    return new F(function(){return _rr/* GHC.Integer.GMP.Prim.integer2Word# */(_rv/* s1Rs */.a);});
  }
},
_rw/* $w$ctoRational */ = function(_rx/* s1l6D */){
  var _ry/* s1l6E */ = B(_qE/* GHC.Integer.Type.decodeDoubleInteger */(_rx/* s1l6D */)),
  _rz/* s1l6F */ = _ry/* s1l6E */.a,
  _rA/* s1l6G */ = _ry/* s1l6E */.b;
  if(_rA/* s1l6G */<0){
    var _rB/* s1l6K */ = function(_rC/* s1l6L */){
      if(!_rC/* s1l6L */){
        return new T2(0,E(_rz/* s1l6F */),B(_3u/* GHC.Integer.Type.shiftLInteger */(_1M/* GHC.Float.$fRealDouble1 */,  -_rA/* s1l6G */)));
      }else{
        var _rD/* s1l6S */ = B(_r0/* GHC.Float.ConversionUtils.elim64# */(B(_ro/* GHC.Integer.Type.integerToInt64 */(_rz/* s1l6F */)),  -_rA/* s1l6G */));
        return new T2(0,E(_rD/* s1l6S */.a),B(_3u/* GHC.Integer.Type.shiftLInteger */(_1M/* GHC.Float.$fRealDouble1 */, _rD/* s1l6S */.b)));
      }
    };
    if(!((B(_rt/* GHC.Integer.Type.integerToWord */(_rz/* s1l6F */))&1)>>>0)){
      return new F(function(){return _rB/* s1l6K */(1);});
    }else{
      return new F(function(){return _rB/* s1l6K */(0);});
    }
  }else{
    return new T2(0,B(_3u/* GHC.Integer.Type.shiftLInteger */(_rz/* s1l6F */, _rA/* s1l6G */)),_1M/* GHC.Float.$fRealDouble1 */);
  }
},
_rE/* $fRealDouble_$ctoRational */ = function(_rF/* s1l6Z */){
  var _rG/* s1l72 */ = B(_rw/* GHC.Float.$w$ctoRational */(E(_rF/* s1l6Z */)));
  return new T2(0,E(_rG/* s1l72 */.a),E(_rG/* s1l72 */.b));
},
_rH/* $fRealDouble */ = new T3(0,_il/* GHC.Float.$fNumDouble */,_jq/* GHC.Classes.$fOrdDouble */,_rE/* GHC.Float.$fRealDouble_$ctoRational */),
_rI/* $p1Integral */ = function(_rJ/* sv9T */){
  return E(E(_rJ/* sv9T */).a);
},
_rK/* $p1Real */ = function(_rL/* svbu */){
  return E(E(_rL/* svbu */).a);
},
_rM/* eftInt */ = function(_rN/* smlE */, _rO/* smlF */){
  if(_rN/* smlE */<=_rO/* smlF */){
    var _rP/* smlI */ = function(_rQ/* smlJ */){
      return new T2(1,_rQ/* smlJ */,new T(function(){
        if(_rQ/* smlJ */!=_rO/* smlF */){
          return B(_rP/* smlI */(_rQ/* smlJ */+1|0));
        }else{
          return __Z/* EXTERNAL */;
        }
      }));
    };
    return new F(function(){return _rP/* smlI */(_rN/* smlE */);});
  }else{
    return __Z/* EXTERNAL */;
  }
},
_rR/* $fEnumInt_$cenumFrom */ = function(_rS/* smzP */){
  return new F(function(){return _rM/* GHC.Enum.eftInt */(E(_rS/* smzP */), 2147483647);});
},
_rT/* efdtIntDn */ = function(_rU/* smkb */, _rV/* smkc */, _rW/* smkd */){
  if(_rW/* smkd */<=_rV/* smkc */){
    var _rX/* smkr */ = new T(function(){
      var _rY/* smkh */ = _rV/* smkc */-_rU/* smkb */|0,
      _rZ/* smkj */ = function(_s0/* smkk */){
        return (_s0/* smkk */>=(_rW/* smkd */-_rY/* smkh */|0)) ? new T2(1,_s0/* smkk */,new T(function(){
          return B(_rZ/* smkj */(_s0/* smkk */+_rY/* smkh */|0));
        })) : new T2(1,_s0/* smkk */,_o/* GHC.Types.[] */);
      };
      return B(_rZ/* smkj */(_rV/* smkc */));
    });
    return new T2(1,_rU/* smkb */,_rX/* smkr */);
  }else{
    return (_rW/* smkd */<=_rU/* smkb */) ? new T2(1,_rU/* smkb */,_o/* GHC.Types.[] */) : __Z/* EXTERNAL */;
  }
},
_s1/* efdtIntUp */ = function(_s2/* smkR */, _s3/* smkS */, _s4/* smkT */){
  if(_s4/* smkT */>=_s3/* smkS */){
    var _s5/* sml7 */ = new T(function(){
      var _s6/* smkX */ = _s3/* smkS */-_s2/* smkR */|0,
      _s7/* smkZ */ = function(_s8/* sml0 */){
        return (_s8/* sml0 */<=(_s4/* smkT */-_s6/* smkX */|0)) ? new T2(1,_s8/* sml0 */,new T(function(){
          return B(_s7/* smkZ */(_s8/* sml0 */+_s6/* smkX */|0));
        })) : new T2(1,_s8/* sml0 */,_o/* GHC.Types.[] */);
      };
      return B(_s7/* smkZ */(_s3/* smkS */));
    });
    return new T2(1,_s2/* smkR */,_s5/* sml7 */);
  }else{
    return (_s4/* smkT */>=_s2/* smkR */) ? new T2(1,_s2/* smkR */,_o/* GHC.Types.[] */) : __Z/* EXTERNAL */;
  }
},
_s9/* efdInt */ = function(_sa/* smln */, _sb/* smlo */){
  if(_sb/* smlo */<_sa/* smln */){
    return new F(function(){return _rT/* GHC.Enum.efdtIntDn */(_sa/* smln */, _sb/* smlo */,  -2147483648);});
  }else{
    return new F(function(){return _s1/* GHC.Enum.efdtIntUp */(_sa/* smln */, _sb/* smlo */, 2147483647);});
  }
},
_sc/* $fEnumInt_$cenumFromThen */ = function(_sd/* smzJ */, _se/* smzK */){
  return new F(function(){return _s9/* GHC.Enum.efdInt */(E(_sd/* smzJ */), E(_se/* smzK */));});
},
_sf/* efdtInt */ = function(_sg/* smli */, _sh/* smlj */, _si/* smlk */){
  if(_sh/* smlj */<_sg/* smli */){
    return new F(function(){return _rT/* GHC.Enum.efdtIntDn */(_sg/* smli */, _sh/* smlj */, _si/* smlk */);});
  }else{
    return new F(function(){return _s1/* GHC.Enum.efdtIntUp */(_sg/* smli */, _sh/* smlj */, _si/* smlk */);});
  }
},
_sj/* $fEnumInt_$cenumFromThenTo */ = function(_sk/* smzu */, _sl/* smzv */, _sm/* smzw */){
  return new F(function(){return _sf/* GHC.Enum.efdtInt */(E(_sk/* smzu */), E(_sl/* smzv */), E(_sm/* smzw */));});
},
_sn/* $fEnumInt_$cenumFromTo */ = function(_so/* smzD */, _sp/* smzE */){
  return new F(function(){return _rM/* GHC.Enum.eftInt */(E(_so/* smzD */), E(_sp/* smzE */));});
},
_sq/* $fEnumInt_$cfromEnum */ = function(_sr/* smzS */){
  return E(_sr/* smzS */);
},
_ss/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));
}),
_st/* $fEnumInt1 */ = new T(function(){
  return B(err/* EXTERNAL */(_ss/* GHC.Enum.lvl28 */));
}),
_su/* $fEnumInt_$cpred */ = function(_sv/* smAv */){
  var _sw/* smAy */ = E(_sv/* smAv */);
  return (_sw/* smAy */==( -2147483648)) ? E(_st/* GHC.Enum.$fEnumInt1 */) : _sw/* smAy */-1|0;
},
_sx/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));
}),
_sy/* $fEnumInt2 */ = new T(function(){
  return B(err/* EXTERNAL */(_sx/* GHC.Enum.lvl27 */));
}),
_sz/* $fEnumInt_$csucc */ = function(_sA/* smAq */){
  var _sB/* smAt */ = E(_sA/* smAq */);
  return (_sB/* smAt */==2147483647) ? E(_sy/* GHC.Enum.$fEnumInt2 */) : _sB/* smAt */+1|0;
},
_sC/* $fEnumInt */ = {_:0,a:_sz/* GHC.Enum.$fEnumInt_$csucc */,b:_su/* GHC.Enum.$fEnumInt_$cpred */,c:_sq/* GHC.Enum.$fEnumInt_$cfromEnum */,d:_sq/* GHC.Enum.$fEnumInt_$cfromEnum */,e:_rR/* GHC.Enum.$fEnumInt_$cenumFrom */,f:_sc/* GHC.Enum.$fEnumInt_$cenumFromThen */,g:_sn/* GHC.Enum.$fEnumInt_$cenumFromTo */,h:_sj/* GHC.Enum.$fEnumInt_$cenumFromThenTo */},
_sD/* divInt# */ = function(_sE/* scDT */, _sF/* scDU */){
  if(_sE/* scDT */<=0){
    if(_sE/* scDT */>=0){
      return new F(function(){return quot/* EXTERNAL */(_sE/* scDT */, _sF/* scDU */);});
    }else{
      if(_sF/* scDU */<=0){
        return new F(function(){return quot/* EXTERNAL */(_sE/* scDT */, _sF/* scDU */);});
      }else{
        return quot/* EXTERNAL */(_sE/* scDT */+1|0, _sF/* scDU */)-1|0;
      }
    }
  }else{
    if(_sF/* scDU */>=0){
      if(_sE/* scDT */>=0){
        return new F(function(){return quot/* EXTERNAL */(_sE/* scDT */, _sF/* scDU */);});
      }else{
        if(_sF/* scDU */<=0){
          return new F(function(){return quot/* EXTERNAL */(_sE/* scDT */, _sF/* scDU */);});
        }else{
          return quot/* EXTERNAL */(_sE/* scDT */+1|0, _sF/* scDU */)-1|0;
        }
      }
    }else{
      return quot/* EXTERNAL */(_sE/* scDT */-1|0, _sF/* scDU */)-1|0;
    }
  }
},
_sG/* Overflow */ = 0,
_sH/* overflowException */ = new T(function(){
  return B(_2R/* GHC.Exception.$fExceptionArithException_$ctoException */(_sG/* GHC.Exception.Overflow */));
}),
_sI/* overflowError */ = new T(function(){
  return die/* EXTERNAL */(_sH/* GHC.Exception.overflowException */);
}),
_sJ/* $w$cdiv */ = function(_sK/* svjX */, _sL/* svjY */){
  var _sM/* svjZ */ = E(_sL/* svjY */);
  switch(_sM/* svjZ */){
    case  -1:
      var _sN/* svk0 */ = E(_sK/* svjX */);
      if(_sN/* svk0 */==( -2147483648)){
        return E(_sI/* GHC.Real.overflowError */);
      }else{
        return new F(function(){return _sD/* GHC.Classes.divInt# */(_sN/* svk0 */,  -1);});
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return _sD/* GHC.Classes.divInt# */(_sK/* svjX */, _sM/* svjZ */);});
  }
},
_sO/* $fIntegralInt_$cdiv */ = function(_sP/* svk3 */, _sQ/* svk4 */){
  return new F(function(){return _sJ/* GHC.Real.$w$cdiv */(E(_sP/* svk3 */), E(_sQ/* svk4 */));});
},
_sR/* $fIntegralInt1 */ = 0,
_sS/* lvl2 */ = new T2(0,_sI/* GHC.Real.overflowError */,_sR/* GHC.Real.$fIntegralInt1 */),
_sT/* $fIntegralInt_$cdivMod */ = function(_sU/* svi2 */, _sV/* svi3 */){
  var _sW/* svi4 */ = E(_sU/* svi2 */),
  _sX/* svi8 */ = E(_sV/* svi3 */);
  switch(_sX/* svi8 */){
    case  -1:
      var _sY/* svj6 */ = E(_sW/* svi4 */);
      if(_sY/* svj6 */==( -2147483648)){
        return E(_sS/* GHC.Real.lvl2 */);
      }else{
        if(_sY/* svj6 */<=0){
          if(_sY/* svj6 */>=0){
            var _sZ/* svjb */ = quotRemI/* EXTERNAL */(_sY/* svj6 */,  -1);
            return new T2(0,_sZ/* svjb */.a,_sZ/* svjb */.b);
          }else{
            var _t0/* svjg */ = quotRemI/* EXTERNAL */(_sY/* svj6 */,  -1);
            return new T2(0,_t0/* svjg */.a,_t0/* svjg */.b);
          }
        }else{
          var _t1/* svjm */ = quotRemI/* EXTERNAL */(_sY/* svj6 */-1|0,  -1);
          return new T2(0,_t1/* svjm */.a-1|0,(_t1/* svjm */.b+( -1)|0)+1|0);
        }
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      if(_sW/* svi4 */<=0){
        if(_sW/* svi4 */>=0){
          var _t2/* svid */ = quotRemI/* EXTERNAL */(_sW/* svi4 */, _sX/* svi8 */);
          return new T2(0,_t2/* svid */.a,_t2/* svid */.b);
        }else{
          if(_sX/* svi8 */<=0){
            var _t3/* svik */ = quotRemI/* EXTERNAL */(_sW/* svi4 */, _sX/* svi8 */);
            return new T2(0,_t3/* svik */.a,_t3/* svik */.b);
          }else{
            var _t4/* sviq */ = quotRemI/* EXTERNAL */(_sW/* svi4 */+1|0, _sX/* svi8 */);
            return new T2(0,_t4/* sviq */.a-1|0,(_t4/* sviq */.b+_sX/* svi8 */|0)-1|0);
          }
        }
      }else{
        if(_sX/* svi8 */>=0){
          if(_sW/* svi4 */>=0){
            var _t5/* sviC */ = quotRemI/* EXTERNAL */(_sW/* svi4 */, _sX/* svi8 */);
            return new T2(0,_t5/* sviC */.a,_t5/* sviC */.b);
          }else{
            if(_sX/* svi8 */<=0){
              var _t6/* sviJ */ = quotRemI/* EXTERNAL */(_sW/* svi4 */, _sX/* svi8 */);
              return new T2(0,_t6/* sviJ */.a,_t6/* sviJ */.b);
            }else{
              var _t7/* sviP */ = quotRemI/* EXTERNAL */(_sW/* svi4 */+1|0, _sX/* svi8 */);
              return new T2(0,_t7/* sviP */.a-1|0,(_t7/* sviP */.b+_sX/* svi8 */|0)-1|0);
            }
          }
        }else{
          var _t8/* sviY */ = quotRemI/* EXTERNAL */(_sW/* svi4 */-1|0, _sX/* svi8 */);
          return new T2(0,_t8/* sviY */.a-1|0,(_t8/* sviY */.b+_sX/* svi8 */|0)+1|0);
        }
      }
  }
},
_t9/* modInt# */ = function(_ta/* scF6 */, _tb/* scF7 */){
  var _tc/* scF8 */ = _ta/* scF6 */%_tb/* scF7 */;
  if(_ta/* scF6 */<=0){
    if(_ta/* scF6 */>=0){
      return E(_tc/* scF8 */);
    }else{
      if(_tb/* scF7 */<=0){
        return E(_tc/* scF8 */);
      }else{
        var _td/* scFf */ = E(_tc/* scF8 */);
        return (_td/* scFf */==0) ? 0 : _td/* scFf */+_tb/* scF7 */|0;
      }
    }
  }else{
    if(_tb/* scF7 */>=0){
      if(_ta/* scF6 */>=0){
        return E(_tc/* scF8 */);
      }else{
        if(_tb/* scF7 */<=0){
          return E(_tc/* scF8 */);
        }else{
          var _te/* scFm */ = E(_tc/* scF8 */);
          return (_te/* scFm */==0) ? 0 : _te/* scFm */+_tb/* scF7 */|0;
        }
      }
    }else{
      var _tf/* scFn */ = E(_tc/* scF8 */);
      return (_tf/* scFn */==0) ? 0 : _tf/* scFn */+_tb/* scF7 */|0;
    }
  }
},
_tg/* $fIntegralInt_$cmod */ = function(_th/* svjO */, _ti/* svjP */){
  var _tj/* svjS */ = E(_ti/* svjP */);
  switch(_tj/* svjS */){
    case  -1:
      return E(_sR/* GHC.Real.$fIntegralInt1 */);
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return _t9/* GHC.Classes.modInt# */(E(_th/* svjO */), _tj/* svjS */);});
  }
},
_tk/* $fIntegralInt_$cquot */ = function(_tl/* svki */, _tm/* svkj */){
  var _tn/* svkk */ = E(_tl/* svki */),
  _to/* svko */ = E(_tm/* svkj */);
  switch(_to/* svko */){
    case  -1:
      var _tp/* svkq */ = E(_tn/* svkk */);
      if(_tp/* svkq */==( -2147483648)){
        return E(_sI/* GHC.Real.overflowError */);
      }else{
        return new F(function(){return quot/* EXTERNAL */(_tp/* svkq */,  -1);});
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return new F(function(){return quot/* EXTERNAL */(_tn/* svkk */, _to/* svko */);});
  }
},
_tq/* $fIntegralInt_$cquotRem */ = function(_tr/* svjv */, _ts/* svjw */){
  var _tt/* svjx */ = E(_tr/* svjv */),
  _tu/* svjB */ = E(_ts/* svjw */);
  switch(_tu/* svjB */){
    case  -1:
      var _tv/* svjH */ = E(_tt/* svjx */);
      if(_tv/* svjH */==( -2147483648)){
        return E(_sS/* GHC.Real.lvl2 */);
      }else{
        var _tw/* svjI */ = quotRemI/* EXTERNAL */(_tv/* svjH */,  -1);
        return new T2(0,_tw/* svjI */.a,_tw/* svjI */.b);
      }
      break;
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      var _tx/* svjC */ = quotRemI/* EXTERNAL */(_tt/* svjx */, _tu/* svjB */);
      return new T2(0,_tx/* svjC */.a,_tx/* svjC */.b);
  }
},
_ty/* $fIntegralInt_$crem */ = function(_tz/* svka */, _tA/* svkb */){
  var _tB/* svke */ = E(_tA/* svkb */);
  switch(_tB/* svke */){
    case  -1:
      return E(_sR/* GHC.Real.$fIntegralInt1 */);
    case 0:
      return E(_2V/* GHC.Real.divZeroError */);
    default:
      return E(_tz/* svka */)%_tB/* svke */;
  }
},
_tC/* $fIntegralInt_$ctoInteger */ = function(_tD/* svhV */){
  return new F(function(){return _qH/* GHC.Integer.Type.smallInteger */(E(_tD/* svhV */));});
},
_tE/* $fEnumRatio_$ctoRational */ = function(_tF/* svhY */){
  return new T2(0,E(B(_qH/* GHC.Integer.Type.smallInteger */(E(_tF/* svhY */)))),E(_mq/* GHC.Real.$fEnumRatio1 */));
},
_tG/* $fNumInt_$c* */ = function(_tH/* s6GN */, _tI/* s6GO */){
  return imul/* EXTERNAL */(E(_tH/* s6GN */), E(_tI/* s6GO */))|0;
},
_tJ/* $fNumInt_$c+ */ = function(_tK/* s6H1 */, _tL/* s6H2 */){
  return E(_tK/* s6H1 */)+E(_tL/* s6H2 */)|0;
},
_tM/* $fNumInt_$c- */ = function(_tN/* s6GU */, _tO/* s6GV */){
  return E(_tN/* s6GU */)-E(_tO/* s6GV */)|0;
},
_tP/* $fNumInt_$cabs */ = function(_tQ/* s6He */){
  var _tR/* s6Hf */ = E(_tQ/* s6He */);
  return (_tR/* s6Hf */<0) ?  -_tR/* s6Hf */ : E(_tR/* s6Hf */);
},
_tS/* $fNumInt_$cfromInteger */ = function(_tT/* s6GH */){
  return new F(function(){return _38/* GHC.Integer.Type.integerToInt */(_tT/* s6GH */);});
},
_tU/* $fNumInt_$cnegate */ = function(_tV/* s6GJ */){
  return  -E(_tV/* s6GJ */);
},
_tW/* $fNumInt1 */ =  -1,
_tX/* $fNumInt2 */ = 0,
_tY/* $fNumInt3 */ = 1,
_tZ/* $fNumInt_$csignum */ = function(_u0/* s6H8 */){
  var _u1/* s6H9 */ = E(_u0/* s6H8 */);
  return (_u1/* s6H9 */>=0) ? (E(_u1/* s6H9 */)==0) ? E(_tX/* GHC.Num.$fNumInt2 */) : E(_tY/* GHC.Num.$fNumInt3 */) : E(_tW/* GHC.Num.$fNumInt1 */);
},
_u2/* $fNumInt */ = {_:0,a:_tJ/* GHC.Num.$fNumInt_$c+ */,b:_tM/* GHC.Num.$fNumInt_$c- */,c:_tG/* GHC.Num.$fNumInt_$c* */,d:_tU/* GHC.Num.$fNumInt_$cnegate */,e:_tP/* GHC.Num.$fNumInt_$cabs */,f:_tZ/* GHC.Num.$fNumInt_$csignum */,g:_tS/* GHC.Num.$fNumInt_$cfromInteger */},
_u3/* eqInt */ = function(_u4/* scEd */, _u5/* scEe */){
  return E(_u4/* scEd */)==E(_u5/* scEe */);
},
_u6/* neInt */ = function(_u7/* scEM */, _u8/* scEN */){
  return E(_u7/* scEM */)!=E(_u8/* scEN */);
},
_u9/* $fEqInt */ = new T2(0,_u3/* GHC.Classes.eqInt */,_u6/* GHC.Classes.neInt */),
_ua/* $fOrdInt_$cmax */ = function(_ub/* scK3 */, _uc/* scK4 */){
  var _ud/* scK5 */ = E(_ub/* scK3 */),
  _ue/* scK7 */ = E(_uc/* scK4 */);
  return (_ud/* scK5 */>_ue/* scK7 */) ? E(_ud/* scK5 */) : E(_ue/* scK7 */);
},
_uf/* $fOrdInt_$cmin */ = function(_ug/* scJV */, _uh/* scJW */){
  var _ui/* scJX */ = E(_ug/* scJV */),
  _uj/* scJZ */ = E(_uh/* scJW */);
  return (_ui/* scJX */>_uj/* scJZ */) ? E(_uj/* scJZ */) : E(_ui/* scJX */);
},
_uk/* compareInt# */ = function(_ul/* scDH */, _um/* scDI */){
  return (_ul/* scDH */>=_um/* scDI */) ? (_ul/* scDH */!=_um/* scDI */) ? 2 : 1 : 0;
},
_un/* compareInt */ = function(_uo/* scDN */, _up/* scDO */){
  return new F(function(){return _uk/* GHC.Classes.compareInt# */(E(_uo/* scDN */), E(_up/* scDO */));});
},
_uq/* geInt */ = function(_ur/* scEk */, _us/* scEl */){
  return E(_ur/* scEk */)>=E(_us/* scEl */);
},
_ut/* gtInt */ = function(_uu/* scEr */, _uv/* scEs */){
  return E(_uu/* scEr */)>E(_uv/* scEs */);
},
_uw/* leInt */ = function(_ux/* scEy */, _uy/* scEz */){
  return E(_ux/* scEy */)<=E(_uy/* scEz */);
},
_uz/* ltInt */ = function(_uA/* scEF */, _uB/* scEG */){
  return E(_uA/* scEF */)<E(_uB/* scEG */);
},
_uC/* $fOrdInt */ = {_:0,a:_u9/* GHC.Classes.$fEqInt */,b:_un/* GHC.Classes.compareInt */,c:_uz/* GHC.Classes.ltInt */,d:_uw/* GHC.Classes.leInt */,e:_ut/* GHC.Classes.gtInt */,f:_uq/* GHC.Classes.geInt */,g:_ua/* GHC.Classes.$fOrdInt_$cmax */,h:_uf/* GHC.Classes.$fOrdInt_$cmin */},
_uD/* $fRealInt */ = new T3(0,_u2/* GHC.Num.$fNumInt */,_uC/* GHC.Classes.$fOrdInt */,_tE/* GHC.Real.$fEnumRatio_$ctoRational */),
_uE/* $fIntegralInt */ = {_:0,a:_uD/* GHC.Real.$fRealInt */,b:_sC/* GHC.Enum.$fEnumInt */,c:_tk/* GHC.Real.$fIntegralInt_$cquot */,d:_ty/* GHC.Real.$fIntegralInt_$crem */,e:_sO/* GHC.Real.$fIntegralInt_$cdiv */,f:_tg/* GHC.Real.$fIntegralInt_$cmod */,g:_tq/* GHC.Real.$fIntegralInt_$cquotRem */,h:_sT/* GHC.Real.$fIntegralInt_$cdivMod */,i:_tC/* GHC.Real.$fIntegralInt_$ctoInteger */},
_uF/* $fRealFloatDouble5 */ = new T1(0,2),
_uG/* timesInteger */ = function(_uH/* s1PN */, _uI/* s1PO */){
  while(1){
    var _uJ/* s1PP */ = E(_uH/* s1PN */);
    if(!_uJ/* s1PP */._){
      var _uK/* s1PQ */ = _uJ/* s1PP */.a,
      _uL/* s1PR */ = E(_uI/* s1PO */);
      if(!_uL/* s1PR */._){
        var _uM/* s1PS */ = _uL/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_uK/* s1PQ */, _uM/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_uK/* s1PQ */, _uM/* s1PS */)|0);
        }else{
          _uH/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_uK/* s1PQ */));
          _uI/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_uM/* s1PS */));
          continue;
        }
      }else{
        _uH/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_uK/* s1PQ */));
        _uI/* s1PO */ = _uL/* s1PR */;
        continue;
      }
    }else{
      var _uN/* s1Q6 */ = E(_uI/* s1PO */);
      if(!_uN/* s1Q6 */._){
        _uH/* s1PN */ = _uJ/* s1PP */;
        _uI/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_uN/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_uJ/* s1PP */.a, _uN/* s1Q6 */.a));
      }
    }
  }
},
_uO/* $wg1 */ = function(_uP/* svGB */, _uQ/* svGC */, _uR/* svGD */){
  while(1){
    if(!(_uQ/* svGC */%2)){
      var _uS/*  svGB */ = B(_uG/* GHC.Integer.Type.timesInteger */(_uP/* svGB */, _uP/* svGB */)),
      _uT/*  svGC */ = quot/* EXTERNAL */(_uQ/* svGC */, 2);
      _uP/* svGB */ = _uS/*  svGB */;
      _uQ/* svGC */ = _uT/*  svGC */;
      continue;
    }else{
      var _uU/* svGF */ = E(_uQ/* svGC */);
      if(_uU/* svGF */==1){
        return new F(function(){return _uG/* GHC.Integer.Type.timesInteger */(_uP/* svGB */, _uR/* svGD */);});
      }else{
        var _uS/*  svGB */ = B(_uG/* GHC.Integer.Type.timesInteger */(_uP/* svGB */, _uP/* svGB */)),
        _uV/*  svGD */ = B(_uG/* GHC.Integer.Type.timesInteger */(_uP/* svGB */, _uR/* svGD */));
        _uP/* svGB */ = _uS/*  svGB */;
        _uQ/* svGC */ = quot/* EXTERNAL */(_uU/* svGF */-1|0, 2);
        _uR/* svGD */ = _uV/*  svGD */;
        continue;
      }
    }
  }
},
_uW/* $wf */ = function(_uX/* svGM */, _uY/* svGN */){
  while(1){
    if(!(_uY/* svGN */%2)){
      var _uZ/*  svGM */ = B(_uG/* GHC.Integer.Type.timesInteger */(_uX/* svGM */, _uX/* svGM */)),
      _v0/*  svGN */ = quot/* EXTERNAL */(_uY/* svGN */, 2);
      _uX/* svGM */ = _uZ/*  svGM */;
      _uY/* svGN */ = _v0/*  svGN */;
      continue;
    }else{
      var _v1/* svGP */ = E(_uY/* svGN */);
      if(_v1/* svGP */==1){
        return E(_uX/* svGM */);
      }else{
        return new F(function(){return _uO/* GHC.Real.$wg1 */(B(_uG/* GHC.Integer.Type.timesInteger */(_uX/* svGM */, _uX/* svGM */)), quot/* EXTERNAL */(_v1/* svGP */-1|0, 2), _uX/* svGM */);});
      }
    }
  }
},
_v2/* $p2Real */ = function(_v3/* svbz */){
  return E(E(_v3/* svbz */).b);
},
_v4/* < */ = function(_v5/* scCc */){
  return E(E(_v5/* scCc */).c);
},
_v6/* even1 */ = new T1(0,0),
_v7/* rem */ = function(_v8/* svaq */){
  return E(E(_v8/* svaq */).d);
},
_v9/* even */ = function(_va/* svAV */, _vb/* svAW */){
  var _vc/* svAX */ = B(_rI/* GHC.Real.$p1Integral */(_va/* svAV */)),
  _vd/* svAY */ = new T(function(){
    return B(_rK/* GHC.Real.$p1Real */(_vc/* svAX */));
  }),
  _ve/* svB2 */ = new T(function(){
    return B(A3(_v7/* GHC.Real.rem */,_va/* svAV */, _vb/* svAW */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_vd/* svAY */, _mA/* GHC.Real.even2 */));
    })));
  });
  return new F(function(){return A3(_ll/* GHC.Classes.== */,B(_l7/* GHC.Classes.$p1Ord */(B(_v2/* GHC.Real.$p2Real */(_vc/* svAX */)))), _ve/* svB2 */, new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,_vd/* svAY */, _v6/* GHC.Real.even1 */));
  }));});
},
_vf/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_vg/* lvl11 */ = new T(function(){
  return B(err/* EXTERNAL */(_vf/* GHC.Real.lvl5 */));
}),
_vh/* quot */ = function(_vi/* svaf */){
  return E(E(_vi/* svaf */).c);
},
_vj/* ^ */ = function(_vk/* svH6 */, _vl/* svH7 */, _vm/* svH8 */, _vn/* svH9 */){
  var _vo/* svHa */ = B(_rI/* GHC.Real.$p1Integral */(_vl/* svH7 */)),
  _vp/* svHb */ = new T(function(){
    return B(_rK/* GHC.Real.$p1Real */(_vo/* svHa */));
  }),
  _vq/* svHc */ = B(_v2/* GHC.Real.$p2Real */(_vo/* svHa */));
  if(!B(A3(_v4/* GHC.Classes.< */,_vq/* svHc */, _vn/* svH9 */, new T(function(){
    return B(A2(_91/* GHC.Num.fromInteger */,_vp/* svHb */, _v6/* GHC.Real.even1 */));
  })))){
    if(!B(A3(_ll/* GHC.Classes.== */,B(_l7/* GHC.Classes.$p1Ord */(_vq/* svHc */)), _vn/* svH9 */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_vp/* svHb */, _v6/* GHC.Real.even1 */));
    })))){
      var _vr/* svHi */ = new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_vp/* svHb */, _mA/* GHC.Real.even2 */));
      }),
      _vs/* svHj */ = new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_vp/* svHb */, _mq/* GHC.Real.$fEnumRatio1 */));
      }),
      _vt/* svHk */ = B(_l7/* GHC.Classes.$p1Ord */(_vq/* svHc */)),
      _vu/* svHl */ = function(_vv/*  svHm */, _vw/*  svHn */, _vx/*  svHo */){
        while(1){
          var _vy/*  svHl */ = B((function(_vz/* svHm */, _vA/* svHn */, _vB/* svHo */){
            if(!B(_v9/* GHC.Real.even */(_vl/* svH7 */, _vA/* svHn */))){
              if(!B(A3(_ll/* GHC.Classes.== */,_vt/* svHk */, _vA/* svHn */, _vs/* svHj */))){
                var _vC/* svHt */ = new T(function(){
                  return B(A3(_vh/* GHC.Real.quot */,_vl/* svH7 */, new T(function(){
                    return B(A3(_7m/* GHC.Num.- */,_vp/* svHb */, _vA/* svHn */, _vs/* svHj */));
                  }), _vr/* svHi */));
                });
                _vv/*  svHm */ = new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_vk/* svH6 */, _vz/* svHm */, _vz/* svHm */));
                });
                _vw/*  svHn */ = _vC/* svHt */;
                _vx/*  svHo */ = new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_vk/* svH6 */, _vz/* svHm */, _vB/* svHo */));
                });
                return __continue/* EXTERNAL */;
              }else{
                return new F(function(){return A3(_7k/* GHC.Num.* */,_vk/* svH6 */, _vz/* svHm */, _vB/* svHo */);});
              }
            }else{
              var _vD/*   svHo */ = _vB/* svHo */;
              _vv/*  svHm */ = new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_vk/* svH6 */, _vz/* svHm */, _vz/* svHm */));
              });
              _vw/*  svHn */ = new T(function(){
                return B(A3(_vh/* GHC.Real.quot */,_vl/* svH7 */, _vA/* svHn */, _vr/* svHi */));
              });
              _vx/*  svHo */ = _vD/*   svHo */;
              return __continue/* EXTERNAL */;
            }
          })(_vv/*  svHm */, _vw/*  svHn */, _vx/*  svHo */));
          if(_vy/*  svHl */!=__continue/* EXTERNAL */){
            return _vy/*  svHl */;
          }
        }
      },
      _vE/* svHx */ = function(_vF/*  svHy */, _vG/*  svHz */){
        while(1){
          var _vH/*  svHx */ = B((function(_vI/* svHy */, _vJ/* svHz */){
            if(!B(_v9/* GHC.Real.even */(_vl/* svH7 */, _vJ/* svHz */))){
              if(!B(A3(_ll/* GHC.Classes.== */,_vt/* svHk */, _vJ/* svHz */, _vs/* svHj */))){
                var _vK/* svHE */ = new T(function(){
                  return B(A3(_vh/* GHC.Real.quot */,_vl/* svH7 */, new T(function(){
                    return B(A3(_7m/* GHC.Num.- */,_vp/* svHb */, _vJ/* svHz */, _vs/* svHj */));
                  }), _vr/* svHi */));
                });
                return new F(function(){return _vu/* svHl */(new T(function(){
                  return B(A3(_7k/* GHC.Num.* */,_vk/* svH6 */, _vI/* svHy */, _vI/* svHy */));
                }), _vK/* svHE */, _vI/* svHy */);});
              }else{
                return E(_vI/* svHy */);
              }
            }else{
              _vF/*  svHy */ = new T(function(){
                return B(A3(_7k/* GHC.Num.* */,_vk/* svH6 */, _vI/* svHy */, _vI/* svHy */));
              });
              _vG/*  svHz */ = new T(function(){
                return B(A3(_vh/* GHC.Real.quot */,_vl/* svH7 */, _vJ/* svHz */, _vr/* svHi */));
              });
              return __continue/* EXTERNAL */;
            }
          })(_vF/*  svHy */, _vG/*  svHz */));
          if(_vH/*  svHx */!=__continue/* EXTERNAL */){
            return _vH/*  svHx */;
          }
        }
      };
      return new F(function(){return _vE/* svHx */(_vm/* svH8 */, _vn/* svH9 */);});
    }else{
      return new F(function(){return A2(_91/* GHC.Num.fromInteger */,_vk/* svH6 */, _mq/* GHC.Real.$fEnumRatio1 */);});
    }
  }else{
    return E(_vg/* GHC.Real.lvl11 */);
  }
},
_vL/* ^1 */ = new T(function(){
  return B(err/* EXTERNAL */(_vf/* GHC.Real.lvl5 */));
}),
_vM/* $w$cproperFraction */ = function(_vN/* s1l7J */, _vO/* s1l7K */){
  var _vP/* s1l7L */ = B(_qE/* GHC.Integer.Type.decodeDoubleInteger */(_vO/* s1l7K */)),
  _vQ/* s1l7M */ = _vP/* s1l7L */.a,
  _vR/* s1l7N */ = _vP/* s1l7L */.b,
  _vS/* s1l7P */ = new T(function(){
    return B(_rK/* GHC.Real.$p1Real */(new T(function(){
      return B(_rI/* GHC.Real.$p1Integral */(_vN/* s1l7J */));
    })));
  });
  if(_vR/* s1l7N */<0){
    var _vT/* s1l7S */ =  -_vR/* s1l7N */;
    if(_vT/* s1l7S */>=0){
      var _vU/* s1l7W */ = E(_vT/* s1l7S */);
      if(!_vU/* s1l7W */){
        var _vV/* s1l7W#result */ = E(_mq/* GHC.Real.$fEnumRatio1 */);
      }else{
        var _vV/* s1l7W#result */ = B(_uW/* GHC.Real.$wf */(_uF/* GHC.Float.$fRealFloatDouble5 */, _vU/* s1l7W */));
      }
      if(!B(_30/* GHC.Integer.Type.eqInteger */(_vV/* s1l7W#result */, _3t/* GHC.Float.rationalToDouble5 */))){
        var _vW/* s1l7Y */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_vQ/* s1l7M */, _vV/* s1l7W#result */));
        return new T2(0,new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_vS/* s1l7P */, _vW/* s1l7Y */.a));
        }),new T(function(){
          return B(_2W/* GHC.Integer.Type.encodeDoubleInteger */(_vW/* s1l7Y */.b, _vR/* s1l7N */));
        }));
      }else{
        return E(_2V/* GHC.Real.divZeroError */);
      }
    }else{
      return E(_vL/* GHC.Real.^1 */);
    }
  }else{
    var _vX/* s1l8a */ = new T(function(){
      var _vY/* s1l89 */ = new T(function(){
        return B(_vj/* GHC.Real.^ */(_vS/* s1l7P */, _uE/* GHC.Real.$fIntegralInt */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_vS/* s1l7P */, _uF/* GHC.Float.$fRealFloatDouble5 */));
        }), _vR/* s1l7N */));
      });
      return B(A3(_7k/* GHC.Num.* */,_vS/* s1l7P */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_vS/* s1l7P */, _vQ/* s1l7M */));
      }), _vY/* s1l89 */));
    });
    return new T2(0,_vX/* s1l8a */,_6i/* GHC.Float.rationalToDouble4 */);
  }
},
_vZ/* $fRealFracDouble_$cceiling */ = function(_w0/* s1l8X */, _w1/* s1l8Y */){
  var _w2/* s1l91 */ = B(_vM/* GHC.Float.$w$cproperFraction */(_w0/* s1l8X */, E(_w1/* s1l8Y */))),
  _w3/* s1l92 */ = _w2/* s1l91 */.a;
  if(E(_w2/* s1l91 */.b)<=0){
    return E(_w3/* s1l92 */);
  }else{
    var _w4/* s1l99 */ = B(_rK/* GHC.Real.$p1Real */(B(_rI/* GHC.Real.$p1Integral */(_w0/* s1l8X */))));
    return new F(function(){return A3(_6I/* GHC.Num.+ */,_w4/* s1l99 */, _w3/* s1l92 */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_w4/* s1l99 */, _1M/* GHC.Float.$fRealDouble1 */));
    }));});
  }
},
_w5/* $fRealFracDouble_$cfloor */ = function(_w6/* s1l9b */, _w7/* s1l9c */){
  var _w8/* s1l9f */ = B(_vM/* GHC.Float.$w$cproperFraction */(_w6/* s1l9b */, E(_w7/* s1l9c */))),
  _w9/* s1l9g */ = _w8/* s1l9f */.a;
  if(E(_w8/* s1l9f */.b)>=0){
    return E(_w9/* s1l9g */);
  }else{
    var _wa/* s1l9n */ = B(_rK/* GHC.Real.$p1Real */(B(_rI/* GHC.Real.$p1Integral */(_w6/* s1l9b */))));
    return new F(function(){return A3(_7m/* GHC.Num.- */,_wa/* s1l9n */, _w9/* s1l9g */, new T(function(){
      return B(A2(_91/* GHC.Num.fromInteger */,_wa/* s1l9n */, _1M/* GHC.Float.$fRealDouble1 */));
    }));});
  }
},
_wb/* $fRealFracDouble_$cproperFraction */ = function(_wc/* s1l8b */, _wd/* s1l8c */){
  var _we/* s1l8f */ = B(_vM/* GHC.Float.$w$cproperFraction */(_wc/* s1l8b */, E(_wd/* s1l8c */)));
  return new T2(0,_we/* s1l8f */.a,_we/* s1l8f */.b);
},
_wf/* $w$cround */ = function(_wg/* s1l8p */, _wh/* s1l8q */){
  var _wi/* s1l8r */ = B(_vM/* GHC.Float.$w$cproperFraction */(_wg/* s1l8p */, _wh/* s1l8q */)),
  _wj/* s1l8s */ = _wi/* s1l8r */.a,
  _wk/* s1l8u */ = E(_wi/* s1l8r */.b),
  _wl/* s1l8w */ = new T(function(){
    var _wm/* s1l8y */ = B(_rK/* GHC.Real.$p1Real */(B(_rI/* GHC.Real.$p1Integral */(_wg/* s1l8p */))));
    if(_wk/* s1l8u */>=0){
      return B(A3(_6I/* GHC.Num.+ */,_wm/* s1l8y */, _wj/* s1l8s */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_wm/* s1l8y */, _1M/* GHC.Float.$fRealDouble1 */));
      })));
    }else{
      return B(A3(_7m/* GHC.Num.- */,_wm/* s1l8y */, _wj/* s1l8s */, new T(function(){
        return B(A2(_91/* GHC.Num.fromInteger */,_wm/* s1l8y */, _1M/* GHC.Float.$fRealDouble1 */));
      })));
    }
  }),
  _wn/* s1l8D */ = function(_wo/* s1l8E */){
    var _wp/* s1l8F */ = _wo/* s1l8E */-0.5;
    return (_wp/* s1l8F */>=0) ? (E(_wp/* s1l8F */)==0) ? (!B(_v9/* GHC.Real.even */(_wg/* s1l8p */, _wj/* s1l8s */))) ? E(_wl/* s1l8w */) : E(_wj/* s1l8s */) : E(_wl/* s1l8w */) : E(_wj/* s1l8s */);
  },
  _wq/* s1l8K */ = E(_wk/* s1l8u */);
  if(!_wq/* s1l8K */){
    return new F(function(){return _wn/* s1l8D */(0);});
  }else{
    if(_wq/* s1l8K */<=0){
      var _wr/* s1l8N */ =  -_wq/* s1l8K */-0.5;
      return (_wr/* s1l8N */>=0) ? (E(_wr/* s1l8N */)==0) ? (!B(_v9/* GHC.Real.even */(_wg/* s1l8p */, _wj/* s1l8s */))) ? E(_wl/* s1l8w */) : E(_wj/* s1l8s */) : E(_wl/* s1l8w */) : E(_wj/* s1l8s */);
    }else{
      return new F(function(){return _wn/* s1l8D */(_wq/* s1l8K */);});
    }
  }
},
_ws/* $fRealFracDouble_$cround */ = function(_wt/* s1l8T */, _wu/* s1l8U */){
  return new F(function(){return _wf/* GHC.Float.$w$cround */(_wt/* s1l8T */, E(_wu/* s1l8U */));});
},
_wv/* $fRealFracDouble_$ctruncate */ = function(_ww/* s1l8i */, _wx/* s1l8j */){
  return E(B(_vM/* GHC.Float.$w$cproperFraction */(_ww/* s1l8i */, E(_wx/* s1l8j */))).a);
},
_wy/* $fRealFracDouble */ = {_:0,a:_rH/* GHC.Float.$fRealDouble */,b:_ip/* GHC.Float.$fFractionalDouble */,c:_wb/* GHC.Float.$fRealFracDouble_$cproperFraction */,d:_wv/* GHC.Float.$fRealFracDouble_$ctruncate */,e:_ws/* GHC.Float.$fRealFracDouble_$cround */,f:_vZ/* GHC.Float.$fRealFracDouble_$cceiling */,g:_w5/* GHC.Float.$fRealFracDouble_$cfloor */},
_wz/* $fEnumInteger2 */ = new T1(0,1),
_wA/* $wenumDeltaInteger */ = function(_wB/* smF4 */, _wC/* smF5 */){
  var _wD/* smF6 */ = E(_wB/* smF4 */);
  return new T2(0,_wD/* smF6 */,new T(function(){
    var _wE/* smF8 */ = B(_wA/* GHC.Enum.$wenumDeltaInteger */(B(_3b/* GHC.Integer.Type.plusInteger */(_wD/* smF6 */, _wC/* smF5 */)), _wC/* smF5 */));
    return new T2(1,_wE/* smF8 */.a,_wE/* smF8 */.b);
  }));
},
_wF/* $fEnumInteger_$cenumFrom */ = function(_wG/* smFn */){
  var _wH/* smFo */ = B(_wA/* GHC.Enum.$wenumDeltaInteger */(_wG/* smFn */, _wz/* GHC.Enum.$fEnumInteger2 */));
  return new T2(1,_wH/* smFo */.a,_wH/* smFo */.b);
},
_wI/* $fEnumInteger_$cenumFromThen */ = function(_wJ/* smFr */, _wK/* smFs */){
  var _wL/* smFu */ = B(_wA/* GHC.Enum.$wenumDeltaInteger */(_wJ/* smFr */, new T(function(){
    return B(_5w/* GHC.Integer.Type.minusInteger */(_wK/* smFs */, _wJ/* smFr */));
  })));
  return new T2(1,_wL/* smFu */.a,_wL/* smFu */.b);
},
_wM/* $fEnumInteger1 */ = new T1(0,0),
_wN/* geInteger */ = function(_wO/* s1FG */, _wP/* s1FH */){
  var _wQ/* s1FI */ = E(_wO/* s1FG */);
  if(!_wQ/* s1FI */._){
    var _wR/* s1FJ */ = _wQ/* s1FI */.a,
    _wS/* s1FK */ = E(_wP/* s1FH */);
    return (_wS/* s1FK */._==0) ? _wR/* s1FJ */>=_wS/* s1FK */.a : I_compareInt/* EXTERNAL */(_wS/* s1FK */.a, _wR/* s1FJ */)<=0;
  }else{
    var _wT/* s1FR */ = _wQ/* s1FI */.a,
    _wU/* s1FS */ = E(_wP/* s1FH */);
    return (_wU/* s1FS */._==0) ? I_compareInt/* EXTERNAL */(_wT/* s1FR */, _wU/* s1FS */.a)>=0 : I_compare/* EXTERNAL */(_wT/* s1FR */, _wU/* s1FS */.a)>=0;
  }
},
_wV/* enumDeltaToInteger */ = function(_wW/* smFx */, _wX/* smFy */, _wY/* smFz */){
  if(!B(_wN/* GHC.Integer.Type.geInteger */(_wX/* smFy */, _wM/* GHC.Enum.$fEnumInteger1 */))){
    var _wZ/* smFB */ = function(_x0/* smFC */){
      return (!B(_3N/* GHC.Integer.Type.ltInteger */(_x0/* smFC */, _wY/* smFz */))) ? new T2(1,_x0/* smFC */,new T(function(){
        return B(_wZ/* smFB */(B(_3b/* GHC.Integer.Type.plusInteger */(_x0/* smFC */, _wX/* smFy */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _wZ/* smFB */(_wW/* smFx */);});
  }else{
    var _x1/* smFG */ = function(_x2/* smFH */){
      return (!B(_3E/* GHC.Integer.Type.gtInteger */(_x2/* smFH */, _wY/* smFz */))) ? new T2(1,_x2/* smFH */,new T(function(){
        return B(_x1/* smFG */(B(_3b/* GHC.Integer.Type.plusInteger */(_x2/* smFH */, _wX/* smFy */))));
      })) : __Z/* EXTERNAL */;
    };
    return new F(function(){return _x1/* smFG */(_wW/* smFx */);});
  }
},
_x3/* $fEnumInteger_$cenumFromThenTo */ = function(_x4/* smFY */, _x5/* smFZ */, _x6/* smG0 */){
  return new F(function(){return _wV/* GHC.Enum.enumDeltaToInteger */(_x4/* smFY */, B(_5w/* GHC.Integer.Type.minusInteger */(_x5/* smFZ */, _x4/* smFY */)), _x6/* smG0 */);});
},
_x7/* $fEnumInteger_$cenumFromTo */ = function(_x8/* smFW */, _x9/* smFX */){
  return new F(function(){return _wV/* GHC.Enum.enumDeltaToInteger */(_x8/* smFW */, _wz/* GHC.Enum.$fEnumInteger2 */, _x9/* smFX */);});
},
_xa/* $fEnumInteger_$cfromEnum */ = function(_xb/* smEX */){
  return new F(function(){return _38/* GHC.Integer.Type.integerToInt */(_xb/* smEX */);});
},
_xc/* $fEnumInteger_$cpred */ = function(_xd/* smF3 */){
  return new F(function(){return _5w/* GHC.Integer.Type.minusInteger */(_xd/* smF3 */, _wz/* GHC.Enum.$fEnumInteger2 */);});
},
_xe/* $fEnumInteger_$csucc */ = function(_xf/* smF2 */){
  return new F(function(){return _3b/* GHC.Integer.Type.plusInteger */(_xf/* smF2 */, _wz/* GHC.Enum.$fEnumInteger2 */);});
},
_xg/* $fEnumInteger_$ctoEnum */ = function(_xh/* smEZ */){
  return new F(function(){return _qH/* GHC.Integer.Type.smallInteger */(E(_xh/* smEZ */));});
},
_xi/* $fEnumInteger */ = {_:0,a:_xe/* GHC.Enum.$fEnumInteger_$csucc */,b:_xc/* GHC.Enum.$fEnumInteger_$cpred */,c:_xg/* GHC.Enum.$fEnumInteger_$ctoEnum */,d:_xa/* GHC.Enum.$fEnumInteger_$cfromEnum */,e:_wF/* GHC.Enum.$fEnumInteger_$cenumFrom */,f:_wI/* GHC.Enum.$fEnumInteger_$cenumFromThen */,g:_x7/* GHC.Enum.$fEnumInteger_$cenumFromTo */,h:_x3/* GHC.Enum.$fEnumInteger_$cenumFromThenTo */},
_xj/* divInteger */ = function(_xk/* s1Nz */, _xl/* s1NA */){
  while(1){
    var _xm/* s1NB */ = E(_xk/* s1Nz */);
    if(!_xm/* s1NB */._){
      var _xn/* s1ND */ = E(_xm/* s1NB */.a);
      if(_xn/* s1ND */==( -2147483648)){
        _xk/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _xo/* s1NE */ = E(_xl/* s1NA */);
        if(!_xo/* s1NE */._){
          return new T1(0,B(_sD/* GHC.Classes.divInt# */(_xn/* s1ND */, _xo/* s1NE */.a)));
        }else{
          _xk/* s1Nz */ = new T1(1,I_fromInt/* EXTERNAL */(_xn/* s1ND */));
          _xl/* s1NA */ = _xo/* s1NE */;
          continue;
        }
      }
    }else{
      var _xp/* s1NO */ = _xm/* s1NB */.a,
      _xq/* s1NP */ = E(_xl/* s1NA */);
      return (_xq/* s1NP */._==0) ? new T1(1,I_div/* EXTERNAL */(_xp/* s1NO */, I_fromInt/* EXTERNAL */(_xq/* s1NP */.a))) : new T1(1,I_div/* EXTERNAL */(_xp/* s1NO */, _xq/* s1NP */.a));
    }
  }
},
_xr/* $fIntegralInteger_$cdiv */ = function(_xs/* svkR */, _xt/* svkS */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_xt/* svkS */, _v6/* GHC.Real.even1 */))){
    return new F(function(){return _xj/* GHC.Integer.Type.divInteger */(_xs/* svkR */, _xt/* svkS */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xu/* divModInteger */ = function(_xv/* s1MF */, _xw/* s1MG */){
  while(1){
    var _xx/* s1MH */ = E(_xv/* s1MF */);
    if(!_xx/* s1MH */._){
      var _xy/* s1MJ */ = E(_xx/* s1MH */.a);
      if(_xy/* s1MJ */==( -2147483648)){
        _xv/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _xz/* s1MK */ = E(_xw/* s1MG */);
        if(!_xz/* s1MK */._){
          var _xA/* s1ML */ = _xz/* s1MK */.a;
          return new T2(0,new T1(0,B(_sD/* GHC.Classes.divInt# */(_xy/* s1MJ */, _xA/* s1ML */))),new T1(0,B(_t9/* GHC.Classes.modInt# */(_xy/* s1MJ */, _xA/* s1ML */))));
        }else{
          _xv/* s1MF */ = new T1(1,I_fromInt/* EXTERNAL */(_xy/* s1MJ */));
          _xw/* s1MG */ = _xz/* s1MK */;
          continue;
        }
      }
    }else{
      var _xB/* s1MY */ = E(_xw/* s1MG */);
      if(!_xB/* s1MY */._){
        _xv/* s1MF */ = _xx/* s1MH */;
        _xw/* s1MG */ = new T1(1,I_fromInt/* EXTERNAL */(_xB/* s1MY */.a));
        continue;
      }else{
        var _xC/* s1N5 */ = I_divMod/* EXTERNAL */(_xx/* s1MH */.a, _xB/* s1MY */.a);
        return new T2(0,new T1(1,_xC/* s1N5 */.a),new T1(1,_xC/* s1N5 */.b));
      }
    }
  }
},
_xD/* $fIntegralInteger_$cdivMod */ = function(_xE/* svkC */, _xF/* svkD */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_xF/* svkD */, _v6/* GHC.Real.even1 */))){
    var _xG/* svkF */ = B(_xu/* GHC.Integer.Type.divModInteger */(_xE/* svkC */, _xF/* svkD */));
    return new T2(0,_xG/* svkF */.a,_xG/* svkF */.b);
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xH/* modInteger */ = function(_xI/* s1Na */, _xJ/* s1Nb */){
  while(1){
    var _xK/* s1Nc */ = E(_xI/* s1Na */);
    if(!_xK/* s1Nc */._){
      var _xL/* s1Ne */ = E(_xK/* s1Nc */.a);
      if(_xL/* s1Ne */==( -2147483648)){
        _xI/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _xM/* s1Nf */ = E(_xJ/* s1Nb */);
        if(!_xM/* s1Nf */._){
          return new T1(0,B(_t9/* GHC.Classes.modInt# */(_xL/* s1Ne */, _xM/* s1Nf */.a)));
        }else{
          _xI/* s1Na */ = new T1(1,I_fromInt/* EXTERNAL */(_xL/* s1Ne */));
          _xJ/* s1Nb */ = _xM/* s1Nf */;
          continue;
        }
      }
    }else{
      var _xN/* s1Np */ = _xK/* s1Nc */.a,
      _xO/* s1Nq */ = E(_xJ/* s1Nb */);
      return (_xO/* s1Nq */._==0) ? new T1(1,I_mod/* EXTERNAL */(_xN/* s1Np */, I_fromInt/* EXTERNAL */(_xO/* s1Nq */.a))) : new T1(1,I_mod/* EXTERNAL */(_xN/* s1Np */, _xO/* s1Nq */.a));
    }
  }
},
_xP/* $fIntegralInteger_$cmod */ = function(_xQ/* svkO */, _xR/* svkP */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_xR/* svkP */, _v6/* GHC.Real.even1 */))){
    return new F(function(){return _xH/* GHC.Integer.Type.modInteger */(_xQ/* svkO */, _xR/* svkP */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_xS/* quotInteger */ = function(_xT/* s1On */, _xU/* s1Oo */){
  while(1){
    var _xV/* s1Op */ = E(_xT/* s1On */);
    if(!_xV/* s1Op */._){
      var _xW/* s1Or */ = E(_xV/* s1Op */.a);
      if(_xW/* s1Or */==( -2147483648)){
        _xT/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _xX/* s1Os */ = E(_xU/* s1Oo */);
        if(!_xX/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_xW/* s1Or */, _xX/* s1Os */.a));
        }else{
          _xT/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_xW/* s1Or */));
          _xU/* s1Oo */ = _xX/* s1Os */;
          continue;
        }
      }
    }else{
      var _xY/* s1OC */ = _xV/* s1Op */.a,
      _xZ/* s1OD */ = E(_xU/* s1Oo */);
      return (_xZ/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_xY/* s1OC */, I_fromInt/* EXTERNAL */(_xZ/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_xY/* s1OC */, _xZ/* s1OD */.a));
    }
  }
},
_y0/* $fIntegralInteger_$cquot */ = function(_y1/* svkX */, _y2/* svkY */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_y2/* svkY */, _v6/* GHC.Real.even1 */))){
    return new F(function(){return _xS/* GHC.Integer.Type.quotInteger */(_y1/* svkX */, _y2/* svkY */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_y3/* $fIntegralInteger_$cquotRem */ = function(_y4/* svkI */, _y5/* svkJ */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_y5/* svkJ */, _v6/* GHC.Real.even1 */))){
    var _y6/* svkL */ = B(_3k/* GHC.Integer.Type.quotRemInteger */(_y4/* svkI */, _y5/* svkJ */));
    return new T2(0,_y6/* svkL */.a,_y6/* svkL */.b);
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_y7/* remInteger */ = function(_y8/* s1NY */, _y9/* s1NZ */){
  while(1){
    var _ya/* s1O0 */ = E(_y8/* s1NY */);
    if(!_ya/* s1O0 */._){
      var _yb/* s1O2 */ = E(_ya/* s1O0 */.a);
      if(_yb/* s1O2 */==( -2147483648)){
        _y8/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */( -2147483648));
        continue;
      }else{
        var _yc/* s1O3 */ = E(_y9/* s1NZ */);
        if(!_yc/* s1O3 */._){
          return new T1(0,_yb/* s1O2 */%_yc/* s1O3 */.a);
        }else{
          _y8/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_yb/* s1O2 */));
          _y9/* s1NZ */ = _yc/* s1O3 */;
          continue;
        }
      }
    }else{
      var _yd/* s1Od */ = _ya/* s1O0 */.a,
      _ye/* s1Oe */ = E(_y9/* s1NZ */);
      return (_ye/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_yd/* s1Od */, I_fromInt/* EXTERNAL */(_ye/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_yd/* s1Od */, _ye/* s1Oe */.a));
    }
  }
},
_yf/* $fIntegralInteger_$crem */ = function(_yg/* svkU */, _yh/* svkV */){
  if(!B(_30/* GHC.Integer.Type.eqInteger */(_yh/* svkV */, _v6/* GHC.Real.even1 */))){
    return new F(function(){return _y7/* GHC.Integer.Type.remInteger */(_yg/* svkU */, _yh/* svkV */);});
  }else{
    return E(_2V/* GHC.Real.divZeroError */);
  }
},
_yi/* $fIntegralInteger_$ctoInteger */ = function(_yj/* svkB */){
  return E(_yj/* svkB */);
},
_yk/* $fNumInteger_$cfromInteger */ = function(_yl/* s6HS */){
  return E(_yl/* s6HS */);
},
_ym/* absInteger */ = function(_yn/* s1QP */){
  var _yo/* s1QQ */ = E(_yn/* s1QP */);
  if(!_yo/* s1QQ */._){
    var _yp/* s1QS */ = E(_yo/* s1QQ */.a);
    return (_yp/* s1QS */==( -2147483648)) ? E(_6a/* GHC.Integer.Type.lvl3 */) : (_yp/* s1QS */<0) ? new T1(0, -_yp/* s1QS */) : E(_yo/* s1QQ */);
  }else{
    var _yq/* s1QW */ = _yo/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_yq/* s1QW */, 0)>=0) ? E(_yo/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_yq/* s1QW */));
  }
},
_yr/* lvl */ = new T1(0,0),
_ys/* lvl1 */ = new T1(0, -1),
_yt/* signumInteger */ = function(_yu/* s1OO */){
  var _yv/* s1OP */ = E(_yu/* s1OO */);
  if(!_yv/* s1OP */._){
    var _yw/* s1OQ */ = _yv/* s1OP */.a;
    return (_yw/* s1OQ */>=0) ? (E(_yw/* s1OQ */)==0) ? E(_yr/* GHC.Integer.Type.lvl */) : E(_3M/* GHC.Integer.Type.log2I1 */) : E(_ys/* GHC.Integer.Type.lvl1 */);
  }else{
    var _yx/* s1OW */ = I_compareInt/* EXTERNAL */(_yv/* s1OP */.a, 0);
    return (_yx/* s1OW */<=0) ? (E(_yx/* s1OW */)==0) ? E(_yr/* GHC.Integer.Type.lvl */) : E(_ys/* GHC.Integer.Type.lvl1 */) : E(_3M/* GHC.Integer.Type.log2I1 */);
  }
},
_yy/* $fNumInteger */ = {_:0,a:_3b/* GHC.Integer.Type.plusInteger */,b:_5w/* GHC.Integer.Type.minusInteger */,c:_uG/* GHC.Integer.Type.timesInteger */,d:_6b/* GHC.Integer.Type.negateInteger */,e:_ym/* GHC.Integer.Type.absInteger */,f:_yt/* GHC.Integer.Type.signumInteger */,g:_yk/* GHC.Num.$fNumInteger_$cfromInteger */},
_yz/* neqInteger */ = function(_yA/* s1H2 */, _yB/* s1H3 */){
  var _yC/* s1H4 */ = E(_yA/* s1H2 */);
  if(!_yC/* s1H4 */._){
    var _yD/* s1H5 */ = _yC/* s1H4 */.a,
    _yE/* s1H6 */ = E(_yB/* s1H3 */);
    return (_yE/* s1H6 */._==0) ? _yD/* s1H5 */!=_yE/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_yE/* s1H6 */.a, _yD/* s1H5 */)==0) ? false : true;
  }else{
    var _yF/* s1Hc */ = _yC/* s1H4 */.a,
    _yG/* s1Hd */ = E(_yB/* s1H3 */);
    return (_yG/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_yF/* s1Hc */, _yG/* s1Hd */.a)==0) ? false : true : (I_compare/* EXTERNAL */(_yF/* s1Hc */, _yG/* s1Hd */.a)==0) ? false : true;
  }
},
_yH/* $fEqInteger */ = new T2(0,_30/* GHC.Integer.Type.eqInteger */,_yz/* GHC.Integer.Type.neqInteger */),
_yI/* $fOrdInteger_$cmax */ = function(_yJ/* s1HU */, _yK/* s1HV */){
  return (!B(_5h/* GHC.Integer.Type.leInteger */(_yJ/* s1HU */, _yK/* s1HV */))) ? E(_yJ/* s1HU */) : E(_yK/* s1HV */);
},
_yL/* $fOrdInteger_$cmin */ = function(_yM/* s1HR */, _yN/* s1HS */){
  return (!B(_5h/* GHC.Integer.Type.leInteger */(_yM/* s1HR */, _yN/* s1HS */))) ? E(_yN/* s1HS */) : E(_yM/* s1HR */);
},
_yO/* $fOrdInteger */ = {_:0,a:_yH/* GHC.Integer.Type.$fEqInteger */,b:_1N/* GHC.Integer.Type.compareInteger */,c:_3N/* GHC.Integer.Type.ltInteger */,d:_5h/* GHC.Integer.Type.leInteger */,e:_3E/* GHC.Integer.Type.gtInteger */,f:_wN/* GHC.Integer.Type.geInteger */,g:_yI/* GHC.Integer.Type.$fOrdInteger_$cmax */,h:_yL/* GHC.Integer.Type.$fOrdInteger_$cmin */},
_yP/* $fRealInteger_$s$cfromInteger */ = function(_yQ/* svhv */){
  return new T2(0,E(_yQ/* svhv */),E(_mq/* GHC.Real.$fEnumRatio1 */));
},
_yR/* $fRealInteger */ = new T3(0,_yy/* GHC.Num.$fNumInteger */,_yO/* GHC.Integer.Type.$fOrdInteger */,_yP/* GHC.Real.$fRealInteger_$s$cfromInteger */),
_yS/* $fIntegralInteger */ = {_:0,a:_yR/* GHC.Real.$fRealInteger */,b:_xi/* GHC.Enum.$fEnumInteger */,c:_y0/* GHC.Real.$fIntegralInteger_$cquot */,d:_yf/* GHC.Real.$fIntegralInteger_$crem */,e:_xr/* GHC.Real.$fIntegralInteger_$cdiv */,f:_xP/* GHC.Real.$fIntegralInteger_$cmod */,g:_y3/* GHC.Real.$fIntegralInteger_$cquotRem */,h:_xD/* GHC.Real.$fIntegralInteger_$cdivMod */,i:_yi/* GHC.Real.$fIntegralInteger_$ctoInteger */},
_yT/* $p2RealFrac */ = function(_yU/* svbS */){
  return E(E(_yU/* svbS */).b);
},
_yV/* floor */ = function(_yW/* svcB */){
  return E(E(_yW/* svcB */).g);
},
_yX/* fmod1 */ = new T1(0,1),
_yY/* fmod */ = function(_yZ/* s6Pi */, _z0/* s6Pj */, _z1/* s6Pk */){
  var _z2/* s6Pl */ = B(_yT/* GHC.Real.$p2RealFrac */(_yZ/* s6Pi */)),
  _z3/* s6Pm */ = B(_7i/* GHC.Real.$p1Fractional */(_z2/* s6Pl */)),
  _z4/* s6Pt */ = new T(function(){
    var _z5/* s6Ps */ = new T(function(){
      var _z6/* s6Pr */ = new T(function(){
        var _z7/* s6Pq */ = new T(function(){
          return B(A3(_yV/* GHC.Real.floor */,_yZ/* s6Pi */, _yS/* GHC.Real.$fIntegralInteger */, new T(function(){
            return B(A3(_9b/* GHC.Real./ */,_z2/* s6Pl */, _z0/* s6Pj */, _z1/* s6Pk */));
          })));
        });
        return B(A2(_91/* GHC.Num.fromInteger */,_z3/* s6Pm */, _z7/* s6Pq */));
      }),
      _z8/* s6Po */ = new T(function(){
        return B(A2(_6K/* GHC.Num.negate */,_z3/* s6Pm */, new T(function(){
          return B(A2(_91/* GHC.Num.fromInteger */,_z3/* s6Pm */, _yX/* Lib.Util.fmod1 */));
        })));
      });
      return B(A3(_7k/* GHC.Num.* */,_z3/* s6Pm */, _z8/* s6Po */, _z6/* s6Pr */));
    });
    return B(A3(_7k/* GHC.Num.* */,_z3/* s6Pm */, _z5/* s6Ps */, _z1/* s6Pk */));
  });
  return new F(function(){return A3(_6I/* GHC.Num.+ */,_z3/* s6Pm */, _z0/* s6Pj */, _z4/* s6Pt */);});
},
_z9/* square2 */ = 1.5707963267948966,
_za/* initial13 */ = function(_zb/* szcp */){
  return 0.2/Math.cos/* EXTERNAL */(B(_yY/* Lib.Util.fmod */(_wy/* GHC.Float.$fRealFracDouble */, _zb/* szcp */, _z9/* Lib.Object.square2 */))-0.7853981633974483);
},
_zc/* initial8 */ = 2,
_zd/* initial9 */ = 0.3,
_ze/* initial6 */ = new T(function(){
  var _zf/* szcv */ = B(_p8/* Lib.Object.$wmake */(_za/* Main.initial13 */, 1.2, _qD/* Main.initial12 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qC/* Main.initial10 */, _zd/* Main.initial9 */, _zc/* Main.initial8 */, _qr/* Main.initial11 */, _qr/* Main.initial11 */, _qy/* Main.initial7 */));
  return {_:0,a:E(_zf/* szcv */.a),b:E(_zf/* szcv */.b),c:E(_zf/* szcv */.c),d:E(_zf/* szcv */.d),e:E(_zf/* szcv */.e),f:E(_zf/* szcv */.f),g:E(_zf/* szcv */.g),h:_zf/* szcv */.h,i:_zf/* szcv */.i};
}),
_zg/* initial5 */ = new T2(1,_ze/* Main.initial6 */,_o/* GHC.Types.[] */),
_zh/* initial_ls */ = new T2(1,_qz/* Main.initial14 */,_zg/* Main.initial5 */),
_zi/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative range size"));
}),
_zj/* negRange */ = new T(function(){
  return B(err/* EXTERNAL */(_zi/* GHC.Arr.lvl36 */));
}),
_zk/* initial3 */ = function(_/* EXTERNAL */){
  var _zl/* szcH */ = B(_hf/* GHC.List.$wlenAcc */(_zh/* Main.initial_ls */, 0))-1|0,
  _zm/* szcI */ = function(_zn/* szcJ */){
    if(_zn/* szcJ */>=0){
      var _zo/* szcM */ = newArr/* EXTERNAL */(_zn/* szcJ */, _hl/* GHC.Arr.arrEleBottom */),
      _zp/* szcO */ = _zo/* szcM */,
      _zq/* szcP */ = E(_zn/* szcJ */);
      if(!_zq/* szcP */){
        return new T4(0,E(_qB/* Main.initial4 */),E(_zl/* szcH */),0,_zp/* szcO */);
      }else{
        var _zr/* szcR */ = function(_zs/* szd1 */, _zt/* szd2 */, _/* EXTERNAL */){
          while(1){
            var _zu/* szd4 */ = E(_zs/* szd1 */);
            if(!_zu/* szd4 */._){
              return E(_/* EXTERNAL */);
            }else{
              var _/* EXTERNAL */ = _zp/* szcO */[_zt/* szd2 */] = _zu/* szd4 */.a;
              if(_zt/* szd2 */!=(_zq/* szcP */-1|0)){
                var _zv/*  szd2 */ = _zt/* szd2 */+1|0;
                _zs/* szd1 */ = _zu/* szd4 */.b;
                _zt/* szd2 */ = _zv/*  szd2 */;
                continue;
              }else{
                return E(_/* EXTERNAL */);
              }
            }
          }
        },
        _/* EXTERNAL */ = B((function(_zw/* szcS */, _zx/* szcT */, _zy/* szcU */, _/* EXTERNAL */){
          var _/* EXTERNAL */ = _zp/* szcO */[_zy/* szcU */] = _zw/* szcS */;
          if(_zy/* szcU */!=(_zq/* szcP */-1|0)){
            return new F(function(){return _zr/* szcR */(_zx/* szcT */, _zy/* szcU */+1|0, _/* EXTERNAL */);});
          }else{
            return E(_/* EXTERNAL */);
          }
        })(_qz/* Main.initial14 */, _zg/* Main.initial5 */, 0, _/* EXTERNAL */));
        return new T4(0,E(_qB/* Main.initial4 */),E(_zl/* szcH */),_zq/* szcP */,_zp/* szcO */);
      }
    }else{
      return E(_zj/* GHC.Arr.negRange */);
    }
  };
  if(0>_zl/* szcH */){
    return new F(function(){return _zm/* szcI */(0);});
  }else{
    return new F(function(){return _zm/* szcI */(_zl/* szcH */+1|0);});
  }
},
_zz/* runSTRep */ = function(_zA/* sjpo */){
  var _zB/* sjpp */ = B(A1(_zA/* sjpo */,_/* EXTERNAL */));
  return E(_zB/* sjpp */);
},
_zC/* initial2 */ = new T(function(){
  return B(_zz/* GHC.ST.runSTRep */(_zk/* Main.initial3 */));
}),
_zD/* $fApplicativeIO1 */ = function(_zE/* s3he */, _zF/* s3hf */, _/* EXTERNAL */){
  var _zG/* s3hh */ = B(A1(_zE/* s3he */,_/* EXTERNAL */)),
  _zH/* s3hk */ = B(A1(_zF/* s3hf */,_/* EXTERNAL */));
  return _zG/* s3hh */;
},
_zI/* $fApplicativeIO2 */ = function(_zJ/* s3gs */, _zK/* s3gt */, _/* EXTERNAL */){
  var _zL/* s3gv */ = B(A1(_zJ/* s3gs */,_/* EXTERNAL */)),
  _zM/* s3gy */ = B(A1(_zK/* s3gt */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_zL/* s3gv */,_zM/* s3gy */));
  });
},
_zN/* $fFunctorIO1 */ = function(_zO/* s3gX */, _zP/* s3gY */, _/* EXTERNAL */){
  var _zQ/* s3h0 */ = B(A1(_zP/* s3gY */,_/* EXTERNAL */));
  return _zO/* s3gX */;
},
_zR/* $fFunctorIO2 */ = function(_zS/* s3gQ */, _zT/* s3gR */, _/* EXTERNAL */){
  var _zU/* s3gT */ = B(A1(_zT/* s3gR */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_zS/* s3gQ */,_zU/* s3gT */));
  });
},
_zV/* $fFunctorIO */ = new T2(0,_zR/* GHC.Base.$fFunctorIO2 */,_zN/* GHC.Base.$fFunctorIO1 */),
_zW/* returnIO1 */ = function(_zX/* s3g5 */, _/* EXTERNAL */){
  return _zX/* s3g5 */;
},
_zY/* thenIO1 */ = function(_zZ/* s3fZ */, _A0/* s3g0 */, _/* EXTERNAL */){
  var _A1/* s3g2 */ = B(A1(_zZ/* s3fZ */,_/* EXTERNAL */));
  return new F(function(){return A1(_A0/* s3g0 */,_/* EXTERNAL */);});
},
_A2/* $fApplicativeIO */ = new T5(0,_zV/* GHC.Base.$fFunctorIO */,_zW/* GHC.Base.returnIO1 */,_zI/* GHC.Base.$fApplicativeIO2 */,_zY/* GHC.Base.thenIO1 */,_zD/* GHC.Base.$fApplicativeIO1 */),
_A3/* $fIx(,)_$cunsafeRangeSize */ = function(_A4/* sLFI */){
  var _A5/* sLFJ */ = E(_A4/* sLFI */);
  return (E(_A5/* sLFJ */.b)-E(_A5/* sLFJ */.a)|0)+1|0;
},
_A6/* $fIxInt_$cinRange */ = function(_A7/* sLHc */, _A8/* sLHd */){
  var _A9/* sLHe */ = E(_A7/* sLHc */),
  _Aa/* sLHl */ = E(_A8/* sLHd */);
  return (E(_A9/* sLHe */.a)>_Aa/* sLHl */) ? false : _Aa/* sLHl */<=E(_A9/* sLHe */.b);
},
_Ab/* itos */ = function(_Ac/* sf6u */, _Ad/* sf6v */){
  var _Ae/* sf6x */ = jsShowI/* EXTERNAL */(_Ac/* sf6u */);
  return new F(function(){return _f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_Ae/* sf6x */), _Ad/* sf6v */);});
},
_Af/* $wshowSignedInt */ = function(_Ag/* sf6C */, _Ah/* sf6D */, _Ai/* sf6E */){
  if(_Ah/* sf6D */>=0){
    return new F(function(){return _Ab/* GHC.Show.itos */(_Ah/* sf6D */, _Ai/* sf6E */);});
  }else{
    if(_Ag/* sf6C */<=6){
      return new F(function(){return _Ab/* GHC.Show.itos */(_Ah/* sf6D */, _Ai/* sf6E */);});
    }else{
      return new T2(1,_71/* GHC.Show.shows8 */,new T(function(){
        var _Aj/* sf6K */ = jsShowI/* EXTERNAL */(_Ah/* sf6D */);
        return B(_f/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_Aj/* sf6K */), new T2(1,_70/* GHC.Show.shows7 */,_Ai/* sf6E */)));
      }));
    }
  }
},
_Ak/* $fShowInt_$cshow */ = function(_Al/* sfaP */){
  return new F(function(){return _Af/* GHC.Show.$wshowSignedInt */(0, E(_Al/* sfaP */), _o/* GHC.Types.[] */);});
},
_Am/* showSignedInt */ = function(_An/* sf6R */, _Ao/* sf6S */, _Ap/* sf6T */){
  return new F(function(){return _Af/* GHC.Show.$wshowSignedInt */(E(_An/* sf6R */), E(_Ao/* sf6S */), _Ap/* sf6T */);});
},
_Aq/* shows6 */ = function(_Ar/* sf9f */, _As/* sf9g */){
  return new F(function(){return _Af/* GHC.Show.$wshowSignedInt */(0, E(_Ar/* sf9f */), _As/* sf9g */);});
},
_At/* shows_$cshowList1 */ = function(_Au/* sfaI */, _Av/* sfaJ */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_Aq/* GHC.Show.shows6 */, _Au/* sfaI */, _Av/* sfaJ */);});
},
_Aw/* $fShowInt */ = new T3(0,_Am/* GHC.Show.showSignedInt */,_Ak/* GHC.Show.$fShowInt_$cshow */,_At/* GHC.Show.shows_$cshowList1 */),
_Ax/* $fIxChar1 */ = 0,
_Ay/* $fShow(,)1 */ = function(_Az/* sfbb */, _AA/* sfbc */, _AB/* sfbd */){
  return new F(function(){return A1(_Az/* sfbb */,new T2(1,_2y/* GHC.Show.showList__1 */,new T(function(){
    return B(A1(_AA/* sfbc */,_AB/* sfbd */));
  })));});
},
_AC/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("foldr1"));
}),
_AD/* lvl8 */ = new T(function(){
  return B(_lQ/* GHC.List.errorEmptyList */(_AC/* GHC.List.lvl7 */));
}),
_AE/* foldr1 */ = function(_AF/* sbKQ */, _AG/* sbKR */){
  var _AH/* sbKS */ = E(_AG/* sbKR */);
  if(!_AH/* sbKS */._){
    return E(_AD/* GHC.List.lvl8 */);
  }else{
    var _AI/* sbKT */ = _AH/* sbKS */.a,
    _AJ/* sbKV */ = E(_AH/* sbKS */.b);
    if(!_AJ/* sbKV */._){
      return E(_AI/* sbKT */);
    }else{
      return new F(function(){return A2(_AF/* sbKQ */,_AI/* sbKT */, new T(function(){
        return B(_AE/* GHC.List.foldr1 */(_AF/* sbKQ */, _AJ/* sbKV */));
      }));});
    }
  }
},
_AK/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" out of range "));
}),
_AL/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}.index: Index "));
}),
_AM/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ix{"));
}),
_AN/* lvl16 */ = new T2(1,_70/* GHC.Show.shows7 */,_o/* GHC.Types.[] */),
_AO/* lvl17 */ = new T2(1,_70/* GHC.Show.shows7 */,_AN/* GHC.Arr.lvl16 */),
_AP/* shows14 */ = 0,
_AQ/* showsPrec */ = function(_AR/* sf65 */){
  return E(E(_AR/* sf65 */).a);
},
_AS/* lvl18 */ = function(_AT/* sL5Y */, _AU/* sL5Z */, _AV/* sL60 */, _AW/* sL61 */, _AX/* sL62 */){
  var _AY/* sL6f */ = new T(function(){
    var _AZ/* sL6e */ = new T(function(){
      var _B0/* sL6c */ = new T(function(){
        var _B1/* sL6a */ = new T(function(){
          var _B2/* sL67 */ = new T(function(){
            return B(A3(_AE/* GHC.List.foldr1 */,_Ay/* GHC.Show.$fShow(,)1 */, new T2(1,new T(function(){
              return B(A3(_AQ/* GHC.Show.showsPrec */,_AV/* sL60 */, _AP/* GHC.Show.shows14 */, _AW/* sL61 */));
            }),new T2(1,new T(function(){
              return B(A3(_AQ/* GHC.Show.showsPrec */,_AV/* sL60 */, _AP/* GHC.Show.shows14 */, _AX/* sL62 */));
            }),_o/* GHC.Types.[] */)), _AO/* GHC.Arr.lvl17 */));
          });
          return B(_f/* GHC.Base.++ */(_AK/* GHC.Arr.lvl13 */, new T2(1,_71/* GHC.Show.shows8 */,new T2(1,_71/* GHC.Show.shows8 */,_B2/* sL67 */))));
        });
        return B(A(_AQ/* GHC.Show.showsPrec */,[_AV/* sL60 */, _Ax/* GHC.Arr.$fIxChar1 */, _AU/* sL5Z */, new T2(1,_70/* GHC.Show.shows7 */,_B1/* sL6a */)]));
      });
      return B(_f/* GHC.Base.++ */(_AL/* GHC.Arr.lvl14 */, new T2(1,_71/* GHC.Show.shows8 */,_B0/* sL6c */)));
    },1);
    return B(_f/* GHC.Base.++ */(_AT/* sL5Y */, _AZ/* sL6e */));
  },1);
  return new F(function(){return err/* EXTERNAL */(B(_f/* GHC.Base.++ */(_AM/* GHC.Arr.lvl15 */, _AY/* sL6f */)));});
},
_B3/* $wlvl4 */ = function(_B4/* sL6h */, _B5/* sL6i */, _B6/* sL6j */, _B7/* sL6k */, _B8/* sL6l */){
  return new F(function(){return _AS/* GHC.Arr.lvl18 */(_B4/* sL6h */, _B5/* sL6i */, _B8/* sL6l */, _B6/* sL6j */, _B7/* sL6k */);});
},
_B9/* lvl19 */ = function(_Ba/* sL6m */, _Bb/* sL6n */, _Bc/* sL6o */, _Bd/* sL6p */){
  var _Be/* sL6q */ = E(_Bc/* sL6o */);
  return new F(function(){return _B3/* GHC.Arr.$wlvl4 */(_Ba/* sL6m */, _Bb/* sL6n */, _Be/* sL6q */.a, _Be/* sL6q */.b, _Bd/* sL6p */);});
},
_Bf/* indexError */ = function(_Bg/* sLxR */, _Bh/* sLxS */, _Bi/* sLxT */, _Bj/* sLxU */){
  return new F(function(){return _B9/* GHC.Arr.lvl19 */(_Bj/* sLxU */, _Bi/* sLxT */, _Bh/* sLxS */, _Bg/* sLxR */);});
},
_Bk/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Int"));
}),
_Bl/* lvl40 */ = function(_Bm/* sLHv */, _Bn/* sLHw */){
  return new F(function(){return _Bf/* GHC.Arr.indexError */(_Aw/* GHC.Show.$fShowInt */, _Bm/* sLHv */, _Bn/* sLHw */, _Bk/* GHC.Arr.lvl20 */);});
},
_Bo/* $fIxInt_$cindex */ = function(_Bp/* sLHx */, _Bq/* sLHy */){
  var _Br/* sLHz */ = E(_Bp/* sLHx */),
  _Bs/* sLHC */ = E(_Br/* sLHz */.a),
  _Bt/* sLHG */ = E(_Bq/* sLHy */);
  if(_Bs/* sLHC */>_Bt/* sLHG */){
    return new F(function(){return _Bl/* GHC.Arr.lvl40 */(_Br/* sLHz */, _Bt/* sLHG */);});
  }else{
    if(_Bt/* sLHG */>E(_Br/* sLHz */.b)){
      return new F(function(){return _Bl/* GHC.Arr.lvl40 */(_Br/* sLHz */, _Bt/* sLHG */);});
    }else{
      return _Bt/* sLHG */-_Bs/* sLHC */|0;
    }
  }
},
_Bu/* $fIxInt_$crange */ = function(_Bv/* sLHN */){
  var _Bw/* sLHO */ = E(_Bv/* sLHN */);
  return new F(function(){return _sn/* GHC.Enum.$fEnumInt_$cenumFromTo */(_Bw/* sLHO */.a, _Bw/* sLHO */.b);});
},
_Bx/* $fIxInt_$crangeSize */ = function(_By/* sLH0 */){
  var _Bz/* sLH1 */ = E(_By/* sLH0 */),
  _BA/* sLH4 */ = E(_Bz/* sLH1 */.a),
  _BB/* sLH6 */ = E(_Bz/* sLH1 */.b);
  return (_BA/* sLH4 */>_BB/* sLH6 */) ? E(_Ax/* GHC.Arr.$fIxChar1 */) : (_BB/* sLH6 */-_BA/* sLH4 */|0)+1|0;
},
_BC/* $fIxInt_$cunsafeIndex */ = function(_BD/* sLHq */, _BE/* sLHr */){
  return new F(function(){return _tM/* GHC.Num.$fNumInt_$c- */(_BE/* sLHr */, E(_BD/* sLHq */).a);});
},
_BF/* $fIxInt */ = {_:0,a:_uC/* GHC.Classes.$fOrdInt */,b:_Bu/* GHC.Arr.$fIxInt_$crange */,c:_Bo/* GHC.Arr.$fIxInt_$cindex */,d:_BC/* GHC.Arr.$fIxInt_$cunsafeIndex */,e:_A6/* GHC.Arr.$fIxInt_$cinRange */,f:_Bx/* GHC.Arr.$fIxInt_$crangeSize */,g:_A3/* GHC.Arr.$fIx(,)_$cunsafeRangeSize */},
_BG/* : */ = function(_BH/* B2 */, _BI/* B1 */){
  return new T2(1,_BH/* B2 */,_BI/* B1 */);
},
_BJ/* bounds */ = function(_BK/* sLl6 */, _BL/* sLl7 */){
  var _BM/* sLl8 */ = E(_BL/* sLl7 */);
  return new T2(0,_BM/* sLl8 */.a,_BM/* sLl8 */.b);
},
_BN/* rangeSize */ = function(_BO/* sL3K */){
  return E(E(_BO/* sL3K */).f);
},
_BP/* listArray */ = function(_BQ/* sLrT */, _BR/* sLrU */, _BS/* sLrV */){
  var _BT/* sLrW */ = E(_BR/* sLrU */),
  _BU/* sLrX */ = _BT/* sLrW */.a,
  _BV/* sLrY */ = _BT/* sLrW */.b,
  _BW/* sLsy */ = function(_/* EXTERNAL */){
    var _BX/* sLs0 */ = B(A2(_BN/* GHC.Arr.rangeSize */,_BQ/* sLrT */, _BT/* sLrW */));
    if(_BX/* sLs0 */>=0){
      var _BY/* sLs4 */ = newArr/* EXTERNAL */(_BX/* sLs0 */, _hl/* GHC.Arr.arrEleBottom */),
      _BZ/* sLs6 */ = _BY/* sLs4 */,
      _C0/* sLs7 */ = E(_BX/* sLs0 */);
      if(!_C0/* sLs7 */){
        return new T(function(){
          return new T4(0,E(_BU/* sLrX */),E(_BV/* sLrY */),0,_BZ/* sLs6 */);
        });
      }else{
        var _C1/* sLs8 */ = function(_C2/* sLs9 */, _C3/* sLsa */, _/* EXTERNAL */){
          while(1){
            var _C4/* sLsc */ = E(_C2/* sLs9 */);
            if(!_C4/* sLsc */._){
              return E(_/* EXTERNAL */);
            }else{
              var _/* EXTERNAL */ = _BZ/* sLs6 */[_C3/* sLsa */] = _C4/* sLsc */.a;
              if(_C3/* sLsa */!=(_C0/* sLs7 */-1|0)){
                var _C5/*  sLsa */ = _C3/* sLsa */+1|0;
                _C2/* sLs9 */ = _C4/* sLsc */.b;
                _C3/* sLsa */ = _C5/*  sLsa */;
                continue;
              }else{
                return E(_/* EXTERNAL */);
              }
            }
          }
        },
        _/* EXTERNAL */ = B(_C1/* sLs8 */(_BS/* sLrV */, 0, _/* EXTERNAL */));
        return new T(function(){
          return new T4(0,E(_BU/* sLrX */),E(_BV/* sLrY */),_C0/* sLs7 */,_BZ/* sLs6 */);
        });
      }
    }else{
      return E(_zj/* GHC.Arr.negRange */);
    }
  };
  return new F(function(){return _zz/* GHC.ST.runSTRep */(_BW/* sLsy */);});
},
_C6/* $w$ctraverse */ = function(_C7/* s5AkJ */, _C8/* s5AkK */, _C9/* s5AkL */, _Ca/* s5AkM */){
  var _Cb/* s5Alb */ = new T(function(){
    var _Cc/* s5AkQ */ = E(_Ca/* s5AkM */),
    _Cd/* s5AkV */ = _Cc/* s5AkQ */.c-1|0,
    _Ce/* s5AkW */ = new T(function(){
      return B(A2(_cX/* GHC.Base.pure */,_C8/* s5AkK */, _o/* GHC.Types.[] */));
    });
    if(0<=_Cd/* s5AkV */){
      var _Cf/* s5AkZ */ = new T(function(){
        return B(_97/* GHC.Base.$p1Applicative */(_C8/* s5AkK */));
      }),
      _Cg/* s5Al0 */ = function(_Ch/* s5Al1 */){
        var _Ci/* s5Al6 */ = new T(function(){
          var _Cj/* s5Al5 */ = new T(function(){
            return B(A1(_C9/* s5AkL */,new T(function(){
              return E(_Cc/* s5AkQ */.d[_Ch/* s5Al1 */]);
            })));
          });
          return B(A3(_9f/* GHC.Base.fmap */,_Cf/* s5AkZ */, _BG/* GHC.Types.: */, _Cj/* s5Al5 */));
        });
        return new F(function(){return A3(_9d/* GHC.Base.<*> */,_C8/* s5AkK */, _Ci/* s5Al6 */, new T(function(){
          if(_Ch/* s5Al1 */!=_Cd/* s5AkV */){
            return B(_Cg/* s5Al0 */(_Ch/* s5Al1 */+1|0));
          }else{
            return E(_Ce/* s5AkW */);
          }
        }));});
      };
      return B(_Cg/* s5Al0 */(0));
    }else{
      return E(_Ce/* s5AkW */);
    }
  }),
  _Ck/* s5AkO */ = new T(function(){
    return B(_BJ/* GHC.Arr.bounds */(_C7/* s5AkJ */, _Ca/* s5AkM */));
  });
  return new F(function(){return A3(_9f/* GHC.Base.fmap */,B(_97/* GHC.Base.$p1Applicative */(_C8/* s5AkK */)), function(_Cl/* B1 */){
    return new F(function(){return _BP/* GHC.Arr.listArray */(_C7/* s5AkJ */, _Ck/* s5AkO */, _Cl/* B1 */);});
  }, _Cb/* s5Alb */);});
},
_Cm/* toAny */ = function(_Cn/* sbDZ */){
  return E(E(_Cn/* sbDZ */).a);
},
_Co/* $fFFI(->)_$c__ffi */ = function(_Cp/* siUQ */, _Cq/* siUR */, _Cr/* siUS */, _Cs/* siUT */, _Ct/* siUU */){
  var _Cu/* siUX */ = B(A2(_Cm/* Haste.Prim.Any.toAny */,_Cp/* siUQ */, E(_Ct/* siUU */)));
  return new F(function(){return A2(_Cq/* siUR */,_Cr/* siUS */, new T2(1,_Cu/* siUX */,E(_Cs/* siUT */)));});
},
_Cv/* $fToAnyObject1 */ = "outline",
_Cw/* $fToAnyObject2 */ = "polygon",
_Cx/* $w$ctoAny */ = function(_Cy/* sgp8 */){
  return new F(function(){return _jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,new T(function(){
    return E(_Cy/* sgp8 */).h;
  })),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,new T(function(){
    return E(_Cy/* sgp8 */).i;
  })),_o/* GHC.Types.[] */)));});
},
_Cz/* $fToAnyObject_$ctoAny */ = function(_CA/* sgpz */){
  return new F(function(){return _Cx/* Lib.Object.$w$ctoAny */(_CA/* sgpz */);});
},
_CB/* $fToAnyObject_$clistToAny */ = function(_CC/* sgpB */){
  return new F(function(){return __lst2arr/* EXTERNAL */(B(_jW/* GHC.Base.map */(_Cz/* Lib.Object.$fToAnyObject_$ctoAny */, _CC/* sgpB */)));});
},
_CD/* $fToAnyObject */ = new T2(0,_Cz/* Lib.Object.$fToAnyObject_$ctoAny */,_CB/* Lib.Object.$fToAnyObject_$clistToAny */),
_CE/* $fFromAny()2 */ = function(_CF/* sc0A */, _/* EXTERNAL */){
  var _CG/* sc0C */ = E(_CF/* sc0A */);
  if(!_CG/* sc0C */._){
    return _o/* GHC.Types.[] */;
  }else{
    var _CH/* sc0F */ = B(_CE/* Haste.Prim.Any.$fFromAny()2 */(_CG/* sc0C */.b, _/* EXTERNAL */));
    return new T2(1,_jz/* GHC.Tuple.() */,_CH/* sc0F */);
  }
},
_CI/* $wa */ = function(_CJ/* sc0J */, _/* EXTERNAL */){
  var _CK/* sc0M */ = __arr2lst/* EXTERNAL */(0, _CJ/* sc0J */);
  return new F(function(){return _CE/* Haste.Prim.Any.$fFromAny()2 */(_CK/* sc0M */, _/* EXTERNAL */);});
},
_CL/* $fFromAny()1 */ = function(_CM/* sc0Q */, _/* EXTERNAL */){
  return new F(function(){return _CI/* Haste.Prim.Any.$wa */(E(_CM/* sc0Q */), _/* EXTERNAL */);});
},
_CN/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _jz/* GHC.Tuple.() */;
},
_CO/* $fFromAny()3 */ = function(_CP/* sbTt */, _/* EXTERNAL */){
  return new F(function(){return _CN/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_CQ/* $fFromAny() */ = new T2(0,_CO/* Haste.Prim.Any.$fFromAny()3 */,_CL/* Haste.Prim.Any.$fFromAny()1 */),
_CR/* fromAny */ = function(_CS/* sbDR */){
  return E(E(_CS/* sbDR */).a);
},
_CT/* $wa1 */ = function(_CU/* siUp */, _CV/* siUq */, _CW/* siUr */, _/* EXTERNAL */){
  var _CX/* siUw */ = __apply/* EXTERNAL */(_CV/* siUq */, E(_CW/* siUr */));
  return new F(function(){return A3(_CR/* Haste.Prim.Any.fromAny */,_CU/* siUp */, _CX/* siUw */, _/* EXTERNAL */);});
},
_CY/* a1 */ = function(_CZ/* siUA */, _D0/* siUB */, _D1/* siUC */, _/* EXTERNAL */){
  return new F(function(){return _CT/* Haste.Prim.Foreign.$wa1 */(_CZ/* siUA */, E(_D0/* siUB */), _D1/* siUC */, _/* EXTERNAL */);});
},
_D2/* ffiio */ = function(_D3/* B4 */, _D4/* B3 */, _D5/* B2 */, _/* EXTERNAL */){
  return new F(function(){return _CY/* Haste.Prim.Foreign.a1 */(_D3/* B4 */, _D4/* B3 */, _D5/* B2 */, _/* EXTERNAL */);});
},
_D6/* $sffi2 */ = function(_D7/* B3 */, _D8/* B2 */, _/* EXTERNAL */){
  return new F(function(){return _D2/* Haste.Prim.Foreign.ffiio */(_CQ/* Haste.Prim.Any.$fFromAny() */, _D7/* B3 */, _D8/* B2 */, _/* EXTERNAL */);});
},
_D9/* drawObject_f1 */ = new T(function(){
  return eval/* EXTERNAL */("drawObject");
}),
_Da/* drawObject */ = function(_Db/* B1 */){
  return new F(function(){return _Co/* Haste.Prim.Foreign.$fFFI(->)_$c__ffi */(_CD/* Lib.Object.$fToAnyObject */, _D6/* Lib.Object.$sffi2 */, _D9/* Lib.Object.drawObject_f1 */, _o/* GHC.Types.[] */, _Db/* B1 */);});
},
_Dc/* draw_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(draw)");
}),
_Dd/* $fApplicativeIdentity2 */ = function(_De/* s6Rmj */){
  return E(_De/* s6Rmj */);
},
_Df/* $fApplicativeIdentity3 */ = function(_Dg/* s6RlP */){
  return E(_Dg/* s6RlP */);
},
_Dh/* $fApplicativeIdentity_$c*> */ = function(_Di/* s6Ro6 */, _Dj/* s6Ro7 */){
  return E(_Dj/* s6Ro7 */);
},
_Dk/* $fFunctorIdentity1 */ = function(_Dl/* s6RlM */, _Dm/* s6RlN */){
  return E(_Dl/* s6RlM */);
},
_Dn/* $fFunctorIdentity2 */ = function(_Do/* s6Rmk */){
  return E(_Do/* s6Rmk */);
},
_Dp/* $fFunctorIdentity */ = new T2(0,_Dn/* Data.Functor.Identity.$fFunctorIdentity2 */,_Dk/* Data.Functor.Identity.$fFunctorIdentity1 */),
_Dq/* a1 */ = function(_Dr/* s6Ro8 */, _Ds/* s6Ro9 */){
  return E(_Dr/* s6Ro8 */);
},
_Dt/* $fApplicativeIdentity */ = new T5(0,_Dp/* Data.Functor.Identity.$fFunctorIdentity */,_Df/* Data.Functor.Identity.$fApplicativeIdentity3 */,_Dd/* Data.Functor.Identity.$fApplicativeIdentity2 */,_Dh/* Data.Functor.Identity.$fApplicativeIdentity_$c*> */,_Dq/* Data.Functor.Identity.a1 */),
_Du/* $fFromAnyContactPoint10 */ = "c2y",
_Dv/* $fFromAnyContactPoint11 */ = "c2x",
_Dw/* $fFromAnyContactPoint12 */ = "c1y",
_Dx/* $fFromAnyContactPoint13 */ = "c1x",
_Dy/* $fFromAnyContactPoint4 */ = "n2z",
_Dz/* $fFromAnyContactPoint5 */ = "n2y",
_DA/* $fFromAnyContactPoint6 */ = "n2x",
_DB/* $fFromAnyContactPoint7 */ = "n1z",
_DC/* $fFromAnyContactPoint8 */ = "n1y",
_DD/* $fFromAnyContactPoint9 */ = "n1x",
_DE/* $wa1 */ = function(_DF/* snzq */, _/* EXTERNAL */){
  var _DG/* snzv */ = __get/* EXTERNAL */(_DF/* snzq */, E(_Dx/* Lib.Constraint.$fFromAnyContactPoint13 */)),
  _DH/* snzB */ = __get/* EXTERNAL */(_DF/* snzq */, E(_Dw/* Lib.Constraint.$fFromAnyContactPoint12 */)),
  _DI/* snzH */ = __get/* EXTERNAL */(_DF/* snzq */, E(_Dv/* Lib.Constraint.$fFromAnyContactPoint11 */)),
  _DJ/* snzN */ = __get/* EXTERNAL */(_DF/* snzq */, E(_Du/* Lib.Constraint.$fFromAnyContactPoint10 */)),
  _DK/* snzT */ = __get/* EXTERNAL */(_DF/* snzq */, E(_DD/* Lib.Constraint.$fFromAnyContactPoint9 */)),
  _DL/* snzZ */ = __get/* EXTERNAL */(_DF/* snzq */, E(_DC/* Lib.Constraint.$fFromAnyContactPoint8 */)),
  _DM/* snA5 */ = __get/* EXTERNAL */(_DF/* snzq */, E(_DB/* Lib.Constraint.$fFromAnyContactPoint7 */)),
  _DN/* snAb */ = __get/* EXTERNAL */(_DF/* snzq */, E(_DA/* Lib.Constraint.$fFromAnyContactPoint6 */)),
  _DO/* snAh */ = __get/* EXTERNAL */(_DF/* snzq */, E(_Dz/* Lib.Constraint.$fFromAnyContactPoint5 */)),
  _DP/* snAn */ = __get/* EXTERNAL */(_DF/* snzq */, E(_Dy/* Lib.Constraint.$fFromAnyContactPoint4 */));
  return new T4(0,E(new T2(0,E(_DG/* snzv */),E(_DH/* snzB */))),E(new T2(0,E(_DI/* snzH */),E(_DJ/* snzN */))),E(new T3(0,E(_DK/* snzT */),E(_DL/* snzZ */),E(_DM/* snA5 */))),E(new T3(0,E(_DN/* snAb */),E(_DO/* snAh */),E(_DP/* snAn */))));
},
_DQ/* $fFromAnyContactPoint2 */ = function(_DR/* snGD */, _/* EXTERNAL */){
  var _DS/* snGF */ = E(_DR/* snGD */);
  if(!_DS/* snGF */._){
    return _o/* GHC.Types.[] */;
  }else{
    var _DT/* snGK */ = B(_DE/* Lib.Constraint.$wa1 */(E(_DS/* snGF */.a), _/* EXTERNAL */)),
    _DU/* snGN */ = B(_DQ/* Lib.Constraint.$fFromAnyContactPoint2 */(_DS/* snGF */.b, _/* EXTERNAL */));
    return new T2(1,_DT/* snGK */,_DU/* snGN */);
  }
},
_DV/* go */ = function(_DW/* swor */){
  var _DX/* swos */ = E(_DW/* swor */);
  if(!_DX/* swos */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_DX/* swos */.a, new T(function(){
      return B(_DV/* Lib.Physics.go */(_DX/* swos */.b));
    },1));});
  }
},
_DY/* $sgo1 */ = function(_DZ/* swoo */, _E0/* swop */){
  return new F(function(){return _f/* GHC.Base.++ */(_DZ/* swoo */, new T(function(){
    return B(_DV/* Lib.Physics.go */(_E0/* swop */));
  },1));});
},
_E1/* $w$c* */ = function(_E2/* sghT */, _E3/* sghU */, _E4/* sghV */, _E5/* sghW */, _E6/* sghX */, _E7/* sghY */, _E8/* sghZ */, _E9/* sgi0 */, _Ea/* sgi1 */){
  var _Eb/* sgi2 */ = B(_7k/* GHC.Num.* */(_E2/* sghT */));
  return new T2(0,new T3(0,E(B(A1(B(A1(_Eb/* sgi2 */,_E3/* sghU */)),_E7/* sghY */))),E(B(A1(B(A1(_Eb/* sgi2 */,_E4/* sghV */)),_E8/* sghZ */))),E(B(A1(B(A1(_Eb/* sgi2 */,_E5/* sghW */)),_E9/* sgi0 */)))),B(A1(B(A1(_Eb/* sgi2 */,_E6/* sghX */)),_Ea/* sgi1 */)));
},
_Ec/* $w$c+ */ = function(_Ed/* sgiw */, _Ee/* sgix */, _Ef/* sgiy */, _Eg/* sgiz */, _Eh/* sgiA */, _Ei/* sgiB */, _Ej/* sgiC */, _Ek/* sgiD */, _El/* sgiE */){
  var _Em/* sgiF */ = B(_6I/* GHC.Num.+ */(_Ed/* sgiw */));
  return new T2(0,new T3(0,E(B(A1(B(A1(_Em/* sgiF */,_Ee/* sgix */)),_Ei/* sgiB */))),E(B(A1(B(A1(_Em/* sgiF */,_Ef/* sgiy */)),_Ej/* sgiC */))),E(B(A1(B(A1(_Em/* sgiF */,_Eg/* sgiz */)),_Ek/* sgiD */)))),B(A1(B(A1(_Em/* sgiF */,_Eh/* sgiA */)),_El/* sgiE */)));
},
_En/* dt */ = 5.0e-2,
_Eo/* $wa */ = function(_Ep/* swna */, _Eq/* swnb */, _Er/* swnc */, _Es/* swnd */, _Et/* swne */, _Eu/* swnf */, _Ev/* swng */, _Ew/* swnh */, _Ex/* swni */, _Ey/* swnj */, _Ez/* swnk */, _EA/* swnl */, _EB/* swnm */, _EC/* swnn */, _ED/* swno */, _EE/* swnp */, _EF/* swnq */){
  var _EG/* swnr */ = B(_E1/* Lib.Object.$w$c* */(_il/* GHC.Float.$fNumDouble */, _Ew/* swnh */, _Ex/* swni */, _Ey/* swnj */, _Ez/* swnk */, _En/* Lib.Physics.dt */, _En/* Lib.Physics.dt */, _En/* Lib.Physics.dt */, _En/* Lib.Physics.dt */)),
  _EH/* swnu */ = E(_EG/* swnr */.a),
  _EI/* swny */ = B(_Ec/* Lib.Object.$w$c+ */(_il/* GHC.Float.$fNumDouble */, _Es/* swnd */, _Et/* swne */, _Eu/* swnf */, _Ev/* swng */, _EH/* swnu */.a, _EH/* swnu */.b, _EH/* swnu */.c, _EG/* swnr */.b)),
  _EJ/* swnB */ = E(_EI/* swny */.a);
  return new F(function(){return _op/* Lib.Object.$wfitO */(_Ep/* swna */, _Eq/* swnb */, _Er/* swnc */, _EJ/* swnB */.a, _EJ/* swnB */.b, _EJ/* swnB */.c, _EI/* swny */.b, _Ew/* swnh */, _Ex/* swni */, _Ey/* swnj */, _Ez/* swnk */, _EA/* swnl */, _EB/* swnm */, _EC/* swnn */, _ED/* swno */, _EE/* swnp */, _EF/* swnq */);});
},
_EK/* a17 */ = function(_EL/* swmj */){
  var _EM/* swmk */ = E(_EL/* swmj */),
  _EN/* swmu */ = E(_EM/* swmk */.b),
  _EO/* swmy */ = E(_EM/* swmk */.e),
  _EP/* swmB */ = E(_EO/* swmy */.a),
  _EQ/* swmL */ = E(_EM/* swmk */.g),
  _ER/* swmP */ = B(_l9/* Lib.World.$wperpTo */(_iR/* GHC.Float.$fFloatingDouble */, _EN/* swmu */.a, _EN/* swmu */.b, _EN/* swmu */.c, _EQ/* swmL */.a, _EQ/* swmL */.b, _EQ/* swmL */.c));
  return {_:0,a:E(_EM/* swmk */.a),b:E(_EN/* swmu */),c:E(_EM/* swmk */.c),d:E(_EM/* swmk */.d),e:E(new T2(0,E(new T3(0,E(_EP/* swmB */.a)+E(_ER/* swmP */.a)*5.0e-2,E(_EP/* swmB */.b)+E(_ER/* swmP */.b)*5.0e-2,E(_EP/* swmB */.c)+E(_ER/* swmP */.c)*5.0e-2)),E(_EO/* swmy */.b))),f:E(_EM/* swmk */.f),g:E(_EQ/* swmL */),h:_EM/* swmk */.h,i:_EM/* swmk */.i};
},
_ES/* a18 */ = function(_ET/* swnF */){
  var _EU/* swnG */ = E(_ET/* swnF */),
  _EV/* swnQ */ = E(_EU/* swnG */.d),
  _EW/* swnT */ = E(_EV/* swnQ */.a),
  _EX/* swnX */ = E(_EU/* swnG */.e),
  _EY/* swo0 */ = E(_EX/* swnX */.a),
  _EZ/* swo4 */ = E(_EU/* swnG */.f),
  _F0/* swo8 */ = B(_Eo/* Lib.Physics.$wa */(_EU/* swnG */.a, _EU/* swnG */.b, _EU/* swnG */.c, _EW/* swnT */.a, _EW/* swnT */.b, _EW/* swnT */.c, _EV/* swnQ */.b, _EY/* swo0 */.a, _EY/* swo0 */.b, _EY/* swo0 */.c, _EX/* swnX */.b, _EZ/* swo4 */.a, _EZ/* swo4 */.b, _EZ/* swo4 */.c, _EU/* swnG */.g, _EU/* swnG */.h, _EU/* swnG */.i));
  return {_:0,a:E(_F0/* swo8 */.a),b:E(_F0/* swo8 */.b),c:E(_F0/* swo8 */.c),d:E(_F0/* swo8 */.d),e:E(_F0/* swo8 */.e),f:E(_F0/* swo8 */.f),g:E(_F0/* swo8 */.g),h:_F0/* swo8 */.h,i:_F0/* swo8 */.i};
},
_F1/* a20 */ = function(_F2/* swoE */, _F3/* swoF */, _/* EXTERNAL */){
  var _F4/* swoH */ = E(_F2/* swoE */);
  if(!_F4/* swoH */._){
    return new T2(0,_o/* GHC.Types.[] */,_F3/* swoF */);
  }else{
    var _F5/* swoL */ = E(_F4/* swoH */.a),
    _F6/* swoQ */ = B(_F1/* Lib.Physics.a20 */(_F4/* swoH */.b, _F3/* swoF */, _/* EXTERNAL */));
    return new T2(0,new T2(1,_jz/* GHC.Tuple.() */,new T(function(){
      return E(E(_F6/* swoQ */).a);
    })),new T(function(){
      return E(E(_F6/* swoQ */).b);
    }));
  }
},
_F7/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("collide");
}),
_F8/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_F9/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_Fa/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_Fb/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_F8/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_F9/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_Fa/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_Fc/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_Fb/* GHC.IO.Exception.$fExceptionIOException_wild */,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),
_Fd/* $fExceptionIOException3 */ = function(_Fe/* s3MW8 */){
  return E(_Fc/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_Ff/* $fExceptionIOException_$cfromException */ = function(_Fg/* s3N1e */){
  var _Fh/* s3N1f */ = E(_Fg/* s3N1e */);
  return new F(function(){return _28/* Data.Typeable.cast */(B(_26/* GHC.Exception.$p1Exception */(_Fh/* s3N1f */.a)), _Fd/* GHC.IO.Exception.$fExceptionIOException3 */, _Fh/* s3N1f */.b);});
},
_Fi/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_Fj/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_Fk/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_Fl/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_Fm/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_Fn/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_Fo/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_Fp/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_Fq/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_Fr/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_Fs/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_Ft/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_Fu/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_Fv/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_Fw/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_Fx/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_Fy/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_Fz/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_FA/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_FB/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_FC/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_FD/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_FE/* $w$cshowsPrec3 */ = function(_FF/* s3N03 */, _FG/* s3N04 */){
  switch(E(_FF/* s3N03 */)){
    case 0:
      return new F(function(){return _f/* GHC.Base.++ */(_Fv/* GHC.IO.Exception.lvl18 */, _FG/* s3N04 */);});
      break;
    case 1:
      return new F(function(){return _f/* GHC.Base.++ */(_Fu/* GHC.IO.Exception.lvl17 */, _FG/* s3N04 */);});
      break;
    case 2:
      return new F(function(){return _f/* GHC.Base.++ */(_Ft/* GHC.IO.Exception.lvl16 */, _FG/* s3N04 */);});
      break;
    case 3:
      return new F(function(){return _f/* GHC.Base.++ */(_Fs/* GHC.IO.Exception.lvl15 */, _FG/* s3N04 */);});
      break;
    case 4:
      return new F(function(){return _f/* GHC.Base.++ */(_Fr/* GHC.IO.Exception.lvl14 */, _FG/* s3N04 */);});
      break;
    case 5:
      return new F(function(){return _f/* GHC.Base.++ */(_Fq/* GHC.IO.Exception.lvl13 */, _FG/* s3N04 */);});
      break;
    case 6:
      return new F(function(){return _f/* GHC.Base.++ */(_Fp/* GHC.IO.Exception.lvl12 */, _FG/* s3N04 */);});
      break;
    case 7:
      return new F(function(){return _f/* GHC.Base.++ */(_Fo/* GHC.IO.Exception.lvl11 */, _FG/* s3N04 */);});
      break;
    case 8:
      return new F(function(){return _f/* GHC.Base.++ */(_Fn/* GHC.IO.Exception.lvl10 */, _FG/* s3N04 */);});
      break;
    case 9:
      return new F(function(){return _f/* GHC.Base.++ */(_FD/* GHC.IO.Exception.lvl9 */, _FG/* s3N04 */);});
      break;
    case 10:
      return new F(function(){return _f/* GHC.Base.++ */(_FC/* GHC.IO.Exception.lvl8 */, _FG/* s3N04 */);});
      break;
    case 11:
      return new F(function(){return _f/* GHC.Base.++ */(_FB/* GHC.IO.Exception.lvl7 */, _FG/* s3N04 */);});
      break;
    case 12:
      return new F(function(){return _f/* GHC.Base.++ */(_FA/* GHC.IO.Exception.lvl6 */, _FG/* s3N04 */);});
      break;
    case 13:
      return new F(function(){return _f/* GHC.Base.++ */(_Fz/* GHC.IO.Exception.lvl5 */, _FG/* s3N04 */);});
      break;
    case 14:
      return new F(function(){return _f/* GHC.Base.++ */(_Fy/* GHC.IO.Exception.lvl4 */, _FG/* s3N04 */);});
      break;
    case 15:
      return new F(function(){return _f/* GHC.Base.++ */(_Fx/* GHC.IO.Exception.lvl3 */, _FG/* s3N04 */);});
      break;
    case 16:
      return new F(function(){return _f/* GHC.Base.++ */(_Fw/* GHC.IO.Exception.lvl2 */, _FG/* s3N04 */);});
      break;
    case 17:
      return new F(function(){return _f/* GHC.Base.++ */(_Fm/* GHC.IO.Exception.lvl1 */, _FG/* s3N04 */);});
      break;
    default:
      return new F(function(){return _f/* GHC.Base.++ */(_Fl/* GHC.IO.Exception.lvl */, _FG/* s3N04 */);});
  }
},
_FH/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_FI/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_FJ/* $w$cshowsPrec2 */ = function(_FK/* s3N0c */, _FL/* s3N0d */, _FM/* s3N0e */, _FN/* s3N0f */, _FO/* s3N0g */, _FP/* s3N0h */){
  var _FQ/* s3N0i */ = new T(function(){
    var _FR/* s3N0j */ = new T(function(){
      var _FS/* s3N0p */ = new T(function(){
        var _FT/* s3N0k */ = E(_FN/* s3N0f */);
        if(!_FT/* s3N0k */._){
          return E(_FP/* s3N0h */);
        }else{
          var _FU/* s3N0o */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_FT/* s3N0k */, new T(function(){
              return B(_f/* GHC.Base.++ */(_Fj/* GHC.IO.Exception.$fExceptionIOException1 */, _FP/* s3N0h */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_Fk/* GHC.IO.Exception.$fExceptionIOException2 */, _FU/* s3N0o */));
        }
      },1);
      return B(_FE/* GHC.IO.Exception.$w$cshowsPrec3 */(_FL/* s3N0d */, _FS/* s3N0p */));
    }),
    _FV/* s3N0q */ = E(_FM/* s3N0e */);
    if(!_FV/* s3N0q */._){
      return E(_FR/* s3N0j */);
    }else{
      return B(_f/* GHC.Base.++ */(_FV/* s3N0q */, new T(function(){
        return B(_f/* GHC.Base.++ */(_Fi/* GHC.IO.Exception.$fExceptionArrayException2 */, _FR/* s3N0j */));
      },1)));
    }
  }),
  _FW/* s3N0u */ = E(_FO/* s3N0g */);
  if(!_FW/* s3N0u */._){
    var _FX/* s3N0v */ = E(_FK/* s3N0c */);
    if(!_FX/* s3N0v */._){
      return E(_FQ/* s3N0i */);
    }else{
      var _FY/* s3N0x */ = E(_FX/* s3N0v */.a);
      if(!_FY/* s3N0x */._){
        var _FZ/* s3N0C */ = new T(function(){
          var _G0/* s3N0B */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_FH/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_f/* GHC.Base.++ */(_Fi/* GHC.IO.Exception.$fExceptionArrayException2 */, _FQ/* s3N0i */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_FY/* s3N0x */.a, _G0/* s3N0B */));
        },1);
        return new F(function(){return _f/* GHC.Base.++ */(_FI/* GHC.IO.Handle.Types.showHandle2 */, _FZ/* s3N0C */);});
      }else{
        var _G1/* s3N0I */ = new T(function(){
          var _G2/* s3N0H */ = new T(function(){
            return B(_f/* GHC.Base.++ */(_FH/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_f/* GHC.Base.++ */(_Fi/* GHC.IO.Exception.$fExceptionArrayException2 */, _FQ/* s3N0i */));
            },1)));
          },1);
          return B(_f/* GHC.Base.++ */(_FY/* s3N0x */.a, _G2/* s3N0H */));
        },1);
        return new F(function(){return _f/* GHC.Base.++ */(_FI/* GHC.IO.Handle.Types.showHandle2 */, _G1/* s3N0I */);});
      }
    }
  }else{
    return new F(function(){return _f/* GHC.Base.++ */(_FW/* s3N0u */.a, new T(function(){
      return B(_f/* GHC.Base.++ */(_Fi/* GHC.IO.Exception.$fExceptionArrayException2 */, _FQ/* s3N0i */));
    },1));});
  }
},
_G3/* $fExceptionIOException_$cshow */ = function(_G4/* s3N16 */){
  var _G5/* s3N17 */ = E(_G4/* s3N16 */);
  return new F(function(){return _FJ/* GHC.IO.Exception.$w$cshowsPrec2 */(_G5/* s3N17 */.a, _G5/* s3N17 */.b, _G5/* s3N17 */.c, _G5/* s3N17 */.d, _G5/* s3N17 */.f, _o/* GHC.Types.[] */);});
},
_G6/* $fExceptionIOException_$cshowsPrec */ = function(_G7/* s3N0L */, _G8/* s3N0M */, _G9/* s3N0N */){
  var _Ga/* s3N0O */ = E(_G8/* s3N0M */);
  return new F(function(){return _FJ/* GHC.IO.Exception.$w$cshowsPrec2 */(_Ga/* s3N0O */.a, _Ga/* s3N0O */.b, _Ga/* s3N0O */.c, _Ga/* s3N0O */.d, _Ga/* s3N0O */.f, _G9/* s3N0N */);});
},
_Gb/* $s$dmshow9 */ = function(_Gc/* s3N0V */, _Gd/* s3N0W */){
  var _Ge/* s3N0X */ = E(_Gc/* s3N0V */);
  return new F(function(){return _FJ/* GHC.IO.Exception.$w$cshowsPrec2 */(_Ge/* s3N0X */.a, _Ge/* s3N0X */.b, _Ge/* s3N0X */.c, _Ge/* s3N0X */.d, _Ge/* s3N0X */.f, _Gd/* s3N0W */);});
},
_Gf/* $fShowIOException_$cshowList */ = function(_Gg/* s3N14 */, _Gh/* s3N15 */){
  return new F(function(){return _2B/* GHC.Show.showList__ */(_Gb/* GHC.IO.Exception.$s$dmshow9 */, _Gg/* s3N14 */, _Gh/* s3N15 */);});
},
_Gi/* $fShowIOException */ = new T3(0,_G6/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_G3/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_Gf/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_Gj/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_Fd/* GHC.IO.Exception.$fExceptionIOException3 */,_Gi/* GHC.IO.Exception.$fShowIOException */,_Gk/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_Ff/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_G3/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_Gk/* $fExceptionIOException_$ctoException */ = function(_Gl/* B1 */){
  return new T2(0,_Gj/* GHC.IO.Exception.$fExceptionIOException */,_Gl/* B1 */);
},
_Gm/* Nothing */ = __Z/* EXTERNAL */,
_Gn/* UserError */ = 7,
_Go/* str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));
}),
_Gp/* lvl22 */ = new T6(0,_Gm/* GHC.Base.Nothing */,_Gn/* GHC.IO.Exception.UserError */,_o/* GHC.Types.[] */,_Go/* Lib.Physics.str */,_Gm/* GHC.Base.Nothing */,_Gm/* GHC.Base.Nothing */),
_Gq/* lvl23 */ = new T(function(){
  return B(_Gk/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_Gp/* Lib.Physics.lvl22 */));
}),
_Gr/* str1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));
}),
_Gs/* lvl24 */ = new T6(0,_Gm/* GHC.Base.Nothing */,_Gn/* GHC.IO.Exception.UserError */,_o/* GHC.Types.[] */,_Gr/* Lib.Physics.str1 */,_Gm/* GHC.Base.Nothing */,_Gm/* GHC.Base.Nothing */),
_Gt/* lvl25 */ = new T(function(){
  return B(_Gk/* GHC.IO.Exception.$fExceptionIOException_$ctoException */(_Gs/* Lib.Physics.lvl24 */));
}),
_Gu/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_Gv/* lvl27 */ = function(_Gw/* swow */, _Gx/* swox */){
  var _Gy/* swoC */ = new T(function(){
    var _Gz/* swoB */ = new T(function(){
      return B(unAppCStr/* EXTERNAL */(" not in range [0..", new T(function(){
        return B(_f/* GHC.Base.++ */(B(_Af/* GHC.Show.$wshowSignedInt */(0, _Gx/* swox */, _o/* GHC.Types.[] */)), _Gu/* Lib.Physics.lvl26 */));
      })));
    },1);
    return B(_f/* GHC.Base.++ */(B(_Af/* GHC.Show.$wshowSignedInt */(0, _Gw/* swow */, _o/* GHC.Types.[] */)), _Gz/* swoB */));
  });
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Error in array index; ", _Gy/* swoC */)));});
},
_GA/* nextFrame1 */ = function(_GB/* swp3 */, _/* EXTERNAL */){
  var _GC/* swp5 */ = B(_C6/* Data.Traversable.$w$ctraverse */(_BF/* GHC.Arr.$fIxInt */, _Dt/* Data.Functor.Identity.$fApplicativeIdentity */, _EK/* Lib.Physics.a17 */, _GB/* swp3 */)),
  _GD/* swp8 */ = _GC/* swp5 */.c,
  _GE/* swp9 */ = _GC/* swp5 */.d,
  _GF/* swpa */ = E(_GC/* swp5 */.a),
  _GG/* swpc */ = E(_GC/* swp5 */.b);
  if(_GF/* swpa */<=_GG/* swpc */){
    var _GH/* swph */ = function(_GI/* swuC */, _GJ/* swuD */, _/* EXTERNAL */){
      if(_GI/* swuC */<=_GG/* swpc */){
        var _GK/* swuH */ = E(_GJ/* swuD */),
        _GL/* swuK */ = _GK/* swuH */.c,
        _GM/* swuL */ = _GK/* swuH */.d,
        _GN/* swuM */ = E(_GK/* swuH */.a),
        _GO/* swuO */ = E(_GK/* swuH */.b);
        if(_GN/* swuM */>_GI/* swuC */){
          return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
        }else{
          if(_GI/* swuC */>_GO/* swuO */){
            return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
          }else{
            if(_GN/* swuM */>_GI/* swuC */){
              return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
            }else{
              if(_GI/* swuC */>_GO/* swuO */){
                return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
              }else{
                var _GP/* swv2 */ = _GI/* swuC */-_GN/* swuM */|0;
                if(0>_GP/* swv2 */){
                  return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_GP/* swv2 */, _GL/* swuK */);});
                }else{
                  if(_GP/* swv2 */>=_GL/* swuK */){
                    return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_GP/* swv2 */, _GL/* swuK */);});
                  }else{
                    var _GQ/* swvb */ = E(_GM/* swuL */[_GP/* swv2 */]),
                    _GR/* swvs */ = _GI/* swuC */-_GN/* swuM */|0;
                    if(0>_GR/* swvs */){
                      return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_GR/* swvs */, _GL/* swuK */);});
                    }else{
                      if(_GR/* swvs */>=_GL/* swuK */){
                        return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_GR/* swvs */, _GL/* swuK */);});
                      }else{
                        var _GS/* swvB */ = E(_GM/* swuL */[_GR/* swvs */]),
                        _GT/* swvS */ = E(_F7/* Lib.Physics.f1 */),
                        _GU/* swvV */ = __app2/* EXTERNAL */(_GT/* swvS */, B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_GQ/* swvb */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_GQ/* swvb */.i),_o/* GHC.Types.[] */)))), B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_GS/* swvB */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_GS/* swvB */.i),_o/* GHC.Types.[] */))))),
                        _GV/* swvZ */ = __arr2lst/* EXTERNAL */(0, _GU/* swvV */),
                        _GW/* sww3 */ = B(_DQ/* Lib.Constraint.$fFromAnyContactPoint2 */(_GV/* swvZ */, _/* EXTERNAL */)),
                        _GX/* sww9 */ = B(_F1/* Lib.Physics.a20 */(_GW/* sww3 */, new T4(0,E(_GN/* swuM */),E(_GO/* swuO */),_GL/* swuK */,_GM/* swuL */), _/* EXTERNAL */));
                        if(_GI/* swuC */!=_GG/* swpc */){
                          var _GY/* swwe */ = E(_GX/* sww9 */),
                          _GZ/* swwf */ = _GY/* swwe */.a,
                          _H0/* swwh */ = E(_GY/* swwe */.b),
                          _H1/* swwq */ = function(_H2/* swwr */, _H3/* swws */, _H4/* swwt */, _H5/* swwu */, _H6/* swwv */, _/* EXTERNAL */){
                            if(_H3/* swws */>_GI/* swuC */){
                              return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
                            }else{
                              if(_GI/* swuC */>_H4/* swwt */){
                                return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
                              }else{
                                if(_H3/* swws */>_H2/* swwr */){
                                  return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
                                }else{
                                  if(_H2/* swwr */>_H4/* swwt */){
                                    return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
                                  }else{
                                    var _H7/* swwJ */ = _GI/* swuC */-_H3/* swws */|0;
                                    if(0>_H7/* swwJ */){
                                      return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_H7/* swwJ */, _H5/* swwu */);});
                                    }else{
                                      if(_H7/* swwJ */>=_H5/* swwu */){
                                        return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_H7/* swwJ */, _H5/* swwu */);});
                                      }else{
                                        var _H8/* swwS */ = E(_H6/* swwv */[_H7/* swwJ */]),
                                        _H9/* swx9 */ = _H2/* swwr */-_H3/* swws */|0;
                                        if(0>_H9/* swx9 */){
                                          return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_H9/* swx9 */, _H5/* swwu */);});
                                        }else{
                                          if(_H9/* swx9 */>=_H5/* swwu */){
                                            return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_H9/* swx9 */, _H5/* swwu */);});
                                          }else{
                                            var _Ha/* swxi */ = E(_H6/* swwv */[_H9/* swx9 */]),
                                            _Hb/* swxA */ = __app2/* EXTERNAL */(_GT/* swvS */, B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_H8/* swwS */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_H8/* swwS */.i),_o/* GHC.Types.[] */)))), B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_Ha/* swxi */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_Ha/* swxi */.i),_o/* GHC.Types.[] */))))),
                                            _Hc/* swxE */ = __arr2lst/* EXTERNAL */(0, _Hb/* swxA */),
                                            _Hd/* swxI */ = B(_DQ/* Lib.Constraint.$fFromAnyContactPoint2 */(_Hc/* swxE */, _/* EXTERNAL */)),
                                            _He/* swxO */ = B(_F1/* Lib.Physics.a20 */(_Hd/* swxI */, new T4(0,E(_H3/* swws */),E(_H4/* swwt */),_H5/* swwu */,_H6/* swwv */), _/* EXTERNAL */));
                                            if(_H2/* swwr */!=_GG/* swpc */){
                                              var _Hf/* swxT */ = E(_He/* swxO */),
                                              _Hg/* swxW */ = E(_Hf/* swxT */.b),
                                              _Hh/* swy6 */ = B(_H1/* swwq */(_H2/* swwr */+1|0, E(_Hg/* swxW */.a), E(_Hg/* swxW */.b), _Hg/* swxW */.c, _Hg/* swxW */.d, _/* EXTERNAL */));
                                              return new T2(0,new T2(1,_Hf/* swxT */.a,new T(function(){
                                                return E(E(_Hh/* swy6 */).a);
                                              })),new T(function(){
                                                return E(E(_Hh/* swy6 */).b);
                                              }));
                                            }else{
                                              return new T2(0,new T2(1,new T(function(){
                                                return E(E(_He/* swxO */).a);
                                              }),_o/* GHC.Types.[] */),new T(function(){
                                                return E(E(_He/* swxO */).b);
                                              }));
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          },
                          _Hi/* swyu */ = B(_H1/* swwq */(_GI/* swuC */+1|0, E(_H0/* swwh */.a), E(_H0/* swwh */.b), _H0/* swwh */.c, _H0/* swwh */.d, _/* EXTERNAL */));
                          if(_GI/* swuC */!=_GG/* swpc */){
                            var _Hj/* swyE */ = B(_GH/* swph */(_GI/* swuC */+1|0, new T(function(){
                              return E(E(_Hi/* swyu */).b);
                            },1), _/* EXTERNAL */)),
                            _Hk/* swyL */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(_GZ/* swwf */, new T(function(){
                                return E(E(_Hi/* swyu */).a);
                              })));
                            });
                            return new T2(0,new T2(1,_Hk/* swyL */,new T(function(){
                              return E(E(_Hj/* swyE */).a);
                            })),new T(function(){
                              return E(E(_Hj/* swyE */).b);
                            }));
                          }else{
                            var _Hl/* swz0 */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(_GZ/* swwf */, new T(function(){
                                return E(E(_Hi/* swyu */).a);
                              })));
                            });
                            return new T2(0,new T2(1,_Hl/* swz0 */,_o/* GHC.Types.[] */),new T(function(){
                              return E(E(_Hi/* swyu */).b);
                            }));
                          }
                        }else{
                          if(_GI/* swuC */!=_GG/* swpc */){
                            var _Hm/* swze */ = B(_GH/* swph */(_GI/* swuC */+1|0, new T(function(){
                              return E(E(_GX/* sww9 */).b);
                            },1), _/* EXTERNAL */)),
                            _Hn/* swzl */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(new T(function(){
                                return E(E(_GX/* sww9 */).a);
                              }), _o/* GHC.Types.[] */));
                            });
                            return new T2(0,new T2(1,_Hn/* swzl */,new T(function(){
                              return E(E(_Hm/* swze */).a);
                            })),new T(function(){
                              return E(E(_Hm/* swze */).b);
                            }));
                          }else{
                            var _Ho/* swzA */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(new T(function(){
                                return E(E(_GX/* sww9 */).a);
                              }), _o/* GHC.Types.[] */));
                            });
                            return new T2(0,new T2(1,_Ho/* swzA */,_o/* GHC.Types.[] */),new T(function(){
                              return E(E(_GX/* sww9 */).b);
                            }));
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }else{
        if(_GI/* swuC */!=_GG/* swpc */){
          var _Hp/* swzK */ = B(_GH/* swph */(_GI/* swuC */+1|0, _GJ/* swuD */, _/* EXTERNAL */));
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
            return E(E(_Hp/* swzK */).a);
          })),new T(function(){
            return E(E(_Hp/* swzK */).b);
          }));
        }else{
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),_GJ/* swuD */);
        }
      }
    },
    _Hq/* swpg */ = function(_Hr/* swpi */, _Hs/* swpj */, _Ht/* swpk */, _Hu/* swpl */, _Hv/* swpm */, _/* EXTERNAL */){
      if(_Hr/* swpi */<=_GG/* swpc */){
        if(_Hs/* swpj */>_Hr/* swpi */){
          return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
        }else{
          if(_Hr/* swpi */>_Ht/* swpk */){
            return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
          }else{
            if(_Hs/* swpj */>_Hr/* swpi */){
              return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
            }else{
              if(_Hr/* swpi */>_Ht/* swpk */){
                return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
              }else{
                var _Hw/* swpC */ = _Hr/* swpi */-_Hs/* swpj */|0;
                if(0>_Hw/* swpC */){
                  return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_Hw/* swpC */, _Hu/* swpl */);});
                }else{
                  if(_Hw/* swpC */>=_Hu/* swpl */){
                    return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_Hw/* swpC */, _Hu/* swpl */);});
                  }else{
                    var _Hx/* swpL */ = E(_Hv/* swpm */[_Hw/* swpC */]),
                    _Hy/* swq2 */ = _Hr/* swpi */-_Hs/* swpj */|0;
                    if(0>_Hy/* swq2 */){
                      return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_Hy/* swq2 */, _Hu/* swpl */);});
                    }else{
                      if(_Hy/* swq2 */>=_Hu/* swpl */){
                        return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_Hy/* swq2 */, _Hu/* swpl */);});
                      }else{
                        var _Hz/* swqb */ = E(_Hv/* swpm */[_Hy/* swq2 */]),
                        _HA/* swqs */ = E(_F7/* Lib.Physics.f1 */),
                        _HB/* swqv */ = __app2/* EXTERNAL */(_HA/* swqs */, B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_Hx/* swpL */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_Hx/* swpL */.i),_o/* GHC.Types.[] */)))), B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_Hz/* swqb */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_Hz/* swqb */.i),_o/* GHC.Types.[] */))))),
                        _HC/* swqz */ = __arr2lst/* EXTERNAL */(0, _HB/* swqv */),
                        _HD/* swqD */ = B(_DQ/* Lib.Constraint.$fFromAnyContactPoint2 */(_HC/* swqz */, _/* EXTERNAL */)),
                        _HE/* swqJ */ = B(_F1/* Lib.Physics.a20 */(_HD/* swqD */, new T4(0,E(_Hs/* swpj */),E(_Ht/* swpk */),_Hu/* swpl */,_Hv/* swpm */), _/* EXTERNAL */));
                        if(_Hr/* swpi */!=_GG/* swpc */){
                          var _HF/* swqO */ = E(_HE/* swqJ */),
                          _HG/* swqP */ = _HF/* swqO */.a,
                          _HH/* swqR */ = E(_HF/* swqO */.b),
                          _HI/* swr0 */ = function(_HJ/* swr1 */, _HK/* swr2 */, _HL/* swr3 */, _HM/* swr4 */, _HN/* swr5 */, _/* EXTERNAL */){
                            if(_HK/* swr2 */>_Hr/* swpi */){
                              return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
                            }else{
                              if(_Hr/* swpi */>_HL/* swr3 */){
                                return new F(function(){return die/* EXTERNAL */(_Gq/* Lib.Physics.lvl23 */);});
                              }else{
                                if(_HK/* swr2 */>_HJ/* swr1 */){
                                  return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
                                }else{
                                  if(_HJ/* swr1 */>_HL/* swr3 */){
                                    return new F(function(){return die/* EXTERNAL */(_Gt/* Lib.Physics.lvl25 */);});
                                  }else{
                                    var _HO/* swrj */ = _Hr/* swpi */-_HK/* swr2 */|0;
                                    if(0>_HO/* swrj */){
                                      return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_HO/* swrj */, _HM/* swr4 */);});
                                    }else{
                                      if(_HO/* swrj */>=_HM/* swr4 */){
                                        return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_HO/* swrj */, _HM/* swr4 */);});
                                      }else{
                                        var _HP/* swrs */ = E(_HN/* swr5 */[_HO/* swrj */]),
                                        _HQ/* swrJ */ = _HJ/* swr1 */-_HK/* swr2 */|0;
                                        if(0>_HQ/* swrJ */){
                                          return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_HQ/* swrJ */, _HM/* swr4 */);});
                                        }else{
                                          if(_HQ/* swrJ */>=_HM/* swr4 */){
                                            return new F(function(){return _Gv/* Lib.Physics.lvl27 */(_HQ/* swrJ */, _HM/* swr4 */);});
                                          }else{
                                            var _HR/* swrS */ = E(_HN/* swr5 */[_HQ/* swrJ */]),
                                            _HS/* swsa */ = __app2/* EXTERNAL */(_HA/* swqs */, B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_HP/* swrs */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_HP/* swrs */.i),_o/* GHC.Types.[] */)))), B(_jA/* Haste.Prim.Any.$wtoObject */(new T2(1,new T2(0,_Cw/* Lib.Object.$fToAnyObject2 */,_HR/* swrS */.h),new T2(1,new T2(0,_Cv/* Lib.Object.$fToAnyObject1 */,_HR/* swrS */.i),_o/* GHC.Types.[] */))))),
                                            _HT/* swse */ = __arr2lst/* EXTERNAL */(0, _HS/* swsa */),
                                            _HU/* swsi */ = B(_DQ/* Lib.Constraint.$fFromAnyContactPoint2 */(_HT/* swse */, _/* EXTERNAL */)),
                                            _HV/* swso */ = B(_F1/* Lib.Physics.a20 */(_HU/* swsi */, new T4(0,E(_HK/* swr2 */),E(_HL/* swr3 */),_HM/* swr4 */,_HN/* swr5 */), _/* EXTERNAL */));
                                            if(_HJ/* swr1 */!=_GG/* swpc */){
                                              var _HW/* swst */ = E(_HV/* swso */),
                                              _HX/* swsw */ = E(_HW/* swst */.b),
                                              _HY/* swsG */ = B(_HI/* swr0 */(_HJ/* swr1 */+1|0, E(_HX/* swsw */.a), E(_HX/* swsw */.b), _HX/* swsw */.c, _HX/* swsw */.d, _/* EXTERNAL */));
                                              return new T2(0,new T2(1,_HW/* swst */.a,new T(function(){
                                                return E(E(_HY/* swsG */).a);
                                              })),new T(function(){
                                                return E(E(_HY/* swsG */).b);
                                              }));
                                            }else{
                                              return new T2(0,new T2(1,new T(function(){
                                                return E(E(_HV/* swso */).a);
                                              }),_o/* GHC.Types.[] */),new T(function(){
                                                return E(E(_HV/* swso */).b);
                                              }));
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          },
                          _HZ/* swt4 */ = B(_HI/* swr0 */(_Hr/* swpi */+1|0, E(_HH/* swqR */.a), E(_HH/* swqR */.b), _HH/* swqR */.c, _HH/* swqR */.d, _/* EXTERNAL */));
                          if(_Hr/* swpi */!=_GG/* swpc */){
                            var _I0/* swte */ = B(_GH/* swph */(_Hr/* swpi */+1|0, new T(function(){
                              return E(E(_HZ/* swt4 */).b);
                            },1), _/* EXTERNAL */)),
                            _I1/* swtl */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(_HG/* swqP */, new T(function(){
                                return E(E(_HZ/* swt4 */).a);
                              })));
                            });
                            return new T2(0,new T2(1,_I1/* swtl */,new T(function(){
                              return E(E(_I0/* swte */).a);
                            })),new T(function(){
                              return E(E(_I0/* swte */).b);
                            }));
                          }else{
                            var _I2/* swtA */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(_HG/* swqP */, new T(function(){
                                return E(E(_HZ/* swt4 */).a);
                              })));
                            });
                            return new T2(0,new T2(1,_I2/* swtA */,_o/* GHC.Types.[] */),new T(function(){
                              return E(E(_HZ/* swt4 */).b);
                            }));
                          }
                        }else{
                          if(_Hr/* swpi */!=_GG/* swpc */){
                            var _I3/* swtO */ = B(_GH/* swph */(_Hr/* swpi */+1|0, new T(function(){
                              return E(E(_HE/* swqJ */).b);
                            },1), _/* EXTERNAL */)),
                            _I4/* swtV */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(new T(function(){
                                return E(E(_HE/* swqJ */).a);
                              }), _o/* GHC.Types.[] */));
                            });
                            return new T2(0,new T2(1,_I4/* swtV */,new T(function(){
                              return E(E(_I3/* swtO */).a);
                            })),new T(function(){
                              return E(E(_I3/* swtO */).b);
                            }));
                          }else{
                            var _I5/* swua */ = new T(function(){
                              return B(_DY/* Lib.Physics.$sgo1 */(new T(function(){
                                return E(E(_HE/* swqJ */).a);
                              }), _o/* GHC.Types.[] */));
                            });
                            return new T2(0,new T2(1,_I5/* swua */,_o/* GHC.Types.[] */),new T(function(){
                              return E(E(_HE/* swqJ */).b);
                            }));
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }else{
        if(_Hr/* swpi */!=_GG/* swpc */){
          var _I6/* swuk */ = B(_Hq/* swpg */(_Hr/* swpi */+1|0, _Hs/* swpj */, _Ht/* swpk */, _Hu/* swpl */, _Hv/* swpm */, _/* EXTERNAL */));
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,new T(function(){
            return E(E(_I6/* swuk */).a);
          })),new T(function(){
            return E(E(_I6/* swuk */).b);
          }));
        }else{
          return new T2(0,new T2(1,_o/* GHC.Types.[] */,_o/* GHC.Types.[] */),new T4(0,E(_Hs/* swpj */),E(_Ht/* swpk */),_Hu/* swpl */,_Hv/* swpm */));
        }
      }
    },
    _I7/* swzZ */ = B(_Hq/* swpg */(_GF/* swpa */, _GF/* swpa */, _GG/* swpc */, _GD/* swp8 */, _GE/* swp9 */, _/* EXTERNAL */)),
    _I8/* swA6 */ = new T(function(){
      return B(_C6/* Data.Traversable.$w$ctraverse */(_BF/* GHC.Arr.$fIxInt */, _Dt/* Data.Functor.Identity.$fApplicativeIdentity */, _ES/* Lib.Physics.a18 */, new T(function(){
        return E(E(_I7/* swzZ */).b);
      })));
    });
    return new T2(0,_jz/* GHC.Tuple.() */,_I8/* swA6 */);
  }else{
    var _I9/* swBE */ = new T(function(){
      var _Ia/* swBD */ = function(_/* EXTERNAL */){
        var _Ib/* swA9 */ = function(_Ic/* swAa */){
          if(_Ic/* swAa */>=0){
            var _Id/* swAd */ = newArr/* EXTERNAL */(_Ic/* swAa */, _hl/* GHC.Arr.arrEleBottom */),
            _Ie/* swAf */ = _Id/* swAd */,
            _If/* swAg */ = E(_Ic/* swAa */);
            if(!_If/* swAg */){
              return new T4(0,E(_GF/* swpa */),E(_GG/* swpc */),0,_Ie/* swAf */);
            }else{
              var _Ig/* swAh */ = _GD/* swp8 */-1|0,
              _Ih/* swAl */ = function(_Ii/* swAm */, _Ij/* swAn */, _/* EXTERNAL */){
                while(1){
                  var _Ik/* swAp */ = E(_Ii/* swAm */);
                  if(!_Ik/* swAp */._){
                    return E(_/* EXTERNAL */);
                  }else{
                    var _/* EXTERNAL */ = _Ie/* swAf */[_Ij/* swAn */] = _Ik/* swAp */.a;
                    if(_Ij/* swAn */!=(_If/* swAg */-1|0)){
                      var _Il/*  swAn */ = _Ij/* swAn */+1|0;
                      _Ii/* swAm */ = _Ik/* swAp */.b;
                      _Ij/* swAn */ = _Il/*  swAn */;
                      continue;
                    }else{
                      return E(_/* EXTERNAL */);
                    }
                  }
                }
              };
              if(0<=_Ig/* swAh */){
                var _Im/* swAz */ = function(_In/* swAA */){
                  return new T2(1,new T(function(){
                    var _Io/* swAD */ = E(_GE/* swp9 */[_In/* swAA */]),
                    _Ip/* swAN */ = E(_Io/* swAD */.d),
                    _Iq/* swAQ */ = E(_Ip/* swAN */.a),
                    _Ir/* swAU */ = E(_Io/* swAD */.e),
                    _Is/* swAX */ = E(_Ir/* swAU */.a),
                    _It/* swB1 */ = E(_Io/* swAD */.f),
                    _Iu/* swB5 */ = B(_Eo/* Lib.Physics.$wa */(_Io/* swAD */.a, _Io/* swAD */.b, _Io/* swAD */.c, _Iq/* swAQ */.a, _Iq/* swAQ */.b, _Iq/* swAQ */.c, _Ip/* swAN */.b, _Is/* swAX */.a, _Is/* swAX */.b, _Is/* swAX */.c, _Ir/* swAU */.b, _It/* swB1 */.a, _It/* swB1 */.b, _It/* swB1 */.c, _Io/* swAD */.g, _Io/* swAD */.h, _Io/* swAD */.i));
                    return {_:0,a:E(_Iu/* swB5 */.a),b:E(_Iu/* swB5 */.b),c:E(_Iu/* swB5 */.c),d:E(_Iu/* swB5 */.d),e:E(_Iu/* swB5 */.e),f:E(_Iu/* swB5 */.f),g:E(_Iu/* swB5 */.g),h:_Iu/* swB5 */.h,i:_Iu/* swB5 */.i};
                  }),new T(function(){
                    if(_In/* swAA */!=_Ig/* swAh */){
                      return B(_Im/* swAz */(_In/* swAA */+1|0));
                    }else{
                      return __Z/* EXTERNAL */;
                    }
                  }));
                },
                _/* EXTERNAL */ = B(_Ih/* swAl */(B(_Im/* swAz */(0)), 0, _/* EXTERNAL */));
                return new T4(0,E(_GF/* swpa */),E(_GG/* swpc */),_If/* swAg */,_Ie/* swAf */);
              }else{
                return new T4(0,E(_GF/* swpa */),E(_GG/* swpc */),_If/* swAg */,_Ie/* swAf */);
              }
            }
          }else{
            return E(_zj/* GHC.Arr.negRange */);
          }
        };
        if(_GF/* swpa */>_GG/* swpc */){
          return new F(function(){return _Ib/* swA9 */(0);});
        }else{
          return new F(function(){return _Ib/* swA9 */((_GG/* swpc */-_GF/* swpa */|0)+1|0);});
        }
      };
      return B(_zz/* GHC.ST.runSTRep */(_Ia/* swBD */));
    });
    return new T2(0,_jz/* GHC.Tuple.() */,_I9/* swBE */);
  }
},
_Iv/* refresh_f1 */ = new T(function(){
  return eval/* EXTERNAL */("__strict(refresh)");
}),
_Iw/* main2 */ = function(_Ix/* szds */, _/* EXTERNAL */){
  var _Iy/* szdx */ = __app0/* EXTERNAL */(E(_Iv/* Lib.Screen.refresh_f1 */)),
  _Iz/* szdD */ = __app0/* EXTERNAL */(E(_Dc/* Lib.Screen.draw_f1 */)),
  _IA/* szdG */ = B(A(_C6/* Data.Traversable.$w$ctraverse */,[_BF/* GHC.Arr.$fIxInt */, _A2/* GHC.Base.$fApplicativeIO */, _Da/* Lib.Object.drawObject */, _Ix/* szds */, _/* EXTERNAL */])),
  _IB/* szdJ */ = B(_GA/* Lib.Physics.nextFrame1 */(_Ix/* szds */, _/* EXTERNAL */));
  return new T(function(){
    return E(E(_IB/* szdJ */).b);
  });
},
_IC/* a1 */ = function(_ID/* snHB */, _/* EXTERNAL */){
  while(1){
    var _IE/* snHD */ = E(_ID/* snHB */);
    if(!_IE/* snHD */._){
      return _jz/* GHC.Tuple.() */;
    }else{
      var _IF/* snHF */ = _IE/* snHD */.b,
      _IG/* snHG */ = E(_IE/* snHD */.a);
      switch(_IG/* snHG */._){
        case 0:
          var _IH/* snHI */ = B(A1(_IG/* snHG */.a,_/* EXTERNAL */));
          _ID/* snHB */ = B(_f/* GHC.Base.++ */(_IF/* snHF */, new T2(1,_IH/* snHI */,_o/* GHC.Types.[] */)));
          continue;
        case 1:
          _ID/* snHB */ = B(_f/* GHC.Base.++ */(_IF/* snHF */, _IG/* snHG */.a));
          continue;
        default:
          _ID/* snHB */ = _IF/* snHF */;
          continue;
      }
    }
  }
},
_II/* $fMonadEventCIO_$sa */ = function(_IJ/* snHp */, _IK/* snHq */, _/* EXTERNAL */){
  var _IL/* snHs */ = E(_IJ/* snHp */);
  switch(_IL/* snHs */._){
    case 0:
      var _IM/* snHu */ = B(A1(_IL/* snHs */.a,_/* EXTERNAL */));
      return new F(function(){return _IC/* Haste.Concurrent.Monad.a1 */(B(_f/* GHC.Base.++ */(_IK/* snHq */, new T2(1,_IM/* snHu */,_o/* GHC.Types.[] */))), _/* EXTERNAL */);});
      break;
    case 1:
      return new F(function(){return _IC/* Haste.Concurrent.Monad.a1 */(B(_f/* GHC.Base.++ */(_IK/* snHq */, _IL/* snHs */.a)), _/* EXTERNAL */);});
      break;
    default:
      return new F(function(){return _IC/* Haste.Concurrent.Monad.a1 */(_IK/* snHq */, _/* EXTERNAL */);});
  }
},
_IN/* $c>>=1 */ = function(_IO/* snHc */, _IP/* snHd */, _IQ/* snHe */){
  return new F(function(){return A1(_IO/* snHc */,function(_IR/* snHf */){
    return new F(function(){return A2(_IP/* snHd */,_IR/* snHf */, _IQ/* snHe */);});
  });});
},
_IS/* $fApplicativeCIO1 */ = function(_IT/* snLu */, _IU/* snLv */, _IV/* snLw */){
  var _IW/* snLB */ = function(_IX/* snLx */){
    var _IY/* snLy */ = new T(function(){
      return B(A1(_IV/* snLw */,_IX/* snLx */));
    });
    return new F(function(){return A1(_IU/* snLv */,function(_IZ/* snLz */){
      return E(_IY/* snLy */);
    });});
  };
  return new F(function(){return A1(_IT/* snLu */,_IW/* snLB */);});
},
_J0/* $fApplicativeCIO2 */ = function(_J1/* snLm */, _J2/* snLn */, _J3/* snLo */){
  var _J4/* snLp */ = new T(function(){
    return B(A1(_J2/* snLn */,function(_J5/* snLq */){
      return new F(function(){return A1(_J3/* snLo */,_J5/* snLq */);});
    }));
  });
  return new F(function(){return A1(_J1/* snLm */,function(_J6/* snLs */){
    return E(_J4/* snLp */);
  });});
},
_J7/* $fApplicativeCIO3 */ = function(_J8/* snHP */, _J9/* snHQ */, _Ja/* snHR */){
  var _Jb/* snHW */ = function(_Jc/* snHS */){
    var _Jd/* snHV */ = function(_Je/* snHT */){
      return new F(function(){return A1(_Ja/* snHR */,new T(function(){
        return B(A1(_Jc/* snHS */,_Je/* snHT */));
      }));});
    };
    return new F(function(){return A1(_J9/* snHQ */,_Jd/* snHV */);});
  };
  return new F(function(){return A1(_J8/* snHP */,_Jb/* snHW */);});
},
_Jf/* $fApplicativeCIO4 */ = function(_Jg/* snHh */, _Jh/* snHi */){
  return new F(function(){return A1(_Jh/* snHi */,_Jg/* snHh */);});
},
_Ji/* $fFunctorCIO1 */ = function(_Jj/* snLg */, _Jk/* snLh */, _Jl/* snLi */){
  var _Jm/* snLj */ = new T(function(){
    return B(A1(_Jl/* snLi */,_Jj/* snLg */));
  });
  return new F(function(){return A1(_Jk/* snLh */,function(_Jn/* snLk */){
    return E(_Jm/* snLj */);
  });});
},
_Jo/* $fFunctorCIO2 */ = function(_Jp/* snH6 */, _Jq/* snH7 */, _Jr/* snH8 */){
  var _Js/* snHb */ = function(_Jt/* snH9 */){
    return new F(function(){return A1(_Jr/* snH8 */,new T(function(){
      return B(A1(_Jp/* snH6 */,_Jt/* snH9 */));
    }));});
  };
  return new F(function(){return A1(_Jq/* snH7 */,_Js/* snHb */);});
},
_Ju/* $fFunctorCIO */ = new T2(0,_Jo/* Haste.Concurrent.Monad.$fFunctorCIO2 */,_Ji/* Haste.Concurrent.Monad.$fFunctorCIO1 */),
_Jv/* $fApplicativeCIO */ = new T5(0,_Ju/* Haste.Concurrent.Monad.$fFunctorCIO */,_Jf/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_J7/* Haste.Concurrent.Monad.$fApplicativeCIO3 */,_J0/* Haste.Concurrent.Monad.$fApplicativeCIO2 */,_IS/* Haste.Concurrent.Monad.$fApplicativeCIO1 */),
_Jw/* >>= */ = function(_Jx/* s34T */){
  return E(E(_Jx/* s34T */).b);
},
_Jy/* $fMonadCIO_$c>> */ = function(_Jz/* snLD */, _JA/* snLE */){
  return new F(function(){return A3(_Jw/* GHC.Base.>>= */,_JB/* Haste.Concurrent.Monad.$fMonadCIO */, _Jz/* snLD */, function(_JC/* snLF */){
    return E(_JA/* snLE */);
  });});
},
_JD/* a5 */ = function(_JE/* snLC */){
  return new F(function(){return err/* EXTERNAL */(_JE/* snLC */);});
},
_JB/* $fMonadCIO */ = new T(function(){
  return new T5(0,_Jv/* Haste.Concurrent.Monad.$fApplicativeCIO */,_IN/* Haste.Concurrent.Monad.$c>>=1 */,_Jy/* Haste.Concurrent.Monad.$fMonadCIO_$c>> */,_Jf/* Haste.Concurrent.Monad.$fApplicativeCIO4 */,_JD/* Haste.Concurrent.Monad.a5 */);
}),
_JF/* $fMonadIOCIO1 */ = function(_JG/* snH3 */, _JH/* snH4 */){
  return new T1(0,function(_/* EXTERNAL */){
    return new F(function(){return _zR/* GHC.Base.$fFunctorIO2 */(_JH/* snH4 */, _JG/* snH3 */, _/* EXTERNAL */);});
  });
},
_JI/* $fMonadIOCIO */ = new T2(0,_JB/* Haste.Concurrent.Monad.$fMonadCIO */,_JF/* Haste.Concurrent.Monad.$fMonadIOCIO1 */),
_JJ/* forkIO1 */ = function(_JK/* snHj */){
  return new T0(2);
},
_JL/* forkIO */ = function(_JM/* snKc */){
  var _JN/* snKd */ = new T(function(){
    return B(A1(_JM/* snKc */,_JJ/* Haste.Concurrent.Monad.forkIO1 */));
  }),
  _JO/* snKi */ = function(_JP/* snKf */){
    return new T1(1,new T2(1,new T(function(){
      return B(A1(_JP/* snKf */,_jz/* GHC.Tuple.() */));
    }),new T2(1,_JN/* snKd */,_o/* GHC.Types.[] */)));
  };
  return E(_JO/* snKi */);
},
_JQ/* $fMonadConcCIO */ = new T3(0,_JI/* Haste.Concurrent.Monad.$fMonadIOCIO */,_7S/* GHC.Base.id */,_JL/* Haste.Concurrent.Monad.forkIO */),
_JR/* jsNull */ = new T(function(){
  return E(_p7/* Haste.Prim.Any.nullValue */);
}),
_JS/* Stop */ = new T0(2),
_JT/* liftCIO */ = function(_JU/* snGT */){
  return E(E(_JU/* snGT */).b);
},
_JV/* putMVar */ = function(_JW/* snKj */, _JX/* snKk */, _JY/* snKl */){
  var _JZ/* snKT */ = function(_K0/* snKn */){
    var _K1/* snKS */ = function(_/* EXTERNAL */){
      var _K2/* snKp */ = E(_JX/* snKk */),
      _K3/* snKr */ = rMV/* EXTERNAL */(_K2/* snKp */),
      _K4/* snKu */ = E(_K3/* snKr */);
      if(!_K4/* snKu */._){
        var _K5/* snKC */ = new T(function(){
          var _K6/* snKx */ = new T(function(){
            return B(A1(_K0/* snKn */,_jz/* GHC.Tuple.() */));
          });
          return B(_f/* GHC.Base.++ */(_K4/* snKu */.b, new T2(1,new T2(0,_JY/* snKl */,function(_K7/* snKy */){
            return E(_K6/* snKx */);
          }),_o/* GHC.Types.[] */)));
        }),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_K2/* snKp */, new T2(0,_K4/* snKu */.a,_K5/* snKC */));
        return _JS/* Haste.Concurrent.Monad.Stop */;
      }else{
        var _K8/* snKG */ = E(_K4/* snKu */.a);
        if(!_K8/* snKG */._){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_K2/* snKp */, new T2(0,_JY/* snKl */,_o/* GHC.Types.[] */));
          return new T(function(){
            return B(A1(_K0/* snKn */,_jz/* GHC.Tuple.() */));
          });
        }else{
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_K2/* snKp */, new T1(1,_K8/* snKG */.b));
          return new T1(1,new T2(1,new T(function(){
            return B(A1(_K0/* snKn */,_jz/* GHC.Tuple.() */));
          }),new T2(1,new T(function(){
            return B(A2(_K8/* snKG */.a,_JY/* snKl */, _JJ/* Haste.Concurrent.Monad.forkIO1 */));
          }),_o/* GHC.Types.[] */)));
        }
      }
    };
    return new T1(0,_K1/* snKS */);
  };
  return new F(function(){return A2(_JT/* Haste.Concurrent.Monad.liftCIO */,_JW/* snKj */, _JZ/* snKT */);});
},
_K9/* requestAnimationFrame_f1 */ = new T(function(){
  return eval/* EXTERNAL */("window.requestAnimationFrame");
}),
_Ka/* takeMVar1 */ = new T1(1,_o/* GHC.Types.[] */),
_Kb/* takeMVar */ = function(_Kc/* snJ3 */, _Kd/* snJ4 */){
  var _Ke/* snJF */ = function(_Kf/* snJ5 */){
    var _Kg/* snJE */ = function(_/* EXTERNAL */){
      var _Kh/* snJ7 */ = E(_Kd/* snJ4 */),
      _Ki/* snJ9 */ = rMV/* EXTERNAL */(_Kh/* snJ7 */),
      _Kj/* snJc */ = E(_Ki/* snJ9 */);
      if(!_Kj/* snJc */._){
        var _Kk/* snJd */ = _Kj/* snJc */.a,
        _Kl/* snJf */ = E(_Kj/* snJc */.b);
        if(!_Kl/* snJf */._){
          var _/* EXTERNAL */ = wMV/* EXTERNAL */(_Kh/* snJ7 */, _Ka/* Haste.Concurrent.Monad.takeMVar1 */);
          return new T(function(){
            return B(A1(_Kf/* snJ5 */,_Kk/* snJd */));
          });
        }else{
          var _Km/* snJk */ = E(_Kl/* snJf */.a),
          _/* EXTERNAL */ = wMV/* EXTERNAL */(_Kh/* snJ7 */, new T2(0,_Km/* snJk */.a,_Kl/* snJf */.b));
          return new T1(1,new T2(1,new T(function(){
            return B(A1(_Kf/* snJ5 */,_Kk/* snJd */));
          }),new T2(1,new T(function(){
            return B(A1(_Km/* snJk */.b,_JJ/* Haste.Concurrent.Monad.forkIO1 */));
          }),_o/* GHC.Types.[] */)));
        }
      }else{
        var _Kn/* snJB */ = new T(function(){
          var _Ko/* snJz */ = function(_Kp/* snJv */){
            var _Kq/* snJw */ = new T(function(){
              return B(A1(_Kf/* snJ5 */,_Kp/* snJv */));
            });
            return function(_Kr/* snJx */){
              return E(_Kq/* snJw */);
            };
          };
          return B(_f/* GHC.Base.++ */(_Kj/* snJc */.a, new T2(1,_Ko/* snJz */,_o/* GHC.Types.[] */)));
        }),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_Kh/* snJ7 */, new T1(1,_Kn/* snJB */));
        return _JS/* Haste.Concurrent.Monad.Stop */;
      }
    };
    return new T1(0,_Kg/* snJE */);
  };
  return new F(function(){return A2(_JT/* Haste.Concurrent.Monad.liftCIO */,_Kc/* snJ3 */, _Ke/* snJF */);});
},
_Ks/* $wa */ = function(_Kt/* s7Uj */, _Ku/* s7Uk */){
  var _Kv/* s7Ul */ = new T(function(){
    return B(A(_JV/* Haste.Concurrent.Monad.putMVar */,[_JQ/* Haste.Concurrent.Monad.$fMonadConcCIO */, _Kt/* s7Uj */, _jz/* GHC.Tuple.() */, _JJ/* Haste.Concurrent.Monad.forkIO1 */]));
  });
  return function(_/* EXTERNAL */){
    var _Kw/* s7Uw */ = __createJSFunc/* EXTERNAL */(2, function(_Kx/* s7Un */, _/* EXTERNAL */){
      var _Ky/* s7Up */ = B(_II/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(_Kv/* s7Ul */, _o/* GHC.Types.[] */, _/* EXTERNAL */));
      return _JR/* Haste.Prim.Any.jsNull */;
    }),
    _Kz/* s7UC */ = __app1/* EXTERNAL */(E(_K9/* Haste.Graphics.AnimationFrame.requestAnimationFrame_f1 */), _Kw/* s7Uw */);
    return new T(function(){
      return B(A3(_Kb/* Haste.Concurrent.Monad.takeMVar */,_JQ/* Haste.Concurrent.Monad.$fMonadConcCIO */, _Kt/* s7Uj */, _Ku/* s7Uk */));
    });
  };
},
_KA/* run2 */ = new T1(1,_o/* GHC.Types.[] */),
_KB/* run1 */ = function(_KC/* s7UV */, _KD/* s7UW */, _/* EXTERNAL */){
  var _KE/* s7Vs */ = function(_/* EXTERNAL */){
    var _KF/* s7UZ */ = nMV/* EXTERNAL */(_KC/* s7UV */),
    _KG/* s7V1 */ = _KF/* s7UZ */;
    return new T(function(){
      var _KH/* s7V2 */ = new T(function(){
        return B(_KI/* s7V5 */(_/* EXTERNAL */));
      }),
      _KJ/* s7V3 */ = function(_/* EXTERNAL */){
        var _KK/* s7V7 */ = rMV/* EXTERNAL */(_KG/* s7V1 */),
        _KL/* s7Va */ = B(A2(_KD/* s7UW */,_KK/* s7V7 */, _/* EXTERNAL */)),
        _/* EXTERNAL */ = wMV/* EXTERNAL */(_KG/* s7V1 */, _KL/* s7Va */),
        _KM/* s7Vo */ = function(_/* EXTERNAL */){
          var _KN/* s7Vf */ = nMV/* EXTERNAL */(_KA/* Lib.Screen.run2 */);
          return new T(function(){
            return new T1(0,B(_Ks/* Lib.Screen.$wa */(_KN/* s7Vf */, function(_KO/* s7Vj */){
              return E(_KH/* s7V2 */);
            })));
          });
        };
        return new T1(0,_KM/* s7Vo */);
      },
      _KP/* s7V4 */ = new T(function(){
        return new T1(0,_KJ/* s7V3 */);
      }),
      _KI/* s7V5 */ = function(_KQ/* s7Vq */){
        return E(_KP/* s7V4 */);
      };
      return B(_KI/* s7V5 */(_/* EXTERNAL */));
    });
  };
  return new F(function(){return _II/* Haste.Concurrent.Monad.$fMonadEventCIO_$sa */(new T1(0,_KE/* s7Vs */), _o/* GHC.Types.[] */, _/* EXTERNAL */);});
},
_KR/* main1 */ = function(_/* EXTERNAL */){
  var _KS/* szdY */ = __app2/* EXTERNAL */(E(_0/* Lib.Screen.compile_f1 */), E(_7U/* Lib.Shader.fieldStr */), E(_he/* Lib.Shader.gradStr */));
  return new F(function(){return _KB/* Lib.Screen.run1 */(_zC/* Main.initial2 */, _Iw/* Main.main2 */, _/* EXTERNAL */);});
},
_KT/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _KR/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_KT, [0]));};window.onload = hasteMain;