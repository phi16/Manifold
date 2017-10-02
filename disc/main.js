"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

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
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
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
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
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
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return E(E(_hP).a);}),_hR=new T(function(){return B(_8J(new T(function(){return B(_8H(_hQ));})));}),_hS=new T(function(){return B(A2(_8s,_hR,_8r));}),_hT=function(_hU){var _hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=new T(function(){return E(E(_hU).c);});return B(A3(_8L,_hR,_hY,_hY));}),_hZ=new T(function(){var _i0=new T(function(){return E(E(_hU).a);});return B(A3(_8L,_hR,_i0,_i0));});return B(A3(_6X,_hR,_hZ,_hX));});return B(A2(_9t,_hQ,_hW));});return new F(function(){return A3(_9p,_hR,_hV,_hS);});};return E(_hT);},_i1=function(_ef,_ee){return new T2(0,_ef,_ee);},_i2=function(_i3,_i4,_i5){var _i6=new T(function(){var _i7=E(_i3),_i8=_i7.a,_i9=new T(function(){return B(A1(_i7.b,new T(function(){return B(_8J(B(_8H(E(_i7.c).a))));})));});return B(A3(_8R,_i8,new T(function(){return B(A3(_8T,B(_8F(_i8)),_i1,_i5));}),_i9));});return E(B(A1(_i4,_i6)).b);},_ia=function(_ib){var _ic=new T(function(){return E(E(_ib).a);}),_id=new T(function(){return E(E(_ib).b);}),_ie=new T(function(){var _if=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),_ig=new T(function(){var _ih=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_eb(_ih,new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_hO(new T2(0,_ig,_if)));});return function(_ii){return new F(function(){return _i2(new T3(0,_8p,_8u,new T2(0,_ic,_id)),_ie,_ii);});};},_ij=new T(function(){return B(_ia(_7V));}),_ik=new T(function(){return B(A1(_ij,_E));}),_il=new T(function(){return E(E(_ik).a);}),_im=new T(function(){return B(unCStr(",y:"));}),_in=new T1(0,_im),_io=new T(function(){return E(E(_ik).b);}),_ip=new T(function(){return B(unCStr(",z:"));}),_iq=new T1(0,_ip),_ir=new T(function(){return E(E(_ik).c);}),_is=new T(function(){return B(unCStr("})"));}),_it=new T1(0,_is),_iu=new T2(1,_it,_w),_iv=new T2(1,_ir,_iu),_iw=new T2(1,_iq,_iv),_ix=new T2(1,_io,_iw),_iy=new T2(1,_in,_ix),_iz=new T2(1,_il,_iy),_iA=new T(function(){return B(unCStr("({x:"));}),_iB=new T1(0,_iA),_iC=new T2(1,_iB,_iz),_iD=function(_iE){return E(_iE);},_iF=new T(function(){return toJSStr(B(_e(_x,_iD,_iC)));}),_iG=new T(function(){return B(_hO(_7V));}),_iH=new T(function(){return B(A1(_iG,_E));}),_iI=new T(function(){return toJSStr(B(_4(_x,_iD,_iH)));}),_iJ=function(_iK,_iL,_iM){var _iN=E(_iM);if(!_iN._){return new F(function(){return A1(_iL,_iN.a);});}else{var _iO=new T(function(){return B(_0(_iK));}),_iP=new T(function(){return B(_2(_iK));}),_iQ=function(_iR){var _iS=E(_iR);if(!_iS._){return E(_iP);}else{return new F(function(){return A2(_iO,new T(function(){return B(_iJ(_iK,_iL,_iS.a));}),new T(function(){return B(_iQ(_iS.b));}));});}};return new F(function(){return _iQ(_iN.a);});}},_iT=new T(function(){return B(unCStr("x"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("y"));}),_iW=new T1(0,_iV),_iX=new T(function(){return B(unCStr("z"));}),_iY=new T1(0,_iX),_iZ=new T3(0,E(_iU),E(_iW),E(_iY)),_j0=new T(function(){return B(unCStr(","));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr("pow("));}),_j3=new T1(0,_j2),_j4=new T(function(){return B(unCStr(")"));}),_j5=new T1(0,_j4),_j6=new T2(1,_j5,_w),_j7=function(_j8,_j9){return new T1(1,new T2(1,_j3,new T2(1,_j8,new T2(1,_j1,new T2(1,_j9,_j6)))));},_ja=new T(function(){return B(unCStr("acos("));}),_jb=new T1(0,_ja),_jc=function(_jd){return new T1(1,new T2(1,_jb,new T2(1,_jd,_j6)));},_je=new T(function(){return B(unCStr("acosh("));}),_jf=new T1(0,_je),_jg=function(_jh){return new T1(1,new T2(1,_jf,new T2(1,_jh,_j6)));},_ji=new T(function(){return B(unCStr("asin("));}),_jj=new T1(0,_ji),_jk=function(_jl){return new T1(1,new T2(1,_jj,new T2(1,_jl,_j6)));},_jm=new T(function(){return B(unCStr("asinh("));}),_jn=new T1(0,_jm),_jo=function(_jp){return new T1(1,new T2(1,_jn,new T2(1,_jp,_j6)));},_jq=new T(function(){return B(unCStr("atan("));}),_jr=new T1(0,_jq),_js=function(_jt){return new T1(1,new T2(1,_jr,new T2(1,_jt,_j6)));},_ju=new T(function(){return B(unCStr("atanh("));}),_jv=new T1(0,_ju),_jw=function(_jx){return new T1(1,new T2(1,_jv,new T2(1,_jx,_j6)));},_jy=new T(function(){return B(unCStr("cos("));}),_jz=new T1(0,_jy),_jA=function(_jB){return new T1(1,new T2(1,_jz,new T2(1,_jB,_j6)));},_jC=new T(function(){return B(unCStr("cosh("));}),_jD=new T1(0,_jC),_jE=function(_jF){return new T1(1,new T2(1,_jD,new T2(1,_jF,_j6)));},_jG=new T(function(){return B(unCStr("exp("));}),_jH=new T1(0,_jG),_jI=function(_jJ){return new T1(1,new T2(1,_jH,new T2(1,_jJ,_j6)));},_jK=new T(function(){return B(unCStr("log("));}),_jL=new T1(0,_jK),_jM=function(_jN){return new T1(1,new T2(1,_jL,new T2(1,_jN,_j6)));},_jO=new T(function(){return B(unCStr(")/log("));}),_jP=new T1(0,_jO),_jQ=function(_jR,_jS){return new T1(1,new T2(1,_jL,new T2(1,_jS,new T2(1,_jP,new T2(1,_jR,_j6)))));},_jT=new T(function(){return B(unCStr("pi"));}),_jU=new T1(0,_jT),_jV=new T(function(){return B(unCStr("sin("));}),_jW=new T1(0,_jV),_jX=function(_jY){return new T1(1,new T2(1,_jW,new T2(1,_jY,_j6)));},_jZ=new T(function(){return B(unCStr("sinh("));}),_k0=new T1(0,_jZ),_k1=function(_k2){return new T1(1,new T2(1,_k0,new T2(1,_k2,_j6)));},_k3=new T(function(){return B(unCStr("sqrt("));}),_k4=new T1(0,_k3),_k5=function(_k6){return new T1(1,new T2(1,_k4,new T2(1,_k6,_j6)));},_k7=new T(function(){return B(unCStr("tan("));}),_k8=new T1(0,_k7),_k9=function(_ka){return new T1(1,new T2(1,_k8,new T2(1,_ka,_j6)));},_kb=new T(function(){return B(unCStr("tanh("));}),_kc=new T1(0,_kb),_kd=function(_ke){return new T1(1,new T2(1,_kc,new T2(1,_ke,_j6)));},_kf=new T(function(){return B(unCStr("("));}),_kg=new T1(0,_kf),_kh=new T(function(){return B(unCStr(")/("));}),_ki=new T1(0,_kh),_kj=function(_kk,_kl){return new T1(1,new T2(1,_kg,new T2(1,_kk,new T2(1,_ki,new T2(1,_kl,_j6)))));},_km=function(_kn){return new T1(0,new T(function(){var _ko=E(_kn),_kp=jsShow(B(_6y(_ko.a,_ko.b)));return fromJSStr(_kp);}));},_kq=new T(function(){return B(unCStr("1./("));}),_kr=new T1(0,_kq),_ks=function(_kt){return new T1(1,new T2(1,_kr,new T2(1,_kt,_j6)));},_ku=new T(function(){return B(unCStr(")+("));}),_kv=new T1(0,_ku),_kw=function(_kx,_ky){return new T1(1,new T2(1,_kg,new T2(1,_kx,new T2(1,_kv,new T2(1,_ky,_j6)))));},_kz=new T(function(){return B(unCStr("-("));}),_kA=new T1(0,_kz),_kB=function(_kC){return new T1(1,new T2(1,_kA,new T2(1,_kC,_j6)));},_kD=new T(function(){return B(unCStr(")*("));}),_kE=new T1(0,_kD),_kF=function(_kG,_kH){return new T1(1,new T2(1,_kg,new T2(1,_kG,new T2(1,_kE,new T2(1,_kH,_j6)))));},_kI=function(_kJ,_kK){return new F(function(){return A3(_6X,_kL,_kJ,new T(function(){return B(A2(_6Z,_kL,_kK));}));});},_kM=new T(function(){return B(unCStr("abs("));}),_kN=new T1(0,_kM),_kO=function(_kP){return new T1(1,new T2(1,_kN,new T2(1,_kP,_j6)));},_kQ=new T(function(){return B(unCStr("."));}),_kR=function(_kS){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kS,_w)),_kQ));}));},_kT=new T(function(){return B(unCStr("sign("));}),_kU=new T1(0,_kT),_kV=function(_kW){return new T1(1,new T2(1,_kU,new T2(1,_kW,_j6)));},_kL=new T(function(){return {_:0,a:_kw,b:_kI,c:_kF,d:_kB,e:_kO,f:_kV,g:_kR};}),_kX=new T4(0,_kL,_kj,_ks,_km),_kY={_:0,a:_kX,b:_jU,c:_jI,d:_jM,e:_k5,f:_j7,g:_jQ,h:_jX,i:_jA,j:_k9,k:_jk,l:_jc,m:_js,n:_k1,o:_jE,p:_kd,q:_jo,r:_jg,s:_jw},_kZ=new T(function(){return B(unCStr("(/=) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T(function(){return B(unCStr("(==) is not defined"));}),_l2=new T(function(){return B(err(_l1));}),_l3=new T2(0,_l2,_l0),_l4=new T(function(){return B(unCStr("(<) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(<=) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("(>=) is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("compare is not defined"));}),_ld=new T(function(){return B(err(_lc));}),_le=new T(function(){return B(unCStr("max("));}),_lf=new T1(0,_le),_lg=function(_lh,_li){return new T1(1,new T2(1,_lf,new T2(1,_lh,new T2(1,_j1,new T2(1,_li,_j6)))));},_lj=new T(function(){return B(unCStr("min("));}),_lk=new T1(0,_lj),_ll=function(_lm,_ln){return new T1(1,new T2(1,_lk,new T2(1,_lm,new T2(1,_j1,new T2(1,_ln,_j6)))));},_lo={_:0,a:_l3,b:_ld,c:_l5,d:_l7,e:_l9,f:_lb,g:_lg,h:_ll},_lp=new T2(0,_kY,_lo),_lq=new T(function(){return B(_hO(_lp));}),_lr=new T(function(){return B(A1(_lq,_iZ));}),_ls=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lr)));}),_lt=new T(function(){return eval("__strict(compile)");}),_lu=new T(function(){return toJSStr(E(_iV));}),_lv=function(_lw,_lx,_ly){var _lz=new T(function(){return B(_0(_lw));}),_lA=new T(function(){return B(_2(_lw));}),_lB=function(_lC){var _lD=E(_lC);if(!_lD._){return E(_lA);}else{return new F(function(){return A2(_lz,new T(function(){return B(_iJ(_lw,_lx,_lD.a));}),new T(function(){return B(_lB(_lD.b));}));});}};return new F(function(){return _lB(_ly);});},_lE=new T(function(){return B(unCStr("vec3("));}),_lF=new T1(0,_lE),_lG=new T(function(){return B(_7i(0,_8r,_w));}),_lH=new T(function(){return B(_n(_lG,_kQ));}),_lI=new T1(0,_lH),_lJ=new T(function(){return B(_7i(0,_8q,_w));}),_lK=new T(function(){return B(_n(_lJ,_kQ));}),_lL=new T1(0,_lK),_lM=new T2(1,_lL,_w),_lN=new T2(1,_lI,_lM),_lO=function(_lP,_lQ){var _lR=E(_lQ);return (_lR._==0)?__Z:new T2(1,_lP,new T2(1,_lR.a,new T(function(){return B(_lO(_lP,_lR.b));})));},_lS=new T(function(){return B(_lO(_j1,_lN));}),_lT=new T2(1,_lL,_lS),_lU=new T1(1,_lT),_lV=new T2(1,_lU,_j6),_lW=new T2(1,_lF,_lV),_lX=new T(function(){return toJSStr(B(_lv(_x,_iD,_lW)));}),_lY=function(_lZ,_m0){while(1){var _m1=E(_lZ);if(!_m1._){return E(_m0);}else{var _m2=_m0+1|0;_lZ=_m1.b;_m0=_m2;continue;}}},_m3=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_m4=new T(function(){return B(err(_m3));}),_m5=0,_m6=new T3(0,E(_m5),E(_m5),E(_m5)),_m7=new T(function(){return B(unCStr("Negative exponent"));}),_m8=new T(function(){return B(err(_m7));}),_m9=function(_ma,_mb,_mc){while(1){if(!(_mb%2)){var _md=_ma*_ma,_me=quot(_mb,2);_ma=_md;_mb=_me;continue;}else{var _mf=E(_mb);if(_mf==1){return _ma*_mc;}else{var _md=_ma*_ma,_mg=_ma*_mc;_ma=_md;_mb=quot(_mf-1|0,2);_mc=_mg;continue;}}}},_mh=function(_mi,_mj){while(1){if(!(_mj%2)){var _mk=_mi*_mi,_ml=quot(_mj,2);_mi=_mk;_mj=_ml;continue;}else{var _mm=E(_mj);if(_mm==1){return E(_mi);}else{return new F(function(){return _m9(_mi*_mi,quot(_mm-1|0,2),_mi);});}}}},_mn=function(_mo){var _mp=E(_mo);return new F(function(){return Math.log(_mp+(_mp+1)*Math.sqrt((_mp-1)/(_mp+1)));});},_mq=function(_mr){var _ms=E(_mr);return new F(function(){return Math.log(_ms+Math.sqrt(1+_ms*_ms));});},_mt=function(_mu){var _mv=E(_mu);return 0.5*Math.log((1+_mv)/(1-_mv));},_mw=function(_mx,_my){return Math.log(E(_my))/Math.log(E(_mx));},_mz=3.141592653589793,_mA=function(_mB){var _mC=E(_mB);return new F(function(){return _6y(_mC.a,_mC.b);});},_mD=function(_mE){return 1/E(_mE);},_mF=function(_mG){var _mH=E(_mG),_mI=E(_mH);return (_mI==0)?E(_6x):(_mI<=0)? -_mI:E(_mH);},_mJ=function(_mK){var _mL=E(_mK);if(!_mL._){return _mL.a;}else{return new F(function(){return I_toNumber(_mL.a);});}},_mM=function(_mN){return new F(function(){return _mJ(_mN);});},_mO=1,_mP=-1,_mQ=function(_mR){var _mS=E(_mR);return (_mS<=0)?(_mS>=0)?E(_mS):E(_mP):E(_mO);},_mT=function(_mU,_mV){return E(_mU)-E(_mV);},_mW=function(_mX){return  -E(_mX);},_mY=function(_mZ,_n0){return E(_mZ)+E(_n0);},_n1=function(_n2,_n3){return E(_n2)*E(_n3);},_n4={_:0,a:_mY,b:_mT,c:_n1,d:_mW,e:_mF,f:_mQ,g:_mM},_n5=function(_n6,_n7){return E(_n6)/E(_n7);},_n8=new T4(0,_n4,_n5,_mD,_mA),_n9=function(_na){return new F(function(){return Math.acos(E(_na));});},_nb=function(_nc){return new F(function(){return Math.asin(E(_nc));});},_nd=function(_ne){return new F(function(){return Math.atan(E(_ne));});},_nf=function(_ng){return new F(function(){return Math.cos(E(_ng));});},_nh=function(_ni){return new F(function(){return cosh(E(_ni));});},_nj=function(_nk){return new F(function(){return Math.exp(E(_nk));});},_nl=function(_nm){return new F(function(){return Math.log(E(_nm));});},_nn=function(_no,_np){return new F(function(){return Math.pow(E(_no),E(_np));});},_nq=function(_nr){return new F(function(){return Math.sin(E(_nr));});},_ns=function(_nt){return new F(function(){return sinh(E(_nt));});},_nu=function(_nv){return new F(function(){return Math.sqrt(E(_nv));});},_nw=function(_nx){return new F(function(){return Math.tan(E(_nx));});},_ny=function(_nz){return new F(function(){return tanh(E(_nz));});},_nA={_:0,a:_n8,b:_mz,c:_nj,d:_nl,e:_nu,f:_nn,g:_mw,h:_nq,i:_nf,j:_nw,k:_nb,l:_n9,m:_nd,n:_ns,o:_nh,p:_ny,q:_mq,r:_mn,s:_mt},_nB=function(_nC,_nD){return (E(_nC)!=E(_nD))?true:false;},_nE=function(_nF,_nG){return E(_nF)==E(_nG);},_nH=new T2(0,_nE,_nB),_nI=function(_nJ,_nK){return E(_nJ)<E(_nK);},_nL=function(_nM,_nN){return E(_nM)<=E(_nN);},_nO=function(_nP,_nQ){return E(_nP)>E(_nQ);},_nR=function(_nS,_nT){return E(_nS)>=E(_nT);},_nU=function(_nV,_nW){var _nX=E(_nV),_nY=E(_nW);return (_nX>=_nY)?(_nX!=_nY)?2:1:0;},_nZ=function(_o0,_o1){var _o2=E(_o0),_o3=E(_o1);return (_o2>_o3)?E(_o2):E(_o3);},_o4=function(_o5,_o6){var _o7=E(_o5),_o8=E(_o6);return (_o7>_o8)?E(_o8):E(_o7);},_o9={_:0,a:_nH,b:_nU,c:_nI,d:_nL,e:_nO,f:_nR,g:_nZ,h:_o4},_oa="dz",_ob="wy",_oc="wx",_od="dy",_oe="dx",_of="t",_og="a",_oh="r",_oi="ly",_oj="lx",_ok="wz",_ol=0,_om=function(_on){var _oo=__new(),_op=_oo,_oq=function(_or,_){while(1){var _os=E(_or);if(!_os._){return _ol;}else{var _ot=E(_os.a),_ou=__set(_op,E(_ot.a),E(_ot.b));_or=_os.b;continue;}}},_ov=B(_oq(_on,_));return E(_op);},_ow=function(_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE,_oF){return new F(function(){return _om(new T2(1,new T2(0,_oc,_ox),new T2(1,new T2(0,_ob,_oy),new T2(1,new T2(0,_ok,_oz),new T2(1,new T2(0,_oj,_oA*_oB*Math.cos(_oC)),new T2(1,new T2(0,_oi,_oA*_oB*Math.sin(_oC)),new T2(1,new T2(0,_oh,_oA),new T2(1,new T2(0,_og,_oB),new T2(1,new T2(0,_of,_oC),new T2(1,new T2(0,_oe,_oD),new T2(1,new T2(0,_od,_oE),new T2(1,new T2(0,_oa,_oF),_w))))))))))));});},_oG=function(_oH){var _oI=E(_oH),_oJ=E(_oI.a),_oK=E(_oI.b),_oL=E(_oI.d);return new F(function(){return _ow(_oJ.a,_oJ.b,_oJ.c,E(_oK.a),E(_oK.b),E(_oI.c),_oL.a,_oL.b,_oL.c);});},_oM=function(_oN,_oO){var _oP=E(_oO);return (_oP._==0)?__Z:new T2(1,new T(function(){return B(A1(_oN,_oP.a));}),new T(function(){return B(_oM(_oN,_oP.b));}));},_oQ=function(_oR,_oS,_oT){var _oU=__lst2arr(B(_oM(_oG,new T2(1,_oR,new T2(1,_oS,new T2(1,_oT,_w))))));return E(_oU);},_oV=function(_oW){var _oX=E(_oW);return new F(function(){return _oQ(_oX.a,_oX.b,_oX.c);});},_oY=new T2(0,_nA,_o9),_oZ=function(_p0,_p1,_p2,_p3,_p4,_p5,_p6){var _p7=B(_8J(B(_8H(_p0)))),_p8=new T(function(){return B(A3(_6X,_p7,new T(function(){return B(A3(_8L,_p7,_p1,_p4));}),new T(function(){return B(A3(_8L,_p7,_p2,_p5));})));});return new F(function(){return A3(_6X,_p7,_p8,new T(function(){return B(A3(_8L,_p7,_p3,_p6));}));});},_p9=function(_pa,_pb,_pc,_pd){var _pe=B(_8H(_pa)),_pf=new T(function(){return B(A2(_9t,_pa,new T(function(){return B(_oZ(_pa,_pb,_pc,_pd,_pb,_pc,_pd));})));});return new T3(0,B(A3(_8P,_pe,_pb,_pf)),B(A3(_8P,_pe,_pc,_pf)),B(A3(_8P,_pe,_pd,_pf)));},_pg=function(_ph,_pi,_pj,_pk,_pl,_pm,_pn){var _po=B(_8L(_ph));return new T3(0,B(A1(B(A1(_po,_pi)),_pl)),B(A1(B(A1(_po,_pj)),_pm)),B(A1(B(A1(_po,_pk)),_pn)));},_pp=function(_pq,_pr,_ps,_pt,_pu,_pv,_pw){var _px=B(_6X(_pq));return new T3(0,B(A1(B(A1(_px,_pr)),_pu)),B(A1(B(A1(_px,_ps)),_pv)),B(A1(B(A1(_px,_pt)),_pw)));},_py=function(_pz,_pA){var _pB=new T(function(){return E(E(_pz).a);}),_pC=new T(function(){var _pD=E(_pA),_pE=new T(function(){return B(_8J(new T(function(){return B(_8H(_pB));})));}),_pF=B(A2(_8s,_pE,_8q));return new T3(0,E(_pF),E(B(A2(_8s,_pE,_8r))),E(_pF));}),_pG=new T(function(){var _pH=E(_pC),_pI=B(_p9(_pB,_pH.a,_pH.b,_pH.c));return new T3(0,E(_pI.a),E(_pI.b),E(_pI.c));}),_pJ=new T(function(){var _pK=E(_pA),_pL=_pK.b,_pM=E(_pG),_pN=B(_8H(_pB)),_pO=new T(function(){return B(A2(_9t,_pB,new T(function(){var _pP=E(_pC),_pQ=_pP.a,_pR=_pP.b,_pS=_pP.c;return B(_oZ(_pB,_pQ,_pR,_pS,_pQ,_pR,_pS));})));}),_pT=B(A3(_8P,_pN,_pL,_pO)),_pU=B(_8J(_pN)),_pV=B(_pg(_pU,_pM.a,_pM.b,_pM.c,_pT,_pT,_pT)),_pW=B(_6Z(_pU)),_pX=B(_pp(_pU,_pK.a,_pL,_pK.c,B(A1(_pW,_pV.a)),B(A1(_pW,_pV.b)),B(A1(_pW,_pV.c))));return new T3(0,E(_pX.a),E(_pX.b),E(_pX.c));});return new T2(0,_pJ,_pG);},_pY=function(_pZ){return E(E(_pZ).a);},_q0=function(_q1,_q2,_q3,_q4,_q5,_q6,_q7){var _q8=B(_oZ(_q1,_q5,_q6,_q7,_q2,_q3,_q4)),_q9=B(_8J(B(_8H(_q1)))),_qa=B(_pg(_q9,_q5,_q6,_q7,_q8,_q8,_q8)),_qb=B(_6Z(_q9));return new F(function(){return _pp(_q9,_q2,_q3,_q4,B(A1(_qb,_qa.a)),B(A1(_qb,_qa.b)),B(A1(_qb,_qa.c)));});},_qc=function(_qd){return E(E(_qd).a);},_qe=function(_qf,_qg,_qh,_qi){var _qj=new T(function(){var _qk=E(_qi),_ql=E(_qh),_qm=B(_q0(_qf,_qk.a,_qk.b,_qk.c,_ql.a,_ql.b,_ql.c));return new T3(0,E(_qm.a),E(_qm.b),E(_qm.c));}),_qn=new T(function(){return B(A2(_9t,_qf,new T(function(){var _qo=E(_qj),_qp=_qo.a,_qq=_qo.b,_qr=_qo.c;return B(_oZ(_qf,_qp,_qq,_qr,_qp,_qq,_qr));})));});if(!B(A3(_qc,B(_pY(_qg)),_qn,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qf)))),_8q));})))){var _qs=E(_qj),_qt=B(_p9(_qf,_qs.a,_qs.b,_qs.c)),_qu=B(A2(_9t,_qf,new T(function(){var _qv=E(_qi),_qw=_qv.a,_qx=_qv.b,_qy=_qv.c;return B(_oZ(_qf,_qw,_qx,_qy,_qw,_qx,_qy));}))),_qz=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qf));})));})));return new T3(0,B(A1(B(A1(_qz,_qt.a)),_qu)),B(A1(B(A1(_qz,_qt.b)),_qu)),B(A1(B(A1(_qz,_qt.c)),_qu)));}else{var _qA=B(A2(_8s,B(_8J(B(_8H(_qf)))),_8q));return new T3(0,_qA,_qA,_qA);}},_qB=new T(function(){var _qC=eval("angleCount"),_qD=Number(_qC);return jsTrunc(_qD);}),_qE=new T(function(){return E(_qB);}),_qF=new T(function(){return B(unCStr(": empty list"));}),_qG=new T(function(){return B(unCStr("Prelude."));}),_qH=function(_qI){return new F(function(){return err(B(_n(_qG,new T(function(){return B(_n(_qI,_qF));},1))));});},_qJ=new T(function(){return B(unCStr("head"));}),_qK=new T(function(){return B(_qH(_qJ));}),_qL=function(_qM,_qN,_qO){var _qP=E(_qM);if(!_qP._){return __Z;}else{var _qQ=E(_qN);if(!_qQ._){return __Z;}else{var _qR=_qQ.a,_qS=E(_qO);if(!_qS._){return __Z;}else{var _qT=E(_qS.a),_qU=_qT.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_qP.a),E(_qR),E(_qU));}),new T2(1,new T(function(){return new T3(0,E(_qR),E(_qU),E(_qT.b));}),_w)),new T(function(){return B(_qL(_qP.b,_qQ.b,_qS.b));},1));});}}}},_qV=new T(function(){return B(unCStr("tail"));}),_qW=new T(function(){return B(_qH(_qV));}),_qX=function(_qY,_qZ){var _r0=E(_qY);if(!_r0._){return __Z;}else{var _r1=E(_qZ);return (_r1._==0)?__Z:new T2(1,new T2(0,_r0.a,_r1.a),new T(function(){return B(_qX(_r0.b,_r1.b));}));}},_r2=function(_r3,_r4){var _r5=E(_r3);if(!_r5._){return __Z;}else{var _r6=E(_r4);if(!_r6._){return __Z;}else{var _r7=E(_r5.a),_r8=_r7.b,_r9=E(_r6.a).b,_ra=new T(function(){var _rb=new T(function(){return B(_qX(_r9,new T(function(){var _rc=E(_r9);if(!_rc._){return E(_qW);}else{return E(_rc.b);}},1)));},1);return B(_qL(_r8,new T(function(){var _rd=E(_r8);if(!_rd._){return E(_qW);}else{return E(_rd.b);}},1),_rb));});return new F(function(){return _n(new T2(1,new T(function(){var _re=E(_r8);if(!_re._){return E(_qK);}else{var _rf=E(_r9);if(!_rf._){return E(_qK);}else{return new T3(0,E(_r7.a),E(_re.a),E(_rf.a));}}}),_ra),new T(function(){return B(_r2(_r5.b,_r6.b));},1));});}}},_rg=new T(function(){return E(_qE)-1;}),_rh=new T1(0,1),_ri=function(_rj,_rk){var _rl=E(_rk),_rm=new T(function(){var _rn=B(_8J(_rj)),_ro=B(_ri(_rj,B(A3(_6X,_rn,_rl,new T(function(){return B(A2(_8s,_rn,_rh));})))));return new T2(1,_ro.a,_ro.b);});return new T2(0,_rl,_rm);},_rp=function(_rq){return E(E(_rq).d);},_rr=new T1(0,2),_rs=function(_rt,_ru){var _rv=E(_ru);if(!_rv._){return __Z;}else{var _rw=_rv.a;return (!B(A1(_rt,_rw)))?__Z:new T2(1,_rw,new T(function(){return B(_rs(_rt,_rv.b));}));}},_rx=function(_ry,_rz,_rA,_rB){var _rC=B(_ri(_rz,_rA)),_rD=new T(function(){var _rE=B(_8J(_rz)),_rF=new T(function(){return B(A3(_8P,_rz,new T(function(){return B(A2(_8s,_rE,_rh));}),new T(function(){return B(A2(_8s,_rE,_rr));})));});return B(A3(_6X,_rE,_rB,_rF));});return new F(function(){return _rs(function(_rG){return new F(function(){return A3(_rp,_ry,_rG,_rD);});},new T2(1,_rC.a,_rC.b));});},_rH=new T(function(){return B(_rx(_o9,_n8,_m5,_rg));}),_rI=function(_rJ,_rK){while(1){var _rL=E(_rJ);if(!_rL._){return E(_rK);}else{_rJ=_rL.b;_rK=_rL.a;continue;}}},_rM=new T(function(){return B(unCStr("last"));}),_rN=new T(function(){return B(_qH(_rM));}),_rO=function(_rP){return new F(function(){return _rI(_rP,_rN);});},_rQ=function(_rR){return new F(function(){return _rO(E(_rR).b);});},_rS=new T(function(){var _rT=eval("proceedCount"),_rU=Number(_rT);return jsTrunc(_rU);}),_rV=new T(function(){return E(_rS);}),_rW=1,_rX=new T(function(){return B(_rx(_o9,_n8,_rW,_rV));}),_rY=function(_rZ,_s0,_s1,_s2,_s3,_s4,_s5,_s6,_s7,_s8,_s9,_sa,_sb,_sc){var _sd=new T(function(){var _se=new T(function(){var _sf=E(_s8),_sg=E(_sc),_sh=E(_sb),_si=E(_s9),_sj=E(_sa),_sk=E(_s7);return new T3(0,_sf*_sg-_sh*_si,_si*_sj-_sg*_sk,_sk*_sh-_sj*_sf);}),_sl=function(_sm){var _sn=new T(function(){var _so=E(_sm)/E(_qE);return (_so+_so)*3.141592653589793;}),_sp=new T(function(){return B(A1(_rZ,_sn));}),_sq=new T(function(){var _sr=new T(function(){var _ss=E(_sp)/E(_rV);return new T3(0,E(_ss),E(_ss),E(_ss));}),_st=function(_su,_sv){var _sw=E(_su);if(!_sw._){return new T2(0,_w,_sv);}else{var _sx=new T(function(){var _sy=B(_py(_oY,new T(function(){var _sz=E(_sv),_sA=E(_sz.a),_sB=E(_sz.b),_sC=E(_sr);return new T3(0,E(_sA.a)+E(_sB.a)*E(_sC.a),E(_sA.b)+E(_sB.b)*E(_sC.b),E(_sA.c)+E(_sB.c)*E(_sC.c));}))),_sD=_sy.a,_sE=new T(function(){var _sF=E(_sy.b),_sG=E(E(_sv).b),_sH=B(_q0(_nA,_sG.a,_sG.b,_sG.c,_sF.a,_sF.b,_sF.c)),_sI=B(_p9(_nA,_sH.a,_sH.b,_sH.c));return new T3(0,E(_sI.a),E(_sI.b),E(_sI.c));});return new T2(0,new T(function(){var _sJ=E(_sp),_sK=E(_sn);return new T4(0,E(_sD),E(new T2(0,E(_sw.a)/E(_rV),E(_sJ))),E(_sK),E(_sE));}),new T2(0,_sD,_sE));}),_sL=new T(function(){var _sM=B(_st(_sw.b,new T(function(){return E(E(_sx).b);})));return new T2(0,_sM.a,_sM.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sx).a);}),new T(function(){return E(E(_sL).a);})),new T(function(){return E(E(_sL).b);}));}},_sN=function(_sO,_sP,_sQ,_sR,_sS){var _sT=E(_sO);if(!_sT._){return new T2(0,_w,new T2(0,new T3(0,E(_sP),E(_sQ),E(_sR)),_sS));}else{var _sU=new T(function(){var _sV=B(_py(_oY,new T(function(){var _sW=E(_sS),_sX=E(_sr);return new T3(0,E(_sP)+E(_sW.a)*E(_sX.a),E(_sQ)+E(_sW.b)*E(_sX.b),E(_sR)+E(_sW.c)*E(_sX.c));}))),_sY=_sV.a,_sZ=new T(function(){var _t0=E(_sV.b),_t1=E(_sS),_t2=B(_q0(_nA,_t1.a,_t1.b,_t1.c,_t0.a,_t0.b,_t0.c)),_t3=B(_p9(_nA,_t2.a,_t2.b,_t2.c));return new T3(0,E(_t3.a),E(_t3.b),E(_t3.c));});return new T2(0,new T(function(){var _t4=E(_sp),_t5=E(_sn);return new T4(0,E(_sY),E(new T2(0,E(_sT.a)/E(_rV),E(_t4))),E(_t5),E(_sZ));}),new T2(0,_sY,_sZ));}),_t6=new T(function(){var _t7=B(_st(_sT.b,new T(function(){return E(E(_sU).b);})));return new T2(0,_t7.a,_t7.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sU).a);}),new T(function(){return E(E(_t6).a);})),new T(function(){return E(E(_t6).b);}));}};return E(B(_sN(_rX,_s2,_s3,_s4,new T(function(){var _t8=E(_se),_t9=E(_sn)+_s5,_ta=Math.cos(_t9),_tb=Math.sin(_t9);return new T3(0,E(_s7)*_ta+E(_t8.a)*_tb,E(_s8)*_ta+E(_t8.b)*_tb,E(_s9)*_ta+E(_t8.c)*_tb);}))).a);});return new T2(0,new T(function(){var _tc=E(_sp),_td=E(_sn);return new T4(0,E(new T3(0,E(_s2),E(_s3),E(_s4))),E(new T2(0,E(_m5),E(_tc))),E(_td),E(_m6));}),_sq);};return B(_oM(_sl,_rH));}),_te=new T(function(){var _tf=new T(function(){var _tg=B(_n(_sd,new T2(1,new T(function(){var _th=E(_sd);if(!_th._){return E(_qK);}else{return E(_th.a);}}),_w)));if(!_tg._){return E(_qW);}else{return E(_tg.b);}},1);return B(_r2(_sd,_tf));});return new T2(0,_te,new T(function(){return B(_oM(_rQ,_sd));}));},_ti=function(_tj,_tk,_tl,_tm,_tn,_to,_tp,_tq,_tr,_ts,_tt,_tu,_tv,_tw,_tx,_ty,_tz){var _tA=B(_py(_oY,new T3(0,E(_tm),E(_tn),E(_to)))),_tB=_tA.b,_tC=E(_tA.a),_tD=B(_qe(_nA,_o9,_tB,new T3(0,E(_tq),E(_tr),E(_ts)))),_tE=E(_tB),_tF=_tE.a,_tG=_tE.b,_tH=_tE.c,_tI=B(_q0(_nA,_tu,_tv,_tw,_tF,_tG,_tH)),_tJ=B(_p9(_nA,_tI.a,_tI.b,_tI.c)),_tK=_tJ.a,_tL=_tJ.b,_tM=_tJ.c,_tN=E(_tp),_tO=new T2(0,E(new T3(0,E(_tD.a),E(_tD.b),E(_tD.c))),E(_tt)),_tP=B(_rY(_tj,_tk,_tl,_tC.a,_tC.b,_tC.c,_tN,_tO,_tK,_tL,_tM,_tF,_tG,_tH)),_tQ=__lst2arr(B(_oM(_oV,_tP.a))),_tR=__lst2arr(B(_oM(_oG,_tP.b)));return {_:0,a:_tj,b:_tk,c:_tl,d:new T2(0,E(_tC),E(_tN)),e:_tO,f:new T3(0,E(_tK),E(_tL),E(_tM)),g:_tE,h:_tQ,i:_tR};},_tS=-4,_tT=new T3(0,E(_m5),E(_m5),E(_tS)),_tU=function(_tV){return E(_tT);},_tW=new T(function(){return 6.283185307179586/E(_qE);}),_tX=function(_){return new F(function(){return __jsNull();});},_tY=function(_tZ){var _u0=B(A1(_tZ,_));return E(_u0);},_u1=new T(function(){return B(_tY(_tX));}),_u2=function(_u3,_u4,_u5,_u6,_u7,_u8,_u9,_ua,_ub,_uc,_ud,_ue,_uf){var _ug=function(_uh){var _ui=E(_tW),_uj=2+_uh|0,_uk=_uj-1|0,_ul=(2+_uh)*(1+_uh),_um=E(_rH);if(!_um._){return _ui*0;}else{var _un=_um.a,_uo=_um.b,_up=B(A1(_u3,new T(function(){return 6.283185307179586*E(_un)/E(_qE);}))),_uq=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_un)+1)/E(_qE);})));if(_up!=_uq){if(_uj>=0){var _ur=E(_uj);if(!_ur){var _us=function(_ut,_uu){while(1){var _uv=B((function(_uw,_ux){var _uy=E(_uw);if(!_uy._){return E(_ux);}else{var _uz=_uy.a,_uA=_uy.b,_uB=B(A1(_u3,new T(function(){return 6.283185307179586*E(_uz)/E(_qE);}))),_uC=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_uz)+1)/E(_qE);})));if(_uB!=_uC){var _uD=_ux+0/(_uB-_uC)/_ul;_ut=_uA;_uu=_uD;return __continue;}else{if(_uk>=0){var _uE=E(_uk);if(!_uE){var _uD=_ux+_uj/_ul;_ut=_uA;_uu=_uD;return __continue;}else{var _uD=_ux+_uj*B(_mh(_uB,_uE))/_ul;_ut=_uA;_uu=_uD;return __continue;}}else{return E(_m8);}}}})(_ut,_uu));if(_uv!=__continue){return _uv;}}};return _ui*B(_us(_uo,0/(_up-_uq)/_ul));}else{var _uF=function(_uG,_uH){while(1){var _uI=B((function(_uJ,_uK){var _uL=E(_uJ);if(!_uL._){return E(_uK);}else{var _uM=_uL.a,_uN=_uL.b,_uO=B(A1(_u3,new T(function(){return 6.283185307179586*E(_uM)/E(_qE);}))),_uP=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_uM)+1)/E(_qE);})));if(_uO!=_uP){if(_ur>=0){var _uQ=_uK+(B(_mh(_uO,_ur))-B(_mh(_uP,_ur)))/(_uO-_uP)/_ul;_uG=_uN;_uH=_uQ;return __continue;}else{return E(_m8);}}else{if(_uk>=0){var _uR=E(_uk);if(!_uR){var _uQ=_uK+_uj/_ul;_uG=_uN;_uH=_uQ;return __continue;}else{var _uQ=_uK+_uj*B(_mh(_uO,_uR))/_ul;_uG=_uN;_uH=_uQ;return __continue;}}else{return E(_m8);}}}})(_uG,_uH));if(_uI!=__continue){return _uI;}}};return _ui*B(_uF(_uo,(B(_mh(_up,_ur))-B(_mh(_uq,_ur)))/(_up-_uq)/_ul));}}else{return E(_m8);}}else{if(_uk>=0){var _uS=E(_uk);if(!_uS){var _uT=function(_uU,_uV){while(1){var _uW=B((function(_uX,_uY){var _uZ=E(_uX);if(!_uZ._){return E(_uY);}else{var _v0=_uZ.a,_v1=_uZ.b,_v2=B(A1(_u3,new T(function(){return 6.283185307179586*E(_v0)/E(_qE);}))),_v3=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_v0)+1)/E(_qE);})));if(_v2!=_v3){if(_uj>=0){var _v4=E(_uj);if(!_v4){var _v5=_uY+0/(_v2-_v3)/_ul;_uU=_v1;_uV=_v5;return __continue;}else{var _v5=_uY+(B(_mh(_v2,_v4))-B(_mh(_v3,_v4)))/(_v2-_v3)/_ul;_uU=_v1;_uV=_v5;return __continue;}}else{return E(_m8);}}else{var _v5=_uY+_uj/_ul;_uU=_v1;_uV=_v5;return __continue;}}})(_uU,_uV));if(_uW!=__continue){return _uW;}}};return _ui*B(_uT(_uo,_uj/_ul));}else{var _v6=function(_v7,_v8){while(1){var _v9=B((function(_va,_vb){var _vc=E(_va);if(!_vc._){return E(_vb);}else{var _vd=_vc.a,_ve=_vc.b,_vf=B(A1(_u3,new T(function(){return 6.283185307179586*E(_vd)/E(_qE);}))),_vg=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_vd)+1)/E(_qE);})));if(_vf!=_vg){if(_uj>=0){var _vh=E(_uj);if(!_vh){var _vi=_vb+0/(_vf-_vg)/_ul;_v7=_ve;_v8=_vi;return __continue;}else{var _vi=_vb+(B(_mh(_vf,_vh))-B(_mh(_vg,_vh)))/(_vf-_vg)/_ul;_v7=_ve;_v8=_vi;return __continue;}}else{return E(_m8);}}else{if(_uS>=0){var _vi=_vb+_uj*B(_mh(_vf,_uS))/_ul;_v7=_ve;_v8=_vi;return __continue;}else{return E(_m8);}}}})(_v7,_v8));if(_v9!=__continue){return _v9;}}};return _ui*B(_v6(_uo,_uj*B(_mh(_up,_uS))/_ul));}}else{return E(_m8);}}}},_vj=E(_u1),_vk=1/(B(_ug(1))*_u4);return new F(function(){return _ti(_u3,_tU,new T2(0,E(new T3(0,E(_vk),E(_vk),E(_vk))),1/(B(_ug(3))*_u4)),_u5,_u6,_u7,_u8,_u9,_ua,_ub,_uc,_ud,_ue,_uf,_m6,_vj,_vj);});},_vl=1,_vm=0,_vn=function(_vo){var _vp=I_decodeDouble(_vo);return new T2(0,new T1(1,_vp.b),_vp.a);},_vq=function(_vr){return new T1(0,_vr);},_vs=function(_vt){var _vu=hs_intToInt64(2147483647),_vv=hs_leInt64(_vt,_vu);if(!_vv){return new T1(1,I_fromInt64(_vt));}else{var _vw=hs_intToInt64(-2147483648),_vx=hs_geInt64(_vt,_vw);if(!_vx){return new T1(1,I_fromInt64(_vt));}else{var _vy=hs_int64ToInt(_vt);return new F(function(){return _vq(_vy);});}}},_vz=new T(function(){var _vA=newByteArr(256),_vB=_vA,_=_vB["v"]["i8"][0]=8,_vC=function(_vD,_vE,_vF,_){while(1){if(_vF>=256){if(_vD>=256){return E(_);}else{var _vG=imul(2,_vD)|0,_vH=_vE+1|0,_vI=_vD;_vD=_vG;_vE=_vH;_vF=_vI;continue;}}else{var _=_vB["v"]["i8"][_vF]=_vE,_vI=_vF+_vD|0;_vF=_vI;continue;}}},_=B(_vC(2,0,1,_));return _vB;}),_vJ=function(_vK,_vL){var _vM=hs_int64ToInt(_vK),_vN=E(_vz),_vO=_vN["v"]["i8"][(255&_vM>>>0)>>>0&4294967295];if(_vL>_vO){if(_vO>=8){var _vP=hs_uncheckedIShiftRA64(_vK,8),_vQ=function(_vR,_vS){while(1){var _vT=B((function(_vU,_vV){var _vW=hs_int64ToInt(_vU),_vX=_vN["v"]["i8"][(255&_vW>>>0)>>>0&4294967295];if(_vV>_vX){if(_vX>=8){var _vY=hs_uncheckedIShiftRA64(_vU,8),_vZ=_vV-8|0;_vR=_vY;_vS=_vZ;return __continue;}else{return new T2(0,new T(function(){var _w0=hs_uncheckedIShiftRA64(_vU,_vX);return B(_vs(_w0));}),_vV-_vX|0);}}else{return new T2(0,new T(function(){var _w1=hs_uncheckedIShiftRA64(_vU,_vV);return B(_vs(_w1));}),0);}})(_vR,_vS));if(_vT!=__continue){return _vT;}}};return new F(function(){return _vQ(_vP,_vL-8|0);});}else{return new T2(0,new T(function(){var _w2=hs_uncheckedIShiftRA64(_vK,_vO);return B(_vs(_w2));}),_vL-_vO|0);}}else{return new T2(0,new T(function(){var _w3=hs_uncheckedIShiftRA64(_vK,_vL);return B(_vs(_w3));}),0);}},_w4=function(_w5){var _w6=hs_intToInt64(_w5);return E(_w6);},_w7=function(_w8){var _w9=E(_w8);if(!_w9._){return new F(function(){return _w4(_w9.a);});}else{return new F(function(){return I_toInt64(_w9.a);});}},_wa=function(_wb){return I_toInt(_wb)>>>0;},_wc=function(_wd){var _we=E(_wd);if(!_we._){return _we.a>>>0;}else{return new F(function(){return _wa(_we.a);});}},_wf=function(_wg){var _wh=B(_vn(_wg)),_wi=_wh.a,_wj=_wh.b;if(_wj<0){var _wk=function(_wl){if(!_wl){return new T2(0,E(_wi),B(_3J(_21, -_wj)));}else{var _wm=B(_vJ(B(_w7(_wi)), -_wj));return new T2(0,E(_wm.a),B(_3J(_21,_wm.b)));}};if(!((B(_wc(_wi))&1)>>>0)){return new F(function(){return _wk(1);});}else{return new F(function(){return _wk(0);});}}else{return new T2(0,B(_3J(_wi,_wj)),_21);}},_wn=function(_wo){var _wp=B(_wf(E(_wo)));return new T2(0,E(_wp.a),E(_wp.b));},_wq=new T3(0,_n4,_o9,_wn),_wr=function(_ws){return E(E(_ws).a);},_wt=function(_wu){return E(E(_wu).a);},_wv=function(_ww,_wx){if(_ww<=_wx){var _wy=function(_wz){return new T2(1,_wz,new T(function(){if(_wz!=_wx){return B(_wy(_wz+1|0));}else{return __Z;}}));};return new F(function(){return _wy(_ww);});}else{return __Z;}},_wA=function(_wB){return new F(function(){return _wv(E(_wB),2147483647);});},_wC=function(_wD,_wE,_wF){if(_wF<=_wE){var _wG=new T(function(){var _wH=_wE-_wD|0,_wI=function(_wJ){return (_wJ>=(_wF-_wH|0))?new T2(1,_wJ,new T(function(){return B(_wI(_wJ+_wH|0));})):new T2(1,_wJ,_w);};return B(_wI(_wE));});return new T2(1,_wD,_wG);}else{return (_wF<=_wD)?new T2(1,_wD,_w):__Z;}},_wK=function(_wL,_wM,_wN){if(_wN>=_wM){var _wO=new T(function(){var _wP=_wM-_wL|0,_wQ=function(_wR){return (_wR<=(_wN-_wP|0))?new T2(1,_wR,new T(function(){return B(_wQ(_wR+_wP|0));})):new T2(1,_wR,_w);};return B(_wQ(_wM));});return new T2(1,_wL,_wO);}else{return (_wN>=_wL)?new T2(1,_wL,_w):__Z;}},_wS=function(_wT,_wU){if(_wU<_wT){return new F(function(){return _wC(_wT,_wU,-2147483648);});}else{return new F(function(){return _wK(_wT,_wU,2147483647);});}},_wV=function(_wW,_wX){return new F(function(){return _wS(E(_wW),E(_wX));});},_wY=function(_wZ,_x0,_x1){if(_x0<_wZ){return new F(function(){return _wC(_wZ,_x0,_x1);});}else{return new F(function(){return _wK(_wZ,_x0,_x1);});}},_x2=function(_x3,_x4,_x5){return new F(function(){return _wY(E(_x3),E(_x4),E(_x5));});},_x6=function(_x7,_x8){return new F(function(){return _wv(E(_x7),E(_x8));});},_x9=function(_xa){return E(_xa);},_xb=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xc=new T(function(){return B(err(_xb));}),_xd=function(_xe){var _xf=E(_xe);return (_xf==(-2147483648))?E(_xc):_xf-1|0;},_xg=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xh=new T(function(){return B(err(_xg));}),_xi=function(_xj){var _xk=E(_xj);return (_xk==2147483647)?E(_xh):_xk+1|0;},_xl={_:0,a:_xi,b:_xd,c:_x9,d:_x9,e:_wA,f:_wV,g:_x6,h:_x2},_xm=function(_xn,_xo){if(_xn<=0){if(_xn>=0){return new F(function(){return quot(_xn,_xo);});}else{if(_xo<=0){return new F(function(){return quot(_xn,_xo);});}else{return quot(_xn+1|0,_xo)-1|0;}}}else{if(_xo>=0){if(_xn>=0){return new F(function(){return quot(_xn,_xo);});}else{if(_xo<=0){return new F(function(){return quot(_xn,_xo);});}else{return quot(_xn+1|0,_xo)-1|0;}}}else{return quot(_xn-1|0,_xo)-1|0;}}},_xp=0,_xq=new T(function(){return B(_36(_xp));}),_xr=new T(function(){return die(_xq);}),_xs=function(_xt,_xu){var _xv=E(_xu);switch(_xv){case -1:var _xw=E(_xt);if(_xw==(-2147483648)){return E(_xr);}else{return new F(function(){return _xm(_xw,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xm(_xt,_xv);});}},_xx=function(_xy,_xz){return new F(function(){return _xs(E(_xy),E(_xz));});},_xA=0,_xB=new T2(0,_xr,_xA),_xC=function(_xD,_xE){var _xF=E(_xD),_xG=E(_xE);switch(_xG){case -1:var _xH=E(_xF);if(_xH==(-2147483648)){return E(_xB);}else{if(_xH<=0){if(_xH>=0){var _xI=quotRemI(_xH,-1);return new T2(0,_xI.a,_xI.b);}else{var _xJ=quotRemI(_xH,-1);return new T2(0,_xJ.a,_xJ.b);}}else{var _xK=quotRemI(_xH-1|0,-1);return new T2(0,_xK.a-1|0,(_xK.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_xF<=0){if(_xF>=0){var _xL=quotRemI(_xF,_xG);return new T2(0,_xL.a,_xL.b);}else{if(_xG<=0){var _xM=quotRemI(_xF,_xG);return new T2(0,_xM.a,_xM.b);}else{var _xN=quotRemI(_xF+1|0,_xG);return new T2(0,_xN.a-1|0,(_xN.b+_xG|0)-1|0);}}}else{if(_xG>=0){if(_xF>=0){var _xO=quotRemI(_xF,_xG);return new T2(0,_xO.a,_xO.b);}else{if(_xG<=0){var _xP=quotRemI(_xF,_xG);return new T2(0,_xP.a,_xP.b);}else{var _xQ=quotRemI(_xF+1|0,_xG);return new T2(0,_xQ.a-1|0,(_xQ.b+_xG|0)-1|0);}}}else{var _xR=quotRemI(_xF-1|0,_xG);return new T2(0,_xR.a-1|0,(_xR.b+_xG|0)+1|0);}}}},_xS=function(_xT,_xU){var _xV=_xT%_xU;if(_xT<=0){if(_xT>=0){return E(_xV);}else{if(_xU<=0){return E(_xV);}else{var _xW=E(_xV);return (_xW==0)?0:_xW+_xU|0;}}}else{if(_xU>=0){if(_xT>=0){return E(_xV);}else{if(_xU<=0){return E(_xV);}else{var _xX=E(_xV);return (_xX==0)?0:_xX+_xU|0;}}}else{var _xY=E(_xV);return (_xY==0)?0:_xY+_xU|0;}}},_xZ=function(_y0,_y1){var _y2=E(_y1);switch(_y2){case -1:return E(_xA);case 0:return E(_3a);default:return new F(function(){return _xS(E(_y0),_y2);});}},_y3=function(_y4,_y5){var _y6=E(_y4),_y7=E(_y5);switch(_y7){case -1:var _y8=E(_y6);if(_y8==(-2147483648)){return E(_xr);}else{return new F(function(){return quot(_y8,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_y6,_y7);});}},_y9=function(_ya,_yb){var _yc=E(_ya),_yd=E(_yb);switch(_yd){case -1:var _ye=E(_yc);if(_ye==(-2147483648)){return E(_xB);}else{var _yf=quotRemI(_ye,-1);return new T2(0,_yf.a,_yf.b);}break;case 0:return E(_3a);default:var _yg=quotRemI(_yc,_yd);return new T2(0,_yg.a,_yg.b);}},_yh=function(_yi,_yj){var _yk=E(_yj);switch(_yk){case -1:return E(_xA);case 0:return E(_3a);default:return E(_yi)%_yk;}},_yl=function(_ym){return new F(function(){return _vq(E(_ym));});},_yn=function(_yo){return new T2(0,E(B(_vq(E(_yo)))),E(_rh));},_yp=function(_yq,_yr){return imul(E(_yq),E(_yr))|0;},_ys=function(_yt,_yu){return E(_yt)+E(_yu)|0;},_yv=function(_yw,_yx){return E(_yw)-E(_yx)|0;},_yy=function(_yz){var _yA=E(_yz);return (_yA<0)? -_yA:E(_yA);},_yB=function(_yC){return new F(function(){return _3n(_yC);});},_yD=function(_yE){return  -E(_yE);},_yF=-1,_yG=0,_yH=1,_yI=function(_yJ){var _yK=E(_yJ);return (_yK>=0)?(E(_yK)==0)?E(_yG):E(_yH):E(_yF);},_yL={_:0,a:_ys,b:_yv,c:_yp,d:_yD,e:_yy,f:_yI,g:_yB},_yM=function(_yN,_yO){return E(_yN)==E(_yO);},_yP=function(_yQ,_yR){return E(_yQ)!=E(_yR);},_yS=new T2(0,_yM,_yP),_yT=function(_yU,_yV){var _yW=E(_yU),_yX=E(_yV);return (_yW>_yX)?E(_yW):E(_yX);},_yY=function(_yZ,_z0){var _z1=E(_yZ),_z2=E(_z0);return (_z1>_z2)?E(_z2):E(_z1);},_z3=function(_z4,_z5){return (_z4>=_z5)?(_z4!=_z5)?2:1:0;},_z6=function(_z7,_z8){return new F(function(){return _z3(E(_z7),E(_z8));});},_z9=function(_za,_zb){return E(_za)>=E(_zb);},_zc=function(_zd,_ze){return E(_zd)>E(_ze);},_zf=function(_zg,_zh){return E(_zg)<=E(_zh);},_zi=function(_zj,_zk){return E(_zj)<E(_zk);},_zl={_:0,a:_yS,b:_z6,c:_zi,d:_zf,e:_zc,f:_z9,g:_yT,h:_yY},_zm=new T3(0,_yL,_zl,_yn),_zn={_:0,a:_zm,b:_xl,c:_y3,d:_yh,e:_xx,f:_xZ,g:_y9,h:_xC,i:_yl},_zo=new T1(0,2),_zp=function(_zq,_zr){while(1){var _zs=E(_zq);if(!_zs._){var _zt=_zs.a,_zu=E(_zr);if(!_zu._){var _zv=_zu.a;if(!(imul(_zt,_zv)|0)){return new T1(0,imul(_zt,_zv)|0);}else{_zq=new T1(1,I_fromInt(_zt));_zr=new T1(1,I_fromInt(_zv));continue;}}else{_zq=new T1(1,I_fromInt(_zt));_zr=_zu;continue;}}else{var _zw=E(_zr);if(!_zw._){_zq=_zs;_zr=new T1(1,I_fromInt(_zw.a));continue;}else{return new T1(1,I_mul(_zs.a,_zw.a));}}}},_zx=function(_zy,_zz,_zA){while(1){if(!(_zz%2)){var _zB=B(_zp(_zy,_zy)),_zC=quot(_zz,2);_zy=_zB;_zz=_zC;continue;}else{var _zD=E(_zz);if(_zD==1){return new F(function(){return _zp(_zy,_zA);});}else{var _zB=B(_zp(_zy,_zy)),_zE=B(_zp(_zy,_zA));_zy=_zB;_zz=quot(_zD-1|0,2);_zA=_zE;continue;}}}},_zF=function(_zG,_zH){while(1){if(!(_zH%2)){var _zI=B(_zp(_zG,_zG)),_zJ=quot(_zH,2);_zG=_zI;_zH=_zJ;continue;}else{var _zK=E(_zH);if(_zK==1){return E(_zG);}else{return new F(function(){return _zx(B(_zp(_zG,_zG)),quot(_zK-1|0,2),_zG);});}}}},_zL=function(_zM){return E(E(_zM).b);},_zN=function(_zO){return E(E(_zO).c);},_zP=new T1(0,0),_zQ=function(_zR){return E(E(_zR).d);},_zS=function(_zT,_zU){var _zV=B(_wr(_zT)),_zW=new T(function(){return B(_wt(_zV));}),_zX=new T(function(){return B(A3(_zQ,_zT,_zU,new T(function(){return B(A2(_8s,_zW,_rr));})));});return new F(function(){return A3(_qc,B(_pY(B(_zL(_zV)))),_zX,new T(function(){return B(A2(_8s,_zW,_zP));}));});},_zY=new T(function(){return B(unCStr("Negative exponent"));}),_zZ=new T(function(){return B(err(_zY));}),_A0=function(_A1){return E(E(_A1).c);},_A2=function(_A3,_A4,_A5,_A6){var _A7=B(_wr(_A4)),_A8=new T(function(){return B(_wt(_A7));}),_A9=B(_zL(_A7));if(!B(A3(_zN,_A9,_A6,new T(function(){return B(A2(_8s,_A8,_zP));})))){if(!B(A3(_qc,B(_pY(_A9)),_A6,new T(function(){return B(A2(_8s,_A8,_zP));})))){var _Aa=new T(function(){return B(A2(_8s,_A8,_rr));}),_Ab=new T(function(){return B(A2(_8s,_A8,_rh));}),_Ac=B(_pY(_A9)),_Ad=function(_Ae,_Af,_Ag){while(1){var _Ah=B((function(_Ai,_Aj,_Ak){if(!B(_zS(_A4,_Aj))){if(!B(A3(_qc,_Ac,_Aj,_Ab))){var _Al=new T(function(){return B(A3(_A0,_A4,new T(function(){return B(A3(_9p,_A8,_Aj,_Ab));}),_Aa));});_Ae=new T(function(){return B(A3(_8L,_A3,_Ai,_Ai));});_Af=_Al;_Ag=new T(function(){return B(A3(_8L,_A3,_Ai,_Ak));});return __continue;}else{return new F(function(){return A3(_8L,_A3,_Ai,_Ak);});}}else{var _Am=_Ak;_Ae=new T(function(){return B(A3(_8L,_A3,_Ai,_Ai));});_Af=new T(function(){return B(A3(_A0,_A4,_Aj,_Aa));});_Ag=_Am;return __continue;}})(_Ae,_Af,_Ag));if(_Ah!=__continue){return _Ah;}}},_An=function(_Ao,_Ap){while(1){var _Aq=B((function(_Ar,_As){if(!B(_zS(_A4,_As))){if(!B(A3(_qc,_Ac,_As,_Ab))){var _At=new T(function(){return B(A3(_A0,_A4,new T(function(){return B(A3(_9p,_A8,_As,_Ab));}),_Aa));});return new F(function(){return _Ad(new T(function(){return B(A3(_8L,_A3,_Ar,_Ar));}),_At,_Ar);});}else{return E(_Ar);}}else{_Ao=new T(function(){return B(A3(_8L,_A3,_Ar,_Ar));});_Ap=new T(function(){return B(A3(_A0,_A4,_As,_Aa));});return __continue;}})(_Ao,_Ap));if(_Aq!=__continue){return _Aq;}}};return new F(function(){return _An(_A5,_A6);});}else{return new F(function(){return A2(_8s,_A3,_rh);});}}else{return E(_zZ);}},_Au=new T(function(){return B(err(_zY));}),_Av=function(_Aw,_Ax){var _Ay=B(_vn(_Ax)),_Az=_Ay.a,_AA=_Ay.b,_AB=new T(function(){return B(_wt(new T(function(){return B(_wr(_Aw));})));});if(_AA<0){var _AC= -_AA;if(_AC>=0){var _AD=E(_AC);if(!_AD){var _AE=E(_rh);}else{var _AE=B(_zF(_zo,_AD));}if(!B(_3f(_AE,_3I))){var _AF=B(_3z(_Az,_AE));return new T2(0,new T(function(){return B(A2(_8s,_AB,_AF.a));}),new T(function(){return B(_3b(_AF.b,_AA));}));}else{return E(_3a);}}else{return E(_Au);}}else{var _AG=new T(function(){var _AH=new T(function(){return B(_A2(_AB,_zn,new T(function(){return B(A2(_8s,_AB,_zo));}),_AA));});return B(A3(_8L,_AB,new T(function(){return B(A2(_8s,_AB,_Az));}),_AH));});return new T2(0,_AG,_6x);}},_AI=function(_AJ,_AK){var _AL=B(_Av(_AJ,E(_AK))),_AM=_AL.a;if(E(_AL.b)<=0){return E(_AM);}else{var _AN=B(_wt(B(_wr(_AJ))));return new F(function(){return A3(_6X,_AN,_AM,new T(function(){return B(A2(_8s,_AN,_21));}));});}},_AO=function(_AP,_AQ){var _AR=B(_Av(_AP,E(_AQ))),_AS=_AR.a;if(E(_AR.b)>=0){return E(_AS);}else{var _AT=B(_wt(B(_wr(_AP))));return new F(function(){return A3(_9p,_AT,_AS,new T(function(){return B(A2(_8s,_AT,_21));}));});}},_AU=function(_AV,_AW){var _AX=B(_Av(_AV,E(_AW)));return new T2(0,_AX.a,_AX.b);},_AY=function(_AZ,_B0){var _B1=B(_Av(_AZ,_B0)),_B2=_B1.a,_B3=E(_B1.b),_B4=new T(function(){var _B5=B(_wt(B(_wr(_AZ))));if(_B3>=0){return B(A3(_6X,_B5,_B2,new T(function(){return B(A2(_8s,_B5,_21));})));}else{return B(A3(_9p,_B5,_B2,new T(function(){return B(A2(_8s,_B5,_21));})));}}),_B6=function(_B7){var _B8=_B7-0.5;return (_B8>=0)?(E(_B8)==0)?(!B(_zS(_AZ,_B2)))?E(_B4):E(_B2):E(_B4):E(_B2);},_B9=E(_B3);if(!_B9){return new F(function(){return _B6(0);});}else{if(_B9<=0){var _Ba= -_B9-0.5;return (_Ba>=0)?(E(_Ba)==0)?(!B(_zS(_AZ,_B2)))?E(_B4):E(_B2):E(_B4):E(_B2);}else{return new F(function(){return _B6(_B9);});}}},_Bb=function(_Bc,_Bd){return new F(function(){return _AY(_Bc,E(_Bd));});},_Be=function(_Bf,_Bg){return E(B(_Av(_Bf,E(_Bg))).a);},_Bh={_:0,a:_wq,b:_n8,c:_AU,d:_Be,e:_Bb,f:_AI,g:_AO},_Bi=new T1(0,1),_Bj=function(_Bk,_Bl){var _Bm=E(_Bk);return new T2(0,_Bm,new T(function(){var _Bn=B(_Bj(B(_3q(_Bm,_Bl)),_Bl));return new T2(1,_Bn.a,_Bn.b);}));},_Bo=function(_Bp){var _Bq=B(_Bj(_Bp,_Bi));return new T2(1,_Bq.a,_Bq.b);},_Br=function(_Bs,_Bt){var _Bu=B(_Bj(_Bs,new T(function(){return B(_5L(_Bt,_Bs));})));return new T2(1,_Bu.a,_Bu.b);},_Bv=new T1(0,0),_Bw=function(_Bx,_By){var _Bz=E(_Bx);if(!_Bz._){var _BA=_Bz.a,_BB=E(_By);return (_BB._==0)?_BA>=_BB.a:I_compareInt(_BB.a,_BA)<=0;}else{var _BC=_Bz.a,_BD=E(_By);return (_BD._==0)?I_compareInt(_BC,_BD.a)>=0:I_compare(_BC,_BD.a)>=0;}},_BE=function(_BF,_BG,_BH){if(!B(_Bw(_BG,_Bv))){var _BI=function(_BJ){return (!B(_42(_BJ,_BH)))?new T2(1,_BJ,new T(function(){return B(_BI(B(_3q(_BJ,_BG))));})):__Z;};return new F(function(){return _BI(_BF);});}else{var _BK=function(_BL){return (!B(_3T(_BL,_BH)))?new T2(1,_BL,new T(function(){return B(_BK(B(_3q(_BL,_BG))));})):__Z;};return new F(function(){return _BK(_BF);});}},_BM=function(_BN,_BO,_BP){return new F(function(){return _BE(_BN,B(_5L(_BO,_BN)),_BP);});},_BQ=function(_BR,_BS){return new F(function(){return _BE(_BR,_Bi,_BS);});},_BT=function(_BU){return new F(function(){return _3n(_BU);});},_BV=function(_BW){return new F(function(){return _5L(_BW,_Bi);});},_BX=function(_BY){return new F(function(){return _3q(_BY,_Bi);});},_BZ=function(_C0){return new F(function(){return _vq(E(_C0));});},_C1={_:0,a:_BX,b:_BV,c:_BZ,d:_BT,e:_Bo,f:_Br,g:_BQ,h:_BM},_C2=function(_C3,_C4){while(1){var _C5=E(_C3);if(!_C5._){var _C6=E(_C5.a);if(_C6==(-2147483648)){_C3=new T1(1,I_fromInt(-2147483648));continue;}else{var _C7=E(_C4);if(!_C7._){return new T1(0,B(_xm(_C6,_C7.a)));}else{_C3=new T1(1,I_fromInt(_C6));_C4=_C7;continue;}}}else{var _C8=_C5.a,_C9=E(_C4);return (_C9._==0)?new T1(1,I_div(_C8,I_fromInt(_C9.a))):new T1(1,I_div(_C8,_C9.a));}}},_Ca=function(_Cb,_Cc){if(!B(_3f(_Cc,_zP))){return new F(function(){return _C2(_Cb,_Cc);});}else{return E(_3a);}},_Cd=function(_Ce,_Cf){while(1){var _Cg=E(_Ce);if(!_Cg._){var _Ch=E(_Cg.a);if(_Ch==(-2147483648)){_Ce=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ci=E(_Cf);if(!_Ci._){var _Cj=_Ci.a;return new T2(0,new T1(0,B(_xm(_Ch,_Cj))),new T1(0,B(_xS(_Ch,_Cj))));}else{_Ce=new T1(1,I_fromInt(_Ch));_Cf=_Ci;continue;}}}else{var _Ck=E(_Cf);if(!_Ck._){_Ce=_Cg;_Cf=new T1(1,I_fromInt(_Ck.a));continue;}else{var _Cl=I_divMod(_Cg.a,_Ck.a);return new T2(0,new T1(1,_Cl.a),new T1(1,_Cl.b));}}}},_Cm=function(_Cn,_Co){if(!B(_3f(_Co,_zP))){var _Cp=B(_Cd(_Cn,_Co));return new T2(0,_Cp.a,_Cp.b);}else{return E(_3a);}},_Cq=function(_Cr,_Cs){while(1){var _Ct=E(_Cr);if(!_Ct._){var _Cu=E(_Ct.a);if(_Cu==(-2147483648)){_Cr=new T1(1,I_fromInt(-2147483648));continue;}else{var _Cv=E(_Cs);if(!_Cv._){return new T1(0,B(_xS(_Cu,_Cv.a)));}else{_Cr=new T1(1,I_fromInt(_Cu));_Cs=_Cv;continue;}}}else{var _Cw=_Ct.a,_Cx=E(_Cs);return (_Cx._==0)?new T1(1,I_mod(_Cw,I_fromInt(_Cx.a))):new T1(1,I_mod(_Cw,_Cx.a));}}},_Cy=function(_Cz,_CA){if(!B(_3f(_CA,_zP))){return new F(function(){return _Cq(_Cz,_CA);});}else{return E(_3a);}},_CB=function(_CC,_CD){while(1){var _CE=E(_CC);if(!_CE._){var _CF=E(_CE.a);if(_CF==(-2147483648)){_CC=new T1(1,I_fromInt(-2147483648));continue;}else{var _CG=E(_CD);if(!_CG._){return new T1(0,quot(_CF,_CG.a));}else{_CC=new T1(1,I_fromInt(_CF));_CD=_CG;continue;}}}else{var _CH=_CE.a,_CI=E(_CD);return (_CI._==0)?new T1(0,I_toInt(I_quot(_CH,I_fromInt(_CI.a)))):new T1(1,I_quot(_CH,_CI.a));}}},_CJ=function(_CK,_CL){if(!B(_3f(_CL,_zP))){return new F(function(){return _CB(_CK,_CL);});}else{return E(_3a);}},_CM=function(_CN,_CO){if(!B(_3f(_CO,_zP))){var _CP=B(_3z(_CN,_CO));return new T2(0,_CP.a,_CP.b);}else{return E(_3a);}},_CQ=function(_CR,_CS){while(1){var _CT=E(_CR);if(!_CT._){var _CU=E(_CT.a);if(_CU==(-2147483648)){_CR=new T1(1,I_fromInt(-2147483648));continue;}else{var _CV=E(_CS);if(!_CV._){return new T1(0,_CU%_CV.a);}else{_CR=new T1(1,I_fromInt(_CU));_CS=_CV;continue;}}}else{var _CW=_CT.a,_CX=E(_CS);return (_CX._==0)?new T1(1,I_rem(_CW,I_fromInt(_CX.a))):new T1(1,I_rem(_CW,_CX.a));}}},_CY=function(_CZ,_D0){if(!B(_3f(_D0,_zP))){return new F(function(){return _CQ(_CZ,_D0);});}else{return E(_3a);}},_D1=function(_D2){return E(_D2);},_D3=function(_D4){return E(_D4);},_D5=function(_D6){var _D7=E(_D6);if(!_D7._){var _D8=E(_D7.a);return (_D8==(-2147483648))?E(_6p):(_D8<0)?new T1(0, -_D8):E(_D7);}else{var _D9=_D7.a;return (I_compareInt(_D9,0)>=0)?E(_D7):new T1(1,I_negate(_D9));}},_Da=new T1(0,0),_Db=new T1(0,-1),_Dc=function(_Dd){var _De=E(_Dd);if(!_De._){var _Df=_De.a;return (_Df>=0)?(E(_Df)==0)?E(_Da):E(_41):E(_Db);}else{var _Dg=I_compareInt(_De.a,0);return (_Dg<=0)?(E(_Dg)==0)?E(_Da):E(_Db):E(_41);}},_Dh={_:0,a:_3q,b:_5L,c:_zp,d:_6q,e:_D5,f:_Dc,g:_D3},_Di=function(_Dj,_Dk){var _Dl=E(_Dj);if(!_Dl._){var _Dm=_Dl.a,_Dn=E(_Dk);return (_Dn._==0)?_Dm!=_Dn.a:(I_compareInt(_Dn.a,_Dm)==0)?false:true;}else{var _Do=_Dl.a,_Dp=E(_Dk);return (_Dp._==0)?(I_compareInt(_Do,_Dp.a)==0)?false:true:(I_compare(_Do,_Dp.a)==0)?false:true;}},_Dq=new T2(0,_3f,_Di),_Dr=function(_Ds,_Dt){return (!B(_5w(_Ds,_Dt)))?E(_Ds):E(_Dt);},_Du=function(_Dv,_Dw){return (!B(_5w(_Dv,_Dw)))?E(_Dw):E(_Dv);},_Dx={_:0,a:_Dq,b:_22,c:_42,d:_5w,e:_3T,f:_Bw,g:_Dr,h:_Du},_Dy=function(_Dz){return new T2(0,E(_Dz),E(_rh));},_DA=new T3(0,_Dh,_Dx,_Dy),_DB={_:0,a:_DA,b:_C1,c:_CJ,d:_CY,e:_Ca,f:_Cy,g:_CM,h:_Cm,i:_D1},_DC=function(_DD){return E(E(_DD).b);},_DE=function(_DF){return E(E(_DF).g);},_DG=new T1(0,1),_DH=function(_DI,_DJ,_DK){var _DL=B(_DC(_DI)),_DM=B(_8J(_DL)),_DN=new T(function(){var _DO=new T(function(){var _DP=new T(function(){var _DQ=new T(function(){return B(A3(_DE,_DI,_DB,new T(function(){return B(A3(_8P,_DL,_DJ,_DK));})));});return B(A2(_8s,_DM,_DQ));}),_DR=new T(function(){return B(A2(_6Z,_DM,new T(function(){return B(A2(_8s,_DM,_DG));})));});return B(A3(_8L,_DM,_DR,_DP));});return B(A3(_8L,_DM,_DO,_DK));});return new F(function(){return A3(_6X,_DM,_DJ,_DN);});},_DS=1.5707963267948966,_DT=function(_DU){return 0.2/Math.cos(B(_DH(_Bh,_DU,_DS))-0.7853981633974483);},_DV=new T(function(){var _DW=B(_u2(_DT,1.2,_vm,_vm,_vl,_vm,_vm,_vm,_vm,_vm,_vl,_vl,_vl));return {_:0,a:E(_DW.a),b:E(_DW.b),c:E(_DW.c),d:E(_DW.d),e:E(_DW.e),f:E(_DW.f),g:E(_DW.g),h:_DW.h,i:_DW.i};}),_DX=0,_DY=0.3,_DZ=function(_E0){return E(_DY);},_E1=new T(function(){var _E2=B(_u2(_DZ,1.2,_vl,_vm,_vl,_vm,_vm,_vm,_vm,_vm,_vl,_vl,_vl));return {_:0,a:E(_E2.a),b:E(_E2.b),c:E(_E2.c),d:E(_E2.d),e:E(_E2.e),f:E(_E2.f),g:E(_E2.g),h:_E2.h,i:_E2.i};}),_E3=new T(function(){var _E4=B(_u2(_DZ,1.2,_vl,_vl,_vm,_vm,_vm,_vm,_vm,_vm,_vl,_vl,_vl));return {_:0,a:E(_E4.a),b:E(_E4.b),c:E(_E4.c),d:E(_E4.d),e:E(_E4.e),f:E(_E4.f),g:E(_E4.g),h:_E4.h,i:_E4.i};}),_E5=2,_E6=function(_E7){return 0.3/Math.cos(B(_DH(_Bh,_E7,_DS))-0.7853981633974483);},_E8=new T(function(){var _E9=B(_u2(_E6,1.2,_E5,_vl,_vl,_vm,_vm,_vm,_vm,_vm,_vl,_vl,_vl));return {_:0,a:E(_E9.a),b:E(_E9.b),c:E(_E9.c),d:E(_E9.d),e:E(_E9.e),f:E(_E9.f),g:E(_E9.g),h:_E9.h,i:_E9.i};}),_Ea=0.5,_Eb=new T(function(){var _Ec=B(_u2(_DZ,1.2,_vm,_vl,_Ea,_vm,_vm,_vm,_vm,_vm,_vl,_vl,_vl));return {_:0,a:E(_Ec.a),b:E(_Ec.b),c:E(_Ec.c),d:E(_Ec.d),e:E(_Ec.e),f:E(_Ec.f),g:E(_Ec.g),h:_Ec.h,i:_Ec.i};}),_Ed=new T2(1,_Eb,_w),_Ee=new T2(1,_E8,_Ed),_Ef=new T2(1,_E3,_Ee),_Eg=new T2(1,_E1,_Ef),_Eh=new T2(1,_DV,_Eg),_Ei=new T(function(){return B(unCStr("Negative range size"));}),_Ej=new T(function(){return B(err(_Ei));}),_Ek=function(_){var _El=B(_lY(_Eh,0))-1|0,_Em=function(_En){if(_En>=0){var _Eo=newArr(_En,_m4),_Ep=_Eo,_Eq=E(_En);if(!_Eq){return new T4(0,E(_DX),E(_El),0,_Ep);}else{var _Er=function(_Es,_Et,_){while(1){var _Eu=E(_Es);if(!_Eu._){return E(_);}else{var _=_Ep[_Et]=_Eu.a;if(_Et!=(_Eq-1|0)){var _Ev=_Et+1|0;_Es=_Eu.b;_Et=_Ev;continue;}else{return E(_);}}}},_=B((function(_Ew,_Ex,_Ey,_){var _=_Ep[_Ey]=_Ew;if(_Ey!=(_Eq-1|0)){return new F(function(){return _Er(_Ex,_Ey+1|0,_);});}else{return E(_);}})(_DV,_Eg,0,_));return new T4(0,E(_DX),E(_El),_Eq,_Ep);}}else{return E(_Ej);}};if(0>_El){return new F(function(){return _Em(0);});}else{return new F(function(){return _Em(_El+1|0);});}},_Ez=function(_EA){var _EB=B(A1(_EA,_));return E(_EB);},_EC=new T(function(){return B(_Ez(_Ek));}),_ED="outline",_EE="polygon",_EF=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_EG=new T(function(){return B(err(_EF));}),_EH=new T(function(){return eval("__strict(drawObjects)");}),_EI=new T(function(){return eval("__strict(draw)");}),_EJ=function(_EK,_EL){var _EM=jsShowI(_EK);return new F(function(){return _n(fromJSStr(_EM),_EL);});},_EN=function(_EO,_EP,_EQ){if(_EP>=0){return new F(function(){return _EJ(_EP,_EQ);});}else{if(_EO<=6){return new F(function(){return _EJ(_EP,_EQ);});}else{return new T2(1,_7g,new T(function(){var _ER=jsShowI(_EP);return B(_n(fromJSStr(_ER),new T2(1,_7f,_EQ)));}));}}},_ES=new T(function(){return B(unCStr(")"));}),_ET=function(_EU,_EV){var _EW=new T(function(){var _EX=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EN(0,_EU,_w)),_ES));})));},1);return B(_n(B(_EN(0,_EV,_w)),_EX));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_EW)));});},_EY=new T2(1,_ol,_w),_EZ=function(_F0){return E(_F0);},_F1=function(_F2){return E(_F2);},_F3=function(_F4,_F5){return E(_F5);},_F6=function(_F7,_F8){return E(_F7);},_F9=function(_Fa){return E(_Fa);},_Fb=new T2(0,_F9,_F6),_Fc=function(_Fd,_Fe){return E(_Fd);},_Ff=new T5(0,_Fb,_F1,_EZ,_F3,_Fc),_Fg="flipped2",_Fh="flipped1",_Fi="c1y",_Fj="c1x",_Fk="w2z",_Fl="w2y",_Fm="w2x",_Fn="w1z",_Fo="w1y",_Fp="w1x",_Fq="d2z",_Fr="d2y",_Fs="d2x",_Ft="d1z",_Fu="d1y",_Fv="d1x",_Fw="c2y",_Fx="c2x",_Fy=function(_Fz,_){var _FA=__get(_Fz,E(_Fp)),_FB=__get(_Fz,E(_Fo)),_FC=__get(_Fz,E(_Fn)),_FD=__get(_Fz,E(_Fm)),_FE=__get(_Fz,E(_Fl)),_FF=__get(_Fz,E(_Fk)),_FG=__get(_Fz,E(_Fj)),_FH=__get(_Fz,E(_Fi)),_FI=__get(_Fz,E(_Fx)),_FJ=__get(_Fz,E(_Fw)),_FK=__get(_Fz,E(_Fv)),_FL=__get(_Fz,E(_Fu)),_FM=__get(_Fz,E(_Ft)),_FN=__get(_Fz,E(_Fs)),_FO=__get(_Fz,E(_Fr)),_FP=__get(_Fz,E(_Fq)),_FQ=__get(_Fz,E(_Fh)),_FR=__get(_Fz,E(_Fg));return {_:0,a:E(new T3(0,E(_FA),E(_FB),E(_FC))),b:E(new T3(0,E(_FD),E(_FE),E(_FF))),c:E(new T2(0,E(_FG),E(_FH))),d:E(new T2(0,E(_FI),E(_FJ))),e:E(new T3(0,E(_FK),E(_FL),E(_FM))),f:E(new T3(0,E(_FN),E(_FO),E(_FP))),g:E(_FQ),h:E(_FR)};},_FS=function(_FT,_){var _FU=E(_FT);if(!_FU._){return _w;}else{var _FV=B(_Fy(E(_FU.a),_)),_FW=B(_FS(_FU.b,_));return new T2(1,_FV,_FW);}},_FX=function(_FY){var _FZ=E(_FY);return (E(_FZ.b)-E(_FZ.a)|0)+1|0;},_G0=function(_G1,_G2){var _G3=E(_G1),_G4=E(_G2);return (E(_G3.a)>_G4)?false:_G4<=E(_G3.b);},_G5=function(_G6){return new F(function(){return _EN(0,E(_G6),_w);});},_G7=function(_G8,_G9,_Ga){return new F(function(){return _EN(E(_G8),E(_G9),_Ga);});},_Gb=function(_Gc,_Gd){return new F(function(){return _EN(0,E(_Gc),_Gd);});},_Ge=function(_Gf,_Gg){return new F(function(){return _2Q(_Gb,_Gf,_Gg);});},_Gh=new T3(0,_G7,_G5,_Ge),_Gi=0,_Gj=function(_Gk,_Gl,_Gm){return new F(function(){return A1(_Gk,new T2(1,_2N,new T(function(){return B(A1(_Gl,_Gm));})));});},_Gn=new T(function(){return B(unCStr("foldr1"));}),_Go=new T(function(){return B(_qH(_Gn));}),_Gp=function(_Gq,_Gr){var _Gs=E(_Gr);if(!_Gs._){return E(_Go);}else{var _Gt=_Gs.a,_Gu=E(_Gs.b);if(!_Gu._){return E(_Gt);}else{return new F(function(){return A2(_Gq,_Gt,new T(function(){return B(_Gp(_Gq,_Gu));}));});}}},_Gv=new T(function(){return B(unCStr(" out of range "));}),_Gw=new T(function(){return B(unCStr("}.index: Index "));}),_Gx=new T(function(){return B(unCStr("Ix{"));}),_Gy=new T2(1,_7f,_w),_Gz=new T2(1,_7f,_Gy),_GA=0,_GB=function(_GC){return E(E(_GC).a);},_GD=function(_GE,_GF,_GG,_GH,_GI){var _GJ=new T(function(){var _GK=new T(function(){var _GL=new T(function(){var _GM=new T(function(){var _GN=new T(function(){return B(A3(_Gp,_Gj,new T2(1,new T(function(){return B(A3(_GB,_GG,_GA,_GH));}),new T2(1,new T(function(){return B(A3(_GB,_GG,_GA,_GI));}),_w)),_Gz));});return B(_n(_Gv,new T2(1,_7g,new T2(1,_7g,_GN))));});return B(A(_GB,[_GG,_Gi,_GF,new T2(1,_7f,_GM)]));});return B(_n(_Gw,new T2(1,_7g,_GL)));},1);return B(_n(_GE,_GK));},1);return new F(function(){return err(B(_n(_Gx,_GJ)));});},_GO=function(_GP,_GQ,_GR,_GS,_GT){return new F(function(){return _GD(_GP,_GQ,_GT,_GR,_GS);});},_GU=function(_GV,_GW,_GX,_GY){var _GZ=E(_GX);return new F(function(){return _GO(_GV,_GW,_GZ.a,_GZ.b,_GY);});},_H0=function(_H1,_H2,_H3,_H4){return new F(function(){return _GU(_H4,_H3,_H2,_H1);});},_H5=new T(function(){return B(unCStr("Int"));}),_H6=function(_H7,_H8){return new F(function(){return _H0(_Gh,_H8,_H7,_H5);});},_H9=function(_Ha,_Hb){var _Hc=E(_Ha),_Hd=E(_Hc.a),_He=E(_Hb);if(_Hd>_He){return new F(function(){return _H6(_He,_Hc);});}else{if(_He>E(_Hc.b)){return new F(function(){return _H6(_He,_Hc);});}else{return _He-_Hd|0;}}},_Hf=function(_Hg){var _Hh=E(_Hg);return new F(function(){return _x6(_Hh.a,_Hh.b);});},_Hi=function(_Hj){var _Hk=E(_Hj),_Hl=E(_Hk.a),_Hm=E(_Hk.b);return (_Hl>_Hm)?E(_Gi):(_Hm-_Hl|0)+1|0;},_Hn=function(_Ho,_Hp){return new F(function(){return _yv(_Hp,E(_Ho).a);});},_Hq={_:0,a:_zl,b:_Hf,c:_H9,d:_Hn,e:_G0,f:_Hi,g:_FX},_Hr=function(_Hs,_Ht,_){while(1){var _Hu=B((function(_Hv,_Hw,_){var _Hx=E(_Hv);if(!_Hx._){return new T2(0,_ol,_Hw);}else{var _Hy=B(A2(_Hx.a,_Hw,_));_Hs=_Hx.b;_Ht=new T(function(){return E(E(_Hy).b);});return __continue;}})(_Hs,_Ht,_));if(_Hu!=__continue){return _Hu;}}},_Hz=function(_HA,_HB){return new T2(1,_HA,_HB);},_HC=function(_HD,_HE){var _HF=E(_HE);return new T2(0,_HF.a,_HF.b);},_HG=function(_HH){return E(E(_HH).f);},_HI=function(_HJ,_HK,_HL){var _HM=E(_HK),_HN=_HM.a,_HO=_HM.b,_HP=function(_){var _HQ=B(A2(_HG,_HJ,_HM));if(_HQ>=0){var _HR=newArr(_HQ,_m4),_HS=_HR,_HT=E(_HQ);if(!_HT){return new T(function(){return new T4(0,E(_HN),E(_HO),0,_HS);});}else{var _HU=function(_HV,_HW,_){while(1){var _HX=E(_HV);if(!_HX._){return E(_);}else{var _=_HS[_HW]=_HX.a;if(_HW!=(_HT-1|0)){var _HY=_HW+1|0;_HV=_HX.b;_HW=_HY;continue;}else{return E(_);}}}},_=B(_HU(_HL,0,_));return new T(function(){return new T4(0,E(_HN),E(_HO),_HT,_HS);});}}else{return E(_Ej);}};return new F(function(){return _Ez(_HP);});},_HZ=function(_I0,_I1,_I2,_I3){var _I4=new T(function(){var _I5=E(_I3),_I6=_I5.c-1|0,_I7=new T(function(){return B(A2(_cF,_I1,_w));});if(0<=_I6){var _I8=new T(function(){return B(_8F(_I1));}),_I9=function(_Ia){var _Ib=new T(function(){var _Ic=new T(function(){return B(A1(_I2,new T(function(){return E(_I5.d[_Ia]);})));});return B(A3(_8T,_I8,_Hz,_Ic));});return new F(function(){return A3(_8R,_I1,_Ib,new T(function(){if(_Ia!=_I6){return B(_I9(_Ia+1|0));}else{return E(_I7);}}));});};return B(_I9(0));}else{return E(_I7);}}),_Id=new T(function(){return B(_HC(_I0,_I3));});return new F(function(){return A3(_8T,B(_8F(_I1)),function(_Ie){return new F(function(){return _HI(_I0,_Id,_Ie);});},_I4);});},_If=function(_Ig,_Ih,_Ii,_Ij,_Ik,_Il,_Im,_In,_Io){var _Ip=B(_8L(_Ig));return new T2(0,new T3(0,E(B(A1(B(A1(_Ip,_Ih)),_Il))),E(B(A1(B(A1(_Ip,_Ii)),_Im))),E(B(A1(B(A1(_Ip,_Ij)),_In)))),B(A1(B(A1(_Ip,_Ik)),_Io)));},_Iq=function(_Ir,_Is,_It,_Iu,_Iv,_Iw,_Ix,_Iy,_Iz){var _IA=B(_6X(_Ir));return new T2(0,new T3(0,E(B(A1(B(A1(_IA,_Is)),_Iw))),E(B(A1(B(A1(_IA,_It)),_Ix))),E(B(A1(B(A1(_IA,_Iu)),_Iy)))),B(A1(B(A1(_IA,_Iv)),_Iz)));},_IB=1.0e-2,_IC=function(_ID,_IE,_IF,_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN,_IO,_IP,_IQ,_IR,_IS,_IT){var _IU=B(_If(_n4,_IK,_IL,_IM,_IN,_IB,_IB,_IB,_IB)),_IV=E(_IU.a),_IW=B(_Iq(_n4,_IG,_IH,_II,_IJ,_IV.a,_IV.b,_IV.c,_IU.b)),_IX=E(_IW.a);return new F(function(){return _ti(_ID,_IE,_IF,_IX.a,_IX.b,_IX.c,_IW.b,_IK,_IL,_IM,_IN,_IO,_IP,_IQ,_IR,_IS,_IT);});},_IY=function(_IZ){var _J0=E(_IZ),_J1=E(_J0.d),_J2=E(_J1.a),_J3=E(_J0.e),_J4=E(_J3.a),_J5=E(_J0.f),_J6=B(_IC(_J0.a,_J0.b,_J0.c,_J2.a,_J2.b,_J2.c,_J1.b,_J4.a,_J4.b,_J4.c,_J3.b,_J5.a,_J5.b,_J5.c,_J0.g,_J0.h,_J0.i));return {_:0,a:E(_J6.a),b:E(_J6.b),c:E(_J6.c),d:E(_J6.d),e:E(_J6.e),f:E(_J6.f),g:E(_J6.g),h:_J6.h,i:_J6.i};},_J7=function(_J8,_J9,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg){var _Jh=B(_8J(B(_8H(_J8))));return new F(function(){return A3(_6X,_Jh,new T(function(){return B(_oZ(_J8,_J9,_Ja,_Jb,_Jd,_Je,_Jf));}),new T(function(){return B(A3(_8L,_Jh,_Jc,_Jg));}));});},_Ji=new T(function(){return B(unCStr("base"));}),_Jj=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Jk=new T(function(){return B(unCStr("IOException"));}),_Jl=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Ji,_Jj,_Jk),_Jm=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Jl,_w,_w),_Jn=function(_Jo){return E(_Jm);},_Jp=function(_Jq){var _Jr=E(_Jq);return new F(function(){return _2n(B(_2l(_Jr.a)),_Jn,_Jr.b);});},_Js=new T(function(){return B(unCStr(": "));}),_Jt=new T(function(){return B(unCStr(")"));}),_Ju=new T(function(){return B(unCStr(" ("));}),_Jv=new T(function(){return B(unCStr("interrupted"));}),_Jw=new T(function(){return B(unCStr("system error"));}),_Jx=new T(function(){return B(unCStr("unsatisified constraints"));}),_Jy=new T(function(){return B(unCStr("user error"));}),_Jz=new T(function(){return B(unCStr("permission denied"));}),_JA=new T(function(){return B(unCStr("illegal operation"));}),_JB=new T(function(){return B(unCStr("end of file"));}),_JC=new T(function(){return B(unCStr("resource exhausted"));}),_JD=new T(function(){return B(unCStr("resource busy"));}),_JE=new T(function(){return B(unCStr("does not exist"));}),_JF=new T(function(){return B(unCStr("already exists"));}),_JG=new T(function(){return B(unCStr("resource vanished"));}),_JH=new T(function(){return B(unCStr("timeout"));}),_JI=new T(function(){return B(unCStr("unsupported operation"));}),_JJ=new T(function(){return B(unCStr("hardware fault"));}),_JK=new T(function(){return B(unCStr("inappropriate type"));}),_JL=new T(function(){return B(unCStr("invalid argument"));}),_JM=new T(function(){return B(unCStr("failed"));}),_JN=new T(function(){return B(unCStr("protocol error"));}),_JO=function(_JP,_JQ){switch(E(_JP)){case 0:return new F(function(){return _n(_JF,_JQ);});break;case 1:return new F(function(){return _n(_JE,_JQ);});break;case 2:return new F(function(){return _n(_JD,_JQ);});break;case 3:return new F(function(){return _n(_JC,_JQ);});break;case 4:return new F(function(){return _n(_JB,_JQ);});break;case 5:return new F(function(){return _n(_JA,_JQ);});break;case 6:return new F(function(){return _n(_Jz,_JQ);});break;case 7:return new F(function(){return _n(_Jy,_JQ);});break;case 8:return new F(function(){return _n(_Jx,_JQ);});break;case 9:return new F(function(){return _n(_Jw,_JQ);});break;case 10:return new F(function(){return _n(_JN,_JQ);});break;case 11:return new F(function(){return _n(_JM,_JQ);});break;case 12:return new F(function(){return _n(_JL,_JQ);});break;case 13:return new F(function(){return _n(_JK,_JQ);});break;case 14:return new F(function(){return _n(_JJ,_JQ);});break;case 15:return new F(function(){return _n(_JI,_JQ);});break;case 16:return new F(function(){return _n(_JH,_JQ);});break;case 17:return new F(function(){return _n(_JG,_JQ);});break;default:return new F(function(){return _n(_Jv,_JQ);});}},_JR=new T(function(){return B(unCStr("}"));}),_JS=new T(function(){return B(unCStr("{handle: "));}),_JT=function(_JU,_JV,_JW,_JX,_JY,_JZ){var _K0=new T(function(){var _K1=new T(function(){var _K2=new T(function(){var _K3=E(_JX);if(!_K3._){return E(_JZ);}else{var _K4=new T(function(){return B(_n(_K3,new T(function(){return B(_n(_Jt,_JZ));},1)));},1);return B(_n(_Ju,_K4));}},1);return B(_JO(_JV,_K2));}),_K5=E(_JW);if(!_K5._){return E(_K1);}else{return B(_n(_K5,new T(function(){return B(_n(_Js,_K1));},1)));}}),_K6=E(_JY);if(!_K6._){var _K7=E(_JU);if(!_K7._){return E(_K0);}else{var _K8=E(_K7.a);if(!_K8._){var _K9=new T(function(){var _Ka=new T(function(){return B(_n(_JR,new T(function(){return B(_n(_Js,_K0));},1)));},1);return B(_n(_K8.a,_Ka));},1);return new F(function(){return _n(_JS,_K9);});}else{var _Kb=new T(function(){var _Kc=new T(function(){return B(_n(_JR,new T(function(){return B(_n(_Js,_K0));},1)));},1);return B(_n(_K8.a,_Kc));},1);return new F(function(){return _n(_JS,_Kb);});}}}else{return new F(function(){return _n(_K6.a,new T(function(){return B(_n(_Js,_K0));},1));});}},_Kd=function(_Ke){var _Kf=E(_Ke);return new F(function(){return _JT(_Kf.a,_Kf.b,_Kf.c,_Kf.d,_Kf.f,_w);});},_Kg=function(_Kh,_Ki,_Kj){var _Kk=E(_Ki);return new F(function(){return _JT(_Kk.a,_Kk.b,_Kk.c,_Kk.d,_Kk.f,_Kj);});},_Kl=function(_Km,_Kn){var _Ko=E(_Km);return new F(function(){return _JT(_Ko.a,_Ko.b,_Ko.c,_Ko.d,_Ko.f,_Kn);});},_Kp=function(_Kq,_Kr){return new F(function(){return _2Q(_Kl,_Kq,_Kr);});},_Ks=new T3(0,_Kg,_Kd,_Kp),_Kt=new T(function(){return new T5(0,_Jn,_Ks,_Ku,_Jp,_Kd);}),_Ku=function(_Kv){return new T2(0,_Kt,_Kv);},_Kw=__Z,_Kx=7,_Ky=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_Kz=new T6(0,_Kw,_Kx,_w,_Ky,_Kw,_Kw),_KA=new T(function(){return B(_Ku(_Kz));}),_KB=function(_){return new F(function(){return die(_KA);});},_KC=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_KD=new T6(0,_Kw,_Kx,_w,_KC,_Kw,_Kw),_KE=new T(function(){return B(_Ku(_KD));}),_KF=function(_){return new F(function(){return die(_KE);});},_KG=function(_KH,_){return new T2(0,_w,_KH);},_KI=0.6,_KJ=1,_KK=new T(function(){return B(unCStr(")"));}),_KL=function(_KM,_KN){var _KO=new T(function(){var _KP=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EN(0,_KM,_w)),_KK));})));},1);return B(_n(B(_EN(0,_KN,_w)),_KP));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_KO)));});},_KQ=function(_KR,_KS){var _KT=new T(function(){var _KU=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EN(0,_KS,_w)),_KK));})));},1);return B(_n(B(_EN(0,_KR,_w)),_KU));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_KT)));});},_KV=function(_KW){var _KX=E(_KW);if(!_KX._){return E(_KG);}else{var _KY=new T(function(){return B(_KV(_KX.b));}),_KZ=function(_L0){var _L1=E(_L0);if(!_L1._){return E(_KY);}else{var _L2=_L1.a,_L3=new T(function(){return B(_KZ(_L1.b));}),_L4=new T(function(){return 0.1*E(E(_L2).e)/1.0e-2;}),_L5=new T(function(){var _L6=E(_L2);if(_L6.a!=_L6.b){return E(_KJ);}else{return E(_KI);}}),_L7=function(_L8,_){var _L9=E(_L8),_La=_L9.c,_Lb=_L9.d,_Lc=E(_L9.a),_Ld=E(_L9.b),_Le=E(_L2),_Lf=_Le.a,_Lg=_Le.b,_Lh=E(_Le.c),_Li=_Lh.b,_Lj=E(_Lh.a),_Lk=_Lj.a,_Ll=_Lj.b,_Lm=_Lj.c,_Ln=E(_Le.d),_Lo=_Ln.b,_Lp=E(_Ln.a),_Lq=_Lp.a,_Lr=_Lp.b,_Ls=_Lp.c;if(_Lc>_Lf){return new F(function(){return _KF(_);});}else{if(_Lf>_Ld){return new F(function(){return _KF(_);});}else{if(_Lc>_Lg){return new F(function(){return _KB(_);});}else{if(_Lg>_Ld){return new F(function(){return _KB(_);});}else{var _Lt=_Lf-_Lc|0;if(0>_Lt){return new F(function(){return _KL(_La,_Lt);});}else{if(_Lt>=_La){return new F(function(){return _KL(_La,_Lt);});}else{var _Lu=E(_Lb[_Lt]),_Lv=E(_Lu.c),_Lw=_Lv.b,_Lx=E(_Lv.a),_Ly=_Lx.a,_Lz=_Lx.b,_LA=_Lx.c,_LB=E(_Lu.e),_LC=E(_LB.a),_LD=B(_If(_n4,_Lk,_Ll,_Lm,_Li,_Ly,_Lz,_LA,_Lw)),_LE=E(_LD.a),_LF=B(_If(_n4,_LE.a,_LE.b,_LE.c,_LD.b,_Lk,_Ll,_Lm,_Li)),_LG=E(_LF.a),_LH=_Lg-_Lc|0;if(0>_LH){return new F(function(){return _KQ(_LH,_La);});}else{if(_LH>=_La){return new F(function(){return _KQ(_LH,_La);});}else{var _LI=E(_Lb[_LH]),_LJ=E(_LI.c),_LK=_LJ.b,_LL=E(_LJ.a),_LM=_LL.a,_LN=_LL.b,_LO=_LL.c,_LP=E(_LI.e),_LQ=E(_LP.a),_LR=B(_If(_n4,_Lq,_Lr,_Ls,_Lo,_LM,_LN,_LO,_LK)),_LS=E(_LR.a),_LT=B(_If(_n4,_LS.a,_LS.b,_LS.c,_LR.b,_Lq,_Lr,_Ls,_Lo)),_LU=E(_LT.a),_LV=E(_LG.a)+E(_LG.b)+E(_LG.c)+E(_LF.b)+E(_LU.a)+E(_LU.b)+E(_LU.c)+E(_LT.b);if(!_LV){var _LW=B(A2(_L3,_L9,_));return new T2(0,new T2(1,_ol,new T(function(){return E(E(_LW).a);})),new T(function(){return E(E(_LW).b);}));}else{var _LX=new T(function(){return  -((B(_J7(_nA,_LC.a,_LC.b,_LC.c,_LB.b,_Lk,_Ll,_Lm,_Li))-B(_J7(_nA,_LQ.a,_LQ.b,_LQ.c,_LP.b,_Lq,_Lr,_Ls,_Lo))-E(_L4))/_LV);}),_LY=function(_LZ,_M0,_M1,_M2,_){var _M3=new T(function(){var _M4=function(_M5,_M6,_M7,_M8,_M9){if(_M5>_Lg){return E(_M9);}else{if(_Lg>_M6){return E(_M9);}else{var _Ma=function(_){var _Mb=newArr(_M7,_m4),_Mc=_Mb,_Md=function(_Me,_){while(1){if(_Me!=_M7){var _=_Mc[_Me]=_M8[_Me],_Mf=_Me+1|0;_Me=_Mf;continue;}else{return E(_);}}},_=B(_Md(0,_)),_Mg=_Lg-_M5|0;if(0>_Mg){return new F(function(){return _KQ(_Mg,_M7);});}else{if(_Mg>=_M7){return new F(function(){return _KQ(_Mg,_M7);});}else{var _=_Mc[_Mg]=new T(function(){var _Mh=E(_M8[_Mg]),_Mi=E(_Mh.e),_Mj=E(_Mi.a),_Mk=B(_If(_n4,_LM,_LN,_LO,_LK,_Lq,_Lr,_Ls,_Lo)),_Ml=E(_Mk.a),_Mm=E(_LX)*E(_L5),_Mn=B(_If(_n4,_Ml.a,_Ml.b,_Ml.c,_Mk.b,_Mm,_Mm,_Mm,_Mm)),_Mo=E(_Mn.a),_Mp=B(_Iq(_n4,_Mj.a,_Mj.b,_Mj.c,_Mi.b, -E(_Mo.a), -E(_Mo.b), -E(_Mo.c), -E(_Mn.b)));return {_:0,a:E(_Mh.a),b:E(_Mh.b),c:E(_Mh.c),d:E(_Mh.d),e:E(new T2(0,E(_Mp.a),E(_Mp.b))),f:E(_Mh.f),g:E(_Mh.g),h:_Mh.h,i:_Mh.i};});return new T4(0,E(_M5),E(_M6),_M7,_Mc);}}};return new F(function(){return _Ez(_Ma);});}}};if(_LZ>_Lf){return B(_M4(_LZ,_M0,_M1,_M2,new T4(0,E(_LZ),E(_M0),_M1,_M2)));}else{if(_Lf>_M0){return B(_M4(_LZ,_M0,_M1,_M2,new T4(0,E(_LZ),E(_M0),_M1,_M2)));}else{var _Mq=function(_){var _Mr=newArr(_M1,_m4),_Ms=_Mr,_Mt=function(_Mu,_){while(1){if(_Mu!=_M1){var _=_Ms[_Mu]=_M2[_Mu],_Mv=_Mu+1|0;_Mu=_Mv;continue;}else{return E(_);}}},_=B(_Mt(0,_)),_Mw=_Lf-_LZ|0;if(0>_Mw){return new F(function(){return _KL(_M1,_Mw);});}else{if(_Mw>=_M1){return new F(function(){return _KL(_M1,_Mw);});}else{var _=_Ms[_Mw]=new T(function(){var _Mx=E(_M2[_Mw]),_My=E(_Mx.e),_Mz=E(_My.a),_MA=B(_If(_n4,_Ly,_Lz,_LA,_Lw,_Lk,_Ll,_Lm,_Li)),_MB=E(_MA.a),_MC=E(_LX)*E(_L5),_MD=B(_If(_n4,_MB.a,_MB.b,_MB.c,_MA.b,_MC,_MC,_MC,_MC)),_ME=E(_MD.a),_MF=B(_Iq(_n4,_Mz.a,_Mz.b,_Mz.c,_My.b,_ME.a,_ME.b,_ME.c,_MD.b));return {_:0,a:E(_Mx.a),b:E(_Mx.b),c:E(_Mx.c),d:E(_Mx.d),e:E(new T2(0,E(_MF.a),E(_MF.b))),f:E(_Mx.f),g:E(_Mx.g),h:_Mx.h,i:_Mx.i};});return new T4(0,E(_LZ),E(_M0),_M1,_Ms);}}},_MG=B(_Ez(_Mq));return B(_M4(E(_MG.a),E(_MG.b),_MG.c,_MG.d,_MG));}}});return new T2(0,_ol,_M3);};if(!E(_Le.f)){var _MH=B(_LY(_Lc,_Ld,_La,_Lb,_)),_MI=B(A2(_L3,new T(function(){return E(E(_MH).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MH).a);}),new T(function(){return E(E(_MI).a);})),new T(function(){return E(E(_MI).b);}));}else{if(E(_LX)<0){var _MJ=B(A2(_L3,_L9,_));return new T2(0,new T2(1,_ol,new T(function(){return E(E(_MJ).a);})),new T(function(){return E(E(_MJ).b);}));}else{var _MK=B(_LY(_Lc,_Ld,_La,_Lb,_)),_ML=B(A2(_L3,new T(function(){return E(E(_MK).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MK).a);}),new T(function(){return E(E(_ML).a);})),new T(function(){return E(E(_ML).b);}));}}}}}}}}}}}};return E(_L7);}};return new F(function(){return _KZ(_KX.a);});}},_MM=function(_,_MN){var _MO=new T(function(){return B(_KV(E(_MN).a));}),_MP=function(_MQ){var _MR=E(_MQ);return (_MR==1)?E(new T2(1,_MO,_w)):new T2(1,_MO,new T(function(){return B(_MP(_MR-1|0));}));},_MS=B(_Hr(B(_MP(5)),new T(function(){return E(E(_MN).b);}),_)),_MT=new T(function(){return B(_HZ(_Hq,_Ff,_IY,new T(function(){return E(E(_MS).b);})));});return new T2(0,_ol,_MT);},_MU=function(_MV,_MW,_MX,_MY,_MZ){var _N0=B(_8J(B(_8H(_MV))));return new F(function(){return A3(_6X,_N0,new T(function(){return B(A3(_8L,_N0,_MW,_MY));}),new T(function(){return B(A3(_8L,_N0,_MX,_MZ));}));});},_N1=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_N2=new T6(0,_Kw,_Kx,_w,_N1,_Kw,_Kw),_N3=new T(function(){return B(_Ku(_N2));}),_N4=function(_){return new F(function(){return die(_N3);});},_N5=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_N6=new T6(0,_Kw,_Kx,_w,_N5,_Kw,_Kw),_N7=new T(function(){return B(_Ku(_N6));}),_N8=function(_){return new F(function(){return die(_N7);});},_N9=function(_Na,_Nb,_Nc,_Nd){var _Ne=new T(function(){return B(_8J(new T(function(){return B(_8H(_Na));})));}),_Nf=B(A2(_8s,_Ne,_8q));return new F(function(){return _p9(_Na,_Nf,B(A2(_8s,_Ne,_8r)),_Nf);});},_Ng=false,_Nh=true,_Ni=function(_Nj){var _Nk=E(_Nj),_Nl=_Nk.b,_Nm=E(_Nk.d),_Nn=E(_Nk.e),_No=E(_Nn.a),_Np=E(_Nk.g),_Nq=B(A1(_Nl,_Nm.a)),_Nr=B(_q0(_nA,_Nq.a,_Nq.b,_Nq.c,_Np.a,_Np.b,_Np.c));return {_:0,a:E(_Nk.a),b:E(_Nl),c:E(_Nk.c),d:E(_Nm),e:E(new T2(0,E(new T3(0,E(_No.a)+E(_Nr.a)*1.0e-2,E(_No.b)+E(_Nr.b)*1.0e-2,E(_No.c)+E(_Nr.c)*1.0e-2)),E(_Nn.b))),f:E(_Nk.f),g:E(_Np),h:_Nk.h,i:_Nk.i};},_Ns=new T(function(){return eval("__strict(collideBound)");}),_Nt=new T(function(){return eval("__strict(mouseContact)");}),_Nu=new T(function(){return eval("__strict(collide)");}),_Nv=function(_Nw){var _Nx=E(_Nw);if(!_Nx._){return __Z;}else{return new F(function(){return _n(_Nx.a,new T(function(){return B(_Nv(_Nx.b));},1));});}},_Ny=0,_Nz=new T3(0,E(_Ny),E(_Ny),E(_Ny)),_NA=new T2(0,E(_Nz),E(_Ny)),_NB=function(_NC,_){var _ND=B(_HZ(_Hq,_Ff,_Ni,_NC)),_NE=E(_ND.a),_NF=E(_ND.b);if(_NE<=_NF){var _NG=function(_NH,_NI,_NJ,_NK,_NL,_){if(_NI>_NH){return new F(function(){return _N8(_);});}else{if(_NH>_NJ){return new F(function(){return _N8(_);});}else{var _NM=new T(function(){var _NN=_NH-_NI|0;if(0>_NN){return B(_KQ(_NN,_NK));}else{if(_NN>=_NK){return B(_KQ(_NN,_NK));}else{return E(_NL[_NN]);}}}),_NO=function(_NP,_NQ,_NR,_NS,_NT,_){var _NU=E(_NP);if(!_NU._){return new T2(0,_w,new T4(0,E(_NQ),E(_NR),_NS,_NT));}else{var _NV=E(_NU.a);if(_NQ>_NV){return new F(function(){return _N4(_);});}else{if(_NV>_NR){return new F(function(){return _N4(_);});}else{var _NW=E(_NM),_NX=_NV-_NQ|0;if(0>_NX){return new F(function(){return _KL(_NS,_NX);});}else{if(_NX>=_NS){return new F(function(){return _KL(_NS,_NX);});}else{var _NY=E(_NT[_NX]),_NZ=__app2(E(_Nu),B(_om(new T2(1,new T2(0,_EE,_NW.h),new T2(1,new T2(0,_ED,_NW.i),_w)))),B(_om(new T2(1,new T2(0,_EE,_NY.h),new T2(1,new T2(0,_ED,_NY.i),_w))))),_O0=__arr2lst(0,_NZ),_O1=B(_FS(_O0,_)),_O2=B(_NO(_NU.b,_NQ,_NR,_NS,_NT,_)),_O3=new T(function(){var _O4=new T(function(){return _NH!=_NV;}),_O5=function(_O6){var _O7=E(_O6);if(!_O7._){return __Z;}else{var _O8=_O7.b,_O9=E(_O7.a),_Oa=E(_O9.b),_Ob=E(_O9.a),_Oc=E(_Ob.a),_Od=E(_Ob.b),_Oe=E(_Ob.c),_Of=E(_Oa.a),_Og=E(_Oa.b),_Oh=E(_Oa.c),_Oi=E(_O9.c),_Oj=_Oi.a,_Ok=_Oi.b,_Ol=E(_O9.e),_Om=E(_O9.d),_On=_Om.a,_Oo=_Om.b,_Op=E(_O9.f),_Oq=new T(function(){var _Or=B(_p9(_nA,_Op.a,_Op.b,_Op.c)),_Os=Math.sqrt(B(_MU(_nA,_On,_Oo,_On,_Oo)));return new T3(0,_Os*E(_Or.a),_Os*E(_Or.b),_Os*E(_Or.c));}),_Ot=new T(function(){var _Ou=B(_p9(_nA,_Ol.a,_Ol.b,_Ol.c)),_Ov=Math.sqrt(B(_MU(_nA,_Oj,_Ok,_Oj,_Ok)));return new T3(0,_Ov*E(_Ou.a),_Ov*E(_Ou.b),_Ov*E(_Ou.c));}),_Ow=new T(function(){var _Ox=B(_N9(_nA,_Of,_Og,_Oh));return new T3(0,E(_Ox.a),E(_Ox.b),E(_Ox.c));}),_Oy=new T(function(){var _Oz=B(_N9(_nA,_Oc,_Od,_Oe));return new T3(0,E(_Oz.a),E(_Oz.b),E(_Oz.c));}),_OA=_Of+ -_Oc,_OB=_Og+ -_Od,_OC=_Oh+ -_Oe,_OD=new T(function(){return Math.sqrt(B(_oZ(_nA,_OA,_OB,_OC,_OA,_OB,_OC)));}),_OE=new T(function(){var _OF=1/E(_OD);return new T3(0,_OA*_OF,_OB*_OF,_OC*_OF);}),_OG=new T(function(){if(!E(_O9.g)){return E(_OE);}else{var _OH=E(_OE);return new T3(0,-1*E(_OH.a),-1*E(_OH.b),-1*E(_OH.c));}}),_OI=new T(function(){if(!E(_O9.h)){return E(_OE);}else{var _OJ=E(_OE);return new T3(0,-1*E(_OJ.a),-1*E(_OJ.b),-1*E(_OJ.c));}});return (!E(_O4))?new T2(1,new T(function(){var _OK=E(_OG),_OL=E(_OK.b),_OM=E(_OK.c),_ON=E(_OK.a),_OO=E(_Oy),_OP=E(_OO.c),_OQ=E(_OO.b),_OR=E(_OO.a),_OS=E(_Ot),_OT=E(_OS.c),_OU=E(_OS.b),_OV=E(_OS.a),_OW=_OL*_OP-_OQ*_OM,_OX=_OM*_OR-_OP*_ON,_OY=_ON*_OQ-_OR*_OL,_OZ=B(_oZ(_nA,_OX*_OT-_OU*_OY,_OY*_OV-_OT*_OW,_OW*_OU-_OV*_OX,_OR,_OQ,_OP));return new T6(0,_NH,_NV,E(new T2(0,E(new T3(0,E(_OW),E(_OX),E(_OY))),E(_OZ))),E(_NA),_OD,_Ng);}),new T2(1,new T(function(){var _P0=E(_OI),_P1=E(_P0.b),_P2=E(_P0.c),_P3=E(_P0.a),_P4=E(_Ow),_P5=E(_P4.c),_P6=E(_P4.b),_P7=E(_P4.a),_P8=E(_Oq),_P9=E(_P8.c),_Pa=E(_P8.b),_Pb=E(_P8.a),_Pc=_P1*_P5-_P6*_P2,_Pd=_P2*_P7-_P5*_P3,_Pe=_P3*_P6-_P7*_P1,_Pf=B(_oZ(_nA,_Pd*_P9-_Pa*_Pe,_Pe*_Pb-_P9*_Pc,_Pc*_Pa-_Pb*_Pd,_P7,_P6,_P5));return new T6(0,_NH,_NV,E(_NA),E(new T2(0,E(new T3(0,E(_Pc),E(_Pd),E(_Pe))),E(_Pf))),_OD,_Ng);}),new T(function(){return B(_O5(_O8));}))):new T2(1,new T(function(){var _Pg=E(_OG),_Ph=E(_Pg.b),_Pi=E(_Pg.c),_Pj=E(_Pg.a),_Pk=E(_Oy),_Pl=_Pk.a,_Pm=_Pk.b,_Pn=_Pk.c,_Po=B(_q0(_nA,_Pj,_Ph,_Pi,_Pl,_Pm,_Pn)),_Pp=E(_Ot),_Pq=E(_Pp.c),_Pr=E(_Pp.b),_Ps=E(_Pp.a),_Pt=B(_oZ(_nA,_Ph*_Pq-_Pr*_Pi,_Pi*_Ps-_Pq*_Pj,_Pj*_Pr-_Ps*_Ph,_Pl,_Pm,_Pn)),_Pu=E(_OI),_Pv=E(_Pu.b),_Pw=E(_Pu.c),_Px=E(_Pu.a),_Py=E(_Ow),_Pz=_Py.a,_PA=_Py.b,_PB=_Py.c,_PC=B(_q0(_nA,_Px,_Pv,_Pw,_Pz,_PA,_PB)),_PD=E(_Oq),_PE=E(_PD.c),_PF=E(_PD.b),_PG=E(_PD.a),_PH=B(_oZ(_nA,_Pv*_PE-_PF*_Pw,_Pw*_PG-_PE*_Px,_Px*_PF-_PG*_Pv,_Pz,_PA,_PB));return new T6(0,_NH,_NV,E(new T2(0,E(new T3(0,E(_Po.a),E(_Po.b),E(_Po.c))),E(_Pt))),E(new T2(0,E(new T3(0,E(_PC.a),E(_PC.b),E(_PC.c))),E(_PH))),_OD,_Nh);}),new T(function(){return B(_O5(_O8));}));}};return B(_O5(_O1));});return new T2(0,new T2(1,_O3,new T(function(){return E(E(_O2).a);})),new T(function(){return E(E(_O2).b);}));}}}}}},_PI=B(_NO(B(_wv(_NH,_NF)),_NI,_NJ,_NK,_NL,_)),_PJ=E(_NM),_PK=E(_PJ.d).a,_PL=__app1(E(_Ns),B(_om(new T2(1,new T2(0,_EE,_PJ.h),new T2(1,new T2(0,_ED,_PJ.i),_w))))),_PM=__arr2lst(0,_PL),_PN=B(_FS(_PM,_)),_PO=__app1(E(_Nt),_NH),_PP=__arr2lst(0,_PO),_PQ=B(_FS(_PP,_));if(_NH!=_NF){var _PR=E(_PI),_PS=E(_PR.b),_PT=B(_NG(_NH+1|0,E(_PS.a),E(_PS.b),_PS.c,_PS.d,_)),_PU=new T(function(){var _PV=new T(function(){var _PW=E(_PK),_PX=B(_N9(_nA,_PW.a,_PW.b,_PW.c));return new T3(0,E(_PX.a),E(_PX.b),E(_PX.c));}),_PY=new T(function(){var _PZ=new T(function(){return B(_Nv(_PR.a));}),_Q0=function(_Q1){var _Q2=E(_Q1);if(!_Q2._){return E(_PZ);}else{var _Q3=E(_Q2.a),_Q4=E(_Q3.b),_Q5=E(_Q3.a),_Q6=E(_Q5.a),_Q7=E(_Q5.b),_Q8=E(_Q5.c),_Q9=E(_Q3.c),_Qa=_Q9.a,_Qb=_Q9.b,_Qc=E(_Q3.e);return new T2(1,new T(function(){var _Qd=E(_Q4.a)+ -_Q6,_Qe=E(_Q4.b)+ -_Q7,_Qf=E(_Q4.c)+ -_Q8,_Qg=B(_N9(_nA,_Q6,_Q7,_Q8)),_Qh=_Qg.a,_Qi=_Qg.b,_Qj=_Qg.c,_Qk=Math.sqrt(B(_oZ(_nA,_Qd,_Qe,_Qf,_Qd,_Qe,_Qf))),_Ql=1/_Qk,_Qm=_Qd*_Ql,_Qn=_Qe*_Ql,_Qo=_Qf*_Ql,_Qp=B(_q0(_nA,_Qm,_Qn,_Qo,_Qh,_Qi,_Qj)),_Qq=B(_p9(_nA,_Qc.a,_Qc.b,_Qc.c)),_Qr=Math.sqrt(B(_MU(_nA,_Qa,_Qb,_Qa,_Qb))),_Qs=_Qr*E(_Qq.a),_Qt=_Qr*E(_Qq.b),_Qu=_Qr*E(_Qq.c),_Qv=B(_oZ(_nA,_Qn*_Qu-_Qt*_Qo,_Qo*_Qs-_Qu*_Qm,_Qm*_Qt-_Qs*_Qn,_Qh,_Qi,_Qj));return new T6(0,_NH,_NH,E(new T2(0,E(new T3(0,E(_Qp.a),E(_Qp.b),E(_Qp.c))),E(_Qv))),E(_NA),_Qk,_Nh);}),new T(function(){return B(_Q0(_Q2.b));}));}};return B(_Q0(_PN));}),_Qw=function(_Qx){var _Qy=E(_Qx);if(!_Qy._){return E(_PY);}else{var _Qz=E(_Qy.a),_QA=E(_Qz.b),_QB=new T(function(){var _QC=E(_PK),_QD=E(_QA.c)+ -E(_QC.c),_QE=E(_QA.b)+ -E(_QC.b),_QF=E(_QA.a)+ -E(_QC.a),_QG=Math.sqrt(B(_oZ(_nA,_QF,_QE,_QD,_QF,_QE,_QD))),_QH=function(_QI,_QJ,_QK){var _QL=E(_PV),_QM=_QL.a,_QN=_QL.b,_QO=_QL.c,_QP=B(_q0(_nA,_QI,_QJ,_QK,_QM,_QN,_QO)),_QQ=B(_oZ(_nA,_QJ*0-0*_QK,_QK*0-0*_QI,_QI*0-0*_QJ,_QM,_QN,_QO));return new T6(0,_NH,_NH,new T2(0,E(new T3(0,E(_QP.a),E(_QP.b),E(_QP.c))),E(_QQ)),_NA,_QG,_Nh);};if(!E(_Qz.g)){var _QR=1/_QG,_QS=B(_QH(_QF*_QR,_QE*_QR,_QD*_QR));return new T6(0,_QS.a,_QS.b,E(_QS.c),E(_QS.d),_QS.e,_QS.f);}else{var _QT=1/_QG,_QU=B(_QH(-1*_QF*_QT,-1*_QE*_QT,-1*_QD*_QT));return new T6(0,_QU.a,_QU.b,E(_QU.c),E(_QU.d),_QU.e,_QU.f);}});return new T2(1,_QB,new T(function(){return B(_Qw(_Qy.b));}));}};return B(_Qw(_PQ));});return new T2(0,new T2(1,_PU,new T(function(){return E(E(_PT).a);})),new T(function(){return E(E(_PT).b);}));}else{var _QV=new T(function(){var _QW=new T(function(){var _QX=E(_PK),_QY=B(_N9(_nA,_QX.a,_QX.b,_QX.c));return new T3(0,E(_QY.a),E(_QY.b),E(_QY.c));}),_QZ=new T(function(){var _R0=new T(function(){return B(_Nv(E(_PI).a));}),_R1=function(_R2){var _R3=E(_R2);if(!_R3._){return E(_R0);}else{var _R4=E(_R3.a),_R5=E(_R4.b),_R6=E(_R4.a),_R7=E(_R6.a),_R8=E(_R6.b),_R9=E(_R6.c),_Ra=E(_R4.c),_Rb=_Ra.a,_Rc=_Ra.b,_Rd=E(_R4.e);return new T2(1,new T(function(){var _Re=E(_R5.a)+ -_R7,_Rf=E(_R5.b)+ -_R8,_Rg=E(_R5.c)+ -_R9,_Rh=B(_N9(_nA,_R7,_R8,_R9)),_Ri=_Rh.a,_Rj=_Rh.b,_Rk=_Rh.c,_Rl=Math.sqrt(B(_oZ(_nA,_Re,_Rf,_Rg,_Re,_Rf,_Rg))),_Rm=1/_Rl,_Rn=_Re*_Rm,_Ro=_Rf*_Rm,_Rp=_Rg*_Rm,_Rq=B(_q0(_nA,_Rn,_Ro,_Rp,_Ri,_Rj,_Rk)),_Rr=B(_p9(_nA,_Rd.a,_Rd.b,_Rd.c)),_Rs=Math.sqrt(B(_MU(_nA,_Rb,_Rc,_Rb,_Rc))),_Rt=_Rs*E(_Rr.a),_Ru=_Rs*E(_Rr.b),_Rv=_Rs*E(_Rr.c),_Rw=B(_oZ(_nA,_Ro*_Rv-_Ru*_Rp,_Rp*_Rt-_Rv*_Rn,_Rn*_Ru-_Rt*_Ro,_Ri,_Rj,_Rk));return new T6(0,_NH,_NH,E(new T2(0,E(new T3(0,E(_Rq.a),E(_Rq.b),E(_Rq.c))),E(_Rw))),E(_NA),_Rl,_Nh);}),new T(function(){return B(_R1(_R3.b));}));}};return B(_R1(_PN));}),_Rx=function(_Ry){var _Rz=E(_Ry);if(!_Rz._){return E(_QZ);}else{var _RA=E(_Rz.a),_RB=E(_RA.b),_RC=new T(function(){var _RD=E(_PK),_RE=E(_RB.c)+ -E(_RD.c),_RF=E(_RB.b)+ -E(_RD.b),_RG=E(_RB.a)+ -E(_RD.a),_RH=Math.sqrt(B(_oZ(_nA,_RG,_RF,_RE,_RG,_RF,_RE))),_RI=function(_RJ,_RK,_RL){var _RM=E(_QW),_RN=_RM.a,_RO=_RM.b,_RP=_RM.c,_RQ=B(_q0(_nA,_RJ,_RK,_RL,_RN,_RO,_RP)),_RR=B(_oZ(_nA,_RK*0-0*_RL,_RL*0-0*_RJ,_RJ*0-0*_RK,_RN,_RO,_RP));return new T6(0,_NH,_NH,new T2(0,E(new T3(0,E(_RQ.a),E(_RQ.b),E(_RQ.c))),E(_RR)),_NA,_RH,_Nh);};if(!E(_RA.g)){var _RS=1/_RH,_RT=B(_RI(_RG*_RS,_RF*_RS,_RE*_RS));return new T6(0,_RT.a,_RT.b,E(_RT.c),E(_RT.d),_RT.e,_RT.f);}else{var _RU=1/_RH,_RV=B(_RI(-1*_RG*_RU,-1*_RF*_RU,-1*_RE*_RU));return new T6(0,_RV.a,_RV.b,E(_RV.c),E(_RV.d),_RV.e,_RV.f);}});return new T2(1,_RC,new T(function(){return B(_Rx(_Rz.b));}));}};return B(_Rx(_PQ));});return new T2(0,new T2(1,_QV,_w),new T(function(){return E(E(_PI).b);}));}}}},_RW=B(_NG(_NE,_NE,_NF,_ND.c,_ND.d,_));return new F(function(){return _MM(_,_RW);});}else{return new F(function(){return _MM(_,new T2(0,_w,_ND));});}},_RX=new T(function(){return eval("__strict(passObject)");}),_RY=new T(function(){return eval("__strict(refresh)");}),_RZ=function(_S0,_){var _S1=__app0(E(_RY)),_S2=__app0(E(_EI)),_S3=E(_S0),_S4=_S3.c,_S5=_S3.d,_S6=E(_S3.a),_S7=E(_S3.b);if(_S6<=_S7){if(_S6>_S7){return E(_EG);}else{if(0>=_S4){return new F(function(){return _ET(_S4,0);});}else{var _S8=E(_S5[0]),_S9=E(_RX),_Sa=__app2(_S9,_S6,B(_om(new T2(1,new T2(0,_EE,_S8.h),new T2(1,new T2(0,_ED,_S8.i),_w)))));if(_S6!=_S7){var _Sb=function(_Sc,_){if(_S6>_Sc){return E(_EG);}else{if(_Sc>_S7){return E(_EG);}else{var _Sd=_Sc-_S6|0;if(0>_Sd){return new F(function(){return _ET(_S4,_Sd);});}else{if(_Sd>=_S4){return new F(function(){return _ET(_S4,_Sd);});}else{var _Se=E(_S5[_Sd]),_Sf=__app2(_S9,_Sc,B(_om(new T2(1,new T2(0,_EE,_Se.h),new T2(1,new T2(0,_ED,_Se.i),_w)))));if(_Sc!=_S7){var _Sg=B(_Sb(_Sc+1|0,_));return new T2(1,_ol,_Sg);}else{return _EY;}}}}}},_Sh=B(_Sb(_S6+1|0,_)),_Si=__app0(E(_EH)),_Sj=B(_NB(_S3,_));return new T(function(){return E(E(_Sj).b);});}else{var _Sk=__app0(E(_EH)),_Sl=B(_NB(_S3,_));return new T(function(){return E(E(_Sl).b);});}}}}else{var _Sm=__app0(E(_EH)),_Sn=B(_NB(_S3,_));return new T(function(){return E(E(_Sn).b);});}},_So=function(_Sp,_){while(1){var _Sq=E(_Sp);if(!_Sq._){return _ol;}else{var _Sr=_Sq.b,_Ss=E(_Sq.a);switch(_Ss._){case 0:var _St=B(A1(_Ss.a,_));_Sp=B(_n(_Sr,new T2(1,_St,_w)));continue;case 1:_Sp=B(_n(_Sr,_Ss.a));continue;default:_Sp=_Sr;continue;}}}},_Su=function(_Sv,_Sw,_){var _Sx=E(_Sv);switch(_Sx._){case 0:var _Sy=B(A1(_Sx.a,_));return new F(function(){return _So(B(_n(_Sw,new T2(1,_Sy,_w))),_);});break;case 1:return new F(function(){return _So(B(_n(_Sw,_Sx.a)),_);});break;default:return new F(function(){return _So(_Sw,_);});}},_Sz=new T0(2),_SA=function(_SB){return new T0(2);},_SC=function(_SD,_SE,_SF){return function(_){var _SG=E(_SD),_SH=rMV(_SG),_SI=E(_SH);if(!_SI._){var _SJ=new T(function(){var _SK=new T(function(){return B(A1(_SF,_ol));});return B(_n(_SI.b,new T2(1,new T2(0,_SE,function(_SL){return E(_SK);}),_w)));}),_=wMV(_SG,new T2(0,_SI.a,_SJ));return _Sz;}else{var _SM=E(_SI.a);if(!_SM._){var _=wMV(_SG,new T2(0,_SE,_w));return new T(function(){return B(A1(_SF,_ol));});}else{var _=wMV(_SG,new T1(1,_SM.b));return new T1(1,new T2(1,new T(function(){return B(A1(_SF,_ol));}),new T2(1,new T(function(){return B(A2(_SM.a,_SE,_SA));}),_w)));}}};},_SN=new T(function(){return E(_u1);}),_SO=new T(function(){return eval("window.requestAnimationFrame");}),_SP=new T1(1,_w),_SQ=function(_SR,_SS){return function(_){var _ST=E(_SR),_SU=rMV(_ST),_SV=E(_SU);if(!_SV._){var _SW=_SV.a,_SX=E(_SV.b);if(!_SX._){var _=wMV(_ST,_SP);return new T(function(){return B(A1(_SS,_SW));});}else{var _SY=E(_SX.a),_=wMV(_ST,new T2(0,_SY.a,_SX.b));return new T1(1,new T2(1,new T(function(){return B(A1(_SS,_SW));}),new T2(1,new T(function(){return B(A1(_SY.b,_SA));}),_w)));}}else{var _SZ=new T(function(){var _T0=function(_T1){var _T2=new T(function(){return B(A1(_SS,_T1));});return function(_T3){return E(_T2);};};return B(_n(_SV.a,new T2(1,_T0,_w)));}),_=wMV(_ST,new T1(1,_SZ));return _Sz;}};},_T4=function(_T5,_T6){return new T1(0,B(_SQ(_T5,_T6)));},_T7=function(_T8,_T9){var _Ta=new T(function(){return new T1(0,B(_SC(_T8,_ol,_SA)));});return function(_){var _Tb=__createJSFunc(2,function(_Tc,_){var _Td=B(_Su(_Ta,_w,_));return _SN;}),_Te=__app1(E(_SO),_Tb);return new T(function(){return B(_T4(_T8,_T9));});};},_Tf=new T1(1,_w),_Tg=function(_Th,_Ti,_){var _Tj=function(_){var _Tk=nMV(_Th),_Tl=_Tk;return new T(function(){var _Tm=new T(function(){return B(_Tn(_));}),_To=function(_){var _Tp=rMV(_Tl),_Tq=B(A2(_Ti,_Tp,_)),_=wMV(_Tl,_Tq),_Tr=function(_){var _Ts=nMV(_Tf);return new T(function(){return new T1(0,B(_T7(_Ts,function(_Tt){return E(_Tm);})));});};return new T1(0,_Tr);},_Tu=new T(function(){return new T1(0,_To);}),_Tn=function(_Tv){return E(_Tu);};return B(_Tn(_));});};return new F(function(){return _Su(new T1(0,_Tj),_w,_);});},_Tw=new T(function(){return eval("__strict(setBounds)");}),_Tx=function(_){var _Ty=__app3(E(_lt),E(_lu),E(_lX),E(_ls)),_Tz=__app2(E(_Tw),E(_iI),E(_iF));return new F(function(){return _Tg(_EC,_RZ,_);});},_TA=function(_){return new F(function(){return _Tx(_);});};
var hasteMain = function() {B(A(_TA, [0]));};window.onload = hasteMain;