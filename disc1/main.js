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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return E(E(_hP).a);}),_hR=new T(function(){return B(_8J(new T(function(){return B(_8H(_hQ));})));}),_hS=new T(function(){return B(A2(_8s,_hR,_8r));}),_hT=function(_hU){var _hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=new T(function(){return E(E(_hU).c);});return B(A3(_8L,_hR,_hY,_hY));}),_hZ=new T(function(){var _i0=new T(function(){return E(E(_hU).a);});return B(A3(_8L,_hR,_i0,_i0));});return B(A3(_6X,_hR,_hZ,_hX));});return B(A2(_9t,_hQ,_hW));});return new F(function(){return A3(_9p,_hR,_hV,_hS);});};return E(_hT);},_i1=function(_ef,_ee){return new T2(0,_ef,_ee);},_i2=function(_i3,_i4,_i5){var _i6=new T(function(){var _i7=E(_i3),_i8=_i7.a,_i9=new T(function(){return B(A1(_i7.b,new T(function(){return B(_8J(B(_8H(E(_i7.c).a))));})));});return B(A3(_8R,_i8,new T(function(){return B(A3(_8T,B(_8F(_i8)),_i1,_i5));}),_i9));});return E(B(A1(_i4,_i6)).b);},_ia=function(_ib){var _ic=new T(function(){return E(E(_ib).a);}),_id=new T(function(){return E(E(_ib).b);}),_ie=new T(function(){var _if=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),_ig=new T(function(){var _ih=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_eb(_ih,new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_hO(new T2(0,_ig,_if)));});return function(_ii){return new F(function(){return _i2(new T3(0,_8p,_8u,new T2(0,_ic,_id)),_ie,_ii);});};},_ij=new T(function(){return B(_ia(_7V));}),_ik=new T(function(){return B(A1(_ij,_E));}),_il=new T(function(){return E(E(_ik).a);}),_im=new T(function(){return B(unCStr(",y:"));}),_in=new T1(0,_im),_io=new T(function(){return E(E(_ik).b);}),_ip=new T(function(){return B(unCStr(",z:"));}),_iq=new T1(0,_ip),_ir=new T(function(){return E(E(_ik).c);}),_is=new T(function(){return B(unCStr("})"));}),_it=new T1(0,_is),_iu=new T2(1,_it,_w),_iv=new T2(1,_ir,_iu),_iw=new T2(1,_iq,_iv),_ix=new T2(1,_io,_iw),_iy=new T2(1,_in,_ix),_iz=new T2(1,_il,_iy),_iA=new T(function(){return B(unCStr("({x:"));}),_iB=new T1(0,_iA),_iC=new T2(1,_iB,_iz),_iD=function(_iE){return E(_iE);},_iF=new T(function(){return toJSStr(B(_e(_x,_iD,_iC)));}),_iG=new T(function(){return B(_hO(_7V));}),_iH=new T(function(){return B(A1(_iG,_E));}),_iI=new T(function(){return toJSStr(B(_4(_x,_iD,_iH)));}),_iJ=function(_iK,_iL,_iM){var _iN=E(_iM);if(!_iN._){return new F(function(){return A1(_iL,_iN.a);});}else{var _iO=new T(function(){return B(_0(_iK));}),_iP=new T(function(){return B(_2(_iK));}),_iQ=function(_iR){var _iS=E(_iR);if(!_iS._){return E(_iP);}else{return new F(function(){return A2(_iO,new T(function(){return B(_iJ(_iK,_iL,_iS.a));}),new T(function(){return B(_iQ(_iS.b));}));});}};return new F(function(){return _iQ(_iN.a);});}},_iT=new T(function(){return B(unCStr("x"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("y"));}),_iW=new T1(0,_iV),_iX=new T(function(){return B(unCStr("z"));}),_iY=new T1(0,_iX),_iZ=new T3(0,E(_iU),E(_iW),E(_iY)),_j0=new T(function(){return B(unCStr(","));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr("pow("));}),_j3=new T1(0,_j2),_j4=new T(function(){return B(unCStr(")"));}),_j5=new T1(0,_j4),_j6=new T2(1,_j5,_w),_j7=function(_j8,_j9){return new T1(1,new T2(1,_j3,new T2(1,_j8,new T2(1,_j1,new T2(1,_j9,_j6)))));},_ja=new T(function(){return B(unCStr("acos("));}),_jb=new T1(0,_ja),_jc=function(_jd){return new T1(1,new T2(1,_jb,new T2(1,_jd,_j6)));},_je=new T(function(){return B(unCStr("acosh("));}),_jf=new T1(0,_je),_jg=function(_jh){return new T1(1,new T2(1,_jf,new T2(1,_jh,_j6)));},_ji=new T(function(){return B(unCStr("asin("));}),_jj=new T1(0,_ji),_jk=function(_jl){return new T1(1,new T2(1,_jj,new T2(1,_jl,_j6)));},_jm=new T(function(){return B(unCStr("asinh("));}),_jn=new T1(0,_jm),_jo=function(_jp){return new T1(1,new T2(1,_jn,new T2(1,_jp,_j6)));},_jq=new T(function(){return B(unCStr("atan("));}),_jr=new T1(0,_jq),_js=function(_jt){return new T1(1,new T2(1,_jr,new T2(1,_jt,_j6)));},_ju=new T(function(){return B(unCStr("atanh("));}),_jv=new T1(0,_ju),_jw=function(_jx){return new T1(1,new T2(1,_jv,new T2(1,_jx,_j6)));},_jy=new T(function(){return B(unCStr("cos("));}),_jz=new T1(0,_jy),_jA=function(_jB){return new T1(1,new T2(1,_jz,new T2(1,_jB,_j6)));},_jC=new T(function(){return B(unCStr("cosh("));}),_jD=new T1(0,_jC),_jE=function(_jF){return new T1(1,new T2(1,_jD,new T2(1,_jF,_j6)));},_jG=new T(function(){return B(unCStr("exp("));}),_jH=new T1(0,_jG),_jI=function(_jJ){return new T1(1,new T2(1,_jH,new T2(1,_jJ,_j6)));},_jK=new T(function(){return B(unCStr("log("));}),_jL=new T1(0,_jK),_jM=function(_jN){return new T1(1,new T2(1,_jL,new T2(1,_jN,_j6)));},_jO=new T(function(){return B(unCStr(")/log("));}),_jP=new T1(0,_jO),_jQ=function(_jR,_jS){return new T1(1,new T2(1,_jL,new T2(1,_jS,new T2(1,_jP,new T2(1,_jR,_j6)))));},_jT=new T(function(){return B(unCStr("pi"));}),_jU=new T1(0,_jT),_jV=new T(function(){return B(unCStr("sin("));}),_jW=new T1(0,_jV),_jX=function(_jY){return new T1(1,new T2(1,_jW,new T2(1,_jY,_j6)));},_jZ=new T(function(){return B(unCStr("sinh("));}),_k0=new T1(0,_jZ),_k1=function(_k2){return new T1(1,new T2(1,_k0,new T2(1,_k2,_j6)));},_k3=new T(function(){return B(unCStr("sqrt("));}),_k4=new T1(0,_k3),_k5=function(_k6){return new T1(1,new T2(1,_k4,new T2(1,_k6,_j6)));},_k7=new T(function(){return B(unCStr("tan("));}),_k8=new T1(0,_k7),_k9=function(_ka){return new T1(1,new T2(1,_k8,new T2(1,_ka,_j6)));},_kb=new T(function(){return B(unCStr("tanh("));}),_kc=new T1(0,_kb),_kd=function(_ke){return new T1(1,new T2(1,_kc,new T2(1,_ke,_j6)));},_kf=new T(function(){return B(unCStr("("));}),_kg=new T1(0,_kf),_kh=new T(function(){return B(unCStr(")/("));}),_ki=new T1(0,_kh),_kj=function(_kk,_kl){return new T1(1,new T2(1,_kg,new T2(1,_kk,new T2(1,_ki,new T2(1,_kl,_j6)))));},_km=function(_kn){return new T1(0,new T(function(){var _ko=E(_kn),_kp=jsShow(B(_6y(_ko.a,_ko.b)));return fromJSStr(_kp);}));},_kq=new T(function(){return B(unCStr("1./("));}),_kr=new T1(0,_kq),_ks=function(_kt){return new T1(1,new T2(1,_kr,new T2(1,_kt,_j6)));},_ku=new T(function(){return B(unCStr(")+("));}),_kv=new T1(0,_ku),_kw=function(_kx,_ky){return new T1(1,new T2(1,_kg,new T2(1,_kx,new T2(1,_kv,new T2(1,_ky,_j6)))));},_kz=new T(function(){return B(unCStr("-("));}),_kA=new T1(0,_kz),_kB=function(_kC){return new T1(1,new T2(1,_kA,new T2(1,_kC,_j6)));},_kD=new T(function(){return B(unCStr(")*("));}),_kE=new T1(0,_kD),_kF=function(_kG,_kH){return new T1(1,new T2(1,_kg,new T2(1,_kG,new T2(1,_kE,new T2(1,_kH,_j6)))));},_kI=function(_kJ,_kK){return new F(function(){return A3(_6X,_kL,_kJ,new T(function(){return B(A2(_6Z,_kL,_kK));}));});},_kM=new T(function(){return B(unCStr("abs("));}),_kN=new T1(0,_kM),_kO=function(_kP){return new T1(1,new T2(1,_kN,new T2(1,_kP,_j6)));},_kQ=new T(function(){return B(unCStr("."));}),_kR=function(_kS){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kS,_w)),_kQ));}));},_kT=new T(function(){return B(unCStr("sign("));}),_kU=new T1(0,_kT),_kV=function(_kW){return new T1(1,new T2(1,_kU,new T2(1,_kW,_j6)));},_kL=new T(function(){return {_:0,a:_kw,b:_kI,c:_kF,d:_kB,e:_kO,f:_kV,g:_kR};}),_kX=new T4(0,_kL,_kj,_ks,_km),_kY={_:0,a:_kX,b:_jU,c:_jI,d:_jM,e:_k5,f:_j7,g:_jQ,h:_jX,i:_jA,j:_k9,k:_jk,l:_jc,m:_js,n:_k1,o:_jE,p:_kd,q:_jo,r:_jg,s:_jw},_kZ=new T(function(){return B(unCStr("(/=) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T(function(){return B(unCStr("(==) is not defined"));}),_l2=new T(function(){return B(err(_l1));}),_l3=new T2(0,_l2,_l0),_l4=new T(function(){return B(unCStr("(<) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(<=) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("(>=) is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("compare is not defined"));}),_ld=new T(function(){return B(err(_lc));}),_le=new T(function(){return B(unCStr("max("));}),_lf=new T1(0,_le),_lg=function(_lh,_li){return new T1(1,new T2(1,_lf,new T2(1,_lh,new T2(1,_j1,new T2(1,_li,_j6)))));},_lj=new T(function(){return B(unCStr("min("));}),_lk=new T1(0,_lj),_ll=function(_lm,_ln){return new T1(1,new T2(1,_lk,new T2(1,_lm,new T2(1,_j1,new T2(1,_ln,_j6)))));},_lo={_:0,a:_l3,b:_ld,c:_l5,d:_l7,e:_l9,f:_lb,g:_lg,h:_ll},_lp=new T2(0,_kY,_lo),_lq=new T(function(){return B(_hO(_lp));}),_lr=new T(function(){return B(A1(_lq,_iZ));}),_ls=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lr)));}),_lt=new T(function(){return eval("__strict(compile)");}),_lu=new T(function(){return toJSStr(E(_iV));}),_lv=function(_lw,_lx,_ly){var _lz=new T(function(){return B(_0(_lw));}),_lA=new T(function(){return B(_2(_lw));}),_lB=function(_lC){var _lD=E(_lC);if(!_lD._){return E(_lA);}else{return new F(function(){return A2(_lz,new T(function(){return B(_iJ(_lw,_lx,_lD.a));}),new T(function(){return B(_lB(_lD.b));}));});}};return new F(function(){return _lB(_ly);});},_lE=new T(function(){return B(unCStr("vec3("));}),_lF=new T1(0,_lE),_lG=new T(function(){return B(_7i(0,_8r,_w));}),_lH=new T(function(){return B(_n(_lG,_kQ));}),_lI=new T1(0,_lH),_lJ=new T(function(){return B(_7i(0,_8q,_w));}),_lK=new T(function(){return B(_n(_lJ,_kQ));}),_lL=new T1(0,_lK),_lM=new T2(1,_lL,_w),_lN=new T2(1,_lI,_lM),_lO=function(_lP,_lQ){var _lR=E(_lQ);return (_lR._==0)?__Z:new T2(1,_lP,new T2(1,_lR.a,new T(function(){return B(_lO(_lP,_lR.b));})));},_lS=new T(function(){return B(_lO(_j1,_lN));}),_lT=new T2(1,_lL,_lS),_lU=new T1(1,_lT),_lV=new T2(1,_lU,_j6),_lW=new T2(1,_lF,_lV),_lX=new T(function(){return toJSStr(B(_lv(_x,_iD,_lW)));}),_lY="enclose",_lZ="outline",_m0="polygon",_m1="z",_m2="y",_m3="x",_m4=0,_m5=function(_m6){var _m7=__new(),_m8=_m7,_m9=function(_ma,_){while(1){var _mb=E(_ma);if(!_mb._){return _m4;}else{var _mc=E(_mb.a),_md=__set(_m8,E(_mc.a),E(_mc.b));_ma=_mb.b;continue;}}},_me=B(_m9(_m6,_));return E(_m8);},_mf=function(_mg){return new F(function(){return _m5(new T2(1,new T2(0,_m3,new T(function(){return E(E(E(E(_mg).d).a).a);})),new T2(1,new T2(0,_m2,new T(function(){return E(E(E(E(_mg).d).a).b);})),new T2(1,new T2(0,_m1,new T(function(){return E(E(E(E(_mg).d).a).c);})),new T2(1,new T2(0,_m0,new T(function(){return E(_mg).h;})),new T2(1,new T2(0,_lZ,new T(function(){return E(_mg).i;})),new T2(1,new T2(0,_lY,new T(function(){return E(_mg).j;})),_w)))))));});},_mh=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_mi=new T(function(){return B(err(_mh));}),_mj=new T(function(){return eval("__strict(drawObjects)");}),_mk=new T(function(){return eval("__strict(draw)");}),_ml=function(_mm,_mn){var _mo=jsShowI(_mm);return new F(function(){return _n(fromJSStr(_mo),_mn);});},_mp=function(_mq,_mr,_ms){if(_mr>=0){return new F(function(){return _ml(_mr,_ms);});}else{if(_mq<=6){return new F(function(){return _ml(_mr,_ms);});}else{return new T2(1,_7g,new T(function(){var _mt=jsShowI(_mr);return B(_n(fromJSStr(_mt),new T2(1,_7f,_ms)));}));}}},_mu=new T(function(){return B(unCStr(")"));}),_mv=function(_mw,_mx){var _my=new T(function(){var _mz=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mp(0,_mw,_w)),_mu));})));},1);return B(_n(B(_mp(0,_mx,_w)),_mz));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_my)));});},_mA=new T2(1,_m4,_w),_mB=function(_mC){return E(_mC);},_mD=function(_mE){return E(_mE);},_mF=function(_mG,_mH){return E(_mH);},_mI=function(_mJ,_mK){return E(_mJ);},_mL=function(_mM){return E(_mM);},_mN=new T2(0,_mL,_mI),_mO=function(_mP,_mQ){return E(_mP);},_mR=new T5(0,_mN,_mD,_mB,_mF,_mO),_mS=function(_mT){var _mU=E(_mT);return new F(function(){return Math.log(_mU+(_mU+1)*Math.sqrt((_mU-1)/(_mU+1)));});},_mV=function(_mW){var _mX=E(_mW);return new F(function(){return Math.log(_mX+Math.sqrt(1+_mX*_mX));});},_mY=function(_mZ){var _n0=E(_mZ);return 0.5*Math.log((1+_n0)/(1-_n0));},_n1=function(_n2,_n3){return Math.log(E(_n3))/Math.log(E(_n2));},_n4=3.141592653589793,_n5=function(_n6){var _n7=E(_n6);return new F(function(){return _6y(_n7.a,_n7.b);});},_n8=function(_n9){return 1/E(_n9);},_na=function(_nb){var _nc=E(_nb),_nd=E(_nc);return (_nd==0)?E(_6x):(_nd<=0)? -_nd:E(_nc);},_ne=function(_nf){var _ng=E(_nf);if(!_ng._){return _ng.a;}else{return new F(function(){return I_toNumber(_ng.a);});}},_nh=function(_ni){return new F(function(){return _ne(_ni);});},_nj=1,_nk=-1,_nl=function(_nm){var _nn=E(_nm);return (_nn<=0)?(_nn>=0)?E(_nn):E(_nk):E(_nj);},_no=function(_np,_nq){return E(_np)-E(_nq);},_nr=function(_ns){return  -E(_ns);},_nt=function(_nu,_nv){return E(_nu)+E(_nv);},_nw=function(_nx,_ny){return E(_nx)*E(_ny);},_nz={_:0,a:_nt,b:_no,c:_nw,d:_nr,e:_na,f:_nl,g:_nh},_nA=function(_nB,_nC){return E(_nB)/E(_nC);},_nD=new T4(0,_nz,_nA,_n8,_n5),_nE=function(_nF){return new F(function(){return Math.acos(E(_nF));});},_nG=function(_nH){return new F(function(){return Math.asin(E(_nH));});},_nI=function(_nJ){return new F(function(){return Math.atan(E(_nJ));});},_nK=function(_nL){return new F(function(){return Math.cos(E(_nL));});},_nM=function(_nN){return new F(function(){return cosh(E(_nN));});},_nO=function(_nP){return new F(function(){return Math.exp(E(_nP));});},_nQ=function(_nR){return new F(function(){return Math.log(E(_nR));});},_nS=function(_nT,_nU){return new F(function(){return Math.pow(E(_nT),E(_nU));});},_nV=function(_nW){return new F(function(){return Math.sin(E(_nW));});},_nX=function(_nY){return new F(function(){return sinh(E(_nY));});},_nZ=function(_o0){return new F(function(){return Math.sqrt(E(_o0));});},_o1=function(_o2){return new F(function(){return Math.tan(E(_o2));});},_o3=function(_o4){return new F(function(){return tanh(E(_o4));});},_o5={_:0,a:_nD,b:_n4,c:_nO,d:_nQ,e:_nZ,f:_nS,g:_n1,h:_nV,i:_nK,j:_o1,k:_nG,l:_nE,m:_nI,n:_nX,o:_nM,p:_o3,q:_mV,r:_mS,s:_mY},_o6="flipped2",_o7="flipped1",_o8="c1y",_o9="c1x",_oa="w2z",_ob="w2y",_oc="w2x",_od="w1z",_oe="w1y",_of="w1x",_og="d2z",_oh="d2y",_oi="d2x",_oj="d1z",_ok="d1y",_ol="d1x",_om="c2y",_on="c2x",_oo=function(_op,_){var _oq=__get(_op,E(_of)),_or=__get(_op,E(_oe)),_os=__get(_op,E(_od)),_ot=__get(_op,E(_oc)),_ou=__get(_op,E(_ob)),_ov=__get(_op,E(_oa)),_ow=__get(_op,E(_o9)),_ox=__get(_op,E(_o8)),_oy=__get(_op,E(_on)),_oz=__get(_op,E(_om)),_oA=__get(_op,E(_ol)),_oB=__get(_op,E(_ok)),_oC=__get(_op,E(_oj)),_oD=__get(_op,E(_oi)),_oE=__get(_op,E(_oh)),_oF=__get(_op,E(_og)),_oG=__get(_op,E(_o7)),_oH=__get(_op,E(_o6));return {_:0,a:E(new T3(0,E(_oq),E(_or),E(_os))),b:E(new T3(0,E(_ot),E(_ou),E(_ov))),c:E(new T2(0,E(_ow),E(_ox))),d:E(new T2(0,E(_oy),E(_oz))),e:E(new T3(0,E(_oA),E(_oB),E(_oC))),f:E(new T3(0,E(_oD),E(_oE),E(_oF))),g:E(_oG),h:E(_oH)};},_oI=function(_oJ,_){var _oK=E(_oJ);if(!_oK._){return _w;}else{var _oL=B(_oo(E(_oK.a),_)),_oM=B(_oI(_oK.b,_));return new T2(1,_oL,_oM);}},_oN=function(_oO){var _oP=E(_oO);return (E(_oP.b)-E(_oP.a)|0)+1|0;},_oQ=function(_oR,_oS){var _oT=E(_oR),_oU=E(_oS);return (E(_oT.a)>_oU)?false:_oU<=E(_oT.b);},_oV=function(_oW){return new F(function(){return _mp(0,E(_oW),_w);});},_oX=function(_oY,_oZ,_p0){return new F(function(){return _mp(E(_oY),E(_oZ),_p0);});},_p1=function(_p2,_p3){return new F(function(){return _mp(0,E(_p2),_p3);});},_p4=function(_p5,_p6){return new F(function(){return _2Q(_p1,_p5,_p6);});},_p7=new T3(0,_oX,_oV,_p4),_p8=0,_p9=function(_pa,_pb,_pc){return new F(function(){return A1(_pa,new T2(1,_2N,new T(function(){return B(A1(_pb,_pc));})));});},_pd=new T(function(){return B(unCStr(": empty list"));}),_pe=new T(function(){return B(unCStr("Prelude."));}),_pf=function(_pg){return new F(function(){return err(B(_n(_pe,new T(function(){return B(_n(_pg,_pd));},1))));});},_ph=new T(function(){return B(unCStr("foldr1"));}),_pi=new T(function(){return B(_pf(_ph));}),_pj=function(_pk,_pl){var _pm=E(_pl);if(!_pm._){return E(_pi);}else{var _pn=_pm.a,_po=E(_pm.b);if(!_po._){return E(_pn);}else{return new F(function(){return A2(_pk,_pn,new T(function(){return B(_pj(_pk,_po));}));});}}},_pp=new T(function(){return B(unCStr(" out of range "));}),_pq=new T(function(){return B(unCStr("}.index: Index "));}),_pr=new T(function(){return B(unCStr("Ix{"));}),_ps=new T2(1,_7f,_w),_pt=new T2(1,_7f,_ps),_pu=0,_pv=function(_pw){return E(E(_pw).a);},_px=function(_py,_pz,_pA,_pB,_pC){var _pD=new T(function(){var _pE=new T(function(){var _pF=new T(function(){var _pG=new T(function(){var _pH=new T(function(){return B(A3(_pj,_p9,new T2(1,new T(function(){return B(A3(_pv,_pA,_pu,_pB));}),new T2(1,new T(function(){return B(A3(_pv,_pA,_pu,_pC));}),_w)),_pt));});return B(_n(_pp,new T2(1,_7g,new T2(1,_7g,_pH))));});return B(A(_pv,[_pA,_p8,_pz,new T2(1,_7f,_pG)]));});return B(_n(_pq,new T2(1,_7g,_pF)));},1);return B(_n(_py,_pE));},1);return new F(function(){return err(B(_n(_pr,_pD)));});},_pI=function(_pJ,_pK,_pL,_pM,_pN){return new F(function(){return _px(_pJ,_pK,_pN,_pL,_pM);});},_pO=function(_pP,_pQ,_pR,_pS){var _pT=E(_pR);return new F(function(){return _pI(_pP,_pQ,_pT.a,_pT.b,_pS);});},_pU=function(_pV,_pW,_pX,_pY){return new F(function(){return _pO(_pY,_pX,_pW,_pV);});},_pZ=new T(function(){return B(unCStr("Int"));}),_q0=function(_q1,_q2){return new F(function(){return _pU(_p7,_q2,_q1,_pZ);});},_q3=function(_q4,_q5){var _q6=E(_q4),_q7=E(_q6.a),_q8=E(_q5);if(_q7>_q8){return new F(function(){return _q0(_q8,_q6);});}else{if(_q8>E(_q6.b)){return new F(function(){return _q0(_q8,_q6);});}else{return _q8-_q7|0;}}},_q9=function(_qa,_qb){if(_qa<=_qb){var _qc=function(_qd){return new T2(1,_qd,new T(function(){if(_qd!=_qb){return B(_qc(_qd+1|0));}else{return __Z;}}));};return new F(function(){return _qc(_qa);});}else{return __Z;}},_qe=function(_qf,_qg){return new F(function(){return _q9(E(_qf),E(_qg));});},_qh=function(_qi){var _qj=E(_qi);return new F(function(){return _qe(_qj.a,_qj.b);});},_qk=function(_ql){var _qm=E(_ql),_qn=E(_qm.a),_qo=E(_qm.b);return (_qn>_qo)?E(_p8):(_qo-_qn|0)+1|0;},_qp=function(_qq,_qr){return E(_qq)-E(_qr)|0;},_qs=function(_qt,_qu){return new F(function(){return _qp(_qu,E(_qt).a);});},_qv=function(_qw,_qx){return E(_qw)==E(_qx);},_qy=function(_qz,_qA){return E(_qz)!=E(_qA);},_qB=new T2(0,_qv,_qy),_qC=function(_qD,_qE){var _qF=E(_qD),_qG=E(_qE);return (_qF>_qG)?E(_qF):E(_qG);},_qH=function(_qI,_qJ){var _qK=E(_qI),_qL=E(_qJ);return (_qK>_qL)?E(_qL):E(_qK);},_qM=function(_qN,_qO){return (_qN>=_qO)?(_qN!=_qO)?2:1:0;},_qP=function(_qQ,_qR){return new F(function(){return _qM(E(_qQ),E(_qR));});},_qS=function(_qT,_qU){return E(_qT)>=E(_qU);},_qV=function(_qW,_qX){return E(_qW)>E(_qX);},_qY=function(_qZ,_r0){return E(_qZ)<=E(_r0);},_r1=function(_r2,_r3){return E(_r2)<E(_r3);},_r4={_:0,a:_qB,b:_qP,c:_r1,d:_qY,e:_qV,f:_qS,g:_qC,h:_qH},_r5={_:0,a:_r4,b:_qh,c:_q3,d:_qs,e:_oQ,f:_qk,g:_oN},_r6=function(_r7,_r8,_){while(1){var _r9=B((function(_ra,_rb,_){var _rc=E(_ra);if(!_rc._){return new T2(0,_m4,_rb);}else{var _rd=B(A2(_rc.a,_rb,_));_r7=_rc.b;_r8=new T(function(){return E(E(_rd).b);});return __continue;}})(_r7,_r8,_));if(_r9!=__continue){return _r9;}}},_re=function(_rf,_rg){return new T2(1,_rf,_rg);},_rh=function(_ri,_rj){var _rk=E(_rj);return new T2(0,_rk.a,_rk.b);},_rl=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_rm=new T(function(){return B(err(_rl));}),_rn=new T(function(){return B(unCStr("Negative range size"));}),_ro=new T(function(){return B(err(_rn));}),_rp=function(_rq){return E(E(_rq).f);},_rr=function(_rs){var _rt=B(A1(_rs,_));return E(_rt);},_ru=function(_rv,_rw,_rx){var _ry=E(_rw),_rz=_ry.a,_rA=_ry.b,_rB=function(_){var _rC=B(A2(_rp,_rv,_ry));if(_rC>=0){var _rD=newArr(_rC,_rm),_rE=_rD,_rF=E(_rC);if(!_rF){return new T(function(){return new T4(0,E(_rz),E(_rA),0,_rE);});}else{var _rG=function(_rH,_rI,_){while(1){var _rJ=E(_rH);if(!_rJ._){return E(_);}else{var _=_rE[_rI]=_rJ.a;if(_rI!=(_rF-1|0)){var _rK=_rI+1|0;_rH=_rJ.b;_rI=_rK;continue;}else{return E(_);}}}},_=B(_rG(_rx,0,_));return new T(function(){return new T4(0,E(_rz),E(_rA),_rF,_rE);});}}else{return E(_ro);}};return new F(function(){return _rr(_rB);});},_rL=function(_rM,_rN,_rO,_rP){var _rQ=new T(function(){var _rR=E(_rP),_rS=_rR.c-1|0,_rT=new T(function(){return B(A2(_cF,_rN,_w));});if(0<=_rS){var _rU=new T(function(){return B(_8F(_rN));}),_rV=function(_rW){var _rX=new T(function(){var _rY=new T(function(){return B(A1(_rO,new T(function(){return E(_rR.d[_rW]);})));});return B(A3(_8T,_rU,_re,_rY));});return new F(function(){return A3(_8R,_rN,_rX,new T(function(){if(_rW!=_rS){return B(_rV(_rW+1|0));}else{return E(_rT);}}));});};return B(_rV(0));}else{return E(_rT);}}),_rZ=new T(function(){return B(_rh(_rM,_rP));});return new F(function(){return A3(_8T,B(_8F(_rN)),function(_s0){return new F(function(){return _ru(_rM,_rZ,_s0);});},_rQ);});},_s1=function(_s2,_s3,_s4,_s5,_s6,_s7,_s8,_s9,_sa){var _sb=B(_8L(_s2));return new T2(0,new T3(0,E(B(A1(B(A1(_sb,_s3)),_s7))),E(B(A1(B(A1(_sb,_s4)),_s8))),E(B(A1(B(A1(_sb,_s5)),_s9)))),B(A1(B(A1(_sb,_s6)),_sa)));},_sc=function(_sd,_se,_sf,_sg,_sh,_si,_sj,_sk,_sl){var _sm=B(_6X(_sd));return new T2(0,new T3(0,E(B(A1(B(A1(_sm,_se)),_si))),E(B(A1(B(A1(_sm,_sf)),_sj))),E(B(A1(B(A1(_sm,_sg)),_sk)))),B(A1(B(A1(_sm,_sh)),_sl)));},_sn=function(_so,_sp){return (E(_so)!=E(_sp))?true:false;},_sq=function(_sr,_ss){return E(_sr)==E(_ss);},_st=new T2(0,_sq,_sn),_su=function(_sv,_sw){return E(_sv)<E(_sw);},_sx=function(_sy,_sz){return E(_sy)<=E(_sz);},_sA=function(_sB,_sC){return E(_sB)>E(_sC);},_sD=function(_sE,_sF){return E(_sE)>=E(_sF);},_sG=function(_sH,_sI){var _sJ=E(_sH),_sK=E(_sI);return (_sJ>=_sK)?(_sJ!=_sK)?2:1:0;},_sL=function(_sM,_sN){var _sO=E(_sM),_sP=E(_sN);return (_sO>_sP)?E(_sO):E(_sP);},_sQ=function(_sR,_sS){var _sT=E(_sR),_sU=E(_sS);return (_sT>_sU)?E(_sU):E(_sT);},_sV={_:0,a:_st,b:_sG,c:_su,d:_sx,e:_sA,f:_sD,g:_sL,h:_sQ},_sW="dz",_sX="wy",_sY="wx",_sZ="dy",_t0="dx",_t1="t",_t2="a",_t3="r",_t4="ly",_t5="lx",_t6="wz",_t7=function(_t8,_t9,_ta,_tb,_tc,_td,_te,_tf,_tg){return new F(function(){return _m5(new T2(1,new T2(0,_sY,_t8),new T2(1,new T2(0,_sX,_t9),new T2(1,new T2(0,_t6,_ta),new T2(1,new T2(0,_t5,_tb*_tc*Math.cos(_td)),new T2(1,new T2(0,_t4,_tb*_tc*Math.sin(_td)),new T2(1,new T2(0,_t3,_tb),new T2(1,new T2(0,_t2,_tc),new T2(1,new T2(0,_t1,_td),new T2(1,new T2(0,_t0,_te),new T2(1,new T2(0,_sZ,_tf),new T2(1,new T2(0,_sW,_tg),_w))))))))))));});},_th=function(_ti){var _tj=E(_ti),_tk=E(_tj.a),_tl=E(_tj.b),_tm=E(_tj.d);return new F(function(){return _t7(_tk.a,_tk.b,_tk.c,E(_tl.a),E(_tl.b),E(_tj.c),_tm.a,_tm.b,_tm.c);});},_tn=function(_to,_tp){var _tq=E(_tp);return (_tq._==0)?__Z:new T2(1,new T(function(){return B(A1(_to,_tq.a));}),new T(function(){return B(_tn(_to,_tq.b));}));},_tr=function(_ts,_tt,_tu){var _tv=__lst2arr(B(_tn(_th,new T2(1,_ts,new T2(1,_tt,new T2(1,_tu,_w))))));return E(_tv);},_tw=function(_tx){var _ty=E(_tx);return new F(function(){return _tr(_ty.a,_ty.b,_ty.c);});},_tz=new T2(0,_o5,_sV),_tA=function(_tB,_tC,_tD,_tE,_tF,_tG,_tH){var _tI=B(_8J(B(_8H(_tB)))),_tJ=new T(function(){return B(A3(_6X,_tI,new T(function(){return B(A3(_8L,_tI,_tC,_tF));}),new T(function(){return B(A3(_8L,_tI,_tD,_tG));})));});return new F(function(){return A3(_6X,_tI,_tJ,new T(function(){return B(A3(_8L,_tI,_tE,_tH));}));});},_tK=function(_tL,_tM,_tN,_tO){var _tP=B(_8H(_tL)),_tQ=new T(function(){return B(A2(_9t,_tL,new T(function(){return B(_tA(_tL,_tM,_tN,_tO,_tM,_tN,_tO));})));});return new T3(0,B(A3(_8P,_tP,_tM,_tQ)),B(A3(_8P,_tP,_tN,_tQ)),B(A3(_8P,_tP,_tO,_tQ)));},_tR=function(_tS,_tT,_tU,_tV,_tW,_tX,_tY){var _tZ=B(_8L(_tS));return new T3(0,B(A1(B(A1(_tZ,_tT)),_tW)),B(A1(B(A1(_tZ,_tU)),_tX)),B(A1(B(A1(_tZ,_tV)),_tY)));},_u0=function(_u1,_u2,_u3,_u4,_u5,_u6,_u7){var _u8=B(_6X(_u1));return new T3(0,B(A1(B(A1(_u8,_u2)),_u5)),B(A1(B(A1(_u8,_u3)),_u6)),B(A1(B(A1(_u8,_u4)),_u7)));},_u9=function(_ua,_ub){var _uc=new T(function(){return E(E(_ua).a);}),_ud=new T(function(){var _ue=E(_ub),_uf=new T(function(){return B(_8J(new T(function(){return B(_8H(_uc));})));}),_ug=B(A2(_8s,_uf,_8q));return new T3(0,E(_ug),E(B(A2(_8s,_uf,_8r))),E(_ug));}),_uh=new T(function(){var _ui=E(_ud),_uj=B(_tK(_uc,_ui.a,_ui.b,_ui.c));return new T3(0,E(_uj.a),E(_uj.b),E(_uj.c));}),_uk=new T(function(){var _ul=E(_ub),_um=_ul.b,_un=E(_uh),_uo=B(_8H(_uc)),_up=new T(function(){return B(A2(_9t,_uc,new T(function(){var _uq=E(_ud),_ur=_uq.a,_us=_uq.b,_ut=_uq.c;return B(_tA(_uc,_ur,_us,_ut,_ur,_us,_ut));})));}),_uu=B(A3(_8P,_uo,_um,_up)),_uv=B(_8J(_uo)),_uw=B(_tR(_uv,_un.a,_un.b,_un.c,_uu,_uu,_uu)),_ux=B(_6Z(_uv)),_uy=B(_u0(_uv,_ul.a,_um,_ul.c,B(A1(_ux,_uw.a)),B(A1(_ux,_uw.b)),B(A1(_ux,_uw.c))));return new T3(0,E(_uy.a),E(_uy.b),E(_uy.c));});return new T2(0,_uk,_uh);},_uz=function(_uA){return E(E(_uA).a);},_uB=function(_uC,_uD,_uE,_uF,_uG,_uH,_uI){var _uJ=B(_tA(_uC,_uG,_uH,_uI,_uD,_uE,_uF)),_uK=B(_8J(B(_8H(_uC)))),_uL=B(_tR(_uK,_uG,_uH,_uI,_uJ,_uJ,_uJ)),_uM=B(_6Z(_uK));return new F(function(){return _u0(_uK,_uD,_uE,_uF,B(A1(_uM,_uL.a)),B(A1(_uM,_uL.b)),B(A1(_uM,_uL.c)));});},_uN=function(_uO){return E(E(_uO).a);},_uP=function(_uQ,_uR,_uS,_uT){var _uU=new T(function(){var _uV=E(_uT),_uW=E(_uS),_uX=B(_uB(_uQ,_uV.a,_uV.b,_uV.c,_uW.a,_uW.b,_uW.c));return new T3(0,E(_uX.a),E(_uX.b),E(_uX.c));}),_uY=new T(function(){return B(A2(_9t,_uQ,new T(function(){var _uZ=E(_uU),_v0=_uZ.a,_v1=_uZ.b,_v2=_uZ.c;return B(_tA(_uQ,_v0,_v1,_v2,_v0,_v1,_v2));})));});if(!B(A3(_uN,B(_uz(_uR)),_uY,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_uQ)))),_8q));})))){var _v3=E(_uU),_v4=B(_tK(_uQ,_v3.a,_v3.b,_v3.c)),_v5=B(A2(_9t,_uQ,new T(function(){var _v6=E(_uT),_v7=_v6.a,_v8=_v6.b,_v9=_v6.c;return B(_tA(_uQ,_v7,_v8,_v9,_v7,_v8,_v9));}))),_va=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_uQ));})));})));return new T3(0,B(A1(B(A1(_va,_v4.a)),_v5)),B(A1(B(A1(_va,_v4.b)),_v5)),B(A1(B(A1(_va,_v4.c)),_v5)));}else{var _vb=B(A2(_8s,B(_8J(B(_8H(_uQ)))),_8q));return new T3(0,_vb,_vb,_vb);}},_vc=0,_vd=new T3(0,E(_vc),E(_vc),E(_vc)),_ve=function(_vf,_vg){while(1){var _vh=E(_vf);if(!_vh._){return E(_vg);}else{var _vi=_vh.b,_vj=E(_vh.a);if(_vg>_vj){_vf=_vi;continue;}else{_vf=_vi;_vg=_vj;continue;}}}},_vk=new T(function(){var _vl=eval("angleCount"),_vm=Number(_vl);return jsTrunc(_vm);}),_vn=new T(function(){return E(_vk);}),_vo=new T(function(){return B(unCStr("head"));}),_vp=new T(function(){return B(_pf(_vo));}),_vq=function(_vr,_vs,_vt){var _vu=E(_vr);if(!_vu._){return __Z;}else{var _vv=E(_vs);if(!_vv._){return __Z;}else{var _vw=_vv.a,_vx=E(_vt);if(!_vx._){return __Z;}else{var _vy=E(_vx.a),_vz=_vy.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_vu.a),E(_vw),E(_vz));}),new T2(1,new T(function(){return new T3(0,E(_vw),E(_vz),E(_vy.b));}),_w)),new T(function(){return B(_vq(_vu.b,_vv.b,_vx.b));},1));});}}}},_vA=new T(function(){return B(unCStr("tail"));}),_vB=new T(function(){return B(_pf(_vA));}),_vC=function(_vD,_vE){var _vF=E(_vD);if(!_vF._){return __Z;}else{var _vG=E(_vE);return (_vG._==0)?__Z:new T2(1,new T2(0,_vF.a,_vG.a),new T(function(){return B(_vC(_vF.b,_vG.b));}));}},_vH=function(_vI,_vJ){var _vK=E(_vI);if(!_vK._){return __Z;}else{var _vL=E(_vJ);if(!_vL._){return __Z;}else{var _vM=E(_vK.a),_vN=_vM.b,_vO=E(_vL.a).b,_vP=new T(function(){var _vQ=new T(function(){return B(_vC(_vO,new T(function(){var _vR=E(_vO);if(!_vR._){return E(_vB);}else{return E(_vR.b);}},1)));},1);return B(_vq(_vN,new T(function(){var _vS=E(_vN);if(!_vS._){return E(_vB);}else{return E(_vS.b);}},1),_vQ));});return new F(function(){return _n(new T2(1,new T(function(){var _vT=E(_vN);if(!_vT._){return E(_vp);}else{var _vU=E(_vO);if(!_vU._){return E(_vp);}else{return new T3(0,E(_vM.a),E(_vT.a),E(_vU.a));}}}),_vP),new T(function(){return B(_vH(_vK.b,_vL.b));},1));});}}},_vV=new T(function(){return 6.283185307179586/E(_vn);}),_vW=new T(function(){return E(_vn)-1;}),_vX=new T1(0,1),_vY=function(_vZ,_w0){var _w1=E(_w0),_w2=new T(function(){var _w3=B(_8J(_vZ)),_w4=B(_vY(_vZ,B(A3(_6X,_w3,_w1,new T(function(){return B(A2(_8s,_w3,_vX));})))));return new T2(1,_w4.a,_w4.b);});return new T2(0,_w1,_w2);},_w5=function(_w6){return E(E(_w6).d);},_w7=new T1(0,2),_w8=function(_w9,_wa){var _wb=E(_wa);if(!_wb._){return __Z;}else{var _wc=_wb.a;return (!B(A1(_w9,_wc)))?__Z:new T2(1,_wc,new T(function(){return B(_w8(_w9,_wb.b));}));}},_wd=function(_we,_wf,_wg,_wh){var _wi=B(_vY(_wf,_wg)),_wj=new T(function(){var _wk=B(_8J(_wf)),_wl=new T(function(){return B(A3(_8P,_wf,new T(function(){return B(A2(_8s,_wk,_vX));}),new T(function(){return B(A2(_8s,_wk,_w7));})));});return B(A3(_6X,_wk,_wh,_wl));});return new F(function(){return _w8(function(_wm){return new F(function(){return A3(_w5,_we,_wm,_wj);});},new T2(1,_wi.a,_wi.b));});},_wn=new T(function(){return B(_wd(_sV,_nD,_vc,_vW));}),_wo=function(_wp,_wq){while(1){var _wr=E(_wp);if(!_wr._){return E(_wq);}else{_wp=_wr.b;_wq=_wr.a;continue;}}},_ws=new T(function(){return B(unCStr("last"));}),_wt=new T(function(){return B(_pf(_ws));}),_wu=function(_wv){return new F(function(){return _wo(_wv,_wt);});},_ww=function(_wx){return new F(function(){return _wu(E(_wx).b);});},_wy=new T(function(){return B(unCStr("maximum"));}),_wz=new T(function(){return B(_pf(_wy));}),_wA=new T(function(){var _wB=eval("proceedCount"),_wC=Number(_wB);return jsTrunc(_wC);}),_wD=new T(function(){return E(_wA);}),_wE=1,_wF=new T(function(){return B(_wd(_sV,_nD,_wE,_wD));}),_wG=function(_wH,_wI,_wJ,_wK,_wL,_wM,_wN,_wO,_wP,_wQ,_wR,_wS,_wT,_wU){var _wV=new T(function(){var _wW=new T(function(){var _wX=E(_wQ),_wY=E(_wU),_wZ=E(_wT),_x0=E(_wR),_x1=E(_wS),_x2=E(_wP);return new T3(0,_wX*_wY-_wZ*_x0,_x0*_x1-_wY*_x2,_x2*_wZ-_x1*_wX);}),_x3=function(_x4){var _x5=new T(function(){var _x6=E(_x4)/E(_vn);return (_x6+_x6)*3.141592653589793;}),_x7=new T(function(){return B(A1(_wH,_x5));}),_x8=new T(function(){var _x9=new T(function(){var _xa=E(_x7)/E(_wD);return new T3(0,E(_xa),E(_xa),E(_xa));}),_xb=function(_xc,_xd){var _xe=E(_xc);if(!_xe._){return new T2(0,_w,_xd);}else{var _xf=new T(function(){var _xg=B(_u9(_tz,new T(function(){var _xh=E(_xd),_xi=E(_xh.a),_xj=E(_xh.b),_xk=E(_x9);return new T3(0,E(_xi.a)+E(_xj.a)*E(_xk.a),E(_xi.b)+E(_xj.b)*E(_xk.b),E(_xi.c)+E(_xj.c)*E(_xk.c));}))),_xl=_xg.a,_xm=new T(function(){var _xn=E(_xg.b),_xo=E(E(_xd).b),_xp=B(_uB(_o5,_xo.a,_xo.b,_xo.c,_xn.a,_xn.b,_xn.c)),_xq=B(_tK(_o5,_xp.a,_xp.b,_xp.c));return new T3(0,E(_xq.a),E(_xq.b),E(_xq.c));});return new T2(0,new T(function(){var _xr=E(_x7),_xs=E(_x5);return new T4(0,E(_xl),E(new T2(0,E(_xe.a)/E(_wD),E(_xr))),E(_xs),E(_xm));}),new T2(0,_xl,_xm));}),_xt=new T(function(){var _xu=B(_xb(_xe.b,new T(function(){return E(E(_xf).b);})));return new T2(0,_xu.a,_xu.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xf).a);}),new T(function(){return E(E(_xt).a);})),new T(function(){return E(E(_xt).b);}));}},_xv=function(_xw,_xx,_xy,_xz,_xA){var _xB=E(_xw);if(!_xB._){return new T2(0,_w,new T2(0,new T3(0,E(_xx),E(_xy),E(_xz)),_xA));}else{var _xC=new T(function(){var _xD=B(_u9(_tz,new T(function(){var _xE=E(_xA),_xF=E(_x9);return new T3(0,E(_xx)+E(_xE.a)*E(_xF.a),E(_xy)+E(_xE.b)*E(_xF.b),E(_xz)+E(_xE.c)*E(_xF.c));}))),_xG=_xD.a,_xH=new T(function(){var _xI=E(_xD.b),_xJ=E(_xA),_xK=B(_uB(_o5,_xJ.a,_xJ.b,_xJ.c,_xI.a,_xI.b,_xI.c)),_xL=B(_tK(_o5,_xK.a,_xK.b,_xK.c));return new T3(0,E(_xL.a),E(_xL.b),E(_xL.c));});return new T2(0,new T(function(){var _xM=E(_x7),_xN=E(_x5);return new T4(0,E(_xG),E(new T2(0,E(_xB.a)/E(_wD),E(_xM))),E(_xN),E(_xH));}),new T2(0,_xG,_xH));}),_xO=new T(function(){var _xP=B(_xb(_xB.b,new T(function(){return E(E(_xC).b);})));return new T2(0,_xP.a,_xP.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xC).a);}),new T(function(){return E(E(_xO).a);})),new T(function(){return E(E(_xO).b);}));}};return E(B(_xv(_wF,_wK,_wL,_wM,new T(function(){var _xQ=E(_wW),_xR=E(_x5)+_wN,_xS=Math.cos(_xR),_xT=Math.sin(_xR);return new T3(0,E(_wP)*_xS+E(_xQ.a)*_xT,E(_wQ)*_xS+E(_xQ.b)*_xT,E(_wR)*_xS+E(_xQ.c)*_xT);}))).a);});return new T2(0,new T(function(){var _xU=E(_x7),_xV=E(_x5);return new T4(0,E(new T3(0,E(_wK),E(_wL),E(_wM))),E(new T2(0,E(_vc),E(_xU))),E(_xV),E(_vd));}),_x8);};return B(_tn(_x3,_wn));}),_xW=new T(function(){var _xX=function(_xY){return new F(function(){return A1(_wH,new T(function(){return B(_nw(_xY,_vV));}));});},_xZ=B(_tn(_xX,_wn));if(!_xZ._){return E(_wz);}else{return B(_ve(_xZ.b,E(_xZ.a)));}}),_y0=new T(function(){var _y1=new T(function(){var _y2=B(_n(_wV,new T2(1,new T(function(){var _y3=E(_wV);if(!_y3._){return E(_vp);}else{return E(_y3.a);}}),_w)));if(!_y2._){return E(_vB);}else{return E(_y2.b);}},1);return B(_vH(_wV,_y1));});return new T3(0,_y0,new T(function(){return B(_tn(_ww,_wV));}),_xW);},_y4=function(_y5,_y6,_y7,_y8,_y9,_ya,_yb,_yc,_yd,_ye,_yf,_yg,_yh,_yi,_yj,_yk,_yl,_ym){var _yn=B(_u9(_tz,new T3(0,E(_y8),E(_y9),E(_ya)))),_yo=_yn.b,_yp=E(_yn.a),_yq=B(_uP(_o5,_sV,_yo,new T3(0,E(_yc),E(_yd),E(_ye)))),_yr=E(_yo),_ys=_yr.a,_yt=_yr.b,_yu=_yr.c,_yv=B(_uB(_o5,_yg,_yh,_yi,_ys,_yt,_yu)),_yw=B(_tK(_o5,_yv.a,_yv.b,_yv.c)),_yx=_yw.a,_yy=_yw.b,_yz=_yw.c,_yA=E(_yb),_yB=new T2(0,E(new T3(0,E(_yq.a),E(_yq.b),E(_yq.c))),E(_yf)),_yC=B(_wG(_y5,_y6,_y7,_yp.a,_yp.b,_yp.c,_yA,_yB,_yx,_yy,_yz,_ys,_yt,_yu)),_yD=__lst2arr(B(_tn(_tw,_yC.a))),_yE=__lst2arr(B(_tn(_th,_yC.b)));return {_:0,a:_y5,b:_y6,c:_y7,d:new T2(0,E(_yp),E(_yA)),e:_yB,f:new T3(0,E(_yx),E(_yy),E(_yz)),g:_yr,h:_yD,i:_yE,j:E(_yC.c)};},_yF=1.0e-2,_yG=function(_yH,_yI,_yJ,_yK,_yL,_yM,_yN,_yO,_yP,_yQ,_yR,_yS,_yT,_yU,_yV,_yW,_yX,_yY){var _yZ=B(_s1(_nz,_yO,_yP,_yQ,_yR,_yF,_yF,_yF,_yF)),_z0=E(_yZ.a),_z1=B(_sc(_nz,_yK,_yL,_yM,_yN,_z0.a,_z0.b,_z0.c,_yZ.b)),_z2=E(_z1.a);return new F(function(){return _y4(_yH,_yI,_yJ,_z2.a,_z2.b,_z2.c,_z1.b,_yO,_yP,_yQ,_yR,_yS,_yT,_yU,_yV,_yW,_yX,_yY);});},_z3=function(_z4){var _z5=E(_z4),_z6=E(_z5.d),_z7=E(_z6.a),_z8=E(_z5.e),_z9=E(_z8.a),_za=E(_z5.f),_zb=B(_yG(_z5.a,_z5.b,_z5.c,_z7.a,_z7.b,_z7.c,_z6.b,_z9.a,_z9.b,_z9.c,_z8.b,_za.a,_za.b,_za.c,_z5.g,_z5.h,_z5.i,_z5.j));return {_:0,a:E(_zb.a),b:E(_zb.b),c:E(_zb.c),d:E(_zb.d),e:E(_zb.e),f:E(_zb.f),g:E(_zb.g),h:_zb.h,i:_zb.i,j:_zb.j};},_zc=function(_zd,_ze,_zf,_zg,_zh,_zi,_zj,_zk,_zl){var _zm=B(_8J(B(_8H(_zd))));return new F(function(){return A3(_6X,_zm,new T(function(){return B(_tA(_zd,_ze,_zf,_zg,_zi,_zj,_zk));}),new T(function(){return B(A3(_8L,_zm,_zh,_zl));}));});},_zn=new T(function(){return B(unCStr("base"));}),_zo=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_zp=new T(function(){return B(unCStr("IOException"));}),_zq=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zn,_zo,_zp),_zr=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zq,_w,_w),_zs=function(_zt){return E(_zr);},_zu=function(_zv){var _zw=E(_zv);return new F(function(){return _2n(B(_2l(_zw.a)),_zs,_zw.b);});},_zx=new T(function(){return B(unCStr(": "));}),_zy=new T(function(){return B(unCStr(")"));}),_zz=new T(function(){return B(unCStr(" ("));}),_zA=new T(function(){return B(unCStr("interrupted"));}),_zB=new T(function(){return B(unCStr("system error"));}),_zC=new T(function(){return B(unCStr("unsatisified constraints"));}),_zD=new T(function(){return B(unCStr("user error"));}),_zE=new T(function(){return B(unCStr("permission denied"));}),_zF=new T(function(){return B(unCStr("illegal operation"));}),_zG=new T(function(){return B(unCStr("end of file"));}),_zH=new T(function(){return B(unCStr("resource exhausted"));}),_zI=new T(function(){return B(unCStr("resource busy"));}),_zJ=new T(function(){return B(unCStr("does not exist"));}),_zK=new T(function(){return B(unCStr("already exists"));}),_zL=new T(function(){return B(unCStr("resource vanished"));}),_zM=new T(function(){return B(unCStr("timeout"));}),_zN=new T(function(){return B(unCStr("unsupported operation"));}),_zO=new T(function(){return B(unCStr("hardware fault"));}),_zP=new T(function(){return B(unCStr("inappropriate type"));}),_zQ=new T(function(){return B(unCStr("invalid argument"));}),_zR=new T(function(){return B(unCStr("failed"));}),_zS=new T(function(){return B(unCStr("protocol error"));}),_zT=function(_zU,_zV){switch(E(_zU)){case 0:return new F(function(){return _n(_zK,_zV);});break;case 1:return new F(function(){return _n(_zJ,_zV);});break;case 2:return new F(function(){return _n(_zI,_zV);});break;case 3:return new F(function(){return _n(_zH,_zV);});break;case 4:return new F(function(){return _n(_zG,_zV);});break;case 5:return new F(function(){return _n(_zF,_zV);});break;case 6:return new F(function(){return _n(_zE,_zV);});break;case 7:return new F(function(){return _n(_zD,_zV);});break;case 8:return new F(function(){return _n(_zC,_zV);});break;case 9:return new F(function(){return _n(_zB,_zV);});break;case 10:return new F(function(){return _n(_zS,_zV);});break;case 11:return new F(function(){return _n(_zR,_zV);});break;case 12:return new F(function(){return _n(_zQ,_zV);});break;case 13:return new F(function(){return _n(_zP,_zV);});break;case 14:return new F(function(){return _n(_zO,_zV);});break;case 15:return new F(function(){return _n(_zN,_zV);});break;case 16:return new F(function(){return _n(_zM,_zV);});break;case 17:return new F(function(){return _n(_zL,_zV);});break;default:return new F(function(){return _n(_zA,_zV);});}},_zW=new T(function(){return B(unCStr("}"));}),_zX=new T(function(){return B(unCStr("{handle: "));}),_zY=function(_zZ,_A0,_A1,_A2,_A3,_A4){var _A5=new T(function(){var _A6=new T(function(){var _A7=new T(function(){var _A8=E(_A2);if(!_A8._){return E(_A4);}else{var _A9=new T(function(){return B(_n(_A8,new T(function(){return B(_n(_zy,_A4));},1)));},1);return B(_n(_zz,_A9));}},1);return B(_zT(_A0,_A7));}),_Aa=E(_A1);if(!_Aa._){return E(_A6);}else{return B(_n(_Aa,new T(function(){return B(_n(_zx,_A6));},1)));}}),_Ab=E(_A3);if(!_Ab._){var _Ac=E(_zZ);if(!_Ac._){return E(_A5);}else{var _Ad=E(_Ac.a);if(!_Ad._){var _Ae=new T(function(){var _Af=new T(function(){return B(_n(_zW,new T(function(){return B(_n(_zx,_A5));},1)));},1);return B(_n(_Ad.a,_Af));},1);return new F(function(){return _n(_zX,_Ae);});}else{var _Ag=new T(function(){var _Ah=new T(function(){return B(_n(_zW,new T(function(){return B(_n(_zx,_A5));},1)));},1);return B(_n(_Ad.a,_Ah));},1);return new F(function(){return _n(_zX,_Ag);});}}}else{return new F(function(){return _n(_Ab.a,new T(function(){return B(_n(_zx,_A5));},1));});}},_Ai=function(_Aj){var _Ak=E(_Aj);return new F(function(){return _zY(_Ak.a,_Ak.b,_Ak.c,_Ak.d,_Ak.f,_w);});},_Al=function(_Am,_An,_Ao){var _Ap=E(_An);return new F(function(){return _zY(_Ap.a,_Ap.b,_Ap.c,_Ap.d,_Ap.f,_Ao);});},_Aq=function(_Ar,_As){var _At=E(_Ar);return new F(function(){return _zY(_At.a,_At.b,_At.c,_At.d,_At.f,_As);});},_Au=function(_Av,_Aw){return new F(function(){return _2Q(_Aq,_Av,_Aw);});},_Ax=new T3(0,_Al,_Ai,_Au),_Ay=new T(function(){return new T5(0,_zs,_Ax,_Az,_zu,_Ai);}),_Az=function(_AA){return new T2(0,_Ay,_AA);},_AB=__Z,_AC=7,_AD=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_AE=new T6(0,_AB,_AC,_w,_AD,_AB,_AB),_AF=new T(function(){return B(_Az(_AE));}),_AG=function(_){return new F(function(){return die(_AF);});},_AH=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_AI=new T6(0,_AB,_AC,_w,_AH,_AB,_AB),_AJ=new T(function(){return B(_Az(_AI));}),_AK=function(_){return new F(function(){return die(_AJ);});},_AL=function(_AM,_){return new T2(0,_w,_AM);},_AN=0.6,_AO=1,_AP=new T(function(){return B(unCStr(")"));}),_AQ=function(_AR,_AS){var _AT=new T(function(){var _AU=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mp(0,_AR,_w)),_AP));})));},1);return B(_n(B(_mp(0,_AS,_w)),_AU));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_AT)));});},_AV=function(_AW,_AX){var _AY=new T(function(){var _AZ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mp(0,_AX,_w)),_AP));})));},1);return B(_n(B(_mp(0,_AW,_w)),_AZ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_AY)));});},_B0=function(_B1){var _B2=E(_B1);if(!_B2._){return E(_AL);}else{var _B3=new T(function(){return B(_B0(_B2.b));}),_B4=function(_B5){var _B6=E(_B5);if(!_B6._){return E(_B3);}else{var _B7=_B6.a,_B8=new T(function(){return B(_B4(_B6.b));}),_B9=new T(function(){return 0.1*E(E(_B7).e)/1.0e-2;}),_Ba=new T(function(){var _Bb=E(_B7);if(_Bb.a!=_Bb.b){return E(_AO);}else{return E(_AN);}}),_Bc=function(_Bd,_){var _Be=E(_Bd),_Bf=_Be.c,_Bg=_Be.d,_Bh=E(_Be.a),_Bi=E(_Be.b),_Bj=E(_B7),_Bk=_Bj.a,_Bl=_Bj.b,_Bm=E(_Bj.c),_Bn=_Bm.b,_Bo=E(_Bm.a),_Bp=_Bo.a,_Bq=_Bo.b,_Br=_Bo.c,_Bs=E(_Bj.d),_Bt=_Bs.b,_Bu=E(_Bs.a),_Bv=_Bu.a,_Bw=_Bu.b,_Bx=_Bu.c;if(_Bh>_Bk){return new F(function(){return _AK(_);});}else{if(_Bk>_Bi){return new F(function(){return _AK(_);});}else{if(_Bh>_Bl){return new F(function(){return _AG(_);});}else{if(_Bl>_Bi){return new F(function(){return _AG(_);});}else{var _By=_Bk-_Bh|0;if(0>_By){return new F(function(){return _AQ(_Bf,_By);});}else{if(_By>=_Bf){return new F(function(){return _AQ(_Bf,_By);});}else{var _Bz=E(_Bg[_By]),_BA=E(_Bz.c),_BB=_BA.b,_BC=E(_BA.a),_BD=_BC.a,_BE=_BC.b,_BF=_BC.c,_BG=E(_Bz.e),_BH=E(_BG.a),_BI=B(_s1(_nz,_Bp,_Bq,_Br,_Bn,_BD,_BE,_BF,_BB)),_BJ=E(_BI.a),_BK=B(_s1(_nz,_BJ.a,_BJ.b,_BJ.c,_BI.b,_Bp,_Bq,_Br,_Bn)),_BL=E(_BK.a),_BM=_Bl-_Bh|0;if(0>_BM){return new F(function(){return _AV(_BM,_Bf);});}else{if(_BM>=_Bf){return new F(function(){return _AV(_BM,_Bf);});}else{var _BN=E(_Bg[_BM]),_BO=E(_BN.c),_BP=_BO.b,_BQ=E(_BO.a),_BR=_BQ.a,_BS=_BQ.b,_BT=_BQ.c,_BU=E(_BN.e),_BV=E(_BU.a),_BW=B(_s1(_nz,_Bv,_Bw,_Bx,_Bt,_BR,_BS,_BT,_BP)),_BX=E(_BW.a),_BY=B(_s1(_nz,_BX.a,_BX.b,_BX.c,_BW.b,_Bv,_Bw,_Bx,_Bt)),_BZ=E(_BY.a),_C0=E(_BL.a)+E(_BL.b)+E(_BL.c)+E(_BK.b)+E(_BZ.a)+E(_BZ.b)+E(_BZ.c)+E(_BY.b);if(!_C0){var _C1=B(A2(_B8,_Be,_));return new T2(0,new T2(1,_m4,new T(function(){return E(E(_C1).a);})),new T(function(){return E(E(_C1).b);}));}else{var _C2=new T(function(){return  -((B(_zc(_o5,_BH.a,_BH.b,_BH.c,_BG.b,_Bp,_Bq,_Br,_Bn))-B(_zc(_o5,_BV.a,_BV.b,_BV.c,_BU.b,_Bv,_Bw,_Bx,_Bt))-E(_B9))/_C0);}),_C3=function(_C4,_C5,_C6,_C7,_){var _C8=new T(function(){var _C9=function(_Ca,_Cb,_Cc,_Cd,_Ce){if(_Ca>_Bl){return E(_Ce);}else{if(_Bl>_Cb){return E(_Ce);}else{var _Cf=function(_){var _Cg=newArr(_Cc,_rm),_Ch=_Cg,_Ci=function(_Cj,_){while(1){if(_Cj!=_Cc){var _=_Ch[_Cj]=_Cd[_Cj],_Ck=_Cj+1|0;_Cj=_Ck;continue;}else{return E(_);}}},_=B(_Ci(0,_)),_Cl=_Bl-_Ca|0;if(0>_Cl){return new F(function(){return _AV(_Cl,_Cc);});}else{if(_Cl>=_Cc){return new F(function(){return _AV(_Cl,_Cc);});}else{var _=_Ch[_Cl]=new T(function(){var _Cm=E(_Cd[_Cl]),_Cn=E(_Cm.e),_Co=E(_Cn.a),_Cp=B(_s1(_nz,_BR,_BS,_BT,_BP,_Bv,_Bw,_Bx,_Bt)),_Cq=E(_Cp.a),_Cr=E(_C2)*E(_Ba),_Cs=B(_s1(_nz,_Cq.a,_Cq.b,_Cq.c,_Cp.b,_Cr,_Cr,_Cr,_Cr)),_Ct=E(_Cs.a),_Cu=B(_sc(_nz,_Co.a,_Co.b,_Co.c,_Cn.b, -E(_Ct.a), -E(_Ct.b), -E(_Ct.c), -E(_Cs.b)));return {_:0,a:E(_Cm.a),b:E(_Cm.b),c:E(_Cm.c),d:E(_Cm.d),e:E(new T2(0,E(_Cu.a),E(_Cu.b))),f:E(_Cm.f),g:E(_Cm.g),h:_Cm.h,i:_Cm.i,j:_Cm.j};});return new T4(0,E(_Ca),E(_Cb),_Cc,_Ch);}}};return new F(function(){return _rr(_Cf);});}}};if(_C4>_Bk){return B(_C9(_C4,_C5,_C6,_C7,new T4(0,E(_C4),E(_C5),_C6,_C7)));}else{if(_Bk>_C5){return B(_C9(_C4,_C5,_C6,_C7,new T4(0,E(_C4),E(_C5),_C6,_C7)));}else{var _Cv=function(_){var _Cw=newArr(_C6,_rm),_Cx=_Cw,_Cy=function(_Cz,_){while(1){if(_Cz!=_C6){var _=_Cx[_Cz]=_C7[_Cz],_CA=_Cz+1|0;_Cz=_CA;continue;}else{return E(_);}}},_=B(_Cy(0,_)),_CB=_Bk-_C4|0;if(0>_CB){return new F(function(){return _AQ(_C6,_CB);});}else{if(_CB>=_C6){return new F(function(){return _AQ(_C6,_CB);});}else{var _=_Cx[_CB]=new T(function(){var _CC=E(_C7[_CB]),_CD=E(_CC.e),_CE=E(_CD.a),_CF=B(_s1(_nz,_BD,_BE,_BF,_BB,_Bp,_Bq,_Br,_Bn)),_CG=E(_CF.a),_CH=E(_C2)*E(_Ba),_CI=B(_s1(_nz,_CG.a,_CG.b,_CG.c,_CF.b,_CH,_CH,_CH,_CH)),_CJ=E(_CI.a),_CK=B(_sc(_nz,_CE.a,_CE.b,_CE.c,_CD.b,_CJ.a,_CJ.b,_CJ.c,_CI.b));return {_:0,a:E(_CC.a),b:E(_CC.b),c:E(_CC.c),d:E(_CC.d),e:E(new T2(0,E(_CK.a),E(_CK.b))),f:E(_CC.f),g:E(_CC.g),h:_CC.h,i:_CC.i,j:_CC.j};});return new T4(0,E(_C4),E(_C5),_C6,_Cx);}}},_CL=B(_rr(_Cv));return B(_C9(E(_CL.a),E(_CL.b),_CL.c,_CL.d,_CL));}}});return new T2(0,_m4,_C8);};if(!E(_Bj.f)){var _CM=B(_C3(_Bh,_Bi,_Bf,_Bg,_)),_CN=B(A2(_B8,new T(function(){return E(E(_CM).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CM).a);}),new T(function(){return E(E(_CN).a);})),new T(function(){return E(E(_CN).b);}));}else{if(E(_C2)<0){var _CO=B(A2(_B8,_Be,_));return new T2(0,new T2(1,_m4,new T(function(){return E(E(_CO).a);})),new T(function(){return E(E(_CO).b);}));}else{var _CP=B(_C3(_Bh,_Bi,_Bf,_Bg,_)),_CQ=B(A2(_B8,new T(function(){return E(E(_CP).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CP).a);}),new T(function(){return E(E(_CQ).a);})),new T(function(){return E(E(_CQ).b);}));}}}}}}}}}}}};return E(_Bc);}};return new F(function(){return _B4(_B2.a);});}},_CR=function(_,_CS){var _CT=new T(function(){return B(_B0(E(_CS).a));}),_CU=function(_CV){var _CW=E(_CV);return (_CW==1)?E(new T2(1,_CT,_w)):new T2(1,_CT,new T(function(){return B(_CU(_CW-1|0));}));},_CX=B(_r6(B(_CU(5)),new T(function(){return E(E(_CS).b);}),_)),_CY=new T(function(){return B(_rL(_r5,_mR,_z3,new T(function(){return E(E(_CX).b);})));});return new T2(0,_m4,_CY);},_CZ=function(_D0,_D1,_D2,_D3,_D4){var _D5=B(_8J(B(_8H(_D0))));return new F(function(){return A3(_6X,_D5,new T(function(){return B(A3(_8L,_D5,_D1,_D3));}),new T(function(){return B(A3(_8L,_D5,_D2,_D4));}));});},_D6=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_D7=new T6(0,_AB,_AC,_w,_D6,_AB,_AB),_D8=new T(function(){return B(_Az(_D7));}),_D9=function(_){return new F(function(){return die(_D8);});},_Da=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Db=new T6(0,_AB,_AC,_w,_Da,_AB,_AB),_Dc=new T(function(){return B(_Az(_Db));}),_Dd=function(_){return new F(function(){return die(_Dc);});},_De=function(_Df,_Dg,_Dh,_Di){var _Dj=new T(function(){return B(_8J(new T(function(){return B(_8H(_Df));})));}),_Dk=B(A2(_8s,_Dj,_8q));return new F(function(){return _tK(_Df,_Dk,B(A2(_8s,_Dj,_8r)),_Dk);});},_Dl=false,_Dm=true,_Dn=function(_Do){var _Dp=E(_Do),_Dq=_Dp.b,_Dr=E(_Dp.d),_Ds=E(_Dp.e),_Dt=E(_Ds.a),_Du=E(_Dp.g),_Dv=B(A1(_Dq,_Dr.a)),_Dw=B(_uB(_o5,_Dv.a,_Dv.b,_Dv.c,_Du.a,_Du.b,_Du.c));return {_:0,a:E(_Dp.a),b:E(_Dq),c:E(_Dp.c),d:E(_Dr),e:E(new T2(0,E(new T3(0,E(_Dt.a)+E(_Dw.a)*1.0e-2,E(_Dt.b)+E(_Dw.b)*1.0e-2,E(_Dt.c)+E(_Dw.c)*1.0e-2)),E(_Ds.b))),f:E(_Dp.f),g:E(_Du),h:_Dp.h,i:_Dp.i,j:_Dp.j};},_Dx=new T(function(){return eval("__strict(collideBound)");}),_Dy=new T(function(){return eval("__strict(mouseContact)");}),_Dz=new T(function(){return eval("__strict(collide)");}),_DA=function(_DB){var _DC=E(_DB);if(!_DC._){return __Z;}else{return new F(function(){return _n(_DC.a,new T(function(){return B(_DA(_DC.b));},1));});}},_DD=0,_DE=new T3(0,E(_DD),E(_DD),E(_DD)),_DF=new T2(0,E(_DE),E(_DD)),_DG=function(_DH,_){var _DI=B(_rL(_r5,_mR,_Dn,_DH)),_DJ=E(_DI.a),_DK=E(_DI.b);if(_DJ<=_DK){var _DL=function(_DM,_DN,_DO,_DP,_DQ,_){if(_DN>_DM){return new F(function(){return _Dd(_);});}else{if(_DM>_DO){return new F(function(){return _Dd(_);});}else{var _DR=new T(function(){var _DS=_DM-_DN|0;if(0>_DS){return B(_AV(_DS,_DP));}else{if(_DS>=_DP){return B(_AV(_DS,_DP));}else{return E(_DQ[_DS]);}}}),_DT=function(_DU,_DV,_DW,_DX,_DY,_){var _DZ=E(_DU);if(!_DZ._){return new T2(0,_w,new T4(0,E(_DV),E(_DW),_DX,_DY));}else{var _E0=E(_DZ.a);if(_DV>_E0){return new F(function(){return _D9(_);});}else{if(_E0>_DW){return new F(function(){return _D9(_);});}else{var _E1=_E0-_DV|0;if(0>_E1){return new F(function(){return _AQ(_DX,_E1);});}else{if(_E1>=_DX){return new F(function(){return _AQ(_DX,_E1);});}else{var _E2=__app2(E(_Dz),B(_mf(E(_DR))),B(_mf(E(_DY[_E1])))),_E3=__arr2lst(0,_E2),_E4=B(_oI(_E3,_)),_E5=B(_DT(_DZ.b,_DV,_DW,_DX,_DY,_)),_E6=new T(function(){var _E7=new T(function(){return _DM!=_E0;}),_E8=function(_E9){var _Ea=E(_E9);if(!_Ea._){return __Z;}else{var _Eb=_Ea.b,_Ec=E(_Ea.a),_Ed=E(_Ec.b),_Ee=E(_Ec.a),_Ef=E(_Ee.a),_Eg=E(_Ee.b),_Eh=E(_Ee.c),_Ei=E(_Ed.a),_Ej=E(_Ed.b),_Ek=E(_Ed.c),_El=E(_Ec.c),_Em=_El.a,_En=_El.b,_Eo=E(_Ec.e),_Ep=E(_Ec.d),_Eq=_Ep.a,_Er=_Ep.b,_Es=E(_Ec.f),_Et=new T(function(){var _Eu=B(_tK(_o5,_Es.a,_Es.b,_Es.c)),_Ev=Math.sqrt(B(_CZ(_o5,_Eq,_Er,_Eq,_Er)));return new T3(0,_Ev*E(_Eu.a),_Ev*E(_Eu.b),_Ev*E(_Eu.c));}),_Ew=new T(function(){var _Ex=B(_tK(_o5,_Eo.a,_Eo.b,_Eo.c)),_Ey=Math.sqrt(B(_CZ(_o5,_Em,_En,_Em,_En)));return new T3(0,_Ey*E(_Ex.a),_Ey*E(_Ex.b),_Ey*E(_Ex.c));}),_Ez=new T(function(){var _EA=B(_De(_o5,_Ei,_Ej,_Ek));return new T3(0,E(_EA.a),E(_EA.b),E(_EA.c));}),_EB=new T(function(){var _EC=B(_De(_o5,_Ef,_Eg,_Eh));return new T3(0,E(_EC.a),E(_EC.b),E(_EC.c));}),_ED=_Ei+ -_Ef,_EE=_Ej+ -_Eg,_EF=_Ek+ -_Eh,_EG=new T(function(){return Math.sqrt(B(_tA(_o5,_ED,_EE,_EF,_ED,_EE,_EF)));}),_EH=new T(function(){var _EI=1/E(_EG);return new T3(0,_ED*_EI,_EE*_EI,_EF*_EI);}),_EJ=new T(function(){if(!E(_Ec.g)){return E(_EH);}else{var _EK=E(_EH);return new T3(0,-1*E(_EK.a),-1*E(_EK.b),-1*E(_EK.c));}}),_EL=new T(function(){if(!E(_Ec.h)){return E(_EH);}else{var _EM=E(_EH);return new T3(0,-1*E(_EM.a),-1*E(_EM.b),-1*E(_EM.c));}});return (!E(_E7))?new T2(1,new T(function(){var _EN=E(_EJ),_EO=E(_EN.b),_EP=E(_EN.c),_EQ=E(_EN.a),_ER=E(_EB),_ES=E(_ER.c),_ET=E(_ER.b),_EU=E(_ER.a),_EV=E(_Ew),_EW=E(_EV.c),_EX=E(_EV.b),_EY=E(_EV.a),_EZ=_EO*_ES-_ET*_EP,_F0=_EP*_EU-_ES*_EQ,_F1=_EQ*_ET-_EU*_EO,_F2=B(_tA(_o5,_F0*_EW-_EX*_F1,_F1*_EY-_EW*_EZ,_EZ*_EX-_EY*_F0,_EU,_ET,_ES));return new T6(0,_DM,_E0,E(new T2(0,E(new T3(0,E(_EZ),E(_F0),E(_F1))),E(_F2))),E(_DF),_EG,_Dl);}),new T2(1,new T(function(){var _F3=E(_EL),_F4=E(_F3.b),_F5=E(_F3.c),_F6=E(_F3.a),_F7=E(_Ez),_F8=E(_F7.c),_F9=E(_F7.b),_Fa=E(_F7.a),_Fb=E(_Et),_Fc=E(_Fb.c),_Fd=E(_Fb.b),_Fe=E(_Fb.a),_Ff=_F4*_F8-_F9*_F5,_Fg=_F5*_Fa-_F8*_F6,_Fh=_F6*_F9-_Fa*_F4,_Fi=B(_tA(_o5,_Fg*_Fc-_Fd*_Fh,_Fh*_Fe-_Fc*_Ff,_Ff*_Fd-_Fe*_Fg,_Fa,_F9,_F8));return new T6(0,_DM,_E0,E(_DF),E(new T2(0,E(new T3(0,E(_Ff),E(_Fg),E(_Fh))),E(_Fi))),_EG,_Dl);}),new T(function(){return B(_E8(_Eb));}))):new T2(1,new T(function(){var _Fj=E(_EJ),_Fk=E(_Fj.b),_Fl=E(_Fj.c),_Fm=E(_Fj.a),_Fn=E(_EB),_Fo=_Fn.a,_Fp=_Fn.b,_Fq=_Fn.c,_Fr=B(_uB(_o5,_Fm,_Fk,_Fl,_Fo,_Fp,_Fq)),_Fs=E(_Ew),_Ft=E(_Fs.c),_Fu=E(_Fs.b),_Fv=E(_Fs.a),_Fw=B(_tA(_o5,_Fk*_Ft-_Fu*_Fl,_Fl*_Fv-_Ft*_Fm,_Fm*_Fu-_Fv*_Fk,_Fo,_Fp,_Fq)),_Fx=E(_EL),_Fy=E(_Fx.b),_Fz=E(_Fx.c),_FA=E(_Fx.a),_FB=E(_Ez),_FC=_FB.a,_FD=_FB.b,_FE=_FB.c,_FF=B(_uB(_o5,_FA,_Fy,_Fz,_FC,_FD,_FE)),_FG=E(_Et),_FH=E(_FG.c),_FI=E(_FG.b),_FJ=E(_FG.a),_FK=B(_tA(_o5,_Fy*_FH-_FI*_Fz,_Fz*_FJ-_FH*_FA,_FA*_FI-_FJ*_Fy,_FC,_FD,_FE));return new T6(0,_DM,_E0,E(new T2(0,E(new T3(0,E(_Fr.a),E(_Fr.b),E(_Fr.c))),E(_Fw))),E(new T2(0,E(new T3(0,E(_FF.a),E(_FF.b),E(_FF.c))),E(_FK))),_EG,_Dm);}),new T(function(){return B(_E8(_Eb));}));}};return B(_E8(_E4));});return new T2(0,new T2(1,_E6,new T(function(){return E(E(_E5).a);})),new T(function(){return E(E(_E5).b);}));}}}}}},_FL=B(_DT(B(_q9(_DM,_DK)),_DN,_DO,_DP,_DQ,_)),_FM=E(_DR),_FN=E(_FM.d).a,_FO=__app1(E(_Dx),B(_mf(_FM))),_FP=__arr2lst(0,_FO),_FQ=B(_oI(_FP,_)),_FR=__app1(E(_Dy),_DM),_FS=__arr2lst(0,_FR),_FT=B(_oI(_FS,_));if(_DM!=_DK){var _FU=E(_FL),_FV=E(_FU.b),_FW=B(_DL(_DM+1|0,E(_FV.a),E(_FV.b),_FV.c,_FV.d,_)),_FX=new T(function(){var _FY=new T(function(){var _FZ=E(_FN),_G0=B(_De(_o5,_FZ.a,_FZ.b,_FZ.c));return new T3(0,E(_G0.a),E(_G0.b),E(_G0.c));}),_G1=new T(function(){var _G2=new T(function(){return B(_DA(_FU.a));}),_G3=function(_G4){var _G5=E(_G4);if(!_G5._){return E(_G2);}else{var _G6=E(_G5.a),_G7=E(_G6.b),_G8=E(_G6.a),_G9=E(_G8.a),_Ga=E(_G8.b),_Gb=E(_G8.c),_Gc=E(_G6.c),_Gd=_Gc.a,_Ge=_Gc.b,_Gf=E(_G6.e);return new T2(1,new T(function(){var _Gg=E(_G7.a)+ -_G9,_Gh=E(_G7.b)+ -_Ga,_Gi=E(_G7.c)+ -_Gb,_Gj=B(_De(_o5,_G9,_Ga,_Gb)),_Gk=_Gj.a,_Gl=_Gj.b,_Gm=_Gj.c,_Gn=Math.sqrt(B(_tA(_o5,_Gg,_Gh,_Gi,_Gg,_Gh,_Gi))),_Go=1/_Gn,_Gp=_Gg*_Go,_Gq=_Gh*_Go,_Gr=_Gi*_Go,_Gs=B(_uB(_o5,_Gp,_Gq,_Gr,_Gk,_Gl,_Gm)),_Gt=B(_tK(_o5,_Gf.a,_Gf.b,_Gf.c)),_Gu=Math.sqrt(B(_CZ(_o5,_Gd,_Ge,_Gd,_Ge))),_Gv=_Gu*E(_Gt.a),_Gw=_Gu*E(_Gt.b),_Gx=_Gu*E(_Gt.c),_Gy=B(_tA(_o5,_Gq*_Gx-_Gw*_Gr,_Gr*_Gv-_Gx*_Gp,_Gp*_Gw-_Gv*_Gq,_Gk,_Gl,_Gm));return new T6(0,_DM,_DM,E(new T2(0,E(new T3(0,E(_Gs.a),E(_Gs.b),E(_Gs.c))),E(_Gy))),E(_DF),_Gn,_Dm);}),new T(function(){return B(_G3(_G5.b));}));}};return B(_G3(_FQ));}),_Gz=function(_GA){var _GB=E(_GA);if(!_GB._){return E(_G1);}else{var _GC=E(_GB.a),_GD=E(_GC.b),_GE=new T(function(){var _GF=E(_FN),_GG=E(_GD.c)+ -E(_GF.c),_GH=E(_GD.b)+ -E(_GF.b),_GI=E(_GD.a)+ -E(_GF.a),_GJ=Math.sqrt(B(_tA(_o5,_GI,_GH,_GG,_GI,_GH,_GG))),_GK=function(_GL,_GM,_GN){var _GO=E(_FY),_GP=_GO.a,_GQ=_GO.b,_GR=_GO.c,_GS=B(_uB(_o5,_GL,_GM,_GN,_GP,_GQ,_GR)),_GT=B(_tA(_o5,_GM*0-0*_GN,_GN*0-0*_GL,_GL*0-0*_GM,_GP,_GQ,_GR));return new T6(0,_DM,_DM,new T2(0,E(new T3(0,E(_GS.a),E(_GS.b),E(_GS.c))),E(_GT)),_DF,_GJ,_Dm);};if(!E(_GC.g)){var _GU=1/_GJ,_GV=B(_GK(_GI*_GU,_GH*_GU,_GG*_GU));return new T6(0,_GV.a,_GV.b,E(_GV.c),E(_GV.d),_GV.e,_GV.f);}else{var _GW=1/_GJ,_GX=B(_GK(-1*_GI*_GW,-1*_GH*_GW,-1*_GG*_GW));return new T6(0,_GX.a,_GX.b,E(_GX.c),E(_GX.d),_GX.e,_GX.f);}});return new T2(1,_GE,new T(function(){return B(_Gz(_GB.b));}));}};return B(_Gz(_FT));});return new T2(0,new T2(1,_FX,new T(function(){return E(E(_FW).a);})),new T(function(){return E(E(_FW).b);}));}else{var _GY=new T(function(){var _GZ=new T(function(){var _H0=E(_FN),_H1=B(_De(_o5,_H0.a,_H0.b,_H0.c));return new T3(0,E(_H1.a),E(_H1.b),E(_H1.c));}),_H2=new T(function(){var _H3=new T(function(){return B(_DA(E(_FL).a));}),_H4=function(_H5){var _H6=E(_H5);if(!_H6._){return E(_H3);}else{var _H7=E(_H6.a),_H8=E(_H7.b),_H9=E(_H7.a),_Ha=E(_H9.a),_Hb=E(_H9.b),_Hc=E(_H9.c),_Hd=E(_H7.c),_He=_Hd.a,_Hf=_Hd.b,_Hg=E(_H7.e);return new T2(1,new T(function(){var _Hh=E(_H8.a)+ -_Ha,_Hi=E(_H8.b)+ -_Hb,_Hj=E(_H8.c)+ -_Hc,_Hk=B(_De(_o5,_Ha,_Hb,_Hc)),_Hl=_Hk.a,_Hm=_Hk.b,_Hn=_Hk.c,_Ho=Math.sqrt(B(_tA(_o5,_Hh,_Hi,_Hj,_Hh,_Hi,_Hj))),_Hp=1/_Ho,_Hq=_Hh*_Hp,_Hr=_Hi*_Hp,_Hs=_Hj*_Hp,_Ht=B(_uB(_o5,_Hq,_Hr,_Hs,_Hl,_Hm,_Hn)),_Hu=B(_tK(_o5,_Hg.a,_Hg.b,_Hg.c)),_Hv=Math.sqrt(B(_CZ(_o5,_He,_Hf,_He,_Hf))),_Hw=_Hv*E(_Hu.a),_Hx=_Hv*E(_Hu.b),_Hy=_Hv*E(_Hu.c),_Hz=B(_tA(_o5,_Hr*_Hy-_Hx*_Hs,_Hs*_Hw-_Hy*_Hq,_Hq*_Hx-_Hw*_Hr,_Hl,_Hm,_Hn));return new T6(0,_DM,_DM,E(new T2(0,E(new T3(0,E(_Ht.a),E(_Ht.b),E(_Ht.c))),E(_Hz))),E(_DF),_Ho,_Dm);}),new T(function(){return B(_H4(_H6.b));}));}};return B(_H4(_FQ));}),_HA=function(_HB){var _HC=E(_HB);if(!_HC._){return E(_H2);}else{var _HD=E(_HC.a),_HE=E(_HD.b),_HF=new T(function(){var _HG=E(_FN),_HH=E(_HE.c)+ -E(_HG.c),_HI=E(_HE.b)+ -E(_HG.b),_HJ=E(_HE.a)+ -E(_HG.a),_HK=Math.sqrt(B(_tA(_o5,_HJ,_HI,_HH,_HJ,_HI,_HH))),_HL=function(_HM,_HN,_HO){var _HP=E(_GZ),_HQ=_HP.a,_HR=_HP.b,_HS=_HP.c,_HT=B(_uB(_o5,_HM,_HN,_HO,_HQ,_HR,_HS)),_HU=B(_tA(_o5,_HN*0-0*_HO,_HO*0-0*_HM,_HM*0-0*_HN,_HQ,_HR,_HS));return new T6(0,_DM,_DM,new T2(0,E(new T3(0,E(_HT.a),E(_HT.b),E(_HT.c))),E(_HU)),_DF,_HK,_Dm);};if(!E(_HD.g)){var _HV=1/_HK,_HW=B(_HL(_HJ*_HV,_HI*_HV,_HH*_HV));return new T6(0,_HW.a,_HW.b,E(_HW.c),E(_HW.d),_HW.e,_HW.f);}else{var _HX=1/_HK,_HY=B(_HL(-1*_HJ*_HX,-1*_HI*_HX,-1*_HH*_HX));return new T6(0,_HY.a,_HY.b,E(_HY.c),E(_HY.d),_HY.e,_HY.f);}});return new T2(1,_HF,new T(function(){return B(_HA(_HC.b));}));}};return B(_HA(_FT));});return new T2(0,new T2(1,_GY,_w),new T(function(){return E(E(_FL).b);}));}}}},_HZ=B(_DL(_DJ,_DJ,_DK,_DI.c,_DI.d,_));return new F(function(){return _CR(_,_HZ);});}else{return new F(function(){return _CR(_,new T2(0,_w,_DI));});}},_I0=new T(function(){return eval("__strict(passObject)");}),_I1=new T(function(){return eval("__strict(refresh)");}),_I2=function(_I3,_){var _I4=__app0(E(_I1)),_I5=__app0(E(_mk)),_I6=E(_I3),_I7=_I6.c,_I8=_I6.d,_I9=E(_I6.a),_Ia=E(_I6.b);if(_I9<=_Ia){if(_I9>_Ia){return E(_mi);}else{if(0>=_I7){return new F(function(){return _mv(_I7,0);});}else{var _Ib=E(_I0),_Ic=__app2(_Ib,_I9,B(_mf(E(_I8[0]))));if(_I9!=_Ia){var _Id=function(_Ie,_){if(_I9>_Ie){return E(_mi);}else{if(_Ie>_Ia){return E(_mi);}else{var _If=_Ie-_I9|0;if(0>_If){return new F(function(){return _mv(_I7,_If);});}else{if(_If>=_I7){return new F(function(){return _mv(_I7,_If);});}else{var _Ig=__app2(_Ib,_Ie,B(_mf(E(_I8[_If]))));if(_Ie!=_Ia){var _Ih=B(_Id(_Ie+1|0,_));return new T2(1,_m4,_Ih);}else{return _mA;}}}}}},_Ii=B(_Id(_I9+1|0,_)),_Ij=__app0(E(_mj)),_Ik=B(_DG(_I6,_));return new T(function(){return E(E(_Ik).b);});}else{var _Il=__app0(E(_mj)),_Im=B(_DG(_I6,_));return new T(function(){return E(E(_Im).b);});}}}}else{var _In=__app0(E(_mj)),_Io=B(_DG(_I6,_));return new T(function(){return E(E(_Io).b);});}},_Ip=new T(function(){return B(unCStr("Negative exponent"));}),_Iq=new T(function(){return B(err(_Ip));}),_Ir=function(_Is,_It,_Iu){while(1){if(!(_It%2)){var _Iv=_Is*_Is,_Iw=quot(_It,2);_Is=_Iv;_It=_Iw;continue;}else{var _Ix=E(_It);if(_Ix==1){return _Is*_Iu;}else{var _Iv=_Is*_Is,_Iy=_Is*_Iu;_Is=_Iv;_It=quot(_Ix-1|0,2);_Iu=_Iy;continue;}}}},_Iz=function(_IA,_IB){while(1){if(!(_IB%2)){var _IC=_IA*_IA,_ID=quot(_IB,2);_IA=_IC;_IB=_ID;continue;}else{var _IE=E(_IB);if(_IE==1){return E(_IA);}else{return new F(function(){return _Ir(_IA*_IA,quot(_IE-1|0,2),_IA);});}}}},_IF=-4,_IG=new T3(0,E(_vc),E(_vc),E(_IF)),_IH=function(_II){return E(_IG);},_IJ=function(_){return new F(function(){return __jsNull();});},_IK=function(_IL){var _IM=B(A1(_IL,_));return E(_IM);},_IN=new T(function(){return B(_IK(_IJ));}),_IO=function(_IP,_IQ,_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ,_J0,_J1){var _J2=function(_J3){var _J4=E(_vV),_J5=2+_J3|0,_J6=_J5-1|0,_J7=(2+_J3)*(1+_J3),_J8=E(_wn);if(!_J8._){return _J4*0;}else{var _J9=_J8.a,_Ja=_J8.b,_Jb=B(A1(_IP,new T(function(){return 6.283185307179586*E(_J9)/E(_vn);}))),_Jc=B(A1(_IP,new T(function(){return 6.283185307179586*(E(_J9)+1)/E(_vn);})));if(_Jb!=_Jc){if(_J5>=0){var _Jd=E(_J5);if(!_Jd){var _Je=function(_Jf,_Jg){while(1){var _Jh=B((function(_Ji,_Jj){var _Jk=E(_Ji);if(!_Jk._){return E(_Jj);}else{var _Jl=_Jk.a,_Jm=_Jk.b,_Jn=B(A1(_IP,new T(function(){return 6.283185307179586*E(_Jl)/E(_vn);}))),_Jo=B(A1(_IP,new T(function(){return 6.283185307179586*(E(_Jl)+1)/E(_vn);})));if(_Jn!=_Jo){var _Jp=_Jj+0/(_Jn-_Jo)/_J7;_Jf=_Jm;_Jg=_Jp;return __continue;}else{if(_J6>=0){var _Jq=E(_J6);if(!_Jq){var _Jp=_Jj+_J5/_J7;_Jf=_Jm;_Jg=_Jp;return __continue;}else{var _Jp=_Jj+_J5*B(_Iz(_Jn,_Jq))/_J7;_Jf=_Jm;_Jg=_Jp;return __continue;}}else{return E(_Iq);}}}})(_Jf,_Jg));if(_Jh!=__continue){return _Jh;}}};return _J4*B(_Je(_Ja,0/(_Jb-_Jc)/_J7));}else{var _Jr=function(_Js,_Jt){while(1){var _Ju=B((function(_Jv,_Jw){var _Jx=E(_Jv);if(!_Jx._){return E(_Jw);}else{var _Jy=_Jx.a,_Jz=_Jx.b,_JA=B(A1(_IP,new T(function(){return 6.283185307179586*E(_Jy)/E(_vn);}))),_JB=B(A1(_IP,new T(function(){return 6.283185307179586*(E(_Jy)+1)/E(_vn);})));if(_JA!=_JB){if(_Jd>=0){var _JC=_Jw+(B(_Iz(_JA,_Jd))-B(_Iz(_JB,_Jd)))/(_JA-_JB)/_J7;_Js=_Jz;_Jt=_JC;return __continue;}else{return E(_Iq);}}else{if(_J6>=0){var _JD=E(_J6);if(!_JD){var _JC=_Jw+_J5/_J7;_Js=_Jz;_Jt=_JC;return __continue;}else{var _JC=_Jw+_J5*B(_Iz(_JA,_JD))/_J7;_Js=_Jz;_Jt=_JC;return __continue;}}else{return E(_Iq);}}}})(_Js,_Jt));if(_Ju!=__continue){return _Ju;}}};return _J4*B(_Jr(_Ja,(B(_Iz(_Jb,_Jd))-B(_Iz(_Jc,_Jd)))/(_Jb-_Jc)/_J7));}}else{return E(_Iq);}}else{if(_J6>=0){var _JE=E(_J6);if(!_JE){var _JF=function(_JG,_JH){while(1){var _JI=B((function(_JJ,_JK){var _JL=E(_JJ);if(!_JL._){return E(_JK);}else{var _JM=_JL.a,_JN=_JL.b,_JO=B(A1(_IP,new T(function(){return 6.283185307179586*E(_JM)/E(_vn);}))),_JP=B(A1(_IP,new T(function(){return 6.283185307179586*(E(_JM)+1)/E(_vn);})));if(_JO!=_JP){if(_J5>=0){var _JQ=E(_J5);if(!_JQ){var _JR=_JK+0/(_JO-_JP)/_J7;_JG=_JN;_JH=_JR;return __continue;}else{var _JR=_JK+(B(_Iz(_JO,_JQ))-B(_Iz(_JP,_JQ)))/(_JO-_JP)/_J7;_JG=_JN;_JH=_JR;return __continue;}}else{return E(_Iq);}}else{var _JR=_JK+_J5/_J7;_JG=_JN;_JH=_JR;return __continue;}}})(_JG,_JH));if(_JI!=__continue){return _JI;}}};return _J4*B(_JF(_Ja,_J5/_J7));}else{var _JS=function(_JT,_JU){while(1){var _JV=B((function(_JW,_JX){var _JY=E(_JW);if(!_JY._){return E(_JX);}else{var _JZ=_JY.a,_K0=_JY.b,_K1=B(A1(_IP,new T(function(){return 6.283185307179586*E(_JZ)/E(_vn);}))),_K2=B(A1(_IP,new T(function(){return 6.283185307179586*(E(_JZ)+1)/E(_vn);})));if(_K1!=_K2){if(_J5>=0){var _K3=E(_J5);if(!_K3){var _K4=_JX+0/(_K1-_K2)/_J7;_JT=_K0;_JU=_K4;return __continue;}else{var _K4=_JX+(B(_Iz(_K1,_K3))-B(_Iz(_K2,_K3)))/(_K1-_K2)/_J7;_JT=_K0;_JU=_K4;return __continue;}}else{return E(_Iq);}}else{if(_JE>=0){var _K4=_JX+_J5*B(_Iz(_K1,_JE))/_J7;_JT=_K0;_JU=_K4;return __continue;}else{return E(_Iq);}}}})(_JT,_JU));if(_JV!=__continue){return _JV;}}};return _J4*B(_JS(_Ja,_J5*B(_Iz(_Jb,_JE))/_J7));}}else{return E(_Iq);}}}},_K5=E(_IN),_K6=1/(B(_J2(1))*_IQ);return new F(function(){return _y4(_IP,_IH,new T2(0,E(new T3(0,E(_K6),E(_K6),E(_K6))),1/(B(_J2(3))*_IQ)),_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ,_J0,_J1,_vd,_K5,_K5,0);});},_K7=0.5,_K8=1,_K9=0,_Ka=0.3,_Kb=function(_Kc){return E(_Ka);},_Kd=new T(function(){var _Ke=B(_IO(_Kb,1.2,_K9,_K8,_K7,_K9,_K9,_K9,_K9,_K9,_K8,_K8,_K8));return {_:0,a:E(_Ke.a),b:E(_Ke.b),c:E(_Ke.c),d:E(_Ke.d),e:E(_Ke.e),f:E(_Ke.f),g:E(_Ke.g),h:_Ke.h,i:_Ke.i,j:_Ke.j};}),_Kf=0,_Kg=function(_){var _Kh=newArr(1,_rm),_=_Kh[0]=_Kd;return new T4(0,E(_Kf),E(_Kf),1,_Kh);},_Ki=new T(function(){return B(_rr(_Kg));}),_Kj=function(_Kk,_){while(1){var _Kl=E(_Kk);if(!_Kl._){return _m4;}else{var _Km=_Kl.b,_Kn=E(_Kl.a);switch(_Kn._){case 0:var _Ko=B(A1(_Kn.a,_));_Kk=B(_n(_Km,new T2(1,_Ko,_w)));continue;case 1:_Kk=B(_n(_Km,_Kn.a));continue;default:_Kk=_Km;continue;}}}},_Kp=function(_Kq,_Kr,_){var _Ks=E(_Kq);switch(_Ks._){case 0:var _Kt=B(A1(_Ks.a,_));return new F(function(){return _Kj(B(_n(_Kr,new T2(1,_Kt,_w))),_);});break;case 1:return new F(function(){return _Kj(B(_n(_Kr,_Ks.a)),_);});break;default:return new F(function(){return _Kj(_Kr,_);});}},_Ku=new T0(2),_Kv=function(_Kw){return new T0(2);},_Kx=function(_Ky,_Kz,_KA){return function(_){var _KB=E(_Ky),_KC=rMV(_KB),_KD=E(_KC);if(!_KD._){var _KE=new T(function(){var _KF=new T(function(){return B(A1(_KA,_m4));});return B(_n(_KD.b,new T2(1,new T2(0,_Kz,function(_KG){return E(_KF);}),_w)));}),_=wMV(_KB,new T2(0,_KD.a,_KE));return _Ku;}else{var _KH=E(_KD.a);if(!_KH._){var _=wMV(_KB,new T2(0,_Kz,_w));return new T(function(){return B(A1(_KA,_m4));});}else{var _=wMV(_KB,new T1(1,_KH.b));return new T1(1,new T2(1,new T(function(){return B(A1(_KA,_m4));}),new T2(1,new T(function(){return B(A2(_KH.a,_Kz,_Kv));}),_w)));}}};},_KI=new T(function(){return E(_IN);}),_KJ=new T(function(){return eval("window.requestAnimationFrame");}),_KK=new T1(1,_w),_KL=function(_KM,_KN){return function(_){var _KO=E(_KM),_KP=rMV(_KO),_KQ=E(_KP);if(!_KQ._){var _KR=_KQ.a,_KS=E(_KQ.b);if(!_KS._){var _=wMV(_KO,_KK);return new T(function(){return B(A1(_KN,_KR));});}else{var _KT=E(_KS.a),_=wMV(_KO,new T2(0,_KT.a,_KS.b));return new T1(1,new T2(1,new T(function(){return B(A1(_KN,_KR));}),new T2(1,new T(function(){return B(A1(_KT.b,_Kv));}),_w)));}}else{var _KU=new T(function(){var _KV=function(_KW){var _KX=new T(function(){return B(A1(_KN,_KW));});return function(_KY){return E(_KX);};};return B(_n(_KQ.a,new T2(1,_KV,_w)));}),_=wMV(_KO,new T1(1,_KU));return _Ku;}};},_KZ=function(_L0,_L1){return new T1(0,B(_KL(_L0,_L1)));},_L2=function(_L3,_L4){var _L5=new T(function(){return new T1(0,B(_Kx(_L3,_m4,_Kv)));});return function(_){var _L6=__createJSFunc(2,function(_L7,_){var _L8=B(_Kp(_L5,_w,_));return _KI;}),_L9=__app1(E(_KJ),_L6);return new T(function(){return B(_KZ(_L3,_L4));});};},_La=new T1(1,_w),_Lb=function(_Lc,_Ld,_){var _Le=function(_){var _Lf=nMV(_Lc),_Lg=_Lf;return new T(function(){var _Lh=new T(function(){return B(_Li(_));}),_Lj=function(_){var _Lk=rMV(_Lg),_Ll=B(A2(_Ld,_Lk,_)),_=wMV(_Lg,_Ll),_Lm=function(_){var _Ln=nMV(_La);return new T(function(){return new T1(0,B(_L2(_Ln,function(_Lo){return E(_Lh);})));});};return new T1(0,_Lm);},_Lp=new T(function(){return new T1(0,_Lj);}),_Li=function(_Lq){return E(_Lp);};return B(_Li(_));});};return new F(function(){return _Kp(new T1(0,_Le),_w,_);});},_Lr=new T(function(){return eval("__strict(setBounds)");}),_Ls=function(_){var _Lt=__app3(E(_lt),E(_lu),E(_lX),E(_ls)),_Lu=__app2(E(_Lr),E(_iI),E(_iF));return new F(function(){return _Lb(_Ki,_I2,_);});},_Lv=function(_){return new F(function(){return _Ls(_);});};
var hasteMain = function() {B(A(_Lv, [0]));};window.onload = hasteMain;