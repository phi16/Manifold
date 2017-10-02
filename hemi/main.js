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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(","));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("Math.pow("));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr(")"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=function(_G,_H){return new T1(1,new T2(1,_B,new T2(1,_G,new T2(1,_z,new T2(1,_H,_E)))));},_I=new T(function(){return B(unCStr("Math.acos("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_E)));},_M=new T(function(){return B(unCStr("Math.acosh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_E)));},_Q=new T(function(){return B(unCStr("Math.asin("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_E)));},_U=new T(function(){return B(unCStr("Math.asinh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_E)));},_Y=new T(function(){return B(unCStr("Math.atan("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_E)));},_12=new T(function(){return B(unCStr("Math.atanh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_E)));},_16=new T(function(){return B(unCStr("Math.cos("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_E)));},_1a=new T(function(){return B(unCStr("Math.cosh("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_E)));},_1e=new T(function(){return B(unCStr("Math.exp("));}),_1f=new T1(0,_1e),_1g=function(_1h){return new T1(1,new T2(1,_1f,new T2(1,_1h,_E)));},_1i=new T(function(){return B(unCStr("Math.log("));}),_1j=new T1(0,_1i),_1k=function(_1l){return new T1(1,new T2(1,_1j,new T2(1,_1l,_E)));},_1m=new T(function(){return B(unCStr(")/Math.log("));}),_1n=new T1(0,_1m),_1o=function(_1p,_1q){return new T1(1,new T2(1,_1j,new T2(1,_1q,new T2(1,_1n,new T2(1,_1p,_E)))));},_1r=new T(function(){return B(unCStr("Math.PI"));}),_1s=new T1(0,_1r),_1t=new T(function(){return B(unCStr("Math.sin("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_E)));},_1x=new T(function(){return B(unCStr("Math.sinh("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_E)));},_1B=new T(function(){return B(unCStr("Math.sqrt("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_E)));},_1F=new T(function(){return B(unCStr("Math.tan("));}),_1G=new T1(0,_1F),_1H=function(_1I){return new T1(1,new T2(1,_1G,new T2(1,_1I,_E)));},_1J=new T(function(){return B(unCStr("Math.tanh("));}),_1K=new T1(0,_1J),_1L=function(_1M){return new T1(1,new T2(1,_1K,new T2(1,_1M,_E)));},_1N=new T(function(){return B(unCStr("("));}),_1O=new T1(0,_1N),_1P=new T(function(){return B(unCStr(")/("));}),_1Q=new T1(0,_1P),_1R=function(_1S,_1T){return new T1(1,new T2(1,_1O,new T2(1,_1S,new T2(1,_1Q,new T2(1,_1T,_E)))));},_1U=new T1(0,1),_1V=function(_1W,_1X){var _1Y=E(_1W);if(!_1Y._){var _1Z=_1Y.a,_20=E(_1X);if(!_20._){var _21=_20.a;return (_1Z!=_21)?(_1Z>_21)?2:0:1;}else{var _22=I_compareInt(_20.a,_1Z);return (_22<=0)?(_22>=0)?1:2:0;}}else{var _23=_1Y.a,_24=E(_1X);if(!_24._){var _25=I_compareInt(_23,_24.a);return (_25>=0)?(_25<=0)?1:2:0;}else{var _26=I_compare(_23,_24.a);return (_26>=0)?(_26<=0)?1:2:0;}}},_27=new T(function(){return B(unCStr("base"));}),_28=new T(function(){return B(unCStr("GHC.Exception"));}),_29=new T(function(){return B(unCStr("ArithException"));}),_2a=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_27,_28,_29),_2b=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2a,_w,_w),_2c=function(_2d){return E(_2b);},_2e=function(_2f){return E(E(_2f).a);},_2g=function(_2h,_2i,_2j){var _2k=B(A1(_2h,_)),_2l=B(A1(_2i,_)),_2m=hs_eqWord64(_2k.a,_2l.a);if(!_2m){return __Z;}else{var _2n=hs_eqWord64(_2k.b,_2l.b);return (!_2n)?__Z:new T1(1,_2j);}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _2g(B(_2e(_2q.a)),_2c,_2q.b);});},_2r=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2s=new T(function(){return B(unCStr("denormal"));}),_2t=new T(function(){return B(unCStr("divide by zero"));}),_2u=new T(function(){return B(unCStr("loss of precision"));}),_2v=new T(function(){return B(unCStr("arithmetic underflow"));}),_2w=new T(function(){return B(unCStr("arithmetic overflow"));}),_2x=function(_2y,_2z){switch(E(_2y)){case 0:return new F(function(){return _n(_2w,_2z);});break;case 1:return new F(function(){return _n(_2v,_2z);});break;case 2:return new F(function(){return _n(_2u,_2z);});break;case 3:return new F(function(){return _n(_2t,_2z);});break;case 4:return new F(function(){return _n(_2s,_2z);});break;default:return new F(function(){return _n(_2r,_2z);});}},_2A=function(_2B){return new F(function(){return _2x(_2B,_w);});},_2C=function(_2D,_2E,_2F){return new F(function(){return _2x(_2E,_2F);});},_2G=44,_2H=93,_2I=91,_2J=function(_2K,_2L,_2M){var _2N=E(_2L);if(!_2N._){return new F(function(){return unAppCStr("[]",_2M);});}else{var _2O=new T(function(){var _2P=new T(function(){var _2Q=function(_2R){var _2S=E(_2R);if(!_2S._){return E(new T2(1,_2H,_2M));}else{var _2T=new T(function(){return B(A2(_2K,_2S.a,new T(function(){return B(_2Q(_2S.b));})));});return new T2(1,_2G,_2T);}};return B(_2Q(_2N.b));});return B(A2(_2K,_2N.a,_2P));});return new T2(1,_2I,_2O);}},_2U=function(_2V,_2W){return new F(function(){return _2J(_2x,_2V,_2W);});},_2X=new T3(0,_2C,_2A,_2U),_2Y=new T(function(){return new T5(0,_2c,_2X,_2Z,_2o,_2A);}),_2Z=function(_30){return new T2(0,_2Y,_30);},_31=3,_32=new T(function(){return B(_2Z(_31));}),_33=new T(function(){return die(_32);}),_34=function(_35,_36){var _37=E(_35);return (_37._==0)?_37.a*Math.pow(2,_36):I_toNumber(_37.a)*Math.pow(2,_36);},_38=function(_39,_3a){var _3b=E(_39);if(!_3b._){var _3c=_3b.a,_3d=E(_3a);return (_3d._==0)?_3c==_3d.a:(I_compareInt(_3d.a,_3c)==0)?true:false;}else{var _3e=_3b.a,_3f=E(_3a);return (_3f._==0)?(I_compareInt(_3e,_3f.a)==0)?true:false:(I_compare(_3e,_3f.a)==0)?true:false;}},_3g=function(_3h){var _3i=E(_3h);if(!_3i._){return E(_3i.a);}else{return new F(function(){return I_toInt(_3i.a);});}},_3j=function(_3k,_3l){while(1){var _3m=E(_3k);if(!_3m._){var _3n=_3m.a,_3o=E(_3l);if(!_3o._){var _3p=_3o.a,_3q=addC(_3n,_3p);if(!E(_3q.b)){return new T1(0,_3q.a);}else{_3k=new T1(1,I_fromInt(_3n));_3l=new T1(1,I_fromInt(_3p));continue;}}else{_3k=new T1(1,I_fromInt(_3n));_3l=_3o;continue;}}else{var _3r=E(_3l);if(!_3r._){_3k=_3m;_3l=new T1(1,I_fromInt(_3r.a));continue;}else{return new T1(1,I_add(_3m.a,_3r.a));}}}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){var _3w=E(_3v.a);if(_3w==(-2147483648)){_3t=new T1(1,I_fromInt(-2147483648));continue;}else{var _3x=E(_3u);if(!_3x._){var _3y=_3x.a;return new T2(0,new T1(0,quot(_3w,_3y)),new T1(0,_3w%_3y));}else{_3t=new T1(1,I_fromInt(_3w));_3u=_3x;continue;}}}else{var _3z=E(_3u);if(!_3z._){_3t=_3v;_3u=new T1(1,I_fromInt(_3z.a));continue;}else{var _3A=I_quotRem(_3v.a,_3z.a);return new T2(0,new T1(1,_3A.a),new T1(1,_3A.b));}}}},_3B=new T1(0,0),_3C=function(_3D,_3E){while(1){var _3F=E(_3D);if(!_3F._){_3D=new T1(1,I_fromInt(_3F.a));continue;}else{return new T1(1,I_shiftLeft(_3F.a,_3E));}}},_3G=function(_3H,_3I,_3J){if(!B(_38(_3J,_3B))){var _3K=B(_3s(_3I,_3J)),_3L=_3K.a;switch(B(_1V(B(_3C(_3K.b,1)),_3J))){case 0:return new F(function(){return _34(_3L,_3H);});break;case 1:if(!(B(_3g(_3L))&1)){return new F(function(){return _34(_3L,_3H);});}else{return new F(function(){return _34(B(_3j(_3L,_1U)),_3H);});}break;default:return new F(function(){return _34(B(_3j(_3L,_1U)),_3H);});}}else{return E(_33);}},_3M=function(_3N,_3O){var _3P=E(_3N);if(!_3P._){var _3Q=_3P.a,_3R=E(_3O);return (_3R._==0)?_3Q>_3R.a:I_compareInt(_3R.a,_3Q)<0;}else{var _3S=_3P.a,_3T=E(_3O);return (_3T._==0)?I_compareInt(_3S,_3T.a)>0:I_compare(_3S,_3T.a)>0;}},_3U=new T1(0,1),_3V=function(_3W,_3X){var _3Y=E(_3W);if(!_3Y._){var _3Z=_3Y.a,_40=E(_3X);return (_40._==0)?_3Z<_40.a:I_compareInt(_40.a,_3Z)>0;}else{var _41=_3Y.a,_42=E(_3X);return (_42._==0)?I_compareInt(_41,_42.a)<0:I_compare(_41,_42.a)<0;}},_43=new T(function(){return B(unCStr("base"));}),_44=new T(function(){return B(unCStr("Control.Exception.Base"));}),_45=new T(function(){return B(unCStr("PatternMatchFail"));}),_46=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_43,_44,_45),_47=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_46,_w,_w),_48=function(_49){return E(_47);},_4a=function(_4b){var _4c=E(_4b);return new F(function(){return _2g(B(_2e(_4c.a)),_48,_4c.b);});},_4d=function(_4e){return E(E(_4e).a);},_4f=function(_4g){return new T2(0,_4h,_4g);},_4i=function(_4j,_4k){return new F(function(){return _n(E(_4j).a,_4k);});},_4l=function(_4m,_4n){return new F(function(){return _2J(_4i,_4m,_4n);});},_4o=function(_4p,_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=new T3(0,_4o,_4d,_4l),_4h=new T(function(){return new T5(0,_48,_4s,_4f,_4a,_4d);}),_4t=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4u=function(_4v){return E(E(_4v).c);},_4w=function(_4x,_4y){return new F(function(){return die(new T(function(){return B(A2(_4u,_4y,_4x));}));});},_4z=function(_4A,_30){return new F(function(){return _4w(_4A,_30);});},_4B=function(_4C,_4D){var _4E=E(_4D);if(!_4E._){return new T2(0,_w,_w);}else{var _4F=_4E.a;if(!B(A1(_4C,_4F))){return new T2(0,_w,_4E);}else{var _4G=new T(function(){var _4H=B(_4B(_4C,_4E.b));return new T2(0,_4H.a,_4H.b);});return new T2(0,new T2(1,_4F,new T(function(){return E(E(_4G).a);})),new T(function(){return E(E(_4G).b);}));}}},_4I=32,_4J=new T(function(){return B(unCStr("\n"));}),_4K=function(_4L){return (E(_4L)==124)?false:true;},_4M=function(_4N,_4O){var _4P=B(_4B(_4K,B(unCStr(_4N)))),_4Q=_4P.a,_4R=function(_4S,_4T){var _4U=new T(function(){var _4V=new T(function(){return B(_n(_4O,new T(function(){return B(_n(_4T,_4J));},1)));});return B(unAppCStr(": ",_4V));},1);return new F(function(){return _n(_4S,_4U);});},_4W=E(_4P.b);if(!_4W._){return new F(function(){return _4R(_4Q,_w);});}else{if(E(_4W.a)==124){return new F(function(){return _4R(_4Q,new T2(1,_4I,_4W.b));});}else{return new F(function(){return _4R(_4Q,_w);});}}},_4X=function(_4Y){return new F(function(){return _4z(new T1(0,new T(function(){return B(_4M(_4Y,_4t));})),_4h);});},_4Z=function(_50){var _51=function(_52,_53){while(1){if(!B(_3V(_52,_50))){if(!B(_3M(_52,_50))){if(!B(_38(_52,_50))){return new F(function(){return _4X("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_53);}}else{return _53-1|0;}}else{var _54=B(_3C(_52,1)),_55=_53+1|0;_52=_54;_53=_55;continue;}}};return new F(function(){return _51(_3U,0);});},_56=function(_57){var _58=E(_57);if(!_58._){var _59=_58.a>>>0;if(!_59){return -1;}else{var _5a=function(_5b,_5c){while(1){if(_5b>=_59){if(_5b<=_59){if(_5b!=_59){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5c);}}else{return _5c-1|0;}}else{var _5d=imul(_5b,2)>>>0,_5e=_5c+1|0;_5b=_5d;_5c=_5e;continue;}}};return new F(function(){return _5a(1,0);});}}else{return new F(function(){return _4Z(_58);});}},_5f=function(_5g){var _5h=E(_5g);if(!_5h._){var _5i=_5h.a>>>0;if(!_5i){return new T2(0,-1,0);}else{var _5j=function(_5k,_5l){while(1){if(_5k>=_5i){if(_5k<=_5i){if(_5k!=_5i){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5l);}}else{return _5l-1|0;}}else{var _5m=imul(_5k,2)>>>0,_5n=_5l+1|0;_5k=_5m;_5l=_5n;continue;}}};return new T2(0,B(_5j(1,0)),(_5i&_5i-1>>>0)>>>0&4294967295);}}else{var _5o=_5h.a;return new T2(0,B(_56(_5h)),I_compareInt(I_and(_5o,I_sub(_5o,I_fromInt(1))),0));}},_5p=function(_5q,_5r){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);return (_5u._==0)?_5t<=_5u.a:I_compareInt(_5u.a,_5t)>=0;}else{var _5v=_5s.a,_5w=E(_5r);return (_5w._==0)?I_compareInt(_5v,_5w.a)<=0:I_compare(_5v,_5w.a)<=0;}},_5x=function(_5y,_5z){while(1){var _5A=E(_5y);if(!_5A._){var _5B=_5A.a,_5C=E(_5z);if(!_5C._){return new T1(0,(_5B>>>0&_5C.a>>>0)>>>0&4294967295);}else{_5y=new T1(1,I_fromInt(_5B));_5z=_5C;continue;}}else{var _5D=E(_5z);if(!_5D._){_5y=_5A;_5z=new T1(1,I_fromInt(_5D.a));continue;}else{return new T1(1,I_and(_5A.a,_5D.a));}}}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){var _5K=_5J.a,_5L=subC(_5I,_5K);if(!E(_5L.b)){return new T1(0,_5L.a);}else{_5F=new T1(1,I_fromInt(_5I));_5G=new T1(1,I_fromInt(_5K));continue;}}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5M=E(_5G);if(!_5M._){_5F=_5H;_5G=new T1(1,I_fromInt(_5M.a));continue;}else{return new T1(1,I_sub(_5H.a,_5M.a));}}}},_5N=new T1(0,2),_5O=function(_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=(_5R.a>>>0&(2<<_5Q>>>0)-1>>>0)>>>0,_5T=1<<_5Q>>>0;return (_5T<=_5S)?(_5T>=_5S)?1:2:0;}else{var _5U=B(_5x(_5R,B(_5E(B(_3C(_5N,_5Q)),_3U)))),_5V=B(_3C(_3U,_5Q));return (!B(_3M(_5V,_5U)))?(!B(_3V(_5V,_5U)))?1:2:0;}},_5W=function(_5X,_5Y){while(1){var _5Z=E(_5X);if(!_5Z._){_5X=new T1(1,I_fromInt(_5Z.a));continue;}else{return new T1(1,I_shiftRight(_5Z.a,_5Y));}}},_60=function(_61,_62,_63,_64){var _65=B(_5f(_64)),_66=_65.a;if(!E(_65.b)){var _67=B(_56(_63));if(_67<((_66+_61|0)-1|0)){var _68=_66+(_61-_62|0)|0;if(_68>0){if(_68>_67){if(_68<=(_67+1|0)){if(!E(B(_5f(_63)).b)){return 0;}else{return new F(function(){return _34(_1U,_61-_62|0);});}}else{return 0;}}else{var _69=B(_5W(_63,_68));switch(B(_5O(_63,_68-1|0))){case 0:return new F(function(){return _34(_69,_61-_62|0);});break;case 1:if(!(B(_3g(_69))&1)){return new F(function(){return _34(_69,_61-_62|0);});}else{return new F(function(){return _34(B(_3j(_69,_1U)),_61-_62|0);});}break;default:return new F(function(){return _34(B(_3j(_69,_1U)),_61-_62|0);});}}}else{return new F(function(){return _34(_63,(_61-_62|0)-_68|0);});}}else{if(_67>=_62){var _6a=B(_5W(_63,(_67+1|0)-_62|0));switch(B(_5O(_63,_67-_62|0))){case 0:return new F(function(){return _34(_6a,((_67-_66|0)+1|0)-_62|0);});break;case 2:return new F(function(){return _34(B(_3j(_6a,_1U)),((_67-_66|0)+1|0)-_62|0);});break;default:if(!(B(_3g(_6a))&1)){return new F(function(){return _34(_6a,((_67-_66|0)+1|0)-_62|0);});}else{return new F(function(){return _34(B(_3j(_6a,_1U)),((_67-_66|0)+1|0)-_62|0);});}}}else{return new F(function(){return _34(_63, -_66);});}}}else{var _6b=B(_56(_63))-_66|0,_6c=function(_6d){var _6e=function(_6f,_6g){if(!B(_5p(B(_3C(_6g,_62)),_6f))){return new F(function(){return _3G(_6d-_62|0,_6f,_6g);});}else{return new F(function(){return _3G((_6d-_62|0)+1|0,_6f,B(_3C(_6g,1)));});}};if(_6d>=_62){if(_6d!=_62){return new F(function(){return _6e(_63,new T(function(){return B(_3C(_64,_6d-_62|0));}));});}else{return new F(function(){return _6e(_63,_64);});}}else{return new F(function(){return _6e(new T(function(){return B(_3C(_63,_62-_6d|0));}),_64);});}};if(_61>_6b){return new F(function(){return _6c(_61);});}else{return new F(function(){return _6c(_6b);});}}},_6h=new T1(0,2147483647),_6i=new T(function(){return B(_3j(_6h,_3U));}),_6j=function(_6k){var _6l=E(_6k);if(!_6l._){var _6m=E(_6l.a);return (_6m==(-2147483648))?E(_6i):new T1(0, -_6m);}else{return new T1(1,I_negate(_6l.a));}},_6n=new T(function(){return 0/0;}),_6o=new T(function(){return -1/0;}),_6p=new T(function(){return 1/0;}),_6q=0,_6r=function(_6s,_6t){if(!B(_38(_6t,_3B))){if(!B(_38(_6s,_3B))){if(!B(_3V(_6s,_3B))){return new F(function(){return _60(-1021,53,_6s,_6t);});}else{return  -B(_60(-1021,53,B(_6j(_6s)),_6t));}}else{return E(_6q);}}else{return (!B(_38(_6s,_3B)))?(!B(_3V(_6s,_3B)))?E(_6p):E(_6o):E(_6n);}},_6u=function(_6v){return new T1(0,new T(function(){var _6w=E(_6v),_6x=jsShow(B(_6r(_6w.a,_6w.b)));return fromJSStr(_6x);}));},_6y=new T(function(){return B(unCStr("1/("));}),_6z=new T1(0,_6y),_6A=function(_6B){return new T1(1,new T2(1,_6z,new T2(1,_6B,_E)));},_6C=new T(function(){return B(unCStr(")+("));}),_6D=new T1(0,_6C),_6E=function(_6F,_6G){return new T1(1,new T2(1,_1O,new T2(1,_6F,new T2(1,_6D,new T2(1,_6G,_E)))));},_6H=new T(function(){return B(unCStr("-("));}),_6I=new T1(0,_6H),_6J=function(_6K){return new T1(1,new T2(1,_6I,new T2(1,_6K,_E)));},_6L=new T(function(){return B(unCStr(")*("));}),_6M=new T1(0,_6L),_6N=function(_6O,_6P){return new T1(1,new T2(1,_1O,new T2(1,_6O,new T2(1,_6M,new T2(1,_6P,_E)))));},_6Q=function(_6R){return E(E(_6R).a);},_6S=function(_6T){return E(E(_6T).d);},_6U=function(_6V,_6W){return new F(function(){return A3(_6Q,_6X,_6V,new T(function(){return B(A2(_6S,_6X,_6W));}));});},_6Y=new T(function(){return B(unCStr("Math.abs("));}),_6Z=new T1(0,_6Y),_70=function(_71){return new T1(1,new T2(1,_6Z,new T2(1,_71,_E)));},_72=function(_73){while(1){var _74=E(_73);if(!_74._){_73=new T1(1,I_fromInt(_74.a));continue;}else{return new F(function(){return I_toString(_74.a);});}}},_75=function(_76,_77){return new F(function(){return _n(fromJSStr(B(_72(_76))),_77);});},_78=41,_79=40,_7a=new T1(0,0),_7b=function(_7c,_7d,_7e){if(_7c<=6){return new F(function(){return _75(_7d,_7e);});}else{if(!B(_3V(_7d,_7a))){return new F(function(){return _75(_7d,_7e);});}else{return new T2(1,_79,new T(function(){return B(_n(fromJSStr(B(_72(_7d))),new T2(1,_78,_7e)));}));}}},_7f=new T(function(){return B(unCStr("."));}),_7g=function(_7h){return new T1(0,new T(function(){return B(_n(B(_7b(0,_7h,_w)),_7f));}));},_7i=new T(function(){return B(unCStr("Math.sign("));}),_7j=new T1(0,_7i),_7k=function(_7l){return new T1(1,new T2(1,_7j,new T2(1,_7l,_E)));},_6X=new T(function(){return {_:0,a:_6E,b:_6U,c:_6N,d:_6J,e:_70,f:_7k,g:_7g};}),_7m=new T4(0,_6X,_1R,_6A,_6u),_7n={_:0,a:_7m,b:_1s,c:_1g,d:_1k,e:_1D,f:_F,g:_1o,h:_1v,i:_18,j:_1H,k:_S,l:_K,m:_10,n:_1z,o:_1c,p:_1L,q:_W,r:_O,s:_14},_7o=function(_7p,_7q){var _7r=E(_7p);return E(_7q);},_7s=function(_7t,_7u){var _7v=E(_7u);return E(_7t);},_7w=function(_7x,_7y){var _7z=E(_7x),_7A=E(_7y);return new T3(0,E(B(A1(_7z.a,_7A.a))),E(B(A1(_7z.b,_7A.b))),E(B(A1(_7z.c,_7A.c))));},_7B=function(_7C,_7D,_7E){return new T3(0,E(_7C),E(_7D),E(_7E));},_7F=function(_7G){return new F(function(){return _7B(_7G,_7G,_7G);});},_7H=function(_7I,_7J){var _7K=E(_7J),_7L=E(_7I);return new T3(0,E(_7L),E(_7L),E(_7L));},_7M=function(_7N,_7O){var _7P=E(_7O);return new T3(0,E(B(A1(_7N,_7P.a))),E(B(A1(_7N,_7P.b))),E(B(A1(_7N,_7P.c))));},_7Q=new T2(0,_7M,_7H),_7R=new T5(0,_7Q,_7F,_7w,_7o,_7s),_7S=new T1(0,0),_7T=new T1(0,1),_7U=function(_7V){return E(E(_7V).g);},_7W=function(_7X){var _7Y=B(A2(_7U,_7X,_7T)),_7Z=B(A2(_7U,_7X,_7S));return new T3(0,E(new T3(0,E(_7Y),E(_7Z),E(_7Z))),E(new T3(0,E(_7Z),E(_7Y),E(_7Z))),E(new T3(0,E(_7Z),E(_7Z),E(_7Y))));},_80=function(_81){return E(E(_81).a);},_82=function(_83){return E(E(_83).a);},_84=function(_85){return E(E(_85).a);},_86=function(_87){return E(E(_87).a);},_88=function(_89,_8a,_8b){var _8c=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_89).c).a);})));})));}),_8d=new T(function(){return B(A3(_86,B(_84(E(_89).a)),new T(function(){return B(_6S(_8c));}),_8b));});return new T2(0,new T(function(){return B(A2(_6S,_8c,_8a));}),_8d);},_8e=function(_8f){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_8f));}))));});},_8g=new T(function(){return B(_8e("ww_s4CO Ord a"));}),_8h=function(_8i,_8j,_8k,_8l){var _8m=new T(function(){return B(_82(new T(function(){return B(_80(_8i));})));}),_8n=B(A2(_7U,_8m,_7S));return E(B(_88(new T3(0,_7R,_7W,new T2(0,_8i,_8g)),_8k,new T3(0,E(_8n),E(B(A2(_7U,_8m,_7T))),E(_8n)))).b);},_8o=new T(function(){return B(unCStr("x"));}),_8p=new T1(0,_8o),_8q=new T(function(){return B(unCStr("y"));}),_8r=new T1(0,_8q),_8s=new T(function(){return B(unCStr("z"));}),_8t=new T1(0,_8s),_8u=new T(function(){return B(_8h(_7n,_8p,_8r,_8t));}),_8v=new T(function(){return E(E(_8u).a);}),_8w=new T(function(){return B(unCStr(",y:"));}),_8x=new T1(0,_8w),_8y=new T(function(){return E(E(_8u).b);}),_8z=new T(function(){return B(unCStr(",z:"));}),_8A=new T1(0,_8z),_8B=new T(function(){return E(E(_8u).c);}),_8C=new T(function(){return B(unCStr("})"));}),_8D=new T1(0,_8C),_8E=new T2(1,_8D,_w),_8F=new T2(1,_8B,_8E),_8G=new T2(1,_8A,_8F),_8H=new T2(1,_8y,_8G),_8I=new T2(1,_8x,_8H),_8J=new T2(1,_8v,_8I),_8K=new T(function(){return B(unCStr("({x:"));}),_8L=new T1(0,_8K),_8M=new T2(1,_8L,_8J),_8N=function(_8O){return E(_8O);},_8P=new T(function(){return toJSStr(B(_e(_x,_8N,_8M)));}),_8Q=new T2(1,_8r,_E),_8R=new T2(1,_6I,_8Q),_8S=new T(function(){return toJSStr(B(_e(_x,_8N,_8R)));}),_8T=function(_8U,_8V,_8W){var _8X=E(_8W);if(!_8X._){return new F(function(){return A1(_8V,_8X.a);});}else{var _8Y=new T(function(){return B(_0(_8U));}),_8Z=new T(function(){return B(_2(_8U));}),_90=function(_91){var _92=E(_91);if(!_92._){return E(_8Z);}else{return new F(function(){return A2(_8Y,new T(function(){return B(_8T(_8U,_8V,_92.a));}),new T(function(){return B(_90(_92.b));}));});}};return new F(function(){return _90(_8X.a);});}},_93=function(_94,_95,_96){var _97=new T(function(){return B(_0(_94));}),_98=new T(function(){return B(_2(_94));}),_99=function(_9a){var _9b=E(_9a);if(!_9b._){return E(_98);}else{return new F(function(){return A2(_97,new T(function(){return B(_8T(_94,_95,_9b.a));}),new T(function(){return B(_99(_9b.b));}));});}};return new F(function(){return _99(_96);});},_9c=new T(function(){return B(unCStr("-("));}),_9d=new T1(0,_9c),_9e=new T(function(){return B(unCStr(")"));}),_9f=new T1(0,_9e),_9g=new T2(1,_9f,_w),_9h=new T(function(){return B(unCStr("y"));}),_9i=new T1(0,_9h),_9j=new T2(1,_9i,_9g),_9k=new T2(1,_9d,_9j),_9l=new T(function(){return toJSStr(B(_93(_x,_8N,_9k)));}),_9m=new T(function(){return eval("__strict(compile)");}),_9n=new T(function(){return B(unCStr(","));}),_9o=new T1(0,_9n),_9p=new T(function(){return B(unCStr("pow("));}),_9q=new T1(0,_9p),_9r=function(_9s,_9t){return new T1(1,new T2(1,_9q,new T2(1,_9s,new T2(1,_9o,new T2(1,_9t,_9g)))));},_9u=new T(function(){return B(unCStr("acos("));}),_9v=new T1(0,_9u),_9w=function(_9x){return new T1(1,new T2(1,_9v,new T2(1,_9x,_9g)));},_9y=new T(function(){return B(unCStr("acosh("));}),_9z=new T1(0,_9y),_9A=function(_9B){return new T1(1,new T2(1,_9z,new T2(1,_9B,_9g)));},_9C=new T(function(){return B(unCStr("asin("));}),_9D=new T1(0,_9C),_9E=function(_9F){return new T1(1,new T2(1,_9D,new T2(1,_9F,_9g)));},_9G=new T(function(){return B(unCStr("asinh("));}),_9H=new T1(0,_9G),_9I=function(_9J){return new T1(1,new T2(1,_9H,new T2(1,_9J,_9g)));},_9K=new T(function(){return B(unCStr("atan("));}),_9L=new T1(0,_9K),_9M=function(_9N){return new T1(1,new T2(1,_9L,new T2(1,_9N,_9g)));},_9O=new T(function(){return B(unCStr("atanh("));}),_9P=new T1(0,_9O),_9Q=function(_9R){return new T1(1,new T2(1,_9P,new T2(1,_9R,_9g)));},_9S=new T(function(){return B(unCStr("cos("));}),_9T=new T1(0,_9S),_9U=function(_9V){return new T1(1,new T2(1,_9T,new T2(1,_9V,_9g)));},_9W=new T(function(){return B(unCStr("cosh("));}),_9X=new T1(0,_9W),_9Y=function(_9Z){return new T1(1,new T2(1,_9X,new T2(1,_9Z,_9g)));},_a0=new T(function(){return B(unCStr("exp("));}),_a1=new T1(0,_a0),_a2=function(_a3){return new T1(1,new T2(1,_a1,new T2(1,_a3,_9g)));},_a4=new T(function(){return B(unCStr("log("));}),_a5=new T1(0,_a4),_a6=function(_a7){return new T1(1,new T2(1,_a5,new T2(1,_a7,_9g)));},_a8=new T(function(){return B(unCStr(")/log("));}),_a9=new T1(0,_a8),_aa=function(_ab,_ac){return new T1(1,new T2(1,_a5,new T2(1,_ac,new T2(1,_a9,new T2(1,_ab,_9g)))));},_ad=new T(function(){return B(unCStr("pi"));}),_ae=new T1(0,_ad),_af=new T(function(){return B(unCStr("sin("));}),_ag=new T1(0,_af),_ah=function(_ai){return new T1(1,new T2(1,_ag,new T2(1,_ai,_9g)));},_aj=new T(function(){return B(unCStr("sinh("));}),_ak=new T1(0,_aj),_al=function(_am){return new T1(1,new T2(1,_ak,new T2(1,_am,_9g)));},_an=new T(function(){return B(unCStr("sqrt("));}),_ao=new T1(0,_an),_ap=function(_aq){return new T1(1,new T2(1,_ao,new T2(1,_aq,_9g)));},_ar=new T(function(){return B(unCStr("tan("));}),_as=new T1(0,_ar),_at=function(_au){return new T1(1,new T2(1,_as,new T2(1,_au,_9g)));},_av=new T(function(){return B(unCStr("tanh("));}),_aw=new T1(0,_av),_ax=function(_ay){return new T1(1,new T2(1,_aw,new T2(1,_ay,_9g)));},_az=new T(function(){return B(unCStr("("));}),_aA=new T1(0,_az),_aB=new T(function(){return B(unCStr(")/("));}),_aC=new T1(0,_aB),_aD=function(_aE,_aF){return new T1(1,new T2(1,_aA,new T2(1,_aE,new T2(1,_aC,new T2(1,_aF,_9g)))));},_aG=function(_aH){return new T1(0,new T(function(){var _aI=E(_aH),_aJ=jsShow(B(_6r(_aI.a,_aI.b)));return fromJSStr(_aJ);}));},_aK=new T(function(){return B(unCStr("1./("));}),_aL=new T1(0,_aK),_aM=function(_aN){return new T1(1,new T2(1,_aL,new T2(1,_aN,_9g)));},_aO=new T(function(){return B(unCStr(")+("));}),_aP=new T1(0,_aO),_aQ=function(_aR,_aS){return new T1(1,new T2(1,_aA,new T2(1,_aR,new T2(1,_aP,new T2(1,_aS,_9g)))));},_aT=function(_aU){return new T1(1,new T2(1,_9d,new T2(1,_aU,_9g)));},_aV=new T(function(){return B(unCStr(")*("));}),_aW=new T1(0,_aV),_aX=function(_aY,_aZ){return new T1(1,new T2(1,_aA,new T2(1,_aY,new T2(1,_aW,new T2(1,_aZ,_9g)))));},_b0=function(_b1,_b2){return new F(function(){return A3(_6Q,_b3,_b1,new T(function(){return B(A2(_6S,_b3,_b2));}));});},_b4=new T(function(){return B(unCStr("abs("));}),_b5=new T1(0,_b4),_b6=function(_b7){return new T1(1,new T2(1,_b5,new T2(1,_b7,_9g)));},_b8=new T(function(){return B(unCStr("."));}),_b9=function(_ba){return new T1(0,new T(function(){return B(_n(B(_7b(0,_ba,_w)),_b8));}));},_bb=new T(function(){return B(unCStr("sign("));}),_bc=new T1(0,_bb),_bd=function(_be){return new T1(1,new T2(1,_bc,new T2(1,_be,_9g)));},_b3=new T(function(){return {_:0,a:_aQ,b:_b0,c:_aX,d:_aT,e:_b6,f:_bd,g:_b9};}),_bf=new T4(0,_b3,_aD,_aM,_aG),_bg={_:0,a:_bf,b:_ae,c:_a2,d:_a6,e:_ap,f:_9r,g:_aa,h:_ah,i:_9U,j:_at,k:_9E,l:_9w,m:_9M,n:_al,o:_9Y,p:_ax,q:_9I,r:_9A,s:_9Q},_bh=function(_bi){return E(E(_bi).c);},_bj=function(_bk,_bl,_bm,_bn,_bo,_bp,_bq){var _br=B(_82(B(_80(_bk)))),_bs=new T(function(){return B(A3(_6Q,_br,new T(function(){return B(A3(_bh,_br,_bl,_bo));}),new T(function(){return B(A3(_bh,_br,_bm,_bp));})));});return new F(function(){return A3(_6Q,_br,_bs,new T(function(){return B(A3(_bh,_br,_bn,_bq));}));});},_bt=function(_bu){return E(E(_bu).b);},_bv=function(_bw){return E(E(_bw).e);},_bx=function(_by,_bz){var _bA=B(_82(B(_80(_by)))),_bB=new T(function(){return B(A2(_bv,_by,new T(function(){var _bC=E(_bz),_bD=_bC.a,_bE=_bC.b,_bF=_bC.c;return B(_bj(_by,_bD,_bE,_bF,_bD,_bE,_bF));})));});return new F(function(){return A3(_bt,_bA,_bB,new T(function(){return B(A2(_7U,_bA,_7T));}));});},_bG=new T(function(){return B(unCStr("x"));}),_bH=new T1(0,_bG),_bI=new T(function(){return B(unCStr("z"));}),_bJ=new T1(0,_bI),_bK=new T3(0,E(_bH),E(_9i),E(_bJ)),_bL=new T(function(){return B(_bx(_bg,_bK));}),_bM=new T(function(){return toJSStr(B(_8T(_x,_8N,_bL)));}),_bN=new T(function(){return B(unCStr("(/=) is not defined"));}),_bO=new T(function(){return B(err(_bN));}),_bP=new T(function(){return B(unCStr("(==) is not defined"));}),_bQ=new T(function(){return B(err(_bP));}),_bR=new T2(0,_bQ,_bO),_bS=new T(function(){return B(unCStr("(<) is not defined"));}),_bT=new T(function(){return B(err(_bS));}),_bU=new T(function(){return B(unCStr("(<=) is not defined"));}),_bV=new T(function(){return B(err(_bU));}),_bW=new T(function(){return B(unCStr("(>) is not defined"));}),_bX=new T(function(){return B(err(_bW));}),_bY=new T(function(){return B(unCStr("(>=) is not defined"));}),_bZ=new T(function(){return B(err(_bY));}),_c0=new T(function(){return B(unCStr("compare is not defined"));}),_c1=new T(function(){return B(err(_c0));}),_c2=new T(function(){return B(unCStr("max("));}),_c3=new T1(0,_c2),_c4=function(_c5,_c6){return new T1(1,new T2(1,_c3,new T2(1,_c5,new T2(1,_9o,new T2(1,_c6,_9g)))));},_c7=new T(function(){return B(unCStr("min("));}),_c8=new T1(0,_c7),_c9=function(_ca,_cb){return new T1(1,new T2(1,_c8,new T2(1,_ca,new T2(1,_9o,new T2(1,_cb,_9g)))));},_cc={_:0,a:_bR,b:_c1,c:_bT,d:_bV,e:_bX,f:_bZ,g:_c4,h:_c9},_cd=new T2(0,_bg,_cc),_ce=function(_cf){return E(E(_cf).f);},_cg=function(_ch){return E(E(_ch).b);},_ci=function(_cj){return E(E(_cj).c);},_ck=function(_cl){return E(E(_cl).d);},_cm=function(_cn,_co,_cp,_cq,_cr){var _cs=new T(function(){return E(E(E(_cn).c).a);}),_ct=new T(function(){var _cu=E(_cn).a,_cv=new T(function(){var _cw=new T(function(){return B(_80(_cs));}),_cx=new T(function(){return B(_82(_cw));}),_cy=new T(function(){return B(A2(_ck,_cs,_co));}),_cz=new T(function(){return B(A3(_ce,_cs,_co,_cq));}),_cA=function(_cB,_cC){var _cD=new T(function(){var _cE=new T(function(){return B(A3(_cg,_cw,new T(function(){return B(A3(_bh,_cx,_cq,_cB));}),_co));});return B(A3(_6Q,_cx,_cE,new T(function(){return B(A3(_bh,_cx,_cC,_cy));})));});return new F(function(){return A3(_bh,_cx,_cz,_cD);});};return B(A3(_86,B(_84(_cu)),_cA,_cp));});return B(A3(_ci,_cu,_cv,_cr));});return new T2(0,new T(function(){return B(A3(_ce,_cs,_co,_cq));}),_ct);},_cF=function(_cG,_cH,_cI,_cJ){var _cK=E(_cI),_cL=E(_cJ),_cM=B(_cm(_cH,_cK.a,_cK.b,_cL.a,_cL.b));return new T2(0,_cM.a,_cM.b);},_cN=new T1(0,1),_cO=function(_cP){return E(E(_cP).l);},_cQ=function(_cR,_cS,_cT){var _cU=new T(function(){return E(E(E(_cR).c).a);}),_cV=new T(function(){var _cW=new T(function(){return B(_80(_cU));}),_cX=new T(function(){var _cY=B(_82(_cW)),_cZ=new T(function(){var _d0=new T(function(){return B(A3(_bt,_cY,new T(function(){return B(A2(_7U,_cY,_cN));}),new T(function(){return B(A3(_bh,_cY,_cS,_cS));})));});return B(A2(_bv,_cU,_d0));});return B(A2(_6S,_cY,_cZ));});return B(A3(_86,B(_84(E(_cR).a)),function(_d1){return new F(function(){return A3(_cg,_cW,_d1,_cX);});},_cT));});return new T2(0,new T(function(){return B(A2(_cO,_cU,_cS));}),_cV);},_d2=function(_d3,_d4,_d5){var _d6=E(_d5),_d7=B(_cQ(_d4,_d6.a,_d6.b));return new T2(0,_d7.a,_d7.b);},_d8=function(_d9){return E(E(_d9).r);},_da=function(_db,_dc,_dd){var _de=new T(function(){return E(E(E(_db).c).a);}),_df=new T(function(){var _dg=new T(function(){return B(_80(_de));}),_dh=new T(function(){var _di=new T(function(){var _dj=B(_82(_dg));return B(A3(_bt,_dj,new T(function(){return B(A3(_bh,_dj,_dc,_dc));}),new T(function(){return B(A2(_7U,_dj,_cN));})));});return B(A2(_bv,_de,_di));});return B(A3(_86,B(_84(E(_db).a)),function(_dk){return new F(function(){return A3(_cg,_dg,_dk,_dh);});},_dd));});return new T2(0,new T(function(){return B(A2(_d8,_de,_dc));}),_df);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_da(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds){return E(E(_ds).k);},_dt=function(_du,_dv,_dw){var _dx=new T(function(){return E(E(E(_du).c).a);}),_dy=new T(function(){var _dz=new T(function(){return B(_80(_dx));}),_dA=new T(function(){var _dB=new T(function(){var _dC=B(_82(_dz));return B(A3(_bt,_dC,new T(function(){return B(A2(_7U,_dC,_cN));}),new T(function(){return B(A3(_bh,_dC,_dv,_dv));})));});return B(A2(_bv,_dx,_dB));});return B(A3(_86,B(_84(E(_du).a)),function(_dD){return new F(function(){return A3(_cg,_dz,_dD,_dA);});},_dw));});return new T2(0,new T(function(){return B(A2(_dr,_dx,_dv));}),_dy);},_dE=function(_dF,_dG,_dH){var _dI=E(_dH),_dJ=B(_dt(_dG,_dI.a,_dI.b));return new T2(0,_dJ.a,_dJ.b);},_dK=function(_dL){return E(E(_dL).q);},_dM=function(_dN,_dO,_dP){var _dQ=new T(function(){return E(E(E(_dN).c).a);}),_dR=new T(function(){var _dS=new T(function(){return B(_80(_dQ));}),_dT=new T(function(){var _dU=new T(function(){var _dV=B(_82(_dS));return B(A3(_6Q,_dV,new T(function(){return B(A3(_bh,_dV,_dO,_dO));}),new T(function(){return B(A2(_7U,_dV,_cN));})));});return B(A2(_bv,_dQ,_dU));});return B(A3(_86,B(_84(E(_dN).a)),function(_dW){return new F(function(){return A3(_cg,_dS,_dW,_dT);});},_dP));});return new T2(0,new T(function(){return B(A2(_dK,_dQ,_dO));}),_dR);},_dX=function(_dY,_dZ,_e0){var _e1=E(_e0),_e2=B(_dM(_dZ,_e1.a,_e1.b));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4){return E(E(_e4).m);},_e5=function(_e6,_e7,_e8){var _e9=new T(function(){return E(E(E(_e6).c).a);}),_ea=new T(function(){var _eb=new T(function(){return B(_80(_e9));}),_ec=new T(function(){var _ed=B(_82(_eb));return B(A3(_6Q,_ed,new T(function(){return B(A2(_7U,_ed,_cN));}),new T(function(){return B(A3(_bh,_ed,_e7,_e7));})));});return B(A3(_86,B(_84(E(_e6).a)),function(_ee){return new F(function(){return A3(_cg,_eb,_ee,_ec);});},_e8));});return new T2(0,new T(function(){return B(A2(_e3,_e9,_e7));}),_ea);},_ef=function(_eg,_eh,_ei){var _ej=E(_ei),_ek=B(_e5(_eh,_ej.a,_ej.b));return new T2(0,_ek.a,_ek.b);},_el=function(_em){return E(E(_em).s);},_en=function(_eo,_ep,_eq){var _er=new T(function(){return E(E(E(_eo).c).a);}),_es=new T(function(){var _et=new T(function(){return B(_80(_er));}),_eu=new T(function(){var _ev=B(_82(_et));return B(A3(_bt,_ev,new T(function(){return B(A2(_7U,_ev,_cN));}),new T(function(){return B(A3(_bh,_ev,_ep,_ep));})));});return B(A3(_86,B(_84(E(_eo).a)),function(_ew){return new F(function(){return A3(_cg,_et,_ew,_eu);});},_eq));});return new T2(0,new T(function(){return B(A2(_el,_er,_ep));}),_es);},_ex=function(_ey,_ez,_eA){var _eB=E(_eA),_eC=B(_en(_ez,_eB.a,_eB.b));return new T2(0,_eC.a,_eC.b);},_eD=function(_eE){return E(E(_eE).i);},_eF=function(_eG){return E(E(_eG).h);},_eH=function(_eI,_eJ,_eK){var _eL=new T(function(){return E(E(E(_eI).c).a);}),_eM=new T(function(){var _eN=new T(function(){return B(_82(new T(function(){return B(_80(_eL));})));}),_eO=new T(function(){return B(A2(_6S,_eN,new T(function(){return B(A2(_eF,_eL,_eJ));})));});return B(A3(_86,B(_84(E(_eI).a)),function(_eP){return new F(function(){return A3(_bh,_eN,_eP,_eO);});},_eK));});return new T2(0,new T(function(){return B(A2(_eD,_eL,_eJ));}),_eM);},_eQ=function(_eR,_eS,_eT){var _eU=E(_eT),_eV=B(_eH(_eS,_eU.a,_eU.b));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX){return E(E(_eX).o);},_eY=function(_eZ){return E(E(_eZ).n);},_f0=function(_f1,_f2,_f3){var _f4=new T(function(){return E(E(E(_f1).c).a);}),_f5=new T(function(){var _f6=new T(function(){return B(_82(new T(function(){return B(_80(_f4));})));}),_f7=new T(function(){return B(A2(_eY,_f4,_f2));});return B(A3(_86,B(_84(E(_f1).a)),function(_f8){return new F(function(){return A3(_bh,_f6,_f8,_f7);});},_f3));});return new T2(0,new T(function(){return B(A2(_eW,_f4,_f2));}),_f5);},_f9=function(_fa,_fb,_fc){var _fd=E(_fc),_fe=B(_f0(_fb,_fd.a,_fd.b));return new T2(0,_fe.a,_fe.b);},_ff=function(_fg){return E(E(_fg).c);},_fh=function(_fi,_fj,_fk){var _fl=new T(function(){return E(E(E(_fi).c).a);}),_fm=new T(function(){var _fn=new T(function(){return B(_82(new T(function(){return B(_80(_fl));})));}),_fo=new T(function(){return B(A2(_ff,_fl,_fj));});return B(A3(_86,B(_84(E(_fi).a)),function(_fp){return new F(function(){return A3(_bh,_fn,_fp,_fo);});},_fk));});return new T2(0,new T(function(){return B(A2(_ff,_fl,_fj));}),_fm);},_fq=function(_fr,_fs,_ft){var _fu=E(_ft),_fv=B(_fh(_fs,_fu.a,_fu.b));return new T2(0,_fv.a,_fv.b);},_fw=function(_fx,_fy,_fz){var _fA=new T(function(){return E(E(E(_fx).c).a);}),_fB=new T(function(){var _fC=new T(function(){return B(_80(_fA));}),_fD=new T(function(){return B(_82(_fC));}),_fE=new T(function(){return B(A3(_cg,_fC,new T(function(){return B(A2(_7U,_fD,_cN));}),_fy));});return B(A3(_86,B(_84(E(_fx).a)),function(_fF){return new F(function(){return A3(_bh,_fD,_fF,_fE);});},_fz));});return new T2(0,new T(function(){return B(A2(_ck,_fA,_fy));}),_fB);},_fG=function(_fH,_fI,_fJ){var _fK=E(_fJ),_fL=B(_fw(_fI,_fK.a,_fK.b));return new T2(0,_fL.a,_fL.b);},_fM=function(_fN,_fO,_fP,_fQ){var _fR=new T(function(){return E(E(_fO).c);}),_fS=new T3(0,new T(function(){return E(E(_fO).a);}),new T(function(){return E(E(_fO).b);}),new T2(0,new T(function(){return E(E(_fR).a);}),new T(function(){return E(E(_fR).b);})));return new F(function(){return A3(_cg,_fN,new T(function(){var _fT=E(_fQ),_fU=B(_fw(_fS,_fT.a,_fT.b));return new T2(0,_fU.a,_fU.b);}),new T(function(){var _fV=E(_fP),_fW=B(_fw(_fS,_fV.a,_fV.b));return new T2(0,_fW.a,_fW.b);}));});},_fX=new T1(0,0),_fY=function(_fZ){return E(E(_fZ).b);},_g0=function(_g1){return E(E(_g1).b);},_g2=function(_g3){var _g4=new T(function(){return E(E(E(_g3).c).a);}),_g5=new T(function(){return B(A2(_g0,E(_g3).a,new T(function(){return B(A2(_7U,B(_82(B(_80(_g4)))),_fX));})));});return new T2(0,new T(function(){return B(_fY(_g4));}),_g5);},_g6=function(_g7,_g8){var _g9=B(_g2(_g8));return new T2(0,_g9.a,_g9.b);},_ga=function(_gb,_gc,_gd){var _ge=new T(function(){return E(E(E(_gb).c).a);}),_gf=new T(function(){var _gg=new T(function(){return B(_82(new T(function(){return B(_80(_ge));})));}),_gh=new T(function(){return B(A2(_eD,_ge,_gc));});return B(A3(_86,B(_84(E(_gb).a)),function(_gi){return new F(function(){return A3(_bh,_gg,_gi,_gh);});},_gd));});return new T2(0,new T(function(){return B(A2(_eF,_ge,_gc));}),_gf);},_gj=function(_gk,_gl,_gm){var _gn=E(_gm),_go=B(_ga(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr,_gs){var _gt=new T(function(){return E(E(E(_gq).c).a);}),_gu=new T(function(){var _gv=new T(function(){return B(_82(new T(function(){return B(_80(_gt));})));}),_gw=new T(function(){return B(A2(_eW,_gt,_gr));});return B(A3(_86,B(_84(E(_gq).a)),function(_gx){return new F(function(){return A3(_bh,_gv,_gx,_gw);});},_gs));});return new T2(0,new T(function(){return B(A2(_eY,_gt,_gr));}),_gu);},_gy=function(_gz,_gA,_gB){var _gC=E(_gB),_gD=B(_gp(_gA,_gC.a,_gC.b));return new T2(0,_gD.a,_gD.b);},_gE=new T1(0,2),_gF=function(_gG,_gH,_gI){var _gJ=new T(function(){return E(E(E(_gG).c).a);}),_gK=new T(function(){var _gL=new T(function(){return B(_80(_gJ));}),_gM=new T(function(){return B(_82(_gL));}),_gN=new T(function(){var _gO=new T(function(){return B(A3(_cg,_gL,new T(function(){return B(A2(_7U,_gM,_cN));}),new T(function(){return B(A2(_7U,_gM,_gE));})));});return B(A3(_cg,_gL,_gO,new T(function(){return B(A2(_bv,_gJ,_gH));})));});return B(A3(_86,B(_84(E(_gG).a)),function(_gP){return new F(function(){return A3(_bh,_gM,_gP,_gN);});},_gI));});return new T2(0,new T(function(){return B(A2(_bv,_gJ,_gH));}),_gK);},_gQ=function(_gR,_gS,_gT){var _gU=E(_gT),_gV=B(_gF(_gS,_gU.a,_gU.b));return new T2(0,_gV.a,_gV.b);},_gW=function(_gX){return E(E(_gX).j);},_gY=function(_gZ,_h0,_h1){var _h2=new T(function(){return E(E(E(_gZ).c).a);}),_h3=new T(function(){var _h4=new T(function(){return B(_80(_h2));}),_h5=new T(function(){var _h6=new T(function(){return B(A2(_eD,_h2,_h0));});return B(A3(_bh,B(_82(_h4)),_h6,_h6));});return B(A3(_86,B(_84(E(_gZ).a)),function(_h7){return new F(function(){return A3(_cg,_h4,_h7,_h5);});},_h1));});return new T2(0,new T(function(){return B(A2(_gW,_h2,_h0));}),_h3);},_h8=function(_h9,_ha,_hb){var _hc=E(_hb),_hd=B(_gY(_ha,_hc.a,_hc.b));return new T2(0,_hd.a,_hd.b);},_he=function(_hf){return E(E(_hf).p);},_hg=function(_hh,_hi,_hj){var _hk=new T(function(){return E(E(E(_hh).c).a);}),_hl=new T(function(){var _hm=new T(function(){return B(_80(_hk));}),_hn=new T(function(){var _ho=new T(function(){return B(A2(_eW,_hk,_hi));});return B(A3(_bh,B(_82(_hm)),_ho,_ho));});return B(A3(_86,B(_84(E(_hh).a)),function(_hp){return new F(function(){return A3(_cg,_hm,_hp,_hn);});},_hj));});return new T2(0,new T(function(){return B(A2(_he,_hk,_hi));}),_hl);},_hq=function(_hr,_hs,_ht){var _hu=E(_ht),_hv=B(_hg(_hs,_hu.a,_hu.b));return new T2(0,_hv.a,_hv.b);},_hw=function(_hx,_hy){return {_:0,a:_hx,b:new T(function(){return B(_g6(_hx,_hy));}),c:function(_hz){return new F(function(){return _fq(_hx,_hy,_hz);});},d:function(_hz){return new F(function(){return _fG(_hx,_hy,_hz);});},e:function(_hz){return new F(function(){return _gQ(_hx,_hy,_hz);});},f:function(_hA,_hz){return new F(function(){return _cF(_hx,_hy,_hA,_hz);});},g:function(_hA,_hz){return new F(function(){return _fM(_hx,_hy,_hA,_hz);});},h:function(_hz){return new F(function(){return _gj(_hx,_hy,_hz);});},i:function(_hz){return new F(function(){return _eQ(_hx,_hy,_hz);});},j:function(_hz){return new F(function(){return _h8(_hx,_hy,_hz);});},k:function(_hz){return new F(function(){return _dE(_hx,_hy,_hz);});},l:function(_hz){return new F(function(){return _d2(_hx,_hy,_hz);});},m:function(_hz){return new F(function(){return _ef(_hx,_hy,_hz);});},n:function(_hz){return new F(function(){return _gy(_hx,_hy,_hz);});},o:function(_hz){return new F(function(){return _f9(_hx,_hy,_hz);});},p:function(_hz){return new F(function(){return _hq(_hx,_hy,_hz);});},q:function(_hz){return new F(function(){return _dX(_hx,_hy,_hz);});},r:function(_hz){return new F(function(){return _dl(_hx,_hy,_hz);});},s:function(_hz){return new F(function(){return _ex(_hx,_hy,_hz);});}};},_hB=function(_hC,_hD,_hE,_hF,_hG){var _hH=new T(function(){return B(_80(new T(function(){return E(E(E(_hC).c).a);})));}),_hI=new T(function(){var _hJ=E(_hC).a,_hK=new T(function(){var _hL=new T(function(){return B(_82(_hH));}),_hM=new T(function(){return B(A3(_bh,_hL,_hF,_hF));}),_hN=function(_hO,_hP){var _hQ=new T(function(){return B(A3(_bt,_hL,new T(function(){return B(A3(_bh,_hL,_hO,_hF));}),new T(function(){return B(A3(_bh,_hL,_hD,_hP));})));});return new F(function(){return A3(_cg,_hH,_hQ,_hM);});};return B(A3(_86,B(_84(_hJ)),_hN,_hE));});return B(A3(_ci,_hJ,_hK,_hG));});return new T2(0,new T(function(){return B(A3(_cg,_hH,_hD,_hF));}),_hI);},_hR=function(_hS,_hT,_hU,_hV){var _hW=E(_hU),_hX=E(_hV),_hY=B(_hB(_hT,_hW.a,_hW.b,_hX.a,_hX.b));return new T2(0,_hY.a,_hY.b);},_hZ=function(_i0){return E(E(_i0).d);},_i1=function(_i2,_i3){var _i4=new T(function(){return B(_80(new T(function(){return E(E(E(_i2).c).a);})));}),_i5=new T(function(){return B(A2(_g0,E(_i2).a,new T(function(){return B(A2(_7U,B(_82(_i4)),_fX));})));});return new T2(0,new T(function(){return B(A2(_hZ,_i4,_i3));}),_i5);},_i6=function(_i7,_i8,_i9){var _ia=B(_i1(_i8,_i9));return new T2(0,_ia.a,_ia.b);},_ib=function(_ic,_id,_ie){var _if=new T(function(){return B(_80(new T(function(){return E(E(E(_ic).c).a);})));}),_ig=new T(function(){return B(_82(_if));}),_ih=new T(function(){var _ii=new T(function(){var _ij=new T(function(){return B(A3(_cg,_if,new T(function(){return B(A2(_7U,_ig,_cN));}),new T(function(){return B(A3(_bh,_ig,_id,_id));})));});return B(A2(_6S,_ig,_ij));});return B(A3(_86,B(_84(E(_ic).a)),function(_ik){return new F(function(){return A3(_bh,_ig,_ik,_ii);});},_ie));}),_il=new T(function(){return B(A3(_cg,_if,new T(function(){return B(A2(_7U,_ig,_cN));}),_id));});return new T2(0,_il,_ih);},_im=function(_in,_io,_ip){var _iq=E(_ip),_ir=B(_ib(_io,_iq.a,_iq.b));return new T2(0,_ir.a,_ir.b);},_is=function(_it,_iu){return new T4(0,_it,function(_hA,_hz){return new F(function(){return _hR(_it,_iu,_hA,_hz);});},function(_hz){return new F(function(){return _im(_it,_iu,_hz);});},function(_hz){return new F(function(){return _i6(_it,_iu,_hz);});});},_iv=function(_iw,_ix,_iy,_iz,_iA){var _iB=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_iw).c).a);})));})));}),_iC=new T(function(){var _iD=E(_iw).a,_iE=new T(function(){var _iF=function(_iG,_iH){return new F(function(){return A3(_6Q,_iB,new T(function(){return B(A3(_bh,_iB,_ix,_iH));}),new T(function(){return B(A3(_bh,_iB,_iG,_iz));}));});};return B(A3(_86,B(_84(_iD)),_iF,_iy));});return B(A3(_ci,_iD,_iE,_iA));});return new T2(0,new T(function(){return B(A3(_bh,_iB,_ix,_iz));}),_iC);},_iI=function(_iJ,_iK,_iL){var _iM=E(_iK),_iN=E(_iL),_iO=B(_iv(_iJ,_iM.a,_iM.b,_iN.a,_iN.b));return new T2(0,_iO.a,_iO.b);},_iP=function(_iQ,_iR,_iS,_iT,_iU){var _iV=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_iQ).c).a);})));})));}),_iW=new T(function(){var _iX=E(_iQ).a,_iY=new T(function(){return B(A3(_86,B(_84(_iX)),new T(function(){return B(_6Q(_iV));}),_iS));});return B(A3(_ci,_iX,_iY,_iU));});return new T2(0,new T(function(){return B(A3(_6Q,_iV,_iR,_iT));}),_iW);},_iZ=function(_j0,_j1,_j2){var _j3=E(_j1),_j4=E(_j2),_j5=B(_iP(_j0,_j3.a,_j3.b,_j4.a,_j4.b));return new T2(0,_j5.a,_j5.b);},_j6=function(_j7,_j8,_j9){var _ja=B(_jb(_j7));return new F(function(){return A3(_6Q,_ja,_j8,new T(function(){return B(A2(_6S,_ja,_j9));}));});},_jc=function(_jd){return E(E(_jd).e);},_je=function(_jf){return E(E(_jf).f);},_jg=function(_jh,_ji,_jj){var _jk=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_jh).c).a);})));})));}),_jl=new T(function(){var _jm=new T(function(){return B(A2(_je,_jk,_ji));});return B(A3(_86,B(_84(E(_jh).a)),function(_jn){return new F(function(){return A3(_bh,_jk,_jn,_jm);});},_jj));});return new T2(0,new T(function(){return B(A2(_jc,_jk,_ji));}),_jl);},_jo=function(_jp,_jq){var _jr=E(_jq),_js=B(_jg(_jp,_jr.a,_jr.b));return new T2(0,_js.a,_js.b);},_jt=function(_ju,_jv){var _jw=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_ju).c).a);})));})));}),_jx=new T(function(){return B(A2(_g0,E(_ju).a,new T(function(){return B(A2(_7U,_jw,_fX));})));});return new T2(0,new T(function(){return B(A2(_7U,_jw,_jv));}),_jx);},_jy=function(_jz,_jA){var _jB=B(_jt(_jz,_jA));return new T2(0,_jB.a,_jB.b);},_jC=function(_jD,_jE){var _jF=E(_jE),_jG=B(_88(_jD,_jF.a,_jF.b));return new T2(0,_jG.a,_jG.b);},_jH=function(_jI,_jJ){var _jK=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_jI).c).a);})));})));}),_jL=new T(function(){return B(A2(_g0,E(_jI).a,new T(function(){return B(A2(_7U,_jK,_fX));})));});return new T2(0,new T(function(){return B(A2(_je,_jK,_jJ));}),_jL);},_jM=function(_jN,_jO){var _jP=B(_jH(_jN,E(_jO).a));return new T2(0,_jP.a,_jP.b);},_jb=function(_jQ){return {_:0,a:function(_hA,_hz){return new F(function(){return _iZ(_jQ,_hA,_hz);});},b:function(_hA,_hz){return new F(function(){return _j6(_jQ,_hA,_hz);});},c:function(_hA,_hz){return new F(function(){return _iI(_jQ,_hA,_hz);});},d:function(_hz){return new F(function(){return _jC(_jQ,_hz);});},e:function(_hz){return new F(function(){return _jo(_jQ,_hz);});},f:function(_hz){return new F(function(){return _jM(_jQ,_hz);});},g:function(_hz){return new F(function(){return _jy(_jQ,_hz);});}};},_jR=function(_jS){var _jT=new T(function(){return E(E(_jS).a);}),_jU=new T3(0,_7R,_7W,new T2(0,_jT,new T(function(){return E(E(_jS).b);}))),_jV=new T(function(){return B(_hw(new T(function(){return B(_is(new T(function(){return B(_jb(_jU));}),_jU));}),_jU));}),_jW=new T(function(){return B(_82(new T(function(){return B(_80(_jT));})));}),_jX=function(_jY){return E(B(_bx(_jV,new T(function(){var _jZ=E(_jY),_k0=B(A2(_7U,_jW,_7T)),_k1=B(A2(_7U,_jW,_7S));return new T3(0,E(new T2(0,_jZ.a,new T3(0,E(_k0),E(_k1),E(_k1)))),E(new T2(0,_jZ.b,new T3(0,E(_k1),E(_k0),E(_k1)))),E(new T2(0,_jZ.c,new T3(0,E(_k1),E(_k1),E(_k0)))));}))).b);};return E(_jX);},_k2=new T(function(){return B(_jR(_cd));}),_k3=function(_k4,_k5){var _k6=E(_k5);return (_k6._==0)?__Z:new T2(1,_k4,new T2(1,_k6.a,new T(function(){return B(_k3(_k4,_k6.b));})));},_k7=new T(function(){var _k8=B(A1(_k2,_bK));return new T2(1,_k8.a,new T(function(){return B(_k3(_9o,new T2(1,_k8.b,new T2(1,_k8.c,_w))));}));}),_k9=new T1(1,_k7),_ka=new T2(1,_k9,_9g),_kb=new T(function(){return B(unCStr("vec3("));}),_kc=new T1(0,_kb),_kd=new T2(1,_kc,_ka),_ke=new T(function(){return toJSStr(B(_93(_x,_8N,_kd)));}),_kf=function(_kg,_kh){while(1){var _ki=E(_kg);if(!_ki._){return E(_kh);}else{var _kj=_kh+1|0;_kg=_ki.b;_kh=_kj;continue;}}},_kk=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_kl=new T(function(){return B(err(_kk));}),_km=0,_kn=new T3(0,E(_km),E(_km),E(_km)),_ko=new T(function(){return B(unCStr("Negative exponent"));}),_kp=new T(function(){return B(err(_ko));}),_kq=function(_kr,_ks,_kt){while(1){if(!(_ks%2)){var _ku=_kr*_kr,_kv=quot(_ks,2);_kr=_ku;_ks=_kv;continue;}else{var _kw=E(_ks);if(_kw==1){return _kr*_kt;}else{var _ku=_kr*_kr,_kx=_kr*_kt;_kr=_ku;_ks=quot(_kw-1|0,2);_kt=_kx;continue;}}}},_ky=function(_kz,_kA){while(1){if(!(_kA%2)){var _kB=_kz*_kz,_kC=quot(_kA,2);_kz=_kB;_kA=_kC;continue;}else{var _kD=E(_kA);if(_kD==1){return E(_kz);}else{return new F(function(){return _kq(_kz*_kz,quot(_kD-1|0,2),_kz);});}}}},_kE=function(_kF){var _kG=E(_kF);return new F(function(){return Math.log(_kG+(_kG+1)*Math.sqrt((_kG-1)/(_kG+1)));});},_kH=function(_kI){var _kJ=E(_kI);return new F(function(){return Math.log(_kJ+Math.sqrt(1+_kJ*_kJ));});},_kK=function(_kL){var _kM=E(_kL);return 0.5*Math.log((1+_kM)/(1-_kM));},_kN=function(_kO,_kP){return Math.log(E(_kP))/Math.log(E(_kO));},_kQ=3.141592653589793,_kR=function(_kS){var _kT=E(_kS);return new F(function(){return _6r(_kT.a,_kT.b);});},_kU=function(_kV){return 1/E(_kV);},_kW=function(_kX){var _kY=E(_kX),_kZ=E(_kY);return (_kZ==0)?E(_6q):(_kZ<=0)? -_kZ:E(_kY);},_l0=function(_l1){var _l2=E(_l1);if(!_l2._){return _l2.a;}else{return new F(function(){return I_toNumber(_l2.a);});}},_l3=function(_l4){return new F(function(){return _l0(_l4);});},_l5=1,_l6=-1,_l7=function(_l8){var _l9=E(_l8);return (_l9<=0)?(_l9>=0)?E(_l9):E(_l6):E(_l5);},_la=function(_lb,_lc){return E(_lb)-E(_lc);},_ld=function(_le){return  -E(_le);},_lf=function(_lg,_lh){return E(_lg)+E(_lh);},_li=function(_lj,_lk){return E(_lj)*E(_lk);},_ll={_:0,a:_lf,b:_la,c:_li,d:_ld,e:_kW,f:_l7,g:_l3},_lm=function(_ln,_lo){return E(_ln)/E(_lo);},_lp=new T4(0,_ll,_lm,_kU,_kR),_lq=function(_lr){return new F(function(){return Math.acos(E(_lr));});},_ls=function(_lt){return new F(function(){return Math.asin(E(_lt));});},_lu=function(_lv){return new F(function(){return Math.atan(E(_lv));});},_lw=function(_lx){return new F(function(){return Math.cos(E(_lx));});},_ly=function(_lz){return new F(function(){return cosh(E(_lz));});},_lA=function(_lB){return new F(function(){return Math.exp(E(_lB));});},_lC=function(_lD){return new F(function(){return Math.log(E(_lD));});},_lE=function(_lF,_lG){return new F(function(){return Math.pow(E(_lF),E(_lG));});},_lH=function(_lI){return new F(function(){return Math.sin(E(_lI));});},_lJ=function(_lK){return new F(function(){return sinh(E(_lK));});},_lL=function(_lM){return new F(function(){return Math.sqrt(E(_lM));});},_lN=function(_lO){return new F(function(){return Math.tan(E(_lO));});},_lP=function(_lQ){return new F(function(){return tanh(E(_lQ));});},_lR={_:0,a:_lp,b:_kQ,c:_lA,d:_lC,e:_lL,f:_lE,g:_kN,h:_lH,i:_lw,j:_lN,k:_ls,l:_lq,m:_lu,n:_lJ,o:_ly,p:_lP,q:_kH,r:_kE,s:_kK},_lS=function(_lT,_lU){return (E(_lT)!=E(_lU))?true:false;},_lV=function(_lW,_lX){return E(_lW)==E(_lX);},_lY=new T2(0,_lV,_lS),_lZ=function(_m0,_m1){return E(_m0)<E(_m1);},_m2=function(_m3,_m4){return E(_m3)<=E(_m4);},_m5=function(_m6,_m7){return E(_m6)>E(_m7);},_m8=function(_m9,_ma){return E(_m9)>=E(_ma);},_mb=function(_mc,_md){var _me=E(_mc),_mf=E(_md);return (_me>=_mf)?(_me!=_mf)?2:1:0;},_mg=function(_mh,_mi){var _mj=E(_mh),_mk=E(_mi);return (_mj>_mk)?E(_mj):E(_mk);},_ml=function(_mm,_mn){var _mo=E(_mm),_mp=E(_mn);return (_mo>_mp)?E(_mp):E(_mo);},_mq={_:0,a:_lY,b:_mb,c:_lZ,d:_m2,e:_m5,f:_m8,g:_mg,h:_ml},_mr="dz",_ms="wy",_mt="wx",_mu="dy",_mv="dx",_mw="t",_mx="a",_my="r",_mz="ly",_mA="lx",_mB="wz",_mC=0,_mD=function(_mE){var _mF=__new(),_mG=_mF,_mH=function(_mI,_){while(1){var _mJ=E(_mI);if(!_mJ._){return _mC;}else{var _mK=E(_mJ.a),_mL=__set(_mG,E(_mK.a),E(_mK.b));_mI=_mJ.b;continue;}}},_mM=B(_mH(_mE,_));return E(_mG);},_mN=function(_mO,_mP,_mQ,_mR,_mS,_mT,_mU,_mV,_mW){return new F(function(){return _mD(new T2(1,new T2(0,_mt,_mO),new T2(1,new T2(0,_ms,_mP),new T2(1,new T2(0,_mB,_mQ),new T2(1,new T2(0,_mA,_mR*_mS*Math.cos(_mT)),new T2(1,new T2(0,_mz,_mR*_mS*Math.sin(_mT)),new T2(1,new T2(0,_my,_mR),new T2(1,new T2(0,_mx,_mS),new T2(1,new T2(0,_mw,_mT),new T2(1,new T2(0,_mv,_mU),new T2(1,new T2(0,_mu,_mV),new T2(1,new T2(0,_mr,_mW),_w))))))))))));});},_mX=function(_mY){var _mZ=E(_mY),_n0=E(_mZ.a),_n1=E(_mZ.b),_n2=E(_mZ.d);return new F(function(){return _mN(_n0.a,_n0.b,_n0.c,E(_n1.a),E(_n1.b),E(_mZ.c),_n2.a,_n2.b,_n2.c);});},_n3=function(_n4,_n5){var _n6=E(_n5);return (_n6._==0)?__Z:new T2(1,new T(function(){return B(A1(_n4,_n6.a));}),new T(function(){return B(_n3(_n4,_n6.b));}));},_n7=function(_n8,_n9,_na){var _nb=__lst2arr(B(_n3(_mX,new T2(1,_n8,new T2(1,_n9,new T2(1,_na,_w))))));return E(_nb);},_nc=function(_nd){var _ne=E(_nd);return new F(function(){return _n7(_ne.a,_ne.b,_ne.c);});},_nf=new T2(0,_lR,_mq),_ng=function(_nh,_ni,_nj,_nk){var _nl=B(_80(_nh)),_nm=new T(function(){return B(A2(_bv,_nh,new T(function(){return B(_bj(_nh,_ni,_nj,_nk,_ni,_nj,_nk));})));});return new T3(0,B(A3(_cg,_nl,_ni,_nm)),B(A3(_cg,_nl,_nj,_nm)),B(A3(_cg,_nl,_nk,_nm)));},_nn=function(_no,_np,_nq,_nr,_ns,_nt,_nu){var _nv=B(_bh(_no));return new T3(0,B(A1(B(A1(_nv,_np)),_ns)),B(A1(B(A1(_nv,_nq)),_nt)),B(A1(B(A1(_nv,_nr)),_nu)));},_nw=function(_nx,_ny,_nz,_nA,_nB,_nC,_nD){var _nE=B(_6Q(_nx));return new T3(0,B(A1(B(A1(_nE,_ny)),_nB)),B(A1(B(A1(_nE,_nz)),_nC)),B(A1(B(A1(_nE,_nA)),_nD)));},_nF=function(_nG,_nH){var _nI=new T(function(){return E(E(_nG).a);}),_nJ=new T(function(){return B(A2(_jR,new T2(0,_nI,new T(function(){return E(E(_nG).b);})),_nH));}),_nK=new T(function(){var _nL=E(_nJ),_nM=B(_ng(_nI,_nL.a,_nL.b,_nL.c));return new T3(0,E(_nM.a),E(_nM.b),E(_nM.c));}),_nN=new T(function(){var _nO=E(_nH),_nP=E(_nK),_nQ=B(_80(_nI)),_nR=new T(function(){return B(A2(_bv,_nI,new T(function(){var _nS=E(_nJ),_nT=_nS.a,_nU=_nS.b,_nV=_nS.c;return B(_bj(_nI,_nT,_nU,_nV,_nT,_nU,_nV));})));}),_nW=B(A3(_cg,_nQ,new T(function(){return B(_bx(_nI,_nO));}),_nR)),_nX=B(_82(_nQ)),_nY=B(_nn(_nX,_nP.a,_nP.b,_nP.c,_nW,_nW,_nW)),_nZ=B(_6S(_nX)),_o0=B(_nw(_nX,_nO.a,_nO.b,_nO.c,B(A1(_nZ,_nY.a)),B(A1(_nZ,_nY.b)),B(A1(_nZ,_nY.c))));return new T3(0,E(_o0.a),E(_o0.b),E(_o0.c));});return new T2(0,_nN,_nK);},_o1=function(_o2){return E(E(_o2).a);},_o3=function(_o4,_o5,_o6,_o7,_o8,_o9,_oa){var _ob=B(_bj(_o4,_o8,_o9,_oa,_o5,_o6,_o7)),_oc=B(_82(B(_80(_o4)))),_od=B(_nn(_oc,_o8,_o9,_oa,_ob,_ob,_ob)),_oe=B(_6S(_oc));return new F(function(){return _nw(_oc,_o5,_o6,_o7,B(A1(_oe,_od.a)),B(A1(_oe,_od.b)),B(A1(_oe,_od.c)));});},_of=function(_og){return E(E(_og).a);},_oh=function(_oi,_oj,_ok,_ol){var _om=new T(function(){var _on=E(_ol),_oo=E(_ok),_op=B(_o3(_oi,_on.a,_on.b,_on.c,_oo.a,_oo.b,_oo.c));return new T3(0,E(_op.a),E(_op.b),E(_op.c));}),_oq=new T(function(){return B(A2(_bv,_oi,new T(function(){var _or=E(_om),_os=_or.a,_ot=_or.b,_ou=_or.c;return B(_bj(_oi,_os,_ot,_ou,_os,_ot,_ou));})));});if(!B(A3(_of,B(_o1(_oj)),_oq,new T(function(){return B(A2(_7U,B(_82(B(_80(_oi)))),_7S));})))){var _ov=E(_om),_ow=B(_ng(_oi,_ov.a,_ov.b,_ov.c)),_ox=B(A2(_bv,_oi,new T(function(){var _oy=E(_ol),_oz=_oy.a,_oA=_oy.b,_oB=_oy.c;return B(_bj(_oi,_oz,_oA,_oB,_oz,_oA,_oB));}))),_oC=B(_bh(new T(function(){return B(_82(new T(function(){return B(_80(_oi));})));})));return new T3(0,B(A1(B(A1(_oC,_ow.a)),_ox)),B(A1(B(A1(_oC,_ow.b)),_ox)),B(A1(B(A1(_oC,_ow.c)),_ox)));}else{var _oD=B(A2(_7U,B(_82(B(_80(_oi)))),_7S));return new T3(0,_oD,_oD,_oD);}},_oE=function(_oF,_oG){while(1){var _oH=E(_oF);if(!_oH._){return E(_oG);}else{var _oI=_oH.b,_oJ=E(_oH.a);if(_oG>_oJ){_oF=_oI;continue;}else{_oF=_oI;_oG=_oJ;continue;}}}},_oK=new T(function(){var _oL=eval("angleCount"),_oM=Number(_oL);return jsTrunc(_oM);}),_oN=new T(function(){return E(_oK);}),_oO=new T(function(){return B(unCStr(": empty list"));}),_oP=new T(function(){return B(unCStr("Prelude."));}),_oQ=function(_oR){return new F(function(){return err(B(_n(_oP,new T(function(){return B(_n(_oR,_oO));},1))));});},_oS=new T(function(){return B(unCStr("head"));}),_oT=new T(function(){return B(_oQ(_oS));}),_oU=function(_oV,_oW,_oX){var _oY=E(_oV);if(!_oY._){return __Z;}else{var _oZ=E(_oW);if(!_oZ._){return __Z;}else{var _p0=_oZ.a,_p1=E(_oX);if(!_p1._){return __Z;}else{var _p2=E(_p1.a),_p3=_p2.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_oY.a),E(_p0),E(_p3));}),new T2(1,new T(function(){return new T3(0,E(_p0),E(_p3),E(_p2.b));}),_w)),new T(function(){return B(_oU(_oY.b,_oZ.b,_p1.b));},1));});}}}},_p4=new T(function(){return B(unCStr("tail"));}),_p5=new T(function(){return B(_oQ(_p4));}),_p6=function(_p7,_p8){var _p9=E(_p7);if(!_p9._){return __Z;}else{var _pa=E(_p8);return (_pa._==0)?__Z:new T2(1,new T2(0,_p9.a,_pa.a),new T(function(){return B(_p6(_p9.b,_pa.b));}));}},_pb=function(_pc,_pd){var _pe=E(_pc);if(!_pe._){return __Z;}else{var _pf=E(_pd);if(!_pf._){return __Z;}else{var _pg=E(_pe.a),_ph=_pg.b,_pi=E(_pf.a).b,_pj=new T(function(){var _pk=new T(function(){return B(_p6(_pi,new T(function(){var _pl=E(_pi);if(!_pl._){return E(_p5);}else{return E(_pl.b);}},1)));},1);return B(_oU(_ph,new T(function(){var _pm=E(_ph);if(!_pm._){return E(_p5);}else{return E(_pm.b);}},1),_pk));});return new F(function(){return _n(new T2(1,new T(function(){var _pn=E(_ph);if(!_pn._){return E(_oT);}else{var _po=E(_pi);if(!_po._){return E(_oT);}else{return new T3(0,E(_pg.a),E(_pn.a),E(_po.a));}}}),_pj),new T(function(){return B(_pb(_pe.b,_pf.b));},1));});}}},_pp=new T(function(){return 6.283185307179586/E(_oN);}),_pq=new T(function(){return E(_oN)-1;}),_pr=new T1(0,1),_ps=function(_pt,_pu){var _pv=E(_pu),_pw=new T(function(){var _px=B(_82(_pt)),_py=B(_ps(_pt,B(A3(_6Q,_px,_pv,new T(function(){return B(A2(_7U,_px,_pr));})))));return new T2(1,_py.a,_py.b);});return new T2(0,_pv,_pw);},_pz=function(_pA){return E(E(_pA).d);},_pB=new T1(0,2),_pC=function(_pD,_pE){var _pF=E(_pE);if(!_pF._){return __Z;}else{var _pG=_pF.a;return (!B(A1(_pD,_pG)))?__Z:new T2(1,_pG,new T(function(){return B(_pC(_pD,_pF.b));}));}},_pH=function(_pI,_pJ,_pK,_pL){var _pM=B(_ps(_pJ,_pK)),_pN=new T(function(){var _pO=B(_82(_pJ)),_pP=new T(function(){return B(A3(_cg,_pJ,new T(function(){return B(A2(_7U,_pO,_pr));}),new T(function(){return B(A2(_7U,_pO,_pB));})));});return B(A3(_6Q,_pO,_pL,_pP));});return new F(function(){return _pC(function(_pQ){return new F(function(){return A3(_pz,_pI,_pQ,_pN);});},new T2(1,_pM.a,_pM.b));});},_pR=new T(function(){return B(_pH(_mq,_lp,_km,_pq));}),_pS=function(_pT,_pU){while(1){var _pV=E(_pT);if(!_pV._){return E(_pU);}else{_pT=_pV.b;_pU=_pV.a;continue;}}},_pW=new T(function(){return B(unCStr("last"));}),_pX=new T(function(){return B(_oQ(_pW));}),_pY=function(_pZ){return new F(function(){return _pS(_pZ,_pX);});},_q0=function(_q1){return new F(function(){return _pY(E(_q1).b);});},_q2=new T(function(){return B(unCStr("maximum"));}),_q3=new T(function(){return B(_oQ(_q2));}),_q4=new T(function(){var _q5=eval("proceedCount"),_q6=Number(_q5);return jsTrunc(_q6);}),_q7=new T(function(){return E(_q4);}),_q8=1,_q9=new T(function(){return B(_pH(_mq,_lp,_q8,_q7));}),_qa=function(_qb,_qc,_qd,_qe,_qf,_qg,_qh,_qi,_qj,_qk,_ql,_qm,_qn,_qo){var _qp=new T(function(){var _qq=new T(function(){var _qr=E(_qk),_qs=E(_qo),_qt=E(_qn),_qu=E(_ql),_qv=E(_qm),_qw=E(_qj);return new T3(0,_qr*_qs-_qt*_qu,_qu*_qv-_qs*_qw,_qw*_qt-_qv*_qr);}),_qx=function(_qy){var _qz=new T(function(){var _qA=E(_qy)/E(_oN);return (_qA+_qA)*3.141592653589793;}),_qB=new T(function(){return B(A1(_qb,_qz));}),_qC=new T(function(){var _qD=new T(function(){var _qE=E(_qB)/E(_q7);return new T3(0,E(_qE),E(_qE),E(_qE));}),_qF=function(_qG,_qH){var _qI=E(_qG);if(!_qI._){return new T2(0,_w,_qH);}else{var _qJ=new T(function(){var _qK=B(_nF(_nf,new T(function(){var _qL=E(_qH),_qM=E(_qL.a),_qN=E(_qL.b),_qO=E(_qD);return new T3(0,E(_qM.a)+E(_qN.a)*E(_qO.a),E(_qM.b)+E(_qN.b)*E(_qO.b),E(_qM.c)+E(_qN.c)*E(_qO.c));}))),_qP=_qK.a,_qQ=new T(function(){var _qR=E(_qK.b),_qS=E(E(_qH).b),_qT=B(_o3(_lR,_qS.a,_qS.b,_qS.c,_qR.a,_qR.b,_qR.c)),_qU=B(_ng(_lR,_qT.a,_qT.b,_qT.c));return new T3(0,E(_qU.a),E(_qU.b),E(_qU.c));});return new T2(0,new T(function(){var _qV=E(_qB),_qW=E(_qz);return new T4(0,E(_qP),E(new T2(0,E(_qI.a)/E(_q7),E(_qV))),E(_qW),E(_qQ));}),new T2(0,_qP,_qQ));}),_qX=new T(function(){var _qY=B(_qF(_qI.b,new T(function(){return E(E(_qJ).b);})));return new T2(0,_qY.a,_qY.b);});return new T2(0,new T2(1,new T(function(){return E(E(_qJ).a);}),new T(function(){return E(E(_qX).a);})),new T(function(){return E(E(_qX).b);}));}},_qZ=function(_r0,_r1,_r2,_r3,_r4){var _r5=E(_r0);if(!_r5._){return new T2(0,_w,new T2(0,new T3(0,E(_r1),E(_r2),E(_r3)),_r4));}else{var _r6=new T(function(){var _r7=B(_nF(_nf,new T(function(){var _r8=E(_r4),_r9=E(_qD);return new T3(0,E(_r1)+E(_r8.a)*E(_r9.a),E(_r2)+E(_r8.b)*E(_r9.b),E(_r3)+E(_r8.c)*E(_r9.c));}))),_ra=_r7.a,_rb=new T(function(){var _rc=E(_r7.b),_rd=E(_r4),_re=B(_o3(_lR,_rd.a,_rd.b,_rd.c,_rc.a,_rc.b,_rc.c)),_rf=B(_ng(_lR,_re.a,_re.b,_re.c));return new T3(0,E(_rf.a),E(_rf.b),E(_rf.c));});return new T2(0,new T(function(){var _rg=E(_qB),_rh=E(_qz);return new T4(0,E(_ra),E(new T2(0,E(_r5.a)/E(_q7),E(_rg))),E(_rh),E(_rb));}),new T2(0,_ra,_rb));}),_ri=new T(function(){var _rj=B(_qF(_r5.b,new T(function(){return E(E(_r6).b);})));return new T2(0,_rj.a,_rj.b);});return new T2(0,new T2(1,new T(function(){return E(E(_r6).a);}),new T(function(){return E(E(_ri).a);})),new T(function(){return E(E(_ri).b);}));}};return E(B(_qZ(_q9,_qe,_qf,_qg,new T(function(){var _rk=E(_qq),_rl=E(_qz)+_qh,_rm=Math.cos(_rl),_rn=Math.sin(_rl);return new T3(0,E(_qj)*_rm+E(_rk.a)*_rn,E(_qk)*_rm+E(_rk.b)*_rn,E(_ql)*_rm+E(_rk.c)*_rn);}))).a);});return new T2(0,new T(function(){var _ro=E(_qB),_rp=E(_qz);return new T4(0,E(new T3(0,E(_qe),E(_qf),E(_qg))),E(new T2(0,E(_km),E(_ro))),E(_rp),E(_kn));}),_qC);};return B(_n3(_qx,_pR));}),_rq=new T(function(){var _rr=function(_rs){return new F(function(){return A1(_qb,new T(function(){return B(_li(_rs,_pp));}));});},_rt=B(_n3(_rr,_pR));if(!_rt._){return E(_q3);}else{return B(_oE(_rt.b,E(_rt.a)));}}),_ru=new T(function(){var _rv=new T(function(){var _rw=B(_n(_qp,new T2(1,new T(function(){var _rx=E(_qp);if(!_rx._){return E(_oT);}else{return E(_rx.a);}}),_w)));if(!_rw._){return E(_p5);}else{return E(_rw.b);}},1);return B(_pb(_qp,_rv));});return new T3(0,_ru,new T(function(){return B(_n3(_q0,_qp));}),_rq);},_ry=function(_rz,_rA,_rB,_rC,_rD,_rE,_rF,_rG,_rH,_rI,_rJ,_rK,_rL,_rM,_rN,_rO,_rP,_rQ){var _rR=B(_nF(_nf,new T3(0,E(_rC),E(_rD),E(_rE)))),_rS=_rR.b,_rT=E(_rR.a),_rU=B(_oh(_lR,_mq,_rS,new T3(0,E(_rG),E(_rH),E(_rI)))),_rV=E(_rS),_rW=_rV.a,_rX=_rV.b,_rY=_rV.c,_rZ=B(_o3(_lR,_rK,_rL,_rM,_rW,_rX,_rY)),_s0=B(_ng(_lR,_rZ.a,_rZ.b,_rZ.c)),_s1=_s0.a,_s2=_s0.b,_s3=_s0.c,_s4=E(_rF),_s5=new T2(0,E(new T3(0,E(_rU.a),E(_rU.b),E(_rU.c))),E(_rJ)),_s6=B(_qa(_rz,_rA,_rB,_rT.a,_rT.b,_rT.c,_s4,_s5,_s1,_s2,_s3,_rW,_rX,_rY)),_s7=__lst2arr(B(_n3(_nc,_s6.a))),_s8=__lst2arr(B(_n3(_mX,_s6.b)));return {_:0,a:_rz,b:_rA,c:_rB,d:new T2(0,E(_rT),E(_s4)),e:_s5,f:new T3(0,E(_s1),E(_s2),E(_s3)),g:_rV,h:_s7,i:_s8,j:E(_s6.c)};},_s9=-4,_sa=new T3(0,E(_km),E(_s9),E(_km)),_sb=function(_sc){return E(_sa);},_sd=function(_){return new F(function(){return __jsNull();});},_se=function(_sf){var _sg=B(A1(_sf,_));return E(_sg);},_sh=new T(function(){return B(_se(_sd));}),_si=function(_sj,_sk,_sl,_sm,_sn,_so,_sp,_sq,_sr,_ss,_st,_su,_sv){var _sw=function(_sx){var _sy=E(_pp),_sz=2+_sx|0,_sA=_sz-1|0,_sB=(2+_sx)*(1+_sx),_sC=E(_pR);if(!_sC._){return _sy*0;}else{var _sD=_sC.a,_sE=_sC.b,_sF=B(A1(_sj,new T(function(){return 6.283185307179586*E(_sD)/E(_oN);}))),_sG=B(A1(_sj,new T(function(){return 6.283185307179586*(E(_sD)+1)/E(_oN);})));if(_sF!=_sG){if(_sz>=0){var _sH=E(_sz);if(!_sH){var _sI=function(_sJ,_sK){while(1){var _sL=B((function(_sM,_sN){var _sO=E(_sM);if(!_sO._){return E(_sN);}else{var _sP=_sO.a,_sQ=_sO.b,_sR=B(A1(_sj,new T(function(){return 6.283185307179586*E(_sP)/E(_oN);}))),_sS=B(A1(_sj,new T(function(){return 6.283185307179586*(E(_sP)+1)/E(_oN);})));if(_sR!=_sS){var _sT=_sN+0/(_sR-_sS)/_sB;_sJ=_sQ;_sK=_sT;return __continue;}else{if(_sA>=0){var _sU=E(_sA);if(!_sU){var _sT=_sN+_sz/_sB;_sJ=_sQ;_sK=_sT;return __continue;}else{var _sT=_sN+_sz*B(_ky(_sR,_sU))/_sB;_sJ=_sQ;_sK=_sT;return __continue;}}else{return E(_kp);}}}})(_sJ,_sK));if(_sL!=__continue){return _sL;}}};return _sy*B(_sI(_sE,0/(_sF-_sG)/_sB));}else{var _sV=function(_sW,_sX){while(1){var _sY=B((function(_sZ,_t0){var _t1=E(_sZ);if(!_t1._){return E(_t0);}else{var _t2=_t1.a,_t3=_t1.b,_t4=B(A1(_sj,new T(function(){return 6.283185307179586*E(_t2)/E(_oN);}))),_t5=B(A1(_sj,new T(function(){return 6.283185307179586*(E(_t2)+1)/E(_oN);})));if(_t4!=_t5){if(_sH>=0){var _t6=_t0+(B(_ky(_t4,_sH))-B(_ky(_t5,_sH)))/(_t4-_t5)/_sB;_sW=_t3;_sX=_t6;return __continue;}else{return E(_kp);}}else{if(_sA>=0){var _t7=E(_sA);if(!_t7){var _t6=_t0+_sz/_sB;_sW=_t3;_sX=_t6;return __continue;}else{var _t6=_t0+_sz*B(_ky(_t4,_t7))/_sB;_sW=_t3;_sX=_t6;return __continue;}}else{return E(_kp);}}}})(_sW,_sX));if(_sY!=__continue){return _sY;}}};return _sy*B(_sV(_sE,(B(_ky(_sF,_sH))-B(_ky(_sG,_sH)))/(_sF-_sG)/_sB));}}else{return E(_kp);}}else{if(_sA>=0){var _t8=E(_sA);if(!_t8){var _t9=function(_ta,_tb){while(1){var _tc=B((function(_td,_te){var _tf=E(_td);if(!_tf._){return E(_te);}else{var _tg=_tf.a,_th=_tf.b,_ti=B(A1(_sj,new T(function(){return 6.283185307179586*E(_tg)/E(_oN);}))),_tj=B(A1(_sj,new T(function(){return 6.283185307179586*(E(_tg)+1)/E(_oN);})));if(_ti!=_tj){if(_sz>=0){var _tk=E(_sz);if(!_tk){var _tl=_te+0/(_ti-_tj)/_sB;_ta=_th;_tb=_tl;return __continue;}else{var _tl=_te+(B(_ky(_ti,_tk))-B(_ky(_tj,_tk)))/(_ti-_tj)/_sB;_ta=_th;_tb=_tl;return __continue;}}else{return E(_kp);}}else{var _tl=_te+_sz/_sB;_ta=_th;_tb=_tl;return __continue;}}})(_ta,_tb));if(_tc!=__continue){return _tc;}}};return _sy*B(_t9(_sE,_sz/_sB));}else{var _tm=function(_tn,_to){while(1){var _tp=B((function(_tq,_tr){var _ts=E(_tq);if(!_ts._){return E(_tr);}else{var _tt=_ts.a,_tu=_ts.b,_tv=B(A1(_sj,new T(function(){return 6.283185307179586*E(_tt)/E(_oN);}))),_tw=B(A1(_sj,new T(function(){return 6.283185307179586*(E(_tt)+1)/E(_oN);})));if(_tv!=_tw){if(_sz>=0){var _tx=E(_sz);if(!_tx){var _ty=_tr+0/(_tv-_tw)/_sB;_tn=_tu;_to=_ty;return __continue;}else{var _ty=_tr+(B(_ky(_tv,_tx))-B(_ky(_tw,_tx)))/(_tv-_tw)/_sB;_tn=_tu;_to=_ty;return __continue;}}else{return E(_kp);}}else{if(_t8>=0){var _ty=_tr+_sz*B(_ky(_tv,_t8))/_sB;_tn=_tu;_to=_ty;return __continue;}else{return E(_kp);}}}})(_tn,_to));if(_tp!=__continue){return _tp;}}};return _sy*B(_tm(_sE,_sz*B(_ky(_sF,_t8))/_sB));}}else{return E(_kp);}}}},_tz=E(_sh),_tA=1/(B(_sw(1))*_sk);return new F(function(){return _ry(_sj,_sb,new T2(0,E(new T3(0,E(_tA),E(_tA),E(_tA))),1/(B(_sw(3))*_sk)),_sl,_sm,_sn,_so,_sp,_sq,_sr,_ss,_st,_su,_sv,_kn,_tz,_tz,0);});},_tB=1,_tC=0,_tD=function(_tE){var _tF=I_decodeDouble(_tE);return new T2(0,new T1(1,_tF.b),_tF.a);},_tG=function(_tH){return new T1(0,_tH);},_tI=function(_tJ){var _tK=hs_intToInt64(2147483647),_tL=hs_leInt64(_tJ,_tK);if(!_tL){return new T1(1,I_fromInt64(_tJ));}else{var _tM=hs_intToInt64(-2147483648),_tN=hs_geInt64(_tJ,_tM);if(!_tN){return new T1(1,I_fromInt64(_tJ));}else{var _tO=hs_int64ToInt(_tJ);return new F(function(){return _tG(_tO);});}}},_tP=new T(function(){var _tQ=newByteArr(256),_tR=_tQ,_=_tR["v"]["i8"][0]=8,_tS=function(_tT,_tU,_tV,_){while(1){if(_tV>=256){if(_tT>=256){return E(_);}else{var _tW=imul(2,_tT)|0,_tX=_tU+1|0,_tY=_tT;_tT=_tW;_tU=_tX;_tV=_tY;continue;}}else{var _=_tR["v"]["i8"][_tV]=_tU,_tY=_tV+_tT|0;_tV=_tY;continue;}}},_=B(_tS(2,0,1,_));return _tR;}),_tZ=function(_u0,_u1){var _u2=hs_int64ToInt(_u0),_u3=E(_tP),_u4=_u3["v"]["i8"][(255&_u2>>>0)>>>0&4294967295];if(_u1>_u4){if(_u4>=8){var _u5=hs_uncheckedIShiftRA64(_u0,8),_u6=function(_u7,_u8){while(1){var _u9=B((function(_ua,_ub){var _uc=hs_int64ToInt(_ua),_ud=_u3["v"]["i8"][(255&_uc>>>0)>>>0&4294967295];if(_ub>_ud){if(_ud>=8){var _ue=hs_uncheckedIShiftRA64(_ua,8),_uf=_ub-8|0;_u7=_ue;_u8=_uf;return __continue;}else{return new T2(0,new T(function(){var _ug=hs_uncheckedIShiftRA64(_ua,_ud);return B(_tI(_ug));}),_ub-_ud|0);}}else{return new T2(0,new T(function(){var _uh=hs_uncheckedIShiftRA64(_ua,_ub);return B(_tI(_uh));}),0);}})(_u7,_u8));if(_u9!=__continue){return _u9;}}};return new F(function(){return _u6(_u5,_u1-8|0);});}else{return new T2(0,new T(function(){var _ui=hs_uncheckedIShiftRA64(_u0,_u4);return B(_tI(_ui));}),_u1-_u4|0);}}else{return new T2(0,new T(function(){var _uj=hs_uncheckedIShiftRA64(_u0,_u1);return B(_tI(_uj));}),0);}},_uk=function(_ul){var _um=hs_intToInt64(_ul);return E(_um);},_un=function(_uo){var _up=E(_uo);if(!_up._){return new F(function(){return _uk(_up.a);});}else{return new F(function(){return I_toInt64(_up.a);});}},_uq=function(_ur){return I_toInt(_ur)>>>0;},_us=function(_ut){var _uu=E(_ut);if(!_uu._){return _uu.a>>>0;}else{return new F(function(){return _uq(_uu.a);});}},_uv=function(_uw){var _ux=B(_tD(_uw)),_uy=_ux.a,_uz=_ux.b;if(_uz<0){var _uA=function(_uB){if(!_uB){return new T2(0,E(_uy),B(_3C(_1U, -_uz)));}else{var _uC=B(_tZ(B(_un(_uy)), -_uz));return new T2(0,E(_uC.a),B(_3C(_1U,_uC.b)));}};if(!((B(_us(_uy))&1)>>>0)){return new F(function(){return _uA(1);});}else{return new F(function(){return _uA(0);});}}else{return new T2(0,B(_3C(_uy,_uz)),_1U);}},_uD=function(_uE){var _uF=B(_uv(E(_uE)));return new T2(0,E(_uF.a),E(_uF.b));},_uG=new T3(0,_ll,_mq,_uD),_uH=function(_uI){return E(E(_uI).a);},_uJ=function(_uK){return E(E(_uK).a);},_uL=function(_uM,_uN){if(_uM<=_uN){var _uO=function(_uP){return new T2(1,_uP,new T(function(){if(_uP!=_uN){return B(_uO(_uP+1|0));}else{return __Z;}}));};return new F(function(){return _uO(_uM);});}else{return __Z;}},_uQ=function(_uR){return new F(function(){return _uL(E(_uR),2147483647);});},_uS=function(_uT,_uU,_uV){if(_uV<=_uU){var _uW=new T(function(){var _uX=_uU-_uT|0,_uY=function(_uZ){return (_uZ>=(_uV-_uX|0))?new T2(1,_uZ,new T(function(){return B(_uY(_uZ+_uX|0));})):new T2(1,_uZ,_w);};return B(_uY(_uU));});return new T2(1,_uT,_uW);}else{return (_uV<=_uT)?new T2(1,_uT,_w):__Z;}},_v0=function(_v1,_v2,_v3){if(_v3>=_v2){var _v4=new T(function(){var _v5=_v2-_v1|0,_v6=function(_v7){return (_v7<=(_v3-_v5|0))?new T2(1,_v7,new T(function(){return B(_v6(_v7+_v5|0));})):new T2(1,_v7,_w);};return B(_v6(_v2));});return new T2(1,_v1,_v4);}else{return (_v3>=_v1)?new T2(1,_v1,_w):__Z;}},_v8=function(_v9,_va){if(_va<_v9){return new F(function(){return _uS(_v9,_va,-2147483648);});}else{return new F(function(){return _v0(_v9,_va,2147483647);});}},_vb=function(_vc,_vd){return new F(function(){return _v8(E(_vc),E(_vd));});},_ve=function(_vf,_vg,_vh){if(_vg<_vf){return new F(function(){return _uS(_vf,_vg,_vh);});}else{return new F(function(){return _v0(_vf,_vg,_vh);});}},_vi=function(_vj,_vk,_vl){return new F(function(){return _ve(E(_vj),E(_vk),E(_vl));});},_vm=function(_vn,_vo){return new F(function(){return _uL(E(_vn),E(_vo));});},_vp=function(_vq){return E(_vq);},_vr=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_vs=new T(function(){return B(err(_vr));}),_vt=function(_vu){var _vv=E(_vu);return (_vv==(-2147483648))?E(_vs):_vv-1|0;},_vw=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_vx=new T(function(){return B(err(_vw));}),_vy=function(_vz){var _vA=E(_vz);return (_vA==2147483647)?E(_vx):_vA+1|0;},_vB={_:0,a:_vy,b:_vt,c:_vp,d:_vp,e:_uQ,f:_vb,g:_vm,h:_vi},_vC=function(_vD,_vE){if(_vD<=0){if(_vD>=0){return new F(function(){return quot(_vD,_vE);});}else{if(_vE<=0){return new F(function(){return quot(_vD,_vE);});}else{return quot(_vD+1|0,_vE)-1|0;}}}else{if(_vE>=0){if(_vD>=0){return new F(function(){return quot(_vD,_vE);});}else{if(_vE<=0){return new F(function(){return quot(_vD,_vE);});}else{return quot(_vD+1|0,_vE)-1|0;}}}else{return quot(_vD-1|0,_vE)-1|0;}}},_vF=0,_vG=new T(function(){return B(_2Z(_vF));}),_vH=new T(function(){return die(_vG);}),_vI=function(_vJ,_vK){var _vL=E(_vK);switch(_vL){case -1:var _vM=E(_vJ);if(_vM==(-2147483648)){return E(_vH);}else{return new F(function(){return _vC(_vM,-1);});}break;case 0:return E(_33);default:return new F(function(){return _vC(_vJ,_vL);});}},_vN=function(_vO,_vP){return new F(function(){return _vI(E(_vO),E(_vP));});},_vQ=0,_vR=new T2(0,_vH,_vQ),_vS=function(_vT,_vU){var _vV=E(_vT),_vW=E(_vU);switch(_vW){case -1:var _vX=E(_vV);if(_vX==(-2147483648)){return E(_vR);}else{if(_vX<=0){if(_vX>=0){var _vY=quotRemI(_vX,-1);return new T2(0,_vY.a,_vY.b);}else{var _vZ=quotRemI(_vX,-1);return new T2(0,_vZ.a,_vZ.b);}}else{var _w0=quotRemI(_vX-1|0,-1);return new T2(0,_w0.a-1|0,(_w0.b+(-1)|0)+1|0);}}break;case 0:return E(_33);default:if(_vV<=0){if(_vV>=0){var _w1=quotRemI(_vV,_vW);return new T2(0,_w1.a,_w1.b);}else{if(_vW<=0){var _w2=quotRemI(_vV,_vW);return new T2(0,_w2.a,_w2.b);}else{var _w3=quotRemI(_vV+1|0,_vW);return new T2(0,_w3.a-1|0,(_w3.b+_vW|0)-1|0);}}}else{if(_vW>=0){if(_vV>=0){var _w4=quotRemI(_vV,_vW);return new T2(0,_w4.a,_w4.b);}else{if(_vW<=0){var _w5=quotRemI(_vV,_vW);return new T2(0,_w5.a,_w5.b);}else{var _w6=quotRemI(_vV+1|0,_vW);return new T2(0,_w6.a-1|0,(_w6.b+_vW|0)-1|0);}}}else{var _w7=quotRemI(_vV-1|0,_vW);return new T2(0,_w7.a-1|0,(_w7.b+_vW|0)+1|0);}}}},_w8=function(_w9,_wa){var _wb=_w9%_wa;if(_w9<=0){if(_w9>=0){return E(_wb);}else{if(_wa<=0){return E(_wb);}else{var _wc=E(_wb);return (_wc==0)?0:_wc+_wa|0;}}}else{if(_wa>=0){if(_w9>=0){return E(_wb);}else{if(_wa<=0){return E(_wb);}else{var _wd=E(_wb);return (_wd==0)?0:_wd+_wa|0;}}}else{var _we=E(_wb);return (_we==0)?0:_we+_wa|0;}}},_wf=function(_wg,_wh){var _wi=E(_wh);switch(_wi){case -1:return E(_vQ);case 0:return E(_33);default:return new F(function(){return _w8(E(_wg),_wi);});}},_wj=function(_wk,_wl){var _wm=E(_wk),_wn=E(_wl);switch(_wn){case -1:var _wo=E(_wm);if(_wo==(-2147483648)){return E(_vH);}else{return new F(function(){return quot(_wo,-1);});}break;case 0:return E(_33);default:return new F(function(){return quot(_wm,_wn);});}},_wp=function(_wq,_wr){var _ws=E(_wq),_wt=E(_wr);switch(_wt){case -1:var _wu=E(_ws);if(_wu==(-2147483648)){return E(_vR);}else{var _wv=quotRemI(_wu,-1);return new T2(0,_wv.a,_wv.b);}break;case 0:return E(_33);default:var _ww=quotRemI(_ws,_wt);return new T2(0,_ww.a,_ww.b);}},_wx=function(_wy,_wz){var _wA=E(_wz);switch(_wA){case -1:return E(_vQ);case 0:return E(_33);default:return E(_wy)%_wA;}},_wB=function(_wC){return new F(function(){return _tG(E(_wC));});},_wD=function(_wE){return new T2(0,E(B(_tG(E(_wE)))),E(_pr));},_wF=function(_wG,_wH){return imul(E(_wG),E(_wH))|0;},_wI=function(_wJ,_wK){return E(_wJ)+E(_wK)|0;},_wL=function(_wM,_wN){return E(_wM)-E(_wN)|0;},_wO=function(_wP){var _wQ=E(_wP);return (_wQ<0)? -_wQ:E(_wQ);},_wR=function(_wS){return new F(function(){return _3g(_wS);});},_wT=function(_wU){return  -E(_wU);},_wV=-1,_wW=0,_wX=1,_wY=function(_wZ){var _x0=E(_wZ);return (_x0>=0)?(E(_x0)==0)?E(_wW):E(_wX):E(_wV);},_x1={_:0,a:_wI,b:_wL,c:_wF,d:_wT,e:_wO,f:_wY,g:_wR},_x2=function(_x3,_x4){return E(_x3)==E(_x4);},_x5=function(_x6,_x7){return E(_x6)!=E(_x7);},_x8=new T2(0,_x2,_x5),_x9=function(_xa,_xb){var _xc=E(_xa),_xd=E(_xb);return (_xc>_xd)?E(_xc):E(_xd);},_xe=function(_xf,_xg){var _xh=E(_xf),_xi=E(_xg);return (_xh>_xi)?E(_xi):E(_xh);},_xj=function(_xk,_xl){return (_xk>=_xl)?(_xk!=_xl)?2:1:0;},_xm=function(_xn,_xo){return new F(function(){return _xj(E(_xn),E(_xo));});},_xp=function(_xq,_xr){return E(_xq)>=E(_xr);},_xs=function(_xt,_xu){return E(_xt)>E(_xu);},_xv=function(_xw,_xx){return E(_xw)<=E(_xx);},_xy=function(_xz,_xA){return E(_xz)<E(_xA);},_xB={_:0,a:_x8,b:_xm,c:_xy,d:_xv,e:_xs,f:_xp,g:_x9,h:_xe},_xC=new T3(0,_x1,_xB,_wD),_xD={_:0,a:_xC,b:_vB,c:_wj,d:_wx,e:_vN,f:_wf,g:_wp,h:_vS,i:_wB},_xE=new T1(0,2),_xF=function(_xG,_xH){while(1){var _xI=E(_xG);if(!_xI._){var _xJ=_xI.a,_xK=E(_xH);if(!_xK._){var _xL=_xK.a;if(!(imul(_xJ,_xL)|0)){return new T1(0,imul(_xJ,_xL)|0);}else{_xG=new T1(1,I_fromInt(_xJ));_xH=new T1(1,I_fromInt(_xL));continue;}}else{_xG=new T1(1,I_fromInt(_xJ));_xH=_xK;continue;}}else{var _xM=E(_xH);if(!_xM._){_xG=_xI;_xH=new T1(1,I_fromInt(_xM.a));continue;}else{return new T1(1,I_mul(_xI.a,_xM.a));}}}},_xN=function(_xO,_xP,_xQ){while(1){if(!(_xP%2)){var _xR=B(_xF(_xO,_xO)),_xS=quot(_xP,2);_xO=_xR;_xP=_xS;continue;}else{var _xT=E(_xP);if(_xT==1){return new F(function(){return _xF(_xO,_xQ);});}else{var _xR=B(_xF(_xO,_xO)),_xU=B(_xF(_xO,_xQ));_xO=_xR;_xP=quot(_xT-1|0,2);_xQ=_xU;continue;}}}},_xV=function(_xW,_xX){while(1){if(!(_xX%2)){var _xY=B(_xF(_xW,_xW)),_xZ=quot(_xX,2);_xW=_xY;_xX=_xZ;continue;}else{var _y0=E(_xX);if(_y0==1){return E(_xW);}else{return new F(function(){return _xN(B(_xF(_xW,_xW)),quot(_y0-1|0,2),_xW);});}}}},_y1=function(_y2){return E(E(_y2).b);},_y3=function(_y4){return E(E(_y4).c);},_y5=new T1(0,0),_y6=function(_y7){return E(E(_y7).d);},_y8=function(_y9,_ya){var _yb=B(_uH(_y9)),_yc=new T(function(){return B(_uJ(_yb));}),_yd=new T(function(){return B(A3(_y6,_y9,_ya,new T(function(){return B(A2(_7U,_yc,_pB));})));});return new F(function(){return A3(_of,B(_o1(B(_y1(_yb)))),_yd,new T(function(){return B(A2(_7U,_yc,_y5));}));});},_ye=new T(function(){return B(unCStr("Negative exponent"));}),_yf=new T(function(){return B(err(_ye));}),_yg=function(_yh){return E(E(_yh).c);},_yi=function(_yj,_yk,_yl,_ym){var _yn=B(_uH(_yk)),_yo=new T(function(){return B(_uJ(_yn));}),_yp=B(_y1(_yn));if(!B(A3(_y3,_yp,_ym,new T(function(){return B(A2(_7U,_yo,_y5));})))){if(!B(A3(_of,B(_o1(_yp)),_ym,new T(function(){return B(A2(_7U,_yo,_y5));})))){var _yq=new T(function(){return B(A2(_7U,_yo,_pB));}),_yr=new T(function(){return B(A2(_7U,_yo,_pr));}),_ys=B(_o1(_yp)),_yt=function(_yu,_yv,_yw){while(1){var _yx=B((function(_yy,_yz,_yA){if(!B(_y8(_yk,_yz))){if(!B(A3(_of,_ys,_yz,_yr))){var _yB=new T(function(){return B(A3(_yg,_yk,new T(function(){return B(A3(_bt,_yo,_yz,_yr));}),_yq));});_yu=new T(function(){return B(A3(_bh,_yj,_yy,_yy));});_yv=_yB;_yw=new T(function(){return B(A3(_bh,_yj,_yy,_yA));});return __continue;}else{return new F(function(){return A3(_bh,_yj,_yy,_yA);});}}else{var _yC=_yA;_yu=new T(function(){return B(A3(_bh,_yj,_yy,_yy));});_yv=new T(function(){return B(A3(_yg,_yk,_yz,_yq));});_yw=_yC;return __continue;}})(_yu,_yv,_yw));if(_yx!=__continue){return _yx;}}},_yD=function(_yE,_yF){while(1){var _yG=B((function(_yH,_yI){if(!B(_y8(_yk,_yI))){if(!B(A3(_of,_ys,_yI,_yr))){var _yJ=new T(function(){return B(A3(_yg,_yk,new T(function(){return B(A3(_bt,_yo,_yI,_yr));}),_yq));});return new F(function(){return _yt(new T(function(){return B(A3(_bh,_yj,_yH,_yH));}),_yJ,_yH);});}else{return E(_yH);}}else{_yE=new T(function(){return B(A3(_bh,_yj,_yH,_yH));});_yF=new T(function(){return B(A3(_yg,_yk,_yI,_yq));});return __continue;}})(_yE,_yF));if(_yG!=__continue){return _yG;}}};return new F(function(){return _yD(_yl,_ym);});}else{return new F(function(){return A2(_7U,_yj,_pr);});}}else{return E(_yf);}},_yK=new T(function(){return B(err(_ye));}),_yL=function(_yM,_yN){var _yO=B(_tD(_yN)),_yP=_yO.a,_yQ=_yO.b,_yR=new T(function(){return B(_uJ(new T(function(){return B(_uH(_yM));})));});if(_yQ<0){var _yS= -_yQ;if(_yS>=0){var _yT=E(_yS);if(!_yT){var _yU=E(_pr);}else{var _yU=B(_xV(_xE,_yT));}if(!B(_38(_yU,_3B))){var _yV=B(_3s(_yP,_yU));return new T2(0,new T(function(){return B(A2(_7U,_yR,_yV.a));}),new T(function(){return B(_34(_yV.b,_yQ));}));}else{return E(_33);}}else{return E(_yK);}}else{var _yW=new T(function(){var _yX=new T(function(){return B(_yi(_yR,_xD,new T(function(){return B(A2(_7U,_yR,_xE));}),_yQ));});return B(A3(_bh,_yR,new T(function(){return B(A2(_7U,_yR,_yP));}),_yX));});return new T2(0,_yW,_6q);}},_yY=function(_yZ,_z0){var _z1=B(_yL(_yZ,E(_z0))),_z2=_z1.a;if(E(_z1.b)<=0){return E(_z2);}else{var _z3=B(_uJ(B(_uH(_yZ))));return new F(function(){return A3(_6Q,_z3,_z2,new T(function(){return B(A2(_7U,_z3,_1U));}));});}},_z4=function(_z5,_z6){var _z7=B(_yL(_z5,E(_z6))),_z8=_z7.a;if(E(_z7.b)>=0){return E(_z8);}else{var _z9=B(_uJ(B(_uH(_z5))));return new F(function(){return A3(_bt,_z9,_z8,new T(function(){return B(A2(_7U,_z9,_1U));}));});}},_za=function(_zb,_zc){var _zd=B(_yL(_zb,E(_zc)));return new T2(0,_zd.a,_zd.b);},_ze=function(_zf,_zg){var _zh=B(_yL(_zf,_zg)),_zi=_zh.a,_zj=E(_zh.b),_zk=new T(function(){var _zl=B(_uJ(B(_uH(_zf))));if(_zj>=0){return B(A3(_6Q,_zl,_zi,new T(function(){return B(A2(_7U,_zl,_1U));})));}else{return B(A3(_bt,_zl,_zi,new T(function(){return B(A2(_7U,_zl,_1U));})));}}),_zm=function(_zn){var _zo=_zn-0.5;return (_zo>=0)?(E(_zo)==0)?(!B(_y8(_zf,_zi)))?E(_zk):E(_zi):E(_zk):E(_zi);},_zp=E(_zj);if(!_zp){return new F(function(){return _zm(0);});}else{if(_zp<=0){var _zq= -_zp-0.5;return (_zq>=0)?(E(_zq)==0)?(!B(_y8(_zf,_zi)))?E(_zk):E(_zi):E(_zk):E(_zi);}else{return new F(function(){return _zm(_zp);});}}},_zr=function(_zs,_zt){return new F(function(){return _ze(_zs,E(_zt));});},_zu=function(_zv,_zw){return E(B(_yL(_zv,E(_zw))).a);},_zx={_:0,a:_uG,b:_lp,c:_za,d:_zu,e:_zr,f:_yY,g:_z4},_zy=new T1(0,1),_zz=function(_zA,_zB){var _zC=E(_zA);return new T2(0,_zC,new T(function(){var _zD=B(_zz(B(_3j(_zC,_zB)),_zB));return new T2(1,_zD.a,_zD.b);}));},_zE=function(_zF){var _zG=B(_zz(_zF,_zy));return new T2(1,_zG.a,_zG.b);},_zH=function(_zI,_zJ){var _zK=B(_zz(_zI,new T(function(){return B(_5E(_zJ,_zI));})));return new T2(1,_zK.a,_zK.b);},_zL=new T1(0,0),_zM=function(_zN,_zO){var _zP=E(_zN);if(!_zP._){var _zQ=_zP.a,_zR=E(_zO);return (_zR._==0)?_zQ>=_zR.a:I_compareInt(_zR.a,_zQ)<=0;}else{var _zS=_zP.a,_zT=E(_zO);return (_zT._==0)?I_compareInt(_zS,_zT.a)>=0:I_compare(_zS,_zT.a)>=0;}},_zU=function(_zV,_zW,_zX){if(!B(_zM(_zW,_zL))){var _zY=function(_zZ){return (!B(_3V(_zZ,_zX)))?new T2(1,_zZ,new T(function(){return B(_zY(B(_3j(_zZ,_zW))));})):__Z;};return new F(function(){return _zY(_zV);});}else{var _A0=function(_A1){return (!B(_3M(_A1,_zX)))?new T2(1,_A1,new T(function(){return B(_A0(B(_3j(_A1,_zW))));})):__Z;};return new F(function(){return _A0(_zV);});}},_A2=function(_A3,_A4,_A5){return new F(function(){return _zU(_A3,B(_5E(_A4,_A3)),_A5);});},_A6=function(_A7,_A8){return new F(function(){return _zU(_A7,_zy,_A8);});},_A9=function(_Aa){return new F(function(){return _3g(_Aa);});},_Ab=function(_Ac){return new F(function(){return _5E(_Ac,_zy);});},_Ad=function(_Ae){return new F(function(){return _3j(_Ae,_zy);});},_Af=function(_Ag){return new F(function(){return _tG(E(_Ag));});},_Ah={_:0,a:_Ad,b:_Ab,c:_Af,d:_A9,e:_zE,f:_zH,g:_A6,h:_A2},_Ai=function(_Aj,_Ak){while(1){var _Al=E(_Aj);if(!_Al._){var _Am=E(_Al.a);if(_Am==(-2147483648)){_Aj=new T1(1,I_fromInt(-2147483648));continue;}else{var _An=E(_Ak);if(!_An._){return new T1(0,B(_vC(_Am,_An.a)));}else{_Aj=new T1(1,I_fromInt(_Am));_Ak=_An;continue;}}}else{var _Ao=_Al.a,_Ap=E(_Ak);return (_Ap._==0)?new T1(1,I_div(_Ao,I_fromInt(_Ap.a))):new T1(1,I_div(_Ao,_Ap.a));}}},_Aq=function(_Ar,_As){if(!B(_38(_As,_y5))){return new F(function(){return _Ai(_Ar,_As);});}else{return E(_33);}},_At=function(_Au,_Av){while(1){var _Aw=E(_Au);if(!_Aw._){var _Ax=E(_Aw.a);if(_Ax==(-2147483648)){_Au=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ay=E(_Av);if(!_Ay._){var _Az=_Ay.a;return new T2(0,new T1(0,B(_vC(_Ax,_Az))),new T1(0,B(_w8(_Ax,_Az))));}else{_Au=new T1(1,I_fromInt(_Ax));_Av=_Ay;continue;}}}else{var _AA=E(_Av);if(!_AA._){_Au=_Aw;_Av=new T1(1,I_fromInt(_AA.a));continue;}else{var _AB=I_divMod(_Aw.a,_AA.a);return new T2(0,new T1(1,_AB.a),new T1(1,_AB.b));}}}},_AC=function(_AD,_AE){if(!B(_38(_AE,_y5))){var _AF=B(_At(_AD,_AE));return new T2(0,_AF.a,_AF.b);}else{return E(_33);}},_AG=function(_AH,_AI){while(1){var _AJ=E(_AH);if(!_AJ._){var _AK=E(_AJ.a);if(_AK==(-2147483648)){_AH=new T1(1,I_fromInt(-2147483648));continue;}else{var _AL=E(_AI);if(!_AL._){return new T1(0,B(_w8(_AK,_AL.a)));}else{_AH=new T1(1,I_fromInt(_AK));_AI=_AL;continue;}}}else{var _AM=_AJ.a,_AN=E(_AI);return (_AN._==0)?new T1(1,I_mod(_AM,I_fromInt(_AN.a))):new T1(1,I_mod(_AM,_AN.a));}}},_AO=function(_AP,_AQ){if(!B(_38(_AQ,_y5))){return new F(function(){return _AG(_AP,_AQ);});}else{return E(_33);}},_AR=function(_AS,_AT){while(1){var _AU=E(_AS);if(!_AU._){var _AV=E(_AU.a);if(_AV==(-2147483648)){_AS=new T1(1,I_fromInt(-2147483648));continue;}else{var _AW=E(_AT);if(!_AW._){return new T1(0,quot(_AV,_AW.a));}else{_AS=new T1(1,I_fromInt(_AV));_AT=_AW;continue;}}}else{var _AX=_AU.a,_AY=E(_AT);return (_AY._==0)?new T1(0,I_toInt(I_quot(_AX,I_fromInt(_AY.a)))):new T1(1,I_quot(_AX,_AY.a));}}},_AZ=function(_B0,_B1){if(!B(_38(_B1,_y5))){return new F(function(){return _AR(_B0,_B1);});}else{return E(_33);}},_B2=function(_B3,_B4){if(!B(_38(_B4,_y5))){var _B5=B(_3s(_B3,_B4));return new T2(0,_B5.a,_B5.b);}else{return E(_33);}},_B6=function(_B7,_B8){while(1){var _B9=E(_B7);if(!_B9._){var _Ba=E(_B9.a);if(_Ba==(-2147483648)){_B7=new T1(1,I_fromInt(-2147483648));continue;}else{var _Bb=E(_B8);if(!_Bb._){return new T1(0,_Ba%_Bb.a);}else{_B7=new T1(1,I_fromInt(_Ba));_B8=_Bb;continue;}}}else{var _Bc=_B9.a,_Bd=E(_B8);return (_Bd._==0)?new T1(1,I_rem(_Bc,I_fromInt(_Bd.a))):new T1(1,I_rem(_Bc,_Bd.a));}}},_Be=function(_Bf,_Bg){if(!B(_38(_Bg,_y5))){return new F(function(){return _B6(_Bf,_Bg);});}else{return E(_33);}},_Bh=function(_Bi){return E(_Bi);},_Bj=function(_Bk){return E(_Bk);},_Bl=function(_Bm){var _Bn=E(_Bm);if(!_Bn._){var _Bo=E(_Bn.a);return (_Bo==(-2147483648))?E(_6i):(_Bo<0)?new T1(0, -_Bo):E(_Bn);}else{var _Bp=_Bn.a;return (I_compareInt(_Bp,0)>=0)?E(_Bn):new T1(1,I_negate(_Bp));}},_Bq=new T1(0,0),_Br=new T1(0,-1),_Bs=function(_Bt){var _Bu=E(_Bt);if(!_Bu._){var _Bv=_Bu.a;return (_Bv>=0)?(E(_Bv)==0)?E(_Bq):E(_3U):E(_Br);}else{var _Bw=I_compareInt(_Bu.a,0);return (_Bw<=0)?(E(_Bw)==0)?E(_Bq):E(_Br):E(_3U);}},_Bx={_:0,a:_3j,b:_5E,c:_xF,d:_6j,e:_Bl,f:_Bs,g:_Bj},_By=function(_Bz,_BA){var _BB=E(_Bz);if(!_BB._){var _BC=_BB.a,_BD=E(_BA);return (_BD._==0)?_BC!=_BD.a:(I_compareInt(_BD.a,_BC)==0)?false:true;}else{var _BE=_BB.a,_BF=E(_BA);return (_BF._==0)?(I_compareInt(_BE,_BF.a)==0)?false:true:(I_compare(_BE,_BF.a)==0)?false:true;}},_BG=new T2(0,_38,_By),_BH=function(_BI,_BJ){return (!B(_5p(_BI,_BJ)))?E(_BI):E(_BJ);},_BK=function(_BL,_BM){return (!B(_5p(_BL,_BM)))?E(_BM):E(_BL);},_BN={_:0,a:_BG,b:_1V,c:_3V,d:_5p,e:_3M,f:_zM,g:_BH,h:_BK},_BO=function(_BP){return new T2(0,E(_BP),E(_pr));},_BQ=new T3(0,_Bx,_BN,_BO),_BR={_:0,a:_BQ,b:_Ah,c:_AZ,d:_Be,e:_Aq,f:_AO,g:_B2,h:_AC,i:_Bh},_BS=function(_BT){return E(E(_BT).b);},_BU=function(_BV){return E(E(_BV).g);},_BW=new T1(0,1),_BX=function(_BY,_BZ,_C0){var _C1=B(_BS(_BY)),_C2=B(_82(_C1)),_C3=new T(function(){var _C4=new T(function(){var _C5=new T(function(){var _C6=new T(function(){return B(A3(_BU,_BY,_BR,new T(function(){return B(A3(_cg,_C1,_BZ,_C0));})));});return B(A2(_7U,_C2,_C6));}),_C7=new T(function(){return B(A2(_6S,_C2,new T(function(){return B(A2(_7U,_C2,_BW));})));});return B(A3(_bh,_C2,_C7,_C5));});return B(A3(_bh,_C2,_C4,_C0));});return new F(function(){return A3(_6Q,_C2,_BZ,_C3);});},_C8=1.5707963267948966,_C9=function(_Ca){return 0.2/Math.cos(B(_BX(_zx,_Ca,_C8))-0.7853981633974483);},_Cb=new T(function(){var _Cc=B(_si(_C9,1.2,_tC,_tC,_tB,_tC,_tC,_tC,_tC,_tC,_tB,_tB,_tB));return {_:0,a:E(_Cc.a),b:E(_Cc.b),c:E(_Cc.c),d:E(_Cc.d),e:E(_Cc.e),f:E(_Cc.f),g:E(_Cc.g),h:_Cc.h,i:_Cc.i,j:_Cc.j};}),_Cd=0,_Ce=0.3,_Cf=function(_Cg){return E(_Ce);},_Ch=new T(function(){var _Ci=B(_si(_Cf,1.2,_tB,_tC,_tB,_tC,_tC,_tC,_tC,_tC,_tB,_tB,_tB));return {_:0,a:E(_Ci.a),b:E(_Ci.b),c:E(_Ci.c),d:E(_Ci.d),e:E(_Ci.e),f:E(_Ci.f),g:E(_Ci.g),h:_Ci.h,i:_Ci.i,j:_Ci.j};}),_Cj=new T(function(){var _Ck=B(_si(_Cf,1.2,_tB,_tB,_tC,_tC,_tC,_tC,_tC,_tC,_tB,_tB,_tB));return {_:0,a:E(_Ck.a),b:E(_Ck.b),c:E(_Ck.c),d:E(_Ck.d),e:E(_Ck.e),f:E(_Ck.f),g:E(_Ck.g),h:_Ck.h,i:_Ck.i,j:_Ck.j};}),_Cl=2,_Cm=function(_Cn){return 0.3/Math.cos(B(_BX(_zx,_Cn,_C8))-0.7853981633974483);},_Co=new T(function(){var _Cp=B(_si(_Cm,1.2,_Cl,_tB,_tB,_tC,_tC,_tC,_tC,_tC,_tB,_tB,_tB));return {_:0,a:E(_Cp.a),b:E(_Cp.b),c:E(_Cp.c),d:E(_Cp.d),e:E(_Cp.e),f:E(_Cp.f),g:E(_Cp.g),h:_Cp.h,i:_Cp.i,j:_Cp.j};}),_Cq=0.5,_Cr=new T(function(){var _Cs=B(_si(_Cf,1.2,_tC,_tB,_Cq,_tC,_tC,_tC,_tC,_tC,_tB,_tB,_tB));return {_:0,a:E(_Cs.a),b:E(_Cs.b),c:E(_Cs.c),d:E(_Cs.d),e:E(_Cs.e),f:E(_Cs.f),g:E(_Cs.g),h:_Cs.h,i:_Cs.i,j:_Cs.j};}),_Ct=new T2(1,_Cr,_w),_Cu=new T2(1,_Co,_Ct),_Cv=new T2(1,_Cj,_Cu),_Cw=new T2(1,_Ch,_Cv),_Cx=new T2(1,_Cb,_Cw),_Cy=new T(function(){return B(unCStr("Negative range size"));}),_Cz=new T(function(){return B(err(_Cy));}),_CA=function(_){var _CB=B(_kf(_Cx,0))-1|0,_CC=function(_CD){if(_CD>=0){var _CE=newArr(_CD,_kl),_CF=_CE,_CG=E(_CD);if(!_CG){return new T4(0,E(_Cd),E(_CB),0,_CF);}else{var _CH=function(_CI,_CJ,_){while(1){var _CK=E(_CI);if(!_CK._){return E(_);}else{var _=_CF[_CJ]=_CK.a;if(_CJ!=(_CG-1|0)){var _CL=_CJ+1|0;_CI=_CK.b;_CJ=_CL;continue;}else{return E(_);}}}},_=B((function(_CM,_CN,_CO,_){var _=_CF[_CO]=_CM;if(_CO!=(_CG-1|0)){return new F(function(){return _CH(_CN,_CO+1|0,_);});}else{return E(_);}})(_Cb,_Cw,0,_));return new T4(0,E(_Cd),E(_CB),_CG,_CF);}}else{return E(_Cz);}};if(0>_CB){return new F(function(){return _CC(0);});}else{return new F(function(){return _CC(_CB+1|0);});}},_CP=function(_CQ){var _CR=B(A1(_CQ,_));return E(_CR);},_CS=new T(function(){return B(_CP(_CA));}),_CT="enclose",_CU="outline",_CV="polygon",_CW="z",_CX="y",_CY="x",_CZ=function(_D0){return new F(function(){return _mD(new T2(1,new T2(0,_CY,new T(function(){return E(E(E(E(_D0).d).a).a);})),new T2(1,new T2(0,_CX,new T(function(){return E(E(E(E(_D0).d).a).b);})),new T2(1,new T2(0,_CW,new T(function(){return E(E(E(E(_D0).d).a).c);})),new T2(1,new T2(0,_CV,new T(function(){return E(_D0).h;})),new T2(1,new T2(0,_CU,new T(function(){return E(_D0).i;})),new T2(1,new T2(0,_CT,new T(function(){return E(_D0).j;})),_w)))))));});},_D1=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_D2=new T(function(){return B(err(_D1));}),_D3=new T(function(){return eval("__strict(drawObjects)");}),_D4=new T(function(){return eval("__strict(draw)");}),_D5=function(_D6,_D7){var _D8=jsShowI(_D6);return new F(function(){return _n(fromJSStr(_D8),_D7);});},_D9=function(_Da,_Db,_Dc){if(_Db>=0){return new F(function(){return _D5(_Db,_Dc);});}else{if(_Da<=6){return new F(function(){return _D5(_Db,_Dc);});}else{return new T2(1,_79,new T(function(){var _Dd=jsShowI(_Db);return B(_n(fromJSStr(_Dd),new T2(1,_78,_Dc)));}));}}},_De=new T(function(){return B(unCStr(")"));}),_Df=function(_Dg,_Dh){var _Di=new T(function(){var _Dj=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_D9(0,_Dg,_w)),_De));})));},1);return B(_n(B(_D9(0,_Dh,_w)),_Dj));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Di)));});},_Dk=new T2(1,_mC,_w),_Dl=function(_Dm){return E(_Dm);},_Dn=function(_Do){return E(_Do);},_Dp=function(_Dq,_Dr){return E(_Dr);},_Ds=function(_Dt,_Du){return E(_Dt);},_Dv=function(_Dw){return E(_Dw);},_Dx=new T2(0,_Dv,_Ds),_Dy=function(_Dz,_DA){return E(_Dz);},_DB=new T5(0,_Dx,_Dn,_Dl,_Dp,_Dy),_DC="flipped2",_DD="flipped1",_DE="c1y",_DF="c1x",_DG="w2z",_DH="w2y",_DI="w2x",_DJ="w1z",_DK="w1y",_DL="w1x",_DM="d2z",_DN="d2y",_DO="d2x",_DP="d1z",_DQ="d1y",_DR="d1x",_DS="c2y",_DT="c2x",_DU=function(_DV,_){var _DW=__get(_DV,E(_DL)),_DX=__get(_DV,E(_DK)),_DY=__get(_DV,E(_DJ)),_DZ=__get(_DV,E(_DI)),_E0=__get(_DV,E(_DH)),_E1=__get(_DV,E(_DG)),_E2=__get(_DV,E(_DF)),_E3=__get(_DV,E(_DE)),_E4=__get(_DV,E(_DT)),_E5=__get(_DV,E(_DS)),_E6=__get(_DV,E(_DR)),_E7=__get(_DV,E(_DQ)),_E8=__get(_DV,E(_DP)),_E9=__get(_DV,E(_DO)),_Ea=__get(_DV,E(_DN)),_Eb=__get(_DV,E(_DM)),_Ec=__get(_DV,E(_DD)),_Ed=__get(_DV,E(_DC));return {_:0,a:E(new T3(0,E(_DW),E(_DX),E(_DY))),b:E(new T3(0,E(_DZ),E(_E0),E(_E1))),c:E(new T2(0,E(_E2),E(_E3))),d:E(new T2(0,E(_E4),E(_E5))),e:E(new T3(0,E(_E6),E(_E7),E(_E8))),f:E(new T3(0,E(_E9),E(_Ea),E(_Eb))),g:E(_Ec),h:E(_Ed)};},_Ee=function(_Ef,_){var _Eg=E(_Ef);if(!_Eg._){return _w;}else{var _Eh=B(_DU(E(_Eg.a),_)),_Ei=B(_Ee(_Eg.b,_));return new T2(1,_Eh,_Ei);}},_Ej=function(_Ek){var _El=E(_Ek);return (E(_El.b)-E(_El.a)|0)+1|0;},_Em=function(_En,_Eo){var _Ep=E(_En),_Eq=E(_Eo);return (E(_Ep.a)>_Eq)?false:_Eq<=E(_Ep.b);},_Er=function(_Es){return new F(function(){return _D9(0,E(_Es),_w);});},_Et=function(_Eu,_Ev,_Ew){return new F(function(){return _D9(E(_Eu),E(_Ev),_Ew);});},_Ex=function(_Ey,_Ez){return new F(function(){return _D9(0,E(_Ey),_Ez);});},_EA=function(_EB,_EC){return new F(function(){return _2J(_Ex,_EB,_EC);});},_ED=new T3(0,_Et,_Er,_EA),_EE=0,_EF=function(_EG,_EH,_EI){return new F(function(){return A1(_EG,new T2(1,_2G,new T(function(){return B(A1(_EH,_EI));})));});},_EJ=new T(function(){return B(unCStr("foldr1"));}),_EK=new T(function(){return B(_oQ(_EJ));}),_EL=function(_EM,_EN){var _EO=E(_EN);if(!_EO._){return E(_EK);}else{var _EP=_EO.a,_EQ=E(_EO.b);if(!_EQ._){return E(_EP);}else{return new F(function(){return A2(_EM,_EP,new T(function(){return B(_EL(_EM,_EQ));}));});}}},_ER=new T(function(){return B(unCStr(" out of range "));}),_ES=new T(function(){return B(unCStr("}.index: Index "));}),_ET=new T(function(){return B(unCStr("Ix{"));}),_EU=new T2(1,_78,_w),_EV=new T2(1,_78,_EU),_EW=0,_EX=function(_EY){return E(E(_EY).a);},_EZ=function(_F0,_F1,_F2,_F3,_F4){var _F5=new T(function(){var _F6=new T(function(){var _F7=new T(function(){var _F8=new T(function(){var _F9=new T(function(){return B(A3(_EL,_EF,new T2(1,new T(function(){return B(A3(_EX,_F2,_EW,_F3));}),new T2(1,new T(function(){return B(A3(_EX,_F2,_EW,_F4));}),_w)),_EV));});return B(_n(_ER,new T2(1,_79,new T2(1,_79,_F9))));});return B(A(_EX,[_F2,_EE,_F1,new T2(1,_78,_F8)]));});return B(_n(_ES,new T2(1,_79,_F7)));},1);return B(_n(_F0,_F6));},1);return new F(function(){return err(B(_n(_ET,_F5)));});},_Fa=function(_Fb,_Fc,_Fd,_Fe,_Ff){return new F(function(){return _EZ(_Fb,_Fc,_Ff,_Fd,_Fe);});},_Fg=function(_Fh,_Fi,_Fj,_Fk){var _Fl=E(_Fj);return new F(function(){return _Fa(_Fh,_Fi,_Fl.a,_Fl.b,_Fk);});},_Fm=function(_Fn,_Fo,_Fp,_Fq){return new F(function(){return _Fg(_Fq,_Fp,_Fo,_Fn);});},_Fr=new T(function(){return B(unCStr("Int"));}),_Fs=function(_Ft,_Fu){return new F(function(){return _Fm(_ED,_Fu,_Ft,_Fr);});},_Fv=function(_Fw,_Fx){var _Fy=E(_Fw),_Fz=E(_Fy.a),_FA=E(_Fx);if(_Fz>_FA){return new F(function(){return _Fs(_FA,_Fy);});}else{if(_FA>E(_Fy.b)){return new F(function(){return _Fs(_FA,_Fy);});}else{return _FA-_Fz|0;}}},_FB=function(_FC){var _FD=E(_FC);return new F(function(){return _vm(_FD.a,_FD.b);});},_FE=function(_FF){var _FG=E(_FF),_FH=E(_FG.a),_FI=E(_FG.b);return (_FH>_FI)?E(_EE):(_FI-_FH|0)+1|0;},_FJ=function(_FK,_FL){return new F(function(){return _wL(_FL,E(_FK).a);});},_FM={_:0,a:_xB,b:_FB,c:_Fv,d:_FJ,e:_Em,f:_FE,g:_Ej},_FN=function(_FO,_FP,_){while(1){var _FQ=B((function(_FR,_FS,_){var _FT=E(_FR);if(!_FT._){return new T2(0,_mC,_FS);}else{var _FU=B(A2(_FT.a,_FS,_));_FO=_FT.b;_FP=new T(function(){return E(E(_FU).b);});return __continue;}})(_FO,_FP,_));if(_FQ!=__continue){return _FQ;}}},_FV=function(_FW,_FX){return new T2(1,_FW,_FX);},_FY=function(_FZ,_G0){var _G1=E(_G0);return new T2(0,_G1.a,_G1.b);},_G2=function(_G3){return E(E(_G3).f);},_G4=function(_G5,_G6,_G7){var _G8=E(_G6),_G9=_G8.a,_Ga=_G8.b,_Gb=function(_){var _Gc=B(A2(_G2,_G5,_G8));if(_Gc>=0){var _Gd=newArr(_Gc,_kl),_Ge=_Gd,_Gf=E(_Gc);if(!_Gf){return new T(function(){return new T4(0,E(_G9),E(_Ga),0,_Ge);});}else{var _Gg=function(_Gh,_Gi,_){while(1){var _Gj=E(_Gh);if(!_Gj._){return E(_);}else{var _=_Ge[_Gi]=_Gj.a;if(_Gi!=(_Gf-1|0)){var _Gk=_Gi+1|0;_Gh=_Gj.b;_Gi=_Gk;continue;}else{return E(_);}}}},_=B(_Gg(_G7,0,_));return new T(function(){return new T4(0,E(_G9),E(_Ga),_Gf,_Ge);});}}else{return E(_Cz);}};return new F(function(){return _CP(_Gb);});},_Gl=function(_Gm,_Gn,_Go,_Gp){var _Gq=new T(function(){var _Gr=E(_Gp),_Gs=_Gr.c-1|0,_Gt=new T(function(){return B(A2(_g0,_Gn,_w));});if(0<=_Gs){var _Gu=new T(function(){return B(_84(_Gn));}),_Gv=function(_Gw){var _Gx=new T(function(){var _Gy=new T(function(){return B(A1(_Go,new T(function(){return E(_Gr.d[_Gw]);})));});return B(A3(_86,_Gu,_FV,_Gy));});return new F(function(){return A3(_ci,_Gn,_Gx,new T(function(){if(_Gw!=_Gs){return B(_Gv(_Gw+1|0));}else{return E(_Gt);}}));});};return B(_Gv(0));}else{return E(_Gt);}}),_Gz=new T(function(){return B(_FY(_Gm,_Gp));});return new F(function(){return A3(_86,B(_84(_Gn)),function(_GA){return new F(function(){return _G4(_Gm,_Gz,_GA);});},_Gq);});},_GB=function(_GC,_GD,_GE,_GF,_GG,_GH,_GI,_GJ,_GK){var _GL=B(_bh(_GC));return new T2(0,new T3(0,E(B(A1(B(A1(_GL,_GD)),_GH))),E(B(A1(B(A1(_GL,_GE)),_GI))),E(B(A1(B(A1(_GL,_GF)),_GJ)))),B(A1(B(A1(_GL,_GG)),_GK)));},_GM=function(_GN,_GO,_GP,_GQ,_GR,_GS,_GT,_GU,_GV){var _GW=B(_6Q(_GN));return new T2(0,new T3(0,E(B(A1(B(A1(_GW,_GO)),_GS))),E(B(A1(B(A1(_GW,_GP)),_GT))),E(B(A1(B(A1(_GW,_GQ)),_GU)))),B(A1(B(A1(_GW,_GR)),_GV)));},_GX=1.0e-2,_GY=function(_GZ,_H0,_H1,_H2,_H3,_H4,_H5,_H6,_H7,_H8,_H9,_Ha,_Hb,_Hc,_Hd,_He,_Hf,_Hg){var _Hh=B(_GB(_ll,_H6,_H7,_H8,_H9,_GX,_GX,_GX,_GX)),_Hi=E(_Hh.a),_Hj=B(_GM(_ll,_H2,_H3,_H4,_H5,_Hi.a,_Hi.b,_Hi.c,_Hh.b)),_Hk=E(_Hj.a);return new F(function(){return _ry(_GZ,_H0,_H1,_Hk.a,_Hk.b,_Hk.c,_Hj.b,_H6,_H7,_H8,_H9,_Ha,_Hb,_Hc,_Hd,_He,_Hf,_Hg);});},_Hl=function(_Hm){var _Hn=E(_Hm),_Ho=E(_Hn.d),_Hp=E(_Ho.a),_Hq=E(_Hn.e),_Hr=E(_Hq.a),_Hs=E(_Hn.f),_Ht=B(_GY(_Hn.a,_Hn.b,_Hn.c,_Hp.a,_Hp.b,_Hp.c,_Ho.b,_Hr.a,_Hr.b,_Hr.c,_Hq.b,_Hs.a,_Hs.b,_Hs.c,_Hn.g,_Hn.h,_Hn.i,_Hn.j));return {_:0,a:E(_Ht.a),b:E(_Ht.b),c:E(_Ht.c),d:E(_Ht.d),e:E(_Ht.e),f:E(_Ht.f),g:E(_Ht.g),h:_Ht.h,i:_Ht.i,j:_Ht.j};},_Hu=function(_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD){var _HE=B(_82(B(_80(_Hv))));return new F(function(){return A3(_6Q,_HE,new T(function(){return B(_bj(_Hv,_Hw,_Hx,_Hy,_HA,_HB,_HC));}),new T(function(){return B(A3(_bh,_HE,_Hz,_HD));}));});},_HF=new T(function(){return B(unCStr("base"));}),_HG=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_HH=new T(function(){return B(unCStr("IOException"));}),_HI=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_HF,_HG,_HH),_HJ=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_HI,_w,_w),_HK=function(_HL){return E(_HJ);},_HM=function(_HN){var _HO=E(_HN);return new F(function(){return _2g(B(_2e(_HO.a)),_HK,_HO.b);});},_HP=new T(function(){return B(unCStr(": "));}),_HQ=new T(function(){return B(unCStr(")"));}),_HR=new T(function(){return B(unCStr(" ("));}),_HS=new T(function(){return B(unCStr("interrupted"));}),_HT=new T(function(){return B(unCStr("system error"));}),_HU=new T(function(){return B(unCStr("unsatisified constraints"));}),_HV=new T(function(){return B(unCStr("user error"));}),_HW=new T(function(){return B(unCStr("permission denied"));}),_HX=new T(function(){return B(unCStr("illegal operation"));}),_HY=new T(function(){return B(unCStr("end of file"));}),_HZ=new T(function(){return B(unCStr("resource exhausted"));}),_I0=new T(function(){return B(unCStr("resource busy"));}),_I1=new T(function(){return B(unCStr("does not exist"));}),_I2=new T(function(){return B(unCStr("already exists"));}),_I3=new T(function(){return B(unCStr("resource vanished"));}),_I4=new T(function(){return B(unCStr("timeout"));}),_I5=new T(function(){return B(unCStr("unsupported operation"));}),_I6=new T(function(){return B(unCStr("hardware fault"));}),_I7=new T(function(){return B(unCStr("inappropriate type"));}),_I8=new T(function(){return B(unCStr("invalid argument"));}),_I9=new T(function(){return B(unCStr("failed"));}),_Ia=new T(function(){return B(unCStr("protocol error"));}),_Ib=function(_Ic,_Id){switch(E(_Ic)){case 0:return new F(function(){return _n(_I2,_Id);});break;case 1:return new F(function(){return _n(_I1,_Id);});break;case 2:return new F(function(){return _n(_I0,_Id);});break;case 3:return new F(function(){return _n(_HZ,_Id);});break;case 4:return new F(function(){return _n(_HY,_Id);});break;case 5:return new F(function(){return _n(_HX,_Id);});break;case 6:return new F(function(){return _n(_HW,_Id);});break;case 7:return new F(function(){return _n(_HV,_Id);});break;case 8:return new F(function(){return _n(_HU,_Id);});break;case 9:return new F(function(){return _n(_HT,_Id);});break;case 10:return new F(function(){return _n(_Ia,_Id);});break;case 11:return new F(function(){return _n(_I9,_Id);});break;case 12:return new F(function(){return _n(_I8,_Id);});break;case 13:return new F(function(){return _n(_I7,_Id);});break;case 14:return new F(function(){return _n(_I6,_Id);});break;case 15:return new F(function(){return _n(_I5,_Id);});break;case 16:return new F(function(){return _n(_I4,_Id);});break;case 17:return new F(function(){return _n(_I3,_Id);});break;default:return new F(function(){return _n(_HS,_Id);});}},_Ie=new T(function(){return B(unCStr("}"));}),_If=new T(function(){return B(unCStr("{handle: "));}),_Ig=function(_Ih,_Ii,_Ij,_Ik,_Il,_Im){var _In=new T(function(){var _Io=new T(function(){var _Ip=new T(function(){var _Iq=E(_Ik);if(!_Iq._){return E(_Im);}else{var _Ir=new T(function(){return B(_n(_Iq,new T(function(){return B(_n(_HQ,_Im));},1)));},1);return B(_n(_HR,_Ir));}},1);return B(_Ib(_Ii,_Ip));}),_Is=E(_Ij);if(!_Is._){return E(_Io);}else{return B(_n(_Is,new T(function(){return B(_n(_HP,_Io));},1)));}}),_It=E(_Il);if(!_It._){var _Iu=E(_Ih);if(!_Iu._){return E(_In);}else{var _Iv=E(_Iu.a);if(!_Iv._){var _Iw=new T(function(){var _Ix=new T(function(){return B(_n(_Ie,new T(function(){return B(_n(_HP,_In));},1)));},1);return B(_n(_Iv.a,_Ix));},1);return new F(function(){return _n(_If,_Iw);});}else{var _Iy=new T(function(){var _Iz=new T(function(){return B(_n(_Ie,new T(function(){return B(_n(_HP,_In));},1)));},1);return B(_n(_Iv.a,_Iz));},1);return new F(function(){return _n(_If,_Iy);});}}}else{return new F(function(){return _n(_It.a,new T(function(){return B(_n(_HP,_In));},1));});}},_IA=function(_IB){var _IC=E(_IB);return new F(function(){return _Ig(_IC.a,_IC.b,_IC.c,_IC.d,_IC.f,_w);});},_ID=function(_IE,_IF,_IG){var _IH=E(_IF);return new F(function(){return _Ig(_IH.a,_IH.b,_IH.c,_IH.d,_IH.f,_IG);});},_II=function(_IJ,_IK){var _IL=E(_IJ);return new F(function(){return _Ig(_IL.a,_IL.b,_IL.c,_IL.d,_IL.f,_IK);});},_IM=function(_IN,_IO){return new F(function(){return _2J(_II,_IN,_IO);});},_IP=new T3(0,_ID,_IA,_IM),_IQ=new T(function(){return new T5(0,_HK,_IP,_IR,_HM,_IA);}),_IR=function(_IS){return new T2(0,_IQ,_IS);},_IT=__Z,_IU=7,_IV=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_IW=new T6(0,_IT,_IU,_w,_IV,_IT,_IT),_IX=new T(function(){return B(_IR(_IW));}),_IY=function(_){return new F(function(){return die(_IX);});},_IZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_J0=new T6(0,_IT,_IU,_w,_IZ,_IT,_IT),_J1=new T(function(){return B(_IR(_J0));}),_J2=function(_){return new F(function(){return die(_J1);});},_J3=function(_J4,_){return new T2(0,_w,_J4);},_J5=0.6,_J6=1,_J7=new T(function(){return B(unCStr(")"));}),_J8=function(_J9,_Ja){var _Jb=new T(function(){var _Jc=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_D9(0,_J9,_w)),_J7));})));},1);return B(_n(B(_D9(0,_Ja,_w)),_Jc));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Jb)));});},_Jd=function(_Je,_Jf){var _Jg=new T(function(){var _Jh=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_D9(0,_Jf,_w)),_J7));})));},1);return B(_n(B(_D9(0,_Je,_w)),_Jh));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Jg)));});},_Ji=function(_Jj){var _Jk=E(_Jj);if(!_Jk._){return E(_J3);}else{var _Jl=new T(function(){return B(_Ji(_Jk.b));}),_Jm=function(_Jn){var _Jo=E(_Jn);if(!_Jo._){return E(_Jl);}else{var _Jp=_Jo.a,_Jq=new T(function(){return B(_Jm(_Jo.b));}),_Jr=new T(function(){return 0.1*E(E(_Jp).e)/1.0e-2;}),_Js=new T(function(){var _Jt=E(_Jp);if(_Jt.a!=_Jt.b){return E(_J6);}else{return E(_J5);}}),_Ju=function(_Jv,_){var _Jw=E(_Jv),_Jx=_Jw.c,_Jy=_Jw.d,_Jz=E(_Jw.a),_JA=E(_Jw.b),_JB=E(_Jp),_JC=_JB.a,_JD=_JB.b,_JE=E(_JB.c),_JF=_JE.b,_JG=E(_JE.a),_JH=_JG.a,_JI=_JG.b,_JJ=_JG.c,_JK=E(_JB.d),_JL=_JK.b,_JM=E(_JK.a),_JN=_JM.a,_JO=_JM.b,_JP=_JM.c;if(_Jz>_JC){return new F(function(){return _J2(_);});}else{if(_JC>_JA){return new F(function(){return _J2(_);});}else{if(_Jz>_JD){return new F(function(){return _IY(_);});}else{if(_JD>_JA){return new F(function(){return _IY(_);});}else{var _JQ=_JC-_Jz|0;if(0>_JQ){return new F(function(){return _J8(_Jx,_JQ);});}else{if(_JQ>=_Jx){return new F(function(){return _J8(_Jx,_JQ);});}else{var _JR=E(_Jy[_JQ]),_JS=E(_JR.c),_JT=_JS.b,_JU=E(_JS.a),_JV=_JU.a,_JW=_JU.b,_JX=_JU.c,_JY=E(_JR.e),_JZ=E(_JY.a),_K0=B(_GB(_ll,_JH,_JI,_JJ,_JF,_JV,_JW,_JX,_JT)),_K1=E(_K0.a),_K2=B(_GB(_ll,_K1.a,_K1.b,_K1.c,_K0.b,_JH,_JI,_JJ,_JF)),_K3=E(_K2.a),_K4=_JD-_Jz|0;if(0>_K4){return new F(function(){return _Jd(_K4,_Jx);});}else{if(_K4>=_Jx){return new F(function(){return _Jd(_K4,_Jx);});}else{var _K5=E(_Jy[_K4]),_K6=E(_K5.c),_K7=_K6.b,_K8=E(_K6.a),_K9=_K8.a,_Ka=_K8.b,_Kb=_K8.c,_Kc=E(_K5.e),_Kd=E(_Kc.a),_Ke=B(_GB(_ll,_JN,_JO,_JP,_JL,_K9,_Ka,_Kb,_K7)),_Kf=E(_Ke.a),_Kg=B(_GB(_ll,_Kf.a,_Kf.b,_Kf.c,_Ke.b,_JN,_JO,_JP,_JL)),_Kh=E(_Kg.a),_Ki=E(_K3.a)+E(_K3.b)+E(_K3.c)+E(_K2.b)+E(_Kh.a)+E(_Kh.b)+E(_Kh.c)+E(_Kg.b);if(!_Ki){var _Kj=B(A2(_Jq,_Jw,_));return new T2(0,new T2(1,_mC,new T(function(){return E(E(_Kj).a);})),new T(function(){return E(E(_Kj).b);}));}else{var _Kk=new T(function(){return  -((B(_Hu(_lR,_JZ.a,_JZ.b,_JZ.c,_JY.b,_JH,_JI,_JJ,_JF))-B(_Hu(_lR,_Kd.a,_Kd.b,_Kd.c,_Kc.b,_JN,_JO,_JP,_JL))-E(_Jr))/_Ki);}),_Kl=function(_Km,_Kn,_Ko,_Kp,_){var _Kq=new T(function(){var _Kr=function(_Ks,_Kt,_Ku,_Kv,_Kw){if(_Ks>_JD){return E(_Kw);}else{if(_JD>_Kt){return E(_Kw);}else{var _Kx=function(_){var _Ky=newArr(_Ku,_kl),_Kz=_Ky,_KA=function(_KB,_){while(1){if(_KB!=_Ku){var _=_Kz[_KB]=_Kv[_KB],_KC=_KB+1|0;_KB=_KC;continue;}else{return E(_);}}},_=B(_KA(0,_)),_KD=_JD-_Ks|0;if(0>_KD){return new F(function(){return _Jd(_KD,_Ku);});}else{if(_KD>=_Ku){return new F(function(){return _Jd(_KD,_Ku);});}else{var _=_Kz[_KD]=new T(function(){var _KE=E(_Kv[_KD]),_KF=E(_KE.e),_KG=E(_KF.a),_KH=B(_GB(_ll,_K9,_Ka,_Kb,_K7,_JN,_JO,_JP,_JL)),_KI=E(_KH.a),_KJ=E(_Kk)*E(_Js),_KK=B(_GB(_ll,_KI.a,_KI.b,_KI.c,_KH.b,_KJ,_KJ,_KJ,_KJ)),_KL=E(_KK.a),_KM=B(_GM(_ll,_KG.a,_KG.b,_KG.c,_KF.b, -E(_KL.a), -E(_KL.b), -E(_KL.c), -E(_KK.b)));return {_:0,a:E(_KE.a),b:E(_KE.b),c:E(_KE.c),d:E(_KE.d),e:E(new T2(0,E(_KM.a),E(_KM.b))),f:E(_KE.f),g:E(_KE.g),h:_KE.h,i:_KE.i,j:_KE.j};});return new T4(0,E(_Ks),E(_Kt),_Ku,_Kz);}}};return new F(function(){return _CP(_Kx);});}}};if(_Km>_JC){return B(_Kr(_Km,_Kn,_Ko,_Kp,new T4(0,E(_Km),E(_Kn),_Ko,_Kp)));}else{if(_JC>_Kn){return B(_Kr(_Km,_Kn,_Ko,_Kp,new T4(0,E(_Km),E(_Kn),_Ko,_Kp)));}else{var _KN=function(_){var _KO=newArr(_Ko,_kl),_KP=_KO,_KQ=function(_KR,_){while(1){if(_KR!=_Ko){var _=_KP[_KR]=_Kp[_KR],_KS=_KR+1|0;_KR=_KS;continue;}else{return E(_);}}},_=B(_KQ(0,_)),_KT=_JC-_Km|0;if(0>_KT){return new F(function(){return _J8(_Ko,_KT);});}else{if(_KT>=_Ko){return new F(function(){return _J8(_Ko,_KT);});}else{var _=_KP[_KT]=new T(function(){var _KU=E(_Kp[_KT]),_KV=E(_KU.e),_KW=E(_KV.a),_KX=B(_GB(_ll,_JV,_JW,_JX,_JT,_JH,_JI,_JJ,_JF)),_KY=E(_KX.a),_KZ=E(_Kk)*E(_Js),_L0=B(_GB(_ll,_KY.a,_KY.b,_KY.c,_KX.b,_KZ,_KZ,_KZ,_KZ)),_L1=E(_L0.a),_L2=B(_GM(_ll,_KW.a,_KW.b,_KW.c,_KV.b,_L1.a,_L1.b,_L1.c,_L0.b));return {_:0,a:E(_KU.a),b:E(_KU.b),c:E(_KU.c),d:E(_KU.d),e:E(new T2(0,E(_L2.a),E(_L2.b))),f:E(_KU.f),g:E(_KU.g),h:_KU.h,i:_KU.i,j:_KU.j};});return new T4(0,E(_Km),E(_Kn),_Ko,_KP);}}},_L3=B(_CP(_KN));return B(_Kr(E(_L3.a),E(_L3.b),_L3.c,_L3.d,_L3));}}});return new T2(0,_mC,_Kq);};if(!E(_JB.f)){var _L4=B(_Kl(_Jz,_JA,_Jx,_Jy,_)),_L5=B(A2(_Jq,new T(function(){return E(E(_L4).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_L4).a);}),new T(function(){return E(E(_L5).a);})),new T(function(){return E(E(_L5).b);}));}else{if(E(_Kk)<0){var _L6=B(A2(_Jq,_Jw,_));return new T2(0,new T2(1,_mC,new T(function(){return E(E(_L6).a);})),new T(function(){return E(E(_L6).b);}));}else{var _L7=B(_Kl(_Jz,_JA,_Jx,_Jy,_)),_L8=B(A2(_Jq,new T(function(){return E(E(_L7).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_L7).a);}),new T(function(){return E(E(_L8).a);})),new T(function(){return E(E(_L8).b);}));}}}}}}}}}}}};return E(_Ju);}};return new F(function(){return _Jm(_Jk.a);});}},_L9=function(_,_La){var _Lb=new T(function(){return B(_Ji(E(_La).a));}),_Lc=function(_Ld){var _Le=E(_Ld);return (_Le==1)?E(new T2(1,_Lb,_w)):new T2(1,_Lb,new T(function(){return B(_Lc(_Le-1|0));}));},_Lf=B(_FN(B(_Lc(5)),new T(function(){return E(E(_La).b);}),_)),_Lg=new T(function(){return B(_Gl(_FM,_DB,_Hl,new T(function(){return E(E(_Lf).b);})));});return new T2(0,_mC,_Lg);},_Lh=function(_Li,_Lj,_Lk,_Ll,_Lm){var _Ln=B(_82(B(_80(_Li))));return new F(function(){return A3(_6Q,_Ln,new T(function(){return B(A3(_bh,_Ln,_Lj,_Ll));}),new T(function(){return B(A3(_bh,_Ln,_Lk,_Lm));}));});},_Lo=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Lp=new T6(0,_IT,_IU,_w,_Lo,_IT,_IT),_Lq=new T(function(){return B(_IR(_Lp));}),_Lr=function(_){return new F(function(){return die(_Lq);});},_Ls=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Lt=new T6(0,_IT,_IU,_w,_Ls,_IT,_IT),_Lu=new T(function(){return B(_IR(_Lt));}),_Lv=function(_){return new F(function(){return die(_Lu);});},_Lw=false,_Lx=true,_Ly=function(_Lz){var _LA=E(_Lz),_LB=_LA.b,_LC=E(_LA.d),_LD=E(_LA.e),_LE=E(_LD.a),_LF=E(_LA.g),_LG=B(A1(_LB,_LC.a)),_LH=B(_o3(_lR,_LG.a,_LG.b,_LG.c,_LF.a,_LF.b,_LF.c));return {_:0,a:E(_LA.a),b:E(_LB),c:E(_LA.c),d:E(_LC),e:E(new T2(0,E(new T3(0,E(_LE.a)+E(_LH.a)*1.0e-2,E(_LE.b)+E(_LH.b)*1.0e-2,E(_LE.c)+E(_LH.c)*1.0e-2)),E(_LD.b))),f:E(_LA.f),g:E(_LF),h:_LA.h,i:_LA.i,j:_LA.j};},_LI=new T(function(){return eval("__strict(collideBound)");}),_LJ=new T(function(){return eval("__strict(mouseContact)");}),_LK=new T(function(){return eval("__strict(collide)");}),_LL=function(_LM){var _LN=E(_LM);if(!_LN._){return __Z;}else{return new F(function(){return _n(_LN.a,new T(function(){return B(_LL(_LN.b));},1));});}},_LO=0,_LP=new T3(0,E(_LO),E(_LO),E(_LO)),_LQ=new T2(0,E(_LP),E(_LO)),_LR=new T2(0,_lR,_mq),_LS=new T(function(){return B(_jR(_LR));}),_LT=function(_LU,_){var _LV=B(_Gl(_FM,_DB,_Ly,_LU)),_LW=E(_LV.a),_LX=E(_LV.b);if(_LW<=_LX){var _LY=function(_LZ,_M0,_M1,_M2,_M3,_){if(_M0>_LZ){return new F(function(){return _Lv(_);});}else{if(_LZ>_M1){return new F(function(){return _Lv(_);});}else{var _M4=new T(function(){var _M5=_LZ-_M0|0;if(0>_M5){return B(_Jd(_M5,_M2));}else{if(_M5>=_M2){return B(_Jd(_M5,_M2));}else{return E(_M3[_M5]);}}}),_M6=function(_M7,_M8,_M9,_Ma,_Mb,_){var _Mc=E(_M7);if(!_Mc._){return new T2(0,_w,new T4(0,E(_M8),E(_M9),_Ma,_Mb));}else{var _Md=E(_Mc.a);if(_M8>_Md){return new F(function(){return _Lr(_);});}else{if(_Md>_M9){return new F(function(){return _Lr(_);});}else{var _Me=_Md-_M8|0;if(0>_Me){return new F(function(){return _J8(_Ma,_Me);});}else{if(_Me>=_Ma){return new F(function(){return _J8(_Ma,_Me);});}else{var _Mf=__app2(E(_LK),B(_CZ(E(_M4))),B(_CZ(E(_Mb[_Me])))),_Mg=__arr2lst(0,_Mf),_Mh=B(_Ee(_Mg,_)),_Mi=B(_M6(_Mc.b,_M8,_M9,_Ma,_Mb,_)),_Mj=new T(function(){var _Mk=new T(function(){return _LZ!=_Md;}),_Ml=function(_Mm){var _Mn=E(_Mm);if(!_Mn._){return __Z;}else{var _Mo=_Mn.b,_Mp=E(_Mn.a),_Mq=E(_Mp.b),_Mr=E(_Mp.a),_Ms=E(_Mp.c),_Mt=_Ms.a,_Mu=_Ms.b,_Mv=E(_Mp.e),_Mw=E(_Mp.d),_Mx=_Mw.a,_My=_Mw.b,_Mz=E(_Mp.f),_MA=new T(function(){var _MB=B(_ng(_lR,_Mz.a,_Mz.b,_Mz.c)),_MC=Math.sqrt(B(_Lh(_lR,_Mx,_My,_Mx,_My)));return new T3(0,_MC*E(_MB.a),_MC*E(_MB.b),_MC*E(_MB.c));}),_MD=new T(function(){var _ME=B(_ng(_lR,_Mv.a,_Mv.b,_Mv.c)),_MF=Math.sqrt(B(_Lh(_lR,_Mt,_Mu,_Mt,_Mu)));return new T3(0,_MF*E(_ME.a),_MF*E(_ME.b),_MF*E(_ME.c));}),_MG=new T(function(){var _MH=B(A1(_LS,_Mq)),_MI=B(_ng(_lR,_MH.a,_MH.b,_MH.c));return new T3(0,E(_MI.a),E(_MI.b),E(_MI.c));}),_MJ=new T(function(){var _MK=B(A1(_LS,_Mr)),_ML=B(_ng(_lR,_MK.a,_MK.b,_MK.c));return new T3(0,E(_ML.a),E(_ML.b),E(_ML.c));}),_MM=E(_Mq.a)+ -E(_Mr.a),_MN=E(_Mq.b)+ -E(_Mr.b),_MO=E(_Mq.c)+ -E(_Mr.c),_MP=new T(function(){return Math.sqrt(B(_bj(_lR,_MM,_MN,_MO,_MM,_MN,_MO)));}),_MQ=new T(function(){var _MR=1/E(_MP);return new T3(0,_MM*_MR,_MN*_MR,_MO*_MR);}),_MS=new T(function(){if(!E(_Mp.g)){return E(_MQ);}else{var _MT=E(_MQ);return new T3(0,-1*E(_MT.a),-1*E(_MT.b),-1*E(_MT.c));}}),_MU=new T(function(){if(!E(_Mp.h)){return E(_MQ);}else{var _MV=E(_MQ);return new T3(0,-1*E(_MV.a),-1*E(_MV.b),-1*E(_MV.c));}});return (!E(_Mk))?new T2(1,new T(function(){var _MW=E(_MS),_MX=E(_MW.b),_MY=E(_MW.c),_MZ=E(_MW.a),_N0=E(_MJ),_N1=E(_N0.c),_N2=E(_N0.b),_N3=E(_N0.a),_N4=E(_MD),_N5=E(_N4.c),_N6=E(_N4.b),_N7=E(_N4.a),_N8=_MX*_N1-_N2*_MY,_N9=_MY*_N3-_N1*_MZ,_Na=_MZ*_N2-_N3*_MX,_Nb=B(_bj(_lR,_N9*_N5-_N6*_Na,_Na*_N7-_N5*_N8,_N8*_N6-_N7*_N9,_N3,_N2,_N1));return new T6(0,_LZ,_Md,E(new T2(0,E(new T3(0,E(_N8),E(_N9),E(_Na))),E(_Nb))),E(_LQ),_MP,_Lw);}),new T2(1,new T(function(){var _Nc=E(_MU),_Nd=E(_Nc.b),_Ne=E(_Nc.c),_Nf=E(_Nc.a),_Ng=E(_MG),_Nh=E(_Ng.c),_Ni=E(_Ng.b),_Nj=E(_Ng.a),_Nk=E(_MA),_Nl=E(_Nk.c),_Nm=E(_Nk.b),_Nn=E(_Nk.a),_No=_Nd*_Nh-_Ni*_Ne,_Np=_Ne*_Nj-_Nh*_Nf,_Nq=_Nf*_Ni-_Nj*_Nd,_Nr=B(_bj(_lR,_Np*_Nl-_Nm*_Nq,_Nq*_Nn-_Nl*_No,_No*_Nm-_Nn*_Np,_Nj,_Ni,_Nh));return new T6(0,_LZ,_Md,E(_LQ),E(new T2(0,E(new T3(0,E(_No),E(_Np),E(_Nq))),E(_Nr))),_MP,_Lw);}),new T(function(){return B(_Ml(_Mo));}))):new T2(1,new T(function(){var _Ns=E(_MS),_Nt=E(_Ns.b),_Nu=E(_Ns.c),_Nv=E(_Ns.a),_Nw=E(_MJ),_Nx=_Nw.a,_Ny=_Nw.b,_Nz=_Nw.c,_NA=B(_o3(_lR,_Nv,_Nt,_Nu,_Nx,_Ny,_Nz)),_NB=E(_MD),_NC=E(_NB.c),_ND=E(_NB.b),_NE=E(_NB.a),_NF=B(_bj(_lR,_Nt*_NC-_ND*_Nu,_Nu*_NE-_NC*_Nv,_Nv*_ND-_NE*_Nt,_Nx,_Ny,_Nz)),_NG=E(_MU),_NH=E(_NG.b),_NI=E(_NG.c),_NJ=E(_NG.a),_NK=E(_MG),_NL=_NK.a,_NM=_NK.b,_NN=_NK.c,_NO=B(_o3(_lR,_NJ,_NH,_NI,_NL,_NM,_NN)),_NP=E(_MA),_NQ=E(_NP.c),_NR=E(_NP.b),_NS=E(_NP.a),_NT=B(_bj(_lR,_NH*_NQ-_NR*_NI,_NI*_NS-_NQ*_NJ,_NJ*_NR-_NS*_NH,_NL,_NM,_NN));return new T6(0,_LZ,_Md,E(new T2(0,E(new T3(0,E(_NA.a),E(_NA.b),E(_NA.c))),E(_NF))),E(new T2(0,E(new T3(0,E(_NO.a),E(_NO.b),E(_NO.c))),E(_NT))),_MP,_Lx);}),new T(function(){return B(_Ml(_Mo));}));}};return B(_Ml(_Mh));});return new T2(0,new T2(1,_Mj,new T(function(){return E(E(_Mi).a);})),new T(function(){return E(E(_Mi).b);}));}}}}}},_NU=B(_M6(B(_uL(_LZ,_LX)),_M0,_M1,_M2,_M3,_)),_NV=E(_M4),_NW=E(_NV.d).a,_NX=__app1(E(_LI),B(_CZ(_NV))),_NY=__arr2lst(0,_NX),_NZ=B(_Ee(_NY,_)),_O0=__app1(E(_LJ),_LZ),_O1=__arr2lst(0,_O0),_O2=B(_Ee(_O1,_));if(_LZ!=_LX){var _O3=E(_NU),_O4=E(_O3.b),_O5=B(_LY(_LZ+1|0,E(_O4.a),E(_O4.b),_O4.c,_O4.d,_)),_O6=new T(function(){var _O7=new T(function(){var _O8=B(A1(_LS,_NW)),_O9=B(_ng(_lR,_O8.a,_O8.b,_O8.c));return new T3(0,E(_O9.a),E(_O9.b),E(_O9.c));}),_Oa=new T(function(){var _Ob=new T(function(){return B(_LL(_O3.a));}),_Oc=function(_Od){var _Oe=E(_Od);if(!_Oe._){return E(_Ob);}else{var _Of=E(_Oe.a),_Og=E(_Of.b),_Oh=E(_Of.a),_Oi=E(_Of.c),_Oj=_Oi.a,_Ok=_Oi.b,_Ol=E(_Of.e);return new T2(1,new T(function(){var _Om=E(_Og.a)+ -E(_Oh.a),_On=E(_Og.b)+ -E(_Oh.b),_Oo=E(_Og.c)+ -E(_Oh.c),_Op=B(A1(_LS,_Oh)),_Oq=B(_ng(_lR,_Op.a,_Op.b,_Op.c)),_Or=_Oq.a,_Os=_Oq.b,_Ot=_Oq.c,_Ou=Math.sqrt(B(_bj(_lR,_Om,_On,_Oo,_Om,_On,_Oo))),_Ov=1/_Ou,_Ow=_Om*_Ov,_Ox=_On*_Ov,_Oy=_Oo*_Ov,_Oz=B(_o3(_lR,_Ow,_Ox,_Oy,_Or,_Os,_Ot)),_OA=B(_ng(_lR,_Ol.a,_Ol.b,_Ol.c)),_OB=Math.sqrt(B(_Lh(_lR,_Oj,_Ok,_Oj,_Ok))),_OC=_OB*E(_OA.a),_OD=_OB*E(_OA.b),_OE=_OB*E(_OA.c),_OF=B(_bj(_lR,_Ox*_OE-_OD*_Oy,_Oy*_OC-_OE*_Ow,_Ow*_OD-_OC*_Ox,_Or,_Os,_Ot));return new T6(0,_LZ,_LZ,E(new T2(0,E(new T3(0,E(_Oz.a),E(_Oz.b),E(_Oz.c))),E(_OF))),E(_LQ),_Ou,_Lx);}),new T(function(){return B(_Oc(_Oe.b));}));}};return B(_Oc(_NZ));}),_OG=function(_OH){var _OI=E(_OH);if(!_OI._){return E(_Oa);}else{var _OJ=E(_OI.a),_OK=E(_OJ.b),_OL=new T(function(){var _OM=E(_NW),_ON=E(_OK.c)+ -E(_OM.c),_OO=E(_OK.b)+ -E(_OM.b),_OP=E(_OK.a)+ -E(_OM.a),_OQ=Math.sqrt(B(_bj(_lR,_OP,_OO,_ON,_OP,_OO,_ON))),_OR=function(_OS,_OT,_OU){var _OV=E(_O7),_OW=_OV.a,_OX=_OV.b,_OY=_OV.c,_OZ=B(_o3(_lR,_OS,_OT,_OU,_OW,_OX,_OY)),_P0=B(_bj(_lR,_OT*0-0*_OU,_OU*0-0*_OS,_OS*0-0*_OT,_OW,_OX,_OY));return new T6(0,_LZ,_LZ,new T2(0,E(new T3(0,E(_OZ.a),E(_OZ.b),E(_OZ.c))),E(_P0)),_LQ,_OQ,_Lx);};if(!E(_OJ.g)){var _P1=1/_OQ,_P2=B(_OR(_OP*_P1,_OO*_P1,_ON*_P1));return new T6(0,_P2.a,_P2.b,E(_P2.c),E(_P2.d),_P2.e,_P2.f);}else{var _P3=1/_OQ,_P4=B(_OR(-1*_OP*_P3,-1*_OO*_P3,-1*_ON*_P3));return new T6(0,_P4.a,_P4.b,E(_P4.c),E(_P4.d),_P4.e,_P4.f);}});return new T2(1,_OL,new T(function(){return B(_OG(_OI.b));}));}};return B(_OG(_O2));});return new T2(0,new T2(1,_O6,new T(function(){return E(E(_O5).a);})),new T(function(){return E(E(_O5).b);}));}else{var _P5=new T(function(){var _P6=new T(function(){var _P7=B(A1(_LS,_NW)),_P8=B(_ng(_lR,_P7.a,_P7.b,_P7.c));return new T3(0,E(_P8.a),E(_P8.b),E(_P8.c));}),_P9=new T(function(){var _Pa=new T(function(){return B(_LL(E(_NU).a));}),_Pb=function(_Pc){var _Pd=E(_Pc);if(!_Pd._){return E(_Pa);}else{var _Pe=E(_Pd.a),_Pf=E(_Pe.b),_Pg=E(_Pe.a),_Ph=E(_Pe.c),_Pi=_Ph.a,_Pj=_Ph.b,_Pk=E(_Pe.e);return new T2(1,new T(function(){var _Pl=E(_Pf.a)+ -E(_Pg.a),_Pm=E(_Pf.b)+ -E(_Pg.b),_Pn=E(_Pf.c)+ -E(_Pg.c),_Po=B(A1(_LS,_Pg)),_Pp=B(_ng(_lR,_Po.a,_Po.b,_Po.c)),_Pq=_Pp.a,_Pr=_Pp.b,_Ps=_Pp.c,_Pt=Math.sqrt(B(_bj(_lR,_Pl,_Pm,_Pn,_Pl,_Pm,_Pn))),_Pu=1/_Pt,_Pv=_Pl*_Pu,_Pw=_Pm*_Pu,_Px=_Pn*_Pu,_Py=B(_o3(_lR,_Pv,_Pw,_Px,_Pq,_Pr,_Ps)),_Pz=B(_ng(_lR,_Pk.a,_Pk.b,_Pk.c)),_PA=Math.sqrt(B(_Lh(_lR,_Pi,_Pj,_Pi,_Pj))),_PB=_PA*E(_Pz.a),_PC=_PA*E(_Pz.b),_PD=_PA*E(_Pz.c),_PE=B(_bj(_lR,_Pw*_PD-_PC*_Px,_Px*_PB-_PD*_Pv,_Pv*_PC-_PB*_Pw,_Pq,_Pr,_Ps));return new T6(0,_LZ,_LZ,E(new T2(0,E(new T3(0,E(_Py.a),E(_Py.b),E(_Py.c))),E(_PE))),E(_LQ),_Pt,_Lx);}),new T(function(){return B(_Pb(_Pd.b));}));}};return B(_Pb(_NZ));}),_PF=function(_PG){var _PH=E(_PG);if(!_PH._){return E(_P9);}else{var _PI=E(_PH.a),_PJ=E(_PI.b),_PK=new T(function(){var _PL=E(_NW),_PM=E(_PJ.c)+ -E(_PL.c),_PN=E(_PJ.b)+ -E(_PL.b),_PO=E(_PJ.a)+ -E(_PL.a),_PP=Math.sqrt(B(_bj(_lR,_PO,_PN,_PM,_PO,_PN,_PM))),_PQ=function(_PR,_PS,_PT){var _PU=E(_P6),_PV=_PU.a,_PW=_PU.b,_PX=_PU.c,_PY=B(_o3(_lR,_PR,_PS,_PT,_PV,_PW,_PX)),_PZ=B(_bj(_lR,_PS*0-0*_PT,_PT*0-0*_PR,_PR*0-0*_PS,_PV,_PW,_PX));return new T6(0,_LZ,_LZ,new T2(0,E(new T3(0,E(_PY.a),E(_PY.b),E(_PY.c))),E(_PZ)),_LQ,_PP,_Lx);};if(!E(_PI.g)){var _Q0=1/_PP,_Q1=B(_PQ(_PO*_Q0,_PN*_Q0,_PM*_Q0));return new T6(0,_Q1.a,_Q1.b,E(_Q1.c),E(_Q1.d),_Q1.e,_Q1.f);}else{var _Q2=1/_PP,_Q3=B(_PQ(-1*_PO*_Q2,-1*_PN*_Q2,-1*_PM*_Q2));return new T6(0,_Q3.a,_Q3.b,E(_Q3.c),E(_Q3.d),_Q3.e,_Q3.f);}});return new T2(1,_PK,new T(function(){return B(_PF(_PH.b));}));}};return B(_PF(_O2));});return new T2(0,new T2(1,_P5,_w),new T(function(){return E(E(_NU).b);}));}}}},_Q4=B(_LY(_LW,_LW,_LX,_LV.c,_LV.d,_));return new F(function(){return _L9(_,_Q4);});}else{return new F(function(){return _L9(_,new T2(0,_w,_LV));});}},_Q5=new T(function(){return eval("__strict(passObject)");}),_Q6=new T(function(){return eval("__strict(refresh)");}),_Q7=function(_Q8,_){var _Q9=__app0(E(_Q6)),_Qa=__app0(E(_D4)),_Qb=E(_Q8),_Qc=_Qb.c,_Qd=_Qb.d,_Qe=E(_Qb.a),_Qf=E(_Qb.b);if(_Qe<=_Qf){if(_Qe>_Qf){return E(_D2);}else{if(0>=_Qc){return new F(function(){return _Df(_Qc,0);});}else{var _Qg=E(_Q5),_Qh=__app2(_Qg,_Qe,B(_CZ(E(_Qd[0]))));if(_Qe!=_Qf){var _Qi=function(_Qj,_){if(_Qe>_Qj){return E(_D2);}else{if(_Qj>_Qf){return E(_D2);}else{var _Qk=_Qj-_Qe|0;if(0>_Qk){return new F(function(){return _Df(_Qc,_Qk);});}else{if(_Qk>=_Qc){return new F(function(){return _Df(_Qc,_Qk);});}else{var _Ql=__app2(_Qg,_Qj,B(_CZ(E(_Qd[_Qk]))));if(_Qj!=_Qf){var _Qm=B(_Qi(_Qj+1|0,_));return new T2(1,_mC,_Qm);}else{return _Dk;}}}}}},_Qn=B(_Qi(_Qe+1|0,_)),_Qo=__app0(E(_D3)),_Qp=B(_LT(_Qb,_));return new T(function(){return E(E(_Qp).b);});}else{var _Qq=__app0(E(_D3)),_Qr=B(_LT(_Qb,_));return new T(function(){return E(E(_Qr).b);});}}}}else{var _Qs=__app0(E(_D3)),_Qt=B(_LT(_Qb,_));return new T(function(){return E(E(_Qt).b);});}},_Qu=function(_Qv,_){while(1){var _Qw=E(_Qv);if(!_Qw._){return _mC;}else{var _Qx=_Qw.b,_Qy=E(_Qw.a);switch(_Qy._){case 0:var _Qz=B(A1(_Qy.a,_));_Qv=B(_n(_Qx,new T2(1,_Qz,_w)));continue;case 1:_Qv=B(_n(_Qx,_Qy.a));continue;default:_Qv=_Qx;continue;}}}},_QA=function(_QB,_QC,_){var _QD=E(_QB);switch(_QD._){case 0:var _QE=B(A1(_QD.a,_));return new F(function(){return _Qu(B(_n(_QC,new T2(1,_QE,_w))),_);});break;case 1:return new F(function(){return _Qu(B(_n(_QC,_QD.a)),_);});break;default:return new F(function(){return _Qu(_QC,_);});}},_QF=new T0(2),_QG=function(_QH){return new T0(2);},_QI=function(_QJ,_QK,_QL){return function(_){var _QM=E(_QJ),_QN=rMV(_QM),_QO=E(_QN);if(!_QO._){var _QP=new T(function(){var _QQ=new T(function(){return B(A1(_QL,_mC));});return B(_n(_QO.b,new T2(1,new T2(0,_QK,function(_QR){return E(_QQ);}),_w)));}),_=wMV(_QM,new T2(0,_QO.a,_QP));return _QF;}else{var _QS=E(_QO.a);if(!_QS._){var _=wMV(_QM,new T2(0,_QK,_w));return new T(function(){return B(A1(_QL,_mC));});}else{var _=wMV(_QM,new T1(1,_QS.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QL,_mC));}),new T2(1,new T(function(){return B(A2(_QS.a,_QK,_QG));}),_w)));}}};},_QT=new T(function(){return E(_sh);}),_QU=new T(function(){return eval("window.requestAnimationFrame");}),_QV=new T1(1,_w),_QW=function(_QX,_QY){return function(_){var _QZ=E(_QX),_R0=rMV(_QZ),_R1=E(_R0);if(!_R1._){var _R2=_R1.a,_R3=E(_R1.b);if(!_R3._){var _=wMV(_QZ,_QV);return new T(function(){return B(A1(_QY,_R2));});}else{var _R4=E(_R3.a),_=wMV(_QZ,new T2(0,_R4.a,_R3.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QY,_R2));}),new T2(1,new T(function(){return B(A1(_R4.b,_QG));}),_w)));}}else{var _R5=new T(function(){var _R6=function(_R7){var _R8=new T(function(){return B(A1(_QY,_R7));});return function(_R9){return E(_R8);};};return B(_n(_R1.a,new T2(1,_R6,_w)));}),_=wMV(_QZ,new T1(1,_R5));return _QF;}};},_Ra=function(_Rb,_Rc){return new T1(0,B(_QW(_Rb,_Rc)));},_Rd=function(_Re,_Rf){var _Rg=new T(function(){return new T1(0,B(_QI(_Re,_mC,_QG)));});return function(_){var _Rh=__createJSFunc(2,function(_Ri,_){var _Rj=B(_QA(_Rg,_w,_));return _QT;}),_Rk=__app1(E(_QU),_Rh);return new T(function(){return B(_Ra(_Re,_Rf));});};},_Rl=new T1(1,_w),_Rm=function(_Rn,_Ro,_){var _Rp=function(_){var _Rq=nMV(_Rn),_Rr=_Rq;return new T(function(){var _Rs=new T(function(){return B(_Rt(_));}),_Ru=function(_){var _Rv=rMV(_Rr),_Rw=B(A2(_Ro,_Rv,_)),_=wMV(_Rr,_Rw),_Rx=function(_){var _Ry=nMV(_Rl);return new T(function(){return new T1(0,B(_Rd(_Ry,function(_Rz){return E(_Rs);})));});};return new T1(0,_Rx);},_RA=new T(function(){return new T1(0,_Ru);}),_Rt=function(_RB){return E(_RA);};return B(_Rt(_));});};return new F(function(){return _QA(new T1(0,_Rp),_w,_);});},_RC=new T(function(){return eval("__strict(setBounds)");}),_RD=function(_){var _RE=__app3(E(_9m),E(_bM),E(_ke),E(_9l)),_RF=__app2(E(_RC),E(_8S),E(_8P));return new F(function(){return _Rm(_CS,_Q7,_);});},_RG=function(_){return new F(function(){return _RD(_);});};
var hasteMain = function() {B(A(_RG, [0]));};window.onload = hasteMain;