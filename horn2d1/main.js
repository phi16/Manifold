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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=new T1(0,10),_hP=new T1(0,7),_hQ=new T2(0,E(_hP),E(_hO)),_hR=new T1(0,9),_hS=new T2(0,E(_hR),E(_hO)),_hT=function(_hU){var _hV=new T(function(){return E(E(_hU).a);}),_hW=new T(function(){return B(_8H(_hV));}),_hX=new T(function(){return B(A2(_eE,_hW,_hS));}),_hY=new T(function(){return B(A2(_eE,_hW,_hQ));}),_hZ=new T(function(){return B(_8J(_hW));}),_i0=new T(function(){return B(A2(_8s,_hZ,_8r));}),_i1=new T(function(){return E(E(_hU).b);}),_i2=function(_i3){var _i4=new T(function(){var _i5=new T(function(){return B(A2(_fR,_hZ,new T(function(){return E(E(_i3).c);})));});return B(A3(_9p,_hZ,_i5,_i0));}),_i6=new T(function(){var _i7=new T(function(){var _i8=new T(function(){var _i9=new T(function(){return B(A3(_8L,_hZ,new T(function(){return E(E(_i3).c);}),_hX));});return B(A3(_9p,_hZ,_i9,_hY));});return B(A2(_bU,_hV,_i8));}),_ia=new T(function(){return B(A2(_fR,_hZ,new T(function(){return E(E(_i3).a);})));});return B(A3(_9p,_hZ,_ia,_i7));});return new F(function(){return A3(_gN,_i1,_i6,_i4);});};return E(_i2);},_ib=function(_ef,_ee){return new T2(0,_ef,_ee);},_ic=function(_id,_ie,_if){var _ig=new T(function(){var _ih=E(_id),_ii=_ih.a,_ij=new T(function(){return B(A1(_ih.b,new T(function(){return B(_8J(B(_8H(E(_ih.c).a))));})));});return B(A3(_8R,_ii,new T(function(){return B(A3(_8T,B(_8F(_ii)),_ib,_if));}),_ij));});return E(B(A1(_ie,_ig)).b);},_ik=function(_il){var _im=new T(function(){return E(E(_il).a);}),_in=new T(function(){return E(E(_il).b);}),_io=new T(function(){var _ip=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_im,_in))));}),new T3(0,_8p,_8u,new T2(0,_im,_in))));}),_iq=new T(function(){var _ir=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_im,_in))));}),new T3(0,_8p,_8u,new T2(0,_im,_in))));});return B(_eb(_ir,new T3(0,_8p,_8u,new T2(0,_im,_in))));});return B(_hT(new T2(0,_iq,_ip)));});return function(_is){return new F(function(){return _ic(new T3(0,_8p,_8u,new T2(0,_im,_in)),_io,_is);});};},_it=new T(function(){return B(_ik(_7V));}),_iu=new T(function(){return B(A1(_it,_E));}),_iv=new T(function(){return E(E(_iu).a);}),_iw=new T(function(){return B(unCStr(",y:"));}),_ix=new T1(0,_iw),_iy=new T(function(){return E(E(_iu).b);}),_iz=new T(function(){return B(unCStr(",z:"));}),_iA=new T1(0,_iz),_iB=new T(function(){return E(E(_iu).c);}),_iC=new T(function(){return B(unCStr("})"));}),_iD=new T1(0,_iC),_iE=new T2(1,_iD,_w),_iF=new T2(1,_iB,_iE),_iG=new T2(1,_iA,_iF),_iH=new T2(1,_iy,_iG),_iI=new T2(1,_ix,_iH),_iJ=new T2(1,_iv,_iI),_iK=new T(function(){return B(unCStr("({x:"));}),_iL=new T1(0,_iK),_iM=new T2(1,_iL,_iJ),_iN=function(_iO){return E(_iO);},_iP=new T(function(){return toJSStr(B(_e(_x,_iN,_iM)));}),_iQ=new T(function(){return B(_hT(_7V));}),_iR=new T(function(){return B(A1(_iQ,_E));}),_iS=new T(function(){return toJSStr(B(_4(_x,_iN,_iR)));}),_iT=function(_iU,_iV,_iW){var _iX=E(_iW);if(!_iX._){return new F(function(){return A1(_iV,_iX.a);});}else{var _iY=new T(function(){return B(_0(_iU));}),_iZ=new T(function(){return B(_2(_iU));}),_j0=function(_j1){var _j2=E(_j1);if(!_j2._){return E(_iZ);}else{return new F(function(){return A2(_iY,new T(function(){return B(_iT(_iU,_iV,_j2.a));}),new T(function(){return B(_j0(_j2.b));}));});}};return new F(function(){return _j0(_iX.a);});}},_j3=new T(function(){return B(unCStr("x"));}),_j4=new T1(0,_j3),_j5=new T(function(){return B(unCStr("y"));}),_j6=new T1(0,_j5),_j7=new T(function(){return B(unCStr("z"));}),_j8=new T1(0,_j7),_j9=new T3(0,E(_j4),E(_j6),E(_j8)),_ja=new T(function(){return B(unCStr(","));}),_jb=new T1(0,_ja),_jc=new T(function(){return B(unCStr("pow("));}),_jd=new T1(0,_jc),_je=new T(function(){return B(unCStr(")"));}),_jf=new T1(0,_je),_jg=new T2(1,_jf,_w),_jh=function(_ji,_jj){return new T1(1,new T2(1,_jd,new T2(1,_ji,new T2(1,_jb,new T2(1,_jj,_jg)))));},_jk=new T(function(){return B(unCStr("acos("));}),_jl=new T1(0,_jk),_jm=function(_jn){return new T1(1,new T2(1,_jl,new T2(1,_jn,_jg)));},_jo=new T(function(){return B(unCStr("acosh("));}),_jp=new T1(0,_jo),_jq=function(_jr){return new T1(1,new T2(1,_jp,new T2(1,_jr,_jg)));},_js=new T(function(){return B(unCStr("asin("));}),_jt=new T1(0,_js),_ju=function(_jv){return new T1(1,new T2(1,_jt,new T2(1,_jv,_jg)));},_jw=new T(function(){return B(unCStr("asinh("));}),_jx=new T1(0,_jw),_jy=function(_jz){return new T1(1,new T2(1,_jx,new T2(1,_jz,_jg)));},_jA=new T(function(){return B(unCStr("atan("));}),_jB=new T1(0,_jA),_jC=function(_jD){return new T1(1,new T2(1,_jB,new T2(1,_jD,_jg)));},_jE=new T(function(){return B(unCStr("atanh("));}),_jF=new T1(0,_jE),_jG=function(_jH){return new T1(1,new T2(1,_jF,new T2(1,_jH,_jg)));},_jI=new T(function(){return B(unCStr("cos("));}),_jJ=new T1(0,_jI),_jK=function(_jL){return new T1(1,new T2(1,_jJ,new T2(1,_jL,_jg)));},_jM=new T(function(){return B(unCStr("cosh("));}),_jN=new T1(0,_jM),_jO=function(_jP){return new T1(1,new T2(1,_jN,new T2(1,_jP,_jg)));},_jQ=new T(function(){return B(unCStr("exp("));}),_jR=new T1(0,_jQ),_jS=function(_jT){return new T1(1,new T2(1,_jR,new T2(1,_jT,_jg)));},_jU=new T(function(){return B(unCStr("log("));}),_jV=new T1(0,_jU),_jW=function(_jX){return new T1(1,new T2(1,_jV,new T2(1,_jX,_jg)));},_jY=new T(function(){return B(unCStr(")/log("));}),_jZ=new T1(0,_jY),_k0=function(_k1,_k2){return new T1(1,new T2(1,_jV,new T2(1,_k2,new T2(1,_jZ,new T2(1,_k1,_jg)))));},_k3=new T(function(){return B(unCStr("pi"));}),_k4=new T1(0,_k3),_k5=new T(function(){return B(unCStr("sin("));}),_k6=new T1(0,_k5),_k7=function(_k8){return new T1(1,new T2(1,_k6,new T2(1,_k8,_jg)));},_k9=new T(function(){return B(unCStr("sinh("));}),_ka=new T1(0,_k9),_kb=function(_kc){return new T1(1,new T2(1,_ka,new T2(1,_kc,_jg)));},_kd=new T(function(){return B(unCStr("sqrt("));}),_ke=new T1(0,_kd),_kf=function(_kg){return new T1(1,new T2(1,_ke,new T2(1,_kg,_jg)));},_kh=new T(function(){return B(unCStr("tan("));}),_ki=new T1(0,_kh),_kj=function(_kk){return new T1(1,new T2(1,_ki,new T2(1,_kk,_jg)));},_kl=new T(function(){return B(unCStr("tanh("));}),_km=new T1(0,_kl),_kn=function(_ko){return new T1(1,new T2(1,_km,new T2(1,_ko,_jg)));},_kp=new T(function(){return B(unCStr("("));}),_kq=new T1(0,_kp),_kr=new T(function(){return B(unCStr(")/("));}),_ks=new T1(0,_kr),_kt=function(_ku,_kv){return new T1(1,new T2(1,_kq,new T2(1,_ku,new T2(1,_ks,new T2(1,_kv,_jg)))));},_kw=function(_kx){return new T1(0,new T(function(){var _ky=E(_kx),_kz=jsShow(B(_6y(_ky.a,_ky.b)));return fromJSStr(_kz);}));},_kA=new T(function(){return B(unCStr("1./("));}),_kB=new T1(0,_kA),_kC=function(_kD){return new T1(1,new T2(1,_kB,new T2(1,_kD,_jg)));},_kE=new T(function(){return B(unCStr(")+("));}),_kF=new T1(0,_kE),_kG=function(_kH,_kI){return new T1(1,new T2(1,_kq,new T2(1,_kH,new T2(1,_kF,new T2(1,_kI,_jg)))));},_kJ=new T(function(){return B(unCStr("-("));}),_kK=new T1(0,_kJ),_kL=function(_kM){return new T1(1,new T2(1,_kK,new T2(1,_kM,_jg)));},_kN=new T(function(){return B(unCStr(")*("));}),_kO=new T1(0,_kN),_kP=function(_kQ,_kR){return new T1(1,new T2(1,_kq,new T2(1,_kQ,new T2(1,_kO,new T2(1,_kR,_jg)))));},_kS=function(_kT,_kU){return new F(function(){return A3(_6X,_kV,_kT,new T(function(){return B(A2(_6Z,_kV,_kU));}));});},_kW=new T(function(){return B(unCStr("abs("));}),_kX=new T1(0,_kW),_kY=function(_kZ){return new T1(1,new T2(1,_kX,new T2(1,_kZ,_jg)));},_l0=new T(function(){return B(unCStr("."));}),_l1=function(_l2){return new T1(0,new T(function(){return B(_n(B(_7i(0,_l2,_w)),_l0));}));},_l3=new T(function(){return B(unCStr("sign("));}),_l4=new T1(0,_l3),_l5=function(_l6){return new T1(1,new T2(1,_l4,new T2(1,_l6,_jg)));},_kV=new T(function(){return {_:0,a:_kG,b:_kS,c:_kP,d:_kL,e:_kY,f:_l5,g:_l1};}),_l7=new T4(0,_kV,_kt,_kC,_kw),_l8={_:0,a:_l7,b:_k4,c:_jS,d:_jW,e:_kf,f:_jh,g:_k0,h:_k7,i:_jK,j:_kj,k:_ju,l:_jm,m:_jC,n:_kb,o:_jO,p:_kn,q:_jy,r:_jq,s:_jG},_l9=new T(function(){return B(unCStr("(/=) is not defined"));}),_la=new T(function(){return B(err(_l9));}),_lb=new T(function(){return B(unCStr("(==) is not defined"));}),_lc=new T(function(){return B(err(_lb));}),_ld=new T2(0,_lc,_la),_le=new T(function(){return B(unCStr("(<) is not defined"));}),_lf=new T(function(){return B(err(_le));}),_lg=new T(function(){return B(unCStr("(<=) is not defined"));}),_lh=new T(function(){return B(err(_lg));}),_li=new T(function(){return B(unCStr("(>) is not defined"));}),_lj=new T(function(){return B(err(_li));}),_lk=new T(function(){return B(unCStr("(>=) is not defined"));}),_ll=new T(function(){return B(err(_lk));}),_lm=new T(function(){return B(unCStr("compare is not defined"));}),_ln=new T(function(){return B(err(_lm));}),_lo=new T(function(){return B(unCStr("max("));}),_lp=new T1(0,_lo),_lq=function(_lr,_ls){return new T1(1,new T2(1,_lp,new T2(1,_lr,new T2(1,_jb,new T2(1,_ls,_jg)))));},_lt=new T(function(){return B(unCStr("min("));}),_lu=new T1(0,_lt),_lv=function(_lw,_lx){return new T1(1,new T2(1,_lu,new T2(1,_lw,new T2(1,_jb,new T2(1,_lx,_jg)))));},_ly={_:0,a:_ld,b:_ln,c:_lf,d:_lh,e:_lj,f:_ll,g:_lq,h:_lv},_lz=new T2(0,_l8,_ly),_lA=new T(function(){return B(_hT(_lz));}),_lB=new T(function(){return B(A1(_lA,_j9));}),_lC=new T(function(){return toJSStr(B(_iT(_x,_iN,_lB)));}),_lD=new T(function(){return eval("__strict(compile)");}),_lE=new T(function(){return toJSStr(E(_j5));}),_lF=function(_lG,_lH,_lI){var _lJ=new T(function(){return B(_0(_lG));}),_lK=new T(function(){return B(_2(_lG));}),_lL=function(_lM){var _lN=E(_lM);if(!_lN._){return E(_lK);}else{return new F(function(){return A2(_lJ,new T(function(){return B(_iT(_lG,_lH,_lN.a));}),new T(function(){return B(_lL(_lN.b));}));});}};return new F(function(){return _lL(_lI);});},_lO=new T(function(){return B(unCStr("vec3("));}),_lP=new T1(0,_lO),_lQ=new T(function(){return B(_7i(0,_8r,_w));}),_lR=new T(function(){return B(_n(_lQ,_l0));}),_lS=new T1(0,_lR),_lT=new T(function(){return B(_7i(0,_8q,_w));}),_lU=new T(function(){return B(_n(_lT,_l0));}),_lV=new T1(0,_lU),_lW=new T2(1,_lV,_w),_lX=new T2(1,_lS,_lW),_lY=function(_lZ,_m0){var _m1=E(_m0);return (_m1._==0)?__Z:new T2(1,_lZ,new T2(1,_m1.a,new T(function(){return B(_lY(_lZ,_m1.b));})));},_m2=new T(function(){return B(_lY(_jb,_lX));}),_m3=new T2(1,_lV,_m2),_m4=new T1(1,_m3),_m5=new T2(1,_m4,_jg),_m6=new T2(1,_lP,_m5),_m7=new T(function(){return toJSStr(B(_lF(_x,_iN,_m6)));}),_m8="enclose",_m9="outline",_ma="polygon",_mb="z",_mc="y",_md="x",_me=0,_mf=function(_mg){var _mh=__new(),_mi=_mh,_mj=function(_mk,_){while(1){var _ml=E(_mk);if(!_ml._){return _me;}else{var _mm=E(_ml.a),_mn=__set(_mi,E(_mm.a),E(_mm.b));_mk=_ml.b;continue;}}},_mo=B(_mj(_mg,_));return E(_mi);},_mp=function(_mq){return new F(function(){return _mf(new T2(1,new T2(0,_md,new T(function(){return E(E(E(E(_mq).d).a).a);})),new T2(1,new T2(0,_mc,new T(function(){return E(E(E(E(_mq).d).a).b);})),new T2(1,new T2(0,_mb,new T(function(){return E(E(E(E(_mq).d).a).c);})),new T2(1,new T2(0,_ma,new T(function(){return E(_mq).h;})),new T2(1,new T2(0,_m9,new T(function(){return E(_mq).i;})),new T2(1,new T2(0,_m8,new T(function(){return E(_mq).j;})),_w)))))));});},_mr=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_ms=new T(function(){return B(err(_mr));}),_mt=new T(function(){return eval("__strict(drawObjects)");}),_mu=new T(function(){return eval("__strict(draw)");}),_mv=function(_mw,_mx){var _my=jsShowI(_mw);return new F(function(){return _n(fromJSStr(_my),_mx);});},_mz=function(_mA,_mB,_mC){if(_mB>=0){return new F(function(){return _mv(_mB,_mC);});}else{if(_mA<=6){return new F(function(){return _mv(_mB,_mC);});}else{return new T2(1,_7g,new T(function(){var _mD=jsShowI(_mB);return B(_n(fromJSStr(_mD),new T2(1,_7f,_mC)));}));}}},_mE=new T(function(){return B(unCStr(")"));}),_mF=function(_mG,_mH){var _mI=new T(function(){var _mJ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mz(0,_mG,_w)),_mE));})));},1);return B(_n(B(_mz(0,_mH,_w)),_mJ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_mI)));});},_mK=new T2(1,_me,_w),_mL=function(_mM){return E(_mM);},_mN=function(_mO){return E(_mO);},_mP=function(_mQ,_mR){return E(_mR);},_mS=function(_mT,_mU){return E(_mT);},_mV=function(_mW){return E(_mW);},_mX=new T2(0,_mV,_mS),_mY=function(_mZ,_n0){return E(_mZ);},_n1=new T5(0,_mX,_mN,_mL,_mP,_mY),_n2=function(_n3){var _n4=E(_n3);return new F(function(){return Math.log(_n4+(_n4+1)*Math.sqrt((_n4-1)/(_n4+1)));});},_n5=function(_n6){var _n7=E(_n6);return new F(function(){return Math.log(_n7+Math.sqrt(1+_n7*_n7));});},_n8=function(_n9){var _na=E(_n9);return 0.5*Math.log((1+_na)/(1-_na));},_nb=function(_nc,_nd){return Math.log(E(_nd))/Math.log(E(_nc));},_ne=3.141592653589793,_nf=function(_ng){var _nh=E(_ng);return new F(function(){return _6y(_nh.a,_nh.b);});},_ni=function(_nj){return 1/E(_nj);},_nk=function(_nl){var _nm=E(_nl),_nn=E(_nm);return (_nn==0)?E(_6x):(_nn<=0)? -_nn:E(_nm);},_no=function(_np){var _nq=E(_np);if(!_nq._){return _nq.a;}else{return new F(function(){return I_toNumber(_nq.a);});}},_nr=function(_ns){return new F(function(){return _no(_ns);});},_nt=1,_nu=-1,_nv=function(_nw){var _nx=E(_nw);return (_nx<=0)?(_nx>=0)?E(_nx):E(_nu):E(_nt);},_ny=function(_nz,_nA){return E(_nz)-E(_nA);},_nB=function(_nC){return  -E(_nC);},_nD=function(_nE,_nF){return E(_nE)+E(_nF);},_nG=function(_nH,_nI){return E(_nH)*E(_nI);},_nJ={_:0,a:_nD,b:_ny,c:_nG,d:_nB,e:_nk,f:_nv,g:_nr},_nK=function(_nL,_nM){return E(_nL)/E(_nM);},_nN=new T4(0,_nJ,_nK,_ni,_nf),_nO=function(_nP){return new F(function(){return Math.acos(E(_nP));});},_nQ=function(_nR){return new F(function(){return Math.asin(E(_nR));});},_nS=function(_nT){return new F(function(){return Math.atan(E(_nT));});},_nU=function(_nV){return new F(function(){return Math.cos(E(_nV));});},_nW=function(_nX){return new F(function(){return cosh(E(_nX));});},_nY=function(_nZ){return new F(function(){return Math.exp(E(_nZ));});},_o0=function(_o1){return new F(function(){return Math.log(E(_o1));});},_o2=function(_o3,_o4){return new F(function(){return Math.pow(E(_o3),E(_o4));});},_o5=function(_o6){return new F(function(){return Math.sin(E(_o6));});},_o7=function(_o8){return new F(function(){return sinh(E(_o8));});},_o9=function(_oa){return new F(function(){return Math.sqrt(E(_oa));});},_ob=function(_oc){return new F(function(){return Math.tan(E(_oc));});},_od=function(_oe){return new F(function(){return tanh(E(_oe));});},_of={_:0,a:_nN,b:_ne,c:_nY,d:_o0,e:_o9,f:_o2,g:_nb,h:_o5,i:_nU,j:_ob,k:_nQ,l:_nO,m:_nS,n:_o7,o:_nW,p:_od,q:_n5,r:_n2,s:_n8},_og="flipped2",_oh="flipped1",_oi="c1y",_oj="c1x",_ok="w2z",_ol="w2y",_om="w2x",_on="w1z",_oo="w1y",_op="w1x",_oq="d2z",_or="d2y",_os="d2x",_ot="d1z",_ou="d1y",_ov="d1x",_ow="c2y",_ox="c2x",_oy=function(_oz,_){var _oA=__get(_oz,E(_op)),_oB=__get(_oz,E(_oo)),_oC=__get(_oz,E(_on)),_oD=__get(_oz,E(_om)),_oE=__get(_oz,E(_ol)),_oF=__get(_oz,E(_ok)),_oG=__get(_oz,E(_oj)),_oH=__get(_oz,E(_oi)),_oI=__get(_oz,E(_ox)),_oJ=__get(_oz,E(_ow)),_oK=__get(_oz,E(_ov)),_oL=__get(_oz,E(_ou)),_oM=__get(_oz,E(_ot)),_oN=__get(_oz,E(_os)),_oO=__get(_oz,E(_or)),_oP=__get(_oz,E(_oq)),_oQ=__get(_oz,E(_oh)),_oR=__get(_oz,E(_og));return {_:0,a:E(new T3(0,E(_oA),E(_oB),E(_oC))),b:E(new T3(0,E(_oD),E(_oE),E(_oF))),c:E(new T2(0,E(_oG),E(_oH))),d:E(new T2(0,E(_oI),E(_oJ))),e:E(new T3(0,E(_oK),E(_oL),E(_oM))),f:E(new T3(0,E(_oN),E(_oO),E(_oP))),g:E(_oQ),h:E(_oR)};},_oS=function(_oT,_){var _oU=E(_oT);if(!_oU._){return _w;}else{var _oV=B(_oy(E(_oU.a),_)),_oW=B(_oS(_oU.b,_));return new T2(1,_oV,_oW);}},_oX=function(_oY){var _oZ=E(_oY);return (E(_oZ.b)-E(_oZ.a)|0)+1|0;},_p0=function(_p1,_p2){var _p3=E(_p1),_p4=E(_p2);return (E(_p3.a)>_p4)?false:_p4<=E(_p3.b);},_p5=function(_p6){return new F(function(){return _mz(0,E(_p6),_w);});},_p7=function(_p8,_p9,_pa){return new F(function(){return _mz(E(_p8),E(_p9),_pa);});},_pb=function(_pc,_pd){return new F(function(){return _mz(0,E(_pc),_pd);});},_pe=function(_pf,_pg){return new F(function(){return _2Q(_pb,_pf,_pg);});},_ph=new T3(0,_p7,_p5,_pe),_pi=0,_pj=function(_pk,_pl,_pm){return new F(function(){return A1(_pk,new T2(1,_2N,new T(function(){return B(A1(_pl,_pm));})));});},_pn=new T(function(){return B(unCStr(": empty list"));}),_po=new T(function(){return B(unCStr("Prelude."));}),_pp=function(_pq){return new F(function(){return err(B(_n(_po,new T(function(){return B(_n(_pq,_pn));},1))));});},_pr=new T(function(){return B(unCStr("foldr1"));}),_ps=new T(function(){return B(_pp(_pr));}),_pt=function(_pu,_pv){var _pw=E(_pv);if(!_pw._){return E(_ps);}else{var _px=_pw.a,_py=E(_pw.b);if(!_py._){return E(_px);}else{return new F(function(){return A2(_pu,_px,new T(function(){return B(_pt(_pu,_py));}));});}}},_pz=new T(function(){return B(unCStr(" out of range "));}),_pA=new T(function(){return B(unCStr("}.index: Index "));}),_pB=new T(function(){return B(unCStr("Ix{"));}),_pC=new T2(1,_7f,_w),_pD=new T2(1,_7f,_pC),_pE=0,_pF=function(_pG){return E(E(_pG).a);},_pH=function(_pI,_pJ,_pK,_pL,_pM){var _pN=new T(function(){var _pO=new T(function(){var _pP=new T(function(){var _pQ=new T(function(){var _pR=new T(function(){return B(A3(_pt,_pj,new T2(1,new T(function(){return B(A3(_pF,_pK,_pE,_pL));}),new T2(1,new T(function(){return B(A3(_pF,_pK,_pE,_pM));}),_w)),_pD));});return B(_n(_pz,new T2(1,_7g,new T2(1,_7g,_pR))));});return B(A(_pF,[_pK,_pi,_pJ,new T2(1,_7f,_pQ)]));});return B(_n(_pA,new T2(1,_7g,_pP)));},1);return B(_n(_pI,_pO));},1);return new F(function(){return err(B(_n(_pB,_pN)));});},_pS=function(_pT,_pU,_pV,_pW,_pX){return new F(function(){return _pH(_pT,_pU,_pX,_pV,_pW);});},_pY=function(_pZ,_q0,_q1,_q2){var _q3=E(_q1);return new F(function(){return _pS(_pZ,_q0,_q3.a,_q3.b,_q2);});},_q4=function(_q5,_q6,_q7,_q8){return new F(function(){return _pY(_q8,_q7,_q6,_q5);});},_q9=new T(function(){return B(unCStr("Int"));}),_qa=function(_qb,_qc){return new F(function(){return _q4(_ph,_qc,_qb,_q9);});},_qd=function(_qe,_qf){var _qg=E(_qe),_qh=E(_qg.a),_qi=E(_qf);if(_qh>_qi){return new F(function(){return _qa(_qi,_qg);});}else{if(_qi>E(_qg.b)){return new F(function(){return _qa(_qi,_qg);});}else{return _qi-_qh|0;}}},_qj=function(_qk,_ql){if(_qk<=_ql){var _qm=function(_qn){return new T2(1,_qn,new T(function(){if(_qn!=_ql){return B(_qm(_qn+1|0));}else{return __Z;}}));};return new F(function(){return _qm(_qk);});}else{return __Z;}},_qo=function(_qp,_qq){return new F(function(){return _qj(E(_qp),E(_qq));});},_qr=function(_qs){var _qt=E(_qs);return new F(function(){return _qo(_qt.a,_qt.b);});},_qu=function(_qv){var _qw=E(_qv),_qx=E(_qw.a),_qy=E(_qw.b);return (_qx>_qy)?E(_pi):(_qy-_qx|0)+1|0;},_qz=function(_qA,_qB){return E(_qA)-E(_qB)|0;},_qC=function(_qD,_qE){return new F(function(){return _qz(_qE,E(_qD).a);});},_qF=function(_qG,_qH){return E(_qG)==E(_qH);},_qI=function(_qJ,_qK){return E(_qJ)!=E(_qK);},_qL=new T2(0,_qF,_qI),_qM=function(_qN,_qO){var _qP=E(_qN),_qQ=E(_qO);return (_qP>_qQ)?E(_qP):E(_qQ);},_qR=function(_qS,_qT){var _qU=E(_qS),_qV=E(_qT);return (_qU>_qV)?E(_qV):E(_qU);},_qW=function(_qX,_qY){return (_qX>=_qY)?(_qX!=_qY)?2:1:0;},_qZ=function(_r0,_r1){return new F(function(){return _qW(E(_r0),E(_r1));});},_r2=function(_r3,_r4){return E(_r3)>=E(_r4);},_r5=function(_r6,_r7){return E(_r6)>E(_r7);},_r8=function(_r9,_ra){return E(_r9)<=E(_ra);},_rb=function(_rc,_rd){return E(_rc)<E(_rd);},_re={_:0,a:_qL,b:_qZ,c:_rb,d:_r8,e:_r5,f:_r2,g:_qM,h:_qR},_rf={_:0,a:_re,b:_qr,c:_qd,d:_qC,e:_p0,f:_qu,g:_oX},_rg=function(_rh,_ri,_){while(1){var _rj=B((function(_rk,_rl,_){var _rm=E(_rk);if(!_rm._){return new T2(0,_me,_rl);}else{var _rn=B(A2(_rm.a,_rl,_));_rh=_rm.b;_ri=new T(function(){return E(E(_rn).b);});return __continue;}})(_rh,_ri,_));if(_rj!=__continue){return _rj;}}},_ro=function(_rp,_rq){return new T2(1,_rp,_rq);},_rr=function(_rs,_rt){var _ru=E(_rt);return new T2(0,_ru.a,_ru.b);},_rv=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_rw=new T(function(){return B(err(_rv));}),_rx=new T(function(){return B(unCStr("Negative range size"));}),_ry=new T(function(){return B(err(_rx));}),_rz=function(_rA){return E(E(_rA).f);},_rB=function(_rC){var _rD=B(A1(_rC,_));return E(_rD);},_rE=function(_rF,_rG,_rH){var _rI=E(_rG),_rJ=_rI.a,_rK=_rI.b,_rL=function(_){var _rM=B(A2(_rz,_rF,_rI));if(_rM>=0){var _rN=newArr(_rM,_rw),_rO=_rN,_rP=E(_rM);if(!_rP){return new T(function(){return new T4(0,E(_rJ),E(_rK),0,_rO);});}else{var _rQ=function(_rR,_rS,_){while(1){var _rT=E(_rR);if(!_rT._){return E(_);}else{var _=_rO[_rS]=_rT.a;if(_rS!=(_rP-1|0)){var _rU=_rS+1|0;_rR=_rT.b;_rS=_rU;continue;}else{return E(_);}}}},_=B(_rQ(_rH,0,_));return new T(function(){return new T4(0,E(_rJ),E(_rK),_rP,_rO);});}}else{return E(_ry);}};return new F(function(){return _rB(_rL);});},_rV=function(_rW,_rX,_rY,_rZ){var _s0=new T(function(){var _s1=E(_rZ),_s2=_s1.c-1|0,_s3=new T(function(){return B(A2(_cF,_rX,_w));});if(0<=_s2){var _s4=new T(function(){return B(_8F(_rX));}),_s5=function(_s6){var _s7=new T(function(){var _s8=new T(function(){return B(A1(_rY,new T(function(){return E(_s1.d[_s6]);})));});return B(A3(_8T,_s4,_ro,_s8));});return new F(function(){return A3(_8R,_rX,_s7,new T(function(){if(_s6!=_s2){return B(_s5(_s6+1|0));}else{return E(_s3);}}));});};return B(_s5(0));}else{return E(_s3);}}),_s9=new T(function(){return B(_rr(_rW,_rZ));});return new F(function(){return A3(_8T,B(_8F(_rX)),function(_sa){return new F(function(){return _rE(_rW,_s9,_sa);});},_s0);});},_sb=function(_sc,_sd,_se,_sf,_sg,_sh,_si,_sj,_sk){var _sl=B(_8L(_sc));return new T2(0,new T3(0,E(B(A1(B(A1(_sl,_sd)),_sh))),E(B(A1(B(A1(_sl,_se)),_si))),E(B(A1(B(A1(_sl,_sf)),_sj)))),B(A1(B(A1(_sl,_sg)),_sk)));},_sm=function(_sn,_so,_sp,_sq,_sr,_ss,_st,_su,_sv){var _sw=B(_6X(_sn));return new T2(0,new T3(0,E(B(A1(B(A1(_sw,_so)),_ss))),E(B(A1(B(A1(_sw,_sp)),_st))),E(B(A1(B(A1(_sw,_sq)),_su)))),B(A1(B(A1(_sw,_sr)),_sv)));},_sx=function(_sy,_sz){return (E(_sy)!=E(_sz))?true:false;},_sA=function(_sB,_sC){return E(_sB)==E(_sC);},_sD=new T2(0,_sA,_sx),_sE=function(_sF,_sG){return E(_sF)<E(_sG);},_sH=function(_sI,_sJ){return E(_sI)<=E(_sJ);},_sK=function(_sL,_sM){return E(_sL)>E(_sM);},_sN=function(_sO,_sP){return E(_sO)>=E(_sP);},_sQ=function(_sR,_sS){var _sT=E(_sR),_sU=E(_sS);return (_sT>=_sU)?(_sT!=_sU)?2:1:0;},_sV=function(_sW,_sX){var _sY=E(_sW),_sZ=E(_sX);return (_sY>_sZ)?E(_sY):E(_sZ);},_t0=function(_t1,_t2){var _t3=E(_t1),_t4=E(_t2);return (_t3>_t4)?E(_t4):E(_t3);},_t5={_:0,a:_sD,b:_sQ,c:_sE,d:_sH,e:_sK,f:_sN,g:_sV,h:_t0},_t6="dz",_t7="wy",_t8="wx",_t9="dy",_ta="dx",_tb="t",_tc="a",_td="r",_te="ly",_tf="lx",_tg="wz",_th=function(_ti,_tj,_tk,_tl,_tm,_tn,_to,_tp,_tq){return new F(function(){return _mf(new T2(1,new T2(0,_t8,_ti),new T2(1,new T2(0,_t7,_tj),new T2(1,new T2(0,_tg,_tk),new T2(1,new T2(0,_tf,_tl*_tm*Math.cos(_tn)),new T2(1,new T2(0,_te,_tl*_tm*Math.sin(_tn)),new T2(1,new T2(0,_td,_tl),new T2(1,new T2(0,_tc,_tm),new T2(1,new T2(0,_tb,_tn),new T2(1,new T2(0,_ta,_to),new T2(1,new T2(0,_t9,_tp),new T2(1,new T2(0,_t6,_tq),_w))))))))))));});},_tr=function(_ts){var _tt=E(_ts),_tu=E(_tt.a),_tv=E(_tt.b),_tw=E(_tt.d);return new F(function(){return _th(_tu.a,_tu.b,_tu.c,E(_tv.a),E(_tv.b),E(_tt.c),_tw.a,_tw.b,_tw.c);});},_tx=function(_ty,_tz){var _tA=E(_tz);return (_tA._==0)?__Z:new T2(1,new T(function(){return B(A1(_ty,_tA.a));}),new T(function(){return B(_tx(_ty,_tA.b));}));},_tB=function(_tC,_tD,_tE){var _tF=__lst2arr(B(_tx(_tr,new T2(1,_tC,new T2(1,_tD,new T2(1,_tE,_w))))));return E(_tF);},_tG=function(_tH){var _tI=E(_tH);return new F(function(){return _tB(_tI.a,_tI.b,_tI.c);});},_tJ=new T2(0,_of,_t5),_tK=function(_tL,_tM,_tN,_tO,_tP,_tQ,_tR){var _tS=B(_8J(B(_8H(_tL)))),_tT=new T(function(){return B(A3(_6X,_tS,new T(function(){return B(A3(_8L,_tS,_tM,_tP));}),new T(function(){return B(A3(_8L,_tS,_tN,_tQ));})));});return new F(function(){return A3(_6X,_tS,_tT,new T(function(){return B(A3(_8L,_tS,_tO,_tR));}));});},_tU=function(_tV,_tW,_tX,_tY){var _tZ=B(_8H(_tV)),_u0=new T(function(){return B(A2(_9t,_tV,new T(function(){return B(_tK(_tV,_tW,_tX,_tY,_tW,_tX,_tY));})));});return new T3(0,B(A3(_8P,_tZ,_tW,_u0)),B(A3(_8P,_tZ,_tX,_u0)),B(A3(_8P,_tZ,_tY,_u0)));},_u1=function(_u2,_u3,_u4,_u5,_u6,_u7,_u8){var _u9=B(_8L(_u2));return new T3(0,B(A1(B(A1(_u9,_u3)),_u6)),B(A1(B(A1(_u9,_u4)),_u7)),B(A1(B(A1(_u9,_u5)),_u8)));},_ua=function(_ub,_uc,_ud,_ue,_uf,_ug,_uh){var _ui=B(_6X(_ub));return new T3(0,B(A1(B(A1(_ui,_uc)),_uf)),B(A1(B(A1(_ui,_ud)),_ug)),B(A1(B(A1(_ui,_ue)),_uh)));},_uj=function(_uk,_ul){var _um=new T(function(){return E(E(_uk).a);}),_un=new T(function(){var _uo=E(_ul),_up=new T(function(){return B(_8J(new T(function(){return B(_8H(_um));})));}),_uq=B(A2(_8s,_up,_8q));return new T3(0,E(_uq),E(B(A2(_8s,_up,_8r))),E(_uq));}),_ur=new T(function(){var _us=E(_un),_ut=B(_tU(_um,_us.a,_us.b,_us.c));return new T3(0,E(_ut.a),E(_ut.b),E(_ut.c));}),_uu=new T(function(){var _uv=E(_ul),_uw=_uv.b,_ux=E(_ur),_uy=B(_8H(_um)),_uz=new T(function(){return B(A2(_9t,_um,new T(function(){var _uA=E(_un),_uB=_uA.a,_uC=_uA.b,_uD=_uA.c;return B(_tK(_um,_uB,_uC,_uD,_uB,_uC,_uD));})));}),_uE=B(A3(_8P,_uy,_uw,_uz)),_uF=B(_8J(_uy)),_uG=B(_u1(_uF,_ux.a,_ux.b,_ux.c,_uE,_uE,_uE)),_uH=B(_6Z(_uF)),_uI=B(_ua(_uF,_uv.a,_uw,_uv.c,B(A1(_uH,_uG.a)),B(A1(_uH,_uG.b)),B(A1(_uH,_uG.c))));return new T3(0,E(_uI.a),E(_uI.b),E(_uI.c));});return new T2(0,_uu,_ur);},_uJ=function(_uK){return E(E(_uK).a);},_uL=function(_uM,_uN,_uO,_uP,_uQ,_uR,_uS){var _uT=B(_tK(_uM,_uQ,_uR,_uS,_uN,_uO,_uP)),_uU=B(_8J(B(_8H(_uM)))),_uV=B(_u1(_uU,_uQ,_uR,_uS,_uT,_uT,_uT)),_uW=B(_6Z(_uU));return new F(function(){return _ua(_uU,_uN,_uO,_uP,B(A1(_uW,_uV.a)),B(A1(_uW,_uV.b)),B(A1(_uW,_uV.c)));});},_uX=function(_uY){return E(E(_uY).a);},_uZ=function(_v0,_v1,_v2,_v3){var _v4=new T(function(){var _v5=E(_v3),_v6=E(_v2),_v7=B(_uL(_v0,_v5.a,_v5.b,_v5.c,_v6.a,_v6.b,_v6.c));return new T3(0,E(_v7.a),E(_v7.b),E(_v7.c));}),_v8=new T(function(){return B(A2(_9t,_v0,new T(function(){var _v9=E(_v4),_va=_v9.a,_vb=_v9.b,_vc=_v9.c;return B(_tK(_v0,_va,_vb,_vc,_va,_vb,_vc));})));});if(!B(A3(_uX,B(_uJ(_v1)),_v8,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_v0)))),_8q));})))){var _vd=E(_v4),_ve=B(_tU(_v0,_vd.a,_vd.b,_vd.c)),_vf=B(A2(_9t,_v0,new T(function(){var _vg=E(_v3),_vh=_vg.a,_vi=_vg.b,_vj=_vg.c;return B(_tK(_v0,_vh,_vi,_vj,_vh,_vi,_vj));}))),_vk=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_v0));})));})));return new T3(0,B(A1(B(A1(_vk,_ve.a)),_vf)),B(A1(B(A1(_vk,_ve.b)),_vf)),B(A1(B(A1(_vk,_ve.c)),_vf)));}else{var _vl=B(A2(_8s,B(_8J(B(_8H(_v0)))),_8q));return new T3(0,_vl,_vl,_vl);}},_vm=0,_vn=new T3(0,E(_vm),E(_vm),E(_vm)),_vo=function(_vp,_vq){while(1){var _vr=E(_vp);if(!_vr._){return E(_vq);}else{var _vs=_vr.b,_vt=E(_vr.a);if(_vq>_vt){_vp=_vs;continue;}else{_vp=_vs;_vq=_vt;continue;}}}},_vu=new T(function(){var _vv=eval("angleCount"),_vw=Number(_vv);return jsTrunc(_vw);}),_vx=new T(function(){return E(_vu);}),_vy=new T(function(){return B(unCStr("head"));}),_vz=new T(function(){return B(_pp(_vy));}),_vA=function(_vB,_vC,_vD){var _vE=E(_vB);if(!_vE._){return __Z;}else{var _vF=E(_vC);if(!_vF._){return __Z;}else{var _vG=_vF.a,_vH=E(_vD);if(!_vH._){return __Z;}else{var _vI=E(_vH.a),_vJ=_vI.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_vE.a),E(_vG),E(_vJ));}),new T2(1,new T(function(){return new T3(0,E(_vG),E(_vJ),E(_vI.b));}),_w)),new T(function(){return B(_vA(_vE.b,_vF.b,_vH.b));},1));});}}}},_vK=new T(function(){return B(unCStr("tail"));}),_vL=new T(function(){return B(_pp(_vK));}),_vM=function(_vN,_vO){var _vP=E(_vN);if(!_vP._){return __Z;}else{var _vQ=E(_vO);return (_vQ._==0)?__Z:new T2(1,new T2(0,_vP.a,_vQ.a),new T(function(){return B(_vM(_vP.b,_vQ.b));}));}},_vR=function(_vS,_vT){var _vU=E(_vS);if(!_vU._){return __Z;}else{var _vV=E(_vT);if(!_vV._){return __Z;}else{var _vW=E(_vU.a),_vX=_vW.b,_vY=E(_vV.a).b,_vZ=new T(function(){var _w0=new T(function(){return B(_vM(_vY,new T(function(){var _w1=E(_vY);if(!_w1._){return E(_vL);}else{return E(_w1.b);}},1)));},1);return B(_vA(_vX,new T(function(){var _w2=E(_vX);if(!_w2._){return E(_vL);}else{return E(_w2.b);}},1),_w0));});return new F(function(){return _n(new T2(1,new T(function(){var _w3=E(_vX);if(!_w3._){return E(_vz);}else{var _w4=E(_vY);if(!_w4._){return E(_vz);}else{return new T3(0,E(_vW.a),E(_w3.a),E(_w4.a));}}}),_vZ),new T(function(){return B(_vR(_vU.b,_vV.b));},1));});}}},_w5=new T(function(){return 6.283185307179586/E(_vx);}),_w6=new T(function(){return E(_vx)-1;}),_w7=new T1(0,1),_w8=function(_w9,_wa){var _wb=E(_wa),_wc=new T(function(){var _wd=B(_8J(_w9)),_we=B(_w8(_w9,B(A3(_6X,_wd,_wb,new T(function(){return B(A2(_8s,_wd,_w7));})))));return new T2(1,_we.a,_we.b);});return new T2(0,_wb,_wc);},_wf=function(_wg){return E(E(_wg).d);},_wh=new T1(0,2),_wi=function(_wj,_wk){var _wl=E(_wk);if(!_wl._){return __Z;}else{var _wm=_wl.a;return (!B(A1(_wj,_wm)))?__Z:new T2(1,_wm,new T(function(){return B(_wi(_wj,_wl.b));}));}},_wn=function(_wo,_wp,_wq,_wr){var _ws=B(_w8(_wp,_wq)),_wt=new T(function(){var _wu=B(_8J(_wp)),_wv=new T(function(){return B(A3(_8P,_wp,new T(function(){return B(A2(_8s,_wu,_w7));}),new T(function(){return B(A2(_8s,_wu,_wh));})));});return B(A3(_6X,_wu,_wr,_wv));});return new F(function(){return _wi(function(_ww){return new F(function(){return A3(_wf,_wo,_ww,_wt);});},new T2(1,_ws.a,_ws.b));});},_wx=new T(function(){return B(_wn(_t5,_nN,_vm,_w6));}),_wy=function(_wz,_wA){while(1){var _wB=E(_wz);if(!_wB._){return E(_wA);}else{_wz=_wB.b;_wA=_wB.a;continue;}}},_wC=new T(function(){return B(unCStr("last"));}),_wD=new T(function(){return B(_pp(_wC));}),_wE=function(_wF){return new F(function(){return _wy(_wF,_wD);});},_wG=function(_wH){return new F(function(){return _wE(E(_wH).b);});},_wI=new T(function(){return B(unCStr("maximum"));}),_wJ=new T(function(){return B(_pp(_wI));}),_wK=new T(function(){var _wL=eval("proceedCount"),_wM=Number(_wL);return jsTrunc(_wM);}),_wN=new T(function(){return E(_wK);}),_wO=1,_wP=new T(function(){return B(_wn(_t5,_nN,_wO,_wN));}),_wQ=function(_wR,_wS,_wT,_wU,_wV,_wW,_wX,_wY,_wZ,_x0,_x1,_x2,_x3,_x4){var _x5=new T(function(){var _x6=new T(function(){var _x7=E(_x0),_x8=E(_x4),_x9=E(_x3),_xa=E(_x1),_xb=E(_x2),_xc=E(_wZ);return new T3(0,_x7*_x8-_x9*_xa,_xa*_xb-_x8*_xc,_xc*_x9-_xb*_x7);}),_xd=function(_xe){var _xf=new T(function(){var _xg=E(_xe)/E(_vx);return (_xg+_xg)*3.141592653589793;}),_xh=new T(function(){return B(A1(_wR,_xf));}),_xi=new T(function(){var _xj=new T(function(){var _xk=E(_xh)/E(_wN);return new T3(0,E(_xk),E(_xk),E(_xk));}),_xl=function(_xm,_xn){var _xo=E(_xm);if(!_xo._){return new T2(0,_w,_xn);}else{var _xp=new T(function(){var _xq=B(_uj(_tJ,new T(function(){var _xr=E(_xn),_xs=E(_xr.a),_xt=E(_xr.b),_xu=E(_xj);return new T3(0,E(_xs.a)+E(_xt.a)*E(_xu.a),E(_xs.b)+E(_xt.b)*E(_xu.b),E(_xs.c)+E(_xt.c)*E(_xu.c));}))),_xv=_xq.a,_xw=new T(function(){var _xx=E(_xq.b),_xy=E(E(_xn).b),_xz=B(_uL(_of,_xy.a,_xy.b,_xy.c,_xx.a,_xx.b,_xx.c)),_xA=B(_tU(_of,_xz.a,_xz.b,_xz.c));return new T3(0,E(_xA.a),E(_xA.b),E(_xA.c));});return new T2(0,new T(function(){var _xB=E(_xh),_xC=E(_xf);return new T4(0,E(_xv),E(new T2(0,E(_xo.a)/E(_wN),E(_xB))),E(_xC),E(_xw));}),new T2(0,_xv,_xw));}),_xD=new T(function(){var _xE=B(_xl(_xo.b,new T(function(){return E(E(_xp).b);})));return new T2(0,_xE.a,_xE.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xp).a);}),new T(function(){return E(E(_xD).a);})),new T(function(){return E(E(_xD).b);}));}},_xF=function(_xG,_xH,_xI,_xJ,_xK){var _xL=E(_xG);if(!_xL._){return new T2(0,_w,new T2(0,new T3(0,E(_xH),E(_xI),E(_xJ)),_xK));}else{var _xM=new T(function(){var _xN=B(_uj(_tJ,new T(function(){var _xO=E(_xK),_xP=E(_xj);return new T3(0,E(_xH)+E(_xO.a)*E(_xP.a),E(_xI)+E(_xO.b)*E(_xP.b),E(_xJ)+E(_xO.c)*E(_xP.c));}))),_xQ=_xN.a,_xR=new T(function(){var _xS=E(_xN.b),_xT=E(_xK),_xU=B(_uL(_of,_xT.a,_xT.b,_xT.c,_xS.a,_xS.b,_xS.c)),_xV=B(_tU(_of,_xU.a,_xU.b,_xU.c));return new T3(0,E(_xV.a),E(_xV.b),E(_xV.c));});return new T2(0,new T(function(){var _xW=E(_xh),_xX=E(_xf);return new T4(0,E(_xQ),E(new T2(0,E(_xL.a)/E(_wN),E(_xW))),E(_xX),E(_xR));}),new T2(0,_xQ,_xR));}),_xY=new T(function(){var _xZ=B(_xl(_xL.b,new T(function(){return E(E(_xM).b);})));return new T2(0,_xZ.a,_xZ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xM).a);}),new T(function(){return E(E(_xY).a);})),new T(function(){return E(E(_xY).b);}));}};return E(B(_xF(_wP,_wU,_wV,_wW,new T(function(){var _y0=E(_x6),_y1=E(_xf)+_wX,_y2=Math.cos(_y1),_y3=Math.sin(_y1);return new T3(0,E(_wZ)*_y2+E(_y0.a)*_y3,E(_x0)*_y2+E(_y0.b)*_y3,E(_x1)*_y2+E(_y0.c)*_y3);}))).a);});return new T2(0,new T(function(){var _y4=E(_xh),_y5=E(_xf);return new T4(0,E(new T3(0,E(_wU),E(_wV),E(_wW))),E(new T2(0,E(_vm),E(_y4))),E(_y5),E(_vn));}),_xi);};return B(_tx(_xd,_wx));}),_y6=new T(function(){var _y7=function(_y8){return new F(function(){return A1(_wR,new T(function(){return B(_nG(_y8,_w5));}));});},_y9=B(_tx(_y7,_wx));if(!_y9._){return E(_wJ);}else{return B(_vo(_y9.b,E(_y9.a)));}}),_ya=new T(function(){var _yb=new T(function(){var _yc=B(_n(_x5,new T2(1,new T(function(){var _yd=E(_x5);if(!_yd._){return E(_vz);}else{return E(_yd.a);}}),_w)));if(!_yc._){return E(_vL);}else{return E(_yc.b);}},1);return B(_vR(_x5,_yb));});return new T3(0,_ya,new T(function(){return B(_tx(_wG,_x5));}),_y6);},_ye=function(_yf,_yg,_yh,_yi,_yj,_yk,_yl,_ym,_yn,_yo,_yp,_yq,_yr,_ys,_yt,_yu,_yv,_yw){var _yx=B(_uj(_tJ,new T3(0,E(_yi),E(_yj),E(_yk)))),_yy=_yx.b,_yz=E(_yx.a),_yA=B(_uZ(_of,_t5,_yy,new T3(0,E(_ym),E(_yn),E(_yo)))),_yB=E(_yy),_yC=_yB.a,_yD=_yB.b,_yE=_yB.c,_yF=B(_uL(_of,_yq,_yr,_ys,_yC,_yD,_yE)),_yG=B(_tU(_of,_yF.a,_yF.b,_yF.c)),_yH=_yG.a,_yI=_yG.b,_yJ=_yG.c,_yK=E(_yl),_yL=new T2(0,E(new T3(0,E(_yA.a),E(_yA.b),E(_yA.c))),E(_yp)),_yM=B(_wQ(_yf,_yg,_yh,_yz.a,_yz.b,_yz.c,_yK,_yL,_yH,_yI,_yJ,_yC,_yD,_yE)),_yN=__lst2arr(B(_tx(_tG,_yM.a))),_yO=__lst2arr(B(_tx(_tr,_yM.b)));return {_:0,a:_yf,b:_yg,c:_yh,d:new T2(0,E(_yz),E(_yK)),e:_yL,f:new T3(0,E(_yH),E(_yI),E(_yJ)),g:_yB,h:_yN,i:_yO,j:E(_yM.c)};},_yP=1.0e-2,_yQ=function(_yR,_yS,_yT,_yU,_yV,_yW,_yX,_yY,_yZ,_z0,_z1,_z2,_z3,_z4,_z5,_z6,_z7,_z8){var _z9=B(_sb(_nJ,_yY,_yZ,_z0,_z1,_yP,_yP,_yP,_yP)),_za=E(_z9.a),_zb=B(_sm(_nJ,_yU,_yV,_yW,_yX,_za.a,_za.b,_za.c,_z9.b)),_zc=E(_zb.a);return new F(function(){return _ye(_yR,_yS,_yT,_zc.a,_zc.b,_zc.c,_zb.b,_yY,_yZ,_z0,_z1,_z2,_z3,_z4,_z5,_z6,_z7,_z8);});},_zd=function(_ze){var _zf=E(_ze),_zg=E(_zf.d),_zh=E(_zg.a),_zi=E(_zf.e),_zj=E(_zi.a),_zk=E(_zf.f),_zl=B(_yQ(_zf.a,_zf.b,_zf.c,_zh.a,_zh.b,_zh.c,_zg.b,_zj.a,_zj.b,_zj.c,_zi.b,_zk.a,_zk.b,_zk.c,_zf.g,_zf.h,_zf.i,_zf.j));return {_:0,a:E(_zl.a),b:E(_zl.b),c:E(_zl.c),d:E(_zl.d),e:E(_zl.e),f:E(_zl.f),g:E(_zl.g),h:_zl.h,i:_zl.i,j:_zl.j};},_zm=function(_zn,_zo,_zp,_zq,_zr,_zs,_zt,_zu,_zv){var _zw=B(_8J(B(_8H(_zn))));return new F(function(){return A3(_6X,_zw,new T(function(){return B(_tK(_zn,_zo,_zp,_zq,_zs,_zt,_zu));}),new T(function(){return B(A3(_8L,_zw,_zr,_zv));}));});},_zx=new T(function(){return B(unCStr("base"));}),_zy=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_zz=new T(function(){return B(unCStr("IOException"));}),_zA=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zx,_zy,_zz),_zB=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zA,_w,_w),_zC=function(_zD){return E(_zB);},_zE=function(_zF){var _zG=E(_zF);return new F(function(){return _2n(B(_2l(_zG.a)),_zC,_zG.b);});},_zH=new T(function(){return B(unCStr(": "));}),_zI=new T(function(){return B(unCStr(")"));}),_zJ=new T(function(){return B(unCStr(" ("));}),_zK=new T(function(){return B(unCStr("interrupted"));}),_zL=new T(function(){return B(unCStr("system error"));}),_zM=new T(function(){return B(unCStr("unsatisified constraints"));}),_zN=new T(function(){return B(unCStr("user error"));}),_zO=new T(function(){return B(unCStr("permission denied"));}),_zP=new T(function(){return B(unCStr("illegal operation"));}),_zQ=new T(function(){return B(unCStr("end of file"));}),_zR=new T(function(){return B(unCStr("resource exhausted"));}),_zS=new T(function(){return B(unCStr("resource busy"));}),_zT=new T(function(){return B(unCStr("does not exist"));}),_zU=new T(function(){return B(unCStr("already exists"));}),_zV=new T(function(){return B(unCStr("resource vanished"));}),_zW=new T(function(){return B(unCStr("timeout"));}),_zX=new T(function(){return B(unCStr("unsupported operation"));}),_zY=new T(function(){return B(unCStr("hardware fault"));}),_zZ=new T(function(){return B(unCStr("inappropriate type"));}),_A0=new T(function(){return B(unCStr("invalid argument"));}),_A1=new T(function(){return B(unCStr("failed"));}),_A2=new T(function(){return B(unCStr("protocol error"));}),_A3=function(_A4,_A5){switch(E(_A4)){case 0:return new F(function(){return _n(_zU,_A5);});break;case 1:return new F(function(){return _n(_zT,_A5);});break;case 2:return new F(function(){return _n(_zS,_A5);});break;case 3:return new F(function(){return _n(_zR,_A5);});break;case 4:return new F(function(){return _n(_zQ,_A5);});break;case 5:return new F(function(){return _n(_zP,_A5);});break;case 6:return new F(function(){return _n(_zO,_A5);});break;case 7:return new F(function(){return _n(_zN,_A5);});break;case 8:return new F(function(){return _n(_zM,_A5);});break;case 9:return new F(function(){return _n(_zL,_A5);});break;case 10:return new F(function(){return _n(_A2,_A5);});break;case 11:return new F(function(){return _n(_A1,_A5);});break;case 12:return new F(function(){return _n(_A0,_A5);});break;case 13:return new F(function(){return _n(_zZ,_A5);});break;case 14:return new F(function(){return _n(_zY,_A5);});break;case 15:return new F(function(){return _n(_zX,_A5);});break;case 16:return new F(function(){return _n(_zW,_A5);});break;case 17:return new F(function(){return _n(_zV,_A5);});break;default:return new F(function(){return _n(_zK,_A5);});}},_A6=new T(function(){return B(unCStr("}"));}),_A7=new T(function(){return B(unCStr("{handle: "));}),_A8=function(_A9,_Aa,_Ab,_Ac,_Ad,_Ae){var _Af=new T(function(){var _Ag=new T(function(){var _Ah=new T(function(){var _Ai=E(_Ac);if(!_Ai._){return E(_Ae);}else{var _Aj=new T(function(){return B(_n(_Ai,new T(function(){return B(_n(_zI,_Ae));},1)));},1);return B(_n(_zJ,_Aj));}},1);return B(_A3(_Aa,_Ah));}),_Ak=E(_Ab);if(!_Ak._){return E(_Ag);}else{return B(_n(_Ak,new T(function(){return B(_n(_zH,_Ag));},1)));}}),_Al=E(_Ad);if(!_Al._){var _Am=E(_A9);if(!_Am._){return E(_Af);}else{var _An=E(_Am.a);if(!_An._){var _Ao=new T(function(){var _Ap=new T(function(){return B(_n(_A6,new T(function(){return B(_n(_zH,_Af));},1)));},1);return B(_n(_An.a,_Ap));},1);return new F(function(){return _n(_A7,_Ao);});}else{var _Aq=new T(function(){var _Ar=new T(function(){return B(_n(_A6,new T(function(){return B(_n(_zH,_Af));},1)));},1);return B(_n(_An.a,_Ar));},1);return new F(function(){return _n(_A7,_Aq);});}}}else{return new F(function(){return _n(_Al.a,new T(function(){return B(_n(_zH,_Af));},1));});}},_As=function(_At){var _Au=E(_At);return new F(function(){return _A8(_Au.a,_Au.b,_Au.c,_Au.d,_Au.f,_w);});},_Av=function(_Aw,_Ax,_Ay){var _Az=E(_Ax);return new F(function(){return _A8(_Az.a,_Az.b,_Az.c,_Az.d,_Az.f,_Ay);});},_AA=function(_AB,_AC){var _AD=E(_AB);return new F(function(){return _A8(_AD.a,_AD.b,_AD.c,_AD.d,_AD.f,_AC);});},_AE=function(_AF,_AG){return new F(function(){return _2Q(_AA,_AF,_AG);});},_AH=new T3(0,_Av,_As,_AE),_AI=new T(function(){return new T5(0,_zC,_AH,_AJ,_zE,_As);}),_AJ=function(_AK){return new T2(0,_AI,_AK);},_AL=__Z,_AM=7,_AN=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_AO=new T6(0,_AL,_AM,_w,_AN,_AL,_AL),_AP=new T(function(){return B(_AJ(_AO));}),_AQ=function(_){return new F(function(){return die(_AP);});},_AR=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_AS=new T6(0,_AL,_AM,_w,_AR,_AL,_AL),_AT=new T(function(){return B(_AJ(_AS));}),_AU=function(_){return new F(function(){return die(_AT);});},_AV=function(_AW,_){return new T2(0,_w,_AW);},_AX=0.6,_AY=1,_AZ=new T(function(){return B(unCStr(")"));}),_B0=function(_B1,_B2){var _B3=new T(function(){var _B4=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mz(0,_B1,_w)),_AZ));})));},1);return B(_n(B(_mz(0,_B2,_w)),_B4));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B3)));});},_B5=function(_B6,_B7){var _B8=new T(function(){var _B9=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mz(0,_B7,_w)),_AZ));})));},1);return B(_n(B(_mz(0,_B6,_w)),_B9));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B8)));});},_Ba=function(_Bb){var _Bc=E(_Bb);if(!_Bc._){return E(_AV);}else{var _Bd=new T(function(){return B(_Ba(_Bc.b));}),_Be=function(_Bf){var _Bg=E(_Bf);if(!_Bg._){return E(_Bd);}else{var _Bh=_Bg.a,_Bi=new T(function(){return B(_Be(_Bg.b));}),_Bj=new T(function(){return 0.1*E(E(_Bh).e)/1.0e-2;}),_Bk=new T(function(){var _Bl=E(_Bh);if(_Bl.a!=_Bl.b){return E(_AY);}else{return E(_AX);}}),_Bm=function(_Bn,_){var _Bo=E(_Bn),_Bp=_Bo.c,_Bq=_Bo.d,_Br=E(_Bo.a),_Bs=E(_Bo.b),_Bt=E(_Bh),_Bu=_Bt.a,_Bv=_Bt.b,_Bw=E(_Bt.c),_Bx=_Bw.b,_By=E(_Bw.a),_Bz=_By.a,_BA=_By.b,_BB=_By.c,_BC=E(_Bt.d),_BD=_BC.b,_BE=E(_BC.a),_BF=_BE.a,_BG=_BE.b,_BH=_BE.c;if(_Br>_Bu){return new F(function(){return _AU(_);});}else{if(_Bu>_Bs){return new F(function(){return _AU(_);});}else{if(_Br>_Bv){return new F(function(){return _AQ(_);});}else{if(_Bv>_Bs){return new F(function(){return _AQ(_);});}else{var _BI=_Bu-_Br|0;if(0>_BI){return new F(function(){return _B0(_Bp,_BI);});}else{if(_BI>=_Bp){return new F(function(){return _B0(_Bp,_BI);});}else{var _BJ=E(_Bq[_BI]),_BK=E(_BJ.c),_BL=_BK.b,_BM=E(_BK.a),_BN=_BM.a,_BO=_BM.b,_BP=_BM.c,_BQ=E(_BJ.e),_BR=E(_BQ.a),_BS=B(_sb(_nJ,_Bz,_BA,_BB,_Bx,_BN,_BO,_BP,_BL)),_BT=E(_BS.a),_BU=B(_sb(_nJ,_BT.a,_BT.b,_BT.c,_BS.b,_Bz,_BA,_BB,_Bx)),_BV=E(_BU.a),_BW=_Bv-_Br|0;if(0>_BW){return new F(function(){return _B5(_BW,_Bp);});}else{if(_BW>=_Bp){return new F(function(){return _B5(_BW,_Bp);});}else{var _BX=E(_Bq[_BW]),_BY=E(_BX.c),_BZ=_BY.b,_C0=E(_BY.a),_C1=_C0.a,_C2=_C0.b,_C3=_C0.c,_C4=E(_BX.e),_C5=E(_C4.a),_C6=B(_sb(_nJ,_BF,_BG,_BH,_BD,_C1,_C2,_C3,_BZ)),_C7=E(_C6.a),_C8=B(_sb(_nJ,_C7.a,_C7.b,_C7.c,_C6.b,_BF,_BG,_BH,_BD)),_C9=E(_C8.a),_Ca=E(_BV.a)+E(_BV.b)+E(_BV.c)+E(_BU.b)+E(_C9.a)+E(_C9.b)+E(_C9.c)+E(_C8.b);if(!_Ca){var _Cb=B(A2(_Bi,_Bo,_));return new T2(0,new T2(1,_me,new T(function(){return E(E(_Cb).a);})),new T(function(){return E(E(_Cb).b);}));}else{var _Cc=new T(function(){return  -((B(_zm(_of,_BR.a,_BR.b,_BR.c,_BQ.b,_Bz,_BA,_BB,_Bx))-B(_zm(_of,_C5.a,_C5.b,_C5.c,_C4.b,_BF,_BG,_BH,_BD))-E(_Bj))/_Ca);}),_Cd=function(_Ce,_Cf,_Cg,_Ch,_){var _Ci=new T(function(){var _Cj=function(_Ck,_Cl,_Cm,_Cn,_Co){if(_Ck>_Bv){return E(_Co);}else{if(_Bv>_Cl){return E(_Co);}else{var _Cp=function(_){var _Cq=newArr(_Cm,_rw),_Cr=_Cq,_Cs=function(_Ct,_){while(1){if(_Ct!=_Cm){var _=_Cr[_Ct]=_Cn[_Ct],_Cu=_Ct+1|0;_Ct=_Cu;continue;}else{return E(_);}}},_=B(_Cs(0,_)),_Cv=_Bv-_Ck|0;if(0>_Cv){return new F(function(){return _B5(_Cv,_Cm);});}else{if(_Cv>=_Cm){return new F(function(){return _B5(_Cv,_Cm);});}else{var _=_Cr[_Cv]=new T(function(){var _Cw=E(_Cn[_Cv]),_Cx=E(_Cw.e),_Cy=E(_Cx.a),_Cz=B(_sb(_nJ,_C1,_C2,_C3,_BZ,_BF,_BG,_BH,_BD)),_CA=E(_Cz.a),_CB=E(_Cc)*E(_Bk),_CC=B(_sb(_nJ,_CA.a,_CA.b,_CA.c,_Cz.b,_CB,_CB,_CB,_CB)),_CD=E(_CC.a),_CE=B(_sm(_nJ,_Cy.a,_Cy.b,_Cy.c,_Cx.b, -E(_CD.a), -E(_CD.b), -E(_CD.c), -E(_CC.b)));return {_:0,a:E(_Cw.a),b:E(_Cw.b),c:E(_Cw.c),d:E(_Cw.d),e:E(new T2(0,E(_CE.a),E(_CE.b))),f:E(_Cw.f),g:E(_Cw.g),h:_Cw.h,i:_Cw.i,j:_Cw.j};});return new T4(0,E(_Ck),E(_Cl),_Cm,_Cr);}}};return new F(function(){return _rB(_Cp);});}}};if(_Ce>_Bu){return B(_Cj(_Ce,_Cf,_Cg,_Ch,new T4(0,E(_Ce),E(_Cf),_Cg,_Ch)));}else{if(_Bu>_Cf){return B(_Cj(_Ce,_Cf,_Cg,_Ch,new T4(0,E(_Ce),E(_Cf),_Cg,_Ch)));}else{var _CF=function(_){var _CG=newArr(_Cg,_rw),_CH=_CG,_CI=function(_CJ,_){while(1){if(_CJ!=_Cg){var _=_CH[_CJ]=_Ch[_CJ],_CK=_CJ+1|0;_CJ=_CK;continue;}else{return E(_);}}},_=B(_CI(0,_)),_CL=_Bu-_Ce|0;if(0>_CL){return new F(function(){return _B0(_Cg,_CL);});}else{if(_CL>=_Cg){return new F(function(){return _B0(_Cg,_CL);});}else{var _=_CH[_CL]=new T(function(){var _CM=E(_Ch[_CL]),_CN=E(_CM.e),_CO=E(_CN.a),_CP=B(_sb(_nJ,_BN,_BO,_BP,_BL,_Bz,_BA,_BB,_Bx)),_CQ=E(_CP.a),_CR=E(_Cc)*E(_Bk),_CS=B(_sb(_nJ,_CQ.a,_CQ.b,_CQ.c,_CP.b,_CR,_CR,_CR,_CR)),_CT=E(_CS.a),_CU=B(_sm(_nJ,_CO.a,_CO.b,_CO.c,_CN.b,_CT.a,_CT.b,_CT.c,_CS.b));return {_:0,a:E(_CM.a),b:E(_CM.b),c:E(_CM.c),d:E(_CM.d),e:E(new T2(0,E(_CU.a),E(_CU.b))),f:E(_CM.f),g:E(_CM.g),h:_CM.h,i:_CM.i,j:_CM.j};});return new T4(0,E(_Ce),E(_Cf),_Cg,_CH);}}},_CV=B(_rB(_CF));return B(_Cj(E(_CV.a),E(_CV.b),_CV.c,_CV.d,_CV));}}});return new T2(0,_me,_Ci);};if(!E(_Bt.f)){var _CW=B(_Cd(_Br,_Bs,_Bp,_Bq,_)),_CX=B(A2(_Bi,new T(function(){return E(E(_CW).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CW).a);}),new T(function(){return E(E(_CX).a);})),new T(function(){return E(E(_CX).b);}));}else{if(E(_Cc)<0){var _CY=B(A2(_Bi,_Bo,_));return new T2(0,new T2(1,_me,new T(function(){return E(E(_CY).a);})),new T(function(){return E(E(_CY).b);}));}else{var _CZ=B(_Cd(_Br,_Bs,_Bp,_Bq,_)),_D0=B(A2(_Bi,new T(function(){return E(E(_CZ).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CZ).a);}),new T(function(){return E(E(_D0).a);})),new T(function(){return E(E(_D0).b);}));}}}}}}}}}}}};return E(_Bm);}};return new F(function(){return _Be(_Bc.a);});}},_D1=function(_,_D2){var _D3=new T(function(){return B(_Ba(E(_D2).a));}),_D4=function(_D5){var _D6=E(_D5);return (_D6==1)?E(new T2(1,_D3,_w)):new T2(1,_D3,new T(function(){return B(_D4(_D6-1|0));}));},_D7=B(_rg(B(_D4(5)),new T(function(){return E(E(_D2).b);}),_)),_D8=new T(function(){return B(_rV(_rf,_n1,_zd,new T(function(){return E(E(_D7).b);})));});return new T2(0,_me,_D8);},_D9=function(_Da,_Db,_Dc,_Dd,_De){var _Df=B(_8J(B(_8H(_Da))));return new F(function(){return A3(_6X,_Df,new T(function(){return B(A3(_8L,_Df,_Db,_Dd));}),new T(function(){return B(A3(_8L,_Df,_Dc,_De));}));});},_Dg=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Dh=new T6(0,_AL,_AM,_w,_Dg,_AL,_AL),_Di=new T(function(){return B(_AJ(_Dh));}),_Dj=function(_){return new F(function(){return die(_Di);});},_Dk=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Dl=new T6(0,_AL,_AM,_w,_Dk,_AL,_AL),_Dm=new T(function(){return B(_AJ(_Dl));}),_Dn=function(_){return new F(function(){return die(_Dm);});},_Do=function(_Dp,_Dq,_Dr,_Ds){var _Dt=new T(function(){return B(_8J(new T(function(){return B(_8H(_Dp));})));}),_Du=B(A2(_8s,_Dt,_8q));return new F(function(){return _tU(_Dp,_Du,B(A2(_8s,_Dt,_8r)),_Du);});},_Dv=false,_Dw=true,_Dx=function(_Dy){var _Dz=E(_Dy),_DA=_Dz.b,_DB=E(_Dz.d),_DC=E(_Dz.e),_DD=E(_DC.a),_DE=E(_Dz.g),_DF=B(A1(_DA,_DB.a)),_DG=B(_uL(_of,_DF.a,_DF.b,_DF.c,_DE.a,_DE.b,_DE.c));return {_:0,a:E(_Dz.a),b:E(_DA),c:E(_Dz.c),d:E(_DB),e:E(new T2(0,E(new T3(0,E(_DD.a)+E(_DG.a)*1.0e-2,E(_DD.b)+E(_DG.b)*1.0e-2,E(_DD.c)+E(_DG.c)*1.0e-2)),E(_DC.b))),f:E(_Dz.f),g:E(_DE),h:_Dz.h,i:_Dz.i,j:_Dz.j};},_DH=new T(function(){return eval("__strict(collideBound)");}),_DI=new T(function(){return eval("__strict(mouseContact)");}),_DJ=new T(function(){return eval("__strict(collide)");}),_DK=function(_DL){var _DM=E(_DL);if(!_DM._){return __Z;}else{return new F(function(){return _n(_DM.a,new T(function(){return B(_DK(_DM.b));},1));});}},_DN=0,_DO=new T3(0,E(_DN),E(_DN),E(_DN)),_DP=new T2(0,E(_DO),E(_DN)),_DQ=function(_DR,_){var _DS=B(_rV(_rf,_n1,_Dx,_DR)),_DT=E(_DS.a),_DU=E(_DS.b);if(_DT<=_DU){var _DV=function(_DW,_DX,_DY,_DZ,_E0,_){if(_DX>_DW){return new F(function(){return _Dn(_);});}else{if(_DW>_DY){return new F(function(){return _Dn(_);});}else{var _E1=new T(function(){var _E2=_DW-_DX|0;if(0>_E2){return B(_B5(_E2,_DZ));}else{if(_E2>=_DZ){return B(_B5(_E2,_DZ));}else{return E(_E0[_E2]);}}}),_E3=function(_E4,_E5,_E6,_E7,_E8,_){var _E9=E(_E4);if(!_E9._){return new T2(0,_w,new T4(0,E(_E5),E(_E6),_E7,_E8));}else{var _Ea=E(_E9.a);if(_E5>_Ea){return new F(function(){return _Dj(_);});}else{if(_Ea>_E6){return new F(function(){return _Dj(_);});}else{var _Eb=_Ea-_E5|0;if(0>_Eb){return new F(function(){return _B0(_E7,_Eb);});}else{if(_Eb>=_E7){return new F(function(){return _B0(_E7,_Eb);});}else{var _Ec=__app2(E(_DJ),B(_mp(E(_E1))),B(_mp(E(_E8[_Eb])))),_Ed=__arr2lst(0,_Ec),_Ee=B(_oS(_Ed,_)),_Ef=B(_E3(_E9.b,_E5,_E6,_E7,_E8,_)),_Eg=new T(function(){var _Eh=new T(function(){return _DW!=_Ea;}),_Ei=function(_Ej){var _Ek=E(_Ej);if(!_Ek._){return __Z;}else{var _El=_Ek.b,_Em=E(_Ek.a),_En=E(_Em.b),_Eo=E(_Em.a),_Ep=E(_Eo.a),_Eq=E(_Eo.b),_Er=E(_Eo.c),_Es=E(_En.a),_Et=E(_En.b),_Eu=E(_En.c),_Ev=E(_Em.c),_Ew=_Ev.a,_Ex=_Ev.b,_Ey=E(_Em.e),_Ez=E(_Em.d),_EA=_Ez.a,_EB=_Ez.b,_EC=E(_Em.f),_ED=new T(function(){var _EE=B(_tU(_of,_EC.a,_EC.b,_EC.c)),_EF=Math.sqrt(B(_D9(_of,_EA,_EB,_EA,_EB)));return new T3(0,_EF*E(_EE.a),_EF*E(_EE.b),_EF*E(_EE.c));}),_EG=new T(function(){var _EH=B(_tU(_of,_Ey.a,_Ey.b,_Ey.c)),_EI=Math.sqrt(B(_D9(_of,_Ew,_Ex,_Ew,_Ex)));return new T3(0,_EI*E(_EH.a),_EI*E(_EH.b),_EI*E(_EH.c));}),_EJ=new T(function(){var _EK=B(_Do(_of,_Es,_Et,_Eu));return new T3(0,E(_EK.a),E(_EK.b),E(_EK.c));}),_EL=new T(function(){var _EM=B(_Do(_of,_Ep,_Eq,_Er));return new T3(0,E(_EM.a),E(_EM.b),E(_EM.c));}),_EN=_Es+ -_Ep,_EO=_Et+ -_Eq,_EP=_Eu+ -_Er,_EQ=new T(function(){return Math.sqrt(B(_tK(_of,_EN,_EO,_EP,_EN,_EO,_EP)));}),_ER=new T(function(){var _ES=1/E(_EQ);return new T3(0,_EN*_ES,_EO*_ES,_EP*_ES);}),_ET=new T(function(){if(!E(_Em.g)){return E(_ER);}else{var _EU=E(_ER);return new T3(0,-1*E(_EU.a),-1*E(_EU.b),-1*E(_EU.c));}}),_EV=new T(function(){if(!E(_Em.h)){return E(_ER);}else{var _EW=E(_ER);return new T3(0,-1*E(_EW.a),-1*E(_EW.b),-1*E(_EW.c));}});return (!E(_Eh))?new T2(1,new T(function(){var _EX=E(_ET),_EY=E(_EX.b),_EZ=E(_EX.c),_F0=E(_EX.a),_F1=E(_EL),_F2=E(_F1.c),_F3=E(_F1.b),_F4=E(_F1.a),_F5=E(_EG),_F6=E(_F5.c),_F7=E(_F5.b),_F8=E(_F5.a),_F9=_EY*_F2-_F3*_EZ,_Fa=_EZ*_F4-_F2*_F0,_Fb=_F0*_F3-_F4*_EY,_Fc=B(_tK(_of,_Fa*_F6-_F7*_Fb,_Fb*_F8-_F6*_F9,_F9*_F7-_F8*_Fa,_F4,_F3,_F2));return new T6(0,_DW,_Ea,E(new T2(0,E(new T3(0,E(_F9),E(_Fa),E(_Fb))),E(_Fc))),E(_DP),_EQ,_Dv);}),new T2(1,new T(function(){var _Fd=E(_EV),_Fe=E(_Fd.b),_Ff=E(_Fd.c),_Fg=E(_Fd.a),_Fh=E(_EJ),_Fi=E(_Fh.c),_Fj=E(_Fh.b),_Fk=E(_Fh.a),_Fl=E(_ED),_Fm=E(_Fl.c),_Fn=E(_Fl.b),_Fo=E(_Fl.a),_Fp=_Fe*_Fi-_Fj*_Ff,_Fq=_Ff*_Fk-_Fi*_Fg,_Fr=_Fg*_Fj-_Fk*_Fe,_Fs=B(_tK(_of,_Fq*_Fm-_Fn*_Fr,_Fr*_Fo-_Fm*_Fp,_Fp*_Fn-_Fo*_Fq,_Fk,_Fj,_Fi));return new T6(0,_DW,_Ea,E(_DP),E(new T2(0,E(new T3(0,E(_Fp),E(_Fq),E(_Fr))),E(_Fs))),_EQ,_Dv);}),new T(function(){return B(_Ei(_El));}))):new T2(1,new T(function(){var _Ft=E(_ET),_Fu=E(_Ft.b),_Fv=E(_Ft.c),_Fw=E(_Ft.a),_Fx=E(_EL),_Fy=_Fx.a,_Fz=_Fx.b,_FA=_Fx.c,_FB=B(_uL(_of,_Fw,_Fu,_Fv,_Fy,_Fz,_FA)),_FC=E(_EG),_FD=E(_FC.c),_FE=E(_FC.b),_FF=E(_FC.a),_FG=B(_tK(_of,_Fu*_FD-_FE*_Fv,_Fv*_FF-_FD*_Fw,_Fw*_FE-_FF*_Fu,_Fy,_Fz,_FA)),_FH=E(_EV),_FI=E(_FH.b),_FJ=E(_FH.c),_FK=E(_FH.a),_FL=E(_EJ),_FM=_FL.a,_FN=_FL.b,_FO=_FL.c,_FP=B(_uL(_of,_FK,_FI,_FJ,_FM,_FN,_FO)),_FQ=E(_ED),_FR=E(_FQ.c),_FS=E(_FQ.b),_FT=E(_FQ.a),_FU=B(_tK(_of,_FI*_FR-_FS*_FJ,_FJ*_FT-_FR*_FK,_FK*_FS-_FT*_FI,_FM,_FN,_FO));return new T6(0,_DW,_Ea,E(new T2(0,E(new T3(0,E(_FB.a),E(_FB.b),E(_FB.c))),E(_FG))),E(new T2(0,E(new T3(0,E(_FP.a),E(_FP.b),E(_FP.c))),E(_FU))),_EQ,_Dw);}),new T(function(){return B(_Ei(_El));}));}};return B(_Ei(_Ee));});return new T2(0,new T2(1,_Eg,new T(function(){return E(E(_Ef).a);})),new T(function(){return E(E(_Ef).b);}));}}}}}},_FV=B(_E3(B(_qj(_DW,_DU)),_DX,_DY,_DZ,_E0,_)),_FW=E(_E1),_FX=E(_FW.d).a,_FY=__app1(E(_DH),B(_mp(_FW))),_FZ=__arr2lst(0,_FY),_G0=B(_oS(_FZ,_)),_G1=__app1(E(_DI),_DW),_G2=__arr2lst(0,_G1),_G3=B(_oS(_G2,_));if(_DW!=_DU){var _G4=E(_FV),_G5=E(_G4.b),_G6=B(_DV(_DW+1|0,E(_G5.a),E(_G5.b),_G5.c,_G5.d,_)),_G7=new T(function(){var _G8=new T(function(){var _G9=E(_FX),_Ga=B(_Do(_of,_G9.a,_G9.b,_G9.c));return new T3(0,E(_Ga.a),E(_Ga.b),E(_Ga.c));}),_Gb=new T(function(){var _Gc=new T(function(){return B(_DK(_G4.a));}),_Gd=function(_Ge){var _Gf=E(_Ge);if(!_Gf._){return E(_Gc);}else{var _Gg=E(_Gf.a),_Gh=E(_Gg.b),_Gi=E(_Gg.a),_Gj=E(_Gi.a),_Gk=E(_Gi.b),_Gl=E(_Gi.c),_Gm=E(_Gg.c),_Gn=_Gm.a,_Go=_Gm.b,_Gp=E(_Gg.e);return new T2(1,new T(function(){var _Gq=E(_Gh.a)+ -_Gj,_Gr=E(_Gh.b)+ -_Gk,_Gs=E(_Gh.c)+ -_Gl,_Gt=B(_Do(_of,_Gj,_Gk,_Gl)),_Gu=_Gt.a,_Gv=_Gt.b,_Gw=_Gt.c,_Gx=Math.sqrt(B(_tK(_of,_Gq,_Gr,_Gs,_Gq,_Gr,_Gs))),_Gy=1/_Gx,_Gz=_Gq*_Gy,_GA=_Gr*_Gy,_GB=_Gs*_Gy,_GC=B(_uL(_of,_Gz,_GA,_GB,_Gu,_Gv,_Gw)),_GD=B(_tU(_of,_Gp.a,_Gp.b,_Gp.c)),_GE=Math.sqrt(B(_D9(_of,_Gn,_Go,_Gn,_Go))),_GF=_GE*E(_GD.a),_GG=_GE*E(_GD.b),_GH=_GE*E(_GD.c),_GI=B(_tK(_of,_GA*_GH-_GG*_GB,_GB*_GF-_GH*_Gz,_Gz*_GG-_GF*_GA,_Gu,_Gv,_Gw));return new T6(0,_DW,_DW,E(new T2(0,E(new T3(0,E(_GC.a),E(_GC.b),E(_GC.c))),E(_GI))),E(_DP),_Gx,_Dw);}),new T(function(){return B(_Gd(_Gf.b));}));}};return B(_Gd(_G0));}),_GJ=function(_GK){var _GL=E(_GK);if(!_GL._){return E(_Gb);}else{var _GM=E(_GL.a),_GN=E(_GM.b),_GO=new T(function(){var _GP=E(_FX),_GQ=E(_GN.c)+ -E(_GP.c),_GR=E(_GN.b)+ -E(_GP.b),_GS=E(_GN.a)+ -E(_GP.a),_GT=Math.sqrt(B(_tK(_of,_GS,_GR,_GQ,_GS,_GR,_GQ))),_GU=function(_GV,_GW,_GX){var _GY=E(_G8),_GZ=_GY.a,_H0=_GY.b,_H1=_GY.c,_H2=B(_uL(_of,_GV,_GW,_GX,_GZ,_H0,_H1)),_H3=B(_tK(_of,_GW*0-0*_GX,_GX*0-0*_GV,_GV*0-0*_GW,_GZ,_H0,_H1));return new T6(0,_DW,_DW,new T2(0,E(new T3(0,E(_H2.a),E(_H2.b),E(_H2.c))),E(_H3)),_DP,_GT,_Dw);};if(!E(_GM.g)){var _H4=1/_GT,_H5=B(_GU(_GS*_H4,_GR*_H4,_GQ*_H4));return new T6(0,_H5.a,_H5.b,E(_H5.c),E(_H5.d),_H5.e,_H5.f);}else{var _H6=1/_GT,_H7=B(_GU(-1*_GS*_H6,-1*_GR*_H6,-1*_GQ*_H6));return new T6(0,_H7.a,_H7.b,E(_H7.c),E(_H7.d),_H7.e,_H7.f);}});return new T2(1,_GO,new T(function(){return B(_GJ(_GL.b));}));}};return B(_GJ(_G3));});return new T2(0,new T2(1,_G7,new T(function(){return E(E(_G6).a);})),new T(function(){return E(E(_G6).b);}));}else{var _H8=new T(function(){var _H9=new T(function(){var _Ha=E(_FX),_Hb=B(_Do(_of,_Ha.a,_Ha.b,_Ha.c));return new T3(0,E(_Hb.a),E(_Hb.b),E(_Hb.c));}),_Hc=new T(function(){var _Hd=new T(function(){return B(_DK(E(_FV).a));}),_He=function(_Hf){var _Hg=E(_Hf);if(!_Hg._){return E(_Hd);}else{var _Hh=E(_Hg.a),_Hi=E(_Hh.b),_Hj=E(_Hh.a),_Hk=E(_Hj.a),_Hl=E(_Hj.b),_Hm=E(_Hj.c),_Hn=E(_Hh.c),_Ho=_Hn.a,_Hp=_Hn.b,_Hq=E(_Hh.e);return new T2(1,new T(function(){var _Hr=E(_Hi.a)+ -_Hk,_Hs=E(_Hi.b)+ -_Hl,_Ht=E(_Hi.c)+ -_Hm,_Hu=B(_Do(_of,_Hk,_Hl,_Hm)),_Hv=_Hu.a,_Hw=_Hu.b,_Hx=_Hu.c,_Hy=Math.sqrt(B(_tK(_of,_Hr,_Hs,_Ht,_Hr,_Hs,_Ht))),_Hz=1/_Hy,_HA=_Hr*_Hz,_HB=_Hs*_Hz,_HC=_Ht*_Hz,_HD=B(_uL(_of,_HA,_HB,_HC,_Hv,_Hw,_Hx)),_HE=B(_tU(_of,_Hq.a,_Hq.b,_Hq.c)),_HF=Math.sqrt(B(_D9(_of,_Ho,_Hp,_Ho,_Hp))),_HG=_HF*E(_HE.a),_HH=_HF*E(_HE.b),_HI=_HF*E(_HE.c),_HJ=B(_tK(_of,_HB*_HI-_HH*_HC,_HC*_HG-_HI*_HA,_HA*_HH-_HG*_HB,_Hv,_Hw,_Hx));return new T6(0,_DW,_DW,E(new T2(0,E(new T3(0,E(_HD.a),E(_HD.b),E(_HD.c))),E(_HJ))),E(_DP),_Hy,_Dw);}),new T(function(){return B(_He(_Hg.b));}));}};return B(_He(_G0));}),_HK=function(_HL){var _HM=E(_HL);if(!_HM._){return E(_Hc);}else{var _HN=E(_HM.a),_HO=E(_HN.b),_HP=new T(function(){var _HQ=E(_FX),_HR=E(_HO.c)+ -E(_HQ.c),_HS=E(_HO.b)+ -E(_HQ.b),_HT=E(_HO.a)+ -E(_HQ.a),_HU=Math.sqrt(B(_tK(_of,_HT,_HS,_HR,_HT,_HS,_HR))),_HV=function(_HW,_HX,_HY){var _HZ=E(_H9),_I0=_HZ.a,_I1=_HZ.b,_I2=_HZ.c,_I3=B(_uL(_of,_HW,_HX,_HY,_I0,_I1,_I2)),_I4=B(_tK(_of,_HX*0-0*_HY,_HY*0-0*_HW,_HW*0-0*_HX,_I0,_I1,_I2));return new T6(0,_DW,_DW,new T2(0,E(new T3(0,E(_I3.a),E(_I3.b),E(_I3.c))),E(_I4)),_DP,_HU,_Dw);};if(!E(_HN.g)){var _I5=1/_HU,_I6=B(_HV(_HT*_I5,_HS*_I5,_HR*_I5));return new T6(0,_I6.a,_I6.b,E(_I6.c),E(_I6.d),_I6.e,_I6.f);}else{var _I7=1/_HU,_I8=B(_HV(-1*_HT*_I7,-1*_HS*_I7,-1*_HR*_I7));return new T6(0,_I8.a,_I8.b,E(_I8.c),E(_I8.d),_I8.e,_I8.f);}});return new T2(1,_HP,new T(function(){return B(_HK(_HM.b));}));}};return B(_HK(_G3));});return new T2(0,new T2(1,_H8,_w),new T(function(){return E(E(_FV).b);}));}}}},_I9=B(_DV(_DT,_DT,_DU,_DS.c,_DS.d,_));return new F(function(){return _D1(_,_I9);});}else{return new F(function(){return _D1(_,new T2(0,_w,_DS));});}},_Ia=new T(function(){return eval("__strict(passObject)");}),_Ib=new T(function(){return eval("__strict(refresh)");}),_Ic=function(_Id,_){var _Ie=__app0(E(_Ib)),_If=__app0(E(_mu)),_Ig=E(_Id),_Ih=_Ig.c,_Ii=_Ig.d,_Ij=E(_Ig.a),_Ik=E(_Ig.b);if(_Ij<=_Ik){if(_Ij>_Ik){return E(_ms);}else{if(0>=_Ih){return new F(function(){return _mF(_Ih,0);});}else{var _Il=E(_Ia),_Im=__app2(_Il,_Ij,B(_mp(E(_Ii[0]))));if(_Ij!=_Ik){var _In=function(_Io,_){if(_Ij>_Io){return E(_ms);}else{if(_Io>_Ik){return E(_ms);}else{var _Ip=_Io-_Ij|0;if(0>_Ip){return new F(function(){return _mF(_Ih,_Ip);});}else{if(_Ip>=_Ih){return new F(function(){return _mF(_Ih,_Ip);});}else{var _Iq=__app2(_Il,_Io,B(_mp(E(_Ii[_Ip]))));if(_Io!=_Ik){var _Ir=B(_In(_Io+1|0,_));return new T2(1,_me,_Ir);}else{return _mK;}}}}}},_Is=B(_In(_Ij+1|0,_)),_It=__app0(E(_mt)),_Iu=B(_DQ(_Ig,_));return new T(function(){return E(E(_Iu).b);});}else{var _Iv=__app0(E(_mt)),_Iw=B(_DQ(_Ig,_));return new T(function(){return E(E(_Iw).b);});}}}}else{var _Ix=__app0(E(_mt)),_Iy=B(_DQ(_Ig,_));return new T(function(){return E(E(_Iy).b);});}},_Iz=new T(function(){return B(unCStr("Negative exponent"));}),_IA=new T(function(){return B(err(_Iz));}),_IB=function(_IC,_ID,_IE){while(1){if(!(_ID%2)){var _IF=_IC*_IC,_IG=quot(_ID,2);_IC=_IF;_ID=_IG;continue;}else{var _IH=E(_ID);if(_IH==1){return _IC*_IE;}else{var _IF=_IC*_IC,_II=_IC*_IE;_IC=_IF;_ID=quot(_IH-1|0,2);_IE=_II;continue;}}}},_IJ=function(_IK,_IL){while(1){if(!(_IL%2)){var _IM=_IK*_IK,_IN=quot(_IL,2);_IK=_IM;_IL=_IN;continue;}else{var _IO=E(_IL);if(_IO==1){return E(_IK);}else{return new F(function(){return _IB(_IK*_IK,quot(_IO-1|0,2),_IK);});}}}},_IP=-4,_IQ=new T3(0,E(_vm),E(_vm),E(_IP)),_IR=function(_IS){return E(_IQ);},_IT=function(_){return new F(function(){return __jsNull();});},_IU=function(_IV){var _IW=B(A1(_IV,_));return E(_IW);},_IX=new T(function(){return B(_IU(_IT));}),_IY=function(_IZ,_J0,_J1,_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb){var _Jc=function(_Jd){var _Je=E(_w5),_Jf=2+_Jd|0,_Jg=_Jf-1|0,_Jh=(2+_Jd)*(1+_Jd),_Ji=E(_wx);if(!_Ji._){return _Je*0;}else{var _Jj=_Ji.a,_Jk=_Ji.b,_Jl=B(A1(_IZ,new T(function(){return 6.283185307179586*E(_Jj)/E(_vx);}))),_Jm=B(A1(_IZ,new T(function(){return 6.283185307179586*(E(_Jj)+1)/E(_vx);})));if(_Jl!=_Jm){if(_Jf>=0){var _Jn=E(_Jf);if(!_Jn){var _Jo=function(_Jp,_Jq){while(1){var _Jr=B((function(_Js,_Jt){var _Ju=E(_Js);if(!_Ju._){return E(_Jt);}else{var _Jv=_Ju.a,_Jw=_Ju.b,_Jx=B(A1(_IZ,new T(function(){return 6.283185307179586*E(_Jv)/E(_vx);}))),_Jy=B(A1(_IZ,new T(function(){return 6.283185307179586*(E(_Jv)+1)/E(_vx);})));if(_Jx!=_Jy){var _Jz=_Jt+0/(_Jx-_Jy)/_Jh;_Jp=_Jw;_Jq=_Jz;return __continue;}else{if(_Jg>=0){var _JA=E(_Jg);if(!_JA){var _Jz=_Jt+_Jf/_Jh;_Jp=_Jw;_Jq=_Jz;return __continue;}else{var _Jz=_Jt+_Jf*B(_IJ(_Jx,_JA))/_Jh;_Jp=_Jw;_Jq=_Jz;return __continue;}}else{return E(_IA);}}}})(_Jp,_Jq));if(_Jr!=__continue){return _Jr;}}};return _Je*B(_Jo(_Jk,0/(_Jl-_Jm)/_Jh));}else{var _JB=function(_JC,_JD){while(1){var _JE=B((function(_JF,_JG){var _JH=E(_JF);if(!_JH._){return E(_JG);}else{var _JI=_JH.a,_JJ=_JH.b,_JK=B(A1(_IZ,new T(function(){return 6.283185307179586*E(_JI)/E(_vx);}))),_JL=B(A1(_IZ,new T(function(){return 6.283185307179586*(E(_JI)+1)/E(_vx);})));if(_JK!=_JL){if(_Jn>=0){var _JM=_JG+(B(_IJ(_JK,_Jn))-B(_IJ(_JL,_Jn)))/(_JK-_JL)/_Jh;_JC=_JJ;_JD=_JM;return __continue;}else{return E(_IA);}}else{if(_Jg>=0){var _JN=E(_Jg);if(!_JN){var _JM=_JG+_Jf/_Jh;_JC=_JJ;_JD=_JM;return __continue;}else{var _JM=_JG+_Jf*B(_IJ(_JK,_JN))/_Jh;_JC=_JJ;_JD=_JM;return __continue;}}else{return E(_IA);}}}})(_JC,_JD));if(_JE!=__continue){return _JE;}}};return _Je*B(_JB(_Jk,(B(_IJ(_Jl,_Jn))-B(_IJ(_Jm,_Jn)))/(_Jl-_Jm)/_Jh));}}else{return E(_IA);}}else{if(_Jg>=0){var _JO=E(_Jg);if(!_JO){var _JP=function(_JQ,_JR){while(1){var _JS=B((function(_JT,_JU){var _JV=E(_JT);if(!_JV._){return E(_JU);}else{var _JW=_JV.a,_JX=_JV.b,_JY=B(A1(_IZ,new T(function(){return 6.283185307179586*E(_JW)/E(_vx);}))),_JZ=B(A1(_IZ,new T(function(){return 6.283185307179586*(E(_JW)+1)/E(_vx);})));if(_JY!=_JZ){if(_Jf>=0){var _K0=E(_Jf);if(!_K0){var _K1=_JU+0/(_JY-_JZ)/_Jh;_JQ=_JX;_JR=_K1;return __continue;}else{var _K1=_JU+(B(_IJ(_JY,_K0))-B(_IJ(_JZ,_K0)))/(_JY-_JZ)/_Jh;_JQ=_JX;_JR=_K1;return __continue;}}else{return E(_IA);}}else{var _K1=_JU+_Jf/_Jh;_JQ=_JX;_JR=_K1;return __continue;}}})(_JQ,_JR));if(_JS!=__continue){return _JS;}}};return _Je*B(_JP(_Jk,_Jf/_Jh));}else{var _K2=function(_K3,_K4){while(1){var _K5=B((function(_K6,_K7){var _K8=E(_K6);if(!_K8._){return E(_K7);}else{var _K9=_K8.a,_Ka=_K8.b,_Kb=B(A1(_IZ,new T(function(){return 6.283185307179586*E(_K9)/E(_vx);}))),_Kc=B(A1(_IZ,new T(function(){return 6.283185307179586*(E(_K9)+1)/E(_vx);})));if(_Kb!=_Kc){if(_Jf>=0){var _Kd=E(_Jf);if(!_Kd){var _Ke=_K7+0/(_Kb-_Kc)/_Jh;_K3=_Ka;_K4=_Ke;return __continue;}else{var _Ke=_K7+(B(_IJ(_Kb,_Kd))-B(_IJ(_Kc,_Kd)))/(_Kb-_Kc)/_Jh;_K3=_Ka;_K4=_Ke;return __continue;}}else{return E(_IA);}}else{if(_JO>=0){var _Ke=_K7+_Jf*B(_IJ(_Kb,_JO))/_Jh;_K3=_Ka;_K4=_Ke;return __continue;}else{return E(_IA);}}}})(_K3,_K4));if(_K5!=__continue){return _K5;}}};return _Je*B(_K2(_Jk,_Jf*B(_IJ(_Jl,_JO))/_Jh));}}else{return E(_IA);}}}},_Kf=E(_IX),_Kg=1/(B(_Jc(1))*_J0);return new F(function(){return _ye(_IZ,_IR,new T2(0,E(new T3(0,E(_Kg),E(_Kg),E(_Kg))),1/(B(_Jc(3))*_J0)),_J1,_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_vn,_Kf,_Kf,0);});},_Kh=0.5,_Ki=1,_Kj=0,_Kk=0.3,_Kl=function(_Km){return E(_Kk);},_Kn=new T(function(){var _Ko=B(_IY(_Kl,1.2,_Kj,_Ki,_Kh,_Kj,_Kj,_Kj,_Kj,_Kj,_Ki,_Ki,_Ki));return {_:0,a:E(_Ko.a),b:E(_Ko.b),c:E(_Ko.c),d:E(_Ko.d),e:E(_Ko.e),f:E(_Ko.f),g:E(_Ko.g),h:_Ko.h,i:_Ko.i,j:_Ko.j};}),_Kp=0,_Kq=function(_){var _Kr=newArr(1,_rw),_=_Kr[0]=_Kn;return new T4(0,E(_Kp),E(_Kp),1,_Kr);},_Ks=new T(function(){return B(_rB(_Kq));}),_Kt=function(_Ku,_){while(1){var _Kv=E(_Ku);if(!_Kv._){return _me;}else{var _Kw=_Kv.b,_Kx=E(_Kv.a);switch(_Kx._){case 0:var _Ky=B(A1(_Kx.a,_));_Ku=B(_n(_Kw,new T2(1,_Ky,_w)));continue;case 1:_Ku=B(_n(_Kw,_Kx.a));continue;default:_Ku=_Kw;continue;}}}},_Kz=function(_KA,_KB,_){var _KC=E(_KA);switch(_KC._){case 0:var _KD=B(A1(_KC.a,_));return new F(function(){return _Kt(B(_n(_KB,new T2(1,_KD,_w))),_);});break;case 1:return new F(function(){return _Kt(B(_n(_KB,_KC.a)),_);});break;default:return new F(function(){return _Kt(_KB,_);});}},_KE=new T0(2),_KF=function(_KG){return new T0(2);},_KH=function(_KI,_KJ,_KK){return function(_){var _KL=E(_KI),_KM=rMV(_KL),_KN=E(_KM);if(!_KN._){var _KO=new T(function(){var _KP=new T(function(){return B(A1(_KK,_me));});return B(_n(_KN.b,new T2(1,new T2(0,_KJ,function(_KQ){return E(_KP);}),_w)));}),_=wMV(_KL,new T2(0,_KN.a,_KO));return _KE;}else{var _KR=E(_KN.a);if(!_KR._){var _=wMV(_KL,new T2(0,_KJ,_w));return new T(function(){return B(A1(_KK,_me));});}else{var _=wMV(_KL,new T1(1,_KR.b));return new T1(1,new T2(1,new T(function(){return B(A1(_KK,_me));}),new T2(1,new T(function(){return B(A2(_KR.a,_KJ,_KF));}),_w)));}}};},_KS=new T(function(){return E(_IX);}),_KT=new T(function(){return eval("window.requestAnimationFrame");}),_KU=new T1(1,_w),_KV=function(_KW,_KX){return function(_){var _KY=E(_KW),_KZ=rMV(_KY),_L0=E(_KZ);if(!_L0._){var _L1=_L0.a,_L2=E(_L0.b);if(!_L2._){var _=wMV(_KY,_KU);return new T(function(){return B(A1(_KX,_L1));});}else{var _L3=E(_L2.a),_=wMV(_KY,new T2(0,_L3.a,_L2.b));return new T1(1,new T2(1,new T(function(){return B(A1(_KX,_L1));}),new T2(1,new T(function(){return B(A1(_L3.b,_KF));}),_w)));}}else{var _L4=new T(function(){var _L5=function(_L6){var _L7=new T(function(){return B(A1(_KX,_L6));});return function(_L8){return E(_L7);};};return B(_n(_L0.a,new T2(1,_L5,_w)));}),_=wMV(_KY,new T1(1,_L4));return _KE;}};},_L9=function(_La,_Lb){return new T1(0,B(_KV(_La,_Lb)));},_Lc=function(_Ld,_Le){var _Lf=new T(function(){return new T1(0,B(_KH(_Ld,_me,_KF)));});return function(_){var _Lg=__createJSFunc(2,function(_Lh,_){var _Li=B(_Kz(_Lf,_w,_));return _KS;}),_Lj=__app1(E(_KT),_Lg);return new T(function(){return B(_L9(_Ld,_Le));});};},_Lk=new T1(1,_w),_Ll=function(_Lm,_Ln,_){var _Lo=function(_){var _Lp=nMV(_Lm),_Lq=_Lp;return new T(function(){var _Lr=new T(function(){return B(_Ls(_));}),_Lt=function(_){var _Lu=rMV(_Lq),_Lv=B(A2(_Ln,_Lu,_)),_=wMV(_Lq,_Lv),_Lw=function(_){var _Lx=nMV(_Lk);return new T(function(){return new T1(0,B(_Lc(_Lx,function(_Ly){return E(_Lr);})));});};return new T1(0,_Lw);},_Lz=new T(function(){return new T1(0,_Lt);}),_Ls=function(_LA){return E(_Lz);};return B(_Ls(_));});};return new F(function(){return _Kz(new T1(0,_Lo),_w,_);});},_LB=new T(function(){return eval("__strict(setBounds)");}),_LC=function(_){var _LD=__app3(E(_lD),E(_lE),E(_m7),E(_lC)),_LE=__app2(E(_LB),E(_iS),E(_iP));return new F(function(){return _Ll(_Ks,_Ic,_);});},_LF=function(_){return new F(function(){return _LC(_);});};
var hasteMain = function() {B(A(_LF, [0]));};window.onload = hasteMain;