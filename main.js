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

var _0=function(_1,_2,_3){return new F(function(){return A1(_1,function(_4){return new F(function(){return A2(_2,_4,_3);});});});},_5=function(_6,_7,_8){var _9=function(_a){var _b=new T(function(){return B(A1(_8,_a));});return new F(function(){return A1(_7,function(_c){return E(_b);});});};return new F(function(){return A1(_6,_9);});},_d=function(_e,_f,_g){var _h=new T(function(){return B(A1(_f,function(_i){return new F(function(){return A1(_g,_i);});}));});return new F(function(){return A1(_e,function(_j){return E(_h);});});},_k=function(_l,_m,_n){var _o=function(_p){var _q=function(_r){return new F(function(){return A1(_n,new T(function(){return B(A1(_p,_r));}));});};return new F(function(){return A1(_m,_q);});};return new F(function(){return A1(_l,_o);});},_s=function(_t,_u){return new F(function(){return A1(_u,_t);});},_v=function(_w,_x,_y){var _z=new T(function(){return B(A1(_y,_w));});return new F(function(){return A1(_x,function(_A){return E(_z);});});},_B=function(_C,_D,_E){var _F=function(_G){return new F(function(){return A1(_E,new T(function(){return B(A1(_C,_G));}));});};return new F(function(){return A1(_D,_F);});},_H=new T2(0,_B,_v),_I=new T5(0,_H,_s,_k,_d,_5),_J=function(_K){return E(E(_K).b);},_L=function(_M,_N){return new F(function(){return A3(_J,_O,_M,function(_P){return E(_N);});});},_Q=function(_R){return new F(function(){return err(_R);});},_O=new T(function(){return new T5(0,_I,_0,_L,_s,_Q);}),_S=0,_T=__Z,_U=function(_V){return new T0(2);},_W=function(_X){var _Y=new T(function(){return B(A1(_X,_U));}),_Z=function(_10){return new T1(1,new T2(1,new T(function(){return B(A1(_10,_S));}),new T2(1,_Y,_T)));};return E(_Z);},_11=function(_12){return E(_12);},_13=new T3(0,_O,_11,_W),_14=function(_15,_16){var _17=E(_15);return (_17._==0)?E(_16):new T2(1,_17.a,new T(function(){return B(_14(_17.b,_16));}));},_18=function(_19,_){while(1){var _1a=E(_19);if(!_1a._){return _S;}else{var _1b=_1a.b,_1c=E(_1a.a);switch(_1c._){case 0:var _1d=B(A1(_1c.a,_));_19=B(_14(_1b,new T2(1,_1d,_T)));continue;case 1:_19=B(_14(_1b,_1c.a));continue;default:_19=_1b;continue;}}}},_1e=function(_1f,_1g,_){var _1h=E(_1f);switch(_1h._){case 0:var _1i=B(A1(_1h.a,_));return new F(function(){return _18(B(_14(_1g,new T2(1,_1i,_T))),_);});break;case 1:return new F(function(){return _18(B(_14(_1g,_1h.a)),_);});break;default:return new F(function(){return _18(_1g,_);});}},_1j=new T(function(){return eval("compile");}),_1k=function(_1l){return E(E(_1l).b);},_1m=function(_1n){return E(E(_1n).a);},_1o=function(_1p,_1q,_1r){var _1s=E(_1r);if(!_1s._){return new F(function(){return A1(_1q,_1s.a);});}else{var _1t=new T(function(){return B(_1k(_1p));}),_1u=new T(function(){return B(_1m(_1p));}),_1v=function(_1w){var _1x=E(_1w);if(!_1x._){return E(_1u);}else{return new F(function(){return A2(_1t,new T(function(){return B(_1o(_1p,_1q,_1x.a));}),new T(function(){return B(_1v(_1x.b));}));});}};return new F(function(){return _1v(_1s.a);});}},_1y=function(_1z){var _1A=E(_1z);if(!_1A._){return __Z;}else{return new F(function(){return _14(_1A.a,new T(function(){return B(_1y(_1A.b));},1));});}},_1B=function(_1C){return new F(function(){return _1y(_1C);});},_1D=new T3(0,_T,_14,_1B),_1E=new T(function(){return B(unCStr(","));}),_1F=new T1(0,_1E),_1G=new T(function(){return B(unCStr("pow("));}),_1H=new T1(0,_1G),_1I=new T(function(){return B(unCStr(")"));}),_1J=new T1(0,_1I),_1K=new T2(1,_1J,_T),_1L=function(_1M,_1N){return new T1(1,new T2(1,_1H,new T2(1,_1M,new T2(1,_1F,new T2(1,_1N,_1K)))));},_1O=new T(function(){return B(unCStr("acos("));}),_1P=new T1(0,_1O),_1Q=function(_1R){return new T1(1,new T2(1,_1P,new T2(1,_1R,_1K)));},_1S=new T(function(){return B(unCStr("acosh("));}),_1T=new T1(0,_1S),_1U=function(_1V){return new T1(1,new T2(1,_1T,new T2(1,_1V,_1K)));},_1W=new T(function(){return B(unCStr("asin("));}),_1X=new T1(0,_1W),_1Y=function(_1Z){return new T1(1,new T2(1,_1X,new T2(1,_1Z,_1K)));},_20=new T(function(){return B(unCStr("asinh("));}),_21=new T1(0,_20),_22=function(_23){return new T1(1,new T2(1,_21,new T2(1,_23,_1K)));},_24=new T(function(){return B(unCStr("atan("));}),_25=new T1(0,_24),_26=function(_27){return new T1(1,new T2(1,_25,new T2(1,_27,_1K)));},_28=new T(function(){return B(unCStr("atanh("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1K)));},_2c=new T(function(){return B(unCStr("cos("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1K)));},_2g=new T(function(){return B(unCStr("cosh("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1K)));},_2k=new T(function(){return B(unCStr("exp("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1K)));},_2o=new T(function(){return B(unCStr("log("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1K)));},_2s=new T(function(){return B(unCStr(")/log("));}),_2t=new T1(0,_2s),_2u=function(_2v,_2w){return new T1(1,new T2(1,_2p,new T2(1,_2w,new T2(1,_2t,new T2(1,_2v,_1K)))));},_2x=new T(function(){return B(unCStr("pi"));}),_2y=new T1(0,_2x),_2z=new T(function(){return B(unCStr("sin("));}),_2A=new T1(0,_2z),_2B=function(_2C){return new T1(1,new T2(1,_2A,new T2(1,_2C,_1K)));},_2D=new T(function(){return B(unCStr("sinh("));}),_2E=new T1(0,_2D),_2F=function(_2G){return new T1(1,new T2(1,_2E,new T2(1,_2G,_1K)));},_2H=new T(function(){return B(unCStr("sqrt("));}),_2I=new T1(0,_2H),_2J=function(_2K){return new T1(1,new T2(1,_2I,new T2(1,_2K,_1K)));},_2L=new T(function(){return B(unCStr("tan("));}),_2M=new T1(0,_2L),_2N=function(_2O){return new T1(1,new T2(1,_2M,new T2(1,_2O,_1K)));},_2P=new T(function(){return B(unCStr("tanh("));}),_2Q=new T1(0,_2P),_2R=function(_2S){return new T1(1,new T2(1,_2Q,new T2(1,_2S,_1K)));},_2T=new T(function(){return B(unCStr("("));}),_2U=new T1(0,_2T),_2V=new T(function(){return B(unCStr(")/("));}),_2W=new T1(0,_2V),_2X=function(_2Y,_2Z){return new T1(1,new T2(1,_2U,new T2(1,_2Y,new T2(1,_2W,new T2(1,_2Z,_1K)))));},_30=new T1(0,1),_31=function(_32,_33){var _34=E(_32);if(!_34._){var _35=_34.a,_36=E(_33);if(!_36._){var _37=_36.a;return (_35!=_37)?(_35>_37)?2:0:1;}else{var _38=I_compareInt(_36.a,_35);return (_38<=0)?(_38>=0)?1:2:0;}}else{var _39=_34.a,_3a=E(_33);if(!_3a._){var _3b=I_compareInt(_39,_3a.a);return (_3b>=0)?(_3b<=0)?1:2:0;}else{var _3c=I_compare(_39,_3a.a);return (_3c>=0)?(_3c<=0)?1:2:0;}}},_3d=new T(function(){return B(unCStr("base"));}),_3e=new T(function(){return B(unCStr("GHC.Exception"));}),_3f=new T(function(){return B(unCStr("ArithException"));}),_3g=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3d,_3e,_3f),_3h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3g,_T,_T),_3i=function(_3j){return E(_3h);},_3k=function(_3l){return E(E(_3l).a);},_3m=function(_3n,_3o,_3p){var _3q=B(A1(_3n,_)),_3r=B(A1(_3o,_)),_3s=hs_eqWord64(_3q.a,_3r.a);if(!_3s){return __Z;}else{var _3t=hs_eqWord64(_3q.b,_3r.b);return (!_3t)?__Z:new T1(1,_3p);}},_3u=function(_3v){var _3w=E(_3v);return new F(function(){return _3m(B(_3k(_3w.a)),_3i,_3w.b);});},_3x=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3y=new T(function(){return B(unCStr("denormal"));}),_3z=new T(function(){return B(unCStr("divide by zero"));}),_3A=new T(function(){return B(unCStr("loss of precision"));}),_3B=new T(function(){return B(unCStr("arithmetic underflow"));}),_3C=new T(function(){return B(unCStr("arithmetic overflow"));}),_3D=function(_3E,_3F){switch(E(_3E)){case 0:return new F(function(){return _14(_3C,_3F);});break;case 1:return new F(function(){return _14(_3B,_3F);});break;case 2:return new F(function(){return _14(_3A,_3F);});break;case 3:return new F(function(){return _14(_3z,_3F);});break;case 4:return new F(function(){return _14(_3y,_3F);});break;default:return new F(function(){return _14(_3x,_3F);});}},_3G=function(_3H){return new F(function(){return _3D(_3H,_T);});},_3I=function(_3J,_3K,_3L){return new F(function(){return _3D(_3K,_3L);});},_3M=44,_3N=93,_3O=91,_3P=function(_3Q,_3R,_3S){var _3T=E(_3R);if(!_3T._){return new F(function(){return unAppCStr("[]",_3S);});}else{var _3U=new T(function(){var _3V=new T(function(){var _3W=function(_3X){var _3Y=E(_3X);if(!_3Y._){return E(new T2(1,_3N,_3S));}else{var _3Z=new T(function(){return B(A2(_3Q,_3Y.a,new T(function(){return B(_3W(_3Y.b));})));});return new T2(1,_3M,_3Z);}};return B(_3W(_3T.b));});return B(A2(_3Q,_3T.a,_3V));});return new T2(1,_3O,_3U);}},_40=function(_41,_42){return new F(function(){return _3P(_3D,_41,_42);});},_43=new T3(0,_3I,_3G,_40),_44=new T(function(){return new T5(0,_3i,_43,_45,_3u,_3G);}),_45=function(_46){return new T2(0,_44,_46);},_47=3,_48=new T(function(){return B(_45(_47));}),_49=new T(function(){return die(_48);}),_4a=function(_4b,_4c){var _4d=E(_4b);return (_4d._==0)?_4d.a*Math.pow(2,_4c):I_toNumber(_4d.a)*Math.pow(2,_4c);},_4e=function(_4f,_4g){var _4h=E(_4f);if(!_4h._){var _4i=_4h.a,_4j=E(_4g);return (_4j._==0)?_4i==_4j.a:(I_compareInt(_4j.a,_4i)==0)?true:false;}else{var _4k=_4h.a,_4l=E(_4g);return (_4l._==0)?(I_compareInt(_4k,_4l.a)==0)?true:false:(I_compare(_4k,_4l.a)==0)?true:false;}},_4m=function(_4n){var _4o=E(_4n);if(!_4o._){return E(_4o.a);}else{return new F(function(){return I_toInt(_4o.a);});}},_4p=function(_4q,_4r){while(1){var _4s=E(_4q);if(!_4s._){var _4t=_4s.a,_4u=E(_4r);if(!_4u._){var _4v=_4u.a,_4w=addC(_4t,_4v);if(!E(_4w.b)){return new T1(0,_4w.a);}else{_4q=new T1(1,I_fromInt(_4t));_4r=new T1(1,I_fromInt(_4v));continue;}}else{_4q=new T1(1,I_fromInt(_4t));_4r=_4u;continue;}}else{var _4x=E(_4r);if(!_4x._){_4q=_4s;_4r=new T1(1,I_fromInt(_4x.a));continue;}else{return new T1(1,I_add(_4s.a,_4x.a));}}}},_4y=function(_4z,_4A){while(1){var _4B=E(_4z);if(!_4B._){var _4C=E(_4B.a);if(_4C==(-2147483648)){_4z=new T1(1,I_fromInt(-2147483648));continue;}else{var _4D=E(_4A);if(!_4D._){var _4E=_4D.a;return new T2(0,new T1(0,quot(_4C,_4E)),new T1(0,_4C%_4E));}else{_4z=new T1(1,I_fromInt(_4C));_4A=_4D;continue;}}}else{var _4F=E(_4A);if(!_4F._){_4z=_4B;_4A=new T1(1,I_fromInt(_4F.a));continue;}else{var _4G=I_quotRem(_4B.a,_4F.a);return new T2(0,new T1(1,_4G.a),new T1(1,_4G.b));}}}},_4H=new T1(0,0),_4I=function(_4J,_4K){while(1){var _4L=E(_4J);if(!_4L._){_4J=new T1(1,I_fromInt(_4L.a));continue;}else{return new T1(1,I_shiftLeft(_4L.a,_4K));}}},_4M=function(_4N,_4O,_4P){if(!B(_4e(_4P,_4H))){var _4Q=B(_4y(_4O,_4P)),_4R=_4Q.a;switch(B(_31(B(_4I(_4Q.b,1)),_4P))){case 0:return new F(function(){return _4a(_4R,_4N);});break;case 1:if(!(B(_4m(_4R))&1)){return new F(function(){return _4a(_4R,_4N);});}else{return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}break;default:return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}}else{return E(_49);}},_4S=function(_4T,_4U){var _4V=E(_4T);if(!_4V._){var _4W=_4V.a,_4X=E(_4U);return (_4X._==0)?_4W>_4X.a:I_compareInt(_4X.a,_4W)<0;}else{var _4Y=_4V.a,_4Z=E(_4U);return (_4Z._==0)?I_compareInt(_4Y,_4Z.a)>0:I_compare(_4Y,_4Z.a)>0;}},_50=new T1(0,1),_51=function(_52,_53){var _54=E(_52);if(!_54._){var _55=_54.a,_56=E(_53);return (_56._==0)?_55<_56.a:I_compareInt(_56.a,_55)>0;}else{var _57=_54.a,_58=E(_53);return (_58._==0)?I_compareInt(_57,_58.a)<0:I_compare(_57,_58.a)<0;}},_59=new T(function(){return B(unCStr("base"));}),_5a=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5b=new T(function(){return B(unCStr("PatternMatchFail"));}),_5c=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_59,_5a,_5b),_5d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5c,_T,_T),_5e=function(_5f){return E(_5d);},_5g=function(_5h){var _5i=E(_5h);return new F(function(){return _3m(B(_3k(_5i.a)),_5e,_5i.b);});},_5j=function(_5k){return E(E(_5k).a);},_5l=function(_5m){return new T2(0,_5n,_5m);},_5o=function(_5p,_5q){return new F(function(){return _14(E(_5p).a,_5q);});},_5r=function(_5s,_5t){return new F(function(){return _3P(_5o,_5s,_5t);});},_5u=function(_5v,_5w,_5x){return new F(function(){return _14(E(_5w).a,_5x);});},_5y=new T3(0,_5u,_5j,_5r),_5n=new T(function(){return new T5(0,_5e,_5y,_5l,_5g,_5j);}),_5z=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5A=function(_5B){return E(E(_5B).c);},_5C=function(_5D,_5E){return new F(function(){return die(new T(function(){return B(A2(_5A,_5E,_5D));}));});},_5F=function(_5G,_46){return new F(function(){return _5C(_5G,_46);});},_5H=function(_5I,_5J){var _5K=E(_5J);if(!_5K._){return new T2(0,_T,_T);}else{var _5L=_5K.a;if(!B(A1(_5I,_5L))){return new T2(0,_T,_5K);}else{var _5M=new T(function(){var _5N=B(_5H(_5I,_5K.b));return new T2(0,_5N.a,_5N.b);});return new T2(0,new T2(1,_5L,new T(function(){return E(E(_5M).a);})),new T(function(){return E(E(_5M).b);}));}}},_5O=32,_5P=new T(function(){return B(unCStr("\n"));}),_5Q=function(_5R){return (E(_5R)==124)?false:true;},_5S=function(_5T,_5U){var _5V=B(_5H(_5Q,B(unCStr(_5T)))),_5W=_5V.a,_5X=function(_5Y,_5Z){var _60=new T(function(){var _61=new T(function(){return B(_14(_5U,new T(function(){return B(_14(_5Z,_5P));},1)));});return B(unAppCStr(": ",_61));},1);return new F(function(){return _14(_5Y,_60);});},_62=E(_5V.b);if(!_62._){return new F(function(){return _5X(_5W,_T);});}else{if(E(_62.a)==124){return new F(function(){return _5X(_5W,new T2(1,_5O,_62.b));});}else{return new F(function(){return _5X(_5W,_T);});}}},_63=function(_64){return new F(function(){return _5F(new T1(0,new T(function(){return B(_5S(_64,_5z));})),_5n);});},_65=function(_66){var _67=function(_68,_69){while(1){if(!B(_51(_68,_66))){if(!B(_4S(_68,_66))){if(!B(_4e(_68,_66))){return new F(function(){return _63("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_69);}}else{return _69-1|0;}}else{var _6a=B(_4I(_68,1)),_6b=_69+1|0;_68=_6a;_69=_6b;continue;}}};return new F(function(){return _67(_50,0);});},_6c=function(_6d){var _6e=E(_6d);if(!_6e._){var _6f=_6e.a>>>0;if(!_6f){return -1;}else{var _6g=function(_6h,_6i){while(1){if(_6h>=_6f){if(_6h<=_6f){if(_6h!=_6f){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6i);}}else{return _6i-1|0;}}else{var _6j=imul(_6h,2)>>>0,_6k=_6i+1|0;_6h=_6j;_6i=_6k;continue;}}};return new F(function(){return _6g(1,0);});}}else{return new F(function(){return _65(_6e);});}},_6l=function(_6m){var _6n=E(_6m);if(!_6n._){var _6o=_6n.a>>>0;if(!_6o){return new T2(0,-1,0);}else{var _6p=function(_6q,_6r){while(1){if(_6q>=_6o){if(_6q<=_6o){if(_6q!=_6o){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6r);}}else{return _6r-1|0;}}else{var _6s=imul(_6q,2)>>>0,_6t=_6r+1|0;_6q=_6s;_6r=_6t;continue;}}};return new T2(0,B(_6p(1,0)),(_6o&_6o-1>>>0)>>>0&4294967295);}}else{var _6u=_6n.a;return new T2(0,B(_6c(_6n)),I_compareInt(I_and(_6u,I_sub(_6u,I_fromInt(1))),0));}},_6v=function(_6w,_6x){var _6y=E(_6w);if(!_6y._){var _6z=_6y.a,_6A=E(_6x);return (_6A._==0)?_6z<=_6A.a:I_compareInt(_6A.a,_6z)>=0;}else{var _6B=_6y.a,_6C=E(_6x);return (_6C._==0)?I_compareInt(_6B,_6C.a)<=0:I_compare(_6B,_6C.a)<=0;}},_6D=function(_6E,_6F){while(1){var _6G=E(_6E);if(!_6G._){var _6H=_6G.a,_6I=E(_6F);if(!_6I._){return new T1(0,(_6H>>>0&_6I.a>>>0)>>>0&4294967295);}else{_6E=new T1(1,I_fromInt(_6H));_6F=_6I;continue;}}else{var _6J=E(_6F);if(!_6J._){_6E=_6G;_6F=new T1(1,I_fromInt(_6J.a));continue;}else{return new T1(1,I_and(_6G.a,_6J.a));}}}},_6K=function(_6L,_6M){while(1){var _6N=E(_6L);if(!_6N._){var _6O=_6N.a,_6P=E(_6M);if(!_6P._){var _6Q=_6P.a,_6R=subC(_6O,_6Q);if(!E(_6R.b)){return new T1(0,_6R.a);}else{_6L=new T1(1,I_fromInt(_6O));_6M=new T1(1,I_fromInt(_6Q));continue;}}else{_6L=new T1(1,I_fromInt(_6O));_6M=_6P;continue;}}else{var _6S=E(_6M);if(!_6S._){_6L=_6N;_6M=new T1(1,I_fromInt(_6S.a));continue;}else{return new T1(1,I_sub(_6N.a,_6S.a));}}}},_6T=new T1(0,2),_6U=function(_6V,_6W){var _6X=E(_6V);if(!_6X._){var _6Y=(_6X.a>>>0&(2<<_6W>>>0)-1>>>0)>>>0,_6Z=1<<_6W>>>0;return (_6Z<=_6Y)?(_6Z>=_6Y)?1:2:0;}else{var _70=B(_6D(_6X,B(_6K(B(_4I(_6T,_6W)),_50)))),_71=B(_4I(_50,_6W));return (!B(_4S(_71,_70)))?(!B(_51(_71,_70)))?1:2:0;}},_72=function(_73,_74){while(1){var _75=E(_73);if(!_75._){_73=new T1(1,I_fromInt(_75.a));continue;}else{return new T1(1,I_shiftRight(_75.a,_74));}}},_76=function(_77,_78,_79,_7a){var _7b=B(_6l(_7a)),_7c=_7b.a;if(!E(_7b.b)){var _7d=B(_6c(_79));if(_7d<((_7c+_77|0)-1|0)){var _7e=_7c+(_77-_78|0)|0;if(_7e>0){if(_7e>_7d){if(_7e<=(_7d+1|0)){if(!E(B(_6l(_79)).b)){return 0;}else{return new F(function(){return _4a(_30,_77-_78|0);});}}else{return 0;}}else{var _7f=B(_72(_79,_7e));switch(B(_6U(_79,_7e-1|0))){case 0:return new F(function(){return _4a(_7f,_77-_78|0);});break;case 1:if(!(B(_4m(_7f))&1)){return new F(function(){return _4a(_7f,_77-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}break;default:return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}}}else{return new F(function(){return _4a(_79,(_77-_78|0)-_7e|0);});}}else{if(_7d>=_78){var _7g=B(_72(_79,(_7d+1|0)-_78|0));switch(B(_6U(_79,_7d-_78|0))){case 0:return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});break;case 2:return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});break;default:if(!(B(_4m(_7g))&1)){return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});}}}else{return new F(function(){return _4a(_79, -_7c);});}}}else{var _7h=B(_6c(_79))-_7c|0,_7i=function(_7j){var _7k=function(_7l,_7m){if(!B(_6v(B(_4I(_7m,_78)),_7l))){return new F(function(){return _4M(_7j-_78|0,_7l,_7m);});}else{return new F(function(){return _4M((_7j-_78|0)+1|0,_7l,B(_4I(_7m,1)));});}};if(_7j>=_78){if(_7j!=_78){return new F(function(){return _7k(_79,new T(function(){return B(_4I(_7a,_7j-_78|0));}));});}else{return new F(function(){return _7k(_79,_7a);});}}else{return new F(function(){return _7k(new T(function(){return B(_4I(_79,_78-_7j|0));}),_7a);});}};if(_77>_7h){return new F(function(){return _7i(_77);});}else{return new F(function(){return _7i(_7h);});}}},_7n=new T1(0,2147483647),_7o=new T(function(){return B(_4p(_7n,_50));}),_7p=function(_7q){var _7r=E(_7q);if(!_7r._){var _7s=E(_7r.a);return (_7s==(-2147483648))?E(_7o):new T1(0, -_7s);}else{return new T1(1,I_negate(_7r.a));}},_7t=new T(function(){return 0/0;}),_7u=new T(function(){return -1/0;}),_7v=new T(function(){return 1/0;}),_7w=0,_7x=function(_7y,_7z){if(!B(_4e(_7z,_4H))){if(!B(_4e(_7y,_4H))){if(!B(_51(_7y,_4H))){return new F(function(){return _76(-1021,53,_7y,_7z);});}else{return  -B(_76(-1021,53,B(_7p(_7y)),_7z));}}else{return E(_7w);}}else{return (!B(_4e(_7y,_4H)))?(!B(_51(_7y,_4H)))?E(_7v):E(_7u):E(_7t);}},_7A=function(_7B){return new T1(0,new T(function(){var _7C=E(_7B),_7D=jsShow(B(_7x(_7C.a,_7C.b)));return fromJSStr(_7D);}));},_7E=new T(function(){return B(unCStr("1./("));}),_7F=new T1(0,_7E),_7G=function(_7H){return new T1(1,new T2(1,_7F,new T2(1,_7H,_1K)));},_7I=new T(function(){return B(unCStr(")+("));}),_7J=new T1(0,_7I),_7K=function(_7L,_7M){return new T1(1,new T2(1,_2U,new T2(1,_7L,new T2(1,_7J,new T2(1,_7M,_1K)))));},_7N=new T(function(){return B(unCStr("-("));}),_7O=new T1(0,_7N),_7P=function(_7Q){return new T1(1,new T2(1,_7O,new T2(1,_7Q,_1K)));},_7R=new T(function(){return B(unCStr(")*("));}),_7S=new T1(0,_7R),_7T=function(_7U,_7V){return new T1(1,new T2(1,_2U,new T2(1,_7U,new T2(1,_7S,new T2(1,_7V,_1K)))));},_7W=function(_7X){return E(E(_7X).a);},_7Y=function(_7Z){return E(E(_7Z).d);},_80=function(_81,_82){return new F(function(){return A3(_7W,_83,_81,new T(function(){return B(A2(_7Y,_83,_82));}));});},_84=new T(function(){return B(unCStr("abs("));}),_85=new T1(0,_84),_86=function(_87){return new T1(1,new T2(1,_85,new T2(1,_87,_1K)));},_88=function(_89){while(1){var _8a=E(_89);if(!_8a._){_89=new T1(1,I_fromInt(_8a.a));continue;}else{return new F(function(){return I_toString(_8a.a);});}}},_8b=function(_8c,_8d){return new F(function(){return _14(fromJSStr(B(_88(_8c))),_8d);});},_8e=41,_8f=40,_8g=new T1(0,0),_8h=function(_8i,_8j,_8k){if(_8i<=6){return new F(function(){return _8b(_8j,_8k);});}else{if(!B(_51(_8j,_8g))){return new F(function(){return _8b(_8j,_8k);});}else{return new T2(1,_8f,new T(function(){return B(_14(fromJSStr(B(_88(_8j))),new T2(1,_8e,_8k)));}));}}},_8l=new T(function(){return B(unCStr("."));}),_8m=function(_8n){return new T1(0,new T(function(){return B(_14(B(_8h(0,_8n,_T)),_8l));}));},_8o=new T(function(){return B(unCStr("sign("));}),_8p=new T1(0,_8o),_8q=function(_8r){return new T1(1,new T2(1,_8p,new T2(1,_8r,_1K)));},_83=new T(function(){return {_:0,a:_7K,b:_80,c:_7T,d:_7P,e:_86,f:_8q,g:_8m};}),_8s=new T4(0,_83,_2X,_7G,_7A),_8t={_:0,a:_8s,b:_2y,c:_2m,d:_2q,e:_2J,f:_1L,g:_2u,h:_2B,i:_2e,j:_2N,k:_1Y,l:_1Q,m:_26,n:_2F,o:_2i,p:_2R,q:_22,r:_1U,s:_2a},_8u=function(_8v){return E(E(_8v).a);},_8w=function(_8x){return E(E(_8x).a);},_8y=function(_8z){return E(E(_8z).c);},_8A=function(_8B){return E(E(_8B).b);},_8C=function(_8D){return E(E(_8D).d);},_8E=new T1(0,1),_8F=new T1(0,2),_8G=new T2(0,E(_8E),E(_8F)),_8H=new T1(0,5),_8I=new T1(0,4),_8J=new T2(0,E(_8I),E(_8H)),_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O,_8P,_8Q){var _8R=B(_8u(_8N)),_8S=B(_8w(_8R)),_8T=new T(function(){var _8U=new T(function(){var _8V=new T(function(){var _8W=new T(function(){var _8X=new T(function(){var _8Y=new T(function(){return B(A3(_7W,_8S,new T(function(){return B(A3(_8y,_8S,_8O,_8O));}),new T(function(){return B(A3(_8y,_8S,_8Q,_8Q));})));});return B(A2(_8K,_8N,_8Y));});return B(A3(_8A,_8S,_8X,new T(function(){return B(A2(_8C,_8R,_8J));})));});return B(A3(_8y,_8S,_8W,_8W));});return B(A3(_7W,_8S,_8V,new T(function(){return B(A3(_8y,_8S,_8P,_8P));})));});return B(A2(_8K,_8N,_8U));});return new F(function(){return A3(_8A,_8S,_8T,new T(function(){return B(A2(_8C,_8R,_8G));}));});},_8Z=new T(function(){return B(unCStr("x"));}),_90=new T1(0,_8Z),_91=new T(function(){return B(unCStr("y"));}),_92=new T1(0,_91),_93=new T(function(){return B(unCStr("z"));}),_94=new T1(0,_93),_95=new T(function(){return B(_8M(_8t,_90,_92,_94));}),_96=new T(function(){return toJSStr(B(_1o(_1D,_11,_95)));}),_97=function(_98,_99,_9a){var _9b=new T(function(){return B(_1k(_98));}),_9c=new T(function(){return B(_1m(_98));}),_9d=function(_9e){var _9f=E(_9e);if(!_9f._){return E(_9c);}else{return new F(function(){return A2(_9b,new T(function(){return B(_1o(_98,_99,_9f.a));}),new T(function(){return B(_9d(_9f.b));}));});}};return new F(function(){return _9d(_9a);});},_9g=new T3(0,E(_90),E(_92),E(_94)),_9h=new T(function(){return B(unCStr("(/=) is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("(==) is not defined"));}),_9k=new T(function(){return B(err(_9j));}),_9l=new T2(0,_9k,_9i),_9m=new T(function(){return B(unCStr("(<) is not defined"));}),_9n=new T(function(){return B(err(_9m));}),_9o=new T(function(){return B(unCStr("(<=) is not defined"));}),_9p=new T(function(){return B(err(_9o));}),_9q=new T(function(){return B(unCStr("(>) is not defined"));}),_9r=new T(function(){return B(err(_9q));}),_9s=new T(function(){return B(unCStr("(>=) is not defined"));}),_9t=new T(function(){return B(err(_9s));}),_9u=new T(function(){return B(unCStr("compare is not defined"));}),_9v=new T(function(){return B(err(_9u));}),_9w=new T(function(){return B(unCStr("max("));}),_9x=new T1(0,_9w),_9y=function(_9z,_9A){return new T1(1,new T2(1,_9x,new T2(1,_9z,new T2(1,_1F,new T2(1,_9A,_1K)))));},_9B=new T(function(){return B(unCStr("min("));}),_9C=new T1(0,_9B),_9D=function(_9E,_9F){return new T1(1,new T2(1,_9C,new T2(1,_9E,new T2(1,_1F,new T2(1,_9F,_1K)))));},_9G={_:0,a:_9l,b:_9v,c:_9n,d:_9p,e:_9r,f:_9t,g:_9y,h:_9D},_9H=new T2(0,_8t,_9G),_9I=function(_9J,_9K){var _9L=E(_9J);return E(_9K);},_9M=function(_9N,_9O){var _9P=E(_9O);return E(_9N);},_9Q=function(_9R,_9S){var _9T=E(_9R),_9U=E(_9S);return new T3(0,E(B(A1(_9T.a,_9U.a))),E(B(A1(_9T.b,_9U.b))),E(B(A1(_9T.c,_9U.c))));},_9V=function(_9W,_9X,_9Y){return new T3(0,E(_9W),E(_9X),E(_9Y));},_9Z=function(_a0){return new F(function(){return _9V(_a0,_a0,_a0);});},_a1=function(_a2,_a3){var _a4=E(_a3),_a5=E(_a2);return new T3(0,E(_a5),E(_a5),E(_a5));},_a6=function(_a7,_a8){var _a9=E(_a8);return new T3(0,E(B(A1(_a7,_a9.a))),E(B(A1(_a7,_a9.b))),E(B(A1(_a7,_a9.c))));},_aa=new T2(0,_a6,_a1),_ab=new T5(0,_aa,_9Z,_9Q,_9I,_9M),_ac=new T1(0,0),_ad=function(_ae){return E(E(_ae).g);},_af=function(_ag){var _ah=B(A2(_ad,_ag,_8E)),_ai=B(A2(_ad,_ag,_ac));return new T3(0,E(new T3(0,E(_ah),E(_ai),E(_ai))),E(new T3(0,E(_ai),E(_ah),E(_ai))),E(new T3(0,E(_ai),E(_ai),E(_ah))));},_aj=function(_ak){return E(E(_ak).a);},_al=function(_am){return E(E(_am).f);},_an=function(_ao){return E(E(_ao).b);},_ap=function(_aq){return E(E(_aq).c);},_ar=function(_as){return E(E(_as).a);},_at=function(_au){return E(E(_au).d);},_av=function(_aw,_ax,_ay,_az,_aA){var _aB=new T(function(){return E(E(E(_aw).c).a);}),_aC=new T(function(){var _aD=E(_aw).a,_aE=new T(function(){var _aF=new T(function(){return B(_8u(_aB));}),_aG=new T(function(){return B(_8w(_aF));}),_aH=new T(function(){return B(A2(_at,_aB,_ax));}),_aI=new T(function(){return B(A3(_al,_aB,_ax,_az));}),_aJ=function(_aK,_aL){var _aM=new T(function(){var _aN=new T(function(){return B(A3(_an,_aF,new T(function(){return B(A3(_8y,_aG,_az,_aK));}),_ax));});return B(A3(_7W,_aG,_aN,new T(function(){return B(A3(_8y,_aG,_aL,_aH));})));});return new F(function(){return A3(_8y,_aG,_aI,_aM);});};return B(A3(_ar,B(_aj(_aD)),_aJ,_ay));});return B(A3(_ap,_aD,_aE,_aA));});return new T2(0,new T(function(){return B(A3(_al,_aB,_ax,_az));}),_aC);},_aO=function(_aP,_aQ,_aR,_aS){var _aT=E(_aR),_aU=E(_aS),_aV=B(_av(_aQ,_aT.a,_aT.b,_aU.a,_aU.b));return new T2(0,_aV.a,_aV.b);},_aW=new T1(0,1),_aX=function(_aY){return E(E(_aY).l);},_aZ=function(_b0,_b1,_b2){var _b3=new T(function(){return E(E(E(_b0).c).a);}),_b4=new T(function(){var _b5=new T(function(){return B(_8u(_b3));}),_b6=new T(function(){var _b7=B(_8w(_b5)),_b8=new T(function(){var _b9=new T(function(){return B(A3(_8A,_b7,new T(function(){return B(A2(_ad,_b7,_aW));}),new T(function(){return B(A3(_8y,_b7,_b1,_b1));})));});return B(A2(_8K,_b3,_b9));});return B(A2(_7Y,_b7,_b8));});return B(A3(_ar,B(_aj(E(_b0).a)),function(_ba){return new F(function(){return A3(_an,_b5,_ba,_b6);});},_b2));});return new T2(0,new T(function(){return B(A2(_aX,_b3,_b1));}),_b4);},_bb=function(_bc,_bd,_be){var _bf=E(_be),_bg=B(_aZ(_bd,_bf.a,_bf.b));return new T2(0,_bg.a,_bg.b);},_bh=function(_bi){return E(E(_bi).r);},_bj=function(_bk,_bl,_bm){var _bn=new T(function(){return E(E(E(_bk).c).a);}),_bo=new T(function(){var _bp=new T(function(){return B(_8u(_bn));}),_bq=new T(function(){var _br=new T(function(){var _bs=B(_8w(_bp));return B(A3(_8A,_bs,new T(function(){return B(A3(_8y,_bs,_bl,_bl));}),new T(function(){return B(A2(_ad,_bs,_aW));})));});return B(A2(_8K,_bn,_br));});return B(A3(_ar,B(_aj(E(_bk).a)),function(_bt){return new F(function(){return A3(_an,_bp,_bt,_bq);});},_bm));});return new T2(0,new T(function(){return B(A2(_bh,_bn,_bl));}),_bo);},_bu=function(_bv,_bw,_bx){var _by=E(_bx),_bz=B(_bj(_bw,_by.a,_by.b));return new T2(0,_bz.a,_bz.b);},_bA=function(_bB){return E(E(_bB).k);},_bC=function(_bD,_bE,_bF){var _bG=new T(function(){return E(E(E(_bD).c).a);}),_bH=new T(function(){var _bI=new T(function(){return B(_8u(_bG));}),_bJ=new T(function(){var _bK=new T(function(){var _bL=B(_8w(_bI));return B(A3(_8A,_bL,new T(function(){return B(A2(_ad,_bL,_aW));}),new T(function(){return B(A3(_8y,_bL,_bE,_bE));})));});return B(A2(_8K,_bG,_bK));});return B(A3(_ar,B(_aj(E(_bD).a)),function(_bM){return new F(function(){return A3(_an,_bI,_bM,_bJ);});},_bF));});return new T2(0,new T(function(){return B(A2(_bA,_bG,_bE));}),_bH);},_bN=function(_bO,_bP,_bQ){var _bR=E(_bQ),_bS=B(_bC(_bP,_bR.a,_bR.b));return new T2(0,_bS.a,_bS.b);},_bT=function(_bU){return E(E(_bU).q);},_bV=function(_bW,_bX,_bY){var _bZ=new T(function(){return E(E(E(_bW).c).a);}),_c0=new T(function(){var _c1=new T(function(){return B(_8u(_bZ));}),_c2=new T(function(){var _c3=new T(function(){var _c4=B(_8w(_c1));return B(A3(_7W,_c4,new T(function(){return B(A3(_8y,_c4,_bX,_bX));}),new T(function(){return B(A2(_ad,_c4,_aW));})));});return B(A2(_8K,_bZ,_c3));});return B(A3(_ar,B(_aj(E(_bW).a)),function(_c5){return new F(function(){return A3(_an,_c1,_c5,_c2);});},_bY));});return new T2(0,new T(function(){return B(A2(_bT,_bZ,_bX));}),_c0);},_c6=function(_c7,_c8,_c9){var _ca=E(_c9),_cb=B(_bV(_c8,_ca.a,_ca.b));return new T2(0,_cb.a,_cb.b);},_cc=function(_cd){return E(E(_cd).m);},_ce=function(_cf,_cg,_ch){var _ci=new T(function(){return E(E(E(_cf).c).a);}),_cj=new T(function(){var _ck=new T(function(){return B(_8u(_ci));}),_cl=new T(function(){var _cm=B(_8w(_ck));return B(A3(_7W,_cm,new T(function(){return B(A2(_ad,_cm,_aW));}),new T(function(){return B(A3(_8y,_cm,_cg,_cg));})));});return B(A3(_ar,B(_aj(E(_cf).a)),function(_cn){return new F(function(){return A3(_an,_ck,_cn,_cl);});},_ch));});return new T2(0,new T(function(){return B(A2(_cc,_ci,_cg));}),_cj);},_co=function(_cp,_cq,_cr){var _cs=E(_cr),_ct=B(_ce(_cq,_cs.a,_cs.b));return new T2(0,_ct.a,_ct.b);},_cu=function(_cv){return E(E(_cv).s);},_cw=function(_cx,_cy,_cz){var _cA=new T(function(){return E(E(E(_cx).c).a);}),_cB=new T(function(){var _cC=new T(function(){return B(_8u(_cA));}),_cD=new T(function(){var _cE=B(_8w(_cC));return B(A3(_8A,_cE,new T(function(){return B(A2(_ad,_cE,_aW));}),new T(function(){return B(A3(_8y,_cE,_cy,_cy));})));});return B(A3(_ar,B(_aj(E(_cx).a)),function(_cF){return new F(function(){return A3(_an,_cC,_cF,_cD);});},_cz));});return new T2(0,new T(function(){return B(A2(_cu,_cA,_cy));}),_cB);},_cG=function(_cH,_cI,_cJ){var _cK=E(_cJ),_cL=B(_cw(_cI,_cK.a,_cK.b));return new T2(0,_cL.a,_cL.b);},_cM=function(_cN){return E(E(_cN).i);},_cO=function(_cP){return E(E(_cP).h);},_cQ=function(_cR,_cS,_cT){var _cU=new T(function(){return E(E(E(_cR).c).a);}),_cV=new T(function(){var _cW=new T(function(){return B(_8w(new T(function(){return B(_8u(_cU));})));}),_cX=new T(function(){return B(A2(_7Y,_cW,new T(function(){return B(A2(_cO,_cU,_cS));})));});return B(A3(_ar,B(_aj(E(_cR).a)),function(_cY){return new F(function(){return A3(_8y,_cW,_cY,_cX);});},_cT));});return new T2(0,new T(function(){return B(A2(_cM,_cU,_cS));}),_cV);},_cZ=function(_d0,_d1,_d2){var _d3=E(_d2),_d4=B(_cQ(_d1,_d3.a,_d3.b));return new T2(0,_d4.a,_d4.b);},_d5=function(_d6){return E(E(_d6).o);},_d7=function(_d8){return E(E(_d8).n);},_d9=function(_da,_db,_dc){var _dd=new T(function(){return E(E(E(_da).c).a);}),_de=new T(function(){var _df=new T(function(){return B(_8w(new T(function(){return B(_8u(_dd));})));}),_dg=new T(function(){return B(A2(_d7,_dd,_db));});return B(A3(_ar,B(_aj(E(_da).a)),function(_dh){return new F(function(){return A3(_8y,_df,_dh,_dg);});},_dc));});return new T2(0,new T(function(){return B(A2(_d5,_dd,_db));}),_de);},_di=function(_dj,_dk,_dl){var _dm=E(_dl),_dn=B(_d9(_dk,_dm.a,_dm.b));return new T2(0,_dn.a,_dn.b);},_do=function(_dp){return E(E(_dp).c);},_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_8w(new T(function(){return B(_8u(_du));})));}),_dx=new T(function(){return B(A2(_do,_du,_ds));});return B(A3(_ar,B(_aj(E(_dr).a)),function(_dy){return new F(function(){return A3(_8y,_dw,_dy,_dx);});},_dt));});return new T2(0,new T(function(){return B(A2(_do,_du,_ds));}),_dv);},_dz=function(_dA,_dB,_dC){var _dD=E(_dC),_dE=B(_dq(_dB,_dD.a,_dD.b));return new T2(0,_dE.a,_dE.b);},_dF=function(_dG,_dH,_dI){var _dJ=new T(function(){return E(E(E(_dG).c).a);}),_dK=new T(function(){var _dL=new T(function(){return B(_8u(_dJ));}),_dM=new T(function(){return B(_8w(_dL));}),_dN=new T(function(){return B(A3(_an,_dL,new T(function(){return B(A2(_ad,_dM,_aW));}),_dH));});return B(A3(_ar,B(_aj(E(_dG).a)),function(_dO){return new F(function(){return A3(_8y,_dM,_dO,_dN);});},_dI));});return new T2(0,new T(function(){return B(A2(_at,_dJ,_dH));}),_dK);},_dP=function(_dQ,_dR,_dS){var _dT=E(_dS),_dU=B(_dF(_dR,_dT.a,_dT.b));return new T2(0,_dU.a,_dU.b);},_dV=function(_dW,_dX,_dY,_dZ){var _e0=new T(function(){return E(E(_dX).c);}),_e1=new T3(0,new T(function(){return E(E(_dX).a);}),new T(function(){return E(E(_dX).b);}),new T2(0,new T(function(){return E(E(_e0).a);}),new T(function(){return E(E(_e0).b);})));return new F(function(){return A3(_an,_dW,new T(function(){var _e2=E(_dZ),_e3=B(_dF(_e1,_e2.a,_e2.b));return new T2(0,_e3.a,_e3.b);}),new T(function(){var _e4=E(_dY),_e5=B(_dF(_e1,_e4.a,_e4.b));return new T2(0,_e5.a,_e5.b);}));});},_e6=new T1(0,0),_e7=function(_e8){return E(E(_e8).b);},_e9=function(_ea){return E(E(_ea).b);},_eb=function(_ec){var _ed=new T(function(){return E(E(E(_ec).c).a);}),_ee=new T(function(){return B(A2(_e9,E(_ec).a,new T(function(){return B(A2(_ad,B(_8w(B(_8u(_ed)))),_e6));})));});return new T2(0,new T(function(){return B(_e7(_ed));}),_ee);},_ef=function(_eg,_eh){var _ei=B(_eb(_eh));return new T2(0,_ei.a,_ei.b);},_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(E(_ek).c).a);}),_eo=new T(function(){var _ep=new T(function(){return B(_8w(new T(function(){return B(_8u(_en));})));}),_eq=new T(function(){return B(A2(_cM,_en,_el));});return B(A3(_ar,B(_aj(E(_ek).a)),function(_er){return new F(function(){return A3(_8y,_ep,_er,_eq);});},_em));});return new T2(0,new T(function(){return B(A2(_cO,_en,_el));}),_eo);},_es=function(_et,_eu,_ev){var _ew=E(_ev),_ex=B(_ej(_eu,_ew.a,_ew.b));return new T2(0,_ex.a,_ex.b);},_ey=function(_ez,_eA,_eB){var _eC=new T(function(){return E(E(E(_ez).c).a);}),_eD=new T(function(){var _eE=new T(function(){return B(_8w(new T(function(){return B(_8u(_eC));})));}),_eF=new T(function(){return B(A2(_d5,_eC,_eA));});return B(A3(_ar,B(_aj(E(_ez).a)),function(_eG){return new F(function(){return A3(_8y,_eE,_eG,_eF);});},_eB));});return new T2(0,new T(function(){return B(A2(_d7,_eC,_eA));}),_eD);},_eH=function(_eI,_eJ,_eK){var _eL=E(_eK),_eM=B(_ey(_eJ,_eL.a,_eL.b));return new T2(0,_eM.a,_eM.b);},_eN=new T1(0,2),_eO=function(_eP,_eQ,_eR){var _eS=new T(function(){return E(E(E(_eP).c).a);}),_eT=new T(function(){var _eU=new T(function(){return B(_8u(_eS));}),_eV=new T(function(){return B(_8w(_eU));}),_eW=new T(function(){var _eX=new T(function(){return B(A3(_an,_eU,new T(function(){return B(A2(_ad,_eV,_aW));}),new T(function(){return B(A2(_ad,_eV,_eN));})));});return B(A3(_an,_eU,_eX,new T(function(){return B(A2(_8K,_eS,_eQ));})));});return B(A3(_ar,B(_aj(E(_eP).a)),function(_eY){return new F(function(){return A3(_8y,_eV,_eY,_eW);});},_eR));});return new T2(0,new T(function(){return B(A2(_8K,_eS,_eQ));}),_eT);},_eZ=function(_f0,_f1,_f2){var _f3=E(_f2),_f4=B(_eO(_f1,_f3.a,_f3.b));return new T2(0,_f4.a,_f4.b);},_f5=function(_f6){return E(E(_f6).j);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return E(E(E(_f8).c).a);}),_fc=new T(function(){var _fd=new T(function(){return B(_8u(_fb));}),_fe=new T(function(){var _ff=new T(function(){return B(A2(_cM,_fb,_f9));});return B(A3(_8y,B(_8w(_fd)),_ff,_ff));});return B(A3(_ar,B(_aj(E(_f8).a)),function(_fg){return new F(function(){return A3(_an,_fd,_fg,_fe);});},_fa));});return new T2(0,new T(function(){return B(A2(_f5,_fb,_f9));}),_fc);},_fh=function(_fi,_fj,_fk){var _fl=E(_fk),_fm=B(_f7(_fj,_fl.a,_fl.b));return new T2(0,_fm.a,_fm.b);},_fn=function(_fo){return E(E(_fo).p);},_fp=function(_fq,_fr,_fs){var _ft=new T(function(){return E(E(E(_fq).c).a);}),_fu=new T(function(){var _fv=new T(function(){return B(_8u(_ft));}),_fw=new T(function(){var _fx=new T(function(){return B(A2(_d5,_ft,_fr));});return B(A3(_8y,B(_8w(_fv)),_fx,_fx));});return B(A3(_ar,B(_aj(E(_fq).a)),function(_fy){return new F(function(){return A3(_an,_fv,_fy,_fw);});},_fs));});return new T2(0,new T(function(){return B(A2(_fn,_ft,_fr));}),_fu);},_fz=function(_fA,_fB,_fC){var _fD=E(_fC),_fE=B(_fp(_fB,_fD.a,_fD.b));return new T2(0,_fE.a,_fE.b);},_fF=function(_fG,_fH){return {_:0,a:_fG,b:new T(function(){return B(_ef(_fG,_fH));}),c:function(_fI){return new F(function(){return _dz(_fG,_fH,_fI);});},d:function(_fI){return new F(function(){return _dP(_fG,_fH,_fI);});},e:function(_fI){return new F(function(){return _eZ(_fG,_fH,_fI);});},f:function(_fJ,_fI){return new F(function(){return _aO(_fG,_fH,_fJ,_fI);});},g:function(_fJ,_fI){return new F(function(){return _dV(_fG,_fH,_fJ,_fI);});},h:function(_fI){return new F(function(){return _es(_fG,_fH,_fI);});},i:function(_fI){return new F(function(){return _cZ(_fG,_fH,_fI);});},j:function(_fI){return new F(function(){return _fh(_fG,_fH,_fI);});},k:function(_fI){return new F(function(){return _bN(_fG,_fH,_fI);});},l:function(_fI){return new F(function(){return _bb(_fG,_fH,_fI);});},m:function(_fI){return new F(function(){return _co(_fG,_fH,_fI);});},n:function(_fI){return new F(function(){return _eH(_fG,_fH,_fI);});},o:function(_fI){return new F(function(){return _di(_fG,_fH,_fI);});},p:function(_fI){return new F(function(){return _fz(_fG,_fH,_fI);});},q:function(_fI){return new F(function(){return _c6(_fG,_fH,_fI);});},r:function(_fI){return new F(function(){return _bu(_fG,_fH,_fI);});},s:function(_fI){return new F(function(){return _cG(_fG,_fH,_fI);});}};},_fK=function(_fL,_fM,_fN,_fO,_fP){var _fQ=new T(function(){return B(_8u(new T(function(){return E(E(E(_fL).c).a);})));}),_fR=new T(function(){var _fS=E(_fL).a,_fT=new T(function(){var _fU=new T(function(){return B(_8w(_fQ));}),_fV=new T(function(){return B(A3(_8y,_fU,_fO,_fO));}),_fW=function(_fX,_fY){var _fZ=new T(function(){return B(A3(_8A,_fU,new T(function(){return B(A3(_8y,_fU,_fX,_fO));}),new T(function(){return B(A3(_8y,_fU,_fM,_fY));})));});return new F(function(){return A3(_an,_fQ,_fZ,_fV);});};return B(A3(_ar,B(_aj(_fS)),_fW,_fN));});return B(A3(_ap,_fS,_fT,_fP));});return new T2(0,new T(function(){return B(A3(_an,_fQ,_fM,_fO));}),_fR);},_g0=function(_g1,_g2,_g3,_g4){var _g5=E(_g3),_g6=E(_g4),_g7=B(_fK(_g2,_g5.a,_g5.b,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8u(new T(function(){return E(E(E(_g9).c).a);})));}),_gc=new T(function(){return B(A2(_e9,E(_g9).a,new T(function(){return B(A2(_ad,B(_8w(_gb)),_e6));})));});return new T2(0,new T(function(){return B(A2(_8C,_gb,_ga));}),_gc);},_gd=function(_ge,_gf,_gg){var _gh=B(_g8(_gf,_gg));return new T2(0,_gh.a,_gh.b);},_gi=function(_gj,_gk,_gl){var _gm=new T(function(){return B(_8u(new T(function(){return E(E(E(_gj).c).a);})));}),_gn=new T(function(){return B(_8w(_gm));}),_go=new T(function(){var _gp=new T(function(){var _gq=new T(function(){return B(A3(_an,_gm,new T(function(){return B(A2(_ad,_gn,_aW));}),new T(function(){return B(A3(_8y,_gn,_gk,_gk));})));});return B(A2(_7Y,_gn,_gq));});return B(A3(_ar,B(_aj(E(_gj).a)),function(_gr){return new F(function(){return A3(_8y,_gn,_gr,_gp);});},_gl));}),_gs=new T(function(){return B(A3(_an,_gm,new T(function(){return B(A2(_ad,_gn,_aW));}),_gk));});return new T2(0,_gs,_go);},_gt=function(_gu,_gv,_gw){var _gx=E(_gw),_gy=B(_gi(_gv,_gx.a,_gx.b));return new T2(0,_gy.a,_gy.b);},_gz=function(_gA,_gB){return new T4(0,_gA,function(_fJ,_fI){return new F(function(){return _g0(_gA,_gB,_fJ,_fI);});},function(_fI){return new F(function(){return _gt(_gA,_gB,_fI);});},function(_fI){return new F(function(){return _gd(_gA,_gB,_fI);});});},_gC=function(_gD,_gE,_gF,_gG,_gH){var _gI=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_gD).c).a);})));})));}),_gJ=new T(function(){var _gK=E(_gD).a,_gL=new T(function(){var _gM=function(_gN,_gO){return new F(function(){return A3(_7W,_gI,new T(function(){return B(A3(_8y,_gI,_gE,_gO));}),new T(function(){return B(A3(_8y,_gI,_gN,_gG));}));});};return B(A3(_ar,B(_aj(_gK)),_gM,_gF));});return B(A3(_ap,_gK,_gL,_gH));});return new T2(0,new T(function(){return B(A3(_8y,_gI,_gE,_gG));}),_gJ);},_gP=function(_gQ,_gR,_gS){var _gT=E(_gR),_gU=E(_gS),_gV=B(_gC(_gQ,_gT.a,_gT.b,_gU.a,_gU.b));return new T2(0,_gV.a,_gV.b);},_gW=function(_gX,_gY,_gZ,_h0,_h1){var _h2=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_gX).c).a);})));})));}),_h3=new T(function(){var _h4=E(_gX).a,_h5=new T(function(){return B(A3(_ar,B(_aj(_h4)),new T(function(){return B(_7W(_h2));}),_gZ));});return B(A3(_ap,_h4,_h5,_h1));});return new T2(0,new T(function(){return B(A3(_7W,_h2,_gY,_h0));}),_h3);},_h6=function(_h7,_h8,_h9){var _ha=E(_h8),_hb=E(_h9),_hc=B(_gW(_h7,_ha.a,_ha.b,_hb.a,_hb.b));return new T2(0,_hc.a,_hc.b);},_hd=function(_he,_hf,_hg){var _hh=B(_hi(_he));return new F(function(){return A3(_7W,_hh,_hf,new T(function(){return B(A2(_7Y,_hh,_hg));}));});},_hj=function(_hk){return E(E(_hk).e);},_hl=function(_hm){return E(E(_hm).f);},_hn=function(_ho,_hp,_hq){var _hr=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_ho).c).a);})));})));}),_hs=new T(function(){var _ht=new T(function(){return B(A2(_hl,_hr,_hp));});return B(A3(_ar,B(_aj(E(_ho).a)),function(_hu){return new F(function(){return A3(_8y,_hr,_hu,_ht);});},_hq));});return new T2(0,new T(function(){return B(A2(_hj,_hr,_hp));}),_hs);},_hv=function(_hw,_hx){var _hy=E(_hx),_hz=B(_hn(_hw,_hy.a,_hy.b));return new T2(0,_hz.a,_hz.b);},_hA=function(_hB,_hC){var _hD=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hB).c).a);})));})));}),_hE=new T(function(){return B(A2(_e9,E(_hB).a,new T(function(){return B(A2(_ad,_hD,_e6));})));});return new T2(0,new T(function(){return B(A2(_ad,_hD,_hC));}),_hE);},_hF=function(_hG,_hH){var _hI=B(_hA(_hG,_hH));return new T2(0,_hI.a,_hI.b);},_hJ=function(_hK,_hL,_hM){var _hN=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hK).c).a);})));})));}),_hO=new T(function(){return B(A3(_ar,B(_aj(E(_hK).a)),new T(function(){return B(_7Y(_hN));}),_hM));});return new T2(0,new T(function(){return B(A2(_7Y,_hN,_hL));}),_hO);},_hP=function(_hQ,_hR){var _hS=E(_hR),_hT=B(_hJ(_hQ,_hS.a,_hS.b));return new T2(0,_hT.a,_hT.b);},_hU=function(_hV,_hW){var _hX=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hV).c).a);})));})));}),_hY=new T(function(){return B(A2(_e9,E(_hV).a,new T(function(){return B(A2(_ad,_hX,_e6));})));});return new T2(0,new T(function(){return B(A2(_hl,_hX,_hW));}),_hY);},_hZ=function(_i0,_i1){var _i2=B(_hU(_i0,E(_i1).a));return new T2(0,_i2.a,_i2.b);},_hi=function(_i3){return {_:0,a:function(_fJ,_fI){return new F(function(){return _h6(_i3,_fJ,_fI);});},b:function(_fJ,_fI){return new F(function(){return _hd(_i3,_fJ,_fI);});},c:function(_fJ,_fI){return new F(function(){return _gP(_i3,_fJ,_fI);});},d:function(_fI){return new F(function(){return _hP(_i3,_fI);});},e:function(_fI){return new F(function(){return _hv(_i3,_fI);});},f:function(_fI){return new F(function(){return _hZ(_i3,_fI);});},g:function(_fI){return new F(function(){return _hF(_i3,_fI);});}};},_i4=function(_i5){var _i6=new T(function(){return E(E(_i5).a);}),_i7=new T3(0,_ab,_af,new T2(0,_i6,new T(function(){return E(E(_i5).b);}))),_i8=new T(function(){return B(_fF(new T(function(){return B(_gz(new T(function(){return B(_hi(_i7));}),_i7));}),_i7));}),_i9=new T(function(){return B(_8w(new T(function(){return B(_8u(_i6));})));});return function(_ia){var _ib=E(_ia),_ic=B(A2(_ad,_i9,_8E)),_id=B(A2(_ad,_i9,_ac));return E(B(_8M(_i8,new T2(0,_ib.a,new T3(0,E(_ic),E(_id),E(_id))),new T2(0,_ib.b,new T3(0,E(_id),E(_ic),E(_id))),new T2(0,_ib.c,new T3(0,E(_id),E(_id),E(_ic))))).b);};},_ie=new T(function(){return B(_i4(_9H));}),_if=function(_ig,_ih){var _ii=E(_ih);return (_ii._==0)?__Z:new T2(1,_ig,new T2(1,_ii.a,new T(function(){return B(_if(_ig,_ii.b));})));},_ij=new T(function(){var _ik=B(A1(_ie,_9g));return new T2(1,_ik.a,new T(function(){return B(_if(_1F,new T2(1,_ik.b,new T2(1,_ik.c,_T))));}));}),_il=new T1(1,_ij),_im=new T2(1,_il,_1K),_in=new T(function(){return B(unCStr("vec3("));}),_io=new T1(0,_in),_ip=new T2(1,_io,_im),_iq=new T(function(){return toJSStr(B(_97(_1D,_11,_ip)));}),_ir=function(_is,_it){while(1){var _iu=E(_is);if(!_iu._){return E(_it);}else{var _iv=_it+1|0;_is=_iu.b;_it=_iv;continue;}}},_iw=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ix=new T(function(){return B(err(_iw));}),_iy=0,_iz=new T3(0,E(_iy),E(_iy),E(_iy)),_iA=new T(function(){return B(unCStr("Negative exponent"));}),_iB=new T(function(){return B(err(_iA));}),_iC=function(_iD,_iE,_iF){while(1){if(!(_iE%2)){var _iG=_iD*_iD,_iH=quot(_iE,2);_iD=_iG;_iE=_iH;continue;}else{var _iI=E(_iE);if(_iI==1){return _iD*_iF;}else{var _iG=_iD*_iD,_iJ=_iD*_iF;_iD=_iG;_iE=quot(_iI-1|0,2);_iF=_iJ;continue;}}}},_iK=function(_iL,_iM){while(1){if(!(_iM%2)){var _iN=_iL*_iL,_iO=quot(_iM,2);_iL=_iN;_iM=_iO;continue;}else{var _iP=E(_iM);if(_iP==1){return E(_iL);}else{return new F(function(){return _iC(_iL*_iL,quot(_iP-1|0,2),_iL);});}}}},_iQ=function(_iR){var _iS=E(_iR);return new F(function(){return Math.log(_iS+(_iS+1)*Math.sqrt((_iS-1)/(_iS+1)));});},_iT=function(_iU){var _iV=E(_iU);return new F(function(){return Math.log(_iV+Math.sqrt(1+_iV*_iV));});},_iW=function(_iX){var _iY=E(_iX);return 0.5*Math.log((1+_iY)/(1-_iY));},_iZ=function(_j0,_j1){return Math.log(E(_j1))/Math.log(E(_j0));},_j2=3.141592653589793,_j3=function(_j4){var _j5=E(_j4);return new F(function(){return _7x(_j5.a,_j5.b);});},_j6=function(_j7){return 1/E(_j7);},_j8=function(_j9){var _ja=E(_j9),_jb=E(_ja);return (_jb==0)?E(_7w):(_jb<=0)? -_jb:E(_ja);},_jc=function(_jd){var _je=E(_jd);if(!_je._){return _je.a;}else{return new F(function(){return I_toNumber(_je.a);});}},_jf=function(_jg){return new F(function(){return _jc(_jg);});},_jh=1,_ji=-1,_jj=function(_jk){var _jl=E(_jk);return (_jl<=0)?(_jl>=0)?E(_jl):E(_ji):E(_jh);},_jm=function(_jn,_jo){return E(_jn)-E(_jo);},_jp=function(_jq){return  -E(_jq);},_jr=function(_js,_jt){return E(_js)+E(_jt);},_ju=function(_jv,_jw){return E(_jv)*E(_jw);},_jx={_:0,a:_jr,b:_jm,c:_ju,d:_jp,e:_j8,f:_jj,g:_jf},_jy=function(_jz,_jA){return E(_jz)/E(_jA);},_jB=new T4(0,_jx,_jy,_j6,_j3),_jC=function(_jD){return new F(function(){return Math.acos(E(_jD));});},_jE=function(_jF){return new F(function(){return Math.asin(E(_jF));});},_jG=function(_jH){return new F(function(){return Math.atan(E(_jH));});},_jI=function(_jJ){return new F(function(){return Math.cos(E(_jJ));});},_jK=function(_jL){return new F(function(){return cosh(E(_jL));});},_jM=function(_jN){return new F(function(){return Math.exp(E(_jN));});},_jO=function(_jP){return new F(function(){return Math.log(E(_jP));});},_jQ=function(_jR,_jS){return new F(function(){return Math.pow(E(_jR),E(_jS));});},_jT=function(_jU){return new F(function(){return Math.sin(E(_jU));});},_jV=function(_jW){return new F(function(){return sinh(E(_jW));});},_jX=function(_jY){return new F(function(){return Math.sqrt(E(_jY));});},_jZ=function(_k0){return new F(function(){return Math.tan(E(_k0));});},_k1=function(_k2){return new F(function(){return tanh(E(_k2));});},_k3={_:0,a:_jB,b:_j2,c:_jM,d:_jO,e:_jX,f:_jQ,g:_iZ,h:_jT,i:_jI,j:_jZ,k:_jE,l:_jC,m:_jG,n:_jV,o:_jK,p:_k1,q:_iT,r:_iQ,s:_iW},_k4=function(_k5,_k6){return (E(_k5)!=E(_k6))?true:false;},_k7=function(_k8,_k9){return E(_k8)==E(_k9);},_ka=new T2(0,_k7,_k4),_kb=function(_kc,_kd){return E(_kc)<E(_kd);},_ke=function(_kf,_kg){return E(_kf)<=E(_kg);},_kh=function(_ki,_kj){return E(_ki)>E(_kj);},_kk=function(_kl,_km){return E(_kl)>=E(_km);},_kn=function(_ko,_kp){var _kq=E(_ko),_kr=E(_kp);return (_kq>=_kr)?(_kq!=_kr)?2:1:0;},_ks=function(_kt,_ku){var _kv=E(_kt),_kw=E(_ku);return (_kv>_kw)?E(_kv):E(_kw);},_kx=function(_ky,_kz){var _kA=E(_ky),_kB=E(_kz);return (_kA>_kB)?E(_kB):E(_kA);},_kC={_:0,a:_ka,b:_kn,c:_kb,d:_ke,e:_kh,f:_kk,g:_ks,h:_kx},_kD=new T2(0,_k3,_kC),_kE=function(_kF,_kG,_kH,_kI,_kJ,_kK,_kL){var _kM=B(_8w(B(_8u(_kF)))),_kN=new T(function(){return B(A3(_7W,_kM,new T(function(){return B(A3(_8y,_kM,_kG,_kJ));}),new T(function(){return B(A3(_8y,_kM,_kH,_kK));})));});return new F(function(){return A3(_7W,_kM,_kN,new T(function(){return B(A3(_8y,_kM,_kI,_kL));}));});},_kO=function(_kP,_kQ,_kR,_kS){var _kT=B(_8u(_kP)),_kU=new T(function(){return B(A2(_8K,_kP,new T(function(){return B(_kE(_kP,_kQ,_kR,_kS,_kQ,_kR,_kS));})));});return new T3(0,B(A3(_an,_kT,_kQ,_kU)),B(A3(_an,_kT,_kR,_kU)),B(A3(_an,_kT,_kS,_kU)));},_kV=function(_kW,_kX,_kY,_kZ,_l0,_l1,_l2){var _l3=B(_8y(_kW));return new T3(0,B(A1(B(A1(_l3,_kX)),_l0)),B(A1(B(A1(_l3,_kY)),_l1)),B(A1(B(A1(_l3,_kZ)),_l2)));},_l4=function(_l5,_l6,_l7,_l8,_l9,_la,_lb){var _lc=B(_7W(_l5));return new T3(0,B(A1(B(A1(_lc,_l6)),_l9)),B(A1(B(A1(_lc,_l7)),_la)),B(A1(B(A1(_lc,_l8)),_lb)));},_ld=function(_le,_lf){var _lg=new T(function(){return E(E(_le).a);}),_lh=new T(function(){return B(A2(_i4,new T2(0,_lg,new T(function(){return E(E(_le).b);})),_lf));}),_li=new T(function(){var _lj=E(_lh),_lk=B(_kO(_lg,_lj.a,_lj.b,_lj.c));return new T3(0,E(_lk.a),E(_lk.b),E(_lk.c));}),_ll=new T(function(){var _lm=E(_lf),_ln=_lm.a,_lo=_lm.b,_lp=_lm.c,_lq=E(_li),_lr=B(_8u(_lg)),_ls=new T(function(){return B(A2(_8K,_lg,new T(function(){var _lt=E(_lh),_lu=_lt.a,_lv=_lt.b,_lw=_lt.c;return B(_kE(_lg,_lu,_lv,_lw,_lu,_lv,_lw));})));}),_lx=B(A3(_an,_lr,new T(function(){return B(_8M(_lg,_ln,_lo,_lp));}),_ls)),_ly=B(_8w(_lr)),_lz=B(_kV(_ly,_lq.a,_lq.b,_lq.c,_lx,_lx,_lx)),_lA=B(_7Y(_ly)),_lB=B(_l4(_ly,_ln,_lo,_lp,B(A1(_lA,_lz.a)),B(A1(_lA,_lz.b)),B(A1(_lA,_lz.c))));return new T3(0,E(_lB.a),E(_lB.b),E(_lB.c));});return new T2(0,_ll,_li);},_lC=function(_lD){return E(E(_lD).a);},_lE=function(_lF,_lG,_lH,_lI,_lJ,_lK,_lL){var _lM=B(_kE(_lF,_lJ,_lK,_lL,_lG,_lH,_lI)),_lN=B(_8w(B(_8u(_lF)))),_lO=B(_kV(_lN,_lJ,_lK,_lL,_lM,_lM,_lM)),_lP=B(_7Y(_lN));return new F(function(){return _l4(_lN,_lG,_lH,_lI,B(A1(_lP,_lO.a)),B(A1(_lP,_lO.b)),B(A1(_lP,_lO.c)));});},_lQ=function(_lR){return E(E(_lR).a);},_lS=function(_lT,_lU,_lV,_lW){var _lX=new T(function(){var _lY=E(_lW),_lZ=E(_lV),_m0=B(_lE(_lT,_lY.a,_lY.b,_lY.c,_lZ.a,_lZ.b,_lZ.c));return new T3(0,E(_m0.a),E(_m0.b),E(_m0.c));}),_m1=new T(function(){return B(A2(_8K,_lT,new T(function(){var _m2=E(_lX),_m3=_m2.a,_m4=_m2.b,_m5=_m2.c;return B(_kE(_lT,_m3,_m4,_m5,_m3,_m4,_m5));})));});if(!B(A3(_lQ,B(_lC(_lU)),_m1,new T(function(){return B(A2(_ad,B(_8w(B(_8u(_lT)))),_ac));})))){var _m6=E(_lX),_m7=B(_kO(_lT,_m6.a,_m6.b,_m6.c)),_m8=B(A2(_8K,_lT,new T(function(){var _m9=E(_lW),_ma=_m9.a,_mb=_m9.b,_mc=_m9.c;return B(_kE(_lT,_ma,_mb,_mc,_ma,_mb,_mc));}))),_md=B(_8y(new T(function(){return B(_8w(new T(function(){return B(_8u(_lT));})));})));return new T3(0,B(A1(B(A1(_md,_m7.a)),_m8)),B(A1(B(A1(_md,_m7.b)),_m8)),B(A1(B(A1(_md,_m7.c)),_m8)));}else{var _me=B(A2(_ad,B(_8w(B(_8u(_lT)))),_ac));return new T3(0,_me,_me,_me);}},_mf=function(_mg,_mh){var _mi=E(_mh);return (_mi._==0)?__Z:new T2(1,E(B(A1(_mg,_mi.a))),E(B(_mf(_mg,_mi.b))));},_mj=function(_mk){var _ml=E(_mk);return (_ml._==0)?__Z:new T2(1,E(_ml.a),E(B(_mj(_ml.b))));},_mm=function(_mn,_mo){return new T2(1,E(_mn),E(_mo));},_mp=__Z,_mq=function(_mr,_ms,_mt){var _mu=E(_mt);if(!_mu._){return new F(function(){return A2(_e9,_mr,_mp);});}else{var _mv=new T(function(){return B(A3(_ar,B(_aj(_mr)),_mm,new T(function(){return B(A1(_ms,_mu.a));})));});return new F(function(){return A3(_ap,_mr,_mv,new T(function(){return B(_mq(_mr,_ms,_mu.b));}));});}},_mw=function(_mx,_my,_mz){return new T2(0,_mx,new T(function(){return E(B(A1(_my,_mz)).b);}));},_mA=function(_mB,_mC,_mD){var _mE=new T(function(){return B(A1(_mC,_mD));}),_mF=new T(function(){return B(A1(_mB,new T(function(){return E(E(_mE).a);})));});return new T2(0,_mF,new T(function(){return E(E(_mE).b);}));},_mG=new T2(0,_mA,_mw),_mH=function(_mI,_mJ,_mK){var _mL=new T(function(){return B(A1(_mI,_mK));}),_mM=new T(function(){return B(A1(_mJ,new T(function(){return E(E(_mL).b);})));}),_mN=new T(function(){return B(A1(E(_mL).a,new T(function(){return E(E(_mM).a);})));});return new T2(0,_mN,new T(function(){return E(E(_mM).b);}));},_mO=function(_mP,_mQ,_mR){var _mS=new T(function(){return B(A1(_mQ,new T(function(){return E(B(A1(_mP,_mR)).b);})));});return new T2(0,new T(function(){return E(E(_mS).a);}),new T(function(){return E(E(_mS).b);}));},_mT=function(_mU,_mV,_mW){var _mX=new T(function(){return B(A1(_mU,_mW));}),_mY=new T(function(){return E(B(A1(_mV,new T(function(){return E(E(_mX).b);}))).b);});return new T2(0,new T(function(){return E(E(_mX).a);}),_mY);},_mZ=function(_n0,_n1){return new T2(0,_n0,_n1);},_n2=new T5(0,_mG,_mZ,_mH,_mO,_mT),_n3=function(_n4,_n5){var _n6=E(_n4);return (_n6._==0)?E(_n5):new T2(1,E(_n6.a),E(B(_n3(_n6.b,_n5))));},_n7=new T(function(){var _n8=eval("angleCount"),_n9=Number(_n8);return jsTrunc(_n9);}),_na=new T(function(){return E(_n7);}),_nb=function(_nc){var _nd=E(_nc);if(!_nd._){return __Z;}else{return new F(function(){return _n3(_nd.a,B(_nb(_nd.b)));});}},_ne=new T(function(){return B(unCStr("head : empty list"));}),_nf=new T(function(){return B(err(_ne));}),_ng=function(_nh){var _ni=E(_nh);return (_ni._==0)?E(_nf):E(_ni.a);},_nj=new T(function(){return B(unCStr("last : empty list"));}),_nk=new T(function(){return B(err(_nj));}),_nl=function(_nm,_nn){while(1){var _no=E(_nn);if(!_no._){return E(_nm);}else{_nm=_no.a;_nn=_no.b;continue;}}},_np=function(_nq){var _nr=E(E(_nq).b);if(!_nr._){return E(_nk);}else{var _ns=E(_nr.b);if(!_ns._){return E(_nr.a);}else{return new F(function(){return _nl(_ns.a,_ns.b);});}}},_nt=function(_nu,_nv,_nw){return new T3(0,E(_nu),E(_nv),E(_nw));},_nx=function(_ny,_nz,_nA,_nB){return new F(function(){return _mj(new T2(1,new T(function(){return B(_nt(_ny,_nz,_nA));}),new T2(1,new T(function(){return B(_nt(_nz,_nA,_nB));}),_T)));});},_nC=function(_nD,_nE){var _nF=E(_nD),_nG=E(_nE);return new F(function(){return _nx(_nF.a,_nF.b,_nG.a,_nG.b);});},_nH=new T(function(){return B(_mj(_T));}),_nI=function(_nJ,_nK){var _nL=E(_nJ);if(!_nL._){return E(_nH);}else{var _nM=E(_nK);return (_nM._==0)?E(_nH):new T2(1,E(new T2(0,_nL.a,_nM.a)),E(B(_nI(_nL.b,_nM.b))));}},_nN=new T(function(){return B(_mj(_T));}),_nO=function(_nP,_nQ,_nR){var _nS=E(_nQ);if(!_nS._){return E(_nN);}else{var _nT=E(_nR);return (_nT._==0)?E(_nN):new T2(1,E(B(A2(_nP,_nS.a,_nT.a))),E(B(_nO(_nP,_nS.b,_nT.b))));}},_nU=function(_nV,_nW,_nX,_nY,_nZ){var _o0=E(_nY);if(!_o0._){return E(_nf);}else{var _o1=E(_nZ);return (_o1._==0)?E(_nf):new T2(0,new T3(0,E(new T3(0,E(_nV),E(_nW),E(_nX))),E(_o0.a),E(_o1.a)),B(_nb(B(_nO(_nC,B(_nI(_o0,_o0.b)),new T(function(){return B(_nI(_o1,_o1.b));},1))))));}},_o2=function(_o3,_o4){var _o5=E(_o3),_o6=E(_o5.a),_o7=B(_nU(_o6.a,_o6.b,_o6.c,_o5.b,E(_o4).b));return new T2(1,E(_o7.a),E(_o7.b));},_o8=new T(function(){return E(_na)-1;}),_o9=new T1(0,1),_oa=function(_ob,_oc){var _od=E(_oc),_oe=new T(function(){var _of=B(_8w(_ob)),_og=B(_oa(_ob,B(A3(_7W,_of,_od,new T(function(){return B(A2(_ad,_of,_o9));})))));return new T2(1,_og.a,_og.b);});return new T2(0,_od,_oe);},_oh=function(_oi){return E(E(_oi).d);},_oj=new T1(0,2),_ok=function(_ol,_om){var _on=E(_om);if(!_on._){return __Z;}else{var _oo=_on.a;return (!B(A1(_ol,_oo)))?__Z:new T2(1,_oo,new T(function(){return B(_ok(_ol,_on.b));}));}},_op=function(_oq,_or,_os,_ot){var _ou=B(_oa(_or,_os)),_ov=new T(function(){var _ow=B(_8w(_or)),_ox=new T(function(){return B(A3(_an,_or,new T(function(){return B(A2(_ad,_ow,_o9));}),new T(function(){return B(A2(_ad,_ow,_oj));})));});return B(A3(_7W,_ow,_ot,_ox));});return new F(function(){return _ok(function(_oy){return new F(function(){return A3(_oh,_oq,_oy,_ov);});},new T2(1,_ou.a,_ou.b));});},_oz=new T(function(){return B(_op(_kC,_jB,_iy,_o8));}),_oA=new T(function(){return B(_mj(_oz));}),_oB=new T(function(){var _oC=eval("proceedCount"),_oD=Number(_oC);return jsTrunc(_oD);}),_oE=new T(function(){return E(_oB);}),_oF=new T(function(){return B(unCStr("tail : empty list"));}),_oG=new T(function(){return B(err(_oF));}),_oH=1,_oI=new T(function(){return B(_op(_kC,_jB,_oH,_oE));}),_oJ=new T(function(){return B(_mj(_oI));}),_oK=function(_oL,_oM,_oN,_oO,_oP,_oQ,_oR,_oS,_oT,_oU,_oV,_oW,_oX,_oY){var _oZ=new T(function(){var _p0=new T(function(){var _p1=E(_oS),_p2=E(_oW),_p3=E(_oV),_p4=E(_oT),_p5=E(_oU),_p6=E(_oR);return new T3(0,_p1*_p2-_p3*_p4,_p4*_p5-_p2*_p6,_p6*_p3-_p5*_p1);}),_p7=function(_p8){var _p9=new T(function(){var _pa=E(_p8)/E(_na);return (_pa+_pa)*3.141592653589793;}),_pb=new T(function(){return B(A1(_oL,_p9));}),_pc=new T(function(){var _pd=new T(function(){var _pe=E(_pb)/E(_oE);return new T3(0,E(_pe),E(_pe),E(_pe));}),_pf=function(_pg){var _ph=new T(function(){var _pi=E(_pb);return new T2(0,E(_pg)/E(_oE),E(_pi));}),_pj=function(_pk){var _pl=B(_ld(_kD,new T(function(){var _pm=E(_pk),_pn=E(_pm.a),_po=E(_pm.b),_pp=E(_pd);return new T3(0,E(_pn.a)+E(_po.a)*E(_pp.a),E(_pn.b)+E(_po.b)*E(_pp.b),E(_pn.c)+E(_po.c)*E(_pp.c));}))),_pq=_pl.a;return new T2(0,new T(function(){var _pr=E(_p9);return new T3(0,E(_pq),E(_ph),E(_pr));}),new T2(0,_pq,new T(function(){var _ps=E(_pl.b),_pt=E(E(_pk).b),_pu=B(_lE(_k3,_pt.a,_pt.b,_pt.c,_ps.a,_ps.b,_ps.c)),_pv=B(_kO(_k3,_pu.a,_pu.b,_pu.c));return new T3(0,E(_pv.a),E(_pv.b),E(_pv.c));})));};return E(_pj);};return E(B(A(_mq,[_n2,_pf,_oJ,new T2(0,_oO,new T(function(){var _pw=E(_p0),_px=E(_p9)+_oP,_py=Math.cos(_px),_pz=Math.sin(_px);return new T3(0,E(_oR)*_py+E(_pw.a)*_pz,E(_oS)*_py+E(_pw.b)*_pz,E(_oT)*_py+E(_pw.c)*_pz);}))])).a);});return new T2(0,new T(function(){var _pA=E(_pb),_pB=E(_p9);return new T3(0,E(_oO),E(new T2(0,E(_iy),E(_pA))),E(_pB));}),_pc);};return B(_mf(_p7,_oA));}),_pC=new T(function(){var _pD=new T(function(){var _pE=B(_n3(_oZ,B(_mj(new T2(1,new T(function(){return B(_ng(_oZ));}),_T)))));if(!_pE._){return E(_oG);}else{return E(_pE.b);}},1);return B(_nb(B(_nO(_o2,_oZ,_pD))));});return new T2(0,_pC,new T(function(){return B(_mf(_np,_oZ));}));},_pF=function(_pG,_pH,_pI,_pJ,_pK,_pL,_pM,_pN,_pO,_pP,_pQ,_pR,_pS,_pT,_pU,_pV,_pW){var _pX=B(_ld(_kD,new T3(0,E(_pJ),E(_pK),E(_pL)))),_pY=_pX.b,_pZ=E(_pX.a),_q0=B(_lS(_k3,_kC,_pY,new T3(0,E(_pN),E(_pO),E(_pP)))),_q1=E(_pY),_q2=_q1.a,_q3=_q1.b,_q4=_q1.c,_q5=B(_lE(_k3,_pR,_pS,_pT,_q2,_q3,_q4)),_q6=B(_kO(_k3,_q5.a,_q5.b,_q5.c)),_q7=_q6.a,_q8=_q6.b,_q9=_q6.c,_qa=E(_pM),_qb=new T2(0,E(new T3(0,E(_q0.a),E(_q0.b),E(_q0.c))),E(_pQ)),_qc=B(_oK(_pG,_pH,_pI,_pZ,_qa,_qb,_q7,_q8,_q9,_q2,_q3,_q4,_pV,_pW));return {_:0,a:_pG,b:_pH,c:_pI,d:new T2(0,E(_pZ),E(_qa)),e:_qb,f:new T3(0,E(_q7),E(_q8),E(_q9)),g:_q1,h:E(_qc.a),i:E(_qc.b)};},_qd=new T(function(){return B(_mj(_T));}),_qe=new T(function(){return B(_mj(_T));}),_qf=new T(function(){return 6.283185307179586/E(_na);}),_qg=-1,_qh=0.5,_qi=new T3(0,E(_iy),E(_qh),E(_qg)),_qj=function(_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw){var _qx=function(_qy){var _qz=E(_qf),_qA=2+_qy|0,_qB=_qA-1|0,_qC=(2+_qy)*(1+_qy),_qD=E(_oz);if(!_qD._){return _qz*0;}else{var _qE=_qD.a,_qF=_qD.b,_qG=B(A1(_qk,new T(function(){return 6.283185307179586*E(_qE)/E(_na);}))),_qH=B(A1(_qk,new T(function(){return 6.283185307179586*(E(_qE)+1)/E(_na);})));if(_qG!=_qH){if(_qA>=0){var _qI=E(_qA);if(!_qI){var _qJ=function(_qK,_qL){while(1){var _qM=B((function(_qN,_qO){var _qP=E(_qN);if(!_qP._){return E(_qO);}else{var _qQ=_qP.a,_qR=_qP.b,_qS=B(A1(_qk,new T(function(){return 6.283185307179586*E(_qQ)/E(_na);}))),_qT=B(A1(_qk,new T(function(){return 6.283185307179586*(E(_qQ)+1)/E(_na);})));if(_qS!=_qT){var _qU=_qO+0/(_qS-_qT)/_qC;_qK=_qR;_qL=_qU;return __continue;}else{if(_qB>=0){var _qV=E(_qB);if(!_qV){var _qU=_qO+_qA/_qC;_qK=_qR;_qL=_qU;return __continue;}else{var _qU=_qO+_qA*B(_iK(_qS,_qV))/_qC;_qK=_qR;_qL=_qU;return __continue;}}else{return E(_iB);}}}})(_qK,_qL));if(_qM!=__continue){return _qM;}}};return _qz*B(_qJ(_qF,0/(_qG-_qH)/_qC));}else{var _qW=function(_qX,_qY){while(1){var _qZ=B((function(_r0,_r1){var _r2=E(_r0);if(!_r2._){return E(_r1);}else{var _r3=_r2.a,_r4=_r2.b,_r5=B(A1(_qk,new T(function(){return 6.283185307179586*E(_r3)/E(_na);}))),_r6=B(A1(_qk,new T(function(){return 6.283185307179586*(E(_r3)+1)/E(_na);})));if(_r5!=_r6){if(_qI>=0){var _r7=_r1+(B(_iK(_r5,_qI))-B(_iK(_r6,_qI)))/(_r5-_r6)/_qC;_qX=_r4;_qY=_r7;return __continue;}else{return E(_iB);}}else{if(_qB>=0){var _r8=E(_qB);if(!_r8){var _r7=_r1+_qA/_qC;_qX=_r4;_qY=_r7;return __continue;}else{var _r7=_r1+_qA*B(_iK(_r5,_r8))/_qC;_qX=_r4;_qY=_r7;return __continue;}}else{return E(_iB);}}}})(_qX,_qY));if(_qZ!=__continue){return _qZ;}}};return _qz*B(_qW(_qF,(B(_iK(_qG,_qI))-B(_iK(_qH,_qI)))/(_qG-_qH)/_qC));}}else{return E(_iB);}}else{if(_qB>=0){var _r9=E(_qB);if(!_r9){var _ra=function(_rb,_rc){while(1){var _rd=B((function(_re,_rf){var _rg=E(_re);if(!_rg._){return E(_rf);}else{var _rh=_rg.a,_ri=_rg.b,_rj=B(A1(_qk,new T(function(){return 6.283185307179586*E(_rh)/E(_na);}))),_rk=B(A1(_qk,new T(function(){return 6.283185307179586*(E(_rh)+1)/E(_na);})));if(_rj!=_rk){if(_qA>=0){var _rl=E(_qA);if(!_rl){var _rm=_rf+0/(_rj-_rk)/_qC;_rb=_ri;_rc=_rm;return __continue;}else{var _rm=_rf+(B(_iK(_rj,_rl))-B(_iK(_rk,_rl)))/(_rj-_rk)/_qC;_rb=_ri;_rc=_rm;return __continue;}}else{return E(_iB);}}else{var _rm=_rf+_qA/_qC;_rb=_ri;_rc=_rm;return __continue;}}})(_rb,_rc));if(_rd!=__continue){return _rd;}}};return _qz*B(_ra(_qF,_qA/_qC));}else{var _rn=function(_ro,_rp){while(1){var _rq=B((function(_rr,_rs){var _rt=E(_rr);if(!_rt._){return E(_rs);}else{var _ru=_rt.a,_rv=_rt.b,_rw=B(A1(_qk,new T(function(){return 6.283185307179586*E(_ru)/E(_na);}))),_rx=B(A1(_qk,new T(function(){return 6.283185307179586*(E(_ru)+1)/E(_na);})));if(_rw!=_rx){if(_qA>=0){var _ry=E(_qA);if(!_ry){var _rz=_rs+0/(_rw-_rx)/_qC;_ro=_rv;_rp=_rz;return __continue;}else{var _rz=_rs+(B(_iK(_rw,_ry))-B(_iK(_rx,_ry)))/(_rw-_rx)/_qC;_ro=_rv;_rp=_rz;return __continue;}}else{return E(_iB);}}else{if(_r9>=0){var _rz=_rs+_qA*B(_iK(_rw,_r9))/_qC;_ro=_rv;_rp=_rz;return __continue;}else{return E(_iB);}}}})(_ro,_rp));if(_rq!=__continue){return _rq;}}};return _qz*B(_rn(_qF,_qA*B(_iK(_qG,_r9))/_qC));}}else{return E(_iB);}}}},_rA=1/(B(_qx(1))*_ql);return new F(function(){return _pF(_qk,_qi,new T2(0,E(new T3(0,E(_rA),E(_rA),E(_rA))),1/(B(_qx(3))*_ql)),_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_iz,_qe,_qd);});},_rB=0,_rC=-0.2,_rD=0.5,_rE=-0.8,_rF=0.2,_rG=function(_rH){return E(_rF);},_rI=1,_rJ=new T(function(){var _rK=B(_qj(_rG,1.2,_rE,_rD,_rB,_rB,_rC,_rB,_rI,_rB,_rB,_rB,_rI));return {_:0,a:E(_rK.a),b:E(_rK.b),c:E(_rK.c),d:E(_rK.d),e:E(_rK.e),f:E(_rK.f),g:E(_rK.g),h:E(_rK.h),i:E(_rK.i)};}),_rL=0,_rM=-0.1,_rN=1.3,_rO=function(_rP){var _rQ=I_decodeDouble(_rP);return new T2(0,new T1(1,_rQ.b),_rQ.a);},_rR=function(_rS){return new T1(0,_rS);},_rT=function(_rU){var _rV=hs_intToInt64(2147483647),_rW=hs_leInt64(_rU,_rV);if(!_rW){return new T1(1,I_fromInt64(_rU));}else{var _rX=hs_intToInt64(-2147483648),_rY=hs_geInt64(_rU,_rX);if(!_rY){return new T1(1,I_fromInt64(_rU));}else{var _rZ=hs_int64ToInt(_rU);return new F(function(){return _rR(_rZ);});}}},_s0=new T(function(){var _s1=newByteArr(256),_s2=_s1,_=_s2["v"]["i8"][0]=8,_s3=function(_s4,_s5,_s6,_){while(1){if(_s6>=256){if(_s4>=256){return E(_);}else{var _s7=imul(2,_s4)|0,_s8=_s5+1|0,_s9=_s4;_s4=_s7;_s5=_s8;_s6=_s9;continue;}}else{var _=_s2["v"]["i8"][_s6]=_s5,_s9=_s6+_s4|0;_s6=_s9;continue;}}},_=B(_s3(2,0,1,_));return _s2;}),_sa=function(_sb,_sc){var _sd=hs_int64ToInt(_sb),_se=E(_s0),_sf=_se["v"]["i8"][(255&_sd>>>0)>>>0&4294967295];if(_sc>_sf){if(_sf>=8){var _sg=hs_uncheckedIShiftRA64(_sb,8),_sh=function(_si,_sj){while(1){var _sk=B((function(_sl,_sm){var _sn=hs_int64ToInt(_sl),_so=_se["v"]["i8"][(255&_sn>>>0)>>>0&4294967295];if(_sm>_so){if(_so>=8){var _sp=hs_uncheckedIShiftRA64(_sl,8),_sq=_sm-8|0;_si=_sp;_sj=_sq;return __continue;}else{return new T2(0,new T(function(){var _sr=hs_uncheckedIShiftRA64(_sl,_so);return B(_rT(_sr));}),_sm-_so|0);}}else{return new T2(0,new T(function(){var _ss=hs_uncheckedIShiftRA64(_sl,_sm);return B(_rT(_ss));}),0);}})(_si,_sj));if(_sk!=__continue){return _sk;}}};return new F(function(){return _sh(_sg,_sc-8|0);});}else{return new T2(0,new T(function(){var _st=hs_uncheckedIShiftRA64(_sb,_sf);return B(_rT(_st));}),_sc-_sf|0);}}else{return new T2(0,new T(function(){var _su=hs_uncheckedIShiftRA64(_sb,_sc);return B(_rT(_su));}),0);}},_sv=function(_sw){var _sx=hs_intToInt64(_sw);return E(_sx);},_sy=function(_sz){var _sA=E(_sz);if(!_sA._){return new F(function(){return _sv(_sA.a);});}else{return new F(function(){return I_toInt64(_sA.a);});}},_sB=function(_sC){return I_toInt(_sC)>>>0;},_sD=function(_sE){var _sF=E(_sE);if(!_sF._){return _sF.a>>>0;}else{return new F(function(){return _sB(_sF.a);});}},_sG=function(_sH){var _sI=B(_rO(_sH)),_sJ=_sI.a,_sK=_sI.b;if(_sK<0){var _sL=function(_sM){if(!_sM){return new T2(0,E(_sJ),B(_4I(_30, -_sK)));}else{var _sN=B(_sa(B(_sy(_sJ)), -_sK));return new T2(0,E(_sN.a),B(_4I(_30,_sN.b)));}};if(!((B(_sD(_sJ))&1)>>>0)){return new F(function(){return _sL(1);});}else{return new F(function(){return _sL(0);});}}else{return new T2(0,B(_4I(_sJ,_sK)),_30);}},_sO=function(_sP){var _sQ=B(_sG(E(_sP)));return new T2(0,E(_sQ.a),E(_sQ.b));},_sR=new T3(0,_jx,_kC,_sO),_sS=function(_sT){return E(E(_sT).a);},_sU=function(_sV){return E(E(_sV).a);},_sW=function(_sX,_sY){if(_sX<=_sY){var _sZ=function(_t0){return new T2(1,_t0,new T(function(){if(_t0!=_sY){return B(_sZ(_t0+1|0));}else{return __Z;}}));};return new F(function(){return _sZ(_sX);});}else{return __Z;}},_t1=function(_t2){return new F(function(){return _sW(E(_t2),2147483647);});},_t3=function(_t4,_t5,_t6){if(_t6<=_t5){var _t7=new T(function(){var _t8=_t5-_t4|0,_t9=function(_ta){return (_ta>=(_t6-_t8|0))?new T2(1,_ta,new T(function(){return B(_t9(_ta+_t8|0));})):new T2(1,_ta,_T);};return B(_t9(_t5));});return new T2(1,_t4,_t7);}else{return (_t6<=_t4)?new T2(1,_t4,_T):__Z;}},_tb=function(_tc,_td,_te){if(_te>=_td){var _tf=new T(function(){var _tg=_td-_tc|0,_th=function(_ti){return (_ti<=(_te-_tg|0))?new T2(1,_ti,new T(function(){return B(_th(_ti+_tg|0));})):new T2(1,_ti,_T);};return B(_th(_td));});return new T2(1,_tc,_tf);}else{return (_te>=_tc)?new T2(1,_tc,_T):__Z;}},_tj=function(_tk,_tl){if(_tl<_tk){return new F(function(){return _t3(_tk,_tl,-2147483648);});}else{return new F(function(){return _tb(_tk,_tl,2147483647);});}},_tm=function(_tn,_to){return new F(function(){return _tj(E(_tn),E(_to));});},_tp=function(_tq,_tr,_ts){if(_tr<_tq){return new F(function(){return _t3(_tq,_tr,_ts);});}else{return new F(function(){return _tb(_tq,_tr,_ts);});}},_tt=function(_tu,_tv,_tw){return new F(function(){return _tp(E(_tu),E(_tv),E(_tw));});},_tx=function(_ty,_tz){return new F(function(){return _sW(E(_ty),E(_tz));});},_tA=function(_tB){return E(_tB);},_tC=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tD=new T(function(){return B(err(_tC));}),_tE=function(_tF){var _tG=E(_tF);return (_tG==(-2147483648))?E(_tD):_tG-1|0;},_tH=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tI=new T(function(){return B(err(_tH));}),_tJ=function(_tK){var _tL=E(_tK);return (_tL==2147483647)?E(_tI):_tL+1|0;},_tM={_:0,a:_tJ,b:_tE,c:_tA,d:_tA,e:_t1,f:_tm,g:_tx,h:_tt},_tN=function(_tO,_tP){if(_tO<=0){if(_tO>=0){return new F(function(){return quot(_tO,_tP);});}else{if(_tP<=0){return new F(function(){return quot(_tO,_tP);});}else{return quot(_tO+1|0,_tP)-1|0;}}}else{if(_tP>=0){if(_tO>=0){return new F(function(){return quot(_tO,_tP);});}else{if(_tP<=0){return new F(function(){return quot(_tO,_tP);});}else{return quot(_tO+1|0,_tP)-1|0;}}}else{return quot(_tO-1|0,_tP)-1|0;}}},_tQ=0,_tR=new T(function(){return B(_45(_tQ));}),_tS=new T(function(){return die(_tR);}),_tT=function(_tU,_tV){var _tW=E(_tV);switch(_tW){case -1:var _tX=E(_tU);if(_tX==(-2147483648)){return E(_tS);}else{return new F(function(){return _tN(_tX,-1);});}break;case 0:return E(_49);default:return new F(function(){return _tN(_tU,_tW);});}},_tY=function(_tZ,_u0){return new F(function(){return _tT(E(_tZ),E(_u0));});},_u1=0,_u2=new T2(0,_tS,_u1),_u3=function(_u4,_u5){var _u6=E(_u4),_u7=E(_u5);switch(_u7){case -1:var _u8=E(_u6);if(_u8==(-2147483648)){return E(_u2);}else{if(_u8<=0){if(_u8>=0){var _u9=quotRemI(_u8,-1);return new T2(0,_u9.a,_u9.b);}else{var _ua=quotRemI(_u8,-1);return new T2(0,_ua.a,_ua.b);}}else{var _ub=quotRemI(_u8-1|0,-1);return new T2(0,_ub.a-1|0,(_ub.b+(-1)|0)+1|0);}}break;case 0:return E(_49);default:if(_u6<=0){if(_u6>=0){var _uc=quotRemI(_u6,_u7);return new T2(0,_uc.a,_uc.b);}else{if(_u7<=0){var _ud=quotRemI(_u6,_u7);return new T2(0,_ud.a,_ud.b);}else{var _ue=quotRemI(_u6+1|0,_u7);return new T2(0,_ue.a-1|0,(_ue.b+_u7|0)-1|0);}}}else{if(_u7>=0){if(_u6>=0){var _uf=quotRemI(_u6,_u7);return new T2(0,_uf.a,_uf.b);}else{if(_u7<=0){var _ug=quotRemI(_u6,_u7);return new T2(0,_ug.a,_ug.b);}else{var _uh=quotRemI(_u6+1|0,_u7);return new T2(0,_uh.a-1|0,(_uh.b+_u7|0)-1|0);}}}else{var _ui=quotRemI(_u6-1|0,_u7);return new T2(0,_ui.a-1|0,(_ui.b+_u7|0)+1|0);}}}},_uj=function(_uk,_ul){var _um=_uk%_ul;if(_uk<=0){if(_uk>=0){return E(_um);}else{if(_ul<=0){return E(_um);}else{var _un=E(_um);return (_un==0)?0:_un+_ul|0;}}}else{if(_ul>=0){if(_uk>=0){return E(_um);}else{if(_ul<=0){return E(_um);}else{var _uo=E(_um);return (_uo==0)?0:_uo+_ul|0;}}}else{var _up=E(_um);return (_up==0)?0:_up+_ul|0;}}},_uq=function(_ur,_us){var _ut=E(_us);switch(_ut){case -1:return E(_u1);case 0:return E(_49);default:return new F(function(){return _uj(E(_ur),_ut);});}},_uu=function(_uv,_uw){var _ux=E(_uv),_uy=E(_uw);switch(_uy){case -1:var _uz=E(_ux);if(_uz==(-2147483648)){return E(_tS);}else{return new F(function(){return quot(_uz,-1);});}break;case 0:return E(_49);default:return new F(function(){return quot(_ux,_uy);});}},_uA=function(_uB,_uC){var _uD=E(_uB),_uE=E(_uC);switch(_uE){case -1:var _uF=E(_uD);if(_uF==(-2147483648)){return E(_u2);}else{var _uG=quotRemI(_uF,-1);return new T2(0,_uG.a,_uG.b);}break;case 0:return E(_49);default:var _uH=quotRemI(_uD,_uE);return new T2(0,_uH.a,_uH.b);}},_uI=function(_uJ,_uK){var _uL=E(_uK);switch(_uL){case -1:return E(_u1);case 0:return E(_49);default:return E(_uJ)%_uL;}},_uM=function(_uN){return new F(function(){return _rR(E(_uN));});},_uO=function(_uP){return new T2(0,E(B(_rR(E(_uP)))),E(_o9));},_uQ=function(_uR,_uS){return imul(E(_uR),E(_uS))|0;},_uT=function(_uU,_uV){return E(_uU)+E(_uV)|0;},_uW=function(_uX,_uY){return E(_uX)-E(_uY)|0;},_uZ=function(_v0){var _v1=E(_v0);return (_v1<0)? -_v1:E(_v1);},_v2=function(_v3){return new F(function(){return _4m(_v3);});},_v4=function(_v5){return  -E(_v5);},_v6=-1,_v7=0,_v8=1,_v9=function(_va){var _vb=E(_va);return (_vb>=0)?(E(_vb)==0)?E(_v7):E(_v8):E(_v6);},_vc={_:0,a:_uT,b:_uW,c:_uQ,d:_v4,e:_uZ,f:_v9,g:_v2},_vd=function(_ve,_vf){return E(_ve)==E(_vf);},_vg=function(_vh,_vi){return E(_vh)!=E(_vi);},_vj=new T2(0,_vd,_vg),_vk=function(_vl,_vm){var _vn=E(_vl),_vo=E(_vm);return (_vn>_vo)?E(_vn):E(_vo);},_vp=function(_vq,_vr){var _vs=E(_vq),_vt=E(_vr);return (_vs>_vt)?E(_vt):E(_vs);},_vu=function(_vv,_vw){return (_vv>=_vw)?(_vv!=_vw)?2:1:0;},_vx=function(_vy,_vz){return new F(function(){return _vu(E(_vy),E(_vz));});},_vA=function(_vB,_vC){return E(_vB)>=E(_vC);},_vD=function(_vE,_vF){return E(_vE)>E(_vF);},_vG=function(_vH,_vI){return E(_vH)<=E(_vI);},_vJ=function(_vK,_vL){return E(_vK)<E(_vL);},_vM={_:0,a:_vj,b:_vx,c:_vJ,d:_vG,e:_vD,f:_vA,g:_vk,h:_vp},_vN=new T3(0,_vc,_vM,_uO),_vO={_:0,a:_vN,b:_tM,c:_uu,d:_uI,e:_tY,f:_uq,g:_uA,h:_u3,i:_uM},_vP=new T1(0,2),_vQ=function(_vR,_vS){while(1){var _vT=E(_vR);if(!_vT._){var _vU=_vT.a,_vV=E(_vS);if(!_vV._){var _vW=_vV.a;if(!(imul(_vU,_vW)|0)){return new T1(0,imul(_vU,_vW)|0);}else{_vR=new T1(1,I_fromInt(_vU));_vS=new T1(1,I_fromInt(_vW));continue;}}else{_vR=new T1(1,I_fromInt(_vU));_vS=_vV;continue;}}else{var _vX=E(_vS);if(!_vX._){_vR=_vT;_vS=new T1(1,I_fromInt(_vX.a));continue;}else{return new T1(1,I_mul(_vT.a,_vX.a));}}}},_vY=function(_vZ,_w0,_w1){while(1){if(!(_w0%2)){var _w2=B(_vQ(_vZ,_vZ)),_w3=quot(_w0,2);_vZ=_w2;_w0=_w3;continue;}else{var _w4=E(_w0);if(_w4==1){return new F(function(){return _vQ(_vZ,_w1);});}else{var _w2=B(_vQ(_vZ,_vZ)),_w5=B(_vQ(_vZ,_w1));_vZ=_w2;_w0=quot(_w4-1|0,2);_w1=_w5;continue;}}}},_w6=function(_w7,_w8){while(1){if(!(_w8%2)){var _w9=B(_vQ(_w7,_w7)),_wa=quot(_w8,2);_w7=_w9;_w8=_wa;continue;}else{var _wb=E(_w8);if(_wb==1){return E(_w7);}else{return new F(function(){return _vY(B(_vQ(_w7,_w7)),quot(_wb-1|0,2),_w7);});}}}},_wc=function(_wd){return E(E(_wd).b);},_we=function(_wf){return E(E(_wf).c);},_wg=new T1(0,0),_wh=function(_wi){return E(E(_wi).d);},_wj=function(_wk,_wl){var _wm=B(_sS(_wk)),_wn=new T(function(){return B(_sU(_wm));}),_wo=new T(function(){return B(A3(_wh,_wk,_wl,new T(function(){return B(A2(_ad,_wn,_oj));})));});return new F(function(){return A3(_lQ,B(_lC(B(_wc(_wm)))),_wo,new T(function(){return B(A2(_ad,_wn,_wg));}));});},_wp=new T(function(){return B(unCStr("Negative exponent"));}),_wq=new T(function(){return B(err(_wp));}),_wr=function(_ws){return E(E(_ws).c);},_wt=function(_wu,_wv,_ww,_wx){var _wy=B(_sS(_wv)),_wz=new T(function(){return B(_sU(_wy));}),_wA=B(_wc(_wy));if(!B(A3(_we,_wA,_wx,new T(function(){return B(A2(_ad,_wz,_wg));})))){if(!B(A3(_lQ,B(_lC(_wA)),_wx,new T(function(){return B(A2(_ad,_wz,_wg));})))){var _wB=new T(function(){return B(A2(_ad,_wz,_oj));}),_wC=new T(function(){return B(A2(_ad,_wz,_o9));}),_wD=B(_lC(_wA)),_wE=function(_wF,_wG,_wH){while(1){var _wI=B((function(_wJ,_wK,_wL){if(!B(_wj(_wv,_wK))){if(!B(A3(_lQ,_wD,_wK,_wC))){var _wM=new T(function(){return B(A3(_wr,_wv,new T(function(){return B(A3(_8A,_wz,_wK,_wC));}),_wB));});_wF=new T(function(){return B(A3(_8y,_wu,_wJ,_wJ));});_wG=_wM;_wH=new T(function(){return B(A3(_8y,_wu,_wJ,_wL));});return __continue;}else{return new F(function(){return A3(_8y,_wu,_wJ,_wL);});}}else{var _wN=_wL;_wF=new T(function(){return B(A3(_8y,_wu,_wJ,_wJ));});_wG=new T(function(){return B(A3(_wr,_wv,_wK,_wB));});_wH=_wN;return __continue;}})(_wF,_wG,_wH));if(_wI!=__continue){return _wI;}}},_wO=function(_wP,_wQ){while(1){var _wR=B((function(_wS,_wT){if(!B(_wj(_wv,_wT))){if(!B(A3(_lQ,_wD,_wT,_wC))){var _wU=new T(function(){return B(A3(_wr,_wv,new T(function(){return B(A3(_8A,_wz,_wT,_wC));}),_wB));});return new F(function(){return _wE(new T(function(){return B(A3(_8y,_wu,_wS,_wS));}),_wU,_wS);});}else{return E(_wS);}}else{_wP=new T(function(){return B(A3(_8y,_wu,_wS,_wS));});_wQ=new T(function(){return B(A3(_wr,_wv,_wT,_wB));});return __continue;}})(_wP,_wQ));if(_wR!=__continue){return _wR;}}};return new F(function(){return _wO(_ww,_wx);});}else{return new F(function(){return A2(_ad,_wu,_o9);});}}else{return E(_wq);}},_wV=new T(function(){return B(err(_wp));}),_wW=function(_wX,_wY){var _wZ=B(_rO(_wY)),_x0=_wZ.a,_x1=_wZ.b,_x2=new T(function(){return B(_sU(new T(function(){return B(_sS(_wX));})));});if(_x1<0){var _x3= -_x1;if(_x3>=0){var _x4=E(_x3);if(!_x4){var _x5=E(_o9);}else{var _x5=B(_w6(_vP,_x4));}if(!B(_4e(_x5,_4H))){var _x6=B(_4y(_x0,_x5));return new T2(0,new T(function(){return B(A2(_ad,_x2,_x6.a));}),new T(function(){return B(_4a(_x6.b,_x1));}));}else{return E(_49);}}else{return E(_wV);}}else{var _x7=new T(function(){var _x8=new T(function(){return B(_wt(_x2,_vO,new T(function(){return B(A2(_ad,_x2,_vP));}),_x1));});return B(A3(_8y,_x2,new T(function(){return B(A2(_ad,_x2,_x0));}),_x8));});return new T2(0,_x7,_7w);}},_x9=function(_xa,_xb){var _xc=B(_wW(_xa,E(_xb))),_xd=_xc.a;if(E(_xc.b)<=0){return E(_xd);}else{var _xe=B(_sU(B(_sS(_xa))));return new F(function(){return A3(_7W,_xe,_xd,new T(function(){return B(A2(_ad,_xe,_30));}));});}},_xf=function(_xg,_xh){var _xi=B(_wW(_xg,E(_xh))),_xj=_xi.a;if(E(_xi.b)>=0){return E(_xj);}else{var _xk=B(_sU(B(_sS(_xg))));return new F(function(){return A3(_8A,_xk,_xj,new T(function(){return B(A2(_ad,_xk,_30));}));});}},_xl=function(_xm,_xn){var _xo=B(_wW(_xm,E(_xn)));return new T2(0,_xo.a,_xo.b);},_xp=function(_xq,_xr){var _xs=B(_wW(_xq,_xr)),_xt=_xs.a,_xu=E(_xs.b),_xv=new T(function(){var _xw=B(_sU(B(_sS(_xq))));if(_xu>=0){return B(A3(_7W,_xw,_xt,new T(function(){return B(A2(_ad,_xw,_30));})));}else{return B(A3(_8A,_xw,_xt,new T(function(){return B(A2(_ad,_xw,_30));})));}}),_xx=function(_xy){var _xz=_xy-0.5;return (_xz>=0)?(E(_xz)==0)?(!B(_wj(_xq,_xt)))?E(_xv):E(_xt):E(_xv):E(_xt);},_xA=E(_xu);if(!_xA){return new F(function(){return _xx(0);});}else{if(_xA<=0){var _xB= -_xA-0.5;return (_xB>=0)?(E(_xB)==0)?(!B(_wj(_xq,_xt)))?E(_xv):E(_xt):E(_xv):E(_xt);}else{return new F(function(){return _xx(_xA);});}}},_xC=function(_xD,_xE){return new F(function(){return _xp(_xD,E(_xE));});},_xF=function(_xG,_xH){return E(B(_wW(_xG,E(_xH))).a);},_xI={_:0,a:_sR,b:_jB,c:_xl,d:_xF,e:_xC,f:_x9,g:_xf},_xJ=new T1(0,1),_xK=function(_xL,_xM){var _xN=E(_xL);return new T2(0,_xN,new T(function(){var _xO=B(_xK(B(_4p(_xN,_xM)),_xM));return new T2(1,_xO.a,_xO.b);}));},_xP=function(_xQ){var _xR=B(_xK(_xQ,_xJ));return new T2(1,_xR.a,_xR.b);},_xS=function(_xT,_xU){var _xV=B(_xK(_xT,new T(function(){return B(_6K(_xU,_xT));})));return new T2(1,_xV.a,_xV.b);},_xW=new T1(0,0),_xX=function(_xY,_xZ){var _y0=E(_xY);if(!_y0._){var _y1=_y0.a,_y2=E(_xZ);return (_y2._==0)?_y1>=_y2.a:I_compareInt(_y2.a,_y1)<=0;}else{var _y3=_y0.a,_y4=E(_xZ);return (_y4._==0)?I_compareInt(_y3,_y4.a)>=0:I_compare(_y3,_y4.a)>=0;}},_y5=function(_y6,_y7,_y8){if(!B(_xX(_y7,_xW))){var _y9=function(_ya){return (!B(_51(_ya,_y8)))?new T2(1,_ya,new T(function(){return B(_y9(B(_4p(_ya,_y7))));})):__Z;};return new F(function(){return _y9(_y6);});}else{var _yb=function(_yc){return (!B(_4S(_yc,_y8)))?new T2(1,_yc,new T(function(){return B(_yb(B(_4p(_yc,_y7))));})):__Z;};return new F(function(){return _yb(_y6);});}},_yd=function(_ye,_yf,_yg){return new F(function(){return _y5(_ye,B(_6K(_yf,_ye)),_yg);});},_yh=function(_yi,_yj){return new F(function(){return _y5(_yi,_xJ,_yj);});},_yk=function(_yl){return new F(function(){return _4m(_yl);});},_ym=function(_yn){return new F(function(){return _6K(_yn,_xJ);});},_yo=function(_yp){return new F(function(){return _4p(_yp,_xJ);});},_yq=function(_yr){return new F(function(){return _rR(E(_yr));});},_ys={_:0,a:_yo,b:_ym,c:_yq,d:_yk,e:_xP,f:_xS,g:_yh,h:_yd},_yt=function(_yu,_yv){while(1){var _yw=E(_yu);if(!_yw._){var _yx=E(_yw.a);if(_yx==(-2147483648)){_yu=new T1(1,I_fromInt(-2147483648));continue;}else{var _yy=E(_yv);if(!_yy._){return new T1(0,B(_tN(_yx,_yy.a)));}else{_yu=new T1(1,I_fromInt(_yx));_yv=_yy;continue;}}}else{var _yz=_yw.a,_yA=E(_yv);return (_yA._==0)?new T1(1,I_div(_yz,I_fromInt(_yA.a))):new T1(1,I_div(_yz,_yA.a));}}},_yB=function(_yC,_yD){if(!B(_4e(_yD,_wg))){return new F(function(){return _yt(_yC,_yD);});}else{return E(_49);}},_yE=function(_yF,_yG){while(1){var _yH=E(_yF);if(!_yH._){var _yI=E(_yH.a);if(_yI==(-2147483648)){_yF=new T1(1,I_fromInt(-2147483648));continue;}else{var _yJ=E(_yG);if(!_yJ._){var _yK=_yJ.a;return new T2(0,new T1(0,B(_tN(_yI,_yK))),new T1(0,B(_uj(_yI,_yK))));}else{_yF=new T1(1,I_fromInt(_yI));_yG=_yJ;continue;}}}else{var _yL=E(_yG);if(!_yL._){_yF=_yH;_yG=new T1(1,I_fromInt(_yL.a));continue;}else{var _yM=I_divMod(_yH.a,_yL.a);return new T2(0,new T1(1,_yM.a),new T1(1,_yM.b));}}}},_yN=function(_yO,_yP){if(!B(_4e(_yP,_wg))){var _yQ=B(_yE(_yO,_yP));return new T2(0,_yQ.a,_yQ.b);}else{return E(_49);}},_yR=function(_yS,_yT){while(1){var _yU=E(_yS);if(!_yU._){var _yV=E(_yU.a);if(_yV==(-2147483648)){_yS=new T1(1,I_fromInt(-2147483648));continue;}else{var _yW=E(_yT);if(!_yW._){return new T1(0,B(_uj(_yV,_yW.a)));}else{_yS=new T1(1,I_fromInt(_yV));_yT=_yW;continue;}}}else{var _yX=_yU.a,_yY=E(_yT);return (_yY._==0)?new T1(1,I_mod(_yX,I_fromInt(_yY.a))):new T1(1,I_mod(_yX,_yY.a));}}},_yZ=function(_z0,_z1){if(!B(_4e(_z1,_wg))){return new F(function(){return _yR(_z0,_z1);});}else{return E(_49);}},_z2=function(_z3,_z4){while(1){var _z5=E(_z3);if(!_z5._){var _z6=E(_z5.a);if(_z6==(-2147483648)){_z3=new T1(1,I_fromInt(-2147483648));continue;}else{var _z7=E(_z4);if(!_z7._){return new T1(0,quot(_z6,_z7.a));}else{_z3=new T1(1,I_fromInt(_z6));_z4=_z7;continue;}}}else{var _z8=_z5.a,_z9=E(_z4);return (_z9._==0)?new T1(0,I_toInt(I_quot(_z8,I_fromInt(_z9.a)))):new T1(1,I_quot(_z8,_z9.a));}}},_za=function(_zb,_zc){if(!B(_4e(_zc,_wg))){return new F(function(){return _z2(_zb,_zc);});}else{return E(_49);}},_zd=function(_ze,_zf){if(!B(_4e(_zf,_wg))){var _zg=B(_4y(_ze,_zf));return new T2(0,_zg.a,_zg.b);}else{return E(_49);}},_zh=function(_zi,_zj){while(1){var _zk=E(_zi);if(!_zk._){var _zl=E(_zk.a);if(_zl==(-2147483648)){_zi=new T1(1,I_fromInt(-2147483648));continue;}else{var _zm=E(_zj);if(!_zm._){return new T1(0,_zl%_zm.a);}else{_zi=new T1(1,I_fromInt(_zl));_zj=_zm;continue;}}}else{var _zn=_zk.a,_zo=E(_zj);return (_zo._==0)?new T1(1,I_rem(_zn,I_fromInt(_zo.a))):new T1(1,I_rem(_zn,_zo.a));}}},_zp=function(_zq,_zr){if(!B(_4e(_zr,_wg))){return new F(function(){return _zh(_zq,_zr);});}else{return E(_49);}},_zs=function(_zt){return E(_zt);},_zu=function(_zv){return E(_zv);},_zw=function(_zx){var _zy=E(_zx);if(!_zy._){var _zz=E(_zy.a);return (_zz==(-2147483648))?E(_7o):(_zz<0)?new T1(0, -_zz):E(_zy);}else{var _zA=_zy.a;return (I_compareInt(_zA,0)>=0)?E(_zy):new T1(1,I_negate(_zA));}},_zB=new T1(0,0),_zC=new T1(0,-1),_zD=function(_zE){var _zF=E(_zE);if(!_zF._){var _zG=_zF.a;return (_zG>=0)?(E(_zG)==0)?E(_zB):E(_50):E(_zC);}else{var _zH=I_compareInt(_zF.a,0);return (_zH<=0)?(E(_zH)==0)?E(_zB):E(_zC):E(_50);}},_zI={_:0,a:_4p,b:_6K,c:_vQ,d:_7p,e:_zw,f:_zD,g:_zu},_zJ=function(_zK,_zL){var _zM=E(_zK);if(!_zM._){var _zN=_zM.a,_zO=E(_zL);return (_zO._==0)?_zN!=_zO.a:(I_compareInt(_zO.a,_zN)==0)?false:true;}else{var _zP=_zM.a,_zQ=E(_zL);return (_zQ._==0)?(I_compareInt(_zP,_zQ.a)==0)?false:true:(I_compare(_zP,_zQ.a)==0)?false:true;}},_zR=new T2(0,_4e,_zJ),_zS=function(_zT,_zU){return (!B(_6v(_zT,_zU)))?E(_zT):E(_zU);},_zV=function(_zW,_zX){return (!B(_6v(_zW,_zX)))?E(_zX):E(_zW);},_zY={_:0,a:_zR,b:_31,c:_51,d:_6v,e:_4S,f:_xX,g:_zS,h:_zV},_zZ=function(_A0){return new T2(0,E(_A0),E(_o9));},_A1=new T3(0,_zI,_zY,_zZ),_A2={_:0,a:_A1,b:_ys,c:_za,d:_zp,e:_yB,f:_yZ,g:_zd,h:_yN,i:_zs},_A3=function(_A4){return E(E(_A4).b);},_A5=function(_A6){return E(E(_A6).g);},_A7=new T1(0,1),_A8=function(_A9,_Aa,_Ab){var _Ac=B(_A3(_A9)),_Ad=B(_8w(_Ac)),_Ae=new T(function(){var _Af=new T(function(){var _Ag=new T(function(){var _Ah=new T(function(){return B(A3(_A5,_A9,_A2,new T(function(){return B(A3(_an,_Ac,_Aa,_Ab));})));});return B(A2(_ad,_Ad,_Ah));}),_Ai=new T(function(){return B(A2(_7Y,_Ad,new T(function(){return B(A2(_ad,_Ad,_A7));})));});return B(A3(_8y,_Ad,_Ai,_Ag));});return B(A3(_8y,_Ad,_Af,_Ab));});return new F(function(){return A3(_7W,_Ad,_Aa,_Ae);});},_Aj=1.5707963267948966,_Ak=function(_Al){return 0.2/Math.cos(B(_A8(_xI,_Al,_Aj))-0.7853981633974483);},_Am=2,_An=0.3,_Ao=new T(function(){var _Ap=B(_qj(_Ak,1.2,_rN,_rB,_rB,_rB,_rB,_rM,_An,_Am,_rB,_rB,_rI));return {_:0,a:E(_Ap.a),b:E(_Ap.b),c:E(_Ap.c),d:E(_Ap.d),e:E(_Ap.e),f:E(_Ap.f),g:E(_Ap.g),h:E(_Ap.h),i:E(_Ap.i)};}),_Aq=new T2(1,_Ao,_T),_Ar=new T2(1,_rJ,_Aq),_As=new T(function(){return B(unCStr("Negative range size"));}),_At=new T(function(){return B(err(_As));}),_Au=function(_){var _Av=B(_ir(_Ar,0))-1|0,_Aw=function(_Ax){if(_Ax>=0){var _Ay=newArr(_Ax,_ix),_Az=_Ay,_AA=E(_Ax);if(!_AA){return new T4(0,E(_rL),E(_Av),0,_Az);}else{var _AB=function(_AC,_AD,_){while(1){var _AE=E(_AC);if(!_AE._){return E(_);}else{var _=_Az[_AD]=_AE.a;if(_AD!=(_AA-1|0)){var _AF=_AD+1|0;_AC=_AE.b;_AD=_AF;continue;}else{return E(_);}}}},_=B((function(_AG,_AH,_AI,_){var _=_Az[_AI]=_AG;if(_AI!=(_AA-1|0)){return new F(function(){return _AB(_AH,_AI+1|0,_);});}else{return E(_);}})(_rJ,_Aq,0,_));return new T4(0,E(_rL),E(_Av),_AA,_Az);}}else{return E(_At);}};if(0>_Av){return new F(function(){return _Aw(0);});}else{return new F(function(){return _Aw(_Av+1|0);});}},_AJ=function(_AK){var _AL=B(A1(_AK,_));return E(_AL);},_AM=new T(function(){return B(_AJ(_Au));}),_AN=function(_AO,_AP,_){var _AQ=B(A1(_AO,_)),_AR=B(A1(_AP,_));return _AQ;},_AS=function(_AT,_AU,_){var _AV=B(A1(_AT,_)),_AW=B(A1(_AU,_));return new T(function(){return B(A1(_AV,_AW));});},_AX=function(_AY,_AZ,_){var _B0=B(A1(_AZ,_));return _AY;},_B1=function(_B2,_B3,_){var _B4=B(A1(_B3,_));return new T(function(){return B(A1(_B2,_B4));});},_B5=new T2(0,_B1,_AX),_B6=function(_B7,_){return _B7;},_B8=function(_B9,_Ba,_){var _Bb=B(A1(_B9,_));return new F(function(){return A1(_Ba,_);});},_Bc=new T5(0,_B5,_B6,_AS,_B8,_AN),_Bd=function(_Be){var _Bf=E(_Be);return (E(_Bf.b)-E(_Bf.a)|0)+1|0;},_Bg=function(_Bh,_Bi){var _Bj=E(_Bh),_Bk=E(_Bi);return (E(_Bj.a)>_Bk)?false:_Bk<=E(_Bj.b);},_Bl=function(_Bm,_Bn){var _Bo=jsShowI(_Bm);return new F(function(){return _14(fromJSStr(_Bo),_Bn);});},_Bp=function(_Bq,_Br,_Bs){if(_Br>=0){return new F(function(){return _Bl(_Br,_Bs);});}else{if(_Bq<=6){return new F(function(){return _Bl(_Br,_Bs);});}else{return new T2(1,_8f,new T(function(){var _Bt=jsShowI(_Br);return B(_14(fromJSStr(_Bt),new T2(1,_8e,_Bs)));}));}}},_Bu=function(_Bv){return new F(function(){return _Bp(0,E(_Bv),_T);});},_Bw=function(_Bx,_By,_Bz){return new F(function(){return _Bp(E(_Bx),E(_By),_Bz);});},_BA=function(_BB,_BC){return new F(function(){return _Bp(0,E(_BB),_BC);});},_BD=function(_BE,_BF){return new F(function(){return _3P(_BA,_BE,_BF);});},_BG=new T3(0,_Bw,_Bu,_BD),_BH=0,_BI=function(_BJ,_BK,_BL){return new F(function(){return A1(_BJ,new T2(1,_3M,new T(function(){return B(A1(_BK,_BL));})));});},_BM=new T(function(){return B(unCStr(": empty list"));}),_BN=new T(function(){return B(unCStr("Prelude."));}),_BO=function(_BP){return new F(function(){return err(B(_14(_BN,new T(function(){return B(_14(_BP,_BM));},1))));});},_BQ=new T(function(){return B(unCStr("foldr1"));}),_BR=new T(function(){return B(_BO(_BQ));}),_BS=function(_BT,_BU){var _BV=E(_BU);if(!_BV._){return E(_BR);}else{var _BW=_BV.a,_BX=E(_BV.b);if(!_BX._){return E(_BW);}else{return new F(function(){return A2(_BT,_BW,new T(function(){return B(_BS(_BT,_BX));}));});}}},_BY=new T(function(){return B(unCStr(" out of range "));}),_BZ=new T(function(){return B(unCStr("}.index: Index "));}),_C0=new T(function(){return B(unCStr("Ix{"));}),_C1=new T2(1,_8e,_T),_C2=new T2(1,_8e,_C1),_C3=0,_C4=function(_C5){return E(E(_C5).a);},_C6=function(_C7,_C8,_C9,_Ca,_Cb){var _Cc=new T(function(){var _Cd=new T(function(){var _Ce=new T(function(){var _Cf=new T(function(){var _Cg=new T(function(){return B(A3(_BS,_BI,new T2(1,new T(function(){return B(A3(_C4,_C9,_C3,_Ca));}),new T2(1,new T(function(){return B(A3(_C4,_C9,_C3,_Cb));}),_T)),_C2));});return B(_14(_BY,new T2(1,_8f,new T2(1,_8f,_Cg))));});return B(A(_C4,[_C9,_BH,_C8,new T2(1,_8e,_Cf)]));});return B(_14(_BZ,new T2(1,_8f,_Ce)));},1);return B(_14(_C7,_Cd));},1);return new F(function(){return err(B(_14(_C0,_Cc)));});},_Ch=function(_Ci,_Cj,_Ck,_Cl,_Cm){return new F(function(){return _C6(_Ci,_Cj,_Cm,_Ck,_Cl);});},_Cn=function(_Co,_Cp,_Cq,_Cr){var _Cs=E(_Cq);return new F(function(){return _Ch(_Co,_Cp,_Cs.a,_Cs.b,_Cr);});},_Ct=function(_Cu,_Cv,_Cw,_Cx){return new F(function(){return _Cn(_Cx,_Cw,_Cv,_Cu);});},_Cy=new T(function(){return B(unCStr("Int"));}),_Cz=function(_CA,_CB){return new F(function(){return _Ct(_BG,_CB,_CA,_Cy);});},_CC=function(_CD,_CE){var _CF=E(_CD),_CG=E(_CF.a),_CH=E(_CE);if(_CG>_CH){return new F(function(){return _Cz(_CH,_CF);});}else{if(_CH>E(_CF.b)){return new F(function(){return _Cz(_CH,_CF);});}else{return _CH-_CG|0;}}},_CI=function(_CJ){var _CK=E(_CJ);return new F(function(){return _tx(_CK.a,_CK.b);});},_CL=function(_CM){var _CN=E(_CM),_CO=E(_CN.a),_CP=E(_CN.b);return (_CO>_CP)?E(_BH):(_CP-_CO|0)+1|0;},_CQ=function(_CR,_CS){return new F(function(){return _uW(_CS,E(_CR).a);});},_CT={_:0,a:_vM,b:_CI,c:_CC,d:_CQ,e:_Bg,f:_CL,g:_Bd},_CU=function(_CV,_CW){return new T2(1,_CV,_CW);},_CX=function(_CY,_CZ){var _D0=E(_CZ);return new T2(0,_D0.a,_D0.b);},_D1=function(_D2){return E(E(_D2).f);},_D3=function(_D4,_D5,_D6){var _D7=E(_D5),_D8=_D7.a,_D9=_D7.b,_Da=function(_){var _Db=B(A2(_D1,_D4,_D7));if(_Db>=0){var _Dc=newArr(_Db,_ix),_Dd=_Dc,_De=E(_Db);if(!_De){return new T(function(){return new T4(0,E(_D8),E(_D9),0,_Dd);});}else{var _Df=function(_Dg,_Dh,_){while(1){var _Di=E(_Dg);if(!_Di._){return E(_);}else{var _=_Dd[_Dh]=_Di.a;if(_Dh!=(_De-1|0)){var _Dj=_Dh+1|0;_Dg=_Di.b;_Dh=_Dj;continue;}else{return E(_);}}}},_=B(_Df(_D6,0,_));return new T(function(){return new T4(0,E(_D8),E(_D9),_De,_Dd);});}}else{return E(_At);}};return new F(function(){return _AJ(_Da);});},_Dk=function(_Dl,_Dm,_Dn,_Do){var _Dp=new T(function(){var _Dq=E(_Do),_Dr=_Dq.c-1|0,_Ds=new T(function(){return B(A2(_e9,_Dm,_T));});if(0<=_Dr){var _Dt=new T(function(){return B(_aj(_Dm));}),_Du=function(_Dv){var _Dw=new T(function(){var _Dx=new T(function(){return B(A1(_Dn,new T(function(){return E(_Dq.d[_Dv]);})));});return B(A3(_ar,_Dt,_CU,_Dx));});return new F(function(){return A3(_ap,_Dm,_Dw,new T(function(){if(_Dv!=_Dr){return B(_Du(_Dv+1|0));}else{return E(_Ds);}}));});};return B(_Du(0));}else{return E(_Ds);}}),_Dy=new T(function(){return B(_CX(_Dl,_Do));});return new F(function(){return A3(_ar,B(_aj(_Dm)),function(_Dz){return new F(function(){return _D3(_Dl,_Dy,_Dz);});},_Dp);});},_DA=function(_DB,_DC,_DD){var _DE=E(_DD);if(!_DE._){return E(_DC);}else{return new F(function(){return A2(_DB,_DE.a,new T(function(){return B(_DA(_DB,_DC,_DE.b));}));});}},_DF=function(_){return _S;},_DG=new T(function(){return eval("vertex");}),_DH=function(_DI,_DJ,_){var _DK=E(_DI),_DL=E(_DK.a),_DM=E(_DK.b),_DN=__apply(E(_DG),new T2(1,_DK.c,new T2(1,_DM.b,new T2(1,_DM.a,new T2(1,_DL.c,new T2(1,_DL.b,new T2(1,_DL.a,_T)))))));return new F(function(){return A1(_DJ,_);});},_DO=function(_DP,_DQ,_){var _DR=B(A(_DA,[_DH,_DF,B(_n3(B(_mj(new T2(1,new T(function(){return E(E(_DP).a);}),new T2(1,new T(function(){return E(E(_DP).b);}),new T2(1,new T(function(){return E(E(_DP).c);}),_T))))),_mp)),_]));return new F(function(){return A1(_DQ,_);});},_DS=function(_){return _S;},_DT=new T(function(){return eval("drawTriangles");}),_DU=function(_){var _DV=__app0(E(_DT));return new F(function(){return _DS(_);});},_DW=function(_DX,_){var _DY=B(A(_DA,[_DO,_DF,E(_DX).h,_]));return new F(function(){return _DU(_);});},_DZ=new T(function(){return eval("draw");}),_E0=function(_E1){return E(_E1);},_E2=function(_E3){return E(_E3);},_E4=function(_E5,_E6){return E(_E6);},_E7=function(_E8,_E9){return E(_E8);},_Ea=function(_Eb){return E(_Eb);},_Ec=new T2(0,_Ea,_E7),_Ed=function(_Ee,_Ef){return E(_Ee);},_Eg=new T5(0,_Ec,_E2,_E0,_E4,_Ed),_Eh=6,_Ei=new T(function(){return B(unCStr(" :! "));}),_Ej=new T(function(){return B(unCStr("Nil"));}),_Ek=function(_El){return new F(function(){return _14(_Ej,_El);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Ep);if(!_Eq._){return E(_Ek);}else{var _Er=new T(function(){return B(A3(_C4,_En,_Eh,_Eq.a));}),_Es=new T(function(){return B(_Em(_En,_Eh,_Eq.b));});if(E(_Eo)<6){var _Et=function(_Eu){var _Ev=new T(function(){return B(_14(_Ei,new T(function(){return B(A1(_Es,_Eu));},1)));});return new F(function(){return A1(_Er,_Ev);});};return E(_Et);}else{var _Ew=function(_Ex){var _Ey=new T(function(){var _Ez=new T(function(){return B(_14(_Ei,new T(function(){return B(A1(_Es,new T2(1,_8e,_Ex)));},1)));});return B(A1(_Er,_Ez));});return new T2(1,_8f,_Ey);};return E(_Ew);}}},_EA=function(_EB,_EC,_ED,_){var _EE=B(A2(_EC,_ED,_));return new T2(0,_EB,new T(function(){return E(E(_EE).b);}));},_EF=function(_EG,_EH,_EI,_){var _EJ=B(A2(_EH,_EI,_)),_EK=new T(function(){return B(A1(_EG,new T(function(){return E(E(_EJ).a);})));});return new T2(0,_EK,new T(function(){return E(E(_EJ).b);}));},_EL=new T2(0,_EF,_EA),_EM=function(_EN,_EO,_EP,_){var _EQ=B(A2(_EN,_EP,_)),_ER=B(A2(_EO,new T(function(){return E(E(_EQ).b);}),_)),_ES=new T(function(){return B(A1(E(_EQ).a,new T(function(){return E(E(_ER).a);})));});return new T2(0,_ES,new T(function(){return E(E(_ER).b);}));},_ET=function(_EU,_EV,_EW,_){var _EX=B(A2(_EU,_EW,_)),_EY=B(A2(_EV,new T(function(){return E(E(_EX).b);}),_));return new T2(0,new T(function(){return E(E(_EY).a);}),new T(function(){return E(E(_EY).b);}));},_EZ=function(_F0,_F1,_F2,_){var _F3=B(A2(_F0,_F2,_)),_F4=B(A2(_F1,new T(function(){return E(E(_F3).b);}),_));return new T2(0,new T(function(){return E(E(_F3).a);}),new T(function(){return E(E(_F4).b);}));},_F5=function(_F6,_F7,_){return new T2(0,_F6,_F7);},_F8=new T5(0,_EL,_F5,_EM,_ET,_EZ),_F9=function(_Fa){var _Fb=jsShow(E(_Fa));return new F(function(){return fromJSStr(_Fb);});},_Fc=function(_Fd){var _Fe=jsShow(E(_Fd));return new F(function(){return fromJSStr(_Fe);});},_Ff=function(_Fg){var _Fh=new T(function(){return B(_Fc(_Fg));});return function(_Fi){return new F(function(){return _14(_Fh,_Fi);});};},_Fj=function(_Fk,_Fl){return new F(function(){return _3P(_Ff,_Fk,_Fl);});},_Fm=function(_Fn,_Fo){var _Fp=new T(function(){return B(_Fc(_Fo));});return function(_Fi){return new F(function(){return _14(_Fp,_Fi);});};},_Fq=new T3(0,_Fm,_F9,_Fj),_Fr=new T(function(){return B(unCStr("World "));}),_Fs=11,_Ft=32,_Fu=function(_Fv,_Fw,_Fx,_Fy,_Fz){var _FA=new T(function(){return B(A3(_C4,_Fv,_Fs,_Fx));}),_FB=new T(function(){return B(A3(_C4,_Fv,_Fs,_Fy));}),_FC=new T(function(){return B(A3(_C4,_Fv,_Fs,_Fz));}),_FD=function(_FE){var _FF=new T(function(){var _FG=new T(function(){return B(A1(_FB,new T2(1,_Ft,new T(function(){return B(A1(_FC,_FE));}))));});return B(A1(_FA,new T2(1,_Ft,_FG)));},1);return new F(function(){return _14(_Fr,_FF);});};if(_Fw<11){return E(_FD);}else{var _FH=function(_FI){return new T2(1,_8f,new T(function(){return B(_FD(new T2(1,_8e,_FI)));}));};return E(_FH);}},_FJ=new T(function(){return B(unCStr("Local "));}),_FK=11,_FL=function(_FM,_FN,_FO,_FP){var _FQ=new T(function(){return B(A3(_C4,_FM,_FK,_FO));}),_FR=new T(function(){return B(A3(_C4,_FM,_FK,_FP));});if(_FN<11){var _FS=function(_FT){var _FU=new T(function(){return B(A1(_FQ,new T2(1,_Ft,new T(function(){return B(A1(_FR,_FT));}))));},1);return new F(function(){return _14(_FJ,_FU);});};return E(_FS);}else{var _FV=function(_FW){var _FX=new T(function(){var _FY=new T(function(){return B(A1(_FQ,new T2(1,_Ft,new T(function(){return B(A1(_FR,new T2(1,_8e,_FW)));}))));},1);return B(_14(_FJ,_FY));});return new T2(1,_8f,_FX);};return E(_FV);}},_FZ=function(_G0,_G1,_G2){var _G3=new T(function(){return B(A3(_BS,_BI,new T2(1,new T(function(){var _G4=E(_G0);return B(_Fu(_Fq,0,_G4.a,_G4.b,_G4.c));}),new T2(1,new T(function(){var _G5=E(_G1);return B(_FL(_Fq,0,_G5.a,_G5.b));}),_T)),new T2(1,_8e,_G2)));});return new T2(0,_8f,_G3);},_G6=function(_G7,_G8,_G9){var _Ga=E(_G8),_Gb=B(_FZ(_Ga.a,_Ga.b,_G9));return new T2(1,_Gb.a,_Gb.b);},_Gc=new T2(1,_8e,_T),_Gd=function(_Ge,_Gf){var _Gg=new T(function(){return B(A3(_BS,_BI,new T2(1,new T(function(){var _Gh=E(_Ge);return B(_Fu(_Fq,0,_Gh.a,_Gh.b,_Gh.c));}),new T2(1,new T(function(){var _Gi=E(_Gf);return B(_FL(_Fq,0,_Gi.a,_Gi.b));}),_T)),_Gc));});return new T2(0,_8f,_Gg);},_Gj=function(_Gk){var _Gl=E(_Gk),_Gm=B(_Gd(_Gl.a,_Gl.b));return new T2(1,_Gm.a,_Gm.b);},_Gn=function(_Go,_Gp){var _Gq=E(_Go),_Gr=new T(function(){return B(A3(_BS,_BI,new T2(1,new T(function(){var _Gs=E(_Gq.a);return B(_Fu(_Fq,0,_Gs.a,_Gs.b,_Gs.c));}),new T2(1,new T(function(){var _Gt=E(_Gq.b);return B(_FL(_Fq,0,_Gt.a,_Gt.b));}),_T)),new T2(1,_8e,_Gp)));});return new T2(1,_8f,_Gr);},_Gu=function(_Gv,_Gw){return new F(function(){return _3P(_Gn,_Gv,_Gw);});},_Gx=new T3(0,_G6,_Gj,_Gu),_Gy=new T(function(){return B(unCStr("base"));}),_Gz=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_GA=new T(function(){return B(unCStr("IOException"));}),_GB=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Gy,_Gz,_GA),_GC=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_GB,_T,_T),_GD=function(_GE){return E(_GC);},_GF=function(_GG){var _GH=E(_GG);return new F(function(){return _3m(B(_3k(_GH.a)),_GD,_GH.b);});},_GI=new T(function(){return B(unCStr(": "));}),_GJ=new T(function(){return B(unCStr(")"));}),_GK=new T(function(){return B(unCStr(" ("));}),_GL=new T(function(){return B(unCStr("interrupted"));}),_GM=new T(function(){return B(unCStr("system error"));}),_GN=new T(function(){return B(unCStr("unsatisified constraints"));}),_GO=new T(function(){return B(unCStr("user error"));}),_GP=new T(function(){return B(unCStr("permission denied"));}),_GQ=new T(function(){return B(unCStr("illegal operation"));}),_GR=new T(function(){return B(unCStr("end of file"));}),_GS=new T(function(){return B(unCStr("resource exhausted"));}),_GT=new T(function(){return B(unCStr("resource busy"));}),_GU=new T(function(){return B(unCStr("does not exist"));}),_GV=new T(function(){return B(unCStr("already exists"));}),_GW=new T(function(){return B(unCStr("resource vanished"));}),_GX=new T(function(){return B(unCStr("timeout"));}),_GY=new T(function(){return B(unCStr("unsupported operation"));}),_GZ=new T(function(){return B(unCStr("hardware fault"));}),_H0=new T(function(){return B(unCStr("inappropriate type"));}),_H1=new T(function(){return B(unCStr("invalid argument"));}),_H2=new T(function(){return B(unCStr("failed"));}),_H3=new T(function(){return B(unCStr("protocol error"));}),_H4=function(_H5,_H6){switch(E(_H5)){case 0:return new F(function(){return _14(_GV,_H6);});break;case 1:return new F(function(){return _14(_GU,_H6);});break;case 2:return new F(function(){return _14(_GT,_H6);});break;case 3:return new F(function(){return _14(_GS,_H6);});break;case 4:return new F(function(){return _14(_GR,_H6);});break;case 5:return new F(function(){return _14(_GQ,_H6);});break;case 6:return new F(function(){return _14(_GP,_H6);});break;case 7:return new F(function(){return _14(_GO,_H6);});break;case 8:return new F(function(){return _14(_GN,_H6);});break;case 9:return new F(function(){return _14(_GM,_H6);});break;case 10:return new F(function(){return _14(_H3,_H6);});break;case 11:return new F(function(){return _14(_H2,_H6);});break;case 12:return new F(function(){return _14(_H1,_H6);});break;case 13:return new F(function(){return _14(_H0,_H6);});break;case 14:return new F(function(){return _14(_GZ,_H6);});break;case 15:return new F(function(){return _14(_GY,_H6);});break;case 16:return new F(function(){return _14(_GX,_H6);});break;case 17:return new F(function(){return _14(_GW,_H6);});break;default:return new F(function(){return _14(_GL,_H6);});}},_H7=new T(function(){return B(unCStr("}"));}),_H8=new T(function(){return B(unCStr("{handle: "));}),_H9=function(_Ha,_Hb,_Hc,_Hd,_He,_Hf){var _Hg=new T(function(){var _Hh=new T(function(){var _Hi=new T(function(){var _Hj=E(_Hd);if(!_Hj._){return E(_Hf);}else{var _Hk=new T(function(){return B(_14(_Hj,new T(function(){return B(_14(_GJ,_Hf));},1)));},1);return B(_14(_GK,_Hk));}},1);return B(_H4(_Hb,_Hi));}),_Hl=E(_Hc);if(!_Hl._){return E(_Hh);}else{return B(_14(_Hl,new T(function(){return B(_14(_GI,_Hh));},1)));}}),_Hm=E(_He);if(!_Hm._){var _Hn=E(_Ha);if(!_Hn._){return E(_Hg);}else{var _Ho=E(_Hn.a);if(!_Ho._){var _Hp=new T(function(){var _Hq=new T(function(){return B(_14(_H7,new T(function(){return B(_14(_GI,_Hg));},1)));},1);return B(_14(_Ho.a,_Hq));},1);return new F(function(){return _14(_H8,_Hp);});}else{var _Hr=new T(function(){var _Hs=new T(function(){return B(_14(_H7,new T(function(){return B(_14(_GI,_Hg));},1)));},1);return B(_14(_Ho.a,_Hs));},1);return new F(function(){return _14(_H8,_Hr);});}}}else{return new F(function(){return _14(_Hm.a,new T(function(){return B(_14(_GI,_Hg));},1));});}},_Ht=function(_Hu){var _Hv=E(_Hu);return new F(function(){return _H9(_Hv.a,_Hv.b,_Hv.c,_Hv.d,_Hv.f,_T);});},_Hw=function(_Hx,_Hy,_Hz){var _HA=E(_Hy);return new F(function(){return _H9(_HA.a,_HA.b,_HA.c,_HA.d,_HA.f,_Hz);});},_HB=function(_HC,_HD){var _HE=E(_HC);return new F(function(){return _H9(_HE.a,_HE.b,_HE.c,_HE.d,_HE.f,_HD);});},_HF=function(_HG,_HH){return new F(function(){return _3P(_HB,_HG,_HH);});},_HI=new T3(0,_Hw,_Ht,_HF),_HJ=new T(function(){return new T5(0,_GD,_HI,_HK,_GF,_Ht);}),_HK=function(_HL){return new T2(0,_HJ,_HL);},_HM=__Z,_HN=7,_HO=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:88:7-13"));}),_HP=new T6(0,_HM,_HN,_T,_HO,_HM,_HM),_HQ=new T(function(){return B(_HK(_HP));}),_HR=function(_){return new F(function(){return die(_HQ);});},_HS=function(_HT,_HU){var _HV=E(_HT);return (_HV._==0)?E(_HU):E(_HV);},_HW=function(_HX,_HY,_HZ){var _I0=E(_HZ);if(!_I0._){return new F(function(){return _1m(_HX);});}else{return new F(function(){return A3(_1k,_HX,new T(function(){return B(A1(_HY,_I0.a));}),new T(function(){return B(_HW(_HX,_HY,_I0.b));}));});}},_I1=function(_I2){while(1){var _I3=E(_I2);if(!_I3._){return true;}else{if(!E(_I3.a)){return false;}else{_I2=_I3.b;continue;}}}},_I4=function(_I5){return new F(function(){return _I1(_I5);});},_I6=function(_I7,_I8){return (!E(_I7))?false:E(_I8);},_I9=true,_Ia=new T3(0,_I9,_I6,_I4),_Ib=function(_Ic,_Id,_Ie,_If,_Ig){var _Ih=B(_8w(B(_8u(_Ic))));return new F(function(){return A3(_7W,_Ih,new T(function(){return B(A3(_8y,_Ih,_Id,_If));}),new T(function(){return B(A3(_8y,_Ih,_Ie,_Ig));}));});},_Ii=function(_Ij,_Ik){var _Il=new T(function(){return E(E(_Ik).c);}),_Im=B(_8w(B(_8u(_Ij)))),_In=new T(function(){return B(A3(_8y,_Im,new T(function(){return E(E(E(_Ik).b).b);}),new T(function(){return E(E(E(_Ik).b).a);})));});return new T2(0,B(A3(_8y,_Im,_In,new T(function(){return B(A2(_cM,_Ij,_Il));}))),B(A3(_8y,_Im,_In,new T(function(){return B(A2(_cO,_Ij,_Il));}))));},_Io=function(_Ip){return E(_Ip)>=0;},_Iq=function(_Ir){while(1){var _Is=B((function(_It){var _Iu=E(_It);if(!_Iu._){return __Z;}else{var _Iv=_Iu.b,_Iw=E(_Iu.a);if(!_Iw._){_Ir=_Iv;return __continue;}else{return new T2(1,_Iw.a,new T(function(){return B(_Iq(_Iv));}));}}})(_Ir));if(_Is!=__continue){return _Is;}}},_Ix=function(_Iy,_Iz,_IA,_IB,_IC,_ID,_IE,_IF,_IG,_IH){var _II=function(_IJ,_IK){var _IL=new T(function(){var _IM=function(_IN){var _IO=E(E(_IJ).a),_IP=E(_IO.a),_IQ=E(_IO.b),_IR=E(_IO.c),_IS=E(_IN),_IT=E(_IS.a),_IU=E(_IT.a),_IV=E(_IU.a),_IW=E(_IU.b),_IX=E(_IU.c),_IY=E(_IS.c),_IZ=E(_IY.a),_J0=E(_IZ.a),_J1=E(_IZ.b),_J2=E(_IZ.c),_J3=E(_IS.b),_J4=E(_J3.a),_J5=E(_J4.a),_J6=E(_J4.b),_J7=E(_J4.c),_J8=E(_IT.b),_J9=E(_IT.c),_Ja=E(_J3.b),_Jb=E(_J3.c),_Jc=E(_IY.b),_Jd=E(_IY.c),_Je=_J0+ -_IV,_Jf=_J1+ -_IW,_Jg=_J2+ -_IX,_Jh=_J0+ -_J5,_Ji=_J1+ -_J6,_Jj=_J2+ -_J7,_Jk=B(_kO(_k3,_Jf*_Jj-_Ji*_Jg,_Jg*_Jh-_Jj*_Je,_Je*_Ji-_Jh*_Jf)),_Jl=_Jk.a,_Jm=_Jk.b,_Jn=_Jk.c,_Jo=B(_kE(_k3,_IP+ -_IV,_IQ+ -_IW,_IR+ -_IX,_Jl,_Jm,_Jn)),_Jp=function(_Jq){if(_Jq>=0.1){return __Z;}else{var _Jr=new T(function(){return new T3(0,_IP+ -(E(_Jl)*_Jo),_IQ+ -(E(_Jm)*_Jo),_IR+ -(E(_Jn)*_Jo));}),_Js=function(_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA,_JB){var _JC=E(_Jr),_JD=E(_Jm),_JE=E(_Jn),_JF=E(_Jl),_JG=_Jz+ -_Jw,_JH=_JA+ -_Jx,_JI=_JB+ -_Jy,_JJ=B(_kO(_k3,_JD*_JI-_JH*_JE,_JE*_JG-_JI*_JF,_JF*_JH-_JG*_JD)),_JK=_JJ.a,_JL=_JJ.b,_JM=_JJ.c;return B(_kE(_k3,E(_JC.a)+ -_Jw,E(_JC.b)+ -_Jx,E(_JC.c)+ -_Jy,_JK,_JL,_JM))/B(_kE(_k3,_Jt+ -_Jw,_Ju+ -_Jx,_Jv+ -_Jy,_JK,_JL,_JM));},_JN=new T(function(){return B(_Js(_IV,_IW,_IX,_J5,_J6,_J7,_J0,_J1,_J2));}),_JO=new T(function(){return B(_Js(_J5,_J6,_J7,_J0,_J1,_J2,_IV,_IW,_IX));}),_JP=new T(function(){return B(_Js(_J0,_J1,_J2,_IV,_IW,_IX,_J5,_J6,_J7));});return (!B(_HW(_Ia,_Io,B(_n3(B(_mj(new T2(1,_JN,new T2(1,_JO,new T2(1,_JP,_T))))),_mp)))))?__Z:new T1(1,new T(function(){var _JQ=E(_JN),_JR=E(_JO),_JS=E(_JP),_JT=E(_Jc.b)*E(_Jc.a),_JU=E(_Ja.b)*E(_Ja.a),_JV=E(_J8.b)*E(_J8.a);return new T2(0,_JV*Math.cos(_J9)*_JQ+_JU*Math.cos(_Jb)*_JR+_JT*Math.cos(_Jd)*_JS,_JV*Math.sin(_J9)*_JQ+_JU*Math.sin(_Jb)*_JR+_JT*Math.sin(_Jd)*_JS);}));}},_JW=E(_Jo);if(!_JW){return new F(function(){return _Jp(0);});}else{if(_JW<=0){return new F(function(){return _Jp( -_JW);});}else{return new F(function(){return _Jp(_JW);});}}},_JX=B(_DA(_HS,_HM,B(_mf(_IM,_IH))));if(!_JX._){return __Z;}else{var _JY=E(_JX.a),_JZ=B(_Ii(_k3,_IJ)),_K0=E(_JY.a)+ -E(_JZ.a),_K1=E(_JY.b)+ -E(_JZ.b);if(Math.sqrt(B(_Ib(_k3,_K0,_K1,_K0,_K1)))<1.0e-4){return __Z;}else{return new T1(1,new T2(0,new T(function(){return E(E(_IJ).a);}),_JY));}}}),_K2=function(_K3){return new T2(1,_IL,new T(function(){return B(A1(_IK,_K3));}));};return E(_K2);};return new F(function(){return _mj(B(_Iq(B(A(_DA,[_II,_11,_IG,_T])))));});},_K4=function(_K5,_K6,_){var _K7=E(_K5);return new T2(0,_S,_K6);},_K8=function(_K9){var _Ka=E(_K9),_Kb=E(_Ka.b),_Kc=E(_Ka.e),_Kd=E(_Kc.a),_Ke=E(_Ka.g),_Kf=B(_lE(_k3,_Kb.a,_Kb.b,_Kb.c,_Ke.a,_Ke.b,_Ke.c));return {_:0,a:E(_Ka.a),b:E(_Kb),c:E(_Ka.c),d:E(_Ka.d),e:E(new T2(0,E(new T3(0,E(_Kd.a)+E(_Kf.a)*5.0e-2,E(_Kd.b)+E(_Kf.b)*5.0e-2,E(_Kd.c)+E(_Kf.c)*5.0e-2)),E(_Kc.b))),f:E(_Ka.f),g:E(_Ke),h:E(_Ka.h),i:E(_Ka.i)};},_Kg=function(_Kh,_Ki,_Kj,_Kk,_Kl,_Km,_Kn,_Ko,_Kp){var _Kq=B(_8y(_Kh));return new T2(0,new T3(0,E(B(A1(B(A1(_Kq,_Ki)),_Km))),E(B(A1(B(A1(_Kq,_Kj)),_Kn))),E(B(A1(B(A1(_Kq,_Kk)),_Ko)))),B(A1(B(A1(_Kq,_Kl)),_Kp)));},_Kr=function(_Ks,_Kt,_Ku,_Kv,_Kw,_Kx,_Ky,_Kz,_KA){var _KB=B(_7W(_Ks));return new T2(0,new T3(0,E(B(A1(B(A1(_KB,_Kt)),_Kx))),E(B(A1(B(A1(_KB,_Ku)),_Ky))),E(B(A1(B(A1(_KB,_Kv)),_Kz)))),B(A1(B(A1(_KB,_Kw)),_KA)));},_KC=5.0e-2,_KD=function(_KE,_KF,_KG,_KH,_KI,_KJ,_KK,_KL,_KM,_KN,_KO,_KP,_KQ,_KR,_KS,_KT,_KU){var _KV=B(_Kg(_jx,_KL,_KM,_KN,_KO,_KC,_KC,_KC,_KC)),_KW=E(_KV.a),_KX=B(_Kr(_jx,_KH,_KI,_KJ,_KK,_KW.a,_KW.b,_KW.c,_KV.b)),_KY=E(_KX.a);return new F(function(){return _pF(_KE,_KF,_KG,_KY.a,_KY.b,_KY.c,_KX.b,_KL,_KM,_KN,_KO,_KP,_KQ,_KR,_KS,_KT,_KU);});},_KZ=function(_L0){var _L1=E(_L0),_L2=E(_L1.d),_L3=E(_L2.a),_L4=E(_L1.e),_L5=E(_L4.a),_L6=E(_L1.f),_L7=B(_KD(_L1.a,_L1.b,_L1.c,_L3.a,_L3.b,_L3.c,_L2.b,_L5.a,_L5.b,_L5.c,_L4.b,_L6.a,_L6.b,_L6.c,_L1.g,_L1.h,_L1.i));return {_:0,a:E(_L7.a),b:E(_L7.b),c:E(_L7.c),d:E(_L7.d),e:E(_L7.e),f:E(_L7.f),g:E(_L7.g),h:E(_L7.h),i:E(_L7.i)};},_L8=new T(function(){return B(_mj(_T));}),_L9=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:87:7-13"));}),_La=new T6(0,_HM,_HN,_T,_L9,_HM,_HM),_Lb=new T(function(){return B(_HK(_La));}),_Lc=new T(function(){return B(unCStr(")"));}),_Ld=function(_Le,_Lf){var _Lg=new T(function(){var _Lh=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_14(B(_Bp(0,_Le,_T)),_Lc));})));},1);return B(_14(B(_Bp(0,_Lf,_T)),_Lh));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Lg)));});},_Li=function(_Lj,_){var _Lk=B(_Dk(_CT,_Eg,_K8,_Lj)),_Ll=E(_Lk.b),_Lm=function(_Ln){var _Lo=new T(function(){var _Lp=E(_Ln),_Lq=function(_Lr,_Ls,_){var _Lt=E(_Ls),_Lu=_Lt.c,_Lv=_Lt.d,_Lw=E(_Lt.a),_Lx=E(_Lt.b);if(_Lw>_Lp){return new F(function(){return die(_Lb);});}else{if(_Lp>_Lx){return new F(function(){return die(_Lb);});}else{var _Ly=E(_Lr);if(_Lw>_Ly){return new F(function(){return _HR(_);});}else{if(_Ly>_Lx){return new F(function(){return _HR(_);});}else{var _Lz=new T(function(){var _LA=new T(function(){var _LB=_Lp-_Lw|0;if(0>_LB){return B(_Ld(_Lu,_LB));}else{if(_LB>=_Lu){return B(_Ld(_Lu,_LB));}else{return E(_Lv[_LB]);}}}),_LC=new T(function(){var _LD=_Ly-_Lw|0;if(0>_LD){return B(_Ld(_Lu,_LD));}else{if(_LD>=_Lu){return B(_Ld(_Lu,_LD));}else{return E(_Lv[_LD]);}}}),_LE=new T(function(){var _LF=E(_LC);return B(_Em(_Gx,_C3,B(_Ix(_LF.a,_LF.b,_LF.c,_LF.d,_LF.e,_LF.f,_LF.g,_LF.h,_LF.i,new T(function(){return E(E(_LA).h);})))));}),_LG=new T(function(){var _LH=E(_LA);return B(_Em(_Gx,_C3,B(_Ix(_LH.a,_LH.b,_LH.c,_LH.d,_LH.e,_LH.f,_LH.g,_LH.h,_LH.i,new T(function(){return E(E(_LC).h);})))));});return B(A3(_BS,_BI,new T2(1,_LG,new T2(1,_LE,_T)),_Gc));}),_LI=B(_ir(new T2(1,_8f,_Lz),0));return new F(function(){return A(_mq,[_F8,_K4,_L8,_Lt,_]);});}}}}};return B(_mq(_F8,_Lq,B(_mj(B(_sW(_Lp,_Ll))))));}),_LJ=function(_LK,_){var _LL=B(A2(_Lo,_LK,_));return new T2(0,new T(function(){return B(_nb(E(_LL).a));}),new T(function(){return E(E(_LL).b);}));};return E(_LJ);},_LM=B(A(_mq,[_F8,_Lm,B(_mj(B(_sW(E(_Lk.a),_Ll)))),_Lk,_])),_LN=new T(function(){return B(_Dk(_CT,_Eg,_KZ,new T(function(){return E(E(_LM).b);})));});return new T2(0,_S,_LN);},_LO=new T(function(){return eval("refresh");}),_LP=function(_LQ,_){var _LR=__app0(E(_LO)),_LS=__app0(E(_DZ)),_LT=B(A(_Dk,[_CT,_Bc,_DW,_LQ,_])),_LU=B(_Li(_LQ,_));return new T(function(){return E(E(_LU).b);});},_LV=function(_LW,_LX,_LY){var _LZ=function(_){var _M0=B(_LP(_LW,_));return new T(function(){return B(A1(_LY,new T1(1,_M0)));});};return new T1(0,_LZ);},_M1=new T0(2),_M2=function(_M3,_M4,_M5){return function(_){var _M6=E(_M3),_M7=rMV(_M6),_M8=E(_M7);if(!_M8._){var _M9=new T(function(){var _Ma=new T(function(){return B(A1(_M5,_S));});return B(_14(_M8.b,new T2(1,new T2(0,_M4,function(_Mb){return E(_Ma);}),_T)));}),_=wMV(_M6,new T2(0,_M8.a,_M9));return _M1;}else{var _Mc=E(_M8.a);if(!_Mc._){var _=wMV(_M6,new T2(0,_M4,_T));return new T(function(){return B(A1(_M5,_S));});}else{var _=wMV(_M6,new T1(1,_Mc.b));return new T1(1,new T2(1,new T(function(){return B(A1(_M5,_S));}),new T2(1,new T(function(){return B(A2(_Mc.a,_M4,_U));}),_T)));}}};},_Md=function(_Me){return E(E(_Me).b);},_Mf=function(_Mg,_Mh,_Mi){var _Mj=new T(function(){return new T1(0,B(_M2(_Mh,_Mi,_U)));}),_Mk=function(_Ml){return new T1(1,new T2(1,new T(function(){return B(A1(_Ml,_S));}),new T2(1,_Mj,_T)));};return new F(function(){return A2(_Md,_Mg,_Mk);});},_Mm=function(_){return new F(function(){return __jsNull();});},_Mn=function(_Mo){var _Mp=B(A1(_Mo,_));return E(_Mp);},_Mq=new T(function(){return B(_Mn(_Mm));}),_Mr=new T(function(){return E(_Mq);}),_Ms=new T(function(){return eval("window.requestAnimationFrame");}),_Mt=new T1(1,_T),_Mu=function(_Mv,_Mw){return function(_){var _Mx=E(_Mv),_My=rMV(_Mx),_Mz=E(_My);if(!_Mz._){var _MA=_Mz.a,_MB=E(_Mz.b);if(!_MB._){var _=wMV(_Mx,_Mt);return new T(function(){return B(A1(_Mw,_MA));});}else{var _MC=E(_MB.a),_=wMV(_Mx,new T2(0,_MC.a,_MB.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Mw,_MA));}),new T2(1,new T(function(){return B(A1(_MC.b,_U));}),_T)));}}else{var _MD=new T(function(){var _ME=function(_MF){var _MG=new T(function(){return B(A1(_Mw,_MF));});return function(_MH){return E(_MG);};};return B(_14(_Mz.a,new T2(1,_ME,_T)));}),_=wMV(_Mx,new T1(1,_MD));return _M1;}};},_MI=function(_MJ,_MK){return new T1(0,B(_Mu(_MJ,_MK)));},_ML=function(_MM,_MN){var _MO=new T(function(){return new T1(0,B(_M2(_MM,_S,_U)));});return function(_){var _MP=__createJSFunc(2,function(_MQ,_){var _MR=B(_1e(_MO,_T,_));return _Mr;}),_MS=__app1(E(_Ms),_MP);return new T(function(){return B(_MI(_MM,_MN));});};},_MT=new T1(1,_T),_MU=function(_MV){var _MW=new T(function(){return B(_MX(_));}),_MY=new T(function(){var _MZ=function(_N0){return E(_MW);},_N1=function(_){var _N2=nMV(_MT);return new T(function(){return new T1(0,B(_ML(_N2,_MZ)));});};return B(A(_Mf,[_13,_MV,_S,function(_N3){return E(new T1(0,_N1));}]));}),_MX=function(_N4){return E(_MY);};return new F(function(){return _MX(_);});},_N5=function(_N6){return E(E(_N6).a);},_N7=function(_N8){return E(E(_N8).d);},_N9=function(_Na){return E(E(_Na).c);},_Nb=function(_Nc){return E(E(_Nc).c);},_Nd=new T1(1,_T),_Ne=function(_Nf){var _Ng=function(_){var _Nh=nMV(_Nd);return new T(function(){return B(A1(_Nf,_Nh));});};return new T1(0,_Ng);},_Ni=function(_Nj,_Nk){var _Nl=new T(function(){return B(_Nb(_Nj));}),_Nm=B(_N5(_Nj)),_Nn=function(_No){var _Np=new T(function(){return B(A1(_Nl,new T(function(){return B(A1(_Nk,_No));})));});return new F(function(){return A3(_N9,_Nm,_Np,new T(function(){return B(A2(_N7,_Nm,_No));}));});};return new F(function(){return A3(_J,_Nm,new T(function(){return B(A2(_Md,_Nj,_Ne));}),_Nn);});},_Nq=function(_Nr,_Ns,_Nt){var _Nu=new T(function(){return B(_N5(_Nr));}),_Nv=new T(function(){return B(A2(_N7,_Nu,_S));}),_Nw=function(_Nx,_Ny){var _Nz=new T(function(){var _NA=new T(function(){return B(A2(_Md,_Nr,function(_NB){return new F(function(){return _MI(_Ny,_NB);});}));});return B(A3(_J,_Nu,_NA,new T(function(){return B(A1(_Nt,_Nx));})));});return new F(function(){return A3(_J,_Nu,_Nz,function(_NC){var _ND=E(_NC);if(!_ND._){return E(_Nv);}else{return new F(function(){return _Nw(_ND.a,_Ny);});}});});};return new F(function(){return _Ni(_Nr,function(_NB){return new F(function(){return _Nw(_Ns,_NB);});});});},_NE=function(_){var _NF=__app2(E(_1j),E(_96),E(_iq));return new F(function(){return _1e(new T(function(){return B(A(_Nq,[_13,_AM,_LV,_MU]));}),_T,_);});},_NG=function(_){return new F(function(){return _NE(_);});};
var hasteMain = function() {B(A(_NG, [0]));};window.onload = hasteMain;