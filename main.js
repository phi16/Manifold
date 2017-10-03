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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=function(_i,_j,_k){return new F(function(){return A1(_i,function(_l){return new F(function(){return A2(_j,_l,_k);});});});},_m=function(_n,_o,_p){var _q=function(_r){var _s=new T(function(){return B(A1(_p,_r));});return new F(function(){return A1(_o,function(_t){return E(_s);});});};return new F(function(){return A1(_n,_q);});},_u=function(_v,_w,_x){var _y=new T(function(){return B(A1(_w,function(_z){return new F(function(){return A1(_x,_z);});}));});return new F(function(){return A1(_v,function(_A){return E(_y);});});},_B=function(_C,_D,_E){var _F=function(_G){var _H=function(_I){return new F(function(){return A1(_E,new T(function(){return B(A1(_G,_I));}));});};return new F(function(){return A1(_D,_H);});};return new F(function(){return A1(_C,_F);});},_J=function(_K,_L){return new F(function(){return A1(_L,_K);});},_M=function(_N,_O,_P){var _Q=new T(function(){return B(A1(_P,_N));});return new F(function(){return A1(_O,function(_R){return E(_Q);});});},_S=function(_T,_U,_V){var _W=function(_X){return new F(function(){return A1(_V,new T(function(){return B(A1(_T,_X));}));});};return new F(function(){return A1(_U,_W);});},_Y=new T2(0,_S,_M),_Z=new T5(0,_Y,_J,_B,_u,_m),_10=function(_11){return E(E(_11).b);},_12=function(_13,_14){return new F(function(){return A3(_10,_15,_13,function(_16){return E(_14);});});},_17=function(_18){return new F(function(){return err(_18);});},_15=new T(function(){return new T5(0,_Z,_h,_12,_J,_17);}),_19=function(_1a){return new T0(2);},_1b=function(_1c){var _1d=new T(function(){return B(A1(_1c,_19));}),_1e=function(_1f){return new T1(1,new T2(1,new T(function(){return B(A1(_1f,_5));}),new T2(1,_1d,_4)));};return E(_1e);},_1g=function(_1h){return E(_1h);},_1i=new T3(0,_15,_1g,_1b),_1j=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1k=new T(function(){return B(err(_1j));}),_1l=0,_1m=new T3(0,_1l,_1l,_1l),_1n=1,_1o=new T3(0,_1l,_1n,_1l),_1p=80,_1q=new T1(0,_1p),_1r=new T(function(){return eval("scrW");}),_1s=new T(function(){return E(_1r)/2-1;}),_1t=new T3(0,_1s,_1p,_1l),_1u=1.5542474911317904e-8,_1v=4.973591971621729e-5,_1w=new T3(0,_1v,_1v,_1u),_1x=new T5(0,_1q,_1t,_1m,_1o,_1w),_1y=60,_1z=new T(function(){return E(_1r)/2-2;}),_1A=new T3(0,_1z,_1y,_1l),_1B=new T5(0,_1q,_1A,_1m,_1o,_1w),_1C=2,_1D=0,_1E=new T(function(){return E(_1r)/2-3;}),_1F=100,_1G=new T3(0,_1E,_1F,_1l),_1H=new T5(0,_1q,_1G,_1m,_1o,_1w),_1I=function(_){var _1J=newArr(3,_1k),_=_1J[0]=_1B,_=_1J[1]=_1x,_=_1J[2]=_1H;return new T4(0,E(_1D),E(_1C),3,_1J);},_1K=function(_1L){var _1M=B(A1(_1L,_));return E(_1M);},_1N=new T(function(){return B(_1K(_1I));}),_1O=function(_1P,_1Q,_){var _1R=B(A1(_1P,_)),_1S=B(A1(_1Q,_));return _1R;},_1T=function(_1U,_1V,_){var _1W=B(A1(_1U,_)),_1X=B(A1(_1V,_));return new T(function(){return B(A1(_1W,_1X));});},_1Y=function(_1Z,_20,_){var _21=B(A1(_20,_));return _1Z;},_22=function(_23,_24,_){var _25=B(A1(_24,_));return new T(function(){return B(A1(_23,_25));});},_26=new T2(0,_22,_1Y),_27=function(_28,_){return _28;},_29=function(_2a,_2b,_){var _2c=B(A1(_2a,_));return new F(function(){return A1(_2b,_);});},_2d=new T5(0,_26,_27,_1T,_29,_1O),_2e=function(_2f){var _2g=E(_2f);return (E(_2g.b)-E(_2g.a)|0)+1|0;},_2h=function(_2i,_2j){var _2k=E(_2i),_2l=E(_2j);return (E(_2k.a)>_2l)?false:_2l<=E(_2k.b);},_2m=function(_2n,_2o){var _2p=jsShowI(_2n);return new F(function(){return _0(fromJSStr(_2p),_2o);});},_2q=41,_2r=40,_2s=function(_2t,_2u,_2v){if(_2u>=0){return new F(function(){return _2m(_2u,_2v);});}else{if(_2t<=6){return new F(function(){return _2m(_2u,_2v);});}else{return new T2(1,_2r,new T(function(){var _2w=jsShowI(_2u);return B(_0(fromJSStr(_2w),new T2(1,_2q,_2v)));}));}}},_2x=function(_2y){return new F(function(){return _2s(0,E(_2y),_4);});},_2z=function(_2A,_2B,_2C){return new F(function(){return _2s(E(_2A),E(_2B),_2C);});},_2D=44,_2E=93,_2F=91,_2G=function(_2H,_2I,_2J){var _2K=E(_2I);if(!_2K._){return new F(function(){return unAppCStr("[]",_2J);});}else{var _2L=new T(function(){var _2M=new T(function(){var _2N=function(_2O){var _2P=E(_2O);if(!_2P._){return E(new T2(1,_2E,_2J));}else{var _2Q=new T(function(){return B(A2(_2H,_2P.a,new T(function(){return B(_2N(_2P.b));})));});return new T2(1,_2D,_2Q);}};return B(_2N(_2K.b));});return B(A2(_2H,_2K.a,_2M));});return new T2(1,_2F,_2L);}},_2R=function(_2S,_2T){return new F(function(){return _2s(0,E(_2S),_2T);});},_2U=function(_2V,_2W){return new F(function(){return _2G(_2R,_2V,_2W);});},_2X=new T3(0,_2z,_2x,_2U),_2Y=0,_2Z=function(_30,_31,_32){return new F(function(){return A1(_30,new T2(1,_2D,new T(function(){return B(A1(_31,_32));})));});},_33=new T(function(){return B(unCStr(": empty list"));}),_34=new T(function(){return B(unCStr("Prelude."));}),_35=function(_36){return new F(function(){return err(B(_0(_34,new T(function(){return B(_0(_36,_33));},1))));});},_37=new T(function(){return B(unCStr("foldr1"));}),_38=new T(function(){return B(_35(_37));}),_39=function(_3a,_3b){var _3c=E(_3b);if(!_3c._){return E(_38);}else{var _3d=_3c.a,_3e=E(_3c.b);if(!_3e._){return E(_3d);}else{return new F(function(){return A2(_3a,_3d,new T(function(){return B(_39(_3a,_3e));}));});}}},_3f=new T(function(){return B(unCStr(" out of range "));}),_3g=new T(function(){return B(unCStr("}.index: Index "));}),_3h=new T(function(){return B(unCStr("Ix{"));}),_3i=new T2(1,_2q,_4),_3j=new T2(1,_2q,_3i),_3k=0,_3l=function(_3m){return E(E(_3m).a);},_3n=function(_3o,_3p,_3q,_3r,_3s){var _3t=new T(function(){var _3u=new T(function(){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){return B(A3(_39,_2Z,new T2(1,new T(function(){return B(A3(_3l,_3q,_3k,_3r));}),new T2(1,new T(function(){return B(A3(_3l,_3q,_3k,_3s));}),_4)),_3j));});return B(_0(_3f,new T2(1,_2r,new T2(1,_2r,_3x))));});return B(A(_3l,[_3q,_2Y,_3p,new T2(1,_2q,_3w)]));});return B(_0(_3g,new T2(1,_2r,_3v)));},1);return B(_0(_3o,_3u));},1);return new F(function(){return err(B(_0(_3h,_3t)));});},_3y=function(_3z,_3A,_3B,_3C,_3D){return new F(function(){return _3n(_3z,_3A,_3D,_3B,_3C);});},_3E=function(_3F,_3G,_3H,_3I){var _3J=E(_3H);return new F(function(){return _3y(_3F,_3G,_3J.a,_3J.b,_3I);});},_3K=function(_3L,_3M,_3N,_3O){return new F(function(){return _3E(_3O,_3N,_3M,_3L);});},_3P=new T(function(){return B(unCStr("Int"));}),_3Q=function(_3R,_3S){return new F(function(){return _3K(_2X,_3S,_3R,_3P);});},_3T=function(_3U,_3V){var _3W=E(_3U),_3X=E(_3W.a),_3Y=E(_3V);if(_3X>_3Y){return new F(function(){return _3Q(_3Y,_3W);});}else{if(_3Y>E(_3W.b)){return new F(function(){return _3Q(_3Y,_3W);});}else{return _3Y-_3X|0;}}},_3Z=function(_40,_41){if(_40<=_41){var _42=function(_43){return new T2(1,_43,new T(function(){if(_43!=_41){return B(_42(_43+1|0));}else{return __Z;}}));};return new F(function(){return _42(_40);});}else{return __Z;}},_44=function(_45,_46){return new F(function(){return _3Z(E(_45),E(_46));});},_47=function(_48){var _49=E(_48);return new F(function(){return _44(_49.a,_49.b);});},_4a=function(_4b){var _4c=E(_4b),_4d=E(_4c.a),_4e=E(_4c.b);return (_4d>_4e)?E(_2Y):(_4e-_4d|0)+1|0;},_4f=function(_4g,_4h){return E(_4g)-E(_4h)|0;},_4i=function(_4j,_4k){return new F(function(){return _4f(_4k,E(_4j).a);});},_4l=function(_4m,_4n){return E(_4m)==E(_4n);},_4o=function(_4p,_4q){return E(_4p)!=E(_4q);},_4r=new T2(0,_4l,_4o),_4s=function(_4t,_4u){var _4v=E(_4t),_4w=E(_4u);return (_4v>_4w)?E(_4v):E(_4w);},_4x=function(_4y,_4z){var _4A=E(_4y),_4B=E(_4z);return (_4A>_4B)?E(_4B):E(_4A);},_4C=function(_4D,_4E){return (_4D>=_4E)?(_4D!=_4E)?2:1:0;},_4F=function(_4G,_4H){return new F(function(){return _4C(E(_4G),E(_4H));});},_4I=function(_4J,_4K){return E(_4J)>=E(_4K);},_4L=function(_4M,_4N){return E(_4M)>E(_4N);},_4O=function(_4P,_4Q){return E(_4P)<=E(_4Q);},_4R=function(_4S,_4T){return E(_4S)<E(_4T);},_4U={_:0,a:_4r,b:_4F,c:_4R,d:_4O,e:_4L,f:_4I,g:_4s,h:_4x},_4V={_:0,a:_4U,b:_47,c:_3T,d:_4i,e:_2h,f:_4a,g:_2e},_4W=function(_4X){return E(E(_4X).a);},_4Y=function(_4Z,_50){return new T2(1,_4Z,_50);},_51=function(_52){return E(E(_52).c);},_53=function(_54,_55){var _56=E(_55);return new T2(0,_56.a,_56.b);},_57=function(_58){return E(E(_58).a);},_59=new T(function(){return B(unCStr("Negative range size"));}),_5a=new T(function(){return B(err(_59));}),_5b=function(_5c){return E(E(_5c).f);},_5d=function(_5e,_5f,_5g){var _5h=E(_5f),_5i=_5h.a,_5j=_5h.b,_5k=function(_){var _5l=B(A2(_5b,_5e,_5h));if(_5l>=0){var _5m=newArr(_5l,_1k),_5n=_5m,_5o=E(_5l);if(!_5o){return new T(function(){return new T4(0,E(_5i),E(_5j),0,_5n);});}else{var _5p=function(_5q,_5r,_){while(1){var _5s=E(_5q);if(!_5s._){return E(_);}else{var _=_5n[_5r]=_5s.a;if(_5r!=(_5o-1|0)){var _5t=_5r+1|0;_5q=_5s.b;_5r=_5t;continue;}else{return E(_);}}}},_=B(_5p(_5g,0,_));return new T(function(){return new T4(0,E(_5i),E(_5j),_5o,_5n);});}}else{return E(_5a);}};return new F(function(){return _1K(_5k);});},_5u=function(_5v){return E(E(_5v).b);},_5w=function(_5x,_5y,_5z,_5A){var _5B=new T(function(){var _5C=E(_5A),_5D=_5C.c-1|0,_5E=new T(function(){return B(A2(_5u,_5y,_4));});if(0<=_5D){var _5F=new T(function(){return B(_4W(_5y));}),_5G=function(_5H){var _5I=new T(function(){var _5J=new T(function(){return B(A1(_5z,new T(function(){return E(_5C.d[_5H]);})));});return B(A3(_57,_5F,_4Y,_5J));});return new F(function(){return A3(_51,_5y,_5I,new T(function(){if(_5H!=_5D){return B(_5G(_5H+1|0));}else{return E(_5E);}}));});};return B(_5G(0));}else{return E(_5E);}}),_5K=new T(function(){return B(_53(_5x,_5A));});return new F(function(){return A3(_57,B(_4W(_5y)),function(_5L){return new F(function(){return _5d(_5x,_5K,_5L);});},_5B);});},_5M=function(_){return _5;},_5N=new T(function(){return eval("drawCircle");}),_5O=new T(function(){return eval("drawRect");}),_5P=function(_5Q,_5R,_5S,_5T,_){var _5U=E(_5Q);if(!_5U._){var _5V=__app4(E(_5N),_5R,_5S,_5T,E(_5U.a));return new F(function(){return _5M(_);});}else{var _5W=__app5(E(_5O),_5R,_5S,_5T,E(_5U.a),E(_5U.b));return new F(function(){return _5M(_);});}},_5X=new T(function(){return B(_3Z(-1,1));}),_5Y=new T(function(){return eval("scrH");}),_5Z=function(_60,_){var _61=function(_62,_){var _63=E(_62);if(!_63._){return _4;}else{var _64=_63.b,_65=E(_5X);if(!_65._){var _66=B(_61(_64,_));return new T2(1,_4,_66);}else{var _67=E(_60),_68=_67.a,_69=E(_67.b),_6a=E(_69.a),_6b=E(_63.a),_6c=E(_1r),_6d=E(_69.b),_6e=E(_5Y),_6f=E(_69.c),_6g=B(_5P(_68,_6a+_6b*_6c,_6d+E(_65.a)*_6e,_6f,_)),_6h=function(_6i,_){var _6j=E(_6i);if(!_6j._){return _4;}else{var _6k=B(_5P(_68,_6a+_6b*_6c,_6d+E(_6j.a)*_6e,_6f,_)),_6l=B(_6h(_6j.b,_));return new T2(1,_6k,_6l);}},_6m=B(_6h(_65.b,_)),_6n=B(_61(_64,_));return new T2(1,new T2(1,_6g,_6m),_6n);}}},_6o=B(_61(_5X,_));return _5;},_6p=function(_6q){return E(_6q);},_6r=function(_6s){return E(_6s);},_6t=function(_6u,_6v){return E(_6v);},_6w=function(_6x,_6y){return E(_6x);},_6z=function(_6A){return E(_6A);},_6B=new T2(0,_6z,_6w),_6C=function(_6D,_6E){return E(_6D);},_6F=new T5(0,_6B,_6r,_6p,_6t,_6C),_6G=function(_6H,_6I,_){while(1){var _6J=B((function(_6K,_6L,_){var _6M=E(_6K);if(!_6M._){return new T2(0,_5,_6L);}else{var _6N=B(A2(_6M.a,_6L,_));_6H=_6M.b;_6I=new T(function(){return E(E(_6N).b);});return __continue;}})(_6H,_6I,_));if(_6J!=__continue){return _6J;}}},_6O=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_6P=new T(function(){return B(err(_6O));}),_6Q=1,_6R=-1,_6S=function(_6T,_6U){return E(_6T)-E(_6U);},_6V=function(_6W,_6X){var _6Y=E(_6W),_6Z=E(_6X);return new T2(0,new T(function(){return B(_6S(_6Y.a,_6Z.a));}),new T(function(){return B(_6S(_6Y.b,_6Z.b));}));},_70=function(_71,_72){return new F(function(){return _6V(_72,_71);});},_73=new T(function(){return B(unCStr("!!: negative index"));}),_74=new T(function(){return B(_0(_34,_73));}),_75=new T(function(){return B(err(_74));}),_76=new T(function(){return B(unCStr("!!: index too large"));}),_77=new T(function(){return B(_0(_34,_76));}),_78=new T(function(){return B(err(_77));}),_79=function(_7a,_7b){while(1){var _7c=E(_7a);if(!_7c._){return E(_78);}else{var _7d=E(_7b);if(!_7d){return E(_7c.a);}else{_7a=_7c.b;_7b=_7d-1|0;continue;}}}},_7e=function(_7f,_7g){if(_7g>=0){return new F(function(){return _79(_7f,_7g);});}else{return E(_75);}},_7h=__Z,_7i=function(_7j,_7k,_7l){while(1){var _7m=E(_7j);if(!_7m._){return new T2(0,_7k,_7l);}else{var _7n=_7m.b,_7o=E(_7m.a),_7p=_7o.a,_7q=_7o.b,_7r=E(_7k);if(!_7r._){if(!E(_7p)._){var _7s=E(_7l),_7t=E(_7q);if(_7s>_7t){_7j=_7n;_7k=_7h;_7l=_7t;continue;}else{_7j=_7n;_7k=_7h;_7l=_7s;continue;}}else{_7j=_7n;_7k=_7h;continue;}}else{var _7u=E(_7p);if(!_7u._){_7j=_7n;_7k=_7h;_7l=_7q;continue;}else{var _7v=E(_7r.a),_7w=E(_7u.a);if(_7v>=_7w){if(_7v!=_7w){_7j=_7n;_7k=_7u;_7l=_7q;continue;}else{var _7x=E(_7l),_7y=E(_7q);if(_7x>_7y){_7j=_7n;_7k=_7u;_7l=_7y;continue;}else{_7j=_7n;_7k=_7r;_7l=_7x;continue;}}}else{_7j=_7n;_7k=_7r;continue;}}}}}},_7z=function(_7A,_7B,_7C){while(1){var _7D=E(_7A);if(!_7D._){return new T2(0,_7B,_7C);}else{var _7E=_7D.b,_7F=E(_7D.a),_7G=_7F.a,_7H=_7F.b,_7I=E(_7B);if(!_7I._){var _7J=E(_7G);if(!_7J._){var _7K=E(_7C),_7L=E(_7H);if(_7K>_7L){_7A=_7E;_7B=_7h;_7C=_7K;continue;}else{_7A=_7E;_7B=_7h;_7C=_7L;continue;}}else{_7A=_7E;_7B=_7J;_7C=_7H;continue;}}else{var _7M=E(_7G);if(!_7M._){_7A=_7E;_7B=_7I;continue;}else{var _7N=E(_7I.a),_7O=E(_7M.a);if(_7N>=_7O){if(_7N!=_7O){_7A=_7E;_7B=_7I;continue;}else{var _7P=E(_7C),_7Q=E(_7H);if(_7P>_7Q){_7A=_7E;_7B=_7I;_7C=_7P;continue;}else{_7A=_7E;_7B=_7M;_7C=_7Q;continue;}}}else{_7A=_7E;_7B=_7M;_7C=_7H;continue;}}}}}},_7R=function(_7S,_7T,_7U){while(1){var _7V=E(_7S);if(!_7V._){return new T2(0,_7T,_7U);}else{var _7W=_7V.b,_7X=E(_7V.a),_7Y=_7X.a,_7Z=_7X.b,_80=E(_7T);if(!_80._){var _81=E(_7Y);if(!_81._){var _82=E(_7U),_83=E(_7Z);if(_82>_83){_7S=_7W;_7T=_7h;_7U=_82;continue;}else{_7S=_7W;_7T=_7h;_7U=_83;continue;}}else{_7S=_7W;_7T=_81;_7U=_7Z;continue;}}else{var _84=E(_7Y);if(!_84._){_7S=_7W;_7T=_80;continue;}else{var _85=E(_80.a),_86=E(_84.a);if(_85>=_86){if(_85!=_86){_7S=_7W;_7T=_80;continue;}else{var _87=E(_7U),_88=E(_7Z);if(_87>_88){_7S=_7W;_7T=_80;_7U=_87;continue;}else{_7S=_7W;_7T=_84;_7U=_88;continue;}}}else{_7S=_7W;_7T=_84;_7U=_7Z;continue;}}}}}},_89=function(_8a,_8b){while(1){var _8c=B((function(_8d,_8e){var _8f=E(_8e);if(!_8f._){return __Z;}else{var _8g=_8f.a,_8h=_8f.b;if(!B(A1(_8d,_8g))){var _8i=_8d;_8a=_8i;_8b=_8h;return __continue;}else{return new T2(1,_8g,new T(function(){return B(_89(_8d,_8h));}));}}})(_8a,_8b));if(_8c!=__continue){return _8c;}}},_8j=function(_8k){return E(E(_8k).a);},_8l=function(_8m,_8n){var _8o=E(_8m);if(!_8o._){var _8p=E(_8n);return __Z;}else{var _8q=E(_8n);return (_8q._==0)?__Z:(E(_8o.a)>E(_8q.a))?E(_8q):E(_8o);}},_8r=function(_8s,_8t){while(1){var _8u=E(_8s);if(!_8u._){return E(_8t);}else{var _8v=B(_8l(_8t,_8u.a));_8s=_8u.b;_8t=_8v;continue;}}},_8w=function(_8x,_8y){while(1){var _8z=E(_8x);if(!_8z._){return E(_8y);}else{var _8A=B(_8l(_8y,_8z.a));_8x=_8z.b;_8y=_8A;continue;}}},_8B=function(_8C){return (E(_8C)._==0)?false:true;},_8D=new T(function(){return B(unCStr("minimum"));}),_8E=new T(function(){return B(_35(_8D));}),_8F=function(_8G,_8H){var _8I=E(_8G);if(!_8I._){return __Z;}else{var _8J=E(_8H);return (_8J._==0)?__Z:new T2(1,new T2(0,new T(function(){var _8K=B(_89(_8B,_8I.a));if(!_8K._){return E(_8E);}else{return B(_8w(_8K.b,_8K.a));}}),_8J.a),new T(function(){return B(_8F(_8I.b,_8J.b));}));}},_8L=function(_8M,_8N){while(1){var _8O=E(_8M);if(!_8O._){return E(_8N);}else{var _8P=B(_8l(_8N,_8O.a));_8M=_8O.b;_8N=_8P;continue;}}},_8Q=function(_8R,_8S){while(1){var _8T=E(_8R);if(!_8T._){return E(_8S);}else{var _8U=B(_8l(_8S,_8T.a));_8R=_8T.b;_8S=_8U;continue;}}},_8V=function(_8W,_8X){var _8Y=E(_8W);if(!_8Y._){return __Z;}else{var _8Z=E(_8X);return (_8Z._==0)?__Z:new T2(1,new T2(0,new T(function(){var _90=B(_89(_8B,_8Y.a));if(!_90._){return E(_8E);}else{return B(_8Q(_90.b,_90.a));}}),_8Z.a),new T(function(){return B(_8V(_8Y.b,_8Z.b));}));}},_91=function(_92){while(1){var _93=E(_92);if(!_93._){return true;}else{if(!E(_93.a)._){_92=_93.b;continue;}else{return false;}}}},_94=function(_95){while(1){var _96=E(_95);if(!_96._){return false;}else{if(!B(_91(_96.a))){_95=_96.b;continue;}else{return true;}}}},_97=function(_98,_99){var _9a=E(_98),_9b=E(_9a.a),_9c=E(_9b.a),_9d=E(_9b.b),_9e=E(_9a.b),_9f=E(_99),_9g= -(E(_9e.b)-_9d),_9h=E(_9e.a)-_9c,_9i=(_9g*E(_9f.a)+_9h*E(_9f.b)-(_9g*_9c+_9h*_9d))/Math.sqrt(_9g*_9g+_9h*_9h);return (_9i<0)?new T1(1,_9i):__Z;},_9j=0,_9k=1,_9l=new T(function(){return B(unCStr("maximum"));}),_9m=new T(function(){return B(_35(_9l));}),_9n=new T(function(){return B(_35(_8D));}),_9o=new T(function(){return B(_3Z(0,3));}),_9p=new T(function(){return B(unCStr("base"));}),_9q=new T(function(){return B(unCStr("Control.Exception.Base"));}),_9r=new T(function(){return B(unCStr("PatternMatchFail"));}),_9s=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9p,_9q,_9r),_9t=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9s,_4,_4),_9u=function(_9v){return E(_9t);},_9w=function(_9x){return E(E(_9x).a);},_9y=function(_9z,_9A,_9B){var _9C=B(A1(_9z,_)),_9D=B(A1(_9A,_)),_9E=hs_eqWord64(_9C.a,_9D.a);if(!_9E){return __Z;}else{var _9F=hs_eqWord64(_9C.b,_9D.b);return (!_9F)?__Z:new T1(1,_9B);}},_9G=function(_9H){var _9I=E(_9H);return new F(function(){return _9y(B(_9w(_9I.a)),_9u,_9I.b);});},_9J=function(_9K){return E(E(_9K).a);},_9L=function(_9M){return new T2(0,_9N,_9M);},_9O=function(_9P,_9Q){return new F(function(){return _0(E(_9P).a,_9Q);});},_9R=function(_9S,_9T){return new F(function(){return _2G(_9O,_9S,_9T);});},_9U=function(_9V,_9W,_9X){return new F(function(){return _0(E(_9W).a,_9X);});},_9Y=new T3(0,_9U,_9J,_9R),_9N=new T(function(){return new T5(0,_9u,_9Y,_9L,_9G,_9J);}),_9Z=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_a0=function(_a1){return E(E(_a1).c);},_a2=function(_a3,_a4){return new F(function(){return die(new T(function(){return B(A2(_a0,_a4,_a3));}));});},_a5=function(_a6,_a7){return new F(function(){return _a2(_a6,_a7);});},_a8=function(_a9,_aa){var _ab=E(_aa);if(!_ab._){return new T2(0,_4,_4);}else{var _ac=_ab.a;if(!B(A1(_a9,_ac))){return new T2(0,_4,_ab);}else{var _ad=new T(function(){var _ae=B(_a8(_a9,_ab.b));return new T2(0,_ae.a,_ae.b);});return new T2(0,new T2(1,_ac,new T(function(){return E(E(_ad).a);})),new T(function(){return E(E(_ad).b);}));}}},_af=32,_ag=new T(function(){return B(unCStr("\n"));}),_ah=function(_ai){return (E(_ai)==124)?false:true;},_aj=function(_ak,_al){var _am=B(_a8(_ah,B(unCStr(_ak)))),_an=_am.a,_ao=function(_ap,_aq){var _ar=new T(function(){var _as=new T(function(){return B(_0(_al,new T(function(){return B(_0(_aq,_ag));},1)));});return B(unAppCStr(": ",_as));},1);return new F(function(){return _0(_ap,_ar);});},_at=E(_am.b);if(!_at._){return new F(function(){return _ao(_an,_4);});}else{if(E(_at.a)==124){return new F(function(){return _ao(_an,new T2(1,_af,_at.b));});}else{return new F(function(){return _ao(_an,_4);});}}},_au=function(_av){return new F(function(){return _a5(new T1(0,new T(function(){return B(_aj(_av,_9Z));})),_9N);});},_aw=new T(function(){return B(_au("Lib\\Physics.hs:96:13-61|(Just d\', f\')"));}),_ax=new T2(0,_1n,_1l),_ay=function(_az){return  -E(_az);},_aA=function(_aB){var _aC=E(_aB);return new T2(0,new T(function(){return B(_ay(_aC.a));}),new T(function(){return B(_ay(_aC.b));}));},_aD=function(_aE){var _aF=E(_aE);return new T5(0,_aF.b,_aF.a,new T(function(){return B(_aA(_aF.d));}),new T(function(){return B(_aA(_aF.c));}),_aF.e);},_aG=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_aH=function(_aI){return new F(function(){return _a5(new T1(0,new T(function(){return B(_aj(_aI,_aG));})),_9N);});},_aJ=new T(function(){return B(_aH("Lib\\Physics.hs:(58,26)-(61,63)|multi-way if"));}),_aK=function(_aL,_aM){var _aN=E(_aM);return (_aN._==0)?__Z:new T2(1,new T(function(){return B(A1(_aL,_aN.a));}),new T(function(){return B(_aK(_aL,_aN.b));}));},_aO=function(_aP,_aQ){var _aR=_aP%_aQ;if(_aP<=0){if(_aP>=0){return E(_aR);}else{if(_aQ<=0){return E(_aR);}else{var _aS=E(_aR);return (_aS==0)?0:_aS+_aQ|0;}}}else{if(_aQ>=0){if(_aP>=0){return E(_aR);}else{if(_aQ<=0){return E(_aR);}else{var _aT=E(_aR);return (_aT==0)?0:_aT+_aQ|0;}}}else{var _aU=E(_aR);return (_aU==0)?0:_aU+_aQ|0;}}},_aV=function(_aW){return E(E(_aW).b);},_aX=new T(function(){return B(unCStr("tail"));}),_aY=new T(function(){return B(_35(_aX));}),_aZ=-1,_b0=new T2(0,_aZ,_aZ),_b1=new T2(0,_aZ,_9k),_b2=new T2(0,_9k,_9k),_b3=new T2(0,_9k,_aZ),_b4=new T2(1,_b0,_4),_b5=new T2(1,_b3,_b4),_b6=new T2(1,_b2,_b5),_b7=new T2(1,_b1,_b6),_b8=new T2(1,_b0,_b7),_b9=function(_ba,_bb){var _bc=E(_ba);if(!_bc._){return __Z;}else{var _bd=E(_bb);return (_bd._==0)?__Z:new T2(1,new T2(0,_bc.a,_bd.a),new T(function(){return B(_b9(_bc.b,_bd.b));}));}},_be=function(_bf,_bg,_bh,_bi){var _bj=E(_bg);if(!_bj._){return __Z;}else{var _bk=E(_bh);if(!_bk._){return __Z;}else{var _bl=E(_bi);return (_bl._==0)?__Z:new T2(1,new T(function(){return B(A3(_bf,_bj.a,_bk.a,_bl.a));}),new T(function(){return B(_be(_bf,_bj.b,_bk.b,_bl.b));}));}}},_bm=function(_bn,_bo,_bp,_bq){var _br=E(_bn);if(!_br._){var _bs=_br.a,_bt=E(_bp);if(!_bt._){var _bu=E(_bo),_bv=E(_bq),_bw=E(_bs),_bx=E(_bt.a),_by=E(_bu.a)-E(_bv.a),_bz=E(_bu.b)-E(_bv.b),_bA=Math.sqrt(_by*_by+_bz*_bz),_bB=_bw+_bx;if(_bA<=_bB){var _bC=new T(function(){var _bD=E(_bA);if(!_bD){return E(_ax);}else{return new T2(0,new T(function(){return _by/_bD;}),new T(function(){return _bz/_bD;}));}}),_bE=new T(function(){var _bF=E(_bC);return new T2(0,new T(function(){return E(_bF.a)*_bx;}),new T(function(){return E(_bF.b)*_bx;}));}),_bG=new T(function(){var _bH=E(_bC);return new T2(0,new T(function(){return  -(E(_bH.a)*_bw);}),new T(function(){return  -(E(_bH.b)*_bw);}));});return new T2(1,new T5(0,_bG,_bE,_bC,_bC,_bB-_bA),_4);}else{return __Z;}}else{var _bI=E(_bo),_bJ=E(_bI.a),_bK=E(_bq),_bL=E(_bK.a),_bM=E(_bK.c),_bN=E(_bI.b),_bO=E(_bK.b),_bP=E(_bt.a),_bQ=_bJ-_bL,_bR= -_bM,_bS=_bN-_bO,_bT=_bQ*Math.cos(_bR)-_bS*Math.sin(_bR),_bU= -(_bP/2),_bV=_bP/2,_bW=function(_bX){var _bY=E(_bt.b),_bZ=_bQ*Math.sin(_bR)+_bS*Math.cos(_bR),_c0= -(_bY/2),_c1=_bY/2,_c2=function(_c3){var _c4=E(_bs),_c5=_bT-_bX,_c6=_bZ-_c3,_c7=Math.sqrt(_c5*_c5+_c6*_c6);if(_c7<=_c4){var _c8=new T(function(){var _c9=function(_ca){if(_ca>0){var _cb=function(_cc){if(_cc>0){return (_ca>_cc)?(_ca<_cc)?E(_aJ):new T2(0,new T2(0,_9j,new T(function(){if(_c6<=0){if(_c6>=0){return _c6;}else{return E(_6R);}}else{return E(_6Q);}})),_c4+_cc):new T2(0,new T2(0,new T(function(){if(_c5<=0){if(_c5>=0){return _c5;}else{return E(_6R);}}else{return E(_6Q);}}),_9j),_c4+_ca);}else{var _cd=new T(function(){var _ce=E(_c7);if(!_ce){return E(_ax);}else{return new T2(0,new T(function(){return _c5/_ce;}),new T(function(){return _c6/_ce;}));}});return new T2(0,_cd,_c4-_c7);}},_cf=E(_bZ);if(!_cf){return new F(function(){return _cb(_bY/2);});}else{if(_cf<=0){return new F(function(){return _cb(_bY/2+_cf);});}else{return new F(function(){return _cb(_bY/2-_cf);});}}}else{var _cg=new T(function(){var _ch=E(_c7);if(!_ch){return E(_ax);}else{return new T2(0,new T(function(){return _c5/_ch;}),new T(function(){return _c6/_ch;}));}});return new T2(0,_cg,_c4-_c7);}},_ci=E(_bT);if(!_ci){var _cj=B(_c9(_bP/2));return new T2(0,_cj.a,_cj.b);}else{if(_ci<=0){var _ck=B(_c9(_bP/2+_ci));return new T2(0,_ck.a,_ck.b);}else{var _cl=B(_c9(_bP/2-_ci));return new T2(0,_cl.a,_cl.b);}}}),_cm=new T(function(){return E(E(_c8).b);}),_cn=new T(function(){var _co=E(E(_c8).a),_cp=_co.a,_cq=_co.b;return new T2(0,new T(function(){return E(_cp)*Math.cos(_bM)-E(_cq)*Math.sin(_bM);}),new T(function(){return E(_cp)*Math.sin(_bM)+E(_cq)*Math.cos(_bM);}));}),_cr=new T(function(){var _cs=E(_cn);return new T2(0,new T(function(){return _bJ-E(_cs.a)*_c4;}),new T(function(){return _bN-E(_cs.b)*_c4;}));}),_ct=new T(function(){var _cu=E(_cr),_cv=E(_cn);return new T2(0,new T(function(){return E(_cu.a)+E(_cv.a)*E(_cm)-_bL;}),new T(function(){return E(_cu.b)+E(_cv.b)*E(_cm)-_bO;}));}),_cw=new T(function(){var _cx=E(_cr);return new T2(0,new T(function(){return E(_cx.a)-_bJ;}),new T(function(){return E(_cx.b)-_bN;}));});return new T2(1,new T5(0,_cw,_ct,_cn,_cn,_cm),_4);}else{return __Z;}};if(_c0>_bZ){if(_c1>_c0){return new F(function(){return _c2(_c0);});}else{return new F(function(){return _c2(_c1);});}}else{if(_c1>_bZ){return new F(function(){return _c2(_bZ);});}else{return new F(function(){return _c2(_c1);});}}};if(_bU>_bT){if(_bV>_bU){return new F(function(){return _bW(_bU);});}else{return new F(function(){return _bW(_bV);});}}else{if(_bV>_bT){return new F(function(){return _bW(_bT);});}else{return new F(function(){return _bW(_bV);});}}}}else{var _cy=E(_bp);if(!_cy._){return new F(function(){return _aK(_aD,B(_bm(_cy,_bq,_br,_bo)));});}else{var _cz=new T(function(){var _cA=function(_cB){var _cC=E(_cB),_cD=new T(function(){return E(E(_bq).c);}),_cE=new T(function(){return E(_cC.a)*E(_cy.a)*0.5;}),_cF=new T(function(){return E(_cC.b)*E(_cy.b)*0.5;});return new T2(0,new T(function(){var _cG=E(_cD);return E(E(_bq).a)+(E(_cE)*Math.cos(_cG)-E(_cF)*Math.sin(_cG));}),new T(function(){var _cH=E(_cD);return E(E(_bq).b)+E(_cE)*Math.sin(_cH)+E(_cF)*Math.cos(_cH);}));};return B(_aK(_cA,_b8));}),_cI=new T(function(){return B(_b9(_cz,new T(function(){var _cJ=E(_cz);if(!_cJ._){return E(_aY);}else{return E(_cJ.b);}},1)));}),_cK=function(_cL){var _cM=E(_cL),_cN=new T(function(){return E(E(_bo).c);}),_cO=new T(function(){return E(_cM.a)*E(_br.a)*0.5;}),_cP=new T(function(){return E(_cM.b)*E(_br.b)*0.5;});return new T2(0,new T(function(){var _cQ=E(_cN);return E(E(_bo).a)+(E(_cO)*Math.cos(_cQ)-E(_cP)*Math.sin(_cQ));}),new T(function(){var _cR=E(_cN);return E(E(_bo).b)+E(_cO)*Math.sin(_cR)+E(_cP)*Math.cos(_cR);}));},_cS=B(_aK(_cK,_b8)),_cT=new T(function(){var _cU=function(_cV){var _cW=E(_cS);if(!_cW._){return E(_aY);}else{return new F(function(){return _aK(function(_cX){return new F(function(){return _97(_cV,_cX);});},_cW.b);});}};return B(_aK(_cU,_cI));}),_cY=B(_b9(_cS,new T(function(){var _cZ=E(_cS);if(!_cZ._){return E(_aY);}else{return E(_cZ.b);}},1))),_d0=function(_d1){var _d2=E(_cz);if(!_d2._){return E(_aY);}else{return new F(function(){return _aK(function(_cX){return new F(function(){return _97(_d1,_cX);});},_d2.b);});}},_d3=B(_aK(_d0,_cY));if(!B(_94(B(_0(_d3,_cT))))){var _d4=B(_8V(_d3,_9o));if(!_d4._){return E(_9m);}else{var _d5=E(_d4.a),_d6=E(B(_7R(_d4.b,_d5.a,_d5.b)).b),_d7=B(_89(_8B,B(_7e(_d3,_d6))));if(!_d7._){return E(_8E);}else{var _d8=B(_8F(_cT,_9o));if(!_d8._){return E(_9m);}else{var _d9=E(_d8.a),_da=E(B(_7z(_d8.b,_d9.a,_d9.b)).b),_db=B(_89(_8B,B(_7e(_cT,_da))));if(!_db._){return E(_8E);}else{var _dc=B(_8r(_db.b,_db.a)),_dd=B(_8L(_d7.b,_d7.a)),_de=E(_dd);if(!_de._){var _df=E(_dc),_dg=false;}else{var _dh=E(_dc);if(!_dh._){var _di=true;}else{var _di=E(_de.a)>E(_dh.a);}var _dg=_di;}var _dj=function(_dk,_dl){var _dm=function(_dn,_do,_dp,_dq){var _dr=E(_dp),_ds=E(_dq),_dt=E(_dr.a),_du=E(_dr.b),_dv=E(_ds.a),_dw=E(_ds.b),_dx=_dv-_dt,_dy=_dw-_du,_dz=Math.sqrt(_dx*_dx+_dy*_dy);if(!_dz){var _dA=E(_dn),_dB=E(_dA.a),_dC=E(_dA.b),_dD=E(_do),_dE= -(E(_dD.b)-_dC),_dF=E(_dD.a)-_dB,_dG=function(_dH,_dI,_dJ){var _dK=E(_dI),_dL=E(_dJ),_dM=_dt+_du*0,_dN=_dv+_dw*0-_dM,_dO=new T(function(){var _dP=E(E(_dH).a);return (E(_dP.a)+E(_dP.b)*0-_dM)/_dN;}),_dQ=new T(function(){var _dR=E(E(_dH).b);return (E(_dR.a)+E(_dR.b)*0-_dM)/_dN;}),_dS=function(_dT){var _dU=new T(function(){var _dV=E(_dT);if(0>_dV){return E(_9j);}else{if(1>_dV){return E(_dV);}else{return E(_9k);}}}),_dW=new T(function(){return E(_dQ)-E(_dU);}),_dX=new T(function(){return E(_dU)-E(_dO);});return new T2(0,new T(function(){var _dY=E(_dW),_dZ=E(_dX);return (E(_dK.a)*_dY+E(_dL.a)*_dZ)/(_dY+_dZ);}),new T(function(){var _e0=E(_dW),_e1=E(_dX);return (E(_dK.b)*_e0+E(_dL.b)*_e1)/(_e0+_e1);}));},_e2=B(_dS(_dO)),_e3=E(_e2.a),_e4=E(_e2.b),_e5=new T(function(){var _e6=B(_dS(_dQ)),_e7=E(_e6.a),_e8=E(_e6.b),_e9=(_dE*_e7+_dF*_e8-(_dE*_dB+_dF*_dC))/Math.sqrt(_dE*_dE+_dF*_dF);if(_e9<0){return new T2(1,new T2(0,new T2(0,_e7,_e8), -_e9),_4);}else{return __Z;}}),_ea=(_dE*_e3+_dF*_e4-(_dE*_dB+_dF*_dC))/Math.sqrt(_dE*_dE+_dF*_dF);if(_ea<0){var _eb=new T2(1,new T2(0,new T2(0,_e3,_e4), -_ea),_e5);}else{var _eb=E(_e5);}var _ec=new T(function(){return B(_aK(_8j,_eb));}),_ed= -0,_ee=new T(function(){var _ef=function(_eg){var _eh=E(_eg),_ei=_eh.b,_ej=E(_eh.a);return new T2(0,new T(function(){return E(_ej.a)+_ed*E(_ei);}),new T(function(){return E(_ej.b)+E(_ei);}));};return B(_aK(_ef,_eb));}),_ek=new T(function(){if(!E(_dg)){var _el=new T(function(){return E(E(_bq).b);}),_em=new T(function(){return E(E(_bq).a);});return B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_em,_el),_cX);});},_ee));}else{var _en=new T(function(){return E(E(_bq).b);}),_eo=new T(function(){return E(E(_bq).a);});return B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_eo,_en),_cX);});},_ec));}}),_ep=new T(function(){if(!E(_dg)){return new T2(0,_ed,1);}else{return new T2(0, -_ed,-1);}}),_eq=function(_er,_es,_et){return new T5(0,_er,_es,_ep,_ep,_et);};if(!E(_dg)){var _eu=new T(function(){return E(E(_bo).b);}),_ev=new T(function(){return E(E(_bo).a);});return new F(function(){return _be(_eq,B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_ev,_eu),_cX);});},_ec)),_ek,new T(function(){return B(_aK(_aV,_eb));},1));});}else{var _ew=new T(function(){return E(E(_bo).b);}),_ex=new T(function(){return E(E(_bo).a);});return new F(function(){return _be(_eq,B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_ex,_ew),_cX);});},_ee)),_ek,new T(function(){return B(_aK(_aV,_eb));},1));});}},_ey=function(_ez){var _eA=function(_eB,_eC){while(1){var _eD=B((function(_eE,_eF){var _eG=E(_eE);if(!_eG._){return __Z;}else{var _eH=_eG.b,_eI=E(_eF);if(!_eI._){return __Z;}else{var _eJ=_eI.b,_eK=E(_eG.a),_eL=(_dE*E(_eK.a)+_dF*E(_eK.b)-(_dE*_dB+_dF*_dC))/Math.sqrt(_dE*_dE+_dF*_dF);if(_eL<0){return new T2(1,new T2(0,new T1(1,_eL),_eI.a),new T(function(){return B(_eA(_eH,_eJ));}));}else{_eB=_eH;_eC=_eJ;return __continue;}}}})(_eB,_eC));if(_eD!=__continue){return _eD;}}};return new F(function(){return _eA(_ez,_9o);});},_eM=function(_eN){var _eO=B(_7e(_dl,_eN)),_eP=E(_eO.a),_eQ=E(_eO.b),_eR=E(_eP.a)-E(_eQ.a),_eS=E(_eP.b)-E(_eQ.b),_eT=function(_eU,_eV){var _eW=function(_eX){var _eY=B(_7e(_dl,B(_aO(_eN+1|0,4)))),_eZ=E(_eY.b),_f0=E(_eY.a),_f1=E(_eZ.a)-E(_f0.a),_f2=E(_eZ.b)-E(_f0.b),_f3=Math.sqrt(_f1*_f1+_f2*_f2);if(!_f3){return (_eX<=1)?new T3(0,_eY,_f0,_eZ):new T3(0,new T2(0,_eQ,_eP),_eQ,_eP);}else{var _f4=_f1/_f3+0*(_f2/_f3);return (_f4==0)?(_eX<=0)?new T3(0,_eY,_f0,_eZ):new T3(0,new T2(0,_eQ,_eP),_eQ,_eP):(_f4<=0)?(_eX<= -_f4)?new T3(0,_eY,_f0,_eZ):new T3(0,new T2(0,_eQ,_eP),_eQ,_eP):(_eX<=_f4)?new T3(0,_eY,_f0,_eZ):new T3(0,new T2(0,_eQ,_eP),_eQ,_eP);}},_f5=_eU+0*_eV;if(!_f5){return new F(function(){return _eW(0);});}else{if(_f5<=0){return new F(function(){return _eW( -_f5);});}else{return new F(function(){return _eW(_f5);});}}},_f6=Math.sqrt(_eR*_eR+_eS*_eS);if(!_f6){return new F(function(){return _eT(1,0);});}else{return new F(function(){return _eT(_eR/_f6,_eS/_f6);});}};if(!E(_dg)){var _f7=E(_cS);if(!_f7._){return E(_aY);}else{var _f8=B(_ey(_f7.b));if(!_f8._){return E(_9n);}else{var _f9=E(_f8.a),_fa=B(_eM(E(B(_7i(_f8.b,_f9.a,_f9.b)).b)));return new F(function(){return _dG(_fa.a,_fa.b,_fa.c);});}}}else{var _fb=E(_cz);if(!_fb._){return E(_aY);}else{var _fc=B(_ey(_fb.b));if(!_fc._){return E(_9n);}else{var _fd=E(_fc.a),_fe=B(_eM(E(B(_7i(_fc.b,_fd.a,_fd.b)).b)));return new F(function(){return _dG(_fe.a,_fe.b,_fe.c);});}}}}else{var _ff=_dx/_dz,_fg=_dy/_dz,_fh=E(_dn),_fi=E(_fh.a),_fj=E(_fh.b),_fk=E(_do),_fl= -(E(_fk.b)-_fj),_fm=E(_fk.a)-_fi,_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=_dt*_ff+_du*_fg,_fu=_dv*_ff+_dw*_fg-_ft,_fv=new T(function(){var _fw=E(E(_fo).a);return (E(_fw.a)*_ff+E(_fw.b)*_fg-_ft)/_fu;}),_fx=new T(function(){var _fy=E(E(_fo).b);return (E(_fy.a)*_ff+E(_fy.b)*_fg-_ft)/_fu;}),_fz=function(_fA){var _fB=new T(function(){var _fC=E(_fA);if(0>_fC){return E(_9j);}else{if(1>_fC){return E(_fC);}else{return E(_9k);}}}),_fD=new T(function(){return E(_fx)-E(_fB);}),_fE=new T(function(){return E(_fB)-E(_fv);});return new T2(0,new T(function(){var _fF=E(_fD),_fG=E(_fE);return (E(_fr.a)*_fF+E(_fs.a)*_fG)/(_fF+_fG);}),new T(function(){var _fH=E(_fD),_fI=E(_fE);return (E(_fr.b)*_fH+E(_fs.b)*_fI)/(_fH+_fI);}));},_fJ=B(_fz(_fv)),_fK=E(_fJ.a),_fL=E(_fJ.b),_fM=new T(function(){var _fN=B(_fz(_fx)),_fO=E(_fN.a),_fP=E(_fN.b),_fQ=(_fl*_fO+_fm*_fP-(_fl*_fi+_fm*_fj))/Math.sqrt(_fl*_fl+_fm*_fm);if(_fQ<0){return new T2(1,new T2(0,new T2(0,_fO,_fP), -_fQ),_4);}else{return __Z;}}),_fR=(_fl*_fK+_fm*_fL-(_fl*_fi+_fm*_fj))/Math.sqrt(_fl*_fl+_fm*_fm);if(_fR<0){var _fS=new T2(1,new T2(0,new T2(0,_fK,_fL), -_fR),_fM);}else{var _fS=E(_fM);}var _fT=new T(function(){return B(_aK(_8j,_fS));}),_fU= -_fg,_fV=new T(function(){var _fW=function(_fX){var _fY=E(_fX),_fZ=_fY.b,_g0=E(_fY.a);return new T2(0,new T(function(){return E(_g0.a)+_fU*E(_fZ);}),new T(function(){return E(_g0.b)+_ff*E(_fZ);}));};return B(_aK(_fW,_fS));}),_g1=new T(function(){if(!E(_dg)){var _g2=new T(function(){return E(E(_bq).b);}),_g3=new T(function(){return E(E(_bq).a);});return B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_g3,_g2),_cX);});},_fV));}else{var _g4=new T(function(){return E(E(_bq).b);}),_g5=new T(function(){return E(E(_bq).a);});return B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_g5,_g4),_cX);});},_fT));}}),_g6=new T(function(){if(!E(_dg)){return new T2(0,_fU,_ff);}else{return new T2(0, -_fU, -_ff);}}),_g7=function(_g8,_g9,_ga){return new T5(0,_g8,_g9,_g6,_g6,_ga);};if(!E(_dg)){var _gb=new T(function(){return E(E(_bo).b);}),_gc=new T(function(){return E(E(_bo).a);});return new F(function(){return _be(_g7,B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_gc,_gb),_cX);});},_fT)),_g1,new T(function(){return B(_aK(_aV,_fS));},1));});}else{var _gd=new T(function(){return E(E(_bo).b);}),_ge=new T(function(){return E(E(_bo).a);});return new F(function(){return _be(_g7,B(_aK(function(_cX){return new F(function(){return _70(new T2(0,_ge,_gd),_cX);});},_fV)),_g1,new T(function(){return B(_aK(_aV,_fS));},1));});}},_gf=function(_gg){var _gh=function(_gi,_gj){while(1){var _gk=B((function(_gl,_gm){var _gn=E(_gl);if(!_gn._){return __Z;}else{var _go=_gn.b,_gp=E(_gm);if(!_gp._){return __Z;}else{var _gq=_gp.b,_gr=E(_gn.a),_gs=(_fl*E(_gr.a)+_fm*E(_gr.b)-(_fl*_fi+_fm*_fj))/Math.sqrt(_fl*_fl+_fm*_fm);if(_gs<0){return new T2(1,new T2(0,new T1(1,_gs),_gp.a),new T(function(){return B(_gh(_go,_gq));}));}else{_gi=_go;_gj=_gq;return __continue;}}}})(_gi,_gj));if(_gk!=__continue){return _gk;}}};return new F(function(){return _gh(_gg,_9o);});},_gt=function(_gu){var _gv=B(_7e(_dl,_gu)),_gw=E(_gv.a),_gx=E(_gv.b),_gy=E(_gw.a)-E(_gx.a),_gz=E(_gw.b)-E(_gx.b),_gA=function(_gB,_gC){var _gD=function(_gE){var _gF=B(_7e(_dl,B(_aO(_gu+1|0,4)))),_gG=E(_gF.b),_gH=E(_gF.a),_gI=E(_gG.a)-E(_gH.a),_gJ=E(_gG.b)-E(_gH.b),_gK=Math.sqrt(_gI*_gI+_gJ*_gJ);if(!_gK){var _gL=_ff+_fg*0;return (_gL==0)?(_gE<=0)?new T3(0,_gF,_gH,_gG):new T3(0,new T2(0,_gx,_gw),_gx,_gw):(_gL<=0)?(_gE<= -_gL)?new T3(0,_gF,_gH,_gG):new T3(0,new T2(0,_gx,_gw),_gx,_gw):(_gE<=_gL)?new T3(0,_gF,_gH,_gG):new T3(0,new T2(0,_gx,_gw),_gx,_gw);}else{var _gM=_ff*(_gI/_gK)+_fg*(_gJ/_gK);return (_gM==0)?(_gE<=0)?new T3(0,_gF,_gH,_gG):new T3(0,new T2(0,_gx,_gw),_gx,_gw):(_gM<=0)?(_gE<= -_gM)?new T3(0,_gF,_gH,_gG):new T3(0,new T2(0,_gx,_gw),_gx,_gw):(_gE<=_gM)?new T3(0,_gF,_gH,_gG):new T3(0,new T2(0,_gx,_gw),_gx,_gw);}},_gN=_ff*_gB+_fg*_gC;if(!_gN){return new F(function(){return _gD(0);});}else{if(_gN<=0){return new F(function(){return _gD( -_gN);});}else{return new F(function(){return _gD(_gN);});}}},_gO=Math.sqrt(_gy*_gy+_gz*_gz);if(!_gO){return new F(function(){return _gA(1,0);});}else{return new F(function(){return _gA(_gy/_gO,_gz/_gO);});}};if(!E(_dg)){var _gP=E(_cS);if(!_gP._){return E(_aY);}else{var _gQ=B(_gf(_gP.b));if(!_gQ._){return E(_9n);}else{var _gR=E(_gQ.a),_gS=B(_gt(E(B(_7i(_gQ.b,_gR.a,_gR.b)).b)));return new F(function(){return _fn(_gS.a,_gS.b,_gS.c);});}}}else{var _gT=E(_cz);if(!_gT._){return E(_aY);}else{var _gU=B(_gf(_gT.b));if(!_gU._){return E(_9n);}else{var _gV=E(_gU.a),_gW=B(_gt(E(B(_7i(_gU.b,_gV.a,_gV.b)).b)));return new F(function(){return _fn(_gW.a,_gW.b,_gW.c);});}}}}};if(!E(_dg)){if(!E(_dc)._){return E(_aw);}else{var _gX=B(_7e(_dk,_da)),_gY=_gX.a,_gZ=_gX.b;return new F(function(){return _dm(_gY,_gZ,_gY,_gZ);});}}else{if(!E(_dd)._){return E(_aw);}else{var _h0=B(_7e(_dk,_d6)),_h1=_h0.a,_h2=_h0.b;return new F(function(){return _dm(_h1,_h2,_h1,_h2);});}}};if(!E(_dg)){return new F(function(){return _dj(_cI,_cY);});}else{return new F(function(){return _dj(_cY,_cI);});}}}}}}else{return __Z;}}}},_h3=new T(function(){return B(_3Z(-1,1));}),_h4=function(_h5,_h6){var _h7=new T(function(){var _h8=E(E(_h5).b),_h9=E(E(_h6).b);if(E(_h8.a)!=E(_h9.a)){return false;}else{if(E(_h8.b)!=E(_h9.b)){return false;}else{return E(_h8.c)==E(_h9.c);}}}),_ha=new T(function(){return E(E(_h6).a);}),_hb=function(_hc){var _hd=E(_hc);if(!_hd._){return __Z;}else{var _he=_hd.a,_hf=new T(function(){return B(_hb(_hd.b));}),_hg=function(_hh){var _hi=E(_hh);if(!_hi._){return E(_hf);}else{var _hj=_hi.a,_hk=new T(function(){return B(_hg(_hi.b));}),_hl=function(_hm){var _hn=E(_h5),_ho=new T(function(){var _hp=E(E(_h6).b);return new T3(0,new T(function(){return E(_hp.a)+E(_he)*E(_1r);}),new T(function(){return E(_hp.b)+E(_hj)*E(_5Y);}),_hp.c);});return new F(function(){return _0(B(_bm(_hn.a,_hn.b,_ha,_ho)),_hk);});};if(!E(_h7)){return new F(function(){return _hl(_);});}else{if(!E(_he)){if(!E(_hj)){return E(_hk);}else{return new F(function(){return _hl(_);});}}else{return new F(function(){return _hl(_);});}}}};return new F(function(){return _hg(_h3);});}};return new F(function(){return _hb(_h3);});},_hq=function(_hr,_hs){var _ht=E(_hr),_hu=E(_hs);return E(_ht.a)*E(_hu.b)-E(_hu.a)*E(_ht.b);},_hv=new T(function(){return eval("drawContact");}),_hw=function(_hx){var _hy=E(_hx);if(!_hy._){return __Z;}else{return new F(function(){return _0(_hy.a,new T(function(){return B(_hw(_hy.b));},1));});}},_hz=function(_hA){var _hB=E(_hA);if(!_hB._){return __Z;}else{return new F(function(){return _0(_hB.a,new T(function(){return B(_hz(_hB.b));},1));});}},_hC=new T(function(){return B(unCStr(")"));}),_hD=function(_hE,_hF){var _hG=new T(function(){var _hH=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2s(0,_hF,_4)),_hC));})));},1);return B(_0(B(_2s(0,_hE,_4)),_hH));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_hG)));});},_hI=function(_hJ,_hK,_hL,_hM,_hN,_){if(_hJ<=_hK){var _hO=function(_hP,_hQ,_){var _hR=_hP+1|0;if(_hR<=_hK){var _hS=new T(function(){if(_hJ>_hP){return E(_6P);}else{if(_hP>_hK){return E(_6P);}else{var _hT=_hP-_hJ|0;if(0>_hT){return B(_hD(_hT,_hL));}else{if(_hT>=_hL){return B(_hD(_hT,_hL));}else{return E(_hM[_hT]);}}}}}),_hU=function(_hV,_hW,_){var _hX=new T(function(){if(_hJ>_hV){return E(_6P);}else{if(_hV>_hK){return E(_6P);}else{var _hY=_hV-_hJ|0;if(0>_hY){return B(_hD(_hY,_hL));}else{if(_hY>=_hL){return B(_hD(_hY,_hL));}else{return E(_hM[_hY]);}}}}}),_hZ=B(_h4(_hS,_hX)),_i0=function(_,_i1,_i2){var _i3=new T(function(){var _i4=function(_i5){var _i6=E(_i5),_i7=_i6.c,_i8=_i6.d;return new T5(0,_hP,_hV,new T3(0,new T(function(){return E(E(_i7).a);}),new T(function(){return E(E(_i7).b);}),new T(function(){return B(_hq(_i6.a,_i7));})),new T3(0,new T(function(){return E(E(_i8).a);}),new T(function(){return E(E(_i8).b);}),new T(function(){return B(_hq(_i6.b,_i8));})),_i6.e);};return B(_aK(_i4,_hZ));});if(_hV!=_hK){var _i9=B(_hU(_hV+1|0,_i2,_));return new T2(0,new T2(1,_i3,new T(function(){return E(E(_i9).a);})),new T(function(){return E(E(_i9).b);}));}else{return new T2(0,new T2(1,_i3,_4),_i2);}},_ia=E(_hZ);if(!_ia._){return new F(function(){return _i0(_,_4,_hW);});}else{var _ib=E(_ia.a),_ic=E(E(_hS).b),_id=E(_ic.a),_ie=E(_ib.a),_if=E(_ic.b),_ig=E(_ib.c),_ih=E(_ib.e),_ii=E(_hv),_ij=__app5(_ii,_id+E(_ie.a),_if+E(_ie.b),E(_ig.a),E(_ig.b),_ih),_ik=E(E(_hX).b),_il=E(_ik.a),_im=E(_ib.b),_in=E(_ik.b),_io=E(_ib.d),_ip=__app5(_ii,_il+E(_im.a),_in+E(_im.b), -E(_io.a), -E(_io.b),_ih),_iq=function(_ir,_is,_){var _it=E(_ir);if(!_it._){return new T2(0,_4,_is);}else{var _iu=E(_it.a),_iv=E(_iu.a),_iw=E(_iu.c),_ix=E(_iu.e),_iy=__app5(_ii,_id+E(_iv.a),_if+E(_iv.b),E(_iw.a),E(_iw.b),_ix),_iz=E(_iu.b),_iA=E(_iu.d),_iB=__app5(_ii,_il+E(_iz.a),_in+E(_iz.b), -E(_iA.a), -E(_iA.b),_ix),_iC=B(_iq(_it.b,_is,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_iC).a);})),new T(function(){return E(E(_iC).b);}));}},_iD=B(_iq(_ia.b,_hW,_));return new F(function(){return _i0(_,new T2(1,_5,new T(function(){return E(E(_iD).a);})),new T(function(){return E(E(_iD).b);}));});}},_iE=B(_hU(_hR,_hQ,_));if(_hP!=_hK){var _iF=B(_hO(_hR,new T(function(){return E(E(_iE).b);}),_));return new T2(0,new T2(1,new T(function(){return B(_hz(E(_iE).a));}),new T(function(){return E(E(_iF).a);})),new T(function(){return E(E(_iF).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_hz(E(_iE).a));}),_4),new T(function(){return E(E(_iE).b);}));}}else{if(_hP!=_hK){var _iG=B(_hO(_hR,_hQ,_));return new T2(0,new T2(1,_4,new T(function(){return E(E(_iG).a);})),new T(function(){return E(E(_iG).b);}));}else{return new T2(0,new T2(1,_4,_4),_hQ);}}},_iH=B(_hO(_hJ,_hN,_));return new T2(0,new T(function(){return B(_hw(E(_iH).a));}),new T(function(){return E(E(_iH).b);}));}else{return new T2(0,_4,_hN);}},_iI=function(_iJ){var _iK=E(_iJ),_iL=_iK.c,_iM=new T(function(){var _iN=E(_iK.b),_iO=E(_iL);return new T3(0,new T(function(){return E(_iN.a)+E(_iO.a)*0.2;}),new T(function(){return E(_iN.b)+E(_iO.b)*0.2;}),new T(function(){return E(_iN.c)+E(_iO.c)*0.2;}));});return new T5(0,_iK.a,_iM,_iL,_iK.d,_iK.e);},_iP=function(_iQ,_iR,_iS,_iT,_iU){var _iV=new T(function(){var _iW=E(_iS),_iX=E(_iT),_iY=new T(function(){var _iZ=E(E(_iR).b)/E(_5Y);return 0.2*Math.sin((_iZ+_iZ)*3.141592653589793);});return new T3(0,new T(function(){return E(_iW.a)+E(_iX.a)*E(_iY);}),new T(function(){return E(_iW.b)+E(_iX.b)*E(_iY);}),new T(function(){return E(_iW.c)+E(_iX.c)*E(_iY);}));});return new T5(0,_iQ,_iR,_iV,_iT,_iU);},_j0=function(_j1){var _j2=E(_j1),_j3=B(_iP(_j2.a,_j2.b,_j2.c,_j2.d,_j2.e));return new T5(0,_j3.a,_j3.b,_j3.c,_j3.d,_j3.e);},_j4=function(_j5,_){return new T2(0,_4,_j5);},_j6=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_j7=new T(function(){return B(err(_j6));}),_j8=function(_j9,_ja){var _jb=new T(function(){var _jc=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2s(0,_j9,_4)),_hC));})));},1);return B(_0(B(_2s(0,_ja,_4)),_jc));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_jb)));});},_jd=0.6,_je=function(_jf){var _jg=E(_jf);if(!_jg._){return E(_j4);}else{var _jh=_jg.a,_ji=new T(function(){return B(_je(_jg.b));}),_jj=new T(function(){return 0.1*E(E(_jh).e)/0.2;}),_jk=new T(function(){var _jl=E(_jh);if(E(_jl.a)!=E(_jl.b)){return E(_9k);}else{return E(_jd);}}),_jm=function(_jn,_){var _jo=E(_jn),_jp=_jo.c,_jq=_jo.d,_jr=E(_jo.a),_js=E(_jo.b),_jt=E(_jh),_ju=E(_jt.a);if(_jr>_ju){return E(_j7);}else{if(_ju>_js){return E(_j7);}else{var _jv=_ju-_jr|0;if(0>_jv){return new F(function(){return _j8(_jp,_jv);});}else{if(_jv>=_jp){return new F(function(){return _j8(_jp,_jv);});}else{var _jw=E(_jq[_jv]),_jx=E(_jw.e),_jy=E(_jx.a),_jz=E(_jx.b),_jA=E(_jx.c),_jB=E(_jt.c),_jC=E(_jB.a),_jD=E(_jB.b),_jE=E(_jB.c),_jF=E(_jt.b);if(_jr>_jF){return E(_j7);}else{if(_jF>_js){return E(_j7);}else{var _jG=_jF-_jr|0;if(0>_jG){return new F(function(){return _hD(_jG,_jp);});}else{if(_jG>=_jp){return new F(function(){return _hD(_jG,_jp);});}else{var _jH=E(_jq[_jG]),_jI=E(_jH.e),_jJ=E(_jI.a),_jK=E(_jI.b),_jL=E(_jI.c),_jM=E(_jt.d),_jN=E(_jM.a),_jO=E(_jM.b),_jP=E(_jM.c),_jQ=_jC*_jy*_jC+_jD*_jz*_jD+_jE*_jA*_jE+_jN*_jJ*_jN+_jO*_jK*_jO+_jP*_jL*_jP;if(!_jQ){var _jR=B(A2(_ji,_jo,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_jR).a);})),new T(function(){return E(E(_jR).b);}));}else{var _jS=E(_jw.c),_jT=E(_jS.a),_jU=E(_jS.b),_jV=E(_jS.c),_jW=E(_jH.c),_jX= -((_jT*_jC+_jU*_jD+_jV*_jE-(E(_jW.a)*_jN+E(_jW.b)*_jO+E(_jW.c)*_jP)-E(_jj))/_jQ);if(_jX<0){var _jY=B(A2(_ji,_jo,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_jY).a);})),new T(function(){return E(E(_jY).b);}));}else{var _jZ=new T(function(){var _k0=function(_){var _k1=newArr(_jp,_1k),_k2=_k1,_k3=function(_k4,_){while(1){if(_k4!=_jp){var _=_k2[_k4]=_jq[_k4],_k5=_k4+1|0;_k4=_k5;continue;}else{return E(_);}}},_=B(_k3(0,_)),_k6=new T(function(){return _jX*E(_jk);}),_=_k2[_jv]=new T5(0,_jw.a,_jw.b,new T3(0,new T(function(){return _jT+_jy*_jC*E(_k6);}),new T(function(){return _jU+_jz*_jD*E(_k6);}),new T(function(){return _jV+_jA*_jE*E(_k6);})),_jw.d,_jx);return new T4(0,E(_jr),E(_js),_jp,_k2);},_k7=B(_1K(_k0)),_k8=_k7.c,_k9=_k7.d,_ka=E(_k7.a),_kb=E(_k7.b);if(_ka>_jF){return E(_k7);}else{if(_jF>_kb){return E(_k7);}else{var _kc=function(_){var _kd=newArr(_k8,_1k),_ke=_kd,_kf=function(_kg,_){while(1){if(_kg!=_k8){var _=_ke[_kg]=_k9[_kg],_kh=_kg+1|0;_kg=_kh;continue;}else{return E(_);}}},_=B(_kf(0,_)),_ki=_jF-_ka|0;if(0>_ki){return new F(function(){return _hD(_ki,_k8);});}else{if(_ki>=_k8){return new F(function(){return _hD(_ki,_k8);});}else{var _kj=new T(function(){var _kk=E(_k9[_ki]),_kl=new T(function(){return _jX*E(_jk);}),_km=new T(function(){var _kn=E(_kk.c);return new T3(0,new T(function(){return E(_kn.a)-_jJ*_jN*E(_kl);}),new T(function(){return E(_kn.b)-_jK*_jO*E(_kl);}),new T(function(){return E(_kn.c)-_jL*_jP*E(_kl);}));});return new T5(0,_kk.a,_kk.b,_km,_kk.d,_kk.e);}),_=_ke[_ki]=_kj;return new T4(0,E(_ka),E(_kb),_k8,_ke);}}};return B(_1K(_kc));}}}),_ko=B(A2(_ji,_jZ,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_ko).a);})),new T(function(){return E(E(_ko).b);}));}}}}}}}}}}};return E(_jm);}},_kp=new T1(0,1),_kq=function(_kr,_ks){var _kt=E(_kr);if(!_kt._){var _ku=_kt.a,_kv=E(_ks);if(!_kv._){var _kw=_kv.a;return (_ku!=_kw)?(_ku>_kw)?2:0:1;}else{var _kx=I_compareInt(_kv.a,_ku);return (_kx<=0)?(_kx>=0)?1:2:0;}}else{var _ky=_kt.a,_kz=E(_ks);if(!_kz._){var _kA=I_compareInt(_ky,_kz.a);return (_kA>=0)?(_kA<=0)?1:2:0;}else{var _kB=I_compare(_ky,_kz.a);return (_kB>=0)?(_kB<=0)?1:2:0;}}},_kC=new T(function(){return B(unCStr("base"));}),_kD=new T(function(){return B(unCStr("GHC.Exception"));}),_kE=new T(function(){return B(unCStr("ArithException"));}),_kF=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kC,_kD,_kE),_kG=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kF,_4,_4),_kH=function(_kI){return E(_kG);},_kJ=function(_kK){var _kL=E(_kK);return new F(function(){return _9y(B(_9w(_kL.a)),_kH,_kL.b);});},_kM=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_kN=new T(function(){return B(unCStr("denormal"));}),_kO=new T(function(){return B(unCStr("divide by zero"));}),_kP=new T(function(){return B(unCStr("loss of precision"));}),_kQ=new T(function(){return B(unCStr("arithmetic underflow"));}),_kR=new T(function(){return B(unCStr("arithmetic overflow"));}),_kS=function(_kT,_kU){switch(E(_kT)){case 0:return new F(function(){return _0(_kR,_kU);});break;case 1:return new F(function(){return _0(_kQ,_kU);});break;case 2:return new F(function(){return _0(_kP,_kU);});break;case 3:return new F(function(){return _0(_kO,_kU);});break;case 4:return new F(function(){return _0(_kN,_kU);});break;default:return new F(function(){return _0(_kM,_kU);});}},_kV=function(_kW){return new F(function(){return _kS(_kW,_4);});},_kX=function(_kY,_kZ,_l0){return new F(function(){return _kS(_kZ,_l0);});},_l1=function(_l2,_l3){return new F(function(){return _2G(_kS,_l2,_l3);});},_l4=new T3(0,_kX,_kV,_l1),_l5=new T(function(){return new T5(0,_kH,_l4,_l6,_kJ,_kV);}),_l6=function(_a7){return new T2(0,_l5,_a7);},_l7=3,_l8=new T(function(){return B(_l6(_l7));}),_l9=new T(function(){return die(_l8);}),_la=function(_lb,_lc){var _ld=E(_lb);return (_ld._==0)?_ld.a*Math.pow(2,_lc):I_toNumber(_ld.a)*Math.pow(2,_lc);},_le=function(_lf,_lg){var _lh=E(_lf);if(!_lh._){var _li=_lh.a,_lj=E(_lg);return (_lj._==0)?_li==_lj.a:(I_compareInt(_lj.a,_li)==0)?true:false;}else{var _lk=_lh.a,_ll=E(_lg);return (_ll._==0)?(I_compareInt(_lk,_ll.a)==0)?true:false:(I_compare(_lk,_ll.a)==0)?true:false;}},_lm=function(_ln){var _lo=E(_ln);if(!_lo._){return E(_lo.a);}else{return new F(function(){return I_toInt(_lo.a);});}},_lp=function(_lq,_lr){while(1){var _ls=E(_lq);if(!_ls._){var _lt=_ls.a,_lu=E(_lr);if(!_lu._){var _lv=_lu.a,_lw=addC(_lt,_lv);if(!E(_lw.b)){return new T1(0,_lw.a);}else{_lq=new T1(1,I_fromInt(_lt));_lr=new T1(1,I_fromInt(_lv));continue;}}else{_lq=new T1(1,I_fromInt(_lt));_lr=_lu;continue;}}else{var _lx=E(_lr);if(!_lx._){_lq=_ls;_lr=new T1(1,I_fromInt(_lx.a));continue;}else{return new T1(1,I_add(_ls.a,_lx.a));}}}},_ly=function(_lz,_lA){while(1){var _lB=E(_lz);if(!_lB._){var _lC=E(_lB.a);if(_lC==(-2147483648)){_lz=new T1(1,I_fromInt(-2147483648));continue;}else{var _lD=E(_lA);if(!_lD._){var _lE=_lD.a;return new T2(0,new T1(0,quot(_lC,_lE)),new T1(0,_lC%_lE));}else{_lz=new T1(1,I_fromInt(_lC));_lA=_lD;continue;}}}else{var _lF=E(_lA);if(!_lF._){_lz=_lB;_lA=new T1(1,I_fromInt(_lF.a));continue;}else{var _lG=I_quotRem(_lB.a,_lF.a);return new T2(0,new T1(1,_lG.a),new T1(1,_lG.b));}}}},_lH=new T1(0,0),_lI=function(_lJ,_lK){while(1){var _lL=E(_lJ);if(!_lL._){_lJ=new T1(1,I_fromInt(_lL.a));continue;}else{return new T1(1,I_shiftLeft(_lL.a,_lK));}}},_lM=function(_lN,_lO,_lP){if(!B(_le(_lP,_lH))){var _lQ=B(_ly(_lO,_lP)),_lR=_lQ.a;switch(B(_kq(B(_lI(_lQ.b,1)),_lP))){case 0:return new F(function(){return _la(_lR,_lN);});break;case 1:if(!(B(_lm(_lR))&1)){return new F(function(){return _la(_lR,_lN);});}else{return new F(function(){return _la(B(_lp(_lR,_kp)),_lN);});}break;default:return new F(function(){return _la(B(_lp(_lR,_kp)),_lN);});}}else{return E(_l9);}},_lS=function(_lT,_lU){var _lV=E(_lT);if(!_lV._){var _lW=_lV.a,_lX=E(_lU);return (_lX._==0)?_lW>_lX.a:I_compareInt(_lX.a,_lW)<0;}else{var _lY=_lV.a,_lZ=E(_lU);return (_lZ._==0)?I_compareInt(_lY,_lZ.a)>0:I_compare(_lY,_lZ.a)>0;}},_m0=new T1(0,1),_m1=function(_m2,_m3){var _m4=E(_m2);if(!_m4._){var _m5=_m4.a,_m6=E(_m3);return (_m6._==0)?_m5<_m6.a:I_compareInt(_m6.a,_m5)>0;}else{var _m7=_m4.a,_m8=E(_m3);return (_m8._==0)?I_compareInt(_m7,_m8.a)<0:I_compare(_m7,_m8.a)<0;}},_m9=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ma=function(_mb){return new F(function(){return _a5(new T1(0,new T(function(){return B(_aj(_mb,_m9));})),_9N);});},_mc=function(_md){var _me=function(_mf,_mg){while(1){if(!B(_m1(_mf,_md))){if(!B(_lS(_mf,_md))){if(!B(_le(_mf,_md))){return new F(function(){return _ma("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_mg);}}else{return _mg-1|0;}}else{var _mh=B(_lI(_mf,1)),_mi=_mg+1|0;_mf=_mh;_mg=_mi;continue;}}};return new F(function(){return _me(_m0,0);});},_mj=function(_mk){var _ml=E(_mk);if(!_ml._){var _mm=_ml.a>>>0;if(!_mm){return -1;}else{var _mn=function(_mo,_mp){while(1){if(_mo>=_mm){if(_mo<=_mm){if(_mo!=_mm){return new F(function(){return _ma("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_mp);}}else{return _mp-1|0;}}else{var _mq=imul(_mo,2)>>>0,_mr=_mp+1|0;_mo=_mq;_mp=_mr;continue;}}};return new F(function(){return _mn(1,0);});}}else{return new F(function(){return _mc(_ml);});}},_ms=function(_mt){var _mu=E(_mt);if(!_mu._){var _mv=_mu.a>>>0;if(!_mv){return new T2(0,-1,0);}else{var _mw=function(_mx,_my){while(1){if(_mx>=_mv){if(_mx<=_mv){if(_mx!=_mv){return new F(function(){return _ma("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_my);}}else{return _my-1|0;}}else{var _mz=imul(_mx,2)>>>0,_mA=_my+1|0;_mx=_mz;_my=_mA;continue;}}};return new T2(0,B(_mw(1,0)),(_mv&_mv-1>>>0)>>>0&4294967295);}}else{var _mB=_mu.a;return new T2(0,B(_mj(_mu)),I_compareInt(I_and(_mB,I_sub(_mB,I_fromInt(1))),0));}},_mC=function(_mD,_mE){var _mF=E(_mD);if(!_mF._){var _mG=_mF.a,_mH=E(_mE);return (_mH._==0)?_mG<=_mH.a:I_compareInt(_mH.a,_mG)>=0;}else{var _mI=_mF.a,_mJ=E(_mE);return (_mJ._==0)?I_compareInt(_mI,_mJ.a)<=0:I_compare(_mI,_mJ.a)<=0;}},_mK=function(_mL,_mM){while(1){var _mN=E(_mL);if(!_mN._){var _mO=_mN.a,_mP=E(_mM);if(!_mP._){return new T1(0,(_mO>>>0&_mP.a>>>0)>>>0&4294967295);}else{_mL=new T1(1,I_fromInt(_mO));_mM=_mP;continue;}}else{var _mQ=E(_mM);if(!_mQ._){_mL=_mN;_mM=new T1(1,I_fromInt(_mQ.a));continue;}else{return new T1(1,I_and(_mN.a,_mQ.a));}}}},_mR=function(_mS,_mT){while(1){var _mU=E(_mS);if(!_mU._){var _mV=_mU.a,_mW=E(_mT);if(!_mW._){var _mX=_mW.a,_mY=subC(_mV,_mX);if(!E(_mY.b)){return new T1(0,_mY.a);}else{_mS=new T1(1,I_fromInt(_mV));_mT=new T1(1,I_fromInt(_mX));continue;}}else{_mS=new T1(1,I_fromInt(_mV));_mT=_mW;continue;}}else{var _mZ=E(_mT);if(!_mZ._){_mS=_mU;_mT=new T1(1,I_fromInt(_mZ.a));continue;}else{return new T1(1,I_sub(_mU.a,_mZ.a));}}}},_n0=new T1(0,2),_n1=function(_n2,_n3){var _n4=E(_n2);if(!_n4._){var _n5=(_n4.a>>>0&(2<<_n3>>>0)-1>>>0)>>>0,_n6=1<<_n3>>>0;return (_n6<=_n5)?(_n6>=_n5)?1:2:0;}else{var _n7=B(_mK(_n4,B(_mR(B(_lI(_n0,_n3)),_m0)))),_n8=B(_lI(_m0,_n3));return (!B(_lS(_n8,_n7)))?(!B(_m1(_n8,_n7)))?1:2:0;}},_n9=function(_na,_nb){while(1){var _nc=E(_na);if(!_nc._){_na=new T1(1,I_fromInt(_nc.a));continue;}else{return new T1(1,I_shiftRight(_nc.a,_nb));}}},_nd=function(_ne,_nf,_ng,_nh){var _ni=B(_ms(_nh)),_nj=_ni.a;if(!E(_ni.b)){var _nk=B(_mj(_ng));if(_nk<((_nj+_ne|0)-1|0)){var _nl=_nj+(_ne-_nf|0)|0;if(_nl>0){if(_nl>_nk){if(_nl<=(_nk+1|0)){if(!E(B(_ms(_ng)).b)){return 0;}else{return new F(function(){return _la(_kp,_ne-_nf|0);});}}else{return 0;}}else{var _nm=B(_n9(_ng,_nl));switch(B(_n1(_ng,_nl-1|0))){case 0:return new F(function(){return _la(_nm,_ne-_nf|0);});break;case 1:if(!(B(_lm(_nm))&1)){return new F(function(){return _la(_nm,_ne-_nf|0);});}else{return new F(function(){return _la(B(_lp(_nm,_kp)),_ne-_nf|0);});}break;default:return new F(function(){return _la(B(_lp(_nm,_kp)),_ne-_nf|0);});}}}else{return new F(function(){return _la(_ng,(_ne-_nf|0)-_nl|0);});}}else{if(_nk>=_nf){var _nn=B(_n9(_ng,(_nk+1|0)-_nf|0));switch(B(_n1(_ng,_nk-_nf|0))){case 0:return new F(function(){return _la(_nn,((_nk-_nj|0)+1|0)-_nf|0);});break;case 2:return new F(function(){return _la(B(_lp(_nn,_kp)),((_nk-_nj|0)+1|0)-_nf|0);});break;default:if(!(B(_lm(_nn))&1)){return new F(function(){return _la(_nn,((_nk-_nj|0)+1|0)-_nf|0);});}else{return new F(function(){return _la(B(_lp(_nn,_kp)),((_nk-_nj|0)+1|0)-_nf|0);});}}}else{return new F(function(){return _la(_ng, -_nj);});}}}else{var _no=B(_mj(_ng))-_nj|0,_np=function(_nq){var _nr=function(_ns,_nt){if(!B(_mC(B(_lI(_nt,_nf)),_ns))){return new F(function(){return _lM(_nq-_nf|0,_ns,_nt);});}else{return new F(function(){return _lM((_nq-_nf|0)+1|0,_ns,B(_lI(_nt,1)));});}};if(_nq>=_nf){if(_nq!=_nf){return new F(function(){return _nr(_ng,new T(function(){return B(_lI(_nh,_nq-_nf|0));}));});}else{return new F(function(){return _nr(_ng,_nh);});}}else{return new F(function(){return _nr(new T(function(){return B(_lI(_ng,_nf-_nq|0));}),_nh);});}};if(_ne>_no){return new F(function(){return _np(_ne);});}else{return new F(function(){return _np(_no);});}}},_nu=new T1(0,2147483647),_nv=new T(function(){return B(_lp(_nu,_m0));}),_nw=function(_nx){var _ny=E(_nx);if(!_ny._){var _nz=E(_ny.a);return (_nz==(-2147483648))?E(_nv):new T1(0, -_nz);}else{return new T1(1,I_negate(_ny.a));}},_nA=new T(function(){return 0/0;}),_nB=new T(function(){return -1/0;}),_nC=new T(function(){return 1/0;}),_nD=0,_nE=function(_nF,_nG){if(!B(_le(_nG,_lH))){if(!B(_le(_nF,_lH))){if(!B(_m1(_nF,_lH))){return new F(function(){return _nd(-1021,53,_nF,_nG);});}else{return  -B(_nd(-1021,53,B(_nw(_nF)),_nG));}}else{return E(_nD);}}else{return (!B(_le(_nF,_lH)))?(!B(_m1(_nF,_lH)))?E(_nC):E(_nB):E(_nA);}},_nH=function(_nI){var _nJ=E(_nI);return new F(function(){return _nE(_nJ.a,_nJ.b);});},_nK=function(_nL){return 1/E(_nL);},_nM=function(_nN){var _nO=E(_nN),_nP=E(_nO);return (_nP==0)?E(_nD):(_nP<=0)? -_nP:E(_nO);},_nQ=function(_nR){var _nS=E(_nR);if(!_nS._){return _nS.a;}else{return new F(function(){return I_toNumber(_nS.a);});}},_nT=function(_nU){return new F(function(){return _nQ(_nU);});},_nV=function(_nW){var _nX=E(_nW);return (_nX<=0)?(_nX>=0)?E(_nX):E(_6R):E(_6Q);},_nY=function(_nZ,_o0){return E(_nZ)+E(_o0);},_o1=function(_o2,_o3){return E(_o2)*E(_o3);},_o4={_:0,a:_nY,b:_6S,c:_o1,d:_ay,e:_nM,f:_nV,g:_nT},_o5=function(_o6,_o7){return E(_o6)/E(_o7);},_o8=new T4(0,_o4,_o5,_nK,_nH),_o9=function(_oa,_ob){return (E(_oa)!=E(_ob))?true:false;},_oc=function(_od,_oe){return E(_od)==E(_oe);},_of=new T2(0,_oc,_o9),_og=function(_oh,_oi){return E(_oh)<E(_oi);},_oj=function(_ok,_ol){return E(_ok)<=E(_ol);},_om=function(_on,_oo){return E(_on)>E(_oo);},_op=function(_oq,_or){return E(_oq)>=E(_or);},_os=function(_ot,_ou){var _ov=E(_ot),_ow=E(_ou);return (_ov>=_ow)?(_ov!=_ow)?2:1:0;},_ox=function(_oy,_oz){var _oA=E(_oy),_oB=E(_oz);return (_oA>_oB)?E(_oA):E(_oB);},_oC=function(_oD,_oE){var _oF=E(_oD),_oG=E(_oE);return (_oF>_oG)?E(_oG):E(_oF);},_oH={_:0,a:_of,b:_os,c:_og,d:_oj,e:_om,f:_op,g:_ox,h:_oC},_oI=function(_oJ){var _oK=I_decodeDouble(_oJ);return new T2(0,new T1(1,_oK.b),_oK.a);},_oL=function(_oM){return new T1(0,_oM);},_oN=function(_oO){var _oP=hs_intToInt64(2147483647),_oQ=hs_leInt64(_oO,_oP);if(!_oQ){return new T1(1,I_fromInt64(_oO));}else{var _oR=hs_intToInt64(-2147483648),_oS=hs_geInt64(_oO,_oR);if(!_oS){return new T1(1,I_fromInt64(_oO));}else{var _oT=hs_int64ToInt(_oO);return new F(function(){return _oL(_oT);});}}},_oU=new T(function(){var _oV=newByteArr(256),_oW=_oV,_=_oW["v"]["i8"][0]=8,_oX=function(_oY,_oZ,_p0,_){while(1){if(_p0>=256){if(_oY>=256){return E(_);}else{var _p1=imul(2,_oY)|0,_p2=_oZ+1|0,_p3=_oY;_oY=_p1;_oZ=_p2;_p0=_p3;continue;}}else{var _=_oW["v"]["i8"][_p0]=_oZ,_p3=_p0+_oY|0;_p0=_p3;continue;}}},_=B(_oX(2,0,1,_));return _oW;}),_p4=function(_p5,_p6){var _p7=hs_int64ToInt(_p5),_p8=E(_oU),_p9=_p8["v"]["i8"][(255&_p7>>>0)>>>0&4294967295];if(_p6>_p9){if(_p9>=8){var _pa=hs_uncheckedIShiftRA64(_p5,8),_pb=function(_pc,_pd){while(1){var _pe=B((function(_pf,_pg){var _ph=hs_int64ToInt(_pf),_pi=_p8["v"]["i8"][(255&_ph>>>0)>>>0&4294967295];if(_pg>_pi){if(_pi>=8){var _pj=hs_uncheckedIShiftRA64(_pf,8),_pk=_pg-8|0;_pc=_pj;_pd=_pk;return __continue;}else{return new T2(0,new T(function(){var _pl=hs_uncheckedIShiftRA64(_pf,_pi);return B(_oN(_pl));}),_pg-_pi|0);}}else{return new T2(0,new T(function(){var _pm=hs_uncheckedIShiftRA64(_pf,_pg);return B(_oN(_pm));}),0);}})(_pc,_pd));if(_pe!=__continue){return _pe;}}};return new F(function(){return _pb(_pa,_p6-8|0);});}else{return new T2(0,new T(function(){var _pn=hs_uncheckedIShiftRA64(_p5,_p9);return B(_oN(_pn));}),_p6-_p9|0);}}else{return new T2(0,new T(function(){var _po=hs_uncheckedIShiftRA64(_p5,_p6);return B(_oN(_po));}),0);}},_pp=function(_pq){var _pr=hs_intToInt64(_pq);return E(_pr);},_ps=function(_pt){var _pu=E(_pt);if(!_pu._){return new F(function(){return _pp(_pu.a);});}else{return new F(function(){return I_toInt64(_pu.a);});}},_pv=function(_pw){return I_toInt(_pw)>>>0;},_px=function(_py){var _pz=E(_py);if(!_pz._){return _pz.a>>>0;}else{return new F(function(){return _pv(_pz.a);});}},_pA=function(_pB){var _pC=B(_oI(_pB)),_pD=_pC.a,_pE=_pC.b;if(_pE<0){var _pF=function(_pG){if(!_pG){return new T2(0,E(_pD),B(_lI(_kp, -_pE)));}else{var _pH=B(_p4(B(_ps(_pD)), -_pE));return new T2(0,E(_pH.a),B(_lI(_kp,_pH.b)));}};if(!((B(_px(_pD))&1)>>>0)){return new F(function(){return _pF(1);});}else{return new F(function(){return _pF(0);});}}else{return new T2(0,B(_lI(_pD,_pE)),_kp);}},_pI=function(_pJ){var _pK=B(_pA(E(_pJ)));return new T2(0,E(_pK.a),E(_pK.b));},_pL=new T3(0,_o4,_oH,_pI),_pM=function(_pN){return E(E(_pN).a);},_pO=function(_pP){return E(E(_pP).a);},_pQ=new T1(0,1),_pR=function(_pS){return new F(function(){return _3Z(E(_pS),2147483647);});},_pT=function(_pU,_pV,_pW){if(_pW<=_pV){var _pX=new T(function(){var _pY=_pV-_pU|0,_pZ=function(_q0){return (_q0>=(_pW-_pY|0))?new T2(1,_q0,new T(function(){return B(_pZ(_q0+_pY|0));})):new T2(1,_q0,_4);};return B(_pZ(_pV));});return new T2(1,_pU,_pX);}else{return (_pW<=_pU)?new T2(1,_pU,_4):__Z;}},_q1=function(_q2,_q3,_q4){if(_q4>=_q3){var _q5=new T(function(){var _q6=_q3-_q2|0,_q7=function(_q8){return (_q8<=(_q4-_q6|0))?new T2(1,_q8,new T(function(){return B(_q7(_q8+_q6|0));})):new T2(1,_q8,_4);};return B(_q7(_q3));});return new T2(1,_q2,_q5);}else{return (_q4>=_q2)?new T2(1,_q2,_4):__Z;}},_q9=function(_qa,_qb){if(_qb<_qa){return new F(function(){return _pT(_qa,_qb,-2147483648);});}else{return new F(function(){return _q1(_qa,_qb,2147483647);});}},_qc=function(_qd,_qe){return new F(function(){return _q9(E(_qd),E(_qe));});},_qf=function(_qg,_qh,_qi){if(_qh<_qg){return new F(function(){return _pT(_qg,_qh,_qi);});}else{return new F(function(){return _q1(_qg,_qh,_qi);});}},_qj=function(_qk,_ql,_qm){return new F(function(){return _qf(E(_qk),E(_ql),E(_qm));});},_qn=function(_qo){return E(_qo);},_qp=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_qq=new T(function(){return B(err(_qp));}),_qr=function(_qs){var _qt=E(_qs);return (_qt==(-2147483648))?E(_qq):_qt-1|0;},_qu=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_qv=new T(function(){return B(err(_qu));}),_qw=function(_qx){var _qy=E(_qx);return (_qy==2147483647)?E(_qv):_qy+1|0;},_qz={_:0,a:_qw,b:_qr,c:_qn,d:_qn,e:_pR,f:_qc,g:_44,h:_qj},_qA=function(_qB,_qC){if(_qB<=0){if(_qB>=0){return new F(function(){return quot(_qB,_qC);});}else{if(_qC<=0){return new F(function(){return quot(_qB,_qC);});}else{return quot(_qB+1|0,_qC)-1|0;}}}else{if(_qC>=0){if(_qB>=0){return new F(function(){return quot(_qB,_qC);});}else{if(_qC<=0){return new F(function(){return quot(_qB,_qC);});}else{return quot(_qB+1|0,_qC)-1|0;}}}else{return quot(_qB-1|0,_qC)-1|0;}}},_qD=0,_qE=new T(function(){return B(_l6(_qD));}),_qF=new T(function(){return die(_qE);}),_qG=function(_qH,_qI){var _qJ=E(_qI);switch(_qJ){case -1:var _qK=E(_qH);if(_qK==(-2147483648)){return E(_qF);}else{return new F(function(){return _qA(_qK,-1);});}break;case 0:return E(_l9);default:return new F(function(){return _qA(_qH,_qJ);});}},_qL=function(_qM,_qN){return new F(function(){return _qG(E(_qM),E(_qN));});},_qO=0,_qP=new T2(0,_qF,_qO),_qQ=function(_qR,_qS){var _qT=E(_qR),_qU=E(_qS);switch(_qU){case -1:var _qV=E(_qT);if(_qV==(-2147483648)){return E(_qP);}else{if(_qV<=0){if(_qV>=0){var _qW=quotRemI(_qV,-1);return new T2(0,_qW.a,_qW.b);}else{var _qX=quotRemI(_qV,-1);return new T2(0,_qX.a,_qX.b);}}else{var _qY=quotRemI(_qV-1|0,-1);return new T2(0,_qY.a-1|0,(_qY.b+(-1)|0)+1|0);}}break;case 0:return E(_l9);default:if(_qT<=0){if(_qT>=0){var _qZ=quotRemI(_qT,_qU);return new T2(0,_qZ.a,_qZ.b);}else{if(_qU<=0){var _r0=quotRemI(_qT,_qU);return new T2(0,_r0.a,_r0.b);}else{var _r1=quotRemI(_qT+1|0,_qU);return new T2(0,_r1.a-1|0,(_r1.b+_qU|0)-1|0);}}}else{if(_qU>=0){if(_qT>=0){var _r2=quotRemI(_qT,_qU);return new T2(0,_r2.a,_r2.b);}else{if(_qU<=0){var _r3=quotRemI(_qT,_qU);return new T2(0,_r3.a,_r3.b);}else{var _r4=quotRemI(_qT+1|0,_qU);return new T2(0,_r4.a-1|0,(_r4.b+_qU|0)-1|0);}}}else{var _r5=quotRemI(_qT-1|0,_qU);return new T2(0,_r5.a-1|0,(_r5.b+_qU|0)+1|0);}}}},_r6=function(_r7,_r8){var _r9=E(_r8);switch(_r9){case -1:return E(_qO);case 0:return E(_l9);default:return new F(function(){return _aO(E(_r7),_r9);});}},_ra=function(_rb,_rc){var _rd=E(_rb),_re=E(_rc);switch(_re){case -1:var _rf=E(_rd);if(_rf==(-2147483648)){return E(_qF);}else{return new F(function(){return quot(_rf,-1);});}break;case 0:return E(_l9);default:return new F(function(){return quot(_rd,_re);});}},_rg=function(_rh,_ri){var _rj=E(_rh),_rk=E(_ri);switch(_rk){case -1:var _rl=E(_rj);if(_rl==(-2147483648)){return E(_qP);}else{var _rm=quotRemI(_rl,-1);return new T2(0,_rm.a,_rm.b);}break;case 0:return E(_l9);default:var _rn=quotRemI(_rj,_rk);return new T2(0,_rn.a,_rn.b);}},_ro=function(_rp,_rq){var _rr=E(_rq);switch(_rr){case -1:return E(_qO);case 0:return E(_l9);default:return E(_rp)%_rr;}},_rs=function(_rt){return new F(function(){return _oL(E(_rt));});},_ru=function(_rv){return new T2(0,E(B(_oL(E(_rv)))),E(_pQ));},_rw=function(_rx,_ry){return imul(E(_rx),E(_ry))|0;},_rz=function(_rA,_rB){return E(_rA)+E(_rB)|0;},_rC=function(_rD){var _rE=E(_rD);return (_rE<0)? -_rE:E(_rE);},_rF=function(_rG){return new F(function(){return _lm(_rG);});},_rH=function(_rI){return  -E(_rI);},_rJ=-1,_rK=0,_rL=1,_rM=function(_rN){var _rO=E(_rN);return (_rO>=0)?(E(_rO)==0)?E(_rK):E(_rL):E(_rJ);},_rP={_:0,a:_rz,b:_4f,c:_rw,d:_rH,e:_rC,f:_rM,g:_rF},_rQ=new T3(0,_rP,_4U,_ru),_rR={_:0,a:_rQ,b:_qz,c:_ra,d:_ro,e:_qL,f:_r6,g:_rg,h:_qQ,i:_rs},_rS=new T1(0,2),_rT=function(_rU,_rV){while(1){var _rW=E(_rU);if(!_rW._){var _rX=_rW.a,_rY=E(_rV);if(!_rY._){var _rZ=_rY.a;if(!(imul(_rX,_rZ)|0)){return new T1(0,imul(_rX,_rZ)|0);}else{_rU=new T1(1,I_fromInt(_rX));_rV=new T1(1,I_fromInt(_rZ));continue;}}else{_rU=new T1(1,I_fromInt(_rX));_rV=_rY;continue;}}else{var _s0=E(_rV);if(!_s0._){_rU=_rW;_rV=new T1(1,I_fromInt(_s0.a));continue;}else{return new T1(1,I_mul(_rW.a,_s0.a));}}}},_s1=function(_s2,_s3,_s4){while(1){if(!(_s3%2)){var _s5=B(_rT(_s2,_s2)),_s6=quot(_s3,2);_s2=_s5;_s3=_s6;continue;}else{var _s7=E(_s3);if(_s7==1){return new F(function(){return _rT(_s2,_s4);});}else{var _s5=B(_rT(_s2,_s2)),_s8=B(_rT(_s2,_s4));_s2=_s5;_s3=quot(_s7-1|0,2);_s4=_s8;continue;}}}},_s9=function(_sa,_sb){while(1){if(!(_sb%2)){var _sc=B(_rT(_sa,_sa)),_sd=quot(_sb,2);_sa=_sc;_sb=_sd;continue;}else{var _se=E(_sb);if(_se==1){return E(_sa);}else{return new F(function(){return _s1(B(_rT(_sa,_sa)),quot(_se-1|0,2),_sa);});}}}},_sf=function(_sg){return E(E(_sg).c);},_sh=function(_si){return E(E(_si).a);},_sj=function(_sk){return E(E(_sk).b);},_sl=function(_sm){return E(E(_sm).b);},_sn=function(_so){return E(E(_so).c);},_sp=function(_sq){return E(E(_sq).a);},_sr=new T1(0,0),_ss=new T1(0,2),_st=function(_su){return E(E(_su).g);},_sv=function(_sw){return E(E(_sw).d);},_sx=function(_sy,_sz){var _sA=B(_pM(_sy)),_sB=new T(function(){return B(_pO(_sA));}),_sC=new T(function(){return B(A3(_sv,_sy,_sz,new T(function(){return B(A2(_st,_sB,_ss));})));});return new F(function(){return A3(_sp,B(_sh(B(_sj(_sA)))),_sC,new T(function(){return B(A2(_st,_sB,_sr));}));});},_sD=new T(function(){return B(unCStr("Negative exponent"));}),_sE=new T(function(){return B(err(_sD));}),_sF=function(_sG){return E(E(_sG).c);},_sH=function(_sI,_sJ,_sK,_sL){var _sM=B(_pM(_sJ)),_sN=new T(function(){return B(_pO(_sM));}),_sO=B(_sj(_sM));if(!B(A3(_sn,_sO,_sL,new T(function(){return B(A2(_st,_sN,_sr));})))){if(!B(A3(_sp,B(_sh(_sO)),_sL,new T(function(){return B(A2(_st,_sN,_sr));})))){var _sP=new T(function(){return B(A2(_st,_sN,_ss));}),_sQ=new T(function(){return B(A2(_st,_sN,_pQ));}),_sR=B(_sh(_sO)),_sS=function(_sT,_sU,_sV){while(1){var _sW=B((function(_sX,_sY,_sZ){if(!B(_sx(_sJ,_sY))){if(!B(A3(_sp,_sR,_sY,_sQ))){var _t0=new T(function(){return B(A3(_sF,_sJ,new T(function(){return B(A3(_sl,_sN,_sY,_sQ));}),_sP));});_sT=new T(function(){return B(A3(_sf,_sI,_sX,_sX));});_sU=_t0;_sV=new T(function(){return B(A3(_sf,_sI,_sX,_sZ));});return __continue;}else{return new F(function(){return A3(_sf,_sI,_sX,_sZ);});}}else{var _t1=_sZ;_sT=new T(function(){return B(A3(_sf,_sI,_sX,_sX));});_sU=new T(function(){return B(A3(_sF,_sJ,_sY,_sP));});_sV=_t1;return __continue;}})(_sT,_sU,_sV));if(_sW!=__continue){return _sW;}}},_t2=function(_t3,_t4){while(1){var _t5=B((function(_t6,_t7){if(!B(_sx(_sJ,_t7))){if(!B(A3(_sp,_sR,_t7,_sQ))){var _t8=new T(function(){return B(A3(_sF,_sJ,new T(function(){return B(A3(_sl,_sN,_t7,_sQ));}),_sP));});return new F(function(){return _sS(new T(function(){return B(A3(_sf,_sI,_t6,_t6));}),_t8,_t6);});}else{return E(_t6);}}else{_t3=new T(function(){return B(A3(_sf,_sI,_t6,_t6));});_t4=new T(function(){return B(A3(_sF,_sJ,_t7,_sP));});return __continue;}})(_t3,_t4));if(_t5!=__continue){return _t5;}}};return new F(function(){return _t2(_sK,_sL);});}else{return new F(function(){return A2(_st,_sI,_pQ);});}}else{return E(_sE);}},_t9=new T(function(){return B(err(_sD));}),_ta=function(_tb,_tc){var _td=B(_oI(_tc)),_te=_td.a,_tf=_td.b,_tg=new T(function(){return B(_pO(new T(function(){return B(_pM(_tb));})));});if(_tf<0){var _th= -_tf;if(_th>=0){var _ti=E(_th);if(!_ti){var _tj=E(_pQ);}else{var _tj=B(_s9(_rS,_ti));}if(!B(_le(_tj,_lH))){var _tk=B(_ly(_te,_tj));return new T2(0,new T(function(){return B(A2(_st,_tg,_tk.a));}),new T(function(){return B(_la(_tk.b,_tf));}));}else{return E(_l9);}}else{return E(_t9);}}else{var _tl=new T(function(){var _tm=new T(function(){return B(_sH(_tg,_rR,new T(function(){return B(A2(_st,_tg,_rS));}),_tf));});return B(A3(_sf,_tg,new T(function(){return B(A2(_st,_tg,_te));}),_tm));});return new T2(0,_tl,_nD);}},_tn=function(_to){return E(E(_to).a);},_tp=function(_tq,_tr){var _ts=B(_ta(_tq,E(_tr))),_tt=_ts.a;if(E(_ts.b)<=0){return E(_tt);}else{var _tu=B(_pO(B(_pM(_tq))));return new F(function(){return A3(_tn,_tu,_tt,new T(function(){return B(A2(_st,_tu,_kp));}));});}},_tv=function(_tw,_tx){var _ty=B(_ta(_tw,E(_tx))),_tz=_ty.a;if(E(_ty.b)>=0){return E(_tz);}else{var _tA=B(_pO(B(_pM(_tw))));return new F(function(){return A3(_sl,_tA,_tz,new T(function(){return B(A2(_st,_tA,_kp));}));});}},_tB=function(_tC,_tD){var _tE=B(_ta(_tC,E(_tD)));return new T2(0,_tE.a,_tE.b);},_tF=function(_tG,_tH){var _tI=B(_ta(_tG,_tH)),_tJ=_tI.a,_tK=E(_tI.b),_tL=new T(function(){var _tM=B(_pO(B(_pM(_tG))));if(_tK>=0){return B(A3(_tn,_tM,_tJ,new T(function(){return B(A2(_st,_tM,_kp));})));}else{return B(A3(_sl,_tM,_tJ,new T(function(){return B(A2(_st,_tM,_kp));})));}}),_tN=function(_tO){var _tP=_tO-0.5;return (_tP>=0)?(E(_tP)==0)?(!B(_sx(_tG,_tJ)))?E(_tL):E(_tJ):E(_tL):E(_tJ);},_tQ=E(_tK);if(!_tQ){return new F(function(){return _tN(0);});}else{if(_tQ<=0){var _tR= -_tQ-0.5;return (_tR>=0)?(E(_tR)==0)?(!B(_sx(_tG,_tJ)))?E(_tL):E(_tJ):E(_tL):E(_tJ);}else{return new F(function(){return _tN(_tQ);});}}},_tS=function(_tT,_tU){return new F(function(){return _tF(_tT,E(_tU));});},_tV=function(_tW,_tX){return E(B(_ta(_tW,E(_tX))).a);},_tY={_:0,a:_pL,b:_o8,c:_tB,d:_tV,e:_tS,f:_tp,g:_tv},_tZ=new T1(0,1),_u0=function(_u1,_u2){var _u3=E(_u1);return new T2(0,_u3,new T(function(){var _u4=B(_u0(B(_lp(_u3,_u2)),_u2));return new T2(1,_u4.a,_u4.b);}));},_u5=function(_u6){var _u7=B(_u0(_u6,_tZ));return new T2(1,_u7.a,_u7.b);},_u8=function(_u9,_ua){var _ub=B(_u0(_u9,new T(function(){return B(_mR(_ua,_u9));})));return new T2(1,_ub.a,_ub.b);},_uc=new T1(0,0),_ud=function(_ue,_uf){var _ug=E(_ue);if(!_ug._){var _uh=_ug.a,_ui=E(_uf);return (_ui._==0)?_uh>=_ui.a:I_compareInt(_ui.a,_uh)<=0;}else{var _uj=_ug.a,_uk=E(_uf);return (_uk._==0)?I_compareInt(_uj,_uk.a)>=0:I_compare(_uj,_uk.a)>=0;}},_ul=function(_um,_un,_uo){if(!B(_ud(_un,_uc))){var _up=function(_uq){return (!B(_m1(_uq,_uo)))?new T2(1,_uq,new T(function(){return B(_up(B(_lp(_uq,_un))));})):__Z;};return new F(function(){return _up(_um);});}else{var _ur=function(_us){return (!B(_lS(_us,_uo)))?new T2(1,_us,new T(function(){return B(_ur(B(_lp(_us,_un))));})):__Z;};return new F(function(){return _ur(_um);});}},_ut=function(_uu,_uv,_uw){return new F(function(){return _ul(_uu,B(_mR(_uv,_uu)),_uw);});},_ux=function(_uy,_uz){return new F(function(){return _ul(_uy,_tZ,_uz);});},_uA=function(_uB){return new F(function(){return _lm(_uB);});},_uC=function(_uD){return new F(function(){return _mR(_uD,_tZ);});},_uE=function(_uF){return new F(function(){return _lp(_uF,_tZ);});},_uG=function(_uH){return new F(function(){return _oL(E(_uH));});},_uI={_:0,a:_uE,b:_uC,c:_uG,d:_uA,e:_u5,f:_u8,g:_ux,h:_ut},_uJ=function(_uK,_uL){while(1){var _uM=E(_uK);if(!_uM._){var _uN=E(_uM.a);if(_uN==(-2147483648)){_uK=new T1(1,I_fromInt(-2147483648));continue;}else{var _uO=E(_uL);if(!_uO._){return new T1(0,B(_qA(_uN,_uO.a)));}else{_uK=new T1(1,I_fromInt(_uN));_uL=_uO;continue;}}}else{var _uP=_uM.a,_uQ=E(_uL);return (_uQ._==0)?new T1(1,I_div(_uP,I_fromInt(_uQ.a))):new T1(1,I_div(_uP,_uQ.a));}}},_uR=function(_uS,_uT){if(!B(_le(_uT,_sr))){return new F(function(){return _uJ(_uS,_uT);});}else{return E(_l9);}},_uU=function(_uV,_uW){while(1){var _uX=E(_uV);if(!_uX._){var _uY=E(_uX.a);if(_uY==(-2147483648)){_uV=new T1(1,I_fromInt(-2147483648));continue;}else{var _uZ=E(_uW);if(!_uZ._){var _v0=_uZ.a;return new T2(0,new T1(0,B(_qA(_uY,_v0))),new T1(0,B(_aO(_uY,_v0))));}else{_uV=new T1(1,I_fromInt(_uY));_uW=_uZ;continue;}}}else{var _v1=E(_uW);if(!_v1._){_uV=_uX;_uW=new T1(1,I_fromInt(_v1.a));continue;}else{var _v2=I_divMod(_uX.a,_v1.a);return new T2(0,new T1(1,_v2.a),new T1(1,_v2.b));}}}},_v3=function(_v4,_v5){if(!B(_le(_v5,_sr))){var _v6=B(_uU(_v4,_v5));return new T2(0,_v6.a,_v6.b);}else{return E(_l9);}},_v7=function(_v8,_v9){while(1){var _va=E(_v8);if(!_va._){var _vb=E(_va.a);if(_vb==(-2147483648)){_v8=new T1(1,I_fromInt(-2147483648));continue;}else{var _vc=E(_v9);if(!_vc._){return new T1(0,B(_aO(_vb,_vc.a)));}else{_v8=new T1(1,I_fromInt(_vb));_v9=_vc;continue;}}}else{var _vd=_va.a,_ve=E(_v9);return (_ve._==0)?new T1(1,I_mod(_vd,I_fromInt(_ve.a))):new T1(1,I_mod(_vd,_ve.a));}}},_vf=function(_vg,_vh){if(!B(_le(_vh,_sr))){return new F(function(){return _v7(_vg,_vh);});}else{return E(_l9);}},_vi=function(_vj,_vk){while(1){var _vl=E(_vj);if(!_vl._){var _vm=E(_vl.a);if(_vm==(-2147483648)){_vj=new T1(1,I_fromInt(-2147483648));continue;}else{var _vn=E(_vk);if(!_vn._){return new T1(0,quot(_vm,_vn.a));}else{_vj=new T1(1,I_fromInt(_vm));_vk=_vn;continue;}}}else{var _vo=_vl.a,_vp=E(_vk);return (_vp._==0)?new T1(0,I_toInt(I_quot(_vo,I_fromInt(_vp.a)))):new T1(1,I_quot(_vo,_vp.a));}}},_vq=function(_vr,_vs){if(!B(_le(_vs,_sr))){return new F(function(){return _vi(_vr,_vs);});}else{return E(_l9);}},_vt=function(_vu,_vv){if(!B(_le(_vv,_sr))){var _vw=B(_ly(_vu,_vv));return new T2(0,_vw.a,_vw.b);}else{return E(_l9);}},_vx=function(_vy,_vz){while(1){var _vA=E(_vy);if(!_vA._){var _vB=E(_vA.a);if(_vB==(-2147483648)){_vy=new T1(1,I_fromInt(-2147483648));continue;}else{var _vC=E(_vz);if(!_vC._){return new T1(0,_vB%_vC.a);}else{_vy=new T1(1,I_fromInt(_vB));_vz=_vC;continue;}}}else{var _vD=_vA.a,_vE=E(_vz);return (_vE._==0)?new T1(1,I_rem(_vD,I_fromInt(_vE.a))):new T1(1,I_rem(_vD,_vE.a));}}},_vF=function(_vG,_vH){if(!B(_le(_vH,_sr))){return new F(function(){return _vx(_vG,_vH);});}else{return E(_l9);}},_vI=function(_vJ){return E(_vJ);},_vK=function(_vL){return E(_vL);},_vM=function(_vN){var _vO=E(_vN);if(!_vO._){var _vP=E(_vO.a);return (_vP==(-2147483648))?E(_nv):(_vP<0)?new T1(0, -_vP):E(_vO);}else{var _vQ=_vO.a;return (I_compareInt(_vQ,0)>=0)?E(_vO):new T1(1,I_negate(_vQ));}},_vR=new T1(0,0),_vS=new T1(0,-1),_vT=function(_vU){var _vV=E(_vU);if(!_vV._){var _vW=_vV.a;return (_vW>=0)?(E(_vW)==0)?E(_vR):E(_m0):E(_vS);}else{var _vX=I_compareInt(_vV.a,0);return (_vX<=0)?(E(_vX)==0)?E(_vR):E(_vS):E(_m0);}},_vY={_:0,a:_lp,b:_mR,c:_rT,d:_nw,e:_vM,f:_vT,g:_vK},_vZ=function(_w0,_w1){var _w2=E(_w0);if(!_w2._){var _w3=_w2.a,_w4=E(_w1);return (_w4._==0)?_w3!=_w4.a:(I_compareInt(_w4.a,_w3)==0)?false:true;}else{var _w5=_w2.a,_w6=E(_w1);return (_w6._==0)?(I_compareInt(_w5,_w6.a)==0)?false:true:(I_compare(_w5,_w6.a)==0)?false:true;}},_w7=new T2(0,_le,_vZ),_w8=function(_w9,_wa){return (!B(_mC(_w9,_wa)))?E(_w9):E(_wa);},_wb=function(_wc,_wd){return (!B(_mC(_wc,_wd)))?E(_wd):E(_wc);},_we={_:0,a:_w7,b:_kq,c:_m1,d:_mC,e:_lS,f:_ud,g:_w8,h:_wb},_wf=function(_wg){return new T2(0,E(_wg),E(_pQ));},_wh=new T3(0,_vY,_we,_wf),_wi={_:0,a:_wh,b:_uI,c:_vq,d:_vF,e:_uR,f:_vf,g:_vt,h:_v3,i:_vI},_wj=function(_wk){return E(E(_wk).a);},_wl=function(_wm){return E(E(_wm).b);},_wn=function(_wo){return E(E(_wo).b);},_wp=function(_wq){return E(E(_wq).g);},_wr=new T1(0,1),_ws=function(_wt){return E(E(_wt).d);},_wu=function(_wv,_ww,_wx){var _wy=B(_wl(_wv)),_wz=B(_wj(_wy)),_wA=new T(function(){var _wB=new T(function(){var _wC=new T(function(){var _wD=new T(function(){return B(A3(_wp,_wv,_wi,new T(function(){return B(A3(_wn,_wy,_ww,_wx));})));});return B(A2(_st,_wz,_wD));}),_wE=new T(function(){return B(A2(_ws,_wz,new T(function(){return B(A2(_st,_wz,_wr));})));});return B(A3(_sf,_wz,_wE,_wC));});return B(A3(_sf,_wz,_wB,_wx));});return new F(function(){return A3(_tn,_wz,_ww,_wA);});},_wF=function(_wG){var _wH=new T(function(){var _wI=E(E(_wG).b);return new T3(0,new T(function(){return B(_wu(_tY,_wI.a,_1r));}),new T(function(){return B(_wu(_tY,_wI.b,_5Y));}),_wI.c);});return new T5(0,new T(function(){return E(E(_wG).a);}),_wH,new T(function(){return E(E(_wG).c);}),new T(function(){return E(E(_wG).d);}),new T(function(){return E(E(_wG).e);}));},_wJ=function(_wK,_){var _wL=B(_5w(_4V,_6F,_j0,_wK)),_wM=B(_hI(E(_wL.a),E(_wL.b),_wL.c,_wL.d,_wL,_)),_wN=new T(function(){return B(_je(E(_wM).a));}),_wO=function(_wP){var _wQ=E(_wP);return (_wQ==1)?E(new T2(1,_wN,_4)):new T2(1,_wN,new T(function(){return B(_wO(_wQ-1|0));}));},_wR=B(_6G(B(_wO(5)),new T(function(){return E(E(_wM).b);}),_)),_wS=new T(function(){var _wT=new T(function(){return B(_5w(_4V,_6F,_iI,new T(function(){return E(E(_wR).b);})));});return B(_5w(_4V,_6F,_wF,_wT));});return new T2(0,_5,_wS);},_wU=new T(function(){return eval("refresh");}),_wV=function(_wW,_){var _wX=__app0(E(_wU)),_wY=B(A(_5w,[_4V,_2d,_5Z,_wW,_])),_wZ=B(_wJ(_wW,_));return new T(function(){return E(E(_wZ).b);});},_x0=function(_x1,_x2,_x3){var _x4=function(_){var _x5=B(_wV(_x1,_));return new T(function(){return B(A1(_x3,new T1(1,_x5)));});};return new T1(0,_x4);},_x6=new T0(2),_x7=function(_x8,_x9,_xa){return function(_){var _xb=E(_x8),_xc=rMV(_xb),_xd=E(_xc);if(!_xd._){var _xe=new T(function(){var _xf=new T(function(){return B(A1(_xa,_5));});return B(_0(_xd.b,new T2(1,new T2(0,_x9,function(_xg){return E(_xf);}),_4)));}),_=wMV(_xb,new T2(0,_xd.a,_xe));return _x6;}else{var _xh=E(_xd.a);if(!_xh._){var _=wMV(_xb,new T2(0,_x9,_4));return new T(function(){return B(A1(_xa,_5));});}else{var _=wMV(_xb,new T1(1,_xh.b));return new T1(1,new T2(1,new T(function(){return B(A1(_xa,_5));}),new T2(1,new T(function(){return B(A2(_xh.a,_x9,_19));}),_4)));}}};},_xi=function(_xj){return E(E(_xj).b);},_xk=function(_xl,_xm,_xn){var _xo=new T(function(){return new T1(0,B(_x7(_xm,_xn,_19)));}),_xp=function(_xq){return new T1(1,new T2(1,new T(function(){return B(A1(_xq,_5));}),new T2(1,_xo,_4)));};return new F(function(){return A2(_xi,_xl,_xp);});},_xr=new T1(1,_4),_xs=function(_xt,_xu){return function(_){var _xv=E(_xt),_xw=rMV(_xv),_xx=E(_xw);if(!_xx._){var _xy=_xx.a,_xz=E(_xx.b);if(!_xz._){var _=wMV(_xv,_xr);return new T(function(){return B(A1(_xu,_xy));});}else{var _xA=E(_xz.a),_=wMV(_xv,new T2(0,_xA.a,_xz.b));return new T1(1,new T2(1,new T(function(){return B(A1(_xu,_xy));}),new T2(1,new T(function(){return B(A1(_xA.b,_19));}),_4)));}}else{var _xB=new T(function(){var _xC=function(_xD){var _xE=new T(function(){return B(A1(_xu,_xD));});return function(_xF){return E(_xE);};};return B(_0(_xx.a,new T2(1,_xC,_4)));}),_=wMV(_xv,new T1(1,_xB));return _x6;}};},_xG=function(_){return new F(function(){return __jsNull();});},_xH=function(_xI){var _xJ=B(A1(_xI,_));return E(_xJ);},_xK=new T(function(){return B(_xH(_xG));}),_xL=new T(function(){return E(_xK);}),_xM=new T(function(){return eval("window.requestAnimationFrame");}),_xN=new T1(1,_4),_xO=function(_xP){var _xQ=new T(function(){return B(_xR(_));}),_xS=new T(function(){var _xT=function(_xU){return E(_xQ);},_xV=function(_){var _xW=nMV(_xN),_xX=_xW,_xY=new T(function(){return new T1(0,B(_x7(_xX,_5,_19)));}),_xZ=function(_){var _y0=__createJSFunc(2,function(_y1,_){var _y2=B(_c(_xY,_4,_));return _xL;}),_y3=__app1(E(_xM),_y0);return new T(function(){return new T1(0,B(_xs(_xX,_xT)));});};return new T1(0,_xZ);};return B(A(_xk,[_1i,_xP,_5,function(_y4){return E(new T1(0,_xV));}]));}),_xR=function(_y5){return E(_xS);};return new F(function(){return _xR(_);});},_y6=function(_y7){return E(E(_y7).a);},_y8=function(_y9){return E(E(_y9).d);},_ya=function(_yb){return E(E(_yb).c);},_yc=function(_yd){return E(E(_yd).c);},_ye=new T1(1,_4),_yf=function(_yg){var _yh=function(_){var _yi=nMV(_ye);return new T(function(){return B(A1(_yg,_yi));});};return new T1(0,_yh);},_yj=function(_yk,_yl){var _ym=new T(function(){return B(_yc(_yk));}),_yn=B(_y6(_yk)),_yo=function(_yp){var _yq=new T(function(){return B(A1(_ym,new T(function(){return B(A1(_yl,_yp));})));});return new F(function(){return A3(_ya,_yn,_yq,new T(function(){return B(A2(_y8,_yn,_yp));}));});};return new F(function(){return A3(_10,_yn,new T(function(){return B(A2(_xi,_yk,_yf));}),_yo);});},_yr=function(_ys,_yt){return new T1(0,B(_xs(_ys,_yt)));},_yu=function(_yv,_yw,_yx){var _yy=new T(function(){return B(_y6(_yv));}),_yz=new T(function(){return B(A2(_y8,_yy,_5));}),_yA=function(_yB,_yC){var _yD=new T(function(){var _yE=new T(function(){return B(A2(_xi,_yv,function(_yF){return new F(function(){return _yr(_yC,_yF);});}));});return B(A3(_10,_yy,_yE,new T(function(){return B(A1(_yx,_yB));})));});return new F(function(){return A3(_10,_yy,_yD,function(_yG){var _yH=E(_yG);if(!_yH._){return E(_yz);}else{return new F(function(){return _yA(_yH.a,_yC);});}});});};return new F(function(){return _yj(_yv,function(_yF){return new F(function(){return _yA(_yw,_yF);});});});},_yI=new T(function(){return B(A(_yu,[_1i,_1N,_x0,_xO]));}),_yJ=function(_){return new F(function(){return _c(_yI,_4,_);});},_yK=function(_){return new F(function(){return _yJ(_);});};
var hasteMain = function() {B(A(_yK, [0]));};window.onload = hasteMain;