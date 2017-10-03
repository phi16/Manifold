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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=function(_i,_j,_k){return new F(function(){return A1(_i,function(_l){return new F(function(){return A2(_j,_l,_k);});});});},_m=function(_n,_o,_p){var _q=function(_r){var _s=new T(function(){return B(A1(_p,_r));});return new F(function(){return A1(_o,function(_t){return E(_s);});});};return new F(function(){return A1(_n,_q);});},_u=function(_v,_w,_x){var _y=new T(function(){return B(A1(_w,function(_z){return new F(function(){return A1(_x,_z);});}));});return new F(function(){return A1(_v,function(_A){return E(_y);});});},_B=function(_C,_D,_E){var _F=function(_G){var _H=function(_I){return new F(function(){return A1(_E,new T(function(){return B(A1(_G,_I));}));});};return new F(function(){return A1(_D,_H);});};return new F(function(){return A1(_C,_F);});},_J=function(_K,_L){return new F(function(){return A1(_L,_K);});},_M=function(_N,_O,_P){var _Q=new T(function(){return B(A1(_P,_N));});return new F(function(){return A1(_O,function(_R){return E(_Q);});});},_S=function(_T,_U,_V){var _W=function(_X){return new F(function(){return A1(_V,new T(function(){return B(A1(_T,_X));}));});};return new F(function(){return A1(_U,_W);});},_Y=new T2(0,_S,_M),_Z=new T5(0,_Y,_J,_B,_u,_m),_10=function(_11){return E(E(_11).b);},_12=function(_13,_14){return new F(function(){return A3(_10,_15,_13,function(_16){return E(_14);});});},_17=function(_18){return new F(function(){return err(_18);});},_15=new T(function(){return new T5(0,_Z,_h,_12,_J,_17);}),_19=function(_1a){return new T0(2);},_1b=function(_1c){var _1d=new T(function(){return B(A1(_1c,_19));}),_1e=function(_1f){return new T1(1,new T2(1,new T(function(){return B(A1(_1f,_5));}),new T2(1,_1d,_4)));};return E(_1e);},_1g=function(_1h){return E(_1h);},_1i=new T3(0,_15,_1g,_1b),_1j=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1k=new T(function(){return B(err(_1j));}),_1l=0,_1m=new T3(0,_1l,_1l,_1l),_1n=1,_1o=new T3(0,_1l,_1n,_1l),_1p=40,_1q=new T1(0,_1p),_1r=1.5707963267948966,_1s=80,_1t=new T(function(){return eval("scrW");}),_1u=new T(function(){return E(_1t)/2-1;}),_1v=new T3(0,_1u,_1s,_1r),_1w=2.4867959858108646e-7,_1x=1.9894367886486917e-4,_1y=new T3(0,_1x,_1x,_1w),_1z=new T5(0,_1q,_1v,_1m,_1o,_1y),_1A=60,_1B=new T(function(){return E(_1t)/2-2;}),_1C=new T3(0,_1B,_1A,_1r),_1D=new T5(0,_1q,_1C,_1m,_1o,_1y),_1E=2,_1F=0,_1G=new T(function(){return E(_1t)/2-3;}),_1H=100,_1I=new T3(0,_1G,_1H,_1r),_1J=new T5(0,_1q,_1I,_1m,_1o,_1y),_1K=function(_){var _1L=newArr(3,_1k),_=_1L[0]=_1D,_=_1L[1]=_1z,_=_1L[2]=_1J;return new T4(0,E(_1F),E(_1E),3,_1L);},_1M=function(_1N){var _1O=B(A1(_1N,_));return E(_1O);},_1P=new T(function(){return B(_1M(_1K));}),_1Q=function(_1R,_1S,_){var _1T=B(A1(_1R,_)),_1U=B(A1(_1S,_));return _1T;},_1V=function(_1W,_1X,_){var _1Y=B(A1(_1W,_)),_1Z=B(A1(_1X,_));return new T(function(){return B(A1(_1Y,_1Z));});},_20=function(_21,_22,_){var _23=B(A1(_22,_));return _21;},_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=new T2(0,_24,_20),_29=function(_2a,_){return _2a;},_2b=function(_2c,_2d,_){var _2e=B(A1(_2c,_));return new F(function(){return A1(_2d,_);});},_2f=new T5(0,_28,_29,_1V,_2b,_1Q),_2g=function(_2h){var _2i=E(_2h);return (E(_2i.b)-E(_2i.a)|0)+1|0;},_2j=function(_2k,_2l){var _2m=E(_2k),_2n=E(_2l);return (E(_2m.a)>_2n)?false:_2n<=E(_2m.b);},_2o=function(_2p,_2q){var _2r=jsShowI(_2p);return new F(function(){return _0(fromJSStr(_2r),_2q);});},_2s=41,_2t=40,_2u=function(_2v,_2w,_2x){if(_2w>=0){return new F(function(){return _2o(_2w,_2x);});}else{if(_2v<=6){return new F(function(){return _2o(_2w,_2x);});}else{return new T2(1,_2t,new T(function(){var _2y=jsShowI(_2w);return B(_0(fromJSStr(_2y),new T2(1,_2s,_2x)));}));}}},_2z=function(_2A){return new F(function(){return _2u(0,E(_2A),_4);});},_2B=function(_2C,_2D,_2E){return new F(function(){return _2u(E(_2C),E(_2D),_2E);});},_2F=44,_2G=93,_2H=91,_2I=function(_2J,_2K,_2L){var _2M=E(_2K);if(!_2M._){return new F(function(){return unAppCStr("[]",_2L);});}else{var _2N=new T(function(){var _2O=new T(function(){var _2P=function(_2Q){var _2R=E(_2Q);if(!_2R._){return E(new T2(1,_2G,_2L));}else{var _2S=new T(function(){return B(A2(_2J,_2R.a,new T(function(){return B(_2P(_2R.b));})));});return new T2(1,_2F,_2S);}};return B(_2P(_2M.b));});return B(A2(_2J,_2M.a,_2O));});return new T2(1,_2H,_2N);}},_2T=function(_2U,_2V){return new F(function(){return _2u(0,E(_2U),_2V);});},_2W=function(_2X,_2Y){return new F(function(){return _2I(_2T,_2X,_2Y);});},_2Z=new T3(0,_2B,_2z,_2W),_30=0,_31=function(_32,_33,_34){return new F(function(){return A1(_32,new T2(1,_2F,new T(function(){return B(A1(_33,_34));})));});},_35=new T(function(){return B(unCStr(": empty list"));}),_36=new T(function(){return B(unCStr("Prelude."));}),_37=function(_38){return new F(function(){return err(B(_0(_36,new T(function(){return B(_0(_38,_35));},1))));});},_39=new T(function(){return B(unCStr("foldr1"));}),_3a=new T(function(){return B(_37(_39));}),_3b=function(_3c,_3d){var _3e=E(_3d);if(!_3e._){return E(_3a);}else{var _3f=_3e.a,_3g=E(_3e.b);if(!_3g._){return E(_3f);}else{return new F(function(){return A2(_3c,_3f,new T(function(){return B(_3b(_3c,_3g));}));});}}},_3h=new T(function(){return B(unCStr(" out of range "));}),_3i=new T(function(){return B(unCStr("}.index: Index "));}),_3j=new T(function(){return B(unCStr("Ix{"));}),_3k=new T2(1,_2s,_4),_3l=new T2(1,_2s,_3k),_3m=0,_3n=function(_3o){return E(E(_3o).a);},_3p=function(_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=new T(function(){var _3z=new T(function(){return B(A3(_3b,_31,new T2(1,new T(function(){return B(A3(_3n,_3s,_3m,_3t));}),new T2(1,new T(function(){return B(A3(_3n,_3s,_3m,_3u));}),_4)),_3l));});return B(_0(_3h,new T2(1,_2t,new T2(1,_2t,_3z))));});return B(A(_3n,[_3s,_30,_3r,new T2(1,_2s,_3y)]));});return B(_0(_3i,new T2(1,_2t,_3x)));},1);return B(_0(_3q,_3w));},1);return new F(function(){return err(B(_0(_3j,_3v)));});},_3A=function(_3B,_3C,_3D,_3E,_3F){return new F(function(){return _3p(_3B,_3C,_3F,_3D,_3E);});},_3G=function(_3H,_3I,_3J,_3K){var _3L=E(_3J);return new F(function(){return _3A(_3H,_3I,_3L.a,_3L.b,_3K);});},_3M=function(_3N,_3O,_3P,_3Q){return new F(function(){return _3G(_3Q,_3P,_3O,_3N);});},_3R=new T(function(){return B(unCStr("Int"));}),_3S=function(_3T,_3U){return new F(function(){return _3M(_2Z,_3U,_3T,_3R);});},_3V=function(_3W,_3X){var _3Y=E(_3W),_3Z=E(_3Y.a),_40=E(_3X);if(_3Z>_40){return new F(function(){return _3S(_40,_3Y);});}else{if(_40>E(_3Y.b)){return new F(function(){return _3S(_40,_3Y);});}else{return _40-_3Z|0;}}},_41=function(_42,_43){if(_42<=_43){var _44=function(_45){return new T2(1,_45,new T(function(){if(_45!=_43){return B(_44(_45+1|0));}else{return __Z;}}));};return new F(function(){return _44(_42);});}else{return __Z;}},_46=function(_47,_48){return new F(function(){return _41(E(_47),E(_48));});},_49=function(_4a){var _4b=E(_4a);return new F(function(){return _46(_4b.a,_4b.b);});},_4c=function(_4d){var _4e=E(_4d),_4f=E(_4e.a),_4g=E(_4e.b);return (_4f>_4g)?E(_30):(_4g-_4f|0)+1|0;},_4h=function(_4i,_4j){return E(_4i)-E(_4j)|0;},_4k=function(_4l,_4m){return new F(function(){return _4h(_4m,E(_4l).a);});},_4n=function(_4o,_4p){return E(_4o)==E(_4p);},_4q=function(_4r,_4s){return E(_4r)!=E(_4s);},_4t=new T2(0,_4n,_4q),_4u=function(_4v,_4w){var _4x=E(_4v),_4y=E(_4w);return (_4x>_4y)?E(_4x):E(_4y);},_4z=function(_4A,_4B){var _4C=E(_4A),_4D=E(_4B);return (_4C>_4D)?E(_4D):E(_4C);},_4E=function(_4F,_4G){return (_4F>=_4G)?(_4F!=_4G)?2:1:0;},_4H=function(_4I,_4J){return new F(function(){return _4E(E(_4I),E(_4J));});},_4K=function(_4L,_4M){return E(_4L)>=E(_4M);},_4N=function(_4O,_4P){return E(_4O)>E(_4P);},_4Q=function(_4R,_4S){return E(_4R)<=E(_4S);},_4T=function(_4U,_4V){return E(_4U)<E(_4V);},_4W={_:0,a:_4t,b:_4H,c:_4T,d:_4Q,e:_4N,f:_4K,g:_4u,h:_4z},_4X={_:0,a:_4W,b:_49,c:_3V,d:_4k,e:_2j,f:_4c,g:_2g},_4Y=function(_4Z){return E(E(_4Z).a);},_50=function(_51,_52){return new T2(1,_51,_52);},_53=function(_54){return E(E(_54).c);},_55=function(_56,_57){var _58=E(_57);return new T2(0,_58.a,_58.b);},_59=function(_5a){return E(E(_5a).a);},_5b=new T(function(){return B(unCStr("Negative range size"));}),_5c=new T(function(){return B(err(_5b));}),_5d=function(_5e){return E(E(_5e).f);},_5f=function(_5g,_5h,_5i){var _5j=E(_5h),_5k=_5j.a,_5l=_5j.b,_5m=function(_){var _5n=B(A2(_5d,_5g,_5j));if(_5n>=0){var _5o=newArr(_5n,_1k),_5p=_5o,_5q=E(_5n);if(!_5q){return new T(function(){return new T4(0,E(_5k),E(_5l),0,_5p);});}else{var _5r=function(_5s,_5t,_){while(1){var _5u=E(_5s);if(!_5u._){return E(_);}else{var _=_5p[_5t]=_5u.a;if(_5t!=(_5q-1|0)){var _5v=_5t+1|0;_5s=_5u.b;_5t=_5v;continue;}else{return E(_);}}}},_=B(_5r(_5i,0,_));return new T(function(){return new T4(0,E(_5k),E(_5l),_5q,_5p);});}}else{return E(_5c);}};return new F(function(){return _1M(_5m);});},_5w=function(_5x){return E(E(_5x).b);},_5y=function(_5z,_5A,_5B,_5C){var _5D=new T(function(){var _5E=E(_5C),_5F=_5E.c-1|0,_5G=new T(function(){return B(A2(_5w,_5A,_4));});if(0<=_5F){var _5H=new T(function(){return B(_4Y(_5A));}),_5I=function(_5J){var _5K=new T(function(){var _5L=new T(function(){return B(A1(_5B,new T(function(){return E(_5E.d[_5J]);})));});return B(A3(_59,_5H,_50,_5L));});return new F(function(){return A3(_53,_5A,_5K,new T(function(){if(_5J!=_5F){return B(_5I(_5J+1|0));}else{return E(_5G);}}));});};return B(_5I(0));}else{return E(_5G);}}),_5M=new T(function(){return B(_55(_5z,_5C));});return new F(function(){return A3(_59,B(_4Y(_5A)),function(_5N){return new F(function(){return _5f(_5z,_5M,_5N);});},_5D);});},_5O=new T(function(){return eval("draw");}),_5P=function(_){return _5;},_5Q=new T(function(){return eval("drawCircle");}),_5R=function(_5S,_5T,_){var _5U=E(_5S);if(!_5U._){var _5V=E(_5T),_5W=__app4(E(_5Q),E(_5V.a),E(_5V.b),E(_5V.c),E(_5U.a));return new F(function(){return _5P(_);});}else{return _5;}},_5X=function(_5Y,_){var _5Z=E(_5Y);return new F(function(){return _5R(_5Z.a,_5Z.b,_);});},_60=function(_61){return E(_61);},_62=function(_63){return E(_63);},_64=function(_65,_66){return E(_66);},_67=function(_68,_69){return E(_68);},_6a=function(_6b){return E(_6b);},_6c=new T2(0,_6a,_67),_6d=function(_6e,_6f){return E(_6e);},_6g=new T5(0,_6c,_62,_60,_64,_6d),_6h=function(_6i,_6j,_){while(1){var _6k=B((function(_6l,_6m,_){var _6n=E(_6l);if(!_6n._){return new T2(0,_5,_6m);}else{var _6o=B(A2(_6n.a,_6m,_));_6i=_6n.b;_6j=new T(function(){return E(E(_6o).b);});return __continue;}})(_6i,_6j,_));if(_6k!=__continue){return _6k;}}},_6p="y",_6q="x",_6r=function(_6s,_){var _6t=__get(_6s,E(_6q)),_6u=__get(_6s,E(_6p));return new T2(0,_6t,_6u);},_6v=function(_6w,_){var _6x=E(_6w);if(!_6x._){return _4;}else{var _6y=B(_6r(E(_6x.a),_)),_6z=B(_6v(_6x.b,_));return new T2(1,_6y,_6z);}},_6A=new T(function(){return B(unCStr("base"));}),_6B=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_6C=new T(function(){return B(unCStr("IOException"));}),_6D=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_6A,_6B,_6C),_6E=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_6D,_4,_4),_6F=function(_6G){return E(_6E);},_6H=function(_6I){return E(E(_6I).a);},_6J=function(_6K,_6L,_6M){var _6N=B(A1(_6K,_)),_6O=B(A1(_6L,_)),_6P=hs_eqWord64(_6N.a,_6O.a);if(!_6P){return __Z;}else{var _6Q=hs_eqWord64(_6N.b,_6O.b);return (!_6Q)?__Z:new T1(1,_6M);}},_6R=function(_6S){var _6T=E(_6S);return new F(function(){return _6J(B(_6H(_6T.a)),_6F,_6T.b);});},_6U=new T(function(){return B(unCStr(": "));}),_6V=new T(function(){return B(unCStr(")"));}),_6W=new T(function(){return B(unCStr(" ("));}),_6X=new T(function(){return B(unCStr("interrupted"));}),_6Y=new T(function(){return B(unCStr("system error"));}),_6Z=new T(function(){return B(unCStr("unsatisified constraints"));}),_70=new T(function(){return B(unCStr("user error"));}),_71=new T(function(){return B(unCStr("permission denied"));}),_72=new T(function(){return B(unCStr("illegal operation"));}),_73=new T(function(){return B(unCStr("end of file"));}),_74=new T(function(){return B(unCStr("resource exhausted"));}),_75=new T(function(){return B(unCStr("resource busy"));}),_76=new T(function(){return B(unCStr("does not exist"));}),_77=new T(function(){return B(unCStr("already exists"));}),_78=new T(function(){return B(unCStr("resource vanished"));}),_79=new T(function(){return B(unCStr("timeout"));}),_7a=new T(function(){return B(unCStr("unsupported operation"));}),_7b=new T(function(){return B(unCStr("hardware fault"));}),_7c=new T(function(){return B(unCStr("inappropriate type"));}),_7d=new T(function(){return B(unCStr("invalid argument"));}),_7e=new T(function(){return B(unCStr("failed"));}),_7f=new T(function(){return B(unCStr("protocol error"));}),_7g=function(_7h,_7i){switch(E(_7h)){case 0:return new F(function(){return _0(_77,_7i);});break;case 1:return new F(function(){return _0(_76,_7i);});break;case 2:return new F(function(){return _0(_75,_7i);});break;case 3:return new F(function(){return _0(_74,_7i);});break;case 4:return new F(function(){return _0(_73,_7i);});break;case 5:return new F(function(){return _0(_72,_7i);});break;case 6:return new F(function(){return _0(_71,_7i);});break;case 7:return new F(function(){return _0(_70,_7i);});break;case 8:return new F(function(){return _0(_6Z,_7i);});break;case 9:return new F(function(){return _0(_6Y,_7i);});break;case 10:return new F(function(){return _0(_7f,_7i);});break;case 11:return new F(function(){return _0(_7e,_7i);});break;case 12:return new F(function(){return _0(_7d,_7i);});break;case 13:return new F(function(){return _0(_7c,_7i);});break;case 14:return new F(function(){return _0(_7b,_7i);});break;case 15:return new F(function(){return _0(_7a,_7i);});break;case 16:return new F(function(){return _0(_79,_7i);});break;case 17:return new F(function(){return _0(_78,_7i);});break;default:return new F(function(){return _0(_6X,_7i);});}},_7j=new T(function(){return B(unCStr("}"));}),_7k=new T(function(){return B(unCStr("{handle: "));}),_7l=function(_7m,_7n,_7o,_7p,_7q,_7r){var _7s=new T(function(){var _7t=new T(function(){var _7u=new T(function(){var _7v=E(_7p);if(!_7v._){return E(_7r);}else{var _7w=new T(function(){return B(_0(_7v,new T(function(){return B(_0(_6V,_7r));},1)));},1);return B(_0(_6W,_7w));}},1);return B(_7g(_7n,_7u));}),_7x=E(_7o);if(!_7x._){return E(_7t);}else{return B(_0(_7x,new T(function(){return B(_0(_6U,_7t));},1)));}}),_7y=E(_7q);if(!_7y._){var _7z=E(_7m);if(!_7z._){return E(_7s);}else{var _7A=E(_7z.a);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(_0(_7j,new T(function(){return B(_0(_6U,_7s));},1)));},1);return B(_0(_7A.a,_7C));},1);return new F(function(){return _0(_7k,_7B);});}else{var _7D=new T(function(){var _7E=new T(function(){return B(_0(_7j,new T(function(){return B(_0(_6U,_7s));},1)));},1);return B(_0(_7A.a,_7E));},1);return new F(function(){return _0(_7k,_7D);});}}}else{return new F(function(){return _0(_7y.a,new T(function(){return B(_0(_6U,_7s));},1));});}},_7F=function(_7G){var _7H=E(_7G);return new F(function(){return _7l(_7H.a,_7H.b,_7H.c,_7H.d,_7H.f,_4);});},_7I=function(_7J,_7K,_7L){var _7M=E(_7K);return new F(function(){return _7l(_7M.a,_7M.b,_7M.c,_7M.d,_7M.f,_7L);});},_7N=function(_7O,_7P){var _7Q=E(_7O);return new F(function(){return _7l(_7Q.a,_7Q.b,_7Q.c,_7Q.d,_7Q.f,_7P);});},_7R=function(_7S,_7T){return new F(function(){return _2I(_7N,_7S,_7T);});},_7U=new T3(0,_7I,_7F,_7R),_7V=new T(function(){return new T5(0,_6F,_7U,_7W,_6R,_7F);}),_7W=function(_7X){return new T2(0,_7V,_7X);},_7Y=__Z,_7Z=7,_80=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:157:5-11"));}),_81=new T6(0,_7Y,_7Z,_4,_80,_7Y,_7Y),_82=new T(function(){return B(_7W(_81));}),_83=function(_){return new F(function(){return die(_82);});},_84=1,_85=-1,_86=function(_87,_88){return E(_87)-E(_88);},_89=function(_8a,_8b){var _8c=E(_8a),_8d=E(_8b);return new T2(0,new T(function(){return B(_86(_8c.a,_8d.a));}),new T(function(){return B(_86(_8c.b,_8d.b));}));},_8e=function(_8f,_8g){return new F(function(){return _89(_8g,_8f);});},_8h=new T(function(){return B(unCStr("!!: negative index"));}),_8i=new T(function(){return B(_0(_36,_8h));}),_8j=new T(function(){return B(err(_8i));}),_8k=new T(function(){return B(unCStr("!!: index too large"));}),_8l=new T(function(){return B(_0(_36,_8k));}),_8m=new T(function(){return B(err(_8l));}),_8n=function(_8o,_8p){while(1){var _8q=E(_8o);if(!_8q._){return E(_8m);}else{var _8r=E(_8p);if(!_8r){return E(_8q.a);}else{_8o=_8q.b;_8p=_8r-1|0;continue;}}}},_8s=function(_8t,_8u){if(_8u>=0){return new F(function(){return _8n(_8t,_8u);});}else{return E(_8j);}},_8v=function(_8w,_8x,_8y){while(1){var _8z=E(_8w);if(!_8z._){return new T2(0,_8x,_8y);}else{var _8A=_8z.b,_8B=E(_8z.a),_8C=_8B.a,_8D=_8B.b,_8E=E(_8x);if(!_8E._){if(!E(_8C)._){var _8F=E(_8y),_8G=E(_8D);if(_8F>_8G){_8w=_8A;_8x=_7Y;_8y=_8G;continue;}else{_8w=_8A;_8x=_7Y;_8y=_8F;continue;}}else{_8w=_8A;_8x=_7Y;continue;}}else{var _8H=E(_8C);if(!_8H._){_8w=_8A;_8x=_7Y;_8y=_8D;continue;}else{var _8I=E(_8E.a),_8J=E(_8H.a);if(_8I>=_8J){if(_8I!=_8J){_8w=_8A;_8x=_8H;_8y=_8D;continue;}else{var _8K=E(_8y),_8L=E(_8D);if(_8K>_8L){_8w=_8A;_8x=_8H;_8y=_8L;continue;}else{_8w=_8A;_8x=_8E;_8y=_8K;continue;}}}else{_8w=_8A;_8x=_8E;continue;}}}}}},_8M=function(_8N,_8O,_8P){while(1){var _8Q=E(_8N);if(!_8Q._){return new T2(0,_8O,_8P);}else{var _8R=_8Q.b,_8S=E(_8Q.a),_8T=_8S.a,_8U=_8S.b,_8V=E(_8O);if(!_8V._){var _8W=E(_8T);if(!_8W._){var _8X=E(_8P),_8Y=E(_8U);if(_8X>_8Y){_8N=_8R;_8O=_7Y;_8P=_8X;continue;}else{_8N=_8R;_8O=_7Y;_8P=_8Y;continue;}}else{_8N=_8R;_8O=_8W;_8P=_8U;continue;}}else{var _8Z=E(_8T);if(!_8Z._){_8N=_8R;_8O=_8V;continue;}else{var _90=E(_8V.a),_91=E(_8Z.a);if(_90>=_91){if(_90!=_91){_8N=_8R;_8O=_8V;continue;}else{var _92=E(_8P),_93=E(_8U);if(_92>_93){_8N=_8R;_8O=_8V;_8P=_92;continue;}else{_8N=_8R;_8O=_8Z;_8P=_93;continue;}}}else{_8N=_8R;_8O=_8Z;_8P=_8U;continue;}}}}}},_94=function(_95,_96,_97){while(1){var _98=E(_95);if(!_98._){return new T2(0,_96,_97);}else{var _99=_98.b,_9a=E(_98.a),_9b=_9a.a,_9c=_9a.b,_9d=E(_96);if(!_9d._){var _9e=E(_9b);if(!_9e._){var _9f=E(_97),_9g=E(_9c);if(_9f>_9g){_95=_99;_96=_7Y;_97=_9f;continue;}else{_95=_99;_96=_7Y;_97=_9g;continue;}}else{_95=_99;_96=_9e;_97=_9c;continue;}}else{var _9h=E(_9b);if(!_9h._){_95=_99;_96=_9d;continue;}else{var _9i=E(_9d.a),_9j=E(_9h.a);if(_9i>=_9j){if(_9i!=_9j){_95=_99;_96=_9d;continue;}else{var _9k=E(_97),_9l=E(_9c);if(_9k>_9l){_95=_99;_96=_9d;_97=_9k;continue;}else{_95=_99;_96=_9h;_97=_9l;continue;}}}else{_95=_99;_96=_9h;_97=_9c;continue;}}}}}},_9m=function(_9n,_9o){while(1){var _9p=B((function(_9q,_9r){var _9s=E(_9r);if(!_9s._){return __Z;}else{var _9t=_9s.a,_9u=_9s.b;if(!B(A1(_9q,_9t))){var _9v=_9q;_9n=_9v;_9o=_9u;return __continue;}else{return new T2(1,_9t,new T(function(){return B(_9m(_9q,_9u));}));}}})(_9n,_9o));if(_9p!=__continue){return _9p;}}},_9w=function(_9x){return E(E(_9x).a);},_9y=function(_9z,_9A){var _9B=E(_9z);if(!_9B._){var _9C=E(_9A);return __Z;}else{var _9D=E(_9A);return (_9D._==0)?__Z:(E(_9B.a)>E(_9D.a))?E(_9D):E(_9B);}},_9E=function(_9F,_9G){while(1){var _9H=E(_9F);if(!_9H._){return E(_9G);}else{var _9I=B(_9y(_9G,_9H.a));_9F=_9H.b;_9G=_9I;continue;}}},_9J=function(_9K,_9L){while(1){var _9M=E(_9K);if(!_9M._){return E(_9L);}else{var _9N=B(_9y(_9L,_9M.a));_9K=_9M.b;_9L=_9N;continue;}}},_9O=function(_9P){return (E(_9P)._==0)?false:true;},_9Q=new T(function(){return B(unCStr("minimum"));}),_9R=new T(function(){return B(_37(_9Q));}),_9S=function(_9T,_9U){var _9V=E(_9T);if(!_9V._){return __Z;}else{var _9W=E(_9U);return (_9W._==0)?__Z:new T2(1,new T2(0,new T(function(){var _9X=B(_9m(_9O,_9V.a));if(!_9X._){return E(_9R);}else{return B(_9J(_9X.b,_9X.a));}}),_9W.a),new T(function(){return B(_9S(_9V.b,_9W.b));}));}},_9Y=function(_9Z,_a0){while(1){var _a1=E(_9Z);if(!_a1._){return E(_a0);}else{var _a2=B(_9y(_a0,_a1.a));_9Z=_a1.b;_a0=_a2;continue;}}},_a3=function(_a4,_a5){while(1){var _a6=E(_a4);if(!_a6._){return E(_a5);}else{var _a7=B(_9y(_a5,_a6.a));_a4=_a6.b;_a5=_a7;continue;}}},_a8=function(_a9,_aa){var _ab=E(_a9);if(!_ab._){return __Z;}else{var _ac=E(_aa);return (_ac._==0)?__Z:new T2(1,new T2(0,new T(function(){var _ad=B(_9m(_9O,_ab.a));if(!_ad._){return E(_9R);}else{return B(_a3(_ad.b,_ad.a));}}),_ac.a),new T(function(){return B(_a8(_ab.b,_ac.b));}));}},_ae=function(_af){while(1){var _ag=E(_af);if(!_ag._){return true;}else{if(!E(_ag.a)._){_af=_ag.b;continue;}else{return false;}}}},_ah=function(_ai){while(1){var _aj=E(_ai);if(!_aj._){return false;}else{if(!B(_ae(_aj.a))){_ai=_aj.b;continue;}else{return true;}}}},_ak=function(_al,_am){var _an=E(_al),_ao=E(_an.a),_ap=E(_ao.a),_aq=E(_ao.b),_ar=E(_an.b),_as=E(_am),_at= -(E(_ar.b)-_aq),_au=E(_ar.a)-_ap,_av=(_at*E(_as.a)+_au*E(_as.b)-(_at*_ap+_au*_aq))/Math.sqrt(_at*_at+_au*_au);return (_av<0)?new T1(1,_av):__Z;},_aw=new T(function(){return B(unCStr("maximum"));}),_ax=new T(function(){return B(_37(_aw));}),_ay=new T(function(){return B(_37(_9Q));}),_az=0,_aA=new T2(0,_1n,_1l),_aB=1,_aC=new T(function(){return B(_41(0,3));}),_aD=new T(function(){return B(unCStr("base"));}),_aE=new T(function(){return B(unCStr("Control.Exception.Base"));}),_aF=new T(function(){return B(unCStr("PatternMatchFail"));}),_aG=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aD,_aE,_aF),_aH=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aG,_4,_4),_aI=function(_aJ){return E(_aH);},_aK=function(_aL){var _aM=E(_aL);return new F(function(){return _6J(B(_6H(_aM.a)),_aI,_aM.b);});},_aN=function(_aO){return E(E(_aO).a);},_aP=function(_aQ){return new T2(0,_aR,_aQ);},_aS=function(_aT,_aU){return new F(function(){return _0(E(_aT).a,_aU);});},_aV=function(_aW,_aX){return new F(function(){return _2I(_aS,_aW,_aX);});},_aY=function(_aZ,_b0,_b1){return new F(function(){return _0(E(_b0).a,_b1);});},_b2=new T3(0,_aY,_aN,_aV),_aR=new T(function(){return new T5(0,_aI,_b2,_aP,_aK,_aN);}),_b3=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_b4=function(_b5){return E(E(_b5).c);},_b6=function(_b7,_b8){return new F(function(){return die(new T(function(){return B(A2(_b4,_b8,_b7));}));});},_b9=function(_ba,_bb){return new F(function(){return _b6(_ba,_bb);});},_bc=function(_bd,_be){var _bf=E(_be);if(!_bf._){return new T2(0,_4,_4);}else{var _bg=_bf.a;if(!B(A1(_bd,_bg))){return new T2(0,_4,_bf);}else{var _bh=new T(function(){var _bi=B(_bc(_bd,_bf.b));return new T2(0,_bi.a,_bi.b);});return new T2(0,new T2(1,_bg,new T(function(){return E(E(_bh).a);})),new T(function(){return E(E(_bh).b);}));}}},_bj=32,_bk=new T(function(){return B(unCStr("\n"));}),_bl=function(_bm){return (E(_bm)==124)?false:true;},_bn=function(_bo,_bp){var _bq=B(_bc(_bl,B(unCStr(_bo)))),_br=_bq.a,_bs=function(_bt,_bu){var _bv=new T(function(){var _bw=new T(function(){return B(_0(_bp,new T(function(){return B(_0(_bu,_bk));},1)));});return B(unAppCStr(": ",_bw));},1);return new F(function(){return _0(_bt,_bv);});},_bx=E(_bq.b);if(!_bx._){return new F(function(){return _bs(_br,_4);});}else{if(E(_bx.a)==124){return new F(function(){return _bs(_br,new T2(1,_bj,_bx.b));});}else{return new F(function(){return _bs(_br,_4);});}}},_by=function(_bz){return new F(function(){return _b9(new T1(0,new T(function(){return B(_bn(_bz,_b3));})),_aR);});},_bA=new T(function(){return B(_by("Lib\\Physics.hs:98:13-61|(Just d\', f\')"));}),_bB=function(_bC){return  -E(_bC);},_bD=function(_bE){var _bF=E(_bE);return new T2(0,new T(function(){return B(_bB(_bF.a));}),new T(function(){return B(_bB(_bF.b));}));},_bG=function(_bH){var _bI=E(_bH);return new T5(0,_bI.b,_bI.a,new T(function(){return B(_bD(_bI.d));}),new T(function(){return B(_bD(_bI.c));}),_bI.e);},_bJ=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_bK=function(_bL){return new F(function(){return _b9(new T1(0,new T(function(){return B(_bn(_bL,_bJ));})),_aR);});},_bM=new T(function(){return B(_bK("Lib\\Physics.hs:(60,26)-(63,63)|multi-way if"));}),_bN=function(_bO,_bP){var _bQ=E(_bP);return (_bQ._==0)?__Z:new T2(1,new T(function(){return B(A1(_bO,_bQ.a));}),new T(function(){return B(_bN(_bO,_bQ.b));}));},_bR=function(_bS,_bT){var _bU=_bS%_bT;if(_bS<=0){if(_bS>=0){return E(_bU);}else{if(_bT<=0){return E(_bU);}else{var _bV=E(_bU);return (_bV==0)?0:_bV+_bT|0;}}}else{if(_bT>=0){if(_bS>=0){return E(_bU);}else{if(_bT<=0){return E(_bU);}else{var _bW=E(_bU);return (_bW==0)?0:_bW+_bT|0;}}}else{var _bX=E(_bU);return (_bX==0)?0:_bX+_bT|0;}}},_bY=function(_bZ){return E(E(_bZ).b);},_c0=new T(function(){return B(unCStr("tail"));}),_c1=new T(function(){return B(_37(_c0));}),_c2=-1,_c3=new T2(0,_c2,_c2),_c4=new T2(0,_c2,_aB),_c5=new T2(0,_aB,_aB),_c6=new T2(0,_aB,_c2),_c7=new T2(1,_c3,_4),_c8=new T2(1,_c6,_c7),_c9=new T2(1,_c5,_c8),_ca=new T2(1,_c4,_c9),_cb=new T2(1,_c3,_ca),_cc=function(_cd,_ce){var _cf=E(_cd);if(!_cf._){return __Z;}else{var _cg=E(_ce);return (_cg._==0)?__Z:new T2(1,new T2(0,_cf.a,_cg.a),new T(function(){return B(_cc(_cf.b,_cg.b));}));}},_ch=function(_ci,_cj,_ck,_cl){var _cm=E(_cj);if(!_cm._){return __Z;}else{var _cn=E(_ck);if(!_cn._){return __Z;}else{var _co=E(_cl);return (_co._==0)?__Z:new T2(1,new T(function(){return B(A3(_ci,_cm.a,_cn.a,_co.a));}),new T(function(){return B(_ch(_ci,_cm.b,_cn.b,_co.b));}));}}},_cp=function(_cq,_cr,_cs,_ct){var _cu=E(_cq);if(!_cu._){var _cv=_cu.a,_cw=E(_cs);if(!_cw._){var _cx=E(_cr),_cy=E(_ct),_cz=E(_cv),_cA=E(_cw.a),_cB=E(_cx.a)-E(_cy.a),_cC=E(_cx.b)-E(_cy.b),_cD=Math.sqrt(_cB*_cB+_cC*_cC),_cE=_cz+_cA;if(_cD<=_cE){var _cF=new T(function(){var _cG=E(_cD);if(!_cG){return E(_aA);}else{return new T2(0,new T(function(){return _cB/_cG;}),new T(function(){return _cC/_cG;}));}}),_cH=new T(function(){var _cI=E(_cF);return new T2(0,new T(function(){return E(_cI.a)*_cA;}),new T(function(){return E(_cI.b)*_cA;}));}),_cJ=new T(function(){var _cK=E(_cF);return new T2(0,new T(function(){return  -(E(_cK.a)*_cz);}),new T(function(){return  -(E(_cK.b)*_cz);}));});return new T2(1,new T5(0,_cJ,_cH,_cF,_cF,_cE-_cD),_4);}else{return __Z;}}else{var _cL=E(_cr),_cM=E(_cL.a),_cN=E(_ct),_cO=E(_cN.a),_cP=E(_cN.c),_cQ=E(_cL.b),_cR=E(_cN.b),_cS=E(_cw.a),_cT=_cM-_cO,_cU= -_cP,_cV=_cQ-_cR,_cW=_cT*Math.cos(_cU)-_cV*Math.sin(_cU),_cX= -(_cS/2),_cY=_cS/2,_cZ=function(_d0){var _d1=E(_cw.b),_d2=_cT*Math.sin(_cU)+_cV*Math.cos(_cU),_d3= -(_d1/2),_d4=_d1/2,_d5=function(_d6){var _d7=E(_cv),_d8=_cW-_d0,_d9=_d2-_d6,_da=Math.sqrt(_d8*_d8+_d9*_d9);if(_da<=_d7){var _db=new T(function(){var _dc=function(_dd){if(_dd>0){var _de=function(_df){if(_df>0){return (_dd>_df)?(_dd<_df)?E(_bM):new T2(0,new T2(0,_az,new T(function(){if(_d9<=0){if(_d9>=0){return _d9;}else{return E(_85);}}else{return E(_84);}})),_d7+_df):new T2(0,new T2(0,new T(function(){if(_d8<=0){if(_d8>=0){return _d8;}else{return E(_85);}}else{return E(_84);}}),_az),_d7+_dd);}else{var _dg=new T(function(){var _dh=E(_da);if(!_dh){return E(_aA);}else{return new T2(0,new T(function(){return _d8/_dh;}),new T(function(){return _d9/_dh;}));}});return new T2(0,_dg,_d7-_da);}},_di=E(_d2);if(!_di){return new F(function(){return _de(_d1/2);});}else{if(_di<=0){return new F(function(){return _de(_d1/2+_di);});}else{return new F(function(){return _de(_d1/2-_di);});}}}else{var _dj=new T(function(){var _dk=E(_da);if(!_dk){return E(_aA);}else{return new T2(0,new T(function(){return _d8/_dk;}),new T(function(){return _d9/_dk;}));}});return new T2(0,_dj,_d7-_da);}},_dl=E(_cW);if(!_dl){var _dm=B(_dc(_cS/2));return new T2(0,_dm.a,_dm.b);}else{if(_dl<=0){var _dn=B(_dc(_cS/2+_dl));return new T2(0,_dn.a,_dn.b);}else{var _do=B(_dc(_cS/2-_dl));return new T2(0,_do.a,_do.b);}}}),_dp=new T(function(){return E(E(_db).b);}),_dq=new T(function(){var _dr=E(E(_db).a),_ds=_dr.a,_dt=_dr.b;return new T2(0,new T(function(){return E(_ds)*Math.cos(_cP)-E(_dt)*Math.sin(_cP);}),new T(function(){return E(_ds)*Math.sin(_cP)+E(_dt)*Math.cos(_cP);}));}),_du=new T(function(){var _dv=E(_dq);return new T2(0,new T(function(){return _cM-E(_dv.a)*_d7;}),new T(function(){return _cQ-E(_dv.b)*_d7;}));}),_dw=new T(function(){var _dx=E(_du),_dy=E(_dq);return new T2(0,new T(function(){return E(_dx.a)+E(_dy.a)*E(_dp)-_cO;}),new T(function(){return E(_dx.b)+E(_dy.b)*E(_dp)-_cR;}));}),_dz=new T(function(){var _dA=E(_du);return new T2(0,new T(function(){return E(_dA.a)-_cM;}),new T(function(){return E(_dA.b)-_cQ;}));});return new T2(1,new T5(0,_dz,_dw,_dq,_dq,_dp),_4);}else{return __Z;}};if(_d3>_d2){if(_d4>_d3){return new F(function(){return _d5(_d3);});}else{return new F(function(){return _d5(_d4);});}}else{if(_d4>_d2){return new F(function(){return _d5(_d2);});}else{return new F(function(){return _d5(_d4);});}}};if(_cX>_cW){if(_cY>_cX){return new F(function(){return _cZ(_cX);});}else{return new F(function(){return _cZ(_cY);});}}else{if(_cY>_cW){return new F(function(){return _cZ(_cW);});}else{return new F(function(){return _cZ(_cY);});}}}}else{var _dB=E(_cs);if(!_dB._){return new F(function(){return _bN(_bG,B(_cp(_dB,_ct,_cu,_cr)));});}else{var _dC=new T(function(){var _dD=function(_dE){var _dF=E(_dE),_dG=new T(function(){return E(E(_ct).c);}),_dH=new T(function(){return E(_dF.a)*E(_dB.a)*0.5;}),_dI=new T(function(){return E(_dF.b)*E(_dB.b)*0.5;});return new T2(0,new T(function(){var _dJ=E(_dG);return E(E(_ct).a)+(E(_dH)*Math.cos(_dJ)-E(_dI)*Math.sin(_dJ));}),new T(function(){var _dK=E(_dG);return E(E(_ct).b)+E(_dH)*Math.sin(_dK)+E(_dI)*Math.cos(_dK);}));};return B(_bN(_dD,_cb));}),_dL=new T(function(){return B(_cc(_dC,new T(function(){var _dM=E(_dC);if(!_dM._){return E(_c1);}else{return E(_dM.b);}},1)));}),_dN=function(_dO){var _dP=E(_dO),_dQ=new T(function(){return E(E(_cr).c);}),_dR=new T(function(){return E(_dP.a)*E(_cu.a)*0.5;}),_dS=new T(function(){return E(_dP.b)*E(_cu.b)*0.5;});return new T2(0,new T(function(){var _dT=E(_dQ);return E(E(_cr).a)+(E(_dR)*Math.cos(_dT)-E(_dS)*Math.sin(_dT));}),new T(function(){var _dU=E(_dQ);return E(E(_cr).b)+E(_dR)*Math.sin(_dU)+E(_dS)*Math.cos(_dU);}));},_dV=B(_bN(_dN,_cb)),_dW=new T(function(){var _dX=function(_dY){var _dZ=E(_dV);if(!_dZ._){return E(_c1);}else{return new F(function(){return _bN(function(_e0){return new F(function(){return _ak(_dY,_e0);});},_dZ.b);});}};return B(_bN(_dX,_dL));}),_e1=B(_cc(_dV,new T(function(){var _e2=E(_dV);if(!_e2._){return E(_c1);}else{return E(_e2.b);}},1))),_e3=function(_e4){var _e5=E(_dC);if(!_e5._){return E(_c1);}else{return new F(function(){return _bN(function(_e0){return new F(function(){return _ak(_e4,_e0);});},_e5.b);});}},_e6=B(_bN(_e3,_e1));if(!B(_ah(B(_0(_e6,_dW))))){var _e7=B(_a8(_e6,_aC));if(!_e7._){return E(_ax);}else{var _e8=E(_e7.a),_e9=E(B(_94(_e7.b,_e8.a,_e8.b)).b),_ea=B(_9m(_9O,B(_8s(_e6,_e9))));if(!_ea._){return E(_9R);}else{var _eb=B(_9S(_dW,_aC));if(!_eb._){return E(_ax);}else{var _ec=E(_eb.a),_ed=E(B(_8M(_eb.b,_ec.a,_ec.b)).b),_ee=B(_9m(_9O,B(_8s(_dW,_ed))));if(!_ee._){return E(_9R);}else{var _ef=B(_9E(_ee.b,_ee.a)),_eg=B(_9Y(_ea.b,_ea.a)),_eh=E(_eg);if(!_eh._){var _ei=E(_ef),_ej=false;}else{var _ek=E(_ef);if(!_ek._){var _el=true;}else{var _el=E(_eh.a)>E(_ek.a);}var _ej=_el;}var _em=function(_en,_eo){var _ep=function(_eq,_er,_es,_et){var _eu=E(_es),_ev=E(_et),_ew=E(_eu.a),_ex=E(_eu.b),_ey=E(_ev.a),_ez=E(_ev.b),_eA=_ey-_ew,_eB=_ez-_ex,_eC=Math.sqrt(_eA*_eA+_eB*_eB);if(!_eC){var _eD=E(_eq),_eE=E(_eD.a),_eF=E(_eD.b),_eG=E(_er),_eH= -(E(_eG.b)-_eF),_eI=E(_eG.a)-_eE,_eJ=function(_eK,_eL,_eM){var _eN=E(_eL),_eO=E(_eM),_eP=_ew+_ex*0,_eQ=_ey+_ez*0-_eP,_eR=new T(function(){var _eS=E(E(_eK).a);return (E(_eS.a)+E(_eS.b)*0-_eP)/_eQ;}),_eT=new T(function(){var _eU=E(E(_eK).b);return (E(_eU.a)+E(_eU.b)*0-_eP)/_eQ;}),_eV=function(_eW){var _eX=new T(function(){var _eY=E(_eW);if(0>_eY){return E(_az);}else{if(1>_eY){return E(_eY);}else{return E(_aB);}}}),_eZ=new T(function(){return E(_eT)-E(_eX);}),_f0=new T(function(){return E(_eX)-E(_eR);});return new T2(0,new T(function(){var _f1=E(_eZ),_f2=E(_f0);return (E(_eN.a)*_f1+E(_eO.a)*_f2)/(_f1+_f2);}),new T(function(){var _f3=E(_eZ),_f4=E(_f0);return (E(_eN.b)*_f3+E(_eO.b)*_f4)/(_f3+_f4);}));},_f5=B(_eV(_eR)),_f6=E(_f5.a),_f7=E(_f5.b),_f8=new T(function(){var _f9=B(_eV(_eT)),_fa=E(_f9.a),_fb=E(_f9.b),_fc=(_eH*_fa+_eI*_fb-(_eH*_eE+_eI*_eF))/Math.sqrt(_eH*_eH+_eI*_eI);if(_fc<0){return new T2(1,new T2(0,new T2(0,_fa,_fb), -_fc),_4);}else{return __Z;}}),_fd=(_eH*_f6+_eI*_f7-(_eH*_eE+_eI*_eF))/Math.sqrt(_eH*_eH+_eI*_eI);if(_fd<0){var _fe=new T2(1,new T2(0,new T2(0,_f6,_f7), -_fd),_f8);}else{var _fe=E(_f8);}var _ff=new T(function(){return B(_bN(_9w,_fe));}),_fg= -0,_fh=new T(function(){var _fi=function(_fj){var _fk=E(_fj),_fl=_fk.b,_fm=E(_fk.a);return new T2(0,new T(function(){return E(_fm.a)+_fg*E(_fl);}),new T(function(){return E(_fm.b)+E(_fl);}));};return B(_bN(_fi,_fe));}),_fn=new T(function(){if(!E(_ej)){var _fo=new T(function(){return E(E(_ct).b);}),_fp=new T(function(){return E(E(_ct).a);});return B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_fp,_fo),_e0);});},_fh));}else{var _fq=new T(function(){return E(E(_ct).b);}),_fr=new T(function(){return E(E(_ct).a);});return B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_fr,_fq),_e0);});},_ff));}}),_fs=new T(function(){if(!E(_ej)){return new T2(0,_fg,1);}else{return new T2(0, -_fg,-1);}}),_ft=function(_fu,_fv,_fw){return new T5(0,_fu,_fv,_fs,_fs,_fw);};if(!E(_ej)){var _fx=new T(function(){return E(E(_cr).b);}),_fy=new T(function(){return E(E(_cr).a);});return new F(function(){return _ch(_ft,B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_fy,_fx),_e0);});},_ff)),_fn,new T(function(){return B(_bN(_bY,_fe));},1));});}else{var _fz=new T(function(){return E(E(_cr).b);}),_fA=new T(function(){return E(E(_cr).a);});return new F(function(){return _ch(_ft,B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_fA,_fz),_e0);});},_fh)),_fn,new T(function(){return B(_bN(_bY,_fe));},1));});}},_fB=function(_fC){var _fD=function(_fE,_fF){while(1){var _fG=B((function(_fH,_fI){var _fJ=E(_fH);if(!_fJ._){return __Z;}else{var _fK=_fJ.b,_fL=E(_fI);if(!_fL._){return __Z;}else{var _fM=_fL.b,_fN=E(_fJ.a),_fO=(_eH*E(_fN.a)+_eI*E(_fN.b)-(_eH*_eE+_eI*_eF))/Math.sqrt(_eH*_eH+_eI*_eI);if(_fO<0){return new T2(1,new T2(0,new T1(1,_fO),_fL.a),new T(function(){return B(_fD(_fK,_fM));}));}else{_fE=_fK;_fF=_fM;return __continue;}}}})(_fE,_fF));if(_fG!=__continue){return _fG;}}};return new F(function(){return _fD(_fC,_aC);});},_fP=function(_fQ){var _fR=B(_8s(_eo,_fQ)),_fS=E(_fR.a),_fT=E(_fR.b),_fU=E(_fS.a)-E(_fT.a),_fV=E(_fS.b)-E(_fT.b),_fW=function(_fX,_fY){var _fZ=function(_g0){var _g1=B(_8s(_eo,B(_bR(_fQ+1|0,4)))),_g2=E(_g1.b),_g3=E(_g1.a),_g4=E(_g2.a)-E(_g3.a),_g5=E(_g2.b)-E(_g3.b),_g6=Math.sqrt(_g4*_g4+_g5*_g5);if(!_g6){return (_g0<=1)?new T3(0,_g1,_g3,_g2):new T3(0,new T2(0,_fT,_fS),_fT,_fS);}else{var _g7=_g4/_g6+0*(_g5/_g6);return (_g7==0)?(_g0<=0)?new T3(0,_g1,_g3,_g2):new T3(0,new T2(0,_fT,_fS),_fT,_fS):(_g7<=0)?(_g0<= -_g7)?new T3(0,_g1,_g3,_g2):new T3(0,new T2(0,_fT,_fS),_fT,_fS):(_g0<=_g7)?new T3(0,_g1,_g3,_g2):new T3(0,new T2(0,_fT,_fS),_fT,_fS);}},_g8=_fX+0*_fY;if(!_g8){return new F(function(){return _fZ(0);});}else{if(_g8<=0){return new F(function(){return _fZ( -_g8);});}else{return new F(function(){return _fZ(_g8);});}}},_g9=Math.sqrt(_fU*_fU+_fV*_fV);if(!_g9){return new F(function(){return _fW(1,0);});}else{return new F(function(){return _fW(_fU/_g9,_fV/_g9);});}};if(!E(_ej)){var _ga=E(_dV);if(!_ga._){return E(_c1);}else{var _gb=B(_fB(_ga.b));if(!_gb._){return E(_ay);}else{var _gc=E(_gb.a),_gd=B(_fP(E(B(_8v(_gb.b,_gc.a,_gc.b)).b)));return new F(function(){return _eJ(_gd.a,_gd.b,_gd.c);});}}}else{var _ge=E(_dC);if(!_ge._){return E(_c1);}else{var _gf=B(_fB(_ge.b));if(!_gf._){return E(_ay);}else{var _gg=E(_gf.a),_gh=B(_fP(E(B(_8v(_gf.b,_gg.a,_gg.b)).b)));return new F(function(){return _eJ(_gh.a,_gh.b,_gh.c);});}}}}else{var _gi=_eA/_eC,_gj=_eB/_eC,_gk=E(_eq),_gl=E(_gk.a),_gm=E(_gk.b),_gn=E(_er),_go= -(E(_gn.b)-_gm),_gp=E(_gn.a)-_gl,_gq=function(_gr,_gs,_gt){var _gu=E(_gs),_gv=E(_gt),_gw=_ew*_gi+_ex*_gj,_gx=_ey*_gi+_ez*_gj-_gw,_gy=new T(function(){var _gz=E(E(_gr).a);return (E(_gz.a)*_gi+E(_gz.b)*_gj-_gw)/_gx;}),_gA=new T(function(){var _gB=E(E(_gr).b);return (E(_gB.a)*_gi+E(_gB.b)*_gj-_gw)/_gx;}),_gC=function(_gD){var _gE=new T(function(){var _gF=E(_gD);if(0>_gF){return E(_az);}else{if(1>_gF){return E(_gF);}else{return E(_aB);}}}),_gG=new T(function(){return E(_gA)-E(_gE);}),_gH=new T(function(){return E(_gE)-E(_gy);});return new T2(0,new T(function(){var _gI=E(_gG),_gJ=E(_gH);return (E(_gu.a)*_gI+E(_gv.a)*_gJ)/(_gI+_gJ);}),new T(function(){var _gK=E(_gG),_gL=E(_gH);return (E(_gu.b)*_gK+E(_gv.b)*_gL)/(_gK+_gL);}));},_gM=B(_gC(_gy)),_gN=E(_gM.a),_gO=E(_gM.b),_gP=new T(function(){var _gQ=B(_gC(_gA)),_gR=E(_gQ.a),_gS=E(_gQ.b),_gT=(_go*_gR+_gp*_gS-(_go*_gl+_gp*_gm))/Math.sqrt(_go*_go+_gp*_gp);if(_gT<0){return new T2(1,new T2(0,new T2(0,_gR,_gS), -_gT),_4);}else{return __Z;}}),_gU=(_go*_gN+_gp*_gO-(_go*_gl+_gp*_gm))/Math.sqrt(_go*_go+_gp*_gp);if(_gU<0){var _gV=new T2(1,new T2(0,new T2(0,_gN,_gO), -_gU),_gP);}else{var _gV=E(_gP);}var _gW=new T(function(){return B(_bN(_9w,_gV));}),_gX= -_gj,_gY=new T(function(){var _gZ=function(_h0){var _h1=E(_h0),_h2=_h1.b,_h3=E(_h1.a);return new T2(0,new T(function(){return E(_h3.a)+_gX*E(_h2);}),new T(function(){return E(_h3.b)+_gi*E(_h2);}));};return B(_bN(_gZ,_gV));}),_h4=new T(function(){if(!E(_ej)){var _h5=new T(function(){return E(E(_ct).b);}),_h6=new T(function(){return E(E(_ct).a);});return B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_h6,_h5),_e0);});},_gY));}else{var _h7=new T(function(){return E(E(_ct).b);}),_h8=new T(function(){return E(E(_ct).a);});return B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_h8,_h7),_e0);});},_gW));}}),_h9=new T(function(){if(!E(_ej)){return new T2(0,_gX,_gi);}else{return new T2(0, -_gX, -_gi);}}),_ha=function(_hb,_hc,_hd){return new T5(0,_hb,_hc,_h9,_h9,_hd);};if(!E(_ej)){var _he=new T(function(){return E(E(_cr).b);}),_hf=new T(function(){return E(E(_cr).a);});return new F(function(){return _ch(_ha,B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_hf,_he),_e0);});},_gW)),_h4,new T(function(){return B(_bN(_bY,_gV));},1));});}else{var _hg=new T(function(){return E(E(_cr).b);}),_hh=new T(function(){return E(E(_cr).a);});return new F(function(){return _ch(_ha,B(_bN(function(_e0){return new F(function(){return _8e(new T2(0,_hh,_hg),_e0);});},_gY)),_h4,new T(function(){return B(_bN(_bY,_gV));},1));});}},_hi=function(_hj){var _hk=function(_hl,_hm){while(1){var _hn=B((function(_ho,_hp){var _hq=E(_ho);if(!_hq._){return __Z;}else{var _hr=_hq.b,_hs=E(_hp);if(!_hs._){return __Z;}else{var _ht=_hs.b,_hu=E(_hq.a),_hv=(_go*E(_hu.a)+_gp*E(_hu.b)-(_go*_gl+_gp*_gm))/Math.sqrt(_go*_go+_gp*_gp);if(_hv<0){return new T2(1,new T2(0,new T1(1,_hv),_hs.a),new T(function(){return B(_hk(_hr,_ht));}));}else{_hl=_hr;_hm=_ht;return __continue;}}}})(_hl,_hm));if(_hn!=__continue){return _hn;}}};return new F(function(){return _hk(_hj,_aC);});},_hw=function(_hx){var _hy=B(_8s(_eo,_hx)),_hz=E(_hy.a),_hA=E(_hy.b),_hB=E(_hz.a)-E(_hA.a),_hC=E(_hz.b)-E(_hA.b),_hD=function(_hE,_hF){var _hG=function(_hH){var _hI=B(_8s(_eo,B(_bR(_hx+1|0,4)))),_hJ=E(_hI.b),_hK=E(_hI.a),_hL=E(_hJ.a)-E(_hK.a),_hM=E(_hJ.b)-E(_hK.b),_hN=Math.sqrt(_hL*_hL+_hM*_hM);if(!_hN){var _hO=_gi+_gj*0;return (_hO==0)?(_hH<=0)?new T3(0,_hI,_hK,_hJ):new T3(0,new T2(0,_hA,_hz),_hA,_hz):(_hO<=0)?(_hH<= -_hO)?new T3(0,_hI,_hK,_hJ):new T3(0,new T2(0,_hA,_hz),_hA,_hz):(_hH<=_hO)?new T3(0,_hI,_hK,_hJ):new T3(0,new T2(0,_hA,_hz),_hA,_hz);}else{var _hP=_gi*(_hL/_hN)+_gj*(_hM/_hN);return (_hP==0)?(_hH<=0)?new T3(0,_hI,_hK,_hJ):new T3(0,new T2(0,_hA,_hz),_hA,_hz):(_hP<=0)?(_hH<= -_hP)?new T3(0,_hI,_hK,_hJ):new T3(0,new T2(0,_hA,_hz),_hA,_hz):(_hH<=_hP)?new T3(0,_hI,_hK,_hJ):new T3(0,new T2(0,_hA,_hz),_hA,_hz);}},_hQ=_gi*_hE+_gj*_hF;if(!_hQ){return new F(function(){return _hG(0);});}else{if(_hQ<=0){return new F(function(){return _hG( -_hQ);});}else{return new F(function(){return _hG(_hQ);});}}},_hR=Math.sqrt(_hB*_hB+_hC*_hC);if(!_hR){return new F(function(){return _hD(1,0);});}else{return new F(function(){return _hD(_hB/_hR,_hC/_hR);});}};if(!E(_ej)){var _hS=E(_dV);if(!_hS._){return E(_c1);}else{var _hT=B(_hi(_hS.b));if(!_hT._){return E(_ay);}else{var _hU=E(_hT.a),_hV=B(_hw(E(B(_8v(_hT.b,_hU.a,_hU.b)).b)));return new F(function(){return _gq(_hV.a,_hV.b,_hV.c);});}}}else{var _hW=E(_dC);if(!_hW._){return E(_c1);}else{var _hX=B(_hi(_hW.b));if(!_hX._){return E(_ay);}else{var _hY=E(_hX.a),_hZ=B(_hw(E(B(_8v(_hX.b,_hY.a,_hY.b)).b)));return new F(function(){return _gq(_hZ.a,_hZ.b,_hZ.c);});}}}}};if(!E(_ej)){if(!E(_ef)._){return E(_bA);}else{var _i0=B(_8s(_en,_ed)),_i1=_i0.a,_i2=_i0.b;return new F(function(){return _ep(_i1,_i2,_i1,_i2);});}}else{if(!E(_eg)._){return E(_bA);}else{var _i3=B(_8s(_en,_e9)),_i4=_i3.a,_i5=_i3.b;return new F(function(){return _ep(_i4,_i5,_i4,_i5);});}}};if(!E(_ej)){return new F(function(){return _em(_dL,_e1);});}else{return new F(function(){return _em(_e1,_dL);});}}}}}}else{return __Z;}}}},_i6=new T(function(){return B(_41(-1,1));}),_i7=new T(function(){return eval("scrH");}),_i8=function(_i9,_ia){var _ib=new T(function(){var _ic=E(E(_i9).b),_id=E(E(_ia).b);if(E(_ic.a)!=E(_id.a)){return false;}else{if(E(_ic.b)!=E(_id.b)){return false;}else{return E(_ic.c)==E(_id.c);}}}),_ie=new T(function(){return E(E(_ia).a);}),_if=function(_ig){var _ih=E(_ig);if(!_ih._){return __Z;}else{var _ii=_ih.a,_ij=new T(function(){return B(_if(_ih.b));}),_ik=function(_il){var _im=E(_il);if(!_im._){return E(_ij);}else{var _in=_im.a,_io=new T(function(){return B(_ik(_im.b));}),_ip=function(_iq){var _ir=E(_i9),_is=new T(function(){var _it=E(E(_ia).b);return new T3(0,new T(function(){return E(_it.a)+E(_ii)*E(_1t);}),new T(function(){return E(_it.b)+E(_in)*E(_i7);}),_it.c);});return new F(function(){return _0(B(_cp(_ir.a,_ir.b,_ie,_is)),_io);});};if(!E(_ib)){return new F(function(){return _ip(_);});}else{if(!E(_ii)){if(!E(_in)){return E(_io);}else{return new F(function(){return _ip(_);});}}else{return new F(function(){return _ip(_);});}}}};return new F(function(){return _ik(_i6);});}};return new F(function(){return _if(_i6);});},_iu=function(_iv,_iw){var _ix=E(_iv),_iy=E(_iw);return E(_ix.a)*E(_iy.b)-E(_iy.a)*E(_ix.b);},_iz=new T(function(){return eval("mouseContact");}),_iA=function(_iB){var _iC=E(_iB);if(!_iC._){return __Z;}else{return new F(function(){return _0(_iC.a,new T(function(){return B(_iA(_iC.b));},1));});}},_iD=function(_iE){var _iF=E(_iE);if(!_iF._){return __Z;}else{return new F(function(){return _0(_iF.a,new T(function(){return B(_iD(_iF.b));},1));});}},_iG=new T(function(){return B(unCStr(")"));}),_iH=function(_iI,_iJ){var _iK=new T(function(){var _iL=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2u(0,_iI,_4)),_iG));})));},1);return B(_0(B(_2u(0,_iJ,_4)),_iL));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_iK)));});},_iM=function(_iN,_iO){var _iP=new T(function(){var _iQ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2u(0,_iO,_4)),_iG));})));},1);return B(_0(B(_2u(0,_iN,_4)),_iQ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_iP)));});},_iR=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:159:7-13"));}),_iS=new T6(0,_7Y,_7Z,_4,_iR,_7Y,_7Y),_iT=new T(function(){return B(_7W(_iS));}),_iU=function(_iV,_iW){return E(_iV)*E(_iW);},_iX=function(_iY,_iZ,_j0,_j1,_){if(_iY<=_iZ){var _j2=E(_j1),_j3=function(_j4,_j5,_j6,_j7,_j8,_){if(_j5>_j4){return new F(function(){return _83(_);});}else{if(_j4>_j6){return new F(function(){return _83(_);});}else{var _j9=new T(function(){var _ja=_j4-_j5|0;if(0>_ja){return B(_iM(_ja,_j7));}else{if(_ja>=_j7){return B(_iM(_ja,_j7));}else{return E(_j8[_ja]);}}}),_jb=function(_jc,_jd,_je,_jf,_jg,_){var _jh=E(_jc);if(!_jh._){return new T2(0,_4,new T4(0,E(_jd),E(_je),_jf,_jg));}else{var _ji=E(_jh.a);if(_jd>_ji){return new F(function(){return die(_iT);});}else{if(_ji>_je){return new F(function(){return die(_iT);});}else{var _jj=B(_jb(_jh.b,_jd,_je,_jf,_jg,_)),_jk=new T(function(){var _jl=function(_jm){var _jn=E(_jm),_jo=_jn.c,_jp=_jn.d;return new T5(0,_j4,_ji,new T3(0,new T(function(){return E(E(_jo).a);}),new T(function(){return E(E(_jo).b);}),new T(function(){return B(_iu(_jn.a,_jo));})),new T3(0,new T(function(){return E(E(_jp).a);}),new T(function(){return E(E(_jp).b);}),new T(function(){return B(_iu(_jn.b,_jp));})),_jn.e);};return B(_bN(_jl,B(_i8(_j9,new T(function(){var _jq=_ji-_jd|0;if(0>_jq){return B(_iH(_jf,_jq));}else{if(_jq>=_jf){return B(_iH(_jf,_jq));}else{return E(_jg[_jq]);}}})))));});return new T2(0,new T2(1,_jk,new T(function(){return E(E(_jj).a);})),new T(function(){return E(E(_jj).b);}));}}}},_jr=B(_jb(B(_41(_j4+1|0,_iZ)),_j5,_j6,_j7,_j8,_)),_js=__app1(E(_iz),_j4),_jt=__arr2lst(0,_js),_ju=B(_6v(_jt,_));if(_j4!=_iZ){var _jv=E(_jr),_jw=E(_jv.b),_jx=B(_j3(_j4+1|0,E(_jw.a),E(_jw.b),_jw.c,_jw.d,_)),_jy=new T(function(){var _jz=new T(function(){return E(E(E(_j9).b).a);}),_jA=new T(function(){return E(E(E(_j9).b).b);}),_jB=new T(function(){return B(_iD(_jv.a));}),_jC=function(_jD){var _jE=E(_jD);if(!_jE._){return E(_jB);}else{var _jF=new T(function(){var _jG=E(_jE.a);return new T2(0,new T(function(){return B(_86(_jG.a,_jz));}),new T(function(){return B(_86(_jG.b,_jA));}));}),_jH=new T(function(){var _jI=E(_jF),_jJ=E(_jI.a),_jK=E(_jI.b);return Math.sqrt(_jJ*_jJ+_jK*_jK);}),_jL=new T(function(){var _jM=E(_jF),_jN=new T(function(){return 1/E(_jH);});return new T2(0,new T(function(){return B(_iU(_jM.a,_jN));}),new T(function(){return B(_iU(_jM.b,_jN));}));});return new T2(1,new T5(0,_j4,_j4,new T3(0,new T(function(){return E(E(_jL).a);}),new T(function(){return E(E(_jL).b);}),_az),_1m,_jH),new T(function(){return B(_jC(_jE.b));}));}};return B(_jC(_ju));});return new T2(0,new T2(1,_jy,new T(function(){return E(E(_jx).a);})),new T(function(){return E(E(_jx).b);}));}else{var _jO=new T(function(){var _jP=new T(function(){return E(E(E(_j9).b).a);}),_jQ=new T(function(){return E(E(E(_j9).b).b);}),_jR=new T(function(){return B(_iD(E(_jr).a));}),_jS=function(_jT){var _jU=E(_jT);if(!_jU._){return E(_jR);}else{var _jV=new T(function(){var _jW=E(_jU.a);return new T2(0,new T(function(){return B(_86(_jW.a,_jP));}),new T(function(){return B(_86(_jW.b,_jQ));}));}),_jX=new T(function(){var _jY=E(_jV),_jZ=E(_jY.a),_k0=E(_jY.b);return Math.sqrt(_jZ*_jZ+_k0*_k0);}),_k1=new T(function(){var _k2=E(_jV),_k3=new T(function(){return 1/E(_jX);});return new T2(0,new T(function(){return B(_iU(_k2.a,_k3));}),new T(function(){return B(_iU(_k2.b,_k3));}));});return new T2(1,new T5(0,_j4,_j4,new T3(0,new T(function(){return E(E(_k1).a);}),new T(function(){return E(E(_k1).b);}),_az),_1m,_jX),new T(function(){return B(_jS(_jU.b));}));}};return B(_jS(_ju));});return new T2(0,new T2(1,_jO,_4),new T(function(){return E(E(_jr).b);}));}}}},_k4=B(_j3(_iY,E(_j2.a),E(_j2.b),_j2.c,_j2.d,_));return new T2(0,new T(function(){return B(_iA(E(_k4).a));}),new T(function(){return E(E(_k4).b);}));}else{return new T2(0,_4,_j1);}},_k5=function(_k6){var _k7=E(_k6),_k8=_k7.c,_k9=new T(function(){var _ka=E(_k7.b),_kb=E(_k8);return new T3(0,new T(function(){return E(_ka.a)+E(_kb.a)*0.2;}),new T(function(){return E(_ka.b)+E(_kb.b)*0.2;}),new T(function(){return E(_ka.c)+E(_kb.c)*0.2;}));});return new T5(0,_k7.a,_k9,_k8,_k7.d,_k7.e);},_kc=function(_kd,_ke,_kf,_kg,_kh){var _ki=new T(function(){var _kj=E(_kf),_kk=E(_kg),_kl=new T(function(){var _km=E(E(_ke).b)/E(_i7);return 0.2*Math.sin((_km+_km)*3.141592653589793);});return new T3(0,new T(function(){return E(_kj.a)+E(_kk.a)*E(_kl);}),new T(function(){return E(_kj.b)+E(_kk.b)*E(_kl);}),new T(function(){return E(_kj.c)+E(_kk.c)*E(_kl);}));});return new T5(0,_kd,_ke,_ki,_kg,_kh);},_kn=function(_ko){var _kp=E(_ko),_kq=B(_kc(_kp.a,_kp.b,_kp.c,_kp.d,_kp.e));return new T5(0,_kq.a,_kq.b,_kq.c,_kq.d,_kq.e);},_kr=function(_ks,_){return new T2(0,_4,_ks);},_kt=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_ku=new T(function(){return B(err(_kt));}),_kv=0.6,_kw=function(_kx){var _ky=E(_kx);if(!_ky._){return E(_kr);}else{var _kz=_ky.a,_kA=new T(function(){return B(_kw(_ky.b));}),_kB=new T(function(){return 0.1*E(E(_kz).e)/0.2;}),_kC=new T(function(){var _kD=E(_kz);if(E(_kD.a)!=E(_kD.b)){return E(_aB);}else{return E(_kv);}}),_kE=function(_kF,_){var _kG=E(_kF),_kH=_kG.c,_kI=_kG.d,_kJ=E(_kG.a),_kK=E(_kG.b),_kL=E(_kz),_kM=E(_kL.a);if(_kJ>_kM){return E(_ku);}else{if(_kM>_kK){return E(_ku);}else{var _kN=_kM-_kJ|0;if(0>_kN){return new F(function(){return _iH(_kH,_kN);});}else{if(_kN>=_kH){return new F(function(){return _iH(_kH,_kN);});}else{var _kO=E(_kI[_kN]),_kP=E(_kO.e),_kQ=E(_kP.a),_kR=E(_kP.b),_kS=E(_kP.c),_kT=E(_kL.c),_kU=E(_kT.a),_kV=E(_kT.b),_kW=E(_kT.c),_kX=E(_kL.b);if(_kJ>_kX){return E(_ku);}else{if(_kX>_kK){return E(_ku);}else{var _kY=_kX-_kJ|0;if(0>_kY){return new F(function(){return _iM(_kY,_kH);});}else{if(_kY>=_kH){return new F(function(){return _iM(_kY,_kH);});}else{var _kZ=E(_kI[_kY]),_l0=E(_kZ.e),_l1=E(_l0.a),_l2=E(_l0.b),_l3=E(_l0.c),_l4=E(_kL.d),_l5=E(_l4.a),_l6=E(_l4.b),_l7=E(_l4.c),_l8=_kU*_kQ*_kU+_kV*_kR*_kV+_kW*_kS*_kW+_l5*_l1*_l5+_l6*_l2*_l6+_l7*_l3*_l7;if(!_l8){var _l9=B(A2(_kA,_kG,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_l9).a);})),new T(function(){return E(E(_l9).b);}));}else{var _la=E(_kO.c),_lb=E(_la.a),_lc=E(_la.b),_ld=E(_la.c),_le=E(_kZ.c),_lf= -((_lb*_kU+_lc*_kV+_ld*_kW-(E(_le.a)*_l5+E(_le.b)*_l6+E(_le.c)*_l7)-E(_kB))/_l8);if(_lf<0){var _lg=B(A2(_kA,_kG,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_lg).a);})),new T(function(){return E(E(_lg).b);}));}else{var _lh=new T(function(){var _li=function(_){var _lj=newArr(_kH,_1k),_lk=_lj,_ll=function(_lm,_){while(1){if(_lm!=_kH){var _=_lk[_lm]=_kI[_lm],_ln=_lm+1|0;_lm=_ln;continue;}else{return E(_);}}},_=B(_ll(0,_)),_lo=new T(function(){return _lf*E(_kC);}),_=_lk[_kN]=new T5(0,_kO.a,_kO.b,new T3(0,new T(function(){return _lb+_kQ*_kU*E(_lo);}),new T(function(){return _lc+_kR*_kV*E(_lo);}),new T(function(){return _ld+_kS*_kW*E(_lo);})),_kO.d,_kP);return new T4(0,E(_kJ),E(_kK),_kH,_lk);},_lp=B(_1M(_li)),_lq=_lp.c,_lr=_lp.d,_ls=E(_lp.a),_lt=E(_lp.b);if(_ls>_kX){return E(_lp);}else{if(_kX>_lt){return E(_lp);}else{var _lu=function(_){var _lv=newArr(_lq,_1k),_lw=_lv,_lx=function(_ly,_){while(1){if(_ly!=_lq){var _=_lw[_ly]=_lr[_ly],_lz=_ly+1|0;_ly=_lz;continue;}else{return E(_);}}},_=B(_lx(0,_)),_lA=_kX-_ls|0;if(0>_lA){return new F(function(){return _iM(_lA,_lq);});}else{if(_lA>=_lq){return new F(function(){return _iM(_lA,_lq);});}else{var _lB=new T(function(){var _lC=E(_lr[_lA]),_lD=new T(function(){return _lf*E(_kC);}),_lE=new T(function(){var _lF=E(_lC.c);return new T3(0,new T(function(){return E(_lF.a)-_l1*_l5*E(_lD);}),new T(function(){return E(_lF.b)-_l2*_l6*E(_lD);}),new T(function(){return E(_lF.c)-_l3*_l7*E(_lD);}));});return new T5(0,_lC.a,_lC.b,_lE,_lC.d,_lC.e);}),_=_lw[_lA]=_lB;return new T4(0,E(_ls),E(_lt),_lq,_lw);}}};return B(_1M(_lu));}}}),_lG=B(A2(_kA,_lh,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_lG).a);})),new T(function(){return E(E(_lG).b);}));}}}}}}}}}}};return E(_kE);}},_lH=new T1(0,1),_lI=function(_lJ,_lK){var _lL=E(_lJ);if(!_lL._){var _lM=_lL.a,_lN=E(_lK);if(!_lN._){var _lO=_lN.a;return (_lM!=_lO)?(_lM>_lO)?2:0:1;}else{var _lP=I_compareInt(_lN.a,_lM);return (_lP<=0)?(_lP>=0)?1:2:0;}}else{var _lQ=_lL.a,_lR=E(_lK);if(!_lR._){var _lS=I_compareInt(_lQ,_lR.a);return (_lS>=0)?(_lS<=0)?1:2:0;}else{var _lT=I_compare(_lQ,_lR.a);return (_lT>=0)?(_lT<=0)?1:2:0;}}},_lU=new T(function(){return B(unCStr("base"));}),_lV=new T(function(){return B(unCStr("GHC.Exception"));}),_lW=new T(function(){return B(unCStr("ArithException"));}),_lX=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_lU,_lV,_lW),_lY=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_lX,_4,_4),_lZ=function(_m0){return E(_lY);},_m1=function(_m2){var _m3=E(_m2);return new F(function(){return _6J(B(_6H(_m3.a)),_lZ,_m3.b);});},_m4=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_m5=new T(function(){return B(unCStr("denormal"));}),_m6=new T(function(){return B(unCStr("divide by zero"));}),_m7=new T(function(){return B(unCStr("loss of precision"));}),_m8=new T(function(){return B(unCStr("arithmetic underflow"));}),_m9=new T(function(){return B(unCStr("arithmetic overflow"));}),_ma=function(_mb,_mc){switch(E(_mb)){case 0:return new F(function(){return _0(_m9,_mc);});break;case 1:return new F(function(){return _0(_m8,_mc);});break;case 2:return new F(function(){return _0(_m7,_mc);});break;case 3:return new F(function(){return _0(_m6,_mc);});break;case 4:return new F(function(){return _0(_m5,_mc);});break;default:return new F(function(){return _0(_m4,_mc);});}},_md=function(_me){return new F(function(){return _ma(_me,_4);});},_mf=function(_mg,_mh,_mi){return new F(function(){return _ma(_mh,_mi);});},_mj=function(_mk,_ml){return new F(function(){return _2I(_ma,_mk,_ml);});},_mm=new T3(0,_mf,_md,_mj),_mn=new T(function(){return new T5(0,_lZ,_mm,_mo,_m1,_md);}),_mo=function(_bb){return new T2(0,_mn,_bb);},_mp=3,_mq=new T(function(){return B(_mo(_mp));}),_mr=new T(function(){return die(_mq);}),_ms=function(_mt,_mu){var _mv=E(_mt);return (_mv._==0)?_mv.a*Math.pow(2,_mu):I_toNumber(_mv.a)*Math.pow(2,_mu);},_mw=function(_mx,_my){var _mz=E(_mx);if(!_mz._){var _mA=_mz.a,_mB=E(_my);return (_mB._==0)?_mA==_mB.a:(I_compareInt(_mB.a,_mA)==0)?true:false;}else{var _mC=_mz.a,_mD=E(_my);return (_mD._==0)?(I_compareInt(_mC,_mD.a)==0)?true:false:(I_compare(_mC,_mD.a)==0)?true:false;}},_mE=function(_mF){var _mG=E(_mF);if(!_mG._){return E(_mG.a);}else{return new F(function(){return I_toInt(_mG.a);});}},_mH=function(_mI,_mJ){while(1){var _mK=E(_mI);if(!_mK._){var _mL=_mK.a,_mM=E(_mJ);if(!_mM._){var _mN=_mM.a,_mO=addC(_mL,_mN);if(!E(_mO.b)){return new T1(0,_mO.a);}else{_mI=new T1(1,I_fromInt(_mL));_mJ=new T1(1,I_fromInt(_mN));continue;}}else{_mI=new T1(1,I_fromInt(_mL));_mJ=_mM;continue;}}else{var _mP=E(_mJ);if(!_mP._){_mI=_mK;_mJ=new T1(1,I_fromInt(_mP.a));continue;}else{return new T1(1,I_add(_mK.a,_mP.a));}}}},_mQ=function(_mR,_mS){while(1){var _mT=E(_mR);if(!_mT._){var _mU=E(_mT.a);if(_mU==(-2147483648)){_mR=new T1(1,I_fromInt(-2147483648));continue;}else{var _mV=E(_mS);if(!_mV._){var _mW=_mV.a;return new T2(0,new T1(0,quot(_mU,_mW)),new T1(0,_mU%_mW));}else{_mR=new T1(1,I_fromInt(_mU));_mS=_mV;continue;}}}else{var _mX=E(_mS);if(!_mX._){_mR=_mT;_mS=new T1(1,I_fromInt(_mX.a));continue;}else{var _mY=I_quotRem(_mT.a,_mX.a);return new T2(0,new T1(1,_mY.a),new T1(1,_mY.b));}}}},_mZ=new T1(0,0),_n0=function(_n1,_n2){while(1){var _n3=E(_n1);if(!_n3._){_n1=new T1(1,I_fromInt(_n3.a));continue;}else{return new T1(1,I_shiftLeft(_n3.a,_n2));}}},_n4=function(_n5,_n6,_n7){if(!B(_mw(_n7,_mZ))){var _n8=B(_mQ(_n6,_n7)),_n9=_n8.a;switch(B(_lI(B(_n0(_n8.b,1)),_n7))){case 0:return new F(function(){return _ms(_n9,_n5);});break;case 1:if(!(B(_mE(_n9))&1)){return new F(function(){return _ms(_n9,_n5);});}else{return new F(function(){return _ms(B(_mH(_n9,_lH)),_n5);});}break;default:return new F(function(){return _ms(B(_mH(_n9,_lH)),_n5);});}}else{return E(_mr);}},_na=function(_nb,_nc){var _nd=E(_nb);if(!_nd._){var _ne=_nd.a,_nf=E(_nc);return (_nf._==0)?_ne>_nf.a:I_compareInt(_nf.a,_ne)<0;}else{var _ng=_nd.a,_nh=E(_nc);return (_nh._==0)?I_compareInt(_ng,_nh.a)>0:I_compare(_ng,_nh.a)>0;}},_ni=new T1(0,1),_nj=function(_nk,_nl){var _nm=E(_nk);if(!_nm._){var _nn=_nm.a,_no=E(_nl);return (_no._==0)?_nn<_no.a:I_compareInt(_no.a,_nn)>0;}else{var _np=_nm.a,_nq=E(_nl);return (_nq._==0)?I_compareInt(_np,_nq.a)<0:I_compare(_np,_nq.a)<0;}},_nr=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ns=function(_nt){return new F(function(){return _b9(new T1(0,new T(function(){return B(_bn(_nt,_nr));})),_aR);});},_nu=function(_nv){var _nw=function(_nx,_ny){while(1){if(!B(_nj(_nx,_nv))){if(!B(_na(_nx,_nv))){if(!B(_mw(_nx,_nv))){return new F(function(){return _ns("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ny);}}else{return _ny-1|0;}}else{var _nz=B(_n0(_nx,1)),_nA=_ny+1|0;_nx=_nz;_ny=_nA;continue;}}};return new F(function(){return _nw(_ni,0);});},_nB=function(_nC){var _nD=E(_nC);if(!_nD._){var _nE=_nD.a>>>0;if(!_nE){return -1;}else{var _nF=function(_nG,_nH){while(1){if(_nG>=_nE){if(_nG<=_nE){if(_nG!=_nE){return new F(function(){return _ns("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_nH);}}else{return _nH-1|0;}}else{var _nI=imul(_nG,2)>>>0,_nJ=_nH+1|0;_nG=_nI;_nH=_nJ;continue;}}};return new F(function(){return _nF(1,0);});}}else{return new F(function(){return _nu(_nD);});}},_nK=function(_nL){var _nM=E(_nL);if(!_nM._){var _nN=_nM.a>>>0;if(!_nN){return new T2(0,-1,0);}else{var _nO=function(_nP,_nQ){while(1){if(_nP>=_nN){if(_nP<=_nN){if(_nP!=_nN){return new F(function(){return _ns("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_nQ);}}else{return _nQ-1|0;}}else{var _nR=imul(_nP,2)>>>0,_nS=_nQ+1|0;_nP=_nR;_nQ=_nS;continue;}}};return new T2(0,B(_nO(1,0)),(_nN&_nN-1>>>0)>>>0&4294967295);}}else{var _nT=_nM.a;return new T2(0,B(_nB(_nM)),I_compareInt(I_and(_nT,I_sub(_nT,I_fromInt(1))),0));}},_nU=function(_nV,_nW){var _nX=E(_nV);if(!_nX._){var _nY=_nX.a,_nZ=E(_nW);return (_nZ._==0)?_nY<=_nZ.a:I_compareInt(_nZ.a,_nY)>=0;}else{var _o0=_nX.a,_o1=E(_nW);return (_o1._==0)?I_compareInt(_o0,_o1.a)<=0:I_compare(_o0,_o1.a)<=0;}},_o2=function(_o3,_o4){while(1){var _o5=E(_o3);if(!_o5._){var _o6=_o5.a,_o7=E(_o4);if(!_o7._){return new T1(0,(_o6>>>0&_o7.a>>>0)>>>0&4294967295);}else{_o3=new T1(1,I_fromInt(_o6));_o4=_o7;continue;}}else{var _o8=E(_o4);if(!_o8._){_o3=_o5;_o4=new T1(1,I_fromInt(_o8.a));continue;}else{return new T1(1,I_and(_o5.a,_o8.a));}}}},_o9=function(_oa,_ob){while(1){var _oc=E(_oa);if(!_oc._){var _od=_oc.a,_oe=E(_ob);if(!_oe._){var _of=_oe.a,_og=subC(_od,_of);if(!E(_og.b)){return new T1(0,_og.a);}else{_oa=new T1(1,I_fromInt(_od));_ob=new T1(1,I_fromInt(_of));continue;}}else{_oa=new T1(1,I_fromInt(_od));_ob=_oe;continue;}}else{var _oh=E(_ob);if(!_oh._){_oa=_oc;_ob=new T1(1,I_fromInt(_oh.a));continue;}else{return new T1(1,I_sub(_oc.a,_oh.a));}}}},_oi=new T1(0,2),_oj=function(_ok,_ol){var _om=E(_ok);if(!_om._){var _on=(_om.a>>>0&(2<<_ol>>>0)-1>>>0)>>>0,_oo=1<<_ol>>>0;return (_oo<=_on)?(_oo>=_on)?1:2:0;}else{var _op=B(_o2(_om,B(_o9(B(_n0(_oi,_ol)),_ni)))),_oq=B(_n0(_ni,_ol));return (!B(_na(_oq,_op)))?(!B(_nj(_oq,_op)))?1:2:0;}},_or=function(_os,_ot){while(1){var _ou=E(_os);if(!_ou._){_os=new T1(1,I_fromInt(_ou.a));continue;}else{return new T1(1,I_shiftRight(_ou.a,_ot));}}},_ov=function(_ow,_ox,_oy,_oz){var _oA=B(_nK(_oz)),_oB=_oA.a;if(!E(_oA.b)){var _oC=B(_nB(_oy));if(_oC<((_oB+_ow|0)-1|0)){var _oD=_oB+(_ow-_ox|0)|0;if(_oD>0){if(_oD>_oC){if(_oD<=(_oC+1|0)){if(!E(B(_nK(_oy)).b)){return 0;}else{return new F(function(){return _ms(_lH,_ow-_ox|0);});}}else{return 0;}}else{var _oE=B(_or(_oy,_oD));switch(B(_oj(_oy,_oD-1|0))){case 0:return new F(function(){return _ms(_oE,_ow-_ox|0);});break;case 1:if(!(B(_mE(_oE))&1)){return new F(function(){return _ms(_oE,_ow-_ox|0);});}else{return new F(function(){return _ms(B(_mH(_oE,_lH)),_ow-_ox|0);});}break;default:return new F(function(){return _ms(B(_mH(_oE,_lH)),_ow-_ox|0);});}}}else{return new F(function(){return _ms(_oy,(_ow-_ox|0)-_oD|0);});}}else{if(_oC>=_ox){var _oF=B(_or(_oy,(_oC+1|0)-_ox|0));switch(B(_oj(_oy,_oC-_ox|0))){case 0:return new F(function(){return _ms(_oF,((_oC-_oB|0)+1|0)-_ox|0);});break;case 2:return new F(function(){return _ms(B(_mH(_oF,_lH)),((_oC-_oB|0)+1|0)-_ox|0);});break;default:if(!(B(_mE(_oF))&1)){return new F(function(){return _ms(_oF,((_oC-_oB|0)+1|0)-_ox|0);});}else{return new F(function(){return _ms(B(_mH(_oF,_lH)),((_oC-_oB|0)+1|0)-_ox|0);});}}}else{return new F(function(){return _ms(_oy, -_oB);});}}}else{var _oG=B(_nB(_oy))-_oB|0,_oH=function(_oI){var _oJ=function(_oK,_oL){if(!B(_nU(B(_n0(_oL,_ox)),_oK))){return new F(function(){return _n4(_oI-_ox|0,_oK,_oL);});}else{return new F(function(){return _n4((_oI-_ox|0)+1|0,_oK,B(_n0(_oL,1)));});}};if(_oI>=_ox){if(_oI!=_ox){return new F(function(){return _oJ(_oy,new T(function(){return B(_n0(_oz,_oI-_ox|0));}));});}else{return new F(function(){return _oJ(_oy,_oz);});}}else{return new F(function(){return _oJ(new T(function(){return B(_n0(_oy,_ox-_oI|0));}),_oz);});}};if(_ow>_oG){return new F(function(){return _oH(_ow);});}else{return new F(function(){return _oH(_oG);});}}},_oM=new T1(0,2147483647),_oN=new T(function(){return B(_mH(_oM,_ni));}),_oO=function(_oP){var _oQ=E(_oP);if(!_oQ._){var _oR=E(_oQ.a);return (_oR==(-2147483648))?E(_oN):new T1(0, -_oR);}else{return new T1(1,I_negate(_oQ.a));}},_oS=new T(function(){return 0/0;}),_oT=new T(function(){return -1/0;}),_oU=new T(function(){return 1/0;}),_oV=0,_oW=function(_oX,_oY){if(!B(_mw(_oY,_mZ))){if(!B(_mw(_oX,_mZ))){if(!B(_nj(_oX,_mZ))){return new F(function(){return _ov(-1021,53,_oX,_oY);});}else{return  -B(_ov(-1021,53,B(_oO(_oX)),_oY));}}else{return E(_oV);}}else{return (!B(_mw(_oX,_mZ)))?(!B(_nj(_oX,_mZ)))?E(_oU):E(_oT):E(_oS);}},_oZ=function(_p0){var _p1=E(_p0);return new F(function(){return _oW(_p1.a,_p1.b);});},_p2=function(_p3){return 1/E(_p3);},_p4=function(_p5){var _p6=E(_p5),_p7=E(_p6);return (_p7==0)?E(_oV):(_p7<=0)? -_p7:E(_p6);},_p8=function(_p9){var _pa=E(_p9);if(!_pa._){return _pa.a;}else{return new F(function(){return I_toNumber(_pa.a);});}},_pb=function(_pc){return new F(function(){return _p8(_pc);});},_pd=function(_pe){var _pf=E(_pe);return (_pf<=0)?(_pf>=0)?E(_pf):E(_85):E(_84);},_pg=function(_ph,_pi){return E(_ph)+E(_pi);},_pj={_:0,a:_pg,b:_86,c:_iU,d:_bB,e:_p4,f:_pd,g:_pb},_pk=function(_pl,_pm){return E(_pl)/E(_pm);},_pn=new T4(0,_pj,_pk,_p2,_oZ),_po=function(_pp,_pq){return (E(_pp)!=E(_pq))?true:false;},_pr=function(_ps,_pt){return E(_ps)==E(_pt);},_pu=new T2(0,_pr,_po),_pv=function(_pw,_px){return E(_pw)<E(_px);},_py=function(_pz,_pA){return E(_pz)<=E(_pA);},_pB=function(_pC,_pD){return E(_pC)>E(_pD);},_pE=function(_pF,_pG){return E(_pF)>=E(_pG);},_pH=function(_pI,_pJ){var _pK=E(_pI),_pL=E(_pJ);return (_pK>=_pL)?(_pK!=_pL)?2:1:0;},_pM=function(_pN,_pO){var _pP=E(_pN),_pQ=E(_pO);return (_pP>_pQ)?E(_pP):E(_pQ);},_pR=function(_pS,_pT){var _pU=E(_pS),_pV=E(_pT);return (_pU>_pV)?E(_pV):E(_pU);},_pW={_:0,a:_pu,b:_pH,c:_pv,d:_py,e:_pB,f:_pE,g:_pM,h:_pR},_pX=function(_pY){var _pZ=I_decodeDouble(_pY);return new T2(0,new T1(1,_pZ.b),_pZ.a);},_q0=function(_q1){return new T1(0,_q1);},_q2=function(_q3){var _q4=hs_intToInt64(2147483647),_q5=hs_leInt64(_q3,_q4);if(!_q5){return new T1(1,I_fromInt64(_q3));}else{var _q6=hs_intToInt64(-2147483648),_q7=hs_geInt64(_q3,_q6);if(!_q7){return new T1(1,I_fromInt64(_q3));}else{var _q8=hs_int64ToInt(_q3);return new F(function(){return _q0(_q8);});}}},_q9=new T(function(){var _qa=newByteArr(256),_qb=_qa,_=_qb["v"]["i8"][0]=8,_qc=function(_qd,_qe,_qf,_){while(1){if(_qf>=256){if(_qd>=256){return E(_);}else{var _qg=imul(2,_qd)|0,_qh=_qe+1|0,_qi=_qd;_qd=_qg;_qe=_qh;_qf=_qi;continue;}}else{var _=_qb["v"]["i8"][_qf]=_qe,_qi=_qf+_qd|0;_qf=_qi;continue;}}},_=B(_qc(2,0,1,_));return _qb;}),_qj=function(_qk,_ql){var _qm=hs_int64ToInt(_qk),_qn=E(_q9),_qo=_qn["v"]["i8"][(255&_qm>>>0)>>>0&4294967295];if(_ql>_qo){if(_qo>=8){var _qp=hs_uncheckedIShiftRA64(_qk,8),_qq=function(_qr,_qs){while(1){var _qt=B((function(_qu,_qv){var _qw=hs_int64ToInt(_qu),_qx=_qn["v"]["i8"][(255&_qw>>>0)>>>0&4294967295];if(_qv>_qx){if(_qx>=8){var _qy=hs_uncheckedIShiftRA64(_qu,8),_qz=_qv-8|0;_qr=_qy;_qs=_qz;return __continue;}else{return new T2(0,new T(function(){var _qA=hs_uncheckedIShiftRA64(_qu,_qx);return B(_q2(_qA));}),_qv-_qx|0);}}else{return new T2(0,new T(function(){var _qB=hs_uncheckedIShiftRA64(_qu,_qv);return B(_q2(_qB));}),0);}})(_qr,_qs));if(_qt!=__continue){return _qt;}}};return new F(function(){return _qq(_qp,_ql-8|0);});}else{return new T2(0,new T(function(){var _qC=hs_uncheckedIShiftRA64(_qk,_qo);return B(_q2(_qC));}),_ql-_qo|0);}}else{return new T2(0,new T(function(){var _qD=hs_uncheckedIShiftRA64(_qk,_ql);return B(_q2(_qD));}),0);}},_qE=function(_qF){var _qG=hs_intToInt64(_qF);return E(_qG);},_qH=function(_qI){var _qJ=E(_qI);if(!_qJ._){return new F(function(){return _qE(_qJ.a);});}else{return new F(function(){return I_toInt64(_qJ.a);});}},_qK=function(_qL){return I_toInt(_qL)>>>0;},_qM=function(_qN){var _qO=E(_qN);if(!_qO._){return _qO.a>>>0;}else{return new F(function(){return _qK(_qO.a);});}},_qP=function(_qQ){var _qR=B(_pX(_qQ)),_qS=_qR.a,_qT=_qR.b;if(_qT<0){var _qU=function(_qV){if(!_qV){return new T2(0,E(_qS),B(_n0(_lH, -_qT)));}else{var _qW=B(_qj(B(_qH(_qS)), -_qT));return new T2(0,E(_qW.a),B(_n0(_lH,_qW.b)));}};if(!((B(_qM(_qS))&1)>>>0)){return new F(function(){return _qU(1);});}else{return new F(function(){return _qU(0);});}}else{return new T2(0,B(_n0(_qS,_qT)),_lH);}},_qX=function(_qY){var _qZ=B(_qP(E(_qY)));return new T2(0,E(_qZ.a),E(_qZ.b));},_r0=new T3(0,_pj,_pW,_qX),_r1=function(_r2){return E(E(_r2).a);},_r3=function(_r4){return E(E(_r4).a);},_r5=new T1(0,1),_r6=function(_r7){return new F(function(){return _41(E(_r7),2147483647);});},_r8=function(_r9,_ra,_rb){if(_rb<=_ra){var _rc=new T(function(){var _rd=_ra-_r9|0,_re=function(_rf){return (_rf>=(_rb-_rd|0))?new T2(1,_rf,new T(function(){return B(_re(_rf+_rd|0));})):new T2(1,_rf,_4);};return B(_re(_ra));});return new T2(1,_r9,_rc);}else{return (_rb<=_r9)?new T2(1,_r9,_4):__Z;}},_rg=function(_rh,_ri,_rj){if(_rj>=_ri){var _rk=new T(function(){var _rl=_ri-_rh|0,_rm=function(_rn){return (_rn<=(_rj-_rl|0))?new T2(1,_rn,new T(function(){return B(_rm(_rn+_rl|0));})):new T2(1,_rn,_4);};return B(_rm(_ri));});return new T2(1,_rh,_rk);}else{return (_rj>=_rh)?new T2(1,_rh,_4):__Z;}},_ro=function(_rp,_rq){if(_rq<_rp){return new F(function(){return _r8(_rp,_rq,-2147483648);});}else{return new F(function(){return _rg(_rp,_rq,2147483647);});}},_rr=function(_rs,_rt){return new F(function(){return _ro(E(_rs),E(_rt));});},_ru=function(_rv,_rw,_rx){if(_rw<_rv){return new F(function(){return _r8(_rv,_rw,_rx);});}else{return new F(function(){return _rg(_rv,_rw,_rx);});}},_ry=function(_rz,_rA,_rB){return new F(function(){return _ru(E(_rz),E(_rA),E(_rB));});},_rC=function(_rD){return E(_rD);},_rE=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_rF=new T(function(){return B(err(_rE));}),_rG=function(_rH){var _rI=E(_rH);return (_rI==(-2147483648))?E(_rF):_rI-1|0;},_rJ=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_rK=new T(function(){return B(err(_rJ));}),_rL=function(_rM){var _rN=E(_rM);return (_rN==2147483647)?E(_rK):_rN+1|0;},_rO={_:0,a:_rL,b:_rG,c:_rC,d:_rC,e:_r6,f:_rr,g:_46,h:_ry},_rP=function(_rQ,_rR){if(_rQ<=0){if(_rQ>=0){return new F(function(){return quot(_rQ,_rR);});}else{if(_rR<=0){return new F(function(){return quot(_rQ,_rR);});}else{return quot(_rQ+1|0,_rR)-1|0;}}}else{if(_rR>=0){if(_rQ>=0){return new F(function(){return quot(_rQ,_rR);});}else{if(_rR<=0){return new F(function(){return quot(_rQ,_rR);});}else{return quot(_rQ+1|0,_rR)-1|0;}}}else{return quot(_rQ-1|0,_rR)-1|0;}}},_rS=0,_rT=new T(function(){return B(_mo(_rS));}),_rU=new T(function(){return die(_rT);}),_rV=function(_rW,_rX){var _rY=E(_rX);switch(_rY){case -1:var _rZ=E(_rW);if(_rZ==(-2147483648)){return E(_rU);}else{return new F(function(){return _rP(_rZ,-1);});}break;case 0:return E(_mr);default:return new F(function(){return _rP(_rW,_rY);});}},_s0=function(_s1,_s2){return new F(function(){return _rV(E(_s1),E(_s2));});},_s3=0,_s4=new T2(0,_rU,_s3),_s5=function(_s6,_s7){var _s8=E(_s6),_s9=E(_s7);switch(_s9){case -1:var _sa=E(_s8);if(_sa==(-2147483648)){return E(_s4);}else{if(_sa<=0){if(_sa>=0){var _sb=quotRemI(_sa,-1);return new T2(0,_sb.a,_sb.b);}else{var _sc=quotRemI(_sa,-1);return new T2(0,_sc.a,_sc.b);}}else{var _sd=quotRemI(_sa-1|0,-1);return new T2(0,_sd.a-1|0,(_sd.b+(-1)|0)+1|0);}}break;case 0:return E(_mr);default:if(_s8<=0){if(_s8>=0){var _se=quotRemI(_s8,_s9);return new T2(0,_se.a,_se.b);}else{if(_s9<=0){var _sf=quotRemI(_s8,_s9);return new T2(0,_sf.a,_sf.b);}else{var _sg=quotRemI(_s8+1|0,_s9);return new T2(0,_sg.a-1|0,(_sg.b+_s9|0)-1|0);}}}else{if(_s9>=0){if(_s8>=0){var _sh=quotRemI(_s8,_s9);return new T2(0,_sh.a,_sh.b);}else{if(_s9<=0){var _si=quotRemI(_s8,_s9);return new T2(0,_si.a,_si.b);}else{var _sj=quotRemI(_s8+1|0,_s9);return new T2(0,_sj.a-1|0,(_sj.b+_s9|0)-1|0);}}}else{var _sk=quotRemI(_s8-1|0,_s9);return new T2(0,_sk.a-1|0,(_sk.b+_s9|0)+1|0);}}}},_sl=function(_sm,_sn){var _so=E(_sn);switch(_so){case -1:return E(_s3);case 0:return E(_mr);default:return new F(function(){return _bR(E(_sm),_so);});}},_sp=function(_sq,_sr){var _ss=E(_sq),_st=E(_sr);switch(_st){case -1:var _su=E(_ss);if(_su==(-2147483648)){return E(_rU);}else{return new F(function(){return quot(_su,-1);});}break;case 0:return E(_mr);default:return new F(function(){return quot(_ss,_st);});}},_sv=function(_sw,_sx){var _sy=E(_sw),_sz=E(_sx);switch(_sz){case -1:var _sA=E(_sy);if(_sA==(-2147483648)){return E(_s4);}else{var _sB=quotRemI(_sA,-1);return new T2(0,_sB.a,_sB.b);}break;case 0:return E(_mr);default:var _sC=quotRemI(_sy,_sz);return new T2(0,_sC.a,_sC.b);}},_sD=function(_sE,_sF){var _sG=E(_sF);switch(_sG){case -1:return E(_s3);case 0:return E(_mr);default:return E(_sE)%_sG;}},_sH=function(_sI){return new F(function(){return _q0(E(_sI));});},_sJ=function(_sK){return new T2(0,E(B(_q0(E(_sK)))),E(_r5));},_sL=function(_sM,_sN){return imul(E(_sM),E(_sN))|0;},_sO=function(_sP,_sQ){return E(_sP)+E(_sQ)|0;},_sR=function(_sS){var _sT=E(_sS);return (_sT<0)? -_sT:E(_sT);},_sU=function(_sV){return new F(function(){return _mE(_sV);});},_sW=function(_sX){return  -E(_sX);},_sY=-1,_sZ=0,_t0=1,_t1=function(_t2){var _t3=E(_t2);return (_t3>=0)?(E(_t3)==0)?E(_sZ):E(_t0):E(_sY);},_t4={_:0,a:_sO,b:_4h,c:_sL,d:_sW,e:_sR,f:_t1,g:_sU},_t5=new T3(0,_t4,_4W,_sJ),_t6={_:0,a:_t5,b:_rO,c:_sp,d:_sD,e:_s0,f:_sl,g:_sv,h:_s5,i:_sH},_t7=new T1(0,2),_t8=function(_t9,_ta){while(1){var _tb=E(_t9);if(!_tb._){var _tc=_tb.a,_td=E(_ta);if(!_td._){var _te=_td.a;if(!(imul(_tc,_te)|0)){return new T1(0,imul(_tc,_te)|0);}else{_t9=new T1(1,I_fromInt(_tc));_ta=new T1(1,I_fromInt(_te));continue;}}else{_t9=new T1(1,I_fromInt(_tc));_ta=_td;continue;}}else{var _tf=E(_ta);if(!_tf._){_t9=_tb;_ta=new T1(1,I_fromInt(_tf.a));continue;}else{return new T1(1,I_mul(_tb.a,_tf.a));}}}},_tg=function(_th,_ti,_tj){while(1){if(!(_ti%2)){var _tk=B(_t8(_th,_th)),_tl=quot(_ti,2);_th=_tk;_ti=_tl;continue;}else{var _tm=E(_ti);if(_tm==1){return new F(function(){return _t8(_th,_tj);});}else{var _tk=B(_t8(_th,_th)),_tn=B(_t8(_th,_tj));_th=_tk;_ti=quot(_tm-1|0,2);_tj=_tn;continue;}}}},_to=function(_tp,_tq){while(1){if(!(_tq%2)){var _tr=B(_t8(_tp,_tp)),_ts=quot(_tq,2);_tp=_tr;_tq=_ts;continue;}else{var _tt=E(_tq);if(_tt==1){return E(_tp);}else{return new F(function(){return _tg(B(_t8(_tp,_tp)),quot(_tt-1|0,2),_tp);});}}}},_tu=function(_tv){return E(E(_tv).c);},_tw=function(_tx){return E(E(_tx).a);},_ty=function(_tz){return E(E(_tz).b);},_tA=function(_tB){return E(E(_tB).b);},_tC=function(_tD){return E(E(_tD).c);},_tE=function(_tF){return E(E(_tF).a);},_tG=new T1(0,0),_tH=new T1(0,2),_tI=function(_tJ){return E(E(_tJ).g);},_tK=function(_tL){return E(E(_tL).d);},_tM=function(_tN,_tO){var _tP=B(_r1(_tN)),_tQ=new T(function(){return B(_r3(_tP));}),_tR=new T(function(){return B(A3(_tK,_tN,_tO,new T(function(){return B(A2(_tI,_tQ,_tH));})));});return new F(function(){return A3(_tE,B(_tw(B(_ty(_tP)))),_tR,new T(function(){return B(A2(_tI,_tQ,_tG));}));});},_tS=new T(function(){return B(unCStr("Negative exponent"));}),_tT=new T(function(){return B(err(_tS));}),_tU=function(_tV){return E(E(_tV).c);},_tW=function(_tX,_tY,_tZ,_u0){var _u1=B(_r1(_tY)),_u2=new T(function(){return B(_r3(_u1));}),_u3=B(_ty(_u1));if(!B(A3(_tC,_u3,_u0,new T(function(){return B(A2(_tI,_u2,_tG));})))){if(!B(A3(_tE,B(_tw(_u3)),_u0,new T(function(){return B(A2(_tI,_u2,_tG));})))){var _u4=new T(function(){return B(A2(_tI,_u2,_tH));}),_u5=new T(function(){return B(A2(_tI,_u2,_r5));}),_u6=B(_tw(_u3)),_u7=function(_u8,_u9,_ua){while(1){var _ub=B((function(_uc,_ud,_ue){if(!B(_tM(_tY,_ud))){if(!B(A3(_tE,_u6,_ud,_u5))){var _uf=new T(function(){return B(A3(_tU,_tY,new T(function(){return B(A3(_tA,_u2,_ud,_u5));}),_u4));});_u8=new T(function(){return B(A3(_tu,_tX,_uc,_uc));});_u9=_uf;_ua=new T(function(){return B(A3(_tu,_tX,_uc,_ue));});return __continue;}else{return new F(function(){return A3(_tu,_tX,_uc,_ue);});}}else{var _ug=_ue;_u8=new T(function(){return B(A3(_tu,_tX,_uc,_uc));});_u9=new T(function(){return B(A3(_tU,_tY,_ud,_u4));});_ua=_ug;return __continue;}})(_u8,_u9,_ua));if(_ub!=__continue){return _ub;}}},_uh=function(_ui,_uj){while(1){var _uk=B((function(_ul,_um){if(!B(_tM(_tY,_um))){if(!B(A3(_tE,_u6,_um,_u5))){var _un=new T(function(){return B(A3(_tU,_tY,new T(function(){return B(A3(_tA,_u2,_um,_u5));}),_u4));});return new F(function(){return _u7(new T(function(){return B(A3(_tu,_tX,_ul,_ul));}),_un,_ul);});}else{return E(_ul);}}else{_ui=new T(function(){return B(A3(_tu,_tX,_ul,_ul));});_uj=new T(function(){return B(A3(_tU,_tY,_um,_u4));});return __continue;}})(_ui,_uj));if(_uk!=__continue){return _uk;}}};return new F(function(){return _uh(_tZ,_u0);});}else{return new F(function(){return A2(_tI,_tX,_r5);});}}else{return E(_tT);}},_uo=new T(function(){return B(err(_tS));}),_up=function(_uq,_ur){var _us=B(_pX(_ur)),_ut=_us.a,_uu=_us.b,_uv=new T(function(){return B(_r3(new T(function(){return B(_r1(_uq));})));});if(_uu<0){var _uw= -_uu;if(_uw>=0){var _ux=E(_uw);if(!_ux){var _uy=E(_r5);}else{var _uy=B(_to(_t7,_ux));}if(!B(_mw(_uy,_mZ))){var _uz=B(_mQ(_ut,_uy));return new T2(0,new T(function(){return B(A2(_tI,_uv,_uz.a));}),new T(function(){return B(_ms(_uz.b,_uu));}));}else{return E(_mr);}}else{return E(_uo);}}else{var _uA=new T(function(){var _uB=new T(function(){return B(_tW(_uv,_t6,new T(function(){return B(A2(_tI,_uv,_t7));}),_uu));});return B(A3(_tu,_uv,new T(function(){return B(A2(_tI,_uv,_ut));}),_uB));});return new T2(0,_uA,_oV);}},_uC=function(_uD){return E(E(_uD).a);},_uE=function(_uF,_uG){var _uH=B(_up(_uF,E(_uG))),_uI=_uH.a;if(E(_uH.b)<=0){return E(_uI);}else{var _uJ=B(_r3(B(_r1(_uF))));return new F(function(){return A3(_uC,_uJ,_uI,new T(function(){return B(A2(_tI,_uJ,_lH));}));});}},_uK=function(_uL,_uM){var _uN=B(_up(_uL,E(_uM))),_uO=_uN.a;if(E(_uN.b)>=0){return E(_uO);}else{var _uP=B(_r3(B(_r1(_uL))));return new F(function(){return A3(_tA,_uP,_uO,new T(function(){return B(A2(_tI,_uP,_lH));}));});}},_uQ=function(_uR,_uS){var _uT=B(_up(_uR,E(_uS)));return new T2(0,_uT.a,_uT.b);},_uU=function(_uV,_uW){var _uX=B(_up(_uV,_uW)),_uY=_uX.a,_uZ=E(_uX.b),_v0=new T(function(){var _v1=B(_r3(B(_r1(_uV))));if(_uZ>=0){return B(A3(_uC,_v1,_uY,new T(function(){return B(A2(_tI,_v1,_lH));})));}else{return B(A3(_tA,_v1,_uY,new T(function(){return B(A2(_tI,_v1,_lH));})));}}),_v2=function(_v3){var _v4=_v3-0.5;return (_v4>=0)?(E(_v4)==0)?(!B(_tM(_uV,_uY)))?E(_v0):E(_uY):E(_v0):E(_uY);},_v5=E(_uZ);if(!_v5){return new F(function(){return _v2(0);});}else{if(_v5<=0){var _v6= -_v5-0.5;return (_v6>=0)?(E(_v6)==0)?(!B(_tM(_uV,_uY)))?E(_v0):E(_uY):E(_v0):E(_uY);}else{return new F(function(){return _v2(_v5);});}}},_v7=function(_v8,_v9){return new F(function(){return _uU(_v8,E(_v9));});},_va=function(_vb,_vc){return E(B(_up(_vb,E(_vc))).a);},_vd={_:0,a:_r0,b:_pn,c:_uQ,d:_va,e:_v7,f:_uE,g:_uK},_ve=new T1(0,1),_vf=function(_vg,_vh){var _vi=E(_vg);return new T2(0,_vi,new T(function(){var _vj=B(_vf(B(_mH(_vi,_vh)),_vh));return new T2(1,_vj.a,_vj.b);}));},_vk=function(_vl){var _vm=B(_vf(_vl,_ve));return new T2(1,_vm.a,_vm.b);},_vn=function(_vo,_vp){var _vq=B(_vf(_vo,new T(function(){return B(_o9(_vp,_vo));})));return new T2(1,_vq.a,_vq.b);},_vr=new T1(0,0),_vs=function(_vt,_vu){var _vv=E(_vt);if(!_vv._){var _vw=_vv.a,_vx=E(_vu);return (_vx._==0)?_vw>=_vx.a:I_compareInt(_vx.a,_vw)<=0;}else{var _vy=_vv.a,_vz=E(_vu);return (_vz._==0)?I_compareInt(_vy,_vz.a)>=0:I_compare(_vy,_vz.a)>=0;}},_vA=function(_vB,_vC,_vD){if(!B(_vs(_vC,_vr))){var _vE=function(_vF){return (!B(_nj(_vF,_vD)))?new T2(1,_vF,new T(function(){return B(_vE(B(_mH(_vF,_vC))));})):__Z;};return new F(function(){return _vE(_vB);});}else{var _vG=function(_vH){return (!B(_na(_vH,_vD)))?new T2(1,_vH,new T(function(){return B(_vG(B(_mH(_vH,_vC))));})):__Z;};return new F(function(){return _vG(_vB);});}},_vI=function(_vJ,_vK,_vL){return new F(function(){return _vA(_vJ,B(_o9(_vK,_vJ)),_vL);});},_vM=function(_vN,_vO){return new F(function(){return _vA(_vN,_ve,_vO);});},_vP=function(_vQ){return new F(function(){return _mE(_vQ);});},_vR=function(_vS){return new F(function(){return _o9(_vS,_ve);});},_vT=function(_vU){return new F(function(){return _mH(_vU,_ve);});},_vV=function(_vW){return new F(function(){return _q0(E(_vW));});},_vX={_:0,a:_vT,b:_vR,c:_vV,d:_vP,e:_vk,f:_vn,g:_vM,h:_vI},_vY=function(_vZ,_w0){while(1){var _w1=E(_vZ);if(!_w1._){var _w2=E(_w1.a);if(_w2==(-2147483648)){_vZ=new T1(1,I_fromInt(-2147483648));continue;}else{var _w3=E(_w0);if(!_w3._){return new T1(0,B(_rP(_w2,_w3.a)));}else{_vZ=new T1(1,I_fromInt(_w2));_w0=_w3;continue;}}}else{var _w4=_w1.a,_w5=E(_w0);return (_w5._==0)?new T1(1,I_div(_w4,I_fromInt(_w5.a))):new T1(1,I_div(_w4,_w5.a));}}},_w6=function(_w7,_w8){if(!B(_mw(_w8,_tG))){return new F(function(){return _vY(_w7,_w8);});}else{return E(_mr);}},_w9=function(_wa,_wb){while(1){var _wc=E(_wa);if(!_wc._){var _wd=E(_wc.a);if(_wd==(-2147483648)){_wa=new T1(1,I_fromInt(-2147483648));continue;}else{var _we=E(_wb);if(!_we._){var _wf=_we.a;return new T2(0,new T1(0,B(_rP(_wd,_wf))),new T1(0,B(_bR(_wd,_wf))));}else{_wa=new T1(1,I_fromInt(_wd));_wb=_we;continue;}}}else{var _wg=E(_wb);if(!_wg._){_wa=_wc;_wb=new T1(1,I_fromInt(_wg.a));continue;}else{var _wh=I_divMod(_wc.a,_wg.a);return new T2(0,new T1(1,_wh.a),new T1(1,_wh.b));}}}},_wi=function(_wj,_wk){if(!B(_mw(_wk,_tG))){var _wl=B(_w9(_wj,_wk));return new T2(0,_wl.a,_wl.b);}else{return E(_mr);}},_wm=function(_wn,_wo){while(1){var _wp=E(_wn);if(!_wp._){var _wq=E(_wp.a);if(_wq==(-2147483648)){_wn=new T1(1,I_fromInt(-2147483648));continue;}else{var _wr=E(_wo);if(!_wr._){return new T1(0,B(_bR(_wq,_wr.a)));}else{_wn=new T1(1,I_fromInt(_wq));_wo=_wr;continue;}}}else{var _ws=_wp.a,_wt=E(_wo);return (_wt._==0)?new T1(1,I_mod(_ws,I_fromInt(_wt.a))):new T1(1,I_mod(_ws,_wt.a));}}},_wu=function(_wv,_ww){if(!B(_mw(_ww,_tG))){return new F(function(){return _wm(_wv,_ww);});}else{return E(_mr);}},_wx=function(_wy,_wz){while(1){var _wA=E(_wy);if(!_wA._){var _wB=E(_wA.a);if(_wB==(-2147483648)){_wy=new T1(1,I_fromInt(-2147483648));continue;}else{var _wC=E(_wz);if(!_wC._){return new T1(0,quot(_wB,_wC.a));}else{_wy=new T1(1,I_fromInt(_wB));_wz=_wC;continue;}}}else{var _wD=_wA.a,_wE=E(_wz);return (_wE._==0)?new T1(0,I_toInt(I_quot(_wD,I_fromInt(_wE.a)))):new T1(1,I_quot(_wD,_wE.a));}}},_wF=function(_wG,_wH){if(!B(_mw(_wH,_tG))){return new F(function(){return _wx(_wG,_wH);});}else{return E(_mr);}},_wI=function(_wJ,_wK){if(!B(_mw(_wK,_tG))){var _wL=B(_mQ(_wJ,_wK));return new T2(0,_wL.a,_wL.b);}else{return E(_mr);}},_wM=function(_wN,_wO){while(1){var _wP=E(_wN);if(!_wP._){var _wQ=E(_wP.a);if(_wQ==(-2147483648)){_wN=new T1(1,I_fromInt(-2147483648));continue;}else{var _wR=E(_wO);if(!_wR._){return new T1(0,_wQ%_wR.a);}else{_wN=new T1(1,I_fromInt(_wQ));_wO=_wR;continue;}}}else{var _wS=_wP.a,_wT=E(_wO);return (_wT._==0)?new T1(1,I_rem(_wS,I_fromInt(_wT.a))):new T1(1,I_rem(_wS,_wT.a));}}},_wU=function(_wV,_wW){if(!B(_mw(_wW,_tG))){return new F(function(){return _wM(_wV,_wW);});}else{return E(_mr);}},_wX=function(_wY){return E(_wY);},_wZ=function(_x0){return E(_x0);},_x1=function(_x2){var _x3=E(_x2);if(!_x3._){var _x4=E(_x3.a);return (_x4==(-2147483648))?E(_oN):(_x4<0)?new T1(0, -_x4):E(_x3);}else{var _x5=_x3.a;return (I_compareInt(_x5,0)>=0)?E(_x3):new T1(1,I_negate(_x5));}},_x6=new T1(0,0),_x7=new T1(0,-1),_x8=function(_x9){var _xa=E(_x9);if(!_xa._){var _xb=_xa.a;return (_xb>=0)?(E(_xb)==0)?E(_x6):E(_ni):E(_x7);}else{var _xc=I_compareInt(_xa.a,0);return (_xc<=0)?(E(_xc)==0)?E(_x6):E(_x7):E(_ni);}},_xd={_:0,a:_mH,b:_o9,c:_t8,d:_oO,e:_x1,f:_x8,g:_wZ},_xe=function(_xf,_xg){var _xh=E(_xf);if(!_xh._){var _xi=_xh.a,_xj=E(_xg);return (_xj._==0)?_xi!=_xj.a:(I_compareInt(_xj.a,_xi)==0)?false:true;}else{var _xk=_xh.a,_xl=E(_xg);return (_xl._==0)?(I_compareInt(_xk,_xl.a)==0)?false:true:(I_compare(_xk,_xl.a)==0)?false:true;}},_xm=new T2(0,_mw,_xe),_xn=function(_xo,_xp){return (!B(_nU(_xo,_xp)))?E(_xo):E(_xp);},_xq=function(_xr,_xs){return (!B(_nU(_xr,_xs)))?E(_xs):E(_xr);},_xt={_:0,a:_xm,b:_lI,c:_nj,d:_nU,e:_na,f:_vs,g:_xn,h:_xq},_xu=function(_xv){return new T2(0,E(_xv),E(_r5));},_xw=new T3(0,_xd,_xt,_xu),_xx={_:0,a:_xw,b:_vX,c:_wF,d:_wU,e:_w6,f:_wu,g:_wI,h:_wi,i:_wX},_xy=function(_xz){return E(E(_xz).a);},_xA=function(_xB){return E(E(_xB).b);},_xC=function(_xD){return E(E(_xD).b);},_xE=function(_xF){return E(E(_xF).g);},_xG=new T1(0,1),_xH=function(_xI){return E(E(_xI).d);},_xJ=function(_xK,_xL,_xM){var _xN=B(_xA(_xK)),_xO=B(_xy(_xN)),_xP=new T(function(){var _xQ=new T(function(){var _xR=new T(function(){var _xS=new T(function(){return B(A3(_xE,_xK,_xx,new T(function(){return B(A3(_xC,_xN,_xL,_xM));})));});return B(A2(_tI,_xO,_xS));}),_xT=new T(function(){return B(A2(_xH,_xO,new T(function(){return B(A2(_tI,_xO,_xG));})));});return B(A3(_tu,_xO,_xT,_xR));});return B(A3(_tu,_xO,_xQ,_xM));});return new F(function(){return A3(_uC,_xO,_xL,_xP);});},_xU=function(_xV){var _xW=new T(function(){var _xX=E(E(_xV).b);return new T3(0,new T(function(){return B(_xJ(_vd,_xX.a,_1t));}),new T(function(){return B(_xJ(_vd,_xX.b,_i7));}),_xX.c);});return new T5(0,new T(function(){return E(E(_xV).a);}),_xW,new T(function(){return E(E(_xV).c);}),new T(function(){return E(E(_xV).d);}),new T(function(){return E(E(_xV).e);}));},_xY=function(_xZ,_){var _y0=B(_5y(_4X,_6g,_kn,_xZ)),_y1=B(_iX(E(_y0.a),E(_y0.b),_y0.d,_y0,_)),_y2=new T(function(){return B(_kw(E(_y1).a));}),_y3=function(_y4){var _y5=E(_y4);return (_y5==1)?E(new T2(1,_y2,_4)):new T2(1,_y2,new T(function(){return B(_y3(_y5-1|0));}));},_y6=B(_6h(B(_y3(5)),new T(function(){return E(E(_y1).b);}),_)),_y7=new T(function(){var _y8=new T(function(){return B(_5y(_4X,_6g,_k5,new T(function(){return E(E(_y6).b);})));});return B(_5y(_4X,_6g,_xU,_y8));});return new T2(0,_5,_y7);},_y9=new T(function(){return eval("refresh");}),_ya=function(_yb,_){var _yc=__app0(E(_y9)),_yd=B(A(_5y,[_4X,_2f,_5X,_yb,_])),_ye=__app0(E(_5O)),_yf=B(_xY(_yb,_));return new T(function(){return E(E(_yf).b);});},_yg=function(_yh,_yi,_yj){var _yk=function(_){var _yl=B(_ya(_yh,_));return new T(function(){return B(A1(_yj,new T1(1,_yl)));});};return new T1(0,_yk);},_ym=new T0(2),_yn=function(_yo,_yp,_yq){return function(_){var _yr=E(_yo),_ys=rMV(_yr),_yt=E(_ys);if(!_yt._){var _yu=new T(function(){var _yv=new T(function(){return B(A1(_yq,_5));});return B(_0(_yt.b,new T2(1,new T2(0,_yp,function(_yw){return E(_yv);}),_4)));}),_=wMV(_yr,new T2(0,_yt.a,_yu));return _ym;}else{var _yx=E(_yt.a);if(!_yx._){var _=wMV(_yr,new T2(0,_yp,_4));return new T(function(){return B(A1(_yq,_5));});}else{var _=wMV(_yr,new T1(1,_yx.b));return new T1(1,new T2(1,new T(function(){return B(A1(_yq,_5));}),new T2(1,new T(function(){return B(A2(_yx.a,_yp,_19));}),_4)));}}};},_yy=function(_yz){return E(E(_yz).b);},_yA=function(_yB,_yC,_yD){var _yE=new T(function(){return new T1(0,B(_yn(_yC,_yD,_19)));}),_yF=function(_yG){return new T1(1,new T2(1,new T(function(){return B(A1(_yG,_5));}),new T2(1,_yE,_4)));};return new F(function(){return A2(_yy,_yB,_yF);});},_yH=new T1(1,_4),_yI=function(_yJ,_yK){return function(_){var _yL=E(_yJ),_yM=rMV(_yL),_yN=E(_yM);if(!_yN._){var _yO=_yN.a,_yP=E(_yN.b);if(!_yP._){var _=wMV(_yL,_yH);return new T(function(){return B(A1(_yK,_yO));});}else{var _yQ=E(_yP.a),_=wMV(_yL,new T2(0,_yQ.a,_yP.b));return new T1(1,new T2(1,new T(function(){return B(A1(_yK,_yO));}),new T2(1,new T(function(){return B(A1(_yQ.b,_19));}),_4)));}}else{var _yR=new T(function(){var _yS=function(_yT){var _yU=new T(function(){return B(A1(_yK,_yT));});return function(_yV){return E(_yU);};};return B(_0(_yN.a,new T2(1,_yS,_4)));}),_=wMV(_yL,new T1(1,_yR));return _ym;}};},_yW=function(_){return new F(function(){return __jsNull();});},_yX=function(_yY){var _yZ=B(A1(_yY,_));return E(_yZ);},_z0=new T(function(){return B(_yX(_yW));}),_z1=new T(function(){return E(_z0);}),_z2=new T(function(){return eval("window.requestAnimationFrame");}),_z3=new T1(1,_4),_z4=function(_z5){var _z6=new T(function(){return B(_z7(_));}),_z8=new T(function(){var _z9=function(_za){return E(_z6);},_zb=function(_){var _zc=nMV(_z3),_zd=_zc,_ze=new T(function(){return new T1(0,B(_yn(_zd,_5,_19)));}),_zf=function(_){var _zg=__createJSFunc(2,function(_zh,_){var _zi=B(_c(_ze,_4,_));return _z1;}),_zj=__app1(E(_z2),_zg);return new T(function(){return new T1(0,B(_yI(_zd,_z9)));});};return new T1(0,_zf);};return B(A(_yA,[_1i,_z5,_5,function(_zk){return E(new T1(0,_zb));}]));}),_z7=function(_zl){return E(_z8);};return new F(function(){return _z7(_);});},_zm=function(_zn){return E(E(_zn).a);},_zo=function(_zp){return E(E(_zp).d);},_zq=function(_zr){return E(E(_zr).c);},_zs=function(_zt){return E(E(_zt).c);},_zu=new T1(1,_4),_zv=function(_zw){var _zx=function(_){var _zy=nMV(_zu);return new T(function(){return B(A1(_zw,_zy));});};return new T1(0,_zx);},_zz=function(_zA,_zB){var _zC=new T(function(){return B(_zs(_zA));}),_zD=B(_zm(_zA)),_zE=function(_zF){var _zG=new T(function(){return B(A1(_zC,new T(function(){return B(A1(_zB,_zF));})));});return new F(function(){return A3(_zq,_zD,_zG,new T(function(){return B(A2(_zo,_zD,_zF));}));});};return new F(function(){return A3(_10,_zD,new T(function(){return B(A2(_yy,_zA,_zv));}),_zE);});},_zH=function(_zI,_zJ){return new T1(0,B(_yI(_zI,_zJ)));},_zK=function(_zL,_zM,_zN){var _zO=new T(function(){return B(_zm(_zL));}),_zP=new T(function(){return B(A2(_zo,_zO,_5));}),_zQ=function(_zR,_zS){var _zT=new T(function(){var _zU=new T(function(){return B(A2(_yy,_zL,function(_zV){return new F(function(){return _zH(_zS,_zV);});}));});return B(A3(_10,_zO,_zU,new T(function(){return B(A1(_zN,_zR));})));});return new F(function(){return A3(_10,_zO,_zT,function(_zW){var _zX=E(_zW);if(!_zX._){return E(_zP);}else{return new F(function(){return _zQ(_zX.a,_zS);});}});});};return new F(function(){return _zz(_zL,function(_zV){return new F(function(){return _zQ(_zM,_zV);});});});},_zY=new T(function(){return B(A(_zK,[_1i,_1P,_yg,_z4]));}),_zZ=function(_){return new F(function(){return _c(_zY,_4,_);});},_A0=function(_){return new F(function(){return _zZ(_);});};
var hasteMain = function() {B(A(_A0, [0]));};window.onload = hasteMain;