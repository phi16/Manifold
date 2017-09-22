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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==(-2147483648)){_3l=new T1(1,I_fromInt(-2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0,-1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==(-2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S(-1021,53,_6k,_6l);});}else{return  -B(_5S(-1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=function(_7h){return E(E(_7h).a);},_7i=function(_7j){return E(E(_7j).a);},_7k=function(_7l){return E(E(_7l).c);},_7m=function(_7n){return E(E(_7n).b);},_7o=function(_7p){return E(E(_7p).d);},_7q=new T1(0,1),_7r=new T1(0,2),_7s=new T2(0,E(_7q),E(_7r)),_7t=new T1(0,5),_7u=new T1(0,4),_7v=new T2(0,E(_7u),E(_7t)),_7w=function(_7x){return E(E(_7x).e);},_7y=function(_7z,_7A,_7B,_7C){var _7D=B(_7g(_7z)),_7E=B(_7i(_7D)),_7F=new T(function(){var _7G=new T(function(){var _7H=new T(function(){var _7I=new T(function(){var _7J=new T(function(){var _7K=new T(function(){return B(A3(_6I,_7E,new T(function(){return B(A3(_7k,_7E,_7A,_7A));}),new T(function(){return B(A3(_7k,_7E,_7C,_7C));})));});return B(A2(_7w,_7z,_7K));});return B(A3(_7m,_7E,_7J,new T(function(){return B(A2(_7o,_7D,_7v));})));});return B(A3(_7k,_7E,_7I,_7I));});return B(A3(_6I,_7E,_7H,new T(function(){return B(A3(_7k,_7E,_7B,_7B));})));});return B(A2(_7w,_7z,_7G));});return new F(function(){return A3(_7m,_7E,_7F,new T(function(){return B(A2(_7o,_7D,_7s));}));});},_7L=new T(function(){return B(unCStr("x"));}),_7M=new T1(0,_7L),_7N=new T(function(){return B(unCStr("y"));}),_7O=new T1(0,_7N),_7P=new T(function(){return B(unCStr("z"));}),_7Q=new T1(0,_7P),_7R=new T(function(){return B(_7y(_7f,_7M,_7O,_7Q));}),_7S=function(_7T){return E(_7T);},_7U=new T(function(){return toJSStr(B(_5(_p,_7S,_7R)));}),_7V=function(_7W,_7X,_7Y){var _7Z=new T(function(){return B(_1(_7W));}),_80=new T(function(){return B(_3(_7W));}),_81=function(_82){var _83=E(_82);if(!_83._){return E(_80);}else{return new F(function(){return A2(_7Z,new T(function(){return B(_5(_7W,_7X,_83.a));}),new T(function(){return B(_81(_83.b));}));});}};return new F(function(){return _81(_7Y);});},_84=new T3(0,E(_7M),E(_7O),E(_7Q)),_85=new T(function(){return B(unCStr("(/=) is not defined"));}),_86=new T(function(){return B(err(_85));}),_87=new T(function(){return B(unCStr("(==) is not defined"));}),_88=new T(function(){return B(err(_87));}),_89=new T2(0,_88,_86),_8a=new T(function(){return B(unCStr("(<) is not defined"));}),_8b=new T(function(){return B(err(_8a));}),_8c=new T(function(){return B(unCStr("(<=) is not defined"));}),_8d=new T(function(){return B(err(_8c));}),_8e=new T(function(){return B(unCStr("(>) is not defined"));}),_8f=new T(function(){return B(err(_8e));}),_8g=new T(function(){return B(unCStr("(>=) is not defined"));}),_8h=new T(function(){return B(err(_8g));}),_8i=new T(function(){return B(unCStr("compare is not defined"));}),_8j=new T(function(){return B(err(_8i));}),_8k=new T(function(){return B(unCStr("max("));}),_8l=new T1(0,_8k),_8m=function(_8n,_8o){return new T1(1,new T2(1,_8l,new T2(1,_8n,new T2(1,_r,new T2(1,_8o,_w)))));},_8p=new T(function(){return B(unCStr("min("));}),_8q=new T1(0,_8p),_8r=function(_8s,_8t){return new T1(1,new T2(1,_8q,new T2(1,_8s,new T2(1,_r,new T2(1,_8t,_w)))));},_8u={_:0,a:_89,b:_8j,c:_8b,d:_8d,e:_8f,f:_8h,g:_8m,h:_8r},_8v=new T2(0,_7f,_8u),_8w=function(_8x,_8y){var _8z=E(_8x);return E(_8y);},_8A=function(_8B,_8C){var _8D=E(_8C);return E(_8B);},_8E=function(_8F,_8G){var _8H=E(_8F),_8I=E(_8G);return new T3(0,E(B(A1(_8H.a,_8I.a))),E(B(A1(_8H.b,_8I.b))),E(B(A1(_8H.c,_8I.c))));},_8J=function(_8K,_8L,_8M){return new T3(0,E(_8K),E(_8L),E(_8M));},_8N=function(_8O){return new F(function(){return _8J(_8O,_8O,_8O);});},_8P=function(_8Q,_8R){var _8S=E(_8R),_8T=E(_8Q);return new T3(0,E(_8T),E(_8T),E(_8T));},_8U=function(_8V,_8W){var _8X=E(_8W);return new T3(0,E(B(A1(_8V,_8X.a))),E(B(A1(_8V,_8X.b))),E(B(A1(_8V,_8X.c))));},_8Y=new T2(0,_8U,_8P),_8Z=new T5(0,_8Y,_8N,_8E,_8w,_8A),_90=new T1(0,0),_91=function(_92){return E(E(_92).g);},_93=function(_94){var _95=B(A2(_91,_94,_7q)),_96=B(A2(_91,_94,_90));return new T3(0,E(new T3(0,E(_95),E(_96),E(_96))),E(new T3(0,E(_96),E(_95),E(_96))),E(new T3(0,E(_96),E(_96),E(_95))));},_97=function(_98){return E(E(_98).a);},_99=function(_9a){return E(E(_9a).f);},_9b=function(_9c){return E(E(_9c).b);},_9d=function(_9e){return E(E(_9e).c);},_9f=function(_9g){return E(E(_9g).a);},_9h=function(_9i){return E(E(_9i).d);},_9j=function(_9k,_9l,_9m,_9n,_9o){var _9p=new T(function(){return E(E(E(_9k).c).a);}),_9q=new T(function(){var _9r=E(_9k).a,_9s=new T(function(){var _9t=new T(function(){return B(_7g(_9p));}),_9u=new T(function(){return B(_7i(_9t));}),_9v=new T(function(){return B(A2(_9h,_9p,_9l));}),_9w=new T(function(){return B(A3(_99,_9p,_9l,_9n));}),_9x=function(_9y,_9z){var _9A=new T(function(){var _9B=new T(function(){return B(A3(_9b,_9t,new T(function(){return B(A3(_7k,_9u,_9n,_9y));}),_9l));});return B(A3(_6I,_9u,_9B,new T(function(){return B(A3(_7k,_9u,_9z,_9v));})));});return new F(function(){return A3(_7k,_9u,_9w,_9A);});};return B(A3(_9f,B(_97(_9r)),_9x,_9m));});return B(A3(_9d,_9r,_9s,_9o));});return new T2(0,new T(function(){return B(A3(_99,_9p,_9l,_9n));}),_9q);},_9C=function(_9D,_9E,_9F,_9G){var _9H=E(_9F),_9I=E(_9G),_9J=B(_9j(_9E,_9H.a,_9H.b,_9I.a,_9I.b));return new T2(0,_9J.a,_9J.b);},_9K=new T1(0,1),_9L=function(_9M){return E(E(_9M).l);},_9N=function(_9O,_9P,_9Q){var _9R=new T(function(){return E(E(E(_9O).c).a);}),_9S=new T(function(){var _9T=new T(function(){return B(_7g(_9R));}),_9U=new T(function(){var _9V=B(_7i(_9T)),_9W=new T(function(){var _9X=new T(function(){return B(A3(_7m,_9V,new T(function(){return B(A2(_91,_9V,_9K));}),new T(function(){return B(A3(_7k,_9V,_9P,_9P));})));});return B(A2(_7w,_9R,_9X));});return B(A2(_6K,_9V,_9W));});return B(A3(_9f,B(_97(E(_9O).a)),function(_9Y){return new F(function(){return A3(_9b,_9T,_9Y,_9U);});},_9Q));});return new T2(0,new T(function(){return B(A2(_9L,_9R,_9P));}),_9S);},_9Z=function(_a0,_a1,_a2){var _a3=E(_a2),_a4=B(_9N(_a1,_a3.a,_a3.b));return new T2(0,_a4.a,_a4.b);},_a5=function(_a6){return E(E(_a6).r);},_a7=function(_a8,_a9,_aa){var _ab=new T(function(){return E(E(E(_a8).c).a);}),_ac=new T(function(){var _ad=new T(function(){return B(_7g(_ab));}),_ae=new T(function(){var _af=new T(function(){var _ag=B(_7i(_ad));return B(A3(_7m,_ag,new T(function(){return B(A3(_7k,_ag,_a9,_a9));}),new T(function(){return B(A2(_91,_ag,_9K));})));});return B(A2(_7w,_ab,_af));});return B(A3(_9f,B(_97(E(_a8).a)),function(_ah){return new F(function(){return A3(_9b,_ad,_ah,_ae);});},_aa));});return new T2(0,new T(function(){return B(A2(_a5,_ab,_a9));}),_ac);},_ai=function(_aj,_ak,_al){var _am=E(_al),_an=B(_a7(_ak,_am.a,_am.b));return new T2(0,_an.a,_an.b);},_ao=function(_ap){return E(E(_ap).k);},_aq=function(_ar,_as,_at){var _au=new T(function(){return E(E(E(_ar).c).a);}),_av=new T(function(){var _aw=new T(function(){return B(_7g(_au));}),_ax=new T(function(){var _ay=new T(function(){var _az=B(_7i(_aw));return B(A3(_7m,_az,new T(function(){return B(A2(_91,_az,_9K));}),new T(function(){return B(A3(_7k,_az,_as,_as));})));});return B(A2(_7w,_au,_ay));});return B(A3(_9f,B(_97(E(_ar).a)),function(_aA){return new F(function(){return A3(_9b,_aw,_aA,_ax);});},_at));});return new T2(0,new T(function(){return B(A2(_ao,_au,_as));}),_av);},_aB=function(_aC,_aD,_aE){var _aF=E(_aE),_aG=B(_aq(_aD,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=function(_aI){return E(E(_aI).q);},_aJ=function(_aK,_aL,_aM){var _aN=new T(function(){return E(E(E(_aK).c).a);}),_aO=new T(function(){var _aP=new T(function(){return B(_7g(_aN));}),_aQ=new T(function(){var _aR=new T(function(){var _aS=B(_7i(_aP));return B(A3(_6I,_aS,new T(function(){return B(A3(_7k,_aS,_aL,_aL));}),new T(function(){return B(A2(_91,_aS,_9K));})));});return B(A2(_7w,_aN,_aR));});return B(A3(_9f,B(_97(E(_aK).a)),function(_aT){return new F(function(){return A3(_9b,_aP,_aT,_aQ);});},_aM));});return new T2(0,new T(function(){return B(A2(_aH,_aN,_aL));}),_aO);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aJ(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).m);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_7g(_b6));}),_b9=new T(function(){var _ba=B(_7i(_b8));return B(A3(_6I,_ba,new T(function(){return B(A2(_91,_ba,_9K));}),new T(function(){return B(A3(_7k,_ba,_b4,_b4));})));});return B(A3(_9f,B(_97(E(_b3).a)),function(_bb){return new F(function(){return A3(_9b,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).s);},_bk=function(_bl,_bm,_bn){var _bo=new T(function(){return E(E(E(_bl).c).a);}),_bp=new T(function(){var _bq=new T(function(){return B(_7g(_bo));}),_br=new T(function(){var _bs=B(_7i(_bq));return B(A3(_7m,_bs,new T(function(){return B(A2(_91,_bs,_9K));}),new T(function(){return B(A3(_7k,_bs,_bm,_bm));})));});return B(A3(_9f,B(_97(E(_bl).a)),function(_bt){return new F(function(){return A3(_9b,_bq,_bt,_br);});},_bn));});return new T2(0,new T(function(){return B(A2(_bi,_bo,_bm));}),_bp);},_bu=function(_bv,_bw,_bx){var _by=E(_bx),_bz=B(_bk(_bw,_by.a,_by.b));return new T2(0,_bz.a,_bz.b);},_bA=function(_bB){return E(E(_bB).i);},_bC=function(_bD){return E(E(_bD).h);},_bE=function(_bF,_bG,_bH){var _bI=new T(function(){return E(E(E(_bF).c).a);}),_bJ=new T(function(){var _bK=new T(function(){return B(_7i(new T(function(){return B(_7g(_bI));})));}),_bL=new T(function(){return B(A2(_6K,_bK,new T(function(){return B(A2(_bC,_bI,_bG));})));});return B(A3(_9f,B(_97(E(_bF).a)),function(_bM){return new F(function(){return A3(_7k,_bK,_bM,_bL);});},_bH));});return new T2(0,new T(function(){return B(A2(_bA,_bI,_bG));}),_bJ);},_bN=function(_bO,_bP,_bQ){var _bR=E(_bQ),_bS=B(_bE(_bP,_bR.a,_bR.b));return new T2(0,_bS.a,_bS.b);},_bT=function(_bU){return E(E(_bU).o);},_bV=function(_bW){return E(E(_bW).n);},_bX=function(_bY,_bZ,_c0){var _c1=new T(function(){return E(E(E(_bY).c).a);}),_c2=new T(function(){var _c3=new T(function(){return B(_7i(new T(function(){return B(_7g(_c1));})));}),_c4=new T(function(){return B(A2(_bV,_c1,_bZ));});return B(A3(_9f,B(_97(E(_bY).a)),function(_c5){return new F(function(){return A3(_7k,_c3,_c5,_c4);});},_c0));});return new T2(0,new T(function(){return B(A2(_bT,_c1,_bZ));}),_c2);},_c6=function(_c7,_c8,_c9){var _ca=E(_c9),_cb=B(_bX(_c8,_ca.a,_ca.b));return new T2(0,_cb.a,_cb.b);},_cc=function(_cd){return E(E(_cd).c);},_ce=function(_cf,_cg,_ch){var _ci=new T(function(){return E(E(E(_cf).c).a);}),_cj=new T(function(){var _ck=new T(function(){return B(_7i(new T(function(){return B(_7g(_ci));})));}),_cl=new T(function(){return B(A2(_cc,_ci,_cg));});return B(A3(_9f,B(_97(E(_cf).a)),function(_cm){return new F(function(){return A3(_7k,_ck,_cm,_cl);});},_ch));});return new T2(0,new T(function(){return B(A2(_cc,_ci,_cg));}),_cj);},_cn=function(_co,_cp,_cq){var _cr=E(_cq),_cs=B(_ce(_cp,_cr.a,_cr.b));return new T2(0,_cs.a,_cs.b);},_ct=function(_cu,_cv,_cw){var _cx=new T(function(){return E(E(E(_cu).c).a);}),_cy=new T(function(){var _cz=new T(function(){return B(_7g(_cx));}),_cA=new T(function(){return B(_7i(_cz));}),_cB=new T(function(){return B(A3(_9b,_cz,new T(function(){return B(A2(_91,_cA,_9K));}),_cv));});return B(A3(_9f,B(_97(E(_cu).a)),function(_cC){return new F(function(){return A3(_7k,_cA,_cC,_cB);});},_cw));});return new T2(0,new T(function(){return B(A2(_9h,_cx,_cv));}),_cy);},_cD=function(_cE,_cF,_cG){var _cH=E(_cG),_cI=B(_ct(_cF,_cH.a,_cH.b));return new T2(0,_cI.a,_cI.b);},_cJ=function(_cK,_cL,_cM,_cN){var _cO=new T(function(){return E(E(_cL).c);}),_cP=new T3(0,new T(function(){return E(E(_cL).a);}),new T(function(){return E(E(_cL).b);}),new T2(0,new T(function(){return E(E(_cO).a);}),new T(function(){return E(E(_cO).b);})));return new F(function(){return A3(_9b,_cK,new T(function(){var _cQ=E(_cN),_cR=B(_ct(_cP,_cQ.a,_cQ.b));return new T2(0,_cR.a,_cR.b);}),new T(function(){var _cS=E(_cM),_cT=B(_ct(_cP,_cS.a,_cS.b));return new T2(0,_cT.a,_cT.b);}));});},_cU=new T1(0,0),_cV=function(_cW){return E(E(_cW).b);},_cX=function(_cY){return E(E(_cY).b);},_cZ=function(_d0){var _d1=new T(function(){return E(E(E(_d0).c).a);}),_d2=new T(function(){return B(A2(_cX,E(_d0).a,new T(function(){return B(A2(_91,B(_7i(B(_7g(_d1)))),_cU));})));});return new T2(0,new T(function(){return B(_cV(_d1));}),_d2);},_d3=function(_d4,_d5){var _d6=B(_cZ(_d5));return new T2(0,_d6.a,_d6.b);},_d7=function(_d8,_d9,_da){var _db=new T(function(){return E(E(E(_d8).c).a);}),_dc=new T(function(){var _dd=new T(function(){return B(_7i(new T(function(){return B(_7g(_db));})));}),_de=new T(function(){return B(A2(_bA,_db,_d9));});return B(A3(_9f,B(_97(E(_d8).a)),function(_df){return new F(function(){return A3(_7k,_dd,_df,_de);});},_da));});return new T2(0,new T(function(){return B(A2(_bC,_db,_d9));}),_dc);},_dg=function(_dh,_di,_dj){var _dk=E(_dj),_dl=B(_d7(_di,_dk.a,_dk.b));return new T2(0,_dl.a,_dl.b);},_dm=function(_dn,_do,_dp){var _dq=new T(function(){return E(E(E(_dn).c).a);}),_dr=new T(function(){var _ds=new T(function(){return B(_7i(new T(function(){return B(_7g(_dq));})));}),_dt=new T(function(){return B(A2(_bT,_dq,_do));});return B(A3(_9f,B(_97(E(_dn).a)),function(_du){return new F(function(){return A3(_7k,_ds,_du,_dt);});},_dp));});return new T2(0,new T(function(){return B(A2(_bV,_dq,_do));}),_dr);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dm(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=new T1(0,2),_dC=function(_dD,_dE,_dF){var _dG=new T(function(){return E(E(E(_dD).c).a);}),_dH=new T(function(){var _dI=new T(function(){return B(_7g(_dG));}),_dJ=new T(function(){return B(_7i(_dI));}),_dK=new T(function(){var _dL=new T(function(){return B(A3(_9b,_dI,new T(function(){return B(A2(_91,_dJ,_9K));}),new T(function(){return B(A2(_91,_dJ,_dB));})));});return B(A3(_9b,_dI,_dL,new T(function(){return B(A2(_7w,_dG,_dE));})));});return B(A3(_9f,B(_97(E(_dD).a)),function(_dM){return new F(function(){return A3(_7k,_dJ,_dM,_dK);});},_dF));});return new T2(0,new T(function(){return B(A2(_7w,_dG,_dE));}),_dH);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dC(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).j);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_7g(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bA,_dZ,_dX));});return B(A3(_7k,B(_7i(_e1)),_e3,_e3));});return B(A3(_9f,B(_97(E(_dW).a)),function(_e4){return new F(function(){return A3(_9b,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec){return E(E(_ec).p);},_ed=function(_ee,_ef,_eg){var _eh=new T(function(){return E(E(E(_ee).c).a);}),_ei=new T(function(){var _ej=new T(function(){return B(_7g(_eh));}),_ek=new T(function(){var _el=new T(function(){return B(A2(_bT,_eh,_ef));});return B(A3(_7k,B(_7i(_ej)),_el,_el));});return B(A3(_9f,B(_97(E(_ee).a)),function(_em){return new F(function(){return A3(_9b,_ej,_em,_ek);});},_eg));});return new T2(0,new T(function(){return B(A2(_eb,_eh,_ef));}),_ei);},_en=function(_eo,_ep,_eq){var _er=E(_eq),_es=B(_ed(_ep,_er.a,_er.b));return new T2(0,_es.a,_es.b);},_et=function(_eu,_ev){return {_:0,a:_eu,b:new T(function(){return B(_d3(_eu,_ev));}),c:function(_ew){return new F(function(){return _cn(_eu,_ev,_ew);});},d:function(_ew){return new F(function(){return _cD(_eu,_ev,_ew);});},e:function(_ew){return new F(function(){return _dN(_eu,_ev,_ew);});},f:function(_ex,_ew){return new F(function(){return _9C(_eu,_ev,_ex,_ew);});},g:function(_ex,_ew){return new F(function(){return _cJ(_eu,_ev,_ex,_ew);});},h:function(_ew){return new F(function(){return _dg(_eu,_ev,_ew);});},i:function(_ew){return new F(function(){return _bN(_eu,_ev,_ew);});},j:function(_ew){return new F(function(){return _e5(_eu,_ev,_ew);});},k:function(_ew){return new F(function(){return _aB(_eu,_ev,_ew);});},l:function(_ew){return new F(function(){return _9Z(_eu,_ev,_ew);});},m:function(_ew){return new F(function(){return _bc(_eu,_ev,_ew);});},n:function(_ew){return new F(function(){return _dv(_eu,_ev,_ew);});},o:function(_ew){return new F(function(){return _c6(_eu,_ev,_ew);});},p:function(_ew){return new F(function(){return _en(_eu,_ev,_ew);});},q:function(_ew){return new F(function(){return _aU(_eu,_ev,_ew);});},r:function(_ew){return new F(function(){return _ai(_eu,_ev,_ew);});},s:function(_ew){return new F(function(){return _bu(_eu,_ev,_ew);});}};},_ey=function(_ez,_eA,_eB,_eC,_eD){var _eE=new T(function(){return B(_7g(new T(function(){return E(E(E(_ez).c).a);})));}),_eF=new T(function(){var _eG=E(_ez).a,_eH=new T(function(){var _eI=new T(function(){return B(_7i(_eE));}),_eJ=new T(function(){return B(A3(_7k,_eI,_eC,_eC));}),_eK=function(_eL,_eM){var _eN=new T(function(){return B(A3(_7m,_eI,new T(function(){return B(A3(_7k,_eI,_eL,_eC));}),new T(function(){return B(A3(_7k,_eI,_eA,_eM));})));});return new F(function(){return A3(_9b,_eE,_eN,_eJ);});};return B(A3(_9f,B(_97(_eG)),_eK,_eB));});return B(A3(_9d,_eG,_eH,_eD));});return new T2(0,new T(function(){return B(A3(_9b,_eE,_eA,_eC));}),_eF);},_eO=function(_eP,_eQ,_eR,_eS){var _eT=E(_eR),_eU=E(_eS),_eV=B(_ey(_eQ,_eT.a,_eT.b,_eU.a,_eU.b));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX,_eY){var _eZ=new T(function(){return B(_7g(new T(function(){return E(E(E(_eX).c).a);})));}),_f0=new T(function(){return B(A2(_cX,E(_eX).a,new T(function(){return B(A2(_91,B(_7i(_eZ)),_cU));})));});return new T2(0,new T(function(){return B(A2(_7o,_eZ,_eY));}),_f0);},_f1=function(_f2,_f3,_f4){var _f5=B(_eW(_f3,_f4));return new T2(0,_f5.a,_f5.b);},_f6=function(_f7,_f8,_f9){var _fa=new T(function(){return B(_7g(new T(function(){return E(E(E(_f7).c).a);})));}),_fb=new T(function(){return B(_7i(_fa));}),_fc=new T(function(){var _fd=new T(function(){var _fe=new T(function(){return B(A3(_9b,_fa,new T(function(){return B(A2(_91,_fb,_9K));}),new T(function(){return B(A3(_7k,_fb,_f8,_f8));})));});return B(A2(_6K,_fb,_fe));});return B(A3(_9f,B(_97(E(_f7).a)),function(_ff){return new F(function(){return A3(_7k,_fb,_ff,_fd);});},_f9));}),_fg=new T(function(){return B(A3(_9b,_fa,new T(function(){return B(A2(_91,_fb,_9K));}),_f8));});return new T2(0,_fg,_fc);},_fh=function(_fi,_fj,_fk){var _fl=E(_fk),_fm=B(_f6(_fj,_fl.a,_fl.b));return new T2(0,_fm.a,_fm.b);},_fn=function(_fo,_fp){return new T4(0,_fo,function(_ex,_ew){return new F(function(){return _eO(_fo,_fp,_ex,_ew);});},function(_ew){return new F(function(){return _fh(_fo,_fp,_ew);});},function(_ew){return new F(function(){return _f1(_fo,_fp,_ew);});});},_fq=function(_fr,_fs,_ft,_fu,_fv){var _fw=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fr).c).a);})));})));}),_fx=new T(function(){var _fy=E(_fr).a,_fz=new T(function(){var _fA=function(_fB,_fC){return new F(function(){return A3(_6I,_fw,new T(function(){return B(A3(_7k,_fw,_fs,_fC));}),new T(function(){return B(A3(_7k,_fw,_fB,_fu));}));});};return B(A3(_9f,B(_97(_fy)),_fA,_ft));});return B(A3(_9d,_fy,_fz,_fv));});return new T2(0,new T(function(){return B(A3(_7k,_fw,_fs,_fu));}),_fx);},_fD=function(_fE,_fF,_fG){var _fH=E(_fF),_fI=E(_fG),_fJ=B(_fq(_fE,_fH.a,_fH.b,_fI.a,_fI.b));return new T2(0,_fJ.a,_fJ.b);},_fK=function(_fL,_fM,_fN,_fO,_fP){var _fQ=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fL).c).a);})));})));}),_fR=new T(function(){var _fS=E(_fL).a,_fT=new T(function(){return B(A3(_9f,B(_97(_fS)),new T(function(){return B(_6I(_fQ));}),_fN));});return B(A3(_9d,_fS,_fT,_fP));});return new T2(0,new T(function(){return B(A3(_6I,_fQ,_fM,_fO));}),_fR);},_fU=function(_fV,_fW,_fX){var _fY=E(_fW),_fZ=E(_fX),_g0=B(_fK(_fV,_fY.a,_fY.b,_fZ.a,_fZ.b));return new T2(0,_g0.a,_g0.b);},_g1=function(_g2,_g3,_g4){var _g5=B(_g6(_g2));return new F(function(){return A3(_6I,_g5,_g3,new T(function(){return B(A2(_6K,_g5,_g4));}));});},_g7=function(_g8){return E(E(_g8).e);},_g9=function(_ga){return E(E(_ga).f);},_gb=function(_gc,_gd,_ge){var _gf=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gc).c).a);})));})));}),_gg=new T(function(){var _gh=new T(function(){return B(A2(_g9,_gf,_gd));});return B(A3(_9f,B(_97(E(_gc).a)),function(_gi){return new F(function(){return A3(_7k,_gf,_gi,_gh);});},_ge));});return new T2(0,new T(function(){return B(A2(_g7,_gf,_gd));}),_gg);},_gj=function(_gk,_gl){var _gm=E(_gl),_gn=B(_gb(_gk,_gm.a,_gm.b));return new T2(0,_gn.a,_gn.b);},_go=function(_gp,_gq){var _gr=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gs=new T(function(){return B(A2(_cX,E(_gp).a,new T(function(){return B(A2(_91,_gr,_cU));})));});return new T2(0,new T(function(){return B(A2(_91,_gr,_gq));}),_gs);},_gt=function(_gu,_gv){var _gw=B(_go(_gu,_gv));return new T2(0,_gw.a,_gw.b);},_gx=function(_gy,_gz,_gA){var _gB=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gy).c).a);})));})));}),_gC=new T(function(){return B(A3(_9f,B(_97(E(_gy).a)),new T(function(){return B(_6K(_gB));}),_gA));});return new T2(0,new T(function(){return B(A2(_6K,_gB,_gz));}),_gC);},_gD=function(_gE,_gF){var _gG=E(_gF),_gH=B(_gx(_gE,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK){var _gL=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gM=new T(function(){return B(A2(_cX,E(_gJ).a,new T(function(){return B(A2(_91,_gL,_cU));})));});return new T2(0,new T(function(){return B(A2(_g9,_gL,_gK));}),_gM);},_gN=function(_gO,_gP){var _gQ=B(_gI(_gO,E(_gP).a));return new T2(0,_gQ.a,_gQ.b);},_g6=function(_gR){return {_:0,a:function(_ex,_ew){return new F(function(){return _fU(_gR,_ex,_ew);});},b:function(_ex,_ew){return new F(function(){return _g1(_gR,_ex,_ew);});},c:function(_ex,_ew){return new F(function(){return _fD(_gR,_ex,_ew);});},d:function(_ew){return new F(function(){return _gD(_gR,_ew);});},e:function(_ew){return new F(function(){return _gj(_gR,_ew);});},f:function(_ew){return new F(function(){return _gN(_gR,_ew);});},g:function(_ew){return new F(function(){return _gt(_gR,_ew);});}};},_gS=function(_gT){var _gU=new T(function(){return E(E(_gT).a);}),_gV=new T3(0,_8Z,_93,new T2(0,_gU,new T(function(){return E(E(_gT).b);}))),_gW=new T(function(){return B(_et(new T(function(){return B(_fn(new T(function(){return B(_g6(_gV));}),_gV));}),_gV));}),_gX=new T(function(){return B(_7i(new T(function(){return B(_7g(_gU));})));});return function(_gY){var _gZ=E(_gY),_h0=B(A2(_91,_gX,_7q)),_h1=B(A2(_91,_gX,_90));return E(B(_7y(_gW,new T2(0,_gZ.a,new T3(0,E(_h0),E(_h1),E(_h1))),new T2(0,_gZ.b,new T3(0,E(_h1),E(_h0),E(_h1))),new T2(0,_gZ.c,new T3(0,E(_h1),E(_h1),E(_h0))))).b);};},_h2=new T(function(){return B(_gS(_8v));}),_h3=function(_h4,_h5){var _h6=E(_h5);return (_h6._==0)?__Z:new T2(1,_h4,new T2(1,_h6.a,new T(function(){return B(_h3(_h4,_h6.b));})));},_h7=new T(function(){var _h8=B(A1(_h2,_84));return new T2(1,_h8.a,new T(function(){return B(_h3(_r,new T2(1,_h8.b,new T2(1,_h8.c,_o))));}));}),_h9=new T1(1,_h7),_ha=new T2(1,_h9,_w),_hb=new T(function(){return B(unCStr("vec3("));}),_hc=new T1(0,_hb),_hd=new T2(1,_hc,_ha),_he=new T(function(){return toJSStr(B(_7V(_p,_7S,_hd)));}),_hf=function(_hg,_hh){while(1){var _hi=E(_hg);if(!_hi._){return E(_hh);}else{var _hj=_hh+1|0;_hg=_hi.b;_hh=_hj;continue;}}},_hk=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hl=new T(function(){return B(err(_hk));}),_hm=0,_hn=new T3(0,E(_hm),E(_hm),E(_hm)),_ho=new T(function(){return B(unCStr("Negative exponent"));}),_hp=new T(function(){return B(err(_ho));}),_hq=function(_hr,_hs,_ht){while(1){if(!(_hs%2)){var _hu=_hr*_hr,_hv=quot(_hs,2);_hr=_hu;_hs=_hv;continue;}else{var _hw=E(_hs);if(_hw==1){return _hr*_ht;}else{var _hu=_hr*_hr,_hx=_hr*_ht;_hr=_hu;_hs=quot(_hw-1|0,2);_ht=_hx;continue;}}}},_hy=function(_hz,_hA){while(1){if(!(_hA%2)){var _hB=_hz*_hz,_hC=quot(_hA,2);_hz=_hB;_hA=_hC;continue;}else{var _hD=E(_hA);if(_hD==1){return E(_hz);}else{return new F(function(){return _hq(_hz*_hz,quot(_hD-1|0,2),_hz);});}}}},_hE=function(_hF){var _hG=E(_hF);return new F(function(){return Math.log(_hG+(_hG+1)*Math.sqrt((_hG-1)/(_hG+1)));});},_hH=function(_hI){var _hJ=E(_hI);return new F(function(){return Math.log(_hJ+Math.sqrt(1+_hJ*_hJ));});},_hK=function(_hL){var _hM=E(_hL);return 0.5*Math.log((1+_hM)/(1-_hM));},_hN=function(_hO,_hP){return Math.log(E(_hP))/Math.log(E(_hO));},_hQ=3.141592653589793,_hR=function(_hS){var _hT=E(_hS);return new F(function(){return _6j(_hT.a,_hT.b);});},_hU=function(_hV){return 1/E(_hV);},_hW=function(_hX){var _hY=E(_hX),_hZ=E(_hY);return (_hZ==0)?E(_6i):(_hZ<=0)? -_hZ:E(_hY);},_i0=function(_i1){var _i2=E(_i1);if(!_i2._){return _i2.a;}else{return new F(function(){return I_toNumber(_i2.a);});}},_i3=function(_i4){return new F(function(){return _i0(_i4);});},_i5=1,_i6=-1,_i7=function(_i8){var _i9=E(_i8);return (_i9<=0)?(_i9>=0)?E(_i9):E(_i6):E(_i5);},_ia=function(_ib,_ic){return E(_ib)-E(_ic);},_id=function(_ie){return  -E(_ie);},_if=function(_ig,_ih){return E(_ig)+E(_ih);},_ii=function(_ij,_ik){return E(_ij)*E(_ik);},_il={_:0,a:_if,b:_ia,c:_ii,d:_id,e:_hW,f:_i7,g:_i3},_im=function(_in,_io){return E(_in)/E(_io);},_ip=new T4(0,_il,_im,_hU,_hR),_iq=function(_ir){return new F(function(){return Math.acos(E(_ir));});},_is=function(_it){return new F(function(){return Math.asin(E(_it));});},_iu=function(_iv){return new F(function(){return Math.atan(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.cos(E(_ix));});},_iy=function(_iz){return new F(function(){return cosh(E(_iz));});},_iA=function(_iB){return new F(function(){return Math.exp(E(_iB));});},_iC=function(_iD){return new F(function(){return Math.log(E(_iD));});},_iE=function(_iF,_iG){return new F(function(){return Math.pow(E(_iF),E(_iG));});},_iH=function(_iI){return new F(function(){return Math.sin(E(_iI));});},_iJ=function(_iK){return new F(function(){return sinh(E(_iK));});},_iL=function(_iM){return new F(function(){return Math.sqrt(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.tan(E(_iO));});},_iP=function(_iQ){return new F(function(){return tanh(E(_iQ));});},_iR={_:0,a:_ip,b:_hQ,c:_iA,d:_iC,e:_iL,f:_iE,g:_hN,h:_iH,i:_iw,j:_iN,k:_is,l:_iq,m:_iu,n:_iJ,o:_iy,p:_iP,q:_hH,r:_hE,s:_hK},_iS=function(_iT,_iU){return (E(_iT)!=E(_iU))?true:false;},_iV=function(_iW,_iX){return E(_iW)==E(_iX);},_iY=new T2(0,_iV,_iS),_iZ=function(_j0,_j1){return E(_j0)<E(_j1);},_j2=function(_j3,_j4){return E(_j3)<=E(_j4);},_j5=function(_j6,_j7){return E(_j6)>E(_j7);},_j8=function(_j9,_ja){return E(_j9)>=E(_ja);},_jb=function(_jc,_jd){var _je=E(_jc),_jf=E(_jd);return (_je>=_jf)?(_je!=_jf)?2:1:0;},_jg=function(_jh,_ji){var _jj=E(_jh),_jk=E(_ji);return (_jj>_jk)?E(_jj):E(_jk);},_jl=function(_jm,_jn){var _jo=E(_jm),_jp=E(_jn);return (_jo>_jp)?E(_jp):E(_jo);},_jq={_:0,a:_iY,b:_jb,c:_iZ,d:_j2,e:_j5,f:_j8,g:_jg,h:_jl},_jr="dz",_js="wy",_jt="wx",_ju="dy",_jv="dx",_jw="t",_jx="a",_jy="r",_jz="ly",_jA="lx",_jB="wz",_jC=0,_jD=function(_jE){var _jF=__new(),_jG=_jF,_jH=function(_jI,_){while(1){var _jJ=E(_jI);if(!_jJ._){return _jC;}else{var _jK=E(_jJ.a),_jL=__set(_jG,E(_jK.a),E(_jK.b));_jI=_jJ.b;continue;}}},_jM=B(_jH(_jE,_));return E(_jG);},_jN=function(_jO,_jP,_jQ,_jR,_jS,_jT,_jU,_jV,_jW){return new F(function(){return _jD(new T2(1,new T2(0,_jt,_jO),new T2(1,new T2(0,_js,_jP),new T2(1,new T2(0,_jB,_jQ),new T2(1,new T2(0,_jA,_jR*_jS*Math.cos(_jT)),new T2(1,new T2(0,_jz,_jR*_jS*Math.sin(_jT)),new T2(1,new T2(0,_jy,_jR),new T2(1,new T2(0,_jx,_jS),new T2(1,new T2(0,_jw,_jT),new T2(1,new T2(0,_jv,_jU),new T2(1,new T2(0,_ju,_jV),new T2(1,new T2(0,_jr,_jW),_o))))))))))));});},_jX=function(_jY){var _jZ=E(_jY),_k0=E(_jZ.a),_k1=E(_jZ.b),_k2=E(_jZ.d);return new F(function(){return _jN(_k0.a,_k0.b,_k0.c,E(_k1.a),E(_k1.b),E(_jZ.c),_k2.a,_k2.b,_k2.c);});},_k3=function(_k4,_k5){var _k6=E(_k5);return (_k6._==0)?__Z:new T2(1,new T(function(){return B(A1(_k4,_k6.a));}),new T(function(){return B(_k3(_k4,_k6.b));}));},_k7=function(_k8,_k9,_ka){var _kb=__lst2arr(B(_k3(_jX,new T2(1,_k8,new T2(1,_k9,new T2(1,_ka,_o))))));return E(_kb);},_kc=function(_kd){var _ke=E(_kd);return new F(function(){return _k7(_ke.a,_ke.b,_ke.c);});},_kf=new T2(0,_iR,_jq),_kg=function(_kh,_ki,_kj,_kk,_kl,_km,_kn){var _ko=B(_7i(B(_7g(_kh)))),_kp=new T(function(){return B(A3(_6I,_ko,new T(function(){return B(A3(_7k,_ko,_ki,_kl));}),new T(function(){return B(A3(_7k,_ko,_kj,_km));})));});return new F(function(){return A3(_6I,_ko,_kp,new T(function(){return B(A3(_7k,_ko,_kk,_kn));}));});},_kq=function(_kr,_ks,_kt,_ku){var _kv=B(_7g(_kr)),_kw=new T(function(){return B(A2(_7w,_kr,new T(function(){return B(_kg(_kr,_ks,_kt,_ku,_ks,_kt,_ku));})));});return new T3(0,B(A3(_9b,_kv,_ks,_kw)),B(A3(_9b,_kv,_kt,_kw)),B(A3(_9b,_kv,_ku,_kw)));},_kx=function(_ky,_kz,_kA,_kB,_kC,_kD,_kE){var _kF=B(_7k(_ky));return new T3(0,B(A1(B(A1(_kF,_kz)),_kC)),B(A1(B(A1(_kF,_kA)),_kD)),B(A1(B(A1(_kF,_kB)),_kE)));},_kG=function(_kH,_kI,_kJ,_kK,_kL,_kM,_kN){var _kO=B(_6I(_kH));return new T3(0,B(A1(B(A1(_kO,_kI)),_kL)),B(A1(B(A1(_kO,_kJ)),_kM)),B(A1(B(A1(_kO,_kK)),_kN)));},_kP=function(_kQ,_kR){var _kS=new T(function(){return E(E(_kQ).a);}),_kT=new T(function(){return B(A2(_gS,new T2(0,_kS,new T(function(){return E(E(_kQ).b);})),_kR));}),_kU=new T(function(){var _kV=E(_kT),_kW=B(_kq(_kS,_kV.a,_kV.b,_kV.c));return new T3(0,E(_kW.a),E(_kW.b),E(_kW.c));}),_kX=new T(function(){var _kY=E(_kR),_kZ=_kY.a,_l0=_kY.b,_l1=_kY.c,_l2=E(_kU),_l3=B(_7g(_kS)),_l4=new T(function(){return B(A2(_7w,_kS,new T(function(){var _l5=E(_kT),_l6=_l5.a,_l7=_l5.b,_l8=_l5.c;return B(_kg(_kS,_l6,_l7,_l8,_l6,_l7,_l8));})));}),_l9=B(A3(_9b,_l3,new T(function(){return B(_7y(_kS,_kZ,_l0,_l1));}),_l4)),_la=B(_7i(_l3)),_lb=B(_kx(_la,_l2.a,_l2.b,_l2.c,_l9,_l9,_l9)),_lc=B(_6K(_la)),_ld=B(_kG(_la,_kZ,_l0,_l1,B(A1(_lc,_lb.a)),B(A1(_lc,_lb.b)),B(A1(_lc,_lb.c))));return new T3(0,E(_ld.a),E(_ld.b),E(_ld.c));});return new T2(0,_kX,_kU);},_le=function(_lf){return E(E(_lf).a);},_lg=function(_lh,_li,_lj,_lk,_ll,_lm,_ln){var _lo=B(_kg(_lh,_ll,_lm,_ln,_li,_lj,_lk)),_lp=B(_7i(B(_7g(_lh)))),_lq=B(_kx(_lp,_ll,_lm,_ln,_lo,_lo,_lo)),_lr=B(_6K(_lp));return new F(function(){return _kG(_lp,_li,_lj,_lk,B(A1(_lr,_lq.a)),B(A1(_lr,_lq.b)),B(A1(_lr,_lq.c)));});},_ls=function(_lt){return E(E(_lt).a);},_lu=function(_lv,_lw,_lx,_ly){var _lz=new T(function(){var _lA=E(_ly),_lB=E(_lx),_lC=B(_lg(_lv,_lA.a,_lA.b,_lA.c,_lB.a,_lB.b,_lB.c));return new T3(0,E(_lC.a),E(_lC.b),E(_lC.c));}),_lD=new T(function(){return B(A2(_7w,_lv,new T(function(){var _lE=E(_lz),_lF=_lE.a,_lG=_lE.b,_lH=_lE.c;return B(_kg(_lv,_lF,_lG,_lH,_lF,_lG,_lH));})));});if(!B(A3(_ls,B(_le(_lw)),_lD,new T(function(){return B(A2(_91,B(_7i(B(_7g(_lv)))),_90));})))){var _lI=E(_lz),_lJ=B(_kq(_lv,_lI.a,_lI.b,_lI.c)),_lK=B(A2(_7w,_lv,new T(function(){var _lL=E(_ly),_lM=_lL.a,_lN=_lL.b,_lO=_lL.c;return B(_kg(_lv,_lM,_lN,_lO,_lM,_lN,_lO));}))),_lP=B(_7k(new T(function(){return B(_7i(new T(function(){return B(_7g(_lv));})));})));return new T3(0,B(A1(B(A1(_lP,_lJ.a)),_lK)),B(A1(B(A1(_lP,_lJ.b)),_lK)),B(A1(B(A1(_lP,_lJ.c)),_lK)));}else{var _lQ=B(A2(_91,B(_7i(B(_7g(_lv)))),_90));return new T3(0,_lQ,_lQ,_lQ);}},_lR=new T(function(){var _lS=eval("angleCount"),_lT=Number(_lS);return jsTrunc(_lT);}),_lU=new T(function(){return E(_lR);}),_lV=new T(function(){return B(unCStr(": empty list"));}),_lW=new T(function(){return B(unCStr("Prelude."));}),_lX=function(_lY){return new F(function(){return err(B(_f(_lW,new T(function(){return B(_f(_lY,_lV));},1))));});},_lZ=new T(function(){return B(unCStr("head"));}),_m0=new T(function(){return B(_lX(_lZ));}),_m1=function(_m2,_m3,_m4){var _m5=E(_m2);if(!_m5._){return __Z;}else{var _m6=E(_m3);if(!_m6._){return __Z;}else{var _m7=_m6.a,_m8=E(_m4);if(!_m8._){return __Z;}else{var _m9=E(_m8.a),_ma=_m9.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_m5.a),E(_m7),E(_ma));}),new T2(1,new T(function(){return new T3(0,E(_m7),E(_ma),E(_m9.b));}),_o)),new T(function(){return B(_m1(_m5.b,_m6.b,_m8.b));},1));});}}}},_mb=new T(function(){return B(unCStr("tail"));}),_mc=new T(function(){return B(_lX(_mb));}),_md=function(_me,_mf){var _mg=E(_me);if(!_mg._){return __Z;}else{var _mh=E(_mf);return (_mh._==0)?__Z:new T2(1,new T2(0,_mg.a,_mh.a),new T(function(){return B(_md(_mg.b,_mh.b));}));}},_mi=function(_mj,_mk){var _ml=E(_mj);if(!_ml._){return __Z;}else{var _mm=E(_mk);if(!_mm._){return __Z;}else{var _mn=E(_ml.a),_mo=_mn.b,_mp=E(_mm.a).b,_mq=new T(function(){var _mr=new T(function(){return B(_md(_mp,new T(function(){var _ms=E(_mp);if(!_ms._){return E(_mc);}else{return E(_ms.b);}},1)));},1);return B(_m1(_mo,new T(function(){var _mt=E(_mo);if(!_mt._){return E(_mc);}else{return E(_mt.b);}},1),_mr));});return new F(function(){return _f(new T2(1,new T(function(){var _mu=E(_mo);if(!_mu._){return E(_m0);}else{var _mv=E(_mp);if(!_mv._){return E(_m0);}else{return new T3(0,E(_mn.a),E(_mu.a),E(_mv.a));}}}),_mq),new T(function(){return B(_mi(_ml.b,_mm.b));},1));});}}},_mw=new T(function(){return E(_lU)-1;}),_mx=new T1(0,1),_my=function(_mz,_mA){var _mB=E(_mA),_mC=new T(function(){var _mD=B(_7i(_mz)),_mE=B(_my(_mz,B(A3(_6I,_mD,_mB,new T(function(){return B(A2(_91,_mD,_mx));})))));return new T2(1,_mE.a,_mE.b);});return new T2(0,_mB,_mC);},_mF=function(_mG){return E(E(_mG).d);},_mH=new T1(0,2),_mI=function(_mJ,_mK){var _mL=E(_mK);if(!_mL._){return __Z;}else{var _mM=_mL.a;return (!B(A1(_mJ,_mM)))?__Z:new T2(1,_mM,new T(function(){return B(_mI(_mJ,_mL.b));}));}},_mN=function(_mO,_mP,_mQ,_mR){var _mS=B(_my(_mP,_mQ)),_mT=new T(function(){var _mU=B(_7i(_mP)),_mV=new T(function(){return B(A3(_9b,_mP,new T(function(){return B(A2(_91,_mU,_mx));}),new T(function(){return B(A2(_91,_mU,_mH));})));});return B(A3(_6I,_mU,_mR,_mV));});return new F(function(){return _mI(function(_mW){return new F(function(){return A3(_mF,_mO,_mW,_mT);});},new T2(1,_mS.a,_mS.b));});},_mX=new T(function(){return B(_mN(_jq,_ip,_hm,_mw));}),_mY=function(_mZ,_n0){while(1){var _n1=E(_mZ);if(!_n1._){return E(_n0);}else{_mZ=_n1.b;_n0=_n1.a;continue;}}},_n2=new T(function(){return B(unCStr("last"));}),_n3=new T(function(){return B(_lX(_n2));}),_n4=function(_n5){return new F(function(){return _mY(_n5,_n3);});},_n6=function(_n7){return new F(function(){return _n4(E(_n7).b);});},_n8=new T(function(){var _n9=eval("proceedCount"),_na=Number(_n9);return jsTrunc(_na);}),_nb=new T(function(){return E(_n8);}),_nc=1,_nd=new T(function(){return B(_mN(_jq,_ip,_nc,_nb));}),_ne=function(_nf,_ng,_nh,_ni,_nj,_nk,_nl,_nm,_nn,_no,_np,_nq,_nr,_ns){var _nt=new T(function(){var _nu=new T(function(){var _nv=E(_no),_nw=E(_ns),_nx=E(_nr),_ny=E(_np),_nz=E(_nq),_nA=E(_nn);return new T3(0,_nv*_nw-_nx*_ny,_ny*_nz-_nw*_nA,_nA*_nx-_nz*_nv);}),_nB=function(_nC){var _nD=new T(function(){var _nE=E(_nC)/E(_lU);return (_nE+_nE)*3.141592653589793;}),_nF=new T(function(){return B(A1(_nf,_nD));}),_nG=new T(function(){var _nH=new T(function(){var _nI=E(_nF)/E(_nb);return new T3(0,E(_nI),E(_nI),E(_nI));}),_nJ=function(_nK,_nL){var _nM=E(_nK);if(!_nM._){return new T2(0,_o,_nL);}else{var _nN=new T(function(){var _nO=B(_kP(_kf,new T(function(){var _nP=E(_nL),_nQ=E(_nP.a),_nR=E(_nP.b),_nS=E(_nH);return new T3(0,E(_nQ.a)+E(_nR.a)*E(_nS.a),E(_nQ.b)+E(_nR.b)*E(_nS.b),E(_nQ.c)+E(_nR.c)*E(_nS.c));}))),_nT=_nO.a,_nU=new T(function(){var _nV=E(_nO.b),_nW=E(E(_nL).b),_nX=B(_lg(_iR,_nW.a,_nW.b,_nW.c,_nV.a,_nV.b,_nV.c)),_nY=B(_kq(_iR,_nX.a,_nX.b,_nX.c));return new T3(0,E(_nY.a),E(_nY.b),E(_nY.c));});return new T2(0,new T(function(){var _nZ=E(_nF),_o0=E(_nD);return new T4(0,E(_nT),E(new T2(0,E(_nM.a)/E(_nb),E(_nZ))),E(_o0),E(_nU));}),new T2(0,_nT,_nU));}),_o1=new T(function(){var _o2=B(_nJ(_nM.b,new T(function(){return E(E(_nN).b);})));return new T2(0,_o2.a,_o2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nN).a);}),new T(function(){return E(E(_o1).a);})),new T(function(){return E(E(_o1).b);}));}},_o3=function(_o4,_o5,_o6,_o7,_o8){var _o9=E(_o4);if(!_o9._){return new T2(0,_o,new T2(0,new T3(0,E(_o5),E(_o6),E(_o7)),_o8));}else{var _oa=new T(function(){var _ob=B(_kP(_kf,new T(function(){var _oc=E(_o8),_od=E(_nH);return new T3(0,E(_o5)+E(_oc.a)*E(_od.a),E(_o6)+E(_oc.b)*E(_od.b),E(_o7)+E(_oc.c)*E(_od.c));}))),_oe=_ob.a,_of=new T(function(){var _og=E(_ob.b),_oh=E(_o8),_oi=B(_lg(_iR,_oh.a,_oh.b,_oh.c,_og.a,_og.b,_og.c)),_oj=B(_kq(_iR,_oi.a,_oi.b,_oi.c));return new T3(0,E(_oj.a),E(_oj.b),E(_oj.c));});return new T2(0,new T(function(){var _ok=E(_nF),_ol=E(_nD);return new T4(0,E(_oe),E(new T2(0,E(_o9.a)/E(_nb),E(_ok))),E(_ol),E(_of));}),new T2(0,_oe,_of));}),_om=new T(function(){var _on=B(_nJ(_o9.b,new T(function(){return E(E(_oa).b);})));return new T2(0,_on.a,_on.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oa).a);}),new T(function(){return E(E(_om).a);})),new T(function(){return E(E(_om).b);}));}};return E(B(_o3(_nd,_ni,_nj,_nk,new T(function(){var _oo=E(_nu),_op=E(_nD)+_nl,_oq=Math.cos(_op),_or=Math.sin(_op);return new T3(0,E(_nn)*_oq+E(_oo.a)*_or,E(_no)*_oq+E(_oo.b)*_or,E(_np)*_oq+E(_oo.c)*_or);}))).a);});return new T2(0,new T(function(){var _os=E(_nF),_ot=E(_nD);return new T4(0,E(new T3(0,E(_ni),E(_nj),E(_nk))),E(new T2(0,E(_hm),E(_os))),E(_ot),E(_hn));}),_nG);};return B(_k3(_nB,_mX));}),_ou=new T(function(){var _ov=new T(function(){var _ow=B(_f(_nt,new T2(1,new T(function(){var _ox=E(_nt);if(!_ox._){return E(_m0);}else{return E(_ox.a);}}),_o)));if(!_ow._){return E(_mc);}else{return E(_ow.b);}},1);return B(_mi(_nt,_ov));});return new T2(0,_ou,new T(function(){return B(_k3(_n6,_nt));}));},_oy=function(_oz,_oA,_oB,_oC,_oD,_oE,_oF,_oG,_oH,_oI,_oJ,_oK,_oL,_oM,_oN,_oO,_oP){var _oQ=B(_kP(_kf,new T3(0,E(_oC),E(_oD),E(_oE)))),_oR=_oQ.b,_oS=E(_oQ.a),_oT=B(_lu(_iR,_jq,_oR,new T3(0,E(_oG),E(_oH),E(_oI)))),_oU=E(_oR),_oV=_oU.a,_oW=_oU.b,_oX=_oU.c,_oY=B(_lg(_iR,_oK,_oL,_oM,_oV,_oW,_oX)),_oZ=B(_kq(_iR,_oY.a,_oY.b,_oY.c)),_p0=_oZ.a,_p1=_oZ.b,_p2=_oZ.c,_p3=E(_oF),_p4=new T2(0,E(new T3(0,E(_oT.a),E(_oT.b),E(_oT.c))),E(_oJ)),_p5=B(_ne(_oz,_oA,_oB,_oS.a,_oS.b,_oS.c,_p3,_p4,_p0,_p1,_p2,_oV,_oW,_oX)),_p6=__lst2arr(B(_k3(_kc,_p5.a))),_p7=__lst2arr(B(_k3(_jX,_p5.b)));return {_:0,a:_oz,b:_oA,c:_oB,d:new T2(0,E(_oS),E(_p3)),e:_p4,f:new T3(0,E(_p0),E(_p1),E(_p2)),g:_oU,h:_p6,i:_p7};},_p8=new T(function(){return 6.283185307179586/E(_lU);}),_p9=-0.4,_pa=new T3(0,E(_hm),E(_p9),E(_hm)),_pb=function(_){return new F(function(){return __jsNull();});},_pc=function(_pd){var _pe=B(A1(_pd,_));return E(_pe);},_pf=new T(function(){return B(_pc(_pb));}),_pg=function(_ph,_pi,_pj,_pk,_pl,_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt){var _pu=function(_pv){var _pw=E(_p8),_px=2+_pv|0,_py=_px-1|0,_pz=(2+_pv)*(1+_pv),_pA=E(_mX);if(!_pA._){return _pw*0;}else{var _pB=_pA.a,_pC=_pA.b,_pD=B(A1(_ph,new T(function(){return 6.283185307179586*E(_pB)/E(_lU);}))),_pE=B(A1(_ph,new T(function(){return 6.283185307179586*(E(_pB)+1)/E(_lU);})));if(_pD!=_pE){if(_px>=0){var _pF=E(_px);if(!_pF){var _pG=function(_pH,_pI){while(1){var _pJ=B((function(_pK,_pL){var _pM=E(_pK);if(!_pM._){return E(_pL);}else{var _pN=_pM.a,_pO=_pM.b,_pP=B(A1(_ph,new T(function(){return 6.283185307179586*E(_pN)/E(_lU);}))),_pQ=B(A1(_ph,new T(function(){return 6.283185307179586*(E(_pN)+1)/E(_lU);})));if(_pP!=_pQ){var _pR=_pL+0/(_pP-_pQ)/_pz;_pH=_pO;_pI=_pR;return __continue;}else{if(_py>=0){var _pS=E(_py);if(!_pS){var _pR=_pL+_px/_pz;_pH=_pO;_pI=_pR;return __continue;}else{var _pR=_pL+_px*B(_hy(_pP,_pS))/_pz;_pH=_pO;_pI=_pR;return __continue;}}else{return E(_hp);}}}})(_pH,_pI));if(_pJ!=__continue){return _pJ;}}};return _pw*B(_pG(_pC,0/(_pD-_pE)/_pz));}else{var _pT=function(_pU,_pV){while(1){var _pW=B((function(_pX,_pY){var _pZ=E(_pX);if(!_pZ._){return E(_pY);}else{var _q0=_pZ.a,_q1=_pZ.b,_q2=B(A1(_ph,new T(function(){return 6.283185307179586*E(_q0)/E(_lU);}))),_q3=B(A1(_ph,new T(function(){return 6.283185307179586*(E(_q0)+1)/E(_lU);})));if(_q2!=_q3){if(_pF>=0){var _q4=_pY+(B(_hy(_q2,_pF))-B(_hy(_q3,_pF)))/(_q2-_q3)/_pz;_pU=_q1;_pV=_q4;return __continue;}else{return E(_hp);}}else{if(_py>=0){var _q5=E(_py);if(!_q5){var _q4=_pY+_px/_pz;_pU=_q1;_pV=_q4;return __continue;}else{var _q4=_pY+_px*B(_hy(_q2,_q5))/_pz;_pU=_q1;_pV=_q4;return __continue;}}else{return E(_hp);}}}})(_pU,_pV));if(_pW!=__continue){return _pW;}}};return _pw*B(_pT(_pC,(B(_hy(_pD,_pF))-B(_hy(_pE,_pF)))/(_pD-_pE)/_pz));}}else{return E(_hp);}}else{if(_py>=0){var _q6=E(_py);if(!_q6){var _q7=function(_q8,_q9){while(1){var _qa=B((function(_qb,_qc){var _qd=E(_qb);if(!_qd._){return E(_qc);}else{var _qe=_qd.a,_qf=_qd.b,_qg=B(A1(_ph,new T(function(){return 6.283185307179586*E(_qe)/E(_lU);}))),_qh=B(A1(_ph,new T(function(){return 6.283185307179586*(E(_qe)+1)/E(_lU);})));if(_qg!=_qh){if(_px>=0){var _qi=E(_px);if(!_qi){var _qj=_qc+0/(_qg-_qh)/_pz;_q8=_qf;_q9=_qj;return __continue;}else{var _qj=_qc+(B(_hy(_qg,_qi))-B(_hy(_qh,_qi)))/(_qg-_qh)/_pz;_q8=_qf;_q9=_qj;return __continue;}}else{return E(_hp);}}else{var _qj=_qc+_px/_pz;_q8=_qf;_q9=_qj;return __continue;}}})(_q8,_q9));if(_qa!=__continue){return _qa;}}};return _pw*B(_q7(_pC,_px/_pz));}else{var _qk=function(_ql,_qm){while(1){var _qn=B((function(_qo,_qp){var _qq=E(_qo);if(!_qq._){return E(_qp);}else{var _qr=_qq.a,_qs=_qq.b,_qt=B(A1(_ph,new T(function(){return 6.283185307179586*E(_qr)/E(_lU);}))),_qu=B(A1(_ph,new T(function(){return 6.283185307179586*(E(_qr)+1)/E(_lU);})));if(_qt!=_qu){if(_px>=0){var _qv=E(_px);if(!_qv){var _qw=_qp+0/(_qt-_qu)/_pz;_ql=_qs;_qm=_qw;return __continue;}else{var _qw=_qp+(B(_hy(_qt,_qv))-B(_hy(_qu,_qv)))/(_qt-_qu)/_pz;_ql=_qs;_qm=_qw;return __continue;}}else{return E(_hp);}}else{if(_q6>=0){var _qw=_qp+_px*B(_hy(_qt,_q6))/_pz;_ql=_qs;_qm=_qw;return __continue;}else{return E(_hp);}}}})(_ql,_qm));if(_qn!=__continue){return _qn;}}};return _pw*B(_qk(_pC,_px*B(_hy(_pD,_q6))/_pz));}}else{return E(_hp);}}}},_qx=E(_pf),_qy=1/(B(_pu(1))*_pi);return new F(function(){return _oy(_ph,_pa,new T2(0,E(new T3(0,E(_qy),E(_qy),E(_qy))),1/(B(_pu(3))*_pi)),_pj,_pk,_pl,_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt,_hn,_qx,_qx);});},_qz=0,_qA=-2,_qB=-0.2,_qC=0.2,_qD=0.4,_qE=function(_qF){return E(_qD);},_qG=1,_qH=new T(function(){var _qI=B(_pg(_qE,1.2,_qC,_qB,_qC,_qz,_qz,_qz,_qz,_qA,_qz,_qz,_qG));return {_:0,a:E(_qI.a),b:E(_qI.b),c:E(_qI.c),d:E(_qI.d),e:E(_qI.e),f:E(_qI.f),g:E(_qI.g),h:_qI.h,i:_qI.i};}),_qJ=0,_qK=-0.1,_qL=1.3,_qM=function(_qN){var _qO=I_decodeDouble(_qN);return new T2(0,new T1(1,_qO.b),_qO.a);},_qP=function(_qQ){return new T1(0,_qQ);},_qR=function(_qS){var _qT=hs_intToInt64(2147483647),_qU=hs_leInt64(_qS,_qT);if(!_qU){return new T1(1,I_fromInt64(_qS));}else{var _qV=hs_intToInt64(-2147483648),_qW=hs_geInt64(_qS,_qV);if(!_qW){return new T1(1,I_fromInt64(_qS));}else{var _qX=hs_int64ToInt(_qS);return new F(function(){return _qP(_qX);});}}},_qY=new T(function(){var _qZ=newByteArr(256),_r0=_qZ,_=_r0["v"]["i8"][0]=8,_r1=function(_r2,_r3,_r4,_){while(1){if(_r4>=256){if(_r2>=256){return E(_);}else{var _r5=imul(2,_r2)|0,_r6=_r3+1|0,_r7=_r2;_r2=_r5;_r3=_r6;_r4=_r7;continue;}}else{var _=_r0["v"]["i8"][_r4]=_r3,_r7=_r4+_r2|0;_r4=_r7;continue;}}},_=B(_r1(2,0,1,_));return _r0;}),_r8=function(_r9,_ra){var _rb=hs_int64ToInt(_r9),_rc=E(_qY),_rd=_rc["v"]["i8"][(255&_rb>>>0)>>>0&4294967295];if(_ra>_rd){if(_rd>=8){var _re=hs_uncheckedIShiftRA64(_r9,8),_rf=function(_rg,_rh){while(1){var _ri=B((function(_rj,_rk){var _rl=hs_int64ToInt(_rj),_rm=_rc["v"]["i8"][(255&_rl>>>0)>>>0&4294967295];if(_rk>_rm){if(_rm>=8){var _rn=hs_uncheckedIShiftRA64(_rj,8),_ro=_rk-8|0;_rg=_rn;_rh=_ro;return __continue;}else{return new T2(0,new T(function(){var _rp=hs_uncheckedIShiftRA64(_rj,_rm);return B(_qR(_rp));}),_rk-_rm|0);}}else{return new T2(0,new T(function(){var _rq=hs_uncheckedIShiftRA64(_rj,_rk);return B(_qR(_rq));}),0);}})(_rg,_rh));if(_ri!=__continue){return _ri;}}};return new F(function(){return _rf(_re,_ra-8|0);});}else{return new T2(0,new T(function(){var _rr=hs_uncheckedIShiftRA64(_r9,_rd);return B(_qR(_rr));}),_ra-_rd|0);}}else{return new T2(0,new T(function(){var _rs=hs_uncheckedIShiftRA64(_r9,_ra);return B(_qR(_rs));}),0);}},_rt=function(_ru){var _rv=hs_intToInt64(_ru);return E(_rv);},_rw=function(_rx){var _ry=E(_rx);if(!_ry._){return new F(function(){return _rt(_ry.a);});}else{return new F(function(){return I_toInt64(_ry.a);});}},_rz=function(_rA){return I_toInt(_rA)>>>0;},_rB=function(_rC){var _rD=E(_rC);if(!_rD._){return _rD.a>>>0;}else{return new F(function(){return _rz(_rD.a);});}},_rE=function(_rF){var _rG=B(_qM(_rF)),_rH=_rG.a,_rI=_rG.b;if(_rI<0){var _rJ=function(_rK){if(!_rK){return new T2(0,E(_rH),B(_3u(_1M, -_rI)));}else{var _rL=B(_r8(B(_rw(_rH)), -_rI));return new T2(0,E(_rL.a),B(_3u(_1M,_rL.b)));}};if(!((B(_rB(_rH))&1)>>>0)){return new F(function(){return _rJ(1);});}else{return new F(function(){return _rJ(0);});}}else{return new T2(0,B(_3u(_rH,_rI)),_1M);}},_rM=function(_rN){var _rO=B(_rE(E(_rN)));return new T2(0,E(_rO.a),E(_rO.b));},_rP=new T3(0,_il,_jq,_rM),_rQ=function(_rR){return E(E(_rR).a);},_rS=function(_rT){return E(E(_rT).a);},_rU=function(_rV,_rW){if(_rV<=_rW){var _rX=function(_rY){return new T2(1,_rY,new T(function(){if(_rY!=_rW){return B(_rX(_rY+1|0));}else{return __Z;}}));};return new F(function(){return _rX(_rV);});}else{return __Z;}},_rZ=function(_s0){return new F(function(){return _rU(E(_s0),2147483647);});},_s1=function(_s2,_s3,_s4){if(_s4<=_s3){var _s5=new T(function(){var _s6=_s3-_s2|0,_s7=function(_s8){return (_s8>=(_s4-_s6|0))?new T2(1,_s8,new T(function(){return B(_s7(_s8+_s6|0));})):new T2(1,_s8,_o);};return B(_s7(_s3));});return new T2(1,_s2,_s5);}else{return (_s4<=_s2)?new T2(1,_s2,_o):__Z;}},_s9=function(_sa,_sb,_sc){if(_sc>=_sb){var _sd=new T(function(){var _se=_sb-_sa|0,_sf=function(_sg){return (_sg<=(_sc-_se|0))?new T2(1,_sg,new T(function(){return B(_sf(_sg+_se|0));})):new T2(1,_sg,_o);};return B(_sf(_sb));});return new T2(1,_sa,_sd);}else{return (_sc>=_sa)?new T2(1,_sa,_o):__Z;}},_sh=function(_si,_sj){if(_sj<_si){return new F(function(){return _s1(_si,_sj,-2147483648);});}else{return new F(function(){return _s9(_si,_sj,2147483647);});}},_sk=function(_sl,_sm){return new F(function(){return _sh(E(_sl),E(_sm));});},_sn=function(_so,_sp,_sq){if(_sp<_so){return new F(function(){return _s1(_so,_sp,_sq);});}else{return new F(function(){return _s9(_so,_sp,_sq);});}},_sr=function(_ss,_st,_su){return new F(function(){return _sn(E(_ss),E(_st),E(_su));});},_sv=function(_sw,_sx){return new F(function(){return _rU(E(_sw),E(_sx));});},_sy=function(_sz){return E(_sz);},_sA=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_sB=new T(function(){return B(err(_sA));}),_sC=function(_sD){var _sE=E(_sD);return (_sE==(-2147483648))?E(_sB):_sE-1|0;},_sF=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_sG=new T(function(){return B(err(_sF));}),_sH=function(_sI){var _sJ=E(_sI);return (_sJ==2147483647)?E(_sG):_sJ+1|0;},_sK={_:0,a:_sH,b:_sC,c:_sy,d:_sy,e:_rZ,f:_sk,g:_sv,h:_sr},_sL=function(_sM,_sN){if(_sM<=0){if(_sM>=0){return new F(function(){return quot(_sM,_sN);});}else{if(_sN<=0){return new F(function(){return quot(_sM,_sN);});}else{return quot(_sM+1|0,_sN)-1|0;}}}else{if(_sN>=0){if(_sM>=0){return new F(function(){return quot(_sM,_sN);});}else{if(_sN<=0){return new F(function(){return quot(_sM,_sN);});}else{return quot(_sM+1|0,_sN)-1|0;}}}else{return quot(_sM-1|0,_sN)-1|0;}}},_sO=0,_sP=new T(function(){return B(_2R(_sO));}),_sQ=new T(function(){return die(_sP);}),_sR=function(_sS,_sT){var _sU=E(_sT);switch(_sU){case -1:var _sV=E(_sS);if(_sV==(-2147483648)){return E(_sQ);}else{return new F(function(){return _sL(_sV,-1);});}break;case 0:return E(_2V);default:return new F(function(){return _sL(_sS,_sU);});}},_sW=function(_sX,_sY){return new F(function(){return _sR(E(_sX),E(_sY));});},_sZ=0,_t0=new T2(0,_sQ,_sZ),_t1=function(_t2,_t3){var _t4=E(_t2),_t5=E(_t3);switch(_t5){case -1:var _t6=E(_t4);if(_t6==(-2147483648)){return E(_t0);}else{if(_t6<=0){if(_t6>=0){var _t7=quotRemI(_t6,-1);return new T2(0,_t7.a,_t7.b);}else{var _t8=quotRemI(_t6,-1);return new T2(0,_t8.a,_t8.b);}}else{var _t9=quotRemI(_t6-1|0,-1);return new T2(0,_t9.a-1|0,(_t9.b+(-1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_t4<=0){if(_t4>=0){var _ta=quotRemI(_t4,_t5);return new T2(0,_ta.a,_ta.b);}else{if(_t5<=0){var _tb=quotRemI(_t4,_t5);return new T2(0,_tb.a,_tb.b);}else{var _tc=quotRemI(_t4+1|0,_t5);return new T2(0,_tc.a-1|0,(_tc.b+_t5|0)-1|0);}}}else{if(_t5>=0){if(_t4>=0){var _td=quotRemI(_t4,_t5);return new T2(0,_td.a,_td.b);}else{if(_t5<=0){var _te=quotRemI(_t4,_t5);return new T2(0,_te.a,_te.b);}else{var _tf=quotRemI(_t4+1|0,_t5);return new T2(0,_tf.a-1|0,(_tf.b+_t5|0)-1|0);}}}else{var _tg=quotRemI(_t4-1|0,_t5);return new T2(0,_tg.a-1|0,(_tg.b+_t5|0)+1|0);}}}},_th=function(_ti,_tj){var _tk=_ti%_tj;if(_ti<=0){if(_ti>=0){return E(_tk);}else{if(_tj<=0){return E(_tk);}else{var _tl=E(_tk);return (_tl==0)?0:_tl+_tj|0;}}}else{if(_tj>=0){if(_ti>=0){return E(_tk);}else{if(_tj<=0){return E(_tk);}else{var _tm=E(_tk);return (_tm==0)?0:_tm+_tj|0;}}}else{var _tn=E(_tk);return (_tn==0)?0:_tn+_tj|0;}}},_to=function(_tp,_tq){var _tr=E(_tq);switch(_tr){case -1:return E(_sZ);case 0:return E(_2V);default:return new F(function(){return _th(E(_tp),_tr);});}},_ts=function(_tt,_tu){var _tv=E(_tt),_tw=E(_tu);switch(_tw){case -1:var _tx=E(_tv);if(_tx==(-2147483648)){return E(_sQ);}else{return new F(function(){return quot(_tx,-1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_tv,_tw);});}},_ty=function(_tz,_tA){var _tB=E(_tz),_tC=E(_tA);switch(_tC){case -1:var _tD=E(_tB);if(_tD==(-2147483648)){return E(_t0);}else{var _tE=quotRemI(_tD,-1);return new T2(0,_tE.a,_tE.b);}break;case 0:return E(_2V);default:var _tF=quotRemI(_tB,_tC);return new T2(0,_tF.a,_tF.b);}},_tG=function(_tH,_tI){var _tJ=E(_tI);switch(_tJ){case -1:return E(_sZ);case 0:return E(_2V);default:return E(_tH)%_tJ;}},_tK=function(_tL){return new F(function(){return _qP(E(_tL));});},_tM=function(_tN){return new T2(0,E(B(_qP(E(_tN)))),E(_mx));},_tO=function(_tP,_tQ){return imul(E(_tP),E(_tQ))|0;},_tR=function(_tS,_tT){return E(_tS)+E(_tT)|0;},_tU=function(_tV,_tW){return E(_tV)-E(_tW)|0;},_tX=function(_tY){var _tZ=E(_tY);return (_tZ<0)? -_tZ:E(_tZ);},_u0=function(_u1){return new F(function(){return _38(_u1);});},_u2=function(_u3){return  -E(_u3);},_u4=-1,_u5=0,_u6=1,_u7=function(_u8){var _u9=E(_u8);return (_u9>=0)?(E(_u9)==0)?E(_u5):E(_u6):E(_u4);},_ua={_:0,a:_tR,b:_tU,c:_tO,d:_u2,e:_tX,f:_u7,g:_u0},_ub=function(_uc,_ud){return E(_uc)==E(_ud);},_ue=function(_uf,_ug){return E(_uf)!=E(_ug);},_uh=new T2(0,_ub,_ue),_ui=function(_uj,_uk){var _ul=E(_uj),_um=E(_uk);return (_ul>_um)?E(_ul):E(_um);},_un=function(_uo,_up){var _uq=E(_uo),_ur=E(_up);return (_uq>_ur)?E(_ur):E(_uq);},_us=function(_ut,_uu){return (_ut>=_uu)?(_ut!=_uu)?2:1:0;},_uv=function(_uw,_ux){return new F(function(){return _us(E(_uw),E(_ux));});},_uy=function(_uz,_uA){return E(_uz)>=E(_uA);},_uB=function(_uC,_uD){return E(_uC)>E(_uD);},_uE=function(_uF,_uG){return E(_uF)<=E(_uG);},_uH=function(_uI,_uJ){return E(_uI)<E(_uJ);},_uK={_:0,a:_uh,b:_uv,c:_uH,d:_uE,e:_uB,f:_uy,g:_ui,h:_un},_uL=new T3(0,_ua,_uK,_tM),_uM={_:0,a:_uL,b:_sK,c:_ts,d:_tG,e:_sW,f:_to,g:_ty,h:_t1,i:_tK},_uN=new T1(0,2),_uO=function(_uP,_uQ){while(1){var _uR=E(_uP);if(!_uR._){var _uS=_uR.a,_uT=E(_uQ);if(!_uT._){var _uU=_uT.a;if(!(imul(_uS,_uU)|0)){return new T1(0,imul(_uS,_uU)|0);}else{_uP=new T1(1,I_fromInt(_uS));_uQ=new T1(1,I_fromInt(_uU));continue;}}else{_uP=new T1(1,I_fromInt(_uS));_uQ=_uT;continue;}}else{var _uV=E(_uQ);if(!_uV._){_uP=_uR;_uQ=new T1(1,I_fromInt(_uV.a));continue;}else{return new T1(1,I_mul(_uR.a,_uV.a));}}}},_uW=function(_uX,_uY,_uZ){while(1){if(!(_uY%2)){var _v0=B(_uO(_uX,_uX)),_v1=quot(_uY,2);_uX=_v0;_uY=_v1;continue;}else{var _v2=E(_uY);if(_v2==1){return new F(function(){return _uO(_uX,_uZ);});}else{var _v0=B(_uO(_uX,_uX)),_v3=B(_uO(_uX,_uZ));_uX=_v0;_uY=quot(_v2-1|0,2);_uZ=_v3;continue;}}}},_v4=function(_v5,_v6){while(1){if(!(_v6%2)){var _v7=B(_uO(_v5,_v5)),_v8=quot(_v6,2);_v5=_v7;_v6=_v8;continue;}else{var _v9=E(_v6);if(_v9==1){return E(_v5);}else{return new F(function(){return _uW(B(_uO(_v5,_v5)),quot(_v9-1|0,2),_v5);});}}}},_va=function(_vb){return E(E(_vb).b);},_vc=function(_vd){return E(E(_vd).c);},_ve=new T1(0,0),_vf=function(_vg){return E(E(_vg).d);},_vh=function(_vi,_vj){var _vk=B(_rQ(_vi)),_vl=new T(function(){return B(_rS(_vk));}),_vm=new T(function(){return B(A3(_vf,_vi,_vj,new T(function(){return B(A2(_91,_vl,_mH));})));});return new F(function(){return A3(_ls,B(_le(B(_va(_vk)))),_vm,new T(function(){return B(A2(_91,_vl,_ve));}));});},_vn=new T(function(){return B(unCStr("Negative exponent"));}),_vo=new T(function(){return B(err(_vn));}),_vp=function(_vq){return E(E(_vq).c);},_vr=function(_vs,_vt,_vu,_vv){var _vw=B(_rQ(_vt)),_vx=new T(function(){return B(_rS(_vw));}),_vy=B(_va(_vw));if(!B(A3(_vc,_vy,_vv,new T(function(){return B(A2(_91,_vx,_ve));})))){if(!B(A3(_ls,B(_le(_vy)),_vv,new T(function(){return B(A2(_91,_vx,_ve));})))){var _vz=new T(function(){return B(A2(_91,_vx,_mH));}),_vA=new T(function(){return B(A2(_91,_vx,_mx));}),_vB=B(_le(_vy)),_vC=function(_vD,_vE,_vF){while(1){var _vG=B((function(_vH,_vI,_vJ){if(!B(_vh(_vt,_vI))){if(!B(A3(_ls,_vB,_vI,_vA))){var _vK=new T(function(){return B(A3(_vp,_vt,new T(function(){return B(A3(_7m,_vx,_vI,_vA));}),_vz));});_vD=new T(function(){return B(A3(_7k,_vs,_vH,_vH));});_vE=_vK;_vF=new T(function(){return B(A3(_7k,_vs,_vH,_vJ));});return __continue;}else{return new F(function(){return A3(_7k,_vs,_vH,_vJ);});}}else{var _vL=_vJ;_vD=new T(function(){return B(A3(_7k,_vs,_vH,_vH));});_vE=new T(function(){return B(A3(_vp,_vt,_vI,_vz));});_vF=_vL;return __continue;}})(_vD,_vE,_vF));if(_vG!=__continue){return _vG;}}},_vM=function(_vN,_vO){while(1){var _vP=B((function(_vQ,_vR){if(!B(_vh(_vt,_vR))){if(!B(A3(_ls,_vB,_vR,_vA))){var _vS=new T(function(){return B(A3(_vp,_vt,new T(function(){return B(A3(_7m,_vx,_vR,_vA));}),_vz));});return new F(function(){return _vC(new T(function(){return B(A3(_7k,_vs,_vQ,_vQ));}),_vS,_vQ);});}else{return E(_vQ);}}else{_vN=new T(function(){return B(A3(_7k,_vs,_vQ,_vQ));});_vO=new T(function(){return B(A3(_vp,_vt,_vR,_vz));});return __continue;}})(_vN,_vO));if(_vP!=__continue){return _vP;}}};return new F(function(){return _vM(_vu,_vv);});}else{return new F(function(){return A2(_91,_vs,_mx);});}}else{return E(_vo);}},_vT=new T(function(){return B(err(_vn));}),_vU=function(_vV,_vW){var _vX=B(_qM(_vW)),_vY=_vX.a,_vZ=_vX.b,_w0=new T(function(){return B(_rS(new T(function(){return B(_rQ(_vV));})));});if(_vZ<0){var _w1= -_vZ;if(_w1>=0){var _w2=E(_w1);if(!_w2){var _w3=E(_mx);}else{var _w3=B(_v4(_uN,_w2));}if(!B(_30(_w3,_3t))){var _w4=B(_3k(_vY,_w3));return new T2(0,new T(function(){return B(A2(_91,_w0,_w4.a));}),new T(function(){return B(_2W(_w4.b,_vZ));}));}else{return E(_2V);}}else{return E(_vT);}}else{var _w5=new T(function(){var _w6=new T(function(){return B(_vr(_w0,_uM,new T(function(){return B(A2(_91,_w0,_uN));}),_vZ));});return B(A3(_7k,_w0,new T(function(){return B(A2(_91,_w0,_vY));}),_w6));});return new T2(0,_w5,_6i);}},_w7=function(_w8,_w9){var _wa=B(_vU(_w8,E(_w9))),_wb=_wa.a;if(E(_wa.b)<=0){return E(_wb);}else{var _wc=B(_rS(B(_rQ(_w8))));return new F(function(){return A3(_6I,_wc,_wb,new T(function(){return B(A2(_91,_wc,_1M));}));});}},_wd=function(_we,_wf){var _wg=B(_vU(_we,E(_wf))),_wh=_wg.a;if(E(_wg.b)>=0){return E(_wh);}else{var _wi=B(_rS(B(_rQ(_we))));return new F(function(){return A3(_7m,_wi,_wh,new T(function(){return B(A2(_91,_wi,_1M));}));});}},_wj=function(_wk,_wl){var _wm=B(_vU(_wk,E(_wl)));return new T2(0,_wm.a,_wm.b);},_wn=function(_wo,_wp){var _wq=B(_vU(_wo,_wp)),_wr=_wq.a,_ws=E(_wq.b),_wt=new T(function(){var _wu=B(_rS(B(_rQ(_wo))));if(_ws>=0){return B(A3(_6I,_wu,_wr,new T(function(){return B(A2(_91,_wu,_1M));})));}else{return B(A3(_7m,_wu,_wr,new T(function(){return B(A2(_91,_wu,_1M));})));}}),_wv=function(_ww){var _wx=_ww-0.5;return (_wx>=0)?(E(_wx)==0)?(!B(_vh(_wo,_wr)))?E(_wt):E(_wr):E(_wt):E(_wr);},_wy=E(_ws);if(!_wy){return new F(function(){return _wv(0);});}else{if(_wy<=0){var _wz= -_wy-0.5;return (_wz>=0)?(E(_wz)==0)?(!B(_vh(_wo,_wr)))?E(_wt):E(_wr):E(_wt):E(_wr);}else{return new F(function(){return _wv(_wy);});}}},_wA=function(_wB,_wC){return new F(function(){return _wn(_wB,E(_wC));});},_wD=function(_wE,_wF){return E(B(_vU(_wE,E(_wF))).a);},_wG={_:0,a:_rP,b:_ip,c:_wj,d:_wD,e:_wA,f:_w7,g:_wd},_wH=new T1(0,1),_wI=function(_wJ,_wK){var _wL=E(_wJ);return new T2(0,_wL,new T(function(){var _wM=B(_wI(B(_3b(_wL,_wK)),_wK));return new T2(1,_wM.a,_wM.b);}));},_wN=function(_wO){var _wP=B(_wI(_wO,_wH));return new T2(1,_wP.a,_wP.b);},_wQ=function(_wR,_wS){var _wT=B(_wI(_wR,new T(function(){return B(_5w(_wS,_wR));})));return new T2(1,_wT.a,_wT.b);},_wU=new T1(0,0),_wV=function(_wW,_wX){var _wY=E(_wW);if(!_wY._){var _wZ=_wY.a,_x0=E(_wX);return (_x0._==0)?_wZ>=_x0.a:I_compareInt(_x0.a,_wZ)<=0;}else{var _x1=_wY.a,_x2=E(_wX);return (_x2._==0)?I_compareInt(_x1,_x2.a)>=0:I_compare(_x1,_x2.a)>=0;}},_x3=function(_x4,_x5,_x6){if(!B(_wV(_x5,_wU))){var _x7=function(_x8){return (!B(_3N(_x8,_x6)))?new T2(1,_x8,new T(function(){return B(_x7(B(_3b(_x8,_x5))));})):__Z;};return new F(function(){return _x7(_x4);});}else{var _x9=function(_xa){return (!B(_3E(_xa,_x6)))?new T2(1,_xa,new T(function(){return B(_x9(B(_3b(_xa,_x5))));})):__Z;};return new F(function(){return _x9(_x4);});}},_xb=function(_xc,_xd,_xe){return new F(function(){return _x3(_xc,B(_5w(_xd,_xc)),_xe);});},_xf=function(_xg,_xh){return new F(function(){return _x3(_xg,_wH,_xh);});},_xi=function(_xj){return new F(function(){return _38(_xj);});},_xk=function(_xl){return new F(function(){return _5w(_xl,_wH);});},_xm=function(_xn){return new F(function(){return _3b(_xn,_wH);});},_xo=function(_xp){return new F(function(){return _qP(E(_xp));});},_xq={_:0,a:_xm,b:_xk,c:_xo,d:_xi,e:_wN,f:_wQ,g:_xf,h:_xb},_xr=function(_xs,_xt){while(1){var _xu=E(_xs);if(!_xu._){var _xv=E(_xu.a);if(_xv==(-2147483648)){_xs=new T1(1,I_fromInt(-2147483648));continue;}else{var _xw=E(_xt);if(!_xw._){return new T1(0,B(_sL(_xv,_xw.a)));}else{_xs=new T1(1,I_fromInt(_xv));_xt=_xw;continue;}}}else{var _xx=_xu.a,_xy=E(_xt);return (_xy._==0)?new T1(1,I_div(_xx,I_fromInt(_xy.a))):new T1(1,I_div(_xx,_xy.a));}}},_xz=function(_xA,_xB){if(!B(_30(_xB,_ve))){return new F(function(){return _xr(_xA,_xB);});}else{return E(_2V);}},_xC=function(_xD,_xE){while(1){var _xF=E(_xD);if(!_xF._){var _xG=E(_xF.a);if(_xG==(-2147483648)){_xD=new T1(1,I_fromInt(-2147483648));continue;}else{var _xH=E(_xE);if(!_xH._){var _xI=_xH.a;return new T2(0,new T1(0,B(_sL(_xG,_xI))),new T1(0,B(_th(_xG,_xI))));}else{_xD=new T1(1,I_fromInt(_xG));_xE=_xH;continue;}}}else{var _xJ=E(_xE);if(!_xJ._){_xD=_xF;_xE=new T1(1,I_fromInt(_xJ.a));continue;}else{var _xK=I_divMod(_xF.a,_xJ.a);return new T2(0,new T1(1,_xK.a),new T1(1,_xK.b));}}}},_xL=function(_xM,_xN){if(!B(_30(_xN,_ve))){var _xO=B(_xC(_xM,_xN));return new T2(0,_xO.a,_xO.b);}else{return E(_2V);}},_xP=function(_xQ,_xR){while(1){var _xS=E(_xQ);if(!_xS._){var _xT=E(_xS.a);if(_xT==(-2147483648)){_xQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _xU=E(_xR);if(!_xU._){return new T1(0,B(_th(_xT,_xU.a)));}else{_xQ=new T1(1,I_fromInt(_xT));_xR=_xU;continue;}}}else{var _xV=_xS.a,_xW=E(_xR);return (_xW._==0)?new T1(1,I_mod(_xV,I_fromInt(_xW.a))):new T1(1,I_mod(_xV,_xW.a));}}},_xX=function(_xY,_xZ){if(!B(_30(_xZ,_ve))){return new F(function(){return _xP(_xY,_xZ);});}else{return E(_2V);}},_y0=function(_y1,_y2){while(1){var _y3=E(_y1);if(!_y3._){var _y4=E(_y3.a);if(_y4==(-2147483648)){_y1=new T1(1,I_fromInt(-2147483648));continue;}else{var _y5=E(_y2);if(!_y5._){return new T1(0,quot(_y4,_y5.a));}else{_y1=new T1(1,I_fromInt(_y4));_y2=_y5;continue;}}}else{var _y6=_y3.a,_y7=E(_y2);return (_y7._==0)?new T1(0,I_toInt(I_quot(_y6,I_fromInt(_y7.a)))):new T1(1,I_quot(_y6,_y7.a));}}},_y8=function(_y9,_ya){if(!B(_30(_ya,_ve))){return new F(function(){return _y0(_y9,_ya);});}else{return E(_2V);}},_yb=function(_yc,_yd){if(!B(_30(_yd,_ve))){var _ye=B(_3k(_yc,_yd));return new T2(0,_ye.a,_ye.b);}else{return E(_2V);}},_yf=function(_yg,_yh){while(1){var _yi=E(_yg);if(!_yi._){var _yj=E(_yi.a);if(_yj==(-2147483648)){_yg=new T1(1,I_fromInt(-2147483648));continue;}else{var _yk=E(_yh);if(!_yk._){return new T1(0,_yj%_yk.a);}else{_yg=new T1(1,I_fromInt(_yj));_yh=_yk;continue;}}}else{var _yl=_yi.a,_ym=E(_yh);return (_ym._==0)?new T1(1,I_rem(_yl,I_fromInt(_ym.a))):new T1(1,I_rem(_yl,_ym.a));}}},_yn=function(_yo,_yp){if(!B(_30(_yp,_ve))){return new F(function(){return _yf(_yo,_yp);});}else{return E(_2V);}},_yq=function(_yr){return E(_yr);},_ys=function(_yt){return E(_yt);},_yu=function(_yv){var _yw=E(_yv);if(!_yw._){var _yx=E(_yw.a);return (_yx==(-2147483648))?E(_6a):(_yx<0)?new T1(0, -_yx):E(_yw);}else{var _yy=_yw.a;return (I_compareInt(_yy,0)>=0)?E(_yw):new T1(1,I_negate(_yy));}},_yz=new T1(0,0),_yA=new T1(0,-1),_yB=function(_yC){var _yD=E(_yC);if(!_yD._){var _yE=_yD.a;return (_yE>=0)?(E(_yE)==0)?E(_yz):E(_3M):E(_yA);}else{var _yF=I_compareInt(_yD.a,0);return (_yF<=0)?(E(_yF)==0)?E(_yz):E(_yA):E(_3M);}},_yG={_:0,a:_3b,b:_5w,c:_uO,d:_6b,e:_yu,f:_yB,g:_ys},_yH=function(_yI,_yJ){var _yK=E(_yI);if(!_yK._){var _yL=_yK.a,_yM=E(_yJ);return (_yM._==0)?_yL!=_yM.a:(I_compareInt(_yM.a,_yL)==0)?false:true;}else{var _yN=_yK.a,_yO=E(_yJ);return (_yO._==0)?(I_compareInt(_yN,_yO.a)==0)?false:true:(I_compare(_yN,_yO.a)==0)?false:true;}},_yP=new T2(0,_30,_yH),_yQ=function(_yR,_yS){return (!B(_5h(_yR,_yS)))?E(_yR):E(_yS);},_yT=function(_yU,_yV){return (!B(_5h(_yU,_yV)))?E(_yV):E(_yU);},_yW={_:0,a:_yP,b:_1N,c:_3N,d:_5h,e:_3E,f:_wV,g:_yQ,h:_yT},_yX=function(_yY){return new T2(0,E(_yY),E(_mx));},_yZ=new T3(0,_yG,_yW,_yX),_z0={_:0,a:_yZ,b:_xq,c:_y8,d:_yn,e:_xz,f:_xX,g:_yb,h:_xL,i:_yq},_z1=function(_z2){return E(E(_z2).b);},_z3=function(_z4){return E(E(_z4).g);},_z5=new T1(0,1),_z6=function(_z7,_z8,_z9){var _za=B(_z1(_z7)),_zb=B(_7i(_za)),_zc=new T(function(){var _zd=new T(function(){var _ze=new T(function(){var _zf=new T(function(){return B(A3(_z3,_z7,_z0,new T(function(){return B(A3(_9b,_za,_z8,_z9));})));});return B(A2(_91,_zb,_zf));}),_zg=new T(function(){return B(A2(_6K,_zb,new T(function(){return B(A2(_91,_zb,_z5));})));});return B(A3(_7k,_zb,_zg,_ze));});return B(A3(_7k,_zb,_zd,_z9));});return new F(function(){return A3(_6I,_zb,_z8,_zc);});},_zh=1.5707963267948966,_zi=function(_zj){return 0.2/Math.cos(B(_z6(_wG,_zj,_zh))-0.7853981633974483);},_zk=4,_zl=0.3,_zm=new T(function(){var _zn=B(_pg(_zi,1.2,_qL,_qz,_qz,_qz,_qz,_qK,_zl,_zk,_qz,_qz,_qG));return {_:0,a:E(_zn.a),b:E(_zn.b),c:E(_zn.c),d:E(_zn.d),e:E(_zn.e),f:E(_zn.f),g:E(_zn.g),h:_zn.h,i:_zn.i};}),_zo=new T2(1,_zm,_o),_zp=new T2(1,_qH,_zo),_zq=new T(function(){return B(unCStr("Negative range size"));}),_zr=new T(function(){return B(err(_zq));}),_zs=function(_){var _zt=B(_hf(_zp,0))-1|0,_zu=function(_zv){if(_zv>=0){var _zw=newArr(_zv,_hl),_zx=_zw,_zy=E(_zv);if(!_zy){return new T4(0,E(_qJ),E(_zt),0,_zx);}else{var _zz=function(_zA,_zB,_){while(1){var _zC=E(_zA);if(!_zC._){return E(_);}else{var _=_zx[_zB]=_zC.a;if(_zB!=(_zy-1|0)){var _zD=_zB+1|0;_zA=_zC.b;_zB=_zD;continue;}else{return E(_);}}}},_=B((function(_zE,_zF,_zG,_){var _=_zx[_zG]=_zE;if(_zG!=(_zy-1|0)){return new F(function(){return _zz(_zF,_zG+1|0,_);});}else{return E(_);}})(_qH,_zo,0,_));return new T4(0,E(_qJ),E(_zt),_zy,_zx);}}else{return E(_zr);}};if(0>_zt){return new F(function(){return _zu(0);});}else{return new F(function(){return _zu(_zt+1|0);});}},_zH=function(_zI){var _zJ=B(A1(_zI,_));return E(_zJ);},_zK=new T(function(){return B(_zH(_zs));}),_zL=function(_zM,_zN,_){var _zO=B(A1(_zM,_)),_zP=B(A1(_zN,_));return _zO;},_zQ=function(_zR,_zS,_){var _zT=B(A1(_zR,_)),_zU=B(A1(_zS,_));return new T(function(){return B(A1(_zT,_zU));});},_zV=function(_zW,_zX,_){var _zY=B(A1(_zX,_));return _zW;},_zZ=function(_A0,_A1,_){var _A2=B(A1(_A1,_));return new T(function(){return B(A1(_A0,_A2));});},_A3=new T2(0,_zZ,_zV),_A4=function(_A5,_){return _A5;},_A6=function(_A7,_A8,_){var _A9=B(A1(_A7,_));return new F(function(){return A1(_A8,_);});},_Aa=new T5(0,_A3,_A4,_zQ,_A6,_zL),_Ab=function(_Ac){var _Ad=E(_Ac);return (E(_Ad.b)-E(_Ad.a)|0)+1|0;},_Ae=function(_Af,_Ag){var _Ah=E(_Af),_Ai=E(_Ag);return (E(_Ah.a)>_Ai)?false:_Ai<=E(_Ah.b);},_Aj=function(_Ak,_Al){var _Am=jsShowI(_Ak);return new F(function(){return _f(fromJSStr(_Am),_Al);});},_An=function(_Ao,_Ap,_Aq){if(_Ap>=0){return new F(function(){return _Aj(_Ap,_Aq);});}else{if(_Ao<=6){return new F(function(){return _Aj(_Ap,_Aq);});}else{return new T2(1,_71,new T(function(){var _Ar=jsShowI(_Ap);return B(_f(fromJSStr(_Ar),new T2(1,_70,_Aq)));}));}}},_As=function(_At){return new F(function(){return _An(0,E(_At),_o);});},_Au=function(_Av,_Aw,_Ax){return new F(function(){return _An(E(_Av),E(_Aw),_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _An(0,E(_Az),_AA);});},_AB=function(_AC,_AD){return new F(function(){return _2B(_Ay,_AC,_AD);});},_AE=new T3(0,_Au,_As,_AB),_AF=0,_AG=function(_AH,_AI,_AJ){return new F(function(){return A1(_AH,new T2(1,_2y,new T(function(){return B(A1(_AI,_AJ));})));});},_AK=new T(function(){return B(unCStr("foldr1"));}),_AL=new T(function(){return B(_lX(_AK));}),_AM=function(_AN,_AO){var _AP=E(_AO);if(!_AP._){return E(_AL);}else{var _AQ=_AP.a,_AR=E(_AP.b);if(!_AR._){return E(_AQ);}else{return new F(function(){return A2(_AN,_AQ,new T(function(){return B(_AM(_AN,_AR));}));});}}},_AS=new T(function(){return B(unCStr(" out of range "));}),_AT=new T(function(){return B(unCStr("}.index: Index "));}),_AU=new T(function(){return B(unCStr("Ix{"));}),_AV=new T2(1,_70,_o),_AW=new T2(1,_70,_AV),_AX=0,_AY=function(_AZ){return E(E(_AZ).a);},_B0=function(_B1,_B2,_B3,_B4,_B5){var _B6=new T(function(){var _B7=new T(function(){var _B8=new T(function(){var _B9=new T(function(){var _Ba=new T(function(){return B(A3(_AM,_AG,new T2(1,new T(function(){return B(A3(_AY,_B3,_AX,_B4));}),new T2(1,new T(function(){return B(A3(_AY,_B3,_AX,_B5));}),_o)),_AW));});return B(_f(_AS,new T2(1,_71,new T2(1,_71,_Ba))));});return B(A(_AY,[_B3,_AF,_B2,new T2(1,_70,_B9)]));});return B(_f(_AT,new T2(1,_71,_B8)));},1);return B(_f(_B1,_B7));},1);return new F(function(){return err(B(_f(_AU,_B6)));});},_Bb=function(_Bc,_Bd,_Be,_Bf,_Bg){return new F(function(){return _B0(_Bc,_Bd,_Bg,_Be,_Bf);});},_Bh=function(_Bi,_Bj,_Bk,_Bl){var _Bm=E(_Bk);return new F(function(){return _Bb(_Bi,_Bj,_Bm.a,_Bm.b,_Bl);});},_Bn=function(_Bo,_Bp,_Bq,_Br){return new F(function(){return _Bh(_Br,_Bq,_Bp,_Bo);});},_Bs=new T(function(){return B(unCStr("Int"));}),_Bt=function(_Bu,_Bv){return new F(function(){return _Bn(_AE,_Bv,_Bu,_Bs);});},_Bw=function(_Bx,_By){var _Bz=E(_Bx),_BA=E(_Bz.a),_BB=E(_By);if(_BA>_BB){return new F(function(){return _Bt(_BB,_Bz);});}else{if(_BB>E(_Bz.b)){return new F(function(){return _Bt(_BB,_Bz);});}else{return _BB-_BA|0;}}},_BC=function(_BD){var _BE=E(_BD);return new F(function(){return _sv(_BE.a,_BE.b);});},_BF=function(_BG){var _BH=E(_BG),_BI=E(_BH.a),_BJ=E(_BH.b);return (_BI>_BJ)?E(_AF):(_BJ-_BI|0)+1|0;},_BK=function(_BL,_BM){return new F(function(){return _tU(_BM,E(_BL).a);});},_BN={_:0,a:_uK,b:_BC,c:_Bw,d:_BK,e:_Ae,f:_BF,g:_Ab},_BO=function(_BP,_BQ){return new T2(1,_BP,_BQ);},_BR=function(_BS,_BT){var _BU=E(_BT);return new T2(0,_BU.a,_BU.b);},_BV=function(_BW){return E(E(_BW).f);},_BX=function(_BY,_BZ,_C0){var _C1=E(_BZ),_C2=_C1.a,_C3=_C1.b,_C4=function(_){var _C5=B(A2(_BV,_BY,_C1));if(_C5>=0){var _C6=newArr(_C5,_hl),_C7=_C6,_C8=E(_C5);if(!_C8){return new T(function(){return new T4(0,E(_C2),E(_C3),0,_C7);});}else{var _C9=function(_Ca,_Cb,_){while(1){var _Cc=E(_Ca);if(!_Cc._){return E(_);}else{var _=_C7[_Cb]=_Cc.a;if(_Cb!=(_C8-1|0)){var _Cd=_Cb+1|0;_Ca=_Cc.b;_Cb=_Cd;continue;}else{return E(_);}}}},_=B(_C9(_C0,0,_));return new T(function(){return new T4(0,E(_C2),E(_C3),_C8,_C7);});}}else{return E(_zr);}};return new F(function(){return _zH(_C4);});},_Ce=function(_Cf,_Cg,_Ch,_Ci){var _Cj=new T(function(){var _Ck=E(_Ci),_Cl=_Ck.c-1|0,_Cm=new T(function(){return B(A2(_cX,_Cg,_o));});if(0<=_Cl){var _Cn=new T(function(){return B(_97(_Cg));}),_Co=function(_Cp){var _Cq=new T(function(){var _Cr=new T(function(){return B(A1(_Ch,new T(function(){return E(_Ck.d[_Cp]);})));});return B(A3(_9f,_Cn,_BO,_Cr));});return new F(function(){return A3(_9d,_Cg,_Cq,new T(function(){if(_Cp!=_Cl){return B(_Co(_Cp+1|0));}else{return E(_Cm);}}));});};return B(_Co(0));}else{return E(_Cm);}}),_Cs=new T(function(){return B(_BR(_Cf,_Ci));});return new F(function(){return A3(_9f,B(_97(_Cg)),function(_Ct){return new F(function(){return _BX(_Cf,_Cs,_Ct);});},_Cj);});},_Cu=function(_Cv){return E(E(_Cv).a);},_Cw=function(_Cx,_Cy,_Cz,_CA,_CB){var _CC=B(A2(_Cu,_Cx,E(_CB)));return new F(function(){return A2(_Cy,_Cz,new T2(1,_CC,E(_CA)));});},_CD="outline",_CE="polygon",_CF=function(_CG){return new F(function(){return _jD(new T2(1,new T2(0,_CE,new T(function(){return E(_CG).h;})),new T2(1,new T2(0,_CD,new T(function(){return E(_CG).i;})),_o)));});},_CH=function(_CI){return new F(function(){return _CF(_CI);});},_CJ=function(_CK){return new F(function(){return __lst2arr(B(_k3(_CH,_CK)));});},_CL=new T2(0,_CH,_CJ),_CM=function(_CN,_){var _CO=E(_CN);if(!_CO._){return _o;}else{var _CP=B(_CM(_CO.b,_));return new T2(1,_jC,_CP);}},_CQ=function(_CR,_){var _CS=__arr2lst(0,_CR);return new F(function(){return _CM(_CS,_);});},_CT=function(_CU,_){return new F(function(){return _CQ(E(_CU),_);});},_CV=function(_){return _jC;},_CW=function(_CX,_){return new F(function(){return _CV(_);});},_CY=new T2(0,_CW,_CT),_CZ=function(_D0){return E(E(_D0).a);},_D1=function(_D2,_D3,_D4,_){var _D5=__apply(_D3,E(_D4));return new F(function(){return A3(_CZ,_D2,_D5,_);});},_D6=function(_D7,_D8,_D9,_){return new F(function(){return _D1(_D7,E(_D8),_D9,_);});},_Da=function(_Db,_Dc,_Dd,_){return new F(function(){return _D6(_Db,_Dc,_Dd,_);});},_De=function(_Df,_Dg,_){return new F(function(){return _Da(_CY,_Df,_Dg,_);});},_Dh=new T(function(){return eval("drawObject");}),_Di=function(_Dj){return new F(function(){return _Cw(_CL,_De,_Dh,_o,_Dj);});},_Dk=new T(function(){return eval("__strict(draw)");}),_Dl=function(_Dm){return E(_Dm);},_Dn=function(_Do){return E(_Do);},_Dp=function(_Dq,_Dr){return E(_Dr);},_Ds=function(_Dt,_Du){return E(_Dt);},_Dv=function(_Dw){return E(_Dw);},_Dx=new T2(0,_Dv,_Ds),_Dy=function(_Dz,_DA){return E(_Dz);},_DB=new T5(0,_Dx,_Dn,_Dl,_Dp,_Dy),_DC="d2z",_DD="d2y",_DE="w2z",_DF="w2y",_DG="w2x",_DH="w1z",_DI="w1y",_DJ="w1x",_DK="d2x",_DL="d1z",_DM="d1y",_DN="d1x",_DO="c2y",_DP="c2x",_DQ="c1y",_DR="c1x",_DS=function(_DT,_){var _DU=__get(_DT,E(_DJ)),_DV=__get(_DT,E(_DI)),_DW=__get(_DT,E(_DH)),_DX=__get(_DT,E(_DG)),_DY=__get(_DT,E(_DF)),_DZ=__get(_DT,E(_DE)),_E0=__get(_DT,E(_DR)),_E1=__get(_DT,E(_DQ)),_E2=__get(_DT,E(_DP)),_E3=__get(_DT,E(_DO)),_E4=__get(_DT,E(_DN)),_E5=__get(_DT,E(_DM)),_E6=__get(_DT,E(_DL)),_E7=__get(_DT,E(_DK)),_E8=__get(_DT,E(_DD)),_E9=__get(_DT,E(_DC));return new T6(0,E(new T3(0,E(_DU),E(_DV),E(_DW))),E(new T3(0,E(_DX),E(_DY),E(_DZ))),E(new T2(0,E(_E0),E(_E1))),E(new T2(0,E(_E2),E(_E3))),E(new T3(0,E(_E4),E(_E5),E(_E6))),E(new T3(0,E(_E7),E(_E8),E(_E9))));},_Ea=function(_Eb,_){var _Ec=E(_Eb);if(!_Ec._){return _o;}else{var _Ed=B(_DS(E(_Ec.a),_)),_Ee=B(_Ea(_Ec.b,_));return new T2(1,_Ed,_Ee);}},_Ef=function(_Eg,_Eh,_){while(1){var _Ei=B((function(_Ej,_Ek,_){var _El=E(_Ej);if(!_El._){return new T2(0,_jC,_Ek);}else{var _Em=B(A2(_El.a,_Ek,_));_Eg=_El.b;_Eh=new T(function(){return E(E(_Em).b);});return __continue;}})(_Eg,_Eh,_));if(_Ei!=__continue){return _Ei;}}},_En=function(_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew){var _Ex=B(_7k(_Eo));return new T2(0,new T3(0,E(B(A1(B(A1(_Ex,_Ep)),_Et))),E(B(A1(B(A1(_Ex,_Eq)),_Eu))),E(B(A1(B(A1(_Ex,_Er)),_Ev)))),B(A1(B(A1(_Ex,_Es)),_Ew)));},_Ey=function(_Ez,_EA,_EB,_EC,_ED,_EE,_EF,_EG,_EH){var _EI=B(_6I(_Ez));return new T2(0,new T3(0,E(B(A1(B(A1(_EI,_EA)),_EE))),E(B(A1(B(A1(_EI,_EB)),_EF))),E(B(A1(B(A1(_EI,_EC)),_EG)))),B(A1(B(A1(_EI,_ED)),_EH)));},_EJ=1.0e-2,_EK=function(_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1){var _F2=B(_En(_il,_ES,_ET,_EU,_EV,_EJ,_EJ,_EJ,_EJ)),_F3=E(_F2.a),_F4=B(_Ey(_il,_EO,_EP,_EQ,_ER,_F3.a,_F3.b,_F3.c,_F2.b)),_F5=E(_F4.a);return new F(function(){return _oy(_EL,_EM,_EN,_F5.a,_F5.b,_F5.c,_F4.b,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1);});},_F6=function(_F7){var _F8=E(_F7),_F9=E(_F8.d),_Fa=E(_F9.a),_Fb=E(_F8.e),_Fc=E(_Fb.a),_Fd=E(_F8.f),_Fe=B(_EK(_F8.a,_F8.b,_F8.c,_Fa.a,_Fa.b,_Fa.c,_F9.b,_Fc.a,_Fc.b,_Fc.c,_Fb.b,_Fd.a,_Fd.b,_Fd.c,_F8.g,_F8.h,_F8.i));return {_:0,a:E(_Fe.a),b:E(_Fe.b),c:E(_Fe.c),d:E(_Fe.d),e:E(_Fe.e),f:E(_Fe.f),g:E(_Fe.g),h:_Fe.h,i:_Fe.i};},_Ff=function(_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo){var _Fp=B(_7i(B(_7g(_Fg))));return new F(function(){return A3(_6I,_Fp,new T(function(){return B(_kg(_Fg,_Fh,_Fi,_Fj,_Fl,_Fm,_Fn));}),new T(function(){return B(A3(_7k,_Fp,_Fk,_Fo));}));});},_Fq=new T(function(){return B(unCStr("base"));}),_Fr=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fs=new T(function(){return B(unCStr("IOException"));}),_Ft=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fq,_Fr,_Fs),_Fu=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Ft,_o,_o),_Fv=function(_Fw){return E(_Fu);},_Fx=function(_Fy){var _Fz=E(_Fy);return new F(function(){return _28(B(_26(_Fz.a)),_Fv,_Fz.b);});},_FA=new T(function(){return B(unCStr(": "));}),_FB=new T(function(){return B(unCStr(")"));}),_FC=new T(function(){return B(unCStr(" ("));}),_FD=new T(function(){return B(unCStr("interrupted"));}),_FE=new T(function(){return B(unCStr("system error"));}),_FF=new T(function(){return B(unCStr("unsatisified constraints"));}),_FG=new T(function(){return B(unCStr("user error"));}),_FH=new T(function(){return B(unCStr("permission denied"));}),_FI=new T(function(){return B(unCStr("illegal operation"));}),_FJ=new T(function(){return B(unCStr("end of file"));}),_FK=new T(function(){return B(unCStr("resource exhausted"));}),_FL=new T(function(){return B(unCStr("resource busy"));}),_FM=new T(function(){return B(unCStr("does not exist"));}),_FN=new T(function(){return B(unCStr("already exists"));}),_FO=new T(function(){return B(unCStr("resource vanished"));}),_FP=new T(function(){return B(unCStr("timeout"));}),_FQ=new T(function(){return B(unCStr("unsupported operation"));}),_FR=new T(function(){return B(unCStr("hardware fault"));}),_FS=new T(function(){return B(unCStr("inappropriate type"));}),_FT=new T(function(){return B(unCStr("invalid argument"));}),_FU=new T(function(){return B(unCStr("failed"));}),_FV=new T(function(){return B(unCStr("protocol error"));}),_FW=function(_FX,_FY){switch(E(_FX)){case 0:return new F(function(){return _f(_FN,_FY);});break;case 1:return new F(function(){return _f(_FM,_FY);});break;case 2:return new F(function(){return _f(_FL,_FY);});break;case 3:return new F(function(){return _f(_FK,_FY);});break;case 4:return new F(function(){return _f(_FJ,_FY);});break;case 5:return new F(function(){return _f(_FI,_FY);});break;case 6:return new F(function(){return _f(_FH,_FY);});break;case 7:return new F(function(){return _f(_FG,_FY);});break;case 8:return new F(function(){return _f(_FF,_FY);});break;case 9:return new F(function(){return _f(_FE,_FY);});break;case 10:return new F(function(){return _f(_FV,_FY);});break;case 11:return new F(function(){return _f(_FU,_FY);});break;case 12:return new F(function(){return _f(_FT,_FY);});break;case 13:return new F(function(){return _f(_FS,_FY);});break;case 14:return new F(function(){return _f(_FR,_FY);});break;case 15:return new F(function(){return _f(_FQ,_FY);});break;case 16:return new F(function(){return _f(_FP,_FY);});break;case 17:return new F(function(){return _f(_FO,_FY);});break;default:return new F(function(){return _f(_FD,_FY);});}},_FZ=new T(function(){return B(unCStr("}"));}),_G0=new T(function(){return B(unCStr("{handle: "));}),_G1=function(_G2,_G3,_G4,_G5,_G6,_G7){var _G8=new T(function(){var _G9=new T(function(){var _Ga=new T(function(){var _Gb=E(_G5);if(!_Gb._){return E(_G7);}else{var _Gc=new T(function(){return B(_f(_Gb,new T(function(){return B(_f(_FB,_G7));},1)));},1);return B(_f(_FC,_Gc));}},1);return B(_FW(_G3,_Ga));}),_Gd=E(_G4);if(!_Gd._){return E(_G9);}else{return B(_f(_Gd,new T(function(){return B(_f(_FA,_G9));},1)));}}),_Ge=E(_G6);if(!_Ge._){var _Gf=E(_G2);if(!_Gf._){return E(_G8);}else{var _Gg=E(_Gf.a);if(!_Gg._){var _Gh=new T(function(){var _Gi=new T(function(){return B(_f(_FZ,new T(function(){return B(_f(_FA,_G8));},1)));},1);return B(_f(_Gg.a,_Gi));},1);return new F(function(){return _f(_G0,_Gh);});}else{var _Gj=new T(function(){var _Gk=new T(function(){return B(_f(_FZ,new T(function(){return B(_f(_FA,_G8));},1)));},1);return B(_f(_Gg.a,_Gk));},1);return new F(function(){return _f(_G0,_Gj);});}}}else{return new F(function(){return _f(_Ge.a,new T(function(){return B(_f(_FA,_G8));},1));});}},_Gl=function(_Gm){var _Gn=E(_Gm);return new F(function(){return _G1(_Gn.a,_Gn.b,_Gn.c,_Gn.d,_Gn.f,_o);});},_Go=function(_Gp,_Gq,_Gr){var _Gs=E(_Gq);return new F(function(){return _G1(_Gs.a,_Gs.b,_Gs.c,_Gs.d,_Gs.f,_Gr);});},_Gt=function(_Gu,_Gv){var _Gw=E(_Gu);return new F(function(){return _G1(_Gw.a,_Gw.b,_Gw.c,_Gw.d,_Gw.f,_Gv);});},_Gx=function(_Gy,_Gz){return new F(function(){return _2B(_Gt,_Gy,_Gz);});},_GA=new T3(0,_Go,_Gl,_Gx),_GB=new T(function(){return new T5(0,_Fv,_GA,_GC,_Fx,_Gl);}),_GC=function(_GD){return new T2(0,_GB,_GD);},_GE=__Z,_GF=7,_GG=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:78:3-9"));}),_GH=new T6(0,_GE,_GF,_o,_GG,_GE,_GE),_GI=new T(function(){return B(_GC(_GH));}),_GJ=function(_){return new F(function(){return die(_GI);});},_GK=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:77:3-9"));}),_GL=new T6(0,_GE,_GF,_o,_GK,_GE,_GE),_GM=new T(function(){return B(_GC(_GL));}),_GN=function(_){return new F(function(){return die(_GM);});},_GO=function(_GP,_){return new T2(0,_o,_GP);},_GQ=1,_GR=new T(function(){return B(unCStr(")"));}),_GS=function(_GT,_GU){var _GV=new T(function(){var _GW=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_An(0,_GT,_o)),_GR));})));},1);return B(_f(B(_An(0,_GU,_o)),_GW));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GV)));});},_GX=function(_GY,_GZ){var _H0=new T(function(){var _H1=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_An(0,_GZ,_o)),_GR));})));},1);return B(_f(B(_An(0,_GY,_o)),_H1));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_H0)));});},_H2=0.6,_H3=function(_H4){var _H5=E(_H4);if(!_H5._){return E(_GO);}else{var _H6=new T(function(){return B(_H3(_H5.b));}),_H7=function(_H8){var _H9=E(_H8);if(!_H9._){return E(_H6);}else{var _Ha=_H9.a,_Hb=new T(function(){return B(_H7(_H9.b));}),_Hc=new T(function(){return 0.1*E(E(_Ha).e)/1.0e-2;}),_Hd=new T(function(){var _He=E(_Ha);if(_He.a!=_He.b){return E(_GQ);}else{return E(_H2);}}),_Hf=function(_Hg,_){var _Hh=E(_Hg),_Hi=_Hh.c,_Hj=_Hh.d,_Hk=E(_Hh.a),_Hl=E(_Hh.b),_Hm=E(_Ha),_Hn=_Hm.a,_Ho=_Hm.b,_Hp=E(_Hm.c),_Hq=_Hp.b,_Hr=E(_Hp.a),_Hs=_Hr.a,_Ht=_Hr.b,_Hu=_Hr.c,_Hv=E(_Hm.d),_Hw=_Hv.b,_Hx=E(_Hv.a),_Hy=_Hx.a,_Hz=_Hx.b,_HA=_Hx.c;if(_Hk>_Hn){return new F(function(){return _GN(_);});}else{if(_Hn>_Hl){return new F(function(){return _GN(_);});}else{if(_Hk>_Ho){return new F(function(){return _GJ(_);});}else{if(_Ho>_Hl){return new F(function(){return _GJ(_);});}else{var _HB=_Hn-_Hk|0;if(0>_HB){return new F(function(){return _GS(_Hi,_HB);});}else{if(_HB>=_Hi){return new F(function(){return _GS(_Hi,_HB);});}else{var _HC=E(_Hj[_HB]),_HD=E(_HC.c),_HE=_HD.b,_HF=E(_HD.a),_HG=_HF.a,_HH=_HF.b,_HI=_HF.c,_HJ=E(_HC.e),_HK=E(_HJ.a),_HL=B(_En(_il,_Hs,_Ht,_Hu,_Hq,_HG,_HH,_HI,_HE)),_HM=E(_HL.a),_HN=B(_En(_il,_HM.a,_HM.b,_HM.c,_HL.b,_Hs,_Ht,_Hu,_Hq)),_HO=E(_HN.a),_HP=_Ho-_Hk|0;if(0>_HP){return new F(function(){return _GX(_HP,_Hi);});}else{if(_HP>=_Hi){return new F(function(){return _GX(_HP,_Hi);});}else{var _HQ=E(_Hj[_HP]),_HR=E(_HQ.c),_HS=_HR.b,_HT=E(_HR.a),_HU=_HT.a,_HV=_HT.b,_HW=_HT.c,_HX=E(_HQ.e),_HY=E(_HX.a),_HZ=B(_En(_il,_Hy,_Hz,_HA,_Hw,_HU,_HV,_HW,_HS)),_I0=E(_HZ.a),_I1=B(_En(_il,_I0.a,_I0.b,_I0.c,_HZ.b,_Hy,_Hz,_HA,_Hw)),_I2=E(_I1.a),_I3=E(_HO.a)+E(_HO.b)+E(_HO.c)+E(_HN.b)+E(_I2.a)+E(_I2.b)+E(_I2.c)+E(_I1.b);if(!_I3){var _I4=B(A2(_Hb,_Hh,_));return new T2(0,new T2(1,_jC,new T(function(){return E(E(_I4).a);})),new T(function(){return E(E(_I4).b);}));}else{var _I5=new T(function(){return  -((B(_Ff(_iR,_HK.a,_HK.b,_HK.c,_HJ.b,_Hs,_Ht,_Hu,_Hq))-B(_Ff(_iR,_HY.a,_HY.b,_HY.c,_HX.b,_Hy,_Hz,_HA,_Hw))-E(_Hc))/_I3);}),_I6=function(_I7,_I8,_I9,_Ia,_){var _Ib=new T(function(){var _Ic=function(_Id,_Ie,_If,_Ig,_Ih){if(_Id>_Ho){return E(_Ih);}else{if(_Ho>_Ie){return E(_Ih);}else{var _Ii=function(_){var _Ij=newArr(_If,_hl),_Ik=_Ij,_Il=function(_Im,_){while(1){if(_Im!=_If){var _=_Ik[_Im]=_Ig[_Im],_In=_Im+1|0;_Im=_In;continue;}else{return E(_);}}},_=B(_Il(0,_)),_Io=_Ho-_Id|0;if(0>_Io){return new F(function(){return _GX(_Io,_If);});}else{if(_Io>=_If){return new F(function(){return _GX(_Io,_If);});}else{var _=_Ik[_Io]=new T(function(){var _Ip=E(_Ig[_Io]),_Iq=E(_Ip.e),_Ir=E(_Iq.a),_Is=B(_En(_il,_HU,_HV,_HW,_HS,_Hy,_Hz,_HA,_Hw)),_It=E(_Is.a),_Iu=E(_I5)*E(_Hd),_Iv=B(_En(_il,_It.a,_It.b,_It.c,_Is.b,_Iu,_Iu,_Iu,_Iu)),_Iw=E(_Iv.a),_Ix=B(_Ey(_il,_Ir.a,_Ir.b,_Ir.c,_Iq.b, -E(_Iw.a), -E(_Iw.b), -E(_Iw.c), -E(_Iv.b)));return {_:0,a:E(_Ip.a),b:E(_Ip.b),c:E(_Ip.c),d:E(_Ip.d),e:E(new T2(0,E(_Ix.a),E(_Ix.b))),f:E(_Ip.f),g:E(_Ip.g),h:_Ip.h,i:_Ip.i};});return new T4(0,E(_Id),E(_Ie),_If,_Ik);}}};return new F(function(){return _zH(_Ii);});}}};if(_I7>_Hn){return B(_Ic(_I7,_I8,_I9,_Ia,new T4(0,E(_I7),E(_I8),_I9,_Ia)));}else{if(_Hn>_I8){return B(_Ic(_I7,_I8,_I9,_Ia,new T4(0,E(_I7),E(_I8),_I9,_Ia)));}else{var _Iy=function(_){var _Iz=newArr(_I9,_hl),_IA=_Iz,_IB=function(_IC,_){while(1){if(_IC!=_I9){var _=_IA[_IC]=_Ia[_IC],_ID=_IC+1|0;_IC=_ID;continue;}else{return E(_);}}},_=B(_IB(0,_)),_IE=_Hn-_I7|0;if(0>_IE){return new F(function(){return _GS(_I9,_IE);});}else{if(_IE>=_I9){return new F(function(){return _GS(_I9,_IE);});}else{var _=_IA[_IE]=new T(function(){var _IF=E(_Ia[_IE]),_IG=E(_IF.e),_IH=E(_IG.a),_II=B(_En(_il,_HG,_HH,_HI,_HE,_Hs,_Ht,_Hu,_Hq)),_IJ=E(_II.a),_IK=E(_I5)*E(_Hd),_IL=B(_En(_il,_IJ.a,_IJ.b,_IJ.c,_II.b,_IK,_IK,_IK,_IK)),_IM=E(_IL.a),_IN=B(_Ey(_il,_IH.a,_IH.b,_IH.c,_IG.b,_IM.a,_IM.b,_IM.c,_IL.b));return {_:0,a:E(_IF.a),b:E(_IF.b),c:E(_IF.c),d:E(_IF.d),e:E(new T2(0,E(_IN.a),E(_IN.b))),f:E(_IF.f),g:E(_IF.g),h:_IF.h,i:_IF.i};});return new T4(0,E(_I7),E(_I8),_I9,_IA);}}},_IO=B(_zH(_Iy));return B(_Ic(E(_IO.a),E(_IO.b),_IO.c,_IO.d,_IO));}}});return new T2(0,_jC,_Ib);};if(!E(_Hm.f)){var _IP=B(_I6(_Hk,_Hl,_Hi,_Hj,_)),_IQ=B(A2(_Hb,new T(function(){return E(E(_IP).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IP).a);}),new T(function(){return E(E(_IQ).a);})),new T(function(){return E(E(_IQ).b);}));}else{if(E(_I5)<0){var _IR=B(A2(_Hb,_Hh,_));return new T2(0,new T2(1,_jC,new T(function(){return E(E(_IR).a);})),new T(function(){return E(E(_IR).b);}));}else{var _IS=B(_I6(_Hk,_Hl,_Hi,_Hj,_)),_IT=B(A2(_Hb,new T(function(){return E(E(_IS).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IS).a);}),new T(function(){return E(E(_IT).a);})),new T(function(){return E(E(_IT).b);}));}}}}}}}}}}}};return E(_Hf);}};return new F(function(){return _H7(_H5.a);});}},_IU=function(_,_IV){var _IW=new T(function(){return B(_H3(E(_IV).a));}),_IX=function(_IY){var _IZ=E(_IY);return (_IZ==1)?E(new T2(1,_IW,_o)):new T2(1,_IW,new T(function(){return B(_IX(_IZ-1|0));}));},_J0=B(_Ef(B(_IX(5)),new T(function(){return E(E(_IV).b);}),_)),_J1=new T(function(){return B(_Ce(_BN,_DB,_F6,new T(function(){return E(E(_J0).b);})));});return new T2(0,_jC,_J1);},_J2=function(_J3,_J4,_J5,_J6,_J7){var _J8=B(_7i(B(_7g(_J3))));return new F(function(){return A3(_6I,_J8,new T(function(){return B(A3(_7k,_J8,_J4,_J6));}),new T(function(){return B(A3(_7k,_J8,_J5,_J7));}));});},_J9=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));}),_Ja=new T6(0,_GE,_GF,_o,_J9,_GE,_GE),_Jb=new T(function(){return B(_GC(_Ja));}),_Jc=function(_){return new F(function(){return die(_Jb);});},_Jd=false,_Je=true,_Jf=function(_Jg){var _Jh=E(_Jg),_Ji=E(_Jh.b),_Jj=E(_Jh.e),_Jk=E(_Jj.a),_Jl=E(_Jh.g),_Jm=B(_lg(_iR,_Ji.a,_Ji.b,_Ji.c,_Jl.a,_Jl.b,_Jl.c));return {_:0,a:E(_Jh.a),b:E(_Ji),c:E(_Jh.c),d:E(_Jh.d),e:E(new T2(0,E(new T3(0,E(_Jk.a)+E(_Jm.a)*1.0e-2,E(_Jk.b)+E(_Jm.b)*1.0e-2,E(_Jk.c)+E(_Jm.c)*1.0e-2)),E(_Jj.b))),f:E(_Jh.f),g:E(_Jl),h:_Jh.h,i:_Jh.i};},_Jn=new T(function(){return eval("collide");}),_Jo=function(_Jp){var _Jq=E(_Jp);if(!_Jq._){return __Z;}else{return new F(function(){return _f(_Jq.a,new T(function(){return B(_Jo(_Jq.b));},1));});}},_Jr=0,_Js=new T3(0,E(_Jr),E(_Jr),E(_Jr)),_Jt=new T2(0,E(_Js),E(_Jr)),_Ju=new T2(0,_iR,_jq),_Jv=new T(function(){return B(_gS(_Ju));}),_Jw=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_Jx=new T6(0,_GE,_GF,_o,_Jw,_GE,_GE),_Jy=new T(function(){return B(_GC(_Jx));}),_Jz=function(_JA,_){var _JB=B(_Ce(_BN,_DB,_Jf,_JA)),_JC=E(_JB.a),_JD=E(_JB.b);if(_JC<=_JD){var _JE=function(_JF,_JG,_){if(_JF<=_JD){var _JH=E(_JG),_JI=function(_JJ,_JK,_JL,_JM,_JN,_){if(_JK>_JF){return new F(function(){return die(_Jy);});}else{if(_JF>_JL){return new F(function(){return die(_Jy);});}else{if(_JK>_JJ){return new F(function(){return _Jc(_);});}else{if(_JJ>_JL){return new F(function(){return _Jc(_);});}else{var _JO=_JF-_JK|0;if(0>_JO){return new F(function(){return _GX(_JO,_JM);});}else{if(_JO>=_JM){return new F(function(){return _GX(_JO,_JM);});}else{var _JP=E(_JN[_JO]),_JQ=_JJ-_JK|0;if(0>_JQ){return new F(function(){return _GX(_JQ,_JM);});}else{if(_JQ>=_JM){return new F(function(){return _GX(_JQ,_JM);});}else{var _JR=E(_JN[_JQ]),_JS=__app2(E(_Jn),B(_jD(new T2(1,new T2(0,_CE,_JP.h),new T2(1,new T2(0,_CD,_JP.i),_o)))),B(_jD(new T2(1,new T2(0,_CE,_JR.h),new T2(1,new T2(0,_CD,_JR.i),_o))))),_JT=__arr2lst(0,_JS),_JU=B(_Ea(_JT,_));if(_JJ!=_JD){var _JV=B(_JI(_JJ+1|0,_JK,_JL,_JM,_JN,_)),_JW=new T(function(){var _JX=new T(function(){return _JF!=_JJ;}),_JY=function(_JZ){var _K0=E(_JZ);if(!_K0._){return __Z;}else{var _K1=_K0.b,_K2=E(_K0.a),_K3=E(_K2.b),_K4=E(_K2.a),_K5=E(_K2.c),_K6=_K5.a,_K7=_K5.b,_K8=E(_K2.e),_K9=E(_K2.d),_Ka=_K9.a,_Kb=_K9.b,_Kc=E(_K2.f),_Kd=new T(function(){var _Ke=B(_kq(_iR,_Kc.a,_Kc.b,_Kc.c)),_Kf=Math.sqrt(B(_J2(_iR,_Ka,_Kb,_Ka,_Kb)));return new T3(0,_Kf*E(_Ke.a),_Kf*E(_Ke.b),_Kf*E(_Ke.c));}),_Kg=new T(function(){var _Kh=B(_kq(_iR,_K8.a,_K8.b,_K8.c)),_Ki=Math.sqrt(B(_J2(_iR,_K6,_K7,_K6,_K7)));return new T3(0,_Ki*E(_Kh.a),_Ki*E(_Kh.b),_Ki*E(_Kh.c));}),_Kj=new T(function(){var _Kk=B(A1(_Jv,_K3)),_Kl=B(_kq(_iR,_Kk.a,_Kk.b,_Kk.c));return new T3(0,E(_Kl.a),E(_Kl.b),E(_Kl.c));}),_Km=new T(function(){var _Kn=B(A1(_Jv,_K4)),_Ko=B(_kq(_iR,_Kn.a,_Kn.b,_Kn.c));return new T3(0,E(_Ko.a),E(_Ko.b),E(_Ko.c));}),_Kp=E(_K3.a)+ -E(_K4.a),_Kq=E(_K3.b)+ -E(_K4.b),_Kr=E(_K3.c)+ -E(_K4.c),_Ks=new T(function(){return Math.sqrt(B(_kg(_iR,_Kp,_Kq,_Kr,_Kp,_Kq,_Kr)));}),_Kt=new T(function(){var _Ku=1/E(_Ks);return new T3(0,_Kp*_Ku,_Kq*_Ku,_Kr*_Ku);});return (!E(_JX))?new T2(1,new T(function(){var _Kv=E(_Kt),_Kw=E(_Kv.b),_Kx=E(_Kv.c),_Ky=E(_Kv.a),_Kz=E(_Km),_KA=E(_Kz.c),_KB=E(_Kz.b),_KC=E(_Kz.a),_KD=E(_Kg),_KE=E(_KD.c),_KF=E(_KD.b),_KG=E(_KD.a),_KH=_Kw*_KA-_KB*_Kx,_KI=_Kx*_KC-_KA*_Ky,_KJ=_Ky*_KB-_KC*_Kw,_KK=B(_kg(_iR,_KI*_KE-_KF*_KJ,_KJ*_KG-_KE*_KH,_KH*_KF-_KG*_KI,_KC,_KB,_KA));return new T6(0,_JF,_JJ,E(new T2(0,E(new T3(0,E(_KH),E(_KI),E(_KJ))),E(_KK))),E(_Jt),_Ks,_Jd);}),new T2(1,new T(function(){var _KL=E(_Kt),_KM=E(_KL.b),_KN=E(_KL.c),_KO=E(_KL.a),_KP=E(_Kj),_KQ=E(_KP.c),_KR=E(_KP.b),_KS=E(_KP.a),_KT=E(_Kd),_KU=E(_KT.c),_KV=E(_KT.b),_KW=E(_KT.a),_KX=_KM*_KQ-_KR*_KN,_KY=_KN*_KS-_KQ*_KO,_KZ=_KO*_KR-_KS*_KM,_L0=B(_kg(_iR,_KY*_KU-_KV*_KZ,_KZ*_KW-_KU*_KX,_KX*_KV-_KW*_KY,_KS,_KR,_KQ));return new T6(0,_JF,_JJ,E(_Jt),E(new T2(0,E(new T3(0,E(_KX),E(_KY),E(_KZ))),E(_L0))),_Ks,_Jd);}),new T(function(){return B(_JY(_K1));}))):new T2(1,new T(function(){var _L1=E(_Kt),_L2=E(_L1.b),_L3=E(_L1.c),_L4=E(_L1.a),_L5=E(_Km),_L6=_L5.a,_L7=_L5.b,_L8=_L5.c,_L9=B(_lg(_iR,_L4,_L2,_L3,_L6,_L7,_L8)),_La=E(_Kg),_Lb=E(_La.c),_Lc=E(_La.b),_Ld=E(_La.a),_Le=B(_kg(_iR,_L2*_Lb-_Lc*_L3,_L3*_Ld-_Lb*_L4,_L4*_Lc-_Ld*_L2,_L6,_L7,_L8)),_Lf=E(_Kj),_Lg=_Lf.a,_Lh=_Lf.b,_Li=_Lf.c,_Lj=B(_lg(_iR,_L4,_L2,_L3,_Lg,_Lh,_Li)),_Lk=E(_Kd),_Ll=E(_Lk.c),_Lm=E(_Lk.b),_Ln=E(_Lk.a),_Lo=B(_kg(_iR,_L2*_Ll-_Lm*_L3,_L3*_Ln-_Ll*_L4,_L4*_Lm-_Ln*_L2,_Lg,_Lh,_Li));return new T6(0,_JF,_JJ,E(new T2(0,E(new T3(0,E(_L9.a),E(_L9.b),E(_L9.c))),E(_Le))),E(new T2(0,E(new T3(0,E(_Lj.a),E(_Lj.b),E(_Lj.c))),E(_Lo))),_Ks,_Je);}),new T(function(){return B(_JY(_K1));}));}};return B(_JY(_JU));});return new T2(0,new T2(1,_JW,new T(function(){return E(E(_JV).a);})),new T(function(){return E(E(_JV).b);}));}else{var _Lp=new T(function(){var _Lq=new T(function(){return _JF!=_JJ;}),_Lr=function(_Ls){var _Lt=E(_Ls);if(!_Lt._){return __Z;}else{var _Lu=_Lt.b,_Lv=E(_Lt.a),_Lw=E(_Lv.b),_Lx=E(_Lv.a),_Ly=E(_Lv.c),_Lz=_Ly.a,_LA=_Ly.b,_LB=E(_Lv.e),_LC=E(_Lv.d),_LD=_LC.a,_LE=_LC.b,_LF=E(_Lv.f),_LG=new T(function(){var _LH=B(_kq(_iR,_LF.a,_LF.b,_LF.c)),_LI=Math.sqrt(B(_J2(_iR,_LD,_LE,_LD,_LE)));return new T3(0,_LI*E(_LH.a),_LI*E(_LH.b),_LI*E(_LH.c));}),_LJ=new T(function(){var _LK=B(_kq(_iR,_LB.a,_LB.b,_LB.c)),_LL=Math.sqrt(B(_J2(_iR,_Lz,_LA,_Lz,_LA)));return new T3(0,_LL*E(_LK.a),_LL*E(_LK.b),_LL*E(_LK.c));}),_LM=new T(function(){var _LN=B(A1(_Jv,_Lw)),_LO=B(_kq(_iR,_LN.a,_LN.b,_LN.c));return new T3(0,E(_LO.a),E(_LO.b),E(_LO.c));}),_LP=new T(function(){var _LQ=B(A1(_Jv,_Lx)),_LR=B(_kq(_iR,_LQ.a,_LQ.b,_LQ.c));return new T3(0,E(_LR.a),E(_LR.b),E(_LR.c));}),_LS=E(_Lw.a)+ -E(_Lx.a),_LT=E(_Lw.b)+ -E(_Lx.b),_LU=E(_Lw.c)+ -E(_Lx.c),_LV=new T(function(){return Math.sqrt(B(_kg(_iR,_LS,_LT,_LU,_LS,_LT,_LU)));}),_LW=new T(function(){var _LX=1/E(_LV);return new T3(0,_LS*_LX,_LT*_LX,_LU*_LX);});return (!E(_Lq))?new T2(1,new T(function(){var _LY=E(_LW),_LZ=E(_LY.b),_M0=E(_LY.c),_M1=E(_LY.a),_M2=E(_LP),_M3=E(_M2.c),_M4=E(_M2.b),_M5=E(_M2.a),_M6=E(_LJ),_M7=E(_M6.c),_M8=E(_M6.b),_M9=E(_M6.a),_Ma=_LZ*_M3-_M4*_M0,_Mb=_M0*_M5-_M3*_M1,_Mc=_M1*_M4-_M5*_LZ,_Md=B(_kg(_iR,_Mb*_M7-_M8*_Mc,_Mc*_M9-_M7*_Ma,_Ma*_M8-_M9*_Mb,_M5,_M4,_M3));return new T6(0,_JF,_JJ,E(new T2(0,E(new T3(0,E(_Ma),E(_Mb),E(_Mc))),E(_Md))),E(_Jt),_LV,_Jd);}),new T2(1,new T(function(){var _Me=E(_LW),_Mf=E(_Me.b),_Mg=E(_Me.c),_Mh=E(_Me.a),_Mi=E(_LM),_Mj=E(_Mi.c),_Mk=E(_Mi.b),_Ml=E(_Mi.a),_Mm=E(_LG),_Mn=E(_Mm.c),_Mo=E(_Mm.b),_Mp=E(_Mm.a),_Mq=_Mf*_Mj-_Mk*_Mg,_Mr=_Mg*_Ml-_Mj*_Mh,_Ms=_Mh*_Mk-_Ml*_Mf,_Mt=B(_kg(_iR,_Mr*_Mn-_Mo*_Ms,_Ms*_Mp-_Mn*_Mq,_Mq*_Mo-_Mp*_Mr,_Ml,_Mk,_Mj));return new T6(0,_JF,_JJ,E(_Jt),E(new T2(0,E(new T3(0,E(_Mq),E(_Mr),E(_Ms))),E(_Mt))),_LV,_Jd);}),new T(function(){return B(_Lr(_Lu));}))):new T2(1,new T(function(){var _Mu=E(_LW),_Mv=E(_Mu.b),_Mw=E(_Mu.c),_Mx=E(_Mu.a),_My=E(_LP),_Mz=_My.a,_MA=_My.b,_MB=_My.c,_MC=B(_lg(_iR,_Mx,_Mv,_Mw,_Mz,_MA,_MB)),_MD=E(_LJ),_ME=E(_MD.c),_MF=E(_MD.b),_MG=E(_MD.a),_MH=B(_kg(_iR,_Mv*_ME-_MF*_Mw,_Mw*_MG-_ME*_Mx,_Mx*_MF-_MG*_Mv,_Mz,_MA,_MB)),_MI=E(_LM),_MJ=_MI.a,_MK=_MI.b,_ML=_MI.c,_MM=B(_lg(_iR,_Mx,_Mv,_Mw,_MJ,_MK,_ML)),_MN=E(_LG),_MO=E(_MN.c),_MP=E(_MN.b),_MQ=E(_MN.a),_MR=B(_kg(_iR,_Mv*_MO-_MP*_Mw,_Mw*_MQ-_MO*_Mx,_Mx*_MP-_MQ*_Mv,_MJ,_MK,_ML));return new T6(0,_JF,_JJ,E(new T2(0,E(new T3(0,E(_MC.a),E(_MC.b),E(_MC.c))),E(_MH))),E(new T2(0,E(new T3(0,E(_MM.a),E(_MM.b),E(_MM.c))),E(_MR))),_LV,_Je);}),new T(function(){return B(_Lr(_Lu));}));}};return B(_Lr(_JU));});return new T2(0,new T2(1,_Lp,_o),new T4(0,E(_JK),E(_JL),_JM,_JN));}}}}}}}}}},_MS=B(_JI(_JF,E(_JH.a),E(_JH.b),_JH.c,_JH.d,_));if(_JF!=_JD){var _MT=B(_JE(_JF+1|0,new T(function(){return E(E(_MS).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Jo(E(_MS).a));}),new T(function(){return E(E(_MT).a);})),new T(function(){return E(E(_MT).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Jo(E(_MS).a));}),_o),new T(function(){return E(E(_MS).b);}));}}else{if(_JF!=_JD){var _MU=B(_JE(_JF+1|0,_JG,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_MU).a);})),new T(function(){return E(E(_MU).b);}));}else{return new T2(0,new T2(1,_o,_o),_JG);}}},_MV=function(_MW,_MX,_MY,_MZ,_N0,_){if(_MW<=_JD){var _N1=function(_N2,_N3,_N4,_N5,_N6,_){if(_N3>_MW){return new F(function(){return die(_Jy);});}else{if(_MW>_N4){return new F(function(){return die(_Jy);});}else{if(_N3>_N2){return new F(function(){return _Jc(_);});}else{if(_N2>_N4){return new F(function(){return _Jc(_);});}else{var _N7=_MW-_N3|0;if(0>_N7){return new F(function(){return _GX(_N7,_N5);});}else{if(_N7>=_N5){return new F(function(){return _GX(_N7,_N5);});}else{var _N8=E(_N6[_N7]),_N9=_N2-_N3|0;if(0>_N9){return new F(function(){return _GX(_N9,_N5);});}else{if(_N9>=_N5){return new F(function(){return _GX(_N9,_N5);});}else{var _Na=E(_N6[_N9]),_Nb=__app2(E(_Jn),B(_jD(new T2(1,new T2(0,_CE,_N8.h),new T2(1,new T2(0,_CD,_N8.i),_o)))),B(_jD(new T2(1,new T2(0,_CE,_Na.h),new T2(1,new T2(0,_CD,_Na.i),_o))))),_Nc=__arr2lst(0,_Nb),_Nd=B(_Ea(_Nc,_));if(_N2!=_JD){var _Ne=B(_N1(_N2+1|0,_N3,_N4,_N5,_N6,_)),_Nf=new T(function(){var _Ng=new T(function(){return _MW!=_N2;}),_Nh=function(_Ni){var _Nj=E(_Ni);if(!_Nj._){return __Z;}else{var _Nk=_Nj.b,_Nl=E(_Nj.a),_Nm=E(_Nl.b),_Nn=E(_Nl.a),_No=E(_Nl.c),_Np=_No.a,_Nq=_No.b,_Nr=E(_Nl.e),_Ns=E(_Nl.d),_Nt=_Ns.a,_Nu=_Ns.b,_Nv=E(_Nl.f),_Nw=new T(function(){var _Nx=B(_kq(_iR,_Nv.a,_Nv.b,_Nv.c)),_Ny=Math.sqrt(B(_J2(_iR,_Nt,_Nu,_Nt,_Nu)));return new T3(0,_Ny*E(_Nx.a),_Ny*E(_Nx.b),_Ny*E(_Nx.c));}),_Nz=new T(function(){var _NA=B(_kq(_iR,_Nr.a,_Nr.b,_Nr.c)),_NB=Math.sqrt(B(_J2(_iR,_Np,_Nq,_Np,_Nq)));return new T3(0,_NB*E(_NA.a),_NB*E(_NA.b),_NB*E(_NA.c));}),_NC=new T(function(){var _ND=B(A1(_Jv,_Nm)),_NE=B(_kq(_iR,_ND.a,_ND.b,_ND.c));return new T3(0,E(_NE.a),E(_NE.b),E(_NE.c));}),_NF=new T(function(){var _NG=B(A1(_Jv,_Nn)),_NH=B(_kq(_iR,_NG.a,_NG.b,_NG.c));return new T3(0,E(_NH.a),E(_NH.b),E(_NH.c));}),_NI=E(_Nm.a)+ -E(_Nn.a),_NJ=E(_Nm.b)+ -E(_Nn.b),_NK=E(_Nm.c)+ -E(_Nn.c),_NL=new T(function(){return Math.sqrt(B(_kg(_iR,_NI,_NJ,_NK,_NI,_NJ,_NK)));}),_NM=new T(function(){var _NN=1/E(_NL);return new T3(0,_NI*_NN,_NJ*_NN,_NK*_NN);});return (!E(_Ng))?new T2(1,new T(function(){var _NO=E(_NM),_NP=E(_NO.b),_NQ=E(_NO.c),_NR=E(_NO.a),_NS=E(_NF),_NT=E(_NS.c),_NU=E(_NS.b),_NV=E(_NS.a),_NW=E(_Nz),_NX=E(_NW.c),_NY=E(_NW.b),_NZ=E(_NW.a),_O0=_NP*_NT-_NU*_NQ,_O1=_NQ*_NV-_NT*_NR,_O2=_NR*_NU-_NV*_NP,_O3=B(_kg(_iR,_O1*_NX-_NY*_O2,_O2*_NZ-_NX*_O0,_O0*_NY-_NZ*_O1,_NV,_NU,_NT));return new T6(0,_MW,_N2,E(new T2(0,E(new T3(0,E(_O0),E(_O1),E(_O2))),E(_O3))),E(_Jt),_NL,_Jd);}),new T2(1,new T(function(){var _O4=E(_NM),_O5=E(_O4.b),_O6=E(_O4.c),_O7=E(_O4.a),_O8=E(_NC),_O9=E(_O8.c),_Oa=E(_O8.b),_Ob=E(_O8.a),_Oc=E(_Nw),_Od=E(_Oc.c),_Oe=E(_Oc.b),_Of=E(_Oc.a),_Og=_O5*_O9-_Oa*_O6,_Oh=_O6*_Ob-_O9*_O7,_Oi=_O7*_Oa-_Ob*_O5,_Oj=B(_kg(_iR,_Oh*_Od-_Oe*_Oi,_Oi*_Of-_Od*_Og,_Og*_Oe-_Of*_Oh,_Ob,_Oa,_O9));return new T6(0,_MW,_N2,E(_Jt),E(new T2(0,E(new T3(0,E(_Og),E(_Oh),E(_Oi))),E(_Oj))),_NL,_Jd);}),new T(function(){return B(_Nh(_Nk));}))):new T2(1,new T(function(){var _Ok=E(_NM),_Ol=E(_Ok.b),_Om=E(_Ok.c),_On=E(_Ok.a),_Oo=E(_NF),_Op=_Oo.a,_Oq=_Oo.b,_Or=_Oo.c,_Os=B(_lg(_iR,_On,_Ol,_Om,_Op,_Oq,_Or)),_Ot=E(_Nz),_Ou=E(_Ot.c),_Ov=E(_Ot.b),_Ow=E(_Ot.a),_Ox=B(_kg(_iR,_Ol*_Ou-_Ov*_Om,_Om*_Ow-_Ou*_On,_On*_Ov-_Ow*_Ol,_Op,_Oq,_Or)),_Oy=E(_NC),_Oz=_Oy.a,_OA=_Oy.b,_OB=_Oy.c,_OC=B(_lg(_iR,_On,_Ol,_Om,_Oz,_OA,_OB)),_OD=E(_Nw),_OE=E(_OD.c),_OF=E(_OD.b),_OG=E(_OD.a),_OH=B(_kg(_iR,_Ol*_OE-_OF*_Om,_Om*_OG-_OE*_On,_On*_OF-_OG*_Ol,_Oz,_OA,_OB));return new T6(0,_MW,_N2,E(new T2(0,E(new T3(0,E(_Os.a),E(_Os.b),E(_Os.c))),E(_Ox))),E(new T2(0,E(new T3(0,E(_OC.a),E(_OC.b),E(_OC.c))),E(_OH))),_NL,_Je);}),new T(function(){return B(_Nh(_Nk));}));}};return B(_Nh(_Nd));});return new T2(0,new T2(1,_Nf,new T(function(){return E(E(_Ne).a);})),new T(function(){return E(E(_Ne).b);}));}else{var _OI=new T(function(){var _OJ=new T(function(){return _MW!=_N2;}),_OK=function(_OL){var _OM=E(_OL);if(!_OM._){return __Z;}else{var _ON=_OM.b,_OO=E(_OM.a),_OP=E(_OO.b),_OQ=E(_OO.a),_OR=E(_OO.c),_OS=_OR.a,_OT=_OR.b,_OU=E(_OO.e),_OV=E(_OO.d),_OW=_OV.a,_OX=_OV.b,_OY=E(_OO.f),_OZ=new T(function(){var _P0=B(_kq(_iR,_OY.a,_OY.b,_OY.c)),_P1=Math.sqrt(B(_J2(_iR,_OW,_OX,_OW,_OX)));return new T3(0,_P1*E(_P0.a),_P1*E(_P0.b),_P1*E(_P0.c));}),_P2=new T(function(){var _P3=B(_kq(_iR,_OU.a,_OU.b,_OU.c)),_P4=Math.sqrt(B(_J2(_iR,_OS,_OT,_OS,_OT)));return new T3(0,_P4*E(_P3.a),_P4*E(_P3.b),_P4*E(_P3.c));}),_P5=new T(function(){var _P6=B(A1(_Jv,_OP)),_P7=B(_kq(_iR,_P6.a,_P6.b,_P6.c));return new T3(0,E(_P7.a),E(_P7.b),E(_P7.c));}),_P8=new T(function(){var _P9=B(A1(_Jv,_OQ)),_Pa=B(_kq(_iR,_P9.a,_P9.b,_P9.c));return new T3(0,E(_Pa.a),E(_Pa.b),E(_Pa.c));}),_Pb=E(_OP.a)+ -E(_OQ.a),_Pc=E(_OP.b)+ -E(_OQ.b),_Pd=E(_OP.c)+ -E(_OQ.c),_Pe=new T(function(){return Math.sqrt(B(_kg(_iR,_Pb,_Pc,_Pd,_Pb,_Pc,_Pd)));}),_Pf=new T(function(){var _Pg=1/E(_Pe);return new T3(0,_Pb*_Pg,_Pc*_Pg,_Pd*_Pg);});return (!E(_OJ))?new T2(1,new T(function(){var _Ph=E(_Pf),_Pi=E(_Ph.b),_Pj=E(_Ph.c),_Pk=E(_Ph.a),_Pl=E(_P8),_Pm=E(_Pl.c),_Pn=E(_Pl.b),_Po=E(_Pl.a),_Pp=E(_P2),_Pq=E(_Pp.c),_Pr=E(_Pp.b),_Ps=E(_Pp.a),_Pt=_Pi*_Pm-_Pn*_Pj,_Pu=_Pj*_Po-_Pm*_Pk,_Pv=_Pk*_Pn-_Po*_Pi,_Pw=B(_kg(_iR,_Pu*_Pq-_Pr*_Pv,_Pv*_Ps-_Pq*_Pt,_Pt*_Pr-_Ps*_Pu,_Po,_Pn,_Pm));return new T6(0,_MW,_N2,E(new T2(0,E(new T3(0,E(_Pt),E(_Pu),E(_Pv))),E(_Pw))),E(_Jt),_Pe,_Jd);}),new T2(1,new T(function(){var _Px=E(_Pf),_Py=E(_Px.b),_Pz=E(_Px.c),_PA=E(_Px.a),_PB=E(_P5),_PC=E(_PB.c),_PD=E(_PB.b),_PE=E(_PB.a),_PF=E(_OZ),_PG=E(_PF.c),_PH=E(_PF.b),_PI=E(_PF.a),_PJ=_Py*_PC-_PD*_Pz,_PK=_Pz*_PE-_PC*_PA,_PL=_PA*_PD-_PE*_Py,_PM=B(_kg(_iR,_PK*_PG-_PH*_PL,_PL*_PI-_PG*_PJ,_PJ*_PH-_PI*_PK,_PE,_PD,_PC));return new T6(0,_MW,_N2,E(_Jt),E(new T2(0,E(new T3(0,E(_PJ),E(_PK),E(_PL))),E(_PM))),_Pe,_Jd);}),new T(function(){return B(_OK(_ON));}))):new T2(1,new T(function(){var _PN=E(_Pf),_PO=E(_PN.b),_PP=E(_PN.c),_PQ=E(_PN.a),_PR=E(_P8),_PS=_PR.a,_PT=_PR.b,_PU=_PR.c,_PV=B(_lg(_iR,_PQ,_PO,_PP,_PS,_PT,_PU)),_PW=E(_P2),_PX=E(_PW.c),_PY=E(_PW.b),_PZ=E(_PW.a),_Q0=B(_kg(_iR,_PO*_PX-_PY*_PP,_PP*_PZ-_PX*_PQ,_PQ*_PY-_PZ*_PO,_PS,_PT,_PU)),_Q1=E(_P5),_Q2=_Q1.a,_Q3=_Q1.b,_Q4=_Q1.c,_Q5=B(_lg(_iR,_PQ,_PO,_PP,_Q2,_Q3,_Q4)),_Q6=E(_OZ),_Q7=E(_Q6.c),_Q8=E(_Q6.b),_Q9=E(_Q6.a),_Qa=B(_kg(_iR,_PO*_Q7-_Q8*_PP,_PP*_Q9-_Q7*_PQ,_PQ*_Q8-_Q9*_PO,_Q2,_Q3,_Q4));return new T6(0,_MW,_N2,E(new T2(0,E(new T3(0,E(_PV.a),E(_PV.b),E(_PV.c))),E(_Q0))),E(new T2(0,E(new T3(0,E(_Q5.a),E(_Q5.b),E(_Q5.c))),E(_Qa))),_Pe,_Je);}),new T(function(){return B(_OK(_ON));}));}};return B(_OK(_Nd));});return new T2(0,new T2(1,_OI,_o),new T4(0,E(_N3),E(_N4),_N5,_N6));}}}}}}}}}},_Qb=B(_N1(_MW,_MX,_MY,_MZ,_N0,_));if(_MW!=_JD){var _Qc=B(_JE(_MW+1|0,new T(function(){return E(E(_Qb).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Jo(E(_Qb).a));}),new T(function(){return E(E(_Qc).a);})),new T(function(){return E(E(_Qc).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Jo(E(_Qb).a));}),_o),new T(function(){return E(E(_Qb).b);}));}}else{if(_MW!=_JD){var _Qd=B(_MV(_MW+1|0,_MX,_MY,_MZ,_N0,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Qd).a);})),new T(function(){return E(E(_Qd).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_MX),E(_MY),_MZ,_N0));}}},_Qe=B(_MV(_JC,_JC,_JD,_JB.c,_JB.d,_));return new F(function(){return _IU(_,_Qe);});}else{return new F(function(){return _IU(_,new T2(0,_o,_JB));});}},_Qf=new T(function(){return eval("__strict(refresh)");}),_Qg=function(_Qh,_){var _Qi=__app0(E(_Qf)),_Qj=__app0(E(_Dk)),_Qk=B(A(_Ce,[_BN,_Aa,_Di,_Qh,_])),_Ql=B(_Jz(_Qh,_));return new T(function(){return E(E(_Ql).b);});},_Qm=function(_Qn,_){while(1){var _Qo=E(_Qn);if(!_Qo._){return _jC;}else{var _Qp=_Qo.b,_Qq=E(_Qo.a);switch(_Qq._){case 0:var _Qr=B(A1(_Qq.a,_));_Qn=B(_f(_Qp,new T2(1,_Qr,_o)));continue;case 1:_Qn=B(_f(_Qp,_Qq.a));continue;default:_Qn=_Qp;continue;}}}},_Qs=function(_Qt,_Qu,_){var _Qv=E(_Qt);switch(_Qv._){case 0:var _Qw=B(A1(_Qv.a,_));return new F(function(){return _Qm(B(_f(_Qu,new T2(1,_Qw,_o))),_);});break;case 1:return new F(function(){return _Qm(B(_f(_Qu,_Qv.a)),_);});break;default:return new F(function(){return _Qm(_Qu,_);});}},_Qx=new T0(2),_Qy=function(_Qz){return new T0(2);},_QA=function(_QB,_QC,_QD){return function(_){var _QE=E(_QB),_QF=rMV(_QE),_QG=E(_QF);if(!_QG._){var _QH=new T(function(){var _QI=new T(function(){return B(A1(_QD,_jC));});return B(_f(_QG.b,new T2(1,new T2(0,_QC,function(_QJ){return E(_QI);}),_o)));}),_=wMV(_QE,new T2(0,_QG.a,_QH));return _Qx;}else{var _QK=E(_QG.a);if(!_QK._){var _=wMV(_QE,new T2(0,_QC,_o));return new T(function(){return B(A1(_QD,_jC));});}else{var _=wMV(_QE,new T1(1,_QK.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QD,_jC));}),new T2(1,new T(function(){return B(A2(_QK.a,_QC,_Qy));}),_o)));}}};},_QL=new T(function(){return E(_pf);}),_QM=new T(function(){return eval("window.requestAnimationFrame");}),_QN=new T1(1,_o),_QO=function(_QP,_QQ){return function(_){var _QR=E(_QP),_QS=rMV(_QR),_QT=E(_QS);if(!_QT._){var _QU=_QT.a,_QV=E(_QT.b);if(!_QV._){var _=wMV(_QR,_QN);return new T(function(){return B(A1(_QQ,_QU));});}else{var _QW=E(_QV.a),_=wMV(_QR,new T2(0,_QW.a,_QV.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QQ,_QU));}),new T2(1,new T(function(){return B(A1(_QW.b,_Qy));}),_o)));}}else{var _QX=new T(function(){var _QY=function(_QZ){var _R0=new T(function(){return B(A1(_QQ,_QZ));});return function(_R1){return E(_R0);};};return B(_f(_QT.a,new T2(1,_QY,_o)));}),_=wMV(_QR,new T1(1,_QX));return _Qx;}};},_R2=function(_R3,_R4){return new T1(0,B(_QO(_R3,_R4)));},_R5=function(_R6,_R7){var _R8=new T(function(){return new T1(0,B(_QA(_R6,_jC,_Qy)));});return function(_){var _R9=__createJSFunc(2,function(_Ra,_){var _Rb=B(_Qs(_R8,_o,_));return _QL;}),_Rc=__app1(E(_QM),_R9);return new T(function(){return B(_R2(_R6,_R7));});};},_Rd=new T1(1,_o),_Re=function(_Rf,_Rg,_){var _Rh=function(_){var _Ri=nMV(_Rf),_Rj=_Ri;return new T(function(){var _Rk=new T(function(){return B(_Rl(_));}),_Rm=function(_){var _Rn=rMV(_Rj),_Ro=B(A2(_Rg,_Rn,_)),_=wMV(_Rj,_Ro),_Rp=function(_){var _Rq=nMV(_Rd);return new T(function(){return new T1(0,B(_R5(_Rq,function(_Rr){return E(_Rk);})));});};return new T1(0,_Rp);},_Rs=new T(function(){return new T1(0,_Rm);}),_Rl=function(_Rt){return E(_Rs);};return B(_Rl(_));});};return new F(function(){return _Qs(new T1(0,_Rh),_o,_);});},_Ru=function(_){var _Rv=__app2(E(_0),E(_7U),E(_he));return new F(function(){return _Re(_zK,_Qg,_);});},_Rw=function(_){return new F(function(){return _Ru(_);});};
var hasteMain = function() {B(A(_Rw, [0]));};window.onload = hasteMain;