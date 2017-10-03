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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x){return E(E(_8x).b);},_8y=function(_8z){return E(E(_8z).d);},_8A=new T1(0,2),_8B=new T2(0,E(_1o),E(_8A)),_8C=new T1(0,5),_8D=new T1(0,4),_8E=new T2(0,E(_8D),E(_8C)),_8F=function(_8G){return E(E(_8G).e);},_8H=function(_8I,_8J,_8K,_8L){var _8M=B(_8q(_8I)),_8N=B(_8s(_8M)),_8O=new T(function(){var _8P=new T(function(){var _8Q=new T(function(){var _8R=new T(function(){var _8S=new T(function(){var _8T=new T(function(){return B(A3(_86,_8N,new T(function(){return B(A3(_8u,_8N,_8J,_8J));}),new T(function(){return B(A3(_8u,_8N,_8L,_8L));})));});return B(A2(_8F,_8I,_8T));});return B(A3(_8w,_8N,_8S,new T(function(){return B(A2(_8y,_8M,_8E));})));});return B(A3(_8u,_8N,_8R,_8R));});return B(A3(_86,_8N,_8Q,new T(function(){return B(A3(_8u,_8N,_8K,_8K));})));});return B(A2(_8F,_8I,_8P));});return new F(function(){return A3(_8w,_8N,_8O,new T(function(){return B(A2(_8y,_8M,_8B));}));});},_8U=new T(function(){return B(unCStr("x"));}),_8V=new T1(0,_8U),_8W=new T(function(){return B(unCStr("y"));}),_8X=new T1(0,_8W),_8Y=new T(function(){return B(unCStr("z"));}),_8Z=new T1(0,_8Y),_90=new T(function(){return B(_8H(_8p,_8V,_8X,_8Z));}),_91=new T(function(){return toJSStr(B(_1v(_x,_1l,_90)));}),_92=new T3(0,E(_8V),E(_8X),E(_8Z)),_93=new T(function(){return B(unCStr("(/=) is not defined"));}),_94=new T(function(){return B(err(_93));}),_95=new T(function(){return B(unCStr("(==) is not defined"));}),_96=new T(function(){return B(err(_95));}),_97=new T2(0,_96,_94),_98=new T(function(){return B(unCStr("(<) is not defined"));}),_99=new T(function(){return B(err(_98));}),_9a=new T(function(){return B(unCStr("(<=) is not defined"));}),_9b=new T(function(){return B(err(_9a));}),_9c=new T(function(){return B(unCStr("(>) is not defined"));}),_9d=new T(function(){return B(err(_9c));}),_9e=new T(function(){return B(unCStr("(>=) is not defined"));}),_9f=new T(function(){return B(err(_9e));}),_9g=new T(function(){return B(unCStr("compare is not defined"));}),_9h=new T(function(){return B(err(_9g));}),_9i=new T(function(){return B(unCStr("max("));}),_9j=new T1(0,_9i),_9k=function(_9l,_9m){return new T1(1,new T2(1,_9j,new T2(1,_9l,new T2(1,_22,new T2(1,_9m,_1S)))));},_9n=new T(function(){return B(unCStr("min("));}),_9o=new T1(0,_9n),_9p=function(_9q,_9r){return new T1(1,new T2(1,_9o,new T2(1,_9q,new T2(1,_22,new T2(1,_9r,_1S)))));},_9s={_:0,a:_97,b:_9h,c:_99,d:_9b,e:_9d,f:_9f,g:_9k,h:_9p},_9t=new T2(0,_8p,_9s),_9u=function(_9v,_9w){var _9x=E(_9v);return E(_9w);},_9y=function(_9z,_9A){var _9B=E(_9A);return E(_9z);},_9C=function(_9D,_9E){var _9F=E(_9D),_9G=E(_9E);return new T3(0,E(B(A1(_9F.a,_9G.a))),E(B(A1(_9F.b,_9G.b))),E(B(A1(_9F.c,_9G.c))));},_9H=function(_9I,_9J,_9K){return new T3(0,E(_9I),E(_9J),E(_9K));},_9L=function(_9M){return new F(function(){return _9H(_9M,_9M,_9M);});},_9N=function(_9O,_9P){var _9Q=E(_9P),_9R=E(_9O);return new T3(0,E(_9R),E(_9R),E(_9R));},_9S=function(_9T,_9U){var _9V=E(_9U);return new T3(0,E(B(A1(_9T,_9V.a))),E(B(A1(_9T,_9V.b))),E(B(A1(_9T,_9V.c))));},_9W=new T2(0,_9S,_9N),_9X=new T5(0,_9W,_9L,_9C,_9u,_9y),_9Y=new T1(0,0),_9Z=function(_a0){return E(E(_a0).g);},_a1=function(_a2){var _a3=B(A2(_9Z,_a2,_1o)),_a4=B(A2(_9Z,_a2,_9Y));return new T3(0,E(new T3(0,E(_a3),E(_a4),E(_a4))),E(new T3(0,E(_a4),E(_a3),E(_a4))),E(new T3(0,E(_a4),E(_a4),E(_a3))));},_a5=function(_a6){return E(E(_a6).a);},_a7=function(_a8){return E(E(_a8).f);},_a9=function(_aa){return E(E(_aa).b);},_ab=function(_ac){return E(E(_ac).c);},_ad=function(_ae){return E(E(_ae).a);},_af=function(_ag){return E(E(_ag).d);},_ah=function(_ai,_aj,_ak,_al,_am){var _an=new T(function(){return E(E(E(_ai).c).a);}),_ao=new T(function(){var _ap=E(_ai).a,_aq=new T(function(){var _ar=new T(function(){return B(_8q(_an));}),_as=new T(function(){return B(_8s(_ar));}),_at=new T(function(){return B(A2(_af,_an,_aj));}),_au=new T(function(){return B(A3(_a7,_an,_aj,_al));}),_av=function(_aw,_ax){var _ay=new T(function(){var _az=new T(function(){return B(A3(_a9,_ar,new T(function(){return B(A3(_8u,_as,_al,_aw));}),_aj));});return B(A3(_86,_as,_az,new T(function(){return B(A3(_8u,_as,_ax,_at));})));});return new F(function(){return A3(_8u,_as,_au,_ay);});};return B(A3(_ad,B(_a5(_ap)),_av,_ak));});return B(A3(_ab,_ap,_aq,_am));});return new T2(0,new T(function(){return B(A3(_a7,_an,_aj,_al));}),_ao);},_aA=function(_aB,_aC,_aD,_aE){var _aF=E(_aD),_aG=E(_aE),_aH=B(_ah(_aC,_aF.a,_aF.b,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=new T1(0,1),_aJ=function(_aK){return E(E(_aK).l);},_aL=function(_aM,_aN,_aO){var _aP=new T(function(){return E(E(E(_aM).c).a);}),_aQ=new T(function(){var _aR=new T(function(){return B(_8q(_aP));}),_aS=new T(function(){var _aT=B(_8s(_aR)),_aU=new T(function(){var _aV=new T(function(){return B(A3(_8w,_aT,new T(function(){return B(A2(_9Z,_aT,_aI));}),new T(function(){return B(A3(_8u,_aT,_aN,_aN));})));});return B(A2(_8F,_aP,_aV));});return B(A2(_88,_aT,_aU));});return B(A3(_ad,B(_a5(E(_aM).a)),function(_aW){return new F(function(){return A3(_a9,_aR,_aW,_aS);});},_aO));});return new T2(0,new T(function(){return B(A2(_aJ,_aP,_aN));}),_aQ);},_aX=function(_aY,_aZ,_b0){var _b1=E(_b0),_b2=B(_aL(_aZ,_b1.a,_b1.b));return new T2(0,_b2.a,_b2.b);},_b3=function(_b4){return E(E(_b4).r);},_b5=function(_b6,_b7,_b8){var _b9=new T(function(){return E(E(E(_b6).c).a);}),_ba=new T(function(){var _bb=new T(function(){return B(_8q(_b9));}),_bc=new T(function(){var _bd=new T(function(){var _be=B(_8s(_bb));return B(A3(_8w,_be,new T(function(){return B(A3(_8u,_be,_b7,_b7));}),new T(function(){return B(A2(_9Z,_be,_aI));})));});return B(A2(_8F,_b9,_bd));});return B(A3(_ad,B(_a5(E(_b6).a)),function(_bf){return new F(function(){return A3(_a9,_bb,_bf,_bc);});},_b8));});return new T2(0,new T(function(){return B(A2(_b3,_b9,_b7));}),_ba);},_bg=function(_bh,_bi,_bj){var _bk=E(_bj),_bl=B(_b5(_bi,_bk.a,_bk.b));return new T2(0,_bl.a,_bl.b);},_bm=function(_bn){return E(E(_bn).k);},_bo=function(_bp,_bq,_br){var _bs=new T(function(){return E(E(E(_bp).c).a);}),_bt=new T(function(){var _bu=new T(function(){return B(_8q(_bs));}),_bv=new T(function(){var _bw=new T(function(){var _bx=B(_8s(_bu));return B(A3(_8w,_bx,new T(function(){return B(A2(_9Z,_bx,_aI));}),new T(function(){return B(A3(_8u,_bx,_bq,_bq));})));});return B(A2(_8F,_bs,_bw));});return B(A3(_ad,B(_a5(E(_bp).a)),function(_by){return new F(function(){return A3(_a9,_bu,_by,_bv);});},_br));});return new T2(0,new T(function(){return B(A2(_bm,_bs,_bq));}),_bt);},_bz=function(_bA,_bB,_bC){var _bD=E(_bC),_bE=B(_bo(_bB,_bD.a,_bD.b));return new T2(0,_bE.a,_bE.b);},_bF=function(_bG){return E(E(_bG).q);},_bH=function(_bI,_bJ,_bK){var _bL=new T(function(){return E(E(E(_bI).c).a);}),_bM=new T(function(){var _bN=new T(function(){return B(_8q(_bL));}),_bO=new T(function(){var _bP=new T(function(){var _bQ=B(_8s(_bN));return B(A3(_86,_bQ,new T(function(){return B(A3(_8u,_bQ,_bJ,_bJ));}),new T(function(){return B(A2(_9Z,_bQ,_aI));})));});return B(A2(_8F,_bL,_bP));});return B(A3(_ad,B(_a5(E(_bI).a)),function(_bR){return new F(function(){return A3(_a9,_bN,_bR,_bO);});},_bK));});return new T2(0,new T(function(){return B(A2(_bF,_bL,_bJ));}),_bM);},_bS=function(_bT,_bU,_bV){var _bW=E(_bV),_bX=B(_bH(_bU,_bW.a,_bW.b));return new T2(0,_bX.a,_bX.b);},_bY=function(_bZ){return E(E(_bZ).m);},_c0=function(_c1,_c2,_c3){var _c4=new T(function(){return E(E(E(_c1).c).a);}),_c5=new T(function(){var _c6=new T(function(){return B(_8q(_c4));}),_c7=new T(function(){var _c8=B(_8s(_c6));return B(A3(_86,_c8,new T(function(){return B(A2(_9Z,_c8,_aI));}),new T(function(){return B(A3(_8u,_c8,_c2,_c2));})));});return B(A3(_ad,B(_a5(E(_c1).a)),function(_c9){return new F(function(){return A3(_a9,_c6,_c9,_c7);});},_c3));});return new T2(0,new T(function(){return B(A2(_bY,_c4,_c2));}),_c5);},_ca=function(_cb,_cc,_cd){var _ce=E(_cd),_cf=B(_c0(_cc,_ce.a,_ce.b));return new T2(0,_cf.a,_cf.b);},_cg=function(_ch){return E(E(_ch).s);},_ci=function(_cj,_ck,_cl){var _cm=new T(function(){return E(E(E(_cj).c).a);}),_cn=new T(function(){var _co=new T(function(){return B(_8q(_cm));}),_cp=new T(function(){var _cq=B(_8s(_co));return B(A3(_8w,_cq,new T(function(){return B(A2(_9Z,_cq,_aI));}),new T(function(){return B(A3(_8u,_cq,_ck,_ck));})));});return B(A3(_ad,B(_a5(E(_cj).a)),function(_cr){return new F(function(){return A3(_a9,_co,_cr,_cp);});},_cl));});return new T2(0,new T(function(){return B(A2(_cg,_cm,_ck));}),_cn);},_cs=function(_ct,_cu,_cv){var _cw=E(_cv),_cx=B(_ci(_cu,_cw.a,_cw.b));return new T2(0,_cx.a,_cx.b);},_cy=function(_cz){return E(E(_cz).i);},_cA=function(_cB){return E(E(_cB).h);},_cC=function(_cD,_cE,_cF){var _cG=new T(function(){return E(E(E(_cD).c).a);}),_cH=new T(function(){var _cI=new T(function(){return B(_8s(new T(function(){return B(_8q(_cG));})));}),_cJ=new T(function(){return B(A2(_88,_cI,new T(function(){return B(A2(_cA,_cG,_cE));})));});return B(A3(_ad,B(_a5(E(_cD).a)),function(_cK){return new F(function(){return A3(_8u,_cI,_cK,_cJ);});},_cF));});return new T2(0,new T(function(){return B(A2(_cy,_cG,_cE));}),_cH);},_cL=function(_cM,_cN,_cO){var _cP=E(_cO),_cQ=B(_cC(_cN,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);},_cR=function(_cS){return E(E(_cS).o);},_cT=function(_cU){return E(E(_cU).n);},_cV=function(_cW,_cX,_cY){var _cZ=new T(function(){return E(E(E(_cW).c).a);}),_d0=new T(function(){var _d1=new T(function(){return B(_8s(new T(function(){return B(_8q(_cZ));})));}),_d2=new T(function(){return B(A2(_cT,_cZ,_cX));});return B(A3(_ad,B(_a5(E(_cW).a)),function(_d3){return new F(function(){return A3(_8u,_d1,_d3,_d2);});},_cY));});return new T2(0,new T(function(){return B(A2(_cR,_cZ,_cX));}),_d0);},_d4=function(_d5,_d6,_d7){var _d8=E(_d7),_d9=B(_cV(_d6,_d8.a,_d8.b));return new T2(0,_d9.a,_d9.b);},_da=function(_db){return E(E(_db).c);},_dc=function(_dd,_de,_df){var _dg=new T(function(){return E(E(E(_dd).c).a);}),_dh=new T(function(){var _di=new T(function(){return B(_8s(new T(function(){return B(_8q(_dg));})));}),_dj=new T(function(){return B(A2(_da,_dg,_de));});return B(A3(_ad,B(_a5(E(_dd).a)),function(_dk){return new F(function(){return A3(_8u,_di,_dk,_dj);});},_df));});return new T2(0,new T(function(){return B(A2(_da,_dg,_de));}),_dh);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_dc(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du){var _dv=new T(function(){return E(E(E(_ds).c).a);}),_dw=new T(function(){var _dx=new T(function(){return B(_8q(_dv));}),_dy=new T(function(){return B(_8s(_dx));}),_dz=new T(function(){return B(A3(_a9,_dx,new T(function(){return B(A2(_9Z,_dy,_aI));}),_dt));});return B(A3(_ad,B(_a5(E(_ds).a)),function(_dA){return new F(function(){return A3(_8u,_dy,_dA,_dz);});},_du));});return new T2(0,new T(function(){return B(A2(_af,_dv,_dt));}),_dw);},_dB=function(_dC,_dD,_dE){var _dF=E(_dE),_dG=B(_dr(_dD,_dF.a,_dF.b));return new T2(0,_dG.a,_dG.b);},_dH=function(_dI,_dJ,_dK,_dL){var _dM=new T(function(){return E(E(_dJ).c);}),_dN=new T3(0,new T(function(){return E(E(_dJ).a);}),new T(function(){return E(E(_dJ).b);}),new T2(0,new T(function(){return E(E(_dM).a);}),new T(function(){return E(E(_dM).b);})));return new F(function(){return A3(_a9,_dI,new T(function(){var _dO=E(_dL),_dP=B(_dr(_dN,_dO.a,_dO.b));return new T2(0,_dP.a,_dP.b);}),new T(function(){var _dQ=E(_dK),_dR=B(_dr(_dN,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);}));});},_dS=function(_dT){return E(E(_dT).b);},_dU=function(_dV){return E(E(_dV).b);},_dW=function(_dX){var _dY=new T(function(){return E(E(E(_dX).c).a);}),_dZ=new T(function(){return B(A2(_dU,E(_dX).a,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_dY)))),_L));})));});return new T2(0,new T(function(){return B(_dS(_dY));}),_dZ);},_e0=function(_e1,_e2){var _e3=B(_dW(_e2));return new T2(0,_e3.a,_e3.b);},_e4=function(_e5,_e6,_e7){var _e8=new T(function(){return E(E(E(_e5).c).a);}),_e9=new T(function(){var _ea=new T(function(){return B(_8s(new T(function(){return B(_8q(_e8));})));}),_eb=new T(function(){return B(A2(_cy,_e8,_e6));});return B(A3(_ad,B(_a5(E(_e5).a)),function(_ec){return new F(function(){return A3(_8u,_ea,_ec,_eb);});},_e7));});return new T2(0,new T(function(){return B(A2(_cA,_e8,_e6));}),_e9);},_ed=function(_ee,_ef,_eg){var _eh=E(_eg),_ei=B(_e4(_ef,_eh.a,_eh.b));return new T2(0,_ei.a,_ei.b);},_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(E(_ek).c).a);}),_eo=new T(function(){var _ep=new T(function(){return B(_8s(new T(function(){return B(_8q(_en));})));}),_eq=new T(function(){return B(A2(_cR,_en,_el));});return B(A3(_ad,B(_a5(E(_ek).a)),function(_er){return new F(function(){return A3(_8u,_ep,_er,_eq);});},_em));});return new T2(0,new T(function(){return B(A2(_cT,_en,_el));}),_eo);},_es=function(_et,_eu,_ev){var _ew=E(_ev),_ex=B(_ej(_eu,_ew.a,_ew.b));return new T2(0,_ex.a,_ex.b);},_ey=new T1(0,2),_ez=function(_eA,_eB,_eC){var _eD=new T(function(){return E(E(E(_eA).c).a);}),_eE=new T(function(){var _eF=new T(function(){return B(_8q(_eD));}),_eG=new T(function(){return B(_8s(_eF));}),_eH=new T(function(){var _eI=new T(function(){return B(A3(_a9,_eF,new T(function(){return B(A2(_9Z,_eG,_aI));}),new T(function(){return B(A2(_9Z,_eG,_ey));})));});return B(A3(_a9,_eF,_eI,new T(function(){return B(A2(_8F,_eD,_eB));})));});return B(A3(_ad,B(_a5(E(_eA).a)),function(_eJ){return new F(function(){return A3(_8u,_eG,_eJ,_eH);});},_eC));});return new T2(0,new T(function(){return B(A2(_8F,_eD,_eB));}),_eE);},_eK=function(_eL,_eM,_eN){var _eO=E(_eN),_eP=B(_ez(_eM,_eO.a,_eO.b));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR){return E(E(_eR).j);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_8q(_eW));}),_eZ=new T(function(){var _f0=new T(function(){return B(A2(_cy,_eW,_eU));});return B(A3(_8u,B(_8s(_eY)),_f0,_f0));});return B(A3(_ad,B(_a5(E(_eT).a)),function(_f1){return new F(function(){return A3(_a9,_eY,_f1,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_eQ,_eW,_eU));}),_eX);},_f2=function(_f3,_f4,_f5){var _f6=E(_f5),_f7=B(_eS(_f4,_f6.a,_f6.b));return new T2(0,_f7.a,_f7.b);},_f8=function(_f9){return E(E(_f9).p);},_fa=function(_fb,_fc,_fd){var _fe=new T(function(){return E(E(E(_fb).c).a);}),_ff=new T(function(){var _fg=new T(function(){return B(_8q(_fe));}),_fh=new T(function(){var _fi=new T(function(){return B(A2(_cR,_fe,_fc));});return B(A3(_8u,B(_8s(_fg)),_fi,_fi));});return B(A3(_ad,B(_a5(E(_fb).a)),function(_fj){return new F(function(){return A3(_a9,_fg,_fj,_fh);});},_fd));});return new T2(0,new T(function(){return B(A2(_f8,_fe,_fc));}),_ff);},_fk=function(_fl,_fm,_fn){var _fo=E(_fn),_fp=B(_fa(_fm,_fo.a,_fo.b));return new T2(0,_fp.a,_fp.b);},_fq=function(_fr,_fs){return {_:0,a:_fr,b:new T(function(){return B(_e0(_fr,_fs));}),c:function(_ft){return new F(function(){return _dl(_fr,_fs,_ft);});},d:function(_ft){return new F(function(){return _dB(_fr,_fs,_ft);});},e:function(_ft){return new F(function(){return _eK(_fr,_fs,_ft);});},f:function(_fu,_ft){return new F(function(){return _aA(_fr,_fs,_fu,_ft);});},g:function(_fu,_ft){return new F(function(){return _dH(_fr,_fs,_fu,_ft);});},h:function(_ft){return new F(function(){return _ed(_fr,_fs,_ft);});},i:function(_ft){return new F(function(){return _cL(_fr,_fs,_ft);});},j:function(_ft){return new F(function(){return _f2(_fr,_fs,_ft);});},k:function(_ft){return new F(function(){return _bz(_fr,_fs,_ft);});},l:function(_ft){return new F(function(){return _aX(_fr,_fs,_ft);});},m:function(_ft){return new F(function(){return _ca(_fr,_fs,_ft);});},n:function(_ft){return new F(function(){return _es(_fr,_fs,_ft);});},o:function(_ft){return new F(function(){return _d4(_fr,_fs,_ft);});},p:function(_ft){return new F(function(){return _fk(_fr,_fs,_ft);});},q:function(_ft){return new F(function(){return _bS(_fr,_fs,_ft);});},r:function(_ft){return new F(function(){return _bg(_fr,_fs,_ft);});},s:function(_ft){return new F(function(){return _cs(_fr,_fs,_ft);});}};},_fv=function(_fw,_fx,_fy,_fz,_fA){var _fB=new T(function(){return B(_8q(new T(function(){return E(E(E(_fw).c).a);})));}),_fC=new T(function(){var _fD=E(_fw).a,_fE=new T(function(){var _fF=new T(function(){return B(_8s(_fB));}),_fG=new T(function(){return B(A3(_8u,_fF,_fz,_fz));}),_fH=function(_fI,_fJ){var _fK=new T(function(){return B(A3(_8w,_fF,new T(function(){return B(A3(_8u,_fF,_fI,_fz));}),new T(function(){return B(A3(_8u,_fF,_fx,_fJ));})));});return new F(function(){return A3(_a9,_fB,_fK,_fG);});};return B(A3(_ad,B(_a5(_fD)),_fH,_fy));});return B(A3(_ab,_fD,_fE,_fA));});return new T2(0,new T(function(){return B(A3(_a9,_fB,_fx,_fz));}),_fC);},_fL=function(_fM,_fN,_fO,_fP){var _fQ=E(_fO),_fR=E(_fP),_fS=B(_fv(_fN,_fQ.a,_fQ.b,_fR.a,_fR.b));return new T2(0,_fS.a,_fS.b);},_fT=function(_fU,_fV){var _fW=new T(function(){return B(_8q(new T(function(){return E(E(E(_fU).c).a);})));}),_fX=new T(function(){return B(A2(_dU,E(_fU).a,new T(function(){return B(A2(_9Z,B(_8s(_fW)),_L));})));});return new T2(0,new T(function(){return B(A2(_8y,_fW,_fV));}),_fX);},_fY=function(_fZ,_g0,_g1){var _g2=B(_fT(_g0,_g1));return new T2(0,_g2.a,_g2.b);},_g3=function(_g4,_g5,_g6){var _g7=new T(function(){return B(_8q(new T(function(){return E(E(E(_g4).c).a);})));}),_g8=new T(function(){return B(_8s(_g7));}),_g9=new T(function(){var _ga=new T(function(){var _gb=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),new T(function(){return B(A3(_8u,_g8,_g5,_g5));})));});return B(A2(_88,_g8,_gb));});return B(A3(_ad,B(_a5(E(_g4).a)),function(_gc){return new F(function(){return A3(_8u,_g8,_gc,_ga);});},_g6));}),_gd=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),_g5));});return new T2(0,_gd,_g9);},_ge=function(_gf,_gg,_gh){var _gi=E(_gh),_gj=B(_g3(_gg,_gi.a,_gi.b));return new T2(0,_gj.a,_gj.b);},_gk=function(_gl,_gm){return new T4(0,_gl,function(_fu,_ft){return new F(function(){return _fL(_gl,_gm,_fu,_ft);});},function(_ft){return new F(function(){return _ge(_gl,_gm,_ft);});},function(_ft){return new F(function(){return _fY(_gl,_gm,_ft);});});},_gn=function(_go,_gp,_gq,_gr,_gs){var _gt=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_go).c).a);})));})));}),_gu=new T(function(){var _gv=E(_go).a,_gw=new T(function(){var _gx=function(_gy,_gz){return new F(function(){return A3(_86,_gt,new T(function(){return B(A3(_8u,_gt,_gp,_gz));}),new T(function(){return B(A3(_8u,_gt,_gy,_gr));}));});};return B(A3(_ad,B(_a5(_gv)),_gx,_gq));});return B(A3(_ab,_gv,_gw,_gs));});return new T2(0,new T(function(){return B(A3(_8u,_gt,_gp,_gr));}),_gu);},_gA=function(_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gn(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ,_gK,_gL,_gM){var _gN=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gI).c).a);})));})));}),_gO=new T(function(){var _gP=E(_gI).a,_gQ=new T(function(){return B(A3(_ad,B(_a5(_gP)),new T(function(){return B(_86(_gN));}),_gK));});return B(A3(_ab,_gP,_gQ,_gM));});return new T2(0,new T(function(){return B(A3(_86,_gN,_gJ,_gL));}),_gO);},_gR=function(_gS,_gT,_gU){var _gV=E(_gT),_gW=E(_gU),_gX=B(_gH(_gS,_gV.a,_gV.b,_gW.a,_gW.b));return new T2(0,_gX.a,_gX.b);},_gY=function(_gZ,_h0,_h1){var _h2=B(_h3(_gZ));return new F(function(){return A3(_86,_h2,_h0,new T(function(){return B(A2(_88,_h2,_h1));}));});},_h4=function(_h5){return E(E(_h5).e);},_h6=function(_h7){return E(E(_h7).f);},_h8=function(_h9,_ha,_hb){var _hc=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_h9).c).a);})));})));}),_hd=new T(function(){var _he=new T(function(){return B(A2(_h6,_hc,_ha));});return B(A3(_ad,B(_a5(E(_h9).a)),function(_hf){return new F(function(){return A3(_8u,_hc,_hf,_he);});},_hb));});return new T2(0,new T(function(){return B(A2(_h4,_hc,_ha));}),_hd);},_hg=function(_hh,_hi){var _hj=E(_hi),_hk=B(_h8(_hh,_hj.a,_hj.b));return new T2(0,_hk.a,_hk.b);},_hl=function(_hm,_hn){var _ho=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hm).c).a);})));})));}),_hp=new T(function(){return B(A2(_dU,E(_hm).a,new T(function(){return B(A2(_9Z,_ho,_L));})));});return new T2(0,new T(function(){return B(A2(_9Z,_ho,_hn));}),_hp);},_hq=function(_hr,_hs){var _ht=B(_hl(_hr,_hs));return new T2(0,_ht.a,_ht.b);},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hv).c).a);})));})));}),_hz=new T(function(){return B(A3(_ad,B(_a5(E(_hv).a)),new T(function(){return B(_88(_hy));}),_hx));});return new T2(0,new T(function(){return B(A2(_88,_hy,_hw));}),_hz);},_hA=function(_hB,_hC){var _hD=E(_hC),_hE=B(_hu(_hB,_hD.a,_hD.b));return new T2(0,_hE.a,_hE.b);},_hF=function(_hG,_hH){var _hI=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hG).c).a);})));})));}),_hJ=new T(function(){return B(A2(_dU,E(_hG).a,new T(function(){return B(A2(_9Z,_hI,_L));})));});return new T2(0,new T(function(){return B(A2(_h6,_hI,_hH));}),_hJ);},_hK=function(_hL,_hM){var _hN=B(_hF(_hL,E(_hM).a));return new T2(0,_hN.a,_hN.b);},_h3=function(_hO){return {_:0,a:function(_fu,_ft){return new F(function(){return _gR(_hO,_fu,_ft);});},b:function(_fu,_ft){return new F(function(){return _gY(_hO,_fu,_ft);});},c:function(_fu,_ft){return new F(function(){return _gA(_hO,_fu,_ft);});},d:function(_ft){return new F(function(){return _hA(_hO,_ft);});},e:function(_ft){return new F(function(){return _hg(_hO,_ft);});},f:function(_ft){return new F(function(){return _hK(_hO,_ft);});},g:function(_ft){return new F(function(){return _hq(_hO,_ft);});}};},_hP=function(_hQ){var _hR=new T(function(){return E(E(_hQ).a);}),_hS=new T3(0,_9X,_a1,new T2(0,_hR,new T(function(){return E(E(_hQ).b);}))),_hT=new T(function(){return B(_fq(new T(function(){return B(_gk(new T(function(){return B(_h3(_hS));}),_hS));}),_hS));}),_hU=new T(function(){return B(_8s(new T(function(){return B(_8q(_hR));})));});return function(_hV){var _hW=E(_hV),_hX=B(A2(_9Z,_hU,_1o)),_hY=B(A2(_9Z,_hU,_9Y));return E(B(_8H(_hT,new T2(0,_hW.a,new T3(0,E(_hX),E(_hY),E(_hY))),new T2(0,_hW.b,new T3(0,E(_hY),E(_hX),E(_hY))),new T2(0,_hW.c,new T3(0,E(_hY),E(_hY),E(_hX))))).b);};},_hZ=new T(function(){return B(_hP(_9t));}),_i0=function(_i1,_i2){var _i3=E(_i2);return (_i3._==0)?__Z:new T2(1,_i1,new T2(1,_i3.a,new T(function(){return B(_i0(_i1,_i3.b));})));},_i4=new T(function(){var _i5=B(A1(_hZ,_92));return new T2(1,_i5.a,new T(function(){return B(_i0(_22,new T2(1,_i5.b,new T2(1,_i5.c,_w))));}));}),_i6=new T1(1,_i4),_i7=new T2(1,_i6,_1S),_i8=new T(function(){return B(unCStr("vec3("));}),_i9=new T1(0,_i8),_ia=new T2(1,_i9,_i7),_ib=new T(function(){return toJSStr(B(_1F(_x,_1l,_ia)));}),_ic="enclose",_id="outline",_ie="polygon",_if="z",_ig="y",_ih="x",_ii=0,_ij=function(_ik){var _il=__new(),_im=_il,_in=function(_io,_){while(1){var _ip=E(_io);if(!_ip._){return _ii;}else{var _iq=E(_ip.a),_ir=__set(_im,E(_iq.a),E(_iq.b));_io=_ip.b;continue;}}},_is=B(_in(_ik,_));return E(_im);},_it=function(_iu){return new F(function(){return _ij(new T2(1,new T2(0,_ih,new T(function(){return E(E(E(E(_iu).d).a).a);})),new T2(1,new T2(0,_ig,new T(function(){return E(E(E(E(_iu).d).a).b);})),new T2(1,new T2(0,_if,new T(function(){return E(E(E(E(_iu).d).a).c);})),new T2(1,new T2(0,_ie,new T(function(){return E(_iu).h;})),new T2(1,new T2(0,_id,new T(function(){return E(_iu).i;})),new T2(1,new T2(0,_ic,new T(function(){return E(_iu).j;})),_w)))))));});},_iv=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_iw=new T(function(){return B(err(_iv));}),_ix=new T(function(){return eval("__strict(drawObjects)");}),_iy=new T(function(){return eval("__strict(draw)");}),_iz=function(_iA,_iB){var _iC=jsShowI(_iA);return new F(function(){return _n(fromJSStr(_iC),_iB);});},_iD=function(_iE,_iF,_iG){if(_iF>=0){return new F(function(){return _iz(_iF,_iG);});}else{if(_iE<=6){return new F(function(){return _iz(_iF,_iG);});}else{return new T2(1,_11,new T(function(){var _iH=jsShowI(_iF);return B(_n(fromJSStr(_iH),new T2(1,_10,_iG)));}));}}},_iI=new T(function(){return B(unCStr(")"));}),_iJ=function(_iK,_iL){var _iM=new T(function(){var _iN=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_iD(0,_iK,_w)),_iI));})));},1);return B(_n(B(_iD(0,_iL,_w)),_iN));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_iM)));});},_iO=new T2(1,_ii,_w),_iP=function(_iQ){return E(_iQ);},_iR=function(_iS){return E(_iS);},_iT=function(_iU,_iV){return E(_iV);},_iW=function(_iX,_iY){return E(_iX);},_iZ=function(_j0){return E(_j0);},_j1=new T2(0,_iZ,_iW),_j2=function(_j3,_j4){return E(_j3);},_j5=new T5(0,_j1,_iR,_iP,_iT,_j2),_j6=function(_j7){var _j8=E(_j7);return new F(function(){return Math.log(_j8+(_j8+1)*Math.sqrt((_j8-1)/(_j8+1)));});},_j9=function(_ja){var _jb=E(_ja);return new F(function(){return Math.log(_jb+Math.sqrt(1+_jb*_jb));});},_jc=function(_jd){var _je=E(_jd);return 0.5*Math.log((1+_je)/(1-_je));},_jf=function(_jg,_jh){return Math.log(E(_jh))/Math.log(E(_jg));},_ji=3.141592653589793,_jj=function(_jk){var _jl=E(_jk);return new F(function(){return _7J(_jl.a,_jl.b);});},_jm=function(_jn){return 1/E(_jn);},_jo=function(_jp){var _jq=E(_jp),_jr=E(_jq);return (_jr==0)?E(_7I):(_jr<=0)? -_jr:E(_jq);},_js=function(_jt){var _ju=E(_jt);if(!_ju._){return _ju.a;}else{return new F(function(){return I_toNumber(_ju.a);});}},_jv=function(_jw){return new F(function(){return _js(_jw);});},_jx=1,_jy=-1,_jz=function(_jA){var _jB=E(_jA);return (_jB<=0)?(_jB>=0)?E(_jB):E(_jy):E(_jx);},_jC=function(_jD,_jE){return E(_jD)-E(_jE);},_jF=function(_jG){return  -E(_jG);},_jH=function(_jI,_jJ){return E(_jI)+E(_jJ);},_jK=function(_jL,_jM){return E(_jL)*E(_jM);},_jN={_:0,a:_jH,b:_jC,c:_jK,d:_jF,e:_jo,f:_jz,g:_jv},_jO=function(_jP,_jQ){return E(_jP)/E(_jQ);},_jR=new T4(0,_jN,_jO,_jm,_jj),_jS=function(_jT){return new F(function(){return Math.acos(E(_jT));});},_jU=function(_jV){return new F(function(){return Math.asin(E(_jV));});},_jW=function(_jX){return new F(function(){return Math.atan(E(_jX));});},_jY=function(_jZ){return new F(function(){return Math.cos(E(_jZ));});},_k0=function(_k1){return new F(function(){return cosh(E(_k1));});},_k2=function(_k3){return new F(function(){return Math.exp(E(_k3));});},_k4=function(_k5){return new F(function(){return Math.log(E(_k5));});},_k6=function(_k7,_k8){return new F(function(){return Math.pow(E(_k7),E(_k8));});},_k9=function(_ka){return new F(function(){return Math.sin(E(_ka));});},_kb=function(_kc){return new F(function(){return sinh(E(_kc));});},_kd=function(_ke){return new F(function(){return Math.sqrt(E(_ke));});},_kf=function(_kg){return new F(function(){return Math.tan(E(_kg));});},_kh=function(_ki){return new F(function(){return tanh(E(_ki));});},_kj={_:0,a:_jR,b:_ji,c:_k2,d:_k4,e:_kd,f:_k6,g:_jf,h:_k9,i:_jY,j:_kf,k:_jU,l:_jS,m:_jW,n:_kb,o:_k0,p:_kh,q:_j9,r:_j6,s:_jc},_kk="flipped2",_kl="flipped1",_km="c1y",_kn="c1x",_ko="w2z",_kp="w2y",_kq="w2x",_kr="w1z",_ks="w1y",_kt="w1x",_ku="d2z",_kv="d2y",_kw="d2x",_kx="d1z",_ky="d1y",_kz="d1x",_kA="c2y",_kB="c2x",_kC=function(_kD,_){var _kE=__get(_kD,E(_kt)),_kF=__get(_kD,E(_ks)),_kG=__get(_kD,E(_kr)),_kH=__get(_kD,E(_kq)),_kI=__get(_kD,E(_kp)),_kJ=__get(_kD,E(_ko)),_kK=__get(_kD,E(_kn)),_kL=__get(_kD,E(_km)),_kM=__get(_kD,E(_kB)),_kN=__get(_kD,E(_kA)),_kO=__get(_kD,E(_kz)),_kP=__get(_kD,E(_ky)),_kQ=__get(_kD,E(_kx)),_kR=__get(_kD,E(_kw)),_kS=__get(_kD,E(_kv)),_kT=__get(_kD,E(_ku)),_kU=__get(_kD,E(_kl)),_kV=__get(_kD,E(_kk));return {_:0,a:E(new T3(0,E(_kE),E(_kF),E(_kG))),b:E(new T3(0,E(_kH),E(_kI),E(_kJ))),c:E(new T2(0,E(_kK),E(_kL))),d:E(new T2(0,E(_kM),E(_kN))),e:E(new T3(0,E(_kO),E(_kP),E(_kQ))),f:E(new T3(0,E(_kR),E(_kS),E(_kT))),g:E(_kU),h:E(_kV)};},_kW=function(_kX,_){var _kY=E(_kX);if(!_kY._){return _w;}else{var _kZ=B(_kC(E(_kY.a),_)),_l0=B(_kW(_kY.b,_));return new T2(1,_kZ,_l0);}},_l1=function(_l2){var _l3=E(_l2);return (E(_l3.b)-E(_l3.a)|0)+1|0;},_l4=function(_l5,_l6){var _l7=E(_l5),_l8=E(_l6);return (E(_l7.a)>_l8)?false:_l8<=E(_l7.b);},_l9=function(_la){return new F(function(){return _iD(0,E(_la),_w);});},_lb=function(_lc,_ld,_le){return new F(function(){return _iD(E(_lc),E(_ld),_le);});},_lf=function(_lg,_lh){return new F(function(){return _iD(0,E(_lg),_lh);});},_li=function(_lj,_lk){return new F(function(){return _49(_lf,_lj,_lk);});},_ll=new T3(0,_lb,_l9,_li),_lm=0,_ln=function(_lo,_lp,_lq){return new F(function(){return A1(_lo,new T2(1,_46,new T(function(){return B(A1(_lp,_lq));})));});},_lr=new T(function(){return B(unCStr(": empty list"));}),_ls=new T(function(){return B(unCStr("Prelude."));}),_lt=function(_lu){return new F(function(){return err(B(_n(_ls,new T(function(){return B(_n(_lu,_lr));},1))));});},_lv=new T(function(){return B(unCStr("foldr1"));}),_lw=new T(function(){return B(_lt(_lv));}),_lx=function(_ly,_lz){var _lA=E(_lz);if(!_lA._){return E(_lw);}else{var _lB=_lA.a,_lC=E(_lA.b);if(!_lC._){return E(_lB);}else{return new F(function(){return A2(_ly,_lB,new T(function(){return B(_lx(_ly,_lC));}));});}}},_lD=new T(function(){return B(unCStr(" out of range "));}),_lE=new T(function(){return B(unCStr("}.index: Index "));}),_lF=new T(function(){return B(unCStr("Ix{"));}),_lG=new T2(1,_10,_w),_lH=new T2(1,_10,_lG),_lI=0,_lJ=function(_lK){return E(E(_lK).a);},_lL=function(_lM,_lN,_lO,_lP,_lQ){var _lR=new T(function(){var _lS=new T(function(){var _lT=new T(function(){var _lU=new T(function(){var _lV=new T(function(){return B(A3(_lx,_ln,new T2(1,new T(function(){return B(A3(_lJ,_lO,_lI,_lP));}),new T2(1,new T(function(){return B(A3(_lJ,_lO,_lI,_lQ));}),_w)),_lH));});return B(_n(_lD,new T2(1,_11,new T2(1,_11,_lV))));});return B(A(_lJ,[_lO,_lm,_lN,new T2(1,_10,_lU)]));});return B(_n(_lE,new T2(1,_11,_lT)));},1);return B(_n(_lM,_lS));},1);return new F(function(){return err(B(_n(_lF,_lR)));});},_lW=function(_lX,_lY,_lZ,_m0,_m1){return new F(function(){return _lL(_lX,_lY,_m1,_lZ,_m0);});},_m2=function(_m3,_m4,_m5,_m6){var _m7=E(_m5);return new F(function(){return _lW(_m3,_m4,_m7.a,_m7.b,_m6);});},_m8=function(_m9,_ma,_mb,_mc){return new F(function(){return _m2(_mc,_mb,_ma,_m9);});},_md=new T(function(){return B(unCStr("Int"));}),_me=function(_mf,_mg){return new F(function(){return _m8(_ll,_mg,_mf,_md);});},_mh=function(_mi,_mj){var _mk=E(_mi),_ml=E(_mk.a),_mm=E(_mj);if(_ml>_mm){return new F(function(){return _me(_mm,_mk);});}else{if(_mm>E(_mk.b)){return new F(function(){return _me(_mm,_mk);});}else{return _mm-_ml|0;}}},_mn=function(_mo,_mp){if(_mo<=_mp){var _mq=function(_mr){return new T2(1,_mr,new T(function(){if(_mr!=_mp){return B(_mq(_mr+1|0));}else{return __Z;}}));};return new F(function(){return _mq(_mo);});}else{return __Z;}},_ms=function(_mt,_mu){return new F(function(){return _mn(E(_mt),E(_mu));});},_mv=function(_mw){var _mx=E(_mw);return new F(function(){return _ms(_mx.a,_mx.b);});},_my=function(_mz){var _mA=E(_mz),_mB=E(_mA.a),_mC=E(_mA.b);return (_mB>_mC)?E(_lm):(_mC-_mB|0)+1|0;},_mD=function(_mE,_mF){return E(_mE)-E(_mF)|0;},_mG=function(_mH,_mI){return new F(function(){return _mD(_mI,E(_mH).a);});},_mJ=function(_mK,_mL){return E(_mK)==E(_mL);},_mM=function(_mN,_mO){return E(_mN)!=E(_mO);},_mP=new T2(0,_mJ,_mM),_mQ=function(_mR,_mS){var _mT=E(_mR),_mU=E(_mS);return (_mT>_mU)?E(_mT):E(_mU);},_mV=function(_mW,_mX){var _mY=E(_mW),_mZ=E(_mX);return (_mY>_mZ)?E(_mZ):E(_mY);},_n0=function(_n1,_n2){return (_n1>=_n2)?(_n1!=_n2)?2:1:0;},_n3=function(_n4,_n5){return new F(function(){return _n0(E(_n4),E(_n5));});},_n6=function(_n7,_n8){return E(_n7)>=E(_n8);},_n9=function(_na,_nb){return E(_na)>E(_nb);},_nc=function(_nd,_ne){return E(_nd)<=E(_ne);},_nf=function(_ng,_nh){return E(_ng)<E(_nh);},_ni={_:0,a:_mP,b:_n3,c:_nf,d:_nc,e:_n9,f:_n6,g:_mQ,h:_mV},_nj={_:0,a:_ni,b:_mv,c:_mh,d:_mG,e:_l4,f:_my,g:_l1},_nk=function(_nl,_nm,_){while(1){var _nn=B((function(_no,_np,_){var _nq=E(_no);if(!_nq._){return new T2(0,_ii,_np);}else{var _nr=B(A2(_nq.a,_np,_));_nl=_nq.b;_nm=new T(function(){return E(E(_nr).b);});return __continue;}})(_nl,_nm,_));if(_nn!=__continue){return _nn;}}},_ns=function(_nt,_nu){return new T2(1,_nt,_nu);},_nv=function(_nw,_nx){var _ny=E(_nx);return new T2(0,_ny.a,_ny.b);},_nz=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_nA=new T(function(){return B(err(_nz));}),_nB=new T(function(){return B(unCStr("Negative range size"));}),_nC=new T(function(){return B(err(_nB));}),_nD=function(_nE){return E(E(_nE).f);},_nF=function(_nG){var _nH=B(A1(_nG,_));return E(_nH);},_nI=function(_nJ,_nK,_nL){var _nM=E(_nK),_nN=_nM.a,_nO=_nM.b,_nP=function(_){var _nQ=B(A2(_nD,_nJ,_nM));if(_nQ>=0){var _nR=newArr(_nQ,_nA),_nS=_nR,_nT=E(_nQ);if(!_nT){return new T(function(){return new T4(0,E(_nN),E(_nO),0,_nS);});}else{var _nU=function(_nV,_nW,_){while(1){var _nX=E(_nV);if(!_nX._){return E(_);}else{var _=_nS[_nW]=_nX.a;if(_nW!=(_nT-1|0)){var _nY=_nW+1|0;_nV=_nX.b;_nW=_nY;continue;}else{return E(_);}}}},_=B(_nU(_nL,0,_));return new T(function(){return new T4(0,E(_nN),E(_nO),_nT,_nS);});}}else{return E(_nC);}};return new F(function(){return _nF(_nP);});},_nZ=function(_o0,_o1,_o2,_o3){var _o4=new T(function(){var _o5=E(_o3),_o6=_o5.c-1|0,_o7=new T(function(){return B(A2(_dU,_o1,_w));});if(0<=_o6){var _o8=new T(function(){return B(_a5(_o1));}),_o9=function(_oa){var _ob=new T(function(){var _oc=new T(function(){return B(A1(_o2,new T(function(){return E(_o5.d[_oa]);})));});return B(A3(_ad,_o8,_ns,_oc));});return new F(function(){return A3(_ab,_o1,_ob,new T(function(){if(_oa!=_o6){return B(_o9(_oa+1|0));}else{return E(_o7);}}));});};return B(_o9(0));}else{return E(_o7);}}),_od=new T(function(){return B(_nv(_o0,_o3));});return new F(function(){return A3(_ad,B(_a5(_o1)),function(_oe){return new F(function(){return _nI(_o0,_od,_oe);});},_o4);});},_of=function(_og,_oh,_oi,_oj,_ok,_ol,_om,_on,_oo){var _op=B(_8u(_og));return new T2(0,new T3(0,E(B(A1(B(A1(_op,_oh)),_ol))),E(B(A1(B(A1(_op,_oi)),_om))),E(B(A1(B(A1(_op,_oj)),_on)))),B(A1(B(A1(_op,_ok)),_oo)));},_oq=function(_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz){var _oA=B(_86(_or));return new T2(0,new T3(0,E(B(A1(B(A1(_oA,_os)),_ow))),E(B(A1(B(A1(_oA,_ot)),_ox))),E(B(A1(B(A1(_oA,_ou)),_oy)))),B(A1(B(A1(_oA,_ov)),_oz)));},_oB=function(_oC,_oD){return (E(_oC)!=E(_oD))?true:false;},_oE=function(_oF,_oG){return E(_oF)==E(_oG);},_oH=new T2(0,_oE,_oB),_oI=function(_oJ,_oK){return E(_oJ)<E(_oK);},_oL=function(_oM,_oN){return E(_oM)<=E(_oN);},_oO=function(_oP,_oQ){return E(_oP)>E(_oQ);},_oR=function(_oS,_oT){return E(_oS)>=E(_oT);},_oU=function(_oV,_oW){var _oX=E(_oV),_oY=E(_oW);return (_oX>=_oY)?(_oX!=_oY)?2:1:0;},_oZ=function(_p0,_p1){var _p2=E(_p0),_p3=E(_p1);return (_p2>_p3)?E(_p2):E(_p3);},_p4=function(_p5,_p6){var _p7=E(_p5),_p8=E(_p6);return (_p7>_p8)?E(_p8):E(_p7);},_p9={_:0,a:_oH,b:_oU,c:_oI,d:_oL,e:_oO,f:_oR,g:_oZ,h:_p4},_pa="dz",_pb="wy",_pc="wx",_pd="dy",_pe="dx",_pf="t",_pg="a",_ph="r",_pi="ly",_pj="lx",_pk="wz",_pl=function(_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt,_pu){return new F(function(){return _ij(new T2(1,new T2(0,_pc,_pm),new T2(1,new T2(0,_pb,_pn),new T2(1,new T2(0,_pk,_po),new T2(1,new T2(0,_pj,_pp*_pq*Math.cos(_pr)),new T2(1,new T2(0,_pi,_pp*_pq*Math.sin(_pr)),new T2(1,new T2(0,_ph,_pp),new T2(1,new T2(0,_pg,_pq),new T2(1,new T2(0,_pf,_pr),new T2(1,new T2(0,_pe,_ps),new T2(1,new T2(0,_pd,_pt),new T2(1,new T2(0,_pa,_pu),_w))))))))))));});},_pv=function(_pw){var _px=E(_pw),_py=E(_px.a),_pz=E(_px.b),_pA=E(_px.d);return new F(function(){return _pl(_py.a,_py.b,_py.c,E(_pz.a),E(_pz.b),E(_px.c),_pA.a,_pA.b,_pA.c);});},_pB=function(_pC,_pD){var _pE=E(_pD);return (_pE._==0)?__Z:new T2(1,new T(function(){return B(A1(_pC,_pE.a));}),new T(function(){return B(_pB(_pC,_pE.b));}));},_pF=function(_pG,_pH,_pI){var _pJ=__lst2arr(B(_pB(_pv,new T2(1,_pG,new T2(1,_pH,new T2(1,_pI,_w))))));return E(_pJ);},_pK=function(_pL){var _pM=E(_pL);return new F(function(){return _pF(_pM.a,_pM.b,_pM.c);});},_pN=new T2(0,_kj,_p9),_pO=function(_pP,_pQ,_pR,_pS,_pT,_pU,_pV){var _pW=B(_8s(B(_8q(_pP)))),_pX=new T(function(){return B(A3(_86,_pW,new T(function(){return B(A3(_8u,_pW,_pQ,_pT));}),new T(function(){return B(A3(_8u,_pW,_pR,_pU));})));});return new F(function(){return A3(_86,_pW,_pX,new T(function(){return B(A3(_8u,_pW,_pS,_pV));}));});},_pY=function(_pZ,_q0,_q1,_q2){var _q3=B(_8q(_pZ)),_q4=new T(function(){return B(A2(_8F,_pZ,new T(function(){return B(_pO(_pZ,_q0,_q1,_q2,_q0,_q1,_q2));})));});return new T3(0,B(A3(_a9,_q3,_q0,_q4)),B(A3(_a9,_q3,_q1,_q4)),B(A3(_a9,_q3,_q2,_q4)));},_q5=function(_q6,_q7,_q8,_q9,_qa,_qb,_qc){var _qd=B(_8u(_q6));return new T3(0,B(A1(B(A1(_qd,_q7)),_qa)),B(A1(B(A1(_qd,_q8)),_qb)),B(A1(B(A1(_qd,_q9)),_qc)));},_qe=function(_qf,_qg,_qh,_qi,_qj,_qk,_ql){var _qm=B(_86(_qf));return new T3(0,B(A1(B(A1(_qm,_qg)),_qj)),B(A1(B(A1(_qm,_qh)),_qk)),B(A1(B(A1(_qm,_qi)),_ql)));},_qn=function(_qo,_qp){var _qq=new T(function(){return E(E(_qo).a);}),_qr=new T(function(){return B(A2(_hP,new T2(0,_qq,new T(function(){return E(E(_qo).b);})),_qp));}),_qs=new T(function(){var _qt=E(_qr),_qu=B(_pY(_qq,_qt.a,_qt.b,_qt.c));return new T3(0,E(_qu.a),E(_qu.b),E(_qu.c));}),_qv=new T(function(){var _qw=E(_qp),_qx=_qw.a,_qy=_qw.b,_qz=_qw.c,_qA=E(_qs),_qB=B(_8q(_qq)),_qC=new T(function(){return B(A2(_8F,_qq,new T(function(){var _qD=E(_qr),_qE=_qD.a,_qF=_qD.b,_qG=_qD.c;return B(_pO(_qq,_qE,_qF,_qG,_qE,_qF,_qG));})));}),_qH=B(A3(_a9,_qB,new T(function(){return B(_8H(_qq,_qx,_qy,_qz));}),_qC)),_qI=B(_8s(_qB)),_qJ=B(_q5(_qI,_qA.a,_qA.b,_qA.c,_qH,_qH,_qH)),_qK=B(_88(_qI)),_qL=B(_qe(_qI,_qx,_qy,_qz,B(A1(_qK,_qJ.a)),B(A1(_qK,_qJ.b)),B(A1(_qK,_qJ.c))));return new T3(0,E(_qL.a),E(_qL.b),E(_qL.c));});return new T2(0,_qv,_qs);},_qM=function(_qN){return E(E(_qN).a);},_qO=function(_qP,_qQ,_qR,_qS,_qT,_qU,_qV){var _qW=B(_pO(_qP,_qT,_qU,_qV,_qQ,_qR,_qS)),_qX=B(_8s(B(_8q(_qP)))),_qY=B(_q5(_qX,_qT,_qU,_qV,_qW,_qW,_qW)),_qZ=B(_88(_qX));return new F(function(){return _qe(_qX,_qQ,_qR,_qS,B(A1(_qZ,_qY.a)),B(A1(_qZ,_qY.b)),B(A1(_qZ,_qY.c)));});},_r0=function(_r1){return E(E(_r1).a);},_r2=function(_r3,_r4,_r5,_r6){var _r7=new T(function(){var _r8=E(_r6),_r9=E(_r5),_ra=B(_qO(_r3,_r8.a,_r8.b,_r8.c,_r9.a,_r9.b,_r9.c));return new T3(0,E(_ra.a),E(_ra.b),E(_ra.c));}),_rb=new T(function(){return B(A2(_8F,_r3,new T(function(){var _rc=E(_r7),_rd=_rc.a,_re=_rc.b,_rf=_rc.c;return B(_pO(_r3,_rd,_re,_rf,_rd,_re,_rf));})));});if(!B(A3(_r0,B(_qM(_r4)),_rb,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_r3)))),_9Y));})))){var _rg=E(_r7),_rh=B(_pY(_r3,_rg.a,_rg.b,_rg.c)),_ri=B(A2(_8F,_r3,new T(function(){var _rj=E(_r6),_rk=_rj.a,_rl=_rj.b,_rm=_rj.c;return B(_pO(_r3,_rk,_rl,_rm,_rk,_rl,_rm));}))),_rn=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_r3));})));})));return new T3(0,B(A1(B(A1(_rn,_rh.a)),_ri)),B(A1(B(A1(_rn,_rh.b)),_ri)),B(A1(B(A1(_rn,_rh.c)),_ri)));}else{var _ro=B(A2(_9Z,B(_8s(B(_8q(_r3)))),_9Y));return new T3(0,_ro,_ro,_ro);}},_rp=0,_rq=new T3(0,E(_rp),E(_rp),E(_rp)),_rr=function(_rs,_rt){while(1){var _ru=E(_rs);if(!_ru._){return E(_rt);}else{var _rv=_ru.b,_rw=E(_ru.a);if(_rt>_rw){_rs=_rv;continue;}else{_rs=_rv;_rt=_rw;continue;}}}},_rx=new T(function(){var _ry=eval("angleCount"),_rz=Number(_ry);return jsTrunc(_rz);}),_rA=new T(function(){return E(_rx);}),_rB=new T(function(){return B(unCStr("head"));}),_rC=new T(function(){return B(_lt(_rB));}),_rD=function(_rE,_rF,_rG){var _rH=E(_rE);if(!_rH._){return __Z;}else{var _rI=E(_rF);if(!_rI._){return __Z;}else{var _rJ=_rI.a,_rK=E(_rG);if(!_rK._){return __Z;}else{var _rL=E(_rK.a),_rM=_rL.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_rH.a),E(_rJ),E(_rM));}),new T2(1,new T(function(){return new T3(0,E(_rJ),E(_rM),E(_rL.b));}),_w)),new T(function(){return B(_rD(_rH.b,_rI.b,_rK.b));},1));});}}}},_rN=new T(function(){return B(unCStr("tail"));}),_rO=new T(function(){return B(_lt(_rN));}),_rP=function(_rQ,_rR){var _rS=E(_rQ);if(!_rS._){return __Z;}else{var _rT=E(_rR);return (_rT._==0)?__Z:new T2(1,new T2(0,_rS.a,_rT.a),new T(function(){return B(_rP(_rS.b,_rT.b));}));}},_rU=function(_rV,_rW){var _rX=E(_rV);if(!_rX._){return __Z;}else{var _rY=E(_rW);if(!_rY._){return __Z;}else{var _rZ=E(_rX.a),_s0=_rZ.b,_s1=E(_rY.a).b,_s2=new T(function(){var _s3=new T(function(){return B(_rP(_s1,new T(function(){var _s4=E(_s1);if(!_s4._){return E(_rO);}else{return E(_s4.b);}},1)));},1);return B(_rD(_s0,new T(function(){var _s5=E(_s0);if(!_s5._){return E(_rO);}else{return E(_s5.b);}},1),_s3));});return new F(function(){return _n(new T2(1,new T(function(){var _s6=E(_s0);if(!_s6._){return E(_rC);}else{var _s7=E(_s1);if(!_s7._){return E(_rC);}else{return new T3(0,E(_rZ.a),E(_s6.a),E(_s7.a));}}}),_s2),new T(function(){return B(_rU(_rX.b,_rY.b));},1));});}}},_s8=new T(function(){return 6.283185307179586/E(_rA);}),_s9=new T(function(){return E(_rA)-1;}),_sa=new T1(0,1),_sb=function(_sc,_sd){var _se=E(_sd),_sf=new T(function(){var _sg=B(_8s(_sc)),_sh=B(_sb(_sc,B(A3(_86,_sg,_se,new T(function(){return B(A2(_9Z,_sg,_sa));})))));return new T2(1,_sh.a,_sh.b);});return new T2(0,_se,_sf);},_si=function(_sj){return E(E(_sj).d);},_sk=new T1(0,2),_sl=function(_sm,_sn){var _so=E(_sn);if(!_so._){return __Z;}else{var _sp=_so.a;return (!B(A1(_sm,_sp)))?__Z:new T2(1,_sp,new T(function(){return B(_sl(_sm,_so.b));}));}},_sq=function(_sr,_ss,_st,_su){var _sv=B(_sb(_ss,_st)),_sw=new T(function(){var _sx=B(_8s(_ss)),_sy=new T(function(){return B(A3(_a9,_ss,new T(function(){return B(A2(_9Z,_sx,_sa));}),new T(function(){return B(A2(_9Z,_sx,_sk));})));});return B(A3(_86,_sx,_su,_sy));});return new F(function(){return _sl(function(_sz){return new F(function(){return A3(_si,_sr,_sz,_sw);});},new T2(1,_sv.a,_sv.b));});},_sA=new T(function(){return B(_sq(_p9,_jR,_rp,_s9));}),_sB=function(_sC,_sD){while(1){var _sE=E(_sC);if(!_sE._){return E(_sD);}else{_sC=_sE.b;_sD=_sE.a;continue;}}},_sF=new T(function(){return B(unCStr("last"));}),_sG=new T(function(){return B(_lt(_sF));}),_sH=function(_sI){return new F(function(){return _sB(_sI,_sG);});},_sJ=function(_sK){return new F(function(){return _sH(E(_sK).b);});},_sL=new T(function(){return B(unCStr("maximum"));}),_sM=new T(function(){return B(_lt(_sL));}),_sN=new T(function(){var _sO=eval("proceedCount"),_sP=Number(_sO);return jsTrunc(_sP);}),_sQ=new T(function(){return E(_sN);}),_sR=1,_sS=new T(function(){return B(_sq(_p9,_jR,_sR,_sQ));}),_sT=function(_sU,_sV,_sW,_sX,_sY,_sZ,_t0,_t1,_t2,_t3,_t4,_t5,_t6,_t7){var _t8=new T(function(){var _t9=new T(function(){var _ta=E(_t3),_tb=E(_t7),_tc=E(_t6),_td=E(_t4),_te=E(_t5),_tf=E(_t2);return new T3(0,_ta*_tb-_tc*_td,_td*_te-_tb*_tf,_tf*_tc-_te*_ta);}),_tg=function(_th){var _ti=new T(function(){var _tj=E(_th)/E(_rA);return (_tj+_tj)*3.141592653589793;}),_tk=new T(function(){return B(A1(_sU,_ti));}),_tl=new T(function(){var _tm=new T(function(){var _tn=E(_tk)/E(_sQ);return new T3(0,E(_tn),E(_tn),E(_tn));}),_to=function(_tp,_tq){var _tr=E(_tp);if(!_tr._){return new T2(0,_w,_tq);}else{var _ts=new T(function(){var _tt=B(_qn(_pN,new T(function(){var _tu=E(_tq),_tv=E(_tu.a),_tw=E(_tu.b),_tx=E(_tm);return new T3(0,E(_tv.a)+E(_tw.a)*E(_tx.a),E(_tv.b)+E(_tw.b)*E(_tx.b),E(_tv.c)+E(_tw.c)*E(_tx.c));}))),_ty=_tt.a,_tz=new T(function(){var _tA=E(_tt.b),_tB=E(E(_tq).b),_tC=B(_qO(_kj,_tB.a,_tB.b,_tB.c,_tA.a,_tA.b,_tA.c)),_tD=B(_pY(_kj,_tC.a,_tC.b,_tC.c));return new T3(0,E(_tD.a),E(_tD.b),E(_tD.c));});return new T2(0,new T(function(){var _tE=E(_tk),_tF=E(_ti);return new T4(0,E(_ty),E(new T2(0,E(_tr.a)/E(_sQ),E(_tE))),E(_tF),E(_tz));}),new T2(0,_ty,_tz));}),_tG=new T(function(){var _tH=B(_to(_tr.b,new T(function(){return E(E(_ts).b);})));return new T2(0,_tH.a,_tH.b);});return new T2(0,new T2(1,new T(function(){return E(E(_ts).a);}),new T(function(){return E(E(_tG).a);})),new T(function(){return E(E(_tG).b);}));}},_tI=function(_tJ,_tK,_tL,_tM,_tN){var _tO=E(_tJ);if(!_tO._){return new T2(0,_w,new T2(0,new T3(0,E(_tK),E(_tL),E(_tM)),_tN));}else{var _tP=new T(function(){var _tQ=B(_qn(_pN,new T(function(){var _tR=E(_tN),_tS=E(_tm);return new T3(0,E(_tK)+E(_tR.a)*E(_tS.a),E(_tL)+E(_tR.b)*E(_tS.b),E(_tM)+E(_tR.c)*E(_tS.c));}))),_tT=_tQ.a,_tU=new T(function(){var _tV=E(_tQ.b),_tW=E(_tN),_tX=B(_qO(_kj,_tW.a,_tW.b,_tW.c,_tV.a,_tV.b,_tV.c)),_tY=B(_pY(_kj,_tX.a,_tX.b,_tX.c));return new T3(0,E(_tY.a),E(_tY.b),E(_tY.c));});return new T2(0,new T(function(){var _tZ=E(_tk),_u0=E(_ti);return new T4(0,E(_tT),E(new T2(0,E(_tO.a)/E(_sQ),E(_tZ))),E(_u0),E(_tU));}),new T2(0,_tT,_tU));}),_u1=new T(function(){var _u2=B(_to(_tO.b,new T(function(){return E(E(_tP).b);})));return new T2(0,_u2.a,_u2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_tP).a);}),new T(function(){return E(E(_u1).a);})),new T(function(){return E(E(_u1).b);}));}};return E(B(_tI(_sS,_sX,_sY,_sZ,new T(function(){var _u3=E(_t9),_u4=E(_ti)+_t0,_u5=Math.cos(_u4),_u6=Math.sin(_u4);return new T3(0,E(_t2)*_u5+E(_u3.a)*_u6,E(_t3)*_u5+E(_u3.b)*_u6,E(_t4)*_u5+E(_u3.c)*_u6);}))).a);});return new T2(0,new T(function(){var _u7=E(_tk),_u8=E(_ti);return new T4(0,E(new T3(0,E(_sX),E(_sY),E(_sZ))),E(new T2(0,E(_rp),E(_u7))),E(_u8),E(_rq));}),_tl);};return B(_pB(_tg,_sA));}),_u9=new T(function(){var _ua=function(_ub){return new F(function(){return A1(_sU,new T(function(){return B(_jK(_ub,_s8));}));});},_uc=B(_pB(_ua,_sA));if(!_uc._){return E(_sM);}else{return B(_rr(_uc.b,E(_uc.a)));}}),_ud=new T(function(){var _ue=new T(function(){var _uf=B(_n(_t8,new T2(1,new T(function(){var _ug=E(_t8);if(!_ug._){return E(_rC);}else{return E(_ug.a);}}),_w)));if(!_uf._){return E(_rO);}else{return E(_uf.b);}},1);return B(_rU(_t8,_ue));});return new T3(0,_ud,new T(function(){return B(_pB(_sJ,_t8));}),_u9);},_uh=function(_ui,_uj,_uk,_ul,_um,_un,_uo,_up,_uq,_ur,_us,_ut,_uu,_uv,_uw,_ux,_uy,_uz){var _uA=B(_qn(_pN,new T3(0,E(_ul),E(_um),E(_un)))),_uB=_uA.b,_uC=E(_uA.a),_uD=B(_r2(_kj,_p9,_uB,new T3(0,E(_up),E(_uq),E(_ur)))),_uE=E(_uB),_uF=_uE.a,_uG=_uE.b,_uH=_uE.c,_uI=B(_qO(_kj,_ut,_uu,_uv,_uF,_uG,_uH)),_uJ=B(_pY(_kj,_uI.a,_uI.b,_uI.c)),_uK=_uJ.a,_uL=_uJ.b,_uM=_uJ.c,_uN=E(_uo),_uO=new T2(0,E(new T3(0,E(_uD.a),E(_uD.b),E(_uD.c))),E(_us)),_uP=B(_sT(_ui,_uj,_uk,_uC.a,_uC.b,_uC.c,_uN,_uO,_uK,_uL,_uM,_uF,_uG,_uH)),_uQ=__lst2arr(B(_pB(_pK,_uP.a))),_uR=__lst2arr(B(_pB(_pv,_uP.b)));return {_:0,a:_ui,b:_uj,c:_uk,d:new T2(0,E(_uC),E(_uN)),e:_uO,f:new T3(0,E(_uK),E(_uL),E(_uM)),g:_uE,h:_uQ,i:_uR,j:E(_uP.c)};},_uS=1.0e-2,_uT=function(_uU,_uV,_uW,_uX,_uY,_uZ,_v0,_v1,_v2,_v3,_v4,_v5,_v6,_v7,_v8,_v9,_va,_vb){var _vc=B(_of(_jN,_v1,_v2,_v3,_v4,_uS,_uS,_uS,_uS)),_vd=E(_vc.a),_ve=B(_oq(_jN,_uX,_uY,_uZ,_v0,_vd.a,_vd.b,_vd.c,_vc.b)),_vf=E(_ve.a);return new F(function(){return _uh(_uU,_uV,_uW,_vf.a,_vf.b,_vf.c,_ve.b,_v1,_v2,_v3,_v4,_v5,_v6,_v7,_v8,_v9,_va,_vb);});},_vg=function(_vh){var _vi=E(_vh),_vj=E(_vi.d),_vk=E(_vj.a),_vl=E(_vi.e),_vm=E(_vl.a),_vn=E(_vi.f),_vo=B(_uT(_vi.a,_vi.b,_vi.c,_vk.a,_vk.b,_vk.c,_vj.b,_vm.a,_vm.b,_vm.c,_vl.b,_vn.a,_vn.b,_vn.c,_vi.g,_vi.h,_vi.i,_vi.j));return {_:0,a:E(_vo.a),b:E(_vo.b),c:E(_vo.c),d:E(_vo.d),e:E(_vo.e),f:E(_vo.f),g:E(_vo.g),h:_vo.h,i:_vo.i,j:_vo.j};},_vp=function(_vq,_vr,_vs,_vt,_vu,_vv,_vw,_vx,_vy){var _vz=B(_8s(B(_8q(_vq))));return new F(function(){return A3(_86,_vz,new T(function(){return B(_pO(_vq,_vr,_vs,_vt,_vv,_vw,_vx));}),new T(function(){return B(A3(_8u,_vz,_vu,_vy));}));});},_vA=new T(function(){return B(unCStr("base"));}),_vB=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_vC=new T(function(){return B(unCStr("IOException"));}),_vD=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_vA,_vB,_vC),_vE=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_vD,_w,_w),_vF=function(_vG){return E(_vE);},_vH=function(_vI){var _vJ=E(_vI);return new F(function(){return _3G(B(_3E(_vJ.a)),_vF,_vJ.b);});},_vK=new T(function(){return B(unCStr(": "));}),_vL=new T(function(){return B(unCStr(")"));}),_vM=new T(function(){return B(unCStr(" ("));}),_vN=new T(function(){return B(unCStr("interrupted"));}),_vO=new T(function(){return B(unCStr("system error"));}),_vP=new T(function(){return B(unCStr("unsatisified constraints"));}),_vQ=new T(function(){return B(unCStr("user error"));}),_vR=new T(function(){return B(unCStr("permission denied"));}),_vS=new T(function(){return B(unCStr("illegal operation"));}),_vT=new T(function(){return B(unCStr("end of file"));}),_vU=new T(function(){return B(unCStr("resource exhausted"));}),_vV=new T(function(){return B(unCStr("resource busy"));}),_vW=new T(function(){return B(unCStr("does not exist"));}),_vX=new T(function(){return B(unCStr("already exists"));}),_vY=new T(function(){return B(unCStr("resource vanished"));}),_vZ=new T(function(){return B(unCStr("timeout"));}),_w0=new T(function(){return B(unCStr("unsupported operation"));}),_w1=new T(function(){return B(unCStr("hardware fault"));}),_w2=new T(function(){return B(unCStr("inappropriate type"));}),_w3=new T(function(){return B(unCStr("invalid argument"));}),_w4=new T(function(){return B(unCStr("failed"));}),_w5=new T(function(){return B(unCStr("protocol error"));}),_w6=function(_w7,_w8){switch(E(_w7)){case 0:return new F(function(){return _n(_vX,_w8);});break;case 1:return new F(function(){return _n(_vW,_w8);});break;case 2:return new F(function(){return _n(_vV,_w8);});break;case 3:return new F(function(){return _n(_vU,_w8);});break;case 4:return new F(function(){return _n(_vT,_w8);});break;case 5:return new F(function(){return _n(_vS,_w8);});break;case 6:return new F(function(){return _n(_vR,_w8);});break;case 7:return new F(function(){return _n(_vQ,_w8);});break;case 8:return new F(function(){return _n(_vP,_w8);});break;case 9:return new F(function(){return _n(_vO,_w8);});break;case 10:return new F(function(){return _n(_w5,_w8);});break;case 11:return new F(function(){return _n(_w4,_w8);});break;case 12:return new F(function(){return _n(_w3,_w8);});break;case 13:return new F(function(){return _n(_w2,_w8);});break;case 14:return new F(function(){return _n(_w1,_w8);});break;case 15:return new F(function(){return _n(_w0,_w8);});break;case 16:return new F(function(){return _n(_vZ,_w8);});break;case 17:return new F(function(){return _n(_vY,_w8);});break;default:return new F(function(){return _n(_vN,_w8);});}},_w9=new T(function(){return B(unCStr("}"));}),_wa=new T(function(){return B(unCStr("{handle: "));}),_wb=function(_wc,_wd,_we,_wf,_wg,_wh){var _wi=new T(function(){var _wj=new T(function(){var _wk=new T(function(){var _wl=E(_wf);if(!_wl._){return E(_wh);}else{var _wm=new T(function(){return B(_n(_wl,new T(function(){return B(_n(_vL,_wh));},1)));},1);return B(_n(_vM,_wm));}},1);return B(_w6(_wd,_wk));}),_wn=E(_we);if(!_wn._){return E(_wj);}else{return B(_n(_wn,new T(function(){return B(_n(_vK,_wj));},1)));}}),_wo=E(_wg);if(!_wo._){var _wp=E(_wc);if(!_wp._){return E(_wi);}else{var _wq=E(_wp.a);if(!_wq._){var _wr=new T(function(){var _ws=new T(function(){return B(_n(_w9,new T(function(){return B(_n(_vK,_wi));},1)));},1);return B(_n(_wq.a,_ws));},1);return new F(function(){return _n(_wa,_wr);});}else{var _wt=new T(function(){var _wu=new T(function(){return B(_n(_w9,new T(function(){return B(_n(_vK,_wi));},1)));},1);return B(_n(_wq.a,_wu));},1);return new F(function(){return _n(_wa,_wt);});}}}else{return new F(function(){return _n(_wo.a,new T(function(){return B(_n(_vK,_wi));},1));});}},_wv=function(_ww){var _wx=E(_ww);return new F(function(){return _wb(_wx.a,_wx.b,_wx.c,_wx.d,_wx.f,_w);});},_wy=function(_wz,_wA,_wB){var _wC=E(_wA);return new F(function(){return _wb(_wC.a,_wC.b,_wC.c,_wC.d,_wC.f,_wB);});},_wD=function(_wE,_wF){var _wG=E(_wE);return new F(function(){return _wb(_wG.a,_wG.b,_wG.c,_wG.d,_wG.f,_wF);});},_wH=function(_wI,_wJ){return new F(function(){return _49(_wD,_wI,_wJ);});},_wK=new T3(0,_wy,_wv,_wH),_wL=new T(function(){return new T5(0,_vF,_wK,_wM,_vH,_wv);}),_wM=function(_wN){return new T2(0,_wL,_wN);},_wO=__Z,_wP=7,_wQ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_wR=new T6(0,_wO,_wP,_w,_wQ,_wO,_wO),_wS=new T(function(){return B(_wM(_wR));}),_wT=function(_){return new F(function(){return die(_wS);});},_wU=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_wV=new T6(0,_wO,_wP,_w,_wU,_wO,_wO),_wW=new T(function(){return B(_wM(_wV));}),_wX=function(_){return new F(function(){return die(_wW);});},_wY=function(_wZ,_){return new T2(0,_w,_wZ);},_x0=0.6,_x1=1,_x2=new T(function(){return B(unCStr(")"));}),_x3=function(_x4,_x5){var _x6=new T(function(){var _x7=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_iD(0,_x4,_w)),_x2));})));},1);return B(_n(B(_iD(0,_x5,_w)),_x7));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_x6)));});},_x8=function(_x9,_xa){var _xb=new T(function(){var _xc=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_iD(0,_xa,_w)),_x2));})));},1);return B(_n(B(_iD(0,_x9,_w)),_xc));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_xb)));});},_xd=function(_xe){var _xf=E(_xe);if(!_xf._){return E(_wY);}else{var _xg=new T(function(){return B(_xd(_xf.b));}),_xh=function(_xi){var _xj=E(_xi);if(!_xj._){return E(_xg);}else{var _xk=_xj.a,_xl=new T(function(){return B(_xh(_xj.b));}),_xm=new T(function(){return 0.1*E(E(_xk).e)/1.0e-2;}),_xn=new T(function(){var _xo=E(_xk);if(_xo.a!=_xo.b){return E(_x1);}else{return E(_x0);}}),_xp=function(_xq,_){var _xr=E(_xq),_xs=_xr.c,_xt=_xr.d,_xu=E(_xr.a),_xv=E(_xr.b),_xw=E(_xk),_xx=_xw.a,_xy=_xw.b,_xz=E(_xw.c),_xA=_xz.b,_xB=E(_xz.a),_xC=_xB.a,_xD=_xB.b,_xE=_xB.c,_xF=E(_xw.d),_xG=_xF.b,_xH=E(_xF.a),_xI=_xH.a,_xJ=_xH.b,_xK=_xH.c;if(_xu>_xx){return new F(function(){return _wX(_);});}else{if(_xx>_xv){return new F(function(){return _wX(_);});}else{if(_xu>_xy){return new F(function(){return _wT(_);});}else{if(_xy>_xv){return new F(function(){return _wT(_);});}else{var _xL=_xx-_xu|0;if(0>_xL){return new F(function(){return _x3(_xs,_xL);});}else{if(_xL>=_xs){return new F(function(){return _x3(_xs,_xL);});}else{var _xM=E(_xt[_xL]),_xN=E(_xM.c),_xO=_xN.b,_xP=E(_xN.a),_xQ=_xP.a,_xR=_xP.b,_xS=_xP.c,_xT=E(_xM.e),_xU=E(_xT.a),_xV=B(_of(_jN,_xC,_xD,_xE,_xA,_xQ,_xR,_xS,_xO)),_xW=E(_xV.a),_xX=B(_of(_jN,_xW.a,_xW.b,_xW.c,_xV.b,_xC,_xD,_xE,_xA)),_xY=E(_xX.a),_xZ=_xy-_xu|0;if(0>_xZ){return new F(function(){return _x8(_xZ,_xs);});}else{if(_xZ>=_xs){return new F(function(){return _x8(_xZ,_xs);});}else{var _y0=E(_xt[_xZ]),_y1=E(_y0.c),_y2=_y1.b,_y3=E(_y1.a),_y4=_y3.a,_y5=_y3.b,_y6=_y3.c,_y7=E(_y0.e),_y8=E(_y7.a),_y9=B(_of(_jN,_xI,_xJ,_xK,_xG,_y4,_y5,_y6,_y2)),_ya=E(_y9.a),_yb=B(_of(_jN,_ya.a,_ya.b,_ya.c,_y9.b,_xI,_xJ,_xK,_xG)),_yc=E(_yb.a),_yd=E(_xY.a)+E(_xY.b)+E(_xY.c)+E(_xX.b)+E(_yc.a)+E(_yc.b)+E(_yc.c)+E(_yb.b);if(!_yd){var _ye=B(A2(_xl,_xr,_));return new T2(0,new T2(1,_ii,new T(function(){return E(E(_ye).a);})),new T(function(){return E(E(_ye).b);}));}else{var _yf=new T(function(){return  -((B(_vp(_kj,_xU.a,_xU.b,_xU.c,_xT.b,_xC,_xD,_xE,_xA))-B(_vp(_kj,_y8.a,_y8.b,_y8.c,_y7.b,_xI,_xJ,_xK,_xG))-E(_xm))/_yd);}),_yg=function(_yh,_yi,_yj,_yk,_){var _yl=new T(function(){var _ym=function(_yn,_yo,_yp,_yq,_yr){if(_yn>_xy){return E(_yr);}else{if(_xy>_yo){return E(_yr);}else{var _ys=function(_){var _yt=newArr(_yp,_nA),_yu=_yt,_yv=function(_yw,_){while(1){if(_yw!=_yp){var _=_yu[_yw]=_yq[_yw],_yx=_yw+1|0;_yw=_yx;continue;}else{return E(_);}}},_=B(_yv(0,_)),_yy=_xy-_yn|0;if(0>_yy){return new F(function(){return _x8(_yy,_yp);});}else{if(_yy>=_yp){return new F(function(){return _x8(_yy,_yp);});}else{var _=_yu[_yy]=new T(function(){var _yz=E(_yq[_yy]),_yA=E(_yz.e),_yB=E(_yA.a),_yC=B(_of(_jN,_y4,_y5,_y6,_y2,_xI,_xJ,_xK,_xG)),_yD=E(_yC.a),_yE=E(_yf)*E(_xn),_yF=B(_of(_jN,_yD.a,_yD.b,_yD.c,_yC.b,_yE,_yE,_yE,_yE)),_yG=E(_yF.a),_yH=B(_oq(_jN,_yB.a,_yB.b,_yB.c,_yA.b, -E(_yG.a), -E(_yG.b), -E(_yG.c), -E(_yF.b)));return {_:0,a:E(_yz.a),b:E(_yz.b),c:E(_yz.c),d:E(_yz.d),e:E(new T2(0,E(_yH.a),E(_yH.b))),f:E(_yz.f),g:E(_yz.g),h:_yz.h,i:_yz.i,j:_yz.j};});return new T4(0,E(_yn),E(_yo),_yp,_yu);}}};return new F(function(){return _nF(_ys);});}}};if(_yh>_xx){return B(_ym(_yh,_yi,_yj,_yk,new T4(0,E(_yh),E(_yi),_yj,_yk)));}else{if(_xx>_yi){return B(_ym(_yh,_yi,_yj,_yk,new T4(0,E(_yh),E(_yi),_yj,_yk)));}else{var _yI=function(_){var _yJ=newArr(_yj,_nA),_yK=_yJ,_yL=function(_yM,_){while(1){if(_yM!=_yj){var _=_yK[_yM]=_yk[_yM],_yN=_yM+1|0;_yM=_yN;continue;}else{return E(_);}}},_=B(_yL(0,_)),_yO=_xx-_yh|0;if(0>_yO){return new F(function(){return _x3(_yj,_yO);});}else{if(_yO>=_yj){return new F(function(){return _x3(_yj,_yO);});}else{var _=_yK[_yO]=new T(function(){var _yP=E(_yk[_yO]),_yQ=E(_yP.e),_yR=E(_yQ.a),_yS=B(_of(_jN,_xQ,_xR,_xS,_xO,_xC,_xD,_xE,_xA)),_yT=E(_yS.a),_yU=E(_yf)*E(_xn),_yV=B(_of(_jN,_yT.a,_yT.b,_yT.c,_yS.b,_yU,_yU,_yU,_yU)),_yW=E(_yV.a),_yX=B(_oq(_jN,_yR.a,_yR.b,_yR.c,_yQ.b,_yW.a,_yW.b,_yW.c,_yV.b));return {_:0,a:E(_yP.a),b:E(_yP.b),c:E(_yP.c),d:E(_yP.d),e:E(new T2(0,E(_yX.a),E(_yX.b))),f:E(_yP.f),g:E(_yP.g),h:_yP.h,i:_yP.i,j:_yP.j};});return new T4(0,E(_yh),E(_yi),_yj,_yK);}}},_yY=B(_nF(_yI));return B(_ym(E(_yY.a),E(_yY.b),_yY.c,_yY.d,_yY));}}});return new T2(0,_ii,_yl);};if(!E(_xw.f)){var _yZ=B(_yg(_xu,_xv,_xs,_xt,_)),_z0=B(A2(_xl,new T(function(){return E(E(_yZ).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_yZ).a);}),new T(function(){return E(E(_z0).a);})),new T(function(){return E(E(_z0).b);}));}else{if(E(_yf)<0){var _z1=B(A2(_xl,_xr,_));return new T2(0,new T2(1,_ii,new T(function(){return E(E(_z1).a);})),new T(function(){return E(E(_z1).b);}));}else{var _z2=B(_yg(_xu,_xv,_xs,_xt,_)),_z3=B(A2(_xl,new T(function(){return E(E(_z2).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_z2).a);}),new T(function(){return E(E(_z3).a);})),new T(function(){return E(E(_z3).b);}));}}}}}}}}}}}};return E(_xp);}};return new F(function(){return _xh(_xf.a);});}},_z4=function(_,_z5){var _z6=new T(function(){return B(_xd(E(_z5).a));}),_z7=function(_z8){var _z9=E(_z8);return (_z9==1)?E(new T2(1,_z6,_w)):new T2(1,_z6,new T(function(){return B(_z7(_z9-1|0));}));},_za=B(_nk(B(_z7(5)),new T(function(){return E(E(_z5).b);}),_)),_zb=new T(function(){return B(_nZ(_nj,_j5,_vg,new T(function(){return E(E(_za).b);})));});return new T2(0,_ii,_zb);},_zc=function(_zd,_ze,_zf,_zg,_zh){var _zi=B(_8s(B(_8q(_zd))));return new F(function(){return A3(_86,_zi,new T(function(){return B(A3(_8u,_zi,_ze,_zg));}),new T(function(){return B(A3(_8u,_zi,_zf,_zh));}));});},_zj=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_zk=new T6(0,_wO,_wP,_w,_zj,_wO,_wO),_zl=new T(function(){return B(_wM(_zk));}),_zm=function(_){return new F(function(){return die(_zl);});},_zn=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_zo=new T6(0,_wO,_wP,_w,_zn,_wO,_wO),_zp=new T(function(){return B(_wM(_zo));}),_zq=function(_){return new F(function(){return die(_zp);});},_zr=false,_zs=true,_zt=function(_zu){var _zv=E(_zu),_zw=_zv.b,_zx=E(_zv.d),_zy=E(_zv.e),_zz=E(_zy.a),_zA=E(_zv.g),_zB=B(A1(_zw,_zx.a)),_zC=B(_qO(_kj,_zB.a,_zB.b,_zB.c,_zA.a,_zA.b,_zA.c));return {_:0,a:E(_zv.a),b:E(_zw),c:E(_zv.c),d:E(_zx),e:E(new T2(0,E(new T3(0,E(_zz.a)+E(_zC.a)*1.0e-2,E(_zz.b)+E(_zC.b)*1.0e-2,E(_zz.c)+E(_zC.c)*1.0e-2)),E(_zy.b))),f:E(_zv.f),g:E(_zA),h:_zv.h,i:_zv.i,j:_zv.j};},_zD=new T(function(){return eval("__strict(collideBound)");}),_zE=new T(function(){return eval("__strict(mouseContact)");}),_zF=new T(function(){return eval("__strict(collide)");}),_zG=function(_zH){var _zI=E(_zH);if(!_zI._){return __Z;}else{return new F(function(){return _n(_zI.a,new T(function(){return B(_zG(_zI.b));},1));});}},_zJ=0,_zK=new T3(0,E(_zJ),E(_zJ),E(_zJ)),_zL=new T2(0,E(_zK),E(_zJ)),_zM=new T2(0,_kj,_p9),_zN=new T(function(){return B(_hP(_zM));}),_zO=function(_zP,_){var _zQ=B(_nZ(_nj,_j5,_zt,_zP)),_zR=E(_zQ.a),_zS=E(_zQ.b);if(_zR<=_zS){var _zT=function(_zU,_zV,_zW,_zX,_zY,_){if(_zV>_zU){return new F(function(){return _zq(_);});}else{if(_zU>_zW){return new F(function(){return _zq(_);});}else{var _zZ=new T(function(){var _A0=_zU-_zV|0;if(0>_A0){return B(_x8(_A0,_zX));}else{if(_A0>=_zX){return B(_x8(_A0,_zX));}else{return E(_zY[_A0]);}}}),_A1=function(_A2,_A3,_A4,_A5,_A6,_){var _A7=E(_A2);if(!_A7._){return new T2(0,_w,new T4(0,E(_A3),E(_A4),_A5,_A6));}else{var _A8=E(_A7.a);if(_A3>_A8){return new F(function(){return _zm(_);});}else{if(_A8>_A4){return new F(function(){return _zm(_);});}else{var _A9=_A8-_A3|0;if(0>_A9){return new F(function(){return _x3(_A5,_A9);});}else{if(_A9>=_A5){return new F(function(){return _x3(_A5,_A9);});}else{var _Aa=__app2(E(_zF),B(_it(E(_zZ))),B(_it(E(_A6[_A9])))),_Ab=__arr2lst(0,_Aa),_Ac=B(_kW(_Ab,_)),_Ad=B(_A1(_A7.b,_A3,_A4,_A5,_A6,_)),_Ae=new T(function(){var _Af=new T(function(){return _zU!=_A8;}),_Ag=function(_Ah){var _Ai=E(_Ah);if(!_Ai._){return __Z;}else{var _Aj=_Ai.b,_Ak=E(_Ai.a),_Al=E(_Ak.b),_Am=E(_Ak.a),_An=E(_Ak.c),_Ao=_An.a,_Ap=_An.b,_Aq=E(_Ak.e),_Ar=E(_Ak.d),_As=_Ar.a,_At=_Ar.b,_Au=E(_Ak.f),_Av=new T(function(){var _Aw=B(_pY(_kj,_Au.a,_Au.b,_Au.c)),_Ax=Math.sqrt(B(_zc(_kj,_As,_At,_As,_At)));return new T3(0,_Ax*E(_Aw.a),_Ax*E(_Aw.b),_Ax*E(_Aw.c));}),_Ay=new T(function(){var _Az=B(_pY(_kj,_Aq.a,_Aq.b,_Aq.c)),_AA=Math.sqrt(B(_zc(_kj,_Ao,_Ap,_Ao,_Ap)));return new T3(0,_AA*E(_Az.a),_AA*E(_Az.b),_AA*E(_Az.c));}),_AB=new T(function(){var _AC=B(A1(_zN,_Al)),_AD=B(_pY(_kj,_AC.a,_AC.b,_AC.c));return new T3(0,E(_AD.a),E(_AD.b),E(_AD.c));}),_AE=new T(function(){var _AF=B(A1(_zN,_Am)),_AG=B(_pY(_kj,_AF.a,_AF.b,_AF.c));return new T3(0,E(_AG.a),E(_AG.b),E(_AG.c));}),_AH=E(_Al.a)+ -E(_Am.a),_AI=E(_Al.b)+ -E(_Am.b),_AJ=E(_Al.c)+ -E(_Am.c),_AK=new T(function(){return Math.sqrt(B(_pO(_kj,_AH,_AI,_AJ,_AH,_AI,_AJ)));}),_AL=new T(function(){var _AM=1/E(_AK);return new T3(0,_AH*_AM,_AI*_AM,_AJ*_AM);}),_AN=new T(function(){if(!E(_Ak.g)){return E(_AL);}else{var _AO=E(_AL);return new T3(0,-1*E(_AO.a),-1*E(_AO.b),-1*E(_AO.c));}}),_AP=new T(function(){if(!E(_Ak.h)){return E(_AL);}else{var _AQ=E(_AL);return new T3(0,-1*E(_AQ.a),-1*E(_AQ.b),-1*E(_AQ.c));}});return (!E(_Af))?new T2(1,new T(function(){var _AR=E(_AN),_AS=E(_AR.b),_AT=E(_AR.c),_AU=E(_AR.a),_AV=E(_AE),_AW=E(_AV.c),_AX=E(_AV.b),_AY=E(_AV.a),_AZ=E(_Ay),_B0=E(_AZ.c),_B1=E(_AZ.b),_B2=E(_AZ.a),_B3=_AS*_AW-_AX*_AT,_B4=_AT*_AY-_AW*_AU,_B5=_AU*_AX-_AY*_AS,_B6=B(_pO(_kj,_B4*_B0-_B1*_B5,_B5*_B2-_B0*_B3,_B3*_B1-_B2*_B4,_AY,_AX,_AW));return new T6(0,_zU,_A8,E(new T2(0,E(new T3(0,E(_B3),E(_B4),E(_B5))),E(_B6))),E(_zL),_AK,_zr);}),new T2(1,new T(function(){var _B7=E(_AP),_B8=E(_B7.b),_B9=E(_B7.c),_Ba=E(_B7.a),_Bb=E(_AB),_Bc=E(_Bb.c),_Bd=E(_Bb.b),_Be=E(_Bb.a),_Bf=E(_Av),_Bg=E(_Bf.c),_Bh=E(_Bf.b),_Bi=E(_Bf.a),_Bj=_B8*_Bc-_Bd*_B9,_Bk=_B9*_Be-_Bc*_Ba,_Bl=_Ba*_Bd-_Be*_B8,_Bm=B(_pO(_kj,_Bk*_Bg-_Bh*_Bl,_Bl*_Bi-_Bg*_Bj,_Bj*_Bh-_Bi*_Bk,_Be,_Bd,_Bc));return new T6(0,_zU,_A8,E(_zL),E(new T2(0,E(new T3(0,E(_Bj),E(_Bk),E(_Bl))),E(_Bm))),_AK,_zr);}),new T(function(){return B(_Ag(_Aj));}))):new T2(1,new T(function(){var _Bn=E(_AN),_Bo=E(_Bn.b),_Bp=E(_Bn.c),_Bq=E(_Bn.a),_Br=E(_AE),_Bs=_Br.a,_Bt=_Br.b,_Bu=_Br.c,_Bv=B(_qO(_kj,_Bq,_Bo,_Bp,_Bs,_Bt,_Bu)),_Bw=E(_Ay),_Bx=E(_Bw.c),_By=E(_Bw.b),_Bz=E(_Bw.a),_BA=B(_pO(_kj,_Bo*_Bx-_By*_Bp,_Bp*_Bz-_Bx*_Bq,_Bq*_By-_Bz*_Bo,_Bs,_Bt,_Bu)),_BB=E(_AP),_BC=E(_BB.b),_BD=E(_BB.c),_BE=E(_BB.a),_BF=E(_AB),_BG=_BF.a,_BH=_BF.b,_BI=_BF.c,_BJ=B(_qO(_kj,_BE,_BC,_BD,_BG,_BH,_BI)),_BK=E(_Av),_BL=E(_BK.c),_BM=E(_BK.b),_BN=E(_BK.a),_BO=B(_pO(_kj,_BC*_BL-_BM*_BD,_BD*_BN-_BL*_BE,_BE*_BM-_BN*_BC,_BG,_BH,_BI));return new T6(0,_zU,_A8,E(new T2(0,E(new T3(0,E(_Bv.a),E(_Bv.b),E(_Bv.c))),E(_BA))),E(new T2(0,E(new T3(0,E(_BJ.a),E(_BJ.b),E(_BJ.c))),E(_BO))),_AK,_zs);}),new T(function(){return B(_Ag(_Aj));}));}};return B(_Ag(_Ac));});return new T2(0,new T2(1,_Ae,new T(function(){return E(E(_Ad).a);})),new T(function(){return E(E(_Ad).b);}));}}}}}},_BP=B(_A1(B(_mn(_zU,_zS)),_zV,_zW,_zX,_zY,_)),_BQ=E(_zZ),_BR=E(_BQ.d).a,_BS=__app1(E(_zD),B(_it(_BQ))),_BT=__arr2lst(0,_BS),_BU=B(_kW(_BT,_)),_BV=__app1(E(_zE),_zU),_BW=__arr2lst(0,_BV),_BX=B(_kW(_BW,_));if(_zU!=_zS){var _BY=E(_BP),_BZ=E(_BY.b),_C0=B(_zT(_zU+1|0,E(_BZ.a),E(_BZ.b),_BZ.c,_BZ.d,_)),_C1=new T(function(){var _C2=new T(function(){var _C3=B(A1(_zN,_BR)),_C4=B(_pY(_kj,_C3.a,_C3.b,_C3.c));return new T3(0,E(_C4.a),E(_C4.b),E(_C4.c));}),_C5=new T(function(){var _C6=new T(function(){return B(_zG(_BY.a));}),_C7=function(_C8){var _C9=E(_C8);if(!_C9._){return E(_C6);}else{var _Ca=E(_C9.a),_Cb=E(_Ca.b),_Cc=E(_Ca.a),_Cd=E(_Ca.c),_Ce=_Cd.a,_Cf=_Cd.b,_Cg=E(_Ca.e);return new T2(1,new T(function(){var _Ch=E(_Cb.a)+ -E(_Cc.a),_Ci=E(_Cb.b)+ -E(_Cc.b),_Cj=E(_Cb.c)+ -E(_Cc.c),_Ck=B(A1(_zN,_Cc)),_Cl=B(_pY(_kj,_Ck.a,_Ck.b,_Ck.c)),_Cm=_Cl.a,_Cn=_Cl.b,_Co=_Cl.c,_Cp=Math.sqrt(B(_pO(_kj,_Ch,_Ci,_Cj,_Ch,_Ci,_Cj))),_Cq=1/_Cp,_Cr=_Ch*_Cq,_Cs=_Ci*_Cq,_Ct=_Cj*_Cq,_Cu=B(_qO(_kj,_Cr,_Cs,_Ct,_Cm,_Cn,_Co)),_Cv=B(_pY(_kj,_Cg.a,_Cg.b,_Cg.c)),_Cw=Math.sqrt(B(_zc(_kj,_Ce,_Cf,_Ce,_Cf))),_Cx=_Cw*E(_Cv.a),_Cy=_Cw*E(_Cv.b),_Cz=_Cw*E(_Cv.c),_CA=B(_pO(_kj,_Cs*_Cz-_Cy*_Ct,_Ct*_Cx-_Cz*_Cr,_Cr*_Cy-_Cx*_Cs,_Cm,_Cn,_Co));return new T6(0,_zU,_zU,E(new T2(0,E(new T3(0,E(_Cu.a),E(_Cu.b),E(_Cu.c))),E(_CA))),E(_zL),_Cp,_zs);}),new T(function(){return B(_C7(_C9.b));}));}};return B(_C7(_BU));}),_CB=function(_CC){var _CD=E(_CC);if(!_CD._){return E(_C5);}else{var _CE=E(_CD.a),_CF=E(_CE.b),_CG=new T(function(){var _CH=E(_BR),_CI=E(_CF.c)+ -E(_CH.c),_CJ=E(_CF.b)+ -E(_CH.b),_CK=E(_CF.a)+ -E(_CH.a),_CL=Math.sqrt(B(_pO(_kj,_CK,_CJ,_CI,_CK,_CJ,_CI))),_CM=function(_CN,_CO,_CP){var _CQ=E(_C2),_CR=_CQ.a,_CS=_CQ.b,_CT=_CQ.c,_CU=B(_qO(_kj,_CN,_CO,_CP,_CR,_CS,_CT)),_CV=B(_pO(_kj,_CO*0-0*_CP,_CP*0-0*_CN,_CN*0-0*_CO,_CR,_CS,_CT));return new T6(0,_zU,_zU,new T2(0,E(new T3(0,E(_CU.a),E(_CU.b),E(_CU.c))),E(_CV)),_zL,_CL,_zs);};if(!E(_CE.g)){var _CW=1/_CL,_CX=B(_CM(_CK*_CW,_CJ*_CW,_CI*_CW));return new T6(0,_CX.a,_CX.b,E(_CX.c),E(_CX.d),_CX.e,_CX.f);}else{var _CY=1/_CL,_CZ=B(_CM(-1*_CK*_CY,-1*_CJ*_CY,-1*_CI*_CY));return new T6(0,_CZ.a,_CZ.b,E(_CZ.c),E(_CZ.d),_CZ.e,_CZ.f);}});return new T2(1,_CG,new T(function(){return B(_CB(_CD.b));}));}};return B(_CB(_BX));});return new T2(0,new T2(1,_C1,new T(function(){return E(E(_C0).a);})),new T(function(){return E(E(_C0).b);}));}else{var _D0=new T(function(){var _D1=new T(function(){var _D2=B(A1(_zN,_BR)),_D3=B(_pY(_kj,_D2.a,_D2.b,_D2.c));return new T3(0,E(_D3.a),E(_D3.b),E(_D3.c));}),_D4=new T(function(){var _D5=new T(function(){return B(_zG(E(_BP).a));}),_D6=function(_D7){var _D8=E(_D7);if(!_D8._){return E(_D5);}else{var _D9=E(_D8.a),_Da=E(_D9.b),_Db=E(_D9.a),_Dc=E(_D9.c),_Dd=_Dc.a,_De=_Dc.b,_Df=E(_D9.e);return new T2(1,new T(function(){var _Dg=E(_Da.a)+ -E(_Db.a),_Dh=E(_Da.b)+ -E(_Db.b),_Di=E(_Da.c)+ -E(_Db.c),_Dj=B(A1(_zN,_Db)),_Dk=B(_pY(_kj,_Dj.a,_Dj.b,_Dj.c)),_Dl=_Dk.a,_Dm=_Dk.b,_Dn=_Dk.c,_Do=Math.sqrt(B(_pO(_kj,_Dg,_Dh,_Di,_Dg,_Dh,_Di))),_Dp=1/_Do,_Dq=_Dg*_Dp,_Dr=_Dh*_Dp,_Ds=_Di*_Dp,_Dt=B(_qO(_kj,_Dq,_Dr,_Ds,_Dl,_Dm,_Dn)),_Du=B(_pY(_kj,_Df.a,_Df.b,_Df.c)),_Dv=Math.sqrt(B(_zc(_kj,_Dd,_De,_Dd,_De))),_Dw=_Dv*E(_Du.a),_Dx=_Dv*E(_Du.b),_Dy=_Dv*E(_Du.c),_Dz=B(_pO(_kj,_Dr*_Dy-_Dx*_Ds,_Ds*_Dw-_Dy*_Dq,_Dq*_Dx-_Dw*_Dr,_Dl,_Dm,_Dn));return new T6(0,_zU,_zU,E(new T2(0,E(new T3(0,E(_Dt.a),E(_Dt.b),E(_Dt.c))),E(_Dz))),E(_zL),_Do,_zs);}),new T(function(){return B(_D6(_D8.b));}));}};return B(_D6(_BU));}),_DA=function(_DB){var _DC=E(_DB);if(!_DC._){return E(_D4);}else{var _DD=E(_DC.a),_DE=E(_DD.b),_DF=new T(function(){var _DG=E(_BR),_DH=E(_DE.c)+ -E(_DG.c),_DI=E(_DE.b)+ -E(_DG.b),_DJ=E(_DE.a)+ -E(_DG.a),_DK=Math.sqrt(B(_pO(_kj,_DJ,_DI,_DH,_DJ,_DI,_DH))),_DL=function(_DM,_DN,_DO){var _DP=E(_D1),_DQ=_DP.a,_DR=_DP.b,_DS=_DP.c,_DT=B(_qO(_kj,_DM,_DN,_DO,_DQ,_DR,_DS)),_DU=B(_pO(_kj,_DN*0-0*_DO,_DO*0-0*_DM,_DM*0-0*_DN,_DQ,_DR,_DS));return new T6(0,_zU,_zU,new T2(0,E(new T3(0,E(_DT.a),E(_DT.b),E(_DT.c))),E(_DU)),_zL,_DK,_zs);};if(!E(_DD.g)){var _DV=1/_DK,_DW=B(_DL(_DJ*_DV,_DI*_DV,_DH*_DV));return new T6(0,_DW.a,_DW.b,E(_DW.c),E(_DW.d),_DW.e,_DW.f);}else{var _DX=1/_DK,_DY=B(_DL(-1*_DJ*_DX,-1*_DI*_DX,-1*_DH*_DX));return new T6(0,_DY.a,_DY.b,E(_DY.c),E(_DY.d),_DY.e,_DY.f);}});return new T2(1,_DF,new T(function(){return B(_DA(_DC.b));}));}};return B(_DA(_BX));});return new T2(0,new T2(1,_D0,_w),new T(function(){return E(E(_BP).b);}));}}}},_DZ=B(_zT(_zR,_zR,_zS,_zQ.c,_zQ.d,_));return new F(function(){return _z4(_,_DZ);});}else{return new F(function(){return _z4(_,new T2(0,_w,_zQ));});}},_E0=new T(function(){return eval("__strict(passObject)");}),_E1=new T(function(){return eval("__strict(refresh)");}),_E2=function(_E3,_){var _E4=__app0(E(_E1)),_E5=__app0(E(_iy)),_E6=E(_E3),_E7=_E6.c,_E8=_E6.d,_E9=E(_E6.a),_Ea=E(_E6.b);if(_E9<=_Ea){if(_E9>_Ea){return E(_iw);}else{if(0>=_E7){return new F(function(){return _iJ(_E7,0);});}else{var _Eb=E(_E0),_Ec=__app2(_Eb,_E9,B(_it(E(_E8[0]))));if(_E9!=_Ea){var _Ed=function(_Ee,_){if(_E9>_Ee){return E(_iw);}else{if(_Ee>_Ea){return E(_iw);}else{var _Ef=_Ee-_E9|0;if(0>_Ef){return new F(function(){return _iJ(_E7,_Ef);});}else{if(_Ef>=_E7){return new F(function(){return _iJ(_E7,_Ef);});}else{var _Eg=__app2(_Eb,_Ee,B(_it(E(_E8[_Ef]))));if(_Ee!=_Ea){var _Eh=B(_Ed(_Ee+1|0,_));return new T2(1,_ii,_Eh);}else{return _iO;}}}}}},_Ei=B(_Ed(_E9+1|0,_)),_Ej=__app0(E(_ix)),_Ek=B(_zO(_E6,_));return new T(function(){return E(E(_Ek).b);});}else{var _El=__app0(E(_ix)),_Em=B(_zO(_E6,_));return new T(function(){return E(E(_Em).b);});}}}}else{var _En=__app0(E(_ix)),_Eo=B(_zO(_E6,_));return new T(function(){return E(E(_Eo).b);});}},_Ep=new T(function(){return B(unCStr("Negative exponent"));}),_Eq=new T(function(){return B(err(_Ep));}),_Er=function(_Es,_Et,_Eu){while(1){if(!(_Et%2)){var _Ev=_Es*_Es,_Ew=quot(_Et,2);_Es=_Ev;_Et=_Ew;continue;}else{var _Ex=E(_Et);if(_Ex==1){return _Es*_Eu;}else{var _Ev=_Es*_Es,_Ey=_Es*_Eu;_Es=_Ev;_Et=quot(_Ex-1|0,2);_Eu=_Ey;continue;}}}},_Ez=function(_EA,_EB){while(1){if(!(_EB%2)){var _EC=_EA*_EA,_ED=quot(_EB,2);_EA=_EC;_EB=_ED;continue;}else{var _EE=E(_EB);if(_EE==1){return E(_EA);}else{return new F(function(){return _Er(_EA*_EA,quot(_EE-1|0,2),_EA);});}}}},_EF=function(_EG){var _EH=E(_EG);return new T3(0,E(_EH.c), -E(_EH.b), -E(_EH.a));},_EI=function(_){return new F(function(){return __jsNull();});},_EJ=function(_EK){var _EL=B(A1(_EK,_));return E(_EL);},_EM=new T(function(){return B(_EJ(_EI));}),_EN=function(_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0){var _F1=function(_F2){var _F3=E(_s8),_F4=2+_F2|0,_F5=_F4-1|0,_F6=(2+_F2)*(1+_F2),_F7=E(_sA);if(!_F7._){return _F3*0;}else{var _F8=_F7.a,_F9=_F7.b,_Fa=B(A1(_EO,new T(function(){return 6.283185307179586*E(_F8)/E(_rA);}))),_Fb=B(A1(_EO,new T(function(){return 6.283185307179586*(E(_F8)+1)/E(_rA);})));if(_Fa!=_Fb){if(_F4>=0){var _Fc=E(_F4);if(!_Fc){var _Fd=function(_Fe,_Ff){while(1){var _Fg=B((function(_Fh,_Fi){var _Fj=E(_Fh);if(!_Fj._){return E(_Fi);}else{var _Fk=_Fj.a,_Fl=_Fj.b,_Fm=B(A1(_EO,new T(function(){return 6.283185307179586*E(_Fk)/E(_rA);}))),_Fn=B(A1(_EO,new T(function(){return 6.283185307179586*(E(_Fk)+1)/E(_rA);})));if(_Fm!=_Fn){var _Fo=_Fi+0/(_Fm-_Fn)/_F6;_Fe=_Fl;_Ff=_Fo;return __continue;}else{if(_F5>=0){var _Fp=E(_F5);if(!_Fp){var _Fo=_Fi+_F4/_F6;_Fe=_Fl;_Ff=_Fo;return __continue;}else{var _Fo=_Fi+_F4*B(_Ez(_Fm,_Fp))/_F6;_Fe=_Fl;_Ff=_Fo;return __continue;}}else{return E(_Eq);}}}})(_Fe,_Ff));if(_Fg!=__continue){return _Fg;}}};return _F3*B(_Fd(_F9,0/(_Fa-_Fb)/_F6));}else{var _Fq=function(_Fr,_Fs){while(1){var _Ft=B((function(_Fu,_Fv){var _Fw=E(_Fu);if(!_Fw._){return E(_Fv);}else{var _Fx=_Fw.a,_Fy=_Fw.b,_Fz=B(A1(_EO,new T(function(){return 6.283185307179586*E(_Fx)/E(_rA);}))),_FA=B(A1(_EO,new T(function(){return 6.283185307179586*(E(_Fx)+1)/E(_rA);})));if(_Fz!=_FA){if(_Fc>=0){var _FB=_Fv+(B(_Ez(_Fz,_Fc))-B(_Ez(_FA,_Fc)))/(_Fz-_FA)/_F6;_Fr=_Fy;_Fs=_FB;return __continue;}else{return E(_Eq);}}else{if(_F5>=0){var _FC=E(_F5);if(!_FC){var _FB=_Fv+_F4/_F6;_Fr=_Fy;_Fs=_FB;return __continue;}else{var _FB=_Fv+_F4*B(_Ez(_Fz,_FC))/_F6;_Fr=_Fy;_Fs=_FB;return __continue;}}else{return E(_Eq);}}}})(_Fr,_Fs));if(_Ft!=__continue){return _Ft;}}};return _F3*B(_Fq(_F9,(B(_Ez(_Fa,_Fc))-B(_Ez(_Fb,_Fc)))/(_Fa-_Fb)/_F6));}}else{return E(_Eq);}}else{if(_F5>=0){var _FD=E(_F5);if(!_FD){var _FE=function(_FF,_FG){while(1){var _FH=B((function(_FI,_FJ){var _FK=E(_FI);if(!_FK._){return E(_FJ);}else{var _FL=_FK.a,_FM=_FK.b,_FN=B(A1(_EO,new T(function(){return 6.283185307179586*E(_FL)/E(_rA);}))),_FO=B(A1(_EO,new T(function(){return 6.283185307179586*(E(_FL)+1)/E(_rA);})));if(_FN!=_FO){if(_F4>=0){var _FP=E(_F4);if(!_FP){var _FQ=_FJ+0/(_FN-_FO)/_F6;_FF=_FM;_FG=_FQ;return __continue;}else{var _FQ=_FJ+(B(_Ez(_FN,_FP))-B(_Ez(_FO,_FP)))/(_FN-_FO)/_F6;_FF=_FM;_FG=_FQ;return __continue;}}else{return E(_Eq);}}else{var _FQ=_FJ+_F4/_F6;_FF=_FM;_FG=_FQ;return __continue;}}})(_FF,_FG));if(_FH!=__continue){return _FH;}}};return _F3*B(_FE(_F9,_F4/_F6));}else{var _FR=function(_FS,_FT){while(1){var _FU=B((function(_FV,_FW){var _FX=E(_FV);if(!_FX._){return E(_FW);}else{var _FY=_FX.a,_FZ=_FX.b,_G0=B(A1(_EO,new T(function(){return 6.283185307179586*E(_FY)/E(_rA);}))),_G1=B(A1(_EO,new T(function(){return 6.283185307179586*(E(_FY)+1)/E(_rA);})));if(_G0!=_G1){if(_F4>=0){var _G2=E(_F4);if(!_G2){var _G3=_FW+0/(_G0-_G1)/_F6;_FS=_FZ;_FT=_G3;return __continue;}else{var _G3=_FW+(B(_Ez(_G0,_G2))-B(_Ez(_G1,_G2)))/(_G0-_G1)/_F6;_FS=_FZ;_FT=_G3;return __continue;}}else{return E(_Eq);}}else{if(_FD>=0){var _G3=_FW+_F4*B(_Ez(_G0,_FD))/_F6;_FS=_FZ;_FT=_G3;return __continue;}else{return E(_Eq);}}}})(_FS,_FT));if(_FU!=__continue){return _FU;}}};return _F3*B(_FR(_F9,_F4*B(_Ez(_Fa,_FD))/_F6));}}else{return E(_Eq);}}}},_G4=E(_EM),_G5=1/(B(_F1(1))*_EP);return new F(function(){return _uh(_EO,_EF,new T2(0,E(new T3(0,E(_G5),E(_G5),E(_G5))),1/(B(_F1(3))*_EP)),_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_rq,_G4,_G4,0);});},_G6=0.5,_G7=1,_G8=0,_G9=0.3,_Ga=function(_Gb){return E(_G9);},_Gc=new T(function(){var _Gd=B(_EN(_Ga,1.2,_G8,_G7,_G6,_G8,_G8,_G8,_G8,_G8,_G7,_G7,_G7));return {_:0,a:E(_Gd.a),b:E(_Gd.b),c:E(_Gd.c),d:E(_Gd.d),e:E(_Gd.e),f:E(_Gd.f),g:E(_Gd.g),h:_Gd.h,i:_Gd.i,j:_Gd.j};}),_Ge=0,_Gf=function(_){var _Gg=newArr(1,_nA),_=_Gg[0]=_Gc;return new T4(0,E(_Ge),E(_Ge),1,_Gg);},_Gh=new T(function(){return B(_nF(_Gf));}),_Gi=function(_Gj,_){while(1){var _Gk=E(_Gj);if(!_Gk._){return _ii;}else{var _Gl=_Gk.b,_Gm=E(_Gk.a);switch(_Gm._){case 0:var _Gn=B(A1(_Gm.a,_));_Gj=B(_n(_Gl,new T2(1,_Gn,_w)));continue;case 1:_Gj=B(_n(_Gl,_Gm.a));continue;default:_Gj=_Gl;continue;}}}},_Go=function(_Gp,_Gq,_){var _Gr=E(_Gp);switch(_Gr._){case 0:var _Gs=B(A1(_Gr.a,_));return new F(function(){return _Gi(B(_n(_Gq,new T2(1,_Gs,_w))),_);});break;case 1:return new F(function(){return _Gi(B(_n(_Gq,_Gr.a)),_);});break;default:return new F(function(){return _Gi(_Gq,_);});}},_Gt=new T0(2),_Gu=function(_Gv){return new T0(2);},_Gw=function(_Gx,_Gy,_Gz){return function(_){var _GA=E(_Gx),_GB=rMV(_GA),_GC=E(_GB);if(!_GC._){var _GD=new T(function(){var _GE=new T(function(){return B(A1(_Gz,_ii));});return B(_n(_GC.b,new T2(1,new T2(0,_Gy,function(_GF){return E(_GE);}),_w)));}),_=wMV(_GA,new T2(0,_GC.a,_GD));return _Gt;}else{var _GG=E(_GC.a);if(!_GG._){var _=wMV(_GA,new T2(0,_Gy,_w));return new T(function(){return B(A1(_Gz,_ii));});}else{var _=wMV(_GA,new T1(1,_GG.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Gz,_ii));}),new T2(1,new T(function(){return B(A2(_GG.a,_Gy,_Gu));}),_w)));}}};},_GH=new T(function(){return E(_EM);}),_GI=new T(function(){return eval("window.requestAnimationFrame");}),_GJ=new T1(1,_w),_GK=function(_GL,_GM){return function(_){var _GN=E(_GL),_GO=rMV(_GN),_GP=E(_GO);if(!_GP._){var _GQ=_GP.a,_GR=E(_GP.b);if(!_GR._){var _=wMV(_GN,_GJ);return new T(function(){return B(A1(_GM,_GQ));});}else{var _GS=E(_GR.a),_=wMV(_GN,new T2(0,_GS.a,_GR.b));return new T1(1,new T2(1,new T(function(){return B(A1(_GM,_GQ));}),new T2(1,new T(function(){return B(A1(_GS.b,_Gu));}),_w)));}}else{var _GT=new T(function(){var _GU=function(_GV){var _GW=new T(function(){return B(A1(_GM,_GV));});return function(_GX){return E(_GW);};};return B(_n(_GP.a,new T2(1,_GU,_w)));}),_=wMV(_GN,new T1(1,_GT));return _Gt;}};},_GY=function(_GZ,_H0){return new T1(0,B(_GK(_GZ,_H0)));},_H1=function(_H2,_H3){var _H4=new T(function(){return new T1(0,B(_Gw(_H2,_ii,_Gu)));});return function(_){var _H5=__createJSFunc(2,function(_H6,_){var _H7=B(_Go(_H4,_w,_));return _GH;}),_H8=__app1(E(_GI),_H5);return new T(function(){return B(_GY(_H2,_H3));});};},_H9=new T1(1,_w),_Ha=function(_Hb,_Hc,_){var _Hd=function(_){var _He=nMV(_Hb),_Hf=_He;return new T(function(){var _Hg=new T(function(){return B(_Hh(_));}),_Hi=function(_){var _Hj=rMV(_Hf),_Hk=B(A2(_Hc,_Hj,_)),_=wMV(_Hf,_Hk),_Hl=function(_){var _Hm=nMV(_H9);return new T(function(){return new T1(0,B(_H1(_Hm,function(_Hn){return E(_Hg);})));});};return new T1(0,_Hl);},_Ho=new T(function(){return new T1(0,_Hi);}),_Hh=function(_Hp){return E(_Ho);};return B(_Hh(_));});};return new F(function(){return _Go(new T1(0,_Hd),_w,_);});},_Hq=new T(function(){return eval("__strict(setBounds)");}),_Hr=function(_){var _Hs=__app3(E(_20),E(_91),E(_ib),E(_1Z)),_Ht=__app2(E(_Hq),E(_1u),E(_1n));return new F(function(){return _Ha(_Gh,_E2,_);});},_Hu=function(_){return new F(function(){return _Hr(_);});};
var hasteMain = function() {B(A(_Hu, [0]));};window.onload = hasteMain;