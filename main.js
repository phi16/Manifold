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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==(-2147483648)){_3l=new T1(1,I_fromInt(-2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0,-1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==(-2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S(-1021,53,_6k,_6l);});}else{return  -B(_5S(-1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=new T1(0,1),_7h=function(_7i){return E(E(_7i).a);},_7j=function(_7k){return E(E(_7k).a);},_7l=function(_7m){return E(E(_7m).c);},_7n=function(_7o,_7p,_7q,_7r,_7s,_7t,_7u){var _7v=B(_7j(B(_7h(_7o)))),_7w=new T(function(){return B(A3(_6I,_7v,new T(function(){return B(A3(_7l,_7v,_7p,_7s));}),new T(function(){return B(A3(_7l,_7v,_7q,_7t));})));});return new F(function(){return A3(_6I,_7v,_7w,new T(function(){return B(A3(_7l,_7v,_7r,_7u));}));});},_7x=function(_7y){return E(E(_7y).b);},_7z=function(_7A){return E(E(_7A).g);},_7B=function(_7C){return E(E(_7C).e);},_7D=function(_7E,_7F){var _7G=B(_7j(B(_7h(_7E)))),_7H=new T(function(){return B(A2(_7B,_7E,new T(function(){var _7I=E(_7F),_7J=_7I.a,_7K=_7I.b,_7L=_7I.c;return B(_7n(_7E,_7J,_7K,_7L,_7J,_7K,_7L));})));});return new F(function(){return A3(_7x,_7G,_7H,new T(function(){return B(A2(_7z,_7G,_7g));}));});},_7M=new T(function(){return B(unCStr("x"));}),_7N=new T1(0,_7M),_7O=new T(function(){return B(unCStr("y"));}),_7P=new T1(0,_7O),_7Q=new T(function(){return B(unCStr("z"));}),_7R=new T1(0,_7Q),_7S=new T3(0,E(_7N),E(_7P),E(_7R)),_7T=new T(function(){return B(_7D(_7f,_7S));}),_7U=function(_7V){return E(_7V);},_7W=new T(function(){return toJSStr(B(_5(_p,_7U,_7T)));}),_7X=function(_7Y,_7Z,_80){var _81=new T(function(){return B(_1(_7Y));}),_82=new T(function(){return B(_3(_7Y));}),_83=function(_84){var _85=E(_84);if(!_85._){return E(_82);}else{return new F(function(){return A2(_81,new T(function(){return B(_5(_7Y,_7Z,_85.a));}),new T(function(){return B(_83(_85.b));}));});}};return new F(function(){return _83(_80);});},_86=new T(function(){return B(unCStr("(/=) is not defined"));}),_87=new T(function(){return B(err(_86));}),_88=new T(function(){return B(unCStr("(==) is not defined"));}),_89=new T(function(){return B(err(_88));}),_8a=new T2(0,_89,_87),_8b=new T(function(){return B(unCStr("(<) is not defined"));}),_8c=new T(function(){return B(err(_8b));}),_8d=new T(function(){return B(unCStr("(<=) is not defined"));}),_8e=new T(function(){return B(err(_8d));}),_8f=new T(function(){return B(unCStr("(>) is not defined"));}),_8g=new T(function(){return B(err(_8f));}),_8h=new T(function(){return B(unCStr("(>=) is not defined"));}),_8i=new T(function(){return B(err(_8h));}),_8j=new T(function(){return B(unCStr("compare is not defined"));}),_8k=new T(function(){return B(err(_8j));}),_8l=new T(function(){return B(unCStr("max("));}),_8m=new T1(0,_8l),_8n=function(_8o,_8p){return new T1(1,new T2(1,_8m,new T2(1,_8o,new T2(1,_r,new T2(1,_8p,_w)))));},_8q=new T(function(){return B(unCStr("min("));}),_8r=new T1(0,_8q),_8s=function(_8t,_8u){return new T1(1,new T2(1,_8r,new T2(1,_8t,new T2(1,_r,new T2(1,_8u,_w)))));},_8v={_:0,a:_8a,b:_8k,c:_8c,d:_8e,e:_8g,f:_8i,g:_8n,h:_8s},_8w=new T2(0,_7f,_8v),_8x=function(_8y,_8z){var _8A=E(_8y);return E(_8z);},_8B=function(_8C,_8D){var _8E=E(_8D);return E(_8C);},_8F=function(_8G,_8H){var _8I=E(_8G),_8J=E(_8H);return new T3(0,E(B(A1(_8I.a,_8J.a))),E(B(A1(_8I.b,_8J.b))),E(B(A1(_8I.c,_8J.c))));},_8K=function(_8L,_8M,_8N){return new T3(0,E(_8L),E(_8M),E(_8N));},_8O=function(_8P){return new F(function(){return _8K(_8P,_8P,_8P);});},_8Q=function(_8R,_8S){var _8T=E(_8S),_8U=E(_8R);return new T3(0,E(_8U),E(_8U),E(_8U));},_8V=function(_8W,_8X){var _8Y=E(_8X);return new T3(0,E(B(A1(_8W,_8Y.a))),E(B(A1(_8W,_8Y.b))),E(B(A1(_8W,_8Y.c))));},_8Z=new T2(0,_8V,_8Q),_90=new T5(0,_8Z,_8O,_8F,_8x,_8B),_91=new T1(0,0),_92=function(_93){var _94=B(A2(_7z,_93,_7g)),_95=B(A2(_7z,_93,_91));return new T3(0,E(new T3(0,E(_94),E(_95),E(_95))),E(new T3(0,E(_95),E(_94),E(_95))),E(new T3(0,E(_95),E(_95),E(_94))));},_96=function(_97){return E(E(_97).a);},_98=function(_99){return E(E(_99).f);},_9a=function(_9b){return E(E(_9b).b);},_9c=function(_9d){return E(E(_9d).c);},_9e=function(_9f){return E(E(_9f).a);},_9g=function(_9h){return E(E(_9h).d);},_9i=function(_9j,_9k,_9l,_9m,_9n){var _9o=new T(function(){return E(E(E(_9j).c).a);}),_9p=new T(function(){var _9q=E(_9j).a,_9r=new T(function(){var _9s=new T(function(){return B(_7h(_9o));}),_9t=new T(function(){return B(_7j(_9s));}),_9u=new T(function(){return B(A2(_9g,_9o,_9k));}),_9v=new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9w=function(_9x,_9y){var _9z=new T(function(){var _9A=new T(function(){return B(A3(_9a,_9s,new T(function(){return B(A3(_7l,_9t,_9m,_9x));}),_9k));});return B(A3(_6I,_9t,_9A,new T(function(){return B(A3(_7l,_9t,_9y,_9u));})));});return new F(function(){return A3(_7l,_9t,_9v,_9z);});};return B(A3(_9e,B(_96(_9q)),_9w,_9l));});return B(A3(_9c,_9q,_9r,_9n));});return new T2(0,new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9p);},_9B=function(_9C,_9D,_9E,_9F){var _9G=E(_9E),_9H=E(_9F),_9I=B(_9i(_9D,_9G.a,_9G.b,_9H.a,_9H.b));return new T2(0,_9I.a,_9I.b);},_9J=new T1(0,1),_9K=function(_9L){return E(E(_9L).l);},_9M=function(_9N,_9O,_9P){var _9Q=new T(function(){return E(E(E(_9N).c).a);}),_9R=new T(function(){var _9S=new T(function(){return B(_7h(_9Q));}),_9T=new T(function(){var _9U=B(_7j(_9S)),_9V=new T(function(){var _9W=new T(function(){return B(A3(_7x,_9U,new T(function(){return B(A2(_7z,_9U,_9J));}),new T(function(){return B(A3(_7l,_9U,_9O,_9O));})));});return B(A2(_7B,_9Q,_9W));});return B(A2(_6K,_9U,_9V));});return B(A3(_9e,B(_96(E(_9N).a)),function(_9X){return new F(function(){return A3(_9a,_9S,_9X,_9T);});},_9P));});return new T2(0,new T(function(){return B(A2(_9K,_9Q,_9O));}),_9R);},_9Y=function(_9Z,_a0,_a1){var _a2=E(_a1),_a3=B(_9M(_a0,_a2.a,_a2.b));return new T2(0,_a3.a,_a3.b);},_a4=function(_a5){return E(E(_a5).r);},_a6=function(_a7,_a8,_a9){var _aa=new T(function(){return E(E(E(_a7).c).a);}),_ab=new T(function(){var _ac=new T(function(){return B(_7h(_aa));}),_ad=new T(function(){var _ae=new T(function(){var _af=B(_7j(_ac));return B(A3(_7x,_af,new T(function(){return B(A3(_7l,_af,_a8,_a8));}),new T(function(){return B(A2(_7z,_af,_9J));})));});return B(A2(_7B,_aa,_ae));});return B(A3(_9e,B(_96(E(_a7).a)),function(_ag){return new F(function(){return A3(_9a,_ac,_ag,_ad);});},_a9));});return new T2(0,new T(function(){return B(A2(_a4,_aa,_a8));}),_ab);},_ah=function(_ai,_aj,_ak){var _al=E(_ak),_am=B(_a6(_aj,_al.a,_al.b));return new T2(0,_am.a,_am.b);},_an=function(_ao){return E(E(_ao).k);},_ap=function(_aq,_ar,_as){var _at=new T(function(){return E(E(E(_aq).c).a);}),_au=new T(function(){var _av=new T(function(){return B(_7h(_at));}),_aw=new T(function(){var _ax=new T(function(){var _ay=B(_7j(_av));return B(A3(_7x,_ay,new T(function(){return B(A2(_7z,_ay,_9J));}),new T(function(){return B(A3(_7l,_ay,_ar,_ar));})));});return B(A2(_7B,_at,_ax));});return B(A3(_9e,B(_96(E(_aq).a)),function(_az){return new F(function(){return A3(_9a,_av,_az,_aw);});},_as));});return new T2(0,new T(function(){return B(A2(_an,_at,_ar));}),_au);},_aA=function(_aB,_aC,_aD){var _aE=E(_aD),_aF=B(_ap(_aC,_aE.a,_aE.b));return new T2(0,_aF.a,_aF.b);},_aG=function(_aH){return E(E(_aH).q);},_aI=function(_aJ,_aK,_aL){var _aM=new T(function(){return E(E(E(_aJ).c).a);}),_aN=new T(function(){var _aO=new T(function(){return B(_7h(_aM));}),_aP=new T(function(){var _aQ=new T(function(){var _aR=B(_7j(_aO));return B(A3(_6I,_aR,new T(function(){return B(A3(_7l,_aR,_aK,_aK));}),new T(function(){return B(A2(_7z,_aR,_9J));})));});return B(A2(_7B,_aM,_aQ));});return B(A3(_9e,B(_96(E(_aJ).a)),function(_aS){return new F(function(){return A3(_9a,_aO,_aS,_aP);});},_aL));});return new T2(0,new T(function(){return B(A2(_aG,_aM,_aK));}),_aN);},_aT=function(_aU,_aV,_aW){var _aX=E(_aW),_aY=B(_aI(_aV,_aX.a,_aX.b));return new T2(0,_aY.a,_aY.b);},_aZ=function(_b0){return E(E(_b0).m);},_b1=function(_b2,_b3,_b4){var _b5=new T(function(){return E(E(E(_b2).c).a);}),_b6=new T(function(){var _b7=new T(function(){return B(_7h(_b5));}),_b8=new T(function(){var _b9=B(_7j(_b7));return B(A3(_6I,_b9,new T(function(){return B(A2(_7z,_b9,_9J));}),new T(function(){return B(A3(_7l,_b9,_b3,_b3));})));});return B(A3(_9e,B(_96(E(_b2).a)),function(_ba){return new F(function(){return A3(_9a,_b7,_ba,_b8);});},_b4));});return new T2(0,new T(function(){return B(A2(_aZ,_b5,_b3));}),_b6);},_bb=function(_bc,_bd,_be){var _bf=E(_be),_bg=B(_b1(_bd,_bf.a,_bf.b));return new T2(0,_bg.a,_bg.b);},_bh=function(_bi){return E(E(_bi).s);},_bj=function(_bk,_bl,_bm){var _bn=new T(function(){return E(E(E(_bk).c).a);}),_bo=new T(function(){var _bp=new T(function(){return B(_7h(_bn));}),_bq=new T(function(){var _br=B(_7j(_bp));return B(A3(_7x,_br,new T(function(){return B(A2(_7z,_br,_9J));}),new T(function(){return B(A3(_7l,_br,_bl,_bl));})));});return B(A3(_9e,B(_96(E(_bk).a)),function(_bs){return new F(function(){return A3(_9a,_bp,_bs,_bq);});},_bm));});return new T2(0,new T(function(){return B(A2(_bh,_bn,_bl));}),_bo);},_bt=function(_bu,_bv,_bw){var _bx=E(_bw),_by=B(_bj(_bv,_bx.a,_bx.b));return new T2(0,_by.a,_by.b);},_bz=function(_bA){return E(E(_bA).i);},_bB=function(_bC){return E(E(_bC).h);},_bD=function(_bE,_bF,_bG){var _bH=new T(function(){return E(E(E(_bE).c).a);}),_bI=new T(function(){var _bJ=new T(function(){return B(_7j(new T(function(){return B(_7h(_bH));})));}),_bK=new T(function(){return B(A2(_6K,_bJ,new T(function(){return B(A2(_bB,_bH,_bF));})));});return B(A3(_9e,B(_96(E(_bE).a)),function(_bL){return new F(function(){return A3(_7l,_bJ,_bL,_bK);});},_bG));});return new T2(0,new T(function(){return B(A2(_bz,_bH,_bF));}),_bI);},_bM=function(_bN,_bO,_bP){var _bQ=E(_bP),_bR=B(_bD(_bO,_bQ.a,_bQ.b));return new T2(0,_bR.a,_bR.b);},_bS=function(_bT){return E(E(_bT).o);},_bU=function(_bV){return E(E(_bV).n);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_7j(new T(function(){return B(_7h(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_9e,B(_96(E(_bX).a)),function(_c4){return new F(function(){return A3(_7l,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bS,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc){return E(E(_cc).c);},_cd=function(_ce,_cf,_cg){var _ch=new T(function(){return E(E(E(_ce).c).a);}),_ci=new T(function(){var _cj=new T(function(){return B(_7j(new T(function(){return B(_7h(_ch));})));}),_ck=new T(function(){return B(A2(_cb,_ch,_cf));});return B(A3(_9e,B(_96(E(_ce).a)),function(_cl){return new F(function(){return A3(_7l,_cj,_cl,_ck);});},_cg));});return new T2(0,new T(function(){return B(A2(_cb,_ch,_cf));}),_ci);},_cm=function(_cn,_co,_cp){var _cq=E(_cp),_cr=B(_cd(_co,_cq.a,_cq.b));return new T2(0,_cr.a,_cr.b);},_cs=function(_ct,_cu,_cv){var _cw=new T(function(){return E(E(E(_ct).c).a);}),_cx=new T(function(){var _cy=new T(function(){return B(_7h(_cw));}),_cz=new T(function(){return B(_7j(_cy));}),_cA=new T(function(){return B(A3(_9a,_cy,new T(function(){return B(A2(_7z,_cz,_9J));}),_cu));});return B(A3(_9e,B(_96(E(_ct).a)),function(_cB){return new F(function(){return A3(_7l,_cz,_cB,_cA);});},_cv));});return new T2(0,new T(function(){return B(A2(_9g,_cw,_cu));}),_cx);},_cC=function(_cD,_cE,_cF){var _cG=E(_cF),_cH=B(_cs(_cE,_cG.a,_cG.b));return new T2(0,_cH.a,_cH.b);},_cI=function(_cJ,_cK,_cL,_cM){var _cN=new T(function(){return E(E(_cK).c);}),_cO=new T3(0,new T(function(){return E(E(_cK).a);}),new T(function(){return E(E(_cK).b);}),new T2(0,new T(function(){return E(E(_cN).a);}),new T(function(){return E(E(_cN).b);})));return new F(function(){return A3(_9a,_cJ,new T(function(){var _cP=E(_cM),_cQ=B(_cs(_cO,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);}),new T(function(){var _cR=E(_cL),_cS=B(_cs(_cO,_cR.a,_cR.b));return new T2(0,_cS.a,_cS.b);}));});},_cT=new T1(0,0),_cU=function(_cV){return E(E(_cV).b);},_cW=function(_cX){return E(E(_cX).b);},_cY=function(_cZ){var _d0=new T(function(){return E(E(E(_cZ).c).a);}),_d1=new T(function(){return B(A2(_cW,E(_cZ).a,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_d0)))),_cT));})));});return new T2(0,new T(function(){return B(_cU(_d0));}),_d1);},_d2=function(_d3,_d4){var _d5=B(_cY(_d4));return new T2(0,_d5.a,_d5.b);},_d6=function(_d7,_d8,_d9){var _da=new T(function(){return E(E(E(_d7).c).a);}),_db=new T(function(){var _dc=new T(function(){return B(_7j(new T(function(){return B(_7h(_da));})));}),_dd=new T(function(){return B(A2(_bz,_da,_d8));});return B(A3(_9e,B(_96(E(_d7).a)),function(_de){return new F(function(){return A3(_7l,_dc,_de,_dd);});},_d9));});return new T2(0,new T(function(){return B(A2(_bB,_da,_d8));}),_db);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d6(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm,_dn,_do){var _dp=new T(function(){return E(E(E(_dm).c).a);}),_dq=new T(function(){var _dr=new T(function(){return B(_7j(new T(function(){return B(_7h(_dp));})));}),_ds=new T(function(){return B(A2(_bS,_dp,_dn));});return B(A3(_9e,B(_96(E(_dm).a)),function(_dt){return new F(function(){return A3(_7l,_dr,_dt,_ds);});},_do));});return new T2(0,new T(function(){return B(A2(_bU,_dp,_dn));}),_dq);},_du=function(_dv,_dw,_dx){var _dy=E(_dx),_dz=B(_dl(_dw,_dy.a,_dy.b));return new T2(0,_dz.a,_dz.b);},_dA=new T1(0,2),_dB=function(_dC,_dD,_dE){var _dF=new T(function(){return E(E(E(_dC).c).a);}),_dG=new T(function(){var _dH=new T(function(){return B(_7h(_dF));}),_dI=new T(function(){return B(_7j(_dH));}),_dJ=new T(function(){var _dK=new T(function(){return B(A3(_9a,_dH,new T(function(){return B(A2(_7z,_dI,_9J));}),new T(function(){return B(A2(_7z,_dI,_dA));})));});return B(A3(_9a,_dH,_dK,new T(function(){return B(A2(_7B,_dF,_dD));})));});return B(A3(_9e,B(_96(E(_dC).a)),function(_dL){return new F(function(){return A3(_7l,_dI,_dL,_dJ);});},_dE));});return new T2(0,new T(function(){return B(A2(_7B,_dF,_dD));}),_dG);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dP),_dR=B(_dB(_dO,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);},_dS=function(_dT){return E(E(_dT).j);},_dU=function(_dV,_dW,_dX){var _dY=new T(function(){return E(E(E(_dV).c).a);}),_dZ=new T(function(){var _e0=new T(function(){return B(_7h(_dY));}),_e1=new T(function(){var _e2=new T(function(){return B(A2(_bz,_dY,_dW));});return B(A3(_7l,B(_7j(_e0)),_e2,_e2));});return B(A3(_9e,B(_96(E(_dV).a)),function(_e3){return new F(function(){return A3(_9a,_e0,_e3,_e1);});},_dX));});return new T2(0,new T(function(){return B(A2(_dS,_dY,_dW));}),_dZ);},_e4=function(_e5,_e6,_e7){var _e8=E(_e7),_e9=B(_dU(_e6,_e8.a,_e8.b));return new T2(0,_e9.a,_e9.b);},_ea=function(_eb){return E(E(_eb).p);},_ec=function(_ed,_ee,_ef){var _eg=new T(function(){return E(E(E(_ed).c).a);}),_eh=new T(function(){var _ei=new T(function(){return B(_7h(_eg));}),_ej=new T(function(){var _ek=new T(function(){return B(A2(_bS,_eg,_ee));});return B(A3(_7l,B(_7j(_ei)),_ek,_ek));});return B(A3(_9e,B(_96(E(_ed).a)),function(_el){return new F(function(){return A3(_9a,_ei,_el,_ej);});},_ef));});return new T2(0,new T(function(){return B(A2(_ea,_eg,_ee));}),_eh);},_em=function(_en,_eo,_ep){var _eq=E(_ep),_er=B(_ec(_eo,_eq.a,_eq.b));return new T2(0,_er.a,_er.b);},_es=function(_et,_eu){return {_:0,a:_et,b:new T(function(){return B(_d2(_et,_eu));}),c:function(_ev){return new F(function(){return _cm(_et,_eu,_ev);});},d:function(_ev){return new F(function(){return _cC(_et,_eu,_ev);});},e:function(_ev){return new F(function(){return _dM(_et,_eu,_ev);});},f:function(_ew,_ev){return new F(function(){return _9B(_et,_eu,_ew,_ev);});},g:function(_ew,_ev){return new F(function(){return _cI(_et,_eu,_ew,_ev);});},h:function(_ev){return new F(function(){return _df(_et,_eu,_ev);});},i:function(_ev){return new F(function(){return _bM(_et,_eu,_ev);});},j:function(_ev){return new F(function(){return _e4(_et,_eu,_ev);});},k:function(_ev){return new F(function(){return _aA(_et,_eu,_ev);});},l:function(_ev){return new F(function(){return _9Y(_et,_eu,_ev);});},m:function(_ev){return new F(function(){return _bb(_et,_eu,_ev);});},n:function(_ev){return new F(function(){return _du(_et,_eu,_ev);});},o:function(_ev){return new F(function(){return _c5(_et,_eu,_ev);});},p:function(_ev){return new F(function(){return _em(_et,_eu,_ev);});},q:function(_ev){return new F(function(){return _aT(_et,_eu,_ev);});},r:function(_ev){return new F(function(){return _ah(_et,_eu,_ev);});},s:function(_ev){return new F(function(){return _bt(_et,_eu,_ev);});}};},_ex=function(_ey,_ez,_eA,_eB,_eC){var _eD=new T(function(){return B(_7h(new T(function(){return E(E(E(_ey).c).a);})));}),_eE=new T(function(){var _eF=E(_ey).a,_eG=new T(function(){var _eH=new T(function(){return B(_7j(_eD));}),_eI=new T(function(){return B(A3(_7l,_eH,_eB,_eB));}),_eJ=function(_eK,_eL){var _eM=new T(function(){return B(A3(_7x,_eH,new T(function(){return B(A3(_7l,_eH,_eK,_eB));}),new T(function(){return B(A3(_7l,_eH,_ez,_eL));})));});return new F(function(){return A3(_9a,_eD,_eM,_eI);});};return B(A3(_9e,B(_96(_eF)),_eJ,_eA));});return B(A3(_9c,_eF,_eG,_eC));});return new T2(0,new T(function(){return B(A3(_9a,_eD,_ez,_eB));}),_eE);},_eN=function(_eO,_eP,_eQ,_eR){var _eS=E(_eQ),_eT=E(_eR),_eU=B(_ex(_eP,_eS.a,_eS.b,_eT.a,_eT.b));return new T2(0,_eU.a,_eU.b);},_eV=function(_eW){return E(E(_eW).d);},_eX=function(_eY,_eZ){var _f0=new T(function(){return B(_7h(new T(function(){return E(E(E(_eY).c).a);})));}),_f1=new T(function(){return B(A2(_cW,E(_eY).a,new T(function(){return B(A2(_7z,B(_7j(_f0)),_cT));})));});return new T2(0,new T(function(){return B(A2(_eV,_f0,_eZ));}),_f1);},_f2=function(_f3,_f4,_f5){var _f6=B(_eX(_f4,_f5));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return B(_7h(new T(function(){return E(E(E(_f8).c).a);})));}),_fc=new T(function(){return B(_7j(_fb));}),_fd=new T(function(){var _fe=new T(function(){var _ff=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),new T(function(){return B(A3(_7l,_fc,_f9,_f9));})));});return B(A2(_6K,_fc,_ff));});return B(A3(_9e,B(_96(E(_f8).a)),function(_fg){return new F(function(){return A3(_7l,_fc,_fg,_fe);});},_fa));}),_fh=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),_f9));});return new T2(0,_fh,_fd);},_fi=function(_fj,_fk,_fl){var _fm=E(_fl),_fn=B(_f7(_fk,_fm.a,_fm.b));return new T2(0,_fn.a,_fn.b);},_fo=function(_fp,_fq){return new T4(0,_fp,function(_ew,_ev){return new F(function(){return _eN(_fp,_fq,_ew,_ev);});},function(_ev){return new F(function(){return _fi(_fp,_fq,_ev);});},function(_ev){return new F(function(){return _f2(_fp,_fq,_ev);});});},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fs).c).a);})));})));}),_fy=new T(function(){var _fz=E(_fs).a,_fA=new T(function(){var _fB=function(_fC,_fD){return new F(function(){return A3(_6I,_fx,new T(function(){return B(A3(_7l,_fx,_ft,_fD));}),new T(function(){return B(A3(_7l,_fx,_fC,_fv));}));});};return B(A3(_9e,B(_96(_fz)),_fB,_fu));});return B(A3(_9c,_fz,_fA,_fw));});return new T2(0,new T(function(){return B(A3(_7l,_fx,_ft,_fv));}),_fy);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fr(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO,_fP,_fQ){var _fR=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fM).c).a);})));})));}),_fS=new T(function(){var _fT=E(_fM).a,_fU=new T(function(){return B(A3(_9e,B(_96(_fT)),new T(function(){return B(_6I(_fR));}),_fO));});return B(A3(_9c,_fT,_fU,_fQ));});return new T2(0,new T(function(){return B(A3(_6I,_fR,_fN,_fP));}),_fS);},_fV=function(_fW,_fX,_fY){var _fZ=E(_fX),_g0=E(_fY),_g1=B(_fL(_fW,_fZ.a,_fZ.b,_g0.a,_g0.b));return new T2(0,_g1.a,_g1.b);},_g2=function(_g3,_g4,_g5){var _g6=B(_g7(_g3));return new F(function(){return A3(_6I,_g6,_g4,new T(function(){return B(A2(_6K,_g6,_g5));}));});},_g8=function(_g9){return E(E(_g9).e);},_ga=function(_gb){return E(E(_gb).f);},_gc=function(_gd,_ge,_gf){var _gg=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gd).c).a);})));})));}),_gh=new T(function(){var _gi=new T(function(){return B(A2(_ga,_gg,_ge));});return B(A3(_9e,B(_96(E(_gd).a)),function(_gj){return new F(function(){return A3(_7l,_gg,_gj,_gi);});},_gf));});return new T2(0,new T(function(){return B(A2(_g8,_gg,_ge));}),_gh);},_gk=function(_gl,_gm){var _gn=E(_gm),_go=B(_gc(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr){var _gs=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gq).c).a);})));})));}),_gt=new T(function(){return B(A2(_cW,E(_gq).a,new T(function(){return B(A2(_7z,_gs,_cT));})));});return new T2(0,new T(function(){return B(A2(_7z,_gs,_gr));}),_gt);},_gu=function(_gv,_gw){var _gx=B(_gp(_gv,_gw));return new T2(0,_gx.a,_gx.b);},_gy=function(_gz,_gA,_gB){var _gC=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gz).c).a);})));})));}),_gD=new T(function(){return B(A3(_9e,B(_96(E(_gz).a)),new T(function(){return B(_6K(_gC));}),_gB));});return new T2(0,new T(function(){return B(A2(_6K,_gC,_gA));}),_gD);},_gE=function(_gF,_gG){var _gH=E(_gG),_gI=B(_gy(_gF,_gH.a,_gH.b));return new T2(0,_gI.a,_gI.b);},_gJ=function(_gK,_gL){var _gM=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gK).c).a);})));})));}),_gN=new T(function(){return B(A2(_cW,E(_gK).a,new T(function(){return B(A2(_7z,_gM,_cT));})));});return new T2(0,new T(function(){return B(A2(_ga,_gM,_gL));}),_gN);},_gO=function(_gP,_gQ){var _gR=B(_gJ(_gP,E(_gQ).a));return new T2(0,_gR.a,_gR.b);},_g7=function(_gS){return {_:0,a:function(_ew,_ev){return new F(function(){return _fV(_gS,_ew,_ev);});},b:function(_ew,_ev){return new F(function(){return _g2(_gS,_ew,_ev);});},c:function(_ew,_ev){return new F(function(){return _fE(_gS,_ew,_ev);});},d:function(_ev){return new F(function(){return _gE(_gS,_ev);});},e:function(_ev){return new F(function(){return _gk(_gS,_ev);});},f:function(_ev){return new F(function(){return _gO(_gS,_ev);});},g:function(_ev){return new F(function(){return _gu(_gS,_ev);});}};},_gT=function(_gU){var _gV=new T(function(){return E(E(_gU).a);}),_gW=new T3(0,_90,_92,new T2(0,_gV,new T(function(){return E(E(_gU).b);}))),_gX=new T(function(){return B(_es(new T(function(){return B(_fo(new T(function(){return B(_g7(_gW));}),_gW));}),_gW));}),_gY=new T(function(){return B(_7j(new T(function(){return B(_7h(_gV));})));}),_gZ=function(_h0){return E(B(_7D(_gX,new T(function(){var _h1=E(_h0),_h2=B(A2(_7z,_gY,_7g)),_h3=B(A2(_7z,_gY,_91));return new T3(0,E(new T2(0,_h1.a,new T3(0,E(_h2),E(_h3),E(_h3)))),E(new T2(0,_h1.b,new T3(0,E(_h3),E(_h2),E(_h3)))),E(new T2(0,_h1.c,new T3(0,E(_h3),E(_h3),E(_h2)))));}))).b);};return E(_gZ);},_h4=new T(function(){return B(_gT(_8w));}),_h5=function(_h6,_h7){var _h8=E(_h7);return (_h8._==0)?__Z:new T2(1,_h6,new T2(1,_h8.a,new T(function(){return B(_h5(_h6,_h8.b));})));},_h9=new T(function(){var _ha=B(A1(_h4,_7S));return new T2(1,_ha.a,new T(function(){return B(_h5(_r,new T2(1,_ha.b,new T2(1,_ha.c,_o))));}));}),_hb=new T1(1,_h9),_hc=new T2(1,_hb,_w),_hd=new T(function(){return B(unCStr("vec3("));}),_he=new T1(0,_hd),_hf=new T2(1,_he,_hc),_hg=new T(function(){return toJSStr(B(_7X(_p,_7U,_hf)));}),_hh=function(_hi,_hj){while(1){var _hk=E(_hi);if(!_hk._){return E(_hj);}else{var _hl=_hj+1|0;_hi=_hk.b;_hj=_hl;continue;}}},_hm=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hn=new T(function(){return B(err(_hm));}),_ho=0,_hp=new T3(0,E(_ho),E(_ho),E(_ho)),_hq=new T(function(){return B(unCStr("Negative exponent"));}),_hr=new T(function(){return B(err(_hq));}),_hs=function(_ht,_hu,_hv){while(1){if(!(_hu%2)){var _hw=_ht*_ht,_hx=quot(_hu,2);_ht=_hw;_hu=_hx;continue;}else{var _hy=E(_hu);if(_hy==1){return _ht*_hv;}else{var _hw=_ht*_ht,_hz=_ht*_hv;_ht=_hw;_hu=quot(_hy-1|0,2);_hv=_hz;continue;}}}},_hA=function(_hB,_hC){while(1){if(!(_hC%2)){var _hD=_hB*_hB,_hE=quot(_hC,2);_hB=_hD;_hC=_hE;continue;}else{var _hF=E(_hC);if(_hF==1){return E(_hB);}else{return new F(function(){return _hs(_hB*_hB,quot(_hF-1|0,2),_hB);});}}}},_hG=function(_hH){var _hI=E(_hH);return new F(function(){return Math.log(_hI+(_hI+1)*Math.sqrt((_hI-1)/(_hI+1)));});},_hJ=function(_hK){var _hL=E(_hK);return new F(function(){return Math.log(_hL+Math.sqrt(1+_hL*_hL));});},_hM=function(_hN){var _hO=E(_hN);return 0.5*Math.log((1+_hO)/(1-_hO));},_hP=function(_hQ,_hR){return Math.log(E(_hR))/Math.log(E(_hQ));},_hS=3.141592653589793,_hT=function(_hU){var _hV=E(_hU);return new F(function(){return _6j(_hV.a,_hV.b);});},_hW=function(_hX){return 1/E(_hX);},_hY=function(_hZ){var _i0=E(_hZ),_i1=E(_i0);return (_i1==0)?E(_6i):(_i1<=0)? -_i1:E(_i0);},_i2=function(_i3){var _i4=E(_i3);if(!_i4._){return _i4.a;}else{return new F(function(){return I_toNumber(_i4.a);});}},_i5=function(_i6){return new F(function(){return _i2(_i6);});},_i7=1,_i8=-1,_i9=function(_ia){var _ib=E(_ia);return (_ib<=0)?(_ib>=0)?E(_ib):E(_i8):E(_i7);},_ic=function(_id,_ie){return E(_id)-E(_ie);},_if=function(_ig){return  -E(_ig);},_ih=function(_ii,_ij){return E(_ii)+E(_ij);},_ik=function(_il,_im){return E(_il)*E(_im);},_in={_:0,a:_ih,b:_ic,c:_ik,d:_if,e:_hY,f:_i9,g:_i5},_io=function(_ip,_iq){return E(_ip)/E(_iq);},_ir=new T4(0,_in,_io,_hW,_hT),_is=function(_it){return new F(function(){return Math.acos(E(_it));});},_iu=function(_iv){return new F(function(){return Math.asin(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.atan(E(_ix));});},_iy=function(_iz){return new F(function(){return Math.cos(E(_iz));});},_iA=function(_iB){return new F(function(){return cosh(E(_iB));});},_iC=function(_iD){return new F(function(){return Math.exp(E(_iD));});},_iE=function(_iF){return new F(function(){return Math.log(E(_iF));});},_iG=function(_iH,_iI){return new F(function(){return Math.pow(E(_iH),E(_iI));});},_iJ=function(_iK){return new F(function(){return Math.sin(E(_iK));});},_iL=function(_iM){return new F(function(){return sinh(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.sqrt(E(_iO));});},_iP=function(_iQ){return new F(function(){return Math.tan(E(_iQ));});},_iR=function(_iS){return new F(function(){return tanh(E(_iS));});},_iT={_:0,a:_ir,b:_hS,c:_iC,d:_iE,e:_iN,f:_iG,g:_hP,h:_iJ,i:_iy,j:_iP,k:_iu,l:_is,m:_iw,n:_iL,o:_iA,p:_iR,q:_hJ,r:_hG,s:_hM},_iU=function(_iV,_iW){return (E(_iV)!=E(_iW))?true:false;},_iX=function(_iY,_iZ){return E(_iY)==E(_iZ);},_j0=new T2(0,_iX,_iU),_j1=function(_j2,_j3){return E(_j2)<E(_j3);},_j4=function(_j5,_j6){return E(_j5)<=E(_j6);},_j7=function(_j8,_j9){return E(_j8)>E(_j9);},_ja=function(_jb,_jc){return E(_jb)>=E(_jc);},_jd=function(_je,_jf){var _jg=E(_je),_jh=E(_jf);return (_jg>=_jh)?(_jg!=_jh)?2:1:0;},_ji=function(_jj,_jk){var _jl=E(_jj),_jm=E(_jk);return (_jl>_jm)?E(_jl):E(_jm);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=E(_jp);return (_jq>_jr)?E(_jr):E(_jq);},_js={_:0,a:_j0,b:_jd,c:_j1,d:_j4,e:_j7,f:_ja,g:_ji,h:_jn},_jt="dz",_ju="wy",_jv="wx",_jw="dy",_jx="dx",_jy="t",_jz="a",_jA="r",_jB="ly",_jC="lx",_jD="wz",_jE=0,_jF=function(_jG){var _jH=__new(),_jI=_jH,_jJ=function(_jK,_){while(1){var _jL=E(_jK);if(!_jL._){return _jE;}else{var _jM=E(_jL.a),_jN=__set(_jI,E(_jM.a),E(_jM.b));_jK=_jL.b;continue;}}},_jO=B(_jJ(_jG,_));return E(_jI);},_jP=function(_jQ,_jR,_jS,_jT,_jU,_jV,_jW,_jX,_jY){return new F(function(){return _jF(new T2(1,new T2(0,_jv,_jQ),new T2(1,new T2(0,_ju,_jR),new T2(1,new T2(0,_jD,_jS),new T2(1,new T2(0,_jC,_jT*_jU*Math.cos(_jV)),new T2(1,new T2(0,_jB,_jT*_jU*Math.sin(_jV)),new T2(1,new T2(0,_jA,_jT),new T2(1,new T2(0,_jz,_jU),new T2(1,new T2(0,_jy,_jV),new T2(1,new T2(0,_jx,_jW),new T2(1,new T2(0,_jw,_jX),new T2(1,new T2(0,_jt,_jY),_o))))))))))));});},_jZ=function(_k0){var _k1=E(_k0),_k2=E(_k1.a),_k3=E(_k1.b),_k4=E(_k1.d);return new F(function(){return _jP(_k2.a,_k2.b,_k2.c,E(_k3.a),E(_k3.b),E(_k1.c),_k4.a,_k4.b,_k4.c);});},_k5=function(_k6,_k7){var _k8=E(_k7);return (_k8._==0)?__Z:new T2(1,new T(function(){return B(A1(_k6,_k8.a));}),new T(function(){return B(_k5(_k6,_k8.b));}));},_k9=function(_ka,_kb,_kc){var _kd=__lst2arr(B(_k5(_jZ,new T2(1,_ka,new T2(1,_kb,new T2(1,_kc,_o))))));return E(_kd);},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k9(_kg.a,_kg.b,_kg.c);});},_kh=new T2(0,_iT,_js),_ki=function(_kj,_kk,_kl,_km){var _kn=B(_7h(_kj)),_ko=new T(function(){return B(A2(_7B,_kj,new T(function(){return B(_7n(_kj,_kk,_kl,_km,_kk,_kl,_km));})));});return new T3(0,B(A3(_9a,_kn,_kk,_ko)),B(A3(_9a,_kn,_kl,_ko)),B(A3(_9a,_kn,_km,_ko)));},_kp=function(_kq,_kr,_ks,_kt,_ku,_kv,_kw){var _kx=B(_7l(_kq));return new T3(0,B(A1(B(A1(_kx,_kr)),_ku)),B(A1(B(A1(_kx,_ks)),_kv)),B(A1(B(A1(_kx,_kt)),_kw)));},_ky=function(_kz,_kA,_kB,_kC,_kD,_kE,_kF){var _kG=B(_6I(_kz));return new T3(0,B(A1(B(A1(_kG,_kA)),_kD)),B(A1(B(A1(_kG,_kB)),_kE)),B(A1(B(A1(_kG,_kC)),_kF)));},_kH=function(_kI,_kJ){var _kK=new T(function(){return E(E(_kI).a);}),_kL=new T(function(){return B(A2(_gT,new T2(0,_kK,new T(function(){return E(E(_kI).b);})),_kJ));}),_kM=new T(function(){var _kN=E(_kL),_kO=B(_ki(_kK,_kN.a,_kN.b,_kN.c));return new T3(0,E(_kO.a),E(_kO.b),E(_kO.c));}),_kP=new T(function(){var _kQ=E(_kJ),_kR=E(_kM),_kS=B(_7h(_kK)),_kT=new T(function(){return B(A2(_7B,_kK,new T(function(){var _kU=E(_kL),_kV=_kU.a,_kW=_kU.b,_kX=_kU.c;return B(_7n(_kK,_kV,_kW,_kX,_kV,_kW,_kX));})));}),_kY=B(A3(_9a,_kS,new T(function(){return B(_7D(_kK,_kQ));}),_kT)),_kZ=B(_7j(_kS)),_l0=B(_kp(_kZ,_kR.a,_kR.b,_kR.c,_kY,_kY,_kY)),_l1=B(_6K(_kZ)),_l2=B(_ky(_kZ,_kQ.a,_kQ.b,_kQ.c,B(A1(_l1,_l0.a)),B(A1(_l1,_l0.b)),B(A1(_l1,_l0.c))));return new T3(0,E(_l2.a),E(_l2.b),E(_l2.c));});return new T2(0,_kP,_kM);},_l3=function(_l4){return E(E(_l4).a);},_l5=function(_l6,_l7,_l8,_l9,_la,_lb,_lc){var _ld=B(_7n(_l6,_la,_lb,_lc,_l7,_l8,_l9)),_le=B(_7j(B(_7h(_l6)))),_lf=B(_kp(_le,_la,_lb,_lc,_ld,_ld,_ld)),_lg=B(_6K(_le));return new F(function(){return _ky(_le,_l7,_l8,_l9,B(A1(_lg,_lf.a)),B(A1(_lg,_lf.b)),B(A1(_lg,_lf.c)));});},_lh=function(_li){return E(E(_li).a);},_lj=function(_lk,_ll,_lm,_ln){var _lo=new T(function(){var _lp=E(_ln),_lq=E(_lm),_lr=B(_l5(_lk,_lp.a,_lp.b,_lp.c,_lq.a,_lq.b,_lq.c));return new T3(0,E(_lr.a),E(_lr.b),E(_lr.c));}),_ls=new T(function(){return B(A2(_7B,_lk,new T(function(){var _lt=E(_lo),_lu=_lt.a,_lv=_lt.b,_lw=_lt.c;return B(_7n(_lk,_lu,_lv,_lw,_lu,_lv,_lw));})));});if(!B(A3(_lh,B(_l3(_ll)),_ls,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_lk)))),_91));})))){var _lx=E(_lo),_ly=B(_ki(_lk,_lx.a,_lx.b,_lx.c)),_lz=B(A2(_7B,_lk,new T(function(){var _lA=E(_ln),_lB=_lA.a,_lC=_lA.b,_lD=_lA.c;return B(_7n(_lk,_lB,_lC,_lD,_lB,_lC,_lD));}))),_lE=B(_7l(new T(function(){return B(_7j(new T(function(){return B(_7h(_lk));})));})));return new T3(0,B(A1(B(A1(_lE,_ly.a)),_lz)),B(A1(B(A1(_lE,_ly.b)),_lz)),B(A1(B(A1(_lE,_ly.c)),_lz)));}else{var _lF=B(A2(_7z,B(_7j(B(_7h(_lk)))),_91));return new T3(0,_lF,_lF,_lF);}},_lG=new T(function(){var _lH=eval("angleCount"),_lI=Number(_lH);return jsTrunc(_lI);}),_lJ=new T(function(){return E(_lG);}),_lK=new T(function(){return B(unCStr(": empty list"));}),_lL=new T(function(){return B(unCStr("Prelude."));}),_lM=function(_lN){return new F(function(){return err(B(_f(_lL,new T(function(){return B(_f(_lN,_lK));},1))));});},_lO=new T(function(){return B(unCStr("head"));}),_lP=new T(function(){return B(_lM(_lO));}),_lQ=function(_lR,_lS,_lT){var _lU=E(_lR);if(!_lU._){return __Z;}else{var _lV=E(_lS);if(!_lV._){return __Z;}else{var _lW=_lV.a,_lX=E(_lT);if(!_lX._){return __Z;}else{var _lY=E(_lX.a),_lZ=_lY.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_lU.a),E(_lW),E(_lZ));}),new T2(1,new T(function(){return new T3(0,E(_lW),E(_lZ),E(_lY.b));}),_o)),new T(function(){return B(_lQ(_lU.b,_lV.b,_lX.b));},1));});}}}},_m0=new T(function(){return B(unCStr("tail"));}),_m1=new T(function(){return B(_lM(_m0));}),_m2=function(_m3,_m4){var _m5=E(_m3);if(!_m5._){return __Z;}else{var _m6=E(_m4);return (_m6._==0)?__Z:new T2(1,new T2(0,_m5.a,_m6.a),new T(function(){return B(_m2(_m5.b,_m6.b));}));}},_m7=function(_m8,_m9){var _ma=E(_m8);if(!_ma._){return __Z;}else{var _mb=E(_m9);if(!_mb._){return __Z;}else{var _mc=E(_ma.a),_md=_mc.b,_me=E(_mb.a).b,_mf=new T(function(){var _mg=new T(function(){return B(_m2(_me,new T(function(){var _mh=E(_me);if(!_mh._){return E(_m1);}else{return E(_mh.b);}},1)));},1);return B(_lQ(_md,new T(function(){var _mi=E(_md);if(!_mi._){return E(_m1);}else{return E(_mi.b);}},1),_mg));});return new F(function(){return _f(new T2(1,new T(function(){var _mj=E(_md);if(!_mj._){return E(_lP);}else{var _mk=E(_me);if(!_mk._){return E(_lP);}else{return new T3(0,E(_mc.a),E(_mj.a),E(_mk.a));}}}),_mf),new T(function(){return B(_m7(_ma.b,_mb.b));},1));});}}},_ml=new T(function(){return E(_lJ)-1;}),_mm=new T1(0,1),_mn=function(_mo,_mp){var _mq=E(_mp),_mr=new T(function(){var _ms=B(_7j(_mo)),_mt=B(_mn(_mo,B(A3(_6I,_ms,_mq,new T(function(){return B(A2(_7z,_ms,_mm));})))));return new T2(1,_mt.a,_mt.b);});return new T2(0,_mq,_mr);},_mu=function(_mv){return E(E(_mv).d);},_mw=new T1(0,2),_mx=function(_my,_mz){var _mA=E(_mz);if(!_mA._){return __Z;}else{var _mB=_mA.a;return (!B(A1(_my,_mB)))?__Z:new T2(1,_mB,new T(function(){return B(_mx(_my,_mA.b));}));}},_mC=function(_mD,_mE,_mF,_mG){var _mH=B(_mn(_mE,_mF)),_mI=new T(function(){var _mJ=B(_7j(_mE)),_mK=new T(function(){return B(A3(_9a,_mE,new T(function(){return B(A2(_7z,_mJ,_mm));}),new T(function(){return B(A2(_7z,_mJ,_mw));})));});return B(A3(_6I,_mJ,_mG,_mK));});return new F(function(){return _mx(function(_mL){return new F(function(){return A3(_mu,_mD,_mL,_mI);});},new T2(1,_mH.a,_mH.b));});},_mM=new T(function(){return B(_mC(_js,_ir,_ho,_ml));}),_mN=function(_mO,_mP){while(1){var _mQ=E(_mO);if(!_mQ._){return E(_mP);}else{_mO=_mQ.b;_mP=_mQ.a;continue;}}},_mR=new T(function(){return B(unCStr("last"));}),_mS=new T(function(){return B(_lM(_mR));}),_mT=function(_mU){return new F(function(){return _mN(_mU,_mS);});},_mV=function(_mW){return new F(function(){return _mT(E(_mW).b);});},_mX=new T(function(){var _mY=eval("proceedCount"),_mZ=Number(_mY);return jsTrunc(_mZ);}),_n0=new T(function(){return E(_mX);}),_n1=1,_n2=new T(function(){return B(_mC(_js,_ir,_n1,_n0));}),_n3=function(_n4,_n5,_n6,_n7,_n8,_n9,_na,_nb,_nc,_nd,_ne,_nf,_ng,_nh){var _ni=new T(function(){var _nj=new T(function(){var _nk=E(_nd),_nl=E(_nh),_nm=E(_ng),_nn=E(_ne),_no=E(_nf),_np=E(_nc);return new T3(0,_nk*_nl-_nm*_nn,_nn*_no-_nl*_np,_np*_nm-_no*_nk);}),_nq=function(_nr){var _ns=new T(function(){var _nt=E(_nr)/E(_lJ);return (_nt+_nt)*3.141592653589793;}),_nu=new T(function(){return B(A1(_n4,_ns));}),_nv=new T(function(){var _nw=new T(function(){var _nx=E(_nu)/E(_n0);return new T3(0,E(_nx),E(_nx),E(_nx));}),_ny=function(_nz,_nA){var _nB=E(_nz);if(!_nB._){return new T2(0,_o,_nA);}else{var _nC=new T(function(){var _nD=B(_kH(_kh,new T(function(){var _nE=E(_nA),_nF=E(_nE.a),_nG=E(_nE.b),_nH=E(_nw);return new T3(0,E(_nF.a)+E(_nG.a)*E(_nH.a),E(_nF.b)+E(_nG.b)*E(_nH.b),E(_nF.c)+E(_nG.c)*E(_nH.c));}))),_nI=_nD.a,_nJ=new T(function(){var _nK=E(_nD.b),_nL=E(E(_nA).b),_nM=B(_l5(_iT,_nL.a,_nL.b,_nL.c,_nK.a,_nK.b,_nK.c)),_nN=B(_ki(_iT,_nM.a,_nM.b,_nM.c));return new T3(0,E(_nN.a),E(_nN.b),E(_nN.c));});return new T2(0,new T(function(){var _nO=E(_nu),_nP=E(_ns);return new T4(0,E(_nI),E(new T2(0,E(_nB.a)/E(_n0),E(_nO))),E(_nP),E(_nJ));}),new T2(0,_nI,_nJ));}),_nQ=new T(function(){var _nR=B(_ny(_nB.b,new T(function(){return E(E(_nC).b);})));return new T2(0,_nR.a,_nR.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nC).a);}),new T(function(){return E(E(_nQ).a);})),new T(function(){return E(E(_nQ).b);}));}},_nS=function(_nT,_nU,_nV,_nW,_nX){var _nY=E(_nT);if(!_nY._){return new T2(0,_o,new T2(0,new T3(0,E(_nU),E(_nV),E(_nW)),_nX));}else{var _nZ=new T(function(){var _o0=B(_kH(_kh,new T(function(){var _o1=E(_nX),_o2=E(_nw);return new T3(0,E(_nU)+E(_o1.a)*E(_o2.a),E(_nV)+E(_o1.b)*E(_o2.b),E(_nW)+E(_o1.c)*E(_o2.c));}))),_o3=_o0.a,_o4=new T(function(){var _o5=E(_o0.b),_o6=E(_nX),_o7=B(_l5(_iT,_o6.a,_o6.b,_o6.c,_o5.a,_o5.b,_o5.c)),_o8=B(_ki(_iT,_o7.a,_o7.b,_o7.c));return new T3(0,E(_o8.a),E(_o8.b),E(_o8.c));});return new T2(0,new T(function(){var _o9=E(_nu),_oa=E(_ns);return new T4(0,E(_o3),E(new T2(0,E(_nY.a)/E(_n0),E(_o9))),E(_oa),E(_o4));}),new T2(0,_o3,_o4));}),_ob=new T(function(){var _oc=B(_ny(_nY.b,new T(function(){return E(E(_nZ).b);})));return new T2(0,_oc.a,_oc.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nZ).a);}),new T(function(){return E(E(_ob).a);})),new T(function(){return E(E(_ob).b);}));}};return E(B(_nS(_n2,_n7,_n8,_n9,new T(function(){var _od=E(_nj),_oe=E(_ns)+_na,_of=Math.cos(_oe),_og=Math.sin(_oe);return new T3(0,E(_nc)*_of+E(_od.a)*_og,E(_nd)*_of+E(_od.b)*_og,E(_ne)*_of+E(_od.c)*_og);}))).a);});return new T2(0,new T(function(){var _oh=E(_nu),_oi=E(_ns);return new T4(0,E(new T3(0,E(_n7),E(_n8),E(_n9))),E(new T2(0,E(_ho),E(_oh))),E(_oi),E(_hp));}),_nv);};return B(_k5(_nq,_mM));}),_oj=new T(function(){var _ok=new T(function(){var _ol=B(_f(_ni,new T2(1,new T(function(){var _om=E(_ni);if(!_om._){return E(_lP);}else{return E(_om.a);}}),_o)));if(!_ol._){return E(_m1);}else{return E(_ol.b);}},1);return B(_m7(_ni,_ok));});return new T2(0,_oj,new T(function(){return B(_k5(_mV,_ni));}));},_on=function(_oo,_op,_oq,_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE){var _oF=B(_kH(_kh,new T3(0,E(_or),E(_os),E(_ot)))),_oG=_oF.b,_oH=E(_oF.a),_oI=B(_lj(_iT,_js,_oG,new T3(0,E(_ov),E(_ow),E(_ox)))),_oJ=E(_oG),_oK=_oJ.a,_oL=_oJ.b,_oM=_oJ.c,_oN=B(_l5(_iT,_oz,_oA,_oB,_oK,_oL,_oM)),_oO=B(_ki(_iT,_oN.a,_oN.b,_oN.c)),_oP=_oO.a,_oQ=_oO.b,_oR=_oO.c,_oS=E(_ou),_oT=new T2(0,E(new T3(0,E(_oI.a),E(_oI.b),E(_oI.c))),E(_oy)),_oU=B(_n3(_oo,_op,_oq,_oH.a,_oH.b,_oH.c,_oS,_oT,_oP,_oQ,_oR,_oK,_oL,_oM)),_oV=__lst2arr(B(_k5(_ke,_oU.a))),_oW=__lst2arr(B(_k5(_jZ,_oU.b)));return {_:0,a:_oo,b:_op,c:_oq,d:new T2(0,E(_oH),E(_oS)),e:_oT,f:new T3(0,E(_oP),E(_oQ),E(_oR)),g:_oJ,h:_oV,i:_oW};},_oX=new T(function(){return 6.283185307179586/E(_lJ);}),_oY=0.4,_oZ=new T3(0,E(_oY),E(_oY),E(_oY)),_p0=function(_){return new F(function(){return __jsNull();});},_p1=function(_p2){var _p3=B(A1(_p2,_));return E(_p3);},_p4=new T(function(){return B(_p1(_p0));}),_p5=function(_p6,_p7,_p8,_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi){var _pj=function(_pk){var _pl=E(_oX),_pm=2+_pk|0,_pn=_pm-1|0,_po=(2+_pk)*(1+_pk),_pp=E(_mM);if(!_pp._){return _pl*0;}else{var _pq=_pp.a,_pr=_pp.b,_ps=B(A1(_p6,new T(function(){return 6.283185307179586*E(_pq)/E(_lJ);}))),_pt=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_pq)+1)/E(_lJ);})));if(_ps!=_pt){if(_pm>=0){var _pu=E(_pm);if(!_pu){var _pv=function(_pw,_px){while(1){var _py=B((function(_pz,_pA){var _pB=E(_pz);if(!_pB._){return E(_pA);}else{var _pC=_pB.a,_pD=_pB.b,_pE=B(A1(_p6,new T(function(){return 6.283185307179586*E(_pC)/E(_lJ);}))),_pF=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_pC)+1)/E(_lJ);})));if(_pE!=_pF){var _pG=_pA+0/(_pE-_pF)/_po;_pw=_pD;_px=_pG;return __continue;}else{if(_pn>=0){var _pH=E(_pn);if(!_pH){var _pG=_pA+_pm/_po;_pw=_pD;_px=_pG;return __continue;}else{var _pG=_pA+_pm*B(_hA(_pE,_pH))/_po;_pw=_pD;_px=_pG;return __continue;}}else{return E(_hr);}}}})(_pw,_px));if(_py!=__continue){return _py;}}};return _pl*B(_pv(_pr,0/(_ps-_pt)/_po));}else{var _pI=function(_pJ,_pK){while(1){var _pL=B((function(_pM,_pN){var _pO=E(_pM);if(!_pO._){return E(_pN);}else{var _pP=_pO.a,_pQ=_pO.b,_pR=B(A1(_p6,new T(function(){return 6.283185307179586*E(_pP)/E(_lJ);}))),_pS=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_pP)+1)/E(_lJ);})));if(_pR!=_pS){if(_pu>=0){var _pT=_pN+(B(_hA(_pR,_pu))-B(_hA(_pS,_pu)))/(_pR-_pS)/_po;_pJ=_pQ;_pK=_pT;return __continue;}else{return E(_hr);}}else{if(_pn>=0){var _pU=E(_pn);if(!_pU){var _pT=_pN+_pm/_po;_pJ=_pQ;_pK=_pT;return __continue;}else{var _pT=_pN+_pm*B(_hA(_pR,_pU))/_po;_pJ=_pQ;_pK=_pT;return __continue;}}else{return E(_hr);}}}})(_pJ,_pK));if(_pL!=__continue){return _pL;}}};return _pl*B(_pI(_pr,(B(_hA(_ps,_pu))-B(_hA(_pt,_pu)))/(_ps-_pt)/_po));}}else{return E(_hr);}}else{if(_pn>=0){var _pV=E(_pn);if(!_pV){var _pW=function(_pX,_pY){while(1){var _pZ=B((function(_q0,_q1){var _q2=E(_q0);if(!_q2._){return E(_q1);}else{var _q3=_q2.a,_q4=_q2.b,_q5=B(A1(_p6,new T(function(){return 6.283185307179586*E(_q3)/E(_lJ);}))),_q6=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_q3)+1)/E(_lJ);})));if(_q5!=_q6){if(_pm>=0){var _q7=E(_pm);if(!_q7){var _q8=_q1+0/(_q5-_q6)/_po;_pX=_q4;_pY=_q8;return __continue;}else{var _q8=_q1+(B(_hA(_q5,_q7))-B(_hA(_q6,_q7)))/(_q5-_q6)/_po;_pX=_q4;_pY=_q8;return __continue;}}else{return E(_hr);}}else{var _q8=_q1+_pm/_po;_pX=_q4;_pY=_q8;return __continue;}}})(_pX,_pY));if(_pZ!=__continue){return _pZ;}}};return _pl*B(_pW(_pr,_pm/_po));}else{var _q9=function(_qa,_qb){while(1){var _qc=B((function(_qd,_qe){var _qf=E(_qd);if(!_qf._){return E(_qe);}else{var _qg=_qf.a,_qh=_qf.b,_qi=B(A1(_p6,new T(function(){return 6.283185307179586*E(_qg)/E(_lJ);}))),_qj=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_qg)+1)/E(_lJ);})));if(_qi!=_qj){if(_pm>=0){var _qk=E(_pm);if(!_qk){var _ql=_qe+0/(_qi-_qj)/_po;_qa=_qh;_qb=_ql;return __continue;}else{var _ql=_qe+(B(_hA(_qi,_qk))-B(_hA(_qj,_qk)))/(_qi-_qj)/_po;_qa=_qh;_qb=_ql;return __continue;}}else{return E(_hr);}}else{if(_pV>=0){var _ql=_qe+_pm*B(_hA(_qi,_pV))/_po;_qa=_qh;_qb=_ql;return __continue;}else{return E(_hr);}}}})(_qa,_qb));if(_qc!=__continue){return _qc;}}};return _pl*B(_q9(_pr,_pm*B(_hA(_ps,_pV))/_po));}}else{return E(_hr);}}}},_qm=E(_p4),_qn=1/(B(_pj(1))*_p7);return new F(function(){return _on(_p6,_oZ,new T2(0,E(new T3(0,E(_qn),E(_qn),E(_qn))),1/(B(_pj(3))*_p7)),_p8,_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi,_hp,_qm,_qm);});},_qo=0,_qp=0.4,_qq=function(_qr){return E(_qp);},_qs=1,_qt=new T(function(){var _qu=B(_p5(_qq,1.2,_qp,_qp,_qp,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qs));return {_:0,a:E(_qu.a),b:E(_qu.b),c:E(_qu.c),d:E(_qu.d),e:E(_qu.e),f:E(_qu.f),g:E(_qu.g),h:_qu.h,i:_qu.i};}),_qv=0,_qw=1.3,_qx=new T(function(){var _qy=B(_p5(_qq,1.2,_qw,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qs));return {_:0,a:E(_qy.a),b:E(_qy.b),c:E(_qy.c),d:E(_qy.d),e:E(_qy.e),f:E(_qy.f),g:E(_qy.g),h:_qy.h,i:_qy.i};}),_qz=new T(function(){var _qA=B(_p5(_qq,1.2,_qs,_qs,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qs));return {_:0,a:E(_qA.a),b:E(_qA.b),c:E(_qA.c),d:E(_qA.d),e:E(_qA.e),f:E(_qA.f),g:E(_qA.g),h:_qA.h,i:_qA.i};}),_qB=new T(function(){var _qC=B(_p5(_qq,1.2,_qo,_qs,_qs,_qo,_qo,_qo,_qo,_qo,_qo,_qo,_qs));return {_:0,a:E(_qC.a),b:E(_qC.b),c:E(_qC.c),d:E(_qC.d),e:E(_qC.e),f:E(_qC.f),g:E(_qC.g),h:_qC.h,i:_qC.i};}),_qD=new T2(1,_qB,_o),_qE=new T2(1,_qz,_qD),_qF=new T2(1,_qx,_qE),_qG=new T2(1,_qt,_qF),_qH=new T(function(){return B(unCStr("Negative range size"));}),_qI=new T(function(){return B(err(_qH));}),_qJ=function(_){var _qK=B(_hh(_qG,0))-1|0,_qL=function(_qM){if(_qM>=0){var _qN=newArr(_qM,_hn),_qO=_qN,_qP=E(_qM);if(!_qP){return new T4(0,E(_qv),E(_qK),0,_qO);}else{var _qQ=function(_qR,_qS,_){while(1){var _qT=E(_qR);if(!_qT._){return E(_);}else{var _=_qO[_qS]=_qT.a;if(_qS!=(_qP-1|0)){var _qU=_qS+1|0;_qR=_qT.b;_qS=_qU;continue;}else{return E(_);}}}},_=B((function(_qV,_qW,_qX,_){var _=_qO[_qX]=_qV;if(_qX!=(_qP-1|0)){return new F(function(){return _qQ(_qW,_qX+1|0,_);});}else{return E(_);}})(_qt,_qF,0,_));return new T4(0,E(_qv),E(_qK),_qP,_qO);}}else{return E(_qI);}};if(0>_qK){return new F(function(){return _qL(0);});}else{return new F(function(){return _qL(_qK+1|0);});}},_qY=function(_qZ){var _r0=B(A1(_qZ,_));return E(_r0);},_r1=new T(function(){return B(_qY(_qJ));}),_r2="outline",_r3="polygon",_r4=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_r5=new T(function(){return B(err(_r4));}),_r6=new T(function(){return eval("drawObjects");}),_r7=new T(function(){return eval("__strict(draw)");}),_r8=function(_r9,_ra){var _rb=jsShowI(_r9);return new F(function(){return _f(fromJSStr(_rb),_ra);});},_rc=function(_rd,_re,_rf){if(_re>=0){return new F(function(){return _r8(_re,_rf);});}else{if(_rd<=6){return new F(function(){return _r8(_re,_rf);});}else{return new T2(1,_71,new T(function(){var _rg=jsShowI(_re);return B(_f(fromJSStr(_rg),new T2(1,_70,_rf)));}));}}},_rh=new T(function(){return B(unCStr(")"));}),_ri=function(_rj,_rk){var _rl=new T(function(){var _rm=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_rc(0,_rj,_o)),_rh));})));},1);return B(_f(B(_rc(0,_rk,_o)),_rm));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_rl)));});},_rn=new T2(1,_jE,_o),_ro=function(_rp){return E(_rp);},_rq=function(_rr){return E(_rr);},_rs=function(_rt,_ru){return E(_ru);},_rv=function(_rw,_rx){return E(_rw);},_ry=function(_rz){return E(_rz);},_rA=new T2(0,_ry,_rv),_rB=function(_rC,_rD){return E(_rC);},_rE=new T5(0,_rA,_rq,_ro,_rs,_rB),_rF="d2z",_rG="d2y",_rH="w2z",_rI="w2y",_rJ="w2x",_rK="w1z",_rL="w1y",_rM="w1x",_rN="d2x",_rO="d1z",_rP="d1y",_rQ="d1x",_rR="c2y",_rS="c2x",_rT="c1y",_rU="c1x",_rV=function(_rW,_){var _rX=__get(_rW,E(_rM)),_rY=__get(_rW,E(_rL)),_rZ=__get(_rW,E(_rK)),_s0=__get(_rW,E(_rJ)),_s1=__get(_rW,E(_rI)),_s2=__get(_rW,E(_rH)),_s3=__get(_rW,E(_rU)),_s4=__get(_rW,E(_rT)),_s5=__get(_rW,E(_rS)),_s6=__get(_rW,E(_rR)),_s7=__get(_rW,E(_rQ)),_s8=__get(_rW,E(_rP)),_s9=__get(_rW,E(_rO)),_sa=__get(_rW,E(_rN)),_sb=__get(_rW,E(_rG)),_sc=__get(_rW,E(_rF));return new T6(0,E(new T3(0,E(_rX),E(_rY),E(_rZ))),E(new T3(0,E(_s0),E(_s1),E(_s2))),E(new T2(0,E(_s3),E(_s4))),E(new T2(0,E(_s5),E(_s6))),E(new T3(0,E(_s7),E(_s8),E(_s9))),E(new T3(0,E(_sa),E(_sb),E(_sc))));},_sd=function(_se,_){var _sf=E(_se);if(!_sf._){return _o;}else{var _sg=B(_rV(E(_sf.a),_)),_sh=B(_sd(_sf.b,_));return new T2(1,_sg,_sh);}},_si=function(_sj){var _sk=E(_sj);return (E(_sk.b)-E(_sk.a)|0)+1|0;},_sl=function(_sm,_sn){var _so=E(_sm),_sp=E(_sn);return (E(_so.a)>_sp)?false:_sp<=E(_so.b);},_sq=function(_sr){return new F(function(){return _rc(0,E(_sr),_o);});},_ss=function(_st,_su,_sv){return new F(function(){return _rc(E(_st),E(_su),_sv);});},_sw=function(_sx,_sy){return new F(function(){return _rc(0,E(_sx),_sy);});},_sz=function(_sA,_sB){return new F(function(){return _2B(_sw,_sA,_sB);});},_sC=new T3(0,_ss,_sq,_sz),_sD=0,_sE=function(_sF,_sG,_sH){return new F(function(){return A1(_sF,new T2(1,_2y,new T(function(){return B(A1(_sG,_sH));})));});},_sI=new T(function(){return B(unCStr("foldr1"));}),_sJ=new T(function(){return B(_lM(_sI));}),_sK=function(_sL,_sM){var _sN=E(_sM);if(!_sN._){return E(_sJ);}else{var _sO=_sN.a,_sP=E(_sN.b);if(!_sP._){return E(_sO);}else{return new F(function(){return A2(_sL,_sO,new T(function(){return B(_sK(_sL,_sP));}));});}}},_sQ=new T(function(){return B(unCStr(" out of range "));}),_sR=new T(function(){return B(unCStr("}.index: Index "));}),_sS=new T(function(){return B(unCStr("Ix{"));}),_sT=new T2(1,_70,_o),_sU=new T2(1,_70,_sT),_sV=0,_sW=function(_sX){return E(E(_sX).a);},_sY=function(_sZ,_t0,_t1,_t2,_t3){var _t4=new T(function(){var _t5=new T(function(){var _t6=new T(function(){var _t7=new T(function(){var _t8=new T(function(){return B(A3(_sK,_sE,new T2(1,new T(function(){return B(A3(_sW,_t1,_sV,_t2));}),new T2(1,new T(function(){return B(A3(_sW,_t1,_sV,_t3));}),_o)),_sU));});return B(_f(_sQ,new T2(1,_71,new T2(1,_71,_t8))));});return B(A(_sW,[_t1,_sD,_t0,new T2(1,_70,_t7)]));});return B(_f(_sR,new T2(1,_71,_t6)));},1);return B(_f(_sZ,_t5));},1);return new F(function(){return err(B(_f(_sS,_t4)));});},_t9=function(_ta,_tb,_tc,_td,_te){return new F(function(){return _sY(_ta,_tb,_te,_tc,_td);});},_tf=function(_tg,_th,_ti,_tj){var _tk=E(_ti);return new F(function(){return _t9(_tg,_th,_tk.a,_tk.b,_tj);});},_tl=function(_tm,_tn,_to,_tp){return new F(function(){return _tf(_tp,_to,_tn,_tm);});},_tq=new T(function(){return B(unCStr("Int"));}),_tr=function(_ts,_tt){return new F(function(){return _tl(_sC,_tt,_ts,_tq);});},_tu=function(_tv,_tw){var _tx=E(_tv),_ty=E(_tx.a),_tz=E(_tw);if(_ty>_tz){return new F(function(){return _tr(_tz,_tx);});}else{if(_tz>E(_tx.b)){return new F(function(){return _tr(_tz,_tx);});}else{return _tz-_ty|0;}}},_tA=function(_tB,_tC){if(_tB<=_tC){var _tD=function(_tE){return new T2(1,_tE,new T(function(){if(_tE!=_tC){return B(_tD(_tE+1|0));}else{return __Z;}}));};return new F(function(){return _tD(_tB);});}else{return __Z;}},_tF=function(_tG,_tH){return new F(function(){return _tA(E(_tG),E(_tH));});},_tI=function(_tJ){var _tK=E(_tJ);return new F(function(){return _tF(_tK.a,_tK.b);});},_tL=function(_tM){var _tN=E(_tM),_tO=E(_tN.a),_tP=E(_tN.b);return (_tO>_tP)?E(_sD):(_tP-_tO|0)+1|0;},_tQ=function(_tR,_tS){return E(_tR)-E(_tS)|0;},_tT=function(_tU,_tV){return new F(function(){return _tQ(_tV,E(_tU).a);});},_tW=function(_tX,_tY){return E(_tX)==E(_tY);},_tZ=function(_u0,_u1){return E(_u0)!=E(_u1);},_u2=new T2(0,_tW,_tZ),_u3=function(_u4,_u5){var _u6=E(_u4),_u7=E(_u5);return (_u6>_u7)?E(_u6):E(_u7);},_u8=function(_u9,_ua){var _ub=E(_u9),_uc=E(_ua);return (_ub>_uc)?E(_uc):E(_ub);},_ud=function(_ue,_uf){return (_ue>=_uf)?(_ue!=_uf)?2:1:0;},_ug=function(_uh,_ui){return new F(function(){return _ud(E(_uh),E(_ui));});},_uj=function(_uk,_ul){return E(_uk)>=E(_ul);},_um=function(_un,_uo){return E(_un)>E(_uo);},_up=function(_uq,_ur){return E(_uq)<=E(_ur);},_us=function(_ut,_uu){return E(_ut)<E(_uu);},_uv={_:0,a:_u2,b:_ug,c:_us,d:_up,e:_um,f:_uj,g:_u3,h:_u8},_uw={_:0,a:_uv,b:_tI,c:_tu,d:_tT,e:_sl,f:_tL,g:_si},_ux=function(_uy,_uz,_){while(1){var _uA=B((function(_uB,_uC,_){var _uD=E(_uB);if(!_uD._){return new T2(0,_jE,_uC);}else{var _uE=B(A2(_uD.a,_uC,_));_uy=_uD.b;_uz=new T(function(){return E(E(_uE).b);});return __continue;}})(_uy,_uz,_));if(_uA!=__continue){return _uA;}}},_uF=function(_uG,_uH){return new T2(1,_uG,_uH);},_uI=function(_uJ,_uK){var _uL=E(_uK);return new T2(0,_uL.a,_uL.b);},_uM=function(_uN){return E(E(_uN).f);},_uO=function(_uP,_uQ,_uR){var _uS=E(_uQ),_uT=_uS.a,_uU=_uS.b,_uV=function(_){var _uW=B(A2(_uM,_uP,_uS));if(_uW>=0){var _uX=newArr(_uW,_hn),_uY=_uX,_uZ=E(_uW);if(!_uZ){return new T(function(){return new T4(0,E(_uT),E(_uU),0,_uY);});}else{var _v0=function(_v1,_v2,_){while(1){var _v3=E(_v1);if(!_v3._){return E(_);}else{var _=_uY[_v2]=_v3.a;if(_v2!=(_uZ-1|0)){var _v4=_v2+1|0;_v1=_v3.b;_v2=_v4;continue;}else{return E(_);}}}},_=B(_v0(_uR,0,_));return new T(function(){return new T4(0,E(_uT),E(_uU),_uZ,_uY);});}}else{return E(_qI);}};return new F(function(){return _qY(_uV);});},_v5=function(_v6,_v7,_v8,_v9){var _va=new T(function(){var _vb=E(_v9),_vc=_vb.c-1|0,_vd=new T(function(){return B(A2(_cW,_v7,_o));});if(0<=_vc){var _ve=new T(function(){return B(_96(_v7));}),_vf=function(_vg){var _vh=new T(function(){var _vi=new T(function(){return B(A1(_v8,new T(function(){return E(_vb.d[_vg]);})));});return B(A3(_9e,_ve,_uF,_vi));});return new F(function(){return A3(_9c,_v7,_vh,new T(function(){if(_vg!=_vc){return B(_vf(_vg+1|0));}else{return E(_vd);}}));});};return B(_vf(0));}else{return E(_vd);}}),_vj=new T(function(){return B(_uI(_v6,_v9));});return new F(function(){return A3(_9e,B(_96(_v7)),function(_vk){return new F(function(){return _uO(_v6,_vj,_vk);});},_va);});},_vl=function(_vm,_vn,_vo,_vp,_vq,_vr,_vs,_vt,_vu){var _vv=B(_7l(_vm));return new T2(0,new T3(0,E(B(A1(B(A1(_vv,_vn)),_vr))),E(B(A1(B(A1(_vv,_vo)),_vs))),E(B(A1(B(A1(_vv,_vp)),_vt)))),B(A1(B(A1(_vv,_vq)),_vu)));},_vw=function(_vx,_vy,_vz,_vA,_vB,_vC,_vD,_vE,_vF){var _vG=B(_6I(_vx));return new T2(0,new T3(0,E(B(A1(B(A1(_vG,_vy)),_vC))),E(B(A1(B(A1(_vG,_vz)),_vD))),E(B(A1(B(A1(_vG,_vA)),_vE)))),B(A1(B(A1(_vG,_vB)),_vF)));},_vH=1.0e-2,_vI=function(_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_vR,_vS,_vT,_vU,_vV,_vW,_vX,_vY,_vZ){var _w0=B(_vl(_in,_vQ,_vR,_vS,_vT,_vH,_vH,_vH,_vH)),_w1=E(_w0.a),_w2=B(_vw(_in,_vM,_vN,_vO,_vP,_w1.a,_w1.b,_w1.c,_w0.b)),_w3=E(_w2.a);return new F(function(){return _on(_vJ,_vK,_vL,_w3.a,_w3.b,_w3.c,_w2.b,_vQ,_vR,_vS,_vT,_vU,_vV,_vW,_vX,_vY,_vZ);});},_w4=function(_w5){var _w6=E(_w5),_w7=E(_w6.d),_w8=E(_w7.a),_w9=E(_w6.e),_wa=E(_w9.a),_wb=E(_w6.f),_wc=B(_vI(_w6.a,_w6.b,_w6.c,_w8.a,_w8.b,_w8.c,_w7.b,_wa.a,_wa.b,_wa.c,_w9.b,_wb.a,_wb.b,_wb.c,_w6.g,_w6.h,_w6.i));return {_:0,a:E(_wc.a),b:E(_wc.b),c:E(_wc.c),d:E(_wc.d),e:E(_wc.e),f:E(_wc.f),g:E(_wc.g),h:_wc.h,i:_wc.i};},_wd=function(_we,_wf,_wg,_wh,_wi,_wj,_wk,_wl,_wm){var _wn=B(_7j(B(_7h(_we))));return new F(function(){return A3(_6I,_wn,new T(function(){return B(_7n(_we,_wf,_wg,_wh,_wj,_wk,_wl));}),new T(function(){return B(A3(_7l,_wn,_wi,_wm));}));});},_wo=new T(function(){return B(unCStr("base"));}),_wp=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_wq=new T(function(){return B(unCStr("IOException"));}),_wr=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_wo,_wp,_wq),_ws=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_wr,_o,_o),_wt=function(_wu){return E(_ws);},_wv=function(_ww){var _wx=E(_ww);return new F(function(){return _28(B(_26(_wx.a)),_wt,_wx.b);});},_wy=new T(function(){return B(unCStr(": "));}),_wz=new T(function(){return B(unCStr(")"));}),_wA=new T(function(){return B(unCStr(" ("));}),_wB=new T(function(){return B(unCStr("interrupted"));}),_wC=new T(function(){return B(unCStr("system error"));}),_wD=new T(function(){return B(unCStr("unsatisified constraints"));}),_wE=new T(function(){return B(unCStr("user error"));}),_wF=new T(function(){return B(unCStr("permission denied"));}),_wG=new T(function(){return B(unCStr("illegal operation"));}),_wH=new T(function(){return B(unCStr("end of file"));}),_wI=new T(function(){return B(unCStr("resource exhausted"));}),_wJ=new T(function(){return B(unCStr("resource busy"));}),_wK=new T(function(){return B(unCStr("does not exist"));}),_wL=new T(function(){return B(unCStr("already exists"));}),_wM=new T(function(){return B(unCStr("resource vanished"));}),_wN=new T(function(){return B(unCStr("timeout"));}),_wO=new T(function(){return B(unCStr("unsupported operation"));}),_wP=new T(function(){return B(unCStr("hardware fault"));}),_wQ=new T(function(){return B(unCStr("inappropriate type"));}),_wR=new T(function(){return B(unCStr("invalid argument"));}),_wS=new T(function(){return B(unCStr("failed"));}),_wT=new T(function(){return B(unCStr("protocol error"));}),_wU=function(_wV,_wW){switch(E(_wV)){case 0:return new F(function(){return _f(_wL,_wW);});break;case 1:return new F(function(){return _f(_wK,_wW);});break;case 2:return new F(function(){return _f(_wJ,_wW);});break;case 3:return new F(function(){return _f(_wI,_wW);});break;case 4:return new F(function(){return _f(_wH,_wW);});break;case 5:return new F(function(){return _f(_wG,_wW);});break;case 6:return new F(function(){return _f(_wF,_wW);});break;case 7:return new F(function(){return _f(_wE,_wW);});break;case 8:return new F(function(){return _f(_wD,_wW);});break;case 9:return new F(function(){return _f(_wC,_wW);});break;case 10:return new F(function(){return _f(_wT,_wW);});break;case 11:return new F(function(){return _f(_wS,_wW);});break;case 12:return new F(function(){return _f(_wR,_wW);});break;case 13:return new F(function(){return _f(_wQ,_wW);});break;case 14:return new F(function(){return _f(_wP,_wW);});break;case 15:return new F(function(){return _f(_wO,_wW);});break;case 16:return new F(function(){return _f(_wN,_wW);});break;case 17:return new F(function(){return _f(_wM,_wW);});break;default:return new F(function(){return _f(_wB,_wW);});}},_wX=new T(function(){return B(unCStr("}"));}),_wY=new T(function(){return B(unCStr("{handle: "));}),_wZ=function(_x0,_x1,_x2,_x3,_x4,_x5){var _x6=new T(function(){var _x7=new T(function(){var _x8=new T(function(){var _x9=E(_x3);if(!_x9._){return E(_x5);}else{var _xa=new T(function(){return B(_f(_x9,new T(function(){return B(_f(_wz,_x5));},1)));},1);return B(_f(_wA,_xa));}},1);return B(_wU(_x1,_x8));}),_xb=E(_x2);if(!_xb._){return E(_x7);}else{return B(_f(_xb,new T(function(){return B(_f(_wy,_x7));},1)));}}),_xc=E(_x4);if(!_xc._){var _xd=E(_x0);if(!_xd._){return E(_x6);}else{var _xe=E(_xd.a);if(!_xe._){var _xf=new T(function(){var _xg=new T(function(){return B(_f(_wX,new T(function(){return B(_f(_wy,_x6));},1)));},1);return B(_f(_xe.a,_xg));},1);return new F(function(){return _f(_wY,_xf);});}else{var _xh=new T(function(){var _xi=new T(function(){return B(_f(_wX,new T(function(){return B(_f(_wy,_x6));},1)));},1);return B(_f(_xe.a,_xi));},1);return new F(function(){return _f(_wY,_xh);});}}}else{return new F(function(){return _f(_xc.a,new T(function(){return B(_f(_wy,_x6));},1));});}},_xj=function(_xk){var _xl=E(_xk);return new F(function(){return _wZ(_xl.a,_xl.b,_xl.c,_xl.d,_xl.f,_o);});},_xm=function(_xn,_xo,_xp){var _xq=E(_xo);return new F(function(){return _wZ(_xq.a,_xq.b,_xq.c,_xq.d,_xq.f,_xp);});},_xr=function(_xs,_xt){var _xu=E(_xs);return new F(function(){return _wZ(_xu.a,_xu.b,_xu.c,_xu.d,_xu.f,_xt);});},_xv=function(_xw,_xx){return new F(function(){return _2B(_xr,_xw,_xx);});},_xy=new T3(0,_xm,_xj,_xv),_xz=new T(function(){return new T5(0,_wt,_xy,_xA,_wv,_xj);}),_xA=function(_xB){return new T2(0,_xz,_xB);},_xC=__Z,_xD=7,_xE=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:77:3-9"));}),_xF=new T6(0,_xC,_xD,_o,_xE,_xC,_xC),_xG=new T(function(){return B(_xA(_xF));}),_xH=function(_){return new F(function(){return die(_xG);});},_xI=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:76:3-9"));}),_xJ=new T6(0,_xC,_xD,_o,_xI,_xC,_xC),_xK=new T(function(){return B(_xA(_xJ));}),_xL=function(_){return new F(function(){return die(_xK);});},_xM=function(_xN,_){return new T2(0,_o,_xN);},_xO=1,_xP=new T(function(){return B(unCStr(")"));}),_xQ=function(_xR,_xS){var _xT=new T(function(){var _xU=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_rc(0,_xR,_o)),_xP));})));},1);return B(_f(B(_rc(0,_xS,_o)),_xU));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_xT)));});},_xV=function(_xW,_xX){var _xY=new T(function(){var _xZ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_rc(0,_xX,_o)),_xP));})));},1);return B(_f(B(_rc(0,_xW,_o)),_xZ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_xY)));});},_y0=0.6,_y1=function(_y2){var _y3=E(_y2);if(!_y3._){return E(_xM);}else{var _y4=new T(function(){return B(_y1(_y3.b));}),_y5=function(_y6){var _y7=E(_y6);if(!_y7._){return E(_y4);}else{var _y8=_y7.a,_y9=new T(function(){return B(_y5(_y7.b));}),_ya=new T(function(){return 0.1*E(E(_y8).e)/1.0e-2;}),_yb=new T(function(){var _yc=E(_y8);if(_yc.a!=_yc.b){return E(_xO);}else{return E(_y0);}}),_yd=function(_ye,_){var _yf=E(_ye),_yg=_yf.c,_yh=_yf.d,_yi=E(_yf.a),_yj=E(_yf.b),_yk=E(_y8),_yl=_yk.a,_ym=_yk.b,_yn=E(_yk.c),_yo=_yn.b,_yp=E(_yn.a),_yq=_yp.a,_yr=_yp.b,_ys=_yp.c,_yt=E(_yk.d),_yu=_yt.b,_yv=E(_yt.a),_yw=_yv.a,_yx=_yv.b,_yy=_yv.c;if(_yi>_yl){return new F(function(){return _xL(_);});}else{if(_yl>_yj){return new F(function(){return _xL(_);});}else{if(_yi>_ym){return new F(function(){return _xH(_);});}else{if(_ym>_yj){return new F(function(){return _xH(_);});}else{var _yz=_yl-_yi|0;if(0>_yz){return new F(function(){return _xQ(_yg,_yz);});}else{if(_yz>=_yg){return new F(function(){return _xQ(_yg,_yz);});}else{var _yA=E(_yh[_yz]),_yB=E(_yA.c),_yC=_yB.b,_yD=E(_yB.a),_yE=_yD.a,_yF=_yD.b,_yG=_yD.c,_yH=E(_yA.e),_yI=E(_yH.a),_yJ=B(_vl(_in,_yq,_yr,_ys,_yo,_yE,_yF,_yG,_yC)),_yK=E(_yJ.a),_yL=B(_vl(_in,_yK.a,_yK.b,_yK.c,_yJ.b,_yq,_yr,_ys,_yo)),_yM=E(_yL.a),_yN=_ym-_yi|0;if(0>_yN){return new F(function(){return _xV(_yN,_yg);});}else{if(_yN>=_yg){return new F(function(){return _xV(_yN,_yg);});}else{var _yO=E(_yh[_yN]),_yP=E(_yO.c),_yQ=_yP.b,_yR=E(_yP.a),_yS=_yR.a,_yT=_yR.b,_yU=_yR.c,_yV=E(_yO.e),_yW=E(_yV.a),_yX=B(_vl(_in,_yw,_yx,_yy,_yu,_yS,_yT,_yU,_yQ)),_yY=E(_yX.a),_yZ=B(_vl(_in,_yY.a,_yY.b,_yY.c,_yX.b,_yw,_yx,_yy,_yu)),_z0=E(_yZ.a),_z1=E(_yM.a)+E(_yM.b)+E(_yM.c)+E(_yL.b)+E(_z0.a)+E(_z0.b)+E(_z0.c)+E(_yZ.b);if(!_z1){var _z2=B(A2(_y9,_yf,_));return new T2(0,new T2(1,_jE,new T(function(){return E(E(_z2).a);})),new T(function(){return E(E(_z2).b);}));}else{var _z3=new T(function(){return  -((B(_wd(_iT,_yI.a,_yI.b,_yI.c,_yH.b,_yq,_yr,_ys,_yo))-B(_wd(_iT,_yW.a,_yW.b,_yW.c,_yV.b,_yw,_yx,_yy,_yu))-E(_ya))/_z1);}),_z4=function(_z5,_z6,_z7,_z8,_){var _z9=new T(function(){var _za=function(_zb,_zc,_zd,_ze,_zf){if(_zb>_ym){return E(_zf);}else{if(_ym>_zc){return E(_zf);}else{var _zg=function(_){var _zh=newArr(_zd,_hn),_zi=_zh,_zj=function(_zk,_){while(1){if(_zk!=_zd){var _=_zi[_zk]=_ze[_zk],_zl=_zk+1|0;_zk=_zl;continue;}else{return E(_);}}},_=B(_zj(0,_)),_zm=_ym-_zb|0;if(0>_zm){return new F(function(){return _xV(_zm,_zd);});}else{if(_zm>=_zd){return new F(function(){return _xV(_zm,_zd);});}else{var _=_zi[_zm]=new T(function(){var _zn=E(_ze[_zm]),_zo=E(_zn.e),_zp=E(_zo.a),_zq=B(_vl(_in,_yS,_yT,_yU,_yQ,_yw,_yx,_yy,_yu)),_zr=E(_zq.a),_zs=E(_z3)*E(_yb),_zt=B(_vl(_in,_zr.a,_zr.b,_zr.c,_zq.b,_zs,_zs,_zs,_zs)),_zu=E(_zt.a),_zv=B(_vw(_in,_zp.a,_zp.b,_zp.c,_zo.b, -E(_zu.a), -E(_zu.b), -E(_zu.c), -E(_zt.b)));return {_:0,a:E(_zn.a),b:E(_zn.b),c:E(_zn.c),d:E(_zn.d),e:E(new T2(0,E(_zv.a),E(_zv.b))),f:E(_zn.f),g:E(_zn.g),h:_zn.h,i:_zn.i};});return new T4(0,E(_zb),E(_zc),_zd,_zi);}}};return new F(function(){return _qY(_zg);});}}};if(_z5>_yl){return B(_za(_z5,_z6,_z7,_z8,new T4(0,E(_z5),E(_z6),_z7,_z8)));}else{if(_yl>_z6){return B(_za(_z5,_z6,_z7,_z8,new T4(0,E(_z5),E(_z6),_z7,_z8)));}else{var _zw=function(_){var _zx=newArr(_z7,_hn),_zy=_zx,_zz=function(_zA,_){while(1){if(_zA!=_z7){var _=_zy[_zA]=_z8[_zA],_zB=_zA+1|0;_zA=_zB;continue;}else{return E(_);}}},_=B(_zz(0,_)),_zC=_yl-_z5|0;if(0>_zC){return new F(function(){return _xQ(_z7,_zC);});}else{if(_zC>=_z7){return new F(function(){return _xQ(_z7,_zC);});}else{var _=_zy[_zC]=new T(function(){var _zD=E(_z8[_zC]),_zE=E(_zD.e),_zF=E(_zE.a),_zG=B(_vl(_in,_yE,_yF,_yG,_yC,_yq,_yr,_ys,_yo)),_zH=E(_zG.a),_zI=E(_z3)*E(_yb),_zJ=B(_vl(_in,_zH.a,_zH.b,_zH.c,_zG.b,_zI,_zI,_zI,_zI)),_zK=E(_zJ.a),_zL=B(_vw(_in,_zF.a,_zF.b,_zF.c,_zE.b,_zK.a,_zK.b,_zK.c,_zJ.b));return {_:0,a:E(_zD.a),b:E(_zD.b),c:E(_zD.c),d:E(_zD.d),e:E(new T2(0,E(_zL.a),E(_zL.b))),f:E(_zD.f),g:E(_zD.g),h:_zD.h,i:_zD.i};});return new T4(0,E(_z5),E(_z6),_z7,_zy);}}},_zM=B(_qY(_zw));return B(_za(E(_zM.a),E(_zM.b),_zM.c,_zM.d,_zM));}}});return new T2(0,_jE,_z9);};if(!E(_yk.f)){var _zN=B(_z4(_yi,_yj,_yg,_yh,_)),_zO=B(A2(_y9,new T(function(){return E(E(_zN).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_zN).a);}),new T(function(){return E(E(_zO).a);})),new T(function(){return E(E(_zO).b);}));}else{if(E(_z3)<0){var _zP=B(A2(_y9,_yf,_));return new T2(0,new T2(1,_jE,new T(function(){return E(E(_zP).a);})),new T(function(){return E(E(_zP).b);}));}else{var _zQ=B(_z4(_yi,_yj,_yg,_yh,_)),_zR=B(A2(_y9,new T(function(){return E(E(_zQ).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_zQ).a);}),new T(function(){return E(E(_zR).a);})),new T(function(){return E(E(_zR).b);}));}}}}}}}}}}}};return E(_yd);}};return new F(function(){return _y5(_y3.a);});}},_zS=function(_,_zT){var _zU=new T(function(){return B(_y1(E(_zT).a));}),_zV=function(_zW){var _zX=E(_zW);return (_zX==1)?E(new T2(1,_zU,_o)):new T2(1,_zU,new T(function(){return B(_zV(_zX-1|0));}));},_zY=B(_ux(B(_zV(5)),new T(function(){return E(E(_zT).b);}),_)),_zZ=new T(function(){return B(_v5(_uw,_rE,_w4,new T(function(){return E(E(_zY).b);})));});return new T2(0,_jE,_zZ);},_A0=function(_A1,_A2,_A3,_A4,_A5){var _A6=B(_7j(B(_7h(_A1))));return new F(function(){return A3(_6I,_A6,new T(function(){return B(A3(_7l,_A6,_A2,_A4));}),new T(function(){return B(A3(_7l,_A6,_A3,_A5));}));});},_A7=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_A8=new T6(0,_xC,_xD,_o,_A7,_xC,_xC),_A9=new T(function(){return B(_xA(_A8));}),_Aa=function(_){return new F(function(){return die(_A9);});},_Ab=false,_Ac=true,_Ad=function(_Ae){var _Af=E(_Ae),_Ag=E(_Af.b),_Ah=E(_Af.e),_Ai=E(_Ah.a),_Aj=E(_Af.g),_Ak=B(_l5(_iT,_Ag.a,_Ag.b,_Ag.c,_Aj.a,_Aj.b,_Aj.c));return {_:0,a:E(_Af.a),b:E(_Ag),c:E(_Af.c),d:E(_Af.d),e:E(new T2(0,E(new T3(0,E(_Ai.a)+E(_Ak.a)*1.0e-2,E(_Ai.b)+E(_Ak.b)*1.0e-2,E(_Ai.c)+E(_Ak.c)*1.0e-2)),E(_Ah.b))),f:E(_Af.f),g:E(_Aj),h:_Af.h,i:_Af.i};},_Al=new T(function(){return eval("collide");}),_Am=function(_An){var _Ao=E(_An);if(!_Ao._){return __Z;}else{return new F(function(){return _f(_Ao.a,new T(function(){return B(_Am(_Ao.b));},1));});}},_Ap=0,_Aq=new T3(0,E(_Ap),E(_Ap),E(_Ap)),_Ar=new T2(0,E(_Aq),E(_Ap)),_As=new T2(0,_iT,_js),_At=new T(function(){return B(_gT(_As));}),_Au=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:50:7-13"));}),_Av=new T6(0,_xC,_xD,_o,_Au,_xC,_xC),_Aw=new T(function(){return B(_xA(_Av));}),_Ax=function(_Ay,_){var _Az=B(_v5(_uw,_rE,_Ad,_Ay)),_AA=E(_Az.a),_AB=E(_Az.b);if(_AA<=_AB){var _AC=function(_AD,_AE,_){if(_AD<=_AB){var _AF=E(_AE),_AG=function(_AH,_AI,_AJ,_AK,_AL,_){if(_AI>_AD){return new F(function(){return die(_Aw);});}else{if(_AD>_AJ){return new F(function(){return die(_Aw);});}else{if(_AI>_AH){return new F(function(){return _Aa(_);});}else{if(_AH>_AJ){return new F(function(){return _Aa(_);});}else{var _AM=_AD-_AI|0;if(0>_AM){return new F(function(){return _xV(_AM,_AK);});}else{if(_AM>=_AK){return new F(function(){return _xV(_AM,_AK);});}else{var _AN=E(_AL[_AM]),_AO=_AH-_AI|0;if(0>_AO){return new F(function(){return _xV(_AO,_AK);});}else{if(_AO>=_AK){return new F(function(){return _xV(_AO,_AK);});}else{var _AP=E(_AL[_AO]),_AQ=__app2(E(_Al),B(_jF(new T2(1,new T2(0,_r3,_AN.h),new T2(1,new T2(0,_r2,_AN.i),_o)))),B(_jF(new T2(1,new T2(0,_r3,_AP.h),new T2(1,new T2(0,_r2,_AP.i),_o))))),_AR=__arr2lst(0,_AQ),_AS=B(_sd(_AR,_));if(_AH!=_AB){var _AT=B(_AG(_AH+1|0,_AI,_AJ,_AK,_AL,_)),_AU=new T(function(){var _AV=new T(function(){return _AD!=_AH;}),_AW=function(_AX){var _AY=E(_AX);if(!_AY._){return __Z;}else{var _AZ=_AY.b,_B0=E(_AY.a),_B1=E(_B0.b),_B2=E(_B0.a),_B3=E(_B0.c),_B4=_B3.a,_B5=_B3.b,_B6=E(_B0.e),_B7=E(_B0.d),_B8=_B7.a,_B9=_B7.b,_Ba=E(_B0.f),_Bb=new T(function(){var _Bc=B(_ki(_iT,_Ba.a,_Ba.b,_Ba.c)),_Bd=Math.sqrt(B(_A0(_iT,_B8,_B9,_B8,_B9)));return new T3(0,_Bd*E(_Bc.a),_Bd*E(_Bc.b),_Bd*E(_Bc.c));}),_Be=new T(function(){var _Bf=B(_ki(_iT,_B6.a,_B6.b,_B6.c)),_Bg=Math.sqrt(B(_A0(_iT,_B4,_B5,_B4,_B5)));return new T3(0,_Bg*E(_Bf.a),_Bg*E(_Bf.b),_Bg*E(_Bf.c));}),_Bh=new T(function(){var _Bi=B(A1(_At,_B1)),_Bj=B(_ki(_iT,_Bi.a,_Bi.b,_Bi.c));return new T3(0,E(_Bj.a),E(_Bj.b),E(_Bj.c));}),_Bk=new T(function(){var _Bl=B(A1(_At,_B2)),_Bm=B(_ki(_iT,_Bl.a,_Bl.b,_Bl.c));return new T3(0,E(_Bm.a),E(_Bm.b),E(_Bm.c));}),_Bn=E(_B1.a)+ -E(_B2.a),_Bo=E(_B1.b)+ -E(_B2.b),_Bp=E(_B1.c)+ -E(_B2.c),_Bq=new T(function(){return Math.sqrt(B(_7n(_iT,_Bn,_Bo,_Bp,_Bn,_Bo,_Bp)));}),_Br=new T(function(){var _Bs=1/E(_Bq);return new T3(0,_Bn*_Bs,_Bo*_Bs,_Bp*_Bs);});return (!E(_AV))?new T2(1,new T(function(){var _Bt=E(_Br),_Bu=E(_Bt.b),_Bv=E(_Bt.c),_Bw=E(_Bt.a),_Bx=E(_Bk),_By=E(_Bx.c),_Bz=E(_Bx.b),_BA=E(_Bx.a),_BB=E(_Be),_BC=E(_BB.c),_BD=E(_BB.b),_BE=E(_BB.a),_BF=_Bu*_By-_Bz*_Bv,_BG=_Bv*_BA-_By*_Bw,_BH=_Bw*_Bz-_BA*_Bu,_BI=B(_7n(_iT,_BG*_BC-_BD*_BH,_BH*_BE-_BC*_BF,_BF*_BD-_BE*_BG,_BA,_Bz,_By));return new T6(0,_AD,_AH,E(new T2(0,E(new T3(0,E(_BF),E(_BG),E(_BH))),E(_BI))),E(_Ar),_Bq,_Ab);}),new T2(1,new T(function(){var _BJ=E(_Br),_BK=E(_BJ.b),_BL=E(_BJ.c),_BM=E(_BJ.a),_BN=E(_Bh),_BO=E(_BN.c),_BP=E(_BN.b),_BQ=E(_BN.a),_BR=E(_Bb),_BS=E(_BR.c),_BT=E(_BR.b),_BU=E(_BR.a),_BV=_BK*_BO-_BP*_BL,_BW=_BL*_BQ-_BO*_BM,_BX=_BM*_BP-_BQ*_BK,_BY=B(_7n(_iT,_BW*_BS-_BT*_BX,_BX*_BU-_BS*_BV,_BV*_BT-_BU*_BW,_BQ,_BP,_BO));return new T6(0,_AD,_AH,E(_Ar),E(new T2(0,E(new T3(0,E(_BV),E(_BW),E(_BX))),E(_BY))),_Bq,_Ab);}),new T(function(){return B(_AW(_AZ));}))):new T2(1,new T(function(){var _BZ=E(_Br),_C0=E(_BZ.b),_C1=E(_BZ.c),_C2=E(_BZ.a),_C3=E(_Bk),_C4=_C3.a,_C5=_C3.b,_C6=_C3.c,_C7=B(_l5(_iT,_C2,_C0,_C1,_C4,_C5,_C6)),_C8=E(_Be),_C9=E(_C8.c),_Ca=E(_C8.b),_Cb=E(_C8.a),_Cc=B(_7n(_iT,_C0*_C9-_Ca*_C1,_C1*_Cb-_C9*_C2,_C2*_Ca-_Cb*_C0,_C4,_C5,_C6)),_Cd=E(_Bh),_Ce=_Cd.a,_Cf=_Cd.b,_Cg=_Cd.c,_Ch=B(_l5(_iT,_C2,_C0,_C1,_Ce,_Cf,_Cg)),_Ci=E(_Bb),_Cj=E(_Ci.c),_Ck=E(_Ci.b),_Cl=E(_Ci.a),_Cm=B(_7n(_iT,_C0*_Cj-_Ck*_C1,_C1*_Cl-_Cj*_C2,_C2*_Ck-_Cl*_C0,_Ce,_Cf,_Cg));return new T6(0,_AD,_AH,E(new T2(0,E(new T3(0,E(_C7.a),E(_C7.b),E(_C7.c))),E(_Cc))),E(new T2(0,E(new T3(0,E(_Ch.a),E(_Ch.b),E(_Ch.c))),E(_Cm))),_Bq,_Ac);}),new T(function(){return B(_AW(_AZ));}));}};return B(_AW(_AS));});return new T2(0,new T2(1,_AU,new T(function(){return E(E(_AT).a);})),new T(function(){return E(E(_AT).b);}));}else{var _Cn=new T(function(){var _Co=new T(function(){return _AD!=_AH;}),_Cp=function(_Cq){var _Cr=E(_Cq);if(!_Cr._){return __Z;}else{var _Cs=_Cr.b,_Ct=E(_Cr.a),_Cu=E(_Ct.b),_Cv=E(_Ct.a),_Cw=E(_Ct.c),_Cx=_Cw.a,_Cy=_Cw.b,_Cz=E(_Ct.e),_CA=E(_Ct.d),_CB=_CA.a,_CC=_CA.b,_CD=E(_Ct.f),_CE=new T(function(){var _CF=B(_ki(_iT,_CD.a,_CD.b,_CD.c)),_CG=Math.sqrt(B(_A0(_iT,_CB,_CC,_CB,_CC)));return new T3(0,_CG*E(_CF.a),_CG*E(_CF.b),_CG*E(_CF.c));}),_CH=new T(function(){var _CI=B(_ki(_iT,_Cz.a,_Cz.b,_Cz.c)),_CJ=Math.sqrt(B(_A0(_iT,_Cx,_Cy,_Cx,_Cy)));return new T3(0,_CJ*E(_CI.a),_CJ*E(_CI.b),_CJ*E(_CI.c));}),_CK=new T(function(){var _CL=B(A1(_At,_Cu)),_CM=B(_ki(_iT,_CL.a,_CL.b,_CL.c));return new T3(0,E(_CM.a),E(_CM.b),E(_CM.c));}),_CN=new T(function(){var _CO=B(A1(_At,_Cv)),_CP=B(_ki(_iT,_CO.a,_CO.b,_CO.c));return new T3(0,E(_CP.a),E(_CP.b),E(_CP.c));}),_CQ=E(_Cu.a)+ -E(_Cv.a),_CR=E(_Cu.b)+ -E(_Cv.b),_CS=E(_Cu.c)+ -E(_Cv.c),_CT=new T(function(){return Math.sqrt(B(_7n(_iT,_CQ,_CR,_CS,_CQ,_CR,_CS)));}),_CU=new T(function(){var _CV=1/E(_CT);return new T3(0,_CQ*_CV,_CR*_CV,_CS*_CV);});return (!E(_Co))?new T2(1,new T(function(){var _CW=E(_CU),_CX=E(_CW.b),_CY=E(_CW.c),_CZ=E(_CW.a),_D0=E(_CN),_D1=E(_D0.c),_D2=E(_D0.b),_D3=E(_D0.a),_D4=E(_CH),_D5=E(_D4.c),_D6=E(_D4.b),_D7=E(_D4.a),_D8=_CX*_D1-_D2*_CY,_D9=_CY*_D3-_D1*_CZ,_Da=_CZ*_D2-_D3*_CX,_Db=B(_7n(_iT,_D9*_D5-_D6*_Da,_Da*_D7-_D5*_D8,_D8*_D6-_D7*_D9,_D3,_D2,_D1));return new T6(0,_AD,_AH,E(new T2(0,E(new T3(0,E(_D8),E(_D9),E(_Da))),E(_Db))),E(_Ar),_CT,_Ab);}),new T2(1,new T(function(){var _Dc=E(_CU),_Dd=E(_Dc.b),_De=E(_Dc.c),_Df=E(_Dc.a),_Dg=E(_CK),_Dh=E(_Dg.c),_Di=E(_Dg.b),_Dj=E(_Dg.a),_Dk=E(_CE),_Dl=E(_Dk.c),_Dm=E(_Dk.b),_Dn=E(_Dk.a),_Do=_Dd*_Dh-_Di*_De,_Dp=_De*_Dj-_Dh*_Df,_Dq=_Df*_Di-_Dj*_Dd,_Dr=B(_7n(_iT,_Dp*_Dl-_Dm*_Dq,_Dq*_Dn-_Dl*_Do,_Do*_Dm-_Dn*_Dp,_Dj,_Di,_Dh));return new T6(0,_AD,_AH,E(_Ar),E(new T2(0,E(new T3(0,E(_Do),E(_Dp),E(_Dq))),E(_Dr))),_CT,_Ab);}),new T(function(){return B(_Cp(_Cs));}))):new T2(1,new T(function(){var _Ds=E(_CU),_Dt=E(_Ds.b),_Du=E(_Ds.c),_Dv=E(_Ds.a),_Dw=E(_CN),_Dx=_Dw.a,_Dy=_Dw.b,_Dz=_Dw.c,_DA=B(_l5(_iT,_Dv,_Dt,_Du,_Dx,_Dy,_Dz)),_DB=E(_CH),_DC=E(_DB.c),_DD=E(_DB.b),_DE=E(_DB.a),_DF=B(_7n(_iT,_Dt*_DC-_DD*_Du,_Du*_DE-_DC*_Dv,_Dv*_DD-_DE*_Dt,_Dx,_Dy,_Dz)),_DG=E(_CK),_DH=_DG.a,_DI=_DG.b,_DJ=_DG.c,_DK=B(_l5(_iT,_Dv,_Dt,_Du,_DH,_DI,_DJ)),_DL=E(_CE),_DM=E(_DL.c),_DN=E(_DL.b),_DO=E(_DL.a),_DP=B(_7n(_iT,_Dt*_DM-_DN*_Du,_Du*_DO-_DM*_Dv,_Dv*_DN-_DO*_Dt,_DH,_DI,_DJ));return new T6(0,_AD,_AH,E(new T2(0,E(new T3(0,E(_DA.a),E(_DA.b),E(_DA.c))),E(_DF))),E(new T2(0,E(new T3(0,E(_DK.a),E(_DK.b),E(_DK.c))),E(_DP))),_CT,_Ac);}),new T(function(){return B(_Cp(_Cs));}));}};return B(_Cp(_AS));});return new T2(0,new T2(1,_Cn,_o),new T4(0,E(_AI),E(_AJ),_AK,_AL));}}}}}}}}}},_DQ=B(_AG(_AD,E(_AF.a),E(_AF.b),_AF.c,_AF.d,_));if(_AD!=_AB){var _DR=B(_AC(_AD+1|0,new T(function(){return E(E(_DQ).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Am(E(_DQ).a));}),new T(function(){return E(E(_DR).a);})),new T(function(){return E(E(_DR).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Am(E(_DQ).a));}),_o),new T(function(){return E(E(_DQ).b);}));}}else{if(_AD!=_AB){var _DS=B(_AC(_AD+1|0,_AE,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_DS).a);})),new T(function(){return E(E(_DS).b);}));}else{return new T2(0,new T2(1,_o,_o),_AE);}}},_DT=function(_DU,_DV,_DW,_DX,_DY,_){if(_DU<=_AB){var _DZ=function(_E0,_E1,_E2,_E3,_E4,_){if(_E1>_DU){return new F(function(){return die(_Aw);});}else{if(_DU>_E2){return new F(function(){return die(_Aw);});}else{if(_E1>_E0){return new F(function(){return _Aa(_);});}else{if(_E0>_E2){return new F(function(){return _Aa(_);});}else{var _E5=_DU-_E1|0;if(0>_E5){return new F(function(){return _xV(_E5,_E3);});}else{if(_E5>=_E3){return new F(function(){return _xV(_E5,_E3);});}else{var _E6=E(_E4[_E5]),_E7=_E0-_E1|0;if(0>_E7){return new F(function(){return _xV(_E7,_E3);});}else{if(_E7>=_E3){return new F(function(){return _xV(_E7,_E3);});}else{var _E8=E(_E4[_E7]),_E9=__app2(E(_Al),B(_jF(new T2(1,new T2(0,_r3,_E6.h),new T2(1,new T2(0,_r2,_E6.i),_o)))),B(_jF(new T2(1,new T2(0,_r3,_E8.h),new T2(1,new T2(0,_r2,_E8.i),_o))))),_Ea=__arr2lst(0,_E9),_Eb=B(_sd(_Ea,_));if(_E0!=_AB){var _Ec=B(_DZ(_E0+1|0,_E1,_E2,_E3,_E4,_)),_Ed=new T(function(){var _Ee=new T(function(){return _DU!=_E0;}),_Ef=function(_Eg){var _Eh=E(_Eg);if(!_Eh._){return __Z;}else{var _Ei=_Eh.b,_Ej=E(_Eh.a),_Ek=E(_Ej.b),_El=E(_Ej.a),_Em=E(_Ej.c),_En=_Em.a,_Eo=_Em.b,_Ep=E(_Ej.e),_Eq=E(_Ej.d),_Er=_Eq.a,_Es=_Eq.b,_Et=E(_Ej.f),_Eu=new T(function(){var _Ev=B(_ki(_iT,_Et.a,_Et.b,_Et.c)),_Ew=Math.sqrt(B(_A0(_iT,_Er,_Es,_Er,_Es)));return new T3(0,_Ew*E(_Ev.a),_Ew*E(_Ev.b),_Ew*E(_Ev.c));}),_Ex=new T(function(){var _Ey=B(_ki(_iT,_Ep.a,_Ep.b,_Ep.c)),_Ez=Math.sqrt(B(_A0(_iT,_En,_Eo,_En,_Eo)));return new T3(0,_Ez*E(_Ey.a),_Ez*E(_Ey.b),_Ez*E(_Ey.c));}),_EA=new T(function(){var _EB=B(A1(_At,_Ek)),_EC=B(_ki(_iT,_EB.a,_EB.b,_EB.c));return new T3(0,E(_EC.a),E(_EC.b),E(_EC.c));}),_ED=new T(function(){var _EE=B(A1(_At,_El)),_EF=B(_ki(_iT,_EE.a,_EE.b,_EE.c));return new T3(0,E(_EF.a),E(_EF.b),E(_EF.c));}),_EG=E(_Ek.a)+ -E(_El.a),_EH=E(_Ek.b)+ -E(_El.b),_EI=E(_Ek.c)+ -E(_El.c),_EJ=new T(function(){return Math.sqrt(B(_7n(_iT,_EG,_EH,_EI,_EG,_EH,_EI)));}),_EK=new T(function(){var _EL=1/E(_EJ);return new T3(0,_EG*_EL,_EH*_EL,_EI*_EL);});return (!E(_Ee))?new T2(1,new T(function(){var _EM=E(_EK),_EN=E(_EM.b),_EO=E(_EM.c),_EP=E(_EM.a),_EQ=E(_ED),_ER=E(_EQ.c),_ES=E(_EQ.b),_ET=E(_EQ.a),_EU=E(_Ex),_EV=E(_EU.c),_EW=E(_EU.b),_EX=E(_EU.a),_EY=_EN*_ER-_ES*_EO,_EZ=_EO*_ET-_ER*_EP,_F0=_EP*_ES-_ET*_EN,_F1=B(_7n(_iT,_EZ*_EV-_EW*_F0,_F0*_EX-_EV*_EY,_EY*_EW-_EX*_EZ,_ET,_ES,_ER));return new T6(0,_DU,_E0,E(new T2(0,E(new T3(0,E(_EY),E(_EZ),E(_F0))),E(_F1))),E(_Ar),_EJ,_Ab);}),new T2(1,new T(function(){var _F2=E(_EK),_F3=E(_F2.b),_F4=E(_F2.c),_F5=E(_F2.a),_F6=E(_EA),_F7=E(_F6.c),_F8=E(_F6.b),_F9=E(_F6.a),_Fa=E(_Eu),_Fb=E(_Fa.c),_Fc=E(_Fa.b),_Fd=E(_Fa.a),_Fe=_F3*_F7-_F8*_F4,_Ff=_F4*_F9-_F7*_F5,_Fg=_F5*_F8-_F9*_F3,_Fh=B(_7n(_iT,_Ff*_Fb-_Fc*_Fg,_Fg*_Fd-_Fb*_Fe,_Fe*_Fc-_Fd*_Ff,_F9,_F8,_F7));return new T6(0,_DU,_E0,E(_Ar),E(new T2(0,E(new T3(0,E(_Fe),E(_Ff),E(_Fg))),E(_Fh))),_EJ,_Ab);}),new T(function(){return B(_Ef(_Ei));}))):new T2(1,new T(function(){var _Fi=E(_EK),_Fj=E(_Fi.b),_Fk=E(_Fi.c),_Fl=E(_Fi.a),_Fm=E(_ED),_Fn=_Fm.a,_Fo=_Fm.b,_Fp=_Fm.c,_Fq=B(_l5(_iT,_Fl,_Fj,_Fk,_Fn,_Fo,_Fp)),_Fr=E(_Ex),_Fs=E(_Fr.c),_Ft=E(_Fr.b),_Fu=E(_Fr.a),_Fv=B(_7n(_iT,_Fj*_Fs-_Ft*_Fk,_Fk*_Fu-_Fs*_Fl,_Fl*_Ft-_Fu*_Fj,_Fn,_Fo,_Fp)),_Fw=E(_EA),_Fx=_Fw.a,_Fy=_Fw.b,_Fz=_Fw.c,_FA=B(_l5(_iT,_Fl,_Fj,_Fk,_Fx,_Fy,_Fz)),_FB=E(_Eu),_FC=E(_FB.c),_FD=E(_FB.b),_FE=E(_FB.a),_FF=B(_7n(_iT,_Fj*_FC-_FD*_Fk,_Fk*_FE-_FC*_Fl,_Fl*_FD-_FE*_Fj,_Fx,_Fy,_Fz));return new T6(0,_DU,_E0,E(new T2(0,E(new T3(0,E(_Fq.a),E(_Fq.b),E(_Fq.c))),E(_Fv))),E(new T2(0,E(new T3(0,E(_FA.a),E(_FA.b),E(_FA.c))),E(_FF))),_EJ,_Ac);}),new T(function(){return B(_Ef(_Ei));}));}};return B(_Ef(_Eb));});return new T2(0,new T2(1,_Ed,new T(function(){return E(E(_Ec).a);})),new T(function(){return E(E(_Ec).b);}));}else{var _FG=new T(function(){var _FH=new T(function(){return _DU!=_E0;}),_FI=function(_FJ){var _FK=E(_FJ);if(!_FK._){return __Z;}else{var _FL=_FK.b,_FM=E(_FK.a),_FN=E(_FM.b),_FO=E(_FM.a),_FP=E(_FM.c),_FQ=_FP.a,_FR=_FP.b,_FS=E(_FM.e),_FT=E(_FM.d),_FU=_FT.a,_FV=_FT.b,_FW=E(_FM.f),_FX=new T(function(){var _FY=B(_ki(_iT,_FW.a,_FW.b,_FW.c)),_FZ=Math.sqrt(B(_A0(_iT,_FU,_FV,_FU,_FV)));return new T3(0,_FZ*E(_FY.a),_FZ*E(_FY.b),_FZ*E(_FY.c));}),_G0=new T(function(){var _G1=B(_ki(_iT,_FS.a,_FS.b,_FS.c)),_G2=Math.sqrt(B(_A0(_iT,_FQ,_FR,_FQ,_FR)));return new T3(0,_G2*E(_G1.a),_G2*E(_G1.b),_G2*E(_G1.c));}),_G3=new T(function(){var _G4=B(A1(_At,_FN)),_G5=B(_ki(_iT,_G4.a,_G4.b,_G4.c));return new T3(0,E(_G5.a),E(_G5.b),E(_G5.c));}),_G6=new T(function(){var _G7=B(A1(_At,_FO)),_G8=B(_ki(_iT,_G7.a,_G7.b,_G7.c));return new T3(0,E(_G8.a),E(_G8.b),E(_G8.c));}),_G9=E(_FN.a)+ -E(_FO.a),_Ga=E(_FN.b)+ -E(_FO.b),_Gb=E(_FN.c)+ -E(_FO.c),_Gc=new T(function(){return Math.sqrt(B(_7n(_iT,_G9,_Ga,_Gb,_G9,_Ga,_Gb)));}),_Gd=new T(function(){var _Ge=1/E(_Gc);return new T3(0,_G9*_Ge,_Ga*_Ge,_Gb*_Ge);});return (!E(_FH))?new T2(1,new T(function(){var _Gf=E(_Gd),_Gg=E(_Gf.b),_Gh=E(_Gf.c),_Gi=E(_Gf.a),_Gj=E(_G6),_Gk=E(_Gj.c),_Gl=E(_Gj.b),_Gm=E(_Gj.a),_Gn=E(_G0),_Go=E(_Gn.c),_Gp=E(_Gn.b),_Gq=E(_Gn.a),_Gr=_Gg*_Gk-_Gl*_Gh,_Gs=_Gh*_Gm-_Gk*_Gi,_Gt=_Gi*_Gl-_Gm*_Gg,_Gu=B(_7n(_iT,_Gs*_Go-_Gp*_Gt,_Gt*_Gq-_Go*_Gr,_Gr*_Gp-_Gq*_Gs,_Gm,_Gl,_Gk));return new T6(0,_DU,_E0,E(new T2(0,E(new T3(0,E(_Gr),E(_Gs),E(_Gt))),E(_Gu))),E(_Ar),_Gc,_Ab);}),new T2(1,new T(function(){var _Gv=E(_Gd),_Gw=E(_Gv.b),_Gx=E(_Gv.c),_Gy=E(_Gv.a),_Gz=E(_G3),_GA=E(_Gz.c),_GB=E(_Gz.b),_GC=E(_Gz.a),_GD=E(_FX),_GE=E(_GD.c),_GF=E(_GD.b),_GG=E(_GD.a),_GH=_Gw*_GA-_GB*_Gx,_GI=_Gx*_GC-_GA*_Gy,_GJ=_Gy*_GB-_GC*_Gw,_GK=B(_7n(_iT,_GI*_GE-_GF*_GJ,_GJ*_GG-_GE*_GH,_GH*_GF-_GG*_GI,_GC,_GB,_GA));return new T6(0,_DU,_E0,E(_Ar),E(new T2(0,E(new T3(0,E(_GH),E(_GI),E(_GJ))),E(_GK))),_Gc,_Ab);}),new T(function(){return B(_FI(_FL));}))):new T2(1,new T(function(){var _GL=E(_Gd),_GM=E(_GL.b),_GN=E(_GL.c),_GO=E(_GL.a),_GP=E(_G6),_GQ=_GP.a,_GR=_GP.b,_GS=_GP.c,_GT=B(_l5(_iT,_GO,_GM,_GN,_GQ,_GR,_GS)),_GU=E(_G0),_GV=E(_GU.c),_GW=E(_GU.b),_GX=E(_GU.a),_GY=B(_7n(_iT,_GM*_GV-_GW*_GN,_GN*_GX-_GV*_GO,_GO*_GW-_GX*_GM,_GQ,_GR,_GS)),_GZ=E(_G3),_H0=_GZ.a,_H1=_GZ.b,_H2=_GZ.c,_H3=B(_l5(_iT,_GO,_GM,_GN,_H0,_H1,_H2)),_H4=E(_FX),_H5=E(_H4.c),_H6=E(_H4.b),_H7=E(_H4.a),_H8=B(_7n(_iT,_GM*_H5-_H6*_GN,_GN*_H7-_H5*_GO,_GO*_H6-_H7*_GM,_H0,_H1,_H2));return new T6(0,_DU,_E0,E(new T2(0,E(new T3(0,E(_GT.a),E(_GT.b),E(_GT.c))),E(_GY))),E(new T2(0,E(new T3(0,E(_H3.a),E(_H3.b),E(_H3.c))),E(_H8))),_Gc,_Ac);}),new T(function(){return B(_FI(_FL));}));}};return B(_FI(_Eb));});return new T2(0,new T2(1,_FG,_o),new T4(0,E(_E1),E(_E2),_E3,_E4));}}}}}}}}}},_H9=B(_DZ(_DU,_DV,_DW,_DX,_DY,_));if(_DU!=_AB){var _Ha=B(_AC(_DU+1|0,new T(function(){return E(E(_H9).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Am(E(_H9).a));}),new T(function(){return E(E(_Ha).a);})),new T(function(){return E(E(_Ha).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Am(E(_H9).a));}),_o),new T(function(){return E(E(_H9).b);}));}}else{if(_DU!=_AB){var _Hb=B(_DT(_DU+1|0,_DV,_DW,_DX,_DY,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Hb).a);})),new T(function(){return E(E(_Hb).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_DV),E(_DW),_DX,_DY));}}},_Hc=B(_DT(_AA,_AA,_AB,_Az.c,_Az.d,_));return new F(function(){return _zS(_,_Hc);});}else{return new F(function(){return _zS(_,new T2(0,_o,_Az));});}},_Hd=new T(function(){return eval("passObject");}),_He=new T(function(){return eval("__strict(refresh)");}),_Hf=function(_Hg,_){var _Hh=__app0(E(_He)),_Hi=__app0(E(_r7)),_Hj=E(_Hg),_Hk=_Hj.c,_Hl=_Hj.d,_Hm=E(_Hj.a),_Hn=E(_Hj.b);if(_Hm<=_Hn){if(_Hm>_Hn){return E(_r5);}else{if(0>=_Hk){return new F(function(){return _ri(_Hk,0);});}else{var _Ho=E(_Hl[0]),_Hp=E(_Hd),_Hq=__app2(_Hp,_Hm,B(_jF(new T2(1,new T2(0,_r3,_Ho.h),new T2(1,new T2(0,_r2,_Ho.i),_o)))));if(_Hm!=_Hn){var _Hr=function(_Hs,_){if(_Hm>_Hs){return E(_r5);}else{if(_Hs>_Hn){return E(_r5);}else{var _Ht=_Hs-_Hm|0;if(0>_Ht){return new F(function(){return _ri(_Hk,_Ht);});}else{if(_Ht>=_Hk){return new F(function(){return _ri(_Hk,_Ht);});}else{var _Hu=E(_Hl[_Ht]),_Hv=__app2(_Hp,_Hs,B(_jF(new T2(1,new T2(0,_r3,_Hu.h),new T2(1,new T2(0,_r2,_Hu.i),_o)))));if(_Hs!=_Hn){var _Hw=B(_Hr(_Hs+1|0,_));return new T2(1,_jE,_Hw);}else{return _rn;}}}}}},_Hx=B(_Hr(_Hm+1|0,_)),_Hy=__app0(E(_r6)),_Hz=B(_Ax(_Hj,_));return new T(function(){return E(E(_Hz).b);});}else{var _HA=__app0(E(_r6)),_HB=B(_Ax(_Hj,_));return new T(function(){return E(E(_HB).b);});}}}}else{var _HC=__app0(E(_r6)),_HD=B(_Ax(_Hj,_));return new T(function(){return E(E(_HD).b);});}},_HE=function(_HF,_){while(1){var _HG=E(_HF);if(!_HG._){return _jE;}else{var _HH=_HG.b,_HI=E(_HG.a);switch(_HI._){case 0:var _HJ=B(A1(_HI.a,_));_HF=B(_f(_HH,new T2(1,_HJ,_o)));continue;case 1:_HF=B(_f(_HH,_HI.a));continue;default:_HF=_HH;continue;}}}},_HK=function(_HL,_HM,_){var _HN=E(_HL);switch(_HN._){case 0:var _HO=B(A1(_HN.a,_));return new F(function(){return _HE(B(_f(_HM,new T2(1,_HO,_o))),_);});break;case 1:return new F(function(){return _HE(B(_f(_HM,_HN.a)),_);});break;default:return new F(function(){return _HE(_HM,_);});}},_HP=new T0(2),_HQ=function(_HR){return new T0(2);},_HS=function(_HT,_HU,_HV){return function(_){var _HW=E(_HT),_HX=rMV(_HW),_HY=E(_HX);if(!_HY._){var _HZ=new T(function(){var _I0=new T(function(){return B(A1(_HV,_jE));});return B(_f(_HY.b,new T2(1,new T2(0,_HU,function(_I1){return E(_I0);}),_o)));}),_=wMV(_HW,new T2(0,_HY.a,_HZ));return _HP;}else{var _I2=E(_HY.a);if(!_I2._){var _=wMV(_HW,new T2(0,_HU,_o));return new T(function(){return B(A1(_HV,_jE));});}else{var _=wMV(_HW,new T1(1,_I2.b));return new T1(1,new T2(1,new T(function(){return B(A1(_HV,_jE));}),new T2(1,new T(function(){return B(A2(_I2.a,_HU,_HQ));}),_o)));}}};},_I3=new T(function(){return E(_p4);}),_I4=new T(function(){return eval("window.requestAnimationFrame");}),_I5=new T1(1,_o),_I6=function(_I7,_I8){return function(_){var _I9=E(_I7),_Ia=rMV(_I9),_Ib=E(_Ia);if(!_Ib._){var _Ic=_Ib.a,_Id=E(_Ib.b);if(!_Id._){var _=wMV(_I9,_I5);return new T(function(){return B(A1(_I8,_Ic));});}else{var _Ie=E(_Id.a),_=wMV(_I9,new T2(0,_Ie.a,_Id.b));return new T1(1,new T2(1,new T(function(){return B(A1(_I8,_Ic));}),new T2(1,new T(function(){return B(A1(_Ie.b,_HQ));}),_o)));}}else{var _If=new T(function(){var _Ig=function(_Ih){var _Ii=new T(function(){return B(A1(_I8,_Ih));});return function(_Ij){return E(_Ii);};};return B(_f(_Ib.a,new T2(1,_Ig,_o)));}),_=wMV(_I9,new T1(1,_If));return _HP;}};},_Ik=function(_Il,_Im){return new T1(0,B(_I6(_Il,_Im)));},_In=function(_Io,_Ip){var _Iq=new T(function(){return new T1(0,B(_HS(_Io,_jE,_HQ)));});return function(_){var _Ir=__createJSFunc(2,function(_Is,_){var _It=B(_HK(_Iq,_o,_));return _I3;}),_Iu=__app1(E(_I4),_Ir);return new T(function(){return B(_Ik(_Io,_Ip));});};},_Iv=new T1(1,_o),_Iw=function(_Ix,_Iy,_){var _Iz=function(_){var _IA=nMV(_Ix),_IB=_IA;return new T(function(){var _IC=new T(function(){return B(_ID(_));}),_IE=function(_){var _IF=rMV(_IB),_IG=B(A2(_Iy,_IF,_)),_=wMV(_IB,_IG),_IH=function(_){var _II=nMV(_Iv);return new T(function(){return new T1(0,B(_In(_II,function(_IJ){return E(_IC);})));});};return new T1(0,_IH);},_IK=new T(function(){return new T1(0,_IE);}),_ID=function(_IL){return E(_IK);};return B(_ID(_));});};return new F(function(){return _HK(new T1(0,_Iz),_o,_);});},_IM=function(_){var _IN=__app2(E(_0),E(_7W),E(_hg));return new F(function(){return _Iw(_r1,_Hf,_);});},_IO=function(_){return new F(function(){return _IM(_);});};
var hasteMain = function() {B(A(_IO, [0]));};window.onload = hasteMain;