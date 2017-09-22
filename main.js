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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==(-2147483648)){_3l=new T1(1,I_fromInt(-2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0,-1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==(-2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S(-1021,53,_6k,_6l);});}else{return  -B(_5S(-1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=function(_7h){return E(E(_7h).a);},_7i=function(_7j){return E(E(_7j).a);},_7k=function(_7l){return E(E(_7l).c);},_7m=function(_7n){return E(E(_7n).b);},_7o=function(_7p){return E(E(_7p).c);},_7q=function(_7r){return E(E(_7r).e);},_7s=function(_7t,_7u,_7v,_7w){var _7x=B(_7i(B(_7g(_7t)))),_7y=new T(function(){var _7z=new T(function(){return B(A3(_6I,_7x,new T(function(){return B(A3(_7k,_7x,_7u,_7u));}),new T(function(){return B(A3(_7k,_7x,_7w,_7w));})));});return B(A2(_7q,_7t,_7z));});return new F(function(){return A3(_7m,_7x,_7y,new T(function(){return B(A2(_7o,_7t,_7v));}));});},_7A=new T(function(){return B(unCStr("x"));}),_7B=new T1(0,_7A),_7C=new T(function(){return B(unCStr("y"));}),_7D=new T1(0,_7C),_7E=new T(function(){return B(unCStr("z"));}),_7F=new T1(0,_7E),_7G=new T(function(){return B(_7s(_7f,_7B,_7D,_7F));}),_7H=function(_7I){return E(_7I);},_7J=new T(function(){return toJSStr(B(_5(_p,_7H,_7G)));}),_7K=function(_7L,_7M,_7N){var _7O=new T(function(){return B(_1(_7L));}),_7P=new T(function(){return B(_3(_7L));}),_7Q=function(_7R){var _7S=E(_7R);if(!_7S._){return E(_7P);}else{return new F(function(){return A2(_7O,new T(function(){return B(_5(_7L,_7M,_7S.a));}),new T(function(){return B(_7Q(_7S.b));}));});}};return new F(function(){return _7Q(_7N);});},_7T=new T3(0,E(_7B),E(_7D),E(_7F)),_7U=new T(function(){return B(unCStr("(/=) is not defined"));}),_7V=new T(function(){return B(err(_7U));}),_7W=new T(function(){return B(unCStr("(==) is not defined"));}),_7X=new T(function(){return B(err(_7W));}),_7Y=new T2(0,_7X,_7V),_7Z=new T(function(){return B(unCStr("(<) is not defined"));}),_80=new T(function(){return B(err(_7Z));}),_81=new T(function(){return B(unCStr("(<=) is not defined"));}),_82=new T(function(){return B(err(_81));}),_83=new T(function(){return B(unCStr("(>) is not defined"));}),_84=new T(function(){return B(err(_83));}),_85=new T(function(){return B(unCStr("(>=) is not defined"));}),_86=new T(function(){return B(err(_85));}),_87=new T(function(){return B(unCStr("compare is not defined"));}),_88=new T(function(){return B(err(_87));}),_89=new T(function(){return B(unCStr("max("));}),_8a=new T1(0,_89),_8b=function(_8c,_8d){return new T1(1,new T2(1,_8a,new T2(1,_8c,new T2(1,_r,new T2(1,_8d,_w)))));},_8e=new T(function(){return B(unCStr("min("));}),_8f=new T1(0,_8e),_8g=function(_8h,_8i){return new T1(1,new T2(1,_8f,new T2(1,_8h,new T2(1,_r,new T2(1,_8i,_w)))));},_8j={_:0,a:_7Y,b:_88,c:_80,d:_82,e:_84,f:_86,g:_8b,h:_8g},_8k=new T2(0,_7f,_8j),_8l=function(_8m,_8n){var _8o=E(_8m);return E(_8n);},_8p=function(_8q,_8r){var _8s=E(_8r);return E(_8q);},_8t=function(_8u,_8v){var _8w=E(_8u),_8x=E(_8v);return new T3(0,E(B(A1(_8w.a,_8x.a))),E(B(A1(_8w.b,_8x.b))),E(B(A1(_8w.c,_8x.c))));},_8y=function(_8z,_8A,_8B){return new T3(0,E(_8z),E(_8A),E(_8B));},_8C=function(_8D){return new F(function(){return _8y(_8D,_8D,_8D);});},_8E=function(_8F,_8G){var _8H=E(_8G),_8I=E(_8F);return new T3(0,E(_8I),E(_8I),E(_8I));},_8J=function(_8K,_8L){var _8M=E(_8L);return new T3(0,E(B(A1(_8K,_8M.a))),E(B(A1(_8K,_8M.b))),E(B(A1(_8K,_8M.c))));},_8N=new T2(0,_8J,_8E),_8O=new T5(0,_8N,_8C,_8t,_8l,_8p),_8P=new T1(0,0),_8Q=new T1(0,1),_8R=function(_8S){return E(E(_8S).g);},_8T=function(_8U){var _8V=B(A2(_8R,_8U,_8Q)),_8W=B(A2(_8R,_8U,_8P));return new T3(0,E(new T3(0,E(_8V),E(_8W),E(_8W))),E(new T3(0,E(_8W),E(_8V),E(_8W))),E(new T3(0,E(_8W),E(_8W),E(_8V))));},_8X=function(_8Y){return E(E(_8Y).a);},_8Z=function(_90){return E(E(_90).f);},_91=function(_92){return E(E(_92).b);},_93=function(_94){return E(E(_94).c);},_95=function(_96){return E(E(_96).a);},_97=function(_98){return E(E(_98).d);},_99=function(_9a,_9b,_9c,_9d,_9e){var _9f=new T(function(){return E(E(E(_9a).c).a);}),_9g=new T(function(){var _9h=E(_9a).a,_9i=new T(function(){var _9j=new T(function(){return B(_7g(_9f));}),_9k=new T(function(){return B(_7i(_9j));}),_9l=new T(function(){return B(A2(_97,_9f,_9b));}),_9m=new T(function(){return B(A3(_8Z,_9f,_9b,_9d));}),_9n=function(_9o,_9p){var _9q=new T(function(){var _9r=new T(function(){return B(A3(_91,_9j,new T(function(){return B(A3(_7k,_9k,_9d,_9o));}),_9b));});return B(A3(_6I,_9k,_9r,new T(function(){return B(A3(_7k,_9k,_9p,_9l));})));});return new F(function(){return A3(_7k,_9k,_9m,_9q);});};return B(A3(_95,B(_8X(_9h)),_9n,_9c));});return B(A3(_93,_9h,_9i,_9e));});return new T2(0,new T(function(){return B(A3(_8Z,_9f,_9b,_9d));}),_9g);},_9s=function(_9t,_9u,_9v,_9w){var _9x=E(_9v),_9y=E(_9w),_9z=B(_99(_9u,_9x.a,_9x.b,_9y.a,_9y.b));return new T2(0,_9z.a,_9z.b);},_9A=new T1(0,1),_9B=function(_9C){return E(E(_9C).l);},_9D=function(_9E,_9F,_9G){var _9H=new T(function(){return E(E(E(_9E).c).a);}),_9I=new T(function(){var _9J=new T(function(){return B(_7g(_9H));}),_9K=new T(function(){var _9L=B(_7i(_9J)),_9M=new T(function(){var _9N=new T(function(){return B(A3(_7m,_9L,new T(function(){return B(A2(_8R,_9L,_9A));}),new T(function(){return B(A3(_7k,_9L,_9F,_9F));})));});return B(A2(_7q,_9H,_9N));});return B(A2(_6K,_9L,_9M));});return B(A3(_95,B(_8X(E(_9E).a)),function(_9O){return new F(function(){return A3(_91,_9J,_9O,_9K);});},_9G));});return new T2(0,new T(function(){return B(A2(_9B,_9H,_9F));}),_9I);},_9P=function(_9Q,_9R,_9S){var _9T=E(_9S),_9U=B(_9D(_9R,_9T.a,_9T.b));return new T2(0,_9U.a,_9U.b);},_9V=function(_9W){return E(E(_9W).r);},_9X=function(_9Y,_9Z,_a0){var _a1=new T(function(){return E(E(E(_9Y).c).a);}),_a2=new T(function(){var _a3=new T(function(){return B(_7g(_a1));}),_a4=new T(function(){var _a5=new T(function(){var _a6=B(_7i(_a3));return B(A3(_7m,_a6,new T(function(){return B(A3(_7k,_a6,_9Z,_9Z));}),new T(function(){return B(A2(_8R,_a6,_9A));})));});return B(A2(_7q,_a1,_a5));});return B(A3(_95,B(_8X(E(_9Y).a)),function(_a7){return new F(function(){return A3(_91,_a3,_a7,_a4);});},_a0));});return new T2(0,new T(function(){return B(A2(_9V,_a1,_9Z));}),_a2);},_a8=function(_a9,_aa,_ab){var _ac=E(_ab),_ad=B(_9X(_aa,_ac.a,_ac.b));return new T2(0,_ad.a,_ad.b);},_ae=function(_af){return E(E(_af).k);},_ag=function(_ah,_ai,_aj){var _ak=new T(function(){return E(E(E(_ah).c).a);}),_al=new T(function(){var _am=new T(function(){return B(_7g(_ak));}),_an=new T(function(){var _ao=new T(function(){var _ap=B(_7i(_am));return B(A3(_7m,_ap,new T(function(){return B(A2(_8R,_ap,_9A));}),new T(function(){return B(A3(_7k,_ap,_ai,_ai));})));});return B(A2(_7q,_ak,_ao));});return B(A3(_95,B(_8X(E(_ah).a)),function(_aq){return new F(function(){return A3(_91,_am,_aq,_an);});},_aj));});return new T2(0,new T(function(){return B(A2(_ae,_ak,_ai));}),_al);},_ar=function(_as,_at,_au){var _av=E(_au),_aw=B(_ag(_at,_av.a,_av.b));return new T2(0,_aw.a,_aw.b);},_ax=function(_ay){return E(E(_ay).q);},_az=function(_aA,_aB,_aC){var _aD=new T(function(){return E(E(E(_aA).c).a);}),_aE=new T(function(){var _aF=new T(function(){return B(_7g(_aD));}),_aG=new T(function(){var _aH=new T(function(){var _aI=B(_7i(_aF));return B(A3(_6I,_aI,new T(function(){return B(A3(_7k,_aI,_aB,_aB));}),new T(function(){return B(A2(_8R,_aI,_9A));})));});return B(A2(_7q,_aD,_aH));});return B(A3(_95,B(_8X(E(_aA).a)),function(_aJ){return new F(function(){return A3(_91,_aF,_aJ,_aG);});},_aC));});return new T2(0,new T(function(){return B(A2(_ax,_aD,_aB));}),_aE);},_aK=function(_aL,_aM,_aN){var _aO=E(_aN),_aP=B(_az(_aM,_aO.a,_aO.b));return new T2(0,_aP.a,_aP.b);},_aQ=function(_aR){return E(E(_aR).m);},_aS=function(_aT,_aU,_aV){var _aW=new T(function(){return E(E(E(_aT).c).a);}),_aX=new T(function(){var _aY=new T(function(){return B(_7g(_aW));}),_aZ=new T(function(){var _b0=B(_7i(_aY));return B(A3(_6I,_b0,new T(function(){return B(A2(_8R,_b0,_9A));}),new T(function(){return B(A3(_7k,_b0,_aU,_aU));})));});return B(A3(_95,B(_8X(E(_aT).a)),function(_b1){return new F(function(){return A3(_91,_aY,_b1,_aZ);});},_aV));});return new T2(0,new T(function(){return B(A2(_aQ,_aW,_aU));}),_aX);},_b2=function(_b3,_b4,_b5){var _b6=E(_b5),_b7=B(_aS(_b4,_b6.a,_b6.b));return new T2(0,_b7.a,_b7.b);},_b8=function(_b9){return E(E(_b9).s);},_ba=function(_bb,_bc,_bd){var _be=new T(function(){return E(E(E(_bb).c).a);}),_bf=new T(function(){var _bg=new T(function(){return B(_7g(_be));}),_bh=new T(function(){var _bi=B(_7i(_bg));return B(A3(_7m,_bi,new T(function(){return B(A2(_8R,_bi,_9A));}),new T(function(){return B(A3(_7k,_bi,_bc,_bc));})));});return B(A3(_95,B(_8X(E(_bb).a)),function(_bj){return new F(function(){return A3(_91,_bg,_bj,_bh);});},_bd));});return new T2(0,new T(function(){return B(A2(_b8,_be,_bc));}),_bf);},_bk=function(_bl,_bm,_bn){var _bo=E(_bn),_bp=B(_ba(_bm,_bo.a,_bo.b));return new T2(0,_bp.a,_bp.b);},_bq=function(_br){return E(E(_br).i);},_bs=function(_bt){return E(E(_bt).h);},_bu=function(_bv,_bw,_bx){var _by=new T(function(){return E(E(E(_bv).c).a);}),_bz=new T(function(){var _bA=new T(function(){return B(_7i(new T(function(){return B(_7g(_by));})));}),_bB=new T(function(){return B(A2(_6K,_bA,new T(function(){return B(A2(_bs,_by,_bw));})));});return B(A3(_95,B(_8X(E(_bv).a)),function(_bC){return new F(function(){return A3(_7k,_bA,_bC,_bB);});},_bx));});return new T2(0,new T(function(){return B(A2(_bq,_by,_bw));}),_bz);},_bD=function(_bE,_bF,_bG){var _bH=E(_bG),_bI=B(_bu(_bF,_bH.a,_bH.b));return new T2(0,_bI.a,_bI.b);},_bJ=function(_bK){return E(E(_bK).o);},_bL=function(_bM){return E(E(_bM).n);},_bN=function(_bO,_bP,_bQ){var _bR=new T(function(){return E(E(E(_bO).c).a);}),_bS=new T(function(){var _bT=new T(function(){return B(_7i(new T(function(){return B(_7g(_bR));})));}),_bU=new T(function(){return B(A2(_bL,_bR,_bP));});return B(A3(_95,B(_8X(E(_bO).a)),function(_bV){return new F(function(){return A3(_7k,_bT,_bV,_bU);});},_bQ));});return new T2(0,new T(function(){return B(A2(_bJ,_bR,_bP));}),_bS);},_bW=function(_bX,_bY,_bZ){var _c0=E(_bZ),_c1=B(_bN(_bY,_c0.a,_c0.b));return new T2(0,_c1.a,_c1.b);},_c2=function(_c3,_c4,_c5){var _c6=new T(function(){return E(E(E(_c3).c).a);}),_c7=new T(function(){var _c8=new T(function(){return B(_7i(new T(function(){return B(_7g(_c6));})));}),_c9=new T(function(){return B(A2(_7o,_c6,_c4));});return B(A3(_95,B(_8X(E(_c3).a)),function(_ca){return new F(function(){return A3(_7k,_c8,_ca,_c9);});},_c5));});return new T2(0,new T(function(){return B(A2(_7o,_c6,_c4));}),_c7);},_cb=function(_cc,_cd,_ce){var _cf=E(_ce),_cg=B(_c2(_cd,_cf.a,_cf.b));return new T2(0,_cg.a,_cg.b);},_ch=function(_ci,_cj,_ck){var _cl=new T(function(){return E(E(E(_ci).c).a);}),_cm=new T(function(){var _cn=new T(function(){return B(_7g(_cl));}),_co=new T(function(){return B(_7i(_cn));}),_cp=new T(function(){return B(A3(_91,_cn,new T(function(){return B(A2(_8R,_co,_9A));}),_cj));});return B(A3(_95,B(_8X(E(_ci).a)),function(_cq){return new F(function(){return A3(_7k,_co,_cq,_cp);});},_ck));});return new T2(0,new T(function(){return B(A2(_97,_cl,_cj));}),_cm);},_cr=function(_cs,_ct,_cu){var _cv=E(_cu),_cw=B(_ch(_ct,_cv.a,_cv.b));return new T2(0,_cw.a,_cw.b);},_cx=function(_cy,_cz,_cA,_cB){var _cC=new T(function(){return E(E(_cz).c);}),_cD=new T3(0,new T(function(){return E(E(_cz).a);}),new T(function(){return E(E(_cz).b);}),new T2(0,new T(function(){return E(E(_cC).a);}),new T(function(){return E(E(_cC).b);})));return new F(function(){return A3(_91,_cy,new T(function(){var _cE=E(_cB),_cF=B(_ch(_cD,_cE.a,_cE.b));return new T2(0,_cF.a,_cF.b);}),new T(function(){var _cG=E(_cA),_cH=B(_ch(_cD,_cG.a,_cG.b));return new T2(0,_cH.a,_cH.b);}));});},_cI=new T1(0,0),_cJ=function(_cK){return E(E(_cK).b);},_cL=function(_cM){return E(E(_cM).b);},_cN=function(_cO){var _cP=new T(function(){return E(E(E(_cO).c).a);}),_cQ=new T(function(){return B(A2(_cL,E(_cO).a,new T(function(){return B(A2(_8R,B(_7i(B(_7g(_cP)))),_cI));})));});return new T2(0,new T(function(){return B(_cJ(_cP));}),_cQ);},_cR=function(_cS,_cT){var _cU=B(_cN(_cT));return new T2(0,_cU.a,_cU.b);},_cV=function(_cW,_cX,_cY){var _cZ=new T(function(){return E(E(E(_cW).c).a);}),_d0=new T(function(){var _d1=new T(function(){return B(_7i(new T(function(){return B(_7g(_cZ));})));}),_d2=new T(function(){return B(A2(_bq,_cZ,_cX));});return B(A3(_95,B(_8X(E(_cW).a)),function(_d3){return new F(function(){return A3(_7k,_d1,_d3,_d2);});},_cY));});return new T2(0,new T(function(){return B(A2(_bs,_cZ,_cX));}),_d0);},_d4=function(_d5,_d6,_d7){var _d8=E(_d7),_d9=B(_cV(_d6,_d8.a,_d8.b));return new T2(0,_d9.a,_d9.b);},_da=function(_db,_dc,_dd){var _de=new T(function(){return E(E(E(_db).c).a);}),_df=new T(function(){var _dg=new T(function(){return B(_7i(new T(function(){return B(_7g(_de));})));}),_dh=new T(function(){return B(A2(_bJ,_de,_dc));});return B(A3(_95,B(_8X(E(_db).a)),function(_di){return new F(function(){return A3(_7k,_dg,_di,_dh);});},_dd));});return new T2(0,new T(function(){return B(A2(_bL,_de,_dc));}),_df);},_dj=function(_dk,_dl,_dm){var _dn=E(_dm),_do=B(_da(_dl,_dn.a,_dn.b));return new T2(0,_do.a,_do.b);},_dp=new T1(0,2),_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_7g(_du));}),_dx=new T(function(){return B(_7i(_dw));}),_dy=new T(function(){var _dz=new T(function(){return B(A3(_91,_dw,new T(function(){return B(A2(_8R,_dx,_9A));}),new T(function(){return B(A2(_8R,_dx,_dp));})));});return B(A3(_91,_dw,_dz,new T(function(){return B(A2(_7q,_du,_ds));})));});return B(A3(_95,B(_8X(E(_dr).a)),function(_dA){return new F(function(){return A3(_7k,_dx,_dA,_dy);});},_dt));});return new T2(0,new T(function(){return B(A2(_7q,_du,_ds));}),_dv);},_dB=function(_dC,_dD,_dE){var _dF=E(_dE),_dG=B(_dq(_dD,_dF.a,_dF.b));return new T2(0,_dG.a,_dG.b);},_dH=function(_dI){return E(E(_dI).j);},_dJ=function(_dK,_dL,_dM){var _dN=new T(function(){return E(E(E(_dK).c).a);}),_dO=new T(function(){var _dP=new T(function(){return B(_7g(_dN));}),_dQ=new T(function(){var _dR=new T(function(){return B(A2(_bq,_dN,_dL));});return B(A3(_7k,B(_7i(_dP)),_dR,_dR));});return B(A3(_95,B(_8X(E(_dK).a)),function(_dS){return new F(function(){return A3(_91,_dP,_dS,_dQ);});},_dM));});return new T2(0,new T(function(){return B(A2(_dH,_dN,_dL));}),_dO);},_dT=function(_dU,_dV,_dW){var _dX=E(_dW),_dY=B(_dJ(_dV,_dX.a,_dX.b));return new T2(0,_dY.a,_dY.b);},_dZ=function(_e0){return E(E(_e0).p);},_e1=function(_e2,_e3,_e4){var _e5=new T(function(){return E(E(E(_e2).c).a);}),_e6=new T(function(){var _e7=new T(function(){return B(_7g(_e5));}),_e8=new T(function(){var _e9=new T(function(){return B(A2(_bJ,_e5,_e3));});return B(A3(_7k,B(_7i(_e7)),_e9,_e9));});return B(A3(_95,B(_8X(E(_e2).a)),function(_ea){return new F(function(){return A3(_91,_e7,_ea,_e8);});},_e4));});return new T2(0,new T(function(){return B(A2(_dZ,_e5,_e3));}),_e6);},_eb=function(_ec,_ed,_ee){var _ef=E(_ee),_eg=B(_e1(_ed,_ef.a,_ef.b));return new T2(0,_eg.a,_eg.b);},_eh=function(_ei,_ej){return {_:0,a:_ei,b:new T(function(){return B(_cR(_ei,_ej));}),c:function(_ek){return new F(function(){return _cb(_ei,_ej,_ek);});},d:function(_ek){return new F(function(){return _cr(_ei,_ej,_ek);});},e:function(_ek){return new F(function(){return _dB(_ei,_ej,_ek);});},f:function(_el,_ek){return new F(function(){return _9s(_ei,_ej,_el,_ek);});},g:function(_el,_ek){return new F(function(){return _cx(_ei,_ej,_el,_ek);});},h:function(_ek){return new F(function(){return _d4(_ei,_ej,_ek);});},i:function(_ek){return new F(function(){return _bD(_ei,_ej,_ek);});},j:function(_ek){return new F(function(){return _dT(_ei,_ej,_ek);});},k:function(_ek){return new F(function(){return _ar(_ei,_ej,_ek);});},l:function(_ek){return new F(function(){return _9P(_ei,_ej,_ek);});},m:function(_ek){return new F(function(){return _b2(_ei,_ej,_ek);});},n:function(_ek){return new F(function(){return _dj(_ei,_ej,_ek);});},o:function(_ek){return new F(function(){return _bW(_ei,_ej,_ek);});},p:function(_ek){return new F(function(){return _eb(_ei,_ej,_ek);});},q:function(_ek){return new F(function(){return _aK(_ei,_ej,_ek);});},r:function(_ek){return new F(function(){return _a8(_ei,_ej,_ek);});},s:function(_ek){return new F(function(){return _bk(_ei,_ej,_ek);});}};},_em=function(_en,_eo,_ep,_eq,_er){var _es=new T(function(){return B(_7g(new T(function(){return E(E(E(_en).c).a);})));}),_et=new T(function(){var _eu=E(_en).a,_ev=new T(function(){var _ew=new T(function(){return B(_7i(_es));}),_ex=new T(function(){return B(A3(_7k,_ew,_eq,_eq));}),_ey=function(_ez,_eA){var _eB=new T(function(){return B(A3(_7m,_ew,new T(function(){return B(A3(_7k,_ew,_ez,_eq));}),new T(function(){return B(A3(_7k,_ew,_eo,_eA));})));});return new F(function(){return A3(_91,_es,_eB,_ex);});};return B(A3(_95,B(_8X(_eu)),_ey,_ep));});return B(A3(_93,_eu,_ev,_er));});return new T2(0,new T(function(){return B(A3(_91,_es,_eo,_eq));}),_et);},_eC=function(_eD,_eE,_eF,_eG){var _eH=E(_eF),_eI=E(_eG),_eJ=B(_em(_eE,_eH.a,_eH.b,_eI.a,_eI.b));return new T2(0,_eJ.a,_eJ.b);},_eK=function(_eL){return E(E(_eL).d);},_eM=function(_eN,_eO){var _eP=new T(function(){return B(_7g(new T(function(){return E(E(E(_eN).c).a);})));}),_eQ=new T(function(){return B(A2(_cL,E(_eN).a,new T(function(){return B(A2(_8R,B(_7i(_eP)),_cI));})));});return new T2(0,new T(function(){return B(A2(_eK,_eP,_eO));}),_eQ);},_eR=function(_eS,_eT,_eU){var _eV=B(_eM(_eT,_eU));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX,_eY,_eZ){var _f0=new T(function(){return B(_7g(new T(function(){return E(E(E(_eX).c).a);})));}),_f1=new T(function(){return B(_7i(_f0));}),_f2=new T(function(){var _f3=new T(function(){var _f4=new T(function(){return B(A3(_91,_f0,new T(function(){return B(A2(_8R,_f1,_9A));}),new T(function(){return B(A3(_7k,_f1,_eY,_eY));})));});return B(A2(_6K,_f1,_f4));});return B(A3(_95,B(_8X(E(_eX).a)),function(_f5){return new F(function(){return A3(_7k,_f1,_f5,_f3);});},_eZ));}),_f6=new T(function(){return B(A3(_91,_f0,new T(function(){return B(A2(_8R,_f1,_9A));}),_eY));});return new T2(0,_f6,_f2);},_f7=function(_f8,_f9,_fa){var _fb=E(_fa),_fc=B(_eW(_f9,_fb.a,_fb.b));return new T2(0,_fc.a,_fc.b);},_fd=function(_fe,_ff){return new T4(0,_fe,function(_el,_ek){return new F(function(){return _eC(_fe,_ff,_el,_ek);});},function(_ek){return new F(function(){return _f7(_fe,_ff,_ek);});},function(_ek){return new F(function(){return _eR(_fe,_ff,_ek);});});},_fg=function(_fh,_fi,_fj,_fk,_fl){var _fm=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fh).c).a);})));})));}),_fn=new T(function(){var _fo=E(_fh).a,_fp=new T(function(){var _fq=function(_fr,_fs){return new F(function(){return A3(_6I,_fm,new T(function(){return B(A3(_7k,_fm,_fi,_fs));}),new T(function(){return B(A3(_7k,_fm,_fr,_fk));}));});};return B(A3(_95,B(_8X(_fo)),_fq,_fj));});return B(A3(_93,_fo,_fp,_fl));});return new T2(0,new T(function(){return B(A3(_7k,_fm,_fi,_fk));}),_fn);},_ft=function(_fu,_fv,_fw){var _fx=E(_fv),_fy=E(_fw),_fz=B(_fg(_fu,_fx.a,_fx.b,_fy.a,_fy.b));return new T2(0,_fz.a,_fz.b);},_fA=function(_fB,_fC,_fD,_fE,_fF){var _fG=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fB).c).a);})));})));}),_fH=new T(function(){var _fI=E(_fB).a,_fJ=new T(function(){return B(A3(_95,B(_8X(_fI)),new T(function(){return B(_6I(_fG));}),_fD));});return B(A3(_93,_fI,_fJ,_fF));});return new T2(0,new T(function(){return B(A3(_6I,_fG,_fC,_fE));}),_fH);},_fK=function(_fL,_fM,_fN){var _fO=E(_fM),_fP=E(_fN),_fQ=B(_fA(_fL,_fO.a,_fO.b,_fP.a,_fP.b));return new T2(0,_fQ.a,_fQ.b);},_fR=function(_fS,_fT,_fU){var _fV=B(_fW(_fS));return new F(function(){return A3(_6I,_fV,_fT,new T(function(){return B(A2(_6K,_fV,_fU));}));});},_fX=function(_fY){return E(E(_fY).e);},_fZ=function(_g0){return E(E(_g0).f);},_g1=function(_g2,_g3,_g4){var _g5=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_g2).c).a);})));})));}),_g6=new T(function(){var _g7=new T(function(){return B(A2(_fZ,_g5,_g3));});return B(A3(_95,B(_8X(E(_g2).a)),function(_g8){return new F(function(){return A3(_7k,_g5,_g8,_g7);});},_g4));});return new T2(0,new T(function(){return B(A2(_fX,_g5,_g3));}),_g6);},_g9=function(_ga,_gb){var _gc=E(_gb),_gd=B(_g1(_ga,_gc.a,_gc.b));return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg){var _gh=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gf).c).a);})));})));}),_gi=new T(function(){return B(A2(_cL,E(_gf).a,new T(function(){return B(A2(_8R,_gh,_cI));})));});return new T2(0,new T(function(){return B(A2(_8R,_gh,_gg));}),_gi);},_gj=function(_gk,_gl){var _gm=B(_ge(_gk,_gl));return new T2(0,_gm.a,_gm.b);},_gn=function(_go,_gp,_gq){var _gr=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_go).c).a);})));})));}),_gs=new T(function(){return B(A3(_95,B(_8X(E(_go).a)),new T(function(){return B(_6K(_gr));}),_gq));});return new T2(0,new T(function(){return B(A2(_6K,_gr,_gp));}),_gs);},_gt=function(_gu,_gv){var _gw=E(_gv),_gx=B(_gn(_gu,_gw.a,_gw.b));return new T2(0,_gx.a,_gx.b);},_gy=function(_gz,_gA){var _gB=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gz).c).a);})));})));}),_gC=new T(function(){return B(A2(_cL,E(_gz).a,new T(function(){return B(A2(_8R,_gB,_cI));})));});return new T2(0,new T(function(){return B(A2(_fZ,_gB,_gA));}),_gC);},_gD=function(_gE,_gF){var _gG=B(_gy(_gE,E(_gF).a));return new T2(0,_gG.a,_gG.b);},_fW=function(_gH){return {_:0,a:function(_el,_ek){return new F(function(){return _fK(_gH,_el,_ek);});},b:function(_el,_ek){return new F(function(){return _fR(_gH,_el,_ek);});},c:function(_el,_ek){return new F(function(){return _ft(_gH,_el,_ek);});},d:function(_ek){return new F(function(){return _gt(_gH,_ek);});},e:function(_ek){return new F(function(){return _g9(_gH,_ek);});},f:function(_ek){return new F(function(){return _gD(_gH,_ek);});},g:function(_ek){return new F(function(){return _gj(_gH,_ek);});}};},_gI=function(_gJ){var _gK=new T(function(){return E(E(_gJ).a);}),_gL=new T3(0,_8O,_8T,new T2(0,_gK,new T(function(){return E(E(_gJ).b);}))),_gM=new T(function(){return B(_eh(new T(function(){return B(_fd(new T(function(){return B(_fW(_gL));}),_gL));}),_gL));}),_gN=new T(function(){return B(_7i(new T(function(){return B(_7g(_gK));})));});return function(_gO){var _gP=E(_gO),_gQ=B(A2(_8R,_gN,_8Q)),_gR=B(A2(_8R,_gN,_8P));return E(B(_7s(_gM,new T2(0,_gP.a,new T3(0,E(_gQ),E(_gR),E(_gR))),new T2(0,_gP.b,new T3(0,E(_gR),E(_gQ),E(_gR))),new T2(0,_gP.c,new T3(0,E(_gR),E(_gR),E(_gQ))))).b);};},_gS=new T(function(){return B(_gI(_8k));}),_gT=function(_gU,_gV){var _gW=E(_gV);return (_gW._==0)?__Z:new T2(1,_gU,new T2(1,_gW.a,new T(function(){return B(_gT(_gU,_gW.b));})));},_gX=new T(function(){var _gY=B(A1(_gS,_7T));return new T2(1,_gY.a,new T(function(){return B(_gT(_r,new T2(1,_gY.b,new T2(1,_gY.c,_o))));}));}),_gZ=new T1(1,_gX),_h0=new T2(1,_gZ,_w),_h1=new T(function(){return B(unCStr("vec3("));}),_h2=new T1(0,_h1),_h3=new T2(1,_h2,_h0),_h4=new T(function(){return toJSStr(B(_7K(_p,_7H,_h3)));}),_h5=function(_h6,_h7){while(1){var _h8=E(_h6);if(!_h8._){return E(_h7);}else{var _h9=_h7+1|0;_h6=_h8.b;_h7=_h9;continue;}}},_ha=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hb=new T(function(){return B(err(_ha));}),_hc=0,_hd=new T3(0,E(_hc),E(_hc),E(_hc)),_he=new T(function(){return B(unCStr("Negative exponent"));}),_hf=new T(function(){return B(err(_he));}),_hg=function(_hh,_hi,_hj){while(1){if(!(_hi%2)){var _hk=_hh*_hh,_hl=quot(_hi,2);_hh=_hk;_hi=_hl;continue;}else{var _hm=E(_hi);if(_hm==1){return _hh*_hj;}else{var _hk=_hh*_hh,_hn=_hh*_hj;_hh=_hk;_hi=quot(_hm-1|0,2);_hj=_hn;continue;}}}},_ho=function(_hp,_hq){while(1){if(!(_hq%2)){var _hr=_hp*_hp,_hs=quot(_hq,2);_hp=_hr;_hq=_hs;continue;}else{var _ht=E(_hq);if(_ht==1){return E(_hp);}else{return new F(function(){return _hg(_hp*_hp,quot(_ht-1|0,2),_hp);});}}}},_hu=function(_hv){var _hw=E(_hv);return new F(function(){return Math.log(_hw+(_hw+1)*Math.sqrt((_hw-1)/(_hw+1)));});},_hx=function(_hy){var _hz=E(_hy);return new F(function(){return Math.log(_hz+Math.sqrt(1+_hz*_hz));});},_hA=function(_hB){var _hC=E(_hB);return 0.5*Math.log((1+_hC)/(1-_hC));},_hD=function(_hE,_hF){return Math.log(E(_hF))/Math.log(E(_hE));},_hG=3.141592653589793,_hH=function(_hI){var _hJ=E(_hI);return new F(function(){return _6j(_hJ.a,_hJ.b);});},_hK=function(_hL){return 1/E(_hL);},_hM=function(_hN){var _hO=E(_hN),_hP=E(_hO);return (_hP==0)?E(_6i):(_hP<=0)? -_hP:E(_hO);},_hQ=function(_hR){var _hS=E(_hR);if(!_hS._){return _hS.a;}else{return new F(function(){return I_toNumber(_hS.a);});}},_hT=function(_hU){return new F(function(){return _hQ(_hU);});},_hV=1,_hW=-1,_hX=function(_hY){var _hZ=E(_hY);return (_hZ<=0)?(_hZ>=0)?E(_hZ):E(_hW):E(_hV);},_i0=function(_i1,_i2){return E(_i1)-E(_i2);},_i3=function(_i4){return  -E(_i4);},_i5=function(_i6,_i7){return E(_i6)+E(_i7);},_i8=function(_i9,_ia){return E(_i9)*E(_ia);},_ib={_:0,a:_i5,b:_i0,c:_i8,d:_i3,e:_hM,f:_hX,g:_hT},_ic=function(_id,_ie){return E(_id)/E(_ie);},_if=new T4(0,_ib,_ic,_hK,_hH),_ig=function(_ih){return new F(function(){return Math.acos(E(_ih));});},_ii=function(_ij){return new F(function(){return Math.asin(E(_ij));});},_ik=function(_il){return new F(function(){return Math.atan(E(_il));});},_im=function(_in){return new F(function(){return Math.cos(E(_in));});},_io=function(_ip){return new F(function(){return cosh(E(_ip));});},_iq=function(_ir){return new F(function(){return Math.exp(E(_ir));});},_is=function(_it){return new F(function(){return Math.log(E(_it));});},_iu=function(_iv,_iw){return new F(function(){return Math.pow(E(_iv),E(_iw));});},_ix=function(_iy){return new F(function(){return Math.sin(E(_iy));});},_iz=function(_iA){return new F(function(){return sinh(E(_iA));});},_iB=function(_iC){return new F(function(){return Math.sqrt(E(_iC));});},_iD=function(_iE){return new F(function(){return Math.tan(E(_iE));});},_iF=function(_iG){return new F(function(){return tanh(E(_iG));});},_iH={_:0,a:_if,b:_hG,c:_iq,d:_is,e:_iB,f:_iu,g:_hD,h:_ix,i:_im,j:_iD,k:_ii,l:_ig,m:_ik,n:_iz,o:_io,p:_iF,q:_hx,r:_hu,s:_hA},_iI=function(_iJ,_iK){return (E(_iJ)!=E(_iK))?true:false;},_iL=function(_iM,_iN){return E(_iM)==E(_iN);},_iO=new T2(0,_iL,_iI),_iP=function(_iQ,_iR){return E(_iQ)<E(_iR);},_iS=function(_iT,_iU){return E(_iT)<=E(_iU);},_iV=function(_iW,_iX){return E(_iW)>E(_iX);},_iY=function(_iZ,_j0){return E(_iZ)>=E(_j0);},_j1=function(_j2,_j3){var _j4=E(_j2),_j5=E(_j3);return (_j4>=_j5)?(_j4!=_j5)?2:1:0;},_j6=function(_j7,_j8){var _j9=E(_j7),_ja=E(_j8);return (_j9>_ja)?E(_j9):E(_ja);},_jb=function(_jc,_jd){var _je=E(_jc),_jf=E(_jd);return (_je>_jf)?E(_jf):E(_je);},_jg={_:0,a:_iO,b:_j1,c:_iP,d:_iS,e:_iV,f:_iY,g:_j6,h:_jb},_jh="dz",_ji="wy",_jj="wx",_jk="dy",_jl="dx",_jm="t",_jn="a",_jo="r",_jp="ly",_jq="lx",_jr="wz",_js=0,_jt=function(_ju){var _jv=__new(),_jw=_jv,_jx=function(_jy,_){while(1){var _jz=E(_jy);if(!_jz._){return _js;}else{var _jA=E(_jz.a),_jB=__set(_jw,E(_jA.a),E(_jA.b));_jy=_jz.b;continue;}}},_jC=B(_jx(_ju,_));return E(_jw);},_jD=function(_jE,_jF,_jG,_jH,_jI,_jJ,_jK,_jL,_jM){return new F(function(){return _jt(new T2(1,new T2(0,_jj,_jE),new T2(1,new T2(0,_ji,_jF),new T2(1,new T2(0,_jr,_jG),new T2(1,new T2(0,_jq,_jH*_jI*Math.cos(_jJ)),new T2(1,new T2(0,_jp,_jH*_jI*Math.sin(_jJ)),new T2(1,new T2(0,_jo,_jH),new T2(1,new T2(0,_jn,_jI),new T2(1,new T2(0,_jm,_jJ),new T2(1,new T2(0,_jl,_jK),new T2(1,new T2(0,_jk,_jL),new T2(1,new T2(0,_jh,_jM),_o))))))))))));});},_jN=function(_jO){var _jP=E(_jO),_jQ=E(_jP.a),_jR=E(_jP.b),_jS=E(_jP.d);return new F(function(){return _jD(_jQ.a,_jQ.b,_jQ.c,E(_jR.a),E(_jR.b),E(_jP.c),_jS.a,_jS.b,_jS.c);});},_jT=function(_jU,_jV){var _jW=E(_jV);return (_jW._==0)?__Z:new T2(1,new T(function(){return B(A1(_jU,_jW.a));}),new T(function(){return B(_jT(_jU,_jW.b));}));},_jX=function(_jY,_jZ,_k0){var _k1=__lst2arr(B(_jT(_jN,new T2(1,_jY,new T2(1,_jZ,new T2(1,_k0,_o))))));return E(_k1);},_k2=function(_k3){var _k4=E(_k3);return new F(function(){return _jX(_k4.a,_k4.b,_k4.c);});},_k5=new T2(0,_iH,_jg),_k6=function(_k7,_k8,_k9,_ka,_kb,_kc,_kd){var _ke=B(_7i(B(_7g(_k7)))),_kf=new T(function(){return B(A3(_6I,_ke,new T(function(){return B(A3(_7k,_ke,_k8,_kb));}),new T(function(){return B(A3(_7k,_ke,_k9,_kc));})));});return new F(function(){return A3(_6I,_ke,_kf,new T(function(){return B(A3(_7k,_ke,_ka,_kd));}));});},_kg=function(_kh,_ki,_kj,_kk){var _kl=B(_7g(_kh)),_km=new T(function(){return B(A2(_7q,_kh,new T(function(){return B(_k6(_kh,_ki,_kj,_kk,_ki,_kj,_kk));})));});return new T3(0,B(A3(_91,_kl,_ki,_km)),B(A3(_91,_kl,_kj,_km)),B(A3(_91,_kl,_kk,_km)));},_kn=function(_ko,_kp,_kq,_kr,_ks,_kt,_ku){var _kv=B(_7k(_ko));return new T3(0,B(A1(B(A1(_kv,_kp)),_ks)),B(A1(B(A1(_kv,_kq)),_kt)),B(A1(B(A1(_kv,_kr)),_ku)));},_kw=function(_kx,_ky,_kz,_kA,_kB,_kC,_kD){var _kE=B(_6I(_kx));return new T3(0,B(A1(B(A1(_kE,_ky)),_kB)),B(A1(B(A1(_kE,_kz)),_kC)),B(A1(B(A1(_kE,_kA)),_kD)));},_kF=function(_kG,_kH){var _kI=new T(function(){return E(E(_kG).a);}),_kJ=new T(function(){return B(A2(_gI,new T2(0,_kI,new T(function(){return E(E(_kG).b);})),_kH));}),_kK=new T(function(){var _kL=E(_kJ),_kM=B(_kg(_kI,_kL.a,_kL.b,_kL.c));return new T3(0,E(_kM.a),E(_kM.b),E(_kM.c));}),_kN=new T(function(){var _kO=E(_kH),_kP=_kO.a,_kQ=_kO.b,_kR=_kO.c,_kS=E(_kK),_kT=B(_7g(_kI)),_kU=new T(function(){return B(A2(_7q,_kI,new T(function(){var _kV=E(_kJ),_kW=_kV.a,_kX=_kV.b,_kY=_kV.c;return B(_k6(_kI,_kW,_kX,_kY,_kW,_kX,_kY));})));}),_kZ=B(A3(_91,_kT,new T(function(){return B(_7s(_kI,_kP,_kQ,_kR));}),_kU)),_l0=B(_7i(_kT)),_l1=B(_kn(_l0,_kS.a,_kS.b,_kS.c,_kZ,_kZ,_kZ)),_l2=B(_6K(_l0)),_l3=B(_kw(_l0,_kP,_kQ,_kR,B(A1(_l2,_l1.a)),B(A1(_l2,_l1.b)),B(A1(_l2,_l1.c))));return new T3(0,E(_l3.a),E(_l3.b),E(_l3.c));});return new T2(0,_kN,_kK);},_l4=function(_l5){return E(E(_l5).a);},_l6=function(_l7,_l8,_l9,_la,_lb,_lc,_ld){var _le=B(_k6(_l7,_lb,_lc,_ld,_l8,_l9,_la)),_lf=B(_7i(B(_7g(_l7)))),_lg=B(_kn(_lf,_lb,_lc,_ld,_le,_le,_le)),_lh=B(_6K(_lf));return new F(function(){return _kw(_lf,_l8,_l9,_la,B(A1(_lh,_lg.a)),B(A1(_lh,_lg.b)),B(A1(_lh,_lg.c)));});},_li=function(_lj){return E(E(_lj).a);},_lk=function(_ll,_lm,_ln,_lo){var _lp=new T(function(){var _lq=E(_lo),_lr=E(_ln),_ls=B(_l6(_ll,_lq.a,_lq.b,_lq.c,_lr.a,_lr.b,_lr.c));return new T3(0,E(_ls.a),E(_ls.b),E(_ls.c));}),_lt=new T(function(){return B(A2(_7q,_ll,new T(function(){var _lu=E(_lp),_lv=_lu.a,_lw=_lu.b,_lx=_lu.c;return B(_k6(_ll,_lv,_lw,_lx,_lv,_lw,_lx));})));});if(!B(A3(_li,B(_l4(_lm)),_lt,new T(function(){return B(A2(_8R,B(_7i(B(_7g(_ll)))),_8P));})))){var _ly=E(_lp),_lz=B(_kg(_ll,_ly.a,_ly.b,_ly.c)),_lA=B(A2(_7q,_ll,new T(function(){var _lB=E(_lo),_lC=_lB.a,_lD=_lB.b,_lE=_lB.c;return B(_k6(_ll,_lC,_lD,_lE,_lC,_lD,_lE));}))),_lF=B(_7k(new T(function(){return B(_7i(new T(function(){return B(_7g(_ll));})));})));return new T3(0,B(A1(B(A1(_lF,_lz.a)),_lA)),B(A1(B(A1(_lF,_lz.b)),_lA)),B(A1(B(A1(_lF,_lz.c)),_lA)));}else{var _lG=B(A2(_8R,B(_7i(B(_7g(_ll)))),_8P));return new T3(0,_lG,_lG,_lG);}},_lH=new T(function(){var _lI=eval("angleCount"),_lJ=Number(_lI);return jsTrunc(_lJ);}),_lK=new T(function(){return E(_lH);}),_lL=new T(function(){return B(unCStr(": empty list"));}),_lM=new T(function(){return B(unCStr("Prelude."));}),_lN=function(_lO){return new F(function(){return err(B(_f(_lM,new T(function(){return B(_f(_lO,_lL));},1))));});},_lP=new T(function(){return B(unCStr("head"));}),_lQ=new T(function(){return B(_lN(_lP));}),_lR=function(_lS,_lT,_lU){var _lV=E(_lS);if(!_lV._){return __Z;}else{var _lW=E(_lT);if(!_lW._){return __Z;}else{var _lX=_lW.a,_lY=E(_lU);if(!_lY._){return __Z;}else{var _lZ=E(_lY.a),_m0=_lZ.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_lV.a),E(_lX),E(_m0));}),new T2(1,new T(function(){return new T3(0,E(_lX),E(_m0),E(_lZ.b));}),_o)),new T(function(){return B(_lR(_lV.b,_lW.b,_lY.b));},1));});}}}},_m1=new T(function(){return B(unCStr("tail"));}),_m2=new T(function(){return B(_lN(_m1));}),_m3=function(_m4,_m5){var _m6=E(_m4);if(!_m6._){return __Z;}else{var _m7=E(_m5);return (_m7._==0)?__Z:new T2(1,new T2(0,_m6.a,_m7.a),new T(function(){return B(_m3(_m6.b,_m7.b));}));}},_m8=function(_m9,_ma){var _mb=E(_m9);if(!_mb._){return __Z;}else{var _mc=E(_ma);if(!_mc._){return __Z;}else{var _md=E(_mb.a),_me=_md.b,_mf=E(_mc.a).b,_mg=new T(function(){var _mh=new T(function(){return B(_m3(_mf,new T(function(){var _mi=E(_mf);if(!_mi._){return E(_m2);}else{return E(_mi.b);}},1)));},1);return B(_lR(_me,new T(function(){var _mj=E(_me);if(!_mj._){return E(_m2);}else{return E(_mj.b);}},1),_mh));});return new F(function(){return _f(new T2(1,new T(function(){var _mk=E(_me);if(!_mk._){return E(_lQ);}else{var _ml=E(_mf);if(!_ml._){return E(_lQ);}else{return new T3(0,E(_md.a),E(_mk.a),E(_ml.a));}}}),_mg),new T(function(){return B(_m8(_mb.b,_mc.b));},1));});}}},_mm=new T(function(){return E(_lK)-1;}),_mn=new T1(0,1),_mo=function(_mp,_mq){var _mr=E(_mq),_ms=new T(function(){var _mt=B(_7i(_mp)),_mu=B(_mo(_mp,B(A3(_6I,_mt,_mr,new T(function(){return B(A2(_8R,_mt,_mn));})))));return new T2(1,_mu.a,_mu.b);});return new T2(0,_mr,_ms);},_mv=function(_mw){return E(E(_mw).d);},_mx=new T1(0,2),_my=function(_mz,_mA){var _mB=E(_mA);if(!_mB._){return __Z;}else{var _mC=_mB.a;return (!B(A1(_mz,_mC)))?__Z:new T2(1,_mC,new T(function(){return B(_my(_mz,_mB.b));}));}},_mD=function(_mE,_mF,_mG,_mH){var _mI=B(_mo(_mF,_mG)),_mJ=new T(function(){var _mK=B(_7i(_mF)),_mL=new T(function(){return B(A3(_91,_mF,new T(function(){return B(A2(_8R,_mK,_mn));}),new T(function(){return B(A2(_8R,_mK,_mx));})));});return B(A3(_6I,_mK,_mH,_mL));});return new F(function(){return _my(function(_mM){return new F(function(){return A3(_mv,_mE,_mM,_mJ);});},new T2(1,_mI.a,_mI.b));});},_mN=new T(function(){return B(_mD(_jg,_if,_hc,_mm));}),_mO=function(_mP,_mQ){while(1){var _mR=E(_mP);if(!_mR._){return E(_mQ);}else{_mP=_mR.b;_mQ=_mR.a;continue;}}},_mS=new T(function(){return B(unCStr("last"));}),_mT=new T(function(){return B(_lN(_mS));}),_mU=function(_mV){return new F(function(){return _mO(_mV,_mT);});},_mW=function(_mX){return new F(function(){return _mU(E(_mX).b);});},_mY=new T(function(){var _mZ=eval("proceedCount"),_n0=Number(_mZ);return jsTrunc(_n0);}),_n1=new T(function(){return E(_mY);}),_n2=1,_n3=new T(function(){return B(_mD(_jg,_if,_n2,_n1));}),_n4=function(_n5,_n6,_n7,_n8,_n9,_na,_nb,_nc,_nd,_ne,_nf,_ng,_nh,_ni){var _nj=new T(function(){var _nk=new T(function(){var _nl=E(_ne),_nm=E(_ni),_nn=E(_nh),_no=E(_nf),_np=E(_ng),_nq=E(_nd);return new T3(0,_nl*_nm-_nn*_no,_no*_np-_nm*_nq,_nq*_nn-_np*_nl);}),_nr=function(_ns){var _nt=new T(function(){var _nu=E(_ns)/E(_lK);return (_nu+_nu)*3.141592653589793;}),_nv=new T(function(){return B(A1(_n5,_nt));}),_nw=new T(function(){var _nx=new T(function(){var _ny=E(_nv)/E(_n1);return new T3(0,E(_ny),E(_ny),E(_ny));}),_nz=function(_nA,_nB){var _nC=E(_nA);if(!_nC._){return new T2(0,_o,_nB);}else{var _nD=new T(function(){var _nE=B(_kF(_k5,new T(function(){var _nF=E(_nB),_nG=E(_nF.a),_nH=E(_nF.b),_nI=E(_nx);return new T3(0,E(_nG.a)+E(_nH.a)*E(_nI.a),E(_nG.b)+E(_nH.b)*E(_nI.b),E(_nG.c)+E(_nH.c)*E(_nI.c));}))),_nJ=_nE.a,_nK=new T(function(){var _nL=E(_nE.b),_nM=E(E(_nB).b),_nN=B(_l6(_iH,_nM.a,_nM.b,_nM.c,_nL.a,_nL.b,_nL.c)),_nO=B(_kg(_iH,_nN.a,_nN.b,_nN.c));return new T3(0,E(_nO.a),E(_nO.b),E(_nO.c));});return new T2(0,new T(function(){var _nP=E(_nv),_nQ=E(_nt);return new T4(0,E(_nJ),E(new T2(0,E(_nC.a)/E(_n1),E(_nP))),E(_nQ),E(_nK));}),new T2(0,_nJ,_nK));}),_nR=new T(function(){var _nS=B(_nz(_nC.b,new T(function(){return E(E(_nD).b);})));return new T2(0,_nS.a,_nS.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nD).a);}),new T(function(){return E(E(_nR).a);})),new T(function(){return E(E(_nR).b);}));}},_nT=function(_nU,_nV,_nW,_nX,_nY){var _nZ=E(_nU);if(!_nZ._){return new T2(0,_o,new T2(0,new T3(0,E(_nV),E(_nW),E(_nX)),_nY));}else{var _o0=new T(function(){var _o1=B(_kF(_k5,new T(function(){var _o2=E(_nY),_o3=E(_nx);return new T3(0,E(_nV)+E(_o2.a)*E(_o3.a),E(_nW)+E(_o2.b)*E(_o3.b),E(_nX)+E(_o2.c)*E(_o3.c));}))),_o4=_o1.a,_o5=new T(function(){var _o6=E(_o1.b),_o7=E(_nY),_o8=B(_l6(_iH,_o7.a,_o7.b,_o7.c,_o6.a,_o6.b,_o6.c)),_o9=B(_kg(_iH,_o8.a,_o8.b,_o8.c));return new T3(0,E(_o9.a),E(_o9.b),E(_o9.c));});return new T2(0,new T(function(){var _oa=E(_nv),_ob=E(_nt);return new T4(0,E(_o4),E(new T2(0,E(_nZ.a)/E(_n1),E(_oa))),E(_ob),E(_o5));}),new T2(0,_o4,_o5));}),_oc=new T(function(){var _od=B(_nz(_nZ.b,new T(function(){return E(E(_o0).b);})));return new T2(0,_od.a,_od.b);});return new T2(0,new T2(1,new T(function(){return E(E(_o0).a);}),new T(function(){return E(E(_oc).a);})),new T(function(){return E(E(_oc).b);}));}};return E(B(_nT(_n3,_n8,_n9,_na,new T(function(){var _oe=E(_nk),_of=E(_nt)+_nb,_og=Math.cos(_of),_oh=Math.sin(_of);return new T3(0,E(_nd)*_og+E(_oe.a)*_oh,E(_ne)*_og+E(_oe.b)*_oh,E(_nf)*_og+E(_oe.c)*_oh);}))).a);});return new T2(0,new T(function(){var _oi=E(_nv),_oj=E(_nt);return new T4(0,E(new T3(0,E(_n8),E(_n9),E(_na))),E(new T2(0,E(_hc),E(_oi))),E(_oj),E(_hd));}),_nw);};return B(_jT(_nr,_mN));}),_ok=new T(function(){var _ol=new T(function(){var _om=B(_f(_nj,new T2(1,new T(function(){var _on=E(_nj);if(!_on._){return E(_lQ);}else{return E(_on.a);}}),_o)));if(!_om._){return E(_m2);}else{return E(_om.b);}},1);return B(_m8(_nj,_ol));});return new T2(0,_ok,new T(function(){return B(_jT(_mW,_nj));}));},_oo=function(_op,_oq,_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE,_oF){var _oG=B(_kF(_k5,new T3(0,E(_os),E(_ot),E(_ou)))),_oH=_oG.b,_oI=E(_oG.a),_oJ=B(_lk(_iH,_jg,_oH,new T3(0,E(_ow),E(_ox),E(_oy)))),_oK=E(_oH),_oL=_oK.a,_oM=_oK.b,_oN=_oK.c,_oO=B(_l6(_iH,_oA,_oB,_oC,_oL,_oM,_oN)),_oP=B(_kg(_iH,_oO.a,_oO.b,_oO.c)),_oQ=_oP.a,_oR=_oP.b,_oS=_oP.c,_oT=E(_ov),_oU=new T2(0,E(new T3(0,E(_oJ.a),E(_oJ.b),E(_oJ.c))),E(_oz)),_oV=B(_n4(_op,_oq,_or,_oI.a,_oI.b,_oI.c,_oT,_oU,_oQ,_oR,_oS,_oL,_oM,_oN)),_oW=__lst2arr(B(_jT(_k2,_oV.a))),_oX=__lst2arr(B(_jT(_jN,_oV.b)));return {_:0,a:_op,b:_oq,c:_or,d:new T2(0,E(_oI),E(_oT)),e:_oU,f:new T3(0,E(_oQ),E(_oR),E(_oS)),g:_oK,h:_oW,i:_oX};},_oY=new T(function(){return 6.283185307179586/E(_lK);}),_oZ=-0.4,_p0=new T3(0,E(_hc),E(_oZ),E(_hc)),_p1=function(_){return new F(function(){return __jsNull();});},_p2=function(_p3){var _p4=B(A1(_p3,_));return E(_p4);},_p5=new T(function(){return B(_p2(_p1));}),_p6=function(_p7,_p8,_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi,_pj){var _pk=function(_pl){var _pm=E(_oY),_pn=2+_pl|0,_po=_pn-1|0,_pp=(2+_pl)*(1+_pl),_pq=E(_mN);if(!_pq._){return _pm*0;}else{var _pr=_pq.a,_ps=_pq.b,_pt=B(A1(_p7,new T(function(){return 6.283185307179586*E(_pr)/E(_lK);}))),_pu=B(A1(_p7,new T(function(){return 6.283185307179586*(E(_pr)+1)/E(_lK);})));if(_pt!=_pu){if(_pn>=0){var _pv=E(_pn);if(!_pv){var _pw=function(_px,_py){while(1){var _pz=B((function(_pA,_pB){var _pC=E(_pA);if(!_pC._){return E(_pB);}else{var _pD=_pC.a,_pE=_pC.b,_pF=B(A1(_p7,new T(function(){return 6.283185307179586*E(_pD)/E(_lK);}))),_pG=B(A1(_p7,new T(function(){return 6.283185307179586*(E(_pD)+1)/E(_lK);})));if(_pF!=_pG){var _pH=_pB+0/(_pF-_pG)/_pp;_px=_pE;_py=_pH;return __continue;}else{if(_po>=0){var _pI=E(_po);if(!_pI){var _pH=_pB+_pn/_pp;_px=_pE;_py=_pH;return __continue;}else{var _pH=_pB+_pn*B(_ho(_pF,_pI))/_pp;_px=_pE;_py=_pH;return __continue;}}else{return E(_hf);}}}})(_px,_py));if(_pz!=__continue){return _pz;}}};return _pm*B(_pw(_ps,0/(_pt-_pu)/_pp));}else{var _pJ=function(_pK,_pL){while(1){var _pM=B((function(_pN,_pO){var _pP=E(_pN);if(!_pP._){return E(_pO);}else{var _pQ=_pP.a,_pR=_pP.b,_pS=B(A1(_p7,new T(function(){return 6.283185307179586*E(_pQ)/E(_lK);}))),_pT=B(A1(_p7,new T(function(){return 6.283185307179586*(E(_pQ)+1)/E(_lK);})));if(_pS!=_pT){if(_pv>=0){var _pU=_pO+(B(_ho(_pS,_pv))-B(_ho(_pT,_pv)))/(_pS-_pT)/_pp;_pK=_pR;_pL=_pU;return __continue;}else{return E(_hf);}}else{if(_po>=0){var _pV=E(_po);if(!_pV){var _pU=_pO+_pn/_pp;_pK=_pR;_pL=_pU;return __continue;}else{var _pU=_pO+_pn*B(_ho(_pS,_pV))/_pp;_pK=_pR;_pL=_pU;return __continue;}}else{return E(_hf);}}}})(_pK,_pL));if(_pM!=__continue){return _pM;}}};return _pm*B(_pJ(_ps,(B(_ho(_pt,_pv))-B(_ho(_pu,_pv)))/(_pt-_pu)/_pp));}}else{return E(_hf);}}else{if(_po>=0){var _pW=E(_po);if(!_pW){var _pX=function(_pY,_pZ){while(1){var _q0=B((function(_q1,_q2){var _q3=E(_q1);if(!_q3._){return E(_q2);}else{var _q4=_q3.a,_q5=_q3.b,_q6=B(A1(_p7,new T(function(){return 6.283185307179586*E(_q4)/E(_lK);}))),_q7=B(A1(_p7,new T(function(){return 6.283185307179586*(E(_q4)+1)/E(_lK);})));if(_q6!=_q7){if(_pn>=0){var _q8=E(_pn);if(!_q8){var _q9=_q2+0/(_q6-_q7)/_pp;_pY=_q5;_pZ=_q9;return __continue;}else{var _q9=_q2+(B(_ho(_q6,_q8))-B(_ho(_q7,_q8)))/(_q6-_q7)/_pp;_pY=_q5;_pZ=_q9;return __continue;}}else{return E(_hf);}}else{var _q9=_q2+_pn/_pp;_pY=_q5;_pZ=_q9;return __continue;}}})(_pY,_pZ));if(_q0!=__continue){return _q0;}}};return _pm*B(_pX(_ps,_pn/_pp));}else{var _qa=function(_qb,_qc){while(1){var _qd=B((function(_qe,_qf){var _qg=E(_qe);if(!_qg._){return E(_qf);}else{var _qh=_qg.a,_qi=_qg.b,_qj=B(A1(_p7,new T(function(){return 6.283185307179586*E(_qh)/E(_lK);}))),_qk=B(A1(_p7,new T(function(){return 6.283185307179586*(E(_qh)+1)/E(_lK);})));if(_qj!=_qk){if(_pn>=0){var _ql=E(_pn);if(!_ql){var _qm=_qf+0/(_qj-_qk)/_pp;_qb=_qi;_qc=_qm;return __continue;}else{var _qm=_qf+(B(_ho(_qj,_ql))-B(_ho(_qk,_ql)))/(_qj-_qk)/_pp;_qb=_qi;_qc=_qm;return __continue;}}else{return E(_hf);}}else{if(_pW>=0){var _qm=_qf+_pn*B(_ho(_qj,_pW))/_pp;_qb=_qi;_qc=_qm;return __continue;}else{return E(_hf);}}}})(_qb,_qc));if(_qd!=__continue){return _qd;}}};return _pm*B(_qa(_ps,_pn*B(_ho(_pt,_pW))/_pp));}}else{return E(_hf);}}}},_qn=E(_p5),_qo=1/(B(_pk(1))*_p8);return new F(function(){return _oo(_p7,_p0,new T2(0,E(new T3(0,E(_qo),E(_qo),E(_qo))),1/(B(_pk(3))*_p8)),_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi,_pj,_hd,_qn,_qn);});},_qp=0,_qq=-2,_qr=-0.2,_qs=0.2,_qt=0.4,_qu=function(_qv){return E(_qt);},_qw=1,_qx=new T(function(){var _qy=B(_p6(_qu,1.2,_qs,_qr,_qs,_qp,_qp,_qp,_qp,_qq,_qp,_qp,_qw));return {_:0,a:E(_qy.a),b:E(_qy.b),c:E(_qy.c),d:E(_qy.d),e:E(_qy.e),f:E(_qy.f),g:E(_qy.g),h:_qy.h,i:_qy.i};}),_qz=0,_qA=-0.1,_qB=1.3,_qC=function(_qD){var _qE=I_decodeDouble(_qD);return new T2(0,new T1(1,_qE.b),_qE.a);},_qF=function(_qG){return new T1(0,_qG);},_qH=function(_qI){var _qJ=hs_intToInt64(2147483647),_qK=hs_leInt64(_qI,_qJ);if(!_qK){return new T1(1,I_fromInt64(_qI));}else{var _qL=hs_intToInt64(-2147483648),_qM=hs_geInt64(_qI,_qL);if(!_qM){return new T1(1,I_fromInt64(_qI));}else{var _qN=hs_int64ToInt(_qI);return new F(function(){return _qF(_qN);});}}},_qO=new T(function(){var _qP=newByteArr(256),_qQ=_qP,_=_qQ["v"]["i8"][0]=8,_qR=function(_qS,_qT,_qU,_){while(1){if(_qU>=256){if(_qS>=256){return E(_);}else{var _qV=imul(2,_qS)|0,_qW=_qT+1|0,_qX=_qS;_qS=_qV;_qT=_qW;_qU=_qX;continue;}}else{var _=_qQ["v"]["i8"][_qU]=_qT,_qX=_qU+_qS|0;_qU=_qX;continue;}}},_=B(_qR(2,0,1,_));return _qQ;}),_qY=function(_qZ,_r0){var _r1=hs_int64ToInt(_qZ),_r2=E(_qO),_r3=_r2["v"]["i8"][(255&_r1>>>0)>>>0&4294967295];if(_r0>_r3){if(_r3>=8){var _r4=hs_uncheckedIShiftRA64(_qZ,8),_r5=function(_r6,_r7){while(1){var _r8=B((function(_r9,_ra){var _rb=hs_int64ToInt(_r9),_rc=_r2["v"]["i8"][(255&_rb>>>0)>>>0&4294967295];if(_ra>_rc){if(_rc>=8){var _rd=hs_uncheckedIShiftRA64(_r9,8),_re=_ra-8|0;_r6=_rd;_r7=_re;return __continue;}else{return new T2(0,new T(function(){var _rf=hs_uncheckedIShiftRA64(_r9,_rc);return B(_qH(_rf));}),_ra-_rc|0);}}else{return new T2(0,new T(function(){var _rg=hs_uncheckedIShiftRA64(_r9,_ra);return B(_qH(_rg));}),0);}})(_r6,_r7));if(_r8!=__continue){return _r8;}}};return new F(function(){return _r5(_r4,_r0-8|0);});}else{return new T2(0,new T(function(){var _rh=hs_uncheckedIShiftRA64(_qZ,_r3);return B(_qH(_rh));}),_r0-_r3|0);}}else{return new T2(0,new T(function(){var _ri=hs_uncheckedIShiftRA64(_qZ,_r0);return B(_qH(_ri));}),0);}},_rj=function(_rk){var _rl=hs_intToInt64(_rk);return E(_rl);},_rm=function(_rn){var _ro=E(_rn);if(!_ro._){return new F(function(){return _rj(_ro.a);});}else{return new F(function(){return I_toInt64(_ro.a);});}},_rp=function(_rq){return I_toInt(_rq)>>>0;},_rr=function(_rs){var _rt=E(_rs);if(!_rt._){return _rt.a>>>0;}else{return new F(function(){return _rp(_rt.a);});}},_ru=function(_rv){var _rw=B(_qC(_rv)),_rx=_rw.a,_ry=_rw.b;if(_ry<0){var _rz=function(_rA){if(!_rA){return new T2(0,E(_rx),B(_3u(_1M, -_ry)));}else{var _rB=B(_qY(B(_rm(_rx)), -_ry));return new T2(0,E(_rB.a),B(_3u(_1M,_rB.b)));}};if(!((B(_rr(_rx))&1)>>>0)){return new F(function(){return _rz(1);});}else{return new F(function(){return _rz(0);});}}else{return new T2(0,B(_3u(_rx,_ry)),_1M);}},_rC=function(_rD){var _rE=B(_ru(E(_rD)));return new T2(0,E(_rE.a),E(_rE.b));},_rF=new T3(0,_ib,_jg,_rC),_rG=function(_rH){return E(E(_rH).a);},_rI=function(_rJ){return E(E(_rJ).a);},_rK=function(_rL,_rM){if(_rL<=_rM){var _rN=function(_rO){return new T2(1,_rO,new T(function(){if(_rO!=_rM){return B(_rN(_rO+1|0));}else{return __Z;}}));};return new F(function(){return _rN(_rL);});}else{return __Z;}},_rP=function(_rQ){return new F(function(){return _rK(E(_rQ),2147483647);});},_rR=function(_rS,_rT,_rU){if(_rU<=_rT){var _rV=new T(function(){var _rW=_rT-_rS|0,_rX=function(_rY){return (_rY>=(_rU-_rW|0))?new T2(1,_rY,new T(function(){return B(_rX(_rY+_rW|0));})):new T2(1,_rY,_o);};return B(_rX(_rT));});return new T2(1,_rS,_rV);}else{return (_rU<=_rS)?new T2(1,_rS,_o):__Z;}},_rZ=function(_s0,_s1,_s2){if(_s2>=_s1){var _s3=new T(function(){var _s4=_s1-_s0|0,_s5=function(_s6){return (_s6<=(_s2-_s4|0))?new T2(1,_s6,new T(function(){return B(_s5(_s6+_s4|0));})):new T2(1,_s6,_o);};return B(_s5(_s1));});return new T2(1,_s0,_s3);}else{return (_s2>=_s0)?new T2(1,_s0,_o):__Z;}},_s7=function(_s8,_s9){if(_s9<_s8){return new F(function(){return _rR(_s8,_s9,-2147483648);});}else{return new F(function(){return _rZ(_s8,_s9,2147483647);});}},_sa=function(_sb,_sc){return new F(function(){return _s7(E(_sb),E(_sc));});},_sd=function(_se,_sf,_sg){if(_sf<_se){return new F(function(){return _rR(_se,_sf,_sg);});}else{return new F(function(){return _rZ(_se,_sf,_sg);});}},_sh=function(_si,_sj,_sk){return new F(function(){return _sd(E(_si),E(_sj),E(_sk));});},_sl=function(_sm,_sn){return new F(function(){return _rK(E(_sm),E(_sn));});},_so=function(_sp){return E(_sp);},_sq=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_sr=new T(function(){return B(err(_sq));}),_ss=function(_st){var _su=E(_st);return (_su==(-2147483648))?E(_sr):_su-1|0;},_sv=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_sw=new T(function(){return B(err(_sv));}),_sx=function(_sy){var _sz=E(_sy);return (_sz==2147483647)?E(_sw):_sz+1|0;},_sA={_:0,a:_sx,b:_ss,c:_so,d:_so,e:_rP,f:_sa,g:_sl,h:_sh},_sB=function(_sC,_sD){if(_sC<=0){if(_sC>=0){return new F(function(){return quot(_sC,_sD);});}else{if(_sD<=0){return new F(function(){return quot(_sC,_sD);});}else{return quot(_sC+1|0,_sD)-1|0;}}}else{if(_sD>=0){if(_sC>=0){return new F(function(){return quot(_sC,_sD);});}else{if(_sD<=0){return new F(function(){return quot(_sC,_sD);});}else{return quot(_sC+1|0,_sD)-1|0;}}}else{return quot(_sC-1|0,_sD)-1|0;}}},_sE=0,_sF=new T(function(){return B(_2R(_sE));}),_sG=new T(function(){return die(_sF);}),_sH=function(_sI,_sJ){var _sK=E(_sJ);switch(_sK){case -1:var _sL=E(_sI);if(_sL==(-2147483648)){return E(_sG);}else{return new F(function(){return _sB(_sL,-1);});}break;case 0:return E(_2V);default:return new F(function(){return _sB(_sI,_sK);});}},_sM=function(_sN,_sO){return new F(function(){return _sH(E(_sN),E(_sO));});},_sP=0,_sQ=new T2(0,_sG,_sP),_sR=function(_sS,_sT){var _sU=E(_sS),_sV=E(_sT);switch(_sV){case -1:var _sW=E(_sU);if(_sW==(-2147483648)){return E(_sQ);}else{if(_sW<=0){if(_sW>=0){var _sX=quotRemI(_sW,-1);return new T2(0,_sX.a,_sX.b);}else{var _sY=quotRemI(_sW,-1);return new T2(0,_sY.a,_sY.b);}}else{var _sZ=quotRemI(_sW-1|0,-1);return new T2(0,_sZ.a-1|0,(_sZ.b+(-1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_sU<=0){if(_sU>=0){var _t0=quotRemI(_sU,_sV);return new T2(0,_t0.a,_t0.b);}else{if(_sV<=0){var _t1=quotRemI(_sU,_sV);return new T2(0,_t1.a,_t1.b);}else{var _t2=quotRemI(_sU+1|0,_sV);return new T2(0,_t2.a-1|0,(_t2.b+_sV|0)-1|0);}}}else{if(_sV>=0){if(_sU>=0){var _t3=quotRemI(_sU,_sV);return new T2(0,_t3.a,_t3.b);}else{if(_sV<=0){var _t4=quotRemI(_sU,_sV);return new T2(0,_t4.a,_t4.b);}else{var _t5=quotRemI(_sU+1|0,_sV);return new T2(0,_t5.a-1|0,(_t5.b+_sV|0)-1|0);}}}else{var _t6=quotRemI(_sU-1|0,_sV);return new T2(0,_t6.a-1|0,(_t6.b+_sV|0)+1|0);}}}},_t7=function(_t8,_t9){var _ta=_t8%_t9;if(_t8<=0){if(_t8>=0){return E(_ta);}else{if(_t9<=0){return E(_ta);}else{var _tb=E(_ta);return (_tb==0)?0:_tb+_t9|0;}}}else{if(_t9>=0){if(_t8>=0){return E(_ta);}else{if(_t9<=0){return E(_ta);}else{var _tc=E(_ta);return (_tc==0)?0:_tc+_t9|0;}}}else{var _td=E(_ta);return (_td==0)?0:_td+_t9|0;}}},_te=function(_tf,_tg){var _th=E(_tg);switch(_th){case -1:return E(_sP);case 0:return E(_2V);default:return new F(function(){return _t7(E(_tf),_th);});}},_ti=function(_tj,_tk){var _tl=E(_tj),_tm=E(_tk);switch(_tm){case -1:var _tn=E(_tl);if(_tn==(-2147483648)){return E(_sG);}else{return new F(function(){return quot(_tn,-1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_tl,_tm);});}},_to=function(_tp,_tq){var _tr=E(_tp),_ts=E(_tq);switch(_ts){case -1:var _tt=E(_tr);if(_tt==(-2147483648)){return E(_sQ);}else{var _tu=quotRemI(_tt,-1);return new T2(0,_tu.a,_tu.b);}break;case 0:return E(_2V);default:var _tv=quotRemI(_tr,_ts);return new T2(0,_tv.a,_tv.b);}},_tw=function(_tx,_ty){var _tz=E(_ty);switch(_tz){case -1:return E(_sP);case 0:return E(_2V);default:return E(_tx)%_tz;}},_tA=function(_tB){return new F(function(){return _qF(E(_tB));});},_tC=function(_tD){return new T2(0,E(B(_qF(E(_tD)))),E(_mn));},_tE=function(_tF,_tG){return imul(E(_tF),E(_tG))|0;},_tH=function(_tI,_tJ){return E(_tI)+E(_tJ)|0;},_tK=function(_tL,_tM){return E(_tL)-E(_tM)|0;},_tN=function(_tO){var _tP=E(_tO);return (_tP<0)? -_tP:E(_tP);},_tQ=function(_tR){return new F(function(){return _38(_tR);});},_tS=function(_tT){return  -E(_tT);},_tU=-1,_tV=0,_tW=1,_tX=function(_tY){var _tZ=E(_tY);return (_tZ>=0)?(E(_tZ)==0)?E(_tV):E(_tW):E(_tU);},_u0={_:0,a:_tH,b:_tK,c:_tE,d:_tS,e:_tN,f:_tX,g:_tQ},_u1=function(_u2,_u3){return E(_u2)==E(_u3);},_u4=function(_u5,_u6){return E(_u5)!=E(_u6);},_u7=new T2(0,_u1,_u4),_u8=function(_u9,_ua){var _ub=E(_u9),_uc=E(_ua);return (_ub>_uc)?E(_ub):E(_uc);},_ud=function(_ue,_uf){var _ug=E(_ue),_uh=E(_uf);return (_ug>_uh)?E(_uh):E(_ug);},_ui=function(_uj,_uk){return (_uj>=_uk)?(_uj!=_uk)?2:1:0;},_ul=function(_um,_un){return new F(function(){return _ui(E(_um),E(_un));});},_uo=function(_up,_uq){return E(_up)>=E(_uq);},_ur=function(_us,_ut){return E(_us)>E(_ut);},_uu=function(_uv,_uw){return E(_uv)<=E(_uw);},_ux=function(_uy,_uz){return E(_uy)<E(_uz);},_uA={_:0,a:_u7,b:_ul,c:_ux,d:_uu,e:_ur,f:_uo,g:_u8,h:_ud},_uB=new T3(0,_u0,_uA,_tC),_uC={_:0,a:_uB,b:_sA,c:_ti,d:_tw,e:_sM,f:_te,g:_to,h:_sR,i:_tA},_uD=new T1(0,2),_uE=function(_uF,_uG){while(1){var _uH=E(_uF);if(!_uH._){var _uI=_uH.a,_uJ=E(_uG);if(!_uJ._){var _uK=_uJ.a;if(!(imul(_uI,_uK)|0)){return new T1(0,imul(_uI,_uK)|0);}else{_uF=new T1(1,I_fromInt(_uI));_uG=new T1(1,I_fromInt(_uK));continue;}}else{_uF=new T1(1,I_fromInt(_uI));_uG=_uJ;continue;}}else{var _uL=E(_uG);if(!_uL._){_uF=_uH;_uG=new T1(1,I_fromInt(_uL.a));continue;}else{return new T1(1,I_mul(_uH.a,_uL.a));}}}},_uM=function(_uN,_uO,_uP){while(1){if(!(_uO%2)){var _uQ=B(_uE(_uN,_uN)),_uR=quot(_uO,2);_uN=_uQ;_uO=_uR;continue;}else{var _uS=E(_uO);if(_uS==1){return new F(function(){return _uE(_uN,_uP);});}else{var _uQ=B(_uE(_uN,_uN)),_uT=B(_uE(_uN,_uP));_uN=_uQ;_uO=quot(_uS-1|0,2);_uP=_uT;continue;}}}},_uU=function(_uV,_uW){while(1){if(!(_uW%2)){var _uX=B(_uE(_uV,_uV)),_uY=quot(_uW,2);_uV=_uX;_uW=_uY;continue;}else{var _uZ=E(_uW);if(_uZ==1){return E(_uV);}else{return new F(function(){return _uM(B(_uE(_uV,_uV)),quot(_uZ-1|0,2),_uV);});}}}},_v0=function(_v1){return E(E(_v1).b);},_v2=function(_v3){return E(E(_v3).c);},_v4=new T1(0,0),_v5=function(_v6){return E(E(_v6).d);},_v7=function(_v8,_v9){var _va=B(_rG(_v8)),_vb=new T(function(){return B(_rI(_va));}),_vc=new T(function(){return B(A3(_v5,_v8,_v9,new T(function(){return B(A2(_8R,_vb,_mx));})));});return new F(function(){return A3(_li,B(_l4(B(_v0(_va)))),_vc,new T(function(){return B(A2(_8R,_vb,_v4));}));});},_vd=new T(function(){return B(unCStr("Negative exponent"));}),_ve=new T(function(){return B(err(_vd));}),_vf=function(_vg){return E(E(_vg).c);},_vh=function(_vi,_vj,_vk,_vl){var _vm=B(_rG(_vj)),_vn=new T(function(){return B(_rI(_vm));}),_vo=B(_v0(_vm));if(!B(A3(_v2,_vo,_vl,new T(function(){return B(A2(_8R,_vn,_v4));})))){if(!B(A3(_li,B(_l4(_vo)),_vl,new T(function(){return B(A2(_8R,_vn,_v4));})))){var _vp=new T(function(){return B(A2(_8R,_vn,_mx));}),_vq=new T(function(){return B(A2(_8R,_vn,_mn));}),_vr=B(_l4(_vo)),_vs=function(_vt,_vu,_vv){while(1){var _vw=B((function(_vx,_vy,_vz){if(!B(_v7(_vj,_vy))){if(!B(A3(_li,_vr,_vy,_vq))){var _vA=new T(function(){return B(A3(_vf,_vj,new T(function(){return B(A3(_7m,_vn,_vy,_vq));}),_vp));});_vt=new T(function(){return B(A3(_7k,_vi,_vx,_vx));});_vu=_vA;_vv=new T(function(){return B(A3(_7k,_vi,_vx,_vz));});return __continue;}else{return new F(function(){return A3(_7k,_vi,_vx,_vz);});}}else{var _vB=_vz;_vt=new T(function(){return B(A3(_7k,_vi,_vx,_vx));});_vu=new T(function(){return B(A3(_vf,_vj,_vy,_vp));});_vv=_vB;return __continue;}})(_vt,_vu,_vv));if(_vw!=__continue){return _vw;}}},_vC=function(_vD,_vE){while(1){var _vF=B((function(_vG,_vH){if(!B(_v7(_vj,_vH))){if(!B(A3(_li,_vr,_vH,_vq))){var _vI=new T(function(){return B(A3(_vf,_vj,new T(function(){return B(A3(_7m,_vn,_vH,_vq));}),_vp));});return new F(function(){return _vs(new T(function(){return B(A3(_7k,_vi,_vG,_vG));}),_vI,_vG);});}else{return E(_vG);}}else{_vD=new T(function(){return B(A3(_7k,_vi,_vG,_vG));});_vE=new T(function(){return B(A3(_vf,_vj,_vH,_vp));});return __continue;}})(_vD,_vE));if(_vF!=__continue){return _vF;}}};return new F(function(){return _vC(_vk,_vl);});}else{return new F(function(){return A2(_8R,_vi,_mn);});}}else{return E(_ve);}},_vJ=new T(function(){return B(err(_vd));}),_vK=function(_vL,_vM){var _vN=B(_qC(_vM)),_vO=_vN.a,_vP=_vN.b,_vQ=new T(function(){return B(_rI(new T(function(){return B(_rG(_vL));})));});if(_vP<0){var _vR= -_vP;if(_vR>=0){var _vS=E(_vR);if(!_vS){var _vT=E(_mn);}else{var _vT=B(_uU(_uD,_vS));}if(!B(_30(_vT,_3t))){var _vU=B(_3k(_vO,_vT));return new T2(0,new T(function(){return B(A2(_8R,_vQ,_vU.a));}),new T(function(){return B(_2W(_vU.b,_vP));}));}else{return E(_2V);}}else{return E(_vJ);}}else{var _vV=new T(function(){var _vW=new T(function(){return B(_vh(_vQ,_uC,new T(function(){return B(A2(_8R,_vQ,_uD));}),_vP));});return B(A3(_7k,_vQ,new T(function(){return B(A2(_8R,_vQ,_vO));}),_vW));});return new T2(0,_vV,_6i);}},_vX=function(_vY,_vZ){var _w0=B(_vK(_vY,E(_vZ))),_w1=_w0.a;if(E(_w0.b)<=0){return E(_w1);}else{var _w2=B(_rI(B(_rG(_vY))));return new F(function(){return A3(_6I,_w2,_w1,new T(function(){return B(A2(_8R,_w2,_1M));}));});}},_w3=function(_w4,_w5){var _w6=B(_vK(_w4,E(_w5))),_w7=_w6.a;if(E(_w6.b)>=0){return E(_w7);}else{var _w8=B(_rI(B(_rG(_w4))));return new F(function(){return A3(_7m,_w8,_w7,new T(function(){return B(A2(_8R,_w8,_1M));}));});}},_w9=function(_wa,_wb){var _wc=B(_vK(_wa,E(_wb)));return new T2(0,_wc.a,_wc.b);},_wd=function(_we,_wf){var _wg=B(_vK(_we,_wf)),_wh=_wg.a,_wi=E(_wg.b),_wj=new T(function(){var _wk=B(_rI(B(_rG(_we))));if(_wi>=0){return B(A3(_6I,_wk,_wh,new T(function(){return B(A2(_8R,_wk,_1M));})));}else{return B(A3(_7m,_wk,_wh,new T(function(){return B(A2(_8R,_wk,_1M));})));}}),_wl=function(_wm){var _wn=_wm-0.5;return (_wn>=0)?(E(_wn)==0)?(!B(_v7(_we,_wh)))?E(_wj):E(_wh):E(_wj):E(_wh);},_wo=E(_wi);if(!_wo){return new F(function(){return _wl(0);});}else{if(_wo<=0){var _wp= -_wo-0.5;return (_wp>=0)?(E(_wp)==0)?(!B(_v7(_we,_wh)))?E(_wj):E(_wh):E(_wj):E(_wh);}else{return new F(function(){return _wl(_wo);});}}},_wq=function(_wr,_ws){return new F(function(){return _wd(_wr,E(_ws));});},_wt=function(_wu,_wv){return E(B(_vK(_wu,E(_wv))).a);},_ww={_:0,a:_rF,b:_if,c:_w9,d:_wt,e:_wq,f:_vX,g:_w3},_wx=new T1(0,1),_wy=function(_wz,_wA){var _wB=E(_wz);return new T2(0,_wB,new T(function(){var _wC=B(_wy(B(_3b(_wB,_wA)),_wA));return new T2(1,_wC.a,_wC.b);}));},_wD=function(_wE){var _wF=B(_wy(_wE,_wx));return new T2(1,_wF.a,_wF.b);},_wG=function(_wH,_wI){var _wJ=B(_wy(_wH,new T(function(){return B(_5w(_wI,_wH));})));return new T2(1,_wJ.a,_wJ.b);},_wK=new T1(0,0),_wL=function(_wM,_wN){var _wO=E(_wM);if(!_wO._){var _wP=_wO.a,_wQ=E(_wN);return (_wQ._==0)?_wP>=_wQ.a:I_compareInt(_wQ.a,_wP)<=0;}else{var _wR=_wO.a,_wS=E(_wN);return (_wS._==0)?I_compareInt(_wR,_wS.a)>=0:I_compare(_wR,_wS.a)>=0;}},_wT=function(_wU,_wV,_wW){if(!B(_wL(_wV,_wK))){var _wX=function(_wY){return (!B(_3N(_wY,_wW)))?new T2(1,_wY,new T(function(){return B(_wX(B(_3b(_wY,_wV))));})):__Z;};return new F(function(){return _wX(_wU);});}else{var _wZ=function(_x0){return (!B(_3E(_x0,_wW)))?new T2(1,_x0,new T(function(){return B(_wZ(B(_3b(_x0,_wV))));})):__Z;};return new F(function(){return _wZ(_wU);});}},_x1=function(_x2,_x3,_x4){return new F(function(){return _wT(_x2,B(_5w(_x3,_x2)),_x4);});},_x5=function(_x6,_x7){return new F(function(){return _wT(_x6,_wx,_x7);});},_x8=function(_x9){return new F(function(){return _38(_x9);});},_xa=function(_xb){return new F(function(){return _5w(_xb,_wx);});},_xc=function(_xd){return new F(function(){return _3b(_xd,_wx);});},_xe=function(_xf){return new F(function(){return _qF(E(_xf));});},_xg={_:0,a:_xc,b:_xa,c:_xe,d:_x8,e:_wD,f:_wG,g:_x5,h:_x1},_xh=function(_xi,_xj){while(1){var _xk=E(_xi);if(!_xk._){var _xl=E(_xk.a);if(_xl==(-2147483648)){_xi=new T1(1,I_fromInt(-2147483648));continue;}else{var _xm=E(_xj);if(!_xm._){return new T1(0,B(_sB(_xl,_xm.a)));}else{_xi=new T1(1,I_fromInt(_xl));_xj=_xm;continue;}}}else{var _xn=_xk.a,_xo=E(_xj);return (_xo._==0)?new T1(1,I_div(_xn,I_fromInt(_xo.a))):new T1(1,I_div(_xn,_xo.a));}}},_xp=function(_xq,_xr){if(!B(_30(_xr,_v4))){return new F(function(){return _xh(_xq,_xr);});}else{return E(_2V);}},_xs=function(_xt,_xu){while(1){var _xv=E(_xt);if(!_xv._){var _xw=E(_xv.a);if(_xw==(-2147483648)){_xt=new T1(1,I_fromInt(-2147483648));continue;}else{var _xx=E(_xu);if(!_xx._){var _xy=_xx.a;return new T2(0,new T1(0,B(_sB(_xw,_xy))),new T1(0,B(_t7(_xw,_xy))));}else{_xt=new T1(1,I_fromInt(_xw));_xu=_xx;continue;}}}else{var _xz=E(_xu);if(!_xz._){_xt=_xv;_xu=new T1(1,I_fromInt(_xz.a));continue;}else{var _xA=I_divMod(_xv.a,_xz.a);return new T2(0,new T1(1,_xA.a),new T1(1,_xA.b));}}}},_xB=function(_xC,_xD){if(!B(_30(_xD,_v4))){var _xE=B(_xs(_xC,_xD));return new T2(0,_xE.a,_xE.b);}else{return E(_2V);}},_xF=function(_xG,_xH){while(1){var _xI=E(_xG);if(!_xI._){var _xJ=E(_xI.a);if(_xJ==(-2147483648)){_xG=new T1(1,I_fromInt(-2147483648));continue;}else{var _xK=E(_xH);if(!_xK._){return new T1(0,B(_t7(_xJ,_xK.a)));}else{_xG=new T1(1,I_fromInt(_xJ));_xH=_xK;continue;}}}else{var _xL=_xI.a,_xM=E(_xH);return (_xM._==0)?new T1(1,I_mod(_xL,I_fromInt(_xM.a))):new T1(1,I_mod(_xL,_xM.a));}}},_xN=function(_xO,_xP){if(!B(_30(_xP,_v4))){return new F(function(){return _xF(_xO,_xP);});}else{return E(_2V);}},_xQ=function(_xR,_xS){while(1){var _xT=E(_xR);if(!_xT._){var _xU=E(_xT.a);if(_xU==(-2147483648)){_xR=new T1(1,I_fromInt(-2147483648));continue;}else{var _xV=E(_xS);if(!_xV._){return new T1(0,quot(_xU,_xV.a));}else{_xR=new T1(1,I_fromInt(_xU));_xS=_xV;continue;}}}else{var _xW=_xT.a,_xX=E(_xS);return (_xX._==0)?new T1(0,I_toInt(I_quot(_xW,I_fromInt(_xX.a)))):new T1(1,I_quot(_xW,_xX.a));}}},_xY=function(_xZ,_y0){if(!B(_30(_y0,_v4))){return new F(function(){return _xQ(_xZ,_y0);});}else{return E(_2V);}},_y1=function(_y2,_y3){if(!B(_30(_y3,_v4))){var _y4=B(_3k(_y2,_y3));return new T2(0,_y4.a,_y4.b);}else{return E(_2V);}},_y5=function(_y6,_y7){while(1){var _y8=E(_y6);if(!_y8._){var _y9=E(_y8.a);if(_y9==(-2147483648)){_y6=new T1(1,I_fromInt(-2147483648));continue;}else{var _ya=E(_y7);if(!_ya._){return new T1(0,_y9%_ya.a);}else{_y6=new T1(1,I_fromInt(_y9));_y7=_ya;continue;}}}else{var _yb=_y8.a,_yc=E(_y7);return (_yc._==0)?new T1(1,I_rem(_yb,I_fromInt(_yc.a))):new T1(1,I_rem(_yb,_yc.a));}}},_yd=function(_ye,_yf){if(!B(_30(_yf,_v4))){return new F(function(){return _y5(_ye,_yf);});}else{return E(_2V);}},_yg=function(_yh){return E(_yh);},_yi=function(_yj){return E(_yj);},_yk=function(_yl){var _ym=E(_yl);if(!_ym._){var _yn=E(_ym.a);return (_yn==(-2147483648))?E(_6a):(_yn<0)?new T1(0, -_yn):E(_ym);}else{var _yo=_ym.a;return (I_compareInt(_yo,0)>=0)?E(_ym):new T1(1,I_negate(_yo));}},_yp=new T1(0,0),_yq=new T1(0,-1),_yr=function(_ys){var _yt=E(_ys);if(!_yt._){var _yu=_yt.a;return (_yu>=0)?(E(_yu)==0)?E(_yp):E(_3M):E(_yq);}else{var _yv=I_compareInt(_yt.a,0);return (_yv<=0)?(E(_yv)==0)?E(_yp):E(_yq):E(_3M);}},_yw={_:0,a:_3b,b:_5w,c:_uE,d:_6b,e:_yk,f:_yr,g:_yi},_yx=function(_yy,_yz){var _yA=E(_yy);if(!_yA._){var _yB=_yA.a,_yC=E(_yz);return (_yC._==0)?_yB!=_yC.a:(I_compareInt(_yC.a,_yB)==0)?false:true;}else{var _yD=_yA.a,_yE=E(_yz);return (_yE._==0)?(I_compareInt(_yD,_yE.a)==0)?false:true:(I_compare(_yD,_yE.a)==0)?false:true;}},_yF=new T2(0,_30,_yx),_yG=function(_yH,_yI){return (!B(_5h(_yH,_yI)))?E(_yH):E(_yI);},_yJ=function(_yK,_yL){return (!B(_5h(_yK,_yL)))?E(_yL):E(_yK);},_yM={_:0,a:_yF,b:_1N,c:_3N,d:_5h,e:_3E,f:_wL,g:_yG,h:_yJ},_yN=function(_yO){return new T2(0,E(_yO),E(_mn));},_yP=new T3(0,_yw,_yM,_yN),_yQ={_:0,a:_yP,b:_xg,c:_xY,d:_yd,e:_xp,f:_xN,g:_y1,h:_xB,i:_yg},_yR=function(_yS){return E(E(_yS).b);},_yT=function(_yU){return E(E(_yU).g);},_yV=new T1(0,1),_yW=function(_yX,_yY,_yZ){var _z0=B(_yR(_yX)),_z1=B(_7i(_z0)),_z2=new T(function(){var _z3=new T(function(){var _z4=new T(function(){var _z5=new T(function(){return B(A3(_yT,_yX,_yQ,new T(function(){return B(A3(_91,_z0,_yY,_yZ));})));});return B(A2(_8R,_z1,_z5));}),_z6=new T(function(){return B(A2(_6K,_z1,new T(function(){return B(A2(_8R,_z1,_yV));})));});return B(A3(_7k,_z1,_z6,_z4));});return B(A3(_7k,_z1,_z3,_yZ));});return new F(function(){return A3(_6I,_z1,_yY,_z2);});},_z7=1.5707963267948966,_z8=function(_z9){return 0.2/Math.cos(B(_yW(_ww,_z9,_z7))-0.7853981633974483);},_za=4,_zb=0.3,_zc=new T(function(){var _zd=B(_p6(_z8,1.2,_qB,_qp,_qp,_qp,_qp,_qA,_zb,_za,_qp,_qp,_qw));return {_:0,a:E(_zd.a),b:E(_zd.b),c:E(_zd.c),d:E(_zd.d),e:E(_zd.e),f:E(_zd.f),g:E(_zd.g),h:_zd.h,i:_zd.i};}),_ze=new T2(1,_zc,_o),_zf=new T2(1,_qx,_ze),_zg=new T(function(){return B(unCStr("Negative range size"));}),_zh=new T(function(){return B(err(_zg));}),_zi=function(_){var _zj=B(_h5(_zf,0))-1|0,_zk=function(_zl){if(_zl>=0){var _zm=newArr(_zl,_hb),_zn=_zm,_zo=E(_zl);if(!_zo){return new T4(0,E(_qz),E(_zj),0,_zn);}else{var _zp=function(_zq,_zr,_){while(1){var _zs=E(_zq);if(!_zs._){return E(_);}else{var _=_zn[_zr]=_zs.a;if(_zr!=(_zo-1|0)){var _zt=_zr+1|0;_zq=_zs.b;_zr=_zt;continue;}else{return E(_);}}}},_=B((function(_zu,_zv,_zw,_){var _=_zn[_zw]=_zu;if(_zw!=(_zo-1|0)){return new F(function(){return _zp(_zv,_zw+1|0,_);});}else{return E(_);}})(_qx,_ze,0,_));return new T4(0,E(_qz),E(_zj),_zo,_zn);}}else{return E(_zh);}};if(0>_zj){return new F(function(){return _zk(0);});}else{return new F(function(){return _zk(_zj+1|0);});}},_zx=function(_zy){var _zz=B(A1(_zy,_));return E(_zz);},_zA=new T(function(){return B(_zx(_zi));}),_zB=function(_zC,_zD,_){var _zE=B(A1(_zC,_)),_zF=B(A1(_zD,_));return _zE;},_zG=function(_zH,_zI,_){var _zJ=B(A1(_zH,_)),_zK=B(A1(_zI,_));return new T(function(){return B(A1(_zJ,_zK));});},_zL=function(_zM,_zN,_){var _zO=B(A1(_zN,_));return _zM;},_zP=function(_zQ,_zR,_){var _zS=B(A1(_zR,_));return new T(function(){return B(A1(_zQ,_zS));});},_zT=new T2(0,_zP,_zL),_zU=function(_zV,_){return _zV;},_zW=function(_zX,_zY,_){var _zZ=B(A1(_zX,_));return new F(function(){return A1(_zY,_);});},_A0=new T5(0,_zT,_zU,_zG,_zW,_zB),_A1=function(_A2){var _A3=E(_A2);return (E(_A3.b)-E(_A3.a)|0)+1|0;},_A4=function(_A5,_A6){var _A7=E(_A5),_A8=E(_A6);return (E(_A7.a)>_A8)?false:_A8<=E(_A7.b);},_A9=function(_Aa,_Ab){var _Ac=jsShowI(_Aa);return new F(function(){return _f(fromJSStr(_Ac),_Ab);});},_Ad=function(_Ae,_Af,_Ag){if(_Af>=0){return new F(function(){return _A9(_Af,_Ag);});}else{if(_Ae<=6){return new F(function(){return _A9(_Af,_Ag);});}else{return new T2(1,_71,new T(function(){var _Ah=jsShowI(_Af);return B(_f(fromJSStr(_Ah),new T2(1,_70,_Ag)));}));}}},_Ai=function(_Aj){return new F(function(){return _Ad(0,E(_Aj),_o);});},_Ak=function(_Al,_Am,_An){return new F(function(){return _Ad(E(_Al),E(_Am),_An);});},_Ao=function(_Ap,_Aq){return new F(function(){return _Ad(0,E(_Ap),_Aq);});},_Ar=function(_As,_At){return new F(function(){return _2B(_Ao,_As,_At);});},_Au=new T3(0,_Ak,_Ai,_Ar),_Av=0,_Aw=function(_Ax,_Ay,_Az){return new F(function(){return A1(_Ax,new T2(1,_2y,new T(function(){return B(A1(_Ay,_Az));})));});},_AA=new T(function(){return B(unCStr("foldr1"));}),_AB=new T(function(){return B(_lN(_AA));}),_AC=function(_AD,_AE){var _AF=E(_AE);if(!_AF._){return E(_AB);}else{var _AG=_AF.a,_AH=E(_AF.b);if(!_AH._){return E(_AG);}else{return new F(function(){return A2(_AD,_AG,new T(function(){return B(_AC(_AD,_AH));}));});}}},_AI=new T(function(){return B(unCStr(" out of range "));}),_AJ=new T(function(){return B(unCStr("}.index: Index "));}),_AK=new T(function(){return B(unCStr("Ix{"));}),_AL=new T2(1,_70,_o),_AM=new T2(1,_70,_AL),_AN=0,_AO=function(_AP){return E(E(_AP).a);},_AQ=function(_AR,_AS,_AT,_AU,_AV){var _AW=new T(function(){var _AX=new T(function(){var _AY=new T(function(){var _AZ=new T(function(){var _B0=new T(function(){return B(A3(_AC,_Aw,new T2(1,new T(function(){return B(A3(_AO,_AT,_AN,_AU));}),new T2(1,new T(function(){return B(A3(_AO,_AT,_AN,_AV));}),_o)),_AM));});return B(_f(_AI,new T2(1,_71,new T2(1,_71,_B0))));});return B(A(_AO,[_AT,_Av,_AS,new T2(1,_70,_AZ)]));});return B(_f(_AJ,new T2(1,_71,_AY)));},1);return B(_f(_AR,_AX));},1);return new F(function(){return err(B(_f(_AK,_AW)));});},_B1=function(_B2,_B3,_B4,_B5,_B6){return new F(function(){return _AQ(_B2,_B3,_B6,_B4,_B5);});},_B7=function(_B8,_B9,_Ba,_Bb){var _Bc=E(_Ba);return new F(function(){return _B1(_B8,_B9,_Bc.a,_Bc.b,_Bb);});},_Bd=function(_Be,_Bf,_Bg,_Bh){return new F(function(){return _B7(_Bh,_Bg,_Bf,_Be);});},_Bi=new T(function(){return B(unCStr("Int"));}),_Bj=function(_Bk,_Bl){return new F(function(){return _Bd(_Au,_Bl,_Bk,_Bi);});},_Bm=function(_Bn,_Bo){var _Bp=E(_Bn),_Bq=E(_Bp.a),_Br=E(_Bo);if(_Bq>_Br){return new F(function(){return _Bj(_Br,_Bp);});}else{if(_Br>E(_Bp.b)){return new F(function(){return _Bj(_Br,_Bp);});}else{return _Br-_Bq|0;}}},_Bs=function(_Bt){var _Bu=E(_Bt);return new F(function(){return _sl(_Bu.a,_Bu.b);});},_Bv=function(_Bw){var _Bx=E(_Bw),_By=E(_Bx.a),_Bz=E(_Bx.b);return (_By>_Bz)?E(_Av):(_Bz-_By|0)+1|0;},_BA=function(_BB,_BC){return new F(function(){return _tK(_BC,E(_BB).a);});},_BD={_:0,a:_uA,b:_Bs,c:_Bm,d:_BA,e:_A4,f:_Bv,g:_A1},_BE=function(_BF,_BG){return new T2(1,_BF,_BG);},_BH=function(_BI,_BJ){var _BK=E(_BJ);return new T2(0,_BK.a,_BK.b);},_BL=function(_BM){return E(E(_BM).f);},_BN=function(_BO,_BP,_BQ){var _BR=E(_BP),_BS=_BR.a,_BT=_BR.b,_BU=function(_){var _BV=B(A2(_BL,_BO,_BR));if(_BV>=0){var _BW=newArr(_BV,_hb),_BX=_BW,_BY=E(_BV);if(!_BY){return new T(function(){return new T4(0,E(_BS),E(_BT),0,_BX);});}else{var _BZ=function(_C0,_C1,_){while(1){var _C2=E(_C0);if(!_C2._){return E(_);}else{var _=_BX[_C1]=_C2.a;if(_C1!=(_BY-1|0)){var _C3=_C1+1|0;_C0=_C2.b;_C1=_C3;continue;}else{return E(_);}}}},_=B(_BZ(_BQ,0,_));return new T(function(){return new T4(0,E(_BS),E(_BT),_BY,_BX);});}}else{return E(_zh);}};return new F(function(){return _zx(_BU);});},_C4=function(_C5,_C6,_C7,_C8){var _C9=new T(function(){var _Ca=E(_C8),_Cb=_Ca.c-1|0,_Cc=new T(function(){return B(A2(_cL,_C6,_o));});if(0<=_Cb){var _Cd=new T(function(){return B(_8X(_C6));}),_Ce=function(_Cf){var _Cg=new T(function(){var _Ch=new T(function(){return B(A1(_C7,new T(function(){return E(_Ca.d[_Cf]);})));});return B(A3(_95,_Cd,_BE,_Ch));});return new F(function(){return A3(_93,_C6,_Cg,new T(function(){if(_Cf!=_Cb){return B(_Ce(_Cf+1|0));}else{return E(_Cc);}}));});};return B(_Ce(0));}else{return E(_Cc);}}),_Ci=new T(function(){return B(_BH(_C5,_C8));});return new F(function(){return A3(_95,B(_8X(_C6)),function(_Cj){return new F(function(){return _BN(_C5,_Ci,_Cj);});},_C9);});},_Ck=function(_Cl){return E(E(_Cl).a);},_Cm=function(_Cn,_Co,_Cp,_Cq,_Cr){var _Cs=B(A2(_Ck,_Cn,E(_Cr)));return new F(function(){return A2(_Co,_Cp,new T2(1,_Cs,E(_Cq)));});},_Ct="outline",_Cu="polygon",_Cv=function(_Cw){return new F(function(){return _jt(new T2(1,new T2(0,_Cu,new T(function(){return E(_Cw).h;})),new T2(1,new T2(0,_Ct,new T(function(){return E(_Cw).i;})),_o)));});},_Cx=function(_Cy){return new F(function(){return _Cv(_Cy);});},_Cz=function(_CA){return new F(function(){return __lst2arr(B(_jT(_Cx,_CA)));});},_CB=new T2(0,_Cx,_Cz),_CC=function(_CD,_){var _CE=E(_CD);if(!_CE._){return _o;}else{var _CF=B(_CC(_CE.b,_));return new T2(1,_js,_CF);}},_CG=function(_CH,_){var _CI=__arr2lst(0,_CH);return new F(function(){return _CC(_CI,_);});},_CJ=function(_CK,_){return new F(function(){return _CG(E(_CK),_);});},_CL=function(_){return _js;},_CM=function(_CN,_){return new F(function(){return _CL(_);});},_CO=new T2(0,_CM,_CJ),_CP=function(_CQ){return E(E(_CQ).a);},_CR=function(_CS,_CT,_CU,_){var _CV=__apply(_CT,E(_CU));return new F(function(){return A3(_CP,_CS,_CV,_);});},_CW=function(_CX,_CY,_CZ,_){return new F(function(){return _CR(_CX,E(_CY),_CZ,_);});},_D0=function(_D1,_D2,_D3,_){return new F(function(){return _CW(_D1,_D2,_D3,_);});},_D4=function(_D5,_D6,_){return new F(function(){return _D0(_CO,_D5,_D6,_);});},_D7=new T(function(){return eval("drawObject");}),_D8=function(_D9){return new F(function(){return _Cm(_CB,_D4,_D7,_o,_D9);});},_Da=new T(function(){return eval("__strict(draw)");}),_Db=function(_Dc){return E(_Dc);},_Dd=function(_De){return E(_De);},_Df=function(_Dg,_Dh){return E(_Dh);},_Di=function(_Dj,_Dk){return E(_Dj);},_Dl=function(_Dm){return E(_Dm);},_Dn=new T2(0,_Dl,_Di),_Do=function(_Dp,_Dq){return E(_Dp);},_Dr=new T5(0,_Dn,_Dd,_Db,_Df,_Do),_Ds="d2z",_Dt="d2y",_Du="w2z",_Dv="w2y",_Dw="w2x",_Dx="w1z",_Dy="w1y",_Dz="w1x",_DA="d2x",_DB="d1z",_DC="d1y",_DD="d1x",_DE="c2y",_DF="c2x",_DG="c1y",_DH="c1x",_DI=function(_DJ,_){var _DK=__get(_DJ,E(_Dz)),_DL=__get(_DJ,E(_Dy)),_DM=__get(_DJ,E(_Dx)),_DN=__get(_DJ,E(_Dw)),_DO=__get(_DJ,E(_Dv)),_DP=__get(_DJ,E(_Du)),_DQ=__get(_DJ,E(_DH)),_DR=__get(_DJ,E(_DG)),_DS=__get(_DJ,E(_DF)),_DT=__get(_DJ,E(_DE)),_DU=__get(_DJ,E(_DD)),_DV=__get(_DJ,E(_DC)),_DW=__get(_DJ,E(_DB)),_DX=__get(_DJ,E(_DA)),_DY=__get(_DJ,E(_Dt)),_DZ=__get(_DJ,E(_Ds));return new T6(0,E(new T3(0,E(_DK),E(_DL),E(_DM))),E(new T3(0,E(_DN),E(_DO),E(_DP))),E(new T2(0,E(_DQ),E(_DR))),E(new T2(0,E(_DS),E(_DT))),E(new T3(0,E(_DU),E(_DV),E(_DW))),E(new T3(0,E(_DX),E(_DY),E(_DZ))));},_E0=function(_E1,_){var _E2=E(_E1);if(!_E2._){return _o;}else{var _E3=B(_DI(E(_E2.a),_)),_E4=B(_E0(_E2.b,_));return new T2(1,_E3,_E4);}},_E5=function(_E6,_E7,_){while(1){var _E8=B((function(_E9,_Ea,_){var _Eb=E(_E9);if(!_Eb._){return new T2(0,_js,_Ea);}else{var _Ec=B(A2(_Eb.a,_Ea,_));_E6=_Eb.b;_E7=new T(function(){return E(E(_Ec).b);});return __continue;}})(_E6,_E7,_));if(_E8!=__continue){return _E8;}}},_Ed=function(_Ee,_Ef,_Eg,_Eh,_Ei,_Ej,_Ek,_El,_Em){var _En=B(_7k(_Ee));return new T2(0,new T3(0,E(B(A1(B(A1(_En,_Ef)),_Ej))),E(B(A1(B(A1(_En,_Eg)),_Ek))),E(B(A1(B(A1(_En,_Eh)),_El)))),B(A1(B(A1(_En,_Ei)),_Em)));},_Eo=function(_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew,_Ex){var _Ey=B(_6I(_Ep));return new T2(0,new T3(0,E(B(A1(B(A1(_Ey,_Eq)),_Eu))),E(B(A1(B(A1(_Ey,_Er)),_Ev))),E(B(A1(B(A1(_Ey,_Es)),_Ew)))),B(A1(B(A1(_Ey,_Et)),_Ex)));},_Ez=1.0e-2,_EA=function(_EB,_EC,_ED,_EE,_EF,_EG,_EH,_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER){var _ES=B(_Ed(_ib,_EI,_EJ,_EK,_EL,_Ez,_Ez,_Ez,_Ez)),_ET=E(_ES.a),_EU=B(_Eo(_ib,_EE,_EF,_EG,_EH,_ET.a,_ET.b,_ET.c,_ES.b)),_EV=E(_EU.a);return new F(function(){return _oo(_EB,_EC,_ED,_EV.a,_EV.b,_EV.c,_EU.b,_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER);});},_EW=function(_EX){var _EY=E(_EX),_EZ=E(_EY.d),_F0=E(_EZ.a),_F1=E(_EY.e),_F2=E(_F1.a),_F3=E(_EY.f),_F4=B(_EA(_EY.a,_EY.b,_EY.c,_F0.a,_F0.b,_F0.c,_EZ.b,_F2.a,_F2.b,_F2.c,_F1.b,_F3.a,_F3.b,_F3.c,_EY.g,_EY.h,_EY.i));return {_:0,a:E(_F4.a),b:E(_F4.b),c:E(_F4.c),d:E(_F4.d),e:E(_F4.e),f:E(_F4.f),g:E(_F4.g),h:_F4.h,i:_F4.i};},_F5=function(_F6,_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe){var _Ff=B(_7i(B(_7g(_F6))));return new F(function(){return A3(_6I,_Ff,new T(function(){return B(_k6(_F6,_F7,_F8,_F9,_Fb,_Fc,_Fd));}),new T(function(){return B(A3(_7k,_Ff,_Fa,_Fe));}));});},_Fg=new T(function(){return B(unCStr("base"));}),_Fh=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fi=new T(function(){return B(unCStr("IOException"));}),_Fj=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fg,_Fh,_Fi),_Fk=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fj,_o,_o),_Fl=function(_Fm){return E(_Fk);},_Fn=function(_Fo){var _Fp=E(_Fo);return new F(function(){return _28(B(_26(_Fp.a)),_Fl,_Fp.b);});},_Fq=new T(function(){return B(unCStr(": "));}),_Fr=new T(function(){return B(unCStr(")"));}),_Fs=new T(function(){return B(unCStr(" ("));}),_Ft=new T(function(){return B(unCStr("interrupted"));}),_Fu=new T(function(){return B(unCStr("system error"));}),_Fv=new T(function(){return B(unCStr("unsatisified constraints"));}),_Fw=new T(function(){return B(unCStr("user error"));}),_Fx=new T(function(){return B(unCStr("permission denied"));}),_Fy=new T(function(){return B(unCStr("illegal operation"));}),_Fz=new T(function(){return B(unCStr("end of file"));}),_FA=new T(function(){return B(unCStr("resource exhausted"));}),_FB=new T(function(){return B(unCStr("resource busy"));}),_FC=new T(function(){return B(unCStr("does not exist"));}),_FD=new T(function(){return B(unCStr("already exists"));}),_FE=new T(function(){return B(unCStr("resource vanished"));}),_FF=new T(function(){return B(unCStr("timeout"));}),_FG=new T(function(){return B(unCStr("unsupported operation"));}),_FH=new T(function(){return B(unCStr("hardware fault"));}),_FI=new T(function(){return B(unCStr("inappropriate type"));}),_FJ=new T(function(){return B(unCStr("invalid argument"));}),_FK=new T(function(){return B(unCStr("failed"));}),_FL=new T(function(){return B(unCStr("protocol error"));}),_FM=function(_FN,_FO){switch(E(_FN)){case 0:return new F(function(){return _f(_FD,_FO);});break;case 1:return new F(function(){return _f(_FC,_FO);});break;case 2:return new F(function(){return _f(_FB,_FO);});break;case 3:return new F(function(){return _f(_FA,_FO);});break;case 4:return new F(function(){return _f(_Fz,_FO);});break;case 5:return new F(function(){return _f(_Fy,_FO);});break;case 6:return new F(function(){return _f(_Fx,_FO);});break;case 7:return new F(function(){return _f(_Fw,_FO);});break;case 8:return new F(function(){return _f(_Fv,_FO);});break;case 9:return new F(function(){return _f(_Fu,_FO);});break;case 10:return new F(function(){return _f(_FL,_FO);});break;case 11:return new F(function(){return _f(_FK,_FO);});break;case 12:return new F(function(){return _f(_FJ,_FO);});break;case 13:return new F(function(){return _f(_FI,_FO);});break;case 14:return new F(function(){return _f(_FH,_FO);});break;case 15:return new F(function(){return _f(_FG,_FO);});break;case 16:return new F(function(){return _f(_FF,_FO);});break;case 17:return new F(function(){return _f(_FE,_FO);});break;default:return new F(function(){return _f(_Ft,_FO);});}},_FP=new T(function(){return B(unCStr("}"));}),_FQ=new T(function(){return B(unCStr("{handle: "));}),_FR=function(_FS,_FT,_FU,_FV,_FW,_FX){var _FY=new T(function(){var _FZ=new T(function(){var _G0=new T(function(){var _G1=E(_FV);if(!_G1._){return E(_FX);}else{var _G2=new T(function(){return B(_f(_G1,new T(function(){return B(_f(_Fr,_FX));},1)));},1);return B(_f(_Fs,_G2));}},1);return B(_FM(_FT,_G0));}),_G3=E(_FU);if(!_G3._){return E(_FZ);}else{return B(_f(_G3,new T(function(){return B(_f(_Fq,_FZ));},1)));}}),_G4=E(_FW);if(!_G4._){var _G5=E(_FS);if(!_G5._){return E(_FY);}else{var _G6=E(_G5.a);if(!_G6._){var _G7=new T(function(){var _G8=new T(function(){return B(_f(_FP,new T(function(){return B(_f(_Fq,_FY));},1)));},1);return B(_f(_G6.a,_G8));},1);return new F(function(){return _f(_FQ,_G7);});}else{var _G9=new T(function(){var _Ga=new T(function(){return B(_f(_FP,new T(function(){return B(_f(_Fq,_FY));},1)));},1);return B(_f(_G6.a,_Ga));},1);return new F(function(){return _f(_FQ,_G9);});}}}else{return new F(function(){return _f(_G4.a,new T(function(){return B(_f(_Fq,_FY));},1));});}},_Gb=function(_Gc){var _Gd=E(_Gc);return new F(function(){return _FR(_Gd.a,_Gd.b,_Gd.c,_Gd.d,_Gd.f,_o);});},_Ge=function(_Gf,_Gg,_Gh){var _Gi=E(_Gg);return new F(function(){return _FR(_Gi.a,_Gi.b,_Gi.c,_Gi.d,_Gi.f,_Gh);});},_Gj=function(_Gk,_Gl){var _Gm=E(_Gk);return new F(function(){return _FR(_Gm.a,_Gm.b,_Gm.c,_Gm.d,_Gm.f,_Gl);});},_Gn=function(_Go,_Gp){return new F(function(){return _2B(_Gj,_Go,_Gp);});},_Gq=new T3(0,_Ge,_Gb,_Gn),_Gr=new T(function(){return new T5(0,_Fl,_Gq,_Gs,_Fn,_Gb);}),_Gs=function(_Gt){return new T2(0,_Gr,_Gt);},_Gu=__Z,_Gv=7,_Gw=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:78:3-9"));}),_Gx=new T6(0,_Gu,_Gv,_o,_Gw,_Gu,_Gu),_Gy=new T(function(){return B(_Gs(_Gx));}),_Gz=function(_){return new F(function(){return die(_Gy);});},_GA=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:77:3-9"));}),_GB=new T6(0,_Gu,_Gv,_o,_GA,_Gu,_Gu),_GC=new T(function(){return B(_Gs(_GB));}),_GD=function(_){return new F(function(){return die(_GC);});},_GE=function(_GF,_){return new T2(0,_o,_GF);},_GG=1,_GH=new T(function(){return B(unCStr(")"));}),_GI=function(_GJ,_GK){var _GL=new T(function(){var _GM=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_Ad(0,_GJ,_o)),_GH));})));},1);return B(_f(B(_Ad(0,_GK,_o)),_GM));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GL)));});},_GN=function(_GO,_GP){var _GQ=new T(function(){var _GR=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_Ad(0,_GP,_o)),_GH));})));},1);return B(_f(B(_Ad(0,_GO,_o)),_GR));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GQ)));});},_GS=0.6,_GT=function(_GU){var _GV=E(_GU);if(!_GV._){return E(_GE);}else{var _GW=new T(function(){return B(_GT(_GV.b));}),_GX=function(_GY){var _GZ=E(_GY);if(!_GZ._){return E(_GW);}else{var _H0=_GZ.a,_H1=new T(function(){return B(_GX(_GZ.b));}),_H2=new T(function(){return 0.1*E(E(_H0).e)/1.0e-2;}),_H3=new T(function(){var _H4=E(_H0);if(_H4.a!=_H4.b){return E(_GG);}else{return E(_GS);}}),_H5=function(_H6,_){var _H7=E(_H6),_H8=_H7.c,_H9=_H7.d,_Ha=E(_H7.a),_Hb=E(_H7.b),_Hc=E(_H0),_Hd=_Hc.a,_He=_Hc.b,_Hf=E(_Hc.c),_Hg=_Hf.b,_Hh=E(_Hf.a),_Hi=_Hh.a,_Hj=_Hh.b,_Hk=_Hh.c,_Hl=E(_Hc.d),_Hm=_Hl.b,_Hn=E(_Hl.a),_Ho=_Hn.a,_Hp=_Hn.b,_Hq=_Hn.c;if(_Ha>_Hd){return new F(function(){return _GD(_);});}else{if(_Hd>_Hb){return new F(function(){return _GD(_);});}else{if(_Ha>_He){return new F(function(){return _Gz(_);});}else{if(_He>_Hb){return new F(function(){return _Gz(_);});}else{var _Hr=_Hd-_Ha|0;if(0>_Hr){return new F(function(){return _GI(_H8,_Hr);});}else{if(_Hr>=_H8){return new F(function(){return _GI(_H8,_Hr);});}else{var _Hs=E(_H9[_Hr]),_Ht=E(_Hs.c),_Hu=_Ht.b,_Hv=E(_Ht.a),_Hw=_Hv.a,_Hx=_Hv.b,_Hy=_Hv.c,_Hz=E(_Hs.e),_HA=E(_Hz.a),_HB=B(_Ed(_ib,_Hi,_Hj,_Hk,_Hg,_Hw,_Hx,_Hy,_Hu)),_HC=E(_HB.a),_HD=B(_Ed(_ib,_HC.a,_HC.b,_HC.c,_HB.b,_Hi,_Hj,_Hk,_Hg)),_HE=E(_HD.a),_HF=_He-_Ha|0;if(0>_HF){return new F(function(){return _GN(_HF,_H8);});}else{if(_HF>=_H8){return new F(function(){return _GN(_HF,_H8);});}else{var _HG=E(_H9[_HF]),_HH=E(_HG.c),_HI=_HH.b,_HJ=E(_HH.a),_HK=_HJ.a,_HL=_HJ.b,_HM=_HJ.c,_HN=E(_HG.e),_HO=E(_HN.a),_HP=B(_Ed(_ib,_Ho,_Hp,_Hq,_Hm,_HK,_HL,_HM,_HI)),_HQ=E(_HP.a),_HR=B(_Ed(_ib,_HQ.a,_HQ.b,_HQ.c,_HP.b,_Ho,_Hp,_Hq,_Hm)),_HS=E(_HR.a),_HT=E(_HE.a)+E(_HE.b)+E(_HE.c)+E(_HD.b)+E(_HS.a)+E(_HS.b)+E(_HS.c)+E(_HR.b);if(!_HT){var _HU=B(A2(_H1,_H7,_));return new T2(0,new T2(1,_js,new T(function(){return E(E(_HU).a);})),new T(function(){return E(E(_HU).b);}));}else{var _HV=new T(function(){return  -((B(_F5(_iH,_HA.a,_HA.b,_HA.c,_Hz.b,_Hi,_Hj,_Hk,_Hg))-B(_F5(_iH,_HO.a,_HO.b,_HO.c,_HN.b,_Ho,_Hp,_Hq,_Hm))-E(_H2))/_HT);}),_HW=function(_HX,_HY,_HZ,_I0,_){var _I1=new T(function(){var _I2=function(_I3,_I4,_I5,_I6,_I7){if(_I3>_He){return E(_I7);}else{if(_He>_I4){return E(_I7);}else{var _I8=function(_){var _I9=newArr(_I5,_hb),_Ia=_I9,_Ib=function(_Ic,_){while(1){if(_Ic!=_I5){var _=_Ia[_Ic]=_I6[_Ic],_Id=_Ic+1|0;_Ic=_Id;continue;}else{return E(_);}}},_=B(_Ib(0,_)),_Ie=_He-_I3|0;if(0>_Ie){return new F(function(){return _GN(_Ie,_I5);});}else{if(_Ie>=_I5){return new F(function(){return _GN(_Ie,_I5);});}else{var _=_Ia[_Ie]=new T(function(){var _If=E(_I6[_Ie]),_Ig=E(_If.e),_Ih=E(_Ig.a),_Ii=B(_Ed(_ib,_HK,_HL,_HM,_HI,_Ho,_Hp,_Hq,_Hm)),_Ij=E(_Ii.a),_Ik=E(_HV)*E(_H3),_Il=B(_Ed(_ib,_Ij.a,_Ij.b,_Ij.c,_Ii.b,_Ik,_Ik,_Ik,_Ik)),_Im=E(_Il.a),_In=B(_Eo(_ib,_Ih.a,_Ih.b,_Ih.c,_Ig.b, -E(_Im.a), -E(_Im.b), -E(_Im.c), -E(_Il.b)));return {_:0,a:E(_If.a),b:E(_If.b),c:E(_If.c),d:E(_If.d),e:E(new T2(0,E(_In.a),E(_In.b))),f:E(_If.f),g:E(_If.g),h:_If.h,i:_If.i};});return new T4(0,E(_I3),E(_I4),_I5,_Ia);}}};return new F(function(){return _zx(_I8);});}}};if(_HX>_Hd){return B(_I2(_HX,_HY,_HZ,_I0,new T4(0,E(_HX),E(_HY),_HZ,_I0)));}else{if(_Hd>_HY){return B(_I2(_HX,_HY,_HZ,_I0,new T4(0,E(_HX),E(_HY),_HZ,_I0)));}else{var _Io=function(_){var _Ip=newArr(_HZ,_hb),_Iq=_Ip,_Ir=function(_Is,_){while(1){if(_Is!=_HZ){var _=_Iq[_Is]=_I0[_Is],_It=_Is+1|0;_Is=_It;continue;}else{return E(_);}}},_=B(_Ir(0,_)),_Iu=_Hd-_HX|0;if(0>_Iu){return new F(function(){return _GI(_HZ,_Iu);});}else{if(_Iu>=_HZ){return new F(function(){return _GI(_HZ,_Iu);});}else{var _=_Iq[_Iu]=new T(function(){var _Iv=E(_I0[_Iu]),_Iw=E(_Iv.e),_Ix=E(_Iw.a),_Iy=B(_Ed(_ib,_Hw,_Hx,_Hy,_Hu,_Hi,_Hj,_Hk,_Hg)),_Iz=E(_Iy.a),_IA=E(_HV)*E(_H3),_IB=B(_Ed(_ib,_Iz.a,_Iz.b,_Iz.c,_Iy.b,_IA,_IA,_IA,_IA)),_IC=E(_IB.a),_ID=B(_Eo(_ib,_Ix.a,_Ix.b,_Ix.c,_Iw.b,_IC.a,_IC.b,_IC.c,_IB.b));return {_:0,a:E(_Iv.a),b:E(_Iv.b),c:E(_Iv.c),d:E(_Iv.d),e:E(new T2(0,E(_ID.a),E(_ID.b))),f:E(_Iv.f),g:E(_Iv.g),h:_Iv.h,i:_Iv.i};});return new T4(0,E(_HX),E(_HY),_HZ,_Iq);}}},_IE=B(_zx(_Io));return B(_I2(E(_IE.a),E(_IE.b),_IE.c,_IE.d,_IE));}}});return new T2(0,_js,_I1);};if(!E(_Hc.f)){var _IF=B(_HW(_Ha,_Hb,_H8,_H9,_)),_IG=B(A2(_H1,new T(function(){return E(E(_IF).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IF).a);}),new T(function(){return E(E(_IG).a);})),new T(function(){return E(E(_IG).b);}));}else{if(E(_HV)<0){var _IH=B(A2(_H1,_H7,_));return new T2(0,new T2(1,_js,new T(function(){return E(E(_IH).a);})),new T(function(){return E(E(_IH).b);}));}else{var _II=B(_HW(_Ha,_Hb,_H8,_H9,_)),_IJ=B(A2(_H1,new T(function(){return E(E(_II).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_II).a);}),new T(function(){return E(E(_IJ).a);})),new T(function(){return E(E(_IJ).b);}));}}}}}}}}}}}};return E(_H5);}};return new F(function(){return _GX(_GV.a);});}},_IK=function(_,_IL){var _IM=new T(function(){return B(_GT(E(_IL).a));}),_IN=function(_IO){var _IP=E(_IO);return (_IP==1)?E(new T2(1,_IM,_o)):new T2(1,_IM,new T(function(){return B(_IN(_IP-1|0));}));},_IQ=B(_E5(B(_IN(5)),new T(function(){return E(E(_IL).b);}),_)),_IR=new T(function(){return B(_C4(_BD,_Dr,_EW,new T(function(){return E(E(_IQ).b);})));});return new T2(0,_js,_IR);},_IS=function(_IT,_IU,_IV,_IW,_IX){var _IY=B(_7i(B(_7g(_IT))));return new F(function(){return A3(_6I,_IY,new T(function(){return B(A3(_7k,_IY,_IU,_IW));}),new T(function(){return B(A3(_7k,_IY,_IV,_IX));}));});},_IZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));}),_J0=new T6(0,_Gu,_Gv,_o,_IZ,_Gu,_Gu),_J1=new T(function(){return B(_Gs(_J0));}),_J2=function(_){return new F(function(){return die(_J1);});},_J3=false,_J4=true,_J5=function(_J6){var _J7=E(_J6),_J8=E(_J7.b),_J9=E(_J7.e),_Ja=E(_J9.a),_Jb=E(_J7.g),_Jc=B(_l6(_iH,_J8.a,_J8.b,_J8.c,_Jb.a,_Jb.b,_Jb.c));return {_:0,a:E(_J7.a),b:E(_J8),c:E(_J7.c),d:E(_J7.d),e:E(new T2(0,E(new T3(0,E(_Ja.a)+E(_Jc.a)*1.0e-2,E(_Ja.b)+E(_Jc.b)*1.0e-2,E(_Ja.c)+E(_Jc.c)*1.0e-2)),E(_J9.b))),f:E(_J7.f),g:E(_Jb),h:_J7.h,i:_J7.i};},_Jd=new T(function(){return eval("collide");}),_Je=function(_Jf){var _Jg=E(_Jf);if(!_Jg._){return __Z;}else{return new F(function(){return _f(_Jg.a,new T(function(){return B(_Je(_Jg.b));},1));});}},_Jh=0,_Ji=new T3(0,E(_Jh),E(_Jh),E(_Jh)),_Jj=new T2(0,E(_Ji),E(_Jh)),_Jk=new T2(0,_iH,_jg),_Jl=new T(function(){return B(_gI(_Jk));}),_Jm=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_Jn=new T6(0,_Gu,_Gv,_o,_Jm,_Gu,_Gu),_Jo=new T(function(){return B(_Gs(_Jn));}),_Jp=function(_Jq,_){var _Jr=B(_C4(_BD,_Dr,_J5,_Jq)),_Js=E(_Jr.a),_Jt=E(_Jr.b);if(_Js<=_Jt){var _Ju=function(_Jv,_Jw,_){if(_Jv<=_Jt){var _Jx=E(_Jw),_Jy=function(_Jz,_JA,_JB,_JC,_JD,_){if(_JA>_Jv){return new F(function(){return die(_Jo);});}else{if(_Jv>_JB){return new F(function(){return die(_Jo);});}else{if(_JA>_Jz){return new F(function(){return _J2(_);});}else{if(_Jz>_JB){return new F(function(){return _J2(_);});}else{var _JE=_Jv-_JA|0;if(0>_JE){return new F(function(){return _GN(_JE,_JC);});}else{if(_JE>=_JC){return new F(function(){return _GN(_JE,_JC);});}else{var _JF=E(_JD[_JE]),_JG=_Jz-_JA|0;if(0>_JG){return new F(function(){return _GN(_JG,_JC);});}else{if(_JG>=_JC){return new F(function(){return _GN(_JG,_JC);});}else{var _JH=E(_JD[_JG]),_JI=__app2(E(_Jd),B(_jt(new T2(1,new T2(0,_Cu,_JF.h),new T2(1,new T2(0,_Ct,_JF.i),_o)))),B(_jt(new T2(1,new T2(0,_Cu,_JH.h),new T2(1,new T2(0,_Ct,_JH.i),_o))))),_JJ=__arr2lst(0,_JI),_JK=B(_E0(_JJ,_));if(_Jz!=_Jt){var _JL=B(_Jy(_Jz+1|0,_JA,_JB,_JC,_JD,_)),_JM=new T(function(){var _JN=new T(function(){return _Jv!=_Jz;}),_JO=function(_JP){var _JQ=E(_JP);if(!_JQ._){return __Z;}else{var _JR=_JQ.b,_JS=E(_JQ.a),_JT=E(_JS.b),_JU=E(_JS.a),_JV=E(_JS.c),_JW=_JV.a,_JX=_JV.b,_JY=E(_JS.e),_JZ=E(_JS.d),_K0=_JZ.a,_K1=_JZ.b,_K2=E(_JS.f),_K3=new T(function(){var _K4=B(_kg(_iH,_K2.a,_K2.b,_K2.c)),_K5=Math.sqrt(B(_IS(_iH,_K0,_K1,_K0,_K1)));return new T3(0,_K5*E(_K4.a),_K5*E(_K4.b),_K5*E(_K4.c));}),_K6=new T(function(){var _K7=B(_kg(_iH,_JY.a,_JY.b,_JY.c)),_K8=Math.sqrt(B(_IS(_iH,_JW,_JX,_JW,_JX)));return new T3(0,_K8*E(_K7.a),_K8*E(_K7.b),_K8*E(_K7.c));}),_K9=new T(function(){var _Ka=B(A1(_Jl,_JT)),_Kb=B(_kg(_iH,_Ka.a,_Ka.b,_Ka.c));return new T3(0,E(_Kb.a),E(_Kb.b),E(_Kb.c));}),_Kc=new T(function(){var _Kd=B(A1(_Jl,_JU)),_Ke=B(_kg(_iH,_Kd.a,_Kd.b,_Kd.c));return new T3(0,E(_Ke.a),E(_Ke.b),E(_Ke.c));}),_Kf=E(_JT.a)+ -E(_JU.a),_Kg=E(_JT.b)+ -E(_JU.b),_Kh=E(_JT.c)+ -E(_JU.c),_Ki=new T(function(){return Math.sqrt(B(_k6(_iH,_Kf,_Kg,_Kh,_Kf,_Kg,_Kh)));}),_Kj=new T(function(){var _Kk=1/E(_Ki);return new T3(0,_Kf*_Kk,_Kg*_Kk,_Kh*_Kk);});return (!E(_JN))?new T2(1,new T(function(){var _Kl=E(_Kj),_Km=E(_Kl.b),_Kn=E(_Kl.c),_Ko=E(_Kl.a),_Kp=E(_Kc),_Kq=E(_Kp.c),_Kr=E(_Kp.b),_Ks=E(_Kp.a),_Kt=E(_K6),_Ku=E(_Kt.c),_Kv=E(_Kt.b),_Kw=E(_Kt.a),_Kx=_Km*_Kq-_Kr*_Kn,_Ky=_Kn*_Ks-_Kq*_Ko,_Kz=_Ko*_Kr-_Ks*_Km,_KA=B(_k6(_iH,_Ky*_Ku-_Kv*_Kz,_Kz*_Kw-_Ku*_Kx,_Kx*_Kv-_Kw*_Ky,_Ks,_Kr,_Kq));return new T6(0,_Jv,_Jz,E(new T2(0,E(new T3(0,E(_Kx),E(_Ky),E(_Kz))),E(_KA))),E(_Jj),_Ki,_J3);}),new T2(1,new T(function(){var _KB=E(_Kj),_KC=E(_KB.b),_KD=E(_KB.c),_KE=E(_KB.a),_KF=E(_K9),_KG=E(_KF.c),_KH=E(_KF.b),_KI=E(_KF.a),_KJ=E(_K3),_KK=E(_KJ.c),_KL=E(_KJ.b),_KM=E(_KJ.a),_KN=_KC*_KG-_KH*_KD,_KO=_KD*_KI-_KG*_KE,_KP=_KE*_KH-_KI*_KC,_KQ=B(_k6(_iH,_KO*_KK-_KL*_KP,_KP*_KM-_KK*_KN,_KN*_KL-_KM*_KO,_KI,_KH,_KG));return new T6(0,_Jv,_Jz,E(_Jj),E(new T2(0,E(new T3(0,E(_KN),E(_KO),E(_KP))),E(_KQ))),_Ki,_J3);}),new T(function(){return B(_JO(_JR));}))):new T2(1,new T(function(){var _KR=E(_Kj),_KS=E(_KR.b),_KT=E(_KR.c),_KU=E(_KR.a),_KV=E(_Kc),_KW=_KV.a,_KX=_KV.b,_KY=_KV.c,_KZ=B(_l6(_iH,_KU,_KS,_KT,_KW,_KX,_KY)),_L0=E(_K6),_L1=E(_L0.c),_L2=E(_L0.b),_L3=E(_L0.a),_L4=B(_k6(_iH,_KS*_L1-_L2*_KT,_KT*_L3-_L1*_KU,_KU*_L2-_L3*_KS,_KW,_KX,_KY)),_L5=E(_K9),_L6=_L5.a,_L7=_L5.b,_L8=_L5.c,_L9=B(_l6(_iH,_KU,_KS,_KT,_L6,_L7,_L8)),_La=E(_K3),_Lb=E(_La.c),_Lc=E(_La.b),_Ld=E(_La.a),_Le=B(_k6(_iH,_KS*_Lb-_Lc*_KT,_KT*_Ld-_Lb*_KU,_KU*_Lc-_Ld*_KS,_L6,_L7,_L8));return new T6(0,_Jv,_Jz,E(new T2(0,E(new T3(0,E(_KZ.a),E(_KZ.b),E(_KZ.c))),E(_L4))),E(new T2(0,E(new T3(0,E(_L9.a),E(_L9.b),E(_L9.c))),E(_Le))),_Ki,_J4);}),new T(function(){return B(_JO(_JR));}));}};return B(_JO(_JK));});return new T2(0,new T2(1,_JM,new T(function(){return E(E(_JL).a);})),new T(function(){return E(E(_JL).b);}));}else{var _Lf=new T(function(){var _Lg=new T(function(){return _Jv!=_Jz;}),_Lh=function(_Li){var _Lj=E(_Li);if(!_Lj._){return __Z;}else{var _Lk=_Lj.b,_Ll=E(_Lj.a),_Lm=E(_Ll.b),_Ln=E(_Ll.a),_Lo=E(_Ll.c),_Lp=_Lo.a,_Lq=_Lo.b,_Lr=E(_Ll.e),_Ls=E(_Ll.d),_Lt=_Ls.a,_Lu=_Ls.b,_Lv=E(_Ll.f),_Lw=new T(function(){var _Lx=B(_kg(_iH,_Lv.a,_Lv.b,_Lv.c)),_Ly=Math.sqrt(B(_IS(_iH,_Lt,_Lu,_Lt,_Lu)));return new T3(0,_Ly*E(_Lx.a),_Ly*E(_Lx.b),_Ly*E(_Lx.c));}),_Lz=new T(function(){var _LA=B(_kg(_iH,_Lr.a,_Lr.b,_Lr.c)),_LB=Math.sqrt(B(_IS(_iH,_Lp,_Lq,_Lp,_Lq)));return new T3(0,_LB*E(_LA.a),_LB*E(_LA.b),_LB*E(_LA.c));}),_LC=new T(function(){var _LD=B(A1(_Jl,_Lm)),_LE=B(_kg(_iH,_LD.a,_LD.b,_LD.c));return new T3(0,E(_LE.a),E(_LE.b),E(_LE.c));}),_LF=new T(function(){var _LG=B(A1(_Jl,_Ln)),_LH=B(_kg(_iH,_LG.a,_LG.b,_LG.c));return new T3(0,E(_LH.a),E(_LH.b),E(_LH.c));}),_LI=E(_Lm.a)+ -E(_Ln.a),_LJ=E(_Lm.b)+ -E(_Ln.b),_LK=E(_Lm.c)+ -E(_Ln.c),_LL=new T(function(){return Math.sqrt(B(_k6(_iH,_LI,_LJ,_LK,_LI,_LJ,_LK)));}),_LM=new T(function(){var _LN=1/E(_LL);return new T3(0,_LI*_LN,_LJ*_LN,_LK*_LN);});return (!E(_Lg))?new T2(1,new T(function(){var _LO=E(_LM),_LP=E(_LO.b),_LQ=E(_LO.c),_LR=E(_LO.a),_LS=E(_LF),_LT=E(_LS.c),_LU=E(_LS.b),_LV=E(_LS.a),_LW=E(_Lz),_LX=E(_LW.c),_LY=E(_LW.b),_LZ=E(_LW.a),_M0=_LP*_LT-_LU*_LQ,_M1=_LQ*_LV-_LT*_LR,_M2=_LR*_LU-_LV*_LP,_M3=B(_k6(_iH,_M1*_LX-_LY*_M2,_M2*_LZ-_LX*_M0,_M0*_LY-_LZ*_M1,_LV,_LU,_LT));return new T6(0,_Jv,_Jz,E(new T2(0,E(new T3(0,E(_M0),E(_M1),E(_M2))),E(_M3))),E(_Jj),_LL,_J3);}),new T2(1,new T(function(){var _M4=E(_LM),_M5=E(_M4.b),_M6=E(_M4.c),_M7=E(_M4.a),_M8=E(_LC),_M9=E(_M8.c),_Ma=E(_M8.b),_Mb=E(_M8.a),_Mc=E(_Lw),_Md=E(_Mc.c),_Me=E(_Mc.b),_Mf=E(_Mc.a),_Mg=_M5*_M9-_Ma*_M6,_Mh=_M6*_Mb-_M9*_M7,_Mi=_M7*_Ma-_Mb*_M5,_Mj=B(_k6(_iH,_Mh*_Md-_Me*_Mi,_Mi*_Mf-_Md*_Mg,_Mg*_Me-_Mf*_Mh,_Mb,_Ma,_M9));return new T6(0,_Jv,_Jz,E(_Jj),E(new T2(0,E(new T3(0,E(_Mg),E(_Mh),E(_Mi))),E(_Mj))),_LL,_J3);}),new T(function(){return B(_Lh(_Lk));}))):new T2(1,new T(function(){var _Mk=E(_LM),_Ml=E(_Mk.b),_Mm=E(_Mk.c),_Mn=E(_Mk.a),_Mo=E(_LF),_Mp=_Mo.a,_Mq=_Mo.b,_Mr=_Mo.c,_Ms=B(_l6(_iH,_Mn,_Ml,_Mm,_Mp,_Mq,_Mr)),_Mt=E(_Lz),_Mu=E(_Mt.c),_Mv=E(_Mt.b),_Mw=E(_Mt.a),_Mx=B(_k6(_iH,_Ml*_Mu-_Mv*_Mm,_Mm*_Mw-_Mu*_Mn,_Mn*_Mv-_Mw*_Ml,_Mp,_Mq,_Mr)),_My=E(_LC),_Mz=_My.a,_MA=_My.b,_MB=_My.c,_MC=B(_l6(_iH,_Mn,_Ml,_Mm,_Mz,_MA,_MB)),_MD=E(_Lw),_ME=E(_MD.c),_MF=E(_MD.b),_MG=E(_MD.a),_MH=B(_k6(_iH,_Ml*_ME-_MF*_Mm,_Mm*_MG-_ME*_Mn,_Mn*_MF-_MG*_Ml,_Mz,_MA,_MB));return new T6(0,_Jv,_Jz,E(new T2(0,E(new T3(0,E(_Ms.a),E(_Ms.b),E(_Ms.c))),E(_Mx))),E(new T2(0,E(new T3(0,E(_MC.a),E(_MC.b),E(_MC.c))),E(_MH))),_LL,_J4);}),new T(function(){return B(_Lh(_Lk));}));}};return B(_Lh(_JK));});return new T2(0,new T2(1,_Lf,_o),new T4(0,E(_JA),E(_JB),_JC,_JD));}}}}}}}}}},_MI=B(_Jy(_Jv,E(_Jx.a),E(_Jx.b),_Jx.c,_Jx.d,_));if(_Jv!=_Jt){var _MJ=B(_Ju(_Jv+1|0,new T(function(){return E(E(_MI).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Je(E(_MI).a));}),new T(function(){return E(E(_MJ).a);})),new T(function(){return E(E(_MJ).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Je(E(_MI).a));}),_o),new T(function(){return E(E(_MI).b);}));}}else{if(_Jv!=_Jt){var _MK=B(_Ju(_Jv+1|0,_Jw,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_MK).a);})),new T(function(){return E(E(_MK).b);}));}else{return new T2(0,new T2(1,_o,_o),_Jw);}}},_ML=function(_MM,_MN,_MO,_MP,_MQ,_){if(_MM<=_Jt){var _MR=function(_MS,_MT,_MU,_MV,_MW,_){if(_MT>_MM){return new F(function(){return die(_Jo);});}else{if(_MM>_MU){return new F(function(){return die(_Jo);});}else{if(_MT>_MS){return new F(function(){return _J2(_);});}else{if(_MS>_MU){return new F(function(){return _J2(_);});}else{var _MX=_MM-_MT|0;if(0>_MX){return new F(function(){return _GN(_MX,_MV);});}else{if(_MX>=_MV){return new F(function(){return _GN(_MX,_MV);});}else{var _MY=E(_MW[_MX]),_MZ=_MS-_MT|0;if(0>_MZ){return new F(function(){return _GN(_MZ,_MV);});}else{if(_MZ>=_MV){return new F(function(){return _GN(_MZ,_MV);});}else{var _N0=E(_MW[_MZ]),_N1=__app2(E(_Jd),B(_jt(new T2(1,new T2(0,_Cu,_MY.h),new T2(1,new T2(0,_Ct,_MY.i),_o)))),B(_jt(new T2(1,new T2(0,_Cu,_N0.h),new T2(1,new T2(0,_Ct,_N0.i),_o))))),_N2=__arr2lst(0,_N1),_N3=B(_E0(_N2,_));if(_MS!=_Jt){var _N4=B(_MR(_MS+1|0,_MT,_MU,_MV,_MW,_)),_N5=new T(function(){var _N6=new T(function(){return _MM!=_MS;}),_N7=function(_N8){var _N9=E(_N8);if(!_N9._){return __Z;}else{var _Na=_N9.b,_Nb=E(_N9.a),_Nc=E(_Nb.b),_Nd=E(_Nb.a),_Ne=E(_Nb.c),_Nf=_Ne.a,_Ng=_Ne.b,_Nh=E(_Nb.e),_Ni=E(_Nb.d),_Nj=_Ni.a,_Nk=_Ni.b,_Nl=E(_Nb.f),_Nm=new T(function(){var _Nn=B(_kg(_iH,_Nl.a,_Nl.b,_Nl.c)),_No=Math.sqrt(B(_IS(_iH,_Nj,_Nk,_Nj,_Nk)));return new T3(0,_No*E(_Nn.a),_No*E(_Nn.b),_No*E(_Nn.c));}),_Np=new T(function(){var _Nq=B(_kg(_iH,_Nh.a,_Nh.b,_Nh.c)),_Nr=Math.sqrt(B(_IS(_iH,_Nf,_Ng,_Nf,_Ng)));return new T3(0,_Nr*E(_Nq.a),_Nr*E(_Nq.b),_Nr*E(_Nq.c));}),_Ns=new T(function(){var _Nt=B(A1(_Jl,_Nc)),_Nu=B(_kg(_iH,_Nt.a,_Nt.b,_Nt.c));return new T3(0,E(_Nu.a),E(_Nu.b),E(_Nu.c));}),_Nv=new T(function(){var _Nw=B(A1(_Jl,_Nd)),_Nx=B(_kg(_iH,_Nw.a,_Nw.b,_Nw.c));return new T3(0,E(_Nx.a),E(_Nx.b),E(_Nx.c));}),_Ny=E(_Nc.a)+ -E(_Nd.a),_Nz=E(_Nc.b)+ -E(_Nd.b),_NA=E(_Nc.c)+ -E(_Nd.c),_NB=new T(function(){return Math.sqrt(B(_k6(_iH,_Ny,_Nz,_NA,_Ny,_Nz,_NA)));}),_NC=new T(function(){var _ND=1/E(_NB);return new T3(0,_Ny*_ND,_Nz*_ND,_NA*_ND);});return (!E(_N6))?new T2(1,new T(function(){var _NE=E(_NC),_NF=E(_NE.b),_NG=E(_NE.c),_NH=E(_NE.a),_NI=E(_Nv),_NJ=E(_NI.c),_NK=E(_NI.b),_NL=E(_NI.a),_NM=E(_Np),_NN=E(_NM.c),_NO=E(_NM.b),_NP=E(_NM.a),_NQ=_NF*_NJ-_NK*_NG,_NR=_NG*_NL-_NJ*_NH,_NS=_NH*_NK-_NL*_NF,_NT=B(_k6(_iH,_NR*_NN-_NO*_NS,_NS*_NP-_NN*_NQ,_NQ*_NO-_NP*_NR,_NL,_NK,_NJ));return new T6(0,_MM,_MS,E(new T2(0,E(new T3(0,E(_NQ),E(_NR),E(_NS))),E(_NT))),E(_Jj),_NB,_J3);}),new T2(1,new T(function(){var _NU=E(_NC),_NV=E(_NU.b),_NW=E(_NU.c),_NX=E(_NU.a),_NY=E(_Ns),_NZ=E(_NY.c),_O0=E(_NY.b),_O1=E(_NY.a),_O2=E(_Nm),_O3=E(_O2.c),_O4=E(_O2.b),_O5=E(_O2.a),_O6=_NV*_NZ-_O0*_NW,_O7=_NW*_O1-_NZ*_NX,_O8=_NX*_O0-_O1*_NV,_O9=B(_k6(_iH,_O7*_O3-_O4*_O8,_O8*_O5-_O3*_O6,_O6*_O4-_O5*_O7,_O1,_O0,_NZ));return new T6(0,_MM,_MS,E(_Jj),E(new T2(0,E(new T3(0,E(_O6),E(_O7),E(_O8))),E(_O9))),_NB,_J3);}),new T(function(){return B(_N7(_Na));}))):new T2(1,new T(function(){var _Oa=E(_NC),_Ob=E(_Oa.b),_Oc=E(_Oa.c),_Od=E(_Oa.a),_Oe=E(_Nv),_Of=_Oe.a,_Og=_Oe.b,_Oh=_Oe.c,_Oi=B(_l6(_iH,_Od,_Ob,_Oc,_Of,_Og,_Oh)),_Oj=E(_Np),_Ok=E(_Oj.c),_Ol=E(_Oj.b),_Om=E(_Oj.a),_On=B(_k6(_iH,_Ob*_Ok-_Ol*_Oc,_Oc*_Om-_Ok*_Od,_Od*_Ol-_Om*_Ob,_Of,_Og,_Oh)),_Oo=E(_Ns),_Op=_Oo.a,_Oq=_Oo.b,_Or=_Oo.c,_Os=B(_l6(_iH,_Od,_Ob,_Oc,_Op,_Oq,_Or)),_Ot=E(_Nm),_Ou=E(_Ot.c),_Ov=E(_Ot.b),_Ow=E(_Ot.a),_Ox=B(_k6(_iH,_Ob*_Ou-_Ov*_Oc,_Oc*_Ow-_Ou*_Od,_Od*_Ov-_Ow*_Ob,_Op,_Oq,_Or));return new T6(0,_MM,_MS,E(new T2(0,E(new T3(0,E(_Oi.a),E(_Oi.b),E(_Oi.c))),E(_On))),E(new T2(0,E(new T3(0,E(_Os.a),E(_Os.b),E(_Os.c))),E(_Ox))),_NB,_J4);}),new T(function(){return B(_N7(_Na));}));}};return B(_N7(_N3));});return new T2(0,new T2(1,_N5,new T(function(){return E(E(_N4).a);})),new T(function(){return E(E(_N4).b);}));}else{var _Oy=new T(function(){var _Oz=new T(function(){return _MM!=_MS;}),_OA=function(_OB){var _OC=E(_OB);if(!_OC._){return __Z;}else{var _OD=_OC.b,_OE=E(_OC.a),_OF=E(_OE.b),_OG=E(_OE.a),_OH=E(_OE.c),_OI=_OH.a,_OJ=_OH.b,_OK=E(_OE.e),_OL=E(_OE.d),_OM=_OL.a,_ON=_OL.b,_OO=E(_OE.f),_OP=new T(function(){var _OQ=B(_kg(_iH,_OO.a,_OO.b,_OO.c)),_OR=Math.sqrt(B(_IS(_iH,_OM,_ON,_OM,_ON)));return new T3(0,_OR*E(_OQ.a),_OR*E(_OQ.b),_OR*E(_OQ.c));}),_OS=new T(function(){var _OT=B(_kg(_iH,_OK.a,_OK.b,_OK.c)),_OU=Math.sqrt(B(_IS(_iH,_OI,_OJ,_OI,_OJ)));return new T3(0,_OU*E(_OT.a),_OU*E(_OT.b),_OU*E(_OT.c));}),_OV=new T(function(){var _OW=B(A1(_Jl,_OF)),_OX=B(_kg(_iH,_OW.a,_OW.b,_OW.c));return new T3(0,E(_OX.a),E(_OX.b),E(_OX.c));}),_OY=new T(function(){var _OZ=B(A1(_Jl,_OG)),_P0=B(_kg(_iH,_OZ.a,_OZ.b,_OZ.c));return new T3(0,E(_P0.a),E(_P0.b),E(_P0.c));}),_P1=E(_OF.a)+ -E(_OG.a),_P2=E(_OF.b)+ -E(_OG.b),_P3=E(_OF.c)+ -E(_OG.c),_P4=new T(function(){return Math.sqrt(B(_k6(_iH,_P1,_P2,_P3,_P1,_P2,_P3)));}),_P5=new T(function(){var _P6=1/E(_P4);return new T3(0,_P1*_P6,_P2*_P6,_P3*_P6);});return (!E(_Oz))?new T2(1,new T(function(){var _P7=E(_P5),_P8=E(_P7.b),_P9=E(_P7.c),_Pa=E(_P7.a),_Pb=E(_OY),_Pc=E(_Pb.c),_Pd=E(_Pb.b),_Pe=E(_Pb.a),_Pf=E(_OS),_Pg=E(_Pf.c),_Ph=E(_Pf.b),_Pi=E(_Pf.a),_Pj=_P8*_Pc-_Pd*_P9,_Pk=_P9*_Pe-_Pc*_Pa,_Pl=_Pa*_Pd-_Pe*_P8,_Pm=B(_k6(_iH,_Pk*_Pg-_Ph*_Pl,_Pl*_Pi-_Pg*_Pj,_Pj*_Ph-_Pi*_Pk,_Pe,_Pd,_Pc));return new T6(0,_MM,_MS,E(new T2(0,E(new T3(0,E(_Pj),E(_Pk),E(_Pl))),E(_Pm))),E(_Jj),_P4,_J3);}),new T2(1,new T(function(){var _Pn=E(_P5),_Po=E(_Pn.b),_Pp=E(_Pn.c),_Pq=E(_Pn.a),_Pr=E(_OV),_Ps=E(_Pr.c),_Pt=E(_Pr.b),_Pu=E(_Pr.a),_Pv=E(_OP),_Pw=E(_Pv.c),_Px=E(_Pv.b),_Py=E(_Pv.a),_Pz=_Po*_Ps-_Pt*_Pp,_PA=_Pp*_Pu-_Ps*_Pq,_PB=_Pq*_Pt-_Pu*_Po,_PC=B(_k6(_iH,_PA*_Pw-_Px*_PB,_PB*_Py-_Pw*_Pz,_Pz*_Px-_Py*_PA,_Pu,_Pt,_Ps));return new T6(0,_MM,_MS,E(_Jj),E(new T2(0,E(new T3(0,E(_Pz),E(_PA),E(_PB))),E(_PC))),_P4,_J3);}),new T(function(){return B(_OA(_OD));}))):new T2(1,new T(function(){var _PD=E(_P5),_PE=E(_PD.b),_PF=E(_PD.c),_PG=E(_PD.a),_PH=E(_OY),_PI=_PH.a,_PJ=_PH.b,_PK=_PH.c,_PL=B(_l6(_iH,_PG,_PE,_PF,_PI,_PJ,_PK)),_PM=E(_OS),_PN=E(_PM.c),_PO=E(_PM.b),_PP=E(_PM.a),_PQ=B(_k6(_iH,_PE*_PN-_PO*_PF,_PF*_PP-_PN*_PG,_PG*_PO-_PP*_PE,_PI,_PJ,_PK)),_PR=E(_OV),_PS=_PR.a,_PT=_PR.b,_PU=_PR.c,_PV=B(_l6(_iH,_PG,_PE,_PF,_PS,_PT,_PU)),_PW=E(_OP),_PX=E(_PW.c),_PY=E(_PW.b),_PZ=E(_PW.a),_Q0=B(_k6(_iH,_PE*_PX-_PY*_PF,_PF*_PZ-_PX*_PG,_PG*_PY-_PZ*_PE,_PS,_PT,_PU));return new T6(0,_MM,_MS,E(new T2(0,E(new T3(0,E(_PL.a),E(_PL.b),E(_PL.c))),E(_PQ))),E(new T2(0,E(new T3(0,E(_PV.a),E(_PV.b),E(_PV.c))),E(_Q0))),_P4,_J4);}),new T(function(){return B(_OA(_OD));}));}};return B(_OA(_N3));});return new T2(0,new T2(1,_Oy,_o),new T4(0,E(_MT),E(_MU),_MV,_MW));}}}}}}}}}},_Q1=B(_MR(_MM,_MN,_MO,_MP,_MQ,_));if(_MM!=_Jt){var _Q2=B(_Ju(_MM+1|0,new T(function(){return E(E(_Q1).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Je(E(_Q1).a));}),new T(function(){return E(E(_Q2).a);})),new T(function(){return E(E(_Q2).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Je(E(_Q1).a));}),_o),new T(function(){return E(E(_Q1).b);}));}}else{if(_MM!=_Jt){var _Q3=B(_ML(_MM+1|0,_MN,_MO,_MP,_MQ,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Q3).a);})),new T(function(){return E(E(_Q3).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_MN),E(_MO),_MP,_MQ));}}},_Q4=B(_ML(_Js,_Js,_Jt,_Jr.c,_Jr.d,_));return new F(function(){return _IK(_,_Q4);});}else{return new F(function(){return _IK(_,new T2(0,_o,_Jr));});}},_Q5=new T(function(){return eval("__strict(refresh)");}),_Q6=function(_Q7,_){var _Q8=__app0(E(_Q5)),_Q9=__app0(E(_Da)),_Qa=B(A(_C4,[_BD,_A0,_D8,_Q7,_])),_Qb=B(_Jp(_Q7,_));return new T(function(){return E(E(_Qb).b);});},_Qc=function(_Qd,_){while(1){var _Qe=E(_Qd);if(!_Qe._){return _js;}else{var _Qf=_Qe.b,_Qg=E(_Qe.a);switch(_Qg._){case 0:var _Qh=B(A1(_Qg.a,_));_Qd=B(_f(_Qf,new T2(1,_Qh,_o)));continue;case 1:_Qd=B(_f(_Qf,_Qg.a));continue;default:_Qd=_Qf;continue;}}}},_Qi=function(_Qj,_Qk,_){var _Ql=E(_Qj);switch(_Ql._){case 0:var _Qm=B(A1(_Ql.a,_));return new F(function(){return _Qc(B(_f(_Qk,new T2(1,_Qm,_o))),_);});break;case 1:return new F(function(){return _Qc(B(_f(_Qk,_Ql.a)),_);});break;default:return new F(function(){return _Qc(_Qk,_);});}},_Qn=new T0(2),_Qo=function(_Qp){return new T0(2);},_Qq=function(_Qr,_Qs,_Qt){return function(_){var _Qu=E(_Qr),_Qv=rMV(_Qu),_Qw=E(_Qv);if(!_Qw._){var _Qx=new T(function(){var _Qy=new T(function(){return B(A1(_Qt,_js));});return B(_f(_Qw.b,new T2(1,new T2(0,_Qs,function(_Qz){return E(_Qy);}),_o)));}),_=wMV(_Qu,new T2(0,_Qw.a,_Qx));return _Qn;}else{var _QA=E(_Qw.a);if(!_QA._){var _=wMV(_Qu,new T2(0,_Qs,_o));return new T(function(){return B(A1(_Qt,_js));});}else{var _=wMV(_Qu,new T1(1,_QA.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Qt,_js));}),new T2(1,new T(function(){return B(A2(_QA.a,_Qs,_Qo));}),_o)));}}};},_QB=new T(function(){return E(_p5);}),_QC=new T(function(){return eval("window.requestAnimationFrame");}),_QD=new T1(1,_o),_QE=function(_QF,_QG){return function(_){var _QH=E(_QF),_QI=rMV(_QH),_QJ=E(_QI);if(!_QJ._){var _QK=_QJ.a,_QL=E(_QJ.b);if(!_QL._){var _=wMV(_QH,_QD);return new T(function(){return B(A1(_QG,_QK));});}else{var _QM=E(_QL.a),_=wMV(_QH,new T2(0,_QM.a,_QL.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QG,_QK));}),new T2(1,new T(function(){return B(A1(_QM.b,_Qo));}),_o)));}}else{var _QN=new T(function(){var _QO=function(_QP){var _QQ=new T(function(){return B(A1(_QG,_QP));});return function(_QR){return E(_QQ);};};return B(_f(_QJ.a,new T2(1,_QO,_o)));}),_=wMV(_QH,new T1(1,_QN));return _Qn;}};},_QS=function(_QT,_QU){return new T1(0,B(_QE(_QT,_QU)));},_QV=function(_QW,_QX){var _QY=new T(function(){return new T1(0,B(_Qq(_QW,_js,_Qo)));});return function(_){var _QZ=__createJSFunc(2,function(_R0,_){var _R1=B(_Qi(_QY,_o,_));return _QB;}),_R2=__app1(E(_QC),_QZ);return new T(function(){return B(_QS(_QW,_QX));});};},_R3=new T1(1,_o),_R4=function(_R5,_R6,_){var _R7=function(_){var _R8=nMV(_R5),_R9=_R8;return new T(function(){var _Ra=new T(function(){return B(_Rb(_));}),_Rc=function(_){var _Rd=rMV(_R9),_Re=B(A2(_R6,_Rd,_)),_=wMV(_R9,_Re),_Rf=function(_){var _Rg=nMV(_R3);return new T(function(){return new T1(0,B(_QV(_Rg,function(_Rh){return E(_Ra);})));});};return new T1(0,_Rf);},_Ri=new T(function(){return new T1(0,_Rc);}),_Rb=function(_Rj){return E(_Ri);};return B(_Rb(_));});};return new F(function(){return _Qi(new T1(0,_R7),_o,_);});},_Rk=function(_){var _Rl=__app2(E(_0),E(_7J),E(_h4));return new F(function(){return _R4(_zA,_Q6,_);});},_Rm=function(_){return new F(function(){return _Rk(_);});};
var hasteMain = function() {B(A(_Rm, [0]));};window.onload = hasteMain;