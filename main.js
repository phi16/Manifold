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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T(function(){return eval("compile");}),_i=function(_j){return E(E(_j).b);},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=E(_p);if(!_q._){return new F(function(){return A1(_o,_q.a);});}else{var _r=new T(function(){return B(_i(_n));}),_s=new T(function(){return B(_k(_n));}),_t=function(_u){var _v=E(_u);if(!_v._){return E(_s);}else{return new F(function(){return A2(_r,new T(function(){return B(_m(_n,_o,_v.a));}),new T(function(){return B(_t(_v.b));}));});}};return new F(function(){return _t(_q.a);});}},_w=function(_x){var _y=E(_x);if(!_y._){return __Z;}else{return new F(function(){return _0(_y.a,new T(function(){return B(_w(_y.b));},1));});}},_z=function(_A){return new F(function(){return _w(_A);});},_B=new T3(0,_4,_0,_z),_C=new T(function(){return B(unCStr(","));}),_D=new T1(0,_C),_E=new T(function(){return B(unCStr("pow("));}),_F=new T1(0,_E),_G=new T(function(){return B(unCStr(")"));}),_H=new T1(0,_G),_I=new T2(1,_H,_4),_J=function(_K,_L){return new T1(1,new T2(1,_F,new T2(1,_K,new T2(1,_D,new T2(1,_L,_I)))));},_M=new T(function(){return B(unCStr("acos("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_I)));},_Q=new T(function(){return B(unCStr("acosh("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_I)));},_U=new T(function(){return B(unCStr("asin("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_I)));},_Y=new T(function(){return B(unCStr("asinh("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_I)));},_12=new T(function(){return B(unCStr("atan("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_I)));},_16=new T(function(){return B(unCStr("atanh("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_I)));},_1a=new T(function(){return B(unCStr("cos("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_I)));},_1e=new T(function(){return B(unCStr("cosh("));}),_1f=new T1(0,_1e),_1g=function(_1h){return new T1(1,new T2(1,_1f,new T2(1,_1h,_I)));},_1i=new T(function(){return B(unCStr("exp("));}),_1j=new T1(0,_1i),_1k=function(_1l){return new T1(1,new T2(1,_1j,new T2(1,_1l,_I)));},_1m=new T(function(){return B(unCStr("log("));}),_1n=new T1(0,_1m),_1o=function(_1p){return new T1(1,new T2(1,_1n,new T2(1,_1p,_I)));},_1q=new T(function(){return B(unCStr(")/log("));}),_1r=new T1(0,_1q),_1s=function(_1t,_1u){return new T1(1,new T2(1,_1n,new T2(1,_1u,new T2(1,_1r,new T2(1,_1t,_I)))));},_1v=new T(function(){return B(unCStr("pi"));}),_1w=new T1(0,_1v),_1x=new T(function(){return B(unCStr("sin("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_I)));},_1B=new T(function(){return B(unCStr("sinh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_I)));},_1F=new T(function(){return B(unCStr("sqrt("));}),_1G=new T1(0,_1F),_1H=function(_1I){return new T1(1,new T2(1,_1G,new T2(1,_1I,_I)));},_1J=new T(function(){return B(unCStr("tan("));}),_1K=new T1(0,_1J),_1L=function(_1M){return new T1(1,new T2(1,_1K,new T2(1,_1M,_I)));},_1N=new T(function(){return B(unCStr("tanh("));}),_1O=new T1(0,_1N),_1P=function(_1Q){return new T1(1,new T2(1,_1O,new T2(1,_1Q,_I)));},_1R=new T(function(){return B(unCStr("("));}),_1S=new T1(0,_1R),_1T=new T(function(){return B(unCStr(")/("));}),_1U=new T1(0,_1T),_1V=function(_1W,_1X){return new T1(1,new T2(1,_1S,new T2(1,_1W,new T2(1,_1U,new T2(1,_1X,_I)))));},_1Y=new T1(0,1),_1Z=function(_20,_21){var _22=E(_20);if(!_22._){var _23=_22.a,_24=E(_21);if(!_24._){var _25=_24.a;return (_23!=_25)?(_23>_25)?2:0:1;}else{var _26=I_compareInt(_24.a,_23);return (_26<=0)?(_26>=0)?1:2:0;}}else{var _27=_22.a,_28=E(_21);if(!_28._){var _29=I_compareInt(_27,_28.a);return (_29>=0)?(_29<=0)?1:2:0;}else{var _2a=I_compare(_27,_28.a);return (_2a>=0)?(_2a<=0)?1:2:0;}}},_2b=new T(function(){return B(unCStr("base"));}),_2c=new T(function(){return B(unCStr("GHC.Exception"));}),_2d=new T(function(){return B(unCStr("ArithException"));}),_2e=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2b,_2c,_2d),_2f=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_4,_4),_2g=function(_2h){return E(_2f);},_2i=function(_2j){return E(E(_2j).a);},_2k=function(_2l,_2m,_2n){var _2o=B(A1(_2l,_)),_2p=B(A1(_2m,_)),_2q=hs_eqWord64(_2o.a,_2p.a);if(!_2q){return __Z;}else{var _2r=hs_eqWord64(_2o.b,_2p.b);return (!_2r)?__Z:new T1(1,_2n);}},_2s=function(_2t){var _2u=E(_2t);return new F(function(){return _2k(B(_2i(_2u.a)),_2g,_2u.b);});},_2v=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2w=new T(function(){return B(unCStr("denormal"));}),_2x=new T(function(){return B(unCStr("divide by zero"));}),_2y=new T(function(){return B(unCStr("loss of precision"));}),_2z=new T(function(){return B(unCStr("arithmetic underflow"));}),_2A=new T(function(){return B(unCStr("arithmetic overflow"));}),_2B=function(_2C,_2D){switch(E(_2C)){case 0:return new F(function(){return _0(_2A,_2D);});break;case 1:return new F(function(){return _0(_2z,_2D);});break;case 2:return new F(function(){return _0(_2y,_2D);});break;case 3:return new F(function(){return _0(_2x,_2D);});break;case 4:return new F(function(){return _0(_2w,_2D);});break;default:return new F(function(){return _0(_2v,_2D);});}},_2E=function(_2F){return new F(function(){return _2B(_2F,_4);});},_2G=function(_2H,_2I,_2J){return new F(function(){return _2B(_2I,_2J);});},_2K=44,_2L=93,_2M=91,_2N=function(_2O,_2P,_2Q){var _2R=E(_2P);if(!_2R._){return new F(function(){return unAppCStr("[]",_2Q);});}else{var _2S=new T(function(){var _2T=new T(function(){var _2U=function(_2V){var _2W=E(_2V);if(!_2W._){return E(new T2(1,_2L,_2Q));}else{var _2X=new T(function(){return B(A2(_2O,_2W.a,new T(function(){return B(_2U(_2W.b));})));});return new T2(1,_2K,_2X);}};return B(_2U(_2R.b));});return B(A2(_2O,_2R.a,_2T));});return new T2(1,_2M,_2S);}},_2Y=function(_2Z,_30){return new F(function(){return _2N(_2B,_2Z,_30);});},_31=new T3(0,_2G,_2E,_2Y),_32=new T(function(){return new T5(0,_2g,_31,_33,_2s,_2E);}),_33=function(_34){return new T2(0,_32,_34);},_35=3,_36=new T(function(){return B(_33(_35));}),_37=new T(function(){return die(_36);}),_38=function(_39,_3a){var _3b=E(_39);return (_3b._==0)?_3b.a*Math.pow(2,_3a):I_toNumber(_3b.a)*Math.pow(2,_3a);},_3c=function(_3d,_3e){var _3f=E(_3d);if(!_3f._){var _3g=_3f.a,_3h=E(_3e);return (_3h._==0)?_3g==_3h.a:(I_compareInt(_3h.a,_3g)==0)?true:false;}else{var _3i=_3f.a,_3j=E(_3e);return (_3j._==0)?(I_compareInt(_3i,_3j.a)==0)?true:false:(I_compare(_3i,_3j.a)==0)?true:false;}},_3k=function(_3l){var _3m=E(_3l);if(!_3m._){return E(_3m.a);}else{return new F(function(){return I_toInt(_3m.a);});}},_3n=function(_3o,_3p){while(1){var _3q=E(_3o);if(!_3q._){var _3r=_3q.a,_3s=E(_3p);if(!_3s._){var _3t=_3s.a,_3u=addC(_3r,_3t);if(!E(_3u.b)){return new T1(0,_3u.a);}else{_3o=new T1(1,I_fromInt(_3r));_3p=new T1(1,I_fromInt(_3t));continue;}}else{_3o=new T1(1,I_fromInt(_3r));_3p=_3s;continue;}}else{var _3v=E(_3p);if(!_3v._){_3o=_3q;_3p=new T1(1,I_fromInt(_3v.a));continue;}else{return new T1(1,I_add(_3q.a,_3v.a));}}}},_3w=function(_3x,_3y){while(1){var _3z=E(_3x);if(!_3z._){var _3A=E(_3z.a);if(_3A==(-2147483648)){_3x=new T1(1,I_fromInt(-2147483648));continue;}else{var _3B=E(_3y);if(!_3B._){var _3C=_3B.a;return new T2(0,new T1(0,quot(_3A,_3C)),new T1(0,_3A%_3C));}else{_3x=new T1(1,I_fromInt(_3A));_3y=_3B;continue;}}}else{var _3D=E(_3y);if(!_3D._){_3x=_3z;_3y=new T1(1,I_fromInt(_3D.a));continue;}else{var _3E=I_quotRem(_3z.a,_3D.a);return new T2(0,new T1(1,_3E.a),new T1(1,_3E.b));}}}},_3F=new T1(0,0),_3G=function(_3H,_3I){while(1){var _3J=E(_3H);if(!_3J._){_3H=new T1(1,I_fromInt(_3J.a));continue;}else{return new T1(1,I_shiftLeft(_3J.a,_3I));}}},_3K=function(_3L,_3M,_3N){if(!B(_3c(_3N,_3F))){var _3O=B(_3w(_3M,_3N)),_3P=_3O.a;switch(B(_1Z(B(_3G(_3O.b,1)),_3N))){case 0:return new F(function(){return _38(_3P,_3L);});break;case 1:if(!(B(_3k(_3P))&1)){return new F(function(){return _38(_3P,_3L);});}else{return new F(function(){return _38(B(_3n(_3P,_1Y)),_3L);});}break;default:return new F(function(){return _38(B(_3n(_3P,_1Y)),_3L);});}}else{return E(_37);}},_3Q=function(_3R,_3S){var _3T=E(_3R);if(!_3T._){var _3U=_3T.a,_3V=E(_3S);return (_3V._==0)?_3U>_3V.a:I_compareInt(_3V.a,_3U)<0;}else{var _3W=_3T.a,_3X=E(_3S);return (_3X._==0)?I_compareInt(_3W,_3X.a)>0:I_compare(_3W,_3X.a)>0;}},_3Y=new T1(0,1),_3Z=function(_40,_41){var _42=E(_40);if(!_42._){var _43=_42.a,_44=E(_41);return (_44._==0)?_43<_44.a:I_compareInt(_44.a,_43)>0;}else{var _45=_42.a,_46=E(_41);return (_46._==0)?I_compareInt(_45,_46.a)<0:I_compare(_45,_46.a)<0;}},_47=new T(function(){return B(unCStr("base"));}),_48=new T(function(){return B(unCStr("Control.Exception.Base"));}),_49=new T(function(){return B(unCStr("PatternMatchFail"));}),_4a=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_47,_48,_49),_4b=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4,_4),_4c=function(_4d){return E(_4b);},_4e=function(_4f){var _4g=E(_4f);return new F(function(){return _2k(B(_2i(_4g.a)),_4c,_4g.b);});},_4h=function(_4i){return E(E(_4i).a);},_4j=function(_4k){return new T2(0,_4l,_4k);},_4m=function(_4n,_4o){return new F(function(){return _0(E(_4n).a,_4o);});},_4p=function(_4q,_4r){return new F(function(){return _2N(_4m,_4q,_4r);});},_4s=function(_4t,_4u,_4v){return new F(function(){return _0(E(_4u).a,_4v);});},_4w=new T3(0,_4s,_4h,_4p),_4l=new T(function(){return new T5(0,_4c,_4w,_4j,_4e,_4h);}),_4x=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4y=function(_4z){return E(E(_4z).c);},_4A=function(_4B,_4C){return new F(function(){return die(new T(function(){return B(A2(_4y,_4C,_4B));}));});},_4D=function(_4E,_34){return new F(function(){return _4A(_4E,_34);});},_4F=function(_4G,_4H){var _4I=E(_4H);if(!_4I._){return new T2(0,_4,_4);}else{var _4J=_4I.a;if(!B(A1(_4G,_4J))){return new T2(0,_4,_4I);}else{var _4K=new T(function(){var _4L=B(_4F(_4G,_4I.b));return new T2(0,_4L.a,_4L.b);});return new T2(0,new T2(1,_4J,new T(function(){return E(E(_4K).a);})),new T(function(){return E(E(_4K).b);}));}}},_4M=32,_4N=new T(function(){return B(unCStr("\n"));}),_4O=function(_4P){return (E(_4P)==124)?false:true;},_4Q=function(_4R,_4S){var _4T=B(_4F(_4O,B(unCStr(_4R)))),_4U=_4T.a,_4V=function(_4W,_4X){var _4Y=new T(function(){var _4Z=new T(function(){return B(_0(_4S,new T(function(){return B(_0(_4X,_4N));},1)));});return B(unAppCStr(": ",_4Z));},1);return new F(function(){return _0(_4W,_4Y);});},_50=E(_4T.b);if(!_50._){return new F(function(){return _4V(_4U,_4);});}else{if(E(_50.a)==124){return new F(function(){return _4V(_4U,new T2(1,_4M,_50.b));});}else{return new F(function(){return _4V(_4U,_4);});}}},_51=function(_52){return new F(function(){return _4D(new T1(0,new T(function(){return B(_4Q(_52,_4x));})),_4l);});},_53=function(_54){var _55=function(_56,_57){while(1){if(!B(_3Z(_56,_54))){if(!B(_3Q(_56,_54))){if(!B(_3c(_56,_54))){return new F(function(){return _51("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_57);}}else{return _57-1|0;}}else{var _58=B(_3G(_56,1)),_59=_57+1|0;_56=_58;_57=_59;continue;}}};return new F(function(){return _55(_3Y,0);});},_5a=function(_5b){var _5c=E(_5b);if(!_5c._){var _5d=_5c.a>>>0;if(!_5d){return -1;}else{var _5e=function(_5f,_5g){while(1){if(_5f>=_5d){if(_5f<=_5d){if(_5f!=_5d){return new F(function(){return _51("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5g);}}else{return _5g-1|0;}}else{var _5h=imul(_5f,2)>>>0,_5i=_5g+1|0;_5f=_5h;_5g=_5i;continue;}}};return new F(function(){return _5e(1,0);});}}else{return new F(function(){return _53(_5c);});}},_5j=function(_5k){var _5l=E(_5k);if(!_5l._){var _5m=_5l.a>>>0;if(!_5m){return new T2(0,-1,0);}else{var _5n=function(_5o,_5p){while(1){if(_5o>=_5m){if(_5o<=_5m){if(_5o!=_5m){return new F(function(){return _51("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5p);}}else{return _5p-1|0;}}else{var _5q=imul(_5o,2)>>>0,_5r=_5p+1|0;_5o=_5q;_5p=_5r;continue;}}};return new T2(0,B(_5n(1,0)),(_5m&_5m-1>>>0)>>>0&4294967295);}}else{var _5s=_5l.a;return new T2(0,B(_5a(_5l)),I_compareInt(I_and(_5s,I_sub(_5s,I_fromInt(1))),0));}},_5t=function(_5u,_5v){var _5w=E(_5u);if(!_5w._){var _5x=_5w.a,_5y=E(_5v);return (_5y._==0)?_5x<=_5y.a:I_compareInt(_5y.a,_5x)>=0;}else{var _5z=_5w.a,_5A=E(_5v);return (_5A._==0)?I_compareInt(_5z,_5A.a)<=0:I_compare(_5z,_5A.a)<=0;}},_5B=function(_5C,_5D){while(1){var _5E=E(_5C);if(!_5E._){var _5F=_5E.a,_5G=E(_5D);if(!_5G._){return new T1(0,(_5F>>>0&_5G.a>>>0)>>>0&4294967295);}else{_5C=new T1(1,I_fromInt(_5F));_5D=_5G;continue;}}else{var _5H=E(_5D);if(!_5H._){_5C=_5E;_5D=new T1(1,I_fromInt(_5H.a));continue;}else{return new T1(1,I_and(_5E.a,_5H.a));}}}},_5I=function(_5J,_5K){while(1){var _5L=E(_5J);if(!_5L._){var _5M=_5L.a,_5N=E(_5K);if(!_5N._){var _5O=_5N.a,_5P=subC(_5M,_5O);if(!E(_5P.b)){return new T1(0,_5P.a);}else{_5J=new T1(1,I_fromInt(_5M));_5K=new T1(1,I_fromInt(_5O));continue;}}else{_5J=new T1(1,I_fromInt(_5M));_5K=_5N;continue;}}else{var _5Q=E(_5K);if(!_5Q._){_5J=_5L;_5K=new T1(1,I_fromInt(_5Q.a));continue;}else{return new T1(1,I_sub(_5L.a,_5Q.a));}}}},_5R=new T1(0,2),_5S=function(_5T,_5U){var _5V=E(_5T);if(!_5V._){var _5W=(_5V.a>>>0&(2<<_5U>>>0)-1>>>0)>>>0,_5X=1<<_5U>>>0;return (_5X<=_5W)?(_5X>=_5W)?1:2:0;}else{var _5Y=B(_5B(_5V,B(_5I(B(_3G(_5R,_5U)),_3Y)))),_5Z=B(_3G(_3Y,_5U));return (!B(_3Q(_5Z,_5Y)))?(!B(_3Z(_5Z,_5Y)))?1:2:0;}},_60=function(_61,_62){while(1){var _63=E(_61);if(!_63._){_61=new T1(1,I_fromInt(_63.a));continue;}else{return new T1(1,I_shiftRight(_63.a,_62));}}},_64=function(_65,_66,_67,_68){var _69=B(_5j(_68)),_6a=_69.a;if(!E(_69.b)){var _6b=B(_5a(_67));if(_6b<((_6a+_65|0)-1|0)){var _6c=_6a+(_65-_66|0)|0;if(_6c>0){if(_6c>_6b){if(_6c<=(_6b+1|0)){if(!E(B(_5j(_67)).b)){return 0;}else{return new F(function(){return _38(_1Y,_65-_66|0);});}}else{return 0;}}else{var _6d=B(_60(_67,_6c));switch(B(_5S(_67,_6c-1|0))){case 0:return new F(function(){return _38(_6d,_65-_66|0);});break;case 1:if(!(B(_3k(_6d))&1)){return new F(function(){return _38(_6d,_65-_66|0);});}else{return new F(function(){return _38(B(_3n(_6d,_1Y)),_65-_66|0);});}break;default:return new F(function(){return _38(B(_3n(_6d,_1Y)),_65-_66|0);});}}}else{return new F(function(){return _38(_67,(_65-_66|0)-_6c|0);});}}else{if(_6b>=_66){var _6e=B(_60(_67,(_6b+1|0)-_66|0));switch(B(_5S(_67,_6b-_66|0))){case 0:return new F(function(){return _38(_6e,((_6b-_6a|0)+1|0)-_66|0);});break;case 2:return new F(function(){return _38(B(_3n(_6e,_1Y)),((_6b-_6a|0)+1|0)-_66|0);});break;default:if(!(B(_3k(_6e))&1)){return new F(function(){return _38(_6e,((_6b-_6a|0)+1|0)-_66|0);});}else{return new F(function(){return _38(B(_3n(_6e,_1Y)),((_6b-_6a|0)+1|0)-_66|0);});}}}else{return new F(function(){return _38(_67, -_6a);});}}}else{var _6f=B(_5a(_67))-_6a|0,_6g=function(_6h){var _6i=function(_6j,_6k){if(!B(_5t(B(_3G(_6k,_66)),_6j))){return new F(function(){return _3K(_6h-_66|0,_6j,_6k);});}else{return new F(function(){return _3K((_6h-_66|0)+1|0,_6j,B(_3G(_6k,1)));});}};if(_6h>=_66){if(_6h!=_66){return new F(function(){return _6i(_67,new T(function(){return B(_3G(_68,_6h-_66|0));}));});}else{return new F(function(){return _6i(_67,_68);});}}else{return new F(function(){return _6i(new T(function(){return B(_3G(_67,_66-_6h|0));}),_68);});}};if(_65>_6f){return new F(function(){return _6g(_65);});}else{return new F(function(){return _6g(_6f);});}}},_6l=new T1(0,2147483647),_6m=new T(function(){return B(_3n(_6l,_3Y));}),_6n=function(_6o){var _6p=E(_6o);if(!_6p._){var _6q=E(_6p.a);return (_6q==(-2147483648))?E(_6m):new T1(0, -_6q);}else{return new T1(1,I_negate(_6p.a));}},_6r=new T(function(){return 0/0;}),_6s=new T(function(){return -1/0;}),_6t=new T(function(){return 1/0;}),_6u=0,_6v=function(_6w,_6x){if(!B(_3c(_6x,_3F))){if(!B(_3c(_6w,_3F))){if(!B(_3Z(_6w,_3F))){return new F(function(){return _64(-1021,53,_6w,_6x);});}else{return  -B(_64(-1021,53,B(_6n(_6w)),_6x));}}else{return E(_6u);}}else{return (!B(_3c(_6w,_3F)))?(!B(_3Z(_6w,_3F)))?E(_6t):E(_6s):E(_6r);}},_6y=function(_6z){return new T1(0,new T(function(){var _6A=E(_6z),_6B=jsShow(B(_6v(_6A.a,_6A.b)));return fromJSStr(_6B);}));},_6C=new T(function(){return B(unCStr("1./("));}),_6D=new T1(0,_6C),_6E=function(_6F){return new T1(1,new T2(1,_6D,new T2(1,_6F,_I)));},_6G=new T(function(){return B(unCStr(")+("));}),_6H=new T1(0,_6G),_6I=function(_6J,_6K){return new T1(1,new T2(1,_1S,new T2(1,_6J,new T2(1,_6H,new T2(1,_6K,_I)))));},_6L=new T(function(){return B(unCStr("-("));}),_6M=new T1(0,_6L),_6N=function(_6O){return new T1(1,new T2(1,_6M,new T2(1,_6O,_I)));},_6P=new T(function(){return B(unCStr(")*("));}),_6Q=new T1(0,_6P),_6R=function(_6S,_6T){return new T1(1,new T2(1,_1S,new T2(1,_6S,new T2(1,_6Q,new T2(1,_6T,_I)))));},_6U=function(_6V){return E(E(_6V).a);},_6W=function(_6X){return E(E(_6X).d);},_6Y=function(_6Z,_70){return new F(function(){return A3(_6U,_71,_6Z,new T(function(){return B(A2(_6W,_71,_70));}));});},_72=new T(function(){return B(unCStr("abs("));}),_73=new T1(0,_72),_74=function(_75){return new T1(1,new T2(1,_73,new T2(1,_75,_I)));},_76=function(_77){while(1){var _78=E(_77);if(!_78._){_77=new T1(1,I_fromInt(_78.a));continue;}else{return new F(function(){return I_toString(_78.a);});}}},_79=function(_7a,_7b){return new F(function(){return _0(fromJSStr(B(_76(_7a))),_7b);});},_7c=41,_7d=40,_7e=new T1(0,0),_7f=function(_7g,_7h,_7i){if(_7g<=6){return new F(function(){return _79(_7h,_7i);});}else{if(!B(_3Z(_7h,_7e))){return new F(function(){return _79(_7h,_7i);});}else{return new T2(1,_7d,new T(function(){return B(_0(fromJSStr(B(_76(_7h))),new T2(1,_7c,_7i)));}));}}},_7j=new T(function(){return B(unCStr("."));}),_7k=function(_7l){return new T1(0,new T(function(){return B(_0(B(_7f(0,_7l,_4)),_7j));}));},_7m=new T(function(){return B(unCStr("sign("));}),_7n=new T1(0,_7m),_7o=function(_7p){return new T1(1,new T2(1,_7n,new T2(1,_7p,_I)));},_71=new T(function(){return {_:0,a:_6I,b:_6Y,c:_6R,d:_6N,e:_74,f:_7o,g:_7k};}),_7q=new T4(0,_71,_1V,_6E,_6y),_7r={_:0,a:_7q,b:_1w,c:_1k,d:_1o,e:_1H,f:_J,g:_1s,h:_1z,i:_1c,j:_1L,k:_W,l:_O,m:_14,n:_1D,o:_1g,p:_1P,q:_10,r:_S,s:_18},_7s=function(_7t){return E(E(_7t).a);},_7u=function(_7v){return E(E(_7v).a);},_7w=function(_7x){return E(E(_7x).c);},_7y=function(_7z){return E(E(_7z).b);},_7A=function(_7B){return E(E(_7B).d);},_7C=new T1(0,1),_7D=new T1(0,2),_7E=new T2(0,E(_7C),E(_7D)),_7F=new T1(0,5),_7G=new T1(0,4),_7H=new T2(0,E(_7G),E(_7F)),_7I=function(_7J){return E(E(_7J).e);},_7K=function(_7L,_7M,_7N,_7O){var _7P=B(_7s(_7L)),_7Q=B(_7u(_7P)),_7R=new T(function(){var _7S=new T(function(){var _7T=new T(function(){var _7U=new T(function(){var _7V=new T(function(){var _7W=new T(function(){return B(A3(_6U,_7Q,new T(function(){return B(A3(_7w,_7Q,_7M,_7M));}),new T(function(){return B(A3(_7w,_7Q,_7O,_7O));})));});return B(A2(_7I,_7L,_7W));});return B(A3(_7y,_7Q,_7V,new T(function(){return B(A2(_7A,_7P,_7H));})));});return B(A3(_7w,_7Q,_7U,_7U));});return B(A3(_6U,_7Q,_7T,new T(function(){return B(A3(_7w,_7Q,_7N,_7N));})));});return B(A2(_7I,_7L,_7S));});return new F(function(){return A3(_7y,_7Q,_7R,new T(function(){return B(A2(_7A,_7P,_7E));}));});},_7X=new T(function(){return B(unCStr("z"));}),_7Y=new T1(0,_7X),_7Z=new T(function(){return B(unCStr("y"));}),_80=new T1(0,_7Z),_81=new T(function(){return B(unCStr("x"));}),_82=new T1(0,_81),_83=new T(function(){return B(_7K(_7r,_82,_80,_7Y));}),_84=function(_85){return E(_85);},_86=new T(function(){return toJSStr(B(_m(_B,_84,_83)));}),_87=function(_88,_89,_8a){var _8b=new T(function(){return B(_i(_88));}),_8c=new T(function(){return B(_k(_88));}),_8d=function(_8e){var _8f=E(_8e);if(!_8f._){return E(_8c);}else{return new F(function(){return A2(_8b,new T(function(){return B(_m(_88,_89,_8f.a));}),new T(function(){return B(_8d(_8f.b));}));});}};return new F(function(){return _8d(_8a);});},_8g=new T3(0,_82,_80,_7Y),_8h=function(_8i,_8j){var _8k=E(_8i);return E(_8j);},_8l=function(_8m,_8n){var _8o=E(_8m),_8p=E(_8n);return new T3(0,new T(function(){return B(A1(_8o.a,_8p.a));}),new T(function(){return B(A1(_8o.b,_8p.b));}),new T(function(){return B(A1(_8o.c,_8p.c));}));},_8q=function(_8r){return new T3(0,_8r,_8r,_8r);},_8s=function(_8t,_8u){var _8v=E(_8u);return new T3(0,_8t,_8t,_8t);},_8w=function(_8x,_8y){var _8z=E(_8y);return new T3(0,new T(function(){return B(A1(_8x,_8z.a));}),new T(function(){return B(A1(_8x,_8z.b));}),new T(function(){return B(A1(_8x,_8z.c));}));},_8A=new T2(0,_8w,_8s),_8B=function(_8C,_8D){var _8E=E(_8C),_8F=E(_8D);return new T3(0,_8E.a,_8E.b,_8E.c);},_8G=new T5(0,_8A,_8q,_8l,_8h,_8B),_8H=new T1(0,0),_8I=function(_8J){return E(E(_8J).g);},_8K=function(_8L){return new T3(0,new T3(0,new T(function(){return B(A2(_8I,_8L,_7C));}),new T(function(){return B(A2(_8I,_8L,_8H));}),new T(function(){return B(A2(_8I,_8L,_8H));})),new T3(0,new T(function(){return B(A2(_8I,_8L,_8H));}),new T(function(){return B(A2(_8I,_8L,_7C));}),new T(function(){return B(A2(_8I,_8L,_8H));})),new T3(0,new T(function(){return B(A2(_8I,_8L,_8H));}),new T(function(){return B(A2(_8I,_8L,_8H));}),new T(function(){return B(A2(_8I,_8L,_7C));})));},_8M=function(_8N){var _8O=B(_8K(_8N));return new T3(0,_8O.a,_8O.b,_8O.c);},_8P=function(_8Q){return E(E(_8Q).a);},_8R=function(_8S){return E(E(_8S).f);},_8T=function(_8U){return E(E(_8U).b);},_8V=function(_8W){return E(E(_8W).c);},_8X=function(_8Y){return E(E(_8Y).a);},_8Z=function(_90){return E(E(_90).d);},_91=function(_92,_93,_94,_95,_96){var _97=new T(function(){return E(E(_92).c);}),_98=new T(function(){var _99=E(_92).a,_9a=new T(function(){var _9b=new T(function(){return B(_7s(_97));}),_9c=new T(function(){return B(_7u(_9b));}),_9d=new T(function(){return B(A2(_8Z,_97,_93));}),_9e=new T(function(){return B(A3(_8R,_97,_93,_95));}),_9f=function(_9g,_9h){var _9i=new T(function(){var _9j=new T(function(){return B(A3(_8T,_9b,new T(function(){return B(A3(_7w,_9c,_95,_9g));}),_93));});return B(A3(_6U,_9c,_9j,new T(function(){return B(A3(_7w,_9c,_9h,_9d));})));});return new F(function(){return A3(_7w,_9c,_9e,_9i);});};return B(A3(_8X,B(_8P(_99)),_9f,_94));});return B(A3(_8V,_99,_9a,_96));});return new T2(0,new T(function(){return B(A3(_8R,_97,_93,_95));}),_98);},_9k=function(_9l,_9m,_9n,_9o){var _9p=E(_9n),_9q=E(_9o),_9r=B(_91(_9m,_9p.a,_9p.b,_9q.a,_9q.b));return new T2(0,_9r.a,_9r.b);},_9s=new T1(0,1),_9t=function(_9u){return E(E(_9u).l);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(_9w).c);}),_9A=new T(function(){var _9B=new T(function(){return B(_7s(_9z));}),_9C=new T(function(){var _9D=B(_7u(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_7y,_9D,new T(function(){return B(A2(_8I,_9D,_9s));}),new T(function(){return B(A3(_7w,_9D,_9x,_9x));})));});return B(A2(_7I,_9z,_9F));});return B(A2(_6W,_9D,_9E));});return B(A3(_8X,B(_8P(E(_9w).a)),function(_9G){return new F(function(){return A3(_8T,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9t,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(_9Q).c);}),_9U=new T(function(){var _9V=new T(function(){return B(_7s(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_7u(_9V));return B(A3(_7y,_9Y,new T(function(){return B(A3(_7w,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8I,_9Y,_9s));})));});return B(A2(_7I,_9T,_9X));});return B(A3(_8X,B(_8P(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8T,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(_a9).c);}),_ad=new T(function(){var _ae=new T(function(){return B(_7s(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_7u(_ae));return B(A3(_7y,_ah,new T(function(){return B(A2(_8I,_ah,_9s));}),new T(function(){return B(A3(_7w,_ah,_aa,_aa));})));});return B(A2(_7I,_ac,_ag));});return B(A3(_8X,B(_8P(E(_a9).a)),function(_ai){return new F(function(){return A3(_8T,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(_as).c);}),_aw=new T(function(){var _ax=new T(function(){return B(_7s(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_7u(_ax));return B(A3(_6U,_aA,new T(function(){return B(A3(_7w,_aA,_at,_at));}),new T(function(){return B(A2(_8I,_aA,_9s));})));});return B(A2(_7I,_av,_az));});return B(A3(_8X,B(_8P(E(_as).a)),function(_aB){return new F(function(){return A3(_8T,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(_aL).c);}),_aP=new T(function(){var _aQ=new T(function(){return B(_7s(_aO));}),_aR=new T(function(){var _aS=B(_7u(_aQ));return B(A3(_6U,_aS,new T(function(){return B(A2(_8I,_aS,_9s));}),new T(function(){return B(A3(_7w,_aS,_aM,_aM));})));});return B(A3(_8X,B(_8P(E(_aL).a)),function(_aT){return new F(function(){return A3(_8T,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(_b3).c);}),_b7=new T(function(){var _b8=new T(function(){return B(_7s(_b6));}),_b9=new T(function(){var _ba=B(_7u(_b8));return B(A3(_7y,_ba,new T(function(){return B(A2(_8I,_ba,_9s));}),new T(function(){return B(A3(_7w,_ba,_b4,_b4));})));});return B(A3(_8X,B(_8P(E(_b3).a)),function(_bb){return new F(function(){return A3(_8T,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(_bn).c);}),_br=new T(function(){var _bs=new T(function(){return B(_7u(new T(function(){return B(_7s(_bq));})));}),_bt=new T(function(){return B(A2(_6W,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8X,B(_8P(E(_bn).a)),function(_bu){return new F(function(){return A3(_7w,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(_bG).c);}),_bK=new T(function(){var _bL=new T(function(){return B(_7u(new T(function(){return B(_7s(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8X,B(_8P(E(_bG).a)),function(_bN){return new F(function(){return A3(_7w,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(_bX).c);}),_c1=new T(function(){var _c2=new T(function(){return B(_7u(new T(function(){return B(_7s(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8X,B(_8P(E(_bX).a)),function(_c4){return new F(function(){return A3(_7w,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(_cc).c);}),_cg=new T(function(){var _ch=new T(function(){return B(_7s(_cf));}),_ci=new T(function(){return B(_7u(_ch));}),_cj=new T(function(){return B(A3(_8T,_ch,new T(function(){return B(A2(_8I,_ci,_9s));}),_cd));});return B(A3(_8X,B(_8P(E(_cc).a)),function(_ck){return new F(function(){return A3(_7w,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8Z,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T(function(){return E(E(_ct).c);}));return new F(function(){return A3(_8T,_cs,new T(function(){var _cx=E(_cv),_cy=B(_cb(_cw,_cx.a,_cx.b));return new T2(0,_cy.a,_cy.b);}),new T(function(){var _cz=E(_cu),_cA=B(_cb(_cw,_cz.a,_cz.b));return new T2(0,_cA.a,_cA.b);}));});},_cB=new T1(0,0),_cC=function(_cD){return E(E(_cD).b);},_cE=function(_cF){return E(E(_cF).b);},_cG=function(_cH){var _cI=new T(function(){return E(E(_cH).c);}),_cJ=new T(function(){return B(A2(_cE,E(_cH).a,new T(function(){return B(A2(_8I,B(_7u(B(_7s(_cI)))),_cB));})));});return new T2(0,new T(function(){return B(_cC(_cI));}),_cJ);},_cK=function(_cL,_cM){var _cN=B(_cG(_cM));return new T2(0,_cN.a,_cN.b);},_cO=function(_cP,_cQ,_cR){var _cS=new T(function(){return E(E(_cP).c);}),_cT=new T(function(){var _cU=new T(function(){return B(_7u(new T(function(){return B(_7s(_cS));})));}),_cV=new T(function(){return B(A2(_bi,_cS,_cQ));});return B(A3(_8X,B(_8P(E(_cP).a)),function(_cW){return new F(function(){return A3(_7w,_cU,_cW,_cV);});},_cR));});return new T2(0,new T(function(){return B(A2(_bk,_cS,_cQ));}),_cT);},_cX=function(_cY,_cZ,_d0){var _d1=E(_d0),_d2=B(_cO(_cZ,_d1.a,_d1.b));return new T2(0,_d2.a,_d2.b);},_d3=function(_d4,_d5,_d6){var _d7=new T(function(){return E(E(_d4).c);}),_d8=new T(function(){var _d9=new T(function(){return B(_7u(new T(function(){return B(_7s(_d7));})));}),_da=new T(function(){return B(A2(_bB,_d7,_d5));});return B(A3(_8X,B(_8P(E(_d4).a)),function(_db){return new F(function(){return A3(_7w,_d9,_db,_da);});},_d6));});return new T2(0,new T(function(){return B(A2(_bD,_d7,_d5));}),_d8);},_dc=function(_dd,_de,_df){var _dg=E(_df),_dh=B(_d3(_de,_dg.a,_dg.b));return new T2(0,_dh.a,_dh.b);},_di=new T1(0,2),_dj=function(_dk,_dl,_dm){var _dn=new T(function(){return E(E(_dk).c);}),_do=new T(function(){var _dp=new T(function(){return B(_7s(_dn));}),_dq=new T(function(){return B(_7u(_dp));}),_dr=new T(function(){var _ds=new T(function(){return B(A3(_8T,_dp,new T(function(){return B(A2(_8I,_dq,_9s));}),new T(function(){return B(A2(_8I,_dq,_di));})));});return B(A3(_8T,_dp,_ds,new T(function(){return B(A2(_7I,_dn,_dl));})));});return B(A3(_8X,B(_8P(E(_dk).a)),function(_dt){return new F(function(){return A3(_7w,_dq,_dt,_dr);});},_dm));});return new T2(0,new T(function(){return B(A2(_7I,_dn,_dl));}),_do);},_du=function(_dv,_dw,_dx){var _dy=E(_dx),_dz=B(_dj(_dw,_dy.a,_dy.b));return new T2(0,_dz.a,_dz.b);},_dA=function(_dB){return E(E(_dB).j);},_dC=function(_dD,_dE,_dF){var _dG=new T(function(){return E(E(_dD).c);}),_dH=new T(function(){var _dI=new T(function(){return B(_7s(_dG));}),_dJ=new T(function(){var _dK=new T(function(){return B(A2(_bi,_dG,_dE));});return B(A3(_7w,B(_7u(_dI)),_dK,_dK));});return B(A3(_8X,B(_8P(E(_dD).a)),function(_dL){return new F(function(){return A3(_8T,_dI,_dL,_dJ);});},_dF));});return new T2(0,new T(function(){return B(A2(_dA,_dG,_dE));}),_dH);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dP),_dR=B(_dC(_dO,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);},_dS=function(_dT){return E(E(_dT).p);},_dU=function(_dV,_dW,_dX){var _dY=new T(function(){return E(E(_dV).c);}),_dZ=new T(function(){var _e0=new T(function(){return B(_7s(_dY));}),_e1=new T(function(){var _e2=new T(function(){return B(A2(_bB,_dY,_dW));});return B(A3(_7w,B(_7u(_e0)),_e2,_e2));});return B(A3(_8X,B(_8P(E(_dV).a)),function(_e3){return new F(function(){return A3(_8T,_e0,_e3,_e1);});},_dX));});return new T2(0,new T(function(){return B(A2(_dS,_dY,_dW));}),_dZ);},_e4=function(_e5,_e6,_e7){var _e8=E(_e7),_e9=B(_dU(_e6,_e8.a,_e8.b));return new T2(0,_e9.a,_e9.b);},_ea=function(_eb,_ec){return {_:0,a:_eb,b:new T(function(){return B(_cK(_eb,_ec));}),c:function(_ed){return new F(function(){return _c5(_eb,_ec,_ed);});},d:function(_ed){return new F(function(){return _cl(_eb,_ec,_ed);});},e:function(_ed){return new F(function(){return _du(_eb,_ec,_ed);});},f:function(_ee,_ed){return new F(function(){return _9k(_eb,_ec,_ee,_ed);});},g:function(_ee,_ed){return new F(function(){return _cr(_eb,_ec,_ee,_ed);});},h:function(_ed){return new F(function(){return _cX(_eb,_ec,_ed);});},i:function(_ed){return new F(function(){return _bv(_eb,_ec,_ed);});},j:function(_ed){return new F(function(){return _dM(_eb,_ec,_ed);});},k:function(_ed){return new F(function(){return _aj(_eb,_ec,_ed);});},l:function(_ed){return new F(function(){return _9H(_eb,_ec,_ed);});},m:function(_ed){return new F(function(){return _aU(_eb,_ec,_ed);});},n:function(_ed){return new F(function(){return _dc(_eb,_ec,_ed);});},o:function(_ed){return new F(function(){return _bO(_eb,_ec,_ed);});},p:function(_ed){return new F(function(){return _e4(_eb,_ec,_ed);});},q:function(_ed){return new F(function(){return _aC(_eb,_ec,_ed);});},r:function(_ed){return new F(function(){return _a0(_eb,_ec,_ed);});},s:function(_ed){return new F(function(){return _bc(_eb,_ec,_ed);});}};},_ef=function(_eg,_eh,_ei,_ej,_ek){var _el=new T(function(){return B(_7s(new T(function(){return E(E(_eg).c);})));}),_em=new T(function(){var _en=E(_eg).a,_eo=new T(function(){var _ep=new T(function(){return B(_7u(_el));}),_eq=new T(function(){return B(A3(_7w,_ep,_ej,_ej));}),_er=function(_es,_et){var _eu=new T(function(){return B(A3(_7y,_ep,new T(function(){return B(A3(_7w,_ep,_es,_ej));}),new T(function(){return B(A3(_7w,_ep,_eh,_et));})));});return new F(function(){return A3(_8T,_el,_eu,_eq);});};return B(A3(_8X,B(_8P(_en)),_er,_ei));});return B(A3(_8V,_en,_eo,_ek));});return new T2(0,new T(function(){return B(A3(_8T,_el,_eh,_ej));}),_em);},_ev=function(_ew,_ex,_ey,_ez){var _eA=E(_ey),_eB=E(_ez),_eC=B(_ef(_ex,_eA.a,_eA.b,_eB.a,_eB.b));return new T2(0,_eC.a,_eC.b);},_eD=function(_eE,_eF){var _eG=new T(function(){return B(_7s(new T(function(){return E(E(_eE).c);})));}),_eH=new T(function(){return B(A2(_cE,E(_eE).a,new T(function(){return B(A2(_8I,B(_7u(_eG)),_cB));})));});return new T2(0,new T(function(){return B(A2(_7A,_eG,_eF));}),_eH);},_eI=function(_eJ,_eK,_eL){var _eM=B(_eD(_eK,_eL));return new T2(0,_eM.a,_eM.b);},_eN=function(_eO,_eP,_eQ){var _eR=new T(function(){return B(_7s(new T(function(){return E(E(_eO).c);})));}),_eS=new T(function(){return B(_7u(_eR));}),_eT=new T(function(){var _eU=new T(function(){var _eV=new T(function(){return B(A3(_8T,_eR,new T(function(){return B(A2(_8I,_eS,_9s));}),new T(function(){return B(A3(_7w,_eS,_eP,_eP));})));});return B(A2(_6W,_eS,_eV));});return B(A3(_8X,B(_8P(E(_eO).a)),function(_eW){return new F(function(){return A3(_7w,_eS,_eW,_eU);});},_eQ));}),_eX=new T(function(){return B(A3(_8T,_eR,new T(function(){return B(A2(_8I,_eS,_9s));}),_eP));});return new T2(0,_eX,_eT);},_eY=function(_eZ,_f0,_f1){var _f2=E(_f1),_f3=B(_eN(_f0,_f2.a,_f2.b));return new T2(0,_f3.a,_f3.b);},_f4=function(_f5,_f6){return new T4(0,_f5,function(_ee,_ed){return new F(function(){return _ev(_f5,_f6,_ee,_ed);});},function(_ed){return new F(function(){return _eY(_f5,_f6,_ed);});},function(_ed){return new F(function(){return _eI(_f5,_f6,_ed);});});},_f7=function(_f8,_f9,_fa,_fb,_fc){var _fd=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_f8).c);})));})));}),_fe=new T(function(){var _ff=E(_f8).a,_fg=new T(function(){var _fh=function(_fi,_fj){return new F(function(){return A3(_6U,_fd,new T(function(){return B(A3(_7w,_fd,_f9,_fj));}),new T(function(){return B(A3(_7w,_fd,_fi,_fb));}));});};return B(A3(_8X,B(_8P(_ff)),_fh,_fa));});return B(A3(_8V,_ff,_fg,_fc));});return new T2(0,new T(function(){return B(A3(_7w,_fd,_f9,_fb));}),_fe);},_fk=function(_fl,_fm,_fn){var _fo=E(_fm),_fp=E(_fn),_fq=B(_f7(_fl,_fo.a,_fo.b,_fp.a,_fp.b));return new T2(0,_fq.a,_fq.b);},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_fs).c);})));})));}),_fy=new T(function(){var _fz=E(_fs).a,_fA=new T(function(){return B(A3(_8X,B(_8P(_fz)),new T(function(){return B(_6U(_fx));}),_fu));});return B(A3(_8V,_fz,_fA,_fw));});return new T2(0,new T(function(){return B(A3(_6U,_fx,_ft,_fv));}),_fy);},_fB=function(_fC,_fD,_fE){var _fF=E(_fD),_fG=E(_fE),_fH=B(_fr(_fC,_fF.a,_fF.b,_fG.a,_fG.b));return new T2(0,_fH.a,_fH.b);},_fI=function(_fJ,_fK,_fL){var _fM=B(_fN(_fJ));return new F(function(){return A3(_6U,_fM,_fK,new T(function(){return B(A2(_6W,_fM,_fL));}));});},_fO=function(_fP){return E(E(_fP).e);},_fQ=function(_fR){return E(E(_fR).f);},_fS=function(_fT,_fU,_fV){var _fW=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_fT).c);})));})));}),_fX=new T(function(){var _fY=new T(function(){return B(A2(_fQ,_fW,_fU));});return B(A3(_8X,B(_8P(E(_fT).a)),function(_fZ){return new F(function(){return A3(_7w,_fW,_fZ,_fY);});},_fV));});return new T2(0,new T(function(){return B(A2(_fO,_fW,_fU));}),_fX);},_g0=function(_g1,_g2){var _g3=E(_g2),_g4=B(_fS(_g1,_g3.a,_g3.b));return new T2(0,_g4.a,_g4.b);},_g5=function(_g6,_g7){var _g8=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_g6).c);})));})));}),_g9=new T(function(){return B(A2(_cE,E(_g6).a,new T(function(){return B(A2(_8I,_g8,_cB));})));});return new T2(0,new T(function(){return B(A2(_8I,_g8,_g7));}),_g9);},_ga=function(_gb,_gc){var _gd=B(_g5(_gb,_gc));return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg,_gh){var _gi=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_gf).c);})));})));}),_gj=new T(function(){return B(A3(_8X,B(_8P(E(_gf).a)),new T(function(){return B(_6W(_gi));}),_gh));});return new T2(0,new T(function(){return B(A2(_6W,_gi,_gg));}),_gj);},_gk=function(_gl,_gm){var _gn=E(_gm),_go=B(_ge(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr){var _gs=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_gq).c);})));})));}),_gt=new T(function(){return B(A2(_cE,E(_gq).a,new T(function(){return B(A2(_8I,_gs,_cB));})));});return new T2(0,new T(function(){return B(A2(_fQ,_gs,_gr));}),_gt);},_gu=function(_gv,_gw){var _gx=B(_gp(_gv,E(_gw).a));return new T2(0,_gx.a,_gx.b);},_fN=function(_gy){return {_:0,a:function(_ee,_ed){return new F(function(){return _fB(_gy,_ee,_ed);});},b:function(_ee,_ed){return new F(function(){return _fI(_gy,_ee,_ed);});},c:function(_ee,_ed){return new F(function(){return _fk(_gy,_ee,_ed);});},d:function(_ed){return new F(function(){return _gk(_gy,_ed);});},e:function(_ed){return new F(function(){return _g0(_gy,_ed);});},f:function(_ed){return new F(function(){return _gu(_gy,_ed);});},g:function(_ed){return new F(function(){return _ga(_gy,_ed);});}};},_gz=function(_gA){var _gB=new T3(0,_8G,_8M,_gA),_gC=new T(function(){return B(_ea(new T(function(){return B(_f4(new T(function(){return B(_fN(_gB));}),_gB));}),_gB));}),_gD=new T(function(){return B(_7u(new T(function(){return B(_7s(_gA));})));});return function(_gE){var _gF=E(_gE),_gG=B(_8K(_gD));return E(B(_7K(_gC,new T2(0,_gF.a,_gG.a),new T2(0,_gF.b,_gG.b),new T2(0,_gF.c,_gG.c))).b);};},_gH=new T(function(){return B(_gz(_7r));}),_gI=function(_gJ,_gK){var _gL=E(_gK);return (_gL._==0)?__Z:new T2(1,_gJ,new T2(1,_gL.a,new T(function(){return B(_gI(_gJ,_gL.b));})));},_gM=new T(function(){var _gN=B(A1(_gH,_8g));return new T2(1,_gN.a,new T(function(){return B(_gI(_D,new T2(1,_gN.b,new T2(1,_gN.c,_4))));}));}),_gO=new T1(1,_gM),_gP=new T2(1,_gO,_I),_gQ=new T(function(){return B(unCStr("vec3("));}),_gR=new T1(0,_gQ),_gS=new T2(1,_gR,_gP),_gT=new T(function(){return toJSStr(B(_87(_B,_84,_gS)));}),_gU=function(_gV,_gW,_gX){return new F(function(){return A1(_gV,function(_gY){return new F(function(){return A2(_gW,_gY,_gX);});});});},_gZ=function(_h0,_h1,_h2){var _h3=function(_h4){var _h5=new T(function(){return B(A1(_h2,_h4));});return new F(function(){return A1(_h1,function(_h6){return E(_h5);});});};return new F(function(){return A1(_h0,_h3);});},_h7=function(_h8,_h9,_ha){var _hb=new T(function(){return B(A1(_h9,function(_hc){return new F(function(){return A1(_ha,_hc);});}));});return new F(function(){return A1(_h8,function(_hd){return E(_hb);});});},_he=function(_hf,_hg,_hh){var _hi=function(_hj){var _hk=function(_hl){return new F(function(){return A1(_hh,new T(function(){return B(A1(_hj,_hl));}));});};return new F(function(){return A1(_hg,_hk);});};return new F(function(){return A1(_hf,_hi);});},_hm=function(_hn,_ho){return new F(function(){return A1(_ho,_hn);});},_hp=function(_hq,_hr,_hs){var _ht=new T(function(){return B(A1(_hs,_hq));});return new F(function(){return A1(_hr,function(_hu){return E(_ht);});});},_hv=function(_hw,_hx,_hy){var _hz=function(_hA){return new F(function(){return A1(_hy,new T(function(){return B(A1(_hw,_hA));}));});};return new F(function(){return A1(_hx,_hz);});},_hB=new T2(0,_hv,_hp),_hC=new T5(0,_hB,_hm,_he,_h7,_gZ),_hD=function(_hE){return E(E(_hE).b);},_hF=function(_hG,_hH){return new F(function(){return A3(_hD,_hI,_hG,function(_hJ){return E(_hH);});});},_hK=function(_hL){return new F(function(){return err(_hL);});},_hI=new T(function(){return new T5(0,_hC,_gU,_hF,_hm,_hK);}),_hM=function(_hN){return new T0(2);},_hO=function(_hP){var _hQ=new T(function(){return B(A1(_hP,_hM));}),_hR=function(_hS){return new T1(1,new T2(1,new T(function(){return B(A1(_hS,_5));}),new T2(1,_hQ,_4)));};return E(_hR);},_hT=new T3(0,_hI,_84,_hO),_hU=0,_hV=1,_hW=new T3(0,_hU,_hU,_hV),_hX=function(_hY){var _hZ=E(_hY);return new F(function(){return Math.log(_hZ+(_hZ+1)*Math.sqrt((_hZ-1)/(_hZ+1)));});},_i0=function(_i1){var _i2=E(_i1);return new F(function(){return Math.log(_i2+Math.sqrt(1+_i2*_i2));});},_i3=function(_i4){var _i5=E(_i4);return 0.5*Math.log((1+_i5)/(1-_i5));},_i6=function(_i7,_i8){return Math.log(E(_i8))/Math.log(E(_i7));},_i9=3.141592653589793,_ia=function(_ib){var _ic=E(_ib);return new F(function(){return _6v(_ic.a,_ic.b);});},_id=function(_ie){return 1/E(_ie);},_if=function(_ig){var _ih=E(_ig),_ii=E(_ih);return (_ii==0)?E(_6u):(_ii<=0)? -_ii:E(_ih);},_ij=function(_ik){var _il=E(_ik);if(!_il._){return _il.a;}else{return new F(function(){return I_toNumber(_il.a);});}},_im=function(_in){return new F(function(){return _ij(_in);});},_io=1,_ip=-1,_iq=function(_ir){var _is=E(_ir);return (_is<=0)?(_is>=0)?E(_is):E(_ip):E(_io);},_it=function(_iu,_iv){return E(_iu)-E(_iv);},_iw=function(_ix){return  -E(_ix);},_iy=function(_iz,_iA){return E(_iz)+E(_iA);},_iB=function(_iC,_iD){return E(_iC)*E(_iD);},_iE={_:0,a:_iy,b:_it,c:_iB,d:_iw,e:_if,f:_iq,g:_im},_iF=function(_iG,_iH){return E(_iG)/E(_iH);},_iI=new T4(0,_iE,_iF,_id,_ia),_iJ=function(_iK){return new F(function(){return Math.acos(E(_iK));});},_iL=function(_iM){return new F(function(){return Math.asin(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.atan(E(_iO));});},_iP=function(_iQ){return new F(function(){return Math.cos(E(_iQ));});},_iR=function(_iS){return new F(function(){return cosh(E(_iS));});},_iT=function(_iU){return new F(function(){return Math.exp(E(_iU));});},_iV=function(_iW){return new F(function(){return Math.log(E(_iW));});},_iX=function(_iY,_iZ){return new F(function(){return Math.pow(E(_iY),E(_iZ));});},_j0=function(_j1){return new F(function(){return Math.sin(E(_j1));});},_j2=function(_j3){return new F(function(){return sinh(E(_j3));});},_j4=function(_j5){return new F(function(){return Math.sqrt(E(_j5));});},_j6=function(_j7){return new F(function(){return Math.tan(E(_j7));});},_j8=function(_j9){return new F(function(){return tanh(E(_j9));});},_ja={_:0,a:_iI,b:_i9,c:_iT,d:_iV,e:_j4,f:_iX,g:_i6,h:_j0,i:_iP,j:_j6,k:_iL,l:_iJ,m:_iN,n:_j2,o:_iR,p:_j8,q:_i0,r:_hX,s:_i3},_jb=function(_jc,_jd,_je,_jf,_jg,_jh,_ji){var _jj=B(_7u(B(_7s(_jc)))),_jk=new T(function(){return B(A3(_6U,_jj,new T(function(){return B(A3(_7w,_jj,_jd,_jg));}),new T(function(){return B(A3(_7w,_jj,_je,_jh));})));});return new F(function(){return A3(_6U,_jj,_jk,new T(function(){return B(A3(_7w,_jj,_jf,_ji));}));});},_jl=function(_jm,_jn,_jo,_jp){var _jq=new T(function(){return B(_7s(_jm));}),_jr=new T(function(){return B(A2(_7I,_jm,new T(function(){return B(_jb(_jm,_jn,_jo,_jp,_jn,_jo,_jp));})));});return new T3(0,new T(function(){return B(A3(_8T,_jq,_jn,_jr));}),new T(function(){return B(A3(_8T,_jq,_jo,_jr));}),new T(function(){return B(A3(_8T,_jq,_jp,_jr));}));},_js=0.2,_jt=new T(function(){var _ju=B(_jl(_ja,_hU,_hV,_js));return new T3(0,_ju.a,_ju.b,_ju.c);}),_jv=-1.3,_jw=new T3(0,_jv,_hU,_hU),_jx=new T3(0,_jw,_jt,_hW),_jy=function(_jz,_jA){return (E(_jz)!=E(_jA))?true:false;},_jB=function(_jC,_jD){return E(_jC)==E(_jD);},_jE=new T2(0,_jB,_jy),_jF=function(_jG,_jH){return E(_jG)<E(_jH);},_jI=function(_jJ,_jK){return E(_jJ)<=E(_jK);},_jL=function(_jM,_jN){return E(_jM)>E(_jN);},_jO=function(_jP,_jQ){return E(_jP)>=E(_jQ);},_jR=function(_jS,_jT){var _jU=E(_jS),_jV=E(_jT);return (_jU>=_jV)?(_jU!=_jV)?2:1:0;},_jW=function(_jX,_jY){var _jZ=E(_jX),_k0=E(_jY);return (_jZ>_k0)?E(_jZ):E(_k0);},_k1=function(_k2,_k3){var _k4=E(_k2),_k5=E(_k3);return (_k4>_k5)?E(_k5):E(_k4);},_k6={_:0,a:_jE,b:_jR,c:_jF,d:_jI,e:_jL,f:_jO,g:_jW,h:_k1},_k7=function(_k8){var _k9=I_decodeDouble(_k8);return new T2(0,new T1(1,_k9.b),_k9.a);},_ka=function(_kb){return new T1(0,_kb);},_kc=function(_kd){var _ke=hs_intToInt64(2147483647),_kf=hs_leInt64(_kd,_ke);if(!_kf){return new T1(1,I_fromInt64(_kd));}else{var _kg=hs_intToInt64(-2147483648),_kh=hs_geInt64(_kd,_kg);if(!_kh){return new T1(1,I_fromInt64(_kd));}else{var _ki=hs_int64ToInt(_kd);return new F(function(){return _ka(_ki);});}}},_kj=new T(function(){var _kk=newByteArr(256),_kl=_kk,_=_kl["v"]["i8"][0]=8,_km=function(_kn,_ko,_kp,_){while(1){if(_kp>=256){if(_kn>=256){return E(_);}else{var _kq=imul(2,_kn)|0,_kr=_ko+1|0,_ks=_kn;_kn=_kq;_ko=_kr;_kp=_ks;continue;}}else{var _=_kl["v"]["i8"][_kp]=_ko,_ks=_kp+_kn|0;_kp=_ks;continue;}}},_=B(_km(2,0,1,_));return _kl;}),_kt=function(_ku,_kv){var _kw=hs_int64ToInt(_ku),_kx=E(_kj),_ky=_kx["v"]["i8"][(255&_kw>>>0)>>>0&4294967295];if(_kv>_ky){if(_ky>=8){var _kz=hs_uncheckedIShiftRA64(_ku,8),_kA=function(_kB,_kC){while(1){var _kD=B((function(_kE,_kF){var _kG=hs_int64ToInt(_kE),_kH=_kx["v"]["i8"][(255&_kG>>>0)>>>0&4294967295];if(_kF>_kH){if(_kH>=8){var _kI=hs_uncheckedIShiftRA64(_kE,8),_kJ=_kF-8|0;_kB=_kI;_kC=_kJ;return __continue;}else{return new T2(0,new T(function(){var _kK=hs_uncheckedIShiftRA64(_kE,_kH);return B(_kc(_kK));}),_kF-_kH|0);}}else{return new T2(0,new T(function(){var _kL=hs_uncheckedIShiftRA64(_kE,_kF);return B(_kc(_kL));}),0);}})(_kB,_kC));if(_kD!=__continue){return _kD;}}};return new F(function(){return _kA(_kz,_kv-8|0);});}else{return new T2(0,new T(function(){var _kM=hs_uncheckedIShiftRA64(_ku,_ky);return B(_kc(_kM));}),_kv-_ky|0);}}else{return new T2(0,new T(function(){var _kN=hs_uncheckedIShiftRA64(_ku,_kv);return B(_kc(_kN));}),0);}},_kO=function(_kP){var _kQ=hs_intToInt64(_kP);return E(_kQ);},_kR=function(_kS){var _kT=E(_kS);if(!_kT._){return new F(function(){return _kO(_kT.a);});}else{return new F(function(){return I_toInt64(_kT.a);});}},_kU=function(_kV){return I_toInt(_kV)>>>0;},_kW=function(_kX){var _kY=E(_kX);if(!_kY._){return _kY.a>>>0;}else{return new F(function(){return _kU(_kY.a);});}},_kZ=function(_l0){var _l1=B(_k7(_l0)),_l2=_l1.a,_l3=_l1.b;if(_l3<0){var _l4=function(_l5){if(!_l5){return new T2(0,E(_l2),B(_3G(_1Y, -_l3)));}else{var _l6=B(_kt(B(_kR(_l2)), -_l3));return new T2(0,E(_l6.a),B(_3G(_1Y,_l6.b)));}};if(!((B(_kW(_l2))&1)>>>0)){return new F(function(){return _l4(1);});}else{return new F(function(){return _l4(0);});}}else{return new T2(0,B(_3G(_l2,_l3)),_1Y);}},_l7=function(_l8){var _l9=B(_kZ(E(_l8)));return new T2(0,E(_l9.a),E(_l9.b));},_la=new T3(0,_iE,_k6,_l7),_lb=function(_lc){return E(E(_lc).a);},_ld=function(_le){return E(E(_le).a);},_lf=new T1(0,1),_lg=function(_lh,_li){if(_lh<=_li){var _lj=function(_lk){return new T2(1,_lk,new T(function(){if(_lk!=_li){return B(_lj(_lk+1|0));}else{return __Z;}}));};return new F(function(){return _lj(_lh);});}else{return __Z;}},_ll=function(_lm){return new F(function(){return _lg(E(_lm),2147483647);});},_ln=function(_lo,_lp,_lq){if(_lq<=_lp){var _lr=new T(function(){var _ls=_lp-_lo|0,_lt=function(_lu){return (_lu>=(_lq-_ls|0))?new T2(1,_lu,new T(function(){return B(_lt(_lu+_ls|0));})):new T2(1,_lu,_4);};return B(_lt(_lp));});return new T2(1,_lo,_lr);}else{return (_lq<=_lo)?new T2(1,_lo,_4):__Z;}},_lv=function(_lw,_lx,_ly){if(_ly>=_lx){var _lz=new T(function(){var _lA=_lx-_lw|0,_lB=function(_lC){return (_lC<=(_ly-_lA|0))?new T2(1,_lC,new T(function(){return B(_lB(_lC+_lA|0));})):new T2(1,_lC,_4);};return B(_lB(_lx));});return new T2(1,_lw,_lz);}else{return (_ly>=_lw)?new T2(1,_lw,_4):__Z;}},_lD=function(_lE,_lF){if(_lF<_lE){return new F(function(){return _ln(_lE,_lF,-2147483648);});}else{return new F(function(){return _lv(_lE,_lF,2147483647);});}},_lG=function(_lH,_lI){return new F(function(){return _lD(E(_lH),E(_lI));});},_lJ=function(_lK,_lL,_lM){if(_lL<_lK){return new F(function(){return _ln(_lK,_lL,_lM);});}else{return new F(function(){return _lv(_lK,_lL,_lM);});}},_lN=function(_lO,_lP,_lQ){return new F(function(){return _lJ(E(_lO),E(_lP),E(_lQ));});},_lR=function(_lS,_lT){return new F(function(){return _lg(E(_lS),E(_lT));});},_lU=function(_lV){return E(_lV);},_lW=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_lX=new T(function(){return B(err(_lW));}),_lY=function(_lZ){var _m0=E(_lZ);return (_m0==(-2147483648))?E(_lX):_m0-1|0;},_m1=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_m2=new T(function(){return B(err(_m1));}),_m3=function(_m4){var _m5=E(_m4);return (_m5==2147483647)?E(_m2):_m5+1|0;},_m6={_:0,a:_m3,b:_lY,c:_lU,d:_lU,e:_ll,f:_lG,g:_lR,h:_lN},_m7=function(_m8,_m9){if(_m8<=0){if(_m8>=0){return new F(function(){return quot(_m8,_m9);});}else{if(_m9<=0){return new F(function(){return quot(_m8,_m9);});}else{return quot(_m8+1|0,_m9)-1|0;}}}else{if(_m9>=0){if(_m8>=0){return new F(function(){return quot(_m8,_m9);});}else{if(_m9<=0){return new F(function(){return quot(_m8,_m9);});}else{return quot(_m8+1|0,_m9)-1|0;}}}else{return quot(_m8-1|0,_m9)-1|0;}}},_ma=0,_mb=new T(function(){return B(_33(_ma));}),_mc=new T(function(){return die(_mb);}),_md=function(_me,_mf){var _mg=E(_mf);switch(_mg){case -1:var _mh=E(_me);if(_mh==(-2147483648)){return E(_mc);}else{return new F(function(){return _m7(_mh,-1);});}break;case 0:return E(_37);default:return new F(function(){return _m7(_me,_mg);});}},_mi=function(_mj,_mk){return new F(function(){return _md(E(_mj),E(_mk));});},_ml=0,_mm=new T2(0,_mc,_ml),_mn=function(_mo,_mp){var _mq=E(_mo),_mr=E(_mp);switch(_mr){case -1:var _ms=E(_mq);if(_ms==(-2147483648)){return E(_mm);}else{if(_ms<=0){if(_ms>=0){var _mt=quotRemI(_ms,-1);return new T2(0,_mt.a,_mt.b);}else{var _mu=quotRemI(_ms,-1);return new T2(0,_mu.a,_mu.b);}}else{var _mv=quotRemI(_ms-1|0,-1);return new T2(0,_mv.a-1|0,(_mv.b+(-1)|0)+1|0);}}break;case 0:return E(_37);default:if(_mq<=0){if(_mq>=0){var _mw=quotRemI(_mq,_mr);return new T2(0,_mw.a,_mw.b);}else{if(_mr<=0){var _mx=quotRemI(_mq,_mr);return new T2(0,_mx.a,_mx.b);}else{var _my=quotRemI(_mq+1|0,_mr);return new T2(0,_my.a-1|0,(_my.b+_mr|0)-1|0);}}}else{if(_mr>=0){if(_mq>=0){var _mz=quotRemI(_mq,_mr);return new T2(0,_mz.a,_mz.b);}else{if(_mr<=0){var _mA=quotRemI(_mq,_mr);return new T2(0,_mA.a,_mA.b);}else{var _mB=quotRemI(_mq+1|0,_mr);return new T2(0,_mB.a-1|0,(_mB.b+_mr|0)-1|0);}}}else{var _mC=quotRemI(_mq-1|0,_mr);return new T2(0,_mC.a-1|0,(_mC.b+_mr|0)+1|0);}}}},_mD=function(_mE,_mF){var _mG=_mE%_mF;if(_mE<=0){if(_mE>=0){return E(_mG);}else{if(_mF<=0){return E(_mG);}else{var _mH=E(_mG);return (_mH==0)?0:_mH+_mF|0;}}}else{if(_mF>=0){if(_mE>=0){return E(_mG);}else{if(_mF<=0){return E(_mG);}else{var _mI=E(_mG);return (_mI==0)?0:_mI+_mF|0;}}}else{var _mJ=E(_mG);return (_mJ==0)?0:_mJ+_mF|0;}}},_mK=function(_mL,_mM){var _mN=E(_mM);switch(_mN){case -1:return E(_ml);case 0:return E(_37);default:return new F(function(){return _mD(E(_mL),_mN);});}},_mO=function(_mP,_mQ){var _mR=E(_mP),_mS=E(_mQ);switch(_mS){case -1:var _mT=E(_mR);if(_mT==(-2147483648)){return E(_mc);}else{return new F(function(){return quot(_mT,-1);});}break;case 0:return E(_37);default:return new F(function(){return quot(_mR,_mS);});}},_mU=function(_mV,_mW){var _mX=E(_mV),_mY=E(_mW);switch(_mY){case -1:var _mZ=E(_mX);if(_mZ==(-2147483648)){return E(_mm);}else{var _n0=quotRemI(_mZ,-1);return new T2(0,_n0.a,_n0.b);}break;case 0:return E(_37);default:var _n1=quotRemI(_mX,_mY);return new T2(0,_n1.a,_n1.b);}},_n2=function(_n3,_n4){var _n5=E(_n4);switch(_n5){case -1:return E(_ml);case 0:return E(_37);default:return E(_n3)%_n5;}},_n6=function(_n7){return new F(function(){return _ka(E(_n7));});},_n8=function(_n9){return new T2(0,E(B(_ka(E(_n9)))),E(_lf));},_na=function(_nb,_nc){return imul(E(_nb),E(_nc))|0;},_nd=function(_ne,_nf){return E(_ne)+E(_nf)|0;},_ng=function(_nh,_ni){return E(_nh)-E(_ni)|0;},_nj=function(_nk){var _nl=E(_nk);return (_nl<0)? -_nl:E(_nl);},_nm=function(_nn){return new F(function(){return _3k(_nn);});},_no=function(_np){return  -E(_np);},_nq=-1,_nr=0,_ns=1,_nt=function(_nu){var _nv=E(_nu);return (_nv>=0)?(E(_nv)==0)?E(_nr):E(_ns):E(_nq);},_nw={_:0,a:_nd,b:_ng,c:_na,d:_no,e:_nj,f:_nt,g:_nm},_nx=function(_ny,_nz){return E(_ny)==E(_nz);},_nA=function(_nB,_nC){return E(_nB)!=E(_nC);},_nD=new T2(0,_nx,_nA),_nE=function(_nF,_nG){var _nH=E(_nF),_nI=E(_nG);return (_nH>_nI)?E(_nH):E(_nI);},_nJ=function(_nK,_nL){var _nM=E(_nK),_nN=E(_nL);return (_nM>_nN)?E(_nN):E(_nM);},_nO=function(_nP,_nQ){return (_nP>=_nQ)?(_nP!=_nQ)?2:1:0;},_nR=function(_nS,_nT){return new F(function(){return _nO(E(_nS),E(_nT));});},_nU=function(_nV,_nW){return E(_nV)>=E(_nW);},_nX=function(_nY,_nZ){return E(_nY)>E(_nZ);},_o0=function(_o1,_o2){return E(_o1)<=E(_o2);},_o3=function(_o4,_o5){return E(_o4)<E(_o5);},_o6={_:0,a:_nD,b:_nR,c:_o3,d:_o0,e:_nX,f:_nU,g:_nE,h:_nJ},_o7=new T3(0,_nw,_o6,_n8),_o8={_:0,a:_o7,b:_m6,c:_mO,d:_n2,e:_mi,f:_mK,g:_mU,h:_mn,i:_n6},_o9=new T1(0,2),_oa=function(_ob,_oc){while(1){var _od=E(_ob);if(!_od._){var _oe=_od.a,_of=E(_oc);if(!_of._){var _og=_of.a;if(!(imul(_oe,_og)|0)){return new T1(0,imul(_oe,_og)|0);}else{_ob=new T1(1,I_fromInt(_oe));_oc=new T1(1,I_fromInt(_og));continue;}}else{_ob=new T1(1,I_fromInt(_oe));_oc=_of;continue;}}else{var _oh=E(_oc);if(!_oh._){_ob=_od;_oc=new T1(1,I_fromInt(_oh.a));continue;}else{return new T1(1,I_mul(_od.a,_oh.a));}}}},_oi=function(_oj,_ok,_ol){while(1){if(!(_ok%2)){var _om=B(_oa(_oj,_oj)),_on=quot(_ok,2);_oj=_om;_ok=_on;continue;}else{var _oo=E(_ok);if(_oo==1){return new F(function(){return _oa(_oj,_ol);});}else{var _om=B(_oa(_oj,_oj)),_op=B(_oa(_oj,_ol));_oj=_om;_ok=quot(_oo-1|0,2);_ol=_op;continue;}}}},_oq=function(_or,_os){while(1){if(!(_os%2)){var _ot=B(_oa(_or,_or)),_ou=quot(_os,2);_or=_ot;_os=_ou;continue;}else{var _ov=E(_os);if(_ov==1){return E(_or);}else{return new F(function(){return _oi(B(_oa(_or,_or)),quot(_ov-1|0,2),_or);});}}}},_ow=function(_ox){return E(E(_ox).a);},_oy=function(_oz){return E(E(_oz).b);},_oA=function(_oB){return E(E(_oB).c);},_oC=function(_oD){return E(E(_oD).a);},_oE=new T1(0,0),_oF=new T1(0,2),_oG=function(_oH){return E(E(_oH).d);},_oI=function(_oJ,_oK){var _oL=B(_lb(_oJ)),_oM=new T(function(){return B(_ld(_oL));}),_oN=new T(function(){return B(A3(_oG,_oJ,_oK,new T(function(){return B(A2(_8I,_oM,_oF));})));});return new F(function(){return A3(_oC,B(_ow(B(_oy(_oL)))),_oN,new T(function(){return B(A2(_8I,_oM,_oE));}));});},_oO=new T(function(){return B(unCStr("Negative exponent"));}),_oP=new T(function(){return B(err(_oO));}),_oQ=function(_oR){return E(E(_oR).c);},_oS=function(_oT,_oU,_oV,_oW){var _oX=B(_lb(_oU)),_oY=new T(function(){return B(_ld(_oX));}),_oZ=B(_oy(_oX));if(!B(A3(_oA,_oZ,_oW,new T(function(){return B(A2(_8I,_oY,_oE));})))){if(!B(A3(_oC,B(_ow(_oZ)),_oW,new T(function(){return B(A2(_8I,_oY,_oE));})))){var _p0=new T(function(){return B(A2(_8I,_oY,_oF));}),_p1=new T(function(){return B(A2(_8I,_oY,_lf));}),_p2=B(_ow(_oZ)),_p3=function(_p4,_p5,_p6){while(1){var _p7=B((function(_p8,_p9,_pa){if(!B(_oI(_oU,_p9))){if(!B(A3(_oC,_p2,_p9,_p1))){var _pb=new T(function(){return B(A3(_oQ,_oU,new T(function(){return B(A3(_7y,_oY,_p9,_p1));}),_p0));});_p4=new T(function(){return B(A3(_7w,_oT,_p8,_p8));});_p5=_pb;_p6=new T(function(){return B(A3(_7w,_oT,_p8,_pa));});return __continue;}else{return new F(function(){return A3(_7w,_oT,_p8,_pa);});}}else{var _pc=_pa;_p4=new T(function(){return B(A3(_7w,_oT,_p8,_p8));});_p5=new T(function(){return B(A3(_oQ,_oU,_p9,_p0));});_p6=_pc;return __continue;}})(_p4,_p5,_p6));if(_p7!=__continue){return _p7;}}},_pd=function(_pe,_pf){while(1){var _pg=B((function(_ph,_pi){if(!B(_oI(_oU,_pi))){if(!B(A3(_oC,_p2,_pi,_p1))){var _pj=new T(function(){return B(A3(_oQ,_oU,new T(function(){return B(A3(_7y,_oY,_pi,_p1));}),_p0));});return new F(function(){return _p3(new T(function(){return B(A3(_7w,_oT,_ph,_ph));}),_pj,_ph);});}else{return E(_ph);}}else{_pe=new T(function(){return B(A3(_7w,_oT,_ph,_ph));});_pf=new T(function(){return B(A3(_oQ,_oU,_pi,_p0));});return __continue;}})(_pe,_pf));if(_pg!=__continue){return _pg;}}};return new F(function(){return _pd(_oV,_oW);});}else{return new F(function(){return A2(_8I,_oT,_lf);});}}else{return E(_oP);}},_pk=new T(function(){return B(err(_oO));}),_pl=function(_pm,_pn){var _po=B(_k7(_pn)),_pp=_po.a,_pq=_po.b,_pr=new T(function(){return B(_ld(new T(function(){return B(_lb(_pm));})));});if(_pq<0){var _ps= -_pq;if(_ps>=0){var _pt=E(_ps);if(!_pt){var _pu=E(_lf);}else{var _pu=B(_oq(_o9,_pt));}if(!B(_3c(_pu,_3F))){var _pv=B(_3w(_pp,_pu));return new T2(0,new T(function(){return B(A2(_8I,_pr,_pv.a));}),new T(function(){return B(_38(_pv.b,_pq));}));}else{return E(_37);}}else{return E(_pk);}}else{var _pw=new T(function(){var _px=new T(function(){return B(_oS(_pr,_o8,new T(function(){return B(A2(_8I,_pr,_o9));}),_pq));});return B(A3(_7w,_pr,new T(function(){return B(A2(_8I,_pr,_pp));}),_px));});return new T2(0,_pw,_6u);}},_py=function(_pz,_pA){var _pB=B(_pl(_pz,E(_pA))),_pC=_pB.a;if(E(_pB.b)<=0){return E(_pC);}else{var _pD=B(_ld(B(_lb(_pz))));return new F(function(){return A3(_6U,_pD,_pC,new T(function(){return B(A2(_8I,_pD,_1Y));}));});}},_pE=function(_pF,_pG){var _pH=B(_pl(_pF,E(_pG))),_pI=_pH.a;if(E(_pH.b)>=0){return E(_pI);}else{var _pJ=B(_ld(B(_lb(_pF))));return new F(function(){return A3(_7y,_pJ,_pI,new T(function(){return B(A2(_8I,_pJ,_1Y));}));});}},_pK=function(_pL,_pM){var _pN=B(_pl(_pL,E(_pM)));return new T2(0,_pN.a,_pN.b);},_pO=function(_pP,_pQ){var _pR=B(_pl(_pP,_pQ)),_pS=_pR.a,_pT=E(_pR.b),_pU=new T(function(){var _pV=B(_ld(B(_lb(_pP))));if(_pT>=0){return B(A3(_6U,_pV,_pS,new T(function(){return B(A2(_8I,_pV,_1Y));})));}else{return B(A3(_7y,_pV,_pS,new T(function(){return B(A2(_8I,_pV,_1Y));})));}}),_pW=function(_pX){var _pY=_pX-0.5;return (_pY>=0)?(E(_pY)==0)?(!B(_oI(_pP,_pS)))?E(_pU):E(_pS):E(_pU):E(_pS);},_pZ=E(_pT);if(!_pZ){return new F(function(){return _pW(0);});}else{if(_pZ<=0){var _q0= -_pZ-0.5;return (_q0>=0)?(E(_q0)==0)?(!B(_oI(_pP,_pS)))?E(_pU):E(_pS):E(_pU):E(_pS);}else{return new F(function(){return _pW(_pZ);});}}},_q1=function(_q2,_q3){return new F(function(){return _pO(_q2,E(_q3));});},_q4=function(_q5,_q6){return E(B(_pl(_q5,E(_q6))).a);},_q7={_:0,a:_la,b:_iI,c:_pK,d:_q4,e:_q1,f:_py,g:_pE},_q8=function(_q9,_qa,_qb){var _qc=E(_q9);if(!_qc._){return __Z;}else{var _qd=E(_qa);if(!_qd._){return __Z;}else{var _qe=_qd.a,_qf=E(_qb);if(!_qf._){return __Z;}else{var _qg=E(_qf.a),_qh=_qg.a;return new F(function(){return _0(new T2(1,new T3(0,_qc.a,_qe,_qh),new T2(1,new T3(0,_qe,_qh,_qg.b),_4)),new T(function(){return B(_q8(_qc.b,_qd.b,_qf.b));},1));});}}}},_qi=function(_qj,_qk,_ql,_qm){var _qn=E(_ql);if(!_qn._){return __Z;}else{var _qo=_qn.a,_qp=E(_qm);if(!_qp._){return __Z;}else{var _qq=E(_qp.a),_qr=_qq.a;return new F(function(){return _0(new T2(1,new T3(0,_qj,_qo,_qr),new T2(1,new T3(0,_qo,_qr,_qq.b),_4)),new T(function(){return B(_q8(_qk,_qn.b,_qp.b));},1));});}}},_qs=function(_qt,_qu,_qv,_qw,_qx,_qy,_qz){var _qA=new T(function(){return B(_7u(new T(function(){return B(_7s(_qt));})));}),_qB=new T(function(){return B(A3(_7y,_qA,new T(function(){return B(A3(_7w,_qA,_qu,_qy));}),new T(function(){return B(A3(_7w,_qA,_qx,_qv));})));}),_qC=new T(function(){return B(A3(_7y,_qA,new T(function(){return B(A3(_7w,_qA,_qw,_qx));}),new T(function(){return B(A3(_7w,_qA,_qz,_qu));})));}),_qD=new T(function(){return B(A3(_7y,_qA,new T(function(){return B(A3(_7w,_qA,_qv,_qz));}),new T(function(){return B(A3(_7w,_qA,_qy,_qw));})));});return new T3(0,_qD,_qC,_qB);},_qE=new T(function(){return B(_gz(_ja));}),_qF=function(_qG,_qH,_qI){var _qJ=B(A1(_qE,new T3(0,_qG,_qH,_qI))),_qK=_qJ.a,_qL=_qJ.b,_qM=_qJ.c,_qN=B(_jl(_ja,_qK,_qL,_qM)),_qO=new T(function(){return B(_7K(_ja,_qG,_qH,_qI))/Math.sqrt(B(_jb(_ja,_qK,_qL,_qM,_qK,_qL,_qM)));});return new T3(0,new T(function(){return E(_qG)+ -(E(_qN.a)*E(_qO));}),new T(function(){return E(_qH)+ -(E(_qN.b)*E(_qO));}),new T(function(){return E(_qI)+ -(E(_qN.c)*E(_qO));}));},_qP=function(_qQ,_qR,_qS,_qT){var _qU=B(A1(_qE,_qQ)),_qV=B(_jl(_ja,_qU.a,_qU.b,_qU.c)),_qW=_qV.a,_qX=_qV.b,_qY=_qV.c,_qZ=new T(function(){return  -B(_jb(_ja,_qR,_qS,_qT,_qW,_qX,_qY));}),_r0=new T(function(){return E(_qR)+E(_qW)*E(_qZ);}),_r1=new T(function(){return E(_qS)+E(_qX)*E(_qZ);}),_r2=new T(function(){return E(_qT)+E(_qY)*E(_qZ);}),_r3=new T(function(){return Math.sqrt(B(_jb(_ja,_r0,_r1,_r2,_r0,_r1,_r2)));});return new T3(0,new T(function(){return B(_iF(_r0,_r3));}),new T(function(){return B(_iF(_r1,_r3));}),new T(function(){return B(_iF(_r2,_r3));}));},_r4=new T(function(){return B(unCStr(": empty list"));}),_r5=new T(function(){return B(unCStr("Prelude."));}),_r6=function(_r7){return new F(function(){return err(B(_0(_r5,new T(function(){return B(_0(_r7,_r4));},1))));});},_r8=new T(function(){return B(unCStr("head"));}),_r9=new T(function(){return B(_r6(_r8));}),_ra=new T(function(){return eval("drawTriangles");}),_rb=new T(function(){return eval("draw");}),_rc=function(_rd,_re,_rf,_rg){var _rh=Math.sqrt(B(_jb(_ja,_re,_rf,_rg,_re,_rf,_rg)));if(!_rh){return new T3(0,_hU,_hU,_hU);}else{var _ri=B(A1(_qE,_rd)),_rj=B(_jl(_ja,_ri.a,_ri.b,_ri.c)),_rk=_rj.a,_rl=_rj.b,_rm=_rj.c,_rn=new T(function(){return  -B(_jb(_ja,_re,_rf,_rg,_rk,_rl,_rm));}),_ro=new T(function(){return E(_re)+E(_rk)*E(_rn);}),_rp=new T(function(){return E(_rf)+E(_rl)*E(_rn);}),_rq=new T(function(){return E(_rg)+E(_rm)*E(_rn);}),_rr=new T(function(){return Math.sqrt(B(_jb(_ja,_ro,_rp,_rq,_ro,_rp,_rq)));});return new T3(0,new T(function(){return _rh*(E(_ro)/E(_rr));}),new T(function(){return _rh*(E(_rp)/E(_rr));}),new T(function(){return _rh*(E(_rq)/E(_rr));}));}},_rs=function(_rt,_ru){var _rv=E(_ru),_rw=B(_rc(_rt,_rv.a,_rv.b,_rv.c));return new T3(0,_rw.a,_rw.b,_rw.c);},_rx=new T1(0,1),_ry=function(_rz,_rA){var _rB=E(_rz);return new T2(0,_rB,new T(function(){var _rC=B(_ry(B(_3n(_rB,_rA)),_rA));return new T2(1,_rC.a,_rC.b);}));},_rD=function(_rE){var _rF=B(_ry(_rE,_rx));return new T2(1,_rF.a,_rF.b);},_rG=function(_rH,_rI){var _rJ=B(_ry(_rH,new T(function(){return B(_5I(_rI,_rH));})));return new T2(1,_rJ.a,_rJ.b);},_rK=new T1(0,0),_rL=function(_rM,_rN){var _rO=E(_rM);if(!_rO._){var _rP=_rO.a,_rQ=E(_rN);return (_rQ._==0)?_rP>=_rQ.a:I_compareInt(_rQ.a,_rP)<=0;}else{var _rR=_rO.a,_rS=E(_rN);return (_rS._==0)?I_compareInt(_rR,_rS.a)>=0:I_compare(_rR,_rS.a)>=0;}},_rT=function(_rU,_rV,_rW){if(!B(_rL(_rV,_rK))){var _rX=function(_rY){return (!B(_3Z(_rY,_rW)))?new T2(1,_rY,new T(function(){return B(_rX(B(_3n(_rY,_rV))));})):__Z;};return new F(function(){return _rX(_rU);});}else{var _rZ=function(_s0){return (!B(_3Q(_s0,_rW)))?new T2(1,_s0,new T(function(){return B(_rZ(B(_3n(_s0,_rV))));})):__Z;};return new F(function(){return _rZ(_rU);});}},_s1=function(_s2,_s3,_s4){return new F(function(){return _rT(_s2,B(_5I(_s3,_s2)),_s4);});},_s5=function(_s6,_s7){return new F(function(){return _rT(_s6,_rx,_s7);});},_s8=function(_s9){return new F(function(){return _3k(_s9);});},_sa=function(_sb){return new F(function(){return _5I(_sb,_rx);});},_sc=function(_sd){return new F(function(){return _3n(_sd,_rx);});},_se=function(_sf){return new F(function(){return _ka(E(_sf));});},_sg={_:0,a:_sc,b:_sa,c:_se,d:_s8,e:_rD,f:_rG,g:_s5,h:_s1},_sh=function(_si,_sj){while(1){var _sk=E(_si);if(!_sk._){var _sl=E(_sk.a);if(_sl==(-2147483648)){_si=new T1(1,I_fromInt(-2147483648));continue;}else{var _sm=E(_sj);if(!_sm._){return new T1(0,B(_m7(_sl,_sm.a)));}else{_si=new T1(1,I_fromInt(_sl));_sj=_sm;continue;}}}else{var _sn=_sk.a,_so=E(_sj);return (_so._==0)?new T1(1,I_div(_sn,I_fromInt(_so.a))):new T1(1,I_div(_sn,_so.a));}}},_sp=function(_sq,_sr){if(!B(_3c(_sr,_oE))){return new F(function(){return _sh(_sq,_sr);});}else{return E(_37);}},_ss=function(_st,_su){while(1){var _sv=E(_st);if(!_sv._){var _sw=E(_sv.a);if(_sw==(-2147483648)){_st=new T1(1,I_fromInt(-2147483648));continue;}else{var _sx=E(_su);if(!_sx._){var _sy=_sx.a;return new T2(0,new T1(0,B(_m7(_sw,_sy))),new T1(0,B(_mD(_sw,_sy))));}else{_st=new T1(1,I_fromInt(_sw));_su=_sx;continue;}}}else{var _sz=E(_su);if(!_sz._){_st=_sv;_su=new T1(1,I_fromInt(_sz.a));continue;}else{var _sA=I_divMod(_sv.a,_sz.a);return new T2(0,new T1(1,_sA.a),new T1(1,_sA.b));}}}},_sB=function(_sC,_sD){if(!B(_3c(_sD,_oE))){var _sE=B(_ss(_sC,_sD));return new T2(0,_sE.a,_sE.b);}else{return E(_37);}},_sF=function(_sG,_sH){while(1){var _sI=E(_sG);if(!_sI._){var _sJ=E(_sI.a);if(_sJ==(-2147483648)){_sG=new T1(1,I_fromInt(-2147483648));continue;}else{var _sK=E(_sH);if(!_sK._){return new T1(0,B(_mD(_sJ,_sK.a)));}else{_sG=new T1(1,I_fromInt(_sJ));_sH=_sK;continue;}}}else{var _sL=_sI.a,_sM=E(_sH);return (_sM._==0)?new T1(1,I_mod(_sL,I_fromInt(_sM.a))):new T1(1,I_mod(_sL,_sM.a));}}},_sN=function(_sO,_sP){if(!B(_3c(_sP,_oE))){return new F(function(){return _sF(_sO,_sP);});}else{return E(_37);}},_sQ=function(_sR,_sS){while(1){var _sT=E(_sR);if(!_sT._){var _sU=E(_sT.a);if(_sU==(-2147483648)){_sR=new T1(1,I_fromInt(-2147483648));continue;}else{var _sV=E(_sS);if(!_sV._){return new T1(0,quot(_sU,_sV.a));}else{_sR=new T1(1,I_fromInt(_sU));_sS=_sV;continue;}}}else{var _sW=_sT.a,_sX=E(_sS);return (_sX._==0)?new T1(0,I_toInt(I_quot(_sW,I_fromInt(_sX.a)))):new T1(1,I_quot(_sW,_sX.a));}}},_sY=function(_sZ,_t0){if(!B(_3c(_t0,_oE))){return new F(function(){return _sQ(_sZ,_t0);});}else{return E(_37);}},_t1=function(_t2,_t3){if(!B(_3c(_t3,_oE))){var _t4=B(_3w(_t2,_t3));return new T2(0,_t4.a,_t4.b);}else{return E(_37);}},_t5=function(_t6,_t7){while(1){var _t8=E(_t6);if(!_t8._){var _t9=E(_t8.a);if(_t9==(-2147483648)){_t6=new T1(1,I_fromInt(-2147483648));continue;}else{var _ta=E(_t7);if(!_ta._){return new T1(0,_t9%_ta.a);}else{_t6=new T1(1,I_fromInt(_t9));_t7=_ta;continue;}}}else{var _tb=_t8.a,_tc=E(_t7);return (_tc._==0)?new T1(1,I_rem(_tb,I_fromInt(_tc.a))):new T1(1,I_rem(_tb,_tc.a));}}},_td=function(_te,_tf){if(!B(_3c(_tf,_oE))){return new F(function(){return _t5(_te,_tf);});}else{return E(_37);}},_tg=function(_th){return E(_th);},_ti=function(_tj){return E(_tj);},_tk=function(_tl){var _tm=E(_tl);if(!_tm._){var _tn=E(_tm.a);return (_tn==(-2147483648))?E(_6m):(_tn<0)?new T1(0, -_tn):E(_tm);}else{var _to=_tm.a;return (I_compareInt(_to,0)>=0)?E(_tm):new T1(1,I_negate(_to));}},_tp=new T1(0,0),_tq=new T1(0,-1),_tr=function(_ts){var _tt=E(_ts);if(!_tt._){var _tu=_tt.a;return (_tu>=0)?(E(_tu)==0)?E(_tp):E(_3Y):E(_tq);}else{var _tv=I_compareInt(_tt.a,0);return (_tv<=0)?(E(_tv)==0)?E(_tp):E(_tq):E(_3Y);}},_tw={_:0,a:_3n,b:_5I,c:_oa,d:_6n,e:_tk,f:_tr,g:_ti},_tx=function(_ty,_tz){var _tA=E(_ty);if(!_tA._){var _tB=_tA.a,_tC=E(_tz);return (_tC._==0)?_tB!=_tC.a:(I_compareInt(_tC.a,_tB)==0)?false:true;}else{var _tD=_tA.a,_tE=E(_tz);return (_tE._==0)?(I_compareInt(_tD,_tE.a)==0)?false:true:(I_compare(_tD,_tE.a)==0)?false:true;}},_tF=new T2(0,_3c,_tx),_tG=function(_tH,_tI){return (!B(_5t(_tH,_tI)))?E(_tH):E(_tI);},_tJ=function(_tK,_tL){return (!B(_5t(_tK,_tL)))?E(_tL):E(_tK);},_tM={_:0,a:_tF,b:_1Z,c:_3Z,d:_5t,e:_3Q,f:_rL,g:_tG,h:_tJ},_tN=function(_tO){return new T2(0,E(_tO),E(_lf));},_tP=new T3(0,_tw,_tM,_tN),_tQ={_:0,a:_tP,b:_sg,c:_sY,d:_td,e:_sp,f:_sN,g:_t1,h:_sB,i:_tg},_tR=function(_tS){return E(E(_tS).b);},_tT=function(_tU){return E(E(_tU).g);},_tV=new T1(0,1),_tW=function(_tX,_tY,_tZ){var _u0=B(_tR(_tX)),_u1=B(_7u(_u0)),_u2=new T(function(){var _u3=new T(function(){var _u4=new T(function(){var _u5=new T(function(){return B(A3(_tT,_tX,_tQ,new T(function(){return B(A3(_8T,_u0,_tY,_tZ));})));});return B(A2(_8I,_u1,_u5));}),_u6=new T(function(){return B(A2(_6W,_u1,new T(function(){return B(A2(_8I,_u1,_tV));})));});return B(A3(_7w,_u1,_u6,_u4));});return B(A3(_7w,_u1,_u3,_tZ));});return new F(function(){return A3(_6U,_u1,_tY,_u2);});},_u7=1.5707963267948966,_u8=new T(function(){return eval("refresh");}),_u9=new T(function(){return B(unCStr("tail"));}),_ua=new T(function(){return B(_r6(_u9));}),_ub=new T(function(){return eval("triangle");}),_uc=23,_ud=function(_ue,_uf){var _ug=E(_uf),_uh=new T(function(){var _ui=B(_7u(_ue)),_uj=B(_ud(_ue,B(A3(_6U,_ui,_ug,new T(function(){return B(A2(_8I,_ui,_lf));})))));return new T2(1,_uj.a,_uj.b);});return new T2(0,_ug,_uh);},_uk=function(_ul){return E(E(_ul).d);},_um=function(_un,_uo){var _up=E(_uo);if(!_up._){return __Z;}else{var _uq=_up.a;return (!B(A1(_un,_uq)))?__Z:new T2(1,_uq,new T(function(){return B(_um(_un,_up.b));}));}},_ur=function(_us,_ut,_uu,_uv){var _uw=B(_ud(_ut,_uu)),_ux=new T(function(){var _uy=B(_7u(_ut)),_uz=new T(function(){return B(A3(_8T,_ut,new T(function(){return B(A2(_8I,_uy,_lf));}),new T(function(){return B(A2(_8I,_uy,_oF));})));});return B(A3(_6U,_uy,_uv,_uz));});return new F(function(){return _um(function(_uA){return new F(function(){return A3(_uk,_us,_uA,_ux);});},new T2(1,_uw.a,_uw.b));});},_uB=new T(function(){return B(_ur(_k6,_iI,_hU,_uc));}),_uC=4,_uD=new T(function(){return B(_ur(_k6,_iI,_hV,_uC));}),_uE=function(_uF,_uG){var _uH=E(_uF);if(!_uH._){return __Z;}else{var _uI=E(_uG);return (_uI._==0)?__Z:new T2(1,new T2(0,_uH.a,_uI.a),new T(function(){return B(_uE(_uH.b,_uI.b));}));}},_uJ=function(_uK,_uL,_uM,_uN,_uO,_uP,_uQ,_){var _uR=__app0(E(_u8)),_uS=E(_uK),_uT=E(_uL),_uU=E(_uM),_uV=E(_uO),_uW=E(_uP),_uX=E(_uQ),_uY=__apply(E(_rb),new T2(1,_uX,new T2(1,_uW,new T2(1,_uV,new T2(1,_uU,new T2(1,_uT,new T2(1,_uS,_4))))))),_uZ=new T(function(){var _v0=B(A1(_qE,new T3(0,_uS,_uT,_uU))),_v1=B(_jl(_ja,_v0.a,_v0.b,_v0.c)),_v2=B(_qs(_ja,_uV,_uW,_uX,_v1.a,_v1.b,_v1.c));return new T3(0,_v2.a,_v2.b,_v2.c);}),_v3=function(_v4,_){var _v5=E(_v4);if(!_v5._){return _4;}else{var _v6=_v5.b,_v7=new T(function(){var _v8=E(_v5.a)/24;return (_v8+_v8)*3.141592653589793;}),_v9=new T(function(){return 1/Math.cos(B(_tW(_q7,_v7,_u7))-0.7853981633974483);}),_va=function(_vb,_vc,_vd,_){var _ve=E(_vb);if(!_ve._){return new T2(0,_4,new T2(0,_vc,_vd));}else{var _vf=new T(function(){var _vg=E(_vc),_vh=E(_vd),_vi=new T(function(){return 5.5e-2*(1+1/E(_ve.a))*E(_v9);}),_vj=B(_qF(new T(function(){return E(_vg.a)+E(_vh.a)*E(_vi);}),new T(function(){return E(_vg.b)+E(_vh.b)*E(_vi);}),new T(function(){return E(_vg.c)+E(_vh.c)*E(_vi);})));return new T3(0,_vj.a,_vj.b,_vj.c);}),_vk=B(_va(_ve.b,_vf,new T(function(){var _vl=E(_vd),_vm=B(_qP(_vf,_vl.a,_vl.b,_vl.c));return new T3(0,_vm.a,_vm.b,_vm.c);}),_));return new T2(0,new T2(1,_vf,new T(function(){return E(E(_vk).a);})),new T(function(){return E(E(_vk).b);}));}},_vn=new T(function(){var _vo=E(_uZ),_vp=new T(function(){return Math.cos(E(_v7));}),_vq=new T(function(){return Math.sin(E(_v7));});return new T3(0,new T(function(){return _uV*E(_vp)+E(_vo.a)*E(_vq);}),new T(function(){return _uW*E(_vp)+E(_vo.b)*E(_vq);}),new T(function(){return _uX*E(_vp)+E(_vo.c)*E(_vq);}));}),_vr=E(_uD);if(!_vr._){var _vs=B(_v3(_v6,_));return new T2(1,_4,_vs);}else{var _vt=new T(function(){var _vu=E(_vn),_vv=new T(function(){return 5.5e-2*(1+1/E(_vr.a))*E(_v9);}),_vw=B(_qF(new T(function(){return _uS+E(_vu.a)*E(_vv);}),new T(function(){return _uT+E(_vu.b)*E(_vv);}),new T(function(){return _uU+E(_vu.c)*E(_vv);})));return new T3(0,_vw.a,_vw.b,_vw.c);}),_vx=B(_va(_vr.b,_vt,new T(function(){var _vy=E(_vn),_vz=B(_qP(_vt,_vy.a,_vy.b,_vy.c));return new T3(0,_vz.a,_vz.b,_vz.c);}),_)),_vA=B(_v3(_v6,_));return new T2(1,new T2(1,_vt,new T(function(){return E(E(_vx).a);})),_vA);}}},_vB=B(_v3(_uB,_)),_vC=function(_vD,_vE,_){var _vF=E(_vD);if(!_vF._){return _4;}else{var _vG=E(_vE);if(!_vG._){return _4;}else{var _vH=E(_vF.a);if(!_vH._){return E(_r9);}else{var _vI=_vH.b,_vJ=E(_vH.a),_vK=E(_vG.a);if(!_vK._){return E(_r9);}else{var _vL=E(_vK.a),_vM=E(_ub),_vN=__apply(_vM,new T2(1,E(_vL.c),new T2(1,E(_vL.b),new T2(1,E(_vL.a),new T2(1,E(_vJ.c),new T2(1,E(_vJ.b),new T2(1,E(_vJ.a),new T2(1,_uU,new T2(1,_uT,new T2(1,_uS,_4)))))))))),_vO=function(_vP,_){var _vQ=E(_vP);if(!_vQ._){return new F(function(){return _vC(_vF.b,_vG.b,_);});}else{var _vR=E(_vQ.a),_vS=E(_vR.a),_vT=E(_vR.b),_vU=E(_vR.c),_vV=__apply(_vM,new T2(1,E(_vU.c),new T2(1,E(_vU.b),new T2(1,E(_vU.a),new T2(1,E(_vT.c),new T2(1,E(_vT.b),new T2(1,E(_vT.a),new T2(1,E(_vS.c),new T2(1,E(_vS.b),new T2(1,E(_vS.a),_4)))))))))),_vW=B(_vO(_vQ.b,_));return new T2(1,_5,_vW);}},_vX=B(_vO(B(_qi(_vJ,_vI,_vI,new T(function(){return B(_uE(_vK,_vK.b));},1))),_));return new T2(1,_5,_vX);}}}}},_vY=new T(function(){var _vZ=B(_0(_vB,new T2(1,new T(function(){var _w0=E(_vB);if(!_w0._){return E(_r9);}else{return E(_w0.a);}}),_4)));if(!_vZ._){return E(_ua);}else{return E(_vZ.b);}},1),_w1=B(_vC(_vB,_vY,_)),_w2=__app0(E(_ra)),_w3=new T(function(){var _w4=E(_uN),_w5=B(_qF(new T(function(){return _uS+E(_w4.a)*2.0e-2;}),new T(function(){return _uT+E(_w4.b)*2.0e-2;}),new T(function(){return _uU+E(_w4.c)*2.0e-2;})));return new T3(0,_w5.a,_w5.b,_w5.c);});return new T3(0,_w3,new T(function(){return B(_rs(_w3,_uN));}),new T(function(){var _w6=B(_qP(_w3,_uV,_uW,_uX));return new T3(0,_w6.a,_w6.b,_w6.c);}));},_w7=function(_w8,_w9,_wa){var _wb=function(_){var _wc=E(_w8),_wd=E(_wc.a),_we=E(_wc.c),_wf=B(_uJ(_wd.a,_wd.b,_wd.c,_wc.b,_we.a,_we.b,_we.c,_));return new T(function(){return B(A1(_wa,new T1(1,_wf)));});};return new T1(0,_wb);},_wg=new T0(2),_wh=function(_wi,_wj,_wk){return function(_){var _wl=E(_wi),_wm=rMV(_wl),_wn=E(_wm);if(!_wn._){var _wo=new T(function(){var _wp=new T(function(){return B(A1(_wk,_5));});return B(_0(_wn.b,new T2(1,new T2(0,_wj,function(_wq){return E(_wp);}),_4)));}),_=wMV(_wl,new T2(0,_wn.a,_wo));return _wg;}else{var _wr=E(_wn.a);if(!_wr._){var _=wMV(_wl,new T2(0,_wj,_4));return new T(function(){return B(A1(_wk,_5));});}else{var _=wMV(_wl,new T1(1,_wr.b));return new T1(1,new T2(1,new T(function(){return B(A1(_wk,_5));}),new T2(1,new T(function(){return B(A2(_wr.a,_wj,_hM));}),_4)));}}};},_ws=function(_wt){return E(E(_wt).b);},_wu=function(_wv,_ww,_wx){var _wy=new T(function(){return new T1(0,B(_wh(_ww,_wx,_hM)));}),_wz=function(_wA){return new T1(1,new T2(1,new T(function(){return B(A1(_wA,_5));}),new T2(1,_wy,_4)));};return new F(function(){return A2(_ws,_wv,_wz);});},_wB=function(_){return new F(function(){return __jsNull();});},_wC=function(_wD){var _wE=B(A1(_wD,_));return E(_wE);},_wF=new T(function(){return B(_wC(_wB));}),_wG=new T(function(){return E(_wF);}),_wH=new T(function(){return eval("window.requestAnimationFrame");}),_wI=new T1(1,_4),_wJ=function(_wK,_wL){return function(_){var _wM=E(_wK),_wN=rMV(_wM),_wO=E(_wN);if(!_wO._){var _wP=_wO.a,_wQ=E(_wO.b);if(!_wQ._){var _=wMV(_wM,_wI);return new T(function(){return B(A1(_wL,_wP));});}else{var _wR=E(_wQ.a),_=wMV(_wM,new T2(0,_wR.a,_wQ.b));return new T1(1,new T2(1,new T(function(){return B(A1(_wL,_wP));}),new T2(1,new T(function(){return B(A1(_wR.b,_hM));}),_4)));}}else{var _wS=new T(function(){var _wT=function(_wU){var _wV=new T(function(){return B(A1(_wL,_wU));});return function(_wW){return E(_wV);};};return B(_0(_wO.a,new T2(1,_wT,_4)));}),_=wMV(_wM,new T1(1,_wS));return _wg;}};},_wX=function(_wY,_wZ){return new T1(0,B(_wJ(_wY,_wZ)));},_x0=function(_x1,_x2){var _x3=new T(function(){return new T1(0,B(_wh(_x1,_5,_hM)));});return function(_){var _x4=__createJSFunc(2,function(_x5,_){var _x6=B(_c(_x3,_4,_));return _wG;}),_x7=__app1(E(_wH),_x4);return new T(function(){return B(_wX(_x1,_x2));});};},_x8=new T1(1,_4),_x9=function(_xa){var _xb=new T(function(){return B(_xc(_));}),_xd=new T(function(){var _xe=function(_xf){return E(_xb);},_xg=function(_){var _xh=nMV(_x8);return new T(function(){return new T1(0,B(_x0(_xh,_xe)));});};return B(A(_wu,[_hT,_xa,_5,function(_xi){return E(new T1(0,_xg));}]));}),_xc=function(_xj){return E(_xd);};return new F(function(){return _xc(_);});},_xk=function(_xl){return E(E(_xl).a);},_xm=function(_xn){return E(E(_xn).d);},_xo=function(_xp){return E(E(_xp).c);},_xq=function(_xr){return E(E(_xr).c);},_xs=new T1(1,_4),_xt=function(_xu){var _xv=function(_){var _xw=nMV(_xs);return new T(function(){return B(A1(_xu,_xw));});};return new T1(0,_xv);},_xx=function(_xy,_xz){var _xA=new T(function(){return B(_xq(_xy));}),_xB=B(_xk(_xy)),_xC=function(_xD){var _xE=new T(function(){return B(A1(_xA,new T(function(){return B(A1(_xz,_xD));})));});return new F(function(){return A3(_xo,_xB,_xE,new T(function(){return B(A2(_xm,_xB,_xD));}));});};return new F(function(){return A3(_hD,_xB,new T(function(){return B(A2(_ws,_xy,_xt));}),_xC);});},_xF=function(_xG,_xH,_xI){var _xJ=new T(function(){return B(_xk(_xG));}),_xK=new T(function(){return B(A2(_xm,_xJ,_5));}),_xL=function(_xM,_xN){var _xO=new T(function(){var _xP=new T(function(){return B(A2(_ws,_xG,function(_xQ){return new F(function(){return _wX(_xN,_xQ);});}));});return B(A3(_hD,_xJ,_xP,new T(function(){return B(A1(_xI,_xM));})));});return new F(function(){return A3(_hD,_xJ,_xO,function(_xR){var _xS=E(_xR);if(!_xS._){return E(_xK);}else{return new F(function(){return _xL(_xS.a,_xN);});}});});};return new F(function(){return _xx(_xG,function(_xQ){return new F(function(){return _xL(_xH,_xQ);});});});},_xT=new T(function(){return B(A(_xF,[_hT,_jx,_w7,_x9]));}),_xU=function(_){var _xV=__app2(E(_h),E(_86),E(_gT));return new F(function(){return _c(_xT,_4,_);});},_xW=function(_){return new F(function(){return _xU(_);});};
var hasteMain = function() {B(A(_xW, [0]));};window.onload = hasteMain;