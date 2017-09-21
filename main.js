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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==(-2147483648)){_3l=new T1(1,I_fromInt(-2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0,-1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==(-2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S(-1021,53,_6k,_6l);});}else{return  -B(_5S(-1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=function(_7h){return E(E(_7h).a);},_7i=function(_7j){return E(E(_7j).a);},_7k=function(_7l){return E(E(_7l).c);},_7m=function(_7n){return E(E(_7n).b);},_7o=function(_7p){return E(E(_7p).d);},_7q=new T1(0,1),_7r=new T1(0,2),_7s=new T2(0,E(_7q),E(_7r)),_7t=new T1(0,5),_7u=new T1(0,4),_7v=new T2(0,E(_7u),E(_7t)),_7w=function(_7x){return E(E(_7x).e);},_7y=function(_7z,_7A,_7B,_7C){var _7D=B(_7g(_7z)),_7E=B(_7i(_7D)),_7F=new T(function(){var _7G=new T(function(){var _7H=new T(function(){var _7I=new T(function(){var _7J=new T(function(){var _7K=new T(function(){return B(A3(_6I,_7E,new T(function(){return B(A3(_7k,_7E,_7A,_7A));}),new T(function(){return B(A3(_7k,_7E,_7C,_7C));})));});return B(A2(_7w,_7z,_7K));});return B(A3(_7m,_7E,_7J,new T(function(){return B(A2(_7o,_7D,_7v));})));});return B(A3(_7k,_7E,_7I,_7I));});return B(A3(_6I,_7E,_7H,new T(function(){return B(A3(_7k,_7E,_7B,_7B));})));});return B(A2(_7w,_7z,_7G));});return new F(function(){return A3(_7m,_7E,_7F,new T(function(){return B(A2(_7o,_7D,_7s));}));});},_7L=new T(function(){return B(unCStr("x"));}),_7M=new T1(0,_7L),_7N=new T(function(){return B(unCStr("y"));}),_7O=new T1(0,_7N),_7P=new T(function(){return B(unCStr("z"));}),_7Q=new T1(0,_7P),_7R=new T(function(){return B(_7y(_7f,_7M,_7O,_7Q));}),_7S=function(_7T){return E(_7T);},_7U=new T(function(){return toJSStr(B(_5(_p,_7S,_7R)));}),_7V=function(_7W,_7X,_7Y){var _7Z=new T(function(){return B(_1(_7W));}),_80=new T(function(){return B(_3(_7W));}),_81=function(_82){var _83=E(_82);if(!_83._){return E(_80);}else{return new F(function(){return A2(_7Z,new T(function(){return B(_5(_7W,_7X,_83.a));}),new T(function(){return B(_81(_83.b));}));});}};return new F(function(){return _81(_7Y);});},_84=new T3(0,E(_7M),E(_7O),E(_7Q)),_85=new T(function(){return B(unCStr("(/=) is not defined"));}),_86=new T(function(){return B(err(_85));}),_87=new T(function(){return B(unCStr("(==) is not defined"));}),_88=new T(function(){return B(err(_87));}),_89=new T2(0,_88,_86),_8a=new T(function(){return B(unCStr("(<) is not defined"));}),_8b=new T(function(){return B(err(_8a));}),_8c=new T(function(){return B(unCStr("(<=) is not defined"));}),_8d=new T(function(){return B(err(_8c));}),_8e=new T(function(){return B(unCStr("(>) is not defined"));}),_8f=new T(function(){return B(err(_8e));}),_8g=new T(function(){return B(unCStr("(>=) is not defined"));}),_8h=new T(function(){return B(err(_8g));}),_8i=new T(function(){return B(unCStr("compare is not defined"));}),_8j=new T(function(){return B(err(_8i));}),_8k=new T(function(){return B(unCStr("max("));}),_8l=new T1(0,_8k),_8m=function(_8n,_8o){return new T1(1,new T2(1,_8l,new T2(1,_8n,new T2(1,_r,new T2(1,_8o,_w)))));},_8p=new T(function(){return B(unCStr("min("));}),_8q=new T1(0,_8p),_8r=function(_8s,_8t){return new T1(1,new T2(1,_8q,new T2(1,_8s,new T2(1,_r,new T2(1,_8t,_w)))));},_8u={_:0,a:_89,b:_8j,c:_8b,d:_8d,e:_8f,f:_8h,g:_8m,h:_8r},_8v=new T2(0,_7f,_8u),_8w=function(_8x,_8y){var _8z=E(_8x);return E(_8y);},_8A=function(_8B,_8C){var _8D=E(_8C);return E(_8B);},_8E=function(_8F,_8G){var _8H=E(_8F),_8I=E(_8G);return new T3(0,E(B(A1(_8H.a,_8I.a))),E(B(A1(_8H.b,_8I.b))),E(B(A1(_8H.c,_8I.c))));},_8J=function(_8K,_8L,_8M){return new T3(0,E(_8K),E(_8L),E(_8M));},_8N=function(_8O){return new F(function(){return _8J(_8O,_8O,_8O);});},_8P=function(_8Q,_8R){var _8S=E(_8R),_8T=E(_8Q);return new T3(0,E(_8T),E(_8T),E(_8T));},_8U=function(_8V,_8W){var _8X=E(_8W);return new T3(0,E(B(A1(_8V,_8X.a))),E(B(A1(_8V,_8X.b))),E(B(A1(_8V,_8X.c))));},_8Y=new T2(0,_8U,_8P),_8Z=new T5(0,_8Y,_8N,_8E,_8w,_8A),_90=new T1(0,0),_91=function(_92){return E(E(_92).g);},_93=function(_94){var _95=B(A2(_91,_94,_7q)),_96=B(A2(_91,_94,_90));return new T3(0,E(new T3(0,E(_95),E(_96),E(_96))),E(new T3(0,E(_96),E(_95),E(_96))),E(new T3(0,E(_96),E(_96),E(_95))));},_97=function(_98){return E(E(_98).a);},_99=function(_9a){return E(E(_9a).f);},_9b=function(_9c){return E(E(_9c).b);},_9d=function(_9e){return E(E(_9e).c);},_9f=function(_9g){return E(E(_9g).a);},_9h=function(_9i){return E(E(_9i).d);},_9j=function(_9k,_9l,_9m,_9n,_9o){var _9p=new T(function(){return E(E(E(_9k).c).a);}),_9q=new T(function(){var _9r=E(_9k).a,_9s=new T(function(){var _9t=new T(function(){return B(_7g(_9p));}),_9u=new T(function(){return B(_7i(_9t));}),_9v=new T(function(){return B(A2(_9h,_9p,_9l));}),_9w=new T(function(){return B(A3(_99,_9p,_9l,_9n));}),_9x=function(_9y,_9z){var _9A=new T(function(){var _9B=new T(function(){return B(A3(_9b,_9t,new T(function(){return B(A3(_7k,_9u,_9n,_9y));}),_9l));});return B(A3(_6I,_9u,_9B,new T(function(){return B(A3(_7k,_9u,_9z,_9v));})));});return new F(function(){return A3(_7k,_9u,_9w,_9A);});};return B(A3(_9f,B(_97(_9r)),_9x,_9m));});return B(A3(_9d,_9r,_9s,_9o));});return new T2(0,new T(function(){return B(A3(_99,_9p,_9l,_9n));}),_9q);},_9C=function(_9D,_9E,_9F,_9G){var _9H=E(_9F),_9I=E(_9G),_9J=B(_9j(_9E,_9H.a,_9H.b,_9I.a,_9I.b));return new T2(0,_9J.a,_9J.b);},_9K=new T1(0,1),_9L=function(_9M){return E(E(_9M).l);},_9N=function(_9O,_9P,_9Q){var _9R=new T(function(){return E(E(E(_9O).c).a);}),_9S=new T(function(){var _9T=new T(function(){return B(_7g(_9R));}),_9U=new T(function(){var _9V=B(_7i(_9T)),_9W=new T(function(){var _9X=new T(function(){return B(A3(_7m,_9V,new T(function(){return B(A2(_91,_9V,_9K));}),new T(function(){return B(A3(_7k,_9V,_9P,_9P));})));});return B(A2(_7w,_9R,_9X));});return B(A2(_6K,_9V,_9W));});return B(A3(_9f,B(_97(E(_9O).a)),function(_9Y){return new F(function(){return A3(_9b,_9T,_9Y,_9U);});},_9Q));});return new T2(0,new T(function(){return B(A2(_9L,_9R,_9P));}),_9S);},_9Z=function(_a0,_a1,_a2){var _a3=E(_a2),_a4=B(_9N(_a1,_a3.a,_a3.b));return new T2(0,_a4.a,_a4.b);},_a5=function(_a6){return E(E(_a6).r);},_a7=function(_a8,_a9,_aa){var _ab=new T(function(){return E(E(E(_a8).c).a);}),_ac=new T(function(){var _ad=new T(function(){return B(_7g(_ab));}),_ae=new T(function(){var _af=new T(function(){var _ag=B(_7i(_ad));return B(A3(_7m,_ag,new T(function(){return B(A3(_7k,_ag,_a9,_a9));}),new T(function(){return B(A2(_91,_ag,_9K));})));});return B(A2(_7w,_ab,_af));});return B(A3(_9f,B(_97(E(_a8).a)),function(_ah){return new F(function(){return A3(_9b,_ad,_ah,_ae);});},_aa));});return new T2(0,new T(function(){return B(A2(_a5,_ab,_a9));}),_ac);},_ai=function(_aj,_ak,_al){var _am=E(_al),_an=B(_a7(_ak,_am.a,_am.b));return new T2(0,_an.a,_an.b);},_ao=function(_ap){return E(E(_ap).k);},_aq=function(_ar,_as,_at){var _au=new T(function(){return E(E(E(_ar).c).a);}),_av=new T(function(){var _aw=new T(function(){return B(_7g(_au));}),_ax=new T(function(){var _ay=new T(function(){var _az=B(_7i(_aw));return B(A3(_7m,_az,new T(function(){return B(A2(_91,_az,_9K));}),new T(function(){return B(A3(_7k,_az,_as,_as));})));});return B(A2(_7w,_au,_ay));});return B(A3(_9f,B(_97(E(_ar).a)),function(_aA){return new F(function(){return A3(_9b,_aw,_aA,_ax);});},_at));});return new T2(0,new T(function(){return B(A2(_ao,_au,_as));}),_av);},_aB=function(_aC,_aD,_aE){var _aF=E(_aE),_aG=B(_aq(_aD,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=function(_aI){return E(E(_aI).q);},_aJ=function(_aK,_aL,_aM){var _aN=new T(function(){return E(E(E(_aK).c).a);}),_aO=new T(function(){var _aP=new T(function(){return B(_7g(_aN));}),_aQ=new T(function(){var _aR=new T(function(){var _aS=B(_7i(_aP));return B(A3(_6I,_aS,new T(function(){return B(A3(_7k,_aS,_aL,_aL));}),new T(function(){return B(A2(_91,_aS,_9K));})));});return B(A2(_7w,_aN,_aR));});return B(A3(_9f,B(_97(E(_aK).a)),function(_aT){return new F(function(){return A3(_9b,_aP,_aT,_aQ);});},_aM));});return new T2(0,new T(function(){return B(A2(_aH,_aN,_aL));}),_aO);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aJ(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).m);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_7g(_b6));}),_b9=new T(function(){var _ba=B(_7i(_b8));return B(A3(_6I,_ba,new T(function(){return B(A2(_91,_ba,_9K));}),new T(function(){return B(A3(_7k,_ba,_b4,_b4));})));});return B(A3(_9f,B(_97(E(_b3).a)),function(_bb){return new F(function(){return A3(_9b,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).s);},_bk=function(_bl,_bm,_bn){var _bo=new T(function(){return E(E(E(_bl).c).a);}),_bp=new T(function(){var _bq=new T(function(){return B(_7g(_bo));}),_br=new T(function(){var _bs=B(_7i(_bq));return B(A3(_7m,_bs,new T(function(){return B(A2(_91,_bs,_9K));}),new T(function(){return B(A3(_7k,_bs,_bm,_bm));})));});return B(A3(_9f,B(_97(E(_bl).a)),function(_bt){return new F(function(){return A3(_9b,_bq,_bt,_br);});},_bn));});return new T2(0,new T(function(){return B(A2(_bi,_bo,_bm));}),_bp);},_bu=function(_bv,_bw,_bx){var _by=E(_bx),_bz=B(_bk(_bw,_by.a,_by.b));return new T2(0,_bz.a,_bz.b);},_bA=function(_bB){return E(E(_bB).i);},_bC=function(_bD){return E(E(_bD).h);},_bE=function(_bF,_bG,_bH){var _bI=new T(function(){return E(E(E(_bF).c).a);}),_bJ=new T(function(){var _bK=new T(function(){return B(_7i(new T(function(){return B(_7g(_bI));})));}),_bL=new T(function(){return B(A2(_6K,_bK,new T(function(){return B(A2(_bC,_bI,_bG));})));});return B(A3(_9f,B(_97(E(_bF).a)),function(_bM){return new F(function(){return A3(_7k,_bK,_bM,_bL);});},_bH));});return new T2(0,new T(function(){return B(A2(_bA,_bI,_bG));}),_bJ);},_bN=function(_bO,_bP,_bQ){var _bR=E(_bQ),_bS=B(_bE(_bP,_bR.a,_bR.b));return new T2(0,_bS.a,_bS.b);},_bT=function(_bU){return E(E(_bU).o);},_bV=function(_bW){return E(E(_bW).n);},_bX=function(_bY,_bZ,_c0){var _c1=new T(function(){return E(E(E(_bY).c).a);}),_c2=new T(function(){var _c3=new T(function(){return B(_7i(new T(function(){return B(_7g(_c1));})));}),_c4=new T(function(){return B(A2(_bV,_c1,_bZ));});return B(A3(_9f,B(_97(E(_bY).a)),function(_c5){return new F(function(){return A3(_7k,_c3,_c5,_c4);});},_c0));});return new T2(0,new T(function(){return B(A2(_bT,_c1,_bZ));}),_c2);},_c6=function(_c7,_c8,_c9){var _ca=E(_c9),_cb=B(_bX(_c8,_ca.a,_ca.b));return new T2(0,_cb.a,_cb.b);},_cc=function(_cd){return E(E(_cd).c);},_ce=function(_cf,_cg,_ch){var _ci=new T(function(){return E(E(E(_cf).c).a);}),_cj=new T(function(){var _ck=new T(function(){return B(_7i(new T(function(){return B(_7g(_ci));})));}),_cl=new T(function(){return B(A2(_cc,_ci,_cg));});return B(A3(_9f,B(_97(E(_cf).a)),function(_cm){return new F(function(){return A3(_7k,_ck,_cm,_cl);});},_ch));});return new T2(0,new T(function(){return B(A2(_cc,_ci,_cg));}),_cj);},_cn=function(_co,_cp,_cq){var _cr=E(_cq),_cs=B(_ce(_cp,_cr.a,_cr.b));return new T2(0,_cs.a,_cs.b);},_ct=function(_cu,_cv,_cw){var _cx=new T(function(){return E(E(E(_cu).c).a);}),_cy=new T(function(){var _cz=new T(function(){return B(_7g(_cx));}),_cA=new T(function(){return B(_7i(_cz));}),_cB=new T(function(){return B(A3(_9b,_cz,new T(function(){return B(A2(_91,_cA,_9K));}),_cv));});return B(A3(_9f,B(_97(E(_cu).a)),function(_cC){return new F(function(){return A3(_7k,_cA,_cC,_cB);});},_cw));});return new T2(0,new T(function(){return B(A2(_9h,_cx,_cv));}),_cy);},_cD=function(_cE,_cF,_cG){var _cH=E(_cG),_cI=B(_ct(_cF,_cH.a,_cH.b));return new T2(0,_cI.a,_cI.b);},_cJ=function(_cK,_cL,_cM,_cN){var _cO=new T(function(){return E(E(_cL).c);}),_cP=new T3(0,new T(function(){return E(E(_cL).a);}),new T(function(){return E(E(_cL).b);}),new T2(0,new T(function(){return E(E(_cO).a);}),new T(function(){return E(E(_cO).b);})));return new F(function(){return A3(_9b,_cK,new T(function(){var _cQ=E(_cN),_cR=B(_ct(_cP,_cQ.a,_cQ.b));return new T2(0,_cR.a,_cR.b);}),new T(function(){var _cS=E(_cM),_cT=B(_ct(_cP,_cS.a,_cS.b));return new T2(0,_cT.a,_cT.b);}));});},_cU=new T1(0,0),_cV=function(_cW){return E(E(_cW).b);},_cX=function(_cY){return E(E(_cY).b);},_cZ=function(_d0){var _d1=new T(function(){return E(E(E(_d0).c).a);}),_d2=new T(function(){return B(A2(_cX,E(_d0).a,new T(function(){return B(A2(_91,B(_7i(B(_7g(_d1)))),_cU));})));});return new T2(0,new T(function(){return B(_cV(_d1));}),_d2);},_d3=function(_d4,_d5){var _d6=B(_cZ(_d5));return new T2(0,_d6.a,_d6.b);},_d7=function(_d8,_d9,_da){var _db=new T(function(){return E(E(E(_d8).c).a);}),_dc=new T(function(){var _dd=new T(function(){return B(_7i(new T(function(){return B(_7g(_db));})));}),_de=new T(function(){return B(A2(_bA,_db,_d9));});return B(A3(_9f,B(_97(E(_d8).a)),function(_df){return new F(function(){return A3(_7k,_dd,_df,_de);});},_da));});return new T2(0,new T(function(){return B(A2(_bC,_db,_d9));}),_dc);},_dg=function(_dh,_di,_dj){var _dk=E(_dj),_dl=B(_d7(_di,_dk.a,_dk.b));return new T2(0,_dl.a,_dl.b);},_dm=function(_dn,_do,_dp){var _dq=new T(function(){return E(E(E(_dn).c).a);}),_dr=new T(function(){var _ds=new T(function(){return B(_7i(new T(function(){return B(_7g(_dq));})));}),_dt=new T(function(){return B(A2(_bT,_dq,_do));});return B(A3(_9f,B(_97(E(_dn).a)),function(_du){return new F(function(){return A3(_7k,_ds,_du,_dt);});},_dp));});return new T2(0,new T(function(){return B(A2(_bV,_dq,_do));}),_dr);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dm(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=new T1(0,2),_dC=function(_dD,_dE,_dF){var _dG=new T(function(){return E(E(E(_dD).c).a);}),_dH=new T(function(){var _dI=new T(function(){return B(_7g(_dG));}),_dJ=new T(function(){return B(_7i(_dI));}),_dK=new T(function(){var _dL=new T(function(){return B(A3(_9b,_dI,new T(function(){return B(A2(_91,_dJ,_9K));}),new T(function(){return B(A2(_91,_dJ,_dB));})));});return B(A3(_9b,_dI,_dL,new T(function(){return B(A2(_7w,_dG,_dE));})));});return B(A3(_9f,B(_97(E(_dD).a)),function(_dM){return new F(function(){return A3(_7k,_dJ,_dM,_dK);});},_dF));});return new T2(0,new T(function(){return B(A2(_7w,_dG,_dE));}),_dH);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dC(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).j);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_7g(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bA,_dZ,_dX));});return B(A3(_7k,B(_7i(_e1)),_e3,_e3));});return B(A3(_9f,B(_97(E(_dW).a)),function(_e4){return new F(function(){return A3(_9b,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec){return E(E(_ec).p);},_ed=function(_ee,_ef,_eg){var _eh=new T(function(){return E(E(E(_ee).c).a);}),_ei=new T(function(){var _ej=new T(function(){return B(_7g(_eh));}),_ek=new T(function(){var _el=new T(function(){return B(A2(_bT,_eh,_ef));});return B(A3(_7k,B(_7i(_ej)),_el,_el));});return B(A3(_9f,B(_97(E(_ee).a)),function(_em){return new F(function(){return A3(_9b,_ej,_em,_ek);});},_eg));});return new T2(0,new T(function(){return B(A2(_eb,_eh,_ef));}),_ei);},_en=function(_eo,_ep,_eq){var _er=E(_eq),_es=B(_ed(_ep,_er.a,_er.b));return new T2(0,_es.a,_es.b);},_et=function(_eu,_ev){return {_:0,a:_eu,b:new T(function(){return B(_d3(_eu,_ev));}),c:function(_ew){return new F(function(){return _cn(_eu,_ev,_ew);});},d:function(_ew){return new F(function(){return _cD(_eu,_ev,_ew);});},e:function(_ew){return new F(function(){return _dN(_eu,_ev,_ew);});},f:function(_ex,_ew){return new F(function(){return _9C(_eu,_ev,_ex,_ew);});},g:function(_ex,_ew){return new F(function(){return _cJ(_eu,_ev,_ex,_ew);});},h:function(_ew){return new F(function(){return _dg(_eu,_ev,_ew);});},i:function(_ew){return new F(function(){return _bN(_eu,_ev,_ew);});},j:function(_ew){return new F(function(){return _e5(_eu,_ev,_ew);});},k:function(_ew){return new F(function(){return _aB(_eu,_ev,_ew);});},l:function(_ew){return new F(function(){return _9Z(_eu,_ev,_ew);});},m:function(_ew){return new F(function(){return _bc(_eu,_ev,_ew);});},n:function(_ew){return new F(function(){return _dv(_eu,_ev,_ew);});},o:function(_ew){return new F(function(){return _c6(_eu,_ev,_ew);});},p:function(_ew){return new F(function(){return _en(_eu,_ev,_ew);});},q:function(_ew){return new F(function(){return _aU(_eu,_ev,_ew);});},r:function(_ew){return new F(function(){return _ai(_eu,_ev,_ew);});},s:function(_ew){return new F(function(){return _bu(_eu,_ev,_ew);});}};},_ey=function(_ez,_eA,_eB,_eC,_eD){var _eE=new T(function(){return B(_7g(new T(function(){return E(E(E(_ez).c).a);})));}),_eF=new T(function(){var _eG=E(_ez).a,_eH=new T(function(){var _eI=new T(function(){return B(_7i(_eE));}),_eJ=new T(function(){return B(A3(_7k,_eI,_eC,_eC));}),_eK=function(_eL,_eM){var _eN=new T(function(){return B(A3(_7m,_eI,new T(function(){return B(A3(_7k,_eI,_eL,_eC));}),new T(function(){return B(A3(_7k,_eI,_eA,_eM));})));});return new F(function(){return A3(_9b,_eE,_eN,_eJ);});};return B(A3(_9f,B(_97(_eG)),_eK,_eB));});return B(A3(_9d,_eG,_eH,_eD));});return new T2(0,new T(function(){return B(A3(_9b,_eE,_eA,_eC));}),_eF);},_eO=function(_eP,_eQ,_eR,_eS){var _eT=E(_eR),_eU=E(_eS),_eV=B(_ey(_eQ,_eT.a,_eT.b,_eU.a,_eU.b));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX,_eY){var _eZ=new T(function(){return B(_7g(new T(function(){return E(E(E(_eX).c).a);})));}),_f0=new T(function(){return B(A2(_cX,E(_eX).a,new T(function(){return B(A2(_91,B(_7i(_eZ)),_cU));})));});return new T2(0,new T(function(){return B(A2(_7o,_eZ,_eY));}),_f0);},_f1=function(_f2,_f3,_f4){var _f5=B(_eW(_f3,_f4));return new T2(0,_f5.a,_f5.b);},_f6=function(_f7,_f8,_f9){var _fa=new T(function(){return B(_7g(new T(function(){return E(E(E(_f7).c).a);})));}),_fb=new T(function(){return B(_7i(_fa));}),_fc=new T(function(){var _fd=new T(function(){var _fe=new T(function(){return B(A3(_9b,_fa,new T(function(){return B(A2(_91,_fb,_9K));}),new T(function(){return B(A3(_7k,_fb,_f8,_f8));})));});return B(A2(_6K,_fb,_fe));});return B(A3(_9f,B(_97(E(_f7).a)),function(_ff){return new F(function(){return A3(_7k,_fb,_ff,_fd);});},_f9));}),_fg=new T(function(){return B(A3(_9b,_fa,new T(function(){return B(A2(_91,_fb,_9K));}),_f8));});return new T2(0,_fg,_fc);},_fh=function(_fi,_fj,_fk){var _fl=E(_fk),_fm=B(_f6(_fj,_fl.a,_fl.b));return new T2(0,_fm.a,_fm.b);},_fn=function(_fo,_fp){return new T4(0,_fo,function(_ex,_ew){return new F(function(){return _eO(_fo,_fp,_ex,_ew);});},function(_ew){return new F(function(){return _fh(_fo,_fp,_ew);});},function(_ew){return new F(function(){return _f1(_fo,_fp,_ew);});});},_fq=function(_fr,_fs,_ft,_fu,_fv){var _fw=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fr).c).a);})));})));}),_fx=new T(function(){var _fy=E(_fr).a,_fz=new T(function(){var _fA=function(_fB,_fC){return new F(function(){return A3(_6I,_fw,new T(function(){return B(A3(_7k,_fw,_fs,_fC));}),new T(function(){return B(A3(_7k,_fw,_fB,_fu));}));});};return B(A3(_9f,B(_97(_fy)),_fA,_ft));});return B(A3(_9d,_fy,_fz,_fv));});return new T2(0,new T(function(){return B(A3(_7k,_fw,_fs,_fu));}),_fx);},_fD=function(_fE,_fF,_fG){var _fH=E(_fF),_fI=E(_fG),_fJ=B(_fq(_fE,_fH.a,_fH.b,_fI.a,_fI.b));return new T2(0,_fJ.a,_fJ.b);},_fK=function(_fL,_fM,_fN,_fO,_fP){var _fQ=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_fL).c).a);})));})));}),_fR=new T(function(){var _fS=E(_fL).a,_fT=new T(function(){return B(A3(_9f,B(_97(_fS)),new T(function(){return B(_6I(_fQ));}),_fN));});return B(A3(_9d,_fS,_fT,_fP));});return new T2(0,new T(function(){return B(A3(_6I,_fQ,_fM,_fO));}),_fR);},_fU=function(_fV,_fW,_fX){var _fY=E(_fW),_fZ=E(_fX),_g0=B(_fK(_fV,_fY.a,_fY.b,_fZ.a,_fZ.b));return new T2(0,_g0.a,_g0.b);},_g1=function(_g2,_g3,_g4){var _g5=B(_g6(_g2));return new F(function(){return A3(_6I,_g5,_g3,new T(function(){return B(A2(_6K,_g5,_g4));}));});},_g7=function(_g8){return E(E(_g8).e);},_g9=function(_ga){return E(E(_ga).f);},_gb=function(_gc,_gd,_ge){var _gf=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gc).c).a);})));})));}),_gg=new T(function(){var _gh=new T(function(){return B(A2(_g9,_gf,_gd));});return B(A3(_9f,B(_97(E(_gc).a)),function(_gi){return new F(function(){return A3(_7k,_gf,_gi,_gh);});},_ge));});return new T2(0,new T(function(){return B(A2(_g7,_gf,_gd));}),_gg);},_gj=function(_gk,_gl){var _gm=E(_gl),_gn=B(_gb(_gk,_gm.a,_gm.b));return new T2(0,_gn.a,_gn.b);},_go=function(_gp,_gq){var _gr=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gs=new T(function(){return B(A2(_cX,E(_gp).a,new T(function(){return B(A2(_91,_gr,_cU));})));});return new T2(0,new T(function(){return B(A2(_91,_gr,_gq));}),_gs);},_gt=function(_gu,_gv){var _gw=B(_go(_gu,_gv));return new T2(0,_gw.a,_gw.b);},_gx=function(_gy,_gz,_gA){var _gB=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gy).c).a);})));})));}),_gC=new T(function(){return B(A3(_9f,B(_97(E(_gy).a)),new T(function(){return B(_6K(_gB));}),_gA));});return new T2(0,new T(function(){return B(A2(_6K,_gB,_gz));}),_gC);},_gD=function(_gE,_gF){var _gG=E(_gF),_gH=B(_gx(_gE,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK){var _gL=new T(function(){return B(_7i(new T(function(){return B(_7g(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gM=new T(function(){return B(A2(_cX,E(_gJ).a,new T(function(){return B(A2(_91,_gL,_cU));})));});return new T2(0,new T(function(){return B(A2(_g9,_gL,_gK));}),_gM);},_gN=function(_gO,_gP){var _gQ=B(_gI(_gO,E(_gP).a));return new T2(0,_gQ.a,_gQ.b);},_g6=function(_gR){return {_:0,a:function(_ex,_ew){return new F(function(){return _fU(_gR,_ex,_ew);});},b:function(_ex,_ew){return new F(function(){return _g1(_gR,_ex,_ew);});},c:function(_ex,_ew){return new F(function(){return _fD(_gR,_ex,_ew);});},d:function(_ew){return new F(function(){return _gD(_gR,_ew);});},e:function(_ew){return new F(function(){return _gj(_gR,_ew);});},f:function(_ew){return new F(function(){return _gN(_gR,_ew);});},g:function(_ew){return new F(function(){return _gt(_gR,_ew);});}};},_gS=function(_gT){var _gU=new T(function(){return E(E(_gT).a);}),_gV=new T3(0,_8Z,_93,new T2(0,_gU,new T(function(){return E(E(_gT).b);}))),_gW=new T(function(){return B(_et(new T(function(){return B(_fn(new T(function(){return B(_g6(_gV));}),_gV));}),_gV));}),_gX=new T(function(){return B(_7i(new T(function(){return B(_7g(_gU));})));});return function(_gY){var _gZ=E(_gY),_h0=B(A2(_91,_gX,_7q)),_h1=B(A2(_91,_gX,_90));return E(B(_7y(_gW,new T2(0,_gZ.a,new T3(0,E(_h0),E(_h1),E(_h1))),new T2(0,_gZ.b,new T3(0,E(_h1),E(_h0),E(_h1))),new T2(0,_gZ.c,new T3(0,E(_h1),E(_h1),E(_h0))))).b);};},_h2=new T(function(){return B(_gS(_8v));}),_h3=function(_h4,_h5){var _h6=E(_h5);return (_h6._==0)?__Z:new T2(1,_h4,new T2(1,_h6.a,new T(function(){return B(_h3(_h4,_h6.b));})));},_h7=new T(function(){var _h8=B(A1(_h2,_84));return new T2(1,_h8.a,new T(function(){return B(_h3(_r,new T2(1,_h8.b,new T2(1,_h8.c,_o))));}));}),_h9=new T1(1,_h7),_ha=new T2(1,_h9,_w),_hb=new T(function(){return B(unCStr("vec3("));}),_hc=new T1(0,_hb),_hd=new T2(1,_hc,_ha),_he=new T(function(){return toJSStr(B(_7V(_p,_7S,_hd)));}),_hf=function(_hg,_hh){while(1){var _hi=E(_hg);if(!_hi._){return E(_hh);}else{var _hj=_hh+1|0;_hg=_hi.b;_hh=_hj;continue;}}},_hk=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hl=new T(function(){return B(err(_hk));}),_hm=0,_hn=new T3(0,E(_hm),E(_hm),E(_hm)),_ho=new T(function(){return B(unCStr("Negative exponent"));}),_hp=new T(function(){return B(err(_ho));}),_hq=function(_hr,_hs,_ht){while(1){if(!(_hs%2)){var _hu=_hr*_hr,_hv=quot(_hs,2);_hr=_hu;_hs=_hv;continue;}else{var _hw=E(_hs);if(_hw==1){return _hr*_ht;}else{var _hu=_hr*_hr,_hx=_hr*_ht;_hr=_hu;_hs=quot(_hw-1|0,2);_ht=_hx;continue;}}}},_hy=function(_hz,_hA){while(1){if(!(_hA%2)){var _hB=_hz*_hz,_hC=quot(_hA,2);_hz=_hB;_hA=_hC;continue;}else{var _hD=E(_hA);if(_hD==1){return E(_hz);}else{return new F(function(){return _hq(_hz*_hz,quot(_hD-1|0,2),_hz);});}}}},_hE=function(_hF){var _hG=E(_hF);return new F(function(){return Math.log(_hG+(_hG+1)*Math.sqrt((_hG-1)/(_hG+1)));});},_hH=function(_hI){var _hJ=E(_hI);return new F(function(){return Math.log(_hJ+Math.sqrt(1+_hJ*_hJ));});},_hK=function(_hL){var _hM=E(_hL);return 0.5*Math.log((1+_hM)/(1-_hM));},_hN=function(_hO,_hP){return Math.log(E(_hP))/Math.log(E(_hO));},_hQ=3.141592653589793,_hR=function(_hS){var _hT=E(_hS);return new F(function(){return _6j(_hT.a,_hT.b);});},_hU=function(_hV){return 1/E(_hV);},_hW=function(_hX){var _hY=E(_hX),_hZ=E(_hY);return (_hZ==0)?E(_6i):(_hZ<=0)? -_hZ:E(_hY);},_i0=function(_i1){var _i2=E(_i1);if(!_i2._){return _i2.a;}else{return new F(function(){return I_toNumber(_i2.a);});}},_i3=function(_i4){return new F(function(){return _i0(_i4);});},_i5=1,_i6=-1,_i7=function(_i8){var _i9=E(_i8);return (_i9<=0)?(_i9>=0)?E(_i9):E(_i6):E(_i5);},_ia=function(_ib,_ic){return E(_ib)-E(_ic);},_id=function(_ie){return  -E(_ie);},_if=function(_ig,_ih){return E(_ig)+E(_ih);},_ii=function(_ij,_ik){return E(_ij)*E(_ik);},_il={_:0,a:_if,b:_ia,c:_ii,d:_id,e:_hW,f:_i7,g:_i3},_im=function(_in,_io){return E(_in)/E(_io);},_ip=new T4(0,_il,_im,_hU,_hR),_iq=function(_ir){return new F(function(){return Math.acos(E(_ir));});},_is=function(_it){return new F(function(){return Math.asin(E(_it));});},_iu=function(_iv){return new F(function(){return Math.atan(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.cos(E(_ix));});},_iy=function(_iz){return new F(function(){return cosh(E(_iz));});},_iA=function(_iB){return new F(function(){return Math.exp(E(_iB));});},_iC=function(_iD){return new F(function(){return Math.log(E(_iD));});},_iE=function(_iF,_iG){return new F(function(){return Math.pow(E(_iF),E(_iG));});},_iH=function(_iI){return new F(function(){return Math.sin(E(_iI));});},_iJ=function(_iK){return new F(function(){return sinh(E(_iK));});},_iL=function(_iM){return new F(function(){return Math.sqrt(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.tan(E(_iO));});},_iP=function(_iQ){return new F(function(){return tanh(E(_iQ));});},_iR={_:0,a:_ip,b:_hQ,c:_iA,d:_iC,e:_iL,f:_iE,g:_hN,h:_iH,i:_iw,j:_iN,k:_is,l:_iq,m:_iu,n:_iJ,o:_iy,p:_iP,q:_hH,r:_hE,s:_hK},_iS=function(_iT,_iU){return (E(_iT)!=E(_iU))?true:false;},_iV=function(_iW,_iX){return E(_iW)==E(_iX);},_iY=new T2(0,_iV,_iS),_iZ=function(_j0,_j1){return E(_j0)<E(_j1);},_j2=function(_j3,_j4){return E(_j3)<=E(_j4);},_j5=function(_j6,_j7){return E(_j6)>E(_j7);},_j8=function(_j9,_ja){return E(_j9)>=E(_ja);},_jb=function(_jc,_jd){var _je=E(_jc),_jf=E(_jd);return (_je>=_jf)?(_je!=_jf)?2:1:0;},_jg=function(_jh,_ji){var _jj=E(_jh),_jk=E(_ji);return (_jj>_jk)?E(_jj):E(_jk);},_jl=function(_jm,_jn){var _jo=E(_jm),_jp=E(_jn);return (_jo>_jp)?E(_jp):E(_jo);},_jq={_:0,a:_iY,b:_jb,c:_iZ,d:_j2,e:_j5,f:_j8,g:_jg,h:_jl},_jr="dz",_js="wy",_jt="wx",_ju="dy",_jv="dx",_jw="t",_jx="a",_jy="r",_jz="ly",_jA="lx",_jB="wz",_jC=0,_jD=function(_jE){var _jF=__new(),_jG=_jF,_jH=function(_jI,_){while(1){var _jJ=E(_jI);if(!_jJ._){return _jC;}else{var _jK=E(_jJ.a),_jL=__set(_jG,E(_jK.a),E(_jK.b));_jI=_jJ.b;continue;}}},_jM=B(_jH(_jE,_));return E(_jG);},_jN=function(_jO,_jP,_jQ,_jR,_jS,_jT,_jU,_jV,_jW){return new F(function(){return _jD(new T2(1,new T2(0,_jt,_jO),new T2(1,new T2(0,_js,_jP),new T2(1,new T2(0,_jB,_jQ),new T2(1,new T2(0,_jA,_jR*_jS*Math.cos(_jT)),new T2(1,new T2(0,_jz,_jR*_jS*Math.sin(_jT)),new T2(1,new T2(0,_jy,_jR),new T2(1,new T2(0,_jx,_jS),new T2(1,new T2(0,_jw,_jT),new T2(1,new T2(0,_jv,_jU),new T2(1,new T2(0,_ju,_jV),new T2(1,new T2(0,_jr,_jW),_o))))))))))));});},_jX=function(_jY){var _jZ=E(_jY),_k0=E(_jZ.a),_k1=E(_jZ.b),_k2=E(_jZ.d);return new F(function(){return _jN(_k0.a,_k0.b,_k0.c,E(_k1.a),E(_k1.b),E(_jZ.c),_k2.a,_k2.b,_k2.c);});},_k3=function(_k4,_k5){var _k6=E(_k5);return (_k6._==0)?__Z:new T2(1,new T(function(){return B(A1(_k4,_k6.a));}),new T(function(){return B(_k3(_k4,_k6.b));}));},_k7=function(_k8,_k9,_ka){var _kb=__lst2arr(B(_k3(_jX,new T2(1,_k8,new T2(1,_k9,new T2(1,_ka,_o))))));return E(_kb);},_kc=function(_kd){var _ke=E(_kd);return new F(function(){return _k7(_ke.a,_ke.b,_ke.c);});},_kf=new T2(0,_iR,_jq),_kg=function(_kh,_ki,_kj,_kk,_kl,_km,_kn){var _ko=B(_7i(B(_7g(_kh)))),_kp=new T(function(){return B(A3(_6I,_ko,new T(function(){return B(A3(_7k,_ko,_ki,_kl));}),new T(function(){return B(A3(_7k,_ko,_kj,_km));})));});return new F(function(){return A3(_6I,_ko,_kp,new T(function(){return B(A3(_7k,_ko,_kk,_kn));}));});},_kq=function(_kr,_ks,_kt,_ku){var _kv=B(_7g(_kr)),_kw=new T(function(){return B(A2(_7w,_kr,new T(function(){return B(_kg(_kr,_ks,_kt,_ku,_ks,_kt,_ku));})));});return new T3(0,B(A3(_9b,_kv,_ks,_kw)),B(A3(_9b,_kv,_kt,_kw)),B(A3(_9b,_kv,_ku,_kw)));},_kx=function(_ky,_kz,_kA,_kB,_kC,_kD,_kE){var _kF=B(_7k(_ky));return new T3(0,B(A1(B(A1(_kF,_kz)),_kC)),B(A1(B(A1(_kF,_kA)),_kD)),B(A1(B(A1(_kF,_kB)),_kE)));},_kG=function(_kH,_kI,_kJ,_kK,_kL,_kM,_kN){var _kO=B(_6I(_kH));return new T3(0,B(A1(B(A1(_kO,_kI)),_kL)),B(A1(B(A1(_kO,_kJ)),_kM)),B(A1(B(A1(_kO,_kK)),_kN)));},_kP=function(_kQ,_kR){var _kS=new T(function(){return E(E(_kQ).a);}),_kT=new T(function(){return B(A2(_gS,new T2(0,_kS,new T(function(){return E(E(_kQ).b);})),_kR));}),_kU=new T(function(){var _kV=E(_kT),_kW=B(_kq(_kS,_kV.a,_kV.b,_kV.c));return new T3(0,E(_kW.a),E(_kW.b),E(_kW.c));}),_kX=new T(function(){var _kY=E(_kR),_kZ=_kY.a,_l0=_kY.b,_l1=_kY.c,_l2=E(_kU),_l3=B(_7g(_kS)),_l4=new T(function(){return B(A2(_7w,_kS,new T(function(){var _l5=E(_kT),_l6=_l5.a,_l7=_l5.b,_l8=_l5.c;return B(_kg(_kS,_l6,_l7,_l8,_l6,_l7,_l8));})));}),_l9=B(A3(_9b,_l3,new T(function(){return B(_7y(_kS,_kZ,_l0,_l1));}),_l4)),_la=B(_7i(_l3)),_lb=B(_kx(_la,_l2.a,_l2.b,_l2.c,_l9,_l9,_l9)),_lc=B(_6K(_la)),_ld=B(_kG(_la,_kZ,_l0,_l1,B(A1(_lc,_lb.a)),B(A1(_lc,_lb.b)),B(A1(_lc,_lb.c))));return new T3(0,E(_ld.a),E(_ld.b),E(_ld.c));});return new T2(0,_kX,_kU);},_le=function(_lf){return E(E(_lf).a);},_lg=function(_lh,_li,_lj,_lk,_ll,_lm,_ln){var _lo=B(_kg(_lh,_ll,_lm,_ln,_li,_lj,_lk)),_lp=B(_7i(B(_7g(_lh)))),_lq=B(_kx(_lp,_ll,_lm,_ln,_lo,_lo,_lo)),_lr=B(_6K(_lp));return new F(function(){return _kG(_lp,_li,_lj,_lk,B(A1(_lr,_lq.a)),B(A1(_lr,_lq.b)),B(A1(_lr,_lq.c)));});},_ls=function(_lt){return E(E(_lt).a);},_lu=function(_lv,_lw,_lx,_ly){var _lz=new T(function(){var _lA=E(_ly),_lB=E(_lx),_lC=B(_lg(_lv,_lA.a,_lA.b,_lA.c,_lB.a,_lB.b,_lB.c));return new T3(0,E(_lC.a),E(_lC.b),E(_lC.c));}),_lD=new T(function(){return B(A2(_7w,_lv,new T(function(){var _lE=E(_lz),_lF=_lE.a,_lG=_lE.b,_lH=_lE.c;return B(_kg(_lv,_lF,_lG,_lH,_lF,_lG,_lH));})));});if(!B(A3(_ls,B(_le(_lw)),_lD,new T(function(){return B(A2(_91,B(_7i(B(_7g(_lv)))),_90));})))){var _lI=E(_lz),_lJ=B(_kq(_lv,_lI.a,_lI.b,_lI.c)),_lK=B(A2(_7w,_lv,new T(function(){var _lL=E(_ly),_lM=_lL.a,_lN=_lL.b,_lO=_lL.c;return B(_kg(_lv,_lM,_lN,_lO,_lM,_lN,_lO));}))),_lP=B(_7k(new T(function(){return B(_7i(new T(function(){return B(_7g(_lv));})));})));return new T3(0,B(A1(B(A1(_lP,_lJ.a)),_lK)),B(A1(B(A1(_lP,_lJ.b)),_lK)),B(A1(B(A1(_lP,_lJ.c)),_lK)));}else{var _lQ=B(A2(_91,B(_7i(B(_7g(_lv)))),_90));return new T3(0,_lQ,_lQ,_lQ);}},_lR=new T(function(){var _lS=eval("angleCount"),_lT=Number(_lS);return jsTrunc(_lT);}),_lU=new T(function(){return E(_lR);}),_lV=new T(function(){return B(unCStr(": empty list"));}),_lW=new T(function(){return B(unCStr("Prelude."));}),_lX=function(_lY){return new F(function(){return err(B(_f(_lW,new T(function(){return B(_f(_lY,_lV));},1))));});},_lZ=new T(function(){return B(unCStr("head"));}),_m0=new T(function(){return B(_lX(_lZ));}),_m1=function(_m2,_m3,_m4){var _m5=E(_m2);if(!_m5._){return __Z;}else{var _m6=E(_m3);if(!_m6._){return __Z;}else{var _m7=_m6.a,_m8=E(_m4);if(!_m8._){return __Z;}else{var _m9=E(_m8.a),_ma=_m9.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_m5.a),E(_m7),E(_ma));}),new T2(1,new T(function(){return new T3(0,E(_m7),E(_ma),E(_m9.b));}),_o)),new T(function(){return B(_m1(_m5.b,_m6.b,_m8.b));},1));});}}}},_mb=new T(function(){return B(unCStr("tail"));}),_mc=new T(function(){return B(_lX(_mb));}),_md=function(_me,_mf){var _mg=E(_me);if(!_mg._){return __Z;}else{var _mh=E(_mf);return (_mh._==0)?__Z:new T2(1,new T2(0,_mg.a,_mh.a),new T(function(){return B(_md(_mg.b,_mh.b));}));}},_mi=function(_mj,_mk){var _ml=E(_mj);if(!_ml._){return __Z;}else{var _mm=E(_mk);if(!_mm._){return __Z;}else{var _mn=E(_ml.a),_mo=_mn.b,_mp=E(_mm.a).b,_mq=new T(function(){var _mr=new T(function(){return B(_md(_mp,new T(function(){var _ms=E(_mp);if(!_ms._){return E(_mc);}else{return E(_ms.b);}},1)));},1);return B(_m1(_mo,new T(function(){var _mt=E(_mo);if(!_mt._){return E(_mc);}else{return E(_mt.b);}},1),_mr));});return new F(function(){return _f(new T2(1,new T(function(){var _mu=E(_mo);if(!_mu._){return E(_m0);}else{var _mv=E(_mp);if(!_mv._){return E(_m0);}else{return new T3(0,E(_mn.a),E(_mu.a),E(_mv.a));}}}),_mq),new T(function(){return B(_mi(_ml.b,_mm.b));},1));});}}},_mw=new T(function(){return E(_lU)-1;}),_mx=new T1(0,1),_my=function(_mz,_mA){var _mB=E(_mA),_mC=new T(function(){var _mD=B(_7i(_mz)),_mE=B(_my(_mz,B(A3(_6I,_mD,_mB,new T(function(){return B(A2(_91,_mD,_mx));})))));return new T2(1,_mE.a,_mE.b);});return new T2(0,_mB,_mC);},_mF=function(_mG){return E(E(_mG).d);},_mH=new T1(0,2),_mI=function(_mJ,_mK){var _mL=E(_mK);if(!_mL._){return __Z;}else{var _mM=_mL.a;return (!B(A1(_mJ,_mM)))?__Z:new T2(1,_mM,new T(function(){return B(_mI(_mJ,_mL.b));}));}},_mN=function(_mO,_mP,_mQ,_mR){var _mS=B(_my(_mP,_mQ)),_mT=new T(function(){var _mU=B(_7i(_mP)),_mV=new T(function(){return B(A3(_9b,_mP,new T(function(){return B(A2(_91,_mU,_mx));}),new T(function(){return B(A2(_91,_mU,_mH));})));});return B(A3(_6I,_mU,_mR,_mV));});return new F(function(){return _mI(function(_mW){return new F(function(){return A3(_mF,_mO,_mW,_mT);});},new T2(1,_mS.a,_mS.b));});},_mX=new T(function(){return B(_mN(_jq,_ip,_hm,_mw));}),_mY=function(_mZ,_n0){while(1){var _n1=E(_mZ);if(!_n1._){return E(_n0);}else{_mZ=_n1.b;_n0=_n1.a;continue;}}},_n2=new T(function(){return B(unCStr("last"));}),_n3=new T(function(){return B(_lX(_n2));}),_n4=function(_n5){return new F(function(){return _mY(_n5,_n3);});},_n6=function(_n7){return new F(function(){return _n4(E(_n7).b);});},_n8=new T(function(){var _n9=eval("proceedCount"),_na=Number(_n9);return jsTrunc(_na);}),_nb=new T(function(){return E(_n8);}),_nc=1,_nd=new T(function(){return B(_mN(_jq,_ip,_nc,_nb));}),_ne=function(_nf,_ng,_nh,_ni,_nj,_nk,_nl,_nm,_nn,_no,_np,_nq,_nr,_ns){var _nt=new T(function(){var _nu=new T(function(){var _nv=E(_no),_nw=E(_ns),_nx=E(_nr),_ny=E(_np),_nz=E(_nq),_nA=E(_nn);return new T3(0,_nv*_nw-_nx*_ny,_ny*_nz-_nw*_nA,_nA*_nx-_nz*_nv);}),_nB=function(_nC){var _nD=new T(function(){var _nE=E(_nC)/E(_lU);return (_nE+_nE)*3.141592653589793;}),_nF=new T(function(){return B(A1(_nf,_nD));}),_nG=new T(function(){var _nH=new T(function(){var _nI=E(_nF)/E(_nb);return new T3(0,E(_nI),E(_nI),E(_nI));}),_nJ=function(_nK,_nL){var _nM=E(_nK);if(!_nM._){return new T2(0,_o,_nL);}else{var _nN=new T(function(){var _nO=B(_kP(_kf,new T(function(){var _nP=E(_nL),_nQ=E(_nP.a),_nR=E(_nP.b),_nS=E(_nH);return new T3(0,E(_nQ.a)+E(_nR.a)*E(_nS.a),E(_nQ.b)+E(_nR.b)*E(_nS.b),E(_nQ.c)+E(_nR.c)*E(_nS.c));}))),_nT=_nO.a,_nU=new T(function(){var _nV=E(_nO.b),_nW=E(E(_nL).b),_nX=B(_lg(_iR,_nW.a,_nW.b,_nW.c,_nV.a,_nV.b,_nV.c)),_nY=B(_kq(_iR,_nX.a,_nX.b,_nX.c));return new T3(0,E(_nY.a),E(_nY.b),E(_nY.c));});return new T2(0,new T(function(){var _nZ=E(_nF),_o0=E(_nD);return new T4(0,E(_nT),E(new T2(0,E(_nM.a)/E(_nb),E(_nZ))),E(_o0),E(_nU));}),new T2(0,_nT,_nU));}),_o1=new T(function(){var _o2=B(_nJ(_nM.b,new T(function(){return E(E(_nN).b);})));return new T2(0,_o2.a,_o2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nN).a);}),new T(function(){return E(E(_o1).a);})),new T(function(){return E(E(_o1).b);}));}},_o3=function(_o4,_o5,_o6,_o7,_o8){var _o9=E(_o4);if(!_o9._){return new T2(0,_o,new T2(0,new T3(0,E(_o5),E(_o6),E(_o7)),_o8));}else{var _oa=new T(function(){var _ob=B(_kP(_kf,new T(function(){var _oc=E(_o8),_od=E(_nH);return new T3(0,E(_o5)+E(_oc.a)*E(_od.a),E(_o6)+E(_oc.b)*E(_od.b),E(_o7)+E(_oc.c)*E(_od.c));}))),_oe=_ob.a,_of=new T(function(){var _og=E(_ob.b),_oh=E(_o8),_oi=B(_lg(_iR,_oh.a,_oh.b,_oh.c,_og.a,_og.b,_og.c)),_oj=B(_kq(_iR,_oi.a,_oi.b,_oi.c));return new T3(0,E(_oj.a),E(_oj.b),E(_oj.c));});return new T2(0,new T(function(){var _ok=E(_nF),_ol=E(_nD);return new T4(0,E(_oe),E(new T2(0,E(_o9.a)/E(_nb),E(_ok))),E(_ol),E(_of));}),new T2(0,_oe,_of));}),_om=new T(function(){var _on=B(_nJ(_o9.b,new T(function(){return E(E(_oa).b);})));return new T2(0,_on.a,_on.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oa).a);}),new T(function(){return E(E(_om).a);})),new T(function(){return E(E(_om).b);}));}};return E(B(_o3(_nd,_ni,_nj,_nk,new T(function(){var _oo=E(_nu),_op=E(_nD)+_nl,_oq=Math.cos(_op),_or=Math.sin(_op);return new T3(0,E(_nn)*_oq+E(_oo.a)*_or,E(_no)*_oq+E(_oo.b)*_or,E(_np)*_oq+E(_oo.c)*_or);}))).a);});return new T2(0,new T(function(){var _os=E(_nF),_ot=E(_nD);return new T4(0,E(new T3(0,E(_ni),E(_nj),E(_nk))),E(new T2(0,E(_hm),E(_os))),E(_ot),E(_hn));}),_nG);};return B(_k3(_nB,_mX));}),_ou=new T(function(){var _ov=new T(function(){var _ow=B(_f(_nt,new T2(1,new T(function(){var _ox=E(_nt);if(!_ox._){return E(_m0);}else{return E(_ox.a);}}),_o)));if(!_ow._){return E(_mc);}else{return E(_ow.b);}},1);return B(_mi(_nt,_ov));});return new T2(0,_ou,new T(function(){return B(_k3(_n6,_nt));}));},_oy=function(_oz,_oA,_oB,_oC,_oD,_oE,_oF,_oG,_oH,_oI,_oJ,_oK,_oL,_oM,_oN,_oO,_oP){var _oQ=B(_kP(_kf,new T3(0,E(_oC),E(_oD),E(_oE)))),_oR=_oQ.b,_oS=E(_oQ.a),_oT=B(_lu(_iR,_jq,_oR,new T3(0,E(_oG),E(_oH),E(_oI)))),_oU=E(_oR),_oV=_oU.a,_oW=_oU.b,_oX=_oU.c,_oY=B(_lg(_iR,_oK,_oL,_oM,_oV,_oW,_oX)),_oZ=B(_kq(_iR,_oY.a,_oY.b,_oY.c)),_p0=_oZ.a,_p1=_oZ.b,_p2=_oZ.c,_p3=E(_oF),_p4=new T2(0,E(new T3(0,E(_oT.a),E(_oT.b),E(_oT.c))),E(_oJ)),_p5=B(_ne(_oz,_oA,_oB,_oS.a,_oS.b,_oS.c,_p3,_p4,_p0,_p1,_p2,_oV,_oW,_oX)),_p6=__lst2arr(B(_k3(_kc,_p5.a))),_p7=__lst2arr(B(_k3(_jX,_p5.b)));return {_:0,a:_oz,b:_oA,c:_oB,d:new T2(0,E(_oS),E(_p3)),e:_p4,f:new T3(0,E(_p0),E(_p1),E(_p2)),g:_oU,h:_p6,i:_p7};},_p8=new T(function(){return 6.283185307179586/E(_lU);}),_p9=-1,_pa=0.5,_pb=new T3(0,E(_hm),E(_pa),E(_p9)),_pc=function(_){return new F(function(){return __jsNull();});},_pd=function(_pe){var _pf=B(A1(_pe,_));return E(_pf);},_pg=new T(function(){return B(_pd(_pc));}),_ph=function(_pi,_pj,_pk,_pl,_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt,_pu){var _pv=function(_pw){var _px=E(_p8),_py=2+_pw|0,_pz=_py-1|0,_pA=(2+_pw)*(1+_pw),_pB=E(_mX);if(!_pB._){return _px*0;}else{var _pC=_pB.a,_pD=_pB.b,_pE=B(A1(_pi,new T(function(){return 6.283185307179586*E(_pC)/E(_lU);}))),_pF=B(A1(_pi,new T(function(){return 6.283185307179586*(E(_pC)+1)/E(_lU);})));if(_pE!=_pF){if(_py>=0){var _pG=E(_py);if(!_pG){var _pH=function(_pI,_pJ){while(1){var _pK=B((function(_pL,_pM){var _pN=E(_pL);if(!_pN._){return E(_pM);}else{var _pO=_pN.a,_pP=_pN.b,_pQ=B(A1(_pi,new T(function(){return 6.283185307179586*E(_pO)/E(_lU);}))),_pR=B(A1(_pi,new T(function(){return 6.283185307179586*(E(_pO)+1)/E(_lU);})));if(_pQ!=_pR){var _pS=_pM+0/(_pQ-_pR)/_pA;_pI=_pP;_pJ=_pS;return __continue;}else{if(_pz>=0){var _pT=E(_pz);if(!_pT){var _pS=_pM+_py/_pA;_pI=_pP;_pJ=_pS;return __continue;}else{var _pS=_pM+_py*B(_hy(_pQ,_pT))/_pA;_pI=_pP;_pJ=_pS;return __continue;}}else{return E(_hp);}}}})(_pI,_pJ));if(_pK!=__continue){return _pK;}}};return _px*B(_pH(_pD,0/(_pE-_pF)/_pA));}else{var _pU=function(_pV,_pW){while(1){var _pX=B((function(_pY,_pZ){var _q0=E(_pY);if(!_q0._){return E(_pZ);}else{var _q1=_q0.a,_q2=_q0.b,_q3=B(A1(_pi,new T(function(){return 6.283185307179586*E(_q1)/E(_lU);}))),_q4=B(A1(_pi,new T(function(){return 6.283185307179586*(E(_q1)+1)/E(_lU);})));if(_q3!=_q4){if(_pG>=0){var _q5=_pZ+(B(_hy(_q3,_pG))-B(_hy(_q4,_pG)))/(_q3-_q4)/_pA;_pV=_q2;_pW=_q5;return __continue;}else{return E(_hp);}}else{if(_pz>=0){var _q6=E(_pz);if(!_q6){var _q5=_pZ+_py/_pA;_pV=_q2;_pW=_q5;return __continue;}else{var _q5=_pZ+_py*B(_hy(_q3,_q6))/_pA;_pV=_q2;_pW=_q5;return __continue;}}else{return E(_hp);}}}})(_pV,_pW));if(_pX!=__continue){return _pX;}}};return _px*B(_pU(_pD,(B(_hy(_pE,_pG))-B(_hy(_pF,_pG)))/(_pE-_pF)/_pA));}}else{return E(_hp);}}else{if(_pz>=0){var _q7=E(_pz);if(!_q7){var _q8=function(_q9,_qa){while(1){var _qb=B((function(_qc,_qd){var _qe=E(_qc);if(!_qe._){return E(_qd);}else{var _qf=_qe.a,_qg=_qe.b,_qh=B(A1(_pi,new T(function(){return 6.283185307179586*E(_qf)/E(_lU);}))),_qi=B(A1(_pi,new T(function(){return 6.283185307179586*(E(_qf)+1)/E(_lU);})));if(_qh!=_qi){if(_py>=0){var _qj=E(_py);if(!_qj){var _qk=_qd+0/(_qh-_qi)/_pA;_q9=_qg;_qa=_qk;return __continue;}else{var _qk=_qd+(B(_hy(_qh,_qj))-B(_hy(_qi,_qj)))/(_qh-_qi)/_pA;_q9=_qg;_qa=_qk;return __continue;}}else{return E(_hp);}}else{var _qk=_qd+_py/_pA;_q9=_qg;_qa=_qk;return __continue;}}})(_q9,_qa));if(_qb!=__continue){return _qb;}}};return _px*B(_q8(_pD,_py/_pA));}else{var _ql=function(_qm,_qn){while(1){var _qo=B((function(_qp,_qq){var _qr=E(_qp);if(!_qr._){return E(_qq);}else{var _qs=_qr.a,_qt=_qr.b,_qu=B(A1(_pi,new T(function(){return 6.283185307179586*E(_qs)/E(_lU);}))),_qv=B(A1(_pi,new T(function(){return 6.283185307179586*(E(_qs)+1)/E(_lU);})));if(_qu!=_qv){if(_py>=0){var _qw=E(_py);if(!_qw){var _qx=_qq+0/(_qu-_qv)/_pA;_qm=_qt;_qn=_qx;return __continue;}else{var _qx=_qq+(B(_hy(_qu,_qw))-B(_hy(_qv,_qw)))/(_qu-_qv)/_pA;_qm=_qt;_qn=_qx;return __continue;}}else{return E(_hp);}}else{if(_q7>=0){var _qx=_qq+_py*B(_hy(_qu,_q7))/_pA;_qm=_qt;_qn=_qx;return __continue;}else{return E(_hp);}}}})(_qm,_qn));if(_qo!=__continue){return _qo;}}};return _px*B(_ql(_pD,_py*B(_hy(_pE,_q7))/_pA));}}else{return E(_hp);}}}},_qy=E(_pg),_qz=1/(B(_pv(1))*_pj);return new F(function(){return _oy(_pi,_pb,new T2(0,E(new T3(0,E(_qz),E(_qz),E(_qz))),1/(B(_pv(3))*_pj)),_pk,_pl,_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt,_pu,_hn,_qy,_qy);});},_qA=0,_qB=0.5,_qC=-0.8,_qD=0.2,_qE=function(_qF){return E(_qD);},_qG=1,_qH=0.3,_qI=new T(function(){var _qJ=B(_ph(_qE,1.2,_qC,_qB,_qA,_qA,_qA,_qA,_qH,_qA,_qA,_qA,_qG));return {_:0,a:E(_qJ.a),b:E(_qJ.b),c:E(_qJ.c),d:E(_qJ.d),e:E(_qJ.e),f:E(_qJ.f),g:E(_qJ.g),h:_qJ.h,i:_qJ.i};}),_qK=0,_qL=-0.1,_qM=1.3,_qN=function(_qO){var _qP=I_decodeDouble(_qO);return new T2(0,new T1(1,_qP.b),_qP.a);},_qQ=function(_qR){return new T1(0,_qR);},_qS=function(_qT){var _qU=hs_intToInt64(2147483647),_qV=hs_leInt64(_qT,_qU);if(!_qV){return new T1(1,I_fromInt64(_qT));}else{var _qW=hs_intToInt64(-2147483648),_qX=hs_geInt64(_qT,_qW);if(!_qX){return new T1(1,I_fromInt64(_qT));}else{var _qY=hs_int64ToInt(_qT);return new F(function(){return _qQ(_qY);});}}},_qZ=new T(function(){var _r0=newByteArr(256),_r1=_r0,_=_r1["v"]["i8"][0]=8,_r2=function(_r3,_r4,_r5,_){while(1){if(_r5>=256){if(_r3>=256){return E(_);}else{var _r6=imul(2,_r3)|0,_r7=_r4+1|0,_r8=_r3;_r3=_r6;_r4=_r7;_r5=_r8;continue;}}else{var _=_r1["v"]["i8"][_r5]=_r4,_r8=_r5+_r3|0;_r5=_r8;continue;}}},_=B(_r2(2,0,1,_));return _r1;}),_r9=function(_ra,_rb){var _rc=hs_int64ToInt(_ra),_rd=E(_qZ),_re=_rd["v"]["i8"][(255&_rc>>>0)>>>0&4294967295];if(_rb>_re){if(_re>=8){var _rf=hs_uncheckedIShiftRA64(_ra,8),_rg=function(_rh,_ri){while(1){var _rj=B((function(_rk,_rl){var _rm=hs_int64ToInt(_rk),_rn=_rd["v"]["i8"][(255&_rm>>>0)>>>0&4294967295];if(_rl>_rn){if(_rn>=8){var _ro=hs_uncheckedIShiftRA64(_rk,8),_rp=_rl-8|0;_rh=_ro;_ri=_rp;return __continue;}else{return new T2(0,new T(function(){var _rq=hs_uncheckedIShiftRA64(_rk,_rn);return B(_qS(_rq));}),_rl-_rn|0);}}else{return new T2(0,new T(function(){var _rr=hs_uncheckedIShiftRA64(_rk,_rl);return B(_qS(_rr));}),0);}})(_rh,_ri));if(_rj!=__continue){return _rj;}}};return new F(function(){return _rg(_rf,_rb-8|0);});}else{return new T2(0,new T(function(){var _rs=hs_uncheckedIShiftRA64(_ra,_re);return B(_qS(_rs));}),_rb-_re|0);}}else{return new T2(0,new T(function(){var _rt=hs_uncheckedIShiftRA64(_ra,_rb);return B(_qS(_rt));}),0);}},_ru=function(_rv){var _rw=hs_intToInt64(_rv);return E(_rw);},_rx=function(_ry){var _rz=E(_ry);if(!_rz._){return new F(function(){return _ru(_rz.a);});}else{return new F(function(){return I_toInt64(_rz.a);});}},_rA=function(_rB){return I_toInt(_rB)>>>0;},_rC=function(_rD){var _rE=E(_rD);if(!_rE._){return _rE.a>>>0;}else{return new F(function(){return _rA(_rE.a);});}},_rF=function(_rG){var _rH=B(_qN(_rG)),_rI=_rH.a,_rJ=_rH.b;if(_rJ<0){var _rK=function(_rL){if(!_rL){return new T2(0,E(_rI),B(_3u(_1M, -_rJ)));}else{var _rM=B(_r9(B(_rx(_rI)), -_rJ));return new T2(0,E(_rM.a),B(_3u(_1M,_rM.b)));}};if(!((B(_rC(_rI))&1)>>>0)){return new F(function(){return _rK(1);});}else{return new F(function(){return _rK(0);});}}else{return new T2(0,B(_3u(_rI,_rJ)),_1M);}},_rN=function(_rO){var _rP=B(_rF(E(_rO)));return new T2(0,E(_rP.a),E(_rP.b));},_rQ=new T3(0,_il,_jq,_rN),_rR=function(_rS){return E(E(_rS).a);},_rT=function(_rU){return E(E(_rU).a);},_rV=function(_rW,_rX){if(_rW<=_rX){var _rY=function(_rZ){return new T2(1,_rZ,new T(function(){if(_rZ!=_rX){return B(_rY(_rZ+1|0));}else{return __Z;}}));};return new F(function(){return _rY(_rW);});}else{return __Z;}},_s0=function(_s1){return new F(function(){return _rV(E(_s1),2147483647);});},_s2=function(_s3,_s4,_s5){if(_s5<=_s4){var _s6=new T(function(){var _s7=_s4-_s3|0,_s8=function(_s9){return (_s9>=(_s5-_s7|0))?new T2(1,_s9,new T(function(){return B(_s8(_s9+_s7|0));})):new T2(1,_s9,_o);};return B(_s8(_s4));});return new T2(1,_s3,_s6);}else{return (_s5<=_s3)?new T2(1,_s3,_o):__Z;}},_sa=function(_sb,_sc,_sd){if(_sd>=_sc){var _se=new T(function(){var _sf=_sc-_sb|0,_sg=function(_sh){return (_sh<=(_sd-_sf|0))?new T2(1,_sh,new T(function(){return B(_sg(_sh+_sf|0));})):new T2(1,_sh,_o);};return B(_sg(_sc));});return new T2(1,_sb,_se);}else{return (_sd>=_sb)?new T2(1,_sb,_o):__Z;}},_si=function(_sj,_sk){if(_sk<_sj){return new F(function(){return _s2(_sj,_sk,-2147483648);});}else{return new F(function(){return _sa(_sj,_sk,2147483647);});}},_sl=function(_sm,_sn){return new F(function(){return _si(E(_sm),E(_sn));});},_so=function(_sp,_sq,_sr){if(_sq<_sp){return new F(function(){return _s2(_sp,_sq,_sr);});}else{return new F(function(){return _sa(_sp,_sq,_sr);});}},_ss=function(_st,_su,_sv){return new F(function(){return _so(E(_st),E(_su),E(_sv));});},_sw=function(_sx,_sy){return new F(function(){return _rV(E(_sx),E(_sy));});},_sz=function(_sA){return E(_sA);},_sB=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_sC=new T(function(){return B(err(_sB));}),_sD=function(_sE){var _sF=E(_sE);return (_sF==(-2147483648))?E(_sC):_sF-1|0;},_sG=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_sH=new T(function(){return B(err(_sG));}),_sI=function(_sJ){var _sK=E(_sJ);return (_sK==2147483647)?E(_sH):_sK+1|0;},_sL={_:0,a:_sI,b:_sD,c:_sz,d:_sz,e:_s0,f:_sl,g:_sw,h:_ss},_sM=function(_sN,_sO){if(_sN<=0){if(_sN>=0){return new F(function(){return quot(_sN,_sO);});}else{if(_sO<=0){return new F(function(){return quot(_sN,_sO);});}else{return quot(_sN+1|0,_sO)-1|0;}}}else{if(_sO>=0){if(_sN>=0){return new F(function(){return quot(_sN,_sO);});}else{if(_sO<=0){return new F(function(){return quot(_sN,_sO);});}else{return quot(_sN+1|0,_sO)-1|0;}}}else{return quot(_sN-1|0,_sO)-1|0;}}},_sP=0,_sQ=new T(function(){return B(_2R(_sP));}),_sR=new T(function(){return die(_sQ);}),_sS=function(_sT,_sU){var _sV=E(_sU);switch(_sV){case -1:var _sW=E(_sT);if(_sW==(-2147483648)){return E(_sR);}else{return new F(function(){return _sM(_sW,-1);});}break;case 0:return E(_2V);default:return new F(function(){return _sM(_sT,_sV);});}},_sX=function(_sY,_sZ){return new F(function(){return _sS(E(_sY),E(_sZ));});},_t0=0,_t1=new T2(0,_sR,_t0),_t2=function(_t3,_t4){var _t5=E(_t3),_t6=E(_t4);switch(_t6){case -1:var _t7=E(_t5);if(_t7==(-2147483648)){return E(_t1);}else{if(_t7<=0){if(_t7>=0){var _t8=quotRemI(_t7,-1);return new T2(0,_t8.a,_t8.b);}else{var _t9=quotRemI(_t7,-1);return new T2(0,_t9.a,_t9.b);}}else{var _ta=quotRemI(_t7-1|0,-1);return new T2(0,_ta.a-1|0,(_ta.b+(-1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_t5<=0){if(_t5>=0){var _tb=quotRemI(_t5,_t6);return new T2(0,_tb.a,_tb.b);}else{if(_t6<=0){var _tc=quotRemI(_t5,_t6);return new T2(0,_tc.a,_tc.b);}else{var _td=quotRemI(_t5+1|0,_t6);return new T2(0,_td.a-1|0,(_td.b+_t6|0)-1|0);}}}else{if(_t6>=0){if(_t5>=0){var _te=quotRemI(_t5,_t6);return new T2(0,_te.a,_te.b);}else{if(_t6<=0){var _tf=quotRemI(_t5,_t6);return new T2(0,_tf.a,_tf.b);}else{var _tg=quotRemI(_t5+1|0,_t6);return new T2(0,_tg.a-1|0,(_tg.b+_t6|0)-1|0);}}}else{var _th=quotRemI(_t5-1|0,_t6);return new T2(0,_th.a-1|0,(_th.b+_t6|0)+1|0);}}}},_ti=function(_tj,_tk){var _tl=_tj%_tk;if(_tj<=0){if(_tj>=0){return E(_tl);}else{if(_tk<=0){return E(_tl);}else{var _tm=E(_tl);return (_tm==0)?0:_tm+_tk|0;}}}else{if(_tk>=0){if(_tj>=0){return E(_tl);}else{if(_tk<=0){return E(_tl);}else{var _tn=E(_tl);return (_tn==0)?0:_tn+_tk|0;}}}else{var _to=E(_tl);return (_to==0)?0:_to+_tk|0;}}},_tp=function(_tq,_tr){var _ts=E(_tr);switch(_ts){case -1:return E(_t0);case 0:return E(_2V);default:return new F(function(){return _ti(E(_tq),_ts);});}},_tt=function(_tu,_tv){var _tw=E(_tu),_tx=E(_tv);switch(_tx){case -1:var _ty=E(_tw);if(_ty==(-2147483648)){return E(_sR);}else{return new F(function(){return quot(_ty,-1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_tw,_tx);});}},_tz=function(_tA,_tB){var _tC=E(_tA),_tD=E(_tB);switch(_tD){case -1:var _tE=E(_tC);if(_tE==(-2147483648)){return E(_t1);}else{var _tF=quotRemI(_tE,-1);return new T2(0,_tF.a,_tF.b);}break;case 0:return E(_2V);default:var _tG=quotRemI(_tC,_tD);return new T2(0,_tG.a,_tG.b);}},_tH=function(_tI,_tJ){var _tK=E(_tJ);switch(_tK){case -1:return E(_t0);case 0:return E(_2V);default:return E(_tI)%_tK;}},_tL=function(_tM){return new F(function(){return _qQ(E(_tM));});},_tN=function(_tO){return new T2(0,E(B(_qQ(E(_tO)))),E(_mx));},_tP=function(_tQ,_tR){return imul(E(_tQ),E(_tR))|0;},_tS=function(_tT,_tU){return E(_tT)+E(_tU)|0;},_tV=function(_tW,_tX){return E(_tW)-E(_tX)|0;},_tY=function(_tZ){var _u0=E(_tZ);return (_u0<0)? -_u0:E(_u0);},_u1=function(_u2){return new F(function(){return _38(_u2);});},_u3=function(_u4){return  -E(_u4);},_u5=-1,_u6=0,_u7=1,_u8=function(_u9){var _ua=E(_u9);return (_ua>=0)?(E(_ua)==0)?E(_u6):E(_u7):E(_u5);},_ub={_:0,a:_tS,b:_tV,c:_tP,d:_u3,e:_tY,f:_u8,g:_u1},_uc=function(_ud,_ue){return E(_ud)==E(_ue);},_uf=function(_ug,_uh){return E(_ug)!=E(_uh);},_ui=new T2(0,_uc,_uf),_uj=function(_uk,_ul){var _um=E(_uk),_un=E(_ul);return (_um>_un)?E(_um):E(_un);},_uo=function(_up,_uq){var _ur=E(_up),_us=E(_uq);return (_ur>_us)?E(_us):E(_ur);},_ut=function(_uu,_uv){return (_uu>=_uv)?(_uu!=_uv)?2:1:0;},_uw=function(_ux,_uy){return new F(function(){return _ut(E(_ux),E(_uy));});},_uz=function(_uA,_uB){return E(_uA)>=E(_uB);},_uC=function(_uD,_uE){return E(_uD)>E(_uE);},_uF=function(_uG,_uH){return E(_uG)<=E(_uH);},_uI=function(_uJ,_uK){return E(_uJ)<E(_uK);},_uL={_:0,a:_ui,b:_uw,c:_uI,d:_uF,e:_uC,f:_uz,g:_uj,h:_uo},_uM=new T3(0,_ub,_uL,_tN),_uN={_:0,a:_uM,b:_sL,c:_tt,d:_tH,e:_sX,f:_tp,g:_tz,h:_t2,i:_tL},_uO=new T1(0,2),_uP=function(_uQ,_uR){while(1){var _uS=E(_uQ);if(!_uS._){var _uT=_uS.a,_uU=E(_uR);if(!_uU._){var _uV=_uU.a;if(!(imul(_uT,_uV)|0)){return new T1(0,imul(_uT,_uV)|0);}else{_uQ=new T1(1,I_fromInt(_uT));_uR=new T1(1,I_fromInt(_uV));continue;}}else{_uQ=new T1(1,I_fromInt(_uT));_uR=_uU;continue;}}else{var _uW=E(_uR);if(!_uW._){_uQ=_uS;_uR=new T1(1,I_fromInt(_uW.a));continue;}else{return new T1(1,I_mul(_uS.a,_uW.a));}}}},_uX=function(_uY,_uZ,_v0){while(1){if(!(_uZ%2)){var _v1=B(_uP(_uY,_uY)),_v2=quot(_uZ,2);_uY=_v1;_uZ=_v2;continue;}else{var _v3=E(_uZ);if(_v3==1){return new F(function(){return _uP(_uY,_v0);});}else{var _v1=B(_uP(_uY,_uY)),_v4=B(_uP(_uY,_v0));_uY=_v1;_uZ=quot(_v3-1|0,2);_v0=_v4;continue;}}}},_v5=function(_v6,_v7){while(1){if(!(_v7%2)){var _v8=B(_uP(_v6,_v6)),_v9=quot(_v7,2);_v6=_v8;_v7=_v9;continue;}else{var _va=E(_v7);if(_va==1){return E(_v6);}else{return new F(function(){return _uX(B(_uP(_v6,_v6)),quot(_va-1|0,2),_v6);});}}}},_vb=function(_vc){return E(E(_vc).b);},_vd=function(_ve){return E(E(_ve).c);},_vf=new T1(0,0),_vg=function(_vh){return E(E(_vh).d);},_vi=function(_vj,_vk){var _vl=B(_rR(_vj)),_vm=new T(function(){return B(_rT(_vl));}),_vn=new T(function(){return B(A3(_vg,_vj,_vk,new T(function(){return B(A2(_91,_vm,_mH));})));});return new F(function(){return A3(_ls,B(_le(B(_vb(_vl)))),_vn,new T(function(){return B(A2(_91,_vm,_vf));}));});},_vo=new T(function(){return B(unCStr("Negative exponent"));}),_vp=new T(function(){return B(err(_vo));}),_vq=function(_vr){return E(E(_vr).c);},_vs=function(_vt,_vu,_vv,_vw){var _vx=B(_rR(_vu)),_vy=new T(function(){return B(_rT(_vx));}),_vz=B(_vb(_vx));if(!B(A3(_vd,_vz,_vw,new T(function(){return B(A2(_91,_vy,_vf));})))){if(!B(A3(_ls,B(_le(_vz)),_vw,new T(function(){return B(A2(_91,_vy,_vf));})))){var _vA=new T(function(){return B(A2(_91,_vy,_mH));}),_vB=new T(function(){return B(A2(_91,_vy,_mx));}),_vC=B(_le(_vz)),_vD=function(_vE,_vF,_vG){while(1){var _vH=B((function(_vI,_vJ,_vK){if(!B(_vi(_vu,_vJ))){if(!B(A3(_ls,_vC,_vJ,_vB))){var _vL=new T(function(){return B(A3(_vq,_vu,new T(function(){return B(A3(_7m,_vy,_vJ,_vB));}),_vA));});_vE=new T(function(){return B(A3(_7k,_vt,_vI,_vI));});_vF=_vL;_vG=new T(function(){return B(A3(_7k,_vt,_vI,_vK));});return __continue;}else{return new F(function(){return A3(_7k,_vt,_vI,_vK);});}}else{var _vM=_vK;_vE=new T(function(){return B(A3(_7k,_vt,_vI,_vI));});_vF=new T(function(){return B(A3(_vq,_vu,_vJ,_vA));});_vG=_vM;return __continue;}})(_vE,_vF,_vG));if(_vH!=__continue){return _vH;}}},_vN=function(_vO,_vP){while(1){var _vQ=B((function(_vR,_vS){if(!B(_vi(_vu,_vS))){if(!B(A3(_ls,_vC,_vS,_vB))){var _vT=new T(function(){return B(A3(_vq,_vu,new T(function(){return B(A3(_7m,_vy,_vS,_vB));}),_vA));});return new F(function(){return _vD(new T(function(){return B(A3(_7k,_vt,_vR,_vR));}),_vT,_vR);});}else{return E(_vR);}}else{_vO=new T(function(){return B(A3(_7k,_vt,_vR,_vR));});_vP=new T(function(){return B(A3(_vq,_vu,_vS,_vA));});return __continue;}})(_vO,_vP));if(_vQ!=__continue){return _vQ;}}};return new F(function(){return _vN(_vv,_vw);});}else{return new F(function(){return A2(_91,_vt,_mx);});}}else{return E(_vp);}},_vU=new T(function(){return B(err(_vo));}),_vV=function(_vW,_vX){var _vY=B(_qN(_vX)),_vZ=_vY.a,_w0=_vY.b,_w1=new T(function(){return B(_rT(new T(function(){return B(_rR(_vW));})));});if(_w0<0){var _w2= -_w0;if(_w2>=0){var _w3=E(_w2);if(!_w3){var _w4=E(_mx);}else{var _w4=B(_v5(_uO,_w3));}if(!B(_30(_w4,_3t))){var _w5=B(_3k(_vZ,_w4));return new T2(0,new T(function(){return B(A2(_91,_w1,_w5.a));}),new T(function(){return B(_2W(_w5.b,_w0));}));}else{return E(_2V);}}else{return E(_vU);}}else{var _w6=new T(function(){var _w7=new T(function(){return B(_vs(_w1,_uN,new T(function(){return B(A2(_91,_w1,_uO));}),_w0));});return B(A3(_7k,_w1,new T(function(){return B(A2(_91,_w1,_vZ));}),_w7));});return new T2(0,_w6,_6i);}},_w8=function(_w9,_wa){var _wb=B(_vV(_w9,E(_wa))),_wc=_wb.a;if(E(_wb.b)<=0){return E(_wc);}else{var _wd=B(_rT(B(_rR(_w9))));return new F(function(){return A3(_6I,_wd,_wc,new T(function(){return B(A2(_91,_wd,_1M));}));});}},_we=function(_wf,_wg){var _wh=B(_vV(_wf,E(_wg))),_wi=_wh.a;if(E(_wh.b)>=0){return E(_wi);}else{var _wj=B(_rT(B(_rR(_wf))));return new F(function(){return A3(_7m,_wj,_wi,new T(function(){return B(A2(_91,_wj,_1M));}));});}},_wk=function(_wl,_wm){var _wn=B(_vV(_wl,E(_wm)));return new T2(0,_wn.a,_wn.b);},_wo=function(_wp,_wq){var _wr=B(_vV(_wp,_wq)),_ws=_wr.a,_wt=E(_wr.b),_wu=new T(function(){var _wv=B(_rT(B(_rR(_wp))));if(_wt>=0){return B(A3(_6I,_wv,_ws,new T(function(){return B(A2(_91,_wv,_1M));})));}else{return B(A3(_7m,_wv,_ws,new T(function(){return B(A2(_91,_wv,_1M));})));}}),_ww=function(_wx){var _wy=_wx-0.5;return (_wy>=0)?(E(_wy)==0)?(!B(_vi(_wp,_ws)))?E(_wu):E(_ws):E(_wu):E(_ws);},_wz=E(_wt);if(!_wz){return new F(function(){return _ww(0);});}else{if(_wz<=0){var _wA= -_wz-0.5;return (_wA>=0)?(E(_wA)==0)?(!B(_vi(_wp,_ws)))?E(_wu):E(_ws):E(_wu):E(_ws);}else{return new F(function(){return _ww(_wz);});}}},_wB=function(_wC,_wD){return new F(function(){return _wo(_wC,E(_wD));});},_wE=function(_wF,_wG){return E(B(_vV(_wF,E(_wG))).a);},_wH={_:0,a:_rQ,b:_ip,c:_wk,d:_wE,e:_wB,f:_w8,g:_we},_wI=new T1(0,1),_wJ=function(_wK,_wL){var _wM=E(_wK);return new T2(0,_wM,new T(function(){var _wN=B(_wJ(B(_3b(_wM,_wL)),_wL));return new T2(1,_wN.a,_wN.b);}));},_wO=function(_wP){var _wQ=B(_wJ(_wP,_wI));return new T2(1,_wQ.a,_wQ.b);},_wR=function(_wS,_wT){var _wU=B(_wJ(_wS,new T(function(){return B(_5w(_wT,_wS));})));return new T2(1,_wU.a,_wU.b);},_wV=new T1(0,0),_wW=function(_wX,_wY){var _wZ=E(_wX);if(!_wZ._){var _x0=_wZ.a,_x1=E(_wY);return (_x1._==0)?_x0>=_x1.a:I_compareInt(_x1.a,_x0)<=0;}else{var _x2=_wZ.a,_x3=E(_wY);return (_x3._==0)?I_compareInt(_x2,_x3.a)>=0:I_compare(_x2,_x3.a)>=0;}},_x4=function(_x5,_x6,_x7){if(!B(_wW(_x6,_wV))){var _x8=function(_x9){return (!B(_3N(_x9,_x7)))?new T2(1,_x9,new T(function(){return B(_x8(B(_3b(_x9,_x6))));})):__Z;};return new F(function(){return _x8(_x5);});}else{var _xa=function(_xb){return (!B(_3E(_xb,_x7)))?new T2(1,_xb,new T(function(){return B(_xa(B(_3b(_xb,_x6))));})):__Z;};return new F(function(){return _xa(_x5);});}},_xc=function(_xd,_xe,_xf){return new F(function(){return _x4(_xd,B(_5w(_xe,_xd)),_xf);});},_xg=function(_xh,_xi){return new F(function(){return _x4(_xh,_wI,_xi);});},_xj=function(_xk){return new F(function(){return _38(_xk);});},_xl=function(_xm){return new F(function(){return _5w(_xm,_wI);});},_xn=function(_xo){return new F(function(){return _3b(_xo,_wI);});},_xp=function(_xq){return new F(function(){return _qQ(E(_xq));});},_xr={_:0,a:_xn,b:_xl,c:_xp,d:_xj,e:_wO,f:_wR,g:_xg,h:_xc},_xs=function(_xt,_xu){while(1){var _xv=E(_xt);if(!_xv._){var _xw=E(_xv.a);if(_xw==(-2147483648)){_xt=new T1(1,I_fromInt(-2147483648));continue;}else{var _xx=E(_xu);if(!_xx._){return new T1(0,B(_sM(_xw,_xx.a)));}else{_xt=new T1(1,I_fromInt(_xw));_xu=_xx;continue;}}}else{var _xy=_xv.a,_xz=E(_xu);return (_xz._==0)?new T1(1,I_div(_xy,I_fromInt(_xz.a))):new T1(1,I_div(_xy,_xz.a));}}},_xA=function(_xB,_xC){if(!B(_30(_xC,_vf))){return new F(function(){return _xs(_xB,_xC);});}else{return E(_2V);}},_xD=function(_xE,_xF){while(1){var _xG=E(_xE);if(!_xG._){var _xH=E(_xG.a);if(_xH==(-2147483648)){_xE=new T1(1,I_fromInt(-2147483648));continue;}else{var _xI=E(_xF);if(!_xI._){var _xJ=_xI.a;return new T2(0,new T1(0,B(_sM(_xH,_xJ))),new T1(0,B(_ti(_xH,_xJ))));}else{_xE=new T1(1,I_fromInt(_xH));_xF=_xI;continue;}}}else{var _xK=E(_xF);if(!_xK._){_xE=_xG;_xF=new T1(1,I_fromInt(_xK.a));continue;}else{var _xL=I_divMod(_xG.a,_xK.a);return new T2(0,new T1(1,_xL.a),new T1(1,_xL.b));}}}},_xM=function(_xN,_xO){if(!B(_30(_xO,_vf))){var _xP=B(_xD(_xN,_xO));return new T2(0,_xP.a,_xP.b);}else{return E(_2V);}},_xQ=function(_xR,_xS){while(1){var _xT=E(_xR);if(!_xT._){var _xU=E(_xT.a);if(_xU==(-2147483648)){_xR=new T1(1,I_fromInt(-2147483648));continue;}else{var _xV=E(_xS);if(!_xV._){return new T1(0,B(_ti(_xU,_xV.a)));}else{_xR=new T1(1,I_fromInt(_xU));_xS=_xV;continue;}}}else{var _xW=_xT.a,_xX=E(_xS);return (_xX._==0)?new T1(1,I_mod(_xW,I_fromInt(_xX.a))):new T1(1,I_mod(_xW,_xX.a));}}},_xY=function(_xZ,_y0){if(!B(_30(_y0,_vf))){return new F(function(){return _xQ(_xZ,_y0);});}else{return E(_2V);}},_y1=function(_y2,_y3){while(1){var _y4=E(_y2);if(!_y4._){var _y5=E(_y4.a);if(_y5==(-2147483648)){_y2=new T1(1,I_fromInt(-2147483648));continue;}else{var _y6=E(_y3);if(!_y6._){return new T1(0,quot(_y5,_y6.a));}else{_y2=new T1(1,I_fromInt(_y5));_y3=_y6;continue;}}}else{var _y7=_y4.a,_y8=E(_y3);return (_y8._==0)?new T1(0,I_toInt(I_quot(_y7,I_fromInt(_y8.a)))):new T1(1,I_quot(_y7,_y8.a));}}},_y9=function(_ya,_yb){if(!B(_30(_yb,_vf))){return new F(function(){return _y1(_ya,_yb);});}else{return E(_2V);}},_yc=function(_yd,_ye){if(!B(_30(_ye,_vf))){var _yf=B(_3k(_yd,_ye));return new T2(0,_yf.a,_yf.b);}else{return E(_2V);}},_yg=function(_yh,_yi){while(1){var _yj=E(_yh);if(!_yj._){var _yk=E(_yj.a);if(_yk==(-2147483648)){_yh=new T1(1,I_fromInt(-2147483648));continue;}else{var _yl=E(_yi);if(!_yl._){return new T1(0,_yk%_yl.a);}else{_yh=new T1(1,I_fromInt(_yk));_yi=_yl;continue;}}}else{var _ym=_yj.a,_yn=E(_yi);return (_yn._==0)?new T1(1,I_rem(_ym,I_fromInt(_yn.a))):new T1(1,I_rem(_ym,_yn.a));}}},_yo=function(_yp,_yq){if(!B(_30(_yq,_vf))){return new F(function(){return _yg(_yp,_yq);});}else{return E(_2V);}},_yr=function(_ys){return E(_ys);},_yt=function(_yu){return E(_yu);},_yv=function(_yw){var _yx=E(_yw);if(!_yx._){var _yy=E(_yx.a);return (_yy==(-2147483648))?E(_6a):(_yy<0)?new T1(0, -_yy):E(_yx);}else{var _yz=_yx.a;return (I_compareInt(_yz,0)>=0)?E(_yx):new T1(1,I_negate(_yz));}},_yA=new T1(0,0),_yB=new T1(0,-1),_yC=function(_yD){var _yE=E(_yD);if(!_yE._){var _yF=_yE.a;return (_yF>=0)?(E(_yF)==0)?E(_yA):E(_3M):E(_yB);}else{var _yG=I_compareInt(_yE.a,0);return (_yG<=0)?(E(_yG)==0)?E(_yA):E(_yB):E(_3M);}},_yH={_:0,a:_3b,b:_5w,c:_uP,d:_6b,e:_yv,f:_yC,g:_yt},_yI=function(_yJ,_yK){var _yL=E(_yJ);if(!_yL._){var _yM=_yL.a,_yN=E(_yK);return (_yN._==0)?_yM!=_yN.a:(I_compareInt(_yN.a,_yM)==0)?false:true;}else{var _yO=_yL.a,_yP=E(_yK);return (_yP._==0)?(I_compareInt(_yO,_yP.a)==0)?false:true:(I_compare(_yO,_yP.a)==0)?false:true;}},_yQ=new T2(0,_30,_yI),_yR=function(_yS,_yT){return (!B(_5h(_yS,_yT)))?E(_yS):E(_yT);},_yU=function(_yV,_yW){return (!B(_5h(_yV,_yW)))?E(_yW):E(_yV);},_yX={_:0,a:_yQ,b:_1N,c:_3N,d:_5h,e:_3E,f:_wW,g:_yR,h:_yU},_yY=function(_yZ){return new T2(0,E(_yZ),E(_mx));},_z0=new T3(0,_yH,_yX,_yY),_z1={_:0,a:_z0,b:_xr,c:_y9,d:_yo,e:_xA,f:_xY,g:_yc,h:_xM,i:_yr},_z2=function(_z3){return E(E(_z3).b);},_z4=function(_z5){return E(E(_z5).g);},_z6=new T1(0,1),_z7=function(_z8,_z9,_za){var _zb=B(_z2(_z8)),_zc=B(_7i(_zb)),_zd=new T(function(){var _ze=new T(function(){var _zf=new T(function(){var _zg=new T(function(){return B(A3(_z4,_z8,_z1,new T(function(){return B(A3(_9b,_zb,_z9,_za));})));});return B(A2(_91,_zc,_zg));}),_zh=new T(function(){return B(A2(_6K,_zc,new T(function(){return B(A2(_91,_zc,_z6));})));});return B(A3(_7k,_zc,_zh,_zf));});return B(A3(_7k,_zc,_ze,_za));});return new F(function(){return A3(_6I,_zc,_z9,_zd);});},_zi=1.5707963267948966,_zj=function(_zk){return 0.2/Math.cos(B(_z7(_wH,_zk,_zi))-0.7853981633974483);},_zl=2,_zm=new T(function(){var _zn=B(_ph(_zj,1.2,_qM,_qA,_qA,_qA,_qA,_qL,_qH,_zl,_qA,_qA,_qG));return {_:0,a:E(_zn.a),b:E(_zn.b),c:E(_zn.c),d:E(_zn.d),e:E(_zn.e),f:E(_zn.f),g:E(_zn.g),h:_zn.h,i:_zn.i};}),_zo=new T2(1,_zm,_o),_zp=new T2(1,_qI,_zo),_zq=new T(function(){return B(unCStr("Negative range size"));}),_zr=new T(function(){return B(err(_zq));}),_zs=function(_){var _zt=B(_hf(_zp,0))-1|0,_zu=function(_zv){if(_zv>=0){var _zw=newArr(_zv,_hl),_zx=_zw,_zy=E(_zv);if(!_zy){return new T4(0,E(_qK),E(_zt),0,_zx);}else{var _zz=function(_zA,_zB,_){while(1){var _zC=E(_zA);if(!_zC._){return E(_);}else{var _=_zx[_zB]=_zC.a;if(_zB!=(_zy-1|0)){var _zD=_zB+1|0;_zA=_zC.b;_zB=_zD;continue;}else{return E(_);}}}},_=B((function(_zE,_zF,_zG,_){var _=_zx[_zG]=_zE;if(_zG!=(_zy-1|0)){return new F(function(){return _zz(_zF,_zG+1|0,_);});}else{return E(_);}})(_qI,_zo,0,_));return new T4(0,E(_qK),E(_zt),_zy,_zx);}}else{return E(_zr);}};if(0>_zt){return new F(function(){return _zu(0);});}else{return new F(function(){return _zu(_zt+1|0);});}},_zH=function(_zI){var _zJ=B(A1(_zI,_));return E(_zJ);},_zK=new T(function(){return B(_zH(_zs));}),_zL=function(_zM,_zN,_){var _zO=B(A1(_zM,_)),_zP=B(A1(_zN,_));return _zO;},_zQ=function(_zR,_zS,_){var _zT=B(A1(_zR,_)),_zU=B(A1(_zS,_));return new T(function(){return B(A1(_zT,_zU));});},_zV=function(_zW,_zX,_){var _zY=B(A1(_zX,_));return _zW;},_zZ=function(_A0,_A1,_){var _A2=B(A1(_A1,_));return new T(function(){return B(A1(_A0,_A2));});},_A3=new T2(0,_zZ,_zV),_A4=function(_A5,_){return _A5;},_A6=function(_A7,_A8,_){var _A9=B(A1(_A7,_));return new F(function(){return A1(_A8,_);});},_Aa=new T5(0,_A3,_A4,_zQ,_A6,_zL),_Ab=function(_Ac){var _Ad=E(_Ac);return (E(_Ad.b)-E(_Ad.a)|0)+1|0;},_Ae=function(_Af,_Ag){var _Ah=E(_Af),_Ai=E(_Ag);return (E(_Ah.a)>_Ai)?false:_Ai<=E(_Ah.b);},_Aj=function(_Ak,_Al){var _Am=jsShowI(_Ak);return new F(function(){return _f(fromJSStr(_Am),_Al);});},_An=function(_Ao,_Ap,_Aq){if(_Ap>=0){return new F(function(){return _Aj(_Ap,_Aq);});}else{if(_Ao<=6){return new F(function(){return _Aj(_Ap,_Aq);});}else{return new T2(1,_71,new T(function(){var _Ar=jsShowI(_Ap);return B(_f(fromJSStr(_Ar),new T2(1,_70,_Aq)));}));}}},_As=function(_At){return new F(function(){return _An(0,E(_At),_o);});},_Au=function(_Av,_Aw,_Ax){return new F(function(){return _An(E(_Av),E(_Aw),_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _An(0,E(_Az),_AA);});},_AB=function(_AC,_AD){return new F(function(){return _2B(_Ay,_AC,_AD);});},_AE=new T3(0,_Au,_As,_AB),_AF=0,_AG=function(_AH,_AI,_AJ){return new F(function(){return A1(_AH,new T2(1,_2y,new T(function(){return B(A1(_AI,_AJ));})));});},_AK=new T(function(){return B(unCStr("foldr1"));}),_AL=new T(function(){return B(_lX(_AK));}),_AM=function(_AN,_AO){var _AP=E(_AO);if(!_AP._){return E(_AL);}else{var _AQ=_AP.a,_AR=E(_AP.b);if(!_AR._){return E(_AQ);}else{return new F(function(){return A2(_AN,_AQ,new T(function(){return B(_AM(_AN,_AR));}));});}}},_AS=new T(function(){return B(unCStr(" out of range "));}),_AT=new T(function(){return B(unCStr("}.index: Index "));}),_AU=new T(function(){return B(unCStr("Ix{"));}),_AV=new T2(1,_70,_o),_AW=new T2(1,_70,_AV),_AX=0,_AY=function(_AZ){return E(E(_AZ).a);},_B0=function(_B1,_B2,_B3,_B4,_B5){var _B6=new T(function(){var _B7=new T(function(){var _B8=new T(function(){var _B9=new T(function(){var _Ba=new T(function(){return B(A3(_AM,_AG,new T2(1,new T(function(){return B(A3(_AY,_B3,_AX,_B4));}),new T2(1,new T(function(){return B(A3(_AY,_B3,_AX,_B5));}),_o)),_AW));});return B(_f(_AS,new T2(1,_71,new T2(1,_71,_Ba))));});return B(A(_AY,[_B3,_AF,_B2,new T2(1,_70,_B9)]));});return B(_f(_AT,new T2(1,_71,_B8)));},1);return B(_f(_B1,_B7));},1);return new F(function(){return err(B(_f(_AU,_B6)));});},_Bb=function(_Bc,_Bd,_Be,_Bf,_Bg){return new F(function(){return _B0(_Bc,_Bd,_Bg,_Be,_Bf);});},_Bh=function(_Bi,_Bj,_Bk,_Bl){var _Bm=E(_Bk);return new F(function(){return _Bb(_Bi,_Bj,_Bm.a,_Bm.b,_Bl);});},_Bn=function(_Bo,_Bp,_Bq,_Br){return new F(function(){return _Bh(_Br,_Bq,_Bp,_Bo);});},_Bs=new T(function(){return B(unCStr("Int"));}),_Bt=function(_Bu,_Bv){return new F(function(){return _Bn(_AE,_Bv,_Bu,_Bs);});},_Bw=function(_Bx,_By){var _Bz=E(_Bx),_BA=E(_Bz.a),_BB=E(_By);if(_BA>_BB){return new F(function(){return _Bt(_BB,_Bz);});}else{if(_BB>E(_Bz.b)){return new F(function(){return _Bt(_BB,_Bz);});}else{return _BB-_BA|0;}}},_BC=function(_BD){var _BE=E(_BD);return new F(function(){return _sw(_BE.a,_BE.b);});},_BF=function(_BG){var _BH=E(_BG),_BI=E(_BH.a),_BJ=E(_BH.b);return (_BI>_BJ)?E(_AF):(_BJ-_BI|0)+1|0;},_BK=function(_BL,_BM){return new F(function(){return _tV(_BM,E(_BL).a);});},_BN={_:0,a:_uL,b:_BC,c:_Bw,d:_BK,e:_Ae,f:_BF,g:_Ab},_BO=function(_BP,_BQ){return new T2(1,_BP,_BQ);},_BR=function(_BS,_BT){var _BU=E(_BT);return new T2(0,_BU.a,_BU.b);},_BV=function(_BW){return E(E(_BW).f);},_BX=function(_BY,_BZ,_C0){var _C1=E(_BZ),_C2=_C1.a,_C3=_C1.b,_C4=function(_){var _C5=B(A2(_BV,_BY,_C1));if(_C5>=0){var _C6=newArr(_C5,_hl),_C7=_C6,_C8=E(_C5);if(!_C8){return new T(function(){return new T4(0,E(_C2),E(_C3),0,_C7);});}else{var _C9=function(_Ca,_Cb,_){while(1){var _Cc=E(_Ca);if(!_Cc._){return E(_);}else{var _=_C7[_Cb]=_Cc.a;if(_Cb!=(_C8-1|0)){var _Cd=_Cb+1|0;_Ca=_Cc.b;_Cb=_Cd;continue;}else{return E(_);}}}},_=B(_C9(_C0,0,_));return new T(function(){return new T4(0,E(_C2),E(_C3),_C8,_C7);});}}else{return E(_zr);}};return new F(function(){return _zH(_C4);});},_Ce=function(_Cf,_Cg,_Ch,_Ci){var _Cj=new T(function(){var _Ck=E(_Ci),_Cl=_Ck.c-1|0,_Cm=new T(function(){return B(A2(_cX,_Cg,_o));});if(0<=_Cl){var _Cn=new T(function(){return B(_97(_Cg));}),_Co=function(_Cp){var _Cq=new T(function(){var _Cr=new T(function(){return B(A1(_Ch,new T(function(){return E(_Ck.d[_Cp]);})));});return B(A3(_9f,_Cn,_BO,_Cr));});return new F(function(){return A3(_9d,_Cg,_Cq,new T(function(){if(_Cp!=_Cl){return B(_Co(_Cp+1|0));}else{return E(_Cm);}}));});};return B(_Co(0));}else{return E(_Cm);}}),_Cs=new T(function(){return B(_BR(_Cf,_Ci));});return new F(function(){return A3(_9f,B(_97(_Cg)),function(_Ct){return new F(function(){return _BX(_Cf,_Cs,_Ct);});},_Cj);});},_Cu=function(_Cv){return E(E(_Cv).a);},_Cw=function(_Cx,_Cy,_Cz,_CA,_CB){var _CC=B(A2(_Cu,_Cx,E(_CB)));return new F(function(){return A2(_Cy,_Cz,new T2(1,_CC,E(_CA)));});},_CD="outline",_CE="polygon",_CF=function(_CG){return new F(function(){return _jD(new T2(1,new T2(0,_CE,new T(function(){return E(_CG).h;})),new T2(1,new T2(0,_CD,new T(function(){return E(_CG).i;})),_o)));});},_CH=function(_CI){return new F(function(){return _CF(_CI);});},_CJ=function(_CK){return new F(function(){return __lst2arr(B(_k3(_CH,_CK)));});},_CL=new T2(0,_CH,_CJ),_CM=function(_CN,_){var _CO=E(_CN);if(!_CO._){return _o;}else{var _CP=B(_CM(_CO.b,_));return new T2(1,_jC,_CP);}},_CQ=function(_CR,_){var _CS=__arr2lst(0,_CR);return new F(function(){return _CM(_CS,_);});},_CT=function(_CU,_){return new F(function(){return _CQ(E(_CU),_);});},_CV=function(_){return _jC;},_CW=function(_CX,_){return new F(function(){return _CV(_);});},_CY=new T2(0,_CW,_CT),_CZ=function(_D0){return E(E(_D0).a);},_D1=function(_D2,_D3,_D4,_){var _D5=__apply(_D3,E(_D4));return new F(function(){return A3(_CZ,_D2,_D5,_);});},_D6=function(_D7,_D8,_D9,_){return new F(function(){return _D1(_D7,E(_D8),_D9,_);});},_Da=function(_Db,_Dc,_Dd,_){return new F(function(){return _D6(_Db,_Dc,_Dd,_);});},_De=function(_Df,_Dg,_){return new F(function(){return _Da(_CY,_Df,_Dg,_);});},_Dh=new T(function(){return eval("drawObject");}),_Di=function(_Dj){return new F(function(){return _Cw(_CL,_De,_Dh,_o,_Dj);});},_Dk=new T(function(){return eval("__strict(draw)");}),_Dl=function(_Dm){return E(_Dm);},_Dn=function(_Do){return E(_Do);},_Dp=function(_Dq,_Dr){return E(_Dr);},_Ds=function(_Dt,_Du){return E(_Dt);},_Dv=function(_Dw){return E(_Dw);},_Dx=new T2(0,_Dv,_Ds),_Dy=function(_Dz,_DA){return E(_Dz);},_DB=new T5(0,_Dx,_Dn,_Dl,_Dp,_Dy),_DC="d2z",_DD="d2y",_DE="w2z",_DF="w2y",_DG="w2x",_DH="w1z",_DI="w1y",_DJ="w1x",_DK="d2x",_DL="d1z",_DM="d1y",_DN="d1x",_DO="c2y",_DP="c2x",_DQ="c1y",_DR="c1x",_DS=function(_DT,_){var _DU=__get(_DT,E(_DJ)),_DV=__get(_DT,E(_DI)),_DW=__get(_DT,E(_DH)),_DX=__get(_DT,E(_DG)),_DY=__get(_DT,E(_DF)),_DZ=__get(_DT,E(_DE)),_E0=__get(_DT,E(_DR)),_E1=__get(_DT,E(_DQ)),_E2=__get(_DT,E(_DP)),_E3=__get(_DT,E(_DO)),_E4=__get(_DT,E(_DN)),_E5=__get(_DT,E(_DM)),_E6=__get(_DT,E(_DL)),_E7=__get(_DT,E(_DK)),_E8=__get(_DT,E(_DD)),_E9=__get(_DT,E(_DC));return new T6(0,E(new T3(0,E(_DU),E(_DV),E(_DW))),E(new T3(0,E(_DX),E(_DY),E(_DZ))),E(new T2(0,E(_E0),E(_E1))),E(new T2(0,E(_E2),E(_E3))),E(new T3(0,E(_E4),E(_E5),E(_E6))),E(new T3(0,E(_E7),E(_E8),E(_E9))));},_Ea=function(_Eb,_){var _Ec=E(_Eb);if(!_Ec._){return _o;}else{var _Ed=B(_DS(E(_Ec.a),_)),_Ee=B(_Ea(_Ec.b,_));return new T2(1,_Ed,_Ee);}},_Ef=function(_Eg,_Eh,_){while(1){var _Ei=B((function(_Ej,_Ek,_){var _El=E(_Ej);if(!_El._){return new T2(0,_jC,_Ek);}else{var _Em=B(A2(_El.a,_Ek,_));_Eg=_El.b;_Eh=new T(function(){return E(E(_Em).b);});return __continue;}})(_Eg,_Eh,_));if(_Ei!=__continue){return _Ei;}}},_En=function(_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew){var _Ex=B(_7k(_Eo));return new T2(0,new T3(0,E(B(A1(B(A1(_Ex,_Ep)),_Et))),E(B(A1(B(A1(_Ex,_Eq)),_Eu))),E(B(A1(B(A1(_Ex,_Er)),_Ev)))),B(A1(B(A1(_Ex,_Es)),_Ew)));},_Ey=function(_Ez,_EA,_EB,_EC,_ED,_EE,_EF,_EG,_EH){var _EI=B(_6I(_Ez));return new T2(0,new T3(0,E(B(A1(B(A1(_EI,_EA)),_EE))),E(B(A1(B(A1(_EI,_EB)),_EF))),E(B(A1(B(A1(_EI,_EC)),_EG)))),B(A1(B(A1(_EI,_ED)),_EH)));},_EJ=1.0e-2,_EK=function(_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1){var _F2=B(_En(_il,_ES,_ET,_EU,_EV,_EJ,_EJ,_EJ,_EJ)),_F3=E(_F2.a),_F4=B(_Ey(_il,_EO,_EP,_EQ,_ER,_F3.a,_F3.b,_F3.c,_F2.b)),_F5=E(_F4.a);return new F(function(){return _oy(_EL,_EM,_EN,_F5.a,_F5.b,_F5.c,_F4.b,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1);});},_F6=function(_F7){var _F8=E(_F7),_F9=E(_F8.d),_Fa=E(_F9.a),_Fb=E(_F8.e),_Fc=E(_Fb.a),_Fd=E(_F8.f),_Fe=B(_EK(_F8.a,_F8.b,_F8.c,_Fa.a,_Fa.b,_Fa.c,_F9.b,_Fc.a,_Fc.b,_Fc.c,_Fb.b,_Fd.a,_Fd.b,_Fd.c,_F8.g,_F8.h,_F8.i));return {_:0,a:E(_Fe.a),b:E(_Fe.b),c:E(_Fe.c),d:E(_Fe.d),e:E(_Fe.e),f:E(_Fe.f),g:E(_Fe.g),h:_Fe.h,i:_Fe.i};},_Ff=function(_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo){var _Fp=B(_7i(B(_7g(_Fg))));return new F(function(){return A3(_6I,_Fp,new T(function(){return B(_kg(_Fg,_Fh,_Fi,_Fj,_Fl,_Fm,_Fn));}),new T(function(){return B(A3(_7k,_Fp,_Fk,_Fo));}));});},_Fq=new T(function(){return B(unCStr("base"));}),_Fr=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fs=new T(function(){return B(unCStr("IOException"));}),_Ft=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fq,_Fr,_Fs),_Fu=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Ft,_o,_o),_Fv=function(_Fw){return E(_Fu);},_Fx=function(_Fy){var _Fz=E(_Fy);return new F(function(){return _28(B(_26(_Fz.a)),_Fv,_Fz.b);});},_FA=new T(function(){return B(unCStr(": "));}),_FB=new T(function(){return B(unCStr(")"));}),_FC=new T(function(){return B(unCStr(" ("));}),_FD=new T(function(){return B(unCStr("interrupted"));}),_FE=new T(function(){return B(unCStr("system error"));}),_FF=new T(function(){return B(unCStr("unsatisified constraints"));}),_FG=new T(function(){return B(unCStr("user error"));}),_FH=new T(function(){return B(unCStr("permission denied"));}),_FI=new T(function(){return B(unCStr("illegal operation"));}),_FJ=new T(function(){return B(unCStr("end of file"));}),_FK=new T(function(){return B(unCStr("resource exhausted"));}),_FL=new T(function(){return B(unCStr("resource busy"));}),_FM=new T(function(){return B(unCStr("does not exist"));}),_FN=new T(function(){return B(unCStr("already exists"));}),_FO=new T(function(){return B(unCStr("resource vanished"));}),_FP=new T(function(){return B(unCStr("timeout"));}),_FQ=new T(function(){return B(unCStr("unsupported operation"));}),_FR=new T(function(){return B(unCStr("hardware fault"));}),_FS=new T(function(){return B(unCStr("inappropriate type"));}),_FT=new T(function(){return B(unCStr("invalid argument"));}),_FU=new T(function(){return B(unCStr("failed"));}),_FV=new T(function(){return B(unCStr("protocol error"));}),_FW=function(_FX,_FY){switch(E(_FX)){case 0:return new F(function(){return _f(_FN,_FY);});break;case 1:return new F(function(){return _f(_FM,_FY);});break;case 2:return new F(function(){return _f(_FL,_FY);});break;case 3:return new F(function(){return _f(_FK,_FY);});break;case 4:return new F(function(){return _f(_FJ,_FY);});break;case 5:return new F(function(){return _f(_FI,_FY);});break;case 6:return new F(function(){return _f(_FH,_FY);});break;case 7:return new F(function(){return _f(_FG,_FY);});break;case 8:return new F(function(){return _f(_FF,_FY);});break;case 9:return new F(function(){return _f(_FE,_FY);});break;case 10:return new F(function(){return _f(_FV,_FY);});break;case 11:return new F(function(){return _f(_FU,_FY);});break;case 12:return new F(function(){return _f(_FT,_FY);});break;case 13:return new F(function(){return _f(_FS,_FY);});break;case 14:return new F(function(){return _f(_FR,_FY);});break;case 15:return new F(function(){return _f(_FQ,_FY);});break;case 16:return new F(function(){return _f(_FP,_FY);});break;case 17:return new F(function(){return _f(_FO,_FY);});break;default:return new F(function(){return _f(_FD,_FY);});}},_FZ=new T(function(){return B(unCStr("}"));}),_G0=new T(function(){return B(unCStr("{handle: "));}),_G1=function(_G2,_G3,_G4,_G5,_G6,_G7){var _G8=new T(function(){var _G9=new T(function(){var _Ga=new T(function(){var _Gb=E(_G5);if(!_Gb._){return E(_G7);}else{var _Gc=new T(function(){return B(_f(_Gb,new T(function(){return B(_f(_FB,_G7));},1)));},1);return B(_f(_FC,_Gc));}},1);return B(_FW(_G3,_Ga));}),_Gd=E(_G4);if(!_Gd._){return E(_G9);}else{return B(_f(_Gd,new T(function(){return B(_f(_FA,_G9));},1)));}}),_Ge=E(_G6);if(!_Ge._){var _Gf=E(_G2);if(!_Gf._){return E(_G8);}else{var _Gg=E(_Gf.a);if(!_Gg._){var _Gh=new T(function(){var _Gi=new T(function(){return B(_f(_FZ,new T(function(){return B(_f(_FA,_G8));},1)));},1);return B(_f(_Gg.a,_Gi));},1);return new F(function(){return _f(_G0,_Gh);});}else{var _Gj=new T(function(){var _Gk=new T(function(){return B(_f(_FZ,new T(function(){return B(_f(_FA,_G8));},1)));},1);return B(_f(_Gg.a,_Gk));},1);return new F(function(){return _f(_G0,_Gj);});}}}else{return new F(function(){return _f(_Ge.a,new T(function(){return B(_f(_FA,_G8));},1));});}},_Gl=function(_Gm){var _Gn=E(_Gm);return new F(function(){return _G1(_Gn.a,_Gn.b,_Gn.c,_Gn.d,_Gn.f,_o);});},_Go=function(_Gp,_Gq,_Gr){var _Gs=E(_Gq);return new F(function(){return _G1(_Gs.a,_Gs.b,_Gs.c,_Gs.d,_Gs.f,_Gr);});},_Gt=function(_Gu,_Gv){var _Gw=E(_Gu);return new F(function(){return _G1(_Gw.a,_Gw.b,_Gw.c,_Gw.d,_Gw.f,_Gv);});},_Gx=function(_Gy,_Gz){return new F(function(){return _2B(_Gt,_Gy,_Gz);});},_GA=new T3(0,_Go,_Gl,_Gx),_GB=new T(function(){return new T5(0,_Fv,_GA,_GC,_Fx,_Gl);}),_GC=function(_GD){return new T2(0,_GB,_GD);},_GE=__Z,_GF=7,_GG=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:70:3-9"));}),_GH=new T6(0,_GE,_GF,_o,_GG,_GE,_GE),_GI=new T(function(){return B(_GC(_GH));}),_GJ=function(_){return new F(function(){return die(_GI);});},_GK=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:69:3-9"));}),_GL=new T6(0,_GE,_GF,_o,_GK,_GE,_GE),_GM=new T(function(){return B(_GC(_GL));}),_GN=function(_){return new F(function(){return die(_GM);});},_GO=function(_GP,_){return new T2(0,_o,_GP);},_GQ=1,_GR=new T(function(){return B(unCStr(")"));}),_GS=function(_GT,_GU){var _GV=new T(function(){var _GW=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_An(0,_GT,_o)),_GR));})));},1);return B(_f(B(_An(0,_GU,_o)),_GW));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GV)));});},_GX=function(_GY,_GZ){var _H0=new T(function(){var _H1=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_An(0,_GZ,_o)),_GR));})));},1);return B(_f(B(_An(0,_GY,_o)),_H1));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_H0)));});},_H2=0.6,_H3=function(_H4){var _H5=E(_H4);if(!_H5._){return E(_GO);}else{var _H6=new T(function(){return B(_H3(_H5.b));}),_H7=function(_H8){var _H9=E(_H8);if(!_H9._){return E(_H6);}else{var _Ha=_H9.a,_Hb=new T(function(){return B(_H7(_H9.b));}),_Hc=new T(function(){return 0.1*E(E(_Ha).e)/1.0e-2;}),_Hd=new T(function(){var _He=E(_Ha);if(_He.a!=_He.b){return E(_GQ);}else{return E(_H2);}}),_Hf=function(_Hg,_){var _Hh=E(_Hg),_Hi=_Hh.c,_Hj=_Hh.d,_Hk=E(_Hh.a),_Hl=E(_Hh.b),_Hm=E(_Ha),_Hn=_Hm.a,_Ho=_Hm.b,_Hp=E(_Hm.c),_Hq=_Hp.b,_Hr=E(_Hp.a),_Hs=_Hr.a,_Ht=_Hr.b,_Hu=_Hr.c,_Hv=E(_Hm.d),_Hw=_Hv.b,_Hx=E(_Hv.a),_Hy=_Hx.a,_Hz=_Hx.b,_HA=_Hx.c;if(_Hk>_Hn){return new F(function(){return _GN(_);});}else{if(_Hn>_Hl){return new F(function(){return _GN(_);});}else{if(_Hk>_Ho){return new F(function(){return _GJ(_);});}else{if(_Ho>_Hl){return new F(function(){return _GJ(_);});}else{var _HB=_Hn-_Hk|0;if(0>_HB){return new F(function(){return _GS(_Hi,_HB);});}else{if(_HB>=_Hi){return new F(function(){return _GS(_Hi,_HB);});}else{var _HC=E(_Hj[_HB]),_HD=E(_HC.c),_HE=_HD.b,_HF=E(_HD.a),_HG=_HF.a,_HH=_HF.b,_HI=_HF.c,_HJ=E(_HC.e),_HK=_HJ.b,_HL=E(_HJ.a),_HM=_HL.a,_HN=_HL.b,_HO=_HL.c,_HP=B(_En(_il,_Hs,_Ht,_Hu,_Hq,_HG,_HH,_HI,_HE)),_HQ=E(_HP.a),_HR=B(_En(_il,_HQ.a,_HQ.b,_HQ.c,_HP.b,_Hs,_Ht,_Hu,_Hq)),_HS=E(_HR.a),_HT=_Ho-_Hk|0;if(0>_HT){return new F(function(){return _GX(_HT,_Hi);});}else{if(_HT>=_Hi){return new F(function(){return _GX(_HT,_Hi);});}else{var _HU=E(_Hj[_HT]),_HV=E(_HU.c),_HW=_HV.b,_HX=E(_HV.a),_HY=_HX.a,_HZ=_HX.b,_I0=_HX.c,_I1=E(_HU.e),_I2=E(_I1.a),_I3=B(_En(_il,_Hy,_Hz,_HA,_Hw,_HY,_HZ,_I0,_HW)),_I4=E(_I3.a),_I5=B(_En(_il,_I4.a,_I4.b,_I4.c,_I3.b,_Hy,_Hz,_HA,_Hw)),_I6=E(_I5.a),_I7=E(_HS.a)+E(_HS.b)+E(_HS.c)+E(_HR.b)+E(_I6.a)+E(_I6.b)+E(_I6.c)+E(_I5.b);if(!_I7){var _I8=B(A2(_Hb,_Hh,_));return new T2(0,new T2(1,_jC,new T(function(){return E(E(_I8).a);})),new T(function(){return E(E(_I8).b);}));}else{var _I9= -((B(_Ff(_iR,_HM,_HN,_HO,_HK,_Hs,_Ht,_Hu,_Hq))-B(_Ff(_iR,_I2.a,_I2.b,_I2.c,_I1.b,_Hy,_Hz,_HA,_Hw))-E(_Hc))/_I7);if(_I9<0){var _Ia=B(A2(_Hb,_Hh,_));return new T2(0,new T2(1,_jC,new T(function(){return E(E(_Ia).a);})),new T(function(){return E(E(_Ia).b);}));}else{var _Ib=new T(function(){var _Ic=function(_){var _Id=newArr(_Hi,_hl),_Ie=_Id,_If=function(_Ig,_){while(1){if(_Ig!=_Hi){var _=_Ie[_Ig]=_Hj[_Ig],_Ih=_Ig+1|0;_Ig=_Ih;continue;}else{return E(_);}}},_=B(_If(0,_)),_=_Ie[_HB]=new T(function(){var _Ii=B(_En(_il,_HG,_HH,_HI,_HE,_Hs,_Ht,_Hu,_Hq)),_Ij=E(_Ii.a),_Ik=_I9*E(_Hd),_Il=B(_En(_il,_Ij.a,_Ij.b,_Ij.c,_Ii.b,_Ik,_Ik,_Ik,_Ik)),_Im=E(_Il.a),_In=B(_Ey(_il,_HM,_HN,_HO,_HK,_Im.a,_Im.b,_Im.c,_Il.b));return {_:0,a:E(_HC.a),b:E(_HC.b),c:E(_HD),d:E(_HC.d),e:E(new T2(0,E(_In.a),E(_In.b))),f:E(_HC.f),g:E(_HC.g),h:_HC.h,i:_HC.i};});return new T4(0,E(_Hk),E(_Hl),_Hi,_Ie);},_Io=B(_zH(_Ic)),_Ip=_Io.c,_Iq=_Io.d,_Ir=E(_Io.a),_Is=E(_Io.b);if(_Ir>_Ho){return E(_Io);}else{if(_Ho>_Is){return E(_Io);}else{var _It=function(_){var _Iu=newArr(_Ip,_hl),_Iv=_Iu,_Iw=function(_Ix,_){while(1){if(_Ix!=_Ip){var _=_Iv[_Ix]=_Iq[_Ix],_Iy=_Ix+1|0;_Ix=_Iy;continue;}else{return E(_);}}},_=B(_Iw(0,_)),_Iz=_Ho-_Ir|0;if(0>_Iz){return new F(function(){return _GX(_Iz,_Ip);});}else{if(_Iz>=_Ip){return new F(function(){return _GX(_Iz,_Ip);});}else{var _=_Iv[_Iz]=new T(function(){var _IA=B(_En(_il,_HY,_HZ,_I0,_HW,_Hy,_Hz,_HA,_Hw)),_IB=E(_IA.a),_IC=_I9*E(_Hd),_ID=B(_En(_il,_IB.a,_IB.b,_IB.c,_IA.b,_IC,_IC,_IC,_IC)),_IE=E(_ID.a),_IF=E(_Iq[_Iz]),_IG=E(_IF.e),_IH=E(_IG.a),_II=B(_Ey(_il,_IH.a,_IH.b,_IH.c,_IG.b, -E(_IE.a), -E(_IE.b), -E(_IE.c), -E(_ID.b)));return {_:0,a:E(_IF.a),b:E(_IF.b),c:E(_IF.c),d:E(_IF.d),e:E(new T2(0,E(_II.a),E(_II.b))),f:E(_IF.f),g:E(_IF.g),h:_IF.h,i:_IF.i};});return new T4(0,E(_Ir),E(_Is),_Ip,_Iv);}}};return B(_zH(_It));}}}),_IJ=B(A2(_Hb,_Ib,_));return new T2(0,new T2(1,_jC,new T(function(){return E(E(_IJ).a);})),new T(function(){return E(E(_IJ).b);}));}}}}}}}}}}};return E(_Hf);}};return new F(function(){return _H7(_H5.a);});}},_IK=function(_,_IL){var _IM=new T(function(){return B(_H3(E(_IL).a));}),_IN=function(_IO){var _IP=E(_IO);return (_IP==1)?E(new T2(1,_IM,_o)):new T2(1,_IM,new T(function(){return B(_IN(_IP-1|0));}));},_IQ=B(_Ef(B(_IN(5)),new T(function(){return E(E(_IL).b);}),_)),_IR=new T(function(){return B(_Ce(_BN,_DB,_F6,new T(function(){return E(E(_IQ).b);})));});return new T2(0,_jC,_IR);},_IS=function(_IT,_IU,_IV,_IW,_IX){var _IY=B(_7i(B(_7g(_IT))));return new F(function(){return A3(_6I,_IY,new T(function(){return B(A3(_7k,_IY,_IU,_IW));}),new T(function(){return B(A3(_7k,_IY,_IV,_IX));}));});},_IZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));}),_J0=new T6(0,_GE,_GF,_o,_IZ,_GE,_GE),_J1=new T(function(){return B(_GC(_J0));}),_J2=function(_){return new F(function(){return die(_J1);});},_J3=function(_J4){var _J5=E(_J4),_J6=E(_J5.b),_J7=E(_J5.e),_J8=E(_J7.a),_J9=E(_J5.g),_Ja=B(_lg(_iR,_J6.a,_J6.b,_J6.c,_J9.a,_J9.b,_J9.c));return {_:0,a:E(_J5.a),b:E(_J6),c:E(_J5.c),d:E(_J5.d),e:E(new T2(0,E(new T3(0,E(_J8.a)+E(_Ja.a)*1.0e-2,E(_J8.b)+E(_Ja.b)*1.0e-2,E(_J8.c)+E(_Ja.c)*1.0e-2)),E(_J7.b))),f:E(_J5.f),g:E(_J9),h:_J5.h,i:_J5.i};},_Jb=new T(function(){return eval("collide");}),_Jc=function(_Jd){var _Je=E(_Jd);if(!_Je._){return __Z;}else{return new F(function(){return _f(_Je.a,new T(function(){return B(_Jc(_Je.b));},1));});}},_Jf=new T2(0,_iR,_jq),_Jg=new T(function(){return B(_gS(_Jf));}),_Jh=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_Ji=new T6(0,_GE,_GF,_o,_Jh,_GE,_GE),_Jj=new T(function(){return B(_GC(_Ji));}),_Jk=function(_Jl,_){var _Jm=B(_Ce(_BN,_DB,_J3,_Jl)),_Jn=E(_Jm.a),_Jo=E(_Jm.b);if(_Jn<=_Jo){var _Jp=function(_Jq,_Jr,_){if(_Jq<=_Jo){var _Js=E(_Jr),_Jt=function(_Ju,_Jv,_Jw,_Jx,_Jy,_){if(_Jv>_Jq){return new F(function(){return die(_Jj);});}else{if(_Jq>_Jw){return new F(function(){return die(_Jj);});}else{if(_Jv>_Ju){return new F(function(){return _J2(_);});}else{if(_Ju>_Jw){return new F(function(){return _J2(_);});}else{var _Jz=_Jq-_Jv|0;if(0>_Jz){return new F(function(){return _GX(_Jz,_Jx);});}else{if(_Jz>=_Jx){return new F(function(){return _GX(_Jz,_Jx);});}else{var _JA=E(_Jy[_Jz]),_JB=_Ju-_Jv|0;if(0>_JB){return new F(function(){return _GX(_JB,_Jx);});}else{if(_JB>=_Jx){return new F(function(){return _GX(_JB,_Jx);});}else{var _JC=E(_Jy[_JB]),_JD=__app2(E(_Jb),B(_jD(new T2(1,new T2(0,_CE,_JA.h),new T2(1,new T2(0,_CD,_JA.i),_o)))),B(_jD(new T2(1,new T2(0,_CE,_JC.h),new T2(1,new T2(0,_CD,_JC.i),_o))))),_JE=__arr2lst(0,_JD),_JF=B(_Ea(_JE,_)),_JG=function(_JH,_JI,_){var _JJ=E(_JH);if(!_JJ._){return new T2(0,_o,_JI);}else{var _JK=E(_JJ.a),_JL=E(_JK.b),_JM=E(_JK.a),_JN=E(_JK.c),_JO=_JN.a,_JP=_JN.b,_JQ=E(_JK.e),_JR=E(_JK.d),_JS=_JR.a,_JT=_JR.b,_JU=E(_JK.f),_JV=B(_JG(_JJ.b,_JI,_));return new T2(0,new T2(1,new T(function(){var _JW=E(_JL.a)+ -E(_JM.a),_JX=E(_JL.b)+ -E(_JM.b),_JY=E(_JL.c)+ -E(_JM.c),_JZ=B(A1(_Jg,_JM)),_K0=B(_kq(_iR,_JZ.a,_JZ.b,_JZ.c)),_K1=Math.sqrt(B(_kg(_iR,_JW,_JX,_JY,_JW,_JX,_JY))),_K2=1/_K1,_K3=_JW*_K2,_K4=_JX*_K2,_K5=_JY*_K2,_K6=B(_lg(_iR,_K3,_K4,_K5,_K0.a,_K0.b,_K0.c)),_K7=B(_kq(_iR,_JQ.a,_JQ.b,_JQ.c)),_K8=E(_K7.b),_K9=B(A1(_Jg,_JL)),_Ka=B(_kq(_iR,_K9.a,_K9.b,_K9.c)),_Kb=B(_lg(_iR,_K3,_K4,_K5,_Ka.a,_Ka.b,_Ka.c)),_Kc=B(_kq(_iR,_JU.a,_JU.b,_JU.c)),_Kd=E(_Kc.b),_Ke=Math.sqrt(B(_IS(_iR,_JO,_JP,_JO,_JP))),_Kf=Math.sqrt(B(_IS(_iR,_JS,_JT,_JS,_JT)));return new T5(0,_Jq,_Ju,E(new T2(0,E(new T3(0,E(_K6.a),E(_K6.b),E(_K6.c))),_K5*_Ke*E(_K7.a)-_Ke*E(_K7.c)*_K3)),E(new T2(0,E(new T3(0,E(_Kb.a),E(_Kb.b),E(_Kb.c))),_K5*_Kf*E(_Kc.a)-_Kf*E(_Kc.c)*_K3)),_K1);}),new T(function(){return E(E(_JV).a);})),new T(function(){return E(E(_JV).b);}));}},_Kg=B(_JG(_JF,new T4(0,E(_Jv),E(_Jw),_Jx,_Jy),_));if(_Ju!=_Jo){var _Kh=E(_Kg),_Ki=E(_Kh.b),_Kj=B(_Jt(_Ju+1|0,E(_Ki.a),E(_Ki.b),_Ki.c,_Ki.d,_));return new T2(0,new T2(1,_Kh.a,new T(function(){return E(E(_Kj).a);})),new T(function(){return E(E(_Kj).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_Kg).a);}),_o),new T(function(){return E(E(_Kg).b);}));}}}}}}}}}},_Kk=B(_Jt(_Jq,E(_Js.a),E(_Js.b),_Js.c,_Js.d,_));if(_Jq!=_Jo){var _Kl=B(_Jp(_Jq+1|0,new T(function(){return E(E(_Kk).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Jc(E(_Kk).a));}),new T(function(){return E(E(_Kl).a);})),new T(function(){return E(E(_Kl).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Jc(E(_Kk).a));}),_o),new T(function(){return E(E(_Kk).b);}));}}else{if(_Jq!=_Jo){var _Km=B(_Jp(_Jq+1|0,_Jr,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Km).a);})),new T(function(){return E(E(_Km).b);}));}else{return new T2(0,new T2(1,_o,_o),_Jr);}}},_Kn=function(_Ko,_Kp,_Kq,_Kr,_Ks,_){if(_Ko<=_Jo){var _Kt=function(_Ku,_Kv,_Kw,_Kx,_Ky,_){if(_Kv>_Ko){return new F(function(){return die(_Jj);});}else{if(_Ko>_Kw){return new F(function(){return die(_Jj);});}else{if(_Kv>_Ku){return new F(function(){return _J2(_);});}else{if(_Ku>_Kw){return new F(function(){return _J2(_);});}else{var _Kz=_Ko-_Kv|0;if(0>_Kz){return new F(function(){return _GX(_Kz,_Kx);});}else{if(_Kz>=_Kx){return new F(function(){return _GX(_Kz,_Kx);});}else{var _KA=E(_Ky[_Kz]),_KB=_Ku-_Kv|0;if(0>_KB){return new F(function(){return _GX(_KB,_Kx);});}else{if(_KB>=_Kx){return new F(function(){return _GX(_KB,_Kx);});}else{var _KC=E(_Ky[_KB]),_KD=__app2(E(_Jb),B(_jD(new T2(1,new T2(0,_CE,_KA.h),new T2(1,new T2(0,_CD,_KA.i),_o)))),B(_jD(new T2(1,new T2(0,_CE,_KC.h),new T2(1,new T2(0,_CD,_KC.i),_o))))),_KE=__arr2lst(0,_KD),_KF=B(_Ea(_KE,_)),_KG=function(_KH,_KI,_){var _KJ=E(_KH);if(!_KJ._){return new T2(0,_o,_KI);}else{var _KK=E(_KJ.a),_KL=E(_KK.b),_KM=E(_KK.a),_KN=E(_KK.c),_KO=_KN.a,_KP=_KN.b,_KQ=E(_KK.e),_KR=E(_KK.d),_KS=_KR.a,_KT=_KR.b,_KU=E(_KK.f),_KV=B(_KG(_KJ.b,_KI,_));return new T2(0,new T2(1,new T(function(){var _KW=E(_KL.a)+ -E(_KM.a),_KX=E(_KL.b)+ -E(_KM.b),_KY=E(_KL.c)+ -E(_KM.c),_KZ=B(A1(_Jg,_KM)),_L0=B(_kq(_iR,_KZ.a,_KZ.b,_KZ.c)),_L1=Math.sqrt(B(_kg(_iR,_KW,_KX,_KY,_KW,_KX,_KY))),_L2=1/_L1,_L3=_KW*_L2,_L4=_KX*_L2,_L5=_KY*_L2,_L6=B(_lg(_iR,_L3,_L4,_L5,_L0.a,_L0.b,_L0.c)),_L7=B(_kq(_iR,_KQ.a,_KQ.b,_KQ.c)),_L8=E(_L7.b),_L9=B(A1(_Jg,_KL)),_La=B(_kq(_iR,_L9.a,_L9.b,_L9.c)),_Lb=B(_lg(_iR,_L3,_L4,_L5,_La.a,_La.b,_La.c)),_Lc=B(_kq(_iR,_KU.a,_KU.b,_KU.c)),_Ld=E(_Lc.b),_Le=Math.sqrt(B(_IS(_iR,_KO,_KP,_KO,_KP))),_Lf=Math.sqrt(B(_IS(_iR,_KS,_KT,_KS,_KT)));return new T5(0,_Ko,_Ku,E(new T2(0,E(new T3(0,E(_L6.a),E(_L6.b),E(_L6.c))),_L5*_Le*E(_L7.a)-_Le*E(_L7.c)*_L3)),E(new T2(0,E(new T3(0,E(_Lb.a),E(_Lb.b),E(_Lb.c))),_L5*_Lf*E(_Lc.a)-_Lf*E(_Lc.c)*_L3)),_L1);}),new T(function(){return E(E(_KV).a);})),new T(function(){return E(E(_KV).b);}));}},_Lg=B(_KG(_KF,new T4(0,E(_Kv),E(_Kw),_Kx,_Ky),_));if(_Ku!=_Jo){var _Lh=E(_Lg),_Li=E(_Lh.b),_Lj=B(_Kt(_Ku+1|0,E(_Li.a),E(_Li.b),_Li.c,_Li.d,_));return new T2(0,new T2(1,_Lh.a,new T(function(){return E(E(_Lj).a);})),new T(function(){return E(E(_Lj).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_Lg).a);}),_o),new T(function(){return E(E(_Lg).b);}));}}}}}}}}}},_Lk=B(_Kt(_Ko,_Kp,_Kq,_Kr,_Ks,_));if(_Ko!=_Jo){var _Ll=B(_Jp(_Ko+1|0,new T(function(){return E(E(_Lk).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Jc(E(_Lk).a));}),new T(function(){return E(E(_Ll).a);})),new T(function(){return E(E(_Ll).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Jc(E(_Lk).a));}),_o),new T(function(){return E(E(_Lk).b);}));}}else{if(_Ko!=_Jo){var _Lm=B(_Kn(_Ko+1|0,_Kp,_Kq,_Kr,_Ks,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_Lm).a);})),new T(function(){return E(E(_Lm).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_Kp),E(_Kq),_Kr,_Ks));}}},_Ln=B(_Kn(_Jn,_Jn,_Jo,_Jm.c,_Jm.d,_));return new F(function(){return _IK(_,_Ln);});}else{return new F(function(){return _IK(_,new T2(0,_o,_Jm));});}},_Lo=new T(function(){return eval("__strict(refresh)");}),_Lp=function(_Lq,_){var _Lr=__app0(E(_Lo)),_Ls=__app0(E(_Dk)),_Lt=B(A(_Ce,[_BN,_Aa,_Di,_Lq,_])),_Lu=B(_Jk(_Lq,_));return new T(function(){return E(E(_Lu).b);});},_Lv=function(_Lw,_){while(1){var _Lx=E(_Lw);if(!_Lx._){return _jC;}else{var _Ly=_Lx.b,_Lz=E(_Lx.a);switch(_Lz._){case 0:var _LA=B(A1(_Lz.a,_));_Lw=B(_f(_Ly,new T2(1,_LA,_o)));continue;case 1:_Lw=B(_f(_Ly,_Lz.a));continue;default:_Lw=_Ly;continue;}}}},_LB=function(_LC,_LD,_){var _LE=E(_LC);switch(_LE._){case 0:var _LF=B(A1(_LE.a,_));return new F(function(){return _Lv(B(_f(_LD,new T2(1,_LF,_o))),_);});break;case 1:return new F(function(){return _Lv(B(_f(_LD,_LE.a)),_);});break;default:return new F(function(){return _Lv(_LD,_);});}},_LG=new T0(2),_LH=function(_LI){return new T0(2);},_LJ=function(_LK,_LL,_LM){return function(_){var _LN=E(_LK),_LO=rMV(_LN),_LP=E(_LO);if(!_LP._){var _LQ=new T(function(){var _LR=new T(function(){return B(A1(_LM,_jC));});return B(_f(_LP.b,new T2(1,new T2(0,_LL,function(_LS){return E(_LR);}),_o)));}),_=wMV(_LN,new T2(0,_LP.a,_LQ));return _LG;}else{var _LT=E(_LP.a);if(!_LT._){var _=wMV(_LN,new T2(0,_LL,_o));return new T(function(){return B(A1(_LM,_jC));});}else{var _=wMV(_LN,new T1(1,_LT.b));return new T1(1,new T2(1,new T(function(){return B(A1(_LM,_jC));}),new T2(1,new T(function(){return B(A2(_LT.a,_LL,_LH));}),_o)));}}};},_LU=new T(function(){return E(_pg);}),_LV=new T(function(){return eval("window.requestAnimationFrame");}),_LW=new T1(1,_o),_LX=function(_LY,_LZ){return function(_){var _M0=E(_LY),_M1=rMV(_M0),_M2=E(_M1);if(!_M2._){var _M3=_M2.a,_M4=E(_M2.b);if(!_M4._){var _=wMV(_M0,_LW);return new T(function(){return B(A1(_LZ,_M3));});}else{var _M5=E(_M4.a),_=wMV(_M0,new T2(0,_M5.a,_M4.b));return new T1(1,new T2(1,new T(function(){return B(A1(_LZ,_M3));}),new T2(1,new T(function(){return B(A1(_M5.b,_LH));}),_o)));}}else{var _M6=new T(function(){var _M7=function(_M8){var _M9=new T(function(){return B(A1(_LZ,_M8));});return function(_Ma){return E(_M9);};};return B(_f(_M2.a,new T2(1,_M7,_o)));}),_=wMV(_M0,new T1(1,_M6));return _LG;}};},_Mb=function(_Mc,_Md){return new T1(0,B(_LX(_Mc,_Md)));},_Me=function(_Mf,_Mg){var _Mh=new T(function(){return new T1(0,B(_LJ(_Mf,_jC,_LH)));});return function(_){var _Mi=__createJSFunc(2,function(_Mj,_){var _Mk=B(_LB(_Mh,_o,_));return _LU;}),_Ml=__app1(E(_LV),_Mi);return new T(function(){return B(_Mb(_Mf,_Mg));});};},_Mm=new T1(1,_o),_Mn=function(_Mo,_Mp,_){var _Mq=function(_){var _Mr=nMV(_Mo),_Ms=_Mr;return new T(function(){var _Mt=new T(function(){return B(_Mu(_));}),_Mv=function(_){var _Mw=rMV(_Ms),_Mx=B(A2(_Mp,_Mw,_)),_=wMV(_Ms,_Mx),_My=function(_){var _Mz=nMV(_Mm);return new T(function(){return new T1(0,B(_Me(_Mz,function(_MA){return E(_Mt);})));});};return new T1(0,_My);},_MB=new T(function(){return new T1(0,_Mv);}),_Mu=function(_MC){return E(_MB);};return B(_Mu(_));});};return new F(function(){return _LB(new T1(0,_Mq),_o,_);});},_MD=function(_){var _ME=__app2(E(_0),E(_7U),E(_he));return new F(function(){return _Mn(_zK,_Lp,_);});},_MF=function(_){return new F(function(){return _MD(_);});};
var hasteMain = function() {B(A(_MF, [0]));};window.onload = hasteMain;