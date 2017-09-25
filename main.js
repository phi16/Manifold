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

var _0=new T(function(){return eval("__strict(compile)");}),_1=new T(function(){return B(unCStr("y"));}),_2=new T(function(){return toJSStr(E(_1));}),_3=function(_4){return E(E(_4).b);},_5=function(_6){return E(E(_6).a);},_7=function(_8,_9,_a){var _b=E(_a);if(!_b._){return new F(function(){return A1(_9,_b.a);});}else{var _c=new T(function(){return B(_3(_8));}),_d=new T(function(){return B(_5(_8));}),_e=function(_f){var _g=E(_f);if(!_g._){return E(_d);}else{return new F(function(){return A2(_c,new T(function(){return B(_7(_8,_9,_g.a));}),new T(function(){return B(_e(_g.b));}));});}};return new F(function(){return _e(_b.a);});}},_h=function(_i,_j,_k){var _l=new T(function(){return B(_3(_i));}),_m=new T(function(){return B(_5(_i));}),_n=function(_o){var _p=E(_o);if(!_p._){return E(_m);}else{return new F(function(){return A2(_l,new T(function(){return B(_7(_i,_j,_p.a));}),new T(function(){return B(_n(_p.b));}));});}};return new F(function(){return _n(_k);});},_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v){var _w=E(_v);if(!_w._){return __Z;}else{return new F(function(){return _q(_w.a,new T(function(){return B(_u(_w.b));},1));});}},_x=function(_y){return new F(function(){return _u(_y);});},_z=__Z,_A=new T3(0,_z,_q,_x),_B=new T(function(){return B(unCStr("vec3("));}),_C=new T1(0,_B),_D=new T(function(){return B(unCStr(")"));}),_E=new T1(0,_D),_F=new T2(1,_E,_z),_G=new T(function(){return B(unCStr(","));}),_H=new T1(0,_G),_I=new T(function(){return B(unCStr("."));}),_J=new T1(0,1),_K=function(_L){while(1){var _M=E(_L);if(!_M._){_L=new T1(1,I_fromInt(_M.a));continue;}else{return new F(function(){return I_toString(_M.a);});}}},_N=function(_O,_P){return new F(function(){return _q(fromJSStr(B(_K(_O))),_P);});},_Q=function(_R,_S){var _T=E(_R);if(!_T._){var _U=_T.a,_V=E(_S);return (_V._==0)?_U<_V.a:I_compareInt(_V.a,_U)>0;}else{var _W=_T.a,_X=E(_S);return (_X._==0)?I_compareInt(_W,_X.a)<0:I_compare(_W,_X.a)<0;}},_Y=41,_Z=40,_10=new T1(0,0),_11=function(_12,_13,_14){if(_12<=6){return new F(function(){return _N(_13,_14);});}else{if(!B(_Q(_13,_10))){return new F(function(){return _N(_13,_14);});}else{return new T2(1,_Z,new T(function(){return B(_q(fromJSStr(B(_K(_13))),new T2(1,_Y,_14)));}));}}},_15=new T(function(){return B(_11(0,_J,_z));}),_16=new T(function(){return B(_q(_15,_I));}),_17=new T1(0,_16),_18=new T1(0,0),_19=new T(function(){return B(_11(0,_18,_z));}),_1a=new T(function(){return B(_q(_19,_I));}),_1b=new T1(0,_1a),_1c=new T2(1,_1b,_z),_1d=new T2(1,_17,_1c),_1e=function(_1f,_1g){var _1h=E(_1g);return (_1h._==0)?__Z:new T2(1,_1f,new T2(1,_1h.a,new T(function(){return B(_1e(_1f,_1h.b));})));},_1i=new T(function(){return B(_1e(_H,_1d));}),_1j=new T2(1,_1b,_1i),_1k=new T1(1,_1j),_1l=new T2(1,_1k,_F),_1m=new T2(1,_C,_1l),_1n=function(_1o){return E(_1o);},_1p=new T(function(){return toJSStr(B(_h(_A,_1n,_1m)));}),_1q=function(_1r,_1s){while(1){var _1t=E(_1r);if(!_1t._){return E(_1s);}else{var _1u=_1s+1|0;_1r=_1t.b;_1s=_1u;continue;}}},_1v=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1w=new T(function(){return B(err(_1v));}),_1x=0,_1y=new T3(0,E(_1x),E(_1x),E(_1x)),_1z=new T(function(){return B(unCStr("Negative exponent"));}),_1A=new T(function(){return B(err(_1z));}),_1B=function(_1C,_1D,_1E){while(1){if(!(_1D%2)){var _1F=_1C*_1C,_1G=quot(_1D,2);_1C=_1F;_1D=_1G;continue;}else{var _1H=E(_1D);if(_1H==1){return _1C*_1E;}else{var _1F=_1C*_1C,_1I=_1C*_1E;_1C=_1F;_1D=quot(_1H-1|0,2);_1E=_1I;continue;}}}},_1J=function(_1K,_1L){while(1){if(!(_1L%2)){var _1M=_1K*_1K,_1N=quot(_1L,2);_1K=_1M;_1L=_1N;continue;}else{var _1O=E(_1L);if(_1O==1){return E(_1K);}else{return new F(function(){return _1B(_1K*_1K,quot(_1O-1|0,2),_1K);});}}}},_1P=function(_1Q){var _1R=E(_1Q);return new F(function(){return Math.log(_1R+(_1R+1)*Math.sqrt((_1R-1)/(_1R+1)));});},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return Math.log(_1U+Math.sqrt(1+_1U*_1U));});},_1V=function(_1W){var _1X=E(_1W);return 0.5*Math.log((1+_1X)/(1-_1X));},_1Y=function(_1Z,_20){return Math.log(E(_20))/Math.log(E(_1Z));},_21=3.141592653589793,_22=new T1(0,1),_23=function(_24,_25){var _26=E(_24);if(!_26._){var _27=_26.a,_28=E(_25);if(!_28._){var _29=_28.a;return (_27!=_29)?(_27>_29)?2:0:1;}else{var _2a=I_compareInt(_28.a,_27);return (_2a<=0)?(_2a>=0)?1:2:0;}}else{var _2b=_26.a,_2c=E(_25);if(!_2c._){var _2d=I_compareInt(_2b,_2c.a);return (_2d>=0)?(_2d<=0)?1:2:0;}else{var _2e=I_compare(_2b,_2c.a);return (_2e>=0)?(_2e<=0)?1:2:0;}}},_2f=new T(function(){return B(unCStr("base"));}),_2g=new T(function(){return B(unCStr("GHC.Exception"));}),_2h=new T(function(){return B(unCStr("ArithException"));}),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2f,_2g,_2h),_2j=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2i,_z,_z),_2k=function(_2l){return E(_2j);},_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r){var _2s=B(A1(_2p,_)),_2t=B(A1(_2q,_)),_2u=hs_eqWord64(_2s.a,_2t.a);if(!_2u){return __Z;}else{var _2v=hs_eqWord64(_2s.b,_2t.b);return (!_2v)?__Z:new T1(1,_2r);}},_2w=function(_2x){var _2y=E(_2x);return new F(function(){return _2o(B(_2m(_2y.a)),_2k,_2y.b);});},_2z=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2A=new T(function(){return B(unCStr("denormal"));}),_2B=new T(function(){return B(unCStr("divide by zero"));}),_2C=new T(function(){return B(unCStr("loss of precision"));}),_2D=new T(function(){return B(unCStr("arithmetic underflow"));}),_2E=new T(function(){return B(unCStr("arithmetic overflow"));}),_2F=function(_2G,_2H){switch(E(_2G)){case 0:return new F(function(){return _q(_2E,_2H);});break;case 1:return new F(function(){return _q(_2D,_2H);});break;case 2:return new F(function(){return _q(_2C,_2H);});break;case 3:return new F(function(){return _q(_2B,_2H);});break;case 4:return new F(function(){return _q(_2A,_2H);});break;default:return new F(function(){return _q(_2z,_2H);});}},_2I=function(_2J){return new F(function(){return _2F(_2J,_z);});},_2K=function(_2L,_2M,_2N){return new F(function(){return _2F(_2M,_2N);});},_2O=44,_2P=93,_2Q=91,_2R=function(_2S,_2T,_2U){var _2V=E(_2T);if(!_2V._){return new F(function(){return unAppCStr("[]",_2U);});}else{var _2W=new T(function(){var _2X=new T(function(){var _2Y=function(_2Z){var _30=E(_2Z);if(!_30._){return E(new T2(1,_2P,_2U));}else{var _31=new T(function(){return B(A2(_2S,_30.a,new T(function(){return B(_2Y(_30.b));})));});return new T2(1,_2O,_31);}};return B(_2Y(_2V.b));});return B(A2(_2S,_2V.a,_2X));});return new T2(1,_2Q,_2W);}},_32=function(_33,_34){return new F(function(){return _2R(_2F,_33,_34);});},_35=new T3(0,_2K,_2I,_32),_36=new T(function(){return new T5(0,_2k,_35,_37,_2w,_2I);}),_37=function(_38){return new T2(0,_36,_38);},_39=3,_3a=new T(function(){return B(_37(_39));}),_3b=new T(function(){return die(_3a);}),_3c=function(_3d,_3e){var _3f=E(_3d);return (_3f._==0)?_3f.a*Math.pow(2,_3e):I_toNumber(_3f.a)*Math.pow(2,_3e);},_3g=function(_3h,_3i){var _3j=E(_3h);if(!_3j._){var _3k=_3j.a,_3l=E(_3i);return (_3l._==0)?_3k==_3l.a:(I_compareInt(_3l.a,_3k)==0)?true:false;}else{var _3m=_3j.a,_3n=E(_3i);return (_3n._==0)?(I_compareInt(_3m,_3n.a)==0)?true:false:(I_compare(_3m,_3n.a)==0)?true:false;}},_3o=function(_3p){var _3q=E(_3p);if(!_3q._){return E(_3q.a);}else{return new F(function(){return I_toInt(_3q.a);});}},_3r=function(_3s,_3t){while(1){var _3u=E(_3s);if(!_3u._){var _3v=_3u.a,_3w=E(_3t);if(!_3w._){var _3x=_3w.a,_3y=addC(_3v,_3x);if(!E(_3y.b)){return new T1(0,_3y.a);}else{_3s=new T1(1,I_fromInt(_3v));_3t=new T1(1,I_fromInt(_3x));continue;}}else{_3s=new T1(1,I_fromInt(_3v));_3t=_3w;continue;}}else{var _3z=E(_3t);if(!_3z._){_3s=_3u;_3t=new T1(1,I_fromInt(_3z.a));continue;}else{return new T1(1,I_add(_3u.a,_3z.a));}}}},_3A=function(_3B,_3C){while(1){var _3D=E(_3B);if(!_3D._){var _3E=E(_3D.a);if(_3E==(-2147483648)){_3B=new T1(1,I_fromInt(-2147483648));continue;}else{var _3F=E(_3C);if(!_3F._){var _3G=_3F.a;return new T2(0,new T1(0,quot(_3E,_3G)),new T1(0,_3E%_3G));}else{_3B=new T1(1,I_fromInt(_3E));_3C=_3F;continue;}}}else{var _3H=E(_3C);if(!_3H._){_3B=_3D;_3C=new T1(1,I_fromInt(_3H.a));continue;}else{var _3I=I_quotRem(_3D.a,_3H.a);return new T2(0,new T1(1,_3I.a),new T1(1,_3I.b));}}}},_3J=new T1(0,0),_3K=function(_3L,_3M){while(1){var _3N=E(_3L);if(!_3N._){_3L=new T1(1,I_fromInt(_3N.a));continue;}else{return new T1(1,I_shiftLeft(_3N.a,_3M));}}},_3O=function(_3P,_3Q,_3R){if(!B(_3g(_3R,_3J))){var _3S=B(_3A(_3Q,_3R)),_3T=_3S.a;switch(B(_23(B(_3K(_3S.b,1)),_3R))){case 0:return new F(function(){return _3c(_3T,_3P);});break;case 1:if(!(B(_3o(_3T))&1)){return new F(function(){return _3c(_3T,_3P);});}else{return new F(function(){return _3c(B(_3r(_3T,_22)),_3P);});}break;default:return new F(function(){return _3c(B(_3r(_3T,_22)),_3P);});}}else{return E(_3b);}},_3U=function(_3V,_3W){var _3X=E(_3V);if(!_3X._){var _3Y=_3X.a,_3Z=E(_3W);return (_3Z._==0)?_3Y>_3Z.a:I_compareInt(_3Z.a,_3Y)<0;}else{var _40=_3X.a,_41=E(_3W);return (_41._==0)?I_compareInt(_40,_41.a)>0:I_compare(_40,_41.a)>0;}},_42=new T1(0,1),_43=new T(function(){return B(unCStr("base"));}),_44=new T(function(){return B(unCStr("Control.Exception.Base"));}),_45=new T(function(){return B(unCStr("PatternMatchFail"));}),_46=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_43,_44,_45),_47=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_46,_z,_z),_48=function(_49){return E(_47);},_4a=function(_4b){var _4c=E(_4b);return new F(function(){return _2o(B(_2m(_4c.a)),_48,_4c.b);});},_4d=function(_4e){return E(E(_4e).a);},_4f=function(_4g){return new T2(0,_4h,_4g);},_4i=function(_4j,_4k){return new F(function(){return _q(E(_4j).a,_4k);});},_4l=function(_4m,_4n){return new F(function(){return _2R(_4i,_4m,_4n);});},_4o=function(_4p,_4q,_4r){return new F(function(){return _q(E(_4q).a,_4r);});},_4s=new T3(0,_4o,_4d,_4l),_4h=new T(function(){return new T5(0,_48,_4s,_4f,_4a,_4d);}),_4t=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4u=function(_4v){return E(E(_4v).c);},_4w=function(_4x,_4y){return new F(function(){return die(new T(function(){return B(A2(_4u,_4y,_4x));}));});},_4z=function(_4A,_38){return new F(function(){return _4w(_4A,_38);});},_4B=function(_4C,_4D){var _4E=E(_4D);if(!_4E._){return new T2(0,_z,_z);}else{var _4F=_4E.a;if(!B(A1(_4C,_4F))){return new T2(0,_z,_4E);}else{var _4G=new T(function(){var _4H=B(_4B(_4C,_4E.b));return new T2(0,_4H.a,_4H.b);});return new T2(0,new T2(1,_4F,new T(function(){return E(E(_4G).a);})),new T(function(){return E(E(_4G).b);}));}}},_4I=32,_4J=new T(function(){return B(unCStr("\n"));}),_4K=function(_4L){return (E(_4L)==124)?false:true;},_4M=function(_4N,_4O){var _4P=B(_4B(_4K,B(unCStr(_4N)))),_4Q=_4P.a,_4R=function(_4S,_4T){var _4U=new T(function(){var _4V=new T(function(){return B(_q(_4O,new T(function(){return B(_q(_4T,_4J));},1)));});return B(unAppCStr(": ",_4V));},1);return new F(function(){return _q(_4S,_4U);});},_4W=E(_4P.b);if(!_4W._){return new F(function(){return _4R(_4Q,_z);});}else{if(E(_4W.a)==124){return new F(function(){return _4R(_4Q,new T2(1,_4I,_4W.b));});}else{return new F(function(){return _4R(_4Q,_z);});}}},_4X=function(_4Y){return new F(function(){return _4z(new T1(0,new T(function(){return B(_4M(_4Y,_4t));})),_4h);});},_4Z=function(_50){var _51=function(_52,_53){while(1){if(!B(_Q(_52,_50))){if(!B(_3U(_52,_50))){if(!B(_3g(_52,_50))){return new F(function(){return _4X("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_53);}}else{return _53-1|0;}}else{var _54=B(_3K(_52,1)),_55=_53+1|0;_52=_54;_53=_55;continue;}}};return new F(function(){return _51(_42,0);});},_56=function(_57){var _58=E(_57);if(!_58._){var _59=_58.a>>>0;if(!_59){return -1;}else{var _5a=function(_5b,_5c){while(1){if(_5b>=_59){if(_5b<=_59){if(_5b!=_59){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5c);}}else{return _5c-1|0;}}else{var _5d=imul(_5b,2)>>>0,_5e=_5c+1|0;_5b=_5d;_5c=_5e;continue;}}};return new F(function(){return _5a(1,0);});}}else{return new F(function(){return _4Z(_58);});}},_5f=function(_5g){var _5h=E(_5g);if(!_5h._){var _5i=_5h.a>>>0;if(!_5i){return new T2(0,-1,0);}else{var _5j=function(_5k,_5l){while(1){if(_5k>=_5i){if(_5k<=_5i){if(_5k!=_5i){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5l);}}else{return _5l-1|0;}}else{var _5m=imul(_5k,2)>>>0,_5n=_5l+1|0;_5k=_5m;_5l=_5n;continue;}}};return new T2(0,B(_5j(1,0)),(_5i&_5i-1>>>0)>>>0&4294967295);}}else{var _5o=_5h.a;return new T2(0,B(_56(_5h)),I_compareInt(I_and(_5o,I_sub(_5o,I_fromInt(1))),0));}},_5p=function(_5q,_5r){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);return (_5u._==0)?_5t<=_5u.a:I_compareInt(_5u.a,_5t)>=0;}else{var _5v=_5s.a,_5w=E(_5r);return (_5w._==0)?I_compareInt(_5v,_5w.a)<=0:I_compare(_5v,_5w.a)<=0;}},_5x=function(_5y,_5z){while(1){var _5A=E(_5y);if(!_5A._){var _5B=_5A.a,_5C=E(_5z);if(!_5C._){return new T1(0,(_5B>>>0&_5C.a>>>0)>>>0&4294967295);}else{_5y=new T1(1,I_fromInt(_5B));_5z=_5C;continue;}}else{var _5D=E(_5z);if(!_5D._){_5y=_5A;_5z=new T1(1,I_fromInt(_5D.a));continue;}else{return new T1(1,I_and(_5A.a,_5D.a));}}}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){var _5K=_5J.a,_5L=subC(_5I,_5K);if(!E(_5L.b)){return new T1(0,_5L.a);}else{_5F=new T1(1,I_fromInt(_5I));_5G=new T1(1,I_fromInt(_5K));continue;}}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5M=E(_5G);if(!_5M._){_5F=_5H;_5G=new T1(1,I_fromInt(_5M.a));continue;}else{return new T1(1,I_sub(_5H.a,_5M.a));}}}},_5N=new T1(0,2),_5O=function(_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=(_5R.a>>>0&(2<<_5Q>>>0)-1>>>0)>>>0,_5T=1<<_5Q>>>0;return (_5T<=_5S)?(_5T>=_5S)?1:2:0;}else{var _5U=B(_5x(_5R,B(_5E(B(_3K(_5N,_5Q)),_42)))),_5V=B(_3K(_42,_5Q));return (!B(_3U(_5V,_5U)))?(!B(_Q(_5V,_5U)))?1:2:0;}},_5W=function(_5X,_5Y){while(1){var _5Z=E(_5X);if(!_5Z._){_5X=new T1(1,I_fromInt(_5Z.a));continue;}else{return new T1(1,I_shiftRight(_5Z.a,_5Y));}}},_60=function(_61,_62,_63,_64){var _65=B(_5f(_64)),_66=_65.a;if(!E(_65.b)){var _67=B(_56(_63));if(_67<((_66+_61|0)-1|0)){var _68=_66+(_61-_62|0)|0;if(_68>0){if(_68>_67){if(_68<=(_67+1|0)){if(!E(B(_5f(_63)).b)){return 0;}else{return new F(function(){return _3c(_22,_61-_62|0);});}}else{return 0;}}else{var _69=B(_5W(_63,_68));switch(B(_5O(_63,_68-1|0))){case 0:return new F(function(){return _3c(_69,_61-_62|0);});break;case 1:if(!(B(_3o(_69))&1)){return new F(function(){return _3c(_69,_61-_62|0);});}else{return new F(function(){return _3c(B(_3r(_69,_22)),_61-_62|0);});}break;default:return new F(function(){return _3c(B(_3r(_69,_22)),_61-_62|0);});}}}else{return new F(function(){return _3c(_63,(_61-_62|0)-_68|0);});}}else{if(_67>=_62){var _6a=B(_5W(_63,(_67+1|0)-_62|0));switch(B(_5O(_63,_67-_62|0))){case 0:return new F(function(){return _3c(_6a,((_67-_66|0)+1|0)-_62|0);});break;case 2:return new F(function(){return _3c(B(_3r(_6a,_22)),((_67-_66|0)+1|0)-_62|0);});break;default:if(!(B(_3o(_6a))&1)){return new F(function(){return _3c(_6a,((_67-_66|0)+1|0)-_62|0);});}else{return new F(function(){return _3c(B(_3r(_6a,_22)),((_67-_66|0)+1|0)-_62|0);});}}}else{return new F(function(){return _3c(_63, -_66);});}}}else{var _6b=B(_56(_63))-_66|0,_6c=function(_6d){var _6e=function(_6f,_6g){if(!B(_5p(B(_3K(_6g,_62)),_6f))){return new F(function(){return _3O(_6d-_62|0,_6f,_6g);});}else{return new F(function(){return _3O((_6d-_62|0)+1|0,_6f,B(_3K(_6g,1)));});}};if(_6d>=_62){if(_6d!=_62){return new F(function(){return _6e(_63,new T(function(){return B(_3K(_64,_6d-_62|0));}));});}else{return new F(function(){return _6e(_63,_64);});}}else{return new F(function(){return _6e(new T(function(){return B(_3K(_63,_62-_6d|0));}),_64);});}};if(_61>_6b){return new F(function(){return _6c(_61);});}else{return new F(function(){return _6c(_6b);});}}},_6h=new T1(0,2147483647),_6i=new T(function(){return B(_3r(_6h,_42));}),_6j=function(_6k){var _6l=E(_6k);if(!_6l._){var _6m=E(_6l.a);return (_6m==(-2147483648))?E(_6i):new T1(0, -_6m);}else{return new T1(1,I_negate(_6l.a));}},_6n=new T(function(){return 0/0;}),_6o=new T(function(){return -1/0;}),_6p=new T(function(){return 1/0;}),_6q=0,_6r=function(_6s,_6t){if(!B(_3g(_6t,_3J))){if(!B(_3g(_6s,_3J))){if(!B(_Q(_6s,_3J))){return new F(function(){return _60(-1021,53,_6s,_6t);});}else{return  -B(_60(-1021,53,B(_6j(_6s)),_6t));}}else{return E(_6q);}}else{return (!B(_3g(_6s,_3J)))?(!B(_Q(_6s,_3J)))?E(_6p):E(_6o):E(_6n);}},_6u=function(_6v){var _6w=E(_6v);return new F(function(){return _6r(_6w.a,_6w.b);});},_6x=function(_6y){return 1/E(_6y);},_6z=function(_6A){var _6B=E(_6A),_6C=E(_6B);return (_6C==0)?E(_6q):(_6C<=0)? -_6C:E(_6B);},_6D=function(_6E){var _6F=E(_6E);if(!_6F._){return _6F.a;}else{return new F(function(){return I_toNumber(_6F.a);});}},_6G=function(_6H){return new F(function(){return _6D(_6H);});},_6I=1,_6J=-1,_6K=function(_6L){var _6M=E(_6L);return (_6M<=0)?(_6M>=0)?E(_6M):E(_6J):E(_6I);},_6N=function(_6O,_6P){return E(_6O)-E(_6P);},_6Q=function(_6R){return  -E(_6R);},_6S=function(_6T,_6U){return E(_6T)+E(_6U);},_6V=function(_6W,_6X){return E(_6W)*E(_6X);},_6Y={_:0,a:_6S,b:_6N,c:_6V,d:_6Q,e:_6z,f:_6K,g:_6G},_6Z=function(_70,_71){return E(_70)/E(_71);},_72=new T4(0,_6Y,_6Z,_6x,_6u),_73=function(_74){return new F(function(){return Math.acos(E(_74));});},_75=function(_76){return new F(function(){return Math.asin(E(_76));});},_77=function(_78){return new F(function(){return Math.atan(E(_78));});},_79=function(_7a){return new F(function(){return Math.cos(E(_7a));});},_7b=function(_7c){return new F(function(){return cosh(E(_7c));});},_7d=function(_7e){return new F(function(){return Math.exp(E(_7e));});},_7f=function(_7g){return new F(function(){return Math.log(E(_7g));});},_7h=function(_7i,_7j){return new F(function(){return Math.pow(E(_7i),E(_7j));});},_7k=function(_7l){return new F(function(){return Math.sin(E(_7l));});},_7m=function(_7n){return new F(function(){return sinh(E(_7n));});},_7o=function(_7p){return new F(function(){return Math.sqrt(E(_7p));});},_7q=function(_7r){return new F(function(){return Math.tan(E(_7r));});},_7s=function(_7t){return new F(function(){return tanh(E(_7t));});},_7u={_:0,a:_72,b:_21,c:_7d,d:_7f,e:_7o,f:_7h,g:_1Y,h:_7k,i:_79,j:_7q,k:_75,l:_73,m:_77,n:_7m,o:_7b,p:_7s,q:_1S,r:_1P,s:_1V},_7v=function(_7w,_7x){return (E(_7w)!=E(_7x))?true:false;},_7y=function(_7z,_7A){return E(_7z)==E(_7A);},_7B=new T2(0,_7y,_7v),_7C=function(_7D,_7E){return E(_7D)<E(_7E);},_7F=function(_7G,_7H){return E(_7G)<=E(_7H);},_7I=function(_7J,_7K){return E(_7J)>E(_7K);},_7L=function(_7M,_7N){return E(_7M)>=E(_7N);},_7O=function(_7P,_7Q){var _7R=E(_7P),_7S=E(_7Q);return (_7R>=_7S)?(_7R!=_7S)?2:1:0;},_7T=function(_7U,_7V){var _7W=E(_7U),_7X=E(_7V);return (_7W>_7X)?E(_7W):E(_7X);},_7Y=function(_7Z,_80){var _81=E(_7Z),_82=E(_80);return (_81>_82)?E(_82):E(_81);},_83={_:0,a:_7B,b:_7O,c:_7C,d:_7F,e:_7I,f:_7L,g:_7T,h:_7Y},_84="dz",_85="wy",_86="wx",_87="dy",_88="dx",_89="t",_8a="a",_8b="r",_8c="ly",_8d="lx",_8e="wz",_8f=0,_8g=function(_8h){var _8i=__new(),_8j=_8i,_8k=function(_8l,_){while(1){var _8m=E(_8l);if(!_8m._){return _8f;}else{var _8n=E(_8m.a),_8o=__set(_8j,E(_8n.a),E(_8n.b));_8l=_8m.b;continue;}}},_8p=B(_8k(_8h,_));return E(_8j);},_8q=function(_8r,_8s,_8t,_8u,_8v,_8w,_8x,_8y,_8z){return new F(function(){return _8g(new T2(1,new T2(0,_86,_8r),new T2(1,new T2(0,_85,_8s),new T2(1,new T2(0,_8e,_8t),new T2(1,new T2(0,_8d,_8u*_8v*Math.cos(_8w)),new T2(1,new T2(0,_8c,_8u*_8v*Math.sin(_8w)),new T2(1,new T2(0,_8b,_8u),new T2(1,new T2(0,_8a,_8v),new T2(1,new T2(0,_89,_8w),new T2(1,new T2(0,_88,_8x),new T2(1,new T2(0,_87,_8y),new T2(1,new T2(0,_84,_8z),_z))))))))))));});},_8A=function(_8B){var _8C=E(_8B),_8D=E(_8C.a),_8E=E(_8C.b),_8F=E(_8C.d);return new F(function(){return _8q(_8D.a,_8D.b,_8D.c,E(_8E.a),E(_8E.b),E(_8C.c),_8F.a,_8F.b,_8F.c);});},_8G=function(_8H,_8I){var _8J=E(_8I);return (_8J._==0)?__Z:new T2(1,new T(function(){return B(A1(_8H,_8J.a));}),new T(function(){return B(_8G(_8H,_8J.b));}));},_8K=function(_8L,_8M,_8N){var _8O=__lst2arr(B(_8G(_8A,new T2(1,_8L,new T2(1,_8M,new T2(1,_8N,_z))))));return E(_8O);},_8P=function(_8Q){var _8R=E(_8Q);return new F(function(){return _8K(_8R.a,_8R.b,_8R.c);});},_8S=new T2(0,_7u,_83),_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).a);},_8X=function(_8Y){return E(E(_8Y).c);},_8Z=function(_90){return E(E(_90).a);},_91=function(_92,_93,_94,_95,_96,_97,_98){var _99=B(_8V(B(_8T(_92)))),_9a=new T(function(){return B(A3(_8Z,_99,new T(function(){return B(A3(_8X,_99,_93,_96));}),new T(function(){return B(A3(_8X,_99,_94,_97));})));});return new F(function(){return A3(_8Z,_99,_9a,new T(function(){return B(A3(_8X,_99,_95,_98));}));});},_9b=function(_9c){return E(E(_9c).b);},_9d=function(_9e){return E(E(_9e).e);},_9f=function(_9g,_9h,_9i,_9j){var _9k=B(_8T(_9g)),_9l=new T(function(){return B(A2(_9d,_9g,new T(function(){return B(_91(_9g,_9h,_9i,_9j,_9h,_9i,_9j));})));});return new T3(0,B(A3(_9b,_9k,_9h,_9l)),B(A3(_9b,_9k,_9i,_9l)),B(A3(_9b,_9k,_9j,_9l)));},_9m=function(_9n,_9o,_9p,_9q,_9r,_9s,_9t){var _9u=B(_8X(_9n));return new T3(0,B(A1(B(A1(_9u,_9o)),_9r)),B(A1(B(A1(_9u,_9p)),_9s)),B(A1(B(A1(_9u,_9q)),_9t)));},_9v=function(_9w,_9x,_9y,_9z,_9A,_9B,_9C){var _9D=B(_8Z(_9w));return new T3(0,B(A1(B(A1(_9D,_9x)),_9A)),B(A1(B(A1(_9D,_9y)),_9B)),B(A1(B(A1(_9D,_9z)),_9C)));},_9E=function(_9F){return E(E(_9F).g);},_9G=function(_9H){return E(E(_9H).d);},_9I=function(_9J,_9K){var _9L=new T(function(){return E(E(_9J).a);}),_9M=new T(function(){var _9N=E(_9K),_9O=new T(function(){return B(_8V(new T(function(){return B(_8T(_9L));})));}),_9P=B(A2(_9E,_9O,_18));return new T3(0,E(_9P),E(B(A2(_9E,_9O,_J))),E(_9P));}),_9Q=new T(function(){var _9R=E(_9M),_9S=B(_9f(_9L,_9R.a,_9R.b,_9R.c));return new T3(0,E(_9S.a),E(_9S.b),E(_9S.c));}),_9T=new T(function(){var _9U=E(_9K),_9V=_9U.b,_9W=E(_9Q),_9X=B(_8T(_9L)),_9Y=new T(function(){return B(A2(_9d,_9L,new T(function(){var _9Z=E(_9M),_a0=_9Z.a,_a1=_9Z.b,_a2=_9Z.c;return B(_91(_9L,_a0,_a1,_a2,_a0,_a1,_a2));})));}),_a3=B(A3(_9b,_9X,_9V,_9Y)),_a4=B(_8V(_9X)),_a5=B(_9m(_a4,_9W.a,_9W.b,_9W.c,_a3,_a3,_a3)),_a6=B(_9G(_a4)),_a7=B(_9v(_a4,_9U.a,_9V,_9U.c,B(A1(_a6,_a5.a)),B(A1(_a6,_a5.b)),B(A1(_a6,_a5.c))));return new T3(0,E(_a7.a),E(_a7.b),E(_a7.c));});return new T2(0,_9T,_9Q);},_a8=function(_a9){return E(E(_a9).a);},_aa=function(_ab,_ac,_ad,_ae,_af,_ag,_ah){var _ai=B(_91(_ab,_af,_ag,_ah,_ac,_ad,_ae)),_aj=B(_8V(B(_8T(_ab)))),_ak=B(_9m(_aj,_af,_ag,_ah,_ai,_ai,_ai)),_al=B(_9G(_aj));return new F(function(){return _9v(_aj,_ac,_ad,_ae,B(A1(_al,_ak.a)),B(A1(_al,_ak.b)),B(A1(_al,_ak.c)));});},_am=function(_an){return E(E(_an).a);},_ao=function(_ap,_aq,_ar,_as){var _at=new T(function(){var _au=E(_as),_av=E(_ar),_aw=B(_aa(_ap,_au.a,_au.b,_au.c,_av.a,_av.b,_av.c));return new T3(0,E(_aw.a),E(_aw.b),E(_aw.c));}),_ax=new T(function(){return B(A2(_9d,_ap,new T(function(){var _ay=E(_at),_az=_ay.a,_aA=_ay.b,_aB=_ay.c;return B(_91(_ap,_az,_aA,_aB,_az,_aA,_aB));})));});if(!B(A3(_am,B(_a8(_aq)),_ax,new T(function(){return B(A2(_9E,B(_8V(B(_8T(_ap)))),_18));})))){var _aC=E(_at),_aD=B(_9f(_ap,_aC.a,_aC.b,_aC.c)),_aE=B(A2(_9d,_ap,new T(function(){var _aF=E(_as),_aG=_aF.a,_aH=_aF.b,_aI=_aF.c;return B(_91(_ap,_aG,_aH,_aI,_aG,_aH,_aI));}))),_aJ=B(_8X(new T(function(){return B(_8V(new T(function(){return B(_8T(_ap));})));})));return new T3(0,B(A1(B(A1(_aJ,_aD.a)),_aE)),B(A1(B(A1(_aJ,_aD.b)),_aE)),B(A1(B(A1(_aJ,_aD.c)),_aE)));}else{var _aK=B(A2(_9E,B(_8V(B(_8T(_ap)))),_18));return new T3(0,_aK,_aK,_aK);}},_aL=new T(function(){var _aM=eval("angleCount"),_aN=Number(_aM);return jsTrunc(_aN);}),_aO=new T(function(){return E(_aL);}),_aP=new T(function(){return B(unCStr(": empty list"));}),_aQ=new T(function(){return B(unCStr("Prelude."));}),_aR=function(_aS){return new F(function(){return err(B(_q(_aQ,new T(function(){return B(_q(_aS,_aP));},1))));});},_aT=new T(function(){return B(unCStr("head"));}),_aU=new T(function(){return B(_aR(_aT));}),_aV=function(_aW,_aX,_aY){var _aZ=E(_aW);if(!_aZ._){return __Z;}else{var _b0=E(_aX);if(!_b0._){return __Z;}else{var _b1=_b0.a,_b2=E(_aY);if(!_b2._){return __Z;}else{var _b3=E(_b2.a),_b4=_b3.a;return new F(function(){return _q(new T2(1,new T(function(){return new T3(0,E(_aZ.a),E(_b1),E(_b4));}),new T2(1,new T(function(){return new T3(0,E(_b1),E(_b4),E(_b3.b));}),_z)),new T(function(){return B(_aV(_aZ.b,_b0.b,_b2.b));},1));});}}}},_b5=new T(function(){return B(unCStr("tail"));}),_b6=new T(function(){return B(_aR(_b5));}),_b7=function(_b8,_b9){var _ba=E(_b8);if(!_ba._){return __Z;}else{var _bb=E(_b9);return (_bb._==0)?__Z:new T2(1,new T2(0,_ba.a,_bb.a),new T(function(){return B(_b7(_ba.b,_bb.b));}));}},_bc=function(_bd,_be){var _bf=E(_bd);if(!_bf._){return __Z;}else{var _bg=E(_be);if(!_bg._){return __Z;}else{var _bh=E(_bf.a),_bi=_bh.b,_bj=E(_bg.a).b,_bk=new T(function(){var _bl=new T(function(){return B(_b7(_bj,new T(function(){var _bm=E(_bj);if(!_bm._){return E(_b6);}else{return E(_bm.b);}},1)));},1);return B(_aV(_bi,new T(function(){var _bn=E(_bi);if(!_bn._){return E(_b6);}else{return E(_bn.b);}},1),_bl));});return new F(function(){return _q(new T2(1,new T(function(){var _bo=E(_bi);if(!_bo._){return E(_aU);}else{var _bp=E(_bj);if(!_bp._){return E(_aU);}else{return new T3(0,E(_bh.a),E(_bo.a),E(_bp.a));}}}),_bk),new T(function(){return B(_bc(_bf.b,_bg.b));},1));});}}},_bq=new T(function(){return E(_aO)-1;}),_br=new T1(0,1),_bs=function(_bt,_bu){var _bv=E(_bu),_bw=new T(function(){var _bx=B(_8V(_bt)),_by=B(_bs(_bt,B(A3(_8Z,_bx,_bv,new T(function(){return B(A2(_9E,_bx,_br));})))));return new T2(1,_by.a,_by.b);});return new T2(0,_bv,_bw);},_bz=function(_bA){return E(E(_bA).d);},_bB=new T1(0,2),_bC=function(_bD,_bE){var _bF=E(_bE);if(!_bF._){return __Z;}else{var _bG=_bF.a;return (!B(A1(_bD,_bG)))?__Z:new T2(1,_bG,new T(function(){return B(_bC(_bD,_bF.b));}));}},_bH=function(_bI,_bJ,_bK,_bL){var _bM=B(_bs(_bJ,_bK)),_bN=new T(function(){var _bO=B(_8V(_bJ)),_bP=new T(function(){return B(A3(_9b,_bJ,new T(function(){return B(A2(_9E,_bO,_br));}),new T(function(){return B(A2(_9E,_bO,_bB));})));});return B(A3(_8Z,_bO,_bL,_bP));});return new F(function(){return _bC(function(_bQ){return new F(function(){return A3(_bz,_bI,_bQ,_bN);});},new T2(1,_bM.a,_bM.b));});},_bR=new T(function(){return B(_bH(_83,_72,_1x,_bq));}),_bS=function(_bT,_bU){while(1){var _bV=E(_bT);if(!_bV._){return E(_bU);}else{_bT=_bV.b;_bU=_bV.a;continue;}}},_bW=new T(function(){return B(unCStr("last"));}),_bX=new T(function(){return B(_aR(_bW));}),_bY=function(_bZ){return new F(function(){return _bS(_bZ,_bX);});},_c0=function(_c1){return new F(function(){return _bY(E(_c1).b);});},_c2=new T(function(){var _c3=eval("proceedCount"),_c4=Number(_c3);return jsTrunc(_c4);}),_c5=new T(function(){return E(_c2);}),_c6=1,_c7=new T(function(){return B(_bH(_83,_72,_c6,_c5));}),_c8=function(_c9,_ca,_cb,_cc,_cd,_ce,_cf,_cg,_ch,_ci,_cj,_ck,_cl,_cm){var _cn=new T(function(){var _co=new T(function(){var _cp=E(_ci),_cq=E(_cm),_cr=E(_cl),_cs=E(_cj),_ct=E(_ck),_cu=E(_ch);return new T3(0,_cp*_cq-_cr*_cs,_cs*_ct-_cq*_cu,_cu*_cr-_ct*_cp);}),_cv=function(_cw){var _cx=new T(function(){var _cy=E(_cw)/E(_aO);return (_cy+_cy)*3.141592653589793;}),_cz=new T(function(){return B(A1(_c9,_cx));}),_cA=new T(function(){var _cB=new T(function(){var _cC=E(_cz)/E(_c5);return new T3(0,E(_cC),E(_cC),E(_cC));}),_cD=function(_cE,_cF){var _cG=E(_cE);if(!_cG._){return new T2(0,_z,_cF);}else{var _cH=new T(function(){var _cI=B(_9I(_8S,new T(function(){var _cJ=E(_cF),_cK=E(_cJ.a),_cL=E(_cJ.b),_cM=E(_cB);return new T3(0,E(_cK.a)+E(_cL.a)*E(_cM.a),E(_cK.b)+E(_cL.b)*E(_cM.b),E(_cK.c)+E(_cL.c)*E(_cM.c));}))),_cN=_cI.a,_cO=new T(function(){var _cP=E(_cI.b),_cQ=E(E(_cF).b),_cR=B(_aa(_7u,_cQ.a,_cQ.b,_cQ.c,_cP.a,_cP.b,_cP.c)),_cS=B(_9f(_7u,_cR.a,_cR.b,_cR.c));return new T3(0,E(_cS.a),E(_cS.b),E(_cS.c));});return new T2(0,new T(function(){var _cT=E(_cz),_cU=E(_cx);return new T4(0,E(_cN),E(new T2(0,E(_cG.a)/E(_c5),E(_cT))),E(_cU),E(_cO));}),new T2(0,_cN,_cO));}),_cV=new T(function(){var _cW=B(_cD(_cG.b,new T(function(){return E(E(_cH).b);})));return new T2(0,_cW.a,_cW.b);});return new T2(0,new T2(1,new T(function(){return E(E(_cH).a);}),new T(function(){return E(E(_cV).a);})),new T(function(){return E(E(_cV).b);}));}},_cX=function(_cY,_cZ,_d0,_d1,_d2){var _d3=E(_cY);if(!_d3._){return new T2(0,_z,new T2(0,new T3(0,E(_cZ),E(_d0),E(_d1)),_d2));}else{var _d4=new T(function(){var _d5=B(_9I(_8S,new T(function(){var _d6=E(_d2),_d7=E(_cB);return new T3(0,E(_cZ)+E(_d6.a)*E(_d7.a),E(_d0)+E(_d6.b)*E(_d7.b),E(_d1)+E(_d6.c)*E(_d7.c));}))),_d8=_d5.a,_d9=new T(function(){var _da=E(_d5.b),_db=E(_d2),_dc=B(_aa(_7u,_db.a,_db.b,_db.c,_da.a,_da.b,_da.c)),_dd=B(_9f(_7u,_dc.a,_dc.b,_dc.c));return new T3(0,E(_dd.a),E(_dd.b),E(_dd.c));});return new T2(0,new T(function(){var _de=E(_cz),_df=E(_cx);return new T4(0,E(_d8),E(new T2(0,E(_d3.a)/E(_c5),E(_de))),E(_df),E(_d9));}),new T2(0,_d8,_d9));}),_dg=new T(function(){var _dh=B(_cD(_d3.b,new T(function(){return E(E(_d4).b);})));return new T2(0,_dh.a,_dh.b);});return new T2(0,new T2(1,new T(function(){return E(E(_d4).a);}),new T(function(){return E(E(_dg).a);})),new T(function(){return E(E(_dg).b);}));}};return E(B(_cX(_c7,_cc,_cd,_ce,new T(function(){var _di=E(_co),_dj=E(_cx)+_cf,_dk=Math.cos(_dj),_dl=Math.sin(_dj);return new T3(0,E(_ch)*_dk+E(_di.a)*_dl,E(_ci)*_dk+E(_di.b)*_dl,E(_cj)*_dk+E(_di.c)*_dl);}))).a);});return new T2(0,new T(function(){var _dm=E(_cz),_dn=E(_cx);return new T4(0,E(new T3(0,E(_cc),E(_cd),E(_ce))),E(new T2(0,E(_1x),E(_dm))),E(_dn),E(_1y));}),_cA);};return B(_8G(_cv,_bR));}),_do=new T(function(){var _dp=new T(function(){var _dq=B(_q(_cn,new T2(1,new T(function(){var _dr=E(_cn);if(!_dr._){return E(_aU);}else{return E(_dr.a);}}),_z)));if(!_dq._){return E(_b6);}else{return E(_dq.b);}},1);return B(_bc(_cn,_dp));});return new T2(0,_do,new T(function(){return B(_8G(_c0,_cn));}));},_ds=function(_dt,_du,_dv,_dw,_dx,_dy,_dz,_dA,_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dI,_dJ){var _dK=B(_9I(_8S,new T3(0,E(_dw),E(_dx),E(_dy)))),_dL=_dK.b,_dM=E(_dK.a),_dN=B(_ao(_7u,_83,_dL,new T3(0,E(_dA),E(_dB),E(_dC)))),_dO=E(_dL),_dP=_dO.a,_dQ=_dO.b,_dR=_dO.c,_dS=B(_aa(_7u,_dE,_dF,_dG,_dP,_dQ,_dR)),_dT=B(_9f(_7u,_dS.a,_dS.b,_dS.c)),_dU=_dT.a,_dV=_dT.b,_dW=_dT.c,_dX=E(_dz),_dY=new T2(0,E(new T3(0,E(_dN.a),E(_dN.b),E(_dN.c))),E(_dD)),_dZ=B(_c8(_dt,_du,_dv,_dM.a,_dM.b,_dM.c,_dX,_dY,_dU,_dV,_dW,_dP,_dQ,_dR)),_e0=__lst2arr(B(_8G(_8P,_dZ.a))),_e1=__lst2arr(B(_8G(_8A,_dZ.b)));return {_:0,a:_dt,b:_du,c:_dv,d:new T2(0,E(_dM),E(_dX)),e:_dY,f:new T3(0,E(_dU),E(_dV),E(_dW)),g:_dO,h:_e0,i:_e1};},_e2=function(_e3){var _e4=E(_e3);return new T3(0, -E(_e4.a), -E(_e4.b), -E(_e4.c));},_e5=new T(function(){return 6.283185307179586/E(_aO);}),_e6=function(_){return new F(function(){return __jsNull();});},_e7=function(_e8){var _e9=B(A1(_e8,_));return E(_e9);},_ea=new T(function(){return B(_e7(_e6));}),_eb=function(_ec,_ed,_ee,_ef,_eg,_eh,_ei,_ej,_ek,_el,_em,_en,_eo){var _ep=function(_eq){var _er=E(_e5),_es=2+_eq|0,_et=_es-1|0,_eu=(2+_eq)*(1+_eq),_ev=E(_bR);if(!_ev._){return _er*0;}else{var _ew=_ev.a,_ex=_ev.b,_ey=B(A1(_ec,new T(function(){return 6.283185307179586*E(_ew)/E(_aO);}))),_ez=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_ew)+1)/E(_aO);})));if(_ey!=_ez){if(_es>=0){var _eA=E(_es);if(!_eA){var _eB=function(_eC,_eD){while(1){var _eE=B((function(_eF,_eG){var _eH=E(_eF);if(!_eH._){return E(_eG);}else{var _eI=_eH.a,_eJ=_eH.b,_eK=B(A1(_ec,new T(function(){return 6.283185307179586*E(_eI)/E(_aO);}))),_eL=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_eI)+1)/E(_aO);})));if(_eK!=_eL){var _eM=_eG+0/(_eK-_eL)/_eu;_eC=_eJ;_eD=_eM;return __continue;}else{if(_et>=0){var _eN=E(_et);if(!_eN){var _eM=_eG+_es/_eu;_eC=_eJ;_eD=_eM;return __continue;}else{var _eM=_eG+_es*B(_1J(_eK,_eN))/_eu;_eC=_eJ;_eD=_eM;return __continue;}}else{return E(_1A);}}}})(_eC,_eD));if(_eE!=__continue){return _eE;}}};return _er*B(_eB(_ex,0/(_ey-_ez)/_eu));}else{var _eO=function(_eP,_eQ){while(1){var _eR=B((function(_eS,_eT){var _eU=E(_eS);if(!_eU._){return E(_eT);}else{var _eV=_eU.a,_eW=_eU.b,_eX=B(A1(_ec,new T(function(){return 6.283185307179586*E(_eV)/E(_aO);}))),_eY=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_eV)+1)/E(_aO);})));if(_eX!=_eY){if(_eA>=0){var _eZ=_eT+(B(_1J(_eX,_eA))-B(_1J(_eY,_eA)))/(_eX-_eY)/_eu;_eP=_eW;_eQ=_eZ;return __continue;}else{return E(_1A);}}else{if(_et>=0){var _f0=E(_et);if(!_f0){var _eZ=_eT+_es/_eu;_eP=_eW;_eQ=_eZ;return __continue;}else{var _eZ=_eT+_es*B(_1J(_eX,_f0))/_eu;_eP=_eW;_eQ=_eZ;return __continue;}}else{return E(_1A);}}}})(_eP,_eQ));if(_eR!=__continue){return _eR;}}};return _er*B(_eO(_ex,(B(_1J(_ey,_eA))-B(_1J(_ez,_eA)))/(_ey-_ez)/_eu));}}else{return E(_1A);}}else{if(_et>=0){var _f1=E(_et);if(!_f1){var _f2=function(_f3,_f4){while(1){var _f5=B((function(_f6,_f7){var _f8=E(_f6);if(!_f8._){return E(_f7);}else{var _f9=_f8.a,_fa=_f8.b,_fb=B(A1(_ec,new T(function(){return 6.283185307179586*E(_f9)/E(_aO);}))),_fc=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_f9)+1)/E(_aO);})));if(_fb!=_fc){if(_es>=0){var _fd=E(_es);if(!_fd){var _fe=_f7+0/(_fb-_fc)/_eu;_f3=_fa;_f4=_fe;return __continue;}else{var _fe=_f7+(B(_1J(_fb,_fd))-B(_1J(_fc,_fd)))/(_fb-_fc)/_eu;_f3=_fa;_f4=_fe;return __continue;}}else{return E(_1A);}}else{var _fe=_f7+_es/_eu;_f3=_fa;_f4=_fe;return __continue;}}})(_f3,_f4));if(_f5!=__continue){return _f5;}}};return _er*B(_f2(_ex,_es/_eu));}else{var _ff=function(_fg,_fh){while(1){var _fi=B((function(_fj,_fk){var _fl=E(_fj);if(!_fl._){return E(_fk);}else{var _fm=_fl.a,_fn=_fl.b,_fo=B(A1(_ec,new T(function(){return 6.283185307179586*E(_fm)/E(_aO);}))),_fp=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_fm)+1)/E(_aO);})));if(_fo!=_fp){if(_es>=0){var _fq=E(_es);if(!_fq){var _fr=_fk+0/(_fo-_fp)/_eu;_fg=_fn;_fh=_fr;return __continue;}else{var _fr=_fk+(B(_1J(_fo,_fq))-B(_1J(_fp,_fq)))/(_fo-_fp)/_eu;_fg=_fn;_fh=_fr;return __continue;}}else{return E(_1A);}}else{if(_f1>=0){var _fr=_fk+_es*B(_1J(_fo,_f1))/_eu;_fg=_fn;_fh=_fr;return __continue;}else{return E(_1A);}}}})(_fg,_fh));if(_fi!=__continue){return _fi;}}};return _er*B(_ff(_ex,_es*B(_1J(_ey,_f1))/_eu));}}else{return E(_1A);}}}},_fs=E(_ea),_ft=1/(B(_ep(1))*_ed);return new F(function(){return _ds(_ec,_e2,new T2(0,E(new T3(0,E(_ft),E(_ft),E(_ft))),1/(B(_ep(3))*_ed)),_ee,_ef,_eg,_eh,_ei,_ej,_ek,_el,_em,_en,_eo,_1y,_fs,_fs);});},_fu=1,_fv=function(_fw){var _fx=I_decodeDouble(_fw);return new T2(0,new T1(1,_fx.b),_fx.a);},_fy=function(_fz){return new T1(0,_fz);},_fA=function(_fB){var _fC=hs_intToInt64(2147483647),_fD=hs_leInt64(_fB,_fC);if(!_fD){return new T1(1,I_fromInt64(_fB));}else{var _fE=hs_intToInt64(-2147483648),_fF=hs_geInt64(_fB,_fE);if(!_fF){return new T1(1,I_fromInt64(_fB));}else{var _fG=hs_int64ToInt(_fB);return new F(function(){return _fy(_fG);});}}},_fH=new T(function(){var _fI=newByteArr(256),_fJ=_fI,_=_fJ["v"]["i8"][0]=8,_fK=function(_fL,_fM,_fN,_){while(1){if(_fN>=256){if(_fL>=256){return E(_);}else{var _fO=imul(2,_fL)|0,_fP=_fM+1|0,_fQ=_fL;_fL=_fO;_fM=_fP;_fN=_fQ;continue;}}else{var _=_fJ["v"]["i8"][_fN]=_fM,_fQ=_fN+_fL|0;_fN=_fQ;continue;}}},_=B(_fK(2,0,1,_));return _fJ;}),_fR=function(_fS,_fT){var _fU=hs_int64ToInt(_fS),_fV=E(_fH),_fW=_fV["v"]["i8"][(255&_fU>>>0)>>>0&4294967295];if(_fT>_fW){if(_fW>=8){var _fX=hs_uncheckedIShiftRA64(_fS,8),_fY=function(_fZ,_g0){while(1){var _g1=B((function(_g2,_g3){var _g4=hs_int64ToInt(_g2),_g5=_fV["v"]["i8"][(255&_g4>>>0)>>>0&4294967295];if(_g3>_g5){if(_g5>=8){var _g6=hs_uncheckedIShiftRA64(_g2,8),_g7=_g3-8|0;_fZ=_g6;_g0=_g7;return __continue;}else{return new T2(0,new T(function(){var _g8=hs_uncheckedIShiftRA64(_g2,_g5);return B(_fA(_g8));}),_g3-_g5|0);}}else{return new T2(0,new T(function(){var _g9=hs_uncheckedIShiftRA64(_g2,_g3);return B(_fA(_g9));}),0);}})(_fZ,_g0));if(_g1!=__continue){return _g1;}}};return new F(function(){return _fY(_fX,_fT-8|0);});}else{return new T2(0,new T(function(){var _ga=hs_uncheckedIShiftRA64(_fS,_fW);return B(_fA(_ga));}),_fT-_fW|0);}}else{return new T2(0,new T(function(){var _gb=hs_uncheckedIShiftRA64(_fS,_fT);return B(_fA(_gb));}),0);}},_gc=function(_gd){var _ge=hs_intToInt64(_gd);return E(_ge);},_gf=function(_gg){var _gh=E(_gg);if(!_gh._){return new F(function(){return _gc(_gh.a);});}else{return new F(function(){return I_toInt64(_gh.a);});}},_gi=function(_gj){return I_toInt(_gj)>>>0;},_gk=function(_gl){var _gm=E(_gl);if(!_gm._){return _gm.a>>>0;}else{return new F(function(){return _gi(_gm.a);});}},_gn=function(_go){var _gp=B(_fv(_go)),_gq=_gp.a,_gr=_gp.b;if(_gr<0){var _gs=function(_gt){if(!_gt){return new T2(0,E(_gq),B(_3K(_22, -_gr)));}else{var _gu=B(_fR(B(_gf(_gq)), -_gr));return new T2(0,E(_gu.a),B(_3K(_22,_gu.b)));}};if(!((B(_gk(_gq))&1)>>>0)){return new F(function(){return _gs(1);});}else{return new F(function(){return _gs(0);});}}else{return new T2(0,B(_3K(_gq,_gr)),_22);}},_gv=function(_gw){var _gx=B(_gn(E(_gw)));return new T2(0,E(_gx.a),E(_gx.b));},_gy=new T3(0,_6Y,_83,_gv),_gz=function(_gA){return E(E(_gA).a);},_gB=function(_gC){return E(E(_gC).a);},_gD=function(_gE,_gF){if(_gE<=_gF){var _gG=function(_gH){return new T2(1,_gH,new T(function(){if(_gH!=_gF){return B(_gG(_gH+1|0));}else{return __Z;}}));};return new F(function(){return _gG(_gE);});}else{return __Z;}},_gI=function(_gJ){return new F(function(){return _gD(E(_gJ),2147483647);});},_gK=function(_gL,_gM,_gN){if(_gN<=_gM){var _gO=new T(function(){var _gP=_gM-_gL|0,_gQ=function(_gR){return (_gR>=(_gN-_gP|0))?new T2(1,_gR,new T(function(){return B(_gQ(_gR+_gP|0));})):new T2(1,_gR,_z);};return B(_gQ(_gM));});return new T2(1,_gL,_gO);}else{return (_gN<=_gL)?new T2(1,_gL,_z):__Z;}},_gS=function(_gT,_gU,_gV){if(_gV>=_gU){var _gW=new T(function(){var _gX=_gU-_gT|0,_gY=function(_gZ){return (_gZ<=(_gV-_gX|0))?new T2(1,_gZ,new T(function(){return B(_gY(_gZ+_gX|0));})):new T2(1,_gZ,_z);};return B(_gY(_gU));});return new T2(1,_gT,_gW);}else{return (_gV>=_gT)?new T2(1,_gT,_z):__Z;}},_h0=function(_h1,_h2){if(_h2<_h1){return new F(function(){return _gK(_h1,_h2,-2147483648);});}else{return new F(function(){return _gS(_h1,_h2,2147483647);});}},_h3=function(_h4,_h5){return new F(function(){return _h0(E(_h4),E(_h5));});},_h6=function(_h7,_h8,_h9){if(_h8<_h7){return new F(function(){return _gK(_h7,_h8,_h9);});}else{return new F(function(){return _gS(_h7,_h8,_h9);});}},_ha=function(_hb,_hc,_hd){return new F(function(){return _h6(E(_hb),E(_hc),E(_hd));});},_he=function(_hf,_hg){return new F(function(){return _gD(E(_hf),E(_hg));});},_hh=function(_hi){return E(_hi);},_hj=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_hk=new T(function(){return B(err(_hj));}),_hl=function(_hm){var _hn=E(_hm);return (_hn==(-2147483648))?E(_hk):_hn-1|0;},_ho=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_hp=new T(function(){return B(err(_ho));}),_hq=function(_hr){var _hs=E(_hr);return (_hs==2147483647)?E(_hp):_hs+1|0;},_ht={_:0,a:_hq,b:_hl,c:_hh,d:_hh,e:_gI,f:_h3,g:_he,h:_ha},_hu=function(_hv,_hw){if(_hv<=0){if(_hv>=0){return new F(function(){return quot(_hv,_hw);});}else{if(_hw<=0){return new F(function(){return quot(_hv,_hw);});}else{return quot(_hv+1|0,_hw)-1|0;}}}else{if(_hw>=0){if(_hv>=0){return new F(function(){return quot(_hv,_hw);});}else{if(_hw<=0){return new F(function(){return quot(_hv,_hw);});}else{return quot(_hv+1|0,_hw)-1|0;}}}else{return quot(_hv-1|0,_hw)-1|0;}}},_hx=0,_hy=new T(function(){return B(_37(_hx));}),_hz=new T(function(){return die(_hy);}),_hA=function(_hB,_hC){var _hD=E(_hC);switch(_hD){case -1:var _hE=E(_hB);if(_hE==(-2147483648)){return E(_hz);}else{return new F(function(){return _hu(_hE,-1);});}break;case 0:return E(_3b);default:return new F(function(){return _hu(_hB,_hD);});}},_hF=function(_hG,_hH){return new F(function(){return _hA(E(_hG),E(_hH));});},_hI=0,_hJ=new T2(0,_hz,_hI),_hK=function(_hL,_hM){var _hN=E(_hL),_hO=E(_hM);switch(_hO){case -1:var _hP=E(_hN);if(_hP==(-2147483648)){return E(_hJ);}else{if(_hP<=0){if(_hP>=0){var _hQ=quotRemI(_hP,-1);return new T2(0,_hQ.a,_hQ.b);}else{var _hR=quotRemI(_hP,-1);return new T2(0,_hR.a,_hR.b);}}else{var _hS=quotRemI(_hP-1|0,-1);return new T2(0,_hS.a-1|0,(_hS.b+(-1)|0)+1|0);}}break;case 0:return E(_3b);default:if(_hN<=0){if(_hN>=0){var _hT=quotRemI(_hN,_hO);return new T2(0,_hT.a,_hT.b);}else{if(_hO<=0){var _hU=quotRemI(_hN,_hO);return new T2(0,_hU.a,_hU.b);}else{var _hV=quotRemI(_hN+1|0,_hO);return new T2(0,_hV.a-1|0,(_hV.b+_hO|0)-1|0);}}}else{if(_hO>=0){if(_hN>=0){var _hW=quotRemI(_hN,_hO);return new T2(0,_hW.a,_hW.b);}else{if(_hO<=0){var _hX=quotRemI(_hN,_hO);return new T2(0,_hX.a,_hX.b);}else{var _hY=quotRemI(_hN+1|0,_hO);return new T2(0,_hY.a-1|0,(_hY.b+_hO|0)-1|0);}}}else{var _hZ=quotRemI(_hN-1|0,_hO);return new T2(0,_hZ.a-1|0,(_hZ.b+_hO|0)+1|0);}}}},_i0=function(_i1,_i2){var _i3=_i1%_i2;if(_i1<=0){if(_i1>=0){return E(_i3);}else{if(_i2<=0){return E(_i3);}else{var _i4=E(_i3);return (_i4==0)?0:_i4+_i2|0;}}}else{if(_i2>=0){if(_i1>=0){return E(_i3);}else{if(_i2<=0){return E(_i3);}else{var _i5=E(_i3);return (_i5==0)?0:_i5+_i2|0;}}}else{var _i6=E(_i3);return (_i6==0)?0:_i6+_i2|0;}}},_i7=function(_i8,_i9){var _ia=E(_i9);switch(_ia){case -1:return E(_hI);case 0:return E(_3b);default:return new F(function(){return _i0(E(_i8),_ia);});}},_ib=function(_ic,_id){var _ie=E(_ic),_if=E(_id);switch(_if){case -1:var _ig=E(_ie);if(_ig==(-2147483648)){return E(_hz);}else{return new F(function(){return quot(_ig,-1);});}break;case 0:return E(_3b);default:return new F(function(){return quot(_ie,_if);});}},_ih=function(_ii,_ij){var _ik=E(_ii),_il=E(_ij);switch(_il){case -1:var _im=E(_ik);if(_im==(-2147483648)){return E(_hJ);}else{var _in=quotRemI(_im,-1);return new T2(0,_in.a,_in.b);}break;case 0:return E(_3b);default:var _io=quotRemI(_ik,_il);return new T2(0,_io.a,_io.b);}},_ip=function(_iq,_ir){var _is=E(_ir);switch(_is){case -1:return E(_hI);case 0:return E(_3b);default:return E(_iq)%_is;}},_it=function(_iu){return new F(function(){return _fy(E(_iu));});},_iv=function(_iw){return new T2(0,E(B(_fy(E(_iw)))),E(_br));},_ix=function(_iy,_iz){return imul(E(_iy),E(_iz))|0;},_iA=function(_iB,_iC){return E(_iB)+E(_iC)|0;},_iD=function(_iE,_iF){return E(_iE)-E(_iF)|0;},_iG=function(_iH){var _iI=E(_iH);return (_iI<0)? -_iI:E(_iI);},_iJ=function(_iK){return new F(function(){return _3o(_iK);});},_iL=function(_iM){return  -E(_iM);},_iN=-1,_iO=0,_iP=1,_iQ=function(_iR){var _iS=E(_iR);return (_iS>=0)?(E(_iS)==0)?E(_iO):E(_iP):E(_iN);},_iT={_:0,a:_iA,b:_iD,c:_ix,d:_iL,e:_iG,f:_iQ,g:_iJ},_iU=function(_iV,_iW){return E(_iV)==E(_iW);},_iX=function(_iY,_iZ){return E(_iY)!=E(_iZ);},_j0=new T2(0,_iU,_iX),_j1=function(_j2,_j3){var _j4=E(_j2),_j5=E(_j3);return (_j4>_j5)?E(_j4):E(_j5);},_j6=function(_j7,_j8){var _j9=E(_j7),_ja=E(_j8);return (_j9>_ja)?E(_ja):E(_j9);},_jb=function(_jc,_jd){return (_jc>=_jd)?(_jc!=_jd)?2:1:0;},_je=function(_jf,_jg){return new F(function(){return _jb(E(_jf),E(_jg));});},_jh=function(_ji,_jj){return E(_ji)>=E(_jj);},_jk=function(_jl,_jm){return E(_jl)>E(_jm);},_jn=function(_jo,_jp){return E(_jo)<=E(_jp);},_jq=function(_jr,_js){return E(_jr)<E(_js);},_jt={_:0,a:_j0,b:_je,c:_jq,d:_jn,e:_jk,f:_jh,g:_j1,h:_j6},_ju=new T3(0,_iT,_jt,_iv),_jv={_:0,a:_ju,b:_ht,c:_ib,d:_ip,e:_hF,f:_i7,g:_ih,h:_hK,i:_it},_jw=new T1(0,2),_jx=function(_jy,_jz){while(1){var _jA=E(_jy);if(!_jA._){var _jB=_jA.a,_jC=E(_jz);if(!_jC._){var _jD=_jC.a;if(!(imul(_jB,_jD)|0)){return new T1(0,imul(_jB,_jD)|0);}else{_jy=new T1(1,I_fromInt(_jB));_jz=new T1(1,I_fromInt(_jD));continue;}}else{_jy=new T1(1,I_fromInt(_jB));_jz=_jC;continue;}}else{var _jE=E(_jz);if(!_jE._){_jy=_jA;_jz=new T1(1,I_fromInt(_jE.a));continue;}else{return new T1(1,I_mul(_jA.a,_jE.a));}}}},_jF=function(_jG,_jH,_jI){while(1){if(!(_jH%2)){var _jJ=B(_jx(_jG,_jG)),_jK=quot(_jH,2);_jG=_jJ;_jH=_jK;continue;}else{var _jL=E(_jH);if(_jL==1){return new F(function(){return _jx(_jG,_jI);});}else{var _jJ=B(_jx(_jG,_jG)),_jM=B(_jx(_jG,_jI));_jG=_jJ;_jH=quot(_jL-1|0,2);_jI=_jM;continue;}}}},_jN=function(_jO,_jP){while(1){if(!(_jP%2)){var _jQ=B(_jx(_jO,_jO)),_jR=quot(_jP,2);_jO=_jQ;_jP=_jR;continue;}else{var _jS=E(_jP);if(_jS==1){return E(_jO);}else{return new F(function(){return _jF(B(_jx(_jO,_jO)),quot(_jS-1|0,2),_jO);});}}}},_jT=function(_jU){return E(E(_jU).b);},_jV=function(_jW){return E(E(_jW).b);},_jX=function(_jY){return E(E(_jY).c);},_jZ=new T1(0,0),_k0=function(_k1){return E(E(_k1).d);},_k2=function(_k3,_k4){var _k5=B(_gz(_k3)),_k6=new T(function(){return B(_gB(_k5));}),_k7=new T(function(){return B(A3(_k0,_k3,_k4,new T(function(){return B(A2(_9E,_k6,_bB));})));});return new F(function(){return A3(_am,B(_a8(B(_jT(_k5)))),_k7,new T(function(){return B(A2(_9E,_k6,_jZ));}));});},_k8=new T(function(){return B(unCStr("Negative exponent"));}),_k9=new T(function(){return B(err(_k8));}),_ka=function(_kb){return E(E(_kb).c);},_kc=function(_kd,_ke,_kf,_kg){var _kh=B(_gz(_ke)),_ki=new T(function(){return B(_gB(_kh));}),_kj=B(_jT(_kh));if(!B(A3(_jX,_kj,_kg,new T(function(){return B(A2(_9E,_ki,_jZ));})))){if(!B(A3(_am,B(_a8(_kj)),_kg,new T(function(){return B(A2(_9E,_ki,_jZ));})))){var _kk=new T(function(){return B(A2(_9E,_ki,_bB));}),_kl=new T(function(){return B(A2(_9E,_ki,_br));}),_km=B(_a8(_kj)),_kn=function(_ko,_kp,_kq){while(1){var _kr=B((function(_ks,_kt,_ku){if(!B(_k2(_ke,_kt))){if(!B(A3(_am,_km,_kt,_kl))){var _kv=new T(function(){return B(A3(_ka,_ke,new T(function(){return B(A3(_jV,_ki,_kt,_kl));}),_kk));});_ko=new T(function(){return B(A3(_8X,_kd,_ks,_ks));});_kp=_kv;_kq=new T(function(){return B(A3(_8X,_kd,_ks,_ku));});return __continue;}else{return new F(function(){return A3(_8X,_kd,_ks,_ku);});}}else{var _kw=_ku;_ko=new T(function(){return B(A3(_8X,_kd,_ks,_ks));});_kp=new T(function(){return B(A3(_ka,_ke,_kt,_kk));});_kq=_kw;return __continue;}})(_ko,_kp,_kq));if(_kr!=__continue){return _kr;}}},_kx=function(_ky,_kz){while(1){var _kA=B((function(_kB,_kC){if(!B(_k2(_ke,_kC))){if(!B(A3(_am,_km,_kC,_kl))){var _kD=new T(function(){return B(A3(_ka,_ke,new T(function(){return B(A3(_jV,_ki,_kC,_kl));}),_kk));});return new F(function(){return _kn(new T(function(){return B(A3(_8X,_kd,_kB,_kB));}),_kD,_kB);});}else{return E(_kB);}}else{_ky=new T(function(){return B(A3(_8X,_kd,_kB,_kB));});_kz=new T(function(){return B(A3(_ka,_ke,_kC,_kk));});return __continue;}})(_ky,_kz));if(_kA!=__continue){return _kA;}}};return new F(function(){return _kx(_kf,_kg);});}else{return new F(function(){return A2(_9E,_kd,_br);});}}else{return E(_k9);}},_kE=new T(function(){return B(err(_k8));}),_kF=function(_kG,_kH){var _kI=B(_fv(_kH)),_kJ=_kI.a,_kK=_kI.b,_kL=new T(function(){return B(_gB(new T(function(){return B(_gz(_kG));})));});if(_kK<0){var _kM= -_kK;if(_kM>=0){var _kN=E(_kM);if(!_kN){var _kO=E(_br);}else{var _kO=B(_jN(_jw,_kN));}if(!B(_3g(_kO,_3J))){var _kP=B(_3A(_kJ,_kO));return new T2(0,new T(function(){return B(A2(_9E,_kL,_kP.a));}),new T(function(){return B(_3c(_kP.b,_kK));}));}else{return E(_3b);}}else{return E(_kE);}}else{var _kQ=new T(function(){var _kR=new T(function(){return B(_kc(_kL,_jv,new T(function(){return B(A2(_9E,_kL,_jw));}),_kK));});return B(A3(_8X,_kL,new T(function(){return B(A2(_9E,_kL,_kJ));}),_kR));});return new T2(0,_kQ,_6q);}},_kS=function(_kT,_kU){var _kV=B(_kF(_kT,E(_kU))),_kW=_kV.a;if(E(_kV.b)<=0){return E(_kW);}else{var _kX=B(_gB(B(_gz(_kT))));return new F(function(){return A3(_8Z,_kX,_kW,new T(function(){return B(A2(_9E,_kX,_22));}));});}},_kY=function(_kZ,_l0){var _l1=B(_kF(_kZ,E(_l0))),_l2=_l1.a;if(E(_l1.b)>=0){return E(_l2);}else{var _l3=B(_gB(B(_gz(_kZ))));return new F(function(){return A3(_jV,_l3,_l2,new T(function(){return B(A2(_9E,_l3,_22));}));});}},_l4=function(_l5,_l6){var _l7=B(_kF(_l5,E(_l6)));return new T2(0,_l7.a,_l7.b);},_l8=function(_l9,_la){var _lb=B(_kF(_l9,_la)),_lc=_lb.a,_ld=E(_lb.b),_le=new T(function(){var _lf=B(_gB(B(_gz(_l9))));if(_ld>=0){return B(A3(_8Z,_lf,_lc,new T(function(){return B(A2(_9E,_lf,_22));})));}else{return B(A3(_jV,_lf,_lc,new T(function(){return B(A2(_9E,_lf,_22));})));}}),_lg=function(_lh){var _li=_lh-0.5;return (_li>=0)?(E(_li)==0)?(!B(_k2(_l9,_lc)))?E(_le):E(_lc):E(_le):E(_lc);},_lj=E(_ld);if(!_lj){return new F(function(){return _lg(0);});}else{if(_lj<=0){var _lk= -_lj-0.5;return (_lk>=0)?(E(_lk)==0)?(!B(_k2(_l9,_lc)))?E(_le):E(_lc):E(_le):E(_lc);}else{return new F(function(){return _lg(_lj);});}}},_ll=function(_lm,_ln){return new F(function(){return _l8(_lm,E(_ln));});},_lo=function(_lp,_lq){return E(B(_kF(_lp,E(_lq))).a);},_lr={_:0,a:_gy,b:_72,c:_l4,d:_lo,e:_ll,f:_kS,g:_kY},_ls=new T1(0,1),_lt=function(_lu,_lv){var _lw=E(_lu);return new T2(0,_lw,new T(function(){var _lx=B(_lt(B(_3r(_lw,_lv)),_lv));return new T2(1,_lx.a,_lx.b);}));},_ly=function(_lz){var _lA=B(_lt(_lz,_ls));return new T2(1,_lA.a,_lA.b);},_lB=function(_lC,_lD){var _lE=B(_lt(_lC,new T(function(){return B(_5E(_lD,_lC));})));return new T2(1,_lE.a,_lE.b);},_lF=new T1(0,0),_lG=function(_lH,_lI){var _lJ=E(_lH);if(!_lJ._){var _lK=_lJ.a,_lL=E(_lI);return (_lL._==0)?_lK>=_lL.a:I_compareInt(_lL.a,_lK)<=0;}else{var _lM=_lJ.a,_lN=E(_lI);return (_lN._==0)?I_compareInt(_lM,_lN.a)>=0:I_compare(_lM,_lN.a)>=0;}},_lO=function(_lP,_lQ,_lR){if(!B(_lG(_lQ,_lF))){var _lS=function(_lT){return (!B(_Q(_lT,_lR)))?new T2(1,_lT,new T(function(){return B(_lS(B(_3r(_lT,_lQ))));})):__Z;};return new F(function(){return _lS(_lP);});}else{var _lU=function(_lV){return (!B(_3U(_lV,_lR)))?new T2(1,_lV,new T(function(){return B(_lU(B(_3r(_lV,_lQ))));})):__Z;};return new F(function(){return _lU(_lP);});}},_lW=function(_lX,_lY,_lZ){return new F(function(){return _lO(_lX,B(_5E(_lY,_lX)),_lZ);});},_m0=function(_m1,_m2){return new F(function(){return _lO(_m1,_ls,_m2);});},_m3=function(_m4){return new F(function(){return _3o(_m4);});},_m5=function(_m6){return new F(function(){return _5E(_m6,_ls);});},_m7=function(_m8){return new F(function(){return _3r(_m8,_ls);});},_m9=function(_ma){return new F(function(){return _fy(E(_ma));});},_mb={_:0,a:_m7,b:_m5,c:_m9,d:_m3,e:_ly,f:_lB,g:_m0,h:_lW},_mc=function(_md,_me){while(1){var _mf=E(_md);if(!_mf._){var _mg=E(_mf.a);if(_mg==(-2147483648)){_md=new T1(1,I_fromInt(-2147483648));continue;}else{var _mh=E(_me);if(!_mh._){return new T1(0,B(_hu(_mg,_mh.a)));}else{_md=new T1(1,I_fromInt(_mg));_me=_mh;continue;}}}else{var _mi=_mf.a,_mj=E(_me);return (_mj._==0)?new T1(1,I_div(_mi,I_fromInt(_mj.a))):new T1(1,I_div(_mi,_mj.a));}}},_mk=function(_ml,_mm){if(!B(_3g(_mm,_jZ))){return new F(function(){return _mc(_ml,_mm);});}else{return E(_3b);}},_mn=function(_mo,_mp){while(1){var _mq=E(_mo);if(!_mq._){var _mr=E(_mq.a);if(_mr==(-2147483648)){_mo=new T1(1,I_fromInt(-2147483648));continue;}else{var _ms=E(_mp);if(!_ms._){var _mt=_ms.a;return new T2(0,new T1(0,B(_hu(_mr,_mt))),new T1(0,B(_i0(_mr,_mt))));}else{_mo=new T1(1,I_fromInt(_mr));_mp=_ms;continue;}}}else{var _mu=E(_mp);if(!_mu._){_mo=_mq;_mp=new T1(1,I_fromInt(_mu.a));continue;}else{var _mv=I_divMod(_mq.a,_mu.a);return new T2(0,new T1(1,_mv.a),new T1(1,_mv.b));}}}},_mw=function(_mx,_my){if(!B(_3g(_my,_jZ))){var _mz=B(_mn(_mx,_my));return new T2(0,_mz.a,_mz.b);}else{return E(_3b);}},_mA=function(_mB,_mC){while(1){var _mD=E(_mB);if(!_mD._){var _mE=E(_mD.a);if(_mE==(-2147483648)){_mB=new T1(1,I_fromInt(-2147483648));continue;}else{var _mF=E(_mC);if(!_mF._){return new T1(0,B(_i0(_mE,_mF.a)));}else{_mB=new T1(1,I_fromInt(_mE));_mC=_mF;continue;}}}else{var _mG=_mD.a,_mH=E(_mC);return (_mH._==0)?new T1(1,I_mod(_mG,I_fromInt(_mH.a))):new T1(1,I_mod(_mG,_mH.a));}}},_mI=function(_mJ,_mK){if(!B(_3g(_mK,_jZ))){return new F(function(){return _mA(_mJ,_mK);});}else{return E(_3b);}},_mL=function(_mM,_mN){while(1){var _mO=E(_mM);if(!_mO._){var _mP=E(_mO.a);if(_mP==(-2147483648)){_mM=new T1(1,I_fromInt(-2147483648));continue;}else{var _mQ=E(_mN);if(!_mQ._){return new T1(0,quot(_mP,_mQ.a));}else{_mM=new T1(1,I_fromInt(_mP));_mN=_mQ;continue;}}}else{var _mR=_mO.a,_mS=E(_mN);return (_mS._==0)?new T1(0,I_toInt(I_quot(_mR,I_fromInt(_mS.a)))):new T1(1,I_quot(_mR,_mS.a));}}},_mT=function(_mU,_mV){if(!B(_3g(_mV,_jZ))){return new F(function(){return _mL(_mU,_mV);});}else{return E(_3b);}},_mW=function(_mX,_mY){if(!B(_3g(_mY,_jZ))){var _mZ=B(_3A(_mX,_mY));return new T2(0,_mZ.a,_mZ.b);}else{return E(_3b);}},_n0=function(_n1,_n2){while(1){var _n3=E(_n1);if(!_n3._){var _n4=E(_n3.a);if(_n4==(-2147483648)){_n1=new T1(1,I_fromInt(-2147483648));continue;}else{var _n5=E(_n2);if(!_n5._){return new T1(0,_n4%_n5.a);}else{_n1=new T1(1,I_fromInt(_n4));_n2=_n5;continue;}}}else{var _n6=_n3.a,_n7=E(_n2);return (_n7._==0)?new T1(1,I_rem(_n6,I_fromInt(_n7.a))):new T1(1,I_rem(_n6,_n7.a));}}},_n8=function(_n9,_na){if(!B(_3g(_na,_jZ))){return new F(function(){return _n0(_n9,_na);});}else{return E(_3b);}},_nb=function(_nc){return E(_nc);},_nd=function(_ne){return E(_ne);},_nf=function(_ng){var _nh=E(_ng);if(!_nh._){var _ni=E(_nh.a);return (_ni==(-2147483648))?E(_6i):(_ni<0)?new T1(0, -_ni):E(_nh);}else{var _nj=_nh.a;return (I_compareInt(_nj,0)>=0)?E(_nh):new T1(1,I_negate(_nj));}},_nk=new T1(0,0),_nl=new T1(0,-1),_nm=function(_nn){var _no=E(_nn);if(!_no._){var _np=_no.a;return (_np>=0)?(E(_np)==0)?E(_nk):E(_42):E(_nl);}else{var _nq=I_compareInt(_no.a,0);return (_nq<=0)?(E(_nq)==0)?E(_nk):E(_nl):E(_42);}},_nr={_:0,a:_3r,b:_5E,c:_jx,d:_6j,e:_nf,f:_nm,g:_nd},_ns=function(_nt,_nu){var _nv=E(_nt);if(!_nv._){var _nw=_nv.a,_nx=E(_nu);return (_nx._==0)?_nw!=_nx.a:(I_compareInt(_nx.a,_nw)==0)?false:true;}else{var _ny=_nv.a,_nz=E(_nu);return (_nz._==0)?(I_compareInt(_ny,_nz.a)==0)?false:true:(I_compare(_ny,_nz.a)==0)?false:true;}},_nA=new T2(0,_3g,_ns),_nB=function(_nC,_nD){return (!B(_5p(_nC,_nD)))?E(_nC):E(_nD);},_nE=function(_nF,_nG){return (!B(_5p(_nF,_nG)))?E(_nG):E(_nF);},_nH={_:0,a:_nA,b:_23,c:_Q,d:_5p,e:_3U,f:_lG,g:_nB,h:_nE},_nI=function(_nJ){return new T2(0,E(_nJ),E(_br));},_nK=new T3(0,_nr,_nH,_nI),_nL={_:0,a:_nK,b:_mb,c:_mT,d:_n8,e:_mk,f:_mI,g:_mW,h:_mw,i:_nb},_nM=function(_nN){return E(E(_nN).b);},_nO=function(_nP){return E(E(_nP).g);},_nQ=new T1(0,1),_nR=function(_nS,_nT,_nU){var _nV=B(_nM(_nS)),_nW=B(_8V(_nV)),_nX=new T(function(){var _nY=new T(function(){var _nZ=new T(function(){var _o0=new T(function(){return B(A3(_nO,_nS,_nL,new T(function(){return B(A3(_9b,_nV,_nT,_nU));})));});return B(A2(_9E,_nW,_o0));}),_o1=new T(function(){return B(A2(_9G,_nW,new T(function(){return B(A2(_9E,_nW,_nQ));})));});return B(A3(_8X,_nW,_o1,_nZ));});return B(A3(_8X,_nW,_nY,_nU));});return new F(function(){return A3(_8Z,_nW,_nT,_nX);});},_o2=1.5707963267948966,_o3=function(_o4){return 0.2/Math.cos(B(_nR(_lr,_o4,_o2))-0.7853981633974483);},_o5=0,_o6=new T(function(){var _o7=B(_eb(_o3,1.2,_o5,_o5,_fu,_o5,_o5,_o5,_o5,_o5,_fu,_fu,_fu));return {_:0,a:E(_o7.a),b:E(_o7.b),c:E(_o7.c),d:E(_o7.d),e:E(_o7.e),f:E(_o7.f),g:E(_o7.g),h:_o7.h,i:_o7.i};}),_o8=0,_o9=0.3,_oa=function(_ob){return E(_o9);},_oc=new T(function(){var _od=B(_eb(_oa,1.2,_fu,_o5,_fu,_o5,_o5,_o5,_o5,_o5,_fu,_fu,_fu));return {_:0,a:E(_od.a),b:E(_od.b),c:E(_od.c),d:E(_od.d),e:E(_od.e),f:E(_od.f),g:E(_od.g),h:_od.h,i:_od.i};}),_oe=new T(function(){var _of=B(_eb(_oa,1.2,_fu,_fu,_o5,_o5,_o5,_o5,_o5,_o5,_fu,_fu,_fu));return {_:0,a:E(_of.a),b:E(_of.b),c:E(_of.c),d:E(_of.d),e:E(_of.e),f:E(_of.f),g:E(_of.g),h:_of.h,i:_of.i};}),_og=2,_oh=function(_oi){return 0.3/Math.cos(B(_nR(_lr,_oi,_o2))-0.7853981633974483);},_oj=new T(function(){var _ok=B(_eb(_oh,1.2,_og,_fu,_fu,_o5,_o5,_o5,_o5,_o5,_fu,_fu,_fu));return {_:0,a:E(_ok.a),b:E(_ok.b),c:E(_ok.c),d:E(_ok.d),e:E(_ok.e),f:E(_ok.f),g:E(_ok.g),h:_ok.h,i:_ok.i};}),_ol=new T2(1,_oj,_z),_om=new T2(1,_oe,_ol),_on=new T2(1,_oc,_om),_oo=new T2(1,_o6,_on),_op=new T(function(){return B(unCStr("Negative range size"));}),_oq=new T(function(){return B(err(_op));}),_or=function(_){var _os=B(_1q(_oo,0))-1|0,_ot=function(_ou){if(_ou>=0){var _ov=newArr(_ou,_1w),_ow=_ov,_ox=E(_ou);if(!_ox){return new T4(0,E(_o8),E(_os),0,_ow);}else{var _oy=function(_oz,_oA,_){while(1){var _oB=E(_oz);if(!_oB._){return E(_);}else{var _=_ow[_oA]=_oB.a;if(_oA!=(_ox-1|0)){var _oC=_oA+1|0;_oz=_oB.b;_oA=_oC;continue;}else{return E(_);}}}},_=B((function(_oD,_oE,_oF,_){var _=_ow[_oF]=_oD;if(_oF!=(_ox-1|0)){return new F(function(){return _oy(_oE,_oF+1|0,_);});}else{return E(_);}})(_o6,_on,0,_));return new T4(0,E(_o8),E(_os),_ox,_ow);}}else{return E(_oq);}};if(0>_os){return new F(function(){return _ot(0);});}else{return new F(function(){return _ot(_os+1|0);});}},_oG=function(_oH){var _oI=B(A1(_oH,_));return E(_oI);},_oJ=new T(function(){return B(_oG(_or));}),_oK="outline",_oL="polygon",_oM=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_oN=new T(function(){return B(err(_oM));}),_oO=new T(function(){return eval("__strict(drawObjects)");}),_oP=new T(function(){return eval("__strict(draw)");}),_oQ=function(_oR,_oS){var _oT=jsShowI(_oR);return new F(function(){return _q(fromJSStr(_oT),_oS);});},_oU=function(_oV,_oW,_oX){if(_oW>=0){return new F(function(){return _oQ(_oW,_oX);});}else{if(_oV<=6){return new F(function(){return _oQ(_oW,_oX);});}else{return new T2(1,_Z,new T(function(){var _oY=jsShowI(_oW);return B(_q(fromJSStr(_oY),new T2(1,_Y,_oX)));}));}}},_oZ=new T(function(){return B(unCStr(")"));}),_p0=function(_p1,_p2){var _p3=new T(function(){var _p4=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_q(B(_oU(0,_p1,_z)),_oZ));})));},1);return B(_q(B(_oU(0,_p2,_z)),_p4));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_p3)));});},_p5=new T2(1,_8f,_z),_p6=function(_p7){return E(_p7);},_p8=function(_p9){return E(_p9);},_pa=function(_pb,_pc){return E(_pc);},_pd=function(_pe,_pf){return E(_pe);},_pg=function(_ph){return E(_ph);},_pi=new T2(0,_pg,_pd),_pj=function(_pk,_pl){return E(_pk);},_pm=new T5(0,_pi,_p8,_p6,_pa,_pj),_pn="flipped2",_po="flipped1",_pp="c1y",_pq="c1x",_pr="w2z",_ps="w2y",_pt="w2x",_pu="w1z",_pv="w1y",_pw="w1x",_px="d2z",_py="d2y",_pz="d2x",_pA="d1z",_pB="d1y",_pC="d1x",_pD="c2y",_pE="c2x",_pF=function(_pG,_){var _pH=__get(_pG,E(_pw)),_pI=__get(_pG,E(_pv)),_pJ=__get(_pG,E(_pu)),_pK=__get(_pG,E(_pt)),_pL=__get(_pG,E(_ps)),_pM=__get(_pG,E(_pr)),_pN=__get(_pG,E(_pq)),_pO=__get(_pG,E(_pp)),_pP=__get(_pG,E(_pE)),_pQ=__get(_pG,E(_pD)),_pR=__get(_pG,E(_pC)),_pS=__get(_pG,E(_pB)),_pT=__get(_pG,E(_pA)),_pU=__get(_pG,E(_pz)),_pV=__get(_pG,E(_py)),_pW=__get(_pG,E(_px)),_pX=__get(_pG,E(_po)),_pY=__get(_pG,E(_pn));return {_:0,a:E(new T3(0,E(_pH),E(_pI),E(_pJ))),b:E(new T3(0,E(_pK),E(_pL),E(_pM))),c:E(new T2(0,E(_pN),E(_pO))),d:E(new T2(0,E(_pP),E(_pQ))),e:E(new T3(0,E(_pR),E(_pS),E(_pT))),f:E(new T3(0,E(_pU),E(_pV),E(_pW))),g:E(_pX),h:E(_pY)};},_pZ=function(_q0,_){var _q1=E(_q0);if(!_q1._){return _z;}else{var _q2=B(_pF(E(_q1.a),_)),_q3=B(_pZ(_q1.b,_));return new T2(1,_q2,_q3);}},_q4=function(_q5){var _q6=E(_q5);return (E(_q6.b)-E(_q6.a)|0)+1|0;},_q7=function(_q8,_q9){var _qa=E(_q8),_qb=E(_q9);return (E(_qa.a)>_qb)?false:_qb<=E(_qa.b);},_qc=function(_qd){return new F(function(){return _oU(0,E(_qd),_z);});},_qe=function(_qf,_qg,_qh){return new F(function(){return _oU(E(_qf),E(_qg),_qh);});},_qi=function(_qj,_qk){return new F(function(){return _oU(0,E(_qj),_qk);});},_ql=function(_qm,_qn){return new F(function(){return _2R(_qi,_qm,_qn);});},_qo=new T3(0,_qe,_qc,_ql),_qp=0,_qq=function(_qr,_qs,_qt){return new F(function(){return A1(_qr,new T2(1,_2O,new T(function(){return B(A1(_qs,_qt));})));});},_qu=new T(function(){return B(unCStr("foldr1"));}),_qv=new T(function(){return B(_aR(_qu));}),_qw=function(_qx,_qy){var _qz=E(_qy);if(!_qz._){return E(_qv);}else{var _qA=_qz.a,_qB=E(_qz.b);if(!_qB._){return E(_qA);}else{return new F(function(){return A2(_qx,_qA,new T(function(){return B(_qw(_qx,_qB));}));});}}},_qC=new T(function(){return B(unCStr(" out of range "));}),_qD=new T(function(){return B(unCStr("}.index: Index "));}),_qE=new T(function(){return B(unCStr("Ix{"));}),_qF=new T2(1,_Y,_z),_qG=new T2(1,_Y,_qF),_qH=0,_qI=function(_qJ){return E(E(_qJ).a);},_qK=function(_qL,_qM,_qN,_qO,_qP){var _qQ=new T(function(){var _qR=new T(function(){var _qS=new T(function(){var _qT=new T(function(){var _qU=new T(function(){return B(A3(_qw,_qq,new T2(1,new T(function(){return B(A3(_qI,_qN,_qH,_qO));}),new T2(1,new T(function(){return B(A3(_qI,_qN,_qH,_qP));}),_z)),_qG));});return B(_q(_qC,new T2(1,_Z,new T2(1,_Z,_qU))));});return B(A(_qI,[_qN,_qp,_qM,new T2(1,_Y,_qT)]));});return B(_q(_qD,new T2(1,_Z,_qS)));},1);return B(_q(_qL,_qR));},1);return new F(function(){return err(B(_q(_qE,_qQ)));});},_qV=function(_qW,_qX,_qY,_qZ,_r0){return new F(function(){return _qK(_qW,_qX,_r0,_qY,_qZ);});},_r1=function(_r2,_r3,_r4,_r5){var _r6=E(_r4);return new F(function(){return _qV(_r2,_r3,_r6.a,_r6.b,_r5);});},_r7=function(_r8,_r9,_ra,_rb){return new F(function(){return _r1(_rb,_ra,_r9,_r8);});},_rc=new T(function(){return B(unCStr("Int"));}),_rd=function(_re,_rf){return new F(function(){return _r7(_qo,_rf,_re,_rc);});},_rg=function(_rh,_ri){var _rj=E(_rh),_rk=E(_rj.a),_rl=E(_ri);if(_rk>_rl){return new F(function(){return _rd(_rl,_rj);});}else{if(_rl>E(_rj.b)){return new F(function(){return _rd(_rl,_rj);});}else{return _rl-_rk|0;}}},_rm=function(_rn){var _ro=E(_rn);return new F(function(){return _he(_ro.a,_ro.b);});},_rp=function(_rq){var _rr=E(_rq),_rs=E(_rr.a),_rt=E(_rr.b);return (_rs>_rt)?E(_qp):(_rt-_rs|0)+1|0;},_ru=function(_rv,_rw){return new F(function(){return _iD(_rw,E(_rv).a);});},_rx={_:0,a:_jt,b:_rm,c:_rg,d:_ru,e:_q7,f:_rp,g:_q4},_ry=function(_rz,_rA,_){while(1){var _rB=B((function(_rC,_rD,_){var _rE=E(_rC);if(!_rE._){return new T2(0,_8f,_rD);}else{var _rF=B(A2(_rE.a,_rD,_));_rz=_rE.b;_rA=new T(function(){return E(E(_rF).b);});return __continue;}})(_rz,_rA,_));if(_rB!=__continue){return _rB;}}},_rG=function(_rH){return E(E(_rH).a);},_rI=function(_rJ,_rK){return new T2(1,_rJ,_rK);},_rL=function(_rM){return E(E(_rM).c);},_rN=function(_rO,_rP){var _rQ=E(_rP);return new T2(0,_rQ.a,_rQ.b);},_rR=function(_rS){return E(E(_rS).a);},_rT=function(_rU){return E(E(_rU).f);},_rV=function(_rW,_rX,_rY){var _rZ=E(_rX),_s0=_rZ.a,_s1=_rZ.b,_s2=function(_){var _s3=B(A2(_rT,_rW,_rZ));if(_s3>=0){var _s4=newArr(_s3,_1w),_s5=_s4,_s6=E(_s3);if(!_s6){return new T(function(){return new T4(0,E(_s0),E(_s1),0,_s5);});}else{var _s7=function(_s8,_s9,_){while(1){var _sa=E(_s8);if(!_sa._){return E(_);}else{var _=_s5[_s9]=_sa.a;if(_s9!=(_s6-1|0)){var _sb=_s9+1|0;_s8=_sa.b;_s9=_sb;continue;}else{return E(_);}}}},_=B(_s7(_rY,0,_));return new T(function(){return new T4(0,E(_s0),E(_s1),_s6,_s5);});}}else{return E(_oq);}};return new F(function(){return _oG(_s2);});},_sc=function(_sd){return E(E(_sd).b);},_se=function(_sf,_sg,_sh,_si){var _sj=new T(function(){var _sk=E(_si),_sl=_sk.c-1|0,_sm=new T(function(){return B(A2(_sc,_sg,_z));});if(0<=_sl){var _sn=new T(function(){return B(_rG(_sg));}),_so=function(_sp){var _sq=new T(function(){var _sr=new T(function(){return B(A1(_sh,new T(function(){return E(_sk.d[_sp]);})));});return B(A3(_rR,_sn,_rI,_sr));});return new F(function(){return A3(_rL,_sg,_sq,new T(function(){if(_sp!=_sl){return B(_so(_sp+1|0));}else{return E(_sm);}}));});};return B(_so(0));}else{return E(_sm);}}),_ss=new T(function(){return B(_rN(_sf,_si));});return new F(function(){return A3(_rR,B(_rG(_sg)),function(_st){return new F(function(){return _rV(_sf,_ss,_st);});},_sj);});},_su=function(_sv,_sw,_sx,_sy,_sz,_sA,_sB,_sC,_sD){var _sE=B(_8X(_sv));return new T2(0,new T3(0,E(B(A1(B(A1(_sE,_sw)),_sA))),E(B(A1(B(A1(_sE,_sx)),_sB))),E(B(A1(B(A1(_sE,_sy)),_sC)))),B(A1(B(A1(_sE,_sz)),_sD)));},_sF=function(_sG,_sH,_sI,_sJ,_sK,_sL,_sM,_sN,_sO){var _sP=B(_8Z(_sG));return new T2(0,new T3(0,E(B(A1(B(A1(_sP,_sH)),_sL))),E(B(A1(B(A1(_sP,_sI)),_sM))),E(B(A1(B(A1(_sP,_sJ)),_sN)))),B(A1(B(A1(_sP,_sK)),_sO)));},_sQ=1.0e-2,_sR=function(_sS,_sT,_sU,_sV,_sW,_sX,_sY,_sZ,_t0,_t1,_t2,_t3,_t4,_t5,_t6,_t7,_t8){var _t9=B(_su(_6Y,_sZ,_t0,_t1,_t2,_sQ,_sQ,_sQ,_sQ)),_ta=E(_t9.a),_tb=B(_sF(_6Y,_sV,_sW,_sX,_sY,_ta.a,_ta.b,_ta.c,_t9.b)),_tc=E(_tb.a);return new F(function(){return _ds(_sS,_sT,_sU,_tc.a,_tc.b,_tc.c,_tb.b,_sZ,_t0,_t1,_t2,_t3,_t4,_t5,_t6,_t7,_t8);});},_td=function(_te){var _tf=E(_te),_tg=E(_tf.d),_th=E(_tg.a),_ti=E(_tf.e),_tj=E(_ti.a),_tk=E(_tf.f),_tl=B(_sR(_tf.a,_tf.b,_tf.c,_th.a,_th.b,_th.c,_tg.b,_tj.a,_tj.b,_tj.c,_ti.b,_tk.a,_tk.b,_tk.c,_tf.g,_tf.h,_tf.i));return {_:0,a:E(_tl.a),b:E(_tl.b),c:E(_tl.c),d:E(_tl.d),e:E(_tl.e),f:E(_tl.f),g:E(_tl.g),h:_tl.h,i:_tl.i};},_tm=function(_tn,_to,_tp,_tq,_tr,_ts,_tt,_tu,_tv){var _tw=B(_8V(B(_8T(_tn))));return new F(function(){return A3(_8Z,_tw,new T(function(){return B(_91(_tn,_to,_tp,_tq,_ts,_tt,_tu));}),new T(function(){return B(A3(_8X,_tw,_tr,_tv));}));});},_tx=new T(function(){return B(unCStr("base"));}),_ty=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_tz=new T(function(){return B(unCStr("IOException"));}),_tA=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_tx,_ty,_tz),_tB=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_tA,_z,_z),_tC=function(_tD){return E(_tB);},_tE=function(_tF){var _tG=E(_tF);return new F(function(){return _2o(B(_2m(_tG.a)),_tC,_tG.b);});},_tH=new T(function(){return B(unCStr(": "));}),_tI=new T(function(){return B(unCStr(")"));}),_tJ=new T(function(){return B(unCStr(" ("));}),_tK=new T(function(){return B(unCStr("interrupted"));}),_tL=new T(function(){return B(unCStr("system error"));}),_tM=new T(function(){return B(unCStr("unsatisified constraints"));}),_tN=new T(function(){return B(unCStr("user error"));}),_tO=new T(function(){return B(unCStr("permission denied"));}),_tP=new T(function(){return B(unCStr("illegal operation"));}),_tQ=new T(function(){return B(unCStr("end of file"));}),_tR=new T(function(){return B(unCStr("resource exhausted"));}),_tS=new T(function(){return B(unCStr("resource busy"));}),_tT=new T(function(){return B(unCStr("does not exist"));}),_tU=new T(function(){return B(unCStr("already exists"));}),_tV=new T(function(){return B(unCStr("resource vanished"));}),_tW=new T(function(){return B(unCStr("timeout"));}),_tX=new T(function(){return B(unCStr("unsupported operation"));}),_tY=new T(function(){return B(unCStr("hardware fault"));}),_tZ=new T(function(){return B(unCStr("inappropriate type"));}),_u0=new T(function(){return B(unCStr("invalid argument"));}),_u1=new T(function(){return B(unCStr("failed"));}),_u2=new T(function(){return B(unCStr("protocol error"));}),_u3=function(_u4,_u5){switch(E(_u4)){case 0:return new F(function(){return _q(_tU,_u5);});break;case 1:return new F(function(){return _q(_tT,_u5);});break;case 2:return new F(function(){return _q(_tS,_u5);});break;case 3:return new F(function(){return _q(_tR,_u5);});break;case 4:return new F(function(){return _q(_tQ,_u5);});break;case 5:return new F(function(){return _q(_tP,_u5);});break;case 6:return new F(function(){return _q(_tO,_u5);});break;case 7:return new F(function(){return _q(_tN,_u5);});break;case 8:return new F(function(){return _q(_tM,_u5);});break;case 9:return new F(function(){return _q(_tL,_u5);});break;case 10:return new F(function(){return _q(_u2,_u5);});break;case 11:return new F(function(){return _q(_u1,_u5);});break;case 12:return new F(function(){return _q(_u0,_u5);});break;case 13:return new F(function(){return _q(_tZ,_u5);});break;case 14:return new F(function(){return _q(_tY,_u5);});break;case 15:return new F(function(){return _q(_tX,_u5);});break;case 16:return new F(function(){return _q(_tW,_u5);});break;case 17:return new F(function(){return _q(_tV,_u5);});break;default:return new F(function(){return _q(_tK,_u5);});}},_u6=new T(function(){return B(unCStr("}"));}),_u7=new T(function(){return B(unCStr("{handle: "));}),_u8=function(_u9,_ua,_ub,_uc,_ud,_ue){var _uf=new T(function(){var _ug=new T(function(){var _uh=new T(function(){var _ui=E(_uc);if(!_ui._){return E(_ue);}else{var _uj=new T(function(){return B(_q(_ui,new T(function(){return B(_q(_tI,_ue));},1)));},1);return B(_q(_tJ,_uj));}},1);return B(_u3(_ua,_uh));}),_uk=E(_ub);if(!_uk._){return E(_ug);}else{return B(_q(_uk,new T(function(){return B(_q(_tH,_ug));},1)));}}),_ul=E(_ud);if(!_ul._){var _um=E(_u9);if(!_um._){return E(_uf);}else{var _un=E(_um.a);if(!_un._){var _uo=new T(function(){var _up=new T(function(){return B(_q(_u6,new T(function(){return B(_q(_tH,_uf));},1)));},1);return B(_q(_un.a,_up));},1);return new F(function(){return _q(_u7,_uo);});}else{var _uq=new T(function(){var _ur=new T(function(){return B(_q(_u6,new T(function(){return B(_q(_tH,_uf));},1)));},1);return B(_q(_un.a,_ur));},1);return new F(function(){return _q(_u7,_uq);});}}}else{return new F(function(){return _q(_ul.a,new T(function(){return B(_q(_tH,_uf));},1));});}},_us=function(_ut){var _uu=E(_ut);return new F(function(){return _u8(_uu.a,_uu.b,_uu.c,_uu.d,_uu.f,_z);});},_uv=function(_uw,_ux,_uy){var _uz=E(_ux);return new F(function(){return _u8(_uz.a,_uz.b,_uz.c,_uz.d,_uz.f,_uy);});},_uA=function(_uB,_uC){var _uD=E(_uB);return new F(function(){return _u8(_uD.a,_uD.b,_uD.c,_uD.d,_uD.f,_uC);});},_uE=function(_uF,_uG){return new F(function(){return _2R(_uA,_uF,_uG);});},_uH=new T3(0,_uv,_us,_uE),_uI=new T(function(){return new T5(0,_tC,_uH,_uJ,_tE,_us);}),_uJ=function(_uK){return new T2(0,_uI,_uK);},_uL=__Z,_uM=7,_uN=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:85:3-9"));}),_uO=new T6(0,_uL,_uM,_z,_uN,_uL,_uL),_uP=new T(function(){return B(_uJ(_uO));}),_uQ=function(_){return new F(function(){return die(_uP);});},_uR=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:84:3-9"));}),_uS=new T6(0,_uL,_uM,_z,_uR,_uL,_uL),_uT=new T(function(){return B(_uJ(_uS));}),_uU=function(_){return new F(function(){return die(_uT);});},_uV=function(_uW,_){return new T2(0,_z,_uW);},_uX=1,_uY=new T(function(){return B(unCStr(")"));}),_uZ=function(_v0,_v1){var _v2=new T(function(){var _v3=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_q(B(_oU(0,_v0,_z)),_uY));})));},1);return B(_q(B(_oU(0,_v1,_z)),_v3));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_v2)));});},_v4=function(_v5,_v6){var _v7=new T(function(){var _v8=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_q(B(_oU(0,_v6,_z)),_uY));})));},1);return B(_q(B(_oU(0,_v5,_z)),_v8));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_v7)));});},_v9=0.6,_va=function(_vb){var _vc=E(_vb);if(!_vc._){return E(_uV);}else{var _vd=new T(function(){return B(_va(_vc.b));}),_ve=function(_vf){var _vg=E(_vf);if(!_vg._){return E(_vd);}else{var _vh=_vg.a,_vi=new T(function(){return B(_ve(_vg.b));}),_vj=new T(function(){return 0.1*E(E(_vh).e)/1.0e-2;}),_vk=new T(function(){var _vl=E(_vh);if(_vl.a!=_vl.b){return E(_uX);}else{return E(_v9);}}),_vm=function(_vn,_){var _vo=E(_vn),_vp=_vo.c,_vq=_vo.d,_vr=E(_vo.a),_vs=E(_vo.b),_vt=E(_vh),_vu=_vt.a,_vv=_vt.b,_vw=E(_vt.c),_vx=_vw.b,_vy=E(_vw.a),_vz=_vy.a,_vA=_vy.b,_vB=_vy.c,_vC=E(_vt.d),_vD=_vC.b,_vE=E(_vC.a),_vF=_vE.a,_vG=_vE.b,_vH=_vE.c;if(_vr>_vu){return new F(function(){return _uU(_);});}else{if(_vu>_vs){return new F(function(){return _uU(_);});}else{if(_vr>_vv){return new F(function(){return _uQ(_);});}else{if(_vv>_vs){return new F(function(){return _uQ(_);});}else{var _vI=_vu-_vr|0;if(0>_vI){return new F(function(){return _uZ(_vp,_vI);});}else{if(_vI>=_vp){return new F(function(){return _uZ(_vp,_vI);});}else{var _vJ=E(_vq[_vI]),_vK=E(_vJ.c),_vL=_vK.b,_vM=E(_vK.a),_vN=_vM.a,_vO=_vM.b,_vP=_vM.c,_vQ=E(_vJ.e),_vR=E(_vQ.a),_vS=B(_su(_6Y,_vz,_vA,_vB,_vx,_vN,_vO,_vP,_vL)),_vT=E(_vS.a),_vU=B(_su(_6Y,_vT.a,_vT.b,_vT.c,_vS.b,_vz,_vA,_vB,_vx)),_vV=E(_vU.a),_vW=_vv-_vr|0;if(0>_vW){return new F(function(){return _v4(_vW,_vp);});}else{if(_vW>=_vp){return new F(function(){return _v4(_vW,_vp);});}else{var _vX=E(_vq[_vW]),_vY=E(_vX.c),_vZ=_vY.b,_w0=E(_vY.a),_w1=_w0.a,_w2=_w0.b,_w3=_w0.c,_w4=E(_vX.e),_w5=E(_w4.a),_w6=B(_su(_6Y,_vF,_vG,_vH,_vD,_w1,_w2,_w3,_vZ)),_w7=E(_w6.a),_w8=B(_su(_6Y,_w7.a,_w7.b,_w7.c,_w6.b,_vF,_vG,_vH,_vD)),_w9=E(_w8.a),_wa=E(_vV.a)+E(_vV.b)+E(_vV.c)+E(_vU.b)+E(_w9.a)+E(_w9.b)+E(_w9.c)+E(_w8.b);if(!_wa){var _wb=B(A2(_vi,_vo,_));return new T2(0,new T2(1,_8f,new T(function(){return E(E(_wb).a);})),new T(function(){return E(E(_wb).b);}));}else{var _wc=new T(function(){return  -((B(_tm(_7u,_vR.a,_vR.b,_vR.c,_vQ.b,_vz,_vA,_vB,_vx))-B(_tm(_7u,_w5.a,_w5.b,_w5.c,_w4.b,_vF,_vG,_vH,_vD))-E(_vj))/_wa);}),_wd=function(_we,_wf,_wg,_wh,_){var _wi=new T(function(){var _wj=function(_wk,_wl,_wm,_wn,_wo){if(_wk>_vv){return E(_wo);}else{if(_vv>_wl){return E(_wo);}else{var _wp=function(_){var _wq=newArr(_wm,_1w),_wr=_wq,_ws=function(_wt,_){while(1){if(_wt!=_wm){var _=_wr[_wt]=_wn[_wt],_wu=_wt+1|0;_wt=_wu;continue;}else{return E(_);}}},_=B(_ws(0,_)),_wv=_vv-_wk|0;if(0>_wv){return new F(function(){return _v4(_wv,_wm);});}else{if(_wv>=_wm){return new F(function(){return _v4(_wv,_wm);});}else{var _=_wr[_wv]=new T(function(){var _ww=E(_wn[_wv]),_wx=E(_ww.e),_wy=E(_wx.a),_wz=B(_su(_6Y,_w1,_w2,_w3,_vZ,_vF,_vG,_vH,_vD)),_wA=E(_wz.a),_wB=E(_wc)*E(_vk),_wC=B(_su(_6Y,_wA.a,_wA.b,_wA.c,_wz.b,_wB,_wB,_wB,_wB)),_wD=E(_wC.a),_wE=B(_sF(_6Y,_wy.a,_wy.b,_wy.c,_wx.b, -E(_wD.a), -E(_wD.b), -E(_wD.c), -E(_wC.b)));return {_:0,a:E(_ww.a),b:E(_ww.b),c:E(_ww.c),d:E(_ww.d),e:E(new T2(0,E(_wE.a),E(_wE.b))),f:E(_ww.f),g:E(_ww.g),h:_ww.h,i:_ww.i};});return new T4(0,E(_wk),E(_wl),_wm,_wr);}}};return new F(function(){return _oG(_wp);});}}};if(_we>_vu){return B(_wj(_we,_wf,_wg,_wh,new T4(0,E(_we),E(_wf),_wg,_wh)));}else{if(_vu>_wf){return B(_wj(_we,_wf,_wg,_wh,new T4(0,E(_we),E(_wf),_wg,_wh)));}else{var _wF=function(_){var _wG=newArr(_wg,_1w),_wH=_wG,_wI=function(_wJ,_){while(1){if(_wJ!=_wg){var _=_wH[_wJ]=_wh[_wJ],_wK=_wJ+1|0;_wJ=_wK;continue;}else{return E(_);}}},_=B(_wI(0,_)),_wL=_vu-_we|0;if(0>_wL){return new F(function(){return _uZ(_wg,_wL);});}else{if(_wL>=_wg){return new F(function(){return _uZ(_wg,_wL);});}else{var _=_wH[_wL]=new T(function(){var _wM=E(_wh[_wL]),_wN=E(_wM.e),_wO=E(_wN.a),_wP=B(_su(_6Y,_vN,_vO,_vP,_vL,_vz,_vA,_vB,_vx)),_wQ=E(_wP.a),_wR=E(_wc)*E(_vk),_wS=B(_su(_6Y,_wQ.a,_wQ.b,_wQ.c,_wP.b,_wR,_wR,_wR,_wR)),_wT=E(_wS.a),_wU=B(_sF(_6Y,_wO.a,_wO.b,_wO.c,_wN.b,_wT.a,_wT.b,_wT.c,_wS.b));return {_:0,a:E(_wM.a),b:E(_wM.b),c:E(_wM.c),d:E(_wM.d),e:E(new T2(0,E(_wU.a),E(_wU.b))),f:E(_wM.f),g:E(_wM.g),h:_wM.h,i:_wM.i};});return new T4(0,E(_we),E(_wf),_wg,_wH);}}},_wV=B(_oG(_wF));return B(_wj(E(_wV.a),E(_wV.b),_wV.c,_wV.d,_wV));}}});return new T2(0,_8f,_wi);};if(!E(_vt.f)){var _wW=B(_wd(_vr,_vs,_vp,_vq,_)),_wX=B(A2(_vi,new T(function(){return E(E(_wW).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_wW).a);}),new T(function(){return E(E(_wX).a);})),new T(function(){return E(E(_wX).b);}));}else{if(E(_wc)<0){var _wY=B(A2(_vi,_vo,_));return new T2(0,new T2(1,_8f,new T(function(){return E(E(_wY).a);})),new T(function(){return E(E(_wY).b);}));}else{var _wZ=B(_wd(_vr,_vs,_vp,_vq,_)),_x0=B(A2(_vi,new T(function(){return E(E(_wZ).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_wZ).a);}),new T(function(){return E(E(_x0).a);})),new T(function(){return E(E(_x0).b);}));}}}}}}}}}}}};return E(_vm);}};return new F(function(){return _ve(_vc.a);});}},_x1=function(_,_x2){var _x3=new T(function(){return B(_va(E(_x2).a));}),_x4=function(_x5){var _x6=E(_x5);return (_x6==1)?E(new T2(1,_x3,_z)):new T2(1,_x3,new T(function(){return B(_x4(_x6-1|0));}));},_x7=B(_ry(B(_x4(5)),new T(function(){return E(E(_x2).b);}),_)),_x8=new T(function(){return B(_se(_rx,_pm,_td,new T(function(){return E(E(_x7).b);})));});return new T2(0,_8f,_x8);},_x9=function(_xa,_xb,_xc,_xd,_xe){var _xf=B(_8V(B(_8T(_xa))));return new F(function(){return A3(_8Z,_xf,new T(function(){return B(A3(_8X,_xf,_xb,_xd));}),new T(function(){return B(A3(_8X,_xf,_xc,_xe));}));});},_xg=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:55:7-13"));}),_xh=new T6(0,_uL,_uM,_z,_xg,_uL,_uL),_xi=new T(function(){return B(_uJ(_xh));}),_xj=function(_){return new F(function(){return die(_xi);});},_xk=function(_xl,_xm,_xn,_xo){var _xp=new T(function(){return B(_8V(new T(function(){return B(_8T(_xl));})));}),_xq=B(A2(_9E,_xp,_18));return new F(function(){return _9f(_xl,_xq,B(A2(_9E,_xp,_J)),_xq);});},_xr=false,_xs=true,_xt=function(_xu){var _xv=E(_xu),_xw=_xv.b,_xx=E(_xv.d),_xy=E(_xv.e),_xz=E(_xy.a),_xA=E(_xv.g),_xB=B(A1(_xw,_xx.a)),_xC=B(_aa(_7u,_xB.a,_xB.b,_xB.c,_xA.a,_xA.b,_xA.c));return {_:0,a:E(_xv.a),b:E(_xw),c:E(_xv.c),d:E(_xx),e:E(new T2(0,E(new T3(0,E(_xz.a)+E(_xC.a)*1.0e-2,E(_xz.b)+E(_xC.b)*1.0e-2,E(_xz.c)+E(_xC.c)*1.0e-2)),E(_xy.b))),f:E(_xv.f),g:E(_xA),h:_xv.h,i:_xv.i};},_xD=new T(function(){return eval("collide");}),_xE=function(_xF){var _xG=E(_xF);if(!_xG._){return __Z;}else{return new F(function(){return _q(_xG.a,new T(function(){return B(_xE(_xG.b));},1));});}},_xH=0,_xI=new T3(0,E(_xH),E(_xH),E(_xH)),_xJ=new T2(0,E(_xI),E(_xH)),_xK=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:54:7-13"));}),_xL=new T6(0,_uL,_uM,_z,_xK,_uL,_uL),_xM=new T(function(){return B(_uJ(_xL));}),_xN=function(_xO,_){var _xP=B(_se(_rx,_pm,_xt,_xO)),_xQ=E(_xP.a),_xR=E(_xP.b);if(_xQ<=_xR){var _xS=function(_xT,_xU,_){if(_xT<=_xR){var _xV=E(_xU),_xW=function(_xX,_xY,_xZ,_y0,_y1,_){if(_xY>_xT){return new F(function(){return die(_xM);});}else{if(_xT>_xZ){return new F(function(){return die(_xM);});}else{if(_xY>_xX){return new F(function(){return _xj(_);});}else{if(_xX>_xZ){return new F(function(){return _xj(_);});}else{var _y2=_xT-_xY|0;if(0>_y2){return new F(function(){return _v4(_y2,_y0);});}else{if(_y2>=_y0){return new F(function(){return _v4(_y2,_y0);});}else{var _y3=E(_y1[_y2]),_y4=_xX-_xY|0;if(0>_y4){return new F(function(){return _v4(_y4,_y0);});}else{if(_y4>=_y0){return new F(function(){return _v4(_y4,_y0);});}else{var _y5=E(_y1[_y4]),_y6=__app2(E(_xD),B(_8g(new T2(1,new T2(0,_oL,_y3.h),new T2(1,new T2(0,_oK,_y3.i),_z)))),B(_8g(new T2(1,new T2(0,_oL,_y5.h),new T2(1,new T2(0,_oK,_y5.i),_z))))),_y7=__arr2lst(0,_y6),_y8=B(_pZ(_y7,_));if(_xX!=_xR){var _y9=B(_xW(_xX+1|0,_xY,_xZ,_y0,_y1,_)),_ya=new T(function(){var _yb=new T(function(){return _xT!=_xX;}),_yc=function(_yd){var _ye=E(_yd);if(!_ye._){return __Z;}else{var _yf=_ye.b,_yg=E(_ye.a),_yh=E(_yg.b),_yi=E(_yg.a),_yj=E(_yi.a),_yk=E(_yi.b),_yl=E(_yi.c),_ym=E(_yh.a),_yn=E(_yh.b),_yo=E(_yh.c),_yp=E(_yg.c),_yq=_yp.a,_yr=_yp.b,_ys=E(_yg.e),_yt=E(_yg.d),_yu=_yt.a,_yv=_yt.b,_yw=E(_yg.f),_yx=new T(function(){var _yy=B(_9f(_7u,_yw.a,_yw.b,_yw.c)),_yz=Math.sqrt(B(_x9(_7u,_yu,_yv,_yu,_yv)));return new T3(0,_yz*E(_yy.a),_yz*E(_yy.b),_yz*E(_yy.c));}),_yA=new T(function(){var _yB=B(_9f(_7u,_ys.a,_ys.b,_ys.c)),_yC=Math.sqrt(B(_x9(_7u,_yq,_yr,_yq,_yr)));return new T3(0,_yC*E(_yB.a),_yC*E(_yB.b),_yC*E(_yB.c));}),_yD=new T(function(){var _yE=B(_xk(_7u,_ym,_yn,_yo));return new T3(0,E(_yE.a),E(_yE.b),E(_yE.c));}),_yF=new T(function(){var _yG=B(_xk(_7u,_yj,_yk,_yl));return new T3(0,E(_yG.a),E(_yG.b),E(_yG.c));}),_yH=_ym+ -_yj,_yI=_yn+ -_yk,_yJ=_yo+ -_yl,_yK=new T(function(){return Math.sqrt(B(_91(_7u,_yH,_yI,_yJ,_yH,_yI,_yJ)));}),_yL=new T(function(){var _yM=1/E(_yK);return new T3(0,_yH*_yM,_yI*_yM,_yJ*_yM);}),_yN=new T(function(){if(!E(_yg.g)){return E(_yL);}else{var _yO=E(_yL);return new T3(0,-1*E(_yO.a),-1*E(_yO.b),-1*E(_yO.c));}}),_yP=new T(function(){if(!E(_yg.h)){return E(_yL);}else{var _yQ=E(_yL);return new T3(0,-1*E(_yQ.a),-1*E(_yQ.b),-1*E(_yQ.c));}});return (!E(_yb))?new T2(1,new T(function(){var _yR=E(_yN),_yS=E(_yR.b),_yT=E(_yR.c),_yU=E(_yR.a),_yV=E(_yF),_yW=E(_yV.c),_yX=E(_yV.b),_yY=E(_yV.a),_yZ=E(_yA),_z0=E(_yZ.c),_z1=E(_yZ.b),_z2=E(_yZ.a),_z3=_yS*_yW-_yX*_yT,_z4=_yT*_yY-_yW*_yU,_z5=_yU*_yX-_yY*_yS,_z6=B(_91(_7u,_z4*_z0-_z1*_z5,_z5*_z2-_z0*_z3,_z3*_z1-_z2*_z4,_yY,_yX,_yW));return new T6(0,_xT,_xX,E(new T2(0,E(new T3(0,E(_z3),E(_z4),E(_z5))),E(_z6))),E(_xJ),_yK,_xr);}),new T2(1,new T(function(){var _z7=E(_yP),_z8=E(_z7.b),_z9=E(_z7.c),_za=E(_z7.a),_zb=E(_yD),_zc=E(_zb.c),_zd=E(_zb.b),_ze=E(_zb.a),_zf=E(_yx),_zg=E(_zf.c),_zh=E(_zf.b),_zi=E(_zf.a),_zj=_z8*_zc-_zd*_z9,_zk=_z9*_ze-_zc*_za,_zl=_za*_zd-_ze*_z8,_zm=B(_91(_7u,_zk*_zg-_zh*_zl,_zl*_zi-_zg*_zj,_zj*_zh-_zi*_zk,_ze,_zd,_zc));return new T6(0,_xT,_xX,E(_xJ),E(new T2(0,E(new T3(0,E(_zj),E(_zk),E(_zl))),E(_zm))),_yK,_xr);}),new T(function(){return B(_yc(_yf));}))):new T2(1,new T(function(){var _zn=E(_yN),_zo=E(_zn.b),_zp=E(_zn.c),_zq=E(_zn.a),_zr=E(_yF),_zs=_zr.a,_zt=_zr.b,_zu=_zr.c,_zv=B(_aa(_7u,_zq,_zo,_zp,_zs,_zt,_zu)),_zw=E(_yA),_zx=E(_zw.c),_zy=E(_zw.b),_zz=E(_zw.a),_zA=B(_91(_7u,_zo*_zx-_zy*_zp,_zp*_zz-_zx*_zq,_zq*_zy-_zz*_zo,_zs,_zt,_zu)),_zB=E(_yP),_zC=E(_zB.b),_zD=E(_zB.c),_zE=E(_zB.a),_zF=E(_yD),_zG=_zF.a,_zH=_zF.b,_zI=_zF.c,_zJ=B(_aa(_7u,_zE,_zC,_zD,_zG,_zH,_zI)),_zK=E(_yx),_zL=E(_zK.c),_zM=E(_zK.b),_zN=E(_zK.a),_zO=B(_91(_7u,_zC*_zL-_zM*_zD,_zD*_zN-_zL*_zE,_zE*_zM-_zN*_zC,_zG,_zH,_zI));return new T6(0,_xT,_xX,E(new T2(0,E(new T3(0,E(_zv.a),E(_zv.b),E(_zv.c))),E(_zA))),E(new T2(0,E(new T3(0,E(_zJ.a),E(_zJ.b),E(_zJ.c))),E(_zO))),_yK,_xs);}),new T(function(){return B(_yc(_yf));}));}};return B(_yc(_y8));});return new T2(0,new T2(1,_ya,new T(function(){return E(E(_y9).a);})),new T(function(){return E(E(_y9).b);}));}else{var _zP=new T(function(){var _zQ=new T(function(){return _xT!=_xX;}),_zR=function(_zS){var _zT=E(_zS);if(!_zT._){return __Z;}else{var _zU=_zT.b,_zV=E(_zT.a),_zW=E(_zV.b),_zX=E(_zV.a),_zY=E(_zX.a),_zZ=E(_zX.b),_A0=E(_zX.c),_A1=E(_zW.a),_A2=E(_zW.b),_A3=E(_zW.c),_A4=E(_zV.c),_A5=_A4.a,_A6=_A4.b,_A7=E(_zV.e),_A8=E(_zV.d),_A9=_A8.a,_Aa=_A8.b,_Ab=E(_zV.f),_Ac=new T(function(){var _Ad=B(_9f(_7u,_Ab.a,_Ab.b,_Ab.c)),_Ae=Math.sqrt(B(_x9(_7u,_A9,_Aa,_A9,_Aa)));return new T3(0,_Ae*E(_Ad.a),_Ae*E(_Ad.b),_Ae*E(_Ad.c));}),_Af=new T(function(){var _Ag=B(_9f(_7u,_A7.a,_A7.b,_A7.c)),_Ah=Math.sqrt(B(_x9(_7u,_A5,_A6,_A5,_A6)));return new T3(0,_Ah*E(_Ag.a),_Ah*E(_Ag.b),_Ah*E(_Ag.c));}),_Ai=new T(function(){var _Aj=B(_xk(_7u,_A1,_A2,_A3));return new T3(0,E(_Aj.a),E(_Aj.b),E(_Aj.c));}),_Ak=new T(function(){var _Al=B(_xk(_7u,_zY,_zZ,_A0));return new T3(0,E(_Al.a),E(_Al.b),E(_Al.c));}),_Am=_A1+ -_zY,_An=_A2+ -_zZ,_Ao=_A3+ -_A0,_Ap=new T(function(){return Math.sqrt(B(_91(_7u,_Am,_An,_Ao,_Am,_An,_Ao)));}),_Aq=new T(function(){var _Ar=1/E(_Ap);return new T3(0,_Am*_Ar,_An*_Ar,_Ao*_Ar);}),_As=new T(function(){if(!E(_zV.g)){return E(_Aq);}else{var _At=E(_Aq);return new T3(0,-1*E(_At.a),-1*E(_At.b),-1*E(_At.c));}}),_Au=new T(function(){if(!E(_zV.h)){return E(_Aq);}else{var _Av=E(_Aq);return new T3(0,-1*E(_Av.a),-1*E(_Av.b),-1*E(_Av.c));}});return (!E(_zQ))?new T2(1,new T(function(){var _Aw=E(_As),_Ax=E(_Aw.b),_Ay=E(_Aw.c),_Az=E(_Aw.a),_AA=E(_Ak),_AB=E(_AA.c),_AC=E(_AA.b),_AD=E(_AA.a),_AE=E(_Af),_AF=E(_AE.c),_AG=E(_AE.b),_AH=E(_AE.a),_AI=_Ax*_AB-_AC*_Ay,_AJ=_Ay*_AD-_AB*_Az,_AK=_Az*_AC-_AD*_Ax,_AL=B(_91(_7u,_AJ*_AF-_AG*_AK,_AK*_AH-_AF*_AI,_AI*_AG-_AH*_AJ,_AD,_AC,_AB));return new T6(0,_xT,_xX,E(new T2(0,E(new T3(0,E(_AI),E(_AJ),E(_AK))),E(_AL))),E(_xJ),_Ap,_xr);}),new T2(1,new T(function(){var _AM=E(_Au),_AN=E(_AM.b),_AO=E(_AM.c),_AP=E(_AM.a),_AQ=E(_Ai),_AR=E(_AQ.c),_AS=E(_AQ.b),_AT=E(_AQ.a),_AU=E(_Ac),_AV=E(_AU.c),_AW=E(_AU.b),_AX=E(_AU.a),_AY=_AN*_AR-_AS*_AO,_AZ=_AO*_AT-_AR*_AP,_B0=_AP*_AS-_AT*_AN,_B1=B(_91(_7u,_AZ*_AV-_AW*_B0,_B0*_AX-_AV*_AY,_AY*_AW-_AX*_AZ,_AT,_AS,_AR));return new T6(0,_xT,_xX,E(_xJ),E(new T2(0,E(new T3(0,E(_AY),E(_AZ),E(_B0))),E(_B1))),_Ap,_xr);}),new T(function(){return B(_zR(_zU));}))):new T2(1,new T(function(){var _B2=E(_As),_B3=E(_B2.b),_B4=E(_B2.c),_B5=E(_B2.a),_B6=E(_Ak),_B7=_B6.a,_B8=_B6.b,_B9=_B6.c,_Ba=B(_aa(_7u,_B5,_B3,_B4,_B7,_B8,_B9)),_Bb=E(_Af),_Bc=E(_Bb.c),_Bd=E(_Bb.b),_Be=E(_Bb.a),_Bf=B(_91(_7u,_B3*_Bc-_Bd*_B4,_B4*_Be-_Bc*_B5,_B5*_Bd-_Be*_B3,_B7,_B8,_B9)),_Bg=E(_Au),_Bh=E(_Bg.b),_Bi=E(_Bg.c),_Bj=E(_Bg.a),_Bk=E(_Ai),_Bl=_Bk.a,_Bm=_Bk.b,_Bn=_Bk.c,_Bo=B(_aa(_7u,_Bj,_Bh,_Bi,_Bl,_Bm,_Bn)),_Bp=E(_Ac),_Bq=E(_Bp.c),_Br=E(_Bp.b),_Bs=E(_Bp.a),_Bt=B(_91(_7u,_Bh*_Bq-_Br*_Bi,_Bi*_Bs-_Bq*_Bj,_Bj*_Br-_Bs*_Bh,_Bl,_Bm,_Bn));return new T6(0,_xT,_xX,E(new T2(0,E(new T3(0,E(_Ba.a),E(_Ba.b),E(_Ba.c))),E(_Bf))),E(new T2(0,E(new T3(0,E(_Bo.a),E(_Bo.b),E(_Bo.c))),E(_Bt))),_Ap,_xs);}),new T(function(){return B(_zR(_zU));}));}};return B(_zR(_y8));});return new T2(0,new T2(1,_zP,_z),new T4(0,E(_xY),E(_xZ),_y0,_y1));}}}}}}}}}},_Bu=B(_xW(_xT,E(_xV.a),E(_xV.b),_xV.c,_xV.d,_));if(_xT!=_xR){var _Bv=B(_xS(_xT+1|0,new T(function(){return E(E(_Bu).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_xE(E(_Bu).a));}),new T(function(){return E(E(_Bv).a);})),new T(function(){return E(E(_Bv).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_xE(E(_Bu).a));}),_z),new T(function(){return E(E(_Bu).b);}));}}else{if(_xT!=_xR){var _Bw=B(_xS(_xT+1|0,_xU,_));return new T2(0,new T2(1,_z,new T(function(){return E(E(_Bw).a);})),new T(function(){return E(E(_Bw).b);}));}else{return new T2(0,new T2(1,_z,_z),_xU);}}},_Bx=function(_By,_Bz,_BA,_BB,_BC,_){if(_By<=_xR){var _BD=function(_BE,_BF,_BG,_BH,_BI,_){if(_BF>_By){return new F(function(){return die(_xM);});}else{if(_By>_BG){return new F(function(){return die(_xM);});}else{if(_BF>_BE){return new F(function(){return _xj(_);});}else{if(_BE>_BG){return new F(function(){return _xj(_);});}else{var _BJ=_By-_BF|0;if(0>_BJ){return new F(function(){return _v4(_BJ,_BH);});}else{if(_BJ>=_BH){return new F(function(){return _v4(_BJ,_BH);});}else{var _BK=E(_BI[_BJ]),_BL=_BE-_BF|0;if(0>_BL){return new F(function(){return _v4(_BL,_BH);});}else{if(_BL>=_BH){return new F(function(){return _v4(_BL,_BH);});}else{var _BM=E(_BI[_BL]),_BN=__app2(E(_xD),B(_8g(new T2(1,new T2(0,_oL,_BK.h),new T2(1,new T2(0,_oK,_BK.i),_z)))),B(_8g(new T2(1,new T2(0,_oL,_BM.h),new T2(1,new T2(0,_oK,_BM.i),_z))))),_BO=__arr2lst(0,_BN),_BP=B(_pZ(_BO,_));if(_BE!=_xR){var _BQ=B(_BD(_BE+1|0,_BF,_BG,_BH,_BI,_)),_BR=new T(function(){var _BS=new T(function(){return _By!=_BE;}),_BT=function(_BU){var _BV=E(_BU);if(!_BV._){return __Z;}else{var _BW=_BV.b,_BX=E(_BV.a),_BY=E(_BX.b),_BZ=E(_BX.a),_C0=E(_BZ.a),_C1=E(_BZ.b),_C2=E(_BZ.c),_C3=E(_BY.a),_C4=E(_BY.b),_C5=E(_BY.c),_C6=E(_BX.c),_C7=_C6.a,_C8=_C6.b,_C9=E(_BX.e),_Ca=E(_BX.d),_Cb=_Ca.a,_Cc=_Ca.b,_Cd=E(_BX.f),_Ce=new T(function(){var _Cf=B(_9f(_7u,_Cd.a,_Cd.b,_Cd.c)),_Cg=Math.sqrt(B(_x9(_7u,_Cb,_Cc,_Cb,_Cc)));return new T3(0,_Cg*E(_Cf.a),_Cg*E(_Cf.b),_Cg*E(_Cf.c));}),_Ch=new T(function(){var _Ci=B(_9f(_7u,_C9.a,_C9.b,_C9.c)),_Cj=Math.sqrt(B(_x9(_7u,_C7,_C8,_C7,_C8)));return new T3(0,_Cj*E(_Ci.a),_Cj*E(_Ci.b),_Cj*E(_Ci.c));}),_Ck=new T(function(){var _Cl=B(_xk(_7u,_C3,_C4,_C5));return new T3(0,E(_Cl.a),E(_Cl.b),E(_Cl.c));}),_Cm=new T(function(){var _Cn=B(_xk(_7u,_C0,_C1,_C2));return new T3(0,E(_Cn.a),E(_Cn.b),E(_Cn.c));}),_Co=_C3+ -_C0,_Cp=_C4+ -_C1,_Cq=_C5+ -_C2,_Cr=new T(function(){return Math.sqrt(B(_91(_7u,_Co,_Cp,_Cq,_Co,_Cp,_Cq)));}),_Cs=new T(function(){var _Ct=1/E(_Cr);return new T3(0,_Co*_Ct,_Cp*_Ct,_Cq*_Ct);}),_Cu=new T(function(){if(!E(_BX.g)){return E(_Cs);}else{var _Cv=E(_Cs);return new T3(0,-1*E(_Cv.a),-1*E(_Cv.b),-1*E(_Cv.c));}}),_Cw=new T(function(){if(!E(_BX.h)){return E(_Cs);}else{var _Cx=E(_Cs);return new T3(0,-1*E(_Cx.a),-1*E(_Cx.b),-1*E(_Cx.c));}});return (!E(_BS))?new T2(1,new T(function(){var _Cy=E(_Cu),_Cz=E(_Cy.b),_CA=E(_Cy.c),_CB=E(_Cy.a),_CC=E(_Cm),_CD=E(_CC.c),_CE=E(_CC.b),_CF=E(_CC.a),_CG=E(_Ch),_CH=E(_CG.c),_CI=E(_CG.b),_CJ=E(_CG.a),_CK=_Cz*_CD-_CE*_CA,_CL=_CA*_CF-_CD*_CB,_CM=_CB*_CE-_CF*_Cz,_CN=B(_91(_7u,_CL*_CH-_CI*_CM,_CM*_CJ-_CH*_CK,_CK*_CI-_CJ*_CL,_CF,_CE,_CD));return new T6(0,_By,_BE,E(new T2(0,E(new T3(0,E(_CK),E(_CL),E(_CM))),E(_CN))),E(_xJ),_Cr,_xr);}),new T2(1,new T(function(){var _CO=E(_Cw),_CP=E(_CO.b),_CQ=E(_CO.c),_CR=E(_CO.a),_CS=E(_Ck),_CT=E(_CS.c),_CU=E(_CS.b),_CV=E(_CS.a),_CW=E(_Ce),_CX=E(_CW.c),_CY=E(_CW.b),_CZ=E(_CW.a),_D0=_CP*_CT-_CU*_CQ,_D1=_CQ*_CV-_CT*_CR,_D2=_CR*_CU-_CV*_CP,_D3=B(_91(_7u,_D1*_CX-_CY*_D2,_D2*_CZ-_CX*_D0,_D0*_CY-_CZ*_D1,_CV,_CU,_CT));return new T6(0,_By,_BE,E(_xJ),E(new T2(0,E(new T3(0,E(_D0),E(_D1),E(_D2))),E(_D3))),_Cr,_xr);}),new T(function(){return B(_BT(_BW));}))):new T2(1,new T(function(){var _D4=E(_Cu),_D5=E(_D4.b),_D6=E(_D4.c),_D7=E(_D4.a),_D8=E(_Cm),_D9=_D8.a,_Da=_D8.b,_Db=_D8.c,_Dc=B(_aa(_7u,_D7,_D5,_D6,_D9,_Da,_Db)),_Dd=E(_Ch),_De=E(_Dd.c),_Df=E(_Dd.b),_Dg=E(_Dd.a),_Dh=B(_91(_7u,_D5*_De-_Df*_D6,_D6*_Dg-_De*_D7,_D7*_Df-_Dg*_D5,_D9,_Da,_Db)),_Di=E(_Cw),_Dj=E(_Di.b),_Dk=E(_Di.c),_Dl=E(_Di.a),_Dm=E(_Ck),_Dn=_Dm.a,_Do=_Dm.b,_Dp=_Dm.c,_Dq=B(_aa(_7u,_Dl,_Dj,_Dk,_Dn,_Do,_Dp)),_Dr=E(_Ce),_Ds=E(_Dr.c),_Dt=E(_Dr.b),_Du=E(_Dr.a),_Dv=B(_91(_7u,_Dj*_Ds-_Dt*_Dk,_Dk*_Du-_Ds*_Dl,_Dl*_Dt-_Du*_Dj,_Dn,_Do,_Dp));return new T6(0,_By,_BE,E(new T2(0,E(new T3(0,E(_Dc.a),E(_Dc.b),E(_Dc.c))),E(_Dh))),E(new T2(0,E(new T3(0,E(_Dq.a),E(_Dq.b),E(_Dq.c))),E(_Dv))),_Cr,_xs);}),new T(function(){return B(_BT(_BW));}));}};return B(_BT(_BP));});return new T2(0,new T2(1,_BR,new T(function(){return E(E(_BQ).a);})),new T(function(){return E(E(_BQ).b);}));}else{var _Dw=new T(function(){var _Dx=new T(function(){return _By!=_BE;}),_Dy=function(_Dz){var _DA=E(_Dz);if(!_DA._){return __Z;}else{var _DB=_DA.b,_DC=E(_DA.a),_DD=E(_DC.b),_DE=E(_DC.a),_DF=E(_DE.a),_DG=E(_DE.b),_DH=E(_DE.c),_DI=E(_DD.a),_DJ=E(_DD.b),_DK=E(_DD.c),_DL=E(_DC.c),_DM=_DL.a,_DN=_DL.b,_DO=E(_DC.e),_DP=E(_DC.d),_DQ=_DP.a,_DR=_DP.b,_DS=E(_DC.f),_DT=new T(function(){var _DU=B(_9f(_7u,_DS.a,_DS.b,_DS.c)),_DV=Math.sqrt(B(_x9(_7u,_DQ,_DR,_DQ,_DR)));return new T3(0,_DV*E(_DU.a),_DV*E(_DU.b),_DV*E(_DU.c));}),_DW=new T(function(){var _DX=B(_9f(_7u,_DO.a,_DO.b,_DO.c)),_DY=Math.sqrt(B(_x9(_7u,_DM,_DN,_DM,_DN)));return new T3(0,_DY*E(_DX.a),_DY*E(_DX.b),_DY*E(_DX.c));}),_DZ=new T(function(){var _E0=B(_xk(_7u,_DI,_DJ,_DK));return new T3(0,E(_E0.a),E(_E0.b),E(_E0.c));}),_E1=new T(function(){var _E2=B(_xk(_7u,_DF,_DG,_DH));return new T3(0,E(_E2.a),E(_E2.b),E(_E2.c));}),_E3=_DI+ -_DF,_E4=_DJ+ -_DG,_E5=_DK+ -_DH,_E6=new T(function(){return Math.sqrt(B(_91(_7u,_E3,_E4,_E5,_E3,_E4,_E5)));}),_E7=new T(function(){var _E8=1/E(_E6);return new T3(0,_E3*_E8,_E4*_E8,_E5*_E8);}),_E9=new T(function(){if(!E(_DC.g)){return E(_E7);}else{var _Ea=E(_E7);return new T3(0,-1*E(_Ea.a),-1*E(_Ea.b),-1*E(_Ea.c));}}),_Eb=new T(function(){if(!E(_DC.h)){return E(_E7);}else{var _Ec=E(_E7);return new T3(0,-1*E(_Ec.a),-1*E(_Ec.b),-1*E(_Ec.c));}});return (!E(_Dx))?new T2(1,new T(function(){var _Ed=E(_E9),_Ee=E(_Ed.b),_Ef=E(_Ed.c),_Eg=E(_Ed.a),_Eh=E(_E1),_Ei=E(_Eh.c),_Ej=E(_Eh.b),_Ek=E(_Eh.a),_El=E(_DW),_Em=E(_El.c),_En=E(_El.b),_Eo=E(_El.a),_Ep=_Ee*_Ei-_Ej*_Ef,_Eq=_Ef*_Ek-_Ei*_Eg,_Er=_Eg*_Ej-_Ek*_Ee,_Es=B(_91(_7u,_Eq*_Em-_En*_Er,_Er*_Eo-_Em*_Ep,_Ep*_En-_Eo*_Eq,_Ek,_Ej,_Ei));return new T6(0,_By,_BE,E(new T2(0,E(new T3(0,E(_Ep),E(_Eq),E(_Er))),E(_Es))),E(_xJ),_E6,_xr);}),new T2(1,new T(function(){var _Et=E(_Eb),_Eu=E(_Et.b),_Ev=E(_Et.c),_Ew=E(_Et.a),_Ex=E(_DZ),_Ey=E(_Ex.c),_Ez=E(_Ex.b),_EA=E(_Ex.a),_EB=E(_DT),_EC=E(_EB.c),_ED=E(_EB.b),_EE=E(_EB.a),_EF=_Eu*_Ey-_Ez*_Ev,_EG=_Ev*_EA-_Ey*_Ew,_EH=_Ew*_Ez-_EA*_Eu,_EI=B(_91(_7u,_EG*_EC-_ED*_EH,_EH*_EE-_EC*_EF,_EF*_ED-_EE*_EG,_EA,_Ez,_Ey));return new T6(0,_By,_BE,E(_xJ),E(new T2(0,E(new T3(0,E(_EF),E(_EG),E(_EH))),E(_EI))),_E6,_xr);}),new T(function(){return B(_Dy(_DB));}))):new T2(1,new T(function(){var _EJ=E(_E9),_EK=E(_EJ.b),_EL=E(_EJ.c),_EM=E(_EJ.a),_EN=E(_E1),_EO=_EN.a,_EP=_EN.b,_EQ=_EN.c,_ER=B(_aa(_7u,_EM,_EK,_EL,_EO,_EP,_EQ)),_ES=E(_DW),_ET=E(_ES.c),_EU=E(_ES.b),_EV=E(_ES.a),_EW=B(_91(_7u,_EK*_ET-_EU*_EL,_EL*_EV-_ET*_EM,_EM*_EU-_EV*_EK,_EO,_EP,_EQ)),_EX=E(_Eb),_EY=E(_EX.b),_EZ=E(_EX.c),_F0=E(_EX.a),_F1=E(_DZ),_F2=_F1.a,_F3=_F1.b,_F4=_F1.c,_F5=B(_aa(_7u,_F0,_EY,_EZ,_F2,_F3,_F4)),_F6=E(_DT),_F7=E(_F6.c),_F8=E(_F6.b),_F9=E(_F6.a),_Fa=B(_91(_7u,_EY*_F7-_F8*_EZ,_EZ*_F9-_F7*_F0,_F0*_F8-_F9*_EY,_F2,_F3,_F4));return new T6(0,_By,_BE,E(new T2(0,E(new T3(0,E(_ER.a),E(_ER.b),E(_ER.c))),E(_EW))),E(new T2(0,E(new T3(0,E(_F5.a),E(_F5.b),E(_F5.c))),E(_Fa))),_E6,_xs);}),new T(function(){return B(_Dy(_DB));}));}};return B(_Dy(_BP));});return new T2(0,new T2(1,_Dw,_z),new T4(0,E(_BF),E(_BG),_BH,_BI));}}}}}}}}}},_Fb=B(_BD(_By,_Bz,_BA,_BB,_BC,_));if(_By!=_xR){var _Fc=B(_xS(_By+1|0,new T(function(){return E(E(_Fb).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_xE(E(_Fb).a));}),new T(function(){return E(E(_Fc).a);})),new T(function(){return E(E(_Fc).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_xE(E(_Fb).a));}),_z),new T(function(){return E(E(_Fb).b);}));}}else{if(_By!=_xR){var _Fd=B(_Bx(_By+1|0,_Bz,_BA,_BB,_BC,_));return new T2(0,new T2(1,_z,new T(function(){return E(E(_Fd).a);})),new T(function(){return E(E(_Fd).b);}));}else{return new T2(0,new T2(1,_z,_z),new T4(0,E(_Bz),E(_BA),_BB,_BC));}}},_Fe=B(_Bx(_xQ,_xQ,_xR,_xP.c,_xP.d,_));return new F(function(){return _x1(_,_Fe);});}else{return new F(function(){return _x1(_,new T2(0,_z,_xP));});}},_Ff=new T(function(){return eval("__strict(passObject)");}),_Fg=new T(function(){return eval("__strict(refresh)");}),_Fh=function(_Fi,_){var _Fj=__app0(E(_Fg)),_Fk=__app0(E(_oP)),_Fl=E(_Fi),_Fm=_Fl.c,_Fn=_Fl.d,_Fo=E(_Fl.a),_Fp=E(_Fl.b);if(_Fo<=_Fp){if(_Fo>_Fp){return E(_oN);}else{if(0>=_Fm){return new F(function(){return _p0(_Fm,0);});}else{var _Fq=E(_Fn[0]),_Fr=E(_Ff),_Fs=__app2(_Fr,_Fo,B(_8g(new T2(1,new T2(0,_oL,_Fq.h),new T2(1,new T2(0,_oK,_Fq.i),_z)))));if(_Fo!=_Fp){var _Ft=function(_Fu,_){if(_Fo>_Fu){return E(_oN);}else{if(_Fu>_Fp){return E(_oN);}else{var _Fv=_Fu-_Fo|0;if(0>_Fv){return new F(function(){return _p0(_Fm,_Fv);});}else{if(_Fv>=_Fm){return new F(function(){return _p0(_Fm,_Fv);});}else{var _Fw=E(_Fn[_Fv]),_Fx=__app2(_Fr,_Fu,B(_8g(new T2(1,new T2(0,_oL,_Fw.h),new T2(1,new T2(0,_oK,_Fw.i),_z)))));if(_Fu!=_Fp){var _Fy=B(_Ft(_Fu+1|0,_));return new T2(1,_8f,_Fy);}else{return _p5;}}}}}},_Fz=B(_Ft(_Fo+1|0,_)),_FA=__app0(E(_oO)),_FB=B(_xN(_Fl,_));return new T(function(){return E(E(_FB).b);});}else{var _FC=__app0(E(_oO)),_FD=B(_xN(_Fl,_));return new T(function(){return E(E(_FD).b);});}}}}else{var _FE=__app0(E(_oO)),_FF=B(_xN(_Fl,_));return new T(function(){return E(E(_FF).b);});}},_FG=function(_FH,_){while(1){var _FI=E(_FH);if(!_FI._){return _8f;}else{var _FJ=_FI.b,_FK=E(_FI.a);switch(_FK._){case 0:var _FL=B(A1(_FK.a,_));_FH=B(_q(_FJ,new T2(1,_FL,_z)));continue;case 1:_FH=B(_q(_FJ,_FK.a));continue;default:_FH=_FJ;continue;}}}},_FM=function(_FN,_FO,_){var _FP=E(_FN);switch(_FP._){case 0:var _FQ=B(A1(_FP.a,_));return new F(function(){return _FG(B(_q(_FO,new T2(1,_FQ,_z))),_);});break;case 1:return new F(function(){return _FG(B(_q(_FO,_FP.a)),_);});break;default:return new F(function(){return _FG(_FO,_);});}},_FR=new T0(2),_FS=function(_FT){return new T0(2);},_FU=function(_FV,_FW,_FX){return function(_){var _FY=E(_FV),_FZ=rMV(_FY),_G0=E(_FZ);if(!_G0._){var _G1=new T(function(){var _G2=new T(function(){return B(A1(_FX,_8f));});return B(_q(_G0.b,new T2(1,new T2(0,_FW,function(_G3){return E(_G2);}),_z)));}),_=wMV(_FY,new T2(0,_G0.a,_G1));return _FR;}else{var _G4=E(_G0.a);if(!_G4._){var _=wMV(_FY,new T2(0,_FW,_z));return new T(function(){return B(A1(_FX,_8f));});}else{var _=wMV(_FY,new T1(1,_G4.b));return new T1(1,new T2(1,new T(function(){return B(A1(_FX,_8f));}),new T2(1,new T(function(){return B(A2(_G4.a,_FW,_FS));}),_z)));}}};},_G5=new T(function(){return E(_ea);}),_G6=new T(function(){return eval("window.requestAnimationFrame");}),_G7=new T1(1,_z),_G8=function(_G9,_Ga){return function(_){var _Gb=E(_G9),_Gc=rMV(_Gb),_Gd=E(_Gc);if(!_Gd._){var _Ge=_Gd.a,_Gf=E(_Gd.b);if(!_Gf._){var _=wMV(_Gb,_G7);return new T(function(){return B(A1(_Ga,_Ge));});}else{var _Gg=E(_Gf.a),_=wMV(_Gb,new T2(0,_Gg.a,_Gf.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Ga,_Ge));}),new T2(1,new T(function(){return B(A1(_Gg.b,_FS));}),_z)));}}else{var _Gh=new T(function(){var _Gi=function(_Gj){var _Gk=new T(function(){return B(A1(_Ga,_Gj));});return function(_Gl){return E(_Gk);};};return B(_q(_Gd.a,new T2(1,_Gi,_z)));}),_=wMV(_Gb,new T1(1,_Gh));return _FR;}};},_Gm=function(_Gn,_Go){return new T1(0,B(_G8(_Gn,_Go)));},_Gp=function(_Gq,_Gr){var _Gs=new T(function(){return new T1(0,B(_FU(_Gq,_8f,_FS)));});return function(_){var _Gt=__createJSFunc(2,function(_Gu,_){var _Gv=B(_FM(_Gs,_z,_));return _G5;}),_Gw=__app1(E(_G6),_Gt);return new T(function(){return B(_Gm(_Gq,_Gr));});};},_Gx=new T1(1,_z),_Gy=function(_Gz,_GA,_){var _GB=function(_){var _GC=nMV(_Gz),_GD=_GC;return new T(function(){var _GE=new T(function(){return B(_GF(_));}),_GG=function(_){var _GH=rMV(_GD),_GI=B(A2(_GA,_GH,_)),_=wMV(_GD,_GI),_GJ=function(_){var _GK=nMV(_Gx);return new T(function(){return new T1(0,B(_Gp(_GK,function(_GL){return E(_GE);})));});};return new T1(0,_GJ);},_GM=new T(function(){return new T1(0,_GG);}),_GF=function(_GN){return E(_GM);};return B(_GF(_));});};return new F(function(){return _FM(new T1(0,_GB),_z,_);});},_GO=function(_){var _GP=__app2(E(_0),E(_2),E(_1p));return new F(function(){return _Gy(_oJ,_Fh,_);});},_GQ=function(_){return new F(function(){return _GO(_);});};
var hasteMain = function() {B(A(_GQ, [0]));};window.onload = hasteMain;