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

var _0=function(_1,_2,_3){return new F(function(){return A1(_1,function(_4){return new F(function(){return A2(_2,_4,_3);});});});},_5=function(_6,_7,_8){var _9=function(_a){var _b=new T(function(){return B(A1(_8,_a));});return new F(function(){return A1(_7,function(_c){return E(_b);});});};return new F(function(){return A1(_6,_9);});},_d=function(_e,_f,_g){var _h=new T(function(){return B(A1(_f,function(_i){return new F(function(){return A1(_g,_i);});}));});return new F(function(){return A1(_e,function(_j){return E(_h);});});},_k=function(_l,_m,_n){var _o=function(_p){var _q=function(_r){return new F(function(){return A1(_n,new T(function(){return B(A1(_p,_r));}));});};return new F(function(){return A1(_m,_q);});};return new F(function(){return A1(_l,_o);});},_s=function(_t,_u){return new F(function(){return A1(_u,_t);});},_v=function(_w,_x,_y){var _z=new T(function(){return B(A1(_y,_w));});return new F(function(){return A1(_x,function(_A){return E(_z);});});},_B=function(_C,_D,_E){var _F=function(_G){return new F(function(){return A1(_E,new T(function(){return B(A1(_C,_G));}));});};return new F(function(){return A1(_D,_F);});},_H=new T2(0,_B,_v),_I=new T5(0,_H,_s,_k,_d,_5),_J=function(_K){return E(E(_K).b);},_L=function(_M,_N){return new F(function(){return A3(_J,_O,_M,function(_P){return E(_N);});});},_Q=function(_R){return new F(function(){return err(_R);});},_O=new T(function(){return new T5(0,_I,_0,_L,_s,_Q);}),_S=0,_T=__Z,_U=function(_V){return new T0(2);},_W=function(_X){var _Y=new T(function(){return B(A1(_X,_U));}),_Z=function(_10){return new T1(1,new T2(1,new T(function(){return B(A1(_10,_S));}),new T2(1,_Y,_T)));};return E(_Z);},_11=function(_12){return E(_12);},_13=new T3(0,_O,_11,_W),_14=function(_15,_16){var _17=E(_15);return (_17._==0)?E(_16):new T2(1,_17.a,new T(function(){return B(_14(_17.b,_16));}));},_18=function(_19,_){while(1){var _1a=E(_19);if(!_1a._){return _S;}else{var _1b=_1a.b,_1c=E(_1a.a);switch(_1c._){case 0:var _1d=B(A1(_1c.a,_));_19=B(_14(_1b,new T2(1,_1d,_T)));continue;case 1:_19=B(_14(_1b,_1c.a));continue;default:_19=_1b;continue;}}}},_1e=function(_1f,_1g,_){var _1h=E(_1f);switch(_1h._){case 0:var _1i=B(A1(_1h.a,_));return new F(function(){return _18(B(_14(_1g,new T2(1,_1i,_T))),_);});break;case 1:return new F(function(){return _18(B(_14(_1g,_1h.a)),_);});break;default:return new F(function(){return _18(_1g,_);});}},_1j=new T(function(){return eval("compile");}),_1k=function(_1l){return E(E(_1l).b);},_1m=function(_1n){return E(E(_1n).a);},_1o=function(_1p,_1q,_1r){var _1s=E(_1r);if(!_1s._){return new F(function(){return A1(_1q,_1s.a);});}else{var _1t=new T(function(){return B(_1k(_1p));}),_1u=new T(function(){return B(_1m(_1p));}),_1v=function(_1w){var _1x=E(_1w);if(!_1x._){return E(_1u);}else{return new F(function(){return A2(_1t,new T(function(){return B(_1o(_1p,_1q,_1x.a));}),new T(function(){return B(_1v(_1x.b));}));});}};return new F(function(){return _1v(_1s.a);});}},_1y=function(_1z){var _1A=E(_1z);if(!_1A._){return __Z;}else{return new F(function(){return _14(_1A.a,new T(function(){return B(_1y(_1A.b));},1));});}},_1B=function(_1C){return new F(function(){return _1y(_1C);});},_1D=new T3(0,_T,_14,_1B),_1E=new T(function(){return B(unCStr(","));}),_1F=new T1(0,_1E),_1G=new T(function(){return B(unCStr("pow("));}),_1H=new T1(0,_1G),_1I=new T(function(){return B(unCStr(")"));}),_1J=new T1(0,_1I),_1K=new T2(1,_1J,_T),_1L=function(_1M,_1N){return new T1(1,new T2(1,_1H,new T2(1,_1M,new T2(1,_1F,new T2(1,_1N,_1K)))));},_1O=new T(function(){return B(unCStr("acos("));}),_1P=new T1(0,_1O),_1Q=function(_1R){return new T1(1,new T2(1,_1P,new T2(1,_1R,_1K)));},_1S=new T(function(){return B(unCStr("acosh("));}),_1T=new T1(0,_1S),_1U=function(_1V){return new T1(1,new T2(1,_1T,new T2(1,_1V,_1K)));},_1W=new T(function(){return B(unCStr("asin("));}),_1X=new T1(0,_1W),_1Y=function(_1Z){return new T1(1,new T2(1,_1X,new T2(1,_1Z,_1K)));},_20=new T(function(){return B(unCStr("asinh("));}),_21=new T1(0,_20),_22=function(_23){return new T1(1,new T2(1,_21,new T2(1,_23,_1K)));},_24=new T(function(){return B(unCStr("atan("));}),_25=new T1(0,_24),_26=function(_27){return new T1(1,new T2(1,_25,new T2(1,_27,_1K)));},_28=new T(function(){return B(unCStr("atanh("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1K)));},_2c=new T(function(){return B(unCStr("cos("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1K)));},_2g=new T(function(){return B(unCStr("cosh("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1K)));},_2k=new T(function(){return B(unCStr("exp("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1K)));},_2o=new T(function(){return B(unCStr("log("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1K)));},_2s=new T(function(){return B(unCStr(")/log("));}),_2t=new T1(0,_2s),_2u=function(_2v,_2w){return new T1(1,new T2(1,_2p,new T2(1,_2w,new T2(1,_2t,new T2(1,_2v,_1K)))));},_2x=new T(function(){return B(unCStr("pi"));}),_2y=new T1(0,_2x),_2z=new T(function(){return B(unCStr("sin("));}),_2A=new T1(0,_2z),_2B=function(_2C){return new T1(1,new T2(1,_2A,new T2(1,_2C,_1K)));},_2D=new T(function(){return B(unCStr("sinh("));}),_2E=new T1(0,_2D),_2F=function(_2G){return new T1(1,new T2(1,_2E,new T2(1,_2G,_1K)));},_2H=new T(function(){return B(unCStr("sqrt("));}),_2I=new T1(0,_2H),_2J=function(_2K){return new T1(1,new T2(1,_2I,new T2(1,_2K,_1K)));},_2L=new T(function(){return B(unCStr("tan("));}),_2M=new T1(0,_2L),_2N=function(_2O){return new T1(1,new T2(1,_2M,new T2(1,_2O,_1K)));},_2P=new T(function(){return B(unCStr("tanh("));}),_2Q=new T1(0,_2P),_2R=function(_2S){return new T1(1,new T2(1,_2Q,new T2(1,_2S,_1K)));},_2T=new T(function(){return B(unCStr("("));}),_2U=new T1(0,_2T),_2V=new T(function(){return B(unCStr(")/("));}),_2W=new T1(0,_2V),_2X=function(_2Y,_2Z){return new T1(1,new T2(1,_2U,new T2(1,_2Y,new T2(1,_2W,new T2(1,_2Z,_1K)))));},_30=new T1(0,1),_31=function(_32,_33){var _34=E(_32);if(!_34._){var _35=_34.a,_36=E(_33);if(!_36._){var _37=_36.a;return (_35!=_37)?(_35>_37)?2:0:1;}else{var _38=I_compareInt(_36.a,_35);return (_38<=0)?(_38>=0)?1:2:0;}}else{var _39=_34.a,_3a=E(_33);if(!_3a._){var _3b=I_compareInt(_39,_3a.a);return (_3b>=0)?(_3b<=0)?1:2:0;}else{var _3c=I_compare(_39,_3a.a);return (_3c>=0)?(_3c<=0)?1:2:0;}}},_3d=new T(function(){return B(unCStr("base"));}),_3e=new T(function(){return B(unCStr("GHC.Exception"));}),_3f=new T(function(){return B(unCStr("ArithException"));}),_3g=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3d,_3e,_3f),_3h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3g,_T,_T),_3i=function(_3j){return E(_3h);},_3k=function(_3l){return E(E(_3l).a);},_3m=function(_3n,_3o,_3p){var _3q=B(A1(_3n,_)),_3r=B(A1(_3o,_)),_3s=hs_eqWord64(_3q.a,_3r.a);if(!_3s){return __Z;}else{var _3t=hs_eqWord64(_3q.b,_3r.b);return (!_3t)?__Z:new T1(1,_3p);}},_3u=function(_3v){var _3w=E(_3v);return new F(function(){return _3m(B(_3k(_3w.a)),_3i,_3w.b);});},_3x=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3y=new T(function(){return B(unCStr("denormal"));}),_3z=new T(function(){return B(unCStr("divide by zero"));}),_3A=new T(function(){return B(unCStr("loss of precision"));}),_3B=new T(function(){return B(unCStr("arithmetic underflow"));}),_3C=new T(function(){return B(unCStr("arithmetic overflow"));}),_3D=function(_3E,_3F){switch(E(_3E)){case 0:return new F(function(){return _14(_3C,_3F);});break;case 1:return new F(function(){return _14(_3B,_3F);});break;case 2:return new F(function(){return _14(_3A,_3F);});break;case 3:return new F(function(){return _14(_3z,_3F);});break;case 4:return new F(function(){return _14(_3y,_3F);});break;default:return new F(function(){return _14(_3x,_3F);});}},_3G=function(_3H){return new F(function(){return _3D(_3H,_T);});},_3I=function(_3J,_3K,_3L){return new F(function(){return _3D(_3K,_3L);});},_3M=44,_3N=93,_3O=91,_3P=function(_3Q,_3R,_3S){var _3T=E(_3R);if(!_3T._){return new F(function(){return unAppCStr("[]",_3S);});}else{var _3U=new T(function(){var _3V=new T(function(){var _3W=function(_3X){var _3Y=E(_3X);if(!_3Y._){return E(new T2(1,_3N,_3S));}else{var _3Z=new T(function(){return B(A2(_3Q,_3Y.a,new T(function(){return B(_3W(_3Y.b));})));});return new T2(1,_3M,_3Z);}};return B(_3W(_3T.b));});return B(A2(_3Q,_3T.a,_3V));});return new T2(1,_3O,_3U);}},_40=function(_41,_42){return new F(function(){return _3P(_3D,_41,_42);});},_43=new T3(0,_3I,_3G,_40),_44=new T(function(){return new T5(0,_3i,_43,_45,_3u,_3G);}),_45=function(_46){return new T2(0,_44,_46);},_47=3,_48=new T(function(){return B(_45(_47));}),_49=new T(function(){return die(_48);}),_4a=function(_4b,_4c){var _4d=E(_4b);return (_4d._==0)?_4d.a*Math.pow(2,_4c):I_toNumber(_4d.a)*Math.pow(2,_4c);},_4e=function(_4f,_4g){var _4h=E(_4f);if(!_4h._){var _4i=_4h.a,_4j=E(_4g);return (_4j._==0)?_4i==_4j.a:(I_compareInt(_4j.a,_4i)==0)?true:false;}else{var _4k=_4h.a,_4l=E(_4g);return (_4l._==0)?(I_compareInt(_4k,_4l.a)==0)?true:false:(I_compare(_4k,_4l.a)==0)?true:false;}},_4m=function(_4n){var _4o=E(_4n);if(!_4o._){return E(_4o.a);}else{return new F(function(){return I_toInt(_4o.a);});}},_4p=function(_4q,_4r){while(1){var _4s=E(_4q);if(!_4s._){var _4t=_4s.a,_4u=E(_4r);if(!_4u._){var _4v=_4u.a,_4w=addC(_4t,_4v);if(!E(_4w.b)){return new T1(0,_4w.a);}else{_4q=new T1(1,I_fromInt(_4t));_4r=new T1(1,I_fromInt(_4v));continue;}}else{_4q=new T1(1,I_fromInt(_4t));_4r=_4u;continue;}}else{var _4x=E(_4r);if(!_4x._){_4q=_4s;_4r=new T1(1,I_fromInt(_4x.a));continue;}else{return new T1(1,I_add(_4s.a,_4x.a));}}}},_4y=function(_4z,_4A){while(1){var _4B=E(_4z);if(!_4B._){var _4C=E(_4B.a);if(_4C==(-2147483648)){_4z=new T1(1,I_fromInt(-2147483648));continue;}else{var _4D=E(_4A);if(!_4D._){var _4E=_4D.a;return new T2(0,new T1(0,quot(_4C,_4E)),new T1(0,_4C%_4E));}else{_4z=new T1(1,I_fromInt(_4C));_4A=_4D;continue;}}}else{var _4F=E(_4A);if(!_4F._){_4z=_4B;_4A=new T1(1,I_fromInt(_4F.a));continue;}else{var _4G=I_quotRem(_4B.a,_4F.a);return new T2(0,new T1(1,_4G.a),new T1(1,_4G.b));}}}},_4H=new T1(0,0),_4I=function(_4J,_4K){while(1){var _4L=E(_4J);if(!_4L._){_4J=new T1(1,I_fromInt(_4L.a));continue;}else{return new T1(1,I_shiftLeft(_4L.a,_4K));}}},_4M=function(_4N,_4O,_4P){if(!B(_4e(_4P,_4H))){var _4Q=B(_4y(_4O,_4P)),_4R=_4Q.a;switch(B(_31(B(_4I(_4Q.b,1)),_4P))){case 0:return new F(function(){return _4a(_4R,_4N);});break;case 1:if(!(B(_4m(_4R))&1)){return new F(function(){return _4a(_4R,_4N);});}else{return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}break;default:return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}}else{return E(_49);}},_4S=function(_4T,_4U){var _4V=E(_4T);if(!_4V._){var _4W=_4V.a,_4X=E(_4U);return (_4X._==0)?_4W>_4X.a:I_compareInt(_4X.a,_4W)<0;}else{var _4Y=_4V.a,_4Z=E(_4U);return (_4Z._==0)?I_compareInt(_4Y,_4Z.a)>0:I_compare(_4Y,_4Z.a)>0;}},_50=new T1(0,1),_51=function(_52,_53){var _54=E(_52);if(!_54._){var _55=_54.a,_56=E(_53);return (_56._==0)?_55<_56.a:I_compareInt(_56.a,_55)>0;}else{var _57=_54.a,_58=E(_53);return (_58._==0)?I_compareInt(_57,_58.a)<0:I_compare(_57,_58.a)<0;}},_59=new T(function(){return B(unCStr("base"));}),_5a=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5b=new T(function(){return B(unCStr("PatternMatchFail"));}),_5c=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_59,_5a,_5b),_5d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5c,_T,_T),_5e=function(_5f){return E(_5d);},_5g=function(_5h){var _5i=E(_5h);return new F(function(){return _3m(B(_3k(_5i.a)),_5e,_5i.b);});},_5j=function(_5k){return E(E(_5k).a);},_5l=function(_5m){return new T2(0,_5n,_5m);},_5o=function(_5p,_5q){return new F(function(){return _14(E(_5p).a,_5q);});},_5r=function(_5s,_5t){return new F(function(){return _3P(_5o,_5s,_5t);});},_5u=function(_5v,_5w,_5x){return new F(function(){return _14(E(_5w).a,_5x);});},_5y=new T3(0,_5u,_5j,_5r),_5n=new T(function(){return new T5(0,_5e,_5y,_5l,_5g,_5j);}),_5z=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5A=function(_5B){return E(E(_5B).c);},_5C=function(_5D,_5E){return new F(function(){return die(new T(function(){return B(A2(_5A,_5E,_5D));}));});},_5F=function(_5G,_46){return new F(function(){return _5C(_5G,_46);});},_5H=function(_5I,_5J){var _5K=E(_5J);if(!_5K._){return new T2(0,_T,_T);}else{var _5L=_5K.a;if(!B(A1(_5I,_5L))){return new T2(0,_T,_5K);}else{var _5M=new T(function(){var _5N=B(_5H(_5I,_5K.b));return new T2(0,_5N.a,_5N.b);});return new T2(0,new T2(1,_5L,new T(function(){return E(E(_5M).a);})),new T(function(){return E(E(_5M).b);}));}}},_5O=32,_5P=new T(function(){return B(unCStr("\n"));}),_5Q=function(_5R){return (E(_5R)==124)?false:true;},_5S=function(_5T,_5U){var _5V=B(_5H(_5Q,B(unCStr(_5T)))),_5W=_5V.a,_5X=function(_5Y,_5Z){var _60=new T(function(){var _61=new T(function(){return B(_14(_5U,new T(function(){return B(_14(_5Z,_5P));},1)));});return B(unAppCStr(": ",_61));},1);return new F(function(){return _14(_5Y,_60);});},_62=E(_5V.b);if(!_62._){return new F(function(){return _5X(_5W,_T);});}else{if(E(_62.a)==124){return new F(function(){return _5X(_5W,new T2(1,_5O,_62.b));});}else{return new F(function(){return _5X(_5W,_T);});}}},_63=function(_64){return new F(function(){return _5F(new T1(0,new T(function(){return B(_5S(_64,_5z));})),_5n);});},_65=function(_66){var _67=function(_68,_69){while(1){if(!B(_51(_68,_66))){if(!B(_4S(_68,_66))){if(!B(_4e(_68,_66))){return new F(function(){return _63("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_69);}}else{return _69-1|0;}}else{var _6a=B(_4I(_68,1)),_6b=_69+1|0;_68=_6a;_69=_6b;continue;}}};return new F(function(){return _67(_50,0);});},_6c=function(_6d){var _6e=E(_6d);if(!_6e._){var _6f=_6e.a>>>0;if(!_6f){return -1;}else{var _6g=function(_6h,_6i){while(1){if(_6h>=_6f){if(_6h<=_6f){if(_6h!=_6f){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6i);}}else{return _6i-1|0;}}else{var _6j=imul(_6h,2)>>>0,_6k=_6i+1|0;_6h=_6j;_6i=_6k;continue;}}};return new F(function(){return _6g(1,0);});}}else{return new F(function(){return _65(_6e);});}},_6l=function(_6m){var _6n=E(_6m);if(!_6n._){var _6o=_6n.a>>>0;if(!_6o){return new T2(0,-1,0);}else{var _6p=function(_6q,_6r){while(1){if(_6q>=_6o){if(_6q<=_6o){if(_6q!=_6o){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6r);}}else{return _6r-1|0;}}else{var _6s=imul(_6q,2)>>>0,_6t=_6r+1|0;_6q=_6s;_6r=_6t;continue;}}};return new T2(0,B(_6p(1,0)),(_6o&_6o-1>>>0)>>>0&4294967295);}}else{var _6u=_6n.a;return new T2(0,B(_6c(_6n)),I_compareInt(I_and(_6u,I_sub(_6u,I_fromInt(1))),0));}},_6v=function(_6w,_6x){var _6y=E(_6w);if(!_6y._){var _6z=_6y.a,_6A=E(_6x);return (_6A._==0)?_6z<=_6A.a:I_compareInt(_6A.a,_6z)>=0;}else{var _6B=_6y.a,_6C=E(_6x);return (_6C._==0)?I_compareInt(_6B,_6C.a)<=0:I_compare(_6B,_6C.a)<=0;}},_6D=function(_6E,_6F){while(1){var _6G=E(_6E);if(!_6G._){var _6H=_6G.a,_6I=E(_6F);if(!_6I._){return new T1(0,(_6H>>>0&_6I.a>>>0)>>>0&4294967295);}else{_6E=new T1(1,I_fromInt(_6H));_6F=_6I;continue;}}else{var _6J=E(_6F);if(!_6J._){_6E=_6G;_6F=new T1(1,I_fromInt(_6J.a));continue;}else{return new T1(1,I_and(_6G.a,_6J.a));}}}},_6K=function(_6L,_6M){while(1){var _6N=E(_6L);if(!_6N._){var _6O=_6N.a,_6P=E(_6M);if(!_6P._){var _6Q=_6P.a,_6R=subC(_6O,_6Q);if(!E(_6R.b)){return new T1(0,_6R.a);}else{_6L=new T1(1,I_fromInt(_6O));_6M=new T1(1,I_fromInt(_6Q));continue;}}else{_6L=new T1(1,I_fromInt(_6O));_6M=_6P;continue;}}else{var _6S=E(_6M);if(!_6S._){_6L=_6N;_6M=new T1(1,I_fromInt(_6S.a));continue;}else{return new T1(1,I_sub(_6N.a,_6S.a));}}}},_6T=new T1(0,2),_6U=function(_6V,_6W){var _6X=E(_6V);if(!_6X._){var _6Y=(_6X.a>>>0&(2<<_6W>>>0)-1>>>0)>>>0,_6Z=1<<_6W>>>0;return (_6Z<=_6Y)?(_6Z>=_6Y)?1:2:0;}else{var _70=B(_6D(_6X,B(_6K(B(_4I(_6T,_6W)),_50)))),_71=B(_4I(_50,_6W));return (!B(_4S(_71,_70)))?(!B(_51(_71,_70)))?1:2:0;}},_72=function(_73,_74){while(1){var _75=E(_73);if(!_75._){_73=new T1(1,I_fromInt(_75.a));continue;}else{return new T1(1,I_shiftRight(_75.a,_74));}}},_76=function(_77,_78,_79,_7a){var _7b=B(_6l(_7a)),_7c=_7b.a;if(!E(_7b.b)){var _7d=B(_6c(_79));if(_7d<((_7c+_77|0)-1|0)){var _7e=_7c+(_77-_78|0)|0;if(_7e>0){if(_7e>_7d){if(_7e<=(_7d+1|0)){if(!E(B(_6l(_79)).b)){return 0;}else{return new F(function(){return _4a(_30,_77-_78|0);});}}else{return 0;}}else{var _7f=B(_72(_79,_7e));switch(B(_6U(_79,_7e-1|0))){case 0:return new F(function(){return _4a(_7f,_77-_78|0);});break;case 1:if(!(B(_4m(_7f))&1)){return new F(function(){return _4a(_7f,_77-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}break;default:return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}}}else{return new F(function(){return _4a(_79,(_77-_78|0)-_7e|0);});}}else{if(_7d>=_78){var _7g=B(_72(_79,(_7d+1|0)-_78|0));switch(B(_6U(_79,_7d-_78|0))){case 0:return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});break;case 2:return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});break;default:if(!(B(_4m(_7g))&1)){return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});}}}else{return new F(function(){return _4a(_79, -_7c);});}}}else{var _7h=B(_6c(_79))-_7c|0,_7i=function(_7j){var _7k=function(_7l,_7m){if(!B(_6v(B(_4I(_7m,_78)),_7l))){return new F(function(){return _4M(_7j-_78|0,_7l,_7m);});}else{return new F(function(){return _4M((_7j-_78|0)+1|0,_7l,B(_4I(_7m,1)));});}};if(_7j>=_78){if(_7j!=_78){return new F(function(){return _7k(_79,new T(function(){return B(_4I(_7a,_7j-_78|0));}));});}else{return new F(function(){return _7k(_79,_7a);});}}else{return new F(function(){return _7k(new T(function(){return B(_4I(_79,_78-_7j|0));}),_7a);});}};if(_77>_7h){return new F(function(){return _7i(_77);});}else{return new F(function(){return _7i(_7h);});}}},_7n=new T1(0,2147483647),_7o=new T(function(){return B(_4p(_7n,_50));}),_7p=function(_7q){var _7r=E(_7q);if(!_7r._){var _7s=E(_7r.a);return (_7s==(-2147483648))?E(_7o):new T1(0, -_7s);}else{return new T1(1,I_negate(_7r.a));}},_7t=new T(function(){return 0/0;}),_7u=new T(function(){return -1/0;}),_7v=new T(function(){return 1/0;}),_7w=0,_7x=function(_7y,_7z){if(!B(_4e(_7z,_4H))){if(!B(_4e(_7y,_4H))){if(!B(_51(_7y,_4H))){return new F(function(){return _76(-1021,53,_7y,_7z);});}else{return  -B(_76(-1021,53,B(_7p(_7y)),_7z));}}else{return E(_7w);}}else{return (!B(_4e(_7y,_4H)))?(!B(_51(_7y,_4H)))?E(_7v):E(_7u):E(_7t);}},_7A=function(_7B){return new T1(0,new T(function(){var _7C=E(_7B),_7D=jsShow(B(_7x(_7C.a,_7C.b)));return fromJSStr(_7D);}));},_7E=new T(function(){return B(unCStr("1./("));}),_7F=new T1(0,_7E),_7G=function(_7H){return new T1(1,new T2(1,_7F,new T2(1,_7H,_1K)));},_7I=new T(function(){return B(unCStr(")+("));}),_7J=new T1(0,_7I),_7K=function(_7L,_7M){return new T1(1,new T2(1,_2U,new T2(1,_7L,new T2(1,_7J,new T2(1,_7M,_1K)))));},_7N=new T(function(){return B(unCStr("-("));}),_7O=new T1(0,_7N),_7P=function(_7Q){return new T1(1,new T2(1,_7O,new T2(1,_7Q,_1K)));},_7R=new T(function(){return B(unCStr(")*("));}),_7S=new T1(0,_7R),_7T=function(_7U,_7V){return new T1(1,new T2(1,_2U,new T2(1,_7U,new T2(1,_7S,new T2(1,_7V,_1K)))));},_7W=function(_7X){return E(E(_7X).a);},_7Y=function(_7Z){return E(E(_7Z).d);},_80=function(_81,_82){return new F(function(){return A3(_7W,_83,_81,new T(function(){return B(A2(_7Y,_83,_82));}));});},_84=new T(function(){return B(unCStr("abs("));}),_85=new T1(0,_84),_86=function(_87){return new T1(1,new T2(1,_85,new T2(1,_87,_1K)));},_88=function(_89){while(1){var _8a=E(_89);if(!_8a._){_89=new T1(1,I_fromInt(_8a.a));continue;}else{return new F(function(){return I_toString(_8a.a);});}}},_8b=function(_8c,_8d){return new F(function(){return _14(fromJSStr(B(_88(_8c))),_8d);});},_8e=41,_8f=40,_8g=new T1(0,0),_8h=function(_8i,_8j,_8k){if(_8i<=6){return new F(function(){return _8b(_8j,_8k);});}else{if(!B(_51(_8j,_8g))){return new F(function(){return _8b(_8j,_8k);});}else{return new T2(1,_8f,new T(function(){return B(_14(fromJSStr(B(_88(_8j))),new T2(1,_8e,_8k)));}));}}},_8l=new T(function(){return B(unCStr("."));}),_8m=function(_8n){return new T1(0,new T(function(){return B(_14(B(_8h(0,_8n,_T)),_8l));}));},_8o=new T(function(){return B(unCStr("sign("));}),_8p=new T1(0,_8o),_8q=function(_8r){return new T1(1,new T2(1,_8p,new T2(1,_8r,_1K)));},_83=new T(function(){return {_:0,a:_7K,b:_80,c:_7T,d:_7P,e:_86,f:_8q,g:_8m};}),_8s=new T4(0,_83,_2X,_7G,_7A),_8t={_:0,a:_8s,b:_2y,c:_2m,d:_2q,e:_2J,f:_1L,g:_2u,h:_2B,i:_2e,j:_2N,k:_1Y,l:_1Q,m:_26,n:_2F,o:_2i,p:_2R,q:_22,r:_1U,s:_2a},_8u=function(_8v){return E(E(_8v).a);},_8w=function(_8x){return E(E(_8x).a);},_8y=function(_8z){return E(E(_8z).c);},_8A=function(_8B){return E(E(_8B).b);},_8C=function(_8D){return E(E(_8D).d);},_8E=new T1(0,1),_8F=new T1(0,2),_8G=new T2(0,E(_8E),E(_8F)),_8H=new T1(0,5),_8I=new T1(0,4),_8J=new T2(0,E(_8I),E(_8H)),_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O,_8P,_8Q){var _8R=B(_8u(_8N)),_8S=B(_8w(_8R)),_8T=new T(function(){var _8U=new T(function(){var _8V=new T(function(){var _8W=new T(function(){var _8X=new T(function(){var _8Y=new T(function(){return B(A3(_7W,_8S,new T(function(){return B(A3(_8y,_8S,_8O,_8O));}),new T(function(){return B(A3(_8y,_8S,_8Q,_8Q));})));});return B(A2(_8K,_8N,_8Y));});return B(A3(_8A,_8S,_8X,new T(function(){return B(A2(_8C,_8R,_8J));})));});return B(A3(_8y,_8S,_8W,_8W));});return B(A3(_7W,_8S,_8V,new T(function(){return B(A3(_8y,_8S,_8P,_8P));})));});return B(A2(_8K,_8N,_8U));});return new F(function(){return A3(_8A,_8S,_8T,new T(function(){return B(A2(_8C,_8R,_8G));}));});},_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T(function(){return B(unCStr("y"));}),_92=new T1(0,_91),_93=new T(function(){return B(unCStr("x"));}),_94=new T1(0,_93),_95=new T(function(){return B(_8M(_8t,_94,_92,_90));}),_96=new T(function(){return toJSStr(B(_1o(_1D,_11,_95)));}),_97=function(_98,_99,_9a){var _9b=new T(function(){return B(_1k(_98));}),_9c=new T(function(){return B(_1m(_98));}),_9d=function(_9e){var _9f=E(_9e);if(!_9f._){return E(_9c);}else{return new F(function(){return A2(_9b,new T(function(){return B(_1o(_98,_99,_9f.a));}),new T(function(){return B(_9d(_9f.b));}));});}};return new F(function(){return _9d(_9a);});},_9g=new T3(0,_94,_92,_90),_9h=function(_9i,_9j){var _9k=E(_9i);return E(_9j);},_9l=function(_9m,_9n){var _9o=E(_9m),_9p=E(_9n);return new T3(0,new T(function(){return B(A1(_9o.a,_9p.a));}),new T(function(){return B(A1(_9o.b,_9p.b));}),new T(function(){return B(A1(_9o.c,_9p.c));}));},_9q=function(_9r){return new T3(0,_9r,_9r,_9r);},_9s=function(_9t,_9u){var _9v=E(_9u);return new T3(0,_9t,_9t,_9t);},_9w=function(_9x,_9y){var _9z=E(_9y);return new T3(0,new T(function(){return B(A1(_9x,_9z.a));}),new T(function(){return B(A1(_9x,_9z.b));}),new T(function(){return B(A1(_9x,_9z.c));}));},_9A=new T2(0,_9w,_9s),_9B=function(_9C,_9D){var _9E=E(_9C),_9F=E(_9D);return new T3(0,_9E.a,_9E.b,_9E.c);},_9G=new T5(0,_9A,_9q,_9l,_9h,_9B),_9H=new T1(0,0),_9I=function(_9J){return E(E(_9J).g);},_9K=function(_9L){return new T3(0,new T3(0,new T(function(){return B(A2(_9I,_9L,_8E));}),new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_9H));})),new T3(0,new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_8E));}),new T(function(){return B(A2(_9I,_9L,_9H));})),new T3(0,new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_8E));})));},_9M=function(_9N){var _9O=B(_9K(_9N));return new T3(0,_9O.a,_9O.b,_9O.c);},_9P=function(_9Q){return E(E(_9Q).a);},_9R=function(_9S){return E(E(_9S).f);},_9T=function(_9U){return E(E(_9U).b);},_9V=function(_9W){return E(E(_9W).c);},_9X=function(_9Y){return E(E(_9Y).a);},_9Z=function(_a0){return E(E(_a0).d);},_a1=function(_a2,_a3,_a4,_a5,_a6){var _a7=new T(function(){return E(E(_a2).c);}),_a8=new T(function(){var _a9=E(_a2).a,_aa=new T(function(){var _ab=new T(function(){return B(_8u(_a7));}),_ac=new T(function(){return B(_8w(_ab));}),_ad=new T(function(){return B(A2(_9Z,_a7,_a3));}),_ae=new T(function(){return B(A3(_9R,_a7,_a3,_a5));}),_af=function(_ag,_ah){var _ai=new T(function(){var _aj=new T(function(){return B(A3(_9T,_ab,new T(function(){return B(A3(_8y,_ac,_a5,_ag));}),_a3));});return B(A3(_7W,_ac,_aj,new T(function(){return B(A3(_8y,_ac,_ah,_ad));})));});return new F(function(){return A3(_8y,_ac,_ae,_ai);});};return B(A3(_9X,B(_9P(_a9)),_af,_a4));});return B(A3(_9V,_a9,_aa,_a6));});return new T2(0,new T(function(){return B(A3(_9R,_a7,_a3,_a5));}),_a8);},_ak=function(_al,_am,_an,_ao){var _ap=E(_an),_aq=E(_ao),_ar=B(_a1(_am,_ap.a,_ap.b,_aq.a,_aq.b));return new T2(0,_ar.a,_ar.b);},_as=new T1(0,1),_at=function(_au){return E(E(_au).l);},_av=function(_aw,_ax,_ay){var _az=new T(function(){return E(E(_aw).c);}),_aA=new T(function(){var _aB=new T(function(){return B(_8u(_az));}),_aC=new T(function(){var _aD=B(_8w(_aB)),_aE=new T(function(){var _aF=new T(function(){return B(A3(_8A,_aD,new T(function(){return B(A2(_9I,_aD,_as));}),new T(function(){return B(A3(_8y,_aD,_ax,_ax));})));});return B(A2(_8K,_az,_aF));});return B(A2(_7Y,_aD,_aE));});return B(A3(_9X,B(_9P(E(_aw).a)),function(_aG){return new F(function(){return A3(_9T,_aB,_aG,_aC);});},_ay));});return new T2(0,new T(function(){return B(A2(_at,_az,_ax));}),_aA);},_aH=function(_aI,_aJ,_aK){var _aL=E(_aK),_aM=B(_av(_aJ,_aL.a,_aL.b));return new T2(0,_aM.a,_aM.b);},_aN=function(_aO){return E(E(_aO).r);},_aP=function(_aQ,_aR,_aS){var _aT=new T(function(){return E(E(_aQ).c);}),_aU=new T(function(){var _aV=new T(function(){return B(_8u(_aT));}),_aW=new T(function(){var _aX=new T(function(){var _aY=B(_8w(_aV));return B(A3(_8A,_aY,new T(function(){return B(A3(_8y,_aY,_aR,_aR));}),new T(function(){return B(A2(_9I,_aY,_as));})));});return B(A2(_8K,_aT,_aX));});return B(A3(_9X,B(_9P(E(_aQ).a)),function(_aZ){return new F(function(){return A3(_9T,_aV,_aZ,_aW);});},_aS));});return new T2(0,new T(function(){return B(A2(_aN,_aT,_aR));}),_aU);},_b0=function(_b1,_b2,_b3){var _b4=E(_b3),_b5=B(_aP(_b2,_b4.a,_b4.b));return new T2(0,_b5.a,_b5.b);},_b6=function(_b7){return E(E(_b7).k);},_b8=function(_b9,_ba,_bb){var _bc=new T(function(){return E(E(_b9).c);}),_bd=new T(function(){var _be=new T(function(){return B(_8u(_bc));}),_bf=new T(function(){var _bg=new T(function(){var _bh=B(_8w(_be));return B(A3(_8A,_bh,new T(function(){return B(A2(_9I,_bh,_as));}),new T(function(){return B(A3(_8y,_bh,_ba,_ba));})));});return B(A2(_8K,_bc,_bg));});return B(A3(_9X,B(_9P(E(_b9).a)),function(_bi){return new F(function(){return A3(_9T,_be,_bi,_bf);});},_bb));});return new T2(0,new T(function(){return B(A2(_b6,_bc,_ba));}),_bd);},_bj=function(_bk,_bl,_bm){var _bn=E(_bm),_bo=B(_b8(_bl,_bn.a,_bn.b));return new T2(0,_bo.a,_bo.b);},_bp=function(_bq){return E(E(_bq).q);},_br=function(_bs,_bt,_bu){var _bv=new T(function(){return E(E(_bs).c);}),_bw=new T(function(){var _bx=new T(function(){return B(_8u(_bv));}),_by=new T(function(){var _bz=new T(function(){var _bA=B(_8w(_bx));return B(A3(_7W,_bA,new T(function(){return B(A3(_8y,_bA,_bt,_bt));}),new T(function(){return B(A2(_9I,_bA,_as));})));});return B(A2(_8K,_bv,_bz));});return B(A3(_9X,B(_9P(E(_bs).a)),function(_bB){return new F(function(){return A3(_9T,_bx,_bB,_by);});},_bu));});return new T2(0,new T(function(){return B(A2(_bp,_bv,_bt));}),_bw);},_bC=function(_bD,_bE,_bF){var _bG=E(_bF),_bH=B(_br(_bE,_bG.a,_bG.b));return new T2(0,_bH.a,_bH.b);},_bI=function(_bJ){return E(E(_bJ).m);},_bK=function(_bL,_bM,_bN){var _bO=new T(function(){return E(E(_bL).c);}),_bP=new T(function(){var _bQ=new T(function(){return B(_8u(_bO));}),_bR=new T(function(){var _bS=B(_8w(_bQ));return B(A3(_7W,_bS,new T(function(){return B(A2(_9I,_bS,_as));}),new T(function(){return B(A3(_8y,_bS,_bM,_bM));})));});return B(A3(_9X,B(_9P(E(_bL).a)),function(_bT){return new F(function(){return A3(_9T,_bQ,_bT,_bR);});},_bN));});return new T2(0,new T(function(){return B(A2(_bI,_bO,_bM));}),_bP);},_bU=function(_bV,_bW,_bX){var _bY=E(_bX),_bZ=B(_bK(_bW,_bY.a,_bY.b));return new T2(0,_bZ.a,_bZ.b);},_c0=function(_c1){return E(E(_c1).s);},_c2=function(_c3,_c4,_c5){var _c6=new T(function(){return E(E(_c3).c);}),_c7=new T(function(){var _c8=new T(function(){return B(_8u(_c6));}),_c9=new T(function(){var _ca=B(_8w(_c8));return B(A3(_8A,_ca,new T(function(){return B(A2(_9I,_ca,_as));}),new T(function(){return B(A3(_8y,_ca,_c4,_c4));})));});return B(A3(_9X,B(_9P(E(_c3).a)),function(_cb){return new F(function(){return A3(_9T,_c8,_cb,_c9);});},_c5));});return new T2(0,new T(function(){return B(A2(_c0,_c6,_c4));}),_c7);},_cc=function(_cd,_ce,_cf){var _cg=E(_cf),_ch=B(_c2(_ce,_cg.a,_cg.b));return new T2(0,_ch.a,_ch.b);},_ci=function(_cj){return E(E(_cj).i);},_ck=function(_cl){return E(E(_cl).h);},_cm=function(_cn,_co,_cp){var _cq=new T(function(){return E(E(_cn).c);}),_cr=new T(function(){var _cs=new T(function(){return B(_8w(new T(function(){return B(_8u(_cq));})));}),_ct=new T(function(){return B(A2(_7Y,_cs,new T(function(){return B(A2(_ck,_cq,_co));})));});return B(A3(_9X,B(_9P(E(_cn).a)),function(_cu){return new F(function(){return A3(_8y,_cs,_cu,_ct);});},_cp));});return new T2(0,new T(function(){return B(A2(_ci,_cq,_co));}),_cr);},_cv=function(_cw,_cx,_cy){var _cz=E(_cy),_cA=B(_cm(_cx,_cz.a,_cz.b));return new T2(0,_cA.a,_cA.b);},_cB=function(_cC){return E(E(_cC).o);},_cD=function(_cE){return E(E(_cE).n);},_cF=function(_cG,_cH,_cI){var _cJ=new T(function(){return E(E(_cG).c);}),_cK=new T(function(){var _cL=new T(function(){return B(_8w(new T(function(){return B(_8u(_cJ));})));}),_cM=new T(function(){return B(A2(_cD,_cJ,_cH));});return B(A3(_9X,B(_9P(E(_cG).a)),function(_cN){return new F(function(){return A3(_8y,_cL,_cN,_cM);});},_cI));});return new T2(0,new T(function(){return B(A2(_cB,_cJ,_cH));}),_cK);},_cO=function(_cP,_cQ,_cR){var _cS=E(_cR),_cT=B(_cF(_cQ,_cS.a,_cS.b));return new T2(0,_cT.a,_cT.b);},_cU=function(_cV){return E(E(_cV).c);},_cW=function(_cX,_cY,_cZ){var _d0=new T(function(){return E(E(_cX).c);}),_d1=new T(function(){var _d2=new T(function(){return B(_8w(new T(function(){return B(_8u(_d0));})));}),_d3=new T(function(){return B(A2(_cU,_d0,_cY));});return B(A3(_9X,B(_9P(E(_cX).a)),function(_d4){return new F(function(){return A3(_8y,_d2,_d4,_d3);});},_cZ));});return new T2(0,new T(function(){return B(A2(_cU,_d0,_cY));}),_d1);},_d5=function(_d6,_d7,_d8){var _d9=E(_d8),_da=B(_cW(_d7,_d9.a,_d9.b));return new T2(0,_da.a,_da.b);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(_dc).c);}),_dg=new T(function(){var _dh=new T(function(){return B(_8u(_df));}),_di=new T(function(){return B(_8w(_dh));}),_dj=new T(function(){return B(A3(_9T,_dh,new T(function(){return B(A2(_9I,_di,_as));}),_dd));});return B(A3(_9X,B(_9P(E(_dc).a)),function(_dk){return new F(function(){return A3(_8y,_di,_dk,_dj);});},_de));});return new T2(0,new T(function(){return B(A2(_9Z,_df,_dd));}),_dg);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_db(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du,_dv){var _dw=new T3(0,new T(function(){return E(E(_dt).a);}),new T(function(){return E(E(_dt).b);}),new T(function(){return E(E(_dt).c);}));return new F(function(){return A3(_9T,_ds,new T(function(){var _dx=E(_dv),_dy=B(_db(_dw,_dx.a,_dx.b));return new T2(0,_dy.a,_dy.b);}),new T(function(){var _dz=E(_du),_dA=B(_db(_dw,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);}));});},_dB=new T1(0,0),_dC=function(_dD){return E(E(_dD).b);},_dE=function(_dF){return E(E(_dF).b);},_dG=function(_dH){var _dI=new T(function(){return E(E(_dH).c);}),_dJ=new T(function(){return B(A2(_dE,E(_dH).a,new T(function(){return B(A2(_9I,B(_8w(B(_8u(_dI)))),_dB));})));});return new T2(0,new T(function(){return B(_dC(_dI));}),_dJ);},_dK=function(_dL,_dM){var _dN=B(_dG(_dM));return new T2(0,_dN.a,_dN.b);},_dO=function(_dP,_dQ,_dR){var _dS=new T(function(){return E(E(_dP).c);}),_dT=new T(function(){var _dU=new T(function(){return B(_8w(new T(function(){return B(_8u(_dS));})));}),_dV=new T(function(){return B(A2(_ci,_dS,_dQ));});return B(A3(_9X,B(_9P(E(_dP).a)),function(_dW){return new F(function(){return A3(_8y,_dU,_dW,_dV);});},_dR));});return new T2(0,new T(function(){return B(A2(_ck,_dS,_dQ));}),_dT);},_dX=function(_dY,_dZ,_e0){var _e1=E(_e0),_e2=B(_dO(_dZ,_e1.a,_e1.b));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(_e4).c);}),_e8=new T(function(){var _e9=new T(function(){return B(_8w(new T(function(){return B(_8u(_e7));})));}),_ea=new T(function(){return B(A2(_cB,_e7,_e5));});return B(A3(_9X,B(_9P(E(_e4).a)),function(_eb){return new F(function(){return A3(_8y,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cD,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=new T1(0,2),_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(_ek).c);}),_eo=new T(function(){var _ep=new T(function(){return B(_8u(_en));}),_eq=new T(function(){return B(_8w(_ep));}),_er=new T(function(){var _es=new T(function(){return B(A3(_9T,_ep,new T(function(){return B(A2(_9I,_eq,_as));}),new T(function(){return B(A2(_9I,_eq,_ei));})));});return B(A3(_9T,_ep,_es,new T(function(){return B(A2(_8K,_en,_el));})));});return B(A3(_9X,B(_9P(E(_ek).a)),function(_et){return new F(function(){return A3(_8y,_eq,_et,_er);});},_em));});return new T2(0,new T(function(){return B(A2(_8K,_en,_el));}),_eo);},_eu=function(_ev,_ew,_ex){var _ey=E(_ex),_ez=B(_ej(_ew,_ey.a,_ey.b));return new T2(0,_ez.a,_ez.b);},_eA=function(_eB){return E(E(_eB).j);},_eC=function(_eD,_eE,_eF){var _eG=new T(function(){return E(E(_eD).c);}),_eH=new T(function(){var _eI=new T(function(){return B(_8u(_eG));}),_eJ=new T(function(){var _eK=new T(function(){return B(A2(_ci,_eG,_eE));});return B(A3(_8y,B(_8w(_eI)),_eK,_eK));});return B(A3(_9X,B(_9P(E(_eD).a)),function(_eL){return new F(function(){return A3(_9T,_eI,_eL,_eJ);});},_eF));});return new T2(0,new T(function(){return B(A2(_eA,_eG,_eE));}),_eH);},_eM=function(_eN,_eO,_eP){var _eQ=E(_eP),_eR=B(_eC(_eO,_eQ.a,_eQ.b));return new T2(0,_eR.a,_eR.b);},_eS=function(_eT){return E(E(_eT).p);},_eU=function(_eV,_eW,_eX){var _eY=new T(function(){return E(E(_eV).c);}),_eZ=new T(function(){var _f0=new T(function(){return B(_8u(_eY));}),_f1=new T(function(){var _f2=new T(function(){return B(A2(_cB,_eY,_eW));});return B(A3(_8y,B(_8w(_f0)),_f2,_f2));});return B(A3(_9X,B(_9P(E(_eV).a)),function(_f3){return new F(function(){return A3(_9T,_f0,_f3,_f1);});},_eX));});return new T2(0,new T(function(){return B(A2(_eS,_eY,_eW));}),_eZ);},_f4=function(_f5,_f6,_f7){var _f8=E(_f7),_f9=B(_eU(_f6,_f8.a,_f8.b));return new T2(0,_f9.a,_f9.b);},_fa=function(_fb,_fc){return {_:0,a:_fb,b:new T(function(){return B(_dK(_fb,_fc));}),c:function(_fd){return new F(function(){return _d5(_fb,_fc,_fd);});},d:function(_fd){return new F(function(){return _dl(_fb,_fc,_fd);});},e:function(_fd){return new F(function(){return _eu(_fb,_fc,_fd);});},f:function(_fe,_fd){return new F(function(){return _ak(_fb,_fc,_fe,_fd);});},g:function(_fe,_fd){return new F(function(){return _dr(_fb,_fc,_fe,_fd);});},h:function(_fd){return new F(function(){return _dX(_fb,_fc,_fd);});},i:function(_fd){return new F(function(){return _cv(_fb,_fc,_fd);});},j:function(_fd){return new F(function(){return _eM(_fb,_fc,_fd);});},k:function(_fd){return new F(function(){return _bj(_fb,_fc,_fd);});},l:function(_fd){return new F(function(){return _aH(_fb,_fc,_fd);});},m:function(_fd){return new F(function(){return _bU(_fb,_fc,_fd);});},n:function(_fd){return new F(function(){return _ec(_fb,_fc,_fd);});},o:function(_fd){return new F(function(){return _cO(_fb,_fc,_fd);});},p:function(_fd){return new F(function(){return _f4(_fb,_fc,_fd);});},q:function(_fd){return new F(function(){return _bC(_fb,_fc,_fd);});},r:function(_fd){return new F(function(){return _b0(_fb,_fc,_fd);});},s:function(_fd){return new F(function(){return _cc(_fb,_fc,_fd);});}};},_ff=function(_fg,_fh,_fi,_fj,_fk){var _fl=new T(function(){return B(_8u(new T(function(){return E(E(_fg).c);})));}),_fm=new T(function(){var _fn=E(_fg).a,_fo=new T(function(){var _fp=new T(function(){return B(_8w(_fl));}),_fq=new T(function(){return B(A3(_8y,_fp,_fj,_fj));}),_fr=function(_fs,_ft){var _fu=new T(function(){return B(A3(_8A,_fp,new T(function(){return B(A3(_8y,_fp,_fs,_fj));}),new T(function(){return B(A3(_8y,_fp,_fh,_ft));})));});return new F(function(){return A3(_9T,_fl,_fu,_fq);});};return B(A3(_9X,B(_9P(_fn)),_fr,_fi));});return B(A3(_9V,_fn,_fo,_fk));});return new T2(0,new T(function(){return B(A3(_9T,_fl,_fh,_fj));}),_fm);},_fv=function(_fw,_fx,_fy,_fz){var _fA=E(_fy),_fB=E(_fz),_fC=B(_ff(_fx,_fA.a,_fA.b,_fB.a,_fB.b));return new T2(0,_fC.a,_fC.b);},_fD=function(_fE,_fF){var _fG=new T(function(){return B(_8u(new T(function(){return E(E(_fE).c);})));}),_fH=new T(function(){return B(A2(_dE,E(_fE).a,new T(function(){return B(A2(_9I,B(_8w(_fG)),_dB));})));});return new T2(0,new T(function(){return B(A2(_8C,_fG,_fF));}),_fH);},_fI=function(_fJ,_fK,_fL){var _fM=B(_fD(_fK,_fL));return new T2(0,_fM.a,_fM.b);},_fN=function(_fO,_fP,_fQ){var _fR=new T(function(){return B(_8u(new T(function(){return E(E(_fO).c);})));}),_fS=new T(function(){return B(_8w(_fR));}),_fT=new T(function(){var _fU=new T(function(){var _fV=new T(function(){return B(A3(_9T,_fR,new T(function(){return B(A2(_9I,_fS,_as));}),new T(function(){return B(A3(_8y,_fS,_fP,_fP));})));});return B(A2(_7Y,_fS,_fV));});return B(A3(_9X,B(_9P(E(_fO).a)),function(_fW){return new F(function(){return A3(_8y,_fS,_fW,_fU);});},_fQ));}),_fX=new T(function(){return B(A3(_9T,_fR,new T(function(){return B(A2(_9I,_fS,_as));}),_fP));});return new T2(0,_fX,_fT);},_fY=function(_fZ,_g0,_g1){var _g2=E(_g1),_g3=B(_fN(_g0,_g2.a,_g2.b));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6){return new T4(0,_g5,function(_fe,_fd){return new F(function(){return _fv(_g5,_g6,_fe,_fd);});},function(_fd){return new F(function(){return _fY(_g5,_g6,_fd);});},function(_fd){return new F(function(){return _fI(_g5,_g6,_fd);});});},_g7=function(_g8,_g9,_ga,_gb,_gc){var _gd=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_g8).c);})));})));}),_ge=new T(function(){var _gf=E(_g8).a,_gg=new T(function(){var _gh=function(_gi,_gj){return new F(function(){return A3(_7W,_gd,new T(function(){return B(A3(_8y,_gd,_g9,_gj));}),new T(function(){return B(A3(_8y,_gd,_gi,_gb));}));});};return B(A3(_9X,B(_9P(_gf)),_gh,_ga));});return B(A3(_9V,_gf,_gg,_gc));});return new T2(0,new T(function(){return B(A3(_8y,_gd,_g9,_gb));}),_ge);},_gk=function(_gl,_gm,_gn){var _go=E(_gm),_gp=E(_gn),_gq=B(_g7(_gl,_go.a,_go.b,_gp.a,_gp.b));return new T2(0,_gq.a,_gq.b);},_gr=function(_gs,_gt,_gu,_gv,_gw){var _gx=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_gs).c);})));})));}),_gy=new T(function(){var _gz=E(_gs).a,_gA=new T(function(){return B(A3(_9X,B(_9P(_gz)),new T(function(){return B(_7W(_gx));}),_gu));});return B(A3(_9V,_gz,_gA,_gw));});return new T2(0,new T(function(){return B(A3(_7W,_gx,_gt,_gv));}),_gy);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_gr(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL){var _gM=B(_gN(_gJ));return new F(function(){return A3(_7W,_gM,_gK,new T(function(){return B(A2(_7Y,_gM,_gL));}));});},_gO=function(_gP){return E(E(_gP).e);},_gQ=function(_gR){return E(E(_gR).f);},_gS=function(_gT,_gU,_gV){var _gW=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_gT).c);})));})));}),_gX=new T(function(){var _gY=new T(function(){return B(A2(_gQ,_gW,_gU));});return B(A3(_9X,B(_9P(E(_gT).a)),function(_gZ){return new F(function(){return A3(_8y,_gW,_gZ,_gY);});},_gV));});return new T2(0,new T(function(){return B(A2(_gO,_gW,_gU));}),_gX);},_h0=function(_h1,_h2){var _h3=E(_h2),_h4=B(_gS(_h1,_h3.a,_h3.b));return new T2(0,_h4.a,_h4.b);},_h5=function(_h6,_h7){var _h8=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_h6).c);})));})));}),_h9=new T(function(){return B(A2(_dE,E(_h6).a,new T(function(){return B(A2(_9I,_h8,_dB));})));});return new T2(0,new T(function(){return B(A2(_9I,_h8,_h7));}),_h9);},_ha=function(_hb,_hc){var _hd=B(_h5(_hb,_hc));return new T2(0,_hd.a,_hd.b);},_he=function(_hf,_hg,_hh){var _hi=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_hf).c);})));})));}),_hj=new T(function(){return B(A3(_9X,B(_9P(E(_hf).a)),new T(function(){return B(_7Y(_hi));}),_hh));});return new T2(0,new T(function(){return B(A2(_7Y,_hi,_hg));}),_hj);},_hk=function(_hl,_hm){var _hn=E(_hm),_ho=B(_he(_hl,_hn.a,_hn.b));return new T2(0,_ho.a,_ho.b);},_hp=function(_hq,_hr){var _hs=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_hq).c);})));})));}),_ht=new T(function(){return B(A2(_dE,E(_hq).a,new T(function(){return B(A2(_9I,_hs,_dB));})));});return new T2(0,new T(function(){return B(A2(_gQ,_hs,_hr));}),_ht);},_hu=function(_hv,_hw){var _hx=B(_hp(_hv,E(_hw).a));return new T2(0,_hx.a,_hx.b);},_gN=function(_hy){return {_:0,a:function(_fe,_fd){return new F(function(){return _gB(_hy,_fe,_fd);});},b:function(_fe,_fd){return new F(function(){return _gI(_hy,_fe,_fd);});},c:function(_fe,_fd){return new F(function(){return _gk(_hy,_fe,_fd);});},d:function(_fd){return new F(function(){return _hk(_hy,_fd);});},e:function(_fd){return new F(function(){return _h0(_hy,_fd);});},f:function(_fd){return new F(function(){return _hu(_hy,_fd);});},g:function(_fd){return new F(function(){return _ha(_hy,_fd);});}};},_hz=function(_hA){var _hB=new T3(0,_9G,_9M,_hA),_hC=new T(function(){return B(_fa(new T(function(){return B(_g4(new T(function(){return B(_gN(_hB));}),_hB));}),_hB));}),_hD=new T(function(){return B(_8w(new T(function(){return B(_8u(_hA));})));});return function(_hE){var _hF=E(_hE),_hG=B(_9K(_hD));return E(B(_8M(_hC,new T2(0,_hF.a,_hG.a),new T2(0,_hF.b,_hG.b),new T2(0,_hF.c,_hG.c))).b);};},_hH=new T(function(){return B(_hz(_8t));}),_hI=function(_hJ,_hK){var _hL=E(_hK);return (_hL._==0)?__Z:new T2(1,_hJ,new T2(1,_hL.a,new T(function(){return B(_hI(_hJ,_hL.b));})));},_hM=new T(function(){var _hN=B(A1(_hH,_9g));return new T2(1,_hN.a,new T(function(){return B(_hI(_1F,new T2(1,_hN.b,new T2(1,_hN.c,_T))));}));}),_hO=new T1(1,_hM),_hP=new T2(1,_hO,_1K),_hQ=new T(function(){return B(unCStr("vec3("));}),_hR=new T1(0,_hQ),_hS=new T2(1,_hR,_hP),_hT=new T(function(){return toJSStr(B(_97(_1D,_11,_hS)));}),_hU=function(_hV,_hW){while(1){var _hX=E(_hV);if(!_hX._){return E(_hW);}else{var _hY=_hW+1|0;_hV=_hX.b;_hW=_hY;continue;}}},_hZ=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_i0=new T(function(){return B(err(_hZ));}),_i1=new T(function(){return B(unCStr("Negative exponent"));}),_i2=new T(function(){return B(err(_i1));}),_i3=function(_i4,_i5,_i6){while(1){if(!(_i5%2)){var _i7=_i4*_i4,_i8=quot(_i5,2);_i4=_i7;_i5=_i8;continue;}else{var _i9=E(_i5);if(_i9==1){return _i4*_i6;}else{var _i7=_i4*_i4,_ia=_i4*_i6;_i4=_i7;_i5=quot(_i9-1|0,2);_i6=_ia;continue;}}}},_ib=function(_ic,_id){while(1){if(!(_id%2)){var _ie=_ic*_ic,_if=quot(_id,2);_ic=_ie;_id=_if;continue;}else{var _ig=E(_id);if(_ig==1){return E(_ic);}else{return new F(function(){return _i3(_ic*_ic,quot(_ig-1|0,2),_ic);});}}}},_ih=new T(function(){var _ii=eval("angleCount"),_ij=Number(_ii);return jsTrunc(_ij);}),_ik=new T(function(){return E(_ih);}),_il=function(_im,_in){if(_im<=_in){var _io=function(_ip){return new T2(1,_ip,new T(function(){if(_ip!=_in){return B(_io(_ip+1|0));}else{return __Z;}}));};return new F(function(){return _io(_im);});}else{return __Z;}},_iq=1,_ir=0,_is=new T3(0,_ir,_iq,_ir),_it=new T(function(){return 6.283185307179586/E(_ik);}),_iu=function(_iv){var _iw=E(_iv);return new F(function(){return _7x(_iw.a,_iw.b);});},_ix=function(_iy){return 1/E(_iy);},_iz=function(_iA){var _iB=E(_iA),_iC=E(_iB);return (_iC==0)?E(_7w):(_iC<=0)? -_iC:E(_iB);},_iD=function(_iE){var _iF=E(_iE);if(!_iF._){return _iF.a;}else{return new F(function(){return I_toNumber(_iF.a);});}},_iG=function(_iH){return new F(function(){return _iD(_iH);});},_iI=1,_iJ=-1,_iK=function(_iL){var _iM=E(_iL);return (_iM<=0)?(_iM>=0)?E(_iM):E(_iJ):E(_iI);},_iN=function(_iO,_iP){return E(_iO)-E(_iP);},_iQ=function(_iR){return  -E(_iR);},_iS=function(_iT,_iU){return E(_iT)+E(_iU);},_iV=function(_iW,_iX){return E(_iW)*E(_iX);},_iY={_:0,a:_iS,b:_iN,c:_iV,d:_iQ,e:_iz,f:_iK,g:_iG},_iZ=function(_j0,_j1){return E(_j0)/E(_j1);},_j2=new T4(0,_iY,_iZ,_ix,_iu),_j3=function(_j4,_j5){return (E(_j4)!=E(_j5))?true:false;},_j6=function(_j7,_j8){return E(_j7)==E(_j8);},_j9=new T2(0,_j6,_j3),_ja=function(_jb,_jc){return E(_jb)<E(_jc);},_jd=function(_je,_jf){return E(_je)<=E(_jf);},_jg=function(_jh,_ji){return E(_jh)>E(_ji);},_jj=function(_jk,_jl){return E(_jk)>=E(_jl);},_jm=function(_jn,_jo){var _jp=E(_jn),_jq=E(_jo);return (_jp>=_jq)?(_jp!=_jq)?2:1:0;},_jr=function(_js,_jt){var _ju=E(_js),_jv=E(_jt);return (_ju>_jv)?E(_ju):E(_jv);},_jw=function(_jx,_jy){var _jz=E(_jx),_jA=E(_jy);return (_jz>_jA)?E(_jA):E(_jz);},_jB={_:0,a:_j9,b:_jm,c:_ja,d:_jd,e:_jg,f:_jj,g:_jr,h:_jw},_jC=new T(function(){return E(_ik)-1;}),_jD=new T1(0,1),_jE=function(_jF,_jG){var _jH=E(_jG),_jI=new T(function(){var _jJ=B(_8w(_jF)),_jK=B(_jE(_jF,B(A3(_7W,_jJ,_jH,new T(function(){return B(A2(_9I,_jJ,_jD));})))));return new T2(1,_jK.a,_jK.b);});return new T2(0,_jH,_jI);},_jL=function(_jM){return E(E(_jM).d);},_jN=new T1(0,2),_jO=function(_jP,_jQ){var _jR=E(_jQ);if(!_jR._){return __Z;}else{var _jS=_jR.a;return (!B(A1(_jP,_jS)))?__Z:new T2(1,_jS,new T(function(){return B(_jO(_jP,_jR.b));}));}},_jT=function(_jU,_jV,_jW,_jX){var _jY=B(_jE(_jV,_jW)),_jZ=new T(function(){var _k0=B(_8w(_jV)),_k1=new T(function(){return B(A3(_9T,_jV,new T(function(){return B(A2(_9I,_k0,_jD));}),new T(function(){return B(A2(_9I,_k0,_jN));})));});return B(A3(_7W,_k0,_jX,_k1));});return new F(function(){return _jO(function(_k2){return new F(function(){return A3(_jL,_jU,_k2,_jZ);});},new T2(1,_jY.a,_jY.b));});},_k3=new T(function(){return B(_jT(_jB,_j2,_ir,_jC));}),_k4=function(_k5,_k6,_k7,_k8,_k9){var _ka=function(_kb){var _kc=E(_it),_kd=2+_kb|0,_ke=_kd-1|0,_kf=new T(function(){return B(_il(0,_kd-1|0));}),_kg=E(_k3);if(!_kg._){return _kc*0;}else{var _kh=_kg.a,_ki=new T(function(){return B(A1(_k5,new T(function(){return 6.283185307179586*E(_kh)/E(_ik);})));}),_kj=new T(function(){return B(A1(_k5,new T(function(){return 6.283185307179586*(E(_kh)+1)/E(_ik);})));}),_kk=function(_kl,_km){while(1){var _kn=B((function(_ko,_kp){var _kq=E(_ko);if(!_kq._){return E(_kp);}else{var _kr=_kq.b,_ks=E(_kq.a);if(_ks>=0){var _kt=function(_ku){var _kv=_ke-_ks|0;if(_kv>=0){var _kw=E(_kv);return (_kw==0)?_kp+_ku:_kp+_ku*B(_ib(E(_kj),_kw));}else{return E(_i2);}},_kx=E(_ks);if(!_kx){_kl=_kr;_km=B(_kt(1));return __continue;}else{var _ky=E(_ki),_kz=function(_kA,_kB){while(1){var _kC=B((function(_kD,_kE){var _kF=E(_kD);if(!_kF._){return E(_kE);}else{var _kG=_kF.b,_kH=E(_kF.a);if(_kH>=0){var _kI=function(_kJ){var _kK=_ke-_kH|0;if(_kK>=0){var _kL=E(_kK);return (_kL==0)?_kE+_kJ:_kE+_kJ*B(_ib(E(_kj),_kL));}else{return E(_i2);}},_kM=E(_kH);if(!_kM){_kA=_kG;_kB=B(_kI(1));return __continue;}else{_kA=_kG;_kB=B(_kI(B(_ib(_ky,_kM))));return __continue;}}else{return E(_i2);}}})(_kA,_kB));if(_kC!=__continue){return _kC;}}};return new F(function(){return _kz(_kr,B(_kt(B(_ib(_ky,_kx)))));});}}else{return E(_i2);}}})(_kl,_km));if(_kn!=__continue){return _kn;}}},_kN=(2+_kb)*(1+_kb),_kO=function(_kP,_kQ){while(1){var _kR=B((function(_kS,_kT){var _kU=E(_kS);if(!_kU._){return E(_kT);}else{var _kV=_kU.a,_kW=new T(function(){return B(A1(_k5,new T(function(){return 6.283185307179586*E(_kV)/E(_ik);})));}),_kX=new T(function(){return B(A1(_k5,new T(function(){return 6.283185307179586*(E(_kV)+1)/E(_ik);})));}),_kY=function(_kZ,_l0){while(1){var _l1=B((function(_l2,_l3){var _l4=E(_l2);if(!_l4._){return E(_l3);}else{var _l5=_l4.b,_l6=E(_l4.a);if(_l6>=0){var _l7=function(_l8){var _l9=_ke-_l6|0;if(_l9>=0){var _la=E(_l9);return (_la==0)?_l3+_l8:_l3+_l8*B(_ib(E(_kX),_la));}else{return E(_i2);}},_lb=E(_l6);if(!_lb){_kZ=_l5;_l0=B(_l7(1));return __continue;}else{var _lc=E(_kW),_ld=function(_le,_lf){while(1){var _lg=B((function(_lh,_li){var _lj=E(_lh);if(!_lj._){return E(_li);}else{var _lk=_lj.b,_ll=E(_lj.a);if(_ll>=0){var _lm=function(_ln){var _lo=_ke-_ll|0;if(_lo>=0){var _lp=E(_lo);return (_lp==0)?_li+_ln:_li+_ln*B(_ib(E(_kX),_lp));}else{return E(_i2);}},_lq=E(_ll);if(!_lq){_le=_lk;_lf=B(_lm(1));return __continue;}else{_le=_lk;_lf=B(_lm(B(_ib(_lc,_lq))));return __continue;}}else{return E(_i2);}}})(_le,_lf));if(_lg!=__continue){return _lg;}}};return new F(function(){return _ld(_l5,B(_l7(B(_ib(_lc,_lb)))));});}}else{return E(_i2);}}})(_kZ,_l0));if(_l1!=__continue){return _l1;}}},_lr=_kT+B(_kY(_kf,0))/_kN;_kP=_kU.b;_kQ=_lr;return __continue;}})(_kP,_kQ));if(_kR!=__continue){return _kR;}}};return _kc*B(_kO(_kg.b,B(_kk(_kf,0))/_kN));}},_ls=new T(function(){return 1/(B(_ka(1))*E(_k6));});return new T6(0,_k5,_k7,_k8,_k9,_is,new T2(0,new T3(0,_ls,_ls,_ls),new T(function(){return 1/(B(_ka(3))*E(_k6));})));},_lt=1.2,_lu=-0.2,_lv=1,_lw=0,_lx=new T3(0,_lu,_lw,_lv),_ly=new T2(0,_lx,_lw),_lz=0.5,_lA=-0.8,_lB=new T3(0,_lA,_lz,_lw),_lC=new T2(0,_lB,_lw),_lD=4.0e-2,_lE=function(_lF){return E(_lD);},_lG=new T3(0,_lw,_lw,_lv),_lH=new T(function(){var _lI=B(_k4(_lE,_lt,_lC,_ly,_lG));return new T6(0,_lI.a,_lI.b,_lI.c,_lI.d,_lI.e,_lI.f);}),_lJ=0,_lK=1.3,_lL=new T3(0,_lK,_lw,_lw),_lM=new T2(0,_lL,_lw),_lN=function(_lO){var _lP=I_decodeDouble(_lO);return new T2(0,new T1(1,_lP.b),_lP.a);},_lQ=function(_lR){return new T1(0,_lR);},_lS=function(_lT){var _lU=hs_intToInt64(2147483647),_lV=hs_leInt64(_lT,_lU);if(!_lV){return new T1(1,I_fromInt64(_lT));}else{var _lW=hs_intToInt64(-2147483648),_lX=hs_geInt64(_lT,_lW);if(!_lX){return new T1(1,I_fromInt64(_lT));}else{var _lY=hs_int64ToInt(_lT);return new F(function(){return _lQ(_lY);});}}},_lZ=new T(function(){var _m0=newByteArr(256),_m1=_m0,_=_m1["v"]["i8"][0]=8,_m2=function(_m3,_m4,_m5,_){while(1){if(_m5>=256){if(_m3>=256){return E(_);}else{var _m6=imul(2,_m3)|0,_m7=_m4+1|0,_m8=_m3;_m3=_m6;_m4=_m7;_m5=_m8;continue;}}else{var _=_m1["v"]["i8"][_m5]=_m4,_m8=_m5+_m3|0;_m5=_m8;continue;}}},_=B(_m2(2,0,1,_));return _m1;}),_m9=function(_ma,_mb){var _mc=hs_int64ToInt(_ma),_md=E(_lZ),_me=_md["v"]["i8"][(255&_mc>>>0)>>>0&4294967295];if(_mb>_me){if(_me>=8){var _mf=hs_uncheckedIShiftRA64(_ma,8),_mg=function(_mh,_mi){while(1){var _mj=B((function(_mk,_ml){var _mm=hs_int64ToInt(_mk),_mn=_md["v"]["i8"][(255&_mm>>>0)>>>0&4294967295];if(_ml>_mn){if(_mn>=8){var _mo=hs_uncheckedIShiftRA64(_mk,8),_mp=_ml-8|0;_mh=_mo;_mi=_mp;return __continue;}else{return new T2(0,new T(function(){var _mq=hs_uncheckedIShiftRA64(_mk,_mn);return B(_lS(_mq));}),_ml-_mn|0);}}else{return new T2(0,new T(function(){var _mr=hs_uncheckedIShiftRA64(_mk,_ml);return B(_lS(_mr));}),0);}})(_mh,_mi));if(_mj!=__continue){return _mj;}}};return new F(function(){return _mg(_mf,_mb-8|0);});}else{return new T2(0,new T(function(){var _ms=hs_uncheckedIShiftRA64(_ma,_me);return B(_lS(_ms));}),_mb-_me|0);}}else{return new T2(0,new T(function(){var _mt=hs_uncheckedIShiftRA64(_ma,_mb);return B(_lS(_mt));}),0);}},_mu=function(_mv){var _mw=hs_intToInt64(_mv);return E(_mw);},_mx=function(_my){var _mz=E(_my);if(!_mz._){return new F(function(){return _mu(_mz.a);});}else{return new F(function(){return I_toInt64(_mz.a);});}},_mA=function(_mB){return I_toInt(_mB)>>>0;},_mC=function(_mD){var _mE=E(_mD);if(!_mE._){return _mE.a>>>0;}else{return new F(function(){return _mA(_mE.a);});}},_mF=function(_mG){var _mH=B(_lN(_mG)),_mI=_mH.a,_mJ=_mH.b;if(_mJ<0){var _mK=function(_mL){if(!_mL){return new T2(0,E(_mI),B(_4I(_30, -_mJ)));}else{var _mM=B(_m9(B(_mx(_mI)), -_mJ));return new T2(0,E(_mM.a),B(_4I(_30,_mM.b)));}};if(!((B(_mC(_mI))&1)>>>0)){return new F(function(){return _mK(1);});}else{return new F(function(){return _mK(0);});}}else{return new T2(0,B(_4I(_mI,_mJ)),_30);}},_mN=function(_mO){var _mP=B(_mF(E(_mO)));return new T2(0,E(_mP.a),E(_mP.b));},_mQ=new T3(0,_iY,_jB,_mN),_mR=function(_mS){return E(E(_mS).a);},_mT=function(_mU){return E(E(_mU).a);},_mV=function(_mW){return new F(function(){return _il(E(_mW),2147483647);});},_mX=function(_mY,_mZ,_n0){if(_n0<=_mZ){var _n1=new T(function(){var _n2=_mZ-_mY|0,_n3=function(_n4){return (_n4>=(_n0-_n2|0))?new T2(1,_n4,new T(function(){return B(_n3(_n4+_n2|0));})):new T2(1,_n4,_T);};return B(_n3(_mZ));});return new T2(1,_mY,_n1);}else{return (_n0<=_mY)?new T2(1,_mY,_T):__Z;}},_n5=function(_n6,_n7,_n8){if(_n8>=_n7){var _n9=new T(function(){var _na=_n7-_n6|0,_nb=function(_nc){return (_nc<=(_n8-_na|0))?new T2(1,_nc,new T(function(){return B(_nb(_nc+_na|0));})):new T2(1,_nc,_T);};return B(_nb(_n7));});return new T2(1,_n6,_n9);}else{return (_n8>=_n6)?new T2(1,_n6,_T):__Z;}},_nd=function(_ne,_nf){if(_nf<_ne){return new F(function(){return _mX(_ne,_nf,-2147483648);});}else{return new F(function(){return _n5(_ne,_nf,2147483647);});}},_ng=function(_nh,_ni){return new F(function(){return _nd(E(_nh),E(_ni));});},_nj=function(_nk,_nl,_nm){if(_nl<_nk){return new F(function(){return _mX(_nk,_nl,_nm);});}else{return new F(function(){return _n5(_nk,_nl,_nm);});}},_nn=function(_no,_np,_nq){return new F(function(){return _nj(E(_no),E(_np),E(_nq));});},_nr=function(_ns,_nt){return new F(function(){return _il(E(_ns),E(_nt));});},_nu=function(_nv){return E(_nv);},_nw=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_nx=new T(function(){return B(err(_nw));}),_ny=function(_nz){var _nA=E(_nz);return (_nA==(-2147483648))?E(_nx):_nA-1|0;},_nB=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_nC=new T(function(){return B(err(_nB));}),_nD=function(_nE){var _nF=E(_nE);return (_nF==2147483647)?E(_nC):_nF+1|0;},_nG={_:0,a:_nD,b:_ny,c:_nu,d:_nu,e:_mV,f:_ng,g:_nr,h:_nn},_nH=function(_nI,_nJ){if(_nI<=0){if(_nI>=0){return new F(function(){return quot(_nI,_nJ);});}else{if(_nJ<=0){return new F(function(){return quot(_nI,_nJ);});}else{return quot(_nI+1|0,_nJ)-1|0;}}}else{if(_nJ>=0){if(_nI>=0){return new F(function(){return quot(_nI,_nJ);});}else{if(_nJ<=0){return new F(function(){return quot(_nI,_nJ);});}else{return quot(_nI+1|0,_nJ)-1|0;}}}else{return quot(_nI-1|0,_nJ)-1|0;}}},_nK=0,_nL=new T(function(){return B(_45(_nK));}),_nM=new T(function(){return die(_nL);}),_nN=function(_nO,_nP){var _nQ=E(_nP);switch(_nQ){case -1:var _nR=E(_nO);if(_nR==(-2147483648)){return E(_nM);}else{return new F(function(){return _nH(_nR,-1);});}break;case 0:return E(_49);default:return new F(function(){return _nH(_nO,_nQ);});}},_nS=function(_nT,_nU){return new F(function(){return _nN(E(_nT),E(_nU));});},_nV=0,_nW=new T2(0,_nM,_nV),_nX=function(_nY,_nZ){var _o0=E(_nY),_o1=E(_nZ);switch(_o1){case -1:var _o2=E(_o0);if(_o2==(-2147483648)){return E(_nW);}else{if(_o2<=0){if(_o2>=0){var _o3=quotRemI(_o2,-1);return new T2(0,_o3.a,_o3.b);}else{var _o4=quotRemI(_o2,-1);return new T2(0,_o4.a,_o4.b);}}else{var _o5=quotRemI(_o2-1|0,-1);return new T2(0,_o5.a-1|0,(_o5.b+(-1)|0)+1|0);}}break;case 0:return E(_49);default:if(_o0<=0){if(_o0>=0){var _o6=quotRemI(_o0,_o1);return new T2(0,_o6.a,_o6.b);}else{if(_o1<=0){var _o7=quotRemI(_o0,_o1);return new T2(0,_o7.a,_o7.b);}else{var _o8=quotRemI(_o0+1|0,_o1);return new T2(0,_o8.a-1|0,(_o8.b+_o1|0)-1|0);}}}else{if(_o1>=0){if(_o0>=0){var _o9=quotRemI(_o0,_o1);return new T2(0,_o9.a,_o9.b);}else{if(_o1<=0){var _oa=quotRemI(_o0,_o1);return new T2(0,_oa.a,_oa.b);}else{var _ob=quotRemI(_o0+1|0,_o1);return new T2(0,_ob.a-1|0,(_ob.b+_o1|0)-1|0);}}}else{var _oc=quotRemI(_o0-1|0,_o1);return new T2(0,_oc.a-1|0,(_oc.b+_o1|0)+1|0);}}}},_od=function(_oe,_of){var _og=_oe%_of;if(_oe<=0){if(_oe>=0){return E(_og);}else{if(_of<=0){return E(_og);}else{var _oh=E(_og);return (_oh==0)?0:_oh+_of|0;}}}else{if(_of>=0){if(_oe>=0){return E(_og);}else{if(_of<=0){return E(_og);}else{var _oi=E(_og);return (_oi==0)?0:_oi+_of|0;}}}else{var _oj=E(_og);return (_oj==0)?0:_oj+_of|0;}}},_ok=function(_ol,_om){var _on=E(_om);switch(_on){case -1:return E(_nV);case 0:return E(_49);default:return new F(function(){return _od(E(_ol),_on);});}},_oo=function(_op,_oq){var _or=E(_op),_os=E(_oq);switch(_os){case -1:var _ot=E(_or);if(_ot==(-2147483648)){return E(_nM);}else{return new F(function(){return quot(_ot,-1);});}break;case 0:return E(_49);default:return new F(function(){return quot(_or,_os);});}},_ou=function(_ov,_ow){var _ox=E(_ov),_oy=E(_ow);switch(_oy){case -1:var _oz=E(_ox);if(_oz==(-2147483648)){return E(_nW);}else{var _oA=quotRemI(_oz,-1);return new T2(0,_oA.a,_oA.b);}break;case 0:return E(_49);default:var _oB=quotRemI(_ox,_oy);return new T2(0,_oB.a,_oB.b);}},_oC=function(_oD,_oE){var _oF=E(_oE);switch(_oF){case -1:return E(_nV);case 0:return E(_49);default:return E(_oD)%_oF;}},_oG=function(_oH){return new F(function(){return _lQ(E(_oH));});},_oI=function(_oJ){return new T2(0,E(B(_lQ(E(_oJ)))),E(_jD));},_oK=function(_oL,_oM){return imul(E(_oL),E(_oM))|0;},_oN=function(_oO,_oP){return E(_oO)+E(_oP)|0;},_oQ=function(_oR,_oS){return E(_oR)-E(_oS)|0;},_oT=function(_oU){var _oV=E(_oU);return (_oV<0)? -_oV:E(_oV);},_oW=function(_oX){return new F(function(){return _4m(_oX);});},_oY=function(_oZ){return  -E(_oZ);},_p0=-1,_p1=0,_p2=1,_p3=function(_p4){var _p5=E(_p4);return (_p5>=0)?(E(_p5)==0)?E(_p1):E(_p2):E(_p0);},_p6={_:0,a:_oN,b:_oQ,c:_oK,d:_oY,e:_oT,f:_p3,g:_oW},_p7=function(_p8,_p9){return E(_p8)==E(_p9);},_pa=function(_pb,_pc){return E(_pb)!=E(_pc);},_pd=new T2(0,_p7,_pa),_pe=function(_pf,_pg){var _ph=E(_pf),_pi=E(_pg);return (_ph>_pi)?E(_ph):E(_pi);},_pj=function(_pk,_pl){var _pm=E(_pk),_pn=E(_pl);return (_pm>_pn)?E(_pn):E(_pm);},_po=function(_pp,_pq){return (_pp>=_pq)?(_pp!=_pq)?2:1:0;},_pr=function(_ps,_pt){return new F(function(){return _po(E(_ps),E(_pt));});},_pu=function(_pv,_pw){return E(_pv)>=E(_pw);},_px=function(_py,_pz){return E(_py)>E(_pz);},_pA=function(_pB,_pC){return E(_pB)<=E(_pC);},_pD=function(_pE,_pF){return E(_pE)<E(_pF);},_pG={_:0,a:_pd,b:_pr,c:_pD,d:_pA,e:_px,f:_pu,g:_pe,h:_pj},_pH=new T3(0,_p6,_pG,_oI),_pI={_:0,a:_pH,b:_nG,c:_oo,d:_oC,e:_nS,f:_ok,g:_ou,h:_nX,i:_oG},_pJ=new T1(0,2),_pK=function(_pL,_pM){while(1){var _pN=E(_pL);if(!_pN._){var _pO=_pN.a,_pP=E(_pM);if(!_pP._){var _pQ=_pP.a;if(!(imul(_pO,_pQ)|0)){return new T1(0,imul(_pO,_pQ)|0);}else{_pL=new T1(1,I_fromInt(_pO));_pM=new T1(1,I_fromInt(_pQ));continue;}}else{_pL=new T1(1,I_fromInt(_pO));_pM=_pP;continue;}}else{var _pR=E(_pM);if(!_pR._){_pL=_pN;_pM=new T1(1,I_fromInt(_pR.a));continue;}else{return new T1(1,I_mul(_pN.a,_pR.a));}}}},_pS=function(_pT,_pU,_pV){while(1){if(!(_pU%2)){var _pW=B(_pK(_pT,_pT)),_pX=quot(_pU,2);_pT=_pW;_pU=_pX;continue;}else{var _pY=E(_pU);if(_pY==1){return new F(function(){return _pK(_pT,_pV);});}else{var _pW=B(_pK(_pT,_pT)),_pZ=B(_pK(_pT,_pV));_pT=_pW;_pU=quot(_pY-1|0,2);_pV=_pZ;continue;}}}},_q0=function(_q1,_q2){while(1){if(!(_q2%2)){var _q3=B(_pK(_q1,_q1)),_q4=quot(_q2,2);_q1=_q3;_q2=_q4;continue;}else{var _q5=E(_q2);if(_q5==1){return E(_q1);}else{return new F(function(){return _pS(B(_pK(_q1,_q1)),quot(_q5-1|0,2),_q1);});}}}},_q6=function(_q7){return E(E(_q7).a);},_q8=function(_q9){return E(E(_q9).b);},_qa=function(_qb){return E(E(_qb).c);},_qc=function(_qd){return E(E(_qd).a);},_qe=new T1(0,0),_qf=function(_qg){return E(E(_qg).d);},_qh=function(_qi,_qj){var _qk=B(_mR(_qi)),_ql=new T(function(){return B(_mT(_qk));}),_qm=new T(function(){return B(A3(_qf,_qi,_qj,new T(function(){return B(A2(_9I,_ql,_jN));})));});return new F(function(){return A3(_qc,B(_q6(B(_q8(_qk)))),_qm,new T(function(){return B(A2(_9I,_ql,_qe));}));});},_qn=new T(function(){return B(unCStr("Negative exponent"));}),_qo=new T(function(){return B(err(_qn));}),_qp=function(_qq){return E(E(_qq).c);},_qr=function(_qs,_qt,_qu,_qv){var _qw=B(_mR(_qt)),_qx=new T(function(){return B(_mT(_qw));}),_qy=B(_q8(_qw));if(!B(A3(_qa,_qy,_qv,new T(function(){return B(A2(_9I,_qx,_qe));})))){if(!B(A3(_qc,B(_q6(_qy)),_qv,new T(function(){return B(A2(_9I,_qx,_qe));})))){var _qz=new T(function(){return B(A2(_9I,_qx,_jN));}),_qA=new T(function(){return B(A2(_9I,_qx,_jD));}),_qB=B(_q6(_qy)),_qC=function(_qD,_qE,_qF){while(1){var _qG=B((function(_qH,_qI,_qJ){if(!B(_qh(_qt,_qI))){if(!B(A3(_qc,_qB,_qI,_qA))){var _qK=new T(function(){return B(A3(_qp,_qt,new T(function(){return B(A3(_8A,_qx,_qI,_qA));}),_qz));});_qD=new T(function(){return B(A3(_8y,_qs,_qH,_qH));});_qE=_qK;_qF=new T(function(){return B(A3(_8y,_qs,_qH,_qJ));});return __continue;}else{return new F(function(){return A3(_8y,_qs,_qH,_qJ);});}}else{var _qL=_qJ;_qD=new T(function(){return B(A3(_8y,_qs,_qH,_qH));});_qE=new T(function(){return B(A3(_qp,_qt,_qI,_qz));});_qF=_qL;return __continue;}})(_qD,_qE,_qF));if(_qG!=__continue){return _qG;}}},_qM=function(_qN,_qO){while(1){var _qP=B((function(_qQ,_qR){if(!B(_qh(_qt,_qR))){if(!B(A3(_qc,_qB,_qR,_qA))){var _qS=new T(function(){return B(A3(_qp,_qt,new T(function(){return B(A3(_8A,_qx,_qR,_qA));}),_qz));});return new F(function(){return _qC(new T(function(){return B(A3(_8y,_qs,_qQ,_qQ));}),_qS,_qQ);});}else{return E(_qQ);}}else{_qN=new T(function(){return B(A3(_8y,_qs,_qQ,_qQ));});_qO=new T(function(){return B(A3(_qp,_qt,_qR,_qz));});return __continue;}})(_qN,_qO));if(_qP!=__continue){return _qP;}}};return new F(function(){return _qM(_qu,_qv);});}else{return new F(function(){return A2(_9I,_qs,_jD);});}}else{return E(_qo);}},_qT=new T(function(){return B(err(_qn));}),_qU=function(_qV,_qW){var _qX=B(_lN(_qW)),_qY=_qX.a,_qZ=_qX.b,_r0=new T(function(){return B(_mT(new T(function(){return B(_mR(_qV));})));});if(_qZ<0){var _r1= -_qZ;if(_r1>=0){var _r2=E(_r1);if(!_r2){var _r3=E(_jD);}else{var _r3=B(_q0(_pJ,_r2));}if(!B(_4e(_r3,_4H))){var _r4=B(_4y(_qY,_r3));return new T2(0,new T(function(){return B(A2(_9I,_r0,_r4.a));}),new T(function(){return B(_4a(_r4.b,_qZ));}));}else{return E(_49);}}else{return E(_qT);}}else{var _r5=new T(function(){var _r6=new T(function(){return B(_qr(_r0,_pI,new T(function(){return B(A2(_9I,_r0,_pJ));}),_qZ));});return B(A3(_8y,_r0,new T(function(){return B(A2(_9I,_r0,_qY));}),_r6));});return new T2(0,_r5,_7w);}},_r7=function(_r8,_r9){var _ra=B(_qU(_r8,E(_r9))),_rb=_ra.a;if(E(_ra.b)<=0){return E(_rb);}else{var _rc=B(_mT(B(_mR(_r8))));return new F(function(){return A3(_7W,_rc,_rb,new T(function(){return B(A2(_9I,_rc,_30));}));});}},_rd=function(_re,_rf){var _rg=B(_qU(_re,E(_rf))),_rh=_rg.a;if(E(_rg.b)>=0){return E(_rh);}else{var _ri=B(_mT(B(_mR(_re))));return new F(function(){return A3(_8A,_ri,_rh,new T(function(){return B(A2(_9I,_ri,_30));}));});}},_rj=function(_rk,_rl){var _rm=B(_qU(_rk,E(_rl)));return new T2(0,_rm.a,_rm.b);},_rn=function(_ro,_rp){var _rq=B(_qU(_ro,_rp)),_rr=_rq.a,_rs=E(_rq.b),_rt=new T(function(){var _ru=B(_mT(B(_mR(_ro))));if(_rs>=0){return B(A3(_7W,_ru,_rr,new T(function(){return B(A2(_9I,_ru,_30));})));}else{return B(A3(_8A,_ru,_rr,new T(function(){return B(A2(_9I,_ru,_30));})));}}),_rv=function(_rw){var _rx=_rw-0.5;return (_rx>=0)?(E(_rx)==0)?(!B(_qh(_ro,_rr)))?E(_rt):E(_rr):E(_rt):E(_rr);},_ry=E(_rs);if(!_ry){return new F(function(){return _rv(0);});}else{if(_ry<=0){var _rz= -_ry-0.5;return (_rz>=0)?(E(_rz)==0)?(!B(_qh(_ro,_rr)))?E(_rt):E(_rr):E(_rt):E(_rr);}else{return new F(function(){return _rv(_ry);});}}},_rA=function(_rB,_rC){return new F(function(){return _rn(_rB,E(_rC));});},_rD=function(_rE,_rF){return E(B(_qU(_rE,E(_rF))).a);},_rG={_:0,a:_mQ,b:_j2,c:_rj,d:_rD,e:_rA,f:_r7,g:_rd},_rH=new T1(0,1),_rI=function(_rJ,_rK){var _rL=E(_rJ);return new T2(0,_rL,new T(function(){var _rM=B(_rI(B(_4p(_rL,_rK)),_rK));return new T2(1,_rM.a,_rM.b);}));},_rN=function(_rO){var _rP=B(_rI(_rO,_rH));return new T2(1,_rP.a,_rP.b);},_rQ=function(_rR,_rS){var _rT=B(_rI(_rR,new T(function(){return B(_6K(_rS,_rR));})));return new T2(1,_rT.a,_rT.b);},_rU=new T1(0,0),_rV=function(_rW,_rX){var _rY=E(_rW);if(!_rY._){var _rZ=_rY.a,_s0=E(_rX);return (_s0._==0)?_rZ>=_s0.a:I_compareInt(_s0.a,_rZ)<=0;}else{var _s1=_rY.a,_s2=E(_rX);return (_s2._==0)?I_compareInt(_s1,_s2.a)>=0:I_compare(_s1,_s2.a)>=0;}},_s3=function(_s4,_s5,_s6){if(!B(_rV(_s5,_rU))){var _s7=function(_s8){return (!B(_51(_s8,_s6)))?new T2(1,_s8,new T(function(){return B(_s7(B(_4p(_s8,_s5))));})):__Z;};return new F(function(){return _s7(_s4);});}else{var _s9=function(_sa){return (!B(_4S(_sa,_s6)))?new T2(1,_sa,new T(function(){return B(_s9(B(_4p(_sa,_s5))));})):__Z;};return new F(function(){return _s9(_s4);});}},_sb=function(_sc,_sd,_se){return new F(function(){return _s3(_sc,B(_6K(_sd,_sc)),_se);});},_sf=function(_sg,_sh){return new F(function(){return _s3(_sg,_rH,_sh);});},_si=function(_sj){return new F(function(){return _4m(_sj);});},_sk=function(_sl){return new F(function(){return _6K(_sl,_rH);});},_sm=function(_sn){return new F(function(){return _4p(_sn,_rH);});},_so=function(_sp){return new F(function(){return _lQ(E(_sp));});},_sq={_:0,a:_sm,b:_sk,c:_so,d:_si,e:_rN,f:_rQ,g:_sf,h:_sb},_sr=function(_ss,_st){while(1){var _su=E(_ss);if(!_su._){var _sv=E(_su.a);if(_sv==(-2147483648)){_ss=new T1(1,I_fromInt(-2147483648));continue;}else{var _sw=E(_st);if(!_sw._){return new T1(0,B(_nH(_sv,_sw.a)));}else{_ss=new T1(1,I_fromInt(_sv));_st=_sw;continue;}}}else{var _sx=_su.a,_sy=E(_st);return (_sy._==0)?new T1(1,I_div(_sx,I_fromInt(_sy.a))):new T1(1,I_div(_sx,_sy.a));}}},_sz=function(_sA,_sB){if(!B(_4e(_sB,_qe))){return new F(function(){return _sr(_sA,_sB);});}else{return E(_49);}},_sC=function(_sD,_sE){while(1){var _sF=E(_sD);if(!_sF._){var _sG=E(_sF.a);if(_sG==(-2147483648)){_sD=new T1(1,I_fromInt(-2147483648));continue;}else{var _sH=E(_sE);if(!_sH._){var _sI=_sH.a;return new T2(0,new T1(0,B(_nH(_sG,_sI))),new T1(0,B(_od(_sG,_sI))));}else{_sD=new T1(1,I_fromInt(_sG));_sE=_sH;continue;}}}else{var _sJ=E(_sE);if(!_sJ._){_sD=_sF;_sE=new T1(1,I_fromInt(_sJ.a));continue;}else{var _sK=I_divMod(_sF.a,_sJ.a);return new T2(0,new T1(1,_sK.a),new T1(1,_sK.b));}}}},_sL=function(_sM,_sN){if(!B(_4e(_sN,_qe))){var _sO=B(_sC(_sM,_sN));return new T2(0,_sO.a,_sO.b);}else{return E(_49);}},_sP=function(_sQ,_sR){while(1){var _sS=E(_sQ);if(!_sS._){var _sT=E(_sS.a);if(_sT==(-2147483648)){_sQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _sU=E(_sR);if(!_sU._){return new T1(0,B(_od(_sT,_sU.a)));}else{_sQ=new T1(1,I_fromInt(_sT));_sR=_sU;continue;}}}else{var _sV=_sS.a,_sW=E(_sR);return (_sW._==0)?new T1(1,I_mod(_sV,I_fromInt(_sW.a))):new T1(1,I_mod(_sV,_sW.a));}}},_sX=function(_sY,_sZ){if(!B(_4e(_sZ,_qe))){return new F(function(){return _sP(_sY,_sZ);});}else{return E(_49);}},_t0=function(_t1,_t2){while(1){var _t3=E(_t1);if(!_t3._){var _t4=E(_t3.a);if(_t4==(-2147483648)){_t1=new T1(1,I_fromInt(-2147483648));continue;}else{var _t5=E(_t2);if(!_t5._){return new T1(0,quot(_t4,_t5.a));}else{_t1=new T1(1,I_fromInt(_t4));_t2=_t5;continue;}}}else{var _t6=_t3.a,_t7=E(_t2);return (_t7._==0)?new T1(0,I_toInt(I_quot(_t6,I_fromInt(_t7.a)))):new T1(1,I_quot(_t6,_t7.a));}}},_t8=function(_t9,_ta){if(!B(_4e(_ta,_qe))){return new F(function(){return _t0(_t9,_ta);});}else{return E(_49);}},_tb=function(_tc,_td){if(!B(_4e(_td,_qe))){var _te=B(_4y(_tc,_td));return new T2(0,_te.a,_te.b);}else{return E(_49);}},_tf=function(_tg,_th){while(1){var _ti=E(_tg);if(!_ti._){var _tj=E(_ti.a);if(_tj==(-2147483648)){_tg=new T1(1,I_fromInt(-2147483648));continue;}else{var _tk=E(_th);if(!_tk._){return new T1(0,_tj%_tk.a);}else{_tg=new T1(1,I_fromInt(_tj));_th=_tk;continue;}}}else{var _tl=_ti.a,_tm=E(_th);return (_tm._==0)?new T1(1,I_rem(_tl,I_fromInt(_tm.a))):new T1(1,I_rem(_tl,_tm.a));}}},_tn=function(_to,_tp){if(!B(_4e(_tp,_qe))){return new F(function(){return _tf(_to,_tp);});}else{return E(_49);}},_tq=function(_tr){return E(_tr);},_ts=function(_tt){return E(_tt);},_tu=function(_tv){var _tw=E(_tv);if(!_tw._){var _tx=E(_tw.a);return (_tx==(-2147483648))?E(_7o):(_tx<0)?new T1(0, -_tx):E(_tw);}else{var _ty=_tw.a;return (I_compareInt(_ty,0)>=0)?E(_tw):new T1(1,I_negate(_ty));}},_tz=new T1(0,0),_tA=new T1(0,-1),_tB=function(_tC){var _tD=E(_tC);if(!_tD._){var _tE=_tD.a;return (_tE>=0)?(E(_tE)==0)?E(_tz):E(_50):E(_tA);}else{var _tF=I_compareInt(_tD.a,0);return (_tF<=0)?(E(_tF)==0)?E(_tz):E(_tA):E(_50);}},_tG={_:0,a:_4p,b:_6K,c:_pK,d:_7p,e:_tu,f:_tB,g:_ts},_tH=function(_tI,_tJ){var _tK=E(_tI);if(!_tK._){var _tL=_tK.a,_tM=E(_tJ);return (_tM._==0)?_tL!=_tM.a:(I_compareInt(_tM.a,_tL)==0)?false:true;}else{var _tN=_tK.a,_tO=E(_tJ);return (_tO._==0)?(I_compareInt(_tN,_tO.a)==0)?false:true:(I_compare(_tN,_tO.a)==0)?false:true;}},_tP=new T2(0,_4e,_tH),_tQ=function(_tR,_tS){return (!B(_6v(_tR,_tS)))?E(_tR):E(_tS);},_tT=function(_tU,_tV){return (!B(_6v(_tU,_tV)))?E(_tV):E(_tU);},_tW={_:0,a:_tP,b:_31,c:_51,d:_6v,e:_4S,f:_rV,g:_tQ,h:_tT},_tX=function(_tY){return new T2(0,E(_tY),E(_jD));},_tZ=new T3(0,_tG,_tW,_tX),_u0={_:0,a:_tZ,b:_sq,c:_t8,d:_tn,e:_sz,f:_sX,g:_tb,h:_sL,i:_tq},_u1=function(_u2){return E(E(_u2).b);},_u3=function(_u4){return E(E(_u4).g);},_u5=new T1(0,1),_u6=function(_u7,_u8,_u9){var _ua=B(_u1(_u7)),_ub=B(_8w(_ua)),_uc=new T(function(){var _ud=new T(function(){var _ue=new T(function(){var _uf=new T(function(){return B(A3(_u3,_u7,_u0,new T(function(){return B(A3(_9T,_ua,_u8,_u9));})));});return B(A2(_9I,_ub,_uf));}),_ug=new T(function(){return B(A2(_7Y,_ub,new T(function(){return B(A2(_9I,_ub,_u5));})));});return B(A3(_8y,_ub,_ug,_ue));});return B(A3(_8y,_ub,_ud,_u9));});return new F(function(){return A3(_7W,_ub,_u8,_uc);});},_uh=1.5707963267948966,_ui=function(_uj){return 4.0e-2/Math.cos(B(_u6(_rG,_uj,_uh))-0.7853981633974483);},_uk=3,_ul=0.3,_um=-0.1,_un=new T3(0,_lw,_um,_ul),_uo=new T2(0,_un,_uk),_up=new T(function(){var _uq=B(_k4(_ui,_lt,_lM,_uo,_lG));return new T6(0,_uq.a,_uq.b,_uq.c,_uq.d,_uq.e,_uq.f);}),_ur=new T2(1,_up,_T),_us=new T2(1,_lH,_ur),_ut=new T(function(){return B(unCStr("Negative range size"));}),_uu=new T(function(){return B(err(_ut));}),_uv=function(_){var _uw=B(_hU(_us,0))-1|0,_ux=function(_uy){if(_uy>=0){var _uz=newArr(_uy,_i0),_uA=_uz,_uB=E(_uy);if(!_uB){return new T4(0,E(_lJ),E(_uw),0,_uA);}else{var _uC=function(_uD,_uE,_){while(1){var _uF=E(_uD);if(!_uF._){return E(_);}else{var _=_uA[_uE]=_uF.a;if(_uE!=(_uB-1|0)){var _uG=_uE+1|0;_uD=_uF.b;_uE=_uG;continue;}else{return E(_);}}}},_=B((function(_uH,_uI,_uJ,_){var _=_uA[_uJ]=_uH;if(_uJ!=(_uB-1|0)){return new F(function(){return _uC(_uI,_uJ+1|0,_);});}else{return E(_);}})(_lH,_ur,0,_));return new T4(0,E(_lJ),E(_uw),_uB,_uA);}}else{return E(_uu);}};if(0>_uw){return new F(function(){return _ux(0);});}else{return new F(function(){return _ux(_uw+1|0);});}},_uK=function(_uL){var _uM=B(A1(_uL,_));return E(_uM);},_uN=new T(function(){return B(_uK(_uv));}),_uO=function(_uP,_uQ,_){var _uR=B(A1(_uP,_)),_uS=B(A1(_uQ,_));return _uR;},_uT=function(_uU,_uV,_){var _uW=B(A1(_uU,_)),_uX=B(A1(_uV,_));return new T(function(){return B(A1(_uW,_uX));});},_uY=function(_uZ,_v0,_){var _v1=B(A1(_v0,_));return _uZ;},_v2=function(_v3,_v4,_){var _v5=B(A1(_v4,_));return new T(function(){return B(A1(_v3,_v5));});},_v6=new T2(0,_v2,_uY),_v7=function(_v8,_){return _v8;},_v9=function(_va,_vb,_){var _vc=B(A1(_va,_));return new F(function(){return A1(_vb,_);});},_vd=new T5(0,_v6,_v7,_uT,_v9,_uO),_ve=function(_vf){return E(_vf);},_vg=function(_vh){return E(_vh);},_vi=function(_vj,_vk){return E(_vk);},_vl=function(_vm,_vn){return E(_vm);},_vo=function(_vp){return E(_vp);},_vq=new T2(0,_vo,_vl),_vr=function(_vs,_vt){return E(_vs);},_vu=new T5(0,_vq,_vg,_ve,_vi,_vr),_vv=function(_vw){var _vx=E(_vw);return (E(_vx.b)-E(_vx.a)|0)+1|0;},_vy=function(_vz,_vA){var _vB=E(_vz),_vC=E(_vA);return (E(_vB.a)>_vC)?false:_vC<=E(_vB.b);},_vD=function(_vE,_vF){var _vG=jsShowI(_vE);return new F(function(){return _14(fromJSStr(_vG),_vF);});},_vH=function(_vI,_vJ,_vK){if(_vJ>=0){return new F(function(){return _vD(_vJ,_vK);});}else{if(_vI<=6){return new F(function(){return _vD(_vJ,_vK);});}else{return new T2(1,_8f,new T(function(){var _vL=jsShowI(_vJ);return B(_14(fromJSStr(_vL),new T2(1,_8e,_vK)));}));}}},_vM=function(_vN){return new F(function(){return _vH(0,E(_vN),_T);});},_vO=function(_vP,_vQ,_vR){return new F(function(){return _vH(E(_vP),E(_vQ),_vR);});},_vS=function(_vT,_vU){return new F(function(){return _vH(0,E(_vT),_vU);});},_vV=function(_vW,_vX){return new F(function(){return _3P(_vS,_vW,_vX);});},_vY=new T3(0,_vO,_vM,_vV),_vZ=0,_w0=function(_w1,_w2,_w3){return new F(function(){return A1(_w1,new T2(1,_3M,new T(function(){return B(A1(_w2,_w3));})));});},_w4=new T(function(){return B(unCStr(": empty list"));}),_w5=new T(function(){return B(unCStr("Prelude."));}),_w6=function(_w7){return new F(function(){return err(B(_14(_w5,new T(function(){return B(_14(_w7,_w4));},1))));});},_w8=new T(function(){return B(unCStr("foldr1"));}),_w9=new T(function(){return B(_w6(_w8));}),_wa=function(_wb,_wc){var _wd=E(_wc);if(!_wd._){return E(_w9);}else{var _we=_wd.a,_wf=E(_wd.b);if(!_wf._){return E(_we);}else{return new F(function(){return A2(_wb,_we,new T(function(){return B(_wa(_wb,_wf));}));});}}},_wg=new T(function(){return B(unCStr(" out of range "));}),_wh=new T(function(){return B(unCStr("}.index: Index "));}),_wi=new T(function(){return B(unCStr("Ix{"));}),_wj=new T2(1,_8e,_T),_wk=new T2(1,_8e,_wj),_wl=0,_wm=function(_wn){return E(E(_wn).a);},_wo=function(_wp,_wq,_wr,_ws,_wt){var _wu=new T(function(){var _wv=new T(function(){var _ww=new T(function(){var _wx=new T(function(){var _wy=new T(function(){return B(A3(_wa,_w0,new T2(1,new T(function(){return B(A3(_wm,_wr,_wl,_ws));}),new T2(1,new T(function(){return B(A3(_wm,_wr,_wl,_wt));}),_T)),_wk));});return B(_14(_wg,new T2(1,_8f,new T2(1,_8f,_wy))));});return B(A(_wm,[_wr,_vZ,_wq,new T2(1,_8e,_wx)]));});return B(_14(_wh,new T2(1,_8f,_ww)));},1);return B(_14(_wp,_wv));},1);return new F(function(){return err(B(_14(_wi,_wu)));});},_wz=function(_wA,_wB,_wC,_wD,_wE){return new F(function(){return _wo(_wA,_wB,_wE,_wC,_wD);});},_wF=function(_wG,_wH,_wI,_wJ){var _wK=E(_wI);return new F(function(){return _wz(_wG,_wH,_wK.a,_wK.b,_wJ);});},_wL=function(_wM,_wN,_wO,_wP){return new F(function(){return _wF(_wP,_wO,_wN,_wM);});},_wQ=new T(function(){return B(unCStr("Int"));}),_wR=function(_wS,_wT){return new F(function(){return _wL(_vY,_wT,_wS,_wQ);});},_wU=function(_wV,_wW){var _wX=E(_wV),_wY=E(_wX.a),_wZ=E(_wW);if(_wY>_wZ){return new F(function(){return _wR(_wZ,_wX);});}else{if(_wZ>E(_wX.b)){return new F(function(){return _wR(_wZ,_wX);});}else{return _wZ-_wY|0;}}},_x0=function(_x1){var _x2=E(_x1);return new F(function(){return _nr(_x2.a,_x2.b);});},_x3=function(_x4){var _x5=E(_x4),_x6=E(_x5.a),_x7=E(_x5.b);return (_x6>_x7)?E(_vZ):(_x7-_x6|0)+1|0;},_x8=function(_x9,_xa){return new F(function(){return _oQ(_xa,E(_x9).a);});},_xb={_:0,a:_pG,b:_x0,c:_wU,d:_x8,e:_vy,f:_x3,g:_vv},_xc=function(_xd,_xe){return new T2(1,_xd,_xe);},_xf=function(_xg,_xh){var _xi=E(_xh);return new T2(0,_xi.a,_xi.b);},_xj=function(_xk){return E(E(_xk).f);},_xl=function(_xm,_xn,_xo){var _xp=E(_xn),_xq=_xp.a,_xr=_xp.b,_xs=function(_){var _xt=B(A2(_xj,_xm,_xp));if(_xt>=0){var _xu=newArr(_xt,_i0),_xv=_xu,_xw=E(_xt);if(!_xw){return new T(function(){return new T4(0,E(_xq),E(_xr),0,_xv);});}else{var _xx=function(_xy,_xz,_){while(1){var _xA=E(_xy);if(!_xA._){return E(_);}else{var _=_xv[_xz]=_xA.a;if(_xz!=(_xw-1|0)){var _xB=_xz+1|0;_xy=_xA.b;_xz=_xB;continue;}else{return E(_);}}}},_=B(_xx(_xo,0,_));return new T(function(){return new T4(0,E(_xq),E(_xr),_xw,_xv);});}}else{return E(_uu);}};return new F(function(){return _uK(_xs);});},_xC=function(_xD,_xE,_xF,_xG){var _xH=new T(function(){var _xI=E(_xG),_xJ=_xI.c-1|0,_xK=new T(function(){return B(A2(_dE,_xE,_T));});if(0<=_xJ){var _xL=new T(function(){return B(_9P(_xE));}),_xM=function(_xN){var _xO=new T(function(){var _xP=new T(function(){return B(A1(_xF,new T(function(){return E(_xI.d[_xN]);})));});return B(A3(_9X,_xL,_xc,_xP));});return new F(function(){return A3(_9V,_xE,_xO,new T(function(){if(_xN!=_xJ){return B(_xM(_xN+1|0));}else{return E(_xK);}}));});};return B(_xM(0));}else{return E(_xK);}}),_xQ=new T(function(){return B(_xf(_xD,_xG));});return new F(function(){return A3(_9X,B(_9P(_xE)),function(_xR){return new F(function(){return _xl(_xD,_xQ,_xR);});},_xH);});},_xS=function(_xT){var _xU=E(_xT);return new F(function(){return Math.log(_xU+(_xU+1)*Math.sqrt((_xU-1)/(_xU+1)));});},_xV=function(_xW){var _xX=E(_xW);return new F(function(){return Math.log(_xX+Math.sqrt(1+_xX*_xX));});},_xY=function(_xZ){var _y0=E(_xZ);return 0.5*Math.log((1+_y0)/(1-_y0));},_y1=function(_y2,_y3){return Math.log(E(_y3))/Math.log(E(_y2));},_y4=3.141592653589793,_y5=function(_y6){return new F(function(){return Math.acos(E(_y6));});},_y7=function(_y8){return new F(function(){return Math.asin(E(_y8));});},_y9=function(_ya){return new F(function(){return Math.atan(E(_ya));});},_yb=function(_yc){return new F(function(){return Math.cos(E(_yc));});},_yd=function(_ye){return new F(function(){return cosh(E(_ye));});},_yf=function(_yg){return new F(function(){return Math.exp(E(_yg));});},_yh=function(_yi){return new F(function(){return Math.log(E(_yi));});},_yj=function(_yk,_yl){return new F(function(){return Math.pow(E(_yk),E(_yl));});},_ym=function(_yn){return new F(function(){return Math.sin(E(_yn));});},_yo=function(_yp){return new F(function(){return sinh(E(_yp));});},_yq=function(_yr){return new F(function(){return Math.sqrt(E(_yr));});},_ys=function(_yt){return new F(function(){return Math.tan(E(_yt));});},_yu=function(_yv){return new F(function(){return tanh(E(_yv));});},_yw={_:0,a:_j2,b:_y4,c:_yf,d:_yh,e:_yq,f:_yj,g:_y1,h:_ym,i:_yb,j:_ys,k:_y7,l:_y5,m:_y9,n:_yo,o:_yd,p:_yu,q:_xV,r:_xS,s:_xY},_yx=function(_yy,_yz,_yA){var _yB=E(_yy);if(!_yB._){return __Z;}else{var _yC=E(_yz);if(!_yC._){return __Z;}else{var _yD=_yC.a,_yE=E(_yA);if(!_yE._){return __Z;}else{var _yF=E(_yE.a),_yG=_yF.a;return new F(function(){return _14(new T2(1,new T3(0,_yB.a,_yD,_yG),new T2(1,new T3(0,_yD,_yG,_yF.b),_T)),new T(function(){return B(_yx(_yB.b,_yC.b,_yE.b));},1));});}}}},_yH=function(_yI,_yJ,_yK,_yL){var _yM=E(_yK);if(!_yM._){return __Z;}else{var _yN=_yM.a,_yO=E(_yL);if(!_yO._){return __Z;}else{var _yP=E(_yO.a),_yQ=_yP.a;return new F(function(){return _14(new T2(1,new T3(0,_yI,_yN,_yQ),new T2(1,new T3(0,_yN,_yQ,_yP.b),_T)),new T(function(){return B(_yx(_yJ,_yM.b,_yO.b));},1));});}}},_yR=function(_yS,_yT,_yU,_yV,_yW,_yX,_yY){var _yZ=B(_8w(B(_8u(_yS)))),_z0=new T(function(){return B(A3(_7W,_yZ,new T(function(){return B(A3(_8y,_yZ,_yT,_yW));}),new T(function(){return B(A3(_8y,_yZ,_yU,_yX));})));});return new F(function(){return A3(_7W,_yZ,_z0,new T(function(){return B(A3(_8y,_yZ,_yV,_yY));}));});},_z1=function(_z2,_z3,_z4,_z5){var _z6=new T(function(){return B(_8u(_z2));}),_z7=new T(function(){return B(A2(_8K,_z2,new T(function(){return B(_yR(_z2,_z3,_z4,_z5,_z3,_z4,_z5));})));});return new T3(0,new T(function(){return B(A3(_9T,_z6,_z3,_z7));}),new T(function(){return B(A3(_9T,_z6,_z4,_z7));}),new T(function(){return B(A3(_9T,_z6,_z5,_z7));}));},_z8=function(_z9,_za,_zb,_zc){var _zd=B(A2(_hz,_z9,new T3(0,_za,_zb,_zc))),_ze=_zd.a,_zf=_zd.b,_zg=_zd.c,_zh=B(_z1(_z9,_ze,_zf,_zg)),_zi=new T(function(){return B(_8u(_z9));}),_zj=new T(function(){return B(_8w(_zi));}),_zk=new T(function(){return B(_7W(_zj));}),_zl=new T(function(){return B(_7Y(_zj));}),_zm=new T(function(){return B(_8y(_zj));}),_zn=new T(function(){var _zo=new T(function(){return B(A2(_8K,_z9,new T(function(){return B(_yR(_z9,_ze,_zf,_zg,_ze,_zf,_zg));})));});return B(A3(_9T,_zi,new T(function(){return B(_8M(_z9,_za,_zb,_zc));}),_zo));}),_zp=new T(function(){var _zq=new T(function(){return B(A1(_zl,new T(function(){return B(A2(_zm,_zh.c,_zn));})));});return B(A2(_zk,_zc,_zq));}),_zr=new T(function(){var _zs=new T(function(){return B(A1(_zl,new T(function(){return B(A2(_zm,_zh.b,_zn));})));});return B(A2(_zk,_zb,_zs));}),_zt=new T(function(){var _zu=new T(function(){return B(A1(_zl,new T(function(){return B(A2(_zm,_zh.a,_zn));})));});return B(A2(_zk,_za,_zu));});return new T3(0,_zt,_zr,_zp);},_zv=function(_zw,_zx,_zy,_zz,_zA){var _zB=B(A2(_hz,_zw,_zx)),_zC=B(_z1(_zw,_zB.a,_zB.b,_zB.c)),_zD=_zC.a,_zE=_zC.b,_zF=_zC.c,_zG=new T(function(){return B(_8w(new T(function(){return B(_8u(_zw));})));}),_zH=new T(function(){return B(_7W(_zG));}),_zI=new T(function(){return B(_8y(_zG));}),_zJ=new T(function(){return B(A2(_7Y,_zG,new T(function(){return B(_yR(_zw,_zy,_zz,_zA,_zD,_zE,_zF));})));}),_zK=new T(function(){return B(A2(_zH,_zA,new T(function(){return B(A2(_zI,_zF,_zJ));})));}),_zL=new T(function(){return B(A2(_zH,_zz,new T(function(){return B(A2(_zI,_zE,_zJ));})));}),_zM=new T(function(){return B(A2(_zH,_zy,new T(function(){return B(A2(_zI,_zD,_zJ));})));});return new F(function(){return _z1(_zw,_zM,_zL,_zK);});},_zN=new T(function(){return E(_ih);}),_zO=new T(function(){return B(unCStr("head"));}),_zP=new T(function(){return B(_w6(_zO));}),_zQ=function(_){return _S;},_zR=new T(function(){return eval("drawTriangles");}),_zS=function(_){var _zT=__app0(E(_zR));return new F(function(){return _zQ(_);});},_zU=new T(function(){return B(_hz(_yw));}),_zV=new T(function(){return B(unCStr("tail"));}),_zW=new T(function(){return B(_w6(_zV));}),_zX=new T(function(){return eval("triangle");}),_zY=new T(function(){return E(_zN)-1;}),_zZ=0,_A0=new T(function(){return B(_jT(_jB,_j2,_zZ,_zY));}),_A1=1,_A2=new T(function(){var _A3=eval("proceedCount"),_A4=Number(_A3);return jsTrunc(_A4);}),_A5=new T(function(){return E(_A2);}),_A6=new T(function(){return B(_jT(_jB,_j2,_A1,_A5));}),_A7=function(_A8,_A9){var _Aa=E(_A8);if(!_Aa._){return __Z;}else{var _Ab=E(_A9);return (_Ab._==0)?__Z:new T2(1,new T2(0,_Aa.a,_Ab.a),new T(function(){return B(_A7(_Aa.b,_Ab.b));}));}},_Ac=function(_Ad,_){var _Ae=new T(function(){return E(E(E(_Ad).b).a);}),_Af=new T(function(){return E(E(_Ad).d);}),_Ag=new T(function(){var _Ah=E(_Af),_Ai=_Ah.a,_Aj=_Ah.b,_Ak=_Ah.c,_Al=B(A1(_zU,_Ae)),_Am=B(_z1(_yw,_Al.a,_Al.b,_Al.c)),_An=_Am.a,_Ao=_Am.b,_Ap=_Am.c;return new T3(0,new T(function(){return E(_Aj)*E(_Ap)-E(_Ao)*E(_Ak);}),new T(function(){return E(_Ak)*E(_An)-E(_Ap)*E(_Ai);}),new T(function(){return E(_Ai)*E(_Ao)-E(_An)*E(_Aj);}));}),_Aq=function(_Ar,_){var _As=E(_Ar);if(!_As._){return _T;}else{var _At=new T(function(){var _Au=E(_As.a)/E(_zN);return (_Au+_Au)*3.141592653589793;}),_Av=new T(function(){return E(_At)+E(E(E(_Ad).b).b);}),_Aw=new T(function(){return B(A1(E(_Ad).a,_At));}),_Ax=function(_Ay,_Az,_AA,_){var _AB=E(_Ay);if(!_AB._){return new T2(0,_T,new T2(0,_Az,_AA));}else{var _AC=new T(function(){var _AD=E(_Az),_AE=E(_AA),_AF=new T(function(){return (1+1/E(_AB.a))*E(_Aw);}),_AG=B(_z8(_yw,new T(function(){return E(_AD.a)+E(_AE.a)*E(_AF);}),new T(function(){return E(_AD.b)+E(_AE.b)*E(_AF);}),new T(function(){return E(_AD.c)+E(_AE.c)*E(_AF);})));return new T3(0,_AG.a,_AG.b,_AG.c);}),_AH=B(_Ax(_AB.b,_AC,new T(function(){var _AI=E(_AA),_AJ=B(_zv(_yw,_AC,_AI.a,_AI.b,_AI.c));return new T3(0,_AJ.a,_AJ.b,_AJ.c);}),_));return new T2(0,new T2(1,_AC,new T(function(){return E(E(_AH).a);})),new T(function(){return E(E(_AH).b);}));}},_AK=new T(function(){var _AL=E(_Af),_AM=E(_Ag),_AN=new T(function(){return Math.cos(E(_Av));}),_AO=new T(function(){return Math.sin(E(_Av));});return new T3(0,new T(function(){return E(_AL.a)*E(_AN)+E(_AM.a)*E(_AO);}),new T(function(){return E(_AL.b)*E(_AN)+E(_AM.b)*E(_AO);}),new T(function(){return E(_AL.c)*E(_AN)+E(_AM.c)*E(_AO);}));}),_AP=B(_Ax(_A6,_Ae,_AK,_)),_AQ=B(_Aq(_As.b,_));return new T2(1,new T(function(){return E(E(_AP).a);}),_AQ);}},_AR=B(_Aq(_A0,_)),_AS=function(_AT,_AU,_){var _AV=E(_AT);if(!_AV._){return _T;}else{var _AW=E(_AU);if(!_AW._){return _T;}else{var _AX=E(_Ae),_AY=E(_AV.a);if(!_AY._){return E(_zP);}else{var _AZ=_AY.b,_B0=E(_AY.a),_B1=E(_AW.a);if(!_B1._){return E(_zP);}else{var _B2=E(_B1.a),_B3=E(_zX),_B4=__apply(_B3,new T2(1,E(_B2.c),new T2(1,E(_B2.b),new T2(1,E(_B2.a),new T2(1,E(_B0.c),new T2(1,E(_B0.b),new T2(1,E(_B0.a),new T2(1,E(_AX.c),new T2(1,E(_AX.b),new T2(1,E(_AX.a),_T)))))))))),_B5=function(_B6,_){var _B7=E(_B6);if(!_B7._){return new F(function(){return _AS(_AV.b,_AW.b,_);});}else{var _B8=E(_B7.a),_B9=E(_B8.a),_Ba=E(_B8.b),_Bb=E(_B8.c),_Bc=__apply(_B3,new T2(1,E(_Bb.c),new T2(1,E(_Bb.b),new T2(1,E(_Bb.a),new T2(1,E(_Ba.c),new T2(1,E(_Ba.b),new T2(1,E(_Ba.a),new T2(1,E(_B9.c),new T2(1,E(_B9.b),new T2(1,E(_B9.a),_T)))))))))),_Bd=B(_B5(_B7.b,_));return new T2(1,_S,_Bd);}},_Be=B(_B5(B(_yH(_B0,_AZ,_AZ,new T(function(){return B(_A7(_B1,_B1.b));},1))),_));return new T2(1,_S,_Be);}}}}},_Bf=new T(function(){var _Bg=B(_14(_AR,new T2(1,new T(function(){var _Bh=E(_AR);if(!_Bh._){return E(_zP);}else{return E(_Bh.a);}}),_T)));if(!_Bg._){return E(_zW);}else{return E(_Bg.b);}},1),_Bi=B(_AS(_AR,_Bf,_));return new F(function(){return _zS(_);});},_Bj=new T(function(){return eval("draw");}),_Bk=new T(function(){return B(_hz(_yw));}),_Bl=function(_Bm,_Bn,_Bo,_Bp,_Bq,_Br,_Bs){var _Bt=new T(function(){var _Bu=E(_Bp),_Bv=new T(function(){var _Bw=E(_Bu.a),_Bx=E(_Br),_By=_Bx.a,_Bz=_Bx.b,_BA=_Bx.c,_BB=B(A1(_Bk,new T(function(){return E(E(_Bo).a);}))),_BC=B(_z1(_yw,_BB.a,_BB.b,_BB.c)),_BD=_BC.a,_BE=_BC.b,_BF=_BC.c,_BG=new T(function(){return B(_yR(_yw,_BD,_BE,_BF,_By,_Bz,_BA));});return new T3(0,new T(function(){return E(_Bw.a)+(E(_By)+ -(E(_BD)*E(_BG)))*E(_Bm);}),new T(function(){return E(_Bw.b)+(E(_Bz)+ -(E(_BE)*E(_BG)))*E(_Bm);}),new T(function(){return E(_Bw.c)+(E(_BA)+ -(E(_BF)*E(_BG)))*E(_Bm);}));});return new T2(0,_Bv,_Bu.b);});return new T6(0,_Bn,_Bo,_Bt,_Bq,_Br,_Bs);},_BH=5.0e-2,_BI=function(_BJ){var _BK=E(_BJ),_BL=B(_Bl(_BH,_BK.a,_BK.b,_BK.c,_BK.d,_BK.e,_BK.f));return new T6(0,_BL.a,_BL.b,_BL.c,_BL.d,_BL.e,_BL.f);},_BM=function(_BN,_BO,_BP,_BQ){var _BR=new T(function(){return B(_8w(new T(function(){return B(_8u(_BO));})));}),_BS=new T(function(){var _BT=E(_BQ),_BU=_BT.a,_BV=_BT.b,_BW=_BT.c,_BX=B(A2(_hz,_BO,_BP)),_BY=B(_z1(_BO,_BX.a,_BX.b,_BX.c)),_BZ=_BY.a,_C0=_BY.b,_C1=_BY.c,_C2=new T(function(){return B(_7W(_BR));}),_C3=new T(function(){return B(_8y(_BR));}),_C4=new T(function(){return B(A2(_7Y,_BR,new T(function(){return B(_yR(_BO,_BU,_BV,_BW,_BZ,_C0,_C1));})));}),_C5=new T(function(){return B(A2(_C2,_BW,new T(function(){return B(A2(_C3,_C1,_C4));})));}),_C6=new T(function(){return B(A2(_C2,_BV,new T(function(){return B(A2(_C3,_C0,_C4));})));}),_C7=new T(function(){return B(A2(_C2,_BU,new T(function(){return B(A2(_C3,_BZ,_C4));})));});return new T3(0,_C7,_C6,_C5);}),_C8=new T(function(){return B(A2(_8K,_BO,new T(function(){var _C9=E(_BS),_Ca=_C9.a,_Cb=_C9.b,_Cc=_C9.c;return B(_yR(_BO,_Ca,_Cb,_Cc,_Ca,_Cb,_Cc));})));});if(!B(A3(_qc,_BN,_C8,new T(function(){return B(A2(_9I,_BR,_9H));})))){var _Cd=E(_BS),_Ce=B(_z1(_BO,_Cd.a,_Cd.b,_Cd.c)),_Cf=new T(function(){return B(_8y(_BR));}),_Cg=new T(function(){return B(A2(_8K,_BO,new T(function(){var _Ch=E(_BQ),_Ci=_Ch.a,_Cj=_Ch.b,_Ck=_Ch.c;return B(_yR(_BO,_Ci,_Cj,_Ck,_Ci,_Cj,_Ck));})));});return new T3(0,new T(function(){return B(A2(_Cf,_Ce.a,_Cg));}),new T(function(){return B(A2(_Cf,_Ce.b,_Cg));}),new T(function(){return B(A2(_Cf,_Ce.c,_Cg));}));}else{var _Cl=new T(function(){return B(A2(_9I,_BR,_9H));});return new T3(0,_Cl,_Cl,_Cl);}},_Cm=function(_Cn,_Co,_Cp,_Cq,_Cr,_Cs){var _Ct=new T(function(){var _Cu=E(E(_Co).a),_Cv=B(_z8(_yw,_Cu.a,_Cu.b,_Cu.c));return new T3(0,_Cv.a,_Cv.b,_Cv.c);}),_Cw=new T(function(){var _Cx=E(_Cp);return new T2(0,new T(function(){var _Cy=B(_BM(_j9,_yw,_Ct,_Cx.a));return new T3(0,_Cy.a,_Cy.b,_Cy.c);}),_Cx.b);});return new T6(0,_Cn,new T(function(){return new T2(0,_Ct,E(_Co).b);}),_Cw,new T(function(){var _Cz=E(_Cq),_CA=B(_zv(_yw,_Ct,_Cz.a,_Cz.b,_Cz.c));return new T3(0,_CA.a,_CA.b,_CA.c);}),_Cr,_Cs);},_CB=function(_CC,_CD,_CE,_CF,_CG,_CH,_CI){var _CJ=new T(function(){var _CK=E(_CE),_CL=E(_CF),_CM=new T(function(){var _CN=E(_CK.a),_CO=E(_CL.a);return new T3(0,new T(function(){return E(_CN.a)+E(_CO.a)*E(_CC);}),new T(function(){return E(_CN.b)+E(_CO.b)*E(_CC);}),new T(function(){return E(_CN.c)+E(_CO.c)*E(_CC);}));});return new T2(0,_CM,new T(function(){return E(_CK.b)+E(_CL.b)*E(_CC);}));});return new F(function(){return _Cm(_CD,_CJ,_CF,_CG,_CH,_CI);});},_CP=function(_CQ){var _CR=E(_CQ),_CS=B(_CB(_BH,_CR.a,_CR.b,_CR.c,_CR.d,_CR.e,_CR.f));return new T6(0,_CS.a,_CS.b,_CS.c,_CS.d,_CS.e,_CS.f);},_CT=new T(function(){return eval("refresh");}),_CU=function(_CV,_){var _CW=__app0(E(_CT)),_CX=__app0(E(_Bj)),_CY=B(A(_xC,[_xb,_vd,_Ac,_CV,_]));return new T(function(){return B(_xC(_xb,_vu,_CP,new T(function(){return B(_xC(_xb,_vu,_BI,_CV));})));});},_CZ=function(_D0,_D1,_D2){var _D3=function(_){var _D4=B(_CU(_D0,_));return new T(function(){return B(A1(_D2,new T1(1,_D4)));});};return new T1(0,_D3);},_D5=new T0(2),_D6=function(_D7,_D8,_D9){return function(_){var _Da=E(_D7),_Db=rMV(_Da),_Dc=E(_Db);if(!_Dc._){var _Dd=new T(function(){var _De=new T(function(){return B(A1(_D9,_S));});return B(_14(_Dc.b,new T2(1,new T2(0,_D8,function(_Df){return E(_De);}),_T)));}),_=wMV(_Da,new T2(0,_Dc.a,_Dd));return _D5;}else{var _Dg=E(_Dc.a);if(!_Dg._){var _=wMV(_Da,new T2(0,_D8,_T));return new T(function(){return B(A1(_D9,_S));});}else{var _=wMV(_Da,new T1(1,_Dg.b));return new T1(1,new T2(1,new T(function(){return B(A1(_D9,_S));}),new T2(1,new T(function(){return B(A2(_Dg.a,_D8,_U));}),_T)));}}};},_Dh=function(_Di){return E(E(_Di).b);},_Dj=function(_Dk,_Dl,_Dm){var _Dn=new T(function(){return new T1(0,B(_D6(_Dl,_Dm,_U)));}),_Do=function(_Dp){return new T1(1,new T2(1,new T(function(){return B(A1(_Dp,_S));}),new T2(1,_Dn,_T)));};return new F(function(){return A2(_Dh,_Dk,_Do);});},_Dq=function(_){return new F(function(){return __jsNull();});},_Dr=function(_Ds){var _Dt=B(A1(_Ds,_));return E(_Dt);},_Du=new T(function(){return B(_Dr(_Dq));}),_Dv=new T(function(){return E(_Du);}),_Dw=new T(function(){return eval("window.requestAnimationFrame");}),_Dx=new T1(1,_T),_Dy=function(_Dz,_DA){return function(_){var _DB=E(_Dz),_DC=rMV(_DB),_DD=E(_DC);if(!_DD._){var _DE=_DD.a,_DF=E(_DD.b);if(!_DF._){var _=wMV(_DB,_Dx);return new T(function(){return B(A1(_DA,_DE));});}else{var _DG=E(_DF.a),_=wMV(_DB,new T2(0,_DG.a,_DF.b));return new T1(1,new T2(1,new T(function(){return B(A1(_DA,_DE));}),new T2(1,new T(function(){return B(A1(_DG.b,_U));}),_T)));}}else{var _DH=new T(function(){var _DI=function(_DJ){var _DK=new T(function(){return B(A1(_DA,_DJ));});return function(_DL){return E(_DK);};};return B(_14(_DD.a,new T2(1,_DI,_T)));}),_=wMV(_DB,new T1(1,_DH));return _D5;}};},_DM=function(_DN,_DO){return new T1(0,B(_Dy(_DN,_DO)));},_DP=function(_DQ,_DR){var _DS=new T(function(){return new T1(0,B(_D6(_DQ,_S,_U)));});return function(_){var _DT=__createJSFunc(2,function(_DU,_){var _DV=B(_1e(_DS,_T,_));return _Dv;}),_DW=__app1(E(_Dw),_DT);return new T(function(){return B(_DM(_DQ,_DR));});};},_DX=new T1(1,_T),_DY=function(_DZ){var _E0=new T(function(){return B(_E1(_));}),_E2=new T(function(){var _E3=function(_E4){return E(_E0);},_E5=function(_){var _E6=nMV(_DX);return new T(function(){return new T1(0,B(_DP(_E6,_E3)));});};return B(A(_Dj,[_13,_DZ,_S,function(_E7){return E(new T1(0,_E5));}]));}),_E1=function(_E8){return E(_E2);};return new F(function(){return _E1(_);});},_E9=function(_Ea){return E(E(_Ea).a);},_Eb=function(_Ec){return E(E(_Ec).d);},_Ed=function(_Ee){return E(E(_Ee).c);},_Ef=function(_Eg){return E(E(_Eg).c);},_Eh=new T1(1,_T),_Ei=function(_Ej){var _Ek=function(_){var _El=nMV(_Eh);return new T(function(){return B(A1(_Ej,_El));});};return new T1(0,_Ek);},_Em=function(_En,_Eo){var _Ep=new T(function(){return B(_Ef(_En));}),_Eq=B(_E9(_En)),_Er=function(_Es){var _Et=new T(function(){return B(A1(_Ep,new T(function(){return B(A1(_Eo,_Es));})));});return new F(function(){return A3(_Ed,_Eq,_Et,new T(function(){return B(A2(_Eb,_Eq,_Es));}));});};return new F(function(){return A3(_J,_Eq,new T(function(){return B(A2(_Dh,_En,_Ei));}),_Er);});},_Eu=function(_Ev,_Ew,_Ex){var _Ey=new T(function(){return B(_E9(_Ev));}),_Ez=new T(function(){return B(A2(_Eb,_Ey,_S));}),_EA=function(_EB,_EC){var _ED=new T(function(){var _EE=new T(function(){return B(A2(_Dh,_Ev,function(_EF){return new F(function(){return _DM(_EC,_EF);});}));});return B(A3(_J,_Ey,_EE,new T(function(){return B(A1(_Ex,_EB));})));});return new F(function(){return A3(_J,_Ey,_ED,function(_EG){var _EH=E(_EG);if(!_EH._){return E(_Ez);}else{return new F(function(){return _EA(_EH.a,_EC);});}});});};return new F(function(){return _Em(_Ev,function(_EF){return new F(function(){return _EA(_Ew,_EF);});});});},_EI=function(_){var _EJ=__app2(E(_1j),E(_96),E(_hT));return new F(function(){return _1e(new T(function(){return B(A(_Eu,[_13,_uN,_CZ,_DY]));}),_T,_);});},_EK=function(_){return new F(function(){return _EI(_);});};
var hasteMain = function() {B(A(_EK, [0]));};window.onload = hasteMain;