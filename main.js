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

var _0=new T(function(){return eval("__strict(compile)");}),_1=new T(function(){return B(unCStr("y"));}),_2=new T(function(){return toJSStr(E(_1));}),_3=function(_4){return E(E(_4).b);},_5=function(_6){return E(E(_6).a);},_7=function(_8,_9,_a){var _b=E(_a);if(!_b._){return new F(function(){return A1(_9,_b.a);});}else{var _c=new T(function(){return B(_3(_8));}),_d=new T(function(){return B(_5(_8));}),_e=function(_f){var _g=E(_f);if(!_g._){return E(_d);}else{return new F(function(){return A2(_c,new T(function(){return B(_7(_8,_9,_g.a));}),new T(function(){return B(_e(_g.b));}));});}};return new F(function(){return _e(_b.a);});}},_h=function(_i,_j,_k){var _l=new T(function(){return B(_3(_i));}),_m=new T(function(){return B(_5(_i));}),_n=function(_o){var _p=E(_o);if(!_p._){return E(_m);}else{return new F(function(){return A2(_l,new T(function(){return B(_7(_i,_j,_p.a));}),new T(function(){return B(_n(_p.b));}));});}};return new F(function(){return _n(_k);});},_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v){var _w=E(_v);if(!_w._){return __Z;}else{return new F(function(){return _q(_w.a,new T(function(){return B(_u(_w.b));},1));});}},_x=function(_y){return new F(function(){return _u(_y);});},_z=__Z,_A=new T3(0,_z,_q,_x),_B=new T(function(){return B(unCStr("vec3("));}),_C=new T1(0,_B),_D=new T(function(){return B(unCStr(")"));}),_E=new T1(0,_D),_F=new T2(1,_E,_z),_G=new T(function(){return B(unCStr(","));}),_H=new T1(0,_G),_I=new T(function(){return B(unCStr("."));}),_J=new T1(0,1),_K=function(_L){while(1){var _M=E(_L);if(!_M._){_L=new T1(1,I_fromInt(_M.a));continue;}else{return new F(function(){return I_toString(_M.a);});}}},_N=function(_O,_P){return new F(function(){return _q(fromJSStr(B(_K(_O))),_P);});},_Q=function(_R,_S){var _T=E(_R);if(!_T._){var _U=_T.a,_V=E(_S);return (_V._==0)?_U<_V.a:I_compareInt(_V.a,_U)>0;}else{var _W=_T.a,_X=E(_S);return (_X._==0)?I_compareInt(_W,_X.a)<0:I_compare(_W,_X.a)<0;}},_Y=41,_Z=40,_10=new T1(0,0),_11=function(_12,_13,_14){if(_12<=6){return new F(function(){return _N(_13,_14);});}else{if(!B(_Q(_13,_10))){return new F(function(){return _N(_13,_14);});}else{return new T2(1,_Z,new T(function(){return B(_q(fromJSStr(B(_K(_13))),new T2(1,_Y,_14)));}));}}},_15=new T(function(){return B(_11(0,_J,_z));}),_16=new T(function(){return B(_q(_15,_I));}),_17=new T1(0,_16),_18=new T1(0,0),_19=new T(function(){return B(_11(0,_18,_z));}),_1a=new T(function(){return B(_q(_19,_I));}),_1b=new T1(0,_1a),_1c=new T2(1,_1b,_z),_1d=new T2(1,_17,_1c),_1e=function(_1f,_1g){var _1h=E(_1g);return (_1h._==0)?__Z:new T2(1,_1f,new T2(1,_1h.a,new T(function(){return B(_1e(_1f,_1h.b));})));},_1i=new T(function(){return B(_1e(_H,_1d));}),_1j=new T2(1,_1b,_1i),_1k=new T1(1,_1j),_1l=new T2(1,_1k,_F),_1m=new T2(1,_C,_1l),_1n=function(_1o){return E(_1o);},_1p=new T(function(){return toJSStr(B(_h(_A,_1n,_1m)));}),_1q=function(_1r,_1s){while(1){var _1t=E(_1r);if(!_1t._){return E(_1s);}else{var _1u=_1s+1|0;_1r=_1t.b;_1s=_1u;continue;}}},_1v=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1w=new T(function(){return B(err(_1v));}),_1x=0,_1y=new T3(0,E(_1x),E(_1x),E(_1x)),_1z=new T(function(){return B(unCStr("Negative exponent"));}),_1A=new T(function(){return B(err(_1z));}),_1B=function(_1C,_1D,_1E){while(1){if(!(_1D%2)){var _1F=_1C*_1C,_1G=quot(_1D,2);_1C=_1F;_1D=_1G;continue;}else{var _1H=E(_1D);if(_1H==1){return _1C*_1E;}else{var _1F=_1C*_1C,_1I=_1C*_1E;_1C=_1F;_1D=quot(_1H-1|0,2);_1E=_1I;continue;}}}},_1J=function(_1K,_1L){while(1){if(!(_1L%2)){var _1M=_1K*_1K,_1N=quot(_1L,2);_1K=_1M;_1L=_1N;continue;}else{var _1O=E(_1L);if(_1O==1){return E(_1K);}else{return new F(function(){return _1B(_1K*_1K,quot(_1O-1|0,2),_1K);});}}}},_1P=function(_1Q){var _1R=E(_1Q);return new F(function(){return Math.log(_1R+(_1R+1)*Math.sqrt((_1R-1)/(_1R+1)));});},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return Math.log(_1U+Math.sqrt(1+_1U*_1U));});},_1V=function(_1W){var _1X=E(_1W);return 0.5*Math.log((1+_1X)/(1-_1X));},_1Y=function(_1Z,_20){return Math.log(E(_20))/Math.log(E(_1Z));},_21=3.141592653589793,_22=new T1(0,1),_23=function(_24,_25){var _26=E(_24);if(!_26._){var _27=_26.a,_28=E(_25);if(!_28._){var _29=_28.a;return (_27!=_29)?(_27>_29)?2:0:1;}else{var _2a=I_compareInt(_28.a,_27);return (_2a<=0)?(_2a>=0)?1:2:0;}}else{var _2b=_26.a,_2c=E(_25);if(!_2c._){var _2d=I_compareInt(_2b,_2c.a);return (_2d>=0)?(_2d<=0)?1:2:0;}else{var _2e=I_compare(_2b,_2c.a);return (_2e>=0)?(_2e<=0)?1:2:0;}}},_2f=new T(function(){return B(unCStr("base"));}),_2g=new T(function(){return B(unCStr("GHC.Exception"));}),_2h=new T(function(){return B(unCStr("ArithException"));}),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2f,_2g,_2h),_2j=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2i,_z,_z),_2k=function(_2l){return E(_2j);},_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r){var _2s=B(A1(_2p,_)),_2t=B(A1(_2q,_)),_2u=hs_eqWord64(_2s.a,_2t.a);if(!_2u){return __Z;}else{var _2v=hs_eqWord64(_2s.b,_2t.b);return (!_2v)?__Z:new T1(1,_2r);}},_2w=function(_2x){var _2y=E(_2x);return new F(function(){return _2o(B(_2m(_2y.a)),_2k,_2y.b);});},_2z=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2A=new T(function(){return B(unCStr("denormal"));}),_2B=new T(function(){return B(unCStr("divide by zero"));}),_2C=new T(function(){return B(unCStr("loss of precision"));}),_2D=new T(function(){return B(unCStr("arithmetic underflow"));}),_2E=new T(function(){return B(unCStr("arithmetic overflow"));}),_2F=function(_2G,_2H){switch(E(_2G)){case 0:return new F(function(){return _q(_2E,_2H);});break;case 1:return new F(function(){return _q(_2D,_2H);});break;case 2:return new F(function(){return _q(_2C,_2H);});break;case 3:return new F(function(){return _q(_2B,_2H);});break;case 4:return new F(function(){return _q(_2A,_2H);});break;default:return new F(function(){return _q(_2z,_2H);});}},_2I=function(_2J){return new F(function(){return _2F(_2J,_z);});},_2K=function(_2L,_2M,_2N){return new F(function(){return _2F(_2M,_2N);});},_2O=44,_2P=93,_2Q=91,_2R=function(_2S,_2T,_2U){var _2V=E(_2T);if(!_2V._){return new F(function(){return unAppCStr("[]",_2U);});}else{var _2W=new T(function(){var _2X=new T(function(){var _2Y=function(_2Z){var _30=E(_2Z);if(!_30._){return E(new T2(1,_2P,_2U));}else{var _31=new T(function(){return B(A2(_2S,_30.a,new T(function(){return B(_2Y(_30.b));})));});return new T2(1,_2O,_31);}};return B(_2Y(_2V.b));});return B(A2(_2S,_2V.a,_2X));});return new T2(1,_2Q,_2W);}},_32=function(_33,_34){return new F(function(){return _2R(_2F,_33,_34);});},_35=new T3(0,_2K,_2I,_32),_36=new T(function(){return new T5(0,_2k,_35,_37,_2w,_2I);}),_37=function(_38){return new T2(0,_36,_38);},_39=3,_3a=new T(function(){return B(_37(_39));}),_3b=new T(function(){return die(_3a);}),_3c=function(_3d,_3e){var _3f=E(_3d);return (_3f._==0)?_3f.a*Math.pow(2,_3e):I_toNumber(_3f.a)*Math.pow(2,_3e);},_3g=function(_3h,_3i){var _3j=E(_3h);if(!_3j._){var _3k=_3j.a,_3l=E(_3i);return (_3l._==0)?_3k==_3l.a:(I_compareInt(_3l.a,_3k)==0)?true:false;}else{var _3m=_3j.a,_3n=E(_3i);return (_3n._==0)?(I_compareInt(_3m,_3n.a)==0)?true:false:(I_compare(_3m,_3n.a)==0)?true:false;}},_3o=function(_3p){var _3q=E(_3p);if(!_3q._){return E(_3q.a);}else{return new F(function(){return I_toInt(_3q.a);});}},_3r=function(_3s,_3t){while(1){var _3u=E(_3s);if(!_3u._){var _3v=_3u.a,_3w=E(_3t);if(!_3w._){var _3x=_3w.a,_3y=addC(_3v,_3x);if(!E(_3y.b)){return new T1(0,_3y.a);}else{_3s=new T1(1,I_fromInt(_3v));_3t=new T1(1,I_fromInt(_3x));continue;}}else{_3s=new T1(1,I_fromInt(_3v));_3t=_3w;continue;}}else{var _3z=E(_3t);if(!_3z._){_3s=_3u;_3t=new T1(1,I_fromInt(_3z.a));continue;}else{return new T1(1,I_add(_3u.a,_3z.a));}}}},_3A=function(_3B,_3C){while(1){var _3D=E(_3B);if(!_3D._){var _3E=E(_3D.a);if(_3E==(-2147483648)){_3B=new T1(1,I_fromInt(-2147483648));continue;}else{var _3F=E(_3C);if(!_3F._){var _3G=_3F.a;return new T2(0,new T1(0,quot(_3E,_3G)),new T1(0,_3E%_3G));}else{_3B=new T1(1,I_fromInt(_3E));_3C=_3F;continue;}}}else{var _3H=E(_3C);if(!_3H._){_3B=_3D;_3C=new T1(1,I_fromInt(_3H.a));continue;}else{var _3I=I_quotRem(_3D.a,_3H.a);return new T2(0,new T1(1,_3I.a),new T1(1,_3I.b));}}}},_3J=new T1(0,0),_3K=function(_3L,_3M){while(1){var _3N=E(_3L);if(!_3N._){_3L=new T1(1,I_fromInt(_3N.a));continue;}else{return new T1(1,I_shiftLeft(_3N.a,_3M));}}},_3O=function(_3P,_3Q,_3R){if(!B(_3g(_3R,_3J))){var _3S=B(_3A(_3Q,_3R)),_3T=_3S.a;switch(B(_23(B(_3K(_3S.b,1)),_3R))){case 0:return new F(function(){return _3c(_3T,_3P);});break;case 1:if(!(B(_3o(_3T))&1)){return new F(function(){return _3c(_3T,_3P);});}else{return new F(function(){return _3c(B(_3r(_3T,_22)),_3P);});}break;default:return new F(function(){return _3c(B(_3r(_3T,_22)),_3P);});}}else{return E(_3b);}},_3U=function(_3V,_3W){var _3X=E(_3V);if(!_3X._){var _3Y=_3X.a,_3Z=E(_3W);return (_3Z._==0)?_3Y>_3Z.a:I_compareInt(_3Z.a,_3Y)<0;}else{var _40=_3X.a,_41=E(_3W);return (_41._==0)?I_compareInt(_40,_41.a)>0:I_compare(_40,_41.a)>0;}},_42=new T1(0,1),_43=new T(function(){return B(unCStr("base"));}),_44=new T(function(){return B(unCStr("Control.Exception.Base"));}),_45=new T(function(){return B(unCStr("PatternMatchFail"));}),_46=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_43,_44,_45),_47=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_46,_z,_z),_48=function(_49){return E(_47);},_4a=function(_4b){var _4c=E(_4b);return new F(function(){return _2o(B(_2m(_4c.a)),_48,_4c.b);});},_4d=function(_4e){return E(E(_4e).a);},_4f=function(_4g){return new T2(0,_4h,_4g);},_4i=function(_4j,_4k){return new F(function(){return _q(E(_4j).a,_4k);});},_4l=function(_4m,_4n){return new F(function(){return _2R(_4i,_4m,_4n);});},_4o=function(_4p,_4q,_4r){return new F(function(){return _q(E(_4q).a,_4r);});},_4s=new T3(0,_4o,_4d,_4l),_4h=new T(function(){return new T5(0,_48,_4s,_4f,_4a,_4d);}),_4t=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4u=function(_4v){return E(E(_4v).c);},_4w=function(_4x,_4y){return new F(function(){return die(new T(function(){return B(A2(_4u,_4y,_4x));}));});},_4z=function(_4A,_38){return new F(function(){return _4w(_4A,_38);});},_4B=function(_4C,_4D){var _4E=E(_4D);if(!_4E._){return new T2(0,_z,_z);}else{var _4F=_4E.a;if(!B(A1(_4C,_4F))){return new T2(0,_z,_4E);}else{var _4G=new T(function(){var _4H=B(_4B(_4C,_4E.b));return new T2(0,_4H.a,_4H.b);});return new T2(0,new T2(1,_4F,new T(function(){return E(E(_4G).a);})),new T(function(){return E(E(_4G).b);}));}}},_4I=32,_4J=new T(function(){return B(unCStr("\n"));}),_4K=function(_4L){return (E(_4L)==124)?false:true;},_4M=function(_4N,_4O){var _4P=B(_4B(_4K,B(unCStr(_4N)))),_4Q=_4P.a,_4R=function(_4S,_4T){var _4U=new T(function(){var _4V=new T(function(){return B(_q(_4O,new T(function(){return B(_q(_4T,_4J));},1)));});return B(unAppCStr(": ",_4V));},1);return new F(function(){return _q(_4S,_4U);});},_4W=E(_4P.b);if(!_4W._){return new F(function(){return _4R(_4Q,_z);});}else{if(E(_4W.a)==124){return new F(function(){return _4R(_4Q,new T2(1,_4I,_4W.b));});}else{return new F(function(){return _4R(_4Q,_z);});}}},_4X=function(_4Y){return new F(function(){return _4z(new T1(0,new T(function(){return B(_4M(_4Y,_4t));})),_4h);});},_4Z=function(_50){var _51=function(_52,_53){while(1){if(!B(_Q(_52,_50))){if(!B(_3U(_52,_50))){if(!B(_3g(_52,_50))){return new F(function(){return _4X("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_53);}}else{return _53-1|0;}}else{var _54=B(_3K(_52,1)),_55=_53+1|0;_52=_54;_53=_55;continue;}}};return new F(function(){return _51(_42,0);});},_56=function(_57){var _58=E(_57);if(!_58._){var _59=_58.a>>>0;if(!_59){return -1;}else{var _5a=function(_5b,_5c){while(1){if(_5b>=_59){if(_5b<=_59){if(_5b!=_59){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5c);}}else{return _5c-1|0;}}else{var _5d=imul(_5b,2)>>>0,_5e=_5c+1|0;_5b=_5d;_5c=_5e;continue;}}};return new F(function(){return _5a(1,0);});}}else{return new F(function(){return _4Z(_58);});}},_5f=function(_5g){var _5h=E(_5g);if(!_5h._){var _5i=_5h.a>>>0;if(!_5i){return new T2(0,-1,0);}else{var _5j=function(_5k,_5l){while(1){if(_5k>=_5i){if(_5k<=_5i){if(_5k!=_5i){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5l);}}else{return _5l-1|0;}}else{var _5m=imul(_5k,2)>>>0,_5n=_5l+1|0;_5k=_5m;_5l=_5n;continue;}}};return new T2(0,B(_5j(1,0)),(_5i&_5i-1>>>0)>>>0&4294967295);}}else{var _5o=_5h.a;return new T2(0,B(_56(_5h)),I_compareInt(I_and(_5o,I_sub(_5o,I_fromInt(1))),0));}},_5p=function(_5q,_5r){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);return (_5u._==0)?_5t<=_5u.a:I_compareInt(_5u.a,_5t)>=0;}else{var _5v=_5s.a,_5w=E(_5r);return (_5w._==0)?I_compareInt(_5v,_5w.a)<=0:I_compare(_5v,_5w.a)<=0;}},_5x=function(_5y,_5z){while(1){var _5A=E(_5y);if(!_5A._){var _5B=_5A.a,_5C=E(_5z);if(!_5C._){return new T1(0,(_5B>>>0&_5C.a>>>0)>>>0&4294967295);}else{_5y=new T1(1,I_fromInt(_5B));_5z=_5C;continue;}}else{var _5D=E(_5z);if(!_5D._){_5y=_5A;_5z=new T1(1,I_fromInt(_5D.a));continue;}else{return new T1(1,I_and(_5A.a,_5D.a));}}}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){var _5K=_5J.a,_5L=subC(_5I,_5K);if(!E(_5L.b)){return new T1(0,_5L.a);}else{_5F=new T1(1,I_fromInt(_5I));_5G=new T1(1,I_fromInt(_5K));continue;}}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5M=E(_5G);if(!_5M._){_5F=_5H;_5G=new T1(1,I_fromInt(_5M.a));continue;}else{return new T1(1,I_sub(_5H.a,_5M.a));}}}},_5N=new T1(0,2),_5O=function(_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=(_5R.a>>>0&(2<<_5Q>>>0)-1>>>0)>>>0,_5T=1<<_5Q>>>0;return (_5T<=_5S)?(_5T>=_5S)?1:2:0;}else{var _5U=B(_5x(_5R,B(_5E(B(_3K(_5N,_5Q)),_42)))),_5V=B(_3K(_42,_5Q));return (!B(_3U(_5V,_5U)))?(!B(_Q(_5V,_5U)))?1:2:0;}},_5W=function(_5X,_5Y){while(1){var _5Z=E(_5X);if(!_5Z._){_5X=new T1(1,I_fromInt(_5Z.a));continue;}else{return new T1(1,I_shiftRight(_5Z.a,_5Y));}}},_60=function(_61,_62,_63,_64){var _65=B(_5f(_64)),_66=_65.a;if(!E(_65.b)){var _67=B(_56(_63));if(_67<((_66+_61|0)-1|0)){var _68=_66+(_61-_62|0)|0;if(_68>0){if(_68>_67){if(_68<=(_67+1|0)){if(!E(B(_5f(_63)).b)){return 0;}else{return new F(function(){return _3c(_22,_61-_62|0);});}}else{return 0;}}else{var _69=B(_5W(_63,_68));switch(B(_5O(_63,_68-1|0))){case 0:return new F(function(){return _3c(_69,_61-_62|0);});break;case 1:if(!(B(_3o(_69))&1)){return new F(function(){return _3c(_69,_61-_62|0);});}else{return new F(function(){return _3c(B(_3r(_69,_22)),_61-_62|0);});}break;default:return new F(function(){return _3c(B(_3r(_69,_22)),_61-_62|0);});}}}else{return new F(function(){return _3c(_63,(_61-_62|0)-_68|0);});}}else{if(_67>=_62){var _6a=B(_5W(_63,(_67+1|0)-_62|0));switch(B(_5O(_63,_67-_62|0))){case 0:return new F(function(){return _3c(_6a,((_67-_66|0)+1|0)-_62|0);});break;case 2:return new F(function(){return _3c(B(_3r(_6a,_22)),((_67-_66|0)+1|0)-_62|0);});break;default:if(!(B(_3o(_6a))&1)){return new F(function(){return _3c(_6a,((_67-_66|0)+1|0)-_62|0);});}else{return new F(function(){return _3c(B(_3r(_6a,_22)),((_67-_66|0)+1|0)-_62|0);});}}}else{return new F(function(){return _3c(_63, -_66);});}}}else{var _6b=B(_56(_63))-_66|0,_6c=function(_6d){var _6e=function(_6f,_6g){if(!B(_5p(B(_3K(_6g,_62)),_6f))){return new F(function(){return _3O(_6d-_62|0,_6f,_6g);});}else{return new F(function(){return _3O((_6d-_62|0)+1|0,_6f,B(_3K(_6g,1)));});}};if(_6d>=_62){if(_6d!=_62){return new F(function(){return _6e(_63,new T(function(){return B(_3K(_64,_6d-_62|0));}));});}else{return new F(function(){return _6e(_63,_64);});}}else{return new F(function(){return _6e(new T(function(){return B(_3K(_63,_62-_6d|0));}),_64);});}};if(_61>_6b){return new F(function(){return _6c(_61);});}else{return new F(function(){return _6c(_6b);});}}},_6h=new T1(0,2147483647),_6i=new T(function(){return B(_3r(_6h,_42));}),_6j=function(_6k){var _6l=E(_6k);if(!_6l._){var _6m=E(_6l.a);return (_6m==(-2147483648))?E(_6i):new T1(0, -_6m);}else{return new T1(1,I_negate(_6l.a));}},_6n=new T(function(){return 0/0;}),_6o=new T(function(){return -1/0;}),_6p=new T(function(){return 1/0;}),_6q=0,_6r=function(_6s,_6t){if(!B(_3g(_6t,_3J))){if(!B(_3g(_6s,_3J))){if(!B(_Q(_6s,_3J))){return new F(function(){return _60(-1021,53,_6s,_6t);});}else{return  -B(_60(-1021,53,B(_6j(_6s)),_6t));}}else{return E(_6q);}}else{return (!B(_3g(_6s,_3J)))?(!B(_Q(_6s,_3J)))?E(_6p):E(_6o):E(_6n);}},_6u=function(_6v){var _6w=E(_6v);return new F(function(){return _6r(_6w.a,_6w.b);});},_6x=function(_6y){return 1/E(_6y);},_6z=function(_6A){var _6B=E(_6A),_6C=E(_6B);return (_6C==0)?E(_6q):(_6C<=0)? -_6C:E(_6B);},_6D=function(_6E){var _6F=E(_6E);if(!_6F._){return _6F.a;}else{return new F(function(){return I_toNumber(_6F.a);});}},_6G=function(_6H){return new F(function(){return _6D(_6H);});},_6I=1,_6J=-1,_6K=function(_6L){var _6M=E(_6L);return (_6M<=0)?(_6M>=0)?E(_6M):E(_6J):E(_6I);},_6N=function(_6O,_6P){return E(_6O)-E(_6P);},_6Q=function(_6R){return  -E(_6R);},_6S=function(_6T,_6U){return E(_6T)+E(_6U);},_6V=function(_6W,_6X){return E(_6W)*E(_6X);},_6Y={_:0,a:_6S,b:_6N,c:_6V,d:_6Q,e:_6z,f:_6K,g:_6G},_6Z=function(_70,_71){return E(_70)/E(_71);},_72=new T4(0,_6Y,_6Z,_6x,_6u),_73=function(_74){return new F(function(){return Math.acos(E(_74));});},_75=function(_76){return new F(function(){return Math.asin(E(_76));});},_77=function(_78){return new F(function(){return Math.atan(E(_78));});},_79=function(_7a){return new F(function(){return Math.cos(E(_7a));});},_7b=function(_7c){return new F(function(){return cosh(E(_7c));});},_7d=function(_7e){return new F(function(){return Math.exp(E(_7e));});},_7f=function(_7g){return new F(function(){return Math.log(E(_7g));});},_7h=function(_7i,_7j){return new F(function(){return Math.pow(E(_7i),E(_7j));});},_7k=function(_7l){return new F(function(){return Math.sin(E(_7l));});},_7m=function(_7n){return new F(function(){return sinh(E(_7n));});},_7o=function(_7p){return new F(function(){return Math.sqrt(E(_7p));});},_7q=function(_7r){return new F(function(){return Math.tan(E(_7r));});},_7s=function(_7t){return new F(function(){return tanh(E(_7t));});},_7u={_:0,a:_72,b:_21,c:_7d,d:_7f,e:_7o,f:_7h,g:_1Y,h:_7k,i:_79,j:_7q,k:_75,l:_73,m:_77,n:_7m,o:_7b,p:_7s,q:_1S,r:_1P,s:_1V},_7v=function(_7w,_7x){return (E(_7w)!=E(_7x))?true:false;},_7y=function(_7z,_7A){return E(_7z)==E(_7A);},_7B=new T2(0,_7y,_7v),_7C=function(_7D,_7E){return E(_7D)<E(_7E);},_7F=function(_7G,_7H){return E(_7G)<=E(_7H);},_7I=function(_7J,_7K){return E(_7J)>E(_7K);},_7L=function(_7M,_7N){return E(_7M)>=E(_7N);},_7O=function(_7P,_7Q){var _7R=E(_7P),_7S=E(_7Q);return (_7R>=_7S)?(_7R!=_7S)?2:1:0;},_7T=function(_7U,_7V){var _7W=E(_7U),_7X=E(_7V);return (_7W>_7X)?E(_7W):E(_7X);},_7Y=function(_7Z,_80){var _81=E(_7Z),_82=E(_80);return (_81>_82)?E(_82):E(_81);},_83={_:0,a:_7B,b:_7O,c:_7C,d:_7F,e:_7I,f:_7L,g:_7T,h:_7Y},_84="dz",_85="wy",_86="wx",_87="dy",_88="dx",_89="t",_8a="a",_8b="r",_8c="ly",_8d="lx",_8e="wz",_8f=0,_8g=function(_8h){var _8i=__new(),_8j=_8i,_8k=function(_8l,_){while(1){var _8m=E(_8l);if(!_8m._){return _8f;}else{var _8n=E(_8m.a),_8o=__set(_8j,E(_8n.a),E(_8n.b));_8l=_8m.b;continue;}}},_8p=B(_8k(_8h,_));return E(_8j);},_8q=function(_8r,_8s,_8t,_8u,_8v,_8w,_8x,_8y,_8z){return new F(function(){return _8g(new T2(1,new T2(0,_86,_8r),new T2(1,new T2(0,_85,_8s),new T2(1,new T2(0,_8e,_8t),new T2(1,new T2(0,_8d,_8u*_8v*Math.cos(_8w)),new T2(1,new T2(0,_8c,_8u*_8v*Math.sin(_8w)),new T2(1,new T2(0,_8b,_8u),new T2(1,new T2(0,_8a,_8v),new T2(1,new T2(0,_89,_8w),new T2(1,new T2(0,_88,_8x),new T2(1,new T2(0,_87,_8y),new T2(1,new T2(0,_84,_8z),_z))))))))))));});},_8A=function(_8B){var _8C=E(_8B),_8D=E(_8C.a),_8E=E(_8C.b),_8F=E(_8C.d);return new F(function(){return _8q(_8D.a,_8D.b,_8D.c,E(_8E.a),E(_8E.b),E(_8C.c),_8F.a,_8F.b,_8F.c);});},_8G=function(_8H,_8I){var _8J=E(_8I);return (_8J._==0)?__Z:new T2(1,new T(function(){return B(A1(_8H,_8J.a));}),new T(function(){return B(_8G(_8H,_8J.b));}));},_8K=function(_8L,_8M,_8N){var _8O=__lst2arr(B(_8G(_8A,new T2(1,_8L,new T2(1,_8M,new T2(1,_8N,_z))))));return E(_8O);},_8P=function(_8Q){var _8R=E(_8Q);return new F(function(){return _8K(_8R.a,_8R.b,_8R.c);});},_8S=new T2(0,_7u,_83),_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).a);},_8X=function(_8Y){return E(E(_8Y).c);},_8Z=function(_90){return E(E(_90).a);},_91=function(_92,_93,_94,_95,_96,_97,_98){var _99=B(_8V(B(_8T(_92)))),_9a=new T(function(){return B(A3(_8Z,_99,new T(function(){return B(A3(_8X,_99,_93,_96));}),new T(function(){return B(A3(_8X,_99,_94,_97));})));});return new F(function(){return A3(_8Z,_99,_9a,new T(function(){return B(A3(_8X,_99,_95,_98));}));});},_9b=function(_9c){return E(E(_9c).b);},_9d=function(_9e){return E(E(_9e).e);},_9f=function(_9g,_9h,_9i,_9j){var _9k=B(_8T(_9g)),_9l=new T(function(){return B(A2(_9d,_9g,new T(function(){return B(_91(_9g,_9h,_9i,_9j,_9h,_9i,_9j));})));});return new T3(0,B(A3(_9b,_9k,_9h,_9l)),B(A3(_9b,_9k,_9i,_9l)),B(A3(_9b,_9k,_9j,_9l)));},_9m=function(_9n,_9o,_9p,_9q,_9r,_9s,_9t){var _9u=B(_8X(_9n));return new T3(0,B(A1(B(A1(_9u,_9o)),_9r)),B(A1(B(A1(_9u,_9p)),_9s)),B(A1(B(A1(_9u,_9q)),_9t)));},_9v=function(_9w,_9x,_9y,_9z,_9A,_9B,_9C){var _9D=B(_8Z(_9w));return new T3(0,B(A1(B(A1(_9D,_9x)),_9A)),B(A1(B(A1(_9D,_9y)),_9B)),B(A1(B(A1(_9D,_9z)),_9C)));},_9E=function(_9F){return E(E(_9F).g);},_9G=function(_9H){return E(E(_9H).d);},_9I=function(_9J,_9K){var _9L=new T(function(){return E(E(_9J).a);}),_9M=new T(function(){var _9N=E(_9K),_9O=new T(function(){return B(_8V(new T(function(){return B(_8T(_9L));})));}),_9P=B(A2(_9E,_9O,_18));return new T3(0,E(_9P),E(B(A2(_9E,_9O,_J))),E(_9P));}),_9Q=new T(function(){var _9R=E(_9M),_9S=B(_9f(_9L,_9R.a,_9R.b,_9R.c));return new T3(0,E(_9S.a),E(_9S.b),E(_9S.c));}),_9T=new T(function(){var _9U=E(_9K),_9V=_9U.b,_9W=E(_9Q),_9X=B(_8T(_9L)),_9Y=new T(function(){return B(A2(_9d,_9L,new T(function(){var _9Z=E(_9M),_a0=_9Z.a,_a1=_9Z.b,_a2=_9Z.c;return B(_91(_9L,_a0,_a1,_a2,_a0,_a1,_a2));})));}),_a3=B(A3(_9b,_9X,_9V,_9Y)),_a4=B(_8V(_9X)),_a5=B(_9m(_a4,_9W.a,_9W.b,_9W.c,_a3,_a3,_a3)),_a6=B(_9G(_a4)),_a7=B(_9v(_a4,_9U.a,_9V,_9U.c,B(A1(_a6,_a5.a)),B(A1(_a6,_a5.b)),B(A1(_a6,_a5.c))));return new T3(0,E(_a7.a),E(_a7.b),E(_a7.c));});return new T2(0,_9T,_9Q);},_a8=function(_a9){return E(E(_a9).a);},_aa=function(_ab,_ac,_ad,_ae,_af,_ag,_ah){var _ai=B(_91(_ab,_af,_ag,_ah,_ac,_ad,_ae)),_aj=B(_8V(B(_8T(_ab)))),_ak=B(_9m(_aj,_af,_ag,_ah,_ai,_ai,_ai)),_al=B(_9G(_aj));return new F(function(){return _9v(_aj,_ac,_ad,_ae,B(A1(_al,_ak.a)),B(A1(_al,_ak.b)),B(A1(_al,_ak.c)));});},_am=function(_an){return E(E(_an).a);},_ao=function(_ap,_aq,_ar,_as){var _at=new T(function(){var _au=E(_as),_av=E(_ar),_aw=B(_aa(_ap,_au.a,_au.b,_au.c,_av.a,_av.b,_av.c));return new T3(0,E(_aw.a),E(_aw.b),E(_aw.c));}),_ax=new T(function(){return B(A2(_9d,_ap,new T(function(){var _ay=E(_at),_az=_ay.a,_aA=_ay.b,_aB=_ay.c;return B(_91(_ap,_az,_aA,_aB,_az,_aA,_aB));})));});if(!B(A3(_am,B(_a8(_aq)),_ax,new T(function(){return B(A2(_9E,B(_8V(B(_8T(_ap)))),_18));})))){var _aC=E(_at),_aD=B(_9f(_ap,_aC.a,_aC.b,_aC.c)),_aE=B(A2(_9d,_ap,new T(function(){var _aF=E(_as),_aG=_aF.a,_aH=_aF.b,_aI=_aF.c;return B(_91(_ap,_aG,_aH,_aI,_aG,_aH,_aI));}))),_aJ=B(_8X(new T(function(){return B(_8V(new T(function(){return B(_8T(_ap));})));})));return new T3(0,B(A1(B(A1(_aJ,_aD.a)),_aE)),B(A1(B(A1(_aJ,_aD.b)),_aE)),B(A1(B(A1(_aJ,_aD.c)),_aE)));}else{var _aK=B(A2(_9E,B(_8V(B(_8T(_ap)))),_18));return new T3(0,_aK,_aK,_aK);}},_aL=new T(function(){var _aM=eval("angleCount"),_aN=Number(_aM);return jsTrunc(_aN);}),_aO=new T(function(){return E(_aL);}),_aP=new T(function(){return B(unCStr(": empty list"));}),_aQ=new T(function(){return B(unCStr("Prelude."));}),_aR=function(_aS){return new F(function(){return err(B(_q(_aQ,new T(function(){return B(_q(_aS,_aP));},1))));});},_aT=new T(function(){return B(unCStr("head"));}),_aU=new T(function(){return B(_aR(_aT));}),_aV=function(_aW,_aX,_aY){var _aZ=E(_aW);if(!_aZ._){return __Z;}else{var _b0=E(_aX);if(!_b0._){return __Z;}else{var _b1=_b0.a,_b2=E(_aY);if(!_b2._){return __Z;}else{var _b3=E(_b2.a),_b4=_b3.a;return new F(function(){return _q(new T2(1,new T(function(){return new T3(0,E(_aZ.a),E(_b1),E(_b4));}),new T2(1,new T(function(){return new T3(0,E(_b1),E(_b4),E(_b3.b));}),_z)),new T(function(){return B(_aV(_aZ.b,_b0.b,_b2.b));},1));});}}}},_b5=new T(function(){return B(unCStr("tail"));}),_b6=new T(function(){return B(_aR(_b5));}),_b7=function(_b8,_b9){var _ba=E(_b8);if(!_ba._){return __Z;}else{var _bb=E(_b9);return (_bb._==0)?__Z:new T2(1,new T2(0,_ba.a,_bb.a),new T(function(){return B(_b7(_ba.b,_bb.b));}));}},_bc=function(_bd,_be){var _bf=E(_bd);if(!_bf._){return __Z;}else{var _bg=E(_be);if(!_bg._){return __Z;}else{var _bh=E(_bf.a),_bi=_bh.b,_bj=E(_bg.a).b,_bk=new T(function(){var _bl=new T(function(){return B(_b7(_bj,new T(function(){var _bm=E(_bj);if(!_bm._){return E(_b6);}else{return E(_bm.b);}},1)));},1);return B(_aV(_bi,new T(function(){var _bn=E(_bi);if(!_bn._){return E(_b6);}else{return E(_bn.b);}},1),_bl));});return new F(function(){return _q(new T2(1,new T(function(){var _bo=E(_bi);if(!_bo._){return E(_aU);}else{var _bp=E(_bj);if(!_bp._){return E(_aU);}else{return new T3(0,E(_bh.a),E(_bo.a),E(_bp.a));}}}),_bk),new T(function(){return B(_bc(_bf.b,_bg.b));},1));});}}},_bq=new T(function(){return E(_aO)-1;}),_br=new T1(0,1),_bs=function(_bt,_bu){var _bv=E(_bu),_bw=new T(function(){var _bx=B(_8V(_bt)),_by=B(_bs(_bt,B(A3(_8Z,_bx,_bv,new T(function(){return B(A2(_9E,_bx,_br));})))));return new T2(1,_by.a,_by.b);});return new T2(0,_bv,_bw);},_bz=function(_bA){return E(E(_bA).d);},_bB=new T1(0,2),_bC=function(_bD,_bE){var _bF=E(_bE);if(!_bF._){return __Z;}else{var _bG=_bF.a;return (!B(A1(_bD,_bG)))?__Z:new T2(1,_bG,new T(function(){return B(_bC(_bD,_bF.b));}));}},_bH=function(_bI,_bJ,_bK,_bL){var _bM=B(_bs(_bJ,_bK)),_bN=new T(function(){var _bO=B(_8V(_bJ)),_bP=new T(function(){return B(A3(_9b,_bJ,new T(function(){return B(A2(_9E,_bO,_br));}),new T(function(){return B(A2(_9E,_bO,_bB));})));});return B(A3(_8Z,_bO,_bL,_bP));});return new F(function(){return _bC(function(_bQ){return new F(function(){return A3(_bz,_bI,_bQ,_bN);});},new T2(1,_bM.a,_bM.b));});},_bR=new T(function(){return B(_bH(_83,_72,_1x,_bq));}),_bS=function(_bT,_bU){while(1){var _bV=E(_bT);if(!_bV._){return E(_bU);}else{_bT=_bV.b;_bU=_bV.a;continue;}}},_bW=new T(function(){return B(unCStr("last"));}),_bX=new T(function(){return B(_aR(_bW));}),_bY=function(_bZ){return new F(function(){return _bS(_bZ,_bX);});},_c0=function(_c1){return new F(function(){return _bY(E(_c1).b);});},_c2=new T(function(){var _c3=eval("proceedCount"),_c4=Number(_c3);return jsTrunc(_c4);}),_c5=new T(function(){return E(_c2);}),_c6=1,_c7=new T(function(){return B(_bH(_83,_72,_c6,_c5));}),_c8=function(_c9,_ca,_cb,_cc,_cd,_ce,_cf,_cg,_ch,_ci,_cj,_ck,_cl,_cm){var _cn=new T(function(){var _co=new T(function(){var _cp=E(_ci),_cq=E(_cm),_cr=E(_cl),_cs=E(_cj),_ct=E(_ck),_cu=E(_ch);return new T3(0,_cp*_cq-_cr*_cs,_cs*_ct-_cq*_cu,_cu*_cr-_ct*_cp);}),_cv=function(_cw){var _cx=new T(function(){var _cy=E(_cw)/E(_aO);return (_cy+_cy)*3.141592653589793;}),_cz=new T(function(){return B(A1(_c9,_cx));}),_cA=new T(function(){var _cB=new T(function(){var _cC=E(_cz)/E(_c5);return new T3(0,E(_cC),E(_cC),E(_cC));}),_cD=function(_cE,_cF){var _cG=E(_cE);if(!_cG._){return new T2(0,_z,_cF);}else{var _cH=new T(function(){var _cI=B(_9I(_8S,new T(function(){var _cJ=E(_cF),_cK=E(_cJ.a),_cL=E(_cJ.b),_cM=E(_cB);return new T3(0,E(_cK.a)+E(_cL.a)*E(_cM.a),E(_cK.b)+E(_cL.b)*E(_cM.b),E(_cK.c)+E(_cL.c)*E(_cM.c));}))),_cN=_cI.a,_cO=new T(function(){var _cP=E(_cI.b),_cQ=E(E(_cF).b),_cR=B(_aa(_7u,_cQ.a,_cQ.b,_cQ.c,_cP.a,_cP.b,_cP.c)),_cS=B(_9f(_7u,_cR.a,_cR.b,_cR.c));return new T3(0,E(_cS.a),E(_cS.b),E(_cS.c));});return new T2(0,new T(function(){var _cT=E(_cz),_cU=E(_cx);return new T4(0,E(_cN),E(new T2(0,E(_cG.a)/E(_c5),E(_cT))),E(_cU),E(_cO));}),new T2(0,_cN,_cO));}),_cV=new T(function(){var _cW=B(_cD(_cG.b,new T(function(){return E(E(_cH).b);})));return new T2(0,_cW.a,_cW.b);});return new T2(0,new T2(1,new T(function(){return E(E(_cH).a);}),new T(function(){return E(E(_cV).a);})),new T(function(){return E(E(_cV).b);}));}},_cX=function(_cY,_cZ,_d0,_d1,_d2){var _d3=E(_cY);if(!_d3._){return new T2(0,_z,new T2(0,new T3(0,E(_cZ),E(_d0),E(_d1)),_d2));}else{var _d4=new T(function(){var _d5=B(_9I(_8S,new T(function(){var _d6=E(_d2),_d7=E(_cB);return new T3(0,E(_cZ)+E(_d6.a)*E(_d7.a),E(_d0)+E(_d6.b)*E(_d7.b),E(_d1)+E(_d6.c)*E(_d7.c));}))),_d8=_d5.a,_d9=new T(function(){var _da=E(_d5.b),_db=E(_d2),_dc=B(_aa(_7u,_db.a,_db.b,_db.c,_da.a,_da.b,_da.c)),_dd=B(_9f(_7u,_dc.a,_dc.b,_dc.c));return new T3(0,E(_dd.a),E(_dd.b),E(_dd.c));});return new T2(0,new T(function(){var _de=E(_cz),_df=E(_cx);return new T4(0,E(_d8),E(new T2(0,E(_d3.a)/E(_c5),E(_de))),E(_df),E(_d9));}),new T2(0,_d8,_d9));}),_dg=new T(function(){var _dh=B(_cD(_d3.b,new T(function(){return E(E(_d4).b);})));return new T2(0,_dh.a,_dh.b);});return new T2(0,new T2(1,new T(function(){return E(E(_d4).a);}),new T(function(){return E(E(_dg).a);})),new T(function(){return E(E(_dg).b);}));}};return E(B(_cX(_c7,_cc,_cd,_ce,new T(function(){var _di=E(_co),_dj=E(_cx)+_cf,_dk=Math.cos(_dj),_dl=Math.sin(_dj);return new T3(0,E(_ch)*_dk+E(_di.a)*_dl,E(_ci)*_dk+E(_di.b)*_dl,E(_cj)*_dk+E(_di.c)*_dl);}))).a);});return new T2(0,new T(function(){var _dm=E(_cz),_dn=E(_cx);return new T4(0,E(new T3(0,E(_cc),E(_cd),E(_ce))),E(new T2(0,E(_1x),E(_dm))),E(_dn),E(_1y));}),_cA);};return B(_8G(_cv,_bR));}),_do=new T(function(){var _dp=new T(function(){var _dq=B(_q(_cn,new T2(1,new T(function(){var _dr=E(_cn);if(!_dr._){return E(_aU);}else{return E(_dr.a);}}),_z)));if(!_dq._){return E(_b6);}else{return E(_dq.b);}},1);return B(_bc(_cn,_dp));});return new T2(0,_do,new T(function(){return B(_8G(_c0,_cn));}));},_ds=function(_dt,_du,_dv,_dw,_dx,_dy,_dz,_dA,_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dI,_dJ){var _dK=B(_9I(_8S,new T3(0,E(_dw),E(_dx),E(_dy)))),_dL=_dK.b,_dM=E(_dK.a),_dN=B(_ao(_7u,_83,_dL,new T3(0,E(_dA),E(_dB),E(_dC)))),_dO=E(_dL),_dP=_dO.a,_dQ=_dO.b,_dR=_dO.c,_dS=B(_aa(_7u,_dE,_dF,_dG,_dP,_dQ,_dR)),_dT=B(_9f(_7u,_dS.a,_dS.b,_dS.c)),_dU=_dT.a,_dV=_dT.b,_dW=_dT.c,_dX=E(_dz),_dY=new T2(0,E(new T3(0,E(_dN.a),E(_dN.b),E(_dN.c))),E(_dD)),_dZ=B(_c8(_dt,_du,_dv,_dM.a,_dM.b,_dM.c,_dX,_dY,_dU,_dV,_dW,_dP,_dQ,_dR)),_e0=__lst2arr(B(_8G(_8P,_dZ.a))),_e1=__lst2arr(B(_8G(_8A,_dZ.b)));return {_:0,a:_dt,b:_du,c:_dv,d:new T2(0,E(_dM),E(_dX)),e:_dY,f:new T3(0,E(_dU),E(_dV),E(_dW)),g:_dO,h:_e0,i:_e1};},_e2=new T(function(){return 6.283185307179586/E(_aO);}),_e3=-1,_e4=0.5,_e5=new T3(0,E(_1x),E(_e4),E(_e3)),_e6=function(_){return new F(function(){return __jsNull();});},_e7=function(_e8){var _e9=B(A1(_e8,_));return E(_e9);},_ea=new T(function(){return B(_e7(_e6));}),_eb=function(_ec,_ed,_ee,_ef,_eg,_eh,_ei,_ej,_ek,_el,_em,_en,_eo){var _ep=function(_eq){var _er=E(_e2),_es=2+_eq|0,_et=_es-1|0,_eu=(2+_eq)*(1+_eq),_ev=E(_bR);if(!_ev._){return _er*0;}else{var _ew=_ev.a,_ex=_ev.b,_ey=B(A1(_ec,new T(function(){return 6.283185307179586*E(_ew)/E(_aO);}))),_ez=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_ew)+1)/E(_aO);})));if(_ey!=_ez){if(_es>=0){var _eA=E(_es);if(!_eA){var _eB=function(_eC,_eD){while(1){var _eE=B((function(_eF,_eG){var _eH=E(_eF);if(!_eH._){return E(_eG);}else{var _eI=_eH.a,_eJ=_eH.b,_eK=B(A1(_ec,new T(function(){return 6.283185307179586*E(_eI)/E(_aO);}))),_eL=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_eI)+1)/E(_aO);})));if(_eK!=_eL){var _eM=_eG+0/(_eK-_eL)/_eu;_eC=_eJ;_eD=_eM;return __continue;}else{if(_et>=0){var _eN=E(_et);if(!_eN){var _eM=_eG+_es/_eu;_eC=_eJ;_eD=_eM;return __continue;}else{var _eM=_eG+_es*B(_1J(_eK,_eN))/_eu;_eC=_eJ;_eD=_eM;return __continue;}}else{return E(_1A);}}}})(_eC,_eD));if(_eE!=__continue){return _eE;}}};return _er*B(_eB(_ex,0/(_ey-_ez)/_eu));}else{var _eO=function(_eP,_eQ){while(1){var _eR=B((function(_eS,_eT){var _eU=E(_eS);if(!_eU._){return E(_eT);}else{var _eV=_eU.a,_eW=_eU.b,_eX=B(A1(_ec,new T(function(){return 6.283185307179586*E(_eV)/E(_aO);}))),_eY=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_eV)+1)/E(_aO);})));if(_eX!=_eY){if(_eA>=0){var _eZ=_eT+(B(_1J(_eX,_eA))-B(_1J(_eY,_eA)))/(_eX-_eY)/_eu;_eP=_eW;_eQ=_eZ;return __continue;}else{return E(_1A);}}else{if(_et>=0){var _f0=E(_et);if(!_f0){var _eZ=_eT+_es/_eu;_eP=_eW;_eQ=_eZ;return __continue;}else{var _eZ=_eT+_es*B(_1J(_eX,_f0))/_eu;_eP=_eW;_eQ=_eZ;return __continue;}}else{return E(_1A);}}}})(_eP,_eQ));if(_eR!=__continue){return _eR;}}};return _er*B(_eO(_ex,(B(_1J(_ey,_eA))-B(_1J(_ez,_eA)))/(_ey-_ez)/_eu));}}else{return E(_1A);}}else{if(_et>=0){var _f1=E(_et);if(!_f1){var _f2=function(_f3,_f4){while(1){var _f5=B((function(_f6,_f7){var _f8=E(_f6);if(!_f8._){return E(_f7);}else{var _f9=_f8.a,_fa=_f8.b,_fb=B(A1(_ec,new T(function(){return 6.283185307179586*E(_f9)/E(_aO);}))),_fc=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_f9)+1)/E(_aO);})));if(_fb!=_fc){if(_es>=0){var _fd=E(_es);if(!_fd){var _fe=_f7+0/(_fb-_fc)/_eu;_f3=_fa;_f4=_fe;return __continue;}else{var _fe=_f7+(B(_1J(_fb,_fd))-B(_1J(_fc,_fd)))/(_fb-_fc)/_eu;_f3=_fa;_f4=_fe;return __continue;}}else{return E(_1A);}}else{var _fe=_f7+_es/_eu;_f3=_fa;_f4=_fe;return __continue;}}})(_f3,_f4));if(_f5!=__continue){return _f5;}}};return _er*B(_f2(_ex,_es/_eu));}else{var _ff=function(_fg,_fh){while(1){var _fi=B((function(_fj,_fk){var _fl=E(_fj);if(!_fl._){return E(_fk);}else{var _fm=_fl.a,_fn=_fl.b,_fo=B(A1(_ec,new T(function(){return 6.283185307179586*E(_fm)/E(_aO);}))),_fp=B(A1(_ec,new T(function(){return 6.283185307179586*(E(_fm)+1)/E(_aO);})));if(_fo!=_fp){if(_es>=0){var _fq=E(_es);if(!_fq){var _fr=_fk+0/(_fo-_fp)/_eu;_fg=_fn;_fh=_fr;return __continue;}else{var _fr=_fk+(B(_1J(_fo,_fq))-B(_1J(_fp,_fq)))/(_fo-_fp)/_eu;_fg=_fn;_fh=_fr;return __continue;}}else{return E(_1A);}}else{if(_f1>=0){var _fr=_fk+_es*B(_1J(_fo,_f1))/_eu;_fg=_fn;_fh=_fr;return __continue;}else{return E(_1A);}}}})(_fg,_fh));if(_fi!=__continue){return _fi;}}};return _er*B(_ff(_ex,_es*B(_1J(_ey,_f1))/_eu));}}else{return E(_1A);}}}},_fs=E(_ea),_ft=1/(B(_ep(1))*_ed);return new F(function(){return _ds(_ec,_e5,new T2(0,E(new T3(0,E(_ft),E(_ft),E(_ft))),1/(B(_ep(3))*_ed)),_ee,_ef,_eg,_eh,_ei,_ej,_ek,_el,_em,_en,_eo,_1y,_fs,_fs);});},_fu=function(_fv){var _fw=I_decodeDouble(_fv);return new T2(0,new T1(1,_fw.b),_fw.a);},_fx=function(_fy){return new T1(0,_fy);},_fz=function(_fA){var _fB=hs_intToInt64(2147483647),_fC=hs_leInt64(_fA,_fB);if(!_fC){return new T1(1,I_fromInt64(_fA));}else{var _fD=hs_intToInt64(-2147483648),_fE=hs_geInt64(_fA,_fD);if(!_fE){return new T1(1,I_fromInt64(_fA));}else{var _fF=hs_int64ToInt(_fA);return new F(function(){return _fx(_fF);});}}},_fG=new T(function(){var _fH=newByteArr(256),_fI=_fH,_=_fI["v"]["i8"][0]=8,_fJ=function(_fK,_fL,_fM,_){while(1){if(_fM>=256){if(_fK>=256){return E(_);}else{var _fN=imul(2,_fK)|0,_fO=_fL+1|0,_fP=_fK;_fK=_fN;_fL=_fO;_fM=_fP;continue;}}else{var _=_fI["v"]["i8"][_fM]=_fL,_fP=_fM+_fK|0;_fM=_fP;continue;}}},_=B(_fJ(2,0,1,_));return _fI;}),_fQ=function(_fR,_fS){var _fT=hs_int64ToInt(_fR),_fU=E(_fG),_fV=_fU["v"]["i8"][(255&_fT>>>0)>>>0&4294967295];if(_fS>_fV){if(_fV>=8){var _fW=hs_uncheckedIShiftRA64(_fR,8),_fX=function(_fY,_fZ){while(1){var _g0=B((function(_g1,_g2){var _g3=hs_int64ToInt(_g1),_g4=_fU["v"]["i8"][(255&_g3>>>0)>>>0&4294967295];if(_g2>_g4){if(_g4>=8){var _g5=hs_uncheckedIShiftRA64(_g1,8),_g6=_g2-8|0;_fY=_g5;_fZ=_g6;return __continue;}else{return new T2(0,new T(function(){var _g7=hs_uncheckedIShiftRA64(_g1,_g4);return B(_fz(_g7));}),_g2-_g4|0);}}else{return new T2(0,new T(function(){var _g8=hs_uncheckedIShiftRA64(_g1,_g2);return B(_fz(_g8));}),0);}})(_fY,_fZ));if(_g0!=__continue){return _g0;}}};return new F(function(){return _fX(_fW,_fS-8|0);});}else{return new T2(0,new T(function(){var _g9=hs_uncheckedIShiftRA64(_fR,_fV);return B(_fz(_g9));}),_fS-_fV|0);}}else{return new T2(0,new T(function(){var _ga=hs_uncheckedIShiftRA64(_fR,_fS);return B(_fz(_ga));}),0);}},_gb=function(_gc){var _gd=hs_intToInt64(_gc);return E(_gd);},_ge=function(_gf){var _gg=E(_gf);if(!_gg._){return new F(function(){return _gb(_gg.a);});}else{return new F(function(){return I_toInt64(_gg.a);});}},_gh=function(_gi){return I_toInt(_gi)>>>0;},_gj=function(_gk){var _gl=E(_gk);if(!_gl._){return _gl.a>>>0;}else{return new F(function(){return _gh(_gl.a);});}},_gm=function(_gn){var _go=B(_fu(_gn)),_gp=_go.a,_gq=_go.b;if(_gq<0){var _gr=function(_gs){if(!_gs){return new T2(0,E(_gp),B(_3K(_22, -_gq)));}else{var _gt=B(_fQ(B(_ge(_gp)), -_gq));return new T2(0,E(_gt.a),B(_3K(_22,_gt.b)));}};if(!((B(_gj(_gp))&1)>>>0)){return new F(function(){return _gr(1);});}else{return new F(function(){return _gr(0);});}}else{return new T2(0,B(_3K(_gp,_gq)),_22);}},_gu=function(_gv){var _gw=B(_gm(E(_gv)));return new T2(0,E(_gw.a),E(_gw.b));},_gx=new T3(0,_6Y,_83,_gu),_gy=function(_gz){return E(E(_gz).a);},_gA=function(_gB){return E(E(_gB).a);},_gC=function(_gD,_gE){if(_gD<=_gE){var _gF=function(_gG){return new T2(1,_gG,new T(function(){if(_gG!=_gE){return B(_gF(_gG+1|0));}else{return __Z;}}));};return new F(function(){return _gF(_gD);});}else{return __Z;}},_gH=function(_gI){return new F(function(){return _gC(E(_gI),2147483647);});},_gJ=function(_gK,_gL,_gM){if(_gM<=_gL){var _gN=new T(function(){var _gO=_gL-_gK|0,_gP=function(_gQ){return (_gQ>=(_gM-_gO|0))?new T2(1,_gQ,new T(function(){return B(_gP(_gQ+_gO|0));})):new T2(1,_gQ,_z);};return B(_gP(_gL));});return new T2(1,_gK,_gN);}else{return (_gM<=_gK)?new T2(1,_gK,_z):__Z;}},_gR=function(_gS,_gT,_gU){if(_gU>=_gT){var _gV=new T(function(){var _gW=_gT-_gS|0,_gX=function(_gY){return (_gY<=(_gU-_gW|0))?new T2(1,_gY,new T(function(){return B(_gX(_gY+_gW|0));})):new T2(1,_gY,_z);};return B(_gX(_gT));});return new T2(1,_gS,_gV);}else{return (_gU>=_gS)?new T2(1,_gS,_z):__Z;}},_gZ=function(_h0,_h1){if(_h1<_h0){return new F(function(){return _gJ(_h0,_h1,-2147483648);});}else{return new F(function(){return _gR(_h0,_h1,2147483647);});}},_h2=function(_h3,_h4){return new F(function(){return _gZ(E(_h3),E(_h4));});},_h5=function(_h6,_h7,_h8){if(_h7<_h6){return new F(function(){return _gJ(_h6,_h7,_h8);});}else{return new F(function(){return _gR(_h6,_h7,_h8);});}},_h9=function(_ha,_hb,_hc){return new F(function(){return _h5(E(_ha),E(_hb),E(_hc));});},_hd=function(_he,_hf){return new F(function(){return _gC(E(_he),E(_hf));});},_hg=function(_hh){return E(_hh);},_hi=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_hj=new T(function(){return B(err(_hi));}),_hk=function(_hl){var _hm=E(_hl);return (_hm==(-2147483648))?E(_hj):_hm-1|0;},_hn=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_ho=new T(function(){return B(err(_hn));}),_hp=function(_hq){var _hr=E(_hq);return (_hr==2147483647)?E(_ho):_hr+1|0;},_hs={_:0,a:_hp,b:_hk,c:_hg,d:_hg,e:_gH,f:_h2,g:_hd,h:_h9},_ht=function(_hu,_hv){if(_hu<=0){if(_hu>=0){return new F(function(){return quot(_hu,_hv);});}else{if(_hv<=0){return new F(function(){return quot(_hu,_hv);});}else{return quot(_hu+1|0,_hv)-1|0;}}}else{if(_hv>=0){if(_hu>=0){return new F(function(){return quot(_hu,_hv);});}else{if(_hv<=0){return new F(function(){return quot(_hu,_hv);});}else{return quot(_hu+1|0,_hv)-1|0;}}}else{return quot(_hu-1|0,_hv)-1|0;}}},_hw=0,_hx=new T(function(){return B(_37(_hw));}),_hy=new T(function(){return die(_hx);}),_hz=function(_hA,_hB){var _hC=E(_hB);switch(_hC){case -1:var _hD=E(_hA);if(_hD==(-2147483648)){return E(_hy);}else{return new F(function(){return _ht(_hD,-1);});}break;case 0:return E(_3b);default:return new F(function(){return _ht(_hA,_hC);});}},_hE=function(_hF,_hG){return new F(function(){return _hz(E(_hF),E(_hG));});},_hH=0,_hI=new T2(0,_hy,_hH),_hJ=function(_hK,_hL){var _hM=E(_hK),_hN=E(_hL);switch(_hN){case -1:var _hO=E(_hM);if(_hO==(-2147483648)){return E(_hI);}else{if(_hO<=0){if(_hO>=0){var _hP=quotRemI(_hO,-1);return new T2(0,_hP.a,_hP.b);}else{var _hQ=quotRemI(_hO,-1);return new T2(0,_hQ.a,_hQ.b);}}else{var _hR=quotRemI(_hO-1|0,-1);return new T2(0,_hR.a-1|0,(_hR.b+(-1)|0)+1|0);}}break;case 0:return E(_3b);default:if(_hM<=0){if(_hM>=0){var _hS=quotRemI(_hM,_hN);return new T2(0,_hS.a,_hS.b);}else{if(_hN<=0){var _hT=quotRemI(_hM,_hN);return new T2(0,_hT.a,_hT.b);}else{var _hU=quotRemI(_hM+1|0,_hN);return new T2(0,_hU.a-1|0,(_hU.b+_hN|0)-1|0);}}}else{if(_hN>=0){if(_hM>=0){var _hV=quotRemI(_hM,_hN);return new T2(0,_hV.a,_hV.b);}else{if(_hN<=0){var _hW=quotRemI(_hM,_hN);return new T2(0,_hW.a,_hW.b);}else{var _hX=quotRemI(_hM+1|0,_hN);return new T2(0,_hX.a-1|0,(_hX.b+_hN|0)-1|0);}}}else{var _hY=quotRemI(_hM-1|0,_hN);return new T2(0,_hY.a-1|0,(_hY.b+_hN|0)+1|0);}}}},_hZ=function(_i0,_i1){var _i2=_i0%_i1;if(_i0<=0){if(_i0>=0){return E(_i2);}else{if(_i1<=0){return E(_i2);}else{var _i3=E(_i2);return (_i3==0)?0:_i3+_i1|0;}}}else{if(_i1>=0){if(_i0>=0){return E(_i2);}else{if(_i1<=0){return E(_i2);}else{var _i4=E(_i2);return (_i4==0)?0:_i4+_i1|0;}}}else{var _i5=E(_i2);return (_i5==0)?0:_i5+_i1|0;}}},_i6=function(_i7,_i8){var _i9=E(_i8);switch(_i9){case -1:return E(_hH);case 0:return E(_3b);default:return new F(function(){return _hZ(E(_i7),_i9);});}},_ia=function(_ib,_ic){var _id=E(_ib),_ie=E(_ic);switch(_ie){case -1:var _if=E(_id);if(_if==(-2147483648)){return E(_hy);}else{return new F(function(){return quot(_if,-1);});}break;case 0:return E(_3b);default:return new F(function(){return quot(_id,_ie);});}},_ig=function(_ih,_ii){var _ij=E(_ih),_ik=E(_ii);switch(_ik){case -1:var _il=E(_ij);if(_il==(-2147483648)){return E(_hI);}else{var _im=quotRemI(_il,-1);return new T2(0,_im.a,_im.b);}break;case 0:return E(_3b);default:var _in=quotRemI(_ij,_ik);return new T2(0,_in.a,_in.b);}},_io=function(_ip,_iq){var _ir=E(_iq);switch(_ir){case -1:return E(_hH);case 0:return E(_3b);default:return E(_ip)%_ir;}},_is=function(_it){return new F(function(){return _fx(E(_it));});},_iu=function(_iv){return new T2(0,E(B(_fx(E(_iv)))),E(_br));},_iw=function(_ix,_iy){return imul(E(_ix),E(_iy))|0;},_iz=function(_iA,_iB){return E(_iA)+E(_iB)|0;},_iC=function(_iD,_iE){return E(_iD)-E(_iE)|0;},_iF=function(_iG){var _iH=E(_iG);return (_iH<0)? -_iH:E(_iH);},_iI=function(_iJ){return new F(function(){return _3o(_iJ);});},_iK=function(_iL){return  -E(_iL);},_iM=-1,_iN=0,_iO=1,_iP=function(_iQ){var _iR=E(_iQ);return (_iR>=0)?(E(_iR)==0)?E(_iN):E(_iO):E(_iM);},_iS={_:0,a:_iz,b:_iC,c:_iw,d:_iK,e:_iF,f:_iP,g:_iI},_iT=function(_iU,_iV){return E(_iU)==E(_iV);},_iW=function(_iX,_iY){return E(_iX)!=E(_iY);},_iZ=new T2(0,_iT,_iW),_j0=function(_j1,_j2){var _j3=E(_j1),_j4=E(_j2);return (_j3>_j4)?E(_j3):E(_j4);},_j5=function(_j6,_j7){var _j8=E(_j6),_j9=E(_j7);return (_j8>_j9)?E(_j9):E(_j8);},_ja=function(_jb,_jc){return (_jb>=_jc)?(_jb!=_jc)?2:1:0;},_jd=function(_je,_jf){return new F(function(){return _ja(E(_je),E(_jf));});},_jg=function(_jh,_ji){return E(_jh)>=E(_ji);},_jj=function(_jk,_jl){return E(_jk)>E(_jl);},_jm=function(_jn,_jo){return E(_jn)<=E(_jo);},_jp=function(_jq,_jr){return E(_jq)<E(_jr);},_js={_:0,a:_iZ,b:_jd,c:_jp,d:_jm,e:_jj,f:_jg,g:_j0,h:_j5},_jt=new T3(0,_iS,_js,_iu),_ju={_:0,a:_jt,b:_hs,c:_ia,d:_io,e:_hE,f:_i6,g:_ig,h:_hJ,i:_is},_jv=new T1(0,2),_jw=function(_jx,_jy){while(1){var _jz=E(_jx);if(!_jz._){var _jA=_jz.a,_jB=E(_jy);if(!_jB._){var _jC=_jB.a;if(!(imul(_jA,_jC)|0)){return new T1(0,imul(_jA,_jC)|0);}else{_jx=new T1(1,I_fromInt(_jA));_jy=new T1(1,I_fromInt(_jC));continue;}}else{_jx=new T1(1,I_fromInt(_jA));_jy=_jB;continue;}}else{var _jD=E(_jy);if(!_jD._){_jx=_jz;_jy=new T1(1,I_fromInt(_jD.a));continue;}else{return new T1(1,I_mul(_jz.a,_jD.a));}}}},_jE=function(_jF,_jG,_jH){while(1){if(!(_jG%2)){var _jI=B(_jw(_jF,_jF)),_jJ=quot(_jG,2);_jF=_jI;_jG=_jJ;continue;}else{var _jK=E(_jG);if(_jK==1){return new F(function(){return _jw(_jF,_jH);});}else{var _jI=B(_jw(_jF,_jF)),_jL=B(_jw(_jF,_jH));_jF=_jI;_jG=quot(_jK-1|0,2);_jH=_jL;continue;}}}},_jM=function(_jN,_jO){while(1){if(!(_jO%2)){var _jP=B(_jw(_jN,_jN)),_jQ=quot(_jO,2);_jN=_jP;_jO=_jQ;continue;}else{var _jR=E(_jO);if(_jR==1){return E(_jN);}else{return new F(function(){return _jE(B(_jw(_jN,_jN)),quot(_jR-1|0,2),_jN);});}}}},_jS=function(_jT){return E(E(_jT).b);},_jU=function(_jV){return E(E(_jV).b);},_jW=function(_jX){return E(E(_jX).c);},_jY=new T1(0,0),_jZ=function(_k0){return E(E(_k0).d);},_k1=function(_k2,_k3){var _k4=B(_gy(_k2)),_k5=new T(function(){return B(_gA(_k4));}),_k6=new T(function(){return B(A3(_jZ,_k2,_k3,new T(function(){return B(A2(_9E,_k5,_bB));})));});return new F(function(){return A3(_am,B(_a8(B(_jS(_k4)))),_k6,new T(function(){return B(A2(_9E,_k5,_jY));}));});},_k7=new T(function(){return B(unCStr("Negative exponent"));}),_k8=new T(function(){return B(err(_k7));}),_k9=function(_ka){return E(E(_ka).c);},_kb=function(_kc,_kd,_ke,_kf){var _kg=B(_gy(_kd)),_kh=new T(function(){return B(_gA(_kg));}),_ki=B(_jS(_kg));if(!B(A3(_jW,_ki,_kf,new T(function(){return B(A2(_9E,_kh,_jY));})))){if(!B(A3(_am,B(_a8(_ki)),_kf,new T(function(){return B(A2(_9E,_kh,_jY));})))){var _kj=new T(function(){return B(A2(_9E,_kh,_bB));}),_kk=new T(function(){return B(A2(_9E,_kh,_br));}),_kl=B(_a8(_ki)),_km=function(_kn,_ko,_kp){while(1){var _kq=B((function(_kr,_ks,_kt){if(!B(_k1(_kd,_ks))){if(!B(A3(_am,_kl,_ks,_kk))){var _ku=new T(function(){return B(A3(_k9,_kd,new T(function(){return B(A3(_jU,_kh,_ks,_kk));}),_kj));});_kn=new T(function(){return B(A3(_8X,_kc,_kr,_kr));});_ko=_ku;_kp=new T(function(){return B(A3(_8X,_kc,_kr,_kt));});return __continue;}else{return new F(function(){return A3(_8X,_kc,_kr,_kt);});}}else{var _kv=_kt;_kn=new T(function(){return B(A3(_8X,_kc,_kr,_kr));});_ko=new T(function(){return B(A3(_k9,_kd,_ks,_kj));});_kp=_kv;return __continue;}})(_kn,_ko,_kp));if(_kq!=__continue){return _kq;}}},_kw=function(_kx,_ky){while(1){var _kz=B((function(_kA,_kB){if(!B(_k1(_kd,_kB))){if(!B(A3(_am,_kl,_kB,_kk))){var _kC=new T(function(){return B(A3(_k9,_kd,new T(function(){return B(A3(_jU,_kh,_kB,_kk));}),_kj));});return new F(function(){return _km(new T(function(){return B(A3(_8X,_kc,_kA,_kA));}),_kC,_kA);});}else{return E(_kA);}}else{_kx=new T(function(){return B(A3(_8X,_kc,_kA,_kA));});_ky=new T(function(){return B(A3(_k9,_kd,_kB,_kj));});return __continue;}})(_kx,_ky));if(_kz!=__continue){return _kz;}}};return new F(function(){return _kw(_ke,_kf);});}else{return new F(function(){return A2(_9E,_kc,_br);});}}else{return E(_k8);}},_kD=new T(function(){return B(err(_k7));}),_kE=function(_kF,_kG){var _kH=B(_fu(_kG)),_kI=_kH.a,_kJ=_kH.b,_kK=new T(function(){return B(_gA(new T(function(){return B(_gy(_kF));})));});if(_kJ<0){var _kL= -_kJ;if(_kL>=0){var _kM=E(_kL);if(!_kM){var _kN=E(_br);}else{var _kN=B(_jM(_jv,_kM));}if(!B(_3g(_kN,_3J))){var _kO=B(_3A(_kI,_kN));return new T2(0,new T(function(){return B(A2(_9E,_kK,_kO.a));}),new T(function(){return B(_3c(_kO.b,_kJ));}));}else{return E(_3b);}}else{return E(_kD);}}else{var _kP=new T(function(){var _kQ=new T(function(){return B(_kb(_kK,_ju,new T(function(){return B(A2(_9E,_kK,_jv));}),_kJ));});return B(A3(_8X,_kK,new T(function(){return B(A2(_9E,_kK,_kI));}),_kQ));});return new T2(0,_kP,_6q);}},_kR=function(_kS,_kT){var _kU=B(_kE(_kS,E(_kT))),_kV=_kU.a;if(E(_kU.b)<=0){return E(_kV);}else{var _kW=B(_gA(B(_gy(_kS))));return new F(function(){return A3(_8Z,_kW,_kV,new T(function(){return B(A2(_9E,_kW,_22));}));});}},_kX=function(_kY,_kZ){var _l0=B(_kE(_kY,E(_kZ))),_l1=_l0.a;if(E(_l0.b)>=0){return E(_l1);}else{var _l2=B(_gA(B(_gy(_kY))));return new F(function(){return A3(_jU,_l2,_l1,new T(function(){return B(A2(_9E,_l2,_22));}));});}},_l3=function(_l4,_l5){var _l6=B(_kE(_l4,E(_l5)));return new T2(0,_l6.a,_l6.b);},_l7=function(_l8,_l9){var _la=B(_kE(_l8,_l9)),_lb=_la.a,_lc=E(_la.b),_ld=new T(function(){var _le=B(_gA(B(_gy(_l8))));if(_lc>=0){return B(A3(_8Z,_le,_lb,new T(function(){return B(A2(_9E,_le,_22));})));}else{return B(A3(_jU,_le,_lb,new T(function(){return B(A2(_9E,_le,_22));})));}}),_lf=function(_lg){var _lh=_lg-0.5;return (_lh>=0)?(E(_lh)==0)?(!B(_k1(_l8,_lb)))?E(_ld):E(_lb):E(_ld):E(_lb);},_li=E(_lc);if(!_li){return new F(function(){return _lf(0);});}else{if(_li<=0){var _lj= -_li-0.5;return (_lj>=0)?(E(_lj)==0)?(!B(_k1(_l8,_lb)))?E(_ld):E(_lb):E(_ld):E(_lb);}else{return new F(function(){return _lf(_li);});}}},_lk=function(_ll,_lm){return new F(function(){return _l7(_ll,E(_lm));});},_ln=function(_lo,_lp){return E(B(_kE(_lo,E(_lp))).a);},_lq={_:0,a:_gx,b:_72,c:_l3,d:_ln,e:_lk,f:_kR,g:_kX},_lr=new T1(0,1),_ls=function(_lt,_lu){var _lv=E(_lt);return new T2(0,_lv,new T(function(){var _lw=B(_ls(B(_3r(_lv,_lu)),_lu));return new T2(1,_lw.a,_lw.b);}));},_lx=function(_ly){var _lz=B(_ls(_ly,_lr));return new T2(1,_lz.a,_lz.b);},_lA=function(_lB,_lC){var _lD=B(_ls(_lB,new T(function(){return B(_5E(_lC,_lB));})));return new T2(1,_lD.a,_lD.b);},_lE=new T1(0,0),_lF=function(_lG,_lH){var _lI=E(_lG);if(!_lI._){var _lJ=_lI.a,_lK=E(_lH);return (_lK._==0)?_lJ>=_lK.a:I_compareInt(_lK.a,_lJ)<=0;}else{var _lL=_lI.a,_lM=E(_lH);return (_lM._==0)?I_compareInt(_lL,_lM.a)>=0:I_compare(_lL,_lM.a)>=0;}},_lN=function(_lO,_lP,_lQ){if(!B(_lF(_lP,_lE))){var _lR=function(_lS){return (!B(_Q(_lS,_lQ)))?new T2(1,_lS,new T(function(){return B(_lR(B(_3r(_lS,_lP))));})):__Z;};return new F(function(){return _lR(_lO);});}else{var _lT=function(_lU){return (!B(_3U(_lU,_lQ)))?new T2(1,_lU,new T(function(){return B(_lT(B(_3r(_lU,_lP))));})):__Z;};return new F(function(){return _lT(_lO);});}},_lV=function(_lW,_lX,_lY){return new F(function(){return _lN(_lW,B(_5E(_lX,_lW)),_lY);});},_lZ=function(_m0,_m1){return new F(function(){return _lN(_m0,_lr,_m1);});},_m2=function(_m3){return new F(function(){return _3o(_m3);});},_m4=function(_m5){return new F(function(){return _5E(_m5,_lr);});},_m6=function(_m7){return new F(function(){return _3r(_m7,_lr);});},_m8=function(_m9){return new F(function(){return _fx(E(_m9));});},_ma={_:0,a:_m6,b:_m4,c:_m8,d:_m2,e:_lx,f:_lA,g:_lZ,h:_lV},_mb=function(_mc,_md){while(1){var _me=E(_mc);if(!_me._){var _mf=E(_me.a);if(_mf==(-2147483648)){_mc=new T1(1,I_fromInt(-2147483648));continue;}else{var _mg=E(_md);if(!_mg._){return new T1(0,B(_ht(_mf,_mg.a)));}else{_mc=new T1(1,I_fromInt(_mf));_md=_mg;continue;}}}else{var _mh=_me.a,_mi=E(_md);return (_mi._==0)?new T1(1,I_div(_mh,I_fromInt(_mi.a))):new T1(1,I_div(_mh,_mi.a));}}},_mj=function(_mk,_ml){if(!B(_3g(_ml,_jY))){return new F(function(){return _mb(_mk,_ml);});}else{return E(_3b);}},_mm=function(_mn,_mo){while(1){var _mp=E(_mn);if(!_mp._){var _mq=E(_mp.a);if(_mq==(-2147483648)){_mn=new T1(1,I_fromInt(-2147483648));continue;}else{var _mr=E(_mo);if(!_mr._){var _ms=_mr.a;return new T2(0,new T1(0,B(_ht(_mq,_ms))),new T1(0,B(_hZ(_mq,_ms))));}else{_mn=new T1(1,I_fromInt(_mq));_mo=_mr;continue;}}}else{var _mt=E(_mo);if(!_mt._){_mn=_mp;_mo=new T1(1,I_fromInt(_mt.a));continue;}else{var _mu=I_divMod(_mp.a,_mt.a);return new T2(0,new T1(1,_mu.a),new T1(1,_mu.b));}}}},_mv=function(_mw,_mx){if(!B(_3g(_mx,_jY))){var _my=B(_mm(_mw,_mx));return new T2(0,_my.a,_my.b);}else{return E(_3b);}},_mz=function(_mA,_mB){while(1){var _mC=E(_mA);if(!_mC._){var _mD=E(_mC.a);if(_mD==(-2147483648)){_mA=new T1(1,I_fromInt(-2147483648));continue;}else{var _mE=E(_mB);if(!_mE._){return new T1(0,B(_hZ(_mD,_mE.a)));}else{_mA=new T1(1,I_fromInt(_mD));_mB=_mE;continue;}}}else{var _mF=_mC.a,_mG=E(_mB);return (_mG._==0)?new T1(1,I_mod(_mF,I_fromInt(_mG.a))):new T1(1,I_mod(_mF,_mG.a));}}},_mH=function(_mI,_mJ){if(!B(_3g(_mJ,_jY))){return new F(function(){return _mz(_mI,_mJ);});}else{return E(_3b);}},_mK=function(_mL,_mM){while(1){var _mN=E(_mL);if(!_mN._){var _mO=E(_mN.a);if(_mO==(-2147483648)){_mL=new T1(1,I_fromInt(-2147483648));continue;}else{var _mP=E(_mM);if(!_mP._){return new T1(0,quot(_mO,_mP.a));}else{_mL=new T1(1,I_fromInt(_mO));_mM=_mP;continue;}}}else{var _mQ=_mN.a,_mR=E(_mM);return (_mR._==0)?new T1(0,I_toInt(I_quot(_mQ,I_fromInt(_mR.a)))):new T1(1,I_quot(_mQ,_mR.a));}}},_mS=function(_mT,_mU){if(!B(_3g(_mU,_jY))){return new F(function(){return _mK(_mT,_mU);});}else{return E(_3b);}},_mV=function(_mW,_mX){if(!B(_3g(_mX,_jY))){var _mY=B(_3A(_mW,_mX));return new T2(0,_mY.a,_mY.b);}else{return E(_3b);}},_mZ=function(_n0,_n1){while(1){var _n2=E(_n0);if(!_n2._){var _n3=E(_n2.a);if(_n3==(-2147483648)){_n0=new T1(1,I_fromInt(-2147483648));continue;}else{var _n4=E(_n1);if(!_n4._){return new T1(0,_n3%_n4.a);}else{_n0=new T1(1,I_fromInt(_n3));_n1=_n4;continue;}}}else{var _n5=_n2.a,_n6=E(_n1);return (_n6._==0)?new T1(1,I_rem(_n5,I_fromInt(_n6.a))):new T1(1,I_rem(_n5,_n6.a));}}},_n7=function(_n8,_n9){if(!B(_3g(_n9,_jY))){return new F(function(){return _mZ(_n8,_n9);});}else{return E(_3b);}},_na=function(_nb){return E(_nb);},_nc=function(_nd){return E(_nd);},_ne=function(_nf){var _ng=E(_nf);if(!_ng._){var _nh=E(_ng.a);return (_nh==(-2147483648))?E(_6i):(_nh<0)?new T1(0, -_nh):E(_ng);}else{var _ni=_ng.a;return (I_compareInt(_ni,0)>=0)?E(_ng):new T1(1,I_negate(_ni));}},_nj=new T1(0,0),_nk=new T1(0,-1),_nl=function(_nm){var _nn=E(_nm);if(!_nn._){var _no=_nn.a;return (_no>=0)?(E(_no)==0)?E(_nj):E(_42):E(_nk);}else{var _np=I_compareInt(_nn.a,0);return (_np<=0)?(E(_np)==0)?E(_nj):E(_nk):E(_42);}},_nq={_:0,a:_3r,b:_5E,c:_jw,d:_6j,e:_ne,f:_nl,g:_nc},_nr=function(_ns,_nt){var _nu=E(_ns);if(!_nu._){var _nv=_nu.a,_nw=E(_nt);return (_nw._==0)?_nv!=_nw.a:(I_compareInt(_nw.a,_nv)==0)?false:true;}else{var _nx=_nu.a,_ny=E(_nt);return (_ny._==0)?(I_compareInt(_nx,_ny.a)==0)?false:true:(I_compare(_nx,_ny.a)==0)?false:true;}},_nz=new T2(0,_3g,_nr),_nA=function(_nB,_nC){return (!B(_5p(_nB,_nC)))?E(_nB):E(_nC);},_nD=function(_nE,_nF){return (!B(_5p(_nE,_nF)))?E(_nF):E(_nE);},_nG={_:0,a:_nz,b:_23,c:_Q,d:_5p,e:_3U,f:_lF,g:_nA,h:_nD},_nH=function(_nI){return new T2(0,E(_nI),E(_br));},_nJ=new T3(0,_nq,_nG,_nH),_nK={_:0,a:_nJ,b:_ma,c:_mS,d:_n7,e:_mj,f:_mH,g:_mV,h:_mv,i:_na},_nL=function(_nM){return E(E(_nM).b);},_nN=function(_nO){return E(E(_nO).g);},_nP=new T1(0,1),_nQ=function(_nR,_nS,_nT){var _nU=B(_nL(_nR)),_nV=B(_8V(_nU)),_nW=new T(function(){var _nX=new T(function(){var _nY=new T(function(){var _nZ=new T(function(){return B(A3(_nN,_nR,_nK,new T(function(){return B(A3(_9b,_nU,_nS,_nT));})));});return B(A2(_9E,_nV,_nZ));}),_o0=new T(function(){return B(A2(_9G,_nV,new T(function(){return B(A2(_9E,_nV,_nP));})));});return B(A3(_8X,_nV,_o0,_nY));});return B(A3(_8X,_nV,_nX,_nT));});return new F(function(){return A3(_8Z,_nV,_nS,_nW);});},_o1=1.5707963267948966,_o2=function(_o3){return 0.2/Math.cos(B(_nQ(_lq,_o3,_o1))-0.7853981633974483);},_o4=2,_o5=1,_o6=0.7853981633974483,_o7=0,_o8=new T(function(){var _o9=B(_eb(_o2,1.2,_o7,_o7,_o4,_o6,_o7,_o7,_o7,_o7,_o7,_o7,_o5));return {_:0,a:E(_o9.a),b:E(_o9.b),c:E(_o9.c),d:E(_o9.d),e:E(_o9.e),f:E(_o9.f),g:E(_o9.g),h:_o9.h,i:_o9.i};}),_oa=0,_ob=new T2(0,E(_1y),E(_1x)),_oc=0.1,_od=new T(function(){var _oe=B(_eb(_o2,1.2,_oc,_o7,_o7,_o6,_o7,_o7,_o7,_o7,_o7,_o7,_o5));return {_:0,a:E(_oe.a),b:E(_1y),c:E(_ob),d:E(_oe.d),e:E(_oe.e),f:E(_oe.f),g:E(_oe.g),h:_oe.h,i:_oe.i};}),_of=new T2(1,_od,_z),_og=new T2(1,_o8,_of),_oh=new T(function(){return B(unCStr("Negative range size"));}),_oi=new T(function(){return B(err(_oh));}),_oj=function(_){var _ok=B(_1q(_og,0))-1|0,_ol=function(_om){if(_om>=0){var _on=newArr(_om,_1w),_oo=_on,_op=E(_om);if(!_op){return new T4(0,E(_oa),E(_ok),0,_oo);}else{var _oq=function(_or,_os,_){while(1){var _ot=E(_or);if(!_ot._){return E(_);}else{var _=_oo[_os]=_ot.a;if(_os!=(_op-1|0)){var _ou=_os+1|0;_or=_ot.b;_os=_ou;continue;}else{return E(_);}}}},_=B((function(_ov,_ow,_ox,_){var _=_oo[_ox]=_ov;if(_ox!=(_op-1|0)){return new F(function(){return _oq(_ow,_ox+1|0,_);});}else{return E(_);}})(_o8,_of,0,_));return new T4(0,E(_oa),E(_ok),_op,_oo);}}else{return E(_oi);}};if(0>_ok){return new F(function(){return _ol(0);});}else{return new F(function(){return _ol(_ok+1|0);});}},_oy=function(_oz){var _oA=B(A1(_oz,_));return E(_oA);},_oB=new T(function(){return B(_oy(_oj));}),_oC=function(_oD,_oE,_){var _oF=B(A1(_oD,_)),_oG=B(A1(_oE,_));return _oF;},_oH=function(_oI,_oJ,_){var _oK=B(A1(_oI,_)),_oL=B(A1(_oJ,_));return new T(function(){return B(A1(_oK,_oL));});},_oM=function(_oN,_oO,_){var _oP=B(A1(_oO,_));return _oN;},_oQ=function(_oR,_oS,_){var _oT=B(A1(_oS,_));return new T(function(){return B(A1(_oR,_oT));});},_oU=new T2(0,_oQ,_oM),_oV=function(_oW,_){return _oW;},_oX=function(_oY,_oZ,_){var _p0=B(A1(_oY,_));return new F(function(){return A1(_oZ,_);});},_p1=new T5(0,_oU,_oV,_oH,_oX,_oC),_p2=function(_p3){var _p4=E(_p3);return (E(_p4.b)-E(_p4.a)|0)+1|0;},_p5=function(_p6,_p7){var _p8=E(_p6),_p9=E(_p7);return (E(_p8.a)>_p9)?false:_p9<=E(_p8.b);},_pa=function(_pb,_pc){var _pd=jsShowI(_pb);return new F(function(){return _q(fromJSStr(_pd),_pc);});},_pe=function(_pf,_pg,_ph){if(_pg>=0){return new F(function(){return _pa(_pg,_ph);});}else{if(_pf<=6){return new F(function(){return _pa(_pg,_ph);});}else{return new T2(1,_Z,new T(function(){var _pi=jsShowI(_pg);return B(_q(fromJSStr(_pi),new T2(1,_Y,_ph)));}));}}},_pj=function(_pk){return new F(function(){return _pe(0,E(_pk),_z);});},_pl=function(_pm,_pn,_po){return new F(function(){return _pe(E(_pm),E(_pn),_po);});},_pp=function(_pq,_pr){return new F(function(){return _pe(0,E(_pq),_pr);});},_ps=function(_pt,_pu){return new F(function(){return _2R(_pp,_pt,_pu);});},_pv=new T3(0,_pl,_pj,_ps),_pw=0,_px=function(_py,_pz,_pA){return new F(function(){return A1(_py,new T2(1,_2O,new T(function(){return B(A1(_pz,_pA));})));});},_pB=new T(function(){return B(unCStr("foldr1"));}),_pC=new T(function(){return B(_aR(_pB));}),_pD=function(_pE,_pF){var _pG=E(_pF);if(!_pG._){return E(_pC);}else{var _pH=_pG.a,_pI=E(_pG.b);if(!_pI._){return E(_pH);}else{return new F(function(){return A2(_pE,_pH,new T(function(){return B(_pD(_pE,_pI));}));});}}},_pJ=new T(function(){return B(unCStr(" out of range "));}),_pK=new T(function(){return B(unCStr("}.index: Index "));}),_pL=new T(function(){return B(unCStr("Ix{"));}),_pM=new T2(1,_Y,_z),_pN=new T2(1,_Y,_pM),_pO=0,_pP=function(_pQ){return E(E(_pQ).a);},_pR=function(_pS,_pT,_pU,_pV,_pW){var _pX=new T(function(){var _pY=new T(function(){var _pZ=new T(function(){var _q0=new T(function(){var _q1=new T(function(){return B(A3(_pD,_px,new T2(1,new T(function(){return B(A3(_pP,_pU,_pO,_pV));}),new T2(1,new T(function(){return B(A3(_pP,_pU,_pO,_pW));}),_z)),_pN));});return B(_q(_pJ,new T2(1,_Z,new T2(1,_Z,_q1))));});return B(A(_pP,[_pU,_pw,_pT,new T2(1,_Y,_q0)]));});return B(_q(_pK,new T2(1,_Z,_pZ)));},1);return B(_q(_pS,_pY));},1);return new F(function(){return err(B(_q(_pL,_pX)));});},_q2=function(_q3,_q4,_q5,_q6,_q7){return new F(function(){return _pR(_q3,_q4,_q7,_q5,_q6);});},_q8=function(_q9,_qa,_qb,_qc){var _qd=E(_qb);return new F(function(){return _q2(_q9,_qa,_qd.a,_qd.b,_qc);});},_qe=function(_qf,_qg,_qh,_qi){return new F(function(){return _q8(_qi,_qh,_qg,_qf);});},_qj=new T(function(){return B(unCStr("Int"));}),_qk=function(_ql,_qm){return new F(function(){return _qe(_pv,_qm,_ql,_qj);});},_qn=function(_qo,_qp){var _qq=E(_qo),_qr=E(_qq.a),_qs=E(_qp);if(_qr>_qs){return new F(function(){return _qk(_qs,_qq);});}else{if(_qs>E(_qq.b)){return new F(function(){return _qk(_qs,_qq);});}else{return _qs-_qr|0;}}},_qt=function(_qu){var _qv=E(_qu);return new F(function(){return _hd(_qv.a,_qv.b);});},_qw=function(_qx){var _qy=E(_qx),_qz=E(_qy.a),_qA=E(_qy.b);return (_qz>_qA)?E(_pw):(_qA-_qz|0)+1|0;},_qB=function(_qC,_qD){return new F(function(){return _iC(_qD,E(_qC).a);});},_qE={_:0,a:_js,b:_qt,c:_qn,d:_qB,e:_p5,f:_qw,g:_p2},_qF=function(_qG){return E(E(_qG).a);},_qH=function(_qI,_qJ){return new T2(1,_qI,_qJ);},_qK=function(_qL){return E(E(_qL).c);},_qM=function(_qN,_qO){var _qP=E(_qO);return new T2(0,_qP.a,_qP.b);},_qQ=function(_qR){return E(E(_qR).a);},_qS=function(_qT){return E(E(_qT).f);},_qU=function(_qV,_qW,_qX){var _qY=E(_qW),_qZ=_qY.a,_r0=_qY.b,_r1=function(_){var _r2=B(A2(_qS,_qV,_qY));if(_r2>=0){var _r3=newArr(_r2,_1w),_r4=_r3,_r5=E(_r2);if(!_r5){return new T(function(){return new T4(0,E(_qZ),E(_r0),0,_r4);});}else{var _r6=function(_r7,_r8,_){while(1){var _r9=E(_r7);if(!_r9._){return E(_);}else{var _=_r4[_r8]=_r9.a;if(_r8!=(_r5-1|0)){var _ra=_r8+1|0;_r7=_r9.b;_r8=_ra;continue;}else{return E(_);}}}},_=B(_r6(_qX,0,_));return new T(function(){return new T4(0,E(_qZ),E(_r0),_r5,_r4);});}}else{return E(_oi);}};return new F(function(){return _oy(_r1);});},_rb=function(_rc){return E(E(_rc).b);},_rd=function(_re,_rf,_rg,_rh){var _ri=new T(function(){var _rj=E(_rh),_rk=_rj.c-1|0,_rl=new T(function(){return B(A2(_rb,_rf,_z));});if(0<=_rk){var _rm=new T(function(){return B(_qF(_rf));}),_rn=function(_ro){var _rp=new T(function(){var _rq=new T(function(){return B(A1(_rg,new T(function(){return E(_rj.d[_ro]);})));});return B(A3(_qQ,_rm,_qH,_rq));});return new F(function(){return A3(_qK,_rf,_rp,new T(function(){if(_ro!=_rk){return B(_rn(_ro+1|0));}else{return E(_rl);}}));});};return B(_rn(0));}else{return E(_rl);}}),_rr=new T(function(){return B(_qM(_re,_rh));});return new F(function(){return A3(_qQ,B(_qF(_rf)),function(_rs){return new F(function(){return _qU(_re,_rr,_rs);});},_ri);});},_rt=function(_ru){return E(E(_ru).a);},_rv=function(_rw,_rx,_ry,_rz,_rA){var _rB=B(A2(_rt,_rw,E(_rA)));return new F(function(){return A2(_rx,_ry,new T2(1,_rB,E(_rz)));});},_rC="outline",_rD="polygon",_rE=function(_rF){return new F(function(){return _8g(new T2(1,new T2(0,_rD,new T(function(){return E(_rF).h;})),new T2(1,new T2(0,_rC,new T(function(){return E(_rF).i;})),_z)));});},_rG=function(_rH){return new F(function(){return _rE(_rH);});},_rI=function(_rJ){return new F(function(){return __lst2arr(B(_8G(_rG,_rJ)));});},_rK=new T2(0,_rG,_rI),_rL=function(_rM,_){var _rN=E(_rM);if(!_rN._){return _z;}else{var _rO=B(_rL(_rN.b,_));return new T2(1,_8f,_rO);}},_rP=function(_rQ,_){var _rR=__arr2lst(0,_rQ);return new F(function(){return _rL(_rR,_);});},_rS=function(_rT,_){return new F(function(){return _rP(E(_rT),_);});},_rU=function(_){return _8f;},_rV=function(_rW,_){return new F(function(){return _rU(_);});},_rX=new T2(0,_rV,_rS),_rY=function(_rZ){return E(E(_rZ).a);},_s0=function(_s1,_s2,_s3,_){var _s4=__apply(_s2,E(_s3));return new F(function(){return A3(_rY,_s1,_s4,_);});},_s5=function(_s6,_s7,_s8,_){return new F(function(){return _s0(_s6,E(_s7),_s8,_);});},_s9=function(_sa,_sb,_sc,_){return new F(function(){return _s5(_sa,_sb,_sc,_);});},_sd=function(_se,_sf,_){return new F(function(){return _s9(_rX,_se,_sf,_);});},_sg=new T(function(){return eval("drawObject");}),_sh=function(_si){return new F(function(){return _rv(_rK,_sd,_sg,_z,_si);});},_sj=new T(function(){return eval("__strict(draw)");}),_sk=function(_sl){return E(_sl);},_sm=function(_sn){return E(_sn);},_so=function(_sp,_sq){return E(_sq);},_sr=function(_ss,_st){return E(_ss);},_su=function(_sv){return E(_sv);},_sw=new T2(0,_su,_sr),_sx=function(_sy,_sz){return E(_sy);},_sA=new T5(0,_sw,_sm,_sk,_so,_sx),_sB="d2z",_sC="d2y",_sD="w2z",_sE="w2y",_sF="w2x",_sG="w1z",_sH="w1y",_sI="w1x",_sJ="d2x",_sK="d1z",_sL="d1y",_sM="d1x",_sN="c2y",_sO="c2x",_sP="c1y",_sQ="c1x",_sR=function(_sS,_){var _sT=__get(_sS,E(_sI)),_sU=__get(_sS,E(_sH)),_sV=__get(_sS,E(_sG)),_sW=__get(_sS,E(_sF)),_sX=__get(_sS,E(_sE)),_sY=__get(_sS,E(_sD)),_sZ=__get(_sS,E(_sQ)),_t0=__get(_sS,E(_sP)),_t1=__get(_sS,E(_sO)),_t2=__get(_sS,E(_sN)),_t3=__get(_sS,E(_sM)),_t4=__get(_sS,E(_sL)),_t5=__get(_sS,E(_sK)),_t6=__get(_sS,E(_sJ)),_t7=__get(_sS,E(_sC)),_t8=__get(_sS,E(_sB));return new T6(0,E(new T3(0,E(_sT),E(_sU),E(_sV))),E(new T3(0,E(_sW),E(_sX),E(_sY))),E(new T2(0,E(_sZ),E(_t0))),E(new T2(0,E(_t1),E(_t2))),E(new T3(0,E(_t3),E(_t4),E(_t5))),E(new T3(0,E(_t6),E(_t7),E(_t8))));},_t9=function(_ta,_){var _tb=E(_ta);if(!_tb._){return _z;}else{var _tc=B(_sR(E(_tb.a),_)),_td=B(_t9(_tb.b,_));return new T2(1,_tc,_td);}},_te=function(_tf,_tg,_){while(1){var _th=B((function(_ti,_tj,_){var _tk=E(_ti);if(!_tk._){return new T2(0,_8f,_tj);}else{var _tl=B(A2(_tk.a,_tj,_));_tf=_tk.b;_tg=new T(function(){return E(E(_tl).b);});return __continue;}})(_tf,_tg,_));if(_th!=__continue){return _th;}}},_tm=function(_tn,_to,_tp,_tq,_tr,_ts,_tt,_tu,_tv){var _tw=B(_8X(_tn));return new T2(0,new T3(0,E(B(A1(B(A1(_tw,_to)),_ts))),E(B(A1(B(A1(_tw,_tp)),_tt))),E(B(A1(B(A1(_tw,_tq)),_tu)))),B(A1(B(A1(_tw,_tr)),_tv)));},_tx=function(_ty,_tz,_tA,_tB,_tC,_tD,_tE,_tF,_tG){var _tH=B(_8Z(_ty));return new T2(0,new T3(0,E(B(A1(B(A1(_tH,_tz)),_tD))),E(B(A1(B(A1(_tH,_tA)),_tE))),E(B(A1(B(A1(_tH,_tB)),_tF)))),B(A1(B(A1(_tH,_tC)),_tG)));},_tI=1.0e-2,_tJ=function(_tK,_tL,_tM,_tN,_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX,_tY,_tZ,_u0){var _u1=B(_tm(_6Y,_tR,_tS,_tT,_tU,_tI,_tI,_tI,_tI)),_u2=E(_u1.a),_u3=B(_tx(_6Y,_tN,_tO,_tP,_tQ,_u2.a,_u2.b,_u2.c,_u1.b)),_u4=E(_u3.a);return new F(function(){return _ds(_tK,_tL,_tM,_u4.a,_u4.b,_u4.c,_u3.b,_tR,_tS,_tT,_tU,_tV,_tW,_tX,_tY,_tZ,_u0);});},_u5=function(_u6){var _u7=E(_u6),_u8=E(_u7.d),_u9=E(_u8.a),_ua=E(_u7.e),_ub=E(_ua.a),_uc=E(_u7.f),_ud=B(_tJ(_u7.a,_u7.b,_u7.c,_u9.a,_u9.b,_u9.c,_u8.b,_ub.a,_ub.b,_ub.c,_ua.b,_uc.a,_uc.b,_uc.c,_u7.g,_u7.h,_u7.i));return {_:0,a:E(_ud.a),b:E(_ud.b),c:E(_ud.c),d:E(_ud.d),e:E(_ud.e),f:E(_ud.f),g:E(_ud.g),h:_ud.h,i:_ud.i};},_ue=function(_uf,_ug,_uh,_ui,_uj,_uk,_ul,_um,_un){var _uo=B(_8V(B(_8T(_uf))));return new F(function(){return A3(_8Z,_uo,new T(function(){return B(_91(_uf,_ug,_uh,_ui,_uk,_ul,_um));}),new T(function(){return B(A3(_8X,_uo,_uj,_un));}));});},_up=new T(function(){return B(unCStr("base"));}),_uq=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_ur=new T(function(){return B(unCStr("IOException"));}),_us=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_up,_uq,_ur),_ut=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_us,_z,_z),_uu=function(_uv){return E(_ut);},_uw=function(_ux){var _uy=E(_ux);return new F(function(){return _2o(B(_2m(_uy.a)),_uu,_uy.b);});},_uz=new T(function(){return B(unCStr(": "));}),_uA=new T(function(){return B(unCStr(")"));}),_uB=new T(function(){return B(unCStr(" ("));}),_uC=new T(function(){return B(unCStr("interrupted"));}),_uD=new T(function(){return B(unCStr("system error"));}),_uE=new T(function(){return B(unCStr("unsatisified constraints"));}),_uF=new T(function(){return B(unCStr("user error"));}),_uG=new T(function(){return B(unCStr("permission denied"));}),_uH=new T(function(){return B(unCStr("illegal operation"));}),_uI=new T(function(){return B(unCStr("end of file"));}),_uJ=new T(function(){return B(unCStr("resource exhausted"));}),_uK=new T(function(){return B(unCStr("resource busy"));}),_uL=new T(function(){return B(unCStr("does not exist"));}),_uM=new T(function(){return B(unCStr("already exists"));}),_uN=new T(function(){return B(unCStr("resource vanished"));}),_uO=new T(function(){return B(unCStr("timeout"));}),_uP=new T(function(){return B(unCStr("unsupported operation"));}),_uQ=new T(function(){return B(unCStr("hardware fault"));}),_uR=new T(function(){return B(unCStr("inappropriate type"));}),_uS=new T(function(){return B(unCStr("invalid argument"));}),_uT=new T(function(){return B(unCStr("failed"));}),_uU=new T(function(){return B(unCStr("protocol error"));}),_uV=function(_uW,_uX){switch(E(_uW)){case 0:return new F(function(){return _q(_uM,_uX);});break;case 1:return new F(function(){return _q(_uL,_uX);});break;case 2:return new F(function(){return _q(_uK,_uX);});break;case 3:return new F(function(){return _q(_uJ,_uX);});break;case 4:return new F(function(){return _q(_uI,_uX);});break;case 5:return new F(function(){return _q(_uH,_uX);});break;case 6:return new F(function(){return _q(_uG,_uX);});break;case 7:return new F(function(){return _q(_uF,_uX);});break;case 8:return new F(function(){return _q(_uE,_uX);});break;case 9:return new F(function(){return _q(_uD,_uX);});break;case 10:return new F(function(){return _q(_uU,_uX);});break;case 11:return new F(function(){return _q(_uT,_uX);});break;case 12:return new F(function(){return _q(_uS,_uX);});break;case 13:return new F(function(){return _q(_uR,_uX);});break;case 14:return new F(function(){return _q(_uQ,_uX);});break;case 15:return new F(function(){return _q(_uP,_uX);});break;case 16:return new F(function(){return _q(_uO,_uX);});break;case 17:return new F(function(){return _q(_uN,_uX);});break;default:return new F(function(){return _q(_uC,_uX);});}},_uY=new T(function(){return B(unCStr("}"));}),_uZ=new T(function(){return B(unCStr("{handle: "));}),_v0=function(_v1,_v2,_v3,_v4,_v5,_v6){var _v7=new T(function(){var _v8=new T(function(){var _v9=new T(function(){var _va=E(_v4);if(!_va._){return E(_v6);}else{var _vb=new T(function(){return B(_q(_va,new T(function(){return B(_q(_uA,_v6));},1)));},1);return B(_q(_uB,_vb));}},1);return B(_uV(_v2,_v9));}),_vc=E(_v3);if(!_vc._){return E(_v8);}else{return B(_q(_vc,new T(function(){return B(_q(_uz,_v8));},1)));}}),_vd=E(_v5);if(!_vd._){var _ve=E(_v1);if(!_ve._){return E(_v7);}else{var _vf=E(_ve.a);if(!_vf._){var _vg=new T(function(){var _vh=new T(function(){return B(_q(_uY,new T(function(){return B(_q(_uz,_v7));},1)));},1);return B(_q(_vf.a,_vh));},1);return new F(function(){return _q(_uZ,_vg);});}else{var _vi=new T(function(){var _vj=new T(function(){return B(_q(_uY,new T(function(){return B(_q(_uz,_v7));},1)));},1);return B(_q(_vf.a,_vj));},1);return new F(function(){return _q(_uZ,_vi);});}}}else{return new F(function(){return _q(_vd.a,new T(function(){return B(_q(_uz,_v7));},1));});}},_vk=function(_vl){var _vm=E(_vl);return new F(function(){return _v0(_vm.a,_vm.b,_vm.c,_vm.d,_vm.f,_z);});},_vn=function(_vo,_vp,_vq){var _vr=E(_vp);return new F(function(){return _v0(_vr.a,_vr.b,_vr.c,_vr.d,_vr.f,_vq);});},_vs=function(_vt,_vu){var _vv=E(_vt);return new F(function(){return _v0(_vv.a,_vv.b,_vv.c,_vv.d,_vv.f,_vu);});},_vw=function(_vx,_vy){return new F(function(){return _2R(_vs,_vx,_vy);});},_vz=new T3(0,_vn,_vk,_vw),_vA=new T(function(){return new T5(0,_uu,_vz,_vB,_uw,_vk);}),_vB=function(_vC){return new T2(0,_vA,_vC);},_vD=__Z,_vE=7,_vF=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:70:3-9"));}),_vG=new T6(0,_vD,_vE,_z,_vF,_vD,_vD),_vH=new T(function(){return B(_vB(_vG));}),_vI=function(_){return new F(function(){return die(_vH);});},_vJ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:69:3-9"));}),_vK=new T6(0,_vD,_vE,_z,_vJ,_vD,_vD),_vL=new T(function(){return B(_vB(_vK));}),_vM=function(_){return new F(function(){return die(_vL);});},_vN=function(_vO,_){return new T2(0,_z,_vO);},_vP=1,_vQ=new T(function(){return B(unCStr(")"));}),_vR=function(_vS,_vT){var _vU=new T(function(){var _vV=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_q(B(_pe(0,_vS,_z)),_vQ));})));},1);return B(_q(B(_pe(0,_vT,_z)),_vV));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_vU)));});},_vW=function(_vX,_vY){var _vZ=new T(function(){var _w0=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_q(B(_pe(0,_vY,_z)),_vQ));})));},1);return B(_q(B(_pe(0,_vX,_z)),_w0));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_vZ)));});},_w1=0.6,_w2=function(_w3){var _w4=E(_w3);if(!_w4._){return E(_vN);}else{var _w5=new T(function(){return B(_w2(_w4.b));}),_w6=function(_w7){var _w8=E(_w7);if(!_w8._){return E(_w5);}else{var _w9=_w8.a,_wa=new T(function(){return B(_w6(_w8.b));}),_wb=new T(function(){return 0.1*E(E(_w9).e)/1.0e-2;}),_wc=new T(function(){var _wd=E(_w9);if(_wd.a!=_wd.b){return E(_vP);}else{return E(_w1);}}),_we=function(_wf,_){var _wg=E(_wf),_wh=_wg.c,_wi=_wg.d,_wj=E(_wg.a),_wk=E(_wg.b),_wl=E(_w9),_wm=_wl.a,_wn=_wl.b,_wo=E(_wl.c),_wp=_wo.b,_wq=E(_wo.a),_wr=_wq.a,_ws=_wq.b,_wt=_wq.c,_wu=E(_wl.d),_wv=_wu.b,_ww=E(_wu.a),_wx=_ww.a,_wy=_ww.b,_wz=_ww.c;if(_wj>_wm){return new F(function(){return _vM(_);});}else{if(_wm>_wk){return new F(function(){return _vM(_);});}else{if(_wj>_wn){return new F(function(){return _vI(_);});}else{if(_wn>_wk){return new F(function(){return _vI(_);});}else{var _wA=_wm-_wj|0;if(0>_wA){return new F(function(){return _vR(_wh,_wA);});}else{if(_wA>=_wh){return new F(function(){return _vR(_wh,_wA);});}else{var _wB=E(_wi[_wA]),_wC=E(_wB.c),_wD=_wC.b,_wE=E(_wC.a),_wF=_wE.a,_wG=_wE.b,_wH=_wE.c,_wI=E(_wB.e),_wJ=_wI.b,_wK=E(_wI.a),_wL=_wK.a,_wM=_wK.b,_wN=_wK.c,_wO=B(_tm(_6Y,_wr,_ws,_wt,_wp,_wF,_wG,_wH,_wD)),_wP=E(_wO.a),_wQ=B(_tm(_6Y,_wP.a,_wP.b,_wP.c,_wO.b,_wr,_ws,_wt,_wp)),_wR=E(_wQ.a),_wS=_wn-_wj|0;if(0>_wS){return new F(function(){return _vW(_wS,_wh);});}else{if(_wS>=_wh){return new F(function(){return _vW(_wS,_wh);});}else{var _wT=E(_wi[_wS]),_wU=E(_wT.c),_wV=_wU.b,_wW=E(_wU.a),_wX=_wW.a,_wY=_wW.b,_wZ=_wW.c,_x0=E(_wT.e),_x1=E(_x0.a),_x2=B(_tm(_6Y,_wx,_wy,_wz,_wv,_wX,_wY,_wZ,_wV)),_x3=E(_x2.a),_x4=B(_tm(_6Y,_x3.a,_x3.b,_x3.c,_x2.b,_wx,_wy,_wz,_wv)),_x5=E(_x4.a),_x6=E(_wR.a)+E(_wR.b)+E(_wR.c)+E(_wQ.b)+E(_x5.a)+E(_x5.b)+E(_x5.c)+E(_x4.b);if(!_x6){var _x7=B(A2(_wa,_wg,_));return new T2(0,new T2(1,_8f,new T(function(){return E(E(_x7).a);})),new T(function(){return E(E(_x7).b);}));}else{var _x8= -((B(_ue(_7u,_wL,_wM,_wN,_wJ,_wr,_ws,_wt,_wp))-B(_ue(_7u,_x1.a,_x1.b,_x1.c,_x0.b,_wx,_wy,_wz,_wv))-E(_wb))/_x6);if(_x8<0){var _x9=B(A2(_wa,_wg,_));return new T2(0,new T2(1,_8f,new T(function(){return E(E(_x9).a);})),new T(function(){return E(E(_x9).b);}));}else{var _xa=new T(function(){var _xb=function(_){var _xc=newArr(_wh,_1w),_xd=_xc,_xe=function(_xf,_){while(1){if(_xf!=_wh){var _=_xd[_xf]=_wi[_xf],_xg=_xf+1|0;_xf=_xg;continue;}else{return E(_);}}},_=B(_xe(0,_)),_=_xd[_wA]=new T(function(){var _xh=B(_tm(_6Y,_wF,_wG,_wH,_wD,_wr,_ws,_wt,_wp)),_xi=E(_xh.a),_xj=_x8*E(_wc),_xk=B(_tm(_6Y,_xi.a,_xi.b,_xi.c,_xh.b,_xj,_xj,_xj,_xj)),_xl=E(_xk.a),_xm=B(_tx(_6Y,_wL,_wM,_wN,_wJ,_xl.a,_xl.b,_xl.c,_xk.b));return {_:0,a:E(_wB.a),b:E(_wB.b),c:E(_wC),d:E(_wB.d),e:E(new T2(0,E(_xm.a),E(_xm.b))),f:E(_wB.f),g:E(_wB.g),h:_wB.h,i:_wB.i};});return new T4(0,E(_wj),E(_wk),_wh,_xd);},_xn=B(_oy(_xb)),_xo=_xn.c,_xp=_xn.d,_xq=E(_xn.a),_xr=E(_xn.b);if(_xq>_wn){return E(_xn);}else{if(_wn>_xr){return E(_xn);}else{var _xs=function(_){var _xt=newArr(_xo,_1w),_xu=_xt,_xv=function(_xw,_){while(1){if(_xw!=_xo){var _=_xu[_xw]=_xp[_xw],_xx=_xw+1|0;_xw=_xx;continue;}else{return E(_);}}},_=B(_xv(0,_)),_xy=_wn-_xq|0;if(0>_xy){return new F(function(){return _vW(_xy,_xo);});}else{if(_xy>=_xo){return new F(function(){return _vW(_xy,_xo);});}else{var _=_xu[_xy]=new T(function(){var _xz=B(_tm(_6Y,_wX,_wY,_wZ,_wV,_wx,_wy,_wz,_wv)),_xA=E(_xz.a),_xB=_x8*E(_wc),_xC=B(_tm(_6Y,_xA.a,_xA.b,_xA.c,_xz.b,_xB,_xB,_xB,_xB)),_xD=E(_xC.a),_xE=E(_xp[_xy]),_xF=E(_xE.e),_xG=E(_xF.a),_xH=B(_tx(_6Y,_xG.a,_xG.b,_xG.c,_xF.b, -E(_xD.a), -E(_xD.b), -E(_xD.c), -E(_xC.b)));return {_:0,a:E(_xE.a),b:E(_xE.b),c:E(_xE.c),d:E(_xE.d),e:E(new T2(0,E(_xH.a),E(_xH.b))),f:E(_xE.f),g:E(_xE.g),h:_xE.h,i:_xE.i};});return new T4(0,E(_xq),E(_xr),_xo,_xu);}}};return B(_oy(_xs));}}}),_xI=B(A2(_wa,_xa,_));return new T2(0,new T2(1,_8f,new T(function(){return E(E(_xI).a);})),new T(function(){return E(E(_xI).b);}));}}}}}}}}}}};return E(_we);}};return new F(function(){return _w6(_w4.a);});}},_xJ=function(_,_xK){var _xL=new T(function(){return B(_w2(E(_xK).a));}),_xM=function(_xN){var _xO=E(_xN);return (_xO==1)?E(new T2(1,_xL,_z)):new T2(1,_xL,new T(function(){return B(_xM(_xO-1|0));}));},_xP=B(_te(B(_xM(5)),new T(function(){return E(E(_xK).b);}),_)),_xQ=new T(function(){return B(_rd(_qE,_sA,_u5,new T(function(){return E(E(_xP).b);})));});return new T2(0,_8f,_xQ);},_xR=function(_xS,_xT,_xU,_xV,_xW){var _xX=B(_8V(B(_8T(_xS))));return new F(function(){return A3(_8Z,_xX,new T(function(){return B(A3(_8X,_xX,_xT,_xV));}),new T(function(){return B(A3(_8X,_xX,_xU,_xW));}));});},_xY=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:52:7-13"));}),_xZ=new T6(0,_vD,_vE,_z,_xY,_vD,_vD),_y0=new T(function(){return B(_vB(_xZ));}),_y1=function(_){return new F(function(){return die(_y0);});},_y2=function(_y3,_y4,_y5,_y6){var _y7=new T(function(){return B(_8V(new T(function(){return B(_8T(_y3));})));}),_y8=B(A2(_9E,_y7,_18));return new F(function(){return _9f(_y3,_y8,B(A2(_9E,_y7,_J)),_y8);});},_y9=function(_ya){var _yb=E(_ya),_yc=E(_yb.b),_yd=E(_yb.e),_ye=E(_yd.a),_yf=E(_yb.g),_yg=B(_aa(_7u,_yc.a,_yc.b,_yc.c,_yf.a,_yf.b,_yf.c));return {_:0,a:E(_yb.a),b:E(_yc),c:E(_yb.c),d:E(_yb.d),e:E(new T2(0,E(new T3(0,E(_ye.a)+E(_yg.a)*1.0e-2,E(_ye.b)+E(_yg.b)*1.0e-2,E(_ye.c)+E(_yg.c)*1.0e-2)),E(_yd.b))),f:E(_yb.f),g:E(_yf),h:_yb.h,i:_yb.i};},_yh=new T(function(){return eval("collide");}),_yi=function(_yj){var _yk=E(_yj);if(!_yk._){return __Z;}else{return new F(function(){return _q(_yk.a,new T(function(){return B(_yi(_yk.b));},1));});}},_yl=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:51:7-13"));}),_ym=new T6(0,_vD,_vE,_z,_yl,_vD,_vD),_yn=new T(function(){return B(_vB(_ym));}),_yo=function(_yp,_){var _yq=B(_rd(_qE,_sA,_y9,_yp)),_yr=E(_yq.a),_ys=E(_yq.b);if(_yr<=_ys){var _yt=function(_yu,_yv,_){if(_yu<=_ys){var _yw=E(_yv),_yx=function(_yy,_yz,_yA,_yB,_yC,_){if(_yz>_yu){return new F(function(){return die(_yn);});}else{if(_yu>_yA){return new F(function(){return die(_yn);});}else{if(_yz>_yy){return new F(function(){return _y1(_);});}else{if(_yy>_yA){return new F(function(){return _y1(_);});}else{var _yD=_yu-_yz|0;if(0>_yD){return new F(function(){return _vW(_yD,_yB);});}else{if(_yD>=_yB){return new F(function(){return _vW(_yD,_yB);});}else{var _yE=E(_yC[_yD]),_yF=_yy-_yz|0;if(0>_yF){return new F(function(){return _vW(_yF,_yB);});}else{if(_yF>=_yB){return new F(function(){return _vW(_yF,_yB);});}else{var _yG=E(_yC[_yF]),_yH=__app2(E(_yh),B(_8g(new T2(1,new T2(0,_rD,_yE.h),new T2(1,new T2(0,_rC,_yE.i),_z)))),B(_8g(new T2(1,new T2(0,_rD,_yG.h),new T2(1,new T2(0,_rC,_yG.i),_z))))),_yI=__arr2lst(0,_yH),_yJ=B(_t9(_yI,_)),_yK=function(_yL,_yM,_){var _yN=E(_yL);if(!_yN._){return new T2(0,_z,_yM);}else{var _yO=E(_yN.a),_yP=E(_yO.b),_yQ=E(_yO.a),_yR=E(_yQ.a),_yS=E(_yQ.b),_yT=E(_yQ.c),_yU=E(_yP.a),_yV=E(_yP.b),_yW=E(_yP.c),_yX=E(_yO.c),_yY=_yX.a,_yZ=_yX.b,_z0=E(_yO.e),_z1=E(_yO.d),_z2=_z1.a,_z3=_z1.b,_z4=E(_yO.f),_z5=B(_yK(_yN.b,_yM,_));return new T2(0,new T2(1,new T(function(){var _z6=_yU+ -_yR,_z7=_yV+ -_yS,_z8=_yW+ -_yT,_z9=B(_y2(_7u,_yR,_yS,_yT)),_za=Math.sqrt(B(_91(_7u,_z6,_z7,_z8,_z6,_z7,_z8))),_zb=1/_za,_zc=_z6*_zb,_zd=_z7*_zb,_ze=_z8*_zb,_zf=B(_aa(_7u,_zc,_zd,_ze,_z9.a,_z9.b,_z9.c)),_zg=B(_9f(_7u,_z0.a,_z0.b,_z0.c)),_zh=E(_zg.b),_zi=B(_y2(_7u,_yU,_yV,_yW)),_zj=B(_aa(_7u,_zc,_zd,_ze,_zi.a,_zi.b,_zi.c)),_zk=B(_9f(_7u,_z4.a,_z4.b,_z4.c)),_zl=E(_zk.b),_zm=Math.sqrt(B(_xR(_7u,_yY,_yZ,_yY,_yZ))),_zn=Math.sqrt(B(_xR(_7u,_z2,_z3,_z2,_z3)));return new T5(0,_yu,_yy,E(new T2(0,E(new T3(0,E(_zf.a),E(_zf.b),E(_zf.c))),_ze*_zm*E(_zg.a)-_zm*E(_zg.c)*_zc)),E(new T2(0,E(new T3(0,E(_zj.a),E(_zj.b),E(_zj.c))),_ze*_zn*E(_zk.a)-_zn*E(_zk.c)*_zc)),_za);}),new T(function(){return E(E(_z5).a);})),new T(function(){return E(E(_z5).b);}));}},_zo=B(_yK(_yJ,new T4(0,E(_yz),E(_yA),_yB,_yC),_));if(_yy!=_ys){var _zp=E(_zo),_zq=E(_zp.b),_zr=B(_yx(_yy+1|0,E(_zq.a),E(_zq.b),_zq.c,_zq.d,_));return new T2(0,new T2(1,_zp.a,new T(function(){return E(E(_zr).a);})),new T(function(){return E(E(_zr).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_zo).a);}),_z),new T(function(){return E(E(_zo).b);}));}}}}}}}}}},_zs=B(_yx(_yu,E(_yw.a),E(_yw.b),_yw.c,_yw.d,_));if(_yu!=_ys){var _zt=B(_yt(_yu+1|0,new T(function(){return E(E(_zs).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_yi(E(_zs).a));}),new T(function(){return E(E(_zt).a);})),new T(function(){return E(E(_zt).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_yi(E(_zs).a));}),_z),new T(function(){return E(E(_zs).b);}));}}else{if(_yu!=_ys){var _zu=B(_yt(_yu+1|0,_yv,_));return new T2(0,new T2(1,_z,new T(function(){return E(E(_zu).a);})),new T(function(){return E(E(_zu).b);}));}else{return new T2(0,new T2(1,_z,_z),_yv);}}},_zv=function(_zw,_zx,_zy,_zz,_zA,_){if(_zw<=_ys){var _zB=function(_zC,_zD,_zE,_zF,_zG,_){if(_zD>_zw){return new F(function(){return die(_yn);});}else{if(_zw>_zE){return new F(function(){return die(_yn);});}else{if(_zD>_zC){return new F(function(){return _y1(_);});}else{if(_zC>_zE){return new F(function(){return _y1(_);});}else{var _zH=_zw-_zD|0;if(0>_zH){return new F(function(){return _vW(_zH,_zF);});}else{if(_zH>=_zF){return new F(function(){return _vW(_zH,_zF);});}else{var _zI=E(_zG[_zH]),_zJ=_zC-_zD|0;if(0>_zJ){return new F(function(){return _vW(_zJ,_zF);});}else{if(_zJ>=_zF){return new F(function(){return _vW(_zJ,_zF);});}else{var _zK=E(_zG[_zJ]),_zL=__app2(E(_yh),B(_8g(new T2(1,new T2(0,_rD,_zI.h),new T2(1,new T2(0,_rC,_zI.i),_z)))),B(_8g(new T2(1,new T2(0,_rD,_zK.h),new T2(1,new T2(0,_rC,_zK.i),_z))))),_zM=__arr2lst(0,_zL),_zN=B(_t9(_zM,_)),_zO=function(_zP,_zQ,_){var _zR=E(_zP);if(!_zR._){return new T2(0,_z,_zQ);}else{var _zS=E(_zR.a),_zT=E(_zS.b),_zU=E(_zS.a),_zV=E(_zU.a),_zW=E(_zU.b),_zX=E(_zU.c),_zY=E(_zT.a),_zZ=E(_zT.b),_A0=E(_zT.c),_A1=E(_zS.c),_A2=_A1.a,_A3=_A1.b,_A4=E(_zS.e),_A5=E(_zS.d),_A6=_A5.a,_A7=_A5.b,_A8=E(_zS.f),_A9=B(_zO(_zR.b,_zQ,_));return new T2(0,new T2(1,new T(function(){var _Aa=_zY+ -_zV,_Ab=_zZ+ -_zW,_Ac=_A0+ -_zX,_Ad=B(_y2(_7u,_zV,_zW,_zX)),_Ae=Math.sqrt(B(_91(_7u,_Aa,_Ab,_Ac,_Aa,_Ab,_Ac))),_Af=1/_Ae,_Ag=_Aa*_Af,_Ah=_Ab*_Af,_Ai=_Ac*_Af,_Aj=B(_aa(_7u,_Ag,_Ah,_Ai,_Ad.a,_Ad.b,_Ad.c)),_Ak=B(_9f(_7u,_A4.a,_A4.b,_A4.c)),_Al=E(_Ak.b),_Am=B(_y2(_7u,_zY,_zZ,_A0)),_An=B(_aa(_7u,_Ag,_Ah,_Ai,_Am.a,_Am.b,_Am.c)),_Ao=B(_9f(_7u,_A8.a,_A8.b,_A8.c)),_Ap=E(_Ao.b),_Aq=Math.sqrt(B(_xR(_7u,_A2,_A3,_A2,_A3))),_Ar=Math.sqrt(B(_xR(_7u,_A6,_A7,_A6,_A7)));return new T5(0,_zw,_zC,E(new T2(0,E(new T3(0,E(_Aj.a),E(_Aj.b),E(_Aj.c))),_Ai*_Aq*E(_Ak.a)-_Aq*E(_Ak.c)*_Ag)),E(new T2(0,E(new T3(0,E(_An.a),E(_An.b),E(_An.c))),_Ai*_Ar*E(_Ao.a)-_Ar*E(_Ao.c)*_Ag)),_Ae);}),new T(function(){return E(E(_A9).a);})),new T(function(){return E(E(_A9).b);}));}},_As=B(_zO(_zN,new T4(0,E(_zD),E(_zE),_zF,_zG),_));if(_zC!=_ys){var _At=E(_As),_Au=E(_At.b),_Av=B(_zB(_zC+1|0,E(_Au.a),E(_Au.b),_Au.c,_Au.d,_));return new T2(0,new T2(1,_At.a,new T(function(){return E(E(_Av).a);})),new T(function(){return E(E(_Av).b);}));}else{return new T2(0,new T2(1,new T(function(){return E(E(_As).a);}),_z),new T(function(){return E(E(_As).b);}));}}}}}}}}}},_Aw=B(_zB(_zw,_zx,_zy,_zz,_zA,_));if(_zw!=_ys){var _Ax=B(_yt(_zw+1|0,new T(function(){return E(E(_Aw).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_yi(E(_Aw).a));}),new T(function(){return E(E(_Ax).a);})),new T(function(){return E(E(_Ax).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_yi(E(_Aw).a));}),_z),new T(function(){return E(E(_Aw).b);}));}}else{if(_zw!=_ys){var _Ay=B(_zv(_zw+1|0,_zx,_zy,_zz,_zA,_));return new T2(0,new T2(1,_z,new T(function(){return E(E(_Ay).a);})),new T(function(){return E(E(_Ay).b);}));}else{return new T2(0,new T2(1,_z,_z),new T4(0,E(_zx),E(_zy),_zz,_zA));}}},_Az=B(_zv(_yr,_yr,_ys,_yq.c,_yq.d,_));return new F(function(){return _xJ(_,_Az);});}else{return new F(function(){return _xJ(_,new T2(0,_z,_yq));});}},_AA=new T(function(){return eval("__strict(refresh)");}),_AB=function(_AC,_){var _AD=__app0(E(_AA)),_AE=__app0(E(_sj)),_AF=B(A(_rd,[_qE,_p1,_sh,_AC,_])),_AG=B(_yo(_AC,_));return new T(function(){return E(E(_AG).b);});},_AH=function(_AI,_){while(1){var _AJ=E(_AI);if(!_AJ._){return _8f;}else{var _AK=_AJ.b,_AL=E(_AJ.a);switch(_AL._){case 0:var _AM=B(A1(_AL.a,_));_AI=B(_q(_AK,new T2(1,_AM,_z)));continue;case 1:_AI=B(_q(_AK,_AL.a));continue;default:_AI=_AK;continue;}}}},_AN=function(_AO,_AP,_){var _AQ=E(_AO);switch(_AQ._){case 0:var _AR=B(A1(_AQ.a,_));return new F(function(){return _AH(B(_q(_AP,new T2(1,_AR,_z))),_);});break;case 1:return new F(function(){return _AH(B(_q(_AP,_AQ.a)),_);});break;default:return new F(function(){return _AH(_AP,_);});}},_AS=new T0(2),_AT=function(_AU){return new T0(2);},_AV=function(_AW,_AX,_AY){return function(_){var _AZ=E(_AW),_B0=rMV(_AZ),_B1=E(_B0);if(!_B1._){var _B2=new T(function(){var _B3=new T(function(){return B(A1(_AY,_8f));});return B(_q(_B1.b,new T2(1,new T2(0,_AX,function(_B4){return E(_B3);}),_z)));}),_=wMV(_AZ,new T2(0,_B1.a,_B2));return _AS;}else{var _B5=E(_B1.a);if(!_B5._){var _=wMV(_AZ,new T2(0,_AX,_z));return new T(function(){return B(A1(_AY,_8f));});}else{var _=wMV(_AZ,new T1(1,_B5.b));return new T1(1,new T2(1,new T(function(){return B(A1(_AY,_8f));}),new T2(1,new T(function(){return B(A2(_B5.a,_AX,_AT));}),_z)));}}};},_B6=new T(function(){return E(_ea);}),_B7=new T(function(){return eval("window.requestAnimationFrame");}),_B8=new T1(1,_z),_B9=function(_Ba,_Bb){return function(_){var _Bc=E(_Ba),_Bd=rMV(_Bc),_Be=E(_Bd);if(!_Be._){var _Bf=_Be.a,_Bg=E(_Be.b);if(!_Bg._){var _=wMV(_Bc,_B8);return new T(function(){return B(A1(_Bb,_Bf));});}else{var _Bh=E(_Bg.a),_=wMV(_Bc,new T2(0,_Bh.a,_Bg.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Bb,_Bf));}),new T2(1,new T(function(){return B(A1(_Bh.b,_AT));}),_z)));}}else{var _Bi=new T(function(){var _Bj=function(_Bk){var _Bl=new T(function(){return B(A1(_Bb,_Bk));});return function(_Bm){return E(_Bl);};};return B(_q(_Be.a,new T2(1,_Bj,_z)));}),_=wMV(_Bc,new T1(1,_Bi));return _AS;}};},_Bn=function(_Bo,_Bp){return new T1(0,B(_B9(_Bo,_Bp)));},_Bq=function(_Br,_Bs){var _Bt=new T(function(){return new T1(0,B(_AV(_Br,_8f,_AT)));});return function(_){var _Bu=__createJSFunc(2,function(_Bv,_){var _Bw=B(_AN(_Bt,_z,_));return _B6;}),_Bx=__app1(E(_B7),_Bu);return new T(function(){return B(_Bn(_Br,_Bs));});};},_By=new T1(1,_z),_Bz=function(_BA,_BB,_){var _BC=function(_){var _BD=nMV(_BA),_BE=_BD;return new T(function(){var _BF=new T(function(){return B(_BG(_));}),_BH=function(_){var _BI=rMV(_BE),_BJ=B(A2(_BB,_BI,_)),_=wMV(_BE,_BJ),_BK=function(_){var _BL=nMV(_By);return new T(function(){return new T1(0,B(_Bq(_BL,function(_BM){return E(_BF);})));});};return new T1(0,_BK);},_BN=new T(function(){return new T1(0,_BH);}),_BG=function(_BO){return E(_BN);};return B(_BG(_));});};return new F(function(){return _AN(new T1(0,_BC),_z,_);});},_BP=function(_){var _BQ=__app2(E(_0),E(_2),E(_1p));return new F(function(){return _Bz(_oB,_AB,_);});},_BR=function(_){return new F(function(){return _BP(_);});};
var hasteMain = function() {B(A(_BR, [0]));};window.onload = hasteMain;