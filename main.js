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

var _0=function(_1,_2,_3){return new F(function(){return A1(_1,function(_4){return new F(function(){return A2(_2,_4,_3);});});});},_5=function(_6,_7,_8){var _9=function(_a){var _b=new T(function(){return B(A1(_8,_a));});return new F(function(){return A1(_7,function(_c){return E(_b);});});};return new F(function(){return A1(_6,_9);});},_d=function(_e,_f,_g){var _h=new T(function(){return B(A1(_f,function(_i){return new F(function(){return A1(_g,_i);});}));});return new F(function(){return A1(_e,function(_j){return E(_h);});});},_k=function(_l,_m,_n){var _o=function(_p){var _q=function(_r){return new F(function(){return A1(_n,new T(function(){return B(A1(_p,_r));}));});};return new F(function(){return A1(_m,_q);});};return new F(function(){return A1(_l,_o);});},_s=function(_t,_u){return new F(function(){return A1(_u,_t);});},_v=function(_w,_x,_y){var _z=new T(function(){return B(A1(_y,_w));});return new F(function(){return A1(_x,function(_A){return E(_z);});});},_B=function(_C,_D,_E){var _F=function(_G){return new F(function(){return A1(_E,new T(function(){return B(A1(_C,_G));}));});};return new F(function(){return A1(_D,_F);});},_H=new T2(0,_B,_v),_I=new T5(0,_H,_s,_k,_d,_5),_J=function(_K){return E(E(_K).b);},_L=function(_M,_N){return new F(function(){return A3(_J,_O,_M,function(_P){return E(_N);});});},_Q=function(_R){return new F(function(){return err(_R);});},_O=new T(function(){return new T5(0,_I,_0,_L,_s,_Q);}),_S=0,_T=__Z,_U=function(_V){return new T0(2);},_W=function(_X){var _Y=new T(function(){return B(A1(_X,_U));}),_Z=function(_10){return new T1(1,new T2(1,new T(function(){return B(A1(_10,_S));}),new T2(1,_Y,_T)));};return E(_Z);},_11=function(_12){return E(_12);},_13=new T3(0,_O,_11,_W),_14=function(_15,_16){var _17=E(_15);return (_17._==0)?E(_16):new T2(1,_17.a,new T(function(){return B(_14(_17.b,_16));}));},_18=function(_19,_){while(1){var _1a=E(_19);if(!_1a._){return _S;}else{var _1b=_1a.b,_1c=E(_1a.a);switch(_1c._){case 0:var _1d=B(A1(_1c.a,_));_19=B(_14(_1b,new T2(1,_1d,_T)));continue;case 1:_19=B(_14(_1b,_1c.a));continue;default:_19=_1b;continue;}}}},_1e=function(_1f,_1g,_){var _1h=E(_1f);switch(_1h._){case 0:var _1i=B(A1(_1h.a,_));return new F(function(){return _18(B(_14(_1g,new T2(1,_1i,_T))),_);});break;case 1:return new F(function(){return _18(B(_14(_1g,_1h.a)),_);});break;default:return new F(function(){return _18(_1g,_);});}},_1j=new T(function(){return eval("compile");}),_1k=function(_1l){return E(E(_1l).b);},_1m=function(_1n){return E(E(_1n).a);},_1o=function(_1p,_1q,_1r){var _1s=E(_1r);if(!_1s._){return new F(function(){return A1(_1q,_1s.a);});}else{var _1t=new T(function(){return B(_1k(_1p));}),_1u=new T(function(){return B(_1m(_1p));}),_1v=function(_1w){var _1x=E(_1w);if(!_1x._){return E(_1u);}else{return new F(function(){return A2(_1t,new T(function(){return B(_1o(_1p,_1q,_1x.a));}),new T(function(){return B(_1v(_1x.b));}));});}};return new F(function(){return _1v(_1s.a);});}},_1y=function(_1z){var _1A=E(_1z);if(!_1A._){return __Z;}else{return new F(function(){return _14(_1A.a,new T(function(){return B(_1y(_1A.b));},1));});}},_1B=function(_1C){return new F(function(){return _1y(_1C);});},_1D=new T3(0,_T,_14,_1B),_1E=new T(function(){return B(unCStr(","));}),_1F=new T1(0,_1E),_1G=new T(function(){return B(unCStr("pow("));}),_1H=new T1(0,_1G),_1I=new T(function(){return B(unCStr(")"));}),_1J=new T1(0,_1I),_1K=new T2(1,_1J,_T),_1L=function(_1M,_1N){return new T1(1,new T2(1,_1H,new T2(1,_1M,new T2(1,_1F,new T2(1,_1N,_1K)))));},_1O=new T(function(){return B(unCStr("acos("));}),_1P=new T1(0,_1O),_1Q=function(_1R){return new T1(1,new T2(1,_1P,new T2(1,_1R,_1K)));},_1S=new T(function(){return B(unCStr("acosh("));}),_1T=new T1(0,_1S),_1U=function(_1V){return new T1(1,new T2(1,_1T,new T2(1,_1V,_1K)));},_1W=new T(function(){return B(unCStr("asin("));}),_1X=new T1(0,_1W),_1Y=function(_1Z){return new T1(1,new T2(1,_1X,new T2(1,_1Z,_1K)));},_20=new T(function(){return B(unCStr("asinh("));}),_21=new T1(0,_20),_22=function(_23){return new T1(1,new T2(1,_21,new T2(1,_23,_1K)));},_24=new T(function(){return B(unCStr("atan("));}),_25=new T1(0,_24),_26=function(_27){return new T1(1,new T2(1,_25,new T2(1,_27,_1K)));},_28=new T(function(){return B(unCStr("atanh("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1K)));},_2c=new T(function(){return B(unCStr("cos("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1K)));},_2g=new T(function(){return B(unCStr("cosh("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1K)));},_2k=new T(function(){return B(unCStr("exp("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1K)));},_2o=new T(function(){return B(unCStr("log("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1K)));},_2s=new T(function(){return B(unCStr(")/log("));}),_2t=new T1(0,_2s),_2u=function(_2v,_2w){return new T1(1,new T2(1,_2p,new T2(1,_2w,new T2(1,_2t,new T2(1,_2v,_1K)))));},_2x=new T(function(){return B(unCStr("pi"));}),_2y=new T1(0,_2x),_2z=new T(function(){return B(unCStr("sin("));}),_2A=new T1(0,_2z),_2B=function(_2C){return new T1(1,new T2(1,_2A,new T2(1,_2C,_1K)));},_2D=new T(function(){return B(unCStr("sinh("));}),_2E=new T1(0,_2D),_2F=function(_2G){return new T1(1,new T2(1,_2E,new T2(1,_2G,_1K)));},_2H=new T(function(){return B(unCStr("sqrt("));}),_2I=new T1(0,_2H),_2J=function(_2K){return new T1(1,new T2(1,_2I,new T2(1,_2K,_1K)));},_2L=new T(function(){return B(unCStr("tan("));}),_2M=new T1(0,_2L),_2N=function(_2O){return new T1(1,new T2(1,_2M,new T2(1,_2O,_1K)));},_2P=new T(function(){return B(unCStr("tanh("));}),_2Q=new T1(0,_2P),_2R=function(_2S){return new T1(1,new T2(1,_2Q,new T2(1,_2S,_1K)));},_2T=new T(function(){return B(unCStr("("));}),_2U=new T1(0,_2T),_2V=new T(function(){return B(unCStr(")/("));}),_2W=new T1(0,_2V),_2X=function(_2Y,_2Z){return new T1(1,new T2(1,_2U,new T2(1,_2Y,new T2(1,_2W,new T2(1,_2Z,_1K)))));},_30=new T1(0,1),_31=function(_32,_33){var _34=E(_32);if(!_34._){var _35=_34.a,_36=E(_33);if(!_36._){var _37=_36.a;return (_35!=_37)?(_35>_37)?2:0:1;}else{var _38=I_compareInt(_36.a,_35);return (_38<=0)?(_38>=0)?1:2:0;}}else{var _39=_34.a,_3a=E(_33);if(!_3a._){var _3b=I_compareInt(_39,_3a.a);return (_3b>=0)?(_3b<=0)?1:2:0;}else{var _3c=I_compare(_39,_3a.a);return (_3c>=0)?(_3c<=0)?1:2:0;}}},_3d=new T(function(){return B(unCStr("base"));}),_3e=new T(function(){return B(unCStr("GHC.Exception"));}),_3f=new T(function(){return B(unCStr("ArithException"));}),_3g=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3d,_3e,_3f),_3h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3g,_T,_T),_3i=function(_3j){return E(_3h);},_3k=function(_3l){return E(E(_3l).a);},_3m=function(_3n,_3o,_3p){var _3q=B(A1(_3n,_)),_3r=B(A1(_3o,_)),_3s=hs_eqWord64(_3q.a,_3r.a);if(!_3s){return __Z;}else{var _3t=hs_eqWord64(_3q.b,_3r.b);return (!_3t)?__Z:new T1(1,_3p);}},_3u=function(_3v){var _3w=E(_3v);return new F(function(){return _3m(B(_3k(_3w.a)),_3i,_3w.b);});},_3x=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3y=new T(function(){return B(unCStr("denormal"));}),_3z=new T(function(){return B(unCStr("divide by zero"));}),_3A=new T(function(){return B(unCStr("loss of precision"));}),_3B=new T(function(){return B(unCStr("arithmetic underflow"));}),_3C=new T(function(){return B(unCStr("arithmetic overflow"));}),_3D=function(_3E,_3F){switch(E(_3E)){case 0:return new F(function(){return _14(_3C,_3F);});break;case 1:return new F(function(){return _14(_3B,_3F);});break;case 2:return new F(function(){return _14(_3A,_3F);});break;case 3:return new F(function(){return _14(_3z,_3F);});break;case 4:return new F(function(){return _14(_3y,_3F);});break;default:return new F(function(){return _14(_3x,_3F);});}},_3G=function(_3H){return new F(function(){return _3D(_3H,_T);});},_3I=function(_3J,_3K,_3L){return new F(function(){return _3D(_3K,_3L);});},_3M=44,_3N=93,_3O=91,_3P=function(_3Q,_3R,_3S){var _3T=E(_3R);if(!_3T._){return new F(function(){return unAppCStr("[]",_3S);});}else{var _3U=new T(function(){var _3V=new T(function(){var _3W=function(_3X){var _3Y=E(_3X);if(!_3Y._){return E(new T2(1,_3N,_3S));}else{var _3Z=new T(function(){return B(A2(_3Q,_3Y.a,new T(function(){return B(_3W(_3Y.b));})));});return new T2(1,_3M,_3Z);}};return B(_3W(_3T.b));});return B(A2(_3Q,_3T.a,_3V));});return new T2(1,_3O,_3U);}},_40=function(_41,_42){return new F(function(){return _3P(_3D,_41,_42);});},_43=new T3(0,_3I,_3G,_40),_44=new T(function(){return new T5(0,_3i,_43,_45,_3u,_3G);}),_45=function(_46){return new T2(0,_44,_46);},_47=3,_48=new T(function(){return B(_45(_47));}),_49=new T(function(){return die(_48);}),_4a=function(_4b,_4c){var _4d=E(_4b);return (_4d._==0)?_4d.a*Math.pow(2,_4c):I_toNumber(_4d.a)*Math.pow(2,_4c);},_4e=function(_4f,_4g){var _4h=E(_4f);if(!_4h._){var _4i=_4h.a,_4j=E(_4g);return (_4j._==0)?_4i==_4j.a:(I_compareInt(_4j.a,_4i)==0)?true:false;}else{var _4k=_4h.a,_4l=E(_4g);return (_4l._==0)?(I_compareInt(_4k,_4l.a)==0)?true:false:(I_compare(_4k,_4l.a)==0)?true:false;}},_4m=function(_4n){var _4o=E(_4n);if(!_4o._){return E(_4o.a);}else{return new F(function(){return I_toInt(_4o.a);});}},_4p=function(_4q,_4r){while(1){var _4s=E(_4q);if(!_4s._){var _4t=_4s.a,_4u=E(_4r);if(!_4u._){var _4v=_4u.a,_4w=addC(_4t,_4v);if(!E(_4w.b)){return new T1(0,_4w.a);}else{_4q=new T1(1,I_fromInt(_4t));_4r=new T1(1,I_fromInt(_4v));continue;}}else{_4q=new T1(1,I_fromInt(_4t));_4r=_4u;continue;}}else{var _4x=E(_4r);if(!_4x._){_4q=_4s;_4r=new T1(1,I_fromInt(_4x.a));continue;}else{return new T1(1,I_add(_4s.a,_4x.a));}}}},_4y=function(_4z,_4A){while(1){var _4B=E(_4z);if(!_4B._){var _4C=E(_4B.a);if(_4C==(-2147483648)){_4z=new T1(1,I_fromInt(-2147483648));continue;}else{var _4D=E(_4A);if(!_4D._){var _4E=_4D.a;return new T2(0,new T1(0,quot(_4C,_4E)),new T1(0,_4C%_4E));}else{_4z=new T1(1,I_fromInt(_4C));_4A=_4D;continue;}}}else{var _4F=E(_4A);if(!_4F._){_4z=_4B;_4A=new T1(1,I_fromInt(_4F.a));continue;}else{var _4G=I_quotRem(_4B.a,_4F.a);return new T2(0,new T1(1,_4G.a),new T1(1,_4G.b));}}}},_4H=new T1(0,0),_4I=function(_4J,_4K){while(1){var _4L=E(_4J);if(!_4L._){_4J=new T1(1,I_fromInt(_4L.a));continue;}else{return new T1(1,I_shiftLeft(_4L.a,_4K));}}},_4M=function(_4N,_4O,_4P){if(!B(_4e(_4P,_4H))){var _4Q=B(_4y(_4O,_4P)),_4R=_4Q.a;switch(B(_31(B(_4I(_4Q.b,1)),_4P))){case 0:return new F(function(){return _4a(_4R,_4N);});break;case 1:if(!(B(_4m(_4R))&1)){return new F(function(){return _4a(_4R,_4N);});}else{return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}break;default:return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}}else{return E(_49);}},_4S=function(_4T,_4U){var _4V=E(_4T);if(!_4V._){var _4W=_4V.a,_4X=E(_4U);return (_4X._==0)?_4W>_4X.a:I_compareInt(_4X.a,_4W)<0;}else{var _4Y=_4V.a,_4Z=E(_4U);return (_4Z._==0)?I_compareInt(_4Y,_4Z.a)>0:I_compare(_4Y,_4Z.a)>0;}},_50=new T1(0,1),_51=function(_52,_53){var _54=E(_52);if(!_54._){var _55=_54.a,_56=E(_53);return (_56._==0)?_55<_56.a:I_compareInt(_56.a,_55)>0;}else{var _57=_54.a,_58=E(_53);return (_58._==0)?I_compareInt(_57,_58.a)<0:I_compare(_57,_58.a)<0;}},_59=new T(function(){return B(unCStr("base"));}),_5a=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5b=new T(function(){return B(unCStr("PatternMatchFail"));}),_5c=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_59,_5a,_5b),_5d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5c,_T,_T),_5e=function(_5f){return E(_5d);},_5g=function(_5h){var _5i=E(_5h);return new F(function(){return _3m(B(_3k(_5i.a)),_5e,_5i.b);});},_5j=function(_5k){return E(E(_5k).a);},_5l=function(_5m){return new T2(0,_5n,_5m);},_5o=function(_5p,_5q){return new F(function(){return _14(E(_5p).a,_5q);});},_5r=function(_5s,_5t){return new F(function(){return _3P(_5o,_5s,_5t);});},_5u=function(_5v,_5w,_5x){return new F(function(){return _14(E(_5w).a,_5x);});},_5y=new T3(0,_5u,_5j,_5r),_5n=new T(function(){return new T5(0,_5e,_5y,_5l,_5g,_5j);}),_5z=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5A=function(_5B){return E(E(_5B).c);},_5C=function(_5D,_5E){return new F(function(){return die(new T(function(){return B(A2(_5A,_5E,_5D));}));});},_5F=function(_5G,_46){return new F(function(){return _5C(_5G,_46);});},_5H=function(_5I,_5J){var _5K=E(_5J);if(!_5K._){return new T2(0,_T,_T);}else{var _5L=_5K.a;if(!B(A1(_5I,_5L))){return new T2(0,_T,_5K);}else{var _5M=new T(function(){var _5N=B(_5H(_5I,_5K.b));return new T2(0,_5N.a,_5N.b);});return new T2(0,new T2(1,_5L,new T(function(){return E(E(_5M).a);})),new T(function(){return E(E(_5M).b);}));}}},_5O=32,_5P=new T(function(){return B(unCStr("\n"));}),_5Q=function(_5R){return (E(_5R)==124)?false:true;},_5S=function(_5T,_5U){var _5V=B(_5H(_5Q,B(unCStr(_5T)))),_5W=_5V.a,_5X=function(_5Y,_5Z){var _60=new T(function(){var _61=new T(function(){return B(_14(_5U,new T(function(){return B(_14(_5Z,_5P));},1)));});return B(unAppCStr(": ",_61));},1);return new F(function(){return _14(_5Y,_60);});},_62=E(_5V.b);if(!_62._){return new F(function(){return _5X(_5W,_T);});}else{if(E(_62.a)==124){return new F(function(){return _5X(_5W,new T2(1,_5O,_62.b));});}else{return new F(function(){return _5X(_5W,_T);});}}},_63=function(_64){return new F(function(){return _5F(new T1(0,new T(function(){return B(_5S(_64,_5z));})),_5n);});},_65=function(_66){var _67=function(_68,_69){while(1){if(!B(_51(_68,_66))){if(!B(_4S(_68,_66))){if(!B(_4e(_68,_66))){return new F(function(){return _63("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_69);}}else{return _69-1|0;}}else{var _6a=B(_4I(_68,1)),_6b=_69+1|0;_68=_6a;_69=_6b;continue;}}};return new F(function(){return _67(_50,0);});},_6c=function(_6d){var _6e=E(_6d);if(!_6e._){var _6f=_6e.a>>>0;if(!_6f){return -1;}else{var _6g=function(_6h,_6i){while(1){if(_6h>=_6f){if(_6h<=_6f){if(_6h!=_6f){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6i);}}else{return _6i-1|0;}}else{var _6j=imul(_6h,2)>>>0,_6k=_6i+1|0;_6h=_6j;_6i=_6k;continue;}}};return new F(function(){return _6g(1,0);});}}else{return new F(function(){return _65(_6e);});}},_6l=function(_6m){var _6n=E(_6m);if(!_6n._){var _6o=_6n.a>>>0;if(!_6o){return new T2(0,-1,0);}else{var _6p=function(_6q,_6r){while(1){if(_6q>=_6o){if(_6q<=_6o){if(_6q!=_6o){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6r);}}else{return _6r-1|0;}}else{var _6s=imul(_6q,2)>>>0,_6t=_6r+1|0;_6q=_6s;_6r=_6t;continue;}}};return new T2(0,B(_6p(1,0)),(_6o&_6o-1>>>0)>>>0&4294967295);}}else{var _6u=_6n.a;return new T2(0,B(_6c(_6n)),I_compareInt(I_and(_6u,I_sub(_6u,I_fromInt(1))),0));}},_6v=function(_6w,_6x){var _6y=E(_6w);if(!_6y._){var _6z=_6y.a,_6A=E(_6x);return (_6A._==0)?_6z<=_6A.a:I_compareInt(_6A.a,_6z)>=0;}else{var _6B=_6y.a,_6C=E(_6x);return (_6C._==0)?I_compareInt(_6B,_6C.a)<=0:I_compare(_6B,_6C.a)<=0;}},_6D=function(_6E,_6F){while(1){var _6G=E(_6E);if(!_6G._){var _6H=_6G.a,_6I=E(_6F);if(!_6I._){return new T1(0,(_6H>>>0&_6I.a>>>0)>>>0&4294967295);}else{_6E=new T1(1,I_fromInt(_6H));_6F=_6I;continue;}}else{var _6J=E(_6F);if(!_6J._){_6E=_6G;_6F=new T1(1,I_fromInt(_6J.a));continue;}else{return new T1(1,I_and(_6G.a,_6J.a));}}}},_6K=function(_6L,_6M){while(1){var _6N=E(_6L);if(!_6N._){var _6O=_6N.a,_6P=E(_6M);if(!_6P._){var _6Q=_6P.a,_6R=subC(_6O,_6Q);if(!E(_6R.b)){return new T1(0,_6R.a);}else{_6L=new T1(1,I_fromInt(_6O));_6M=new T1(1,I_fromInt(_6Q));continue;}}else{_6L=new T1(1,I_fromInt(_6O));_6M=_6P;continue;}}else{var _6S=E(_6M);if(!_6S._){_6L=_6N;_6M=new T1(1,I_fromInt(_6S.a));continue;}else{return new T1(1,I_sub(_6N.a,_6S.a));}}}},_6T=new T1(0,2),_6U=function(_6V,_6W){var _6X=E(_6V);if(!_6X._){var _6Y=(_6X.a>>>0&(2<<_6W>>>0)-1>>>0)>>>0,_6Z=1<<_6W>>>0;return (_6Z<=_6Y)?(_6Z>=_6Y)?1:2:0;}else{var _70=B(_6D(_6X,B(_6K(B(_4I(_6T,_6W)),_50)))),_71=B(_4I(_50,_6W));return (!B(_4S(_71,_70)))?(!B(_51(_71,_70)))?1:2:0;}},_72=function(_73,_74){while(1){var _75=E(_73);if(!_75._){_73=new T1(1,I_fromInt(_75.a));continue;}else{return new T1(1,I_shiftRight(_75.a,_74));}}},_76=function(_77,_78,_79,_7a){var _7b=B(_6l(_7a)),_7c=_7b.a;if(!E(_7b.b)){var _7d=B(_6c(_79));if(_7d<((_7c+_77|0)-1|0)){var _7e=_7c+(_77-_78|0)|0;if(_7e>0){if(_7e>_7d){if(_7e<=(_7d+1|0)){if(!E(B(_6l(_79)).b)){return 0;}else{return new F(function(){return _4a(_30,_77-_78|0);});}}else{return 0;}}else{var _7f=B(_72(_79,_7e));switch(B(_6U(_79,_7e-1|0))){case 0:return new F(function(){return _4a(_7f,_77-_78|0);});break;case 1:if(!(B(_4m(_7f))&1)){return new F(function(){return _4a(_7f,_77-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}break;default:return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}}}else{return new F(function(){return _4a(_79,(_77-_78|0)-_7e|0);});}}else{if(_7d>=_78){var _7g=B(_72(_79,(_7d+1|0)-_78|0));switch(B(_6U(_79,_7d-_78|0))){case 0:return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});break;case 2:return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});break;default:if(!(B(_4m(_7g))&1)){return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});}}}else{return new F(function(){return _4a(_79, -_7c);});}}}else{var _7h=B(_6c(_79))-_7c|0,_7i=function(_7j){var _7k=function(_7l,_7m){if(!B(_6v(B(_4I(_7m,_78)),_7l))){return new F(function(){return _4M(_7j-_78|0,_7l,_7m);});}else{return new F(function(){return _4M((_7j-_78|0)+1|0,_7l,B(_4I(_7m,1)));});}};if(_7j>=_78){if(_7j!=_78){return new F(function(){return _7k(_79,new T(function(){return B(_4I(_7a,_7j-_78|0));}));});}else{return new F(function(){return _7k(_79,_7a);});}}else{return new F(function(){return _7k(new T(function(){return B(_4I(_79,_78-_7j|0));}),_7a);});}};if(_77>_7h){return new F(function(){return _7i(_77);});}else{return new F(function(){return _7i(_7h);});}}},_7n=new T1(0,2147483647),_7o=new T(function(){return B(_4p(_7n,_50));}),_7p=function(_7q){var _7r=E(_7q);if(!_7r._){var _7s=E(_7r.a);return (_7s==(-2147483648))?E(_7o):new T1(0, -_7s);}else{return new T1(1,I_negate(_7r.a));}},_7t=new T(function(){return 0/0;}),_7u=new T(function(){return -1/0;}),_7v=new T(function(){return 1/0;}),_7w=0,_7x=function(_7y,_7z){if(!B(_4e(_7z,_4H))){if(!B(_4e(_7y,_4H))){if(!B(_51(_7y,_4H))){return new F(function(){return _76(-1021,53,_7y,_7z);});}else{return  -B(_76(-1021,53,B(_7p(_7y)),_7z));}}else{return E(_7w);}}else{return (!B(_4e(_7y,_4H)))?(!B(_51(_7y,_4H)))?E(_7v):E(_7u):E(_7t);}},_7A=function(_7B){return new T1(0,new T(function(){var _7C=E(_7B),_7D=jsShow(B(_7x(_7C.a,_7C.b)));return fromJSStr(_7D);}));},_7E=new T(function(){return B(unCStr("1./("));}),_7F=new T1(0,_7E),_7G=function(_7H){return new T1(1,new T2(1,_7F,new T2(1,_7H,_1K)));},_7I=new T(function(){return B(unCStr(")+("));}),_7J=new T1(0,_7I),_7K=function(_7L,_7M){return new T1(1,new T2(1,_2U,new T2(1,_7L,new T2(1,_7J,new T2(1,_7M,_1K)))));},_7N=new T(function(){return B(unCStr("-("));}),_7O=new T1(0,_7N),_7P=function(_7Q){return new T1(1,new T2(1,_7O,new T2(1,_7Q,_1K)));},_7R=new T(function(){return B(unCStr(")*("));}),_7S=new T1(0,_7R),_7T=function(_7U,_7V){return new T1(1,new T2(1,_2U,new T2(1,_7U,new T2(1,_7S,new T2(1,_7V,_1K)))));},_7W=function(_7X){return E(E(_7X).a);},_7Y=function(_7Z){return E(E(_7Z).d);},_80=function(_81,_82){return new F(function(){return A3(_7W,_83,_81,new T(function(){return B(A2(_7Y,_83,_82));}));});},_84=new T(function(){return B(unCStr("abs("));}),_85=new T1(0,_84),_86=function(_87){return new T1(1,new T2(1,_85,new T2(1,_87,_1K)));},_88=function(_89){while(1){var _8a=E(_89);if(!_8a._){_89=new T1(1,I_fromInt(_8a.a));continue;}else{return new F(function(){return I_toString(_8a.a);});}}},_8b=function(_8c,_8d){return new F(function(){return _14(fromJSStr(B(_88(_8c))),_8d);});},_8e=41,_8f=40,_8g=new T1(0,0),_8h=function(_8i,_8j,_8k){if(_8i<=6){return new F(function(){return _8b(_8j,_8k);});}else{if(!B(_51(_8j,_8g))){return new F(function(){return _8b(_8j,_8k);});}else{return new T2(1,_8f,new T(function(){return B(_14(fromJSStr(B(_88(_8j))),new T2(1,_8e,_8k)));}));}}},_8l=new T(function(){return B(unCStr("."));}),_8m=function(_8n){return new T1(0,new T(function(){return B(_14(B(_8h(0,_8n,_T)),_8l));}));},_8o=new T(function(){return B(unCStr("sign("));}),_8p=new T1(0,_8o),_8q=function(_8r){return new T1(1,new T2(1,_8p,new T2(1,_8r,_1K)));},_83=new T(function(){return {_:0,a:_7K,b:_80,c:_7T,d:_7P,e:_86,f:_8q,g:_8m};}),_8s=new T4(0,_83,_2X,_7G,_7A),_8t={_:0,a:_8s,b:_2y,c:_2m,d:_2q,e:_2J,f:_1L,g:_2u,h:_2B,i:_2e,j:_2N,k:_1Y,l:_1Q,m:_26,n:_2F,o:_2i,p:_2R,q:_22,r:_1U,s:_2a},_8u=function(_8v){return E(E(_8v).a);},_8w=function(_8x){return E(E(_8x).a);},_8y=function(_8z){return E(E(_8z).c);},_8A=function(_8B){return E(E(_8B).b);},_8C=function(_8D){return E(E(_8D).d);},_8E=new T1(0,1),_8F=new T1(0,2),_8G=new T2(0,E(_8E),E(_8F)),_8H=new T1(0,5),_8I=new T1(0,4),_8J=new T2(0,E(_8I),E(_8H)),_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O,_8P,_8Q){var _8R=B(_8u(_8N)),_8S=B(_8w(_8R)),_8T=new T(function(){var _8U=new T(function(){var _8V=new T(function(){var _8W=new T(function(){var _8X=new T(function(){var _8Y=new T(function(){return B(A3(_7W,_8S,new T(function(){return B(A3(_8y,_8S,_8O,_8O));}),new T(function(){return B(A3(_8y,_8S,_8Q,_8Q));})));});return B(A2(_8K,_8N,_8Y));});return B(A3(_8A,_8S,_8X,new T(function(){return B(A2(_8C,_8R,_8J));})));});return B(A3(_8y,_8S,_8W,_8W));});return B(A3(_7W,_8S,_8V,new T(function(){return B(A3(_8y,_8S,_8P,_8P));})));});return B(A2(_8K,_8N,_8U));});return new F(function(){return A3(_8A,_8S,_8T,new T(function(){return B(A2(_8C,_8R,_8G));}));});},_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T(function(){return B(unCStr("y"));}),_92=new T1(0,_91),_93=new T(function(){return B(unCStr("x"));}),_94=new T1(0,_93),_95=new T(function(){return B(_8M(_8t,_94,_92,_90));}),_96=new T(function(){return toJSStr(B(_1o(_1D,_11,_95)));}),_97=function(_98,_99,_9a){var _9b=new T(function(){return B(_1k(_98));}),_9c=new T(function(){return B(_1m(_98));}),_9d=function(_9e){var _9f=E(_9e);if(!_9f._){return E(_9c);}else{return new F(function(){return A2(_9b,new T(function(){return B(_1o(_98,_99,_9f.a));}),new T(function(){return B(_9d(_9f.b));}));});}};return new F(function(){return _9d(_9a);});},_9g=new T3(0,_94,_92,_90),_9h=function(_9i,_9j){var _9k=E(_9i);return E(_9j);},_9l=function(_9m,_9n){var _9o=E(_9m),_9p=E(_9n);return new T3(0,new T(function(){return B(A1(_9o.a,_9p.a));}),new T(function(){return B(A1(_9o.b,_9p.b));}),new T(function(){return B(A1(_9o.c,_9p.c));}));},_9q=function(_9r){return new T3(0,_9r,_9r,_9r);},_9s=function(_9t,_9u){var _9v=E(_9u);return new T3(0,_9t,_9t,_9t);},_9w=function(_9x,_9y){var _9z=E(_9y);return new T3(0,new T(function(){return B(A1(_9x,_9z.a));}),new T(function(){return B(A1(_9x,_9z.b));}),new T(function(){return B(A1(_9x,_9z.c));}));},_9A=new T2(0,_9w,_9s),_9B=function(_9C,_9D){var _9E=E(_9C),_9F=E(_9D);return new T3(0,_9E.a,_9E.b,_9E.c);},_9G=new T5(0,_9A,_9q,_9l,_9h,_9B),_9H=new T1(0,0),_9I=function(_9J){return E(E(_9J).g);},_9K=function(_9L){return new T3(0,new T3(0,new T(function(){return B(A2(_9I,_9L,_8E));}),new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_9H));})),new T3(0,new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_8E));}),new T(function(){return B(A2(_9I,_9L,_9H));})),new T3(0,new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_9H));}),new T(function(){return B(A2(_9I,_9L,_8E));})));},_9M=function(_9N){var _9O=B(_9K(_9N));return new T3(0,_9O.a,_9O.b,_9O.c);},_9P=function(_9Q){return E(E(_9Q).a);},_9R=function(_9S){return E(E(_9S).f);},_9T=function(_9U){return E(E(_9U).b);},_9V=function(_9W){return E(E(_9W).c);},_9X=function(_9Y){return E(E(_9Y).a);},_9Z=function(_a0){return E(E(_a0).d);},_a1=function(_a2,_a3,_a4,_a5,_a6){var _a7=new T(function(){return E(E(_a2).c);}),_a8=new T(function(){var _a9=E(_a2).a,_aa=new T(function(){var _ab=new T(function(){return B(_8u(_a7));}),_ac=new T(function(){return B(_8w(_ab));}),_ad=new T(function(){return B(A2(_9Z,_a7,_a3));}),_ae=new T(function(){return B(A3(_9R,_a7,_a3,_a5));}),_af=function(_ag,_ah){var _ai=new T(function(){var _aj=new T(function(){return B(A3(_9T,_ab,new T(function(){return B(A3(_8y,_ac,_a5,_ag));}),_a3));});return B(A3(_7W,_ac,_aj,new T(function(){return B(A3(_8y,_ac,_ah,_ad));})));});return new F(function(){return A3(_8y,_ac,_ae,_ai);});};return B(A3(_9X,B(_9P(_a9)),_af,_a4));});return B(A3(_9V,_a9,_aa,_a6));});return new T2(0,new T(function(){return B(A3(_9R,_a7,_a3,_a5));}),_a8);},_ak=function(_al,_am,_an,_ao){var _ap=E(_an),_aq=E(_ao),_ar=B(_a1(_am,_ap.a,_ap.b,_aq.a,_aq.b));return new T2(0,_ar.a,_ar.b);},_as=new T1(0,1),_at=function(_au){return E(E(_au).l);},_av=function(_aw,_ax,_ay){var _az=new T(function(){return E(E(_aw).c);}),_aA=new T(function(){var _aB=new T(function(){return B(_8u(_az));}),_aC=new T(function(){var _aD=B(_8w(_aB)),_aE=new T(function(){var _aF=new T(function(){return B(A3(_8A,_aD,new T(function(){return B(A2(_9I,_aD,_as));}),new T(function(){return B(A3(_8y,_aD,_ax,_ax));})));});return B(A2(_8K,_az,_aF));});return B(A2(_7Y,_aD,_aE));});return B(A3(_9X,B(_9P(E(_aw).a)),function(_aG){return new F(function(){return A3(_9T,_aB,_aG,_aC);});},_ay));});return new T2(0,new T(function(){return B(A2(_at,_az,_ax));}),_aA);},_aH=function(_aI,_aJ,_aK){var _aL=E(_aK),_aM=B(_av(_aJ,_aL.a,_aL.b));return new T2(0,_aM.a,_aM.b);},_aN=function(_aO){return E(E(_aO).r);},_aP=function(_aQ,_aR,_aS){var _aT=new T(function(){return E(E(_aQ).c);}),_aU=new T(function(){var _aV=new T(function(){return B(_8u(_aT));}),_aW=new T(function(){var _aX=new T(function(){var _aY=B(_8w(_aV));return B(A3(_8A,_aY,new T(function(){return B(A3(_8y,_aY,_aR,_aR));}),new T(function(){return B(A2(_9I,_aY,_as));})));});return B(A2(_8K,_aT,_aX));});return B(A3(_9X,B(_9P(E(_aQ).a)),function(_aZ){return new F(function(){return A3(_9T,_aV,_aZ,_aW);});},_aS));});return new T2(0,new T(function(){return B(A2(_aN,_aT,_aR));}),_aU);},_b0=function(_b1,_b2,_b3){var _b4=E(_b3),_b5=B(_aP(_b2,_b4.a,_b4.b));return new T2(0,_b5.a,_b5.b);},_b6=function(_b7){return E(E(_b7).k);},_b8=function(_b9,_ba,_bb){var _bc=new T(function(){return E(E(_b9).c);}),_bd=new T(function(){var _be=new T(function(){return B(_8u(_bc));}),_bf=new T(function(){var _bg=new T(function(){var _bh=B(_8w(_be));return B(A3(_8A,_bh,new T(function(){return B(A2(_9I,_bh,_as));}),new T(function(){return B(A3(_8y,_bh,_ba,_ba));})));});return B(A2(_8K,_bc,_bg));});return B(A3(_9X,B(_9P(E(_b9).a)),function(_bi){return new F(function(){return A3(_9T,_be,_bi,_bf);});},_bb));});return new T2(0,new T(function(){return B(A2(_b6,_bc,_ba));}),_bd);},_bj=function(_bk,_bl,_bm){var _bn=E(_bm),_bo=B(_b8(_bl,_bn.a,_bn.b));return new T2(0,_bo.a,_bo.b);},_bp=function(_bq){return E(E(_bq).q);},_br=function(_bs,_bt,_bu){var _bv=new T(function(){return E(E(_bs).c);}),_bw=new T(function(){var _bx=new T(function(){return B(_8u(_bv));}),_by=new T(function(){var _bz=new T(function(){var _bA=B(_8w(_bx));return B(A3(_7W,_bA,new T(function(){return B(A3(_8y,_bA,_bt,_bt));}),new T(function(){return B(A2(_9I,_bA,_as));})));});return B(A2(_8K,_bv,_bz));});return B(A3(_9X,B(_9P(E(_bs).a)),function(_bB){return new F(function(){return A3(_9T,_bx,_bB,_by);});},_bu));});return new T2(0,new T(function(){return B(A2(_bp,_bv,_bt));}),_bw);},_bC=function(_bD,_bE,_bF){var _bG=E(_bF),_bH=B(_br(_bE,_bG.a,_bG.b));return new T2(0,_bH.a,_bH.b);},_bI=function(_bJ){return E(E(_bJ).m);},_bK=function(_bL,_bM,_bN){var _bO=new T(function(){return E(E(_bL).c);}),_bP=new T(function(){var _bQ=new T(function(){return B(_8u(_bO));}),_bR=new T(function(){var _bS=B(_8w(_bQ));return B(A3(_7W,_bS,new T(function(){return B(A2(_9I,_bS,_as));}),new T(function(){return B(A3(_8y,_bS,_bM,_bM));})));});return B(A3(_9X,B(_9P(E(_bL).a)),function(_bT){return new F(function(){return A3(_9T,_bQ,_bT,_bR);});},_bN));});return new T2(0,new T(function(){return B(A2(_bI,_bO,_bM));}),_bP);},_bU=function(_bV,_bW,_bX){var _bY=E(_bX),_bZ=B(_bK(_bW,_bY.a,_bY.b));return new T2(0,_bZ.a,_bZ.b);},_c0=function(_c1){return E(E(_c1).s);},_c2=function(_c3,_c4,_c5){var _c6=new T(function(){return E(E(_c3).c);}),_c7=new T(function(){var _c8=new T(function(){return B(_8u(_c6));}),_c9=new T(function(){var _ca=B(_8w(_c8));return B(A3(_8A,_ca,new T(function(){return B(A2(_9I,_ca,_as));}),new T(function(){return B(A3(_8y,_ca,_c4,_c4));})));});return B(A3(_9X,B(_9P(E(_c3).a)),function(_cb){return new F(function(){return A3(_9T,_c8,_cb,_c9);});},_c5));});return new T2(0,new T(function(){return B(A2(_c0,_c6,_c4));}),_c7);},_cc=function(_cd,_ce,_cf){var _cg=E(_cf),_ch=B(_c2(_ce,_cg.a,_cg.b));return new T2(0,_ch.a,_ch.b);},_ci=function(_cj){return E(E(_cj).i);},_ck=function(_cl){return E(E(_cl).h);},_cm=function(_cn,_co,_cp){var _cq=new T(function(){return E(E(_cn).c);}),_cr=new T(function(){var _cs=new T(function(){return B(_8w(new T(function(){return B(_8u(_cq));})));}),_ct=new T(function(){return B(A2(_7Y,_cs,new T(function(){return B(A2(_ck,_cq,_co));})));});return B(A3(_9X,B(_9P(E(_cn).a)),function(_cu){return new F(function(){return A3(_8y,_cs,_cu,_ct);});},_cp));});return new T2(0,new T(function(){return B(A2(_ci,_cq,_co));}),_cr);},_cv=function(_cw,_cx,_cy){var _cz=E(_cy),_cA=B(_cm(_cx,_cz.a,_cz.b));return new T2(0,_cA.a,_cA.b);},_cB=function(_cC){return E(E(_cC).o);},_cD=function(_cE){return E(E(_cE).n);},_cF=function(_cG,_cH,_cI){var _cJ=new T(function(){return E(E(_cG).c);}),_cK=new T(function(){var _cL=new T(function(){return B(_8w(new T(function(){return B(_8u(_cJ));})));}),_cM=new T(function(){return B(A2(_cD,_cJ,_cH));});return B(A3(_9X,B(_9P(E(_cG).a)),function(_cN){return new F(function(){return A3(_8y,_cL,_cN,_cM);});},_cI));});return new T2(0,new T(function(){return B(A2(_cB,_cJ,_cH));}),_cK);},_cO=function(_cP,_cQ,_cR){var _cS=E(_cR),_cT=B(_cF(_cQ,_cS.a,_cS.b));return new T2(0,_cT.a,_cT.b);},_cU=function(_cV){return E(E(_cV).c);},_cW=function(_cX,_cY,_cZ){var _d0=new T(function(){return E(E(_cX).c);}),_d1=new T(function(){var _d2=new T(function(){return B(_8w(new T(function(){return B(_8u(_d0));})));}),_d3=new T(function(){return B(A2(_cU,_d0,_cY));});return B(A3(_9X,B(_9P(E(_cX).a)),function(_d4){return new F(function(){return A3(_8y,_d2,_d4,_d3);});},_cZ));});return new T2(0,new T(function(){return B(A2(_cU,_d0,_cY));}),_d1);},_d5=function(_d6,_d7,_d8){var _d9=E(_d8),_da=B(_cW(_d7,_d9.a,_d9.b));return new T2(0,_da.a,_da.b);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(_dc).c);}),_dg=new T(function(){var _dh=new T(function(){return B(_8u(_df));}),_di=new T(function(){return B(_8w(_dh));}),_dj=new T(function(){return B(A3(_9T,_dh,new T(function(){return B(A2(_9I,_di,_as));}),_dd));});return B(A3(_9X,B(_9P(E(_dc).a)),function(_dk){return new F(function(){return A3(_8y,_di,_dk,_dj);});},_de));});return new T2(0,new T(function(){return B(A2(_9Z,_df,_dd));}),_dg);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_db(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du,_dv){var _dw=new T3(0,new T(function(){return E(E(_dt).a);}),new T(function(){return E(E(_dt).b);}),new T(function(){return E(E(_dt).c);}));return new F(function(){return A3(_9T,_ds,new T(function(){var _dx=E(_dv),_dy=B(_db(_dw,_dx.a,_dx.b));return new T2(0,_dy.a,_dy.b);}),new T(function(){var _dz=E(_du),_dA=B(_db(_dw,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);}));});},_dB=new T1(0,0),_dC=function(_dD){return E(E(_dD).b);},_dE=function(_dF){return E(E(_dF).b);},_dG=function(_dH){var _dI=new T(function(){return E(E(_dH).c);}),_dJ=new T(function(){return B(A2(_dE,E(_dH).a,new T(function(){return B(A2(_9I,B(_8w(B(_8u(_dI)))),_dB));})));});return new T2(0,new T(function(){return B(_dC(_dI));}),_dJ);},_dK=function(_dL,_dM){var _dN=B(_dG(_dM));return new T2(0,_dN.a,_dN.b);},_dO=function(_dP,_dQ,_dR){var _dS=new T(function(){return E(E(_dP).c);}),_dT=new T(function(){var _dU=new T(function(){return B(_8w(new T(function(){return B(_8u(_dS));})));}),_dV=new T(function(){return B(A2(_ci,_dS,_dQ));});return B(A3(_9X,B(_9P(E(_dP).a)),function(_dW){return new F(function(){return A3(_8y,_dU,_dW,_dV);});},_dR));});return new T2(0,new T(function(){return B(A2(_ck,_dS,_dQ));}),_dT);},_dX=function(_dY,_dZ,_e0){var _e1=E(_e0),_e2=B(_dO(_dZ,_e1.a,_e1.b));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(_e4).c);}),_e8=new T(function(){var _e9=new T(function(){return B(_8w(new T(function(){return B(_8u(_e7));})));}),_ea=new T(function(){return B(A2(_cB,_e7,_e5));});return B(A3(_9X,B(_9P(E(_e4).a)),function(_eb){return new F(function(){return A3(_8y,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cD,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=new T1(0,2),_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(_ek).c);}),_eo=new T(function(){var _ep=new T(function(){return B(_8u(_en));}),_eq=new T(function(){return B(_8w(_ep));}),_er=new T(function(){var _es=new T(function(){return B(A3(_9T,_ep,new T(function(){return B(A2(_9I,_eq,_as));}),new T(function(){return B(A2(_9I,_eq,_ei));})));});return B(A3(_9T,_ep,_es,new T(function(){return B(A2(_8K,_en,_el));})));});return B(A3(_9X,B(_9P(E(_ek).a)),function(_et){return new F(function(){return A3(_8y,_eq,_et,_er);});},_em));});return new T2(0,new T(function(){return B(A2(_8K,_en,_el));}),_eo);},_eu=function(_ev,_ew,_ex){var _ey=E(_ex),_ez=B(_ej(_ew,_ey.a,_ey.b));return new T2(0,_ez.a,_ez.b);},_eA=function(_eB){return E(E(_eB).j);},_eC=function(_eD,_eE,_eF){var _eG=new T(function(){return E(E(_eD).c);}),_eH=new T(function(){var _eI=new T(function(){return B(_8u(_eG));}),_eJ=new T(function(){var _eK=new T(function(){return B(A2(_ci,_eG,_eE));});return B(A3(_8y,B(_8w(_eI)),_eK,_eK));});return B(A3(_9X,B(_9P(E(_eD).a)),function(_eL){return new F(function(){return A3(_9T,_eI,_eL,_eJ);});},_eF));});return new T2(0,new T(function(){return B(A2(_eA,_eG,_eE));}),_eH);},_eM=function(_eN,_eO,_eP){var _eQ=E(_eP),_eR=B(_eC(_eO,_eQ.a,_eQ.b));return new T2(0,_eR.a,_eR.b);},_eS=function(_eT){return E(E(_eT).p);},_eU=function(_eV,_eW,_eX){var _eY=new T(function(){return E(E(_eV).c);}),_eZ=new T(function(){var _f0=new T(function(){return B(_8u(_eY));}),_f1=new T(function(){var _f2=new T(function(){return B(A2(_cB,_eY,_eW));});return B(A3(_8y,B(_8w(_f0)),_f2,_f2));});return B(A3(_9X,B(_9P(E(_eV).a)),function(_f3){return new F(function(){return A3(_9T,_f0,_f3,_f1);});},_eX));});return new T2(0,new T(function(){return B(A2(_eS,_eY,_eW));}),_eZ);},_f4=function(_f5,_f6,_f7){var _f8=E(_f7),_f9=B(_eU(_f6,_f8.a,_f8.b));return new T2(0,_f9.a,_f9.b);},_fa=function(_fb,_fc){return {_:0,a:_fb,b:new T(function(){return B(_dK(_fb,_fc));}),c:function(_fd){return new F(function(){return _d5(_fb,_fc,_fd);});},d:function(_fd){return new F(function(){return _dl(_fb,_fc,_fd);});},e:function(_fd){return new F(function(){return _eu(_fb,_fc,_fd);});},f:function(_fe,_fd){return new F(function(){return _ak(_fb,_fc,_fe,_fd);});},g:function(_fe,_fd){return new F(function(){return _dr(_fb,_fc,_fe,_fd);});},h:function(_fd){return new F(function(){return _dX(_fb,_fc,_fd);});},i:function(_fd){return new F(function(){return _cv(_fb,_fc,_fd);});},j:function(_fd){return new F(function(){return _eM(_fb,_fc,_fd);});},k:function(_fd){return new F(function(){return _bj(_fb,_fc,_fd);});},l:function(_fd){return new F(function(){return _aH(_fb,_fc,_fd);});},m:function(_fd){return new F(function(){return _bU(_fb,_fc,_fd);});},n:function(_fd){return new F(function(){return _ec(_fb,_fc,_fd);});},o:function(_fd){return new F(function(){return _cO(_fb,_fc,_fd);});},p:function(_fd){return new F(function(){return _f4(_fb,_fc,_fd);});},q:function(_fd){return new F(function(){return _bC(_fb,_fc,_fd);});},r:function(_fd){return new F(function(){return _b0(_fb,_fc,_fd);});},s:function(_fd){return new F(function(){return _cc(_fb,_fc,_fd);});}};},_ff=function(_fg,_fh,_fi,_fj,_fk){var _fl=new T(function(){return B(_8u(new T(function(){return E(E(_fg).c);})));}),_fm=new T(function(){var _fn=E(_fg).a,_fo=new T(function(){var _fp=new T(function(){return B(_8w(_fl));}),_fq=new T(function(){return B(A3(_8y,_fp,_fj,_fj));}),_fr=function(_fs,_ft){var _fu=new T(function(){return B(A3(_8A,_fp,new T(function(){return B(A3(_8y,_fp,_fs,_fj));}),new T(function(){return B(A3(_8y,_fp,_fh,_ft));})));});return new F(function(){return A3(_9T,_fl,_fu,_fq);});};return B(A3(_9X,B(_9P(_fn)),_fr,_fi));});return B(A3(_9V,_fn,_fo,_fk));});return new T2(0,new T(function(){return B(A3(_9T,_fl,_fh,_fj));}),_fm);},_fv=function(_fw,_fx,_fy,_fz){var _fA=E(_fy),_fB=E(_fz),_fC=B(_ff(_fx,_fA.a,_fA.b,_fB.a,_fB.b));return new T2(0,_fC.a,_fC.b);},_fD=function(_fE,_fF){var _fG=new T(function(){return B(_8u(new T(function(){return E(E(_fE).c);})));}),_fH=new T(function(){return B(A2(_dE,E(_fE).a,new T(function(){return B(A2(_9I,B(_8w(_fG)),_dB));})));});return new T2(0,new T(function(){return B(A2(_8C,_fG,_fF));}),_fH);},_fI=function(_fJ,_fK,_fL){var _fM=B(_fD(_fK,_fL));return new T2(0,_fM.a,_fM.b);},_fN=function(_fO,_fP,_fQ){var _fR=new T(function(){return B(_8u(new T(function(){return E(E(_fO).c);})));}),_fS=new T(function(){return B(_8w(_fR));}),_fT=new T(function(){var _fU=new T(function(){var _fV=new T(function(){return B(A3(_9T,_fR,new T(function(){return B(A2(_9I,_fS,_as));}),new T(function(){return B(A3(_8y,_fS,_fP,_fP));})));});return B(A2(_7Y,_fS,_fV));});return B(A3(_9X,B(_9P(E(_fO).a)),function(_fW){return new F(function(){return A3(_8y,_fS,_fW,_fU);});},_fQ));}),_fX=new T(function(){return B(A3(_9T,_fR,new T(function(){return B(A2(_9I,_fS,_as));}),_fP));});return new T2(0,_fX,_fT);},_fY=function(_fZ,_g0,_g1){var _g2=E(_g1),_g3=B(_fN(_g0,_g2.a,_g2.b));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6){return new T4(0,_g5,function(_fe,_fd){return new F(function(){return _fv(_g5,_g6,_fe,_fd);});},function(_fd){return new F(function(){return _fY(_g5,_g6,_fd);});},function(_fd){return new F(function(){return _fI(_g5,_g6,_fd);});});},_g7=function(_g8,_g9,_ga,_gb,_gc){var _gd=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_g8).c);})));})));}),_ge=new T(function(){var _gf=E(_g8).a,_gg=new T(function(){var _gh=function(_gi,_gj){return new F(function(){return A3(_7W,_gd,new T(function(){return B(A3(_8y,_gd,_g9,_gj));}),new T(function(){return B(A3(_8y,_gd,_gi,_gb));}));});};return B(A3(_9X,B(_9P(_gf)),_gh,_ga));});return B(A3(_9V,_gf,_gg,_gc));});return new T2(0,new T(function(){return B(A3(_8y,_gd,_g9,_gb));}),_ge);},_gk=function(_gl,_gm,_gn){var _go=E(_gm),_gp=E(_gn),_gq=B(_g7(_gl,_go.a,_go.b,_gp.a,_gp.b));return new T2(0,_gq.a,_gq.b);},_gr=function(_gs,_gt,_gu,_gv,_gw){var _gx=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_gs).c);})));})));}),_gy=new T(function(){var _gz=E(_gs).a,_gA=new T(function(){return B(A3(_9X,B(_9P(_gz)),new T(function(){return B(_7W(_gx));}),_gu));});return B(A3(_9V,_gz,_gA,_gw));});return new T2(0,new T(function(){return B(A3(_7W,_gx,_gt,_gv));}),_gy);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_gr(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL){var _gM=B(_gN(_gJ));return new F(function(){return A3(_7W,_gM,_gK,new T(function(){return B(A2(_7Y,_gM,_gL));}));});},_gO=function(_gP){return E(E(_gP).e);},_gQ=function(_gR){return E(E(_gR).f);},_gS=function(_gT,_gU,_gV){var _gW=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_gT).c);})));})));}),_gX=new T(function(){var _gY=new T(function(){return B(A2(_gQ,_gW,_gU));});return B(A3(_9X,B(_9P(E(_gT).a)),function(_gZ){return new F(function(){return A3(_8y,_gW,_gZ,_gY);});},_gV));});return new T2(0,new T(function(){return B(A2(_gO,_gW,_gU));}),_gX);},_h0=function(_h1,_h2){var _h3=E(_h2),_h4=B(_gS(_h1,_h3.a,_h3.b));return new T2(0,_h4.a,_h4.b);},_h5=function(_h6,_h7){var _h8=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_h6).c);})));})));}),_h9=new T(function(){return B(A2(_dE,E(_h6).a,new T(function(){return B(A2(_9I,_h8,_dB));})));});return new T2(0,new T(function(){return B(A2(_9I,_h8,_h7));}),_h9);},_ha=function(_hb,_hc){var _hd=B(_h5(_hb,_hc));return new T2(0,_hd.a,_hd.b);},_he=function(_hf,_hg,_hh){var _hi=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_hf).c);})));})));}),_hj=new T(function(){return B(A3(_9X,B(_9P(E(_hf).a)),new T(function(){return B(_7Y(_hi));}),_hh));});return new T2(0,new T(function(){return B(A2(_7Y,_hi,_hg));}),_hj);},_hk=function(_hl,_hm){var _hn=E(_hm),_ho=B(_he(_hl,_hn.a,_hn.b));return new T2(0,_ho.a,_ho.b);},_hp=function(_hq,_hr){var _hs=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(_hq).c);})));})));}),_ht=new T(function(){return B(A2(_dE,E(_hq).a,new T(function(){return B(A2(_9I,_hs,_dB));})));});return new T2(0,new T(function(){return B(A2(_gQ,_hs,_hr));}),_ht);},_hu=function(_hv,_hw){var _hx=B(_hp(_hv,E(_hw).a));return new T2(0,_hx.a,_hx.b);},_gN=function(_hy){return {_:0,a:function(_fe,_fd){return new F(function(){return _gB(_hy,_fe,_fd);});},b:function(_fe,_fd){return new F(function(){return _gI(_hy,_fe,_fd);});},c:function(_fe,_fd){return new F(function(){return _gk(_hy,_fe,_fd);});},d:function(_fd){return new F(function(){return _hk(_hy,_fd);});},e:function(_fd){return new F(function(){return _h0(_hy,_fd);});},f:function(_fd){return new F(function(){return _hu(_hy,_fd);});},g:function(_fd){return new F(function(){return _ha(_hy,_fd);});}};},_hz=function(_hA){var _hB=new T3(0,_9G,_9M,_hA),_hC=new T(function(){return B(_fa(new T(function(){return B(_g4(new T(function(){return B(_gN(_hB));}),_hB));}),_hB));}),_hD=new T(function(){return B(_8w(new T(function(){return B(_8u(_hA));})));});return function(_hE){var _hF=E(_hE),_hG=B(_9K(_hD));return E(B(_8M(_hC,new T2(0,_hF.a,_hG.a),new T2(0,_hF.b,_hG.b),new T2(0,_hF.c,_hG.c))).b);};},_hH=new T(function(){return B(_hz(_8t));}),_hI=function(_hJ,_hK){var _hL=E(_hK);return (_hL._==0)?__Z:new T2(1,_hJ,new T2(1,_hL.a,new T(function(){return B(_hI(_hJ,_hL.b));})));},_hM=new T(function(){var _hN=B(A1(_hH,_9g));return new T2(1,_hN.a,new T(function(){return B(_hI(_1F,new T2(1,_hN.b,new T2(1,_hN.c,_T))));}));}),_hO=new T1(1,_hM),_hP=new T2(1,_hO,_1K),_hQ=new T(function(){return B(unCStr("vec3("));}),_hR=new T1(0,_hQ),_hS=new T2(1,_hR,_hP),_hT=new T(function(){return toJSStr(B(_97(_1D,_11,_hS)));}),_hU=function(_hV,_hW){while(1){var _hX=E(_hV);if(!_hX._){return E(_hW);}else{var _hY=_hW+1|0;_hV=_hX.b;_hW=_hY;continue;}}},_hZ=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_i0=new T(function(){return B(err(_hZ));}),_i1=new T(function(){return B(unCStr("Negative exponent"));}),_i2=new T(function(){return B(err(_i1));}),_i3=function(_i4,_i5,_i6){while(1){if(!(_i5%2)){var _i7=_i4*_i4,_i8=quot(_i5,2);_i4=_i7;_i5=_i8;continue;}else{var _i9=E(_i5);if(_i9==1){return _i4*_i6;}else{var _i7=_i4*_i4,_ia=_i4*_i6;_i4=_i7;_i5=quot(_i9-1|0,2);_i6=_ia;continue;}}}},_ib=function(_ic,_id){while(1){if(!(_id%2)){var _ie=_ic*_ic,_if=quot(_id,2);_ic=_ie;_id=_if;continue;}else{var _ig=E(_id);if(_ig==1){return E(_ic);}else{return new F(function(){return _i3(_ic*_ic,quot(_ig-1|0,2),_ic);});}}}},_ih=function(_ii,_ij){return (E(_ii)!=E(_ij))?true:false;},_ik=function(_il,_im){return E(_il)==E(_im);},_in=new T2(0,_ik,_ih),_io=function(_ip){var _iq=E(_ip);return new F(function(){return Math.log(_iq+(_iq+1)*Math.sqrt((_iq-1)/(_iq+1)));});},_ir=function(_is){var _it=E(_is);return new F(function(){return Math.log(_it+Math.sqrt(1+_it*_it));});},_iu=function(_iv){var _iw=E(_iv);return 0.5*Math.log((1+_iw)/(1-_iw));},_ix=function(_iy,_iz){return Math.log(E(_iz))/Math.log(E(_iy));},_iA=3.141592653589793,_iB=function(_iC){var _iD=E(_iC);return new F(function(){return _7x(_iD.a,_iD.b);});},_iE=function(_iF){return 1/E(_iF);},_iG=function(_iH){var _iI=E(_iH),_iJ=E(_iI);return (_iJ==0)?E(_7w):(_iJ<=0)? -_iJ:E(_iI);},_iK=function(_iL){var _iM=E(_iL);if(!_iM._){return _iM.a;}else{return new F(function(){return I_toNumber(_iM.a);});}},_iN=function(_iO){return new F(function(){return _iK(_iO);});},_iP=1,_iQ=-1,_iR=function(_iS){var _iT=E(_iS);return (_iT<=0)?(_iT>=0)?E(_iT):E(_iQ):E(_iP);},_iU=function(_iV,_iW){return E(_iV)-E(_iW);},_iX=function(_iY){return  -E(_iY);},_iZ=function(_j0,_j1){return E(_j0)+E(_j1);},_j2=function(_j3,_j4){return E(_j3)*E(_j4);},_j5={_:0,a:_iZ,b:_iU,c:_j2,d:_iX,e:_iG,f:_iR,g:_iN},_j6=function(_j7,_j8){return E(_j7)/E(_j8);},_j9=new T4(0,_j5,_j6,_iE,_iB),_ja=function(_jb){return new F(function(){return Math.acos(E(_jb));});},_jc=function(_jd){return new F(function(){return Math.asin(E(_jd));});},_je=function(_jf){return new F(function(){return Math.atan(E(_jf));});},_jg=function(_jh){return new F(function(){return Math.cos(E(_jh));});},_ji=function(_jj){return new F(function(){return cosh(E(_jj));});},_jk=function(_jl){return new F(function(){return Math.exp(E(_jl));});},_jm=function(_jn){return new F(function(){return Math.log(E(_jn));});},_jo=function(_jp,_jq){return new F(function(){return Math.pow(E(_jp),E(_jq));});},_jr=function(_js){return new F(function(){return Math.sin(E(_js));});},_jt=function(_ju){return new F(function(){return sinh(E(_ju));});},_jv=function(_jw){return new F(function(){return Math.sqrt(E(_jw));});},_jx=function(_jy){return new F(function(){return Math.tan(E(_jy));});},_jz=function(_jA){return new F(function(){return tanh(E(_jA));});},_jB={_:0,a:_j9,b:_iA,c:_jk,d:_jm,e:_jv,f:_jo,g:_ix,h:_jr,i:_jg,j:_jx,k:_jc,l:_ja,m:_je,n:_jt,o:_ji,p:_jz,q:_ir,r:_io,s:_iu},_jC=function(_jD,_jE,_jF,_jG,_jH,_jI,_jJ){var _jK=B(_8w(B(_8u(_jD)))),_jL=new T(function(){return B(A3(_7W,_jK,new T(function(){return B(A3(_8y,_jK,_jE,_jH));}),new T(function(){return B(A3(_8y,_jK,_jF,_jI));})));});return new F(function(){return A3(_7W,_jK,_jL,new T(function(){return B(A3(_8y,_jK,_jG,_jJ));}));});},_jM=function(_jN,_jO,_jP,_jQ){var _jR=new T(function(){return B(_8u(_jN));}),_jS=new T(function(){return B(A2(_8K,_jN,new T(function(){return B(_jC(_jN,_jO,_jP,_jQ,_jO,_jP,_jQ));})));});return new T3(0,new T(function(){return B(A3(_9T,_jR,_jO,_jS));}),new T(function(){return B(A3(_9T,_jR,_jP,_jS));}),new T(function(){return B(A3(_9T,_jR,_jQ,_jS));}));},_jT=function(_jU,_jV){var _jW=new T(function(){return B(A2(_hz,_jU,_jV));}),_jX=new T(function(){var _jY=E(_jW),_jZ=B(_jM(_jU,_jY.a,_jY.b,_jY.c));return new T3(0,_jZ.a,_jZ.b,_jZ.c);}),_k0=new T(function(){var _k1=E(_jV),_k2=_k1.a,_k3=_k1.b,_k4=_k1.c,_k5=E(_jX),_k6=new T(function(){return B(_8u(_jU));}),_k7=new T(function(){return B(_8w(_k6));}),_k8=new T(function(){return B(_7W(_k7));}),_k9=new T(function(){return B(_7Y(_k7));}),_ka=new T(function(){return B(_8y(_k7));}),_kb=new T(function(){var _kc=new T(function(){return B(A2(_8K,_jU,new T(function(){var _kd=E(_jW),_ke=_kd.a,_kf=_kd.b,_kg=_kd.c;return B(_jC(_jU,_ke,_kf,_kg,_ke,_kf,_kg));})));});return B(A3(_9T,_k6,new T(function(){return B(_8M(_jU,_k2,_k3,_k4));}),_kc));}),_kh=new T(function(){var _ki=new T(function(){return B(A1(_k9,new T(function(){return B(A2(_ka,_k5.c,_kb));})));});return B(A2(_k8,_k4,_ki));}),_kj=new T(function(){var _kk=new T(function(){return B(A1(_k9,new T(function(){return B(A2(_ka,_k5.b,_kb));})));});return B(A2(_k8,_k3,_kk));}),_kl=new T(function(){var _km=new T(function(){return B(A1(_k9,new T(function(){return B(A2(_ka,_k5.a,_kb));})));});return B(A2(_k8,_k2,_km));});return new T3(0,_kl,_kj,_kh);});return new T2(0,_k0,_jX);},_kn=function(_ko,_kp,_kq,_kr,_ks,_kt,_ku){var _kv=new T(function(){return B(_8w(new T(function(){return B(_8u(_ko));})));}),_kw=new T(function(){return B(_7W(_kv));}),_kx=new T(function(){return B(_7Y(_kv));}),_ky=new T(function(){return B(_8y(_kv));}),_kz=new T(function(){return B(_jC(_ko,_ks,_kt,_ku,_kp,_kq,_kr));}),_kA=new T(function(){var _kB=new T(function(){return B(A1(_kx,new T(function(){return B(A2(_ky,_ku,_kz));})));});return B(A2(_kw,_kr,_kB));}),_kC=new T(function(){var _kD=new T(function(){return B(A1(_kx,new T(function(){return B(A2(_ky,_kt,_kz));})));});return B(A2(_kw,_kq,_kD));}),_kE=new T(function(){var _kF=new T(function(){return B(A1(_kx,new T(function(){return B(A2(_ky,_ks,_kz));})));});return B(A2(_kw,_kp,_kF));});return new T3(0,_kE,_kC,_kA);},_kG=function(_kH){return E(E(_kH).a);},_kI=function(_kJ,_kK,_kL,_kM){var _kN=new T(function(){var _kO=E(_kM),_kP=E(_kL),_kQ=B(_kn(_kK,_kO.a,_kO.b,_kO.c,_kP.a,_kP.b,_kP.c));return new T3(0,_kQ.a,_kQ.b,_kQ.c);}),_kR=new T(function(){return B(A2(_8K,_kK,new T(function(){var _kS=E(_kN),_kT=_kS.a,_kU=_kS.b,_kV=_kS.c;return B(_jC(_kK,_kT,_kU,_kV,_kT,_kU,_kV));})));});if(!B(A3(_kG,_kJ,_kR,new T(function(){return B(A2(_9I,B(_8w(B(_8u(_kK)))),_9H));})))){var _kW=E(_kN),_kX=B(_jM(_kK,_kW.a,_kW.b,_kW.c)),_kY=new T(function(){return B(_8y(new T(function(){return B(_8w(new T(function(){return B(_8u(_kK));})));})));}),_kZ=new T(function(){return B(A2(_8K,_kK,new T(function(){var _l0=E(_kM),_l1=_l0.a,_l2=_l0.b,_l3=_l0.c;return B(_jC(_kK,_l1,_l2,_l3,_l1,_l2,_l3));})));});return new T3(0,new T(function(){return B(A2(_kY,_kX.a,_kZ));}),new T(function(){return B(A2(_kY,_kX.b,_kZ));}),new T(function(){return B(A2(_kY,_kX.c,_kZ));}));}else{var _l4=new T(function(){return B(A2(_9I,B(_8w(B(_8u(_kK)))),_9H));});return new T3(0,_l4,_l4,_l4);}},_l5=0,_l6=new T(function(){var _l7=eval("angleCount"),_l8=Number(_l7);return jsTrunc(_l8);}),_l9=new T(function(){return E(_l6);}),_la=new T(function(){return B(unCStr(": empty list"));}),_lb=new T(function(){return B(unCStr("Prelude."));}),_lc=function(_ld){return new F(function(){return err(B(_14(_lb,new T(function(){return B(_14(_ld,_la));},1))));});},_le=new T(function(){return B(unCStr("head"));}),_lf=new T(function(){return B(_lc(_le));}),_lg=function(_lh,_li,_lj){var _lk=E(_lh);if(!_lk._){return __Z;}else{var _ll=E(_li);if(!_ll._){return __Z;}else{var _lm=_ll.a,_ln=E(_lj);if(!_ln._){return __Z;}else{var _lo=E(_ln.a),_lp=_lo.a;return new F(function(){return _14(new T2(1,new T3(0,_lk.a,_lm,_lp),new T2(1,new T3(0,_lm,_lp,_lo.b),_T)),new T(function(){return B(_lg(_lk.b,_ll.b,_ln.b));},1));});}}}},_lq=new T(function(){return B(unCStr("tail"));}),_lr=new T(function(){return B(_lc(_lq));}),_ls=function(_lt,_lu){var _lv=E(_lt);if(!_lv._){return __Z;}else{var _lw=E(_lu);return (_lw._==0)?__Z:new T2(1,new T2(0,_lv.a,_lw.a),new T(function(){return B(_ls(_lv.b,_lw.b));}));}},_lx=function(_ly,_lz){var _lA=E(_ly);if(!_lA._){return __Z;}else{var _lB=E(_lz);if(!_lB._){return __Z;}else{var _lC=E(_lA.a),_lD=_lC.b,_lE=E(_lB.a).b,_lF=new T(function(){var _lG=new T(function(){return B(_ls(_lE,new T(function(){var _lH=E(_lE);if(!_lH._){return E(_lr);}else{return E(_lH.b);}},1)));},1);return B(_lg(_lD,new T(function(){var _lI=E(_lD);if(!_lI._){return E(_lr);}else{return E(_lI.b);}},1),_lG));});return new F(function(){return _14(new T2(1,new T3(0,_lC.a,new T(function(){var _lJ=E(_lD);if(!_lJ._){return E(_lf);}else{return E(_lJ.a);}}),new T(function(){var _lK=E(_lE);if(!_lK._){return E(_lf);}else{return E(_lK.a);}})),_lF),new T(function(){return B(_lx(_lA.b,_lB.b));},1));});}}},_lL=function(_lM,_lN){return E(_lM)<E(_lN);},_lO=function(_lP,_lQ){return E(_lP)<=E(_lQ);},_lR=function(_lS,_lT){return E(_lS)>E(_lT);},_lU=function(_lV,_lW){return E(_lV)>=E(_lW);},_lX=function(_lY,_lZ){var _m0=E(_lY),_m1=E(_lZ);return (_m0>=_m1)?(_m0!=_m1)?2:1:0;},_m2=function(_m3,_m4){var _m5=E(_m3),_m6=E(_m4);return (_m5>_m6)?E(_m5):E(_m6);},_m7=function(_m8,_m9){var _ma=E(_m8),_mb=E(_m9);return (_ma>_mb)?E(_mb):E(_ma);},_mc={_:0,a:_in,b:_lX,c:_lL,d:_lO,e:_lR,f:_lU,g:_m2,h:_m7},_md=new T(function(){return E(_l9)-1;}),_me=new T1(0,1),_mf=function(_mg,_mh){var _mi=E(_mh),_mj=new T(function(){var _mk=B(_8w(_mg)),_ml=B(_mf(_mg,B(A3(_7W,_mk,_mi,new T(function(){return B(A2(_9I,_mk,_me));})))));return new T2(1,_ml.a,_ml.b);});return new T2(0,_mi,_mj);},_mm=function(_mn){return E(E(_mn).d);},_mo=new T1(0,2),_mp=function(_mq,_mr){var _ms=E(_mr);if(!_ms._){return __Z;}else{var _mt=_ms.a;return (!B(A1(_mq,_mt)))?__Z:new T2(1,_mt,new T(function(){return B(_mp(_mq,_ms.b));}));}},_mu=function(_mv,_mw,_mx,_my){var _mz=B(_mf(_mw,_mx)),_mA=new T(function(){var _mB=B(_8w(_mw)),_mC=new T(function(){return B(A3(_9T,_mw,new T(function(){return B(A2(_9I,_mB,_me));}),new T(function(){return B(A2(_9I,_mB,_mo));})));});return B(A3(_7W,_mB,_my,_mC));});return new F(function(){return _mp(function(_mD){return new F(function(){return A3(_mm,_mv,_mD,_mA);});},new T2(1,_mz.a,_mz.b));});},_mE=new T(function(){return B(_mu(_mc,_j9,_l5,_md));}),_mF=function(_mG,_mH){var _mI=E(_mH);return (_mI._==0)?__Z:new T2(1,new T(function(){return B(A1(_mG,_mI.a));}),new T(function(){return B(_mF(_mG,_mI.b));}));},_mJ=new T(function(){var _mK=eval("proceedCount"),_mL=Number(_mK);return jsTrunc(_mL);}),_mM=new T(function(){return E(_mJ);}),_mN=1,_mO=new T(function(){return B(_mu(_mc,_j9,_mN,_mM));}),_mP=function(_mQ,_mR,_mS,_mT,_mU){var _mV=new T(function(){var _mW=E(_mT),_mX=_mW.a,_mY=_mW.b,_mZ=_mW.c,_n0=E(_mU),_n1=_n0.a,_n2=_n0.b,_n3=_n0.c;return new T3(0,new T(function(){return E(_mY)*E(_n3)-E(_n2)*E(_mZ);}),new T(function(){return E(_mZ)*E(_n1)-E(_n3)*E(_mX);}),new T(function(){return E(_mX)*E(_n2)-E(_n1)*E(_mY);}));}),_n4=function(_n5){var _n6=new T(function(){var _n7=E(_n5)/E(_l9);return (_n7+_n7)*3.141592653589793;}),_n8=new T(function(){return B(A1(_mQ,_n6));}),_n9=new T(function(){return E(_n6)+E(_mS);}),_na=new T(function(){var _nb=new T(function(){return E(_n8)/E(_mM);}),_nc=function(_nd,_ne){var _nf=E(_nd);if(!_nf._){return new T2(0,_T,_ne);}else{var _ng=new T(function(){var _nh=new T(function(){var _ni=E(_ne),_nj=E(_ni.a),_nk=E(_ni.b);return new T3(0,new T(function(){return E(_nj.a)+E(_nk.a)*E(_nb);}),new T(function(){return E(_nj.b)+E(_nk.b)*E(_nb);}),new T(function(){return E(_nj.c)+E(_nk.c)*E(_nb);}));}),_nl=B(_jT(_jB,_nh)),_nm=_nl.a;return new T2(0,new T3(0,_nm,new T2(0,new T(function(){return E(_nf.a)/E(_mM);}),_n8),_n9),new T2(0,_nm,new T(function(){var _nn=E(E(_ne).b),_no=E(_nl.b),_np=B(_kn(_jB,_nn.a,_nn.b,_nn.c,_no.a,_no.b,_no.c)),_nq=B(_jM(_jB,_np.a,_np.b,_np.c));return new T3(0,_nq.a,_nq.b,_nq.c);})));}),_nr=new T(function(){var _ns=B(_nc(_nf.b,new T(function(){return E(E(_ng).b);})));return new T2(0,_ns.a,_ns.b);});return new T2(0,new T2(1,new T(function(){return E(E(_ng).a);}),new T(function(){return E(E(_nr).a);})),new T(function(){return E(E(_nr).b);}));}},_nt=function(_nu,_nv,_nw){var _nx=E(_nu);if(!_nx._){return new T2(0,_T,new T2(0,_nv,_nw));}else{var _ny=new T(function(){var _nz=new T(function(){var _nA=E(_nv),_nB=E(_nw);return new T3(0,new T(function(){return E(_nA.a)+E(_nB.a)*E(_nb);}),new T(function(){return E(_nA.b)+E(_nB.b)*E(_nb);}),new T(function(){return E(_nA.c)+E(_nB.c)*E(_nb);}));}),_nC=B(_jT(_jB,_nz)),_nD=_nC.a;return new T2(0,new T3(0,_nD,new T2(0,new T(function(){return E(_nx.a)/E(_mM);}),_n8),_n9),new T2(0,_nD,new T(function(){var _nE=E(_nw),_nF=E(_nC.b),_nG=B(_kn(_jB,_nE.a,_nE.b,_nE.c,_nF.a,_nF.b,_nF.c)),_nH=B(_jM(_jB,_nG.a,_nG.b,_nG.c));return new T3(0,_nH.a,_nH.b,_nH.c);})));}),_nI=new T(function(){var _nJ=B(_nc(_nx.b,new T(function(){return E(E(_ny).b);})));return new T2(0,_nJ.a,_nJ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_ny).a);}),new T(function(){return E(E(_nI).a);})),new T(function(){return E(E(_nI).b);}));}},_nK=new T(function(){var _nL=E(_mT),_nM=E(_mV),_nN=new T(function(){return Math.cos(E(_n9));}),_nO=new T(function(){return Math.sin(E(_n9));});return new T3(0,new T(function(){return E(_nL.a)*E(_nN)+E(_nM.a)*E(_nO);}),new T(function(){return E(_nL.b)*E(_nN)+E(_nM.b)*E(_nO);}),new T(function(){return E(_nL.c)*E(_nN)+E(_nM.c)*E(_nO);}));});return E(B(_nt(_mO,_mR,_nK)).a);});return new T2(0,new T3(0,_mR,new T2(0,_l5,_n8),_n9),_na);},_nP=B(_mF(_n4,_mE)),_nQ=new T(function(){var _nR=B(_14(_nP,new T2(1,new T(function(){var _nS=E(_nP);if(!_nS._){return E(_lf);}else{return E(_nS.a);}}),_T)));if(!_nR._){return E(_lr);}else{return E(_nR.b);}},1);return new F(function(){return _lx(_nP,_nQ);});},_nT=function(_nU,_nV,_nW,_nX,_nY,_nZ){var _o0=new T(function(){var _o1=B(_jT(_jB,new T(function(){return E(E(_nX).a);})));return new T2(0,_o1.a,_o1.b);}),_o2=new T(function(){return E(E(_o0).b);}),_o3=new T(function(){var _o4=E(_nZ),_o5=E(_o2),_o6=B(_kn(_jB,_o4.a,_o4.b,_o4.c,_o5.a,_o5.b,_o5.c)),_o7=B(_jM(_jB,_o6.a,_o6.b,_o6.c));return new T3(0,_o7.a,_o7.b,_o7.c);}),_o8=new T(function(){return new T2(0,new T(function(){return E(E(_o0).a);}),E(_nX).b);}),_o9=new T(function(){var _oa=E(_nY);return new T2(0,new T(function(){var _ob=B(_kI(_in,_jB,_o2,_oa.a));return new T3(0,_ob.a,_ob.b,_ob.c);}),_oa.b);});return {_:0,a:_nU,b:_nV,c:_nW,d:_o8,e:_o9,f:_o3,g:_o2,h:new T(function(){var _oc=E(_o8);return B(_mP(_nU,_oc.a,_oc.b,_o3,_o2));})};},_od=function(_oe,_of){if(_oe<=_of){var _og=function(_oh){return new T2(1,_oh,new T(function(){if(_oh!=_of){return B(_og(_oh+1|0));}else{return __Z;}}));};return new F(function(){return _og(_oe);});}else{return __Z;}},_oi=-1,_oj=0.5,_ok=new T3(0,_l5,_oj,_oi),_ol=new T(function(){return 6.283185307179586/E(_l9);}),_om=function(_on,_oo,_op,_oq,_or){var _os=function(_ot){var _ou=E(_ol),_ov=2+_ot|0,_ow=_ov-1|0,_ox=new T(function(){return B(_od(0,_ov-1|0));}),_oy=E(_mE);if(!_oy._){return _ou*0;}else{var _oz=_oy.a,_oA=new T(function(){return B(A1(_on,new T(function(){return 6.283185307179586*E(_oz)/E(_l9);})));}),_oB=new T(function(){return B(A1(_on,new T(function(){return 6.283185307179586*(E(_oz)+1)/E(_l9);})));}),_oC=function(_oD,_oE){while(1){var _oF=B((function(_oG,_oH){var _oI=E(_oG);if(!_oI._){return E(_oH);}else{var _oJ=_oI.b,_oK=E(_oI.a);if(_oK>=0){var _oL=function(_oM){var _oN=_ow-_oK|0;if(_oN>=0){var _oO=E(_oN);return (_oO==0)?_oH+_oM:_oH+_oM*B(_ib(E(_oB),_oO));}else{return E(_i2);}},_oP=E(_oK);if(!_oP){_oD=_oJ;_oE=B(_oL(1));return __continue;}else{var _oQ=E(_oA),_oR=function(_oS,_oT){while(1){var _oU=B((function(_oV,_oW){var _oX=E(_oV);if(!_oX._){return E(_oW);}else{var _oY=_oX.b,_oZ=E(_oX.a);if(_oZ>=0){var _p0=function(_p1){var _p2=_ow-_oZ|0;if(_p2>=0){var _p3=E(_p2);return (_p3==0)?_oW+_p1:_oW+_p1*B(_ib(E(_oB),_p3));}else{return E(_i2);}},_p4=E(_oZ);if(!_p4){_oS=_oY;_oT=B(_p0(1));return __continue;}else{_oS=_oY;_oT=B(_p0(B(_ib(_oQ,_p4))));return __continue;}}else{return E(_i2);}}})(_oS,_oT));if(_oU!=__continue){return _oU;}}};return new F(function(){return _oR(_oJ,B(_oL(B(_ib(_oQ,_oP)))));});}}else{return E(_i2);}}})(_oD,_oE));if(_oF!=__continue){return _oF;}}},_p5=(2+_ot)*(1+_ot),_p6=function(_p7,_p8){while(1){var _p9=B((function(_pa,_pb){var _pc=E(_pa);if(!_pc._){return E(_pb);}else{var _pd=_pc.a,_pe=new T(function(){return B(A1(_on,new T(function(){return 6.283185307179586*E(_pd)/E(_l9);})));}),_pf=new T(function(){return B(A1(_on,new T(function(){return 6.283185307179586*(E(_pd)+1)/E(_l9);})));}),_pg=function(_ph,_pi){while(1){var _pj=B((function(_pk,_pl){var _pm=E(_pk);if(!_pm._){return E(_pl);}else{var _pn=_pm.b,_po=E(_pm.a);if(_po>=0){var _pp=function(_pq){var _pr=_ow-_po|0;if(_pr>=0){var _ps=E(_pr);return (_ps==0)?_pl+_pq:_pl+_pq*B(_ib(E(_pf),_ps));}else{return E(_i2);}},_pt=E(_po);if(!_pt){_ph=_pn;_pi=B(_pp(1));return __continue;}else{var _pu=E(_pe),_pv=function(_pw,_px){while(1){var _py=B((function(_pz,_pA){var _pB=E(_pz);if(!_pB._){return E(_pA);}else{var _pC=_pB.b,_pD=E(_pB.a);if(_pD>=0){var _pE=function(_pF){var _pG=_ow-_pD|0;if(_pG>=0){var _pH=E(_pG);return (_pH==0)?_pA+_pF:_pA+_pF*B(_ib(E(_pf),_pH));}else{return E(_i2);}},_pI=E(_pD);if(!_pI){_pw=_pC;_px=B(_pE(1));return __continue;}else{_pw=_pC;_px=B(_pE(B(_ib(_pu,_pI))));return __continue;}}else{return E(_i2);}}})(_pw,_px));if(_py!=__continue){return _py;}}};return new F(function(){return _pv(_pn,B(_pp(B(_ib(_pu,_pt)))));});}}else{return E(_i2);}}})(_ph,_pi));if(_pj!=__continue){return _pj;}}},_pJ=_pb+B(_pg(_ox,0))/_p5;_p7=_pc.b;_p8=_pJ;return __continue;}})(_p7,_p8));if(_p9!=__continue){return _p9;}}};return _ou*B(_p6(_oy.b,B(_oC(_ox,0))/_p5));}},_pK=new T(function(){return 1/(B(_os(1))*E(_oo));});return new F(function(){return _nT(_on,_ok,new T2(0,new T3(0,_pK,_pK,_pK),new T(function(){return 1/(B(_os(3))*E(_oo));})),_op,_oq,_or);});},_pL=1.2,_pM=-0.2,_pN=1,_pO=0,_pP=new T3(0,_pM,_pO,_pN),_pQ=new T2(0,_pP,_pO),_pR=0.5,_pS=-0.8,_pT=new T3(0,_pS,_pR,_pO),_pU=new T2(0,_pT,_pO),_pV=0.2,_pW=function(_pX){return E(_pV);},_pY=new T3(0,_pO,_pO,_pN),_pZ=new T(function(){var _q0=B(_om(_pW,_pL,_pU,_pQ,_pY));return {_:0,a:_q0.a,b:_q0.b,c:_q0.c,d:_q0.d,e:_q0.e,f:_q0.f,g:_q0.g,h:_q0.h};}),_q1=0,_q2=1.3,_q3=new T3(0,_q2,_pO,_pO),_q4=new T2(0,_q3,_pO),_q5=function(_q6){var _q7=I_decodeDouble(_q6);return new T2(0,new T1(1,_q7.b),_q7.a);},_q8=function(_q9){return new T1(0,_q9);},_qa=function(_qb){var _qc=hs_intToInt64(2147483647),_qd=hs_leInt64(_qb,_qc);if(!_qd){return new T1(1,I_fromInt64(_qb));}else{var _qe=hs_intToInt64(-2147483648),_qf=hs_geInt64(_qb,_qe);if(!_qf){return new T1(1,I_fromInt64(_qb));}else{var _qg=hs_int64ToInt(_qb);return new F(function(){return _q8(_qg);});}}},_qh=new T(function(){var _qi=newByteArr(256),_qj=_qi,_=_qj["v"]["i8"][0]=8,_qk=function(_ql,_qm,_qn,_){while(1){if(_qn>=256){if(_ql>=256){return E(_);}else{var _qo=imul(2,_ql)|0,_qp=_qm+1|0,_qq=_ql;_ql=_qo;_qm=_qp;_qn=_qq;continue;}}else{var _=_qj["v"]["i8"][_qn]=_qm,_qq=_qn+_ql|0;_qn=_qq;continue;}}},_=B(_qk(2,0,1,_));return _qj;}),_qr=function(_qs,_qt){var _qu=hs_int64ToInt(_qs),_qv=E(_qh),_qw=_qv["v"]["i8"][(255&_qu>>>0)>>>0&4294967295];if(_qt>_qw){if(_qw>=8){var _qx=hs_uncheckedIShiftRA64(_qs,8),_qy=function(_qz,_qA){while(1){var _qB=B((function(_qC,_qD){var _qE=hs_int64ToInt(_qC),_qF=_qv["v"]["i8"][(255&_qE>>>0)>>>0&4294967295];if(_qD>_qF){if(_qF>=8){var _qG=hs_uncheckedIShiftRA64(_qC,8),_qH=_qD-8|0;_qz=_qG;_qA=_qH;return __continue;}else{return new T2(0,new T(function(){var _qI=hs_uncheckedIShiftRA64(_qC,_qF);return B(_qa(_qI));}),_qD-_qF|0);}}else{return new T2(0,new T(function(){var _qJ=hs_uncheckedIShiftRA64(_qC,_qD);return B(_qa(_qJ));}),0);}})(_qz,_qA));if(_qB!=__continue){return _qB;}}};return new F(function(){return _qy(_qx,_qt-8|0);});}else{return new T2(0,new T(function(){var _qK=hs_uncheckedIShiftRA64(_qs,_qw);return B(_qa(_qK));}),_qt-_qw|0);}}else{return new T2(0,new T(function(){var _qL=hs_uncheckedIShiftRA64(_qs,_qt);return B(_qa(_qL));}),0);}},_qM=function(_qN){var _qO=hs_intToInt64(_qN);return E(_qO);},_qP=function(_qQ){var _qR=E(_qQ);if(!_qR._){return new F(function(){return _qM(_qR.a);});}else{return new F(function(){return I_toInt64(_qR.a);});}},_qS=function(_qT){return I_toInt(_qT)>>>0;},_qU=function(_qV){var _qW=E(_qV);if(!_qW._){return _qW.a>>>0;}else{return new F(function(){return _qS(_qW.a);});}},_qX=function(_qY){var _qZ=B(_q5(_qY)),_r0=_qZ.a,_r1=_qZ.b;if(_r1<0){var _r2=function(_r3){if(!_r3){return new T2(0,E(_r0),B(_4I(_30, -_r1)));}else{var _r4=B(_qr(B(_qP(_r0)), -_r1));return new T2(0,E(_r4.a),B(_4I(_30,_r4.b)));}};if(!((B(_qU(_r0))&1)>>>0)){return new F(function(){return _r2(1);});}else{return new F(function(){return _r2(0);});}}else{return new T2(0,B(_4I(_r0,_r1)),_30);}},_r5=function(_r6){var _r7=B(_qX(E(_r6)));return new T2(0,E(_r7.a),E(_r7.b));},_r8=new T3(0,_j5,_mc,_r5),_r9=function(_ra){return E(E(_ra).a);},_rb=function(_rc){return E(E(_rc).a);},_rd=function(_re){return new F(function(){return _od(E(_re),2147483647);});},_rf=function(_rg,_rh,_ri){if(_ri<=_rh){var _rj=new T(function(){var _rk=_rh-_rg|0,_rl=function(_rm){return (_rm>=(_ri-_rk|0))?new T2(1,_rm,new T(function(){return B(_rl(_rm+_rk|0));})):new T2(1,_rm,_T);};return B(_rl(_rh));});return new T2(1,_rg,_rj);}else{return (_ri<=_rg)?new T2(1,_rg,_T):__Z;}},_rn=function(_ro,_rp,_rq){if(_rq>=_rp){var _rr=new T(function(){var _rs=_rp-_ro|0,_rt=function(_ru){return (_ru<=(_rq-_rs|0))?new T2(1,_ru,new T(function(){return B(_rt(_ru+_rs|0));})):new T2(1,_ru,_T);};return B(_rt(_rp));});return new T2(1,_ro,_rr);}else{return (_rq>=_ro)?new T2(1,_ro,_T):__Z;}},_rv=function(_rw,_rx){if(_rx<_rw){return new F(function(){return _rf(_rw,_rx,-2147483648);});}else{return new F(function(){return _rn(_rw,_rx,2147483647);});}},_ry=function(_rz,_rA){return new F(function(){return _rv(E(_rz),E(_rA));});},_rB=function(_rC,_rD,_rE){if(_rD<_rC){return new F(function(){return _rf(_rC,_rD,_rE);});}else{return new F(function(){return _rn(_rC,_rD,_rE);});}},_rF=function(_rG,_rH,_rI){return new F(function(){return _rB(E(_rG),E(_rH),E(_rI));});},_rJ=function(_rK,_rL){return new F(function(){return _od(E(_rK),E(_rL));});},_rM=function(_rN){return E(_rN);},_rO=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_rP=new T(function(){return B(err(_rO));}),_rQ=function(_rR){var _rS=E(_rR);return (_rS==(-2147483648))?E(_rP):_rS-1|0;},_rT=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_rU=new T(function(){return B(err(_rT));}),_rV=function(_rW){var _rX=E(_rW);return (_rX==2147483647)?E(_rU):_rX+1|0;},_rY={_:0,a:_rV,b:_rQ,c:_rM,d:_rM,e:_rd,f:_ry,g:_rJ,h:_rF},_rZ=function(_s0,_s1){if(_s0<=0){if(_s0>=0){return new F(function(){return quot(_s0,_s1);});}else{if(_s1<=0){return new F(function(){return quot(_s0,_s1);});}else{return quot(_s0+1|0,_s1)-1|0;}}}else{if(_s1>=0){if(_s0>=0){return new F(function(){return quot(_s0,_s1);});}else{if(_s1<=0){return new F(function(){return quot(_s0,_s1);});}else{return quot(_s0+1|0,_s1)-1|0;}}}else{return quot(_s0-1|0,_s1)-1|0;}}},_s2=0,_s3=new T(function(){return B(_45(_s2));}),_s4=new T(function(){return die(_s3);}),_s5=function(_s6,_s7){var _s8=E(_s7);switch(_s8){case -1:var _s9=E(_s6);if(_s9==(-2147483648)){return E(_s4);}else{return new F(function(){return _rZ(_s9,-1);});}break;case 0:return E(_49);default:return new F(function(){return _rZ(_s6,_s8);});}},_sa=function(_sb,_sc){return new F(function(){return _s5(E(_sb),E(_sc));});},_sd=0,_se=new T2(0,_s4,_sd),_sf=function(_sg,_sh){var _si=E(_sg),_sj=E(_sh);switch(_sj){case -1:var _sk=E(_si);if(_sk==(-2147483648)){return E(_se);}else{if(_sk<=0){if(_sk>=0){var _sl=quotRemI(_sk,-1);return new T2(0,_sl.a,_sl.b);}else{var _sm=quotRemI(_sk,-1);return new T2(0,_sm.a,_sm.b);}}else{var _sn=quotRemI(_sk-1|0,-1);return new T2(0,_sn.a-1|0,(_sn.b+(-1)|0)+1|0);}}break;case 0:return E(_49);default:if(_si<=0){if(_si>=0){var _so=quotRemI(_si,_sj);return new T2(0,_so.a,_so.b);}else{if(_sj<=0){var _sp=quotRemI(_si,_sj);return new T2(0,_sp.a,_sp.b);}else{var _sq=quotRemI(_si+1|0,_sj);return new T2(0,_sq.a-1|0,(_sq.b+_sj|0)-1|0);}}}else{if(_sj>=0){if(_si>=0){var _sr=quotRemI(_si,_sj);return new T2(0,_sr.a,_sr.b);}else{if(_sj<=0){var _ss=quotRemI(_si,_sj);return new T2(0,_ss.a,_ss.b);}else{var _st=quotRemI(_si+1|0,_sj);return new T2(0,_st.a-1|0,(_st.b+_sj|0)-1|0);}}}else{var _su=quotRemI(_si-1|0,_sj);return new T2(0,_su.a-1|0,(_su.b+_sj|0)+1|0);}}}},_sv=function(_sw,_sx){var _sy=_sw%_sx;if(_sw<=0){if(_sw>=0){return E(_sy);}else{if(_sx<=0){return E(_sy);}else{var _sz=E(_sy);return (_sz==0)?0:_sz+_sx|0;}}}else{if(_sx>=0){if(_sw>=0){return E(_sy);}else{if(_sx<=0){return E(_sy);}else{var _sA=E(_sy);return (_sA==0)?0:_sA+_sx|0;}}}else{var _sB=E(_sy);return (_sB==0)?0:_sB+_sx|0;}}},_sC=function(_sD,_sE){var _sF=E(_sE);switch(_sF){case -1:return E(_sd);case 0:return E(_49);default:return new F(function(){return _sv(E(_sD),_sF);});}},_sG=function(_sH,_sI){var _sJ=E(_sH),_sK=E(_sI);switch(_sK){case -1:var _sL=E(_sJ);if(_sL==(-2147483648)){return E(_s4);}else{return new F(function(){return quot(_sL,-1);});}break;case 0:return E(_49);default:return new F(function(){return quot(_sJ,_sK);});}},_sM=function(_sN,_sO){var _sP=E(_sN),_sQ=E(_sO);switch(_sQ){case -1:var _sR=E(_sP);if(_sR==(-2147483648)){return E(_se);}else{var _sS=quotRemI(_sR,-1);return new T2(0,_sS.a,_sS.b);}break;case 0:return E(_49);default:var _sT=quotRemI(_sP,_sQ);return new T2(0,_sT.a,_sT.b);}},_sU=function(_sV,_sW){var _sX=E(_sW);switch(_sX){case -1:return E(_sd);case 0:return E(_49);default:return E(_sV)%_sX;}},_sY=function(_sZ){return new F(function(){return _q8(E(_sZ));});},_t0=function(_t1){return new T2(0,E(B(_q8(E(_t1)))),E(_me));},_t2=function(_t3,_t4){return imul(E(_t3),E(_t4))|0;},_t5=function(_t6,_t7){return E(_t6)+E(_t7)|0;},_t8=function(_t9,_ta){return E(_t9)-E(_ta)|0;},_tb=function(_tc){var _td=E(_tc);return (_td<0)? -_td:E(_td);},_te=function(_tf){return new F(function(){return _4m(_tf);});},_tg=function(_th){return  -E(_th);},_ti=-1,_tj=0,_tk=1,_tl=function(_tm){var _tn=E(_tm);return (_tn>=0)?(E(_tn)==0)?E(_tj):E(_tk):E(_ti);},_to={_:0,a:_t5,b:_t8,c:_t2,d:_tg,e:_tb,f:_tl,g:_te},_tp=function(_tq,_tr){return E(_tq)==E(_tr);},_ts=function(_tt,_tu){return E(_tt)!=E(_tu);},_tv=new T2(0,_tp,_ts),_tw=function(_tx,_ty){var _tz=E(_tx),_tA=E(_ty);return (_tz>_tA)?E(_tz):E(_tA);},_tB=function(_tC,_tD){var _tE=E(_tC),_tF=E(_tD);return (_tE>_tF)?E(_tF):E(_tE);},_tG=function(_tH,_tI){return (_tH>=_tI)?(_tH!=_tI)?2:1:0;},_tJ=function(_tK,_tL){return new F(function(){return _tG(E(_tK),E(_tL));});},_tM=function(_tN,_tO){return E(_tN)>=E(_tO);},_tP=function(_tQ,_tR){return E(_tQ)>E(_tR);},_tS=function(_tT,_tU){return E(_tT)<=E(_tU);},_tV=function(_tW,_tX){return E(_tW)<E(_tX);},_tY={_:0,a:_tv,b:_tJ,c:_tV,d:_tS,e:_tP,f:_tM,g:_tw,h:_tB},_tZ=new T3(0,_to,_tY,_t0),_u0={_:0,a:_tZ,b:_rY,c:_sG,d:_sU,e:_sa,f:_sC,g:_sM,h:_sf,i:_sY},_u1=new T1(0,2),_u2=function(_u3,_u4){while(1){var _u5=E(_u3);if(!_u5._){var _u6=_u5.a,_u7=E(_u4);if(!_u7._){var _u8=_u7.a;if(!(imul(_u6,_u8)|0)){return new T1(0,imul(_u6,_u8)|0);}else{_u3=new T1(1,I_fromInt(_u6));_u4=new T1(1,I_fromInt(_u8));continue;}}else{_u3=new T1(1,I_fromInt(_u6));_u4=_u7;continue;}}else{var _u9=E(_u4);if(!_u9._){_u3=_u5;_u4=new T1(1,I_fromInt(_u9.a));continue;}else{return new T1(1,I_mul(_u5.a,_u9.a));}}}},_ua=function(_ub,_uc,_ud){while(1){if(!(_uc%2)){var _ue=B(_u2(_ub,_ub)),_uf=quot(_uc,2);_ub=_ue;_uc=_uf;continue;}else{var _ug=E(_uc);if(_ug==1){return new F(function(){return _u2(_ub,_ud);});}else{var _ue=B(_u2(_ub,_ub)),_uh=B(_u2(_ub,_ud));_ub=_ue;_uc=quot(_ug-1|0,2);_ud=_uh;continue;}}}},_ui=function(_uj,_uk){while(1){if(!(_uk%2)){var _ul=B(_u2(_uj,_uj)),_um=quot(_uk,2);_uj=_ul;_uk=_um;continue;}else{var _un=E(_uk);if(_un==1){return E(_uj);}else{return new F(function(){return _ua(B(_u2(_uj,_uj)),quot(_un-1|0,2),_uj);});}}}},_uo=function(_up){return E(E(_up).a);},_uq=function(_ur){return E(E(_ur).b);},_us=function(_ut){return E(E(_ut).c);},_uu=new T1(0,0),_uv=function(_uw){return E(E(_uw).d);},_ux=function(_uy,_uz){var _uA=B(_r9(_uy)),_uB=new T(function(){return B(_rb(_uA));}),_uC=new T(function(){return B(A3(_uv,_uy,_uz,new T(function(){return B(A2(_9I,_uB,_mo));})));});return new F(function(){return A3(_kG,B(_uo(B(_uq(_uA)))),_uC,new T(function(){return B(A2(_9I,_uB,_uu));}));});},_uD=new T(function(){return B(unCStr("Negative exponent"));}),_uE=new T(function(){return B(err(_uD));}),_uF=function(_uG){return E(E(_uG).c);},_uH=function(_uI,_uJ,_uK,_uL){var _uM=B(_r9(_uJ)),_uN=new T(function(){return B(_rb(_uM));}),_uO=B(_uq(_uM));if(!B(A3(_us,_uO,_uL,new T(function(){return B(A2(_9I,_uN,_uu));})))){if(!B(A3(_kG,B(_uo(_uO)),_uL,new T(function(){return B(A2(_9I,_uN,_uu));})))){var _uP=new T(function(){return B(A2(_9I,_uN,_mo));}),_uQ=new T(function(){return B(A2(_9I,_uN,_me));}),_uR=B(_uo(_uO)),_uS=function(_uT,_uU,_uV){while(1){var _uW=B((function(_uX,_uY,_uZ){if(!B(_ux(_uJ,_uY))){if(!B(A3(_kG,_uR,_uY,_uQ))){var _v0=new T(function(){return B(A3(_uF,_uJ,new T(function(){return B(A3(_8A,_uN,_uY,_uQ));}),_uP));});_uT=new T(function(){return B(A3(_8y,_uI,_uX,_uX));});_uU=_v0;_uV=new T(function(){return B(A3(_8y,_uI,_uX,_uZ));});return __continue;}else{return new F(function(){return A3(_8y,_uI,_uX,_uZ);});}}else{var _v1=_uZ;_uT=new T(function(){return B(A3(_8y,_uI,_uX,_uX));});_uU=new T(function(){return B(A3(_uF,_uJ,_uY,_uP));});_uV=_v1;return __continue;}})(_uT,_uU,_uV));if(_uW!=__continue){return _uW;}}},_v2=function(_v3,_v4){while(1){var _v5=B((function(_v6,_v7){if(!B(_ux(_uJ,_v7))){if(!B(A3(_kG,_uR,_v7,_uQ))){var _v8=new T(function(){return B(A3(_uF,_uJ,new T(function(){return B(A3(_8A,_uN,_v7,_uQ));}),_uP));});return new F(function(){return _uS(new T(function(){return B(A3(_8y,_uI,_v6,_v6));}),_v8,_v6);});}else{return E(_v6);}}else{_v3=new T(function(){return B(A3(_8y,_uI,_v6,_v6));});_v4=new T(function(){return B(A3(_uF,_uJ,_v7,_uP));});return __continue;}})(_v3,_v4));if(_v5!=__continue){return _v5;}}};return new F(function(){return _v2(_uK,_uL);});}else{return new F(function(){return A2(_9I,_uI,_me);});}}else{return E(_uE);}},_v9=new T(function(){return B(err(_uD));}),_va=function(_vb,_vc){var _vd=B(_q5(_vc)),_ve=_vd.a,_vf=_vd.b,_vg=new T(function(){return B(_rb(new T(function(){return B(_r9(_vb));})));});if(_vf<0){var _vh= -_vf;if(_vh>=0){var _vi=E(_vh);if(!_vi){var _vj=E(_me);}else{var _vj=B(_ui(_u1,_vi));}if(!B(_4e(_vj,_4H))){var _vk=B(_4y(_ve,_vj));return new T2(0,new T(function(){return B(A2(_9I,_vg,_vk.a));}),new T(function(){return B(_4a(_vk.b,_vf));}));}else{return E(_49);}}else{return E(_v9);}}else{var _vl=new T(function(){var _vm=new T(function(){return B(_uH(_vg,_u0,new T(function(){return B(A2(_9I,_vg,_u1));}),_vf));});return B(A3(_8y,_vg,new T(function(){return B(A2(_9I,_vg,_ve));}),_vm));});return new T2(0,_vl,_7w);}},_vn=function(_vo,_vp){var _vq=B(_va(_vo,E(_vp))),_vr=_vq.a;if(E(_vq.b)<=0){return E(_vr);}else{var _vs=B(_rb(B(_r9(_vo))));return new F(function(){return A3(_7W,_vs,_vr,new T(function(){return B(A2(_9I,_vs,_30));}));});}},_vt=function(_vu,_vv){var _vw=B(_va(_vu,E(_vv))),_vx=_vw.a;if(E(_vw.b)>=0){return E(_vx);}else{var _vy=B(_rb(B(_r9(_vu))));return new F(function(){return A3(_8A,_vy,_vx,new T(function(){return B(A2(_9I,_vy,_30));}));});}},_vz=function(_vA,_vB){var _vC=B(_va(_vA,E(_vB)));return new T2(0,_vC.a,_vC.b);},_vD=function(_vE,_vF){var _vG=B(_va(_vE,_vF)),_vH=_vG.a,_vI=E(_vG.b),_vJ=new T(function(){var _vK=B(_rb(B(_r9(_vE))));if(_vI>=0){return B(A3(_7W,_vK,_vH,new T(function(){return B(A2(_9I,_vK,_30));})));}else{return B(A3(_8A,_vK,_vH,new T(function(){return B(A2(_9I,_vK,_30));})));}}),_vL=function(_vM){var _vN=_vM-0.5;return (_vN>=0)?(E(_vN)==0)?(!B(_ux(_vE,_vH)))?E(_vJ):E(_vH):E(_vJ):E(_vH);},_vO=E(_vI);if(!_vO){return new F(function(){return _vL(0);});}else{if(_vO<=0){var _vP= -_vO-0.5;return (_vP>=0)?(E(_vP)==0)?(!B(_ux(_vE,_vH)))?E(_vJ):E(_vH):E(_vJ):E(_vH);}else{return new F(function(){return _vL(_vO);});}}},_vQ=function(_vR,_vS){return new F(function(){return _vD(_vR,E(_vS));});},_vT=function(_vU,_vV){return E(B(_va(_vU,E(_vV))).a);},_vW={_:0,a:_r8,b:_j9,c:_vz,d:_vT,e:_vQ,f:_vn,g:_vt},_vX=new T1(0,1),_vY=function(_vZ,_w0){var _w1=E(_vZ);return new T2(0,_w1,new T(function(){var _w2=B(_vY(B(_4p(_w1,_w0)),_w0));return new T2(1,_w2.a,_w2.b);}));},_w3=function(_w4){var _w5=B(_vY(_w4,_vX));return new T2(1,_w5.a,_w5.b);},_w6=function(_w7,_w8){var _w9=B(_vY(_w7,new T(function(){return B(_6K(_w8,_w7));})));return new T2(1,_w9.a,_w9.b);},_wa=new T1(0,0),_wb=function(_wc,_wd){var _we=E(_wc);if(!_we._){var _wf=_we.a,_wg=E(_wd);return (_wg._==0)?_wf>=_wg.a:I_compareInt(_wg.a,_wf)<=0;}else{var _wh=_we.a,_wi=E(_wd);return (_wi._==0)?I_compareInt(_wh,_wi.a)>=0:I_compare(_wh,_wi.a)>=0;}},_wj=function(_wk,_wl,_wm){if(!B(_wb(_wl,_wa))){var _wn=function(_wo){return (!B(_51(_wo,_wm)))?new T2(1,_wo,new T(function(){return B(_wn(B(_4p(_wo,_wl))));})):__Z;};return new F(function(){return _wn(_wk);});}else{var _wp=function(_wq){return (!B(_4S(_wq,_wm)))?new T2(1,_wq,new T(function(){return B(_wp(B(_4p(_wq,_wl))));})):__Z;};return new F(function(){return _wp(_wk);});}},_wr=function(_ws,_wt,_wu){return new F(function(){return _wj(_ws,B(_6K(_wt,_ws)),_wu);});},_wv=function(_ww,_wx){return new F(function(){return _wj(_ww,_vX,_wx);});},_wy=function(_wz){return new F(function(){return _4m(_wz);});},_wA=function(_wB){return new F(function(){return _6K(_wB,_vX);});},_wC=function(_wD){return new F(function(){return _4p(_wD,_vX);});},_wE=function(_wF){return new F(function(){return _q8(E(_wF));});},_wG={_:0,a:_wC,b:_wA,c:_wE,d:_wy,e:_w3,f:_w6,g:_wv,h:_wr},_wH=function(_wI,_wJ){while(1){var _wK=E(_wI);if(!_wK._){var _wL=E(_wK.a);if(_wL==(-2147483648)){_wI=new T1(1,I_fromInt(-2147483648));continue;}else{var _wM=E(_wJ);if(!_wM._){return new T1(0,B(_rZ(_wL,_wM.a)));}else{_wI=new T1(1,I_fromInt(_wL));_wJ=_wM;continue;}}}else{var _wN=_wK.a,_wO=E(_wJ);return (_wO._==0)?new T1(1,I_div(_wN,I_fromInt(_wO.a))):new T1(1,I_div(_wN,_wO.a));}}},_wP=function(_wQ,_wR){if(!B(_4e(_wR,_uu))){return new F(function(){return _wH(_wQ,_wR);});}else{return E(_49);}},_wS=function(_wT,_wU){while(1){var _wV=E(_wT);if(!_wV._){var _wW=E(_wV.a);if(_wW==(-2147483648)){_wT=new T1(1,I_fromInt(-2147483648));continue;}else{var _wX=E(_wU);if(!_wX._){var _wY=_wX.a;return new T2(0,new T1(0,B(_rZ(_wW,_wY))),new T1(0,B(_sv(_wW,_wY))));}else{_wT=new T1(1,I_fromInt(_wW));_wU=_wX;continue;}}}else{var _wZ=E(_wU);if(!_wZ._){_wT=_wV;_wU=new T1(1,I_fromInt(_wZ.a));continue;}else{var _x0=I_divMod(_wV.a,_wZ.a);return new T2(0,new T1(1,_x0.a),new T1(1,_x0.b));}}}},_x1=function(_x2,_x3){if(!B(_4e(_x3,_uu))){var _x4=B(_wS(_x2,_x3));return new T2(0,_x4.a,_x4.b);}else{return E(_49);}},_x5=function(_x6,_x7){while(1){var _x8=E(_x6);if(!_x8._){var _x9=E(_x8.a);if(_x9==(-2147483648)){_x6=new T1(1,I_fromInt(-2147483648));continue;}else{var _xa=E(_x7);if(!_xa._){return new T1(0,B(_sv(_x9,_xa.a)));}else{_x6=new T1(1,I_fromInt(_x9));_x7=_xa;continue;}}}else{var _xb=_x8.a,_xc=E(_x7);return (_xc._==0)?new T1(1,I_mod(_xb,I_fromInt(_xc.a))):new T1(1,I_mod(_xb,_xc.a));}}},_xd=function(_xe,_xf){if(!B(_4e(_xf,_uu))){return new F(function(){return _x5(_xe,_xf);});}else{return E(_49);}},_xg=function(_xh,_xi){while(1){var _xj=E(_xh);if(!_xj._){var _xk=E(_xj.a);if(_xk==(-2147483648)){_xh=new T1(1,I_fromInt(-2147483648));continue;}else{var _xl=E(_xi);if(!_xl._){return new T1(0,quot(_xk,_xl.a));}else{_xh=new T1(1,I_fromInt(_xk));_xi=_xl;continue;}}}else{var _xm=_xj.a,_xn=E(_xi);return (_xn._==0)?new T1(0,I_toInt(I_quot(_xm,I_fromInt(_xn.a)))):new T1(1,I_quot(_xm,_xn.a));}}},_xo=function(_xp,_xq){if(!B(_4e(_xq,_uu))){return new F(function(){return _xg(_xp,_xq);});}else{return E(_49);}},_xr=function(_xs,_xt){if(!B(_4e(_xt,_uu))){var _xu=B(_4y(_xs,_xt));return new T2(0,_xu.a,_xu.b);}else{return E(_49);}},_xv=function(_xw,_xx){while(1){var _xy=E(_xw);if(!_xy._){var _xz=E(_xy.a);if(_xz==(-2147483648)){_xw=new T1(1,I_fromInt(-2147483648));continue;}else{var _xA=E(_xx);if(!_xA._){return new T1(0,_xz%_xA.a);}else{_xw=new T1(1,I_fromInt(_xz));_xx=_xA;continue;}}}else{var _xB=_xy.a,_xC=E(_xx);return (_xC._==0)?new T1(1,I_rem(_xB,I_fromInt(_xC.a))):new T1(1,I_rem(_xB,_xC.a));}}},_xD=function(_xE,_xF){if(!B(_4e(_xF,_uu))){return new F(function(){return _xv(_xE,_xF);});}else{return E(_49);}},_xG=function(_xH){return E(_xH);},_xI=function(_xJ){return E(_xJ);},_xK=function(_xL){var _xM=E(_xL);if(!_xM._){var _xN=E(_xM.a);return (_xN==(-2147483648))?E(_7o):(_xN<0)?new T1(0, -_xN):E(_xM);}else{var _xO=_xM.a;return (I_compareInt(_xO,0)>=0)?E(_xM):new T1(1,I_negate(_xO));}},_xP=new T1(0,0),_xQ=new T1(0,-1),_xR=function(_xS){var _xT=E(_xS);if(!_xT._){var _xU=_xT.a;return (_xU>=0)?(E(_xU)==0)?E(_xP):E(_50):E(_xQ);}else{var _xV=I_compareInt(_xT.a,0);return (_xV<=0)?(E(_xV)==0)?E(_xP):E(_xQ):E(_50);}},_xW={_:0,a:_4p,b:_6K,c:_u2,d:_7p,e:_xK,f:_xR,g:_xI},_xX=function(_xY,_xZ){var _y0=E(_xY);if(!_y0._){var _y1=_y0.a,_y2=E(_xZ);return (_y2._==0)?_y1!=_y2.a:(I_compareInt(_y2.a,_y1)==0)?false:true;}else{var _y3=_y0.a,_y4=E(_xZ);return (_y4._==0)?(I_compareInt(_y3,_y4.a)==0)?false:true:(I_compare(_y3,_y4.a)==0)?false:true;}},_y5=new T2(0,_4e,_xX),_y6=function(_y7,_y8){return (!B(_6v(_y7,_y8)))?E(_y7):E(_y8);},_y9=function(_ya,_yb){return (!B(_6v(_ya,_yb)))?E(_yb):E(_ya);},_yc={_:0,a:_y5,b:_31,c:_51,d:_6v,e:_4S,f:_wb,g:_y6,h:_y9},_yd=function(_ye){return new T2(0,E(_ye),E(_me));},_yf=new T3(0,_xW,_yc,_yd),_yg={_:0,a:_yf,b:_wG,c:_xo,d:_xD,e:_wP,f:_xd,g:_xr,h:_x1,i:_xG},_yh=function(_yi){return E(E(_yi).b);},_yj=function(_yk){return E(E(_yk).g);},_yl=new T1(0,1),_ym=function(_yn,_yo,_yp){var _yq=B(_yh(_yn)),_yr=B(_8w(_yq)),_ys=new T(function(){var _yt=new T(function(){var _yu=new T(function(){var _yv=new T(function(){return B(A3(_yj,_yn,_yg,new T(function(){return B(A3(_9T,_yq,_yo,_yp));})));});return B(A2(_9I,_yr,_yv));}),_yw=new T(function(){return B(A2(_7Y,_yr,new T(function(){return B(A2(_9I,_yr,_yl));})));});return B(A3(_8y,_yr,_yw,_yu));});return B(A3(_8y,_yr,_yt,_yp));});return new F(function(){return A3(_7W,_yr,_yo,_ys);});},_yx=1.5707963267948966,_yy=function(_yz){return 0.2/Math.cos(B(_ym(_vW,_yz,_yx))-0.7853981633974483);},_yA=0.3,_yB=-0.1,_yC=new T3(0,_pO,_yB,_yA),_yD=new T2(0,_yC,_pO),_yE=new T(function(){var _yF=B(_om(_yy,_pL,_q4,_yD,_pY));return {_:0,a:_yF.a,b:_yF.b,c:_yF.c,d:_yF.d,e:_yF.e,f:_yF.f,g:_yF.g,h:_yF.h};}),_yG=new T2(1,_yE,_T),_yH=new T2(1,_pZ,_yG),_yI=new T(function(){return B(unCStr("Negative range size"));}),_yJ=new T(function(){return B(err(_yI));}),_yK=function(_){var _yL=B(_hU(_yH,0))-1|0,_yM=function(_yN){if(_yN>=0){var _yO=newArr(_yN,_i0),_yP=_yO,_yQ=E(_yN);if(!_yQ){return new T4(0,E(_q1),E(_yL),0,_yP);}else{var _yR=function(_yS,_yT,_){while(1){var _yU=E(_yS);if(!_yU._){return E(_);}else{var _=_yP[_yT]=_yU.a;if(_yT!=(_yQ-1|0)){var _yV=_yT+1|0;_yS=_yU.b;_yT=_yV;continue;}else{return E(_);}}}},_=B((function(_yW,_yX,_yY,_){var _=_yP[_yY]=_yW;if(_yY!=(_yQ-1|0)){return new F(function(){return _yR(_yX,_yY+1|0,_);});}else{return E(_);}})(_pZ,_yG,0,_));return new T4(0,E(_q1),E(_yL),_yQ,_yP);}}else{return E(_yJ);}};if(0>_yL){return new F(function(){return _yM(0);});}else{return new F(function(){return _yM(_yL+1|0);});}},_yZ=function(_z0){var _z1=B(A1(_z0,_));return E(_z1);},_z2=new T(function(){return B(_yZ(_yK));}),_z3=function(_z4,_z5,_){var _z6=B(A1(_z4,_)),_z7=B(A1(_z5,_));return _z6;},_z8=function(_z9,_za,_){var _zb=B(A1(_z9,_)),_zc=B(A1(_za,_));return new T(function(){return B(A1(_zb,_zc));});},_zd=function(_ze,_zf,_){var _zg=B(A1(_zf,_));return _ze;},_zh=function(_zi,_zj,_){var _zk=B(A1(_zj,_));return new T(function(){return B(A1(_zi,_zk));});},_zl=new T2(0,_zh,_zd),_zm=function(_zn,_){return _zn;},_zo=function(_zp,_zq,_){var _zr=B(A1(_zp,_));return new F(function(){return A1(_zq,_);});},_zs=new T5(0,_zl,_zm,_z8,_zo,_z3),_zt=function(_zu){return E(_zu);},_zv=function(_zw){return E(_zw);},_zx=function(_zy,_zz){return E(_zz);},_zA=function(_zB,_zC){return E(_zB);},_zD=function(_zE){return E(_zE);},_zF=new T2(0,_zD,_zA),_zG=function(_zH,_zI){return E(_zH);},_zJ=new T5(0,_zF,_zv,_zt,_zx,_zG),_zK=function(_zL){var _zM=E(_zL);return (E(_zM.b)-E(_zM.a)|0)+1|0;},_zN=function(_zO,_zP){var _zQ=E(_zO),_zR=E(_zP);return (E(_zQ.a)>_zR)?false:_zR<=E(_zQ.b);},_zS=function(_zT,_zU){var _zV=jsShowI(_zT);return new F(function(){return _14(fromJSStr(_zV),_zU);});},_zW=function(_zX,_zY,_zZ){if(_zY>=0){return new F(function(){return _zS(_zY,_zZ);});}else{if(_zX<=6){return new F(function(){return _zS(_zY,_zZ);});}else{return new T2(1,_8f,new T(function(){var _A0=jsShowI(_zY);return B(_14(fromJSStr(_A0),new T2(1,_8e,_zZ)));}));}}},_A1=function(_A2){return new F(function(){return _zW(0,E(_A2),_T);});},_A3=function(_A4,_A5,_A6){return new F(function(){return _zW(E(_A4),E(_A5),_A6);});},_A7=function(_A8,_A9){return new F(function(){return _zW(0,E(_A8),_A9);});},_Aa=function(_Ab,_Ac){return new F(function(){return _3P(_A7,_Ab,_Ac);});},_Ad=new T3(0,_A3,_A1,_Aa),_Ae=0,_Af=function(_Ag,_Ah,_Ai){return new F(function(){return A1(_Ag,new T2(1,_3M,new T(function(){return B(A1(_Ah,_Ai));})));});},_Aj=new T(function(){return B(unCStr("foldr1"));}),_Ak=new T(function(){return B(_lc(_Aj));}),_Al=function(_Am,_An){var _Ao=E(_An);if(!_Ao._){return E(_Ak);}else{var _Ap=_Ao.a,_Aq=E(_Ao.b);if(!_Aq._){return E(_Ap);}else{return new F(function(){return A2(_Am,_Ap,new T(function(){return B(_Al(_Am,_Aq));}));});}}},_Ar=new T(function(){return B(unCStr(" out of range "));}),_As=new T(function(){return B(unCStr("}.index: Index "));}),_At=new T(function(){return B(unCStr("Ix{"));}),_Au=new T2(1,_8e,_T),_Av=new T2(1,_8e,_Au),_Aw=0,_Ax=function(_Ay){return E(E(_Ay).a);},_Az=function(_AA,_AB,_AC,_AD,_AE){var _AF=new T(function(){var _AG=new T(function(){var _AH=new T(function(){var _AI=new T(function(){var _AJ=new T(function(){return B(A3(_Al,_Af,new T2(1,new T(function(){return B(A3(_Ax,_AC,_Aw,_AD));}),new T2(1,new T(function(){return B(A3(_Ax,_AC,_Aw,_AE));}),_T)),_Av));});return B(_14(_Ar,new T2(1,_8f,new T2(1,_8f,_AJ))));});return B(A(_Ax,[_AC,_Ae,_AB,new T2(1,_8e,_AI)]));});return B(_14(_As,new T2(1,_8f,_AH)));},1);return B(_14(_AA,_AG));},1);return new F(function(){return err(B(_14(_At,_AF)));});},_AK=function(_AL,_AM,_AN,_AO,_AP){return new F(function(){return _Az(_AL,_AM,_AP,_AN,_AO);});},_AQ=function(_AR,_AS,_AT,_AU){var _AV=E(_AT);return new F(function(){return _AK(_AR,_AS,_AV.a,_AV.b,_AU);});},_AW=function(_AX,_AY,_AZ,_B0){return new F(function(){return _AQ(_B0,_AZ,_AY,_AX);});},_B1=new T(function(){return B(unCStr("Int"));}),_B2=function(_B3,_B4){return new F(function(){return _AW(_Ad,_B4,_B3,_B1);});},_B5=function(_B6,_B7){var _B8=E(_B6),_B9=E(_B8.a),_Ba=E(_B7);if(_B9>_Ba){return new F(function(){return _B2(_Ba,_B8);});}else{if(_Ba>E(_B8.b)){return new F(function(){return _B2(_Ba,_B8);});}else{return _Ba-_B9|0;}}},_Bb=function(_Bc){var _Bd=E(_Bc);return new F(function(){return _rJ(_Bd.a,_Bd.b);});},_Be=function(_Bf){var _Bg=E(_Bf),_Bh=E(_Bg.a),_Bi=E(_Bg.b);return (_Bh>_Bi)?E(_Ae):(_Bi-_Bh|0)+1|0;},_Bj=function(_Bk,_Bl){return new F(function(){return _t8(_Bl,E(_Bk).a);});},_Bm={_:0,a:_tY,b:_Bb,c:_B5,d:_Bj,e:_zN,f:_Be,g:_zK},_Bn=function(_Bo,_Bp){return new T2(1,_Bo,_Bp);},_Bq=function(_Br,_Bs){var _Bt=E(_Bs);return new T2(0,_Bt.a,_Bt.b);},_Bu=function(_Bv){return E(E(_Bv).f);},_Bw=function(_Bx,_By,_Bz){var _BA=E(_By),_BB=_BA.a,_BC=_BA.b,_BD=function(_){var _BE=B(A2(_Bu,_Bx,_BA));if(_BE>=0){var _BF=newArr(_BE,_i0),_BG=_BF,_BH=E(_BE);if(!_BH){return new T(function(){return new T4(0,E(_BB),E(_BC),0,_BG);});}else{var _BI=function(_BJ,_BK,_){while(1){var _BL=E(_BJ);if(!_BL._){return E(_);}else{var _=_BG[_BK]=_BL.a;if(_BK!=(_BH-1|0)){var _BM=_BK+1|0;_BJ=_BL.b;_BK=_BM;continue;}else{return E(_);}}}},_=B(_BI(_Bz,0,_));return new T(function(){return new T4(0,E(_BB),E(_BC),_BH,_BG);});}}else{return E(_yJ);}};return new F(function(){return _yZ(_BD);});},_BN=function(_BO,_BP,_BQ,_BR){var _BS=new T(function(){var _BT=E(_BR),_BU=_BT.c-1|0,_BV=new T(function(){return B(A2(_dE,_BP,_T));});if(0<=_BU){var _BW=new T(function(){return B(_9P(_BP));}),_BX=function(_BY){var _BZ=new T(function(){var _C0=new T(function(){return B(A1(_BQ,new T(function(){return E(_BT.d[_BY]);})));});return B(A3(_9X,_BW,_Bn,_C0));});return new F(function(){return A3(_9V,_BP,_BZ,new T(function(){if(_BY!=_BU){return B(_BX(_BY+1|0));}else{return E(_BV);}}));});};return B(_BX(0));}else{return E(_BV);}}),_C1=new T(function(){return B(_Bq(_BO,_BR));});return new F(function(){return A3(_9X,B(_9P(_BP)),function(_C2){return new F(function(){return _Bw(_BO,_C1,_C2);});},_BS);});},_C3=function(_){return _S;},_C4=new T(function(){return eval("vertex");}),_C5=function(_C6,_C7,_C8,_C9,_Ca,_Cb,_){var _Cc=__apply(E(_C4),new T2(1,_Cb,new T2(1,_Ca,new T2(1,_C9,new T2(1,_C8,new T2(1,_C7,new T2(1,_C6,_T)))))));return new F(function(){return _C3(_);});},_Cd=function(_Ce,_){while(1){var _Cf=E(_Ce);if(!_Cf._){return _S;}else{var _Cg=E(_Cf.a),_Ch=E(_Cg.a),_Ci=E(_Ch.a),_Cj=E(_Ch.b),_Ck=B(_C5(E(_Ci.a),E(_Ci.b),E(_Ci.c),E(_Cj.a),E(_Cj.b),E(_Ch.c),_)),_Cl=E(_Cg.b),_Cm=E(_Cl.a),_Cn=E(_Cl.b),_Co=B(_C5(E(_Cm.a),E(_Cm.b),E(_Cm.c),E(_Cn.a),E(_Cn.b),E(_Cl.c),_)),_Cp=E(_Cg.c),_Cq=E(_Cp.a),_Cr=E(_Cp.b),_Cs=B(_C5(E(_Cq.a),E(_Cq.b),E(_Cq.c),E(_Cr.a),E(_Cr.b),E(_Cp.c),_));_Ce=_Cf.b;continue;}}},_Ct=new T(function(){return eval("drawTriangles");}),_Cu=function(_){var _Cv=__app0(E(_Ct));return new F(function(){return _C3(_);});},_Cw=function(_Cx,_){var _Cy=B(_Cd(_Cx,_));return new F(function(){return _Cu(_);});},_Cz=function(_CA,_){return new F(function(){return _Cw(E(_CA).h,_);});},_CB=new T(function(){return eval("draw");}),_CC=function(_CD){var _CE=E(_CD),_CF=_CE.b,_CG=_CE.g,_CH=new T(function(){var _CI=E(_CE.e),_CJ=new T(function(){var _CK=E(_CI.a),_CL=E(_CF),_CM=E(_CG),_CN=B(_kn(_jB,_CL.a,_CL.b,_CL.c,_CM.a,_CM.b,_CM.c));return new T3(0,new T(function(){return E(_CK.a)+E(_CN.a)*5.0e-2;}),new T(function(){return E(_CK.b)+E(_CN.b)*5.0e-2;}),new T(function(){return E(_CK.c)+E(_CN.c)*5.0e-2;}));});return new T2(0,_CJ,_CI.b);});return {_:0,a:_CE.a,b:_CF,c:_CE.c,d:_CE.d,e:_CH,f:_CE.f,g:_CG,h:_CE.h};},_CO=function(_CP,_CQ,_CR,_CS,_CT,_CU){var _CV=new T(function(){var _CW=E(_CS),_CX=E(_CT),_CY=new T(function(){var _CZ=E(_CW.a),_D0=E(_CX.a);return new T3(0,new T(function(){return E(_CZ.a)+E(_D0.a)*5.0e-2;}),new T(function(){return E(_CZ.b)+E(_D0.b)*5.0e-2;}),new T(function(){return E(_CZ.c)+E(_D0.c)*5.0e-2;}));});return new T2(0,_CY,new T(function(){return E(_CW.b)+E(_CX.b)*5.0e-2;}));});return new F(function(){return _nT(_CP,_CQ,_CR,_CV,_CT,_CU);});},_D1=function(_D2){var _D3=E(_D2),_D4=B(_CO(_D3.a,_D3.b,_D3.c,_D3.d,_D3.e,_D3.f));return {_:0,a:_D4.a,b:_D4.b,c:_D4.c,d:_D4.d,e:_D4.e,f:_D4.f,g:_D4.g,h:_D4.h};},_D5=new T(function(){return eval("refresh");}),_D6=function(_D7,_){var _D8=__app0(E(_D5)),_D9=__app0(E(_CB)),_Da=B(A(_BN,[_Bm,_zs,_Cz,_D7,_]));return new T(function(){return B(_BN(_Bm,_zJ,_D1,new T(function(){return B(_BN(_Bm,_zJ,_CC,_D7));})));});},_Db=function(_Dc,_Dd,_De){var _Df=function(_){var _Dg=B(_D6(_Dc,_));return new T(function(){return B(A1(_De,new T1(1,_Dg)));});};return new T1(0,_Df);},_Dh=new T0(2),_Di=function(_Dj,_Dk,_Dl){return function(_){var _Dm=E(_Dj),_Dn=rMV(_Dm),_Do=E(_Dn);if(!_Do._){var _Dp=new T(function(){var _Dq=new T(function(){return B(A1(_Dl,_S));});return B(_14(_Do.b,new T2(1,new T2(0,_Dk,function(_Dr){return E(_Dq);}),_T)));}),_=wMV(_Dm,new T2(0,_Do.a,_Dp));return _Dh;}else{var _Ds=E(_Do.a);if(!_Ds._){var _=wMV(_Dm,new T2(0,_Dk,_T));return new T(function(){return B(A1(_Dl,_S));});}else{var _=wMV(_Dm,new T1(1,_Ds.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Dl,_S));}),new T2(1,new T(function(){return B(A2(_Ds.a,_Dk,_U));}),_T)));}}};},_Dt=function(_Du){return E(E(_Du).b);},_Dv=function(_Dw,_Dx,_Dy){var _Dz=new T(function(){return new T1(0,B(_Di(_Dx,_Dy,_U)));}),_DA=function(_DB){return new T1(1,new T2(1,new T(function(){return B(A1(_DB,_S));}),new T2(1,_Dz,_T)));};return new F(function(){return A2(_Dt,_Dw,_DA);});},_DC=function(_){return new F(function(){return __jsNull();});},_DD=function(_DE){var _DF=B(A1(_DE,_));return E(_DF);},_DG=new T(function(){return B(_DD(_DC));}),_DH=new T(function(){return E(_DG);}),_DI=new T(function(){return eval("window.requestAnimationFrame");}),_DJ=new T1(1,_T),_DK=function(_DL,_DM){return function(_){var _DN=E(_DL),_DO=rMV(_DN),_DP=E(_DO);if(!_DP._){var _DQ=_DP.a,_DR=E(_DP.b);if(!_DR._){var _=wMV(_DN,_DJ);return new T(function(){return B(A1(_DM,_DQ));});}else{var _DS=E(_DR.a),_=wMV(_DN,new T2(0,_DS.a,_DR.b));return new T1(1,new T2(1,new T(function(){return B(A1(_DM,_DQ));}),new T2(1,new T(function(){return B(A1(_DS.b,_U));}),_T)));}}else{var _DT=new T(function(){var _DU=function(_DV){var _DW=new T(function(){return B(A1(_DM,_DV));});return function(_DX){return E(_DW);};};return B(_14(_DP.a,new T2(1,_DU,_T)));}),_=wMV(_DN,new T1(1,_DT));return _Dh;}};},_DY=function(_DZ,_E0){return new T1(0,B(_DK(_DZ,_E0)));},_E1=function(_E2,_E3){var _E4=new T(function(){return new T1(0,B(_Di(_E2,_S,_U)));});return function(_){var _E5=__createJSFunc(2,function(_E6,_){var _E7=B(_1e(_E4,_T,_));return _DH;}),_E8=__app1(E(_DI),_E5);return new T(function(){return B(_DY(_E2,_E3));});};},_E9=new T1(1,_T),_Ea=function(_Eb){var _Ec=new T(function(){return B(_Ed(_));}),_Ee=new T(function(){var _Ef=function(_Eg){return E(_Ec);},_Eh=function(_){var _Ei=nMV(_E9);return new T(function(){return new T1(0,B(_E1(_Ei,_Ef)));});};return B(A(_Dv,[_13,_Eb,_S,function(_Ej){return E(new T1(0,_Eh));}]));}),_Ed=function(_Ek){return E(_Ee);};return new F(function(){return _Ed(_);});},_El=function(_Em){return E(E(_Em).a);},_En=function(_Eo){return E(E(_Eo).d);},_Ep=function(_Eq){return E(E(_Eq).c);},_Er=function(_Es){return E(E(_Es).c);},_Et=new T1(1,_T),_Eu=function(_Ev){var _Ew=function(_){var _Ex=nMV(_Et);return new T(function(){return B(A1(_Ev,_Ex));});};return new T1(0,_Ew);},_Ey=function(_Ez,_EA){var _EB=new T(function(){return B(_Er(_Ez));}),_EC=B(_El(_Ez)),_ED=function(_EE){var _EF=new T(function(){return B(A1(_EB,new T(function(){return B(A1(_EA,_EE));})));});return new F(function(){return A3(_Ep,_EC,_EF,new T(function(){return B(A2(_En,_EC,_EE));}));});};return new F(function(){return A3(_J,_EC,new T(function(){return B(A2(_Dt,_Ez,_Eu));}),_ED);});},_EG=function(_EH,_EI,_EJ){var _EK=new T(function(){return B(_El(_EH));}),_EL=new T(function(){return B(A2(_En,_EK,_S));}),_EM=function(_EN,_EO){var _EP=new T(function(){var _EQ=new T(function(){return B(A2(_Dt,_EH,function(_ER){return new F(function(){return _DY(_EO,_ER);});}));});return B(A3(_J,_EK,_EQ,new T(function(){return B(A1(_EJ,_EN));})));});return new F(function(){return A3(_J,_EK,_EP,function(_ES){var _ET=E(_ES);if(!_ET._){return E(_EL);}else{return new F(function(){return _EM(_ET.a,_EO);});}});});};return new F(function(){return _Ey(_EH,function(_ER){return new F(function(){return _EM(_EI,_ER);});});});},_EU=function(_){var _EV=__app2(E(_1j),E(_96),E(_hT));return new F(function(){return _1e(new T(function(){return B(A(_EG,[_13,_z2,_Db,_Ea]));}),_T,_);});},_EW=function(_){return new F(function(){return _EU(_);});};
var hasteMain = function() {B(A(_EW, [0]));};window.onload = hasteMain;