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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x,_8y,_8z,_8A,_8B,_8C,_8D){var _8E=B(_8s(B(_8q(_8x)))),_8F=new T(function(){return B(A3(_86,_8E,new T(function(){return B(A3(_8u,_8E,_8y,_8B));}),new T(function(){return B(A3(_8u,_8E,_8z,_8C));})));});return new F(function(){return A3(_86,_8E,_8F,new T(function(){return B(A3(_8u,_8E,_8A,_8D));}));});},_8G=function(_8H){return E(E(_8H).b);},_8I=function(_8J){return E(E(_8J).g);},_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O){var _8P=B(_8s(B(_8q(_8N)))),_8Q=new T(function(){return B(A2(_8K,_8N,new T(function(){var _8R=E(_8O),_8S=_8R.a,_8T=_8R.b,_8U=_8R.c;return B(_8w(_8N,_8S,_8T,_8U,_8S,_8T,_8U));})));});return new F(function(){return A3(_8G,_8P,_8Q,new T(function(){return B(A2(_8I,_8P,_1o));}));});},_8V=new T(function(){return B(unCStr("x"));}),_8W=new T1(0,_8V),_8X=new T(function(){return B(unCStr("y"));}),_8Y=new T1(0,_8X),_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T3(0,E(_8W),E(_8Y),E(_90)),_92=new T(function(){return B(_8M(_8p,_91));}),_93=new T(function(){return toJSStr(B(_1v(_x,_1l,_92)));}),_94=new T(function(){return B(unCStr("(/=) is not defined"));}),_95=new T(function(){return B(err(_94));}),_96=new T(function(){return B(unCStr("(==) is not defined"));}),_97=new T(function(){return B(err(_96));}),_98=new T2(0,_97,_95),_99=new T(function(){return B(unCStr("(<) is not defined"));}),_9a=new T(function(){return B(err(_99));}),_9b=new T(function(){return B(unCStr("(<=) is not defined"));}),_9c=new T(function(){return B(err(_9b));}),_9d=new T(function(){return B(unCStr("(>) is not defined"));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("(>=) is not defined"));}),_9g=new T(function(){return B(err(_9f));}),_9h=new T(function(){return B(unCStr("compare is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("max("));}),_9k=new T1(0,_9j),_9l=function(_9m,_9n){return new T1(1,new T2(1,_9k,new T2(1,_9m,new T2(1,_22,new T2(1,_9n,_1S)))));},_9o=new T(function(){return B(unCStr("min("));}),_9p=new T1(0,_9o),_9q=function(_9r,_9s){return new T1(1,new T2(1,_9p,new T2(1,_9r,new T2(1,_22,new T2(1,_9s,_1S)))));},_9t={_:0,a:_98,b:_9i,c:_9a,d:_9c,e:_9e,f:_9g,g:_9l,h:_9q},_9u=new T2(0,_8p,_9t),_9v=function(_9w,_9x){var _9y=E(_9w);return E(_9x);},_9z=function(_9A,_9B){var _9C=E(_9B);return E(_9A);},_9D=function(_9E,_9F){var _9G=E(_9E),_9H=E(_9F);return new T3(0,E(B(A1(_9G.a,_9H.a))),E(B(A1(_9G.b,_9H.b))),E(B(A1(_9G.c,_9H.c))));},_9I=function(_9J,_9K,_9L){return new T3(0,E(_9J),E(_9K),E(_9L));},_9M=function(_9N){return new F(function(){return _9I(_9N,_9N,_9N);});},_9O=function(_9P,_9Q){var _9R=E(_9Q),_9S=E(_9P);return new T3(0,E(_9S),E(_9S),E(_9S));},_9T=function(_9U,_9V){var _9W=E(_9V);return new T3(0,E(B(A1(_9U,_9W.a))),E(B(A1(_9U,_9W.b))),E(B(A1(_9U,_9W.c))));},_9X=new T2(0,_9T,_9O),_9Y=new T5(0,_9X,_9M,_9D,_9v,_9z),_9Z=new T1(0,0),_a0=function(_a1){var _a2=B(A2(_8I,_a1,_1o)),_a3=B(A2(_8I,_a1,_9Z));return new T3(0,E(new T3(0,E(_a2),E(_a3),E(_a3))),E(new T3(0,E(_a3),E(_a2),E(_a3))),E(new T3(0,E(_a3),E(_a3),E(_a2))));},_a4=function(_a5){return E(E(_a5).a);},_a6=function(_a7){return E(E(_a7).f);},_a8=function(_a9){return E(E(_a9).b);},_aa=function(_ab){return E(E(_ab).c);},_ac=function(_ad){return E(E(_ad).a);},_ae=function(_af){return E(E(_af).d);},_ag=function(_ah,_ai,_aj,_ak,_al){var _am=new T(function(){return E(E(E(_ah).c).a);}),_an=new T(function(){var _ao=E(_ah).a,_ap=new T(function(){var _aq=new T(function(){return B(_8q(_am));}),_ar=new T(function(){return B(_8s(_aq));}),_as=new T(function(){return B(A2(_ae,_am,_ai));}),_at=new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_au=function(_av,_aw){var _ax=new T(function(){var _ay=new T(function(){return B(A3(_a8,_aq,new T(function(){return B(A3(_8u,_ar,_ak,_av));}),_ai));});return B(A3(_86,_ar,_ay,new T(function(){return B(A3(_8u,_ar,_aw,_as));})));});return new F(function(){return A3(_8u,_ar,_at,_ax);});};return B(A3(_ac,B(_a4(_ao)),_au,_aj));});return B(A3(_aa,_ao,_ap,_al));});return new T2(0,new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_an);},_az=function(_aA,_aB,_aC,_aD){var _aE=E(_aC),_aF=E(_aD),_aG=B(_ag(_aB,_aE.a,_aE.b,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=new T1(0,1),_aI=function(_aJ){return E(E(_aJ).l);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8q(_aO));}),_aR=new T(function(){var _aS=B(_8s(_aQ)),_aT=new T(function(){var _aU=new T(function(){return B(A3(_8G,_aS,new T(function(){return B(A2(_8I,_aS,_aH));}),new T(function(){return B(A3(_8u,_aS,_aM,_aM));})));});return B(A2(_8K,_aO,_aU));});return B(A2(_88,_aS,_aT));});return B(A3(_ac,B(_a4(E(_aL).a)),function(_aV){return new F(function(){return A3(_a8,_aQ,_aV,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aW=function(_aX,_aY,_aZ){var _b0=E(_aZ),_b1=B(_aK(_aY,_b0.a,_b0.b));return new T2(0,_b1.a,_b1.b);},_b2=function(_b3){return E(E(_b3).r);},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return E(E(E(_b5).c).a);}),_b9=new T(function(){var _ba=new T(function(){return B(_8q(_b8));}),_bb=new T(function(){var _bc=new T(function(){var _bd=B(_8s(_ba));return B(A3(_8G,_bd,new T(function(){return B(A3(_8u,_bd,_b6,_b6));}),new T(function(){return B(A2(_8I,_bd,_aH));})));});return B(A2(_8K,_b8,_bc));});return B(A3(_ac,B(_a4(E(_b5).a)),function(_be){return new F(function(){return A3(_a8,_ba,_be,_bb);});},_b7));});return new T2(0,new T(function(){return B(A2(_b2,_b8,_b6));}),_b9);},_bf=function(_bg,_bh,_bi){var _bj=E(_bi),_bk=B(_b4(_bh,_bj.a,_bj.b));return new T2(0,_bk.a,_bk.b);},_bl=function(_bm){return E(E(_bm).k);},_bn=function(_bo,_bp,_bq){var _br=new T(function(){return E(E(E(_bo).c).a);}),_bs=new T(function(){var _bt=new T(function(){return B(_8q(_br));}),_bu=new T(function(){var _bv=new T(function(){var _bw=B(_8s(_bt));return B(A3(_8G,_bw,new T(function(){return B(A2(_8I,_bw,_aH));}),new T(function(){return B(A3(_8u,_bw,_bp,_bp));})));});return B(A2(_8K,_br,_bv));});return B(A3(_ac,B(_a4(E(_bo).a)),function(_bx){return new F(function(){return A3(_a8,_bt,_bx,_bu);});},_bq));});return new T2(0,new T(function(){return B(A2(_bl,_br,_bp));}),_bs);},_by=function(_bz,_bA,_bB){var _bC=E(_bB),_bD=B(_bn(_bA,_bC.a,_bC.b));return new T2(0,_bD.a,_bD.b);},_bE=function(_bF){return E(E(_bF).q);},_bG=function(_bH,_bI,_bJ){var _bK=new T(function(){return E(E(E(_bH).c).a);}),_bL=new T(function(){var _bM=new T(function(){return B(_8q(_bK));}),_bN=new T(function(){var _bO=new T(function(){var _bP=B(_8s(_bM));return B(A3(_86,_bP,new T(function(){return B(A3(_8u,_bP,_bI,_bI));}),new T(function(){return B(A2(_8I,_bP,_aH));})));});return B(A2(_8K,_bK,_bO));});return B(A3(_ac,B(_a4(E(_bH).a)),function(_bQ){return new F(function(){return A3(_a8,_bM,_bQ,_bN);});},_bJ));});return new T2(0,new T(function(){return B(A2(_bE,_bK,_bI));}),_bL);},_bR=function(_bS,_bT,_bU){var _bV=E(_bU),_bW=B(_bG(_bT,_bV.a,_bV.b));return new T2(0,_bW.a,_bW.b);},_bX=function(_bY){return E(E(_bY).m);},_bZ=function(_c0,_c1,_c2){var _c3=new T(function(){return E(E(E(_c0).c).a);}),_c4=new T(function(){var _c5=new T(function(){return B(_8q(_c3));}),_c6=new T(function(){var _c7=B(_8s(_c5));return B(A3(_86,_c7,new T(function(){return B(A2(_8I,_c7,_aH));}),new T(function(){return B(A3(_8u,_c7,_c1,_c1));})));});return B(A3(_ac,B(_a4(E(_c0).a)),function(_c8){return new F(function(){return A3(_a8,_c5,_c8,_c6);});},_c2));});return new T2(0,new T(function(){return B(A2(_bX,_c3,_c1));}),_c4);},_c9=function(_ca,_cb,_cc){var _cd=E(_cc),_ce=B(_bZ(_cb,_cd.a,_cd.b));return new T2(0,_ce.a,_ce.b);},_cf=function(_cg){return E(E(_cg).s);},_ch=function(_ci,_cj,_ck){var _cl=new T(function(){return E(E(E(_ci).c).a);}),_cm=new T(function(){var _cn=new T(function(){return B(_8q(_cl));}),_co=new T(function(){var _cp=B(_8s(_cn));return B(A3(_8G,_cp,new T(function(){return B(A2(_8I,_cp,_aH));}),new T(function(){return B(A3(_8u,_cp,_cj,_cj));})));});return B(A3(_ac,B(_a4(E(_ci).a)),function(_cq){return new F(function(){return A3(_a8,_cn,_cq,_co);});},_ck));});return new T2(0,new T(function(){return B(A2(_cf,_cl,_cj));}),_cm);},_cr=function(_cs,_ct,_cu){var _cv=E(_cu),_cw=B(_ch(_ct,_cv.a,_cv.b));return new T2(0,_cw.a,_cw.b);},_cx=function(_cy){return E(E(_cy).i);},_cz=function(_cA){return E(E(_cA).h);},_cB=function(_cC,_cD,_cE){var _cF=new T(function(){return E(E(E(_cC).c).a);}),_cG=new T(function(){var _cH=new T(function(){return B(_8s(new T(function(){return B(_8q(_cF));})));}),_cI=new T(function(){return B(A2(_88,_cH,new T(function(){return B(A2(_cz,_cF,_cD));})));});return B(A3(_ac,B(_a4(E(_cC).a)),function(_cJ){return new F(function(){return A3(_8u,_cH,_cJ,_cI);});},_cE));});return new T2(0,new T(function(){return B(A2(_cx,_cF,_cD));}),_cG);},_cK=function(_cL,_cM,_cN){var _cO=E(_cN),_cP=B(_cB(_cM,_cO.a,_cO.b));return new T2(0,_cP.a,_cP.b);},_cQ=function(_cR){return E(E(_cR).o);},_cS=function(_cT){return E(E(_cT).n);},_cU=function(_cV,_cW,_cX){var _cY=new T(function(){return E(E(E(_cV).c).a);}),_cZ=new T(function(){var _d0=new T(function(){return B(_8s(new T(function(){return B(_8q(_cY));})));}),_d1=new T(function(){return B(A2(_cS,_cY,_cW));});return B(A3(_ac,B(_a4(E(_cV).a)),function(_d2){return new F(function(){return A3(_8u,_d0,_d2,_d1);});},_cX));});return new T2(0,new T(function(){return B(A2(_cQ,_cY,_cW));}),_cZ);},_d3=function(_d4,_d5,_d6){var _d7=E(_d6),_d8=B(_cU(_d5,_d7.a,_d7.b));return new T2(0,_d8.a,_d8.b);},_d9=function(_da){return E(E(_da).c);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(E(_dc).c).a);}),_dg=new T(function(){var _dh=new T(function(){return B(_8s(new T(function(){return B(_8q(_df));})));}),_di=new T(function(){return B(A2(_d9,_df,_dd));});return B(A3(_ac,B(_a4(E(_dc).a)),function(_dj){return new F(function(){return A3(_8u,_dh,_dj,_di);});},_de));});return new T2(0,new T(function(){return B(A2(_d9,_df,_dd));}),_dg);},_dk=function(_dl,_dm,_dn){var _do=E(_dn),_dp=B(_db(_dm,_do.a,_do.b));return new T2(0,_dp.a,_dp.b);},_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_8q(_du));}),_dx=new T(function(){return B(_8s(_dw));}),_dy=new T(function(){return B(A3(_a8,_dw,new T(function(){return B(A2(_8I,_dx,_aH));}),_ds));});return B(A3(_ac,B(_a4(E(_dr).a)),function(_dz){return new F(function(){return A3(_8u,_dx,_dz,_dy);});},_dt));});return new T2(0,new T(function(){return B(A2(_ae,_du,_ds));}),_dv);},_dA=function(_dB,_dC,_dD){var _dE=E(_dD),_dF=B(_dq(_dC,_dE.a,_dE.b));return new T2(0,_dF.a,_dF.b);},_dG=function(_dH,_dI,_dJ,_dK){var _dL=new T(function(){return E(E(_dI).c);}),_dM=new T3(0,new T(function(){return E(E(_dI).a);}),new T(function(){return E(E(_dI).b);}),new T2(0,new T(function(){return E(E(_dL).a);}),new T(function(){return E(E(_dL).b);})));return new F(function(){return A3(_a8,_dH,new T(function(){var _dN=E(_dK),_dO=B(_dq(_dM,_dN.a,_dN.b));return new T2(0,_dO.a,_dO.b);}),new T(function(){var _dP=E(_dJ),_dQ=B(_dq(_dM,_dP.a,_dP.b));return new T2(0,_dQ.a,_dQ.b);}));});},_dR=function(_dS){return E(E(_dS).b);},_dT=function(_dU){return E(E(_dU).b);},_dV=function(_dW){var _dX=new T(function(){return E(E(E(_dW).c).a);}),_dY=new T(function(){return B(A2(_dT,E(_dW).a,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_dX)))),_L));})));});return new T2(0,new T(function(){return B(_dR(_dX));}),_dY);},_dZ=function(_e0,_e1){var _e2=B(_dV(_e1));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(E(_e4).c).a);}),_e8=new T(function(){var _e9=new T(function(){return B(_8s(new T(function(){return B(_8q(_e7));})));}),_ea=new T(function(){return B(A2(_cx,_e7,_e5));});return B(A3(_ac,B(_a4(E(_e4).a)),function(_eb){return new F(function(){return A3(_8u,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cz,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=function(_ej,_ek,_el){var _em=new T(function(){return E(E(E(_ej).c).a);}),_en=new T(function(){var _eo=new T(function(){return B(_8s(new T(function(){return B(_8q(_em));})));}),_ep=new T(function(){return B(A2(_cQ,_em,_ek));});return B(A3(_ac,B(_a4(E(_ej).a)),function(_eq){return new F(function(){return A3(_8u,_eo,_eq,_ep);});},_el));});return new T2(0,new T(function(){return B(A2(_cS,_em,_ek));}),_en);},_er=function(_es,_et,_eu){var _ev=E(_eu),_ew=B(_ei(_et,_ev.a,_ev.b));return new T2(0,_ew.a,_ew.b);},_ex=new T1(0,2),_ey=function(_ez,_eA,_eB){var _eC=new T(function(){return E(E(E(_ez).c).a);}),_eD=new T(function(){var _eE=new T(function(){return B(_8q(_eC));}),_eF=new T(function(){return B(_8s(_eE));}),_eG=new T(function(){var _eH=new T(function(){return B(A3(_a8,_eE,new T(function(){return B(A2(_8I,_eF,_aH));}),new T(function(){return B(A2(_8I,_eF,_ex));})));});return B(A3(_a8,_eE,_eH,new T(function(){return B(A2(_8K,_eC,_eA));})));});return B(A3(_ac,B(_a4(E(_ez).a)),function(_eI){return new F(function(){return A3(_8u,_eF,_eI,_eG);});},_eB));});return new T2(0,new T(function(){return B(A2(_8K,_eC,_eA));}),_eD);},_eJ=function(_eK,_eL,_eM){var _eN=E(_eM),_eO=B(_ey(_eL,_eN.a,_eN.b));return new T2(0,_eO.a,_eO.b);},_eP=function(_eQ){return E(E(_eQ).j);},_eR=function(_eS,_eT,_eU){var _eV=new T(function(){return E(E(E(_eS).c).a);}),_eW=new T(function(){var _eX=new T(function(){return B(_8q(_eV));}),_eY=new T(function(){var _eZ=new T(function(){return B(A2(_cx,_eV,_eT));});return B(A3(_8u,B(_8s(_eX)),_eZ,_eZ));});return B(A3(_ac,B(_a4(E(_eS).a)),function(_f0){return new F(function(){return A3(_a8,_eX,_f0,_eY);});},_eU));});return new T2(0,new T(function(){return B(A2(_eP,_eV,_eT));}),_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eR(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8){return E(E(_f8).p);},_f9=function(_fa,_fb,_fc){var _fd=new T(function(){return E(E(E(_fa).c).a);}),_fe=new T(function(){var _ff=new T(function(){return B(_8q(_fd));}),_fg=new T(function(){var _fh=new T(function(){return B(A2(_cQ,_fd,_fb));});return B(A3(_8u,B(_8s(_ff)),_fh,_fh));});return B(A3(_ac,B(_a4(E(_fa).a)),function(_fi){return new F(function(){return A3(_a8,_ff,_fi,_fg);});},_fc));});return new T2(0,new T(function(){return B(A2(_f7,_fd,_fb));}),_fe);},_fj=function(_fk,_fl,_fm){var _fn=E(_fm),_fo=B(_f9(_fl,_fn.a,_fn.b));return new T2(0,_fo.a,_fo.b);},_fp=function(_fq,_fr){return {_:0,a:_fq,b:new T(function(){return B(_dZ(_fq,_fr));}),c:function(_fs){return new F(function(){return _dk(_fq,_fr,_fs);});},d:function(_fs){return new F(function(){return _dA(_fq,_fr,_fs);});},e:function(_fs){return new F(function(){return _eJ(_fq,_fr,_fs);});},f:function(_ft,_fs){return new F(function(){return _az(_fq,_fr,_ft,_fs);});},g:function(_ft,_fs){return new F(function(){return _dG(_fq,_fr,_ft,_fs);});},h:function(_fs){return new F(function(){return _ec(_fq,_fr,_fs);});},i:function(_fs){return new F(function(){return _cK(_fq,_fr,_fs);});},j:function(_fs){return new F(function(){return _f1(_fq,_fr,_fs);});},k:function(_fs){return new F(function(){return _by(_fq,_fr,_fs);});},l:function(_fs){return new F(function(){return _aW(_fq,_fr,_fs);});},m:function(_fs){return new F(function(){return _c9(_fq,_fr,_fs);});},n:function(_fs){return new F(function(){return _er(_fq,_fr,_fs);});},o:function(_fs){return new F(function(){return _d3(_fq,_fr,_fs);});},p:function(_fs){return new F(function(){return _fj(_fq,_fr,_fs);});},q:function(_fs){return new F(function(){return _bR(_fq,_fr,_fs);});},r:function(_fs){return new F(function(){return _bf(_fq,_fr,_fs);});},s:function(_fs){return new F(function(){return _cr(_fq,_fr,_fs);});}};},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8q(new T(function(){return E(E(E(_fv).c).a);})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){var _fE=new T(function(){return B(_8s(_fA));}),_fF=new T(function(){return B(A3(_8u,_fE,_fy,_fy));}),_fG=function(_fH,_fI){var _fJ=new T(function(){return B(A3(_8G,_fE,new T(function(){return B(A3(_8u,_fE,_fH,_fy));}),new T(function(){return B(A3(_8u,_fE,_fw,_fI));})));});return new F(function(){return A3(_a8,_fA,_fJ,_fF);});};return B(A3(_ac,B(_a4(_fC)),_fG,_fx));});return B(A3(_aa,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_a8,_fA,_fw,_fy));}),_fB);},_fK=function(_fL,_fM,_fN,_fO){var _fP=E(_fN),_fQ=E(_fO),_fR=B(_fu(_fM,_fP.a,_fP.b,_fQ.a,_fQ.b));return new T2(0,_fR.a,_fR.b);},_fS=function(_fT){return E(E(_fT).d);},_fU=function(_fV,_fW){var _fX=new T(function(){return B(_8q(new T(function(){return E(E(E(_fV).c).a);})));}),_fY=new T(function(){return B(A2(_dT,E(_fV).a,new T(function(){return B(A2(_8I,B(_8s(_fX)),_L));})));});return new T2(0,new T(function(){return B(A2(_fS,_fX,_fW));}),_fY);},_fZ=function(_g0,_g1,_g2){var _g3=B(_fU(_g1,_g2));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6,_g7){var _g8=new T(function(){return B(_8q(new T(function(){return E(E(E(_g5).c).a);})));}),_g9=new T(function(){return B(_8s(_g8));}),_ga=new T(function(){var _gb=new T(function(){var _gc=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),new T(function(){return B(A3(_8u,_g9,_g6,_g6));})));});return B(A2(_88,_g9,_gc));});return B(A3(_ac,B(_a4(E(_g5).a)),function(_gd){return new F(function(){return A3(_8u,_g9,_gd,_gb);});},_g7));}),_ge=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),_g6));});return new T2(0,_ge,_ga);},_gf=function(_gg,_gh,_gi){var _gj=E(_gi),_gk=B(_g4(_gh,_gj.a,_gj.b));return new T2(0,_gk.a,_gk.b);},_gl=function(_gm,_gn){return new T4(0,_gm,function(_ft,_fs){return new F(function(){return _fK(_gm,_gn,_ft,_fs);});},function(_fs){return new F(function(){return _gf(_gm,_gn,_fs);});},function(_fs){return new F(function(){return _fZ(_gm,_gn,_fs);});});},_go=function(_gp,_gq,_gr,_gs,_gt){var _gu=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gv=new T(function(){var _gw=E(_gp).a,_gx=new T(function(){var _gy=function(_gz,_gA){return new F(function(){return A3(_86,_gu,new T(function(){return B(A3(_8u,_gu,_gq,_gA));}),new T(function(){return B(A3(_8u,_gu,_gz,_gs));}));});};return B(A3(_ac,B(_a4(_gw)),_gy,_gr));});return B(A3(_aa,_gw,_gx,_gt));});return new T2(0,new T(function(){return B(A3(_8u,_gu,_gq,_gs));}),_gv);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_go(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL,_gM,_gN){var _gO=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gP=new T(function(){var _gQ=E(_gJ).a,_gR=new T(function(){return B(A3(_ac,B(_a4(_gQ)),new T(function(){return B(_86(_gO));}),_gL));});return B(A3(_aa,_gQ,_gR,_gN));});return new T2(0,new T(function(){return B(A3(_86,_gO,_gK,_gM));}),_gP);},_gS=function(_gT,_gU,_gV){var _gW=E(_gU),_gX=E(_gV),_gY=B(_gI(_gT,_gW.a,_gW.b,_gX.a,_gX.b));return new T2(0,_gY.a,_gY.b);},_gZ=function(_h0,_h1,_h2){var _h3=B(_h4(_h0));return new F(function(){return A3(_86,_h3,_h1,new T(function(){return B(A2(_88,_h3,_h2));}));});},_h5=function(_h6){return E(E(_h6).e);},_h7=function(_h8){return E(E(_h8).f);},_h9=function(_ha,_hb,_hc){var _hd=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_ha).c).a);})));})));}),_he=new T(function(){var _hf=new T(function(){return B(A2(_h7,_hd,_hb));});return B(A3(_ac,B(_a4(E(_ha).a)),function(_hg){return new F(function(){return A3(_8u,_hd,_hg,_hf);});},_hc));});return new T2(0,new T(function(){return B(A2(_h5,_hd,_hb));}),_he);},_hh=function(_hi,_hj){var _hk=E(_hj),_hl=B(_h9(_hi,_hk.a,_hk.b));return new T2(0,_hl.a,_hl.b);},_hm=function(_hn,_ho){var _hp=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hn).c).a);})));})));}),_hq=new T(function(){return B(A2(_dT,E(_hn).a,new T(function(){return B(A2(_8I,_hp,_L));})));});return new T2(0,new T(function(){return B(A2(_8I,_hp,_ho));}),_hq);},_hr=function(_hs,_ht){var _hu=B(_hm(_hs,_ht));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy){var _hz=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hA=new T(function(){return B(A3(_ac,B(_a4(E(_hw).a)),new T(function(){return B(_88(_hz));}),_hy));});return new T2(0,new T(function(){return B(A2(_88,_hz,_hx));}),_hA);},_hB=function(_hC,_hD){var _hE=E(_hD),_hF=B(_hv(_hC,_hE.a,_hE.b));return new T2(0,_hF.a,_hF.b);},_hG=function(_hH,_hI){var _hJ=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hH).c).a);})));})));}),_hK=new T(function(){return B(A2(_dT,E(_hH).a,new T(function(){return B(A2(_8I,_hJ,_L));})));});return new T2(0,new T(function(){return B(A2(_h7,_hJ,_hI));}),_hK);},_hL=function(_hM,_hN){var _hO=B(_hG(_hM,E(_hN).a));return new T2(0,_hO.a,_hO.b);},_h4=function(_hP){return {_:0,a:function(_ft,_fs){return new F(function(){return _gS(_hP,_ft,_fs);});},b:function(_ft,_fs){return new F(function(){return _gZ(_hP,_ft,_fs);});},c:function(_ft,_fs){return new F(function(){return _gB(_hP,_ft,_fs);});},d:function(_fs){return new F(function(){return _hB(_hP,_fs);});},e:function(_fs){return new F(function(){return _hh(_hP,_fs);});},f:function(_fs){return new F(function(){return _hL(_hP,_fs);});},g:function(_fs){return new F(function(){return _hr(_hP,_fs);});}};},_hQ=function(_hR){var _hS=new T(function(){return E(E(_hR).a);}),_hT=new T3(0,_9Y,_a0,new T2(0,_hS,new T(function(){return E(E(_hR).b);}))),_hU=new T(function(){return B(_fp(new T(function(){return B(_gl(new T(function(){return B(_h4(_hT));}),_hT));}),_hT));}),_hV=new T(function(){return B(_8s(new T(function(){return B(_8q(_hS));})));}),_hW=function(_hX){return E(B(_8M(_hU,new T(function(){var _hY=E(_hX),_hZ=B(A2(_8I,_hV,_1o)),_i0=B(A2(_8I,_hV,_9Z));return new T3(0,E(new T2(0,_hY.a,new T3(0,E(_hZ),E(_i0),E(_i0)))),E(new T2(0,_hY.b,new T3(0,E(_i0),E(_hZ),E(_i0)))),E(new T2(0,_hY.c,new T3(0,E(_i0),E(_i0),E(_hZ)))));}))).b);};return E(_hW);},_i1=new T(function(){return B(_hQ(_9u));}),_i2=function(_i3,_i4){var _i5=E(_i4);return (_i5._==0)?__Z:new T2(1,_i3,new T2(1,_i5.a,new T(function(){return B(_i2(_i3,_i5.b));})));},_i6=new T(function(){var _i7=B(A1(_i1,_91));return new T2(1,_i7.a,new T(function(){return B(_i2(_22,new T2(1,_i7.b,new T2(1,_i7.c,_w))));}));}),_i8=new T1(1,_i6),_i9=new T2(1,_i8,_1S),_ia=new T(function(){return B(unCStr("vec3("));}),_ib=new T1(0,_ia),_ic=new T2(1,_ib,_i9),_id=new T(function(){return toJSStr(B(_1F(_x,_1l,_ic)));}),_ie=function(_if,_ig){while(1){var _ih=E(_if);if(!_ih._){return E(_ig);}else{var _ii=_ig+1|0;_if=_ih.b;_ig=_ii;continue;}}},_ij=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ik=new T(function(){return B(err(_ij));}),_il=0,_im=new T3(0,E(_il),E(_il),E(_il)),_in=new T2(0,E(_im),E(_il)),_io=new T(function(){return B(unCStr("Negative exponent"));}),_ip=new T(function(){return B(err(_io));}),_iq=function(_ir,_is,_it){while(1){if(!(_is%2)){var _iu=_ir*_ir,_iv=quot(_is,2);_ir=_iu;_is=_iv;continue;}else{var _iw=E(_is);if(_iw==1){return _ir*_it;}else{var _iu=_ir*_ir,_ix=_ir*_it;_ir=_iu;_is=quot(_iw-1|0,2);_it=_ix;continue;}}}},_iy=function(_iz,_iA){while(1){if(!(_iA%2)){var _iB=_iz*_iz,_iC=quot(_iA,2);_iz=_iB;_iA=_iC;continue;}else{var _iD=E(_iA);if(_iD==1){return E(_iz);}else{return new F(function(){return _iq(_iz*_iz,quot(_iD-1|0,2),_iz);});}}}},_iE=function(_iF){var _iG=E(_iF);return new F(function(){return Math.log(_iG+(_iG+1)*Math.sqrt((_iG-1)/(_iG+1)));});},_iH=function(_iI){var _iJ=E(_iI);return new F(function(){return Math.log(_iJ+Math.sqrt(1+_iJ*_iJ));});},_iK=function(_iL){var _iM=E(_iL);return 0.5*Math.log((1+_iM)/(1-_iM));},_iN=function(_iO,_iP){return Math.log(E(_iP))/Math.log(E(_iO));},_iQ=3.141592653589793,_iR=function(_iS){var _iT=E(_iS);return new F(function(){return _7J(_iT.a,_iT.b);});},_iU=function(_iV){return 1/E(_iV);},_iW=function(_iX){var _iY=E(_iX),_iZ=E(_iY);return (_iZ==0)?E(_7I):(_iZ<=0)? -_iZ:E(_iY);},_j0=function(_j1){var _j2=E(_j1);if(!_j2._){return _j2.a;}else{return new F(function(){return I_toNumber(_j2.a);});}},_j3=function(_j4){return new F(function(){return _j0(_j4);});},_j5=1,_j6=-1,_j7=function(_j8){var _j9=E(_j8);return (_j9<=0)?(_j9>=0)?E(_j9):E(_j6):E(_j5);},_ja=function(_jb,_jc){return E(_jb)-E(_jc);},_jd=function(_je){return  -E(_je);},_jf=function(_jg,_jh){return E(_jg)+E(_jh);},_ji=function(_jj,_jk){return E(_jj)*E(_jk);},_jl={_:0,a:_jf,b:_ja,c:_ji,d:_jd,e:_iW,f:_j7,g:_j3},_jm=function(_jn,_jo){return E(_jn)/E(_jo);},_jp=new T4(0,_jl,_jm,_iU,_iR),_jq=function(_jr){return new F(function(){return Math.acos(E(_jr));});},_js=function(_jt){return new F(function(){return Math.asin(E(_jt));});},_ju=function(_jv){return new F(function(){return Math.atan(E(_jv));});},_jw=function(_jx){return new F(function(){return Math.cos(E(_jx));});},_jy=function(_jz){return new F(function(){return cosh(E(_jz));});},_jA=function(_jB){return new F(function(){return Math.exp(E(_jB));});},_jC=function(_jD){return new F(function(){return Math.log(E(_jD));});},_jE=function(_jF,_jG){return new F(function(){return Math.pow(E(_jF),E(_jG));});},_jH=function(_jI){return new F(function(){return Math.sin(E(_jI));});},_jJ=function(_jK){return new F(function(){return sinh(E(_jK));});},_jL=function(_jM){return new F(function(){return Math.sqrt(E(_jM));});},_jN=function(_jO){return new F(function(){return Math.tan(E(_jO));});},_jP=function(_jQ){return new F(function(){return tanh(E(_jQ));});},_jR={_:0,a:_jp,b:_iQ,c:_jA,d:_jC,e:_jL,f:_jE,g:_iN,h:_jH,i:_jw,j:_jN,k:_js,l:_jq,m:_ju,n:_jJ,o:_jy,p:_jP,q:_iH,r:_iE,s:_iK},_jS=function(_jT,_jU){return (E(_jT)!=E(_jU))?true:false;},_jV=function(_jW,_jX){return E(_jW)==E(_jX);},_jY=new T2(0,_jV,_jS),_jZ=function(_k0,_k1){return E(_k0)<E(_k1);},_k2=function(_k3,_k4){return E(_k3)<=E(_k4);},_k5=function(_k6,_k7){return E(_k6)>E(_k7);},_k8=function(_k9,_ka){return E(_k9)>=E(_ka);},_kb=function(_kc,_kd){var _ke=E(_kc),_kf=E(_kd);return (_ke>=_kf)?(_ke!=_kf)?2:1:0;},_kg=function(_kh,_ki){var _kj=E(_kh),_kk=E(_ki);return (_kj>_kk)?E(_kj):E(_kk);},_kl=function(_km,_kn){var _ko=E(_km),_kp=E(_kn);return (_ko>_kp)?E(_kp):E(_ko);},_kq={_:0,a:_jY,b:_kb,c:_jZ,d:_k2,e:_k5,f:_k8,g:_kg,h:_kl},_kr="dz",_ks="wy",_kt="wx",_ku="dy",_kv="dx",_kw="t",_kx="a",_ky="r",_kz="ly",_kA="lx",_kB="wz",_kC=0,_kD=function(_kE){var _kF=__new(),_kG=_kF,_kH=function(_kI,_){while(1){var _kJ=E(_kI);if(!_kJ._){return _kC;}else{var _kK=E(_kJ.a),_kL=__set(_kG,E(_kK.a),E(_kK.b));_kI=_kJ.b;continue;}}},_kM=B(_kH(_kE,_));return E(_kG);},_kN=function(_kO,_kP,_kQ,_kR,_kS,_kT,_kU,_kV,_kW){return new F(function(){return _kD(new T2(1,new T2(0,_kt,_kO),new T2(1,new T2(0,_ks,_kP),new T2(1,new T2(0,_kB,_kQ),new T2(1,new T2(0,_kA,_kR*_kS*Math.cos(_kT)),new T2(1,new T2(0,_kz,_kR*_kS*Math.sin(_kT)),new T2(1,new T2(0,_ky,_kR),new T2(1,new T2(0,_kx,_kS),new T2(1,new T2(0,_kw,_kT),new T2(1,new T2(0,_kv,_kU),new T2(1,new T2(0,_ku,_kV),new T2(1,new T2(0,_kr,_kW),_w))))))))))));});},_kX=function(_kY){var _kZ=E(_kY),_l0=E(_kZ.a),_l1=E(_kZ.b),_l2=E(_kZ.d);return new F(function(){return _kN(_l0.a,_l0.b,_l0.c,E(_l1.a),E(_l1.b),E(_kZ.c),_l2.a,_l2.b,_l2.c);});},_l3=function(_l4,_l5){var _l6=E(_l5);return (_l6._==0)?__Z:new T2(1,new T(function(){return B(A1(_l4,_l6.a));}),new T(function(){return B(_l3(_l4,_l6.b));}));},_l7=function(_l8,_l9,_la){var _lb=__lst2arr(B(_l3(_kX,new T2(1,_l8,new T2(1,_l9,new T2(1,_la,_w))))));return E(_lb);},_lc=function(_ld){var _le=E(_ld);return new F(function(){return _l7(_le.a,_le.b,_le.c);});},_lf=new T2(0,_jR,_kq),_lg=function(_lh,_li,_lj,_lk){var _ll=B(_8q(_lh)),_lm=new T(function(){return B(A2(_8K,_lh,new T(function(){return B(_8w(_lh,_li,_lj,_lk,_li,_lj,_lk));})));});return new T3(0,B(A3(_a8,_ll,_li,_lm)),B(A3(_a8,_ll,_lj,_lm)),B(A3(_a8,_ll,_lk,_lm)));},_ln=function(_lo,_lp,_lq,_lr,_ls,_lt,_lu){var _lv=B(_8u(_lo));return new T3(0,B(A1(B(A1(_lv,_lp)),_ls)),B(A1(B(A1(_lv,_lq)),_lt)),B(A1(B(A1(_lv,_lr)),_lu)));},_lw=function(_lx,_ly,_lz,_lA,_lB,_lC,_lD){var _lE=B(_86(_lx));return new T3(0,B(A1(B(A1(_lE,_ly)),_lB)),B(A1(B(A1(_lE,_lz)),_lC)),B(A1(B(A1(_lE,_lA)),_lD)));},_lF=function(_lG,_lH){var _lI=new T(function(){return E(E(_lG).a);}),_lJ=new T(function(){return B(A2(_hQ,new T2(0,_lI,new T(function(){return E(E(_lG).b);})),_lH));}),_lK=new T(function(){var _lL=E(_lJ),_lM=B(_lg(_lI,_lL.a,_lL.b,_lL.c));return new T3(0,E(_lM.a),E(_lM.b),E(_lM.c));}),_lN=new T(function(){var _lO=E(_lH),_lP=E(_lK),_lQ=B(_8q(_lI)),_lR=new T(function(){return B(A2(_8K,_lI,new T(function(){var _lS=E(_lJ),_lT=_lS.a,_lU=_lS.b,_lV=_lS.c;return B(_8w(_lI,_lT,_lU,_lV,_lT,_lU,_lV));})));}),_lW=B(A3(_a8,_lQ,new T(function(){return B(_8M(_lI,_lO));}),_lR)),_lX=B(_8s(_lQ)),_lY=B(_ln(_lX,_lP.a,_lP.b,_lP.c,_lW,_lW,_lW)),_lZ=B(_88(_lX)),_m0=B(_lw(_lX,_lO.a,_lO.b,_lO.c,B(A1(_lZ,_lY.a)),B(A1(_lZ,_lY.b)),B(A1(_lZ,_lY.c))));return new T3(0,E(_m0.a),E(_m0.b),E(_m0.c));});return new T2(0,_lN,_lK);},_m1=function(_m2){return E(E(_m2).a);},_m3=function(_m4,_m5,_m6,_m7,_m8,_m9,_ma){var _mb=B(_8w(_m4,_m8,_m9,_ma,_m5,_m6,_m7)),_mc=B(_8s(B(_8q(_m4)))),_md=B(_ln(_mc,_m8,_m9,_ma,_mb,_mb,_mb)),_me=B(_88(_mc));return new F(function(){return _lw(_mc,_m5,_m6,_m7,B(A1(_me,_md.a)),B(A1(_me,_md.b)),B(A1(_me,_md.c)));});},_mf=function(_mg){return E(E(_mg).a);},_mh=function(_mi,_mj,_mk,_ml){var _mm=new T(function(){var _mn=E(_ml),_mo=E(_mk),_mp=B(_m3(_mi,_mn.a,_mn.b,_mn.c,_mo.a,_mo.b,_mo.c));return new T3(0,E(_mp.a),E(_mp.b),E(_mp.c));}),_mq=new T(function(){return B(A2(_8K,_mi,new T(function(){var _mr=E(_mm),_ms=_mr.a,_mt=_mr.b,_mu=_mr.c;return B(_8w(_mi,_ms,_mt,_mu,_ms,_mt,_mu));})));});if(!B(A3(_mf,B(_m1(_mj)),_mq,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_mi)))),_9Z));})))){var _mv=E(_mm),_mw=B(_lg(_mi,_mv.a,_mv.b,_mv.c)),_mx=B(A2(_8K,_mi,new T(function(){var _my=E(_ml),_mz=_my.a,_mA=_my.b,_mB=_my.c;return B(_8w(_mi,_mz,_mA,_mB,_mz,_mA,_mB));}))),_mC=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_mi));})));})));return new T3(0,B(A1(B(A1(_mC,_mw.a)),_mx)),B(A1(B(A1(_mC,_mw.b)),_mx)),B(A1(B(A1(_mC,_mw.c)),_mx)));}else{var _mD=B(A2(_8I,B(_8s(B(_8q(_mi)))),_9Z));return new T3(0,_mD,_mD,_mD);}},_mE=new T(function(){var _mF=eval("angleCount"),_mG=Number(_mF);return jsTrunc(_mG);}),_mH=new T(function(){return E(_mE);}),_mI=new T(function(){return B(unCStr(": empty list"));}),_mJ=new T(function(){return B(unCStr("Prelude."));}),_mK=function(_mL){return new F(function(){return err(B(_n(_mJ,new T(function(){return B(_n(_mL,_mI));},1))));});},_mM=new T(function(){return B(unCStr("head"));}),_mN=new T(function(){return B(_mK(_mM));}),_mO=function(_mP,_mQ,_mR){var _mS=E(_mP);if(!_mS._){return __Z;}else{var _mT=E(_mQ);if(!_mT._){return __Z;}else{var _mU=_mT.a,_mV=E(_mR);if(!_mV._){return __Z;}else{var _mW=E(_mV.a),_mX=_mW.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_mS.a),E(_mU),E(_mX));}),new T2(1,new T(function(){return new T3(0,E(_mU),E(_mX),E(_mW.b));}),_w)),new T(function(){return B(_mO(_mS.b,_mT.b,_mV.b));},1));});}}}},_mY=new T(function(){return B(unCStr("tail"));}),_mZ=new T(function(){return B(_mK(_mY));}),_n0=function(_n1,_n2){var _n3=E(_n1);if(!_n3._){return __Z;}else{var _n4=E(_n2);return (_n4._==0)?__Z:new T2(1,new T2(0,_n3.a,_n4.a),new T(function(){return B(_n0(_n3.b,_n4.b));}));}},_n5=function(_n6,_n7){var _n8=E(_n6);if(!_n8._){return __Z;}else{var _n9=E(_n7);if(!_n9._){return __Z;}else{var _na=E(_n8.a),_nb=_na.b,_nc=E(_n9.a).b,_nd=new T(function(){var _ne=new T(function(){return B(_n0(_nc,new T(function(){var _nf=E(_nc);if(!_nf._){return E(_mZ);}else{return E(_nf.b);}},1)));},1);return B(_mO(_nb,new T(function(){var _ng=E(_nb);if(!_ng._){return E(_mZ);}else{return E(_ng.b);}},1),_ne));});return new F(function(){return _n(new T2(1,new T(function(){var _nh=E(_nb);if(!_nh._){return E(_mN);}else{var _ni=E(_nc);if(!_ni._){return E(_mN);}else{return new T3(0,E(_na.a),E(_nh.a),E(_ni.a));}}}),_nd),new T(function(){return B(_n5(_n8.b,_n9.b));},1));});}}},_nj=new T(function(){return E(_mH)-1;}),_nk=new T1(0,1),_nl=function(_nm,_nn){var _no=E(_nn),_np=new T(function(){var _nq=B(_8s(_nm)),_nr=B(_nl(_nm,B(A3(_86,_nq,_no,new T(function(){return B(A2(_8I,_nq,_nk));})))));return new T2(1,_nr.a,_nr.b);});return new T2(0,_no,_np);},_ns=function(_nt){return E(E(_nt).d);},_nu=new T1(0,2),_nv=function(_nw,_nx){var _ny=E(_nx);if(!_ny._){return __Z;}else{var _nz=_ny.a;return (!B(A1(_nw,_nz)))?__Z:new T2(1,_nz,new T(function(){return B(_nv(_nw,_ny.b));}));}},_nA=function(_nB,_nC,_nD,_nE){var _nF=B(_nl(_nC,_nD)),_nG=new T(function(){var _nH=B(_8s(_nC)),_nI=new T(function(){return B(A3(_a8,_nC,new T(function(){return B(A2(_8I,_nH,_nk));}),new T(function(){return B(A2(_8I,_nH,_nu));})));});return B(A3(_86,_nH,_nE,_nI));});return new F(function(){return _nv(function(_nJ){return new F(function(){return A3(_ns,_nB,_nJ,_nG);});},new T2(1,_nF.a,_nF.b));});},_nK=new T(function(){return B(_nA(_kq,_jp,_il,_nj));}),_nL=function(_nM,_nN){while(1){var _nO=E(_nM);if(!_nO._){return E(_nN);}else{_nM=_nO.b;_nN=_nO.a;continue;}}},_nP=new T(function(){return B(unCStr("last"));}),_nQ=new T(function(){return B(_mK(_nP));}),_nR=function(_nS){return new F(function(){return _nL(_nS,_nQ);});},_nT=function(_nU){return new F(function(){return _nR(E(_nU).b);});},_nV=new T(function(){var _nW=eval("proceedCount"),_nX=Number(_nW);return jsTrunc(_nX);}),_nY=new T(function(){return E(_nV);}),_nZ=1,_o0=new T(function(){return B(_nA(_kq,_jp,_nZ,_nY));}),_o1=function(_o2,_o3,_o4,_o5,_o6,_o7,_o8,_o9,_oa,_ob,_oc,_od,_oe,_of){var _og=new T(function(){var _oh=new T(function(){var _oi=E(_ob),_oj=E(_of),_ok=E(_oe),_ol=E(_oc),_om=E(_od),_on=E(_oa);return new T3(0,_oi*_oj-_ok*_ol,_ol*_om-_oj*_on,_on*_ok-_om*_oi);}),_oo=function(_op){var _oq=new T(function(){var _or=E(_op)/E(_mH);return (_or+_or)*3.141592653589793;}),_os=new T(function(){return B(A1(_o2,_oq));}),_ot=new T(function(){var _ou=new T(function(){var _ov=E(_os)/E(_nY);return new T3(0,E(_ov),E(_ov),E(_ov));}),_ow=function(_ox,_oy){var _oz=E(_ox);if(!_oz._){return new T2(0,_w,_oy);}else{var _oA=new T(function(){var _oB=B(_lF(_lf,new T(function(){var _oC=E(_oy),_oD=E(_oC.a),_oE=E(_oC.b),_oF=E(_ou);return new T3(0,E(_oD.a)+E(_oE.a)*E(_oF.a),E(_oD.b)+E(_oE.b)*E(_oF.b),E(_oD.c)+E(_oE.c)*E(_oF.c));}))),_oG=_oB.a,_oH=new T(function(){var _oI=E(_oB.b),_oJ=E(E(_oy).b),_oK=B(_m3(_jR,_oJ.a,_oJ.b,_oJ.c,_oI.a,_oI.b,_oI.c)),_oL=B(_lg(_jR,_oK.a,_oK.b,_oK.c));return new T3(0,E(_oL.a),E(_oL.b),E(_oL.c));});return new T2(0,new T(function(){var _oM=E(_os),_oN=E(_oq);return new T4(0,E(_oG),E(new T2(0,E(_oz.a)/E(_nY),E(_oM))),E(_oN),E(_oH));}),new T2(0,_oG,_oH));}),_oO=new T(function(){var _oP=B(_ow(_oz.b,new T(function(){return E(E(_oA).b);})));return new T2(0,_oP.a,_oP.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oA).a);}),new T(function(){return E(E(_oO).a);})),new T(function(){return E(E(_oO).b);}));}},_oQ=function(_oR,_oS,_oT,_oU,_oV){var _oW=E(_oR);if(!_oW._){return new T2(0,_w,new T2(0,new T3(0,E(_oS),E(_oT),E(_oU)),_oV));}else{var _oX=new T(function(){var _oY=B(_lF(_lf,new T(function(){var _oZ=E(_oV),_p0=E(_ou);return new T3(0,E(_oS)+E(_oZ.a)*E(_p0.a),E(_oT)+E(_oZ.b)*E(_p0.b),E(_oU)+E(_oZ.c)*E(_p0.c));}))),_p1=_oY.a,_p2=new T(function(){var _p3=E(_oY.b),_p4=E(_oV),_p5=B(_m3(_jR,_p4.a,_p4.b,_p4.c,_p3.a,_p3.b,_p3.c)),_p6=B(_lg(_jR,_p5.a,_p5.b,_p5.c));return new T3(0,E(_p6.a),E(_p6.b),E(_p6.c));});return new T2(0,new T(function(){var _p7=E(_os),_p8=E(_oq);return new T4(0,E(_p1),E(new T2(0,E(_oW.a)/E(_nY),E(_p7))),E(_p8),E(_p2));}),new T2(0,_p1,_p2));}),_p9=new T(function(){var _pa=B(_ow(_oW.b,new T(function(){return E(E(_oX).b);})));return new T2(0,_pa.a,_pa.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oX).a);}),new T(function(){return E(E(_p9).a);})),new T(function(){return E(E(_p9).b);}));}};return E(B(_oQ(_o0,_o5,_o6,_o7,new T(function(){var _pb=E(_oh),_pc=E(_oq)+_o8,_pd=Math.cos(_pc),_pe=Math.sin(_pc);return new T3(0,E(_oa)*_pd+E(_pb.a)*_pe,E(_ob)*_pd+E(_pb.b)*_pe,E(_oc)*_pd+E(_pb.c)*_pe);}))).a);});return new T2(0,new T(function(){var _pf=E(_os),_pg=E(_oq);return new T4(0,E(new T3(0,E(_o5),E(_o6),E(_o7))),E(new T2(0,E(_il),E(_pf))),E(_pg),E(_im));}),_ot);};return B(_l3(_oo,_nK));}),_ph=new T(function(){var _pi=new T(function(){var _pj=B(_n(_og,new T2(1,new T(function(){var _pk=E(_og);if(!_pk._){return E(_mN);}else{return E(_pk.a);}}),_w)));if(!_pj._){return E(_mZ);}else{return E(_pj.b);}},1);return B(_n5(_og,_pi));});return new T2(0,_ph,new T(function(){return B(_l3(_nT,_og));}));},_pl=function(_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt,_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_pC){var _pD=B(_lF(_lf,new T3(0,E(_pp),E(_pq),E(_pr)))),_pE=_pD.b,_pF=E(_pD.a),_pG=B(_mh(_jR,_kq,_pE,new T3(0,E(_pt),E(_pu),E(_pv)))),_pH=E(_pE),_pI=_pH.a,_pJ=_pH.b,_pK=_pH.c,_pL=B(_m3(_jR,_px,_py,_pz,_pI,_pJ,_pK)),_pM=B(_lg(_jR,_pL.a,_pL.b,_pL.c)),_pN=_pM.a,_pO=_pM.b,_pP=_pM.c,_pQ=E(_ps),_pR=new T2(0,E(new T3(0,E(_pG.a),E(_pG.b),E(_pG.c))),E(_pw)),_pS=B(_o1(_pm,_pn,_po,_pF.a,_pF.b,_pF.c,_pQ,_pR,_pN,_pO,_pP,_pI,_pJ,_pK)),_pT=__lst2arr(B(_l3(_lc,_pS.a))),_pU=__lst2arr(B(_l3(_kX,_pS.b)));return {_:0,a:_pm,b:_pn,c:_po,d:new T2(0,E(_pF),E(_pQ)),e:_pR,f:new T3(0,E(_pN),E(_pO),E(_pP)),g:_pH,h:_pT,i:_pU};},_pV=function(_pW){var _pX=E(_pW);return new T3(0, -E(_pX.a),E(_pX.c), -E(_pX.b));},_pY=new T(function(){return 6.283185307179586/E(_mH);}),_pZ=function(_){return new F(function(){return __jsNull();});},_q0=function(_q1){var _q2=B(A1(_q1,_));return E(_q2);},_q3=new T(function(){return B(_q0(_pZ));}),_q4=function(_q5,_q6,_q7,_q8,_q9,_qa,_qb,_qc,_qd,_qe,_qf,_qg,_qh){var _qi=function(_qj){var _qk=E(_pY),_ql=2+_qj|0,_qm=_ql-1|0,_qn=(2+_qj)*(1+_qj),_qo=E(_nK);if(!_qo._){return _qk*0;}else{var _qp=_qo.a,_qq=_qo.b,_qr=B(A1(_q5,new T(function(){return 6.283185307179586*E(_qp)/E(_mH);}))),_qs=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_qp)+1)/E(_mH);})));if(_qr!=_qs){if(_ql>=0){var _qt=E(_ql);if(!_qt){var _qu=function(_qv,_qw){while(1){var _qx=B((function(_qy,_qz){var _qA=E(_qy);if(!_qA._){return E(_qz);}else{var _qB=_qA.a,_qC=_qA.b,_qD=B(A1(_q5,new T(function(){return 6.283185307179586*E(_qB)/E(_mH);}))),_qE=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_qB)+1)/E(_mH);})));if(_qD!=_qE){var _qF=_qz+0/(_qD-_qE)/_qn;_qv=_qC;_qw=_qF;return __continue;}else{if(_qm>=0){var _qG=E(_qm);if(!_qG){var _qF=_qz+_ql/_qn;_qv=_qC;_qw=_qF;return __continue;}else{var _qF=_qz+_ql*B(_iy(_qD,_qG))/_qn;_qv=_qC;_qw=_qF;return __continue;}}else{return E(_ip);}}}})(_qv,_qw));if(_qx!=__continue){return _qx;}}};return _qk*B(_qu(_qq,0/(_qr-_qs)/_qn));}else{var _qH=function(_qI,_qJ){while(1){var _qK=B((function(_qL,_qM){var _qN=E(_qL);if(!_qN._){return E(_qM);}else{var _qO=_qN.a,_qP=_qN.b,_qQ=B(A1(_q5,new T(function(){return 6.283185307179586*E(_qO)/E(_mH);}))),_qR=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_qO)+1)/E(_mH);})));if(_qQ!=_qR){if(_qt>=0){var _qS=_qM+(B(_iy(_qQ,_qt))-B(_iy(_qR,_qt)))/(_qQ-_qR)/_qn;_qI=_qP;_qJ=_qS;return __continue;}else{return E(_ip);}}else{if(_qm>=0){var _qT=E(_qm);if(!_qT){var _qS=_qM+_ql/_qn;_qI=_qP;_qJ=_qS;return __continue;}else{var _qS=_qM+_ql*B(_iy(_qQ,_qT))/_qn;_qI=_qP;_qJ=_qS;return __continue;}}else{return E(_ip);}}}})(_qI,_qJ));if(_qK!=__continue){return _qK;}}};return _qk*B(_qH(_qq,(B(_iy(_qr,_qt))-B(_iy(_qs,_qt)))/(_qr-_qs)/_qn));}}else{return E(_ip);}}else{if(_qm>=0){var _qU=E(_qm);if(!_qU){var _qV=function(_qW,_qX){while(1){var _qY=B((function(_qZ,_r0){var _r1=E(_qZ);if(!_r1._){return E(_r0);}else{var _r2=_r1.a,_r3=_r1.b,_r4=B(A1(_q5,new T(function(){return 6.283185307179586*E(_r2)/E(_mH);}))),_r5=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_r2)+1)/E(_mH);})));if(_r4!=_r5){if(_ql>=0){var _r6=E(_ql);if(!_r6){var _r7=_r0+0/(_r4-_r5)/_qn;_qW=_r3;_qX=_r7;return __continue;}else{var _r7=_r0+(B(_iy(_r4,_r6))-B(_iy(_r5,_r6)))/(_r4-_r5)/_qn;_qW=_r3;_qX=_r7;return __continue;}}else{return E(_ip);}}else{var _r7=_r0+_ql/_qn;_qW=_r3;_qX=_r7;return __continue;}}})(_qW,_qX));if(_qY!=__continue){return _qY;}}};return _qk*B(_qV(_qq,_ql/_qn));}else{var _r8=function(_r9,_ra){while(1){var _rb=B((function(_rc,_rd){var _re=E(_rc);if(!_re._){return E(_rd);}else{var _rf=_re.a,_rg=_re.b,_rh=B(A1(_q5,new T(function(){return 6.283185307179586*E(_rf)/E(_mH);}))),_ri=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_rf)+1)/E(_mH);})));if(_rh!=_ri){if(_ql>=0){var _rj=E(_ql);if(!_rj){var _rk=_rd+0/(_rh-_ri)/_qn;_r9=_rg;_ra=_rk;return __continue;}else{var _rk=_rd+(B(_iy(_rh,_rj))-B(_iy(_ri,_rj)))/(_rh-_ri)/_qn;_r9=_rg;_ra=_rk;return __continue;}}else{return E(_ip);}}else{if(_qU>=0){var _rk=_rd+_ql*B(_iy(_rh,_qU))/_qn;_r9=_rg;_ra=_rk;return __continue;}else{return E(_ip);}}}})(_r9,_ra));if(_rb!=__continue){return _rb;}}};return _qk*B(_r8(_qq,_ql*B(_iy(_qr,_qU))/_qn));}}else{return E(_ip);}}}},_rl=E(_q3),_rm=1/(B(_qi(1))*_q6);return new F(function(){return _pl(_q5,_pV,new T2(0,E(new T3(0,E(_rm),E(_rm),E(_rm))),1/(B(_qi(3))*_q6)),_q7,_q8,_q9,_qa,_qb,_qc,_qd,_qe,_qf,_qg,_qh,_im,_rl,_rl);});},_rn=1,_ro=0,_rp=function(_rq){return E(_im);},_rr=function(_rs){var _rt=I_decodeDouble(_rs);return new T2(0,new T1(1,_rt.b),_rt.a);},_ru=function(_rv){return new T1(0,_rv);},_rw=function(_rx){var _ry=hs_intToInt64(2147483647),_rz=hs_leInt64(_rx,_ry);if(!_rz){return new T1(1,I_fromInt64(_rx));}else{var _rA=hs_intToInt64(-2147483648),_rB=hs_geInt64(_rx,_rA);if(!_rB){return new T1(1,I_fromInt64(_rx));}else{var _rC=hs_int64ToInt(_rx);return new F(function(){return _ru(_rC);});}}},_rD=new T(function(){var _rE=newByteArr(256),_rF=_rE,_=_rF["v"]["i8"][0]=8,_rG=function(_rH,_rI,_rJ,_){while(1){if(_rJ>=256){if(_rH>=256){return E(_);}else{var _rK=imul(2,_rH)|0,_rL=_rI+1|0,_rM=_rH;_rH=_rK;_rI=_rL;_rJ=_rM;continue;}}else{var _=_rF["v"]["i8"][_rJ]=_rI,_rM=_rJ+_rH|0;_rJ=_rM;continue;}}},_=B(_rG(2,0,1,_));return _rF;}),_rN=function(_rO,_rP){var _rQ=hs_int64ToInt(_rO),_rR=E(_rD),_rS=_rR["v"]["i8"][(255&_rQ>>>0)>>>0&4294967295];if(_rP>_rS){if(_rS>=8){var _rT=hs_uncheckedIShiftRA64(_rO,8),_rU=function(_rV,_rW){while(1){var _rX=B((function(_rY,_rZ){var _s0=hs_int64ToInt(_rY),_s1=_rR["v"]["i8"][(255&_s0>>>0)>>>0&4294967295];if(_rZ>_s1){if(_s1>=8){var _s2=hs_uncheckedIShiftRA64(_rY,8),_s3=_rZ-8|0;_rV=_s2;_rW=_s3;return __continue;}else{return new T2(0,new T(function(){var _s4=hs_uncheckedIShiftRA64(_rY,_s1);return B(_rw(_s4));}),_rZ-_s1|0);}}else{return new T2(0,new T(function(){var _s5=hs_uncheckedIShiftRA64(_rY,_rZ);return B(_rw(_s5));}),0);}})(_rV,_rW));if(_rX!=__continue){return _rX;}}};return new F(function(){return _rU(_rT,_rP-8|0);});}else{return new T2(0,new T(function(){var _s6=hs_uncheckedIShiftRA64(_rO,_rS);return B(_rw(_s6));}),_rP-_rS|0);}}else{return new T2(0,new T(function(){var _s7=hs_uncheckedIShiftRA64(_rO,_rP);return B(_rw(_s7));}),0);}},_s8=function(_s9){var _sa=hs_intToInt64(_s9);return E(_sa);},_sb=function(_sc){var _sd=E(_sc);if(!_sd._){return new F(function(){return _s8(_sd.a);});}else{return new F(function(){return I_toInt64(_sd.a);});}},_se=function(_sf){return I_toInt(_sf)>>>0;},_sg=function(_sh){var _si=E(_sh);if(!_si._){return _si.a>>>0;}else{return new F(function(){return _se(_si.a);});}},_sj=function(_sk){var _sl=B(_rr(_sk)),_sm=_sl.a,_sn=_sl.b;if(_sn<0){var _so=function(_sp){if(!_sp){return new T2(0,E(_sm),B(_52(_3k, -_sn)));}else{var _sq=B(_rN(B(_sb(_sm)), -_sn));return new T2(0,E(_sq.a),B(_52(_3k,_sq.b)));}};if(!((B(_sg(_sm))&1)>>>0)){return new F(function(){return _so(1);});}else{return new F(function(){return _so(0);});}}else{return new T2(0,B(_52(_sm,_sn)),_3k);}},_sr=function(_ss){var _st=B(_sj(E(_ss)));return new T2(0,E(_st.a),E(_st.b));},_su=new T3(0,_jl,_kq,_sr),_sv=function(_sw){return E(E(_sw).a);},_sx=function(_sy){return E(E(_sy).a);},_sz=function(_sA,_sB){if(_sA<=_sB){var _sC=function(_sD){return new T2(1,_sD,new T(function(){if(_sD!=_sB){return B(_sC(_sD+1|0));}else{return __Z;}}));};return new F(function(){return _sC(_sA);});}else{return __Z;}},_sE=function(_sF){return new F(function(){return _sz(E(_sF),2147483647);});},_sG=function(_sH,_sI,_sJ){if(_sJ<=_sI){var _sK=new T(function(){var _sL=_sI-_sH|0,_sM=function(_sN){return (_sN>=(_sJ-_sL|0))?new T2(1,_sN,new T(function(){return B(_sM(_sN+_sL|0));})):new T2(1,_sN,_w);};return B(_sM(_sI));});return new T2(1,_sH,_sK);}else{return (_sJ<=_sH)?new T2(1,_sH,_w):__Z;}},_sO=function(_sP,_sQ,_sR){if(_sR>=_sQ){var _sS=new T(function(){var _sT=_sQ-_sP|0,_sU=function(_sV){return (_sV<=(_sR-_sT|0))?new T2(1,_sV,new T(function(){return B(_sU(_sV+_sT|0));})):new T2(1,_sV,_w);};return B(_sU(_sQ));});return new T2(1,_sP,_sS);}else{return (_sR>=_sP)?new T2(1,_sP,_w):__Z;}},_sW=function(_sX,_sY){if(_sY<_sX){return new F(function(){return _sG(_sX,_sY,-2147483648);});}else{return new F(function(){return _sO(_sX,_sY,2147483647);});}},_sZ=function(_t0,_t1){return new F(function(){return _sW(E(_t0),E(_t1));});},_t2=function(_t3,_t4,_t5){if(_t4<_t3){return new F(function(){return _sG(_t3,_t4,_t5);});}else{return new F(function(){return _sO(_t3,_t4,_t5);});}},_t6=function(_t7,_t8,_t9){return new F(function(){return _t2(E(_t7),E(_t8),E(_t9));});},_ta=function(_tb,_tc){return new F(function(){return _sz(E(_tb),E(_tc));});},_td=function(_te){return E(_te);},_tf=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tg=new T(function(){return B(err(_tf));}),_th=function(_ti){var _tj=E(_ti);return (_tj==(-2147483648))?E(_tg):_tj-1|0;},_tk=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tl=new T(function(){return B(err(_tk));}),_tm=function(_tn){var _to=E(_tn);return (_to==2147483647)?E(_tl):_to+1|0;},_tp={_:0,a:_tm,b:_th,c:_td,d:_td,e:_sE,f:_sZ,g:_ta,h:_t6},_tq=function(_tr,_ts){if(_tr<=0){if(_tr>=0){return new F(function(){return quot(_tr,_ts);});}else{if(_ts<=0){return new F(function(){return quot(_tr,_ts);});}else{return quot(_tr+1|0,_ts)-1|0;}}}else{if(_ts>=0){if(_tr>=0){return new F(function(){return quot(_tr,_ts);});}else{if(_ts<=0){return new F(function(){return quot(_tr,_ts);});}else{return quot(_tr+1|0,_ts)-1|0;}}}else{return quot(_tr-1|0,_ts)-1|0;}}},_tt=0,_tu=new T(function(){return B(_4p(_tt));}),_tv=new T(function(){return die(_tu);}),_tw=function(_tx,_ty){var _tz=E(_ty);switch(_tz){case -1:var _tA=E(_tx);if(_tA==(-2147483648)){return E(_tv);}else{return new F(function(){return _tq(_tA,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tq(_tx,_tz);});}},_tB=function(_tC,_tD){return new F(function(){return _tw(E(_tC),E(_tD));});},_tE=0,_tF=new T2(0,_tv,_tE),_tG=function(_tH,_tI){var _tJ=E(_tH),_tK=E(_tI);switch(_tK){case -1:var _tL=E(_tJ);if(_tL==(-2147483648)){return E(_tF);}else{if(_tL<=0){if(_tL>=0){var _tM=quotRemI(_tL,-1);return new T2(0,_tM.a,_tM.b);}else{var _tN=quotRemI(_tL,-1);return new T2(0,_tN.a,_tN.b);}}else{var _tO=quotRemI(_tL-1|0,-1);return new T2(0,_tO.a-1|0,(_tO.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_tJ<=0){if(_tJ>=0){var _tP=quotRemI(_tJ,_tK);return new T2(0,_tP.a,_tP.b);}else{if(_tK<=0){var _tQ=quotRemI(_tJ,_tK);return new T2(0,_tQ.a,_tQ.b);}else{var _tR=quotRemI(_tJ+1|0,_tK);return new T2(0,_tR.a-1|0,(_tR.b+_tK|0)-1|0);}}}else{if(_tK>=0){if(_tJ>=0){var _tS=quotRemI(_tJ,_tK);return new T2(0,_tS.a,_tS.b);}else{if(_tK<=0){var _tT=quotRemI(_tJ,_tK);return new T2(0,_tT.a,_tT.b);}else{var _tU=quotRemI(_tJ+1|0,_tK);return new T2(0,_tU.a-1|0,(_tU.b+_tK|0)-1|0);}}}else{var _tV=quotRemI(_tJ-1|0,_tK);return new T2(0,_tV.a-1|0,(_tV.b+_tK|0)+1|0);}}}},_tW=function(_tX,_tY){var _tZ=_tX%_tY;if(_tX<=0){if(_tX>=0){return E(_tZ);}else{if(_tY<=0){return E(_tZ);}else{var _u0=E(_tZ);return (_u0==0)?0:_u0+_tY|0;}}}else{if(_tY>=0){if(_tX>=0){return E(_tZ);}else{if(_tY<=0){return E(_tZ);}else{var _u1=E(_tZ);return (_u1==0)?0:_u1+_tY|0;}}}else{var _u2=E(_tZ);return (_u2==0)?0:_u2+_tY|0;}}},_u3=function(_u4,_u5){var _u6=E(_u5);switch(_u6){case -1:return E(_tE);case 0:return E(_4t);default:return new F(function(){return _tW(E(_u4),_u6);});}},_u7=function(_u8,_u9){var _ua=E(_u8),_ub=E(_u9);switch(_ub){case -1:var _uc=E(_ua);if(_uc==(-2147483648)){return E(_tv);}else{return new F(function(){return quot(_uc,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_ua,_ub);});}},_ud=function(_ue,_uf){var _ug=E(_ue),_uh=E(_uf);switch(_uh){case -1:var _ui=E(_ug);if(_ui==(-2147483648)){return E(_tF);}else{var _uj=quotRemI(_ui,-1);return new T2(0,_uj.a,_uj.b);}break;case 0:return E(_4t);default:var _uk=quotRemI(_ug,_uh);return new T2(0,_uk.a,_uk.b);}},_ul=function(_um,_un){var _uo=E(_un);switch(_uo){case -1:return E(_tE);case 0:return E(_4t);default:return E(_um)%_uo;}},_up=function(_uq){return new F(function(){return _ru(E(_uq));});},_ur=function(_us){return new T2(0,E(B(_ru(E(_us)))),E(_nk));},_ut=function(_uu,_uv){return imul(E(_uu),E(_uv))|0;},_uw=function(_ux,_uy){return E(_ux)+E(_uy)|0;},_uz=function(_uA,_uB){return E(_uA)-E(_uB)|0;},_uC=function(_uD){var _uE=E(_uD);return (_uE<0)? -_uE:E(_uE);},_uF=function(_uG){return new F(function(){return _4G(_uG);});},_uH=function(_uI){return  -E(_uI);},_uJ=-1,_uK=0,_uL=1,_uM=function(_uN){var _uO=E(_uN);return (_uO>=0)?(E(_uO)==0)?E(_uK):E(_uL):E(_uJ);},_uP={_:0,a:_uw,b:_uz,c:_ut,d:_uH,e:_uC,f:_uM,g:_uF},_uQ=function(_uR,_uS){return E(_uR)==E(_uS);},_uT=function(_uU,_uV){return E(_uU)!=E(_uV);},_uW=new T2(0,_uQ,_uT),_uX=function(_uY,_uZ){var _v0=E(_uY),_v1=E(_uZ);return (_v0>_v1)?E(_v0):E(_v1);},_v2=function(_v3,_v4){var _v5=E(_v3),_v6=E(_v4);return (_v5>_v6)?E(_v6):E(_v5);},_v7=function(_v8,_v9){return (_v8>=_v9)?(_v8!=_v9)?2:1:0;},_va=function(_vb,_vc){return new F(function(){return _v7(E(_vb),E(_vc));});},_vd=function(_ve,_vf){return E(_ve)>=E(_vf);},_vg=function(_vh,_vi){return E(_vh)>E(_vi);},_vj=function(_vk,_vl){return E(_vk)<=E(_vl);},_vm=function(_vn,_vo){return E(_vn)<E(_vo);},_vp={_:0,a:_uW,b:_va,c:_vm,d:_vj,e:_vg,f:_vd,g:_uX,h:_v2},_vq=new T3(0,_uP,_vp,_ur),_vr={_:0,a:_vq,b:_tp,c:_u7,d:_ul,e:_tB,f:_u3,g:_ud,h:_tG,i:_up},_vs=new T1(0,2),_vt=function(_vu,_vv){while(1){var _vw=E(_vu);if(!_vw._){var _vx=_vw.a,_vy=E(_vv);if(!_vy._){var _vz=_vy.a;if(!(imul(_vx,_vz)|0)){return new T1(0,imul(_vx,_vz)|0);}else{_vu=new T1(1,I_fromInt(_vx));_vv=new T1(1,I_fromInt(_vz));continue;}}else{_vu=new T1(1,I_fromInt(_vx));_vv=_vy;continue;}}else{var _vA=E(_vv);if(!_vA._){_vu=_vw;_vv=new T1(1,I_fromInt(_vA.a));continue;}else{return new T1(1,I_mul(_vw.a,_vA.a));}}}},_vB=function(_vC,_vD,_vE){while(1){if(!(_vD%2)){var _vF=B(_vt(_vC,_vC)),_vG=quot(_vD,2);_vC=_vF;_vD=_vG;continue;}else{var _vH=E(_vD);if(_vH==1){return new F(function(){return _vt(_vC,_vE);});}else{var _vF=B(_vt(_vC,_vC)),_vI=B(_vt(_vC,_vE));_vC=_vF;_vD=quot(_vH-1|0,2);_vE=_vI;continue;}}}},_vJ=function(_vK,_vL){while(1){if(!(_vL%2)){var _vM=B(_vt(_vK,_vK)),_vN=quot(_vL,2);_vK=_vM;_vL=_vN;continue;}else{var _vO=E(_vL);if(_vO==1){return E(_vK);}else{return new F(function(){return _vB(B(_vt(_vK,_vK)),quot(_vO-1|0,2),_vK);});}}}},_vP=function(_vQ){return E(E(_vQ).b);},_vR=function(_vS){return E(E(_vS).c);},_vT=new T1(0,0),_vU=function(_vV){return E(E(_vV).d);},_vW=function(_vX,_vY){var _vZ=B(_sv(_vX)),_w0=new T(function(){return B(_sx(_vZ));}),_w1=new T(function(){return B(A3(_vU,_vX,_vY,new T(function(){return B(A2(_8I,_w0,_nu));})));});return new F(function(){return A3(_mf,B(_m1(B(_vP(_vZ)))),_w1,new T(function(){return B(A2(_8I,_w0,_vT));}));});},_w2=new T(function(){return B(unCStr("Negative exponent"));}),_w3=new T(function(){return B(err(_w2));}),_w4=function(_w5){return E(E(_w5).c);},_w6=function(_w7,_w8,_w9,_wa){var _wb=B(_sv(_w8)),_wc=new T(function(){return B(_sx(_wb));}),_wd=B(_vP(_wb));if(!B(A3(_vR,_wd,_wa,new T(function(){return B(A2(_8I,_wc,_vT));})))){if(!B(A3(_mf,B(_m1(_wd)),_wa,new T(function(){return B(A2(_8I,_wc,_vT));})))){var _we=new T(function(){return B(A2(_8I,_wc,_nu));}),_wf=new T(function(){return B(A2(_8I,_wc,_nk));}),_wg=B(_m1(_wd)),_wh=function(_wi,_wj,_wk){while(1){var _wl=B((function(_wm,_wn,_wo){if(!B(_vW(_w8,_wn))){if(!B(A3(_mf,_wg,_wn,_wf))){var _wp=new T(function(){return B(A3(_w4,_w8,new T(function(){return B(A3(_8G,_wc,_wn,_wf));}),_we));});_wi=new T(function(){return B(A3(_8u,_w7,_wm,_wm));});_wj=_wp;_wk=new T(function(){return B(A3(_8u,_w7,_wm,_wo));});return __continue;}else{return new F(function(){return A3(_8u,_w7,_wm,_wo);});}}else{var _wq=_wo;_wi=new T(function(){return B(A3(_8u,_w7,_wm,_wm));});_wj=new T(function(){return B(A3(_w4,_w8,_wn,_we));});_wk=_wq;return __continue;}})(_wi,_wj,_wk));if(_wl!=__continue){return _wl;}}},_wr=function(_ws,_wt){while(1){var _wu=B((function(_wv,_ww){if(!B(_vW(_w8,_ww))){if(!B(A3(_mf,_wg,_ww,_wf))){var _wx=new T(function(){return B(A3(_w4,_w8,new T(function(){return B(A3(_8G,_wc,_ww,_wf));}),_we));});return new F(function(){return _wh(new T(function(){return B(A3(_8u,_w7,_wv,_wv));}),_wx,_wv);});}else{return E(_wv);}}else{_ws=new T(function(){return B(A3(_8u,_w7,_wv,_wv));});_wt=new T(function(){return B(A3(_w4,_w8,_ww,_we));});return __continue;}})(_ws,_wt));if(_wu!=__continue){return _wu;}}};return new F(function(){return _wr(_w9,_wa);});}else{return new F(function(){return A2(_8I,_w7,_nk);});}}else{return E(_w3);}},_wy=new T(function(){return B(err(_w2));}),_wz=function(_wA,_wB){var _wC=B(_rr(_wB)),_wD=_wC.a,_wE=_wC.b,_wF=new T(function(){return B(_sx(new T(function(){return B(_sv(_wA));})));});if(_wE<0){var _wG= -_wE;if(_wG>=0){var _wH=E(_wG);if(!_wH){var _wI=E(_nk);}else{var _wI=B(_vJ(_vs,_wH));}if(!B(_4y(_wI,_51))){var _wJ=B(_4S(_wD,_wI));return new T2(0,new T(function(){return B(A2(_8I,_wF,_wJ.a));}),new T(function(){return B(_4u(_wJ.b,_wE));}));}else{return E(_4t);}}else{return E(_wy);}}else{var _wK=new T(function(){var _wL=new T(function(){return B(_w6(_wF,_vr,new T(function(){return B(A2(_8I,_wF,_vs));}),_wE));});return B(A3(_8u,_wF,new T(function(){return B(A2(_8I,_wF,_wD));}),_wL));});return new T2(0,_wK,_7I);}},_wM=function(_wN,_wO){var _wP=B(_wz(_wN,E(_wO))),_wQ=_wP.a;if(E(_wP.b)<=0){return E(_wQ);}else{var _wR=B(_sx(B(_sv(_wN))));return new F(function(){return A3(_86,_wR,_wQ,new T(function(){return B(A2(_8I,_wR,_3k));}));});}},_wS=function(_wT,_wU){var _wV=B(_wz(_wT,E(_wU))),_wW=_wV.a;if(E(_wV.b)>=0){return E(_wW);}else{var _wX=B(_sx(B(_sv(_wT))));return new F(function(){return A3(_8G,_wX,_wW,new T(function(){return B(A2(_8I,_wX,_3k));}));});}},_wY=function(_wZ,_x0){var _x1=B(_wz(_wZ,E(_x0)));return new T2(0,_x1.a,_x1.b);},_x2=function(_x3,_x4){var _x5=B(_wz(_x3,_x4)),_x6=_x5.a,_x7=E(_x5.b),_x8=new T(function(){var _x9=B(_sx(B(_sv(_x3))));if(_x7>=0){return B(A3(_86,_x9,_x6,new T(function(){return B(A2(_8I,_x9,_3k));})));}else{return B(A3(_8G,_x9,_x6,new T(function(){return B(A2(_8I,_x9,_3k));})));}}),_xa=function(_xb){var _xc=_xb-0.5;return (_xc>=0)?(E(_xc)==0)?(!B(_vW(_x3,_x6)))?E(_x8):E(_x6):E(_x8):E(_x6);},_xd=E(_x7);if(!_xd){return new F(function(){return _xa(0);});}else{if(_xd<=0){var _xe= -_xd-0.5;return (_xe>=0)?(E(_xe)==0)?(!B(_vW(_x3,_x6)))?E(_x8):E(_x6):E(_x8):E(_x6);}else{return new F(function(){return _xa(_xd);});}}},_xf=function(_xg,_xh){return new F(function(){return _x2(_xg,E(_xh));});},_xi=function(_xj,_xk){return E(B(_wz(_xj,E(_xk))).a);},_xl={_:0,a:_su,b:_jp,c:_wY,d:_xi,e:_xf,f:_wM,g:_wS},_xm=new T1(0,1),_xn=function(_xo,_xp){var _xq=E(_xo);return new T2(0,_xq,new T(function(){var _xr=B(_xn(B(_4J(_xq,_xp)),_xp));return new T2(1,_xr.a,_xr.b);}));},_xs=function(_xt){var _xu=B(_xn(_xt,_xm));return new T2(1,_xu.a,_xu.b);},_xv=function(_xw,_xx){var _xy=B(_xn(_xw,new T(function(){return B(_6W(_xx,_xw));})));return new T2(1,_xy.a,_xy.b);},_xz=new T1(0,0),_xA=function(_xB,_xC){var _xD=E(_xB);if(!_xD._){var _xE=_xD.a,_xF=E(_xC);return (_xF._==0)?_xE>=_xF.a:I_compareInt(_xF.a,_xE)<=0;}else{var _xG=_xD.a,_xH=E(_xC);return (_xH._==0)?I_compareInt(_xG,_xH.a)>=0:I_compare(_xG,_xH.a)>=0;}},_xI=function(_xJ,_xK,_xL){if(!B(_xA(_xK,_xz))){var _xM=function(_xN){return (!B(_S(_xN,_xL)))?new T2(1,_xN,new T(function(){return B(_xM(B(_4J(_xN,_xK))));})):__Z;};return new F(function(){return _xM(_xJ);});}else{var _xO=function(_xP){return (!B(_5c(_xP,_xL)))?new T2(1,_xP,new T(function(){return B(_xO(B(_4J(_xP,_xK))));})):__Z;};return new F(function(){return _xO(_xJ);});}},_xQ=function(_xR,_xS,_xT){return new F(function(){return _xI(_xR,B(_6W(_xS,_xR)),_xT);});},_xU=function(_xV,_xW){return new F(function(){return _xI(_xV,_xm,_xW);});},_xX=function(_xY){return new F(function(){return _4G(_xY);});},_xZ=function(_y0){return new F(function(){return _6W(_y0,_xm);});},_y1=function(_y2){return new F(function(){return _4J(_y2,_xm);});},_y3=function(_y4){return new F(function(){return _ru(E(_y4));});},_y5={_:0,a:_y1,b:_xZ,c:_y3,d:_xX,e:_xs,f:_xv,g:_xU,h:_xQ},_y6=function(_y7,_y8){while(1){var _y9=E(_y7);if(!_y9._){var _ya=E(_y9.a);if(_ya==(-2147483648)){_y7=new T1(1,I_fromInt(-2147483648));continue;}else{var _yb=E(_y8);if(!_yb._){return new T1(0,B(_tq(_ya,_yb.a)));}else{_y7=new T1(1,I_fromInt(_ya));_y8=_yb;continue;}}}else{var _yc=_y9.a,_yd=E(_y8);return (_yd._==0)?new T1(1,I_div(_yc,I_fromInt(_yd.a))):new T1(1,I_div(_yc,_yd.a));}}},_ye=function(_yf,_yg){if(!B(_4y(_yg,_vT))){return new F(function(){return _y6(_yf,_yg);});}else{return E(_4t);}},_yh=function(_yi,_yj){while(1){var _yk=E(_yi);if(!_yk._){var _yl=E(_yk.a);if(_yl==(-2147483648)){_yi=new T1(1,I_fromInt(-2147483648));continue;}else{var _ym=E(_yj);if(!_ym._){var _yn=_ym.a;return new T2(0,new T1(0,B(_tq(_yl,_yn))),new T1(0,B(_tW(_yl,_yn))));}else{_yi=new T1(1,I_fromInt(_yl));_yj=_ym;continue;}}}else{var _yo=E(_yj);if(!_yo._){_yi=_yk;_yj=new T1(1,I_fromInt(_yo.a));continue;}else{var _yp=I_divMod(_yk.a,_yo.a);return new T2(0,new T1(1,_yp.a),new T1(1,_yp.b));}}}},_yq=function(_yr,_ys){if(!B(_4y(_ys,_vT))){var _yt=B(_yh(_yr,_ys));return new T2(0,_yt.a,_yt.b);}else{return E(_4t);}},_yu=function(_yv,_yw){while(1){var _yx=E(_yv);if(!_yx._){var _yy=E(_yx.a);if(_yy==(-2147483648)){_yv=new T1(1,I_fromInt(-2147483648));continue;}else{var _yz=E(_yw);if(!_yz._){return new T1(0,B(_tW(_yy,_yz.a)));}else{_yv=new T1(1,I_fromInt(_yy));_yw=_yz;continue;}}}else{var _yA=_yx.a,_yB=E(_yw);return (_yB._==0)?new T1(1,I_mod(_yA,I_fromInt(_yB.a))):new T1(1,I_mod(_yA,_yB.a));}}},_yC=function(_yD,_yE){if(!B(_4y(_yE,_vT))){return new F(function(){return _yu(_yD,_yE);});}else{return E(_4t);}},_yF=function(_yG,_yH){while(1){var _yI=E(_yG);if(!_yI._){var _yJ=E(_yI.a);if(_yJ==(-2147483648)){_yG=new T1(1,I_fromInt(-2147483648));continue;}else{var _yK=E(_yH);if(!_yK._){return new T1(0,quot(_yJ,_yK.a));}else{_yG=new T1(1,I_fromInt(_yJ));_yH=_yK;continue;}}}else{var _yL=_yI.a,_yM=E(_yH);return (_yM._==0)?new T1(0,I_toInt(I_quot(_yL,I_fromInt(_yM.a)))):new T1(1,I_quot(_yL,_yM.a));}}},_yN=function(_yO,_yP){if(!B(_4y(_yP,_vT))){return new F(function(){return _yF(_yO,_yP);});}else{return E(_4t);}},_yQ=function(_yR,_yS){if(!B(_4y(_yS,_vT))){var _yT=B(_4S(_yR,_yS));return new T2(0,_yT.a,_yT.b);}else{return E(_4t);}},_yU=function(_yV,_yW){while(1){var _yX=E(_yV);if(!_yX._){var _yY=E(_yX.a);if(_yY==(-2147483648)){_yV=new T1(1,I_fromInt(-2147483648));continue;}else{var _yZ=E(_yW);if(!_yZ._){return new T1(0,_yY%_yZ.a);}else{_yV=new T1(1,I_fromInt(_yY));_yW=_yZ;continue;}}}else{var _z0=_yX.a,_z1=E(_yW);return (_z1._==0)?new T1(1,I_rem(_z0,I_fromInt(_z1.a))):new T1(1,I_rem(_z0,_z1.a));}}},_z2=function(_z3,_z4){if(!B(_4y(_z4,_vT))){return new F(function(){return _yU(_z3,_z4);});}else{return E(_4t);}},_z5=function(_z6){return E(_z6);},_z7=function(_z8){return E(_z8);},_z9=function(_za){var _zb=E(_za);if(!_zb._){var _zc=E(_zb.a);return (_zc==(-2147483648))?E(_7A):(_zc<0)?new T1(0, -_zc):E(_zb);}else{var _zd=_zb.a;return (I_compareInt(_zd,0)>=0)?E(_zb):new T1(1,I_negate(_zd));}},_ze=new T1(0,0),_zf=new T1(0,-1),_zg=function(_zh){var _zi=E(_zh);if(!_zi._){var _zj=_zi.a;return (_zj>=0)?(E(_zj)==0)?E(_ze):E(_5k):E(_zf);}else{var _zk=I_compareInt(_zi.a,0);return (_zk<=0)?(E(_zk)==0)?E(_ze):E(_zf):E(_5k);}},_zl={_:0,a:_4J,b:_6W,c:_vt,d:_7B,e:_z9,f:_zg,g:_z7},_zm=function(_zn,_zo){var _zp=E(_zn);if(!_zp._){var _zq=_zp.a,_zr=E(_zo);return (_zr._==0)?_zq!=_zr.a:(I_compareInt(_zr.a,_zq)==0)?false:true;}else{var _zs=_zp.a,_zt=E(_zo);return (_zt._==0)?(I_compareInt(_zs,_zt.a)==0)?false:true:(I_compare(_zs,_zt.a)==0)?false:true;}},_zu=new T2(0,_4y,_zm),_zv=function(_zw,_zx){return (!B(_6H(_zw,_zx)))?E(_zw):E(_zx);},_zy=function(_zz,_zA){return (!B(_6H(_zz,_zA)))?E(_zA):E(_zz);},_zB={_:0,a:_zu,b:_3l,c:_S,d:_6H,e:_5c,f:_xA,g:_zv,h:_zy},_zC=function(_zD){return new T2(0,E(_zD),E(_nk));},_zE=new T3(0,_zl,_zB,_zC),_zF={_:0,a:_zE,b:_y5,c:_yN,d:_z2,e:_ye,f:_yC,g:_yQ,h:_yq,i:_z5},_zG=function(_zH){return E(E(_zH).b);},_zI=function(_zJ){return E(E(_zJ).g);},_zK=new T1(0,1),_zL=function(_zM,_zN,_zO){var _zP=B(_zG(_zM)),_zQ=B(_8s(_zP)),_zR=new T(function(){var _zS=new T(function(){var _zT=new T(function(){var _zU=new T(function(){return B(A3(_zI,_zM,_zF,new T(function(){return B(A3(_a8,_zP,_zN,_zO));})));});return B(A2(_8I,_zQ,_zU));}),_zV=new T(function(){return B(A2(_88,_zQ,new T(function(){return B(A2(_8I,_zQ,_zK));})));});return B(A3(_8u,_zQ,_zV,_zT));});return B(A3(_8u,_zQ,_zS,_zO));});return new F(function(){return A3(_86,_zQ,_zN,_zR);});},_zW=1.5707963267948966,_zX=function(_zY){return 0.2/Math.cos(B(_zL(_xl,_zY,_zW))-0.7853981633974483);},_zZ=new T(function(){var _A0=B(_q4(_zX,1.2,_ro,_ro,_rn,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_A0.a),b:E(_rp),c:E(_in),d:E(_A0.d),e:E(_A0.e),f:E(_A0.f),g:E(_A0.g),h:_A0.h,i:_A0.i};}),_A1=0,_A2=0.3,_A3=function(_A4){return E(_A2);},_A5=new T(function(){var _A6=B(_q4(_A3,1.2,_rn,_ro,_rn,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_A6.a),b:E(_A6.b),c:E(_A6.c),d:E(_A6.d),e:E(_A6.e),f:E(_A6.f),g:E(_A6.g),h:_A6.h,i:_A6.i};}),_A7=new T(function(){var _A8=B(_q4(_A3,1.2,_rn,_rn,_ro,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_A8.a),b:E(_A8.b),c:E(_A8.c),d:E(_A8.d),e:E(_A8.e),f:E(_A8.f),g:E(_A8.g),h:_A8.h,i:_A8.i};}),_A9=2,_Aa=function(_Ab){return 0.3/Math.cos(B(_zL(_xl,_Ab,_zW))-0.7853981633974483);},_Ac=new T(function(){var _Ad=B(_q4(_Aa,1.2,_A9,_rn,_rn,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_Ad.a),b:E(_Ad.b),c:E(_Ad.c),d:E(_Ad.d),e:E(_Ad.e),f:E(_Ad.f),g:E(_Ad.g),h:_Ad.h,i:_Ad.i};}),_Ae=0.5,_Af=new T(function(){var _Ag=B(_q4(_A3,1.2,_ro,_rn,_Ae,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_Ag.a),b:E(_Ag.b),c:E(_Ag.c),d:E(_Ag.d),e:E(_Ag.e),f:E(_Ag.f),g:E(_Ag.g),h:_Ag.h,i:_Ag.i};}),_Ah=new T2(1,_Af,_w),_Ai=new T2(1,_Ac,_Ah),_Aj=new T2(1,_A7,_Ai),_Ak=new T2(1,_A5,_Aj),_Al=new T2(1,_zZ,_Ak),_Am=new T(function(){return B(unCStr("Negative range size"));}),_An=new T(function(){return B(err(_Am));}),_Ao=function(_){var _Ap=B(_ie(_Al,0))-1|0,_Aq=function(_Ar){if(_Ar>=0){var _As=newArr(_Ar,_ik),_At=_As,_Au=E(_Ar);if(!_Au){return new T4(0,E(_A1),E(_Ap),0,_At);}else{var _Av=function(_Aw,_Ax,_){while(1){var _Ay=E(_Aw);if(!_Ay._){return E(_);}else{var _=_At[_Ax]=_Ay.a;if(_Ax!=(_Au-1|0)){var _Az=_Ax+1|0;_Aw=_Ay.b;_Ax=_Az;continue;}else{return E(_);}}}},_=B((function(_AA,_AB,_AC,_){var _=_At[_AC]=_AA;if(_AC!=(_Au-1|0)){return new F(function(){return _Av(_AB,_AC+1|0,_);});}else{return E(_);}})(_zZ,_Ak,0,_));return new T4(0,E(_A1),E(_Ap),_Au,_At);}}else{return E(_An);}};if(0>_Ap){return new F(function(){return _Aq(0);});}else{return new F(function(){return _Aq(_Ap+1|0);});}},_AD=function(_AE){var _AF=B(A1(_AE,_));return E(_AF);},_AG=new T(function(){return B(_AD(_Ao));}),_AH="outline",_AI="polygon",_AJ=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_AK=new T(function(){return B(err(_AJ));}),_AL=new T(function(){return eval("__strict(drawObjects)");}),_AM=new T(function(){return eval("__strict(draw)");}),_AN=function(_AO,_AP){var _AQ=jsShowI(_AO);return new F(function(){return _n(fromJSStr(_AQ),_AP);});},_AR=function(_AS,_AT,_AU){if(_AT>=0){return new F(function(){return _AN(_AT,_AU);});}else{if(_AS<=6){return new F(function(){return _AN(_AT,_AU);});}else{return new T2(1,_11,new T(function(){var _AV=jsShowI(_AT);return B(_n(fromJSStr(_AV),new T2(1,_10,_AU)));}));}}},_AW=new T(function(){return B(unCStr(")"));}),_AX=function(_AY,_AZ){var _B0=new T(function(){var _B1=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AR(0,_AY,_w)),_AW));})));},1);return B(_n(B(_AR(0,_AZ,_w)),_B1));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B0)));});},_B2=new T2(1,_kC,_w),_B3=function(_B4){return E(_B4);},_B5=function(_B6){return E(_B6);},_B7=function(_B8,_B9){return E(_B9);},_Ba=function(_Bb,_Bc){return E(_Bb);},_Bd=function(_Be){return E(_Be);},_Bf=new T2(0,_Bd,_Ba),_Bg=function(_Bh,_Bi){return E(_Bh);},_Bj=new T5(0,_Bf,_B5,_B3,_B7,_Bg),_Bk="flipped2",_Bl="flipped1",_Bm="c1y",_Bn="c1x",_Bo="w2z",_Bp="w2y",_Bq="w2x",_Br="w1z",_Bs="w1y",_Bt="w1x",_Bu="d2z",_Bv="d2y",_Bw="d2x",_Bx="d1z",_By="d1y",_Bz="d1x",_BA="c2y",_BB="c2x",_BC=function(_BD,_){var _BE=__get(_BD,E(_Bt)),_BF=__get(_BD,E(_Bs)),_BG=__get(_BD,E(_Br)),_BH=__get(_BD,E(_Bq)),_BI=__get(_BD,E(_Bp)),_BJ=__get(_BD,E(_Bo)),_BK=__get(_BD,E(_Bn)),_BL=__get(_BD,E(_Bm)),_BM=__get(_BD,E(_BB)),_BN=__get(_BD,E(_BA)),_BO=__get(_BD,E(_Bz)),_BP=__get(_BD,E(_By)),_BQ=__get(_BD,E(_Bx)),_BR=__get(_BD,E(_Bw)),_BS=__get(_BD,E(_Bv)),_BT=__get(_BD,E(_Bu)),_BU=__get(_BD,E(_Bl)),_BV=__get(_BD,E(_Bk));return {_:0,a:E(new T3(0,E(_BE),E(_BF),E(_BG))),b:E(new T3(0,E(_BH),E(_BI),E(_BJ))),c:E(new T2(0,E(_BK),E(_BL))),d:E(new T2(0,E(_BM),E(_BN))),e:E(new T3(0,E(_BO),E(_BP),E(_BQ))),f:E(new T3(0,E(_BR),E(_BS),E(_BT))),g:E(_BU),h:E(_BV)};},_BW=function(_BX,_){var _BY=E(_BX);if(!_BY._){return _w;}else{var _BZ=B(_BC(E(_BY.a),_)),_C0=B(_BW(_BY.b,_));return new T2(1,_BZ,_C0);}},_C1=function(_C2){var _C3=E(_C2);return (E(_C3.b)-E(_C3.a)|0)+1|0;},_C4=function(_C5,_C6){var _C7=E(_C5),_C8=E(_C6);return (E(_C7.a)>_C8)?false:_C8<=E(_C7.b);},_C9=function(_Ca){return new F(function(){return _AR(0,E(_Ca),_w);});},_Cb=function(_Cc,_Cd,_Ce){return new F(function(){return _AR(E(_Cc),E(_Cd),_Ce);});},_Cf=function(_Cg,_Ch){return new F(function(){return _AR(0,E(_Cg),_Ch);});},_Ci=function(_Cj,_Ck){return new F(function(){return _49(_Cf,_Cj,_Ck);});},_Cl=new T3(0,_Cb,_C9,_Ci),_Cm=0,_Cn=function(_Co,_Cp,_Cq){return new F(function(){return A1(_Co,new T2(1,_46,new T(function(){return B(A1(_Cp,_Cq));})));});},_Cr=new T(function(){return B(unCStr("foldr1"));}),_Cs=new T(function(){return B(_mK(_Cr));}),_Ct=function(_Cu,_Cv){var _Cw=E(_Cv);if(!_Cw._){return E(_Cs);}else{var _Cx=_Cw.a,_Cy=E(_Cw.b);if(!_Cy._){return E(_Cx);}else{return new F(function(){return A2(_Cu,_Cx,new T(function(){return B(_Ct(_Cu,_Cy));}));});}}},_Cz=new T(function(){return B(unCStr(" out of range "));}),_CA=new T(function(){return B(unCStr("}.index: Index "));}),_CB=new T(function(){return B(unCStr("Ix{"));}),_CC=new T2(1,_10,_w),_CD=new T2(1,_10,_CC),_CE=0,_CF=function(_CG){return E(E(_CG).a);},_CH=function(_CI,_CJ,_CK,_CL,_CM){var _CN=new T(function(){var _CO=new T(function(){var _CP=new T(function(){var _CQ=new T(function(){var _CR=new T(function(){return B(A3(_Ct,_Cn,new T2(1,new T(function(){return B(A3(_CF,_CK,_CE,_CL));}),new T2(1,new T(function(){return B(A3(_CF,_CK,_CE,_CM));}),_w)),_CD));});return B(_n(_Cz,new T2(1,_11,new T2(1,_11,_CR))));});return B(A(_CF,[_CK,_Cm,_CJ,new T2(1,_10,_CQ)]));});return B(_n(_CA,new T2(1,_11,_CP)));},1);return B(_n(_CI,_CO));},1);return new F(function(){return err(B(_n(_CB,_CN)));});},_CS=function(_CT,_CU,_CV,_CW,_CX){return new F(function(){return _CH(_CT,_CU,_CX,_CV,_CW);});},_CY=function(_CZ,_D0,_D1,_D2){var _D3=E(_D1);return new F(function(){return _CS(_CZ,_D0,_D3.a,_D3.b,_D2);});},_D4=function(_D5,_D6,_D7,_D8){return new F(function(){return _CY(_D8,_D7,_D6,_D5);});},_D9=new T(function(){return B(unCStr("Int"));}),_Da=function(_Db,_Dc){return new F(function(){return _D4(_Cl,_Dc,_Db,_D9);});},_Dd=function(_De,_Df){var _Dg=E(_De),_Dh=E(_Dg.a),_Di=E(_Df);if(_Dh>_Di){return new F(function(){return _Da(_Di,_Dg);});}else{if(_Di>E(_Dg.b)){return new F(function(){return _Da(_Di,_Dg);});}else{return _Di-_Dh|0;}}},_Dj=function(_Dk){var _Dl=E(_Dk);return new F(function(){return _ta(_Dl.a,_Dl.b);});},_Dm=function(_Dn){var _Do=E(_Dn),_Dp=E(_Do.a),_Dq=E(_Do.b);return (_Dp>_Dq)?E(_Cm):(_Dq-_Dp|0)+1|0;},_Dr=function(_Ds,_Dt){return new F(function(){return _uz(_Dt,E(_Ds).a);});},_Du={_:0,a:_vp,b:_Dj,c:_Dd,d:_Dr,e:_C4,f:_Dm,g:_C1},_Dv=function(_Dw,_Dx,_){while(1){var _Dy=B((function(_Dz,_DA,_){var _DB=E(_Dz);if(!_DB._){return new T2(0,_kC,_DA);}else{var _DC=B(A2(_DB.a,_DA,_));_Dw=_DB.b;_Dx=new T(function(){return E(E(_DC).b);});return __continue;}})(_Dw,_Dx,_));if(_Dy!=__continue){return _Dy;}}},_DD=function(_DE,_DF){return new T2(1,_DE,_DF);},_DG=function(_DH,_DI){var _DJ=E(_DI);return new T2(0,_DJ.a,_DJ.b);},_DK=function(_DL){return E(E(_DL).f);},_DM=function(_DN,_DO,_DP){var _DQ=E(_DO),_DR=_DQ.a,_DS=_DQ.b,_DT=function(_){var _DU=B(A2(_DK,_DN,_DQ));if(_DU>=0){var _DV=newArr(_DU,_ik),_DW=_DV,_DX=E(_DU);if(!_DX){return new T(function(){return new T4(0,E(_DR),E(_DS),0,_DW);});}else{var _DY=function(_DZ,_E0,_){while(1){var _E1=E(_DZ);if(!_E1._){return E(_);}else{var _=_DW[_E0]=_E1.a;if(_E0!=(_DX-1|0)){var _E2=_E0+1|0;_DZ=_E1.b;_E0=_E2;continue;}else{return E(_);}}}},_=B(_DY(_DP,0,_));return new T(function(){return new T4(0,E(_DR),E(_DS),_DX,_DW);});}}else{return E(_An);}};return new F(function(){return _AD(_DT);});},_E3=function(_E4,_E5,_E6,_E7){var _E8=new T(function(){var _E9=E(_E7),_Ea=_E9.c-1|0,_Eb=new T(function(){return B(A2(_dT,_E5,_w));});if(0<=_Ea){var _Ec=new T(function(){return B(_a4(_E5));}),_Ed=function(_Ee){var _Ef=new T(function(){var _Eg=new T(function(){return B(A1(_E6,new T(function(){return E(_E9.d[_Ee]);})));});return B(A3(_ac,_Ec,_DD,_Eg));});return new F(function(){return A3(_aa,_E5,_Ef,new T(function(){if(_Ee!=_Ea){return B(_Ed(_Ee+1|0));}else{return E(_Eb);}}));});};return B(_Ed(0));}else{return E(_Eb);}}),_Eh=new T(function(){return B(_DG(_E4,_E7));});return new F(function(){return A3(_ac,B(_a4(_E5)),function(_Ei){return new F(function(){return _DM(_E4,_Eh,_Ei);});},_E8);});},_Ej=function(_Ek,_El,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es){var _Et=B(_8u(_Ek));return new T2(0,new T3(0,E(B(A1(B(A1(_Et,_El)),_Ep))),E(B(A1(B(A1(_Et,_Em)),_Eq))),E(B(A1(B(A1(_Et,_En)),_Er)))),B(A1(B(A1(_Et,_Eo)),_Es)));},_Eu=function(_Ev,_Ew,_Ex,_Ey,_Ez,_EA,_EB,_EC,_ED){var _EE=B(_86(_Ev));return new T2(0,new T3(0,E(B(A1(B(A1(_EE,_Ew)),_EA))),E(B(A1(B(A1(_EE,_Ex)),_EB))),E(B(A1(B(A1(_EE,_Ey)),_EC)))),B(A1(B(A1(_EE,_Ez)),_ED)));},_EF=1.0e-2,_EG=function(_EH,_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX){var _EY=B(_Ej(_jl,_EO,_EP,_EQ,_ER,_EF,_EF,_EF,_EF)),_EZ=E(_EY.a),_F0=B(_Eu(_jl,_EK,_EL,_EM,_EN,_EZ.a,_EZ.b,_EZ.c,_EY.b)),_F1=E(_F0.a);return new F(function(){return _pl(_EH,_EI,_EJ,_F1.a,_F1.b,_F1.c,_F0.b,_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX);});},_F2=function(_F3){var _F4=E(_F3),_F5=E(_F4.d),_F6=E(_F5.a),_F7=E(_F4.e),_F8=E(_F7.a),_F9=E(_F4.f),_Fa=B(_EG(_F4.a,_F4.b,_F4.c,_F6.a,_F6.b,_F6.c,_F5.b,_F8.a,_F8.b,_F8.c,_F7.b,_F9.a,_F9.b,_F9.c,_F4.g,_F4.h,_F4.i));return {_:0,a:E(_Fa.a),b:E(_Fa.b),c:E(_Fa.c),d:E(_Fa.d),e:E(_Fa.e),f:E(_Fa.f),g:E(_Fa.g),h:_Fa.h,i:_Fa.i};},_Fb=function(_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk){var _Fl=B(_8s(B(_8q(_Fc))));return new F(function(){return A3(_86,_Fl,new T(function(){return B(_8w(_Fc,_Fd,_Fe,_Ff,_Fh,_Fi,_Fj));}),new T(function(){return B(A3(_8u,_Fl,_Fg,_Fk));}));});},_Fm=new T(function(){return B(unCStr("base"));}),_Fn=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fo=new T(function(){return B(unCStr("IOException"));}),_Fp=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fm,_Fn,_Fo),_Fq=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fp,_w,_w),_Fr=function(_Fs){return E(_Fq);},_Ft=function(_Fu){var _Fv=E(_Fu);return new F(function(){return _3G(B(_3E(_Fv.a)),_Fr,_Fv.b);});},_Fw=new T(function(){return B(unCStr(": "));}),_Fx=new T(function(){return B(unCStr(")"));}),_Fy=new T(function(){return B(unCStr(" ("));}),_Fz=new T(function(){return B(unCStr("interrupted"));}),_FA=new T(function(){return B(unCStr("system error"));}),_FB=new T(function(){return B(unCStr("unsatisified constraints"));}),_FC=new T(function(){return B(unCStr("user error"));}),_FD=new T(function(){return B(unCStr("permission denied"));}),_FE=new T(function(){return B(unCStr("illegal operation"));}),_FF=new T(function(){return B(unCStr("end of file"));}),_FG=new T(function(){return B(unCStr("resource exhausted"));}),_FH=new T(function(){return B(unCStr("resource busy"));}),_FI=new T(function(){return B(unCStr("does not exist"));}),_FJ=new T(function(){return B(unCStr("already exists"));}),_FK=new T(function(){return B(unCStr("resource vanished"));}),_FL=new T(function(){return B(unCStr("timeout"));}),_FM=new T(function(){return B(unCStr("unsupported operation"));}),_FN=new T(function(){return B(unCStr("hardware fault"));}),_FO=new T(function(){return B(unCStr("inappropriate type"));}),_FP=new T(function(){return B(unCStr("invalid argument"));}),_FQ=new T(function(){return B(unCStr("failed"));}),_FR=new T(function(){return B(unCStr("protocol error"));}),_FS=function(_FT,_FU){switch(E(_FT)){case 0:return new F(function(){return _n(_FJ,_FU);});break;case 1:return new F(function(){return _n(_FI,_FU);});break;case 2:return new F(function(){return _n(_FH,_FU);});break;case 3:return new F(function(){return _n(_FG,_FU);});break;case 4:return new F(function(){return _n(_FF,_FU);});break;case 5:return new F(function(){return _n(_FE,_FU);});break;case 6:return new F(function(){return _n(_FD,_FU);});break;case 7:return new F(function(){return _n(_FC,_FU);});break;case 8:return new F(function(){return _n(_FB,_FU);});break;case 9:return new F(function(){return _n(_FA,_FU);});break;case 10:return new F(function(){return _n(_FR,_FU);});break;case 11:return new F(function(){return _n(_FQ,_FU);});break;case 12:return new F(function(){return _n(_FP,_FU);});break;case 13:return new F(function(){return _n(_FO,_FU);});break;case 14:return new F(function(){return _n(_FN,_FU);});break;case 15:return new F(function(){return _n(_FM,_FU);});break;case 16:return new F(function(){return _n(_FL,_FU);});break;case 17:return new F(function(){return _n(_FK,_FU);});break;default:return new F(function(){return _n(_Fz,_FU);});}},_FV=new T(function(){return B(unCStr("}"));}),_FW=new T(function(){return B(unCStr("{handle: "));}),_FX=function(_FY,_FZ,_G0,_G1,_G2,_G3){var _G4=new T(function(){var _G5=new T(function(){var _G6=new T(function(){var _G7=E(_G1);if(!_G7._){return E(_G3);}else{var _G8=new T(function(){return B(_n(_G7,new T(function(){return B(_n(_Fx,_G3));},1)));},1);return B(_n(_Fy,_G8));}},1);return B(_FS(_FZ,_G6));}),_G9=E(_G0);if(!_G9._){return E(_G5);}else{return B(_n(_G9,new T(function(){return B(_n(_Fw,_G5));},1)));}}),_Ga=E(_G2);if(!_Ga._){var _Gb=E(_FY);if(!_Gb._){return E(_G4);}else{var _Gc=E(_Gb.a);if(!_Gc._){var _Gd=new T(function(){var _Ge=new T(function(){return B(_n(_FV,new T(function(){return B(_n(_Fw,_G4));},1)));},1);return B(_n(_Gc.a,_Ge));},1);return new F(function(){return _n(_FW,_Gd);});}else{var _Gf=new T(function(){var _Gg=new T(function(){return B(_n(_FV,new T(function(){return B(_n(_Fw,_G4));},1)));},1);return B(_n(_Gc.a,_Gg));},1);return new F(function(){return _n(_FW,_Gf);});}}}else{return new F(function(){return _n(_Ga.a,new T(function(){return B(_n(_Fw,_G4));},1));});}},_Gh=function(_Gi){var _Gj=E(_Gi);return new F(function(){return _FX(_Gj.a,_Gj.b,_Gj.c,_Gj.d,_Gj.f,_w);});},_Gk=function(_Gl,_Gm,_Gn){var _Go=E(_Gm);return new F(function(){return _FX(_Go.a,_Go.b,_Go.c,_Go.d,_Go.f,_Gn);});},_Gp=function(_Gq,_Gr){var _Gs=E(_Gq);return new F(function(){return _FX(_Gs.a,_Gs.b,_Gs.c,_Gs.d,_Gs.f,_Gr);});},_Gt=function(_Gu,_Gv){return new F(function(){return _49(_Gp,_Gu,_Gv);});},_Gw=new T3(0,_Gk,_Gh,_Gt),_Gx=new T(function(){return new T5(0,_Fr,_Gw,_Gy,_Ft,_Gh);}),_Gy=function(_Gz){return new T2(0,_Gx,_Gz);},_GA=__Z,_GB=7,_GC=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_GD=new T6(0,_GA,_GB,_w,_GC,_GA,_GA),_GE=new T(function(){return B(_Gy(_GD));}),_GF=function(_){return new F(function(){return die(_GE);});},_GG=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_GH=new T6(0,_GA,_GB,_w,_GG,_GA,_GA),_GI=new T(function(){return B(_Gy(_GH));}),_GJ=function(_){return new F(function(){return die(_GI);});},_GK=function(_GL,_){return new T2(0,_w,_GL);},_GM=0.6,_GN=1,_GO=new T(function(){return B(unCStr(")"));}),_GP=function(_GQ,_GR){var _GS=new T(function(){var _GT=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AR(0,_GQ,_w)),_GO));})));},1);return B(_n(B(_AR(0,_GR,_w)),_GT));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GS)));});},_GU=function(_GV,_GW){var _GX=new T(function(){var _GY=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AR(0,_GW,_w)),_GO));})));},1);return B(_n(B(_AR(0,_GV,_w)),_GY));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GX)));});},_GZ=function(_H0){var _H1=E(_H0);if(!_H1._){return E(_GK);}else{var _H2=new T(function(){return B(_GZ(_H1.b));}),_H3=function(_H4){var _H5=E(_H4);if(!_H5._){return E(_H2);}else{var _H6=_H5.a,_H7=new T(function(){return B(_H3(_H5.b));}),_H8=new T(function(){return 0.1*E(E(_H6).e)/1.0e-2;}),_H9=new T(function(){var _Ha=E(_H6);if(_Ha.a!=_Ha.b){return E(_GN);}else{return E(_GM);}}),_Hb=function(_Hc,_){var _Hd=E(_Hc),_He=_Hd.c,_Hf=_Hd.d,_Hg=E(_Hd.a),_Hh=E(_Hd.b),_Hi=E(_H6),_Hj=_Hi.a,_Hk=_Hi.b,_Hl=E(_Hi.c),_Hm=_Hl.b,_Hn=E(_Hl.a),_Ho=_Hn.a,_Hp=_Hn.b,_Hq=_Hn.c,_Hr=E(_Hi.d),_Hs=_Hr.b,_Ht=E(_Hr.a),_Hu=_Ht.a,_Hv=_Ht.b,_Hw=_Ht.c;if(_Hg>_Hj){return new F(function(){return _GJ(_);});}else{if(_Hj>_Hh){return new F(function(){return _GJ(_);});}else{if(_Hg>_Hk){return new F(function(){return _GF(_);});}else{if(_Hk>_Hh){return new F(function(){return _GF(_);});}else{var _Hx=_Hj-_Hg|0;if(0>_Hx){return new F(function(){return _GP(_He,_Hx);});}else{if(_Hx>=_He){return new F(function(){return _GP(_He,_Hx);});}else{var _Hy=E(_Hf[_Hx]),_Hz=E(_Hy.c),_HA=_Hz.b,_HB=E(_Hz.a),_HC=_HB.a,_HD=_HB.b,_HE=_HB.c,_HF=E(_Hy.e),_HG=E(_HF.a),_HH=B(_Ej(_jl,_Ho,_Hp,_Hq,_Hm,_HC,_HD,_HE,_HA)),_HI=E(_HH.a),_HJ=B(_Ej(_jl,_HI.a,_HI.b,_HI.c,_HH.b,_Ho,_Hp,_Hq,_Hm)),_HK=E(_HJ.a),_HL=_Hk-_Hg|0;if(0>_HL){return new F(function(){return _GU(_HL,_He);});}else{if(_HL>=_He){return new F(function(){return _GU(_HL,_He);});}else{var _HM=E(_Hf[_HL]),_HN=E(_HM.c),_HO=_HN.b,_HP=E(_HN.a),_HQ=_HP.a,_HR=_HP.b,_HS=_HP.c,_HT=E(_HM.e),_HU=E(_HT.a),_HV=B(_Ej(_jl,_Hu,_Hv,_Hw,_Hs,_HQ,_HR,_HS,_HO)),_HW=E(_HV.a),_HX=B(_Ej(_jl,_HW.a,_HW.b,_HW.c,_HV.b,_Hu,_Hv,_Hw,_Hs)),_HY=E(_HX.a),_HZ=E(_HK.a)+E(_HK.b)+E(_HK.c)+E(_HJ.b)+E(_HY.a)+E(_HY.b)+E(_HY.c)+E(_HX.b);if(!_HZ){var _I0=B(A2(_H7,_Hd,_));return new T2(0,new T2(1,_kC,new T(function(){return E(E(_I0).a);})),new T(function(){return E(E(_I0).b);}));}else{var _I1=new T(function(){return  -((B(_Fb(_jR,_HG.a,_HG.b,_HG.c,_HF.b,_Ho,_Hp,_Hq,_Hm))-B(_Fb(_jR,_HU.a,_HU.b,_HU.c,_HT.b,_Hu,_Hv,_Hw,_Hs))-E(_H8))/_HZ);}),_I2=function(_I3,_I4,_I5,_I6,_){var _I7=new T(function(){var _I8=function(_I9,_Ia,_Ib,_Ic,_Id){if(_I9>_Hk){return E(_Id);}else{if(_Hk>_Ia){return E(_Id);}else{var _Ie=function(_){var _If=newArr(_Ib,_ik),_Ig=_If,_Ih=function(_Ii,_){while(1){if(_Ii!=_Ib){var _=_Ig[_Ii]=_Ic[_Ii],_Ij=_Ii+1|0;_Ii=_Ij;continue;}else{return E(_);}}},_=B(_Ih(0,_)),_Ik=_Hk-_I9|0;if(0>_Ik){return new F(function(){return _GU(_Ik,_Ib);});}else{if(_Ik>=_Ib){return new F(function(){return _GU(_Ik,_Ib);});}else{var _=_Ig[_Ik]=new T(function(){var _Il=E(_Ic[_Ik]),_Im=E(_Il.e),_In=E(_Im.a),_Io=B(_Ej(_jl,_HQ,_HR,_HS,_HO,_Hu,_Hv,_Hw,_Hs)),_Ip=E(_Io.a),_Iq=E(_I1)*E(_H9),_Ir=B(_Ej(_jl,_Ip.a,_Ip.b,_Ip.c,_Io.b,_Iq,_Iq,_Iq,_Iq)),_Is=E(_Ir.a),_It=B(_Eu(_jl,_In.a,_In.b,_In.c,_Im.b, -E(_Is.a), -E(_Is.b), -E(_Is.c), -E(_Ir.b)));return {_:0,a:E(_Il.a),b:E(_Il.b),c:E(_Il.c),d:E(_Il.d),e:E(new T2(0,E(_It.a),E(_It.b))),f:E(_Il.f),g:E(_Il.g),h:_Il.h,i:_Il.i};});return new T4(0,E(_I9),E(_Ia),_Ib,_Ig);}}};return new F(function(){return _AD(_Ie);});}}};if(_I3>_Hj){return B(_I8(_I3,_I4,_I5,_I6,new T4(0,E(_I3),E(_I4),_I5,_I6)));}else{if(_Hj>_I4){return B(_I8(_I3,_I4,_I5,_I6,new T4(0,E(_I3),E(_I4),_I5,_I6)));}else{var _Iu=function(_){var _Iv=newArr(_I5,_ik),_Iw=_Iv,_Ix=function(_Iy,_){while(1){if(_Iy!=_I5){var _=_Iw[_Iy]=_I6[_Iy],_Iz=_Iy+1|0;_Iy=_Iz;continue;}else{return E(_);}}},_=B(_Ix(0,_)),_IA=_Hj-_I3|0;if(0>_IA){return new F(function(){return _GP(_I5,_IA);});}else{if(_IA>=_I5){return new F(function(){return _GP(_I5,_IA);});}else{var _=_Iw[_IA]=new T(function(){var _IB=E(_I6[_IA]),_IC=E(_IB.e),_ID=E(_IC.a),_IE=B(_Ej(_jl,_HC,_HD,_HE,_HA,_Ho,_Hp,_Hq,_Hm)),_IF=E(_IE.a),_IG=E(_I1)*E(_H9),_IH=B(_Ej(_jl,_IF.a,_IF.b,_IF.c,_IE.b,_IG,_IG,_IG,_IG)),_II=E(_IH.a),_IJ=B(_Eu(_jl,_ID.a,_ID.b,_ID.c,_IC.b,_II.a,_II.b,_II.c,_IH.b));return {_:0,a:E(_IB.a),b:E(_IB.b),c:E(_IB.c),d:E(_IB.d),e:E(new T2(0,E(_IJ.a),E(_IJ.b))),f:E(_IB.f),g:E(_IB.g),h:_IB.h,i:_IB.i};});return new T4(0,E(_I3),E(_I4),_I5,_Iw);}}},_IK=B(_AD(_Iu));return B(_I8(E(_IK.a),E(_IK.b),_IK.c,_IK.d,_IK));}}});return new T2(0,_kC,_I7);};if(!E(_Hi.f)){var _IL=B(_I2(_Hg,_Hh,_He,_Hf,_)),_IM=B(A2(_H7,new T(function(){return E(E(_IL).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IL).a);}),new T(function(){return E(E(_IM).a);})),new T(function(){return E(E(_IM).b);}));}else{if(E(_I1)<0){var _IN=B(A2(_H7,_Hd,_));return new T2(0,new T2(1,_kC,new T(function(){return E(E(_IN).a);})),new T(function(){return E(E(_IN).b);}));}else{var _IO=B(_I2(_Hg,_Hh,_He,_Hf,_)),_IP=B(A2(_H7,new T(function(){return E(E(_IO).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IO).a);}),new T(function(){return E(E(_IP).a);})),new T(function(){return E(E(_IP).b);}));}}}}}}}}}}}};return E(_Hb);}};return new F(function(){return _H3(_H1.a);});}},_IQ=function(_,_IR){var _IS=new T(function(){return B(_GZ(E(_IR).a));}),_IT=function(_IU){var _IV=E(_IU);return (_IV==1)?E(new T2(1,_IS,_w)):new T2(1,_IS,new T(function(){return B(_IT(_IV-1|0));}));},_IW=B(_Dv(B(_IT(5)),new T(function(){return E(E(_IR).b);}),_)),_IX=new T(function(){return B(_E3(_Du,_Bj,_F2,new T(function(){return E(E(_IW).b);})));});return new T2(0,_kC,_IX);},_IY=function(_IZ,_J0,_J1,_J2,_J3){var _J4=B(_8s(B(_8q(_IZ))));return new F(function(){return A3(_86,_J4,new T(function(){return B(A3(_8u,_J4,_J0,_J2));}),new T(function(){return B(A3(_8u,_J4,_J1,_J3));}));});},_J5=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_J6=new T6(0,_GA,_GB,_w,_J5,_GA,_GA),_J7=new T(function(){return B(_Gy(_J6));}),_J8=function(_){return new F(function(){return die(_J7);});},_J9=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Ja=new T6(0,_GA,_GB,_w,_J9,_GA,_GA),_Jb=new T(function(){return B(_Gy(_Ja));}),_Jc=function(_){return new F(function(){return die(_Jb);});},_Jd=false,_Je=true,_Jf=function(_Jg){var _Jh=E(_Jg),_Ji=_Jh.b,_Jj=E(_Jh.d),_Jk=E(_Jh.e),_Jl=E(_Jk.a),_Jm=E(_Jh.g),_Jn=B(A1(_Ji,_Jj.a)),_Jo=B(_m3(_jR,_Jn.a,_Jn.b,_Jn.c,_Jm.a,_Jm.b,_Jm.c));return {_:0,a:E(_Jh.a),b:E(_Ji),c:E(_Jh.c),d:E(_Jj),e:E(new T2(0,E(new T3(0,E(_Jl.a)+E(_Jo.a)*1.0e-2,E(_Jl.b)+E(_Jo.b)*1.0e-2,E(_Jl.c)+E(_Jo.c)*1.0e-2)),E(_Jk.b))),f:E(_Jh.f),g:E(_Jm),h:_Jh.h,i:_Jh.i};},_Jp=new T(function(){return eval("__strict(collideBound)");}),_Jq=new T(function(){return eval("__strict(mouseContact)");}),_Jr=new T(function(){return eval("__strict(collide)");}),_Js=function(_Jt){var _Ju=E(_Jt);if(!_Ju._){return __Z;}else{return new F(function(){return _n(_Ju.a,new T(function(){return B(_Js(_Ju.b));},1));});}},_Jv=0,_Jw=new T3(0,E(_Jv),E(_Jv),E(_Jv)),_Jx=new T2(0,E(_Jw),E(_Jv)),_Jy=new T2(0,_jR,_kq),_Jz=new T(function(){return B(_hQ(_Jy));}),_JA=function(_JB,_){var _JC=B(_E3(_Du,_Bj,_Jf,_JB)),_JD=E(_JC.a),_JE=E(_JC.b);if(_JD<=_JE){var _JF=function(_JG,_JH,_JI,_JJ,_JK,_){if(_JH>_JG){return new F(function(){return _Jc(_);});}else{if(_JG>_JI){return new F(function(){return _Jc(_);});}else{var _JL=new T(function(){var _JM=_JG-_JH|0;if(0>_JM){return B(_GU(_JM,_JJ));}else{if(_JM>=_JJ){return B(_GU(_JM,_JJ));}else{return E(_JK[_JM]);}}}),_JN=function(_JO,_JP,_JQ,_JR,_JS,_){var _JT=E(_JO);if(!_JT._){return new T2(0,_w,new T4(0,E(_JP),E(_JQ),_JR,_JS));}else{var _JU=E(_JT.a);if(_JP>_JU){return new F(function(){return _J8(_);});}else{if(_JU>_JQ){return new F(function(){return _J8(_);});}else{var _JV=E(_JL),_JW=_JU-_JP|0;if(0>_JW){return new F(function(){return _GP(_JR,_JW);});}else{if(_JW>=_JR){return new F(function(){return _GP(_JR,_JW);});}else{var _JX=E(_JS[_JW]),_JY=__app2(E(_Jr),B(_kD(new T2(1,new T2(0,_AI,_JV.h),new T2(1,new T2(0,_AH,_JV.i),_w)))),B(_kD(new T2(1,new T2(0,_AI,_JX.h),new T2(1,new T2(0,_AH,_JX.i),_w))))),_JZ=__arr2lst(0,_JY),_K0=B(_BW(_JZ,_)),_K1=B(_JN(_JT.b,_JP,_JQ,_JR,_JS,_)),_K2=new T(function(){var _K3=new T(function(){return _JG!=_JU;}),_K4=function(_K5){var _K6=E(_K5);if(!_K6._){return __Z;}else{var _K7=_K6.b,_K8=E(_K6.a),_K9=E(_K8.b),_Ka=E(_K8.a),_Kb=E(_K8.c),_Kc=_Kb.a,_Kd=_Kb.b,_Ke=E(_K8.e),_Kf=E(_K8.d),_Kg=_Kf.a,_Kh=_Kf.b,_Ki=E(_K8.f),_Kj=new T(function(){var _Kk=B(_lg(_jR,_Ki.a,_Ki.b,_Ki.c)),_Kl=Math.sqrt(B(_IY(_jR,_Kg,_Kh,_Kg,_Kh)));return new T3(0,_Kl*E(_Kk.a),_Kl*E(_Kk.b),_Kl*E(_Kk.c));}),_Km=new T(function(){var _Kn=B(_lg(_jR,_Ke.a,_Ke.b,_Ke.c)),_Ko=Math.sqrt(B(_IY(_jR,_Kc,_Kd,_Kc,_Kd)));return new T3(0,_Ko*E(_Kn.a),_Ko*E(_Kn.b),_Ko*E(_Kn.c));}),_Kp=new T(function(){var _Kq=B(A1(_Jz,_K9)),_Kr=B(_lg(_jR,_Kq.a,_Kq.b,_Kq.c));return new T3(0,E(_Kr.a),E(_Kr.b),E(_Kr.c));}),_Ks=new T(function(){var _Kt=B(A1(_Jz,_Ka)),_Ku=B(_lg(_jR,_Kt.a,_Kt.b,_Kt.c));return new T3(0,E(_Ku.a),E(_Ku.b),E(_Ku.c));}),_Kv=E(_K9.a)+ -E(_Ka.a),_Kw=E(_K9.b)+ -E(_Ka.b),_Kx=E(_K9.c)+ -E(_Ka.c),_Ky=new T(function(){return Math.sqrt(B(_8w(_jR,_Kv,_Kw,_Kx,_Kv,_Kw,_Kx)));}),_Kz=new T(function(){var _KA=1/E(_Ky);return new T3(0,_Kv*_KA,_Kw*_KA,_Kx*_KA);}),_KB=new T(function(){if(!E(_K8.g)){return E(_Kz);}else{var _KC=E(_Kz);return new T3(0,-1*E(_KC.a),-1*E(_KC.b),-1*E(_KC.c));}}),_KD=new T(function(){if(!E(_K8.h)){return E(_Kz);}else{var _KE=E(_Kz);return new T3(0,-1*E(_KE.a),-1*E(_KE.b),-1*E(_KE.c));}});return (!E(_K3))?new T2(1,new T(function(){var _KF=E(_KB),_KG=E(_KF.b),_KH=E(_KF.c),_KI=E(_KF.a),_KJ=E(_Ks),_KK=E(_KJ.c),_KL=E(_KJ.b),_KM=E(_KJ.a),_KN=E(_Km),_KO=E(_KN.c),_KP=E(_KN.b),_KQ=E(_KN.a),_KR=_KG*_KK-_KL*_KH,_KS=_KH*_KM-_KK*_KI,_KT=_KI*_KL-_KM*_KG,_KU=B(_8w(_jR,_KS*_KO-_KP*_KT,_KT*_KQ-_KO*_KR,_KR*_KP-_KQ*_KS,_KM,_KL,_KK));return new T6(0,_JG,_JU,E(new T2(0,E(new T3(0,E(_KR),E(_KS),E(_KT))),E(_KU))),E(_Jx),_Ky,_Jd);}),new T2(1,new T(function(){var _KV=E(_KD),_KW=E(_KV.b),_KX=E(_KV.c),_KY=E(_KV.a),_KZ=E(_Kp),_L0=E(_KZ.c),_L1=E(_KZ.b),_L2=E(_KZ.a),_L3=E(_Kj),_L4=E(_L3.c),_L5=E(_L3.b),_L6=E(_L3.a),_L7=_KW*_L0-_L1*_KX,_L8=_KX*_L2-_L0*_KY,_L9=_KY*_L1-_L2*_KW,_La=B(_8w(_jR,_L8*_L4-_L5*_L9,_L9*_L6-_L4*_L7,_L7*_L5-_L6*_L8,_L2,_L1,_L0));return new T6(0,_JG,_JU,E(_Jx),E(new T2(0,E(new T3(0,E(_L7),E(_L8),E(_L9))),E(_La))),_Ky,_Jd);}),new T(function(){return B(_K4(_K7));}))):new T2(1,new T(function(){var _Lb=E(_KB),_Lc=E(_Lb.b),_Ld=E(_Lb.c),_Le=E(_Lb.a),_Lf=E(_Ks),_Lg=_Lf.a,_Lh=_Lf.b,_Li=_Lf.c,_Lj=B(_m3(_jR,_Le,_Lc,_Ld,_Lg,_Lh,_Li)),_Lk=E(_Km),_Ll=E(_Lk.c),_Lm=E(_Lk.b),_Ln=E(_Lk.a),_Lo=B(_8w(_jR,_Lc*_Ll-_Lm*_Ld,_Ld*_Ln-_Ll*_Le,_Le*_Lm-_Ln*_Lc,_Lg,_Lh,_Li)),_Lp=E(_KD),_Lq=E(_Lp.b),_Lr=E(_Lp.c),_Ls=E(_Lp.a),_Lt=E(_Kp),_Lu=_Lt.a,_Lv=_Lt.b,_Lw=_Lt.c,_Lx=B(_m3(_jR,_Ls,_Lq,_Lr,_Lu,_Lv,_Lw)),_Ly=E(_Kj),_Lz=E(_Ly.c),_LA=E(_Ly.b),_LB=E(_Ly.a),_LC=B(_8w(_jR,_Lq*_Lz-_LA*_Lr,_Lr*_LB-_Lz*_Ls,_Ls*_LA-_LB*_Lq,_Lu,_Lv,_Lw));return new T6(0,_JG,_JU,E(new T2(0,E(new T3(0,E(_Lj.a),E(_Lj.b),E(_Lj.c))),E(_Lo))),E(new T2(0,E(new T3(0,E(_Lx.a),E(_Lx.b),E(_Lx.c))),E(_LC))),_Ky,_Je);}),new T(function(){return B(_K4(_K7));}));}};return B(_K4(_K0));});return new T2(0,new T2(1,_K2,new T(function(){return E(E(_K1).a);})),new T(function(){return E(E(_K1).b);}));}}}}}},_LD=B(_JN(B(_sz(_JG,_JE)),_JH,_JI,_JJ,_JK,_)),_LE=E(_JL),_LF=E(_LE.d).a,_LG=__app1(E(_Jp),B(_kD(new T2(1,new T2(0,_AI,_LE.h),new T2(1,new T2(0,_AH,_LE.i),_w))))),_LH=__arr2lst(0,_LG),_LI=B(_BW(_LH,_)),_LJ=__app1(E(_Jq),_JG),_LK=__arr2lst(0,_LJ),_LL=B(_BW(_LK,_));if(_JG!=_JE){var _LM=E(_LD),_LN=E(_LM.b),_LO=B(_JF(_JG+1|0,E(_LN.a),E(_LN.b),_LN.c,_LN.d,_)),_LP=new T(function(){var _LQ=new T(function(){var _LR=B(A1(_Jz,_LF)),_LS=B(_lg(_jR,_LR.a,_LR.b,_LR.c));return new T3(0,E(_LS.a),E(_LS.b),E(_LS.c));}),_LT=new T(function(){var _LU=new T(function(){return B(_Js(_LM.a));}),_LV=function(_LW){var _LX=E(_LW);if(!_LX._){return E(_LU);}else{var _LY=E(_LX.a),_LZ=E(_LY.b),_M0=E(_LY.a),_M1=E(_LY.c),_M2=_M1.a,_M3=_M1.b,_M4=E(_LY.e);return new T2(1,new T(function(){var _M5=E(_LZ.a)+ -E(_M0.a),_M6=E(_LZ.b)+ -E(_M0.b),_M7=E(_LZ.c)+ -E(_M0.c),_M8=B(A1(_Jz,_M0)),_M9=B(_lg(_jR,_M8.a,_M8.b,_M8.c)),_Ma=_M9.a,_Mb=_M9.b,_Mc=_M9.c,_Md=Math.sqrt(B(_8w(_jR,_M5,_M6,_M7,_M5,_M6,_M7))),_Me=1/_Md,_Mf=_M5*_Me,_Mg=_M6*_Me,_Mh=_M7*_Me,_Mi=B(_m3(_jR,_Mf,_Mg,_Mh,_Ma,_Mb,_Mc)),_Mj=B(_lg(_jR,_M4.a,_M4.b,_M4.c)),_Mk=Math.sqrt(B(_IY(_jR,_M2,_M3,_M2,_M3))),_Ml=_Mk*E(_Mj.a),_Mm=_Mk*E(_Mj.b),_Mn=_Mk*E(_Mj.c),_Mo=B(_8w(_jR,_Mg*_Mn-_Mm*_Mh,_Mh*_Ml-_Mn*_Mf,_Mf*_Mm-_Ml*_Mg,_Ma,_Mb,_Mc));return new T6(0,_JG,_JG,E(new T2(0,E(new T3(0,E(_Mi.a),E(_Mi.b),E(_Mi.c))),E(_Mo))),E(_Jx),_Md,_Je);}),new T(function(){return B(_LV(_LX.b));}));}};return B(_LV(_LI));}),_Mp=function(_Mq){var _Mr=E(_Mq);if(!_Mr._){return E(_LT);}else{var _Ms=E(_Mr.a),_Mt=E(_Ms.b),_Mu=new T(function(){var _Mv=E(_LF),_Mw=E(_Mt.c)+ -E(_Mv.c),_Mx=E(_Mt.b)+ -E(_Mv.b),_My=E(_Mt.a)+ -E(_Mv.a),_Mz=Math.sqrt(B(_8w(_jR,_My,_Mx,_Mw,_My,_Mx,_Mw))),_MA=function(_MB,_MC,_MD){var _ME=E(_LQ),_MF=_ME.a,_MG=_ME.b,_MH=_ME.c,_MI=B(_m3(_jR,_MB,_MC,_MD,_MF,_MG,_MH)),_MJ=B(_8w(_jR,_MC*0-0*_MD,_MD*0-0*_MB,_MB*0-0*_MC,_MF,_MG,_MH));return new T6(0,_JG,_JG,new T2(0,E(new T3(0,E(_MI.a),E(_MI.b),E(_MI.c))),E(_MJ)),_Jx,_Mz,_Je);};if(!E(_Ms.g)){var _MK=1/_Mz,_ML=B(_MA(_My*_MK,_Mx*_MK,_Mw*_MK));return new T6(0,_ML.a,_ML.b,E(_ML.c),E(_ML.d),_ML.e,_ML.f);}else{var _MM=1/_Mz,_MN=B(_MA(-1*_My*_MM,-1*_Mx*_MM,-1*_Mw*_MM));return new T6(0,_MN.a,_MN.b,E(_MN.c),E(_MN.d),_MN.e,_MN.f);}});return new T2(1,_Mu,new T(function(){return B(_Mp(_Mr.b));}));}};return B(_Mp(_LL));});return new T2(0,new T2(1,_LP,new T(function(){return E(E(_LO).a);})),new T(function(){return E(E(_LO).b);}));}else{var _MO=new T(function(){var _MP=new T(function(){var _MQ=B(A1(_Jz,_LF)),_MR=B(_lg(_jR,_MQ.a,_MQ.b,_MQ.c));return new T3(0,E(_MR.a),E(_MR.b),E(_MR.c));}),_MS=new T(function(){var _MT=new T(function(){return B(_Js(E(_LD).a));}),_MU=function(_MV){var _MW=E(_MV);if(!_MW._){return E(_MT);}else{var _MX=E(_MW.a),_MY=E(_MX.b),_MZ=E(_MX.a),_N0=E(_MX.c),_N1=_N0.a,_N2=_N0.b,_N3=E(_MX.e);return new T2(1,new T(function(){var _N4=E(_MY.a)+ -E(_MZ.a),_N5=E(_MY.b)+ -E(_MZ.b),_N6=E(_MY.c)+ -E(_MZ.c),_N7=B(A1(_Jz,_MZ)),_N8=B(_lg(_jR,_N7.a,_N7.b,_N7.c)),_N9=_N8.a,_Na=_N8.b,_Nb=_N8.c,_Nc=Math.sqrt(B(_8w(_jR,_N4,_N5,_N6,_N4,_N5,_N6))),_Nd=1/_Nc,_Ne=_N4*_Nd,_Nf=_N5*_Nd,_Ng=_N6*_Nd,_Nh=B(_m3(_jR,_Ne,_Nf,_Ng,_N9,_Na,_Nb)),_Ni=B(_lg(_jR,_N3.a,_N3.b,_N3.c)),_Nj=Math.sqrt(B(_IY(_jR,_N1,_N2,_N1,_N2))),_Nk=_Nj*E(_Ni.a),_Nl=_Nj*E(_Ni.b),_Nm=_Nj*E(_Ni.c),_Nn=B(_8w(_jR,_Nf*_Nm-_Nl*_Ng,_Ng*_Nk-_Nm*_Ne,_Ne*_Nl-_Nk*_Nf,_N9,_Na,_Nb));return new T6(0,_JG,_JG,E(new T2(0,E(new T3(0,E(_Nh.a),E(_Nh.b),E(_Nh.c))),E(_Nn))),E(_Jx),_Nc,_Je);}),new T(function(){return B(_MU(_MW.b));}));}};return B(_MU(_LI));}),_No=function(_Np){var _Nq=E(_Np);if(!_Nq._){return E(_MS);}else{var _Nr=E(_Nq.a),_Ns=E(_Nr.b),_Nt=new T(function(){var _Nu=E(_LF),_Nv=E(_Ns.c)+ -E(_Nu.c),_Nw=E(_Ns.b)+ -E(_Nu.b),_Nx=E(_Ns.a)+ -E(_Nu.a),_Ny=Math.sqrt(B(_8w(_jR,_Nx,_Nw,_Nv,_Nx,_Nw,_Nv))),_Nz=function(_NA,_NB,_NC){var _ND=E(_MP),_NE=_ND.a,_NF=_ND.b,_NG=_ND.c,_NH=B(_m3(_jR,_NA,_NB,_NC,_NE,_NF,_NG)),_NI=B(_8w(_jR,_NB*0-0*_NC,_NC*0-0*_NA,_NA*0-0*_NB,_NE,_NF,_NG));return new T6(0,_JG,_JG,new T2(0,E(new T3(0,E(_NH.a),E(_NH.b),E(_NH.c))),E(_NI)),_Jx,_Ny,_Je);};if(!E(_Nr.g)){var _NJ=1/_Ny,_NK=B(_Nz(_Nx*_NJ,_Nw*_NJ,_Nv*_NJ));return new T6(0,_NK.a,_NK.b,E(_NK.c),E(_NK.d),_NK.e,_NK.f);}else{var _NL=1/_Ny,_NM=B(_Nz(-1*_Nx*_NL,-1*_Nw*_NL,-1*_Nv*_NL));return new T6(0,_NM.a,_NM.b,E(_NM.c),E(_NM.d),_NM.e,_NM.f);}});return new T2(1,_Nt,new T(function(){return B(_No(_Nq.b));}));}};return B(_No(_LL));});return new T2(0,new T2(1,_MO,_w),new T(function(){return E(E(_LD).b);}));}}}},_NN=B(_JF(_JD,_JD,_JE,_JC.c,_JC.d,_));return new F(function(){return _IQ(_,_NN);});}else{return new F(function(){return _IQ(_,new T2(0,_w,_JC));});}},_NO=new T(function(){return eval("__strict(passObject)");}),_NP=new T(function(){return eval("__strict(refresh)");}),_NQ=function(_NR,_){var _NS=__app0(E(_NP)),_NT=__app0(E(_AM)),_NU=E(_NR),_NV=_NU.c,_NW=_NU.d,_NX=E(_NU.a),_NY=E(_NU.b);if(_NX<=_NY){if(_NX>_NY){return E(_AK);}else{if(0>=_NV){return new F(function(){return _AX(_NV,0);});}else{var _NZ=E(_NW[0]),_O0=E(_NO),_O1=__app2(_O0,_NX,B(_kD(new T2(1,new T2(0,_AI,_NZ.h),new T2(1,new T2(0,_AH,_NZ.i),_w)))));if(_NX!=_NY){var _O2=function(_O3,_){if(_NX>_O3){return E(_AK);}else{if(_O3>_NY){return E(_AK);}else{var _O4=_O3-_NX|0;if(0>_O4){return new F(function(){return _AX(_NV,_O4);});}else{if(_O4>=_NV){return new F(function(){return _AX(_NV,_O4);});}else{var _O5=E(_NW[_O4]),_O6=__app2(_O0,_O3,B(_kD(new T2(1,new T2(0,_AI,_O5.h),new T2(1,new T2(0,_AH,_O5.i),_w)))));if(_O3!=_NY){var _O7=B(_O2(_O3+1|0,_));return new T2(1,_kC,_O7);}else{return _B2;}}}}}},_O8=B(_O2(_NX+1|0,_)),_O9=__app0(E(_AL)),_Oa=B(_JA(_NU,_));return new T(function(){return E(E(_Oa).b);});}else{var _Ob=__app0(E(_AL)),_Oc=B(_JA(_NU,_));return new T(function(){return E(E(_Oc).b);});}}}}else{var _Od=__app0(E(_AL)),_Oe=B(_JA(_NU,_));return new T(function(){return E(E(_Oe).b);});}},_Of=function(_Og,_){while(1){var _Oh=E(_Og);if(!_Oh._){return _kC;}else{var _Oi=_Oh.b,_Oj=E(_Oh.a);switch(_Oj._){case 0:var _Ok=B(A1(_Oj.a,_));_Og=B(_n(_Oi,new T2(1,_Ok,_w)));continue;case 1:_Og=B(_n(_Oi,_Oj.a));continue;default:_Og=_Oi;continue;}}}},_Ol=function(_Om,_On,_){var _Oo=E(_Om);switch(_Oo._){case 0:var _Op=B(A1(_Oo.a,_));return new F(function(){return _Of(B(_n(_On,new T2(1,_Op,_w))),_);});break;case 1:return new F(function(){return _Of(B(_n(_On,_Oo.a)),_);});break;default:return new F(function(){return _Of(_On,_);});}},_Oq=new T0(2),_Or=function(_Os){return new T0(2);},_Ot=function(_Ou,_Ov,_Ow){return function(_){var _Ox=E(_Ou),_Oy=rMV(_Ox),_Oz=E(_Oy);if(!_Oz._){var _OA=new T(function(){var _OB=new T(function(){return B(A1(_Ow,_kC));});return B(_n(_Oz.b,new T2(1,new T2(0,_Ov,function(_OC){return E(_OB);}),_w)));}),_=wMV(_Ox,new T2(0,_Oz.a,_OA));return _Oq;}else{var _OD=E(_Oz.a);if(!_OD._){var _=wMV(_Ox,new T2(0,_Ov,_w));return new T(function(){return B(A1(_Ow,_kC));});}else{var _=wMV(_Ox,new T1(1,_OD.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Ow,_kC));}),new T2(1,new T(function(){return B(A2(_OD.a,_Ov,_Or));}),_w)));}}};},_OE=new T(function(){return E(_q3);}),_OF=new T(function(){return eval("window.requestAnimationFrame");}),_OG=new T1(1,_w),_OH=function(_OI,_OJ){return function(_){var _OK=E(_OI),_OL=rMV(_OK),_OM=E(_OL);if(!_OM._){var _ON=_OM.a,_OO=E(_OM.b);if(!_OO._){var _=wMV(_OK,_OG);return new T(function(){return B(A1(_OJ,_ON));});}else{var _OP=E(_OO.a),_=wMV(_OK,new T2(0,_OP.a,_OO.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OJ,_ON));}),new T2(1,new T(function(){return B(A1(_OP.b,_Or));}),_w)));}}else{var _OQ=new T(function(){var _OR=function(_OS){var _OT=new T(function(){return B(A1(_OJ,_OS));});return function(_OU){return E(_OT);};};return B(_n(_OM.a,new T2(1,_OR,_w)));}),_=wMV(_OK,new T1(1,_OQ));return _Oq;}};},_OV=function(_OW,_OX){return new T1(0,B(_OH(_OW,_OX)));},_OY=function(_OZ,_P0){var _P1=new T(function(){return new T1(0,B(_Ot(_OZ,_kC,_Or)));});return function(_){var _P2=__createJSFunc(2,function(_P3,_){var _P4=B(_Ol(_P1,_w,_));return _OE;}),_P5=__app1(E(_OF),_P2);return new T(function(){return B(_OV(_OZ,_P0));});};},_P6=new T1(1,_w),_P7=function(_P8,_P9,_){var _Pa=function(_){var _Pb=nMV(_P8),_Pc=_Pb;return new T(function(){var _Pd=new T(function(){return B(_Pe(_));}),_Pf=function(_){var _Pg=rMV(_Pc),_Ph=B(A2(_P9,_Pg,_)),_=wMV(_Pc,_Ph),_Pi=function(_){var _Pj=nMV(_P6);return new T(function(){return new T1(0,B(_OY(_Pj,function(_Pk){return E(_Pd);})));});};return new T1(0,_Pi);},_Pl=new T(function(){return new T1(0,_Pf);}),_Pe=function(_Pm){return E(_Pl);};return B(_Pe(_));});};return new F(function(){return _Ol(new T1(0,_Pa),_w,_);});},_Pn=new T(function(){return eval("__strict(setBounds)");}),_Po=function(_){var _Pp=__app3(E(_20),E(_93),E(_id),E(_1Z)),_Pq=__app2(E(_Pn),E(_1u),E(_1n));return new F(function(){return _P7(_AG,_NQ,_);});},_Pr=function(_){return new F(function(){return _Po(_);});};
var hasteMain = function() {B(A(_Pr, [0]));};window.onload = hasteMain;