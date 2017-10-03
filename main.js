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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(_hP).a);})));})));}),_hR=new T(function(){return B(_fR(_hQ));}),_hS=new T(function(){return B(A2(_8s,_hQ,_8r));}),_hT=new T(function(){return E(E(_hP).b);}),_hU=function(_hV){var _hW=new T(function(){var _hX=new T(function(){return B(A1(_hR,new T(function(){return E(E(_hV).c);})));}),_hY=new T(function(){return B(A1(_hR,new T(function(){return E(E(_hV).a);})));});return B(A3(_gN,_hT,_hY,_hX));});return new F(function(){return A3(_9p,_hQ,_hW,_hS);});};return E(_hU);},_hZ=function(_ef,_ee){return new T2(0,_ef,_ee);},_i0=function(_i1,_i2,_i3){var _i4=new T(function(){var _i5=E(_i1),_i6=_i5.a,_i7=new T(function(){return B(A1(_i5.b,new T(function(){return B(_8J(B(_8H(E(_i5.c).a))));})));});return B(A3(_8R,_i6,new T(function(){return B(A3(_8T,B(_8F(_i6)),_hZ,_i3));}),_i7));});return E(B(A1(_i2,_i4)).b);},_i8=function(_i9){var _ia=new T(function(){return E(E(_i9).a);}),_ib=new T(function(){return E(E(_i9).b);}),_ic=new T(function(){var _id=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),_ie=new T(function(){var _if=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),new T3(0,_8p,_8u,new T2(0,_ia,_ib))));});return B(_eb(_if,new T3(0,_8p,_8u,new T2(0,_ia,_ib))));});return B(_hO(new T2(0,_ie,_id)));});return function(_ig){return new F(function(){return _i0(new T3(0,_8p,_8u,new T2(0,_ia,_ib)),_ic,_ig);});};},_ih=new T(function(){return B(_i8(_7V));}),_ii=new T(function(){return B(A1(_ih,_E));}),_ij=new T(function(){return E(E(_ii).a);}),_ik=new T(function(){return B(unCStr(",y:"));}),_il=new T1(0,_ik),_im=new T(function(){return E(E(_ii).b);}),_in=new T(function(){return B(unCStr(",z:"));}),_io=new T1(0,_in),_ip=new T(function(){return E(E(_ii).c);}),_iq=new T(function(){return B(unCStr("})"));}),_ir=new T1(0,_iq),_is=new T2(1,_ir,_w),_it=new T2(1,_ip,_is),_iu=new T2(1,_io,_it),_iv=new T2(1,_im,_iu),_iw=new T2(1,_il,_iv),_ix=new T2(1,_ij,_iw),_iy=new T(function(){return B(unCStr("({x:"));}),_iz=new T1(0,_iy),_iA=new T2(1,_iz,_ix),_iB=function(_iC){return E(_iC);},_iD=new T(function(){return toJSStr(B(_e(_x,_iB,_iA)));}),_iE=new T(function(){return B(_hO(_7V));}),_iF=new T(function(){return B(A1(_iE,_E));}),_iG=new T(function(){return toJSStr(B(_4(_x,_iB,_iF)));}),_iH=function(_iI,_iJ,_iK){var _iL=E(_iK);if(!_iL._){return new F(function(){return A1(_iJ,_iL.a);});}else{var _iM=new T(function(){return B(_0(_iI));}),_iN=new T(function(){return B(_2(_iI));}),_iO=function(_iP){var _iQ=E(_iP);if(!_iQ._){return E(_iN);}else{return new F(function(){return A2(_iM,new T(function(){return B(_iH(_iI,_iJ,_iQ.a));}),new T(function(){return B(_iO(_iQ.b));}));});}};return new F(function(){return _iO(_iL.a);});}},_iR=new T(function(){return B(unCStr("x"));}),_iS=new T1(0,_iR),_iT=new T(function(){return B(unCStr("y"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("z"));}),_iW=new T1(0,_iV),_iX=new T3(0,E(_iS),E(_iU),E(_iW)),_iY=new T(function(){return B(unCStr(","));}),_iZ=new T1(0,_iY),_j0=new T(function(){return B(unCStr("pow("));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr(")"));}),_j3=new T1(0,_j2),_j4=new T2(1,_j3,_w),_j5=function(_j6,_j7){return new T1(1,new T2(1,_j1,new T2(1,_j6,new T2(1,_iZ,new T2(1,_j7,_j4)))));},_j8=new T(function(){return B(unCStr("acos("));}),_j9=new T1(0,_j8),_ja=function(_jb){return new T1(1,new T2(1,_j9,new T2(1,_jb,_j4)));},_jc=new T(function(){return B(unCStr("acosh("));}),_jd=new T1(0,_jc),_je=function(_jf){return new T1(1,new T2(1,_jd,new T2(1,_jf,_j4)));},_jg=new T(function(){return B(unCStr("asin("));}),_jh=new T1(0,_jg),_ji=function(_jj){return new T1(1,new T2(1,_jh,new T2(1,_jj,_j4)));},_jk=new T(function(){return B(unCStr("asinh("));}),_jl=new T1(0,_jk),_jm=function(_jn){return new T1(1,new T2(1,_jl,new T2(1,_jn,_j4)));},_jo=new T(function(){return B(unCStr("atan("));}),_jp=new T1(0,_jo),_jq=function(_jr){return new T1(1,new T2(1,_jp,new T2(1,_jr,_j4)));},_js=new T(function(){return B(unCStr("atanh("));}),_jt=new T1(0,_js),_ju=function(_jv){return new T1(1,new T2(1,_jt,new T2(1,_jv,_j4)));},_jw=new T(function(){return B(unCStr("cos("));}),_jx=new T1(0,_jw),_jy=function(_jz){return new T1(1,new T2(1,_jx,new T2(1,_jz,_j4)));},_jA=new T(function(){return B(unCStr("cosh("));}),_jB=new T1(0,_jA),_jC=function(_jD){return new T1(1,new T2(1,_jB,new T2(1,_jD,_j4)));},_jE=new T(function(){return B(unCStr("exp("));}),_jF=new T1(0,_jE),_jG=function(_jH){return new T1(1,new T2(1,_jF,new T2(1,_jH,_j4)));},_jI=new T(function(){return B(unCStr("log("));}),_jJ=new T1(0,_jI),_jK=function(_jL){return new T1(1,new T2(1,_jJ,new T2(1,_jL,_j4)));},_jM=new T(function(){return B(unCStr(")/log("));}),_jN=new T1(0,_jM),_jO=function(_jP,_jQ){return new T1(1,new T2(1,_jJ,new T2(1,_jQ,new T2(1,_jN,new T2(1,_jP,_j4)))));},_jR=new T(function(){return B(unCStr("pi"));}),_jS=new T1(0,_jR),_jT=new T(function(){return B(unCStr("sin("));}),_jU=new T1(0,_jT),_jV=function(_jW){return new T1(1,new T2(1,_jU,new T2(1,_jW,_j4)));},_jX=new T(function(){return B(unCStr("sinh("));}),_jY=new T1(0,_jX),_jZ=function(_k0){return new T1(1,new T2(1,_jY,new T2(1,_k0,_j4)));},_k1=new T(function(){return B(unCStr("sqrt("));}),_k2=new T1(0,_k1),_k3=function(_k4){return new T1(1,new T2(1,_k2,new T2(1,_k4,_j4)));},_k5=new T(function(){return B(unCStr("tan("));}),_k6=new T1(0,_k5),_k7=function(_k8){return new T1(1,new T2(1,_k6,new T2(1,_k8,_j4)));},_k9=new T(function(){return B(unCStr("tanh("));}),_ka=new T1(0,_k9),_kb=function(_kc){return new T1(1,new T2(1,_ka,new T2(1,_kc,_j4)));},_kd=new T(function(){return B(unCStr("("));}),_ke=new T1(0,_kd),_kf=new T(function(){return B(unCStr(")/("));}),_kg=new T1(0,_kf),_kh=function(_ki,_kj){return new T1(1,new T2(1,_ke,new T2(1,_ki,new T2(1,_kg,new T2(1,_kj,_j4)))));},_kk=function(_kl){return new T1(0,new T(function(){var _km=E(_kl),_kn=jsShow(B(_6y(_km.a,_km.b)));return fromJSStr(_kn);}));},_ko=new T(function(){return B(unCStr("1./("));}),_kp=new T1(0,_ko),_kq=function(_kr){return new T1(1,new T2(1,_kp,new T2(1,_kr,_j4)));},_ks=new T(function(){return B(unCStr(")+("));}),_kt=new T1(0,_ks),_ku=function(_kv,_kw){return new T1(1,new T2(1,_ke,new T2(1,_kv,new T2(1,_kt,new T2(1,_kw,_j4)))));},_kx=new T(function(){return B(unCStr("-("));}),_ky=new T1(0,_kx),_kz=function(_kA){return new T1(1,new T2(1,_ky,new T2(1,_kA,_j4)));},_kB=new T(function(){return B(unCStr(")*("));}),_kC=new T1(0,_kB),_kD=function(_kE,_kF){return new T1(1,new T2(1,_ke,new T2(1,_kE,new T2(1,_kC,new T2(1,_kF,_j4)))));},_kG=function(_kH,_kI){return new F(function(){return A3(_6X,_kJ,_kH,new T(function(){return B(A2(_6Z,_kJ,_kI));}));});},_kK=new T(function(){return B(unCStr("abs("));}),_kL=new T1(0,_kK),_kM=function(_kN){return new T1(1,new T2(1,_kL,new T2(1,_kN,_j4)));},_kO=new T(function(){return B(unCStr("."));}),_kP=function(_kQ){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kQ,_w)),_kO));}));},_kR=new T(function(){return B(unCStr("sign("));}),_kS=new T1(0,_kR),_kT=function(_kU){return new T1(1,new T2(1,_kS,new T2(1,_kU,_j4)));},_kJ=new T(function(){return {_:0,a:_ku,b:_kG,c:_kD,d:_kz,e:_kM,f:_kT,g:_kP};}),_kV=new T4(0,_kJ,_kh,_kq,_kk),_kW={_:0,a:_kV,b:_jS,c:_jG,d:_jK,e:_k3,f:_j5,g:_jO,h:_jV,i:_jy,j:_k7,k:_ji,l:_ja,m:_jq,n:_jZ,o:_jC,p:_kb,q:_jm,r:_je,s:_ju},_kX=new T(function(){return B(unCStr("(/=) is not defined"));}),_kY=new T(function(){return B(err(_kX));}),_kZ=new T(function(){return B(unCStr("(==) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T2(0,_l0,_kY),_l2=new T(function(){return B(unCStr("(<) is not defined"));}),_l3=new T(function(){return B(err(_l2));}),_l4=new T(function(){return B(unCStr("(<=) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(>) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>=) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("compare is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("max("));}),_ld=new T1(0,_lc),_le=function(_lf,_lg){return new T1(1,new T2(1,_ld,new T2(1,_lf,new T2(1,_iZ,new T2(1,_lg,_j4)))));},_lh=new T(function(){return B(unCStr("min("));}),_li=new T1(0,_lh),_lj=function(_lk,_ll){return new T1(1,new T2(1,_li,new T2(1,_lk,new T2(1,_iZ,new T2(1,_ll,_j4)))));},_lm={_:0,a:_l1,b:_lb,c:_l3,d:_l5,e:_l7,f:_l9,g:_le,h:_lj},_ln=new T2(0,_kW,_lm),_lo=new T(function(){return B(_hO(_ln));}),_lp=new T(function(){return B(A1(_lo,_iX));}),_lq=new T(function(){return toJSStr(B(_iH(_x,_iB,_lp)));}),_lr=new T(function(){return eval("__strict(compile)");}),_ls=new T(function(){return toJSStr(E(_iT));}),_lt=function(_lu,_lv,_lw){var _lx=new T(function(){return B(_0(_lu));}),_ly=new T(function(){return B(_2(_lu));}),_lz=function(_lA){var _lB=E(_lA);if(!_lB._){return E(_ly);}else{return new F(function(){return A2(_lx,new T(function(){return B(_iH(_lu,_lv,_lB.a));}),new T(function(){return B(_lz(_lB.b));}));});}};return new F(function(){return _lz(_lw);});},_lC=new T(function(){return B(unCStr("vec3("));}),_lD=new T1(0,_lC),_lE=new T(function(){return B(_7i(0,_8r,_w));}),_lF=new T(function(){return B(_n(_lE,_kO));}),_lG=new T1(0,_lF),_lH=new T(function(){return B(_7i(0,_8q,_w));}),_lI=new T(function(){return B(_n(_lH,_kO));}),_lJ=new T1(0,_lI),_lK=new T2(1,_lJ,_w),_lL=new T2(1,_lG,_lK),_lM=function(_lN,_lO){var _lP=E(_lO);return (_lP._==0)?__Z:new T2(1,_lN,new T2(1,_lP.a,new T(function(){return B(_lM(_lN,_lP.b));})));},_lQ=new T(function(){return B(_lM(_iZ,_lL));}),_lR=new T2(1,_lJ,_lQ),_lS=new T1(1,_lR),_lT=new T2(1,_lS,_j4),_lU=new T2(1,_lD,_lT),_lV=new T(function(){return toJSStr(B(_lt(_x,_iB,_lU)));}),_lW="enclose",_lX="outline",_lY="polygon",_lZ="z",_m0="y",_m1="x",_m2=0,_m3=function(_m4){var _m5=__new(),_m6=_m5,_m7=function(_m8,_){while(1){var _m9=E(_m8);if(!_m9._){return _m2;}else{var _ma=E(_m9.a),_mb=__set(_m6,E(_ma.a),E(_ma.b));_m8=_m9.b;continue;}}},_mc=B(_m7(_m4,_));return E(_m6);},_md=function(_me){return new F(function(){return _m3(new T2(1,new T2(0,_m1,new T(function(){return E(E(E(E(_me).d).a).a);})),new T2(1,new T2(0,_m0,new T(function(){return E(E(E(E(_me).d).a).b);})),new T2(1,new T2(0,_lZ,new T(function(){return E(E(E(E(_me).d).a).c);})),new T2(1,new T2(0,_lY,new T(function(){return E(_me).h;})),new T2(1,new T2(0,_lX,new T(function(){return E(_me).i;})),new T2(1,new T2(0,_lW,new T(function(){return E(_me).j;})),_w)))))));});},_mf=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_mg=new T(function(){return B(err(_mf));}),_mh=new T(function(){return eval("__strict(drawObjects)");}),_mi=new T(function(){return eval("__strict(draw)");}),_mj=function(_mk,_ml){var _mm=jsShowI(_mk);return new F(function(){return _n(fromJSStr(_mm),_ml);});},_mn=function(_mo,_mp,_mq){if(_mp>=0){return new F(function(){return _mj(_mp,_mq);});}else{if(_mo<=6){return new F(function(){return _mj(_mp,_mq);});}else{return new T2(1,_7g,new T(function(){var _mr=jsShowI(_mp);return B(_n(fromJSStr(_mr),new T2(1,_7f,_mq)));}));}}},_ms=new T(function(){return B(unCStr(")"));}),_mt=function(_mu,_mv){var _mw=new T(function(){var _mx=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mn(0,_mu,_w)),_ms));})));},1);return B(_n(B(_mn(0,_mv,_w)),_mx));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_mw)));});},_my=new T2(1,_m2,_w),_mz=function(_mA){return E(_mA);},_mB=function(_mC){return E(_mC);},_mD=function(_mE,_mF){return E(_mF);},_mG=function(_mH,_mI){return E(_mH);},_mJ=function(_mK){return E(_mK);},_mL=new T2(0,_mJ,_mG),_mM=function(_mN,_mO){return E(_mN);},_mP=new T5(0,_mL,_mB,_mz,_mD,_mM),_mQ=function(_mR){var _mS=E(_mR);return new F(function(){return Math.log(_mS+(_mS+1)*Math.sqrt((_mS-1)/(_mS+1)));});},_mT=function(_mU){var _mV=E(_mU);return new F(function(){return Math.log(_mV+Math.sqrt(1+_mV*_mV));});},_mW=function(_mX){var _mY=E(_mX);return 0.5*Math.log((1+_mY)/(1-_mY));},_mZ=function(_n0,_n1){return Math.log(E(_n1))/Math.log(E(_n0));},_n2=3.141592653589793,_n3=function(_n4){var _n5=E(_n4);return new F(function(){return _6y(_n5.a,_n5.b);});},_n6=function(_n7){return 1/E(_n7);},_n8=function(_n9){var _na=E(_n9),_nb=E(_na);return (_nb==0)?E(_6x):(_nb<=0)? -_nb:E(_na);},_nc=function(_nd){var _ne=E(_nd);if(!_ne._){return _ne.a;}else{return new F(function(){return I_toNumber(_ne.a);});}},_nf=function(_ng){return new F(function(){return _nc(_ng);});},_nh=1,_ni=-1,_nj=function(_nk){var _nl=E(_nk);return (_nl<=0)?(_nl>=0)?E(_nl):E(_ni):E(_nh);},_nm=function(_nn,_no){return E(_nn)-E(_no);},_np=function(_nq){return  -E(_nq);},_nr=function(_ns,_nt){return E(_ns)+E(_nt);},_nu=function(_nv,_nw){return E(_nv)*E(_nw);},_nx={_:0,a:_nr,b:_nm,c:_nu,d:_np,e:_n8,f:_nj,g:_nf},_ny=function(_nz,_nA){return E(_nz)/E(_nA);},_nB=new T4(0,_nx,_ny,_n6,_n3),_nC=function(_nD){return new F(function(){return Math.acos(E(_nD));});},_nE=function(_nF){return new F(function(){return Math.asin(E(_nF));});},_nG=function(_nH){return new F(function(){return Math.atan(E(_nH));});},_nI=function(_nJ){return new F(function(){return Math.cos(E(_nJ));});},_nK=function(_nL){return new F(function(){return cosh(E(_nL));});},_nM=function(_nN){return new F(function(){return Math.exp(E(_nN));});},_nO=function(_nP){return new F(function(){return Math.log(E(_nP));});},_nQ=function(_nR,_nS){return new F(function(){return Math.pow(E(_nR),E(_nS));});},_nT=function(_nU){return new F(function(){return Math.sin(E(_nU));});},_nV=function(_nW){return new F(function(){return sinh(E(_nW));});},_nX=function(_nY){return new F(function(){return Math.sqrt(E(_nY));});},_nZ=function(_o0){return new F(function(){return Math.tan(E(_o0));});},_o1=function(_o2){return new F(function(){return tanh(E(_o2));});},_o3={_:0,a:_nB,b:_n2,c:_nM,d:_nO,e:_nX,f:_nQ,g:_mZ,h:_nT,i:_nI,j:_nZ,k:_nE,l:_nC,m:_nG,n:_nV,o:_nK,p:_o1,q:_mT,r:_mQ,s:_mW},_o4="flipped2",_o5="flipped1",_o6="c1y",_o7="c1x",_o8="w2z",_o9="w2y",_oa="w2x",_ob="w1z",_oc="w1y",_od="w1x",_oe="d2z",_of="d2y",_og="d2x",_oh="d1z",_oi="d1y",_oj="d1x",_ok="c2y",_ol="c2x",_om=function(_on,_){var _oo=__get(_on,E(_od)),_op=__get(_on,E(_oc)),_oq=__get(_on,E(_ob)),_or=__get(_on,E(_oa)),_os=__get(_on,E(_o9)),_ot=__get(_on,E(_o8)),_ou=__get(_on,E(_o7)),_ov=__get(_on,E(_o6)),_ow=__get(_on,E(_ol)),_ox=__get(_on,E(_ok)),_oy=__get(_on,E(_oj)),_oz=__get(_on,E(_oi)),_oA=__get(_on,E(_oh)),_oB=__get(_on,E(_og)),_oC=__get(_on,E(_of)),_oD=__get(_on,E(_oe)),_oE=__get(_on,E(_o5)),_oF=__get(_on,E(_o4));return {_:0,a:E(new T3(0,E(_oo),E(_op),E(_oq))),b:E(new T3(0,E(_or),E(_os),E(_ot))),c:E(new T2(0,E(_ou),E(_ov))),d:E(new T2(0,E(_ow),E(_ox))),e:E(new T3(0,E(_oy),E(_oz),E(_oA))),f:E(new T3(0,E(_oB),E(_oC),E(_oD))),g:E(_oE),h:E(_oF)};},_oG=function(_oH,_){var _oI=E(_oH);if(!_oI._){return _w;}else{var _oJ=B(_om(E(_oI.a),_)),_oK=B(_oG(_oI.b,_));return new T2(1,_oJ,_oK);}},_oL=function(_oM){var _oN=E(_oM);return (E(_oN.b)-E(_oN.a)|0)+1|0;},_oO=function(_oP,_oQ){var _oR=E(_oP),_oS=E(_oQ);return (E(_oR.a)>_oS)?false:_oS<=E(_oR.b);},_oT=function(_oU){return new F(function(){return _mn(0,E(_oU),_w);});},_oV=function(_oW,_oX,_oY){return new F(function(){return _mn(E(_oW),E(_oX),_oY);});},_oZ=function(_p0,_p1){return new F(function(){return _mn(0,E(_p0),_p1);});},_p2=function(_p3,_p4){return new F(function(){return _2Q(_oZ,_p3,_p4);});},_p5=new T3(0,_oV,_oT,_p2),_p6=0,_p7=function(_p8,_p9,_pa){return new F(function(){return A1(_p8,new T2(1,_2N,new T(function(){return B(A1(_p9,_pa));})));});},_pb=new T(function(){return B(unCStr(": empty list"));}),_pc=new T(function(){return B(unCStr("Prelude."));}),_pd=function(_pe){return new F(function(){return err(B(_n(_pc,new T(function(){return B(_n(_pe,_pb));},1))));});},_pf=new T(function(){return B(unCStr("foldr1"));}),_pg=new T(function(){return B(_pd(_pf));}),_ph=function(_pi,_pj){var _pk=E(_pj);if(!_pk._){return E(_pg);}else{var _pl=_pk.a,_pm=E(_pk.b);if(!_pm._){return E(_pl);}else{return new F(function(){return A2(_pi,_pl,new T(function(){return B(_ph(_pi,_pm));}));});}}},_pn=new T(function(){return B(unCStr(" out of range "));}),_po=new T(function(){return B(unCStr("}.index: Index "));}),_pp=new T(function(){return B(unCStr("Ix{"));}),_pq=new T2(1,_7f,_w),_pr=new T2(1,_7f,_pq),_ps=0,_pt=function(_pu){return E(E(_pu).a);},_pv=function(_pw,_px,_py,_pz,_pA){var _pB=new T(function(){var _pC=new T(function(){var _pD=new T(function(){var _pE=new T(function(){var _pF=new T(function(){return B(A3(_ph,_p7,new T2(1,new T(function(){return B(A3(_pt,_py,_ps,_pz));}),new T2(1,new T(function(){return B(A3(_pt,_py,_ps,_pA));}),_w)),_pr));});return B(_n(_pn,new T2(1,_7g,new T2(1,_7g,_pF))));});return B(A(_pt,[_py,_p6,_px,new T2(1,_7f,_pE)]));});return B(_n(_po,new T2(1,_7g,_pD)));},1);return B(_n(_pw,_pC));},1);return new F(function(){return err(B(_n(_pp,_pB)));});},_pG=function(_pH,_pI,_pJ,_pK,_pL){return new F(function(){return _pv(_pH,_pI,_pL,_pJ,_pK);});},_pM=function(_pN,_pO,_pP,_pQ){var _pR=E(_pP);return new F(function(){return _pG(_pN,_pO,_pR.a,_pR.b,_pQ);});},_pS=function(_pT,_pU,_pV,_pW){return new F(function(){return _pM(_pW,_pV,_pU,_pT);});},_pX=new T(function(){return B(unCStr("Int"));}),_pY=function(_pZ,_q0){return new F(function(){return _pS(_p5,_q0,_pZ,_pX);});},_q1=function(_q2,_q3){var _q4=E(_q2),_q5=E(_q4.a),_q6=E(_q3);if(_q5>_q6){return new F(function(){return _pY(_q6,_q4);});}else{if(_q6>E(_q4.b)){return new F(function(){return _pY(_q6,_q4);});}else{return _q6-_q5|0;}}},_q7=function(_q8,_q9){if(_q8<=_q9){var _qa=function(_qb){return new T2(1,_qb,new T(function(){if(_qb!=_q9){return B(_qa(_qb+1|0));}else{return __Z;}}));};return new F(function(){return _qa(_q8);});}else{return __Z;}},_qc=function(_qd,_qe){return new F(function(){return _q7(E(_qd),E(_qe));});},_qf=function(_qg){var _qh=E(_qg);return new F(function(){return _qc(_qh.a,_qh.b);});},_qi=function(_qj){var _qk=E(_qj),_ql=E(_qk.a),_qm=E(_qk.b);return (_ql>_qm)?E(_p6):(_qm-_ql|0)+1|0;},_qn=function(_qo,_qp){return E(_qo)-E(_qp)|0;},_qq=function(_qr,_qs){return new F(function(){return _qn(_qs,E(_qr).a);});},_qt=function(_qu,_qv){return E(_qu)==E(_qv);},_qw=function(_qx,_qy){return E(_qx)!=E(_qy);},_qz=new T2(0,_qt,_qw),_qA=function(_qB,_qC){var _qD=E(_qB),_qE=E(_qC);return (_qD>_qE)?E(_qD):E(_qE);},_qF=function(_qG,_qH){var _qI=E(_qG),_qJ=E(_qH);return (_qI>_qJ)?E(_qJ):E(_qI);},_qK=function(_qL,_qM){return (_qL>=_qM)?(_qL!=_qM)?2:1:0;},_qN=function(_qO,_qP){return new F(function(){return _qK(E(_qO),E(_qP));});},_qQ=function(_qR,_qS){return E(_qR)>=E(_qS);},_qT=function(_qU,_qV){return E(_qU)>E(_qV);},_qW=function(_qX,_qY){return E(_qX)<=E(_qY);},_qZ=function(_r0,_r1){return E(_r0)<E(_r1);},_r2={_:0,a:_qz,b:_qN,c:_qZ,d:_qW,e:_qT,f:_qQ,g:_qA,h:_qF},_r3={_:0,a:_r2,b:_qf,c:_q1,d:_qq,e:_oO,f:_qi,g:_oL},_r4=function(_r5,_r6,_){while(1){var _r7=B((function(_r8,_r9,_){var _ra=E(_r8);if(!_ra._){return new T2(0,_m2,_r9);}else{var _rb=B(A2(_ra.a,_r9,_));_r5=_ra.b;_r6=new T(function(){return E(E(_rb).b);});return __continue;}})(_r5,_r6,_));if(_r7!=__continue){return _r7;}}},_rc=function(_rd,_re){return new T2(1,_rd,_re);},_rf=function(_rg,_rh){var _ri=E(_rh);return new T2(0,_ri.a,_ri.b);},_rj=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_rk=new T(function(){return B(err(_rj));}),_rl=new T(function(){return B(unCStr("Negative range size"));}),_rm=new T(function(){return B(err(_rl));}),_rn=function(_ro){return E(E(_ro).f);},_rp=function(_rq){var _rr=B(A1(_rq,_));return E(_rr);},_rs=function(_rt,_ru,_rv){var _rw=E(_ru),_rx=_rw.a,_ry=_rw.b,_rz=function(_){var _rA=B(A2(_rn,_rt,_rw));if(_rA>=0){var _rB=newArr(_rA,_rk),_rC=_rB,_rD=E(_rA);if(!_rD){return new T(function(){return new T4(0,E(_rx),E(_ry),0,_rC);});}else{var _rE=function(_rF,_rG,_){while(1){var _rH=E(_rF);if(!_rH._){return E(_);}else{var _=_rC[_rG]=_rH.a;if(_rG!=(_rD-1|0)){var _rI=_rG+1|0;_rF=_rH.b;_rG=_rI;continue;}else{return E(_);}}}},_=B(_rE(_rv,0,_));return new T(function(){return new T4(0,E(_rx),E(_ry),_rD,_rC);});}}else{return E(_rm);}};return new F(function(){return _rp(_rz);});},_rJ=function(_rK,_rL,_rM,_rN){var _rO=new T(function(){var _rP=E(_rN),_rQ=_rP.c-1|0,_rR=new T(function(){return B(A2(_cF,_rL,_w));});if(0<=_rQ){var _rS=new T(function(){return B(_8F(_rL));}),_rT=function(_rU){var _rV=new T(function(){var _rW=new T(function(){return B(A1(_rM,new T(function(){return E(_rP.d[_rU]);})));});return B(A3(_8T,_rS,_rc,_rW));});return new F(function(){return A3(_8R,_rL,_rV,new T(function(){if(_rU!=_rQ){return B(_rT(_rU+1|0));}else{return E(_rR);}}));});};return B(_rT(0));}else{return E(_rR);}}),_rX=new T(function(){return B(_rf(_rK,_rN));});return new F(function(){return A3(_8T,B(_8F(_rL)),function(_rY){return new F(function(){return _rs(_rK,_rX,_rY);});},_rO);});},_rZ=function(_s0,_s1,_s2,_s3,_s4,_s5,_s6,_s7,_s8){var _s9=B(_8L(_s0));return new T2(0,new T3(0,E(B(A1(B(A1(_s9,_s1)),_s5))),E(B(A1(B(A1(_s9,_s2)),_s6))),E(B(A1(B(A1(_s9,_s3)),_s7)))),B(A1(B(A1(_s9,_s4)),_s8)));},_sa=function(_sb,_sc,_sd,_se,_sf,_sg,_sh,_si,_sj){var _sk=B(_6X(_sb));return new T2(0,new T3(0,E(B(A1(B(A1(_sk,_sc)),_sg))),E(B(A1(B(A1(_sk,_sd)),_sh))),E(B(A1(B(A1(_sk,_se)),_si)))),B(A1(B(A1(_sk,_sf)),_sj)));},_sl=function(_sm,_sn){return (E(_sm)!=E(_sn))?true:false;},_so=function(_sp,_sq){return E(_sp)==E(_sq);},_sr=new T2(0,_so,_sl),_ss=function(_st,_su){return E(_st)<E(_su);},_sv=function(_sw,_sx){return E(_sw)<=E(_sx);},_sy=function(_sz,_sA){return E(_sz)>E(_sA);},_sB=function(_sC,_sD){return E(_sC)>=E(_sD);},_sE=function(_sF,_sG){var _sH=E(_sF),_sI=E(_sG);return (_sH>=_sI)?(_sH!=_sI)?2:1:0;},_sJ=function(_sK,_sL){var _sM=E(_sK),_sN=E(_sL);return (_sM>_sN)?E(_sM):E(_sN);},_sO=function(_sP,_sQ){var _sR=E(_sP),_sS=E(_sQ);return (_sR>_sS)?E(_sS):E(_sR);},_sT={_:0,a:_sr,b:_sE,c:_ss,d:_sv,e:_sy,f:_sB,g:_sJ,h:_sO},_sU="dz",_sV="wy",_sW="wx",_sX="dy",_sY="dx",_sZ="t",_t0="a",_t1="r",_t2="ly",_t3="lx",_t4="wz",_t5=function(_t6,_t7,_t8,_t9,_ta,_tb,_tc,_td,_te){return new F(function(){return _m3(new T2(1,new T2(0,_sW,_t6),new T2(1,new T2(0,_sV,_t7),new T2(1,new T2(0,_t4,_t8),new T2(1,new T2(0,_t3,_t9*_ta*Math.cos(_tb)),new T2(1,new T2(0,_t2,_t9*_ta*Math.sin(_tb)),new T2(1,new T2(0,_t1,_t9),new T2(1,new T2(0,_t0,_ta),new T2(1,new T2(0,_sZ,_tb),new T2(1,new T2(0,_sY,_tc),new T2(1,new T2(0,_sX,_td),new T2(1,new T2(0,_sU,_te),_w))))))))))));});},_tf=function(_tg){var _th=E(_tg),_ti=E(_th.a),_tj=E(_th.b),_tk=E(_th.d);return new F(function(){return _t5(_ti.a,_ti.b,_ti.c,E(_tj.a),E(_tj.b),E(_th.c),_tk.a,_tk.b,_tk.c);});},_tl=function(_tm,_tn){var _to=E(_tn);return (_to._==0)?__Z:new T2(1,new T(function(){return B(A1(_tm,_to.a));}),new T(function(){return B(_tl(_tm,_to.b));}));},_tp=function(_tq,_tr,_ts){var _tt=__lst2arr(B(_tl(_tf,new T2(1,_tq,new T2(1,_tr,new T2(1,_ts,_w))))));return E(_tt);},_tu=function(_tv){var _tw=E(_tv);return new F(function(){return _tp(_tw.a,_tw.b,_tw.c);});},_tx=new T2(0,_o3,_sT),_ty=function(_tz,_tA,_tB,_tC,_tD,_tE,_tF){var _tG=B(_8J(B(_8H(_tz)))),_tH=new T(function(){return B(A3(_6X,_tG,new T(function(){return B(A3(_8L,_tG,_tA,_tD));}),new T(function(){return B(A3(_8L,_tG,_tB,_tE));})));});return new F(function(){return A3(_6X,_tG,_tH,new T(function(){return B(A3(_8L,_tG,_tC,_tF));}));});},_tI=function(_tJ,_tK,_tL,_tM){var _tN=B(_8H(_tJ)),_tO=new T(function(){return B(A2(_9t,_tJ,new T(function(){return B(_ty(_tJ,_tK,_tL,_tM,_tK,_tL,_tM));})));});return new T3(0,B(A3(_8P,_tN,_tK,_tO)),B(A3(_8P,_tN,_tL,_tO)),B(A3(_8P,_tN,_tM,_tO)));},_tP=function(_tQ,_tR,_tS,_tT,_tU,_tV,_tW){var _tX=B(_8L(_tQ));return new T3(0,B(A1(B(A1(_tX,_tR)),_tU)),B(A1(B(A1(_tX,_tS)),_tV)),B(A1(B(A1(_tX,_tT)),_tW)));},_tY=function(_tZ,_u0,_u1,_u2,_u3,_u4,_u5){var _u6=B(_6X(_tZ));return new T3(0,B(A1(B(A1(_u6,_u0)),_u3)),B(A1(B(A1(_u6,_u1)),_u4)),B(A1(B(A1(_u6,_u2)),_u5)));},_u7=function(_u8,_u9){var _ua=new T(function(){return E(E(_u8).a);}),_ub=new T(function(){var _uc=E(_u9),_ud=new T(function(){return B(_8J(new T(function(){return B(_8H(_ua));})));}),_ue=B(A2(_8s,_ud,_8q));return new T3(0,E(_ue),E(B(A2(_8s,_ud,_8r))),E(_ue));}),_uf=new T(function(){var _ug=E(_ub),_uh=B(_tI(_ua,_ug.a,_ug.b,_ug.c));return new T3(0,E(_uh.a),E(_uh.b),E(_uh.c));}),_ui=new T(function(){var _uj=E(_u9),_uk=_uj.b,_ul=E(_uf),_um=B(_8H(_ua)),_un=new T(function(){return B(A2(_9t,_ua,new T(function(){var _uo=E(_ub),_up=_uo.a,_uq=_uo.b,_ur=_uo.c;return B(_ty(_ua,_up,_uq,_ur,_up,_uq,_ur));})));}),_us=B(A3(_8P,_um,_uk,_un)),_ut=B(_8J(_um)),_uu=B(_tP(_ut,_ul.a,_ul.b,_ul.c,_us,_us,_us)),_uv=B(_6Z(_ut)),_uw=B(_tY(_ut,_uj.a,_uk,_uj.c,B(A1(_uv,_uu.a)),B(A1(_uv,_uu.b)),B(A1(_uv,_uu.c))));return new T3(0,E(_uw.a),E(_uw.b),E(_uw.c));});return new T2(0,_ui,_uf);},_ux=function(_uy){return E(E(_uy).a);},_uz=function(_uA,_uB,_uC,_uD,_uE,_uF,_uG){var _uH=B(_ty(_uA,_uE,_uF,_uG,_uB,_uC,_uD)),_uI=B(_8J(B(_8H(_uA)))),_uJ=B(_tP(_uI,_uE,_uF,_uG,_uH,_uH,_uH)),_uK=B(_6Z(_uI));return new F(function(){return _tY(_uI,_uB,_uC,_uD,B(A1(_uK,_uJ.a)),B(A1(_uK,_uJ.b)),B(A1(_uK,_uJ.c)));});},_uL=function(_uM){return E(E(_uM).a);},_uN=function(_uO,_uP,_uQ,_uR){var _uS=new T(function(){var _uT=E(_uR),_uU=E(_uQ),_uV=B(_uz(_uO,_uT.a,_uT.b,_uT.c,_uU.a,_uU.b,_uU.c));return new T3(0,E(_uV.a),E(_uV.b),E(_uV.c));}),_uW=new T(function(){return B(A2(_9t,_uO,new T(function(){var _uX=E(_uS),_uY=_uX.a,_uZ=_uX.b,_v0=_uX.c;return B(_ty(_uO,_uY,_uZ,_v0,_uY,_uZ,_v0));})));});if(!B(A3(_uL,B(_ux(_uP)),_uW,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_uO)))),_8q));})))){var _v1=E(_uS),_v2=B(_tI(_uO,_v1.a,_v1.b,_v1.c)),_v3=B(A2(_9t,_uO,new T(function(){var _v4=E(_uR),_v5=_v4.a,_v6=_v4.b,_v7=_v4.c;return B(_ty(_uO,_v5,_v6,_v7,_v5,_v6,_v7));}))),_v8=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_uO));})));})));return new T3(0,B(A1(B(A1(_v8,_v2.a)),_v3)),B(A1(B(A1(_v8,_v2.b)),_v3)),B(A1(B(A1(_v8,_v2.c)),_v3)));}else{var _v9=B(A2(_8s,B(_8J(B(_8H(_uO)))),_8q));return new T3(0,_v9,_v9,_v9);}},_va=0,_vb=new T3(0,E(_va),E(_va),E(_va)),_vc=function(_vd,_ve){while(1){var _vf=E(_vd);if(!_vf._){return E(_ve);}else{var _vg=_vf.b,_vh=E(_vf.a);if(_ve>_vh){_vd=_vg;continue;}else{_vd=_vg;_ve=_vh;continue;}}}},_vi=new T(function(){var _vj=eval("angleCount"),_vk=Number(_vj);return jsTrunc(_vk);}),_vl=new T(function(){return E(_vi);}),_vm=new T(function(){return B(unCStr("head"));}),_vn=new T(function(){return B(_pd(_vm));}),_vo=function(_vp,_vq,_vr){var _vs=E(_vp);if(!_vs._){return __Z;}else{var _vt=E(_vq);if(!_vt._){return __Z;}else{var _vu=_vt.a,_vv=E(_vr);if(!_vv._){return __Z;}else{var _vw=E(_vv.a),_vx=_vw.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_vs.a),E(_vu),E(_vx));}),new T2(1,new T(function(){return new T3(0,E(_vu),E(_vx),E(_vw.b));}),_w)),new T(function(){return B(_vo(_vs.b,_vt.b,_vv.b));},1));});}}}},_vy=new T(function(){return B(unCStr("tail"));}),_vz=new T(function(){return B(_pd(_vy));}),_vA=function(_vB,_vC){var _vD=E(_vB);if(!_vD._){return __Z;}else{var _vE=E(_vC);return (_vE._==0)?__Z:new T2(1,new T2(0,_vD.a,_vE.a),new T(function(){return B(_vA(_vD.b,_vE.b));}));}},_vF=function(_vG,_vH){var _vI=E(_vG);if(!_vI._){return __Z;}else{var _vJ=E(_vH);if(!_vJ._){return __Z;}else{var _vK=E(_vI.a),_vL=_vK.b,_vM=E(_vJ.a).b,_vN=new T(function(){var _vO=new T(function(){return B(_vA(_vM,new T(function(){var _vP=E(_vM);if(!_vP._){return E(_vz);}else{return E(_vP.b);}},1)));},1);return B(_vo(_vL,new T(function(){var _vQ=E(_vL);if(!_vQ._){return E(_vz);}else{return E(_vQ.b);}},1),_vO));});return new F(function(){return _n(new T2(1,new T(function(){var _vR=E(_vL);if(!_vR._){return E(_vn);}else{var _vS=E(_vM);if(!_vS._){return E(_vn);}else{return new T3(0,E(_vK.a),E(_vR.a),E(_vS.a));}}}),_vN),new T(function(){return B(_vF(_vI.b,_vJ.b));},1));});}}},_vT=new T(function(){return 6.283185307179586/E(_vl);}),_vU=new T(function(){return E(_vl)-1;}),_vV=new T1(0,1),_vW=function(_vX,_vY){var _vZ=E(_vY),_w0=new T(function(){var _w1=B(_8J(_vX)),_w2=B(_vW(_vX,B(A3(_6X,_w1,_vZ,new T(function(){return B(A2(_8s,_w1,_vV));})))));return new T2(1,_w2.a,_w2.b);});return new T2(0,_vZ,_w0);},_w3=function(_w4){return E(E(_w4).d);},_w5=new T1(0,2),_w6=function(_w7,_w8){var _w9=E(_w8);if(!_w9._){return __Z;}else{var _wa=_w9.a;return (!B(A1(_w7,_wa)))?__Z:new T2(1,_wa,new T(function(){return B(_w6(_w7,_w9.b));}));}},_wb=function(_wc,_wd,_we,_wf){var _wg=B(_vW(_wd,_we)),_wh=new T(function(){var _wi=B(_8J(_wd)),_wj=new T(function(){return B(A3(_8P,_wd,new T(function(){return B(A2(_8s,_wi,_vV));}),new T(function(){return B(A2(_8s,_wi,_w5));})));});return B(A3(_6X,_wi,_wf,_wj));});return new F(function(){return _w6(function(_wk){return new F(function(){return A3(_w3,_wc,_wk,_wh);});},new T2(1,_wg.a,_wg.b));});},_wl=new T(function(){return B(_wb(_sT,_nB,_va,_vU));}),_wm=function(_wn,_wo){while(1){var _wp=E(_wn);if(!_wp._){return E(_wo);}else{_wn=_wp.b;_wo=_wp.a;continue;}}},_wq=new T(function(){return B(unCStr("last"));}),_wr=new T(function(){return B(_pd(_wq));}),_ws=function(_wt){return new F(function(){return _wm(_wt,_wr);});},_wu=function(_wv){return new F(function(){return _ws(E(_wv).b);});},_ww=new T(function(){return B(unCStr("maximum"));}),_wx=new T(function(){return B(_pd(_ww));}),_wy=new T(function(){var _wz=eval("proceedCount"),_wA=Number(_wz);return jsTrunc(_wA);}),_wB=new T(function(){return E(_wy);}),_wC=1,_wD=new T(function(){return B(_wb(_sT,_nB,_wC,_wB));}),_wE=function(_wF,_wG,_wH,_wI,_wJ,_wK,_wL,_wM,_wN,_wO,_wP,_wQ,_wR,_wS){var _wT=new T(function(){var _wU=new T(function(){var _wV=E(_wO),_wW=E(_wS),_wX=E(_wR),_wY=E(_wP),_wZ=E(_wQ),_x0=E(_wN);return new T3(0,_wV*_wW-_wX*_wY,_wY*_wZ-_wW*_x0,_x0*_wX-_wZ*_wV);}),_x1=function(_x2){var _x3=new T(function(){var _x4=E(_x2)/E(_vl);return (_x4+_x4)*3.141592653589793;}),_x5=new T(function(){return B(A1(_wF,_x3));}),_x6=new T(function(){var _x7=new T(function(){var _x8=E(_x5)/E(_wB);return new T3(0,E(_x8),E(_x8),E(_x8));}),_x9=function(_xa,_xb){var _xc=E(_xa);if(!_xc._){return new T2(0,_w,_xb);}else{var _xd=new T(function(){var _xe=B(_u7(_tx,new T(function(){var _xf=E(_xb),_xg=E(_xf.a),_xh=E(_xf.b),_xi=E(_x7);return new T3(0,E(_xg.a)+E(_xh.a)*E(_xi.a),E(_xg.b)+E(_xh.b)*E(_xi.b),E(_xg.c)+E(_xh.c)*E(_xi.c));}))),_xj=_xe.a,_xk=new T(function(){var _xl=E(_xe.b),_xm=E(E(_xb).b),_xn=B(_uz(_o3,_xm.a,_xm.b,_xm.c,_xl.a,_xl.b,_xl.c)),_xo=B(_tI(_o3,_xn.a,_xn.b,_xn.c));return new T3(0,E(_xo.a),E(_xo.b),E(_xo.c));});return new T2(0,new T(function(){var _xp=E(_x5),_xq=E(_x3);return new T4(0,E(_xj),E(new T2(0,E(_xc.a)/E(_wB),E(_xp))),E(_xq),E(_xk));}),new T2(0,_xj,_xk));}),_xr=new T(function(){var _xs=B(_x9(_xc.b,new T(function(){return E(E(_xd).b);})));return new T2(0,_xs.a,_xs.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xd).a);}),new T(function(){return E(E(_xr).a);})),new T(function(){return E(E(_xr).b);}));}},_xt=function(_xu,_xv,_xw,_xx,_xy){var _xz=E(_xu);if(!_xz._){return new T2(0,_w,new T2(0,new T3(0,E(_xv),E(_xw),E(_xx)),_xy));}else{var _xA=new T(function(){var _xB=B(_u7(_tx,new T(function(){var _xC=E(_xy),_xD=E(_x7);return new T3(0,E(_xv)+E(_xC.a)*E(_xD.a),E(_xw)+E(_xC.b)*E(_xD.b),E(_xx)+E(_xC.c)*E(_xD.c));}))),_xE=_xB.a,_xF=new T(function(){var _xG=E(_xB.b),_xH=E(_xy),_xI=B(_uz(_o3,_xH.a,_xH.b,_xH.c,_xG.a,_xG.b,_xG.c)),_xJ=B(_tI(_o3,_xI.a,_xI.b,_xI.c));return new T3(0,E(_xJ.a),E(_xJ.b),E(_xJ.c));});return new T2(0,new T(function(){var _xK=E(_x5),_xL=E(_x3);return new T4(0,E(_xE),E(new T2(0,E(_xz.a)/E(_wB),E(_xK))),E(_xL),E(_xF));}),new T2(0,_xE,_xF));}),_xM=new T(function(){var _xN=B(_x9(_xz.b,new T(function(){return E(E(_xA).b);})));return new T2(0,_xN.a,_xN.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xA).a);}),new T(function(){return E(E(_xM).a);})),new T(function(){return E(E(_xM).b);}));}};return E(B(_xt(_wD,_wI,_wJ,_wK,new T(function(){var _xO=E(_wU),_xP=E(_x3)+_wL,_xQ=Math.cos(_xP),_xR=Math.sin(_xP);return new T3(0,E(_wN)*_xQ+E(_xO.a)*_xR,E(_wO)*_xQ+E(_xO.b)*_xR,E(_wP)*_xQ+E(_xO.c)*_xR);}))).a);});return new T2(0,new T(function(){var _xS=E(_x5),_xT=E(_x3);return new T4(0,E(new T3(0,E(_wI),E(_wJ),E(_wK))),E(new T2(0,E(_va),E(_xS))),E(_xT),E(_vb));}),_x6);};return B(_tl(_x1,_wl));}),_xU=new T(function(){var _xV=function(_xW){return new F(function(){return A1(_wF,new T(function(){return B(_nu(_xW,_vT));}));});},_xX=B(_tl(_xV,_wl));if(!_xX._){return E(_wx);}else{return B(_vc(_xX.b,E(_xX.a)));}}),_xY=new T(function(){var _xZ=new T(function(){var _y0=B(_n(_wT,new T2(1,new T(function(){var _y1=E(_wT);if(!_y1._){return E(_vn);}else{return E(_y1.a);}}),_w)));if(!_y0._){return E(_vz);}else{return E(_y0.b);}},1);return B(_vF(_wT,_xZ));});return new T3(0,_xY,new T(function(){return B(_tl(_wu,_wT));}),_xU);},_y2=function(_y3,_y4,_y5,_y6,_y7,_y8,_y9,_ya,_yb,_yc,_yd,_ye,_yf,_yg,_yh,_yi,_yj,_yk){var _yl=B(_u7(_tx,new T3(0,E(_y6),E(_y7),E(_y8)))),_ym=_yl.b,_yn=E(_yl.a),_yo=B(_uN(_o3,_sT,_ym,new T3(0,E(_ya),E(_yb),E(_yc)))),_yp=E(_ym),_yq=_yp.a,_yr=_yp.b,_ys=_yp.c,_yt=B(_uz(_o3,_ye,_yf,_yg,_yq,_yr,_ys)),_yu=B(_tI(_o3,_yt.a,_yt.b,_yt.c)),_yv=_yu.a,_yw=_yu.b,_yx=_yu.c,_yy=E(_y9),_yz=new T2(0,E(new T3(0,E(_yo.a),E(_yo.b),E(_yo.c))),E(_yd)),_yA=B(_wE(_y3,_y4,_y5,_yn.a,_yn.b,_yn.c,_yy,_yz,_yv,_yw,_yx,_yq,_yr,_ys)),_yB=__lst2arr(B(_tl(_tu,_yA.a))),_yC=__lst2arr(B(_tl(_tf,_yA.b)));return {_:0,a:_y3,b:_y4,c:_y5,d:new T2(0,E(_yn),E(_yy)),e:_yz,f:new T3(0,E(_yv),E(_yw),E(_yx)),g:_yp,h:_yB,i:_yC,j:E(_yA.c)};},_yD=1.0e-2,_yE=function(_yF,_yG,_yH,_yI,_yJ,_yK,_yL,_yM,_yN,_yO,_yP,_yQ,_yR,_yS,_yT,_yU,_yV,_yW){var _yX=B(_rZ(_nx,_yM,_yN,_yO,_yP,_yD,_yD,_yD,_yD)),_yY=E(_yX.a),_yZ=B(_sa(_nx,_yI,_yJ,_yK,_yL,_yY.a,_yY.b,_yY.c,_yX.b)),_z0=E(_yZ.a);return new F(function(){return _y2(_yF,_yG,_yH,_z0.a,_z0.b,_z0.c,_yZ.b,_yM,_yN,_yO,_yP,_yQ,_yR,_yS,_yT,_yU,_yV,_yW);});},_z1=function(_z2){var _z3=E(_z2),_z4=E(_z3.d),_z5=E(_z4.a),_z6=E(_z3.e),_z7=E(_z6.a),_z8=E(_z3.f),_z9=B(_yE(_z3.a,_z3.b,_z3.c,_z5.a,_z5.b,_z5.c,_z4.b,_z7.a,_z7.b,_z7.c,_z6.b,_z8.a,_z8.b,_z8.c,_z3.g,_z3.h,_z3.i,_z3.j));return {_:0,a:E(_z9.a),b:E(_z9.b),c:E(_z9.c),d:E(_z9.d),e:E(_z9.e),f:E(_z9.f),g:E(_z9.g),h:_z9.h,i:_z9.i,j:_z9.j};},_za=function(_zb,_zc,_zd,_ze,_zf,_zg,_zh,_zi,_zj){var _zk=B(_8J(B(_8H(_zb))));return new F(function(){return A3(_6X,_zk,new T(function(){return B(_ty(_zb,_zc,_zd,_ze,_zg,_zh,_zi));}),new T(function(){return B(A3(_8L,_zk,_zf,_zj));}));});},_zl=new T(function(){return B(unCStr("base"));}),_zm=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_zn=new T(function(){return B(unCStr("IOException"));}),_zo=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zl,_zm,_zn),_zp=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zo,_w,_w),_zq=function(_zr){return E(_zp);},_zs=function(_zt){var _zu=E(_zt);return new F(function(){return _2n(B(_2l(_zu.a)),_zq,_zu.b);});},_zv=new T(function(){return B(unCStr(": "));}),_zw=new T(function(){return B(unCStr(")"));}),_zx=new T(function(){return B(unCStr(" ("));}),_zy=new T(function(){return B(unCStr("interrupted"));}),_zz=new T(function(){return B(unCStr("system error"));}),_zA=new T(function(){return B(unCStr("unsatisified constraints"));}),_zB=new T(function(){return B(unCStr("user error"));}),_zC=new T(function(){return B(unCStr("permission denied"));}),_zD=new T(function(){return B(unCStr("illegal operation"));}),_zE=new T(function(){return B(unCStr("end of file"));}),_zF=new T(function(){return B(unCStr("resource exhausted"));}),_zG=new T(function(){return B(unCStr("resource busy"));}),_zH=new T(function(){return B(unCStr("does not exist"));}),_zI=new T(function(){return B(unCStr("already exists"));}),_zJ=new T(function(){return B(unCStr("resource vanished"));}),_zK=new T(function(){return B(unCStr("timeout"));}),_zL=new T(function(){return B(unCStr("unsupported operation"));}),_zM=new T(function(){return B(unCStr("hardware fault"));}),_zN=new T(function(){return B(unCStr("inappropriate type"));}),_zO=new T(function(){return B(unCStr("invalid argument"));}),_zP=new T(function(){return B(unCStr("failed"));}),_zQ=new T(function(){return B(unCStr("protocol error"));}),_zR=function(_zS,_zT){switch(E(_zS)){case 0:return new F(function(){return _n(_zI,_zT);});break;case 1:return new F(function(){return _n(_zH,_zT);});break;case 2:return new F(function(){return _n(_zG,_zT);});break;case 3:return new F(function(){return _n(_zF,_zT);});break;case 4:return new F(function(){return _n(_zE,_zT);});break;case 5:return new F(function(){return _n(_zD,_zT);});break;case 6:return new F(function(){return _n(_zC,_zT);});break;case 7:return new F(function(){return _n(_zB,_zT);});break;case 8:return new F(function(){return _n(_zA,_zT);});break;case 9:return new F(function(){return _n(_zz,_zT);});break;case 10:return new F(function(){return _n(_zQ,_zT);});break;case 11:return new F(function(){return _n(_zP,_zT);});break;case 12:return new F(function(){return _n(_zO,_zT);});break;case 13:return new F(function(){return _n(_zN,_zT);});break;case 14:return new F(function(){return _n(_zM,_zT);});break;case 15:return new F(function(){return _n(_zL,_zT);});break;case 16:return new F(function(){return _n(_zK,_zT);});break;case 17:return new F(function(){return _n(_zJ,_zT);});break;default:return new F(function(){return _n(_zy,_zT);});}},_zU=new T(function(){return B(unCStr("}"));}),_zV=new T(function(){return B(unCStr("{handle: "));}),_zW=function(_zX,_zY,_zZ,_A0,_A1,_A2){var _A3=new T(function(){var _A4=new T(function(){var _A5=new T(function(){var _A6=E(_A0);if(!_A6._){return E(_A2);}else{var _A7=new T(function(){return B(_n(_A6,new T(function(){return B(_n(_zw,_A2));},1)));},1);return B(_n(_zx,_A7));}},1);return B(_zR(_zY,_A5));}),_A8=E(_zZ);if(!_A8._){return E(_A4);}else{return B(_n(_A8,new T(function(){return B(_n(_zv,_A4));},1)));}}),_A9=E(_A1);if(!_A9._){var _Aa=E(_zX);if(!_Aa._){return E(_A3);}else{var _Ab=E(_Aa.a);if(!_Ab._){var _Ac=new T(function(){var _Ad=new T(function(){return B(_n(_zU,new T(function(){return B(_n(_zv,_A3));},1)));},1);return B(_n(_Ab.a,_Ad));},1);return new F(function(){return _n(_zV,_Ac);});}else{var _Ae=new T(function(){var _Af=new T(function(){return B(_n(_zU,new T(function(){return B(_n(_zv,_A3));},1)));},1);return B(_n(_Ab.a,_Af));},1);return new F(function(){return _n(_zV,_Ae);});}}}else{return new F(function(){return _n(_A9.a,new T(function(){return B(_n(_zv,_A3));},1));});}},_Ag=function(_Ah){var _Ai=E(_Ah);return new F(function(){return _zW(_Ai.a,_Ai.b,_Ai.c,_Ai.d,_Ai.f,_w);});},_Aj=function(_Ak,_Al,_Am){var _An=E(_Al);return new F(function(){return _zW(_An.a,_An.b,_An.c,_An.d,_An.f,_Am);});},_Ao=function(_Ap,_Aq){var _Ar=E(_Ap);return new F(function(){return _zW(_Ar.a,_Ar.b,_Ar.c,_Ar.d,_Ar.f,_Aq);});},_As=function(_At,_Au){return new F(function(){return _2Q(_Ao,_At,_Au);});},_Av=new T3(0,_Aj,_Ag,_As),_Aw=new T(function(){return new T5(0,_zq,_Av,_Ax,_zs,_Ag);}),_Ax=function(_Ay){return new T2(0,_Aw,_Ay);},_Az=__Z,_AA=7,_AB=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_AC=new T6(0,_Az,_AA,_w,_AB,_Az,_Az),_AD=new T(function(){return B(_Ax(_AC));}),_AE=function(_){return new F(function(){return die(_AD);});},_AF=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_AG=new T6(0,_Az,_AA,_w,_AF,_Az,_Az),_AH=new T(function(){return B(_Ax(_AG));}),_AI=function(_){return new F(function(){return die(_AH);});},_AJ=function(_AK,_){return new T2(0,_w,_AK);},_AL=0.6,_AM=1,_AN=new T(function(){return B(unCStr(")"));}),_AO=function(_AP,_AQ){var _AR=new T(function(){var _AS=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mn(0,_AP,_w)),_AN));})));},1);return B(_n(B(_mn(0,_AQ,_w)),_AS));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_AR)));});},_AT=function(_AU,_AV){var _AW=new T(function(){var _AX=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mn(0,_AV,_w)),_AN));})));},1);return B(_n(B(_mn(0,_AU,_w)),_AX));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_AW)));});},_AY=function(_AZ){var _B0=E(_AZ);if(!_B0._){return E(_AJ);}else{var _B1=new T(function(){return B(_AY(_B0.b));}),_B2=function(_B3){var _B4=E(_B3);if(!_B4._){return E(_B1);}else{var _B5=_B4.a,_B6=new T(function(){return B(_B2(_B4.b));}),_B7=new T(function(){return 0.1*E(E(_B5).e)/1.0e-2;}),_B8=new T(function(){var _B9=E(_B5);if(_B9.a!=_B9.b){return E(_AM);}else{return E(_AL);}}),_Ba=function(_Bb,_){var _Bc=E(_Bb),_Bd=_Bc.c,_Be=_Bc.d,_Bf=E(_Bc.a),_Bg=E(_Bc.b),_Bh=E(_B5),_Bi=_Bh.a,_Bj=_Bh.b,_Bk=E(_Bh.c),_Bl=_Bk.b,_Bm=E(_Bk.a),_Bn=_Bm.a,_Bo=_Bm.b,_Bp=_Bm.c,_Bq=E(_Bh.d),_Br=_Bq.b,_Bs=E(_Bq.a),_Bt=_Bs.a,_Bu=_Bs.b,_Bv=_Bs.c;if(_Bf>_Bi){return new F(function(){return _AI(_);});}else{if(_Bi>_Bg){return new F(function(){return _AI(_);});}else{if(_Bf>_Bj){return new F(function(){return _AE(_);});}else{if(_Bj>_Bg){return new F(function(){return _AE(_);});}else{var _Bw=_Bi-_Bf|0;if(0>_Bw){return new F(function(){return _AO(_Bd,_Bw);});}else{if(_Bw>=_Bd){return new F(function(){return _AO(_Bd,_Bw);});}else{var _Bx=E(_Be[_Bw]),_By=E(_Bx.c),_Bz=_By.b,_BA=E(_By.a),_BB=_BA.a,_BC=_BA.b,_BD=_BA.c,_BE=E(_Bx.e),_BF=E(_BE.a),_BG=B(_rZ(_nx,_Bn,_Bo,_Bp,_Bl,_BB,_BC,_BD,_Bz)),_BH=E(_BG.a),_BI=B(_rZ(_nx,_BH.a,_BH.b,_BH.c,_BG.b,_Bn,_Bo,_Bp,_Bl)),_BJ=E(_BI.a),_BK=_Bj-_Bf|0;if(0>_BK){return new F(function(){return _AT(_BK,_Bd);});}else{if(_BK>=_Bd){return new F(function(){return _AT(_BK,_Bd);});}else{var _BL=E(_Be[_BK]),_BM=E(_BL.c),_BN=_BM.b,_BO=E(_BM.a),_BP=_BO.a,_BQ=_BO.b,_BR=_BO.c,_BS=E(_BL.e),_BT=E(_BS.a),_BU=B(_rZ(_nx,_Bt,_Bu,_Bv,_Br,_BP,_BQ,_BR,_BN)),_BV=E(_BU.a),_BW=B(_rZ(_nx,_BV.a,_BV.b,_BV.c,_BU.b,_Bt,_Bu,_Bv,_Br)),_BX=E(_BW.a),_BY=E(_BJ.a)+E(_BJ.b)+E(_BJ.c)+E(_BI.b)+E(_BX.a)+E(_BX.b)+E(_BX.c)+E(_BW.b);if(!_BY){var _BZ=B(A2(_B6,_Bc,_));return new T2(0,new T2(1,_m2,new T(function(){return E(E(_BZ).a);})),new T(function(){return E(E(_BZ).b);}));}else{var _C0=new T(function(){return  -((B(_za(_o3,_BF.a,_BF.b,_BF.c,_BE.b,_Bn,_Bo,_Bp,_Bl))-B(_za(_o3,_BT.a,_BT.b,_BT.c,_BS.b,_Bt,_Bu,_Bv,_Br))-E(_B7))/_BY);}),_C1=function(_C2,_C3,_C4,_C5,_){var _C6=new T(function(){var _C7=function(_C8,_C9,_Ca,_Cb,_Cc){if(_C8>_Bj){return E(_Cc);}else{if(_Bj>_C9){return E(_Cc);}else{var _Cd=function(_){var _Ce=newArr(_Ca,_rk),_Cf=_Ce,_Cg=function(_Ch,_){while(1){if(_Ch!=_Ca){var _=_Cf[_Ch]=_Cb[_Ch],_Ci=_Ch+1|0;_Ch=_Ci;continue;}else{return E(_);}}},_=B(_Cg(0,_)),_Cj=_Bj-_C8|0;if(0>_Cj){return new F(function(){return _AT(_Cj,_Ca);});}else{if(_Cj>=_Ca){return new F(function(){return _AT(_Cj,_Ca);});}else{var _=_Cf[_Cj]=new T(function(){var _Ck=E(_Cb[_Cj]),_Cl=E(_Ck.e),_Cm=E(_Cl.a),_Cn=B(_rZ(_nx,_BP,_BQ,_BR,_BN,_Bt,_Bu,_Bv,_Br)),_Co=E(_Cn.a),_Cp=E(_C0)*E(_B8),_Cq=B(_rZ(_nx,_Co.a,_Co.b,_Co.c,_Cn.b,_Cp,_Cp,_Cp,_Cp)),_Cr=E(_Cq.a),_Cs=B(_sa(_nx,_Cm.a,_Cm.b,_Cm.c,_Cl.b, -E(_Cr.a), -E(_Cr.b), -E(_Cr.c), -E(_Cq.b)));return {_:0,a:E(_Ck.a),b:E(_Ck.b),c:E(_Ck.c),d:E(_Ck.d),e:E(new T2(0,E(_Cs.a),E(_Cs.b))),f:E(_Ck.f),g:E(_Ck.g),h:_Ck.h,i:_Ck.i,j:_Ck.j};});return new T4(0,E(_C8),E(_C9),_Ca,_Cf);}}};return new F(function(){return _rp(_Cd);});}}};if(_C2>_Bi){return B(_C7(_C2,_C3,_C4,_C5,new T4(0,E(_C2),E(_C3),_C4,_C5)));}else{if(_Bi>_C3){return B(_C7(_C2,_C3,_C4,_C5,new T4(0,E(_C2),E(_C3),_C4,_C5)));}else{var _Ct=function(_){var _Cu=newArr(_C4,_rk),_Cv=_Cu,_Cw=function(_Cx,_){while(1){if(_Cx!=_C4){var _=_Cv[_Cx]=_C5[_Cx],_Cy=_Cx+1|0;_Cx=_Cy;continue;}else{return E(_);}}},_=B(_Cw(0,_)),_Cz=_Bi-_C2|0;if(0>_Cz){return new F(function(){return _AO(_C4,_Cz);});}else{if(_Cz>=_C4){return new F(function(){return _AO(_C4,_Cz);});}else{var _=_Cv[_Cz]=new T(function(){var _CA=E(_C5[_Cz]),_CB=E(_CA.e),_CC=E(_CB.a),_CD=B(_rZ(_nx,_BB,_BC,_BD,_Bz,_Bn,_Bo,_Bp,_Bl)),_CE=E(_CD.a),_CF=E(_C0)*E(_B8),_CG=B(_rZ(_nx,_CE.a,_CE.b,_CE.c,_CD.b,_CF,_CF,_CF,_CF)),_CH=E(_CG.a),_CI=B(_sa(_nx,_CC.a,_CC.b,_CC.c,_CB.b,_CH.a,_CH.b,_CH.c,_CG.b));return {_:0,a:E(_CA.a),b:E(_CA.b),c:E(_CA.c),d:E(_CA.d),e:E(new T2(0,E(_CI.a),E(_CI.b))),f:E(_CA.f),g:E(_CA.g),h:_CA.h,i:_CA.i,j:_CA.j};});return new T4(0,E(_C2),E(_C3),_C4,_Cv);}}},_CJ=B(_rp(_Ct));return B(_C7(E(_CJ.a),E(_CJ.b),_CJ.c,_CJ.d,_CJ));}}});return new T2(0,_m2,_C6);};if(!E(_Bh.f)){var _CK=B(_C1(_Bf,_Bg,_Bd,_Be,_)),_CL=B(A2(_B6,new T(function(){return E(E(_CK).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CK).a);}),new T(function(){return E(E(_CL).a);})),new T(function(){return E(E(_CL).b);}));}else{if(E(_C0)<0){var _CM=B(A2(_B6,_Bc,_));return new T2(0,new T2(1,_m2,new T(function(){return E(E(_CM).a);})),new T(function(){return E(E(_CM).b);}));}else{var _CN=B(_C1(_Bf,_Bg,_Bd,_Be,_)),_CO=B(A2(_B6,new T(function(){return E(E(_CN).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CN).a);}),new T(function(){return E(E(_CO).a);})),new T(function(){return E(E(_CO).b);}));}}}}}}}}}}}};return E(_Ba);}};return new F(function(){return _B2(_B0.a);});}},_CP=function(_,_CQ){var _CR=new T(function(){return B(_AY(E(_CQ).a));}),_CS=function(_CT){var _CU=E(_CT);return (_CU==1)?E(new T2(1,_CR,_w)):new T2(1,_CR,new T(function(){return B(_CS(_CU-1|0));}));},_CV=B(_r4(B(_CS(5)),new T(function(){return E(E(_CQ).b);}),_)),_CW=new T(function(){return B(_rJ(_r3,_mP,_z1,new T(function(){return E(E(_CV).b);})));});return new T2(0,_m2,_CW);},_CX=function(_CY,_CZ,_D0,_D1,_D2){var _D3=B(_8J(B(_8H(_CY))));return new F(function(){return A3(_6X,_D3,new T(function(){return B(A3(_8L,_D3,_CZ,_D1));}),new T(function(){return B(A3(_8L,_D3,_D0,_D2));}));});},_D4=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_D5=new T6(0,_Az,_AA,_w,_D4,_Az,_Az),_D6=new T(function(){return B(_Ax(_D5));}),_D7=function(_){return new F(function(){return die(_D6);});},_D8=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_D9=new T6(0,_Az,_AA,_w,_D8,_Az,_Az),_Da=new T(function(){return B(_Ax(_D9));}),_Db=function(_){return new F(function(){return die(_Da);});},_Dc=function(_Dd,_De,_Df,_Dg){var _Dh=new T(function(){return B(_8J(new T(function(){return B(_8H(_Dd));})));}),_Di=B(A2(_8s,_Dh,_8q));return new F(function(){return _tI(_Dd,_Di,B(A2(_8s,_Dh,_8r)),_Di);});},_Dj=false,_Dk=true,_Dl=function(_Dm){var _Dn=E(_Dm),_Do=_Dn.b,_Dp=E(_Dn.d),_Dq=E(_Dn.e),_Dr=E(_Dq.a),_Ds=E(_Dn.g),_Dt=B(A1(_Do,_Dp.a)),_Du=B(_uz(_o3,_Dt.a,_Dt.b,_Dt.c,_Ds.a,_Ds.b,_Ds.c));return {_:0,a:E(_Dn.a),b:E(_Do),c:E(_Dn.c),d:E(_Dp),e:E(new T2(0,E(new T3(0,E(_Dr.a)+E(_Du.a)*1.0e-2,E(_Dr.b)+E(_Du.b)*1.0e-2,E(_Dr.c)+E(_Du.c)*1.0e-2)),E(_Dq.b))),f:E(_Dn.f),g:E(_Ds),h:_Dn.h,i:_Dn.i,j:_Dn.j};},_Dv=new T(function(){return eval("__strict(collideBound)");}),_Dw=new T(function(){return eval("__strict(mouseContact)");}),_Dx=new T(function(){return eval("__strict(collide)");}),_Dy=function(_Dz){var _DA=E(_Dz);if(!_DA._){return __Z;}else{return new F(function(){return _n(_DA.a,new T(function(){return B(_Dy(_DA.b));},1));});}},_DB=0,_DC=new T3(0,E(_DB),E(_DB),E(_DB)),_DD=new T2(0,E(_DC),E(_DB)),_DE=function(_DF,_){var _DG=B(_rJ(_r3,_mP,_Dl,_DF)),_DH=E(_DG.a),_DI=E(_DG.b);if(_DH<=_DI){var _DJ=function(_DK,_DL,_DM,_DN,_DO,_){if(_DL>_DK){return new F(function(){return _Db(_);});}else{if(_DK>_DM){return new F(function(){return _Db(_);});}else{var _DP=new T(function(){var _DQ=_DK-_DL|0;if(0>_DQ){return B(_AT(_DQ,_DN));}else{if(_DQ>=_DN){return B(_AT(_DQ,_DN));}else{return E(_DO[_DQ]);}}}),_DR=function(_DS,_DT,_DU,_DV,_DW,_){var _DX=E(_DS);if(!_DX._){return new T2(0,_w,new T4(0,E(_DT),E(_DU),_DV,_DW));}else{var _DY=E(_DX.a);if(_DT>_DY){return new F(function(){return _D7(_);});}else{if(_DY>_DU){return new F(function(){return _D7(_);});}else{var _DZ=_DY-_DT|0;if(0>_DZ){return new F(function(){return _AO(_DV,_DZ);});}else{if(_DZ>=_DV){return new F(function(){return _AO(_DV,_DZ);});}else{var _E0=__app2(E(_Dx),B(_md(E(_DP))),B(_md(E(_DW[_DZ])))),_E1=__arr2lst(0,_E0),_E2=B(_oG(_E1,_)),_E3=B(_DR(_DX.b,_DT,_DU,_DV,_DW,_)),_E4=new T(function(){var _E5=new T(function(){return _DK!=_DY;}),_E6=function(_E7){var _E8=E(_E7);if(!_E8._){return __Z;}else{var _E9=_E8.b,_Ea=E(_E8.a),_Eb=E(_Ea.b),_Ec=E(_Ea.a),_Ed=E(_Ec.a),_Ee=E(_Ec.b),_Ef=E(_Ec.c),_Eg=E(_Eb.a),_Eh=E(_Eb.b),_Ei=E(_Eb.c),_Ej=E(_Ea.c),_Ek=_Ej.a,_El=_Ej.b,_Em=E(_Ea.e),_En=E(_Ea.d),_Eo=_En.a,_Ep=_En.b,_Eq=E(_Ea.f),_Er=new T(function(){var _Es=B(_tI(_o3,_Eq.a,_Eq.b,_Eq.c)),_Et=Math.sqrt(B(_CX(_o3,_Eo,_Ep,_Eo,_Ep)));return new T3(0,_Et*E(_Es.a),_Et*E(_Es.b),_Et*E(_Es.c));}),_Eu=new T(function(){var _Ev=B(_tI(_o3,_Em.a,_Em.b,_Em.c)),_Ew=Math.sqrt(B(_CX(_o3,_Ek,_El,_Ek,_El)));return new T3(0,_Ew*E(_Ev.a),_Ew*E(_Ev.b),_Ew*E(_Ev.c));}),_Ex=new T(function(){var _Ey=B(_Dc(_o3,_Eg,_Eh,_Ei));return new T3(0,E(_Ey.a),E(_Ey.b),E(_Ey.c));}),_Ez=new T(function(){var _EA=B(_Dc(_o3,_Ed,_Ee,_Ef));return new T3(0,E(_EA.a),E(_EA.b),E(_EA.c));}),_EB=_Eg+ -_Ed,_EC=_Eh+ -_Ee,_ED=_Ei+ -_Ef,_EE=new T(function(){return Math.sqrt(B(_ty(_o3,_EB,_EC,_ED,_EB,_EC,_ED)));}),_EF=new T(function(){var _EG=1/E(_EE);return new T3(0,_EB*_EG,_EC*_EG,_ED*_EG);}),_EH=new T(function(){if(!E(_Ea.g)){return E(_EF);}else{var _EI=E(_EF);return new T3(0,-1*E(_EI.a),-1*E(_EI.b),-1*E(_EI.c));}}),_EJ=new T(function(){if(!E(_Ea.h)){return E(_EF);}else{var _EK=E(_EF);return new T3(0,-1*E(_EK.a),-1*E(_EK.b),-1*E(_EK.c));}});return (!E(_E5))?new T2(1,new T(function(){var _EL=E(_EH),_EM=E(_EL.b),_EN=E(_EL.c),_EO=E(_EL.a),_EP=E(_Ez),_EQ=E(_EP.c),_ER=E(_EP.b),_ES=E(_EP.a),_ET=E(_Eu),_EU=E(_ET.c),_EV=E(_ET.b),_EW=E(_ET.a),_EX=_EM*_EQ-_ER*_EN,_EY=_EN*_ES-_EQ*_EO,_EZ=_EO*_ER-_ES*_EM,_F0=B(_ty(_o3,_EY*_EU-_EV*_EZ,_EZ*_EW-_EU*_EX,_EX*_EV-_EW*_EY,_ES,_ER,_EQ));return new T6(0,_DK,_DY,E(new T2(0,E(new T3(0,E(_EX),E(_EY),E(_EZ))),E(_F0))),E(_DD),_EE,_Dj);}),new T2(1,new T(function(){var _F1=E(_EJ),_F2=E(_F1.b),_F3=E(_F1.c),_F4=E(_F1.a),_F5=E(_Ex),_F6=E(_F5.c),_F7=E(_F5.b),_F8=E(_F5.a),_F9=E(_Er),_Fa=E(_F9.c),_Fb=E(_F9.b),_Fc=E(_F9.a),_Fd=_F2*_F6-_F7*_F3,_Fe=_F3*_F8-_F6*_F4,_Ff=_F4*_F7-_F8*_F2,_Fg=B(_ty(_o3,_Fe*_Fa-_Fb*_Ff,_Ff*_Fc-_Fa*_Fd,_Fd*_Fb-_Fc*_Fe,_F8,_F7,_F6));return new T6(0,_DK,_DY,E(_DD),E(new T2(0,E(new T3(0,E(_Fd),E(_Fe),E(_Ff))),E(_Fg))),_EE,_Dj);}),new T(function(){return B(_E6(_E9));}))):new T2(1,new T(function(){var _Fh=E(_EH),_Fi=E(_Fh.b),_Fj=E(_Fh.c),_Fk=E(_Fh.a),_Fl=E(_Ez),_Fm=_Fl.a,_Fn=_Fl.b,_Fo=_Fl.c,_Fp=B(_uz(_o3,_Fk,_Fi,_Fj,_Fm,_Fn,_Fo)),_Fq=E(_Eu),_Fr=E(_Fq.c),_Fs=E(_Fq.b),_Ft=E(_Fq.a),_Fu=B(_ty(_o3,_Fi*_Fr-_Fs*_Fj,_Fj*_Ft-_Fr*_Fk,_Fk*_Fs-_Ft*_Fi,_Fm,_Fn,_Fo)),_Fv=E(_EJ),_Fw=E(_Fv.b),_Fx=E(_Fv.c),_Fy=E(_Fv.a),_Fz=E(_Ex),_FA=_Fz.a,_FB=_Fz.b,_FC=_Fz.c,_FD=B(_uz(_o3,_Fy,_Fw,_Fx,_FA,_FB,_FC)),_FE=E(_Er),_FF=E(_FE.c),_FG=E(_FE.b),_FH=E(_FE.a),_FI=B(_ty(_o3,_Fw*_FF-_FG*_Fx,_Fx*_FH-_FF*_Fy,_Fy*_FG-_FH*_Fw,_FA,_FB,_FC));return new T6(0,_DK,_DY,E(new T2(0,E(new T3(0,E(_Fp.a),E(_Fp.b),E(_Fp.c))),E(_Fu))),E(new T2(0,E(new T3(0,E(_FD.a),E(_FD.b),E(_FD.c))),E(_FI))),_EE,_Dk);}),new T(function(){return B(_E6(_E9));}));}};return B(_E6(_E2));});return new T2(0,new T2(1,_E4,new T(function(){return E(E(_E3).a);})),new T(function(){return E(E(_E3).b);}));}}}}}},_FJ=B(_DR(B(_q7(_DK,_DI)),_DL,_DM,_DN,_DO,_)),_FK=E(_DP),_FL=E(_FK.d).a,_FM=__app1(E(_Dv),B(_md(_FK))),_FN=__arr2lst(0,_FM),_FO=B(_oG(_FN,_)),_FP=__app1(E(_Dw),_DK),_FQ=__arr2lst(0,_FP),_FR=B(_oG(_FQ,_));if(_DK!=_DI){var _FS=E(_FJ),_FT=E(_FS.b),_FU=B(_DJ(_DK+1|0,E(_FT.a),E(_FT.b),_FT.c,_FT.d,_)),_FV=new T(function(){var _FW=new T(function(){var _FX=E(_FL),_FY=B(_Dc(_o3,_FX.a,_FX.b,_FX.c));return new T3(0,E(_FY.a),E(_FY.b),E(_FY.c));}),_FZ=new T(function(){var _G0=new T(function(){return B(_Dy(_FS.a));}),_G1=function(_G2){var _G3=E(_G2);if(!_G3._){return E(_G0);}else{var _G4=E(_G3.a),_G5=E(_G4.b),_G6=E(_G4.a),_G7=E(_G6.a),_G8=E(_G6.b),_G9=E(_G6.c),_Ga=E(_G4.c),_Gb=_Ga.a,_Gc=_Ga.b,_Gd=E(_G4.e);return new T2(1,new T(function(){var _Ge=E(_G5.a)+ -_G7,_Gf=E(_G5.b)+ -_G8,_Gg=E(_G5.c)+ -_G9,_Gh=B(_Dc(_o3,_G7,_G8,_G9)),_Gi=_Gh.a,_Gj=_Gh.b,_Gk=_Gh.c,_Gl=Math.sqrt(B(_ty(_o3,_Ge,_Gf,_Gg,_Ge,_Gf,_Gg))),_Gm=1/_Gl,_Gn=_Ge*_Gm,_Go=_Gf*_Gm,_Gp=_Gg*_Gm,_Gq=B(_uz(_o3,_Gn,_Go,_Gp,_Gi,_Gj,_Gk)),_Gr=B(_tI(_o3,_Gd.a,_Gd.b,_Gd.c)),_Gs=Math.sqrt(B(_CX(_o3,_Gb,_Gc,_Gb,_Gc))),_Gt=_Gs*E(_Gr.a),_Gu=_Gs*E(_Gr.b),_Gv=_Gs*E(_Gr.c),_Gw=B(_ty(_o3,_Go*_Gv-_Gu*_Gp,_Gp*_Gt-_Gv*_Gn,_Gn*_Gu-_Gt*_Go,_Gi,_Gj,_Gk));return new T6(0,_DK,_DK,E(new T2(0,E(new T3(0,E(_Gq.a),E(_Gq.b),E(_Gq.c))),E(_Gw))),E(_DD),_Gl,_Dk);}),new T(function(){return B(_G1(_G3.b));}));}};return B(_G1(_FO));}),_Gx=function(_Gy){var _Gz=E(_Gy);if(!_Gz._){return E(_FZ);}else{var _GA=E(_Gz.a),_GB=E(_GA.b),_GC=new T(function(){var _GD=E(_FL),_GE=E(_GB.c)+ -E(_GD.c),_GF=E(_GB.b)+ -E(_GD.b),_GG=E(_GB.a)+ -E(_GD.a),_GH=Math.sqrt(B(_ty(_o3,_GG,_GF,_GE,_GG,_GF,_GE))),_GI=function(_GJ,_GK,_GL){var _GM=E(_FW),_GN=_GM.a,_GO=_GM.b,_GP=_GM.c,_GQ=B(_uz(_o3,_GJ,_GK,_GL,_GN,_GO,_GP)),_GR=B(_ty(_o3,_GK*0-0*_GL,_GL*0-0*_GJ,_GJ*0-0*_GK,_GN,_GO,_GP));return new T6(0,_DK,_DK,new T2(0,E(new T3(0,E(_GQ.a),E(_GQ.b),E(_GQ.c))),E(_GR)),_DD,_GH,_Dk);};if(!E(_GA.g)){var _GS=1/_GH,_GT=B(_GI(_GG*_GS,_GF*_GS,_GE*_GS));return new T6(0,_GT.a,_GT.b,E(_GT.c),E(_GT.d),_GT.e,_GT.f);}else{var _GU=1/_GH,_GV=B(_GI(-1*_GG*_GU,-1*_GF*_GU,-1*_GE*_GU));return new T6(0,_GV.a,_GV.b,E(_GV.c),E(_GV.d),_GV.e,_GV.f);}});return new T2(1,_GC,new T(function(){return B(_Gx(_Gz.b));}));}};return B(_Gx(_FR));});return new T2(0,new T2(1,_FV,new T(function(){return E(E(_FU).a);})),new T(function(){return E(E(_FU).b);}));}else{var _GW=new T(function(){var _GX=new T(function(){var _GY=E(_FL),_GZ=B(_Dc(_o3,_GY.a,_GY.b,_GY.c));return new T3(0,E(_GZ.a),E(_GZ.b),E(_GZ.c));}),_H0=new T(function(){var _H1=new T(function(){return B(_Dy(E(_FJ).a));}),_H2=function(_H3){var _H4=E(_H3);if(!_H4._){return E(_H1);}else{var _H5=E(_H4.a),_H6=E(_H5.b),_H7=E(_H5.a),_H8=E(_H7.a),_H9=E(_H7.b),_Ha=E(_H7.c),_Hb=E(_H5.c),_Hc=_Hb.a,_Hd=_Hb.b,_He=E(_H5.e);return new T2(1,new T(function(){var _Hf=E(_H6.a)+ -_H8,_Hg=E(_H6.b)+ -_H9,_Hh=E(_H6.c)+ -_Ha,_Hi=B(_Dc(_o3,_H8,_H9,_Ha)),_Hj=_Hi.a,_Hk=_Hi.b,_Hl=_Hi.c,_Hm=Math.sqrt(B(_ty(_o3,_Hf,_Hg,_Hh,_Hf,_Hg,_Hh))),_Hn=1/_Hm,_Ho=_Hf*_Hn,_Hp=_Hg*_Hn,_Hq=_Hh*_Hn,_Hr=B(_uz(_o3,_Ho,_Hp,_Hq,_Hj,_Hk,_Hl)),_Hs=B(_tI(_o3,_He.a,_He.b,_He.c)),_Ht=Math.sqrt(B(_CX(_o3,_Hc,_Hd,_Hc,_Hd))),_Hu=_Ht*E(_Hs.a),_Hv=_Ht*E(_Hs.b),_Hw=_Ht*E(_Hs.c),_Hx=B(_ty(_o3,_Hp*_Hw-_Hv*_Hq,_Hq*_Hu-_Hw*_Ho,_Ho*_Hv-_Hu*_Hp,_Hj,_Hk,_Hl));return new T6(0,_DK,_DK,E(new T2(0,E(new T3(0,E(_Hr.a),E(_Hr.b),E(_Hr.c))),E(_Hx))),E(_DD),_Hm,_Dk);}),new T(function(){return B(_H2(_H4.b));}));}};return B(_H2(_FO));}),_Hy=function(_Hz){var _HA=E(_Hz);if(!_HA._){return E(_H0);}else{var _HB=E(_HA.a),_HC=E(_HB.b),_HD=new T(function(){var _HE=E(_FL),_HF=E(_HC.c)+ -E(_HE.c),_HG=E(_HC.b)+ -E(_HE.b),_HH=E(_HC.a)+ -E(_HE.a),_HI=Math.sqrt(B(_ty(_o3,_HH,_HG,_HF,_HH,_HG,_HF))),_HJ=function(_HK,_HL,_HM){var _HN=E(_GX),_HO=_HN.a,_HP=_HN.b,_HQ=_HN.c,_HR=B(_uz(_o3,_HK,_HL,_HM,_HO,_HP,_HQ)),_HS=B(_ty(_o3,_HL*0-0*_HM,_HM*0-0*_HK,_HK*0-0*_HL,_HO,_HP,_HQ));return new T6(0,_DK,_DK,new T2(0,E(new T3(0,E(_HR.a),E(_HR.b),E(_HR.c))),E(_HS)),_DD,_HI,_Dk);};if(!E(_HB.g)){var _HT=1/_HI,_HU=B(_HJ(_HH*_HT,_HG*_HT,_HF*_HT));return new T6(0,_HU.a,_HU.b,E(_HU.c),E(_HU.d),_HU.e,_HU.f);}else{var _HV=1/_HI,_HW=B(_HJ(-1*_HH*_HV,-1*_HG*_HV,-1*_HF*_HV));return new T6(0,_HW.a,_HW.b,E(_HW.c),E(_HW.d),_HW.e,_HW.f);}});return new T2(1,_HD,new T(function(){return B(_Hy(_HA.b));}));}};return B(_Hy(_FR));});return new T2(0,new T2(1,_GW,_w),new T(function(){return E(E(_FJ).b);}));}}}},_HX=B(_DJ(_DH,_DH,_DI,_DG.c,_DG.d,_));return new F(function(){return _CP(_,_HX);});}else{return new F(function(){return _CP(_,new T2(0,_w,_DG));});}},_HY=new T(function(){return eval("__strict(passObject)");}),_HZ=new T(function(){return eval("__strict(refresh)");}),_I0=function(_I1,_){var _I2=__app0(E(_HZ)),_I3=__app0(E(_mi)),_I4=E(_I1),_I5=_I4.c,_I6=_I4.d,_I7=E(_I4.a),_I8=E(_I4.b);if(_I7<=_I8){if(_I7>_I8){return E(_mg);}else{if(0>=_I5){return new F(function(){return _mt(_I5,0);});}else{var _I9=E(_HY),_Ia=__app2(_I9,_I7,B(_md(E(_I6[0]))));if(_I7!=_I8){var _Ib=function(_Ic,_){if(_I7>_Ic){return E(_mg);}else{if(_Ic>_I8){return E(_mg);}else{var _Id=_Ic-_I7|0;if(0>_Id){return new F(function(){return _mt(_I5,_Id);});}else{if(_Id>=_I5){return new F(function(){return _mt(_I5,_Id);});}else{var _Ie=__app2(_I9,_Ic,B(_md(E(_I6[_Id]))));if(_Ic!=_I8){var _If=B(_Ib(_Ic+1|0,_));return new T2(1,_m2,_If);}else{return _my;}}}}}},_Ig=B(_Ib(_I7+1|0,_)),_Ih=__app0(E(_mh)),_Ii=B(_DE(_I4,_));return new T(function(){return E(E(_Ii).b);});}else{var _Ij=__app0(E(_mh)),_Ik=B(_DE(_I4,_));return new T(function(){return E(E(_Ik).b);});}}}}else{var _Il=__app0(E(_mh)),_Im=B(_DE(_I4,_));return new T(function(){return E(E(_Im).b);});}},_In=new T(function(){return B(unCStr("Negative exponent"));}),_Io=new T(function(){return B(err(_In));}),_Ip=function(_Iq,_Ir,_Is){while(1){if(!(_Ir%2)){var _It=_Iq*_Iq,_Iu=quot(_Ir,2);_Iq=_It;_Ir=_Iu;continue;}else{var _Iv=E(_Ir);if(_Iv==1){return _Iq*_Is;}else{var _It=_Iq*_Iq,_Iw=_Iq*_Is;_Iq=_It;_Ir=quot(_Iv-1|0,2);_Is=_Iw;continue;}}}},_Ix=function(_Iy,_Iz){while(1){if(!(_Iz%2)){var _IA=_Iy*_Iy,_IB=quot(_Iz,2);_Iy=_IA;_Iz=_IB;continue;}else{var _IC=E(_Iz);if(_IC==1){return E(_Iy);}else{return new F(function(){return _Ip(_Iy*_Iy,quot(_IC-1|0,2),_Iy);});}}}},_ID=-4,_IE=new T3(0,E(_va),E(_va),E(_ID)),_IF=function(_IG){return E(_IE);},_IH=function(_){return new F(function(){return __jsNull();});},_II=function(_IJ){var _IK=B(A1(_IJ,_));return E(_IK);},_IL=new T(function(){return B(_II(_IH));}),_IM=function(_IN,_IO,_IP,_IQ,_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ){var _J0=function(_J1){var _J2=E(_vT),_J3=2+_J1|0,_J4=_J3-1|0,_J5=(2+_J1)*(1+_J1),_J6=E(_wl);if(!_J6._){return _J2*0;}else{var _J7=_J6.a,_J8=_J6.b,_J9=B(A1(_IN,new T(function(){return 6.283185307179586*E(_J7)/E(_vl);}))),_Ja=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_J7)+1)/E(_vl);})));if(_J9!=_Ja){if(_J3>=0){var _Jb=E(_J3);if(!_Jb){var _Jc=function(_Jd,_Je){while(1){var _Jf=B((function(_Jg,_Jh){var _Ji=E(_Jg);if(!_Ji._){return E(_Jh);}else{var _Jj=_Ji.a,_Jk=_Ji.b,_Jl=B(A1(_IN,new T(function(){return 6.283185307179586*E(_Jj)/E(_vl);}))),_Jm=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_Jj)+1)/E(_vl);})));if(_Jl!=_Jm){var _Jn=_Jh+0/(_Jl-_Jm)/_J5;_Jd=_Jk;_Je=_Jn;return __continue;}else{if(_J4>=0){var _Jo=E(_J4);if(!_Jo){var _Jn=_Jh+_J3/_J5;_Jd=_Jk;_Je=_Jn;return __continue;}else{var _Jn=_Jh+_J3*B(_Ix(_Jl,_Jo))/_J5;_Jd=_Jk;_Je=_Jn;return __continue;}}else{return E(_Io);}}}})(_Jd,_Je));if(_Jf!=__continue){return _Jf;}}};return _J2*B(_Jc(_J8,0/(_J9-_Ja)/_J5));}else{var _Jp=function(_Jq,_Jr){while(1){var _Js=B((function(_Jt,_Ju){var _Jv=E(_Jt);if(!_Jv._){return E(_Ju);}else{var _Jw=_Jv.a,_Jx=_Jv.b,_Jy=B(A1(_IN,new T(function(){return 6.283185307179586*E(_Jw)/E(_vl);}))),_Jz=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_Jw)+1)/E(_vl);})));if(_Jy!=_Jz){if(_Jb>=0){var _JA=_Ju+(B(_Ix(_Jy,_Jb))-B(_Ix(_Jz,_Jb)))/(_Jy-_Jz)/_J5;_Jq=_Jx;_Jr=_JA;return __continue;}else{return E(_Io);}}else{if(_J4>=0){var _JB=E(_J4);if(!_JB){var _JA=_Ju+_J3/_J5;_Jq=_Jx;_Jr=_JA;return __continue;}else{var _JA=_Ju+_J3*B(_Ix(_Jy,_JB))/_J5;_Jq=_Jx;_Jr=_JA;return __continue;}}else{return E(_Io);}}}})(_Jq,_Jr));if(_Js!=__continue){return _Js;}}};return _J2*B(_Jp(_J8,(B(_Ix(_J9,_Jb))-B(_Ix(_Ja,_Jb)))/(_J9-_Ja)/_J5));}}else{return E(_Io);}}else{if(_J4>=0){var _JC=E(_J4);if(!_JC){var _JD=function(_JE,_JF){while(1){var _JG=B((function(_JH,_JI){var _JJ=E(_JH);if(!_JJ._){return E(_JI);}else{var _JK=_JJ.a,_JL=_JJ.b,_JM=B(A1(_IN,new T(function(){return 6.283185307179586*E(_JK)/E(_vl);}))),_JN=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_JK)+1)/E(_vl);})));if(_JM!=_JN){if(_J3>=0){var _JO=E(_J3);if(!_JO){var _JP=_JI+0/(_JM-_JN)/_J5;_JE=_JL;_JF=_JP;return __continue;}else{var _JP=_JI+(B(_Ix(_JM,_JO))-B(_Ix(_JN,_JO)))/(_JM-_JN)/_J5;_JE=_JL;_JF=_JP;return __continue;}}else{return E(_Io);}}else{var _JP=_JI+_J3/_J5;_JE=_JL;_JF=_JP;return __continue;}}})(_JE,_JF));if(_JG!=__continue){return _JG;}}};return _J2*B(_JD(_J8,_J3/_J5));}else{var _JQ=function(_JR,_JS){while(1){var _JT=B((function(_JU,_JV){var _JW=E(_JU);if(!_JW._){return E(_JV);}else{var _JX=_JW.a,_JY=_JW.b,_JZ=B(A1(_IN,new T(function(){return 6.283185307179586*E(_JX)/E(_vl);}))),_K0=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_JX)+1)/E(_vl);})));if(_JZ!=_K0){if(_J3>=0){var _K1=E(_J3);if(!_K1){var _K2=_JV+0/(_JZ-_K0)/_J5;_JR=_JY;_JS=_K2;return __continue;}else{var _K2=_JV+(B(_Ix(_JZ,_K1))-B(_Ix(_K0,_K1)))/(_JZ-_K0)/_J5;_JR=_JY;_JS=_K2;return __continue;}}else{return E(_Io);}}else{if(_JC>=0){var _K2=_JV+_J3*B(_Ix(_JZ,_JC))/_J5;_JR=_JY;_JS=_K2;return __continue;}else{return E(_Io);}}}})(_JR,_JS));if(_JT!=__continue){return _JT;}}};return _J2*B(_JQ(_J8,_J3*B(_Ix(_J9,_JC))/_J5));}}else{return E(_Io);}}}},_K3=E(_IL),_K4=1/(B(_J0(1))*_IO);return new F(function(){return _y2(_IN,_IF,new T2(0,E(new T3(0,E(_K4),E(_K4),E(_K4))),1/(B(_J0(3))*_IO)),_IP,_IQ,_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ,_vb,_K3,_K3,0);});},_K5=0.5,_K6=1,_K7=0,_K8=0.3,_K9=function(_Ka){return E(_K8);},_Kb=new T(function(){var _Kc=B(_IM(_K9,1.2,_K7,_K6,_K5,_K7,_K7,_K7,_K7,_K7,_K6,_K6,_K6));return {_:0,a:E(_Kc.a),b:E(_Kc.b),c:E(_Kc.c),d:E(_Kc.d),e:E(_Kc.e),f:E(_Kc.f),g:E(_Kc.g),h:_Kc.h,i:_Kc.i,j:_Kc.j};}),_Kd=0,_Ke=function(_){var _Kf=newArr(1,_rk),_=_Kf[0]=_Kb;return new T4(0,E(_Kd),E(_Kd),1,_Kf);},_Kg=new T(function(){return B(_rp(_Ke));}),_Kh=function(_Ki,_){while(1){var _Kj=E(_Ki);if(!_Kj._){return _m2;}else{var _Kk=_Kj.b,_Kl=E(_Kj.a);switch(_Kl._){case 0:var _Km=B(A1(_Kl.a,_));_Ki=B(_n(_Kk,new T2(1,_Km,_w)));continue;case 1:_Ki=B(_n(_Kk,_Kl.a));continue;default:_Ki=_Kk;continue;}}}},_Kn=function(_Ko,_Kp,_){var _Kq=E(_Ko);switch(_Kq._){case 0:var _Kr=B(A1(_Kq.a,_));return new F(function(){return _Kh(B(_n(_Kp,new T2(1,_Kr,_w))),_);});break;case 1:return new F(function(){return _Kh(B(_n(_Kp,_Kq.a)),_);});break;default:return new F(function(){return _Kh(_Kp,_);});}},_Ks=new T0(2),_Kt=function(_Ku){return new T0(2);},_Kv=function(_Kw,_Kx,_Ky){return function(_){var _Kz=E(_Kw),_KA=rMV(_Kz),_KB=E(_KA);if(!_KB._){var _KC=new T(function(){var _KD=new T(function(){return B(A1(_Ky,_m2));});return B(_n(_KB.b,new T2(1,new T2(0,_Kx,function(_KE){return E(_KD);}),_w)));}),_=wMV(_Kz,new T2(0,_KB.a,_KC));return _Ks;}else{var _KF=E(_KB.a);if(!_KF._){var _=wMV(_Kz,new T2(0,_Kx,_w));return new T(function(){return B(A1(_Ky,_m2));});}else{var _=wMV(_Kz,new T1(1,_KF.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Ky,_m2));}),new T2(1,new T(function(){return B(A2(_KF.a,_Kx,_Kt));}),_w)));}}};},_KG=new T(function(){return E(_IL);}),_KH=new T(function(){return eval("window.requestAnimationFrame");}),_KI=new T1(1,_w),_KJ=function(_KK,_KL){return function(_){var _KM=E(_KK),_KN=rMV(_KM),_KO=E(_KN);if(!_KO._){var _KP=_KO.a,_KQ=E(_KO.b);if(!_KQ._){var _=wMV(_KM,_KI);return new T(function(){return B(A1(_KL,_KP));});}else{var _KR=E(_KQ.a),_=wMV(_KM,new T2(0,_KR.a,_KQ.b));return new T1(1,new T2(1,new T(function(){return B(A1(_KL,_KP));}),new T2(1,new T(function(){return B(A1(_KR.b,_Kt));}),_w)));}}else{var _KS=new T(function(){var _KT=function(_KU){var _KV=new T(function(){return B(A1(_KL,_KU));});return function(_KW){return E(_KV);};};return B(_n(_KO.a,new T2(1,_KT,_w)));}),_=wMV(_KM,new T1(1,_KS));return _Ks;}};},_KX=function(_KY,_KZ){return new T1(0,B(_KJ(_KY,_KZ)));},_L0=function(_L1,_L2){var _L3=new T(function(){return new T1(0,B(_Kv(_L1,_m2,_Kt)));});return function(_){var _L4=__createJSFunc(2,function(_L5,_){var _L6=B(_Kn(_L3,_w,_));return _KG;}),_L7=__app1(E(_KH),_L4);return new T(function(){return B(_KX(_L1,_L2));});};},_L8=new T1(1,_w),_L9=function(_La,_Lb,_){var _Lc=function(_){var _Ld=nMV(_La),_Le=_Ld;return new T(function(){var _Lf=new T(function(){return B(_Lg(_));}),_Lh=function(_){var _Li=rMV(_Le),_Lj=B(A2(_Lb,_Li,_)),_=wMV(_Le,_Lj),_Lk=function(_){var _Ll=nMV(_L8);return new T(function(){return new T1(0,B(_L0(_Ll,function(_Lm){return E(_Lf);})));});};return new T1(0,_Lk);},_Ln=new T(function(){return new T1(0,_Lh);}),_Lg=function(_Lo){return E(_Ln);};return B(_Lg(_));});};return new F(function(){return _Kn(new T1(0,_Lc),_w,_);});},_Lp=new T(function(){return eval("__strict(setBounds)");}),_Lq=function(_){var _Lr=__app3(E(_lr),E(_ls),E(_lV),E(_lq)),_Ls=__app2(E(_Lp),E(_iG),E(_iD));return new F(function(){return _L9(_Kg,_I0,_);});},_Lt=function(_){return new F(function(){return _Lq(_);});};
var hasteMain = function() {B(A(_Lt, [0]));};window.onload = hasteMain;