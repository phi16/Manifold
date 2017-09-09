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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T(function(){return eval("compile");}),_i=function(_j){return E(E(_j).b);},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=E(_p);if(!_q._){return new F(function(){return A1(_o,_q.a);});}else{var _r=new T(function(){return B(_i(_n));}),_s=new T(function(){return B(_k(_n));}),_t=function(_u){var _v=E(_u);if(!_v._){return E(_s);}else{return new F(function(){return A2(_r,new T(function(){return B(_m(_n,_o,_v.a));}),new T(function(){return B(_t(_v.b));}));});}};return new F(function(){return _t(_q.a);});}},_w=function(_x){var _y=E(_x);if(!_y._){return __Z;}else{return new F(function(){return _0(_y.a,new T(function(){return B(_w(_y.b));},1));});}},_z=function(_A){return new F(function(){return _w(_A);});},_B=new T3(0,_4,_0,_z),_C=new T(function(){return B(unCStr("base"));}),_D=new T(function(){return B(unCStr("Control.Exception.Base"));}),_E=new T(function(){return B(unCStr("NoMethodError"));}),_F=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_C,_D,_E),_G=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_F,_4,_4),_H=function(_I){return E(_G);},_J=function(_K){return E(E(_K).a);},_L=function(_M,_N,_O){var _P=B(A1(_M,_)),_Q=B(A1(_N,_)),_R=hs_eqWord64(_P.a,_Q.a);if(!_R){return __Z;}else{var _S=hs_eqWord64(_P.b,_Q.b);return (!_S)?__Z:new T1(1,_O);}},_T=function(_U){var _V=E(_U);return new F(function(){return _L(B(_J(_V.a)),_H,_V.b);});},_W=function(_X){return E(E(_X).a);},_Y=function(_Z){return new T2(0,_10,_Z);},_11=function(_12,_13){return new F(function(){return _0(E(_12).a,_13);});},_14=44,_15=93,_16=91,_17=function(_18,_19,_1a){var _1b=E(_19);if(!_1b._){return new F(function(){return unAppCStr("[]",_1a);});}else{var _1c=new T(function(){var _1d=new T(function(){var _1e=function(_1f){var _1g=E(_1f);if(!_1g._){return E(new T2(1,_15,_1a));}else{var _1h=new T(function(){return B(A2(_18,_1g.a,new T(function(){return B(_1e(_1g.b));})));});return new T2(1,_14,_1h);}};return B(_1e(_1b.b));});return B(A2(_18,_1b.a,_1d));});return new T2(1,_16,_1c);}},_1i=function(_1j,_1k){return new F(function(){return _17(_11,_1j,_1k);});},_1l=function(_1m,_1n,_1o){return new F(function(){return _0(E(_1n).a,_1o);});},_1p=new T3(0,_1l,_W,_1i),_10=new T(function(){return new T5(0,_H,_1p,_Y,_T,_W);}),_1q=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_1r=function(_1s){return E(E(_1s).c);},_1t=function(_1u,_1v){return new F(function(){return die(new T(function(){return B(A2(_1r,_1v,_1u));}));});},_1w=function(_1x,_1y){return new F(function(){return _1t(_1x,_1y);});},_1z=function(_1A,_1B){var _1C=E(_1B);if(!_1C._){return new T2(0,_4,_4);}else{var _1D=_1C.a;if(!B(A1(_1A,_1D))){return new T2(0,_4,_1C);}else{var _1E=new T(function(){var _1F=B(_1z(_1A,_1C.b));return new T2(0,_1F.a,_1F.b);});return new T2(0,new T2(1,_1D,new T(function(){return E(E(_1E).a);})),new T(function(){return E(E(_1E).b);}));}}},_1G=32,_1H=new T(function(){return B(unCStr("\n"));}),_1I=function(_1J){return (E(_1J)==124)?false:true;},_1K=function(_1L,_1M){var _1N=B(_1z(_1I,B(unCStr(_1L)))),_1O=_1N.a,_1P=function(_1Q,_1R){var _1S=new T(function(){var _1T=new T(function(){return B(_0(_1M,new T(function(){return B(_0(_1R,_1H));},1)));});return B(unAppCStr(": ",_1T));},1);return new F(function(){return _0(_1Q,_1S);});},_1U=E(_1N.b);if(!_1U._){return new F(function(){return _1P(_1O,_4);});}else{if(E(_1U.a)==124){return new F(function(){return _1P(_1O,new T2(1,_1G,_1U.b));});}else{return new F(function(){return _1P(_1O,_4);});}}},_1V=function(_1W){return new F(function(){return _1w(new T1(0,new T(function(){return B(_1K(_1W,_1q));})),_10);});},_1X=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|cos"));}),_1Y=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|cosh"));}),_1Z=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|exp"));}),_20=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|log"));}),_21=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|sin"));}),_22=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|sinh"));}),_23=new T(function(){return B(unCStr(")"));}),_24=new T1(0,_23),_25=new T(function(){return B(unCStr("("));}),_26=new T1(0,_25),_27=new T(function(){return B(unCStr(")*("));}),_28=new T1(0,_27),_29=function(_2a){return E(E(_2a).c);},_2b=function(_2c){return E(E(_2c).d);},_2d=function(_2e,_2f){return new F(function(){return A2(_29,_2g,new T1(1,new T2(1,_26,new T2(1,new T(function(){return B(A2(_2b,_2g,_2e));}),new T2(1,_28,new T2(1,_2f,new T2(1,_24,_4)))))));});},_2h=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|acos"));}),_2i=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|acosh"));}),_2j=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|asin"));}),_2k=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|asinh"));}),_2l=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|atan"));}),_2m=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|atanh"));}),_2n=new T(function(){return B(unCStr(")/("));}),_2o=new T1(0,_2n),_2p=function(_2q,_2r){return new T1(1,new T2(1,_26,new T2(1,new T(function(){return B(A2(_2b,_2g,_2r));}),new T2(1,_2o,new T2(1,new T(function(){return B(A2(_2b,_2g,_2q));}),new T2(1,_24,_4))))));},_2s=new T(function(){return B(_1V("Lib\\Render.hs:34:10-30|pi"));}),_2t=function(_2u){return E(E(_2u).f);},_2v=new T(function(){return B(unCStr(" % "));}),_2w=function(_2x){while(1){var _2y=E(_2x);if(!_2y._){_2x=new T1(1,I_fromInt(_2y.a));continue;}else{return new F(function(){return I_toString(_2y.a);});}}},_2z=function(_2A,_2B){return new F(function(){return _0(fromJSStr(B(_2w(_2A))),_2B);});},_2C=function(_2D,_2E){var _2F=E(_2D);if(!_2F._){var _2G=_2F.a,_2H=E(_2E);return (_2H._==0)?_2G<_2H.a:I_compareInt(_2H.a,_2G)>0;}else{var _2I=_2F.a,_2J=E(_2E);return (_2J._==0)?I_compareInt(_2I,_2J.a)<0:I_compare(_2I,_2J.a)<0;}},_2K=41,_2L=40,_2M=new T1(0,0),_2N=function(_2O,_2P,_2Q){if(_2O<=6){return new F(function(){return _2z(_2P,_2Q);});}else{if(!B(_2C(_2P,_2M))){return new F(function(){return _2z(_2P,_2Q);});}else{return new T2(1,_2L,new T(function(){return B(_0(fromJSStr(B(_2w(_2P))),new T2(1,_2K,_2Q)));}));}}},_2R=function(_2S,_2T,_2U,_2V){if(_2S<=7){var _2W=new T(function(){return B(_0(_2v,new T(function(){return B(_2N(8,_2U,_2V));},1)));});return new F(function(){return _2N(8,_2T,_2W);});}else{var _2X=new T(function(){var _2Y=new T(function(){return B(_0(_2v,new T(function(){return B(_2N(8,_2U,new T2(1,_2K,_2V)));},1)));});return B(_2N(8,_2T,_2Y));});return new T2(1,_2L,_2X);}},_2Z=new T1(0,2),_30=new T1(0,1),_31=new T(function(){return B(_2R(0,_30,_2Z,_4));}),_32=new T1(0,_31),_33=function(_34){return new F(function(){return A3(_2t,_2g,_34,_32);});},_35=function(_36){return E(E(_36).i);},_37=function(_38){return E(E(_38).h);},_39=function(_3a){return new T1(1,new T2(1,_26,new T2(1,new T(function(){return B(A2(_37,_2g,_3a));}),new T2(1,_2o,new T2(1,new T(function(){return B(A2(_35,_2g,_3a));}),new T2(1,_24,_4))))));},_3b=function(_3c){return E(E(_3c).o);},_3d=function(_3e){return E(E(_3e).n);},_3f=function(_3g){return new T1(1,new T2(1,_26,new T2(1,new T(function(){return B(A2(_3d,_2g,_3g));}),new T2(1,_2o,new T2(1,new T(function(){return B(A2(_3b,_2g,_3g));}),new T2(1,_24,_4))))));},_3h=new T2(1,_24,_4),_3i=function(_3j,_3k){return new T1(1,new T2(1,_26,new T2(1,_3j,new T2(1,_2o,new T2(1,_3k,_3h)))));},_3l=function(_3m){var _3n=E(_3m);return new F(function(){return _2R(0,_3n.a,_3n.b,_4);});},_3o=function(_3p){return new T1(0,new T(function(){return B(_3l(_3p));}));},_3q=new T(function(){return B(unCStr("1./("));}),_3r=new T1(0,_3q),_3s=function(_3t){return new T1(1,new T2(1,_3r,new T2(1,_3t,_3h)));},_3u=new T(function(){return B(unCStr(")+("));}),_3v=new T1(0,_3u),_3w=function(_3x,_3y){return new T1(1,new T2(1,_26,new T2(1,_3x,new T2(1,_3v,new T2(1,_3y,_3h)))));},_3z=new T(function(){return B(unCStr("-("));}),_3A=new T1(0,_3z),_3B=function(_3C){return new T1(1,new T2(1,_3A,new T2(1,_3C,_3h)));},_3D=function(_3E,_3F){return new T1(1,new T2(1,_26,new T2(1,_3E,new T2(1,_28,new T2(1,_3F,_3h)))));},_3G=function(_3H){return E(E(_3H).a);},_3I=function(_3J){return E(E(_3J).d);},_3K=function(_3L,_3M){return new F(function(){return A3(_3G,_3N,_3L,new T(function(){return B(A2(_3I,_3N,_3M));}));});},_3O=new T(function(){return B(unCStr("abs("));}),_3P=new T1(0,_3O),_3Q=function(_3R){return new T1(1,new T2(1,_3P,new T2(1,_3R,_3h)));},_3S=new T(function(){return B(unCStr("."));}),_3T=function(_3U){return new T1(0,new T(function(){return B(_0(B(_2N(0,_3U,_4)),_3S));}));},_3V=new T(function(){return B(unCStr("sign("));}),_3W=new T1(0,_3V),_3X=function(_3Y){return new T1(1,new T2(1,_3W,new T2(1,_3Y,_3h)));},_3N=new T(function(){return {_:0,a:_3w,b:_3K,c:_3D,d:_3B,e:_3Q,f:_3X,g:_3T};}),_3Z=new T4(0,_3N,_3i,_3s,_3o),_2g=new T(function(){return {_:0,a:_3Z,b:_2s,c:_1Z,d:_20,e:_33,f:_2d,g:_2p,h:_21,i:_1X,j:_39,k:_2j,l:_2h,m:_2l,n:_22,o:_1Y,p:_3f,q:_2k,r:_2i,s:_2m};}),_40=new T(function(){return B(unCStr("z"));}),_41=new T1(0,_40),_42=new T(function(){return B(unCStr("y"));}),_43=new T1(0,_42),_44=new T(function(){return B(unCStr("x"));}),_45=new T1(0,_44),_46=new T3(0,_45,_43,_41),_47=new T1(0,1),_48=function(_49){return E(E(_49).a);},_4a=function(_4b){return E(E(_4b).a);},_4c=function(_4d){return E(E(_4d).c);},_4e=function(_4f,_4g,_4h,_4i,_4j,_4k,_4l){var _4m=B(_4a(B(_48(_4f)))),_4n=new T(function(){return B(A3(_3G,_4m,new T(function(){return B(A3(_4c,_4m,_4g,_4j));}),new T(function(){return B(A3(_4c,_4m,_4h,_4k));})));});return new F(function(){return A3(_3G,_4m,_4n,new T(function(){return B(A3(_4c,_4m,_4i,_4l));}));});},_4o=function(_4p){return E(E(_4p).b);},_4q=function(_4r){return E(E(_4r).g);},_4s=function(_4t,_4u){var _4v=B(_4a(B(_48(_4t))));return new F(function(){return A3(_4o,_4v,new T(function(){var _4w=E(_4u),_4x=_4w.a,_4y=_4w.b,_4z=_4w.c;return B(_4e(_4t,_4x,_4y,_4z,_4x,_4y,_4z));}),new T(function(){return B(A2(_4q,_4v,_47));}));});},_4A=new T(function(){return B(_4s(_2g,_46));}),_4B=function(_4C){return E(_4C);},_4D=new T(function(){return toJSStr(B(_m(_B,_4B,_4A)));}),_4E=function(_4F,_4G,_4H){var _4I=new T(function(){return B(_i(_4F));}),_4J=new T(function(){return B(_k(_4F));}),_4K=function(_4L){var _4M=E(_4L);if(!_4M._){return E(_4J);}else{return new F(function(){return A2(_4I,new T(function(){return B(_m(_4F,_4G,_4M.a));}),new T(function(){return B(_4K(_4M.b));}));});}};return new F(function(){return _4K(_4H);});},_4N=new T(function(){return B(unCStr("vec3("));}),_4O=new T1(0,_4N),_4P=function(_4Q,_4R){var _4S=E(_4Q);return E(_4R);},_4T=function(_4U,_4V){var _4W=E(_4U),_4X=E(_4V);return new T3(0,new T(function(){return B(A1(_4W.a,_4X.a));}),new T(function(){return B(A1(_4W.b,_4X.b));}),new T(function(){return B(A1(_4W.c,_4X.c));}));},_4Y=function(_4Z){return new T3(0,_4Z,_4Z,_4Z);},_50=function(_51,_52){var _53=E(_52);return new T3(0,_51,_51,_51);},_54=function(_55,_56){var _57=E(_56);return new T3(0,new T(function(){return B(A1(_55,_57.a));}),new T(function(){return B(A1(_55,_57.b));}),new T(function(){return B(A1(_55,_57.c));}));},_58=new T2(0,_54,_50),_59=function(_5a,_5b){var _5c=E(_5a),_5d=E(_5b);return new T3(0,_5c.a,_5c.b,_5c.c);},_5e=new T5(0,_58,_4Y,_4T,_4P,_59),_5f=new T1(0,0),_5g=function(_5h){return new T3(0,new T3(0,new T(function(){return B(A2(_4q,_5h,_47));}),new T(function(){return B(A2(_4q,_5h,_5f));}),new T(function(){return B(A2(_4q,_5h,_5f));})),new T3(0,new T(function(){return B(A2(_4q,_5h,_5f));}),new T(function(){return B(A2(_4q,_5h,_47));}),new T(function(){return B(A2(_4q,_5h,_5f));})),new T3(0,new T(function(){return B(A2(_4q,_5h,_5f));}),new T(function(){return B(A2(_4q,_5h,_5f));}),new T(function(){return B(A2(_4q,_5h,_47));})));},_5i=function(_5j){var _5k=B(_5g(_5j));return new T3(0,_5k.a,_5k.b,_5k.c);},_5l=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|atanh"));}),_5m=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|sin"));}),_5n=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|log"));}),_5o=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|exp"));}),_5p=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|pi"));}),_5q=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|acosh"));}),_5r=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|asinh"));}),_5s=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|cosh"));}),_5t=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|sinh"));}),_5u=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|atan"));}),_5v=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|acos"));}),_5w=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|asin"));}),_5x=new T(function(){return B(_1V("Lib\\AD.hs:25:10-42|cos"));}),_5y=function(_5z,_5A,_5B,_5C){var _5D=B(_5E(_5z,_5A)),_5F=new T(function(){return B(A3(_4c,B(_4a(B(_48(_5D)))),new T(function(){return B(A2(_2b,_5D,_5B));}),_5C));});return new F(function(){return A2(_29,_5D,_5F);});},_5G=function(_5H){return E(E(_5H).b);},_5I=function(_5J,_5K,_5L,_5M){var _5N=B(_5E(_5J,_5K));return new F(function(){return A3(_5G,B(_48(_5N)),new T(function(){return B(A2(_2b,_5N,_5M));}),new T(function(){return B(A2(_2b,_5N,_5L));}));});},_5O=function(_5P){return E(E(_5P).d);},_5Q=new T1(0,1),_5R=new T1(0,2),_5S=new T2(0,E(_5Q),E(_5R)),_5T=function(_5U,_5V,_5W){var _5X=B(_5E(_5U,_5V));return new F(function(){return A3(_2t,_5X,_5W,new T(function(){return B(A2(_5O,B(_48(_5X)),_5S));}));});},_5Y=function(_5Z,_60,_61){var _62=B(_5E(_5Z,_60));return new F(function(){return A3(_5G,B(_48(_62)),new T(function(){return B(A2(_37,_62,_61));}),new T(function(){return B(A2(_35,_62,_61));}));});},_63=function(_64,_65,_66){var _67=B(_5E(_64,_65));return new F(function(){return A3(_5G,B(_48(_67)),new T(function(){return B(A2(_3d,_67,_66));}),new T(function(){return B(A2(_3b,_67,_66));}));});},_5E=function(_68,_69){return {_:0,a:_68,b:_5p,c:_5o,d:_5n,e:function(_6a){return new F(function(){return _5T(_68,_69,_6a);});},f:function(_6b,_6a){return new F(function(){return _5y(_68,_69,_6b,_6a);});},g:function(_6b,_6a){return new F(function(){return _5I(_68,_69,_6b,_6a);});},h:_5m,i:_5x,j:function(_6a){return new F(function(){return _5Y(_68,_69,_6a);});},k:_5w,l:_5v,m:_5u,n:_5t,o:_5s,p:function(_6a){return new F(function(){return _63(_68,_69,_6a);});},q:_5r,r:_5q,s:_5l};},_6c=new T(function(){return B(unCStr("Prelude.undefined"));}),_6d=new T(function(){return B(err(_6c));}),_6e=function(_6f,_6g,_6h,_6i){return new T2(0,new T(function(){return B(A3(_5G,B(_48(E(_6g).d)),E(_6h).a,E(_6i).a));}),_6d);},_6j=new T1(0,0),_6k=function(_6l){return E(E(_6l).b);},_6m=function(_6n,_6o){var _6p=new T(function(){return B(_48(new T(function(){return E(E(_6n).d);})));}),_6q=new T(function(){return B(A2(_6k,E(_6n).b,new T(function(){return B(A2(_4q,B(_4a(_6p)),_6j));})));});return new T2(0,new T(function(){return B(A2(_5O,_6p,_6o));}),_6q);},_6r=function(_6s,_6t,_6u){var _6v=B(_6m(_6t,_6u));return new T2(0,_6v.a,_6v.b);},_6w=function(_6x,_6y,_6z){var _6A=new T(function(){var _6B=B(_48(E(_6y).d));return B(A3(_5G,_6B,new T(function(){return B(A2(_4q,B(_4a(_6B)),_5Q));}),E(_6z).a));});return new T2(0,_6A,_6d);},_6C=function(_6D,_6E){return new T4(0,_6D,function(_6b,_6a){return new F(function(){return _6e(_6D,_6E,_6b,_6a);});},function(_6a){return new F(function(){return _6w(_6D,_6E,_6a);});},function(_6a){return new F(function(){return _6r(_6D,_6E,_6a);});});},_6F=function(_6G){return E(E(_6G).a);},_6H=function(_6I){return E(E(_6I).c);},_6J=function(_6K){return E(E(_6K).a);},_6L=function(_6M,_6N,_6O,_6P,_6Q){var _6R=new T(function(){return B(_4a(new T(function(){return B(_48(new T(function(){return E(E(_6M).d);})));})));}),_6S=new T(function(){var _6T=E(_6M).b,_6U=new T(function(){var _6V=function(_6W,_6X){return new F(function(){return A3(_3G,_6R,new T(function(){return B(A3(_4c,_6R,_6N,_6X));}),new T(function(){return B(A3(_4c,_6R,_6W,_6P));}));});};return B(A3(_6J,B(_6F(_6T)),_6V,_6O));});return B(A3(_6H,_6T,_6U,_6Q));});return new T2(0,new T(function(){return B(A3(_4c,_6R,_6N,_6P));}),_6S);},_6Y=function(_6Z,_70,_71){var _72=E(_70),_73=E(_71),_74=B(_6L(_6Z,_72.a,_72.b,_73.a,_73.b));return new T2(0,_74.a,_74.b);},_75=function(_76,_77,_78,_79,_7a){var _7b=new T(function(){return B(_4a(new T(function(){return B(_48(new T(function(){return E(E(_76).d);})));})));}),_7c=new T(function(){var _7d=E(_76).b,_7e=new T(function(){return B(A3(_6J,B(_6F(_7d)),new T(function(){return B(_3G(_7b));}),_78));});return B(A3(_6H,_7d,_7e,_7a));});return new T2(0,new T(function(){return B(A3(_3G,_7b,_77,_79));}),_7c);},_7f=function(_7g,_7h,_7i){var _7j=E(_7h),_7k=E(_7i),_7l=B(_75(_7g,_7j.a,_7j.b,_7k.a,_7k.b));return new T2(0,_7l.a,_7l.b);},_7m=function(_7n,_7o,_7p){var _7q=B(_7r(_7n));return new F(function(){return A3(_3G,_7q,_7o,new T(function(){return B(A2(_3I,_7q,_7p));}));});},_7s=function(_7t){return E(E(_7t).e);},_7u=function(_7v){return E(E(_7v).f);},_7w=function(_7x,_7y,_7z){var _7A=new T(function(){return B(_4a(new T(function(){return B(_48(new T(function(){return E(E(_7x).d);})));})));}),_7B=new T(function(){return B(A3(_6J,B(_6F(E(_7x).b)),new T(function(){return B(_7u(_7A));}),_7z));});return new T2(0,new T(function(){return B(A2(_7s,_7A,_7y));}),_7B);},_7C=function(_7D,_7E){var _7F=E(_7E),_7G=B(_7w(_7D,_7F.a,_7F.b));return new T2(0,_7G.a,_7G.b);},_7H=function(_7I,_7J){var _7K=new T(function(){return B(_4a(new T(function(){return B(_48(new T(function(){return E(E(_7I).d);})));})));}),_7L=new T(function(){return B(A2(_6k,E(_7I).b,new T(function(){return B(A2(_4q,_7K,_6j));})));});return new T2(0,new T(function(){return B(A2(_4q,_7K,_7J));}),_7L);},_7M=function(_7N,_7O){var _7P=B(_7H(_7N,_7O));return new T2(0,_7P.a,_7P.b);},_7Q=function(_7R,_7S,_7T){var _7U=new T(function(){return B(_4a(new T(function(){return B(_48(new T(function(){return E(E(_7R).d);})));})));}),_7V=new T(function(){return B(A3(_6J,B(_6F(E(_7R).b)),new T(function(){return B(_3I(_7U));}),_7T));});return new T2(0,new T(function(){return B(A2(_3I,_7U,_7S));}),_7V);},_7W=function(_7X,_7Y){var _7Z=E(_7Y),_80=B(_7Q(_7X,_7Z.a,_7Z.b));return new T2(0,_80.a,_80.b);},_81=function(_82,_83){var _84=new T(function(){return B(_4a(new T(function(){return B(_48(new T(function(){return E(E(_82).d);})));})));}),_85=new T(function(){return B(A2(_6k,E(_82).b,new T(function(){return B(A2(_4q,_84,_6j));})));});return new T2(0,new T(function(){return B(A2(_7u,_84,_83));}),_85);},_86=function(_87,_88){var _89=B(_81(_87,E(_88).a));return new T2(0,_89.a,_89.b);},_7r=function(_8a){return {_:0,a:function(_6b,_6a){return new F(function(){return _7f(_8a,_6b,_6a);});},b:function(_6b,_6a){return new F(function(){return _7m(_8a,_6b,_6a);});},c:function(_6b,_6a){return new F(function(){return _6Y(_8a,_6b,_6a);});},d:function(_6a){return new F(function(){return _7W(_8a,_6a);});},e:function(_6a){return new F(function(){return _7C(_8a,_6a);});},f:function(_6a){return new F(function(){return _86(_8a,_6a);});},g:function(_6a){return new F(function(){return _7M(_8a,_6a);});}};},_8b=function(_8c,_8d,_8e){var _8f=E(_8e),_8g=new T(function(){return B(A2(_8c,_8f.b,new T(function(){return B(A2(_8c,_8f.c,_8d));})));});return new F(function(){return A2(_8c,_8f.a,_8g);});},_8h=function(_8i,_8j){var _8k=E(_8j);return new F(function(){return A3(_4c,_8i,_8k.a,new T(function(){return B(A3(_4c,_8i,_8k.b,_8k.c));}));});},_8l=function(_8m,_8n){var _8o=E(_8n);return new F(function(){return A3(_3G,_8m,_8o.a,new T(function(){return B(A3(_3G,_8m,_8o.b,_8o.c));}));});},_8p=function(_8q){return E(E(_8q).a);},_8r=function(_8s,_8t){var _8u=new T(function(){return B(A2(_8p,_8s,_8t));});return function(_8v){var _8w=E(_8v);if(!B(A1(_8u,_8w.a))){if(!B(A1(_8u,_8w.b))){return new F(function(){return A1(_8u,_8w.c);});}else{return true;}}else{return true;}};},_8x=function(_8y,_8z,_8A,_8B,_8C){var _8D=new T(function(){return B(A3(_i,_8y,new T(function(){return B(A1(_8z,_8B));}),new T(function(){return B(A1(_8z,_8C));})));});return new F(function(){return A3(_i,_8y,new T(function(){return B(A1(_8z,_8A));}),_8D);});},_8E=function(_8F,_8G,_8H){var _8I=E(_8H);return new F(function(){return _8x(_8F,_8G,_8I.a,_8I.b,_8I.c);});},_8J=function(_8K,_8L,_8M){var _8N=E(_8M),_8O=new T(function(){return B(A2(_8K,new T(function(){return B(A2(_8K,_8L,_8N.a));}),_8N.b));});return new F(function(){return A2(_8K,_8O,_8N.c);});},_8P=function(_8Q,_8R,_8S,_8T,_8U){return new F(function(){return A2(_8Q,B(A2(_8Q,B(A2(_8Q,_8R,_8S)),_8T)),_8U);});},_8V=function(_8W,_8X,_8Y){var _8Z=E(_8Y);return new F(function(){return _8P(_8W,_8X,_8Z.a,_8Z.b,_8Z.c);});},_90=function(_91,_92){var _93=E(_92);return new F(function(){return A2(_91,new T(function(){return B(A2(_91,_93.a,_93.b));}),_93.c);});},_94=function(_95,_96,_97,_98,_99){return new F(function(){return A2(_95,_97,B(A2(_95,_98,B(A2(_95,_99,_96)))));});},_9a=function(_9b,_9c,_9d){var _9e=E(_9d);return new F(function(){return _94(_9b,_9c,_9e.a,_9e.b,_9e.c);});},_9f=function(_9g,_9h){var _9i=E(_9h);return new F(function(){return A2(_9g,_9i.a,new T(function(){return B(A2(_9g,_9i.b,_9i.c));}));});},_9j=3,_9k=function(_9l){var _9m=E(_9l);return E(_9j);},_9n=function(_9o){return E(E(_9o).f);},_9p=function(_9q,_9r,_9s,_9t){return (!B(A3(_9n,_9q,_9s,_9t)))?(!B(A3(_9n,_9q,_9r,_9t)))?E(_9t):E(_9r):(!B(A3(_9n,_9q,_9r,_9s)))?E(_9s):E(_9r);},_9u=function(_9v,_9w){var _9x=E(_9w);return new F(function(){return _9p(_9v,_9x.a,_9x.b,_9x.c);});},_9y=function(_9z){return E(E(_9z).d);},_9A=function(_9B,_9C,_9D,_9E){return (!B(A3(_9y,_9B,_9D,_9E)))?(!B(A3(_9y,_9B,_9C,_9E)))?E(_9E):E(_9C):(!B(A3(_9y,_9B,_9C,_9D)))?E(_9D):E(_9C);},_9F=function(_9G,_9H){var _9I=E(_9H);return new F(function(){return _9A(_9G,_9I.a,_9I.b,_9I.c);});},_9J=function(_9K){var _9L=E(_9K);return false;},_9M=function(_9N,_9O){return new T2(1,_9N,_9O);},_9P=function(_9Q){return E(E(_9Q).c);},_9R=function(_9S){return new F(function(){return A(_9P,[_9T,_9M,_4,_9S]);});},_9U=function(_9V,_9W){var _9X=E(_9W);return new F(function(){return A3(_i,_9V,_9X.a,new T(function(){return B(A3(_i,_9V,_9X.b,_9X.c));}));});},_9T=new T(function(){return {_:0,a:_9U,b:_8E,c:_8b,d:_9a,e:_8J,f:_8V,g:_9f,h:_90,i:_9R,j:_9J,k:_9k,l:_8r,m:_9u,n:_9F,o:_8l,p:_8h};}),_9Y=function(_9Z){return E(E(_9Z).a);},_a0=function(_a1,_a2,_a3){return new T3(0,_a1,_a2,_a3);},_a4=function(_a5,_a6,_a7,_a8,_a9){var _aa=new T(function(){var _ab=new T(function(){return B(A3(_6J,B(_6F(_a5)),_a0,new T(function(){return B(A1(_a6,_a7));})));});return B(A3(_6H,_a5,_ab,new T(function(){return B(A1(_a6,_a8));})));});return new F(function(){return A3(_6H,_a5,_aa,new T(function(){return B(A1(_a6,_a9));}));});},_ac=function(_ad,_ae,_af){var _ag=E(_af);return new F(function(){return _a4(B(_9Y(_ad)),_ae,_ag.a,_ag.b,_ag.c);});},_ah=function(_ai,_aj){var _ak=E(_aj),_al=new T(function(){return B(_9Y(_ai));}),_am=new T(function(){return B(A3(_6H,_al,new T(function(){return B(A3(_6J,B(_6F(_al)),_a0,_ak.a));}),_ak.b));});return new F(function(){return A3(_6H,_al,_am,_ak.c);});},_an=function(_ao,_ap){var _aq=E(_ap),_ar=new T(function(){return B(A3(_6H,_ao,new T(function(){return B(A3(_6J,B(_6F(_ao)),_a0,_aq.a));}),_aq.b));});return new F(function(){return A3(_6H,_ao,_ar,_aq.c);});},_as=function(_at,_au,_av){var _aw=E(_av);return new F(function(){return _a4(_at,_au,_aw.a,_aw.b,_aw.c);});},_ax=new T6(0,_58,_9T,_as,_an,_ac,_ah),_ay=function(_az){var _aA=new T4(0,_ax,_5e,_5i,_az),_aB=new T(function(){return B(_5E(new T(function(){return B(_6C(new T(function(){return B(_7r(_aA));}),_aA));}),_aA));}),_aC=new T(function(){return B(_4a(new T(function(){return B(_48(_az));})));}),_aD=function(_aE){return E(B(_4s(_aB,new T(function(){var _aF=E(_aE),_aG=B(_5g(_aC));return new T3(0,new T2(0,_aF.a,_aG.a),new T2(0,_aF.b,_aG.b),new T2(0,_aF.c,_aG.c));}))).b);};return E(_aD);},_aH=new T(function(){return B(_ay(_2g));}),_aI=new T(function(){return B(A1(_aH,_46));}),_aJ=new T(function(){return E(E(_aI).a);}),_aK=new T(function(){return B(unCStr(","));}),_aL=new T1(0,_aK),_aM=new T(function(){return E(E(_aI).b);}),_aN=new T(function(){return E(E(_aI).c);}),_aO=new T2(1,_aN,_3h),_aP=new T2(1,_aL,_aO),_aQ=new T2(1,_aM,_aP),_aR=new T2(1,_aL,_aQ),_aS=new T2(1,_aJ,_aR),_aT=new T2(1,_4O,_aS),_aU=new T(function(){return toJSStr(B(_4E(_B,_4B,_aT)));}),_aV=function(_aW,_aX,_aY){return new F(function(){return A1(_aW,function(_aZ){return new F(function(){return A2(_aX,_aZ,_aY);});});});},_b0=function(_b1,_b2,_b3){var _b4=function(_b5){var _b6=new T(function(){return B(A1(_b3,_b5));});return new F(function(){return A1(_b2,function(_b7){return E(_b6);});});};return new F(function(){return A1(_b1,_b4);});},_b8=function(_b9,_ba,_bb){var _bc=new T(function(){return B(A1(_ba,function(_bd){return new F(function(){return A1(_bb,_bd);});}));});return new F(function(){return A1(_b9,function(_be){return E(_bc);});});},_bf=function(_bg,_bh,_bi){var _bj=function(_bk){var _bl=function(_bm){return new F(function(){return A1(_bi,new T(function(){return B(A1(_bk,_bm));}));});};return new F(function(){return A1(_bh,_bl);});};return new F(function(){return A1(_bg,_bj);});},_bn=function(_bo,_bp){return new F(function(){return A1(_bp,_bo);});},_bq=function(_br,_bs,_bt){var _bu=new T(function(){return B(A1(_bt,_br));});return new F(function(){return A1(_bs,function(_bv){return E(_bu);});});},_bw=function(_bx,_by,_bz){var _bA=function(_bB){return new F(function(){return A1(_bz,new T(function(){return B(A1(_bx,_bB));}));});};return new F(function(){return A1(_by,_bA);});},_bC=new T2(0,_bw,_bq),_bD=new T5(0,_bC,_bn,_bf,_b8,_b0),_bE=function(_bF){return E(E(_bF).b);},_bG=function(_bH,_bI){return new F(function(){return A3(_bE,_bJ,_bH,function(_bK){return E(_bI);});});},_bL=function(_bM){return new F(function(){return err(_bM);});},_bJ=new T(function(){return new T5(0,_bD,_aV,_bG,_bn,_bL);}),_bN=function(_bO){return new T0(2);},_bP=function(_bQ){var _bR=new T(function(){return B(A1(_bQ,_bN));}),_bS=function(_bT){return new T1(1,new T2(1,new T(function(){return B(A1(_bT,_5));}),new T2(1,_bR,_4)));};return E(_bS);},_bU=new T3(0,_bJ,_4B,_bP),_bV=function(_bW){var _bX=E(_bW);return new F(function(){return Math.log(_bX+(_bX+1)*Math.sqrt((_bX-1)/(_bX+1)));});},_bY=function(_bZ){var _c0=E(_bZ);return new F(function(){return Math.log(_c0+Math.sqrt(1+_c0*_c0));});},_c1=function(_c2){var _c3=E(_c2);return 0.5*Math.log((1+_c3)/(1-_c3));},_c4=function(_c5,_c6){return Math.log(E(_c6))/Math.log(E(_c5));},_c7=3.141592653589793,_c8=new T1(0,1),_c9=function(_ca,_cb){var _cc=E(_ca);if(!_cc._){var _cd=_cc.a,_ce=E(_cb);if(!_ce._){var _cf=_ce.a;return (_cd!=_cf)?(_cd>_cf)?2:0:1;}else{var _cg=I_compareInt(_ce.a,_cd);return (_cg<=0)?(_cg>=0)?1:2:0;}}else{var _ch=_cc.a,_ci=E(_cb);if(!_ci._){var _cj=I_compareInt(_ch,_ci.a);return (_cj>=0)?(_cj<=0)?1:2:0;}else{var _ck=I_compare(_ch,_ci.a);return (_ck>=0)?(_ck<=0)?1:2:0;}}},_cl=new T(function(){return B(unCStr("base"));}),_cm=new T(function(){return B(unCStr("GHC.Exception"));}),_cn=new T(function(){return B(unCStr("ArithException"));}),_co=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_cl,_cm,_cn),_cp=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_co,_4,_4),_cq=function(_cr){return E(_cp);},_cs=function(_ct){var _cu=E(_ct);return new F(function(){return _L(B(_J(_cu.a)),_cq,_cu.b);});},_cv=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_cw=new T(function(){return B(unCStr("denormal"));}),_cx=new T(function(){return B(unCStr("divide by zero"));}),_cy=new T(function(){return B(unCStr("loss of precision"));}),_cz=new T(function(){return B(unCStr("arithmetic underflow"));}),_cA=new T(function(){return B(unCStr("arithmetic overflow"));}),_cB=function(_cC,_cD){switch(E(_cC)){case 0:return new F(function(){return _0(_cA,_cD);});break;case 1:return new F(function(){return _0(_cz,_cD);});break;case 2:return new F(function(){return _0(_cy,_cD);});break;case 3:return new F(function(){return _0(_cx,_cD);});break;case 4:return new F(function(){return _0(_cw,_cD);});break;default:return new F(function(){return _0(_cv,_cD);});}},_cE=function(_cF){return new F(function(){return _cB(_cF,_4);});},_cG=function(_cH,_cI,_cJ){return new F(function(){return _cB(_cI,_cJ);});},_cK=function(_cL,_cM){return new F(function(){return _17(_cB,_cL,_cM);});},_cN=new T3(0,_cG,_cE,_cK),_cO=new T(function(){return new T5(0,_cq,_cN,_cP,_cs,_cE);}),_cP=function(_1y){return new T2(0,_cO,_1y);},_cQ=3,_cR=new T(function(){return B(_cP(_cQ));}),_cS=new T(function(){return die(_cR);}),_cT=function(_cU,_cV){var _cW=E(_cU);return (_cW._==0)?_cW.a*Math.pow(2,_cV):I_toNumber(_cW.a)*Math.pow(2,_cV);},_cX=function(_cY,_cZ){var _d0=E(_cY);if(!_d0._){var _d1=_d0.a,_d2=E(_cZ);return (_d2._==0)?_d1==_d2.a:(I_compareInt(_d2.a,_d1)==0)?true:false;}else{var _d3=_d0.a,_d4=E(_cZ);return (_d4._==0)?(I_compareInt(_d3,_d4.a)==0)?true:false:(I_compare(_d3,_d4.a)==0)?true:false;}},_d5=function(_d6){var _d7=E(_d6);if(!_d7._){return E(_d7.a);}else{return new F(function(){return I_toInt(_d7.a);});}},_d8=function(_d9,_da){while(1){var _db=E(_d9);if(!_db._){var _dc=_db.a,_dd=E(_da);if(!_dd._){var _de=_dd.a,_df=addC(_dc,_de);if(!E(_df.b)){return new T1(0,_df.a);}else{_d9=new T1(1,I_fromInt(_dc));_da=new T1(1,I_fromInt(_de));continue;}}else{_d9=new T1(1,I_fromInt(_dc));_da=_dd;continue;}}else{var _dg=E(_da);if(!_dg._){_d9=_db;_da=new T1(1,I_fromInt(_dg.a));continue;}else{return new T1(1,I_add(_db.a,_dg.a));}}}},_dh=function(_di,_dj){while(1){var _dk=E(_di);if(!_dk._){var _dl=E(_dk.a);if(_dl==(-2147483648)){_di=new T1(1,I_fromInt(-2147483648));continue;}else{var _dm=E(_dj);if(!_dm._){var _dn=_dm.a;return new T2(0,new T1(0,quot(_dl,_dn)),new T1(0,_dl%_dn));}else{_di=new T1(1,I_fromInt(_dl));_dj=_dm;continue;}}}else{var _do=E(_dj);if(!_do._){_di=_dk;_dj=new T1(1,I_fromInt(_do.a));continue;}else{var _dp=I_quotRem(_dk.a,_do.a);return new T2(0,new T1(1,_dp.a),new T1(1,_dp.b));}}}},_dq=new T1(0,0),_dr=function(_ds,_dt){while(1){var _du=E(_ds);if(!_du._){_ds=new T1(1,I_fromInt(_du.a));continue;}else{return new T1(1,I_shiftLeft(_du.a,_dt));}}},_dv=function(_dw,_dx,_dy){if(!B(_cX(_dy,_dq))){var _dz=B(_dh(_dx,_dy)),_dA=_dz.a;switch(B(_c9(B(_dr(_dz.b,1)),_dy))){case 0:return new F(function(){return _cT(_dA,_dw);});break;case 1:if(!(B(_d5(_dA))&1)){return new F(function(){return _cT(_dA,_dw);});}else{return new F(function(){return _cT(B(_d8(_dA,_c8)),_dw);});}break;default:return new F(function(){return _cT(B(_d8(_dA,_c8)),_dw);});}}else{return E(_cS);}},_dB=function(_dC,_dD){var _dE=E(_dC);if(!_dE._){var _dF=_dE.a,_dG=E(_dD);return (_dG._==0)?_dF>_dG.a:I_compareInt(_dG.a,_dF)<0;}else{var _dH=_dE.a,_dI=E(_dD);return (_dI._==0)?I_compareInt(_dH,_dI.a)>0:I_compare(_dH,_dI.a)>0;}},_dJ=new T1(0,1),_dK=new T(function(){return B(unCStr("PatternMatchFail"));}),_dL=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_C,_D,_dK),_dM=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dL,_4,_4),_dN=function(_dO){return E(_dM);},_dP=function(_dQ){var _dR=E(_dQ);return new F(function(){return _L(B(_J(_dR.a)),_dN,_dR.b);});},_dS=function(_dT){return E(E(_dT).a);},_dU=function(_Z){return new T2(0,_dV,_Z);},_dW=function(_dX,_dY){return new F(function(){return _0(E(_dX).a,_dY);});},_dZ=function(_e0,_e1){return new F(function(){return _17(_dW,_e0,_e1);});},_e2=function(_e3,_e4,_e5){return new F(function(){return _0(E(_e4).a,_e5);});},_e6=new T3(0,_e2,_dS,_dZ),_dV=new T(function(){return new T5(0,_dN,_e6,_dU,_dP,_dS);}),_e7=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_e8=function(_e9){return new F(function(){return _1w(new T1(0,new T(function(){return B(_1K(_e9,_e7));})),_dV);});},_ea=function(_eb){var _ec=function(_ed,_ee){while(1){if(!B(_2C(_ed,_eb))){if(!B(_dB(_ed,_eb))){if(!B(_cX(_ed,_eb))){return new F(function(){return _e8("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ee);}}else{return _ee-1|0;}}else{var _ef=B(_dr(_ed,1)),_eg=_ee+1|0;_ed=_ef;_ee=_eg;continue;}}};return new F(function(){return _ec(_dJ,0);});},_eh=function(_ei){var _ej=E(_ei);if(!_ej._){var _ek=_ej.a>>>0;if(!_ek){return -1;}else{var _el=function(_em,_en){while(1){if(_em>=_ek){if(_em<=_ek){if(_em!=_ek){return new F(function(){return _e8("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_en);}}else{return _en-1|0;}}else{var _eo=imul(_em,2)>>>0,_ep=_en+1|0;_em=_eo;_en=_ep;continue;}}};return new F(function(){return _el(1,0);});}}else{return new F(function(){return _ea(_ej);});}},_eq=function(_er){var _es=E(_er);if(!_es._){var _et=_es.a>>>0;if(!_et){return new T2(0,-1,0);}else{var _eu=function(_ev,_ew){while(1){if(_ev>=_et){if(_ev<=_et){if(_ev!=_et){return new F(function(){return _e8("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ew);}}else{return _ew-1|0;}}else{var _ex=imul(_ev,2)>>>0,_ey=_ew+1|0;_ev=_ex;_ew=_ey;continue;}}};return new T2(0,B(_eu(1,0)),(_et&_et-1>>>0)>>>0&4294967295);}}else{var _ez=_es.a;return new T2(0,B(_eh(_es)),I_compareInt(I_and(_ez,I_sub(_ez,I_fromInt(1))),0));}},_eA=function(_eB,_eC){var _eD=E(_eB);if(!_eD._){var _eE=_eD.a,_eF=E(_eC);return (_eF._==0)?_eE<=_eF.a:I_compareInt(_eF.a,_eE)>=0;}else{var _eG=_eD.a,_eH=E(_eC);return (_eH._==0)?I_compareInt(_eG,_eH.a)<=0:I_compare(_eG,_eH.a)<=0;}},_eI=function(_eJ,_eK){while(1){var _eL=E(_eJ);if(!_eL._){var _eM=_eL.a,_eN=E(_eK);if(!_eN._){return new T1(0,(_eM>>>0&_eN.a>>>0)>>>0&4294967295);}else{_eJ=new T1(1,I_fromInt(_eM));_eK=_eN;continue;}}else{var _eO=E(_eK);if(!_eO._){_eJ=_eL;_eK=new T1(1,I_fromInt(_eO.a));continue;}else{return new T1(1,I_and(_eL.a,_eO.a));}}}},_eP=function(_eQ,_eR){while(1){var _eS=E(_eQ);if(!_eS._){var _eT=_eS.a,_eU=E(_eR);if(!_eU._){var _eV=_eU.a,_eW=subC(_eT,_eV);if(!E(_eW.b)){return new T1(0,_eW.a);}else{_eQ=new T1(1,I_fromInt(_eT));_eR=new T1(1,I_fromInt(_eV));continue;}}else{_eQ=new T1(1,I_fromInt(_eT));_eR=_eU;continue;}}else{var _eX=E(_eR);if(!_eX._){_eQ=_eS;_eR=new T1(1,I_fromInt(_eX.a));continue;}else{return new T1(1,I_sub(_eS.a,_eX.a));}}}},_eY=new T1(0,2),_eZ=function(_f0,_f1){var _f2=E(_f0);if(!_f2._){var _f3=(_f2.a>>>0&(2<<_f1>>>0)-1>>>0)>>>0,_f4=1<<_f1>>>0;return (_f4<=_f3)?(_f4>=_f3)?1:2:0;}else{var _f5=B(_eI(_f2,B(_eP(B(_dr(_eY,_f1)),_dJ)))),_f6=B(_dr(_dJ,_f1));return (!B(_dB(_f6,_f5)))?(!B(_2C(_f6,_f5)))?1:2:0;}},_f7=function(_f8,_f9){while(1){var _fa=E(_f8);if(!_fa._){_f8=new T1(1,I_fromInt(_fa.a));continue;}else{return new T1(1,I_shiftRight(_fa.a,_f9));}}},_fb=function(_fc,_fd,_fe,_ff){var _fg=B(_eq(_ff)),_fh=_fg.a;if(!E(_fg.b)){var _fi=B(_eh(_fe));if(_fi<((_fh+_fc|0)-1|0)){var _fj=_fh+(_fc-_fd|0)|0;if(_fj>0){if(_fj>_fi){if(_fj<=(_fi+1|0)){if(!E(B(_eq(_fe)).b)){return 0;}else{return new F(function(){return _cT(_c8,_fc-_fd|0);});}}else{return 0;}}else{var _fk=B(_f7(_fe,_fj));switch(B(_eZ(_fe,_fj-1|0))){case 0:return new F(function(){return _cT(_fk,_fc-_fd|0);});break;case 1:if(!(B(_d5(_fk))&1)){return new F(function(){return _cT(_fk,_fc-_fd|0);});}else{return new F(function(){return _cT(B(_d8(_fk,_c8)),_fc-_fd|0);});}break;default:return new F(function(){return _cT(B(_d8(_fk,_c8)),_fc-_fd|0);});}}}else{return new F(function(){return _cT(_fe,(_fc-_fd|0)-_fj|0);});}}else{if(_fi>=_fd){var _fl=B(_f7(_fe,(_fi+1|0)-_fd|0));switch(B(_eZ(_fe,_fi-_fd|0))){case 0:return new F(function(){return _cT(_fl,((_fi-_fh|0)+1|0)-_fd|0);});break;case 2:return new F(function(){return _cT(B(_d8(_fl,_c8)),((_fi-_fh|0)+1|0)-_fd|0);});break;default:if(!(B(_d5(_fl))&1)){return new F(function(){return _cT(_fl,((_fi-_fh|0)+1|0)-_fd|0);});}else{return new F(function(){return _cT(B(_d8(_fl,_c8)),((_fi-_fh|0)+1|0)-_fd|0);});}}}else{return new F(function(){return _cT(_fe, -_fh);});}}}else{var _fm=B(_eh(_fe))-_fh|0,_fn=function(_fo){var _fp=function(_fq,_fr){if(!B(_eA(B(_dr(_fr,_fd)),_fq))){return new F(function(){return _dv(_fo-_fd|0,_fq,_fr);});}else{return new F(function(){return _dv((_fo-_fd|0)+1|0,_fq,B(_dr(_fr,1)));});}};if(_fo>=_fd){if(_fo!=_fd){return new F(function(){return _fp(_fe,new T(function(){return B(_dr(_ff,_fo-_fd|0));}));});}else{return new F(function(){return _fp(_fe,_ff);});}}else{return new F(function(){return _fp(new T(function(){return B(_dr(_fe,_fd-_fo|0));}),_ff);});}};if(_fc>_fm){return new F(function(){return _fn(_fc);});}else{return new F(function(){return _fn(_fm);});}}},_fs=new T1(0,2147483647),_ft=new T(function(){return B(_d8(_fs,_dJ));}),_fu=function(_fv){var _fw=E(_fv);if(!_fw._){var _fx=E(_fw.a);return (_fx==(-2147483648))?E(_ft):new T1(0, -_fx);}else{return new T1(1,I_negate(_fw.a));}},_fy=new T(function(){return 0/0;}),_fz=new T(function(){return -1/0;}),_fA=new T(function(){return 1/0;}),_fB=0,_fC=function(_fD,_fE){if(!B(_cX(_fE,_dq))){if(!B(_cX(_fD,_dq))){if(!B(_2C(_fD,_dq))){return new F(function(){return _fb(-1021,53,_fD,_fE);});}else{return  -B(_fb(-1021,53,B(_fu(_fD)),_fE));}}else{return E(_fB);}}else{return (!B(_cX(_fD,_dq)))?(!B(_2C(_fD,_dq)))?E(_fA):E(_fz):E(_fy);}},_fF=function(_fG){var _fH=E(_fG);return new F(function(){return _fC(_fH.a,_fH.b);});},_fI=function(_fJ){return 1/E(_fJ);},_fK=function(_fL){var _fM=E(_fL),_fN=E(_fM);return (_fN==0)?E(_fB):(_fN<=0)? -_fN:E(_fM);},_fO=function(_fP){var _fQ=E(_fP);if(!_fQ._){return _fQ.a;}else{return new F(function(){return I_toNumber(_fQ.a);});}},_fR=function(_fS){return new F(function(){return _fO(_fS);});},_fT=1,_fU=-1,_fV=function(_fW){var _fX=E(_fW);return (_fX<=0)?(_fX>=0)?E(_fX):E(_fU):E(_fT);},_fY=function(_fZ,_g0){return E(_fZ)-E(_g0);},_g1=function(_g2){return  -E(_g2);},_g3=function(_g4,_g5){return E(_g4)+E(_g5);},_g6=function(_g7,_g8){return E(_g7)*E(_g8);},_g9={_:0,a:_g3,b:_fY,c:_g6,d:_g1,e:_fK,f:_fV,g:_fR},_ga=function(_gb,_gc){return E(_gb)/E(_gc);},_gd=new T4(0,_g9,_ga,_fI,_fF),_ge=function(_gf){return new F(function(){return Math.acos(E(_gf));});},_gg=function(_gh){return new F(function(){return Math.asin(E(_gh));});},_gi=function(_gj){return new F(function(){return Math.atan(E(_gj));});},_gk=function(_gl){return new F(function(){return Math.cos(E(_gl));});},_gm=function(_gn){return new F(function(){return cosh(E(_gn));});},_go=function(_gp){return new F(function(){return Math.exp(E(_gp));});},_gq=function(_gr){return new F(function(){return Math.log(E(_gr));});},_gs=function(_gt,_gu){return new F(function(){return Math.pow(E(_gt),E(_gu));});},_gv=function(_gw){return new F(function(){return Math.sin(E(_gw));});},_gx=function(_gy){return new F(function(){return sinh(E(_gy));});},_gz=function(_gA){return new F(function(){return Math.sqrt(E(_gA));});},_gB=function(_gC){return new F(function(){return Math.tan(E(_gC));});},_gD=function(_gE){return new F(function(){return tanh(E(_gE));});},_gF={_:0,a:_gd,b:_c7,c:_go,d:_gq,e:_gz,f:_gs,g:_c4,h:_gv,i:_gk,j:_gB,k:_gg,l:_ge,m:_gi,n:_gx,o:_gm,p:_gD,q:_bY,r:_bV,s:_c1},_gG=function(_gH){return E(E(_gH).e);},_gI=function(_gJ,_gK,_gL,_gM){var _gN=new T(function(){return B(_48(_gJ));}),_gO=new T(function(){return B(A2(_gG,_gJ,new T(function(){return B(_4e(_gJ,_gK,_gL,_gM,_gK,_gL,_gM));})));});return new T3(0,new T(function(){return B(A3(_5G,_gN,_gK,_gO));}),new T(function(){return B(A3(_5G,_gN,_gL,_gO));}),new T(function(){return B(A3(_5G,_gN,_gM,_gO));}));},_gP=-0.9,_gQ=0.1,_gR=new T(function(){var _gS=B(_gI(_gF,_gQ,_gQ,_gP));return new T3(0,_gS.a,_gS.b,_gS.c);}),_gT=0,_gU=-1,_gV=new T3(0,_gU,_gT,_gT),_gW=new T2(0,_gV,_gR),_gX=function(_gY,_gZ){return new F(function(){return A3(_5G,B(_48(_gY)),new T(function(){return B(_4s(_gY,_gZ));}),new T(function(){var _h0=B(A2(_ay,_gY,_gZ)),_h1=_h0.a,_h2=_h0.b,_h3=_h0.c;return B(_4e(_gY,_h1,_h2,_h3,_h1,_h2,_h3));}));});},_h4=new T(function(){return eval("draw");}),_h5=new T(function(){return B(_ay(_gF));}),_h6=new T(function(){return eval("refresh");}),_h7=function(_h8,_h9,_ha,_hb,_){var _hc=__app0(E(_h6)),_hd=E(_h8),_he=E(_h9),_hf=E(_ha),_hg=__app3(E(_h4),_hd,_he,_hf),_hh=new T(function(){var _hi=E(_hb);return new T3(0,new T(function(){return _hd+E(_hi.a)*5.0e-2;}),new T(function(){return _he+E(_hi.b)*5.0e-2;}),new T(function(){return _hf+E(_hi.c)*5.0e-2;}));}),_hj=new T(function(){return B(A1(_h5,_hh));}),_hk=new T(function(){var _hl=E(_hh),_hm=E(_hj),_hn=B(_gI(_gF,_hm.a,_hm.b,_hm.c)),_ho=new T(function(){return B(_gX(_gF,_hl));});return new T3(0,new T(function(){return E(_hl.a)+ -(E(_ho)*E(_hn.a));}),new T(function(){return E(_hl.b)+ -(E(_ho)*E(_hn.b));}),new T(function(){return E(_hl.c)+ -(E(_ho)*E(_hn.c));}));}),_hp=new T(function(){var _hq=E(_hb),_hr=_hq.a,_hs=_hq.b,_ht=_hq.c,_hu=B(A1(_h5,_hk)),_hv=_hu.a,_hw=_hu.b,_hx=_hu.c,_hy=E(_hj),_hz=_hy.a,_hA=_hy.b,_hB=_hy.c,_hC=new T(function(){return Math.sqrt(B(_4e(_gF,_hr,_hs,_ht,_hr,_hs,_ht)));}),_hD=new T(function(){return  -(B(_4e(_gF,_hr,_hs,_ht,_hv,_hw,_hx))/(1-B(_4e(_gF,_hz,_hA,_hB,_hv,_hw,_hx))));}),_hE=new T(function(){return E(_hr)+(E(_hv)+ -E(_hz))*E(_hD);}),_hF=new T(function(){return E(_hs)+(E(_hw)+ -E(_hA))*E(_hD);}),_hG=new T(function(){return E(_ht)+(E(_hx)+ -E(_hB))*E(_hD);}),_hH=new T(function(){return Math.sqrt(B(_4e(_gF,_hE,_hF,_hG,_hE,_hF,_hG)));});return new T3(0,new T(function(){return E(_hC)*(E(_hE)/E(_hH));}),new T(function(){return E(_hC)*(E(_hF)/E(_hH));}),new T(function(){return E(_hC)*(E(_hG)/E(_hH));}));});return new T2(0,_hk,_hp);},_hI=function(_hJ,_hK,_hL){var _hM=function(_){var _hN=E(_hJ),_hO=E(_hN.a),_hP=B(_h7(_hO.a,_hO.b,_hO.c,_hN.b,_));return new T(function(){return B(A1(_hL,new T1(1,_hP)));});};return new T1(0,_hM);},_hQ=new T0(2),_hR=function(_hS,_hT,_hU){return function(_){var _hV=E(_hS),_hW=rMV(_hV),_hX=E(_hW);if(!_hX._){var _hY=new T(function(){var _hZ=new T(function(){return B(A1(_hU,_5));});return B(_0(_hX.b,new T2(1,new T2(0,_hT,function(_i0){return E(_hZ);}),_4)));}),_=wMV(_hV,new T2(0,_hX.a,_hY));return _hQ;}else{var _i1=E(_hX.a);if(!_i1._){var _=wMV(_hV,new T2(0,_hT,_4));return new T(function(){return B(A1(_hU,_5));});}else{var _=wMV(_hV,new T1(1,_i1.b));return new T1(1,new T2(1,new T(function(){return B(A1(_hU,_5));}),new T2(1,new T(function(){return B(A2(_i1.a,_hT,_bN));}),_4)));}}};},_i2=function(_i3){return E(E(_i3).b);},_i4=function(_i5,_i6,_i7){var _i8=new T(function(){return new T1(0,B(_hR(_i6,_i7,_bN)));}),_i9=function(_ia){return new T1(1,new T2(1,new T(function(){return B(A1(_ia,_5));}),new T2(1,_i8,_4)));};return new F(function(){return A2(_i2,_i5,_i9);});},_ib=function(_){return new F(function(){return __jsNull();});},_ic=function(_id){var _ie=B(A1(_id,_));return E(_ie);},_if=new T(function(){return B(_ic(_ib));}),_ig=new T(function(){return E(_if);}),_ih=new T(function(){return eval("window.requestAnimationFrame");}),_ii=new T1(1,_4),_ij=function(_ik,_il){return function(_){var _im=E(_ik),_in=rMV(_im),_io=E(_in);if(!_io._){var _ip=_io.a,_iq=E(_io.b);if(!_iq._){var _=wMV(_im,_ii);return new T(function(){return B(A1(_il,_ip));});}else{var _ir=E(_iq.a),_=wMV(_im,new T2(0,_ir.a,_iq.b));return new T1(1,new T2(1,new T(function(){return B(A1(_il,_ip));}),new T2(1,new T(function(){return B(A1(_ir.b,_bN));}),_4)));}}else{var _is=new T(function(){var _it=function(_iu){var _iv=new T(function(){return B(A1(_il,_iu));});return function(_iw){return E(_iv);};};return B(_0(_io.a,new T2(1,_it,_4)));}),_=wMV(_im,new T1(1,_is));return _hQ;}};},_ix=function(_iy,_iz){return new T1(0,B(_ij(_iy,_iz)));},_iA=function(_iB,_iC){var _iD=new T(function(){return new T1(0,B(_hR(_iB,_5,_bN)));});return function(_){var _iE=__createJSFunc(2,function(_iF,_){var _iG=B(_c(_iD,_4,_));return _ig;}),_iH=__app1(E(_ih),_iE);return new T(function(){return B(_ix(_iB,_iC));});};},_iI=new T1(1,_4),_iJ=function(_iK){var _iL=new T(function(){return B(_iM(_));}),_iN=new T(function(){var _iO=function(_iP){return E(_iL);},_iQ=function(_){var _iR=nMV(_iI);return new T(function(){return new T1(0,B(_iA(_iR,_iO)));});};return B(A(_i4,[_bU,_iK,_5,function(_iS){return E(new T1(0,_iQ));}]));}),_iM=function(_iT){return E(_iN);};return new F(function(){return _iM(_);});},_iU=function(_iV){return E(E(_iV).a);},_iW=function(_iX){return E(E(_iX).d);},_iY=function(_iZ){return E(E(_iZ).c);},_j0=function(_j1){return E(E(_j1).c);},_j2=new T1(1,_4),_j3=function(_j4){var _j5=function(_){var _j6=nMV(_j2);return new T(function(){return B(A1(_j4,_j6));});};return new T1(0,_j5);},_j7=function(_j8,_j9){var _ja=new T(function(){return B(_j0(_j8));}),_jb=B(_iU(_j8)),_jc=function(_jd){var _je=new T(function(){return B(A1(_ja,new T(function(){return B(A1(_j9,_jd));})));});return new F(function(){return A3(_iY,_jb,_je,new T(function(){return B(A2(_iW,_jb,_jd));}));});};return new F(function(){return A3(_bE,_jb,new T(function(){return B(A2(_i2,_j8,_j3));}),_jc);});},_jf=function(_jg,_jh,_ji){var _jj=new T(function(){return B(_iU(_jg));}),_jk=new T(function(){return B(A2(_iW,_jj,_5));}),_jl=function(_jm,_jn){var _jo=new T(function(){var _jp=new T(function(){return B(A2(_i2,_jg,function(_jq){return new F(function(){return _ix(_jn,_jq);});}));});return B(A3(_bE,_jj,_jp,new T(function(){return B(A1(_ji,_jm));})));});return new F(function(){return A3(_bE,_jj,_jo,function(_jr){var _js=E(_jr);if(!_js._){return E(_jk);}else{return new F(function(){return _jl(_js.a,_jn);});}});});};return new F(function(){return _j7(_jg,function(_jq){return new F(function(){return _jl(_jh,_jq);});});});},_jt=new T(function(){return B(A(_jf,[_bU,_gW,_hI,_iJ]));}),_ju=function(_){var _jv=__app2(E(_h),E(_4D),E(_aU));return new F(function(){return _c(_jt,_4,_);});},_jw=function(_){return new F(function(){return _ju(_);});};
var hasteMain = function() {B(A(_jw, [0]));};window.onload = hasteMain;