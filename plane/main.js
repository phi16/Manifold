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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(_hP).a);})));})));}),_hR=new T(function(){return B(_fR(_hQ));}),_hS=new T(function(){return B(A2(_8s,_hQ,_8r));}),_hT=new T(function(){return E(E(_hP).b);}),_hU=function(_hV){var _hW=new T(function(){var _hX=new T(function(){return B(A1(_hR,new T(function(){return E(E(_hV).c);})));}),_hY=new T(function(){return B(A1(_hR,new T(function(){return E(E(_hV).a);})));});return B(A3(_gN,_hT,_hY,_hX));});return new F(function(){return A3(_9p,_hQ,_hW,_hS);});};return E(_hU);},_hZ=function(_ef,_ee){return new T2(0,_ef,_ee);},_i0=function(_i1,_i2,_i3){var _i4=new T(function(){var _i5=E(_i1),_i6=_i5.a,_i7=new T(function(){return B(A1(_i5.b,new T(function(){return B(_8J(B(_8H(E(_i5.c).a))));})));});return B(A3(_8R,_i6,new T(function(){return B(A3(_8T,B(_8F(_i6)),_hZ,_i3));}),_i7));});return E(B(A1(_i2,_i4)).b);},_i8=function(_i9){var _ia=new T(function(){return E(E(_i9).a);}),_ib=new T(function(){return E(E(_i9).b);}),_ic=new T(function(){var _id=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),_ie=new T(function(){var _if=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),new T3(0,_8p,_8u,new T2(0,_ia,_ib))));});return B(_eb(_if,new T3(0,_8p,_8u,new T2(0,_ia,_ib))));});return B(_hO(new T2(0,_ie,_id)));});return function(_ig){return new F(function(){return _i0(new T3(0,_8p,_8u,new T2(0,_ia,_ib)),_ic,_ig);});};},_ih=new T(function(){return B(_i8(_7V));}),_ii=new T(function(){return B(A1(_ih,_E));}),_ij=new T(function(){return E(E(_ii).a);}),_ik=new T(function(){return B(unCStr(",y:"));}),_il=new T1(0,_ik),_im=new T(function(){return E(E(_ii).b);}),_in=new T(function(){return B(unCStr(",z:"));}),_io=new T1(0,_in),_ip=new T(function(){return E(E(_ii).c);}),_iq=new T(function(){return B(unCStr("})"));}),_ir=new T1(0,_iq),_is=new T2(1,_ir,_w),_it=new T2(1,_ip,_is),_iu=new T2(1,_io,_it),_iv=new T2(1,_im,_iu),_iw=new T2(1,_il,_iv),_ix=new T2(1,_ij,_iw),_iy=new T(function(){return B(unCStr("({x:"));}),_iz=new T1(0,_iy),_iA=new T2(1,_iz,_ix),_iB=function(_iC){return E(_iC);},_iD=new T(function(){return toJSStr(B(_e(_x,_iB,_iA)));}),_iE=new T(function(){return B(_hO(_7V));}),_iF=new T(function(){return B(A1(_iE,_E));}),_iG=new T(function(){return toJSStr(B(_4(_x,_iB,_iF)));}),_iH=function(_iI,_iJ,_iK){var _iL=E(_iK);if(!_iL._){return new F(function(){return A1(_iJ,_iL.a);});}else{var _iM=new T(function(){return B(_0(_iI));}),_iN=new T(function(){return B(_2(_iI));}),_iO=function(_iP){var _iQ=E(_iP);if(!_iQ._){return E(_iN);}else{return new F(function(){return A2(_iM,new T(function(){return B(_iH(_iI,_iJ,_iQ.a));}),new T(function(){return B(_iO(_iQ.b));}));});}};return new F(function(){return _iO(_iL.a);});}},_iR=new T(function(){return B(unCStr("x"));}),_iS=new T1(0,_iR),_iT=new T(function(){return B(unCStr("y"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("z"));}),_iW=new T1(0,_iV),_iX=new T3(0,E(_iS),E(_iU),E(_iW)),_iY=new T(function(){return B(unCStr(","));}),_iZ=new T1(0,_iY),_j0=new T(function(){return B(unCStr("pow("));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr(")"));}),_j3=new T1(0,_j2),_j4=new T2(1,_j3,_w),_j5=function(_j6,_j7){return new T1(1,new T2(1,_j1,new T2(1,_j6,new T2(1,_iZ,new T2(1,_j7,_j4)))));},_j8=new T(function(){return B(unCStr("acos("));}),_j9=new T1(0,_j8),_ja=function(_jb){return new T1(1,new T2(1,_j9,new T2(1,_jb,_j4)));},_jc=new T(function(){return B(unCStr("acosh("));}),_jd=new T1(0,_jc),_je=function(_jf){return new T1(1,new T2(1,_jd,new T2(1,_jf,_j4)));},_jg=new T(function(){return B(unCStr("asin("));}),_jh=new T1(0,_jg),_ji=function(_jj){return new T1(1,new T2(1,_jh,new T2(1,_jj,_j4)));},_jk=new T(function(){return B(unCStr("asinh("));}),_jl=new T1(0,_jk),_jm=function(_jn){return new T1(1,new T2(1,_jl,new T2(1,_jn,_j4)));},_jo=new T(function(){return B(unCStr("atan("));}),_jp=new T1(0,_jo),_jq=function(_jr){return new T1(1,new T2(1,_jp,new T2(1,_jr,_j4)));},_js=new T(function(){return B(unCStr("atanh("));}),_jt=new T1(0,_js),_ju=function(_jv){return new T1(1,new T2(1,_jt,new T2(1,_jv,_j4)));},_jw=new T(function(){return B(unCStr("cos("));}),_jx=new T1(0,_jw),_jy=function(_jz){return new T1(1,new T2(1,_jx,new T2(1,_jz,_j4)));},_jA=new T(function(){return B(unCStr("cosh("));}),_jB=new T1(0,_jA),_jC=function(_jD){return new T1(1,new T2(1,_jB,new T2(1,_jD,_j4)));},_jE=new T(function(){return B(unCStr("exp("));}),_jF=new T1(0,_jE),_jG=function(_jH){return new T1(1,new T2(1,_jF,new T2(1,_jH,_j4)));},_jI=new T(function(){return B(unCStr("log("));}),_jJ=new T1(0,_jI),_jK=function(_jL){return new T1(1,new T2(1,_jJ,new T2(1,_jL,_j4)));},_jM=new T(function(){return B(unCStr(")/log("));}),_jN=new T1(0,_jM),_jO=function(_jP,_jQ){return new T1(1,new T2(1,_jJ,new T2(1,_jQ,new T2(1,_jN,new T2(1,_jP,_j4)))));},_jR=new T(function(){return B(unCStr("pi"));}),_jS=new T1(0,_jR),_jT=new T(function(){return B(unCStr("sin("));}),_jU=new T1(0,_jT),_jV=function(_jW){return new T1(1,new T2(1,_jU,new T2(1,_jW,_j4)));},_jX=new T(function(){return B(unCStr("sinh("));}),_jY=new T1(0,_jX),_jZ=function(_k0){return new T1(1,new T2(1,_jY,new T2(1,_k0,_j4)));},_k1=new T(function(){return B(unCStr("sqrt("));}),_k2=new T1(0,_k1),_k3=function(_k4){return new T1(1,new T2(1,_k2,new T2(1,_k4,_j4)));},_k5=new T(function(){return B(unCStr("tan("));}),_k6=new T1(0,_k5),_k7=function(_k8){return new T1(1,new T2(1,_k6,new T2(1,_k8,_j4)));},_k9=new T(function(){return B(unCStr("tanh("));}),_ka=new T1(0,_k9),_kb=function(_kc){return new T1(1,new T2(1,_ka,new T2(1,_kc,_j4)));},_kd=new T(function(){return B(unCStr("("));}),_ke=new T1(0,_kd),_kf=new T(function(){return B(unCStr(")/("));}),_kg=new T1(0,_kf),_kh=function(_ki,_kj){return new T1(1,new T2(1,_ke,new T2(1,_ki,new T2(1,_kg,new T2(1,_kj,_j4)))));},_kk=function(_kl){return new T1(0,new T(function(){var _km=E(_kl),_kn=jsShow(B(_6y(_km.a,_km.b)));return fromJSStr(_kn);}));},_ko=new T(function(){return B(unCStr("1./("));}),_kp=new T1(0,_ko),_kq=function(_kr){return new T1(1,new T2(1,_kp,new T2(1,_kr,_j4)));},_ks=new T(function(){return B(unCStr(")+("));}),_kt=new T1(0,_ks),_ku=function(_kv,_kw){return new T1(1,new T2(1,_ke,new T2(1,_kv,new T2(1,_kt,new T2(1,_kw,_j4)))));},_kx=new T(function(){return B(unCStr("-("));}),_ky=new T1(0,_kx),_kz=function(_kA){return new T1(1,new T2(1,_ky,new T2(1,_kA,_j4)));},_kB=new T(function(){return B(unCStr(")*("));}),_kC=new T1(0,_kB),_kD=function(_kE,_kF){return new T1(1,new T2(1,_ke,new T2(1,_kE,new T2(1,_kC,new T2(1,_kF,_j4)))));},_kG=function(_kH,_kI){return new F(function(){return A3(_6X,_kJ,_kH,new T(function(){return B(A2(_6Z,_kJ,_kI));}));});},_kK=new T(function(){return B(unCStr("abs("));}),_kL=new T1(0,_kK),_kM=function(_kN){return new T1(1,new T2(1,_kL,new T2(1,_kN,_j4)));},_kO=new T(function(){return B(unCStr("."));}),_kP=function(_kQ){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kQ,_w)),_kO));}));},_kR=new T(function(){return B(unCStr("sign("));}),_kS=new T1(0,_kR),_kT=function(_kU){return new T1(1,new T2(1,_kS,new T2(1,_kU,_j4)));},_kJ=new T(function(){return {_:0,a:_ku,b:_kG,c:_kD,d:_kz,e:_kM,f:_kT,g:_kP};}),_kV=new T4(0,_kJ,_kh,_kq,_kk),_kW={_:0,a:_kV,b:_jS,c:_jG,d:_jK,e:_k3,f:_j5,g:_jO,h:_jV,i:_jy,j:_k7,k:_ji,l:_ja,m:_jq,n:_jZ,o:_jC,p:_kb,q:_jm,r:_je,s:_ju},_kX=new T(function(){return B(unCStr("(/=) is not defined"));}),_kY=new T(function(){return B(err(_kX));}),_kZ=new T(function(){return B(unCStr("(==) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T2(0,_l0,_kY),_l2=new T(function(){return B(unCStr("(<) is not defined"));}),_l3=new T(function(){return B(err(_l2));}),_l4=new T(function(){return B(unCStr("(<=) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(>) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>=) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("compare is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("max("));}),_ld=new T1(0,_lc),_le=function(_lf,_lg){return new T1(1,new T2(1,_ld,new T2(1,_lf,new T2(1,_iZ,new T2(1,_lg,_j4)))));},_lh=new T(function(){return B(unCStr("min("));}),_li=new T1(0,_lh),_lj=function(_lk,_ll){return new T1(1,new T2(1,_li,new T2(1,_lk,new T2(1,_iZ,new T2(1,_ll,_j4)))));},_lm={_:0,a:_l1,b:_lb,c:_l3,d:_l5,e:_l7,f:_l9,g:_le,h:_lj},_ln=new T2(0,_kW,_lm),_lo=new T(function(){return B(_hO(_ln));}),_lp=new T(function(){return B(A1(_lo,_iX));}),_lq=new T(function(){return toJSStr(B(_iH(_x,_iB,_lp)));}),_lr=new T(function(){return eval("__strict(compile)");}),_ls=new T(function(){return toJSStr(E(_iT));}),_lt=function(_lu,_lv,_lw){var _lx=new T(function(){return B(_0(_lu));}),_ly=new T(function(){return B(_2(_lu));}),_lz=function(_lA){var _lB=E(_lA);if(!_lB._){return E(_ly);}else{return new F(function(){return A2(_lx,new T(function(){return B(_iH(_lu,_lv,_lB.a));}),new T(function(){return B(_lz(_lB.b));}));});}};return new F(function(){return _lz(_lw);});},_lC=new T(function(){return B(unCStr("vec3("));}),_lD=new T1(0,_lC),_lE=new T(function(){return B(_7i(0,_8r,_w));}),_lF=new T(function(){return B(_n(_lE,_kO));}),_lG=new T1(0,_lF),_lH=new T(function(){return B(_7i(0,_8q,_w));}),_lI=new T(function(){return B(_n(_lH,_kO));}),_lJ=new T1(0,_lI),_lK=new T2(1,_lJ,_w),_lL=new T2(1,_lG,_lK),_lM=function(_lN,_lO){var _lP=E(_lO);return (_lP._==0)?__Z:new T2(1,_lN,new T2(1,_lP.a,new T(function(){return B(_lM(_lN,_lP.b));})));},_lQ=new T(function(){return B(_lM(_iZ,_lL));}),_lR=new T2(1,_lJ,_lQ),_lS=new T1(1,_lR),_lT=new T2(1,_lS,_j4),_lU=new T2(1,_lD,_lT),_lV=new T(function(){return toJSStr(B(_lt(_x,_iB,_lU)));}),_lW=function(_lX,_lY){while(1){var _lZ=E(_lX);if(!_lZ._){return E(_lY);}else{var _m0=_lY+1|0;_lX=_lZ.b;_lY=_m0;continue;}}},_m1=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_m2=new T(function(){return B(err(_m1));}),_m3=0,_m4=new T3(0,E(_m3),E(_m3),E(_m3)),_m5=new T(function(){return B(unCStr("Negative exponent"));}),_m6=new T(function(){return B(err(_m5));}),_m7=function(_m8,_m9,_ma){while(1){if(!(_m9%2)){var _mb=_m8*_m8,_mc=quot(_m9,2);_m8=_mb;_m9=_mc;continue;}else{var _md=E(_m9);if(_md==1){return _m8*_ma;}else{var _mb=_m8*_m8,_me=_m8*_ma;_m8=_mb;_m9=quot(_md-1|0,2);_ma=_me;continue;}}}},_mf=function(_mg,_mh){while(1){if(!(_mh%2)){var _mi=_mg*_mg,_mj=quot(_mh,2);_mg=_mi;_mh=_mj;continue;}else{var _mk=E(_mh);if(_mk==1){return E(_mg);}else{return new F(function(){return _m7(_mg*_mg,quot(_mk-1|0,2),_mg);});}}}},_ml=function(_mm){var _mn=E(_mm);return new F(function(){return Math.log(_mn+(_mn+1)*Math.sqrt((_mn-1)/(_mn+1)));});},_mo=function(_mp){var _mq=E(_mp);return new F(function(){return Math.log(_mq+Math.sqrt(1+_mq*_mq));});},_mr=function(_ms){var _mt=E(_ms);return 0.5*Math.log((1+_mt)/(1-_mt));},_mu=function(_mv,_mw){return Math.log(E(_mw))/Math.log(E(_mv));},_mx=3.141592653589793,_my=function(_mz){var _mA=E(_mz);return new F(function(){return _6y(_mA.a,_mA.b);});},_mB=function(_mC){return 1/E(_mC);},_mD=function(_mE){var _mF=E(_mE),_mG=E(_mF);return (_mG==0)?E(_6x):(_mG<=0)? -_mG:E(_mF);},_mH=function(_mI){var _mJ=E(_mI);if(!_mJ._){return _mJ.a;}else{return new F(function(){return I_toNumber(_mJ.a);});}},_mK=function(_mL){return new F(function(){return _mH(_mL);});},_mM=1,_mN=-1,_mO=function(_mP){var _mQ=E(_mP);return (_mQ<=0)?(_mQ>=0)?E(_mQ):E(_mN):E(_mM);},_mR=function(_mS,_mT){return E(_mS)-E(_mT);},_mU=function(_mV){return  -E(_mV);},_mW=function(_mX,_mY){return E(_mX)+E(_mY);},_mZ=function(_n0,_n1){return E(_n0)*E(_n1);},_n2={_:0,a:_mW,b:_mR,c:_mZ,d:_mU,e:_mD,f:_mO,g:_mK},_n3=function(_n4,_n5){return E(_n4)/E(_n5);},_n6=new T4(0,_n2,_n3,_mB,_my),_n7=function(_n8){return new F(function(){return Math.acos(E(_n8));});},_n9=function(_na){return new F(function(){return Math.asin(E(_na));});},_nb=function(_nc){return new F(function(){return Math.atan(E(_nc));});},_nd=function(_ne){return new F(function(){return Math.cos(E(_ne));});},_nf=function(_ng){return new F(function(){return cosh(E(_ng));});},_nh=function(_ni){return new F(function(){return Math.exp(E(_ni));});},_nj=function(_nk){return new F(function(){return Math.log(E(_nk));});},_nl=function(_nm,_nn){return new F(function(){return Math.pow(E(_nm),E(_nn));});},_no=function(_np){return new F(function(){return Math.sin(E(_np));});},_nq=function(_nr){return new F(function(){return sinh(E(_nr));});},_ns=function(_nt){return new F(function(){return Math.sqrt(E(_nt));});},_nu=function(_nv){return new F(function(){return Math.tan(E(_nv));});},_nw=function(_nx){return new F(function(){return tanh(E(_nx));});},_ny={_:0,a:_n6,b:_mx,c:_nh,d:_nj,e:_ns,f:_nl,g:_mu,h:_no,i:_nd,j:_nu,k:_n9,l:_n7,m:_nb,n:_nq,o:_nf,p:_nw,q:_mo,r:_ml,s:_mr},_nz=function(_nA,_nB){return (E(_nA)!=E(_nB))?true:false;},_nC=function(_nD,_nE){return E(_nD)==E(_nE);},_nF=new T2(0,_nC,_nz),_nG=function(_nH,_nI){return E(_nH)<E(_nI);},_nJ=function(_nK,_nL){return E(_nK)<=E(_nL);},_nM=function(_nN,_nO){return E(_nN)>E(_nO);},_nP=function(_nQ,_nR){return E(_nQ)>=E(_nR);},_nS=function(_nT,_nU){var _nV=E(_nT),_nW=E(_nU);return (_nV>=_nW)?(_nV!=_nW)?2:1:0;},_nX=function(_nY,_nZ){var _o0=E(_nY),_o1=E(_nZ);return (_o0>_o1)?E(_o0):E(_o1);},_o2=function(_o3,_o4){var _o5=E(_o3),_o6=E(_o4);return (_o5>_o6)?E(_o6):E(_o5);},_o7={_:0,a:_nF,b:_nS,c:_nG,d:_nJ,e:_nM,f:_nP,g:_nX,h:_o2},_o8="dz",_o9="wy",_oa="wx",_ob="dy",_oc="dx",_od="t",_oe="a",_of="r",_og="ly",_oh="lx",_oi="wz",_oj=0,_ok=function(_ol){var _om=__new(),_on=_om,_oo=function(_op,_){while(1){var _oq=E(_op);if(!_oq._){return _oj;}else{var _or=E(_oq.a),_os=__set(_on,E(_or.a),E(_or.b));_op=_oq.b;continue;}}},_ot=B(_oo(_ol,_));return E(_on);},_ou=function(_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD){return new F(function(){return _ok(new T2(1,new T2(0,_oa,_ov),new T2(1,new T2(0,_o9,_ow),new T2(1,new T2(0,_oi,_ox),new T2(1,new T2(0,_oh,_oy*_oz*Math.cos(_oA)),new T2(1,new T2(0,_og,_oy*_oz*Math.sin(_oA)),new T2(1,new T2(0,_of,_oy),new T2(1,new T2(0,_oe,_oz),new T2(1,new T2(0,_od,_oA),new T2(1,new T2(0,_oc,_oB),new T2(1,new T2(0,_ob,_oC),new T2(1,new T2(0,_o8,_oD),_w))))))))))));});},_oE=function(_oF){var _oG=E(_oF),_oH=E(_oG.a),_oI=E(_oG.b),_oJ=E(_oG.d);return new F(function(){return _ou(_oH.a,_oH.b,_oH.c,E(_oI.a),E(_oI.b),E(_oG.c),_oJ.a,_oJ.b,_oJ.c);});},_oK=function(_oL,_oM){var _oN=E(_oM);return (_oN._==0)?__Z:new T2(1,new T(function(){return B(A1(_oL,_oN.a));}),new T(function(){return B(_oK(_oL,_oN.b));}));},_oO=function(_oP,_oQ,_oR){var _oS=__lst2arr(B(_oK(_oE,new T2(1,_oP,new T2(1,_oQ,new T2(1,_oR,_w))))));return E(_oS);},_oT=function(_oU){var _oV=E(_oU);return new F(function(){return _oO(_oV.a,_oV.b,_oV.c);});},_oW=new T2(0,_ny,_o7),_oX=function(_oY,_oZ,_p0,_p1,_p2,_p3,_p4){var _p5=B(_8J(B(_8H(_oY)))),_p6=new T(function(){return B(A3(_6X,_p5,new T(function(){return B(A3(_8L,_p5,_oZ,_p2));}),new T(function(){return B(A3(_8L,_p5,_p0,_p3));})));});return new F(function(){return A3(_6X,_p5,_p6,new T(function(){return B(A3(_8L,_p5,_p1,_p4));}));});},_p7=function(_p8,_p9,_pa,_pb){var _pc=B(_8H(_p8)),_pd=new T(function(){return B(A2(_9t,_p8,new T(function(){return B(_oX(_p8,_p9,_pa,_pb,_p9,_pa,_pb));})));});return new T3(0,B(A3(_8P,_pc,_p9,_pd)),B(A3(_8P,_pc,_pa,_pd)),B(A3(_8P,_pc,_pb,_pd)));},_pe=function(_pf,_pg,_ph,_pi,_pj,_pk,_pl){var _pm=B(_8L(_pf));return new T3(0,B(A1(B(A1(_pm,_pg)),_pj)),B(A1(B(A1(_pm,_ph)),_pk)),B(A1(B(A1(_pm,_pi)),_pl)));},_pn=function(_po,_pp,_pq,_pr,_ps,_pt,_pu){var _pv=B(_6X(_po));return new T3(0,B(A1(B(A1(_pv,_pp)),_ps)),B(A1(B(A1(_pv,_pq)),_pt)),B(A1(B(A1(_pv,_pr)),_pu)));},_pw=function(_px,_py){var _pz=new T(function(){return E(E(_px).a);}),_pA=new T(function(){var _pB=E(_py),_pC=new T(function(){return B(_8J(new T(function(){return B(_8H(_pz));})));}),_pD=B(A2(_8s,_pC,_8q));return new T3(0,E(_pD),E(B(A2(_8s,_pC,_8r))),E(_pD));}),_pE=new T(function(){var _pF=E(_pA),_pG=B(_p7(_pz,_pF.a,_pF.b,_pF.c));return new T3(0,E(_pG.a),E(_pG.b),E(_pG.c));}),_pH=new T(function(){var _pI=E(_py),_pJ=_pI.b,_pK=E(_pE),_pL=B(_8H(_pz)),_pM=new T(function(){return B(A2(_9t,_pz,new T(function(){var _pN=E(_pA),_pO=_pN.a,_pP=_pN.b,_pQ=_pN.c;return B(_oX(_pz,_pO,_pP,_pQ,_pO,_pP,_pQ));})));}),_pR=B(A3(_8P,_pL,_pJ,_pM)),_pS=B(_8J(_pL)),_pT=B(_pe(_pS,_pK.a,_pK.b,_pK.c,_pR,_pR,_pR)),_pU=B(_6Z(_pS)),_pV=B(_pn(_pS,_pI.a,_pJ,_pI.c,B(A1(_pU,_pT.a)),B(A1(_pU,_pT.b)),B(A1(_pU,_pT.c))));return new T3(0,E(_pV.a),E(_pV.b),E(_pV.c));});return new T2(0,_pH,_pE);},_pW=function(_pX){return E(E(_pX).a);},_pY=function(_pZ,_q0,_q1,_q2,_q3,_q4,_q5){var _q6=B(_oX(_pZ,_q3,_q4,_q5,_q0,_q1,_q2)),_q7=B(_8J(B(_8H(_pZ)))),_q8=B(_pe(_q7,_q3,_q4,_q5,_q6,_q6,_q6)),_q9=B(_6Z(_q7));return new F(function(){return _pn(_q7,_q0,_q1,_q2,B(A1(_q9,_q8.a)),B(A1(_q9,_q8.b)),B(A1(_q9,_q8.c)));});},_qa=function(_qb){return E(E(_qb).a);},_qc=function(_qd,_qe,_qf,_qg){var _qh=new T(function(){var _qi=E(_qg),_qj=E(_qf),_qk=B(_pY(_qd,_qi.a,_qi.b,_qi.c,_qj.a,_qj.b,_qj.c));return new T3(0,E(_qk.a),E(_qk.b),E(_qk.c));}),_ql=new T(function(){return B(A2(_9t,_qd,new T(function(){var _qm=E(_qh),_qn=_qm.a,_qo=_qm.b,_qp=_qm.c;return B(_oX(_qd,_qn,_qo,_qp,_qn,_qo,_qp));})));});if(!B(A3(_qa,B(_pW(_qe)),_ql,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qd)))),_8q));})))){var _qq=E(_qh),_qr=B(_p7(_qd,_qq.a,_qq.b,_qq.c)),_qs=B(A2(_9t,_qd,new T(function(){var _qt=E(_qg),_qu=_qt.a,_qv=_qt.b,_qw=_qt.c;return B(_oX(_qd,_qu,_qv,_qw,_qu,_qv,_qw));}))),_qx=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qd));})));})));return new T3(0,B(A1(B(A1(_qx,_qr.a)),_qs)),B(A1(B(A1(_qx,_qr.b)),_qs)),B(A1(B(A1(_qx,_qr.c)),_qs)));}else{var _qy=B(A2(_8s,B(_8J(B(_8H(_qd)))),_8q));return new T3(0,_qy,_qy,_qy);}},_qz=new T(function(){var _qA=eval("angleCount"),_qB=Number(_qA);return jsTrunc(_qB);}),_qC=new T(function(){return E(_qz);}),_qD=new T(function(){return B(unCStr(": empty list"));}),_qE=new T(function(){return B(unCStr("Prelude."));}),_qF=function(_qG){return new F(function(){return err(B(_n(_qE,new T(function(){return B(_n(_qG,_qD));},1))));});},_qH=new T(function(){return B(unCStr("head"));}),_qI=new T(function(){return B(_qF(_qH));}),_qJ=function(_qK,_qL,_qM){var _qN=E(_qK);if(!_qN._){return __Z;}else{var _qO=E(_qL);if(!_qO._){return __Z;}else{var _qP=_qO.a,_qQ=E(_qM);if(!_qQ._){return __Z;}else{var _qR=E(_qQ.a),_qS=_qR.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_qN.a),E(_qP),E(_qS));}),new T2(1,new T(function(){return new T3(0,E(_qP),E(_qS),E(_qR.b));}),_w)),new T(function(){return B(_qJ(_qN.b,_qO.b,_qQ.b));},1));});}}}},_qT=new T(function(){return B(unCStr("tail"));}),_qU=new T(function(){return B(_qF(_qT));}),_qV=function(_qW,_qX){var _qY=E(_qW);if(!_qY._){return __Z;}else{var _qZ=E(_qX);return (_qZ._==0)?__Z:new T2(1,new T2(0,_qY.a,_qZ.a),new T(function(){return B(_qV(_qY.b,_qZ.b));}));}},_r0=function(_r1,_r2){var _r3=E(_r1);if(!_r3._){return __Z;}else{var _r4=E(_r2);if(!_r4._){return __Z;}else{var _r5=E(_r3.a),_r6=_r5.b,_r7=E(_r4.a).b,_r8=new T(function(){var _r9=new T(function(){return B(_qV(_r7,new T(function(){var _ra=E(_r7);if(!_ra._){return E(_qU);}else{return E(_ra.b);}},1)));},1);return B(_qJ(_r6,new T(function(){var _rb=E(_r6);if(!_rb._){return E(_qU);}else{return E(_rb.b);}},1),_r9));});return new F(function(){return _n(new T2(1,new T(function(){var _rc=E(_r6);if(!_rc._){return E(_qI);}else{var _rd=E(_r7);if(!_rd._){return E(_qI);}else{return new T3(0,E(_r5.a),E(_rc.a),E(_rd.a));}}}),_r8),new T(function(){return B(_r0(_r3.b,_r4.b));},1));});}}},_re=new T(function(){return E(_qC)-1;}),_rf=new T1(0,1),_rg=function(_rh,_ri){var _rj=E(_ri),_rk=new T(function(){var _rl=B(_8J(_rh)),_rm=B(_rg(_rh,B(A3(_6X,_rl,_rj,new T(function(){return B(A2(_8s,_rl,_rf));})))));return new T2(1,_rm.a,_rm.b);});return new T2(0,_rj,_rk);},_rn=function(_ro){return E(E(_ro).d);},_rp=new T1(0,2),_rq=function(_rr,_rs){var _rt=E(_rs);if(!_rt._){return __Z;}else{var _ru=_rt.a;return (!B(A1(_rr,_ru)))?__Z:new T2(1,_ru,new T(function(){return B(_rq(_rr,_rt.b));}));}},_rv=function(_rw,_rx,_ry,_rz){var _rA=B(_rg(_rx,_ry)),_rB=new T(function(){var _rC=B(_8J(_rx)),_rD=new T(function(){return B(A3(_8P,_rx,new T(function(){return B(A2(_8s,_rC,_rf));}),new T(function(){return B(A2(_8s,_rC,_rp));})));});return B(A3(_6X,_rC,_rz,_rD));});return new F(function(){return _rq(function(_rE){return new F(function(){return A3(_rn,_rw,_rE,_rB);});},new T2(1,_rA.a,_rA.b));});},_rF=new T(function(){return B(_rv(_o7,_n6,_m3,_re));}),_rG=function(_rH,_rI){while(1){var _rJ=E(_rH);if(!_rJ._){return E(_rI);}else{_rH=_rJ.b;_rI=_rJ.a;continue;}}},_rK=new T(function(){return B(unCStr("last"));}),_rL=new T(function(){return B(_qF(_rK));}),_rM=function(_rN){return new F(function(){return _rG(_rN,_rL);});},_rO=function(_rP){return new F(function(){return _rM(E(_rP).b);});},_rQ=new T(function(){var _rR=eval("proceedCount"),_rS=Number(_rR);return jsTrunc(_rS);}),_rT=new T(function(){return E(_rQ);}),_rU=1,_rV=new T(function(){return B(_rv(_o7,_n6,_rU,_rT));}),_rW=function(_rX,_rY,_rZ,_s0,_s1,_s2,_s3,_s4,_s5,_s6,_s7,_s8,_s9,_sa){var _sb=new T(function(){var _sc=new T(function(){var _sd=E(_s6),_se=E(_sa),_sf=E(_s9),_sg=E(_s7),_sh=E(_s8),_si=E(_s5);return new T3(0,_sd*_se-_sf*_sg,_sg*_sh-_se*_si,_si*_sf-_sh*_sd);}),_sj=function(_sk){var _sl=new T(function(){var _sm=E(_sk)/E(_qC);return (_sm+_sm)*3.141592653589793;}),_sn=new T(function(){return B(A1(_rX,_sl));}),_so=new T(function(){var _sp=new T(function(){var _sq=E(_sn)/E(_rT);return new T3(0,E(_sq),E(_sq),E(_sq));}),_sr=function(_ss,_st){var _su=E(_ss);if(!_su._){return new T2(0,_w,_st);}else{var _sv=new T(function(){var _sw=B(_pw(_oW,new T(function(){var _sx=E(_st),_sy=E(_sx.a),_sz=E(_sx.b),_sA=E(_sp);return new T3(0,E(_sy.a)+E(_sz.a)*E(_sA.a),E(_sy.b)+E(_sz.b)*E(_sA.b),E(_sy.c)+E(_sz.c)*E(_sA.c));}))),_sB=_sw.a,_sC=new T(function(){var _sD=E(_sw.b),_sE=E(E(_st).b),_sF=B(_pY(_ny,_sE.a,_sE.b,_sE.c,_sD.a,_sD.b,_sD.c)),_sG=B(_p7(_ny,_sF.a,_sF.b,_sF.c));return new T3(0,E(_sG.a),E(_sG.b),E(_sG.c));});return new T2(0,new T(function(){var _sH=E(_sn),_sI=E(_sl);return new T4(0,E(_sB),E(new T2(0,E(_su.a)/E(_rT),E(_sH))),E(_sI),E(_sC));}),new T2(0,_sB,_sC));}),_sJ=new T(function(){var _sK=B(_sr(_su.b,new T(function(){return E(E(_sv).b);})));return new T2(0,_sK.a,_sK.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sv).a);}),new T(function(){return E(E(_sJ).a);})),new T(function(){return E(E(_sJ).b);}));}},_sL=function(_sM,_sN,_sO,_sP,_sQ){var _sR=E(_sM);if(!_sR._){return new T2(0,_w,new T2(0,new T3(0,E(_sN),E(_sO),E(_sP)),_sQ));}else{var _sS=new T(function(){var _sT=B(_pw(_oW,new T(function(){var _sU=E(_sQ),_sV=E(_sp);return new T3(0,E(_sN)+E(_sU.a)*E(_sV.a),E(_sO)+E(_sU.b)*E(_sV.b),E(_sP)+E(_sU.c)*E(_sV.c));}))),_sW=_sT.a,_sX=new T(function(){var _sY=E(_sT.b),_sZ=E(_sQ),_t0=B(_pY(_ny,_sZ.a,_sZ.b,_sZ.c,_sY.a,_sY.b,_sY.c)),_t1=B(_p7(_ny,_t0.a,_t0.b,_t0.c));return new T3(0,E(_t1.a),E(_t1.b),E(_t1.c));});return new T2(0,new T(function(){var _t2=E(_sn),_t3=E(_sl);return new T4(0,E(_sW),E(new T2(0,E(_sR.a)/E(_rT),E(_t2))),E(_t3),E(_sX));}),new T2(0,_sW,_sX));}),_t4=new T(function(){var _t5=B(_sr(_sR.b,new T(function(){return E(E(_sS).b);})));return new T2(0,_t5.a,_t5.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sS).a);}),new T(function(){return E(E(_t4).a);})),new T(function(){return E(E(_t4).b);}));}};return E(B(_sL(_rV,_s0,_s1,_s2,new T(function(){var _t6=E(_sc),_t7=E(_sl)+_s3,_t8=Math.cos(_t7),_t9=Math.sin(_t7);return new T3(0,E(_s5)*_t8+E(_t6.a)*_t9,E(_s6)*_t8+E(_t6.b)*_t9,E(_s7)*_t8+E(_t6.c)*_t9);}))).a);});return new T2(0,new T(function(){var _ta=E(_sn),_tb=E(_sl);return new T4(0,E(new T3(0,E(_s0),E(_s1),E(_s2))),E(new T2(0,E(_m3),E(_ta))),E(_tb),E(_m4));}),_so);};return B(_oK(_sj,_rF));}),_tc=new T(function(){var _td=new T(function(){var _te=B(_n(_sb,new T2(1,new T(function(){var _tf=E(_sb);if(!_tf._){return E(_qI);}else{return E(_tf.a);}}),_w)));if(!_te._){return E(_qU);}else{return E(_te.b);}},1);return B(_r0(_sb,_td));});return new T2(0,_tc,new T(function(){return B(_oK(_rO,_sb));}));},_tg=function(_th,_ti,_tj,_tk,_tl,_tm,_tn,_to,_tp,_tq,_tr,_ts,_tt,_tu,_tv,_tw,_tx){var _ty=B(_pw(_oW,new T3(0,E(_tk),E(_tl),E(_tm)))),_tz=_ty.b,_tA=E(_ty.a),_tB=B(_qc(_ny,_o7,_tz,new T3(0,E(_to),E(_tp),E(_tq)))),_tC=E(_tz),_tD=_tC.a,_tE=_tC.b,_tF=_tC.c,_tG=B(_pY(_ny,_ts,_tt,_tu,_tD,_tE,_tF)),_tH=B(_p7(_ny,_tG.a,_tG.b,_tG.c)),_tI=_tH.a,_tJ=_tH.b,_tK=_tH.c,_tL=E(_tn),_tM=new T2(0,E(new T3(0,E(_tB.a),E(_tB.b),E(_tB.c))),E(_tr)),_tN=B(_rW(_th,_ti,_tj,_tA.a,_tA.b,_tA.c,_tL,_tM,_tI,_tJ,_tK,_tD,_tE,_tF)),_tO=__lst2arr(B(_oK(_oT,_tN.a))),_tP=__lst2arr(B(_oK(_oE,_tN.b)));return {_:0,a:_th,b:_ti,c:_tj,d:new T2(0,E(_tA),E(_tL)),e:_tM,f:new T3(0,E(_tI),E(_tJ),E(_tK)),g:_tC,h:_tO,i:_tP};},_tQ=-4,_tR=new T3(0,E(_m3),E(_m3),E(_tQ)),_tS=function(_tT){return E(_tR);},_tU=new T(function(){return 6.283185307179586/E(_qC);}),_tV=function(_){return new F(function(){return __jsNull();});},_tW=function(_tX){var _tY=B(A1(_tX,_));return E(_tY);},_tZ=new T(function(){return B(_tW(_tV));}),_u0=function(_u1,_u2,_u3,_u4,_u5,_u6,_u7,_u8,_u9,_ua,_ub,_uc,_ud){var _ue=function(_uf){var _ug=E(_tU),_uh=2+_uf|0,_ui=_uh-1|0,_uj=(2+_uf)*(1+_uf),_uk=E(_rF);if(!_uk._){return _ug*0;}else{var _ul=_uk.a,_um=_uk.b,_un=B(A1(_u1,new T(function(){return 6.283185307179586*E(_ul)/E(_qC);}))),_uo=B(A1(_u1,new T(function(){return 6.283185307179586*(E(_ul)+1)/E(_qC);})));if(_un!=_uo){if(_uh>=0){var _up=E(_uh);if(!_up){var _uq=function(_ur,_us){while(1){var _ut=B((function(_uu,_uv){var _uw=E(_uu);if(!_uw._){return E(_uv);}else{var _ux=_uw.a,_uy=_uw.b,_uz=B(A1(_u1,new T(function(){return 6.283185307179586*E(_ux)/E(_qC);}))),_uA=B(A1(_u1,new T(function(){return 6.283185307179586*(E(_ux)+1)/E(_qC);})));if(_uz!=_uA){var _uB=_uv+0/(_uz-_uA)/_uj;_ur=_uy;_us=_uB;return __continue;}else{if(_ui>=0){var _uC=E(_ui);if(!_uC){var _uB=_uv+_uh/_uj;_ur=_uy;_us=_uB;return __continue;}else{var _uB=_uv+_uh*B(_mf(_uz,_uC))/_uj;_ur=_uy;_us=_uB;return __continue;}}else{return E(_m6);}}}})(_ur,_us));if(_ut!=__continue){return _ut;}}};return _ug*B(_uq(_um,0/(_un-_uo)/_uj));}else{var _uD=function(_uE,_uF){while(1){var _uG=B((function(_uH,_uI){var _uJ=E(_uH);if(!_uJ._){return E(_uI);}else{var _uK=_uJ.a,_uL=_uJ.b,_uM=B(A1(_u1,new T(function(){return 6.283185307179586*E(_uK)/E(_qC);}))),_uN=B(A1(_u1,new T(function(){return 6.283185307179586*(E(_uK)+1)/E(_qC);})));if(_uM!=_uN){if(_up>=0){var _uO=_uI+(B(_mf(_uM,_up))-B(_mf(_uN,_up)))/(_uM-_uN)/_uj;_uE=_uL;_uF=_uO;return __continue;}else{return E(_m6);}}else{if(_ui>=0){var _uP=E(_ui);if(!_uP){var _uO=_uI+_uh/_uj;_uE=_uL;_uF=_uO;return __continue;}else{var _uO=_uI+_uh*B(_mf(_uM,_uP))/_uj;_uE=_uL;_uF=_uO;return __continue;}}else{return E(_m6);}}}})(_uE,_uF));if(_uG!=__continue){return _uG;}}};return _ug*B(_uD(_um,(B(_mf(_un,_up))-B(_mf(_uo,_up)))/(_un-_uo)/_uj));}}else{return E(_m6);}}else{if(_ui>=0){var _uQ=E(_ui);if(!_uQ){var _uR=function(_uS,_uT){while(1){var _uU=B((function(_uV,_uW){var _uX=E(_uV);if(!_uX._){return E(_uW);}else{var _uY=_uX.a,_uZ=_uX.b,_v0=B(A1(_u1,new T(function(){return 6.283185307179586*E(_uY)/E(_qC);}))),_v1=B(A1(_u1,new T(function(){return 6.283185307179586*(E(_uY)+1)/E(_qC);})));if(_v0!=_v1){if(_uh>=0){var _v2=E(_uh);if(!_v2){var _v3=_uW+0/(_v0-_v1)/_uj;_uS=_uZ;_uT=_v3;return __continue;}else{var _v3=_uW+(B(_mf(_v0,_v2))-B(_mf(_v1,_v2)))/(_v0-_v1)/_uj;_uS=_uZ;_uT=_v3;return __continue;}}else{return E(_m6);}}else{var _v3=_uW+_uh/_uj;_uS=_uZ;_uT=_v3;return __continue;}}})(_uS,_uT));if(_uU!=__continue){return _uU;}}};return _ug*B(_uR(_um,_uh/_uj));}else{var _v4=function(_v5,_v6){while(1){var _v7=B((function(_v8,_v9){var _va=E(_v8);if(!_va._){return E(_v9);}else{var _vb=_va.a,_vc=_va.b,_vd=B(A1(_u1,new T(function(){return 6.283185307179586*E(_vb)/E(_qC);}))),_ve=B(A1(_u1,new T(function(){return 6.283185307179586*(E(_vb)+1)/E(_qC);})));if(_vd!=_ve){if(_uh>=0){var _vf=E(_uh);if(!_vf){var _vg=_v9+0/(_vd-_ve)/_uj;_v5=_vc;_v6=_vg;return __continue;}else{var _vg=_v9+(B(_mf(_vd,_vf))-B(_mf(_ve,_vf)))/(_vd-_ve)/_uj;_v5=_vc;_v6=_vg;return __continue;}}else{return E(_m6);}}else{if(_uQ>=0){var _vg=_v9+_uh*B(_mf(_vd,_uQ))/_uj;_v5=_vc;_v6=_vg;return __continue;}else{return E(_m6);}}}})(_v5,_v6));if(_v7!=__continue){return _v7;}}};return _ug*B(_v4(_um,_uh*B(_mf(_un,_uQ))/_uj));}}else{return E(_m6);}}}},_vh=E(_tZ),_vi=1/(B(_ue(1))*_u2);return new F(function(){return _tg(_u1,_tS,new T2(0,E(new T3(0,E(_vi),E(_vi),E(_vi))),1/(B(_ue(3))*_u2)),_u3,_u4,_u5,_u6,_u7,_u8,_u9,_ua,_ub,_uc,_ud,_m4,_vh,_vh);});},_vj=1,_vk=0,_vl=function(_vm){var _vn=I_decodeDouble(_vm);return new T2(0,new T1(1,_vn.b),_vn.a);},_vo=function(_vp){return new T1(0,_vp);},_vq=function(_vr){var _vs=hs_intToInt64(2147483647),_vt=hs_leInt64(_vr,_vs);if(!_vt){return new T1(1,I_fromInt64(_vr));}else{var _vu=hs_intToInt64(-2147483648),_vv=hs_geInt64(_vr,_vu);if(!_vv){return new T1(1,I_fromInt64(_vr));}else{var _vw=hs_int64ToInt(_vr);return new F(function(){return _vo(_vw);});}}},_vx=new T(function(){var _vy=newByteArr(256),_vz=_vy,_=_vz["v"]["i8"][0]=8,_vA=function(_vB,_vC,_vD,_){while(1){if(_vD>=256){if(_vB>=256){return E(_);}else{var _vE=imul(2,_vB)|0,_vF=_vC+1|0,_vG=_vB;_vB=_vE;_vC=_vF;_vD=_vG;continue;}}else{var _=_vz["v"]["i8"][_vD]=_vC,_vG=_vD+_vB|0;_vD=_vG;continue;}}},_=B(_vA(2,0,1,_));return _vz;}),_vH=function(_vI,_vJ){var _vK=hs_int64ToInt(_vI),_vL=E(_vx),_vM=_vL["v"]["i8"][(255&_vK>>>0)>>>0&4294967295];if(_vJ>_vM){if(_vM>=8){var _vN=hs_uncheckedIShiftRA64(_vI,8),_vO=function(_vP,_vQ){while(1){var _vR=B((function(_vS,_vT){var _vU=hs_int64ToInt(_vS),_vV=_vL["v"]["i8"][(255&_vU>>>0)>>>0&4294967295];if(_vT>_vV){if(_vV>=8){var _vW=hs_uncheckedIShiftRA64(_vS,8),_vX=_vT-8|0;_vP=_vW;_vQ=_vX;return __continue;}else{return new T2(0,new T(function(){var _vY=hs_uncheckedIShiftRA64(_vS,_vV);return B(_vq(_vY));}),_vT-_vV|0);}}else{return new T2(0,new T(function(){var _vZ=hs_uncheckedIShiftRA64(_vS,_vT);return B(_vq(_vZ));}),0);}})(_vP,_vQ));if(_vR!=__continue){return _vR;}}};return new F(function(){return _vO(_vN,_vJ-8|0);});}else{return new T2(0,new T(function(){var _w0=hs_uncheckedIShiftRA64(_vI,_vM);return B(_vq(_w0));}),_vJ-_vM|0);}}else{return new T2(0,new T(function(){var _w1=hs_uncheckedIShiftRA64(_vI,_vJ);return B(_vq(_w1));}),0);}},_w2=function(_w3){var _w4=hs_intToInt64(_w3);return E(_w4);},_w5=function(_w6){var _w7=E(_w6);if(!_w7._){return new F(function(){return _w2(_w7.a);});}else{return new F(function(){return I_toInt64(_w7.a);});}},_w8=function(_w9){return I_toInt(_w9)>>>0;},_wa=function(_wb){var _wc=E(_wb);if(!_wc._){return _wc.a>>>0;}else{return new F(function(){return _w8(_wc.a);});}},_wd=function(_we){var _wf=B(_vl(_we)),_wg=_wf.a,_wh=_wf.b;if(_wh<0){var _wi=function(_wj){if(!_wj){return new T2(0,E(_wg),B(_3J(_21, -_wh)));}else{var _wk=B(_vH(B(_w5(_wg)), -_wh));return new T2(0,E(_wk.a),B(_3J(_21,_wk.b)));}};if(!((B(_wa(_wg))&1)>>>0)){return new F(function(){return _wi(1);});}else{return new F(function(){return _wi(0);});}}else{return new T2(0,B(_3J(_wg,_wh)),_21);}},_wl=function(_wm){var _wn=B(_wd(E(_wm)));return new T2(0,E(_wn.a),E(_wn.b));},_wo=new T3(0,_n2,_o7,_wl),_wp=function(_wq){return E(E(_wq).a);},_wr=function(_ws){return E(E(_ws).a);},_wt=function(_wu,_wv){if(_wu<=_wv){var _ww=function(_wx){return new T2(1,_wx,new T(function(){if(_wx!=_wv){return B(_ww(_wx+1|0));}else{return __Z;}}));};return new F(function(){return _ww(_wu);});}else{return __Z;}},_wy=function(_wz){return new F(function(){return _wt(E(_wz),2147483647);});},_wA=function(_wB,_wC,_wD){if(_wD<=_wC){var _wE=new T(function(){var _wF=_wC-_wB|0,_wG=function(_wH){return (_wH>=(_wD-_wF|0))?new T2(1,_wH,new T(function(){return B(_wG(_wH+_wF|0));})):new T2(1,_wH,_w);};return B(_wG(_wC));});return new T2(1,_wB,_wE);}else{return (_wD<=_wB)?new T2(1,_wB,_w):__Z;}},_wI=function(_wJ,_wK,_wL){if(_wL>=_wK){var _wM=new T(function(){var _wN=_wK-_wJ|0,_wO=function(_wP){return (_wP<=(_wL-_wN|0))?new T2(1,_wP,new T(function(){return B(_wO(_wP+_wN|0));})):new T2(1,_wP,_w);};return B(_wO(_wK));});return new T2(1,_wJ,_wM);}else{return (_wL>=_wJ)?new T2(1,_wJ,_w):__Z;}},_wQ=function(_wR,_wS){if(_wS<_wR){return new F(function(){return _wA(_wR,_wS,-2147483648);});}else{return new F(function(){return _wI(_wR,_wS,2147483647);});}},_wT=function(_wU,_wV){return new F(function(){return _wQ(E(_wU),E(_wV));});},_wW=function(_wX,_wY,_wZ){if(_wY<_wX){return new F(function(){return _wA(_wX,_wY,_wZ);});}else{return new F(function(){return _wI(_wX,_wY,_wZ);});}},_x0=function(_x1,_x2,_x3){return new F(function(){return _wW(E(_x1),E(_x2),E(_x3));});},_x4=function(_x5,_x6){return new F(function(){return _wt(E(_x5),E(_x6));});},_x7=function(_x8){return E(_x8);},_x9=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xa=new T(function(){return B(err(_x9));}),_xb=function(_xc){var _xd=E(_xc);return (_xd==(-2147483648))?E(_xa):_xd-1|0;},_xe=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xf=new T(function(){return B(err(_xe));}),_xg=function(_xh){var _xi=E(_xh);return (_xi==2147483647)?E(_xf):_xi+1|0;},_xj={_:0,a:_xg,b:_xb,c:_x7,d:_x7,e:_wy,f:_wT,g:_x4,h:_x0},_xk=function(_xl,_xm){if(_xl<=0){if(_xl>=0){return new F(function(){return quot(_xl,_xm);});}else{if(_xm<=0){return new F(function(){return quot(_xl,_xm);});}else{return quot(_xl+1|0,_xm)-1|0;}}}else{if(_xm>=0){if(_xl>=0){return new F(function(){return quot(_xl,_xm);});}else{if(_xm<=0){return new F(function(){return quot(_xl,_xm);});}else{return quot(_xl+1|0,_xm)-1|0;}}}else{return quot(_xl-1|0,_xm)-1|0;}}},_xn=0,_xo=new T(function(){return B(_36(_xn));}),_xp=new T(function(){return die(_xo);}),_xq=function(_xr,_xs){var _xt=E(_xs);switch(_xt){case -1:var _xu=E(_xr);if(_xu==(-2147483648)){return E(_xp);}else{return new F(function(){return _xk(_xu,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xk(_xr,_xt);});}},_xv=function(_xw,_xx){return new F(function(){return _xq(E(_xw),E(_xx));});},_xy=0,_xz=new T2(0,_xp,_xy),_xA=function(_xB,_xC){var _xD=E(_xB),_xE=E(_xC);switch(_xE){case -1:var _xF=E(_xD);if(_xF==(-2147483648)){return E(_xz);}else{if(_xF<=0){if(_xF>=0){var _xG=quotRemI(_xF,-1);return new T2(0,_xG.a,_xG.b);}else{var _xH=quotRemI(_xF,-1);return new T2(0,_xH.a,_xH.b);}}else{var _xI=quotRemI(_xF-1|0,-1);return new T2(0,_xI.a-1|0,(_xI.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_xD<=0){if(_xD>=0){var _xJ=quotRemI(_xD,_xE);return new T2(0,_xJ.a,_xJ.b);}else{if(_xE<=0){var _xK=quotRemI(_xD,_xE);return new T2(0,_xK.a,_xK.b);}else{var _xL=quotRemI(_xD+1|0,_xE);return new T2(0,_xL.a-1|0,(_xL.b+_xE|0)-1|0);}}}else{if(_xE>=0){if(_xD>=0){var _xM=quotRemI(_xD,_xE);return new T2(0,_xM.a,_xM.b);}else{if(_xE<=0){var _xN=quotRemI(_xD,_xE);return new T2(0,_xN.a,_xN.b);}else{var _xO=quotRemI(_xD+1|0,_xE);return new T2(0,_xO.a-1|0,(_xO.b+_xE|0)-1|0);}}}else{var _xP=quotRemI(_xD-1|0,_xE);return new T2(0,_xP.a-1|0,(_xP.b+_xE|0)+1|0);}}}},_xQ=function(_xR,_xS){var _xT=_xR%_xS;if(_xR<=0){if(_xR>=0){return E(_xT);}else{if(_xS<=0){return E(_xT);}else{var _xU=E(_xT);return (_xU==0)?0:_xU+_xS|0;}}}else{if(_xS>=0){if(_xR>=0){return E(_xT);}else{if(_xS<=0){return E(_xT);}else{var _xV=E(_xT);return (_xV==0)?0:_xV+_xS|0;}}}else{var _xW=E(_xT);return (_xW==0)?0:_xW+_xS|0;}}},_xX=function(_xY,_xZ){var _y0=E(_xZ);switch(_y0){case -1:return E(_xy);case 0:return E(_3a);default:return new F(function(){return _xQ(E(_xY),_y0);});}},_y1=function(_y2,_y3){var _y4=E(_y2),_y5=E(_y3);switch(_y5){case -1:var _y6=E(_y4);if(_y6==(-2147483648)){return E(_xp);}else{return new F(function(){return quot(_y6,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_y4,_y5);});}},_y7=function(_y8,_y9){var _ya=E(_y8),_yb=E(_y9);switch(_yb){case -1:var _yc=E(_ya);if(_yc==(-2147483648)){return E(_xz);}else{var _yd=quotRemI(_yc,-1);return new T2(0,_yd.a,_yd.b);}break;case 0:return E(_3a);default:var _ye=quotRemI(_ya,_yb);return new T2(0,_ye.a,_ye.b);}},_yf=function(_yg,_yh){var _yi=E(_yh);switch(_yi){case -1:return E(_xy);case 0:return E(_3a);default:return E(_yg)%_yi;}},_yj=function(_yk){return new F(function(){return _vo(E(_yk));});},_yl=function(_ym){return new T2(0,E(B(_vo(E(_ym)))),E(_rf));},_yn=function(_yo,_yp){return imul(E(_yo),E(_yp))|0;},_yq=function(_yr,_ys){return E(_yr)+E(_ys)|0;},_yt=function(_yu,_yv){return E(_yu)-E(_yv)|0;},_yw=function(_yx){var _yy=E(_yx);return (_yy<0)? -_yy:E(_yy);},_yz=function(_yA){return new F(function(){return _3n(_yA);});},_yB=function(_yC){return  -E(_yC);},_yD=-1,_yE=0,_yF=1,_yG=function(_yH){var _yI=E(_yH);return (_yI>=0)?(E(_yI)==0)?E(_yE):E(_yF):E(_yD);},_yJ={_:0,a:_yq,b:_yt,c:_yn,d:_yB,e:_yw,f:_yG,g:_yz},_yK=function(_yL,_yM){return E(_yL)==E(_yM);},_yN=function(_yO,_yP){return E(_yO)!=E(_yP);},_yQ=new T2(0,_yK,_yN),_yR=function(_yS,_yT){var _yU=E(_yS),_yV=E(_yT);return (_yU>_yV)?E(_yU):E(_yV);},_yW=function(_yX,_yY){var _yZ=E(_yX),_z0=E(_yY);return (_yZ>_z0)?E(_z0):E(_yZ);},_z1=function(_z2,_z3){return (_z2>=_z3)?(_z2!=_z3)?2:1:0;},_z4=function(_z5,_z6){return new F(function(){return _z1(E(_z5),E(_z6));});},_z7=function(_z8,_z9){return E(_z8)>=E(_z9);},_za=function(_zb,_zc){return E(_zb)>E(_zc);},_zd=function(_ze,_zf){return E(_ze)<=E(_zf);},_zg=function(_zh,_zi){return E(_zh)<E(_zi);},_zj={_:0,a:_yQ,b:_z4,c:_zg,d:_zd,e:_za,f:_z7,g:_yR,h:_yW},_zk=new T3(0,_yJ,_zj,_yl),_zl={_:0,a:_zk,b:_xj,c:_y1,d:_yf,e:_xv,f:_xX,g:_y7,h:_xA,i:_yj},_zm=new T1(0,2),_zn=function(_zo,_zp){while(1){var _zq=E(_zo);if(!_zq._){var _zr=_zq.a,_zs=E(_zp);if(!_zs._){var _zt=_zs.a;if(!(imul(_zr,_zt)|0)){return new T1(0,imul(_zr,_zt)|0);}else{_zo=new T1(1,I_fromInt(_zr));_zp=new T1(1,I_fromInt(_zt));continue;}}else{_zo=new T1(1,I_fromInt(_zr));_zp=_zs;continue;}}else{var _zu=E(_zp);if(!_zu._){_zo=_zq;_zp=new T1(1,I_fromInt(_zu.a));continue;}else{return new T1(1,I_mul(_zq.a,_zu.a));}}}},_zv=function(_zw,_zx,_zy){while(1){if(!(_zx%2)){var _zz=B(_zn(_zw,_zw)),_zA=quot(_zx,2);_zw=_zz;_zx=_zA;continue;}else{var _zB=E(_zx);if(_zB==1){return new F(function(){return _zn(_zw,_zy);});}else{var _zz=B(_zn(_zw,_zw)),_zC=B(_zn(_zw,_zy));_zw=_zz;_zx=quot(_zB-1|0,2);_zy=_zC;continue;}}}},_zD=function(_zE,_zF){while(1){if(!(_zF%2)){var _zG=B(_zn(_zE,_zE)),_zH=quot(_zF,2);_zE=_zG;_zF=_zH;continue;}else{var _zI=E(_zF);if(_zI==1){return E(_zE);}else{return new F(function(){return _zv(B(_zn(_zE,_zE)),quot(_zI-1|0,2),_zE);});}}}},_zJ=function(_zK){return E(E(_zK).b);},_zL=function(_zM){return E(E(_zM).c);},_zN=new T1(0,0),_zO=function(_zP){return E(E(_zP).d);},_zQ=function(_zR,_zS){var _zT=B(_wp(_zR)),_zU=new T(function(){return B(_wr(_zT));}),_zV=new T(function(){return B(A3(_zO,_zR,_zS,new T(function(){return B(A2(_8s,_zU,_rp));})));});return new F(function(){return A3(_qa,B(_pW(B(_zJ(_zT)))),_zV,new T(function(){return B(A2(_8s,_zU,_zN));}));});},_zW=new T(function(){return B(unCStr("Negative exponent"));}),_zX=new T(function(){return B(err(_zW));}),_zY=function(_zZ){return E(E(_zZ).c);},_A0=function(_A1,_A2,_A3,_A4){var _A5=B(_wp(_A2)),_A6=new T(function(){return B(_wr(_A5));}),_A7=B(_zJ(_A5));if(!B(A3(_zL,_A7,_A4,new T(function(){return B(A2(_8s,_A6,_zN));})))){if(!B(A3(_qa,B(_pW(_A7)),_A4,new T(function(){return B(A2(_8s,_A6,_zN));})))){var _A8=new T(function(){return B(A2(_8s,_A6,_rp));}),_A9=new T(function(){return B(A2(_8s,_A6,_rf));}),_Aa=B(_pW(_A7)),_Ab=function(_Ac,_Ad,_Ae){while(1){var _Af=B((function(_Ag,_Ah,_Ai){if(!B(_zQ(_A2,_Ah))){if(!B(A3(_qa,_Aa,_Ah,_A9))){var _Aj=new T(function(){return B(A3(_zY,_A2,new T(function(){return B(A3(_9p,_A6,_Ah,_A9));}),_A8));});_Ac=new T(function(){return B(A3(_8L,_A1,_Ag,_Ag));});_Ad=_Aj;_Ae=new T(function(){return B(A3(_8L,_A1,_Ag,_Ai));});return __continue;}else{return new F(function(){return A3(_8L,_A1,_Ag,_Ai);});}}else{var _Ak=_Ai;_Ac=new T(function(){return B(A3(_8L,_A1,_Ag,_Ag));});_Ad=new T(function(){return B(A3(_zY,_A2,_Ah,_A8));});_Ae=_Ak;return __continue;}})(_Ac,_Ad,_Ae));if(_Af!=__continue){return _Af;}}},_Al=function(_Am,_An){while(1){var _Ao=B((function(_Ap,_Aq){if(!B(_zQ(_A2,_Aq))){if(!B(A3(_qa,_Aa,_Aq,_A9))){var _Ar=new T(function(){return B(A3(_zY,_A2,new T(function(){return B(A3(_9p,_A6,_Aq,_A9));}),_A8));});return new F(function(){return _Ab(new T(function(){return B(A3(_8L,_A1,_Ap,_Ap));}),_Ar,_Ap);});}else{return E(_Ap);}}else{_Am=new T(function(){return B(A3(_8L,_A1,_Ap,_Ap));});_An=new T(function(){return B(A3(_zY,_A2,_Aq,_A8));});return __continue;}})(_Am,_An));if(_Ao!=__continue){return _Ao;}}};return new F(function(){return _Al(_A3,_A4);});}else{return new F(function(){return A2(_8s,_A1,_rf);});}}else{return E(_zX);}},_As=new T(function(){return B(err(_zW));}),_At=function(_Au,_Av){var _Aw=B(_vl(_Av)),_Ax=_Aw.a,_Ay=_Aw.b,_Az=new T(function(){return B(_wr(new T(function(){return B(_wp(_Au));})));});if(_Ay<0){var _AA= -_Ay;if(_AA>=0){var _AB=E(_AA);if(!_AB){var _AC=E(_rf);}else{var _AC=B(_zD(_zm,_AB));}if(!B(_3f(_AC,_3I))){var _AD=B(_3z(_Ax,_AC));return new T2(0,new T(function(){return B(A2(_8s,_Az,_AD.a));}),new T(function(){return B(_3b(_AD.b,_Ay));}));}else{return E(_3a);}}else{return E(_As);}}else{var _AE=new T(function(){var _AF=new T(function(){return B(_A0(_Az,_zl,new T(function(){return B(A2(_8s,_Az,_zm));}),_Ay));});return B(A3(_8L,_Az,new T(function(){return B(A2(_8s,_Az,_Ax));}),_AF));});return new T2(0,_AE,_6x);}},_AG=function(_AH,_AI){var _AJ=B(_At(_AH,E(_AI))),_AK=_AJ.a;if(E(_AJ.b)<=0){return E(_AK);}else{var _AL=B(_wr(B(_wp(_AH))));return new F(function(){return A3(_6X,_AL,_AK,new T(function(){return B(A2(_8s,_AL,_21));}));});}},_AM=function(_AN,_AO){var _AP=B(_At(_AN,E(_AO))),_AQ=_AP.a;if(E(_AP.b)>=0){return E(_AQ);}else{var _AR=B(_wr(B(_wp(_AN))));return new F(function(){return A3(_9p,_AR,_AQ,new T(function(){return B(A2(_8s,_AR,_21));}));});}},_AS=function(_AT,_AU){var _AV=B(_At(_AT,E(_AU)));return new T2(0,_AV.a,_AV.b);},_AW=function(_AX,_AY){var _AZ=B(_At(_AX,_AY)),_B0=_AZ.a,_B1=E(_AZ.b),_B2=new T(function(){var _B3=B(_wr(B(_wp(_AX))));if(_B1>=0){return B(A3(_6X,_B3,_B0,new T(function(){return B(A2(_8s,_B3,_21));})));}else{return B(A3(_9p,_B3,_B0,new T(function(){return B(A2(_8s,_B3,_21));})));}}),_B4=function(_B5){var _B6=_B5-0.5;return (_B6>=0)?(E(_B6)==0)?(!B(_zQ(_AX,_B0)))?E(_B2):E(_B0):E(_B2):E(_B0);},_B7=E(_B1);if(!_B7){return new F(function(){return _B4(0);});}else{if(_B7<=0){var _B8= -_B7-0.5;return (_B8>=0)?(E(_B8)==0)?(!B(_zQ(_AX,_B0)))?E(_B2):E(_B0):E(_B2):E(_B0);}else{return new F(function(){return _B4(_B7);});}}},_B9=function(_Ba,_Bb){return new F(function(){return _AW(_Ba,E(_Bb));});},_Bc=function(_Bd,_Be){return E(B(_At(_Bd,E(_Be))).a);},_Bf={_:0,a:_wo,b:_n6,c:_AS,d:_Bc,e:_B9,f:_AG,g:_AM},_Bg=new T1(0,1),_Bh=function(_Bi,_Bj){var _Bk=E(_Bi);return new T2(0,_Bk,new T(function(){var _Bl=B(_Bh(B(_3q(_Bk,_Bj)),_Bj));return new T2(1,_Bl.a,_Bl.b);}));},_Bm=function(_Bn){var _Bo=B(_Bh(_Bn,_Bg));return new T2(1,_Bo.a,_Bo.b);},_Bp=function(_Bq,_Br){var _Bs=B(_Bh(_Bq,new T(function(){return B(_5L(_Br,_Bq));})));return new T2(1,_Bs.a,_Bs.b);},_Bt=new T1(0,0),_Bu=function(_Bv,_Bw){var _Bx=E(_Bv);if(!_Bx._){var _By=_Bx.a,_Bz=E(_Bw);return (_Bz._==0)?_By>=_Bz.a:I_compareInt(_Bz.a,_By)<=0;}else{var _BA=_Bx.a,_BB=E(_Bw);return (_BB._==0)?I_compareInt(_BA,_BB.a)>=0:I_compare(_BA,_BB.a)>=0;}},_BC=function(_BD,_BE,_BF){if(!B(_Bu(_BE,_Bt))){var _BG=function(_BH){return (!B(_42(_BH,_BF)))?new T2(1,_BH,new T(function(){return B(_BG(B(_3q(_BH,_BE))));})):__Z;};return new F(function(){return _BG(_BD);});}else{var _BI=function(_BJ){return (!B(_3T(_BJ,_BF)))?new T2(1,_BJ,new T(function(){return B(_BI(B(_3q(_BJ,_BE))));})):__Z;};return new F(function(){return _BI(_BD);});}},_BK=function(_BL,_BM,_BN){return new F(function(){return _BC(_BL,B(_5L(_BM,_BL)),_BN);});},_BO=function(_BP,_BQ){return new F(function(){return _BC(_BP,_Bg,_BQ);});},_BR=function(_BS){return new F(function(){return _3n(_BS);});},_BT=function(_BU){return new F(function(){return _5L(_BU,_Bg);});},_BV=function(_BW){return new F(function(){return _3q(_BW,_Bg);});},_BX=function(_BY){return new F(function(){return _vo(E(_BY));});},_BZ={_:0,a:_BV,b:_BT,c:_BX,d:_BR,e:_Bm,f:_Bp,g:_BO,h:_BK},_C0=function(_C1,_C2){while(1){var _C3=E(_C1);if(!_C3._){var _C4=E(_C3.a);if(_C4==(-2147483648)){_C1=new T1(1,I_fromInt(-2147483648));continue;}else{var _C5=E(_C2);if(!_C5._){return new T1(0,B(_xk(_C4,_C5.a)));}else{_C1=new T1(1,I_fromInt(_C4));_C2=_C5;continue;}}}else{var _C6=_C3.a,_C7=E(_C2);return (_C7._==0)?new T1(1,I_div(_C6,I_fromInt(_C7.a))):new T1(1,I_div(_C6,_C7.a));}}},_C8=function(_C9,_Ca){if(!B(_3f(_Ca,_zN))){return new F(function(){return _C0(_C9,_Ca);});}else{return E(_3a);}},_Cb=function(_Cc,_Cd){while(1){var _Ce=E(_Cc);if(!_Ce._){var _Cf=E(_Ce.a);if(_Cf==(-2147483648)){_Cc=new T1(1,I_fromInt(-2147483648));continue;}else{var _Cg=E(_Cd);if(!_Cg._){var _Ch=_Cg.a;return new T2(0,new T1(0,B(_xk(_Cf,_Ch))),new T1(0,B(_xQ(_Cf,_Ch))));}else{_Cc=new T1(1,I_fromInt(_Cf));_Cd=_Cg;continue;}}}else{var _Ci=E(_Cd);if(!_Ci._){_Cc=_Ce;_Cd=new T1(1,I_fromInt(_Ci.a));continue;}else{var _Cj=I_divMod(_Ce.a,_Ci.a);return new T2(0,new T1(1,_Cj.a),new T1(1,_Cj.b));}}}},_Ck=function(_Cl,_Cm){if(!B(_3f(_Cm,_zN))){var _Cn=B(_Cb(_Cl,_Cm));return new T2(0,_Cn.a,_Cn.b);}else{return E(_3a);}},_Co=function(_Cp,_Cq){while(1){var _Cr=E(_Cp);if(!_Cr._){var _Cs=E(_Cr.a);if(_Cs==(-2147483648)){_Cp=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ct=E(_Cq);if(!_Ct._){return new T1(0,B(_xQ(_Cs,_Ct.a)));}else{_Cp=new T1(1,I_fromInt(_Cs));_Cq=_Ct;continue;}}}else{var _Cu=_Cr.a,_Cv=E(_Cq);return (_Cv._==0)?new T1(1,I_mod(_Cu,I_fromInt(_Cv.a))):new T1(1,I_mod(_Cu,_Cv.a));}}},_Cw=function(_Cx,_Cy){if(!B(_3f(_Cy,_zN))){return new F(function(){return _Co(_Cx,_Cy);});}else{return E(_3a);}},_Cz=function(_CA,_CB){while(1){var _CC=E(_CA);if(!_CC._){var _CD=E(_CC.a);if(_CD==(-2147483648)){_CA=new T1(1,I_fromInt(-2147483648));continue;}else{var _CE=E(_CB);if(!_CE._){return new T1(0,quot(_CD,_CE.a));}else{_CA=new T1(1,I_fromInt(_CD));_CB=_CE;continue;}}}else{var _CF=_CC.a,_CG=E(_CB);return (_CG._==0)?new T1(0,I_toInt(I_quot(_CF,I_fromInt(_CG.a)))):new T1(1,I_quot(_CF,_CG.a));}}},_CH=function(_CI,_CJ){if(!B(_3f(_CJ,_zN))){return new F(function(){return _Cz(_CI,_CJ);});}else{return E(_3a);}},_CK=function(_CL,_CM){if(!B(_3f(_CM,_zN))){var _CN=B(_3z(_CL,_CM));return new T2(0,_CN.a,_CN.b);}else{return E(_3a);}},_CO=function(_CP,_CQ){while(1){var _CR=E(_CP);if(!_CR._){var _CS=E(_CR.a);if(_CS==(-2147483648)){_CP=new T1(1,I_fromInt(-2147483648));continue;}else{var _CT=E(_CQ);if(!_CT._){return new T1(0,_CS%_CT.a);}else{_CP=new T1(1,I_fromInt(_CS));_CQ=_CT;continue;}}}else{var _CU=_CR.a,_CV=E(_CQ);return (_CV._==0)?new T1(1,I_rem(_CU,I_fromInt(_CV.a))):new T1(1,I_rem(_CU,_CV.a));}}},_CW=function(_CX,_CY){if(!B(_3f(_CY,_zN))){return new F(function(){return _CO(_CX,_CY);});}else{return E(_3a);}},_CZ=function(_D0){return E(_D0);},_D1=function(_D2){return E(_D2);},_D3=function(_D4){var _D5=E(_D4);if(!_D5._){var _D6=E(_D5.a);return (_D6==(-2147483648))?E(_6p):(_D6<0)?new T1(0, -_D6):E(_D5);}else{var _D7=_D5.a;return (I_compareInt(_D7,0)>=0)?E(_D5):new T1(1,I_negate(_D7));}},_D8=new T1(0,0),_D9=new T1(0,-1),_Da=function(_Db){var _Dc=E(_Db);if(!_Dc._){var _Dd=_Dc.a;return (_Dd>=0)?(E(_Dd)==0)?E(_D8):E(_41):E(_D9);}else{var _De=I_compareInt(_Dc.a,0);return (_De<=0)?(E(_De)==0)?E(_D8):E(_D9):E(_41);}},_Df={_:0,a:_3q,b:_5L,c:_zn,d:_6q,e:_D3,f:_Da,g:_D1},_Dg=function(_Dh,_Di){var _Dj=E(_Dh);if(!_Dj._){var _Dk=_Dj.a,_Dl=E(_Di);return (_Dl._==0)?_Dk!=_Dl.a:(I_compareInt(_Dl.a,_Dk)==0)?false:true;}else{var _Dm=_Dj.a,_Dn=E(_Di);return (_Dn._==0)?(I_compareInt(_Dm,_Dn.a)==0)?false:true:(I_compare(_Dm,_Dn.a)==0)?false:true;}},_Do=new T2(0,_3f,_Dg),_Dp=function(_Dq,_Dr){return (!B(_5w(_Dq,_Dr)))?E(_Dq):E(_Dr);},_Ds=function(_Dt,_Du){return (!B(_5w(_Dt,_Du)))?E(_Du):E(_Dt);},_Dv={_:0,a:_Do,b:_22,c:_42,d:_5w,e:_3T,f:_Bu,g:_Dp,h:_Ds},_Dw=function(_Dx){return new T2(0,E(_Dx),E(_rf));},_Dy=new T3(0,_Df,_Dv,_Dw),_Dz={_:0,a:_Dy,b:_BZ,c:_CH,d:_CW,e:_C8,f:_Cw,g:_CK,h:_Ck,i:_CZ},_DA=function(_DB){return E(E(_DB).b);},_DC=function(_DD){return E(E(_DD).g);},_DE=new T1(0,1),_DF=function(_DG,_DH,_DI){var _DJ=B(_DA(_DG)),_DK=B(_8J(_DJ)),_DL=new T(function(){var _DM=new T(function(){var _DN=new T(function(){var _DO=new T(function(){return B(A3(_DC,_DG,_Dz,new T(function(){return B(A3(_8P,_DJ,_DH,_DI));})));});return B(A2(_8s,_DK,_DO));}),_DP=new T(function(){return B(A2(_6Z,_DK,new T(function(){return B(A2(_8s,_DK,_DE));})));});return B(A3(_8L,_DK,_DP,_DN));});return B(A3(_8L,_DK,_DM,_DI));});return new F(function(){return A3(_6X,_DK,_DH,_DL);});},_DQ=1.5707963267948966,_DR=function(_DS){return 0.2/Math.cos(B(_DF(_Bf,_DS,_DQ))-0.7853981633974483);},_DT=new T(function(){var _DU=B(_u0(_DR,1.2,_vk,_vk,_vj,_vk,_vk,_vk,_vk,_vk,_vj,_vj,_vj));return {_:0,a:E(_DU.a),b:E(_DU.b),c:E(_DU.c),d:E(_DU.d),e:E(_DU.e),f:E(_DU.f),g:E(_DU.g),h:_DU.h,i:_DU.i};}),_DV=0,_DW=0.3,_DX=function(_DY){return E(_DW);},_DZ=new T(function(){var _E0=B(_u0(_DX,1.2,_vj,_vk,_vj,_vk,_vk,_vk,_vk,_vk,_vj,_vj,_vj));return {_:0,a:E(_E0.a),b:E(_E0.b),c:E(_E0.c),d:E(_E0.d),e:E(_E0.e),f:E(_E0.f),g:E(_E0.g),h:_E0.h,i:_E0.i};}),_E1=new T(function(){var _E2=B(_u0(_DX,1.2,_vj,_vj,_vk,_vk,_vk,_vk,_vk,_vk,_vj,_vj,_vj));return {_:0,a:E(_E2.a),b:E(_E2.b),c:E(_E2.c),d:E(_E2.d),e:E(_E2.e),f:E(_E2.f),g:E(_E2.g),h:_E2.h,i:_E2.i};}),_E3=2,_E4=function(_E5){return 0.3/Math.cos(B(_DF(_Bf,_E5,_DQ))-0.7853981633974483);},_E6=new T(function(){var _E7=B(_u0(_E4,1.2,_E3,_vj,_vj,_vk,_vk,_vk,_vk,_vk,_vj,_vj,_vj));return {_:0,a:E(_E7.a),b:E(_E7.b),c:E(_E7.c),d:E(_E7.d),e:E(_E7.e),f:E(_E7.f),g:E(_E7.g),h:_E7.h,i:_E7.i};}),_E8=0.5,_E9=new T(function(){var _Ea=B(_u0(_DX,1.2,_vk,_vj,_E8,_vk,_vk,_vk,_vk,_vk,_vj,_vj,_vj));return {_:0,a:E(_Ea.a),b:E(_Ea.b),c:E(_Ea.c),d:E(_Ea.d),e:E(_Ea.e),f:E(_Ea.f),g:E(_Ea.g),h:_Ea.h,i:_Ea.i};}),_Eb=new T2(1,_E9,_w),_Ec=new T2(1,_E6,_Eb),_Ed=new T2(1,_E1,_Ec),_Ee=new T2(1,_DZ,_Ed),_Ef=new T2(1,_DT,_Ee),_Eg=new T(function(){return B(unCStr("Negative range size"));}),_Eh=new T(function(){return B(err(_Eg));}),_Ei=function(_){var _Ej=B(_lW(_Ef,0))-1|0,_Ek=function(_El){if(_El>=0){var _Em=newArr(_El,_m2),_En=_Em,_Eo=E(_El);if(!_Eo){return new T4(0,E(_DV),E(_Ej),0,_En);}else{var _Ep=function(_Eq,_Er,_){while(1){var _Es=E(_Eq);if(!_Es._){return E(_);}else{var _=_En[_Er]=_Es.a;if(_Er!=(_Eo-1|0)){var _Et=_Er+1|0;_Eq=_Es.b;_Er=_Et;continue;}else{return E(_);}}}},_=B((function(_Eu,_Ev,_Ew,_){var _=_En[_Ew]=_Eu;if(_Ew!=(_Eo-1|0)){return new F(function(){return _Ep(_Ev,_Ew+1|0,_);});}else{return E(_);}})(_DT,_Ee,0,_));return new T4(0,E(_DV),E(_Ej),_Eo,_En);}}else{return E(_Eh);}};if(0>_Ej){return new F(function(){return _Ek(0);});}else{return new F(function(){return _Ek(_Ej+1|0);});}},_Ex=function(_Ey){var _Ez=B(A1(_Ey,_));return E(_Ez);},_EA=new T(function(){return B(_Ex(_Ei));}),_EB="outline",_EC="polygon",_ED=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_EE=new T(function(){return B(err(_ED));}),_EF=new T(function(){return eval("__strict(drawObjects)");}),_EG=new T(function(){return eval("__strict(draw)");}),_EH=function(_EI,_EJ){var _EK=jsShowI(_EI);return new F(function(){return _n(fromJSStr(_EK),_EJ);});},_EL=function(_EM,_EN,_EO){if(_EN>=0){return new F(function(){return _EH(_EN,_EO);});}else{if(_EM<=6){return new F(function(){return _EH(_EN,_EO);});}else{return new T2(1,_7g,new T(function(){var _EP=jsShowI(_EN);return B(_n(fromJSStr(_EP),new T2(1,_7f,_EO)));}));}}},_EQ=new T(function(){return B(unCStr(")"));}),_ER=function(_ES,_ET){var _EU=new T(function(){var _EV=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EL(0,_ES,_w)),_EQ));})));},1);return B(_n(B(_EL(0,_ET,_w)),_EV));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_EU)));});},_EW=new T2(1,_oj,_w),_EX=function(_EY){return E(_EY);},_EZ=function(_F0){return E(_F0);},_F1=function(_F2,_F3){return E(_F3);},_F4=function(_F5,_F6){return E(_F5);},_F7=function(_F8){return E(_F8);},_F9=new T2(0,_F7,_F4),_Fa=function(_Fb,_Fc){return E(_Fb);},_Fd=new T5(0,_F9,_EZ,_EX,_F1,_Fa),_Fe="flipped2",_Ff="flipped1",_Fg="c1y",_Fh="c1x",_Fi="w2z",_Fj="w2y",_Fk="w2x",_Fl="w1z",_Fm="w1y",_Fn="w1x",_Fo="d2z",_Fp="d2y",_Fq="d2x",_Fr="d1z",_Fs="d1y",_Ft="d1x",_Fu="c2y",_Fv="c2x",_Fw=function(_Fx,_){var _Fy=__get(_Fx,E(_Fn)),_Fz=__get(_Fx,E(_Fm)),_FA=__get(_Fx,E(_Fl)),_FB=__get(_Fx,E(_Fk)),_FC=__get(_Fx,E(_Fj)),_FD=__get(_Fx,E(_Fi)),_FE=__get(_Fx,E(_Fh)),_FF=__get(_Fx,E(_Fg)),_FG=__get(_Fx,E(_Fv)),_FH=__get(_Fx,E(_Fu)),_FI=__get(_Fx,E(_Ft)),_FJ=__get(_Fx,E(_Fs)),_FK=__get(_Fx,E(_Fr)),_FL=__get(_Fx,E(_Fq)),_FM=__get(_Fx,E(_Fp)),_FN=__get(_Fx,E(_Fo)),_FO=__get(_Fx,E(_Ff)),_FP=__get(_Fx,E(_Fe));return {_:0,a:E(new T3(0,E(_Fy),E(_Fz),E(_FA))),b:E(new T3(0,E(_FB),E(_FC),E(_FD))),c:E(new T2(0,E(_FE),E(_FF))),d:E(new T2(0,E(_FG),E(_FH))),e:E(new T3(0,E(_FI),E(_FJ),E(_FK))),f:E(new T3(0,E(_FL),E(_FM),E(_FN))),g:E(_FO),h:E(_FP)};},_FQ=function(_FR,_){var _FS=E(_FR);if(!_FS._){return _w;}else{var _FT=B(_Fw(E(_FS.a),_)),_FU=B(_FQ(_FS.b,_));return new T2(1,_FT,_FU);}},_FV=function(_FW){var _FX=E(_FW);return (E(_FX.b)-E(_FX.a)|0)+1|0;},_FY=function(_FZ,_G0){var _G1=E(_FZ),_G2=E(_G0);return (E(_G1.a)>_G2)?false:_G2<=E(_G1.b);},_G3=function(_G4){return new F(function(){return _EL(0,E(_G4),_w);});},_G5=function(_G6,_G7,_G8){return new F(function(){return _EL(E(_G6),E(_G7),_G8);});},_G9=function(_Ga,_Gb){return new F(function(){return _EL(0,E(_Ga),_Gb);});},_Gc=function(_Gd,_Ge){return new F(function(){return _2Q(_G9,_Gd,_Ge);});},_Gf=new T3(0,_G5,_G3,_Gc),_Gg=0,_Gh=function(_Gi,_Gj,_Gk){return new F(function(){return A1(_Gi,new T2(1,_2N,new T(function(){return B(A1(_Gj,_Gk));})));});},_Gl=new T(function(){return B(unCStr("foldr1"));}),_Gm=new T(function(){return B(_qF(_Gl));}),_Gn=function(_Go,_Gp){var _Gq=E(_Gp);if(!_Gq._){return E(_Gm);}else{var _Gr=_Gq.a,_Gs=E(_Gq.b);if(!_Gs._){return E(_Gr);}else{return new F(function(){return A2(_Go,_Gr,new T(function(){return B(_Gn(_Go,_Gs));}));});}}},_Gt=new T(function(){return B(unCStr(" out of range "));}),_Gu=new T(function(){return B(unCStr("}.index: Index "));}),_Gv=new T(function(){return B(unCStr("Ix{"));}),_Gw=new T2(1,_7f,_w),_Gx=new T2(1,_7f,_Gw),_Gy=0,_Gz=function(_GA){return E(E(_GA).a);},_GB=function(_GC,_GD,_GE,_GF,_GG){var _GH=new T(function(){var _GI=new T(function(){var _GJ=new T(function(){var _GK=new T(function(){var _GL=new T(function(){return B(A3(_Gn,_Gh,new T2(1,new T(function(){return B(A3(_Gz,_GE,_Gy,_GF));}),new T2(1,new T(function(){return B(A3(_Gz,_GE,_Gy,_GG));}),_w)),_Gx));});return B(_n(_Gt,new T2(1,_7g,new T2(1,_7g,_GL))));});return B(A(_Gz,[_GE,_Gg,_GD,new T2(1,_7f,_GK)]));});return B(_n(_Gu,new T2(1,_7g,_GJ)));},1);return B(_n(_GC,_GI));},1);return new F(function(){return err(B(_n(_Gv,_GH)));});},_GM=function(_GN,_GO,_GP,_GQ,_GR){return new F(function(){return _GB(_GN,_GO,_GR,_GP,_GQ);});},_GS=function(_GT,_GU,_GV,_GW){var _GX=E(_GV);return new F(function(){return _GM(_GT,_GU,_GX.a,_GX.b,_GW);});},_GY=function(_GZ,_H0,_H1,_H2){return new F(function(){return _GS(_H2,_H1,_H0,_GZ);});},_H3=new T(function(){return B(unCStr("Int"));}),_H4=function(_H5,_H6){return new F(function(){return _GY(_Gf,_H6,_H5,_H3);});},_H7=function(_H8,_H9){var _Ha=E(_H8),_Hb=E(_Ha.a),_Hc=E(_H9);if(_Hb>_Hc){return new F(function(){return _H4(_Hc,_Ha);});}else{if(_Hc>E(_Ha.b)){return new F(function(){return _H4(_Hc,_Ha);});}else{return _Hc-_Hb|0;}}},_Hd=function(_He){var _Hf=E(_He);return new F(function(){return _x4(_Hf.a,_Hf.b);});},_Hg=function(_Hh){var _Hi=E(_Hh),_Hj=E(_Hi.a),_Hk=E(_Hi.b);return (_Hj>_Hk)?E(_Gg):(_Hk-_Hj|0)+1|0;},_Hl=function(_Hm,_Hn){return new F(function(){return _yt(_Hn,E(_Hm).a);});},_Ho={_:0,a:_zj,b:_Hd,c:_H7,d:_Hl,e:_FY,f:_Hg,g:_FV},_Hp=function(_Hq,_Hr,_){while(1){var _Hs=B((function(_Ht,_Hu,_){var _Hv=E(_Ht);if(!_Hv._){return new T2(0,_oj,_Hu);}else{var _Hw=B(A2(_Hv.a,_Hu,_));_Hq=_Hv.b;_Hr=new T(function(){return E(E(_Hw).b);});return __continue;}})(_Hq,_Hr,_));if(_Hs!=__continue){return _Hs;}}},_Hx=function(_Hy,_Hz){return new T2(1,_Hy,_Hz);},_HA=function(_HB,_HC){var _HD=E(_HC);return new T2(0,_HD.a,_HD.b);},_HE=function(_HF){return E(E(_HF).f);},_HG=function(_HH,_HI,_HJ){var _HK=E(_HI),_HL=_HK.a,_HM=_HK.b,_HN=function(_){var _HO=B(A2(_HE,_HH,_HK));if(_HO>=0){var _HP=newArr(_HO,_m2),_HQ=_HP,_HR=E(_HO);if(!_HR){return new T(function(){return new T4(0,E(_HL),E(_HM),0,_HQ);});}else{var _HS=function(_HT,_HU,_){while(1){var _HV=E(_HT);if(!_HV._){return E(_);}else{var _=_HQ[_HU]=_HV.a;if(_HU!=(_HR-1|0)){var _HW=_HU+1|0;_HT=_HV.b;_HU=_HW;continue;}else{return E(_);}}}},_=B(_HS(_HJ,0,_));return new T(function(){return new T4(0,E(_HL),E(_HM),_HR,_HQ);});}}else{return E(_Eh);}};return new F(function(){return _Ex(_HN);});},_HX=function(_HY,_HZ,_I0,_I1){var _I2=new T(function(){var _I3=E(_I1),_I4=_I3.c-1|0,_I5=new T(function(){return B(A2(_cF,_HZ,_w));});if(0<=_I4){var _I6=new T(function(){return B(_8F(_HZ));}),_I7=function(_I8){var _I9=new T(function(){var _Ia=new T(function(){return B(A1(_I0,new T(function(){return E(_I3.d[_I8]);})));});return B(A3(_8T,_I6,_Hx,_Ia));});return new F(function(){return A3(_8R,_HZ,_I9,new T(function(){if(_I8!=_I4){return B(_I7(_I8+1|0));}else{return E(_I5);}}));});};return B(_I7(0));}else{return E(_I5);}}),_Ib=new T(function(){return B(_HA(_HY,_I1));});return new F(function(){return A3(_8T,B(_8F(_HZ)),function(_Ic){return new F(function(){return _HG(_HY,_Ib,_Ic);});},_I2);});},_Id=function(_Ie,_If,_Ig,_Ih,_Ii,_Ij,_Ik,_Il,_Im){var _In=B(_8L(_Ie));return new T2(0,new T3(0,E(B(A1(B(A1(_In,_If)),_Ij))),E(B(A1(B(A1(_In,_Ig)),_Ik))),E(B(A1(B(A1(_In,_Ih)),_Il)))),B(A1(B(A1(_In,_Ii)),_Im)));},_Io=function(_Ip,_Iq,_Ir,_Is,_It,_Iu,_Iv,_Iw,_Ix){var _Iy=B(_6X(_Ip));return new T2(0,new T3(0,E(B(A1(B(A1(_Iy,_Iq)),_Iu))),E(B(A1(B(A1(_Iy,_Ir)),_Iv))),E(B(A1(B(A1(_Iy,_Is)),_Iw)))),B(A1(B(A1(_Iy,_It)),_Ix)));},_Iz=1.0e-2,_IA=function(_IB,_IC,_ID,_IE,_IF,_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN,_IO,_IP,_IQ,_IR){var _IS=B(_Id(_n2,_II,_IJ,_IK,_IL,_Iz,_Iz,_Iz,_Iz)),_IT=E(_IS.a),_IU=B(_Io(_n2,_IE,_IF,_IG,_IH,_IT.a,_IT.b,_IT.c,_IS.b)),_IV=E(_IU.a);return new F(function(){return _tg(_IB,_IC,_ID,_IV.a,_IV.b,_IV.c,_IU.b,_II,_IJ,_IK,_IL,_IM,_IN,_IO,_IP,_IQ,_IR);});},_IW=function(_IX){var _IY=E(_IX),_IZ=E(_IY.d),_J0=E(_IZ.a),_J1=E(_IY.e),_J2=E(_J1.a),_J3=E(_IY.f),_J4=B(_IA(_IY.a,_IY.b,_IY.c,_J0.a,_J0.b,_J0.c,_IZ.b,_J2.a,_J2.b,_J2.c,_J1.b,_J3.a,_J3.b,_J3.c,_IY.g,_IY.h,_IY.i));return {_:0,a:E(_J4.a),b:E(_J4.b),c:E(_J4.c),d:E(_J4.d),e:E(_J4.e),f:E(_J4.f),g:E(_J4.g),h:_J4.h,i:_J4.i};},_J5=function(_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd,_Je){var _Jf=B(_8J(B(_8H(_J6))));return new F(function(){return A3(_6X,_Jf,new T(function(){return B(_oX(_J6,_J7,_J8,_J9,_Jb,_Jc,_Jd));}),new T(function(){return B(A3(_8L,_Jf,_Ja,_Je));}));});},_Jg=new T(function(){return B(unCStr("base"));}),_Jh=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Ji=new T(function(){return B(unCStr("IOException"));}),_Jj=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Jg,_Jh,_Ji),_Jk=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Jj,_w,_w),_Jl=function(_Jm){return E(_Jk);},_Jn=function(_Jo){var _Jp=E(_Jo);return new F(function(){return _2n(B(_2l(_Jp.a)),_Jl,_Jp.b);});},_Jq=new T(function(){return B(unCStr(": "));}),_Jr=new T(function(){return B(unCStr(")"));}),_Js=new T(function(){return B(unCStr(" ("));}),_Jt=new T(function(){return B(unCStr("interrupted"));}),_Ju=new T(function(){return B(unCStr("system error"));}),_Jv=new T(function(){return B(unCStr("unsatisified constraints"));}),_Jw=new T(function(){return B(unCStr("user error"));}),_Jx=new T(function(){return B(unCStr("permission denied"));}),_Jy=new T(function(){return B(unCStr("illegal operation"));}),_Jz=new T(function(){return B(unCStr("end of file"));}),_JA=new T(function(){return B(unCStr("resource exhausted"));}),_JB=new T(function(){return B(unCStr("resource busy"));}),_JC=new T(function(){return B(unCStr("does not exist"));}),_JD=new T(function(){return B(unCStr("already exists"));}),_JE=new T(function(){return B(unCStr("resource vanished"));}),_JF=new T(function(){return B(unCStr("timeout"));}),_JG=new T(function(){return B(unCStr("unsupported operation"));}),_JH=new T(function(){return B(unCStr("hardware fault"));}),_JI=new T(function(){return B(unCStr("inappropriate type"));}),_JJ=new T(function(){return B(unCStr("invalid argument"));}),_JK=new T(function(){return B(unCStr("failed"));}),_JL=new T(function(){return B(unCStr("protocol error"));}),_JM=function(_JN,_JO){switch(E(_JN)){case 0:return new F(function(){return _n(_JD,_JO);});break;case 1:return new F(function(){return _n(_JC,_JO);});break;case 2:return new F(function(){return _n(_JB,_JO);});break;case 3:return new F(function(){return _n(_JA,_JO);});break;case 4:return new F(function(){return _n(_Jz,_JO);});break;case 5:return new F(function(){return _n(_Jy,_JO);});break;case 6:return new F(function(){return _n(_Jx,_JO);});break;case 7:return new F(function(){return _n(_Jw,_JO);});break;case 8:return new F(function(){return _n(_Jv,_JO);});break;case 9:return new F(function(){return _n(_Ju,_JO);});break;case 10:return new F(function(){return _n(_JL,_JO);});break;case 11:return new F(function(){return _n(_JK,_JO);});break;case 12:return new F(function(){return _n(_JJ,_JO);});break;case 13:return new F(function(){return _n(_JI,_JO);});break;case 14:return new F(function(){return _n(_JH,_JO);});break;case 15:return new F(function(){return _n(_JG,_JO);});break;case 16:return new F(function(){return _n(_JF,_JO);});break;case 17:return new F(function(){return _n(_JE,_JO);});break;default:return new F(function(){return _n(_Jt,_JO);});}},_JP=new T(function(){return B(unCStr("}"));}),_JQ=new T(function(){return B(unCStr("{handle: "));}),_JR=function(_JS,_JT,_JU,_JV,_JW,_JX){var _JY=new T(function(){var _JZ=new T(function(){var _K0=new T(function(){var _K1=E(_JV);if(!_K1._){return E(_JX);}else{var _K2=new T(function(){return B(_n(_K1,new T(function(){return B(_n(_Jr,_JX));},1)));},1);return B(_n(_Js,_K2));}},1);return B(_JM(_JT,_K0));}),_K3=E(_JU);if(!_K3._){return E(_JZ);}else{return B(_n(_K3,new T(function(){return B(_n(_Jq,_JZ));},1)));}}),_K4=E(_JW);if(!_K4._){var _K5=E(_JS);if(!_K5._){return E(_JY);}else{var _K6=E(_K5.a);if(!_K6._){var _K7=new T(function(){var _K8=new T(function(){return B(_n(_JP,new T(function(){return B(_n(_Jq,_JY));},1)));},1);return B(_n(_K6.a,_K8));},1);return new F(function(){return _n(_JQ,_K7);});}else{var _K9=new T(function(){var _Ka=new T(function(){return B(_n(_JP,new T(function(){return B(_n(_Jq,_JY));},1)));},1);return B(_n(_K6.a,_Ka));},1);return new F(function(){return _n(_JQ,_K9);});}}}else{return new F(function(){return _n(_K4.a,new T(function(){return B(_n(_Jq,_JY));},1));});}},_Kb=function(_Kc){var _Kd=E(_Kc);return new F(function(){return _JR(_Kd.a,_Kd.b,_Kd.c,_Kd.d,_Kd.f,_w);});},_Ke=function(_Kf,_Kg,_Kh){var _Ki=E(_Kg);return new F(function(){return _JR(_Ki.a,_Ki.b,_Ki.c,_Ki.d,_Ki.f,_Kh);});},_Kj=function(_Kk,_Kl){var _Km=E(_Kk);return new F(function(){return _JR(_Km.a,_Km.b,_Km.c,_Km.d,_Km.f,_Kl);});},_Kn=function(_Ko,_Kp){return new F(function(){return _2Q(_Kj,_Ko,_Kp);});},_Kq=new T3(0,_Ke,_Kb,_Kn),_Kr=new T(function(){return new T5(0,_Jl,_Kq,_Ks,_Jn,_Kb);}),_Ks=function(_Kt){return new T2(0,_Kr,_Kt);},_Ku=__Z,_Kv=7,_Kw=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_Kx=new T6(0,_Ku,_Kv,_w,_Kw,_Ku,_Ku),_Ky=new T(function(){return B(_Ks(_Kx));}),_Kz=function(_){return new F(function(){return die(_Ky);});},_KA=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_KB=new T6(0,_Ku,_Kv,_w,_KA,_Ku,_Ku),_KC=new T(function(){return B(_Ks(_KB));}),_KD=function(_){return new F(function(){return die(_KC);});},_KE=function(_KF,_){return new T2(0,_w,_KF);},_KG=0.6,_KH=1,_KI=new T(function(){return B(unCStr(")"));}),_KJ=function(_KK,_KL){var _KM=new T(function(){var _KN=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EL(0,_KK,_w)),_KI));})));},1);return B(_n(B(_EL(0,_KL,_w)),_KN));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_KM)));});},_KO=function(_KP,_KQ){var _KR=new T(function(){var _KS=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EL(0,_KQ,_w)),_KI));})));},1);return B(_n(B(_EL(0,_KP,_w)),_KS));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_KR)));});},_KT=function(_KU){var _KV=E(_KU);if(!_KV._){return E(_KE);}else{var _KW=new T(function(){return B(_KT(_KV.b));}),_KX=function(_KY){var _KZ=E(_KY);if(!_KZ._){return E(_KW);}else{var _L0=_KZ.a,_L1=new T(function(){return B(_KX(_KZ.b));}),_L2=new T(function(){return 0.1*E(E(_L0).e)/1.0e-2;}),_L3=new T(function(){var _L4=E(_L0);if(_L4.a!=_L4.b){return E(_KH);}else{return E(_KG);}}),_L5=function(_L6,_){var _L7=E(_L6),_L8=_L7.c,_L9=_L7.d,_La=E(_L7.a),_Lb=E(_L7.b),_Lc=E(_L0),_Ld=_Lc.a,_Le=_Lc.b,_Lf=E(_Lc.c),_Lg=_Lf.b,_Lh=E(_Lf.a),_Li=_Lh.a,_Lj=_Lh.b,_Lk=_Lh.c,_Ll=E(_Lc.d),_Lm=_Ll.b,_Ln=E(_Ll.a),_Lo=_Ln.a,_Lp=_Ln.b,_Lq=_Ln.c;if(_La>_Ld){return new F(function(){return _KD(_);});}else{if(_Ld>_Lb){return new F(function(){return _KD(_);});}else{if(_La>_Le){return new F(function(){return _Kz(_);});}else{if(_Le>_Lb){return new F(function(){return _Kz(_);});}else{var _Lr=_Ld-_La|0;if(0>_Lr){return new F(function(){return _KJ(_L8,_Lr);});}else{if(_Lr>=_L8){return new F(function(){return _KJ(_L8,_Lr);});}else{var _Ls=E(_L9[_Lr]),_Lt=E(_Ls.c),_Lu=_Lt.b,_Lv=E(_Lt.a),_Lw=_Lv.a,_Lx=_Lv.b,_Ly=_Lv.c,_Lz=E(_Ls.e),_LA=E(_Lz.a),_LB=B(_Id(_n2,_Li,_Lj,_Lk,_Lg,_Lw,_Lx,_Ly,_Lu)),_LC=E(_LB.a),_LD=B(_Id(_n2,_LC.a,_LC.b,_LC.c,_LB.b,_Li,_Lj,_Lk,_Lg)),_LE=E(_LD.a),_LF=_Le-_La|0;if(0>_LF){return new F(function(){return _KO(_LF,_L8);});}else{if(_LF>=_L8){return new F(function(){return _KO(_LF,_L8);});}else{var _LG=E(_L9[_LF]),_LH=E(_LG.c),_LI=_LH.b,_LJ=E(_LH.a),_LK=_LJ.a,_LL=_LJ.b,_LM=_LJ.c,_LN=E(_LG.e),_LO=E(_LN.a),_LP=B(_Id(_n2,_Lo,_Lp,_Lq,_Lm,_LK,_LL,_LM,_LI)),_LQ=E(_LP.a),_LR=B(_Id(_n2,_LQ.a,_LQ.b,_LQ.c,_LP.b,_Lo,_Lp,_Lq,_Lm)),_LS=E(_LR.a),_LT=E(_LE.a)+E(_LE.b)+E(_LE.c)+E(_LD.b)+E(_LS.a)+E(_LS.b)+E(_LS.c)+E(_LR.b);if(!_LT){var _LU=B(A2(_L1,_L7,_));return new T2(0,new T2(1,_oj,new T(function(){return E(E(_LU).a);})),new T(function(){return E(E(_LU).b);}));}else{var _LV=new T(function(){return  -((B(_J5(_ny,_LA.a,_LA.b,_LA.c,_Lz.b,_Li,_Lj,_Lk,_Lg))-B(_J5(_ny,_LO.a,_LO.b,_LO.c,_LN.b,_Lo,_Lp,_Lq,_Lm))-E(_L2))/_LT);}),_LW=function(_LX,_LY,_LZ,_M0,_){var _M1=new T(function(){var _M2=function(_M3,_M4,_M5,_M6,_M7){if(_M3>_Le){return E(_M7);}else{if(_Le>_M4){return E(_M7);}else{var _M8=function(_){var _M9=newArr(_M5,_m2),_Ma=_M9,_Mb=function(_Mc,_){while(1){if(_Mc!=_M5){var _=_Ma[_Mc]=_M6[_Mc],_Md=_Mc+1|0;_Mc=_Md;continue;}else{return E(_);}}},_=B(_Mb(0,_)),_Me=_Le-_M3|0;if(0>_Me){return new F(function(){return _KO(_Me,_M5);});}else{if(_Me>=_M5){return new F(function(){return _KO(_Me,_M5);});}else{var _=_Ma[_Me]=new T(function(){var _Mf=E(_M6[_Me]),_Mg=E(_Mf.e),_Mh=E(_Mg.a),_Mi=B(_Id(_n2,_LK,_LL,_LM,_LI,_Lo,_Lp,_Lq,_Lm)),_Mj=E(_Mi.a),_Mk=E(_LV)*E(_L3),_Ml=B(_Id(_n2,_Mj.a,_Mj.b,_Mj.c,_Mi.b,_Mk,_Mk,_Mk,_Mk)),_Mm=E(_Ml.a),_Mn=B(_Io(_n2,_Mh.a,_Mh.b,_Mh.c,_Mg.b, -E(_Mm.a), -E(_Mm.b), -E(_Mm.c), -E(_Ml.b)));return {_:0,a:E(_Mf.a),b:E(_Mf.b),c:E(_Mf.c),d:E(_Mf.d),e:E(new T2(0,E(_Mn.a),E(_Mn.b))),f:E(_Mf.f),g:E(_Mf.g),h:_Mf.h,i:_Mf.i};});return new T4(0,E(_M3),E(_M4),_M5,_Ma);}}};return new F(function(){return _Ex(_M8);});}}};if(_LX>_Ld){return B(_M2(_LX,_LY,_LZ,_M0,new T4(0,E(_LX),E(_LY),_LZ,_M0)));}else{if(_Ld>_LY){return B(_M2(_LX,_LY,_LZ,_M0,new T4(0,E(_LX),E(_LY),_LZ,_M0)));}else{var _Mo=function(_){var _Mp=newArr(_LZ,_m2),_Mq=_Mp,_Mr=function(_Ms,_){while(1){if(_Ms!=_LZ){var _=_Mq[_Ms]=_M0[_Ms],_Mt=_Ms+1|0;_Ms=_Mt;continue;}else{return E(_);}}},_=B(_Mr(0,_)),_Mu=_Ld-_LX|0;if(0>_Mu){return new F(function(){return _KJ(_LZ,_Mu);});}else{if(_Mu>=_LZ){return new F(function(){return _KJ(_LZ,_Mu);});}else{var _=_Mq[_Mu]=new T(function(){var _Mv=E(_M0[_Mu]),_Mw=E(_Mv.e),_Mx=E(_Mw.a),_My=B(_Id(_n2,_Lw,_Lx,_Ly,_Lu,_Li,_Lj,_Lk,_Lg)),_Mz=E(_My.a),_MA=E(_LV)*E(_L3),_MB=B(_Id(_n2,_Mz.a,_Mz.b,_Mz.c,_My.b,_MA,_MA,_MA,_MA)),_MC=E(_MB.a),_MD=B(_Io(_n2,_Mx.a,_Mx.b,_Mx.c,_Mw.b,_MC.a,_MC.b,_MC.c,_MB.b));return {_:0,a:E(_Mv.a),b:E(_Mv.b),c:E(_Mv.c),d:E(_Mv.d),e:E(new T2(0,E(_MD.a),E(_MD.b))),f:E(_Mv.f),g:E(_Mv.g),h:_Mv.h,i:_Mv.i};});return new T4(0,E(_LX),E(_LY),_LZ,_Mq);}}},_ME=B(_Ex(_Mo));return B(_M2(E(_ME.a),E(_ME.b),_ME.c,_ME.d,_ME));}}});return new T2(0,_oj,_M1);};if(!E(_Lc.f)){var _MF=B(_LW(_La,_Lb,_L8,_L9,_)),_MG=B(A2(_L1,new T(function(){return E(E(_MF).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MF).a);}),new T(function(){return E(E(_MG).a);})),new T(function(){return E(E(_MG).b);}));}else{if(E(_LV)<0){var _MH=B(A2(_L1,_L7,_));return new T2(0,new T2(1,_oj,new T(function(){return E(E(_MH).a);})),new T(function(){return E(E(_MH).b);}));}else{var _MI=B(_LW(_La,_Lb,_L8,_L9,_)),_MJ=B(A2(_L1,new T(function(){return E(E(_MI).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MI).a);}),new T(function(){return E(E(_MJ).a);})),new T(function(){return E(E(_MJ).b);}));}}}}}}}}}}}};return E(_L5);}};return new F(function(){return _KX(_KV.a);});}},_MK=function(_,_ML){var _MM=new T(function(){return B(_KT(E(_ML).a));}),_MN=function(_MO){var _MP=E(_MO);return (_MP==1)?E(new T2(1,_MM,_w)):new T2(1,_MM,new T(function(){return B(_MN(_MP-1|0));}));},_MQ=B(_Hp(B(_MN(5)),new T(function(){return E(E(_ML).b);}),_)),_MR=new T(function(){return B(_HX(_Ho,_Fd,_IW,new T(function(){return E(E(_MQ).b);})));});return new T2(0,_oj,_MR);},_MS=function(_MT,_MU,_MV,_MW,_MX){var _MY=B(_8J(B(_8H(_MT))));return new F(function(){return A3(_6X,_MY,new T(function(){return B(A3(_8L,_MY,_MU,_MW));}),new T(function(){return B(A3(_8L,_MY,_MV,_MX));}));});},_MZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_N0=new T6(0,_Ku,_Kv,_w,_MZ,_Ku,_Ku),_N1=new T(function(){return B(_Ks(_N0));}),_N2=function(_){return new F(function(){return die(_N1);});},_N3=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_N4=new T6(0,_Ku,_Kv,_w,_N3,_Ku,_Ku),_N5=new T(function(){return B(_Ks(_N4));}),_N6=function(_){return new F(function(){return die(_N5);});},_N7=function(_N8,_N9,_Na,_Nb){var _Nc=new T(function(){return B(_8J(new T(function(){return B(_8H(_N8));})));}),_Nd=B(A2(_8s,_Nc,_8q));return new F(function(){return _p7(_N8,_Nd,B(A2(_8s,_Nc,_8r)),_Nd);});},_Ne=false,_Nf=true,_Ng=function(_Nh){var _Ni=E(_Nh),_Nj=_Ni.b,_Nk=E(_Ni.d),_Nl=E(_Ni.e),_Nm=E(_Nl.a),_Nn=E(_Ni.g),_No=B(A1(_Nj,_Nk.a)),_Np=B(_pY(_ny,_No.a,_No.b,_No.c,_Nn.a,_Nn.b,_Nn.c));return {_:0,a:E(_Ni.a),b:E(_Nj),c:E(_Ni.c),d:E(_Nk),e:E(new T2(0,E(new T3(0,E(_Nm.a)+E(_Np.a)*1.0e-2,E(_Nm.b)+E(_Np.b)*1.0e-2,E(_Nm.c)+E(_Np.c)*1.0e-2)),E(_Nl.b))),f:E(_Ni.f),g:E(_Nn),h:_Ni.h,i:_Ni.i};},_Nq=new T(function(){return eval("__strict(collideBound)");}),_Nr=new T(function(){return eval("__strict(mouseContact)");}),_Ns=new T(function(){return eval("__strict(collide)");}),_Nt=function(_Nu){var _Nv=E(_Nu);if(!_Nv._){return __Z;}else{return new F(function(){return _n(_Nv.a,new T(function(){return B(_Nt(_Nv.b));},1));});}},_Nw=0,_Nx=new T3(0,E(_Nw),E(_Nw),E(_Nw)),_Ny=new T2(0,E(_Nx),E(_Nw)),_Nz=function(_NA,_){var _NB=B(_HX(_Ho,_Fd,_Ng,_NA)),_NC=E(_NB.a),_ND=E(_NB.b);if(_NC<=_ND){var _NE=function(_NF,_NG,_NH,_NI,_NJ,_){if(_NG>_NF){return new F(function(){return _N6(_);});}else{if(_NF>_NH){return new F(function(){return _N6(_);});}else{var _NK=new T(function(){var _NL=_NF-_NG|0;if(0>_NL){return B(_KO(_NL,_NI));}else{if(_NL>=_NI){return B(_KO(_NL,_NI));}else{return E(_NJ[_NL]);}}}),_NM=function(_NN,_NO,_NP,_NQ,_NR,_){var _NS=E(_NN);if(!_NS._){return new T2(0,_w,new T4(0,E(_NO),E(_NP),_NQ,_NR));}else{var _NT=E(_NS.a);if(_NO>_NT){return new F(function(){return _N2(_);});}else{if(_NT>_NP){return new F(function(){return _N2(_);});}else{var _NU=E(_NK),_NV=_NT-_NO|0;if(0>_NV){return new F(function(){return _KJ(_NQ,_NV);});}else{if(_NV>=_NQ){return new F(function(){return _KJ(_NQ,_NV);});}else{var _NW=E(_NR[_NV]),_NX=__app2(E(_Ns),B(_ok(new T2(1,new T2(0,_EC,_NU.h),new T2(1,new T2(0,_EB,_NU.i),_w)))),B(_ok(new T2(1,new T2(0,_EC,_NW.h),new T2(1,new T2(0,_EB,_NW.i),_w))))),_NY=__arr2lst(0,_NX),_NZ=B(_FQ(_NY,_)),_O0=B(_NM(_NS.b,_NO,_NP,_NQ,_NR,_)),_O1=new T(function(){var _O2=new T(function(){return _NF!=_NT;}),_O3=function(_O4){var _O5=E(_O4);if(!_O5._){return __Z;}else{var _O6=_O5.b,_O7=E(_O5.a),_O8=E(_O7.b),_O9=E(_O7.a),_Oa=E(_O9.a),_Ob=E(_O9.b),_Oc=E(_O9.c),_Od=E(_O8.a),_Oe=E(_O8.b),_Of=E(_O8.c),_Og=E(_O7.c),_Oh=_Og.a,_Oi=_Og.b,_Oj=E(_O7.e),_Ok=E(_O7.d),_Ol=_Ok.a,_Om=_Ok.b,_On=E(_O7.f),_Oo=new T(function(){var _Op=B(_p7(_ny,_On.a,_On.b,_On.c)),_Oq=Math.sqrt(B(_MS(_ny,_Ol,_Om,_Ol,_Om)));return new T3(0,_Oq*E(_Op.a),_Oq*E(_Op.b),_Oq*E(_Op.c));}),_Or=new T(function(){var _Os=B(_p7(_ny,_Oj.a,_Oj.b,_Oj.c)),_Ot=Math.sqrt(B(_MS(_ny,_Oh,_Oi,_Oh,_Oi)));return new T3(0,_Ot*E(_Os.a),_Ot*E(_Os.b),_Ot*E(_Os.c));}),_Ou=new T(function(){var _Ov=B(_N7(_ny,_Od,_Oe,_Of));return new T3(0,E(_Ov.a),E(_Ov.b),E(_Ov.c));}),_Ow=new T(function(){var _Ox=B(_N7(_ny,_Oa,_Ob,_Oc));return new T3(0,E(_Ox.a),E(_Ox.b),E(_Ox.c));}),_Oy=_Od+ -_Oa,_Oz=_Oe+ -_Ob,_OA=_Of+ -_Oc,_OB=new T(function(){return Math.sqrt(B(_oX(_ny,_Oy,_Oz,_OA,_Oy,_Oz,_OA)));}),_OC=new T(function(){var _OD=1/E(_OB);return new T3(0,_Oy*_OD,_Oz*_OD,_OA*_OD);}),_OE=new T(function(){if(!E(_O7.g)){return E(_OC);}else{var _OF=E(_OC);return new T3(0,-1*E(_OF.a),-1*E(_OF.b),-1*E(_OF.c));}}),_OG=new T(function(){if(!E(_O7.h)){return E(_OC);}else{var _OH=E(_OC);return new T3(0,-1*E(_OH.a),-1*E(_OH.b),-1*E(_OH.c));}});return (!E(_O2))?new T2(1,new T(function(){var _OI=E(_OE),_OJ=E(_OI.b),_OK=E(_OI.c),_OL=E(_OI.a),_OM=E(_Ow),_ON=E(_OM.c),_OO=E(_OM.b),_OP=E(_OM.a),_OQ=E(_Or),_OR=E(_OQ.c),_OS=E(_OQ.b),_OT=E(_OQ.a),_OU=_OJ*_ON-_OO*_OK,_OV=_OK*_OP-_ON*_OL,_OW=_OL*_OO-_OP*_OJ,_OX=B(_oX(_ny,_OV*_OR-_OS*_OW,_OW*_OT-_OR*_OU,_OU*_OS-_OT*_OV,_OP,_OO,_ON));return new T6(0,_NF,_NT,E(new T2(0,E(new T3(0,E(_OU),E(_OV),E(_OW))),E(_OX))),E(_Ny),_OB,_Ne);}),new T2(1,new T(function(){var _OY=E(_OG),_OZ=E(_OY.b),_P0=E(_OY.c),_P1=E(_OY.a),_P2=E(_Ou),_P3=E(_P2.c),_P4=E(_P2.b),_P5=E(_P2.a),_P6=E(_Oo),_P7=E(_P6.c),_P8=E(_P6.b),_P9=E(_P6.a),_Pa=_OZ*_P3-_P4*_P0,_Pb=_P0*_P5-_P3*_P1,_Pc=_P1*_P4-_P5*_OZ,_Pd=B(_oX(_ny,_Pb*_P7-_P8*_Pc,_Pc*_P9-_P7*_Pa,_Pa*_P8-_P9*_Pb,_P5,_P4,_P3));return new T6(0,_NF,_NT,E(_Ny),E(new T2(0,E(new T3(0,E(_Pa),E(_Pb),E(_Pc))),E(_Pd))),_OB,_Ne);}),new T(function(){return B(_O3(_O6));}))):new T2(1,new T(function(){var _Pe=E(_OE),_Pf=E(_Pe.b),_Pg=E(_Pe.c),_Ph=E(_Pe.a),_Pi=E(_Ow),_Pj=_Pi.a,_Pk=_Pi.b,_Pl=_Pi.c,_Pm=B(_pY(_ny,_Ph,_Pf,_Pg,_Pj,_Pk,_Pl)),_Pn=E(_Or),_Po=E(_Pn.c),_Pp=E(_Pn.b),_Pq=E(_Pn.a),_Pr=B(_oX(_ny,_Pf*_Po-_Pp*_Pg,_Pg*_Pq-_Po*_Ph,_Ph*_Pp-_Pq*_Pf,_Pj,_Pk,_Pl)),_Ps=E(_OG),_Pt=E(_Ps.b),_Pu=E(_Ps.c),_Pv=E(_Ps.a),_Pw=E(_Ou),_Px=_Pw.a,_Py=_Pw.b,_Pz=_Pw.c,_PA=B(_pY(_ny,_Pv,_Pt,_Pu,_Px,_Py,_Pz)),_PB=E(_Oo),_PC=E(_PB.c),_PD=E(_PB.b),_PE=E(_PB.a),_PF=B(_oX(_ny,_Pt*_PC-_PD*_Pu,_Pu*_PE-_PC*_Pv,_Pv*_PD-_PE*_Pt,_Px,_Py,_Pz));return new T6(0,_NF,_NT,E(new T2(0,E(new T3(0,E(_Pm.a),E(_Pm.b),E(_Pm.c))),E(_Pr))),E(new T2(0,E(new T3(0,E(_PA.a),E(_PA.b),E(_PA.c))),E(_PF))),_OB,_Nf);}),new T(function(){return B(_O3(_O6));}));}};return B(_O3(_NZ));});return new T2(0,new T2(1,_O1,new T(function(){return E(E(_O0).a);})),new T(function(){return E(E(_O0).b);}));}}}}}},_PG=B(_NM(B(_wt(_NF,_ND)),_NG,_NH,_NI,_NJ,_)),_PH=E(_NK),_PI=E(_PH.d).a,_PJ=__app1(E(_Nq),B(_ok(new T2(1,new T2(0,_EC,_PH.h),new T2(1,new T2(0,_EB,_PH.i),_w))))),_PK=__arr2lst(0,_PJ),_PL=B(_FQ(_PK,_)),_PM=__app1(E(_Nr),_NF),_PN=__arr2lst(0,_PM),_PO=B(_FQ(_PN,_));if(_NF!=_ND){var _PP=E(_PG),_PQ=E(_PP.b),_PR=B(_NE(_NF+1|0,E(_PQ.a),E(_PQ.b),_PQ.c,_PQ.d,_)),_PS=new T(function(){var _PT=new T(function(){var _PU=E(_PI),_PV=B(_N7(_ny,_PU.a,_PU.b,_PU.c));return new T3(0,E(_PV.a),E(_PV.b),E(_PV.c));}),_PW=new T(function(){var _PX=new T(function(){return B(_Nt(_PP.a));}),_PY=function(_PZ){var _Q0=E(_PZ);if(!_Q0._){return E(_PX);}else{var _Q1=E(_Q0.a),_Q2=E(_Q1.b),_Q3=E(_Q1.a),_Q4=E(_Q3.a),_Q5=E(_Q3.b),_Q6=E(_Q3.c),_Q7=E(_Q1.c),_Q8=_Q7.a,_Q9=_Q7.b,_Qa=E(_Q1.e);return new T2(1,new T(function(){var _Qb=E(_Q2.a)+ -_Q4,_Qc=E(_Q2.b)+ -_Q5,_Qd=E(_Q2.c)+ -_Q6,_Qe=B(_N7(_ny,_Q4,_Q5,_Q6)),_Qf=_Qe.a,_Qg=_Qe.b,_Qh=_Qe.c,_Qi=Math.sqrt(B(_oX(_ny,_Qb,_Qc,_Qd,_Qb,_Qc,_Qd))),_Qj=1/_Qi,_Qk=_Qb*_Qj,_Ql=_Qc*_Qj,_Qm=_Qd*_Qj,_Qn=B(_pY(_ny,_Qk,_Ql,_Qm,_Qf,_Qg,_Qh)),_Qo=B(_p7(_ny,_Qa.a,_Qa.b,_Qa.c)),_Qp=Math.sqrt(B(_MS(_ny,_Q8,_Q9,_Q8,_Q9))),_Qq=_Qp*E(_Qo.a),_Qr=_Qp*E(_Qo.b),_Qs=_Qp*E(_Qo.c),_Qt=B(_oX(_ny,_Ql*_Qs-_Qr*_Qm,_Qm*_Qq-_Qs*_Qk,_Qk*_Qr-_Qq*_Ql,_Qf,_Qg,_Qh));return new T6(0,_NF,_NF,E(new T2(0,E(new T3(0,E(_Qn.a),E(_Qn.b),E(_Qn.c))),E(_Qt))),E(_Ny),_Qi,_Nf);}),new T(function(){return B(_PY(_Q0.b));}));}};return B(_PY(_PL));}),_Qu=function(_Qv){var _Qw=E(_Qv);if(!_Qw._){return E(_PW);}else{var _Qx=E(_Qw.a),_Qy=E(_Qx.b),_Qz=new T(function(){var _QA=E(_PI),_QB=E(_Qy.c)+ -E(_QA.c),_QC=E(_Qy.b)+ -E(_QA.b),_QD=E(_Qy.a)+ -E(_QA.a),_QE=Math.sqrt(B(_oX(_ny,_QD,_QC,_QB,_QD,_QC,_QB))),_QF=function(_QG,_QH,_QI){var _QJ=E(_PT),_QK=_QJ.a,_QL=_QJ.b,_QM=_QJ.c,_QN=B(_pY(_ny,_QG,_QH,_QI,_QK,_QL,_QM)),_QO=B(_oX(_ny,_QH*0-0*_QI,_QI*0-0*_QG,_QG*0-0*_QH,_QK,_QL,_QM));return new T6(0,_NF,_NF,new T2(0,E(new T3(0,E(_QN.a),E(_QN.b),E(_QN.c))),E(_QO)),_Ny,_QE,_Nf);};if(!E(_Qx.g)){var _QP=1/_QE,_QQ=B(_QF(_QD*_QP,_QC*_QP,_QB*_QP));return new T6(0,_QQ.a,_QQ.b,E(_QQ.c),E(_QQ.d),_QQ.e,_QQ.f);}else{var _QR=1/_QE,_QS=B(_QF(-1*_QD*_QR,-1*_QC*_QR,-1*_QB*_QR));return new T6(0,_QS.a,_QS.b,E(_QS.c),E(_QS.d),_QS.e,_QS.f);}});return new T2(1,_Qz,new T(function(){return B(_Qu(_Qw.b));}));}};return B(_Qu(_PO));});return new T2(0,new T2(1,_PS,new T(function(){return E(E(_PR).a);})),new T(function(){return E(E(_PR).b);}));}else{var _QT=new T(function(){var _QU=new T(function(){var _QV=E(_PI),_QW=B(_N7(_ny,_QV.a,_QV.b,_QV.c));return new T3(0,E(_QW.a),E(_QW.b),E(_QW.c));}),_QX=new T(function(){var _QY=new T(function(){return B(_Nt(E(_PG).a));}),_QZ=function(_R0){var _R1=E(_R0);if(!_R1._){return E(_QY);}else{var _R2=E(_R1.a),_R3=E(_R2.b),_R4=E(_R2.a),_R5=E(_R4.a),_R6=E(_R4.b),_R7=E(_R4.c),_R8=E(_R2.c),_R9=_R8.a,_Ra=_R8.b,_Rb=E(_R2.e);return new T2(1,new T(function(){var _Rc=E(_R3.a)+ -_R5,_Rd=E(_R3.b)+ -_R6,_Re=E(_R3.c)+ -_R7,_Rf=B(_N7(_ny,_R5,_R6,_R7)),_Rg=_Rf.a,_Rh=_Rf.b,_Ri=_Rf.c,_Rj=Math.sqrt(B(_oX(_ny,_Rc,_Rd,_Re,_Rc,_Rd,_Re))),_Rk=1/_Rj,_Rl=_Rc*_Rk,_Rm=_Rd*_Rk,_Rn=_Re*_Rk,_Ro=B(_pY(_ny,_Rl,_Rm,_Rn,_Rg,_Rh,_Ri)),_Rp=B(_p7(_ny,_Rb.a,_Rb.b,_Rb.c)),_Rq=Math.sqrt(B(_MS(_ny,_R9,_Ra,_R9,_Ra))),_Rr=_Rq*E(_Rp.a),_Rs=_Rq*E(_Rp.b),_Rt=_Rq*E(_Rp.c),_Ru=B(_oX(_ny,_Rm*_Rt-_Rs*_Rn,_Rn*_Rr-_Rt*_Rl,_Rl*_Rs-_Rr*_Rm,_Rg,_Rh,_Ri));return new T6(0,_NF,_NF,E(new T2(0,E(new T3(0,E(_Ro.a),E(_Ro.b),E(_Ro.c))),E(_Ru))),E(_Ny),_Rj,_Nf);}),new T(function(){return B(_QZ(_R1.b));}));}};return B(_QZ(_PL));}),_Rv=function(_Rw){var _Rx=E(_Rw);if(!_Rx._){return E(_QX);}else{var _Ry=E(_Rx.a),_Rz=E(_Ry.b),_RA=new T(function(){var _RB=E(_PI),_RC=E(_Rz.c)+ -E(_RB.c),_RD=E(_Rz.b)+ -E(_RB.b),_RE=E(_Rz.a)+ -E(_RB.a),_RF=Math.sqrt(B(_oX(_ny,_RE,_RD,_RC,_RE,_RD,_RC))),_RG=function(_RH,_RI,_RJ){var _RK=E(_QU),_RL=_RK.a,_RM=_RK.b,_RN=_RK.c,_RO=B(_pY(_ny,_RH,_RI,_RJ,_RL,_RM,_RN)),_RP=B(_oX(_ny,_RI*0-0*_RJ,_RJ*0-0*_RH,_RH*0-0*_RI,_RL,_RM,_RN));return new T6(0,_NF,_NF,new T2(0,E(new T3(0,E(_RO.a),E(_RO.b),E(_RO.c))),E(_RP)),_Ny,_RF,_Nf);};if(!E(_Ry.g)){var _RQ=1/_RF,_RR=B(_RG(_RE*_RQ,_RD*_RQ,_RC*_RQ));return new T6(0,_RR.a,_RR.b,E(_RR.c),E(_RR.d),_RR.e,_RR.f);}else{var _RS=1/_RF,_RT=B(_RG(-1*_RE*_RS,-1*_RD*_RS,-1*_RC*_RS));return new T6(0,_RT.a,_RT.b,E(_RT.c),E(_RT.d),_RT.e,_RT.f);}});return new T2(1,_RA,new T(function(){return B(_Rv(_Rx.b));}));}};return B(_Rv(_PO));});return new T2(0,new T2(1,_QT,_w),new T(function(){return E(E(_PG).b);}));}}}},_RU=B(_NE(_NC,_NC,_ND,_NB.c,_NB.d,_));return new F(function(){return _MK(_,_RU);});}else{return new F(function(){return _MK(_,new T2(0,_w,_NB));});}},_RV=new T(function(){return eval("__strict(passObject)");}),_RW=new T(function(){return eval("__strict(refresh)");}),_RX=function(_RY,_){var _RZ=__app0(E(_RW)),_S0=__app0(E(_EG)),_S1=E(_RY),_S2=_S1.c,_S3=_S1.d,_S4=E(_S1.a),_S5=E(_S1.b);if(_S4<=_S5){if(_S4>_S5){return E(_EE);}else{if(0>=_S2){return new F(function(){return _ER(_S2,0);});}else{var _S6=E(_S3[0]),_S7=E(_RV),_S8=__app2(_S7,_S4,B(_ok(new T2(1,new T2(0,_EC,_S6.h),new T2(1,new T2(0,_EB,_S6.i),_w)))));if(_S4!=_S5){var _S9=function(_Sa,_){if(_S4>_Sa){return E(_EE);}else{if(_Sa>_S5){return E(_EE);}else{var _Sb=_Sa-_S4|0;if(0>_Sb){return new F(function(){return _ER(_S2,_Sb);});}else{if(_Sb>=_S2){return new F(function(){return _ER(_S2,_Sb);});}else{var _Sc=E(_S3[_Sb]),_Sd=__app2(_S7,_Sa,B(_ok(new T2(1,new T2(0,_EC,_Sc.h),new T2(1,new T2(0,_EB,_Sc.i),_w)))));if(_Sa!=_S5){var _Se=B(_S9(_Sa+1|0,_));return new T2(1,_oj,_Se);}else{return _EW;}}}}}},_Sf=B(_S9(_S4+1|0,_)),_Sg=__app0(E(_EF)),_Sh=B(_Nz(_S1,_));return new T(function(){return E(E(_Sh).b);});}else{var _Si=__app0(E(_EF)),_Sj=B(_Nz(_S1,_));return new T(function(){return E(E(_Sj).b);});}}}}else{var _Sk=__app0(E(_EF)),_Sl=B(_Nz(_S1,_));return new T(function(){return E(E(_Sl).b);});}},_Sm=function(_Sn,_){while(1){var _So=E(_Sn);if(!_So._){return _oj;}else{var _Sp=_So.b,_Sq=E(_So.a);switch(_Sq._){case 0:var _Sr=B(A1(_Sq.a,_));_Sn=B(_n(_Sp,new T2(1,_Sr,_w)));continue;case 1:_Sn=B(_n(_Sp,_Sq.a));continue;default:_Sn=_Sp;continue;}}}},_Ss=function(_St,_Su,_){var _Sv=E(_St);switch(_Sv._){case 0:var _Sw=B(A1(_Sv.a,_));return new F(function(){return _Sm(B(_n(_Su,new T2(1,_Sw,_w))),_);});break;case 1:return new F(function(){return _Sm(B(_n(_Su,_Sv.a)),_);});break;default:return new F(function(){return _Sm(_Su,_);});}},_Sx=new T0(2),_Sy=function(_Sz){return new T0(2);},_SA=function(_SB,_SC,_SD){return function(_){var _SE=E(_SB),_SF=rMV(_SE),_SG=E(_SF);if(!_SG._){var _SH=new T(function(){var _SI=new T(function(){return B(A1(_SD,_oj));});return B(_n(_SG.b,new T2(1,new T2(0,_SC,function(_SJ){return E(_SI);}),_w)));}),_=wMV(_SE,new T2(0,_SG.a,_SH));return _Sx;}else{var _SK=E(_SG.a);if(!_SK._){var _=wMV(_SE,new T2(0,_SC,_w));return new T(function(){return B(A1(_SD,_oj));});}else{var _=wMV(_SE,new T1(1,_SK.b));return new T1(1,new T2(1,new T(function(){return B(A1(_SD,_oj));}),new T2(1,new T(function(){return B(A2(_SK.a,_SC,_Sy));}),_w)));}}};},_SL=new T(function(){return E(_tZ);}),_SM=new T(function(){return eval("window.requestAnimationFrame");}),_SN=new T1(1,_w),_SO=function(_SP,_SQ){return function(_){var _SR=E(_SP),_SS=rMV(_SR),_ST=E(_SS);if(!_ST._){var _SU=_ST.a,_SV=E(_ST.b);if(!_SV._){var _=wMV(_SR,_SN);return new T(function(){return B(A1(_SQ,_SU));});}else{var _SW=E(_SV.a),_=wMV(_SR,new T2(0,_SW.a,_SV.b));return new T1(1,new T2(1,new T(function(){return B(A1(_SQ,_SU));}),new T2(1,new T(function(){return B(A1(_SW.b,_Sy));}),_w)));}}else{var _SX=new T(function(){var _SY=function(_SZ){var _T0=new T(function(){return B(A1(_SQ,_SZ));});return function(_T1){return E(_T0);};};return B(_n(_ST.a,new T2(1,_SY,_w)));}),_=wMV(_SR,new T1(1,_SX));return _Sx;}};},_T2=function(_T3,_T4){return new T1(0,B(_SO(_T3,_T4)));},_T5=function(_T6,_T7){var _T8=new T(function(){return new T1(0,B(_SA(_T6,_oj,_Sy)));});return function(_){var _T9=__createJSFunc(2,function(_Ta,_){var _Tb=B(_Ss(_T8,_w,_));return _SL;}),_Tc=__app1(E(_SM),_T9);return new T(function(){return B(_T2(_T6,_T7));});};},_Td=new T1(1,_w),_Te=function(_Tf,_Tg,_){var _Th=function(_){var _Ti=nMV(_Tf),_Tj=_Ti;return new T(function(){var _Tk=new T(function(){return B(_Tl(_));}),_Tm=function(_){var _Tn=rMV(_Tj),_To=B(A2(_Tg,_Tn,_)),_=wMV(_Tj,_To),_Tp=function(_){var _Tq=nMV(_Td);return new T(function(){return new T1(0,B(_T5(_Tq,function(_Tr){return E(_Tk);})));});};return new T1(0,_Tp);},_Ts=new T(function(){return new T1(0,_Tm);}),_Tl=function(_Tt){return E(_Ts);};return B(_Tl(_));});};return new F(function(){return _Ss(new T1(0,_Th),_w,_);});},_Tu=new T(function(){return eval("__strict(setBounds)");}),_Tv=function(_){var _Tw=__app3(E(_lr),E(_ls),E(_lV),E(_lq)),_Tx=__app2(E(_Tu),E(_iG),E(_iD));return new F(function(){return _Te(_EA,_RX,_);});},_Ty=function(_){return new F(function(){return _Tv(_);});};
var hasteMain = function() {B(A(_Ty, [0]));};window.onload = hasteMain;