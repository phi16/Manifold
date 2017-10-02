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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x){return E(E(_8x).b);},_8y=function(_8z){return E(E(_8z).d);},_8A=new T1(0,2),_8B=new T2(0,E(_1o),E(_8A)),_8C=new T1(0,5),_8D=new T1(0,4),_8E=new T2(0,E(_8D),E(_8C)),_8F=function(_8G){return E(E(_8G).e);},_8H=function(_8I,_8J,_8K,_8L){var _8M=B(_8q(_8I)),_8N=B(_8s(_8M)),_8O=new T(function(){var _8P=new T(function(){var _8Q=new T(function(){var _8R=new T(function(){var _8S=new T(function(){var _8T=new T(function(){return B(A3(_86,_8N,new T(function(){return B(A3(_8u,_8N,_8J,_8J));}),new T(function(){return B(A3(_8u,_8N,_8L,_8L));})));});return B(A2(_8F,_8I,_8T));});return B(A3(_8w,_8N,_8S,new T(function(){return B(A2(_8y,_8M,_8E));})));});return B(A3(_8u,_8N,_8R,_8R));});return B(A3(_86,_8N,_8Q,new T(function(){return B(A3(_8u,_8N,_8K,_8K));})));});return B(A2(_8F,_8I,_8P));});return new F(function(){return A3(_8w,_8N,_8O,new T(function(){return B(A2(_8y,_8M,_8B));}));});},_8U=new T(function(){return B(unCStr("x"));}),_8V=new T1(0,_8U),_8W=new T(function(){return B(unCStr("y"));}),_8X=new T1(0,_8W),_8Y=new T(function(){return B(unCStr("z"));}),_8Z=new T1(0,_8Y),_90=new T(function(){return B(_8H(_8p,_8V,_8X,_8Z));}),_91=new T(function(){return toJSStr(B(_1v(_x,_1l,_90)));}),_92=new T3(0,E(_8V),E(_8X),E(_8Z)),_93=new T(function(){return B(unCStr("(/=) is not defined"));}),_94=new T(function(){return B(err(_93));}),_95=new T(function(){return B(unCStr("(==) is not defined"));}),_96=new T(function(){return B(err(_95));}),_97=new T2(0,_96,_94),_98=new T(function(){return B(unCStr("(<) is not defined"));}),_99=new T(function(){return B(err(_98));}),_9a=new T(function(){return B(unCStr("(<=) is not defined"));}),_9b=new T(function(){return B(err(_9a));}),_9c=new T(function(){return B(unCStr("(>) is not defined"));}),_9d=new T(function(){return B(err(_9c));}),_9e=new T(function(){return B(unCStr("(>=) is not defined"));}),_9f=new T(function(){return B(err(_9e));}),_9g=new T(function(){return B(unCStr("compare is not defined"));}),_9h=new T(function(){return B(err(_9g));}),_9i=new T(function(){return B(unCStr("max("));}),_9j=new T1(0,_9i),_9k=function(_9l,_9m){return new T1(1,new T2(1,_9j,new T2(1,_9l,new T2(1,_22,new T2(1,_9m,_1S)))));},_9n=new T(function(){return B(unCStr("min("));}),_9o=new T1(0,_9n),_9p=function(_9q,_9r){return new T1(1,new T2(1,_9o,new T2(1,_9q,new T2(1,_22,new T2(1,_9r,_1S)))));},_9s={_:0,a:_97,b:_9h,c:_99,d:_9b,e:_9d,f:_9f,g:_9k,h:_9p},_9t=new T2(0,_8p,_9s),_9u=function(_9v,_9w){var _9x=E(_9v);return E(_9w);},_9y=function(_9z,_9A){var _9B=E(_9A);return E(_9z);},_9C=function(_9D,_9E){var _9F=E(_9D),_9G=E(_9E);return new T3(0,E(B(A1(_9F.a,_9G.a))),E(B(A1(_9F.b,_9G.b))),E(B(A1(_9F.c,_9G.c))));},_9H=function(_9I,_9J,_9K){return new T3(0,E(_9I),E(_9J),E(_9K));},_9L=function(_9M){return new F(function(){return _9H(_9M,_9M,_9M);});},_9N=function(_9O,_9P){var _9Q=E(_9P),_9R=E(_9O);return new T3(0,E(_9R),E(_9R),E(_9R));},_9S=function(_9T,_9U){var _9V=E(_9U);return new T3(0,E(B(A1(_9T,_9V.a))),E(B(A1(_9T,_9V.b))),E(B(A1(_9T,_9V.c))));},_9W=new T2(0,_9S,_9N),_9X=new T5(0,_9W,_9L,_9C,_9u,_9y),_9Y=new T1(0,0),_9Z=function(_a0){return E(E(_a0).g);},_a1=function(_a2){var _a3=B(A2(_9Z,_a2,_1o)),_a4=B(A2(_9Z,_a2,_9Y));return new T3(0,E(new T3(0,E(_a3),E(_a4),E(_a4))),E(new T3(0,E(_a4),E(_a3),E(_a4))),E(new T3(0,E(_a4),E(_a4),E(_a3))));},_a5=function(_a6){return E(E(_a6).a);},_a7=function(_a8){return E(E(_a8).f);},_a9=function(_aa){return E(E(_aa).b);},_ab=function(_ac){return E(E(_ac).c);},_ad=function(_ae){return E(E(_ae).a);},_af=function(_ag){return E(E(_ag).d);},_ah=function(_ai,_aj,_ak,_al,_am){var _an=new T(function(){return E(E(E(_ai).c).a);}),_ao=new T(function(){var _ap=E(_ai).a,_aq=new T(function(){var _ar=new T(function(){return B(_8q(_an));}),_as=new T(function(){return B(_8s(_ar));}),_at=new T(function(){return B(A2(_af,_an,_aj));}),_au=new T(function(){return B(A3(_a7,_an,_aj,_al));}),_av=function(_aw,_ax){var _ay=new T(function(){var _az=new T(function(){return B(A3(_a9,_ar,new T(function(){return B(A3(_8u,_as,_al,_aw));}),_aj));});return B(A3(_86,_as,_az,new T(function(){return B(A3(_8u,_as,_ax,_at));})));});return new F(function(){return A3(_8u,_as,_au,_ay);});};return B(A3(_ad,B(_a5(_ap)),_av,_ak));});return B(A3(_ab,_ap,_aq,_am));});return new T2(0,new T(function(){return B(A3(_a7,_an,_aj,_al));}),_ao);},_aA=function(_aB,_aC,_aD,_aE){var _aF=E(_aD),_aG=E(_aE),_aH=B(_ah(_aC,_aF.a,_aF.b,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=new T1(0,1),_aJ=function(_aK){return E(E(_aK).l);},_aL=function(_aM,_aN,_aO){var _aP=new T(function(){return E(E(E(_aM).c).a);}),_aQ=new T(function(){var _aR=new T(function(){return B(_8q(_aP));}),_aS=new T(function(){var _aT=B(_8s(_aR)),_aU=new T(function(){var _aV=new T(function(){return B(A3(_8w,_aT,new T(function(){return B(A2(_9Z,_aT,_aI));}),new T(function(){return B(A3(_8u,_aT,_aN,_aN));})));});return B(A2(_8F,_aP,_aV));});return B(A2(_88,_aT,_aU));});return B(A3(_ad,B(_a5(E(_aM).a)),function(_aW){return new F(function(){return A3(_a9,_aR,_aW,_aS);});},_aO));});return new T2(0,new T(function(){return B(A2(_aJ,_aP,_aN));}),_aQ);},_aX=function(_aY,_aZ,_b0){var _b1=E(_b0),_b2=B(_aL(_aZ,_b1.a,_b1.b));return new T2(0,_b2.a,_b2.b);},_b3=function(_b4){return E(E(_b4).r);},_b5=function(_b6,_b7,_b8){var _b9=new T(function(){return E(E(E(_b6).c).a);}),_ba=new T(function(){var _bb=new T(function(){return B(_8q(_b9));}),_bc=new T(function(){var _bd=new T(function(){var _be=B(_8s(_bb));return B(A3(_8w,_be,new T(function(){return B(A3(_8u,_be,_b7,_b7));}),new T(function(){return B(A2(_9Z,_be,_aI));})));});return B(A2(_8F,_b9,_bd));});return B(A3(_ad,B(_a5(E(_b6).a)),function(_bf){return new F(function(){return A3(_a9,_bb,_bf,_bc);});},_b8));});return new T2(0,new T(function(){return B(A2(_b3,_b9,_b7));}),_ba);},_bg=function(_bh,_bi,_bj){var _bk=E(_bj),_bl=B(_b5(_bi,_bk.a,_bk.b));return new T2(0,_bl.a,_bl.b);},_bm=function(_bn){return E(E(_bn).k);},_bo=function(_bp,_bq,_br){var _bs=new T(function(){return E(E(E(_bp).c).a);}),_bt=new T(function(){var _bu=new T(function(){return B(_8q(_bs));}),_bv=new T(function(){var _bw=new T(function(){var _bx=B(_8s(_bu));return B(A3(_8w,_bx,new T(function(){return B(A2(_9Z,_bx,_aI));}),new T(function(){return B(A3(_8u,_bx,_bq,_bq));})));});return B(A2(_8F,_bs,_bw));});return B(A3(_ad,B(_a5(E(_bp).a)),function(_by){return new F(function(){return A3(_a9,_bu,_by,_bv);});},_br));});return new T2(0,new T(function(){return B(A2(_bm,_bs,_bq));}),_bt);},_bz=function(_bA,_bB,_bC){var _bD=E(_bC),_bE=B(_bo(_bB,_bD.a,_bD.b));return new T2(0,_bE.a,_bE.b);},_bF=function(_bG){return E(E(_bG).q);},_bH=function(_bI,_bJ,_bK){var _bL=new T(function(){return E(E(E(_bI).c).a);}),_bM=new T(function(){var _bN=new T(function(){return B(_8q(_bL));}),_bO=new T(function(){var _bP=new T(function(){var _bQ=B(_8s(_bN));return B(A3(_86,_bQ,new T(function(){return B(A3(_8u,_bQ,_bJ,_bJ));}),new T(function(){return B(A2(_9Z,_bQ,_aI));})));});return B(A2(_8F,_bL,_bP));});return B(A3(_ad,B(_a5(E(_bI).a)),function(_bR){return new F(function(){return A3(_a9,_bN,_bR,_bO);});},_bK));});return new T2(0,new T(function(){return B(A2(_bF,_bL,_bJ));}),_bM);},_bS=function(_bT,_bU,_bV){var _bW=E(_bV),_bX=B(_bH(_bU,_bW.a,_bW.b));return new T2(0,_bX.a,_bX.b);},_bY=function(_bZ){return E(E(_bZ).m);},_c0=function(_c1,_c2,_c3){var _c4=new T(function(){return E(E(E(_c1).c).a);}),_c5=new T(function(){var _c6=new T(function(){return B(_8q(_c4));}),_c7=new T(function(){var _c8=B(_8s(_c6));return B(A3(_86,_c8,new T(function(){return B(A2(_9Z,_c8,_aI));}),new T(function(){return B(A3(_8u,_c8,_c2,_c2));})));});return B(A3(_ad,B(_a5(E(_c1).a)),function(_c9){return new F(function(){return A3(_a9,_c6,_c9,_c7);});},_c3));});return new T2(0,new T(function(){return B(A2(_bY,_c4,_c2));}),_c5);},_ca=function(_cb,_cc,_cd){var _ce=E(_cd),_cf=B(_c0(_cc,_ce.a,_ce.b));return new T2(0,_cf.a,_cf.b);},_cg=function(_ch){return E(E(_ch).s);},_ci=function(_cj,_ck,_cl){var _cm=new T(function(){return E(E(E(_cj).c).a);}),_cn=new T(function(){var _co=new T(function(){return B(_8q(_cm));}),_cp=new T(function(){var _cq=B(_8s(_co));return B(A3(_8w,_cq,new T(function(){return B(A2(_9Z,_cq,_aI));}),new T(function(){return B(A3(_8u,_cq,_ck,_ck));})));});return B(A3(_ad,B(_a5(E(_cj).a)),function(_cr){return new F(function(){return A3(_a9,_co,_cr,_cp);});},_cl));});return new T2(0,new T(function(){return B(A2(_cg,_cm,_ck));}),_cn);},_cs=function(_ct,_cu,_cv){var _cw=E(_cv),_cx=B(_ci(_cu,_cw.a,_cw.b));return new T2(0,_cx.a,_cx.b);},_cy=function(_cz){return E(E(_cz).i);},_cA=function(_cB){return E(E(_cB).h);},_cC=function(_cD,_cE,_cF){var _cG=new T(function(){return E(E(E(_cD).c).a);}),_cH=new T(function(){var _cI=new T(function(){return B(_8s(new T(function(){return B(_8q(_cG));})));}),_cJ=new T(function(){return B(A2(_88,_cI,new T(function(){return B(A2(_cA,_cG,_cE));})));});return B(A3(_ad,B(_a5(E(_cD).a)),function(_cK){return new F(function(){return A3(_8u,_cI,_cK,_cJ);});},_cF));});return new T2(0,new T(function(){return B(A2(_cy,_cG,_cE));}),_cH);},_cL=function(_cM,_cN,_cO){var _cP=E(_cO),_cQ=B(_cC(_cN,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);},_cR=function(_cS){return E(E(_cS).o);},_cT=function(_cU){return E(E(_cU).n);},_cV=function(_cW,_cX,_cY){var _cZ=new T(function(){return E(E(E(_cW).c).a);}),_d0=new T(function(){var _d1=new T(function(){return B(_8s(new T(function(){return B(_8q(_cZ));})));}),_d2=new T(function(){return B(A2(_cT,_cZ,_cX));});return B(A3(_ad,B(_a5(E(_cW).a)),function(_d3){return new F(function(){return A3(_8u,_d1,_d3,_d2);});},_cY));});return new T2(0,new T(function(){return B(A2(_cR,_cZ,_cX));}),_d0);},_d4=function(_d5,_d6,_d7){var _d8=E(_d7),_d9=B(_cV(_d6,_d8.a,_d8.b));return new T2(0,_d9.a,_d9.b);},_da=function(_db){return E(E(_db).c);},_dc=function(_dd,_de,_df){var _dg=new T(function(){return E(E(E(_dd).c).a);}),_dh=new T(function(){var _di=new T(function(){return B(_8s(new T(function(){return B(_8q(_dg));})));}),_dj=new T(function(){return B(A2(_da,_dg,_de));});return B(A3(_ad,B(_a5(E(_dd).a)),function(_dk){return new F(function(){return A3(_8u,_di,_dk,_dj);});},_df));});return new T2(0,new T(function(){return B(A2(_da,_dg,_de));}),_dh);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_dc(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du){var _dv=new T(function(){return E(E(E(_ds).c).a);}),_dw=new T(function(){var _dx=new T(function(){return B(_8q(_dv));}),_dy=new T(function(){return B(_8s(_dx));}),_dz=new T(function(){return B(A3(_a9,_dx,new T(function(){return B(A2(_9Z,_dy,_aI));}),_dt));});return B(A3(_ad,B(_a5(E(_ds).a)),function(_dA){return new F(function(){return A3(_8u,_dy,_dA,_dz);});},_du));});return new T2(0,new T(function(){return B(A2(_af,_dv,_dt));}),_dw);},_dB=function(_dC,_dD,_dE){var _dF=E(_dE),_dG=B(_dr(_dD,_dF.a,_dF.b));return new T2(0,_dG.a,_dG.b);},_dH=function(_dI,_dJ,_dK,_dL){var _dM=new T(function(){return E(E(_dJ).c);}),_dN=new T3(0,new T(function(){return E(E(_dJ).a);}),new T(function(){return E(E(_dJ).b);}),new T2(0,new T(function(){return E(E(_dM).a);}),new T(function(){return E(E(_dM).b);})));return new F(function(){return A3(_a9,_dI,new T(function(){var _dO=E(_dL),_dP=B(_dr(_dN,_dO.a,_dO.b));return new T2(0,_dP.a,_dP.b);}),new T(function(){var _dQ=E(_dK),_dR=B(_dr(_dN,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);}));});},_dS=function(_dT){return E(E(_dT).b);},_dU=function(_dV){return E(E(_dV).b);},_dW=function(_dX){var _dY=new T(function(){return E(E(E(_dX).c).a);}),_dZ=new T(function(){return B(A2(_dU,E(_dX).a,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_dY)))),_L));})));});return new T2(0,new T(function(){return B(_dS(_dY));}),_dZ);},_e0=function(_e1,_e2){var _e3=B(_dW(_e2));return new T2(0,_e3.a,_e3.b);},_e4=function(_e5,_e6,_e7){var _e8=new T(function(){return E(E(E(_e5).c).a);}),_e9=new T(function(){var _ea=new T(function(){return B(_8s(new T(function(){return B(_8q(_e8));})));}),_eb=new T(function(){return B(A2(_cy,_e8,_e6));});return B(A3(_ad,B(_a5(E(_e5).a)),function(_ec){return new F(function(){return A3(_8u,_ea,_ec,_eb);});},_e7));});return new T2(0,new T(function(){return B(A2(_cA,_e8,_e6));}),_e9);},_ed=function(_ee,_ef,_eg){var _eh=E(_eg),_ei=B(_e4(_ef,_eh.a,_eh.b));return new T2(0,_ei.a,_ei.b);},_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(E(_ek).c).a);}),_eo=new T(function(){var _ep=new T(function(){return B(_8s(new T(function(){return B(_8q(_en));})));}),_eq=new T(function(){return B(A2(_cR,_en,_el));});return B(A3(_ad,B(_a5(E(_ek).a)),function(_er){return new F(function(){return A3(_8u,_ep,_er,_eq);});},_em));});return new T2(0,new T(function(){return B(A2(_cT,_en,_el));}),_eo);},_es=function(_et,_eu,_ev){var _ew=E(_ev),_ex=B(_ej(_eu,_ew.a,_ew.b));return new T2(0,_ex.a,_ex.b);},_ey=new T1(0,2),_ez=function(_eA,_eB,_eC){var _eD=new T(function(){return E(E(E(_eA).c).a);}),_eE=new T(function(){var _eF=new T(function(){return B(_8q(_eD));}),_eG=new T(function(){return B(_8s(_eF));}),_eH=new T(function(){var _eI=new T(function(){return B(A3(_a9,_eF,new T(function(){return B(A2(_9Z,_eG,_aI));}),new T(function(){return B(A2(_9Z,_eG,_ey));})));});return B(A3(_a9,_eF,_eI,new T(function(){return B(A2(_8F,_eD,_eB));})));});return B(A3(_ad,B(_a5(E(_eA).a)),function(_eJ){return new F(function(){return A3(_8u,_eG,_eJ,_eH);});},_eC));});return new T2(0,new T(function(){return B(A2(_8F,_eD,_eB));}),_eE);},_eK=function(_eL,_eM,_eN){var _eO=E(_eN),_eP=B(_ez(_eM,_eO.a,_eO.b));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR){return E(E(_eR).j);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_8q(_eW));}),_eZ=new T(function(){var _f0=new T(function(){return B(A2(_cy,_eW,_eU));});return B(A3(_8u,B(_8s(_eY)),_f0,_f0));});return B(A3(_ad,B(_a5(E(_eT).a)),function(_f1){return new F(function(){return A3(_a9,_eY,_f1,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_eQ,_eW,_eU));}),_eX);},_f2=function(_f3,_f4,_f5){var _f6=E(_f5),_f7=B(_eS(_f4,_f6.a,_f6.b));return new T2(0,_f7.a,_f7.b);},_f8=function(_f9){return E(E(_f9).p);},_fa=function(_fb,_fc,_fd){var _fe=new T(function(){return E(E(E(_fb).c).a);}),_ff=new T(function(){var _fg=new T(function(){return B(_8q(_fe));}),_fh=new T(function(){var _fi=new T(function(){return B(A2(_cR,_fe,_fc));});return B(A3(_8u,B(_8s(_fg)),_fi,_fi));});return B(A3(_ad,B(_a5(E(_fb).a)),function(_fj){return new F(function(){return A3(_a9,_fg,_fj,_fh);});},_fd));});return new T2(0,new T(function(){return B(A2(_f8,_fe,_fc));}),_ff);},_fk=function(_fl,_fm,_fn){var _fo=E(_fn),_fp=B(_fa(_fm,_fo.a,_fo.b));return new T2(0,_fp.a,_fp.b);},_fq=function(_fr,_fs){return {_:0,a:_fr,b:new T(function(){return B(_e0(_fr,_fs));}),c:function(_ft){return new F(function(){return _dl(_fr,_fs,_ft);});},d:function(_ft){return new F(function(){return _dB(_fr,_fs,_ft);});},e:function(_ft){return new F(function(){return _eK(_fr,_fs,_ft);});},f:function(_fu,_ft){return new F(function(){return _aA(_fr,_fs,_fu,_ft);});},g:function(_fu,_ft){return new F(function(){return _dH(_fr,_fs,_fu,_ft);});},h:function(_ft){return new F(function(){return _ed(_fr,_fs,_ft);});},i:function(_ft){return new F(function(){return _cL(_fr,_fs,_ft);});},j:function(_ft){return new F(function(){return _f2(_fr,_fs,_ft);});},k:function(_ft){return new F(function(){return _bz(_fr,_fs,_ft);});},l:function(_ft){return new F(function(){return _aX(_fr,_fs,_ft);});},m:function(_ft){return new F(function(){return _ca(_fr,_fs,_ft);});},n:function(_ft){return new F(function(){return _es(_fr,_fs,_ft);});},o:function(_ft){return new F(function(){return _d4(_fr,_fs,_ft);});},p:function(_ft){return new F(function(){return _fk(_fr,_fs,_ft);});},q:function(_ft){return new F(function(){return _bS(_fr,_fs,_ft);});},r:function(_ft){return new F(function(){return _bg(_fr,_fs,_ft);});},s:function(_ft){return new F(function(){return _cs(_fr,_fs,_ft);});}};},_fv=function(_fw,_fx,_fy,_fz,_fA){var _fB=new T(function(){return B(_8q(new T(function(){return E(E(E(_fw).c).a);})));}),_fC=new T(function(){var _fD=E(_fw).a,_fE=new T(function(){var _fF=new T(function(){return B(_8s(_fB));}),_fG=new T(function(){return B(A3(_8u,_fF,_fz,_fz));}),_fH=function(_fI,_fJ){var _fK=new T(function(){return B(A3(_8w,_fF,new T(function(){return B(A3(_8u,_fF,_fI,_fz));}),new T(function(){return B(A3(_8u,_fF,_fx,_fJ));})));});return new F(function(){return A3(_a9,_fB,_fK,_fG);});};return B(A3(_ad,B(_a5(_fD)),_fH,_fy));});return B(A3(_ab,_fD,_fE,_fA));});return new T2(0,new T(function(){return B(A3(_a9,_fB,_fx,_fz));}),_fC);},_fL=function(_fM,_fN,_fO,_fP){var _fQ=E(_fO),_fR=E(_fP),_fS=B(_fv(_fN,_fQ.a,_fQ.b,_fR.a,_fR.b));return new T2(0,_fS.a,_fS.b);},_fT=function(_fU,_fV){var _fW=new T(function(){return B(_8q(new T(function(){return E(E(E(_fU).c).a);})));}),_fX=new T(function(){return B(A2(_dU,E(_fU).a,new T(function(){return B(A2(_9Z,B(_8s(_fW)),_L));})));});return new T2(0,new T(function(){return B(A2(_8y,_fW,_fV));}),_fX);},_fY=function(_fZ,_g0,_g1){var _g2=B(_fT(_g0,_g1));return new T2(0,_g2.a,_g2.b);},_g3=function(_g4,_g5,_g6){var _g7=new T(function(){return B(_8q(new T(function(){return E(E(E(_g4).c).a);})));}),_g8=new T(function(){return B(_8s(_g7));}),_g9=new T(function(){var _ga=new T(function(){var _gb=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),new T(function(){return B(A3(_8u,_g8,_g5,_g5));})));});return B(A2(_88,_g8,_gb));});return B(A3(_ad,B(_a5(E(_g4).a)),function(_gc){return new F(function(){return A3(_8u,_g8,_gc,_ga);});},_g6));}),_gd=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),_g5));});return new T2(0,_gd,_g9);},_ge=function(_gf,_gg,_gh){var _gi=E(_gh),_gj=B(_g3(_gg,_gi.a,_gi.b));return new T2(0,_gj.a,_gj.b);},_gk=function(_gl,_gm){return new T4(0,_gl,function(_fu,_ft){return new F(function(){return _fL(_gl,_gm,_fu,_ft);});},function(_ft){return new F(function(){return _ge(_gl,_gm,_ft);});},function(_ft){return new F(function(){return _fY(_gl,_gm,_ft);});});},_gn=function(_go,_gp,_gq,_gr,_gs){var _gt=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_go).c).a);})));})));}),_gu=new T(function(){var _gv=E(_go).a,_gw=new T(function(){var _gx=function(_gy,_gz){return new F(function(){return A3(_86,_gt,new T(function(){return B(A3(_8u,_gt,_gp,_gz));}),new T(function(){return B(A3(_8u,_gt,_gy,_gr));}));});};return B(A3(_ad,B(_a5(_gv)),_gx,_gq));});return B(A3(_ab,_gv,_gw,_gs));});return new T2(0,new T(function(){return B(A3(_8u,_gt,_gp,_gr));}),_gu);},_gA=function(_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gn(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ,_gK,_gL,_gM){var _gN=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gI).c).a);})));})));}),_gO=new T(function(){var _gP=E(_gI).a,_gQ=new T(function(){return B(A3(_ad,B(_a5(_gP)),new T(function(){return B(_86(_gN));}),_gK));});return B(A3(_ab,_gP,_gQ,_gM));});return new T2(0,new T(function(){return B(A3(_86,_gN,_gJ,_gL));}),_gO);},_gR=function(_gS,_gT,_gU){var _gV=E(_gT),_gW=E(_gU),_gX=B(_gH(_gS,_gV.a,_gV.b,_gW.a,_gW.b));return new T2(0,_gX.a,_gX.b);},_gY=function(_gZ,_h0,_h1){var _h2=B(_h3(_gZ));return new F(function(){return A3(_86,_h2,_h0,new T(function(){return B(A2(_88,_h2,_h1));}));});},_h4=function(_h5){return E(E(_h5).e);},_h6=function(_h7){return E(E(_h7).f);},_h8=function(_h9,_ha,_hb){var _hc=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_h9).c).a);})));})));}),_hd=new T(function(){var _he=new T(function(){return B(A2(_h6,_hc,_ha));});return B(A3(_ad,B(_a5(E(_h9).a)),function(_hf){return new F(function(){return A3(_8u,_hc,_hf,_he);});},_hb));});return new T2(0,new T(function(){return B(A2(_h4,_hc,_ha));}),_hd);},_hg=function(_hh,_hi){var _hj=E(_hi),_hk=B(_h8(_hh,_hj.a,_hj.b));return new T2(0,_hk.a,_hk.b);},_hl=function(_hm,_hn){var _ho=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hm).c).a);})));})));}),_hp=new T(function(){return B(A2(_dU,E(_hm).a,new T(function(){return B(A2(_9Z,_ho,_L));})));});return new T2(0,new T(function(){return B(A2(_9Z,_ho,_hn));}),_hp);},_hq=function(_hr,_hs){var _ht=B(_hl(_hr,_hs));return new T2(0,_ht.a,_ht.b);},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hv).c).a);})));})));}),_hz=new T(function(){return B(A3(_ad,B(_a5(E(_hv).a)),new T(function(){return B(_88(_hy));}),_hx));});return new T2(0,new T(function(){return B(A2(_88,_hy,_hw));}),_hz);},_hA=function(_hB,_hC){var _hD=E(_hC),_hE=B(_hu(_hB,_hD.a,_hD.b));return new T2(0,_hE.a,_hE.b);},_hF=function(_hG,_hH){var _hI=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hG).c).a);})));})));}),_hJ=new T(function(){return B(A2(_dU,E(_hG).a,new T(function(){return B(A2(_9Z,_hI,_L));})));});return new T2(0,new T(function(){return B(A2(_h6,_hI,_hH));}),_hJ);},_hK=function(_hL,_hM){var _hN=B(_hF(_hL,E(_hM).a));return new T2(0,_hN.a,_hN.b);},_h3=function(_hO){return {_:0,a:function(_fu,_ft){return new F(function(){return _gR(_hO,_fu,_ft);});},b:function(_fu,_ft){return new F(function(){return _gY(_hO,_fu,_ft);});},c:function(_fu,_ft){return new F(function(){return _gA(_hO,_fu,_ft);});},d:function(_ft){return new F(function(){return _hA(_hO,_ft);});},e:function(_ft){return new F(function(){return _hg(_hO,_ft);});},f:function(_ft){return new F(function(){return _hK(_hO,_ft);});},g:function(_ft){return new F(function(){return _hq(_hO,_ft);});}};},_hP=function(_hQ){var _hR=new T(function(){return E(E(_hQ).a);}),_hS=new T3(0,_9X,_a1,new T2(0,_hR,new T(function(){return E(E(_hQ).b);}))),_hT=new T(function(){return B(_fq(new T(function(){return B(_gk(new T(function(){return B(_h3(_hS));}),_hS));}),_hS));}),_hU=new T(function(){return B(_8s(new T(function(){return B(_8q(_hR));})));});return function(_hV){var _hW=E(_hV),_hX=B(A2(_9Z,_hU,_1o)),_hY=B(A2(_9Z,_hU,_9Y));return E(B(_8H(_hT,new T2(0,_hW.a,new T3(0,E(_hX),E(_hY),E(_hY))),new T2(0,_hW.b,new T3(0,E(_hY),E(_hX),E(_hY))),new T2(0,_hW.c,new T3(0,E(_hY),E(_hY),E(_hX))))).b);};},_hZ=new T(function(){return B(_hP(_9t));}),_i0=function(_i1,_i2){var _i3=E(_i2);return (_i3._==0)?__Z:new T2(1,_i1,new T2(1,_i3.a,new T(function(){return B(_i0(_i1,_i3.b));})));},_i4=new T(function(){var _i5=B(A1(_hZ,_92));return new T2(1,_i5.a,new T(function(){return B(_i0(_22,new T2(1,_i5.b,new T2(1,_i5.c,_w))));}));}),_i6=new T1(1,_i4),_i7=new T2(1,_i6,_1S),_i8=new T(function(){return B(unCStr("vec3("));}),_i9=new T1(0,_i8),_ia=new T2(1,_i9,_i7),_ib=new T(function(){return toJSStr(B(_1F(_x,_1l,_ia)));}),_ic=function(_id,_ie){while(1){var _if=E(_id);if(!_if._){return E(_ie);}else{var _ig=_ie+1|0;_id=_if.b;_ie=_ig;continue;}}},_ih=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ii=new T(function(){return B(err(_ih));}),_ij=0,_ik=new T3(0,E(_ij),E(_ij),E(_ij)),_il=new T2(0,E(_ik),E(_ij)),_im=new T(function(){return B(unCStr("Negative exponent"));}),_in=new T(function(){return B(err(_im));}),_io=function(_ip,_iq,_ir){while(1){if(!(_iq%2)){var _is=_ip*_ip,_it=quot(_iq,2);_ip=_is;_iq=_it;continue;}else{var _iu=E(_iq);if(_iu==1){return _ip*_ir;}else{var _is=_ip*_ip,_iv=_ip*_ir;_ip=_is;_iq=quot(_iu-1|0,2);_ir=_iv;continue;}}}},_iw=function(_ix,_iy){while(1){if(!(_iy%2)){var _iz=_ix*_ix,_iA=quot(_iy,2);_ix=_iz;_iy=_iA;continue;}else{var _iB=E(_iy);if(_iB==1){return E(_ix);}else{return new F(function(){return _io(_ix*_ix,quot(_iB-1|0,2),_ix);});}}}},_iC=function(_iD){var _iE=E(_iD);return new F(function(){return Math.log(_iE+(_iE+1)*Math.sqrt((_iE-1)/(_iE+1)));});},_iF=function(_iG){var _iH=E(_iG);return new F(function(){return Math.log(_iH+Math.sqrt(1+_iH*_iH));});},_iI=function(_iJ){var _iK=E(_iJ);return 0.5*Math.log((1+_iK)/(1-_iK));},_iL=function(_iM,_iN){return Math.log(E(_iN))/Math.log(E(_iM));},_iO=3.141592653589793,_iP=function(_iQ){var _iR=E(_iQ);return new F(function(){return _7J(_iR.a,_iR.b);});},_iS=function(_iT){return 1/E(_iT);},_iU=function(_iV){var _iW=E(_iV),_iX=E(_iW);return (_iX==0)?E(_7I):(_iX<=0)? -_iX:E(_iW);},_iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return _j0.a;}else{return new F(function(){return I_toNumber(_j0.a);});}},_j1=function(_j2){return new F(function(){return _iY(_j2);});},_j3=1,_j4=-1,_j5=function(_j6){var _j7=E(_j6);return (_j7<=0)?(_j7>=0)?E(_j7):E(_j4):E(_j3);},_j8=function(_j9,_ja){return E(_j9)-E(_ja);},_jb=function(_jc){return  -E(_jc);},_jd=function(_je,_jf){return E(_je)+E(_jf);},_jg=function(_jh,_ji){return E(_jh)*E(_ji);},_jj={_:0,a:_jd,b:_j8,c:_jg,d:_jb,e:_iU,f:_j5,g:_j1},_jk=function(_jl,_jm){return E(_jl)/E(_jm);},_jn=new T4(0,_jj,_jk,_iS,_iP),_jo=function(_jp){return new F(function(){return Math.acos(E(_jp));});},_jq=function(_jr){return new F(function(){return Math.asin(E(_jr));});},_js=function(_jt){return new F(function(){return Math.atan(E(_jt));});},_ju=function(_jv){return new F(function(){return Math.cos(E(_jv));});},_jw=function(_jx){return new F(function(){return cosh(E(_jx));});},_jy=function(_jz){return new F(function(){return Math.exp(E(_jz));});},_jA=function(_jB){return new F(function(){return Math.log(E(_jB));});},_jC=function(_jD,_jE){return new F(function(){return Math.pow(E(_jD),E(_jE));});},_jF=function(_jG){return new F(function(){return Math.sin(E(_jG));});},_jH=function(_jI){return new F(function(){return sinh(E(_jI));});},_jJ=function(_jK){return new F(function(){return Math.sqrt(E(_jK));});},_jL=function(_jM){return new F(function(){return Math.tan(E(_jM));});},_jN=function(_jO){return new F(function(){return tanh(E(_jO));});},_jP={_:0,a:_jn,b:_iO,c:_jy,d:_jA,e:_jJ,f:_jC,g:_iL,h:_jF,i:_ju,j:_jL,k:_jq,l:_jo,m:_js,n:_jH,o:_jw,p:_jN,q:_iF,r:_iC,s:_iI},_jQ=function(_jR,_jS){return (E(_jR)!=E(_jS))?true:false;},_jT=function(_jU,_jV){return E(_jU)==E(_jV);},_jW=new T2(0,_jT,_jQ),_jX=function(_jY,_jZ){return E(_jY)<E(_jZ);},_k0=function(_k1,_k2){return E(_k1)<=E(_k2);},_k3=function(_k4,_k5){return E(_k4)>E(_k5);},_k6=function(_k7,_k8){return E(_k7)>=E(_k8);},_k9=function(_ka,_kb){var _kc=E(_ka),_kd=E(_kb);return (_kc>=_kd)?(_kc!=_kd)?2:1:0;},_ke=function(_kf,_kg){var _kh=E(_kf),_ki=E(_kg);return (_kh>_ki)?E(_kh):E(_ki);},_kj=function(_kk,_kl){var _km=E(_kk),_kn=E(_kl);return (_km>_kn)?E(_kn):E(_km);},_ko={_:0,a:_jW,b:_k9,c:_jX,d:_k0,e:_k3,f:_k6,g:_ke,h:_kj},_kp="dz",_kq="wy",_kr="wx",_ks="dy",_kt="dx",_ku="t",_kv="a",_kw="r",_kx="ly",_ky="lx",_kz="wz",_kA=0,_kB=function(_kC){var _kD=__new(),_kE=_kD,_kF=function(_kG,_){while(1){var _kH=E(_kG);if(!_kH._){return _kA;}else{var _kI=E(_kH.a),_kJ=__set(_kE,E(_kI.a),E(_kI.b));_kG=_kH.b;continue;}}},_kK=B(_kF(_kC,_));return E(_kE);},_kL=function(_kM,_kN,_kO,_kP,_kQ,_kR,_kS,_kT,_kU){return new F(function(){return _kB(new T2(1,new T2(0,_kr,_kM),new T2(1,new T2(0,_kq,_kN),new T2(1,new T2(0,_kz,_kO),new T2(1,new T2(0,_ky,_kP*_kQ*Math.cos(_kR)),new T2(1,new T2(0,_kx,_kP*_kQ*Math.sin(_kR)),new T2(1,new T2(0,_kw,_kP),new T2(1,new T2(0,_kv,_kQ),new T2(1,new T2(0,_ku,_kR),new T2(1,new T2(0,_kt,_kS),new T2(1,new T2(0,_ks,_kT),new T2(1,new T2(0,_kp,_kU),_w))))))))))));});},_kV=function(_kW){var _kX=E(_kW),_kY=E(_kX.a),_kZ=E(_kX.b),_l0=E(_kX.d);return new F(function(){return _kL(_kY.a,_kY.b,_kY.c,E(_kZ.a),E(_kZ.b),E(_kX.c),_l0.a,_l0.b,_l0.c);});},_l1=function(_l2,_l3){var _l4=E(_l3);return (_l4._==0)?__Z:new T2(1,new T(function(){return B(A1(_l2,_l4.a));}),new T(function(){return B(_l1(_l2,_l4.b));}));},_l5=function(_l6,_l7,_l8){var _l9=__lst2arr(B(_l1(_kV,new T2(1,_l6,new T2(1,_l7,new T2(1,_l8,_w))))));return E(_l9);},_la=function(_lb){var _lc=E(_lb);return new F(function(){return _l5(_lc.a,_lc.b,_lc.c);});},_ld=new T2(0,_jP,_ko),_le=function(_lf,_lg,_lh,_li,_lj,_lk,_ll){var _lm=B(_8s(B(_8q(_lf)))),_ln=new T(function(){return B(A3(_86,_lm,new T(function(){return B(A3(_8u,_lm,_lg,_lj));}),new T(function(){return B(A3(_8u,_lm,_lh,_lk));})));});return new F(function(){return A3(_86,_lm,_ln,new T(function(){return B(A3(_8u,_lm,_li,_ll));}));});},_lo=function(_lp,_lq,_lr,_ls){var _lt=B(_8q(_lp)),_lu=new T(function(){return B(A2(_8F,_lp,new T(function(){return B(_le(_lp,_lq,_lr,_ls,_lq,_lr,_ls));})));});return new T3(0,B(A3(_a9,_lt,_lq,_lu)),B(A3(_a9,_lt,_lr,_lu)),B(A3(_a9,_lt,_ls,_lu)));},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC){var _lD=B(_8u(_lw));return new T3(0,B(A1(B(A1(_lD,_lx)),_lA)),B(A1(B(A1(_lD,_ly)),_lB)),B(A1(B(A1(_lD,_lz)),_lC)));},_lE=function(_lF,_lG,_lH,_lI,_lJ,_lK,_lL){var _lM=B(_86(_lF));return new T3(0,B(A1(B(A1(_lM,_lG)),_lJ)),B(A1(B(A1(_lM,_lH)),_lK)),B(A1(B(A1(_lM,_lI)),_lL)));},_lN=function(_lO,_lP){var _lQ=new T(function(){return E(E(_lO).a);}),_lR=new T(function(){return B(A2(_hP,new T2(0,_lQ,new T(function(){return E(E(_lO).b);})),_lP));}),_lS=new T(function(){var _lT=E(_lR),_lU=B(_lo(_lQ,_lT.a,_lT.b,_lT.c));return new T3(0,E(_lU.a),E(_lU.b),E(_lU.c));}),_lV=new T(function(){var _lW=E(_lP),_lX=_lW.a,_lY=_lW.b,_lZ=_lW.c,_m0=E(_lS),_m1=B(_8q(_lQ)),_m2=new T(function(){return B(A2(_8F,_lQ,new T(function(){var _m3=E(_lR),_m4=_m3.a,_m5=_m3.b,_m6=_m3.c;return B(_le(_lQ,_m4,_m5,_m6,_m4,_m5,_m6));})));}),_m7=B(A3(_a9,_m1,new T(function(){return B(_8H(_lQ,_lX,_lY,_lZ));}),_m2)),_m8=B(_8s(_m1)),_m9=B(_lv(_m8,_m0.a,_m0.b,_m0.c,_m7,_m7,_m7)),_ma=B(_88(_m8)),_mb=B(_lE(_m8,_lX,_lY,_lZ,B(A1(_ma,_m9.a)),B(A1(_ma,_m9.b)),B(A1(_ma,_m9.c))));return new T3(0,E(_mb.a),E(_mb.b),E(_mb.c));});return new T2(0,_lV,_lS);},_mc=function(_md){return E(E(_md).a);},_me=function(_mf,_mg,_mh,_mi,_mj,_mk,_ml){var _mm=B(_le(_mf,_mj,_mk,_ml,_mg,_mh,_mi)),_mn=B(_8s(B(_8q(_mf)))),_mo=B(_lv(_mn,_mj,_mk,_ml,_mm,_mm,_mm)),_mp=B(_88(_mn));return new F(function(){return _lE(_mn,_mg,_mh,_mi,B(A1(_mp,_mo.a)),B(A1(_mp,_mo.b)),B(A1(_mp,_mo.c)));});},_mq=function(_mr){return E(E(_mr).a);},_ms=function(_mt,_mu,_mv,_mw){var _mx=new T(function(){var _my=E(_mw),_mz=E(_mv),_mA=B(_me(_mt,_my.a,_my.b,_my.c,_mz.a,_mz.b,_mz.c));return new T3(0,E(_mA.a),E(_mA.b),E(_mA.c));}),_mB=new T(function(){return B(A2(_8F,_mt,new T(function(){var _mC=E(_mx),_mD=_mC.a,_mE=_mC.b,_mF=_mC.c;return B(_le(_mt,_mD,_mE,_mF,_mD,_mE,_mF));})));});if(!B(A3(_mq,B(_mc(_mu)),_mB,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_mt)))),_9Y));})))){var _mG=E(_mx),_mH=B(_lo(_mt,_mG.a,_mG.b,_mG.c)),_mI=B(A2(_8F,_mt,new T(function(){var _mJ=E(_mw),_mK=_mJ.a,_mL=_mJ.b,_mM=_mJ.c;return B(_le(_mt,_mK,_mL,_mM,_mK,_mL,_mM));}))),_mN=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_mt));})));})));return new T3(0,B(A1(B(A1(_mN,_mH.a)),_mI)),B(A1(B(A1(_mN,_mH.b)),_mI)),B(A1(B(A1(_mN,_mH.c)),_mI)));}else{var _mO=B(A2(_9Z,B(_8s(B(_8q(_mt)))),_9Y));return new T3(0,_mO,_mO,_mO);}},_mP=new T(function(){var _mQ=eval("angleCount"),_mR=Number(_mQ);return jsTrunc(_mR);}),_mS=new T(function(){return E(_mP);}),_mT=new T(function(){return B(unCStr(": empty list"));}),_mU=new T(function(){return B(unCStr("Prelude."));}),_mV=function(_mW){return new F(function(){return err(B(_n(_mU,new T(function(){return B(_n(_mW,_mT));},1))));});},_mX=new T(function(){return B(unCStr("head"));}),_mY=new T(function(){return B(_mV(_mX));}),_mZ=function(_n0,_n1,_n2){var _n3=E(_n0);if(!_n3._){return __Z;}else{var _n4=E(_n1);if(!_n4._){return __Z;}else{var _n5=_n4.a,_n6=E(_n2);if(!_n6._){return __Z;}else{var _n7=E(_n6.a),_n8=_n7.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_n3.a),E(_n5),E(_n8));}),new T2(1,new T(function(){return new T3(0,E(_n5),E(_n8),E(_n7.b));}),_w)),new T(function(){return B(_mZ(_n3.b,_n4.b,_n6.b));},1));});}}}},_n9=new T(function(){return B(unCStr("tail"));}),_na=new T(function(){return B(_mV(_n9));}),_nb=function(_nc,_nd){var _ne=E(_nc);if(!_ne._){return __Z;}else{var _nf=E(_nd);return (_nf._==0)?__Z:new T2(1,new T2(0,_ne.a,_nf.a),new T(function(){return B(_nb(_ne.b,_nf.b));}));}},_ng=function(_nh,_ni){var _nj=E(_nh);if(!_nj._){return __Z;}else{var _nk=E(_ni);if(!_nk._){return __Z;}else{var _nl=E(_nj.a),_nm=_nl.b,_nn=E(_nk.a).b,_no=new T(function(){var _np=new T(function(){return B(_nb(_nn,new T(function(){var _nq=E(_nn);if(!_nq._){return E(_na);}else{return E(_nq.b);}},1)));},1);return B(_mZ(_nm,new T(function(){var _nr=E(_nm);if(!_nr._){return E(_na);}else{return E(_nr.b);}},1),_np));});return new F(function(){return _n(new T2(1,new T(function(){var _ns=E(_nm);if(!_ns._){return E(_mY);}else{var _nt=E(_nn);if(!_nt._){return E(_mY);}else{return new T3(0,E(_nl.a),E(_ns.a),E(_nt.a));}}}),_no),new T(function(){return B(_ng(_nj.b,_nk.b));},1));});}}},_nu=new T(function(){return E(_mS)-1;}),_nv=new T1(0,1),_nw=function(_nx,_ny){var _nz=E(_ny),_nA=new T(function(){var _nB=B(_8s(_nx)),_nC=B(_nw(_nx,B(A3(_86,_nB,_nz,new T(function(){return B(A2(_9Z,_nB,_nv));})))));return new T2(1,_nC.a,_nC.b);});return new T2(0,_nz,_nA);},_nD=function(_nE){return E(E(_nE).d);},_nF=new T1(0,2),_nG=function(_nH,_nI){var _nJ=E(_nI);if(!_nJ._){return __Z;}else{var _nK=_nJ.a;return (!B(A1(_nH,_nK)))?__Z:new T2(1,_nK,new T(function(){return B(_nG(_nH,_nJ.b));}));}},_nL=function(_nM,_nN,_nO,_nP){var _nQ=B(_nw(_nN,_nO)),_nR=new T(function(){var _nS=B(_8s(_nN)),_nT=new T(function(){return B(A3(_a9,_nN,new T(function(){return B(A2(_9Z,_nS,_nv));}),new T(function(){return B(A2(_9Z,_nS,_nF));})));});return B(A3(_86,_nS,_nP,_nT));});return new F(function(){return _nG(function(_nU){return new F(function(){return A3(_nD,_nM,_nU,_nR);});},new T2(1,_nQ.a,_nQ.b));});},_nV=new T(function(){return B(_nL(_ko,_jn,_ij,_nu));}),_nW=function(_nX,_nY){while(1){var _nZ=E(_nX);if(!_nZ._){return E(_nY);}else{_nX=_nZ.b;_nY=_nZ.a;continue;}}},_o0=new T(function(){return B(unCStr("last"));}),_o1=new T(function(){return B(_mV(_o0));}),_o2=function(_o3){return new F(function(){return _nW(_o3,_o1);});},_o4=function(_o5){return new F(function(){return _o2(E(_o5).b);});},_o6=new T(function(){var _o7=eval("proceedCount"),_o8=Number(_o7);return jsTrunc(_o8);}),_o9=new T(function(){return E(_o6);}),_oa=1,_ob=new T(function(){return B(_nL(_ko,_jn,_oa,_o9));}),_oc=function(_od,_oe,_of,_og,_oh,_oi,_oj,_ok,_ol,_om,_on,_oo,_op,_oq){var _or=new T(function(){var _os=new T(function(){var _ot=E(_om),_ou=E(_oq),_ov=E(_op),_ow=E(_on),_ox=E(_oo),_oy=E(_ol);return new T3(0,_ot*_ou-_ov*_ow,_ow*_ox-_ou*_oy,_oy*_ov-_ox*_ot);}),_oz=function(_oA){var _oB=new T(function(){var _oC=E(_oA)/E(_mS);return (_oC+_oC)*3.141592653589793;}),_oD=new T(function(){return B(A1(_od,_oB));}),_oE=new T(function(){var _oF=new T(function(){var _oG=E(_oD)/E(_o9);return new T3(0,E(_oG),E(_oG),E(_oG));}),_oH=function(_oI,_oJ){var _oK=E(_oI);if(!_oK._){return new T2(0,_w,_oJ);}else{var _oL=new T(function(){var _oM=B(_lN(_ld,new T(function(){var _oN=E(_oJ),_oO=E(_oN.a),_oP=E(_oN.b),_oQ=E(_oF);return new T3(0,E(_oO.a)+E(_oP.a)*E(_oQ.a),E(_oO.b)+E(_oP.b)*E(_oQ.b),E(_oO.c)+E(_oP.c)*E(_oQ.c));}))),_oR=_oM.a,_oS=new T(function(){var _oT=E(_oM.b),_oU=E(E(_oJ).b),_oV=B(_me(_jP,_oU.a,_oU.b,_oU.c,_oT.a,_oT.b,_oT.c)),_oW=B(_lo(_jP,_oV.a,_oV.b,_oV.c));return new T3(0,E(_oW.a),E(_oW.b),E(_oW.c));});return new T2(0,new T(function(){var _oX=E(_oD),_oY=E(_oB);return new T4(0,E(_oR),E(new T2(0,E(_oK.a)/E(_o9),E(_oX))),E(_oY),E(_oS));}),new T2(0,_oR,_oS));}),_oZ=new T(function(){var _p0=B(_oH(_oK.b,new T(function(){return E(E(_oL).b);})));return new T2(0,_p0.a,_p0.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oL).a);}),new T(function(){return E(E(_oZ).a);})),new T(function(){return E(E(_oZ).b);}));}},_p1=function(_p2,_p3,_p4,_p5,_p6){var _p7=E(_p2);if(!_p7._){return new T2(0,_w,new T2(0,new T3(0,E(_p3),E(_p4),E(_p5)),_p6));}else{var _p8=new T(function(){var _p9=B(_lN(_ld,new T(function(){var _pa=E(_p6),_pb=E(_oF);return new T3(0,E(_p3)+E(_pa.a)*E(_pb.a),E(_p4)+E(_pa.b)*E(_pb.b),E(_p5)+E(_pa.c)*E(_pb.c));}))),_pc=_p9.a,_pd=new T(function(){var _pe=E(_p9.b),_pf=E(_p6),_pg=B(_me(_jP,_pf.a,_pf.b,_pf.c,_pe.a,_pe.b,_pe.c)),_ph=B(_lo(_jP,_pg.a,_pg.b,_pg.c));return new T3(0,E(_ph.a),E(_ph.b),E(_ph.c));});return new T2(0,new T(function(){var _pi=E(_oD),_pj=E(_oB);return new T4(0,E(_pc),E(new T2(0,E(_p7.a)/E(_o9),E(_pi))),E(_pj),E(_pd));}),new T2(0,_pc,_pd));}),_pk=new T(function(){var _pl=B(_oH(_p7.b,new T(function(){return E(E(_p8).b);})));return new T2(0,_pl.a,_pl.b);});return new T2(0,new T2(1,new T(function(){return E(E(_p8).a);}),new T(function(){return E(E(_pk).a);})),new T(function(){return E(E(_pk).b);}));}};return E(B(_p1(_ob,_og,_oh,_oi,new T(function(){var _pm=E(_os),_pn=E(_oB)+_oj,_po=Math.cos(_pn),_pp=Math.sin(_pn);return new T3(0,E(_ol)*_po+E(_pm.a)*_pp,E(_om)*_po+E(_pm.b)*_pp,E(_on)*_po+E(_pm.c)*_pp);}))).a);});return new T2(0,new T(function(){var _pq=E(_oD),_pr=E(_oB);return new T4(0,E(new T3(0,E(_og),E(_oh),E(_oi))),E(new T2(0,E(_ij),E(_pq))),E(_pr),E(_ik));}),_oE);};return B(_l1(_oz,_nV));}),_ps=new T(function(){var _pt=new T(function(){var _pu=B(_n(_or,new T2(1,new T(function(){var _pv=E(_or);if(!_pv._){return E(_mY);}else{return E(_pv.a);}}),_w)));if(!_pu._){return E(_na);}else{return E(_pu.b);}},1);return B(_ng(_or,_pt));});return new T2(0,_ps,new T(function(){return B(_l1(_o4,_or));}));},_pw=function(_px,_py,_pz,_pA,_pB,_pC,_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_pL,_pM,_pN){var _pO=B(_lN(_ld,new T3(0,E(_pA),E(_pB),E(_pC)))),_pP=_pO.b,_pQ=E(_pO.a),_pR=B(_ms(_jP,_ko,_pP,new T3(0,E(_pE),E(_pF),E(_pG)))),_pS=E(_pP),_pT=_pS.a,_pU=_pS.b,_pV=_pS.c,_pW=B(_me(_jP,_pI,_pJ,_pK,_pT,_pU,_pV)),_pX=B(_lo(_jP,_pW.a,_pW.b,_pW.c)),_pY=_pX.a,_pZ=_pX.b,_q0=_pX.c,_q1=E(_pD),_q2=new T2(0,E(new T3(0,E(_pR.a),E(_pR.b),E(_pR.c))),E(_pH)),_q3=B(_oc(_px,_py,_pz,_pQ.a,_pQ.b,_pQ.c,_q1,_q2,_pY,_pZ,_q0,_pT,_pU,_pV)),_q4=__lst2arr(B(_l1(_la,_q3.a))),_q5=__lst2arr(B(_l1(_kV,_q3.b)));return {_:0,a:_px,b:_py,c:_pz,d:new T2(0,E(_pQ),E(_q1)),e:_q2,f:new T3(0,E(_pY),E(_pZ),E(_q0)),g:_pS,h:_q4,i:_q5};},_q6=function(_q7){var _q8=E(_q7);return new T3(0,E(_q8.c), -E(_q8.b), -E(_q8.a));},_q9=new T(function(){return 6.283185307179586/E(_mS);}),_qa=function(_){return new F(function(){return __jsNull();});},_qb=function(_qc){var _qd=B(A1(_qc,_));return E(_qd);},_qe=new T(function(){return B(_qb(_qa));}),_qf=function(_qg,_qh,_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs){var _qt=function(_qu){var _qv=E(_q9),_qw=2+_qu|0,_qx=_qw-1|0,_qy=(2+_qu)*(1+_qu),_qz=E(_nV);if(!_qz._){return _qv*0;}else{var _qA=_qz.a,_qB=_qz.b,_qC=B(A1(_qg,new T(function(){return 6.283185307179586*E(_qA)/E(_mS);}))),_qD=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_qA)+1)/E(_mS);})));if(_qC!=_qD){if(_qw>=0){var _qE=E(_qw);if(!_qE){var _qF=function(_qG,_qH){while(1){var _qI=B((function(_qJ,_qK){var _qL=E(_qJ);if(!_qL._){return E(_qK);}else{var _qM=_qL.a,_qN=_qL.b,_qO=B(A1(_qg,new T(function(){return 6.283185307179586*E(_qM)/E(_mS);}))),_qP=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_qM)+1)/E(_mS);})));if(_qO!=_qP){var _qQ=_qK+0/(_qO-_qP)/_qy;_qG=_qN;_qH=_qQ;return __continue;}else{if(_qx>=0){var _qR=E(_qx);if(!_qR){var _qQ=_qK+_qw/_qy;_qG=_qN;_qH=_qQ;return __continue;}else{var _qQ=_qK+_qw*B(_iw(_qO,_qR))/_qy;_qG=_qN;_qH=_qQ;return __continue;}}else{return E(_in);}}}})(_qG,_qH));if(_qI!=__continue){return _qI;}}};return _qv*B(_qF(_qB,0/(_qC-_qD)/_qy));}else{var _qS=function(_qT,_qU){while(1){var _qV=B((function(_qW,_qX){var _qY=E(_qW);if(!_qY._){return E(_qX);}else{var _qZ=_qY.a,_r0=_qY.b,_r1=B(A1(_qg,new T(function(){return 6.283185307179586*E(_qZ)/E(_mS);}))),_r2=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_qZ)+1)/E(_mS);})));if(_r1!=_r2){if(_qE>=0){var _r3=_qX+(B(_iw(_r1,_qE))-B(_iw(_r2,_qE)))/(_r1-_r2)/_qy;_qT=_r0;_qU=_r3;return __continue;}else{return E(_in);}}else{if(_qx>=0){var _r4=E(_qx);if(!_r4){var _r3=_qX+_qw/_qy;_qT=_r0;_qU=_r3;return __continue;}else{var _r3=_qX+_qw*B(_iw(_r1,_r4))/_qy;_qT=_r0;_qU=_r3;return __continue;}}else{return E(_in);}}}})(_qT,_qU));if(_qV!=__continue){return _qV;}}};return _qv*B(_qS(_qB,(B(_iw(_qC,_qE))-B(_iw(_qD,_qE)))/(_qC-_qD)/_qy));}}else{return E(_in);}}else{if(_qx>=0){var _r5=E(_qx);if(!_r5){var _r6=function(_r7,_r8){while(1){var _r9=B((function(_ra,_rb){var _rc=E(_ra);if(!_rc._){return E(_rb);}else{var _rd=_rc.a,_re=_rc.b,_rf=B(A1(_qg,new T(function(){return 6.283185307179586*E(_rd)/E(_mS);}))),_rg=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_rd)+1)/E(_mS);})));if(_rf!=_rg){if(_qw>=0){var _rh=E(_qw);if(!_rh){var _ri=_rb+0/(_rf-_rg)/_qy;_r7=_re;_r8=_ri;return __continue;}else{var _ri=_rb+(B(_iw(_rf,_rh))-B(_iw(_rg,_rh)))/(_rf-_rg)/_qy;_r7=_re;_r8=_ri;return __continue;}}else{return E(_in);}}else{var _ri=_rb+_qw/_qy;_r7=_re;_r8=_ri;return __continue;}}})(_r7,_r8));if(_r9!=__continue){return _r9;}}};return _qv*B(_r6(_qB,_qw/_qy));}else{var _rj=function(_rk,_rl){while(1){var _rm=B((function(_rn,_ro){var _rp=E(_rn);if(!_rp._){return E(_ro);}else{var _rq=_rp.a,_rr=_rp.b,_rs=B(A1(_qg,new T(function(){return 6.283185307179586*E(_rq)/E(_mS);}))),_rt=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_rq)+1)/E(_mS);})));if(_rs!=_rt){if(_qw>=0){var _ru=E(_qw);if(!_ru){var _rv=_ro+0/(_rs-_rt)/_qy;_rk=_rr;_rl=_rv;return __continue;}else{var _rv=_ro+(B(_iw(_rs,_ru))-B(_iw(_rt,_ru)))/(_rs-_rt)/_qy;_rk=_rr;_rl=_rv;return __continue;}}else{return E(_in);}}else{if(_r5>=0){var _rv=_ro+_qw*B(_iw(_rs,_r5))/_qy;_rk=_rr;_rl=_rv;return __continue;}else{return E(_in);}}}})(_rk,_rl));if(_rm!=__continue){return _rm;}}};return _qv*B(_rj(_qB,_qw*B(_iw(_qC,_r5))/_qy));}}else{return E(_in);}}}},_rw=E(_qe),_rx=1/(B(_qt(1))*_qh);return new F(function(){return _pw(_qg,_q6,new T2(0,E(new T3(0,E(_rx),E(_rx),E(_rx))),1/(B(_qt(3))*_qh)),_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_ik,_rw,_rw);});},_ry=1,_rz=function(_rA){return E(_ik);},_rB=function(_rC){var _rD=I_decodeDouble(_rC);return new T2(0,new T1(1,_rD.b),_rD.a);},_rE=function(_rF){return new T1(0,_rF);},_rG=function(_rH){var _rI=hs_intToInt64(2147483647),_rJ=hs_leInt64(_rH,_rI);if(!_rJ){return new T1(1,I_fromInt64(_rH));}else{var _rK=hs_intToInt64(-2147483648),_rL=hs_geInt64(_rH,_rK);if(!_rL){return new T1(1,I_fromInt64(_rH));}else{var _rM=hs_int64ToInt(_rH);return new F(function(){return _rE(_rM);});}}},_rN=new T(function(){var _rO=newByteArr(256),_rP=_rO,_=_rP["v"]["i8"][0]=8,_rQ=function(_rR,_rS,_rT,_){while(1){if(_rT>=256){if(_rR>=256){return E(_);}else{var _rU=imul(2,_rR)|0,_rV=_rS+1|0,_rW=_rR;_rR=_rU;_rS=_rV;_rT=_rW;continue;}}else{var _=_rP["v"]["i8"][_rT]=_rS,_rW=_rT+_rR|0;_rT=_rW;continue;}}},_=B(_rQ(2,0,1,_));return _rP;}),_rX=function(_rY,_rZ){var _s0=hs_int64ToInt(_rY),_s1=E(_rN),_s2=_s1["v"]["i8"][(255&_s0>>>0)>>>0&4294967295];if(_rZ>_s2){if(_s2>=8){var _s3=hs_uncheckedIShiftRA64(_rY,8),_s4=function(_s5,_s6){while(1){var _s7=B((function(_s8,_s9){var _sa=hs_int64ToInt(_s8),_sb=_s1["v"]["i8"][(255&_sa>>>0)>>>0&4294967295];if(_s9>_sb){if(_sb>=8){var _sc=hs_uncheckedIShiftRA64(_s8,8),_sd=_s9-8|0;_s5=_sc;_s6=_sd;return __continue;}else{return new T2(0,new T(function(){var _se=hs_uncheckedIShiftRA64(_s8,_sb);return B(_rG(_se));}),_s9-_sb|0);}}else{return new T2(0,new T(function(){var _sf=hs_uncheckedIShiftRA64(_s8,_s9);return B(_rG(_sf));}),0);}})(_s5,_s6));if(_s7!=__continue){return _s7;}}};return new F(function(){return _s4(_s3,_rZ-8|0);});}else{return new T2(0,new T(function(){var _sg=hs_uncheckedIShiftRA64(_rY,_s2);return B(_rG(_sg));}),_rZ-_s2|0);}}else{return new T2(0,new T(function(){var _sh=hs_uncheckedIShiftRA64(_rY,_rZ);return B(_rG(_sh));}),0);}},_si=function(_sj){var _sk=hs_intToInt64(_sj);return E(_sk);},_sl=function(_sm){var _sn=E(_sm);if(!_sn._){return new F(function(){return _si(_sn.a);});}else{return new F(function(){return I_toInt64(_sn.a);});}},_so=function(_sp){return I_toInt(_sp)>>>0;},_sq=function(_sr){var _ss=E(_sr);if(!_ss._){return _ss.a>>>0;}else{return new F(function(){return _so(_ss.a);});}},_st=function(_su){var _sv=B(_rB(_su)),_sw=_sv.a,_sx=_sv.b;if(_sx<0){var _sy=function(_sz){if(!_sz){return new T2(0,E(_sw),B(_52(_3k, -_sx)));}else{var _sA=B(_rX(B(_sl(_sw)), -_sx));return new T2(0,E(_sA.a),B(_52(_3k,_sA.b)));}};if(!((B(_sq(_sw))&1)>>>0)){return new F(function(){return _sy(1);});}else{return new F(function(){return _sy(0);});}}else{return new T2(0,B(_52(_sw,_sx)),_3k);}},_sB=function(_sC){var _sD=B(_st(E(_sC)));return new T2(0,E(_sD.a),E(_sD.b));},_sE=new T3(0,_jj,_ko,_sB),_sF=function(_sG){return E(E(_sG).a);},_sH=function(_sI){return E(E(_sI).a);},_sJ=function(_sK,_sL){if(_sK<=_sL){var _sM=function(_sN){return new T2(1,_sN,new T(function(){if(_sN!=_sL){return B(_sM(_sN+1|0));}else{return __Z;}}));};return new F(function(){return _sM(_sK);});}else{return __Z;}},_sO=function(_sP){return new F(function(){return _sJ(E(_sP),2147483647);});},_sQ=function(_sR,_sS,_sT){if(_sT<=_sS){var _sU=new T(function(){var _sV=_sS-_sR|0,_sW=function(_sX){return (_sX>=(_sT-_sV|0))?new T2(1,_sX,new T(function(){return B(_sW(_sX+_sV|0));})):new T2(1,_sX,_w);};return B(_sW(_sS));});return new T2(1,_sR,_sU);}else{return (_sT<=_sR)?new T2(1,_sR,_w):__Z;}},_sY=function(_sZ,_t0,_t1){if(_t1>=_t0){var _t2=new T(function(){var _t3=_t0-_sZ|0,_t4=function(_t5){return (_t5<=(_t1-_t3|0))?new T2(1,_t5,new T(function(){return B(_t4(_t5+_t3|0));})):new T2(1,_t5,_w);};return B(_t4(_t0));});return new T2(1,_sZ,_t2);}else{return (_t1>=_sZ)?new T2(1,_sZ,_w):__Z;}},_t6=function(_t7,_t8){if(_t8<_t7){return new F(function(){return _sQ(_t7,_t8,-2147483648);});}else{return new F(function(){return _sY(_t7,_t8,2147483647);});}},_t9=function(_ta,_tb){return new F(function(){return _t6(E(_ta),E(_tb));});},_tc=function(_td,_te,_tf){if(_te<_td){return new F(function(){return _sQ(_td,_te,_tf);});}else{return new F(function(){return _sY(_td,_te,_tf);});}},_tg=function(_th,_ti,_tj){return new F(function(){return _tc(E(_th),E(_ti),E(_tj));});},_tk=function(_tl,_tm){return new F(function(){return _sJ(E(_tl),E(_tm));});},_tn=function(_to){return E(_to);},_tp=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tq=new T(function(){return B(err(_tp));}),_tr=function(_ts){var _tt=E(_ts);return (_tt==(-2147483648))?E(_tq):_tt-1|0;},_tu=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tv=new T(function(){return B(err(_tu));}),_tw=function(_tx){var _ty=E(_tx);return (_ty==2147483647)?E(_tv):_ty+1|0;},_tz={_:0,a:_tw,b:_tr,c:_tn,d:_tn,e:_sO,f:_t9,g:_tk,h:_tg},_tA=function(_tB,_tC){if(_tB<=0){if(_tB>=0){return new F(function(){return quot(_tB,_tC);});}else{if(_tC<=0){return new F(function(){return quot(_tB,_tC);});}else{return quot(_tB+1|0,_tC)-1|0;}}}else{if(_tC>=0){if(_tB>=0){return new F(function(){return quot(_tB,_tC);});}else{if(_tC<=0){return new F(function(){return quot(_tB,_tC);});}else{return quot(_tB+1|0,_tC)-1|0;}}}else{return quot(_tB-1|0,_tC)-1|0;}}},_tD=0,_tE=new T(function(){return B(_4p(_tD));}),_tF=new T(function(){return die(_tE);}),_tG=function(_tH,_tI){var _tJ=E(_tI);switch(_tJ){case -1:var _tK=E(_tH);if(_tK==(-2147483648)){return E(_tF);}else{return new F(function(){return _tA(_tK,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tA(_tH,_tJ);});}},_tL=function(_tM,_tN){return new F(function(){return _tG(E(_tM),E(_tN));});},_tO=0,_tP=new T2(0,_tF,_tO),_tQ=function(_tR,_tS){var _tT=E(_tR),_tU=E(_tS);switch(_tU){case -1:var _tV=E(_tT);if(_tV==(-2147483648)){return E(_tP);}else{if(_tV<=0){if(_tV>=0){var _tW=quotRemI(_tV,-1);return new T2(0,_tW.a,_tW.b);}else{var _tX=quotRemI(_tV,-1);return new T2(0,_tX.a,_tX.b);}}else{var _tY=quotRemI(_tV-1|0,-1);return new T2(0,_tY.a-1|0,(_tY.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_tT<=0){if(_tT>=0){var _tZ=quotRemI(_tT,_tU);return new T2(0,_tZ.a,_tZ.b);}else{if(_tU<=0){var _u0=quotRemI(_tT,_tU);return new T2(0,_u0.a,_u0.b);}else{var _u1=quotRemI(_tT+1|0,_tU);return new T2(0,_u1.a-1|0,(_u1.b+_tU|0)-1|0);}}}else{if(_tU>=0){if(_tT>=0){var _u2=quotRemI(_tT,_tU);return new T2(0,_u2.a,_u2.b);}else{if(_tU<=0){var _u3=quotRemI(_tT,_tU);return new T2(0,_u3.a,_u3.b);}else{var _u4=quotRemI(_tT+1|0,_tU);return new T2(0,_u4.a-1|0,(_u4.b+_tU|0)-1|0);}}}else{var _u5=quotRemI(_tT-1|0,_tU);return new T2(0,_u5.a-1|0,(_u5.b+_tU|0)+1|0);}}}},_u6=function(_u7,_u8){var _u9=_u7%_u8;if(_u7<=0){if(_u7>=0){return E(_u9);}else{if(_u8<=0){return E(_u9);}else{var _ua=E(_u9);return (_ua==0)?0:_ua+_u8|0;}}}else{if(_u8>=0){if(_u7>=0){return E(_u9);}else{if(_u8<=0){return E(_u9);}else{var _ub=E(_u9);return (_ub==0)?0:_ub+_u8|0;}}}else{var _uc=E(_u9);return (_uc==0)?0:_uc+_u8|0;}}},_ud=function(_ue,_uf){var _ug=E(_uf);switch(_ug){case -1:return E(_tO);case 0:return E(_4t);default:return new F(function(){return _u6(E(_ue),_ug);});}},_uh=function(_ui,_uj){var _uk=E(_ui),_ul=E(_uj);switch(_ul){case -1:var _um=E(_uk);if(_um==(-2147483648)){return E(_tF);}else{return new F(function(){return quot(_um,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_uk,_ul);});}},_un=function(_uo,_up){var _uq=E(_uo),_ur=E(_up);switch(_ur){case -1:var _us=E(_uq);if(_us==(-2147483648)){return E(_tP);}else{var _ut=quotRemI(_us,-1);return new T2(0,_ut.a,_ut.b);}break;case 0:return E(_4t);default:var _uu=quotRemI(_uq,_ur);return new T2(0,_uu.a,_uu.b);}},_uv=function(_uw,_ux){var _uy=E(_ux);switch(_uy){case -1:return E(_tO);case 0:return E(_4t);default:return E(_uw)%_uy;}},_uz=function(_uA){return new F(function(){return _rE(E(_uA));});},_uB=function(_uC){return new T2(0,E(B(_rE(E(_uC)))),E(_nv));},_uD=function(_uE,_uF){return imul(E(_uE),E(_uF))|0;},_uG=function(_uH,_uI){return E(_uH)+E(_uI)|0;},_uJ=function(_uK,_uL){return E(_uK)-E(_uL)|0;},_uM=function(_uN){var _uO=E(_uN);return (_uO<0)? -_uO:E(_uO);},_uP=function(_uQ){return new F(function(){return _4G(_uQ);});},_uR=function(_uS){return  -E(_uS);},_uT=-1,_uU=0,_uV=1,_uW=function(_uX){var _uY=E(_uX);return (_uY>=0)?(E(_uY)==0)?E(_uU):E(_uV):E(_uT);},_uZ={_:0,a:_uG,b:_uJ,c:_uD,d:_uR,e:_uM,f:_uW,g:_uP},_v0=function(_v1,_v2){return E(_v1)==E(_v2);},_v3=function(_v4,_v5){return E(_v4)!=E(_v5);},_v6=new T2(0,_v0,_v3),_v7=function(_v8,_v9){var _va=E(_v8),_vb=E(_v9);return (_va>_vb)?E(_va):E(_vb);},_vc=function(_vd,_ve){var _vf=E(_vd),_vg=E(_ve);return (_vf>_vg)?E(_vg):E(_vf);},_vh=function(_vi,_vj){return (_vi>=_vj)?(_vi!=_vj)?2:1:0;},_vk=function(_vl,_vm){return new F(function(){return _vh(E(_vl),E(_vm));});},_vn=function(_vo,_vp){return E(_vo)>=E(_vp);},_vq=function(_vr,_vs){return E(_vr)>E(_vs);},_vt=function(_vu,_vv){return E(_vu)<=E(_vv);},_vw=function(_vx,_vy){return E(_vx)<E(_vy);},_vz={_:0,a:_v6,b:_vk,c:_vw,d:_vt,e:_vq,f:_vn,g:_v7,h:_vc},_vA=new T3(0,_uZ,_vz,_uB),_vB={_:0,a:_vA,b:_tz,c:_uh,d:_uv,e:_tL,f:_ud,g:_un,h:_tQ,i:_uz},_vC=new T1(0,2),_vD=function(_vE,_vF){while(1){var _vG=E(_vE);if(!_vG._){var _vH=_vG.a,_vI=E(_vF);if(!_vI._){var _vJ=_vI.a;if(!(imul(_vH,_vJ)|0)){return new T1(0,imul(_vH,_vJ)|0);}else{_vE=new T1(1,I_fromInt(_vH));_vF=new T1(1,I_fromInt(_vJ));continue;}}else{_vE=new T1(1,I_fromInt(_vH));_vF=_vI;continue;}}else{var _vK=E(_vF);if(!_vK._){_vE=_vG;_vF=new T1(1,I_fromInt(_vK.a));continue;}else{return new T1(1,I_mul(_vG.a,_vK.a));}}}},_vL=function(_vM,_vN,_vO){while(1){if(!(_vN%2)){var _vP=B(_vD(_vM,_vM)),_vQ=quot(_vN,2);_vM=_vP;_vN=_vQ;continue;}else{var _vR=E(_vN);if(_vR==1){return new F(function(){return _vD(_vM,_vO);});}else{var _vP=B(_vD(_vM,_vM)),_vS=B(_vD(_vM,_vO));_vM=_vP;_vN=quot(_vR-1|0,2);_vO=_vS;continue;}}}},_vT=function(_vU,_vV){while(1){if(!(_vV%2)){var _vW=B(_vD(_vU,_vU)),_vX=quot(_vV,2);_vU=_vW;_vV=_vX;continue;}else{var _vY=E(_vV);if(_vY==1){return E(_vU);}else{return new F(function(){return _vL(B(_vD(_vU,_vU)),quot(_vY-1|0,2),_vU);});}}}},_vZ=function(_w0){return E(E(_w0).b);},_w1=function(_w2){return E(E(_w2).c);},_w3=new T1(0,0),_w4=function(_w5){return E(E(_w5).d);},_w6=function(_w7,_w8){var _w9=B(_sF(_w7)),_wa=new T(function(){return B(_sH(_w9));}),_wb=new T(function(){return B(A3(_w4,_w7,_w8,new T(function(){return B(A2(_9Z,_wa,_nF));})));});return new F(function(){return A3(_mq,B(_mc(B(_vZ(_w9)))),_wb,new T(function(){return B(A2(_9Z,_wa,_w3));}));});},_wc=new T(function(){return B(unCStr("Negative exponent"));}),_wd=new T(function(){return B(err(_wc));}),_we=function(_wf){return E(E(_wf).c);},_wg=function(_wh,_wi,_wj,_wk){var _wl=B(_sF(_wi)),_wm=new T(function(){return B(_sH(_wl));}),_wn=B(_vZ(_wl));if(!B(A3(_w1,_wn,_wk,new T(function(){return B(A2(_9Z,_wm,_w3));})))){if(!B(A3(_mq,B(_mc(_wn)),_wk,new T(function(){return B(A2(_9Z,_wm,_w3));})))){var _wo=new T(function(){return B(A2(_9Z,_wm,_nF));}),_wp=new T(function(){return B(A2(_9Z,_wm,_nv));}),_wq=B(_mc(_wn)),_wr=function(_ws,_wt,_wu){while(1){var _wv=B((function(_ww,_wx,_wy){if(!B(_w6(_wi,_wx))){if(!B(A3(_mq,_wq,_wx,_wp))){var _wz=new T(function(){return B(A3(_we,_wi,new T(function(){return B(A3(_8w,_wm,_wx,_wp));}),_wo));});_ws=new T(function(){return B(A3(_8u,_wh,_ww,_ww));});_wt=_wz;_wu=new T(function(){return B(A3(_8u,_wh,_ww,_wy));});return __continue;}else{return new F(function(){return A3(_8u,_wh,_ww,_wy);});}}else{var _wA=_wy;_ws=new T(function(){return B(A3(_8u,_wh,_ww,_ww));});_wt=new T(function(){return B(A3(_we,_wi,_wx,_wo));});_wu=_wA;return __continue;}})(_ws,_wt,_wu));if(_wv!=__continue){return _wv;}}},_wB=function(_wC,_wD){while(1){var _wE=B((function(_wF,_wG){if(!B(_w6(_wi,_wG))){if(!B(A3(_mq,_wq,_wG,_wp))){var _wH=new T(function(){return B(A3(_we,_wi,new T(function(){return B(A3(_8w,_wm,_wG,_wp));}),_wo));});return new F(function(){return _wr(new T(function(){return B(A3(_8u,_wh,_wF,_wF));}),_wH,_wF);});}else{return E(_wF);}}else{_wC=new T(function(){return B(A3(_8u,_wh,_wF,_wF));});_wD=new T(function(){return B(A3(_we,_wi,_wG,_wo));});return __continue;}})(_wC,_wD));if(_wE!=__continue){return _wE;}}};return new F(function(){return _wB(_wj,_wk);});}else{return new F(function(){return A2(_9Z,_wh,_nv);});}}else{return E(_wd);}},_wI=new T(function(){return B(err(_wc));}),_wJ=function(_wK,_wL){var _wM=B(_rB(_wL)),_wN=_wM.a,_wO=_wM.b,_wP=new T(function(){return B(_sH(new T(function(){return B(_sF(_wK));})));});if(_wO<0){var _wQ= -_wO;if(_wQ>=0){var _wR=E(_wQ);if(!_wR){var _wS=E(_nv);}else{var _wS=B(_vT(_vC,_wR));}if(!B(_4y(_wS,_51))){var _wT=B(_4S(_wN,_wS));return new T2(0,new T(function(){return B(A2(_9Z,_wP,_wT.a));}),new T(function(){return B(_4u(_wT.b,_wO));}));}else{return E(_4t);}}else{return E(_wI);}}else{var _wU=new T(function(){var _wV=new T(function(){return B(_wg(_wP,_vB,new T(function(){return B(A2(_9Z,_wP,_vC));}),_wO));});return B(A3(_8u,_wP,new T(function(){return B(A2(_9Z,_wP,_wN));}),_wV));});return new T2(0,_wU,_7I);}},_wW=function(_wX,_wY){var _wZ=B(_wJ(_wX,E(_wY))),_x0=_wZ.a;if(E(_wZ.b)<=0){return E(_x0);}else{var _x1=B(_sH(B(_sF(_wX))));return new F(function(){return A3(_86,_x1,_x0,new T(function(){return B(A2(_9Z,_x1,_3k));}));});}},_x2=function(_x3,_x4){var _x5=B(_wJ(_x3,E(_x4))),_x6=_x5.a;if(E(_x5.b)>=0){return E(_x6);}else{var _x7=B(_sH(B(_sF(_x3))));return new F(function(){return A3(_8w,_x7,_x6,new T(function(){return B(A2(_9Z,_x7,_3k));}));});}},_x8=function(_x9,_xa){var _xb=B(_wJ(_x9,E(_xa)));return new T2(0,_xb.a,_xb.b);},_xc=function(_xd,_xe){var _xf=B(_wJ(_xd,_xe)),_xg=_xf.a,_xh=E(_xf.b),_xi=new T(function(){var _xj=B(_sH(B(_sF(_xd))));if(_xh>=0){return B(A3(_86,_xj,_xg,new T(function(){return B(A2(_9Z,_xj,_3k));})));}else{return B(A3(_8w,_xj,_xg,new T(function(){return B(A2(_9Z,_xj,_3k));})));}}),_xk=function(_xl){var _xm=_xl-0.5;return (_xm>=0)?(E(_xm)==0)?(!B(_w6(_xd,_xg)))?E(_xi):E(_xg):E(_xi):E(_xg);},_xn=E(_xh);if(!_xn){return new F(function(){return _xk(0);});}else{if(_xn<=0){var _xo= -_xn-0.5;return (_xo>=0)?(E(_xo)==0)?(!B(_w6(_xd,_xg)))?E(_xi):E(_xg):E(_xi):E(_xg);}else{return new F(function(){return _xk(_xn);});}}},_xp=function(_xq,_xr){return new F(function(){return _xc(_xq,E(_xr));});},_xs=function(_xt,_xu){return E(B(_wJ(_xt,E(_xu))).a);},_xv={_:0,a:_sE,b:_jn,c:_x8,d:_xs,e:_xp,f:_wW,g:_x2},_xw=new T1(0,1),_xx=function(_xy,_xz){var _xA=E(_xy);return new T2(0,_xA,new T(function(){var _xB=B(_xx(B(_4J(_xA,_xz)),_xz));return new T2(1,_xB.a,_xB.b);}));},_xC=function(_xD){var _xE=B(_xx(_xD,_xw));return new T2(1,_xE.a,_xE.b);},_xF=function(_xG,_xH){var _xI=B(_xx(_xG,new T(function(){return B(_6W(_xH,_xG));})));return new T2(1,_xI.a,_xI.b);},_xJ=new T1(0,0),_xK=function(_xL,_xM){var _xN=E(_xL);if(!_xN._){var _xO=_xN.a,_xP=E(_xM);return (_xP._==0)?_xO>=_xP.a:I_compareInt(_xP.a,_xO)<=0;}else{var _xQ=_xN.a,_xR=E(_xM);return (_xR._==0)?I_compareInt(_xQ,_xR.a)>=0:I_compare(_xQ,_xR.a)>=0;}},_xS=function(_xT,_xU,_xV){if(!B(_xK(_xU,_xJ))){var _xW=function(_xX){return (!B(_S(_xX,_xV)))?new T2(1,_xX,new T(function(){return B(_xW(B(_4J(_xX,_xU))));})):__Z;};return new F(function(){return _xW(_xT);});}else{var _xY=function(_xZ){return (!B(_5c(_xZ,_xV)))?new T2(1,_xZ,new T(function(){return B(_xY(B(_4J(_xZ,_xU))));})):__Z;};return new F(function(){return _xY(_xT);});}},_y0=function(_y1,_y2,_y3){return new F(function(){return _xS(_y1,B(_6W(_y2,_y1)),_y3);});},_y4=function(_y5,_y6){return new F(function(){return _xS(_y5,_xw,_y6);});},_y7=function(_y8){return new F(function(){return _4G(_y8);});},_y9=function(_ya){return new F(function(){return _6W(_ya,_xw);});},_yb=function(_yc){return new F(function(){return _4J(_yc,_xw);});},_yd=function(_ye){return new F(function(){return _rE(E(_ye));});},_yf={_:0,a:_yb,b:_y9,c:_yd,d:_y7,e:_xC,f:_xF,g:_y4,h:_y0},_yg=function(_yh,_yi){while(1){var _yj=E(_yh);if(!_yj._){var _yk=E(_yj.a);if(_yk==(-2147483648)){_yh=new T1(1,I_fromInt(-2147483648));continue;}else{var _yl=E(_yi);if(!_yl._){return new T1(0,B(_tA(_yk,_yl.a)));}else{_yh=new T1(1,I_fromInt(_yk));_yi=_yl;continue;}}}else{var _ym=_yj.a,_yn=E(_yi);return (_yn._==0)?new T1(1,I_div(_ym,I_fromInt(_yn.a))):new T1(1,I_div(_ym,_yn.a));}}},_yo=function(_yp,_yq){if(!B(_4y(_yq,_w3))){return new F(function(){return _yg(_yp,_yq);});}else{return E(_4t);}},_yr=function(_ys,_yt){while(1){var _yu=E(_ys);if(!_yu._){var _yv=E(_yu.a);if(_yv==(-2147483648)){_ys=new T1(1,I_fromInt(-2147483648));continue;}else{var _yw=E(_yt);if(!_yw._){var _yx=_yw.a;return new T2(0,new T1(0,B(_tA(_yv,_yx))),new T1(0,B(_u6(_yv,_yx))));}else{_ys=new T1(1,I_fromInt(_yv));_yt=_yw;continue;}}}else{var _yy=E(_yt);if(!_yy._){_ys=_yu;_yt=new T1(1,I_fromInt(_yy.a));continue;}else{var _yz=I_divMod(_yu.a,_yy.a);return new T2(0,new T1(1,_yz.a),new T1(1,_yz.b));}}}},_yA=function(_yB,_yC){if(!B(_4y(_yC,_w3))){var _yD=B(_yr(_yB,_yC));return new T2(0,_yD.a,_yD.b);}else{return E(_4t);}},_yE=function(_yF,_yG){while(1){var _yH=E(_yF);if(!_yH._){var _yI=E(_yH.a);if(_yI==(-2147483648)){_yF=new T1(1,I_fromInt(-2147483648));continue;}else{var _yJ=E(_yG);if(!_yJ._){return new T1(0,B(_u6(_yI,_yJ.a)));}else{_yF=new T1(1,I_fromInt(_yI));_yG=_yJ;continue;}}}else{var _yK=_yH.a,_yL=E(_yG);return (_yL._==0)?new T1(1,I_mod(_yK,I_fromInt(_yL.a))):new T1(1,I_mod(_yK,_yL.a));}}},_yM=function(_yN,_yO){if(!B(_4y(_yO,_w3))){return new F(function(){return _yE(_yN,_yO);});}else{return E(_4t);}},_yP=function(_yQ,_yR){while(1){var _yS=E(_yQ);if(!_yS._){var _yT=E(_yS.a);if(_yT==(-2147483648)){_yQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _yU=E(_yR);if(!_yU._){return new T1(0,quot(_yT,_yU.a));}else{_yQ=new T1(1,I_fromInt(_yT));_yR=_yU;continue;}}}else{var _yV=_yS.a,_yW=E(_yR);return (_yW._==0)?new T1(0,I_toInt(I_quot(_yV,I_fromInt(_yW.a)))):new T1(1,I_quot(_yV,_yW.a));}}},_yX=function(_yY,_yZ){if(!B(_4y(_yZ,_w3))){return new F(function(){return _yP(_yY,_yZ);});}else{return E(_4t);}},_z0=function(_z1,_z2){if(!B(_4y(_z2,_w3))){var _z3=B(_4S(_z1,_z2));return new T2(0,_z3.a,_z3.b);}else{return E(_4t);}},_z4=function(_z5,_z6){while(1){var _z7=E(_z5);if(!_z7._){var _z8=E(_z7.a);if(_z8==(-2147483648)){_z5=new T1(1,I_fromInt(-2147483648));continue;}else{var _z9=E(_z6);if(!_z9._){return new T1(0,_z8%_z9.a);}else{_z5=new T1(1,I_fromInt(_z8));_z6=_z9;continue;}}}else{var _za=_z7.a,_zb=E(_z6);return (_zb._==0)?new T1(1,I_rem(_za,I_fromInt(_zb.a))):new T1(1,I_rem(_za,_zb.a));}}},_zc=function(_zd,_ze){if(!B(_4y(_ze,_w3))){return new F(function(){return _z4(_zd,_ze);});}else{return E(_4t);}},_zf=function(_zg){return E(_zg);},_zh=function(_zi){return E(_zi);},_zj=function(_zk){var _zl=E(_zk);if(!_zl._){var _zm=E(_zl.a);return (_zm==(-2147483648))?E(_7A):(_zm<0)?new T1(0, -_zm):E(_zl);}else{var _zn=_zl.a;return (I_compareInt(_zn,0)>=0)?E(_zl):new T1(1,I_negate(_zn));}},_zo=new T1(0,0),_zp=new T1(0,-1),_zq=function(_zr){var _zs=E(_zr);if(!_zs._){var _zt=_zs.a;return (_zt>=0)?(E(_zt)==0)?E(_zo):E(_5k):E(_zp);}else{var _zu=I_compareInt(_zs.a,0);return (_zu<=0)?(E(_zu)==0)?E(_zo):E(_zp):E(_5k);}},_zv={_:0,a:_4J,b:_6W,c:_vD,d:_7B,e:_zj,f:_zq,g:_zh},_zw=function(_zx,_zy){var _zz=E(_zx);if(!_zz._){var _zA=_zz.a,_zB=E(_zy);return (_zB._==0)?_zA!=_zB.a:(I_compareInt(_zB.a,_zA)==0)?false:true;}else{var _zC=_zz.a,_zD=E(_zy);return (_zD._==0)?(I_compareInt(_zC,_zD.a)==0)?false:true:(I_compare(_zC,_zD.a)==0)?false:true;}},_zE=new T2(0,_4y,_zw),_zF=function(_zG,_zH){return (!B(_6H(_zG,_zH)))?E(_zG):E(_zH);},_zI=function(_zJ,_zK){return (!B(_6H(_zJ,_zK)))?E(_zK):E(_zJ);},_zL={_:0,a:_zE,b:_3l,c:_S,d:_6H,e:_5c,f:_xK,g:_zF,h:_zI},_zM=function(_zN){return new T2(0,E(_zN),E(_nv));},_zO=new T3(0,_zv,_zL,_zM),_zP={_:0,a:_zO,b:_yf,c:_yX,d:_zc,e:_yo,f:_yM,g:_z0,h:_yA,i:_zf},_zQ=function(_zR){return E(E(_zR).b);},_zS=function(_zT){return E(E(_zT).g);},_zU=new T1(0,1),_zV=function(_zW,_zX,_zY){var _zZ=B(_zQ(_zW)),_A0=B(_8s(_zZ)),_A1=new T(function(){var _A2=new T(function(){var _A3=new T(function(){var _A4=new T(function(){return B(A3(_zS,_zW,_zP,new T(function(){return B(A3(_a9,_zZ,_zX,_zY));})));});return B(A2(_9Z,_A0,_A4));}),_A5=new T(function(){return B(A2(_88,_A0,new T(function(){return B(A2(_9Z,_A0,_zU));})));});return B(A3(_8u,_A0,_A5,_A3));});return B(A3(_8u,_A0,_A2,_zY));});return new F(function(){return A3(_86,_A0,_zX,_A1);});},_A6=1.5707963267948966,_A7=function(_A8){return 0.2/Math.cos(B(_zV(_xv,_A8,_A6))-0.7853981633974483);},_A9=0,_Aa=new T(function(){var _Ab=B(_qf(_A7,1.2,_A9,_A9,_ry,_A9,_A9,_A9,_A9,_A9,_ry,_ry,_ry));return {_:0,a:E(_Ab.a),b:E(_rz),c:E(_il),d:E(_Ab.d),e:E(_Ab.e),f:E(_Ab.f),g:E(_Ab.g),h:_Ab.h,i:_Ab.i};}),_Ac=0,_Ad=0.3,_Ae=function(_Af){return E(_Ad);},_Ag=new T(function(){var _Ah=B(_qf(_Ae,1.2,_ry,_A9,_ry,_A9,_A9,_A9,_A9,_A9,_ry,_ry,_ry));return {_:0,a:E(_Ah.a),b:E(_Ah.b),c:E(_Ah.c),d:E(_Ah.d),e:E(_Ah.e),f:E(_Ah.f),g:E(_Ah.g),h:_Ah.h,i:_Ah.i};}),_Ai=new T(function(){var _Aj=B(_qf(_Ae,1.2,_ry,_ry,_A9,_A9,_A9,_A9,_A9,_A9,_ry,_ry,_ry));return {_:0,a:E(_Aj.a),b:E(_Aj.b),c:E(_Aj.c),d:E(_Aj.d),e:E(_Aj.e),f:E(_Aj.f),g:E(_Aj.g),h:_Aj.h,i:_Aj.i};}),_Ak=2,_Al=function(_Am){return 0.3/Math.cos(B(_zV(_xv,_Am,_A6))-0.7853981633974483);},_An=new T(function(){var _Ao=B(_qf(_Al,1.2,_Ak,_ry,_ry,_A9,_A9,_A9,_A9,_A9,_ry,_ry,_ry));return {_:0,a:E(_Ao.a),b:E(_Ao.b),c:E(_Ao.c),d:E(_Ao.d),e:E(_Ao.e),f:E(_Ao.f),g:E(_Ao.g),h:_Ao.h,i:_Ao.i};}),_Ap=new T2(1,_An,_w),_Aq=new T2(1,_Ai,_Ap),_Ar=new T2(1,_Ag,_Aq),_As=new T2(1,_Aa,_Ar),_At=new T(function(){return B(unCStr("Negative range size"));}),_Au=new T(function(){return B(err(_At));}),_Av=function(_){var _Aw=B(_ic(_As,0))-1|0,_Ax=function(_Ay){if(_Ay>=0){var _Az=newArr(_Ay,_ii),_AA=_Az,_AB=E(_Ay);if(!_AB){return new T4(0,E(_Ac),E(_Aw),0,_AA);}else{var _AC=function(_AD,_AE,_){while(1){var _AF=E(_AD);if(!_AF._){return E(_);}else{var _=_AA[_AE]=_AF.a;if(_AE!=(_AB-1|0)){var _AG=_AE+1|0;_AD=_AF.b;_AE=_AG;continue;}else{return E(_);}}}},_=B((function(_AH,_AI,_AJ,_){var _=_AA[_AJ]=_AH;if(_AJ!=(_AB-1|0)){return new F(function(){return _AC(_AI,_AJ+1|0,_);});}else{return E(_);}})(_Aa,_Ar,0,_));return new T4(0,E(_Ac),E(_Aw),_AB,_AA);}}else{return E(_Au);}};if(0>_Aw){return new F(function(){return _Ax(0);});}else{return new F(function(){return _Ax(_Aw+1|0);});}},_AK=function(_AL){var _AM=B(A1(_AL,_));return E(_AM);},_AN=new T(function(){return B(_AK(_Av));}),_AO="outline",_AP="polygon",_AQ=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_AR=new T(function(){return B(err(_AQ));}),_AS=new T(function(){return eval("__strict(drawObjects)");}),_AT=new T(function(){return eval("__strict(draw)");}),_AU=function(_AV,_AW){var _AX=jsShowI(_AV);return new F(function(){return _n(fromJSStr(_AX),_AW);});},_AY=function(_AZ,_B0,_B1){if(_B0>=0){return new F(function(){return _AU(_B0,_B1);});}else{if(_AZ<=6){return new F(function(){return _AU(_B0,_B1);});}else{return new T2(1,_11,new T(function(){var _B2=jsShowI(_B0);return B(_n(fromJSStr(_B2),new T2(1,_10,_B1)));}));}}},_B3=new T(function(){return B(unCStr(")"));}),_B4=function(_B5,_B6){var _B7=new T(function(){var _B8=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AY(0,_B5,_w)),_B3));})));},1);return B(_n(B(_AY(0,_B6,_w)),_B8));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B7)));});},_B9=new T2(1,_kA,_w),_Ba=function(_Bb){return E(_Bb);},_Bc=function(_Bd){return E(_Bd);},_Be=function(_Bf,_Bg){return E(_Bg);},_Bh=function(_Bi,_Bj){return E(_Bi);},_Bk=function(_Bl){return E(_Bl);},_Bm=new T2(0,_Bk,_Bh),_Bn=function(_Bo,_Bp){return E(_Bo);},_Bq=new T5(0,_Bm,_Bc,_Ba,_Be,_Bn),_Br="flipped2",_Bs="flipped1",_Bt="c1y",_Bu="c1x",_Bv="w2z",_Bw="w2y",_Bx="w2x",_By="w1z",_Bz="w1y",_BA="w1x",_BB="d2z",_BC="d2y",_BD="d2x",_BE="d1z",_BF="d1y",_BG="d1x",_BH="c2y",_BI="c2x",_BJ=function(_BK,_){var _BL=__get(_BK,E(_BA)),_BM=__get(_BK,E(_Bz)),_BN=__get(_BK,E(_By)),_BO=__get(_BK,E(_Bx)),_BP=__get(_BK,E(_Bw)),_BQ=__get(_BK,E(_Bv)),_BR=__get(_BK,E(_Bu)),_BS=__get(_BK,E(_Bt)),_BT=__get(_BK,E(_BI)),_BU=__get(_BK,E(_BH)),_BV=__get(_BK,E(_BG)),_BW=__get(_BK,E(_BF)),_BX=__get(_BK,E(_BE)),_BY=__get(_BK,E(_BD)),_BZ=__get(_BK,E(_BC)),_C0=__get(_BK,E(_BB)),_C1=__get(_BK,E(_Bs)),_C2=__get(_BK,E(_Br));return {_:0,a:E(new T3(0,E(_BL),E(_BM),E(_BN))),b:E(new T3(0,E(_BO),E(_BP),E(_BQ))),c:E(new T2(0,E(_BR),E(_BS))),d:E(new T2(0,E(_BT),E(_BU))),e:E(new T3(0,E(_BV),E(_BW),E(_BX))),f:E(new T3(0,E(_BY),E(_BZ),E(_C0))),g:E(_C1),h:E(_C2)};},_C3=function(_C4,_){var _C5=E(_C4);if(!_C5._){return _w;}else{var _C6=B(_BJ(E(_C5.a),_)),_C7=B(_C3(_C5.b,_));return new T2(1,_C6,_C7);}},_C8=function(_C9){var _Ca=E(_C9);return (E(_Ca.b)-E(_Ca.a)|0)+1|0;},_Cb=function(_Cc,_Cd){var _Ce=E(_Cc),_Cf=E(_Cd);return (E(_Ce.a)>_Cf)?false:_Cf<=E(_Ce.b);},_Cg=function(_Ch){return new F(function(){return _AY(0,E(_Ch),_w);});},_Ci=function(_Cj,_Ck,_Cl){return new F(function(){return _AY(E(_Cj),E(_Ck),_Cl);});},_Cm=function(_Cn,_Co){return new F(function(){return _AY(0,E(_Cn),_Co);});},_Cp=function(_Cq,_Cr){return new F(function(){return _49(_Cm,_Cq,_Cr);});},_Cs=new T3(0,_Ci,_Cg,_Cp),_Ct=0,_Cu=function(_Cv,_Cw,_Cx){return new F(function(){return A1(_Cv,new T2(1,_46,new T(function(){return B(A1(_Cw,_Cx));})));});},_Cy=new T(function(){return B(unCStr("foldr1"));}),_Cz=new T(function(){return B(_mV(_Cy));}),_CA=function(_CB,_CC){var _CD=E(_CC);if(!_CD._){return E(_Cz);}else{var _CE=_CD.a,_CF=E(_CD.b);if(!_CF._){return E(_CE);}else{return new F(function(){return A2(_CB,_CE,new T(function(){return B(_CA(_CB,_CF));}));});}}},_CG=new T(function(){return B(unCStr(" out of range "));}),_CH=new T(function(){return B(unCStr("}.index: Index "));}),_CI=new T(function(){return B(unCStr("Ix{"));}),_CJ=new T2(1,_10,_w),_CK=new T2(1,_10,_CJ),_CL=0,_CM=function(_CN){return E(E(_CN).a);},_CO=function(_CP,_CQ,_CR,_CS,_CT){var _CU=new T(function(){var _CV=new T(function(){var _CW=new T(function(){var _CX=new T(function(){var _CY=new T(function(){return B(A3(_CA,_Cu,new T2(1,new T(function(){return B(A3(_CM,_CR,_CL,_CS));}),new T2(1,new T(function(){return B(A3(_CM,_CR,_CL,_CT));}),_w)),_CK));});return B(_n(_CG,new T2(1,_11,new T2(1,_11,_CY))));});return B(A(_CM,[_CR,_Ct,_CQ,new T2(1,_10,_CX)]));});return B(_n(_CH,new T2(1,_11,_CW)));},1);return B(_n(_CP,_CV));},1);return new F(function(){return err(B(_n(_CI,_CU)));});},_CZ=function(_D0,_D1,_D2,_D3,_D4){return new F(function(){return _CO(_D0,_D1,_D4,_D2,_D3);});},_D5=function(_D6,_D7,_D8,_D9){var _Da=E(_D8);return new F(function(){return _CZ(_D6,_D7,_Da.a,_Da.b,_D9);});},_Db=function(_Dc,_Dd,_De,_Df){return new F(function(){return _D5(_Df,_De,_Dd,_Dc);});},_Dg=new T(function(){return B(unCStr("Int"));}),_Dh=function(_Di,_Dj){return new F(function(){return _Db(_Cs,_Dj,_Di,_Dg);});},_Dk=function(_Dl,_Dm){var _Dn=E(_Dl),_Do=E(_Dn.a),_Dp=E(_Dm);if(_Do>_Dp){return new F(function(){return _Dh(_Dp,_Dn);});}else{if(_Dp>E(_Dn.b)){return new F(function(){return _Dh(_Dp,_Dn);});}else{return _Dp-_Do|0;}}},_Dq=function(_Dr){var _Ds=E(_Dr);return new F(function(){return _tk(_Ds.a,_Ds.b);});},_Dt=function(_Du){var _Dv=E(_Du),_Dw=E(_Dv.a),_Dx=E(_Dv.b);return (_Dw>_Dx)?E(_Ct):(_Dx-_Dw|0)+1|0;},_Dy=function(_Dz,_DA){return new F(function(){return _uJ(_DA,E(_Dz).a);});},_DB={_:0,a:_vz,b:_Dq,c:_Dk,d:_Dy,e:_Cb,f:_Dt,g:_C8},_DC=function(_DD,_DE,_){while(1){var _DF=B((function(_DG,_DH,_){var _DI=E(_DG);if(!_DI._){return new T2(0,_kA,_DH);}else{var _DJ=B(A2(_DI.a,_DH,_));_DD=_DI.b;_DE=new T(function(){return E(E(_DJ).b);});return __continue;}})(_DD,_DE,_));if(_DF!=__continue){return _DF;}}},_DK=function(_DL,_DM){return new T2(1,_DL,_DM);},_DN=function(_DO,_DP){var _DQ=E(_DP);return new T2(0,_DQ.a,_DQ.b);},_DR=function(_DS){return E(E(_DS).f);},_DT=function(_DU,_DV,_DW){var _DX=E(_DV),_DY=_DX.a,_DZ=_DX.b,_E0=function(_){var _E1=B(A2(_DR,_DU,_DX));if(_E1>=0){var _E2=newArr(_E1,_ii),_E3=_E2,_E4=E(_E1);if(!_E4){return new T(function(){return new T4(0,E(_DY),E(_DZ),0,_E3);});}else{var _E5=function(_E6,_E7,_){while(1){var _E8=E(_E6);if(!_E8._){return E(_);}else{var _=_E3[_E7]=_E8.a;if(_E7!=(_E4-1|0)){var _E9=_E7+1|0;_E6=_E8.b;_E7=_E9;continue;}else{return E(_);}}}},_=B(_E5(_DW,0,_));return new T(function(){return new T4(0,E(_DY),E(_DZ),_E4,_E3);});}}else{return E(_Au);}};return new F(function(){return _AK(_E0);});},_Ea=function(_Eb,_Ec,_Ed,_Ee){var _Ef=new T(function(){var _Eg=E(_Ee),_Eh=_Eg.c-1|0,_Ei=new T(function(){return B(A2(_dU,_Ec,_w));});if(0<=_Eh){var _Ej=new T(function(){return B(_a5(_Ec));}),_Ek=function(_El){var _Em=new T(function(){var _En=new T(function(){return B(A1(_Ed,new T(function(){return E(_Eg.d[_El]);})));});return B(A3(_ad,_Ej,_DK,_En));});return new F(function(){return A3(_ab,_Ec,_Em,new T(function(){if(_El!=_Eh){return B(_Ek(_El+1|0));}else{return E(_Ei);}}));});};return B(_Ek(0));}else{return E(_Ei);}}),_Eo=new T(function(){return B(_DN(_Eb,_Ee));});return new F(function(){return A3(_ad,B(_a5(_Ec)),function(_Ep){return new F(function(){return _DT(_Eb,_Eo,_Ep);});},_Ef);});},_Eq=function(_Er,_Es,_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez){var _EA=B(_8u(_Er));return new T2(0,new T3(0,E(B(A1(B(A1(_EA,_Es)),_Ew))),E(B(A1(B(A1(_EA,_Et)),_Ex))),E(B(A1(B(A1(_EA,_Eu)),_Ey)))),B(A1(B(A1(_EA,_Ev)),_Ez)));},_EB=function(_EC,_ED,_EE,_EF,_EG,_EH,_EI,_EJ,_EK){var _EL=B(_86(_EC));return new T2(0,new T3(0,E(B(A1(B(A1(_EL,_ED)),_EH))),E(B(A1(B(A1(_EL,_EE)),_EI))),E(B(A1(B(A1(_EL,_EF)),_EJ)))),B(A1(B(A1(_EL,_EG)),_EK)));},_EM=1.0e-2,_EN=function(_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1,_F2,_F3,_F4){var _F5=B(_Eq(_jj,_EV,_EW,_EX,_EY,_EM,_EM,_EM,_EM)),_F6=E(_F5.a),_F7=B(_EB(_jj,_ER,_ES,_ET,_EU,_F6.a,_F6.b,_F6.c,_F5.b)),_F8=E(_F7.a);return new F(function(){return _pw(_EO,_EP,_EQ,_F8.a,_F8.b,_F8.c,_F7.b,_EV,_EW,_EX,_EY,_EZ,_F0,_F1,_F2,_F3,_F4);});},_F9=function(_Fa){var _Fb=E(_Fa),_Fc=E(_Fb.d),_Fd=E(_Fc.a),_Fe=E(_Fb.e),_Ff=E(_Fe.a),_Fg=E(_Fb.f),_Fh=B(_EN(_Fb.a,_Fb.b,_Fb.c,_Fd.a,_Fd.b,_Fd.c,_Fc.b,_Ff.a,_Ff.b,_Ff.c,_Fe.b,_Fg.a,_Fg.b,_Fg.c,_Fb.g,_Fb.h,_Fb.i));return {_:0,a:E(_Fh.a),b:E(_Fh.b),c:E(_Fh.c),d:E(_Fh.d),e:E(_Fh.e),f:E(_Fh.f),g:E(_Fh.g),h:_Fh.h,i:_Fh.i};},_Fi=function(_Fj,_Fk,_Fl,_Fm,_Fn,_Fo,_Fp,_Fq,_Fr){var _Fs=B(_8s(B(_8q(_Fj))));return new F(function(){return A3(_86,_Fs,new T(function(){return B(_le(_Fj,_Fk,_Fl,_Fm,_Fo,_Fp,_Fq));}),new T(function(){return B(A3(_8u,_Fs,_Fn,_Fr));}));});},_Ft=new T(function(){return B(unCStr("base"));}),_Fu=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fv=new T(function(){return B(unCStr("IOException"));}),_Fw=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Ft,_Fu,_Fv),_Fx=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fw,_w,_w),_Fy=function(_Fz){return E(_Fx);},_FA=function(_FB){var _FC=E(_FB);return new F(function(){return _3G(B(_3E(_FC.a)),_Fy,_FC.b);});},_FD=new T(function(){return B(unCStr(": "));}),_FE=new T(function(){return B(unCStr(")"));}),_FF=new T(function(){return B(unCStr(" ("));}),_FG=new T(function(){return B(unCStr("interrupted"));}),_FH=new T(function(){return B(unCStr("system error"));}),_FI=new T(function(){return B(unCStr("unsatisified constraints"));}),_FJ=new T(function(){return B(unCStr("user error"));}),_FK=new T(function(){return B(unCStr("permission denied"));}),_FL=new T(function(){return B(unCStr("illegal operation"));}),_FM=new T(function(){return B(unCStr("end of file"));}),_FN=new T(function(){return B(unCStr("resource exhausted"));}),_FO=new T(function(){return B(unCStr("resource busy"));}),_FP=new T(function(){return B(unCStr("does not exist"));}),_FQ=new T(function(){return B(unCStr("already exists"));}),_FR=new T(function(){return B(unCStr("resource vanished"));}),_FS=new T(function(){return B(unCStr("timeout"));}),_FT=new T(function(){return B(unCStr("unsupported operation"));}),_FU=new T(function(){return B(unCStr("hardware fault"));}),_FV=new T(function(){return B(unCStr("inappropriate type"));}),_FW=new T(function(){return B(unCStr("invalid argument"));}),_FX=new T(function(){return B(unCStr("failed"));}),_FY=new T(function(){return B(unCStr("protocol error"));}),_FZ=function(_G0,_G1){switch(E(_G0)){case 0:return new F(function(){return _n(_FQ,_G1);});break;case 1:return new F(function(){return _n(_FP,_G1);});break;case 2:return new F(function(){return _n(_FO,_G1);});break;case 3:return new F(function(){return _n(_FN,_G1);});break;case 4:return new F(function(){return _n(_FM,_G1);});break;case 5:return new F(function(){return _n(_FL,_G1);});break;case 6:return new F(function(){return _n(_FK,_G1);});break;case 7:return new F(function(){return _n(_FJ,_G1);});break;case 8:return new F(function(){return _n(_FI,_G1);});break;case 9:return new F(function(){return _n(_FH,_G1);});break;case 10:return new F(function(){return _n(_FY,_G1);});break;case 11:return new F(function(){return _n(_FX,_G1);});break;case 12:return new F(function(){return _n(_FW,_G1);});break;case 13:return new F(function(){return _n(_FV,_G1);});break;case 14:return new F(function(){return _n(_FU,_G1);});break;case 15:return new F(function(){return _n(_FT,_G1);});break;case 16:return new F(function(){return _n(_FS,_G1);});break;case 17:return new F(function(){return _n(_FR,_G1);});break;default:return new F(function(){return _n(_FG,_G1);});}},_G2=new T(function(){return B(unCStr("}"));}),_G3=new T(function(){return B(unCStr("{handle: "));}),_G4=function(_G5,_G6,_G7,_G8,_G9,_Ga){var _Gb=new T(function(){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=E(_G8);if(!_Ge._){return E(_Ga);}else{var _Gf=new T(function(){return B(_n(_Ge,new T(function(){return B(_n(_FE,_Ga));},1)));},1);return B(_n(_FF,_Gf));}},1);return B(_FZ(_G6,_Gd));}),_Gg=E(_G7);if(!_Gg._){return E(_Gc);}else{return B(_n(_Gg,new T(function(){return B(_n(_FD,_Gc));},1)));}}),_Gh=E(_G9);if(!_Gh._){var _Gi=E(_G5);if(!_Gi._){return E(_Gb);}else{var _Gj=E(_Gi.a);if(!_Gj._){var _Gk=new T(function(){var _Gl=new T(function(){return B(_n(_G2,new T(function(){return B(_n(_FD,_Gb));},1)));},1);return B(_n(_Gj.a,_Gl));},1);return new F(function(){return _n(_G3,_Gk);});}else{var _Gm=new T(function(){var _Gn=new T(function(){return B(_n(_G2,new T(function(){return B(_n(_FD,_Gb));},1)));},1);return B(_n(_Gj.a,_Gn));},1);return new F(function(){return _n(_G3,_Gm);});}}}else{return new F(function(){return _n(_Gh.a,new T(function(){return B(_n(_FD,_Gb));},1));});}},_Go=function(_Gp){var _Gq=E(_Gp);return new F(function(){return _G4(_Gq.a,_Gq.b,_Gq.c,_Gq.d,_Gq.f,_w);});},_Gr=function(_Gs,_Gt,_Gu){var _Gv=E(_Gt);return new F(function(){return _G4(_Gv.a,_Gv.b,_Gv.c,_Gv.d,_Gv.f,_Gu);});},_Gw=function(_Gx,_Gy){var _Gz=E(_Gx);return new F(function(){return _G4(_Gz.a,_Gz.b,_Gz.c,_Gz.d,_Gz.f,_Gy);});},_GA=function(_GB,_GC){return new F(function(){return _49(_Gw,_GB,_GC);});},_GD=new T3(0,_Gr,_Go,_GA),_GE=new T(function(){return new T5(0,_Fy,_GD,_GF,_FA,_Go);}),_GF=function(_GG){return new T2(0,_GE,_GG);},_GH=__Z,_GI=7,_GJ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_GK=new T6(0,_GH,_GI,_w,_GJ,_GH,_GH),_GL=new T(function(){return B(_GF(_GK));}),_GM=function(_){return new F(function(){return die(_GL);});},_GN=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_GO=new T6(0,_GH,_GI,_w,_GN,_GH,_GH),_GP=new T(function(){return B(_GF(_GO));}),_GQ=function(_){return new F(function(){return die(_GP);});},_GR=function(_GS,_){return new T2(0,_w,_GS);},_GT=0.6,_GU=1,_GV=new T(function(){return B(unCStr(")"));}),_GW=function(_GX,_GY){var _GZ=new T(function(){var _H0=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AY(0,_GX,_w)),_GV));})));},1);return B(_n(B(_AY(0,_GY,_w)),_H0));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GZ)));});},_H1=function(_H2,_H3){var _H4=new T(function(){var _H5=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AY(0,_H3,_w)),_GV));})));},1);return B(_n(B(_AY(0,_H2,_w)),_H5));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_H4)));});},_H6=function(_H7){var _H8=E(_H7);if(!_H8._){return E(_GR);}else{var _H9=new T(function(){return B(_H6(_H8.b));}),_Ha=function(_Hb){var _Hc=E(_Hb);if(!_Hc._){return E(_H9);}else{var _Hd=_Hc.a,_He=new T(function(){return B(_Ha(_Hc.b));}),_Hf=new T(function(){return 0.1*E(E(_Hd).e)/1.0e-2;}),_Hg=new T(function(){var _Hh=E(_Hd);if(_Hh.a!=_Hh.b){return E(_GU);}else{return E(_GT);}}),_Hi=function(_Hj,_){var _Hk=E(_Hj),_Hl=_Hk.c,_Hm=_Hk.d,_Hn=E(_Hk.a),_Ho=E(_Hk.b),_Hp=E(_Hd),_Hq=_Hp.a,_Hr=_Hp.b,_Hs=E(_Hp.c),_Ht=_Hs.b,_Hu=E(_Hs.a),_Hv=_Hu.a,_Hw=_Hu.b,_Hx=_Hu.c,_Hy=E(_Hp.d),_Hz=_Hy.b,_HA=E(_Hy.a),_HB=_HA.a,_HC=_HA.b,_HD=_HA.c;if(_Hn>_Hq){return new F(function(){return _GQ(_);});}else{if(_Hq>_Ho){return new F(function(){return _GQ(_);});}else{if(_Hn>_Hr){return new F(function(){return _GM(_);});}else{if(_Hr>_Ho){return new F(function(){return _GM(_);});}else{var _HE=_Hq-_Hn|0;if(0>_HE){return new F(function(){return _GW(_Hl,_HE);});}else{if(_HE>=_Hl){return new F(function(){return _GW(_Hl,_HE);});}else{var _HF=E(_Hm[_HE]),_HG=E(_HF.c),_HH=_HG.b,_HI=E(_HG.a),_HJ=_HI.a,_HK=_HI.b,_HL=_HI.c,_HM=E(_HF.e),_HN=E(_HM.a),_HO=B(_Eq(_jj,_Hv,_Hw,_Hx,_Ht,_HJ,_HK,_HL,_HH)),_HP=E(_HO.a),_HQ=B(_Eq(_jj,_HP.a,_HP.b,_HP.c,_HO.b,_Hv,_Hw,_Hx,_Ht)),_HR=E(_HQ.a),_HS=_Hr-_Hn|0;if(0>_HS){return new F(function(){return _H1(_HS,_Hl);});}else{if(_HS>=_Hl){return new F(function(){return _H1(_HS,_Hl);});}else{var _HT=E(_Hm[_HS]),_HU=E(_HT.c),_HV=_HU.b,_HW=E(_HU.a),_HX=_HW.a,_HY=_HW.b,_HZ=_HW.c,_I0=E(_HT.e),_I1=E(_I0.a),_I2=B(_Eq(_jj,_HB,_HC,_HD,_Hz,_HX,_HY,_HZ,_HV)),_I3=E(_I2.a),_I4=B(_Eq(_jj,_I3.a,_I3.b,_I3.c,_I2.b,_HB,_HC,_HD,_Hz)),_I5=E(_I4.a),_I6=E(_HR.a)+E(_HR.b)+E(_HR.c)+E(_HQ.b)+E(_I5.a)+E(_I5.b)+E(_I5.c)+E(_I4.b);if(!_I6){var _I7=B(A2(_He,_Hk,_));return new T2(0,new T2(1,_kA,new T(function(){return E(E(_I7).a);})),new T(function(){return E(E(_I7).b);}));}else{var _I8=new T(function(){return  -((B(_Fi(_jP,_HN.a,_HN.b,_HN.c,_HM.b,_Hv,_Hw,_Hx,_Ht))-B(_Fi(_jP,_I1.a,_I1.b,_I1.c,_I0.b,_HB,_HC,_HD,_Hz))-E(_Hf))/_I6);}),_I9=function(_Ia,_Ib,_Ic,_Id,_){var _Ie=new T(function(){var _If=function(_Ig,_Ih,_Ii,_Ij,_Ik){if(_Ig>_Hr){return E(_Ik);}else{if(_Hr>_Ih){return E(_Ik);}else{var _Il=function(_){var _Im=newArr(_Ii,_ii),_In=_Im,_Io=function(_Ip,_){while(1){if(_Ip!=_Ii){var _=_In[_Ip]=_Ij[_Ip],_Iq=_Ip+1|0;_Ip=_Iq;continue;}else{return E(_);}}},_=B(_Io(0,_)),_Ir=_Hr-_Ig|0;if(0>_Ir){return new F(function(){return _H1(_Ir,_Ii);});}else{if(_Ir>=_Ii){return new F(function(){return _H1(_Ir,_Ii);});}else{var _=_In[_Ir]=new T(function(){var _Is=E(_Ij[_Ir]),_It=E(_Is.e),_Iu=E(_It.a),_Iv=B(_Eq(_jj,_HX,_HY,_HZ,_HV,_HB,_HC,_HD,_Hz)),_Iw=E(_Iv.a),_Ix=E(_I8)*E(_Hg),_Iy=B(_Eq(_jj,_Iw.a,_Iw.b,_Iw.c,_Iv.b,_Ix,_Ix,_Ix,_Ix)),_Iz=E(_Iy.a),_IA=B(_EB(_jj,_Iu.a,_Iu.b,_Iu.c,_It.b, -E(_Iz.a), -E(_Iz.b), -E(_Iz.c), -E(_Iy.b)));return {_:0,a:E(_Is.a),b:E(_Is.b),c:E(_Is.c),d:E(_Is.d),e:E(new T2(0,E(_IA.a),E(_IA.b))),f:E(_Is.f),g:E(_Is.g),h:_Is.h,i:_Is.i};});return new T4(0,E(_Ig),E(_Ih),_Ii,_In);}}};return new F(function(){return _AK(_Il);});}}};if(_Ia>_Hq){return B(_If(_Ia,_Ib,_Ic,_Id,new T4(0,E(_Ia),E(_Ib),_Ic,_Id)));}else{if(_Hq>_Ib){return B(_If(_Ia,_Ib,_Ic,_Id,new T4(0,E(_Ia),E(_Ib),_Ic,_Id)));}else{var _IB=function(_){var _IC=newArr(_Ic,_ii),_ID=_IC,_IE=function(_IF,_){while(1){if(_IF!=_Ic){var _=_ID[_IF]=_Id[_IF],_IG=_IF+1|0;_IF=_IG;continue;}else{return E(_);}}},_=B(_IE(0,_)),_IH=_Hq-_Ia|0;if(0>_IH){return new F(function(){return _GW(_Ic,_IH);});}else{if(_IH>=_Ic){return new F(function(){return _GW(_Ic,_IH);});}else{var _=_ID[_IH]=new T(function(){var _II=E(_Id[_IH]),_IJ=E(_II.e),_IK=E(_IJ.a),_IL=B(_Eq(_jj,_HJ,_HK,_HL,_HH,_Hv,_Hw,_Hx,_Ht)),_IM=E(_IL.a),_IN=E(_I8)*E(_Hg),_IO=B(_Eq(_jj,_IM.a,_IM.b,_IM.c,_IL.b,_IN,_IN,_IN,_IN)),_IP=E(_IO.a),_IQ=B(_EB(_jj,_IK.a,_IK.b,_IK.c,_IJ.b,_IP.a,_IP.b,_IP.c,_IO.b));return {_:0,a:E(_II.a),b:E(_II.b),c:E(_II.c),d:E(_II.d),e:E(new T2(0,E(_IQ.a),E(_IQ.b))),f:E(_II.f),g:E(_II.g),h:_II.h,i:_II.i};});return new T4(0,E(_Ia),E(_Ib),_Ic,_ID);}}},_IR=B(_AK(_IB));return B(_If(E(_IR.a),E(_IR.b),_IR.c,_IR.d,_IR));}}});return new T2(0,_kA,_Ie);};if(!E(_Hp.f)){var _IS=B(_I9(_Hn,_Ho,_Hl,_Hm,_)),_IT=B(A2(_He,new T(function(){return E(E(_IS).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IS).a);}),new T(function(){return E(E(_IT).a);})),new T(function(){return E(E(_IT).b);}));}else{if(E(_I8)<0){var _IU=B(A2(_He,_Hk,_));return new T2(0,new T2(1,_kA,new T(function(){return E(E(_IU).a);})),new T(function(){return E(E(_IU).b);}));}else{var _IV=B(_I9(_Hn,_Ho,_Hl,_Hm,_)),_IW=B(A2(_He,new T(function(){return E(E(_IV).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IV).a);}),new T(function(){return E(E(_IW).a);})),new T(function(){return E(E(_IW).b);}));}}}}}}}}}}}};return E(_Hi);}};return new F(function(){return _Ha(_H8.a);});}},_IX=function(_,_IY){var _IZ=new T(function(){return B(_H6(E(_IY).a));}),_J0=function(_J1){var _J2=E(_J1);return (_J2==1)?E(new T2(1,_IZ,_w)):new T2(1,_IZ,new T(function(){return B(_J0(_J2-1|0));}));},_J3=B(_DC(B(_J0(5)),new T(function(){return E(E(_IY).b);}),_)),_J4=new T(function(){return B(_Ea(_DB,_Bq,_F9,new T(function(){return E(E(_J3).b);})));});return new T2(0,_kA,_J4);},_J5=function(_J6,_J7,_J8,_J9,_Ja){var _Jb=B(_8s(B(_8q(_J6))));return new F(function(){return A3(_86,_Jb,new T(function(){return B(A3(_8u,_Jb,_J7,_J9));}),new T(function(){return B(A3(_8u,_Jb,_J8,_Ja));}));});},_Jc=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Jd=new T6(0,_GH,_GI,_w,_Jc,_GH,_GH),_Je=new T(function(){return B(_GF(_Jd));}),_Jf=function(_){return new F(function(){return die(_Je);});},_Jg=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Jh=new T6(0,_GH,_GI,_w,_Jg,_GH,_GH),_Ji=new T(function(){return B(_GF(_Jh));}),_Jj=function(_){return new F(function(){return die(_Ji);});},_Jk=false,_Jl=true,_Jm=function(_Jn){var _Jo=E(_Jn),_Jp=_Jo.b,_Jq=E(_Jo.d),_Jr=E(_Jo.e),_Js=E(_Jr.a),_Jt=E(_Jo.g),_Ju=B(A1(_Jp,_Jq.a)),_Jv=B(_me(_jP,_Ju.a,_Ju.b,_Ju.c,_Jt.a,_Jt.b,_Jt.c));return {_:0,a:E(_Jo.a),b:E(_Jp),c:E(_Jo.c),d:E(_Jq),e:E(new T2(0,E(new T3(0,E(_Js.a)+E(_Jv.a)*1.0e-2,E(_Js.b)+E(_Jv.b)*1.0e-2,E(_Js.c)+E(_Jv.c)*1.0e-2)),E(_Jr.b))),f:E(_Jo.f),g:E(_Jt),h:_Jo.h,i:_Jo.i};},_Jw=new T(function(){return eval("__strict(collideBound)");}),_Jx=new T(function(){return eval("__strict(mouseContact)");}),_Jy=new T(function(){return eval("__strict(collide)");}),_Jz=function(_JA){var _JB=E(_JA);if(!_JB._){return __Z;}else{return new F(function(){return _n(_JB.a,new T(function(){return B(_Jz(_JB.b));},1));});}},_JC=0,_JD=new T3(0,E(_JC),E(_JC),E(_JC)),_JE=new T2(0,E(_JD),E(_JC)),_JF=new T2(0,_jP,_ko),_JG=new T(function(){return B(_hP(_JF));}),_JH=function(_JI,_){var _JJ=B(_Ea(_DB,_Bq,_Jm,_JI)),_JK=E(_JJ.a),_JL=E(_JJ.b);if(_JK<=_JL){var _JM=function(_JN,_JO,_JP,_JQ,_JR,_){if(_JO>_JN){return new F(function(){return _Jj(_);});}else{if(_JN>_JP){return new F(function(){return _Jj(_);});}else{var _JS=new T(function(){var _JT=_JN-_JO|0;if(0>_JT){return B(_H1(_JT,_JQ));}else{if(_JT>=_JQ){return B(_H1(_JT,_JQ));}else{return E(_JR[_JT]);}}}),_JU=function(_JV,_JW,_JX,_JY,_JZ,_){var _K0=E(_JV);if(!_K0._){return new T2(0,_w,new T4(0,E(_JW),E(_JX),_JY,_JZ));}else{var _K1=E(_K0.a);if(_JW>_K1){return new F(function(){return _Jf(_);});}else{if(_K1>_JX){return new F(function(){return _Jf(_);});}else{var _K2=E(_JS),_K3=_K1-_JW|0;if(0>_K3){return new F(function(){return _GW(_JY,_K3);});}else{if(_K3>=_JY){return new F(function(){return _GW(_JY,_K3);});}else{var _K4=E(_JZ[_K3]),_K5=__app2(E(_Jy),B(_kB(new T2(1,new T2(0,_AP,_K2.h),new T2(1,new T2(0,_AO,_K2.i),_w)))),B(_kB(new T2(1,new T2(0,_AP,_K4.h),new T2(1,new T2(0,_AO,_K4.i),_w))))),_K6=__arr2lst(0,_K5),_K7=B(_C3(_K6,_)),_K8=B(_JU(_K0.b,_JW,_JX,_JY,_JZ,_)),_K9=new T(function(){var _Ka=new T(function(){return _JN!=_K1;}),_Kb=function(_Kc){var _Kd=E(_Kc);if(!_Kd._){return __Z;}else{var _Ke=_Kd.b,_Kf=E(_Kd.a),_Kg=E(_Kf.b),_Kh=E(_Kf.a),_Ki=E(_Kf.c),_Kj=_Ki.a,_Kk=_Ki.b,_Kl=E(_Kf.e),_Km=E(_Kf.d),_Kn=_Km.a,_Ko=_Km.b,_Kp=E(_Kf.f),_Kq=new T(function(){var _Kr=B(_lo(_jP,_Kp.a,_Kp.b,_Kp.c)),_Ks=Math.sqrt(B(_J5(_jP,_Kn,_Ko,_Kn,_Ko)));return new T3(0,_Ks*E(_Kr.a),_Ks*E(_Kr.b),_Ks*E(_Kr.c));}),_Kt=new T(function(){var _Ku=B(_lo(_jP,_Kl.a,_Kl.b,_Kl.c)),_Kv=Math.sqrt(B(_J5(_jP,_Kj,_Kk,_Kj,_Kk)));return new T3(0,_Kv*E(_Ku.a),_Kv*E(_Ku.b),_Kv*E(_Ku.c));}),_Kw=new T(function(){var _Kx=B(A1(_JG,_Kg)),_Ky=B(_lo(_jP,_Kx.a,_Kx.b,_Kx.c));return new T3(0,E(_Ky.a),E(_Ky.b),E(_Ky.c));}),_Kz=new T(function(){var _KA=B(A1(_JG,_Kh)),_KB=B(_lo(_jP,_KA.a,_KA.b,_KA.c));return new T3(0,E(_KB.a),E(_KB.b),E(_KB.c));}),_KC=E(_Kg.a)+ -E(_Kh.a),_KD=E(_Kg.b)+ -E(_Kh.b),_KE=E(_Kg.c)+ -E(_Kh.c),_KF=new T(function(){return Math.sqrt(B(_le(_jP,_KC,_KD,_KE,_KC,_KD,_KE)));}),_KG=new T(function(){var _KH=1/E(_KF);return new T3(0,_KC*_KH,_KD*_KH,_KE*_KH);}),_KI=new T(function(){if(!E(_Kf.g)){return E(_KG);}else{var _KJ=E(_KG);return new T3(0,-1*E(_KJ.a),-1*E(_KJ.b),-1*E(_KJ.c));}}),_KK=new T(function(){if(!E(_Kf.h)){return E(_KG);}else{var _KL=E(_KG);return new T3(0,-1*E(_KL.a),-1*E(_KL.b),-1*E(_KL.c));}});return (!E(_Ka))?new T2(1,new T(function(){var _KM=E(_KI),_KN=E(_KM.b),_KO=E(_KM.c),_KP=E(_KM.a),_KQ=E(_Kz),_KR=E(_KQ.c),_KS=E(_KQ.b),_KT=E(_KQ.a),_KU=E(_Kt),_KV=E(_KU.c),_KW=E(_KU.b),_KX=E(_KU.a),_KY=_KN*_KR-_KS*_KO,_KZ=_KO*_KT-_KR*_KP,_L0=_KP*_KS-_KT*_KN,_L1=B(_le(_jP,_KZ*_KV-_KW*_L0,_L0*_KX-_KV*_KY,_KY*_KW-_KX*_KZ,_KT,_KS,_KR));return new T6(0,_JN,_K1,E(new T2(0,E(new T3(0,E(_KY),E(_KZ),E(_L0))),E(_L1))),E(_JE),_KF,_Jk);}),new T2(1,new T(function(){var _L2=E(_KK),_L3=E(_L2.b),_L4=E(_L2.c),_L5=E(_L2.a),_L6=E(_Kw),_L7=E(_L6.c),_L8=E(_L6.b),_L9=E(_L6.a),_La=E(_Kq),_Lb=E(_La.c),_Lc=E(_La.b),_Ld=E(_La.a),_Le=_L3*_L7-_L8*_L4,_Lf=_L4*_L9-_L7*_L5,_Lg=_L5*_L8-_L9*_L3,_Lh=B(_le(_jP,_Lf*_Lb-_Lc*_Lg,_Lg*_Ld-_Lb*_Le,_Le*_Lc-_Ld*_Lf,_L9,_L8,_L7));return new T6(0,_JN,_K1,E(_JE),E(new T2(0,E(new T3(0,E(_Le),E(_Lf),E(_Lg))),E(_Lh))),_KF,_Jk);}),new T(function(){return B(_Kb(_Ke));}))):new T2(1,new T(function(){var _Li=E(_KI),_Lj=E(_Li.b),_Lk=E(_Li.c),_Ll=E(_Li.a),_Lm=E(_Kz),_Ln=_Lm.a,_Lo=_Lm.b,_Lp=_Lm.c,_Lq=B(_me(_jP,_Ll,_Lj,_Lk,_Ln,_Lo,_Lp)),_Lr=E(_Kt),_Ls=E(_Lr.c),_Lt=E(_Lr.b),_Lu=E(_Lr.a),_Lv=B(_le(_jP,_Lj*_Ls-_Lt*_Lk,_Lk*_Lu-_Ls*_Ll,_Ll*_Lt-_Lu*_Lj,_Ln,_Lo,_Lp)),_Lw=E(_KK),_Lx=E(_Lw.b),_Ly=E(_Lw.c),_Lz=E(_Lw.a),_LA=E(_Kw),_LB=_LA.a,_LC=_LA.b,_LD=_LA.c,_LE=B(_me(_jP,_Lz,_Lx,_Ly,_LB,_LC,_LD)),_LF=E(_Kq),_LG=E(_LF.c),_LH=E(_LF.b),_LI=E(_LF.a),_LJ=B(_le(_jP,_Lx*_LG-_LH*_Ly,_Ly*_LI-_LG*_Lz,_Lz*_LH-_LI*_Lx,_LB,_LC,_LD));return new T6(0,_JN,_K1,E(new T2(0,E(new T3(0,E(_Lq.a),E(_Lq.b),E(_Lq.c))),E(_Lv))),E(new T2(0,E(new T3(0,E(_LE.a),E(_LE.b),E(_LE.c))),E(_LJ))),_KF,_Jl);}),new T(function(){return B(_Kb(_Ke));}));}};return B(_Kb(_K7));});return new T2(0,new T2(1,_K9,new T(function(){return E(E(_K8).a);})),new T(function(){return E(E(_K8).b);}));}}}}}},_LK=B(_JU(B(_sJ(_JN,_JL)),_JO,_JP,_JQ,_JR,_)),_LL=E(_JS),_LM=E(_LL.d).a,_LN=__app1(E(_Jw),B(_kB(new T2(1,new T2(0,_AP,_LL.h),new T2(1,new T2(0,_AO,_LL.i),_w))))),_LO=__arr2lst(0,_LN),_LP=B(_C3(_LO,_)),_LQ=__app1(E(_Jx),_JN),_LR=__arr2lst(0,_LQ),_LS=B(_C3(_LR,_));if(_JN!=_JL){var _LT=E(_LK),_LU=E(_LT.b),_LV=B(_JM(_JN+1|0,E(_LU.a),E(_LU.b),_LU.c,_LU.d,_)),_LW=new T(function(){var _LX=new T(function(){var _LY=B(A1(_JG,_LM)),_LZ=B(_lo(_jP,_LY.a,_LY.b,_LY.c));return new T3(0,E(_LZ.a),E(_LZ.b),E(_LZ.c));}),_M0=new T(function(){var _M1=new T(function(){return B(_Jz(_LT.a));}),_M2=function(_M3){var _M4=E(_M3);if(!_M4._){return E(_M1);}else{var _M5=E(_M4.a),_M6=E(_M5.b),_M7=E(_M5.a),_M8=E(_M5.c),_M9=_M8.a,_Ma=_M8.b,_Mb=E(_M5.e);return new T2(1,new T(function(){var _Mc=E(_M6.a)+ -E(_M7.a),_Md=E(_M6.b)+ -E(_M7.b),_Me=E(_M6.c)+ -E(_M7.c),_Mf=B(A1(_JG,_M7)),_Mg=B(_lo(_jP,_Mf.a,_Mf.b,_Mf.c)),_Mh=_Mg.a,_Mi=_Mg.b,_Mj=_Mg.c,_Mk=Math.sqrt(B(_le(_jP,_Mc,_Md,_Me,_Mc,_Md,_Me))),_Ml=1/_Mk,_Mm=_Mc*_Ml,_Mn=_Md*_Ml,_Mo=_Me*_Ml,_Mp=B(_me(_jP,_Mm,_Mn,_Mo,_Mh,_Mi,_Mj)),_Mq=B(_lo(_jP,_Mb.a,_Mb.b,_Mb.c)),_Mr=Math.sqrt(B(_J5(_jP,_M9,_Ma,_M9,_Ma))),_Ms=_Mr*E(_Mq.a),_Mt=_Mr*E(_Mq.b),_Mu=_Mr*E(_Mq.c),_Mv=B(_le(_jP,_Mn*_Mu-_Mt*_Mo,_Mo*_Ms-_Mu*_Mm,_Mm*_Mt-_Ms*_Mn,_Mh,_Mi,_Mj));return new T6(0,_JN,_JN,E(new T2(0,E(new T3(0,E(_Mp.a),E(_Mp.b),E(_Mp.c))),E(_Mv))),E(_JE),_Mk,_Jl);}),new T(function(){return B(_M2(_M4.b));}));}};return B(_M2(_LP));}),_Mw=function(_Mx){var _My=E(_Mx);if(!_My._){return E(_M0);}else{var _Mz=E(_My.a),_MA=E(_Mz.b),_MB=new T(function(){var _MC=E(_LM),_MD=E(_MA.c)+ -E(_MC.c),_ME=E(_MA.b)+ -E(_MC.b),_MF=E(_MA.a)+ -E(_MC.a),_MG=Math.sqrt(B(_le(_jP,_MF,_ME,_MD,_MF,_ME,_MD))),_MH=function(_MI,_MJ,_MK){var _ML=E(_LX),_MM=_ML.a,_MN=_ML.b,_MO=_ML.c,_MP=B(_me(_jP,_MI,_MJ,_MK,_MM,_MN,_MO)),_MQ=B(_le(_jP,_MJ*0-0*_MK,_MK*0-0*_MI,_MI*0-0*_MJ,_MM,_MN,_MO));return new T6(0,_JN,_JN,new T2(0,E(new T3(0,E(_MP.a),E(_MP.b),E(_MP.c))),E(_MQ)),_JE,_MG,_Jl);};if(!E(_Mz.g)){var _MR=1/_MG,_MS=B(_MH(_MF*_MR,_ME*_MR,_MD*_MR));return new T6(0,_MS.a,_MS.b,E(_MS.c),E(_MS.d),_MS.e,_MS.f);}else{var _MT=1/_MG,_MU=B(_MH(-1*_MF*_MT,-1*_ME*_MT,-1*_MD*_MT));return new T6(0,_MU.a,_MU.b,E(_MU.c),E(_MU.d),_MU.e,_MU.f);}});return new T2(1,_MB,new T(function(){return B(_Mw(_My.b));}));}};return B(_Mw(_LS));});return new T2(0,new T2(1,_LW,new T(function(){return E(E(_LV).a);})),new T(function(){return E(E(_LV).b);}));}else{var _MV=new T(function(){var _MW=new T(function(){var _MX=B(A1(_JG,_LM)),_MY=B(_lo(_jP,_MX.a,_MX.b,_MX.c));return new T3(0,E(_MY.a),E(_MY.b),E(_MY.c));}),_MZ=new T(function(){var _N0=new T(function(){return B(_Jz(E(_LK).a));}),_N1=function(_N2){var _N3=E(_N2);if(!_N3._){return E(_N0);}else{var _N4=E(_N3.a),_N5=E(_N4.b),_N6=E(_N4.a),_N7=E(_N4.c),_N8=_N7.a,_N9=_N7.b,_Na=E(_N4.e);return new T2(1,new T(function(){var _Nb=E(_N5.a)+ -E(_N6.a),_Nc=E(_N5.b)+ -E(_N6.b),_Nd=E(_N5.c)+ -E(_N6.c),_Ne=B(A1(_JG,_N6)),_Nf=B(_lo(_jP,_Ne.a,_Ne.b,_Ne.c)),_Ng=_Nf.a,_Nh=_Nf.b,_Ni=_Nf.c,_Nj=Math.sqrt(B(_le(_jP,_Nb,_Nc,_Nd,_Nb,_Nc,_Nd))),_Nk=1/_Nj,_Nl=_Nb*_Nk,_Nm=_Nc*_Nk,_Nn=_Nd*_Nk,_No=B(_me(_jP,_Nl,_Nm,_Nn,_Ng,_Nh,_Ni)),_Np=B(_lo(_jP,_Na.a,_Na.b,_Na.c)),_Nq=Math.sqrt(B(_J5(_jP,_N8,_N9,_N8,_N9))),_Nr=_Nq*E(_Np.a),_Ns=_Nq*E(_Np.b),_Nt=_Nq*E(_Np.c),_Nu=B(_le(_jP,_Nm*_Nt-_Ns*_Nn,_Nn*_Nr-_Nt*_Nl,_Nl*_Ns-_Nr*_Nm,_Ng,_Nh,_Ni));return new T6(0,_JN,_JN,E(new T2(0,E(new T3(0,E(_No.a),E(_No.b),E(_No.c))),E(_Nu))),E(_JE),_Nj,_Jl);}),new T(function(){return B(_N1(_N3.b));}));}};return B(_N1(_LP));}),_Nv=function(_Nw){var _Nx=E(_Nw);if(!_Nx._){return E(_MZ);}else{var _Ny=E(_Nx.a),_Nz=E(_Ny.b),_NA=new T(function(){var _NB=E(_LM),_NC=E(_Nz.c)+ -E(_NB.c),_ND=E(_Nz.b)+ -E(_NB.b),_NE=E(_Nz.a)+ -E(_NB.a),_NF=Math.sqrt(B(_le(_jP,_NE,_ND,_NC,_NE,_ND,_NC))),_NG=function(_NH,_NI,_NJ){var _NK=E(_MW),_NL=_NK.a,_NM=_NK.b,_NN=_NK.c,_NO=B(_me(_jP,_NH,_NI,_NJ,_NL,_NM,_NN)),_NP=B(_le(_jP,_NI*0-0*_NJ,_NJ*0-0*_NH,_NH*0-0*_NI,_NL,_NM,_NN));return new T6(0,_JN,_JN,new T2(0,E(new T3(0,E(_NO.a),E(_NO.b),E(_NO.c))),E(_NP)),_JE,_NF,_Jl);};if(!E(_Ny.g)){var _NQ=1/_NF,_NR=B(_NG(_NE*_NQ,_ND*_NQ,_NC*_NQ));return new T6(0,_NR.a,_NR.b,E(_NR.c),E(_NR.d),_NR.e,_NR.f);}else{var _NS=1/_NF,_NT=B(_NG(-1*_NE*_NS,-1*_ND*_NS,-1*_NC*_NS));return new T6(0,_NT.a,_NT.b,E(_NT.c),E(_NT.d),_NT.e,_NT.f);}});return new T2(1,_NA,new T(function(){return B(_Nv(_Nx.b));}));}};return B(_Nv(_LS));});return new T2(0,new T2(1,_MV,_w),new T(function(){return E(E(_LK).b);}));}}}},_NU=B(_JM(_JK,_JK,_JL,_JJ.c,_JJ.d,_));return new F(function(){return _IX(_,_NU);});}else{return new F(function(){return _IX(_,new T2(0,_w,_JJ));});}},_NV=new T(function(){return eval("__strict(passObject)");}),_NW=new T(function(){return eval("__strict(refresh)");}),_NX=function(_NY,_){var _NZ=__app0(E(_NW)),_O0=__app0(E(_AT)),_O1=E(_NY),_O2=_O1.c,_O3=_O1.d,_O4=E(_O1.a),_O5=E(_O1.b);if(_O4<=_O5){if(_O4>_O5){return E(_AR);}else{if(0>=_O2){return new F(function(){return _B4(_O2,0);});}else{var _O6=E(_O3[0]),_O7=E(_NV),_O8=__app2(_O7,_O4,B(_kB(new T2(1,new T2(0,_AP,_O6.h),new T2(1,new T2(0,_AO,_O6.i),_w)))));if(_O4!=_O5){var _O9=function(_Oa,_){if(_O4>_Oa){return E(_AR);}else{if(_Oa>_O5){return E(_AR);}else{var _Ob=_Oa-_O4|0;if(0>_Ob){return new F(function(){return _B4(_O2,_Ob);});}else{if(_Ob>=_O2){return new F(function(){return _B4(_O2,_Ob);});}else{var _Oc=E(_O3[_Ob]),_Od=__app2(_O7,_Oa,B(_kB(new T2(1,new T2(0,_AP,_Oc.h),new T2(1,new T2(0,_AO,_Oc.i),_w)))));if(_Oa!=_O5){var _Oe=B(_O9(_Oa+1|0,_));return new T2(1,_kA,_Oe);}else{return _B9;}}}}}},_Of=B(_O9(_O4+1|0,_)),_Og=__app0(E(_AS)),_Oh=B(_JH(_O1,_));return new T(function(){return E(E(_Oh).b);});}else{var _Oi=__app0(E(_AS)),_Oj=B(_JH(_O1,_));return new T(function(){return E(E(_Oj).b);});}}}}else{var _Ok=__app0(E(_AS)),_Ol=B(_JH(_O1,_));return new T(function(){return E(E(_Ol).b);});}},_Om=function(_On,_){while(1){var _Oo=E(_On);if(!_Oo._){return _kA;}else{var _Op=_Oo.b,_Oq=E(_Oo.a);switch(_Oq._){case 0:var _Or=B(A1(_Oq.a,_));_On=B(_n(_Op,new T2(1,_Or,_w)));continue;case 1:_On=B(_n(_Op,_Oq.a));continue;default:_On=_Op;continue;}}}},_Os=function(_Ot,_Ou,_){var _Ov=E(_Ot);switch(_Ov._){case 0:var _Ow=B(A1(_Ov.a,_));return new F(function(){return _Om(B(_n(_Ou,new T2(1,_Ow,_w))),_);});break;case 1:return new F(function(){return _Om(B(_n(_Ou,_Ov.a)),_);});break;default:return new F(function(){return _Om(_Ou,_);});}},_Ox=new T0(2),_Oy=function(_Oz){return new T0(2);},_OA=function(_OB,_OC,_OD){return function(_){var _OE=E(_OB),_OF=rMV(_OE),_OG=E(_OF);if(!_OG._){var _OH=new T(function(){var _OI=new T(function(){return B(A1(_OD,_kA));});return B(_n(_OG.b,new T2(1,new T2(0,_OC,function(_OJ){return E(_OI);}),_w)));}),_=wMV(_OE,new T2(0,_OG.a,_OH));return _Ox;}else{var _OK=E(_OG.a);if(!_OK._){var _=wMV(_OE,new T2(0,_OC,_w));return new T(function(){return B(A1(_OD,_kA));});}else{var _=wMV(_OE,new T1(1,_OK.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OD,_kA));}),new T2(1,new T(function(){return B(A2(_OK.a,_OC,_Oy));}),_w)));}}};},_OL=new T(function(){return E(_qe);}),_OM=new T(function(){return eval("window.requestAnimationFrame");}),_ON=new T1(1,_w),_OO=function(_OP,_OQ){return function(_){var _OR=E(_OP),_OS=rMV(_OR),_OT=E(_OS);if(!_OT._){var _OU=_OT.a,_OV=E(_OT.b);if(!_OV._){var _=wMV(_OR,_ON);return new T(function(){return B(A1(_OQ,_OU));});}else{var _OW=E(_OV.a),_=wMV(_OR,new T2(0,_OW.a,_OV.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OQ,_OU));}),new T2(1,new T(function(){return B(A1(_OW.b,_Oy));}),_w)));}}else{var _OX=new T(function(){var _OY=function(_OZ){var _P0=new T(function(){return B(A1(_OQ,_OZ));});return function(_P1){return E(_P0);};};return B(_n(_OT.a,new T2(1,_OY,_w)));}),_=wMV(_OR,new T1(1,_OX));return _Ox;}};},_P2=function(_P3,_P4){return new T1(0,B(_OO(_P3,_P4)));},_P5=function(_P6,_P7){var _P8=new T(function(){return new T1(0,B(_OA(_P6,_kA,_Oy)));});return function(_){var _P9=__createJSFunc(2,function(_Pa,_){var _Pb=B(_Os(_P8,_w,_));return _OL;}),_Pc=__app1(E(_OM),_P9);return new T(function(){return B(_P2(_P6,_P7));});};},_Pd=new T1(1,_w),_Pe=function(_Pf,_Pg,_){var _Ph=function(_){var _Pi=nMV(_Pf),_Pj=_Pi;return new T(function(){var _Pk=new T(function(){return B(_Pl(_));}),_Pm=function(_){var _Pn=rMV(_Pj),_Po=B(A2(_Pg,_Pn,_)),_=wMV(_Pj,_Po),_Pp=function(_){var _Pq=nMV(_Pd);return new T(function(){return new T1(0,B(_P5(_Pq,function(_Pr){return E(_Pk);})));});};return new T1(0,_Pp);},_Ps=new T(function(){return new T1(0,_Pm);}),_Pl=function(_Pt){return E(_Ps);};return B(_Pl(_));});};return new F(function(){return _Os(new T1(0,_Ph),_w,_);});},_Pu=new T(function(){return eval("__strict(setBounds)");}),_Pv=function(_){var _Pw=__app3(E(_20),E(_91),E(_ib),E(_1Z)),_Px=__app2(E(_Pu),E(_1u),E(_1n));return new F(function(){return _Pe(_AN,_NX,_);});},_Py=function(_){return new F(function(){return _Pv(_);});};
var hasteMain = function() {B(A(_Py, [0]));};window.onload = hasteMain;