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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x,_8y,_8z,_8A,_8B,_8C,_8D){var _8E=B(_8s(B(_8q(_8x)))),_8F=new T(function(){return B(A3(_86,_8E,new T(function(){return B(A3(_8u,_8E,_8y,_8B));}),new T(function(){return B(A3(_8u,_8E,_8z,_8C));})));});return new F(function(){return A3(_86,_8E,_8F,new T(function(){return B(A3(_8u,_8E,_8A,_8D));}));});},_8G=function(_8H){return E(E(_8H).b);},_8I=function(_8J){return E(E(_8J).g);},_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O){var _8P=B(_8s(B(_8q(_8N)))),_8Q=new T(function(){return B(A2(_8K,_8N,new T(function(){var _8R=E(_8O),_8S=_8R.a,_8T=_8R.b,_8U=_8R.c;return B(_8w(_8N,_8S,_8T,_8U,_8S,_8T,_8U));})));});return new F(function(){return A3(_8G,_8P,_8Q,new T(function(){return B(A2(_8I,_8P,_1o));}));});},_8V=new T(function(){return B(unCStr("x"));}),_8W=new T1(0,_8V),_8X=new T(function(){return B(unCStr("y"));}),_8Y=new T1(0,_8X),_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T3(0,E(_8W),E(_8Y),E(_90)),_92=new T(function(){return B(_8M(_8p,_91));}),_93=new T(function(){return toJSStr(B(_1v(_x,_1l,_92)));}),_94=new T(function(){return B(unCStr("(/=) is not defined"));}),_95=new T(function(){return B(err(_94));}),_96=new T(function(){return B(unCStr("(==) is not defined"));}),_97=new T(function(){return B(err(_96));}),_98=new T2(0,_97,_95),_99=new T(function(){return B(unCStr("(<) is not defined"));}),_9a=new T(function(){return B(err(_99));}),_9b=new T(function(){return B(unCStr("(<=) is not defined"));}),_9c=new T(function(){return B(err(_9b));}),_9d=new T(function(){return B(unCStr("(>) is not defined"));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("(>=) is not defined"));}),_9g=new T(function(){return B(err(_9f));}),_9h=new T(function(){return B(unCStr("compare is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("max("));}),_9k=new T1(0,_9j),_9l=function(_9m,_9n){return new T1(1,new T2(1,_9k,new T2(1,_9m,new T2(1,_22,new T2(1,_9n,_1S)))));},_9o=new T(function(){return B(unCStr("min("));}),_9p=new T1(0,_9o),_9q=function(_9r,_9s){return new T1(1,new T2(1,_9p,new T2(1,_9r,new T2(1,_22,new T2(1,_9s,_1S)))));},_9t={_:0,a:_98,b:_9i,c:_9a,d:_9c,e:_9e,f:_9g,g:_9l,h:_9q},_9u=new T2(0,_8p,_9t),_9v=function(_9w,_9x){var _9y=E(_9w);return E(_9x);},_9z=function(_9A,_9B){var _9C=E(_9B);return E(_9A);},_9D=function(_9E,_9F){var _9G=E(_9E),_9H=E(_9F);return new T3(0,E(B(A1(_9G.a,_9H.a))),E(B(A1(_9G.b,_9H.b))),E(B(A1(_9G.c,_9H.c))));},_9I=function(_9J,_9K,_9L){return new T3(0,E(_9J),E(_9K),E(_9L));},_9M=function(_9N){return new F(function(){return _9I(_9N,_9N,_9N);});},_9O=function(_9P,_9Q){var _9R=E(_9Q),_9S=E(_9P);return new T3(0,E(_9S),E(_9S),E(_9S));},_9T=function(_9U,_9V){var _9W=E(_9V);return new T3(0,E(B(A1(_9U,_9W.a))),E(B(A1(_9U,_9W.b))),E(B(A1(_9U,_9W.c))));},_9X=new T2(0,_9T,_9O),_9Y=new T5(0,_9X,_9M,_9D,_9v,_9z),_9Z=new T1(0,0),_a0=function(_a1){var _a2=B(A2(_8I,_a1,_1o)),_a3=B(A2(_8I,_a1,_9Z));return new T3(0,E(new T3(0,E(_a2),E(_a3),E(_a3))),E(new T3(0,E(_a3),E(_a2),E(_a3))),E(new T3(0,E(_a3),E(_a3),E(_a2))));},_a4=function(_a5){return E(E(_a5).a);},_a6=function(_a7){return E(E(_a7).f);},_a8=function(_a9){return E(E(_a9).b);},_aa=function(_ab){return E(E(_ab).c);},_ac=function(_ad){return E(E(_ad).a);},_ae=function(_af){return E(E(_af).d);},_ag=function(_ah,_ai,_aj,_ak,_al){var _am=new T(function(){return E(E(E(_ah).c).a);}),_an=new T(function(){var _ao=E(_ah).a,_ap=new T(function(){var _aq=new T(function(){return B(_8q(_am));}),_ar=new T(function(){return B(_8s(_aq));}),_as=new T(function(){return B(A2(_ae,_am,_ai));}),_at=new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_au=function(_av,_aw){var _ax=new T(function(){var _ay=new T(function(){return B(A3(_a8,_aq,new T(function(){return B(A3(_8u,_ar,_ak,_av));}),_ai));});return B(A3(_86,_ar,_ay,new T(function(){return B(A3(_8u,_ar,_aw,_as));})));});return new F(function(){return A3(_8u,_ar,_at,_ax);});};return B(A3(_ac,B(_a4(_ao)),_au,_aj));});return B(A3(_aa,_ao,_ap,_al));});return new T2(0,new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_an);},_az=function(_aA,_aB,_aC,_aD){var _aE=E(_aC),_aF=E(_aD),_aG=B(_ag(_aB,_aE.a,_aE.b,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=new T1(0,1),_aI=function(_aJ){return E(E(_aJ).l);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8q(_aO));}),_aR=new T(function(){var _aS=B(_8s(_aQ)),_aT=new T(function(){var _aU=new T(function(){return B(A3(_8G,_aS,new T(function(){return B(A2(_8I,_aS,_aH));}),new T(function(){return B(A3(_8u,_aS,_aM,_aM));})));});return B(A2(_8K,_aO,_aU));});return B(A2(_88,_aS,_aT));});return B(A3(_ac,B(_a4(E(_aL).a)),function(_aV){return new F(function(){return A3(_a8,_aQ,_aV,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aW=function(_aX,_aY,_aZ){var _b0=E(_aZ),_b1=B(_aK(_aY,_b0.a,_b0.b));return new T2(0,_b1.a,_b1.b);},_b2=function(_b3){return E(E(_b3).r);},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return E(E(E(_b5).c).a);}),_b9=new T(function(){var _ba=new T(function(){return B(_8q(_b8));}),_bb=new T(function(){var _bc=new T(function(){var _bd=B(_8s(_ba));return B(A3(_8G,_bd,new T(function(){return B(A3(_8u,_bd,_b6,_b6));}),new T(function(){return B(A2(_8I,_bd,_aH));})));});return B(A2(_8K,_b8,_bc));});return B(A3(_ac,B(_a4(E(_b5).a)),function(_be){return new F(function(){return A3(_a8,_ba,_be,_bb);});},_b7));});return new T2(0,new T(function(){return B(A2(_b2,_b8,_b6));}),_b9);},_bf=function(_bg,_bh,_bi){var _bj=E(_bi),_bk=B(_b4(_bh,_bj.a,_bj.b));return new T2(0,_bk.a,_bk.b);},_bl=function(_bm){return E(E(_bm).k);},_bn=function(_bo,_bp,_bq){var _br=new T(function(){return E(E(E(_bo).c).a);}),_bs=new T(function(){var _bt=new T(function(){return B(_8q(_br));}),_bu=new T(function(){var _bv=new T(function(){var _bw=B(_8s(_bt));return B(A3(_8G,_bw,new T(function(){return B(A2(_8I,_bw,_aH));}),new T(function(){return B(A3(_8u,_bw,_bp,_bp));})));});return B(A2(_8K,_br,_bv));});return B(A3(_ac,B(_a4(E(_bo).a)),function(_bx){return new F(function(){return A3(_a8,_bt,_bx,_bu);});},_bq));});return new T2(0,new T(function(){return B(A2(_bl,_br,_bp));}),_bs);},_by=function(_bz,_bA,_bB){var _bC=E(_bB),_bD=B(_bn(_bA,_bC.a,_bC.b));return new T2(0,_bD.a,_bD.b);},_bE=function(_bF){return E(E(_bF).q);},_bG=function(_bH,_bI,_bJ){var _bK=new T(function(){return E(E(E(_bH).c).a);}),_bL=new T(function(){var _bM=new T(function(){return B(_8q(_bK));}),_bN=new T(function(){var _bO=new T(function(){var _bP=B(_8s(_bM));return B(A3(_86,_bP,new T(function(){return B(A3(_8u,_bP,_bI,_bI));}),new T(function(){return B(A2(_8I,_bP,_aH));})));});return B(A2(_8K,_bK,_bO));});return B(A3(_ac,B(_a4(E(_bH).a)),function(_bQ){return new F(function(){return A3(_a8,_bM,_bQ,_bN);});},_bJ));});return new T2(0,new T(function(){return B(A2(_bE,_bK,_bI));}),_bL);},_bR=function(_bS,_bT,_bU){var _bV=E(_bU),_bW=B(_bG(_bT,_bV.a,_bV.b));return new T2(0,_bW.a,_bW.b);},_bX=function(_bY){return E(E(_bY).m);},_bZ=function(_c0,_c1,_c2){var _c3=new T(function(){return E(E(E(_c0).c).a);}),_c4=new T(function(){var _c5=new T(function(){return B(_8q(_c3));}),_c6=new T(function(){var _c7=B(_8s(_c5));return B(A3(_86,_c7,new T(function(){return B(A2(_8I,_c7,_aH));}),new T(function(){return B(A3(_8u,_c7,_c1,_c1));})));});return B(A3(_ac,B(_a4(E(_c0).a)),function(_c8){return new F(function(){return A3(_a8,_c5,_c8,_c6);});},_c2));});return new T2(0,new T(function(){return B(A2(_bX,_c3,_c1));}),_c4);},_c9=function(_ca,_cb,_cc){var _cd=E(_cc),_ce=B(_bZ(_cb,_cd.a,_cd.b));return new T2(0,_ce.a,_ce.b);},_cf=function(_cg){return E(E(_cg).s);},_ch=function(_ci,_cj,_ck){var _cl=new T(function(){return E(E(E(_ci).c).a);}),_cm=new T(function(){var _cn=new T(function(){return B(_8q(_cl));}),_co=new T(function(){var _cp=B(_8s(_cn));return B(A3(_8G,_cp,new T(function(){return B(A2(_8I,_cp,_aH));}),new T(function(){return B(A3(_8u,_cp,_cj,_cj));})));});return B(A3(_ac,B(_a4(E(_ci).a)),function(_cq){return new F(function(){return A3(_a8,_cn,_cq,_co);});},_ck));});return new T2(0,new T(function(){return B(A2(_cf,_cl,_cj));}),_cm);},_cr=function(_cs,_ct,_cu){var _cv=E(_cu),_cw=B(_ch(_ct,_cv.a,_cv.b));return new T2(0,_cw.a,_cw.b);},_cx=function(_cy){return E(E(_cy).i);},_cz=function(_cA){return E(E(_cA).h);},_cB=function(_cC,_cD,_cE){var _cF=new T(function(){return E(E(E(_cC).c).a);}),_cG=new T(function(){var _cH=new T(function(){return B(_8s(new T(function(){return B(_8q(_cF));})));}),_cI=new T(function(){return B(A2(_88,_cH,new T(function(){return B(A2(_cz,_cF,_cD));})));});return B(A3(_ac,B(_a4(E(_cC).a)),function(_cJ){return new F(function(){return A3(_8u,_cH,_cJ,_cI);});},_cE));});return new T2(0,new T(function(){return B(A2(_cx,_cF,_cD));}),_cG);},_cK=function(_cL,_cM,_cN){var _cO=E(_cN),_cP=B(_cB(_cM,_cO.a,_cO.b));return new T2(0,_cP.a,_cP.b);},_cQ=function(_cR){return E(E(_cR).o);},_cS=function(_cT){return E(E(_cT).n);},_cU=function(_cV,_cW,_cX){var _cY=new T(function(){return E(E(E(_cV).c).a);}),_cZ=new T(function(){var _d0=new T(function(){return B(_8s(new T(function(){return B(_8q(_cY));})));}),_d1=new T(function(){return B(A2(_cS,_cY,_cW));});return B(A3(_ac,B(_a4(E(_cV).a)),function(_d2){return new F(function(){return A3(_8u,_d0,_d2,_d1);});},_cX));});return new T2(0,new T(function(){return B(A2(_cQ,_cY,_cW));}),_cZ);},_d3=function(_d4,_d5,_d6){var _d7=E(_d6),_d8=B(_cU(_d5,_d7.a,_d7.b));return new T2(0,_d8.a,_d8.b);},_d9=function(_da){return E(E(_da).c);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(E(_dc).c).a);}),_dg=new T(function(){var _dh=new T(function(){return B(_8s(new T(function(){return B(_8q(_df));})));}),_di=new T(function(){return B(A2(_d9,_df,_dd));});return B(A3(_ac,B(_a4(E(_dc).a)),function(_dj){return new F(function(){return A3(_8u,_dh,_dj,_di);});},_de));});return new T2(0,new T(function(){return B(A2(_d9,_df,_dd));}),_dg);},_dk=function(_dl,_dm,_dn){var _do=E(_dn),_dp=B(_db(_dm,_do.a,_do.b));return new T2(0,_dp.a,_dp.b);},_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_8q(_du));}),_dx=new T(function(){return B(_8s(_dw));}),_dy=new T(function(){return B(A3(_a8,_dw,new T(function(){return B(A2(_8I,_dx,_aH));}),_ds));});return B(A3(_ac,B(_a4(E(_dr).a)),function(_dz){return new F(function(){return A3(_8u,_dx,_dz,_dy);});},_dt));});return new T2(0,new T(function(){return B(A2(_ae,_du,_ds));}),_dv);},_dA=function(_dB,_dC,_dD){var _dE=E(_dD),_dF=B(_dq(_dC,_dE.a,_dE.b));return new T2(0,_dF.a,_dF.b);},_dG=function(_dH,_dI,_dJ,_dK){var _dL=new T(function(){return E(E(_dI).c);}),_dM=new T3(0,new T(function(){return E(E(_dI).a);}),new T(function(){return E(E(_dI).b);}),new T2(0,new T(function(){return E(E(_dL).a);}),new T(function(){return E(E(_dL).b);})));return new F(function(){return A3(_a8,_dH,new T(function(){var _dN=E(_dK),_dO=B(_dq(_dM,_dN.a,_dN.b));return new T2(0,_dO.a,_dO.b);}),new T(function(){var _dP=E(_dJ),_dQ=B(_dq(_dM,_dP.a,_dP.b));return new T2(0,_dQ.a,_dQ.b);}));});},_dR=function(_dS){return E(E(_dS).b);},_dT=function(_dU){return E(E(_dU).b);},_dV=function(_dW){var _dX=new T(function(){return E(E(E(_dW).c).a);}),_dY=new T(function(){return B(A2(_dT,E(_dW).a,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_dX)))),_L));})));});return new T2(0,new T(function(){return B(_dR(_dX));}),_dY);},_dZ=function(_e0,_e1){var _e2=B(_dV(_e1));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(E(_e4).c).a);}),_e8=new T(function(){var _e9=new T(function(){return B(_8s(new T(function(){return B(_8q(_e7));})));}),_ea=new T(function(){return B(A2(_cx,_e7,_e5));});return B(A3(_ac,B(_a4(E(_e4).a)),function(_eb){return new F(function(){return A3(_8u,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cz,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=function(_ej,_ek,_el){var _em=new T(function(){return E(E(E(_ej).c).a);}),_en=new T(function(){var _eo=new T(function(){return B(_8s(new T(function(){return B(_8q(_em));})));}),_ep=new T(function(){return B(A2(_cQ,_em,_ek));});return B(A3(_ac,B(_a4(E(_ej).a)),function(_eq){return new F(function(){return A3(_8u,_eo,_eq,_ep);});},_el));});return new T2(0,new T(function(){return B(A2(_cS,_em,_ek));}),_en);},_er=function(_es,_et,_eu){var _ev=E(_eu),_ew=B(_ei(_et,_ev.a,_ev.b));return new T2(0,_ew.a,_ew.b);},_ex=new T1(0,2),_ey=function(_ez,_eA,_eB){var _eC=new T(function(){return E(E(E(_ez).c).a);}),_eD=new T(function(){var _eE=new T(function(){return B(_8q(_eC));}),_eF=new T(function(){return B(_8s(_eE));}),_eG=new T(function(){var _eH=new T(function(){return B(A3(_a8,_eE,new T(function(){return B(A2(_8I,_eF,_aH));}),new T(function(){return B(A2(_8I,_eF,_ex));})));});return B(A3(_a8,_eE,_eH,new T(function(){return B(A2(_8K,_eC,_eA));})));});return B(A3(_ac,B(_a4(E(_ez).a)),function(_eI){return new F(function(){return A3(_8u,_eF,_eI,_eG);});},_eB));});return new T2(0,new T(function(){return B(A2(_8K,_eC,_eA));}),_eD);},_eJ=function(_eK,_eL,_eM){var _eN=E(_eM),_eO=B(_ey(_eL,_eN.a,_eN.b));return new T2(0,_eO.a,_eO.b);},_eP=function(_eQ){return E(E(_eQ).j);},_eR=function(_eS,_eT,_eU){var _eV=new T(function(){return E(E(E(_eS).c).a);}),_eW=new T(function(){var _eX=new T(function(){return B(_8q(_eV));}),_eY=new T(function(){var _eZ=new T(function(){return B(A2(_cx,_eV,_eT));});return B(A3(_8u,B(_8s(_eX)),_eZ,_eZ));});return B(A3(_ac,B(_a4(E(_eS).a)),function(_f0){return new F(function(){return A3(_a8,_eX,_f0,_eY);});},_eU));});return new T2(0,new T(function(){return B(A2(_eP,_eV,_eT));}),_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eR(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8){return E(E(_f8).p);},_f9=function(_fa,_fb,_fc){var _fd=new T(function(){return E(E(E(_fa).c).a);}),_fe=new T(function(){var _ff=new T(function(){return B(_8q(_fd));}),_fg=new T(function(){var _fh=new T(function(){return B(A2(_cQ,_fd,_fb));});return B(A3(_8u,B(_8s(_ff)),_fh,_fh));});return B(A3(_ac,B(_a4(E(_fa).a)),function(_fi){return new F(function(){return A3(_a8,_ff,_fi,_fg);});},_fc));});return new T2(0,new T(function(){return B(A2(_f7,_fd,_fb));}),_fe);},_fj=function(_fk,_fl,_fm){var _fn=E(_fm),_fo=B(_f9(_fl,_fn.a,_fn.b));return new T2(0,_fo.a,_fo.b);},_fp=function(_fq,_fr){return {_:0,a:_fq,b:new T(function(){return B(_dZ(_fq,_fr));}),c:function(_fs){return new F(function(){return _dk(_fq,_fr,_fs);});},d:function(_fs){return new F(function(){return _dA(_fq,_fr,_fs);});},e:function(_fs){return new F(function(){return _eJ(_fq,_fr,_fs);});},f:function(_ft,_fs){return new F(function(){return _az(_fq,_fr,_ft,_fs);});},g:function(_ft,_fs){return new F(function(){return _dG(_fq,_fr,_ft,_fs);});},h:function(_fs){return new F(function(){return _ec(_fq,_fr,_fs);});},i:function(_fs){return new F(function(){return _cK(_fq,_fr,_fs);});},j:function(_fs){return new F(function(){return _f1(_fq,_fr,_fs);});},k:function(_fs){return new F(function(){return _by(_fq,_fr,_fs);});},l:function(_fs){return new F(function(){return _aW(_fq,_fr,_fs);});},m:function(_fs){return new F(function(){return _c9(_fq,_fr,_fs);});},n:function(_fs){return new F(function(){return _er(_fq,_fr,_fs);});},o:function(_fs){return new F(function(){return _d3(_fq,_fr,_fs);});},p:function(_fs){return new F(function(){return _fj(_fq,_fr,_fs);});},q:function(_fs){return new F(function(){return _bR(_fq,_fr,_fs);});},r:function(_fs){return new F(function(){return _bf(_fq,_fr,_fs);});},s:function(_fs){return new F(function(){return _cr(_fq,_fr,_fs);});}};},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8q(new T(function(){return E(E(E(_fv).c).a);})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){var _fE=new T(function(){return B(_8s(_fA));}),_fF=new T(function(){return B(A3(_8u,_fE,_fy,_fy));}),_fG=function(_fH,_fI){var _fJ=new T(function(){return B(A3(_8G,_fE,new T(function(){return B(A3(_8u,_fE,_fH,_fy));}),new T(function(){return B(A3(_8u,_fE,_fw,_fI));})));});return new F(function(){return A3(_a8,_fA,_fJ,_fF);});};return B(A3(_ac,B(_a4(_fC)),_fG,_fx));});return B(A3(_aa,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_a8,_fA,_fw,_fy));}),_fB);},_fK=function(_fL,_fM,_fN,_fO){var _fP=E(_fN),_fQ=E(_fO),_fR=B(_fu(_fM,_fP.a,_fP.b,_fQ.a,_fQ.b));return new T2(0,_fR.a,_fR.b);},_fS=function(_fT){return E(E(_fT).d);},_fU=function(_fV,_fW){var _fX=new T(function(){return B(_8q(new T(function(){return E(E(E(_fV).c).a);})));}),_fY=new T(function(){return B(A2(_dT,E(_fV).a,new T(function(){return B(A2(_8I,B(_8s(_fX)),_L));})));});return new T2(0,new T(function(){return B(A2(_fS,_fX,_fW));}),_fY);},_fZ=function(_g0,_g1,_g2){var _g3=B(_fU(_g1,_g2));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6,_g7){var _g8=new T(function(){return B(_8q(new T(function(){return E(E(E(_g5).c).a);})));}),_g9=new T(function(){return B(_8s(_g8));}),_ga=new T(function(){var _gb=new T(function(){var _gc=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),new T(function(){return B(A3(_8u,_g9,_g6,_g6));})));});return B(A2(_88,_g9,_gc));});return B(A3(_ac,B(_a4(E(_g5).a)),function(_gd){return new F(function(){return A3(_8u,_g9,_gd,_gb);});},_g7));}),_ge=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),_g6));});return new T2(0,_ge,_ga);},_gf=function(_gg,_gh,_gi){var _gj=E(_gi),_gk=B(_g4(_gh,_gj.a,_gj.b));return new T2(0,_gk.a,_gk.b);},_gl=function(_gm,_gn){return new T4(0,_gm,function(_ft,_fs){return new F(function(){return _fK(_gm,_gn,_ft,_fs);});},function(_fs){return new F(function(){return _gf(_gm,_gn,_fs);});},function(_fs){return new F(function(){return _fZ(_gm,_gn,_fs);});});},_go=function(_gp,_gq,_gr,_gs,_gt){var _gu=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gv=new T(function(){var _gw=E(_gp).a,_gx=new T(function(){var _gy=function(_gz,_gA){return new F(function(){return A3(_86,_gu,new T(function(){return B(A3(_8u,_gu,_gq,_gA));}),new T(function(){return B(A3(_8u,_gu,_gz,_gs));}));});};return B(A3(_ac,B(_a4(_gw)),_gy,_gr));});return B(A3(_aa,_gw,_gx,_gt));});return new T2(0,new T(function(){return B(A3(_8u,_gu,_gq,_gs));}),_gv);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_go(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL,_gM,_gN){var _gO=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gP=new T(function(){var _gQ=E(_gJ).a,_gR=new T(function(){return B(A3(_ac,B(_a4(_gQ)),new T(function(){return B(_86(_gO));}),_gL));});return B(A3(_aa,_gQ,_gR,_gN));});return new T2(0,new T(function(){return B(A3(_86,_gO,_gK,_gM));}),_gP);},_gS=function(_gT,_gU,_gV){var _gW=E(_gU),_gX=E(_gV),_gY=B(_gI(_gT,_gW.a,_gW.b,_gX.a,_gX.b));return new T2(0,_gY.a,_gY.b);},_gZ=function(_h0,_h1,_h2){var _h3=B(_h4(_h0));return new F(function(){return A3(_86,_h3,_h1,new T(function(){return B(A2(_88,_h3,_h2));}));});},_h5=function(_h6){return E(E(_h6).e);},_h7=function(_h8){return E(E(_h8).f);},_h9=function(_ha,_hb,_hc){var _hd=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_ha).c).a);})));})));}),_he=new T(function(){var _hf=new T(function(){return B(A2(_h7,_hd,_hb));});return B(A3(_ac,B(_a4(E(_ha).a)),function(_hg){return new F(function(){return A3(_8u,_hd,_hg,_hf);});},_hc));});return new T2(0,new T(function(){return B(A2(_h5,_hd,_hb));}),_he);},_hh=function(_hi,_hj){var _hk=E(_hj),_hl=B(_h9(_hi,_hk.a,_hk.b));return new T2(0,_hl.a,_hl.b);},_hm=function(_hn,_ho){var _hp=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hn).c).a);})));})));}),_hq=new T(function(){return B(A2(_dT,E(_hn).a,new T(function(){return B(A2(_8I,_hp,_L));})));});return new T2(0,new T(function(){return B(A2(_8I,_hp,_ho));}),_hq);},_hr=function(_hs,_ht){var _hu=B(_hm(_hs,_ht));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy){var _hz=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hA=new T(function(){return B(A3(_ac,B(_a4(E(_hw).a)),new T(function(){return B(_88(_hz));}),_hy));});return new T2(0,new T(function(){return B(A2(_88,_hz,_hx));}),_hA);},_hB=function(_hC,_hD){var _hE=E(_hD),_hF=B(_hv(_hC,_hE.a,_hE.b));return new T2(0,_hF.a,_hF.b);},_hG=function(_hH,_hI){var _hJ=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hH).c).a);})));})));}),_hK=new T(function(){return B(A2(_dT,E(_hH).a,new T(function(){return B(A2(_8I,_hJ,_L));})));});return new T2(0,new T(function(){return B(A2(_h7,_hJ,_hI));}),_hK);},_hL=function(_hM,_hN){var _hO=B(_hG(_hM,E(_hN).a));return new T2(0,_hO.a,_hO.b);},_h4=function(_hP){return {_:0,a:function(_ft,_fs){return new F(function(){return _gS(_hP,_ft,_fs);});},b:function(_ft,_fs){return new F(function(){return _gZ(_hP,_ft,_fs);});},c:function(_ft,_fs){return new F(function(){return _gB(_hP,_ft,_fs);});},d:function(_fs){return new F(function(){return _hB(_hP,_fs);});},e:function(_fs){return new F(function(){return _hh(_hP,_fs);});},f:function(_fs){return new F(function(){return _hL(_hP,_fs);});},g:function(_fs){return new F(function(){return _hr(_hP,_fs);});}};},_hQ=function(_hR){var _hS=new T(function(){return E(E(_hR).a);}),_hT=new T3(0,_9Y,_a0,new T2(0,_hS,new T(function(){return E(E(_hR).b);}))),_hU=new T(function(){return B(_fp(new T(function(){return B(_gl(new T(function(){return B(_h4(_hT));}),_hT));}),_hT));}),_hV=new T(function(){return B(_8s(new T(function(){return B(_8q(_hS));})));}),_hW=function(_hX){return E(B(_8M(_hU,new T(function(){var _hY=E(_hX),_hZ=B(A2(_8I,_hV,_1o)),_i0=B(A2(_8I,_hV,_9Z));return new T3(0,E(new T2(0,_hY.a,new T3(0,E(_hZ),E(_i0),E(_i0)))),E(new T2(0,_hY.b,new T3(0,E(_i0),E(_hZ),E(_i0)))),E(new T2(0,_hY.c,new T3(0,E(_i0),E(_i0),E(_hZ)))));}))).b);};return E(_hW);},_i1=new T(function(){return B(_hQ(_9u));}),_i2=function(_i3,_i4){var _i5=E(_i4);return (_i5._==0)?__Z:new T2(1,_i3,new T2(1,_i5.a,new T(function(){return B(_i2(_i3,_i5.b));})));},_i6=new T(function(){var _i7=B(A1(_i1,_91));return new T2(1,_i7.a,new T(function(){return B(_i2(_22,new T2(1,_i7.b,new T2(1,_i7.c,_w))));}));}),_i8=new T1(1,_i6),_i9=new T2(1,_i8,_1S),_ia=new T(function(){return B(unCStr("vec3("));}),_ib=new T1(0,_ia),_ic=new T2(1,_ib,_i9),_id=new T(function(){return toJSStr(B(_1F(_x,_1l,_ic)));}),_ie=function(_if,_ig){while(1){var _ih=E(_if);if(!_ih._){return E(_ig);}else{var _ii=_ig+1|0;_if=_ih.b;_ig=_ii;continue;}}},_ij=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ik=new T(function(){return B(err(_ij));}),_il=0,_im=new T3(0,E(_il),E(_il),E(_il)),_in=new T(function(){return B(unCStr("Negative exponent"));}),_io=new T(function(){return B(err(_in));}),_ip=function(_iq,_ir,_is){while(1){if(!(_ir%2)){var _it=_iq*_iq,_iu=quot(_ir,2);_iq=_it;_ir=_iu;continue;}else{var _iv=E(_ir);if(_iv==1){return _iq*_is;}else{var _it=_iq*_iq,_iw=_iq*_is;_iq=_it;_ir=quot(_iv-1|0,2);_is=_iw;continue;}}}},_ix=function(_iy,_iz){while(1){if(!(_iz%2)){var _iA=_iy*_iy,_iB=quot(_iz,2);_iy=_iA;_iz=_iB;continue;}else{var _iC=E(_iz);if(_iC==1){return E(_iy);}else{return new F(function(){return _ip(_iy*_iy,quot(_iC-1|0,2),_iy);});}}}},_iD=function(_iE){var _iF=E(_iE);return new F(function(){return Math.log(_iF+(_iF+1)*Math.sqrt((_iF-1)/(_iF+1)));});},_iG=function(_iH){var _iI=E(_iH);return new F(function(){return Math.log(_iI+Math.sqrt(1+_iI*_iI));});},_iJ=function(_iK){var _iL=E(_iK);return 0.5*Math.log((1+_iL)/(1-_iL));},_iM=function(_iN,_iO){return Math.log(E(_iO))/Math.log(E(_iN));},_iP=3.141592653589793,_iQ=function(_iR){var _iS=E(_iR);return new F(function(){return _7J(_iS.a,_iS.b);});},_iT=function(_iU){return 1/E(_iU);},_iV=function(_iW){var _iX=E(_iW),_iY=E(_iX);return (_iY==0)?E(_7I):(_iY<=0)? -_iY:E(_iX);},_iZ=function(_j0){var _j1=E(_j0);if(!_j1._){return _j1.a;}else{return new F(function(){return I_toNumber(_j1.a);});}},_j2=function(_j3){return new F(function(){return _iZ(_j3);});},_j4=1,_j5=-1,_j6=function(_j7){var _j8=E(_j7);return (_j8<=0)?(_j8>=0)?E(_j8):E(_j5):E(_j4);},_j9=function(_ja,_jb){return E(_ja)-E(_jb);},_jc=function(_jd){return  -E(_jd);},_je=function(_jf,_jg){return E(_jf)+E(_jg);},_jh=function(_ji,_jj){return E(_ji)*E(_jj);},_jk={_:0,a:_je,b:_j9,c:_jh,d:_jc,e:_iV,f:_j6,g:_j2},_jl=function(_jm,_jn){return E(_jm)/E(_jn);},_jo=new T4(0,_jk,_jl,_iT,_iQ),_jp=function(_jq){return new F(function(){return Math.acos(E(_jq));});},_jr=function(_js){return new F(function(){return Math.asin(E(_js));});},_jt=function(_ju){return new F(function(){return Math.atan(E(_ju));});},_jv=function(_jw){return new F(function(){return Math.cos(E(_jw));});},_jx=function(_jy){return new F(function(){return cosh(E(_jy));});},_jz=function(_jA){return new F(function(){return Math.exp(E(_jA));});},_jB=function(_jC){return new F(function(){return Math.log(E(_jC));});},_jD=function(_jE,_jF){return new F(function(){return Math.pow(E(_jE),E(_jF));});},_jG=function(_jH){return new F(function(){return Math.sin(E(_jH));});},_jI=function(_jJ){return new F(function(){return sinh(E(_jJ));});},_jK=function(_jL){return new F(function(){return Math.sqrt(E(_jL));});},_jM=function(_jN){return new F(function(){return Math.tan(E(_jN));});},_jO=function(_jP){return new F(function(){return tanh(E(_jP));});},_jQ={_:0,a:_jo,b:_iP,c:_jz,d:_jB,e:_jK,f:_jD,g:_iM,h:_jG,i:_jv,j:_jM,k:_jr,l:_jp,m:_jt,n:_jI,o:_jx,p:_jO,q:_iG,r:_iD,s:_iJ},_jR=function(_jS,_jT){return (E(_jS)!=E(_jT))?true:false;},_jU=function(_jV,_jW){return E(_jV)==E(_jW);},_jX=new T2(0,_jU,_jR),_jY=function(_jZ,_k0){return E(_jZ)<E(_k0);},_k1=function(_k2,_k3){return E(_k2)<=E(_k3);},_k4=function(_k5,_k6){return E(_k5)>E(_k6);},_k7=function(_k8,_k9){return E(_k8)>=E(_k9);},_ka=function(_kb,_kc){var _kd=E(_kb),_ke=E(_kc);return (_kd>=_ke)?(_kd!=_ke)?2:1:0;},_kf=function(_kg,_kh){var _ki=E(_kg),_kj=E(_kh);return (_ki>_kj)?E(_ki):E(_kj);},_kk=function(_kl,_km){var _kn=E(_kl),_ko=E(_km);return (_kn>_ko)?E(_ko):E(_kn);},_kp={_:0,a:_jX,b:_ka,c:_jY,d:_k1,e:_k4,f:_k7,g:_kf,h:_kk},_kq="dz",_kr="wy",_ks="wx",_kt="dy",_ku="dx",_kv="t",_kw="a",_kx="r",_ky="ly",_kz="lx",_kA="wz",_kB=0,_kC=function(_kD){var _kE=__new(),_kF=_kE,_kG=function(_kH,_){while(1){var _kI=E(_kH);if(!_kI._){return _kB;}else{var _kJ=E(_kI.a),_kK=__set(_kF,E(_kJ.a),E(_kJ.b));_kH=_kI.b;continue;}}},_kL=B(_kG(_kD,_));return E(_kF);},_kM=function(_kN,_kO,_kP,_kQ,_kR,_kS,_kT,_kU,_kV){return new F(function(){return _kC(new T2(1,new T2(0,_ks,_kN),new T2(1,new T2(0,_kr,_kO),new T2(1,new T2(0,_kA,_kP),new T2(1,new T2(0,_kz,_kQ*_kR*Math.cos(_kS)),new T2(1,new T2(0,_ky,_kQ*_kR*Math.sin(_kS)),new T2(1,new T2(0,_kx,_kQ),new T2(1,new T2(0,_kw,_kR),new T2(1,new T2(0,_kv,_kS),new T2(1,new T2(0,_ku,_kT),new T2(1,new T2(0,_kt,_kU),new T2(1,new T2(0,_kq,_kV),_w))))))))))));});},_kW=function(_kX){var _kY=E(_kX),_kZ=E(_kY.a),_l0=E(_kY.b),_l1=E(_kY.d);return new F(function(){return _kM(_kZ.a,_kZ.b,_kZ.c,E(_l0.a),E(_l0.b),E(_kY.c),_l1.a,_l1.b,_l1.c);});},_l2=function(_l3,_l4){var _l5=E(_l4);return (_l5._==0)?__Z:new T2(1,new T(function(){return B(A1(_l3,_l5.a));}),new T(function(){return B(_l2(_l3,_l5.b));}));},_l6=function(_l7,_l8,_l9){var _la=__lst2arr(B(_l2(_kW,new T2(1,_l7,new T2(1,_l8,new T2(1,_l9,_w))))));return E(_la);},_lb=function(_lc){var _ld=E(_lc);return new F(function(){return _l6(_ld.a,_ld.b,_ld.c);});},_le=new T2(0,_jQ,_kp),_lf=function(_lg,_lh,_li,_lj){var _lk=B(_8q(_lg)),_ll=new T(function(){return B(A2(_8K,_lg,new T(function(){return B(_8w(_lg,_lh,_li,_lj,_lh,_li,_lj));})));});return new T3(0,B(A3(_a8,_lk,_lh,_ll)),B(A3(_a8,_lk,_li,_ll)),B(A3(_a8,_lk,_lj,_ll)));},_lm=function(_ln,_lo,_lp,_lq,_lr,_ls,_lt){var _lu=B(_8u(_ln));return new T3(0,B(A1(B(A1(_lu,_lo)),_lr)),B(A1(B(A1(_lu,_lp)),_ls)),B(A1(B(A1(_lu,_lq)),_lt)));},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC){var _lD=B(_86(_lw));return new T3(0,B(A1(B(A1(_lD,_lx)),_lA)),B(A1(B(A1(_lD,_ly)),_lB)),B(A1(B(A1(_lD,_lz)),_lC)));},_lE=function(_lF,_lG){var _lH=new T(function(){return E(E(_lF).a);}),_lI=new T(function(){return B(A2(_hQ,new T2(0,_lH,new T(function(){return E(E(_lF).b);})),_lG));}),_lJ=new T(function(){var _lK=E(_lI),_lL=B(_lf(_lH,_lK.a,_lK.b,_lK.c));return new T3(0,E(_lL.a),E(_lL.b),E(_lL.c));}),_lM=new T(function(){var _lN=E(_lG),_lO=E(_lJ),_lP=B(_8q(_lH)),_lQ=new T(function(){return B(A2(_8K,_lH,new T(function(){var _lR=E(_lI),_lS=_lR.a,_lT=_lR.b,_lU=_lR.c;return B(_8w(_lH,_lS,_lT,_lU,_lS,_lT,_lU));})));}),_lV=B(A3(_a8,_lP,new T(function(){return B(_8M(_lH,_lN));}),_lQ)),_lW=B(_8s(_lP)),_lX=B(_lm(_lW,_lO.a,_lO.b,_lO.c,_lV,_lV,_lV)),_lY=B(_88(_lW)),_lZ=B(_lv(_lW,_lN.a,_lN.b,_lN.c,B(A1(_lY,_lX.a)),B(A1(_lY,_lX.b)),B(A1(_lY,_lX.c))));return new T3(0,E(_lZ.a),E(_lZ.b),E(_lZ.c));});return new T2(0,_lM,_lJ);},_m0=function(_m1){return E(E(_m1).a);},_m2=function(_m3,_m4,_m5,_m6,_m7,_m8,_m9){var _ma=B(_8w(_m3,_m7,_m8,_m9,_m4,_m5,_m6)),_mb=B(_8s(B(_8q(_m3)))),_mc=B(_lm(_mb,_m7,_m8,_m9,_ma,_ma,_ma)),_md=B(_88(_mb));return new F(function(){return _lv(_mb,_m4,_m5,_m6,B(A1(_md,_mc.a)),B(A1(_md,_mc.b)),B(A1(_md,_mc.c)));});},_me=function(_mf){return E(E(_mf).a);},_mg=function(_mh,_mi,_mj,_mk){var _ml=new T(function(){var _mm=E(_mk),_mn=E(_mj),_mo=B(_m2(_mh,_mm.a,_mm.b,_mm.c,_mn.a,_mn.b,_mn.c));return new T3(0,E(_mo.a),E(_mo.b),E(_mo.c));}),_mp=new T(function(){return B(A2(_8K,_mh,new T(function(){var _mq=E(_ml),_mr=_mq.a,_ms=_mq.b,_mt=_mq.c;return B(_8w(_mh,_mr,_ms,_mt,_mr,_ms,_mt));})));});if(!B(A3(_me,B(_m0(_mi)),_mp,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_mh)))),_9Z));})))){var _mu=E(_ml),_mv=B(_lf(_mh,_mu.a,_mu.b,_mu.c)),_mw=B(A2(_8K,_mh,new T(function(){var _mx=E(_mk),_my=_mx.a,_mz=_mx.b,_mA=_mx.c;return B(_8w(_mh,_my,_mz,_mA,_my,_mz,_mA));}))),_mB=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_mh));})));})));return new T3(0,B(A1(B(A1(_mB,_mv.a)),_mw)),B(A1(B(A1(_mB,_mv.b)),_mw)),B(A1(B(A1(_mB,_mv.c)),_mw)));}else{var _mC=B(A2(_8I,B(_8s(B(_8q(_mh)))),_9Z));return new T3(0,_mC,_mC,_mC);}},_mD=new T(function(){var _mE=eval("angleCount"),_mF=Number(_mE);return jsTrunc(_mF);}),_mG=new T(function(){return E(_mD);}),_mH=new T(function(){return B(unCStr(": empty list"));}),_mI=new T(function(){return B(unCStr("Prelude."));}),_mJ=function(_mK){return new F(function(){return err(B(_n(_mI,new T(function(){return B(_n(_mK,_mH));},1))));});},_mL=new T(function(){return B(unCStr("head"));}),_mM=new T(function(){return B(_mJ(_mL));}),_mN=function(_mO,_mP,_mQ){var _mR=E(_mO);if(!_mR._){return __Z;}else{var _mS=E(_mP);if(!_mS._){return __Z;}else{var _mT=_mS.a,_mU=E(_mQ);if(!_mU._){return __Z;}else{var _mV=E(_mU.a),_mW=_mV.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_mR.a),E(_mT),E(_mW));}),new T2(1,new T(function(){return new T3(0,E(_mT),E(_mW),E(_mV.b));}),_w)),new T(function(){return B(_mN(_mR.b,_mS.b,_mU.b));},1));});}}}},_mX=new T(function(){return B(unCStr("tail"));}),_mY=new T(function(){return B(_mJ(_mX));}),_mZ=function(_n0,_n1){var _n2=E(_n0);if(!_n2._){return __Z;}else{var _n3=E(_n1);return (_n3._==0)?__Z:new T2(1,new T2(0,_n2.a,_n3.a),new T(function(){return B(_mZ(_n2.b,_n3.b));}));}},_n4=function(_n5,_n6){var _n7=E(_n5);if(!_n7._){return __Z;}else{var _n8=E(_n6);if(!_n8._){return __Z;}else{var _n9=E(_n7.a),_na=_n9.b,_nb=E(_n8.a).b,_nc=new T(function(){var _nd=new T(function(){return B(_mZ(_nb,new T(function(){var _ne=E(_nb);if(!_ne._){return E(_mY);}else{return E(_ne.b);}},1)));},1);return B(_mN(_na,new T(function(){var _nf=E(_na);if(!_nf._){return E(_mY);}else{return E(_nf.b);}},1),_nd));});return new F(function(){return _n(new T2(1,new T(function(){var _ng=E(_na);if(!_ng._){return E(_mM);}else{var _nh=E(_nb);if(!_nh._){return E(_mM);}else{return new T3(0,E(_n9.a),E(_ng.a),E(_nh.a));}}}),_nc),new T(function(){return B(_n4(_n7.b,_n8.b));},1));});}}},_ni=new T(function(){return E(_mG)-1;}),_nj=new T1(0,1),_nk=function(_nl,_nm){var _nn=E(_nm),_no=new T(function(){var _np=B(_8s(_nl)),_nq=B(_nk(_nl,B(A3(_86,_np,_nn,new T(function(){return B(A2(_8I,_np,_nj));})))));return new T2(1,_nq.a,_nq.b);});return new T2(0,_nn,_no);},_nr=function(_ns){return E(E(_ns).d);},_nt=new T1(0,2),_nu=function(_nv,_nw){var _nx=E(_nw);if(!_nx._){return __Z;}else{var _ny=_nx.a;return (!B(A1(_nv,_ny)))?__Z:new T2(1,_ny,new T(function(){return B(_nu(_nv,_nx.b));}));}},_nz=function(_nA,_nB,_nC,_nD){var _nE=B(_nk(_nB,_nC)),_nF=new T(function(){var _nG=B(_8s(_nB)),_nH=new T(function(){return B(A3(_a8,_nB,new T(function(){return B(A2(_8I,_nG,_nj));}),new T(function(){return B(A2(_8I,_nG,_nt));})));});return B(A3(_86,_nG,_nD,_nH));});return new F(function(){return _nu(function(_nI){return new F(function(){return A3(_nr,_nA,_nI,_nF);});},new T2(1,_nE.a,_nE.b));});},_nJ=new T(function(){return B(_nz(_kp,_jo,_il,_ni));}),_nK=function(_nL,_nM){while(1){var _nN=E(_nL);if(!_nN._){return E(_nM);}else{_nL=_nN.b;_nM=_nN.a;continue;}}},_nO=new T(function(){return B(unCStr("last"));}),_nP=new T(function(){return B(_mJ(_nO));}),_nQ=function(_nR){return new F(function(){return _nK(_nR,_nP);});},_nS=function(_nT){return new F(function(){return _nQ(E(_nT).b);});},_nU=new T(function(){var _nV=eval("proceedCount"),_nW=Number(_nV);return jsTrunc(_nW);}),_nX=new T(function(){return E(_nU);}),_nY=1,_nZ=new T(function(){return B(_nz(_kp,_jo,_nY,_nX));}),_o0=function(_o1,_o2,_o3,_o4,_o5,_o6,_o7,_o8,_o9,_oa,_ob,_oc,_od,_oe){var _of=new T(function(){var _og=new T(function(){var _oh=E(_oa),_oi=E(_oe),_oj=E(_od),_ok=E(_ob),_ol=E(_oc),_om=E(_o9);return new T3(0,_oh*_oi-_oj*_ok,_ok*_ol-_oi*_om,_om*_oj-_ol*_oh);}),_on=function(_oo){var _op=new T(function(){var _oq=E(_oo)/E(_mG);return (_oq+_oq)*3.141592653589793;}),_or=new T(function(){return B(A1(_o1,_op));}),_os=new T(function(){var _ot=new T(function(){var _ou=E(_or)/E(_nX);return new T3(0,E(_ou),E(_ou),E(_ou));}),_ov=function(_ow,_ox){var _oy=E(_ow);if(!_oy._){return new T2(0,_w,_ox);}else{var _oz=new T(function(){var _oA=B(_lE(_le,new T(function(){var _oB=E(_ox),_oC=E(_oB.a),_oD=E(_oB.b),_oE=E(_ot);return new T3(0,E(_oC.a)+E(_oD.a)*E(_oE.a),E(_oC.b)+E(_oD.b)*E(_oE.b),E(_oC.c)+E(_oD.c)*E(_oE.c));}))),_oF=_oA.a,_oG=new T(function(){var _oH=E(_oA.b),_oI=E(E(_ox).b),_oJ=B(_m2(_jQ,_oI.a,_oI.b,_oI.c,_oH.a,_oH.b,_oH.c)),_oK=B(_lf(_jQ,_oJ.a,_oJ.b,_oJ.c));return new T3(0,E(_oK.a),E(_oK.b),E(_oK.c));});return new T2(0,new T(function(){var _oL=E(_or),_oM=E(_op);return new T4(0,E(_oF),E(new T2(0,E(_oy.a)/E(_nX),E(_oL))),E(_oM),E(_oG));}),new T2(0,_oF,_oG));}),_oN=new T(function(){var _oO=B(_ov(_oy.b,new T(function(){return E(E(_oz).b);})));return new T2(0,_oO.a,_oO.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oz).a);}),new T(function(){return E(E(_oN).a);})),new T(function(){return E(E(_oN).b);}));}},_oP=function(_oQ,_oR,_oS,_oT,_oU){var _oV=E(_oQ);if(!_oV._){return new T2(0,_w,new T2(0,new T3(0,E(_oR),E(_oS),E(_oT)),_oU));}else{var _oW=new T(function(){var _oX=B(_lE(_le,new T(function(){var _oY=E(_oU),_oZ=E(_ot);return new T3(0,E(_oR)+E(_oY.a)*E(_oZ.a),E(_oS)+E(_oY.b)*E(_oZ.b),E(_oT)+E(_oY.c)*E(_oZ.c));}))),_p0=_oX.a,_p1=new T(function(){var _p2=E(_oX.b),_p3=E(_oU),_p4=B(_m2(_jQ,_p3.a,_p3.b,_p3.c,_p2.a,_p2.b,_p2.c)),_p5=B(_lf(_jQ,_p4.a,_p4.b,_p4.c));return new T3(0,E(_p5.a),E(_p5.b),E(_p5.c));});return new T2(0,new T(function(){var _p6=E(_or),_p7=E(_op);return new T4(0,E(_p0),E(new T2(0,E(_oV.a)/E(_nX),E(_p6))),E(_p7),E(_p1));}),new T2(0,_p0,_p1));}),_p8=new T(function(){var _p9=B(_ov(_oV.b,new T(function(){return E(E(_oW).b);})));return new T2(0,_p9.a,_p9.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oW).a);}),new T(function(){return E(E(_p8).a);})),new T(function(){return E(E(_p8).b);}));}};return E(B(_oP(_nZ,_o4,_o5,_o6,new T(function(){var _pa=E(_og),_pb=E(_op)+_o7,_pc=Math.cos(_pb),_pd=Math.sin(_pb);return new T3(0,E(_o9)*_pc+E(_pa.a)*_pd,E(_oa)*_pc+E(_pa.b)*_pd,E(_ob)*_pc+E(_pa.c)*_pd);}))).a);});return new T2(0,new T(function(){var _pe=E(_or),_pf=E(_op);return new T4(0,E(new T3(0,E(_o4),E(_o5),E(_o6))),E(new T2(0,E(_il),E(_pe))),E(_pf),E(_im));}),_os);};return B(_l2(_on,_nJ));}),_pg=new T(function(){var _ph=new T(function(){var _pi=B(_n(_of,new T2(1,new T(function(){var _pj=E(_of);if(!_pj._){return E(_mM);}else{return E(_pj.a);}}),_w)));if(!_pi._){return E(_mY);}else{return E(_pi.b);}},1);return B(_n4(_of,_ph));});return new T2(0,_pg,new T(function(){return B(_l2(_nS,_of));}));},_pk=function(_pl,_pm,_pn,_po,_pp,_pq,_pr,_ps,_pt,_pu,_pv,_pw,_px,_py,_pz,_pA,_pB){var _pC=B(_lE(_le,new T3(0,E(_po),E(_pp),E(_pq)))),_pD=_pC.b,_pE=E(_pC.a),_pF=B(_mg(_jQ,_kp,_pD,new T3(0,E(_ps),E(_pt),E(_pu)))),_pG=E(_pD),_pH=_pG.a,_pI=_pG.b,_pJ=_pG.c,_pK=B(_m2(_jQ,_pw,_px,_py,_pH,_pI,_pJ)),_pL=B(_lf(_jQ,_pK.a,_pK.b,_pK.c)),_pM=_pL.a,_pN=_pL.b,_pO=_pL.c,_pP=E(_pr),_pQ=new T2(0,E(new T3(0,E(_pF.a),E(_pF.b),E(_pF.c))),E(_pv)),_pR=B(_o0(_pl,_pm,_pn,_pE.a,_pE.b,_pE.c,_pP,_pQ,_pM,_pN,_pO,_pH,_pI,_pJ)),_pS=__lst2arr(B(_l2(_lb,_pR.a))),_pT=__lst2arr(B(_l2(_kW,_pR.b)));return {_:0,a:_pl,b:_pm,c:_pn,d:new T2(0,E(_pE),E(_pP)),e:_pQ,f:new T3(0,E(_pM),E(_pN),E(_pO)),g:_pG,h:_pS,i:_pT};},_pU=-4,_pV=new T3(0,E(_il),E(_pU),E(_il)),_pW=function(_pX){return E(_pV);},_pY=new T(function(){return 6.283185307179586/E(_mG);}),_pZ=function(_){return new F(function(){return __jsNull();});},_q0=function(_q1){var _q2=B(A1(_q1,_));return E(_q2);},_q3=new T(function(){return B(_q0(_pZ));}),_q4=function(_q5,_q6,_q7,_q8,_q9,_qa,_qb,_qc,_qd,_qe,_qf,_qg,_qh){var _qi=function(_qj){var _qk=E(_pY),_ql=2+_qj|0,_qm=_ql-1|0,_qn=(2+_qj)*(1+_qj),_qo=E(_nJ);if(!_qo._){return _qk*0;}else{var _qp=_qo.a,_qq=_qo.b,_qr=B(A1(_q5,new T(function(){return 6.283185307179586*E(_qp)/E(_mG);}))),_qs=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_qp)+1)/E(_mG);})));if(_qr!=_qs){if(_ql>=0){var _qt=E(_ql);if(!_qt){var _qu=function(_qv,_qw){while(1){var _qx=B((function(_qy,_qz){var _qA=E(_qy);if(!_qA._){return E(_qz);}else{var _qB=_qA.a,_qC=_qA.b,_qD=B(A1(_q5,new T(function(){return 6.283185307179586*E(_qB)/E(_mG);}))),_qE=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_qB)+1)/E(_mG);})));if(_qD!=_qE){var _qF=_qz+0/(_qD-_qE)/_qn;_qv=_qC;_qw=_qF;return __continue;}else{if(_qm>=0){var _qG=E(_qm);if(!_qG){var _qF=_qz+_ql/_qn;_qv=_qC;_qw=_qF;return __continue;}else{var _qF=_qz+_ql*B(_ix(_qD,_qG))/_qn;_qv=_qC;_qw=_qF;return __continue;}}else{return E(_io);}}}})(_qv,_qw));if(_qx!=__continue){return _qx;}}};return _qk*B(_qu(_qq,0/(_qr-_qs)/_qn));}else{var _qH=function(_qI,_qJ){while(1){var _qK=B((function(_qL,_qM){var _qN=E(_qL);if(!_qN._){return E(_qM);}else{var _qO=_qN.a,_qP=_qN.b,_qQ=B(A1(_q5,new T(function(){return 6.283185307179586*E(_qO)/E(_mG);}))),_qR=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_qO)+1)/E(_mG);})));if(_qQ!=_qR){if(_qt>=0){var _qS=_qM+(B(_ix(_qQ,_qt))-B(_ix(_qR,_qt)))/(_qQ-_qR)/_qn;_qI=_qP;_qJ=_qS;return __continue;}else{return E(_io);}}else{if(_qm>=0){var _qT=E(_qm);if(!_qT){var _qS=_qM+_ql/_qn;_qI=_qP;_qJ=_qS;return __continue;}else{var _qS=_qM+_ql*B(_ix(_qQ,_qT))/_qn;_qI=_qP;_qJ=_qS;return __continue;}}else{return E(_io);}}}})(_qI,_qJ));if(_qK!=__continue){return _qK;}}};return _qk*B(_qH(_qq,(B(_ix(_qr,_qt))-B(_ix(_qs,_qt)))/(_qr-_qs)/_qn));}}else{return E(_io);}}else{if(_qm>=0){var _qU=E(_qm);if(!_qU){var _qV=function(_qW,_qX){while(1){var _qY=B((function(_qZ,_r0){var _r1=E(_qZ);if(!_r1._){return E(_r0);}else{var _r2=_r1.a,_r3=_r1.b,_r4=B(A1(_q5,new T(function(){return 6.283185307179586*E(_r2)/E(_mG);}))),_r5=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_r2)+1)/E(_mG);})));if(_r4!=_r5){if(_ql>=0){var _r6=E(_ql);if(!_r6){var _r7=_r0+0/(_r4-_r5)/_qn;_qW=_r3;_qX=_r7;return __continue;}else{var _r7=_r0+(B(_ix(_r4,_r6))-B(_ix(_r5,_r6)))/(_r4-_r5)/_qn;_qW=_r3;_qX=_r7;return __continue;}}else{return E(_io);}}else{var _r7=_r0+_ql/_qn;_qW=_r3;_qX=_r7;return __continue;}}})(_qW,_qX));if(_qY!=__continue){return _qY;}}};return _qk*B(_qV(_qq,_ql/_qn));}else{var _r8=function(_r9,_ra){while(1){var _rb=B((function(_rc,_rd){var _re=E(_rc);if(!_re._){return E(_rd);}else{var _rf=_re.a,_rg=_re.b,_rh=B(A1(_q5,new T(function(){return 6.283185307179586*E(_rf)/E(_mG);}))),_ri=B(A1(_q5,new T(function(){return 6.283185307179586*(E(_rf)+1)/E(_mG);})));if(_rh!=_ri){if(_ql>=0){var _rj=E(_ql);if(!_rj){var _rk=_rd+0/(_rh-_ri)/_qn;_r9=_rg;_ra=_rk;return __continue;}else{var _rk=_rd+(B(_ix(_rh,_rj))-B(_ix(_ri,_rj)))/(_rh-_ri)/_qn;_r9=_rg;_ra=_rk;return __continue;}}else{return E(_io);}}else{if(_qU>=0){var _rk=_rd+_ql*B(_ix(_rh,_qU))/_qn;_r9=_rg;_ra=_rk;return __continue;}else{return E(_io);}}}})(_r9,_ra));if(_rb!=__continue){return _rb;}}};return _qk*B(_r8(_qq,_ql*B(_ix(_qr,_qU))/_qn));}}else{return E(_io);}}}},_rl=E(_q3),_rm=1/(B(_qi(1))*_q6);return new F(function(){return _pk(_q5,_pW,new T2(0,E(new T3(0,E(_rm),E(_rm),E(_rm))),1/(B(_qi(3))*_q6)),_q7,_q8,_q9,_qa,_qb,_qc,_qd,_qe,_qf,_qg,_qh,_im,_rl,_rl);});},_rn=1,_ro=0,_rp=function(_rq){var _rr=I_decodeDouble(_rq);return new T2(0,new T1(1,_rr.b),_rr.a);},_rs=function(_rt){return new T1(0,_rt);},_ru=function(_rv){var _rw=hs_intToInt64(2147483647),_rx=hs_leInt64(_rv,_rw);if(!_rx){return new T1(1,I_fromInt64(_rv));}else{var _ry=hs_intToInt64(-2147483648),_rz=hs_geInt64(_rv,_ry);if(!_rz){return new T1(1,I_fromInt64(_rv));}else{var _rA=hs_int64ToInt(_rv);return new F(function(){return _rs(_rA);});}}},_rB=new T(function(){var _rC=newByteArr(256),_rD=_rC,_=_rD["v"]["i8"][0]=8,_rE=function(_rF,_rG,_rH,_){while(1){if(_rH>=256){if(_rF>=256){return E(_);}else{var _rI=imul(2,_rF)|0,_rJ=_rG+1|0,_rK=_rF;_rF=_rI;_rG=_rJ;_rH=_rK;continue;}}else{var _=_rD["v"]["i8"][_rH]=_rG,_rK=_rH+_rF|0;_rH=_rK;continue;}}},_=B(_rE(2,0,1,_));return _rD;}),_rL=function(_rM,_rN){var _rO=hs_int64ToInt(_rM),_rP=E(_rB),_rQ=_rP["v"]["i8"][(255&_rO>>>0)>>>0&4294967295];if(_rN>_rQ){if(_rQ>=8){var _rR=hs_uncheckedIShiftRA64(_rM,8),_rS=function(_rT,_rU){while(1){var _rV=B((function(_rW,_rX){var _rY=hs_int64ToInt(_rW),_rZ=_rP["v"]["i8"][(255&_rY>>>0)>>>0&4294967295];if(_rX>_rZ){if(_rZ>=8){var _s0=hs_uncheckedIShiftRA64(_rW,8),_s1=_rX-8|0;_rT=_s0;_rU=_s1;return __continue;}else{return new T2(0,new T(function(){var _s2=hs_uncheckedIShiftRA64(_rW,_rZ);return B(_ru(_s2));}),_rX-_rZ|0);}}else{return new T2(0,new T(function(){var _s3=hs_uncheckedIShiftRA64(_rW,_rX);return B(_ru(_s3));}),0);}})(_rT,_rU));if(_rV!=__continue){return _rV;}}};return new F(function(){return _rS(_rR,_rN-8|0);});}else{return new T2(0,new T(function(){var _s4=hs_uncheckedIShiftRA64(_rM,_rQ);return B(_ru(_s4));}),_rN-_rQ|0);}}else{return new T2(0,new T(function(){var _s5=hs_uncheckedIShiftRA64(_rM,_rN);return B(_ru(_s5));}),0);}},_s6=function(_s7){var _s8=hs_intToInt64(_s7);return E(_s8);},_s9=function(_sa){var _sb=E(_sa);if(!_sb._){return new F(function(){return _s6(_sb.a);});}else{return new F(function(){return I_toInt64(_sb.a);});}},_sc=function(_sd){return I_toInt(_sd)>>>0;},_se=function(_sf){var _sg=E(_sf);if(!_sg._){return _sg.a>>>0;}else{return new F(function(){return _sc(_sg.a);});}},_sh=function(_si){var _sj=B(_rp(_si)),_sk=_sj.a,_sl=_sj.b;if(_sl<0){var _sm=function(_sn){if(!_sn){return new T2(0,E(_sk),B(_52(_3k, -_sl)));}else{var _so=B(_rL(B(_s9(_sk)), -_sl));return new T2(0,E(_so.a),B(_52(_3k,_so.b)));}};if(!((B(_se(_sk))&1)>>>0)){return new F(function(){return _sm(1);});}else{return new F(function(){return _sm(0);});}}else{return new T2(0,B(_52(_sk,_sl)),_3k);}},_sp=function(_sq){var _sr=B(_sh(E(_sq)));return new T2(0,E(_sr.a),E(_sr.b));},_ss=new T3(0,_jk,_kp,_sp),_st=function(_su){return E(E(_su).a);},_sv=function(_sw){return E(E(_sw).a);},_sx=function(_sy,_sz){if(_sy<=_sz){var _sA=function(_sB){return new T2(1,_sB,new T(function(){if(_sB!=_sz){return B(_sA(_sB+1|0));}else{return __Z;}}));};return new F(function(){return _sA(_sy);});}else{return __Z;}},_sC=function(_sD){return new F(function(){return _sx(E(_sD),2147483647);});},_sE=function(_sF,_sG,_sH){if(_sH<=_sG){var _sI=new T(function(){var _sJ=_sG-_sF|0,_sK=function(_sL){return (_sL>=(_sH-_sJ|0))?new T2(1,_sL,new T(function(){return B(_sK(_sL+_sJ|0));})):new T2(1,_sL,_w);};return B(_sK(_sG));});return new T2(1,_sF,_sI);}else{return (_sH<=_sF)?new T2(1,_sF,_w):__Z;}},_sM=function(_sN,_sO,_sP){if(_sP>=_sO){var _sQ=new T(function(){var _sR=_sO-_sN|0,_sS=function(_sT){return (_sT<=(_sP-_sR|0))?new T2(1,_sT,new T(function(){return B(_sS(_sT+_sR|0));})):new T2(1,_sT,_w);};return B(_sS(_sO));});return new T2(1,_sN,_sQ);}else{return (_sP>=_sN)?new T2(1,_sN,_w):__Z;}},_sU=function(_sV,_sW){if(_sW<_sV){return new F(function(){return _sE(_sV,_sW,-2147483648);});}else{return new F(function(){return _sM(_sV,_sW,2147483647);});}},_sX=function(_sY,_sZ){return new F(function(){return _sU(E(_sY),E(_sZ));});},_t0=function(_t1,_t2,_t3){if(_t2<_t1){return new F(function(){return _sE(_t1,_t2,_t3);});}else{return new F(function(){return _sM(_t1,_t2,_t3);});}},_t4=function(_t5,_t6,_t7){return new F(function(){return _t0(E(_t5),E(_t6),E(_t7));});},_t8=function(_t9,_ta){return new F(function(){return _sx(E(_t9),E(_ta));});},_tb=function(_tc){return E(_tc);},_td=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_te=new T(function(){return B(err(_td));}),_tf=function(_tg){var _th=E(_tg);return (_th==(-2147483648))?E(_te):_th-1|0;},_ti=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tj=new T(function(){return B(err(_ti));}),_tk=function(_tl){var _tm=E(_tl);return (_tm==2147483647)?E(_tj):_tm+1|0;},_tn={_:0,a:_tk,b:_tf,c:_tb,d:_tb,e:_sC,f:_sX,g:_t8,h:_t4},_to=function(_tp,_tq){if(_tp<=0){if(_tp>=0){return new F(function(){return quot(_tp,_tq);});}else{if(_tq<=0){return new F(function(){return quot(_tp,_tq);});}else{return quot(_tp+1|0,_tq)-1|0;}}}else{if(_tq>=0){if(_tp>=0){return new F(function(){return quot(_tp,_tq);});}else{if(_tq<=0){return new F(function(){return quot(_tp,_tq);});}else{return quot(_tp+1|0,_tq)-1|0;}}}else{return quot(_tp-1|0,_tq)-1|0;}}},_tr=0,_ts=new T(function(){return B(_4p(_tr));}),_tt=new T(function(){return die(_ts);}),_tu=function(_tv,_tw){var _tx=E(_tw);switch(_tx){case -1:var _ty=E(_tv);if(_ty==(-2147483648)){return E(_tt);}else{return new F(function(){return _to(_ty,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _to(_tv,_tx);});}},_tz=function(_tA,_tB){return new F(function(){return _tu(E(_tA),E(_tB));});},_tC=0,_tD=new T2(0,_tt,_tC),_tE=function(_tF,_tG){var _tH=E(_tF),_tI=E(_tG);switch(_tI){case -1:var _tJ=E(_tH);if(_tJ==(-2147483648)){return E(_tD);}else{if(_tJ<=0){if(_tJ>=0){var _tK=quotRemI(_tJ,-1);return new T2(0,_tK.a,_tK.b);}else{var _tL=quotRemI(_tJ,-1);return new T2(0,_tL.a,_tL.b);}}else{var _tM=quotRemI(_tJ-1|0,-1);return new T2(0,_tM.a-1|0,(_tM.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_tH<=0){if(_tH>=0){var _tN=quotRemI(_tH,_tI);return new T2(0,_tN.a,_tN.b);}else{if(_tI<=0){var _tO=quotRemI(_tH,_tI);return new T2(0,_tO.a,_tO.b);}else{var _tP=quotRemI(_tH+1|0,_tI);return new T2(0,_tP.a-1|0,(_tP.b+_tI|0)-1|0);}}}else{if(_tI>=0){if(_tH>=0){var _tQ=quotRemI(_tH,_tI);return new T2(0,_tQ.a,_tQ.b);}else{if(_tI<=0){var _tR=quotRemI(_tH,_tI);return new T2(0,_tR.a,_tR.b);}else{var _tS=quotRemI(_tH+1|0,_tI);return new T2(0,_tS.a-1|0,(_tS.b+_tI|0)-1|0);}}}else{var _tT=quotRemI(_tH-1|0,_tI);return new T2(0,_tT.a-1|0,(_tT.b+_tI|0)+1|0);}}}},_tU=function(_tV,_tW){var _tX=_tV%_tW;if(_tV<=0){if(_tV>=0){return E(_tX);}else{if(_tW<=0){return E(_tX);}else{var _tY=E(_tX);return (_tY==0)?0:_tY+_tW|0;}}}else{if(_tW>=0){if(_tV>=0){return E(_tX);}else{if(_tW<=0){return E(_tX);}else{var _tZ=E(_tX);return (_tZ==0)?0:_tZ+_tW|0;}}}else{var _u0=E(_tX);return (_u0==0)?0:_u0+_tW|0;}}},_u1=function(_u2,_u3){var _u4=E(_u3);switch(_u4){case -1:return E(_tC);case 0:return E(_4t);default:return new F(function(){return _tU(E(_u2),_u4);});}},_u5=function(_u6,_u7){var _u8=E(_u6),_u9=E(_u7);switch(_u9){case -1:var _ua=E(_u8);if(_ua==(-2147483648)){return E(_tt);}else{return new F(function(){return quot(_ua,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_u8,_u9);});}},_ub=function(_uc,_ud){var _ue=E(_uc),_uf=E(_ud);switch(_uf){case -1:var _ug=E(_ue);if(_ug==(-2147483648)){return E(_tD);}else{var _uh=quotRemI(_ug,-1);return new T2(0,_uh.a,_uh.b);}break;case 0:return E(_4t);default:var _ui=quotRemI(_ue,_uf);return new T2(0,_ui.a,_ui.b);}},_uj=function(_uk,_ul){var _um=E(_ul);switch(_um){case -1:return E(_tC);case 0:return E(_4t);default:return E(_uk)%_um;}},_un=function(_uo){return new F(function(){return _rs(E(_uo));});},_up=function(_uq){return new T2(0,E(B(_rs(E(_uq)))),E(_nj));},_ur=function(_us,_ut){return imul(E(_us),E(_ut))|0;},_uu=function(_uv,_uw){return E(_uv)+E(_uw)|0;},_ux=function(_uy,_uz){return E(_uy)-E(_uz)|0;},_uA=function(_uB){var _uC=E(_uB);return (_uC<0)? -_uC:E(_uC);},_uD=function(_uE){return new F(function(){return _4G(_uE);});},_uF=function(_uG){return  -E(_uG);},_uH=-1,_uI=0,_uJ=1,_uK=function(_uL){var _uM=E(_uL);return (_uM>=0)?(E(_uM)==0)?E(_uI):E(_uJ):E(_uH);},_uN={_:0,a:_uu,b:_ux,c:_ur,d:_uF,e:_uA,f:_uK,g:_uD},_uO=function(_uP,_uQ){return E(_uP)==E(_uQ);},_uR=function(_uS,_uT){return E(_uS)!=E(_uT);},_uU=new T2(0,_uO,_uR),_uV=function(_uW,_uX){var _uY=E(_uW),_uZ=E(_uX);return (_uY>_uZ)?E(_uY):E(_uZ);},_v0=function(_v1,_v2){var _v3=E(_v1),_v4=E(_v2);return (_v3>_v4)?E(_v4):E(_v3);},_v5=function(_v6,_v7){return (_v6>=_v7)?(_v6!=_v7)?2:1:0;},_v8=function(_v9,_va){return new F(function(){return _v5(E(_v9),E(_va));});},_vb=function(_vc,_vd){return E(_vc)>=E(_vd);},_ve=function(_vf,_vg){return E(_vf)>E(_vg);},_vh=function(_vi,_vj){return E(_vi)<=E(_vj);},_vk=function(_vl,_vm){return E(_vl)<E(_vm);},_vn={_:0,a:_uU,b:_v8,c:_vk,d:_vh,e:_ve,f:_vb,g:_uV,h:_v0},_vo=new T3(0,_uN,_vn,_up),_vp={_:0,a:_vo,b:_tn,c:_u5,d:_uj,e:_tz,f:_u1,g:_ub,h:_tE,i:_un},_vq=new T1(0,2),_vr=function(_vs,_vt){while(1){var _vu=E(_vs);if(!_vu._){var _vv=_vu.a,_vw=E(_vt);if(!_vw._){var _vx=_vw.a;if(!(imul(_vv,_vx)|0)){return new T1(0,imul(_vv,_vx)|0);}else{_vs=new T1(1,I_fromInt(_vv));_vt=new T1(1,I_fromInt(_vx));continue;}}else{_vs=new T1(1,I_fromInt(_vv));_vt=_vw;continue;}}else{var _vy=E(_vt);if(!_vy._){_vs=_vu;_vt=new T1(1,I_fromInt(_vy.a));continue;}else{return new T1(1,I_mul(_vu.a,_vy.a));}}}},_vz=function(_vA,_vB,_vC){while(1){if(!(_vB%2)){var _vD=B(_vr(_vA,_vA)),_vE=quot(_vB,2);_vA=_vD;_vB=_vE;continue;}else{var _vF=E(_vB);if(_vF==1){return new F(function(){return _vr(_vA,_vC);});}else{var _vD=B(_vr(_vA,_vA)),_vG=B(_vr(_vA,_vC));_vA=_vD;_vB=quot(_vF-1|0,2);_vC=_vG;continue;}}}},_vH=function(_vI,_vJ){while(1){if(!(_vJ%2)){var _vK=B(_vr(_vI,_vI)),_vL=quot(_vJ,2);_vI=_vK;_vJ=_vL;continue;}else{var _vM=E(_vJ);if(_vM==1){return E(_vI);}else{return new F(function(){return _vz(B(_vr(_vI,_vI)),quot(_vM-1|0,2),_vI);});}}}},_vN=function(_vO){return E(E(_vO).b);},_vP=function(_vQ){return E(E(_vQ).c);},_vR=new T1(0,0),_vS=function(_vT){return E(E(_vT).d);},_vU=function(_vV,_vW){var _vX=B(_st(_vV)),_vY=new T(function(){return B(_sv(_vX));}),_vZ=new T(function(){return B(A3(_vS,_vV,_vW,new T(function(){return B(A2(_8I,_vY,_nt));})));});return new F(function(){return A3(_me,B(_m0(B(_vN(_vX)))),_vZ,new T(function(){return B(A2(_8I,_vY,_vR));}));});},_w0=new T(function(){return B(unCStr("Negative exponent"));}),_w1=new T(function(){return B(err(_w0));}),_w2=function(_w3){return E(E(_w3).c);},_w4=function(_w5,_w6,_w7,_w8){var _w9=B(_st(_w6)),_wa=new T(function(){return B(_sv(_w9));}),_wb=B(_vN(_w9));if(!B(A3(_vP,_wb,_w8,new T(function(){return B(A2(_8I,_wa,_vR));})))){if(!B(A3(_me,B(_m0(_wb)),_w8,new T(function(){return B(A2(_8I,_wa,_vR));})))){var _wc=new T(function(){return B(A2(_8I,_wa,_nt));}),_wd=new T(function(){return B(A2(_8I,_wa,_nj));}),_we=B(_m0(_wb)),_wf=function(_wg,_wh,_wi){while(1){var _wj=B((function(_wk,_wl,_wm){if(!B(_vU(_w6,_wl))){if(!B(A3(_me,_we,_wl,_wd))){var _wn=new T(function(){return B(A3(_w2,_w6,new T(function(){return B(A3(_8G,_wa,_wl,_wd));}),_wc));});_wg=new T(function(){return B(A3(_8u,_w5,_wk,_wk));});_wh=_wn;_wi=new T(function(){return B(A3(_8u,_w5,_wk,_wm));});return __continue;}else{return new F(function(){return A3(_8u,_w5,_wk,_wm);});}}else{var _wo=_wm;_wg=new T(function(){return B(A3(_8u,_w5,_wk,_wk));});_wh=new T(function(){return B(A3(_w2,_w6,_wl,_wc));});_wi=_wo;return __continue;}})(_wg,_wh,_wi));if(_wj!=__continue){return _wj;}}},_wp=function(_wq,_wr){while(1){var _ws=B((function(_wt,_wu){if(!B(_vU(_w6,_wu))){if(!B(A3(_me,_we,_wu,_wd))){var _wv=new T(function(){return B(A3(_w2,_w6,new T(function(){return B(A3(_8G,_wa,_wu,_wd));}),_wc));});return new F(function(){return _wf(new T(function(){return B(A3(_8u,_w5,_wt,_wt));}),_wv,_wt);});}else{return E(_wt);}}else{_wq=new T(function(){return B(A3(_8u,_w5,_wt,_wt));});_wr=new T(function(){return B(A3(_w2,_w6,_wu,_wc));});return __continue;}})(_wq,_wr));if(_ws!=__continue){return _ws;}}};return new F(function(){return _wp(_w7,_w8);});}else{return new F(function(){return A2(_8I,_w5,_nj);});}}else{return E(_w1);}},_ww=new T(function(){return B(err(_w0));}),_wx=function(_wy,_wz){var _wA=B(_rp(_wz)),_wB=_wA.a,_wC=_wA.b,_wD=new T(function(){return B(_sv(new T(function(){return B(_st(_wy));})));});if(_wC<0){var _wE= -_wC;if(_wE>=0){var _wF=E(_wE);if(!_wF){var _wG=E(_nj);}else{var _wG=B(_vH(_vq,_wF));}if(!B(_4y(_wG,_51))){var _wH=B(_4S(_wB,_wG));return new T2(0,new T(function(){return B(A2(_8I,_wD,_wH.a));}),new T(function(){return B(_4u(_wH.b,_wC));}));}else{return E(_4t);}}else{return E(_ww);}}else{var _wI=new T(function(){var _wJ=new T(function(){return B(_w4(_wD,_vp,new T(function(){return B(A2(_8I,_wD,_vq));}),_wC));});return B(A3(_8u,_wD,new T(function(){return B(A2(_8I,_wD,_wB));}),_wJ));});return new T2(0,_wI,_7I);}},_wK=function(_wL,_wM){var _wN=B(_wx(_wL,E(_wM))),_wO=_wN.a;if(E(_wN.b)<=0){return E(_wO);}else{var _wP=B(_sv(B(_st(_wL))));return new F(function(){return A3(_86,_wP,_wO,new T(function(){return B(A2(_8I,_wP,_3k));}));});}},_wQ=function(_wR,_wS){var _wT=B(_wx(_wR,E(_wS))),_wU=_wT.a;if(E(_wT.b)>=0){return E(_wU);}else{var _wV=B(_sv(B(_st(_wR))));return new F(function(){return A3(_8G,_wV,_wU,new T(function(){return B(A2(_8I,_wV,_3k));}));});}},_wW=function(_wX,_wY){var _wZ=B(_wx(_wX,E(_wY)));return new T2(0,_wZ.a,_wZ.b);},_x0=function(_x1,_x2){var _x3=B(_wx(_x1,_x2)),_x4=_x3.a,_x5=E(_x3.b),_x6=new T(function(){var _x7=B(_sv(B(_st(_x1))));if(_x5>=0){return B(A3(_86,_x7,_x4,new T(function(){return B(A2(_8I,_x7,_3k));})));}else{return B(A3(_8G,_x7,_x4,new T(function(){return B(A2(_8I,_x7,_3k));})));}}),_x8=function(_x9){var _xa=_x9-0.5;return (_xa>=0)?(E(_xa)==0)?(!B(_vU(_x1,_x4)))?E(_x6):E(_x4):E(_x6):E(_x4);},_xb=E(_x5);if(!_xb){return new F(function(){return _x8(0);});}else{if(_xb<=0){var _xc= -_xb-0.5;return (_xc>=0)?(E(_xc)==0)?(!B(_vU(_x1,_x4)))?E(_x6):E(_x4):E(_x6):E(_x4);}else{return new F(function(){return _x8(_xb);});}}},_xd=function(_xe,_xf){return new F(function(){return _x0(_xe,E(_xf));});},_xg=function(_xh,_xi){return E(B(_wx(_xh,E(_xi))).a);},_xj={_:0,a:_ss,b:_jo,c:_wW,d:_xg,e:_xd,f:_wK,g:_wQ},_xk=new T1(0,1),_xl=function(_xm,_xn){var _xo=E(_xm);return new T2(0,_xo,new T(function(){var _xp=B(_xl(B(_4J(_xo,_xn)),_xn));return new T2(1,_xp.a,_xp.b);}));},_xq=function(_xr){var _xs=B(_xl(_xr,_xk));return new T2(1,_xs.a,_xs.b);},_xt=function(_xu,_xv){var _xw=B(_xl(_xu,new T(function(){return B(_6W(_xv,_xu));})));return new T2(1,_xw.a,_xw.b);},_xx=new T1(0,0),_xy=function(_xz,_xA){var _xB=E(_xz);if(!_xB._){var _xC=_xB.a,_xD=E(_xA);return (_xD._==0)?_xC>=_xD.a:I_compareInt(_xD.a,_xC)<=0;}else{var _xE=_xB.a,_xF=E(_xA);return (_xF._==0)?I_compareInt(_xE,_xF.a)>=0:I_compare(_xE,_xF.a)>=0;}},_xG=function(_xH,_xI,_xJ){if(!B(_xy(_xI,_xx))){var _xK=function(_xL){return (!B(_S(_xL,_xJ)))?new T2(1,_xL,new T(function(){return B(_xK(B(_4J(_xL,_xI))));})):__Z;};return new F(function(){return _xK(_xH);});}else{var _xM=function(_xN){return (!B(_5c(_xN,_xJ)))?new T2(1,_xN,new T(function(){return B(_xM(B(_4J(_xN,_xI))));})):__Z;};return new F(function(){return _xM(_xH);});}},_xO=function(_xP,_xQ,_xR){return new F(function(){return _xG(_xP,B(_6W(_xQ,_xP)),_xR);});},_xS=function(_xT,_xU){return new F(function(){return _xG(_xT,_xk,_xU);});},_xV=function(_xW){return new F(function(){return _4G(_xW);});},_xX=function(_xY){return new F(function(){return _6W(_xY,_xk);});},_xZ=function(_y0){return new F(function(){return _4J(_y0,_xk);});},_y1=function(_y2){return new F(function(){return _rs(E(_y2));});},_y3={_:0,a:_xZ,b:_xX,c:_y1,d:_xV,e:_xq,f:_xt,g:_xS,h:_xO},_y4=function(_y5,_y6){while(1){var _y7=E(_y5);if(!_y7._){var _y8=E(_y7.a);if(_y8==(-2147483648)){_y5=new T1(1,I_fromInt(-2147483648));continue;}else{var _y9=E(_y6);if(!_y9._){return new T1(0,B(_to(_y8,_y9.a)));}else{_y5=new T1(1,I_fromInt(_y8));_y6=_y9;continue;}}}else{var _ya=_y7.a,_yb=E(_y6);return (_yb._==0)?new T1(1,I_div(_ya,I_fromInt(_yb.a))):new T1(1,I_div(_ya,_yb.a));}}},_yc=function(_yd,_ye){if(!B(_4y(_ye,_vR))){return new F(function(){return _y4(_yd,_ye);});}else{return E(_4t);}},_yf=function(_yg,_yh){while(1){var _yi=E(_yg);if(!_yi._){var _yj=E(_yi.a);if(_yj==(-2147483648)){_yg=new T1(1,I_fromInt(-2147483648));continue;}else{var _yk=E(_yh);if(!_yk._){var _yl=_yk.a;return new T2(0,new T1(0,B(_to(_yj,_yl))),new T1(0,B(_tU(_yj,_yl))));}else{_yg=new T1(1,I_fromInt(_yj));_yh=_yk;continue;}}}else{var _ym=E(_yh);if(!_ym._){_yg=_yi;_yh=new T1(1,I_fromInt(_ym.a));continue;}else{var _yn=I_divMod(_yi.a,_ym.a);return new T2(0,new T1(1,_yn.a),new T1(1,_yn.b));}}}},_yo=function(_yp,_yq){if(!B(_4y(_yq,_vR))){var _yr=B(_yf(_yp,_yq));return new T2(0,_yr.a,_yr.b);}else{return E(_4t);}},_ys=function(_yt,_yu){while(1){var _yv=E(_yt);if(!_yv._){var _yw=E(_yv.a);if(_yw==(-2147483648)){_yt=new T1(1,I_fromInt(-2147483648));continue;}else{var _yx=E(_yu);if(!_yx._){return new T1(0,B(_tU(_yw,_yx.a)));}else{_yt=new T1(1,I_fromInt(_yw));_yu=_yx;continue;}}}else{var _yy=_yv.a,_yz=E(_yu);return (_yz._==0)?new T1(1,I_mod(_yy,I_fromInt(_yz.a))):new T1(1,I_mod(_yy,_yz.a));}}},_yA=function(_yB,_yC){if(!B(_4y(_yC,_vR))){return new F(function(){return _ys(_yB,_yC);});}else{return E(_4t);}},_yD=function(_yE,_yF){while(1){var _yG=E(_yE);if(!_yG._){var _yH=E(_yG.a);if(_yH==(-2147483648)){_yE=new T1(1,I_fromInt(-2147483648));continue;}else{var _yI=E(_yF);if(!_yI._){return new T1(0,quot(_yH,_yI.a));}else{_yE=new T1(1,I_fromInt(_yH));_yF=_yI;continue;}}}else{var _yJ=_yG.a,_yK=E(_yF);return (_yK._==0)?new T1(0,I_toInt(I_quot(_yJ,I_fromInt(_yK.a)))):new T1(1,I_quot(_yJ,_yK.a));}}},_yL=function(_yM,_yN){if(!B(_4y(_yN,_vR))){return new F(function(){return _yD(_yM,_yN);});}else{return E(_4t);}},_yO=function(_yP,_yQ){if(!B(_4y(_yQ,_vR))){var _yR=B(_4S(_yP,_yQ));return new T2(0,_yR.a,_yR.b);}else{return E(_4t);}},_yS=function(_yT,_yU){while(1){var _yV=E(_yT);if(!_yV._){var _yW=E(_yV.a);if(_yW==(-2147483648)){_yT=new T1(1,I_fromInt(-2147483648));continue;}else{var _yX=E(_yU);if(!_yX._){return new T1(0,_yW%_yX.a);}else{_yT=new T1(1,I_fromInt(_yW));_yU=_yX;continue;}}}else{var _yY=_yV.a,_yZ=E(_yU);return (_yZ._==0)?new T1(1,I_rem(_yY,I_fromInt(_yZ.a))):new T1(1,I_rem(_yY,_yZ.a));}}},_z0=function(_z1,_z2){if(!B(_4y(_z2,_vR))){return new F(function(){return _yS(_z1,_z2);});}else{return E(_4t);}},_z3=function(_z4){return E(_z4);},_z5=function(_z6){return E(_z6);},_z7=function(_z8){var _z9=E(_z8);if(!_z9._){var _za=E(_z9.a);return (_za==(-2147483648))?E(_7A):(_za<0)?new T1(0, -_za):E(_z9);}else{var _zb=_z9.a;return (I_compareInt(_zb,0)>=0)?E(_z9):new T1(1,I_negate(_zb));}},_zc=new T1(0,0),_zd=new T1(0,-1),_ze=function(_zf){var _zg=E(_zf);if(!_zg._){var _zh=_zg.a;return (_zh>=0)?(E(_zh)==0)?E(_zc):E(_5k):E(_zd);}else{var _zi=I_compareInt(_zg.a,0);return (_zi<=0)?(E(_zi)==0)?E(_zc):E(_zd):E(_5k);}},_zj={_:0,a:_4J,b:_6W,c:_vr,d:_7B,e:_z7,f:_ze,g:_z5},_zk=function(_zl,_zm){var _zn=E(_zl);if(!_zn._){var _zo=_zn.a,_zp=E(_zm);return (_zp._==0)?_zo!=_zp.a:(I_compareInt(_zp.a,_zo)==0)?false:true;}else{var _zq=_zn.a,_zr=E(_zm);return (_zr._==0)?(I_compareInt(_zq,_zr.a)==0)?false:true:(I_compare(_zq,_zr.a)==0)?false:true;}},_zs=new T2(0,_4y,_zk),_zt=function(_zu,_zv){return (!B(_6H(_zu,_zv)))?E(_zu):E(_zv);},_zw=function(_zx,_zy){return (!B(_6H(_zx,_zy)))?E(_zy):E(_zx);},_zz={_:0,a:_zs,b:_3l,c:_S,d:_6H,e:_5c,f:_xy,g:_zt,h:_zw},_zA=function(_zB){return new T2(0,E(_zB),E(_nj));},_zC=new T3(0,_zj,_zz,_zA),_zD={_:0,a:_zC,b:_y3,c:_yL,d:_z0,e:_yc,f:_yA,g:_yO,h:_yo,i:_z3},_zE=function(_zF){return E(E(_zF).b);},_zG=function(_zH){return E(E(_zH).g);},_zI=new T1(0,1),_zJ=function(_zK,_zL,_zM){var _zN=B(_zE(_zK)),_zO=B(_8s(_zN)),_zP=new T(function(){var _zQ=new T(function(){var _zR=new T(function(){var _zS=new T(function(){return B(A3(_zG,_zK,_zD,new T(function(){return B(A3(_a8,_zN,_zL,_zM));})));});return B(A2(_8I,_zO,_zS));}),_zT=new T(function(){return B(A2(_88,_zO,new T(function(){return B(A2(_8I,_zO,_zI));})));});return B(A3(_8u,_zO,_zT,_zR));});return B(A3(_8u,_zO,_zQ,_zM));});return new F(function(){return A3(_86,_zO,_zL,_zP);});},_zU=1.5707963267948966,_zV=function(_zW){return 0.2/Math.cos(B(_zJ(_xj,_zW,_zU))-0.7853981633974483);},_zX=new T(function(){var _zY=B(_q4(_zV,1.2,_ro,_ro,_rn,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_zY.a),b:E(_zY.b),c:E(_zY.c),d:E(_zY.d),e:E(_zY.e),f:E(_zY.f),g:E(_zY.g),h:_zY.h,i:_zY.i};}),_zZ=0,_A0=0.3,_A1=function(_A2){return E(_A0);},_A3=new T(function(){var _A4=B(_q4(_A1,1.2,_rn,_ro,_rn,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_A4.a),b:E(_A4.b),c:E(_A4.c),d:E(_A4.d),e:E(_A4.e),f:E(_A4.f),g:E(_A4.g),h:_A4.h,i:_A4.i};}),_A5=new T(function(){var _A6=B(_q4(_A1,1.2,_rn,_rn,_ro,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_A6.a),b:E(_A6.b),c:E(_A6.c),d:E(_A6.d),e:E(_A6.e),f:E(_A6.f),g:E(_A6.g),h:_A6.h,i:_A6.i};}),_A7=2,_A8=function(_A9){return 0.3/Math.cos(B(_zJ(_xj,_A9,_zU))-0.7853981633974483);},_Aa=new T(function(){var _Ab=B(_q4(_A8,1.2,_A7,_rn,_rn,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_Ab.a),b:E(_Ab.b),c:E(_Ab.c),d:E(_Ab.d),e:E(_Ab.e),f:E(_Ab.f),g:E(_Ab.g),h:_Ab.h,i:_Ab.i};}),_Ac=0.5,_Ad=new T(function(){var _Ae=B(_q4(_A1,1.2,_ro,_rn,_Ac,_ro,_ro,_ro,_ro,_ro,_rn,_rn,_rn));return {_:0,a:E(_Ae.a),b:E(_Ae.b),c:E(_Ae.c),d:E(_Ae.d),e:E(_Ae.e),f:E(_Ae.f),g:E(_Ae.g),h:_Ae.h,i:_Ae.i};}),_Af=new T2(1,_Ad,_w),_Ag=new T2(1,_Aa,_Af),_Ah=new T2(1,_A5,_Ag),_Ai=new T2(1,_A3,_Ah),_Aj=new T2(1,_zX,_Ai),_Ak=new T(function(){return B(unCStr("Negative range size"));}),_Al=new T(function(){return B(err(_Ak));}),_Am=function(_){var _An=B(_ie(_Aj,0))-1|0,_Ao=function(_Ap){if(_Ap>=0){var _Aq=newArr(_Ap,_ik),_Ar=_Aq,_As=E(_Ap);if(!_As){return new T4(0,E(_zZ),E(_An),0,_Ar);}else{var _At=function(_Au,_Av,_){while(1){var _Aw=E(_Au);if(!_Aw._){return E(_);}else{var _=_Ar[_Av]=_Aw.a;if(_Av!=(_As-1|0)){var _Ax=_Av+1|0;_Au=_Aw.b;_Av=_Ax;continue;}else{return E(_);}}}},_=B((function(_Ay,_Az,_AA,_){var _=_Ar[_AA]=_Ay;if(_AA!=(_As-1|0)){return new F(function(){return _At(_Az,_AA+1|0,_);});}else{return E(_);}})(_zX,_Ai,0,_));return new T4(0,E(_zZ),E(_An),_As,_Ar);}}else{return E(_Al);}};if(0>_An){return new F(function(){return _Ao(0);});}else{return new F(function(){return _Ao(_An+1|0);});}},_AB=function(_AC){var _AD=B(A1(_AC,_));return E(_AD);},_AE=new T(function(){return B(_AB(_Am));}),_AF="outline",_AG="polygon",_AH=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_AI=new T(function(){return B(err(_AH));}),_AJ=new T(function(){return eval("__strict(drawObjects)");}),_AK=new T(function(){return eval("__strict(draw)");}),_AL=function(_AM,_AN){var _AO=jsShowI(_AM);return new F(function(){return _n(fromJSStr(_AO),_AN);});},_AP=function(_AQ,_AR,_AS){if(_AR>=0){return new F(function(){return _AL(_AR,_AS);});}else{if(_AQ<=6){return new F(function(){return _AL(_AR,_AS);});}else{return new T2(1,_11,new T(function(){var _AT=jsShowI(_AR);return B(_n(fromJSStr(_AT),new T2(1,_10,_AS)));}));}}},_AU=new T(function(){return B(unCStr(")"));}),_AV=function(_AW,_AX){var _AY=new T(function(){var _AZ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AP(0,_AW,_w)),_AU));})));},1);return B(_n(B(_AP(0,_AX,_w)),_AZ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_AY)));});},_B0=new T2(1,_kB,_w),_B1=function(_B2){return E(_B2);},_B3=function(_B4){return E(_B4);},_B5=function(_B6,_B7){return E(_B7);},_B8=function(_B9,_Ba){return E(_B9);},_Bb=function(_Bc){return E(_Bc);},_Bd=new T2(0,_Bb,_B8),_Be=function(_Bf,_Bg){return E(_Bf);},_Bh=new T5(0,_Bd,_B3,_B1,_B5,_Be),_Bi="flipped2",_Bj="flipped1",_Bk="c1y",_Bl="c1x",_Bm="w2z",_Bn="w2y",_Bo="w2x",_Bp="w1z",_Bq="w1y",_Br="w1x",_Bs="d2z",_Bt="d2y",_Bu="d2x",_Bv="d1z",_Bw="d1y",_Bx="d1x",_By="c2y",_Bz="c2x",_BA=function(_BB,_){var _BC=__get(_BB,E(_Br)),_BD=__get(_BB,E(_Bq)),_BE=__get(_BB,E(_Bp)),_BF=__get(_BB,E(_Bo)),_BG=__get(_BB,E(_Bn)),_BH=__get(_BB,E(_Bm)),_BI=__get(_BB,E(_Bl)),_BJ=__get(_BB,E(_Bk)),_BK=__get(_BB,E(_Bz)),_BL=__get(_BB,E(_By)),_BM=__get(_BB,E(_Bx)),_BN=__get(_BB,E(_Bw)),_BO=__get(_BB,E(_Bv)),_BP=__get(_BB,E(_Bu)),_BQ=__get(_BB,E(_Bt)),_BR=__get(_BB,E(_Bs)),_BS=__get(_BB,E(_Bj)),_BT=__get(_BB,E(_Bi));return {_:0,a:E(new T3(0,E(_BC),E(_BD),E(_BE))),b:E(new T3(0,E(_BF),E(_BG),E(_BH))),c:E(new T2(0,E(_BI),E(_BJ))),d:E(new T2(0,E(_BK),E(_BL))),e:E(new T3(0,E(_BM),E(_BN),E(_BO))),f:E(new T3(0,E(_BP),E(_BQ),E(_BR))),g:E(_BS),h:E(_BT)};},_BU=function(_BV,_){var _BW=E(_BV);if(!_BW._){return _w;}else{var _BX=B(_BA(E(_BW.a),_)),_BY=B(_BU(_BW.b,_));return new T2(1,_BX,_BY);}},_BZ=function(_C0){var _C1=E(_C0);return (E(_C1.b)-E(_C1.a)|0)+1|0;},_C2=function(_C3,_C4){var _C5=E(_C3),_C6=E(_C4);return (E(_C5.a)>_C6)?false:_C6<=E(_C5.b);},_C7=function(_C8){return new F(function(){return _AP(0,E(_C8),_w);});},_C9=function(_Ca,_Cb,_Cc){return new F(function(){return _AP(E(_Ca),E(_Cb),_Cc);});},_Cd=function(_Ce,_Cf){return new F(function(){return _AP(0,E(_Ce),_Cf);});},_Cg=function(_Ch,_Ci){return new F(function(){return _49(_Cd,_Ch,_Ci);});},_Cj=new T3(0,_C9,_C7,_Cg),_Ck=0,_Cl=function(_Cm,_Cn,_Co){return new F(function(){return A1(_Cm,new T2(1,_46,new T(function(){return B(A1(_Cn,_Co));})));});},_Cp=new T(function(){return B(unCStr("foldr1"));}),_Cq=new T(function(){return B(_mJ(_Cp));}),_Cr=function(_Cs,_Ct){var _Cu=E(_Ct);if(!_Cu._){return E(_Cq);}else{var _Cv=_Cu.a,_Cw=E(_Cu.b);if(!_Cw._){return E(_Cv);}else{return new F(function(){return A2(_Cs,_Cv,new T(function(){return B(_Cr(_Cs,_Cw));}));});}}},_Cx=new T(function(){return B(unCStr(" out of range "));}),_Cy=new T(function(){return B(unCStr("}.index: Index "));}),_Cz=new T(function(){return B(unCStr("Ix{"));}),_CA=new T2(1,_10,_w),_CB=new T2(1,_10,_CA),_CC=0,_CD=function(_CE){return E(E(_CE).a);},_CF=function(_CG,_CH,_CI,_CJ,_CK){var _CL=new T(function(){var _CM=new T(function(){var _CN=new T(function(){var _CO=new T(function(){var _CP=new T(function(){return B(A3(_Cr,_Cl,new T2(1,new T(function(){return B(A3(_CD,_CI,_CC,_CJ));}),new T2(1,new T(function(){return B(A3(_CD,_CI,_CC,_CK));}),_w)),_CB));});return B(_n(_Cx,new T2(1,_11,new T2(1,_11,_CP))));});return B(A(_CD,[_CI,_Ck,_CH,new T2(1,_10,_CO)]));});return B(_n(_Cy,new T2(1,_11,_CN)));},1);return B(_n(_CG,_CM));},1);return new F(function(){return err(B(_n(_Cz,_CL)));});},_CQ=function(_CR,_CS,_CT,_CU,_CV){return new F(function(){return _CF(_CR,_CS,_CV,_CT,_CU);});},_CW=function(_CX,_CY,_CZ,_D0){var _D1=E(_CZ);return new F(function(){return _CQ(_CX,_CY,_D1.a,_D1.b,_D0);});},_D2=function(_D3,_D4,_D5,_D6){return new F(function(){return _CW(_D6,_D5,_D4,_D3);});},_D7=new T(function(){return B(unCStr("Int"));}),_D8=function(_D9,_Da){return new F(function(){return _D2(_Cj,_Da,_D9,_D7);});},_Db=function(_Dc,_Dd){var _De=E(_Dc),_Df=E(_De.a),_Dg=E(_Dd);if(_Df>_Dg){return new F(function(){return _D8(_Dg,_De);});}else{if(_Dg>E(_De.b)){return new F(function(){return _D8(_Dg,_De);});}else{return _Dg-_Df|0;}}},_Dh=function(_Di){var _Dj=E(_Di);return new F(function(){return _t8(_Dj.a,_Dj.b);});},_Dk=function(_Dl){var _Dm=E(_Dl),_Dn=E(_Dm.a),_Do=E(_Dm.b);return (_Dn>_Do)?E(_Ck):(_Do-_Dn|0)+1|0;},_Dp=function(_Dq,_Dr){return new F(function(){return _ux(_Dr,E(_Dq).a);});},_Ds={_:0,a:_vn,b:_Dh,c:_Db,d:_Dp,e:_C2,f:_Dk,g:_BZ},_Dt=function(_Du,_Dv,_){while(1){var _Dw=B((function(_Dx,_Dy,_){var _Dz=E(_Dx);if(!_Dz._){return new T2(0,_kB,_Dy);}else{var _DA=B(A2(_Dz.a,_Dy,_));_Du=_Dz.b;_Dv=new T(function(){return E(E(_DA).b);});return __continue;}})(_Du,_Dv,_));if(_Dw!=__continue){return _Dw;}}},_DB=function(_DC,_DD){return new T2(1,_DC,_DD);},_DE=function(_DF,_DG){var _DH=E(_DG);return new T2(0,_DH.a,_DH.b);},_DI=function(_DJ){return E(E(_DJ).f);},_DK=function(_DL,_DM,_DN){var _DO=E(_DM),_DP=_DO.a,_DQ=_DO.b,_DR=function(_){var _DS=B(A2(_DI,_DL,_DO));if(_DS>=0){var _DT=newArr(_DS,_ik),_DU=_DT,_DV=E(_DS);if(!_DV){return new T(function(){return new T4(0,E(_DP),E(_DQ),0,_DU);});}else{var _DW=function(_DX,_DY,_){while(1){var _DZ=E(_DX);if(!_DZ._){return E(_);}else{var _=_DU[_DY]=_DZ.a;if(_DY!=(_DV-1|0)){var _E0=_DY+1|0;_DX=_DZ.b;_DY=_E0;continue;}else{return E(_);}}}},_=B(_DW(_DN,0,_));return new T(function(){return new T4(0,E(_DP),E(_DQ),_DV,_DU);});}}else{return E(_Al);}};return new F(function(){return _AB(_DR);});},_E1=function(_E2,_E3,_E4,_E5){var _E6=new T(function(){var _E7=E(_E5),_E8=_E7.c-1|0,_E9=new T(function(){return B(A2(_dT,_E3,_w));});if(0<=_E8){var _Ea=new T(function(){return B(_a4(_E3));}),_Eb=function(_Ec){var _Ed=new T(function(){var _Ee=new T(function(){return B(A1(_E4,new T(function(){return E(_E7.d[_Ec]);})));});return B(A3(_ac,_Ea,_DB,_Ee));});return new F(function(){return A3(_aa,_E3,_Ed,new T(function(){if(_Ec!=_E8){return B(_Eb(_Ec+1|0));}else{return E(_E9);}}));});};return B(_Eb(0));}else{return E(_E9);}}),_Ef=new T(function(){return B(_DE(_E2,_E5));});return new F(function(){return A3(_ac,B(_a4(_E3)),function(_Eg){return new F(function(){return _DK(_E2,_Ef,_Eg);});},_E6);});},_Eh=function(_Ei,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq){var _Er=B(_8u(_Ei));return new T2(0,new T3(0,E(B(A1(B(A1(_Er,_Ej)),_En))),E(B(A1(B(A1(_Er,_Ek)),_Eo))),E(B(A1(B(A1(_Er,_El)),_Ep)))),B(A1(B(A1(_Er,_Em)),_Eq)));},_Es=function(_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez,_EA,_EB){var _EC=B(_86(_Et));return new T2(0,new T3(0,E(B(A1(B(A1(_EC,_Eu)),_Ey))),E(B(A1(B(A1(_EC,_Ev)),_Ez))),E(B(A1(B(A1(_EC,_Ew)),_EA)))),B(A1(B(A1(_EC,_Ex)),_EB)));},_ED=1.0e-2,_EE=function(_EF,_EG,_EH,_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV){var _EW=B(_Eh(_jk,_EM,_EN,_EO,_EP,_ED,_ED,_ED,_ED)),_EX=E(_EW.a),_EY=B(_Es(_jk,_EI,_EJ,_EK,_EL,_EX.a,_EX.b,_EX.c,_EW.b)),_EZ=E(_EY.a);return new F(function(){return _pk(_EF,_EG,_EH,_EZ.a,_EZ.b,_EZ.c,_EY.b,_EM,_EN,_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV);});},_F0=function(_F1){var _F2=E(_F1),_F3=E(_F2.d),_F4=E(_F3.a),_F5=E(_F2.e),_F6=E(_F5.a),_F7=E(_F2.f),_F8=B(_EE(_F2.a,_F2.b,_F2.c,_F4.a,_F4.b,_F4.c,_F3.b,_F6.a,_F6.b,_F6.c,_F5.b,_F7.a,_F7.b,_F7.c,_F2.g,_F2.h,_F2.i));return {_:0,a:E(_F8.a),b:E(_F8.b),c:E(_F8.c),d:E(_F8.d),e:E(_F8.e),f:E(_F8.f),g:E(_F8.g),h:_F8.h,i:_F8.i};},_F9=function(_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi){var _Fj=B(_8s(B(_8q(_Fa))));return new F(function(){return A3(_86,_Fj,new T(function(){return B(_8w(_Fa,_Fb,_Fc,_Fd,_Ff,_Fg,_Fh));}),new T(function(){return B(A3(_8u,_Fj,_Fe,_Fi));}));});},_Fk=new T(function(){return B(unCStr("base"));}),_Fl=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fm=new T(function(){return B(unCStr("IOException"));}),_Fn=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fk,_Fl,_Fm),_Fo=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fn,_w,_w),_Fp=function(_Fq){return E(_Fo);},_Fr=function(_Fs){var _Ft=E(_Fs);return new F(function(){return _3G(B(_3E(_Ft.a)),_Fp,_Ft.b);});},_Fu=new T(function(){return B(unCStr(": "));}),_Fv=new T(function(){return B(unCStr(")"));}),_Fw=new T(function(){return B(unCStr(" ("));}),_Fx=new T(function(){return B(unCStr("interrupted"));}),_Fy=new T(function(){return B(unCStr("system error"));}),_Fz=new T(function(){return B(unCStr("unsatisified constraints"));}),_FA=new T(function(){return B(unCStr("user error"));}),_FB=new T(function(){return B(unCStr("permission denied"));}),_FC=new T(function(){return B(unCStr("illegal operation"));}),_FD=new T(function(){return B(unCStr("end of file"));}),_FE=new T(function(){return B(unCStr("resource exhausted"));}),_FF=new T(function(){return B(unCStr("resource busy"));}),_FG=new T(function(){return B(unCStr("does not exist"));}),_FH=new T(function(){return B(unCStr("already exists"));}),_FI=new T(function(){return B(unCStr("resource vanished"));}),_FJ=new T(function(){return B(unCStr("timeout"));}),_FK=new T(function(){return B(unCStr("unsupported operation"));}),_FL=new T(function(){return B(unCStr("hardware fault"));}),_FM=new T(function(){return B(unCStr("inappropriate type"));}),_FN=new T(function(){return B(unCStr("invalid argument"));}),_FO=new T(function(){return B(unCStr("failed"));}),_FP=new T(function(){return B(unCStr("protocol error"));}),_FQ=function(_FR,_FS){switch(E(_FR)){case 0:return new F(function(){return _n(_FH,_FS);});break;case 1:return new F(function(){return _n(_FG,_FS);});break;case 2:return new F(function(){return _n(_FF,_FS);});break;case 3:return new F(function(){return _n(_FE,_FS);});break;case 4:return new F(function(){return _n(_FD,_FS);});break;case 5:return new F(function(){return _n(_FC,_FS);});break;case 6:return new F(function(){return _n(_FB,_FS);});break;case 7:return new F(function(){return _n(_FA,_FS);});break;case 8:return new F(function(){return _n(_Fz,_FS);});break;case 9:return new F(function(){return _n(_Fy,_FS);});break;case 10:return new F(function(){return _n(_FP,_FS);});break;case 11:return new F(function(){return _n(_FO,_FS);});break;case 12:return new F(function(){return _n(_FN,_FS);});break;case 13:return new F(function(){return _n(_FM,_FS);});break;case 14:return new F(function(){return _n(_FL,_FS);});break;case 15:return new F(function(){return _n(_FK,_FS);});break;case 16:return new F(function(){return _n(_FJ,_FS);});break;case 17:return new F(function(){return _n(_FI,_FS);});break;default:return new F(function(){return _n(_Fx,_FS);});}},_FT=new T(function(){return B(unCStr("}"));}),_FU=new T(function(){return B(unCStr("{handle: "));}),_FV=function(_FW,_FX,_FY,_FZ,_G0,_G1){var _G2=new T(function(){var _G3=new T(function(){var _G4=new T(function(){var _G5=E(_FZ);if(!_G5._){return E(_G1);}else{var _G6=new T(function(){return B(_n(_G5,new T(function(){return B(_n(_Fv,_G1));},1)));},1);return B(_n(_Fw,_G6));}},1);return B(_FQ(_FX,_G4));}),_G7=E(_FY);if(!_G7._){return E(_G3);}else{return B(_n(_G7,new T(function(){return B(_n(_Fu,_G3));},1)));}}),_G8=E(_G0);if(!_G8._){var _G9=E(_FW);if(!_G9._){return E(_G2);}else{var _Ga=E(_G9.a);if(!_Ga._){var _Gb=new T(function(){var _Gc=new T(function(){return B(_n(_FT,new T(function(){return B(_n(_Fu,_G2));},1)));},1);return B(_n(_Ga.a,_Gc));},1);return new F(function(){return _n(_FU,_Gb);});}else{var _Gd=new T(function(){var _Ge=new T(function(){return B(_n(_FT,new T(function(){return B(_n(_Fu,_G2));},1)));},1);return B(_n(_Ga.a,_Ge));},1);return new F(function(){return _n(_FU,_Gd);});}}}else{return new F(function(){return _n(_G8.a,new T(function(){return B(_n(_Fu,_G2));},1));});}},_Gf=function(_Gg){var _Gh=E(_Gg);return new F(function(){return _FV(_Gh.a,_Gh.b,_Gh.c,_Gh.d,_Gh.f,_w);});},_Gi=function(_Gj,_Gk,_Gl){var _Gm=E(_Gk);return new F(function(){return _FV(_Gm.a,_Gm.b,_Gm.c,_Gm.d,_Gm.f,_Gl);});},_Gn=function(_Go,_Gp){var _Gq=E(_Go);return new F(function(){return _FV(_Gq.a,_Gq.b,_Gq.c,_Gq.d,_Gq.f,_Gp);});},_Gr=function(_Gs,_Gt){return new F(function(){return _49(_Gn,_Gs,_Gt);});},_Gu=new T3(0,_Gi,_Gf,_Gr),_Gv=new T(function(){return new T5(0,_Fp,_Gu,_Gw,_Fr,_Gf);}),_Gw=function(_Gx){return new T2(0,_Gv,_Gx);},_Gy=__Z,_Gz=7,_GA=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_GB=new T6(0,_Gy,_Gz,_w,_GA,_Gy,_Gy),_GC=new T(function(){return B(_Gw(_GB));}),_GD=function(_){return new F(function(){return die(_GC);});},_GE=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_GF=new T6(0,_Gy,_Gz,_w,_GE,_Gy,_Gy),_GG=new T(function(){return B(_Gw(_GF));}),_GH=function(_){return new F(function(){return die(_GG);});},_GI=function(_GJ,_){return new T2(0,_w,_GJ);},_GK=0.6,_GL=1,_GM=new T(function(){return B(unCStr(")"));}),_GN=function(_GO,_GP){var _GQ=new T(function(){var _GR=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AP(0,_GO,_w)),_GM));})));},1);return B(_n(B(_AP(0,_GP,_w)),_GR));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GQ)));});},_GS=function(_GT,_GU){var _GV=new T(function(){var _GW=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_AP(0,_GU,_w)),_GM));})));},1);return B(_n(B(_AP(0,_GT,_w)),_GW));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_GV)));});},_GX=function(_GY){var _GZ=E(_GY);if(!_GZ._){return E(_GI);}else{var _H0=new T(function(){return B(_GX(_GZ.b));}),_H1=function(_H2){var _H3=E(_H2);if(!_H3._){return E(_H0);}else{var _H4=_H3.a,_H5=new T(function(){return B(_H1(_H3.b));}),_H6=new T(function(){return 0.1*E(E(_H4).e)/1.0e-2;}),_H7=new T(function(){var _H8=E(_H4);if(_H8.a!=_H8.b){return E(_GL);}else{return E(_GK);}}),_H9=function(_Ha,_){var _Hb=E(_Ha),_Hc=_Hb.c,_Hd=_Hb.d,_He=E(_Hb.a),_Hf=E(_Hb.b),_Hg=E(_H4),_Hh=_Hg.a,_Hi=_Hg.b,_Hj=E(_Hg.c),_Hk=_Hj.b,_Hl=E(_Hj.a),_Hm=_Hl.a,_Hn=_Hl.b,_Ho=_Hl.c,_Hp=E(_Hg.d),_Hq=_Hp.b,_Hr=E(_Hp.a),_Hs=_Hr.a,_Ht=_Hr.b,_Hu=_Hr.c;if(_He>_Hh){return new F(function(){return _GH(_);});}else{if(_Hh>_Hf){return new F(function(){return _GH(_);});}else{if(_He>_Hi){return new F(function(){return _GD(_);});}else{if(_Hi>_Hf){return new F(function(){return _GD(_);});}else{var _Hv=_Hh-_He|0;if(0>_Hv){return new F(function(){return _GN(_Hc,_Hv);});}else{if(_Hv>=_Hc){return new F(function(){return _GN(_Hc,_Hv);});}else{var _Hw=E(_Hd[_Hv]),_Hx=E(_Hw.c),_Hy=_Hx.b,_Hz=E(_Hx.a),_HA=_Hz.a,_HB=_Hz.b,_HC=_Hz.c,_HD=E(_Hw.e),_HE=E(_HD.a),_HF=B(_Eh(_jk,_Hm,_Hn,_Ho,_Hk,_HA,_HB,_HC,_Hy)),_HG=E(_HF.a),_HH=B(_Eh(_jk,_HG.a,_HG.b,_HG.c,_HF.b,_Hm,_Hn,_Ho,_Hk)),_HI=E(_HH.a),_HJ=_Hi-_He|0;if(0>_HJ){return new F(function(){return _GS(_HJ,_Hc);});}else{if(_HJ>=_Hc){return new F(function(){return _GS(_HJ,_Hc);});}else{var _HK=E(_Hd[_HJ]),_HL=E(_HK.c),_HM=_HL.b,_HN=E(_HL.a),_HO=_HN.a,_HP=_HN.b,_HQ=_HN.c,_HR=E(_HK.e),_HS=E(_HR.a),_HT=B(_Eh(_jk,_Hs,_Ht,_Hu,_Hq,_HO,_HP,_HQ,_HM)),_HU=E(_HT.a),_HV=B(_Eh(_jk,_HU.a,_HU.b,_HU.c,_HT.b,_Hs,_Ht,_Hu,_Hq)),_HW=E(_HV.a),_HX=E(_HI.a)+E(_HI.b)+E(_HI.c)+E(_HH.b)+E(_HW.a)+E(_HW.b)+E(_HW.c)+E(_HV.b);if(!_HX){var _HY=B(A2(_H5,_Hb,_));return new T2(0,new T2(1,_kB,new T(function(){return E(E(_HY).a);})),new T(function(){return E(E(_HY).b);}));}else{var _HZ=new T(function(){return  -((B(_F9(_jQ,_HE.a,_HE.b,_HE.c,_HD.b,_Hm,_Hn,_Ho,_Hk))-B(_F9(_jQ,_HS.a,_HS.b,_HS.c,_HR.b,_Hs,_Ht,_Hu,_Hq))-E(_H6))/_HX);}),_I0=function(_I1,_I2,_I3,_I4,_){var _I5=new T(function(){var _I6=function(_I7,_I8,_I9,_Ia,_Ib){if(_I7>_Hi){return E(_Ib);}else{if(_Hi>_I8){return E(_Ib);}else{var _Ic=function(_){var _Id=newArr(_I9,_ik),_Ie=_Id,_If=function(_Ig,_){while(1){if(_Ig!=_I9){var _=_Ie[_Ig]=_Ia[_Ig],_Ih=_Ig+1|0;_Ig=_Ih;continue;}else{return E(_);}}},_=B(_If(0,_)),_Ii=_Hi-_I7|0;if(0>_Ii){return new F(function(){return _GS(_Ii,_I9);});}else{if(_Ii>=_I9){return new F(function(){return _GS(_Ii,_I9);});}else{var _=_Ie[_Ii]=new T(function(){var _Ij=E(_Ia[_Ii]),_Ik=E(_Ij.e),_Il=E(_Ik.a),_Im=B(_Eh(_jk,_HO,_HP,_HQ,_HM,_Hs,_Ht,_Hu,_Hq)),_In=E(_Im.a),_Io=E(_HZ)*E(_H7),_Ip=B(_Eh(_jk,_In.a,_In.b,_In.c,_Im.b,_Io,_Io,_Io,_Io)),_Iq=E(_Ip.a),_Ir=B(_Es(_jk,_Il.a,_Il.b,_Il.c,_Ik.b, -E(_Iq.a), -E(_Iq.b), -E(_Iq.c), -E(_Ip.b)));return {_:0,a:E(_Ij.a),b:E(_Ij.b),c:E(_Ij.c),d:E(_Ij.d),e:E(new T2(0,E(_Ir.a),E(_Ir.b))),f:E(_Ij.f),g:E(_Ij.g),h:_Ij.h,i:_Ij.i};});return new T4(0,E(_I7),E(_I8),_I9,_Ie);}}};return new F(function(){return _AB(_Ic);});}}};if(_I1>_Hh){return B(_I6(_I1,_I2,_I3,_I4,new T4(0,E(_I1),E(_I2),_I3,_I4)));}else{if(_Hh>_I2){return B(_I6(_I1,_I2,_I3,_I4,new T4(0,E(_I1),E(_I2),_I3,_I4)));}else{var _Is=function(_){var _It=newArr(_I3,_ik),_Iu=_It,_Iv=function(_Iw,_){while(1){if(_Iw!=_I3){var _=_Iu[_Iw]=_I4[_Iw],_Ix=_Iw+1|0;_Iw=_Ix;continue;}else{return E(_);}}},_=B(_Iv(0,_)),_Iy=_Hh-_I1|0;if(0>_Iy){return new F(function(){return _GN(_I3,_Iy);});}else{if(_Iy>=_I3){return new F(function(){return _GN(_I3,_Iy);});}else{var _=_Iu[_Iy]=new T(function(){var _Iz=E(_I4[_Iy]),_IA=E(_Iz.e),_IB=E(_IA.a),_IC=B(_Eh(_jk,_HA,_HB,_HC,_Hy,_Hm,_Hn,_Ho,_Hk)),_ID=E(_IC.a),_IE=E(_HZ)*E(_H7),_IF=B(_Eh(_jk,_ID.a,_ID.b,_ID.c,_IC.b,_IE,_IE,_IE,_IE)),_IG=E(_IF.a),_IH=B(_Es(_jk,_IB.a,_IB.b,_IB.c,_IA.b,_IG.a,_IG.b,_IG.c,_IF.b));return {_:0,a:E(_Iz.a),b:E(_Iz.b),c:E(_Iz.c),d:E(_Iz.d),e:E(new T2(0,E(_IH.a),E(_IH.b))),f:E(_Iz.f),g:E(_Iz.g),h:_Iz.h,i:_Iz.i};});return new T4(0,E(_I1),E(_I2),_I3,_Iu);}}},_II=B(_AB(_Is));return B(_I6(E(_II.a),E(_II.b),_II.c,_II.d,_II));}}});return new T2(0,_kB,_I5);};if(!E(_Hg.f)){var _IJ=B(_I0(_He,_Hf,_Hc,_Hd,_)),_IK=B(A2(_H5,new T(function(){return E(E(_IJ).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IJ).a);}),new T(function(){return E(E(_IK).a);})),new T(function(){return E(E(_IK).b);}));}else{if(E(_HZ)<0){var _IL=B(A2(_H5,_Hb,_));return new T2(0,new T2(1,_kB,new T(function(){return E(E(_IL).a);})),new T(function(){return E(E(_IL).b);}));}else{var _IM=B(_I0(_He,_Hf,_Hc,_Hd,_)),_IN=B(A2(_H5,new T(function(){return E(E(_IM).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IM).a);}),new T(function(){return E(E(_IN).a);})),new T(function(){return E(E(_IN).b);}));}}}}}}}}}}}};return E(_H9);}};return new F(function(){return _H1(_GZ.a);});}},_IO=function(_,_IP){var _IQ=new T(function(){return B(_GX(E(_IP).a));}),_IR=function(_IS){var _IT=E(_IS);return (_IT==1)?E(new T2(1,_IQ,_w)):new T2(1,_IQ,new T(function(){return B(_IR(_IT-1|0));}));},_IU=B(_Dt(B(_IR(5)),new T(function(){return E(E(_IP).b);}),_)),_IV=new T(function(){return B(_E1(_Ds,_Bh,_F0,new T(function(){return E(E(_IU).b);})));});return new T2(0,_kB,_IV);},_IW=function(_IX,_IY,_IZ,_J0,_J1){var _J2=B(_8s(B(_8q(_IX))));return new F(function(){return A3(_86,_J2,new T(function(){return B(A3(_8u,_J2,_IY,_J0));}),new T(function(){return B(A3(_8u,_J2,_IZ,_J1));}));});},_J3=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_J4=new T6(0,_Gy,_Gz,_w,_J3,_Gy,_Gy),_J5=new T(function(){return B(_Gw(_J4));}),_J6=function(_){return new F(function(){return die(_J5);});},_J7=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_J8=new T6(0,_Gy,_Gz,_w,_J7,_Gy,_Gy),_J9=new T(function(){return B(_Gw(_J8));}),_Ja=function(_){return new F(function(){return die(_J9);});},_Jb=false,_Jc=true,_Jd=function(_Je){var _Jf=E(_Je),_Jg=_Jf.b,_Jh=E(_Jf.d),_Ji=E(_Jf.e),_Jj=E(_Ji.a),_Jk=E(_Jf.g),_Jl=B(A1(_Jg,_Jh.a)),_Jm=B(_m2(_jQ,_Jl.a,_Jl.b,_Jl.c,_Jk.a,_Jk.b,_Jk.c));return {_:0,a:E(_Jf.a),b:E(_Jg),c:E(_Jf.c),d:E(_Jh),e:E(new T2(0,E(new T3(0,E(_Jj.a)+E(_Jm.a)*1.0e-2,E(_Jj.b)+E(_Jm.b)*1.0e-2,E(_Jj.c)+E(_Jm.c)*1.0e-2)),E(_Ji.b))),f:E(_Jf.f),g:E(_Jk),h:_Jf.h,i:_Jf.i};},_Jn=new T(function(){return eval("__strict(collideBound)");}),_Jo=new T(function(){return eval("__strict(mouseContact)");}),_Jp=new T(function(){return eval("__strict(collide)");}),_Jq=function(_Jr){var _Js=E(_Jr);if(!_Js._){return __Z;}else{return new F(function(){return _n(_Js.a,new T(function(){return B(_Jq(_Js.b));},1));});}},_Jt=0,_Ju=new T3(0,E(_Jt),E(_Jt),E(_Jt)),_Jv=new T2(0,E(_Ju),E(_Jt)),_Jw=new T2(0,_jQ,_kp),_Jx=new T(function(){return B(_hQ(_Jw));}),_Jy=function(_Jz,_){var _JA=B(_E1(_Ds,_Bh,_Jd,_Jz)),_JB=E(_JA.a),_JC=E(_JA.b);if(_JB<=_JC){var _JD=function(_JE,_JF,_JG,_JH,_JI,_){if(_JF>_JE){return new F(function(){return _Ja(_);});}else{if(_JE>_JG){return new F(function(){return _Ja(_);});}else{var _JJ=new T(function(){var _JK=_JE-_JF|0;if(0>_JK){return B(_GS(_JK,_JH));}else{if(_JK>=_JH){return B(_GS(_JK,_JH));}else{return E(_JI[_JK]);}}}),_JL=function(_JM,_JN,_JO,_JP,_JQ,_){var _JR=E(_JM);if(!_JR._){return new T2(0,_w,new T4(0,E(_JN),E(_JO),_JP,_JQ));}else{var _JS=E(_JR.a);if(_JN>_JS){return new F(function(){return _J6(_);});}else{if(_JS>_JO){return new F(function(){return _J6(_);});}else{var _JT=E(_JJ),_JU=_JS-_JN|0;if(0>_JU){return new F(function(){return _GN(_JP,_JU);});}else{if(_JU>=_JP){return new F(function(){return _GN(_JP,_JU);});}else{var _JV=E(_JQ[_JU]),_JW=__app2(E(_Jp),B(_kC(new T2(1,new T2(0,_AG,_JT.h),new T2(1,new T2(0,_AF,_JT.i),_w)))),B(_kC(new T2(1,new T2(0,_AG,_JV.h),new T2(1,new T2(0,_AF,_JV.i),_w))))),_JX=__arr2lst(0,_JW),_JY=B(_BU(_JX,_)),_JZ=B(_JL(_JR.b,_JN,_JO,_JP,_JQ,_)),_K0=new T(function(){var _K1=new T(function(){return _JE!=_JS;}),_K2=function(_K3){var _K4=E(_K3);if(!_K4._){return __Z;}else{var _K5=_K4.b,_K6=E(_K4.a),_K7=E(_K6.b),_K8=E(_K6.a),_K9=E(_K6.c),_Ka=_K9.a,_Kb=_K9.b,_Kc=E(_K6.e),_Kd=E(_K6.d),_Ke=_Kd.a,_Kf=_Kd.b,_Kg=E(_K6.f),_Kh=new T(function(){var _Ki=B(_lf(_jQ,_Kg.a,_Kg.b,_Kg.c)),_Kj=Math.sqrt(B(_IW(_jQ,_Ke,_Kf,_Ke,_Kf)));return new T3(0,_Kj*E(_Ki.a),_Kj*E(_Ki.b),_Kj*E(_Ki.c));}),_Kk=new T(function(){var _Kl=B(_lf(_jQ,_Kc.a,_Kc.b,_Kc.c)),_Km=Math.sqrt(B(_IW(_jQ,_Ka,_Kb,_Ka,_Kb)));return new T3(0,_Km*E(_Kl.a),_Km*E(_Kl.b),_Km*E(_Kl.c));}),_Kn=new T(function(){var _Ko=B(A1(_Jx,_K7)),_Kp=B(_lf(_jQ,_Ko.a,_Ko.b,_Ko.c));return new T3(0,E(_Kp.a),E(_Kp.b),E(_Kp.c));}),_Kq=new T(function(){var _Kr=B(A1(_Jx,_K8)),_Ks=B(_lf(_jQ,_Kr.a,_Kr.b,_Kr.c));return new T3(0,E(_Ks.a),E(_Ks.b),E(_Ks.c));}),_Kt=E(_K7.a)+ -E(_K8.a),_Ku=E(_K7.b)+ -E(_K8.b),_Kv=E(_K7.c)+ -E(_K8.c),_Kw=new T(function(){return Math.sqrt(B(_8w(_jQ,_Kt,_Ku,_Kv,_Kt,_Ku,_Kv)));}),_Kx=new T(function(){var _Ky=1/E(_Kw);return new T3(0,_Kt*_Ky,_Ku*_Ky,_Kv*_Ky);}),_Kz=new T(function(){if(!E(_K6.g)){return E(_Kx);}else{var _KA=E(_Kx);return new T3(0,-1*E(_KA.a),-1*E(_KA.b),-1*E(_KA.c));}}),_KB=new T(function(){if(!E(_K6.h)){return E(_Kx);}else{var _KC=E(_Kx);return new T3(0,-1*E(_KC.a),-1*E(_KC.b),-1*E(_KC.c));}});return (!E(_K1))?new T2(1,new T(function(){var _KD=E(_Kz),_KE=E(_KD.b),_KF=E(_KD.c),_KG=E(_KD.a),_KH=E(_Kq),_KI=E(_KH.c),_KJ=E(_KH.b),_KK=E(_KH.a),_KL=E(_Kk),_KM=E(_KL.c),_KN=E(_KL.b),_KO=E(_KL.a),_KP=_KE*_KI-_KJ*_KF,_KQ=_KF*_KK-_KI*_KG,_KR=_KG*_KJ-_KK*_KE,_KS=B(_8w(_jQ,_KQ*_KM-_KN*_KR,_KR*_KO-_KM*_KP,_KP*_KN-_KO*_KQ,_KK,_KJ,_KI));return new T6(0,_JE,_JS,E(new T2(0,E(new T3(0,E(_KP),E(_KQ),E(_KR))),E(_KS))),E(_Jv),_Kw,_Jb);}),new T2(1,new T(function(){var _KT=E(_KB),_KU=E(_KT.b),_KV=E(_KT.c),_KW=E(_KT.a),_KX=E(_Kn),_KY=E(_KX.c),_KZ=E(_KX.b),_L0=E(_KX.a),_L1=E(_Kh),_L2=E(_L1.c),_L3=E(_L1.b),_L4=E(_L1.a),_L5=_KU*_KY-_KZ*_KV,_L6=_KV*_L0-_KY*_KW,_L7=_KW*_KZ-_L0*_KU,_L8=B(_8w(_jQ,_L6*_L2-_L3*_L7,_L7*_L4-_L2*_L5,_L5*_L3-_L4*_L6,_L0,_KZ,_KY));return new T6(0,_JE,_JS,E(_Jv),E(new T2(0,E(new T3(0,E(_L5),E(_L6),E(_L7))),E(_L8))),_Kw,_Jb);}),new T(function(){return B(_K2(_K5));}))):new T2(1,new T(function(){var _L9=E(_Kz),_La=E(_L9.b),_Lb=E(_L9.c),_Lc=E(_L9.a),_Ld=E(_Kq),_Le=_Ld.a,_Lf=_Ld.b,_Lg=_Ld.c,_Lh=B(_m2(_jQ,_Lc,_La,_Lb,_Le,_Lf,_Lg)),_Li=E(_Kk),_Lj=E(_Li.c),_Lk=E(_Li.b),_Ll=E(_Li.a),_Lm=B(_8w(_jQ,_La*_Lj-_Lk*_Lb,_Lb*_Ll-_Lj*_Lc,_Lc*_Lk-_Ll*_La,_Le,_Lf,_Lg)),_Ln=E(_KB),_Lo=E(_Ln.b),_Lp=E(_Ln.c),_Lq=E(_Ln.a),_Lr=E(_Kn),_Ls=_Lr.a,_Lt=_Lr.b,_Lu=_Lr.c,_Lv=B(_m2(_jQ,_Lq,_Lo,_Lp,_Ls,_Lt,_Lu)),_Lw=E(_Kh),_Lx=E(_Lw.c),_Ly=E(_Lw.b),_Lz=E(_Lw.a),_LA=B(_8w(_jQ,_Lo*_Lx-_Ly*_Lp,_Lp*_Lz-_Lx*_Lq,_Lq*_Ly-_Lz*_Lo,_Ls,_Lt,_Lu));return new T6(0,_JE,_JS,E(new T2(0,E(new T3(0,E(_Lh.a),E(_Lh.b),E(_Lh.c))),E(_Lm))),E(new T2(0,E(new T3(0,E(_Lv.a),E(_Lv.b),E(_Lv.c))),E(_LA))),_Kw,_Jc);}),new T(function(){return B(_K2(_K5));}));}};return B(_K2(_JY));});return new T2(0,new T2(1,_K0,new T(function(){return E(E(_JZ).a);})),new T(function(){return E(E(_JZ).b);}));}}}}}},_LB=B(_JL(B(_sx(_JE,_JC)),_JF,_JG,_JH,_JI,_)),_LC=E(_JJ),_LD=E(_LC.d).a,_LE=__app1(E(_Jn),B(_kC(new T2(1,new T2(0,_AG,_LC.h),new T2(1,new T2(0,_AF,_LC.i),_w))))),_LF=__arr2lst(0,_LE),_LG=B(_BU(_LF,_)),_LH=__app1(E(_Jo),_JE),_LI=__arr2lst(0,_LH),_LJ=B(_BU(_LI,_));if(_JE!=_JC){var _LK=E(_LB),_LL=E(_LK.b),_LM=B(_JD(_JE+1|0,E(_LL.a),E(_LL.b),_LL.c,_LL.d,_)),_LN=new T(function(){var _LO=new T(function(){var _LP=B(A1(_Jx,_LD)),_LQ=B(_lf(_jQ,_LP.a,_LP.b,_LP.c));return new T3(0,E(_LQ.a),E(_LQ.b),E(_LQ.c));}),_LR=new T(function(){var _LS=new T(function(){return B(_Jq(_LK.a));}),_LT=function(_LU){var _LV=E(_LU);if(!_LV._){return E(_LS);}else{var _LW=E(_LV.a),_LX=E(_LW.b),_LY=E(_LW.a),_LZ=E(_LW.c),_M0=_LZ.a,_M1=_LZ.b,_M2=E(_LW.e);return new T2(1,new T(function(){var _M3=E(_LX.a)+ -E(_LY.a),_M4=E(_LX.b)+ -E(_LY.b),_M5=E(_LX.c)+ -E(_LY.c),_M6=B(A1(_Jx,_LY)),_M7=B(_lf(_jQ,_M6.a,_M6.b,_M6.c)),_M8=_M7.a,_M9=_M7.b,_Ma=_M7.c,_Mb=Math.sqrt(B(_8w(_jQ,_M3,_M4,_M5,_M3,_M4,_M5))),_Mc=1/_Mb,_Md=_M3*_Mc,_Me=_M4*_Mc,_Mf=_M5*_Mc,_Mg=B(_m2(_jQ,_Md,_Me,_Mf,_M8,_M9,_Ma)),_Mh=B(_lf(_jQ,_M2.a,_M2.b,_M2.c)),_Mi=Math.sqrt(B(_IW(_jQ,_M0,_M1,_M0,_M1))),_Mj=_Mi*E(_Mh.a),_Mk=_Mi*E(_Mh.b),_Ml=_Mi*E(_Mh.c),_Mm=B(_8w(_jQ,_Me*_Ml-_Mk*_Mf,_Mf*_Mj-_Ml*_Md,_Md*_Mk-_Mj*_Me,_M8,_M9,_Ma));return new T6(0,_JE,_JE,E(new T2(0,E(new T3(0,E(_Mg.a),E(_Mg.b),E(_Mg.c))),E(_Mm))),E(_Jv),_Mb,_Jc);}),new T(function(){return B(_LT(_LV.b));}));}};return B(_LT(_LG));}),_Mn=function(_Mo){var _Mp=E(_Mo);if(!_Mp._){return E(_LR);}else{var _Mq=E(_Mp.a),_Mr=E(_Mq.b),_Ms=new T(function(){var _Mt=E(_LD),_Mu=E(_Mr.c)+ -E(_Mt.c),_Mv=E(_Mr.b)+ -E(_Mt.b),_Mw=E(_Mr.a)+ -E(_Mt.a),_Mx=Math.sqrt(B(_8w(_jQ,_Mw,_Mv,_Mu,_Mw,_Mv,_Mu))),_My=function(_Mz,_MA,_MB){var _MC=E(_LO),_MD=_MC.a,_ME=_MC.b,_MF=_MC.c,_MG=B(_m2(_jQ,_Mz,_MA,_MB,_MD,_ME,_MF)),_MH=B(_8w(_jQ,_MA*0-0*_MB,_MB*0-0*_Mz,_Mz*0-0*_MA,_MD,_ME,_MF));return new T6(0,_JE,_JE,new T2(0,E(new T3(0,E(_MG.a),E(_MG.b),E(_MG.c))),E(_MH)),_Jv,_Mx,_Jc);};if(!E(_Mq.g)){var _MI=1/_Mx,_MJ=B(_My(_Mw*_MI,_Mv*_MI,_Mu*_MI));return new T6(0,_MJ.a,_MJ.b,E(_MJ.c),E(_MJ.d),_MJ.e,_MJ.f);}else{var _MK=1/_Mx,_ML=B(_My(-1*_Mw*_MK,-1*_Mv*_MK,-1*_Mu*_MK));return new T6(0,_ML.a,_ML.b,E(_ML.c),E(_ML.d),_ML.e,_ML.f);}});return new T2(1,_Ms,new T(function(){return B(_Mn(_Mp.b));}));}};return B(_Mn(_LJ));});return new T2(0,new T2(1,_LN,new T(function(){return E(E(_LM).a);})),new T(function(){return E(E(_LM).b);}));}else{var _MM=new T(function(){var _MN=new T(function(){var _MO=B(A1(_Jx,_LD)),_MP=B(_lf(_jQ,_MO.a,_MO.b,_MO.c));return new T3(0,E(_MP.a),E(_MP.b),E(_MP.c));}),_MQ=new T(function(){var _MR=new T(function(){return B(_Jq(E(_LB).a));}),_MS=function(_MT){var _MU=E(_MT);if(!_MU._){return E(_MR);}else{var _MV=E(_MU.a),_MW=E(_MV.b),_MX=E(_MV.a),_MY=E(_MV.c),_MZ=_MY.a,_N0=_MY.b,_N1=E(_MV.e);return new T2(1,new T(function(){var _N2=E(_MW.a)+ -E(_MX.a),_N3=E(_MW.b)+ -E(_MX.b),_N4=E(_MW.c)+ -E(_MX.c),_N5=B(A1(_Jx,_MX)),_N6=B(_lf(_jQ,_N5.a,_N5.b,_N5.c)),_N7=_N6.a,_N8=_N6.b,_N9=_N6.c,_Na=Math.sqrt(B(_8w(_jQ,_N2,_N3,_N4,_N2,_N3,_N4))),_Nb=1/_Na,_Nc=_N2*_Nb,_Nd=_N3*_Nb,_Ne=_N4*_Nb,_Nf=B(_m2(_jQ,_Nc,_Nd,_Ne,_N7,_N8,_N9)),_Ng=B(_lf(_jQ,_N1.a,_N1.b,_N1.c)),_Nh=Math.sqrt(B(_IW(_jQ,_MZ,_N0,_MZ,_N0))),_Ni=_Nh*E(_Ng.a),_Nj=_Nh*E(_Ng.b),_Nk=_Nh*E(_Ng.c),_Nl=B(_8w(_jQ,_Nd*_Nk-_Nj*_Ne,_Ne*_Ni-_Nk*_Nc,_Nc*_Nj-_Ni*_Nd,_N7,_N8,_N9));return new T6(0,_JE,_JE,E(new T2(0,E(new T3(0,E(_Nf.a),E(_Nf.b),E(_Nf.c))),E(_Nl))),E(_Jv),_Na,_Jc);}),new T(function(){return B(_MS(_MU.b));}));}};return B(_MS(_LG));}),_Nm=function(_Nn){var _No=E(_Nn);if(!_No._){return E(_MQ);}else{var _Np=E(_No.a),_Nq=E(_Np.b),_Nr=new T(function(){var _Ns=E(_LD),_Nt=E(_Nq.c)+ -E(_Ns.c),_Nu=E(_Nq.b)+ -E(_Ns.b),_Nv=E(_Nq.a)+ -E(_Ns.a),_Nw=Math.sqrt(B(_8w(_jQ,_Nv,_Nu,_Nt,_Nv,_Nu,_Nt))),_Nx=function(_Ny,_Nz,_NA){var _NB=E(_MN),_NC=_NB.a,_ND=_NB.b,_NE=_NB.c,_NF=B(_m2(_jQ,_Ny,_Nz,_NA,_NC,_ND,_NE)),_NG=B(_8w(_jQ,_Nz*0-0*_NA,_NA*0-0*_Ny,_Ny*0-0*_Nz,_NC,_ND,_NE));return new T6(0,_JE,_JE,new T2(0,E(new T3(0,E(_NF.a),E(_NF.b),E(_NF.c))),E(_NG)),_Jv,_Nw,_Jc);};if(!E(_Np.g)){var _NH=1/_Nw,_NI=B(_Nx(_Nv*_NH,_Nu*_NH,_Nt*_NH));return new T6(0,_NI.a,_NI.b,E(_NI.c),E(_NI.d),_NI.e,_NI.f);}else{var _NJ=1/_Nw,_NK=B(_Nx(-1*_Nv*_NJ,-1*_Nu*_NJ,-1*_Nt*_NJ));return new T6(0,_NK.a,_NK.b,E(_NK.c),E(_NK.d),_NK.e,_NK.f);}});return new T2(1,_Nr,new T(function(){return B(_Nm(_No.b));}));}};return B(_Nm(_LJ));});return new T2(0,new T2(1,_MM,_w),new T(function(){return E(E(_LB).b);}));}}}},_NL=B(_JD(_JB,_JB,_JC,_JA.c,_JA.d,_));return new F(function(){return _IO(_,_NL);});}else{return new F(function(){return _IO(_,new T2(0,_w,_JA));});}},_NM=new T(function(){return eval("__strict(passObject)");}),_NN=new T(function(){return eval("__strict(refresh)");}),_NO=function(_NP,_){var _NQ=__app0(E(_NN)),_NR=__app0(E(_AK)),_NS=E(_NP),_NT=_NS.c,_NU=_NS.d,_NV=E(_NS.a),_NW=E(_NS.b);if(_NV<=_NW){if(_NV>_NW){return E(_AI);}else{if(0>=_NT){return new F(function(){return _AV(_NT,0);});}else{var _NX=E(_NU[0]),_NY=E(_NM),_NZ=__app2(_NY,_NV,B(_kC(new T2(1,new T2(0,_AG,_NX.h),new T2(1,new T2(0,_AF,_NX.i),_w)))));if(_NV!=_NW){var _O0=function(_O1,_){if(_NV>_O1){return E(_AI);}else{if(_O1>_NW){return E(_AI);}else{var _O2=_O1-_NV|0;if(0>_O2){return new F(function(){return _AV(_NT,_O2);});}else{if(_O2>=_NT){return new F(function(){return _AV(_NT,_O2);});}else{var _O3=E(_NU[_O2]),_O4=__app2(_NY,_O1,B(_kC(new T2(1,new T2(0,_AG,_O3.h),new T2(1,new T2(0,_AF,_O3.i),_w)))));if(_O1!=_NW){var _O5=B(_O0(_O1+1|0,_));return new T2(1,_kB,_O5);}else{return _B0;}}}}}},_O6=B(_O0(_NV+1|0,_)),_O7=__app0(E(_AJ)),_O8=B(_Jy(_NS,_));return new T(function(){return E(E(_O8).b);});}else{var _O9=__app0(E(_AJ)),_Oa=B(_Jy(_NS,_));return new T(function(){return E(E(_Oa).b);});}}}}else{var _Ob=__app0(E(_AJ)),_Oc=B(_Jy(_NS,_));return new T(function(){return E(E(_Oc).b);});}},_Od=function(_Oe,_){while(1){var _Of=E(_Oe);if(!_Of._){return _kB;}else{var _Og=_Of.b,_Oh=E(_Of.a);switch(_Oh._){case 0:var _Oi=B(A1(_Oh.a,_));_Oe=B(_n(_Og,new T2(1,_Oi,_w)));continue;case 1:_Oe=B(_n(_Og,_Oh.a));continue;default:_Oe=_Og;continue;}}}},_Oj=function(_Ok,_Ol,_){var _Om=E(_Ok);switch(_Om._){case 0:var _On=B(A1(_Om.a,_));return new F(function(){return _Od(B(_n(_Ol,new T2(1,_On,_w))),_);});break;case 1:return new F(function(){return _Od(B(_n(_Ol,_Om.a)),_);});break;default:return new F(function(){return _Od(_Ol,_);});}},_Oo=new T0(2),_Op=function(_Oq){return new T0(2);},_Or=function(_Os,_Ot,_Ou){return function(_){var _Ov=E(_Os),_Ow=rMV(_Ov),_Ox=E(_Ow);if(!_Ox._){var _Oy=new T(function(){var _Oz=new T(function(){return B(A1(_Ou,_kB));});return B(_n(_Ox.b,new T2(1,new T2(0,_Ot,function(_OA){return E(_Oz);}),_w)));}),_=wMV(_Ov,new T2(0,_Ox.a,_Oy));return _Oo;}else{var _OB=E(_Ox.a);if(!_OB._){var _=wMV(_Ov,new T2(0,_Ot,_w));return new T(function(){return B(A1(_Ou,_kB));});}else{var _=wMV(_Ov,new T1(1,_OB.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Ou,_kB));}),new T2(1,new T(function(){return B(A2(_OB.a,_Ot,_Op));}),_w)));}}};},_OC=new T(function(){return E(_q3);}),_OD=new T(function(){return eval("window.requestAnimationFrame");}),_OE=new T1(1,_w),_OF=function(_OG,_OH){return function(_){var _OI=E(_OG),_OJ=rMV(_OI),_OK=E(_OJ);if(!_OK._){var _OL=_OK.a,_OM=E(_OK.b);if(!_OM._){var _=wMV(_OI,_OE);return new T(function(){return B(A1(_OH,_OL));});}else{var _ON=E(_OM.a),_=wMV(_OI,new T2(0,_ON.a,_OM.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OH,_OL));}),new T2(1,new T(function(){return B(A1(_ON.b,_Op));}),_w)));}}else{var _OO=new T(function(){var _OP=function(_OQ){var _OR=new T(function(){return B(A1(_OH,_OQ));});return function(_OS){return E(_OR);};};return B(_n(_OK.a,new T2(1,_OP,_w)));}),_=wMV(_OI,new T1(1,_OO));return _Oo;}};},_OT=function(_OU,_OV){return new T1(0,B(_OF(_OU,_OV)));},_OW=function(_OX,_OY){var _OZ=new T(function(){return new T1(0,B(_Or(_OX,_kB,_Op)));});return function(_){var _P0=__createJSFunc(2,function(_P1,_){var _P2=B(_Oj(_OZ,_w,_));return _OC;}),_P3=__app1(E(_OD),_P0);return new T(function(){return B(_OT(_OX,_OY));});};},_P4=new T1(1,_w),_P5=function(_P6,_P7,_){var _P8=function(_){var _P9=nMV(_P6),_Pa=_P9;return new T(function(){var _Pb=new T(function(){return B(_Pc(_));}),_Pd=function(_){var _Pe=rMV(_Pa),_Pf=B(A2(_P7,_Pe,_)),_=wMV(_Pa,_Pf),_Pg=function(_){var _Ph=nMV(_P4);return new T(function(){return new T1(0,B(_OW(_Ph,function(_Pi){return E(_Pb);})));});};return new T1(0,_Pg);},_Pj=new T(function(){return new T1(0,_Pd);}),_Pc=function(_Pk){return E(_Pj);};return B(_Pc(_));});};return new F(function(){return _Oj(new T1(0,_P8),_w,_);});},_Pl=new T(function(){return eval("__strict(setBounds)");}),_Pm=function(_){var _Pn=__app3(E(_20),E(_93),E(_id),E(_1Z)),_Po=__app2(E(_Pl),E(_1u),E(_1n));return new F(function(){return _P5(_AE,_NO,_);});},_Pp=function(_){return new F(function(){return _Pm(_);});};
var hasteMain = function() {B(A(_Pp, [0]));};window.onload = hasteMain;