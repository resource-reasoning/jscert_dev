
(function () {
/*
* Tentative redefinitions of InstallFunctions and SetUpLockedPrototype
* These functions make assumptions about lack of redefinition of certain ch15 functions
*/


// Helper function used to install functions on objects.
function InstallFunctions(object, attributes, functions) {
  for (var i = 0; i < functions.length; i+=2) {
    var key = functions[i];
    var f = functions[i + 1];
    f.prototype = undefined;
    var read_only = Boolean(attributes & 1);
    var dont_enum = Boolean(attributes & 2);
    var dont_delete = Boolean(attributes & 4);
    object[key] = f;
    var descriptor = {writable: !read_only,
                      enumerable: !dont_enum,
                      configurable: !dont_delete
                     };
    Object.defineProperty(object, key, descriptor);
  }
}


// Prevents changes to the prototype of a built-in function.
// The "prototype" property of the function object is made non-configurable,
// and the prototype object is made non-extensible.

//as an aside. I've tried to stick as close to the effects of the V8 version
//even when I'm not sure it's necessary for our purposes
function SetUpLockedPrototype(constructor, fields, methods) {
  var prototype = constructor.prototype;
  if (fields) {
    for (var i = 0; i < fields.length; i++) {
      prototype[fields[i]] = undefined;
      Object.defineProperty(prototype, fields[i],
                            {enumerable: false, configurable: false});
    }
  }
  for (var i = 0; i < methods.length; i += 2) {
    var key = methods[i];
    var f = methods[i + 1];
    prototype[key] = f;
    Object.defineProperty(prototype, key, 
                         {writable: false, enumerable: false, configurable: false});
  }
  prototype.prototype = null;
}

var $Array = Array;
var ObjectIsSealed = Object.isSealed;
var ObjectIsFrozen = Object.isFrozen;
var ArrayProtoSlice = Array.prototype.slice.call;
var ArrayProtoShift = Array.prototype.shift.call;
var FunctionProtoApply = Function.prototype.apply.call;
var ObjectGetOwnPropDesc = Object.getOwnPropertyDescriptor;

var InternalArray = function(length) {this.length = length};
InternalArray.prototype = {push: Array.prototype.push, pop: Array.prototype.pop};

function %_CallFunction() {
  var f = arguments[arguments.length - 1];
  delete arguments[arguments.length - 1];
  var args_array = ArrayProtoSlice(arguments);
  var this_arg = ArrayProtoShift(args_array);
  FunctionProtoApply(f, arguments[0], args_array);
}

function MakeTypeError(arg1, arg2) {
  return new TypeError();
}

function %isObserved() {
  return false;
}

function %_IsUndetectableObject() {
  return false;
}

%IS_VAR(x) {
  return x;
}

%_HasCachedArrayIndex() {
  return false;
}

%_FastAsciiArrayJoin(arg1, arg2) {
  return void(0);
}

%StringToNumber(x) {
  return Number(x);
}

%DefaultNumber(x) {
  return Number(x);
}

%_NumberToString(x) {
  return String(x);
}

%DefaultToString(x) {
  return String(x);
}

%ToString(x) {
  return String(x);
}

CHECK_OBJECT_COERCIBLE(arg1, arg2) {
  return;
}

TO_OBJECT_INLINE(x) {
  return ToObject(x);
}

ToObject(x) {
  if(x === null || IS_UNDEFINED(x)) {
    throw new TypeError();
  }
  return Object(x);
}

IS_UNDEFINED(x) {
  return x === void(0);
}

IS_NUMBER(x) {
  return typeof x === "number";
}

IS_STRING(x) {
  return typeof x === "string";
}

IS_BOOLEAN(x) {
  return typeof x === "boolean";
}

IS_ARRAY(x) { // TODO: BROKEN????
  return x instanceof $Array;
}

mod(n, d) {
  var div = n % d;
  if(n < 0) {
    return d + div;
  }
  return div;
}

TO_UINT32(x) {
  var num = TO_NUMBER(x);
  if(num === +0 || num === -0 || num === Infinity || num === -Infinity) {
    return +0;
  }
  var posInt = abs(num) - (abs(num) % 1);
  if(num < 0) {
    posInt = -(round_num);
  }
  return mod(posInt, 4294967296);
}

TO_INTEGER(x) {
  var num = TO_NUMBER(x);
  if(isNaN(num)) {
    return +0;
  }
  if(num === +0 || num === -0 || num === Infinity || num === -Infinity) {
    return num;
  }
  var round_num = abs(num) - (abs(num) % 1);
  if(num < 0) {
    return -(round_num)
  } else {
    return +(round_num)
  }
}

IS_NULL_OR_UNDEFINED(x) {
  return x == null;
}

%PushIfAbsent(list, elem) {
  for(var i = 0; i < list.length; i++) {
    if(list[i] === elem) {
      return false;
    }
  }
  list.push(elem);
  return true;
}

%MoveArrayContents(old_array, array) {
  var len = old_array.length;
  for(var i = 0; i < len; i++) {
    array[i] = old_array[i];
  }
  var j = len;
  while(old_array[j] !== undefined) {
    array[j] = old_array[j];
    j++;
  }
}

%ArrayConcat(arrays) {
  var A = new $Array();
  var n = 0;
  var E;
  while(arrays.length > 0) {
    E = ArrayProtoShift(arrays);
    if(IS_ARRAY(E)) {
      var k = 0;
      while (k < E.length) {
        if(E[k] !== undefined) {
          A[n] = E[k];
        }
        n++;
        k++;
      }
    }
    else {
      A[n] = E;
      n++;
      k++;
    }
  }
  return A;
}

%StringBuilderConcat(elements, length, separator) {
  var ret = "";
  for (var i = 0; i < length; i++) {
    if(elements[i] !== void(0)) {
      ret = ret + separator + elements[i];
    }
  }
  return ret;
}

%StringBuilderJoin(elements, length, separator) {
  var ret = "";
  for (var i = 0; i < length; i++) {
    ret = ret + separator
    if(elements[i] !== void(0)) {
      ret = ret + elements[i];
    }
  }
  return ret;
}

getFunction(name, f, length) {
  var ret_fun = (function() {
    var args_array = ArrayProtoSlice(arguments);
    var this_arg = ArrayProtoShift(args_array);
    FunctionProtoApply(f, this, args_array);
  });
  if(length !== undefined) {
    Object.defineProperty(ret_fun, "length", {value: length, writable: false, enumerable: false, configurable: false});
  }
  return ret_fun;
}

%FinishArrayPrototypeSetup(arg1) {
}

SetUpArray() {
}

})();
