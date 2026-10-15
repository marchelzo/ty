#ifndef JITMOD_H_INCLUDED
#define JITMOD_H_INCLUDED

#include "ty.h"

#define JIT_LAYOUT(X) \
        X(VALUE_SIZE, sizeof (Value)) \
        X(OFF_TYPE, offsetof(Value, type)) \
        X(OFF_TAGS, offsetof(Value, tags)) \
        X(OFF_Z, offsetof(Value, z)) \
        X(OFF_REAL, offsetof(Value, real)) \
        X(OFF_BOOL, offsetof(Value, boolean)) \
        X(OFF_PTR, offsetof(Value, ptr)) \
        X(OFF_CLASS, offsetof(Value, class)) \
        X(OFF_OBJECT, offsetof(Value, object)) \
        X(OFF_STR, offsetof(Value, str)) \
        X(OFF_BYTES, offsetof(Value, bytes)) \
        X(OFF_COUNT, offsetof(Value, count)) \
        X(OFF_ITEMS, offsetof(Value, items)) \
        X(OFF_SLOTS, offsetof(TyObject, slots))

#define JIT_TAGS(X) \
        X(ZERO, VALUE_ZERO) \
        X(INT, VALUE_INTEGER) \
        X(FLOAT, VALUE_REAL) \
        X(BOOL, VALUE_BOOLEAN) \
        X(NIL, VALUE_NIL) \
        X(STRING, VALUE_STRING) \
        X(ARRAY, VALUE_ARRAY) \
        X(DICT, VALUE_DICT) \
        X(SET, VALUE_SET) \
        X(HEAP, VALUE_HEAP) \
        X(BLOB, VALUE_BLOB) \
        X(TUPLE, VALUE_TUPLE) \
        X(OBJECT, VALUE_OBJECT) \
        X(PTR, VALUE_PTR) \
        X(REF, VALUE_REF) \
        X(FUNCTION, VALUE_FUNCTION) \
        X(BOUND_FUNCTION, VALUE_BOUND_FUNCTION) \
        X(STAR_FUNCTION, VALUE_STAR_FUNCTION) \
        X(FOREIGN_FUNCTION, VALUE_FOREIGN_FUNCTION) \
        X(JIT_FUNCTION, VALUE_JIT_FUNCTION) \
        X(NATIVE_FUNCTION, VALUE_NATIVE_FUNCTION) \
        X(BUILTIN_FUNCTION, VALUE_BUILTIN_FUNCTION) \
        X(METHOD, VALUE_METHOD) \
        X(BUILTIN_METHOD, VALUE_BUILTIN_METHOD) \
        X(CLASS, VALUE_CLASS) \
        X(GENERATOR, VALUE_GENERATOR) \
        X(GENERATOR_0, VALUE_GENERATOR_0) \
        X(TAG, VALUE_TAG) \
        X(OPERATOR, VALUE_OPERATOR) \
        X(TYPE, VALUE_TYPE) \
        X(REGEX, VALUE_REGEX) \
        X(QUEUE, VALUE_QUEUE) \
        X(SHARED_QUEUE, VALUE_SHARED_QUEUE) \
        X(THREAD, VALUE_THREAD) \
        X(SENTINEL, VALUE_SENTINEL) \
        X(INDEX, VALUE_INDEX) \
        X(NONE, VALUE_NONE) \
        X(UNINITIALIZED, VALUE_UNINITIALIZED) \
        X(NAMESPACE, VALUE_NAMESPACE) \
        X(MODULE, VALUE_MODULE) \
        X(TRACE, VALUE_TRACE) \
        X(BREAK, VALUE_BREAK) \
        X(TOMBSTONE, VALUE_TOMBSTONE) \
        X(FUN_META, VALUE_FUN_META) \
        X(ANY, VALUE_ANY)

#define JIT_LAYOUT_SIG(name, offset) #name ": Int, "
#define JIT_TAG_SIG(name, value) #name ": Int, "
#define JIT_CONTAINER_SIG "{OFF_ITEMS: Int, OFF_COUNT: Int, OFF_CAPACITY: Int}"

#define JIT_BUILTINS(X) \
        X(op_signatures, "_opSignatures", "() -> Dict[String, String]") \
        X(static_value, "_staticValue", "(expr: Any) -> Any") \
        X(interp, "_interp", "(asm: Ptr[Any], cls: Class) -> (Any, Any)") \
        X(serialize, "_serialize", "(asm: Ptr[Any]) -> (Any, Int, Array[Array[Any]], Any)") \
        X(load, "_load", "(bytes: Blob, ninputs: Int, captures: Array[Array[Any]], holes: Array[Any], cls: Class) -> (Any, Any)") \
        X(helpers, "_helpers", "() -> Array[Any]") \
        X(layout, "_layout", "() -> {" JIT_LAYOUT(JIT_LAYOUT_SIG) "Array: " JIT_CONTAINER_SIG ", Blob: " JIT_CONTAINER_SIG ", Dict: " JIT_CONTAINER_SIG "}") \
        X(tags, "_tags", "() -> {" JIT_TAGS(JIT_TAG_SIG) "TAGGED: Int}") \
        X(arch, "_arch", "() -> String") \
        X(new, "_new", "(name: String, params: Array[Int], ret: Int, mode: Int) -> Ptr[Any]") \
        X(params, "_params", "(asm: Ptr[Any]) -> Array[(Int, Int)]") \
        X(reg, "_reg", "(asm: Ptr[Any], cls: Int) -> Int") \
        X(label, "_label", "(asm: Ptr[Any]) -> Int") \
        X(bind, "_bind", "(asm: Ptr[Any], label: Int) -> Any") \
        X(emit, "_emit", "(asm: Ptr[Any], op: Int, dst: Int, args: Array[Array[Any]], meta: Any) -> Any") \
        X(const, "_const", "(asm: Ptr[Any], value: Any, ref: Bool) -> Int") \
        X(vslot, "_vslot", "(asm: Ptr[Any]) -> Int") \
        X(finish, "_finish", "(asm: Ptr[Any], cls: Class) -> (Any, Any)") \
        X(dump, "_dump", "(asm: Ptr[Any], stage: String) -> (Any, Any)") \
        X(ops, "_ops", "() -> Dict[String, Int]") \
        X(sig, "_sig", "(target: Any) -> (Int, Array[Int], Int, Bool, Int)") \
        X(ptr, "_ptr", "(f: Any) -> Ptr[Any]") \
        X(code, "_code", "(f: Any) -> Ptr[Any]") \
        X(name, "_name", "(f: Any) -> String") \
        X(code_size, "_codeSize", "(code: Ptr[Any]) -> Int") \
        X(code_lir, "_codeLir", "(code: Ptr[Any]) -> String") \
        X(code_bytes, "_codeBytes", "(code: Ptr[Any]) -> Blob") \
        X(code_sites, "_codeSites", "(code: Ptr[Any]) -> Array[(Int, Int)]") \
        X(stats, "_stats", "() -> (Int, Int, Int)") \
        X(current_ty, "_currentTy", "() -> Ptr[Any]")

#define JIT_DECL(c, n, s) Value builtin_jit_##c(Ty *ty, int argc, Value *kwargs);
JIT_BUILTINS(JIT_DECL)
#undef JIT_DECL

#endif
