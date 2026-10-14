#ifndef JITMOD_H_INCLUDED
#define JITMOD_H_INCLUDED

#include "ty.h"

#define JIT_BUILTINS(X) \
        X(op_signatures, "_opSignatures", "() -> Dict[String, String]") \
        X(static_value, "_staticValue", "(expr: Any) -> Any") \
        X(interp, "_interp", "(asm: Ptr[Any], cls: Class) -> (Any, Any)") \
        X(serialize, "_serialize", "(asm: Ptr[Any]) -> (Any, Int, Array[Array[Any]], Any)") \
        X(load, "_load", "(bytes: Blob, ninputs: Int, captures: Array[Array[Any]], holes: Array[Any], cls: Class) -> (Any, Any)") \
        X(helpers, "_helpers", "() -> Array[Any]") \
        X(layout, "_layout", "() -> Dict[String, Int]") \
        X(tags, "_tags", "() -> Dict[String, Int]") \
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
