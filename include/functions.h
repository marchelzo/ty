#ifndef FUNCTIONS_H_INCLUDED
#define FUNCTIONS_H_INCLUDED

#include "ty.h"
#include "value.h"
#include "gen/builtin_decls.h"

void TyFunctionsInit(Ty *ty);

Value builtin_regexv(Ty *ty, int argc, Value *kwargs);
Value builtin_regex_escape(Ty *ty, int argc, Value *kwargs);
Value builtin_array(Ty *ty, int argc, Value *kwargs);
Value builtin_dict(Ty *ty, int argc, Value *kwargs);
Value builtin_queue(Ty *ty, int argc, Value *kwargs);
Value builtin_shared_queue(Ty *ty, int argc, Value *kwargs);
Value builtin_work_queue(Ty *ty, int argc, Value *kwargs);

u64 NextThreadId();

#endif
