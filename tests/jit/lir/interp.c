#include "scalar.h"

static bool
interpret(Ty *ty, Lir *L, LirScalar const *args, u32 n, LirScalar *out, LirError *err)
{
        return lir_interpret(ty, L, args, n, out, err);
}

int
main(void)
{
        scalar_suite(interpret, false);
        return report("LIR interpreter");
}
