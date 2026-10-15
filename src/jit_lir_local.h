static void
bc_local_load(BcLir *c, i32 slot)
{
        bc_value_copy(c, c->ops, c->sp++ * sizeof (Value), c->locals, slot * sizeof (Value));
}

static void
bc_local_store(BcLir *c, i32 slot)
{
        bc_value_copy(c, c->locals, slot * sizeof (Value), c->ops, --c->sp * sizeof (Value));
}
