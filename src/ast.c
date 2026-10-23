#include <ctype.h>

#include "ast.h"
#include "panic.h"
#include "scope.h"
#include "compiler.h"

#include "ty.h"

#define E(f) ((AstXO_##f + sizeof (AstXT_##f) + sizeof (u64) - 1) / sizeof (u64))
#define S(f) ((AstSO_##f + sizeof (AstST_##f) + sizeof (u64) - 1) / sizeof (u64))
u8 const AstSlots[256] = {
        [EXPRESSION_INTEGER]              = E(integer),
        [EXPRESSION_STATEMENT]            = E(integer),
        [EXPRESSION_THROW]                = E(integer),
        [EXPRESSION_PLACEHOLDER]          = E(integer),
        [EXPRESSION_ERROR]                = E(integer),
        [EXPRESSION_TYPE]                 = E(escope),
        [EXPRESSION_NIL]                  = E(integer),
        [EXPRESSION_COMPILE_TIME]         = E(escope),
        [EXPRESSION_PREFIX_QUESTION]      = E(escope),
        [EXPRESSION_PREFIX_BANG]          = E(escope),
        [EXPRESSION_PREFIX_MINUS]         = E(escope),
        [EXPRESSION_PREFIX_HASH]          = E(escope),
        [EXPRESSION_PREFIX_AT]            = E(escope),
        [EXPRESSION_PREFIX_INC]           = E(escope),
        [EXPRESSION_PREFIX_DEC]           = E(escope),
        [EXPRESSION_POSTFIX_INC]          = E(escope),
        [EXPRESSION_POSTFIX_DEC]          = E(escope),
        [EXPRESSION_UNARY_OP]             = E(escope),
        [EXPRESSION_ENTER]                = E(escope),
        [EXPRESSION_TYPE_OF]              = E(escope),
        [EXPRESSION_SPREAD]               = E(escope),
        [EXPRESSION_SPLAT]                = E(escope),
        [EXPRESSION_REF_PATTERN]          = E(escope),
        [EXPRESSION_UNSAFE]               = E(escope),
        [EXPRESSION_PACK_UNION]           = E(escope),
        [EXPRESSION_RESOLVED]             = E(escope),
        [EXPRESSION_TEMPLATE_XHOLE]       = E(escope),
        [EXPRESSION_REAL]                 = E(escope),
        [EXPRESSION_SUPER]                = E(escope),
        [EXPRESSION_CAST]                 = E(escope),
        [EXPRESSION_EVAL]                 = E(escope),
        [EXPRESSION_TEMPLATE_HOLE]        = E(hole),
        [EXPRESSION_TEMPLATE_VHOLE]       = E(hole),
        [EXPRESSION_TEMPLATE_THOLE]       = E(hole),
        [EXPRESSION_ARRAY]                = E(compr),
        [EXPRESSION_ARRAY_COMPR]          = E(compr),
        [EXPRESSION_SET]                  = E(compr),
        [EXPRESSION_SET_COMPR]            = E(compr),
        [EXPRESSION_DICT]                 = E(dflt),
        [EXPRESSION_DICT_COMPR]           = E(dflt),
        [EXPRESSION_CONDITIONAL]          = E(_else),
        [EXPRESSION_LANG_LITERAL]         = E(lit),
        [EXPRESSION_WITH]                 = E(with),
        [EXPRESSION_EQ]                   = E(value),
        [EXPRESSION_MAYBE_EQ]             = E(value),
        [EXPRESSION_PLUS_EQ]              = E(value),
        [EXPRESSION_STAR_EQ]              = E(value),
        [EXPRESSION_DIV_EQ]               = E(value),
        [EXPRESSION_MOD_EQ]               = E(value),
        [EXPRESSION_MINUS_EQ]             = E(value),
        [EXPRESSION_AND_EQ]               = E(value),
        [EXPRESSION_OR_EQ]                = E(value),
        [EXPRESSION_XOR_EQ]               = E(value),
        [EXPRESSION_SHL_EQ]               = E(value),
        [EXPRESSION_SHR_EQ]               = E(value),
        [EXPRESSION_LIST]                 = E(tconds),
        [EXPRESSION_TUPLE]                = E(tconds),
        [EXPRESSION_TUPLE_SPEC]           = E(tconds),
        [EXPRESSION_CHOICE_PATTERN]       = E(tconds),
        [EXPRESSION_YIELD]                = E(tconds),
        [EXPRESSION_MODULE]               = E(tconds),
        [EXPRESSION_FUNCTION_TYPE]        = E(not_nil),
        [EXPRESSION_IN]                   = E(not_nil),
        [EXPRESSION_NOT_IN]               = E(not_nil),
        [EXPRESSION_USER_OP]              = E(not_nil),
        [EXPRESSION_BIT_AND]              = E(not_nil),
        [EXPRESSION_BIT_OR]               = E(not_nil),
        [EXPRESSION_XOR]                  = E(not_nil),
        [EXPRESSION_SHL]                  = E(not_nil),
        [EXPRESSION_SHR]                  = E(not_nil),
        [EXPRESSION_DOT_DOT]              = E(not_nil),
        [EXPRESSION_DOT_DOT_DOT]          = E(not_nil),
        [EXPRESSION_VIEW_PATTERN]         = E(not_nil),
        [EXPRESSION_NOT_NIL_VIEW_PATTERN] = E(not_nil),
        [EXPRESSION_PLUS]                 = E(not_nil),
        [EXPRESSION_MINUS]                = E(not_nil),
        [EXPRESSION_STAR]                 = E(not_nil),
        [EXPRESSION_DIV]                  = E(not_nil),
        [EXPRESSION_PERCENT]              = E(not_nil),
        [EXPRESSION_AND]                  = E(not_nil),
        [EXPRESSION_OR]                   = E(not_nil),
        [EXPRESSION_KW_AND]               = E(not_nil),
        [EXPRESSION_WTF]                  = E(not_nil),
        [EXPRESSION_LT]                   = E(not_nil),
        [EXPRESSION_LEQ]                  = E(not_nil),
        [EXPRESSION_GT]                   = E(not_nil),
        [EXPRESSION_GEQ]                  = E(not_nil),
        [EXPRESSION_CMP]                  = E(not_nil),
        [EXPRESSION_DBL_EQ]               = E(not_nil),
        [EXPRESSION_NOT_EQ]               = E(not_nil),
        [EXPRESSION_CHECK_MATCH]          = E(not_nil),
        [EXPRESSION_TYPE_UNION]           = E(not_nil),
        [EXPRESSION_BOOLEAN]              = E(local),
        [EXPRESSION_STRING]               = E(local),
        [EXPRESSION_OPERATOR]             = E(local),
        [EXPRESSION_IDENTIFIER]           = E(local),
        [EXPRESSION_RESOURCE_BINDING]     = E(local),
        [EXPRESSION_MATCH_ANY]            = E(local),
        [EXPRESSION_MATCH_NOT_NIL]        = E(local),
        [EXPRESSION_MATCH_REST]           = E(local),
        [EXPRESSION_PACK]                 = E(local),
        [EXPRESSION_TAG_PATTERN]          = E(local),
        [EXPRESSION_TAG_PATTERN_CALL]     = E(local),
        [EXPRESSION_ALIAS_PATTERN]        = E(local),
        [EXPRESSION_OBJECT_PATTERN]       = E(local),
        [EXPRESSION_IFDEF]                = E(local),
        [EXPRESSION_VALUE]                = E(local),
        [EXPRESSION_MATCH]                = E(local),
        [EXPRESSION_MUST_EQUAL]           = E(local),
        [EXPRESSION_REGEX]                = E(local),
        [EXPRESSION_TEMPLATE]             = E(template),
        [EXPRESSION_SPECIAL_STRING]       = E(expressions),
        [EXPRESSION_DYNAMIC_REGEX]        = E(expressions),
        [EXPRESSION_TAG_APPLICATION]      = E(kws),
        [EXPRESSION_FUNCTION_CALL]        = E(kws),
        [EXPRESSION_SUBSCRIPT]            = E(kws),
        [EXPRESSION_SAFE_SUBSCRIPT]       = E(kws),
        [EXPRESSION_MEMBER_ACCESS]        = E(maybe),
        [EXPRESSION_DYN_MEMBER_ACCESS]    = E(maybe),
        [EXPRESSION_DYN_METHOD_CALL]      = E(maybe),
        [EXPRESSION_METHOD_CALL]          = E(maybe),
        [EXPRESSION_NAMESPACE]            = E(parent),
        [EXPRESSION_SLICE]                = E(slice),
        [STATEMENT_EXPRESSION]            = S(depth),
        [STATEMENT_RETURN]                = S(depth),
        [STATEMENT_GENERATOR_RETURN]      = S(depth),
        [STATEMENT_DEFER]                 = S(depth),
        [STATEMENT_CONTINUE]              = S(depth),
        [STATEMENT_BREAK]                 = S(depth),
        [STATEMENT_NULL]                  = S(depth),
        [STATEMENT_BLOCK]                 = S(statements),
        [STATEMENT_MULTI]                 = S(statements),
        [STATEMENT_CLEANUP]               = S(statements),
        [STATEMENT_DROP]                  = S(drop),
        [STATEMENT_DEFINITION]            = S(retry),
        [STATEMENT_FUNCTION_DEFINITION]   = S(retry),
        [STATEMENT_OPERATOR_DEFINITION]   = S(retry),
        [STATEMENT_MACRO_DEFINITION]      = S(retry),
        [STATEMENT_FUN_MACRO_DEFINITION]  = S(retry),
        [STATEMENT_PATTERN_DEFINITION]    = S(retry),
        [STATEMENT_FOR_LOOP]              = S(each),
        [STATEMENT_EACH_LOOP]             = S(each),
        [STATEMENT_WHILE]                 = S(_while),
        [STATEMENT_WHILE_MATCH]           = S(match),
        [STATEMENT_MATCH]                 = S(match),
        [STATEMENT_IF]                    = S(_if),
        [STATEMENT_TRY]                   = S(try),
        [STATEMENT_TRY_CLEAN]             = S(try),
        [STATEMENT_IMPORT]                = S(import),
        [STATEMENT_USE]                   = S(use),
};
#undef S
#undef E

static u8 const AstViews[256] = {
        [EXPRESSION_ALIAS_PATTERN]        = AstXV_tagged + 1,
        [EXPRESSION_AND]                  = AstXV_op_name + 1,
        [EXPRESSION_AND_EQ]               = AstXV_target + 1,
        [EXPRESSION_ARRAY]                = AstXV_atmp + 1,
        [EXPRESSION_ARRAY_COMPR]          = AstXV_atmp + 1,
        [EXPRESSION_BIT_AND]              = AstXV_op_name + 1,
        [EXPRESSION_BIT_OR]               = AstXV_op_name + 1,
        [EXPRESSION_BOOLEAN]              = AstXV_boolean + 1,
        [EXPRESSION_CAST]                 = AstXV_op_name + 1,
        [EXPRESSION_CHECK_MATCH]          = AstXV_op_name + 1,
        [EXPRESSION_CHOICE_PATTERN]       = AstXV_ltmp + 1,
        [EXPRESSION_CMP]                  = AstXV_op_name + 1,
        [EXPRESSION_COMPILE_TIME]         = AstXV_uop + 1,
        [EXPRESSION_CONDITIONAL]          = AstXV_cond + 1,
        [EXPRESSION_CTX_INFO]             = AstXV_message + 1,
        [EXPRESSION_DBL_EQ]               = AstXV_op_name + 1,
        [EXPRESSION_DICT]                 = AstXV_dtmp + 1,
        [EXPRESSION_DICT_COMPR]           = AstXV_dtmp + 1,
        [EXPRESSION_DIV]                  = AstXV_op_name + 1,
        [EXPRESSION_DIV_EQ]               = AstXV_target + 1,
        [EXPRESSION_DOT_DOT]              = AstXV_op_name + 1,
        [EXPRESSION_DOT_DOT_DOT]          = AstXV_op_name + 1,
        [EXPRESSION_DYNAMIC_REGEX]        = AstXV_lang + 1,
        [EXPRESSION_DYN_MEMBER_ACCESS]    = AstXV_object + 1,
        [EXPRESSION_DYN_METHOD_CALL]      = AstXV_object + 1,
        [EXPRESSION_ENTER]                = AstXV_uop + 1,
        [EXPRESSION_EQ]                   = AstXV_target + 1,
        [EXPRESSION_ERROR]                = AstXV_message + 1,
        [EXPRESSION_EVAL]                 = AstXV_uop + 1,
        [EXPRESSION_FUNCTION]             = AstXV_name + 1,
        [EXPRESSION_FUNCTION_CALL]        = AstXV_function + 1,
        [EXPRESSION_FUNCTION_TYPE]        = AstXV_op_name + 1,
        [EXPRESSION_FUN_MACRO_INVOCATION] = AstXV_function + 1,
        [EXPRESSION_GENERATOR]            = AstXV_name + 1,
        [EXPRESSION_GEQ]                  = AstXV_op_name + 1,
        [EXPRESSION_GT]                   = AstXV_op_name + 1,
        [EXPRESSION_IDENTIFIER]           = AstXV_tagged + 1,
        [EXPRESSION_IFDEF]                = AstXV_tagged + 1,
        [EXPRESSION_IMPLICIT_FUNCTION]    = AstXV_name + 1,
        [EXPRESSION_IN]                   = AstXV_op_name + 1,
        [EXPRESSION_INTEGER]              = AstXV_integer + 1,
        [EXPRESSION_KW_AND]               = AstXV_op_name + 1,
        [EXPRESSION_LANG_LITERAL]         = AstXV_lit + 1,
        [EXPRESSION_LEQ]                  = AstXV_op_name + 1,
        [EXPRESSION_LIST]                 = AstXV_ltmp + 1,
        [EXPRESSION_LT]                   = AstXV_op_name + 1,
        [EXPRESSION_MATCH]                = AstXV_subject + 1,
        [EXPRESSION_MATCH_ANY]            = AstXV_tagged + 1,
        [EXPRESSION_MATCH_NOT_NIL]        = AstXV_tagged + 1,
        [EXPRESSION_MATCH_REST]           = AstXV_tagged + 1,
        [EXPRESSION_MAYBE_EQ]             = AstXV_target + 1,
        [EXPRESSION_MEMBER_ACCESS]        = AstXV_object + 1,
        [EXPRESSION_METHOD_CALL]          = AstXV_object + 1,
        [EXPRESSION_MINUS]                = AstXV_op_name + 1,
        [EXPRESSION_MINUS_EQ]             = AstXV_target + 1,
        [EXPRESSION_MODULE]               = AstXV_tagged + 1,
        [EXPRESSION_MOD_EQ]               = AstXV_target + 1,
        [EXPRESSION_MULTI_FUNCTION]       = AstXV_name + 1,
        [EXPRESSION_MUST_EQUAL]           = AstXV_tagged + 1,
        [EXPRESSION_NAMESPACE]            = AstXV_name + 1,
        [EXPRESSION_NOT_EQ]               = AstXV_op_name + 1,
        [EXPRESSION_NOT_IN]               = AstXV_op_name + 1,
        [EXPRESSION_NOT_NIL_VIEW_PATTERN] = AstXV_op_name + 1,
        [EXPRESSION_OBJECT_PATTERN]       = AstXV_tagged + 1,
        [EXPRESSION_OPERATOR]             = AstXV_op + 1,
        [EXPRESSION_OR]                   = AstXV_op_name + 1,
        [EXPRESSION_OR_EQ]                = AstXV_target + 1,
        [EXPRESSION_PACK]                 = AstXV_tagged + 1,
        [EXPRESSION_PERCENT]              = AstXV_op_name + 1,
        [EXPRESSION_PLUS]                 = AstXV_op_name + 1,
        [EXPRESSION_PLUS_EQ]              = AstXV_target + 1,
        [EXPRESSION_POSTFIX_DEC]          = AstXV_uop + 1,
        [EXPRESSION_POSTFIX_INC]          = AstXV_uop + 1,
        [EXPRESSION_PREFIX_AT]            = AstXV_uop + 1,
        [EXPRESSION_PREFIX_BANG]          = AstXV_uop + 1,
        [EXPRESSION_PREFIX_DEC]           = AstXV_uop + 1,
        [EXPRESSION_PREFIX_HASH]          = AstXV_uop + 1,
        [EXPRESSION_PREFIX_INC]           = AstXV_uop + 1,
        [EXPRESSION_PREFIX_MINUS]         = AstXV_uop + 1,
        [EXPRESSION_PREFIX_QUESTION]      = AstXV_uop + 1,
        [EXPRESSION_REAL]                 = AstXV_real + 1,
        [EXPRESSION_REF_PATTERN]          = AstXV_target + 1,
        [EXPRESSION_REGEX]                = AstXV_regex + 1,
        [EXPRESSION_RESOLVED]             = AstXV_target + 1,
        [EXPRESSION_RESOURCE_BINDING]     = AstXV_tagged + 1,
        [EXPRESSION_SAFE_SUBSCRIPT]       = AstXV_container + 1,
        [EXPRESSION_SELF_ACCESS]          = AstXV_object + 1,
        [EXPRESSION_SET]                  = AstXV_atmp + 1,
        [EXPRESSION_SET_COMPR]            = AstXV_atmp + 1,
        [EXPRESSION_SHL]                  = AstXV_op_name + 1,
        [EXPRESSION_SHL_EQ]               = AstXV_target + 1,
        [EXPRESSION_SHR]                  = AstXV_op_name + 1,
        [EXPRESSION_SHR_EQ]               = AstXV_target + 1,
        [EXPRESSION_SLICE]                = AstXV_slice + 1,
        [EXPRESSION_SPECIAL_STRING]       = AstXV_lang + 1,
        [EXPRESSION_SPLAT]                = AstXV_target + 1,
        [EXPRESSION_SPREAD]               = AstXV_target + 1,
        [EXPRESSION_STAR]                 = AstXV_op_name + 1,
        [EXPRESSION_STAR_EQ]              = AstXV_target + 1,
        [EXPRESSION_STATEMENT]            = AstXV_statement + 1,
        [EXPRESSION_STRING]               = AstXV_string + 1,
        [EXPRESSION_SUBSCRIPT]            = AstXV_container + 1,
        [EXPRESSION_TAG_APPLICATION]      = AstXV_tagged + 1,
        [EXPRESSION_TAG_PATTERN]          = AstXV_tagged + 1,
        [EXPRESSION_TAG_PATTERN_CALL]     = AstXV_function + 1,
        [EXPRESSION_TEMPLATE]             = AstXV_template + 1,
        [EXPRESSION_TEMPLATE_HOLE]        = AstXV_hole + 1,
        [EXPRESSION_TEMPLATE_THOLE]       = AstXV_hole + 1,
        [EXPRESSION_TEMPLATE_VHOLE]       = AstXV_hole + 1,
        [EXPRESSION_TEMPLATE_XHOLE]       = AstXV_hole + 1,
        [EXPRESSION_THROW]                = AstXV_throw + 1,
        [EXPRESSION_TUPLE]                = AstXV_ltmp + 1,
        [EXPRESSION_TYPE]                 = AstXV_tagged + 1,
        [EXPRESSION_TYPE_OF]              = AstXV_uop + 1,
        [EXPRESSION_TYPE_UNION]           = AstXV_ltmp + 1,
        [EXPRESSION_UNARY_OP]             = AstXV_uop + 1,
        [EXPRESSION_UNSAFE]               = AstXV_uop + 1,
        [EXPRESSION_USER_OP]              = AstXV_op_name + 1,
        [EXPRESSION_VALUE]                = AstXV_v + 1,
        [EXPRESSION_VIEW_PATTERN]         = AstXV_op_name + 1,
        [EXPRESSION_WITH]                 = AstXV_with + 1,
        [EXPRESSION_WTF]                  = AstXV_op_name + 1,
        [EXPRESSION_XOR]                  = AstXV_op_name + 1,
        [EXPRESSION_XOR_EQ]               = AstXV_target + 1,
        [EXPRESSION_YIELD]                = AstXV_ltmp + 1,
        [STATEMENT_BLOCK]                 = AstSV_statements + 1,
        [STATEMENT_BREAK]                 = AstSV_expression + 1,
        [STATEMENT_CLASS_DEFINITION]      = AstSV_tag + 1,
        [STATEMENT_CLEANUP]               = AstSV_statements + 1,
        [STATEMENT_CONTINUE]              = AstSV_expression + 1,
        [STATEMENT_DEFER]                 = AstSV_expression + 1,
        [STATEMENT_DEFINITION]            = AstSV_target + 1,
        [STATEMENT_DROP]                  = AstSV_drop + 1,
        [STATEMENT_EACH_LOOP]             = AstSV_each + 1,
        [STATEMENT_EXPORT]                = AstSV_exports + 1,
        [STATEMENT_EXPRESSION]            = AstSV_expression + 1,
        [STATEMENT_FOR_LOOP]              = AstSV_for_loop + 1,
        [STATEMENT_FUNCTION_DEFINITION]   = AstSV_target + 1,
        [STATEMENT_FUN_MACRO_DEFINITION]  = AstSV_target + 1,
        [STATEMENT_GENERATOR_RETURN]      = AstSV_ret + 1,
        [STATEMENT_IF]                    = AstSV__if + 1,
        [STATEMENT_IMPORT]                = AstSV_import + 1,
        [STATEMENT_MACRO_DEFINITION]      = AstSV_target + 1,
        [STATEMENT_MATCH]                 = AstSV_match + 1,
        [STATEMENT_MULTI]                 = AstSV_statements + 1,
        [STATEMENT_OPERATOR_DEFINITION]   = AstSV_target + 1,
        [STATEMENT_PATTERN_DEFINITION]    = AstSV_target + 1,
        [STATEMENT_RETURN]                = AstSV_ret + 1,
        [STATEMENT_TAG_DEFINITION]        = AstSV_tag + 1,
        [STATEMENT_TRY]                   = AstSV_try + 1,
        [STATEMENT_TRY_CLEAN]             = AstSV_try + 1,
        [STATEMENT_TYPE_DEFINITION]       = AstSV_tag + 1,
        [STATEMENT_USE]                   = AstSV_use + 1,
        [STATEMENT_WHILE]                 = AstSV__while + 1,
        [STATEMENT_WHILE_MATCH]           = AstSV_match + 1,
};

u8     AstKidCount[256];
AstKid AstKidTable[256][AST_MAX_KIDS];

static AstKid const ExprKids[] = {
#define K(v, f, how)     { (how), (v), AstXO_##f },
#define KM(v, f, m, how) { (how), (v), AstXO_##f + offsetof(AstXT_##f, m) },
        TY_EXPR_KIDS
#undef KM
#undef K
};

static AstKid const StmtKids[] = {
#define K(v, f, how)     { (how), (v), AstSO_##f },
#define KM(v, f, m, how) { (how), (v), AstSO_##f + offsetof(AstST_##f, m) },
        TY_STMT_KIDS
#undef KM
#undef K
};

inline static bool
is_method_call(int type)
{
        return (type == EXPRESSION_METHOD_CALL)
            || (type == EXPRESSION_DYN_METHOD_CALL);
}

static bool
KidApplies(int type, AstKid k)
{
        if (type > STATEMENT_TYPE_START) {
                return true;
        }

        if (k.view == AstXV_left) {
                return (type == EXPRESSION_KW_AND) ? (k.off == AstXO_left || k.how == AK_PARTS)
                     :                               (k.how != AK_PARTS);
        }

        if (k.view == AstXV_object) {
                return is_method_call(type) || (k.how == AK_EXPR);
        }

        return true;
}

void
AstKidsInit(void)
{
        for (int type = 0; type < 256; ++type) {
                int           view = AstViews[type] - 1;
                AstKid const *kids = (type > STATEMENT_TYPE_START) ? StmtKids : ExprKids;
                usize         n    = (type > STATEMENT_TYPE_START) ? countof(StmtKids) : countof(ExprKids);

                AstKidCount[type] = 0;

                if (view < 0) {
                        continue;
                }

                for (usize i = 0; i < n; ++i) {
                        AstKid k = kids[i];
                        bool dup = false;

                        if (k.view != view || !KidApplies(type, k)) {
                                continue;
                        }

                        for (int j = 0; j < AstKidCount[type]; ++j) {
                                dup |= (AstKidTable[type][j].off == k.off);
                        }

                        if (!dup) {
                                AstKidTable[type][AstKidCount[type]++] = k;
                        }
                }
        }
}

inline static void
EachPart(struct condpart **parts, int n, void (*f)(void **, void *), void *ctx)
{
        for (int i = 0; i < n; ++i) {
                f((void **)&parts[i]->e,      ctx);
                f((void **)&parts[i]->target, ctx);
        }
}

#if defined(TY_SYSMALLOC)
bool
ChunkIsLive(void const *p);

bool
ChunkIsNode(void const *p);

void
ChunkSetNode(void *p);

static int CheckKids = -1;

inline static void
check_kid(Expr const *e, AstKid k, void const *p)
{
        if (CheckKids < 0) {
                CheckKids = (getenv("TY_CHECK_KIDS") != NULL);
        }

        if (CheckKids && p != NULL && ChunkIsLive(p) && !ChunkIsNode(p)) {
                FILE *f = fopen(getenv("TY_CHECK_KIDS"), "a");
                if (f != NULL) {
                        fprintf(f, "BADKID %s off=%u how=%u\n", ExpressionTypeName(e), (unsigned)k.off, (unsigned)k.how);
                        fclose(f);
                }
        }
}
#else
 #define check_kid(e, k, p) ((void)0)
#endif

void
AstEachKid(void *node, void (*f)(void **slot, void *ctx), void *ctx)
{
        Expr *e    = node;
        char *base = (char *)node + AstHdr(e->type);

        for (int i = 0; i < AstKidCount[e->type]; ++i) {
                AstKid k = AstKidTable[e->type][i];
                void  *p = base + k.off;

                if (k.off + sizeof (ExprVec) > AstCap(e) * sizeof (u64) && k.how != AK_EXPR && k.how != AK_STMT) {
                        continue;
                }

                if (k.off + sizeof (Expr *) > AstCap(e) * sizeof (u64)) {
                        continue;
                }

                switch (k.how) {
                case AK_EXPR:
                case AK_STMT:
                        check_kid(e, k, *(void **)p);
                        f(p, ctx);
                        break;

                case AK_EXPRS:
                case AK_STMTS:
                        for (int j = 0; j < ((ExprVec *)p)->count; ++j) {
                                check_kid(e, k, ((ExprVec *)p)->items[j]);
                                f((void **)&((ExprVec *)p)->items[j], ctx);
                        }
                        break;

                case AK_PARTS:
                        EachPart(((condpart_vector *)p)->items, ((condpart_vector *)p)->count, f, ctx);
                        break;

                case AK_COMPR:
                        for (int j = 0; j < ((Comprehension *)p)->count; ++j) {
                                ComprPart *cp = &((Comprehension *)p)->items[j];
                                f((void **)&cp->pattern, ctx);
                                f((void **)&cp->iter,    ctx);
                                f((void **)&cp->_while,  ctx);
                                f((void **)&cp->where,   ctx);
                                EachPart(cp->_if.items, cp->_if.count, f, ctx);
                        }
                        break;
                }
        }
}


void *
AstSlotFault(void const *node, usize off, usize n)
{
        Expr const *e = node;

        panic(
                "AST slot access out of bounds: %s node has %u slots, field at byte %zu (%zu bytes)",
                ExpressionTypeName(e),
                (unsigned)e->cap,
                off,
                n
        );
}

void *
(AstNew)(Ty *ty, int type, u32 slots)
{
        Expr *e = amA0(AstBytes(type, slots));

        e->type = type;
        e->cap  = slots;

#if defined(TY_SYSMALLOC)
        ChunkSetNode(e);
#endif

        return e;
}

void
(AstRelease)(Ty *ty, void *node)
{
        if (node == NULL || (*AstShared(node) & AST_SHARED)) {
                return;
        }

        Release(ty, node, AstBytes(((Expr *)node)->type, AstCap(node)));
}

Expr *
(AstClone)(Ty *ty, Expr const *e, int type)
{
        u32   cap  = AstCap(e);
        u32   want = (type < 0) ? cap : max(cap, AstNeed(type));
        Expr *new  = amA0(AstBytes(e->type, want));

#if defined(TY_SYSMALLOC)
        ChunkSetNode(new);
#endif

        memcpy(new, e, AstBytes(e->type, cap));

        new->cap = want;

        *AstShared((Expr *)e) |= AST_COPIED;
        *AstShared(new)        = AST_COPIED;

        if (type >= 0) {
                new->type = type;
        }

        return new;
}

void
(AstReplace)(Expr *dst, Expr const *src, usize from)
{
        u32   need = min(AstCap(src), AstNeed(src->type));
        u32   cap  = AstCap(dst);
        usize n    = AstBytes(src->type, need);
        usize m    = AstBytes(src->type, cap);
        u8    sh   = *AstShared(dst) | *AstShared(src) | AST_COPIED;

        if (UNLIKELY(need > cap || AstHdr(src->type) != AstHdr(dst->type))) {
                panic(
                        "AstReplace(): %s node (%u slots) cannot hold %s (%u slots)",
                        ExpressionTypeName(dst),
                        cap,
                        ExpressionTypeName(src),
                        need
                );
        }

        memmove((char *)dst + from, (char const *)src + from, n - from);
        memset((char *)dst + n, 0, m - n);

        dst->cap = cap;

        *AstShared(dst)          = sh;
        *AstShared((Expr *)src) |= AST_COPIED;
}

void
(AstZero)(Expr *e)
{
        usize from = offsetof(Expr, has_resources) + 1;

        memset((char *)e + from, 0, AstBytes(e->type, AstCap(e)) - from);
}

#define V(e) ((e) = visit_expression(ty, e, scope, ctxt))
#define VS(s) ((s) = visit_statement(ty, s, scope, ctxt))
#define VP(e) ((e) = visit_pattern(ty, e, scope, ctxt))
#define VT(t) ((t) = visit_type(ty, t, scope, ctxt))
#define VX(e) ((e) = type ? visit_type(ty, e, scope, ctxt) \
                          : visit_expression(ty, e, scope, ctxt))
#define VL(d, t) ((t) = visit_lvalue(ty, t, scope, ctxt, (d)))
#define VL_(t) ((t) = visit_lvalue(ty, t, scope, ctxt, decl))

#define SUB(f, name, ...) do {                           \
        Scope *tmp_scope = scope;                        \
        if (scope != NULL) {                             \
                scope = scope_new(ty, name, scope, f);   \
        }                                                \
        __VA_ARGS__;                                     \
        scope = tmp_scope;                               \
} while (0)

#define E1(e) ((e) = (ctxt->e_pre)(e, scope, ctxt->user))
#define E2(e) ((e) = (ctxt->e_post)(e, scope, ctxt->user))

#define T1(t) ((t) = (ctxt->t_pre)(t, scope, ctxt->user))
#define T2(t) ((t) = (ctxt->t_post)(t, scope, ctxt->user))

#define S1(s) ((s) = (ctxt->s_pre)(s, scope, ctxt->user))
#define S2(s) ((s) = (ctxt->s_post)(s, scope, ctxt->user))

#define P1(p) ((p) = (ctxt->p_pre)(p, scope, ctxt->user))
#define P2(p) ((p) = (ctxt->p_post)(p, scope, ctxt->user))

#define L1(t) ((t) = (ctxt->l_pre)(t, decl, scope, ctxt->user))
#define L2(t) ((t) = (ctxt->l_post)(t, decl, scope, ctxt->user))

static Expr *
id_e(Expr *e, Scope *scope, void *u)
{
        return e;
}

static Stmt *
id_s(Stmt *s, Scope *scope, void *u)
{
        return s;
}

static Expr *
id_l(Expr *t, bool decl, Scope *scope, void *u)
{
        return t;
}

VisitorCtx
visit_identity(Ty *ty)
{
        return (VisitorCtx) {
                id_e, id_e,
                id_e, id_e,
                id_e, id_e,
                id_l, id_l,
                id_s, id_s,
                NULL
        };
}

static void
bind_name(Ty *ty, Scope *scope, char const *name, u32 flags)
{
        if (scope == NULL || name == NULL || s_eq(name, "_")) {
                return;
        }

        Symbol *existing = scope_local_lookup(ty, scope, name);
        if (existing != NULL) {
                existing->flags |= flags;
                return;
        }

        Symbol sym = {
                .i      = -1,
                .symbol = -1,
                .class  = -1,
                .tag    = -1,
                .flags  = flags
        };

        scope_insert_as(ty, scope, &sym, name);
}

static void
bind_scope(Ty *ty, Scope *dst, Scope const *src)
{
        for (usize i = 0; i < src->size; ++i) {
                for (Symbol *sym = src->table[i]; sym != NULL; sym = sym->next) {
                        if (scope_local_lookup(ty, dst, sym->identifier) == NULL) {
                                scope_insert(ty, dst, sym);
                        }
                }
        }
}

static Scope *
visit_namespace(Ty *ty, Scope *scope, Namespace const *ns)
{
        if (scope == NULL || ns == NULL || !ScopeIsModule(scope)) {
                return scope;
        }

        Scope *parent = visit_namespace(ty, scope, ns->next);
        Symbol *sym = scope_local_lookup(ty, parent, ns->id);
        if (SymbolIsNamespace(sym)) {
                return sym->scope;
        }

        Symbol var = {
                .i      = -1,
                .symbol = -1,
                .class  = -1,
                .tag    = -1,
                .flags  = SYM_NAMESPACE,
                .scope  = scope_new(ty, ns->id, parent, false)
        };
        var.scope->flags |= SCOPE_NAMESPACE;
        scope_insert_as(ty, parent, &var, ns->id);

        return var.scope;
}

static void
bind_regex(Ty *ty, Scope *scope, Regex const *re)
{
        if (scope == NULL) {
                return;
        }

        u32 n;
        u32 width;
        PCRE2_SPTR names;
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMECOUNT, &n);
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMEENTRYSIZE, &width);
        pcre2_pattern_info(re->pcre2, PCRE2_INFO_NAMETABLE, &names);

        for (u32 i = 0; i <= re->ncap; ++i) {
                char id[16];
                ty_snprintf(id, sizeof id, "$%u", i);
                for (u32 j = 0; j < n; ++j) {
                        PCRE2_SPTR entry = names + j * width;
                        if (((entry[0] << 8) | entry[1]) == i) {
                                bind_name(ty, scope, (char const *)(entry + 2), 0);
                                goto NextCapture;
                        }
                }
                bind_name(ty, scope, sclonea(ty, id), 0);
NextCapture:
                ;
        }
}

static void
visit_params(Ty *ty, ExprVec *params, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(*params); ++i) {
                Expr *param = v__(*params, i);
                bind_name(ty, scope, xF(param, identifier), SYM_TYPE_VAR);
                VT(v__(*params, i));
        }
}

static void
visit_function(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(xF(e, decorators)); ++i) {
                V(v__(xF(e, decorators), i));
        }

        SUB(true, xF(e, name) == NULL ? "(anon)" : xF(e, name),
                bind_name(ty, scope, xF(e, name), SYM_FUNCTION | SYM_CONST);
                visit_params(ty, &xF(e, type_params), scope, ctxt);
                for (usize i = 0; i < vN(xF(e, params)); ++i) {
                        V(v__(xF(e, dflts), i));
                        bind_name(ty, scope, v__(xF(e, params), i), 0);
                }
                for (usize i = 0; i < vN(xF(e, constraints)); ++i) {
                        VT(v__(xF(e, constraints), i));
                }
                if (e->type != EXPRESSION_MULTI_FUNCTION) {
                        VT(xF(e, return_type));
                        for (usize i = 0; i < vN(xF(e, type_bounds)); ++i) {
                                VT(v_(xF(e, type_bounds), i)->var);
                                VT(v_(xF(e, type_bounds), i)->bound);
                        }
                }
                for (usize i = 0; i < vN(xF(e, functions)); ++i) {
                        V(v__(xF(e, functions), i));
                }
                VS(xF(e, body));
        );
}

static void
bind_aliases(Ty *ty, MethodAliasVec const *aliases, Scope *scope, bool s, u32 flags)
{
        for (usize i = 0; i < vN(*aliases); ++i) {
                MethodAlias const *a = v_(*aliases, i);
                if (a->s == s) {
                        bind_name(ty, scope, a->name, SYM_MEMBER | flags);
                }
        }
}

static void
bind_members(Ty *ty, ExprVec const *members, Scope *scope, u32 flags)
{
        for (usize i = 0; i < vN(*members); ++i) {
                Expr *m = v__(*members, i);
                char const *name;
                if (m->type == EXPRESSION_EQ) {
                        m = xF(m, target);
                }
                switch (m->type) {
                case EXPRESSION_IDENTIFIER:
                        name = xF(m, identifier);
                        break;
                case EXPRESSION_FUNCTION:
                case EXPRESSION_IMPLICIT_FUNCTION:
                case EXPRESSION_MULTI_FUNCTION:
                case EXPRESSION_GENERATOR:
                        name = xF(m, name);
                        break;
                default:
                        continue;
                }
                bind_name(ty, scope, name, SYM_MEMBER | flags);
        }
}

static void
visit_members(Ty *ty, ExprVec *members, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(*members); ++i) {
                Expr **m = v_(*members, i);
                switch ((*m)->type) {
                case EXPRESSION_IDENTIFIER:
                        VL(true, *m);
                        break;
                case EXPRESSION_EQ:
                        V(xF((*m), value));
                        VL(true, xF((*m), target));
                        break;
                default:
                        V(*m);
                        break;
                }
        }
}

static void
visit_class(Ty *ty, ClassDefinition *cd, Scope *scope, VisitorCtx *ctxt)
{
        SUB(false, cd->name,
                visit_params(ty, &cd->type_params, scope, ctxt);
                VT(cd->super);
                for (usize i = 0; i < vN(cd->traits); ++i) {
                        VT(v__(cd->traits, i));
                }

                bind_members(ty, &cd->s_fields, scope, SYM_STATIC);
                bind_members(ty, &cd->s_methods, scope, SYM_STATIC | SYM_FUNCTION);
                bind_members(ty, &cd->s_getters, scope, SYM_STATIC | SYM_PROPERTY);
                bind_members(ty, &cd->s_setters, scope, SYM_STATIC | SYM_PROPERTY);
                bind_aliases(ty, &cd->aliases, scope, true, SYM_STATIC | SYM_FUNCTION);
                visit_members(ty, &cd->s_fields, scope, ctxt);

                SUB(false, "(static methods)",
                        bind_name(ty, scope, "self", 0);
                        visit_members(ty, &cd->s_methods, scope, ctxt);
                        visit_members(ty, &cd->s_getters, scope, ctxt);
                        visit_members(ty, &cd->s_setters, scope, ctxt);
                );

                SUB(false, "(instance)",
                        bind_members(ty, &cd->fields, scope, 0);
                        bind_members(ty, &cd->methods, scope, SYM_FUNCTION);
                        bind_members(ty, &cd->getters, scope, SYM_PROPERTY);
                        bind_members(ty, &cd->setters, scope, SYM_PROPERTY);
                        bind_aliases(ty, &cd->aliases, scope, false, SYM_FUNCTION);
                        visit_members(ty, &cd->fields, scope, ctxt);
                        bind_name(ty, scope, "self", 0);
                        visit_members(ty, &cd->methods, scope, ctxt);
                        visit_members(ty, &cd->getters, scope, ctxt);
                        visit_members(ty, &cd->setters, scope, ctxt);
                );
        );
}

static void
visit_part(Ty *ty, struct condpart *p, Scope *scope, VisitorCtx *ctxt)
{
        V(p->e);
        if (p->def) {
                VP(p->target);
        } else {
                VL(false, p->target);
        }
}

static Scope *
visit_comprehension(Ty *ty, Comprehension *parts, Scope *scope, VisitorCtx *ctxt)
{
        for (usize i = 0; i < vN(*parts); ++i) {
                ComprPart *part = v_(*parts, i);
                V(part->iter);
                if (scope != NULL) {
                        scope = scope_new(ty, "(comprehension)", scope, false);
                }
                VL(true, part->pattern);
                VS(part->where);
                V(part->_while);
                for (usize j = 0; j < vN(part->_if); ++j) {
                        visit_part(ty, v__(part->_if, j), scope, ctxt);
                }
        }

        return scope;
}

static void
visit_statements(Ty *ty, StmtVec *stmts, Scope *scope, VisitorCtx *ctxt)
{
        usize end = 0;
        bool top = ScopeIsModule(scope) || ScopeIsNamespace(scope);

        for (usize i = 0; i < vN(*stmts); ++i) {
                for (end = max(end, i); end < vN(*stmts); ++end) {
                        Stmt *s = v__(*stmts, end);
                        Scope *bound = visit_namespace(ty, scope, s->ns);
                        switch (s->type) {
                        case STATEMENT_FUNCTION_DEFINITION:
                        case STATEMENT_OPERATOR_DEFINITION:
                        case STATEMENT_MACRO_DEFINITION:
                        case STATEMENT_FUN_MACRO_DEFINITION:
                        case STATEMENT_PATTERN_DEFINITION:
                                bind_name(ty, bound, xF(sF(s, target), identifier), SYM_FUNCTION | SYM_CONST);
                                break;
                        case STATEMENT_CLASS_DEFINITION:
                        case STATEMENT_TAG_DEFINITION:
                        case STATEMENT_TYPE_DEFINITION:
                                if (top) {
                                        bind_name(ty, bound, sF(s, class).name, SYM_CONST);
                                        break;
                                }
                                goto Visit;
                        case STATEMENT_DEFINITION:
                                if (top) {
                                        VisitorCtx decls = visit_identity(ty);
                                        (void)visit_lvalue(ty, sF(s, target), bound, &decls, true);
                                        break;
                                }
                        default:
                                if (!top) {
                                        goto Visit;
                                }
                                break;
                        }
                }
Visit:
                VS(v__(*stmts, i));
        }
}

Stmt *
visit_statement(Ty *ty, Stmt *s, Scope *scope, VisitorCtx *ctxt)
{
        if (s == NULL) {
                return NULL;
        }

        if (IsExpr(s)) {
                return (Stmt *)visit_expression(ty, (Expr *)s, scope, ctxt);
        }

        scope = visit_namespace(ty, scope, s->ns);
        S1(s);

        switch (s->type) {
        case STATEMENT_RETURN:
        case STATEMENT_GENERATOR_RETURN:
                V(sF(s, ret));
                break;
        case STATEMENT_MULTI:
                visit_statements(ty, &sF(s, statements), scope, ctxt);
                break;
        case STATEMENT_BLOCK:
                SUB(false, "(block)",
                        visit_statements(ty, &sF(s, statements), scope, ctxt);
                );
                break;
        case STATEMENT_EXPRESSION:
        case STATEMENT_DEFER:
        case STATEMENT_BREAK:
                V(sF(s, expression));
                break;
        case STATEMENT_WHILE:
                SUB(false, "(while)",
                        for (usize i = 0; i < vN(sF(s, _while).parts); ++i) {
                                visit_part(ty, v__(sF(s, _while).parts, i), scope, ctxt);
                        }
                        VS(sF(s, _while).block);
                );
                break;
        case STATEMENT_IF:
                if (sF(s, _if).neg) {
                        VS(sF(s, _if).then);
                        for (usize i = 0; i < vN(sF(s, _if).parts); ++i) {
                                visit_part(ty, v__(sF(s, _if).parts, i), scope, ctxt);
                        }
                        SUB(false, "(if-not)", VS(sF(s, _if)._else));
                } else {
                        SUB(false, "(if)",
                                for (usize i = 0; i < vN(sF(s, _if).parts); ++i) {
                                        visit_part(ty, v__(sF(s, _if).parts, i), scope, ctxt);
                                }
                                VS(sF(s, _if).then);
                        );
                        SUB(false, "(else)", VS(sF(s, _if)._else));
                }
                break;
        case STATEMENT_WHILE_MATCH:
        case STATEMENT_MATCH:
                V(sF(s, match).e);
                for (int i = 0; i < sF(s, match).patterns.count; ++i) {
                        SUB(false, "(match)",
                                VP(sF(s, match).patterns.items[i]);
                                VS(sF(s, match).statements.items[i]);
                        );
                }
                break;
        case STATEMENT_TRY:
        {
                VS(sF(s, try).s);

                for (int i = 0; i < sF(s, try).patterns.count; ++i) {
                        SUB(false, "(catch)",
                                VP(sF(s, try).patterns.items[i]);
                                VS(sF(s, try).handlers.items[i]);
                        );
                }

                VS(sF(s, try).finally);

                break;

        }
        case STATEMENT_EACH_LOOP:
                V(sF(s, each).array);
                SUB(false, "(each)",
                        VL(true, sF(s, each).target);
                        V(sF(s, each)._if);
                        V(sF(s, each)._while);
                        VS(sF(s, each).body);
                );
                break;
        case STATEMENT_FOR_LOOP:
                SUB(false, "(for)",
                        VS(sF(s, for_loop).init);
                        V(sF(s, for_loop).cond);
                        V(sF(s, for_loop).next);
                        SUB(false, "(for-body)", VS(sF(s, for_loop).body));
                );
                break;
        case STATEMENT_DEFINITION:
                V(sF(s, value));
                VL(true, sF(s, target));
                if (sF(s, cnst) && sF(s, target)->type == EXPRESSION_IDENTIFIER) {
                        bind_name(ty, scope, xF(sF(s, target), identifier), SYM_CONST);
                }
                break;
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
        case STATEMENT_PATTERN_DEFINITION:
                VL(true, sF(s, target));
                V(sF(s, value));
                break;
        case STATEMENT_CLASS_DEFINITION:
        case STATEMENT_TAG_DEFINITION:
                bind_name(ty, scope, sF(s, class).name, SYM_CONST);
                visit_class(ty, &sF(s, class), scope, ctxt);
                break;
        case STATEMENT_TYPE_DEFINITION:
                bind_name(ty, scope, sF(s, class).name, SYM_TYPE_ALIAS | SYM_CONST);
                SUB(false, sF(s, class).name,
                        visit_params(ty, &sF(s, class).type_params, scope, ctxt);
                        VT(sF(s, class).type);
                );
                break;
        case STATEMENT_IMPORT:
                bind_name(ty, scope, sF(s, import).as, SYM_CONST);
                if (!sF(s, import).hiding) {
                        for (usize i = 0; i < vN(sF(s, import).aliases); ++i) {
                                bind_name(ty, scope, v__(sF(s, import).aliases, i), SYM_CONST);
                        }
                }
                break;
        case STATEMENT_USE:
                if (vN(sF(s, use).names) == 0 && vN(sF(s, use).name) > 0) {
                        bind_name(ty, scope, v_L(sF(s, use).name), SYM_CONST);
                }
                for (usize i = 0; i < vN(sF(s, use).names); ++i) {
                        bind_name(ty, scope, v__(sF(s, use).names, i), SYM_CONST);
                }
                break;
        }

        return S2(s);
}

Expr *
visit_pattern(Ty *ty, Expr *p, Scope *scope, VisitorCtx *ctxt)
{
        if (p == NULL) {
                return NULL;
        }

        P1(p);

        switch (p->type) {
        case EXPRESSION_IDENTIFIER:
                if (xF(p, module) != NULL) {
                        V(p);
                        break;
                }
                if (isupper((unsigned char)xF(p, identifier)[0])) {
                        for (Scope *s = scope; s != NULL; s = s->parent) {
                                Symbol *sym = scope_local_lookup(ty, s, xF(p, identifier));
                                if (sym == NULL) {
                                        continue;
                                }
                                if (!SymbolIsConst(sym)) {
                                        break;
                                }
                                V(p);
                                return P2(p);
                        }
                }
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
                bind_name(ty, scope, xF(p, identifier), 0);
                VT(xF(p, constraint));
                break;

        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_ALIAS_PATTERN:
                bind_name(ty, scope, xF(p, identifier), 0);
                VT(xF(p, constraint));
                VP(xF(p, tagged));
                break;

        case EXPRESSION_SPREAD:
                VP(xF(p, value));
                break;

        case EXPRESSION_REF_PATTERN:
                VL(false, xF(p, target));
                break;

        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                V(xF(p, left));
                VP(xF(p, right));
                break;

        case EXPRESSION_CHECK_MATCH:
                VP(xF(p, left));
                V(xF(p, right));
                break;

        case EXPRESSION_KW_AND:
                VP(xF(p, left));
                for (usize i = 0; i < vN(xF(p, p_cond)); ++i) {
                        visit_part(ty, v__(xF(p, p_cond), i), scope, ctxt);
                }
                break;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < vN(xF(p, elements)); ++i) {
                        VP(v__(xF(p, elements), i));
                }
                break;

        case EXPRESSION_DICT:
                V(xF(p, dflt));
                for (usize i = 0; i < vN(xF(p, keys)); ++i) {
                        V(v__(xF(p, keys), i));
                        VP(v__(xF(p, values), i));
                }
                break;

        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (usize i = 0; i < vN(xF(p, es)); ++i) {
                        VP(v__(xF(p, es), i));
                }
                break;

        case EXPRESSION_CHOICE_PATTERN:
        {
                Scope *shared = NULL;
                if (scope != NULL) {
                        shared = scope_new(ty, "(choices)", scope, false);
                }
                for (usize i = 0; i < vN(xF(p, es)); ++i) {
                        SUB(false, "(choice)",
                                VP(v__(xF(p, es), i));
                                if (shared != NULL) {
                                        bind_scope(ty, shared, scope);
                                }
                        );
                }
                if (shared != NULL) {
                        bind_scope(ty, scope, shared);
                }
                break;
        }

        case EXPRESSION_REGEX:
                bind_regex(ty, scope, xF(p, regex));
                V(p);
                break;

        case EXPRESSION_FUNCTION_CALL:
                V(xF(p, function));
                goto Arguments;

        case EXPRESSION_TAG_PATTERN_CALL:
                VP(xF(p, function));
Arguments:
                for (usize i = 0; i < vN(xF(p, args)); ++i) {
                        VP(v__(xF(p, args), i));
                }
                for (usize i = 0; i < vN(xF(p, kwargs)); ++i) {
                        VP(v__(xF(p, kwargs), i));
                }
                break;

        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_OBJECT_PATTERN:
                VP(xF(p, tagged));
                break;

        case EXPRESSION_METHOD_CALL:
                V(xF(p, object));
                for (usize i = 0; i < vN(xF(p, method_args)); ++i) {
                        VP(v__(xF(p, method_args), i));
                }
                for (usize i = 0; i < vN(xF(p, method_kwargs)); ++i) {
                        VP(v__(xF(p, method_kwargs), i));
                }
                break;

        default:
                V(p);
                break;
        }

        return P2(p);
}

Expr *
visit_lvalue(Ty *ty, Expr *t, Scope *scope, VisitorCtx *ctxt, bool decl)
{
        if (t == NULL) {
                return NULL;
        }

        L1(t);

        switch (t->type) {
        case EXPRESSION_TAG_PATTERN:
                VL_(xF(t, tagged));
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
                if (decl) {
                        bind_name(ty, scope, xF(t, identifier), 0);
                }
                VT(xF(t, constraint));
                break;

        case EXPRESSION_SPREAD:
                VL_(xF(t, value));
                break;

        case EXPRESSION_REF_PATTERN:
                VL(false, xF(t, target));
                break;

        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                V(xF(t, left));
                VL_(xF(t, right));
                break;

        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_OBJECT_PATTERN:
                VL_(xF(t, tagged));
                break;

        case EXPRESSION_FUNCTION_CALL:
                V(xF(t, function));
                goto Arguments;

        case EXPRESSION_TAG_PATTERN_CALL:
                VL_(xF(t, function));
Arguments:
                for (usize i = 0; i < vN(xF(t, args)); ++i) {
                        VL_(v__(xF(t, args), i));
                }
                for (usize i = 0; i < vN(xF(t, kwargs)); ++i) {
                        VL_(v__(xF(t, kwargs), i));
                }
                break;

        case EXPRESSION_METHOD_CALL:
                V(xF(t, object));
                for (usize i = 0; i < vN(xF(t, method_args)); ++i) {
                        VL_(v__(xF(t, method_args), i));
                }
                for (usize i = 0; i < vN(xF(t, method_kwargs)); ++i) {
                        VL_(v__(xF(t, method_kwargs), i));
                }
                break;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < xF(t, elements).count; ++i) {
                        VL_(v__(xF(t, elements), i));
                }
                break;

        case EXPRESSION_DICT:
                V(xF(t, dflt));
                for (int i = 0; i < xF(t, keys).count; ++i) {
                        V(xF(t, keys).items[i]);
                        VL_(xF(t, values).items[i]);
                }
                break;

        case EXPRESSION_SUBSCRIPT:
        case EXPRESSION_SAFE_SUBSCRIPT:
                V(xF(t, container));
                V(xF(t, subscript));
                break;

        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                V(xF(t, object));
                break;

        case EXPRESSION_DYN_MEMBER_ACCESS:
                V(xF(t, object));
                V(xF(t, member));
                break;

        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
                for (int i = 0; i < xF(t, es).count; ++i) {
                        VL_(xF(t, es).items[i]);
                }
                break;

        default:
                V(t);
        }

        return L2(t);
}

static void
visit_children(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt, bool type)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_PACK:
                VT(xF(e, constraint));
                break;

        case EXPRESSION_COMPILE_TIME:
                VX(xF(e, operand));
                break;

        case EXPRESSION_LANG_LITERAL:
                V(xF(e, lit).lang);
                break;

        case EXPRESSION_SPECIAL_STRING:
                V(xF(e, lang));
                for (usize i = 0; i < vN(xF(e, fmts)); ++i) {
                        V(v__(xF(e, fmts), i));
                }
                for (usize i = 0; i < vN(xF(e, fmtfs)); ++i) {
                        V(v__(xF(e, fmtfs), i));
                }
        case EXPRESSION_DYNAMIC_REGEX:
                for (int i = 0; i < xF(e, expressions).count; ++i) {
                        V(xF(e, expressions).items[i]);
                }
                break;

        case EXPRESSION_TAG:
                break;

        case EXPRESSION_TAG_APPLICATION:
                VX(xF(e, tagged));
                break;

        case EXPRESSION_MATCH:
                VX(xF(e, subject));
                for (int i = 0; i < xF(e, patterns).count; ++i) {
                        SUB(false, "(match)",
                                VP(xF(e, patterns).items[i]);
                                VX(xF(e, thens).items[i]);
                        );
                }
                break;

        case EXPRESSION_USER_OP:
                VX(xF(e, sc));
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
        case EXPRESSION_WTF:
        case EXPRESSION_CHECK_MATCH:
        case EXPRESSION_LT:
        case EXPRESSION_LEQ:
        case EXPRESSION_GT:
        case EXPRESSION_GEQ:
        case EXPRESSION_CMP:
        case EXPRESSION_DBL_EQ:
        case EXPRESSION_NOT_EQ:
        case EXPRESSION_DOT_DOT:
        case EXPRESSION_DOT_DOT_DOT:
        case EXPRESSION_BIT_OR:
        case EXPRESSION_BIT_AND:
        case EXPRESSION_XOR:
        case EXPRESSION_SHR:
        case EXPRESSION_SHL:
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
                VX(xF(e, left));
                VX(xF(e, right));
                break;

        case EXPRESSION_AND:
        case EXPRESSION_OR:
                VX(xF(e, left));
                SUB(false, "(short-circuit)", VX(xF(e, right)));
                break;

        case EXPRESSION_KW_AND:
                VX(xF(e, left));
                for (int i = 0; i < vN(xF(e, p_cond)); ++i) {
                        visit_part(ty, v__(xF(e, p_cond), i), scope, ctxt);
                }
                break;

        case EXPRESSION_DEFINED:
        case EXPRESSION_IFDEF:
                break;

        case EXPRESSION_EVAL:
        case EXPRESSION_UNARY_OP:
        case EXPRESSION_UNSAFE:
        case EXPRESSION_PREFIX_HASH:
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
        case EXPRESSION_PREFIX_MINUS:
        case EXPRESSION_PREFIX_AT:
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
        case EXPRESSION_ENTER:
                VX(xF(e, operand));
                break;

        case EXPRESSION_TYPE_OF:
                V(xF(e, operand));
                break;

        case EXPRESSION_FUNCTION_TYPE:
                VT(xF(e, left));
                VT(xF(e, right));
                break;

        case EXPRESSION_TYPE:
                VT(xF(e, constraint));
                break;

        case EXPRESSION_CAST:
                VX(xF(e, left));
                VT(xF(e, right));
                break;

        case EXPRESSION_CONDITIONAL:
                SUB(false, "(then)",
                        VX(xF(e, cond));
                        VX(xF(e, then));
                );
                SUB(false, "(else)", VX(xF(e, _else)));
                break;

        case EXPRESSION_STATEMENT:
                VS(xF(e, statement));
                break;

        case EXPRESSION_TEMPLATE:
                for (usize i = 0; i < vN(xF(e, template).exprs); ++i) {
                        V(v__(xF(e, template).exprs, i));
                }
                for (usize i = 0; i < vN(xF(e, template).holes); ++i) {
                        V(v__(xF(e, template).holes, i));
                }
                for (usize i = 0; i < vN(xF(e, template).stmts); ++i) {
                        VS(v__(xF(e, template).stmts, i));
                }
                break;

        case EXPRESSION_FUNCTION_CALL:
                VX(xF(e, function));
                for (usize i = 0; i < vN(xF(e, args)); ++i) {
                        VX(v__(xF(e, args), i));
                }
                for (usize i = 0;  i < vN(xF(e, fconds)); ++i) {
                        VX(v__(xF(e, fconds), i));
                }
                for (usize i = 0; i < vN(xF(e, kwargs)); ++i) {
                        VX(v__(xF(e, kwargs), i));
                }
                for (usize i = 0; i < vN(xF(e, fkwconds)); ++i) {
                        VX(v__(xF(e, fkwconds), i));
                }
                break;

        case EXPRESSION_SUBSCRIPT:
        case EXPRESSION_SAFE_SUBSCRIPT:
                VX(xF(e, container));
                VX(xF(e, subscript));
                break;

        case EXPRESSION_SLICE:
                VX(xF(e, slice).e);
                VX(xF(e, slice).i);
                VX(xF(e, slice).j);
                VX(xF(e, slice).k);
                break;

        case EXPRESSION_DYN_MEMBER_ACCESS:
                VX(xF(e, member));
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                VX(xF(e, object));
                break;

        case EXPRESSION_DYN_METHOD_CALL:
                VX(xF(e, method));
        case EXPRESSION_METHOD_CALL:
                VX(xF(e, object));
                for (usize i = 0; i < xF(e, method_args).count; ++i) {
                        VX(xF(e, method_args).items[i]);
                }
                for (usize i = 0; i < xF(e, mconds).count; ++i) {
                        VX(xF(e, mconds).items[i]);
                }
                for (usize i = 0; i < xF(e, method_kwargs).count; ++i) {
                        VX(xF(e, method_kwargs).items[i]);
                }
                break;

        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MINUS_EQ:
        case EXPRESSION_MOD_EQ:
        case EXPRESSION_AND_EQ:
        case EXPRESSION_OR_EQ:
        case EXPRESSION_XOR_EQ:
        case EXPRESSION_SHL_EQ:
        case EXPRESSION_SHR_EQ:
                VX(xF(e, value));
                VL(false, xF(e, target));
                break;

        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_FUNCTION:
                visit_function(ty, e, scope, ctxt);
                break;

        case EXPRESSION_WITH:
                SUB(false, "(with)",
                        VS(xF(e, with).block);
                );
                for (usize i = 0; i < vN(xF(e, with).defs); ++i) {
                        v__(xF(e, with).defs, i) = v__(sF(xF(e, with).block, statements), i);
                }
                break;

        case EXPRESSION_THROW:
                VX(xF(e, throw));
                break;

        case EXPRESSION_YIELD:
                for (int i = 0; i < xF(e, es).count; ++i) {
                        VX(xF(e, es).items[i]);
                }
                break;

        case EXPRESSION_ARRAY:
        case EXPRESSION_SET:
                for (usize i = 0; i < xF(e, elements).count; ++i) {
                        SUB(false, "(array item)",
                                VX(xF(e, aconds).items[i]);
                                VX(xF(e, elements).items[i]);
                        );
                }
                break;

        case EXPRESSION_ARRAY_COMPR:
        case EXPRESSION_SET_COMPR:
        {
                Scope *outer = scope;
                scope = visit_comprehension(ty, &xF(e, compr), scope, ctxt);
                for (usize i = 0; i < xF(e, elements).count; ++i) {
                        VX(xF(e, elements).items[i]);
                        VX(xF(e, aconds).items[i]);
                }
                scope = outer;
                break;
        }

        case EXPRESSION_DICT:
                VX(xF(e, dflt));
                for (usize i = 0; i < xF(e, keys).count; ++i) {
                        VX(xF(e, keys).items[i]);
                        VX(xF(e, values).items[i]);
                }
                break;

        case EXPRESSION_DICT_COMPR:
        {
                VX(xF(e, dflt));
                Scope *outer = scope;
                scope = visit_comprehension(ty, &xF(e, dcompr), scope, ctxt);
                for (usize i = 0; i < vN(xF(e, keys)); ++i) {
                        VX(v__(xF(e, keys), i));
                        VX(v__(xF(e, values), i));
                }
                scope = outer;
                break;
        }

        case EXPRESSION_TYPE_UNION:
                for (int i = 0; i < xF(e, es).count; ++i) {
                        VT(xF(e, es).items[i]);
                }
                break;

        case EXPRESSION_LIST:
                for (int i = 0; i < xF(e, es).count; ++i) {
                        VX(xF(e, es).items[i]);
                }
                break;

        case EXPRESSION_TUPLE:
                for (int i = 0; i < xF(e, es).count; ++i) {
                        VX(xF(e, es).items[i]);
                        VX(xF(e, tconds).items[i]);
                }
                break;

        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                VX(xF(e, value));
                break;

        case EXPRESSION_MACRO_INVOCATION:
                break;

        }
}

Expr *
visit_expression(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt)
{
        if (e == NULL) {
                return NULL;
        }

        if (IsStmt(e)) {
                return (Expr *)visit_statement(ty, (Stmt *)e, scope, ctxt);
        }

        E1(e);
        visit_children(ty, e, scope, ctxt, false);
        return E2(e);
}

Expr *
visit_type(Ty *ty, Expr *e, Scope *scope, VisitorCtx *ctxt)
{
        if (e == NULL) {
                return NULL;
        }

        T1(e);
        visit_children(ty, e, scope, ctxt, true);
        return T2(e);
}

/* vim: set sw=8 sts=8 expandtab: */
