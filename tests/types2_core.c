#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "types2_core.h"

static int failures;

#define CHECK(condition) do {                                             \
        if (!(condition)) {                                               \
                fprintf(stderr, "%s:%d: check failed: %s\n",             \
                        __FILE__, __LINE__, #condition);                   \
                failures += 1;                                            \
        }                                                                 \
} while (0)

static void
check_string(T2Universe *universe, T2Type type, char const *expected)
{
        char *actual = t2_type_string(universe, type);
        CHECK(actual != NULL);
        if (actual != NULL) {
                CHECK(strcmp(actual, expected) == 0);
        }
        free(actual);
}

static void
check_snapshot(T2Universe *universe, T2Type type)
{
        T2TypeSnapshot *snapshot = t2_type_snapshot_new(universe, type);
        CHECK(snapshot != NULL);
        if (snapshot != NULL) {
                CHECK(t2_type_snapshot_node_count(snapshot) != 0);
                CHECK(t2_type_snapshot_import(universe, snapshot) == type);
        }
        t2_type_snapshot_free(snapshot);
}

typedef struct predicate_test_context {
        T2Universe *universe;
        size_t calls;
} PredicateTestContext;

static T2Relation
resolve_test_predicate(
        void *context,
        T2Solver *solver,
        T2Predicate const *predicate
)
{
        PredicateTestContext *test = context;
        test->calls += 1;

        T2Type left = t2_solver_zonk(
                solver,
                predicate->subtype,
                T2_PREFER_LOWER_BOUND
        );
        T2Type right = t2_solver_zonk(
                solver,
                predicate->operand,
                T2_PREFER_LOWER_BOUND
        );
        T2Type result = t2_solver_zonk(
                solver,
                predicate->supertype,
                T2_PREFER_LOWER_BOUND
        );
        if (
                left == T2_TYPE_INVALID
             || right == T2_TYPE_INVALID
             || result == T2_TYPE_INVALID
        ) return T2_RELATION_COMPLEXITY;
        if (
                t2_type_kind(test->universe, left) == T2_TYPE_VARIABLE
             || t2_type_kind(test->universe, left) == T2_TYPE_META
             || t2_type_kind(test->universe, right) == T2_TYPE_VARIABLE
             || t2_type_kind(test->universe, right) == T2_TYPE_META
             || t2_type_kind(test->universe, result) == T2_TYPE_VARIABLE
             || t2_type_kind(test->universe, result) == T2_TYPE_META
        ) return T2_RELATION_DEFERRED;
        if (
                predicate->kind == T2_PREDICATE_OPERATOR
             && predicate->name != NULL
             && strcmp(predicate->name, "+") == 0
             && left == t2_primitive(test->universe, T2_TYPE_INT)
             && right == left
             && result == left
        ) return T2_RELATION_YES;
        if (
                predicate->kind == T2_PREDICATE_MEMBER_READ
             && predicate->name != NULL
             && strcmp(predicate->name, "length") == 0
             && left == t2_primitive(test->universe, T2_TYPE_STRING)
             && right == t2_primitive(test->universe, T2_TYPE_NEVER)
             && result == t2_primitive(test->universe, T2_TYPE_INT)
        ) return T2_RELATION_YES;
        if (
                predicate->kind == T2_PREDICATE_KEYWORD_SPREAD
             && left == t2_primitive(test->universe, T2_TYPE_STRING)
             && right == t2_primitive(test->universe, T2_TYPE_NEVER)
             && t2_type_kind(test->universe, result) == T2_TYPE_FUNCTION
        ) return T2_RELATION_YES;
        return T2_RELATION_NO;
}

int
main(void)
{
        T2Universe *universe = t2_universe_new();
        CHECK(universe != NULL);

        T2Type never = t2_primitive(universe, T2_TYPE_NEVER);
        T2Type unknown = t2_primitive(universe, T2_TYPE_UNKNOWN);
        T2Type dynamic = t2_primitive(universe, T2_TYPE_DYNAMIC);
        T2Type any = t2_primitive(universe, T2_TYPE_ANY);
        T2Type error = t2_primitive(universe, T2_TYPE_ERROR);
        T2Type nil = t2_primitive(universe, T2_TYPE_NIL);
        T2Type integer = t2_primitive(universe, T2_TYPE_INT);
        T2Type string = t2_primitive(universe, T2_TYPE_STRING);
        T2Type boolean = t2_primitive(universe, T2_TYPE_BOOL);

        CHECK(t2_union(
                universe,
                (T2Type[]) { integer, T2_TYPE_INVALID },
                2
        ) == T2_TYPE_INVALID);
        CHECK(t2_function(
                universe,
                (T2Type[]) { T2_TYPE_INVALID },
                1,
                integer
        ) == T2_TYPE_INVALID);
        CHECK(t2_overload(
                universe,
                (T2Type[]) { integer, T2_TYPE_INVALID },
                2
        ) == T2_TYPE_INVALID);
        CHECK(t2_universe_ok(universe));
        CHECK(t2_literal_string(universe, "still usable") != T2_TYPE_INVALID);

        CHECK(never != unknown && unknown != dynamic && dynamic != any);
        CHECK(t2_subtype(universe, never, integer) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, integer, any) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, any, integer) == T2_RELATION_NO);
        CHECK(t2_consistent(universe, dynamic, integer) == T2_RELATION_YES);
        CHECK(t2_join(universe, any, unknown) == unknown);
        CHECK(t2_join(universe, unknown, any) == unknown);
        CHECK(t2_meet(universe, any, unknown) == unknown);
        CHECK(t2_meet(universe, unknown, any) == unknown);
        CHECK(t2_join(universe, dynamic, integer) == dynamic);
        CHECK(t2_join(universe, integer, dynamic) == dynamic);
        CHECK(t2_meet(universe, dynamic, integer) == integer);
        CHECK(t2_meet(universe, integer, dynamic) == integer);

        T2Type int_or_string_1 = t2_union(
                universe,
                (T2Type[]){ integer, string },
                2
        );
        T2Type int_or_string_2 = t2_union(
                universe,
                (T2Type[]){ string, integer, never, integer },
                4
        );
        CHECK(int_or_string_1 == int_or_string_2);
        check_string(universe, int_or_string_1, "Int | String");

        T2Type one = t2_literal_int(universe, 1);
        T2Type two = t2_literal_int(universe, 2);
        T2Type three = t2_literal_int(universe, 3);
        T2Type four = t2_literal_int(universe, 4);
        T2Type five = t2_literal_int(universe, 5);
        T2Type one_to_four = t2_integer_range(universe, one, four, false);
        T2Type two_to_five = t2_integer_range(universe, two, five, false);
        CHECK(t2_type_kind(universe, one_to_four) == T2_TYPE_INT_RANGE);
        check_string(universe, one_to_four, "1..4");
        CHECK(t2_subtype(universe, one, one_to_four) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, three, one_to_four) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, four, one_to_four) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, one_to_four, integer) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, one_to_four, two_to_five) == T2_RELATION_NO);
        CHECK(t2_meet(universe, one_to_four, two_to_five) != never);
        CHECK(t2_integer_range(universe, four, four, false) == never);
        T2Type inclusive_four = t2_integer_range(universe, four, four, true);
        CHECK(t2_subtype(universe, four, inclusive_four) == T2_RELATION_YES);

        T2Type repeated_int = t2_pack_expansion(universe, integer);
        T2Type two_ints = t2_pack(
                universe,
                (T2Type[]) { integer, integer },
                2,
                T2_TYPE_INVALID
        );
        T2Type mixed_pack = t2_pack(
                universe,
                (T2Type[]) { integer, string },
                2,
                T2_TYPE_INVALID
        );
        CHECK(t2_subtype(universe, two_ints, repeated_int) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, mixed_pack, repeated_int) == T2_RELATION_NO);
        CHECK(t2_pack_fold_union(universe, mixed_pack) == int_or_string_1);
        CHECK(t2_pack_fold_intersection(universe, mixed_pack) == never);
        T2Type variadic_tuple = t2_variadic_tuple(
                universe,
                &string,
                1,
                repeated_int
        );
        check_string(universe, variadic_tuple, "(String, ...Int)");
        T2Type matching_tuple = t2_tuple(
                universe,
                (T2Type[]) { string, integer, integer },
                3
        );
        T2Type mismatching_tuple = t2_tuple(
                universe,
                (T2Type[]) { string, string },
                2
        );
        CHECK(t2_subtype(universe, matching_tuple, variadic_tuple) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, mismatching_tuple, variadic_tuple) == T2_RELATION_NO);

        T2Type int_string_values = t2_multi(
                universe,
                (T2Type[]) { integer, string },
                2
        );
        T2Type optional_string = t2_union(universe, (T2Type[]) { string, nil }, 2);
        T2Type int_optional_string_values = t2_multi(
                universe,
                (T2Type[]) { integer, optional_string },
                2
        );
        check_string(universe, int_string_values, "|Int, String|");
        check_snapshot(universe, int_string_values);
        CHECK(t2_multi(universe, (T2Type[]) { integer, nil }, 2) == integer);
        CHECK(t2_multi(universe, &integer, 1) == integer);
        CHECK(t2_multi(universe, NULL, 0) == nil);
        CHECK(t2_multi_item(universe, int_string_values, 0) == integer);
        CHECK(t2_multi_item(universe, int_string_values, 1) == string);
        CHECK(t2_multi_item(universe, int_string_values, 2) == nil);
        CHECK(t2_multi_item(universe, integer, 0) == integer);
        CHECK(t2_multi_item(universe, integer, 1) == nil);
        CHECK(t2_subtype(
                universe,
                int_string_values,
                int_optional_string_values
        ) == T2_RELATION_YES);
        CHECK(t2_subtype(
                universe,
                int_optional_string_values,
                int_string_values
        ) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, int_string_values, integer) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, integer, int_optional_string_values) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, integer, int_string_values) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, int_string_values, int_string_values) == T2_RELATION_YES);
        CHECK(t2_join(universe, int_string_values, integer) == t2_union(
                universe,
                (T2Type[]) { int_string_values, integer },
                2
        ));
        CHECK(t2_meet(universe, int_string_values, int_optional_string_values) == int_string_values);

        T2Type string_or_bool = t2_union(
                universe,
                (T2Type[]){ string, boolean },
                2
        );
        CHECK(t2_meet(universe, int_or_string_1, string_or_bool) == string);
        CHECK(t2_meet(universe, integer, string) == never);

        T2Type algebra_types[] = {
                never,
                unknown,
                dynamic,
                any,
                error,
                boolean,
                integer,
                string,
                t2_literal_bool(universe, true),
                t2_literal_int(universe, 1),
                t2_literal_string(universe, "s"),
                int_or_string_1,
                string_or_bool
        };
        for (size_t i = 0; i < sizeof algebra_types / sizeof *algebra_types; ++i) {
                CHECK(t2_subtype(
                        universe,
                        algebra_types[i],
                        algebra_types[i]
                ) == T2_RELATION_YES);
                CHECK(t2_join(
                        universe,
                        algebra_types[i],
                        algebra_types[i]
                ) == algebra_types[i]);
                CHECK(t2_meet(
                        universe,
                        algebra_types[i],
                        algebra_types[i]
                ) == algebra_types[i]);

                for (size_t j = 0; j < sizeof algebra_types / sizeof *algebra_types; ++j) {
                        CHECK(t2_join(
                                universe,
                                algebra_types[i],
                                algebra_types[j]
                        ) == t2_join(
                                universe,
                                algebra_types[j],
                                algebra_types[i]
                        ));
                        CHECK(t2_meet(
                                universe,
                                algebra_types[i],
                                algebra_types[j]
                        ) == t2_meet(
                                universe,
                                algebra_types[j],
                                algebra_types[i]
                        ));
                }
        }

        T2Variance covariance[] = { T2_COVARIANT };
        CHECK(t2_declare_nominal(universe, 1, "Array", 1, NULL));
        CHECK(t2_declare_nominal(universe, 2, "Iterable", 1, covariance));
        CHECK(t2_declare_nominal(universe, 3, "Base", 1, covariance));
        CHECK(t2_declare_nominal(universe, 4, "Child", 1, NULL));
        CHECK(t2_declare_nominal(universe, 5, "LateChild", 1, NULL));
        CHECK(t2_declare_nominal(universe, 6, "Regex", 0, NULL));
        T2Type nominal_parameter = t2_nominal_type_parameter(universe, 0);
        T2Type iterable_template = t2_nominal(
                universe,
                2,
                &nominal_parameter,
                1
        );
        CHECK(t2_nominal_add_super(universe, 1, iterable_template));
        T2Type base_template = t2_nominal(universe, 3, &nominal_parameter, 1);
        CHECK(t2_nominal_add_super(universe, 4, base_template));
        T2Type covariant_output = t2_function(
                universe,
                &integer,
                1,
                nominal_parameter
        );
        T2Type invalid_covariant_input = t2_function(
                universe,
                &nominal_parameter,
                1,
                integer
        );
        CHECK(t2_nominal_validate_variance(universe, 3, covariant_output));
        CHECK(!t2_nominal_validate_variance(universe, 3, invalid_covariant_input));
        T2Type array_int = t2_nominal(universe, 1, &integer, 1);
        T2Type array_wide = t2_nominal(universe, 1, &int_or_string_1, 1);
        T2Type iterable_int = t2_nominal(universe, 2, &integer, 1);
        T2Type iterable_wide = t2_nominal(universe, 2, &int_or_string_1, 1);
        CHECK(t2_subtype(universe, array_int, array_wide) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, iterable_int, iterable_wide) == T2_RELATION_YES);
        CHECK(t2_consistent(universe, array_int, integer) == T2_RELATION_NO);
        CHECK(t2_consistent(universe, integer, array_int) == T2_RELATION_NO);
        CHECK(t2_meet(universe, array_int, integer) == never);
        T2Type child_int = t2_nominal(universe, 4, &integer, 1);
        T2Type late_child_int = t2_nominal(universe, 5, &integer, 1);
        T2Type base_int = t2_nominal(universe, 3, &integer, 1);
        T2Type base_wide = t2_nominal(universe, 3, &int_or_string_1, 1);
        CHECK(t2_subtype(universe, child_int, base_int) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, child_int, base_wide) == T2_RELATION_YES);
        CHECK(t2_nominal_project(universe, child_int, 3) == base_int);
        CHECK(t2_nominal_project(universe, child_int, 2) == T2_TYPE_INVALID);
        CHECK(t2_subtype(universe, late_child_int, base_int) == T2_RELATION_NO);
        CHECK(t2_nominal_add_super(universe, 5, base_template));
        CHECK(t2_subtype(universe, late_child_int, base_int) == T2_RELATION_YES);
        CHECK(t2_nominal_project(universe, late_child_int, 3) == base_int);

        T2Type regex = t2_nominal(universe, 6, NULL, 0);
        T2Type regex_zero = t2_refinement(universe, regex, t2_literal_int(universe, 0));
        T2Type regex_one = t2_refinement(universe, regex, t2_literal_int(universe, 1));
        CHECK(t2_type_kind(universe, regex_zero) == T2_TYPE_REFINEMENT);
        CHECK(t2_subtype(universe, regex_zero, regex) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, regex, regex_zero) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, regex_zero, regex_one) == T2_RELATION_NO);
        CHECK(t2_meet(universe, regex_zero, regex_one) == never);
        CHECK(t2_join(universe, regex_zero, regex) == regex);
        check_string(universe, regex_zero, "Regex[0]");

        T2Type flatten_int = t2_computed_type(
                universe,
                1,
                "Flatten",
                &integer,
                1
        );
        T2Type flatten_int_again = t2_computed_type(
                universe,
                1,
                "Flatten",
                &integer,
                1
        );
        T2Type flatten_string = t2_computed_type(
                universe,
                1,
                "Flatten",
                &string,
                1
        );
        CHECK(flatten_int == flatten_int_again);
        CHECK(flatten_int != flatten_string);
        CHECK(t2_type_kind(universe, flatten_int) == T2_TYPE_COMPUTED);
        CHECK(t2_subtype(universe, flatten_int, integer) == T2_RELATION_DEFERRED);
        CHECK(t2_subtype(universe, flatten_int, flatten_string) == T2_RELATION_DEFERRED);
        check_string(universe, flatten_int, "computed Flatten(Int)");
        CHECK(t2_computed_type_result(universe, flatten_int) == T2_TYPE_INVALID);
        CHECK(t2_computed_type_set_result(universe, flatten_int, integer));
        CHECK(t2_computed_type_set_result(universe, flatten_int_again, integer));
        CHECK(!t2_computed_type_set_result(universe, flatten_int, string));
        CHECK(t2_computed_type_result(universe, flatten_int) == integer);
        CHECK(t2_type_resolve_computed(universe, flatten_int) == integer);
        CHECK(t2_subtype(universe, flatten_int, integer) == T2_RELATION_YES);
        CHECK(t2_join(universe, flatten_int, string) == int_or_string_1);
        CHECK(t2_meet(universe, flatten_int, string) == never);
        T2RuntimeFacts runtime_facts;
        CHECK(t2_type_runtime_facts(universe, flatten_int, &runtime_facts));
        CHECK(runtime_facts.exact);
        CHECK(runtime_facts.kind == T2_RUNTIME_INT);
        CHECK(!runtime_facts.nullable);
        T2Type runtime_int_or_nil = t2_union(
                universe,
                (T2Type[]) { integer, nil },
                2
        );
        CHECK(t2_type_runtime_facts(
                universe,
                runtime_int_or_nil,
                &runtime_facts
        ));
        CHECK(runtime_facts.exact);
        CHECK(runtime_facts.kind == T2_RUNTIME_INT);
        CHECK(runtime_facts.nullable);
        CHECK(t2_type_runtime_facts(universe, int_or_string_1, &runtime_facts));
        CHECK(!runtime_facts.exact);
        CHECK(runtime_facts.kind == T2_RUNTIME_UNKNOWN);
        T2Type cyclic_computed = t2_computed_type(
                universe,
                2,
                "Cycle",
                NULL,
                0
        );
        T2Type cyclic_result = t2_tuple(universe, &cyclic_computed, 1);
        CHECK(!t2_computed_type_set_result(
                universe,
                cyclic_computed,
                cyclic_result
        ));
        T2Type computed_chain_a = t2_computed_type(
                universe,
                3,
                "ChainA",
                NULL,
                0
        );
        T2Type computed_chain_b = t2_computed_type(
                universe,
                4,
                "ChainB",
                NULL,
                0
        );
        CHECK(t2_computed_type_set_result(
                universe,
                computed_chain_a,
                computed_chain_b
        ));
        CHECK(!t2_computed_type_set_result(
                universe,
                computed_chain_b,
                computed_chain_a
        ));
        check_snapshot(universe, flatten_int);

        T2Type array_constructor = t2_function(
                universe,
                NULL,
                0,
                array_int
        );
        T2Type array_type_value = t2_type_value(
                universe,
                array_int,
                array_constructor
        );
        CHECK(t2_type_kind(universe, array_type_value) == T2_TYPE_TYPE_VALUE);
        CHECK(t2_type_value_instance(universe, array_type_value) == array_int);
        CHECK(
                t2_type_value_constructor(universe, array_type_value)
             == array_constructor
        );
        CHECK(t2_subtype(
                universe,
                array_type_value,
                t2_primitive(universe, T2_TYPE_OBJECT)
        ) == T2_RELATION_YES);
        check_string(universe, array_type_value, "type[Array[Int]]");
        check_snapshot(universe, array_type_value);

        T2Type wide_parameter = t2_function(
                universe,
                &int_or_string_1,
                1,
                integer
        );
        T2Type narrow_parameter = t2_function(universe, &integer, 1, any);
        CHECK(t2_subtype(universe, wide_parameter, narrow_parameter) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, narrow_parameter, wide_parameter) == T2_RELATION_NO);

        T2FieldSpec a_readonly[] = {{
                .name = "a",
                .type = integer,
                .presence = T2_PRESENCE_REQUIRED,
                .capability = T2_FIELD_READONLY
        }};
        T2FieldSpec ab_readonly[] = {
                a_readonly[0],
                {
                        .name = "b",
                        .type = string,
                        .presence = T2_PRESENCE_REQUIRED,
                        .capability = T2_FIELD_READONLY
                }
        };
        T2Type record_a = t2_record(
                universe,
                a_readonly,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        T2Type record_ab = t2_record(
                universe,
                ab_readonly,
                2,
                T2_TYPE_INVALID,
                T2_RECORD_EXACT
        );
        CHECK(t2_subtype(universe, record_ab, record_a) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, record_a, record_ab) == T2_RELATION_NO);
        T2Type record_b = t2_record(
                universe,
                &ab_readonly[1],
                1,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        T2Type combined_record = t2_meet(universe, record_a, record_b);
        T2Type expected_ab_open = t2_record(
                universe,
                ab_readonly,
                2,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        CHECK(t2_type_kind(universe, combined_record) == T2_TYPE_RECORD);
        CHECK(t2_subtype(
                universe,
                combined_record,
                expected_ab_open
        ) == T2_RELATION_YES);
        T2FieldSpec a_string = a_readonly[0];
        a_string.type = string;
        T2Type incompatible_record = t2_record(
                universe,
                &a_string,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        CHECK(t2_meet(universe, record_a, incompatible_record) == never);

        T2FieldSpec optional_b = {
                .name = "b",
                .type = string,
                .presence = T2_PRESENCE_OPTIONAL,
                .capability = T2_FIELD_READONLY
        };
        T2Type record_optional_b = t2_record(
                universe,
                &optional_b,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        CHECK(t2_subtype(universe, record_ab, record_optional_b) == T2_RELATION_YES);
        T2Presence presence = T2_PRESENCE_UNKNOWN;
        T2FieldCapability capability = T2_FIELD_WRITABLE;
        CHECK(t2_record_field_type(
                universe,
                record_optional_b,
                "b",
                &presence,
                &capability
        ) == string);
        CHECK(presence == T2_PRESENCE_OPTIONAL);
        CHECK(capability == T2_FIELD_READONLY);
        CHECK(t2_record_field_count(universe, record_optional_b) == 1);
        T2FieldSpec reflected_field = {0};
        CHECK(t2_record_field(
                universe,
                record_optional_b,
                0,
                &reflected_field
        ));
        CHECK(strcmp(reflected_field.name, "b") == 0);
        CHECK(reflected_field.type == string);
        CHECK(reflected_field.presence == T2_PRESENCE_OPTIONAL);
        CHECK(reflected_field.capability == T2_FIELD_READONLY);
        CHECK(!t2_record_field(
                universe,
                record_optional_b,
                1,
                &reflected_field
        ));
        CHECK(t2_type_kind(
                universe,
                t2_record_row_tail(universe, record_optional_b)
        ) == T2_TYPE_ROW_ANY);
        T2RecordExactness reflected_exactness = T2_RECORD_EXACT;
        CHECK(t2_record_exactness(
                universe,
                record_optional_b,
                &reflected_exactness
        ));
        CHECK(reflected_exactness == T2_RECORD_OPEN);
        CHECK(t2_record_exactness(
                universe,
                record_ab,
                &reflected_exactness
        ));
        CHECK(reflected_exactness == T2_RECORD_EXACT);

        T2FieldSpec writable_int = {
                .name = "value",
                .type = integer,
                .presence = T2_PRESENCE_REQUIRED,
                .capability = T2_FIELD_WRITABLE
        };
        T2FieldSpec writable_wide = writable_int;
        writable_wide.type = int_or_string_1;
        T2Type record_writable_int = t2_record(
                universe,
                &writable_int,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        T2Type record_writable_wide = t2_record(
                universe,
                &writable_wide,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        CHECK(t2_subtype(
                universe,
                record_writable_int,
                record_writable_wide
        ) == T2_RELATION_NO);

        T2ParameterSpec named_required = {
                .name = "x",
                .type = integer,
                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                .required = true
        };
        T2ParameterSpec differently_named = named_required;
        differently_named.name = "y";
        T2ParameterSpec named_optional = named_required;
        named_optional.required = false;
        T2ParameterSpec positional_required = named_required;
        positional_required.name = NULL;
        positional_required.kind = T2_PARAMETER_POSITIONAL_ONLY;
        T2Type callback_x = t2_callable(
                universe,
                &named_required,
                1,
                integer,
                never,
                t2_primitive(universe, T2_TYPE_NIL)
        );
        T2Type callback_y = t2_callable(
                universe,
                &differently_named,
                1,
                integer,
                never,
                t2_primitive(universe, T2_TYPE_NIL)
        );
        T2Type callback_optional_x = t2_callable(
                universe,
                &named_optional,
                1,
                integer,
                never,
                t2_primitive(universe, T2_TYPE_NIL)
        );
        T2Type callback_positional = t2_callable(
                universe,
                &positional_required,
                1,
                integer,
                never,
                t2_primitive(universe, T2_TYPE_NIL)
        );
        T2Type optional_then_required = t2_callable(
                universe,
                (T2ParameterSpec[]) {
                        {
                                .name = "optional",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = false
                        },
                        {
                                .name = "required",
                                .type = boolean,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        }
                },
                2,
                integer,
                never,
                nil
        );
        CHECK(optional_then_required != T2_TYPE_INVALID);
        CHECK(t2_subtype(
                universe,
                optional_then_required,
                optional_then_required
        ) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, callback_y, callback_x) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, callback_x, callback_optional_x) == T2_RELATION_NO);
        CHECK(t2_subtype(universe, callback_optional_x, callback_x) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, callback_x, callback_positional) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, callback_positional, callback_x) == T2_RELATION_NO);

        T2ParameterSpec pack_then_keyword[] = {
                {
                        .name = "values",
                        .type = mixed_pack,
                        .kind = T2_PARAMETER_PACK,
                        .required = false
                },
                {
                        .name = "longest",
                        .type = boolean,
                        .kind = T2_PARAMETER_KEYWORD_ONLY,
                        .required = false
                }
        };
        T2Type pack_keyword_callable = t2_callable(
                universe,
                pack_then_keyword,
                2,
                integer,
                never,
                nil
        );
        CHECK(pack_keyword_callable != T2_TYPE_INVALID);
        T2ParameterSpec pack_then_positional[] = {
                pack_then_keyword[0],
                positional_required
        };
        CHECK(t2_callable(
                universe,
                pack_then_positional,
                2,
                integer,
                never,
                nil
        ) == T2_TYPE_INVALID);

        T2Type narrow_yield_wide_send = t2_callable(
                universe,
                &named_required,
                1,
                integer,
                integer,
                any
        );
        T2Type wide_yield_narrow_send = t2_callable(
                universe,
                &named_required,
                1,
                integer,
                any,
                integer
        );
        CHECK(t2_subtype(
                universe,
                narrow_yield_wide_send,
                wide_yield_narrow_send
        ) == T2_RELATION_YES);
        CHECK(t2_subtype(
                universe,
                wide_yield_narrow_send,
                narrow_yield_wide_send
        ) == T2_RELATION_NO);
        T2Type effectful_callable = t2_effectful_callable(
                universe,
                &named_required,
                1,
                integer,
                integer,
                any
        );
        CHECK(effectful_callable != T2_TYPE_INVALID);
        CHECK(effectful_callable != narrow_yield_wide_send);
        CHECK(!t2_callable_is_effectful(universe, narrow_yield_wide_send));
        CHECK(t2_callable_is_effectful(universe, effectful_callable));
        check_snapshot(universe, effectful_callable);

        T2Type first_overloads = t2_overload(
                universe,
                (T2Type[]){ callback_x, callback_y },
                2
        );
        T2Type appended_overloads = t2_overload(
                universe,
                (T2Type[]){ first_overloads, callback_optional_x },
                2
        );
        CHECK(t2_type_kind(universe, appended_overloads) == T2_TYPE_OVERLOAD);
        CHECK(t2_type_arity(universe, appended_overloads) == 3);
        CHECK(t2_type_child(universe, appended_overloads, 0) == callback_x);
        CHECK(t2_type_child(universe, appended_overloads, 1) == callback_y);
        CHECK(t2_type_child(universe, appended_overloads, 2) == callback_optional_x);
        CHECK(t2_type_runtime_facts(universe, appended_overloads, &runtime_facts));
        CHECK(runtime_facts.exact);
        CHECK(runtime_facts.kind == T2_RUNTIME_FUNCTION);

        T2Type exact_pack = t2_pack(
                universe,
                (T2Type[]){ integer, string },
                2,
                T2_TYPE_INVALID
        );
        T2Type reversed_pack = t2_pack(
                universe,
                (T2Type[]){ string, integer },
                2,
                T2_TYPE_INVALID
        );
        CHECK(t2_subtype(universe, exact_pack, exact_pack) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, exact_pack, reversed_pack) == T2_RELATION_NO);

        T2Type recursive_variable_1 = t2_recursive_variable(universe, 1001);
        T2FieldSpec recursive_field_1 = {
                .name = "next",
                .type = recursive_variable_1,
                .presence = T2_PRESENCE_OPTIONAL,
                .capability = T2_FIELD_READONLY
        };
        T2Type recursive_body_1 = t2_record(
                universe,
                &recursive_field_1,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_EXACT
        );
        T2Type recursive_1 = t2_recursive(universe, 1001, recursive_body_1);
        T2Type recursive_variable_2 = t2_recursive_variable(universe, 1002);
        T2FieldSpec recursive_field_2 = recursive_field_1;
        recursive_field_2.type = recursive_variable_2;
        T2Type recursive_body_2 = t2_record(
                universe,
                &recursive_field_2,
                1,
                T2_TYPE_INVALID,
                T2_RECORD_EXACT
        );
        T2Type recursive_2 = t2_recursive(universe, 1002, recursive_body_2);
        CHECK(recursive_1 != T2_TYPE_INVALID && recursive_2 != T2_TYPE_INVALID);
        CHECK(t2_recursive_is_guarded(universe, recursive_1));
        CHECK(t2_subtype(universe, recursive_1, recursive_2) == T2_RELATION_YES);
        CHECK(t2_subtype(universe, recursive_2, recursive_1) == T2_RELATION_YES);
        check_snapshot(universe, recursive_1);
        CHECK(t2_type_runtime_facts(universe, recursive_1, &runtime_facts));
        CHECK(runtime_facts.exact);
        CHECK(runtime_facts.kind == T2_RUNTIME_RECORD);
        T2Universe *reflection_universe = t2_universe_new();
        CHECK(reflection_universe != NULL);
        T2TypeSnapshot *recursive_snapshot = t2_type_snapshot_new(
                universe,
                recursive_1
        );
        CHECK(recursive_snapshot != NULL);
        T2Type reflected_recursive = t2_type_snapshot_import(
                reflection_universe,
                recursive_snapshot
        );
        CHECK(reflected_recursive != T2_TYPE_INVALID);
        CHECK(t2_recursive_is_guarded(
                reflection_universe,
                reflected_recursive
        ));
        char *source_recursive = t2_type_string(universe, recursive_1);
        char *target_recursive = t2_type_string(
                reflection_universe,
                reflected_recursive
        );
        CHECK(source_recursive != NULL && target_recursive != NULL);
        if (source_recursive != NULL && target_recursive != NULL) {
                CHECK(strcmp(source_recursive, target_recursive) == 0);
        }
        free(source_recursive);
        free(target_recursive);
        t2_type_snapshot_free(recursive_snapshot);
        t2_universe_free(reflection_universe);
        CHECK(t2_recursive(universe, 1004, integer) == integer);
        T2Type unguarded = t2_recursive_variable(universe, 1003);
        CHECK(t2_recursive(universe, 1003, unguarded) == T2_TYPE_INVALID);
        uint32_t fresh_binder_1 = t2_universe_fresh_recursive_binder(universe);
        uint32_t fresh_binder_2 = t2_universe_fresh_recursive_binder(universe);
        CHECK(fresh_binder_1 != 0);
        CHECK(fresh_binder_2 != 0);
        CHECK(fresh_binder_1 != fresh_binder_2);

        T2Type quantified = t2_variable(universe, T2_VARIABLE_QUANTIFIED, 1);
        T2Type quantified_or_nil = t2_union(
                universe,
                (T2Type[]) { quantified, nil },
                2
        );
        CHECK(t2_subtype(
                universe,
                quantified,
                quantified_or_nil
        ) == T2_RELATION_YES);
        CHECK(t2_subtype(
                universe,
                nil,
                quantified_or_nil
        ) == T2_RELATION_YES);
        CHECK(t2_subtype(
                universe,
                nil,
                quantified
        ) == T2_RELATION_DEFERRED);
        T2Solver *tautology_solver = t2_solver_new(universe);
        CHECK(tautology_solver != NULL);
        CHECK(t2_solver_constrain_subtype(
                tautology_solver,
                quantified,
                quantified_or_nil,
                "quantified union tautology"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                tautology_solver,
                nil,
                quantified_or_nil,
                "concrete union arm"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(tautology_solver) == 0);
        t2_solver_free(tautology_solver);

        T2Solver *self_union_solver = t2_solver_new(universe);
        CHECK(self_union_solver != NULL);
        T2Type self_union_meta = t2_solver_new_meta(
                self_union_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "self union"
        );
        T2Type self_union = t2_union(
                universe,
                (T2Type[]) { self_union_meta, string },
                2
        );
        CHECK(t2_solver_unify(
                self_union_solver,
                self_union_meta,
                self_union,
                "finite set equation"
        ) == T2_RELATION_YES);
        CHECK(!t2_solver_failed(self_union_solver));
        CHECK(t2_solver_lower_bound(
                self_union_solver,
                self_union_meta
        ) == string);
        t2_solver_free(self_union_solver);

        T2Solver *self_edge_solver = t2_solver_new(universe);
        CHECK(self_edge_solver != NULL);
        T2Type edge_subtype = t2_solver_new_meta(
                self_edge_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "self-union edge subtype"
        );
        T2Type edge_supertype = t2_solver_new_meta(
                self_edge_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "self-union edge supertype"
        );
        CHECK(t2_solver_constrain_subtype(
                self_edge_solver,
                edge_subtype,
                edge_supertype,
                "subtype edge"
        ) == T2_RELATION_YES);
        T2Type edge_recursive_upper = t2_union(
                universe,
                (T2Type[]) { quantified, edge_subtype },
                2
        );
        CHECK(t2_solver_constrain_subtype(
                self_edge_solver,
                edge_supertype,
                edge_recursive_upper,
                "tautological propagated upper bound"
        ) == T2_RELATION_YES);
        CHECK(!t2_solver_failed(self_edge_solver));
        t2_solver_free(self_edge_solver);

        T2Solver *merged_union_solver = t2_solver_new(universe);
        CHECK(merged_union_solver != NULL);
        T2Type merged_source = t2_solver_new_meta(
                merged_union_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "merged union source"
        );
        T2Type merged_left = t2_solver_new_meta(
                merged_union_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "merged union left"
        );
        T2Type merged_right = t2_solver_new_meta(
                merged_union_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "merged union right"
        );
        T2Type merged_left_array = t2_nominal(
                universe,
                1,
                &merged_left,
                1
        );
        T2Type merged_right_array = t2_nominal(
                universe,
                1,
                &merged_right,
                1
        );
        T2Type merged_source_array = t2_nominal(
                universe,
                1,
                &merged_source,
                1
        );
        T2Type merged_array_union = t2_union(
                universe,
                (T2Type[]) { merged_left_array, merged_right_array },
                2
        );
        CHECK(t2_solver_constrain_subtype(
                merged_union_solver,
                merged_source_array,
                merged_array_union,
                "union arms become identical"
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(merged_union_solver) == 1);
        CHECK(t2_solver_unify(
                merged_union_solver,
                merged_left,
                merged_right,
                "merge union arm variables"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_unify(
                merged_union_solver,
                merged_source,
                merged_left,
                "merge union source variable"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(merged_union_solver) == 0);
        t2_solver_free(merged_union_solver);

        T2Type generic_identity_type = t2_function(universe, &quantified, 1, quantified);
        T2Scheme *identity_scheme = t2_scheme_new(
                universe,
                (T2Quantifier[]){{ .id = 1, .kind = T2_VARIABLE_QUANTIFIED }},
                1,
                generic_identity_type,
                NULL,
                0
        );
        CHECK(identity_scheme != NULL);

        T2Solver *row_lattice_solver = t2_solver_new(universe);
        CHECK(row_lattice_solver != NULL);
        T2Type row_tail_a = t2_solver_new_meta(
                row_lattice_solver,
                T2_VARIABLE_ROW,
                0,
                "row meet tail a"
        );
        T2Type row_tail_b = t2_solver_new_meta(
                row_lattice_solver,
                T2_VARIABLE_ROW,
                0,
                "row meet tail b"
        );
        T2FieldSpec len_field = {
                .name = "len",
                .type = integer,
                .presence = T2_PRESENCE_REQUIRED,
                .capability = T2_FIELD_READONLY
        };
        T2FieldSpec words_field = {
                .name = "words",
                .type = string,
                .presence = T2_PRESENCE_REQUIRED,
                .capability = T2_FIELD_READONLY
        };
        T2Type record_len = t2_record(
                universe,
                &len_field,
                1,
                row_tail_a,
                T2_RECORD_OPEN
        );
        T2Type record_words = t2_record(
                universe,
                &words_field,
                1,
                row_tail_b,
                T2_RECORD_OPEN
        );
        T2Type record_len_words = t2_meet(universe, record_len, record_words);
        CHECK(record_len_words != T2_TYPE_INVALID);
        CHECK(t2_type_kind(universe, record_len_words) == T2_TYPE_RECORD);
        CHECK(t2_meet(universe, record_len_words, record_len) == record_len_words);
        CHECK(t2_meet(universe, record_len, record_len_words) == record_len_words);
        CHECK(t2_meet(universe, record_len_words, record_words) == record_len_words);
        CHECK(t2_meet(universe, record_words, record_len_words) == record_len_words);

        T2Type constrained_record = t2_solver_new_meta(
                row_lattice_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "record with multiple upper edges"
        );
        T2Type len_upper = t2_solver_new_meta(
                row_lattice_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "len upper"
        );
        T2Type words_upper = t2_solver_new_meta(
                row_lattice_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "words upper"
        );
        CHECK(t2_solver_constrain_subtype(
                row_lattice_solver,
                constrained_record,
                len_upper,
                "len edge"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                row_lattice_solver,
                constrained_record,
                words_upper,
                "words edge"
        ) == T2_RELATION_YES);
        uint64_t row_work_start = t2_solver_work_steps(row_lattice_solver);
        CHECK(t2_solver_constrain_subtype(
                row_lattice_solver,
                len_upper,
                record_len,
                "len requirement"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                row_lattice_solver,
                words_upper,
                record_words,
                "words requirement"
        ) == T2_RELATION_YES);
        CHECK(!t2_solver_failed(row_lattice_solver));
        CHECK(t2_solver_upper_bound(
                row_lattice_solver,
                constrained_record
        ) == record_len_words);
        CHECK(t2_solver_work_steps(row_lattice_solver) - row_work_start < 64);
        CHECK(t2_solver_meta_count(row_lattice_solver) == 5);
        CHECK(t2_solver_edge_count(row_lattice_solver) == 2);
        CHECK(t2_universe_type_count(universe) != 0);
        t2_solver_free(row_lattice_solver);

        T2Solver *solver = t2_solver_new(universe);
        CHECK(solver != NULL);

        T2Type inferred_pack = t2_solver_new_meta(
                solver,
                T2_VARIABLE_PACK,
                0,
                "inferred heterogeneous pack"
        );
        CHECK(t2_type_snapshot_new(universe, inferred_pack) == NULL);
        T2Type inferred_pack_union = t2_pack_fold_union(universe, inferred_pack);
        CHECK(t2_type_kind(universe, inferred_pack_union) == T2_TYPE_PACK_FOLD_UNION);
        CHECK(t2_solver_constrain_subtype(
                solver,
                mixed_pack,
                inferred_pack,
                "pack arguments"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_zonk(
                solver,
                inferred_pack_union,
                T2_PREFER_LOWER_BOUND
        ) == int_or_string_1);

        T2Type mapped_pack = t2_solver_new_meta(
                solver,
                T2_VARIABLE_PACK,
                0,
                "mapped nominal pack"
        );
        T2Type mapped_iterable = t2_nominal(
                universe,
                2,
                &mapped_pack,
                1
        );
        T2Type mapped_expansion = t2_pack_expansion(
                universe,
                mapped_iterable
        );
        T2Type array_string = t2_nominal(universe, 1, &string, 1);
        T2Type mapped_arguments = t2_pack(
                universe,
                (T2Type[]) { array_int, array_string },
                2,
                T2_TYPE_INVALID
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                mapped_arguments,
                mapped_expansion,
                "mapped pack arguments"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_zonk(
                solver,
                mapped_pack,
                T2_PREFER_LOWER_BOUND
        ) == mixed_pack);
        T2Type mapped_tuple = t2_variadic_tuple(
                universe,
                &boolean,
                1,
                mapped_pack
        );
        CHECK(t2_solver_zonk(
                solver,
                mapped_tuple,
                T2_PREFER_LOWER_BOUND
        ) == t2_tuple(
                universe,
                (T2Type[]) { boolean, integer, string },
                3
        ));

        T2Type identity_1 = t2_scheme_instantiate(
                identity_scheme,
                solver,
                0,
                "identity use 1"
        );
        T2Type identity_2 = t2_scheme_instantiate(
                identity_scheme,
                solver,
                0,
                "identity use 2"
        );
        CHECK(identity_1 != T2_TYPE_INVALID && identity_2 != T2_TYPE_INVALID);
        CHECK(identity_1 != identity_2);

        T2Type function_meta = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "function parameter and result"
        );
        T2Type inferred_identity = t2_function(
                universe,
                &function_meta,
                1,
                function_meta
        );
        T2Type integer_identity = t2_function(universe, &integer, 1, integer);
        CHECK(t2_solver_constrain_subtype(
                solver,
                inferred_identity,
                integer_identity,
                "callback protocol"
        ) != T2_RELATION_NO);
        CHECK(t2_solver_lower_bound(solver, function_meta) == integer);
        CHECK(t2_solver_upper_bound(solver, function_meta) == integer);

        T2Type forward_callable = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "forward callable"
        );
        T2Type forward_result = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "forward result"
        );
        T2Type forward_protocol = t2_function(
                universe,
                &integer,
                1,
                forward_result
        );
        T2Type later_definition = t2_function(
                universe,
                &integer,
                1,
                string
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                forward_callable,
                forward_protocol,
                "forward call"
        ) != T2_RELATION_NO);
        CHECK(t2_solver_constrain_subtype(
                solver,
                later_definition,
                forward_callable,
                "later definition"
        ) != T2_RELATION_NO);
        CHECK(t2_solver_lower_bound(solver, forward_result) == string);

        T2Type preserved_row = t2_solver_new_meta(
                solver,
                T2_VARIABLE_ROW,
                0,
                "preserved record fields"
        );
        T2Type expected_open_a = t2_record(
                universe,
                a_readonly,
                1,
                preserved_row,
                T2_RECORD_OPEN
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                record_ab,
                expected_open_a,
                "row preservation"
        ) != T2_RELATION_NO);
        T2Type row_solution = t2_solver_solution(
                solver,
                preserved_row,
                T2_PREFER_LOWER_BOUND
        );
        CHECK(t2_type_kind(universe, row_solution) == T2_TYPE_ROW);
        CHECK(t2_record_field_type(
                universe,
                row_solution,
                "b",
                NULL,
                NULL
        ) == string);

        T2Type pack_remainder = t2_solver_new_meta(
                solver,
                T2_VARIABLE_PACK,
                0,
                "pack remainder"
        );
        T2Type expected_pack_prefix = t2_pack(
                universe,
                &integer,
                1,
                pack_remainder
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                exact_pack,
                expected_pack_prefix,
                "pack prefix"
        ) != T2_RELATION_NO);
        T2Type pack_solution = t2_solver_solution(
                solver,
                pack_remainder,
                T2_PREFER_LOWER_BOUND
        );
        check_string(universe, pack_solution, "pack[String]");

        T2Type union_trial_meta = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "unique union arm"
        );
        T2Type tuple_int = t2_tuple(universe, &integer, 1);
        T2Type tuple_string = t2_tuple(universe, &string, 1);
        T2Type tuple_meta = t2_tuple(universe, &union_trial_meta, 1);
        T2Type tuple_union = t2_union(
                universe,
                (T2Type[]){ tuple_string, tuple_meta },
                2
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                tuple_int,
                tuple_union,
                "transactional union selection"
        ) != T2_RELATION_NO);
        CHECK(t2_solver_lower_bound(solver, union_trial_meta) == integer);

        T2Type lower_meta = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "repeated parameter"
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                integer,
                lower_meta,
                "argument 1"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                solver,
                string,
                lower_meta,
                "argument 2"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_lower_bound(solver, lower_meta) == int_or_string_1);
        CHECK(t2_solver_solution(
                solver,
                lower_meta,
                T2_PREFER_LOWER_BOUND
        ) == int_or_string_1);
        CHECK(t2_solver_zonk(
                solver,
                lower_meta,
                T2_PREFER_LOWER_BOUND
        ) == int_or_string_1);

        T2Type ordinary_occurs = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "ordinary occurs check"
        );
        T2Type recursive_array = t2_nominal(universe, 1, &ordinary_occurs, 1);
        T2SolverMark ordinary_occurs_mark = t2_solver_mark(solver);
        CHECK(t2_solver_constrain_subtype(
                solver,
                ordinary_occurs,
                recursive_array,
                "infinite inferred type"
        ) == T2_RELATION_NO);
        CHECK(t2_solver_failed(solver));
        t2_solver_rollback(solver, ordinary_occurs_mark);
        CHECK(!t2_solver_failed(solver));

        T2Type upper_meta = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "parameter domain"
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                upper_meta,
                int_or_string_1,
                "use 1"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                solver,
                upper_meta,
                string_or_bool,
                "use 2"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_upper_bound(solver, upper_meta) == string);
        CHECK(t2_solver_solution(
                solver,
                upper_meta,
                T2_PREFER_UPPER_BOUND
        ) == string);

        T2Type reverse_upper = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "reversed parameter domain"
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                reverse_upper,
                string_or_bool,
                "reversed use 1"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                solver,
                reverse_upper,
                int_or_string_1,
                "reversed use 2"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_upper_bound(solver, reverse_upper) == string);

        T2Type edge_left = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "edge left"
        );
        T2Type edge_right = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "edge right"
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                edge_left,
                edge_right,
                "edge"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                solver,
                integer,
                edge_left,
                "flow"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_lower_bound(solver, edge_right) == integer);

        T2Type trial = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "overload trial"
        );
        T2SolverMark mark = t2_solver_mark(solver);
        CHECK(t2_solver_constrain_subtype(
                solver,
                integer,
                trial,
                "trial argument"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                solver,
                trial,
                string,
                "trial context"
        ) == T2_RELATION_NO);
        CHECK(t2_solver_failed(solver));
        t2_solver_rollback(solver, mark);
        CHECK(!t2_solver_failed(solver));
        CHECK(t2_solver_lower_bound(solver, trial) == never);
        CHECK(t2_solver_upper_bound(solver, trial) == any);
        CHECK(t2_solver_constrain_subtype(
                solver,
                string,
                trial,
                "committed argument"
        ) == T2_RELATION_YES);

        T2Type rolled_edge_left = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "rolled edge left"
        );
        T2Type rolled_edge_right = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "rolled edge right"
        );
        mark = t2_solver_mark(solver);
        CHECK(t2_solver_constrain_subtype(
                solver,
                rolled_edge_left,
                rolled_edge_right,
                "temporary edge"
        ) == T2_RELATION_YES);
        t2_solver_rollback(solver, mark);
        CHECK(t2_solver_constrain_subtype(
                solver,
                integer,
                rolled_edge_left,
                "post-rollback flow"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_lower_bound(solver, rolled_edge_right) == never);

        T2Type nested_trial = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "nested trial"
        );
        T2SolverMark outer = t2_solver_mark(solver);
        CHECK(t2_solver_constrain_subtype(
                solver,
                integer,
                nested_trial,
                "outer lower"
        ) == T2_RELATION_YES);
        T2SolverMark inner = t2_solver_mark(solver);
        CHECK(t2_solver_constrain_subtype(
                solver,
                nested_trial,
                int_or_string_1,
                "inner upper"
        ) == T2_RELATION_YES);
        t2_solver_commit(solver, inner);
        CHECK(t2_solver_lower_bound(solver, nested_trial) == integer);
        CHECK(t2_solver_upper_bound(solver, nested_trial) == int_or_string_1);
        t2_solver_rollback(solver, outer);
        CHECK(t2_solver_lower_bound(solver, nested_trial) == never);
        CHECK(t2_solver_upper_bound(solver, nested_trial) == any);

        T2Type equal_left = t2_solver_new_meta(
                solver,
                T2_VARIABLE_WEAK,
                0,
                "equality left"
        );
        T2Type equal_right = t2_solver_new_meta(
                solver,
                T2_VARIABLE_WEAK,
                0,
                "equality right"
        );
        CHECK(t2_solver_constrain_subtype(
                solver,
                integer,
                equal_left,
                "lower"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                solver,
                equal_right,
                int_or_string_1,
                "upper"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_unify(
                solver,
                equal_left,
                equal_right,
                "equality"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_lower_bound(solver, equal_right) == integer);
        CHECK(t2_solver_upper_bound(solver, equal_left) == int_or_string_1);

        CHECK(t2_universe_ok(universe));
        CHECK(!t2_solver_failed(solver));
        CHECK(t2_solver_pending_obligations(solver) == 0);

        t2_solver_free(solver);
        t2_scheme_free(identity_scheme);

        T2Solver *kind_solver = t2_solver_new(universe);
        CHECK(kind_solver != NULL);
        CHECK(t2_solver_new_meta(
                kind_solver,
                T2_VARIABLE_RIGID,
                0,
                "rigid"
        ) == T2_TYPE_INVALID);
        T2Type row_meta = t2_solver_new_meta(
                kind_solver,
                T2_VARIABLE_ROW,
                0,
                "row"
        );
        T2Type pack_meta = t2_solver_new_meta(
                kind_solver,
                T2_VARIABLE_PACK,
                0,
                "pack"
        );
        CHECK(t2_solver_unify(
                kind_solver,
                pack_meta,
                exact_pack,
                "pack sequence"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_solution(
                kind_solver,
                pack_meta,
                T2_PREFER_LOWER_BOUND
        ) == exact_pack);

        T2Type concrete_row = t2_row(
                universe,
                a_readonly,
                1,
                T2_TYPE_INVALID
        );
        CHECK(concrete_row != T2_TYPE_INVALID);
        CHECK(t2_solver_unify(
                kind_solver,
                row_meta,
                concrete_row,
                "row suffix"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_solution(
                kind_solver,
                row_meta,
                T2_PREFER_LOWER_BOUND
        ) == concrete_row);

        T2Type recursive_pack_meta = t2_solver_new_meta(
                kind_solver,
                T2_VARIABLE_PACK,
                0,
                "recursive pack"
        );
        T2Type recursive_pack = t2_pack(
                universe,
                NULL,
                0,
                recursive_pack_meta
        );
        T2SolverMark occurs_mark = t2_solver_mark(kind_solver);
        CHECK(t2_solver_unify(
                kind_solver,
                recursive_pack_meta,
                recursive_pack,
                "pack occurs check"
        ) == T2_RELATION_NO);
        CHECK(t2_solver_failed(kind_solver));
        t2_solver_rollback(kind_solver, occurs_mark);
        CHECK(!t2_solver_failed(kind_solver));

        mark = t2_solver_mark(kind_solver);
        CHECK(t2_solver_constrain_subtype(
                kind_solver,
                row_meta,
                pack_meta,
                "kind mismatch"
        ) == T2_RELATION_NO);
        CHECK(t2_solver_failed(kind_solver));
        t2_solver_rollback(kind_solver, mark);
        CHECK(!t2_solver_failed(kind_solver));
        t2_solver_free(kind_solver);

        T2Solver *diagnostic_solver = t2_solver_new(universe);
        CHECK(diagnostic_solver != NULL);
        T2Type diagnostic_meta = t2_solver_new_meta(
                diagnostic_solver,
                T2_VARIABLE_FLEXIBLE,
                0,
                "diagnostic variable"
        );
        CHECK(t2_solver_constrain_subtype(
                diagnostic_solver,
                integer,
                diagnostic_meta,
                "argument 1"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_constrain_subtype(
                diagnostic_solver,
                diagnostic_meta,
                string,
                "parameter use"
        ) == T2_RELATION_NO);
        char *explanation = t2_solver_explain(diagnostic_solver);
        CHECK(explanation != NULL);
        if (explanation != NULL) {
                CHECK(strstr(explanation, "argument 1") != NULL);
                CHECK(strstr(explanation, "parameter use") != NULL);
        }
        free(explanation);
        t2_solver_free(diagnostic_solver);

        T2Solver *generalization_solver = t2_solver_new(universe);
        CHECK(generalization_solver != NULL);
        T2Type generalized_meta = t2_solver_new_meta(
                generalization_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "generalized identity"
        );
        T2Type generalized_identity = t2_function(
                universe,
                &generalized_meta,
                1,
                generalized_meta
        );
        T2Scheme *generalized_scheme = t2_solver_generalize(
                generalization_solver,
                generalized_identity,
                NULL,
                0,
                0,
                false
        );
        CHECK(generalized_scheme != NULL);
        T2Type generalized_use_1 = t2_scheme_instantiate(
                generalized_scheme,
                generalization_solver,
                0,
                "generalized use 1"
        );
        T2Type generalized_use_2 = t2_scheme_instantiate(
                generalized_scheme,
                generalization_solver,
                0,
                "generalized use 2"
        );
        CHECK(generalized_use_1 != generalized_use_2);

        T2Type receiver_parameter = t2_variable(
                universe,
                T2_VARIABLE_QUANTIFIED,
                9001
        );
        T2Type projected_key = t2_solver_new_meta(
                generalization_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "receiver projection key"
        );
        T2Type projected_value = t2_solver_new_meta(
                generalization_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "receiver projection value"
        );
        T2Type projected_pair = t2_tuple(
                universe,
                (T2Type[]) { projected_key, projected_value },
                2
        );
        CHECK(t2_solver_constrain_subtype(
                generalization_solver,
                receiver_parameter,
                projected_pair,
                "receiver-dependent tuple projection"
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(generalization_solver) == 1);
        T2Predicate pending_projection;
        CHECK(t2_solver_pending_obligation(
                generalization_solver,
                0,
                &pending_projection
        ));
        CHECK(pending_projection.subtype == receiver_parameter);
        CHECK(pending_projection.supertype == projected_pair);
        CHECK(strcmp(
                pending_projection.provenance,
                "receiver-dependent tuple projection"
        ) == 0);
        CHECK(!t2_solver_pending_obligation(
                generalization_solver,
                1,
                &pending_projection
        ));
        T2Scheme *projected_scheme = t2_solver_generalize(
                generalization_solver,
                projected_pair,
                NULL,
                0,
                0,
                false
        );
        CHECK(projected_scheme != NULL);
        CHECK(t2_scheme_quantifier_count(projected_scheme) == 2);
        CHECK(t2_scheme_predicate_count(projected_scheme) == 1);
        CHECK(t2_solver_pending_obligations(generalization_solver) == 0);

        T2SolverMark scoped_mark = t2_solver_mark(generalization_solver);
        CHECK(t2_solver_constrain_subtype(
                generalization_solver,
                nil,
                receiver_parameter,
                "scoped enclosing predicate"
        ) == T2_RELATION_DEFERRED);
        T2Scheme *scoped_scheme = t2_solver_generalize_scoped(
                generalization_solver,
                receiver_parameter,
                NULL,
                0,
                0,
                false,
                scoped_mark
        );
        CHECK(scoped_scheme != NULL);
        CHECK(t2_scheme_predicate_count(scoped_scheme) == 1);
        CHECK(t2_solver_pending_obligations(generalization_solver) == 0);
        t2_solver_commit(generalization_solver, scoped_mark);

        T2Scheme *environment_scheme = t2_solver_generalize(
                generalization_solver,
                generalized_identity,
                &generalized_meta,
                1,
                0,
                false
        );
        CHECK(environment_scheme != NULL);
        T2Type environment_use_1 = t2_scheme_instantiate(
                environment_scheme,
                generalization_solver,
                0,
                "environment use 1"
        );
        T2Type environment_use_2 = t2_scheme_instantiate(
                environment_scheme,
                generalization_solver,
                0,
                "environment use 2"
        );
        CHECK(environment_use_1 == environment_use_2);

        T2Type mutable_meta = t2_solver_new_meta(
                generalization_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "mutable allocation"
        );
        T2Type mutable_array = t2_nominal(universe, 1, &mutable_meta, 1);
        T2Scheme *mutable_scheme = t2_solver_generalize(
                generalization_solver,
                mutable_array,
                NULL,
                0,
                0,
                true
        );
        CHECK(mutable_scheme != NULL);
        CHECK(t2_scheme_instantiate(
                mutable_scheme,
                generalization_solver,
                0,
                "mutable use 1"
        ) == t2_scheme_instantiate(
                mutable_scheme,
                generalization_solver,
                0,
                "mutable use 2"
        ));

        T2Type readonly_meta = t2_solver_new_meta(
                generalization_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "covariant allocation"
        );
        T2Type readonly_iterable = t2_nominal(universe, 2, &readonly_meta, 1);
        T2Scheme *readonly_scheme = t2_solver_generalize(
                generalization_solver,
                readonly_iterable,
                NULL,
                0,
                0,
                true
        );
        CHECK(readonly_scheme != NULL);
        CHECK(t2_scheme_instantiate(
                readonly_scheme,
                generalization_solver,
                0,
                "readonly use 1"
        ) != t2_scheme_instantiate(
                readonly_scheme,
                generalization_solver,
                0,
                "readonly use 2"
        ));

        T2Type weak_meta = t2_solver_new_meta(
                generalization_solver,
                T2_VARIABLE_WEAK,
                1,
                "captured mutable state"
        );
        T2Scheme *weak_scheme = t2_solver_generalize(
                generalization_solver,
                weak_meta,
                NULL,
                0,
                0,
                false
        );
        CHECK(weak_scheme != NULL);
        CHECK(t2_scheme_instantiate(
                weak_scheme,
                generalization_solver,
                0,
                "weak use 1"
        ) == t2_scheme_instantiate(
                weak_scheme,
                generalization_solver,
                0,
                "weak use 2"
        ));

        T2Solver *predicate_solver = t2_solver_new(universe);
        CHECK(predicate_solver != NULL);
        PredicateTestContext predicate_context = { .universe = universe };
        t2_solver_set_predicate_resolver(
                predicate_solver,
                resolve_test_predicate,
                &predicate_context
        );

        T2Type predicate_meta = t2_solver_new_meta(
                predicate_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "operator operand"
        );
        T2Predicate plus_predicate = {
                .kind = T2_PREDICATE_OPERATOR,
                .subtype = predicate_meta,
                .supertype = integer,
                .operand = predicate_meta,
                .name = "+",
                .provenance = "operator constraint"
        };
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &plus_predicate
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        CHECK(t2_solver_constrain_subtype(
                predicate_solver,
                integer,
                predicate_meta,
                "integer argument"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);

        T2Type member_subject = t2_solver_new_meta(
                predicate_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "member receiver"
        );
        T2Predicate member_predicate = {
                .kind = T2_PREDICATE_MEMBER_READ,
                .subtype = member_subject,
                .supertype = integer,
                .operand = never,
                .name = "length",
                .provenance = "member constraint"
        };
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &member_predicate
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        CHECK(t2_solver_constrain_subtype(
                predicate_solver,
                string,
                member_subject,
                "string receiver"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);

        T2Type keyword_subject = t2_solver_new_meta(
                predicate_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "keyword spread"
        );
        T2Type keyword_callable = t2_function(
                universe,
                &string,
                1,
                integer
        );
        T2Predicate keyword_predicate = {
                .kind = T2_PREDICATE_KEYWORD_SPREAD,
                .subtype = keyword_subject,
                .supertype = keyword_callable,
                .operand = never,
                .name = "*",
                .provenance = "keyword spread constraint"
        };
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &keyword_predicate
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        CHECK(t2_solver_constrain_subtype(
                predicate_solver,
                string,
                keyword_subject,
                "keyword mapping"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);

        T2Type rollback_meta = t2_solver_new_meta(
                predicate_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "rollback operand"
        );
        T2SolverMark predicate_mark = t2_solver_mark(predicate_solver);
        plus_predicate.subtype = rollback_meta;
        plus_predicate.operand = rollback_meta;
        plus_predicate.provenance = "rolled-back operator constraint";
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &plus_predicate
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        t2_solver_rollback(predicate_solver, predicate_mark);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);

        T2Type cancelled_meta = t2_solver_new_meta(
                predicate_solver,
                T2_VARIABLE_FLEXIBLE,
                1,
                "cancelled operand"
        );
        T2SolverMark cancelled_mark = t2_solver_mark(predicate_solver);
        plus_predicate.subtype = cancelled_meta;
        plus_predicate.operand = cancelled_meta;
        plus_predicate.provenance = "cancelled operator constraint";
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &plus_predicate
        ) == T2_RELATION_DEFERRED);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        CHECK(t2_solver_cancel_obligations_since(
                predicate_solver,
                cancelled_mark
        ));
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);
        t2_solver_commit(predicate_solver, cancelled_mark);
        CHECK(t2_solver_constrain_subtype(
                predicate_solver,
                integer,
                cancelled_meta,
                "cancelled predicate no longer wakes"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);

        T2Type scoped_predicate_meta = t2_solver_new_meta(
                predicate_solver,
                T2_VARIABLE_FLEXIBLE,
                2,
                "predicate-only scoped variable"
        );
        T2SolverMark predicate_scope = t2_solver_mark(predicate_solver);
        plus_predicate.subtype = scoped_predicate_meta;
        plus_predicate.operand = scoped_predicate_meta;
        plus_predicate.provenance = "predicate-only scoped constraint";
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &plus_predicate
        ) == T2_RELATION_DEFERRED);
        T2Scheme *predicate_only_scheme = t2_solver_generalize_scoped(
                predicate_solver,
                integer,
                NULL,
                0,
                1,
                false,
                predicate_scope
        );
        CHECK(predicate_only_scheme != NULL);
        CHECK(t2_scheme_quantifier_count(predicate_only_scheme) == 0);
        CHECK(t2_scheme_predicate_count(predicate_only_scheme) == 0);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        CHECK(t2_scheme_instantiate(
                predicate_only_scheme,
                predicate_solver,
                2,
                "predicate-only scheme use"
        ) == integer);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        CHECK(t2_solver_cancel_obligations_since(
                predicate_solver,
                predicate_scope
        ));
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);
        t2_solver_commit(predicate_solver, predicate_scope);

        T2Type class_parameter = t2_variable(
                universe,
                T2_VARIABLE_QUANTIFIED,
                9199
        );
        T2Type class_method = t2_function(
                universe,
                &class_parameter,
                1,
                class_parameter
        );
        T2SolverMark class_predicate_scope = t2_solver_mark(predicate_solver);
        plus_predicate.subtype = class_parameter;
        plus_predicate.supertype = class_parameter;
        plus_predicate.operand = class_parameter;
        plus_predicate.provenance = "class-parameter scoped constraint";
        CHECK(t2_solver_constrain_predicate(
                predicate_solver,
                &plus_predicate
        ) == T2_RELATION_DEFERRED);
        T2Scheme *class_predicate_scheme = t2_solver_generalize_scoped(
                predicate_solver,
                class_method,
                NULL,
                0,
                1,
                false,
                class_predicate_scope
        );
        CHECK(class_predicate_scheme != NULL);
        CHECK(t2_scheme_quantifier_count(class_predicate_scheme) == 0);
        CHECK(t2_scheme_predicate_count(class_predicate_scheme) == 1);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);
        t2_solver_commit(predicate_solver, class_predicate_scope);

        T2Type predicate_quantified = t2_variable(
                universe,
                T2_VARIABLE_QUANTIFIED,
                9100
        );
        T2Type predicate_identity = t2_function(
                universe,
                &predicate_quantified,
                1,
                predicate_quantified
        );
        T2Predicate scheme_predicate = {
                .kind = T2_PREDICATE_OPERATOR,
                .subtype = predicate_quantified,
                .supertype = predicate_quantified,
                .operand = predicate_quantified,
                .name = "+",
                .provenance = "scheme operator constraint"
        };
        T2Quantifier predicate_quantifier = {
                .id = 9100,
                .kind = T2_VARIABLE_QUANTIFIED
        };
        T2Scheme *predicate_scheme = t2_scheme_new(
                universe,
                &predicate_quantifier,
                1,
                predicate_identity,
                &scheme_predicate,
                1
        );
        CHECK(predicate_scheme != NULL);
        T2Predicate copied_predicate;
        CHECK(t2_scheme_predicate(predicate_scheme, 0, &copied_predicate));
        CHECK(copied_predicate.kind == T2_PREDICATE_OPERATOR);
        CHECK(strcmp(copied_predicate.name, "+") == 0);
        CHECK(strcmp(
                copied_predicate.provenance,
                "scheme operator constraint"
        ) == 0);
        T2Type predicate_use = t2_scheme_instantiate(
                predicate_scheme,
                predicate_solver,
                1,
                "scheme use"
        );
        CHECK(predicate_use != T2_TYPE_INVALID);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 1);
        T2ParameterSpec predicate_parameter;
        CHECK(t2_callable_parameter(
                universe,
                predicate_use,
                0,
                &predicate_parameter
        ));
        t2_scheme_free(predicate_scheme);
        CHECK(t2_solver_constrain_subtype(
                predicate_solver,
                integer,
                predicate_parameter.type,
                "scheme integer argument"
        ) == T2_RELATION_YES);
        CHECK(t2_solver_pending_obligations(predicate_solver) == 0);
        CHECK(predicate_context.calls >= 5);
        t2_scheme_free(predicate_only_scheme);
        t2_scheme_free(class_predicate_scheme);
        t2_solver_free(predicate_solver);

        t2_scheme_free(generalized_scheme);
        t2_scheme_free(projected_scheme);
        t2_scheme_free(scoped_scheme);
        t2_scheme_free(environment_scheme);
        t2_scheme_free(mutable_scheme);
        t2_scheme_free(readonly_scheme);
        t2_scheme_free(weak_scheme);
        t2_solver_free(generalization_solver);

        t2_universe_free(universe);

        if (failures != 0) {
                fprintf(stderr, "%d types2 core check(s) failed\n", failures);
                return 1;
        }

        puts("types2 core: ok");
        return 0;
}
