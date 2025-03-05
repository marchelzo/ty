#ifndef TYPES_H_INCLUDED
#define TYPES_H_INCLUDED

#include "ty.h"

typedef struct type Type;
struct type {
        enum {
                TYPE_CLASS, // e.g. RegexMatch
                TYPE_APP,   // e.g. Array[String]
                TYPE_UNION  // e.g. Int | (Int, Int)
        } type;
        bool fixed;
        union {
                int class;
                struct {
                        /*
                         * TYPE_CLASS[CLASS_FUNCTION]: types[0]=return type, types[1..]=argument types
                         * TYPE_CLASS[CLASS_TUPLE]   : types[0..]=element types
                         * TYPE_APP                  : types[0]=generic type, types[1..]=type arguments
                         * TYPE_UNION                : types[0..]=union elements
                         */
                        vec(Type *) types;
                        StringVector names; // Only for tuples with named entries
                };
        };
};

#endif

/* vim: set sts=8 sw=8 expandtab: */
