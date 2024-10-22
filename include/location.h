#ifndef LOCATION_H_INCLUDED
#define LOCATION_H_INCLUDED

typedef struct location {
        int line;
        int col;
        int byte;
        char const *s;
} Location;

#endif
