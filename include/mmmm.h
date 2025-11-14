#include <string.h>
#include <stdint.h>

#include "ty.h"

/* ====================================================================================
 *
 *   memmem() impl. shamelessly stolen from musl
 *
 * ==================================================================================== */
static u8 *twobyte_memmem(const u8 *h, usize k, const u8 *n)
{
	u16 nw = n[0]<<8 | n[1], hw = h[0]<<8 | h[1];
	for (h+=2, k-=2; k; k--, hw = hw<<8 | *h++)
		if (hw == nw) return (u8 *)h-2;
	return hw == nw ? (u8 *)h-2 : 0;
}

static u8 *threebyte_memmem(const u8 *h, usize k, const u8 *n)
{
	u32 nw = (u32)n[0]<<24 | n[1]<<16 | n[2]<<8;
	u32 hw = (u32)h[0]<<24 | h[1]<<16 | h[2]<<8;
	for (h+=3, k-=3; k; k--, hw = (hw|*h++)<<8)
		if (hw == nw) return (u8 *)h-3;
	return hw == nw ? (u8 *)h-3 : 0;
}

static u8 *fourbyte_memmem(const u8 *h, usize k, const u8 *n)
{
	u32 nw = (u32)n[0]<<24 | n[1]<<16 | n[2]<<8 | n[3];
	u32 hw = (u32)h[0]<<24 | h[1]<<16 | h[2]<<8 | h[3];
	for (h+=4, k-=4; k; k--, hw = hw<<8 | *h++)
		if (hw == nw) return (u8 *)h-4;
	return hw == nw ? (u8 *)h-4 : 0;
}

#define MMMM_MAX(a,b) ((a)>(b)?(a):(b))
#define MMMM_MIN(a,b) ((a)<(b)?(a):(b))

#define MMMM_BITOP(a,b,op) \
 ((a)[(usize)(b)/(8*sizeof *(a))] op (usize)1<<((usize)(b)%(8*sizeof *(a))))

static u8 *twoway_memmem(const u8 *h, const u8 *z, const u8 *n, usize l)
{
	usize i, ip, jp, k, p, ms, p0, mem, mem0;
	usize byteset[32 / sizeof(usize)] = { 0 };
	usize shift[256];

	/* Computing length of needle and fill shift table */
	for (i=0; i<l; i++)
		MMMM_BITOP(byteset, n[i], |=), shift[n[i]] = i+1;

	/* Compute maximal suffix */
	ip = -1; jp = 0; k = p = 1;
	while (jp+k<l) {
		if (n[ip+k] == n[jp+k]) {
			if (k == p) {
				jp += p;
				k = 1;
			} else k++;
		} else if (n[ip+k] > n[jp+k]) {
			jp += k;
			k = 1;
			p = jp - ip;
		} else {
			ip = jp++;
			k = p = 1;
		}
	}
	ms = ip;
	p0 = p;

	/* And with the opposite comparison */
	ip = -1; jp = 0; k = p = 1;
	while (jp+k<l) {
		if (n[ip+k] == n[jp+k]) {
			if (k == p) {
				jp += p;
				k = 1;
			} else k++;
		} else if (n[ip+k] < n[jp+k]) {
			jp += k;
			k = 1;
			p = jp - ip;
		} else {
			ip = jp++;
			k = p = 1;
		}
	}
	if (ip+1 > ms+1) ms = ip;
	else p = p0;

	/* Periodic needle? */
	if (memcmp(n, n+p, ms+1)) {
		mem0 = 0;
		p = MMMM_MAX(ms, l-ms-1) + 1;
	} else mem0 = l-p;
	mem = 0;

	/* Search loop */
	for (;;) {
		/* If remainder of haystack is shorter than needle, done */
		if (z-h < l) return 0;

		/* Check last byte first; advance by shift on mismatch */
		if (MMMM_BITOP(byteset, h[l-1], &)) {
			k = l-shift[h[l-1]];
			if (k) {
				if (k < mem) k = mem;
				h += k;
				mem = 0;
				continue;
			}
		} else {
			h += l;
			mem = 0;
			continue;
		}

		/* Compare right half */
		for (k=MMMM_MAX(ms+1,mem); k<l && n[k] == h[k]; k++);
		if (k < l) {
			h += k-ms;
			mem = 0;
			continue;
		}
		/* Compare left half */
		for (k=ms+1; k>mem && n[k-1] == h[k-1]; k--);
		if (k <= mem) return (u8 *)h;
		h += p;
		mem = mem0;
	}
}

inline static void *
mmmm(const void *h0, usize k, const void *n0, usize l)
{
	const u8 *h = h0, *n = n0;

	/* Return immediately on empty needle */
	if (!l) return (void *)h;

	/* Return immediately when needle is longer than haystack */
	if (k<l) return 0;

	/* Use faster algorithms for short needles */
	h = memchr(h0, *n, k);
	if (!h || l==1) return (void *)h;
	k -= h - (const u8 *)h0;
	if (k<l) return 0;
	if (l==2) return twobyte_memmem(h, k, n);
	if (l==3) return threebyte_memmem(h, k, n);
	if (l==4) return fourbyte_memmem(h, k, n);

	return twoway_memmem(h, h+k, n, l);
}

inline static u8 const *
mmmmr(u8 const *haystack, usize hlen, u8 const *needle, usize nlen)
{
        if (nlen == 0)
                return haystack + hlen;

        if (nlen > hlen)
                return NULL;

        u8 const *last = NULL;

        for (u8 const *p = haystack; p <= haystack + hlen - nlen;) {
                u8 const *match = mmmm(p, hlen - (p - haystack), needle, nlen);
                if (match == NULL)
                        break;
                last = match;
                p = match + 1;
        }

        return last;
}
#undef MMMM_MIN
#undef MMMM_MAX
#undef MMMM_BITOP
/* ==================================================================================== */
