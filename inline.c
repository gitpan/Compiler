#include "EXTERN.h"
#include "perl.h"
/* Revolting hack to define inline PP functions */
#undef PP
#define paste(a,b) a ## b
#define PP(s) static __inline__ paste(fast,s)(void)
#include "pp_hot.c"

void foo(void)
{
}
