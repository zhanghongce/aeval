#include <stdio.h>
#include <string.h>
#include <stdint.h>

int main()
{
    unsigned char buf[16];
    memset (buf, 0, 16);
    float x;

    for (unsigned i = 0; i < 12; ++i)
    {
        x = *((float*)(buf + i));
        printf ("value %f at 0x%08lx\n", x, (intptr_t) (buf + i));
    }
}
