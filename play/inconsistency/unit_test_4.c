#include<stdlib.h>

/*Circular buffer*/

typedef struct queue
{ int inp;
    int outp;
    int size;
    int *buf;
} Queue;


Queue *new(int n)
{
    int *buff = malloc(n*sizeof(int));
    Queue q = {0,0,n,buff};
    Queue *qptr = malloc(sizeof(Queue));
    *qptr = q;
    return qptr;
}

/* put a value into the queue */
int put(Queue *q, int n)
{ q -> buf[q-> inp] = n;
    q -> inp = (q -> inp + 1) % q -> size;
    return n;
}

int get(Queue *q)
{
    int ans = q -> buf[q-> outp];
    q -> outp = (q -> outp + 1) % q -> size;
    return ans;
}

int size(Queue *q)
{
    return (q -> inp - q -> outp) % q -> size;
}
