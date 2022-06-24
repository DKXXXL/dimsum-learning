#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define StackSize 0x400000

struct gt {
	uint64_t rsp;
	uint64_t r15;
	uint64_t r14;
	uint64_t r13;
	uint64_t r12;
	uint64_t rbx;
	uint64_t rbp;
};

struct gt gttbl[2];
char stack[StackSize];
int gtcur = 0;

void gtswtch(struct gt *old, struct gt *new);
void gtyield(void);
/* static void gtstop(void); */
int gtgo(void (*f)(void));

void gtyield(void)
{
	struct gt *old, *new;

	old = &gttbl[gtcur];
        gtcur = (gtcur+1)%2; // rand()%2;
	new = &gttbl[gtcur];
	gtswtch(old, new);
}

/* static void */
/* gtstop(void) { assert(false); /\* unreachable *\/ } */

int
gtgo(void (*f)(void))
{
	struct gt *p;

        p = &gttbl[1];

	/* *(uint64_t *)&stack[StackSize -  8] = (uint64_t)gtstop; */
	*(uint64_t *)&stack[StackSize - 16] = (uint64_t)f;
	p->rsp = (uint64_t)&stack[StackSize - 16];

	return 0;
}

/************************************************************************************/

int yield_val;

int gtyield_with_val(int n) {
  yield_val = n;
  gtyield();
  return yield_val;
}

/************************************************************************************/

void int_stream_inner(int n) {
  gtyield_with_val(n);
  int_stream_inner(n+1);
}

void int_stream()
{
  int_stream_inner(0);
}

int main(void)
{
  gtgo(int_stream);
  /* gtgo(fib_stream); */
  for(int i=0; i<5; i++) {
    int v = gtyield_with_val(-1);
    printf("v is : %d\n", v);
  }
}

/*
void f() {
  while(true) {
    printf("A\n");
    gtyield();
  }
}

int main() {
  gtgo(f);
  while(true) {
    printf("B\n");
    gtyield();
  }
  return 0;
}
*/