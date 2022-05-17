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
int gtcur;

void gtinit(void);
void gtswtch(struct gt *old, struct gt *new);
bool gtyield(void);
/* static void gtstop(void); */
int gtgo(void (*f)(void));

void
gtinit(void)
{
	gtcur = 0;
}

bool
gtyield(void)
{
	struct gt *old, *new;

	old = &gttbl[gtcur];
        gtcur = (gtcur+1)%2; // rand()%2;
	new = &gttbl[gtcur];
	gtswtch(old, new);
	return true;
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

int int_stream_val = 0;
void int_stream()
{
  int_stream_val++;
  int chk = gtyield_with_val(int_stream_val);
  assert(chk == -1);
  int_stream();
}


/* int fib_stream_val0 = 1; */
/* int fib_stream_val1 = 1; */
/* void fib_stream() */
/* { */
/*   gtyield_with_val(fib_stream_val0); */
/*   int tmp = fib_stream_val0 + fib_stream_val1; */
/*   fib_stream_val0 = fib_stream_val1; */
/*   fib_stream_val1 = tmp; */
/*   fib_stream(); */
/* } */

int main(void)
{
  gtinit();
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
  gtinit();
  gtgo(f);
  while(true) {
    printf("B\n");
    gtyield();
  }
  return 0;
}
*/
