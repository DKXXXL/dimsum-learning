#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>


enum {
	MaxGThreads = 4,
	StackSize = 0x400000,
};

struct gt {
	struct gtctx {
		uint64_t rsp;
		uint64_t r15;
		uint64_t r14;
		uint64_t r13;
		uint64_t r12;
		uint64_t rbx;
		uint64_t rbp;
	} ctx;
	enum {
		Unused,
		Running,
		Ready,
	} st;
};

struct gt gttbl[MaxGThreads];
struct gt *gtcur;

void gtinit(void);
void gtret(int ret);
void gtswtch(struct gtctx *old, struct gtctx *new);
bool gtyield(void);
static void gtstop(void);
int gtgo(void (*f)(void));

void
gtinit(void)
{
	gtcur = &gttbl[0];
	gtcur->st = Running;
}

void __attribute__((noreturn))
gtret(int ret)
{
	if (gtcur != &gttbl[0]) {
		gtcur->st = Unused;
		gtyield();
		assert(!"reachable");
	}
	while (gtyield())
		;
	exit(ret);
}

bool
gtyield(void)
{
	struct gt *p;
	struct gtctx *old, *new;

	p = gtcur;
	while (p->st != Ready) {
		if (++p == &gttbl[MaxGThreads])
			p = &gttbl[0];
		if (p == gtcur)
			return false;
	}

	if (gtcur->st != Unused)
		gtcur->st = Ready;
	p->st = Running;
	old = &gtcur->ctx;
	new = &p->ctx;
	gtcur = p;
	gtswtch(old, new);
	return true;
}

static void
gtstop(void) { gtret(0); }

int
gtgo(void (*f)(void))
{
	char *stack;
	struct gt *p;

	for (p = &gttbl[0];; p++)
		if (p == &gttbl[MaxGThreads])
			return -1;
		else if (p->st == Unused)
			break;

	stack = malloc(StackSize);
	if (!stack)
		return -1;

	*(uint64_t *)&stack[StackSize -  8] = (uint64_t)gtstop;
	*(uint64_t *)&stack[StackSize - 16] = (uint64_t)f;
	p->ctx.rsp = (uint64_t)&stack[StackSize - 16];
	p->st = Ready;

	return 0;
}


/* Now, let's run some simple threaded code. */

int yield_val;

int gtyield_with_val(int n) {
  yield_val = n;
  gtyield();
  return yield_val;
}


int int_stream_val = 0;
void int_stream()
{
  int_stream_val++;
  int chk = gtyield_with_val(int_stream_val);
  assert(chk == -1);
  int_stream();
}


int fib_stream_val0 = 1;
int fib_stream_val1 = 1;
void fib_stream()
{
  gtyield_with_val(fib_stream_val0);
  int tmp = fib_stream_val0 + fib_stream_val1;
  fib_stream_val0 = fib_stream_val1;
  fib_stream_val1 = tmp;
  fib_stream();
}


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
fn produce_data() {
    local buffer[100];
    while(true) {
      read = read_data(buffer, 100);
      for(i = 0; i < read; i ++) {
          yield(buffer[i]);
      }
    }
}

fn main1() {
    int cur = 0;
    int n = 0;
    while(true) {
      cur += yield();
      n += 1;
      print(cur / n);
    }
}

fn main2() {
    int cur = 0;
    while(true) {
      new = yield();
      if (new > cur) {
        cur = new;
      }
      print(cur);
    }
}
------------------------------------

fn produce_data() {
    static local buffer[100];
    static local i = 0;
    static local read = 0;    
    if(i == read) { read = read_data(buffer, 100); return produce_data(); }
    else return buffer[i++];
}

fn main1() {
    int cur = 0;
    int n = 0;
    while(true) {
      cur += produce_data();
      n += 1;
      print(cur / n);
    }
}
*/
