# TODOs

Cleanup:
- [ ] cleanup imports
- [ ] cleanup base.v
- [ ] update deps (Iris, Coq, ...)
  - [ ] use gset in definition of heap_state
- [ ] cleanup axioms
- [ ] change folder structure
- [ ] make combinators define mod_state instead of initial state
- [ ] clean up disabled in _CoqProject
- [ ] Rename mod_state? Rename module?

Optional:
- [ ] Add ghost state for f2i and add values of f2i to initial ownership (one persistent map)
- [ ] Add fnptrs to imp (should be easy when one has ghost state for f2i)
- [ ] Make receiving calls for non-existent functions / instructions UB instead of NB
  - Turn UbE into AssertE (P : bool) (e : expr)
- [ ] Add global variables
- [ ] Additional optimizations
- [ ] Remove the disjointness condition on asm and imp linking to the
      condition that the instructions agree on overlapping
      instructions and replace the choice of the side by an angelic
      choice. This should work with the following changes:
      - Allow asm modules to receive all jump events but raise UB if
        there is no matching instructions.
      - When fetching a new instruction, do an angelic choice whether
        to emit an event or whether to fetch the next instruction.
- [ ] example for mmap
  - [ ] Add mmap and munmap syscalls to asm
  - [ ] Give spec for mmap at the C-level
  - [ ] Verify an example using it



Done:
- [X] green-threading example
- [X] new example from key idea section
- [X] clean up mem2reg and integrate it into the compiler
- [X] make regs total by using !!! and get rid of pc in EJump
- [X] prove vertical compositionality
  - Plan A: prove vertical compositionality directly on ownership based prepost
    - [ ] Add [∗ map] ps\mapsto pi \in hb_shared bij, shared ps pi to
          invariant of heap_bij. This ensures that all shared locations are shared persistently.
    - [ ] Use invariant when proving vertical compositionality:
          Additional locations we own in the spec + locations we own
          in the target cover all private locations. This means that
          we can replay all modifications that the env does in the
          source in the target because we own all locations that the
          env could modify in the source and vice versa. Might need
          some additional trickery for i2a (maybe subtract all
          addresses that correspond to shared locations?)
  - [ ] Prove vertical compositionality of pure_i2a.imp_to_asm and
        pure_bij.heap_bij
    - Should be easier than vertical compositionality for heap_bij since
      e.g. we don't need heap_in_bij for middle module to outside
    - [ ] Define pure_i2a.imp_to_asm
    - [ ] Prove equivalence of pure_i2a.imp_to_asm and imp_to_asm
    - [ ] Prove equivalence of pure_bij.heap_bij and heap_bij
- [X] Verify optimization that turns local variables into let-bindings
- [X] Make accesses to unmapped memory emit events
- [X] Allow multiple stacks
  - [X] Allow i2a emit page faults for the stack page
  - [X] Adjust compiler to do probing (at the beginning before any
        allocation by just overapproximating the stack size)
- [X] Make allocation in Imp like RefinedC allocation
- [X] Add system calls to asm
- [X] Generalize imp_prepost for arbitrary imp_event modules on both sides (without prepost)
- [X] Prove imp_to_asm refinement for integer pointer casting module
  - at the imp level, the integer pointer casting can be represented
    by an itree with state gmap prov Z which universally chooses which
    provenance to return
- [X] Verify imp code that links with spec of integer pointer casting.
  - Maybe let x := Alloc 1 in x ← 1; let y = int_to_ptr(ptr_to_int(x)) in let r := !y in Free(y); Return r
    - refines Return 1
- [X] Compiler

Postponed:
- [ ] Allow the proof to use a bigger resource than the prepost, e.g.
      by defining an injection from the prepost resource to the bigger resource
  - [ ] Use this to define ownership of registers for compiler codegen pass
- [ ] Add framework for combining compiler passes
- [ ] Make mod_seq_map only emit events when the inner module accepted them
  - Tricky because the two events are not linked. Maybe it is not
    necessary? With the current asm_closed it seems so since the env
    can cause syscallrets at bad times but this would just cause UB.
    Maybe bad events by the env should be UB instead of NB in general?
    (e.g. in None state of asm allow Syscall events, but make them UB?
    Does it matter?) Or maybe one should add a predicate to
    mod_prepost to rule out non-sensical events from the env?

# Notes

module : state transition system

refines : module → module → Prop

Which refinements should hold and which should not hold?

Properties of silent steps:

      A           B                       A     B
0. 1 --- 2 --- 3 --- 4  equivalent to  1 --- 2 --- 3

  A(); B(1 + 1);  equivalent to  A(); B(2);

Properties of NB:

NB means that the program does not have any further behavior.
It can be seen a termination, but in an actual programming language,
termination probably should also emit a visible event. So here we exploit
that diverging is not observable (since we only consider safety) and
use a diverging loop [while(true);] to model NB.

      A                 A     B
1. 1 --- 2  refines  1 --- 2 --- 3

  A(); while(true);  refines  A(); B();

      A     B                     A
2. 1 --- 2 --- 3  not refines  1 --- 2

  A(); B();  not refines  A(); while(true);


3. ∀ m, 1 --- 2  refines  m

  ∀ m, while(true);  refines  m

  -> NB is the bottom element of the refinement lattice
  -> NB is similar to False

         /--\
4. 1 --- 2  |  equivalent to 1 --- 2
         \--/
  -> we only consider safety properties so infinite loops are equivalent to NB

Properties of UB:

UB means that the program executes an action that it should not execute. We model
it in the pseudo code with dereferencing a NULL pointer [*NULL].

      A     B                 A
5. 1 --- 2 --- 3  refines  1 --- 2 -UB

  A(); B();  refines  A(); *NULL;

      A                         A     B
6. 1 --- 2 -UB  not refines  1 --- 2 --- 3

  A(); *NULL;  not refines  A(); B();

7. ∀ m, m  refines 1 -UB

  ∀ m, m refines  *NULL;

  -> UB is the top element of the refinement lattice
  -> UB is similar to True


Properties of ∃ exists choice: (choose in CCR)

∃ choice allows to perform a choice when constructing a trace.
It occurs e.g. when choosing the address or provenance of an allocation.
Thus, here we use [x = malloc(n);] as an example for ∃-choice.

(Memory model: Locations are pairs of provenances and addresses, memory is a map
from addresses to provenances and values and accesses a memory location checks that
the provenance of the location corresponds to the provenance of the memory, UB
otherwise)

                               A
      A                  /- 2 --- 3
8. 1 --- 2  refines  1 -∃
                         \- 4 --- 5
                               B

  x = alloc_at(10, n); f(x);  refines  x = malloc(n); f(x)
    (where alloc_at also takes the concrete address as argument)
  or
  x = malloc(n + n); y = x + n; f(x, y);  refines  x = malloc(n); y = malloc(n); f(x, y);

  -> Similar to A → A ∨ B

                               A
      B                  /- 2 --- 3
9. 1 --- 2  refines  1 -∃
                         \- 4 --- 5
                               B

  (example same as above)

  -> Similar to B → A ∨ B

                                   A
       C                     /- 2 --- 3
10. 1 --- 2  not refines  1 -∃
                             \- 4 --- 5
                                   B

  g();   not refines   x = malloc(n); f(x);

              A
        /- 2 --- 3                   A
11. 1 -∃            equivalent to 1 --- 2
        \- 4 --- 5
              A

  malloc(n); f();  equivalent to  f();

  -> Similar to A ∨ A ↔ A

              A
        /- 2 --- 3                   A
12. 1 -∃            equivalent to 1 --- 2
        \- 4

  x = malloc(n); while((int) n >= 2 ^ 64); equivalent to  x = malloc_64bit(n)
    (where malloc_64bit only returns 64bit addresses)

  -> right to left follows from 8.
  -> left to right follows from 3 in the second branch and then 11
  -> similar to False ∨ A ↔ A


              A
        /- 2 --- 3
13. 1 -∃            equivalent to 1 -UB
        \- 4 -UB

  (This is used to justify guessing addresses based on allocator non-determinism.)

  -> right to left follows from 9.
  -> left to right follows from 7.
  -> similar to True ∨ A ↔ True

Properties of ∀ forall choice: (take in CCR)

∀ choice gives us the value of the choice when constructing a trace and
one has to provide it when destructing the trace.
It can be used to model integer to pointer casts where the cast uses angelic
choice to choose the provenance (and the integer for the address).

               A
         /- 2 --- 3              A
14.  1 -∀             refines 1 --- 2
         \- 4 --- 5
               B

  p = (void * ) x; f(p)  refines  p = copy_alloc_id(x, q); f(p);

  -> Similar to A ∧ B → A

               A
         /- 2 --- 3              B
15.  1 -∀             refines 1 --- 2
         \- 4 --- 5
               B

  p = (void * ) x; f(p)  refines  p = copy_alloc_id(x, r); f(p);

  -> Similar to A ∧ B → B

               A
         /- 2 --- 3                   C
16.  1 -∀              not refines 1 --- 2
         \- 4 --- 5
               B

  p = (void * ) x; f(p)  not refines  g();

  -> The refinement holds in the underlying refinement of CCR

              A
        /- 2 --- 3                   A
17. 1 -∀            equivalent to 1 --- 2
        \- 4 --- 5
              A

  (void * )n; f();  equivalent to  f();

  -> Similar to A ∧ A ↔ A

              A
        /- 2 --- 3
18. 1 -∀            equivalent to 1 --- 2
        \- 4
  -> left to right follows from 15.
  -> right to left follows from 3.
  -> Similar to False ∧ A ↔ False

                         A
                   /- 2 --- 3                     A                         B
18. m refines  1 -∀             iff  m refines 1 --- 2   and   m refines 1 --- 2
                   \- 4 --- 5
                         B

              A
        /- 2 --- 3                   A
19. 1 -∀            equivalent to 1 --- 2
        \- 4 -UB

  p = (void * ) x; p - q; f(p)  equivalent to   p = copy_alloc_id(x, q); p - q; f(p);
   (p - q has UB if the provanance of p and q differs)

  -> left to right follows from 14.
  -> right to left follows from 7. in the second branch an then 17.
  -> Similar to True ∧ A ↔ A

Commuting ∃ with events:

              A     B                               B
        /- 2 --- 3 --- 4               A      /- 3 --- 4
∃C1 1 -∃                   refines  1 --- 2 -∃
        \- 5 --- 6 --- 7                      \- 5 --- 6
              A     C                               C

   x = malloc(n); p = f(); g(x, p);  refines  p = f(); x = malloc(n); g(x, p);

   This should always hold as one can always use the value of the ∃ in the implementation
   to instantiate the ∃ choice in the spec.

                     B                       A     B
        A      /- 3 --- 4              /- 2 --- 3 --- 4
∃C2  1 --- 2 -∃            refines  1 -∃
               \- 5 --- 6              \- 5 --- 6 --- 7
                     C                       A     C

   p = f(); x = malloc(n); (uintptr_t)x; g(x, p);
     refines
   x = malloc(n); (uintptr_t)x; p = f(); g(x, p);

   Should this hold?
   - What if f is some external call outside of C?
   - What if f := return (void * )a; and g(x, p) := x - p?
       Then there is UB in the implementation (by picking the provenance of
       x to be different than p), but not in the spec (p can have the same provanance as x)!

main1:
  p = f(); x = malloc(n); g(x, p);

  inlined:
    p = (void * )a; x = malloc(n); assert_same_provenance(x, p)


main2:
  x = malloc(n); p = f(); g(x, p);

  inlined:
    x = malloc(n); p = (void * )a; assert_same_provenance(x, p)

f():
  return (void * )a

g(x, p):
  assert_same_provenance(x, p)


main1 + f + g  not refines main2 + f + g

m1 refines m1' →
m2 refines m2' →
m1 + m2 refines m1' + m2'

main1  refines  main2


module[P1 ∪ P2]  equivalent to  module[P1] + module[P2]

-----------------------------
module[C]  refines  module[C]        module[P1]  refines  module[P2]
-----------------------------       --------------------------------
∀ C, module[C] + module[P1]  refines  module[C] + module[P2]
------------------------------------------------------------
∀ C, module[C ∪ P1]  refines  module[C ∪ P2]
-----------------------------------------------
∀ C, C ∪ P1  language-refines  C ∪ P2

main1 + f + g  not refines main2 + f + g


m1 refines m1' →
m2 refines m2' →
m1 + m2 refines m1' + m2'

main1  not refines  main2


Commuting ∀ with events:

                     B                       A     B
        A      /- 3 --- 4              /- 2 --- 3 --- 4
∀C2  1 --- 2 -∀            refines  1 -∀
               \- 5 --- 6              \- 5 --- 6 --- 7
                     C                       A     C

   p = f(); x = (void * )n; g(x, p);   refines  x = (void * )n; p = f(); g(x, p);

   This should always hold as one can use the ∀ choice from the spec to instantiate
   the ∀ choice in the implementation.

              A     B                               B
        /- 2 --- 3 --- 4               A      /- 3 --- 4
∀C1 1 -∀                   refines  1 --- 2 -∀
        \- 5 --- 6 --- 7                      \- 5 --- 6
              A     C                               C

   x = (void * )n; p = f(); g(x, p);  refines  p = f(); x = (void * )n; g(x, p);

   Should this hold?
   - What if f is some external call outside of C?
   - What if f := return malloc(a); and g(x, p) := x - p?
       Then there is UB in the implementation, but not in the spec! (see above)


# Random other notes

(* TODO: for angelic version, list EV must become propset (list EV).
It must also be precise, i.e. TraceEnd must enforce T ≡ {[ [] ]}. For
TraceStep, one can probably use T ≡ (option_list κ ++.) <$> T' and add T' ≡ ({[ κs |
(∃ σ, Pσ σ ∧ κs ∈ fT σ)]}) inside the ∀ σ. Otherwise one could also
explicitly handle the UB on the outside (T' should be unconstrained if there is UB)
 The next steps use [fT σ] as
their set. This also requires the set of next states to be precise.
One can try if the version is sensible by proving for

  A
  /- 1 -- UB
 /
0
 \
  \- 2
  B

That
0 ~{ m, T }~> _, True
→ (∃ κs, B::κs ∈ T) → T ≡ {[ [B] ]}

But one also needs to require that the trace of the spec is a subset of the trace of the source. Not sure how to best handle UB. Maybe the subset must not be empty? One must be careful that one cannot commute UB with external events, i.e. representing UB as the empty set of traces does not seem to work (but it would be very elegant otherwise). Or do something like the following?

Set Printing Universes.
(* Set Universe Polymorphism. *)
Inductive trace (EV : Type) : Type :=
| TEnd : trace EV
| TCons (κ : EV) (κs : trace EV) : trace EV
| TChoice (T : Type): (T → Prop) → (T → trace EV) → trace EV
.

Fixpoint trace_sub {EV} (κs1 κs2 : trace EV) : Prop :=
  match κs1, κs2 with
  | _, TChoice _ T P κs2' => ∀ x : T, P x → trace_sub κs1 (κs2' x)
  | TChoice _ T P κs1', _ => ∃ x : T, P x ∧ trace_sub (κs1' x) κs2
  | TCons _ κ1 κs1', TCons _ κ2 κs2' => κ1 = κ2 ∧ trace_sub κs1' κs2'
  | TEnd _, TEnd _ => True
  | TEnd _, TCons _ _ _ => False
  | TCons _ _ _, TEnd _ => False
  end.

The above seems tricky to work with and may not allow commuting angelic non-det in both directions.

Other idea: Do what was said in the first version above, but ensure that
the arbitrary trace from UB is non-empty. This ensures that the trace set never becomes empty
and that hopefully solves the UB commuting problem.

    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → has_trace m σ2 Pκs2 Pσ3) →
    Pκs ≡ (option_list (Vis <$> κ) ++.) <$> Pκs1 →
    ((∃ σ, Pσ2 σ ∧ Pκs1 ≡ (∃ σ, Pσ2 σ ∧ κs ∈ Pκs2 σ))
     ∨ (¬ (∃ σ, Pσ2 σ) ∧ ∃ κs, κs ∈ Pκs1)
    has_trace m σ1 Pκs Pσ3

Refinement would be defined as:
∀ κs, mimpl.(ms_state) ~{ mimpl, Pκi }~> (λ _, True) → ∃ Pκs, Pκs ⊆ Pκi ∧ mspec.(ms_state) ~{ mspec, Pκs }~> (λ _, True)

Safety would be defined as follows and should be transferred by refinement:
Definition safe {EV} (m : mod_state EV) (P : list (event EV) → Prop) :=
  ∀ Pκs, m.(ms_state) ~{ m, Pκs }~> (λ _, True) → ∃ κs, κs ∈ Pκs ∧ P κs.

Or even Pκs should not be precise, i.e.

    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → has_trace m σ2 (λ κs, Pκs (option_list (Vis <$> κ) ++ κs)) Pσ3) →
    Pκs κs →
    has_trace m σ1 Pκs Pσ3

This means that Refinement can be defined as
∀ Pκs, mimpl.(ms_state) ~{ mimpl, Pκs }~> (λ _, True) → mspec.(ms_state) ~{ mspec, Pκs }~> (λ _, True)

And safety as:
Definition safe {EV} (m : mod_state EV) (P : (list (event EV) → Prop) → Prop) :=
  ∀ Pκs, m.(ms_state) ~{ m, Pκs }~> (λ _, True) → P Pκs.

The key observation is that this definition of has_trace already builds in that a target
can have more angelic behavior as the spec and one can only prove safe for properties that
are closed under expansion to bigger sets. E.g. properties of the form P Pκs := ∃ κ, Pκs ∧ (...) work,
but something with P Pκs := (∀ κs, Pκs κs → ...) does not work. This is feature, not a bug
since such properties are not preserved by refinement anyway.
*)

(* Defining traces using (list (event EV) → Prop) has one big problem:
With this definition angelic choice commutes with visible events and
this causes a few problems. One problem for [mod_filter] is explained
below, but there is a worse problem: horizontal compositionality does
not hold! In short, the problem is that when linking two modules, one
can depend on the angelic choices of the other (this is an important
feature), but refinement can move the angelic choices such that the
spec cannot emulate the same dependency that the implementation had.

Consider the following programs:

MI1:
                S           A
    /- 2 true  --- 3 true  ---
1 -∀
    \- 2 false --- 3 false ---
                S           B

MS1:                        A
         S      /- 4 true  ---
1 --- 2 --- 3 -∀
                \- 4 false ---
                            B

M2:
                S           A
    /- 2 true  --- 3 true  ---
1 -∃
    \- 2 false --- 3 false ---
                S           B

We have MI1 ⊑ MS1, but link MI1 M2 ⊑ link MS1 M2 does not hold!
In particular, link MI1 M2 has the trace
 [(S, S); (A, A)] ∨ [(S, S); (B, B)]
(because the demonic choice in M2 can use the value of the angelic choice of MI1)
but link MS1 M2 does not have this trace since there one has to pick the
value of the demonic choice in M2 before one sees the angelic choice.

 *)

(*
With
    m.(m_step) σ1 Pσ2 →
    (∀ σ2 κ, Pσ2 σ2 κ → has_trace m σ2 (λ κs, Pκs (option_list κ ++ κs)) Pσ3) →

UB commutes with externally visible events, which is bad (or is it?)
Maybe one can work around it by inserting an angelic choice whether to continue the
execution or go to a NB state after each event that should not commute with UB?
This would be a finite angelic choice and thus be not so bad.
*)


(* [trefines m1 m2 ↔ dem_refines m1 m2] cannot hold anymore since we made the
environment more powerful and it can now react to the choices of the module.

Consider the following (demonic) module:
         B
   A     /- 3
1 --- 2 -
         \- 4
         C

It currently refines:
   A      B
   /- 2' --- 3
1 -
   \- 2  --- 4
   A      C

But when cast to an angelic module, the original module
accepts the trace
[tcons A (tall bool (λ b, if b then tcons B nil else tcons C nil))]
But the second does not!

So it seems like one needs to loose a commuting rule of non-det choice. With
angelic choice in the environment, one can now observe the difference between these
two modules. Not sure if this is bad or good.


The problem of adding tall to dem module is that when instantiating Iris, one
cannot use nat as the step index as has_trace might contain infinite branching.
Two solutions:
1. Use Transfinite Iris
2. Restrict all angelic choices everywhere to be finite.
  - This might be the way to go for a first try as most of the examples
    that I can think of so far only rely on finite angelic non-det (e.g.
    choosing a provenance should only need to choose an existing provenance
    I hope). But I am still afraid that this will blow up in our face somewhen.
3. Don't use step-indexing
 *)


(*
TODO: next steps:
- Add sequential product
- Add stateful filter
- Add product that only executes one side and non-determinisitically switches between the two (with an explicit event)
  - This might be more general than the current product as one might be able to get the current one by hiding the switching events?!
    - For (Some _, Some _) events one might need the stateful filter
*)
