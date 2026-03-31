# Verified encodings in Coq

This is a replication of the [verified encodings in Lean](../README.md) project, but in Coq instead of Lean. This project tackles a key link in automated reasoning: while SAT solvers are powerful, the process of encoding problems for them is often done by hand and is prone to errors. Our goal is to use the Coq proof assistant to formally verify that these SAT encodings are correct.
> Build the Library: First, we'll develop the basic building blocks in Coq. This means creating formal definitions for SAT formulas and a system to manage the variables that are essential for efficient encodings. 
> Verify the Basics: To ensure the library works, we'll start by verifying a few standard encodings mentioned in the "Verified Encodings for SAT Solvers" paper, like the ones for at-most-one and parity constraints. This will validate our tool. 
> Tackle Advanced Constraints: Going beyond the paper implementation, the main contribution will be extending the library to include general cardinality constraints, pseudo-boolean constraints, and symmetry-breaking predicates.

## Plan

Build the files bottom up following the dependency order. Each file below will be done by each of the team members:

### Phase 1:

> Step 1: Literal.v: Literals 
This is under _src/cnf/literal.lean_. 
Jeannie

> Step 2: Assignment.v: Assignments
This is under _src/cnf/assignment.lean_. 
Tianyi

> Step 3: Clause.v: Clauses
This is under _src/cnf/clause.lean_.
Mehrad

> Step 4: Cnf.v: CNF formulas
This is under _src/cnf/cnf.lean_.
Linxi

> Step 5: Gensym.v: Fresh variable generator
This is under _src/cnf/gensym.lean_.
Manvi

> Step 6: Encoding.v: Encoding 
This is under _src/cnf/encoding.lean_.
Sarah

### Phase 2: Sarah - Tianyi - Mehrad

Here we work on the Parity constraints.

> Step 1: Parity.v: Parity defintion
This is under _src/parity/parity.lean_.

> Step 2: Explode.v: Clause enumeration
This is under _src/parity/explode.lean_.

> Step 3: DirectParity.v: Direct parity encoding
This is under _src/parity/direct\_parity.lean_.

> Step 4: RecursiveParity.v: Recursive parity encoding
This is under _src/parity/recursive\_parity.lean_.

### Phase 3: Jeannie - Manvi - Linxi - Mehrad

We work on the cardinality constraints.

> Step 1: Amk.v: At most k constraint
_src/cardinality/amk.lean_.

> Step 2: Alk.v: At least k constraint
_src/cardinality/alk.lean_.

> Step 3: ScAmk.v: Sequential counter at most K
_src/cardinality/sc\_amk.lean_

> Step 4: DirectAmo.v: Direct at most one constraint
_src/cardinality/direct\_amo.lean_.

> Step 5: Distinct.v: Helper
_src/cardinality/distinct.lean_.

> Step 6: ScAmo.v: Sequential counter at most one
_src/cardinality/sc\_amo.lean_.

Deadline: 31st of march 5 PM. 4 weeks.

## Building

Prerequisites: Coq 8.20.0 (install via `opam install coq.8.20.0`)

```bash
cd coq
make clean   # optional, removes build artifacts
make         # generates Makefile.coq from _CoqProject, then compiles all .v files
```

This compiles all files in dependency order as specified in `_CoqProject`. If compilation succeeds with no errors, all definitions type-check and all proofs are verified.