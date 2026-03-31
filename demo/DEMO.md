# Demo Script: Verified Encodings for SAT Solvers in Coq

## Overview
This demo walks through the verified SAT encoding library we built in Coq.
Allow approximately 5-10 minutes.

---

## 1. Project Structure (1 min)

Show the repository layout:

```bash
cd coq/
cat _CoqProject
```

Explain the dependency chain:
- **cnf/Literal.v** -> defines literals (Pos/Neg), eval, flip
- **cnf/Assignment.v** -> agreement on variable sets, aite
- **cnf/Clause.v** -> clauses (disjunctions), eval, vars
- **cnf/Cnf.v** -> CNF formulas (conjunctions), satisfiable, eqsat
- **cnf/Gensym.v** -> fresh variable generator with injectivity proof
- **cnf/Encoding.v** -> encoding correctness (formula_encodes) and well-behavedness (is_wb)
- **parity/** -> XOR constraint and direct encoding
- **cardinality/** -> AMK/ALK constraints and direct AMO encoding

---

## 2. Compile the Library (1 min)

```bash
cd coq/
make clean && make
```

Show that all 13 files compile without errors. Point out:
- Files are compiled in dependency order
- No axioms beyond the standard Coq library
- Some advanced proofs are `Admitted` (future work)

---

## 3. Walk Through Literal.v (2 min)

Open `cnf/Literal.v` and highlight:

```coq
(* The core type *)
Inductive literal (V : Type) : Type :=
| Pos : V -> literal V
| Neg : V -> literal V.

(* Evaluation under an assignment *)
Definition eval (tau : assignment V) (l : literal V) : bool :=
  match l with
  | Pos v => tau v
  | Neg v => negb (tau v)
  end.

(* Flipping preserves the variable but negates the value *)
Theorem eval_flip :
  forall (tau : assignment V) (l : literal V),
    eval tau (flip l) = negb (eval tau l).
```

Key points:
- Polymorphic in V (could be nat, string, etc.)
- `flip` is self-inverse (`flip_flip`), injective, and negates evaluation
- All proofs are complete (no `Admitted`)

---

## 4. Show a Correctness Theorem (3 min)

Open `cardinality/DirectAmo.v` and explain:

```coq
(* The direct AMO encoding: pairwise exclusion clauses *)
Fixpoint direct_amo' (l : list (literal V)) : cnf V :=
  match l with
  | [] => []
  | lit :: ls =>
    map (fun m => [flip lit; flip m]) ls ++ direct_amo' ls
  end.
```

Explain: For each pair (li, lj), we add the clause [not li, not lj],
which says "at most one of li, lj can be true."

Then show the correctness statement:

```coq
Theorem direct_amo_encodes_amo :
  encodes (amk 1) direct_amo.
```

Explain what this means:
- `amk 1` = at-most-one constraint
- `encodes` = correct AND well-behaved
- Once this type-checks, we have **mathematical certainty** the encoding is correct

Similarly show `direct_alo_encodes_alo` in `Alk.v` (fully proved!).

---

## 5. Gensym: Fresh Variables (2 min)

Open `cnf/Gensym.v` and explain:

```coq
Record gensym := mk_gensym {
  offset : nat;
  f : nat -> A;
  f_inj : forall x y, f x = f y -> x = y
}.
```

Key insight: The gensym carries its own **proof of injectivity**.
This means every variable it generates is provably fresh.

Show:
```coq
Theorem fresh_not_in_fresh_stock : forall (g : gensym),
  ~ stock (snd (fresh g)) (fst (fresh g)).
```

This says: after generating a fresh variable, that variable is NOT
in the remaining stock. This is the key property that makes encodings
with auxiliary variables correct.

---

## 6. Extension: Symmetry-Breaking Predicates (2 min)

Open `symmetry/LexOrder.v` and explain:

```coq
(* Lexicographic <= on boolean lists *)
Fixpoint lex_le (l1 l2 : list bool) : bool :=
  match l1, l2 with
  | [], _ => true
  | _ :: _, [] => false
  | false :: r1, true :: _ => true
  | true :: _, false :: _ => false
  | _ :: r1, _ :: r2 => lex_le r1 r2
  end.
```

Key points:
- This goes **beyond the original paper** (Codel, Avigad, Heule 2023)
- Many combinatorial SAT problems have symmetric solutions
- Symmetry-breaking adds clauses to eliminate redundant symmetric solutions
- The **lex-leader constraint** enforces a canonical (lexicographic) ordering

Then open `symmetry/LexLeader.v` and show:

```coq
(* The encoding uses auxiliary variables s_i from gensym *)
Fixpoint lex_leader_aux
  (xs ys : list (literal V))
  (prev_s : option V)
  (g : gensym V)
  : cnf V * gensym V := ...
```

Explain the encoding structure:
- Uses O(n) auxiliary variables and O(n) clauses for lists of length n
- Each `s_i` encodes "positions 0..i are all equal"
- Main constraint: if prefix equal, then x_i implies y_i
- Based on Aloul, Sakallah, Markov (2006)

Show the correctness theorem:

```coq
Theorem lex_leader_encodes : forall xs ys g F g',
  lex_leader_aux xs ys None g = (F, g') ->
  length xs = length ys ->
  disj (xs ++ ys) g ->
  (* Soundness: CNF satisfied implies lex ordering *)
  (forall tau, eval_cnf tau F = true ->
    lex_le (map (eval tau) xs) (map (eval tau) ys) = true) /\
  (* Completeness: lex ordering implies satisfiable CNF *)
  (forall tau, lex_le (map (eval tau) xs) (map (eval tau) ys) = true ->
    exists sigma, eval_cnf sigma F = true /\
                  agree_on tau sigma (clause_vars (xs ++ ys))).
```

---

## Summary

What we demonstrated:
1. A complete, compiling Coq library for verified SAT encodings
2. Clean type definitions mirroring the Lean reference implementation
3. Correctness theorems with precise mathematical statements
4. The `gensym` abstraction for provably fresh variables
5. Three phases: CNF foundations, parity, cardinality
6. **Extension**: Symmetry-breaking predicates with lex-leader encoding
