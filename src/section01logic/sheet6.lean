/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intros p,
  left,
  exact p,
end

example : Q → P ∨ Q :=
begin
  intros q,
  right,
  exact q,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros pq pr qr,
  cases pq,
  apply pr,
  exact pq,
  apply qr,
  exact pq,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intros pq,
  cases pq,
  right,
  exact pq,
  left,
  exact pq,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
    intro pqr,
    cases pqr,
    cases pqr,
    left,
    exact pqr,
    right,
    left,
    exact pqr,
    right,
    right,
    exact pqr,

    intros pqr,
    cases pqr,
    left,
    left,
    exact pqr,
    cases pqr,
    left,
    right,
    exact pqr,
    right,
    exact pqr
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros pr qs pq,
  cases pq,
  left,
  apply pr,
  exact pq,
  right,
  apply qs,
  exact pq,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros pq pr,
  cases pr,
  left,
  apply pq,
  exact pr,
  right,
  exact pr,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros pr qs,
  rw pr,
  rw qs,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,

  intros h,
  change P ∨ Q → false at h,
  split,
  intro p,
  apply h,
  left,
  exact p,
  intro q,
  apply h,
  right,
  exact q,

  intros h,
  change P ∨ Q → false,
  intros nh,
  cases h with np nq,
  cases nh,
  apply np,
  exact nh,
  apply nq,
  exact nh,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
    intro h,
    change P ∧ Q → false at h,
    by_cases p : P,
    right,
    intro q,
    apply h,
    split,
    exact p,
    exact q,
    left,
    exact p,

    intro h,
    change P ∧ Q → false,
    intro pq,
    cases h,
    apply h,
    cases pq with p q,
    exact p,
    apply h,
    cases pq with p q,
    exact q,
end
