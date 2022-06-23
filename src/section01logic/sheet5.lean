/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intros pq,
  rw pq,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intros pq,
  rw pq,
  intros pq,
  rw pq,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros pq qr,
  rw pq,
  exact qr,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  intro pq,
  cases pq with p q,
  split,
  exact q,
  exact p,
  intro qp,
  cases qp with q p,
  split,
  exact p,
  exact q,
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  intros pqr,
  cases pqr with pq r,
  cases pq with p q,
  split,
  exact p,
  split,
  exact q,
  exact r,
  intros pqr,
  cases pqr with p qr,
  cases qr with q r,
  split,
  split,
  exact p,
  exact q,
  exact r,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro p,
  split,
  exact p,
  triv,
  intro pt,
  cases pt with p t,
  exact p,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro f,
  exfalso,
  exact f,
  intro pf,
  cases pf with p f,
  exact f,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros pq rs,
  split,
  rw pq,
  rw rs,
  intro h,
  exact h,
  rw pq,
  rw rs,
  intro h,
  exact h,
end

example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  cases h with h1 h2,
  change P → P → false at h1,
  apply h1,
    apply h2,
    intro p,
    apply h1,
    exact p,
    exact p,

    apply h2,
    intro p,
    apply h1,
    exact p,
    exact p,
end
