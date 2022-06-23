/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intros pq,
  cases pq,
  exact pq_left,
end

example : P ∧ Q → Q :=
begin
  intros pq,
  cases pq,
  exact pq_right,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros pqr p_q,
  cases p_q with p q,
  apply pqr,
  exact p,
  exact q,
end

example : P → Q → P ∧ Q :=
begin
  intros p q,
  split,
  exact p,
  exact q,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intros h,
  cases h with p q,
  split,
  exact q,
  exact p,
end

example : P → P ∧ true :=
begin
  intros p,
  split,
  exact p,
  triv,
end

example : false → P ∧ false :=
begin
  intros f,
  split,
  exfalso,
  exact f,
  exact f,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros pq qr,
  cases pq with p q,
  cases qr with q r,
  split,
  exact p,
  exact r,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros pqr p q,
  apply pqr,
  split,
  exact p,
  exact q,
end



