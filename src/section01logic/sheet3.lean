/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intros nt,
  change true → false at nt,
  apply nt,
  triv,
end

example : false → ¬ true :=
begin
  intros f,
  change true → false,
  intros t,
  exact f,
end

example : ¬ false → true :=
begin
  intros nf,
  triv,
end

example : true → ¬ false :=
begin
  intros t,
  change false → false,
  intros f,
  exact f,
end

example : false → ¬ P :=
begin
  intros f,
  change P → false,
  intros p,
  exact f,
end

example : P → ¬ P → false :=
begin
  intros p np,
  change P → false at np,
  apply np,
  apply p,
end

example : P → ¬ (¬ P) :=
begin
  intros p,
  change ¬ P → false,
  intros np,
  apply np,
  apply p,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros pq nq p,
  change Q → false at nq,
  apply nq,
  apply pq,
  exact p,
end

example : ¬ ¬ false → false :=
begin
  intros nn,
  change ¬ false → false at nn,
  apply nn,
  intros f,
  exact f,
end

example : ¬ ¬ P → P :=
begin
  intros nn,
  change ¬ P → false at nn,
  by_contra,
  apply nn,
  exact h,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros h p,
  by_cases hq : Q,
  exact hq,
  exfalso,
  apply h,
  exact hq,
  exact p,
end