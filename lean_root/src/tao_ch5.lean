
import order.bounds
import data.real.basic

-- Consider reworking to be congruent with mathlib's bounds or ereals.
-- https://leanprover-community.github.io/mathlib_docs/order/bounds.html#lower_bounds
def has_infinite_sup (X : set ℝ) : Prop :=
X.nonempty ∧ ¬ (upper_bounds X).nonempty

def has_infinite_inf (X : set ℝ) : Prop :=
X.nonempty ∧ ¬ (lower_bounds X).nonempty

def has_finite_sup (X : set ℝ) : Prop :=
X.nonempty ∧ (upper_bounds X).nonempty

def has_finite_inf (X : set ℝ) : Prop :=
X.nonempty ∧ (lower_bounds X).nonempty

  