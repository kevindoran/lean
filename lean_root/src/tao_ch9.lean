/-
Notes
-----
A set seems to be the lambda λα : Type → Prop
`mem` takes a set and another input and simply applies the set to the other.

    protected def mem (a : α) (s : set α) :=
    s a

∈ is defined in library/init.core.lean.

    infix ∈     := has_mem.mem

with has_mem.mem having the definition:

    class has_mem (α : out_param $ Type u) (y : Type v) := (mem : α→y→Prop)


$ usage. Quoted from "Programming in Lean":
    Note the use of the dollar-sign for function application. In general,
    an expression f $ a denotes nothing more than f a, but the binding strength
    is such that you do not need to use extra parentheses when a is a long
    expression. This provides a convenient idiom in situations exactly like
    the one in the example.

The statement: 
  ∃x ∈ X
is shorthand for:
  ∃ (x : _) (h : x ∈ X)
which is shorthand for:
  ∃ (x : _), ∃ (h : x ∈ X),
-/


/- 
Contents and exercises for Chapter 9 of Tao's Analysis.
-/
-- We want real numbers and their basic properties
import data.real.basic
import data.set
import logic.basic

import tao_ch5

set_option pp.implicit true
-- Make simp display the steps used.  
set_option trace.simplify.rewrite true

-- We want to be able to define functions using the law of excluded middle
noncomputable theory
open_locale classical

-- Use a namespace so that we can copy some of the matlib naming. 
namespace tao_analysis

-- Notation for absolute. Is this in Lean somewhere?
local notation `|`x`|` := abs x


/- Section 9.1
Many of these results can be found in matlib. For example, definitions and
properties of closures can be found here:
https://leanprover-community.github.io/mathlib_docs/topology/basic.html
-/

/- Definition 9.1.1 (Intervals)
Intervals are available in matlib.
https://leanprover-community.github.io/mathlib_docs/data/set/intervals/basic.html
-/
namespace demo
def x₁ : ℝ := 1
def x₂ : ℝ := 4
constant open_interval : set.Ioo x₁ x₂
constant closed_open_interval : set.Ico x₁ x₂
constant open_closed_interval : set.Ioc x₁ x₂
constant closed_interval : set.Icc x₁ x₂
end demo

/-
Exercises
---------
9.1.1
9.1.2 (Lemma 9.1.11)
9.1.3 TODO
9.1.1 again, this time using Lemma 9.1.11, and Exercise 9.1.6.
-/

-- Definition 9.1.7
-- I'm skipping this and going directly to 9.1.8

-- Definition 9.1.8
def is_adherent (x : ℝ) (X : set ℝ) : Prop := 
∀ ε > 0, ∃y ∈ X, |x - y| < ε

infix `is_adherent_to` :55 := is_adherent

-- Definition 9.1.10
def closure (X : set ℝ) : set ℝ := 
{x : ℝ | x is_adherent_to X }

-- Definition 9.1.15
def is_closed (X : set ℝ) :Prop :=
closure X = X

-- Definition 9.1.18 a)
def is_limit_point (x : ℝ) (X : set ℝ) : Prop :=
is_adherent x (X \ {x})

def is_isolated_point (x : ℝ) (X : set ℝ) : Prop :=
x ∈ X ∧ ∃ ε > 0, ∀y ∈ (X \ {x}), |x - y| > ε

-- Definition 9.1.22
def is_bounded (X : set ℝ) : Prop :=
∃ M > 0, X ⊆ set.Icc (-M) M


/- Exercise 9.1.1
If X ⊆ Y ⊆ closure(X), then closure(Y) = closure(X)

This attempt is a hacky δ—ε proof; it doesn't use any properties from Lemma 
9.1.11. I repeat the proof again below using Lemma 9.1.11.
-/
lemma closure_squeeze 
  (X Y : set ℝ) 
  (h₁ : X ⊆ Y) 
  (h₂ : Y ⊆ closure(X)) : 
closure(X) = closure(Y) :=
begin
  apply set.eq_of_subset_of_subset,
  {
    intros x h₃ ε hε,
    have h₄ : x is_adherent_to X, from h₃,
    have h₅ : ∃x' ∈ X, |x - x'| < ε, from h₃ ε hε,
    rcases h₅ with ⟨x', h₆, h₇⟩,
    have h₈ : x' ∈ Y, from h₁ h₆,
    use x',
    exact and.intro h₈ h₇
  },
  {
    intros y h₃ ε hε,
    set δ := ε/3 with hδ,
    have h₅ : δ > 0, by linarith, 
    have h₆ : ∃y' ∈ Y, |y - y'| < δ, from h₃ δ h₅,
    rcases h₆ with ⟨y', hy', h₇⟩,
    have h₈ : y' ∈ closure(X), from h₂ hy',
    have h₉ : ∃x ∈ X, |y' - x| < δ, from h₈ δ h₅,
    rcases h₉ with ⟨x, hx, h₁₀⟩,
    use x,
    have h₁₀ : |(y - y') + (y' - x)| ≤ |y - y'| + |y' - x|, from abs_add _ _,
    have h₁₁ : |y - x| < 2*δ, 
      rw (show (y - x) = (y - y') + (y' - x), by ring),
      linarith,
    have h₁₂ : |y - x| < ε, by linarith,
    exact and.intro hx h₁₂
  }
end

/- Exercise 9.1.2 (Lemma 9.1.11)

There are 4 separate propositions here:

  1. X ⊆ closure(X)
  The 4th part is done next so that it can be used in 2 and 3.
  4. X ⊆ Y → closure(X) ⊆ closure(Y)  
  2. closure(X ∪ Y) = closure(X) ∪ closure(Y)
  3. closure(X ∩ Y) ⊆ closure(X) ∩ closure(Y)
-/ 

-- 1. X ⊆ closure(X)
lemma subset_closure (X : set ℝ ) : X ⊆ closure(X) :=
begin
  intros x h₁ ε h₂,
  apply exists.intro x,
  apply exists.intro h₁,
  rw [sub_self, abs_zero],
  exact h₂,
end

-- Trying to achieve the same thing using a term-based proof.
lemma subset_closure_term (X : set ℝ ) : X ⊆ closure(X) :=
assume x,
assume h₁ : x ∈ X,
have adh: x is_adherent_to X, from
  assume ε,
  assume h₂ : ε > 0,
  have h₃ : |x - x| < ε, from
    have h₄ : x - x = 0, from sub_self x,
    sorry, -- not sure how to proceed here.
  exists.intro x (exists.intro h₁ h₃),
show x ∈ closure(X), from adh   

-- 4. X ⊆ Y → closure(X) ⊆ closure(Y)
lemma closure_mono {X Y :set ℝ} (hXY : X ⊆ Y) : closure(X) ⊆ closure(Y) :=
begin
  intros x hx ε hε,
  have : ∃x' ∈ X, |x - x'| < ε, from hx ε hε,
  rcases this with ⟨x', hx', h₂⟩,
  use x',
  split,
  exact hXY hx',
  exact h₂, -- could use `assumption` here instead.
end

-- 2. closure(X ∪ Y) = closure(X) ∪ closure(Y)       
lemma closure_union 
  {X Y : set ℝ} : 
closure (X ∪ Y) = closure (X) ∪ closure (Y) :=
begin
  apply set.subset.antisymm,
  {
    -- not sure how to do this part in Lean.
    admit
  },
  {
    intros a haXY,
    cases haXY,
    apply closure_mono (set.subset_union_left X Y) haXY,
    apply closure_mono (set.subset_union_right X Y) haXY
  }
end

/- 3. closure(X ∩ Y) ⊆ closure(X) ∩ closure(Y)

Version 1, my original ε attempt. 
Below, using closure_mono, is a nicer proof.
-/
lemma closure_inter_subset_inter_closure (X Y : set ℝ) :
closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
begin
  intros a ha,
  split,
  repeat {
    intros ε hε,
    rcases ha ε hε with ⟨xy, hxy, h₁⟩,
    use xy,
    cases hxy with l r,
    split; assumption
  }
end
 
/- 3. closure(X ∩ Y) ⊆ closure(X) ∩ closure(Y)

Version 2, by Kenny Lau.
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/cleaning.20up.20this.20tactic.20proof.20%28regarding.20closures%29/near/192625784
-/
lemma closure_inter_subset_inter_closure' (X Y : set ℝ) :
closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
have h₁ : closure (X ∩ Y) ⊆ closure X,
  from closure_mono (set.inter_subset_left X Y),
have h₂ : closure (X ∩ Y) ⊆ closure Y, 
  from closure_mono (set.inter_subset_right X Y),
set.subset_inter h₁ h₂

-- Lemma 9.1.12
-- There are 4 parts.

-- 1. Closure of interval (a, b) is [a, b].
lemma closure_Ioo_Icc 
  (a b : ℝ) 
  (hab : a < b) :
closure (set.Ioo a b) = (set.Icc a b) :=
begin
apply set.subset.antisymm,
{
  intros x hx,
  by_contradiction H,
  unfold set.Icc at H,
  simp at H,
  have hxa : x < a ∨ a ≤ x, by exact @lt_or_ge ℝ real.linear_order x a,
  cases hxa with hlt hge,
  {
    have h₁ : ∃ β > 0, x + β = a, from sorry,
    --have h₆ : x = a - β, by linarith,--exact @eq_sub_of_add_eq ℝ real.add_group x a β h₂,
    rcases h₁ with ⟨β, hβ, h₂⟩,
    rcases hx β hβ with ⟨y, hy, hxy⟩,
    have h₃ : a < y, from hy.left,
    have h₄ : ∃ α > 0, a + α = y, from sorry,
    rcases h₄ with ⟨α, hα, h₅⟩,
    have h₆ : a = y - α, by linarith,
    rw h₆ at h₂,
    have h₇ := y - x = β + α, from sorry,--by linarith, -- really linarith!
  },
  {
    admit
  },
},
{
  admit
},
end

-- 2. Closure of interval (a, b] is [a, b].
-- 3. Closure of interval [a, b) is [a, b].
-- 4. Closure of interval [a, b] is [a, b].



-- [TODO: convert to lean]
-- Exercise 9.1.3
-- This needs to be improved! How to properly prove being equal to the
-- empty set?
lemma is_empty_closed : is_closed ∅ :=
begin
unfold is_closed,
unfold closure,
apply set.subset.antisymm,
{
  intros x hx,
  have h₁ : ∀ ε > 0, ∃x' ∈ ∅, |x - x'| < ε, from hx,
  set a : ℝ := 1 with h₂,
  have h₃ : a > 0, by linarith,
  rcases h₁ a h₃ with ⟨x', h0, h0a⟩,
  exact h0
},
{simp,}
end
-- Exercise 9.1.4
-- Exercise 9.1.5

/-
Exercise 9.1.6
-/
lemma closure_closure (X : set ℝ) : closure (closure X) = closure X :=
begin
apply set.subset.antisymm,
{
  intros a haX ε hε,
  set δ := ε/3 with h3δ,
  have hδ : δ > 0, by linarith,
  rcases haX δ hδ with ⟨xc, hxc, h₁⟩,
  rcases hxc δ hδ with ⟨x, hx, h₂⟩,
  use x,
  split,
  exact hx,
  calc |a - x| = |(a - xc) + (xc - x)| : by ring
  ...          ≤ |a - xc| + |xc - x|   : by apply abs_add 
  ...          < 2 * δ                 : by linarith
  ...          < ε                     : by linarith
},
{
  apply subset_closure (closure X)
}
end

/- Exercise 9.1.6 (version 2)

If you decide to follow the book and prove exercise 9.1.1 first, then you can
use that result to prove 9.1.6 easily. Above, 9.1.6 is done without 9.1.1
so as to be available for earlier proofs.
-/
example {X : set ℝ} : closure (closure X) = closure X :=
begin
  -- Use closure(X) as the middle term in 9.1.1's lemma.
  let Y := closure X,
  have h₁ : X ⊆ Y, from subset_closure X,
  have h₂ : Y ⊆ closure X, from set.subset.refl Y,
  have h₃ : closure X = closure (closure X), from closure_squeeze X Y h₁ h₂,
  apply eq.symm, -- Should `simp,` work here instead?
  exact h₃,
end


/- Exercise 9.1.7
A the union of a finite number of closed sets is closed.

It seems possible to either:
  a) take a function, f: ℕ → set ℝ, as input and induce on ℕ, or
  b) take a finset ℝ as input and induce using the provided mechanism of finset.

Let's try a)

The captial 'U' refers to the union of the family of sets.
Note: should the `n` be removed?
mathlib uses 'is_closed_bUnion' to name their method. I'm not sure what
the b prefix means here.
-/
/-lemma is_closed_Union 
  {ss : finset set ℝ} 
  (h₁ : ∀s ∈ ss, is_closed (s)) :
is_closed (set.Union (finset.to_set ss)) :=
sorry
-/
/- TODO
Struggling to induce over finite sets, so I'll try a more general approach of
using index sets and come back later to address it. We can define f to be 
a function that simply maps all i>n to n to achieve the same thing as intented,
it's just not really honoring the intent of the original statement.
-/
lemma is_closed_Union_n 
  {n : ℕ} 
  {f : ℕ → set ℝ}
  (h₁ : ∀i < n, is_closed (f i)) : 
is_closed ⋃ i < n, f i :=
sorry

lemma not_le_of_ge (a b : ℝ) (h : ¬ a < b) : a ≥ b :=
begin
  -- ge_iff_le isn't actually needed.
  rw [@not_lt ℝ real.linear_order a b, ←ge_iff_le] at h, 
  exact h
end
--@iff.mp (¬a < b) (b ≤ a) (@not_lt ℝ real.linear_order a b) h

variables P  : ℝ → Prop
example (a : ℝ) (h : ∀ y : ℝ, P y → ¬ a < y) : ∀ y : ℝ, P y → a ≥ y :=
begin
  simp_rw @not_lt ℝ real.linear_order a at h,
  exact h
end

/-- Exercise 9.1.9
I took two approaches to solving this. 
1. Tao's order
I approached it in the sequence presented in the problem (starting with adherent 
points being limit points xor isolated points). The first part of this turned 
into a monolithic tactic proof. 

2. First introduce to iff statements
In an attempt to make the above proof less of a monolith, I proved the 
bijections:
  is_limit_point x X ↔ x ∈ closure (X \ {x}) 
  is_isolated_point x X ↔ is_adherent x X ∧ x ∉ closure (X \ {x})
However, the second of these proofs turned out to be even more involved than the
original monolith, so nothing was really gained here. 
-/

-- 1. Tao's order.

/- 1.1
An adherent point to set of reals is exactly one of the following: 
  * a limit point or
  * an isolated point
-/
lemma limit_xor_isolated
  (X : set ℝ) 
  (x : ℝ)
  (hx : is_adherent x X) :
is_isolated_point x X ↔ ¬ is_limit_point x X :=
begin
  split,
  {
    intros hix hlx,
    rcases hix with ⟨hxX, ε, hε, hy⟩,
    rcases hlx ε hε with ⟨y, hyX, hxy⟩,
    have h₁ := hy y hyX,
    linarith,
  },
  {
    intros nhlx,
    -- unfold so that simp will be able to work.
    unfold is_limit_point is_adherent at nhlx,
    -- Push the negative all the way to the < relation.
    simp_rw [not_forall, not_exists, @not_lt ℝ real.linear_order] at nhlx,
    -- Writing it out here will nicer variables.
    have h₁ : ∃ (ε : ℝ) (hε : ε > 0), ∀ (y : ℝ), y ∈ X \ {x} → |x - y| ≥ ε, from nhlx,
    -- Q: Is there an easy way to replace all ≥ with > knowing that we can find 
    -- a smaller real?
    -- I just want to replace ≥ with >. It look simple, but it takes me...
    have h₂ : ∃ (ε : ℝ) (hε : ε > 0), ∀ (y : ℝ), y ∈ X \ {x} → |x - y| > ε, 
      rcases h₁ with ⟨ε, hε, hy⟩,
      use ε/2,
      split, 
      {
        exact (by linarith),
      },
      {
        intros y hyX,
        have h:= hy y hyX,
        linarith,
      },
    -- ... 8 lines.
    split,
    { 
      rcases h₁ with ⟨ε, hε, hy⟩,
      rcases hx ε hε with ⟨y, hyX, hxy⟩,
      by_contradiction,
      rw ←(set.diff_singleton_eq_self a) at hyX,
      have nhxy := hy y hyX,
      linarith,
    },
    {
      exact h₂
    }
  }
end

-- 1.2 a limit point is an adherent point.
lemma adherent_of_limit 
  {X : set ℝ}
  {x : ℝ}
  (h : is_limit_point x X) :
is_adherent x X :=
begin 
  set X_diff_x := X \ {x},
  have h₁ : is_adherent x X_diff_x, from h,
  have h₂ : X_diff_x ⊆ X, from set.diff_subset X {x},
  exact closure_mono h₂ h₁,
end

-- 1.3 a isolated point is an adherent point.
lemma adherent_of_isolated
  {X : set ℝ}
  {x : ℝ}
  (h : is_isolated_point x X) :
is_adherent x X :=
begin
  intros ε hε,
  use x,
  rw [sub_self, abs_zero],
  exact ⟨h.left, hε⟩,
end

-- 2. Custom order.
lemma limit_iff_mem_closure_minus
  {X : set ℝ}
  {x : ℝ} : 
is_limit_point x X ↔ x ∈ closure (X \ {x}) :=
begin
unfold is_limit_point closure,
simp
end

lemma isolated_iff_adherent_not_mem_closure_minus
  {X : set ℝ}
  {x : ℝ} :
is_isolated_point x X ↔ is_adherent x X ∧ x ∉ closure (X \ {x}) :=
begin
split,
{
  intro h,
  split,
  {
    intros ε hε,
    use x,
    rw [sub_self, abs_zero],
    exact ⟨h.left,hε⟩,
  },
  { 
    -- I wanted to push the negative to the left and produce:
    --    ∃ ε > 0, ¬∃ y ∈ X\{x}, |x - y| ≤ ε 
    --    ∃ ε/2 > 0, ¬∃ y ∈ X\{x}, |x - y| < ε/2 
    --    ¬ ∀ ε/2 > 0, ∃ y ∈ X\{x}, |x - y| < ε/2 
    -- which is our goal.
    -- But, as seen below, it's tedius, so I'll just bounce between the ∃ and ∀.
    intros hn,
    rcases h.right with ⟨ε, hε, h₁⟩,
    simp at hn h₁,
    rcases hn ε hε with ⟨y, hy, hxy⟩,
    simp at hy,
    have h := h₁ y hy.left hy.right,
    linarith,
  }
},
{
  assume h,
  have h₁ : x ∈ closure X, from h.left,
  split,
  {
    by_contradiction,
    have h₂ : X = X \ {x}, from eq.symm (set.diff_singleton_eq_self a),
    rw h₂ at h₁,
    exact h.right h₁,
  },
  {
    have hr := h.right,
    unfold closure is_adherent at hr,
    rw set.mem_set_of_eq at hr,
    -- Push the negative all the way to the < relation.
    simp_rw [not_forall, not_exists, @not_lt ℝ real.linear_order, 
             iff.symm ge_iff_le] at hr,
    -- I just want to replace ≥ with >. It look simple, but it takes me...
    have ans : ∃ (ε : ℝ) (hε : ε > 0), ∀ (y : ℝ), y ∈ X \ {x} → |x - y| > ε, 
      rcases hr with ⟨ε, hε, hy⟩,
      use ε/2,
      split, 
      exact (by linarith),
      intros y hyX,
      have h:= hy y hyX,
      linarith,
    -- ... 8 lines.-/
    exact ans
  }
}
end

lemma limit_xor_isolated'
  (X : set ℝ) 
  (x : ℝ)
  (hx : is_adherent x X) :
is_isolated_point x X ↔ ¬ is_limit_point x X :=
begin
  split,
  {
    intros hix hlx,
    exact (iff.elim_left isolated_iff_adherent_not_mem_closure_minus hix).right hlx,
  },
  {
    intros nhlx,
    rw limit_iff_mem_closure_minus at nhlx,
    have h₁ := and.intro hx nhlx,
    exact (iff.elim_right isolated_iff_adherent_not_mem_closure_minus h₁)
  }
end


-- Exercise 9.1.10
-- This is an trivial proof on paper, but I ended up with a mess in Lean.
example (X : set ℝ) (h : X.nonempty) : 
is_bounded X ↔ has_finite_sup X ∧ has_finite_inf X :=
begin
  split,
  {
    -- The forward proof isn't too bad—it's the reverse that is the main issue.
    intro hb,
    rcases hb with ⟨u, hu, h₁⟩,
    let l := -u,
    have hub : u ∈ upper_bounds X, 
      intros x hx,
      exact (h₁ hx).right,
    have hlb : l ∈ lower_bounds X, 
      intros x hx,
      exact (h₁ hx).left,
    have hfs : has_finite_sup X, from ⟨h, set.nonempty_of_mem hub⟩,
    have hfi : has_finite_inf X, from ⟨h, set.nonempty_of_mem hlb⟩,
    exact ⟨hfs, hfi⟩,
  },
  {
    -- This part is a mess, mainly becase:
    --   1. I don't find a simple way of going from `u l : ℝ` to `∃ m > 0, m ≥ u ∧ m ≥ l`
    --   2. I don't know of a tactic like `linarith` that will work with abs inequalities.
    intro h,
    rcases h.left.right with ⟨u, hu⟩,
    rcases h.right.right with ⟨l, hl⟩,
    -- Try create m by setting it equal to `|upper bound| + |lower bound| + 1` 
    let m0 := |u| + |l|,
    have h₁ : m0 ≥ |u| ∧ m0 ≥ |l|, 
      split; {norm_num, apply abs_nonneg},
    let m1 : ℝ := m0 + 1,
    have h₂ : m0 ≤ m1, by norm_num,
    have h₄ : m1 ≥ |u| ∧ m1 ≥ |l|, 
      -- Short but opaque alternative for h₄ proof:
      --   split; cases h₁; apply le_trans; assumption,
      split, 
      {
        apply le_trans h₁.left h₂,
      },
      {
        apply le_trans h₁.right h₂,
      },
    use m1,
    split,
    {
    -- Can't find any automation for here.
      have m0_nonneg : 0 ≤ m0, from add_nonneg (abs_nonneg u) (abs_nonneg l),
      have h₃ : 0 < m1, from add_pos_of_nonneg_of_pos m0_nonneg (by norm_num), 
      exact h₃,
    },
    {
      intros x hx,
      -- Can't find any automation for here.
      have hxm : x ≤ m1, from le_trans (hu hx) (le_trans (le_abs_self u) h₄.left), 
      have hml : -l ≤ m1, from le_trans (neg_le_abs_self l) h₄.right,
      rw neg_le at hml,
      have hmx := le_trans hml (hl hx),
      exact ⟨hmx, hxm⟩,
    },
  },
end


example (X : set ℝ) (h : X.nonempty) :
is_bounded X ↔ has_finite_sup X ∧ has_finite_inf X :=
begin
  split,
  { rintro ⟨M, M0, hM⟩,
    exact ⟨⟨h, M, λ x h, (hM h).2⟩, ⟨h, -M, λ x h, (hM h).1⟩⟩ },
  { rintro ⟨⟨_, u, hu⟩, ⟨_, v, hv⟩⟩,
    use max 1 (max u (-v)), split,
    { apply lt_of_lt_of_le zero_lt_one,
      apply le_max_left },
    { intros x hx, split,
      { apply neg_le.1,
        apply le_trans _ (le_max_right _ _),
        apply le_trans _ (le_max_right _ _),
        apply neg_le_neg,
        exact hv hx },
      { apply le_trans _ (le_max_right _ _),
        apply le_trans _ (le_max_left _ _),
        exact hu hx } } }
end


    /-
    intros hlx,
    --have h₁ := not_forall hlx,
    have h₁ := iff.elim_left not_forall hlx,
    -- Why can't I apply rw not_imp here? simp goes too far.
    -- rw not_imp, 
    cases h₁ with ε h₂,
    have h₃ := iff.elim_left not_imp h₂,
    cases h₃,
    rw not_exists at h₃_right,
    -- Why can't I write: rw ←not_le at h₃_right,
    split,
    {
      rcases hx ε h₃_left with ⟨y, hy, hxy⟩,
      have h₄ := h₃_right y,
      rw not_exists at h₄,
      by_contradiction,
      have h₅ := and.intro hy a,
      rw [set.sub_eq_diff, set.mem_diff] at h₄,
      have h₆ : y ≠ x, 
        by_contradiction,
        simp at a_1,
        have h₇ := h₄ ⟨h₅.left, _⟩,
      simp at h₄,
    },
    {
      set δ := ε/2 with h3δ,
      have hδ : δ > 0, by linarith,
      use δ,
      split,
      exact hδ,
      intros y hy,
      have h₄ := h₃_right y,
      rw not_exists at h₄,
      have h₅ := h₄ hy,
      linarith,
      }

    --rcases hx ε h₃.left with ⟨y, hy, hxy⟩,
  }
end-/
 /-have h₁ : ¬(is_isolated_point x X ∧ is_limit_point x X),
    intro h₂,
    rcases h₂.left with ⟨hxX, ε, hε, hy⟩,
    have h₃ := h₂.right ε hε, 
    rcases h₃ with ⟨y, hyX, hxy⟩,
    have h₄ := hy y hyX, 
  linarith,-/

  /-{
    intros hix hlx,
    rcases hix with ⟨hxX, ε, hε, hy⟩,
    rcases hlx ε hε with ⟨y, hyX, hxy⟩,
    have h₁ := hy y hyX,
    linarith,
  },
  {
    intros hlx hix,
  }
end-/

lemma limit_point_is_adherent 
  (X : set ℝ) 
  (x : ℝ) 
  (h₁ : is_limit_point x X): 
is_adherent x X :=
sorry

lemma isolated_point_is_adherent 
  (X : set ℝ) 
  (x : ℝ) 
  (h₁ : is_isolated_point x X): 
is_adherent x X :=
sorry


/-- Exercise 9.1.10
-/
lemma closure_bounded_if_bounded :
  (X :)


end tao_analysis