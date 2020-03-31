import data.real.basic
import tactic

set_option pp.implicit true
-- Make simp display the steps used.  
set_option trace.simplify.rewrite true
-- # 1
namespace problem1

-- let X, Y, Z be sets.
variables {X Y Z : Type} 

-- a function f : X → Y is *injective* if f(a) = f(b) → a = b for all a,b in X.
def injective (f : X → Y)  : Prop :=
∀ a b : X, f(a) = f(b) → a = b

-- challenge: the composite of two injective functions is injective
theorem challenge1
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
    intros a b,
    intro h₁, --: g ∘ f a  = g ∘ f b, How to specify the type of h₁?
    have h₂ : f a = f b, from hg (f a) (f b) h₁,
    have h₃ : a = b, from hf a b h₂,
    exact h₃
end

theorem challenge1_solution
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
  -- the *definition* of "injective" is "for all a and b...", so let
  -- a and b be arbitrary elements of X.
  intros a b,
  -- Assume (g ∘ f) a = (g ∘ f) b
  intro hab,
  -- The goal is now ⊢ a = b .
  -- By injectivity of f, it suffices to prove f(a)=f(b)
  apply hf,
  -- By injectivity of g, it suffices to prove g(f(a))=g(f(b))
  apply hg,
  -- but this is precisely our assumption.
  exact hab,
  -- "no goals" means we're done.
end

end problem1

namespace problem2

-- basic definitions
def upper_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, s ≤ b }
def lower_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, b ≤ s }
def is_least (S : set ℝ) (l : ℝ) : Prop := l ∈ S ∧ l ∈ lower_bounds S
def is_lub (S : set ℝ) (l : ℝ) : Prop := is_least (upper_bounds S) l

/-- A set has at most one least upper bound -/
theorem challenge2 
  (S : set ℝ) 
  (a b : ℝ) 
  (ha : is_lub S a) 
  (hb : is_lub S b) : 
a = b :=
begin
  have h₁ : a ∈ upper_bounds S, from ha.left,
  have h₂ : b ∈ upper_bounds S, from hb.left,
  have h₃ : a ≤ b, from ha.right b h₂, 
  have h₄ : b ≤ a, from hb.right a h₁,
  linarith,
  -- or
  --exact @le_antisymm ℝ real.partial_order a b h₃ h₄
end 

theorem challenge2_solution
  (S : set ℝ) 
  (a b : ℝ) 
  (ha : is_lub S a) 
  (hb : is_lub S b) : 
a = b :=
begin
  -- if you unfold some definitions
   unfold is_lub at ha,
   unfold is_least at ha,
  -- then you discover that by definition ha is a proof of
  -- a ∈ upper_bounds S ∧ a ∈ lower_bounds (upper_bounds S)
  -- so it's a proof of P ∧ Q, so you can use `cases` to recover the proofs of P and Q.
  cases ha with ha1 ha2,
  -- you don't have to do the unfolding though.
  cases hb with hb1 hb2,
  -- we prove a = b by showing a ≤ b and b ≤ a
  apply le_antisymm,
  { -- to prove a ≤ b we want to argue that b is an upper bound and a is the least upper bound.
    -- First let's use the fact that a is at most all upper bounds
    apply ha2,
    -- and now we just need that b is an upper bound
    exact hb1},
  { -- The other way is similar.
    apply hb2,
    exact ha1}
end

end problem2


namespace ploblem3

theorem challenge3 :
(2 : ℝ) + 2 ≠ 5 :=
begin
  linarith,
end

theorem challenge3_solution :
(2 : ℝ) + 2 ≠ 5 :=
begin
  norm_num
end

/-
Notes:
After checking the docs, norm_num is more lightweight, covering arithmetic
evaluations of *,+,-,^,≤, whereas linarith has norm_num as a subset. It
handles 'linear' arithmetic (not exactly sure what is included here), but it
it is far more comprehensive.
-/

end ploblem3


namespace problem4

open function

theorem challenge4 
  (X Y Z : Type) 
  (f : X → Y) 
  (g : Y → Z) : 
surjective (g ∘ f) → surjective g :=
assume h₁,
assume z,
  have h₂ : ∃y : Y, g y = z, from exists.elim (h₁ z) 
  (assume (x : X) (hh₁ : (g ∘ f) x = z),
    have hh₂ : g (f x) = z, from hh₁,
    let y := f x in exists.intro y hh₂),
  h₂


theorem challenge4_solution 
  (X Y Z : Type) 
  (f : X → Y) 
  (g : Y → Z) : 
surjective (g ∘ f) → surjective g :=
begin
  intro h,
  intro z,
  cases h z with a ha,
  use f a,
  assumption,
end

end problem4