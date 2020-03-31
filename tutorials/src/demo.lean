import data.real.basic
import tactic
 
 
namespace logic_example
 
variable U : Type
variables A B : U → Prop
 
/-
If you have a proof, h1, which says:
   for all x, if the property A(x) is true, then the property B(x) is true.
and you have another proof, h2, which says:
   for all x, the property A(X) is true,
 
Then the following is a proof which says:
   for all x, B(X) is true.
-/
example
 (h1 : ∀ x, A x → B x)
 (h2 : ∀ x, A x) :
∀ x, B x :=
assume y,
have h3 : A y, from h2 y,
have h4 : A y → B y, from h1 y,
show B y, from h4 h3
 
end logic_example
 
 
 



 
 
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
 
 
 
 
 
 
 
 
/-- A set has at most one least upper bound -/
theorem challenge2_tactic_version
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
cases ha with ha₁ ha₂,
-- you don't have to do the unfolding though.
cases hb with hb₁ hb₂,
-- we prove a = b by showing a ≤ b and b ≤ a
apply le_antisymm, 
{ -- to prove a ≤ b we want to argue that b is an upper bound and a is the least upper bound.
  -- First let's use the fact that a is at most all upper bounds
  --apply ha₂,
  -- and now we just need that b is an upper bound
  exact hb₁},
{ -- The other way is similar.
  apply hb₂,
  exact ha₁}
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
 
 
 

