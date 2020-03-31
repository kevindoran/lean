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
import analysis.normed_space.basic
--import algebra.archimedean
--open set
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

-- Definition 9.1.7
-- I'm skipping this and going directly to 9.1.8

-- Definition 9.1.8
@[reducible]
def is_adherent (x : ℝ) (X : set ℝ) : Prop := 
∀ ε > 0, ∃y ∈ X, |x - y| < ε

infix `is_adherent_to` :55 := is_adherent

-- Definition 9.1.10
@[reducible]
def closure(X : set ℝ) : set ℝ := 
{x : ℝ | x is_adherent_to X }

/- Exercise 9.1.1
If X ⊆ Y ⊆ closure(X), then closure(Y) = closure(X)
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
    apply exists.elim h₅,
    intros x' h_exists_temp,
    apply exists.elim h_exists_temp,
    intros h₆ h₇,
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


    -- There must be a better way to get a δ = ε/3:
    -- have h₄ : ∃δ : ℝ, δ = ε/3, from exists_eq, 
    -- apply exists.elim h₄,
    -- intro δ,
    -- assume hδ : δ = ε/3,

/-
          have h₆ : ∃x ∈ X, |y - x| < ε, from exists.elim h₅ (
            assume (y' : ℝ) (h : (∃hh₁ : (y' ∈ Y), |y - y'| < ε)),
            exists.elim h (
              assume (hhh₁ : y' ∈ Y) (hhh₂ : |y - y'| < ε),
              have hhh₃ : y' ∈ closure(X), from h₂ hhh₁,   
              have hhh₄ : ∀δ > 0, ∃x' ∈ X, |y' - x'| < δ, from hhh₃, 
                have h4₂ : ∃x' ∈ X, |y' - x'| < δ, from hhh₄ h4₁,
              sorry
              )
          --have h₇ : y is_adherent_to X, from h₆,
          --apply h₄, -- why?
        end)-/
    /-
    ext (assume i, iff.intro
      (assume a: i ∈ closure(X),
        show i ∈ closure(Y), from 
            have h2: is_adherent i X, from a,
            have h3: is_adherent i Y, from adheres_to_superset i Y X h1.left h2,
            show i ∈ closure(Y), from h3)
      (assume a: i ∈ closure(Y),
        show i ∈ closure(X), from 
            have h2: is_adherent i Y, from a,
            have h3: is_adherent i X, from 
              assume ε, 
              exists.elim (exists_rat_lt (ε/3))
                (assume (δ : ℝ) (h4: δ < (ε/3)),
                exists.elim (h2 δ)
                  (assume (y : ℝ) (h5: |i - y| < δ),
                  
                  ) 
              --exists.intro y (|i - y| < ε),

              )
            show i ∈ closure(X), from h3)
      )
    )
    -/
    --have h1 : closure(X) ⊆ closure(Y), from sorry
    --have h2 : closure(Y) ⊆ closure(X), from sorry
    --show closure(X) = closure(Y), from sorry

--print notation `[` a `,` b `]` := {i ∈ ℝ | a ≤ i ≤ b}
--print notation `(` a `,` b `)` := {i ∈ ℝ | a ≤ i ≤ b}
--print notation `[` a `,` b `]` := {i ∈ ℝ | a ≤ i ≤ b}
--print notation `[` a `,` b `]` := {i ∈ ℝ | a ≤ i ≤ b}

/- Lemma 9.1.11
There are 4 separate propositions here:

  1. X ⊆ closure(X)
  2. closure(X ∪ Y) = closure(X) ∪ closure(Y)
  3. closure(X ∩ Y) ⊆ closure(X) ∩ closure(Y)
  4. X ⊆ Y → closure(X) ⊆ closure(Y)
-/ 

-- 1. X ⊆ closure(X)
lemma closure_eq_of_is_closed (X : set ℝ ) : X ⊆ closure(X) :=
begin
  intros x h₁ ε h₂,
  apply exists.intro x,
  apply exists.intro h₁,
  rw [sub_self, abs_zero],
  apply le_of_lt,
  exact h₂,
end

-- Trying to achieve the same thing using a term-based proof.
lemma closure_eq_of_is_closed' (X : set ℝ ) : X ⊆ closure(X) :=
assume x,
assume h₁ : x ∈ X,
have adh: x is_adherent_to X, from
  assume ε,
  assume h₂ : ε > 0,
  have h₃ : |x - x| < ε, from
    have h₄ : x - x = 0, from sub_self x,
    sorry, -- not sure how to proceed here.
  have h₄ : |x - x| ≤ ε, from le_of_lt h₃,
  exists.intro x (exists.intro h₁ h₄),
show x ∈ closure(X), from adh   



-- 2. closure(X ∪ Y) = closure(X) ∪ closure(Y)       


lemma closure_union 
  (X Y : set ℝ) : 
closure (X ∪ Y) = closure (X) ∪ closure (Y) :=
sorry





/-
set.eq_of_subset_of_subset
  (assume x : ℝ, assume h₁ : x ∈ closure (X ∪ Y),
    --have h₂ : x is_adherent_to (X ∪ Y), from h₁, 
    --have h₃ : ∀ ε > 0, ∃i, ∃ h :i ∈ (X ∪ Y), |x - i| < ε, from h₂,
    --have h₄ : ∀ ε > 0, ∃i, ∃ h :(i ∈ X ∨ i ∈ Y), |x - i| < ε, from h₂,
    begin
      simp,
      by_cases h₁,
    end
  )
  /-
  show x ∈ (closure(X) ∪ closure(Y)), from 
    have h₂ : x is_adherent_to (X ∪ Y), from h₁,
    have h₂ : (x is_adherent_to X) ∨ (x is_adherent_to Y), from sorry,
    or.elim h₂ 
      (assume a₁ : x is_adherent_to X, 
        show x ∈ (closure(X) ∪ closure(Y)), from
        have h₃ : x ∈ closure(X), from a₁,
        or.inl h₃)
      (assume a₁ : x is_adherent_to Y, 
        show x ∈ (closure(X) ∪ closure(Y)), from
        have h₃ : x ∈ closure(Y), from a₁, 
        or.inr h₃))
    -/
      
  (assume x, assume h₁ : x ∈ (closure(X) ∪ closure(Y)),
  show x ∈ closure(X ∪ Y), from sorry)
-/
-- 3. closure(X ∩ Y) ⊆ closure(X) ∩ closure(Y)
lemma closure_inter_subset_inter_closure(X Y : set ℝ) : 
    closure(X ∩ Y) ⊆ closure(X) ∩ closure(Y) :=
sorry

-- 4. X ⊆ Y → closure(X) ⊆ closure(Y)
lemma closure_mono (X Y :set ℝ) : X ⊆ Y → closure(X) ⊆ closure(Y) :=
sorry

/-
lemma adheres_to_superset (i : ℝ) (A : set ℝ) (B : set ℝ) (h2: B ⊆ A):
    is_adherent i B → is_adherent i A  :=
    assume a1 : is_adherent i B,
    show is_adherent i A, from
      assume ε,
      assume a2 : ε > 0,
        exists.elim (a1 ε a2) 
          (assume (y : B) (h3: |i - y| < ε),
          show ∃z ∈ A, |i - z| < ε, from sorry)
            --exists.intro y h3)
-/


end tao_analysis

namespace graveyard

lemma closure_squeeze_term(X Y : set ℝ) (h₁ : X ⊆ Y) (h₂ : Y ⊆ closure(X)) 
    : closure(X) = closure(Y) :=
    -- Can either use set.eq_of_subset_of_subset or set.ext. The difference
    -- being whether we are showing that two sets are subsets of each other or
    -- whether we are showing that an object is an element of set X iff it is an
    -- element of Y. Both are equivalent, but we need to choose which to use.
    set.eq_of_subset_of_subset
      (assume x, assume h₃ : x ∈ closure(X),
        show x ∈ closure(Y), from 
        begin 
          intro ε,
          intro h₄,
          have h₅ : ∃ x' ∈ X, |x - x'| ≤ ε, from h₃ ε h₄,
          show ∃ y ∈ Y, |x - y| ≤ ε, from exists.elim h₅ (
            assume (x' : ℝ) (h: (∃hh₁ : (x' ∈ X), |x - x'| ≤ ε)),
            exists.elim h (
              assume (hhh₁ : x' ∈ X) (hhh₂ : |x - x'| ≤ ε),
              have hhh₃ : x' ∈ Y, from h₁ hhh₁,
              show ∃y ∈ Y, |x - y| ≤ ε, from 
                exists.intro x' (exists.intro hhh₃ hhh₂))),
        end)
      (assume y, assume h₃ : y ∈ closure(Y),
        show y ∈ closure(X), from 
          assume ε,
          assume h₄,
          have h₅ : ∃δ : ℝ, δ = ε/3, from exists_eq,
          have h₆ : ∃x ∈ X, |y - x| ≤ ε, from exists.elim h₅ 
            (assume (δ : ℝ) (hh₁ : δ = ε/3),
            have hh₃ : δ > 0, by linarith,
            have hh₂ : ∃ y' ∈ Y, |y - y'| ≤ δ, from h₃ δ hh₃,
            exists.elim hh₂
              (assume (y' : ℝ) (hh₄ : ∃ hhh₁ : y' ∈ Y, | y - y'| ≤ δ),
              exists.elim hh₄ 
                (assume (h4₁ : y' ∈ Y) (h4₂ : |y - y'| ≤ δ),
                have h4₃ : y' ∈ closure(X), from h₂ h4₁,
                have h4₄ : ∃x ∈ X, |y' - x| ≤ δ, from h4₃ δ hh₃,
                exists.elim h4₄
                  (assume (x : ℝ) (h4₅ : ∃ h5₁ : x ∈ X, |y' - x| ≤ δ),
                  exists.elim h4₅
                    (assume (h5₁ : x ∈ X) (h5₂ : |y' - x| ≤ δ),
                    --norm_add_le_of_le (by apply_instance) h4₂ h5₂
                    have h5₇ : |y - x| ≤ 2*δ, from sorry,
                    have h5₈ : |y - x| ≤ ε, by linarith,
                    have h5₉ : ∃x' ∈ X, |y - x'| ≤ ε, from 
                       exists.intro x (exists.intro h5₁ h5₈),
                    h5₉))))),
          h₆)

end graveyard