import data.real.basic
import data.set

namespace my_closure

universes u
variables {α : Type u}
variables P Q Q' : α  Prop

local notation `|`x`|` := abs x

def is_adherent (x : ℝ) (X : set ℝ) : Prop := 
∀ ε > 0, ∃y ∈ X, |x - y| < ε

def closure(X : set ℝ) : set ℝ := 
{x : ℝ | is_adherent x X }

lemma closure_inter_subset_inter_closure (X Y : set ℝ) :
closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
begin
  intros a ha,
  split; {
  intros ε hε,
  rcases ha ε hε with ⟨xy, hxy, h₁⟩,
  use xy, 
  cases hxy,
  split; 
  assumption,
  }
end

lemma closure_inter_subset_inter_closure' (X Y : set ℝ) :
closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
begin
  intros a ha,
  split; 
  intros ε hε;
  rcases ha ε hε with ⟨xy, hxy, h₁⟩;
  use xy; 
  cases hxy;
  split; 
  assumption,
end

lemma universal_impl_distrib  {a : α} :
(∀ a, P a → Q a ∧ Q' a) ↔ (∀ a, P a → Q a) ∧ (∀ a, P a → Q' a) :=
iff.intro
  (assume hl,
    and.intro 
    (assume a, assume p,  
      and.elim_left (hl a p)) 
    (assume a, assume p,
      and.elim_right (hl a p))) 
  (assume hr,
    assume a, assume p,
    and.intro
      (and.elim_left hr a p)
      (and.elim_right hr a p)
    )

lemma closure_inter_subset_inter_closure'' (X Y : set ℝ) :
closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
begin
    intros a ha,
    rw universal_impl_distrib,
end


lemma closure_inter_subset_inter_closure''' (X Y : set ℝ) :
closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
begin
  intros a ha,
  split,
  {
  intros ε hε,
  rcases ha ε hε with ⟨xy, hxy, h₁⟩,
  use xy,
  exact ⟨hxy.left, h₁⟩,
  },
  {
    intros ε hε,
    rcases ha ε hε with ⟨xy, hxy, h₁⟩,
    use xy,
    exact ⟨hxy.right, h₁⟩,
  }
end

end my_closure


