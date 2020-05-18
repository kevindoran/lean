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