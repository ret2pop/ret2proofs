import Mathlib

-- Lemma 1: If f(x) is strictly increasing, it is injective.
-- Proof: suppose f(x) is strictly increasing, yet not injective. Then there exists x, y s.t.
-- x != y yet f(x) = f(y). WLOG let x < y, then f(x) < f(y), so cannot be equal. Contradiction.
lemma injective_of_strictly_increasing (f : ℝ → ℝ) (h : ∀ x y, x < y → f x < f y) :
    Function.Injective f := by
    intro x y h_eq
    -- Proof by contradiction because it is easier
    by_contra! h_neq
    -- unpack cases from not equal
    have two_cases : x < y ∨ y < x := lt_or_gt_of_ne h_neq
    cases two_cases with
    -- x < y
    | inl h_lt =>
      have := h x y h_lt
      linarith
    -- y < x
    | inr h_gt =>
      have := h y x h_gt
      linarith

-- Lemma 2: f(x) = 2x is a continuous function.
-- Proof: |x - x₀| < ε/2
lemma continuous_at_two_x (x₀ : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |2 * x - 2 * x₀| < ε := by
  intro ε hε
  use (ε / 2)
  constructor
  · -- Prove (ε / 2) > 0
    linarith
  · -- Prove the limit implication
    intro x
    rw [← mul_sub 2 x x₀]
    rw [abs_mul]
    norm_num
    -- IDK why linarith doesn't work
    grind_linarith

-- Use non mathlib construction of a limit for practice.
def SeqLimit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- Lemma 3: lim sₙ = L => lim sₙ + c = L + c
-- Proof: |sₙ + c - (L + c)| = |sₙ + c - L - c| = |sₙ - L| < ε
lemma seqLimit_add_const (a : ℕ → ℝ) (L c : ℝ) :
    (SeqLimit a L) → (SeqLimit (fun n => a n + c) (L + c)) := by
    intro a_converges ε hε
    have h_exists := a_converges ε hε
    rcases h_exists with ⟨N, h_bound⟩
    -- we want to use N from a_converges
    use N
    intro n hn
    -- ring solves most of the above, most of the proof is
    -- unpacking predicates in order to apply ring_nf
    ring_nf
    exact h_bound n hn

