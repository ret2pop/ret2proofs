import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic

-- ====================================================================
-- PROBLEM 1: Order & Logic (Warmup)
-- Prove that a strictly increasing function must be injective (one-to-one).
-- ====================================================================

lemma le_irreflexive (x : ℝ) : ¬ (x < x) := by
  exact lt_irrefl x

theorem injective_of_strictly_increasing (f : ℝ → ℝ) (h : ∀ x y, x < y → f x < f y) :
    Function.Injective f := by
    intro x y
    -- We want to prove the contrapositive because it is easier
    contrapose!
    sorry

-- Proves 2x is a continuous function
theorem continuous_at_two_x (x₀ : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |2 * x - 2 * x₀| < ε := by
  intro ε hε
  use (ε / 2)
  constructor
  · -- Prove (ε / 2) > 0
    grind_linarith
  · -- Prove the limit implication
    intro x
    rw [← mul_sub 2 x x₀]
    rw [abs_mul]
    norm_num
    grind_linarith

-- ====================================================================
-- PROBLEM 3: Epsilon-N Sequence Limits
-- Given a custom definition of a sequence limit, prove that shifting a 
-- convergent sequence by a constant 'c' shifts its limit by 'c'.
-- ====================================================================

def SeqLimit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

theorem seqLimit_add_const (a : ℕ → ℝ) (L c : ℝ) (h : SeqLimit a L) :
    SeqLimit (fun n => a n + c) (L + c) := by
  sorry
