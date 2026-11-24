import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedFreeFamily
import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStage

/-!
# A bounded coefficient representative on a finite turnover interval

The canonical first-stage Dyson APIs take a globally bounded coefficient. On `[0,R-b₀]`, the
actual coefficient `1/(R-t)` is represented by a continuous clamp that agrees exactly there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0012 UnforcedLeray.B0094
  UnforcedLeray.Evolution UnforcedLeray.ComplexODEC

/-- Clamp the turnover clock coefficient to the finite interval `[0,R-b₀]`. -/
def turnoverBlockBeta (R b₀ t : ℝ) : ℝ :=
  1 / (R - max 0 (min t (R - b₀)))

theorem continuous_turnoverBlockBeta {R b₀ : ℝ} (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    Continuous (turnoverBlockBeta R b₀) := by
  have hc : Continuous (fun t : ℝ => R - max 0 (min t (R - b₀))) := by
    fun_prop
  exact continuous_const.div hc (by
    intro t
    have hu : 0 ≤ R - b₀ := by linarith
    have hclamp : max 0 (min t (R - b₀)) ≤ R - b₀ :=
      max_le_iff.mpr ⟨hu, min_le_right _ _⟩
    have hden : b₀ ≤ R - max 0 (min t (R - b₀)) := by linarith
    exact ne_of_gt (lt_of_lt_of_le hb₀ hden))

theorem turnoverBlockBeta_pos {R b₀ t : ℝ} (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    0 < turnoverBlockBeta R b₀ t := by
  unfold turnoverBlockBeta
  have hu : 0 ≤ R - b₀ := by linarith
  have hclamp : max 0 (min t (R - b₀)) ≤ R - b₀ := by
    exact max_le_iff.mpr ⟨hu, min_le_right _ _⟩
  have hden : 0 < R - max 0 (min t (R - b₀)) := by linarith
  exact one_div_pos.mpr hden

theorem turnoverBlockBeta_le_inv {R b₀ t : ℝ} (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    turnoverBlockBeta R b₀ t ≤ 1 / b₀ := by
  unfold turnoverBlockBeta
  have hu : 0 ≤ R - b₀ := by linarith
  have hclamp : max 0 (min t (R - b₀)) ≤ R - b₀ :=
    max_le_iff.mpr ⟨hu, min_le_right _ _⟩
  have hden : b₀ ≤ R - max 0 (min t (R - b₀)) := by linarith
  exact one_div_le_one_div_of_le hb₀ hden

theorem turnoverBlockBeta_eq_reciprocal {R b₀ t : ℝ}
    (hR : b₀ ≤ R) (ht0 : 0 ≤ t) (htt : t ≤ R - b₀) :
    turnoverBlockBeta R b₀ t = 1 / (R - t) := by
  unfold turnoverBlockBeta
  rw [min_eq_left htt, max_eq_right ht0]

theorem intervalIntegrable_turnoverBlockBeta {R b₀ s t : ℝ}
    (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    IntervalIntegrable (turnoverBlockBeta R b₀) volume s t :=
  (continuous_turnoverBlockBeta hb₀ hR).intervalIntegrable s t

theorem aestronglyMeasurable_turnoverBlockBeta {R b₀ a b : ℝ}
    (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    AEStronglyMeasurable (turnoverBlockBeta R b₀) (volume.restrict (Icc a b)) :=
  (continuous_turnoverBlockBeta hb₀ hR).aestronglyMeasurable

/-- The first-stage coefficient plus the actual compact `A` term is exactly the bounded part
in the normalized weak generator, with the clamped coefficient agreeing on the active block. -/
theorem turnoverBlockGenerator_eq_transport_add_A {c : ℂ} {F : ℝ → ℂ} {R b₀ t : ℝ}
    (hb₀ : 0 < b₀) (hR : b₀ ≤ R) (ht0 : 0 ≤ t) (htt : t ≤ R - b₀) :
    (((transportDysonPert ((-2 * Complex.I) • omegaOp) (lamMode c) (kapMode c F)
        (turnoverBlockBeta R b₀) 0 (R - b₀)
        (aestronglyMeasurable_turnoverBlockBeta hb₀ hR)
        ⟨1 / b₀, fun r _ => by
          have hβ := turnoverBlockBeta_pos hb₀ hR (t := r)
          have hle := turnoverBlockBeta_le_inv hb₀ hR (t := r)
          rw [abs_of_pos hβ]
          exact hle⟩).A t) + (2 * Complex.I) • kROp) =
      normalizedTurnoverGenerator c F R t := by
  have hβ := turnoverBlockBeta_eq_reciprocal hR ht0 htt
  simp only [normalizedTurnoverGenerator, transportDysonPert]
  rw [hβ]
  simp only [one_div]

end UnforcedLeray.Cons.G3b
