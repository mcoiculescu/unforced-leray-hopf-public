import UnforcedLeray.Analysis.Rayleigh.ZeroExtension
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Continuous Dirichlet zero extension through the actual interval clamp

Vanishing endpoint traces identify the indicator extension with composition
by the clamp. This proves continuity and supplies a genuine monotone
1-Lipschitz parameter map for transferring interior modulus estimates.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh

/-- Clamp a real parameter to the two actual interval endpoints. -/
def intervalClamp (l r t : ℝ) : ℝ := max l (min t r)

lemma intervalClamp_mem {l r : ℝ} (hlr : l ≤ r) (t : ℝ) :
    intervalClamp l r t ∈ Icc l r :=
  ⟨le_max_left _ _, max_le hlr (min_le_right _ _)⟩

lemma intervalClamp_of_mem {l r t : ℝ} (ht : t ∈ Icc l r) :
    intervalClamp l r t = t := by
  simp only [intervalClamp, min_eq_left ht.2, max_eq_right ht.1]

lemma intervalClamp_of_le_left {l r t : ℝ} (ht : t ≤ l) :
    intervalClamp l r t = l :=
  max_eq_left ((min_le_left _ _).trans ht)

lemma intervalClamp_of_right_le {l r t : ℝ} (hlr : l ≤ r) (ht : r ≤ t) :
    intervalClamp l r t = r := by
  simp only [intervalClamp, min_eq_right ht, max_eq_right hlr]

lemma intervalClamp_monotone (l r : ℝ) : Monotone (intervalClamp l r) := by
  intro s t hst
  exact max_le_max le_rfl (min_le_min hst le_rfl)

lemma intervalClamp_lipschitz (l r : ℝ) : LipschitzWith 1 (intervalClamp l r) := by
  change LipschitzWith 1 (fun t : ℝ => max l (min t r))
  simpa using!
    (LipschitzWith.const l).max (LipschitzWith.id.min (LipschitzWith.const r))

lemma intervalClamp_continuous (l r : ℝ) : Continuous (intervalClamp l r) :=
  (intervalClamp_lipschitz l r).continuous

lemma intervalClamp_dist_le (l r s t : ℝ) :
    dist (intervalClamp l r s) (intervalClamp l r t) ≤ dist s t := by
  simpa only [NNReal.coe_one, one_mul] using
    (intervalClamp_lipschitz l r).dist_le_mul s t

lemma intervalClamp_abs_sub_le (l r s t : ℝ) :
    |intervalClamp l r s - intervalClamp l r t| ≤ |s - t| := by
  simpa only [Real.dist_eq] using intervalClamp_dist_le l r s t

/-- Endpoint cancellation makes the indicator extension exactly a clamped composition. -/
theorem zeroExtension_eq_clamp {F : ℝ → ℂ} {l r : ℝ} (hlr : l ≤ r)
    (hl : F l = 0) (hr : F r = 0) (t : ℝ) :
    zeroExtension l r F t = F (intervalClamp l r t) := by
  by_cases ht : t ∈ Ioc l r
  · simp only [zeroExtension, indicator_of_mem ht,
      intervalClamp_of_mem ⟨ht.1.le, ht.2⟩]
  · by_cases htl : t ≤ l
    · simp only [zeroExtension, indicator_of_notMem ht, intervalClamp_of_le_left htl, hl]
    · have hrt : r ≤ t := by
        have hlt : l < t := lt_of_not_ge htl
        exact le_of_lt (lt_of_not_ge (fun htr => ht ⟨hlt, htr⟩))
      simp only [zeroExtension, indicator_of_notMem ht, intervalClamp_of_right_le hlr hrt, hr]

theorem zeroExtension_eq_comp_clamp {F : ℝ → ℂ} {l r : ℝ} (hlr : l ≤ r)
    (hl : F l = 0) (hr : F r = 0) :
    zeroExtension l r F = F ∘ intervalClamp l r :=
  funext (zeroExtension_eq_clamp hlr hl hr)

/-- Actual continuity across both endpoints, with no continuity assumption on the extension. -/
theorem zeroExtension_continuous {F : ℝ → ℂ} (hF : Continuous F)
    {l r : ℝ} (hlr : l ≤ r) (hl : F l = 0) (hr : F r = 0) :
    Continuous (zeroExtension l r F) := by
  rw [zeroExtension_eq_comp_clamp hlr hl hr]
  exact hF.comp (intervalClamp_continuous l r)

/-- The actual extended support lies in the compact closed annulus interval. -/
theorem zeroExtension_tsupport_subset (F : ℝ → ℂ) (l r : ℝ) :
    tsupport (zeroExtension l r F) ⊆ Icc l r := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hin : t ∈ Ioc l r := by
    by_contra hn
    exact ht (by simp only [zeroExtension, indicator_of_notMem hn])
  exact ⟨hin.1.le, hin.2⟩

theorem zeroExtension_hasCompactSupport (F : ℝ → ℂ) (l r : ℝ) :
    HasCompactSupport (zeroExtension l r F) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (zeroExtension_tsupport_subset F l r)

end UnforcedLeray.Rayleigh
