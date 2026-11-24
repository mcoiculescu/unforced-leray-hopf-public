import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Lib.PhaseSpace.Test
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# `PartII-b:T08/3` helper: Hölder bound for the phase pairing against a phase test
(SP 1902-1906): `|⟨Φ, u⟩| ≤ K ‖u‖_{Y_r}` on measurable `u` with finite `Y_r` norm.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- The phase slab `(0,P] × ℝ³`. -/
abbrev hSlab (P : ℝ) : Measure (ℝ × Space) :=
  (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)

theorem phaseInt_eq_slab {P : ℝ} {f : ℝ × Space → ℂ} (hf : Integrable f (hSlab P)) :
    phaseInt P f = P⁻¹ • ∫ z, f z ∂(hSlab P) := by
  unfold phaseInt
  rw [integral_prod f hf]

theorem phaseTest_bound (P : ℝ) (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ (∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) ∧
      ∀ τ ∈ Icc 0 P, ∀ y, ‖Φ (τ, y)‖ ≤ C := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ closedBall (0 : Space) (max R 0)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.smooth.continuous.continuousOn
  refine ⟨max C 0, max R 0, le_max_right _ _, le_max_right _ _,
    fun τ y h => hR τ y (lt_of_le_of_lt (le_max_left _ _) h), ?_⟩
  intro τ hτ y
  by_cases hy : ‖y‖ ≤ max R 0
  · exact (hC (τ, y) ⟨hτ, by simpa using hy⟩).trans (le_max_left _ _)
  · rw [hR τ y (lt_of_le_of_lt (le_max_left _ _) (not_le.1 hy))]
    simp

/-- The majorant `c · 1_{|y| ≤ R}`. -/
def holderF (c R : ℝ) : ℝ × Space → ℝ≥0∞ :=
  fun z => ENNReal.ofReal c * (Prod.snd ⁻¹' closedBall (0 : Space) R).indicator 1 z

theorem measurable_holderF (c R : ℝ) : Measurable (holderF c R) :=
  measurable_const.mul
    (measurable_one.indicator (measurable_snd measurableSet_closedBall))

theorem holderF_lintegral_lt_top (P R c p : ℝ) (hp0 : 0 < p) :
    ∫⁻ z, holderF c R z ^ p ∂(hSlab P) < ⊤ := by
  have hSm : MeasurableSet (Prod.snd ⁻¹' closedBall (0 : Space) R : Set (ℝ × Space)) :=
    measurable_snd measurableSet_closedBall
  have hμS : hSlab P (Prod.snd ⁻¹' closedBall (0 : Space) R) < ⊤ := by
    have : (Prod.snd ⁻¹' closedBall (0 : Space) R : Set (ℝ × Space)) =
        univ ×ˢ closedBall (0 : Space) R := by
      ext z; simp
    rw [this, Measure.prod_prod]
    refine ENNReal.mul_lt_top ?_ measure_closedBall_lt_top
    rw [Measure.restrict_apply_univ]
    simp
  have : ∀ z, holderF c R z ^ p =
      ENNReal.ofReal c ^ p * (Prod.snd ⁻¹' closedBall (0 : Space) R).indicator 1 z := by
    intro z
    by_cases hz : z ∈ (Prod.snd ⁻¹' closedBall (0 : Space) R : Set (ℝ × Space)) <;>
      simp [holderF, hz, hp0]
  simp_rw [this]
  rw [lintegral_const_mul _ (measurable_one.indicator hSm), lintegral_indicator_one hSm]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hμS

theorem holder_pt (C R : ℝ) (hC : 0 ≤ C) (Φ : ℝ × Space → CVec3) (u : ℝ × Space → CVec3)
    (hRsupp : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) (z : ℝ × Space) (hCz : ‖Φ z‖ ≤ C) :
    ‖dotL (Φ z) (u z)‖ₑ ≤
      holderF (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C) R z * ‖u z‖ₑ := by
  by_cases hzS : z ∈ (Prod.snd ⁻¹' closedBall (0 : Space) R : Set (ℝ × Space))
  · have h1 : ‖dotL (Φ z) (u z)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C * ‖u z‖ := by
      calc ‖dotL (Φ z) (u z)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖Φ z‖ * ‖u z‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ _ := by gcongr
    have : holderF (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C) R z =
        ENNReal.ofReal (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C) := by
      simp [holderF, hzS]
    rw [this, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  · have hz0 : Φ z = 0 := by
      have : R < ‖z.2‖ := by simpa using hzS
      simpa using hRsupp z.1 z.2 this
    simp [hz0]

theorem holder_Ur (P r : ℝ) (hP : 0 < P) (hr0 : 0 < r) (u : ℝ × Space → CVec3)
    (hu : Measurable u) :
    ∫⁻ z, ‖u z‖ₑ ^ r ∂(hSlab P) = ENNReal.ofReal P * phaseLpNorm P r u ^ r := by
  have hmeas : Measurable fun z => ‖u z‖ₑ ^ r := hu.enorm.pow_const r
  rw [lintegral_prod _ hmeas.aemeasurable]
  unfold phaseLpNorm
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one,
    ← mul_assoc, ENNReal.ofReal_inv_of_pos hP, ENNReal.mul_inv_cancel
      (by simpa using hP) ENNReal.ofReal_ne_top, one_mul]

end UnforcedLeray.Short.IIb
