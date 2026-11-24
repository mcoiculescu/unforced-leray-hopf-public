import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2
import UnforcedLeray.Lib.ConvIneq.YoungGroup
import UnforcedLeray.Units.B0412

/-!
# Lemma 2: slice facts for spatial mollification (source 2531)

For a mass-one, nonnegative, smooth, compactly supported kernel `ρ` and `f ∈ L^{q₀}(ℝ³)`:
`ρ * f` is smooth, lies in `L^{q₀}` (Young with `L¹` kernel), satisfies the Hölder sup bound
`‖ρ * f(y)‖ ≤ ‖ρ‖_{q₀'} ‖f‖_{q₀}`, and is bounded by `M` when `‖f‖ ≤ M` a.e.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The spatial mollification is the Mathlib convolution with the scalar `lsmul` kernel. -/
theorem moll_eq_convolution_lsmul (K : UnforcedLeray.Space → ℝ)
    (f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) :
    Moll K f = convolution K f (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure UnforcedLeray.Space) := by
  funext y
  have key : ∫ z, K (y - z) • f z = ∫ t, K t • f (y - t) := by
    rw [← integral_sub_left_eq_self (fun t => K t • f (y - t)) (volume : Measure UnforcedLeray.Space) y]
    simp only [sub_sub_cancel]
  show ∫ z, K (y - z) • f z = ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (K t) (f (y - t))
  simp only [ContinuousLinearMap.lsmul_apply]
  exact key

theorem mollSliceFacts : MollSliceFacts := by
  intro ρ hρ n f hf
  obtain ⟨hdiff, hcs, hnn, hint, -⟩ := hρ n
  set K : UnforcedLeray.Space → ℝ := ρ n with hK
  set q := UnforcedLeray.B0412.q0E with hq
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hKc : Continuous K := hdiff.continuous
  have hKint : Integrable K volume := hKc.integrable_of_hasCompactSupport hcs
  have hKmemq : ∀ p : ℝ≥0∞, MemLp K p volume := fun p => hKc.memLp_of_hasCompactSupport (p := p) hcs
  have hqHC : (conjExp q).HolderConjugate q := conjExp_holderConjugate
  -- smoothness
  have hsm : ContDiff ℝ ∞ (Moll K f) := by
    rw [moll_eq_convolution_lsmul]
    exact hcs.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hdiff
      (hf.locallyIntegrable hq1)
  -- L^q membership via Young with L^1 kernel
  have hmeas : AEStronglyMeasurable (Moll K f) volume :=
    (UnforcedLeray.Conv.aestronglyMeasurable_convolution volume (hKmemq 1).1 hf.1)
  have hyoung : eLpNorm (Moll K f) q volume ≤ eLpNorm K 1 volume * eLpNorm f q volume :=
    UnforcedLeray.Conv.eLpNorm_convolution_le_L1 volume (hKmemq 1).1 hf.1 hq1
  have hmem : MemLp (Moll K f) q volume :=
    ⟨hmeas, lt_of_le_of_lt hyoung (ENNReal.mul_lt_top (hKmemq 1).2 hf.2)⟩
  -- pointwise Hölder bound
  have hpt : ∀ y, ‖Moll K f y‖ ≤
      (eLpNorm K (conjExp q) volume).toReal * (eLpNorm f q volume).toReal := by
    intro y
    have hA : eLpNorm K (conjExp q) volume < ⊤ := (hKmemq (conjExp q)).2
    have hB : eLpNorm f q volume < ⊤ := hf.2
    have h1 : ‖Moll K f y‖ₑ ≤ eLpNorm K (conjExp q) volume * eLpNorm f q volume :=
      (UnforcedLeray.Conv.enorm_convolution_le_convAbs volume K f y).trans
        (UnforcedLeray.Conv.convAbs_le_eLpNorm_mul_eLpNorm volume (hKmemq (conjExp q)).1 hf.1 hqHC y)
    have h2 : ENNReal.ofReal ‖Moll K f y‖ ≤
        eLpNorm K (conjExp q) volume * eLpNorm f q volume :=
      (ofReal_norm _).trans_le h1
    exact ((ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hA.ne hB.ne)).1 h2).trans_eq
      ENNReal.toReal_mul
  -- sup bound from mass one and `‖f‖ ≤ M` a.e.
  have hsup : ∀ M : ℝ, (∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), ‖f y‖ ≤ M) →
      ∀ y, ‖Moll K f y‖ ≤ M := by
    intro M hM y
    have hKy : Integrable (fun z => K (y - z)) volume := hKint.comp_sub_left y
    have hle : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space),
        ‖K (y - z) • f z‖ ≤ M * K (y - z) := by
      filter_upwards [hM] with z hz
      rw [norm_smul, Real.norm_of_nonneg (hnn _), mul_comm M]
      exact mul_le_mul_of_nonneg_left hz (hnn _)
    calc ‖Moll K f y‖ = ‖∫ z, K (y - z) • f z‖ := rfl
      _ ≤ ∫ z, M * K (y - z) := norm_integral_le_of_norm_le (hKy.const_mul M) hle
      _ = M := by
        rw [integral_const_mul, integral_sub_left_eq_self K (volume : Measure UnforcedLeray.Space) y,
          hint, mul_one]
  exact ⟨hsm, hmem, hpt, hsup⟩

end UnforcedLeray.Short.PartIIIb.Concrete
