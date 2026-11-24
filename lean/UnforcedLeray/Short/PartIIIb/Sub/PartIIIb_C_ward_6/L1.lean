import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1

/-!
# `OldL2SepReg` (`PartIII-b:C/ward/6`, L1)

Source of record: `the November 2 reference manuscript` 4155-4171, 2666-2703,
3611-3621.  This is `oldSourceReg_of` (`Sub/IIIb-D2_3_1_1_1.lean`) with the datum `g` itself in
place of `G = strSum (χ_oT)`: the a.e. vanishing of `g` on `ν s ≤ 6/5` is the `old` field of
`IsOldL2`, the moment is the `memLp` field, and the leaves are the same.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **(L1) `OldL2SepReg`**: the separated source `T' = oldCutSrc R c (R√(5ν/6)) g` represents the
lift of `g` for old `L²` data. -/
theorem oldL2SepReg_proved : OldL2SepReg := by
  intro ν R c g hν hR hc hg
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  -- chart-null sets pull back to null sets: `g = 0` on `ν s ≤ 6/5`, a.e. for `ageμ c (-1/2)`
  have hN := chartOfNullPullback R c hR hc _ (ae_iff.1 hg.old)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hN] with x hx
    simp only [not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := hr0
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (R * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf R c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (R ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, osr_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  -- the separated source
  have hper : ∀ τ z, oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / R) z =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic R c g τ z]
  have hsupp : ∀ τ z, R * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ R * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  -- the moment of `g` itself (`MemLp g 2`, cf. `l9_lp_lint`)
  have hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤ := by
    have h := MeasureTheory.MemLp.eLpNorm_lt_top hg.memLp
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top] at h
    simpa [ENNReal.rpow_two] using h
  refine ⟨2 * c / R, oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g, by positivity,
    ⟨oldCutMeasurable R c (R * Real.sqrt (5 * ν / 6)) g hg.measurable, hper, hsupp⟩,
    oldCutMoment R c (R * Real.sqrt (5 * ν / 6)) g hR hc hg.measurable hmom,
    fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ, hagree⟩

end UnforcedLeray.Short.PartIIIb.Concrete
