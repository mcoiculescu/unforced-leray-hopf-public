import UnforcedLeray.Short.PartIIb.Sub.T12_2

/-!
# Part II-b, task `PartII-b:T12/2/4`: the slice norm bound (Tonelli)

Source of record: `the November 2 reference manuscript`, lines 1923-1926.

Target: `sliceNormBound_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SliceNormBound`
(the Prop is in `Sub/T12_2.lean`, not changed here).

Proof: `hNorm c r H = (∫⁻ s, s^a ∫⁻ z, ‖H(s,z)‖ₑ^r davgμ ds)^{1/r}` with `a = r/2 - 5/2`
(`ageμ` is the product of the weighted age measure with `avgμ`, so `lintegral_prod` and
`lintegral_withDensity_eq_lintegral_mul` give the iterated integral). The slice hypothesis
gives `∫⁻ ‖G(s,·)‖^r ≤ C^r ∫⁻ ‖F'(s,·)‖^r` for a.e. `s`, which integrates to the claim after the
`1/r` power.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem sliceNormBound_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SliceNormBound := by
  intro c r C G F' hc hr hC hG hF hslice
  haveI hS : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  have hr0 : r ≠ 0 := hr.ne'
  have hrZero : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hrTop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrToReal : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr.le
  -- slice integrals are measurable in `s`
  have hPsiMeas : ∀ H : UnforcedLeray.Short.IIb.CProf, StronglyMeasurable H →
      Measurable fun s : ℝ => ∫⁻ z, ‖H (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) := by
    intro H hH
    have hHm : Measurable fun p : ℝ × (ℝ × ℝ) => ‖H p‖ₑ ^ r :=
      hH.measurable.enorm.pow_const r
    exact hHm.lintegral_prod_right'
  -- the iterated (Tonelli) formula for `hNorm`
  have hNormEq : ∀ H : UnforcedLeray.Short.IIb.CProf, StronglyMeasurable H →
      UnforcedLeray.Short.IIb.hNorm c r H =
        (∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            ∫⁻ z, ‖H (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) ∂(volume.restrict (Ioi (0 : ℝ)))) ^
          (1 / r) := by
    intro H hH
    have hHm : Measurable fun p : ℝ × (ℝ × ℝ) => ‖H p‖ₑ ^ r :=
      hH.measurable.enorm.pow_const r
    unfold UnforcedLeray.Short.IIb.hNorm UnforcedLeray.Short.IIb.hMeas
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrZero hrTop, hrToReal]
    congr 1
    rw [UnforcedLeray.Axi.ageμ, lintegral_prod _ hHm.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ (UnforcedLeray.Axi.measurable_ofReal_rpow _)
        (hPsiMeas H hH)]
    rfl
  rw [hNormEq G hG, hNormEq F' hF]
  -- slice-wise bound, after raising to the power `r`
  have hPsi : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ z, ‖G (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C ^ r * ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) := by
    filter_upwards [hslice] with s hs
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrZero hrTop, hrToReal,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hrZero hrTop, hrToReal] at hs
    have h2 := ENNReal.rpow_le_rpow hs hr.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, one_div, ENNReal.rpow_inv_rpow hr0,
      ENNReal.rpow_inv_rpow hr0] at h2
    exact h2
  -- integrate against the age weight
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
          ∫⁻ z, ‖G (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
          (ENNReal.ofReal C ^ r * ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)) := by
    filter_upwards [hPsi] with s hs
    gcongr
  have hKmeas : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
        ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) :=
    (UnforcedLeray.Axi.measurable_ofReal_rpow _).mul (hPsiMeas F' hF)
  have hCtop : ENNReal.ofReal C ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top
  have hpull :
      ∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
          (ENNReal.ofReal C ^ r * ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c))
          ∂(volume.restrict (Ioi (0 : ℝ))) =
        ENNReal.ofReal C ^ r *
          ∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)
            ∂(volume.restrict (Ioi (0 : ℝ))) := by
    have hrw : ∀ s : ℝ,
        ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            (ENNReal.ofReal C ^ r * ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)) =
          ENNReal.ofReal C ^ r *
            (ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
              ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)) :=
      fun s => by ring
    simp_rw [hrw]
    exact lintegral_const_mul' _ _ hCtop
  calc (∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            ∫⁻ z, ‖G (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) ∂(volume.restrict (Ioi (0 : ℝ)))) ^
          (1 / r)
      ≤ (∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            (ENNReal.ofReal C ^ r * ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c))
            ∂(volume.restrict (Ioi (0 : ℝ)))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hae) (one_div_pos.2 hr).le
    _ = (ENNReal.ofReal C ^ r *
          ∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)
            ∂(volume.restrict (Ioi (0 : ℝ)))) ^ (1 / r) := by
        rw [hpull]
    _ = ENNReal.ofReal C *
          (∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
            ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)
            ∂(volume.restrict (Ioi (0 : ℝ)))) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hr).le, one_div, ENNReal.rpow_rpow_inv hr0]
