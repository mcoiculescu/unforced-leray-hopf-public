import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.OmegaSum

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/18`: folding the atom phase over the periods

Source `the November 2 reference manuscript` (the fold over the periods
`(nP, (n+1)P]` of the phase variable, with the phase weight `omega2 P` of `Kernel.lean`).
Proves `PhaseFold`: for `P > 0` and a measurable `P`-periodic `H`,
`∫⁻ σ, √omega2(σ) H(σ) ≤ (√P + 1/√P) ∫⁻_{(0,P]} H`.

Route: the fundamental domain `Ioc 0 P` of the lattice `ℤ P` gives
`∫⁻ = ∑_{n:ℤ} ∫⁻_{(0,P]} F(σ + nP)`; periodicity of `H` pulls `H(σ)` out of the sum,
`lintegral_tsum` swaps sum and integral, and `omegaSum` bounds the sum of the square-root weights.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

theorem phaseFold : PhaseFold := by
  unfold PhaseFold
  intro P hP H hH hper
  have hω : Measurable (omega2 P) := by
    unfold omega2
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (measurable_const.mul (measurable_const.min Real.measurable_exp)) measurable_const
  -- the lattice `ℤ P` acts with fundamental domain `Ioc 0 P`
  have hfd : MeasureTheory.IsAddFundamentalDomain (AddSubgroup.zmultiples P) (Ioc 0 P) volume := by
    have h := isAddFundamentalDomain_Ioc hP 0
    rw [zero_add] at h
    exact h
  -- the index map `n ↦ n • P` is a bijection from `ℤ` onto `zmultiples P`
  let e : ℤ ≃ AddSubgroup.zmultiples P :=
    Equiv.ofBijective (fun n : ℤ => (⟨n • P, AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples P) n⟩ :
      AddSubgroup.zmultiples P))
      ⟨fun m n h => (zsmul_left_strictMono hP).injective (congrArg Subtype.val h),
        fun g => by
          obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp g.2
          exact ⟨k, Subtype.ext hk⟩⟩
  have hmeas : ∀ n : ℤ, Measurable (fun σ : ℝ =>
      ENNReal.ofReal (Real.sqrt (omega2 P (σ + n * P))) * H σ) := fun n =>
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (hω.comp (measurable_id.add_const ((n : ℝ) * P))))).mul hH
  calc ∫⁻ σ, ENNReal.ofReal (Real.sqrt (omega2 P σ)) * H σ
      = ∑' g : AddSubgroup.zmultiples P, ∫⁻ σ in Ioc 0 P,
          ENNReal.ofReal (Real.sqrt (omega2 P ((g : ℝ) + σ))) * H ((g : ℝ) + σ) :=
        hfd.lintegral_eq_tsum'' _
    _ = ∑' n : ℤ, ∫⁻ σ in Ioc 0 P,
          ENNReal.ofReal (Real.sqrt (omega2 P ((n • P : ℝ) + σ))) * H ((n • P : ℝ) + σ) :=
        (e.tsum_eq _).symm
    _ = ∑' n : ℤ, ∫⁻ σ in Ioc 0 P,
          ENNReal.ofReal (Real.sqrt (omega2 P (σ + n * P))) * H σ := by
        refine tsum_congr fun n => lintegral_congr fun σ => ?_
        rw [zsmul_eq_mul, add_comm ((n : ℝ) * P) σ, hper.int_mul n σ]
    _ = ∫⁻ σ in Ioc 0 P, ∑' n : ℤ,
          ENNReal.ofReal (Real.sqrt (omega2 P (σ + n * P))) * H σ :=
        (lintegral_tsum fun n => (hmeas n).aemeasurable).symm
    _ = ∫⁻ σ in Ioc 0 P, (∑' n : ℤ, ENNReal.ofReal (Real.sqrt (omega2 P (σ + n * P)))) * H σ :=
        lintegral_congr fun σ => ENNReal.tsum_mul_right
    _ ≤ ∫⁻ σ in Ioc 0 P, ENNReal.ofReal (Real.sqrt P + 1 / Real.sqrt P) * H σ :=
        setLIntegral_mono' measurableSet_Ioc fun σ hσ => by
          gcongr
          exact omegaSum P hP σ hσ
    _ = ENNReal.ofReal (Real.sqrt P + 1 / Real.sqrt P) * ∫⁻ σ in Ioc 0 P, H σ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
