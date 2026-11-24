import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L9
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K4

/-!
# `RepairSepBridge` (`PartIII-b:C/rep/2/8`)

Source of record: `the November 2 reference manuscript` 4155-4171, 5148-5176,
2684-2703.  Follows `oldSourceReg_of` (`Sub/IIIb-D2_3_1_1_1.lean`) with the single chart
representative `g = (chiOStr ... M).snd`.  The separated source is
`T = oldCutSrc ε⁻¹ c (ε⁻¹ √(5ν/6)) g`.  The a.e. agreement with `oldPhys ε⁻¹ c g` uses only
`g = 0` where `ν s ≤ 6/5` (the cutoff vanishes there), pulled back by `chartOfNullPullback`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem rb_nsSym_zero : NearInst.nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]

/-- **`RepairSepBridge`** (source 4155-4171, 5148-5176, 2684-2703). -/
theorem repairSepBridge : RepairSepBridge := by
  intro c mZ ρb γ ν ε χo hχo hc hρ hm hν hε M
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  set g : Chart → Ten3 := ((chiOStr c mZ ρb γ ν hχo M).snd : Chart → Ten3) with hgdef
  have hgm : Measurable g := l9_lp_meas ((chiOStr c mZ ρb γ ν hχo M).snd)
  -- the chart representative is `cutFun • M.snd` a.e. on the gain measure
  have hc2 : g =ᵐ[gainHTMeasure c ρb γ ν] cutFun χo ν •
      ((M.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun χo ν) (cutFun_measurable hχo ν) 1 (cutFun_bound hχo ν) M.snd
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at hc2
  have hchart : ∀ᵐ p ∂(ageμ c (-1 / 2)), (ν * p.1 ≤ 6 / 5 → g p = 0) := by
    filter_upwards [hc2] with p e3
    intro hp
    have h0 : cutFun χo ν p = 0 := hχo.zero _ hp
    simp only [e3, Pi.smul_apply', h0, zero_smul]
  have hpull := chartOfNullPullback ε⁻¹ c hR hc _ (ae_iff.1 hchart)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c g x.1 x.2 =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (ε⁻¹ ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  -- periodicity, support, measurability of the separated source
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hper : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / ε⁻¹) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic ε⁻¹ c g τ z]
  have hper2 : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g (τ + 2 * ε * c) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    rw [hP]
    exact hper τ z
  have hsupp : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  have hsep : IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6))
      (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) :=
    { measurable := oldCutMeasurable ε⁻¹ c _ g hgm
      periodic := hper2
      support := hsupp }
  -- the `L²` moment of `g` with respect to the age measure
  have hM : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤ := by
    obtain ⟨κ, hκ, hG⟩ := gainMeasureLower c mZ ρb γ ν hρ hm hν
    have hmeas : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hgm.enorm.pow_const 2
    refine l9_lt_top_of_ofReal_mul hκ ?_
    exact lt_of_le_of_lt ((hG _ hmeas).2) (l9_lp_lint ((chiOStr c mZ ρb γ ν hχo M).snd))
  have hmom := oldCutMoment ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g hR hc hgm hM
  rw [← hP] at hmom
  -- axisymmetry of the cut source
  have hAx : IsAxiSource (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) := by
    unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold oldCutSrc
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco ε⁻¹ c g τ z
      · simp
    · unfold oldCutSrc
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv ε⁻¹ c g τ z
      · simp
  -- the norm inequality, pointwise and then in the mixed norm
  have hPpos : 0 < 2 * ε * c := by positivity
  have hpt : ∀ τ y, IIIa.srcNorm (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) τ y ≤
      ENNReal.ofReal (IIIa.tensorNorm (strPhys ε⁻¹ c g (τ, y))) := by
    intro τ y
    unfold IIIa.srcNorm oldCutSrc
    split_ifs with hz
    · exact le_refl _
    · have h0 : IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
        simp [IIIa.tensorNorm]
      simp [h0]
  have hle : IIIa.ltauLq (2 * ε * c) (22 / 19)
      (IIIa.srcNorm (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g)) ≤
      IIIa.ltauLq (2 * ε * c) (22 / 19)
        (fun τ y => ENNReal.ofReal (IIIa.tensorNorm (strPhys ε⁻¹ c g (τ, y)))) := by
    unfold IIIa.ltauLq
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ zero_le'
    refine lintegral_mono (fun τ => ?_)
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine lintegral_mono (fun y => ?_)
    exact ENNReal.rpow_le_rpow (hpt τ y) (by positivity)
  have heq : IIIa.ltauLq (2 * ε * c) (22 / 19)
      (fun τ y => ENNReal.ofReal (IIIa.tensorNorm (strPhys ε⁻¹ c g (τ, y)))) =
      phaseL2Lr (2 * ε * c) (22 / 19) (strPhys ε⁻¹ c g) := by
    unfold IIIa.ltauLq phaseL2Lr
    rw [ENNReal.ofReal_inv_of_pos hPpos]
  have hnorm : IIIa.ltauLq (2 * ε * c) (22 / 19)
      (IIIa.srcNorm (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g)) ≤
      phaseL2Lr (2 * ε * c) (22 / 19) (strPhys ε⁻¹ c g) := heq ▸ hle
  refine ⟨oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g, hsep, hmom, hAx, ?_, hnorm⟩
  exact fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ

end UnforcedLeray.Short.PartIIIb.Concrete
