import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Dom
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L6
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1

/-!
# `PartIII-b:C/ward/9/3/1`: pointwise domination of `transField` by `transMajA`

Source `the November 2 reference manuscript` 3684-3712, 4181-4214.  The proof of
`transSepDom` (`S1/Dom.lean`: weight `2μ + 2` kept, arbitrary `ν, R > 0`, with the relaxed
commutator leaves of `S1/*.lean`), applied to the separated source `oldCutSrc R c (R√(5ν/6)) g`,
which has the same `sepW` responses as `oldPhys R c g` (`s1_bridge`, the bridge of
`wardYWYoungL2_proved`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem s1_bridge (R c ν : ℝ) (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν)
    (g : Chart → Ten3) (hg : IsOldL2 c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6))
        (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      IsAxiSource (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      (∀ (μ : ℂ) (y : Space) (τ : ℝ),
        IIIa.sepW ν μ (oldPhys R c g) y τ =
          IIIa.sepW ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) y τ) ∧
      IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) ≤
        ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
  have hgm := hg.measurable
  have hpull := chartOfNullPullback R c hR hc _ (ae_iff.1 hg.old)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
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
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
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
  refine ⟨⟨oldCutMeasurable R c _ g hgm, hper, hsupp⟩, ?_,
    fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ, ?_⟩
  · unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold oldCutSrc
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco R c g τ z
      · simp
    · unfold oldCutSrc
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv R c g τ z
      · simp
  · -- the lift identity
    set P : ℝ := 2 * c / R with hPdef
    have hP0 : 0 < P := div_pos (mul_pos two_pos hc) hR
    set I : ℝ≥0∞ := ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) with hI
    have hG2 : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hgm.enorm.pow_const 2
    have hFm : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 :=
      ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG2
    have hAW : ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) = I :=
      ageWeightShift c hc _ hG2
    have hMain := chartPhaseLIntegral R c hR hc _ hFm
    rw [hAW] at hMain
    have hB : ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal P * (ENNReal.ofReal (Real.pi * R ^ 2) * I) := by
      rw [← mul_assoc, ← hMain]
      refine lintegral_mono fun τ => ?_
      rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
      exact lintegral_mono fun z => oldCut_sq_le R c _ g τ z
    have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
    have hX : (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal (Real.pi * R ^ 2) * I := by
      calc _ ≤ (ENNReal.ofReal P)⁻¹ * (ENNReal.ofReal P *
            (ENNReal.ofReal (Real.pi * R ^ 2) * I)) := by gcongr
        _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hPne ENNReal.ofReal_ne_top, one_mul]
    unfold IIIa.ltauLq
    calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (Real.pi * R ^ 2) * I) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
            congr 1
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
          · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
            simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hI]

/-- **Sub 1** (pointwise domination of `transField`). -/
theorem wardYTransDomG_proved : WardYTransDomG := by
  intro ν μ R c χy hχy hν hR hc hμ
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨C, hC0, hdom⟩ := transDomW ν μ R χy hχ hν hR hμ
  refine ⟨C, hC0, ?_⟩
  intro g hg τ y hy
  obtain ⟨hS, hAx, hresp, hB⟩ := s1_bridge R c ν hR hc hν g hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set N : ℝ≥0∞ := eLpNorm g 2 (ageμ c (-1 / 2)) with hNdef
  have hN : N < ⊤ := hg.memLp.eLpNorm_lt_top
  have hmom : SepMoment (2 * c / R) T :=
    lt_of_le_of_lt hB (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)
  have heq : transField ν μ R c χy g = sepTrans ν μ R χy T := by
    rw [transField_eq_sepTrans]
    exact sepTrans_congr hresp
  rw [heq]
  exact hdom (2 * c / R) hP T hS hmom hAx τ y hy

end UnforcedLeray.Short.PartIIIb.Concrete

end
