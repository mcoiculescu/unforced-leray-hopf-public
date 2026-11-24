import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.OpsUnderIntegral
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussInitial
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# Part II-a, `PartII-a:F14/1/1/org`: the truncated integral is Schwartz and solves its equation

Source of record: `the November 2 reference manuscript`, lines 1456-1462 ("truncate
the inverse integral at `M`. Such a truncated integral is Schwartz and its equation has right side
`f - e^{-μM}S(M)f(τ-M)`"), with the inverse integral of lines 1370-1376.

* `fwdIntegrandCont` (proved): `t ↦ F(t, p)` is continuous and `F(0) = f`.
* `truncResSchwartz_of` (proved from `FwdIntegrandRegular`, `FwdIntegrandDecay`): the parametric
  integral over `(0, M]` is smooth (`paramIntegralSmooth_proof`), the operators pass under it
  (`opsUnderIntegral_proof`), and the decay `(1 + |y|)^{-2}` gives slice continuity into `L²`
  (`sliceContOfDecay`).
* `truncResEquation_of` (proved from `FwdIntegrandRegular`, `FwdIntegrandDeriv`, `FwdIntegrandCont`):
  the fundamental theorem of calculus on `[0, M]` for `∂_t F = -(μ + L₀)F`.

This mirrors `adjResolventSolution_of` (`Sub/F05_1.lean`) on the finite interval `(0, M]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Continuity in `t` and the initial value** (`S(0) = 1`). -/
theorem fwdIntegrandCont : FwdIntegrandCont := by
  intro P ν hP hν μ f hf p
  obtain ⟨hJ, -, -⟩ := heatGaussSmooth_proof P hP f hf
  obtain ⟨h0, -⟩ := heatGaussInitial_proof P hP f hf
  refine ⟨?_, ?_⟩
  · have hw : Continuous (fun t : ℝ => fwdW ν t) := by
      show Continuous (fun t : ℝ => Real.sqrt (ν * (Real.exp t - 1)))
      exact (continuous_const.mul (Real.continuous_exp.sub continuous_const)).sqrt
    have hc : Continuous (fun t : ℝ => Complex.exp (-((μ - 1 / 2) * (t : ℂ)))) := by
      fun_prop
    have harg : Continuous (fun t : ℝ => (fwdW ν t, (p.1 - t, Real.exp (t / 2) • p.2))) :=
      hw.prodMk ((continuous_const.sub continuous_id).prodMk
        ((Real.continuous_exp.comp (continuous_id.div_const 2)).smul continuous_const))
    exact hc.smul (hJ.continuous.comp harg)
  · have hw0 : fwdW ν 0 = 0 := by simp [fwdW]
    simp only [fwdIntegrand, hw0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      one_smul, sub_zero, zero_div, Real.exp_zero, h0]

/-- The integrand family satisfies the hypotheses of differentiation under the integral on `(0, M]`. -/
theorem fwd_family {ν : ℝ} {μ : ℂ} {f : ℝ × Space → CVec3}
    (hFs : ∀ t : ℝ, ContDiff ℝ ∞ (fwdIntegrand ν μ f t))
    (hFc : ∀ (k : ℕ) (p : ℝ × Space),
      Continuous (fun t : ℝ => iteratedFDeriv ℝ k (fwdIntegrand ν μ f t) p))
    (hFb : ∀ (M : ℝ) (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) M, ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (fwdIntegrand ν μ f t) p‖ ≤ C)
    (M : ℝ) : ParamFamilyHyp (volume.restrict (Ioc (0 : ℝ) M)) (fwdIntegrand ν μ f) := by
  refine ⟨Eventually.of_forall hFs, fun k p => (hFc k p).aestronglyMeasurable, fun k => ?_⟩
  obtain ⟨C, -, hb⟩ := hFb M k
  refine ⟨fun _ => C, integrable_const C, ?_⟩
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun t ht p => hb t (Ioc_subset_Icc_self ht) p

/-- **The equation of the truncated integral** from the integrand leaves. -/
theorem truncResEquation_of (hR : FwdIntegrandRegular) (hD : FwdIntegrandDeriv)
    (hC : FwdIntegrandCont) : TruncResEquation := by
  intro P ν hP hν μ f hf M hM p
  obtain ⟨hFs, -, hFc, hFb⟩ := hR P ν hP hν μ f hf
  have hfam := fwd_family hFs hFc hFb M
  obtain ⟨iF, iτ, -, ir, il, eτ, -, er, el⟩ :=
    opsUnderIntegral_proof ℝ _ (fwdIntegrand ν μ f) hfam p
  obtain ⟨hcont, h0⟩ := hC P ν hP hν μ f hf p
  have i1 : Integrable (fun t => -(μ - 1 / 2) • fwdIntegrand ν μ f t p)
      (volume.restrict (Ioc (0 : ℝ) M)) := iF.smul (-(μ - 1 / 2) : ℂ)
  have i3 : Integrable (fun t => (1 / 2 : ℝ) • radialT (fwdIntegrand ν μ f t) p)
      (volume.restrict (Ioc (0 : ℝ) M)) := ir.smul (1 / 2 : ℝ)
  have i4 : Integrable (fun t => ν • lapT (fwdIntegrand ν μ f t) p)
      (volume.restrict (Ioc (0 : ℝ) M)) := il.smul ν
  have i12 : Integrable (fun t => -(μ - 1 / 2) • fwdIntegrand ν μ f t p
      - dτ (fwdIntegrand ν μ f t) p) (volume.restrict (Ioc (0 : ℝ) M)) := i1.sub iτ
  have i123 : Integrable (fun t => -(μ - 1 / 2) • fwdIntegrand ν μ f t p
      - dτ (fwdIntegrand ν μ f t) p + (1 / 2 : ℝ) • radialT (fwdIntegrand ν μ f t) p)
      (volume.restrict (Ioc (0 : ℝ) M)) := i12.add i3
  have hftc : ∫ t in Ioc (0 : ℝ) M, (-(μ - 1 / 2) • fwdIntegrand ν μ f t p
      - dτ (fwdIntegrand ν μ f t) p + (1 / 2 : ℝ) • radialT (fwdIntegrand ν μ f t) p
      + ν • lapT (fwdIntegrand ν μ f t) p) = fwdIntegrand ν μ f M p - f p := by
    rw [← intervalIntegral.integral_of_le hM,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hM hcont.continuousOn
        (fun t ht => hD P ν hP hν μ f hf t ht.1 p)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM).2 (i123.add i4)), h0]
  rw [integral_add i123 i4, integral_add i12 i3, integral_sub i1 iτ, integral_smul,
    integral_smul, integral_smul] at hftc
  have eτ' : dτ (truncRes ν μ M f) p = ∫ t in Ioc (0 : ℝ) M, dτ (fwdIntegrand ν μ f t) p := eτ
  have er' : radialT (truncRes ν μ M f) p =
      ∫ t in Ioc (0 : ℝ) M, radialT (fwdIntegrand ν μ f t) p := er
  have el' : lapT (truncRes ν μ M f) p = ∫ t in Ioc (0 : ℝ) M, lapT (fwdIntegrand ν μ f t) p := el
  have hW : truncRes ν μ M f p = ∫ t in Ioc (0 : ℝ) M, fwdIntegrand ν μ f t p := rfl
  rw [← hW, ← eτ', ← er', ← el'] at hftc
  simp only [L0, T0]
  simp only [← Complex.coe_smul] at hftc ⊢
  push_cast at hftc ⊢
  linear_combination (norm := module) (-1 : ℂ) • hftc

/-- **The truncated integral is Schwartz** from the integrand leaves. -/
theorem truncResSchwartz_of (hR : FwdIntegrandRegular) (hY : FwdIntegrandDecay) :
    TruncResSchwartz := by
  intro P ν hP hν μ f hf M hM
  obtain ⟨hFs, hFp, hFc, hFb⟩ := hR P ν hP hν μ f hf
  have hfam := fwd_family hFs hFc hFb M
  obtain ⟨hWs, -⟩ := paramIntegralSmooth_proof (ℝ × Space) ℝ (volume.restrict (Ioc (0 : ℝ) M))
    (fwdIntegrand ν μ f) hfam
  have hWs' : ContDiff ℝ ∞ (truncRes ν μ M f) := hWs
  obtain ⟨C, hC0, hCb⟩ := hY P ν hP hν μ f hf M 2
  have hops := opsUnderIntegral_proof ℝ _ (fwdIntegrand ν μ f) hfam
  have key : ∀ (X : ℝ → CVec3) (y : Space),
      (∀ t ∈ Icc (0 : ℝ) M, ‖X t‖ ≤ C * (1 + ‖y‖) ^ (-((2 : ℕ) : ℝ))) →
      ‖∫ t in Ioc (0 : ℝ) M, X t‖ ≤ (M * C) * (1 + ‖y‖) ^ (-((2 : ℕ) : ℝ)) := by
    intro X y hX
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) M) (f := X)
      measure_Ioc_lt_top (fun t ht => hX t (Ioc_subset_Icc_self ht))
    rw [Real.volume_real_Ioc_of_le hM, sub_zero] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hs : 3 < ((2 : ℕ) : ℝ) * (2 : ℝ≥0∞).toReal := by norm_num
  have hq : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine ⟨hWs', fun τ y => by simp only [truncRes, hFp], ?_, ?_, ?_, ?_⟩
  · refine sliceContOfDecay 2 hq _ (M * C) hs _ hWs'.continuous fun τ y => ?_
    exact key _ y fun t ht => (hCb t ht τ y).1
  · intro j
    refine sliceContOfDecay 2 hq _ (M * C) hs _ (PhaseSpace.contDiff_dy hWs' j).continuous
      fun τ y => ?_
    obtain ⟨-, -, -, -, -, -, ey, -, -⟩ := hops (τ, y)
    have e : dy j (truncRes ν μ M f) (τ, y) =
        ∫ t in Ioc (0 : ℝ) M, dy j (fwdIntegrand ν μ f t) (τ, y) := ey j
    rw [e]
    exact key _ y fun t ht => (hCb t ht τ y).2.2.1 j
  · refine sliceContOfDecay 2 hq _ (M * C) hs _ (PhaseSpace.contDiff_lapT hWs').continuous
      fun τ y => ?_
    obtain ⟨-, -, -, -, -, -, -, -, el⟩ := hops (τ, y)
    have e : lapT (truncRes ν μ M f) (τ, y) =
        ∫ t in Ioc (0 : ℝ) M, lapT (fwdIntegrand ν μ f t) (τ, y) := el
    rw [e]
    exact key _ y fun t ht => (hCb t ht τ y).2.2.2.2
  · have hcont : Continuous (driftT (truncRes ν μ M f)) := by
      show Continuous (fun p => -dτ (truncRes ν μ M f) p
        + (1 / 2 : ℝ) • radialT (truncRes ν μ M f) p + (3 / 2 : ℝ) • truncRes ν μ M f p)
      exact (((PhaseSpace.contDiff_dτ hWs').continuous.neg).add
        ((PhaseSpace.contDiff_radialT hWs').continuous.const_smul (1 / 2 : ℝ))).add
          (hWs'.continuous.const_smul (3 / 2 : ℝ))
    refine sliceContOfDecay 2 hq _ (3 * (M * C)) hs _ hcont fun τ y => ?_
    obtain ⟨-, -, -, -, -, eτ, -, er, -⟩ := hops (τ, y)
    have e1 : dτ (truncRes ν μ M f) (τ, y) =
        ∫ t in Ioc (0 : ℝ) M, dτ (fwdIntegrand ν μ f t) (τ, y) := eτ
    have e2 : radialT (truncRes ν μ M f) (τ, y) =
        ∫ t in Ioc (0 : ℝ) M, radialT (fwdIntegrand ν μ f t) (τ, y) := er
    set B : ℝ := (M * C) * (1 + ‖y‖) ^ (-((2 : ℕ) : ℝ)) with hB
    have b0 : ‖truncRes ν μ M f (τ, y)‖ ≤ B := key _ y fun t ht => (hCb t ht τ y).1
    have b1 : ‖dτ (truncRes ν μ M f) (τ, y)‖ ≤ B := by
      rw [e1]; exact key _ y fun t ht => (hCb t ht τ y).2.1
    have b2 : ‖radialT (truncRes ν μ M f) (τ, y)‖ ≤ B := by
      rw [e2]; exact key _ y fun t ht => (hCb t ht τ y).2.2.2.1
    have hd : driftT (truncRes ν μ M f) (τ, y) = -dτ (truncRes ν μ M f) (τ, y)
        + (1 / 2 : ℝ) • radialT (truncRes ν μ M f) (τ, y)
        + (3 / 2 : ℝ) • truncRes ν μ M f (τ, y) := rfl
    rw [hd]
    have n1 := norm_add_le (-dτ (truncRes ν μ M f) (τ, y)
        + (1 / 2 : ℝ) • radialT (truncRes ν μ M f) (τ, y)) ((3 / 2 : ℝ) • truncRes ν μ M f (τ, y))
    have n2 := norm_add_le (-dτ (truncRes ν μ M f) (τ, y))
        ((1 / 2 : ℝ) • radialT (truncRes ν μ M f) (τ, y))
    have n3 : ‖(1 / 2 : ℝ) • radialT (truncRes ν μ M f) (τ, y)‖ ≤ 1 / 2 * B := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left b2 (by norm_num)
    have n4 : ‖(3 / 2 : ℝ) • truncRes ν μ M f (τ, y)‖ ≤ 3 / 2 * B := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left b0 (by norm_num)
    have n5 : ‖-dτ (truncRes ν μ M f) (τ, y)‖ ≤ B := by rw [norm_neg]; exact b1
    calc _ ≤ _ := n1
      _ ≤ (B + 1 / 2 * B) + 3 / 2 * B := add_le_add (n2.trans (add_le_add n5 n3)) n4
      _ = 3 * (M * C) * (1 + ‖y‖) ^ (-((2 : ℕ) : ℝ)) := by rw [hB]; ring

end UnforcedLeray.Short.PartIIa
