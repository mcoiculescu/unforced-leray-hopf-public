import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_1_1_2_4_1.Base
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Deriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Leaf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Lift
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Mean
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Moment
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Transfer

/-!
# `phaseOscKernel_of_far`: the Y-side phase kernel from the shared far-field leaf

Source `the November 2 reference manuscript`
5400-5427 (one phase primitive in the dilation variable, degree `-5` gradient kernel, radius ratio
`<= 1/sqrt 1.2`), 4168-4171 (`W_mu = -S_mu(chi_o T)`).  The Y-side is the one-resolvent
version of the X-side reduction `GeomX.PhasePrimitive.phasePrimitiveAt_uniform`; the analytic
content is the same leaf `SepOscFar` (`GeomX/PhasePrimitive/FarLeaf.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace PhasePrimYA

open GeomXAsm MeasYAAux ZRegAux PhasePrim

private def Kmu' : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc 0 2

private theorem Kmu'_compact : IsCompact Kmu' := isCompact_Icc.image Complex.continuous_ofReal

private theorem Kmu'_re : ∀ μ ∈ Kmu', -(1 / 4) < μ.re := by
  rintro μ ⟨x, hx, rfl⟩
  simp only [Complex.ofReal_re]
  linarith [hx.1]

private theorem gap_le' (ν : ℝ) (hν : 0 < ν) :
    Real.sqrt (5 * ν / 6) ≤ 11 / 12 * Real.sqrt ν := by
  have h : 11 / 12 * Real.sqrt ν = Real.sqrt ((11 / 12 * Real.sqrt ν) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [h]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, Real.sq_sqrt hν.le]
  nlinarith

private theorem poly_le' (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    1 + ν⁻¹ + cOf ν + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 16 * ν⁻¹ ^ 2 := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := gap_le' ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have h2 : ν⁻¹ ≤ ν⁻¹ ^ 2 := by nlinarith
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  have hc : cOf ν = ν⁻¹ ^ 2 := by unfold cOf; rw [inv_pow]
  rw [hc]
  nlinarith

private theorem rpow_neg_five' (s : ℝ) (hs : 0 < s) :
    ((Real.sqrt s)⁻¹) ^ (-5 : ℝ) = s ^ (5 / 2 : ℝ) := by
  have h0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have h5 : Real.sqrt s ^ (5 : ℝ) = Real.sqrt s ^ (5 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.sqrt s) 5
  rw [Real.rpow_neg (inv_nonneg.2 h0), Real.inv_rpow h0, inv_inv, h5,
    GeomXAsm.sqrt_pow_five hs.le]

private theorem fderiv_sepWre (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) T y τ) y) :
    fderiv ℝ (sepWre ν μ T τ) y = reMap.comp (fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) T y τ) y) :=
  (reMap.hasFDerivAt.comp y hA.hasFDerivAt).fderiv

private theorem dOsc_le (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y)
    (hA' : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c (meanQ c g)) y τ) y) :
    ‖fderiv ℝ (sepWre ν μ (oldPhys R c g) τ) y -
        fderiv ℝ (sepWre ν μ (oldPhys R c (meanQ c g)) τ) y‖ ≤
      2 * ‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y -
        fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c (meanQ c g)) y τ) y‖ := by
  rw [fderiv_sepWre ν μ _ τ y hA, fderiv_sepWre ν μ _ τ y hA', ← ContinuousLinearMap.comp_sub]
  calc _ ≤ ‖reMap‖ * ‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y -
        fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c (meanQ c g)) y τ) y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right opNorm_reMap_le (norm_nonneg _)

/-- **The Y-side phase kernel from the far-field leaf** (source 5400-5427). -/
theorem phaseOscKernel_of_far (hLeaf : SepOscFar) : PhaseOscKernel := by
  obtain ⟨C, k, hC, hlf⟩ := hLeaf Kmu' Kmu'_compact Kmu'_re
  refine ⟨4 * Real.pi * (C + 1) * 16 ^ k, 2 * k, by positivity, ?_⟩
  intro ν ε μ hν hν1 hε hε1 hμ0 hμ1 g hgm hmom hz s hs η
  have hc : 0 < cOf ν := cOf_pos hν
  have hs0 : 0 < s := hs.1
  have hνs : ν * s ≤ 1 := by
    have := hs.2
    rw [le_div_iff₀ hν] at this
    linarith
  set y : Space := NearInst.chartY ε⁻¹ (s, (0, η)) with hy
  have hϱy : ϱ y = ε⁻¹ / Real.sqrt s := by
    rw [hy, GeomXAsm.chartY_eq_hpt, GeomXAsm.ϱ_hpt (by positivity)]
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hcoef : 0 < 4 * Real.pi * (C + 1) * 16 ^ k * ν⁻¹ ^ (2 * k) *
      (ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have := Real.pi_pos
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    positivity
  set N := tenN1 (cOf ν) g with hN
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
  have hz' := ZRegAux.mean_ae_zero (cOf ν) (-1 / 2) ν hc g hgm hz
  set F := cutLift (cOf ν) (Real.sqrt (5 * ν / 6)) g with hF
  have hFm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j :=
    cutLift_measurable _ _ g hgm
  have hFp : ∀ x' Y q, F x' Y (q + cOf ν) = F x' Y q := cutLift_periodic _ _ hc.ne' g
  have hFs : ∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) →
      F x' Y q = 0 := fun x' Y q h => cutLift_support _ _ g x' Y q h
  have hFN : IIIa.thinMoment (cOf ν) F ≤ ENNReal.ofReal Real.pi * N :=
    thinMoment_cutLift_le (cOf ν) (Real.sqrt (5 * ν / 6)) hc g hgm
  have hFfin : IIIa.thinMoment (cOf ν) F ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNtop) hFN
  set xo : Space := ε • y with hxo
  have hxo' : ε⁻¹ • xo = y := by
    rw [hxo, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hxr : Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) = (Real.sqrt s)⁻¹ := by
    have h0 : xo 0 = (Real.sqrt s)⁻¹ := by
      rw [hxo, hy, GeomXAsm.chartY_eq_hpt]
      show ε * (ε⁻¹ / Real.sqrt s) = _
      field_simp
    have h1 : xo 1 = 0 := by
      rw [hxo, hy, GeomXAsm.chartY_eq_hpt]
      show ε * 0 = _
      ring
    rw [h0, h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (by positivity)]
  have hρ : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi : Real.sqrt ν ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
    rw [hxr, le_inv_comm₀ (Real.sqrt_pos.2 hν) hss, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    exact hs.2.trans (le_of_eq (one_div _))
  have hμK : ((μ : ℝ) : ℂ) ∈ Kmu' := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  obtain ⟨B, hBm, hBp, hBae, hBle⟩ := hlf ν (cOf ν) ε (Real.sqrt (5 * ν / 6))
    (Real.sqrt ν) hν hν1 hc hε hε1 (Real.sqrt_nonneg _) hρ (μ : ℂ) hμK F hFm hFp hFs hFfin xo hρi
  have eA : ∀ (μc : ℂ) τ, (fun y => IIIa.sepW ν μc (IIIa.thinSource ε F) y τ) =
      fun y => IIIa.sepW ν μc (oldPhys ε⁻¹ (cOf ν) g) y τ := fun μc τ =>
    funext fun y => sepW_cut (cOf ν) ν ε μc hc hν hε g hz y τ
  have eM : ∀ (μc : ℂ) τ, (fun y => IIIa.sepW ν μc
      (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean (cOf ν) F))) y τ) =
      fun y => IIIa.sepW ν μc (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) y τ :=
    fun μc τ => funext fun y => sepW_mean (cOf ν) ν ε μc hc hν hε g hgm hmom hz' y τ
  have hyr : ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y := by
    rw [hϱy, show ε⁻¹ / Real.sqrt s = ε⁻¹ * (Real.sqrt s)⁻¹ from div_eq_mul_inv _ _]
    apply mul_lt_mul_of_pos_left _ (inv_pos.2 hε)
    rw [← Real.sqrt_inv]
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [← one_div, lt_div_iff₀ hs0]
    nlinarith
  have hmean_m := ZRegAux.measurable_meanQ' (cOf ν) hgm
  have hmean_mom : ∫⁻ p, ‖meanQ (cOf ν) g p‖ₑ ^ 2 ∂(ageμ (cOf ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (ZRegAux.mean_moment_le _ _ hc _ hgm) hmom
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hmaj : ∀ᵐ τ ∂(volume : Measure ℝ),
      ENNReal.ofReal (dOsc ν ε μ g τ (NearInst.chartY ε⁻¹ (s, (0, η)))) ≤ B τ + B τ := by
    filter_upwards [hBae] with τ h1
    rw [hxo', eA, eM] at h1
    have hd := dOsc_le ν μ ε⁻¹ (cOf ν) g τ y
      (sepW_diff (cOf ν) ν ε _ hc hν hε hreμ g hgm hmom hz τ y hyr)
      (sepW_diff (cOf ν) ν ε _ hc hν hε hreμ _ hmean_m hmean_mom hz' τ y hyr)
    have e : dOsc ν ε μ g τ (NearInst.chartY ε⁻¹ (s, (0, η))) =
        ‖fderiv ℝ (sepWre ν μ (oldPhys ε⁻¹ (cOf ν) g) τ) y -
          fderiv ℝ (sepWre ν μ (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) τ) y‖ := rfl
    rw [e]
    calc ENNReal.ofReal ‖fderiv ℝ (sepWre ν μ (oldPhys ε⁻¹ (cOf ν) g) τ) y -
          fderiv ℝ (sepWre ν μ (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) τ) y‖
        ≤ ENNReal.ofReal (2 * ‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (oldPhys ε⁻¹ (cOf ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) y τ) y‖) := ENNReal.ofReal_le_ofReal hd
      _ = ‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (oldPhys ε⁻¹ (cOf ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) y τ) y‖ₑ +
          ‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (oldPhys ε⁻¹ (cOf ν) g) y τ) y - fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) y τ) y‖ₑ := by
          rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm]
          norm_num
          ring
      _ ≤ B τ + B τ := by gcongr
  have hcell := cellL2_le ε (cOf ν) hε hc (dOsc ν ε μ g) s η (fun τ => B τ + B τ)
    (hBm.add hBm) (fun τ => by simp only [hBp τ]) hmaj
  set M := 1 + ν⁻¹ + cOf ν + (Real.sqrt ν)⁻¹ +
    Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ with hM
  have hM0 : 0 ≤ M := by
    have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by
      have := gap_le' ν hν
      have := Real.sqrt_pos.2 hν
      linarith
    have := hc.le
    positivity
  have hMle : M ^ k ≤ 16 ^ k * ν⁻¹ ^ (2 * k) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hM0 (by have := poly_le' ν hν hν1; rw [← hM] at this; linarith) k
  have hrad : Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) = s ^ (5 / 2 : ℝ) := by
    rw [hxr, rpow_neg_five' s hs0]
  set a := C * M ^ k * ε ^ 4 * s ^ (5 / 2 : ℝ) with ha
  have ha0 : 0 ≤ a := by
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    rw [ha]
    positivity
  have hLi : IIIa.ltauAt (2 * ε * cOf ν) B ≤ ENNReal.ofReal (a * Real.pi) * N := by
    refine hBle.trans ?_
    rw [hrad, ← ha, ENNReal.ofReal_mul ha0, mul_assoc]
    exact mul_le_mul_right hFN _
  have ha_le : a * Real.pi * 2 ≤ 4 * Real.pi * (C + 1) * 16 ^ k * ν⁻¹ ^ (2 * k) *
      (ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have hs52 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hpi := Real.pi_pos
    have h1 : C * M ^ k ≤ (C + 1) * (16 ^ k * ν⁻¹ ^ (2 * k)) :=
      mul_le_mul (by linarith) hMle (pow_nonneg hM0 _) (by linarith)
    have h2 : 0 ≤ ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
    calc a * Real.pi * 2 = 2 * Real.pi * (C * M ^ k) * (ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          rw [ha]; ring
      _ ≤ 4 * Real.pi * ((C + 1) * (16 ^ k * ν⁻¹ ^ (2 * k))) * (ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          gcongr
          nlinarith
      _ = _ := by ring
  calc cellL2 ε⁻¹ (cOf ν) (dOsc ν ε μ g) s η
      ≤ IIIa.ltauAt (2 * ε * cOf ν) (fun τ => B τ + B τ) := hcell
    _ ≤ IIIa.ltauAt (2 * ε * cOf ν) B + IIIa.ltauAt (2 * ε * cOf ν) B :=
        IIIa.ltauAt_add_le _ hBm hBm
    _ ≤ ENNReal.ofReal (a * Real.pi) * N + ENNReal.ofReal (a * Real.pi) * N := by gcongr
    _ = ENNReal.ofReal (a * Real.pi * 2) * N := by
        rw [← two_mul, ← mul_assoc, ENNReal.ofReal_mul (mul_nonneg ha0 Real.pi_pos.le)]
        congr 1
        rw [mul_comm]
        norm_num
    _ ≤ ENNReal.ofReal (4 * Real.pi * (C + 1) * 16 ^ k * ν⁻¹ ^ (2 * k) *
          (ε ^ 4 * s ^ (5 / 2 : ℝ))) * N := by
        gcongr

/-- **`phasePrimitiveYA` from the far-field leaf** (the target once `sepOscFar` is proved). -/
theorem phasePrimitiveYA_of_far (hLeaf : SepOscFar) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.PhasePrimitiveYA :=
  phasePrimitiveYA_of_kernel (phaseOscKernel_of_far hLeaf) D hst

end PhasePrimYA

end UnforcedLeray.Short.PartIIIb.Concrete
