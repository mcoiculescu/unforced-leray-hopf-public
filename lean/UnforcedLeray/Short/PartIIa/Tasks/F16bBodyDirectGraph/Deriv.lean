import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph.Tests
import UnforcedLeray.Units.B0005.Spaces

/-!


`B = T0op - 3/4` is the classical generator: `∂_s (dilT s Φ) = dilT s (BΦ)`, and `B` commutes with
`dilT`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.F16b

open UnforcedLeray.PhaseSpace UnforcedLeray.FreeStress

/-- The classical generator `B Φ = 𝒯₀ Φ - (3/4) Φ` on smooth fields. -/
def Bop (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => B0005.T0op Φ p - (3 / 4 : ℂ) • Φ p

theorem isPhaseTest_Bop {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (Bop Φ) := by
  have h : Bop Φ = B0005.T0op Φ + (-(3 / 4 : ℂ)) • Φ := by
    funext p; simp [Bop, sub_eq_add_neg]
  rw [h]
  exact (B0005.IsPhaseTest.T0op hΦ).add (hΦ.const_smul _)

/-- `fderiv Φ q (0, v) = ∑ vⱼ ∂_{yⱼ} Φ(q)`. -/
theorem fderiv_spatial {Φ : ℝ × Space → CVec3} (q : ℝ × Space) (v : Space) :
    fderiv ℝ Φ q (0, v) = ∑ j : Fin 3, (v j) • dy j Φ q := by
  have hv : v = ∑ j : Fin 3, (v j) • coordinateVector j := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  have h : ((0 : ℝ), v) = ∑ j : Fin 3, (v j) • ((0 : ℝ), coordinateVector j) := by
    conv_lhs => rw [hv]
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

theorem radialT_eq_fderiv {Φ : ℝ × Space → CVec3} (q : ℝ × Space) :
    radialT Φ q = fderiv ℝ Φ q (0, q.2) := by
  rw [fderiv_spatial]; rfl

/-- The affine change of variables `g_t(τ, y) = (τ + t, e^{-t/2} y)`. -/
def gmap (t : ℝ) (p : ℝ × Space) : ℝ × Space := (p.1 + t, Real.exp (-(t / 2)) • p.2)

theorem hasFDerivAt_gmap (t : ℝ) (p : ℝ × Space) :
    HasFDerivAt (gmap t)
      ((ContinuousLinearMap.fst ℝ ℝ Space).prod
        (Real.exp (-(t / 2)) • ContinuousLinearMap.snd ℝ ℝ Space)) p := by
  unfold gmap
  have h2 : HasFDerivAt (fun p : ℝ × Space => Real.exp (-(t / 2)) • p.2)
      (Real.exp (-(t / 2)) • ContinuousLinearMap.snd ℝ ℝ Space) p :=
    (Real.exp (-(t / 2)) • ContinuousLinearMap.snd ℝ ℝ Space).hasFDerivAt
  exact ((hasFDerivAt_fst).add_const t).prodMk h2

theorem fderiv_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × Space) :
    fderiv ℝ (dilT t Φ) p =
      (Real.exp (-(3 / 4) * t) : ℂ) • (fderiv ℝ Φ (gmap t p)).comp
        ((ContinuousLinearMap.fst ℝ ℝ Space).prod
          (Real.exp (-(t / 2)) • ContinuousLinearMap.snd ℝ ℝ Space)) := by
  have h := (((hΦ (gmap t p)).hasFDerivAt.comp p (hasFDerivAt_gmap t p))).const_smul
    (Real.exp (-(3 / 4) * t) : ℂ)
  exact h.fderiv

theorem dτ_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × Space) :
    dτ (dilT t Φ) p = (Real.exp (-(3 / 4) * t) : ℂ) • dτ Φ (gmap t p) := by
  simp only [dτ, fderiv_dilT hΦ]
  simp

theorem dy_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (t : ℝ) (j : Fin 3)
    (p : ℝ × Space) :
    dy j (dilT t Φ) p =
      (Real.exp (-(3 / 4) * t) : ℂ) • (Real.exp (-(t / 2)) • dy j Φ (gmap t p)) := by
  simp only [dy, fderiv_dilT hΦ]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero]
  congr 1
  rw [show ((0 : ℝ), Real.exp (-(t / 2)) • coordinateVector j) =
    Real.exp (-(t / 2)) • ((0 : ℝ), coordinateVector j) by simp, map_smul]

theorem radialT_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × Space) :
    radialT (dilT t Φ) p = (Real.exp (-(3 / 4) * t) : ℂ) • radialT Φ (gmap t p) := by
  simp only [radialT, dy_dilT hΦ]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [gmap, PiLp.smul_apply, smul_eq_mul]
  rw [smul_comm (p.2.ofLp j) (Real.exp (-(3 / 4) * t) : ℂ), smul_smul,
    mul_comm (p.2.ofLp j) (Real.exp (-(t / 2)))]

theorem T0op_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × Space) :
    B0005.T0op (dilT t Φ) p = (Real.exp (-(3 / 4) * t) : ℂ) • B0005.T0op Φ (gmap t p) := by
  simp only [B0005.T0op, dτ_dilT hΦ, radialT_dilT hΦ]
  rw [smul_sub, smul_comm (1 / 2 : ℝ)]

theorem Bop_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (t : ℝ) :
    Bop (dilT t Φ) = dilT t (Bop Φ) := by
  funext p
  simp only [Bop, T0op_dilT hΦ, dilT, gmap, smul_sub]
  rw [smul_comm (3 / 4 : ℂ)]

theorem hasDerivAt_dilT {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ) (p : ℝ × Space)
    (s : ℝ) : HasDerivAt (fun s : ℝ => dilT s Φ p) (dilT s (Bop Φ) p) s := by
  have hc : HasDerivAt (fun s : ℝ => (Real.exp (-(3 / 4) * s) : ℂ))
      (((-(3 / 4) * Real.exp (-(3 / 4) * s) : ℝ)) : ℂ) s := by
    have h := (Real.hasDerivAt_exp (-(3 / 4) * s)).comp s ((hasDerivAt_id s).const_mul (-(3 / 4) : ℝ))
    refine HasDerivAt.ofReal_comp ?_
    exact h.congr_deriv (by ring)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s / 2))) (Real.exp (-(s / 2)) * (-(1 / 2))) s := by
    have h := (Real.hasDerivAt_exp (-(s / 2))).comp s (((hasDerivAt_id s).div_const 2).neg)
    exact h.congr_deriv (by simp)
  have hγ : HasDerivAt (fun s : ℝ => gmap s p)
      ((1 : ℝ), (Real.exp (-(s / 2)) * (-(1 / 2))) • p.2) s := by
    unfold gmap
    exact ((hasDerivAt_id s).const_add p.1).prodMk (hexp.smul_const p.2)
  have hΦγ := (hΦ (gmap s p)).hasFDerivAt.comp_hasDerivAt s hγ
  have h := hc.smul hΦγ
  refine HasDerivAt.congr_deriv h ?_
  -- identify the derivative
  set q := gmap s p with hq
  have e1 : fderiv ℝ Φ q ((1 : ℝ), (Real.exp (-(s / 2)) * (-(1 / 2))) • p.2) =
      B0005.T0op Φ q := by
    have hq2 : q.2 = Real.exp (-(s / 2)) • p.2 := rfl
    have : ((1 : ℝ), (Real.exp (-(s / 2)) * (-(1 / 2))) • p.2) =
        ((1 : ℝ), (0 : Space)) + (-(1 / 2 : ℝ)) • ((0 : ℝ), q.2) := by
      ext
      · simp
      · simp [hq2, smul_smul, mul_comm]
    rw [this, map_add, map_smul, ← radialT_eq_fderiv]
    simp only [B0005.T0op, dτ, sub_eq_add_neg, neg_smul]
  rw [e1]
  simp only [dilT, Bop, gmap, Function.comp_apply]
  simp only [hq, gmap]
  push_cast
  module

end UnforcedLeray.Short.PartIIa.F16b
