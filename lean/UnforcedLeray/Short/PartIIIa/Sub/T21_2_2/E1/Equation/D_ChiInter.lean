import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2_4_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2_4_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2_4_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX
import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual

/-!
# `PartIII-a:T21/2/2/3/2/4`: leaf D of `movAdjEquation_of`, the adjoint localized interaction

Source of record: `the November 2 reference manuscript` (SP) lines 2854-2865,
3052-3060. Assembly of the three leaves `mvChi_eq_ladChi_scaled` (`/1`), `cell_integral_rescale`
(`/2`), `isKernelBiotSavart_rescale` (`/3`).

With `a = clockA ν r`, `σ = √a`, `r = revAge ν s ζ`, `C = ν^(-2)`, the cell of `mvChi` is `C/σ`:
`mvChi = a ladChi(σ·)` on the left, `movingPhi = a⁻¹ φ(σ·)` and `movingTrainE = a² E(σ·)` on the
right. Rescaling `x = σ y` with the test `ψ(σ⁻¹·)` and kernel velocity `σ u(σ⁻¹·)` gives
`AdjWeakPointwise` at age `r` on the cell `C`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Product with a constant commutes with `B0579.pd`. -/
theorem pd_const_mul_aux (j : Fin 2) (k : ℝ) (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f)
    (x : ℝ × ℝ) :
    B0579.pd j (fun y => k * f y) x = k * B0579.pd j f x := by
  unfold B0579.pd
  rw [fderiv_const_mul (hf x) k]
  simp [smul_eq_mul]

theorem mvChiInter (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.MvChiInter m := by
  intro hW ν tr t s φ ζ hflow hbd
  have hmc : ∀ y : ℝ × ℝ, mvChi ν tr s φ ζ y = ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
      ladChi tr φ (revAge ν s ζ)
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) :=
    fun y => mvChi_eq_ladChi_scaled m ν tr t s φ ζ hflow y
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, hζ⟩ := hflow
  have hC : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hr0 : 0 ≤ revAge ν s ζ := ht0.trans hr.1.le
  have ha : 0 < clockA ν (revAge ν s ζ) := by
    have h0 : 0 ≤ ν * revAge ν s ζ := mul_nonneg hν.le hr0
    unfold clockA
    linarith
  set a := clockA ν (revAge ν s ζ) with ha_def
  set σ := Real.sqrt a with hσ_def
  have hσpos : 0 < σ := Real.sqrt_pos.2 ha
  have hσ2 : σ * σ = a := Real.mul_self_sqrt ha.le
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσpos.ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hmv : mvLen ν (ν ^ (-2 : ℝ)) s ζ = (ν ^ (-2 : ℝ)) / σ := rfl
  unfold IsAdjInteraction
  rw [hmv]
  intro ψ uψ hψ hu
  -- rescaled test and kernel velocity
  have hψ' : UnforcedLeray.B0579.IsCylTest (ν ^ (-2 : ℝ)) (fun z => ψ (σ⁻¹ • z)) := by
    apply T08.isCylTest_dilate (inv_pos.2 hσpos)
    rw [← div_eq_mul_inv]
    exact hψ
  have hu' : IsKernelBiotSavart (ν ^ (-2 : ℝ)) (fun x => ψ (σ⁻¹ • x))
      (fun x j => σ * uψ (σ⁻¹ • x) j) :=
    isKernelBiotSavart_rescale hσpos hu
  -- the classical weak identity at age `r`
  have hctx : AdjWCtx m ν (ν ^ (-2 : ℝ)) tr t s (physAdj (clockA ν s) G) φ := by
    unfold AdjWCtx
    exact ⟨hν, hC, ht0, hts, hbd, hF.toWeak, hF.jointSmooth⟩
  have hWd := hW ν (ν ^ (-2 : ℝ)) tr t s (physAdj (clockA ν s) G) φ hctx (revAge ν s ζ) hr
    (fun x => ψ (σ⁻¹ • x)) (fun x j => σ * uψ (σ⁻¹ • x) j) hψ' hu'
  -- the left-hand side
  have hL : ∫ y in B0579.cell (ν ^ (-2 : ℝ) / σ), mvChi ν tr s φ ζ y * ((ψ y : ℝ) : ℂ) =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ladChi tr φ (revAge ν s ζ) x * ((ψ (σ⁻¹ • x) : ℝ) : ℂ) := by
    rw [cell_integral_rescale (ν ^ (-2 : ℝ)) σ hσpos
      (fun y => mvChi ν tr s φ ζ y * ((ψ y : ℝ) : ℂ))]
    have hpt : ∀ x : ℝ × ℝ, mvChi ν tr s φ ζ (σ⁻¹ • x) * ((ψ (σ⁻¹ • x) : ℝ) : ℂ) =
        ((a : ℝ) : ℂ) * (ladChi tr φ (revAge ν s ζ) x * ((ψ (σ⁻¹ • x) : ℝ) : ℂ)) := by
      intro x
      have e1 : σ * (σ⁻¹ • x).1 = x.1 := by
        rw [Prod.smul_fst, smul_eq_mul, mul_inv_cancel_left₀ hσpos.ne']
      have e2 : σ * (σ⁻¹ • x).2 = x.2 := by
        rw [Prod.smul_snd, smul_eq_mul, mul_inv_cancel_left₀ hσpos.ne']
      rw [hmc (σ⁻¹ • x), e1, e2, Prod.mk.eta]
      ring
    have hk : (((σ ^ 2)⁻¹ : ℝ) : ℂ) * ((a : ℝ) : ℂ) = 1 := by
      rw [← hσ2]
      push_cast
      field_simp
    simp only [hpt]
    rw [integral_const_mul, ← mul_assoc, hk, one_mul]
  -- the right-hand side
  have hEd : Differentiable ℝ (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) :=
    (ForceMemXAux.contDiff_Ec tr hr0).differentiable (by simp)
  have hcomp : Differentiable ℝ (fun z : ℝ × ℝ => UnforcedLeray.B0238.Ec tr (revAge ν s ζ) (σ • z)) :=
    hEd.comp (differentiable_id.const_smul σ)
  have hME : ∀ (k : Fin 2) (y : ℝ × ℝ), B0579.pd k (movingTrainE tr (revAge ν s ζ)) y =
      a ^ 2 * (σ * B0579.pd k (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) (σ • y)) := by
    intro k y
    calc B0579.pd k (movingTrainE tr (revAge ν s ζ)) y
        = B0579.pd k (fun z : ℝ × ℝ => a ^ 2 * UnforcedLeray.B0238.Ec tr (revAge ν s ζ) (σ • z)) y :=
          rfl
      _ = a ^ 2 * B0579.pd k (fun z : ℝ × ℝ => UnforcedLeray.B0238.Ec tr (revAge ν s ζ) (σ • z)) y :=
          pd_const_mul_aux k (a ^ 2) _ hcomp y
      _ = a ^ 2 * (σ * B0579.pd k (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) (σ • y)) := by
          rw [T08.pd_dilate k hEd σ y]
  have hR : ∫ y in B0579.cell (ν ^ (-2 : ℝ) / σ),
      mvPhi ν φ s ζ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr (revAge ν s ζ)) y +
        uψ y 1 * B0579.pd 1 (movingTrainE tr (revAge ν s ζ)) y : ℝ) : ℂ) =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ (revAge ν s ζ) x *
        ((σ * uψ (σ⁻¹ • x) 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x +
          σ * uψ (σ⁻¹ • x) 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x : ℝ) : ℂ) := by
    rw [cell_integral_rescale (ν ^ (-2 : ℝ)) σ hσpos
      (fun y => mvPhi ν φ s ζ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr (revAge ν s ζ)) y +
        uψ y 1 * B0579.pd 1 (movingTrainE tr (revAge ν s ζ)) y : ℝ) : ℂ))]
    have hpt : ∀ x : ℝ × ℝ,
        mvPhi ν φ s ζ (σ⁻¹ • x) * ((uψ (σ⁻¹ • x) 0 *
          B0579.pd 0 (movingTrainE tr (revAge ν s ζ)) (σ⁻¹ • x) +
          uψ (σ⁻¹ • x) 1 * B0579.pd 1 (movingTrainE tr (revAge ν s ζ)) (σ⁻¹ • x) : ℝ) : ℂ) =
        ((a * σ : ℝ) : ℂ) * (φ (revAge ν s ζ) x *
          ((uψ (σ⁻¹ • x) 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x +
            uψ (σ⁻¹ • x) 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x : ℝ) : ℂ)) := by
      intro x
      have e0 : σ • σ⁻¹ • x = x := smul_inv_smul₀ hσpos.ne' x
      have e1 : σ * (σ⁻¹ • x).1 = x.1 := by
        rw [Prod.smul_fst, smul_eq_mul, mul_inv_cancel_left₀ hσpos.ne']
      have e2 : σ * (σ⁻¹ • x).2 = x.2 := by
        rw [Prod.smul_snd, smul_eq_mul, mul_inv_cancel_left₀ hσpos.ne']
      have hmP : mvPhi ν φ s ζ (σ⁻¹ • x) = ((a⁻¹ : ℝ) : ℂ) * φ (revAge ν s ζ) x := by
        unfold mvPhi movingPhi
        rw [← ha_def, ← hσ_def, e1, e2, Prod.mk.eta]
      rw [hmP, hME 0, hME 1, e0]
      push_cast
      field_simp
    simp only [hpt]
    rw [integral_const_mul]
    have hT : ∀ x : ℝ × ℝ,
        φ (revAge ν s ζ) x * ((σ * uψ (σ⁻¹ • x) 0 *
          B0579.pd 0 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x +
          σ * uψ (σ⁻¹ • x) 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x : ℝ) : ℂ) =
        ((σ : ℝ) : ℂ) * (φ (revAge ν s ζ) x *
          ((uψ (σ⁻¹ • x) 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x +
            uψ (σ⁻¹ • x) 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr (revAge ν s ζ)) x : ℝ) : ℂ)) := by
      intro x
      push_cast
      ring
    simp only [hT]
    rw [integral_const_mul]
    have hk2 : (((σ ^ 2)⁻¹ : ℝ) : ℂ) * ((a * σ : ℝ) : ℂ) = ((σ : ℝ) : ℂ) := by
      rw [← hσ2]
      push_cast
      field_simp
    rw [← mul_assoc, hk2]
  rw [hL, hR]
  exact hWd

end UnforcedLeray.Short.IIIa.AdjE1
