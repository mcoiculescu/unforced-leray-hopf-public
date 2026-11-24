import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit

/-!
# `PartIII-a:T21/2/2/3/5/3/2`: the calculus leaf `PsiDiff`

Source of record: `the November 2 reference manuscript` (SP) lines 2858-2862
(`D^# = Δ - ½y·∇ + 1`) and 3062. Differentiating the reduced moving equation
`a g(√a y) = -(βΔΦ + V·∇Φ - χ)` in `y_k` (the complex partials commute on the smooth `Φ`)
gives `-a^{3/2} ∂_k g(√a y) = β∂_kΔΦ + V·∇∂_kΦ + (∂_kV)·∇Φ - ∂_kχ = xiRed_k - (β/2)∂_kΦ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Complex partial derivatives of a smooth field commute. -/
theorem pdCx_comm_fun {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k l : Fin 2) :
    pdCx k (pdCx l Φ) = pdCx l (pdCx k Φ) := by
  funext y
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (contDiff_infty_iff_fderiv.1 hΦ).2.differentiable (by simp)
  have hs : IsSymmSndFDerivAt ℝ Φ y := (hΦ.contDiffAt).isSymmSndFDerivAt (by simp)
  have key : ∀ j m : Fin 2, pdCx m (pdCx j Φ) y =
      fderiv ℝ (fderiv ℝ Φ) y (B0579.dir m) (B0579.dir j) := by
    intro j m
    have h : HasFDerivAt (fun z => fderiv ℝ Φ z (B0579.dir j))
        ((fderiv ℝ (fderiv ℝ Φ) y).flip (B0579.dir j)) y := by
      simpa using (hd y).hasFDerivAt.clm_apply (hasFDerivAt_const (B0579.dir j) y)
    show fderiv ℝ (fun z => fderiv ℝ Φ z (B0579.dir j)) y (B0579.dir m) = _
    rw [h.fderiv]
    rfl
  rw [key, key]
  exact hs _ _

/-- The Laplacian of a smooth field commutes with `∂_k`. -/
theorem pdCx_lapC_eq {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (lapC Φ) y = lapC (pdCx k Φ) y := by
  have e0 : pdCx k (pdCx 0 (pdCx 0 Φ)) = pdCx 0 (pdCx 0 (pdCx k Φ)) := by
    rw [pdCx_comm_fun (contDiff_pdCx 0 hΦ) k 0, pdCx_comm_fun hΦ k 0]
  have e1 : pdCx k (pdCx 1 (pdCx 1 Φ)) = pdCx 1 (pdCx 1 (pdCx k Φ)) := by
    rw [pdCx_comm_fun (contDiff_pdCx 1 hΦ) k 1, pdCx_comm_fun hΦ k 1]
  have d0 : DifferentiableAt ℝ (pdCx 0 (pdCx 0 Φ)) y :=
    ((contDiff_pdCx 0 (contDiff_pdCx 0 hΦ)).differentiable (by simp)) y
  have d1 : DifferentiableAt ℝ (pdCx 1 (pdCx 1 Φ)) y :=
    ((contDiff_pdCx 1 (contDiff_pdCx 1 hΦ)).differentiable (by simp)) y
  show pdCx k (fun z => pdCx 0 (pdCx 0 Φ) z + pdCx 1 (pdCx 1 Φ) z) y = _
  rw [RateSplitAux.pdCx_add k d0 d1, e0, e1]
  rfl

/-- Each real component of a `C¹` field, cast to `ℂ`, is differentiable. -/
theorem ofReal_comp_differentiableAt {V : ℝ × ℝ → Fin 2 → ℝ} (hV : ContDiff ℝ 1 V) (l : Fin 2)
    (y : ℝ × ℝ) : DifferentiableAt ℝ (fun z => ((V z l : ℝ) : ℂ)) y := by
  have hr : DifferentiableAt ℝ (fun z => V z l) y :=
    ((contDiff_apply ℝ ℝ l).comp hV).differentiable (by simp) y
  exact Complex.ofRealCLM.differentiableAt.comp y hr

/-- `∂_k (V·∇Φ) = V·∇∂_kΦ + (∂_kV)·∇Φ` for a `C¹` field `V` and a smooth `Φ`. -/
theorem pdCx_transC_eq {V : ℝ × ℝ → Fin 2 → ℝ} {Φ : ℝ × ℝ → ℂ} (hV : ContDiff ℝ 1 V)
    (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (transC V Φ) y = transC V (pdCx k Φ) y + dTransC V Φ k y := by
  have hVr : ∀ l : Fin 2, DifferentiableAt ℝ (fun z => V z l) y := fun l =>
    ((contDiff_apply ℝ ℝ l).comp hV).differentiable (by simp) y
  have hVc0 := ofReal_comp_differentiableAt hV 0 y
  have hVc1 := ofReal_comp_differentiableAt hV 1 y
  have hd0 : DifferentiableAt ℝ (pdCx 0 Φ) y := ((contDiff_pdCx 0 hΦ).differentiable (by simp)) y
  have hd1 : DifferentiableAt ℝ (pdCx 1 Φ) y := ((contDiff_pdCx 1 hΦ).differentiable (by simp)) y
  have e0 : pdCx k (fun z => ((V z 0 : ℝ) : ℂ)) y = (B0579.pd k (fun z => V z 0) y : ℂ) :=
    RateSplitAux.pdCx_ofReal (χ := fun z => V z 0) k (hVr 0)
  have e1 : pdCx k (fun z => ((V z 1 : ℝ) : ℂ)) y = (B0579.pd k (fun z => V z 1) y : ℂ) :=
    RateSplitAux.pdCx_ofReal (χ := fun z => V z 1) k (hVr 1)
  have c0 := congrFun (pdCx_comm_fun hΦ k 0) y
  have c1 := congrFun (pdCx_comm_fun hΦ k 1) y
  show pdCx k (fun z => ((V z 0 : ℝ) : ℂ) * pdCx 0 Φ z + ((V z 1 : ℝ) : ℂ) * pdCx 1 Φ z) y = _
  have hf0 : DifferentiableAt ℝ (fun z => ((V z 0 : ℝ) : ℂ) * pdCx 0 Φ z) y := hVc0.mul hd0
  have hf1 : DifferentiableAt ℝ (fun z => ((V z 1 : ℝ) : ℂ) * pdCx 1 Φ z) y := hVc1.mul hd1
  rw [RateSplitAux.pdCx_add k hf0 hf1,
    RateSplitAux.pdCx_mul k hVc0 hd0, RateSplitAux.pdCx_mul k hVc1 hd1, e0, e1]
  unfold transC dTransC
  rw [c0, c1]
  ring

/-- `transC V Φ` is differentiable at `y` for a `C¹` field `V` and a smooth `Φ`. -/
theorem transC_differentiableAt {V : ℝ × ℝ → Fin 2 → ℝ} {Φ : ℝ × ℝ → ℂ} (hV : ContDiff ℝ 1 V)
    (hΦ : ContDiff ℝ ∞ Φ) (y : ℝ × ℝ) : DifferentiableAt ℝ (transC V Φ) y := by
  have hd0 : DifferentiableAt ℝ (pdCx 0 Φ) y := ((contDiff_pdCx 0 hΦ).differentiable (by simp)) y
  have hd1 : DifferentiableAt ℝ (pdCx 1 Φ) y := ((contDiff_pdCx 1 hΦ).differentiable (by simp)) y
  have hf0 : DifferentiableAt ℝ (fun z => ((V z 0 : ℝ) : ℂ) * pdCx 0 Φ z) y :=
    (ofReal_comp_differentiableAt hV 0 y).mul hd0
  have hf1 : DifferentiableAt ℝ (fun z => ((V z 1 : ℝ) : ℂ) * pdCx 1 Φ z) y :=
    (ofReal_comp_differentiableAt hV 1 y).mul hd1
  exact hf0.add hf1

/-- Linearity of `∂_k` on `-(c A + B - C)`. -/
theorem pdCx_neg_lin {A B C : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (k : Fin 2) (c : ℂ)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C x) :
    pdCx k (fun z => -(c * A z + B z - C z)) x = -(c * pdCx k A x + pdCx k B x - pdCx k C x) := by
  have h1 : DifferentiableAt ℝ (fun z => c * A z) x := hA.const_mul c
  have h2 : DifferentiableAt ℝ (fun z => c * A z + B z) x := h1.add hB
  unfold pdCx
  rw [fderiv_fun_neg, fderiv_fun_sub h2 hC, fderiv_fun_add h1 hB, fderiv_const_mul hA]
  simp only [neg_apply, sub_apply,
    add_apply, smul_apply, smul_eq_mul]

/-- **Leaf (calculus: `∂_k` of the reduced equation)** (SP 2858-2862): see `PsiDiff`. -/
theorem psiDiff : UnforcedLeray.Short.IIIa.AdjE1.PsiDiff := by
  intro a β V Φ χ g ha hΦ hV hχ hg h k y
  have hLap : DifferentiableAt ℝ (lapC Φ) y :=
    (((contDiff_pdCx 0 (contDiff_pdCx 0 hΦ)).add
      (contDiff_pdCx 1 (contDiff_pdCx 1 hΦ))).differentiable (by simp)) y
  have hT : DifferentiableAt ℝ (transC V Φ) y := transC_differentiableAt hV hΦ y
  have hχd : DifferentiableAt ℝ χ y := (hχ.differentiable (by simp)) y
  have hL := pdCx_const_mul_comp_smul k hg ((a : ℝ) : ℂ) (Real.sqrt a) y
  have hF : (fun z => ((a : ℝ) : ℂ) * g (Real.sqrt a • z)) =
      fun z => -((β : ℂ) * lapC Φ z + transC V Φ z - χ z) := funext h
  have hE : pdCx k (fun z => ((a : ℝ) : ℂ) * g (Real.sqrt a • z)) y =
      pdCx k (fun z => -((β : ℂ) * lapC Φ z + transC V Φ z - χ z)) y := by
    rw [hF]
  rw [hL, pdCx_neg_lin k (β : ℂ) hLap hT hχd] at hE
  rw [pdCx_lapC_eq hΦ k y, pdCx_transC_eq hV hΦ k y] at hE
  unfold xiRed
  push_cast at hE ⊢
  linear_combination (-1 : ℂ) * hE

end UnforcedLeray.Short.IIIa.AdjE1
