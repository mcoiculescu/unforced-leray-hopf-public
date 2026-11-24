import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs

/-!
# `PartIII-b:C/rep/8/3/2/3`: linearity of the affine expression in the profile (source 5466-5486)

`ringAffGen` is linear in the flat profile `(v, p)`: for `C²` velocity slices and differentiable
pressure slices the expression of a difference is the difference of the expressions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `emb` is additive. -/
theorem rs_emb_sub (a b : ℝ × ℝ) : emb (a - b) = emb a - emb b := by
  funext i
  fin_cases i <;> simp [emb]

/-- `mv B` is additive on embedded meridional vectors. -/
theorem rs_mv_emb_sub (B : Mat3) (a b : ℝ × ℝ) :
    mv B (emb (a - b)) = mv B (emb a) - mv B (emb b) := by
  rw [rs_emb_sub]
  funext i
  simp only [mv, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [Pi.sub_apply, mul_sub]

/-- Differentiability of `y ↦ fderiv V y (e)` for `C²` maps `V`. -/
theorem rs_fderiv_apply_diff {V : ℝ × ℝ → ℝ × ℝ} (hV : ContDiff ℝ 2 V) (e : ℝ × ℝ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y => fderiv ℝ V y e) x := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (m := 1) (by norm_num)
  exact ((h1.clm_apply contDiff_const).differentiable (by norm_num)) x

/-- The contracted Hessian is additive in the profile. -/
theorem rs_hessContr_sub (A : Mat3) (V W : ℝ × ℝ → ℝ × ℝ) (hV : ContDiff ℝ 2 V)
    (hW : ContDiff ℝ 2 W) (x : ℝ × ℝ) :
    hessContr A (fun y => V y - W y) x = hessContr A V x - hessContr A W x := by
  have hk : ∀ b : Fin 2, (fun y => fderiv ℝ (fun y => V y - W y) y (ei b)) =
      fun y => fderiv ℝ V y (ei b) - fderiv ℝ W y (ei b) := by
    intro b
    funext y
    have e : fderiv ℝ (fun y => V y - W y) y = fderiv ℝ V y - fderiv ℝ W y :=
      fderiv_sub (hV.differentiable (by norm_num) y) (hW.differentiable (by norm_num) y)
    rw [e]
    rfl
  have hd : ∀ b : Fin 2, fderiv ℝ (fun y => fderiv ℝ (fun y => V y - W y) y (ei b)) x =
      fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x - fderiv ℝ (fun y => fderiv ℝ W y (ei b)) x := by
    intro b
    rw [hk b]
    exact fderiv_sub (rs_fderiv_apply_diff hV (ei b) x) (rs_fderiv_apply_diff hW (ei b) x)
  unfold hessContr
  simp only [hd, smul_sub, Finset.sum_sub_distrib, sub_apply]
  rw [← rs_emb_sub]

/-- **Linearity of the affine expression in the profile** (`RingAffGenSub`, source 5466-5486). -/
theorem ringAffGenSub : RingAffGenSub := by
  intro ν μ χf A v₁ v₂ p₁ p₂ s x h1 h2 h3 h4
  unfold ringAffGen
  beta_reduce
  have hfd : fderiv ℝ (fun y => p₁ s y - p₂ s y) x = fderiv ℝ (p₁ s) x - fderiv ℝ (p₂ s) x :=
    fderiv_sub (h3.differentiableAt) (h4.differentiableAt)
  have hp : mgrad (fun y => p₁ s y - p₂ s y) x = mgrad (p₁ s) x - mgrad (p₂ s) x := by
    unfold mgrad
    rw [hfd]
    ext <;> simp
  rw [rs_hessContr_sub _ (v₁ s) (v₂ s) h1 h2 x, hp]
  simp only [rs_mv_emb_sub, smul_sub]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
