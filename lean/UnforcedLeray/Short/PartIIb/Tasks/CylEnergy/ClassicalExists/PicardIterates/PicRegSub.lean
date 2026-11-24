import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14

/-!

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

theorem pd_sub_pt_r (j : Fin 2) {f g : B0579.Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : B0579.Plane) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x := by
  unfold B0579.pd
  have h : HasFDerivAt (fun y => f y - g y) (fderiv ℝ f x - fderiv ℝ g x) x :=
    (hf x).hasFDerivAt.sub (hg x).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem contDiff_one_pd_r {a : B0579.Plane → ℝ} (ha : ContDiff ℝ 2 a) (j : Fin 2) :
    ContDiff ℝ 1 (B0579.pd j a) := by
  unfold B0579.pd
  exact (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem pd2_sub_pt_r (i j : Fin 2) {f g : B0579.Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (y : B0579.Plane) :
    B0579.pd i (B0579.pd j (fun z => f z - g z)) y =
      B0579.pd i (B0579.pd j f) y - B0579.pd i (B0579.pd j g) y := by
  have hfun : B0579.pd j (fun z => f z - g z) = fun z => B0579.pd j f z - B0579.pd j g z :=
    funext (pd_sub_pt_r j (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)))
  rw [hfun]
  exact pd_sub_pt_r i ((contDiff_one_pd_r hf j).differentiable (by norm_num))
    ((contDiff_one_pd_r hg j).differentiable (by norm_num)) y

/-- **`PartII-b:T22/1/14/1`** `PicReg` is closed under differences. -/
theorem picRegSub_proof : UnforcedLeray.Short.IIb.CylPDE.PicRegSub := by
  intro c s T a b ha hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    exact (ha.c2 σ hσ).sub (hb.c2 σ hσ)
  · intro σ hσ x
    show a σ (x.1 + c, x.2) - b σ (x.1 + c, x.2) = a σ x - b σ x
    rw [ha.periodic σ hσ x, hb.periodic σ hσ x]
  · exact ha.cont0.sub hb.cont0
  · intro j
    refine ((ha.cont1 j).sub (hb.cont1 j)).congr ?_
    rintro ⟨σ, y⟩ ⟨hσ, -⟩
    show B0579.pd j (fun z => a σ z - b σ z) y = B0579.pd j (a σ) y - B0579.pd j (b σ) y
    exact pd_sub_pt_r j ((ha.c2 σ hσ).differentiable (by norm_num))
      ((hb.c2 σ hσ).differentiable (by norm_num)) y
  · intro i j
    refine ((ha.cont2 i j).sub (hb.cont2 i j)).congr ?_
    rintro ⟨σ, y⟩ ⟨hσ, -⟩
    show B0579.pd i (B0579.pd j (fun z => a σ z - b σ z)) y =
      B0579.pd i (B0579.pd j (a σ)) y - B0579.pd i (B0579.pd j (b σ)) y
    exact pd2_sub_pt_r i j (ha.c2 σ hσ) (hb.c2 σ hσ) y

end CylPDE

end UnforcedLeray.Short.IIb

end
