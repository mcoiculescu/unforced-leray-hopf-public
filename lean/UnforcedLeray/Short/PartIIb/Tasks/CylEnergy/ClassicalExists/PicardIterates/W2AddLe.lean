import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14

/-!

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

theorem pd_add_pt_w (j : Fin 2) {f g : B0579.Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : B0579.Plane) :
    B0579.pd j (fun y => f y + g y) x = B0579.pd j f x + B0579.pd j g x := by
  unfold B0579.pd
  have h : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    (hf x).hasFDerivAt.add (hg x).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem contDiff_one_pd_w {a : B0579.Plane → ℝ} (ha : ContDiff ℝ 2 a) (j : Fin 2) :
    ContDiff ℝ 1 (B0579.pd j a) := by
  unfold B0579.pd
  exact (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- **`PartII-b:T22/1/14/2`** `W2` is subadditive on `C²` functions. -/
theorem w2AddLe_proof : UnforcedLeray.Short.IIb.CylPDE.W2AddLe := by
  intro a b ha hb x
  have hda : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hdb : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hpa : ∀ j, Differentiable ℝ (B0579.pd j a) := fun j =>
    (contDiff_one_pd_w ha j).differentiable (by norm_num)
  have hpb : ∀ j, Differentiable ℝ (B0579.pd j b) := fun j =>
    (contDiff_one_pd_w hb j).differentiable (by norm_num)
  have hA : ∀ j y, B0579.pd j (fun z => a z + b z) y = B0579.pd j a y + B0579.pd j b y :=
    fun j y => pd_add_pt_w j hda hdb y
  have hB : ∀ i j y, B0579.pd i (B0579.pd j (fun z => a z + b z)) y =
      B0579.pd i (B0579.pd j a) y + B0579.pd i (B0579.pd j b) y := by
    intro i j y
    have hfun : B0579.pd j (fun z => a z + b z) = fun z => B0579.pd j a z + B0579.pd j b z :=
      funext (hA j)
    rw [hfun]
    exact pd_add_pt_w i (hpa j) (hpb j) y
  unfold W2
  simp only [hA, hB]
  have h1 := abs_add_le (a x) (b x)
  have h2 := abs_add_le (B0579.pd 0 a x) (B0579.pd 0 b x)
  have h3 := abs_add_le (B0579.pd 1 a x) (B0579.pd 1 b x)
  have h4 := abs_add_le (B0579.pd 0 (B0579.pd 0 a) x) (B0579.pd 0 (B0579.pd 0 b) x)
  have h5 := abs_add_le (B0579.pd 0 (B0579.pd 1 a) x) (B0579.pd 0 (B0579.pd 1 b) x)
  have h6 := abs_add_le (B0579.pd 1 (B0579.pd 0 a) x) (B0579.pd 1 (B0579.pd 0 b) x)
  have h7 := abs_add_le (B0579.pd 1 (B0579.pd 1 a) x) (B0579.pd 1 (B0579.pd 1 b) x)
  linarith

end CylPDE

end UnforcedLeray.Short.IIb

end
