import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D1

/-!
# `PartIII-b:C/rep/8/2/6/2/3`: the second flat train derivatives are symmetric

Source `the November 2 reference manuscript` lines 5463-5465 (the train is smooth).
The flat second derivative `flatD2 L s x j l` is the second derivative of `trainV L s` in the flat
directions `flatDir j`, `flatDir l`; its symmetry is Schwarz's theorem for the `C^∞` map
`trainV L s` on the open set `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The second derivative of `f` applied to a fixed direction `w` in the first slot, symmetric
form: `∂_v (∂_· f · w) = ∂²f (v, w)`. -/
theorem fderiv_fderiv_apply_fixed_ring (f : ℝ × ℝ → ℝ × ℝ) (x w v : ℝ × ℝ)
    (hf : ContDiffAt ℝ ∞ f x) :
    fderiv ℝ (fun x' => fderiv ℝ f x' w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  rw [show (fun x' => fderiv ℝ f x' w) = (fun y => (fderiv ℝ f y) ((fun _ => w) y)) from rfl,
    fderiv_clm_apply hc (differentiableAt_const w)]
  simp

/-- `trainV L s` is `C^∞` at every point of `s > 0`. -/
theorem trainV_contDiffAt_ring (L : ReturnLevel) {s : ℝ} (hs : 0 < s) (x : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (trainV L s) x := by
  rw [trainV_eq_comp_ring L hs]
  exact (vecPairRing.contDiff.contDiffAt).comp x
    ((trainFv_contDiffAt_ring L (Real.log s, x)).comp x
      (contDiffAt_const.prodMk contDiffAt_id))

/-- **`TrainFlatD2Symm`** (source 5463-5465): `∂_j∂_l v = ∂_l∂_j v`. -/
theorem trainFlatD2Symm (L : ReturnLevel) : TrainFlatD2Symm L := by
  intro s hs x j l
  have hf := trainV_contDiffAt_ring L hs x
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  unfold flatD2
  rw [fderiv_fderiv_apply_fixed_ring (trainV L s) x (flatDir l) (flatDir j) hf,
    fderiv_fderiv_apply_fixed_ring (trainV L s) x (flatDir j) (flatDir l) hf]
  rw [hsymm (flatDir j) (flatDir l)]

end UnforcedLeray.Short.PartIIIb.Concrete
