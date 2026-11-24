import UnforcedLeray.Units.B0412.Action
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_2

/-!
# `RealCBound`: the real inclusion `realC` is a linear isometry

Source `the November 2 reference manuscript`
lines 2542-2548, 2563-2569, 1206-1222. `realC x = (x_i : ℂ)_i` is real-linear and norm
preserving, so composition with it leaves every iterated Fréchet derivative norm unchanged.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `realC` as a real linear isometry `ℝ³ → ℂ³`. -/
def realCLI : UnforcedLeray.Space →ₗᵢ[ℝ] CVec3 where
  toFun := UnforcedLeray.B0412.realC
  map_add' x y := by
    ext i
    simp [UnforcedLeray.B0412.realC_apply]
  map_smul' c x := by
    ext i
    simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, UnforcedLeray.B0412.realC_apply, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]

theorem realCBound : RealCBound := by
  intro r k y hr
  have hfun : (fun x : UnforcedLeray.Space => UnforcedLeray.B0412.realC (r x)) = realCLI ∘ r := rfl
  rw [hfun]
  have h := realCLI.norm_iteratedFDeriv_comp_left (x := y) (f := r) (n := ∞) hr.contDiffAt
    (i := k) (by exact_mod_cast le_top)
  exact h.le

end UnforcedLeray.Short.PartIIIb.Concrete
