import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_3

/-!
# Decomposition of `scCylComp` (source 4161-4166, 4178-4186)

`SCCylComp` (composition of a one-variable function with `cylR`) follows from the homogeneous
derivative bound `‖D^i cylR y‖ ≤ K_i r^{1-i}` (`SCCylDeriv`) by Faà di Bruno
(`norm_iteratedFDeriv_comp_le`) on the ball `B(y, r/2)` (`SCCylCompOfDeriv`).
Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Homogeneous derivative bounds for `cylR` (4178-4186): `cylR y = √(y₀²+y₁²)` is homogeneous of
degree 1 in `(y₀,y₁)` and independent of `y₂`, so `D^i cylR(y) = r^{1-i} D^i cylR(y/r)` (scaling in
the first two variables), and `D^i cylR` is bounded on `{y₀²+y₁²=1}` (continuous, independent of
`y₂`, compact circle). -/
def SCCylDeriv : Prop :=
  ∀ i : ℕ, i ≤ 7 → ∃ K : ℝ, ∀ y : Vec3, 0 < cylR y →
    ‖iteratedFDeriv ℝ i cylR y‖ ≤ K * cylR y ^ ((1 : ℝ) - i)

/-- Faà di Bruno step: given `SCCylDeriv`, `SCCylComp` holds.  On `B(y, r/2)` (`r = cylR y`;
`|cylR z - cylR y| ≤ ‖z-y‖`, so `cylR ≥ r/2` there) rescale `z = y + r w`, `g(w) = cylR(y+rw)/r`
and `φ(s)=f(r s)`: `‖D^i g‖ ≤ K_i'` on `‖w‖<1/2`, `|φ^{(k)}| ≤ A r^{-p} 2^{p+k}`; apply
`norm_iteratedFDeriv_comp_le` (or the `'` version) at `w=0` and undo the scaling
(`ContinuousLinearMap.norm_iteratedFDeriv_comp_right`-type scaling gives the factor `r^{-m}`). -/
def SCCylCompOfDeriv : Prop := SCCylDeriv → SCCylComp

theorem scCylComp_of (h1 : SCCylDeriv) (h2 : SCCylCompOfDeriv) : SCCylComp := h2 h1

end UnforcedLeray.Short.PartIIIb.Concrete
