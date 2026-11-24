import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

/-!
# `PartIII-b:C/rep/8/1/1/2/4/org`: the ray symmetry of the zero-width young field — statement

Source `the November 2 reference manuscript`
lines 4771-4782 (the zero-width Newton field `V_{μ,M}` of the axisymmetric Cartesian source
`Σ_M(x') = Q(φ)(ρ⁻¹E)Q(φ)ᵀ`), 4784 (`W^mt_μ(y) = ε² V_μ(εy)`), 4917-4937 (rotation covariance of
`V_μ` off the old source disc), 4180-4182 (the outward primitive along the ray through `y`).

This file imports only `Concrete/SourceL.lean`, so that the statement can be imported both by the
`rep_8_1` chain (`GeomY/AsmYA.lean`) and by its proof (`AsmYA/YoungAzi.lean`, which uses
`newtonVEquivariant` of `SourceL/Sub/PartIII-b_C_srcL_7`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The `z`-component of `W^mt_μ` is the same on all outward rays** (source 4771-4784,
4917-4937): at the point of radius `ρ` on the outward ray through `w` (`rayPt w ρ`, azimuth of
`w`, height `w₃`) and at `(ρ, 0, w₃)` the vertical components agree, for `5ν/6 < (ερ)²` (off the
old source disc, where `V_μ` commutes with the rotations about the axis). -/
def YoungWRayAzi : Prop :=
  ∀ (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
    ∀ w : Vec3, 0 < cylR w → ∀ ρ : ℝ, 5 * ν / 6 < (ε * ρ) ^ 2 →
      youngW c ν ε μ χo M (rayPt w ρ) 2 = youngW c ν ε μ χo M ![ρ, 0, w 2] 2

end UnforcedLeray.Short.PartIIIb.Concrete
