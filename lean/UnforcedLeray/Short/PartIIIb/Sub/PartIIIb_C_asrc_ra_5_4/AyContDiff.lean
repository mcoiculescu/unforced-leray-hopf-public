import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `ay54_contDiffOn`: `A^y = χ_f(ν ·) A` is `C⁶` on `s > 0`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978,
with `A` in the affine class `𝒜` (lines 4741-4745) and the cutoff `χ_f` (lines 4750-4752, 4955-4956).
`Ay ν χ A s = χ (ν * s) • A s`; the scalar factor is `C^∞` and `A` is `C⁶` on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ay54_contDiffOn (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ)
    (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ContDiffOn ℝ ((6 : ℕ) : WithTop ℕ∞) (Ay ν χf A) (Ioi (0 : ℝ)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => χf (ν * s)) :=
    hχ.smooth.comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiffOn ℝ ((6 : ℕ) : WithTop ℕ∞) (fun s : ℝ => χf (ν * s)) (Ioi (0 : ℝ)) :=
    (h1.of_le (by simp)).contDiffOn
  have h6 : ContDiffOn ℝ ((6 : ℕ) : WithTop ℕ∞) A (Ioi (0 : ℝ)) := by
    exact_mod_cast hA.smooth
  exact ContDiffOn.smul h2 h6

end UnforcedLeray.Short.PartIIIb.Concrete
