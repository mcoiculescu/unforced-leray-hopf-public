import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.AyContDiff

/-!
# `bmat54_continuousOn`: `B = (A^y)' + μ A^y / s` is continuous on `s > 0`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`A^y = χ_f(ν ·) A` is `C⁶` on `(0,∞)` (`ay54_contDiffOn`), so its derivative is `C⁵` there,
hence continuous, and `μ/s` is continuous on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bmat54_continuousOn (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ)
    (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ContinuousOn (Bmat ν μ χf A) (Ioi (0 : ℝ)) := by
  have hAy : ContDiffOn ℝ ((6 : ℕ) : WithTop ℕ∞) (Ay ν χf A) (Ioi (0 : ℝ)) :=
    ay54_contDiffOn as χf hχ ν A hA
  have hd : ContinuousOn (deriv (Ay ν χf A)) (Ioi (0 : ℝ)) :=
    hAy.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h2 : ContinuousOn (fun s : ℝ => (μ / s) • Ay ν χf A s) (Ioi (0 : ℝ)) :=
    (continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt hs)).smul hAy.continuousOn
  exact hd.add h2

end UnforcedLeray.Short.PartIIIb.Concrete
