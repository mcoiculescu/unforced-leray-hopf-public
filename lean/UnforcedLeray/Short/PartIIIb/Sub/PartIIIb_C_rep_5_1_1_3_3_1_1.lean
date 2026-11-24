import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3.Tail

/-!
# `PartIII-b:C/rep/5/1/1/3/3/1/1`: `tailBoxThinSeq'` from its three analytic leaves

Source `the November 2 reference manuscript`
5585-5593 (bins), 3604-3621 (kernel gradient), 5569-5575 (Cauchy-Schwarz on the cell).

Leaves: `FarPointDom` (witness constant), `AgeMassLeThin`, `WardYMajBinCore`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tailBoxThinSeq'_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hP : ∃ C : ℝ, FarPointDom C)
    (hA : AgeMassLeThin) (hcore : WardYMajBinCore) : TailBoxThinSeq Pl σ₀ mZ dm dp :=
  tailBoxThinSeq_of Pl σ₀ mZ dm dp hP (tailMajBinSeq_of Pl σ₀ mZ dm dp hcore hA)

end UnforcedLeray.Short.PartIIIb.Concrete
