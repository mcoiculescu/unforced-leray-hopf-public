import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Sub-lemma 3** (source 1580-1583): the weak formulation is additive along the lift of
`VelG`. Proved in `PhysLayer/WeakDmuAdd.lean` as `weakDmuAdd`. -/
theorem weakDmuAdd_proved (c γ ν ε μ : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) :
    WeakDmuAdd c γ ν ε μ :=
  weakDmuAdd hc hν hε

end UnforcedLeray.Short.PartIIIb.Concrete
