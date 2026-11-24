import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem odRepAlg : OD_RepAlg := by
  intro p ψ Ψ Ψτ ΨΔ Ψx Ψ' hΨ hΨτ hΨΔ hΨx hΨ'
  refine Lp.ext ?_
  filter_upwards [hΨ', hΨτ, hΨΔ, hΨx, hΨ,
    Lp.coeFn_add (((p.ν * p.ε ^ 2 : ℝ) : ℂ) • ΨΔ - ((1 / 2 : ℝ) : ℂ) • Ψx - Ψ) Ψτ,
    Lp.coeFn_sub (((p.ν * p.ε ^ 2 : ℝ) : ℂ) • ΨΔ - ((1 / 2 : ℝ) : ℂ) • Ψx) Ψ,
    Lp.coeFn_sub (((p.ν * p.ε ^ 2 : ℝ) : ℂ) • ΨΔ) (((1 / 2 : ℝ) : ℂ) • Ψx),
    Lp.coeFn_smul (((p.ν * p.ε ^ 2 : ℝ) : ℂ)) ΨΔ,
    Lp.coeFn_smul (((1 / 2 : ℝ) : ℂ)) Ψx] with z hz' hτ hΔ hx h0 hadd hsub1 hsub2 hs1 hs2
  simp only [hadd, hsub1, hsub2, hs1, hs2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    ]
  rw [hz', hτ, hΔ, hx, h0]
  simp only [outerGenT, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end UnforcedLeray.Short.PartIIIb.NearInst
