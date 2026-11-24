import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3

/-!
# Differentiation under the integral sign on an open set (task `PartIII-b:C/srcL/6/3/1`)

Proves `XSParamSmoothOpen` (see `Sub/PartIII-b_C_srcL_6_3.lean`).  The family `F σ` is only
assumed smooth on the open set `U`, and the local domination hypothesis is stated on `U`, so the
set-local parametric-integral theorem `UnforcedLeray.L09.contDiffOn_integral` applies directly
with `μ = volume.restrict (Ioi 1)`; no bump-function localisation is needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xsParamSmoothOpen : XSParamSmoothOpen := by
  intro U F hU hF hmeas hdom
  have hsmooth : ∀ᵐ σ ∂(volume.restrict (Ioi (1 : ℝ))),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F σ) U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ using hF σ hσ
  have hdom' : UnforcedLeray.L09.LocDominated (volume.restrict (Ioi (1 : ℝ))) F U := by
    intro n x hx
    obtain ⟨s, hs, g, hg, hb⟩ := hdom n x hx
    refine ⟨s, hs, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact fun y hy => hb σ hσ y hy
  exact UnforcedLeray.L09.contDiffOn_integral hU hsmooth
    (fun n x hx => hmeas n x hx) hdom'

end UnforcedLeray.Short.PartIIIb.Concrete
