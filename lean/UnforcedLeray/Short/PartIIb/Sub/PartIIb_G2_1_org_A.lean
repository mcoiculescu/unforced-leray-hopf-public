import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.PhysUniqueCross
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.Linearity

/-!
# `PartII-b:G2/1/org/A`: `PhysRespLinComb`

Source: `the November 2 reference manuscript` lines 1665-1672.  `IsResponse` is
closed under `a • _ + _` (`isResponse_smul`, `isResponse_add`) and depends on `(F, b)` only up to
`hMeas`-a.e. equality (`nvC_ae_eq_of_ae_pos`, `freeResponseCongr_proof`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open HrOpHelp

theorem physRespLinComb_proof : PhysRespLinComb := by
  intro ν c ε hν hc hε a F₁ F₂ b₁ b₂ F b hF₁ hF₂ hb₁ hb₂ hF hb h₁ h₂ hFe hbe
  have hr1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hP : 0 < 2 * ε * c := by positivity
  have hs := isResponse_add hc hε hr1 (inHr_smul (a : ℂ) hF₁) hF₂
    (inHr_smul (a : ℂ) hb₁) hb₂ (isResponse_smul (a : ℂ) hc hε hr1 hF₁ hb₁ h₁) h₂
  have hFs : InHr c bgp ((a : ℂ) • F₁ + F₂) := inHr_add (inHr_smul (a : ℂ) hF₁) hF₂
  have hbs : InHr c bgp ((a : ℂ) • b₁ + b₂) := inHr_add (inHr_smul (a : ℂ) hb₁) hb₂
  have hFv : ∀ᵐ x : Coord, 0 < x.1 → F x = ((a : ℂ) • F₁ + F₂) x :=
    CongrHelp.ae_volume_of_ageμ hc hF.periodic hFs.periodic hFe
  have hbv : ∀ᵐ x : Coord, 0 < x.1 → b x = ((a : ℂ) • b₁ + b₂) x :=
    CongrHelp.ae_volume_of_ageμ hc hb.periodic hbs.periodic hbe
  exact freeResponseCongr_proof ν 0 bgp (2 * ε * c) _ _ _ _ hP
    (nvC_ae_eq_of_ae_pos hc hε hFs hF (hFv.mono fun x h hx => (h hx).symm))
    (nvC_ae_eq_of_ae_pos hc hε hbs hb (hbv.mono fun x h hx => (h hx).symm)) hs
