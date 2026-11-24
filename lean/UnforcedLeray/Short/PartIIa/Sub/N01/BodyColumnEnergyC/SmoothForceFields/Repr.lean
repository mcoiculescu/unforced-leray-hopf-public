import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2
import UnforcedLeray.Units.B0225

/-!
# `PartII-a:N01/9/1/2/1`: `smoothForceRepr`

Source `shorter-proof-2026-11-02.tex` 3379-3383.  For `g = F` a.e. with `F` continuous,
`B0225.R0_ae_eq` gives `R₀(μ)g(p) = ∫₀^∞ e^{-μt} jointRep F (t,p) dt` a.e.; since
`σ • (F/σ) = F`, `jointRep F (t,p) = σ • ψ(σ)` with `σ = e^{-t}p₁`, and
`B0225.integral_substitution` turns this into `∫₀^{p₁} (σ/p₁)^μ ψ(σ) dσ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

theorem smoothForceRepr : UnforcedLeray.Short.PartIIa.N01.SmoothForceRepr := by
  intro c ν hc hν μ hμ g hg F hF hgF
  have hFm : StronglyMeasurable F := hF.1.continuous.stronglyMeasurable
  obtain ⟨-, h2⟩ := UnforcedLeray.B0225.R0_ae_eq hc ν hμ (g : HSpace c MeridC) hFm hgF.symm
  filter_upwards [h2, UnforcedLeray.B0220.ae_cell_measureH c] with p hp hcell
  have hs : 0 < p.1 := hcell.1
  rw [hp]
  unfold smoothHeatInt
  rw [← UnforcedLeray.B0225.integral_substitution hs μ]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  congr 1
  have hσ : 0 < Real.exp (-t) * p.1 := mul_pos (Real.exp_pos _) hs
  unfold UnforcedLeray.B0225.jointRep
  have h1 : ν * p.1 * (1 - Real.exp (-t)) = ν * (p.1 - Real.exp (-t) * p.1) := by ring
  have key := congrFun (UnforcedLeray.B0224.planeHeat_smul (ν * (p.1 - Real.exp (-t) * p.1))
    (Real.exp (-t) * p.1)
    (fun z => UnforcedLeray.B0220.periodize c (fun q : Profile => (q.1)⁻¹ • F q)
      (Real.exp (-t) * p.1, z))) p.2
  rw [h1]
  refine Eq.trans ?_ key
  show UnforcedLeray.B0224.planeHeat _ _ _ = UnforcedLeray.B0224.planeHeat _ _ _
  congr 1
  funext z
  unfold UnforcedLeray.B0220.periodize
  simp only [smul_smul]
  rw [mul_inv_cancel₀ hσ.ne', one_smul]

end UnforcedLeray.Short.PartIIa.N01
