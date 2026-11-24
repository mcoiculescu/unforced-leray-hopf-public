import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_of
import UnforcedLeray.Units.B0414.Orthogonal
import UnforcedLeray.Lib.LerayLp.Helmholtz

/-!
# `PartII-b:T10/org/2/3/1`: `LerayCFixed` (`𝐏w = w` for solenoidal `w ∈ L^p(ℝ³;ℂ³)`)

Source `the November 2 reference manuscript` (SP solenoidal fixed point).
Route: `isSolenoidalC_iff` gives solenoidality of `Re w` and `Im w`; `RieszLp.lerayLp_eq_self`
fixes each real part; `lerayC_apply` and the real/imaginary decomposition reassemble `w`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0414 UnforcedLeray.RieszLp

/-- Solenoidality is invariant under almost-everywhere equality (cf. `ssf_isSolenoidal_congr`). -/
theorem lerayCFixed_congr {f g : Space → Space} (hf : IsSolenoidal f)
    (hfg : f =ᵐ[volume] g) : IsSolenoidal g where
  integrable ψ hψ := (hf.integrable ψ hψ).congr (hfg.mono fun x hx => by simp only [hx])
  identity ψ hψ :=
    (integral_congr_ae (hfg.symm.mono fun x hx => by simp only [hx])).trans (hf.identity ψ hψ)

theorem lerayCFixed_proof : UnforcedLeray.Short.IIb.LerayCFixed := by
  intro p _ h1 h2 w hsol
  obtain ⟨hre, him⟩ := (isSolenoidalC_iff (w : Space → CVec3)).1 hsol
  have hreL : IsSolenoidal ((reV.compLpL p volume w : Lp Space p (volume : Measure Space)) :
      Space → Space) :=
    lerayCFixed_congr hre (reV.coeFn_compLpL (μ := volume) (p := p) w).symm
  have himL : IsSolenoidal ((imV.compLpL p volume w : Lp Space p (volume : Measure Space)) :
      Space → Space) :=
    lerayCFixed_congr him (imV.coeFn_compLpL (μ := volume) (p := p) w).symm
  have hL1 : lerayLp p h1 h2 (reV.compLpL p volume w) = reV.compLpL p volume w :=
    lerayLp_eq_self h1 h2 _ hreL
  have hL2 : lerayLp p h1 h2 (imV.compLpL p volume w) = imV.compLpL p volume w :=
    lerayLp_eq_self h1 h2 _ himL
  rw [lerayC_apply, hL1, hL2]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofReV.compLpL p volume (reV.compLpL p volume w))
      (ofImV.compLpL p volume (imV.compLpL p volume w)),
    ofReV.coeFn_compLpL (μ := volume) (p := p) (reV.compLpL p volume w),
    ofImV.coeFn_compLpL (μ := volume) (p := p) (imV.compLpL p volume w),
    reV.coeFn_compLpL (μ := volume) (p := p) w,
    imV.coeFn_compLpL (μ := volume) (p := p) w] with x h0 h1' h2' h3 h4
  rw [h0, Pi.add_apply, h1', h2', h3, h4]
  exact ofReV_reV_add_ofImV_imV (w x)

end UnforcedLeray.Short.IIb
