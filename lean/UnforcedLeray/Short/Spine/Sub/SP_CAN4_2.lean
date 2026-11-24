import UnforcedLeray.Short.Spine.Sub.SP_CAN4

/-!
# Spine: `MildIsStrong` reduced to the domain-derivative lemma (task `Spine:SP-CAN/4/2`)

Source: `the November 2 reference manuscript` line 1086 ("smooth for positive
`θ`") and lines 1134-1145 (`X_{G,j}`, `X_{G,2} = 𝒟(D)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- Core of step 2 (shorter proof line 1086, 1134-1145): a mild `V` that is continuous into every
`X_{G,j}` and takes values in `𝒟(D)` for `θ > 0` is differentiable in `X_G` with derivative
`-(L₀ V θ + θ⁻¹ D V θ)`. Proof: differentiate the Duhamel identity
`V θ = e^{log(θ''/θ) D} V θ'' + ∫_θ^θ'' e^{log(v/θ) D} L₀ V v dv` in `θ`
(`S_mild`, `B0123.expD_smoothing`, `hasDerivAt_expD_apply_domain`). -/
def MildDomainDerivative : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsMildOnPos V → IsXGjContinuous V →
    ∀ θ : ℝ, 0 < θ → ∀ h : V θ ∈ B0094.D.domain,
      HasDerivAt V (-(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩)) θ

theorem mildIsStrong_of (hS : MildSpatialSmoothing) (hD : MildDomainDerivative) :
    MildIsStrong := by
  intro hE V hV θ hθ
  obtain ⟨U, hU, -⟩ := hS hE V hV 2
  obtain ⟨h2, -⟩ := hU θ hθ
  have h : V θ ∈ B0094.D.domain := by
    rw [← B0123.XGj_two]; exact h2
  exact ⟨h, hD hE V hV (hS hE V hV) θ hθ h⟩

end UnforcedLeray.Short.Spine
