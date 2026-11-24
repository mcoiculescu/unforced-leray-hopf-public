import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.ProdIsProfileTest
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.DivPairing.InnerCore
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# `DivPairing` (`PartII-a:N01/9/1/1/3/2/3`), source lines 1684-1689

Pairing with the profile gradient `cgrad 0 (θ(s)ψ)` = `(θ ∂_qψ, θ ∂_ηψ)` (an element of
`(solenoidalHC 0 c)ᗮ`, since it lies in the span of the generators) is the weighted slice
divergence integral `∫ θ(s) s^{-3/2} divI(slice_s) ds`, by `InnerCore.innerCore`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open InnerCore

theorem divPairing : UnforcedLeray.Short.PartIIa.N01.Sub.DivPairing := by
  intro c hc θ ψ hθ hψ
  have hΦ : UnforcedLeray.B0226.IsProfileTest c (prodFn θ ψ) := prodIsProfileTest c θ ψ hθ hψ
  have hmem : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 (prodFn θ ψ)) 2 (measureH c) :=
    UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad hΦ
  have hdiff : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hθd : Differentiable ℝ θ := hθ.1.differentiable (by simp)
  have hVdef : ∀ p : Profile, UnforcedLeray.Short.PartIIa.cgrad 0 (prodFn θ ψ) p =
      !₂[((θ p.1 * fderiv ℝ ψ p.2 (1, 0) : ℝ) : ℂ), ((θ p.1 * fderiv ℝ ψ p.2 (0, 1) : ℝ) : ℂ)] := by
    intro p
    have e1 : UnforcedLeray.Axi.dQ (prodFn θ ψ) p = θ p.1 * fderiv ℝ ψ p.2 (1, 0) := by
      show fderiv ℝ (fun y : Profile => θ y.1 * ψ y.2) p (0, (1, 0)) = _
      rw [fderiv_prodFn_apply hθd hdiff]
      simp
    have e2 : UnforcedLeray.Axi.dEta (prodFn θ ψ) p = θ p.1 * fderiv ℝ ψ p.2 (0, 1) := by
      show fderiv ℝ (fun y : Profile => θ y.1 * ψ y.2) p (0, (0, 1)) = _
      rw [fderiv_prodFn_apply hθd hdiff]
      simp
    unfold UnforcedLeray.Short.PartIIa.cgrad
    rw [UnforcedLeray.B0226.Deps_zero, e1, e2]
  have hb0 : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => fderiv ℝ ψ z (1, 0)) :=
    UnforcedLeray.Short.PartIIa.N01.Sub.InnerCore.isPeriodic_of_cylTest (hψ.dirDeriv (1, 0))
  have hb1 : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => fderiv ℝ ψ z (0, 1)) :=
    UnforcedLeray.Short.PartIIa.N01.Sub.InnerCore.isPeriodic_of_cylTest (hψ.dirDeriv (0, 1))
  refine ⟨hmem.toLp (UnforcedLeray.Short.PartIIa.cgrad 0 (prodFn θ ψ)), ?_, ?_⟩
  · unfold UnforcedLeray.Short.PartIIa.solenoidalHC
    exact Submodule.le_orthogonal_orthogonal _
      (Submodule.subset_span ⟨⟨prodFn θ ψ, hΦ⟩, hmem, rfl⟩)
  · intro h
    exact UnforcedLeray.Short.PartIIa.N01.Sub.InnerCore.innerCore hc hθ hb0 hb1 hVdef hmem h

end UnforcedLeray.Short.PartIIa.N01.Sub
