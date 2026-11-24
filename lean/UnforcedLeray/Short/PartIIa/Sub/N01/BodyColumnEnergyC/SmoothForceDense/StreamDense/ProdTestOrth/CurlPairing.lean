import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.ProdIsProfileTest
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.ProdIsStreamFn
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.DivPairing.InnerCore
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# `CurlPairing` (`PartII-a:N01/9/1/1/3/2/4`), source lines 1684-1689

Pairing with the stream field `(∂_η(θψ), -∂_q(θψ))` (an element of `StreamSet c`, via
`ProdIsStreamFn`) is the weighted slice curl integral `∫ θ(s) s^{-3/2} curlI(slice_s) ds`, by
`InnerCore.innerCore` with `b₀ = ∂_ηψ`, `b₁ = -∂_qψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open InnerCore

/-- The complex stream field of a real `Φ`: its components are the cast partial derivatives. -/
theorem streamField_ofReal_apply {Φ : Profile → ℝ} (hΦ : Differentiable ℝ Φ) (p : Profile) :
    UnforcedLeray.Short.PartIIa.N01.StreamField (fun y : Profile => ((Φ y : ℝ) : ℂ)) p =
      !₂[((fderiv ℝ Φ p (0, 0, 1) : ℝ) : ℂ), -((fderiv ℝ Φ p (0, 1, 0) : ℝ) : ℂ)] := by
  unfold UnforcedLeray.Short.PartIIa.N01.StreamField UnforcedLeray.Short.PartIIa.pdEta
    UnforcedLeray.Short.PartIIa.pdQ
  rw [fderiv_ofReal_apply hΦ, fderiv_ofReal_apply hΦ]

/-- The stream field of a real band test is in `L²(measureH c)`. -/
theorem streamField_memLp {c : ℝ} {Φ : Profile → ℝ} (hΦ : UnforcedLeray.B0226.IsProfileTest c Φ) :
    MemLp (UnforcedLeray.Short.PartIIa.N01.StreamField (fun p : Profile => ((Φ p : ℝ) : ℂ)))
      2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  have hdiff : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hΨ := Complex.ofRealCLM.contDiff.comp hΦ.smooth
  have hD : Continuous (fderiv ℝ (fun p : Profile => ((Φ p : ℝ) : ℂ))) :=
    hΨ.continuous_fderiv (by simp)
  have h1 : Continuous fun p : Profile => fderiv ℝ (fun y : Profile => ((Φ y : ℝ) : ℂ)) p (0, 0, 1) :=
    hD.clm_apply continuous_const
  have h2 : Continuous fun p : Profile => fderiv ℝ (fun y : Profile => ((Φ y : ℝ) : ℂ)) p (0, 1, 0) :=
    hD.clm_apply continuous_const
  have hcont : Continuous
      (UnforcedLeray.Short.PartIIa.N01.StreamField (fun p : Profile => ((Φ p : ℝ) : ℂ))) := by
    unfold UnforcedLeray.Short.PartIIa.N01.StreamField UnforcedLeray.Short.PartIIa.pdEta
      UnforcedLeray.Short.PartIIa.pdQ
    exact UnforcedLeray.Short.PartIIa.NearGradMemberAux.continuous_mk h1 h2.neg
  refine UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_of_band (c := c) (s0 := s0)
    (s1 := s1) (L := L) hcont hs0 ?_
  intro p hp
  have hnot : p ∉ tsupport Φ := fun hmem => hp (UnforcedLeray.B0226.tsupport_subset_band hb hmem)
  have hd : fderiv ℝ Φ p = 0 := fderiv_of_notMem_tsupport ℝ hnot
  unfold UnforcedLeray.Short.PartIIa.N01.StreamField UnforcedLeray.Short.PartIIa.pdEta
    UnforcedLeray.Short.PartIIa.pdQ
  rw [fderiv_ofReal_apply hdiff, fderiv_ofReal_apply hdiff, hd]
  ext i
  fin_cases i <;> simp

theorem curlPairing : UnforcedLeray.Short.PartIIa.N01.Sub.CurlPairing := by
  intro c hc θ ψ hθ hψ
  have hΨ := prodIsStreamFn c θ ψ hθ hψ
  have hΦ : UnforcedLeray.B0226.IsProfileTest c (prodFn θ ψ) := prodIsProfileTest c θ ψ hθ hψ
  have hdiffΦ : Differentiable ℝ (prodFn θ ψ) := hΦ.smooth.differentiable (by simp)
  have hdiff : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hθd : Differentiable ℝ θ := hθ.1.differentiable (by simp)
  have hmemV := streamField_memLp hΦ
  have hb0 : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => fderiv ℝ ψ z (0, 1)) :=
    isPeriodic_of_cylTest (hψ.dirDeriv (0, 1))
  have hb1 : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => (-1 : ℝ) * fderiv ℝ ψ z (1, 0)) :=
    isPeriodic_of_cylTest ((hψ.dirDeriv (1, 0)).smul (-1))
  have hVdef : ∀ p : Profile,
      UnforcedLeray.Short.PartIIa.N01.StreamField (fun y : Profile => ((prodFn θ ψ y : ℝ) : ℂ)) p =
        !₂[((θ p.1 * fderiv ℝ ψ p.2 (0, 1) : ℝ) : ℂ),
          ((θ p.1 * ((-1 : ℝ) * fderiv ℝ ψ p.2 (1, 0)) : ℝ) : ℂ)] := by
    intro p
    rw [streamField_ofReal_apply hdiffΦ]
    have e1 : fderiv ℝ (prodFn θ ψ) p (0, 0, 1) = θ p.1 * fderiv ℝ ψ p.2 (0, 1) := by
      show fderiv ℝ (fun y : Profile => θ y.1 * ψ y.2) p (0, 0, 1) = _
      rw [fderiv_prodFn_apply hθd hdiff]
      simp
    have e2 : fderiv ℝ (prodFn θ ψ) p (0, 1, 0) = θ p.1 * fderiv ℝ ψ p.2 (1, 0) := by
      show fderiv ℝ (fun y : Profile => θ y.1 * ψ y.2) p (0, 1, 0) = _
      rw [fderiv_prodFn_apply hθd hdiff]
      simp
    rw [e1, e2]
    ext i
    fin_cases i <;> simp
  refine ⟨hmemV.toLp _, ⟨fun p => ((prodFn θ ψ p : ℝ) : ℂ), hΨ, hmemV.coeFn_toLp⟩, ?_⟩
  intro h
  rw [innerCore hc hθ hb0 hb1 hVdef hmemV h]
  congr 1
  ext s
  congr 1
  unfold curlI
  congr 1
  ext z
  push_cast
  ring

end UnforcedLeray.Short.PartIIa.N01.Sub
