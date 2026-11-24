import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestAlgebra
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.Identity

/-!
# `CTestOpK`: the operator `K` preserves complex band tests (task `PartII-a:N02/2/3`)

`K = 2 s ∂_s + η ∂_η` (source `the November 2 reference manuscript`, line 1652).
By `NearStreamMemberAux.opK_eq`, `K F = s · (2 ∂_s F) + η · ∂_η F`, a sum of two products of
smooth `q`-periodic coefficients with the band tests `∂_s F`, `∂_η F` (`CTestFderiv`), and the
constant `2` is absorbed as a smooth coefficient as well (`CTestAlgebra`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The coefficient `s ↦ (s : ℂ)` is smooth. -/
theorem ctoCoeffS_smooth : ContDiff ℝ ∞ (fun p : Profile => ((p.1 : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_fst : ContDiff ℝ ∞ (fun p : Profile => p.1))

/-- The coefficient `η ↦ (η : ℂ)` is smooth. -/
theorem ctoCoeffEta_smooth : ContDiff ℝ ∞ (fun p : Profile => ((p.2.2 : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_snd.comp contDiff_snd : ContDiff ℝ ∞ (fun p : Profile => p.2.2))

/-- The coefficient `s ↦ (s : ℂ)` is `q`-periodic (it does not depend on `q`). -/
theorem ctoCoeffS_periodic (c : ℝ) : QPeriodic c (fun p : Profile => ((p.1 : ℝ) : ℂ)) :=
  fun _ => rfl

/-- The coefficient `η ↦ (η : ℂ)` is `q`-periodic (it does not depend on `q`). -/
theorem ctoCoeffEta_periodic (c : ℝ) : QPeriodic c (fun p : Profile => ((p.2.2 : ℝ) : ℂ)) :=
  fun _ => rfl

/-- The constant coefficient `2` is `q`-periodic. -/
theorem ctoTwo_periodic (c : ℝ) : QPeriodic c (fun _ : Profile => (2 : ℂ)) :=
  fun _ => rfl

/-- **Target `PartII-a:N02/2/3`**: `K` maps complex band tests to complex band tests. -/
theorem cTestOpK : UnforcedLeray.Short.PartIIa.CTestOpK := by
  unfold UnforcedLeray.Short.PartIIa.CTestOpK
  intro c F hF
  -- `∂_s F` and `∂_η F` are complex band tests (`CTestFderiv`).
  have hS : IsCTest c (pdS F) := cTestFderiv c F hF (1, 0, 0)
  have hE : IsCTest c (pdEta F) := cTestFderiv c F hF (0, 0, 1)
  -- The constant `2` times `∂_s F`.
  have h2S : IsCTest c (fun p => (2 : ℂ) * pdS F p) :=
    cTestAlgebra.2.2.2 c (pdS F) (fun _ => (2 : ℂ)) hS contDiff_const (ctoTwo_periodic c)
  -- Multiplication by the smooth `q`-periodic coefficients `s` and `η`.
  have hT1 : IsCTest c (fun p => (p.1 : ℂ) * (2 * pdS F p)) :=
    cTestAlgebra.2.2.2 c (fun p => (2 : ℂ) * pdS F p) (fun p => ((p.1 : ℝ) : ℂ)) h2S
      ctoCoeffS_smooth (ctoCoeffS_periodic c)
  have hT2 : IsCTest c (fun p => (p.2.2 : ℂ) * pdEta F p) :=
    cTestAlgebra.2.2.2 c (pdEta F) (fun p => ((p.2.2 : ℝ) : ℂ)) hE
      ctoCoeffEta_smooth (ctoCoeffEta_periodic c)
  -- Sum of the two terms.
  have hSum : IsCTest c (fun p => (p.1 : ℂ) * (2 * pdS F p) + (p.2.2 : ℂ) * pdEta F p) :=
    cTestAlgebra.2.1 c _ _ hT1 hT2
  have hopK : opK F = fun p => (p.1 : ℂ) * (2 * pdS F p) + (p.2.2 : ℂ) * pdEta F p :=
    funext (NearStreamMemberAux.opK_eq F)
  rw [hopK]
  exact hSum

end UnforcedLeray.Short.PartIIa
