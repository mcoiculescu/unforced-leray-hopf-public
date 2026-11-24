import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.Identity

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732
(`K = 2S + eta d_eta` anti-self-adjoint for `s^{-3/2}`). Target: `PdAgeScale` (`Sub/N02_2.lean`).

For `s > 0` the function `x ↦ (x.1)^a` (as a `ℂ`-valued profile function) has derivative
`a s^(a-1)` in the `s` direction and `0` in the `q` and `η` directions. The Leibniz rule
`fderiv_mul_apply'` (proved in `Tasks/N02LerayComparison/StreamMember/Identity.lean`) then gives
the three identities of `PdAgeScale`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The `ℂ`-valued function `x ↦ (x.1)^a` has the derivative `a p.1^(a-1) · (fst)` at `p`, for `p.1 > 0`. -/
theorem pasHasFDerivAt (a : ℝ) (p : Profile) (hp : 0 < p.1) :
    HasFDerivAt (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((a * p.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) p := by
  have hd : HasDerivAt (fun y : ℝ => y ^ a) (a * p.1 ^ (a - 1)) p.1 :=
    Real.hasDerivAt_rpow_const (Or.inl hp.ne')
  have h0 : HasFDerivAt (fun x : Profile => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have h1 : HasFDerivAt ((fun y : ℝ => y ^ a) ∘ (fun x : Profile => x.1))
      ((a * p.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hd.comp_hasFDerivAt p h0
  exact Complex.ofRealCLM.hasFDerivAt.comp p h1

theorem pasFderiv (a : ℝ) (p v : Profile) (hp : 0 < p.1) :
    fderiv ℝ (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) p v
      = ((a * p.1 ^ (a - 1) * v.1 : ℝ) : ℂ) := by
  rw [(pasHasFDerivAt a p hp).fderiv]
  simp

theorem pasPdS (a : ℝ) (p : Profile) (hp : 0 < p.1) :
    fderiv ℝ (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) p (1, 0, 0)
      = ((a * p.1 ^ (a - 1) : ℝ) : ℂ) := by
  rw [pasFderiv a p (1, 0, 0) hp]
  simp

theorem pasPdQ (a : ℝ) (p : Profile) (hp : 0 < p.1) :
    fderiv ℝ (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) p (0, 1, 0) = 0 := by
  rw [pasFderiv a p (0, 1, 0) hp]
  simp

theorem pasPdEta (a : ℝ) (p : Profile) (hp : 0 < p.1) :
    fderiv ℝ (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) p (0, 0, 1) = 0 := by
  rw [pasFderiv a p (0, 0, 1) hp]
  simp

/-- **Product rule for the age weight** (task `PartII-a:N02/2/6`): the three derivative identities
for `x ↦ (x.1)^a · F x` at `p` with `p.1 > 0`. -/
theorem pdAgeScale : PdAgeScale := by
  unfold PdAgeScale
  intro a F hF p hp
  have hu : DifferentiableAt ℝ (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) p :=
    (pasHasFDerivAt a p hp).differentiableAt
  have hFd : DifferentiableAt ℝ F p := hF.differentiable (by simp) p
  refine ⟨?_, ?_, ?_⟩
  · simp only [pdS]
    rw [NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) F
      (1, 0, 0) p hu hFd, pasPdS a p hp]
    push_cast
    ring
  · simp only [pdQ]
    rw [NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) F
      (0, 1, 0) p hu hFd, pasPdQ a p hp]
    ring
  · simp only [pdEta]
    rw [NearStreamMemberAux.fderiv_mul_apply' (fun x : Profile => ((x.1 ^ a : ℝ) : ℂ)) F
      (0, 0, 1) p hu hFd, pasPdEta a p hp]
    ring

end UnforcedLeray.Short.PartIIa
