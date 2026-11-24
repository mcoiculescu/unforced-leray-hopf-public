import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth

/-!
# `PartIII-a:T21/2/2/3/2`: the classical moving adjoint equation, decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 2854-2865
(`eq:short-causal-moving`), 2909-2911 (`D^# = Δ - ½y·∇ + 1`), 3036-3037, 3052-3060.

`MovAdjEquation m` asks for a `C¹`, `d`-periodic `χ` which is an adjoint localized interaction and
satisfies `∂_ζΦ = adjGen β V Φ - χ`. The only candidate is the explicit
`mvChi := adjGen β V Φ - ∂_ζΦ` (the `ζ`-derivative of `Φ(ζ)(y)` exists since `φ` is jointly smooth
at the interior age `r = revAge ν s ζ ∈ (t, s)`, `dr/dζ = -a²`). The four leaves are

* `MvPhiDiff`: `ζ' ↦ mvPhi ν φ s ζ' y` is differentiable at `ζ` (chain rule, joint smoothness);
* `MvChiC1`: `mvChi` is `C¹` (it is a rescaling of `χ_phys = ∂_ρφ + νΔφ + v·∇φ`,
  jointly smooth in `(ρ, x)`, with `train.smooth_v`);
* `MvChiPer`: `mvChi` is `d`-periodic (from the periodicity of `φ(r)`, `∂_rφ`, `v`);
* `MvChiInter`: `mvChi` is an adjoint localized interaction, from `AdjWeakPointwise m`
  (`∫ ladChi ψ = ∫ φ (K_cψ)·∇E`) by the rescaling `x = √a y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- The interaction `χ := β D^#Φ + V·∇Φ - ∂_ζΦ` at reverse moving time `ζ` (SP 2858-2862). -/
def mvChi (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ) (y : ℝ × ℝ) : ℂ :=
  adjGen (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y -
    deriv (fun ζ' => mvPhi ν φ s ζ' y) ζ

/-- **Leaf A**: pointwise differentiability of the moving adjoint in the reverse moving time
(chain rule: `revAge` smooth with `dr/dζ = -a²`, `r ∈ (t, s)`, `IsAdjointFlow.jointSmooth`). -/
def MvPhiDiff (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    ∀ y : ℝ × ℝ, DifferentiableAt ℝ (fun ζ' => mvPhi ν φ s ζ' y) ζ

/-- **Leaf B**: `mvChi` is `C¹` (SP 3052-3060: `χ_phys` is jointly smooth; the train is smooth). -/
def MvChiC1 (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    ContDiff ℝ 1 (mvChi ν tr s φ ζ)

/-- **Leaf C**: `mvChi` is periodic with the moving cell length. -/
def MvChiPer (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    ∀ y : ℝ × ℝ, mvChi ν tr s φ ζ (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2) = mvChi ν tr s φ ζ y

/-- **Leaf D**: `mvChi` is the adjoint localized interaction of `mvPhi` (SP 3052-3058), from the
classical weak identity `AdjWeakPointwise m` by the rescaling `x = √a y` of tests and kernel
velocities. -/
def MvChiInter (m : ℝ) : Prop :=
  AdjWeakPointwise m →
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjInteraction (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (movingTrainE tr (revAge ν s ζ))
      (mvPhi ν φ s ζ) (mvChi ν tr s φ ζ)

/-- `MovAdjEquation` from the four leaves and the classical weak identity. -/
theorem movAdjEquation_of (m : ℝ) (hW : AdjWeakPointwise m) (hA : MvPhiDiff m)
    (hB : MvChiC1 m) (hC : MvChiPer m) (hD : MvChiInter m) : MovAdjEquation m := by
  intro ν tr t s φ ζ hflow hbd
  refine ⟨mvChi ν tr s φ ζ, hB ν tr t s φ ζ hflow, hC ν tr t s φ ζ hflow,
    hD hW ν tr t s φ ζ hflow hbd, fun y => ?_⟩
  have h := (hA ν tr t s φ ζ hflow y).hasDerivAt
  have e : adjGen (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y -
      mvChi ν tr s φ ζ y = deriv (fun ζ' => mvPhi ν φ s ζ' y) ζ := by
    simp [mvChi]
  rw [e]
  exact h

end UnforcedLeray.Short.IIIa.AdjE1
