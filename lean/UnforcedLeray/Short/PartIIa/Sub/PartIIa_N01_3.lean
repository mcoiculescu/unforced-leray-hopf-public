import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_4
import UnforcedLeray.Units.B0414.PhaseOrthogonal

/-!
# `PartII-a:N01/3` (decomposition of `PhaseLerayConj`)

Source `the November 2 reference manuscript`,
line 1669 (`P_ε` is the conjugated Cartesian Leray projection), with the chart `y = Rx`,
lines 1639-1643, and the phase Leray projection of `Y₂`, lines 1339-1343 / 7336-7344 of the
paper (`B0414`).

Let `W := U ∘ toX : L²(dx dτ; ℝ³) →ᵣ Y₂`.  Three facts, `PhysGradPhaseSliceTest`,
`PhysGradPhaseOrth`, `PhysSolenoidalToY` (below), give `PhaseLerayConj`: `W (P3D V) ∈ solenoidalY`
(third), and `W (V - P3D V)` is orthogonal to `solenoidalY` because `V - P3D V` lies in the closure
of the span of the gradients `∇ₓφ` (`orthogonal_orthogonal_eq_closure`), `W (∇ₓφ)` is orthogonal to
`solenoidalY` (first two, via `divScaleTransfer`), and orthogonality to `solenoidalY` is a closed
real-linear condition.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (cplx3 toX)

/-- The phase-variable form of the spatial gradient of a physical test `φ(x, τ)`:
`Φ(τ, y) = ∇ₓφ(εy, τ)` (complexified), a field of the phase variables `(τ, y)`
(chart `x = εy`, lines 1639-1643). -/
def physGradPhase (ε : ℝ) (φ : UnforcedLeray.Space × ℝ → ℝ) : ℝ × UnforcedLeray.Space → CVec3 :=
  fun p => cplx3 (UnforcedLeray.B0226.gradX φ (ε • p.2, p.1))

/-- **Sub-lemma 1 (`PartII-a:N01/3/1`).** `physGradPhase ε φ` is a slice test (it is a smooth
`P`-periodic field with bounded spatial support: a phase test). -/
def PhysGradPhaseSliceTest : Prop :=
  ∀ (ε P : ℝ) [Fact (0 < P)], 0 < ε → ∀ φ : UnforcedLeray.Space × ℝ → ℝ,
    UnforcedLeray.B0226.IsPhysTest P φ → IsSliceTest P 2 (physGradPhase ε φ)

/-- **Sub-lemma 2 (`PartII-a:N01/3/2`).** Phase gradients of phase tests are orthogonal to
`solenoidalY` (slice-wise: `g τ` is distributionally solenoidal for a.e. `τ`, and the
`τ`-slice of `physGradPhase ε φ` is the gradient of the real test `y ↦ φ(εy, τ)` rescaled by `ε`;
use `IsSolenoidalC` for the real test `y ↦ φ(εy, τ)`; `IsSolenoidalC` has no conjugation). -/
def PhysGradPhaseOrth : Prop :=
  ∀ (ε P : ℝ) [Fact (0 < P)], 0 < ε → ∀ φ : UnforcedLeray.Space × ℝ → ℝ,
    UnforcedLeray.B0226.IsPhysTest P φ → ∀ g ∈ UnforcedLeray.B0414.solenoidalY P,
      inner ℂ (testElem P 2 (physGradPhase ε φ)) g = 0

/-- **Sub-lemma 3 (`PartII-a:N01/3/3`).** Physically solenoidal fields have a.e. solenoidal phase
slices. -/
def PhysSolenoidalToY : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → ∀ (hP : P = 2 * ε * c),
    ∀ U : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U →
      ∀ V : UnforcedLeray.B0220.PhysL2 ε c, V ∈ UnforcedLeray.B0226.physSolenoidal ε c →
        U (toX hP V) ∈ UnforcedLeray.B0414.solenoidalY P

theorem phaseLerayConj_of (hS : PhysGradPhaseSliceTest) (hO : PhysGradPhaseOrth)
    (hA : PhysSolenoidalToY) : PhaseLerayConj := by
  intro ε c P _ hε hc hP U hU V
  have hP0 : (0 : ℝ) < P := Fact.out
  let W : UnforcedLeray.B0220.PhysL2 ε c →L[ℝ] Yq P 2 :=
    ((U.toContinuousLinearMap).restrictScalars ℝ).comp (toX hP)
  have hW : ∀ u, W u = U (toX hP u) := fun u => rfl
  let K : Submodule ℂ (Yq P 2) := UnforcedLeray.B0414.solenoidalY P
  let S : Submodule ℝ (UnforcedLeray.B0220.PhysL2 ε c) :=
    { carrier := {u | ∀ g ∈ K, inner ℂ (W u) g = 0}
      add_mem' := by
        intro u v hu hv g hg
        rw [map_add, inner_add_left, hu g hg, hv g hg, add_zero]
      zero_mem' := by
        intro g hg
        simp
      smul_mem' := by
        intro r u hu g hg
        rw [map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ) r (W u), inner_smul_left, hu g hg, mul_zero] }
  have hSclosed : IsClosed (S : Set (UnforcedLeray.B0220.PhysL2 ε c)) := by
    have : (S : Set (UnforcedLeray.B0220.PhysL2 ε c)) =
        ⋂ g ∈ K, {u | inner ℂ (W u) g = 0} := by
      ext u
      simp [S]
    rw [this]
    refine isClosed_biInter fun g _ => isClosed_eq ?_ continuous_const
    exact (continuous_id.inner continuous_const).comp W.continuous
  have hgrad : ∀ φ : UnforcedLeray.B0226.PhysTest ε c, UnforcedLeray.B0226.physGrad ε c φ ∈ S := by
    intro φ g hg
    have hφ : UnforcedLeray.B0226.IsPhysTest P φ.1 := by rw [hP]; exact φ.2
    have key := divScaleTransfer hε hP U hU (UnforcedLeray.B0226.physGrad ε c φ)
      (physGradPhase ε φ.1) (hS ε P hε φ.1 hφ) 1 (by
        filter_upwards [UnforcedLeray.B0226.coeFn_physGrad ε c φ] with w hw
        rw [hw]
        simp [physGradPhase, smul_smul, mul_inv_cancel₀ hε.ne'])
    rw [hW, key, inner_smul_left, hO ε P hε φ.1 hφ g hg, mul_zero]
  have hspan : Submodule.span ℝ (Set.range (UnforcedLeray.B0226.physGrad ε c)) ≤ S :=
    Submodule.span_le.2 (by rintro _ ⟨φ, rfl⟩; exact hgrad φ)
  have hcl : (Submodule.span ℝ (Set.range (UnforcedLeray.B0226.physGrad ε c))).topologicalClosure ≤ S :=
    Submodule.topologicalClosure_minimal _ hspan hSclosed
  have hres : V - UnforcedLeray.B0226.P3D ε c V ∈ S := by
    apply hcl
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.sub_starProjection_mem_orthogonal (K := UnforcedLeray.B0226.physSolenoidal ε c) V
  have hmem : U (toX hP (UnforcedLeray.B0226.P3D ε c V)) ∈ K :=
    hA ε c P hε hc hP U hU _ (UnforcedLeray.B0226.P3D_mem V)
  rw [UnforcedLeray.B0414.lerayY_two]
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem fun g hg => ?_
  have := hres g hg
  rwa [map_sub] at this

end UnforcedLeray.Short.PartIIa.N01
