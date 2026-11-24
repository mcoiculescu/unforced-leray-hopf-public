import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Short.Interface.Leaf3_Phase
import UnforcedLeray.Analysis.SobolevEmbedding.Density

/-!
# Interface leaf 3 (`BodyForceL3`): conditional assembly

Source of record: `the November 2 reference manuscript`, lines 6071-6075
("For the first bound use `‖U‖_∞‖∇f‖₂ + ‖∇U‖₃‖f‖₆`").

The body force `g(τ) = Σ_j (symCol j (∂_jU(τ)) (w(τ)) + symCol j (U(τ)) (∂_jw(τ)))` of a regular
background `U` (`U ∈ C_per C₀`, `∇U ∈ C_per L³`) and `w` in the periodic `H¹` class has the
`𝒴₂` bound on the period slab. The identity `⟨𝔓 div(U⊗w + w⊗U), ψ⟩ = ⟨𝔓 g, ψ⟩` at one phase is
the compiled `lerayDivIntegral_eq_bodyForce_L3` (task `Interface:I04`, `Leaf3_Phase.lean`). The
bounded part `symCol j (U) (G j)` is `memLp_bilin_bdd`. The only new analytic points are two facts:

* `SlabMemLpOfPhaseBound` (task `Interface:I05/1`, target of `slab_memLp_of_phase_bound`): a
  jointly measurable field whose `L²(ℝ³)` norm at almost every phase of `(0, P]` is at most a
  constant times that of a dominating `L²(slab)` field is in `L²(slab)` (Tonelli on
  `B0005.IsY2.slab_eq`).
* `PhaseHolderSobolev` (task `Interface:I05/2`, target of `phase_holder_sobolev`): the phase-wise
  bound `‖symCol j (a) (f)‖₂ ≤ ‖symCol j‖ ‖a‖₃ · S Σᵢ ‖∂ᵢf‖₂` for `a ∈ L³`, `f ∈ H¹`, from the
  Hölder triple `(3, 6, 2)` and `H¹ ⊂ L⁶` (`weak_eLpNorm_six_le_sum`).

`bodyForceL3_of` assembles `BodyForceL3` from them. The unconditional `bodyForceL3` is the task
`Interface:I05` (`Short/Interface/Leaf3.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph UnforcedLeray.Cons.C08

/-- Sub-lemma 1 of Leaf 3 (the slab `L²` bound from phase-wise bounds, lines 6071-6075): a jointly
a.e.-strongly measurable `F : ℝ × ℝ³ → ℝ³` such that for almost every phase `τ ∈ (0, P]` the
`L²(ℝ³)` norm of `F(τ, ·)` is at most `c` times that of `D(τ, ·)`, with `D` real valued and in
`L²` of the period slab, is itself in `L²` of the period slab. Proved as
`slab_memLp_of_phase_bound` (task `Interface:I05/1`). -/
def SlabMemLpOfPhaseBound : Prop :=
  ∀ (P : ℝ) (F : SpaceTime → Space) (D : SpaceTime → ℝ) (c : ℝ≥0),
    AEStronglyMeasurable F volume →
    MemLp D 2 (volume.restrict (periodSlab P)) →
    (∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      eLpNorm (fun y => F (τ, y)) 2 volume ≤ (c : ℝ≥0∞) * eLpNorm (fun y => D (τ, y)) 2 volume) →
    MemLp F 2 (volume.restrict (periodSlab P))

/-- Sub-lemma 2 of Leaf 3 (lines 6071-6075, `‖∇U‖₃‖f‖₆` with `‖f‖₆ ≲ ‖∇f‖₂`): for `a ∈ L³` and
`f ∈ L²` with `L²` weak derivatives `g i`, the product `symCol j (a) (f)` has `L²` norm at most
`‖symCol j‖ ‖a‖₃ · S Σᵢ ‖g i‖₂` (`S` the Sobolev constant). Proved as `phase_holder_sobolev`
(task `Interface:I05/2`). -/
def PhaseHolderSobolev : Prop :=
  ∀ (j : Fin 3) (a f : SpatialField) (g : Fin 3 → SpatialField),
    MemLp a 3 volume → MemLp f 2 volume → (∀ i, MemLp (g i) 2 volume) →
    (∀ i, HasWeakSpatialDerivative i f (g i)) →
    eLpNorm (fun x => symCol j (a x) (f x)) 2 volume ≤
      (‖symCol j‖₊ : ℝ≥0∞) * eLpNorm a 3 volume *
        ((SobolevEmbedding.sobolevConstant : ℝ≥0∞) * ∑ i : Fin 3, eLpNorm (g i) 2 volume)

/-- **Leaf 3 from its two sub-lemmas.** The body force is
`g τ = bodyForce (U τ) (dU · τ) (Gp · τ) (w τ)` with `Gp i` the periodization of the weak gradient
`G i` of `w`. Periodicity and joint measurability are as in the draft `exists_bodyForce`; the
slab `L²` bound of the `∇U · w` terms is `SlabMemLpOfPhaseBound` with the dominating field
`Σᵢ ‖Gp i‖` and the phase bound `PhaseHolderSobolev`; the identity at almost every phase is
`lerayDivIntegral_eq_bodyForce_L3`. -/
theorem bodyForceL3_of (h₁ : SlabMemLpOfPhaseBound) (h₂ : PhaseHolderSobolev) : BodyForceL3 := by
  intro P U dU w hP hU hw
  obtain ⟨C, hC⟩ := hU.bounded
  obtain ⟨K, hK⟩ := hU.derivative_L3
  obtain ⟨G, hG⟩ := hw.gradient
  set Gp : Fin 3 → ℝ → SpatialField := fun i => periodize hP (G i) with hGp
  have hGper : ∀ i, Function.Periodic (Gp i) P := fun i => periodize_periodic (G i)
  have hGm : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => Gp i z.1 z.2) volume := fun i =>
    aestronglyMeasurable_periodize (hG i).1
  have hGL : ∀ i, MemLp (fun z : SpaceTime => Gp i z.1 z.2) 2
      (volume.restrict (periodSlab P)) := fun i => memLp_periodize (hG i).2.1
  have hGw : ∀ i, ∀ᵐ τ, HasWeakSpatialDerivative i (w τ) (Gp i τ) := fun i =>
    ae_periodize (q := fun τ v => HasWeakSpatialDerivative i (w τ) v)
      (fun τ v => by rw [hw.value.periodic τ]) (hG i).2.2
  have hwm : AEStronglyMeasurable (fun z : SpaceTime => w z.1 z.2) volume := hw.value.measurable
  have hUm : AEStronglyMeasurable (fun z : SpaceTime => U z.1 z.2) volume := hU.measurable
  have hdUm := hU.derivative_measurable
  have hUb : ∀ z : SpaceTime, ‖U z.1 z.2‖ ≤ C := fun z => hC z.1 z.2
  have hwL := ae_memLp_slice hP hw.value.periodic hw.value.memL2
  have hGL' : ∀ i, ∀ᵐ τ, MemLp (Gp i τ) 2 volume := fun i =>
    ae_memLp_slice hP (hGper i) (hGL i)
  have hphase : ∀ᵐ τ, MemLp (w τ) 2 volume ∧ (∀ i, MemLp (Gp i τ) 2 volume) ∧
      ∀ i, HasWeakSpatialDerivative i (w τ) (Gp i τ) := by
    filter_upwards [hwL, ae_all_iff.mpr hGL', ae_all_iff.mpr hGw] with τ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set D : SpaceTime → ℝ := fun z => ∑ i : Fin 3, ‖Gp i z.1 z.2‖ with hD
  have hDL : MemLp D 2 (volume.restrict (periodSlab P)) :=
    memLp_finsetSum Finset.univ fun i _ => (hGL i).norm
  have hterm : ∀ j : Fin 3, MemLp (fun z : SpaceTime => symCol j (dU j z.1 z.2) (w z.1 z.2)) 2
      (volume.restrict (periodSlab P)) := by
    intro j
    refine h₁ P (fun z : SpaceTime => symCol j (dU j z.1 z.2) (w z.1 z.2)) D
      (‖symCol j‖₊ * K.toNNReal * (SobolevEmbedding.sobolevConstant * 3))
      ((symCol j).aestronglyMeasurable_comp₂ (hdUm j) hwm) hDL ?_
    refine ae_restrict_of_ae ?_
    filter_upwards [hphase] with τ hτ
    obtain ⟨hτw, hτG, hτGw⟩ := hτ
    have h2 := h₂ j (dU j τ) (w τ) (fun i => Gp i τ) (hK τ j).1 hτw hτG hτGw
    have h3 : eLpNorm (dU j τ) 3 volume ≤ (K.toNNReal : ℝ≥0∞) := (hK τ j).2
    have h4 : ∑ i : Fin 3, eLpNorm (Gp i τ) 2 volume ≤
        3 * eLpNorm (fun y => D (τ, y)) 2 volume := by
      calc ∑ i : Fin 3, eLpNorm (Gp i τ) 2 volume
          ≤ ∑ _i : Fin 3, eLpNorm (fun y => D (τ, y)) 2 volume := by
            refine Finset.sum_le_sum fun i _ => eLpNorm_mono fun y => ?_
            have hnn : 0 ≤ D (τ, y) := Finset.sum_nonneg fun k _ => norm_nonneg _
            show ‖Gp i τ y‖ ≤ ‖D (τ, y)‖
            rw [Real.norm_of_nonneg hnn]
            exact Finset.single_le_sum (f := fun k : Fin 3 => ‖Gp k τ y‖)
              (fun k _ => norm_nonneg _) (Finset.mem_univ i)
        _ = 3 * eLpNorm (fun y => D (τ, y)) 2 volume := by simp
    have h6 : (‖symCol j‖₊ : ℝ≥0∞) * eLpNorm (dU j τ) 3 volume *
        ((SobolevEmbedding.sobolevConstant : ℝ≥0∞) * ∑ i : Fin 3, eLpNorm (Gp i τ) 2 volume) ≤
        (‖symCol j‖₊ : ℝ≥0∞) * (K.toNNReal : ℝ≥0∞) *
          ((SobolevEmbedding.sobolevConstant : ℝ≥0∞) *
            (3 * eLpNorm (fun y => D (τ, y)) 2 volume)) :=
      mul_le_mul' (mul_le_mul' le_rfl h3) (mul_le_mul' le_rfl h4)
    refine h2.trans (h6.trans (le_of_eq ?_))
    push_cast
    ring
  refine ⟨fun τ => bodyForce (U τ) (fun j => dU j τ) (fun j => Gp j τ) (w τ),
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro τ
    simp only [hU.periodic τ, hU.derivative_periodic _ τ, hw.value.periodic τ, hGper _ τ]
  · show AEStronglyMeasurable (fun z : SpaceTime => ∑ j : Fin 3,
      (symCol j (dU j z.1 z.2) (w z.1 z.2) + symCol j (U z.1 z.2) (Gp j z.1 z.2))) volume
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => ?_
    exact ((symCol j).aestronglyMeasurable_comp₂ (hdUm j) hwm).add
      ((symCol j).aestronglyMeasurable_comp₂ hUm (hGm j))
  · show MemLp (fun z : SpaceTime => ∑ j : Fin 3,
      (symCol j (dU j z.1 z.2) (w z.1 z.2) + symCol j (U z.1 z.2) (Gp j z.1 z.2))) 2
      (volume.restrict (periodSlab P))
    refine memLp_finsetSum Finset.univ fun j _ => ?_
    exact (hterm j).add (memLp_bilin_bdd (symCol j) hUm.restrict hUb (hGL j))
  · filter_upwards [hphase] with τ hτ
    obtain ⟨hτw, hτG, hτGw⟩ := hτ
    refine ⟨hτw, fun ψ hψ => ?_⟩
    exact (lerayDivIntegral_eq_bodyForce_L3 (hU.continuous τ) (fun x => hC τ x)
      (hU.weak_derivative τ) (fun j => (hK τ j).1) hτw hτG hτGw
      (isVectorTest_slice hψ τ)).2

end UnforcedLeray.Short.Interface
