import UnforcedLeray.Short.Interface.WindowSteps
import UnforcedLeray.Cons.L2.FreeLaplacianRegularity.Window

/-!
# Interface leaf 4a, step W4 (`WindowTransportBack`): conditional assembly

Source of record: `the November 2 reference manuscript`, lines 6071-6075 and
6107-6150 (the regularity of the mode `b ∈ C_per H²`, which `Δ b ∈ 𝒴₂` serves), via the window
argument of the old manuscript `paper/main.tex` lines 7498-7517 ("the distributional form of
(11) supplies its derivatives"; `eq:free-stress-14`, `-15`).

Step W4 takes the weak second derivatives `D2 a b` of the three components `u_i = windowU χ τ₀ w i`
(the output of the heat maximal regularity) and produces the window Laplacian of `w`. It is a
change of variables back from the heat variables `(θ, x)` to `(τ, y)`: first in the unshifted
phase `t = τ - τ₀` (the library `Cons/L2/FreeLaplacianRegularity/Window.lean` does this for the
heat field `heatField χ W c`, `W t = w (τ₀ + t)`), then a time shift by `τ₀`.

Everything reduces to one per-component statement, `WindowComponentTransport`: the component
`c` of `w` has an `L²`-on-the-window Laplacian `Lc`. `windowTransportBack_of` assembles the
vector-valued `Λ = Σ_c Lc c • e_c`. The per-component statement is proved in
`Short/Interface/Leaf4a_Back.lean` from the following facts, each a named Prop below (all nine are
proved there as `windowBack_*`, so the task is closed without sub-tasks):

* `WindowUEqHeatField` (fact 1): `windowU χ τ₀ w i = heatField χ (w (τ₀ + ·)) i`.
* `IsY2ShiftProp` (fact 2): the time shift of a `𝒴₂` field is `𝒴₂`.
* `SimilarityTestShift` (fact 3): the time shift of a similarity test is one.
* `HeatFieldLaplacianOfD2` (fact 4): from the weak second derivatives `D2` of a heat
  field to `∫ u Δ_xφ = ∫ (Σ_j D2_jj) φ`.
* `WindowComponentOfLap` (fact 5): transport back of that Laplacian (a refactor of
  `window_component` of `Window.lean` with the Laplacian supplied, not obtained from the heat
  estimate).
* `WindowComponentUnshifted` (fact 6): the combination of the four facts above.
* `MemLpWindowShift` (fact 7), `CutoffLaplacianShift` (fact 8): the two
  shift lemmas used to move the phase variable by `τ₀`.
* `WindowComponentTransport` (fact 9): the per-component statement.

The unconditional `windowTransportBack` is task `Interface:I15` (`Short/Interface/Leaf4a_Back.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08
open UnforcedLeray.Parabolic (IsSTTest sLap)

/-- Fact 1 (`paper/main.tex` 7485-7497): the field `windowU` of `WindowSteps.lean` is the heat
field `heatField χ W` of `Window.lean` for the phase-shifted `W t = w (τ₀ + t)`. Both are
`χ(log θ) e^{-(log θ)/2} w(τ₀ + log θ, θ^{-1/2}x)_i` for `θ > 0` and `0` otherwise. Proved as
`windowBack_windowU_eq_heatField` (`Leaf4a_Back.lean`). -/
def WindowUEqHeatField : Prop :=
  ∀ (χ : ℝ → ℝ) (τ₀ : ℝ) (w : ℝ → SpatialField) (i : Fin 3),
    windowU χ τ₀ w i =
      UnforcedLeray.Cons.L2.FreeLapReg.heatField χ (fun t => w (τ₀ + t)) i

/-- Fact 2 (periodicity is shift invariant): the time shift `t ↦ w (τ₀ + t)` of a `P`-periodic
`𝒴₂` field is a `P`-periodic `𝒴₂` field. Periodicity is `hw.periodic`; measurability and
`L²` on `(0, P] × ℝ³` come from `IsY2.memLp_slab` (`Cons/L2/FreeLaplacianRegularity/
ChangeOfVariables.lean`) on `Icc τ₀ (τ₀ + P)` pulled back by `timeShift τ₀` (same file,
`measurePreserving_timeShift`). Proved as `windowBack_isY2_shift` (`Leaf4a_Back.lean`). -/
def IsY2ShiftProp : Prop :=
  ∀ (P : ℝ) (w : ℝ → SpatialField) (τ₀ : ℝ), 0 < P → B0005.IsY2 P w →
    B0005.IsY2 P (fun t => w (τ₀ + t))

/-- Fact 3: the time shift `(t, y) ↦ Ψ (τ₀ + t, y)` of a similarity test is a similarity test
(smooth by composition; compact support because it is the preimage of a compact set under a
homeomorphism). Proved as `windowBack_similarityTest_shift` (`Leaf4a_Back.lean`). -/
def SimilarityTestShift : Prop :=
  ∀ (Ψ : SpaceTime → Space) (τ₀ : ℝ), IsSimilarityTest Ψ →
    IsSimilarityTest (fun z : SpaceTime => Ψ (τ₀ + z.1, z.2))

/-- Fact 4 (`paper/main.tex` 7517, "the distributional form of (11) supplies its derivatives"):
if a heat field `u = heatField χ W c` is `L²` and has `L²` weak second derivatives `D a b`, then
`∫ u Δ_xφ = ∫ (Σ_j D j j) φ` for every heat test `φ`. This is the tail of the proof of
`exists_heat_laplacian` (`Window.lean`) with `D` given in place of the output of
`heat_estimate_componentwise`. Proved as `windowBack_heatField_laplacian` (`Leaf4a_Back.lean`). -/
def HeatFieldLaplacianOfD2 : Prop :=
  ∀ (χ : ℝ → ℝ) (W : ℝ → SpatialField) (c : Fin 3) (D : Fin 3 → Fin 3 → SpaceTime → ℝ),
    MemLp (UnforcedLeray.Cons.L2.FreeLapReg.heatField χ W c) 2 volume →
    (∀ a b, MemLp (D a b) 2 volume ∧
      B0423.HasWeakSpaceDeriv2 (d := 3) (UnforcedLeray.Cons.L2.FreeLapReg.heatField χ W c)
        a b (D a b)) →
    ∀ φ : SpaceTime → ℝ, IsSTTest (d := 3) φ →
      ∫ X, UnforcedLeray.Cons.L2.FreeLapReg.heatField χ W c X * sLap φ X =
        ∫ X, (∑ i : Fin 3, D i i X) * φ X

/-- Fact 5 (`paper/main.tex` 7498-7517, B0424): transport of a heat Laplacian back to `(τ, y)`.
This is `window_component` of `Window.lean` (`Cons/L2/FreeLaplacianRegularity/Window.lean`, the
lines from `obtain ⟨Lap, hLap, hLapEq⟩` on) with `Lap, hLap, hLapEq` supplied as hypotheses and
the unused `h, μ, pg, heq` removed; the `L²` membership of the heat field is
`memLp_heatField` there. `Lc(t, y) = e^{3t/2} Lap(e^t, e^{t/2}y)`. Proved as
`windowBack_component_of_lap` (`Leaf4a_Back.lean`). -/
def WindowComponentOfLap : Prop :=
  ∀ (P : ℝ) (W : ℝ → SpatialField) (χ : ℝ → ℝ) (c : Fin 3) (Lap : SpaceTime → ℝ),
    0 < P → B0005.IsY2 P W → ContDiff ℝ ∞ χ → HasCompactSupport χ →
    MemLp Lap 2 volume →
    (∀ φ : SpaceTime → ℝ, IsSTTest (d := 3) φ →
      ∫ X, UnforcedLeray.Cons.L2.FreeLapReg.heatField χ W c X * sLap φ X =
        ∫ X, Lap X * φ X) →
    ∃ Lc : SpaceTime → ℝ,
      (∀ a b, MemLp Lc 2 (volume.restrict (UnforcedLeray.Cons.L2.FreeLapReg.slab a b))) ∧
      ∀ Ψ, IsSimilarityTest Ψ →
        Integrable (fun z : SpaceTime => W z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c)) ∧
        Integrable (fun z : SpaceTime => Lc z * Ψ z c) ∧
        ∫ z : SpaceTime, W z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) =
          ∫ z : SpaceTime, Lc z * Ψ z c

/-- Fact 6: the transport back in the unshifted phase, from the weak second derivatives of
`u_c = windowU χ τ₀ w c`. Combination of facts 1, 2, 4, 5: `windowU χ τ₀ w c =
heatField χ (w (τ₀ + ·)) c` (fact 1), `w (τ₀ + ·)` is `𝒴₂` (fact 2), the heat field is `L²` by
`memLp_heatField`, `Lap = Σ_j D2 j j` has `∫ u Δφ = ∫ Lap φ` (fact 4), then fact 5 with
`W = w (τ₀ + ·)`. Proved as `windowBack_component_unshifted` (`Leaf4a_Back.lean`). -/
def WindowComponentUnshifted : Prop :=
  ∀ (P : ℝ) (w : ℝ → SpatialField) (χ : ℝ → ℝ) (τ₀ : ℝ) (c : Fin 3),
    0 < P → B0005.IsY2 P w → ContDiff ℝ ∞ χ → HasCompactSupport χ →
    (∃ D2 : Fin 3 → Fin 3 → ℝ × Space → ℝ, ∀ a b,
      MemLp (D2 a b) 2 volume ∧ B0423.HasWeakSpaceDeriv2 (d := 3) (windowU χ τ₀ w c) a b (D2 a b)) →
    ∃ Lc : SpaceTime → ℝ,
      (∀ a b, MemLp Lc 2 (volume.restrict (UnforcedLeray.Cons.L2.FreeLapReg.slab a b))) ∧
      ∀ Ψ, IsSimilarityTest Ψ →
        Integrable (fun z : SpaceTime =>
          w (τ₀ + z.1) z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c)) ∧
        Integrable (fun z : SpaceTime => Lc z * Ψ z c) ∧
        ∫ z : SpaceTime, w (τ₀ + z.1) z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) =
          ∫ z : SpaceTime, Lc z * Ψ z c

/-- Fact 7 (shift of `L²` on slabs): if `Lc` is `L²` on every slab `[a, b] × ℝ³`, then
`(τ, y) ↦ Lc (τ - τ₀, y)` is `L²` on the open window `(τ₀ - 1, τ₀ + 1) × ℝ³`. Use
`windowSlab τ₀ 1 ⊆ slab (τ₀ - 1) (τ₀ + 1)` (`MemLp.mono_measure`) and the measure preserving
equivalence `timeShift (-τ₀)` of `ChangeOfVariables.lean` with
`MeasurePreserving.restrict_preimage_emb` and `MemLp.comp_measurePreserving`. Proved as
`windowBack_memLp_shift` (`Leaf4a_Back.lean`). -/
def MemLpWindowShift : Prop :=
  ∀ (τ₀ : ℝ) (Lc : SpaceTime → ℝ),
    (∀ a b, MemLp Lc 2 (volume.restrict (UnforcedLeray.Cons.L2.FreeLapReg.slab a b))) →
    MemLp (fun z : SpaceTime => Lc (z.1 - τ₀, z.2)) 2 (volume.restrict (windowSlab τ₀ 1))

/-- Fact 8 (the cutoff drops out): for a window cutoff `χ` and a similarity test `ψ` with
`tsupport ψ ⊆ windowSlab τ₀ 1`, the shifted test `Ψ(t, y) = ψ(τ₀ + t, y)` satisfies
`χ t * (Δ_y Ψ)(t, y) c = (Δ_y ψ)(τ₀ + t, y) c` for all `t, y, c`. For `|t| < 1` use `χ t = 1`
(`IsWindowCutoff.one`) and that `spatialLaplacian Ψ t y` unfolds to `spatialLaplacian ψ (τ₀+t) y`
(the slice `y ↦ Ψ (t, y)` is the slice `y ↦ ψ (τ₀ + t, y)`); for `|t| ≥ 1` both sides vanish
because `(τ₀ + t, y) ∉ tsupport ψ`, so the slice is identically `0` and has zero derivatives.
Proved as `windowBack_cutoff_laplacian` (`Leaf4a_Back.lean`). -/
def CutoffLaplacianShift : Prop :=
  ∀ (χ : ℝ → ℝ) (τ₀ : ℝ) (ψ : SpaceTime → Space), IsWindowCutoff χ → IsSimilarityTest ψ →
    tsupport ψ ⊆ windowSlab τ₀ 1 → ∀ (t : ℝ) (y : Space) (c : Fin 3),
      χ t * spatialLaplacian (fun z : SpaceTime => ψ (τ₀ + z.1, z.2)) t y c =
        spatialLaplacian ψ (τ₀ + t) y c

/-- The per-component transport back (`paper/main.tex` 7498-7517; step W4 for one component):
from the weak second derivatives of `u_c = windowU χ τ₀ w c` there is `Lc`, `L²` on the window
`windowSlab τ₀ 1`, with `∫∫ w_c (Δψ)_c = ∫∫ Lc ψ_c` for every similarity test supported in the
window, all integrands integrable. Proved as `windowBack_componentTransport` (`Leaf4a_Back.lean`)
from facts 3, 6, 7, 8 by shifting the phase by `τ₀` (`integral_timeShift`,
`measurePreserving_timeShift` of `ChangeOfVariables.lean`) and `Lc' (τ, y) = Lc (τ - τ₀, y)`. -/
def WindowComponentTransport : Prop :=
  ∀ (P : ℝ) (w : ℝ → SpatialField) (χ : ℝ → ℝ) (τ₀ : ℝ) (c : Fin 3),
    0 < P → B0005.IsY2 P w → IsWindowCutoff χ →
    (∃ D2 : Fin 3 → Fin 3 → ℝ × Space → ℝ, ∀ a b,
      MemLp (D2 a b) 2 volume ∧ B0423.HasWeakSpaceDeriv2 (d := 3) (windowU χ τ₀ w c) a b (D2 a b)) →
    ∃ Lc : SpaceTime → ℝ, MemLp Lc 2 (volume.restrict (windowSlab τ₀ 1)) ∧
      ∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ windowSlab τ₀ 1 →
        Integrable (fun z : SpaceTime => w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c) ∧
        Integrable (fun z : SpaceTime => Lc z * ψ z c) ∧
        ∫ z : SpaceTime, w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c =
          ∫ z : SpaceTime, Lc z * ψ z c

/-- `WindowTransportBack` from the per-component transport: take
`Λ(t, y) = Σ_c Lc c (t, y) • e_c`. The vector pairings are the component sums (the same
reduction as `window_laplacian` of `Window.lean`). -/
theorem windowTransportBack_of (h : WindowComponentTransport) : WindowTransportBack := by
  intro P w χ τ₀ hP hw hχ hD2
  choose Lc hLc hEq using fun c : Fin 3 => h P w χ τ₀ c hP hw hχ (hD2 c)
  refine ⟨fun t y => ∑ c : Fin 3, Lc c (t, y) • coordinateVector c, ?_, fun ψ hψ hsupp => ?_⟩
  · refine memLp_finsetSum _ fun c _ => ?_
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector c)).comp_memLp' (hLc c)
  · have hptL : ∀ z : SpaceTime, diffusionTerm w ψ z =
        ∑ c : Fin 3, w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c := by
      intro z
      rw [diffusionTerm, UnforcedLeray.Cons.L2.FreeLapReg.inner_eq_sum]
    have hptR : ∀ z : SpaceTime, pairTerm (fun t y => ∑ c : Fin 3, Lc c (t, y) •
        coordinateVector c) ψ z = ∑ c : Fin 3, Lc c z * ψ z c := by
      intro z
      rw [pairTerm, sum_inner]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [real_inner_smul_left, real_inner_comm,
        UnforcedLeray.Cons.L2.FreeLapReg.inner_coordinateVector]
    have iL : Integrable (diffusionTerm w ψ) := by
      have e : diffusionTerm w ψ =
          fun z => ∑ c : Fin 3, w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c := funext hptL
      rw [e]
      exact integrable_finsetSum _ fun c _ => (hEq c ψ hψ hsupp).1
    have iR : Integrable (pairTerm (fun t y => ∑ c : Fin 3, Lc c (t, y) •
        coordinateVector c) ψ) := by
      have e : pairTerm (fun t y => ∑ c : Fin 3, Lc c (t, y) • coordinateVector c) ψ =
          fun z => ∑ c : Fin 3, Lc c z * ψ z c := funext hptR
      rw [e]
      exact integrable_finsetSum _ fun c _ => (hEq c ψ hψ hsupp).2.1
    refine ⟨iL, iR, ?_⟩
    simp_rw [hptL, hptR]
    rw [integral_finsetSum _ fun c _ => (hEq c ψ hψ hsupp).1,
      integral_finsetSum _ fun c _ => (hEq c ψ hψ hsupp).2.1]
    exact Finset.sum_congr rfl fun c _ => (hEq c ψ hψ hsupp).2.2

end UnforcedLeray.Short.Interface
