import UnforcedLeray.Short.PartIIb.Sub.T22_1.Plan
import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Decomposition of `PartII-b:T22/1/1` (`TrainCoeffBdd`)

Source: `the November 2 reference manuscript` lines 2085-2093 (`TrainClose` at orders
`0, 1`), with `IsTrain.smooth_v` and `periodic_v` (`Units/B0140.lean`).  `CylCoeff c (Σ/ν) tr.v` has six
fields; `periodic` is `IsTrain.periodic_v`, and the rest are four leaves:

* `TcRegular`: slices `C¹`, joint continuity of `v` and of `fderiv`;
* `TcBdd`: `v` bounded (from `cylTrainGap`);
* `TcDeltaD1`: `‖D(v - V_c)‖ ≤ δ` (`TrainClose` at `j = 1`, `jb ≥ 1`);
* `TcVcDeriv`: `V_c` differentiable with `DV_c` bounded for `c ≥ 1`, `σ ∈ [0, Σ/ν]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

/-- Leaf 1 (SP 2085-2093): the train velocity is `C¹` in the plane variable on each slice
`σ ≥ 0`, and `v`, `D_x v` are jointly continuous on `[0,T] × ℝ²`.  Source: `IsTrain.smooth_v` on
`Ici 0 ×ˢ univ`; the slice direction is tangent to the product set
(`fderiv ℝ (v σ) x = fderivWithin ℝ (fun z => v z.1 z.2) (Ici 0 ×ˢ univ) (σ,x) ∘ inr`). -/
def TcRegular : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (T : ℝ), 0 ≤ T →
    (∀ σ ∈ Icc 0 T, ContDiff ℝ 1 (tr.v σ)) ∧
    ContinuousOn (fun z : ℝ × Pl => tr.v z.1 z.2) (Icc 0 T ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × Pl => fderiv ℝ (tr.v z.1) z.2) (Icc 0 T ×ˢ univ)

/-- Leaf 2 (SP 2085-2093, via `cylTrainGap`): the train velocity is bounded on `[0, Σ/ν] × ℝ²`. -/
def TcBdd : Prop :=
  ∀ Sg : ℝ, 0 < Sg → ∀ ν c δ : ℝ, 0 < ν → 1 ≤ c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∃ M : ℝ, ∀ σ ∈ Icc 0 (Sg / ν), ∀ x : Pl, ‖tr.v σ x‖ ≤ M

/-- Leaf 3 (SP 2085-2093): `TrainClose` at order `j = 1` with `jb ≥ 1` gives
`‖D(v - V_c)(σ)(x)‖ ≤ δ` (`norm_iteratedFDeriv_one`-type lemma). -/
def TcDeltaD1 : Prop :=
  ∀ Sg : ℝ, 0 < Sg → ∀ ν c δ : ℝ, 0 < ν → 1 ≤ c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ σ ∈ Icc 0 (Sg / ν), ∀ x : Pl,
      ‖fderiv ℝ (fun z => tr.v σ z - UnforcedLeray.Train.Vc ν c σ z) x‖ ≤ δ

/-- Leaf 4 (SP 2205-2211, lattice sum of the Gaussian vortex of width `1 + νσ ∈ [1, 1 + Σ]`): the
periodized heat vortex `V_c(σ)` is differentiable with uniformly bounded derivative for `c ≥ 1`.
Route: `Train.Vc ν c σ = periodize c (isoV ν σ)` (`Lib/Train/PeriodizedVortex.lean`), termwise
differentiation (`hasFDerivAt_tsum`), the Gaussian lattice bounds of `TrainGap/Lattice.lean`;
`B0147.sup_bound_order` needs `heatWidth ≤ c^2`, so a variant with `1 ≤ c`, `heatWidth ≤ A` is needed. -/
def TcVcDeriv : Prop :=
  ∀ Sg : ℝ, 0 < Sg → ∀ ν c : ℝ, 0 < ν → 1 ≤ c →
    (∀ σ ∈ Icc 0 (Sg / ν), Differentiable ℝ (UnforcedLeray.Train.Vc ν c σ)) ∧
    ∃ M : ℝ, ∀ σ ∈ Icc 0 (Sg / ν), ∀ x : Pl, ‖fderiv ℝ (UnforcedLeray.Train.Vc ν c σ) x‖ ≤ M

theorem trainCoeffBdd_of (h1 : TcRegular) (h2 : TcBdd) (h3 : TcDeltaD1) (h4 : TcVcDeriv) :
    TrainCoeffBdd := by
  intro Sg hSg ν c δ hν hc hδ tr hcl
  have hT : 0 ≤ Sg / ν := div_nonneg hSg.le hν.le
  obtain ⟨hs, hc0, hd0⟩ := h1 ν c tr _ hT
  obtain ⟨M, hM⟩ := h2 Sg hSg ν c δ hν hc hδ tr hcl
  obtain ⟨hVd, K, hK⟩ := h4 Sg hSg ν c hν hc
  refine ⟨hs, hc0, hd0, ?_, ⟨M, hM⟩, ⟨δ + K, ?_⟩⟩
  · intro σ hσ x
    exact tr.isTrain.periodic_v σ hσ.1 x
  · intro σ hσ x
    have hv : Differentiable ℝ (tr.v σ) :=
      ((hs σ hσ).differentiable one_ne_zero)
    have heq : fderiv ℝ (tr.v σ) x =
        fderiv ℝ (fun z => tr.v σ z - UnforcedLeray.Train.Vc ν c σ z) x +
          fderiv ℝ (UnforcedLeray.Train.Vc ν c σ) x := by
      rw [show (fun z => tr.v σ z - UnforcedLeray.Train.Vc ν c σ z) =
          tr.v σ - UnforcedLeray.Train.Vc ν c σ from rfl, fderiv_sub (hv x) (hVd σ hσ x)]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (h3 Sg hSg ν c δ hν hc hδ tr hcl σ hσ x) (hK σ hσ x))

end UnforcedLeray.Short.IIb.CylPDE
