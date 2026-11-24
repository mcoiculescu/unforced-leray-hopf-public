import UnforcedLeray.Lib.HeatCylinder.H3Linearity

/-!
# Completion estimate for actual cylinder heatDiv on H³ data

The smooth Gaussian output operator has a difference estimate in the centered-cell
derivative-energy distance. This file turns it into a Cauchy sequence theorem, ready to pair with
cylinder smooth density in the Euclidean tensor carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- The centered-cell derivative-energy distance between two smooth tensor fields. -/
noncomputable def heatTensorH3Distance (c : ℝ) (T U : Plane → Plane × Plane) : ℝ :=
  Real.sqrt (∑ α : UnforcedLeray.Sob.Idx 2 3,
    (eLpNorm (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α)
      (fun z => T z - U z)) 2 (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2)


/-- The actual H³ outputs of a sequence of smooth cylinder tensors. Explicitly fixing the
input field prevents Lean from recovering it by reducing the large smoothness proof. -/
noncomputable def smoothHeatOutputSequence {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : ℕ → Plane → Plane × Plane}
    (hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n)) :
    ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
  fun n => heatDivH3 (c := c) (θ := θ) (T := T n) hc hθ (hT n)

/-- Cauchy convergence of smooth tensor representatives in the centered-cell derivative energy
passes through the actual Gaussian heat output into the train H³ graph. -/
theorem heatOutputSequence_cauchy_of_heatTensorH3Distance {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {T : ℕ → Plane → Plane × Plane}
    (hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n))
    (hsub : ∀ m n, UnforcedLeray.Sob.IsCylSmooth c (fun z => T m z - T n z))
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      heatTensorH3Distance c (T m) (T n) < ε) :
    CauchySeq (smoothHeatOutputSequence hc hθ hT) := by
  let u : ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
    smoothHeatOutputSequence hc hθ hT
  have hpair : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε := by
    intro ε hε
    let K : ℝ := (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff θ)).toReal
    let δ : ℝ := ε / (K + 1)
    have hK : 0 ≤ K := by
      dsimp [K]
      exact ENNReal.toReal_nonneg
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    obtain ⟨N, hN⟩ := hC δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hbound := norm_heatDivH3_sub_le_energy (c := c) (θ := θ)
      (T := T m) (U := T n) hc hθ (hT m) (hT n) (hsub m n)
    have hnorm : ‖u m - u n‖ ≤ K * heatTensorH3Distance c (T m) (T n) := by
      change ‖heatDivH3 (c := c) (θ := θ) (T := T m) hc hθ (hT m) -
          heatDivH3 (c := c) (θ := θ) (T := T n) hc hθ (hT n)‖ ≤
        ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
          ENNReal.ofReal (heatDivL2Coeff θ)).toReal) *
          Real.sqrt (∑ α : UnforcedLeray.Sob.Idx 2 3,
            (eLpNorm (UnforcedLeray.Sob.iterD
              ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T m z - T n z))
              2 (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2)
      exact hbound
    have hdistNonneg : 0 ≤ heatTensorH3Distance c (T m) (T n) := Real.sqrt_nonneg _
    have hKone : 0 < K + 1 := by linarith
    calc
      dist (u m) (u n) ≤ K * heatTensorH3Distance c (T m) (T n) := by
        rw [dist_eq_norm]
        exact hnorm
      _ ≤ K * δ := mul_le_mul_of_nonneg_left (hN m hm n hn).le hK
      _ < (K + 1) * δ := by nlinarith [hδ]
      _ = ε := by
        dsimp [δ]
        field_simp [hKone.ne']
  have hu : CauchySeq u := (Metric.cauchySeq_iff (u := u)).2 hpair
  change CauchySeq u
  exact hu

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatOutputSequence_cauchy_of_heatTensorH3Distance
