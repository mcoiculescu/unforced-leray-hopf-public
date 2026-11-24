import UnforcedLeray.Lib.TrainB.DatumH3UniformNorm
import UnforcedLeray.Lib.TrainB.DatumHeatSolenoidalMild
import UnforcedLeray.Lib.TrainB.DatumHeatMildAllComponents
import UnforcedLeray.Lib.TrainB.DatumHeatAgeEnvelope
import UnforcedLeray.Lib.TrainB.P0CompactMildSolenoidal
import UnforcedLeray.Lib.TrainB.P0CompactMildUniqueness

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- A common interval, independent of the period `c ≥ 2`, supports the actual Gaussian-datum
H³ mild train. Its radius is the period-independent H³ datum envelope derived from B0141's
uniform jet bounds. The equation uses the literal heat seed and actual projected Gaussian
nonlinearity, and retains the actual datum trace, all-component solenoidality, and ball uniqueness.
-/
theorem exists_uniform_short_datumHeat_solenoidal_mild_train {ν : ℝ} (hν : 0 < ν) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∀ c : ℝ, (hc2 : 2 ≤ c) →
        ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖u‖ ≤ 2 * (4 * datumUniformH3ComponentConstant) ∧
          u = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
            projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
              (by linarith : 1 ≤ c) hν hT.le u ∧
          (∀ t, P0H3CLM (by linarith : 0 < c) (u t) = u t) ∧
          vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
            (memLp_datum_word_derivative (by linarith : 0 < c) Sob.Idx.zero).toLp
              (Train.datum c) ∧
          (∀ t α, vecH3CellDerivCLM α (u t) ∈ Cyl.divFree c) ∧
          (∀ t : Icc (0 : ℝ) T, ∀ α : Sob.Idx 2 3,
            ‖vecH3CellDerivCLM α (u t)‖ ≤ 2 * (4 * datumUniformH3ComponentConstant)) ∧
          (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
            ‖v‖ ≤ 2 * (4 * datumUniformH3ComponentConstant) →
            v = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
              projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
                (by linarith : 1 ≤ c) hν hT.le v → v = u) := by
  let B : ℝ := 4 * datumUniformH3ComponentConstant
  let R : ℝ := 2 * B
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by norm_num) datumUniformH3ComponentConstant_nonneg
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨T, hT, hsmall⟩ := exists_train_short_contraction_time hν hR
  refine ⟨T, hT, fun c hc2 => ?_⟩
  have hc : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  let g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) :=
    (datumHeatSeedPath hc hν).comp compactTimeInclusion
  have hg : ‖g‖ ≤ R / 2 := by
    have hhalf : 0 ≤ R / 2 := by dsimp [R]; nlinarith [hB]
    rw [ContinuousMap.norm_le _ hhalf]
    intro t
    change ‖datumHeatSeedPath hc hν (t : ℝ)‖ ≤ R / 2
    calc
      ‖datumHeatSeedPath hc hν (t : ℝ)‖ ≤ ‖datumVecH3 hc‖ :=
        datumHeatSeedPath_norm_le hc hν (t : ℝ)
      _ ≤ B := by simpa [B] using datumVecH3_norm_le_uniform hc hc2
      _ = R / 2 := by dsimp [R]; ring
  have hgfix : ∀ t, P0H3CLM hc (g t) = g t := by
    intro t
    apply P0H3CLM_eq_self_of_components_divFree hc
    exact datumHeatSeedPath_components_divFree hc2 hν (t : ℝ)
  have hgzero' : g (compactEvolutionZero hT) = datumVecH3 hc := by
    change datumHeatSeedPath hc hν 0 = _
    exact datumHeatSeedPath_zero hc hν
  have hdatumP0 : P0H3CLM hc (datumVecH3 hc) = datumVecH3 hc :=
    P0H3CLM_eq_self_of_components_divFree hc (datumVecH3 hc)
      (datumVecH3_components_divFree hc)
  have hgzero : g (compactEvolutionZero hT) = projectedInitialDatumH3 hc := by
    rw [hgzero', ← hdatumP0]
    rfl
  obtain ⟨u, hu, hfix⟩ := exists_compact_actual_mild_fixedPoint
    hc hc1 hν hT hR hsmall g hg
  have hsol := compactActualMildFixedPoint_solenoidal hc hc1 hν hT g u hfix hgfix
  have htrace := compactActualMildFixedPoint_actualDatumTrace hc hc1 hν hT g u hfix hgzero
  have hu' : ‖u‖ ≤ R := hu
  have hfix' : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u := hfix
  refine ⟨u, ?_, ?_, hsol, htrace, ?_, ?_, ?_⟩
  · simpa [R, B] using hu'
  · simpa [g, compactTimeInclusion] using hfix'
  · intro t α
    exact components_divFree_of_P0H3CLM_fixed hc (u t) (hsol t) α
  · intro t α
    calc
      ‖vecH3CellDerivCLM α (u t)‖ ≤ ‖u t‖ := vecH3CellDeriv_norm_le α (u t)
      _ ≤ ‖u‖ := u.norm_coe_le_norm t
      _ ≤ R := hu'
      _ = 2 * (4 * datumUniformH3ComponentConstant) := by dsimp [R, B]
  · intro v hv hfv
    have hfv' : v = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v := by
      simpa [g, compactTimeInclusion] using hfv
    have huniq := compactActualMildFixedPoint_unique hc hc1 hν hT hR hsmall
      g u v hu' (by simpa [R, B] using hv) hfix' hfv'
    exact huniq.symm

#print axioms UnforcedLeray.TrainB.exists_uniform_short_datumHeat_solenoidal_mild_train

end UnforcedLeray.TrainB
