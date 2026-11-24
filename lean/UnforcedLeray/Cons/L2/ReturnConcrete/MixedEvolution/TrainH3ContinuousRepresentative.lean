import UnforcedLeray.Lib.TrainB.WeakEmbedding
import UnforcedLeray.Lib.TrainB.WeakGraph
import UnforcedLeray.Lib.TrainB.TensorBridge

/-!
# Quantitative continuous representatives for cylinder H³

The B0151 H²-to-L∞ estimate and H³ smooth density give an actual bounded continuous periodic
representative of every scalar H³ class, with a period-independent norm bound. This is an
unweighted embedding only; it does not give a polynomially weighted curl estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

/-- Every scalar cylinder H³ class has a periodic BCF representative bounded by twelve times its
actual H³ graph norm. The constant is independent of the cylinder period for `c ≥ 1`. -/
theorem exists_scalarH3_bcf_representative {c : ℝ} (hc1 : 1 ≤ c)
    (x : ScalarH3 c) :
    ∃ F : Plane →ᵇ ℝ,
      (F : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) ∧
      (∀ z, F (z + (c, 0)) = F z) ∧ ‖F‖ ≤ 12 * ‖x‖ := by
  obtain ⟨xseq, f, hf, F, Fseq, hxrep, hFseq, hF, hvalue, hxlim⟩ :=
    exists_h3_uniform_representative_sequence hc1 x
  have hnormSeq : ∀ n, ‖Fseq n‖ ≤ 12 * ‖xseq n‖ := by
    intro n
    have hpoint : ∀ z, ‖f n z‖ ≤ 12 * ‖xseq n‖ := by
      intro z
      have hc : 0 < c := lt_of_lt_of_le (by norm_num) hc1
      let xs := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (f n) (hf n)
      have hR : 12 * ENNReal.ofReal ‖xs‖ ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
      have h := ENNReal.toReal_mono hR
        (smooth_h3_lowDerivative_enorm_bound hc1 (hf n) [] (by simp) z)
      simp only [UnforcedLeray.B0151.derivWord] at h
      dsimp [xs] at h
      rw [← hxrep n] at h
      -- `hxrep` identifies the smooth approximation with its actual H³ class.
      simpa [xs, hc, toReal_enorm, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (norm_nonneg _)] using h
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro z
    rw [hFseq n z]
    exact hpoint z
  have hnormLeft : Tendsto (fun n => ‖Fseq n‖) atTop (𝓝 ‖F‖) :=
    (continuous_norm.tendsto F).comp hF
  have hscale : Continuous (fun y : ScalarH3 c => (12 : ℝ) * ‖y‖) :=
    continuous_const.mul continuous_norm
  have hnormRight : Tendsto (fun n => 12 * ‖xseq n‖) atTop (𝓝 (12 * ‖x‖)) :=
    (hscale.tendsto x).comp hxlim
  have hnormF : ‖F‖ ≤ 12 * ‖x‖ :=
    le_of_tendsto_of_tendsto hnormLeft hnormRight (Eventually.of_forall hnormSeq)
  have hperiodic : ∀ z, F (z + (c, 0)) = F z := by
    intro z
    have hL : Tendsto (fun n => Fseq n (z + (c, 0))) atTop (𝓝 (F (z + (c, 0)))) :=
      ((continuous_eval_const (z + (c, 0))).tendsto F).comp hF
    have hR : Tendsto (fun n => Fseq n z) atTop (𝓝 (F z)) :=
      ((continuous_eval_const z).tendsto F).comp hF
    have heq : (fun n => Fseq n (z + (c, 0))) =ᶠ[atTop] (fun n => Fseq n z) :=
      Filter.Eventually.of_forall fun n => by
        calc
          Fseq n (z + (c, 0)) = f n (z + (c, 0)) := hFseq n _
          _ = f n z := (hf n).periodic z
          _ = Fseq n z := (hFseq n z).symm
    exact tendsto_nhds_unique (hL.congr' heq) hR
  exact ⟨F, hvalue, hperiodic, hnormF⟩

/-- Each coordinate of a vector cylinder H³ class has the corresponding actual continuous
periodic representative, with the same period-independent estimate. -/
theorem exists_vectorH3_component_bcf_representative {c : ℝ} (hc1 : 1 ≤ c)
    (i : Fin 2) (x : VectorH3 c) :
    ∃ F : Plane →ᵇ ℝ,
      (F : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        (fun z => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ UnforcedLeray.Train.Vec 3 2 x z) i) ∧
      (∀ z, F (z + (c, 0)) = F z) ∧ ‖F‖ ≤ 12 * ‖x‖ := by
  obtain ⟨F, hrep, hperiodic, hnorm⟩ :=
    exists_scalarH3_bcf_representative hc1 (vectorH3Component i x)
  have hnorm' : ‖F‖ ≤ 12 * ‖x‖ :=
    le_trans hnorm (mul_le_mul_of_nonneg_left (norm_vectorH3Component_apply_le i x)
      (by norm_num))
  exact ⟨F, hrep.trans (vectorH3Component_value_ae i x), hperiodic, hnorm'⟩

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.exists_scalarH3_bcf_representative
#print axioms UnforcedLeray.TrainB.exists_vectorH3_component_bcf_representative
