import NavierStokes.R3.SmoothSobolevL6
import UnforcedLeray.Analysis.SobolevGraph.Functions
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# The genuine smooth homogeneous Sobolev inequality on R³

The compact-cutoff/Fatou proof is imported unchanged from OpenAI's
NavierStokesAndEuler, pinned in `lean/BASELINE-SOURCES.json` under Apache-2.0.
This module specializes it to this project's actual spatial fields and
relates the full Fréchet derivative to the three coordinate derivatives.
The coordinate operator-norm proof adapts `operator_norm_sq_le` in the same
pinned source's `NavierStokes/R3CutoffSobolev.lean`; the resulting statement
retains its coordinate-sum bound before squaring.
It does not assume an embedding or a smooth-density certificate.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators

namespace UnforcedLeray.SobolevEmbedding

/-- The genuine finite Mathlib Sobolev constant for dimension three and p=2. -/
def sobolevConstant : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2

/-- The original whole-space smooth inequality in this project's spatial type. -/
theorem smooth_eLpNorm_six_le {f : SpatialField} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤ (sobolevConstant : ℝ≥0∞) *
      eLpNorm (fderiv ℝ f) 2 volume :=
  NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le hf h2

/-- The operator norm is controlled by the actual coordinate images. -/
theorem norm_le_sum_coordinates (A : Space →L[ℝ] Space) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (coordinateVector i)‖ := by
  have hrepr (v : Space) : ∑ i : Fin 3, v i • coordinateVector i = v := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  calc
    ‖A v‖ = ‖A (∑ i : Fin 3, v i • coordinateVector i)‖ := by rw [hrepr]
    _ = ‖∑ i : Fin 3, v i • A (coordinateVector i)‖ := by simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • A (coordinateVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖A (coordinateVector i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (coordinateVector i)‖) * ‖v‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- The full derivative's L² norm is bounded by the sum of its coordinate L² norms. -/
theorem eLpNorm_fderiv_le_sum_coordinates {f : SpatialField} (hf : ContDiff ℝ 1 f) :
    eLpNorm (fderiv ℝ f) 2 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume := by
  have hc (i : Fin 3) : Continuous (fun x => fderiv ℝ f x (coordinateVector i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  calc
    eLpNorm (fderiv ℝ f) 2 volume ≤
        eLpNorm (fun x => ∑ i : Fin 3, ‖fderiv ℝ f x (coordinateVector i)‖) 2 volume :=
      eLpNorm_mono_real (fun x => norm_le_sum_coordinates (fderiv ℝ f x))
    _ = eLpNorm (∑ i : Fin 3, fun x => ‖fderiv ℝ f x (coordinateVector i)‖) 2 volume := by
      rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => ‖fderiv ℝ f x (coordinateVector i)‖) 2 volume :=
      eLpNorm_sum_le (fun i _ => (hc i).norm.aestronglyMeasurable) (by norm_num)
    _ = _ := by simp only [eLpNorm_norm]

/-- Coordinate L² derivative assumptions supply the full L² Fréchet derivative. -/
theorem smooth_memLp_fderiv_of_coordinates {f : SpatialField} (hf : ContDiff ℝ 1 f)
    (hD : ∀ i : Fin 3, MemLp (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume) :
    MemLp (fderiv ℝ f) 2 volume := by
  refine ⟨(hf.continuous_fderiv (by norm_num)).aestronglyMeasurable,
    (eLpNorm_fderiv_le_sum_coordinates hf).trans_lt ?_⟩
  exact ENNReal.sum_lt_top.mpr (fun i _ => (hD i).2)

/-- Homogeneous Sobolev bound in terms of the three coordinate derivatives. -/
theorem smooth_eLpNorm_six_le_sum_coordinates {f : SpatialField} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤ (sobolevConstant : ℝ≥0∞) *
      ∑ i : Fin 3, eLpNorm (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume :=
  (smooth_eLpNorm_six_le hf h2).trans
    (by gcongr; exact eLpNorm_fderiv_le_sum_coordinates hf)

/-- Finite L⁶ membership follows from genuine coordinate L² derivatives. -/
theorem smooth_memLp_six_of_coordinates {f : SpatialField} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD : ∀ i : Fin 3, MemLp (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume) :
    MemLp f 6 volume :=
  NavierStokesR3.RieszTestOperators.smooth_memLp_six hf h2
    (smooth_memLp_fderiv_of_coordinates hf hD)

/-- The same bound with finite real-valued Lᵖ norms. -/
theorem smooth_l6Norm_le_sum_l2Norm {f : SpatialField} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD : ∀ i : Fin 3, MemLp (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤ (sobolevConstant : ℝ) *
      ∑ i : Fin 3, l2Norm (fun x => fderiv ℝ f x (coordinateVector i)) := by
  have hfinite : (sobolevConstant : ℝ≥0∞) *
      ∑ i : Fin 3, eLpNorm (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.sum_lt_top.mpr (fun i _ => (hD i).2))).ne
  have h := ENNReal.toReal_mono hfinite (smooth_eLpNorm_six_le_sum_coordinates hf h2)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun i _ => (hD i).2.ne), l2Norm] using h

/-- A C¹ field with its actual L² coordinate derivatives gives an element of
the existing weak Sobolev graph by the proved integration-by-parts bridge. -/
def smoothH1 (f : SpatialField) (hf : ContDiff ℝ 1 f) (h2 : MemLp f 2 volume)
    (hD : ∀ i : Fin 3, MemLp (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume) :
    SobolevGraph.H1 :=
  SobolevGraph.H1.ofFields f (fun i x => fderiv ℝ f x (coordinateVector i)) h2 hD
    (hasWeakSpatialDerivative_of_contDiff hf)

@[simp] theorem smoothH1_value (f : SpatialField) (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD : ∀ i : Fin 3, MemLp (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume) :
    (smoothH1 f hf h2 hD).value = toL2 f := rfl

@[simp] theorem smoothH1_derivative (f : SpatialField) (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD : ∀ i : Fin 3, MemLp (fun x => fderiv ℝ f x (coordinateVector i)) 2 volume)
    (i : Fin 3) :
    (smoothH1 f hf h2 hD).derivative i =
      toL2 (fun x => fderiv ℝ f x (coordinateVector i)) := rfl

end UnforcedLeray.SobolevEmbedding
