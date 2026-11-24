import UnforcedLeray.Analysis.SobolevEmbedding.Density
import UnforcedLeray.Analysis.SobolevGraph.H1

/-!
# Continuous inclusion of the actual weak H¹ graph into L⁶(R³)

The membership and bound below use the proved mollification/Fatou Sobolev
inequality. The input graph consists of the target statement's genuine weak
coordinate derivatives. No embedding or density hypothesis is supplied.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace UnforcedLeray.SobolevEmbedding

instance instFactOneLeSix : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

abbrev L6Space := Lp Space 6 (volume : Measure Space)

/-- Every element of the concrete weak H¹ graph has its actual field in L⁶. -/
theorem h1_memLp_six (F : SobolevGraph.H1) :
    MemLp (F.value : SpatialField) 6 volume :=
  weak_memLp_six (Lp.memLp F.value) (fun i => Lp.memLp (F.derivative i))
    (F.hasWeakDerivative)

/-- The homogeneous inequality retains the actual L² weak derivatives. -/
theorem h1_l6Norm_le_sum_derivative_norm (F : SobolevGraph.H1) :
    (eLpNorm (F.value : SpatialField) 6 volume).toReal ≤
      (sobolevConstant : ℝ) * ∑ i : Fin 3, ‖F.derivative i‖ := by
  exact weak_l6Norm_le_sum (Lp.memLp F.value) (fun i => Lp.memLp (F.derivative i))
    (F.hasWeakDerivative)

theorem h1_derivative_norm_le (F : SobolevGraph.H1) (i : Fin 3) :
    ‖F.derivative i‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : SobolevGraph.H1Ambient) i.succ

theorem h1_sum_derivative_norm_le (F : SobolevGraph.H1) :
    (∑ i : Fin 3, ‖F.derivative i‖) ≤ 3 * ‖F‖ := by
  calc
    _ ≤ ∑ _i : Fin 3, ‖F‖ :=
      Finset.sum_le_sum (fun i _ => h1_derivative_norm_le F i)
    _ = 3 * ‖F‖ := by simp

/-- A bound in the existing complete Hilbert graph norm. -/
theorem h1_l6Norm_le (F : SobolevGraph.H1) :
    (eLpNorm (F.value : SpatialField) 6 volume).toReal ≤
      (3 * (sobolevConstant : ℝ)) * ‖F‖ := by
  calc
    _ ≤ (sobolevConstant : ℝ) * ∑ i : Fin 3, ‖F.derivative i‖ :=
      h1_l6Norm_le_sum_derivative_norm F
    _ ≤ (sobolevConstant : ℝ) * (3 * ‖F‖) :=
      mul_le_mul_of_nonneg_left (h1_sum_derivative_norm_le F) (NNReal.coe_nonneg _)
    _ = _ := by ring

/-- The L⁶ class of the actual H¹ field. -/
def h1ToL6 (F : SobolevGraph.H1) : L6Space :=
  (h1_memLp_six F).toLp (F.value : SpatialField)

theorem coeFn_h1ToL6 (F : SobolevGraph.H1) :
    (h1ToL6 F : SpatialField) =ᵐ[volume] (F.value : SpatialField) :=
  (h1_memLp_six F).coeFn_toLp

theorem h1ToL6_norm_le (F : SobolevGraph.H1) :
    ‖h1ToL6 F‖ ≤ (3 * (sobolevConstant : ℝ)) * ‖F‖ := by
  rw [h1ToL6, Lp.norm_toLp]
  exact h1_l6Norm_le F

/-- The proved Sobolev inclusion, bundled as a linear map. -/
def h1ToL6Linear : SobolevGraph.H1 →ₗ[ℝ] L6Space where
  toFun := h1ToL6
  map_add' F G := by
    apply Lp.ext
    filter_upwards [coeFn_h1ToL6 (F+G), coeFn_h1ToL6 F, coeFn_h1ToL6 G,
      Lp.coeFn_add (h1ToL6 F) (h1ToL6 G), Lp.coeFn_add F.value G.value]
      with x hsum hF hG hLp hval
    change (h1ToL6 (F+G)) x = (h1ToL6 F + h1ToL6 G) x
    rw [hsum, hLp]
    simp only [Pi.add_apply]
    rw [hF, hG]
    exact hval
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [coeFn_h1ToL6 (c • F), coeFn_h1ToL6 F,
      Lp.coeFn_smul c (h1ToL6 F), Lp.coeFn_smul c F.value]
      with x hsmul hF hLp hval
    change (h1ToL6 (c • F)) x = (c • h1ToL6 F) x
    rw [hsmul, hLp]
    simp only [Pi.smul_apply]
    rw [hF]
    exact hval

/-- A genuine continuous linear inclusion H¹(R³;R³) → L⁶(R³;R³). -/
def h1ToL6CLM : SobolevGraph.H1 →L[ℝ] L6Space :=
  h1ToL6Linear.mkContinuous (3 * (sobolevConstant : ℝ)) h1ToL6_norm_le

@[simp] theorem h1ToL6CLM_apply (F : SobolevGraph.H1) : h1ToL6CLM F = h1ToL6 F := rfl

theorem h1ToL6CLM_norm_le : ‖h1ToL6CLM‖ ≤ 3 * (sobolevConstant : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact h1ToL6_norm_le

/-- The inclusion loses no information, because both Lᵖ classes represent the
same vector field and the weak derivatives are uniquely determined. -/
theorem h1ToL6CLM_injective : Function.Injective h1ToL6CLM := by
  intro F G h
  apply SobolevGraph.H1.value_injective
  apply Lp.ext
  have he : (h1ToL6 F : SpatialField) =ᵐ[volume] (h1ToL6 G : SpatialField) := by
    change h1ToL6 F = h1ToL6 G at h
    rw [h]
  exact (coeFn_h1ToL6 F).symm.trans (he.trans (coeFn_h1ToL6 G))

end UnforcedLeray.SobolevEmbedding
