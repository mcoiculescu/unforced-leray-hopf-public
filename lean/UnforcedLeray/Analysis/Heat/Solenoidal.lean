import UnforcedLeray.Analysis.Heat.Flow
import UnforcedLeray.Analysis.LerayProjection.Translation

/-!
# Actual heat evolution and the solenoidal L² constraint

The proved spatial translation invariance of the genuine orthogonal Leray
projection passes through the Bochner convolution integral. Every scalar L¹
convolution therefore commutes with that projection and preserves the actual
distributional divergence-free condition. The viscosity-one heat semigroup
and its raw field representative inherit these properties, including time zero.
No Fourier multiplier or pressure representation is assumed here.
-/
noncomputable section
open MeasureTheory Filter
namespace UnforcedLeray.Heat

/-- The two concrete translation conventions differ by the sign of the shift. -/
theorem translation_eq_leray_apply (a : Space) (u : L2Space) :
    translation a u = Leray.translation (-a) u := by
  apply Lp.ext
  filter_upwards [translation_ae a u, Leray.coeFn_translation (-a) u] with x hx hy
  rw [hx, hy, sub_eq_add_neg]

/-- The actual Leray projection also commutes with the heat convention of translation. -/
theorem projection_translation (a : Space) (u : L2Space) :
    Leray.projection (translation a u) = translation a (Leray.projection u) := by
  calc
    Leray.projection (translation a u) = Leray.projection (Leray.translation (-a) u) :=
      congrArg Leray.projection (translation_eq_leray_apply a u)
    _ = Leray.translation (-a) (Leray.projection u) := Leray.projection_translation (-a) u
    _ = translation a (Leray.projection u) :=
      (translation_eq_leray_apply a (Leray.projection u)).symm

/-- Every genuine scalar L¹ convolution commutes with the actual L² Leray projection. -/
theorem projection_convolutionOperator (k : Space → ℝ) (hk : Integrable k volume)
    (u : L2Space) :
    Leray.projection (convolutionOperator k hk u) =
      convolutionOperator k hk (Leray.projection u) := by
  calc
    Leray.projection (convolutionOperator k hk u) =
        Leray.projection (∫ y : Space, k y • translation y u) :=
      congrArg Leray.projection (convolutionOperator_eq_integral_translationOrbit k hk u)
    _ = ∫ y : Space, Leray.projection (k y • translation y u) :=
      (Leray.projection.integral_comp_comm (convolutionOrbit_integrable k hk u)).symm
    _ = ∫ y : Space, k y • translation y (Leray.projection u) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [map_smul, projection_translation]
    _ = convolutionOperator k hk (Leray.projection u) :=
      (convolutionOperator_eq_integral_translationOrbit k hk (Leray.projection u)).symm

/-- The commutation identity holds as an equality of actual bounded operators. -/
theorem projection_comp_convolutionOperator (k : Space → ℝ) (hk : Integrable k volume) :
    Leray.projection.comp (convolutionOperator k hk) =
      (convolutionOperator k hk).comp Leray.projection := by
  apply ContinuousLinearMap.ext
  intro u
  exact projection_convolutionOperator k hk u

/-- Scalar L¹ convolution preserves the concrete weak divergence-free condition. -/
theorem convolutionOperator_solenoidal (k : Space → ℝ) (hk : Integrable k volume)
    {u : L2Space} (hu : IsSolenoidal (u : SpatialField)) :
    IsSolenoidal (convolutionOperator k hk u : SpatialField) := by
  apply (Leray.projection_eq_self_iff _).mp
  rw [projection_convolutionOperator, Leray.projection_eq_self hu]

/-- The same preservation holds for the literal spatial Bochner integral. -/
theorem convolution_solenoidal (k : Space → ℝ) (hk : Integrable k volume)
    {f : SpatialField} (hf : MemLp f 2 volume) (hsol : IsSolenoidal f) :
    IsSolenoidal (convolution k f) := by
  have hclass : IsSolenoidal (toL2 f : SpatialField) :=
    Leray.solenoidal_congr_ae hsol (coeFn_toL2 hf).symm
  have hrep : (convolutionOperator k hk (toL2 f) : SpatialField) =ᵐ[volume]
      convolution k f := by
    have he := convolution_congr_ae (EventuallyEq.rfl (f := k)) (coeFn_toL2 hf)
    exact (convolutionToL2_rep k hk (toL2 f)).trans
      (Eventually.of_forall (fun x => congrFun he x))
  exact Leray.solenoidal_congr_ae (convolutionOperator_solenoidal k hk hclass) hrep

/-- The actual heat semigroup commutes with the actual orthogonal Leray projection. -/
theorem projection_heatOperator (t : ℝ) (u : L2Space) :
    Leray.projection (heatOperator t u) = heatOperator t (Leray.projection u) := by
  by_cases ht : 0 < t
  · rw [heatOperator_pos ht]
    exact projection_convolutionOperator (kernel t) (kernel_integrable ht) u
  · rw [heatOperator_nonpos (le_of_not_gt ht)]
    rfl

theorem projection_comp_heatOperator (t : ℝ) :
    Leray.projection.comp (heatOperator t) = (heatOperator t).comp Leray.projection := by
  apply ContinuousLinearMap.ext
  intro u
  exact projection_heatOperator t u

/-- Every heat time preserves the genuine distributional solenoidal constraint. -/
theorem heatOperator_solenoidal (t : ℝ) {u : L2Space}
    (hu : IsSolenoidal (u : SpatialField)) : IsSolenoidal (heatOperator t u : SpatialField) := by
  apply (Leray.projection_eq_self_iff _).mp
  rw [projection_heatOperator, Leray.projection_eq_self hu]

/-- The literal heat flow preserves IsSolenoidal, including its test-integrability guards. -/
theorem flow_solenoidal {f : SpatialField} (hf : MemLp f 2 volume)
    (hsol : IsSolenoidal f) (t : ℝ) : IsSolenoidal (flow f t) := by
  have hclass : IsSolenoidal (toL2 f : SpatialField) :=
    Leray.solenoidal_congr_ae hsol (coeFn_toL2 hf).symm
  have hflow : IsSolenoidal (toL2 (flow f t) : SpatialField) := by
    rw [toL2_flow hf]
    exact heatOperator_solenoidal t hclass
  exact Leray.solenoidal_congr_ae hflow (coeFn_toL2 (flow_memLp hf t))

end UnforcedLeray.Heat
