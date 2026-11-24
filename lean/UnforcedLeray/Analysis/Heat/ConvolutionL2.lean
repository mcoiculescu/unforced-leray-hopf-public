import UnforcedLeray.Analysis.Heat.ConvolutionExistence
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Actual L¹-kernel convolution on vector L²(R³)

The operator is defined by the ordinary Bochner integral, with an explicit
Young inequality and a.e. integrability of its integrand. It acts on the
standard Lebesgue L² quotient, not on a postulated abstract heat space.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace UnforcedLeray.Heat

/-- Literal scalar-kernel convolution of a spatial vector field. -/
def convolution (k : Space → ℝ) (f : SpatialField) : SpatialField :=
  fun x => ∫ y : Space, k y • f (x - y)

theorem convolution_joint_aestronglyMeasurable {k : Space → ℝ} {f : SpatialField}
    (hk : AEStronglyMeasurable k volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z : Space × Space => k z.2 • f (z.1-z.2))
      ((volume : Measure Space).prod volume) :=
  hk.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf

theorem convolution_aestronglyMeasurable {k : Space → ℝ} {f : SpatialField}
    (hk : AEStronglyMeasurable k volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (convolution k f) volume :=
  (convolution_joint_aestronglyMeasurable hk hf).integral_prod_right'

/-- Young's L¹*L² inequality for actual scalar-vector convolution. -/
theorem eLpNorm_convolution_le {k : Space → ℝ} {f : SpatialField}
    (hk : Integrable k volume) (hf : MemLp f 2 volume) :
    eLpNorm (convolution k f) 2 volume ≤ eLpNorm k 1 volume * eLpNorm f 2 volume := by
  have hjoint := convolution_joint_aestronglyMeasurable hk.aestronglyMeasurable
    hf.aestronglyMeasurable
  have hM := NonUniqueEuler.Conv.eLpNorm_integral_le (F := fun x y => k y • f (x-y))
    hjoint (p := 2) (by norm_num) (by norm_num)
  refine hM.trans_eq ?_
  calc
    (∫⁻ y : Space, eLpNorm (fun x => k y • f (x-y)) 2 volume) =
        ∫⁻ y : Space, ‖k y‖ₑ * eLpNorm f 2 volume := by
      apply lintegral_congr
      intro y
      change eLpNorm (k y • (fun x => f (x-y))) 2 volume = _
      rw [eLpNorm_const_smul]
      congr 1
      exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        (measurePreserving_sub_right (volume : Measure Space) y)
    _ = (∫⁻ y : Space, ‖k y‖ₑ) * eLpNorm f 2 volume :=
      lintegral_mul_const' _ _ hf.2.ne
    _ = eLpNorm k 1 volume * eLpNorm f 2 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm]

theorem memLp_convolution {k : Space → ℝ} {f : SpatialField}
    (hk : Integrable k volume) (hf : MemLp f 2 volume) :
    MemLp (convolution k f) 2 volume := by
  refine ⟨convolution_aestronglyMeasurable hk.aestronglyMeasurable hf.aestronglyMeasurable,
    lt_of_le_of_lt (eLpNorm_convolution_le hk hf) ?_⟩
  exact ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hk).2 hf.2

/-- An a.e. change of either input leaves every convolution value unchanged. -/
theorem convolution_congr_ae {k k' : Space → ℝ} {f f' : SpatialField}
    (hk : k =ᵐ[volume] k') (hf : f =ᵐ[volume] f') :
    convolution k f = convolution k' f' := by
  exact MeasureTheory.convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) hk hf

/-- Addition of actual fields commutes with convolution outside a null set. -/
theorem convolution_add_ae {k : Space → ℝ} {f g : SpatialField}
    (hk : Integrable k volume) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    convolution k (f+g) =ᵐ[volume] convolution k f + convolution k g := by
  filter_upwards [ae_integrable_convolution hk hf, ae_integrable_convolution hk hg]
    with x hx hy
  change (∫ y : Space, k y • (f (x-y) + g (x-y))) = _
  simp only [smul_add]
  exact integral_add hx hy

/-- Scalar multiplication commutes with the literal Bochner integral. -/
theorem convolution_smul (k : Space → ℝ) (c : ℝ) (f : SpatialField) :
    convolution k (c • f) = c • convolution k f := by
  exact MeasureTheory.convolution_smul (L := ContinuousLinearMap.lsmul ℝ ℝ)

/-- Convolution on the standard L² equivalence classes. -/
def convolutionToL2 (k : Space → ℝ) (hk : Integrable k volume) (f : L2Space) : L2Space :=
  (memLp_convolution hk (Lp.memLp f)).toLp (convolution k f)

theorem convolutionToL2_rep (k : Space → ℝ) (hk : Integrable k volume) (f : L2Space) :
    (convolutionToL2 k hk f : SpatialField) =ᵐ[volume] convolution k f :=
  (memLp_convolution hk (Lp.memLp f)).coeFn_toLp

theorem convolutionToL2_add (k : Space → ℝ) (hk : Integrable k volume) (f g : L2Space) :
    convolutionToL2 k hk (f+g) = convolutionToL2 k hk f + convolutionToL2 k hk g := by
  apply Lp.ext
  have he := convolution_congr_ae (Filter.EventuallyEq.rfl (f := k)) (Lp.coeFn_add f g)
  filter_upwards [convolutionToL2_rep k hk (f+g), convolutionToL2_rep k hk f,
    convolutionToL2_rep k hk g,
    Lp.coeFn_add (convolutionToL2 k hk f) (convolutionToL2 k hk g),
    convolution_add_ae hk (Lp.memLp f) (Lp.memLp g)] with x hsum hf hg hadd hraw
  rw [hsum, he, hraw, hadd]
  exact congrArg₂ (· + ·) hf.symm hg.symm

theorem convolutionToL2_smul (k : Space → ℝ) (hk : Integrable k volume)
    (c : ℝ) (f : L2Space) :
    convolutionToL2 k hk (c • f) = c • convolutionToL2 k hk f := by
  apply Lp.ext
  have he := convolution_congr_ae (Filter.EventuallyEq.rfl (f := k)) (Lp.coeFn_smul c f)
  filter_upwards [convolutionToL2_rep k hk (c • f), convolutionToL2_rep k hk f,
    Lp.coeFn_smul c (convolutionToL2 k hk f)] with x hsum hf hsmul
  rw [hsum, he, convolution_smul, hsmul]
  exact congrArg (c • ·) hf.symm

theorem convolutionToL2_norm_le (k : Space → ℝ) (hk : Integrable k volume) (f : L2Space) :
    ‖convolutionToL2 k hk f‖ ≤ (∫ y : Space, ‖k y‖) * ‖f‖ := by
  change ‖(memLp_convolution hk (Lp.memLp f)).toLp (convolution k f)‖ ≤ _
  rw [Lp.norm_toLp]
  have hlt : eLpNorm k 1 volume * eLpNorm (f : SpatialField) 2 volume ≠ ∞ :=
    (ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hk).2 (Lp.memLp f).2).ne
  have h := ENNReal.toReal_mono hlt (eLpNorm_convolution_le hk (Lp.memLp f))
  simpa only [ENNReal.toReal_mul, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hk.aestronglyMeasurable, Lp.norm_def] using h

/-- The actual convolution map, with linearity established from a.e. convergent integrals. -/
def convolutionLinear (k : Space → ℝ) (hk : Integrable k volume) : L2Space →ₗ[ℝ] L2Space where
  toFun := convolutionToL2 k hk
  map_add' := convolutionToL2_add k hk
  map_smul' := convolutionToL2_smul k hk

/-- The bounded convolution operator on the actual whole-space vector L² space. -/
def convolutionOperator (k : Space → ℝ) (hk : Integrable k volume) : L2Space →L[ℝ] L2Space :=
  (convolutionLinear k hk).mkContinuous (∫ y : Space, ‖k y‖) (convolutionToL2_norm_le k hk)

@[simp] theorem convolutionOperator_apply (k : Space → ℝ) (hk : Integrable k volume)
    (f : L2Space) : convolutionOperator k hk f = convolutionToL2 k hk f := rfl

/-- Sharp Young operator bound, without a unit-mass hypothesis. -/
theorem convolutionOperator_norm_le (k : Space → ℝ) (hk : Integrable k volume) :
    ‖convolutionOperator k hk‖ ≤ ∫ y : Space, ‖k y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ => norm_nonneg _))
  exact convolutionToL2_norm_le k hk

end UnforcedLeray.Heat

