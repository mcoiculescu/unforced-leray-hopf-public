import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Assembly
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Conformal

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: the short leaves of `TjTrainBSRep`, proved

Source: `the November 2 reference manuscript` (SP) lines 270-288 (`v(-x) = -v(x)`),
2081-2084, 2117-2121, 3121. Statements: `BSRep/Defs.lean`.

* `bsrFDerivNorm : BsrFDerivNorm` (calculus);
* `bsrKcOdd : BsrKcOdd` (`K_c` of an even periodic field is odd);
* `bsrWeightIntShift_of : BsrWeightInt → BsrWeightIntShift` (periodic change of variables);
* `bsrLiouville : BsrLiouville` (Cauchy-Riemann and Liouville);
* `tjTrainBSRep_of_rest`: `TjTrainBSRep m` from `TjTrainVort`, `TjVortDecay m`, `TjLadGrad m`,
  `TjKcBound` and the remaining leaves `BsrWeightInt`, `BsrKcHasFDeriv`, `BsrKcFDerivEval`,
  `BsrKerPointwiseDecay`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`BsrFDerivNorm`**: `Df(y)(h) = h₁ ∂_qf(y) + h₂ ∂_ηf(y)` and `|h_i| ≤ ‖h‖`. -/
theorem bsrFDerivNorm : BsrFDerivNorm := by
  intro f y hf
  have hq : fderiv ℝ f y ((1 : ℝ), (0 : ℝ)) = UnforcedLeray.Cyl.partialQ f y := by
    have h0 : HasDerivAt (fun q : ℝ => ((q, y.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
      (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
    exact ((hf.hasFDerivAt.comp_hasDerivAt y.1 h0).deriv).symm
  have he : fderiv ℝ f y ((0 : ℝ), (1 : ℝ)) = UnforcedLeray.Cyl.partialEta f y := by
    have h0 : HasDerivAt (fun η : ℝ => ((y.1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2 :=
      (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
    exact ((hf.hasFDerivAt.comp_hasDerivAt y.2 h0).deriv).symm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
  have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hval : fderiv ℝ f y h = h.1 * UnforcedLeray.Cyl.partialQ f y +
      h.2 * UnforcedLeray.Cyl.partialEta f y := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, map_smul, hq, he, smul_eq_mul, smul_eq_mul]
  have h1 : |h.1| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le h
  have h2 : |h.2| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le h
  rw [hval]
  calc ‖h.1 * UnforcedLeray.Cyl.partialQ f y + h.2 * UnforcedLeray.Cyl.partialEta f y‖
      ≤ ‖h.1 * UnforcedLeray.Cyl.partialQ f y‖ + ‖h.2 * UnforcedLeray.Cyl.partialEta f y‖ :=
        norm_add_le _ _
    _ = |h.1| * |UnforcedLeray.Cyl.partialQ f y| + |h.2| * |UnforcedLeray.Cyl.partialEta f y| := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ ‖h‖ * |UnforcedLeray.Cyl.partialQ f y| + ‖h‖ * |UnforcedLeray.Cyl.partialEta f y| :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    _ = (|UnforcedLeray.Cyl.partialQ f y| + |UnforcedLeray.Cyl.partialEta f y|) * ‖h‖ := by ring

/-- **`BsrKcOdd`**: `K_cω(-x) = ∫_cell ω(x + y) K_c(y) dy = ∫_cell ω(x - y) K_c(-y) dy = -K_cω(x)`
(the reflection `y ↦ -y` preserves cell integrals of periodic functions). -/
theorem bsrKcOdd : BsrKcOdd := by
  intro c hc g hper heven x
  have hG : UnforcedLeray.Cyl.IsPeriodic c
      (fun y : ℝ × ℝ => g (x + y) • UnforcedLeray.Cyl.bsKernel c y) := by
    intro y
    have e : x + ((y.1 + c, y.2) : ℝ × ℝ) = ((x + y).1 + c, (x + y).2) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    show g (x + (y.1 + c, y.2)) • UnforcedLeray.Cyl.bsKernel c (y.1 + c, y.2) =
      g (x + y) • UnforcedLeray.Cyl.bsKernel c y
    rw [UnforcedLeray.Cyl.isPeriodic_bsKernel c y, e, hper (x + y)]
  have h := UnforcedLeray.Cyl.integral_cell_comp_sub_left hc hG 0
  rw [UnforcedLeray.Cyl.K_eq_reflect hc hper (-x), UnforcedLeray.Cyl.K_eq_reflect hc hper x]
  calc ∫ y in UnforcedLeray.Cyl.cell c, g (-x - y) • UnforcedLeray.Cyl.bsKernel c y
      = ∫ y in UnforcedLeray.Cyl.cell c, g (x + y) • UnforcedLeray.Cyl.bsKernel c y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show g (-x - y) • UnforcedLeray.Cyl.bsKernel c y = g (x + y) • UnforcedLeray.Cyl.bsKernel c y
        rw [show -x - y = -(x + y) by abel, heven]
    _ = ∫ y in UnforcedLeray.Cyl.cell c,
          g (x + (0 - y)) • UnforcedLeray.Cyl.bsKernel c (0 - y) := h.symm
    _ = ∫ y in UnforcedLeray.Cyl.cell c, -(g (x - y) • UnforcedLeray.Cyl.bsKernel c y) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show g (x + (0 - y)) • UnforcedLeray.Cyl.bsKernel c (0 - y) =
          -(g (x - y) • UnforcedLeray.Cyl.bsKernel c y)
        rw [zero_sub, bsr_bsKernel_neg, smul_neg, ← sub_eq_add_neg]
    _ = -∫ y in UnforcedLeray.Cyl.cell c, g (x - y) • UnforcedLeray.Cyl.bsKernel c y :=
        integral_neg _

/-- **`BsrWeightIntShift` from `BsrWeightInt`**: the integrand is `c`-periodic in `y₁`, and
`Cyl.lintegral_cell_comp_sub_left` with `‖K_c(-y)‖ = ‖K_c(y)‖` turns its cell integral into that
of `BsrWeightInt` at `a = x₂`. -/
theorem bsrWeightIntShift_of (h : BsrWeightInt) : BsrWeightIntShift := by
  intro c β hc hβ x
  have hc0 : 0 < c := by linarith
  have hwc : Continuous (fun y : ℝ × ℝ => (1 + y.2 ^ 2) ^ (-(β / 2))) :=
    (continuous_const.add (continuous_snd.pow 2)).rpow_const
      (fun y => Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
  have hKm : Measurable (fun y : ℝ × ℝ => ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖) :=
    ((UnforcedLeray.Cyl.measurable_bsKernel c).comp (measurable_id.sub measurable_const)).norm
  have hGm : Measurable (fun y : ℝ × ℝ =>
      (1 + y.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖) :=
    hwc.measurable.mul hKm
  have hGnn : ∀ y : ℝ × ℝ,
      0 ≤ (1 + y.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖ :=
    fun y => mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  have hper : UnforcedLeray.Cyl.IsPeriodic c (fun y : ℝ × ℝ =>
      ENNReal.ofReal ((1 + y.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖)) := by
    intro y
    have e : ((y.1 + c, y.2) : ℝ × ℝ) - x = ((y - x).1 + c, (y - x).2) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
    show ENNReal.ofReal ((1 + y.2 ^ 2) ^ (-(β / 2)) *
        ‖UnforcedLeray.Cyl.bsKernel c ((y.1 + c, y.2) - x)‖) = _
    rw [e, UnforcedLeray.Cyl.isPeriodic_bsKernel c (y - x)]
  have hlin := UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hc0 hper x
  have hint := h c β hc hβ x.2
  refine ⟨hGm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hGnn), ← hlin]
  have e2 : ∀ y : ℝ × ℝ, (1 + (x - y).2 ^ 2) ^ (-(β / 2)) *
      ‖UnforcedLeray.Cyl.bsKernel c (x - y - x)‖ =
      (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖ := by
    intro y
    rw [show x - y - x = -y by abel, bsr_bsKernel_neg, norm_neg, Prod.snd_sub]
  simp_rw [e2]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))).1 hint.2

/-- **`BsrLiouville`**: `F(ζ) = w₁(ζ) - i w₂(ζ)` (with `ζ ↦ (Re ζ, Im ζ)`) is `ℝ`-differentiable
with `DF(ζ) i = i DF(ζ) 1` by `div w = curl w = 0`, hence entire; it is bounded, hence constant. -/
theorem bsrLiouville : BsrLiouville := by
  intro w hw hdiv hcurl hbdd x y
  obtain ⟨M, hM⟩ := hbdd
  let Φ : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ) -
      (EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).smulRight Complex.I
  have hΦ : ∀ v : UnforcedLeray.Cyl.Vec2,
      Φ v = ((v 0 : ℝ) : ℂ) - ((v 1 : ℝ) : ℂ) * Complex.I := by
    intro v
    simp [Φ, Complex.real_smul]
  let e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  let F : ℂ → ℂ := fun ζ => Φ (w (e ζ))
  have hFd : ∀ ζ : ℂ,
      HasFDerivAt F (Φ.comp ((fderiv ℝ w (e ζ)).comp (e : ℂ →L[ℝ] ℝ × ℝ))) ζ := by
    intro ζ
    exact Φ.hasFDerivAt.comp ζ ((hw (e ζ)).hasFDerivAt.comp ζ e.hasFDerivAt)
  have he1 : (e : ℂ →L[ℝ] ℝ × ℝ) 1 = ((1 : ℝ), (0 : ℝ)) := by simp [e]
  have heI : (e : ℂ →L[ℝ] ℝ × ℝ) Complex.I = ((0 : ℝ), (1 : ℝ)) := by simp [e]
  have hF : Differentiable ℂ F := by
    intro ζ
    refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨(hFd ζ).differentiableAt, ?_⟩
    rw [(hFd ζ).fderiv]
    obtain ⟨hq0, hη0⟩ := bsr_partial_comp (hw (e ζ)).hasFDerivAt 0
    obtain ⟨hq1, hη1⟩ := bsr_partial_comp (hw (e ζ)).hasFDerivAt 1
    have hd := hdiv (e ζ)
    have hc := hcurl (e ζ)
    unfold UnforcedLeray.Cyl.divergence at hd
    unfold UnforcedLeray.Cyl.curl at hc
    rw [hq0, hη1] at hd
    rw [hq1, hη0] at hc
    simp only [ContinuousLinearMap.comp_apply, he1, heI, hΦ]
    apply Complex.ext <;> simp <;> linarith
  have hb : Bornology.IsBounded (Set.range F) := by
    refine isBounded_iff_forall_norm_le.2 ⟨‖Φ‖ * M, ?_⟩
    rintro _ ⟨ζ, rfl⟩
    exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
  have hxy := hF.apply_eq_apply_of_bounded hb (e.symm x) (e.symm y)
  simp only [F, ContinuousLinearEquiv.apply_symm_apply, hΦ] at hxy
  have hre := congrArg Complex.re hxy
  have him := congrArg Complex.im hxy
  simp at hre him
  ext j
  fin_cases j
  · simpa using hre
  · simpa using him

/-- **`BsrKcFDerivEval` from `BsrWeightInt`**: the integrand `Dω(x - y) ⊗ K_c(y)` is dominated by
`A (1 + (x₂ - y₂)²)^{-β/2} ‖K_c(y)‖`, so the integral commutes with evaluation
(`ContinuousLinearMap.integral_apply`); `Dω(z)(1, 0) = ∂_qω(z)`, `Dω(z)(0, 1) = ∂_ηω(z)`, and
`Cyl.K_eq_reflect` for the periodic partials. -/
theorem bsrKcFDerivEval_of (hWI : BsrWeightInt) : BsrKcFDerivEval := by
  intro c β A hc hβ g hg1 hper hA' x
  have hc0 : 0 < c := by linarith
  have hgd : Differentiable ℝ g := hg1.differentiable one_ne_zero
  have hK : Measurable (UnforcedLeray.Cyl.bsKernel c) := UnforcedLeray.Cyl.measurable_bsKernel c
  have hL : Continuous (fun y : ℝ × ℝ => fderiv ℝ g (x - y)) :=
    (hg1.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
  have hint : Integrable (fun y : ℝ × ℝ =>
      (fderiv ℝ g (x - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    refine Integrable.mono' ((hWI c β hc hβ x.2).const_mul A) ?_ ?_
    · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) UnforcedLeray.Cyl.Vec2).continuous₂.comp_aestronglyMeasurable₂
        hL.aestronglyMeasurable hK.aestronglyMeasurable
    · refine Eventually.of_forall (fun y => ?_)
      rw [ContinuousLinearMap.norm_smulRight_apply]
      have hwpos : 0 < (1 + (x - y).2 ^ 2) ^ (β / 2) := Real.rpow_pos_of_pos (by positivity) _
      have hfy : ‖fderiv ℝ g (x - y)‖ ≤ A * (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) := by
        rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, ← Prod.snd_sub, le_div_iff₀ hwpos,
          mul_comm]
        exact hA' (x - y)
      calc ‖fderiv ℝ g (x - y)‖ * ‖UnforcedLeray.Cyl.bsKernel c y‖
          ≤ (A * (1 + (x.2 - y.2) ^ 2) ^ (-(β / 2))) * ‖UnforcedLeray.Cyl.bsKernel c y‖ :=
            mul_le_mul_of_nonneg_right hfy (norm_nonneg _)
        _ = A * ((1 + (x.2 - y.2) ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖) := by
            ring
  have hQ := UnforcedLeray.Cyl.IsPeriodic.partialQ hper
  have hE := UnforcedLeray.Cyl.IsPeriodic.partialEta hper
  constructor
  · rw [ContinuousLinearMap.integral_apply hint, UnforcedLeray.Cyl.K_eq_reflect hc0 hQ x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ((fderiv ℝ g (x - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y)) ((1 : ℝ), (0 : ℝ)) =
      UnforcedLeray.Cyl.partialQ g (x - y) • UnforcedLeray.Cyl.bsKernel c y
    rw [ContinuousLinearMap.smulRight_apply, UnforcedLeray.Cyl.partialQ_eq_fderiv hgd]
  · rw [ContinuousLinearMap.integral_apply hint, UnforcedLeray.Cyl.K_eq_reflect hc0 hE x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ((fderiv ℝ g (x - y)).smulRight (UnforcedLeray.Cyl.bsKernel c y)) ((0 : ℝ), (1 : ℝ)) =
      UnforcedLeray.Cyl.partialEta g (x - y) • UnforcedLeray.Cyl.bsKernel c y
    rw [ContinuousLinearMap.smulRight_apply, UnforcedLeray.Cyl.partialEta_eq_fderiv hgd]

/-! ## The composition -/

/-- **`TjTrainBSRep m` from the remaining leaves** (`BsrWeightInt`, `BsrKcHasFDeriv`,
`BsrKerPointwiseDecay`) and the train leaves. -/
theorem tjTrainBSRep_of_rest (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hDec : TjVortDecay m)
    (hG : TjLadGrad m) (hKb : TjKcBound) (hWI : BsrWeightInt) (hD : BsrKcHasFDeriv)
    (hP : BsrKerPointwiseDecay) : TjTrainBSRep m :=
  tjTrainBSRep_of_leaves m hm hV hDec hG hKb bsrFDerivNorm (bsrWeightIntShift_of hWI) hD
    (bsrKcFDerivEval_of hWI) hP bsrLiouville bsrKcOdd

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.bsrFDerivNorm
#print axioms UnforcedLeray.Short.IIIa.bsrKcOdd
#print axioms UnforcedLeray.Short.IIIa.bsrWeightIntShift_of
#print axioms UnforcedLeray.Short.IIIa.bsrLiouville
#print axioms UnforcedLeray.Short.IIIa.bsrKcFDerivEval_of
#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep_of_rest
