import UnforcedLeray.Analysis.WeakDerivative
import UnforcedLeray.Analysis.SobolevGraph.H2Functions

/-!
# Step L10, helpers: `W^{2,∞}` multipliers of `H²`

Support for `Loc/L10Nonlinear.lean` (step L10 `NonlinearStep`, `paper/main.tex` lines 462–491,
blueprint units B0721, B0722). Lines 504–505 bound `𝓒(K_loc,·)` by "multiplication by
`W^{2,∞}` fields"; this file proves that multiplication on the compiled weak-derivative graph
`SobolevGraph.H2`, for a pointwise bilinear coupling `B(K(x), f(x))`:

* `hasWeak_smul_left`: Leibniz for a smooth scalar multiplier, `∂ᵢ(a f) = a ∂ᵢf + (∂ᵢa) f`;
* `hasWeak_clm`: constant operators commute with weak derivatives;
* `hasWeak_bilin`: `∂ᵢ B(K, f) = B(K, ∂ᵢf) + B(∂ᵢK, f)` for a smooth field `K`;
* `exists_H2_bilin`: if `|K|, |DK|, |D²K| ≤ M` then `B(K, F) ∈ H²` with
  `‖B(K, F)‖_{H²} ≤ 13 ‖B‖ M ‖F‖_{H²}`.

No decay of `K` is used: the multiplier is only bounded with two bounded derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L10

open SobolevGraph

/-! ## Coordinate derivatives of a smooth vector field -/

/-- `∂ᵢK`, the coordinate derivative of a vector field (the body of `Blueprint.testPartial`). -/
def dpart (K : Space → Space) (i : Fin 3) : Space → Space :=
  fun y => fderiv ℝ K y (coordinateVector i)

theorem contDiff_dpart {K : Space → Space} (hK : ContDiff ℝ ∞ K) (i : Fin 3) :
    ContDiff ℝ ∞ (dpart K i) :=
  (ContDiff.fderiv_right (m := ∞) hK (by simp)).clm_apply contDiff_const

theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector, EuclideanSpace.norm_single]

theorem norm_dpart_le (K : Space → Space) (i : Fin 3) (y : Space) :
    ‖dpart K i y‖ ≤ ‖fderiv ℝ K y‖ := by
  have h := (fderiv ℝ K y).le_opNorm (coordinateVector i)
  rw [norm_coordinateVector, mul_one] at h
  exact h

theorem dpart_dpart_eq {K : Space → Space} (hK : ContDiff ℝ ∞ K) (i k : Fin 3) (y : Space) :
    dpart (dpart K i) k y =
      fderiv ℝ (fderiv ℝ K) y (coordinateVector k) (coordinateVector i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ K) y :=
    ((ContDiff.fderiv_right (m := ∞) hK (by simp)).differentiable (by simp)) y
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector i) y)
  unfold dpart
  rw [h.fderiv]
  simp

theorem norm_dpart_dpart_le {K : Space → Space} (hK : ContDiff ℝ ∞ K) (i k : Fin 3)
    (y : Space) : ‖dpart (dpart K i) k y‖ ≤ ‖iteratedFDeriv ℝ 2 K y‖ := by
  have e : ‖fderiv ℝ (fderiv ℝ K) y‖ = ‖iteratedFDeriv ℝ 2 K y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [dpart_dpart_eq hK, ← e]
  calc ‖fderiv ℝ (fderiv ℝ K) y (coordinateVector k) (coordinateVector i)‖
      ≤ ‖fderiv ℝ (fderiv ℝ K) y (coordinateVector k)‖ * ‖coordinateVector i‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ K) y‖ * ‖coordinateVector k‖ * ‖coordinateVector i‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fderiv ℝ K) y‖ := by
        rw [norm_coordinateVector, norm_coordinateVector, mul_one, mul_one]

/-- The derivative of a component is the component of the derivative. -/
theorem spatialTestDerivative_component {K : Space → Space} (hK : ContDiff ℝ ∞ K)
    (m i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => K y m) x = dpart K i x m := by
  have hd : HasFDerivAt K (fderiv ℝ K x) x := ((hK.differentiable (by simp)) x).hasFDerivAt
  have hc := (EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp x hd
  unfold spatialTestDerivative dpart
  rw [show (fun y => K y m) = (EuclideanSpace.proj m : Space →L[ℝ] ℝ) ∘ K from rfl, hc.fderiv]
  rfl

/-! ## Leibniz rules for weak derivatives -/

theorem spatialTestDerivative_mul {φ a : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ContDiff ℝ ∞ a) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => φ y * a y) x =
      spatialTestDerivative i φ x * a x + φ x * spatialTestDerivative i a x := by
  have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
  have had : DifferentiableAt ℝ a x := (ha.differentiable (by simp)) x
  unfold spatialTestDerivative
  rw [show (fun y => φ y * a y) = φ * a from rfl, (hφd.hasFDerivAt.mul had.hasFDerivAt).fderiv]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- **Leibniz, scalar multiplier.** `∂ᵢ(a f) = a ∂ᵢf + (∂ᵢa) f` weakly, for a smooth `a`. -/
theorem hasWeak_smul_left {i : Fin 3} {f g : SpatialField} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (h : HasWeakSpatialDerivative i f g)
    {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) :
    HasWeakSpatialDerivative i (fun x => a x • f x)
      (fun x => a x • g x + spatialTestDerivative i a x • f x) := by
  have hda : Continuous (spatialTestDerivative i a) :=
    ((ContDiff.fderiv_right (m := ∞) ha (by simp)).clm_apply contDiff_const).continuous
  have int1 : ∀ φ, IsSpatialTest φ →
      Integrable (fun x => (spatialTestDerivative i φ x * a x) • f x) :=
    fun φ hφ => hf.integrable_smul_left_of_hasCompactSupport
      ((hφ.derivative i).continuous.mul ha.continuous) (hφ.derivative i).compact.mul_right
  have int2 : ∀ φ, IsSpatialTest φ →
      Integrable (fun x => (φ x * spatialTestDerivative i a x) • f x) :=
    fun φ hφ => hf.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous.mul hda) hφ.compact.mul_right
  have int3 : ∀ φ, IsSpatialTest φ → Integrable (fun x => (φ x * a x) • g x) :=
    fun φ hφ => hg.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous.mul ha.continuous) hφ.compact.mul_right
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · simpa only [smul_smul] using int1 φ hφ
  · simpa only [smul_add, smul_smul] using (int3 φ hφ).fun_add (int2 φ hφ)
  · show (∫ x, spatialTestDerivative i φ x • (a x • f x)) =
      -(∫ x, φ x • (a x • g x + spatialTestDerivative i a x • f x))
    have hψ : IsSpatialTest (fun y => φ y * a y) := ⟨hφ.smooth.mul ha, hφ.compact.mul_right⟩
    have key := h.identity _ hψ
    have hsplit : ∀ x, spatialTestDerivative i (fun y => φ y * a y) x • f x =
        (spatialTestDerivative i φ x * a x) • f x + (φ x * spatialTestDerivative i a x) • f x := by
      intro x
      rw [spatialTestDerivative_mul hφ.smooth ha, add_smul]
    simp_rw [hsplit] at key
    rw [integral_add (int1 φ hφ) (int2 φ hφ)] at key
    have e1 : (fun x => spatialTestDerivative i φ x • (a x • f x)) =
        fun x => (spatialTestDerivative i φ x * a x) • f x := by
      funext x
      rw [smul_smul]
    have e2 : (fun x => φ x • (a x • g x + spatialTestDerivative i a x • f x)) =
        fun x => (φ x * a x) • g x + (φ x * spatialTestDerivative i a x) • f x := by
      funext x
      rw [smul_add, smul_smul, smul_smul]
    rw [e1, e2, integral_add (int3 φ hφ) (int2 φ hφ), neg_add', ← key, add_sub_cancel_right]

/-- Constant operators commute with weak derivatives. -/
theorem hasWeak_clm {i : Fin 3} {f g : SpatialField} (h : HasWeakSpatialDerivative i f g)
    (E : Space →L[ℝ] Space) :
    HasWeakSpatialDerivative i (fun x => E (f x)) (fun x => E (g x)) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · show Integrable (fun x => spatialTestDerivative i φ x • E (f x))
    have e : (fun x => spatialTestDerivative i φ x • E (f x)) =
        fun x => E (spatialTestDerivative i φ x • f x) :=
      funext fun x => (map_smul E _ _).symm
    rw [e]
    exact E.integrable_comp (h.left_integrable φ hφ)
  · show Integrable (fun x => φ x • E (g x))
    have e : (fun x => φ x • E (g x)) = fun x => E (φ x • g x) :=
      funext fun x => (map_smul E _ _).symm
    rw [e]
    exact E.integrable_comp (h.right_integrable φ hφ)
  · show (∫ x, spatialTestDerivative i φ x • E (f x)) = -(∫ x, φ x • E (g x))
    have e1 : (fun x => spatialTestDerivative i φ x • E (f x)) =
        fun x => E (spatialTestDerivative i φ x • f x) :=
      funext fun x => (map_smul E _ _).symm
    have e2 : (fun x => φ x • E (g x)) = fun x => E (φ x • g x) :=
      funext fun x => (map_smul E _ _).symm
    rw [e1, e2, E.integral_comp_comm (h.left_integrable φ hφ),
      E.integral_comp_comm (h.right_integrable φ hφ), h.identity φ hφ, map_neg]

theorem sum_single_coord (v : Space) :
    ∑ m : Fin 3, v m • EuclideanSpace.single m (1 : ℝ) = v := by
  ext i
  simp [Pi.single_apply]

/-- A bilinear coupling in coordinates of its first argument. -/
theorem bilin_expand (B : Space →L[ℝ] Space →L[ℝ] Space) (u v : Space) :
    B u v = u 0 • B (EuclideanSpace.single 0 1) v + u 1 • B (EuclideanSpace.single 1 1) v +
      u 2 • B (EuclideanSpace.single 2 1) v := by
  conv_lhs => rw [← sum_single_coord u]
  rw [map_sum, ContinuousLinearMap.sum_apply, Fin.sum_univ_three]
  simp only [map_smul, ContinuousLinearMap.smul_apply]

/-- **Leibniz, bilinear coupling.** `∂ᵢ B(K, f) = B(K, ∂ᵢf) + B(∂ᵢK, f)` weakly, for a smooth
vector field `K` and `L²` fields `f`, `∂ᵢf`. -/
theorem hasWeak_bilin {i : Fin 3} {f g : SpatialField} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h : HasWeakSpatialDerivative i f g)
    (B : Space →L[ℝ] Space →L[ℝ] Space) {K : Space → Space} (hK : ContDiff ℝ ∞ K) :
    HasWeakSpatialDerivative i (fun x => B (K x) (f x))
      (fun x => B (K x) (g x) + B (dpart K i x) (f x)) := by
  have term : ∀ m : Fin 3, HasWeakSpatialDerivative i
      (fun x => K x m • B (EuclideanSpace.single m 1) (f x))
      (fun x => K x m • B (EuclideanSpace.single m 1) (g x) +
        dpart K i x m • B (EuclideanSpace.single m 1) (f x)) := by
    intro m
    have hE := hasWeak_clm h (B (EuclideanSpace.single m 1))
    have hEf : LocallyIntegrable (fun x => B (EuclideanSpace.single m 1) (f x)) volume :=
      ((B (EuclideanSpace.single m 1)).comp_memLp' hf).locallyIntegrable (by norm_num)
    have hEg : LocallyIntegrable (fun x => B (EuclideanSpace.single m 1) (g x)) volume :=
      ((B (EuclideanSpace.single m 1)).comp_memLp' hg).locallyIntegrable (by norm_num)
    have ham : ContDiff ℝ ∞ (fun x => K x m) :=
      (EuclideanSpace.proj m : Space →L[ℝ] ℝ).contDiff.comp hK
    refine (hasWeak_smul_left hEf hEg hE ham).congr (Eventually.of_forall fun x => rfl)
      (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [spatialTestDerivative_component hK m i x]
  have hsum := ((term 0).add (term 1)).add (term 2)
  refine hsum.congr (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simp only [Pi.add_apply]
    rw [bilin_expand B (K x) (f x)]
  · simp only [Pi.add_apply]
    rw [bilin_expand B (K x) (g x), bilin_expand B (dpart K i x) (f x)]
    abel

/-! ## `L²` bounds for the coupling -/

theorem norm_bilin_le (B : Space →L[ℝ] Space →L[ℝ] Space) {K : Space → Space} {M : ℝ}
    (hb : ∀ x, ‖K x‖ ≤ M) (x v : Space) : ‖B (K x) v‖ ≤ ‖B‖ * M * ‖v‖ := by
  calc ‖B (K x) v‖ ≤ ‖B‖ * ‖K x‖ * ‖v‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * M * ‖v‖ := by gcongr; exact hb x

theorem memLp_bilin (B : Space →L[ℝ] Space →L[ℝ] Space) {K : Space → Space}
    (hK : Continuous K) {M : ℝ} (hb : ∀ x, ‖K x‖ ≤ M) {f : SpatialField}
    (hf : MemLp f 2 volume) : MemLp (fun x => B (K x) (f x)) 2 volume :=
  hf.of_le_mul (B.aestronglyMeasurable_comp₂ hK.aestronglyMeasurable hf.1)
    (Eventually.of_forall fun x => norm_bilin_le B hb x (f x))

theorem l2Norm_nonneg' (f : SpatialField) : 0 ≤ l2Norm f := ENNReal.toReal_nonneg

theorem l2Norm_bilin_le (B : Space →L[ℝ] Space →L[ℝ] Space) {K : Space → Space}
    {M : ℝ} (hb : ∀ x, ‖K x‖ ≤ M) {f : SpatialField} (hf : MemLp f 2 volume) :
    l2Norm (fun x => B (K x) (f x)) ≤ ‖B‖ * M * l2Norm f := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0)
  have hc : 0 ≤ ‖B‖ * M := mul_nonneg (norm_nonneg B) hM
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
    (Eventually.of_forall fun x => norm_bilin_le B hb x (f x)) (2 : ℝ≥0∞)
  have hfin : ENNReal.ofReal (‖B‖ * M) * eLpNorm f 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  unfold l2Norm
  calc (eLpNorm (fun x => B (K x) (f x)) 2 volume).toReal
      ≤ (ENNReal.ofReal (‖B‖ * M) * eLpNorm f 2 volume).toReal := ENNReal.toReal_mono hfin h
    _ = ‖B‖ * M * (eLpNorm f 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

theorem l2Norm_add_le' {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2Norm (fun x => f x + g x) ≤ l2Norm f + l2Norm g := by
  show (eLpNorm (f + g) 2 volume).toReal ≤
    (eLpNorm f 2 volume).toReal + (eLpNorm g 2 volume).toReal
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num))

theorem l2Norm_add_le_of {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    {a b : ℝ} (ha : l2Norm f ≤ a) (hb : l2Norm g ≤ b) :
    l2Norm (fun x => f x + g x) ≤ a + b :=
  (l2Norm_add_le' hf hg).trans (add_le_add ha hb)

theorem l2Norm_Lp (F : L2Space) : l2Norm (F : SpatialField) = ‖F‖ := by
  unfold l2Norm
  rw [Lp.norm_def]

/-! ## Components of the `H²` norm -/

theorem H2.norm_value_le' (F : H2) : ‖F.value‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [H2.norm_sq F]
  have h1 : 0 ≤ ∑ i : Fin 3, ‖F.first i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖F.second i j‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

theorem H2.norm_first_le (F : H2) (i : Fin 3) : ‖F.first i‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [H2.norm_sq F]
  have h1 : ‖F.first i‖ ^ 2 ≤ ∑ j : Fin 3, ‖F.first j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖F.first j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖F.second i j‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith [sq_nonneg ‖F.value‖]

theorem H2.norm_second_le (F : H2) (i k : Fin 3) : ‖F.second i k‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [H2.norm_sq F]
  have h1 : ‖F.second i k‖ ^ 2 ≤ ∑ j : Fin 3, ‖F.second i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖F.second i j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ k)
  have h2 : ∑ j : Fin 3, ‖F.second i j‖ ^ 2 ≤ ∑ l : Fin 3, ∑ j : Fin 3, ‖F.second l j‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ∑ j : Fin 3, ‖F.second l j‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i : Fin 3, ‖F.first i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg ‖F.value‖]

/-! ## `W^{2,∞}` multipliers of `H²` -/

/-- **`W^{2,∞}` multipliers (lines 504–505).** If `K` is smooth with `|K|, |DK|, |D²K| ≤ M`,
then for every `F ∈ H²` the field `x ↦ B(K(x), F(x))` is in `H²`, with
`‖B(K, F)‖_{H²} ≤ 13 ‖B‖ M ‖F‖_{H²}`. -/
theorem exists_H2_bilin (B : Space →L[ℝ] Space →L[ℝ] Space) {K : Space → Space}
    (hK : ContDiff ℝ ∞ K) {M : ℝ}
    (hb : ∀ y, ‖K y‖ ≤ M ∧ ‖fderiv ℝ K y‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 K y‖ ≤ M) (F : H2) :
    ∃ P : H2, (P.value : SpatialField) =ᵐ[volume]
        (fun x => B (K x) ((F.value : SpatialField) x)) ∧
      ‖P‖ ≤ 13 * (‖B‖ * M * ‖F‖) := by
  have hFv : MemLp (F.value : SpatialField) 2 volume := Lp.memLp _
  have hF1 : ∀ i, MemLp (F.first i : SpatialField) 2 volume := fun i => Lp.memLp _
  have hF2 : ∀ i k, MemLp (F.second i k : SpatialField) 2 volume := fun i k => Lp.memLp _
  have hK0 : ∀ y, ‖K y‖ ≤ M := fun y => (hb y).1
  have hK1 : ∀ i y, ‖dpart K i y‖ ≤ M := fun i y => (norm_dpart_le K i y).trans (hb y).2.1
  have hK2 : ∀ i k y, ‖dpart (dpart K i) k y‖ ≤ M :=
    fun i k y => (norm_dpart_dpart_le hK i k y).trans (hb y).2.2
  have hM : 0 ≤ M := (norm_nonneg _).trans (hK0 0)
  have hc0 : Continuous K := hK.continuous
  have hc1 : ∀ i, Continuous (dpart K i) := fun i => (contDiff_dpart hK i).continuous
  have hc2 : ∀ i k, Continuous (dpart (dpart K i) k) :=
    fun i k => (contDiff_dpart (contDiff_dpart hK i) k).continuous
  let c : SpatialField := fun x => B (K x) ((F.value : SpatialField) x)
  let c1 : Fin 3 → SpatialField := fun i x =>
    B (K x) ((F.first i : SpatialField) x) + B (dpart K i x) ((F.value : SpatialField) x)
  let c2 : Fin 3 → Fin 3 → SpatialField := fun i k x =>
    (B (K x) ((F.second i k : SpatialField) x) + B (dpart K k x) ((F.first i : SpatialField) x)) +
      (B (dpart K i x) ((F.first k : SpatialField) x) +
        B (dpart (dpart K i) k x) ((F.value : SpatialField) x))
  have hc : MemLp c 2 volume := memLp_bilin B hc0 hK0 hFv
  have hc1m : ∀ i, MemLp (c1 i) 2 volume := fun i =>
    (memLp_bilin B hc0 hK0 (hF1 i)).add (memLp_bilin B (hc1 i) (hK1 i) hFv)
  have hc2m : ∀ i k, MemLp (c2 i k) 2 volume := fun i k =>
    ((memLp_bilin B hc0 hK0 (hF2 i k)).add (memLp_bilin B (hc1 k) (hK1 k) (hF1 i))).add
      ((memLp_bilin B (hc1 i) (hK1 i) (hF1 k)).add (memLp_bilin B (hc2 i k) (hK2 i k) hFv))
  have hd1 : ∀ i, HasWeakSpatialDerivative i c (c1 i) := fun i =>
    hasWeak_bilin hFv (hF1 i) (F.hasWeakFirst i) B hK
  have hd2 : ∀ i k, HasWeakSpatialDerivative k (c1 i) (c2 i k) := fun i k =>
    (hasWeak_bilin (hF1 i) (hF2 i k) (F.hasWeakSecond i k) B hK).add
      (hasWeak_bilin hFv (hF1 k) (F.hasWeakFirst k) B (contDiff_dpart hK i))
  refine ⟨H2.ofFields c c1 c2 hc hc1m hc2m hd1 hd2, coeFn_toL2 hc, ?_⟩
  have hP := H2.norm_sq_ofFields c c1 c2 hc hc1m hc2m hd1 hd2
  set b := ‖B‖ * M * ‖F‖ with hb_def
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg (norm_nonneg B) hM) (norm_nonneg _)
  have hl : ∀ (K' : Space → Space), (∀ y, ‖K' y‖ ≤ M) → ∀ G : L2Space, ‖G‖ ≤ ‖F‖ →
      l2Norm (fun x => B (K' x) ((G : SpatialField) x)) ≤ b := by
    intro K' hb' G hG
    calc l2Norm (fun x => B (K' x) ((G : SpatialField) x))
        ≤ ‖B‖ * M * l2Norm (G : SpatialField) := l2Norm_bilin_le B hb' (Lp.memLp G)
      _ = ‖B‖ * M * ‖G‖ := by rw [l2Norm_Lp]
      _ ≤ b := by
          rw [hb_def]
          exact mul_le_mul_of_nonneg_left hG (mul_nonneg (norm_nonneg B) hM)
  have b0 : l2Norm c ≤ b := hl K hK0 F.value (H2.norm_value_le' F)
  have b1 : ∀ i, l2Norm (c1 i) ≤ 2 * b := by
    intro i
    exact (l2Norm_add_le_of (memLp_bilin B hc0 hK0 (hF1 i)) (memLp_bilin B (hc1 i) (hK1 i) hFv)
      (hl K hK0 (F.first i) (H2.norm_first_le F i))
      (hl (dpart K i) (hK1 i) F.value (H2.norm_value_le' F))).trans (by linarith)
  have b2 : ∀ i k, l2Norm (c2 i k) ≤ 4 * b := by
    intro i k
    have hA := l2Norm_add_le_of (memLp_bilin B hc0 hK0 (hF2 i k))
      (memLp_bilin B (hc1 k) (hK1 k) (hF1 i))
      (hl K hK0 (F.second i k) (H2.norm_second_le F i k))
      (hl (dpart K k) (hK1 k) (F.first i) (H2.norm_first_le F i))
    have hB := l2Norm_add_le_of (memLp_bilin B (hc1 i) (hK1 i) (hF1 k))
      (memLp_bilin B (hc2 i k) (hK2 i k) hFv)
      (hl (dpart K i) (hK1 i) (F.first k) (H2.norm_first_le F k))
      (hl (dpart (dpart K i) k) (hK2 i k) F.value (H2.norm_value_le' F))
    exact (l2Norm_add_le_of
      ((memLp_bilin B hc0 hK0 (hF2 i k)).add (memLp_bilin B (hc1 k) (hK1 k) (hF1 i)))
      ((memLp_bilin B (hc1 i) (hK1 i) (hF1 k)).add (memLp_bilin B (hc2 i k) (hK2 i k) hFv))
      hA hB).trans (by linarith)
  have s0 : l2Norm c ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (l2Norm_nonneg' _) b0 2
  have s1 : ∑ i : Fin 3, l2Norm (c1 i) ^ 2 ≤ ∑ _i : Fin 3, (2 * b) ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (l2Norm_nonneg' _) (b1 i) 2
  have s2 : ∑ i : Fin 3, ∑ k : Fin 3, l2Norm (c2 i k) ^ 2 ≤
      ∑ _i : Fin 3, ∑ _k : Fin 3, (4 * b) ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
      pow_le_pow_left₀ (l2Norm_nonneg' _) (b2 i k) 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at s1 s2
  have hsq : ‖H2.ofFields c c1 c2 hc hc1m hc2m hd1 hd2‖ ^ 2 ≤ (13 * b) ^ 2 := by
    rw [hP]
    nlinarith [sq_nonneg b]
  exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp hsq

end UnforcedLeray.Blueprint.L10
