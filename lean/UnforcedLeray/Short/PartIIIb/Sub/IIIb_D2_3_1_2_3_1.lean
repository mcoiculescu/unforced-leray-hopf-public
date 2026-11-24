import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailZero
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Decomposition of `kernelEquivariance` (`PartIII-b:IIIb-D2/3/1/2/3/1`)

Source of record: `the November 2 reference manuscript`
lines 3600-3610 (`K_t = δG_t + ∂∂∫_t^∞ G`, radial dependence).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section Orth

variable {M : Matrix (Fin 3) (Fin 3) ℝ}

lemma mul_transpose_comm (hM : M * M.transpose = 1) : M.transpose * M = 1 :=
  mul_eq_one_comm.1 hM

lemma actM_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Space) (i : Fin 3) :
    actM M x i = ∑ a : Fin 3, M i a * x a := by
  simp [actM, Matrix.mulVec, dotProduct]

lemma actM_actM (hM : M * M.transpose = 1) (x : Space) :
    actM M.transpose (actM M x) = x := by
  ext i
  simp only [actM, Matrix.mulVec_mulVec, mul_transpose_comm hM, Matrix.one_mulVec]

lemma actM_actM' (hM : M * M.transpose = 1) (x : Space) :
    actM M (actM M.transpose x) = x := by
  ext i
  simp only [actM, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

lemma norm_actM (hM : M * M.transpose = 1) (x : Space) : ‖actM M x‖ = ‖x‖ := by
  have h : ‖actM M x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have := congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ => (WithLp.ofLp x) ⬝ᵥ (N.mulVec (WithLp.ofLp x)))
      (mul_transpose_comm hM)
    simp only [Matrix.one_mulVec] at this
    have e : (M.mulVec (WithLp.ofLp x)) ⬝ᵥ (M.mulVec (WithLp.ofLp x)) =
        (WithLp.ofLp x) ⬝ᵥ ((M.transpose * M).mulVec (WithLp.ofLp x)) := by
      rw [← Matrix.mulVec_mulVec]
      conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 := e.trans this
    simpa [actM, dotProduct, sq] using e2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The continuous linear map of `M`. -/
def clmOf (M : Matrix (Fin 3) (Fin 3) ℝ) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma clmOf_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Space) : clmOf M x = actM M x := by
  rfl

/-- The continuous linear equivalence of an orthogonal `M`. -/
def cleOf (hM : M * M.transpose = 1) : Space ≃L[ℝ] Space :=
  ContinuousLinearEquiv.equivOfInverse (clmOf M) (clmOf M.transpose)
    (fun x => by simp only [clmOf_apply, actM_actM hM])
    (fun x => by simp only [clmOf_apply, actM_actM' hM])

lemma cleOf_apply (hM : M * M.transpose = 1) (x : Space) : cleOf hM x = actM M x :=
  clmOf_apply M x

/-- A function invariant under `actM M` has `fderiv f (Mx) ∘ M = fderiv f x`, with no regularity. -/
lemma fderiv_actM (hM : M * M.transpose = 1) {f : Space → ℝ} (hf : ∀ y, f (actM M y) = f y)
    (y v : Space) : fderiv ℝ f (actM M y) (actM M v) = fderiv ℝ f y v := by
  have h1 : (f ∘ (cleOf hM)) = f := by
    funext z; simp only [Function.comp, cleOf_apply, hf]
  have h2 := (cleOf hM).comp_right_fderiv (f := f) (x := y)
  rw [h1] at h2
  have h3 := congrArg (fun L : Space →L[ℝ] ℝ => L v) h2
  simp only [ContinuousLinearMap.comp_apply] at h3
  simpa [cleOf_apply] using h3.symm

lemma actM_transpose_coord (j : Fin 3) :
    actM M.transpose (coordinateVector j) = ∑ b : Fin 3, M j b • coordinateVector b := by
  ext i
  simp [actM_apply, coordinateVector, Pi.single_apply, Matrix.transpose_apply, WithLp.ofLp_sum]

/-- The first partials of an `actM M`-invariant function transform by `M`. -/
lemma partial_actM (hM : M * M.transpose = 1) {f : Space → ℝ} (hf : ∀ y, f (actM M y) = f y)
    (j : Fin 3) (y : Space) :
    fderiv ℝ f (actM M y) (coordinateVector j) =
      ∑ b : Fin 3, M j b * fderiv ℝ f y (coordinateVector b) := by
  have h := fderiv_actM hM hf y (actM M.transpose (coordinateVector j))
  rw [actM_actM' hM, actM_transpose_coord] at h
  rw [h]
  simp [map_sum]

/-- **Hessian transformation** for an `actM M`-invariant function that is `C²` at `x` and at `Mx`. -/
theorem part2_actM (hM : M * M.transpose = 1) {f : Space → ℝ} (hf : ∀ y, f (actM M y) = f y)
    {x : Space} (hx : ContDiffAt ℝ 2 f x) (hAx : ContDiffAt ℝ 2 f (actM M x)) (i j : Fin 3) :
    IIIa.part2 f i j (actM M x) =
      ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b * IIIa.part2 f a b x := by
  have hd : ∀ z, ContDiffAt ℝ 2 f z → ∀ b : Fin 3,
      DifferentiableAt ℝ (fun y => fderiv ℝ f y (coordinateVector b)) z := by
    intro z hz b
    have : DifferentiableAt ℝ (fderiv ℝ f) z :=
      (hz.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero
    exact this.clm_apply (differentiableAt_const _)
  set h : Fin 3 → Space → ℝ := fun b y => fderiv ℝ f y (coordinateVector b) with hh
  have hfun : (h j ∘ clmOf M) = fun y => ∑ b : Fin 3, M j b * h b y := by
    funext y
    simp only [Function.comp, clmOf_apply, hh]
    exact partial_actM hM hf j y
  have hA : HasFDerivAt (h j ∘ clmOf M) ((fderiv ℝ (h j) (actM M x)).comp (clmOf M)) x := by
    have h1 : HasFDerivAt (h j) (fderiv ℝ (h j) (actM M x)) (clmOf M x) := by
      rw [clmOf_apply]; exact (hd _ hAx j).hasFDerivAt
    exact h1.comp x (clmOf M).hasFDerivAt
  have hB : HasFDerivAt (fun y => ∑ b : Fin 3, M j b * h b y)
      (∑ b : Fin 3, M j b • fderiv ℝ (h b) x) x := by
    exact HasFDerivAt.fun_sum (u := Finset.univ)
      (fun b _ => ((hd _ hx b).hasFDerivAt).const_mul (M j b))
  rw [hfun] at hA
  have hU := hA.unique hB
  have hv := congrArg (fun L : Space →L[ℝ] ℝ => L (actM M.transpose (coordinateVector i))) hU
  simp only [ContinuousLinearMap.comp_apply, clmOf_apply] at hv
  rw [actM_actM' hM] at hv
  simp only [actM_transpose_coord, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply] at hv
  unfold IIIa.part2
  show fderiv ℝ (h j) (actM M x) (coordinateVector i) = _
  rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  show M j b * (M i a * fderiv ℝ (h b) x (coordinateVector a)) = _
  ring

end Orth

section Newton

lemma norm_cv (j : Fin 3) : ‖coordinateVector j‖ = 1 := by simp [coordinateVector]

/-- The Newtonian potential has no second partials at the origin in the sense of `fderiv`: the
first partials are unbounded near `0`, hence not differentiable at `0`. -/
theorem part2_newton_zero {f : Space → ℝ} (hf : ∀ y, y ≠ 0 → f y = (4 * Real.pi * ‖y‖)⁻¹)
    (i j : Fin 3) : IIIa.part2 f i j 0 = 0 := by
  have hpi : 0 < 4 * Real.pi := by positivity
  have hnd : ¬ DifferentiableAt ℝ (fun y => fderiv ℝ f y (coordinateVector j)) 0 := by
    intro hd
    have hc := hd.continuousAt
    set g : ℝ → Space := fun r => r • coordinateVector j with hg
    have hgc : Continuous g := by fun_prop
    have hg0 : g 0 = 0 := by simp [hg]
    have h1 : Tendsto (fun r => fderiv ℝ f (g r) (coordinateVector j)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ f 0 (coordinateVector j))) := by
      have hg' : Tendsto g (𝓝 0) (𝓝 0) := by simpa [hg0] using hgc.tendsto 0
      exact hc.tendsto.comp (hg'.mono_left nhdsWithin_le_nhds)
    have hval : ∀ r : ℝ, 0 < r → fderiv ℝ f (g r) (coordinateVector j) =
        -(1 / (4 * Real.pi)) * (r⁻¹) ^ 2 := by
      intro r hr
      have hgr : ‖g r‖ = r := by
        simp [hg, norm_smul, norm_cv, abs_of_pos hr]
      have hne : g r ≠ 0 := by
        intro h0; rw [h0] at hgr; simp at hgr; linarith
      have hev : f =ᶠ[𝓝 (g r)] fun y => (4 * Real.pi * ‖y‖)⁻¹ := by
        filter_upwards [isOpen_ne.mem_nhds hne] with y hy using hf y hy
      have hdN : DifferentiableAt ℝ (fun y : Space => (4 * Real.pi * ‖y‖)⁻¹) (g r) := by
        have : DifferentiableAt ℝ (fun y : Space => ‖y‖) (g r) :=
          (differentiableAt_id).norm ℝ hne
        exact (this.const_mul _).inv (by rw [hgr]; positivity)
      have hdf : DifferentiableAt ℝ f (g r) := hdN.congr_of_eventuallyEq hev
      have hder : HasDerivAt (fun s : ℝ => f (g s)) (fderiv ℝ f (g r) (coordinateVector j)) r := by
        have hgd : HasDerivAt g (coordinateVector j) r := by
          simpa [hg] using (hasDerivAt_id r).smul_const (coordinateVector j)
        exact hdf.hasFDerivAt.comp_hasDerivAt r hgd
      have hlin : HasDerivAt (fun s : ℝ => (4 * Real.pi * s)⁻¹)
          (-(4 * Real.pi * 1) / (4 * Real.pi * r) ^ 2) r := by
        exact ((hasDerivAt_id' r).const_mul (4 * Real.pi)).inv (by positivity)
      have heq : (fun s : ℝ => f (g s)) =ᶠ[𝓝 r] fun s => (4 * Real.pi * s)⁻¹ := by
        filter_upwards [Ioi_mem_nhds hr] with s hs
        have hs' : (0 : ℝ) < s := hs
        have hn : ‖g s‖ = s := by
          simp [hg, norm_smul, norm_cv, abs_of_pos hs']
        have hne' : g s ≠ 0 := by
          intro h0; rw [h0] at hn; simp at hn; linarith
        rw [hf _ hne', hn]
      have := hder.unique (hlin.congr_of_eventuallyEq heq)
      rw [this]
      field_simp
    have h2 : Tendsto (fun r : ℝ => -(1 / (4 * Real.pi)) * (r⁻¹) ^ 2) (𝓝[>] 0) atBot := by
      have h3 : Tendsto (fun r : ℝ => (r⁻¹) ^ 2) (𝓝[>] 0) atTop :=
        (tendsto_pow_atTop (two_ne_zero)).comp tendsto_inv_nhdsGT_zero
      have hneg : -(1 / (4 * Real.pi)) < 0 := neg_neg_of_pos (by positivity)
      exact h3.const_mul_atTop_of_neg hneg
    have h4 : Tendsto (fun r => fderiv ℝ f (g r) (coordinateVector j)) (𝓝[>] 0) atBot := by
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr using (hval r hr).symm
    exact not_tendsto_nhds_of_tendsto_atBot h4 _ h1
  unfold IIIa.part2
  rw [fderiv_zero_of_not_differentiableAt hnd]
  simp

end Newton

section Heat

variable {M : Matrix (Fin 3) (Fin 3) ℝ}

lemma heatG_actM (hM : M * M.transpose = 1) (t : ℝ) (x : Space) :
    IIIa.heatG t (actM M x) = IIIa.heatG t x := by
  unfold IIIa.heatG; rw [norm_actM hM]

lemma heatTail_actM (hM : M * M.transpose = 1) (t : ℝ) (x : Space) :
    IIIa.heatTail t (actM M x) = IIIa.heatTail t x := by
  unfold IIIa.heatTail; simp only [heatG_actM hM]

/-- In Lean's `rpow` convention `G_a = 0` for `a ≤ 0`. -/
lemma heatG_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : Space) : IIIa.heatG t x = 0 := by
  unfold IIIa.heatG
  rcases ht.eq_or_lt with h | h
  · subst h
    rw [mul_zero, Real.zero_rpow (by norm_num)]; simp
  · have hn : 4 * Real.pi * t < 0 := mul_neg_of_pos_of_neg (by positivity) h
    rw [Real.rpow_def_of_neg hn]
    have : Real.cos (-3 / 2 * Real.pi) = 0 := by
      rw [show (-3 / 2 * Real.pi) = -(Real.pi / 2 + Real.pi) by ring, Real.cos_neg, Real.cos_add_pi]
      simp
    rw [this]; simp

lemma heatTail_of_nonpos {t : ℝ} (ht : t ≤ 0) (y : Space) :
    IIIa.heatTail t y = IIIa.heatTail 0 y := by
  unfold IIIa.heatTail
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (E := ℝ)
    (f := fun a => IIIa.heatG a y) measurableSet_Ioi (Ioi_subset_Ioi ht) (fun a ha => ?_))
  exact heatG_of_nonpos (not_lt.1 fun h => ha.2 h) y

lemma heatTail_nonpos_eq {t : ℝ} (ht : t ≤ 0) {y : Space} (hy : y ≠ 0) :
    IIIa.heatTail t y = (4 * Real.pi * ‖y‖)⁻¹ :=
  (heatTail_of_nonpos ht y).trans (IIIa.heatTailZero y hy)

lemma contDiffAt_heatTail_nonpos {t : ℝ} (ht : t ≤ 0) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (IIIa.heatTail t) y := by
  have hev : IIIa.heatTail t =ᶠ[𝓝 y] fun z => (4 * Real.pi * ‖z‖)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hy] with z hz using heatTail_nonpos_eq ht hz
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hn : ContDiffAt ℝ 2 (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy
  exact (contDiffAt_const.mul hn).inv (by positivity)

/-- **Source input** (regularity of the heat tail for positive time; 3604-3606: `∫_t^∞ G_a da`
is smooth, uniformly bounded derivatives `a^{-(3+m)/2}` integrable on `(t,∞)`): for `t > 0`,
`heatTail t` is `C²` at every point, including the origin. -/
def HeatTailC2Pos : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : Space, ContDiffAt ℝ 2 (IIIa.heatTail t) x

theorem kernelEquivariance_of (h : HeatTailC2Pos) : KernelEquivariance := by
  intro M hM t i j x
  have hdelta : ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b * (if a = b then IIIa.heatG t x else 0) =
      if i = j then IIIa.heatG t x else 0 := by
    have h1 := congrFun (congrFun hM i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_mul]
    rw [h1]
    split_ifs <;> simp
  have hpart : IIIa.part2 (IIIa.heatTail t) i j (actM M x) =
      ∑ a : Fin 3, ∑ b : Fin 3, M i a * M j b * IIIa.part2 (IIIa.heatTail t) a b x := by
    rcases lt_or_ge 0 t with ht | ht
    · exact part2_actM hM (heatTail_actM hM t) (h t ht x) (h t ht _) i j
    · by_cases hx : x = 0
      · subst hx
        have h0 : actM M 0 = 0 := by ext k; simp [actM]
        have hz : ∀ a b : Fin 3, IIIa.part2 (IIIa.heatTail t) a b 0 = 0 := fun a b =>
          part2_newton_zero (fun y hy => heatTail_nonpos_eq ht hy) a b
        simp [h0, hz]
      · have hAx : actM M x ≠ 0 := by
          intro h0
          apply hx
          have := norm_actM hM x
          rw [h0, norm_zero] at this
          exact norm_eq_zero.1 this.symm
        exact part2_actM hM (heatTail_actM hM t) (contDiffAt_heatTail_nonpos ht hx)
          (contDiffAt_heatTail_nonpos ht hAx) i j
  unfold IIIa.heatLerayK
  simp only [heatG_actM hM, mul_add, Finset.sum_add_distrib]
  rw [hdelta, hpart]

end Heat

end UnforcedLeray.Short.PartIIIb.Concrete
