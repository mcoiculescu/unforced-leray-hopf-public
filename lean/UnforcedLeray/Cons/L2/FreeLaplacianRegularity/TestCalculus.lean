import UnforcedLeray.Cons.L2.FreeLaplacianRegularity.ChangeOfVariables
import UnforcedLeray.Units.B0423

/-!
# C08-reg, part 2: tests transported by the similarity chart

`paper/main.tex` lines 7484–7500 (blueprint unit B0424): "Direct differentiation gives
`v_t - ν e^t Δ_x v = g`", and the cutoff form `(∂_θ - νΔ_x)u = θ^{-1}(χg + χ'v)`. In the weak
form this is a statement about tests: a heat test `φ(θ, x)` is transported to the similarity
test `ψ(t, y) = a(t) φ(e^t, e^{t/2} y) e_c` (`liftTest`), and

* `∂_t ψ = a' φ∘E + a (e^t ∂_θφ + ½ ∇_xφ · e^{t/2} y)∘E` (`timeDerivative_liftTest`),
* `(y·∇_y) ψ = a (∇_xφ · e^{t/2} y)∘E` (`spatialDerivative_liftTest`),
* `Δ_y ψ = a e^t (Δ_x φ)∘E` (`spatialLaplacian_liftTest`),

so that `𝒯₀ψ = ∂_tψ - ½ y·∇ψ` sees only `∂_θφ`: the drift `-½ y·∇` of the similarity
equation is absorbed by the chart. Conversely a similarity test `Ψ` gives the heat test
`φ_c(θ, x) = θ^{-1} Ψ_c(log θ, θ^{-1/2} x)` (`push`, `isSTTest_push`), smooth with compact
support because `Ψ` vanishes for `|t|` large.

Also: `Δ_y(b(t) T Ψ) = b(t) T Δ_y Ψ` for a function `b` of the phase and a linear map `T`
(`spatialLaplacian_smul_clm`).

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Cons.L2.FreeLapReg

open UnforcedLeray.Blueprint
open UnforcedLeray.Parabolic (IsSTTest tD sD sD2 sLap dirD sdir tdir ev)

/-! ## Coordinates -/

theorem inner_coordinateVector (x : Space) (c : Fin 3) :
    inner ℝ x (coordinateVector c) = x c := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

theorem inner_smul_coordinateVector (x : Space) (r : ℝ) (c : Fin 3) :
    inner ℝ x (r • coordinateVector c) = r * x c := by
  rw [real_inner_smul_right, inner_coordinateVector]

theorem coordinateVector_apply_self (r : ℝ) (c : Fin 3) : (r • coordinateVector c) c = r := by
  simp [coordinateVector]

/-! ## Smoothness of the chart -/

theorem contDiff_simE : ContDiff ℝ ∞ simE :=
  (Real.contDiff_exp.comp contDiff_fst).prodMk
    ((Real.contDiff_exp.comp (contDiff_fst.div_const 2)).smul contDiff_snd)

theorem contDiffAt_simG {X : SpaceTime} (hX : 0 < X.1) : ContDiffAt ℝ ∞ simG X := by
  have hlog : ContDiffAt ℝ ∞ (fun X : SpaceTime => Real.log X.1) X :=
    (Real.contDiffAt_log.mpr hX.ne').comp X contDiffAt_fst
  exact hlog.prodMk ((Real.contDiff_exp.contDiffAt.comp X (hlog.div_const 2).neg).smul
    contDiffAt_snd)

/-! ## Lifted tests -/

/-- `liftTest a Φ c (t, y) = a(t) Φ(e^t, e^{t/2} y) e_c`: a heat-variable function `Φ`
transported to similarity variables, with a phase weight `a` (tex 7484–7497). -/
def liftTest (a : ℝ → ℝ) (Φ : SpaceTime → ℝ) (c : Fin 3) (z : SpaceTime) : Space :=
  (a z.1 * Φ (simE z)) • coordinateVector c

variable {a : ℝ → ℝ} {Φ : SpaceTime → ℝ} {c : Fin 3}

theorem contDiff_liftTest (ha : ContDiff ℝ ∞ a) (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (liftTest a Φ c) :=
  ((ha.comp contDiff_fst).mul (hΦ.comp contDiff_simE)).smul contDiff_const

theorem hasCompactSupport_liftTest (hac : HasCompactSupport a) (hΦc : HasCompactSupport Φ) :
    HasCompactSupport (liftTest a Φ c) := by
  obtain ⟨A, hA⟩ := hac.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) A).prod
    (isCompact_closedBall (0 : Space) (R * Real.exp (A / 2)))) ?_
  intro z hz
  simp only [liftTest]
  by_cases h1 : a z.1 = 0
  · simp [h1]
  by_cases h2 : Φ (simE z) = 0
  · simp [h2]
  exfalso
  apply hz
  have hz1 : z.1 ∈ closedBall (0 : ℝ) A := hA (subset_tsupport _ h1)
  have hz2 : simE z ∈ closedBall (0 : SpaceTime) R := hR (subset_tsupport _ h2)
  rw [mem_closedBall, dist_zero_right] at hz1 hz2
  refine ⟨by rw [mem_closedBall, dist_zero_right]; exact hz1, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  have h3 : ‖(simE z).2‖ ≤ R := (norm_snd_le _).trans hz2
  simp only [simE, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h3
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hz2
  rw [Real.norm_eq_abs] at hz1
  have hzA : -A ≤ z.1 := by linarith [neg_abs_le z.1]
  have h4 : ‖z.2‖ ≤ R * Real.exp (-(z.1 / 2)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    linarith
  calc ‖z.2‖ ≤ R * Real.exp (-(z.1 / 2)) := h4
    _ ≤ R * Real.exp (A / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hR0

theorem isSimilarityTest_liftTest (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) : IsSimilarityTest (liftTest a Φ c) :=
  ⟨contDiff_liftTest ha hΦ, hasCompactSupport_liftTest hac hΦc⟩

theorem pairTerm_liftTest (f : ℝ → SpatialField) (z : SpaceTime) :
    pairTerm f (liftTest a Φ c) z = f z.1 z.2 c * (a z.1 * Φ (simE z)) := by
  rw [pairTerm, liftTest, inner_smul_coordinateVector, mul_comm]

/-! ## Derivatives of lifted tests -/

theorem hasDerivAt_simE_time (t : ℝ) (y : Space) :
    HasDerivAt (fun s : ℝ => simE (s, y)) (Real.exp t, (Real.exp (t / 2) * (1 / 2)) • y) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
    ((hasDerivAt_id' t).div_const 2).exp
  exact (Real.hasDerivAt_exp t).prodMk (h1.smul_const y)

/-- `∂_t ψ` for `ψ = a(t) Φ∘E e_c`. -/
theorem timeDerivative_liftTest (ha : Differentiable ℝ a) (hΦ : Differentiable ℝ Φ)
    (t : ℝ) (y : Space) :
    timeDerivative (liftTest a Φ c) t y =
      (deriv a t * Φ (simE (t, y)) + a t * (Real.exp t * tD Φ (simE (t, y)) +
        1 / 2 * fderiv ℝ Φ (simE (t, y)) (0, Real.exp (t / 2) • y))) • coordinateVector c := by
  have hΦγ : HasDerivAt (fun s => Φ (simE (s, y)))
      (fderiv ℝ Φ (simE (t, y)) (Real.exp t, (Real.exp (t / 2) * (1 / 2)) • y)) t :=
    (hΦ _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_simE_time t y)
  have hlin : fderiv ℝ Φ (simE (t, y)) (Real.exp t, (Real.exp (t / 2) * (1 / 2)) • y) =
      Real.exp t * tD Φ (simE (t, y)) +
        1 / 2 * fderiv ℝ Φ (simE (t, y)) (0, Real.exp (t / 2) • y) := by
    have e : ((Real.exp t, (Real.exp (t / 2) * (1 / 2)) • y) : SpaceTime) =
        Real.exp t • ((1 : ℝ), (0 : Space)) + (1 / 2 : ℝ) • ((0 : ℝ), Real.exp (t / 2) • y) := by
      refine Prod.ext ?_ ?_
      · simp
      · simp [smul_smul, mul_comm]
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rfl
  have hfin : HasDerivAt (fun s => liftTest a Φ c (s, y))
      ((deriv a t * Φ (simE (t, y)) + a t * fderiv ℝ Φ (simE (t, y))
        (Real.exp t, (Real.exp (t / 2) * (1 / 2)) • y)) • coordinateVector c) t :=
    ((ha t).hasDerivAt.mul hΦγ).smul_const _
  rw [timeDerivative, fderiv_apply_one_eq_deriv, hfin.deriv, hlin]

theorem hasFDerivAt_simE_space (t : ℝ) (y : Space) :
    HasFDerivAt (fun y' : Space => simE (t, y'))
      ((ContinuousLinearMap.inr ℝ ℝ Space).comp
        (Real.exp (t / 2) • ContinuousLinearMap.id ℝ Space)) y := by
  have h := (hasFDerivAt_const (Real.exp t) y).prodMk
    ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul (Real.exp (t / 2)))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

/-- The spatial derivative of `y ↦ b Φ(e^t, e^{t/2} y) e_c`. -/
theorem fderiv_slice_simE (hΦ : Differentiable ℝ Φ) (b t : ℝ) (y v : Space) :
    fderiv ℝ (fun y' : Space => (b * Φ (simE (t, y'))) • coordinateVector c) y v =
      (b * fderiv ℝ Φ (simE (t, y)) (0, Real.exp (t / 2) • v)) • coordinateVector c := by
  have h2 : HasFDerivAt (fun y' : Space => (b * Φ (simE (t, y'))) • coordinateVector c)
      ((b • ((fderiv ℝ Φ (simE (t, y))).comp ((ContinuousLinearMap.inr ℝ ℝ Space).comp
        (Real.exp (t / 2) • ContinuousLinearMap.id ℝ Space)))).smulRight (coordinateVector c)) y :=
    (((hΦ _).hasFDerivAt.comp y (hasFDerivAt_simE_space t y)).const_mul b).smul_const
      (coordinateVector c)
  rw [h2.fderiv]
  have e : ((0 : ℝ), Real.exp (t / 2) • v) = Real.exp (t / 2) • ((0 : ℝ), v) := by simp
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, e]

theorem spatialDerivative_liftTest (hΦ : Differentiable ℝ Φ) (t : ℝ) (y v : Space) :
    spatialDerivative (liftTest a Φ c) t y v =
      (a t * fderiv ℝ Φ (simE (t, y)) (0, Real.exp (t / 2) • v)) • coordinateVector c :=
  fderiv_slice_simE hΦ (a t) t y v

theorem differentiable_sD {Ψ : SpaceTime → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (i : Fin 3) :
    Differentiable ℝ (sD i Ψ) :=
  ((hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)

/-- `Δ_y ψ = a e^t (Δ_xΦ)∘E e_c` for `ψ = a(t) Φ∘E e_c`. -/
theorem spatialLaplacian_liftTest (hΦ : ContDiff ℝ ∞ Φ) (t : ℝ) (y : Space) :
    spatialLaplacian (liftTest a Φ c) t y =
      (a t * Real.exp t * sLap Φ (simE (t, y))) • coordinateVector c := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hrow : ∀ i : Fin 3,
      (fun y' => spatialDerivative (liftTest a Φ c) t y' (coordinateVector i)) =
        fun y' => ((a t * Real.exp (t / 2)) * sD i Φ (simE (t, y'))) • coordinateVector c := by
    intro i
    funext y'
    rw [spatialDerivative_liftTest hd]
    have e : ((0 : ℝ), Real.exp (t / 2) • coordinateVector i) =
        Real.exp (t / 2) • ((0 : ℝ), coordinateVector i) := by simp
    rw [e, map_smul, smul_eq_mul, ← mul_assoc]
    rfl
  have hterm : ∀ i : Fin 3,
      fderiv ℝ (fun y' => spatialDerivative (liftTest a Φ c) t y' (coordinateVector i)) y
        (coordinateVector i) =
      (a t * Real.exp t * sD2 i i Φ (simE (t, y))) • coordinateVector c := by
    intro i
    rw [hrow i, fderiv_slice_simE (differentiable_sD hΦ i)]
    have e : ((0 : ℝ), Real.exp (t / 2) • coordinateVector i) =
        Real.exp (t / 2) • ((0 : ℝ), coordinateVector i) := by simp
    rw [e, map_smul, smul_eq_mul]
    have hexp : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
      rw [← Real.exp_add, add_halves]
    rw [hexp]
    congr 1
    show _ = a t * (Real.exp (t / 2) * Real.exp (t / 2)) *
      fderiv ℝ (sD i Φ) (simE (t, y)) ((0 : ℝ), coordinateVector i)
    ring
  rw [spatialLaplacian, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul,
    ← Finset.mul_sum]
  rfl

/-! ## Phase weights and linear maps commute with `Δ_y` -/

theorem contDiff_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : SpaceTime → F} (hV : ContDiff ℝ ∞ V) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space => V (t, y)) :=
  hV.comp (contDiff_const.prodMk contDiff_id)

/-- `Δ_y (b(t) T V) = b(t) T Δ_y V`. -/
theorem spatialLaplacian_smul_clm {b : ℝ → ℝ} {V : SpaceTime → Space} (hV : ContDiff ℝ ∞ V)
    (T : Space →L[ℝ] Space) (t : ℝ) (y : Space) :
    spatialLaplacian (fun z => b z.1 • T (V z)) t y = b t • T (spatialLaplacian V t y) := by
  have hsl := contDiff_slice hV t
  have hD : ∀ y', spatialDerivative (fun z => b z.1 • T (V z)) t y' =
      b t • T.comp (spatialDerivative V t y') := fun y' =>
    ((T.hasFDerivAt.comp y' ((hsl.differentiable (by simp)) y').hasFDerivAt).const_smul
      (b t)).fderiv
  rw [spatialLaplacian, spatialLaplacian, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrow : (fun y' => spatialDerivative (fun z => b z.1 • T (V z)) t y' (coordinateVector i)) =
      fun y' => b t • T (spatialDerivative V t y' (coordinateVector i)) :=
    funext fun y' => by rw [hD y']; rfl
  have hdiff : Differentiable ℝ (fun y' => spatialDerivative V t y' (coordinateVector i)) :=
    ((hsl.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have h3 : HasFDerivAt (fun y' => b t • T (spatialDerivative V t y' (coordinateVector i)))
      (b t • T.comp (fderiv ℝ (fun y' => spatialDerivative V t y' (coordinateVector i)) y)) y :=
    (T.hasFDerivAt.comp y (hdiff y).hasFDerivAt).const_smul (b t)
  rw [hrow, h3.fderiv]
  rfl

/-- `Δ_y (b(t) V) = b(t) Δ_y V`. -/
theorem spatialLaplacian_smul_time {b : ℝ → ℝ} {V : SpaceTime → Space} (hV : ContDiff ℝ ∞ V)
    (t : ℝ) (y : Space) :
    spatialLaplacian (fun z => b z.1 • V z) t y = b t • spatialLaplacian V t y :=
  spatialLaplacian_smul_clm (b := b) hV (ContinuousLinearMap.id ℝ Space) t y

/-- `Δ_y (b(t) V_c e_c) = b(t) (Δ_y V)_c e_c`. -/
theorem spatialLaplacian_component {b : ℝ → ℝ} {V : SpaceTime → Space} (hV : ContDiff ℝ ∞ V)
    (c : Fin 3) (t : ℝ) (y : Space) :
    spatialLaplacian (fun z => (b z.1 * V z c) • coordinateVector c) t y =
      (b t * spatialLaplacian V t y c) • coordinateVector c := by
  set T : Space →L[ℝ] Space := (EuclideanSpace.proj c).smulRight (coordinateVector c)
  have h := spatialLaplacian_smul_clm (b := b) hV T t y
  have e : (fun z : SpaceTime => (b z.1 * V z c) • coordinateVector c) =
      fun z => b z.1 • T (V z) := by
    funext z
    simp [T, mul_smul]
  rw [e, h]
  simp [T, mul_smul]

/-! ## Heat tests from similarity tests -/

/-- `push f` is a heat test when `f` is a smooth compactly supported function of `(t, y)`. -/
theorem isSTTest_push {f : SpaceTime → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    IsSTTest (d := 3) (push f) := by
  obtain ⟨R, hR0, hT, hS⟩ := B0005.exists_window_of_hasCompactSupport hfc
  refine ⟨contDiff_iff_contDiffAt.mpr fun X => ?_, ?_⟩
  · by_cases hX : 0 < X.1
    · have hev : (fun X' => f (simG X')) =ᶠ[𝓝 X] push f := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hX] with X' hX'
        have hX'' : 0 < X'.1 := hX'
        simp only [push, hX'', ↓reduceIte]
      exact (hf.contDiffAt.comp X (contDiffAt_simG hX)).congr_of_eventuallyEq hev.symm
    · have hX0 : X.1 < Real.exp (-R) := (not_lt.mp hX).trans_lt (Real.exp_pos _)
      have hev : push f =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hX0] with X' hX'
        have hX'' : X'.1 < Real.exp (-R) := hX'
        by_cases hp : 0 < X'.1
        · simp only [push, hp, ↓reduceIte]
          refine hT _ _ fun hmem => ?_
          have hlt := Real.log_lt_log hp hX''
          rw [Real.log_exp] at hlt
          exact absurd hmem.1 (not_le.mpr hlt)
        · simp only [push, hp, ↓reduceIte]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · refine HasCompactSupport.intro ((isCompact_Icc (a := Real.exp (-R)) (b := Real.exp R)).prod
      (isCompact_closedBall (0 : Space) (R * Real.exp (R / 2)))) ?_
    intro X hX
    by_cases hp : 0 < X.1
    · simp only [push, hp, ↓reduceIte]
      by_cases ht : Real.log X.1 ∈ Icc (-R) R
      · refine hS _ _ ?_
        have hX1 : X.1 ∈ Icc (Real.exp (-R)) (Real.exp R) := by
          rw [← Real.exp_log hp]
          exact ⟨Real.exp_le_exp.mpr ht.1, Real.exp_le_exp.mpr ht.2⟩
        have hX2 : R * Real.exp (R / 2) < ‖X.2‖ := by
          by_contra hle
          exact hX ⟨hX1, by rw [mem_closedBall, dist_zero_right]; exact not_lt.mp hle⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h1 : Real.exp (-(R / 2)) ≤ Real.exp (-(Real.log X.1 / 2)) :=
          Real.exp_le_exp.mpr (by linarith [ht.2])
        have h2 : R = Real.exp (-(R / 2)) * (R * Real.exp (R / 2)) := by
          rw [mul_comm R, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
        calc R = Real.exp (-(R / 2)) * (R * Real.exp (R / 2)) := h2
          _ < Real.exp (-(R / 2)) * ‖X.2‖ := mul_lt_mul_of_pos_left hX2 (Real.exp_pos _)
          _ ≤ Real.exp (-(Real.log X.1 / 2)) * ‖X.2‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      · exact hT _ _ ht
    · simp only [push, hp, ↓reduceIte]

end UnforcedLeray.Cons.L2.FreeLapReg
