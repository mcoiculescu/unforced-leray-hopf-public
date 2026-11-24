import UnforcedLeray.Short.PartIIb.Sub.G1

/-!
# Part II-b, task `PartII-b:G1`: the Cartesian gradient of the ring lift

Proves `UnforcedLeray.Short.IIb.NvFderivBound` (`Sub/G1.lean`), the calculus input of the strong
late coefficient bound. Source of record: `the November 2 reference manuscript`,
SP 2422-2423.

For `R > 0`, `y ∉ axis`, and `b` differentiable at `c = chart R τ y`, put `s = age R y`,
`ε = R⁻¹`, `P = ϱD y w = e_r · w`, `η = c.2.2`. The chart computation gives

`D(Nv b)[w] = s P · frameL(Q_ε b) + s w_z · frameL(∂_η b) + √s b_r · De_r[w]`,

with `Q_ε b = ∂_ξ b - ε(2s ∂_s b + η ∂_η b + b)`. Here `√s = R/ϱ`, `√s/ϱ = ε s`,
`|P| ≤ ‖w‖`, `|w_z| ≤ ‖w‖`, and `‖De_r[w]‖ ≤ ‖w‖/ϱ`. These give the bound
`s(‖∂_η b‖ + ‖Q_ε b‖ + ε|b_r|)`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray UnforcedLeray.Axi

/-- Squared Euclidean norm in coordinates on `Space`. -/
theorem nvFderiv_norm_sq (w : Space) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- `|e_r · w| ≤ ‖w‖`, where `ϱD y w = e_r · w`. -/
theorem nvFderiv_abs_ϱD_le {y : Space} (hy : y ∉ axis) (w : Space) : |ϱD y w| ≤ ‖w‖ := by
  have hρ := ϱ_pos hy
  rw [ϱD_apply, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (norm_nonneg w) hρ.le)
  rw [mul_pow, nvFderiv_norm_sq w, ϱ_sq y]
  nlinarith [sq_nonneg (y 0 * w 1 - y 1 * w 0),
    mul_nonneg (sq_nonneg (w 2)) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))]

/-- The axial coordinate is bounded by the norm. -/
theorem nvFderiv_abs_two_le (w : Space) : |w 2| ≤ ‖w‖ := by
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg w)
  rw [nvFderiv_norm_sq w]
  nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]

/-- `‖De_r[w]‖ ≤ ‖w‖/ϱ` (`eRD_apply`). -/
theorem nvFderiv_eRD_norm_le {y : Space} (hy : y ∉ axis) (w : Space) :
    ‖eRD y w‖ ≤ ‖w‖ / ϱ y := by
  have hρ := ϱ_pos hy
  have hk : ϱD y w = eR y 0 * w 0 + eR y 1 * w 1 := by
    rw [ϱD_apply, eR_apply_zero, eR_apply_one]; ring
  have h1 : eR y 0 ^ 2 + eR y 1 ^ 2 = 1 := by
    rw [eR_apply_zero, eR_apply_one]; exact eR_sq_sum hy
  have hA : ϱD y w * (eR y 0 * w 0 + eR y 1 * w 1) = ϱD y w ^ 2 := by
    rw [← hk]; ring
  have hB : ϱD y w ^ 2 * (eR y 0 ^ 2 + eR y 1 ^ 2) = ϱD y w ^ 2 := by
    rw [h1, mul_one]
  have hu : ‖hor w - ϱD y w • eR y‖ ≤ ‖w‖ := by
    have hsq : ‖hor w - ϱD y w • eR y‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      simp only [nvFderiv_norm_sq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        hor_apply_zero, hor_apply_one, hor_apply_two, eR_apply_two]
      nlinarith [sq_nonneg (w 2), sq_nonneg (ϱD y w), hA, hB]
    have h := abs_le_of_sq_le_sq hsq (norm_nonneg w)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [eRD_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hρ.le), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hu (inv_nonneg.2 hρ.le)

/-- The chart derivative in profile coordinates:
`fderiv b c (chartD v) = (Ds) ∂_s b + (Dξ) ∂_ξ b + (Dη) ∂_η b`. -/
theorem nvFderiv_fderiv_chartD (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (y v : Space) :
    fderiv ℝ b (chart R τ y) (chartD R y v) =
      (-(2 * R ^ 2 / ϱ y ^ 3) * ϱD y v) • dS b (chart R τ y) +
        (R / ϱ y * ϱD y v) • dQ b (chart R τ y) +
        (R / ϱ y * v 2 - R * y 2 / ϱ y ^ 2 * ϱD y v) • dEta b (chart R τ y) := by
  rw [chartD_apply, clm_triple]
  rfl

/-- The profile combination `Q_ε b = ∂_ξ b - ε(2s ∂_s b + η ∂_η b + b)` at a chart point `x`.
It is the same expression as in `gradProfileQuantity`. -/
def nvQ (ε : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × (ℝ × ℝ)) : Merid :=
  dQ b x - ε • ((2 * x.1) • dS b x + x.2.2 • dEta b x + b x)

/-- The derivative of `Nv R b τ` at `y`:
`s P frameL(Q_ε b) + s w_z frameL(∂_η b) + √s b_r De_r`, written as a CLM. -/
def nvL (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (y : Space) : Space →L[ℝ] Space :=
  (ϱD y).smulRight (age R y • frameL y (nvQ R⁻¹ b (chart R τ y))) +
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight
      (age R y • frameL y (dEta b (chart R τ y))) +
    (√(age R y) * b (chart R τ y) 0) • eRD y

theorem nvL_apply (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (y w : Space) :
    nvL R τ b y w = ϱD y w • (age R y • frameL y (nvQ R⁻¹ b (chart R τ y))) +
      w 2 • (age R y • frameL y (dEta b (chart R τ y))) +
      (√(age R y) * b (chart R τ y) 0) • eRD y w := by
  simp only [nvL, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, EuclideanSpace.coe_proj]

/-- The lift `Nv R b τ` is differentiable off the axis with derivative `nvL R τ b y`. -/
theorem nvFderiv_hasFDerivAt {R τ : ℝ} (hR : 0 < R) {b : ℝ × (ℝ × ℝ) → Merid} {y : Space}
    (hy : y ∉ axis) (hb : DifferentiableAt ℝ b (chart R τ y)) :
    HasFDerivAt (Nv R b τ) (nvL R τ b y) y := by
  have hR0 : R ≠ 0 := hR.ne'
  have hρ0 : ϱ y ≠ 0 := ϱ_ne_zero hy
  have hs : 0 < age R y := age_pos hR0 hy
  -- the scalar factor `√(age R ·)`
  have hA : HasFDerivAt (fun x => √(age R x)) ((-(R / ϱ y ^ 2)) • ϱD y) y := by
    refine ((hasFDerivAt_age R hy).sqrt hs.ne').congr_fderiv
      (ContinuousLinearMap.ext fun v => ?_)
    simp only [ageD, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [sqrt_age hR hy]
    field_simp
  -- the frame-valued factor `(b(chart x))_r e_r + (b(chart x))_z e_z`
  have hBx : HasFDerivAt (fun x => b (chart R τ x))
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y)) y :=
    hb.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hb0 := (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hBx
  have hb1 := (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hBx
  have hV := (hb0.fun_smul (hasFDerivAt_eR hy)).add (hb1.fun_smul (hasFDerivAt_const e3 y))
  have hN := hA.fun_smul hV
  have hfun : Nv R b τ = fun x => √(age R x) •
      ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ) (b (chart R τ x)) • eR x +
        (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ) (b (chart R τ x)) • e3) := by
    funext x
    simp only [Nv, frameL_apply, EuclideanSpace.coe_proj]
  rw [hfun]
  refine hN.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  rw [nvL_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Pi.add_apply, Function.comp_apply, smul_zero, zero_add, smul_add,
    EuclideanSpace.coe_proj, nvFderiv_fderiv_chartD, frameL_apply, nvQ,
    PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  simp only [show (chart R τ y).1 = UnforcedLeray.Axi.age R y from rfl,
    show (chart R τ y).2.2 = UnforcedLeray.Axi.trans R y from rfl, sqrt_age hR hy]
  unfold UnforcedLeray.Axi.age UnforcedLeray.Axi.trans
  match_scalars <;> field_simp <;> ring

/-- **`PartII-b:G1`, Cartesian gradient of the ring lift** (`NvFderivBound`, SP 2422-2423). -/
theorem nvFderivBound : UnforcedLeray.Short.IIb.NvFderivBound := by
  unfold UnforcedLeray.Short.IIb.NvFderivBound
  intro R τ b y hR hy hb
  have hL := nvFderiv_hasFDerivAt hR hy hb
  refine ⟨hL.differentiableAt, ?_⟩
  rw [hL.fderiv]
  have hs0 : 0 ≤ age R y := age_nonneg R y
  have hε : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hR0 : R ≠ 0 := hR.ne'
  have hρ0 : ϱ y ≠ 0 := ϱ_ne_zero hy
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ fun w => ?_
  · change 0 ≤ age R y * (‖dEta b (chart R τ y)‖ + ‖nvQ R⁻¹ b (chart R τ y)‖ +
      R⁻¹ * |b (chart R τ y) 0|)
    exact mul_nonneg hs0 (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg hε (abs_nonneg _)))
  · change ‖nvL R τ b y w‖ ≤ age R y * (‖dEta b (chart R τ y)‖ + ‖nvQ R⁻¹ b (chart R τ y)‖ +
      R⁻¹ * |b (chart R τ y) 0|) * ‖w‖
    have n1 : ‖ϱD y w • (age R y • frameL y (nvQ R⁻¹ b (chart R τ y)))‖ ≤
        ‖w‖ * (age R y * ‖nvQ R⁻¹ b (chart R τ y)‖) := by
      simp only [norm_smul, norm_frameL hy, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_right (nvFderiv_abs_ϱD_le hy w)
        (mul_nonneg hs0 (norm_nonneg _))
    have n2 : ‖w 2 • (age R y • frameL y (dEta b (chart R τ y)))‖ ≤
        ‖w‖ * (age R y * ‖dEta b (chart R τ y)‖) := by
      simp only [norm_smul, norm_frameL hy, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_right (nvFderiv_abs_two_le w) (mul_nonneg hs0 (norm_nonneg _))
    have hsq : √(age R y) / ϱ y = R⁻¹ * age R y := by
      rw [sqrt_age hR hy]
      unfold UnforcedLeray.Axi.age
      field_simp
    have n3 : ‖(√(age R y) * b (chart R τ y) 0) • eRD y w‖ ≤
        ‖w‖ * (R⁻¹ * age R y * |b (chart R τ y) 0|) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (age R y))]
      have h1 := mul_le_mul_of_nonneg_left (nvFderiv_eRD_norm_le hy w)
        (mul_nonneg (Real.sqrt_nonneg (age R y)) (abs_nonneg (b (chart R τ y) 0)))
      have e : √(age R y) * |b (chart R τ y) 0| * (‖w‖ / ϱ y) =
          ‖w‖ * (R⁻¹ * age R y * |b (chart R τ y) 0|) := by
        rw [← hsq]; ring
      linarith
    rw [nvL_apply]
    refine norm_add₃_le.trans ?_
    linarith [n1, n2, n3]
