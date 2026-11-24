import UnforcedLeray.Units.B0226.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# B0226, part 7: the axis is removable for the divergence of `L²` fields

Blueprint unit B0226, `paper/main.tex` lines 3394–3402, proof outline ("for the distributional
version, pair with axisymmetric test functions"); scoping note

(removability of the axis).

`mem_physSolenoidal_of_offAxis`: a field `V ∈ L²(dx dτ)` (one period `2εc`) whose divergence
vanishes against every test of `ℝ³ × period` that vanishes near the axis
(`x₀² + x₁² ≤ t` for some `t > 0`) is divergence free against every test.

Proof. For a test `φ` and `0 < t ≤ 1` let `ψ_t = χ_t φ` with
`χ_t(x) = κ((x₀² + x₁²)/t)`, `κ = 0` on `(-∞, 1]` and `κ = 1` on `[2, ∞)` (`kappa`, built from
Mathlib's `Real.smoothTransition`). Then `ψ_t` vanishes near the axis, and
`g_t = ∇ₓφ − ∇ₓψ_t` vanishes off `A_t = {x₀² + x₁² ≤ 2t, |x₃| ≤ R}` (`R` bounds the support of
`φ`). On `A_t`, `|g_t| ≤ M₁ + 2 M₀ C t⁻¹ r`, so `|g_t|² ≤ 2M₁² + 16 M₀² C²/t`, while
`|A_t| ≤ 16 t R P` (a box). Hence `‖g_t‖²_{L²} ≤ 16RP(2M₁² + 16M₀²C²)` uniformly in `t`, and
`⟪V, ∇ₓφ⟫² = ⟪1_{A_t} V, g_t⟫² ≤ ‖1_{A_t} V‖² ‖g_t‖² → 0` as `t → 0`, by absolute continuity of
`∫ |V|²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Function
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-! ### Squared distance to the axis -/

/-- `x₀² + x₁²`, the squared distance to the axis. -/
def axisSq (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2

theorem axisSq_nonneg (x : Space) : 0 ≤ axisSq x := by
  unfold axisSq
  positivity

theorem radius_sq_eq_axisSq (x : Space) : radius x ^ 2 = axisSq x :=
  Real.sq_sqrt (axisSq_nonneg x)

theorem contDiff_axisSq {k : WithTop ℕ∞} : ContDiff ℝ k axisSq := by
  unfold axisSq
  fun_prop

theorem continuous_axisSq : Continuous axisSq :=
  (contDiff_axisSq (k := 0)).continuous

/-- The derivative `v ↦ 2x₀v₀ + 2x₁v₁` of `axisSq`. -/
def axisSqD (x : Space) : Space →L[ℝ] ℝ :=
  (2 * x 0) • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) +
    (2 * x 1) • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)

theorem axisSqD_apply (x v : Space) : axisSqD x v = 2 * x 0 * v 0 + 2 * x 1 * v 1 := by
  simp only [axisSqD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]

theorem hasFDerivAt_axisSq (x : Space) : HasFDerivAt axisSq (axisSqD x) x := by
  have h0 : HasFDerivAt (fun x : Space => x 0)
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun x : Space => x 1)
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  refine ((h0.pow 2).add (h1.pow 2)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [axisSqD_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, nsmul_eq_mul]
  ring

theorem norm_sq_eq_coords (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem abs_axisSqD_le (x v : Space) : |axisSqD x v| ≤ 2 * radius x * ‖v‖ := by
  rw [axisSqD_apply]
  have hr := radius_sq_eq_axisSq x
  have hv := norm_sq_eq_coords v
  unfold axisSq at hr
  refine abs_le_of_sq_le_sq ?_
    (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (norm_nonneg _))
  rw [mul_pow, mul_pow, hr, hv]
  nlinarith [sq_nonneg (x 0 * v 1 - x 1 * v 0), sq_nonneg (v 2), sq_nonneg (x 0),
    sq_nonneg (x 1)]

theorem abs_coord_two_le (x : Space) : |x 2| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x 2
  rwa [Real.norm_eq_abs] at this

/-! ### The cutoff profile `κ` -/

/-- `κ(s) = smoothTransition (s − 1)`: smooth, `0` on `(-∞, 1]`, `1` on `[2, ∞)`. -/
def kappa (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

theorem contDiff_kappa : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kappa :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem kappa_eq_zero {s : ℝ} (h : s ≤ 1) : kappa s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem kappa_eq_one {s : ℝ} (h : 2 ≤ s) : kappa s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem kappa_nonneg (s : ℝ) : 0 ≤ kappa s := Real.smoothTransition.nonneg _

theorem kappa_le_one (s : ℝ) : kappa s ≤ 1 := Real.smoothTransition.le_one _

theorem deriv_kappa_of_lt_one {s : ℝ} (h : s < 1) : deriv kappa s = 0 := by
  have : kappa =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds h] with u hu using kappa_eq_zero hu.le
  rw [this.deriv_eq, deriv_const]

theorem deriv_kappa_of_two_lt {s : ℝ} (h : 2 < s) : deriv kappa s = 0 := by
  have : kappa =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    filter_upwards [lt_mem_nhds h] with u hu using kappa_eq_one hu.le
  rw [this.deriv_eq, deriv_const]

theorem exists_bound_deriv_kappa : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |deriv kappa s| ≤ C := by
  have hc : Continuous (deriv kappa) := contDiff_kappa.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  by_cases h1 : s < 1
  · rw [deriv_kappa_of_lt_one h1, abs_zero]
    exact le_max_right _ _
  by_cases h2 : 2 < s
  · rw [deriv_kappa_of_two_lt h2, abs_zero]
    exact le_max_right _ _
  have := hC s ⟨not_lt.1 h1, not_lt.1 h2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-! ### The axis cutoff `χ_t` and the cut tests `χ_t φ` -/

/-- `χ_t(x, τ) = κ((x₀² + x₁²)/t)`. -/
def cutoff (t : ℝ) (y : Space × ℝ) : ℝ := kappa (axisSq y.1 * t⁻¹)

theorem contDiff_cutoff (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoff t) :=
  contDiff_kappa.comp ((contDiff_axisSq.comp contDiff_fst).mul contDiff_const)

theorem hasFDerivAt_cutoff (t : ℝ) (y : Space × ℝ) :
    HasFDerivAt (cutoff t) (deriv kappa (axisSq y.1 * t⁻¹) •
      (t⁻¹ • (axisSqD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))) y := by
  have h1 : HasFDerivAt (fun y : Space × ℝ => axisSq y.1)
      ((axisSqD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) y :=
    (hasFDerivAt_axisSq y.1).comp y hasFDerivAt_fst
  have hk : HasDerivAt kappa (deriv kappa (axisSq y.1 * t⁻¹)) (axisSq y.1 * t⁻¹) :=
    ((contDiff_kappa.differentiable (by simp)) _).hasDerivAt
  exact hk.comp_hasFDerivAt y (h1.mul_const t⁻¹)

/-- The cut test `χ_t φ`. -/
def cutTest (t : ℝ) (φ : Space × ℝ → ℝ) (y : Space × ℝ) : ℝ := cutoff t y * φ y

theorem isPhysTest_cutTest {P : ℝ} (t : ℝ) {φ : Space × ℝ → ℝ} (hφ : IsPhysTest P φ) :
    IsPhysTest P (cutTest t φ) where
  smooth := (contDiff_cutoff t).mul hφ.smooth
  periodic x τ := by simp only [cutTest, cutoff, hφ.periodic x τ]
  bounded := by
    obtain ⟨R, hR⟩ := hφ.bounded
    exact ⟨R, fun y hy => hR y (right_ne_zero_of_mul hy)⟩

theorem cutTest_eq_zero {t : ℝ} (ht : 0 < t) (φ : Space × ℝ → ℝ) {y : Space × ℝ}
    (hy : axisSq y.1 ≤ t) : cutTest t φ y = 0 := by
  have : axisSq y.1 * t⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one ht).2 hy
  simp only [cutTest, cutoff, kappa_eq_zero this, zero_mul]

/-- `⟪∇ₓφ − ∇ₓ(χ_t φ), v⟫ = (1 − χ_t) Dφ(v,0) − φ κ'(·) t⁻¹ (2x₀v₀ + 2x₁v₁)`. -/
theorem inner_gradX_sub_cutTest {t : ℝ} {φ : Space × ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (y : Space × ℝ) (v : Space) :
    ⟪gradX φ y - gradX (cutTest t φ) y, v⟫_ℝ =
      (1 - cutoff t y) * fderiv ℝ φ y (v, 0) -
        φ y * (deriv kappa (axisSq y.1 * t⁻¹) * (t⁻¹ * axisSqD y.1 v)) := by
  have hd : HasFDerivAt φ (fderiv ℝ φ y) y :=
    ((hφ.differentiable (by simp)) y).hasFDerivAt
  have hm : HasFDerivAt (cutTest t φ) (cutoff t y • fderiv ℝ φ y + φ y •
      (deriv kappa (axisSq y.1 * t⁻¹) •
        (t⁻¹ • (axisSqD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)))) y :=
    (hasFDerivAt_cutoff t y).mul hd
  rw [inner_sub_left, inner_gradX, inner_gradX, hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  ring

theorem norm_prod_zero (v : Space) : ‖((v, 0) : Space × ℝ)‖ = ‖v‖ := by
  simp [Prod.norm_def]

/-! ### Bounds for a test -/

/-- A test `φ` of `ℝ³ × period` has bounded support in `x` and, on one period, bounded values
and derivative. -/
theorem exists_bounds_physTest {P : ℝ} {φ : Space × ℝ → ℝ} (hφ : IsPhysTest P φ) :
    ∃ R M0 M1 : ℝ, 0 ≤ R ∧ 0 ≤ M0 ∧ 0 ≤ M1 ∧
      (∀ y : Space × ℝ, R < ‖y.1‖ → φ y = 0 ∧ fderiv ℝ φ y = 0) ∧
      ∀ y : Space × ℝ, y.2 ∈ Ioc 0 P → |φ y| ≤ M0 ∧ ‖fderiv ℝ φ y‖ ≤ M1 := by
  obtain ⟨R0, hR0⟩ := hφ.bounded
  set R := max R0 0 with hRdef
  have hK : IsCompact (Metric.closedBall (0 : Space) R ×ˢ Icc 0 P) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hc : Continuous φ := hφ.smooth.continuous
  have hDc : Continuous (fderiv ℝ φ) := hφ.smooth.continuous_fderiv (by simp)
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hDc.continuousOn
  have hout : ∀ y : Space × ℝ, R < ‖y.1‖ → φ y = 0 ∧ fderiv ℝ φ y = 0 := by
    intro y hy
    have hy0 : R0 < ‖y.1‖ := lt_of_le_of_lt (le_max_left _ _) hy
    refine ⟨?_, ?_⟩
    · by_contra h
      exact absurd (hR0 y h) (not_le.2 hy0)
    · refine fderiv_of_notMem_tsupport ℝ fun hmem => ?_
      exact absurd (tsupport_subset_of_bound hR0 hmem) (not_le.2 hy0)
  refine ⟨R, max M0 0, max M1 0, le_max_right _ _, le_max_right _ _, le_max_right _ _, hout,
    fun y hy => ?_⟩
  by_cases hyR : ‖y.1‖ ≤ R
  · have hyK : y ∈ Metric.closedBall (0 : Space) R ×ˢ Icc 0 P :=
      ⟨mem_closedBall_zero_iff.2 hyR, Ioc_subset_Icc_self hy⟩
    have h0 := hM0 y hyK
    have h1 := hM1 y hyK
    rw [Real.norm_eq_abs] at h0
    exact ⟨h0.trans (le_max_left _ _), h1.trans (le_max_left _ _)⟩
  · obtain ⟨e1, e2⟩ := hout y (not_le.1 hyR)
    rw [e1, e2, abs_zero, norm_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

/-! ### The region `A_t` and its measure -/

/-- `A_t = {x₀² + x₁² ≤ 2t, |x₃| ≤ R}` (times all `τ`). -/
def cutRegion (t R : ℝ) : Set (Space × ℝ) := {y | axisSq y.1 ≤ 2 * t ∧ |y.1 2| ≤ R}

theorem measurableSet_cutRegion (t R : ℝ) : MeasurableSet (cutRegion t R) := by
  have h1 : Continuous fun y : Space × ℝ => axisSq y.1 := continuous_axisSq.comp continuous_fst
  have h2 : Continuous fun y : Space × ℝ => |y.1 2| := by fun_prop
  exact (measurableSet_le h1.measurable measurable_const).inter
    (measurableSet_le h2.measurable measurable_const)

theorem volume_box_le {t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R) :
    volume {x : Space | axisSq x ≤ 2 * t ∧ |x 2| ≤ R} ≤ ENNReal.ofReal (8 * t * (2 * R)) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(2 * t) := ⟨_, rfl⟩
  set a : Fin 3 → ℝ := ![-s, -s, -R]
  set b : Fin 3 → ℝ := ![s, s, R]
  have hsub : {x : Space | axisSq x ≤ 2 * t ∧ |x 2| ≤ R} ⊆
      (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' Icc a b := by
    rintro x ⟨h1, h2⟩
    have hx0 : x 0 ^ 2 ≤ 2 * t := by
      unfold axisSq at h1
      nlinarith [sq_nonneg (x 1)]
    have hx1 : x 1 ^ 2 ≤ 2 * t := by
      unfold axisSq at h1
      nlinarith [sq_nonneg (x 0)]
    have a0 := abs_le.1 (Real.abs_le_sqrt hx0)
    have a1 := abs_le.1 (Real.abs_le_sqrt hx1)
    rw [← hs] at a0 a1
    have a2 := abs_le.1 h2
    simp only [mem_preimage, mem_Icc]
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp [a, b] <;> linarith
  have hvol : volume ((WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' Icc a b) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
    rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
      measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [hvol, Fin.prod_univ_three]
  simp only [a, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_neg_eq_add]
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * t := hs ▸ Real.sq_sqrt (by positivity)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  nlinarith [hs2]

theorem measure_cutRegion_le {ε c t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R) :
    physMeasure ε c (cutRegion t R) ≤ ENNReal.ofReal (16 * t * R * (2 * ε * c)) := by
  rw [physMeasure, Measure.restrict_apply (measurableSet_cutRegion t R)]
  have hset : cutRegion t R ∩ physDomain ε c =
      {x : Space | axisSq x ≤ 2 * t ∧ |x 2| ≤ R} ×ˢ Ioc 0 (2 * ε * c) := by
    ext y
    simp [cutRegion, physDomain, and_assoc]
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, sub_zero]
  calc volume {x : Space | axisSq x ≤ 2 * t ∧ |x 2| ≤ R} * ENNReal.ofReal (2 * ε * c)
      ≤ ENNReal.ofReal (8 * t * (2 * R)) * ENNReal.ofReal (2 * ε * c) := by
        gcongr
        exact volume_box_le ht hR
    _ = ENNReal.ofReal (16 * t * R * (2 * ε * c)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The pointwise bound on `∇ₓφ − ∇ₓ(χ_t φ)` -/

theorem gradX_sub_cutTest_bound {P t R M0 M1 C : ℝ} (ht : 0 < t) {φ : Space × ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hC : 0 ≤ C) (hCk : ∀ s, |deriv kappa s| ≤ C)
    (hout : ∀ y : Space × ℝ, R < ‖y.1‖ → φ y = 0 ∧ fderiv ℝ φ y = 0)
    (hin : ∀ y : Space × ℝ, y.2 ∈ Ioc 0 P → |φ y| ≤ M0 ∧ ‖fderiv ℝ φ y‖ ≤ M1)
    {y : Space × ℝ} (hy : y.2 ∈ Ioc 0 P) :
    ‖gradX φ y - gradX (cutTest t φ) y‖ ^ 2 ≤
      (cutRegion t R).indicator (fun _ => 2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹) y := by
  set g := gradX φ y - gradX (cutTest t φ) y with hg
  have hformula := inner_gradX_sub_cutTest (t := t) hφ y
  by_cases hA : y ∈ cutRegion t R
  · rw [indicator_of_mem hA]
    obtain ⟨hφ0, hφ1⟩ := hin y hy
    have hχ0 := kappa_nonneg (axisSq y.1 * t⁻¹)
    have hχ1 := kappa_le_one (axisSq y.1 * t⁻¹)
    set K := M1 + 2 * M0 * C * t⁻¹ * radius y.1 with hK
    have hbound : ∀ v : Space, |⟪g, v⟫_ℝ| ≤ K * ‖v‖ := by
      intro v
      rw [hformula v]
      have e1 : |fderiv ℝ φ y (v, 0)| ≤ M1 * ‖v‖ := by
        have := (fderiv ℝ φ y).le_opNorm (v, 0)
        rw [norm_prod_zero, Real.norm_eq_abs] at this
        exact this.trans (mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _))
      have e2 := abs_axisSqD_le y.1 v
      have e3 := hCk (axisSq y.1 * t⁻¹)
      have hti : 0 < t⁻¹ := inv_pos.2 ht
      have e4 : |1 - cutoff t y| ≤ 1 := by
        rw [abs_le]
        constructor <;> simp only [cutoff] <;> linarith
      calc |(1 - cutoff t y) * fderiv ℝ φ y (v, 0) -
            φ y * (deriv kappa (axisSq y.1 * t⁻¹) * (t⁻¹ * axisSqD y.1 v))|
          ≤ |1 - cutoff t y| * |fderiv ℝ φ y (v, 0)| +
            |φ y| * (|deriv kappa (axisSq y.1 * t⁻¹)| * (t⁻¹ * |axisSqD y.1 v|)) := by
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hti]
        _ ≤ 1 * (M1 * ‖v‖) + M0 * (C * (t⁻¹ * (2 * radius y.1 * ‖v‖))) := by
            gcongr
        _ = K * ‖v‖ := by
            rw [hK]
            ring
    have hK0 : 0 ≤ K := by
      rw [hK]
      have : 0 ≤ radius y.1 := Real.sqrt_nonneg _
      have : 0 ≤ t⁻¹ := (inv_pos.2 ht).le
      positivity
    have hgK : ‖g‖ ≤ K := by
      have h1 := hbound g
      rw [real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)] at h1
      by_cases hg0 : ‖g‖ = 0
      · rw [hg0]
        exact hK0
      · have hpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
        nlinarith
    have hr2 : radius y.1 ^ 2 ≤ 2 * t := by
      rw [radius_sq_eq_axisSq]
      exact hA.1
    calc ‖g‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgK 2
      _ ≤ 2 * M1 ^ 2 + 2 * (2 * M0 * C * t⁻¹ * radius y.1) ^ 2 := by
          rw [hK]
          nlinarith [sq_nonneg (M1 - 2 * M0 * C * t⁻¹ * radius y.1)]
      _ = 2 * M1 ^ 2 + 8 * M0 ^ 2 * C ^ 2 * t⁻¹ * t⁻¹ * radius y.1 ^ 2 := by ring
      _ ≤ 2 * M1 ^ 2 + 8 * M0 ^ 2 * C ^ 2 * t⁻¹ * t⁻¹ * (2 * t) := by
          gcongr
      _ = 2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹ := by
          field_simp
          ring
  · rw [indicator_of_notMem hA]
    have hzero : ∀ v : Space, ⟪g, v⟫_ℝ = 0 := by
      intro v
      rw [hformula v]
      simp only [cutRegion, mem_setOf_eq, not_and_or, not_le] at hA
      rcases hA with hA | hA
      · have h2 : 2 < axisSq y.1 * t⁻¹ := by
          rw [← div_eq_mul_inv, lt_div_iff₀ ht]
          linarith
        simp only [cutoff, kappa_eq_one h2.le, deriv_kappa_of_two_lt h2]
        ring
      · have hRy : R < ‖y.1‖ := lt_of_lt_of_le hA (abs_coord_two_le y.1)
        obtain ⟨e1, e2⟩ := hout y hRy
        rw [e1, e2]
        simp
    have : g = 0 := by
      have h := hzero g
      rwa [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h
    rw [this, norm_zero]
    norm_num

/-! ### Removability of the axis -/

/-- **Removability of the axis.** If `V ∈ L²(dx dτ)` (one period `2εc`) is orthogonal to the
gradients of all tests of `ℝ³ × period` vanishing near the axis, then `V` is divergence free. -/
theorem mem_physSolenoidal_of_offAxis {ε c : ℝ} (hP : 0 ≤ 2 * ε * c) (V : PhysL2 ε c)
    (h : ∀ ψ : PhysTest ε c, (∃ t > 0, ∀ y : Space × ℝ, axisSq y.1 ≤ t → ψ.1 y = 0) →
      ⟪V, physGrad ε c ψ⟫_ℝ = 0) :
    V ∈ physSolenoidal ε c := by
  rw [physSolenoidal, mem_orthogonal_span_range]
  intro φ
  set μ := physMeasure ε c with hμ
  obtain ⟨R, M0, M1, hR, hM0, hM1, hout, hin⟩ := exists_bounds_physTest φ.2
  obtain ⟨C, hC, hCk⟩ := exists_bound_deriv_kappa
  set Q : ℝ := 16 * R * (2 * ε * c) * (2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR) hP) (by positivity)
  -- the cut tests
  let ψ : ℝ → PhysTest ε c := fun t => ⟨cutTest t φ.1, isPhysTest_cutTest t φ.2⟩
  set A : ℝ → Set (Space × ℝ) := fun t => cutRegion t R with hA
  have hAm : ∀ t, MeasurableSet (A t) := fun t => measurableSet_cutRegion t R
  have hAfin : ∀ t, 0 ≤ t → μ (A t) ≠ ∞ := fun t ht =>
    ((measure_cutRegion_le ht hR).trans_lt ENNReal.ofReal_lt_top).ne
  -- the square of the pairing is bounded by `Q ∫_{A_t} |V|²`
  have hmain : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ⟪V, physGrad ε c φ⟫_ℝ ^ 2 ≤ (∫ y in A t, ‖V y‖ ^ 2 ∂μ) * Q := by
    intro t ht ht1
    set g := physGrad ε c φ - physGrad ε c (ψ t) with hgdef
    have hψ0 : ⟪V, physGrad ε c (ψ t)⟫_ℝ = 0 :=
      h (ψ t) ⟨t, ht, fun y hy => cutTest_eq_zero ht φ.1 hy⟩
    have h1 : ⟪V, physGrad ε c φ⟫_ℝ = ⟪V, g⟫_ℝ := by
      rw [hgdef, inner_sub_right, hψ0, sub_zero]
    have hgae : ∀ᵐ y ∂μ, g y = gradX φ.1 y - gradX (cutTest t φ.1) y := by
      filter_upwards [Lp.coeFn_sub (physGrad ε c φ) (physGrad ε c (ψ t)),
        coeFn_physGrad ε c φ, coeFn_physGrad ε c (ψ t)] with y e1 e2 e3
      rw [hgdef, e1, Pi.sub_apply, e2, e3]
    have hbd : ∀ᵐ y ∂μ, ‖g y‖ ^ 2 ≤
        (A t).indicator (fun _ => 2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹) y := by
      filter_upwards [hgae, ae_physMeasure ε c] with y e hy
      rw [e]
      exact gradX_sub_cutTest_bound ht φ.2.smooth hM0 hM1 hC hCk hout hin hy.2
    -- the truncated field `1_{A_t} V`
    have hVt : MemLp ((A t).indicator (V : Space × ℝ → Space)) 2 μ :=
      (Lp.memLp V).indicator (hAm t)
    set Vt : PhysL2 ε c := hVt.toLp _ with hVtdef
    have hVtae : (Vt : Space × ℝ → Space) =ᵐ[μ] (A t).indicator V := hVt.coeFn_toLp
    have h2 : ⟪V, g⟫_ℝ = ⟪Vt, g⟫_ℝ := by
      rw [L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hVtae, hbd] with y e1 e2
      rw [e1]
      by_cases hy : y ∈ A t
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy] at e2 ⊢
        have : g y = 0 := by
          have := le_antisymm e2 (sq_nonneg _)
          rwa [sq_eq_zero_iff, norm_eq_zero] at this
        rw [this, inner_zero_right, inner_zero_right]
    have h3 : ⟪Vt, Vt⟫_ℝ = ∫ y in A t, ‖V y‖ ^ 2 ∂μ := by
      rw [L2.inner_def, ← integral_indicator (hAm t)]
      refine integral_congr_ae ?_
      filter_upwards [hVtae] with y e1
      rw [e1, real_inner_self_eq_norm_sq]
      by_cases hy : y ∈ A t
      · rw [indicator_of_mem hy, indicator_of_mem hy]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, norm_zero]
        norm_num
    have h4 : ⟪g, g⟫_ℝ ≤ Q := by
      rw [L2.inner_def]
      have hint : Integrable ((A t).indicator
          (fun _ => 2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹)) μ :=
        (integrable_indicator_iff (hAm t)).2 (integrableOn_const (hAfin t ht.le))
      calc ∫ y, ⟪g y, g y⟫_ℝ ∂μ
          ≤ ∫ y, (A t).indicator (fun _ => 2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹) y ∂μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun y => ?_) hint ?_
            · exact real_inner_self_nonneg
            · filter_upwards [hbd] with y e
              rw [real_inner_self_eq_norm_sq]
              exact e
        _ = μ.real (A t) * (2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹) := by
            rw [integral_indicator_const _ (hAm t), smul_eq_mul]
        _ ≤ (16 * t * R * (2 * ε * c)) * (2 * M1 ^ 2 + 16 * M0 ^ 2 * C ^ 2 * t⁻¹) := by
            gcongr
            rw [measureReal_def]
            exact ENNReal.toReal_le_of_le_ofReal
              (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.le) hR) hP)
              (measure_cutRegion_le ht.le hR)
        _ = 16 * R * (2 * ε * c) * (2 * M1 ^ 2 * t + 16 * M0 ^ 2 * C ^ 2) := by
            field_simp
        _ ≤ Q := by
            rw [hQ]
            have hm : M1 ^ 2 * t ≤ M1 ^ 2 := mul_le_of_le_one_right (sq_nonneg M1) ht1
            exact mul_le_mul_of_nonneg_left (by linarith)
              (mul_nonneg (mul_nonneg (by norm_num) hR) hP)
    have h5 := real_inner_mul_inner_self_le Vt g
    rw [h1, h2, sq, ← h3]
    calc ⟪Vt, g⟫_ℝ * ⟪Vt, g⟫_ℝ ≤ ⟪Vt, Vt⟫_ℝ * ⟪g, g⟫_ℝ := h5
      _ ≤ ⟪Vt, Vt⟫_ℝ * Q := mul_le_mul_of_nonneg_left h4 real_inner_self_nonneg
  -- the truncated energy tends to zero
  set tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with htn
  have htn0 : ∀ n, 0 < tn n := fun n => by positivity
  have htn1 : ∀ n, tn n ≤ 1 := fun n => by
    rw [htn]
    exact (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
  have htlim : Tendsto tn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmeas : Tendsto (fun n => μ (A (tn n))) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => ENNReal.ofReal (16 * tn n * R * (2 * ε * c))) atTop (𝓝 0) := by
      have : Tendsto (fun n => 16 * tn n * R * (2 * ε * c)) atTop (𝓝 0) := by
        have := ((htlim.const_mul 16).mul_const R).mul_const (2 * ε * c)
        simpa using this
      simpa using ENNReal.tendsto_ofReal this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => zero_le) fun n => measure_cutRegion_le (htn0 n).le hR
  have hVint : Integrable (fun y => ‖V y‖ ^ 2) μ := by
    have := L2.integrable_inner (𝕜 := ℝ) V V
    refine this.congr (ae_of_all _ fun y => ?_)
    exact real_inner_self_eq_norm_sq (V y)
  have hI : Tendsto (fun n => ∫ y in A (tn n), ‖V y‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    hVint.tendsto_setIntegral_nhds_zero hmeas
  have hlim : Tendsto (fun n => (∫ y in A (tn n), ‖V y‖ ^ 2 ∂μ) * Q) atTop (𝓝 0) := by
    simpa using hI.mul_const Q
  have hsq : ⟪V, physGrad ε c φ⟫_ℝ ^ 2 ≤ 0 :=
    ge_of_tendsto' hlim fun n => hmain (tn n) (htn0 n) (htn1 n)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hsq (sq_nonneg _))

end UnforcedLeray.B0226
