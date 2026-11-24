import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Compare
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.IBP

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: supports and uniform bounds

Source: SP 2962-2964 ("the transported support remains a fixed disk", cf. SP 2104-2110).

A profile `Φ(z, y)` vanishing for `|y| > R` has all its derivatives vanishing there; continuous
such functions are bounded on every slab `0 ≤ z ≤ Z` (`exists_bound_slab`). The comparison
function `cmp Φ ν s σ` and its age derivative vanish off the ball of radius `R √a(σ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

/-- `Φ(z, y) = 0` for `|y| > R` (Euclidean norm). -/
def SuppIn (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ∀ p : ℝ × (ℝ × ℝ), R ^ 2 < p.2.1 ^ 2 + p.2.2 ^ 2 → Φ p = 0

theorem isOpen_outside (R : ℝ) :
    IsOpen {p : ℝ × (ℝ × ℝ) | R ^ 2 < p.2.1 ^ 2 + p.2.2 ^ 2} :=
  isOpen_lt continuous_const (by fun_prop)

theorem eventuallyEq_zero_of_suppIn {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ)
    {p : ℝ × (ℝ × ℝ)} (hp : R ^ 2 < p.2.1 ^ 2 + p.2.2 ^ 2) : Φ =ᶠ[𝓝 p] fun _ => 0 :=
  Filter.eventually_of_mem ((isOpen_outside R).mem_nhds hp) fun q hq => h q hq

theorem fderiv_eq_zero_of_suppIn {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ)
    {p : ℝ × (ℝ × ℝ)} (hp : R ^ 2 < p.2.1 ^ 2 + p.2.2 ^ 2) : fderiv ℝ Φ p = 0 := by
  rw [(eventuallyEq_zero_of_suppIn h hp).fderiv_eq]
  exact fderiv_const_apply _

theorem suppIn_fderiv_apply {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ)
    (w : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ)) : SuppIn R (fun p => fderiv ℝ Φ p (w p)) := by
  intro p hp
  simp only [fderiv_eq_zero_of_suppIn h hp, ContinuousLinearMap.zero_apply]

theorem suppIn_dY {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ) (j : Fin 2) :
    SuppIn R (dY Φ j) :=
  suppIn_fderiv_apply h (fun _ => (0, B0579.dir j))

theorem suppIn_dYY {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ) (j : Fin 2) :
    SuppIn R (dYY Φ j) :=
  suppIn_fderiv_apply (suppIn_dY h j) (fun _ => (0, B0579.dir j))

theorem suppIn_dZ {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ) : SuppIn R (dZ Φ) :=
  suppIn_fderiv_apply h (fun _ => (1, 0))

theorem suppIn_bracketQ {R : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ} (h : SuppIn R Φ) :
    SuppIn R (bracketQ Φ) := by
  intro p hp
  have h1 := suppIn_fderiv_apply h (fun p => (0, p.2)) p hp
  simp only at h1
  simp only [bracketQ, h p hp, suppIn_dYY h 0 p hp, suppIn_dYY h 1 p hp, h1]
  ring

theorem sq_lt_of_norm_gt {R : ℝ} (hR : 0 ≤ R) {y : ℝ × ℝ} (hy : R < ‖y‖) :
    R ^ 2 < y.1 ^ 2 + y.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hy
  rcases le_total |y.1| |y.2| with h | h
  · rw [max_eq_right h] at hy
    have : R ^ 2 < |y.2| ^ 2 := by nlinarith
    rw [sq_abs] at this
    nlinarith [sq_nonneg y.1]
  · rw [max_eq_left h] at hy
    have : R ^ 2 < |y.1| ^ 2 := by nlinarith
    rw [sq_abs] at this
    nlinarith [sq_nonneg y.2]

/-- **Uniform bound on a slab** for a continuous function vanishing for `|y| > R`. -/
theorem exists_bound_slab {f : ℝ × (ℝ × ℝ) → ℝ} (hf : Continuous f) {R : ℝ} (hR : 0 ≤ R)
    (hs : SuppIn R f) (Z : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → p.1 ≤ Z → |f p| ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) Z ×ˢ Metric.closedBall (0 : ℝ × ℝ) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p hp0 hpZ => ?_⟩
  by_cases hp : ‖p.2‖ ≤ R
  · have hmem : p ∈ Icc (0 : ℝ) Z ×ˢ Metric.closedBall (0 : ℝ × ℝ) R :=
      ⟨⟨hp0, hpZ⟩, by rw [Metric.mem_closedBall, dist_zero_right]; exact hp⟩
    have := hC p hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [not_le] at hp
    rw [hs p (sq_lt_of_norm_gt hR hp), abs_zero]
    exact le_max_right _ _

/-! ## Clock facts -/

theorem clockA_mono {ν σ t : ℝ} (hν : 0 ≤ ν) (h : σ ≤ t) : clockA ν σ ≤ clockA ν t := by
  unfold clockA; nlinarith

theorem one_le_clockA' {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) : 1 ≤ clockA ν σ := by
  unfold clockA; nlinarith [mul_nonneg hν hσ]

theorem movingZ_sub_eq {ν s σ : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (hσ : 0 ≤ σ) :
    movingZ ν σ - movingZ ν s = (σ - s) / (clockA ν σ * clockA ν s) := by
  have ha := clockA_pos hν hσ
  have hb := clockA_pos hν hs
  unfold movingZ
  field_simp
  unfold clockA
  ring

theorem movingZ_mono {ν s σ : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (h : s ≤ σ) :
    movingZ ν s ≤ movingZ ν σ := by
  have := movingZ_sub_eq hν hs (hs.trans h)
  have hp : 0 ≤ (σ - s) / (clockA ν σ * clockA ν s) :=
    div_nonneg (by linarith) (mul_pos (clockA_pos hν (hs.trans h)) (clockA_pos hν hs)).le
  linarith

/-! ## The comparison function off the ball -/

theorem cpt_outside {ν s σ t R : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (hσt : σ ≤ t) (hR : 0 ≤ R)
    {x : ℝ × ℝ} (hx : x ∉ Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t))) :
    R ^ 2 < (cpt ν s σ x).2.1 ^ 2 + (cpt ν s σ x).2.2 ^ 2 := by
  apply sq_lt_of_norm_gt hR
  have ha := clockA_pos hν hσ
  have hsa := Real.sqrt_pos.2 ha
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  have hle : Real.sqrt (clockA ν σ) ≤ Real.sqrt (clockA ν t) :=
    Real.sqrt_le_sqrt (clockA_mono hν hσt)
  have h1 : R * Real.sqrt (clockA ν σ) < ‖x‖ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hR) hx
  simp only [cpt]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hsa]
  rw [lt_inv_mul_iff₀ hsa]
  linarith [mul_comm R (Real.sqrt (clockA ν σ))]

theorem cmp_outside {Φ : ℝ × (ℝ × ℝ) → ℝ} {R : ℝ} (hΦ : SuppIn R Φ) {ν s σ t : ℝ} (hν : 0 ≤ ν)
    (hσ : 0 ≤ σ) (hσt : σ ≤ t) (hR : 0 ≤ R) {x : ℝ × ℝ}
    (hx : x ∉ Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t))) :
    cmp Φ ν s σ x = 0 := by
  unfold cmp
  rw [hΦ _ (cpt_outside (s := s) hν hσ hσt hR hx), mul_zero]

theorem cmpDt_outside {Φ : ℝ × (ℝ × ℝ) → ℝ} {R : ℝ} (hΦ : SuppIn R Φ) {ν s σ t : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (hσt : σ ≤ t) (hR : 0 ≤ R) {x : ℝ × ℝ}
    (hx : x ∉ Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t))) :
    cmpDt Φ ν s σ x = 0 := by
  have hp := cpt_outside (s := s) hν hσ hσt hR hx
  unfold cmpDt dZ
  rw [hΦ _ hp, fderiv_eq_zero_of_suppIn hΦ hp]
  simp

theorem contDiff_cmp {Φ : ℝ × (ℝ × ℝ) → ℝ} {n : WithTop ℕ∞} (hΦ : ContDiff ℝ n Φ)
    (ν s σ : ℝ) : ContDiff ℝ n (cmp Φ ν s σ) := by
  unfold cmp cpt
  exact contDiff_const.mul (hΦ.comp (contDiff_const.prodMk (contDiff_const_smul _)))

theorem continuous_cpt (ν s σ : ℝ) : Continuous (cpt ν s σ) := by
  unfold cpt
  exact continuous_const.prodMk (continuous_const_smul _)

theorem continuous_cmpDt {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) (ν s σ : ℝ) :
    Continuous (cmpDt Φ ν s σ) := by
  have hc := continuous_cpt ν s σ
  have hD : Continuous (fun p => fderiv ℝ Φ p) := hΦ.continuous_fderiv (by norm_num)
  unfold cmpDt dZ
  exact ((continuous_const.mul (hΦ.continuous.comp hc)).add
    (continuous_const.mul ((hD.comp hc).clm_apply continuous_const))).sub
    (continuous_const.mul ((hD.comp hc).clm_apply
      (continuous_const.prodMk (continuous_snd.comp hc))))

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
