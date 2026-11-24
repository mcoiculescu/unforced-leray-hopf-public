import UnforcedLeray.Short.PartI.Sub.PartI_C10

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0123

/-- The graph weight `1 + (1 + ℓ)^j` of the Hermite coefficient `ℓ`. -/
def gwt (j ℓ : ℕ) : ℝ := 1 + (1 + (ℓ : ℝ)) ^ j

theorem gwt_nonneg (j ℓ : ℕ) : 0 ≤ gwt j ℓ := by unfold gwt; positivity

/-- The weighted coefficients of the first `N` modes, as a continuous map into `ℂ^N`. -/
def truncMap (j N : ℕ) : B0010.XG →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  ∑ i : Fin N, ((Real.sqrt (gwt j i) : ℝ) : ℂ) •
    ((innerSL ℂ (B0094.oscBasis i)).smulRight (EuclideanSpace.single i (1 : ℂ)))

theorem truncMap_apply_coord (j N : ℕ) (x : B0010.XG) (k : Fin N) :
    truncMap j N x k = ((Real.sqrt (gwt j k) : ℝ) : ℂ) * ⟪B0094.oscBasis k, x⟫_ℂ := by
  unfold truncMap
  simp [ContinuousLinearMap.smulRight_apply, Pi.single_apply, mul_ite, innerSL_apply_apply]

theorem norm_truncMap_sq (j N : ℕ) (x : B0010.XG) :
    ‖truncMap j N x‖ ^ 2 = ∑ n ∈ Finset.range N, gwt j n * ‖⟪B0094.oscBasis n, x⟫_ℂ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Fin.sum_univ_eq_sum_range
    (fun n => gwt j n * ‖⟪B0094.oscBasis n, x⟫_ℂ‖ ^ 2) N]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [truncMap_apply_coord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (gwt_nonneg j k)]

theorem summable_gwt (j : ℕ) (f : B0010.XG) (hf : f ∈ B0121.XGj j) :
    Summable fun n : ℕ => gwt j n * ‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 := by
  have h1 := (B0121.mem_XGj_iff j f).1 hf
  have h2 := B0121.summable_coef_sq f
  refine (h2.add h1).congr fun n => ?_
  unfold gwt
  ring

theorem partial_le_graphNormSq (j N : ℕ) (f : B0010.XG) (h : f ∈ B0121.XGj j) :
    ∑ n ∈ Finset.range N, gwt j n * ‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 ≤
      B0121.graphNormSq j ⟨f, h⟩ := by
  rw [B0121.graphNormSq_eq]
  exact (summable_gwt j f h).sum_le_tsum _ (fun n _ => by
    have := gwt_nonneg j n
    positivity)

/-- Minkowski for one truncation: the first `N` weighted coefficients of `∫F`. -/
theorem partial_integral_le (j N : ℕ) {a b : ℝ} (hab : a ≤ b) (F : ℝ → B0010.XG)
    (g : ℝ → ℝ) (hF : IntervalIntegrable F volume a b) (hg : IntervalIntegrable g volume a b)
    (hbd : ∀ v ∈ Ioc a b, 0 ≤ g v ∧ ∃ h : F v ∈ (B0121.fracPow j).domain,
        B0121.graphNormSq j ⟨F v, h⟩ ≤ (g v) ^ 2) :
    ∑ n ∈ Finset.range N, gwt j n * ‖⟪B0094.oscBasis n, ∫ v in a..b, F v⟫_ℂ‖ ^ 2 ≤
      (∫ v in a..b, g v) ^ 2 := by
  have hT := (truncMap j N).intervalIntegral_comp_comm hF
  have hnorm : ‖truncMap j N (∫ v in a..b, F v)‖ ≤ ∫ v in a..b, g v := by
    rw [← hT]
    refine intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun v hv => ?_) hg
    obtain ⟨hg0, h, hh⟩ := hbd v hv
    have hsq : ‖truncMap j N (F v)‖ ^ 2 ≤ (g v) ^ 2 := by
      rw [norm_truncMap_sq]
      exact (partial_le_graphNormSq j N (F v) h).trans hh
    nlinarith [norm_nonneg (truncMap j N (F v))]
  rw [← norm_truncMap_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **Minkowski inequality in the graph norm of `X_{G,j}`** (used for the Duhamel integral). -/
theorem graphIntegralBound (j : ℕ) : GraphIntegralBound j := by
  intro a b hab F g hF hg hbd
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      gwt j n * ‖⟪B0094.oscBasis n, ∫ v in a..b, F v⟫_ℂ‖ ^ 2 ≤ (∫ v in a..b, g v) ^ 2 :=
    fun N => partial_integral_le j N hab F g hF hg hbd
  have hsum : Summable fun n : ℕ => gwt j n * ‖⟪B0094.oscBasis n, ∫ v in a..b, F v⟫_ℂ‖ ^ 2 :=
    summable_of_sum_range_le (fun n => mul_nonneg (gwt_nonneg j n) (by positivity)) hpart
  have hmem : (∫ v in a..b, F v) ∈ B0121.XGj j := by
    rw [B0121.mem_XGj_iff]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
    have h1 : (1 + (n : ℝ)) ^ j ≤ gwt j n := by
      unfold gwt
      linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  refine ⟨hmem, ?_⟩
  rw [B0121.graphNormSq_eq]
  exact Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (gwt_nonneg j n) (by positivity)) hpart

end UnforcedLeray.Short.PartI
