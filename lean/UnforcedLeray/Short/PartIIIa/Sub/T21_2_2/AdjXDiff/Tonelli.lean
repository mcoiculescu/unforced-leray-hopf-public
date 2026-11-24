import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff.Cs

/-!
# `PartIII-a:T21/2/2`, helper: the averaged `L²` bound by Tonelli

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073.

For `G : ℝ → X → ℂ` jointly continuous on `uIcc r r' × X`, the `L²(μ)` norm of the average
`x ↦ (r' - r)⁻¹ ∫_r^{r'} G ρ x dρ` is at most the `L²(μ)` norm of `G` averaged over the ages
`ρ ∈ Ι r r'` (Minkowski in the `L²` form, via `norm_avg_sq` and Tonelli). In particular the bound
`eLpNorm_avg_le` gives the uniform estimate `≤ η` as soon as `‖G ρ‖_{L²(μ)} ≤ η` on `Ι r r'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- `eLpNorm f 2 μ ^ 2 = ∫⁻ ‖f‖ₑ²`. -/
theorem eLpNorm_two_sq_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The clamp of an age to `uIcc r r'`. -/
def clampI (r r' ρ : ℝ) : ℝ := max (min ρ (max r r')) (min r r')

theorem clampI_mem (r r' ρ : ℝ) : clampI r r' ρ ∈ uIcc r r' := by
  show min r r' ≤ clampI r r' ρ ∧ clampI r r' ρ ≤ max r r'
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) min_le_max⟩

theorem clampI_eq {r r' ρ : ℝ} (h : ρ ∈ uIcc r r') : clampI r r' ρ = ρ := by
  have h' : min r r' ≤ ρ ∧ ρ ≤ max r r' := h
  unfold clampI
  rw [min_eq_left h'.2, max_eq_left h'.1]

theorem ofReal_norm_eq_enorm_c (z : ℂ) : ENNReal.ofReal ‖z‖ = ‖z‖ₑ := ofReal_norm z

theorem clampI_cont (r r' : ℝ) : Continuous (clampI r r') := by
  unfold clampI
  fun_prop

/-- **Tonelli bound, globally continuous version.** -/
theorem tonelli_cont (μ : Measure (ℝ × ℝ)) [SFinite μ] (r r' : ℝ) (hne : r ≠ r')
    (G : ℝ → ℝ × ℝ → ℂ) (hG : Continuous (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2)) :
    ∫⁻ x, ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ := by
  have hpt : ∀ x, ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x‖ₑ ^ 2 ≤
      ∫⁻ ρ in Ι r r', ENNReal.ofReal |r' - r|⁻¹ * ‖G ρ x‖ₑ ^ 2 := by
    intro x
    have hc : Continuous (fun ρ => G ρ x) := hG.comp (continuous_id.prodMk continuous_const)
    have hn := norm_avg_sq r r' hne (fun ρ => G ρ x) hc.continuousOn
    have hfi : IntegrableOn (fun ρ => |r' - r|⁻¹ * ‖G ρ x‖ ^ 2) (Ι r r') := by
      have : ContinuousOn (fun ρ => |r' - r|⁻¹ * ‖G ρ x‖ ^ 2) (uIcc r r') :=
        continuousOn_const.mul ((hc.norm.pow 2).continuousOn)
      exact (this.integrableOn_uIcc).mono_set uIoc_subset_uIcc
    have hnn : 0 ≤ᵐ[volume.restrict (Ι r r')] fun ρ => |r' - r|⁻¹ * ‖G ρ x‖ ^ 2 :=
      ae_of_all _ fun ρ => by positivity
    have hint : ∀ ρ, ENNReal.ofReal |r' - r|⁻¹ * ‖G ρ x‖ₑ ^ 2 =
        ENNReal.ofReal (|r' - r|⁻¹ * ‖G ρ x‖ ^ 2) := by
      intro ρ
      rw [← ofReal_norm_eq_enorm_c, ← ENNReal.ofReal_pow (norm_nonneg _),
        ENNReal.ofReal_mul (by positivity)]
    simp_rw [hint]
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn]
    rw [← ofReal_norm_eq_enorm_c, ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x‖ ^ 2
        ≤ |r' - r|⁻¹ * ∫ ρ in Ι r r', ‖G ρ x‖ ^ 2 := hn
      _ = ∫ ρ in Ι r r', |r' - r|⁻¹ * ‖G ρ x‖ ^ 2 := (MeasureTheory.integral_const_mul _ _).symm
  have hGm : Measurable (fun q : (ℝ × ℝ) × ℝ => G q.2 q.1) :=
    hG.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hm : Measurable (Function.uncurry fun (x : ℝ × ℝ) (ρ : ℝ) =>
      ENNReal.ofReal |r' - r|⁻¹ * ‖G ρ x‖ₑ ^ 2) := by
    show Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal |r' - r|⁻¹ * ‖G q.2 q.1‖ₑ ^ 2)
    exact ((hGm.enorm).pow_const 2).const_mul _
  calc ∫⁻ x, ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ ρ in Ι r r', ENNReal.ofReal |r' - r|⁻¹ * ‖G ρ x‖ₑ ^ 2) ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ ρ in Ι r r', ∫⁻ x, ENNReal.ofReal |r' - r|⁻¹ * ‖G ρ x‖ₑ ^ 2 ∂μ :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ ρ in Ι r r', ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ := by
        apply lintegral_congr
        intro ρ
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Tonelli bound** under continuity on `uIcc r r' × univ` (the clamp of the age). -/
theorem tonelli_on (μ : Measure (ℝ × ℝ)) [SFinite μ] (r r' : ℝ) (hne : r ≠ r')
    (G : ℝ → ℝ × ℝ → ℂ) (hG : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) (uIcc r r' ×ˢ univ)) :
    ∫⁻ x, ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ := by
  have hGc : Continuous (fun p : ℝ × (ℝ × ℝ) => G (clampI r r' p.1) p.2) :=
    hG.comp_continuous (f := fun p : ℝ × (ℝ × ℝ) => (clampI r r' p.1, p.2))
      ((clampI_cont r r').comp continuous_fst |>.prodMk continuous_snd)
        (fun p => ⟨clampI_mem r r' p.1, mem_univ _⟩)
  have key := tonelli_cont μ r r' hne (fun ρ x => G (clampI r r' ρ) x) hGc
  have e1 : ∀ x, (∫ ρ in r..r', G ρ x) = ∫ ρ in r..r', G (clampI r r' ρ) x := fun x =>
    intervalIntegral.integral_congr fun ρ hρ => by
      show G ρ x = G (clampI r r' ρ) x
      rw [clampI_eq hρ]
  have e2 : ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ =
      ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G (clampI r r' ρ) x‖ₑ ^ 2 ∂μ := by
    apply setLIntegral_congr_fun measurableSet_uIoc
    intro ρ hρ
    dsimp only
    rw [clampI_eq (uIoc_subset_uIcc hρ)]
  calc ∫⁻ x, ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G (clampI r r' ρ) x‖ₑ ^ 2 ∂μ := by
        apply lintegral_congr
        intro x
        rw [e1 x]
    _ ≤ _ := key
    _ = _ := by rw [e2]

/-- **The averaged `L²` bound.** If `‖G ρ‖_{L²(μ)} ≤ η` for all ages `ρ ∈ Ι r r'`, then the
`L²(μ)` norm of `x ↦ (r' - r)⁻¹ ∫_r^{r'} G ρ x dρ` is at most `η`. -/
theorem eLpNorm_avg_le (μ : Measure (ℝ × ℝ)) [SFinite μ] (r r' : ℝ) (hne : r ≠ r')
    (G : ℝ → ℝ × ℝ → ℂ) (hG : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) (uIcc r r' ×ˢ univ))
    (η : ℝ≥0∞) (hη : ∀ ρ ∈ Ι r r', eLpNorm (G ρ) 2 μ ≤ η) :
    eLpNorm (fun x => ((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x) 2 μ ≤ η := by
  have h1 := tonelli_on μ r r' hne G hG
  have h2 : ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _ in Ι r r', η ^ 2 ∂volume := by
    apply setLIntegral_mono' measurableSet_uIoc
    intro ρ hρ
    rw [← eLpNorm_two_sq_eq]
    exact pow_le_pow_left₀ zero_le (hη ρ hρ) 2
  have hsub : |r' - r| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 hne.symm)
  have hc : ENNReal.ofReal |r' - r|⁻¹ * ENNReal.ofReal |r' - r| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hsub, ENNReal.ofReal_one]
  have h3 : ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ ≤ η ^ 2 := by
    calc ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ ρ in Ι r r', ∫⁻ x, ‖G ρ x‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal |r' - r|⁻¹ * ∫⁻ _ in Ι r r', η ^ 2 ∂volume :=
          mul_le_mul_of_nonneg_left h2 zero_le
      _ = ENNReal.ofReal |r' - r|⁻¹ * (η ^ 2 * ENNReal.ofReal |r' - r|) := by
          rw [setLIntegral_const, Real.volume_uIoc, mul_comm]
      _ = η ^ 2 * (ENNReal.ofReal |r' - r|⁻¹ * ENNReal.ofReal |r' - r|) := by ring
      _ = η ^ 2 := by rw [hc, mul_one]
  have hfin : eLpNorm (fun x => ((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ x) 2 μ ^ 2 ≤ η ^ 2 := by
    rw [eLpNorm_two_sq_eq]
    exact le_trans h1 h3
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hfin

end UnforcedLeray.Short.IIIa
