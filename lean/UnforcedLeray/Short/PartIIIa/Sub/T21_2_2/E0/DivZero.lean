import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP

/-!
# `PartIII-a:T21/2/2/2/8`: the divergence of a periodic field has zero cell integral

Source: `the November 2 reference manuscript`, lines 2945-2957 and 3060-3062.
Cutoff in `y₂` (`cutF`, `cutD`), slice FTC in `y₁` for the periodic `F₀`, FTC in `y₂` for
`cutF * F₁`, and dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.Short.IIb.TransportIBP

namespace UnforcedLeray.Short.IIIa.E0

theorem cutD_eq_zero_of_lt {R η : ℝ} (hR : 0 < R) (h : 2 * R < |η|) : cutD R η = 0 := by
  have h0 : HasDerivAt (fun x : ℝ => (0 : ℝ)) 0 η := hasDerivAt_const η 0
  have hev : (fun x : ℝ => cutF R x) =ᶠ[𝓝 η] fun _ => (0 : ℝ) := by
    have : IsOpen {x : ℝ | 2 * R < |x|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [this.mem_nhds h] with x hx
    exact cutF_eq_zero hR hx.le
  exact (hasDerivAt_cutF R η).unique (h0.congr_of_eventuallyEq hev)

theorem integrableOn_cell_of_cont {d R : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ y : ℝ × ℝ, 2 * R < |y.2| → f y = 0) :
    IntegrableOn f (UnforcedLeray.Cyl.cell d) := by
  set K : Set (ℝ × ℝ) := Icc (-d / 2) (d / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hKdef
  have hK : IntegrableOn f K := hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h1 : IntegrableOn f (UnforcedLeray.Cyl.cell d ∩ K) := hK.mono_set inter_subset_right
  have hm : MeasurableSet (UnforcedLeray.Cyl.cell d \ K) :=
    (measurableSet_Ico.prod MeasurableSet.univ).diff (measurableSet_Icc.prod measurableSet_Icc)
  have h2 : IntegrableOn f (UnforcedLeray.Cyl.cell d \ K) := by
    refine (integrableOn_zero (μ := volume)).congr_fun (fun y hy => ?_) hm
    obtain ⟨hyc, hyK⟩ := hy
    have h1' : y.1 ∈ Icc (-d / 2) (d / 2) := Ico_subset_Icc_self hyc.1
    have : y.2 ∉ Icc (-(2 * R)) (2 * R) := fun h => hyK ⟨h1', h⟩
    have h3 : 2 * R < |y.2| := by
      by_contra hc
      exact this (abs_le.1 (not_lt.1 hc))
    exact (h0 y h3).symm
  have := h1.union h2
  rwa [inter_union_sdiff] at this

theorem cellDivZero (d : ℝ) (hd : 0 < d) (F₀ F₁ : ℝ × ℝ → ℝ) (h₀ : ContDiff ℝ 1 F₀)
    (h₁ : ContDiff ℝ 1 F₁) (hp₀ : ∀ y : ℝ × ℝ, F₀ (y.1 + d, y.2) = F₀ y)
    (hi₁ : MeasureTheory.IntegrableOn F₁ (UnforcedLeray.B0579.cell d))
    (hdiv : MeasureTheory.IntegrableOn
      (fun y => UnforcedLeray.B0579.pd 0 F₀ y + UnforcedLeray.B0579.pd 1 F₁ y)
      (UnforcedLeray.B0579.cell d)) :
    ∫ y in UnforcedLeray.B0579.cell d,
      (UnforcedLeray.B0579.pd 0 F₀ y + UnforcedLeray.B0579.pd 1 F₁ y) = 0 := by
  have hcell : UnforcedLeray.B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  rw [hcell] at hi₁ hdiv ⊢
  have hd0 : Differentiable ℝ F₀ := h₀.differentiable one_ne_zero
  have hd1 : Differentiable ℝ F₁ := h₁.differentiable one_ne_zero
  have hcF : ∀ R : ℝ, Differentiable ℝ fun y : ℝ × ℝ => cutF R y.2 := fun R =>
    ((cutF_contDiff R).differentiable (by simp)).comp differentiable_snd
  have hcFc : ∀ R : ℝ, Continuous fun y : ℝ × ℝ => cutF R y.2 := fun R =>
    (cutF_contDiff R).continuous.comp continuous_snd
  have hcDc : ∀ R : ℝ, Continuous fun y : ℝ × ℝ => cutD R y.2 := fun R =>
    (continuous_cutD R).comp continuous_snd
  have hp0c := continuous_pd h₀ 0
  have hp1c := continuous_pd h₁ 1
  have hF1c := h₁.continuous
  -- the two identities for fixed R > 0
  have key0 : ∀ R : ℝ, 0 < R →
      ∫ y in UnforcedLeray.Cyl.cell d, UnforcedLeray.B0579.pd 0 F₀ y * cutF R y.2 = 0 := by
    intro R hR
    have hper : UnforcedLeray.Cyl.IsPeriodic d (fun y : ℝ × ℝ => F₀ y * cutF R y.2) :=
      fun z => by
        show F₀ _ * cutF R _ = F₀ z * cutF R z.2
        rw [hp₀ z]
    refine UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hd
      (F := fun y : ℝ × ℝ => F₀ y * cutF R y.2)
      (F' := fun y => UnforcedLeray.B0579.pd 0 F₀ y * cutF R y.2) hper ?_ ?_
    · intro q η
      have hdp : Differentiable ℝ (fun y : ℝ × ℝ => F₀ y * cutF R y.2) := hd0.mul (hcF R)
      have := UnforcedLeray.Cyl.hasDerivAt_sliceQ hdp q η
      rwa [partialQ_cut hd0 R (q, η)] at this
    · exact integrableOn_cell_of_cont (R := R) (hp0c.mul (hcFc R)) (fun y hy => by
        simp [cutF_eq_zero hR hy.le])
  have key1 : ∀ R : ℝ, 0 < R →
      ∫ y in UnforcedLeray.Cyl.cell d, UnforcedLeray.B0579.pd 1 F₁ y * cutF R y.2 =
        -∫ y in UnforcedLeray.Cyl.cell d, F₁ y * cutD R y.2 := by
    intro R hR
    have iA : IntegrableOn (fun y : ℝ × ℝ => UnforcedLeray.B0579.pd 1 F₁ y * cutF R y.2)
        (UnforcedLeray.Cyl.cell d) :=
      integrableOn_cell_of_cont (R := R) (hp1c.mul (hcFc R)) (fun y hy => by
        simp [cutF_eq_zero hR hy.le])
    have iB : IntegrableOn (fun y : ℝ × ℝ => F₁ y * cutD R y.2) (UnforcedLeray.Cyl.cell d) :=
      integrableOn_cell_of_cont (R := R) (hF1c.mul (hcDc R)) (fun y hy => by
        simp [cutD_eq_zero_of_lt hR hy])
    have iF : IntegrableOn (fun y : ℝ × ℝ => F₁ y * cutF R y.2) (UnforcedLeray.Cyl.cell d) :=
      integrableOn_cell_of_cont (R := R) (hF1c.mul (hcFc R)) (fun y hy => by
        simp [cutF_eq_zero hR hy.le])
    have h := UnforcedLeray.Cyl.integral_cell_deriv_eta (c := d)
      (F := fun y : ℝ × ℝ => F₁ y * cutF R y.2)
      (F' := fun y => UnforcedLeray.B0579.pd 1 F₁ y * cutF R y.2 + F₁ y * cutD R y.2)
      (fun q η => by
        have hdp : Differentiable ℝ (fun y : ℝ × ℝ => F₁ y * cutF R y.2) := hd1.mul (hcF R)
        have := UnforcedLeray.Cyl.hasDerivAt_sliceEta hdp q η
        rwa [show UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => F₁ y * cutF R y.2) (q, η) =
          UnforcedLeray.B0579.pd 1 F₁ (q, η) * cutF R η + F₁ (q, η) * cutD R η from
          partialEta_cut hd1 R (q, η)] at this)
      iF (iA.add iB)
    rw [integral_add iA iB] at h
    exact eq_neg_of_add_eq_zero_left h
  -- dominated convergence
  have hS : ∀ n : ℕ, ∫ y in UnforcedLeray.Cyl.cell d,
      (UnforcedLeray.B0579.pd 0 F₀ y + UnforcedLeray.B0579.pd 1 F₁ y) * cutF ((n : ℝ) + 1) y.2
        = -∫ y in UnforcedLeray.Cyl.cell d, F₁ y * cutD ((n : ℝ) + 1) y.2 := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have iA : IntegrableOn (fun y : ℝ × ℝ => UnforcedLeray.B0579.pd 0 F₀ y *
        cutF ((n : ℝ) + 1) y.2) (UnforcedLeray.Cyl.cell d) :=
      integrableOn_cell_of_cont (R := (n : ℝ) + 1) (hp0c.mul (hcFc _)) (fun y hy => by
        simp [cutF_eq_zero hR hy.le])
    have iB : IntegrableOn (fun y : ℝ × ℝ => UnforcedLeray.B0579.pd 1 F₁ y *
        cutF ((n : ℝ) + 1) y.2) (UnforcedLeray.Cyl.cell d) :=
      integrableOn_cell_of_cont (R := (n : ℝ) + 1) (hp1c.mul (hcFc _)) (fun y hy => by
        simp [cutF_eq_zero hR hy.le])
    simp only [add_mul]
    rw [integral_add iA iB, key0 _ hR, key1 _ hR, zero_add]
  have tDiv : Tendsto (fun n : ℕ => ∫ y in UnforcedLeray.Cyl.cell d,
      (UnforcedLeray.B0579.pd 0 F₀ y + UnforcedLeray.B0579.pd 1 F₁ y) *
        cutF ((n : ℝ) + 1) y.2) atTop
      (𝓝 (∫ y in UnforcedLeray.Cyl.cell d,
        (UnforcedLeray.B0579.pd 0 F₀ y + UnforcedLeray.B0579.pd 1 F₁ y))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖UnforcedLeray.B0579.pd 0 F₀ y + UnforcedLeray.B0579.pd 1 F₁ y‖)
      (Eventually.of_forall fun n => ((hp0c.add hp1c).mul (hcFc _)).aestronglyMeasurable)
      (Eventually.of_forall fun n => ae_of_all _ fun y => ?_) hdiv.norm
      (ae_of_all _ fun y => ?_)
    · rw [norm_mul, Real.norm_of_nonneg (cutF_nonneg _ _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (cutF_le_one _ _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (⌈|y.2|⌉₊)] with n hn
      have h1 : (⌈|y.2|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : |y.2| ≤ (n : ℝ) + 1 := by
        have := Nat.le_ceil |y.2|
        linarith
      rw [cutF_eq_one (by positivity) h2, mul_one]
  obtain ⟨K, hK0, hK⟩ := exists_cutD_bound
  have tZ : Tendsto (fun n : ℕ => ∫ y in UnforcedLeray.Cyl.cell d,
      F₁ y * cutD ((n : ℝ) + 1) y.2) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => (K * ∫ y in UnforcedLeray.Cyl.cell d, ‖F₁ y‖) *
        (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (K * ∫ y in UnforcedLeray.Cyl.cell d, ‖F₁ y‖)
    refine squeeze_zero_norm (fun n => ?_) hb
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc ‖∫ y in UnforcedLeray.Cyl.cell d, F₁ y * cutD ((n : ℝ) + 1) y.2‖
        ≤ ∫ y in UnforcedLeray.Cyl.cell d, ‖F₁ y‖ * (K * (1 / ((n : ℝ) + 1))) := by
          refine norm_integral_le_of_norm_le (hi₁.norm.mul_const _) (ae_of_all _ fun y => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hK _ _ hR) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; ring
  have := tendsto_nhds_unique (tDiv.congr hS) tZ.neg
  simpa using this

end UnforcedLeray.Short.IIIa.E0
