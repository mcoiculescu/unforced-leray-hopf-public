import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7

/-!
# `PartII-b:T13/1/5/5/7/2` leaf: approximate identity for nice functions (`MollNice`)

Source: `the November 2 reference manuscript` lines 1932-1935.
For a continuous, `q`-periodic, bounded `g` vanishing for `|s|` or `|η|` large, the mollified
`g ⋆ ρ_n` converges to `g` in `L^r(cylMeas c)`: pointwise convergence from continuity of `g`
(Mathlib `convolution_tendsto_right`), a uniform bound, vanishing outside a box of finite
`cylMeas`, and dominated convergence.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The box `[-K,K] × (ℝ × [-K,K])` in `Coord` (the `q`-direction is unbounded). -/
def niceBox (K : ℝ) : Set Coord := Icc (-K) K ×ˢ (univ ×ˢ Icc (-K) K)

theorem mem_niceBox (K : ℝ) (x : Coord) :
    x ∈ niceBox K ↔ |x.1| ≤ K ∧ |x.2.2| ≤ K := by
  simp only [niceBox, mem_prod, mem_univ, true_and, mem_Icc, abs_le]

theorem measurableSet_niceBox (K : ℝ) : MeasurableSet (niceBox K) :=
  measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)

/-- `cylMeas c` of the box is finite (the `q`-direction is cut by the cell `Ico (-c/2) (c/2)`). -/
theorem nice_cylMeas_box_ne_top (c K : ℝ) : cylMeas c (niceBox K) ≠ ⊤ := by
  have hT : MeasurableSet ((univ : Set ℝ) ×ˢ Icc (-K) K) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hsub : ((univ : Set ℝ) ×ˢ Icc (-K) K) ∩ UnforcedLeray.Cyl.cell c ⊆
      Icc (-c / 2) (c / 2) ×ˢ Icc (-K) K := by
    rintro ⟨q, η⟩ ⟨⟨_, h2⟩, h3, _⟩
    exact ⟨⟨h3.1, h3.2.le⟩, h2⟩
  have hfin : (volume : Measure (ℝ × ℝ)) (Icc (-c / 2) (c / 2) ×ˢ Icc (-K) K) ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfin2 : (volume : Measure (ℝ × ℝ))
      (((univ : Set ℝ) ×ˢ Icc (-K) K) ∩ UnforcedLeray.Cyl.cell c) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono hsub)
  have hA : (volume : Measure ℝ) (Icc (-K) K) ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  rw [niceBox, cylMeas, Measure.prod_prod, UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hT]
  exact ENNReal.mul_ne_top hA (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2)

open scoped Convolution

/-- Convolution with a kernel in the form used by `MollNice`, as a Mathlib convolution. -/
theorem nice_conv_eq (κ : Coord → ℝ) (g : Coord → ℂ) (x : Coord) :
    convK κ g x = (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  rw [convolution_lsmul]
  unfold convK
  have h := integral_sub_left_eq_self (μ := (volume : Measure Coord))
    (fun t : Coord => (κ t : ℂ) * g (x - t)) x
  simp only [sub_sub_cancel] at h
  simp only [Complex.real_smul]
  rw [← h]
  congr 1
  funext y
  ring

theorem mollNice_proof_aux_continuous (κ : Coord → ℝ) (hκ : IsKer κ) (g : Coord → ℂ)
    (hgc : Continuous g) : Continuous (convK κ g) := by
  have : convK κ g = (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := funext fun x => nice_conv_eq κ g x
  rw [this]
  exact hκ.2.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ.1.continuous
    hgc.locallyIntegrable

theorem mollApprox_nice_proof : UnforcedLeray.Short.IIb.MollNice := by
  intro c r hc hr ρ hρ hρn g hgc _hgp B hB M hM
  have hr0 : (0 : ℝ) < r := by linarith
  -- support radius of the mollifier
  obtain ⟨R, hRnn, hsupp⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ w : Coord, ρ w ≠ 0 → ‖w‖ ≤ R := by
    obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1
      hρ.1.2.isCompact.isBounded
    refine ⟨|R0|, abs_nonneg _, fun w hw => ?_⟩
    have h1 := hR0 (subset_tsupport ρ (Function.mem_support.2 hw))
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    exact h1.trans (le_abs_self R0)
  have hsupN : ∀ (n : ℕ) (z : Coord), molN ρ n z ≠ 0 → ((n : ℝ) + 1) * ‖z‖ ≤ R := by
    intro n z hz
    have h1 : ρ (((n : ℝ) + 1) • z) ≠ 0 := by
      intro h
      apply hz
      simp only [molN, h, mul_zero]
    have h2 := hsupp _ h1
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h2
    exact h2
  have hnorm_le : ∀ (n : ℕ) (z : Coord), molN ρ n z ≠ 0 → ‖z‖ ≤ R := by
    intro n z hz
    have h := hsupN n z hz
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (norm_nonneg z)]
  have hc1 : ∀ z : Coord, |z.1| ≤ ‖z‖ := fun z => by
    rw [← Real.norm_eq_abs]; exact norm_fst_le z
  have hc2 : ∀ z : Coord, |z.2.2| ≤ ‖z‖ := fun z => by
    rw [← Real.norm_eq_abs]; exact (norm_snd_le z.2).trans (norm_snd_le z)
  -- values of `g` outside the box
  have hgzero : ∀ y : Coord, M + R < |y.1| ∨ M + R < |y.2.2| → g y = 0 := by
    intro y hy
    apply hM y
    rcases hy with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  -- convolution vanishes outside the box
  have hconv_zero : ∀ (n : ℕ) (x : Coord), (M + R < |x.1| ∨ M + R < |x.2.2|) →
      convK (molN ρ n) g x = 0 := by
    intro n x hx
    unfold convK
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    by_cases hk : molN ρ n (x - y) = 0
    · simp [hk]
    · have hn := hnorm_le n (x - y) hk
      have hyg : g y = 0 := by
        apply hM y
        rcases hx with hx | hx
        · left
          have h3 := abs_sub_abs_le_abs_sub x.1 y.1
          have h4 : |x.1 - y.1| ≤ R := (hc1 (x - y)).trans hn
          linarith
        · right
          have h3 := abs_sub_abs_le_abs_sub x.2.2 y.2.2
          have h4 : |x.2.2 - y.2.2| ≤ R := (hc2 (x - y)).trans hn
          linarith
      simp [hyg]
  -- pointwise convergence of the mollified function
  have hlim_conv : ∀ x : Coord, Tendsto (fun n : ℕ => convK (molN ρ n) g x) atTop (𝓝 (g x)) := by
    intro x
    have hφ : Tendsto (fun n : ℕ => Function.support (molN ρ n)) atTop (𝓝 (0 : Coord)).smallSets := by
      rw [tendsto_smallSets_iff]
      intro t ht
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
      obtain ⟨N, hN⟩ := exists_nat_gt (R / ε)
      rw [eventually_atTop]
      refine ⟨N, fun n hn z hz => hball ?_⟩
      rw [mem_ball_zero_iff]
      by_contra hcon
      push_neg at hcon
      have h1 := hsupN n z (Function.mem_support.1 hz)
      have h2 : ((n : ℝ) + 1) * ε ≤ ((n : ℝ) + 1) * ‖z‖ :=
        mul_le_mul_of_nonneg_left hcon (by positivity)
      have hN' : R < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h4 : (N : ℝ) * ε ≤ ((n : ℝ) + 1) * ε := by nlinarith
      linarith
    have hnφ : ∀ᶠ n : ℕ in atTop, ∀ z : Coord, 0 ≤ molN ρ n z :=
      Eventually.of_forall fun n z => (hρn n).2.1 z
    have hiφ : ∀ᶠ n : ℕ in atTop, ∫ z : Coord, molN ρ n z = 1 :=
      Eventually.of_forall fun n => (hρn n).2.2
    have hmg : ∀ᶠ _n : ℕ in atTop, AEStronglyMeasurable g volume :=
      Eventually.of_forall fun _ => hgc.aestronglyMeasurable
    have hcg : Tendsto (Function.uncurry fun (_ : ℕ) (z : Coord) => g z) (atTop ×ˢ 𝓝 x) (𝓝 (g x)) :=
      (hgc.tendsto x).comp tendsto_snd
    have key := convolution_tendsto_right (μ := (volume : Measure Coord))
      (g := fun _ => g) (l := atTop) (x₀ := x) (z₀ := g x)
      (φ := fun n => molN ρ n) (k := fun _ => x) hnφ hiφ hφ hmg hcg tendsto_const_nhds
    exact (tendsto_congr fun n => nice_conv_eq (molN ρ n) g x).2 key
  -- uniform bound
  have hbound_conv : ∀ (n : ℕ) (x : Coord), ‖convK (molN ρ n) g x‖ ≤ B := by
    intro n x
    have hk : Integrable (molN ρ n) volume :=
      (hρn n).1.1.continuous.integrable_of_hasCompactSupport (hρn n).1.2
    have hint : Integrable (fun y : Coord => B * molN ρ n (x - y)) volume :=
      (hk.comp_sub_left x).const_mul B
    unfold convK
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)).trans
      (le_of_eq ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ((hρn n).2.1 (x - y))]
      exact mul_le_mul_of_nonneg_right (hB y) ((hρn n).2.1 (x - y))
    · rw [integral_const_mul, integral_sub_left_eq_self (molN ρ n) volume x, (hρn n).2.2, mul_one]
  have hbound_F : ∀ (n : ℕ) (x : Coord), ‖convK (molN ρ n) g x - g x‖ ≤ 2 * B := by
    intro n x
    have := norm_sub_le (convK (molN ρ n) g x) (g x)
    linarith [hbound_conv n x, hB x]
  -- measurability
  have hF_meas : ∀ n : ℕ, Measurable (fun x : Coord => ‖convK (molN ρ n) g x - g x‖ₑ ^ r) := by
    intro n
    have hcont : Continuous (fun x : Coord => convK (molN ρ n) g x - g x) :=
      (mollNice_proof_aux_continuous (molN ρ n) (hρn n).1 g hgc).sub hgc
    exact (hcont.measurable.enorm).pow_const r
  -- pointwise limit of the integrands
  have h_lim : ∀ x : Coord, Tendsto (fun n : ℕ => ‖convK (molN ρ n) g x - g x‖ₑ ^ r) atTop
      (𝓝 0) := by
    intro x
    have h1 : Tendsto (fun n : ℕ => convK (molN ρ n) g x - g x) atTop (𝓝 0) := by
      have := (hlim_conv x).sub_const (g x)
      simpa using this
    have h2 : Tendsto (fun n : ℕ => ‖convK (molN ρ n) g x - g x‖ₑ) atTop (𝓝 ‖(0 : ℂ)‖ₑ) :=
      (continuous_enorm.tendsto 0).comp h1
    rw [enorm_zero] at h2
    have h3 := ((ENNReal.continuous_rpow_const (y := r)).tendsto 0).comp h2
    rw [ENNReal.zero_rpow_of_pos hr0] at h3
    exact h3
  -- domination by an indicator of the box
  have hbound_pt : ∀ (n : ℕ) (x : Coord), ‖convK (molN ρ n) g x - g x‖ₑ ^ r ≤
      (niceBox (M + R)).indicator (fun _ => (ENNReal.ofReal (2 * B)) ^ r) x := by
    intro n x
    by_cases hx : x ∈ niceBox (M + R)
    · rw [Set.indicator_of_mem hx]
      have hx2 := (mem_niceBox (M + R) x).1 hx
      have hle : ‖convK (molN ρ n) g x - g x‖ₑ ≤ ENNReal.ofReal (2 * B) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound_F n x)
      exact ENNReal.rpow_le_rpow hle hr0.le
    · rw [Set.indicator_of_notMem hx]
      have hx' : M + R < |x.1| ∨ M + R < |x.2.2| := by
        by_contra h
        push_neg at h
        exact hx ((mem_niceBox (M + R) x).2 h)
      have hF0 : convK (molN ρ n) g x - g x = 0 := by
        simp [hconv_zero n x hx', hgzero x hx']
      rw [hF0, enorm_zero, ENNReal.zero_rpow_of_pos hr0]
  have hfin : ∫⁻ x, (niceBox (M + R)).indicator (fun _ => (ENNReal.ofReal (2 * B)) ^ r) x
      ∂(cylMeas c) ≠ ⊤ := by
    rw [lintegral_indicator_const (measurableSet_niceBox _)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top)
      (nice_cylMeas_box_ne_top c (M + R))
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := cylMeas c)
    (F := fun n x => ‖convK (molN ρ n) g x - g x‖ₑ ^ r) (f := fun _ => 0)
    (fun x => (niceBox (M + R)).indicator (fun _ => (ENNReal.ofReal (2 * B)) ^ r) x)
    hF_meas (fun n => Eventually.of_forall (hbound_pt n)) hfin
    (Eventually.of_forall h_lim)
  simp only [lintegral_zero] at hdct
  have hfinal : Tendsto (fun n : ℕ => (∫⁻ x, ‖convK (molN ρ n) g x - g x‖ₑ ^ r ∂(cylMeas c)) ^
      (1 / r)) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp hdct
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at h
    exact h
  refine hfinal.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]

end UnforcedLeray.Short.IIb
