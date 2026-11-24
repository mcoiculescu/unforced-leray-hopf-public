import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.l2SqDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# `L2SqWeak`: weak convergence of difference quotients (source 341-348)

`weak_core`: if `h i → 0` pointwise along a countably generated filter and `∫ (h i)² ≤ C`, then
`∫ h i * g → 0` for every `g ∈ L²`.  Proof: truncate `g` to `gR = g · 1_{1/R ≤ |g| ≤ R}`
(`|gR| ≤ R g²`, so integrable; `|gR| ≤ R`); the remainder `g - gR` is small in `L²` (AM-GM), and
`|h| |gR| ≤ min(|h|, M) |gR| + (R/M) h²`, the first term tending to `0` by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.Short.PartI.L2SqDeriv.Weak

/-- The truncation `x ↦ x · 1_{1/R ≤ |x| ≤ R}`. -/
def psi (R : ℕ) (x : ℝ) : ℝ := if 1 / (R : ℝ) ≤ |x| ∧ |x| ≤ R then x else 0

lemma psi_measurable (R : ℕ) : Measurable (psi R) := by
  unfold psi
  refine Measurable.ite ?_ measurable_id measurable_const
  exact (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

lemma abs_psi_le_self (R : ℕ) (x : ℝ) : |psi R x| ≤ |x| := by
  unfold psi; split_ifs <;> simp

lemma abs_self_sub_psi_le (R : ℕ) (x : ℝ) : |x - psi R x| ≤ |x| := by
  unfold psi; split_ifs <;> simp

lemma abs_psi_le_R (R : ℕ) (x : ℝ) : |psi R x| ≤ R := by
  unfold psi; split_ifs with h
  · exact h.2
  · simp

lemma abs_psi_le_sq (R : ℕ) (x : ℝ) : |psi R x| ≤ R * x ^ 2 := by
  unfold psi; split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    by_cases hx : x = 0
    · simp [hx]
    · have hpos : 0 < |x| := abs_pos.mpr hx
      have hR : 0 < (R : ℝ) := lt_of_lt_of_le hpos h2
      have : 1 ≤ R * |x| := by
        rw [div_le_iff₀ hR] at h1; linarith
      calc |x| = |x| * 1 := by ring
        _ ≤ |x| * (R * |x|) := by gcongr
        _ = R * x ^ 2 := by rw [← sq_abs x]; ring
  · simp; positivity

lemma tendsto_sub_psi (x : ℝ) : Tendsto (fun R : ℕ => x - psi R x) atTop (𝓝 0) := by
  by_cases hx : x = 0
  · have : ∀ R : ℕ, x - psi R x = 0 := fun R => by
      subst hx; unfold psi; split_ifs <;> simp
    simp [this]
  · have hpos : 0 < |x| := abs_pos.mpr hx
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    refine ⟨⌈max |x| (1 / |x|)⌉₊, fun R hR => ?_⟩
    have hR' : max |x| (1 / |x|) ≤ R := (Nat.le_ceil _).trans (by exact_mod_cast hR)
    have h1 : |x| ≤ R := le_trans (le_max_left _ _) hR'
    have h2 : 1 / |x| ≤ R := le_trans (le_max_right _ _) hR'
    have hRpos : 0 < (R : ℝ) := lt_of_lt_of_le hpos h1
    have h3 : 1 / (R : ℝ) ≤ |x| := by
      rw [div_le_iff₀ hRpos]; rw [div_le_iff₀ hpos] at h2; linarith
    unfold psi; rw [if_pos ⟨h3, h1⟩]; simp

/-- Elementary inequality. -/
lemma key_ineq (a c M R : ℝ) (ha : 0 ≤ a) (hc0 : 0 ≤ c) (hc : c ≤ R) (hM : 0 < M) :
    a * c ≤ min a M * c + R / M * a ^ 2 := by
  have hR : 0 ≤ R := le_trans hc0 hc
  by_cases hle : a ≤ M
  · rw [min_eq_left hle]
    have : 0 ≤ R / M * a ^ 2 := by positivity
    linarith
  · push_neg at hle
    rw [min_eq_right hle.le]
    have h1 : a - M ≤ a ^ 2 / M := by
      rw [le_div_iff₀ hM]
      nlinarith
    have h2 : (a - M) * c ≤ (a ^ 2 / M) * R :=
      mul_le_mul h1 hc hc0 (by positivity)
    have h3 : R / M * a ^ 2 = (a ^ 2 / M) * R := by ring
    nlinarith

lemma meas_min {α : Type*} [MeasurableSpace α] {μ : Measure α} (f gg : α → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable gg μ) (M : ℝ) :
    AEStronglyMeasurable (fun z => min |f z| M * |gg z|) μ :=
  ((hf.aemeasurable.norm.min aemeasurable_const).mul hg.aemeasurable.norm).aestronglyMeasurable

theorem weak_core {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    [l.IsCountablyGenerated] (h : ι → α → ℝ) (C : ℝ)
    (hm : ∀ᶠ i in l, MemLp (h i) 2 μ) (hC : ∀ᶠ i in l, ∫ z, h i z ^ 2 ∂μ ≤ C)
    (hlim : ∀ z, Tendsto (fun i => h i z) l (𝓝 0)) (g : α → ℝ) (hg : MemLp g 2 μ) :
    Tendsto (fun i => ∫ z, h i z * g z ∂μ) l (𝓝 0) := by
  set D : ℝ := max C 1 with hD
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCD : ∀ᶠ i in l, ∫ z, h i z ^ 2 ∂μ ≤ D :=
    hC.mono fun i hi => hi.trans (le_max_left _ _)
  have hgm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hgR_m : ∀ R : ℕ, AEStronglyMeasurable (fun z => psi R (g z)) μ := fun R =>
    ((psi_measurable R).comp_aemeasurable hgm.aemeasurable).aestronglyMeasurable
  have hgR_L2 : ∀ R : ℕ, MemLp (fun z => psi R (g z)) 2 μ := fun R =>
    hg.mono (hgR_m R) (ae_of_all _ fun z => by
      simpa [Real.norm_eq_abs] using abs_psi_le_self R (g z))
  have hgR_int : ∀ R : ℕ, Integrable (fun z => psi R (g z)) μ := fun R =>
    Integrable.mono' (hg.integrable_sq.const_mul (R : ℝ)) (hgR_m R)
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using abs_psi_le_sq R (g z))
  have he_L2 : ∀ R : ℕ, MemLp (fun z => g z - psi R (g z)) 2 μ := fun R => hg.sub (hgR_L2 R)
  -- the remainder tends to zero in L²
  have hrem : Tendsto (fun R : ℕ => ∫ z, (g z - psi R (g z)) ^ 2 ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (R : ℕ) z => (g z - psi R (g z)) ^ 2) (f := fun _ => (0 : ℝ))
      (fun z => g z ^ 2)
      (fun R => ((he_L2 R).integrable_sq).aestronglyMeasurable)
      hg.integrable_sq
      (fun R => ae_of_all _ fun z => by
        have := abs_self_sub_psi_le R (g z)
        rw [Real.norm_eq_abs, abs_pow, sq_abs]
        have h0 : |g z - psi R (g z)| ^ 2 ≤ |g z| ^ 2 := by gcongr
        simpa [sq_abs] using h0)
      (ae_of_all _ fun z => by simpa using (tendsto_sub_psi (g z)).pow 2)
    simpa using this
  rw [Metric.tendsto_nhds]
  intro ε hε
  set lam : ℝ := 4 * D / ε with hlam
  have hlampos : 0 < lam := by positivity
  obtain ⟨R, hR⟩ := (hrem.eventually (gt_mem_nhds (a := (ε / (4 * lam))) (by positivity))).exists
  set M : ℝ := 4 * R * D / ε + 1 with hMdef
  have hMpos : 0 < M := by positivity
  set e : α → ℝ := fun z => g z - psi R (g z) with he
  set gR : α → ℝ := fun z => psi R (g z) with hgRdef
  -- the dominated-convergence term
  have hA : Tendsto (fun i => ∫ z, min |h i z| M * |gR z| ∂μ) l (𝓝 0) := by
    have hbd_int : Integrable (fun z => M * |gR z|) μ := (hgR_int R).abs.const_mul M
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
      (F := fun i z => min |h i z| M * |gR z|) (f := fun _ => (0 : ℝ))
      (fun z => M * |gR z|)
      (hm.mono fun i hi =>
        meas_min _ _ hi.aestronglyMeasurable (hgR_m R) M)
      (Eventually.of_forall fun i => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr; exact min_le_right _ _)
      hbd_int
      (ae_of_all _ fun z => by
        have := ((hlim z).abs.min (tendsto_const_nhds (x := M))).mul_const |gR z|
        simpa [min_eq_left hMpos.le] using this)
    simpa using this
  have hAev := hA.eventually (gt_mem_nhds (a := ε / 4) (by positivity))
  filter_upwards [hAev, hm, hCD] with i hAi hmi hCi
  rw [Real.dist_eq, sub_zero]
  have hi_gR : Integrable (fun z => h i z * gR z) μ := hmi.integrable_mul (hgR_L2 R)
  have hi_e : Integrable (fun z => h i z * e z) μ := hmi.integrable_mul (he_L2 R)
  have hsplit : ∫ z, h i z * g z ∂μ = ∫ z, h i z * gR z ∂μ + ∫ z, h i z * e z ∂μ := by
    rw [← integral_add hi_gR hi_e]
    congr 1; funext z; simp only [he, hgRdef]; ring
  have hh2 : Integrable (fun z => h i z ^ 2) μ := hmi.integrable_sq
  have hmin_int : Integrable (fun z => min |h i z| M * |gR z|) μ := by
    refine Integrable.mono' ((hgR_int R).abs.const_mul M)
      (meas_min _ _ hmi.aestronglyMeasurable (hgR_m R) M) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr; exact min_le_right _ _
  -- first part
  have hP1 : |∫ z, h i z * gR z ∂μ| ≤ (∫ z, min |h i z| M * |gR z| ∂μ) + R / M * D := by
    have h1 : |∫ z, h i z * gR z ∂μ| ≤ ∫ z, |h i z * gR z| ∂μ := abs_integral_le_integral_abs
    have h2 : ∫ z, |h i z * gR z| ∂μ ≤
        ∫ z, (min |h i z| M * |gR z| + R / M * h i z ^ 2) ∂μ := by
      refine integral_mono hi_gR.abs (hmin_int.add (hh2.const_mul _)) fun z => ?_
      simp only
      rw [abs_mul]
      have := key_ineq |h i z| |gR z| M R (abs_nonneg _) (abs_nonneg _)
        (abs_psi_le_R R (g z)) hMpos
      simpa [sq_abs] using this
    have h3 : ∫ z, (min |h i z| M * |gR z| + R / M * h i z ^ 2) ∂μ =
        ∫ z, min |h i z| M * |gR z| ∂μ + R / M * ∫ z, h i z ^ 2 ∂μ := by
      rw [integral_add hmin_int (hh2.const_mul _), integral_const_mul]
    have hRM : 0 ≤ R / M := by positivity
    have : R / M * ∫ z, h i z ^ 2 ∂μ ≤ R / M * D := mul_le_mul_of_nonneg_left hCi hRM
    have hB : R / M * D ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hMpos, hMdef]
      have : (R : ℝ) * D * 4 = 4 * R * D := by ring
      have h5 : ε / 4 * (4 * R * D / ε + 1) = R * D + ε / 4 := by field_simp
      nlinarith [h5, hε]
    linarith
  have hB : R / M * D ≤ ε / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hMpos, hMdef]
    have h5 : ε / 4 * (4 * R * D / ε + 1) = R * D + ε / 4 := by field_simp
    nlinarith [h5, hε]
  -- second part
  have hP2 : |∫ z, h i z * e z ∂μ| ≤ ε / 4 + ε / 4 := by
    have he2 : Integrable (fun z => e z ^ 2) μ := (he_L2 R).integrable_sq
    have h1 : |∫ z, h i z * e z ∂μ| ≤ ∫ z, |h i z * e z| ∂μ := abs_integral_le_integral_abs
    have h2 : ∫ z, |h i z * e z| ∂μ ≤ ∫ z, (lam / 2 * e z ^ 2 + (1 / (2 * lam)) * h i z ^ 2) ∂μ := by
      refine integral_mono hi_e.abs ((he2.const_mul _).add (hh2.const_mul _)) fun z => ?_
      simp only
      rw [abs_mul]
      have hl2 : 0 < 2 * lam := by positivity
      have : |h i z| * |e z| ≤ lam / 2 * |e z| ^ 2 + 1 / (2 * lam) * |h i z| ^ 2 := by
        have : 0 ≤ (lam * |e z| - |h i z|) ^ 2 := sq_nonneg _
        have e1 : lam / 2 * |e z| ^ 2 + 1 / (2 * lam) * |h i z| ^ 2 - |h i z| * |e z|
            = (lam * |e z| - |h i z|) ^ 2 / (2 * lam) := by field_simp; ring
        have : 0 ≤ (lam * |e z| - |h i z|) ^ 2 / (2 * lam) := by positivity
        linarith
      simpa [sq_abs] using this
    have h3 : ∫ z, (lam / 2 * e z ^ 2 + (1 / (2 * lam)) * h i z ^ 2) ∂μ =
        lam / 2 * ∫ z, e z ^ 2 ∂μ + (1 / (2 * lam)) * ∫ z, h i z ^ 2 ∂μ := by
      rw [integral_add (he2.const_mul _) (hh2.const_mul _), integral_const_mul,
        integral_const_mul]
    have h4 : lam / 2 * ∫ z, e z ^ 2 ∂μ ≤ ε / 4 := by
      have : ∫ z, e z ^ 2 ∂μ < ε / (4 * lam) := hR
      have h6 : lam / 2 * (ε / (4 * lam)) = ε / 8 := by field_simp; ring
      have := mul_le_mul_of_nonneg_left this.le (by positivity : (0:ℝ) ≤ lam / 2)
      linarith
    have h5 : (1 / (2 * lam)) * ∫ z, h i z ^ 2 ∂μ ≤ ε / 4 := by
      have := mul_le_mul_of_nonneg_left hCi (by positivity : (0:ℝ) ≤ 1 / (2 * lam))
      have h7 : 1 / (2 * lam) * D = ε / 8 := by
        rw [hlam]; field_simp; ring
      linarith
    linarith
  rw [hsplit]
  calc |∫ z, h i z * gR z ∂μ + ∫ z, h i z * e z ∂μ|
      ≤ |∫ z, h i z * gR z ∂μ| + |∫ z, h i z * e z ∂μ| := abs_add_le _ _
    _ < ε := by linarith [hP1, hP2, hAi, hB]

end UnforcedLeray.Short.PartI.L2SqDeriv.Weak

open UnforcedLeray.Short.PartI.L2SqDeriv in
/-- Weak convergence of the difference quotients (source 341-348). -/
theorem l2SqWeak : UnforcedLeray.Short.PartI.L2SqDeriv.L2SqWeak := by
  intro μ F s ε K H hm g hg
  have hdiff := l2SqDiff (μ := μ) F s ε K H hm
  obtain ⟨hε, hC, hF, hD⟩ := H
  set d : Plane → ℝ := fun z => deriv (fun t => F t z) s with hd
  have hs : |s - s| < ε := by simpa using hε
  have hdL2 : MemLp d 2 μ := (hD s hs).1
  have hdK : ∫ z, d z ^ 2 ∂μ ≤ K := (hD s hs).2
  have hev : ∀ᶠ r in 𝓝[≠] s, |r - s| < ε ∧ r ≠ s := by
    have h1 : ∀ᶠ r in 𝓝 s, |r - s| < ε := by
      have : Metric.ball s ε ∈ 𝓝 s := Metric.ball_mem_nhds s hε
      filter_upwards [this] with r hr
      simpa [Metric.mem_ball, Real.dist_eq] using hr
    exact (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  set h : ℝ → Plane → ℝ := fun r z => (F r z - F s z) / (r - s) - d z with hh
  have hq : ∀ r, |r - s| < ε → r ≠ s →
      MemLp (fun z => (F r z - F s z) / (r - s)) 2 μ ∧
        ∫ z, ((F r z - F s z) / (r - s)) ^ 2 ∂μ ≤ K := by
    intro r hr hne
    have hne' : r - s ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨h1, h2⟩ := hdiff r hr
    refine ⟨by simpa [div_eq_inv_mul] using h1.const_mul (r - s)⁻¹, ?_⟩
    have : ∫ z, ((F r z - F s z) / (r - s)) ^ 2 ∂μ =
        ((r - s) ^ 2)⁻¹ * ∫ z, (F r z - F s z) ^ 2 ∂μ := by
      rw [← integral_const_mul]; congr 1; funext z
      rw [div_pow, div_eq_inv_mul]
    rw [this]
    have hp : 0 < (r - s) ^ 2 := by positivity
    calc ((r - s) ^ 2)⁻¹ * ∫ z, (F r z - F s z) ^ 2 ∂μ
        ≤ ((r - s) ^ 2)⁻¹ * ((r - s) ^ 2 * K) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K := by field_simp
  have hmem : ∀ᶠ r in 𝓝[≠] s, MemLp (h r) 2 μ := hev.mono fun r ⟨hr, hne⟩ =>
    (hq r hr hne).1.sub hdL2
  have hbd : ∀ᶠ r in 𝓝[≠] s, ∫ z, h r z ^ 2 ∂μ ≤ 4 * K := hev.mono fun r ⟨hr, hne⟩ => by
    obtain ⟨hq1, hq2⟩ := hq r hr hne
    have hi : Integrable (fun z => h r z ^ 2) μ := (hq1.sub hdL2).integrable_sq
    calc ∫ z, h r z ^ 2 ∂μ
        ≤ ∫ z, (2 * ((F r z - F s z) / (r - s)) ^ 2 + 2 * d z ^ 2) ∂μ := by
          refine integral_mono hi ((hq1.integrable_sq.const_mul 2).add
            (hdL2.integrable_sq.const_mul 2)) fun z => ?_
          simp only [hh]
          nlinarith [sq_nonneg (((F r z - F s z) / (r - s)) + d z)]
      _ = 2 * ∫ z, ((F r z - F s z) / (r - s)) ^ 2 ∂μ + 2 * ∫ z, d z ^ 2 ∂μ := by
          rw [integral_add (hq1.integrable_sq.const_mul 2) (hdL2.integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ 4 * K := by linarith
  have hlim : ∀ z, Tendsto (fun r => h r z) (𝓝[≠] s) (𝓝 0) := by
    intro z
    have := (hasDerivAt_iff_tendsto_slope.1
      ((hC z).differentiable (by norm_num) s).hasDerivAt)
    have h2 := this.sub_const (deriv (fun t => F t z) s)
    rw [sub_self] at h2
    refine h2.congr fun r => ?_
    simp only [hh, hd, slope_def_field, div_eq_inv_mul]
  have hcore := Weak.weak_core h (4 * K) hmem hbd hlim g hg
  have hcore2 : Tendsto (fun r => ∫ z, (F r z - F s z) / (r - s) * g z ∂μ -
      ∫ z, d z * g z ∂μ) (𝓝[≠] s) (𝓝 0) := by
    refine hcore.congr' ?_
    filter_upwards [hev] with r ⟨hr, hne⟩
    obtain ⟨hq1, _⟩ := hq r hr hne
    have i1 : Integrable (fun z => (F r z - F s z) / (r - s) * g z) μ := hq1.integrable_mul hg
    have i2 : Integrable (fun z => d z * g z) μ := hdL2.integrable_mul hg
    rw [← integral_sub i1 i2]
    congr 1; funext z; simp only [hh]; ring
  simpa using (tendsto_sub_nhds_zero_iff.1 hcore2)
