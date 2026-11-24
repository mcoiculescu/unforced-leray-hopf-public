import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1

/-!
# Part III-a, task `PartIII-a:T18/2/1`: `L²` pairing helpers for the slice clauses

Helpers for `UnforcedLeray.Short.IIIa.CausalSliceClauses` (`Sub/T18_2_1.lean`). Source of record:
`the November 2 reference manuscript`, lines 3427-3440 ("the test functions have
compact `η`-support so `∂ψ` is in `L²(cell)`").

Content: Hölder on the cell (proved on `lintegral`s), integrability of `L² × L²` products, the
`L²` finiteness of tests on the cell, and passage to the limit `∫ fₙ w → ∫ f w` when
`∫ ‖fₙ - f‖² → 0` and `w ∈ L²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem sc_holder_two : (2 : ℝ).HolderConjugate 2 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Hölder on the cell, in `lintegral` form with `p = q = 2`. -/
theorem sc_holder {α : Type*} [MeasurableSpace α] (μ : Measure α) {f w : α → ℂ}
    (hf : Measurable f) (hw : Measurable w) :
    ∫⁻ x, ENNReal.ofReal ‖f x * w x‖ ∂μ ≤
      (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) := by
  have hF : Measurable fun x => ENNReal.ofReal ‖f x‖ := ENNReal.measurable_ofReal.comp hf.norm
  have hW : Measurable fun x => ENNReal.ofReal ‖w x‖ := ENNReal.measurable_ofReal.comp hw.norm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ sc_holder_two hF.aemeasurable hW.aemeasurable
  have e1 : ∀ x, ENNReal.ofReal ‖f x‖ ^ (2 : ℝ) = ENNReal.ofReal (‖f x‖ ^ 2) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two]
  have e2 : ∀ x, ENNReal.ofReal ‖w x‖ ^ (2 : ℝ) = ENNReal.ofReal (‖w x‖ ^ 2) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (w x)) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two]
  have e3 : ∀ x, ENNReal.ofReal ‖f x * w x‖ = ENNReal.ofReal ‖f x‖ * ENNReal.ofReal ‖w x‖ :=
    fun x => by rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  simp only [e1, e2, Pi.mul_apply] at h
  calc ∫⁻ x, ENNReal.ofReal ‖f x * w x‖ ∂μ
      = ∫⁻ x, ENNReal.ofReal ‖f x‖ * ENNReal.ofReal ‖w x‖ ∂μ := lintegral_congr fun x => e3 x
    _ ≤ _ := h

/-- Products of two `L²` functions are integrable. -/
theorem sc_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f w : α → ℂ}
    (hf : Measurable f) (hw : Measurable w)
    (hf2 : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ < ⊤)
    (hw2 : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ < ⊤) :
    Integrable (fun x => f x * w x) μ := by
  refine ⟨(hf.mul hw).aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).2 ?_⟩
  refine lt_of_le_of_lt (sc_holder μ hf hw) (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf2.ne
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hw2.ne

/-- An `L²` function (as a complex-valued function) has finite `∫ ‖f‖²`, in `ofReal` form. -/
theorem sc_lintegral_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ < ⊤ := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).1
    hi.hasFiniteIntegral

/-- A cylinder test function is in `L²(cell)`. -/
theorem sc_test_L2 {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖(φ x : ℂ)‖ ^ 2) < ⊤ := by
  obtain ⟨R, hR⟩ := hφ.vanish
  have hm : MemLp φ 2 (volume.restrict (B0579.cell c)) :=
    B0579.memLp_cell_of_continuous hφ.continuous (B0579.isCompact_box c R) hR
  exact sc_lintegral_of_memLp hm.ofReal

/-- A cylinder test function, as a complex-valued function, is measurable. -/
theorem sc_cyl_meas {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    Measurable fun x => (φ x : ℂ) :=
  (Complex.continuous_ofReal.comp hφ.continuous).measurable

theorem sc_norm_comp_sq_le (z : Fin 2 → ℂ) (i : Fin 2) : ‖z i‖ ^ 2 ≤ vnorm2 z ^ 2 := by
  rw [causalLin_vnorm2_sq]
  exact Finset.single_le_sum (f := fun k => ‖z k‖ ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem sc_tensor_comp_sq_le (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    ‖T i j‖ ^ 2 ≤ tnorm2 T ^ 2 := by
  rw [causalLin_tnorm2_sq]
  have h1 : ‖T i j‖ ^ 2 ≤ ∑ l, ‖T i l‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖T i l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ l, ‖T i l‖ ^ 2 ≤ ∑ k, ∑ l, ‖T k l‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ∑ l, ‖T k l‖ ^ 2)
      (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
  exact le_trans h1 h2

theorem sc_two_mul_ofReal (t : ℝ) :
    (2 : ℝ≥0∞) * ENNReal.ofReal t = ENNReal.ofReal (2 * t) := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- `‖h‖² ≤ 2‖f‖² + 2‖g‖²` with `f` in `L²` and `g` in `L²` gives `h` in `L²`. -/
theorem sc_lt_top_of_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℂ}
    (hf : Measurable f) (hfg : ∀ x, ‖h x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2)
    (hf2 : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ < ⊤)
    (hg2 : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ < ⊤ := by
  have hpt : ∀ x, ENNReal.ofReal (‖h x‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖f x‖ ^ 2) + 2 * ENNReal.ofReal (‖g x‖ ^ 2) := by
    intro x
    have h1 : (0 : ℝ) ≤ 2 * ‖f x‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * ‖g x‖ ^ 2 := by positivity
    rw [sc_two_mul_ofReal (‖f x‖ ^ 2), sc_two_mul_ofReal (‖g x‖ ^ 2),
      ← ENNReal.ofReal_add h1 h2]
    exact ENNReal.ofReal_le_ofReal (hfg x)
  have hmeas : Measurable fun x => 2 * ENNReal.ofReal (‖f x‖ ^ 2) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hf.norm.pow_const 2))
  calc ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖f x‖ ^ 2) + 2 * ENNReal.ofReal (‖g x‖ ^ 2)) ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ x, 2 * ENNReal.ofReal (‖f x‖ ^ 2) ∂μ + ∫⁻ x, 2 * ENNReal.ofReal (‖g x‖ ^ 2) ∂μ :=
        lintegral_add_left hmeas _
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ + 2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
    _ < ⊤ := ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top (by simp) hf2, ENNReal.mul_lt_top (by simp) hg2⟩

/-- The pairing limit: `∫⁻ ‖hₙ‖² → 0` and `w ∈ L²` give `∫ hₙ w → 0`. -/
theorem sc_tendsto_zero_of_L2 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {h : ℕ → α → ℂ} {w : α → ℂ} (hw : Measurable w)
    (hw2 : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ < ⊤) (hh : ∀ n, Measurable (h n))
    (hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖h n x‖ ^ 2) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, h n x * w x ∂μ) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (‖h n x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)))
      atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / (2 : ℝ)))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h0
  have hG : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (‖h n x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const h0
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hw2.ne))
    rwa [zero_mul] at h1
  have hev : ∀ᶠ n in atTop, (∫⁻ x, ENNReal.ofReal (‖h n x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) < ⊤ :=
    hG.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  have hg : Tendsto (fun n => ((∫⁻ x, ENNReal.ofReal (‖h n x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ))).toReal) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG
    rw [ENNReal.toReal_zero] at h1
    exact h1
  have hreal : Tendsto (fun n => ‖∫ x, h n x * w x ∂μ‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hg
    filter_upwards [hev] with n hn
    refine le_trans (norm_integral_le_lintegral_norm _) (ENNReal.toReal_mono hn.ne ?_)
    exact sc_holder μ (hh n) hw
  exact tendsto_zero_iff_norm_tendsto_zero.2 hreal

/-- The pairing limit `∫ fₙ w → ∫ f w` for `fₙ → f` in `L²` and `w ∈ L²`. -/
theorem sc_tendsto_integral_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {fn : ℕ → α → ℂ} {f0 w : α → ℂ}
    (hfn : ∀ n, Measurable (fn n)) (hf0 : Measurable f0) (hw : Measurable w)
    (hfn2 : ∀ n, ∫⁻ x, ENNReal.ofReal (‖fn n x‖ ^ 2) ∂μ < ⊤)
    (hf02 : ∫⁻ x, ENNReal.ofReal (‖f0 x‖ ^ 2) ∂μ < ⊤)
    (hw2 : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂μ < ⊤)
    (hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖fn n x - f0 x‖ ^ 2) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, fn n x * w x ∂μ) atTop (𝓝 (∫ x, f0 x * w x ∂μ)) := by
  have hd2 : ∀ n, ∫⁻ x, ENNReal.ofReal (‖fn n x - f0 x‖ ^ 2) ∂μ < ⊤ := fun n =>
    sc_lt_top_of_sq_le (h := fun x => fn n x - f0 x) (hfn n)
      (fun x => by
        have := causalLin_norm_sub_sq_le (fn n x) (f0 x)
        exact this)
      (hfn2 n) hf02
  have hsplit : ∀ n, ∫ x, fn n x * w x ∂μ =
      ∫ x, f0 x * w x ∂μ + ∫ x, (fn n x - f0 x) * w x ∂μ := by
    intro n
    rw [← integral_add (sc_integrable hf0 hw hf02 hw2)
      (sc_integrable (f := fun x => fn n x - f0 x) ((hfn n).sub hf0) hw (hd2 n) hw2)]
    congr 1
    funext x
    ring
  have hdiff := sc_tendsto_zero_of_L2 μ (h := fun n x => fn n x - f0 x) hw hw2
    (fun n => (hfn n).sub hf0) hlim
  have hc : Tendsto (fun n => (∫ x, f0 x * w x ∂μ) + ∫ x, (fn n x - f0 x) * w x ∂μ) atTop
      (𝓝 ((∫ x, f0 x * w x ∂μ) + 0)) :=
    tendsto_const_nhds.add hdiff
  rw [add_zero] at hc
  exact Tendsto.congr (fun n => (hsplit n).symm) hc

/-- The `L²` norm of a limit: `∫⁻ ‖Aₙ - B‖² → 0` with `Aₙ ∈ L²` gives `B ∈ L²`. -/
theorem sc_limit_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : ℕ → α → ℂ} {B : α → ℂ}
    (hA : ∀ n, Measurable (A n)) (hA2 : ∀ n, ∫⁻ x, ENNReal.ofReal (‖A n x‖ ^ 2) ∂μ < ⊤)
    (hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖A n x - B x‖ ^ 2) ∂μ) atTop (𝓝 0)) :
    ∫⁻ x, ENNReal.ofReal (‖B x‖ ^ 2) ∂μ < ⊤ := by
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds ENNReal.zero_lt_top)).exists
  exact sc_lt_top_of_sq_le (h := B) (f := A n) (g := fun x => A n x - B x) (hA n)
    (fun x => by
      have := causalLin_norm_sub_sq_le (A n x) (A n x - B x)
      rwa [sub_sub_cancel] at this)
    (hA2 n) hn

/-- Componentwise `L²` convergence from convergence of the vector norm. -/
theorem sc_vnorm_comp_tendsto {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F : ℕ → α → Fin 2 → ℂ}
    (hF : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (vnorm2 (F n x) ^ 2) ∂μ) atTop (𝓝 0))
    (i : Fin 2) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖F n x i‖ ^ 2) ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun n => zero_le)
    (fun n => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (sc_norm_comp_sq_le (F n x) i))

/-- Componentwise `L²` convergence from convergence of the tensor norm. -/
theorem sc_tnorm_comp_tendsto {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {G : ℕ → α → Fin 2 → Fin 2 → ℂ}
    (hG : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (tnorm2 (G n x) ^ 2) ∂μ) atTop (𝓝 0))
    (i j : Fin 2) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖G n x i j‖ ^ 2) ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG (fun n => zero_le)
    (fun n => lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (sc_tensor_comp_sq_le (G n x) i j))

end UnforcedLeray.Short.IIIa
