import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.PeriodAverageAE

/-!
# Part II-a, task `PartII-a:F06/1/3`: averaging the window bound over the centres (`PeriodAverageBound`)

Source of record: `the November 2 reference manuscript`, lines 1431-1480.

Proof. Put `G τ = ∫⁻ y, ‖Λ(τ,y)‖ₑ^r` and `H τ = ‖f τ‖ₑ^r + (1+‖μ‖)^r ‖w τ‖ₑ^r` (slices read at
`(τ : AddCircle P)`). Then:

* `G` is measurable and a.e. `P`-periodic (`hper` plus `lintegral_congr_ae`);
* `H` is AE-measurable on `ℝ` (the covering map `ℝ → AddCircle P` is quasi-measure-preserving,
  shown from `AddCircle.measurePreserving_mk` on the period cells) and everywhere `P`-periodic;
* translation invariance turns `∫⁻ τ in (τ₀-a, τ₀+a), F` into `∫⁻ t in (-a, a), F(τ₀+t)`;
* integrating the window bound over `τ₀ ∈ (0,P]` and applying `periodAverageAE` with
  `I = (-1,1)` (volume `2`) to `G` and with `I = (-2,2)` (volume `4`) to `H` gives
  `2 ∫G ≤ 4 C^r ∫H`, and cancelling `2` yields the stated bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIa

/-- The covering map `ℝ → AddCircle P` is quasi-measure-preserving for Lebesgue measure. -/
lemma pab_coe_preimage_null (P : ℝ) [Fact (0 < P)] {S : Set (AddCircle P)}
    (hS : MeasurableSet S) (h0 : volume S = 0) :
    volume (((↑) : ℝ → AddCircle P) ⁻¹' S) = 0 := by
  have hP : 0 < P := Fact.out
  have hcov : ∀ x : ℝ, ∃ n : ℤ, x ∈ Ioc ((n : ℝ) * P) ((n : ℝ) * P + P) := by
    intro x
    refine ⟨⌈x / P⌉ - 1, ?_⟩
    have h1 : x / P ≤ (⌈x / P⌉ : ℝ) := Int.le_ceil _
    have h2 : (⌈x / P⌉ : ℝ) < x / P + 1 := Int.ceil_lt_add_one _
    have e : x / P * P = x := div_mul_cancel₀ x hP.ne'
    have a1 : ((⌈x / P⌉ : ℝ) - 1) * P < x := by
      have := mul_lt_mul_of_pos_right (show (⌈x / P⌉ : ℝ) - 1 < x / P by linarith) hP
      linarith
    have a2 : x ≤ (⌈x / P⌉ : ℝ) * P := by
      have := mul_le_mul_of_nonneg_right h1 hP.le
      linarith
    rw [mem_Ioc]
    push_cast
    constructor
    · linarith
    · nlinarith
  refine measure_mono_null (t := ⋃ n : ℤ,
      (((↑) : ℝ → AddCircle P) ⁻¹' S) ∩ Ioc ((n : ℝ) * P) ((n : ℝ) * P + P)) ?_ ?_
  · intro x hx
    obtain ⟨n, hn⟩ := hcov x
    exact mem_iUnion.2 ⟨n, hx, hn⟩
  · refine measure_iUnion_null fun n => ?_
    have hmp := AddCircle.measurePreserving_mk (T := P) ((n : ℝ) * P)
    rw [← Measure.restrict_apply (hmp.measurable hS)]
    rw [hmp.measure_preimage hS.nullMeasurableSet, h0]

/-- The covering map `ℝ → AddCircle P` is quasi-measure-preserving for Lebesgue measure. -/
lemma pab_coe_qmp (P : ℝ) [Fact (0 < P)] :
    Measure.QuasiMeasurePreserving ((↑) : ℝ → AddCircle P) volume volume := by
  have hmeas : Measurable ((↑) : ℝ → AddCircle P) :=
    (AddCircle.measurePreserving_mk (T := P) 0).measurable
  refine ⟨hmeas, ?_⟩
  intro s hs
  have h1 : Measure.map ((↑) : ℝ → AddCircle P) volume s ≤
      Measure.map ((↑) : ℝ → AddCircle P) volume (toMeasurable volume s) :=
    measure_mono (subset_toMeasurable _ _)
  have h2 : Measure.map ((↑) : ℝ → AddCircle P) volume (toMeasurable volume s) = 0 := by
    rw [Measure.map_apply hmeas (measurableSet_toMeasurable _ _)]
    exact pab_coe_preimage_null P (measurableSet_toMeasurable _ _)
      (by rw [measure_toMeasurable]; exact hs)
  exact nonpos_iff_eq_zero.mp (h1.trans h2.le)

lemma pab_aemeasurable_coe {P : ℝ} [Fact (0 < P)] {F : AddCircle P → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure (AddCircle P))) :
    AEMeasurable (fun τ : ℝ => F (τ : AddCircle P)) volume :=
  hF.comp_quasiMeasurePreserving (pab_coe_qmp P)

/-- Translation of a set integral over a symmetric interval about `c`. -/
lemma pab_setLIntegral_shift (F : ℝ → ℝ≥0∞) (c a : ℝ) :
    ∫⁻ τ in Ioo (c - a) (c + a), F τ = ∫⁻ t in Ioo (-a) a, F (c + t) := by
  have h := lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
    ((Ioo (c - a) (c + a)).indicator F) c
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  rw [← h]
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator_apply, Set.mem_Ioo]
  by_cases hx : -a < x ∧ x < a
  · have hy : c - a < c + x ∧ c + x < c + a := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [if_pos hx, if_pos hy]
  · have hy : ¬ (c - a < c + x ∧ c + x < c + a) := fun h' =>
      hx ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [if_neg hx, if_neg hy]

theorem periodAverageBound : PeriodAverageBound := by
  intro r _ hr P _ C μ f w Λ hΛ hper hbd
  have hP : 0 < P := Fact.out
  obtain ⟨G, hGfun⟩ : ∃ G : ℝ → ℝ≥0∞, G = fun τ : ℝ => ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal := ⟨_, rfl⟩
  obtain ⟨H, hHfun⟩ : ∃ H : ℝ → ℝ≥0∞, H = fun τ : ℝ =>
      ‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal := ⟨_, rfl⟩
  have hbd' : ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), G τ ≤
      ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), H τ := by
    intro τ₀
    rw [hGfun, hHfun]
    exact hbd τ₀
  -- measurability and periodicity of `G`
  have hGm : Measurable G := by
    rw [hGfun]
    have h1 : Measurable (fun p : ℝ × Space => ‖Λ p‖ₑ ^ r.toReal) :=
      (hΛ.measurable.enorm).pow_const _
    exact h1.lintegral_prod_right'
  have hGper : ∀ᵐ τ : ℝ, G (τ + P) = G τ := by
    filter_upwards [hper] with τ hτ
    rw [hGfun]
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    simp [hy]
  -- measurability and periodicity of `H`
  have hHm : AEMeasurable H volume := by
    have hF : AEMeasurable (fun θ : AddCircle P => ‖f θ‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w θ‖ₑ ^ r.toReal)
        (volume : Measure (AddCircle P)) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      have hfa : AEMeasurable (fun θ : AddCircle P => ‖f θ‖ₑ)
          AddCircle.haarAddCircle :=
        (Lp.aestronglyMeasurable f).enorm
      have hwa : AEMeasurable (fun θ : AddCircle P => ‖w θ‖ₑ)
          AddCircle.haarAddCircle :=
        (Lp.aestronglyMeasurable w).enorm
      exact ((hfa.pow_const _).add ((hwa.pow_const _).const_mul _)).smul_measure _
    rw [hHfun]
    exact pab_aemeasurable_coe hF
  have hHper : ∀ᵐ τ : ℝ, H (τ + P) = H τ := by
    refine Filter.Eventually.of_forall fun τ => ?_
    rw [hHfun]
    simp only [AddCircle.coe_add_period]
  -- centre averaging for `G` and `H`
  have hAG := periodAverageAE P hP G hGm.aemeasurable hGper (Ioo (-1) 1) measurableSet_Ioo
  have hAH := periodAverageAE P hP H hHm hHper (Ioo (-2) 2) measurableSet_Ioo
  have v1 : volume (Ioo (-1 : ℝ) 1) = 2 := by
    rw [Real.volume_Ioo]
    norm_num
  have v2 : volume (Ioo (-2 : ℝ) 2) = 4 := by
    rw [Real.volume_Ioo]
    norm_num
  have hL : ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), G τ = ∫⁻ t in Ioo (-1) 1, G (τ₀ + t) :=
    fun τ₀ => pab_setLIntegral_shift G τ₀ 1
  have hR : ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), H τ = ∫⁻ t in Ioo (-2) 2, H (τ₀ + t) :=
    fun τ₀ => pab_setLIntegral_shift H τ₀ 2
  have key : ∫⁻ τ₀ in Ioc 0 P, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), G τ ≤
      ∫⁻ τ₀ in Ioc 0 P, ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), H τ :=
    lintegral_mono hbd'
  have hK : ENNReal.ofReal C ^ r.toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have eL : ∫⁻ τ₀ in Ioc 0 P, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), G τ =
      2 * ∫⁻ τ in Ioc 0 P, G τ := by
    rw [lintegral_congr hL, hAG, v1]
  have eR : ∫⁻ τ₀ in Ioc 0 P, ENNReal.ofReal C ^ r.toReal *
      ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), H τ =
      ENNReal.ofReal C ^ r.toReal * (4 * ∫⁻ τ in Ioc 0 P, H τ) := by
    rw [lintegral_const_mul' _ _ hK]
    congr 1
    rw [lintegral_congr hR, hAH, v2]
  rw [eL, eR] at key
  have goalG : ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal = ∫⁻ τ in Ioc 0 P, G τ := by
    rw [hGfun]
  have goalH : ∫⁻ τ in Ioc 0 P, (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) =
      ∫⁻ τ in Ioc 0 P, H τ := by
    rw [hHfun]
  rw [goalG, goalH]
  have h2 : (2 : ℝ≥0∞) * ∫⁻ τ in Ioc 0 P, G τ ≤
      2 * (2 * ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioc 0 P, H τ) := by
    calc (2 : ℝ≥0∞) * ∫⁻ τ in Ioc 0 P, G τ
        ≤ ENNReal.ofReal C ^ r.toReal * (4 * ∫⁻ τ in Ioc 0 P, H τ) := key
      _ = 2 * (2 * ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioc 0 P, H τ) := by ring
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h2

end UnforcedLeray.Short.PartIIa
