import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `PartIII-b:C/rep/5/2/2/8` helper: the phase norm in `L²_τ`

The mixed norm `ltauLq1 P q H` is the `L²(μP)` norm of `τ ↦ lqNorm1 q (H τ)`, where
`μP = (ofReal P)⁻¹ • volume|_{(0,P]}` (`ltau_eq_eLp2`). For a `P`-periodic `G` the shift
`τ ↦ G(τ + c)` has the same `L²(μP)` norm (`ltau_shift`, from `pds_window`), for every `P > 0`
(no `P ≤ 1` is needed). The `λ`-integral `∫_0^1 λ^{c}` with `c ≥ -3/22` is at most `22/19`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace Rep522Phase

/-- The normalized phase measure `(1/P) dτ` on `(0, P]`. -/
def muP (P : ℝ) : Measure ℝ := (ENNReal.ofReal P)⁻¹ • (volume.restrict (Ioc 0 P))

end Rep522Phase

theorem eLp2_muP (P : ℝ) (f : ℝ → ℝ≥0∞) :
    eLpNorm f 2 (Rep522Phase.muP P) = ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, f τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  unfold Rep522Phase.muP
  rw [lintegral_smul_measure, smul_eq_mul]

theorem ltau_eq_eLp2 {P q : ℝ} (H : ℝ → ℝ → ℝ≥0∞) :
    ltauLq1 P q H = eLpNorm (fun τ => lqNorm1 q (H τ)) 2 (Rep522Phase.muP P) := by
  rw [eLp2_muP P]
  unfold ltauLq1
  congr 2
  refine lintegral_congr fun τ => ?_
  unfold lqNorm1
  rw [← ENNReal.rpow_mul]
  congr 1
  ring

/-- Translation invariance of the period integral (`pds_window` plus the translation of
Lebesgue measure). -/
theorem ltau_shift {P : ℝ} (hP : 0 < P) {F : ℝ → ℝ≥0∞} (hF : ∀ s, F (s + P) = F s) (c : ℝ) :
    ∫⁻ τ in Ioc 0 P, F (τ + c) = ∫⁻ τ in Ioc 0 P, F τ := by
  have h1 : ∫⁻ τ in Ioc 0 P, F (τ + c) = ∫⁻ τ, (Ioc c (c + P)).indicator F (τ + c) := by
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun τ => ?_
    by_cases hτ : τ ∈ Ioc 0 P
    · have hmem : τ + c ∈ Ioc c (c + P) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      rw [indicator_of_mem hτ, indicator_of_mem hmem]
    · have hmem : τ + c ∉ Ioc c (c + P) := fun h => hτ ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [indicator_of_notMem hτ, indicator_of_notMem hmem]
  rw [h1, lintegral_add_right_eq_self (fun x => (Ioc c (c + P)).indicator F x) c,
    lintegral_indicator measurableSet_Ioc]
  exact pds_window hP hF c


/-- The normalized phase measure is finite for `P > 0`. -/
theorem muP_finite {P : ℝ} (hP : 0 < P) : IsFiniteMeasure (Rep522Phase.muP P) := by
  refine ⟨?_⟩
  unfold Rep522Phase.muP
  rw [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hP)) ENNReal.ofReal_lt_top

/-- The `L²(μP)` norm of a shifted periodic function. -/
theorem eLp2_shift {P : ℝ} (hP : 0 < P) {G : ℝ → ℝ≥0∞} (hG : ∀ s, G (s + P) = G s) (c : ℝ) :
    eLpNorm (fun τ => G (τ + c)) 2 (Rep522Phase.muP P) = eLpNorm G 2 (Rep522Phase.muP P) := by
  rw [eLp2_muP P, eLp2_muP P]
  congr 2
  exact ltau_shift hP (F := fun u => G u ^ (2 : ℝ)) (fun s => by simp only [hG]) c

/-- Constant factors pass through the `L²(μP)` norm. -/
theorem eLp2_const_mul (P : ℝ) (k : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    eLpNorm (fun τ => k * f τ) 2 (Rep522Phase.muP P) = k * eLpNorm f 2 (Rep522Phase.muP P) := by
  rw [eLp2_muP P, eLp2_muP P]
  have hpt : ∀ τ, (k * f τ) ^ (2 : ℝ) = k ^ (2 : ℝ) * f τ ^ (2 : ℝ) :=
    fun τ => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  simp only [hpt]
  rw [lintegral_const_mul _ (hf.pow_const _)]
  rw [show (ENNReal.ofReal P)⁻¹ * (k ^ (2 : ℝ) * ∫⁻ τ in Ioc 0 P, f τ ^ (2 : ℝ)) =
      k ^ (2 : ℝ) * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, f τ ^ (2 : ℝ)) by ring]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num

/-- The `λ`-integral of `λ^c`, `c ≥ -3/22`, is at most `22/19`. -/
theorem phase_int_le {c : ℝ} (hc : -(3 / 22) ≤ c) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) ≤ ENNReal.ofReal (22 / 19) := by
  have hc1 : -1 < c := by linarith
  have hint : IntegrableOn (fun l : ℝ => l ^ c) (Ioo (0 : ℝ) 1) := by
    have h1 : IntervalIntegrable (fun l : ℝ => l ^ c) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' hc1
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h1).mono_set
      Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun l : ℝ => l ^ c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with l hl
    exact Real.rpow_nonneg hl.1.le c
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  apply ENNReal.ofReal_le_ofReal
  have hval : ∫ l in Ioo (0 : ℝ) 1, l ^ c = 1 / (c + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl hc1)]
    rw [Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]
  rw [hval, div_le_iff₀ (by linarith)]
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
