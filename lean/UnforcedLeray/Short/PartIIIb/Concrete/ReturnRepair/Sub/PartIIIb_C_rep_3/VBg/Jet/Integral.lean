import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Leaves
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Ring-chart `Y_2` integration of two-scale jet envelopes (`PartIII-b:C/rep/3/4/1`, helper 1)

Source of record: `the November 2 reference manuscript`, lines 2681-2688,
5225-5235, 5461-5464.

If a nonnegative physical scalar `f(τ, y)` satisfies, at every chart point `pt = (s, (q, η))`:
* `f ≤ B₁ · s · (1 + |η|)⁻¹` for `0 < s ≤ 1`, and
* `f ≤ B₂ · (1 + |η / √s|)⁻¹` for `1 < s`,

then `R⁻¹ ‖ringRead R f‖_{L²(ringPhysμ R c)} ≤ 3 √π (B₁ + B₂)` without measurability assumptions
(using Tonelli `lintegral_prod_le` as in `VSq.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.VBgSq.JetAux

/-- `∫_{(1,∞)} s^{-2} ds = 1`. -/
theorem lintegral_Ioi_rpow_neg_two :
    ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-2 : ℝ)) = ENNReal.ofReal 1 := by
  have hr : (-2 : ℝ) < -1 := by norm_num
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr zero_lt_one)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      Real.rpow_nonneg (zero_lt_one.trans ht).le _), integral_Ioi_rpow_of_lt hr zero_lt_one,
    Real.one_rpow]
  norm_num

/-- `∫_ℝ ((1 + |η|)²)⁻¹ dη ≤ 4`. -/
theorem lintegral_inv_one_add_abs_sq_le :
    ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) ≤ ENNReal.ofReal 4 := by
  calc ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹)
      ≤ ENNReal.ofReal Real.pi := by
        rw [← integral_univ_inv_one_add_sq, ofReal_integral_eq_lintegral_ofReal
          integrable_inv_one_add_sq (ae_of_all _ fun x => by positivity)]
        refine lintegral_mono fun η => ENNReal.ofReal_le_ofReal ?_
        exact inv_anti₀ (by positivity) (by nlinarith [abs_nonneg η, sq_abs η])
    _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal Real.pi_le_four

/-- `∫_ℝ ((1 + |η / √s|)²)⁻¹ dη ≤ 4 √s` for `s > 0`. -/
theorem lintegral_inv_one_add_abs_div_sqrt_sq_le {s : ℝ} (hs : 0 < s) :
    ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η / Real.sqrt s|) ^ 2)⁻¹) ≤
      ENNReal.ofReal (4 * Real.sqrt s) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hint : Integrable (fun η : ℝ => (1 + (η / Real.sqrt s) ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.comp_div hsq.ne'
  have hval : ∫ η : ℝ, (1 + (η / Real.sqrt s) ^ 2)⁻¹ = Real.sqrt s * Real.pi := by
    have h := Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) (Real.sqrt s)
    simpa [abs_of_pos hsq, smul_eq_mul, integral_univ_inv_one_add_sq] using h
  calc ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η / Real.sqrt s|) ^ 2)⁻¹)
      ≤ ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt s) ^ 2)⁻¹) := by
        refine lintegral_mono fun η => ENNReal.ofReal_le_ofReal ?_
        exact inv_anti₀ (by positivity)
          (by nlinarith [abs_nonneg (η / Real.sqrt s), sq_abs (η / Real.sqrt s)])
    _ = ENNReal.ofReal (Real.sqrt s * Real.pi) := by
        rw [← hval, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)]
    _ ≤ ENNReal.ofReal (4 * Real.sqrt s) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [Real.pi_le_four, hsq.le]

/-- Cell average against `Cyl.avgμ c` of a `q`-independent transverse weight `E(η)`. -/
theorem avgμ_lintegral_le_of_eta_bound {c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℝ) (E : ℝ → ℝ)
    (_hE : ∀ η : ℝ, 0 ≤ E η) (hpt : ∀ x : ℝ × ℝ, 0 ≤ g x ∧ g x ≤ E x.2) :
    ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c) ≤ ∫⁻ η : ℝ, ENNReal.ofReal (E η ^ 2) := by
  have hpt2 : ∀ x : ℝ × ℝ, ‖g x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (E x.2 ^ 2) := by
    intro x
    obtain ⟨hg0, hle⟩ := hpt x
    rw [Real.enorm_of_nonneg hg0, ENNReal.ofReal_rpow_of_nonneg hg0 (by norm_num), Real.rpow_two]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hg0 hle 2)
  have hcell : ∫⁻ x, ENNReal.ofReal (E x.2 ^ 2) ∂(Cyl.cellμ c) ≤
      ENNReal.ofReal c * ∫⁻ η : ℝ, ENNReal.ofReal (E η ^ 2) := by
    have hμ : Cyl.cellμ c = (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) := by
      rw [Cyl.cellμ, Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
        Measure.restrict_univ]
    rw [hμ, ← lintegral_prod_swap]
    refine (lintegral_prod_le _).trans (le_of_eq ?_)
    have hinner : ∀ η : ℝ,
        ∫⁻ _q in Ico (-c / 2) (c / 2), ENNReal.ofReal (E η ^ 2) =
          ENNReal.ofReal c * ENNReal.ofReal (E η ^ 2) := by
      intro η
      rw [setLIntegral_const, Real.volume_Ico]
      have : c / 2 - -c / 2 = c := by ring
      rw [this, mul_comm]
    calc ∫⁻ η, ∫⁻ q, ENNReal.ofReal (E (Prod.swap (η, q)).2 ^ 2)
          ∂(volume.restrict (Ico (-c / 2) (c / 2))) ∂(volume : Measure ℝ)
        = ∫⁻ η, ENNReal.ofReal c * ENNReal.ofReal (E η ^ 2) :=
          lintegral_congr fun η => hinner η
      _ = ENNReal.ofReal c * ∫⁻ η, ENNReal.ofReal (E η ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c)
      ≤ ∫⁻ x, ENNReal.ofReal (E x.2 ^ 2) ∂(Cyl.avgμ c) := lintegral_mono hpt2
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x, ENNReal.ofReal (E x.2 ^ 2) ∂(Cyl.cellμ c) := by
        rw [Cyl.avgμ, lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ∫⁻ η, ENNReal.ofReal (E η ^ 2)) := by
        gcongr
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * ∫⁻ η, ENNReal.ofReal (E η ^ 2) := by ring
    _ = ∫⁻ η, ENNReal.ofReal (E η ^ 2) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]

/-- Age-measure integral bound for a two-scale envelope. -/
theorem ageμ_jet_lintegral_le {R c B₁ B₂ : ℝ} (hc : 0 < c) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (f : ℝ → Space → ℝ)
    (h0 : ∀ pt : Chart, 0 < pt.1 → 0 ≤ f (NearInst.chartTau R pt) (NearInst.chartY R pt))
    (hlow : ∀ pt : Chart, 0 < pt.1 → pt.1 ≤ 1 →
      f (NearInst.chartTau R pt) (NearInst.chartY R pt) ≤ B₁ * pt.1 * (1 + |pt.2.2|)⁻¹)
    (hhigh : ∀ pt : Chart, 1 < pt.1 →
      f (NearInst.chartTau R pt) (NearInst.chartY R pt) ≤
        B₂ * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹) :
    ∫⁻ p, ‖ringRead R f p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-5 / 2)) ≤
      ENNReal.ofReal (9 * (B₁ + B₂) ^ 2) := by
  set F : Chart → ℝ≥0∞ := fun p => ‖ringRead R f p‖ₑ ^ (2 : ℝ)
  set I : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, F (s, x) ∂(Cyl.avgμ c)
  set w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))
  have hI_low : ∀ s ∈ Ioc (0 : ℝ) 1,
      w s * I s ≤ ENNReal.ofReal (4 * B₁ ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
    intro s hs
    have hcell : I s ≤ ENNReal.ofReal (4 * B₁ ^ 2 * s ^ 2) := by
      have h1 := avgμ_lintegral_le_of_eta_bound hc (fun x => ringRead R f (s, x))
        (fun η => B₁ * s * (1 + |η|)⁻¹) (fun η => by have := hs.1.le; positivity)
        (fun x => ⟨h0 (s, x) hs.1, hlow (s, x) hs.1 hs.2⟩)
      have hrew : (fun η : ℝ => ENNReal.ofReal ((B₁ * s * (1 + |η|)⁻¹) ^ 2)) =
          fun η : ℝ => ENNReal.ofReal (B₁ ^ 2 * s ^ 2) * ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) := by
        funext η
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_pow, mul_pow, inv_pow]
      refine h1.trans ?_
      rw [hrew, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (B₁ ^ 2 * s ^ 2) * ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹)
          ≤ ENNReal.ofReal (B₁ ^ 2 * s ^ 2) * ENNReal.ofReal 4 := by
            gcongr; exact lintegral_inv_one_add_abs_sq_le
        _ = ENNReal.ofReal (4 * B₁ ^ 2 * s ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    have hpow : s ^ (-5 / 2 : ℝ) * (4 * B₁ ^ 2 * s ^ 2) = 4 * B₁ ^ 2 * s ^ (-1 / 2 : ℝ) := by
      have h : s ^ (-5 / 2 : ℝ) * s ^ 2 = s ^ (-1 / 2 : ℝ) := by
        rw [sq, ← mul_assoc, ← Real.rpow_add_one hs.1.ne', ← Real.rpow_add_one hs.1.ne']
        norm_num
      calc s ^ (-5 / 2 : ℝ) * (4 * B₁ ^ 2 * s ^ 2)
          = 4 * B₁ ^ 2 * (s ^ (-5 / 2 : ℝ) * s ^ 2) := by ring
        _ = 4 * B₁ ^ 2 * s ^ (-1 / 2 : ℝ) := by rw [h]
    calc w s * I s ≤ ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ENNReal.ofReal (4 * B₁ ^ 2 * s ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (4 * B₁ ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _), hpow,
            ENNReal.ofReal_mul (by positivity)]
  have hI_high : ∀ s ∈ Ioi (1 : ℝ),
      w s * I s ≤ ENNReal.ofReal (4 * B₂ ^ 2) * ENNReal.ofReal (s ^ (-2 : ℝ)) := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans hs
    have hcell : I s ≤ ENNReal.ofReal (4 * B₂ ^ 2 * Real.sqrt s) := by
      have h1 := avgμ_lintegral_le_of_eta_bound hc (fun x => ringRead R f (s, x))
        (fun η => B₂ * (1 + |η / Real.sqrt s|)⁻¹) (fun η => by positivity)
        (fun x => ⟨h0 (s, x) hs0, hhigh (s, x) hs⟩)
      have hrew : (fun η : ℝ => ENNReal.ofReal ((B₂ * (1 + |η / Real.sqrt s|)⁻¹) ^ 2)) =
          fun η : ℝ => ENNReal.ofReal (B₂ ^ 2) *
            ENNReal.ofReal (((1 + |η / Real.sqrt s|) ^ 2)⁻¹) := by
        funext η
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_pow, inv_pow]
      refine h1.trans ?_
      rw [hrew, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (B₂ ^ 2) *
            ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η / Real.sqrt s|) ^ 2)⁻¹)
          ≤ ENNReal.ofReal (B₂ ^ 2) * ENNReal.ofReal (4 * Real.sqrt s) := by
            gcongr; exact lintegral_inv_one_add_abs_div_sqrt_sq_le hs0
        _ = ENNReal.ofReal (4 * B₂ ^ 2 * Real.sqrt s) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    have hpow : s ^ (-5 / 2 : ℝ) * (4 * B₂ ^ 2 * Real.sqrt s) = 4 * B₂ ^ 2 * s ^ (-2 : ℝ) := by
      have h : s ^ (-5 / 2 : ℝ) * Real.sqrt s = s ^ (-2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
        norm_num
      calc s ^ (-5 / 2 : ℝ) * (4 * B₂ ^ 2 * Real.sqrt s)
          = 4 * B₂ ^ 2 * (s ^ (-5 / 2 : ℝ) * Real.sqrt s) := by ring
        _ = 4 * B₂ ^ 2 * s ^ (-2 : ℝ) := by rw [h]
    calc w s * I s ≤ ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
          ENNReal.ofReal (4 * B₂ ^ 2 * Real.sqrt s) := by gcongr
      _ = ENNReal.ofReal (4 * B₂ ^ 2) * ENNReal.ofReal (s ^ (-2 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), hpow,
            ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ p, F p ∂(ageμ c (-5 / 2))
      ≤ ∫⁻ s, I s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity w) := by
        rw [ageμ]
        exact lintegral_prod_le _
    _ ≤ ∫⁻ s, (w * I) s ∂(volume.restrict (Ioi (0 : ℝ))) :=
        lintegral_withDensity_le_lintegral_mul _ (measurable_ofReal_rpow _) _
    _ = ∫⁻ s in Ioc (0 : ℝ) 1 ∪ Ioi 1, w s * I s := by
        rw [Ioc_union_Ioi_eq_Ioi zero_le_one]
        rfl
    _ ≤ (∫⁻ s in Ioc (0 : ℝ) 1, w s * I s) + ∫⁻ s in Ioi (1 : ℝ), w s * I s :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (4 * B₁ ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) +
          ∫⁻ s in Ioi (1 : ℝ),
            ENNReal.ofReal (4 * B₂ ^ 2) * ENNReal.ofReal (s ^ (-2 : ℝ)) := by
        refine add_le_add ?_ ?_
        · exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
            (Eventually.of_forall hI_low))
        · exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall hI_high))
    _ = ENNReal.ofReal (4 * B₁ ^ 2) * ENNReal.ofReal 2 +
          ENNReal.ofReal (4 * B₂ ^ 2) * ENNReal.ofReal 1 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_rpow_neg_half,
          lintegral_Ioi_rpow_neg_two]
    _ = ENNReal.ofReal (8 * B₁ ^ 2 + 4 * B₂ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (9 * (B₁ + B₂) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg B₁, sq_nonneg B₂, mul_nonneg hB₁ hB₂]

/-- **Master `Y_2` bound** from low-age (`s ≤ 1`) and high-age (`1 < s`) chart-point bounds. -/
theorem vJet_ringL2_le {R c B₁ B₂ : ℝ} (hR : 0 < R) (hc : 0 < c) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (f : ℝ → Space → ℝ)
    (h0 : ∀ pt : Chart, 0 < pt.1 → 0 ≤ f (NearInst.chartTau R pt) (NearInst.chartY R pt))
    (hlow : ∀ pt : Chart, 0 < pt.1 → pt.1 ≤ 1 →
      f (NearInst.chartTau R pt) (NearInst.chartY R pt) ≤ B₁ * pt.1 * (1 + |pt.2.2|)⁻¹)
    (hhigh : ∀ pt : Chart, 1 < pt.1 →
      f (NearInst.chartTau R pt) (NearInst.chartY R pt) ≤
        B₂ * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹) :
    ENNReal.ofReal R⁻¹ * eLpNorm (ringRead R f) 2 (ringPhysμ R c) ≤
      ENNReal.ofReal (3 * Real.sqrt Real.pi * (B₁ + B₂)) := by
  have hA := ageμ_jet_lintegral_le hc hB₁ hB₂ f h0 hlow hhigh
  rw [ringPhysμ, eLpNorm_smul_measure_of_ne_top (by simp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hhalf : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div, h2]; simp
  rw [h2, hhalf, smul_eq_mul]
  have hB : (∫⁻ x, ‖ringRead R f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-5 / 2))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (3 * (B₁ + B₂)) := by
    refine (ENNReal.rpow_le_rpow hA (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.sqrt_eq_rpow, show 9 * (B₁ + B₂) ^ 2 = (3 * (B₁ + B₂)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hP : ENNReal.ofReal (Real.pi * R ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt Real.pi * R) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
  rw [hP, ← mul_assoc]
  calc ENNReal.ofReal R⁻¹ * ENNReal.ofReal (Real.sqrt Real.pi * R) *
        (∫⁻ x, ‖ringRead R f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-5 / 2))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal R⁻¹ * ENNReal.ofReal (Real.sqrt Real.pi * R) *
          ENNReal.ofReal (3 * (B₁ + B₂)) := by gcongr
    _ = ENNReal.ofReal (3 * Real.sqrt Real.pi * (B₁ + B₂)) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hR.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.VBgSq.JetAux

end
