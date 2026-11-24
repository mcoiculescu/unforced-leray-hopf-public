import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_4
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The `V ⊗ V` part of the thin-coefficient bound (helper of `PartIII-b:C/rep/3/4`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5225-5235 (`R⁻¹‖V⊗V‖_{Y_2} ≤ P_ν` among the thin-coefficient bounds), 2703-2723
(`stress-short:coefficients`: `sup √s W|v| ≤ P_ν`, `sup_{s<σ} √s W|v| ≤ P_ν√σ`,
`‖Wv(s)‖_{L²_ηL^∞_q} ≤ P_ν[(1+s)^{-3/4} + ε(1+s)^{-1/4}]`).

With `V = √s v` and the ring measure `πR²s^{-5/2}ds dq/c dη`,
`R⁻²‖|V|²‖²_{Y_2} = π∫ s^{-1/2}|v|⁴`.  The first two coefficient bounds give `|V|² ≤ P_ν²` and
`|V|² ≤ 2P_ν²s` for `s ≤ 1`, the fourth gives `∫ c⁻¹|v|² dq dη ≤ P_ν²` at every age, so the
integral is at most `P_ν⁴(2∫_0^1 s^{-1/2} + ∫_1^∞ s^{-3/2}) = 6P_ν⁴`.  No measurability is used
(Tonelli in the form `lintegral_prod_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace VBgSq

/-- `∫_{(0,1]} s^{-1/2} ds = 2`. -/
theorem lintegral_Ioc_rpow_neg_half :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) = ENNReal.ofReal 2 := by
  have hr : (-1 : ℝ) < -1 / 2 := by norm_num
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_rpow' hr).1
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _)]
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr),
    Real.zero_rpow (by norm_num), sub_zero, Real.one_rpow]
  norm_num

/-- `∫_{(1,∞)} s^{-3/2} ds = 2`. -/
theorem lintegral_Ioi_rpow_neg_three_halves :
    ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) = ENNReal.ofReal 2 := by
  have hr : (-3 / 2 : ℝ) < -1 := by norm_num
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr zero_lt_one)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      Real.rpow_nonneg (zero_lt_one.trans ht).le _), integral_Ioi_rpow_of_lt hr zero_lt_one,
    Real.one_rpow]
  norm_num

theorem rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The cell integral at one age `s > 0`: if `|V|² ≤ B` on the age surface and
`‖sup_q |v(s,q,·)|‖_{L²_η} ≤ K'`, then `∫ c⁻¹ |V|⁴ dq dη ≤ B s K'²`. -/
theorem cell_lintegral_le {R c s B K' : ℝ} (hc : 0 < c) (hs : 0 < s) (hB : 0 ≤ B) (hK' : 0 ≤ K')
    (V : ℝ → SpatialField)
    (hBd : ∀ x : ℝ × ℝ,
      ‖V (NearInst.chartTau R (s, x)) (NearInst.chartY R (s, x))‖ ^ 2 ≤ B)
    (hE : vEtaSup R c V s ≤ ENNReal.ofReal K') :
    ∫⁻ x, ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) (s, x)‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c) ≤
      ENNReal.ofReal (B * s * K' ^ 2) := by
  set g : ℝ × ℝ → ℝ := fun x => ‖V (NearInst.chartTau R (s, x)) (NearInst.chartY R (s, x))‖
    with hg
  set E : ℝ → ℝ≥0∞ := fun η => essSup (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
      ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))
    (volume.restrict (Ico (-(c / 2)) (c / 2))) with hEdef
  -- pointwise: `|V|⁴ ≤ B |V|²`
  have hpt : ∀ x : ℝ × ℝ,
      ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) (s, x)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal B * ENNReal.ofReal (g x ^ 2) := by
    intro x
    have hg0 : 0 ≤ g x := norm_nonneg _
    have hx : (ringRead R fun τ y => ‖V τ y‖ ^ 2) (s, x) = g x ^ 2 := rfl
    rw [hx, Real.enorm_of_nonneg (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by norm_num), ← ENNReal.ofReal_mul hB]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : (g x ^ 2) ^ (2 : ℝ) = g x ^ 2 * g x ^ 2 := by
      rw [Real.rpow_two, sq]
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hBd x) (by positivity)
  -- the cell integral of `|V|²`
  have hsq : ∀ q η : ℝ, ENNReal.ofReal (g (q, η) ^ 2) =
      ENNReal.ofReal s * ENNReal.ofReal ((Real.sqrt s)⁻¹ * g (q, η)) ^ 2 := by
    intro q η
    have hs' : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hs.le]
    congr 1
    rw [mul_pow, inv_pow, Real.sq_sqrt hs.le]
    field_simp
  have hinner : ∀ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal (g (q, η) ^ 2) ≤
      ENNReal.ofReal s * E η ^ 2 * ENNReal.ofReal c := by
    intro η
    have hI : Ico (-c / 2) (c / 2) = Ico (-(c / 2)) (c / 2) := by rw [neg_div]
    rw [hI]
    calc ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal (g (q, η) ^ 2)
        ≤ ∫⁻ _ in Ico (-(c / 2)) (c / 2), ENNReal.ofReal s * E η ^ 2 := by
          refine lintegral_mono_ae ?_
          filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict (Ico (-(c / 2)) (c / 2)))
            (fun q : ℝ => ENNReal.ofReal ((Real.sqrt s)⁻¹ *
              ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖))] with q hq
          rw [hsq q η]
          gcongr
      _ = ENNReal.ofReal s * E η ^ 2 * ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ico]
          congr 2
          ring
  have hcell : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Cyl.cellμ c) ≤
      ENNReal.ofReal s * ENNReal.ofReal c * ∫⁻ η, E η ^ 2 := by
    have hμ : Cyl.cellμ c = (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) := by
      rw [Cyl.cellμ, Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
        Measure.restrict_univ]
    rw [hμ, ← lintegral_prod_swap]
    refine (lintegral_prod_le _).trans ?_
    calc ∫⁻ η, ∫⁻ q, ENNReal.ofReal (g (Prod.swap (η, q)) ^ 2)
          ∂(volume.restrict (Ico (-c / 2) (c / 2))) ∂(volume : Measure ℝ)
        ≤ ∫⁻ η, ENNReal.ofReal s * ENNReal.ofReal c * E η ^ 2 := by
          refine lintegral_mono fun η => ?_
          refine (hinner η).trans (le_of_eq ?_)
          ring
      _ = ENNReal.ofReal s * ENNReal.ofReal c * ∫⁻ η, E η ^ 2 :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hEint : ∫⁻ η, E η ^ 2 ≤ ENNReal.ofReal (K' ^ 2) := by
    have h1 : ∫⁻ η, E η ^ 2 = vEtaSup R c V s ^ 2 := by
      rw [vEtaSup, rpow_half_sq]
      refine lintegral_congr fun η => ?_
      rw [ENNReal.rpow_two]
    rw [h1, ENNReal.ofReal_pow hK']
    exact pow_le_pow_left' hE 2
  calc ∫⁻ x, ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) (s, x)‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c)
      ≤ ∫⁻ x, ENNReal.ofReal B * ENNReal.ofReal (g x ^ 2) ∂(Cyl.avgμ c) := lintegral_mono hpt
    _ = ENNReal.ofReal B * (ENNReal.ofReal c⁻¹ * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Cyl.cellμ c)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Cyl.avgμ, lintegral_smul_measure,
          smul_eq_mul]
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal c⁻¹ *
          (ENNReal.ofReal s * ENNReal.ofReal c * ENNReal.ofReal (K' ^ 2))) := by
        gcongr
        refine hcell.trans ?_
        gcongr
    _ = ENNReal.ofReal (B * s * K' ^ 2) := by
        rw [← ENNReal.ofReal_mul hs.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ← ENNReal.ofReal_mul hB]
        congr 1
        field_simp

/-- `s^{-5/2}·(B s)·s ≤ ...`: the two age weights. -/
theorem age_weight_low {s K K' : ℝ} (hs : 0 < s) :
    s ^ (-5 / 2 : ℝ) * (2 * K ^ 2 * s * s * K' ^ 2) = 2 * K ^ 2 * K' ^ 2 * s ^ (-1 / 2 : ℝ) := by
  have h : s ^ (-5 / 2 : ℝ) * s * s = s ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hs.ne', ← Real.rpow_add_one hs.ne']
    norm_num
  calc s ^ (-5 / 2 : ℝ) * (2 * K ^ 2 * s * s * K' ^ 2)
      = 2 * K ^ 2 * K' ^ 2 * (s ^ (-5 / 2 : ℝ) * s * s) := by ring
    _ = 2 * K ^ 2 * K' ^ 2 * s ^ (-1 / 2 : ℝ) := by rw [h]

theorem age_weight_high {s K K' : ℝ} (hs : 0 < s) :
    s ^ (-5 / 2 : ℝ) * (K ^ 2 * s * K' ^ 2) = K ^ 2 * K' ^ 2 * s ^ (-3 / 2 : ℝ) := by
  have h : s ^ (-5 / 2 : ℝ) * s = s ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hs.ne']
    norm_num
  calc s ^ (-5 / 2 : ℝ) * (K ^ 2 * s * K' ^ 2)
      = K ^ 2 * K' ^ 2 * (s ^ (-5 / 2 : ℝ) * s) := by ring
    _ = K ^ 2 * K' ^ 2 * s ^ (-3 / 2 : ℝ) := by rw [h]

/-- **The age integral** `∫ s^{-5/2}c⁻¹|V|⁴ ≤ 6K²K'²` from `|V|² ≤ K²`, `|V|² ≤ 2K²s` (`s ≤ 1`)
and `‖sup_q|v(s,q,·)|‖_{L²_η} ≤ K'` (source 5225-5235, 2703-2723). -/
theorem ageμ_lintegral_le {R c K K' : ℝ} (hc : 0 < c) (hK' : 0 ≤ K')
    (V : ℝ → SpatialField)
    (h1 : ∀ pt : Chart, 0 < pt.1 →
      ‖V (NearInst.chartTau R pt) (NearInst.chartY R pt)‖ ^ 2 ≤ K ^ 2)
    (h3 : ∀ pt : Chart, 0 < pt.1 → pt.1 ≤ 1 →
      ‖V (NearInst.chartTau R pt) (NearInst.chartY R pt)‖ ^ 2 ≤ 2 * K ^ 2 * pt.1)
    (h4 : ∀ s : ℝ, 0 < s → vEtaSup R c V s ≤ ENNReal.ofReal K') :
    ∫⁻ p, ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-5 / 2)) ≤
      ENNReal.ofReal (6 * K ^ 2 * K' ^ 2) := by
  set F : Chart → ℝ≥0∞ := fun p => ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) p‖ₑ ^ (2 : ℝ) with hF
  set I : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, F (s, x) ∂(Cyl.avgμ c) with hIdef
  set w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) with hw
  have hlow : ∀ s ∈ Ioc (0 : ℝ) 1, w s * I s ≤
      ENNReal.ofReal (2 * K ^ 2 * K' ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
    intro s hs
    have hB : 0 ≤ 2 * K ^ 2 * s := by have := hs.1.le; positivity
    have hI : I s ≤ ENNReal.ofReal (2 * K ^ 2 * s * s * K' ^ 2) :=
      cell_lintegral_le hc hs.1 hB hK' V (fun x => h3 (s, x) hs.1 hs.2) (h4 s hs.1)
    calc w s * I s ≤ ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
          ENNReal.ofReal (2 * K ^ 2 * s * s * K' ^ 2) := by gcongr
      _ = ENNReal.ofReal (2 * K ^ 2 * K' ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _), age_weight_low hs.1,
          ENNReal.ofReal_mul (by positivity)]
  have hhigh : ∀ s ∈ Ioi (1 : ℝ), w s * I s ≤
      ENNReal.ofReal (K ^ 2 * K' ^ 2) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans hs
    have hI : I s ≤ ENNReal.ofReal (K ^ 2 * s * K' ^ 2) :=
      cell_lintegral_le hc hs0 (sq_nonneg K) hK' V (fun x => h1 (s, x) hs0) (h4 s hs0)
    calc w s * I s ≤ ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ENNReal.ofReal (K ^ 2 * s * K' ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (K ^ 2 * K' ^ 2) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), age_weight_high hs0,
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
            ENNReal.ofReal (2 * K ^ 2 * K' ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) +
          ∫⁻ s in Ioi (1 : ℝ),
            ENNReal.ofReal (K ^ 2 * K' ^ 2) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
        refine add_le_add ?_ ?_
        · exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
            (Eventually.of_forall hlow))
        · exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall hhigh))
    _ = ENNReal.ofReal (2 * K ^ 2 * K' ^ 2) * ENNReal.ofReal 2 +
          ENNReal.ofReal (K ^ 2 * K' ^ 2) * ENNReal.ofReal 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_rpow_neg_half,
          lintegral_Ioi_rpow_neg_three_halves]
    _ = ENNReal.ofReal (6 * K ^ 2 * K' ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The `V ⊗ V` part in `Y_2`** (source 5225-5235): under the coefficient bounds of
`ageμ_lintegral_le`, `R⁻¹‖|V|²‖_{Y_2} ≤ √(6π)KK'` in the ring-chart form. -/
theorem vSq_ringL2_le {R c K K' : ℝ} (hR : 0 < R) (hc : 0 < c) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (V : ℝ → SpatialField)
    (h1 : ∀ pt : Chart, 0 < pt.1 →
      ‖V (NearInst.chartTau R pt) (NearInst.chartY R pt)‖ ^ 2 ≤ K ^ 2)
    (h3 : ∀ pt : Chart, 0 < pt.1 → pt.1 ≤ 1 →
      ‖V (NearInst.chartTau R pt) (NearInst.chartY R pt)‖ ^ 2 ≤ 2 * K ^ 2 * pt.1)
    (h4 : ∀ s : ℝ, 0 < s → vEtaSup R c V s ≤ ENNReal.ofReal K') :
    ENNReal.ofReal R⁻¹ * eLpNorm (ringRead R fun τ y => ‖V τ y‖ ^ 2) 2 (ringPhysμ R c) ≤
      ENNReal.ofReal (Real.sqrt (6 * Real.pi) * K * K') := by
  have hA := ageμ_lintegral_le hc hK' V h1 h3 h4
  rw [ringPhysμ, eLpNorm_smul_measure_of_ne_top (by simp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hhalf : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div, h2]; simp
  rw [h2, hhalf, smul_eq_mul]
  have hB : (∫⁻ x, ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-5 / 2))) ^
      (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt 6 * K * K') := by
    refine (ENNReal.rpow_le_rpow hA (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.sqrt_eq_rpow, show 6 * K ^ 2 * K' ^ 2 = 6 * (K * K') ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    ring
  have hP : ENNReal.ofReal (Real.pi * R ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt Real.pi * R) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
  rw [hP, ← mul_assoc]
  calc ENNReal.ofReal R⁻¹ * ENNReal.ofReal (Real.sqrt Real.pi * R) *
        (∫⁻ x, ‖(ringRead R fun τ y => ‖V τ y‖ ^ 2) x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-5 / 2))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal R⁻¹ * ENNReal.ofReal (Real.sqrt Real.pi * R) *
          ENNReal.ofReal (Real.sqrt 6 * K * K') := by gcongr
    _ = ENNReal.ofReal (Real.sqrt (6 * Real.pi) * K * K') := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hR.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.sqrt_mul (by norm_num)]
        field_simp

/-! ## Instantiation along the concrete sequence -/

theorem Nv_chartPoint_apply_one {R : ℝ} (hR : 0 < R) (b : ℝ × (ℝ × ℝ) → Merid)
    {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    Nv R b (NearInst.chartTau R pt) (NearInst.chartY R pt) 1 = 0 := by
  change Nv R b (IIIa.chartPhase R pt) (IIIa.chartPoint R pt) 1 = 0
  rw [Nv, IIIa.age_chartPoint hR hs, IIIa.chart_chartPoint hR hs, frameL_apply,
    IIIa.eR_chartPoint hR hs]
  simp

theorem norm_space_eq_norm_merid {w : Space} (hw : w 1 = 0) :
    ‖w‖ = ‖(!₂[w 0, w 2] : Merid)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [hw]

theorem one_le_transWeight' {mZ : ℝ} (hmZ : 0 ≤ mZ) (pt : ℝ × (ℝ × ℝ)) :
    1 ≤ IIIa.transWeight mZ pt := by
  unfold IIIa.transWeight
  exact Real.one_le_rpow (by linarith [sq_nonneg (pt.2.2 / Real.sqrt (1 + pt.1))]) (by linarith)

/-- `|V| = √s|v|` at a chart point where the azimuthal component vanishes. -/
theorem norm_chart_eq {R : ℝ} {V : ℝ → SpatialField} {pt : Chart} (hs : 0 < pt.1)
    (hV1 : V (NearInst.chartTau R pt) (NearInst.chartY R pt) 1 = 0) :
    ‖V (NearInst.chartTau R pt) (NearInst.chartY R pt)‖ =
      Real.sqrt pt.1 * ‖IIIa.chartCoeff R V pt‖ := by
  have hs' : 0 < Real.sqrt pt.1 := Real.sqrt_pos.2 hs
  have hcoeff : ‖IIIa.chartCoeff R V pt‖ =
      (Real.sqrt pt.1)⁻¹ * ‖V (NearInst.chartTau R pt) (NearInst.chartY R pt)‖ := by
    change ‖(Real.sqrt pt.1)⁻¹ •
      (!₂[V (NearInst.chartTau R pt) (NearInst.chartY R pt) 0,
          V (NearInst.chartTau R pt) (NearInst.chartY R pt) 2] : Merid)‖ = _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs'.le), ← norm_space_eq_norm_merid hV1]
  rw [hcoeff]
  field_simp

/-- **`ε‖|V|²‖_{Y_2} ≤ P_ν` along the sequence** (source 5225-5235 with 2703-2723): from
`IIIa.StressCoefficients` (first and third clauses, `W ≥ 1`, `|V| = √s|v|` for the swirl-free `V`)
and `repVBg_vEtaSup` (fourth clause). -/
theorem repVBg_vSq (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (D.level n).ε *
          eLpNorm (ringRead (D.level n).ε⁻¹ fun τ y => ‖(D.level n).V τ y‖ ^ 2) 2
            (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k) := by
  have hSC : UnforcedLeray.Short.IIIa.StressCoefficients :=
    UnforcedLeray.Short.IIIa.stressCoefficients_of
      UnforcedLeray.Short.IIIa.rawCoeffLate
      UnforcedLeray.Short.IIIa.rawCoeffEarly
      UnforcedLeray.Short.IIIa.inletCoeffBounds
  obtain ⟨C, k, ν₀, hν₀, h⟩ := hSC dm dp hst.dm_pos D.K.m0 D.K.C0 D.K.k0 hst.m0_pos
    hst.m0_lt.le D.K.mZ hst.mZ_gt D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos hst.planar.eigenpair
  obtain ⟨C₄, k₄, hC₄, heta⟩ := repVBg_vEtaSup D hst
  refine ⟨Real.sqrt (6 * Real.pi) * |C| * C₄, k + k₄, by positivity, ?_⟩
  filter_upwards [hst.actual, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀),
    heta] with n hn hν het
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hv := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.Sin n) (D.V n) (D.rb n)
    hn.split
  obtain ⟨z, -, hVz, -, -⟩ := hn.split.state
  set K : ℝ := |C| * (D.level n).ν⁻¹ ^ k with hKdef
  have hK : 0 ≤ K := by positivity
  have hCK : C * (D.level n).ν⁻¹ ^ k ≤ K :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  -- the azimuthal component of `V` vanishes at the chart points
  have hV1 : ∀ pt : Chart, 0 < pt.1 →
      (D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt)
        (NearInst.chartY (D.level n).ε⁻¹ pt) 1 = 0 := by
    intro pt hs
    have hRpos : 0 < ((D.level n).params D.Pl).R := ((D.level n).params D.Pl).R_pos
    have hax : NearInst.chartY ((D.level n).params D.Pl).R pt ∉ axis :=
      IIIa.chartPoint_not_mem_axis hRpos hs
    have hraw1 : ((D.level n).params D.Pl).raw (NearInst.chartTau ((D.level n).params D.Pl).R pt)
        (NearInst.chartY ((D.level n).params D.Pl).R pt) 1 = 0 := by
      rw [((D.level n).params D.Pl).raw_eq_off_axis _ _ hax]
      exact Nv_chartPoint_apply_one hRpos _ hs
    have hinl1 : ∀ i : Fin 2, ((D.level n).params D.Pl).inlet i
        (NearInst.chartTau ((D.level n).params D.Pl).R pt)
        (NearInst.chartY ((D.level n).params D.Pl).R pt) 1 = 0 :=
      fun i => Nv_chartPoint_apply_one hRpos (((D.level n).params D.Pl).inletProfile i) hs
    change D.V n (NearInst.chartTau ((D.level n).params D.Pl).R pt)
      (NearInst.chartY ((D.level n).params D.Pl).R pt) 1 = 0
    rw [hVz]
    simp [Fin.sum_univ_two, hraw1, hinl1 0, hinl1 1]
  -- `|V| = √s|v| ≤ √s W|v|`
  have hVle : ∀ pt : Chart, 0 < pt.1 →
      ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt) (NearInst.chartY (D.level n).ε⁻¹ pt)‖ ≤
        Real.sqrt pt.1 * IIIa.transWeight D.K.mZ pt *
          ‖IIIa.chartCoeff ((D.level n).params D.Pl).R (D.V n) pt‖ := by
    intro pt hs
    rw [norm_chart_eq hs (hV1 pt hs)]
    have hW := one_le_transWeight' hmZ pt
    have h0 : 0 ≤ Real.sqrt pt.1 * ‖IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V pt‖ := by
      positivity
    calc Real.sqrt pt.1 * ‖IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V pt‖
        = Real.sqrt pt.1 * ‖IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V pt‖ * 1 := by ring
      _ ≤ Real.sqrt pt.1 * ‖IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V pt‖ *
            IIIa.transWeight D.K.mZ pt := mul_le_mul_of_nonneg_left hW h0
      _ = _ := by
        change _ = Real.sqrt pt.1 * IIIa.transWeight D.K.mZ pt *
          ‖IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V pt‖
        ring
  have h1 : ∀ pt : Chart, 0 < pt.1 →
      ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt)
        (NearInst.chartY (D.level n).ε⁻¹ pt)‖ ^ 2 ≤ K ^ 2 := by
    intro pt hs
    have := (hVle pt hs).trans ((hv.1 pt hs).trans hCK)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have h3 : ∀ pt : Chart, 0 < pt.1 → pt.1 ≤ 1 →
      ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt)
        (NearInst.chartY (D.level n).ε⁻¹ pt)‖ ^ 2 ≤ 2 * K ^ 2 * pt.1 := by
    intro pt hs hs1
    rcases le_or_gt pt.1 (1 / 2) with hh | hh
    · have hσ : 0 < 2 * pt.1 := by linarith
      have h3' := hv.2.2.1 (2 * pt.1) hσ (by linarith) pt hs (by linarith)
      have hb : ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt)
          (NearInst.chartY (D.level n).ε⁻¹ pt)‖ ≤ K * Real.sqrt (2 * pt.1) :=
        (hVle pt hs).trans (h3'.trans
          (mul_le_mul_of_nonneg_right hCK (Real.sqrt_nonneg _)))
      calc ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt)
            (NearInst.chartY (D.level n).ε⁻¹ pt)‖ ^ 2
          ≤ (K * Real.sqrt (2 * pt.1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = 2 * K ^ 2 * pt.1 := by
          rw [mul_pow, Real.sq_sqrt hσ.le]
          ring
    · calc ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt)
            (NearInst.chartY (D.level n).ε⁻¹ pt)‖ ^ 2
          ≤ K ^ 2 := h1 pt hs
        _ ≤ 2 * K ^ 2 * pt.1 := by nlinarith [sq_nonneg K]
  have hK4 : 0 ≤ C₄ * (D.level n).ν⁻¹ ^ k₄ := by positivity
  have hmain := vSq_ringL2_le hR (cOf_pos hν0) hK hK4 (D.level n).V h1 h3 het
  rw [inv_inv] at hmain
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hKdef, pow_add]
  ring

end VBgSq

end UnforcedLeray.Short.PartIIIb.Concrete

end
