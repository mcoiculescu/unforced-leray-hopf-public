import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3

/-!
# `PartIII-b:C/rep/8/2/3/3`: the `L²` bound `TML2`, decomposed

Source of record: `the November 2 reference manuscript` (73 pages), lines
5464-5465 (the weighted train coefficient), 5477-5482 ("In physical units the squared body norm
divided by `R²` uses the density `π s^{-5/2} ds dη`; the remaining powers `s^{7/2}` and `s^{11/2}`
are integrable at zero and give only viscosity polynomials at `1/ν`. ... Gaussian moments of fixed
order"), young train 5484-5495.

`TML2` (`Sub/PartIII-b_C_rep_8_2_3.lean`) asks for `‖s^{5/2}𝔴_4 1_{0<s≤1/ν}‖_{L²(srcMeasure)} ≤ P_ν`,
`srcMeasure c = π s^{-3/2} ds ⊗ dq/c dη|_{cell}` (`ageμ`, `Lib/AxisymmetricB/Lift.lean:47`).

## The argument

The square of the norm is `π ∫_0^{1/ν} s^{-3/2} s^5 ∫_cell 𝔴_4² dq/c dη ds`.  One more transverse
power in the pointwise weight pays for the `η`-integral: `𝔴_5 = (1+|η|)𝔴_4` (`trainWeight_succ_tl2`),
so a pointwise bound `𝔴_5 ≤ B` on the young range gives `𝔴_4² ≤ B²(1+|η|)^{-2} ≤ B²(1+η²)^{-1}`,
whose normalized cell integral is `≤ π` (`CellInvSq`), and `∫_0^T s^{-3/2}s^5 ds ≤ T^{9/2}`
(`AgeInt72`, the source's "`s^{7/2}` integrable at zero").  Hence
`‖youngWeight‖ ≤ π B T^{9/4} ≤ 4B ν^{-3}` (`ModelL2`, `youngL2_le`, `ν ≤ 1`, `T = 1/ν`).

The pointwise bound with weight `(1+|η|)^5` (`TMPtW 5`) is the bound `TMPt = TMPtW 4`
(`tmPt_eq_tmPtW`) of task `PartIII-b:C/rep/8/2/3/2` with one more transverse power; it holds for
every fixed weight since the transverse tails of the train are exponential (source 463-467
`sct:transverse`: on `0 ≤ s ≤ S_*` all fields and fixed derivatives have tails
`P(e^{-bl/c} + e^{-bl²/(C₀+νS_*)})` beyond `|η| ≥ C'/ν + 2 + l`, `c = ν^{-2}`), and in the band
`|η| < C'/ν + 2` the weight is `≤ (3 + C'/ν)^5`.  Measurability of the weight is not needed
(`eLpNorm_mono`).

## Contents

* `TMPtW m D dm dp`: the pointwise weighted train bound with transverse weight `(1+|η|)^m`;
  `TMPt D dm dp = TMPtW 4 D dm dp` by `rfl`; `tmPtW_mono` (lower weights follow).
* `youngModel T B`: the model `1_{(0,T]}(s) s^{5/2} B (1+|η|)^{-1}`; `youngWeight_le_model`.
* Calculus Props, all proved here: `AgeInt72` (`ageInt72`), `CellInvSq` (`cellInvSq`),
  `ModelSqInt` (`modelSqInt_of`), `ModelL2` (`modelL2_of`).
* Proved here: `trainWeight_succ_tl2`, `trainWeight_le_succ_tl2`, `trainWeight_mono_tl2`, `tmPtW_mono`,
  `youngWeight_le_model`, `lintegral_srcMeasure_prod`, `youngModel_enorm_sq`, `youngL2_le`,
  `tmL2_of`, and `tmL2_of_pt5 (h5 : TMPtW 5 D dm dp) : TML2 D dm dp`.  The only open input of
  `TML2` is `TMPtW 5`, organized in `PtWOrg.lean` (`tmPtW_of`, `tmL2_of_wdil`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The weight -/

theorem trainWeight_succ_tl2 (m : ℕ) (L : ReturnLevel) (p : Chart) :
    trainWeight (m + 1) L p = (1 + |p.2.2|) * trainWeight m L p := by
  unfold trainWeight
  rw [pow_succ]
  ring

theorem trainWeight_le_succ_tl2 (m : ℕ) (L : ReturnLevel) (p : Chart) :
    trainWeight m L p ≤ trainWeight (m + 1) L p := by
  rw [trainWeight_succ_tl2]
  have h0 := trainWeight_nonneg m L p
  have h1 : 0 ≤ |p.2.2| := abs_nonneg _
  nlinarith

theorem trainWeight_mono_tl2 {m m' : ℕ} (h : m ≤ m') (L : ReturnLevel) (p : Chart) :
    trainWeight m L p ≤ trainWeight m' L p := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (trainWeight_le_succ_tl2 _ L p)

/-! ## 2. The pointwise weighted bound with a general transverse weight -/

/-- **The weighted train coefficient is polynomially bounded on the young range, with transverse
weight `(1+|η|)^m`** (source 5464-5465, 5477-5482, 5484-5495; the transverse tails of
`sct:transverse`, 463-467, and the fixed-band comparison `sct:fixed-band`, 468-478): for large `n`,
`𝔴_m(s,q,η) ≤ C ν^{-k}` on `0 < s ≤ 1/ν`, all `(q, η)`.  `m = 4` is `TMPt`. -/
def TMPtW (m : ℕ) (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ p : Chart,
    0 < p.1 → p.1 ≤ 1 / (D.level n).ν → trainWeight m (D.level n) p ≤ C * (D.level n).ν⁻¹ ^ k

theorem tmPt_eq_tmPtW (D : SeqData) (dm dp : ℝ) : TMPt D dm dp = TMPtW 4 D dm dp := rfl

/-- A bound with a larger transverse weight gives the bound with a smaller one. -/
theorem tmPtW_mono {m m' : ℕ} (h : m ≤ m') (D : SeqData) {dm dp : ℝ}
    (hW : TMPtW m' D dm dp) : TMPtW m D dm dp := by
  intro hst
  obtain ⟨C, k, e⟩ := hW hst
  exact ⟨C, k, e.mono fun n hn p hp hq => (trainWeight_mono_tl2 h _ p).trans (hn p hp hq)⟩

/-! ## 3. The model and the `L²` calculus -/

/-- The model majorant `1_{(0,T]}(s) s^{5/2} B (1+|η|)^{-1}` of `youngWeight` when `𝔴_5 ≤ B`. -/
def youngModel (T B : ℝ) (p : Chart) : ℝ :=
  (Ioc 0 T).indicator (fun s => s ^ (5 / 2 : ℝ)) p.1 * B * (1 + |p.2.2|)⁻¹

theorem youngWeight_le_model (L : ReturnLevel) {B : ℝ}
    (h : ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν → trainWeight 5 L p ≤ B) (p : Chart) :
    ‖youngWeight L p‖ ≤ ‖youngModel (1 / L.ν) B p‖ := by
  unfold youngWeight youngModel
  by_cases hp : p.1 ∈ Ioc 0 (1 / L.ν)
  · have hp' : p ∈ {p : Chart | p.1 ∈ Ioc 0 (1 / L.ν)} := hp
    rw [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
    have h5 : (1 + |p.2.2|) * trainWeight 4 L p ≤ B := by
      rw [← trainWeight_succ_tl2]; exact h p hp.1 hp.2
    have hη : 0 < 1 + |p.2.2| := by positivity
    have h4 : trainWeight 4 L p ≤ B * (1 + |p.2.2|)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hη, mul_comm]; exact h5
    have hs : 0 ≤ p.1 ^ (5 / 2 : ℝ) := Real.rpow_nonneg hp.1.le _
    have hw : 0 ≤ trainWeight 4 L p := trainWeight_nonneg 4 L p
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs hw), mul_assoc,
      abs_of_nonneg (mul_nonneg hs (hw.trans h4))]
    exact mul_le_mul_of_nonneg_left h4 hs
  · have hp' : p ∉ {p : Chart | p.1 ∈ Ioc 0 (1 / L.ν)} := hp
    rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]
    simp

/-- **Product integrals for `srcMeasure`** (Tonelli for `ageμ`, `Lib/AxisymmetricB/Lift.lean:47`):
`∫ f(s)g(q,η) dsrcMeasure = π (∫_0^∞ s^{-3/2} f(s) ds)(∫ g dq/c dη|_{cell})`. -/
theorem lintegral_srcMeasure_prod (c : ℝ) {f : ℝ → ℝ≥0∞} {g : ℝ × ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ p, f p.1 * g p.2 ∂srcMeasure c =
      ENNReal.ofReal Real.pi * ((∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * f s) *
        ∫⁻ x, g x ∂UnforcedLeray.Cyl.avgμ c) := by
  unfold srcMeasure ageμ
  rw [lintegral_smul_measure, lintegral_prod_mul hf.aemeasurable hg.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ofReal_rpow _) hf, smul_eq_mul]
  rfl

/-- **The age integral** (source 5477-5480: "the remaining powers `s^{7/2}` ... are integrable at
zero"): `∫_0^T s^{-3/2}s^5 ds = (2/9)T^{9/2} ≤ T^{9/2}`. -/
def AgeInt72 : Prop :=
  ∀ T : ℝ, 0 < T →
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s) ≤
      ENNReal.ofReal (T ^ (9 / 2 : ℝ))

/-- **The transverse moment of the normalized cell** (source 5477-5482, "Gaussian moments of fixed
order" with the one extra transverse power): `∫_cell (1+|η|)^{-2} dq/c dη ≤ ∫_ℝ (1+η²)^{-1} dη = π`
(`Cyl.avgμ c = c⁻¹ dq dη` on `[-c/2, c/2) × ℝ`). -/
def CellInvSq : Prop :=
  ∀ c : ℝ, 0 < c →
    ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 2)⁻¹) ∂UnforcedLeray.Cyl.avgμ c ≤
      ENNReal.ofReal Real.pi

theorem ageInt72 : AgeInt72 := by
  intro T hT
  have key : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
      ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s) ≤
        (Ioc 0 T).indicator (fun _ => ENNReal.ofReal (T ^ (7 / 2 : ℝ))) s := by
    intro s hs
    by_cases hsT : s ∈ Ioc 0 T
    · rw [Set.indicator_of_mem hsT, Set.indicator_of_mem hsT,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hsT.1.le _),
        ← Real.rpow_add hsT.1]
      refine ENNReal.ofReal_le_ofReal ?_
      have e : (-3 / 2 : ℝ) + 5 = 7 / 2 := by norm_num
      rw [e]
      exact Real.rpow_le_rpow hsT.1.le hsT.2 (by norm_num)
    · rw [Set.indicator_of_notMem hsT, Set.indicator_of_notMem hsT]
      simp
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s)
      ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioc 0 T).indicator (fun _ => ENNReal.ofReal (T ^ (7 / 2 : ℝ))) s :=
        setLIntegral_mono' measurableSet_Ioi key
    _ ≤ ∫⁻ s, (Ioc 0 T).indicator (fun _ => ENNReal.ofReal (T ^ (7 / 2 : ℝ))) s :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (T ^ (7 / 2 : ℝ)) * volume (Ioc 0 T) :=
        lintegral_indicator_const measurableSet_Ioc _
    _ = ENNReal.ofReal (T ^ (9 / 2 : ℝ)) := by
        rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _),
          ← Real.rpow_add_one hT.ne']
        norm_num

theorem cellInvSq : CellInvSq := by
  intro c hc
  have hG : Measurable fun η : ℝ => ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hprod : ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 2)⁻¹) ∂UnforcedLeray.Cyl.cellμ c =
      ENNReal.ofReal c * ∫⁻ η, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) := by
    unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    have e := lintegral_prod_mul (μ := volume.restrict (Ico (-c / 2) (c / 2)))
      (ν := (volume : Measure ℝ)) (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
      hG.aemeasurable
    simp only [one_mul] at e
    rw [e, lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico]
    congr 2
    ring
  have hle : ∫⁻ η, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) ≤ ENNReal.ofReal Real.pi := by
    rw [← integral_univ_inv_one_add_sq, ofReal_integral_eq_lintegral_ofReal
      integrable_inv_one_add_sq (ae_of_all _ fun x => by positivity)]
    refine lintegral_mono fun η => ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 < 1 + η ^ 2 := by positivity
    refine inv_anti₀ h1 ?_
    have := abs_nonneg η
    nlinarith [sq_abs η]
  unfold UnforcedLeray.Cyl.avgμ
  rw [lintegral_smul_measure, hprod, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one,
    one_mul]
  exact hle

/-- **The model integral** (source 5477-5482): `‖youngModel T B‖_{L²(srcMeasure c)}² ≤
π · B²T^{9/2} · π`, so `‖youngModel T B‖ ≤ πBT^{9/4} ≤ 4BT^{9/4}`. -/
def ModelL2 : Prop :=
  ∀ c T B : ℝ, 0 < c → 0 < T → 0 ≤ B →
    eLpNorm (youngModel T B) 2 (srcMeasure c) ≤ ENNReal.ofReal (4 * B * T ^ (9 / 4 : ℝ))

/-- **The square of the model norm** (source 5477-5482): `∫ |youngModel T B|² dsrcMeasure c ≤
π · (B² ∫_0^T s^{7/2} ds) · π ≤ π²B²T^{9/2}` (from `AgeInt72`, `CellInvSq`). -/
def ModelSqInt : Prop :=
  ∀ c T B : ℝ, 0 < c → 0 < T → 0 ≤ B →
    ∫⁻ p, ‖youngModel T B p‖ₑ ^ (2 : ℝ) ∂srcMeasure c ≤
      ENNReal.ofReal (Real.pi ^ 2 * B ^ 2 * T ^ (9 / 2 : ℝ))

theorem youngModel_enorm_sq (T B : ℝ) (p : Chart) :
    ‖youngModel T B p‖ₑ ^ (2 : ℝ) =
      (ENNReal.ofReal (B ^ 2) * ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) p.1)) *
        ENNReal.ofReal (((1 + |p.2.2|) ^ 2)⁻¹) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul (sq_nonneg B), ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg B) ?_)]
  · congr 1
    rw [Real.rpow_two, sq_abs]
    unfold youngModel
    by_cases hs : p.1 ∈ Ioc 0 T
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      have e : (p.1 ^ (5 / 2 : ℝ)) ^ 2 = p.1 ^ (5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]; norm_num
      rw [mul_pow, mul_pow, e, inv_pow]
      ring
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
      ring
  · by_cases hs : p.1 ∈ Ioc 0 T
    · rw [Set.indicator_of_mem hs]; exact Real.rpow_nonneg hs.1.le _
    · rw [Set.indicator_of_notMem hs]

theorem modelSqInt_of (h1 : AgeInt72) (h2 : CellInvSq) : ModelSqInt := by
  intro c T B hc hT hB
  have hF : Measurable fun s : ℝ => ENNReal.ofReal (B ^ 2) *
      ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      ((measurable_id.pow_const _).indicator measurableSet_Ioc))
  have hG : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (((1 + |x.2|) ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  calc ∫⁻ p, ‖youngModel T B p‖ₑ ^ (2 : ℝ) ∂srcMeasure c
      = ∫⁻ p, (ENNReal.ofReal (B ^ 2) *
          ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) p.1)) *
          ENNReal.ofReal (((1 + |p.2.2|) ^ 2)⁻¹) ∂srcMeasure c :=
        lintegral_congr fun p => youngModel_enorm_sq T B p
    _ = ENNReal.ofReal Real.pi * ((∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          (ENNReal.ofReal (B ^ 2) *
            ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s))) *
          ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 2)⁻¹) ∂UnforcedLeray.Cyl.avgμ c) :=
        lintegral_srcMeasure_prod c hF hG
    _ ≤ ENNReal.ofReal Real.pi *
          ((ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (T ^ (9 / 2 : ℝ))) *
            ENNReal.ofReal Real.pi) := by
        gcongr
        · calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
                (ENNReal.ofReal (B ^ 2) *
                  ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s))
              = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (B ^ 2) *
                  (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
                    ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s)) :=
                lintegral_congr fun s => by ring
            _ = ENNReal.ofReal (B ^ 2) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
                    ENNReal.ofReal ((Ioc 0 T).indicator (fun s => s ^ (5 : ℝ)) s) :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (T ^ (9 / 2 : ℝ)) := by
                gcongr; exact h1 T hT
        · exact h2 c hc
    _ = ENNReal.ofReal (Real.pi ^ 2 * B ^ 2 * T ^ (9 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg B), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul Real.pi_pos.le]
        congr 1
        ring

/-- The model norm from its square: `(π²B²T^{9/2})^{1/2} = πBT^{9/4} ≤ 4BT^{9/4}`. -/
theorem modelL2_of (h : ModelSqInt) : ModelL2 := by
  intro c T B hc hT hB
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [e2]
  calc (∫⁻ x, ‖youngModel T B x‖ₑ ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.pi ^ 2 * B ^ 2 * T ^ (9 / 2 : ℝ))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (h c T B hc hT hB) (by norm_num)
    _ = ENNReal.ofReal ((Real.pi ^ 2 * B ^ 2 * T ^ (9 / 2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ ENNReal.ofReal (4 * B * T ^ (9 / 4 : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (Real.pi ^ 2 * B ^ 2 * T ^ (9 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
            Real.pi * B * T ^ (9 / 4 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_natCast Real.pi 2, ← Real.rpow_mul Real.pi_pos.le,
            ← Real.rpow_natCast B 2, ← Real.rpow_mul hB, ← Real.rpow_mul hT.le]
          norm_num
        rw [e]
        have hT' : 0 ≤ T ^ (9 / 4 : ℝ) := Real.rpow_nonneg hT.le _
        have := Real.pi_le_four
        have hBT : 0 ≤ B * T ^ (9 / 4 : ℝ) := mul_nonneg hB hT'
        nlinarith

/-- The `L²` bound of `youngWeight` from a pointwise bound of `𝔴_5` on the young range. -/
theorem youngL2_le (hM : ModelL2) (L : ReturnLevel) {B : ℝ} (hB : 0 ≤ B) (hν : L.ν ≤ 1)
    (h : ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν → trainWeight 5 L p ≤ B) :
    eLpNorm (youngWeight L) 2 (srcMeasure (cOf L.ν)) ≤ ENNReal.ofReal (4 * B * L.ν⁻¹ ^ 3) := by
  have hνp := L.ν_pos
  have hT : 1 ≤ 1 / L.ν := by rw [one_le_div hνp]; exact hν
  calc eLpNorm (youngWeight L) 2 (srcMeasure (cOf L.ν))
      ≤ eLpNorm (youngModel (1 / L.ν) B) 2 (srcMeasure (cOf L.ν)) :=
        eLpNorm_mono (youngWeight_le_model L h)
    _ ≤ ENNReal.ofReal (4 * B * (1 / L.ν) ^ (9 / 4 : ℝ)) :=
        hM _ _ _ (cOf_pos hνp) (by positivity) hB
    _ ≤ ENNReal.ofReal (4 * B * L.ν⁻¹ ^ 3) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
        have e : (1 / L.ν) ^ (9 / 4 : ℝ) ≤ (1 / L.ν) ^ ((3 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
        rw [Real.rpow_natCast] at e
        rw [one_div] at e ⊢
        exact e

/-! ## 4. Assembly -/

/-- **`TML2` from the model integral and the pointwise bound with weight `(1+|η|)^5`.** -/
theorem tmL2_of (D : SeqData) {dm dp : ℝ} (hM : ModelL2) (h5 : TMPtW 5 D dm dp) :
    TML2 D dm dp := by
  intro hst
  obtain ⟨C, k, e⟩ := h5 hst
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨4 * C, k + 3, ?_⟩
  filter_upwards [e, hle] with n a b
  have hν1 : (D.level n).ν ≤ 1 := b.1
  have hνp := (D.level n).ν_pos
  have hB : 0 ≤ C * (D.level n).ν⁻¹ ^ k :=
    (trainWeight_nonneg 5 (D.level n) (1 / (D.level n).ν, (0, 0))).trans
      (a _ (by simp only; positivity) le_rfl)
  calc eLpNorm (youngWeight (D.level n)) 2 (srcMeasure (cOf (D.level n).ν))
      ≤ ENNReal.ofReal (4 * (C * (D.level n).ν⁻¹ ^ k) * (D.level n).ν⁻¹ ^ 3) :=
        youngL2_le hM (D.level n) hB hν1 a
    _ = ENNReal.ofReal (4 * C * (D.level n).ν⁻¹ ^ (k + 3)) := by
        rw [pow_add]; ring_nf

/-- **`TML2` from the pointwise bound with transverse weight `(1+|η|)^5`** (all calculus proved). -/
theorem tmL2_of_pt5 (D : SeqData) {dm dp : ℝ} (h5 : TMPtW 5 D dm dp) : TML2 D dm dp :=
  tmL2_of D (modelL2_of (modelSqInt_of ageInt72 cellInvSq)) h5

end UnforcedLeray.Short.PartIIIb.Concrete
