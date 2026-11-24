import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3.Reduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.EnergyIBP

/-!
# `SmoothRepPairing`: classical energy pairing on the smooth representative
(task `PartIII-b:C/flatset/col/7/1/1/3/1`)

Source of record `the November 2 reference manuscript` 1650-1656, 1684-1689.
Combines the test pairing bound (`TestPairing.lean`) with the age and cell integration by parts
(`EnergyIBP.lean`), sends the `η`-cutoff `R → ∞` to kill the `O(1/R)` cutoff error, and then
takes the monotone limit `S = R = n + 1 → ∞` over exhausting boxes of `Ioi 0 ×ˢ B0579.cell c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- Open-half-open box `(0, S) × ([-c/2, c/2) × (-R, R))` where `thetaS S = 1` and `chiR R = 1`. -/
def boxSR (c S R : ℝ) : Set Chart :=
  Ioo (0 : ℝ) S ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Ioo (-R) R)

theorem measurableSet_boxSR (c S R : ℝ) : MeasurableSet (boxSR c S R) :=
  measurableSet_Ioo.prod (measurableSet_Ico.prod measurableSet_Ioo)

theorem boxSR_subset_cyl (c S R : ℝ) : boxSR c S R ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
  fun _ hp => ⟨hp.1.1, ⟨hp.2.1, mem_univ _⟩⟩

theorem boxSR_mono {c S₁ S₂ R₁ R₂ : ℝ} (hS : S₁ ≤ S₂) (hR : R₁ ≤ R₂) :
    boxSR c S₁ R₁ ⊆ boxSR c S₂ R₂ :=
  fun _ hp => ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 hS⟩,
    ⟨hp.2.1, ⟨lt_of_le_of_lt (neg_le_neg hR) hp.2.2.1, lt_of_lt_of_le hp.2.2.2 hR⟩⟩⟩

theorem iUnion_boxSR_nat (c : ℝ) :
    (⋃ n : ℕ, boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1)) = Ioi (0 : ℝ) ×ˢ B0579.cell c := by
  ext p
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact boxSR_subset_cyl c _ _ hn
  · intro hp
    obtain ⟨n, hn⟩ := exists_nat_gt (max p.1 |p.2.2|)
    have hp1 : p.1 < (n : ℝ) + 1 :=
      lt_trans (lt_of_le_of_lt (le_max_left _ _) hn) (by linarith)
    have hp2 : |p.2.2| < (n : ℝ) + 1 :=
      lt_trans (lt_of_le_of_lt (le_max_right _ _) hn) (by linarith)
    exact ⟨n, ⟨⟨hp.1, hp1⟩, ⟨hp.2.1, abs_lt.1 hp2⟩⟩⟩

/-- Un-cut velocity energy density `s^{-3/2} (μ + 1/4) |b|²`. -/
def rawV (μ : ℝ) (b : Chart → Fin 2 → ℂ) (p : Chart) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * vnorm2 (b p) ^ 2)

/-- Un-cut gradient energy density `s^{-1/2} ν |∇b|²`. -/
def rawG (ν : ℝ) (b : Chart → Fin 2 → ℂ) (p : Chart) : ℝ :=
  p.1 ^ (-(1 / 2 : ℝ)) * (ν * tnorm2 (fun i j => cellGrad b p i j) ^ 2)

theorem energyMainV_eq_rawV_on_boxSR {c μ S R : ℝ} (hR : 0 < R) (b : Chart → Fin 2 → ℂ)
    {p : Chart} (hp : p ∈ boxSR c S R) :
    energyMainV μ S R b p = rawV μ b p := by
  unfold energyMainV rawV
  have hth : thetaS S p.1 = 1 := thetaS_eq_one hp.1.2.le
  have hch : chiR R p.2.2 = 1 :=
    chiR_eq_one hR (abs_le.2 ⟨hp.2.2.1.le, hp.2.2.2.le⟩)
  rw [hth, hch]
  ring

theorem energyMainG_eq_rawG_on_boxSR {c ν S R : ℝ} (hR : 0 < R) (b : Chart → Fin 2 → ℂ)
    {p : Chart} (hp : p ∈ boxSR c S R) :
    energyMainG ν S R b p = rawG ν b p := by
  unfold energyMainG rawG
  have hth : thetaS S p.1 = 1 := thetaS_eq_one hp.1.2.le
  have hch : chiR R p.2.2 = 1 :=
    chiR_eq_one hR (abs_le.2 ⟨hp.2.2.1.le, hp.2.2.2.le⟩)
  rw [hth, hch]
  ring

/-- On any fixed box `boxSR c S R` (`R > 0`), the sum of the two `lintegral`s is bounded by
`c · √(Gn · A) + C / R'` for every `R' ≥ R`, hence by `c · √(Gn · A)`. -/
theorem boxSR_lintegral_le {c ν μ s0 : ℝ} {hc : 0 < c} {R0 : Hsp c →L[ℝ] Hsp c} {g : Hsp c}
    (hctx : ClassicalCtx c ν μ hc R0 g) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (hbe : b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)) (hs0 : 0 < s0)
    (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (S : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ p in boxSR c S R, ENNReal.ofReal (rawV μ b p)) +
      (∫⁻ p in boxSR c S R, ENNReal.ofReal (rawG ν b p)) ≤
      ENNReal.ofReal c *
        ((∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2))) *
          (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)))) ^ (1 / 2 : ℝ) := by
  have hν : 0 < ν := hctx.1
  have hμ : 0 < μ + 1 / 4 := hctx.2.1
  obtain ⟨C, hC0, hCerr⟩ := exists_energyErr_bound hctx hb hbe hs0 hz S
  set RHS := ENNReal.ofReal c *
    ((∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2))) *
      (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)))) ^ (1 / 2 : ℝ)
  -- First show that for any `R' ≥ R`, the `boxSR c S R` lintegral is `≤ RHS + ofReal (C / R')`
  have hstep : ∀ R' : ℝ, R ≤ R' →
      (∫⁻ p in boxSR c S R, ENNReal.ofReal (rawV μ b p)) +
        (∫⁻ p in boxSR c S R, ENNReal.ofReal (rawG ν b p)) ≤
        RHS + ENNReal.ofReal (C / R') := by
    intro R' hRR'
    have hR' : 0 < R' := lt_of_lt_of_le hR hRR'
    have hpair := smoothRep_test_pairing hctx hb hbe
      (zetaCut_isMeridTest hb hs0 hz S hR') (norm_zetaCut_le S R' b)
    have hibp := integral_resolventTest_zetaCut_ge (μ := μ) (ν := ν) (S := S) hb hs0 hz hR'
    have herr := hCerr R' hR'
    set IV := ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyMainV μ S R' b p
    set IG := ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyMainG ν S R' b p
    have hMV0 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c, 0 ≤ energyMainV μ S R' b p := by
      intro p hp
      unfold energyMainV
      have hp0 : (0 : ℝ) < p.1 := hp.1
      exact mul_nonneg (Real.rpow_nonneg hp0.le _)
        (mul_nonneg (mul_nonneg (mul_nonneg hμ.le (thetaS_nonneg S p.1))
          (chiR_nonneg R' p.2.2)) (sq_nonneg _))
    have hMG0 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c, 0 ≤ energyMainG ν S R' b p := by
      intro p hp
      unfold energyMainG
      have hp0 : (0 : ℝ) < p.1 := hp.1
      exact mul_nonneg (Real.rpow_nonneg hp0.le _)
        (mul_nonneg (mul_nonneg (mul_nonneg hν.le (thetaS_nonneg S p.1))
          (chiR_nonneg R' p.2.2)) (sq_nonneg _))
    have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
      measurableSet_Ioi.prod (B0579.measurableSet_cell c)
    have hIV0 : 0 ≤ IV := setIntegral_nonneg hSm hMV0
    have hIG0 : 0 ≤ IG := setIntegral_nonneg hSm hMG0
    have hIV_eq : ENNReal.ofReal IV =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ENNReal.ofReal (energyMainV μ S R' b p) :=
      ofReal_integral_eq_lintegral_ofReal (integrableOn_energyMainV hb hs0 hz hR')
        ((ae_restrict_iff' hSm).2 (Eventually.of_forall hMV0))
    have hIG_eq : ENNReal.ofReal IG =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ENNReal.ofReal (energyMainG ν S R' b p) :=
      ofReal_integral_eq_lintegral_ofReal (integrableOn_energyMainG hb hs0 hz hR')
        ((ae_restrict_iff' hSm).2 (Eventually.of_forall hMG0))
    have hle_real : IV + IG - C / R' ≤
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          p.1 ^ (-(3 / 2 : ℝ)) * (inner ℂ (resolventTest ν μ (zetaCut S R' b) p) (bm b p)).re := by
      linarith
    have hle_enn : ENNReal.ofReal IV + ENNReal.ofReal IG ≤ RHS + ENNReal.ofReal (C / R') := by
      calc ENNReal.ofReal IV + ENNReal.ofReal IG
          = ENNReal.ofReal (IV + IG) := (ENNReal.ofReal_add hIV0 hIG0).symm
        _ = ENNReal.ofReal ((IV + IG - C / R') + C / R') := by ring_nf
        _ ≤ ENNReal.ofReal (IV + IG - C / R') + ENNReal.ofReal (C / R') :=
            ENNReal.ofReal_add_le
        _ ≤ RHS + ENNReal.ofReal (C / R') :=
            add_le_add ((ENNReal.ofReal_le_ofReal hle_real).trans hpair) le_rfl
    have hboxV : ∫⁻ p in boxSR c S R, ENNReal.ofReal (rawV μ b p) ≤ ENNReal.ofReal IV := by
      rw [hIV_eq]
      have hcongr : ∫⁻ p in boxSR c S R, ENNReal.ofReal (rawV μ b p) =
          ∫⁻ p in boxSR c S R, ENNReal.ofReal (energyMainV μ S R' b p) :=
        setLIntegral_congr_fun (measurableSet_boxSR c S R) fun p hp => by
          rw [energyMainV_eq_rawV_on_boxSR hR' b (boxSR_mono le_rfl hRR' hp)]
      rw [hcongr]
      exact lintegral_mono_set (boxSR_subset_cyl c S R)
    have hboxG : ∫⁻ p in boxSR c S R, ENNReal.ofReal (rawG ν b p) ≤ ENNReal.ofReal IG := by
      rw [hIG_eq]
      have hcongr : ∫⁻ p in boxSR c S R, ENNReal.ofReal (rawG ν b p) =
          ∫⁻ p in boxSR c S R, ENNReal.ofReal (energyMainG ν S R' b p) :=
        setLIntegral_congr_fun (measurableSet_boxSR c S R) fun p hp => by
          rw [energyMainG_eq_rawG_on_boxSR hR' b (boxSR_mono le_rfl hRR' hp)]
      rw [hcongr]
      exact lintegral_mono_set (boxSR_subset_cyl c S R)
    exact (add_le_add hboxV hboxG).trans hle_enn
  -- Now eliminate `C / R'` via `ENNReal.le_of_forall_pos_le_add`
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε0 : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.2 hε
  set R' : ℝ := max R (C / (ε : ℝ) + 1)
  have hRR' : R ≤ R' := le_max_left _ _
  have hCR' : C / R' ≤ (ε : ℝ) := by
    have hR'pos : 0 < R' := lt_of_lt_of_le hR hRR'
    rw [div_le_iff₀ hR'pos]
    have h1 : C / (ε : ℝ) ≤ R' := by
      have : C / (ε : ℝ) + 1 ≤ R' := le_max_right _ _
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hε0.le
    have h3 : (ε : ℝ) * (C / (ε : ℝ)) = C := mul_div_cancel₀ C hε0.ne'
    linarith
  have hof : ENNReal.ofReal (C / R') ≤ (ε : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hCR'
  exact (hstep R' hRR').trans (add_le_add le_rfl hof)

/-- Monotone exhaustion of `Ioi 0 ×ˢ B0579.cell c` by `boxSR c (n + 1) (n + 1)`. -/
theorem cyl_lintegral_eq_iSup_boxSR (c : ℝ) {F : Chart → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, F p =
      ⨆ n : ℕ, ∫⁻ p in boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1), F p := by
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  rw [← lintegral_indicator hSm]
  have hBm : ∀ n : ℕ, MeasurableSet (boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1)) :=
    fun n => measurableSet_boxSR c _ _
  simp_rw [← lintegral_indicator (hBm _)]
  have hmono : Monotone (fun n : ℕ =>
      (boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1)).indicator F) := by
    intro n m hnm p
    have hsub : boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1) ⊆
        boxSR c ((m : ℝ) + 1) ((m : ℝ) + 1) := by
      have hle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
      exact boxSR_mono hle hle
    exact indicator_le_indicator_of_subset hsub (fun _ => zero_le) p
  rw [← lintegral_iSup (fun n => hF.indicator (hBm n)) hmono]
  congr 1
  funext p
  rw [← iUnion_boxSR_nat c]
  by_cases hp : p ∈ ⋃ n : ℕ, boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1)
  · rw [indicator_of_mem hp]
    rcases mem_iUnion.1 hp with ⟨n₀, hn₀⟩
    refine le_antisymm ?_ ?_
    · have := le_iSup (fun n : ℕ => (boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1)).indicator F p) n₀
      rwa [indicator_of_mem hn₀] at this
    · refine iSup_le fun n => ?_
      by_cases hpn : p ∈ boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1)
      · rw [indicator_of_mem hpn]
      · rw [indicator_of_notMem hpn]
        exact zero_le
  · rw [indicator_of_notMem hp]
    refine le_antisymm zero_le (iSup_le fun n => ?_)
    have hpn : p ∉ boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1) :=
      fun h => hp (mem_iUnion.2 ⟨n, h⟩)
    rw [indicator_of_notMem hpn]

/-- Relation between `c * (k * ∫⁻ F ∂(ageμ c a))` and the cylinder `lintegral`. -/
theorem ofReal_c_mul_lintegral_ageμ {c : ℝ} (hc : 0 < c) (a a' : ℝ) (haa' : a = a')
    {k : ℝ} (hk : 0 ≤ k) {F : Chart → ℝ} (hF : Measurable (fun p => ENNReal.ofReal (F p))) :
    ENNReal.ofReal c * (ENNReal.ofReal k * ∫⁻ p, ENNReal.ofReal (F p) ∂(ageμ c a)) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ENNReal.ofReal (p.1 ^ a' * (k * F p)) := by
  subst haa'
  have hq : qCell c = B0579.cell c := by
    unfold qCell B0579.cell
    rw [neg_div]
  rw [lintegral_ageμ hc a hF, hq, ← mul_assoc,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) fun p hp => ?_
  have hp0 : (0 : ℝ) < p.1 := hp.1
  have hr0 : 0 ≤ p.1 ^ a := Real.rpow_nonneg hp0.le a
  rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg hc.le hk)]
  congr 1
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

theorem smoothRepPairing : SmoothRepPairing := by
  intro c ν μ hc R0 g hctx b hb hbe
  have hν : 0 < ν := hctx.1
  have hμ : 0 < μ + 1 / 4 := hctx.2.1
  obtain ⟨s0, hs0, hz⟩ := smoothRep_zero_below hctx hb hbe
  -- Measurability of the integrands
  have hmeasV : Measurable fun p : Chart => vnorm2 (b p) ^ 2 := by
    unfold vnorm2
    refine Measurable.pow_const ?_ 2
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (hb.1 i).norm.pow_const 2
  have hmeasG : Measurable fun p : Chart => tnorm2 (fun i j => cellGrad b p i j) ^ 2 := by
    have hgm := sfcGradMeas c b hb
    unfold tnorm2
    refine Measurable.pow_const ?_ 2
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact (hgm i j).norm.pow_const 2
  have hmV : Measurable fun p : Chart => ENNReal.ofReal (rawV μ b p) := by
    unfold rawV
    exact ENNReal.measurable_ofReal.comp
      ((measurable_fst.pow_const _).mul (measurable_const.mul hmeasV))
  have hmG : Measurable fun p : Chart => ENNReal.ofReal (rawG ν b p) := by
    unfold rawG
    exact ENNReal.measurable_ofReal.comp
      ((measurable_fst.pow_const _).mul (measurable_const.mul hmeasG))
  -- Prove the inequality after multiplying both sides by `ENNReal.ofReal c` (`0 < c`)
  have hmul : ENNReal.ofReal c *
      (ENNReal.ofReal (μ + 1 / 4) *
          (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2))) +
        ENNReal.ofReal ν *
          (∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => cellGrad b p i j) ^ 2) ∂(ageμ c (-1 / 2)))) ≤
      ENNReal.ofReal c *
        ((∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2))) *
          (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)))) ^ (1 / 2 : ℝ) := by
    rw [mul_add,
      ofReal_c_mul_lintegral_ageμ hc (-3 / 2) (-(3 / 2 : ℝ)) (by ring) hμ.le
        (ENNReal.measurable_ofReal.comp hmeasV),
      ofReal_c_mul_lintegral_ageμ hc (-1 / 2) (-(1 / 2 : ℝ)) (by ring) hν.le
        (ENNReal.measurable_ofReal.comp hmeasG)]
    change (∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ENNReal.ofReal (rawV μ b p)) +
        (∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ENNReal.ofReal (rawG ν b p)) ≤ _
    rw [cyl_lintegral_eq_iSup_boxSR c hmV, cyl_lintegral_eq_iSup_boxSR c hmG, ENNReal.iSup_add]
    refine iSup_le fun n => ?_
    rw [ENNReal.add_iSup]
    refine iSup_le fun m => ?_
    set k : ℕ := max n m
    have hnk : boxSR c ((n : ℝ) + 1) ((n : ℝ) + 1) ⊆ boxSR c ((k : ℝ) + 1) ((k : ℝ) + 1) := by
      have hle : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right (le_max_left n m) 1
      exact boxSR_mono hle hle
    have hmk : boxSR c ((m : ℝ) + 1) ((m : ℝ) + 1) ⊆ boxSR c ((k : ℝ) + 1) ((k : ℝ) + 1) := by
      have hle : (m : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right (le_max_right n m) 1
      exact boxSR_mono hle hle
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact (add_le_add (lintegral_mono_set hnk) (lintegral_mono_set hmk)).trans
      (boxSR_lintegral_le hctx hb hbe hs0 hz ((k : ℝ) + 1) hkpos)
  have hcancel : ∀ X : ℝ≥0∞, ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * X) = X := fun X => by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_mul]
  have h1 := mul_le_mul_of_nonneg_left hmul (zero_le (a := ENNReal.ofReal c⁻¹))
  rwa [hcancel, hcancel] at h1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
