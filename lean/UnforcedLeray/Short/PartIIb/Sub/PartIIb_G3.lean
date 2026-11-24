import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphFlat
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-b, task `PartII-b:G3`: Intermediate age-window operator comparison (`WindowComparison`, SP 2438–2463)

Source of record: `the November 2 reference manuscript`
(SP), lines 2438–2463:
On the intermediate age window `σ = ε^a ≤ s ≤ S = ε^{-b}` (`a, b > 0`), choosing transverse width
`L = C_D (c/ν + √S + 1)` in `(sct:transverse)` (SP 463–467) splits `windowAgeSet σ S` into:
1. the observation box `obsBox σ S L` (`|η| ≤ L`), where a smooth cutoff
   `ϑ : ObsCut (σ / 2) (2 * S) (L + 1) Γ` equal to `1` on `obsBox σ S L` with
   `Γ ≤ C_Γ ν^{-3} ε^{-8(a+b)}` and `LocalInteractionComparison` (`T20`) bound
   `hpIndNorm p.c (obsBox σ S L) (Ke f - K0 f)` by `C_box ν^{-k_box} ε^{2/539 - N(a+b)} ‖f‖`
   with `N = 8 * k_loc` (`WindowBoxCutoffBound`, `PartII-b:G3/1`);
2. the transverse exterior `windowExtSet σ S L` (`|η| > L`), where increasing `C_D` in
   `sct:transverse` makes all coefficient tails of `b_raw` and `v_c` at most `𝒫_ν e^{-D/ν}` on
   `[σ, S]`, bounding `hpIndNorm p.c (windowExtSet σ S L) (Ke f - K0 f)` by
   `C_tail ν^{-k_tail} e^{-D/ν} ‖f‖` (`WindowTransverseTailBound`, `PartII-b:G3/2`).

## Proved here (zero `sorry`)

* `window_eps_inv_bounds`, `window_gamma_pow_mul_rate`, `window_period_le_one_exists`:
  exponent and parameter bounds on `[ε^a, ε^{-b}]`;
* `measurableSet_windowExtSet`, `hpIndNorm_windowAgeSet_le_box_add_ext`:
  the `H_p` indicator norm triangle inequality splitting `windowAgeSet σ S` into `obsBox σ S L`
  and `windowExtSet σ S L`;
* `windowComparison_of_box_tail`: conditional proof of `WindowComparison` from `WindowBoxCutoffBound`
  (`PartII-b:G3/1`), `WindowTransverseTailBound` (`PartII-b:G3/2`),
  `LocalInteractionComparison` (`T20`), and `YoungLateOperatorBounds` (`G2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Window parameter algebra and `H_p` indicator splitting (SP 2445–2463) -/

/-- Exterior transverse tail of the age window `[σ, S]`: `σ ≤ s ≤ S` and `L < |η|`. -/
def windowExtSet (σ S L : ℝ) : Set Coord :=
  {x : Coord | (σ ≤ x.1 ∧ x.1 ≤ S) ∧ L < |x.2.2|}

theorem measurableSet_windowExtSet (σ S L : ℝ) : MeasurableSet (windowExtSet σ S L) := by
  refine (measurableSet_windowAgeSet σ S).inter ?_
  exact measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_snd.comp measurable_snd))

private theorem rpow_antitone_of_le_one {ε x y : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hxy : x ≤ y) :
    ε ^ y ≤ ε ^ x := by
  have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
  have h1 : ε ^ (y - x) ≤ 1 := Real.rpow_le_one hε0.le hε1 hdiff
  calc ε ^ y = ε ^ (y - x + x) := by ring_nf
    _ = ε ^ (y - x) * ε ^ x := Real.rpow_add hε0 (y - x) x
    _ ≤ 1 * ε ^ x := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hε0.le x)
    _ = ε ^ x := one_mul _

/-- For `0 < ε ≤ 1` and `a, b > 0`, the window parameters `σ = ε^a` and `S = ε^{-b}` satisfy
`1 ≤ ε ^ (-(8 : ℝ) * (a + b))`, `σ⁻¹ ≤ ε ^ (-(8 : ℝ) * (a + b))`, `S ≤ ε ^ (-(8 : ℝ) * (a + b))`,
and `√S ≤ ε ^ (-(8 : ℝ) * (a + b))` (SP 2447–2456). -/
theorem window_eps_inv_bounds {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (ha : 0 < a) (hb : 0 < b) :
    1 ≤ ε ^ (-(8 : ℝ) * (a + b)) ∧
    (ε ^ a)⁻¹ ≤ ε ^ (-(8 : ℝ) * (a + b)) ∧
    ε ^ (-b) ≤ ε ^ (-(8 : ℝ) * (a + b)) ∧
    Real.sqrt (ε ^ (-b)) ≤ ε ^ (-(8 : ℝ) * (a + b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using rpow_antitone_of_le_one hε0 hε1 (show -(8 : ℝ) * (a + b) ≤ 0 by linarith)
  · rw [← Real.rpow_neg hε0.le]
    exact rpow_antitone_of_le_one hε0 hε1 (by linarith)
  · exact rpow_antitone_of_le_one hε0 hε1 (by linarith)
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0.le]
    exact rpow_antitone_of_le_one hε0 hε1 (by linarith)

/-- Exact exponent law for the localized interaction cost on `[ε^a, ε^{-b}]`: with `N = 8 * k_loc`,
`(ε ^ (-8 * (a + b))) ^ k_loc * ε ^ (2 / 539) = ε ^ (2 / 539 - N * (a + b))` (SP 2454–2463). -/
theorem window_gamma_pow_mul_rate {ε a b : ℝ} (hε0 : 0 < ε) (k_loc : ℕ) :
    let N : ℕ := 8 * k_loc
    (ε ^ (-(8 : ℝ) * (a + b))) ^ k_loc * ε ^ (2 / 539 : ℝ) =
      ε ^ ((2 / 539 : ℝ) - (N : ℝ) * (a + b)) := by
  intro N
  rw [← Real.rpow_natCast (ε ^ (-(8 : ℝ) * (a + b))) k_loc,
    ← Real.rpow_mul hε0.le, ← Real.rpow_add hε0]
  congr 1
  dsimp [N]
  push_cast
  ring

/-- For `0 < dm`, there exists `ν_per > 0` such that in `BgRegime p d dm dp` with `p.ν ≤ ν_per`,
`p.period ≤ 1`. -/
theorem window_period_le_one_exists {dm dp : ℝ} (hdm : 0 < dm) :
    ∃ ν_per : ℝ, 0 < ν_per ∧ ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_per →
      p.period ≤ 1 := by
  obtain ⟨ν_per, hν_per, hPer⟩ := poly_exp_small 2 dm 2 hdm
  exact ⟨ν_per, hν_per, fun p d hreg hν => period_le_one_of hreg (hPer p.ν p.ν_pos hν)⟩

private theorem eLpNorm_ind_ne_top (c : ℝ) (A : Set Coord) (g : HpR c) :
    eLpNorm (A.indicator (g : Coord → Axi.Merid)) (ENNReal.ofReal bgp) (hMeas c bgp) ≠ ⊤ :=
  ((eLpNorm_indicator_le (s := A) (g : Coord → Axi.Merid)).trans_lt (Lp.eLpNorm_lt_top g)).ne

/-- Triangle splitting of `hpIndNorm c (windowAgeSet σ S) g` across the observation box
`obsBox σ S L` (`|η| ≤ L`) and the transverse exterior `windowExtSet σ S L` (`|η| > L`). -/
theorem hpIndNorm_windowAgeSet_le_box_add_ext (c σ S L : ℝ) (g : HpR c) :
    hpIndNorm c (windowAgeSet σ S) g ≤
      hpIndNorm c (obsBox σ S L) g + hpIndNorm c (windowExtSet σ S L) g := by
  set pE := ENNReal.ofReal bgp
  set μ := hMeas c bgp
  have hp1 : (1 : ℝ≥0∞) ≤ pE := Fact.out
  set f0 : Coord → Axi.Merid := (windowAgeSet σ S).indicator (g : Coord → Axi.Merid)
  set f1 : Coord → Axi.Merid := (obsBox σ S L).indicator (g : Coord → Axi.Merid)
  set f2 : Coord → Axi.Merid := (windowExtSet σ S L).indicator (g : Coord → Axi.Merid)
  have hm_box : MeasurableSet (obsBox σ S L) :=
    measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)
  have mf1 : AEStronglyMeasurable f1 μ := (Lp.aestronglyMeasurable g).indicator hm_box
  have mf2 : AEStronglyMeasurable f2 μ :=
    (Lp.aestronglyMeasurable g).indicator (measurableSet_windowExtSet σ S L)
  have hptw : ∀ᵐ x ∂μ, ‖f0 x‖ ≤ ((fun y => ‖f1 y‖) + fun y => ‖f2 y‖) x := by
    refine Eventually.of_forall fun x => ?_
    simp only [Pi.add_apply]
    by_cases hw : x ∈ windowAgeSet σ S
    · by_cases hη : |x.2.2| ≤ L
      · have hbox : x ∈ obsBox σ S L := ⟨hw, trivial, abs_le.mp hη⟩
        dsimp [f0, f1]
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem hbox]
        linarith [norm_nonneg (f2 x)]
      · have hext : x ∈ windowExtSet σ S L := ⟨hw, not_le.mp hη⟩
        dsimp [f0, f2]
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem hext]
        linarith [norm_nonneg (f1 x)]
    · dsimp [f0]
      rw [Set.indicator_of_notMem hw, norm_zero]
      positivity
  have hmono : eLpNorm f0 pE μ ≤ eLpNorm ((fun y => ‖f1 y‖) + fun y => ‖f2 y‖) pE μ :=
    eLpNorm_mono_ae_real hptw
  have hsum : eLpNorm ((fun y => ‖f1 y‖) + fun y => ‖f2 y‖) pE μ ≤
      eLpNorm f1 pE μ + eLpNorm f2 pE μ := by
    simpa only [eLpNorm_norm] using eLpNorm_add_le mf1.norm mf2.norm hp1
  have htot := hmono.trans hsum
  have hne1 : eLpNorm f1 pE μ ≠ ⊤ := eLpNorm_ind_ne_top c (obsBox σ S L) g
  have hne2 : eLpNorm f2 pE μ ≠ ⊤ := eLpNorm_ind_ne_top c (windowExtSet σ S L) g
  have hne12 : eLpNorm f1 pE μ + eLpNorm f2 pE μ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩
  have htoReal := ENNReal.toReal_mono hne12 htot
  rw [ENNReal.toReal_add hne1 hne2] at htoReal
  exact htoReal

/-! ## 2. Leaf statements (`PartII-b:G3/1`, `PartII-b:G3/2`) and conditional assembly -/

/-- **Leaf 1 (`PartII-b:G3/1`, `WindowBoxCutoffBound`, SP 2007–2023, 2447–2460)**:
given the single-box comparison constant `C_loc > 0` and exponent `k_loc : ℕ` from
`LocalInteractionComparison` (`T20`), for any window exponents `a, b > 0`, regime bounds `0 < dm`,
and transverse width factor `C_D ≥ 1`, there exist `C_box > 0`, `k_box : ℕ`, and `ν₀ > 0` such that
in `BgRegime p d dm dp` with `p.ν ≤ ν₀` and `p.period ≤ 1`, choosing a smooth cutoff
`ϑ : ObsCut (σ / 2) (2 * S) (L + 1) Γ` equal to `1` on `obsBox σ S L` with `σ = p.ε ^ a`,
`S = p.ε ^ (-b)`, `L = C_D * (p.c / p.ν + Real.sqrt S + 1)`, and
`Γ ≤ C_Γ * (p.ν ^ 3)⁻¹ * p.ε ^ (-(8 : ℝ) * (a + b))` bounds the box indicator norm
`hpIndNorm p.c (obsBox σ S L) (Ke f - K0 f)` by
`C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (8 * k_loc : ℝ) * (a + b)) * ‖f‖`. -/
def WindowBoxCutoffBound : Prop :=
  ∀ (k_loc : ℕ) (C_loc : ℝ), 0 < C_loc →
    let N : ℕ := 8 * k_loc
    ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm → ∀ C_D : ℝ, 1 ≤ C_D →
      ∃ (C_box : ℝ) (k_box : ℕ) (ν₀ : ℝ), 0 < C_box ∧ 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.period ≤ 1 →
        (∀ (Γ σ H₁ L₁ : ℝ), 1 ≤ Γ → p.ν ≤ Γ → p.ν⁻¹ ≤ Γ → σ⁻¹ ≤ Γ → H₁ ≤ Γ → L₁ ≤ Γ → 0 < σ →
          ∀ ϑ : ObsCut σ H₁ L₁ Γ, ∀ F bε b0 gε : CProf,
            InHr p.c bgp F → InHr p.c bgp bε → IsResponse p.ν p.c p.ε 0 bgp F bε →
            IsFlatResponse p.ν 0 F b0 → InFlatClass p.c bgp b0 →
            InHr p.c bgp gε → IsKOut p bε gε →
            ∃ gq gη : CProf, HasWeakVec vQ0 dZero b0 gq ∧ HasWeakVec vEta dZero b0 gη ∧
              hNorm p.c bgp (fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train b0 gq gη x)) ≤
                ENNReal.ofReal (C_loc * Γ ^ k_loc * p.ε ^ (2 / 539 : ℝ)) * hNorm p.c bgp F) →
        ∀ (Ke K0 : HpR p.c →L[ℝ] HpR p.c), IsKop p Ke → IsK0op p K0 → ∀ f : HpR p.c,
          let σ : ℝ := p.ε ^ a
          let S : ℝ := p.ε ^ (-b)
          let L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
          hpIndNorm p.c (obsBox σ S L) (Ke f - K0 f) ≤
            C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (N : ℝ) * (a + b)) * ‖f‖

/-- **Leaf 2 (`PartII-b:G3/2`, `WindowTransverseTailBound`, SP 463–467, 2447–2455)**:
for every `D > 0`, `a, b > 0`, and `dm, dp` (`0 < dm`), there exist a transverse width factor
`C_D ≥ 1`, constant `C_tail > 0`, exponent `k_tail : ℕ`, and threshold `ν₀ > 0` such that in
`BgRegime p d dm dp` with `p.ν ≤ ν₀` and `p.period ≤ 1`, with `σ = p.ε ^ a`, `S = p.ε ^ (-b)`, and
`L = C_D * (p.c / p.ν + Real.sqrt S + 1)`, the transverse tail estimates (`sct:transverse`) for
`b_raw = (v_1, v_2 + ε H)` and `v_c` paired with the physical and flat free graph bounds
(`profileGraphPhys_proof`, `profileGraphFlat_proof`) bound the exterior indicator norm
`hpIndNorm p.c (windowExtSet σ S L) (Ke f - K0 f)` by
`C_tail * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖`. -/
def WindowTransverseTailBound : Prop :=
  ∀ D : ℝ, 0 < D → ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_D C_tail : ℝ) (k_tail : ℕ) (ν₀ : ℝ), 1 ≤ C_D ∧ 0 < C_tail ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.period ≤ 1 →
      ∀ (Ke K0 : HpR p.c →L[ℝ] HpR p.c), IsKop p Ke → IsK0op p K0 → ∀ f : HpR p.c,
        let σ : ℝ := p.ε ^ a
        let S : ℝ := p.ε ^ (-b)
        let L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
        hpIndNorm p.c (windowExtSet σ S L) (Ke f - K0 f) ≤
          C_tail * (p.ν ^ k_tail)⁻¹ * Real.exp (-D / p.ν) * ‖f‖

private theorem inv_pow_mono_le_one {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) {j k : ℕ}
    (hjk : j ≤ k) : (ν ^ j)⁻¹ ≤ (ν ^ k)⁻¹ := by
  rw [inv_le_inv₀ (pow_pos hν0 j) (pow_pos hν0 k)]
  exact pow_le_pow_of_le_one hν0.le hν1 hjk

/-- **Conditional assembly of `WindowComparison` (`PartII-b:G3`, SP 2438–2463)** from
`WindowBoxCutoffBound` (`PartII-b:G3/1`), `WindowTransverseTailBound` (`PartII-b:G3/2`),
`LocalInteractionComparison` (`T20`), and `YoungLateOperatorBounds` (`G2`). -/
theorem windowComparison_of_box_tail
    (hBox : WindowBoxCutoffBound)
    (hTail : WindowTransverseTailBound)
    (h20 : UnforcedLeray.Short.IIb.LocalInteractionComparison)
    (h2 : UnforcedLeray.Short.IIb.YoungLateOperatorBounds) :
    UnforcedLeray.Short.IIb.WindowComparison := by
  obtain ⟨k_loc, C_loc, ν_loc, hC_loc, hν_loc, hLoc⟩ := h20
  refine ⟨8 * k_loc, ?_⟩
  intro D hD a b ha hb dm dp hdm
  obtain ⟨_C_yl, _k_yl, _ν_yl, _hC_yl, _hν_yl, _hYL⟩ := h2 dm dp hdm
  obtain ⟨C_D, C_tail, k_tail, ν_tail, hCD1, hC_tail, hν_tail, hTail_p⟩ :=
    hTail D hD a b ha hb dm dp hdm
  obtain ⟨C_box, k_box, ν_box, hC_box, hν_box, hBox_p⟩ :=
    hBox k_loc C_loc hC_loc a b ha hb dm dp hdm C_D hCD1
  obtain ⟨ν_per, hν_per, hPer⟩ := window_period_le_one_exists (dp := dp) hdm
  set C : ℝ := C_box + C_tail
  set k : ℕ := max k_box k_tail
  set ν₀ : ℝ := min (min ν_box ν_tail) (min ν_per (min ν_loc 1))
  have hC : 0 < C := add_pos hC_box hC_tail
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_box hν_tail) (lt_min hν_per (lt_min hν_loc one_pos))
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν Ke K0 hKe hK0 f
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν_box' : p.ν ≤ ν_box := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_tail' : p.ν ≤ ν_tail := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_per' : p.ν ≤ ν_per := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_loc' : p.ν ≤ ν_loc :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν1 : p.ν ≤ 1 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hP1 : p.period ≤ 1 := hPer p d hreg hν_per'
  set σ : ℝ := p.ε ^ a
  set S : ℝ := p.ε ^ (-b)
  set L : ℝ := C_D * (p.c / p.ν + Real.sqrt S + 1)
  have hsplit := hpIndNorm_windowAgeSet_le_box_add_ext p.c σ S L (Ke f - K0 f)
  have hB := hBox_p p d hreg hν_box' hP1 (hLoc p d dm dp hreg hν_loc' hP1) Ke K0 hKe hK0 f
  have hT := hTail_p p d hreg hν_tail' hP1 Ke K0 hKe hK0 f
  have hk_box : (p.ν ^ k_box)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_le_one hν_pos hν1 (le_max_left _ _)
  have hk_tail : (p.ν ^ k_tail)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_le_one hν_pos hν1 (le_max_right _ _)
  have hε_pos : 0 ≤ p.ε ^ ((2 / 539 : ℝ) - (8 * k_loc : ℕ) * (a + b)) :=
    Real.rpow_nonneg p.ε_pos.le _
  have hexp_pos : 0 ≤ Real.exp (-D / p.ν) := (Real.exp_pos _).le
  have hB' : hpIndNorm p.c (obsBox σ S L) (Ke f - K0 f) ≤
      C_box * (p.ν ^ k)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (8 * k_loc : ℕ) * (a + b)) * ‖f‖ := by
    refine hB.trans ?_
    gcongr
  have hT' : hpIndNorm p.c (windowExtSet σ S L) (Ke f - K0 f) ≤
      C_tail * (p.ν ^ k)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ := by
    refine hT.trans ?_
    gcongr
  calc hpIndNorm p.c (windowAgeSet σ S) (Ke f - K0 f)
      ≤ hpIndNorm p.c (obsBox σ S L) (Ke f - K0 f) +
          hpIndNorm p.c (windowExtSet σ S L) (Ke f - K0 f) := hsplit
    _ ≤ C_box * (p.ν ^ k)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (8 * k_loc : ℕ) * (a + b)) * ‖f‖ +
          C_tail * (p.ν ^ k)⁻¹ * Real.exp (-D / p.ν) * ‖f‖ := add_le_add hB' hT'
    _ ≤ (C_box + C_tail) * (p.ν ^ k)⁻¹ *
          (p.ε ^ ((2 / 539 : ℝ) - (8 * k_loc : ℕ) * (a + b)) + Real.exp (-D / p.ν)) * ‖f‖ := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
        have h1 : 0 ≤ C_box * (p.ν ^ k)⁻¹ * Real.exp (-D / p.ν) := by positivity
        have h2 : 0 ≤ C_tail * (p.ν ^ k)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (8 * k_loc : ℕ) * (a + b)) := by
          positivity
        linarith

end UnforcedLeray.Short.IIb

end
