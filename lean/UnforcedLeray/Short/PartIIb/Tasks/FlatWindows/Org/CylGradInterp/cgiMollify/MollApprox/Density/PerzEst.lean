import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7_1

/-!
# `PartII-b:T13/1/5/5/7/1/5` (`mollPerzEst_proof`): the periodization estimate

Source: `the November 2 reference manuscript` lines 1932-1935.
On the cell strip `moStrip c` the difference `f1 - moPerz c h` is a sum of three
`q`-translates of `mpeV c f1 h = strip.indicator f1 - h` (the other translates vanish there).
Hölder with three terms, translation invariance and the disjointness of the three translated
strips give the bound with `K = (ofReal c⁻¹ * 3^(r-1))^(1/r)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The difference `strip.indicator f1 - h`. -/
def mpeV (c : ℝ) (f1 h : Coord → ℂ) : Coord → ℂ := fun y => (moStrip c).indicator f1 y - h y

/-- Translation vector moving `q` by `k c`. -/
def mpeVec (c : ℝ) (k : ℤ) : Coord := (0, ((k : ℝ) * c, 0))

/-- The set of `y` whose `k`-translate by `-c e_q` lies in the strip. -/
def mpeSet (c : ℝ) (k : ℤ) : Set Coord := (fun y : Coord => y - mpeVec c k) ⁻¹' moStrip c

lemma mpe_add_q (c : ℝ) (k : ℤ) (x : Coord) : (x + mpeVec c k).2.1 = x.2.1 + (k : ℝ) * c := by
  simp [mpeVec]

lemma mpe_sub_q (c : ℝ) (k : ℤ) (x : Coord) : (x - mpeVec c k).2.1 = x.2.1 - (k : ℝ) * c := by
  simp [mpeVec]

lemma mpe_shift_eq (c : ℝ) (k : ℤ) (x : Coord) :
    (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = x + mpeVec c k := by
  simp [mpeVec, Prod.ext_iff]

lemma mpe_zero (c : ℝ) (x : Coord) : x + mpeVec c 0 = x := by
  simp [mpeVec]

lemma mpe_mem_strip (c : ℝ) (x : Coord) : x ∈ moStrip c ↔ -c / 2 ≤ x.2.1 ∧ x.2.1 < c / 2 := by
  simp only [moStrip, UnforcedLeray.Cyl.cell, mem_prod, mem_univ, true_and, and_true, mem_Ico]

lemma mpe_measurableSet_strip (c : ℝ) : MeasurableSet (moStrip c) := by
  unfold moStrip UnforcedLeray.Cyl.cell
  exact MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)

lemma mpe_notMem (c : ℝ) (hc : 0 < c) (x : Coord) (hx : x ∈ moStrip c) (k : ℤ) (hk : k ≠ 0) :
    x + mpeVec c k ∉ moStrip c := by
  intro hmem
  rw [mpe_mem_strip, mpe_add_q] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [mpe_mem_strip] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hk' hc.le]
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith [mul_le_mul_of_nonneg_right hk' hc.le]

lemma mpe_perz_eq (c M : ℝ) (hc : 0 < c) (h : Coord → ℂ)
    (hsupp : ∀ x, x ∉ moWin c M → h x = 0) (x : Coord) (hx : x ∈ moStrip c) :
    moPerz c h x = ∑ k ∈ ({-1, 0, 1} : Finset ℤ), h (x + mpeVec c k) := by
  rw [mpe_mem_strip] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hsub : Function.support (fun k : ℤ => h (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)))
      ⊆ ↑({-1, 0, 1} : Finset ℤ) := by
    intro k hk
    rw [Function.mem_support] at hk
    have hwin : (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) ∈ moWin c M := by
      by_contra hn
      exact hk (hsupp _ hn)
    simp only [moWin, mem_prod, mem_Icc] at hwin
    obtain ⟨_, ⟨hq1, hq2⟩, _⟩ := hwin
    rw [Finset.mem_coe]
    have hk1 : k ≤ 1 := by
      by_contra hn
      have h2 : (2 : ℝ) ≤ k := by exact_mod_cast (show (2 : ℤ) ≤ k by omega)
      nlinarith [mul_le_mul_of_nonneg_right h2 hc.le]
    have hk2 : -1 ≤ k := by
      by_contra hn
      have h2 : (k : ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
      nlinarith [mul_le_mul_of_nonneg_right h2 hc.le]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold moPerz
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mpe_shift_eq]

lemma mpe_sum_indicator (c : ℝ) (hc : 0 < c) (f1 : Coord → ℂ) (x : Coord) (hx : x ∈ moStrip c) :
    ∑ k ∈ ({-1, 0, 1} : Finset ℤ), (moStrip c).indicator f1 (x + mpeVec c k) = f1 x := by
  rw [Finset.sum_eq_single (0 : ℤ)]
  · rw [mpe_zero, indicator_of_mem hx]
  · intro k _ hk0
    exact indicator_of_notMem (mpe_notMem c hc x hx k hk0) _
  · intro h0
    exact absurd (by simp : (0 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ)) h0

lemma mpe_holder (c r M : ℝ) (hc : 0 < c) (hr : 1 < r) (f1 h : Coord → ℂ)
    (hsupp : ∀ x, x ∉ moWin c M → h x = 0) (x : Coord) (hx : x ∈ moStrip c) :
    ‖f1 x - moPerz c h x‖ₑ ^ r ≤
      (3 : ℝ≥0∞) ^ (r - 1) * ∑ k ∈ ({-1, 0, 1} : Finset ℤ), ‖mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r := by
  have hsum : f1 x - moPerz c h x =
      ∑ k ∈ ({-1, 0, 1} : Finset ℤ), mpeV c f1 h (x + mpeVec c k) := by
    rw [mpe_perz_eq c M hc h hsupp x hx]
    simp only [mpeV]
    rw [Finset.sum_sub_distrib, mpe_sum_indicator c hc f1 x hx]
  have hcard : (({-1, 0, 1} : Finset ℤ).card : ℝ≥0∞) ≤ 3 := by
    exact_mod_cast Finset.card_le_three
  rw [hsum]
  calc ‖∑ k ∈ ({-1, 0, 1} : Finset ℤ), mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r
      ≤ (∑ k ∈ ({-1, 0, 1} : Finset ℤ), ‖mpeV c f1 h (x + mpeVec c k)‖ₑ) ^ r :=
        ENNReal.rpow_le_rpow (enorm_sum_le _ _) (by linarith)
    _ ≤ (({-1, 0, 1} : Finset ℤ).card : ℝ≥0∞) ^ (r - 1) *
          ∑ k ∈ ({-1, 0, 1} : Finset ℤ), ‖mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hr.le
    _ ≤ (3 : ℝ≥0∞) ^ (r - 1) *
          ∑ k ∈ ({-1, 0, 1} : Finset ℤ), ‖mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hcard (by linarith)) (by positivity)

lemma mpe_disjoint (c : ℝ) (hc : 0 < c) {k k' : ℤ} (hne : k ≠ k') :
    Disjoint (mpeSet c k) (mpeSet c k') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  simp only [mpeSet, mem_preimage, mpe_mem_strip, mpe_sub_q] at hy hy'
  obtain ⟨a1, a2⟩ := hy
  obtain ⟨b1, b2⟩ := hy'
  have e1 : ((k' - k : ℤ) : ℝ) < 1 := by push_cast; nlinarith
  have e2 : ((k - k' : ℤ) : ℝ) < 1 := by push_cast; nlinarith
  have f1' : k' - k < 1 := by exact_mod_cast e1
  have f2' : k - k' < 1 := by exact_mod_cast e2
  omega

lemma mpe_measurableSet (c : ℝ) (k : ℤ) : MeasurableSet (mpeSet c k) := by
  unfold mpeSet
  exact (mpe_measurableSet_strip c).preimage (measurable_id.sub_const _)

lemma mpe_lintegral_shift (c : ℝ) (k : ℤ) (G : Coord → ℝ≥0∞) :
    ∫⁻ x in moStrip c, G (x + mpeVec c k) = ∫⁻ y in mpeSet c k, G y := by
  have hmp : MeasurePreserving (fun x : Coord => x + mpeVec c k) volume volume :=
    measurePreserving_add_right volume (mpeVec c k)
  have hemb : MeasurableEmbedding (fun x : Coord => x + mpeVec c k) :=
    (Homeomorph.addRight (mpeVec c k)).measurableEmbedding
  have hpre : (fun x : Coord => x + mpeVec c k) ⁻¹' mpeSet c k = moStrip c := by
    ext x
    simp [mpeSet]
  have key := hmp.setLIntegral_comp_preimage_emb hemb G (mpeSet c k)
  rw [hpre] at key
  exact key

lemma mpe_three_le (c : ℝ) (hc : 0 < c) (G : Coord → ℝ≥0∞) :
    ∑ k ∈ ({-1, 0, 1} : Finset ℤ), ∫⁻ y in mpeSet c k, G y ≤ ∫⁻ y, G y := by
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num), Finset.sum_singleton]
  have e1 := lintegral_union (μ := volume) (f := G) (mpe_measurableSet c 0)
    (mpe_disjoint c hc (by norm_num : (-1 : ℤ) ≠ 0))
  have e2 := lintegral_union (μ := volume) (f := G) (mpe_measurableSet c 1)
    (Set.disjoint_union_left.2 ⟨mpe_disjoint c hc (by norm_num : (-1 : ℤ) ≠ 1),
      mpe_disjoint c hc (by norm_num : (0 : ℤ) ≠ 1)⟩)
  have e3 := setLIntegral_le_lintegral (μ := volume) ((mpeSet c (-1) ∪ mpeSet c 0) ∪ mpeSet c 1) G
  rw [e2, e1] at e3
  rw [← add_assoc]
  exact e3

lemma mpe_cylMeas_eq (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict (moStrip c) := by
  unfold moStrip cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [Measure.prod_smul_right]
  congr 1
  have hcoord : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  rw [hcoord, ← Measure.prod_restrict, Measure.restrict_univ]

theorem mollPerzEst_proof : MollPerzEst := by
  unfold MollPerzEst
  intro c r hc hr
  have hr0 : 0 < r := by linarith
  have h3ne : (3 : ℝ≥0∞) ^ (r - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  refine ⟨(ENNReal.ofReal c⁻¹ * (3 : ℝ≥0∞) ^ (r - 1)) ^ (1 / r), ?_, ?_⟩
  · exact ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 hr0.le)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h3ne)
  intro M f1 hf1 _hper h hcont hsupp
  show eLpNorm (fun x => f1 x - moPerz c h x) (ENNReal.ofReal r) (cylMeas c) ≤
    (ENNReal.ofReal c⁻¹ * (3 : ℝ≥0∞) ^ (r - 1)) ^ (1 / r) *
      eLpNorm (mpeV c f1 h) (ENNReal.ofReal r) volume
  have hSm := mpe_measurableSet_strip c
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpne : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hVm : AEStronglyMeasurable (mpeV c f1 h) volume :=
    (hf1.indicator hSm).sub hcont.aestronglyMeasurable
  have hGm : AEMeasurable (fun y => ‖mpeV c f1 h y‖ₑ ^ r) volume :=
    (hVm.aemeasurable.enorm).pow_const r
  have hGk : ∀ k : ℤ, AEMeasurable (fun x => ‖mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r)
      (volume.restrict (moStrip c)) := fun k =>
    (hGm.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (mpeVec c k)).quasiMeasurePreserving).restrict
  have hint : ∫⁻ x in moStrip c, ‖f1 x - moPerz c h x‖ₑ ^ r ≤
      (3 : ℝ≥0∞) ^ (r - 1) * ∫⁻ y, ‖mpeV c f1 h y‖ₑ ^ r := by
    calc ∫⁻ x in moStrip c, ‖f1 x - moPerz c h x‖ₑ ^ r
        ≤ ∫⁻ x in moStrip c, (3 : ℝ≥0∞) ^ (r - 1) *
            ∑ k ∈ ({-1, 0, 1} : Finset ℤ), ‖mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r :=
          setLIntegral_mono' hSm (fun x hx => mpe_holder c r M hc hr f1 h hsupp x hx)
      _ = (3 : ℝ≥0∞) ^ (r - 1) * ∑ k ∈ ({-1, 0, 1} : Finset ℤ),
            ∫⁻ x in moStrip c, ‖mpeV c f1 h (x + mpeVec c k)‖ₑ ^ r := by
          rw [lintegral_const_mul' _ _ h3ne]
          congr 1
          exact lintegral_finsetSum' _ (fun k _ => hGk k)
      _ = (3 : ℝ≥0∞) ^ (r - 1) * ∑ k ∈ ({-1, 0, 1} : Finset ℤ),
            ∫⁻ y in mpeSet c k, ‖mpeV c f1 h y‖ₑ ^ r := by
          congr 1
          exact Finset.sum_congr rfl
            (fun k _ => mpe_lintegral_shift c k (fun y => ‖mpeV c f1 h y‖ₑ ^ r))
      _ ≤ (3 : ℝ≥0∞) ^ (r - 1) * ∫⁻ y, ‖mpeV c f1 h y‖ₑ ^ r :=
          mul_le_mul_of_nonneg_left (mpe_three_le c hc (fun y => ‖mpeV c f1 h y‖ₑ ^ r)) (by positivity)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpne,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpne, hpt, mpe_cylMeas_eq c,
    lintegral_smul_measure, smul_eq_mul]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr0.le)]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.2 hr0.le)
  calc ENNReal.ofReal c⁻¹ * ∫⁻ x in moStrip c, ‖f1 x - moPerz c h x‖ₑ ^ r
      ≤ ENNReal.ofReal c⁻¹ * ((3 : ℝ≥0∞) ^ (r - 1) * ∫⁻ y, ‖mpeV c f1 h y‖ₑ ^ r) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ENNReal.ofReal c⁻¹ * (3 : ℝ≥0∞) ^ (r - 1) * ∫⁻ y, ‖mpeV c f1 h y‖ₑ ^ r := by ring

end UnforcedLeray.Short.IIb
