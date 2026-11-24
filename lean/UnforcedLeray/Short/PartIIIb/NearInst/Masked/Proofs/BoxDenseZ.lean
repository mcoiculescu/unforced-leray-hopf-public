import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# `boxDenseZ`: box inputs are dense in `Z` (source 3905-3912)

Route: cut `F = (F₁, F₂)` to the window `A_n = {1/(n+1) ≤ s ≤ n, |η| ≤ n, ‖F₁‖ ≤ n, ‖F₂‖ ≤ n}`.
The cut `(A_n)ᶜ`-indicator of an `L²` function tends to `0` in `L²` by dominated convergence, since
the `A_n` increase and exhaust `{s > 0}`, which is full for `s^{-1/2}dς` and the two weighted
measures.  The cut components `f_i = 1_{A_n} F_i` are bounded measurable and supported in the band,
so `f₁ + f₂` is a box tensor, and `zsum` of the cut element is a.e. `f₁ + f₂`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The window `A_n` for a pair of functions. -/
def bdWin (g1 g2 : Chart → Ten3) (n : ℕ) : Set Chart :=
  {p | 1 / ((n : ℝ) + 1) ≤ p.1 ∧ p.1 ≤ n ∧ |p.2.2| ≤ n ∧ ‖g1 p‖ ≤ n ∧ ‖g2 p‖ ≤ n}

theorem bdWin_meas {g1 g2 : Chart → Ten3} (h1 : Measurable g1) (h2 : Measurable g2) (n : ℕ) :
    MeasurableSet (bdWin g1 g2 n) := by
  unfold bdWin
  have a1 : Measurable fun p : Chart => p.1 := measurable_fst
  have a2 : Measurable fun p : Chart => |p.2.2| := continuous_abs.measurable.comp (measurable_snd.comp measurable_snd)
  refine (measurableSet_le measurable_const a1).inter ((measurableSet_le a1 measurable_const).inter
    ((measurableSet_le a2 measurable_const).inter
      ((measurableSet_le h1.norm measurable_const).inter
        (measurableSet_le h2.norm measurable_const))))

theorem bdWin_mono (g1 g2 : Chart → Ten3) : Monotone (bdWin g1 g2) := by
  intro n m hnm p hp
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  obtain ⟨a, b, c, d, e⟩ := hp
  refine ⟨?_, b.trans hnm', c.trans hnm', d.trans hnm', e.trans hnm'⟩
  refine le_trans ?_ a
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem bdWin_cover (g1 g2 : Chart → Ten3) {p : Chart} (hp : 0 < p.1) :
    ∃ n, p ∈ bdWin g1 g2 n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max (1 / p.1) p.1) (max (max |p.2.2| ‖g1 p‖) ‖g2 p‖))
  have h1 : 1 / p.1 ≤ n := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hn
  have h2 : p.1 ≤ n := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hn
  have h3 : |p.2.2| ≤ n := ((le_max_left _ _).trans (le_max_left _ _) |>.trans
    (le_max_right _ _)).trans hn
  have h4 : ‖g1 p‖ ≤ n := ((le_max_right _ _).trans (le_max_left _ _) |>.trans
    (le_max_right _ _)).trans hn
  have h5 : ‖g2 p‖ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  refine ⟨n, ?_, h2, h3, h4, h5⟩
  have : 1 / ((n : ℝ) + 1) ≤ p.1 := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hp).1 h1
    nlinarith
  exact this

/-- Dominated convergence for the cut. -/
theorem bd_tendsto_cut {μ : Measure Chart} {g : Chart → Ten3} (hgmeas : Measurable g)
    (hg : MemLp g 2 μ)
    (A : ℕ → Set Chart) (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hcov : ∀ᵐ p ∂μ, ∃ n, p ∈ A n) :
    Tendsto (fun n => eLpNorm ((A n)ᶜ.indicator g) 2 μ) atTop (𝓝 0) := by
  have hgm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hint : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
    have := hg.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at this
    simp only [ENNReal.toReal_ofNat] at this
    have h2 : (∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) < ∞ := this
    by_contra hne
    rw [not_lt, top_le_iff] at hne
    rw [hne] at h2
    simp at h2
  have key : Tendsto (fun n => ∫⁻ p, ‖(A n)ᶜ.indicator g p‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun n p => ‖(A n)ᶜ.indicator g p‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (bound := fun p => ‖g p‖ₑ ^ (2 : ℝ))
      (fun n => ((hgmeas.indicator (hA n).compl).enorm.pow_const _))
      (fun n => Filter.Eventually.of_forall fun p => by
        by_cases hp : p ∈ (A n)ᶜ
        · simp [Set.indicator_of_mem hp]
        · simp [Set.indicator_of_notMem hp])
      hint.ne
      (by
        filter_upwards [hcov] with p ⟨n, hn⟩
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with m hm
        have : p ∈ A m := hmono hm hn
        simp [Set.indicator_of_notMem (show p ∉ (A m)ᶜ from fun h => h this)])
    simpa using this
  have hp : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ))) (𝓝 0) (𝓝 0) := by
    have := ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ)) |>.tendsto 0
    simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this
  refine (hp.comp key).congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp

theorem bd_norm_lt {μ : Measure Chart} (u : Lp Ten3 2 μ) {f : Chart → Ten3} (hf : MemLp f 2 μ)
    {r : ℝ} (h : eLpNorm (⇑u - f) 2 μ < ENNReal.ofReal r) : ‖u - hf.toLp f‖ < r := by
  rw [Lp.norm_def]
  have : eLpNorm (⇑(u - hf.toLp f)) 2 μ = eLpNorm (⇑u - f) 2 μ :=
    eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (EventuallyEq.sub EventuallyEq.rfl hf.coeFn_toLp))
  rw [this]
  exact ENNReal.toReal_lt_of_lt_ofReal h

theorem boxDenseZ : BoxDenseZ := by
  intro c mZ ρb hc hmZ hρ F η hη
  set g1 : Chart → Ten3 := ⇑(F.fst) with hg1
  set g2 : Chart → Ten3 := ⇑(F.snd) with hg2
  have m1 : Measurable g1 := (Lp.stronglyMeasurable F.fst).measurable
  have m2 : Measurable g2 := (Lp.stronglyMeasurable F.snd).measurable
  have hl1 : MemLp g1 2 (z1Measure c mZ) := Lp.memLp F.fst
  have hl2 : MemLp g2 2 (htRhoMeasure c ρb) := Lp.memLp F.snd
  have ac1 : ageμ c (-1 / 2) ≪ z1Measure c mZ :=
    Measure.absolutelyContinuous_of_le_smul (ageμ_le_z1Measure hmZ)
  have ac2 : ageμ c (-1 / 2) ≪ htRhoMeasure c ρb :=
    Measure.absolutelyContinuous_of_le_smul (ageμ_le_htRho hρ)
  have b1 : z1Measure c mZ ≪ ageμ c (-1 / 2) := withDensity_absolutelyContinuous _ _
  have b2 : htRhoMeasure c ρb ≪ ageμ c (-1 / 2) := Measure.smul_absolutelyContinuous
  have pos : ∀ᵐ p ∂(ageμ c (-1 / 2)), 0 < p.1 := UnforcedLeray.Short.IIIa.ae_pos_ageμ c _
  have cov1 : ∀ᵐ p ∂(z1Measure c mZ), ∃ n, p ∈ bdWin g1 g2 n := by
    filter_upwards [b1 pos] with p hp using bdWin_cover g1 g2 hp
  have cov2 : ∀ᵐ p ∂(htRhoMeasure c ρb), ∃ n, p ∈ bdWin g1 g2 n := by
    filter_upwards [b2 pos] with p hp using bdWin_cover g1 g2 hp
  have T1 := bd_tendsto_cut m1 hl1 (bdWin g1 g2) (bdWin_meas m1 m2) (bdWin_mono g1 g2) cov1
  have T2 := bd_tendsto_cut m2 hl2 (bdWin g1 g2) (bdWin_meas m1 m2) (bdWin_mono g1 g2) cov2
  have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨n, hn1, hn2⟩ := ((T1.eventually (gt_mem_nhds hε)).and
    (T2.eventually (gt_mem_nhds hε))).exists
  set A := bdWin g1 g2 n with hAdef
  have hAm : MeasurableSet A := bdWin_meas m1 m2 n
  have hf1 : MemLp (A.indicator g1) 2 (z1Measure c mZ) := hl1.indicator hAm
  have hf2 : MemLp (A.indicator g2) 2 (htRhoMeasure c ρb) := hl2.indicator hAm
  have sub1 : g1 - A.indicator g1 = Aᶜ.indicator g1 := by
    ext p
    by_cases hp : p ∈ A <;> simp [hp]
  have sub2 : g2 - A.indicator g2 = Aᶜ.indicator g2 := by
    ext p
    by_cases hp : p ∈ A <;> simp [hp]
  have hbox : IsBoxTensor (fun p => A.indicator g1 p + A.indicator g2 p) := by
    refine ⟨(m1.indicator hAm).add (m2.indicator hAm), ⟨2 * n, fun p => ?_⟩,
      ⟨1 / ((n : ℝ) + 1), n, n, by positivity, fun p hp => ?_⟩⟩
    · by_cases hpA : p ∈ A
      · have hd := hpA.2.2.2.1
        have he := hpA.2.2.2.2
        simp only [Set.indicator_of_mem hpA]
        calc ‖g1 p + g2 p‖ ≤ ‖g1 p‖ + ‖g2 p‖ := norm_add_le _ _
          _ ≤ 2 * n := by linarith
      · simp [Set.indicator_of_notMem hpA]
    · by_cases hpA : p ∈ A
      · exact ⟨hpA.1, hpA.2.1, hpA.2.2.1⟩
      · exact absurd (by simp [Set.indicator_of_notMem hpA]) hp
  refine ⟨WithLp.toLp 1 (hf1.toLp _, hf2.toLp _), ⟨_, hbox, ?_⟩, ?_⟩
  · have e1 : (hf1.toLp _ : Chart → Ten3) =ᵐ[z1Measure c mZ] A.indicator g1 := hf1.coeFn_toLp
    have e2 : (hf2.toLp _ : Chart → Ten3) =ᵐ[htRhoMeasure c ρb] A.indicator g2 := hf2.coeFn_toLp
    filter_upwards [ac1 e1, ac2 e2] with p h1 h2
    change (hf1.toLp _ : Chart → Ten3) p + (hf2.toLp _ : Chart → Ten3) p = _
    rw [h1, h2]
  · have n1 : ‖F.fst - hf1.toLp _‖ < η / 2 := bd_norm_lt F.fst hf1 (by rw [hg1, sub1]; exact hn1)
    have n2 : ‖F.snd - hf2.toLp _‖ < η / 2 := bd_norm_lt F.snd hf2 (by rw [hg2, sub2]; exact hn2)
    rw [WithLp.prod_norm_eq_of_L1]
    change ‖F.fst - hf1.toLp _‖ + ‖F.snd - hf2.toLp _‖ < η
    linarith

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
