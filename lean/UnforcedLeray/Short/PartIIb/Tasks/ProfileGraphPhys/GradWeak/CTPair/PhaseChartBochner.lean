import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair.PhaseChartAux

/-!
# `PartII-b:T10/7/1/2/2/2` (`phase_chart_bochner`), SP 1639-1668
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PCB

open UnforcedLeray UnforcedLeray.Axi UnforcedLeray.Short.IIb.PCAux

abbrev PM (P : ℝ) : Measure (ℝ × Space) := (volume.restrict (Ioc 0 P)).prod volume

lemma measurable_chart (R : ℝ) :
    Measurable fun z : ℝ × Space => Axi.chart R z.1 z.2 :=
  ((measurable_age R).comp measurable_snd).prodMk
    ((measurable_phase R).prodMk ((measurable_trans R).comp measurable_snd))

lemma lint_chart {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (G : Coord → ℝ≥0∞) (hG : Measurable G) (hper : ∀ x, G (qShift c x) = G x) :
    ∫⁻ z : ℝ × Space, G (Axi.chart R z.1 z.2) ∂(PM P) =
      ENNReal.ofReal P * (ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, G p ∂(ageμ c (-(5 / 2)))) := by
  have hP0 : 0 < P := by rw [hP]; exact div_pos (mul_pos two_pos hc) hR
  have hm : Measurable fun z : ℝ × Space => G (Axi.chart R z.1 z.2) :=
    hG.comp (measurable_chart R)
  rw [PM, lintegral_prod _ hm.aemeasurable]
  have h := phaseAvg_ringChart hR hc hP G hG (fun s q η => hper (s, (q, η)))
  rw [← lintegral_ageμ hc _ hG] at h
  have h0 : ENNReal.ofReal P ≠ 0 := by simpa using hP0
  have h1 : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← h, ← mul_assoc, ENNReal.mul_inv_cancel h0 h1, one_mul]
  rfl


lemma integrable_chart {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (G : Coord → E) (hG : Measurable G) (hper : ∀ x, G (qShift c x) = G x)
    (hint : Integrable G (ageμ c (-(5 / 2)))) :
    Integrable (fun z : ℝ × Space => G (Axi.chart R z.1 z.2)) (PM P) := by
  refine ⟨(hG.comp (measurable_chart R)).aestronglyMeasurable, ?_⟩
  have h := lint_chart hR hc hP (fun x => ‖G x‖ₑ) hG.enorm (fun x => by simp only [hper])
  have hfin : ∫⁻ p, ‖G p‖ₑ ∂(ageμ c (-(5 / 2))) < ⊤ := hint.2
  show ∫⁻ z, ‖G (Axi.chart R z.1 z.2)‖ₑ ∂(PM P) < ⊤
  rw [h]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

lemma real_chart {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (F : Coord → ℝ) (hF : Measurable F) (hper : ∀ x, F (qShift c x) = F x)
    (hint : Integrable F (ageμ c (-(5 / 2)))) :
    ∫ z : ℝ × Space, F (Axi.chart R z.1 z.2) ∂(PM P) =
      P * (Real.pi * R ^ 2) * ∫ p, F p ∂(ageμ c (-(5 / 2))) := by
  have hP0 : 0 < P := by rw [hP]; exact div_pos (mul_pos two_pos hc) hR
  have hK : 0 ≤ Real.pi * R ^ 2 := by positivity
  have hi := integrable_chart hR hc hP F hF hper hint
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  have e1 := lint_chart hR hc hP (fun x => ENNReal.ofReal (F x)) hF.ennreal_ofReal
    (fun x => by simp only [hper])
  have e2 := lint_chart hR hc hP (fun x => ENNReal.ofReal (-F x)) hF.neg.ennreal_ofReal
    (fun x => by simp only [hper])
  rw [e1, e2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hP0.le, ENNReal.toReal_ofReal hK]
  ring

lemma cplx_chart {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (G : Coord → ℂ) (hG : Measurable G) (hper : ∀ x, G (qShift c x) = G x)
    (hint : Integrable G (ageμ c (-(5 / 2)))) :
    Integrable (fun z : ℝ × Space => G (Axi.chart R z.1 z.2)) (PM P) ∧
    ∫ z : ℝ × Space, G (Axi.chart R z.1 z.2) ∂(PM P) =
      ((P * (Real.pi * R ^ 2) : ℝ) : ℂ) * ∫ p, G p ∂(ageμ c (-(5 / 2))) := by
  have hi := integrable_chart hR hc hP G hG hper hint
  refine ⟨hi, ?_⟩
  apply Complex.ext
  · have h1 := integral_re hi
    have h2 := integral_re hint
    simp only [RCLike.re_to_complex] at h1 h2
    rw [← h1, Complex.re_ofReal_mul, ← h2]
    exact real_chart hR hc hP (fun x => (G x).re) (Complex.measurable_re.comp hG)
      (fun x => by simp only [hper]) hint.re
  · have h1 := integral_im hi
    have h2 := integral_im hint
    simp only [RCLike.im_to_complex] at h1 h2
    rw [← h1, Complex.im_ofReal_mul, ← h2]
    exact real_chart hR hc hP (fun x => (G x).im) (Complex.measurable_im.comp hG)
      (fun x => by simp only [hper]) hint.im


lemma ae_good {c : ℝ} {G : Coord → ℂ}
    (hper : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qShift c x) = G x) :
    ∀ᵐ x ∂(volume : Measure Coord), ∀ n : ℤ, 0 < x.1 → G (sh c n x) = G x := by
  have h1 : ∀ n : ℤ, ∀ᵐ x ∂(volume : Measure Coord),
      0 < (sh c n x).1 → G (qShift c (sh c n x)) = G (sh c n x) :=
    fun n => (mp_sh c n).quasiMeasurePreserving.ae hper
  filter_upwards [ae_all_iff.2 h1] with x hx n hxpos
  induction n using Int.induction_on with
  | zero => rw [sh_zero]
  | succ i ih =>
    rw [sh_succ, hx i hxpos]
    exact ih
  | pred i ih =>
    have := hx (-(i : ℤ) - 1) hxpos
    have e : qShift c (sh c (-(i : ℤ) - 1) x) = sh c (-(i : ℤ)) x := by
      rw [← sh_succ]; congr 1; ring
    rw [e] at this
    rw [← this, ih]

lemma rep {c : ℝ} (hc : 0 < c) (a : ℝ) (G : Coord → ℂ) (hint : Integrable G (ageμ c a))
    (hper : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qShift c x) = G x) :
    ∃ G' : Coord → ℂ, Measurable G' ∧ (∀ x, G' (qShift c x) = G' x) ∧
      ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x := by
  set G₀ : Coord → ℂ := hint.1.mk G with hG₀
  have hG₀m : Measurable G₀ := hint.1.stronglyMeasurable_mk.measurable
  have hae : G =ᵐ[ageμ c a] G₀ := hint.1.ae_eq_mk
  refine ⟨fun x => G₀ (red c x), hG₀m.comp (measurable_red c),
    fun x => by simp only [red_qShift c hc], ?_⟩
  set M := toMeasurable (ageμ c a) {x | G x ≠ G₀ x} with hM
  have hM0 : ageμ c a M = 0 := by
    rw [hM, measure_toMeasurable]; exact ae_iff.1 hae
  have hM' := vol_null_of_ageμ_null hc a (measurableSet_toMeasurable _ _) hM0
  have h0 : ∀ᵐ y ∂(volume : Measure Coord), y ∉ M ∩ (Ioi (0 : ℝ) ×ˢ qCell c) := by
    rw [ae_iff]; simp only [not_not]; exact hM'
  have h1 : ∀ n : ℤ, ∀ᵐ x ∂(volume : Measure Coord),
      sh c n x ∉ M ∩ (Ioi (0 : ℝ) ×ˢ qCell c) := fun n =>
    (mp_sh c n).quasiMeasurePreserving.ae h0
  filter_upwards [ae_good hper, ae_all_iff.2 h1] with x hx hy hxpos
  have e1 := hx (-(kk c x.2.1)) hxpos
  have e2 := hy (-(kk c x.2.1))
  have e3 : red c x ∉ M := by
    intro hm
    exact e2 ⟨hm, by rw [← red_eq_sh]; exact ⟨hxpos, red_mem hc x⟩⟩
  have e4 : G (red c x) = G₀ (red c x) := by
    by_contra hne
    exact e3 (subset_toMeasurable _ _ hne)
  show G x = G₀ (red c x)
  rw [← e4, red_eq_sh, e1]

lemma chart_ae {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) {G G' : Coord → ℂ}
    (hD : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x) :
    ∀ᵐ z ∂(PM P), G (Axi.chart R z.1 z.2) = G' (Axi.chart R z.1 z.2) := by
  set N₁ := toMeasurable (volume : Measure Coord) {x | ¬ (0 < x.1 → G x = G' x)} with hN₁
  have hN₁0 : (volume : Measure Coord) N₁ = 0 := by
    rw [hN₁, measure_toMeasurable]; exact ae_iff.1 hD
  have hN₁m : MeasurableSet N₁ := measurableSet_toMeasurable _ _
  set Nt : Set Coord := {x | x.1 ≤ 0} ∪ ⋃ n : ℤ, sh c n ⁻¹' N₁ with hNt
  have hNtm : MeasurableSet Nt :=
    (measurableSet_le measurable_fst measurable_const).union
      (MeasurableSet.iUnion fun n => measurable_sh c n hN₁m)
  have hNtper : ∀ x, qShift c x ∈ Nt ↔ x ∈ Nt := by
    intro x
    simp only [hNt, mem_union, mem_setOf_eq, mem_iUnion, mem_preimage]
    have e : ∀ n : ℤ, sh c n (qShift c x) = sh c (n + 1) x := by
      intro n; rw [← sh_one, sh_sh]
    simp only [e]
    change ((x.1 ≤ 0) ∨ _) ↔ _
    refine or_congr Iff.rfl ?_
    exact ⟨fun ⟨i, h⟩ => ⟨i + 1, h⟩, fun ⟨i, h⟩ => ⟨i - 1, by simpa using h⟩⟩
  have hNt0 : ageμ c (-(5 / 2)) Nt = 0 := by
    refine ageμ_null hc _ hNtm ?_
    refine measure_mono_null ?_ (measure_iUnion_null fun n : ℤ => ?_ :
      (volume : Measure Coord) (⋃ n : ℤ, sh c n ⁻¹' N₁) = 0)
    · intro x hx
      rcases hx.1 with h | h
      · exact absurd (show 0 < x.1 from hx.2) (not_lt.2 h)
      · exact h
    · rw [(mp_sh c n).measure_preimage hN₁m.nullMeasurableSet]; exact hN₁0
  have h := lint_chart hR hc hP (Nt.indicator 1) (measurable_one.indicator hNtm)
    (fun x => by
      by_cases hx : x ∈ Nt
      · simp [indicator_of_mem hx, indicator_of_mem ((hNtper x).2 hx)]
      · simp [indicator_of_notMem hx, indicator_of_notMem (mt (hNtper x).1 hx)])
  rw [lintegral_indicator_one hNtm, hNt0] at h
  simp only [mul_zero] at h
  have hmeas : Measurable fun z : ℝ × Space =>
      (Nt.indicator (1 : Coord → ℝ≥0∞)) (Axi.chart R z.1 z.2) :=
    (measurable_one.indicator hNtm).comp (measurable_chart R)
  have hz0 := (lintegral_eq_zero_iff hmeas).1 h
  filter_upwards [hz0] with z hz
  have hz' : Axi.chart R z.1 z.2 ∉ Nt := by
    by_contra hin
    simp [indicator_of_mem hin] at hz
  have hn1 : Axi.chart R z.1 z.2 ∉ N₁ := fun h1 =>
    hz' (Or.inr (mem_iUnion.2 ⟨0, by simpa [sh_zero] using h1⟩))
  have hpos : 0 < (Axi.chart R z.1 z.2).1 := by
    by_contra hle; exact hz' (Or.inl (not_lt.1 hle))
  by_contra hne
  exact hn1 (subset_toMeasurable _ _ (by simpa [hpos] using hne))

end UnforcedLeray.Short.IIb.PCB

open UnforcedLeray UnforcedLeray.Axi UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb.PCB
  UnforcedLeray.Short.IIb.PCAux in
theorem UnforcedLeray.Short.IIb.PCB.phase_chart_bochner_direct :
    UnforcedLeray.Short.IIb.PhaseChartBochner := by
  intro R c P G hR hc hP hint hper
  obtain ⟨G', hm, hp', hae⟩ := rep hc _ G hint hper
  have hgg : G =ᵐ[ageμ c (-(5 / 2))] G' := ae_ageμ_of_ae_vol hc _ hae
  have hint' : Integrable G' (ageμ c (-(5 / 2))) := hint.congr hgg
  obtain ⟨hi, hv⟩ := cplx_chart hR hc hP G' hm hp' hint'
  have hae2 := chart_ae hR hc hP hae
  have hP0 : 0 < P := by rw [hP]; exact div_pos (mul_pos two_pos hc) hR
  have hrow := Measure.ae_ae_of_ae_prod hae2
  have hcongr : ∫ t in Ioc 0 P, ∫ y, G (Axi.chart R t y) =
      ∫ t in Ioc 0 P, ∫ y, G' (Axi.chart R t y) := by
    refine integral_congr_ae ?_
    filter_upwards [hrow] with t ht
    exact integral_congr_ae ht
  have hprod : ∫ t in Ioc 0 P, ∫ y, G' (Axi.chart R t y) =
      ∫ z : ℝ × Space, G' (Axi.chart R z.1 z.2) ∂(PM P) := (integral_prod _ hi).symm
  unfold phaseInt
  rw [hcongr, hprod, hv, integral_congr_ae hgg, Complex.real_smul]
  have : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
  push_cast
  field_simp

#print axioms UnforcedLeray.Short.IIb.PCB.phase_chart_bochner_direct
