import UnforcedLeray.Short.PartIIIb.NearInst.Chart
import UnforcedLeray.Units.B0220.ChangeOfVariables

/-!
# Recentring of the profile cell onto the chart cell (helper for the bridge leaves)

`NearInst.cellPt c p = (s, recentre q, η)` maps the profile cell `(0,c]` in `q` onto the chart cell
`[-c/2, c/2)` in `q`. Its pushforward of `measureH c` is `c • ageμ c (-3/2)`
(`map_cellPt_measureH`). `ae_ageμ_of_ae_cellPt` transfers a.e. statements from the profile to the
chart. Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.CellMap

/-- One-dimensional recentring: the integral over `(0,c]` of `h ∘ recentre` is the integral over
`[-c/2, c/2)` of `h`. -/
theorem lintegral_recentre {c : ℝ} (hc : 0 < c) (h : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioc 0 c, h (if q < c / 2 then q else q - c) = ∫⁻ x in Ico (-c / 2) (c / 2), h x := by
  have hA : Ioc 0 c = Ioo 0 (c / 2) ∪ Icc (c / 2) c := by
    ext q
    simp only [mem_Ioc, mem_union, mem_Ioo, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hq : q < c / 2
      · exact Or.inl ⟨h1, hq⟩
      · exact Or.inr ⟨not_lt.1 hq, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  have hB : Ico (-c / 2) (c / 2) = Icc (-c / 2) 0 ∪ Ioo 0 (c / 2) := by
    ext x
    simp only [mem_Ico, mem_union, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hx : x ≤ 0
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr ⟨lt_of_not_ge hx, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  have hd1 : Disjoint (Ioo 0 (c / 2)) (Icc (c / 2) c) := by
    rw [Set.disjoint_left]
    intro q hq1 hq2
    linarith [hq1.2, hq2.1]
  have hd2 : Disjoint (Icc (-c / 2) 0) (Ioo 0 (c / 2)) := by
    rw [Set.disjoint_left]
    intro q hq1 hq2
    linarith [hq1.2, hq2.1]
  have e1 : ∫⁻ q in Ioo 0 (c / 2), h (if q < c / 2 then q else q - c) =
      ∫⁻ q in Ioo 0 (c / 2), h q :=
    setLIntegral_congr_fun measurableSet_Ioo fun q hq => by rw [if_pos hq.2]
  have e2 : ∫⁻ q in Icc (c / 2) c, h (if q < c / 2 then q else q - c) =
      ∫⁻ q in Icc (c / 2) c, h (q - c) :=
    setLIntegral_congr_fun measurableSet_Icc fun q hq => by rw [if_neg (not_lt.2 hq.1)]
  have ind : ∀ q : ℝ, (Icc (c / 2) c).indicator (fun q => h (q - c)) q =
      (Icc (-c / 2) 0).indicator h (q - c) := by
    intro q
    by_cases hq : q ∈ Icc (c / 2) c
    · have hq' : q - c ∈ Icc (-c / 2) 0 := ⟨by linarith [hq.1], by linarith [hq.2]⟩
      rw [indicator_of_mem hq, indicator_of_mem hq']
    · have hq' : q - c ∉ Icc (-c / 2) 0 := fun h' => hq ⟨by linarith [h'.1], by linarith [h'.2]⟩
      rw [indicator_of_notMem hq, indicator_of_notMem hq']
  have e3 : ∫⁻ q in Icc (c / 2) c, h (q - c) = ∫⁻ x in Icc (-c / 2) 0, h x := by
    calc ∫⁻ q in Icc (c / 2) c, h (q - c)
        = ∫⁻ q, (Icc (c / 2) c).indicator (fun q => h (q - c)) q := by
          rw [lintegral_indicator measurableSet_Icc]
      _ = ∫⁻ q, (Icc (-c / 2) 0).indicator h (q - c) := lintegral_congr ind
      _ = ∫⁻ x, (Icc (-c / 2) 0).indicator h x := lintegral_sub_right_eq_self _ c
      _ = ∫⁻ x in Icc (-c / 2) 0, h x := by
          rw [lintegral_indicator measurableSet_Icc]
  rw [hA, lintegral_union measurableSet_Icc hd1, hB, lintegral_union measurableSet_Ioo hd2,
    e1, e2, e3]
  exact add_comm _ _

/-- Iterated integral over `(0,∞) × S × ℝ` for a measurable `F` on the chart. -/
theorem lintegral_cylSet (S : Set ℝ) (F : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ (S ×ˢ univ), F p =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ q in S, ∫⁻ η, F (s, q, η) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun s => ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun y : ℝ × ℝ => F (s, y)) (hF.comp measurable_prodMk_left).aemeasurable]

theorem measurable_cellPt' (c : ℝ) : Measurable (NearInst.cellPt c) := by
  unfold NearInst.cellPt
  refine measurable_fst.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine Measurable.ite ?_ (measurable_fst.comp measurable_snd)
    ((measurable_fst.comp measurable_snd).sub_const c)
  exact measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const

/-- Integral of `f ∘ cellPt` against `measureH c`, as `c` times the integral against `ageμ`. -/
theorem lintegral_cellPt {c : ℝ} (hc : 0 < c) (f : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f (NearInst.cellPt c p) ∂(UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c * ∫⁻ x, f x ∂(ageμ c (-(3 / 2))) := by
  have hcp := measurable_cellPt' c
  have hfc : Measurable fun p : UnforcedLeray.B0220.Profile => f (NearInst.cellPt c p) :=
    hf.comp hcp
  have step1 : ∫⁻ p, f (NearInst.cellPt c p) ∂(UnforcedLeray.B0220.measureH c) =
      ∫⁻ p in UnforcedLeray.B0220.cell c,
        UnforcedLeray.B0220.weightH p * f (NearInst.cellPt c p) := by
    rw [UnforcedLeray.B0220.measureH,
      lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH hfc]
    rfl
  have step2 : ∫⁻ p in UnforcedLeray.B0220.cell c,
        UnforcedLeray.B0220.weightH p * f (NearInst.cellPt c p) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ q in Ioc 0 c, ∫⁻ η,
        UnforcedLeray.B0220.weightH (s, q, η) * f (NearInst.cellPt c (s, q, η)) := by
    unfold UnforcedLeray.B0220.cell
    exact lintegral_cylSet (Ioc 0 c)
      (fun p => UnforcedLeray.B0220.weightH p * f (NearInst.cellPt c p))
      (UnforcedLeray.B0220.measurable_weightH.mul hfc)
  have step3 : ∀ s : ℝ, ∫⁻ q in Ioc 0 c, ∫⁻ η,
        UnforcedLeray.B0220.weightH (s, q, η) * f (NearInst.cellPt c (s, q, η)) =
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        ∫⁻ x in Ico (-c / 2) (c / 2), ∫⁻ η, f (s, x, η) := by
    intro s
    have hinner : ∀ q : ℝ, ∫⁻ η,
        UnforcedLeray.B0220.weightH (s, q, η) * f (NearInst.cellPt c (s, q, η)) =
        ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          ∫⁻ η, f (s, (if q < c / 2 then q else q - c), η) := by
      intro q
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun η => ?_
      rfl
    calc ∫⁻ q in Ioc 0 c, ∫⁻ η,
          UnforcedLeray.B0220.weightH (s, q, η) * f (NearInst.cellPt c (s, q, η))
        = ∫⁻ q in Ioc 0 c, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            ∫⁻ η, f (s, (if q < c / 2 then q else q - c), η) := lintegral_congr hinner
      _ = ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            ∫⁻ q in Ioc 0 c, ∫⁻ η, f (s, (if q < c / 2 then q else q - c), η) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            ∫⁻ x in Ico (-c / 2) (c / 2), ∫⁻ η, f (s, x, η) := by
          congr 1
          exact lintegral_recentre hc (fun x => ∫⁻ η, f (s, x, η))
  have hF2 : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(3 / 2 : ℝ))) * f p := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul hf
    exact measurable_const.mul (measurable_fst.pow_const _)
  rw [step1, step2]
  refine (setLIntegral_congr_fun measurableSet_Ioi fun s _ => step3 s).trans ?_
  rw [lintegral_ageμ hc (-(3 / 2)) hf, qCell]
  rw [lintegral_cylSet (Ico (-c / 2) (c / 2))
    (fun p => ENNReal.ofReal (c⁻¹ * p.1 ^ (-(3 / 2 : ℝ))) * f p) hF2]
  rw [← lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  dsimp only
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le]
  have hcc : c * (c⁻¹ * s ^ (-(3 / 2 : ℝ))) = s ^ (-(3 / 2 : ℝ)) := by
    field_simp
  rw [hcc]

/-- The measure identity on sets: `measureH c` of the preimage under `cellPt` is `c · ageμ`. -/
theorem measureH_preimage_cellPt {c : ℝ} (hc : 0 < c) {A : Set (ℝ × (ℝ × ℝ))}
    (hA : MeasurableSet A) :
    UnforcedLeray.B0220.measureH c (NearInst.cellPt c ⁻¹' A) =
      ENNReal.ofReal c * ageμ c (-(3 / 2)) A := by
  have hcp := measurable_cellPt' c
  have hpre : MeasurableSet (NearInst.cellPt c ⁻¹' A) := hcp hA
  calc UnforcedLeray.B0220.measureH c (NearInst.cellPt c ⁻¹' A)
      = ∫⁻ p, (NearInst.cellPt c ⁻¹' A).indicator 1 p ∂(UnforcedLeray.B0220.measureH c) :=
        (lintegral_indicator_one hpre).symm
    _ = ∫⁻ p, A.indicator 1 (NearInst.cellPt c p) ∂(UnforcedLeray.B0220.measureH c) := by
        refine lintegral_congr fun p => ?_
        by_cases hp : NearInst.cellPt c p ∈ A
        · rw [Set.indicator_of_mem (show p ∈ NearInst.cellPt c ⁻¹' A from hp),
            Set.indicator_of_mem hp]
          rfl
        · rw [Set.indicator_of_notMem (show p ∉ NearInst.cellPt c ⁻¹' A from hp),
            Set.indicator_of_notMem hp]
    _ = ENNReal.ofReal c * ∫⁻ x, A.indicator 1 x ∂(ageμ c (-(3 / 2))) :=
        lintegral_cellPt hc (A.indicator 1) (measurable_const.indicator hA)
    _ = ENNReal.ofReal c * ageμ c (-(3 / 2)) A := by rw [lintegral_indicator_one hA]

/-- The pushforward of `measureH c` under `cellPt` is `c • ageμ c (-3/2)`. -/
theorem map_cellPt_measureH {c : ℝ} (hc : 0 < c) :
    (UnforcedLeray.B0220.measureH c).map (NearInst.cellPt c) =
      ENNReal.ofReal c • ageμ c (-(3 / 2)) := by
  ext A hA
  rw [Measure.map_apply (measurable_cellPt' c) hA, Measure.smul_apply, smul_eq_mul,
    measureH_preimage_cellPt hc hA]

/-- The chart region of recentred points: `s > 0`, `q ∈ [-c/2, c/2)`. -/
def regionX (c : ℝ) : Set (ℝ × (ℝ × ℝ)) := Ioi (0 : ℝ) ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ)

theorem measurableSet_regionX (c : ℝ) : MeasurableSet (regionX c) :=
  measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)

/-- Inverse of the recentring on the chart region. -/
def psiInv (c : ℝ) (x : ℝ × (ℝ × ℝ)) : UnforcedLeray.B0220.Profile :=
  (x.1, (if 0 < x.2.1 then x.2.1 else x.2.1 + c, x.2.2))

theorem measurable_psiInv (c : ℝ) : Measurable (psiInv c) := by
  unfold psiInv
  refine measurable_fst.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine Measurable.ite ?_ (measurable_fst.comp measurable_snd)
    ((measurable_fst.comp measurable_snd).add_const c)
  exact measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)

theorem psiInv_cellPt {c : ℝ} {p : UnforcedLeray.B0220.Profile}
    (hp : p ∈ UnforcedLeray.B0220.cell c) : psiInv c (NearInst.cellPt c p) = p := by
  obtain ⟨s, q, η⟩ := p
  have hs : 0 < s := hp.1
  have hq : q ∈ Ioc 0 c := hp.2.1
  by_cases hq' : q < c / 2
  · have h1 : 0 < q := hq.1
    simp [psiInv, NearInst.cellPt, hq', h1]
  · have h2 : ¬ (0 < q - c) := not_lt.2 (by linarith [hq.2])
    simp [psiInv, NearInst.cellPt, hq', h2]

theorem cellPt_psiInv {c : ℝ} {x : ℝ × (ℝ × ℝ)} (hx : x ∈ regionX c) :
    NearInst.cellPt c (psiInv c x) = x := by
  obtain ⟨s, q, η⟩ := x
  have hs : 0 < s := hx.1
  have hq : q ∈ Ico (-c / 2) (c / 2) := hx.2.1
  by_cases h0 : 0 < q
  · have hlt : q < c / 2 := hq.2
    simp [psiInv, NearInst.cellPt, h0, hlt]
  · have h2 : c / 2 ≤ q + c := by linarith [hq.1]
    have hlt : ¬ (q + c < c / 2) := not_lt.2 h2
    simp [psiInv, NearInst.cellPt, h0, hlt]

theorem cellPt_mem_regionX {c : ℝ} (hc : 0 < c) {p : UnforcedLeray.B0220.Profile}
    (hp : p ∈ UnforcedLeray.B0220.cell c) : NearInst.cellPt c p ∈ regionX c := by
  obtain ⟨s, q, η⟩ := p
  have hs : 0 < s := hp.1
  have hq : q ∈ Ioc 0 c := hp.2.1
  unfold regionX NearInst.cellPt
  by_cases h : q < c / 2
  · rw [if_pos h]
    exact ⟨hs, ⟨by linarith [hq.1], h⟩, trivial⟩
  · rw [if_neg h]
    exact ⟨hs, ⟨by linarith [hq.2], by linarith [hq.2]⟩, trivial⟩

/-- **Null-set transfer.** An `ageμ c (-3/2)`-a.e. statement is the same as a `measureH c`-a.e.
statement at the recentred point. -/
theorem ae_ageμ_of_ae_cellPt {c : ℝ} (hc : 0 < c) {P : ℝ × (ℝ × ℝ) → Prop}
    (hP : ∀ᵐ p ∂(UnforcedLeray.B0220.measureH c), P (NearInst.cellPt c p)) :
    ∀ᵐ x ∂(ageμ c (-(3 / 2))), P x := by
  rw [ae_iff] at hP ⊢
  set N : Set (ℝ × (ℝ × ℝ)) := {x | ¬ P x} with hN
  have hPN : UnforcedLeray.B0220.measureH c (NearInst.cellPt c ⁻¹' N) = 0 := hP
  set Tp := toMeasurable (UnforcedLeray.B0220.measureH c) (NearInst.cellPt c ⁻¹' N) with hTp
  have hTpm : MeasurableSet Tp := measurableSet_toMeasurable _ _
  have hTp0 : UnforcedLeray.B0220.measureH c Tp = 0 := by
    rw [hTp, measure_toMeasurable]
    exact hPN
  have hcell0 : UnforcedLeray.B0220.measureH c (UnforcedLeray.B0220.cell c)ᶜ = 0 := by
    have h0 : UnforcedLeray.B0220.cellMeasure c (UnforcedLeray.B0220.cell c)ᶜ = 0 := by
      rw [UnforcedLeray.B0220.cellMeasure,
        Measure.restrict_apply (UnforcedLeray.B0220.measurableSet_cell c).compl]
      simp
    exact withDensity_absolutelyContinuous _ _ h0
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hAA : ageμ c (-(3 / 2)) (psiInv c ⁻¹' Tp) = 0 := by
    have hcpre : UnforcedLeray.B0220.measureH c
        (NearInst.cellPt c ⁻¹' (psiInv c ⁻¹' Tp)) = 0 := by
      apply measure_mono_null (t := Tp ∪ (UnforcedLeray.B0220.cell c)ᶜ)
      · intro p hp
        by_cases hpc : p ∈ UnforcedLeray.B0220.cell c
        · left
          have e : psiInv c (NearInst.cellPt c p) = p := psiInv_cellPt hpc
          have hp' : psiInv c (NearInst.cellPt c p) ∈ Tp := hp
          rw [e] at hp'
          exact hp'
        · right
          exact hpc
      · exact measure_union_null hTp0 hcell0
    have := measureH_preimage_cellPt hc (measurable_psiInv c hTpm)
    rw [hcpre] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hc0
  have hRc : ageμ c (-(3 / 2)) (regionX c)ᶜ = 0 := by
    have hpre0 : UnforcedLeray.B0220.measureH c (NearInst.cellPt c ⁻¹' (regionX c)ᶜ) = 0 := by
      apply measure_mono_null (t := (UnforcedLeray.B0220.cell c)ᶜ)
      · intro p hp hpc
        exact hp (cellPt_mem_regionX hc hpc)
      · exact hcell0
    have := measureH_preimage_cellPt hc (measurableSet_regionX c).compl
    rw [hpre0] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hc0
  have hNsub : N ⊆ psiInv c ⁻¹' Tp ∪ (regionX c)ᶜ := by
    intro x hx
    by_cases hxR : x ∈ regionX c
    · left
      have hcx : NearInst.cellPt c (psiInv c x) = x := cellPt_psiInv hxR
      apply subset_toMeasurable
      show NearInst.cellPt c (psiInv c x) ∈ N
      rw [hcx]
      exact hx
    · right
      exact hxR
  exact measure_mono_null hNsub (measure_union_null hAA hRc)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.CellMap
