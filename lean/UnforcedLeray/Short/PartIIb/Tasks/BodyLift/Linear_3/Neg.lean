import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.Congr

/-!
# `PartII-b:P1/1/3`: the lift congruence for negative `R`

Source: `the November 2 reference manuscript` lines 1902-1906. Reduction to
`R > 0` by the reflection `σ (s, (ξ, η)) = (s, (-ξ, -η))`: `chart R τ y = σ (chart (-R) τ y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem linear3_chart_neg (R τ : ℝ) (y : Space) :
    Axi.chart R τ y =
      ((Axi.chart (-R) τ y).1, (-(Axi.chart (-R) τ y).2.1, -(Axi.chart (-R) τ y).2.2)) := by
  simp only [Axi.chart, Axi.age, Axi.phase, Axi.trans, neg_sq]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only; ring
  · simp only; ring

theorem linear3_refl_null {M : Set Coord} (hM : MeasurableSet M) (h0 : volume M = 0) :
    volume ((fun z : Coord => (z.1, (-z.2.1, -z.2.2))) ⁻¹' M) = 0 := by
  have hσ : MeasurePreserving (fun z : Coord => (z.1, (-z.2.1, -z.2.2))) volume volume := by
    have := (MeasurePreserving.id (volume : Measure ℝ)).prod
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ)))
    exact this
  rw [hσ.measure_preimage hM.nullMeasurableSet]
  exact h0

theorem blrCongrNeg_core (R c : ℝ) (hRneg : R < 0) (hc : 0 < c)
    (g : HpR c) (B : ℝ × (ℝ × ℝ) → Axi.Merid) (_hB : Measurable B)
    (hae : (g : ℝ × (ℝ × ℝ) → Axi.Merid) =ᵐ[hMeas c bgp] B) :
    ∀ᵐ x : ℝ × Space, NvC R (toProf c g) x =
      UnforcedLeray.B0412.realC (Axi.Nv R (Axi.perExt c B) x.1 x.2) := by
  have hR : 0 < -R := by linarith
  have hRne : -R ≠ 0 := hR.ne'
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 2 * c / (-R) := ⟨_, rfl⟩
  have hPpos : 0 < P := by
    rw [hPdef]
    exact div_pos (by linarith) hR
  -- (1) the bad set on the profile space and a measurable null superset
  have hN : Axi.ageμ c (bgp / 2 - 5 / 2)
      {w : Coord | ¬ ((g : Coord → Axi.Merid) w = B w)} = 0 :=
    ae_iff.1 hae
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  have hM0m : MeasurableSet (N' ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) :=
    hN'm.inter (Axi.measurableSet_halfCell c)
  have hM0_0 : volume (N' ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) = 0 :=
    NvCNorm.volume_null_of_ageμ_null hc hN'0
  -- (2) the periodic hull `M` of the half-cell part of `N'`
  obtain ⟨M, hMdef⟩ : ∃ M : Set Coord,
      M = ⋃ k : ℤ, qShift ((k : ℝ) * c) ⁻¹' (N' ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) :=
    ⟨_, rfl⟩
  have hMm : MeasurableSet M := by
    rw [hMdef]
    exact MeasurableSet.iUnion fun k => periodicRep_preimage_measurable hM0m
  have hM0 : volume M = 0 := by
    rw [hMdef]
    exact measure_iUnion_null fun k => periodicRep_preimage_null hM0m hM0_0
  have hMper : ∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M := by
    intro s ξ η
    rw [hMdef]
    exact periodicRep_iUnion_periodic c _ s ξ η
  -- (3) reflect: `M' = σ ⁻¹' M` is periodic and null, and `chart R = σ ∘ chart (-R)`
  obtain ⟨M', hM'def⟩ : ∃ M' : Set Coord,
      M' = (fun z : Coord => (z.1, (-z.2.1, -z.2.2))) ⁻¹' M := ⟨_, rfl⟩
  have hσm : Measurable (fun z : Coord => (z.1, (-z.2.1, -z.2.2))) :=
    measurable_fst.prodMk (((measurable_fst.comp measurable_snd).neg).prodMk
      ((measurable_snd.comp measurable_snd).neg))
  have hM'm : MeasurableSet M' := by
    rw [hM'def]; exact hMm.preimage hσm
  have hM'0 : volume M' = 0 := by
    rw [hM'def]; exact linear3_refl_null hMm hM0
  have hM'per : ∀ s ξ η, (s, (ξ + c, η)) ∈ M' ↔ (s, (ξ, η)) ∈ M' := by
    intro s ξ η
    have h := hMper s (-(ξ + c)) (-η)
    rw [show -(ξ + c) + c = -ξ by ring] at h
    rw [hM'def]
    exact h.symm
  have hchartM : ∀ τ y, Axi.chart (-R) τ y ∈ M' ↔ Axi.chart R τ y ∈ M := by
    intro τ y
    rw [hM'def, Set.mem_preimage, linear3_chart_neg R τ y]
  have hstrip := chartNullPullback (-R) c P hR hc hPdef M' hM'm hM'0 hM'per
  -- (4) extend to all phase times by periodicity
  have hper : ∀ τ : ℝ, (∀ᵐ y : Space, Axi.chart (-R) (τ + P) y ∉ M') ↔
      (∀ᵐ y : Space, Axi.chart (-R) τ y ∉ M') := by
    intro τ
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun y => ?_)
    rw [Axi.chart_add_period hRne hPdef τ y]
    exact not_congr (hM'per (Axi.age (-R) y) (Axi.phase (-R) τ y) (Axi.trans (-R) y))
  have hτ : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, Axi.chart (-R) τ y ∉ M' :=
    blrPerAE_proof P hPpos (fun τ => ∀ᵐ y : Space, Axi.chart (-R) τ y ∉ M') hper hstrip
  -- (5) from the iterated `ae` to the `ae` on `ℝ × Space`
  have hchartm : Measurable (fun x : ℝ × Space => Axi.chart (-R) x.1 x.2) :=
    ((Axi.measurable_age (-R)).comp measurable_snd).prodMk
      ((Axi.measurable_phase (-R)).prodMk ((Axi.measurable_trans (-R)).comp measurable_snd))
  have hset : MeasurableSet {x : ℝ × Space | Axi.chart (-R) x.1 x.2 ∉ M'} :=
    (hM'm.preimage hchartm).compl
  have hprod' : ∀ᵐ x : ℝ × Space, Axi.chart (-R) x.1 x.2 ∉ M' := by
    rw [Measure.volume_eq_prod]
    exact (Measure.ae_prod_iff_ae_ae hset).2 hτ
  have hprod : ∀ᵐ x : ℝ × Space, Axi.chart R x.1 x.2 ∉ M := by
    filter_upwards [hprod'] with x hx
    exact fun h => hx ((hchartM x.1 x.2).2 h)
  -- (6) off `M`, the wrapped profile agrees with `perExt c B`
  have ptwise : ∀ z : Coord, z ∉ M → 0 < z.1 →
      (g : Coord → Axi.Merid) (z.1, (qwrap c z.2.1, z.2.2)) = Axi.perExt c B z := by
    intro z hzM hzpos
    by_contra hne
    apply hzM
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, Axi.cellRep c z.2.1 = z.2.1 + (k₀ : ℝ) * c :=
      ⟨-⌊(z.2.1 + c / 2) / c⌋, by unfold Axi.cellRep; push_cast; ring⟩
    have hWN : (z.1, (Axi.cellRep c z.2.1, z.2.2)) ∈ N' :=
      hNN' (show (z.1, (Axi.cellRep c z.2.1, z.2.2)) ∈
          {w : Coord | ¬ ((g : Coord → Axi.Merid) w = B w)} from fun h => hne h)
    have hmem : qShift ((k₀ : ℝ) * c) z ∈ N' ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c) := by
      have e : qShift ((k₀ : ℝ) * c) z = (z.1, (Axi.cellRep c z.2.1, z.2.2)) := by
        rw [qShift, hk₀]
      rw [e]
      exact ⟨hWN, Set.mk_mem_prod hzpos (periodicRep_mem_qCell hc z.2.1 z.2.2)⟩
    rw [hMdef]
    exact Set.mem_iUnion.2 ⟨k₀, hmem⟩
  -- (7) the lifted real fields agree off the chart pull-back of `M`
  have hNv : ∀ (τ : ℝ) (y : Space), Axi.chart R τ y ∉ M →
      Axi.Nv R (fun z => (g : Coord → Axi.Merid) (z.1, (qwrap c z.2.1, z.2.2))) τ y =
        Axi.Nv R (Axi.perExt c B) τ y := by
    intro τ y hz
    rcases (Axi.age_nonneg R y).eq_or_lt with h0 | hpos
    · simp [Axi.Nv, ← h0]
    · simp only [Axi.Nv]
      rw [ptwise (Axi.chart R τ y) hz hpos]
  filter_upwards [hprod] with x hx
  rw [blrCongr_NvC_eq, hNv x.1 x.2 hx]

end UnforcedLeray.Short.IIb
