import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.PerAE
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.NullSets
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicRepresentative

/-!
# `PartII-b:P1/1/1/4`, `BLRCongr`: the periodic profile of an `H_p` class lifts a.e. like any
measurable representative.

Source of record: `the November 2 reference manuscript`, lines 1902-1906.
Strategy: `NvC` of `toProf c g` is the real lift of `g ∘ wrap` (the imaginary part vanishes);
the set where `g ∘ wrap ≠ perExt c B` is pulled back by the chart into a periodic null set
(`chartNullPullback` on one period, `blrPerAE_proof` for all phase times, and the product
`ae` lemma).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem blrCongr_imM_toProf {c : ℝ} (g : HpR c) (z : Coord) : imM (toProf c g z) = 0 := by
  ext i
  simp [imM, toProf]

theorem blrCongr_reM_toProf {c : ℝ} (g : HpR c) (z : Coord) :
    reM (toProf c g z) = (g : Coord → Axi.Merid) (z.1, (qwrap c z.2.1, z.2.2)) := by
  ext i
  simp [reM, toProf]

theorem blrCongr_NvC_eq {R c : ℝ} (g : HpR c) (x : ℝ × Space) :
    NvC R (toProf c g) x =
      UnforcedLeray.B0412.realC
        (Axi.Nv R (fun z => (g : Coord → Axi.Merid) (z.1, (qwrap c z.2.1, z.2.2))) x.1 x.2) := by
  have hz : Axi.Nv R (fun z => imM (toProf c g z)) x.1 x.2 = 0 := by
    have hfun : (fun z => imM (toProf c g z)) = fun _ => (0 : Axi.Merid) :=
      funext fun z => blrCongr_imM_toProf g z
    rw [hfun]
    simp [Axi.Nv]
  have hreal0 : UnforcedLeray.B0412.realC (0 : Space) = 0 := by
    simp [UnforcedLeray.B0412.realC]
  have hr : (fun z => reM (toProf c g z)) =
      fun z => (g : Coord → Axi.Merid) (z.1, (qwrap c z.2.1, z.2.2)) :=
    funext fun z => blrCongr_reM_toProf g z
  unfold NvC
  rw [hr, hz, hreal0, smul_zero, add_zero]

theorem blrCongr_proof : BLRCongr := by
  intro R c hR hc g B _hB hae
  have hRne : R ≠ 0 := hR.ne'
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 2 * c / R := ⟨_, rfl⟩
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
  -- (3) the chart pulls `M` back to a null set on one period
  have hstrip := chartNullPullback R c P hR hc hPdef M hMm hM0 hMper
  -- (4) extend to all phase times by periodicity
  have hper : ∀ τ : ℝ, (∀ᵐ y : Space, Axi.chart R (τ + P) y ∉ M) ↔
      (∀ᵐ y : Space, Axi.chart R τ y ∉ M) := by
    intro τ
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun y => ?_)
    rw [Axi.chart_add_period hRne hPdef τ y]
    exact not_congr (hMper (Axi.age R y) (Axi.phase R τ y) (Axi.trans R y))
  have hτ : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, Axi.chart R τ y ∉ M :=
    blrPerAE_proof P hPpos (fun τ => ∀ᵐ y : Space, Axi.chart R τ y ∉ M) hper hstrip
  -- (5) from the iterated `ae` to the `ae` on `ℝ × Space`
  have hchartm : Measurable (fun x : ℝ × Space => Axi.chart R x.1 x.2) :=
    ((Axi.measurable_age R).comp measurable_snd).prodMk
      ((Axi.measurable_phase R).prodMk ((Axi.measurable_trans R).comp measurable_snd))
  have hset : MeasurableSet {x : ℝ × Space | Axi.chart R x.1 x.2 ∉ M} :=
    (hMm.preimage hchartm).compl
  have hprod : ∀ᵐ x : ℝ × Space, Axi.chart R x.1 x.2 ∉ M := by
    rw [Measure.volume_eq_prod]
    exact (Measure.ae_prod_iff_ae_ae hset).2 hτ
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
