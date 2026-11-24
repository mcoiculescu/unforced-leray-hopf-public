import UnforcedLeray.Short.PartIIb.Sub.T07
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.NullSets
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicShifts
import UnforcedLeray.Lib.AxisymmetricB.Jv

/-!
# Part II-b, task `PartII-b:T07/7`: the measurable everywhere-periodic representative

Source of record: `the November 2 reference manuscript`, lines 1902-1906 (the
profile `b` of `H_r` is only almost everywhere `q`-periodic and measurable for `ageμ`, while the
lift `N_v` needs an everywhere periodic measurable representative).

Inputs: `NvCNorm.volume_null_of_ageμ_null` (`Tasks/NvCNorm/NullSets.lean`, T07/5),
`ae_qPeriodic_int_shift` and `measurePreserving_qShift` (`Tasks/NvCNorm/PeriodicShifts.lean`,
T07/6), and `Axi.cellRep`, `Axi.cellRep_add`, `Axi.measurable_cellRep` (`Lib/AxisymmetricB/Jv.lean`).

Construction. Let `b₀` be a measurable representative of `b` for `ageμ c (r/2 - 5/2)`, and
`b' (s, ξ, η) = b₀ (s, cellRep c ξ, η)`. Then `b'` is measurable and `c`-periodic. The bad set
`{0 < s, b ≠ b'}` lies in `(N₂ ∩ {s > 0}) ∪ ⋃_k (integer shift by k c)⁻¹' (N₁ ∩ halfcell)`,
where `N₁ = {b₀ ≠ b}` and `N₂ = {x | ¬ ∀ k, b (shift_k x) = b x}` (`QPeriodic` is a.e. on the half
space `s > 0` only, SP 1900-1903). Both are Lebesgue-null up to a measurable superset. The periodic hull `M = ⋃_k (shift_k)⁻¹' M₀` is measurable, null and periodic.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The representative of `ξ` in the centred cell lies in `[-c/2, c/2)`. -/
theorem periodicRep_cellRep_Ico {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    UnforcedLeray.Axi.cellRep c ξ ∈ Ico (-c / 2) (c / 2) := by
  have h1 := Int.floor_le ((ξ + c / 2) / c)
  have h2 := Int.lt_floor_add_one ((ξ + c / 2) / c)
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  unfold UnforcedLeray.Axi.cellRep
  rw [Set.mem_Ico]
  constructor <;> linarith

/-- The pair `(cellRep c ξ, η)` lies in the centred cell `qCell c`. -/
theorem periodicRep_mem_qCell {c : ℝ} (hc : 0 < c) (ξ η : ℝ) :
    (UnforcedLeray.Axi.cellRep c ξ, η) ∈ UnforcedLeray.Axi.qCell c := by
  unfold UnforcedLeray.Axi.qCell
  exact Set.mk_mem_prod (periodicRep_cellRep_Ico hc ξ) (Set.mem_univ η)

/-- Preimages of a measurable set under the shift `qShift s` are measurable. -/
theorem periodicRep_preimage_measurable {s : ℝ} {A : Set Coord} (hA : MeasurableSet A) :
    MeasurableSet (qShift s ⁻¹' A) :=
  (measurePreserving_qShift s).measurable hA

/-- Preimages of a Lebesgue-null measurable set under the shift `qShift s` are null. -/
theorem periodicRep_preimage_null {s : ℝ} {A : Set Coord} (hA : MeasurableSet A)
    (h0 : volume A = 0) : volume (qShift s ⁻¹' A) = 0 := by
  rw [(measurePreserving_qShift s).measure_preimage hA.nullMeasurableSet]
  exact h0

/-- The union of integer shifts of a set is `q`-periodic. -/
theorem periodicRep_iUnion_periodic (c : ℝ) (A : Set Coord) (s ξ η : ℝ) :
    (s, (ξ + c, η)) ∈ (⋃ k : ℤ, qShift ((k : ℝ) * c) ⁻¹' A) ↔
      (s, (ξ, η)) ∈ (⋃ k : ℤ, qShift ((k : ℝ) * c) ⁻¹' A) := by
  simp only [Set.mem_iUnion, Set.mem_preimage, qShift]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have e : ξ + ((k + 1 : ℤ) : ℝ) * c = ξ + c + (k : ℝ) * c := by push_cast; ring
    rw [e]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    have e : ξ + c + ((k - 1 : ℤ) : ℝ) * c = ξ + (k : ℝ) * c := by push_cast; ring
    rw [e]
    exact hk

/-- **`PartII-b:T07/7`: measurable everywhere-periodic representative.** -/
theorem periodicRepresentative : PeriodicRepresentative := by
  intro c r hc b hper hmeas
  have hmeas' : AEStronglyMeasurable b (Axi.ageμ c (r / 2 - 5 / 2)) := hmeas
  -- (1) a measurable representative `b₀` of `b` for `ageμ`
  obtain ⟨b₀, hb₀m, hb₀ae⟩ : ∃ b₀ : CProf, Measurable b₀ ∧
      b₀ =ᵐ[Axi.ageμ c (r / 2 - 5 / 2)] b :=
    ⟨hmeas'.mk b, hmeas'.stronglyMeasurable_mk.measurable, hmeas'.ae_eq_mk.symm⟩
  -- (2) the periodic copy `b' (s, ξ, η) = b₀ (s, cellRep c ξ, η)`
  obtain ⟨b', hb'def⟩ : ∃ b' : CProf, ∀ x : Coord,
      b' x = b₀ (x.1, (Axi.cellRep c x.2.1, x.2.2)) :=
    ⟨fun x => b₀ (x.1, (Axi.cellRep c x.2.1, x.2.2)), fun _ => rfl⟩
  have hb'm : Measurable b' := by
    have hfun : b' = fun x : Coord => b₀ (x.1, (Axi.cellRep c x.2.1, x.2.2)) :=
      funext hb'def
    rw [hfun]
    exact hb₀m.comp (measurable_fst.prodMk (((Axi.measurable_cellRep c).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))
  have hb'per : ∀ s ξ η, b' (s, (ξ + c, η)) = b' (s, (ξ, η)) := by
    intro s ξ η
    simp only [hb'def, Axi.cellRep_add hc.ne']
  -- (3) the bad sets: `N₁ = {b₀ ≠ b}` is `ageμ`-null, `N₂` is the failure of integer shifts
  have hN₁ : Axi.ageμ c (r / 2 - 5 / 2) {x : Coord | ¬ (b₀ x = b x)} = 0 :=
    MeasureTheory.ae_iff.1 hb₀ae
  obtain ⟨E₀, hE₀sub, hE₀m, hE₀0⟩ := exists_measurable_superset_of_null
    (NvCNorm.volume_null_of_ageμ_null hc hN₁)
  have hN₂ := MeasureTheory.ae_iff.1 (ae_qPeriodic_int_shift hper)
  obtain ⟨F, hFsub, hFm, hF0⟩ := exists_measurable_superset_of_null hN₂
  have hFH0 : volume (F ∩ {x : Coord | 0 < x.1}) = 0 := by
    rwa [Measure.restrict_apply hFm] at hF0
  -- (4) a measurable null set `M₀` containing `F ∩ {s > 0}` and all integer shifts of `E₀`
  obtain ⟨M₀, hFM₀, hEM₀, hM₀m, hM₀0⟩ : ∃ M₀ : Set Coord, F ∩ {x : Coord | 0 < x.1} ⊆ M₀ ∧
      (∀ k : ℤ, qShift ((k : ℝ) * c) ⁻¹' E₀ ⊆ M₀) ∧ MeasurableSet M₀ ∧ volume M₀ = 0 :=
    ⟨(F ∩ {x : Coord | 0 < x.1}) ∪ ⋃ k : ℤ, qShift ((k : ℝ) * c) ⁻¹' E₀, fun y hy => Or.inl hy,
      fun k y hy => Or.inr (Set.mem_iUnion.2 ⟨k, hy⟩),
      (hFm.inter measurableSet_halfSpace).union
        (MeasurableSet.iUnion fun k => periodicRep_preimage_measurable hE₀m),
      measure_union_null hFH0
        (measure_iUnion_null fun k => periodicRep_preimage_null hE₀m hE₀0)⟩
  -- (5) off `M₀` and on `s > 0`, `b = b'`
  have hkey : ∀ x : Coord, 0 < x.1 → x ∉ M₀ → b x = b' x := by
    intro x hx hxM
    -- (a) `x ∉ F ∩ {s > 0}` and `0 < s`, so `x` is good for all integer shifts
    have hall : ∀ k : ℤ, b (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = b x := by
      by_contra hcon
      have hxN : x ∈ {a : Coord | ¬ ∀ k : ℤ, b (a.1, (a.2.1 + (k : ℝ) * c, a.2.2)) = b a} :=
        hcon
      exact hxM (hFM₀ ⟨hFsub hxN, hx⟩)
    -- (b) the integer `k₀` moving `x.2.1` into the centred cell
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, Axi.cellRep c x.2.1 = x.2.1 + (k₀ : ℝ) * c :=
      ⟨-⌊(x.2.1 + c / 2) / c⌋, by unfold Axi.cellRep; push_cast; ring⟩
    have hw : (x.1, (x.2.1 + (k₀ : ℝ) * c, x.2.2)) = (x.1, (Axi.cellRep c x.2.1, x.2.2)) := by
      rw [hk₀]
    have hbw : b (x.1, (Axi.cellRep c x.2.1, x.2.2)) = b x := by
      rw [← hw]
      exact hall k₀
    -- (c) the centred point lies in the half cell, and is outside `E₀`
    have hwH : (x.1, (Axi.cellRep c x.2.1, x.2.2)) ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c :=
      Set.mk_mem_prod hx (periodicRep_mem_qCell hc x.2.1 x.2.2)
    have hxE : (x.1, (x.2.1 + (k₀ : ℝ) * c, x.2.2)) ∉ E₀ := fun h =>
      hxM (hEM₀ k₀ (show x ∈ qShift ((k₀ : ℝ) * c) ⁻¹' E₀ from h))
    have hwE : (x.1, (Axi.cellRep c x.2.1, x.2.2)) ∉ E₀ := by
      rw [← hw]
      exact hxE
    -- (d) `b₀ = b` at the centred point, else it would lie in `E₀`
    have hbw₀ : b₀ (x.1, (Axi.cellRep c x.2.1, x.2.2)) = b (x.1, (Axi.cellRep c x.2.1, x.2.2)) := by
      by_contra hne
      exact hwE (hE₀sub (show (x.1, (Axi.cellRep c x.2.1, x.2.2)) ∈
        {x : Coord | ¬ (b₀ x = b x)} ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c) from ⟨hne, hwH⟩))
    rw [hb'def x]
    exact hbw.symm.trans hbw₀.symm
  -- (6) the periodic hull of `M₀`
  refine ⟨b', ⋃ k : ℤ, qShift ((k : ℝ) * c) ⁻¹' M₀, hb'm, hb'per, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun k => periodicRep_preimage_measurable hM₀m
  · exact measure_iUnion_null fun k => periodicRep_preimage_null hM₀m hM₀0
  · exact fun s ξ η => periodicRep_iUnion_periodic c M₀ s ξ η
  · intro x hx hxM
    apply hkey x hx
    intro hxM₀
    apply hxM
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    show qShift (((0 : ℤ) : ℝ) * c) x ∈ M₀
    rw [Int.cast_zero, zero_mul, qShift_zero]
    exact hxM₀

end UnforcedLeray.Short.IIb
