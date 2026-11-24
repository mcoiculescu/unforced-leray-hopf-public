import UnforcedLeray.Short.PartIIb.Sub.T12_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable.Periodic

/-!
# Sub-lemma `LerayLift/1` (`SlicePeriodicRep`), task `PartII-b:T12/2/1`

Source of record: `the November 2 reference manuscript` (periodize, SP 1923-1926).

The proof follows `exists_periodic_rep` (`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`),
but keeps the representative `F' = g0 ∘ redCoord c`, which is exactly `c`-periodic.
The Lebesgue-a.e. clause on `{s > 0}` and the `H_r`-a.e. clause both come from the
periodicity of `F` (a.e., for every shift `n c`) and from `dens` vanishing off `{s > 0} × qCell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem redQ_of_mem_cell {c q : ℝ} (hc : 0 < c) (hq : q ∈ Ico (-c / 2) (c / 2)) :
    redQ c q = q := by
  obtain ⟨h1, h2⟩ := hq
  have hfr : Int.fract ((q + c / 2) / c) = (q + c / 2) / c := by
    rw [Int.fract_eq_self]
    constructor
    · exact div_nonneg (by linarith) hc.le
    · rw [div_lt_one hc]
      linarith
  unfold redQ
  rw [hfr, div_mul_cancel₀ _ hc.ne']
  ring

theorem redQ_add_period {c : ℝ} (hc : 0 < c) (q : ℝ) : redQ c (q + c) = redQ c q := by
  have h : (q + c + c / 2) / c = (q + c / 2) / c + 1 := by
    rw [show q + c + c / 2 = (q + c / 2) + c by ring, add_div, div_self hc.ne']
  unfold redQ
  rw [h, Int.fract_add_one]

theorem redCoord_qShift {c : ℝ} (hc : 0 < c) (x : Coord) :
    redCoord c (qShift c x) = redCoord c x := by
  simp only [redCoord, qShift]
  rw [redQ_add_period hc]

theorem slicePeriodicRep_proof :
    UnforcedLeray.Short.IIb.LerayLiftSub.SlicePeriodicRep := by
  intro c r hc F hF
  set a : ℝ := r / 2 - 5 / 2 with ha
  have hMd : hMeas c r = (volume : Measure Coord).withDensity (dens c a) :=
    ageμ_eq_withDensity hc a
  obtain ⟨g0, hg0s, hae⟩ : ∃ g0 : CProf, StronglyMeasurable g0 ∧ F =ᵐ[hMeas c r] g0 :=
    ⟨hF.meas.mk F, hF.meas.stronglyMeasurable_mk, hF.meas.ae_eq_mk⟩
  -- `QPeriodic` is the a.e. periodicity on the half space `s > 0` (SP 1900-1903)
  have hQ : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F (qSh c x) = F x :=
    QPerHalf.ae_imp hF.periodic
  rw [hMd] at hae
  have hdens : ∀ᵐ x ∂(volume : Measure Coord), dens c a x ≠ 0 → F x = g0 x :=
    (ae_withDensity_iff (p := fun x => F x = g0 x) (measurable_dens c a)).1 hae
  have hE0 : ∀ᵐ x ∂(volume : Measure Coord), x ∈ (Ioi (0 : ℝ) ×ˢ Axi.qCell c) → F x = g0 x := by
    filter_upwards [hdens] with x hx hmem
    apply hx
    have hxpos : (0 : ℝ) < x.1 := hmem.1
    unfold dens
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    exact (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hxpos a))).ne'
  -- periodicity under the shifts `q ↦ q + n c`, almost everywhere
  have hstep : ∀ m : ℤ,
      (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F (qSh ((m : ℝ) * c) x) = F x) →
      ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F (qSh (((m + 1 : ℤ) : ℝ) * c) x) = F x := by
    intro m hm
    have h1 : ∀ᵐ x ∂(volume : Measure Coord), 0 < (qSh ((m : ℝ) * c) x).1 →
        F (qSh c (qSh ((m : ℝ) * c) x)) = F (qSh ((m : ℝ) * c) x) :=
      (qSh_measurePreserving ((m : ℝ) * c)).quasiMeasurePreserving.ae hQ
    have hrel : ∀ x : Coord, qSh (((m + 1 : ℤ) : ℝ) * c) x = qSh c (qSh ((m : ℝ) * c) x) := by
      intro x
      rw [qSh_add]
      congr 1
      push_cast
      ring
    filter_upwards [h1, hm] with x e1 e2 hx0
    rw [hrel x, e1 hx0, e2 hx0]
  have hdown : ∀ m : ℤ, (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 →
      F (qSh (((m + 1 : ℤ) : ℝ) * c) x) = F x) →
      ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F (qSh ((m : ℝ) * c) x) = F x := by
    intro m hm
    have h1 : ∀ᵐ x ∂(volume : Measure Coord), 0 < (qSh ((m : ℝ) * c) x).1 →
        F (qSh c (qSh ((m : ℝ) * c) x)) = F (qSh ((m : ℝ) * c) x) :=
      (qSh_measurePreserving ((m : ℝ) * c)).quasiMeasurePreserving.ae hQ
    have hrel : ∀ x : Coord, qSh (((m + 1 : ℤ) : ℝ) * c) x = qSh c (qSh ((m : ℝ) * c) x) := by
      intro x
      rw [qSh_add]
      congr 1
      push_cast
      ring
    filter_upwards [h1, hm] with x e1 e2 hx0
    have e3 := e2 hx0
    rw [hrel x, e1 hx0] at e3
    exact e3
  have hall : ∀ n : ℤ, ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 →
      F (qSh ((n : ℝ) * c) x) = F x := by
    intro n
    induction n using Int.induction_on with
    | zero => exact ae_of_all _ fun x _ => by simp [qSh_zero]
    | succ i ih => exact hstep (i : ℤ) ih
    | pred i ih =>
      exact hdown (-(i : ℤ) - 1) (by
        rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
        exact ih)
  have hall' : ∀ᵐ x ∂(volume : Measure Coord), ∀ n : ℤ, 0 < x.1 →
      F (qSh ((n : ℝ) * c) x) = F x :=
    ae_all_iff.2 hall
  have hE1 : ∀ᵐ x ∂(volume : Measure Coord), ∀ n : ℤ,
      (qSh ((n : ℝ) * c) x ∈ (Ioi (0 : ℝ) ×ˢ Axi.qCell c) →
        F (qSh ((n : ℝ) * c) x) = g0 (qSh ((n : ℝ) * c) x)) :=
    ae_all_iff.2 fun n => (qSh_measurePreserving ((n : ℝ) * c)).quasiMeasurePreserving.ae hE0
  refine ⟨fun x => g0 (redCoord c x), hg0s.comp_measurable (measurable_redCoord c), ?_, ?_, ?_⟩
  · intro s z
    exact congrArg g0 (redCoord_qShift hc (s, z))
  · rw [hMd, ae_withDensity_iff (measurable_dens c a)]
    filter_upwards [hdens] with x hx hxd
    have hm : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c := by
      by_contra h
      apply hxd
      simp [dens, Set.indicator_of_notMem h]
    have hcell : x.2 ∈ Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := (Set.mem_prod.1 hm).2
    have hq : x.2.1 ∈ Ico (-c / 2) (c / 2) := (Set.mem_prod.1 hcell).1
    have hrc : redCoord c x = x := by
      simp only [redCoord]
      rw [redQ_of_mem_cell hc hq]
    show F x = g0 (redCoord c x)
    rw [hrc]
    exact hx hxd
  · filter_upwards [hall', hE1] with x hx1 hx2 hpos
    have hred : redCoord c x = qSh (((-(⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℤ) : ℝ) * c) x := by
      simp only [redCoord, qSh]
      rw [redQ_eq c hc]
    have hmem : qSh (((-(⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℤ) : ℝ) * c) x ∈
        (Ioi (0 : ℝ) ×ˢ Axi.qCell c) := by
      rw [← hred, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · exact hpos
      · unfold Axi.qCell
        rw [Set.mem_prod]
        exact ⟨redQ_mem hc _, Set.mem_univ _⟩
    show F x = g0 (redCoord c x)
    rw [hred, ← hx1 (-(⌊(x.2.1 + c / 2) / c⌋ : ℤ)) hpos]
    exact hx2 (-(⌊(x.2.1 + c / 2) / c⌋ : ℤ)) hmem

end UnforcedLeray.Short.IIb.LerayLiftSub
