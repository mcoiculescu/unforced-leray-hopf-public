import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.SPeriodic
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Helper for `PartII-b:T12/3`: a strongly measurable periodic representative in `q`

Used by `Tasks/FlatCausal/DuhamelMeasurable.lean`. Given `G` that is `c`-periodic in `q`
(`QPeriodic`) and a.e. measurable for the age-weighted measure `Axi.ageμ c a`, we construct a
strongly measurable `G'` that agrees with `G` Lebesgue-a.e. on `{s > 0}`.

The representative is `G' x = g0 (redCoord c x)`, where `g0` is a strongly measurable version of
`G` and `redCoord` reduces `q` into the cell `[-c/2, c/2)`. Periodicity transfers the a.e.
equality on the cell to a.e. equality on `Coord`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Translation `q ↦ q + a` on the chart `(s, (q, η))`. -/
def qSh (a : ℝ) (x : Coord) : Coord := (x.1, (x.2.1 + a, x.2.2))

/-- Reduction of `q` into the cell `[-c/2, c/2)`. -/
def redQ (c q : ℝ) : ℝ := -c / 2 + Int.fract ((q + c / 2) / c) * c

/-- Reduction of the `q`-variable of a point of `Coord`. -/
def redCoord (c : ℝ) (x : Coord) : Coord := (x.1, (redQ c x.2.1, x.2.2))

theorem qSh_zero (x : Coord) : qSh 0 x = x := by
  simp [qSh]

theorem qSh_add (a b : ℝ) (x : Coord) : qSh a (qSh b x) = qSh (a + b) x := by
  show (x.1, (x.2.1 + b + a, x.2.2)) = (x.1, (x.2.1 + (a + b), x.2.2))
  rw [show x.2.1 + b + a = x.2.1 + (a + b) by ring]

theorem qSh_measurePreserving (a : ℝ) :
    MeasurePreserving (qSh a) (volume : Measure Coord) (volume : Measure Coord) := by
  have h : MeasurePreserving (Prod.map id (Prod.map (fun t : ℝ => t + a) id))
      (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure (ℝ × (ℝ × ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      ((measurePreserving_add_right (volume : Measure ℝ) a).prod
        (MeasurePreserving.id (volume : Measure ℝ)))
  convert h using 1
  funext x
  rfl

theorem measurable_redQ (c : ℝ) : Measurable (redQ c) := by
  unfold redQ
  have h1 : Measurable (fun q : ℝ => Int.fract ((q + c / 2) / c)) :=
    measurable_fract.comp ((measurable_id.add_const (c / 2)).div_const c)
  exact measurable_const.add (h1.mul_const c)

theorem measurable_redCoord (c : ℝ) : Measurable (redCoord c) :=
  measurable_fst.prodMk
    (((measurable_redQ c).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

theorem redQ_eq (c : ℝ) (hc : 0 < c) (q : ℝ) :
    redQ c q = q + ((-(⌊(q + c / 2) / c⌋ : ℤ) : ℤ) : ℝ) * c := by
  have key : (q + c / 2) / c * c = q + c / 2 := div_mul_cancel₀ _ hc.ne'
  unfold redQ Int.fract
  push_cast
  rw [sub_mul, key]
  ring

theorem redQ_mem {c : ℝ} (hc : 0 < c) (q : ℝ) : redQ c q ∈ Ico (-c / 2) (c / 2) := by
  unfold redQ
  have h0 : 0 ≤ Int.fract ((q + c / 2) / c) := Int.fract_nonneg _
  have h1 : Int.fract ((q + c / 2) / c) < 1 := Int.fract_lt_one _
  have h2 : 0 ≤ Int.fract ((q + c / 2) / c) * c := mul_nonneg h0 hc.le
  have h3 : Int.fract ((q + c / 2) / c) * c < c := mul_lt_of_lt_one_left hc h1
  exact Set.mem_Ico.2 ⟨by linarith, by linarith⟩

/-- A strongly measurable, `q`-periodic-in-the-a.e.-sense representative of an a.e.-measurable
`c`-periodic profile, agreeing with `G` a.e. on `{s > 0}`. -/
theorem exists_periodic_rep {c a : ℝ} (hc : 0 < c) {G : CProf} (hQ : QPeriodic c G)
    (hG : AEStronglyMeasurable G (Axi.ageμ c a)) :
    ∃ G' : CProf, StronglyMeasurable G' ∧
      ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x := by
  obtain ⟨g0, hg0s, hae⟩ : ∃ g0 : CProf, StronglyMeasurable g0 ∧ G =ᵐ[Axi.ageμ c a] g0 :=
    ⟨hG.mk G, hG.stronglyMeasurable_mk, hG.ae_eq_mk⟩
  rw [ageμ_eq_withDensity hc a] at hae
  -- equality on the positive-density set
  have hE0 : ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ (Ioi (0 : ℝ) ×ˢ Axi.qCell c) → G x = g0 x := by
    have h := (ae_withDensity_iff (p := fun x => G x = g0 x) (measurable_dens c a)).1 hae
    filter_upwards [h] with x hx hmem
    apply hx
    have hxpos : (0 : ℝ) < x.1 := hmem.1
    unfold dens
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    exact (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hxpos a))).ne'
  -- `QPeriodic` is the a.e. periodicity on the half space `s > 0` (SP 1900-1903)
  have hQ' : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qSh c x) = G x :=
    QPerHalf.ae_imp hQ
  -- the shifts `q ↦ q + n c` preserve the a.e. periodicity on `s > 0`
  have hstep : ∀ m : ℤ,
      (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qSh ((m : ℝ) * c) x) = G x) →
      ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qSh (((m + 1 : ℤ) : ℝ) * c) x) = G x := by
    intro m hm
    have h1 : ∀ᵐ x ∂(volume : Measure Coord), 0 < (qSh ((m : ℝ) * c) x).1 →
        G (qSh c (qSh ((m : ℝ) * c) x)) = G (qSh ((m : ℝ) * c) x) :=
      (qSh_measurePreserving ((m : ℝ) * c)).quasiMeasurePreserving.ae hQ'
    have hrel : ∀ x : Coord, qSh (((m + 1 : ℤ) : ℝ) * c) x = qSh c (qSh ((m : ℝ) * c) x) := by
      intro x
      rw [qSh_add]
      congr 1
      push_cast
      ring
    filter_upwards [h1, hm] with x e1 e2 hx0
    rw [hrel x, e1 hx0, e2 hx0]
  have hdown : ∀ m : ℤ, (∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 →
      G (qSh (((m + 1 : ℤ) : ℝ) * c) x) = G x) →
      ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G (qSh ((m : ℝ) * c) x) = G x := by
    intro m hm
    have h1 : ∀ᵐ x ∂(volume : Measure Coord), 0 < (qSh ((m : ℝ) * c) x).1 →
        G (qSh c (qSh ((m : ℝ) * c) x)) = G (qSh ((m : ℝ) * c) x) :=
      (qSh_measurePreserving ((m : ℝ) * c)).quasiMeasurePreserving.ae hQ'
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
      G (qSh ((n : ℝ) * c) x) = G x := by
    intro n
    induction n using Int.induction_on with
    | zero => exact ae_of_all _ fun x _ => by simp [qSh_zero]
    | succ i ih => exact hstep (i : ℤ) ih
    | pred i ih =>
      exact hdown (-(i : ℤ) - 1) (by
        rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
        exact ih)
  have hall' : ∀ᵐ x ∂(volume : Measure Coord), ∀ n : ℤ, 0 < x.1 →
      G (qSh ((n : ℝ) * c) x) = G x :=
    ae_all_iff.2 hall
  -- the same for the equality on the cell
  have hE1 : ∀ᵐ x ∂(volume : Measure Coord), ∀ n : ℤ,
      (qSh ((n : ℝ) * c) x ∈ (Ioi (0 : ℝ) ×ˢ Axi.qCell c) →
        G (qSh ((n : ℝ) * c) x) = g0 (qSh ((n : ℝ) * c) x)) :=
    ae_all_iff.2 fun n => (qSh_measurePreserving ((n : ℝ) * c)).quasiMeasurePreserving.ae hE0
  refine ⟨fun x => g0 (redCoord c x), hg0s.comp_measurable (measurable_redCoord c), ?_⟩
  filter_upwards [hall', hE1] with x hx1 hx2 hpos
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
  show G x = g0 (redCoord c x)
  rw [hred, ← hx1 (-(⌊(x.2.1 + c / 2) / c⌋ : ℤ)) hpos]
  exact hx2 (-(⌊(x.2.1 + c / 2) / c⌋ : ℤ)) hmem

end UnforcedLeray.Short.IIb
