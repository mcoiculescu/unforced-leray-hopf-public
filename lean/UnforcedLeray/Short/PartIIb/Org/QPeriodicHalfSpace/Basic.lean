import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b: `q`-periodicity on the half space `s > 0`

Source of record: `the November 2 reference manuscript`, lines 1900-1903 (the
spaces `H_r` live on `s > 0`). Since `QPeriodic c b` (`Short/PartII-b/Defs.lean`) is the
almost-everywhere identity `b (qShift c x) = b x` for `volume.restrict {x | 0 < x.1}`, these are
the conversions used by its consumers: the equivalent unrestricted form with the implication
`0 < x.1 → _` (`ae_restrict_iff'`), the passage from a global almost-everywhere identity, and the
global periodicity of a cut-off `{δ < s}.indicator g` for `0 ≤ δ` (the shift fixes `s`).
-/

open MeasureTheory Filter Set

namespace UnforcedLeray.Short.IIb.QPerHalf

/-- The half space `{s > 0}` is measurable. -/
theorem measurableSet_pos : MeasurableSet {x : Coord | 0 < x.1} :=
  measurableSet_lt measurable_const measurable_fst

/-- `QPeriodic` as an unrestricted almost-everywhere statement on `s > 0`. -/
theorem ae_imp {c : ℝ} {b : CProf} (h : QPeriodic c b) :
    ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x :=
  (ae_restrict_iff' measurableSet_pos).1 h

/-- The converse of `ae_imp`. -/
theorem of_ae_imp {c : ℝ} {b : CProf} (h : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x) :
    QPeriodic c b :=
  (ae_restrict_iff' measurableSet_pos).2 h

/-- A globally almost-everywhere periodic profile is `QPeriodic`. -/
theorem of_ae {c : ℝ} {b : CProf} (h : ∀ᵐ x : Coord, b (qShift c x) = b x) : QPeriodic c b :=
  ae_restrict_of_ae h

/-- The first coordinate is fixed by the shift. -/
@[simp] theorem qShift_fst (c : ℝ) (x : Coord) : (qShift c x).1 = x.1 := rfl

/-- A function periodic almost everywhere on `s > 0` becomes globally almost-everywhere periodic
after the cut-off to `{δ < s}`, `0 ≤ δ`. -/
theorem indicator_ae {E : Type*} [Zero E] {c δ : ℝ} (hδ : 0 ≤ δ) {g : Coord → E}
    (h : ∀ᵐ x : Coord, 0 < x.1 → g (qShift c x) = g x) :
    ∀ᵐ x : Coord, ({x : Coord | δ < x.1}.indicator g) (qShift c x) =
      ({x : Coord | δ < x.1}.indicator g) x := by
  filter_upwards [h] with x hx
  by_cases hxs : δ < x.1
  · have hx' : qShift c x ∈ {x : Coord | δ < x.1} := hxs
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem (show x ∈ {x : Coord | δ < x.1} from hxs)]
    exact hx (lt_of_le_of_lt hδ hxs)
  · have hx' : qShift c x ∉ {x : Coord | δ < x.1} := hxs
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem
      (show x ∉ {x : Coord | δ < x.1} from hxs)]

end UnforcedLeray.Short.IIb.QPerHalf
