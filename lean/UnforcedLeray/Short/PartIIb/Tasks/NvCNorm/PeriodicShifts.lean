import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b, task `PartII-b:NvCNorm/PeriodicShifts`: almost-everywhere integer shifts

Source of record: `the November 2 reference manuscript`, lines 1900-1906 (the
spaces `H_r` live on the half space `s > 0`; their profiles are only almost everywhere
`q`-periodic, which the `T07/7` step upgrades to an everywhere periodic representative).
`QPeriodic c b` is `∀ᵐ x ∂(volume.restrict {x | 0 < x.1}), b (qShift c x) = b x`
(`Short/PartII-b/Defs.lean`, `qShift c x = (x.1, (x.2.1 + c, x.2.2))`).

Proof: the shift `qShift s` preserves Lebesgue measure on `Coord = ℝ × (ℝ × ℝ)` and the half
space `{s > 0}`, hence preserves the restricted measure `volume.restrict {x | 0 < x.1}`
(`MeasurePreserving.restrict_preimage`), so `QuasiMeasurePreserving.ae` transports
almost-everywhere identities on the half space along it. Two such shift-invariances add
(`ae_qShift_add`) and invert (`ae_qShift_neg`), which gives the integer multiples `k * c` by
`Int.induction_on`. The countable intersection over `k : ℤ` is `ae_all_iff`.
-/

open MeasureTheory Filter

namespace UnforcedLeray.Short.IIb

/-- The shift `qShift s` preserves Lebesgue measure on `Coord`. -/
theorem measurePreserving_qShift (s : ℝ) :
    MeasurePreserving (qShift s) (volume : Measure Coord) (volume : Measure Coord) := by
  have hA : MeasurePreserving (Prod.map (fun t : ℝ => t + s) (id : ℝ → ℝ))
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) :=
    (measurePreserving_add_right volume s).prod (MeasurePreserving.id volume)
  have hB : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.map (fun t : ℝ => t + s) (id : ℝ → ℝ)))
      (volume : Measure Coord) (volume : Measure Coord) :=
    (MeasurePreserving.id volume).prod hA
  exact hB

/-- Two consecutive shifts compose to one shift. -/
theorem qShift_qShift (s t : ℝ) (x : Coord) : qShift s (qShift t x) = qShift (s + t) x := by
  show (x.1, ((x.2.1 + t) + s, x.2.2)) = (x.1, (x.2.1 + (s + t), x.2.2))
  rw [add_assoc, add_comm t s]

/-- The zero shift is the identity. -/
theorem qShift_zero (x : Coord) : qShift 0 x = x := by
  simp [qShift]

/-- The half space `{s > 0}` is measurable. -/
theorem measurableSet_halfSpace : MeasurableSet {x : Coord | 0 < x.1} :=
  measurableSet_lt measurable_const measurable_fst

/-- The shift `qShift s` maps the half space `{s > 0}` onto itself. -/
theorem qShift_preimage_halfSpace (s : ℝ) :
    qShift s ⁻¹' {x : Coord | 0 < x.1} = {x : Coord | 0 < x.1} := by
  ext x
  simp [qShift]

/-- The shift `qShift s` preserves Lebesgue measure on the half space `{s > 0}`. -/
theorem measurePreserving_qShift_halfSpace (s : ℝ) :
    MeasurePreserving (qShift s) (volume.restrict {x : Coord | 0 < x.1})
      (volume.restrict {x : Coord | 0 < x.1}) := by
  have h := (measurePreserving_qShift s).restrict_preimage measurableSet_halfSpace
  rwa [qShift_preimage_halfSpace] at h

/-- An almost-everywhere property on the half space transports along a shift. -/
theorem ae_qShift_transport {t : ℝ} {P : Coord → Prop}
    (h : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), P x) :
    ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), P (qShift t x) :=
  (measurePreserving_qShift_halfSpace t).quasiMeasurePreserving.ae h

/-- Sum of two almost-everywhere shift-invariances on the half space. -/
theorem ae_qShift_add {s t : ℝ} {b : CProf}
    (hs : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift s x) = b x)
    (ht : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift t x) = b x) :
    ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift (s + t) x) = b x := by
  have h : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      b (qShift s (qShift t x)) = b (qShift t x) :=
    ae_qShift_transport (t := t) hs
  filter_upwards [h, ht] with x hx1 hx2
  rw [← qShift_qShift]
  exact Eq.trans hx1 hx2

/-- Inverse of an almost-everywhere shift-invariance on the half space. -/
theorem ae_qShift_neg {s : ℝ} {b : CProf}
    (hs : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift s x) = b x) :
    ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift (-s) x) = b x := by
  have h : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      b (qShift s (qShift (-s) x)) = b (qShift (-s) x) :=
    ae_qShift_transport (t := -s) hs
  filter_upwards [h] with x hx
  have hz : s + -s = 0 := by ring
  rw [qShift_qShift, hz, qShift_zero] at hx
  exact hx.symm

/-- Integer multiples of the period, almost everywhere on the half space. -/
theorem ae_qShift_int_mul {c : ℝ} {b : CProf} (hper : QPeriodic c b) (k : ℤ) :
    ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift ((k : ℝ) * c) x) = b x := by
  have hp : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift c x) = b x := hper
  refine Int.induction_on k ?_ ?_ ?_
  · filter_upwards with x
    simp [qShift]
  · intro n ih
    have e : ((((n : ℤ) + 1 : ℤ)) : ℝ) * c = ((n : ℤ) : ℝ) * c + c := by
      push_cast
      ring
    rw [e]
    exact ae_qShift_add ih hp
  · intro n ih
    have e : (((-(n : ℤ) - 1 : ℤ)) : ℝ) * c = ((-(n : ℤ) : ℤ) : ℝ) * c + -c := by
      push_cast
      ring
    rw [e]
    exact ae_qShift_add ih (ae_qShift_neg hp)

/-- The almost-everywhere `q`-periodicity of `b` on the half space `{s > 0}` holds simultaneously
for all integer shifts `k * c`. -/
theorem ae_qPeriodic_int_shift {c : ℝ} {b : UnforcedLeray.Short.IIb.CProf}
    (hper : UnforcedLeray.Short.IIb.QPeriodic c b) :
    ∀ᵐ x ∂(volume.restrict {x : UnforcedLeray.Short.IIb.Coord | 0 < x.1}), ∀ k : ℤ,
      b (x.1, (x.2.1 + k * c, x.2.2)) = b x := by
  refine ae_all_iff.2 (fun k => ?_)
  filter_upwards [ae_qShift_int_mul hper k] with x hx
  exact hx

end UnforcedLeray.Short.IIb
