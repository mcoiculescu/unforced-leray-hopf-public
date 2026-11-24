import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Part II-b, task `PartII-b:T12/5`: the flat Duhamel integral is `c`-periodic in `q`

Source of record: `the November 2 reference manuscript`, SP 1924 (the heat flow
commutes with the period shift in `(q, η)`). Target: `DuhamelPeriodic`
(`Short/PartII-b/Sub/T12.lean`, leaf `PartII-b:T12/5`).

Proof. `QPeriodic c G` is `∀ᵐ x, 0 < x.1 → G (qShift c x) = G x` on `Coord = ℝ × (ℝ × ℝ)` (the
a.e. identity on the half space `s > 0`). Splitting the measure as `dt ⊗ dy`
(`Measure.ae_ae_of_ae_prod`) gives, for almost every time `t > 0`, the planar
periodicity `∀ᵐ y, G (t, (y.1 + c, y.2)) = G (t, y)`. For such `t`, the heat convolution
`flatHeat θ (G t)` is `c`-periodic at every planar point: the substitution `w ↦ z - w` preserves
Lebesgue measure on `ℝ × ℝ` and transports the almost-everywhere identity. Hence the time
integrands of `flatDuhamel` agree almost everywhere (shifted and unshifted), and `integral_congr_ae`
on `Ioo 0 s` (only times `t > 0` enter) closes the identity at every `x`. No case split on the
sign of `s` is needed: for `s ≤ 0` both sides are integrals over the empty set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace UnforcedLeray.Short.IIb

/-- Planar periodicity of the heat convolution: if `f : ℝ × ℝ → CMerid` is `c`-periodic in its
first planar variable almost everywhere, then `flatHeat θ f` is `c`-periodic at every point. -/
theorem flatHeat_qShift_of_ae {c θ : ℝ} {f : ℝ × ℝ → CMerid}
    (hf : ∀ᵐ y : ℝ × ℝ, f (y.1 + c, y.2) = f y) (z : ℝ × ℝ) :
    flatHeat θ f (z.1 + c, z.2) = flatHeat θ f z := by
  unfold flatHeat
  apply integral_congr_ae
  have hψ : MeasurePreserving (fun w : ℝ × ℝ => z - w) volume volume :=
    Measure.measurePreserving_sub_left volume z
  have hae : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), f ((z - w).1 + c, (z - w).2) = f (z - w) :=
    hψ.quasiMeasurePreserving.ae hf
  filter_upwards [hae] with w hw
  have hz : (z.1 + c, z.2) - w = ((z - w).1 + c, (z - w).2) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hz, hw]

/-- **Leaf `PartII-b:T12/5`**: the causal Duhamel integral `flatDuhamel ν μ G` of a `c`-periodic
profile `G` is `c`-periodic in `q`, almost everywhere (in fact at every point). -/
theorem duhamelPeriodic : DuhamelPeriodic := by
  unfold DuhamelPeriodic
  intro ν μ c G _hc hG
  -- The volume on `Coord = ℝ × (ℝ × ℝ)` is the product of the volumes on the two factors.
  have hvol : (volume : Measure Coord) =
      (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  -- `QPeriodic` is the a.e. identity on the half space `s > 0` (SP 1900-1903).
  have hG' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      0 < x.1 → G (qShift c x) = G x := by
    rw [← hvol]
    exact QPerHalf.ae_imp hG
  -- For a.e. time `t > 0`, the slice `G (t, ·)` is `c`-periodic in the planar variable.
  have hslice : ∀ᵐ t : ℝ, 0 < t → ∀ᵐ y : ℝ × ℝ, G (t, (y.1 + c, y.2)) = G (t, y) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hG'] with t ht htpos
    filter_upwards [ht] with y hy
    exact hy htpos
  unfold QPeriodic
  refine ae_of_all _ (fun x => ?_)
  simp only [flatDuhamel, qShift]
  apply integral_congr_ae
  -- the Duhamel integral only sees the times `t ∈ (0, s)`
  filter_upwards [ae_restrict_of_ae hslice, ae_restrict_mem measurableSet_Ioo] with t ht htm
  rw [flatHeat_qShift_of_ae (c := c) (θ := ν * (x.1 - t)) (f := fun z => G (t, z)) (ht htm.1)
    x.2]

end UnforcedLeray.Short.IIb

end
