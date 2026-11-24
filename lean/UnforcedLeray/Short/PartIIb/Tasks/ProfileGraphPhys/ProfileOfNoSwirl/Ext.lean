import UnforcedLeray.Lib.AxisymmetricB.Unitary
import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# From the phase measure to Lebesgue measure on `ℝ × ℝ³` for periodic fields

A `P`-periodic field which agrees a.e. on one period `(0, P]` (for the phase measure) with an
a.e.-`P`-periodic field agrees with it volume-a.e. on `ℝ × ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- Translation in the time variable is measure preserving on `ℝ × ℝ³`. -/
theorem measurePreserving_timeShift (a : ℝ) :
    MeasurePreserving (fun x : ℝ × Space => (x.1 + a, x.2)) volume volume :=
  (measurePreserving_add_right (volume : Measure ℝ) a).prod (MeasurePreserving.id volume)

/-- A phase-measure a.e. statement gives an a.e. statement on the slab `τ ∈ (0, P]`. -/
theorem ae_slab_of_phase {P : ℝ} {Q : ℝ × Space → Prop} (h : ∀ᵐ x ∂phaseμ P, Q x) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), x.1 ∈ Ioc (0 : ℝ) P → Q x := by
  have hS : MeasurableSet (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  unfold phaseμ at h
  rw [Measure.prod_smul_left] at h
  have h2 := (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)).1 h
  have e2 : ((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space) =
      ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc 0 P ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e2] at h2
  filter_upwards [(ae_restrict_iff' hS).1 h2] with x hx hx1
  exact hx ⟨hx1, mem_univ _⟩

/-- Integer time shifts of an a.e.-`P`-periodic field are a.e. invariant. -/
theorem ae_int_shift {P : ℝ} {g : ℝ × Space → UnforcedLeray.PhaseSpace.CVec3}
    (hg : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), g (x.1 + P, x.2) = g x) (k : ℤ) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), g (x.1 + (k : ℝ) * P, x.2) = g x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    filter_upwards [(measurePreserving_timeShift ((i : ℝ) * P)).quasiMeasurePreserving.ae hg,
      ih] with x h1 h2
    have e : x.1 + ((i : ℝ) + 1) * P = x.1 + (i : ℝ) * P + P := by ring
    rw [Int.cast_natCast] at h2
    push_cast
    rw [e, h1, h2]
  | pred i ih =>
    filter_upwards [(measurePreserving_timeShift (((-(i : ℤ) - 1 : ℤ) : ℝ) * P)).quasiMeasurePreserving.ae hg,
      ih] with x h1 h2
    have e : x.1 + (((-(i : ℤ) - 1 : ℤ)) : ℝ) * P + P = x.1 + ((-(i : ℤ) : ℤ) : ℝ) * P := by
      push_cast; ring
    rw [e, h2] at h1
    push_cast at h1 ⊢
    rw [← h1]

/-- An a.e.-`P`-periodic field equal a.e. on the phase measure to an everywhere-`P`-periodic field
is equal volume-a.e. on `ℝ × ℝ³`. -/
theorem ae_volume_of_periodic {P : ℝ} (hP : 0 < P) {f g : ℝ × Space → UnforcedLeray.PhaseSpace.CVec3}
    (hf : ∀ τ y, f (τ + P, y) = f (τ, y))
    (hg : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), g (x.1 + P, x.2) = g x)
    (h : ∀ᵐ x ∂phaseμ P, f x = g x) : f =ᵐ[volume] g := by
  have h1 := ae_slab_of_phase h
  have hfk : ∀ (k : ℤ) (τ : ℝ) (y : Space), f (τ + (k : ℝ) * P, y) = f (τ, y) := by
    intro k τ y
    have hper : Function.Periodic (fun t : ℝ => f (t, y)) P := fun t => hf t y
    exact hper.int_mul k τ
  have hk : ∀ k : ℤ, ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      x.1 ∈ Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P) → f x = g x := by
    intro k
    filter_upwards [(measurePreserving_timeShift (((-k : ℤ) : ℝ) * P)).quasiMeasurePreserving.ae h1,
      ae_int_shift hg (-k)] with x h2 h3 hx
    have hmem : x.1 + (((-k : ℤ) : ℝ) * P) ∈ Ioc (0 : ℝ) P := by
      obtain ⟨ha, hb⟩ := hx
      push_cast
      constructor <;> nlinarith
    have h4 := h2 hmem
    have e := hfk (-k) x.1 x.2
    simp only [Int.cast_neg] at e h3 h4
    rw [← e, h4, h3]
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ k : ℤ,
      x.1 ∈ Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P) → f x = g x := ae_all_iff.2 hk
  filter_upwards [hall] with x hx
  have hceil1 : x.1 / P ≤ (⌈x.1 / P⌉ : ℝ) := Int.le_ceil _
  have hceil2 : (⌈x.1 / P⌉ : ℝ) < x.1 / P + 1 := Int.ceil_lt_add_one _
  have e1 : x.1 / P * P = x.1 := div_mul_cancel₀ _ hP.ne'
  have hmem : x.1 ∈ Ioc ((((⌈x.1 / P⌉ - 1 : ℤ)) : ℝ) * P)
      (((((⌈x.1 / P⌉ - 1 : ℤ)) : ℝ) + 1) * P) := by
    push_cast
    constructor <;> nlinarith
  exact hx _ hmem

end UnforcedLeray.Axi
