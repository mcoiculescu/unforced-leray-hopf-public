import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Lib.AxisymmetricB.BridgeRange

/-!
# Part II-b, task `PartII-b:P1/1/4`: additivity and real homogeneity of the joint representative

Target: `blRepLin_proof : UnforcedLeray.Short.IIb.BLRepLin`, i.e.
`rep (f + h) =ᵃᵉ rep f + rep h` and `rep (a • f) =ᵃᵉ a • rep f` on `ℝ × Space`, for `f, h` in the
body space `p.Y` (coerced into `Yq p.period q0E`).

Proof outline.
* Circle level: `rep w τ y = jointRep w (τ mod P, y)`, and each spatial slice of `jointRep w`
  represents the `L^q` class `w θ`. Lp addition and scalar multiplication on the outer and inner
  `Lp` levels give the identities for haar-a.e. phase `θ` and a.e. `y`.
* Line level: `Axi.ae_Ioc_of_ae_circle` moves the phase a.e. statement to `t ∈ (0, P]`.
* Periodic extension: the bad set `{x | G x ≠ 0}` is `P`-periodic in the phase (`rep_add_period`),
  so it is covered by translates of its restriction to `(0, P] × Space`; each translate is
  Lebesgue-null (translation invariance of the product measure), hence the bad set is null.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.BLRepLinAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Shifts of `rep` by integer multiples of the period. -/
theorem rep_int_shift (w : Yq P q) (k : ℤ) (τ : ℝ) (y : Space) :
    rep w (τ + (k : ℝ) * P) y = rep w τ y := by
  have hp : Function.Periodic (fun s : ℝ => rep w s y) P := fun s => rep_add_period w s y
  exact hp.int_mul k τ

/-- Phase-slice identity for sums, on the circle. -/
theorem ae_circle_add (u v : Yq P q) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P), ∀ᵐ y ∂(volume : Measure Space),
      UnforcedLeray.B0449.jointRep (u + v) (θ, y)
        = UnforcedLeray.B0449.jointRep u (θ, y) + UnforcedLeray.B0449.jointRep v (θ, y) := by
  filter_upwards [Lp.coeFn_add u v] with θ hθ
  have hθ' : (u + v) θ = u θ + v θ := hθ
  have h1 := UnforcedLeray.B0449.jointRep_slice (u + v) θ
  have h2 := UnforcedLeray.B0449.jointRep_slice u θ
  have h3 := UnforcedLeray.B0449.jointRep_slice v θ
  have h4 := Lp.coeFn_add (u θ) (v θ)
  filter_upwards [h1, h2, h3, h4] with y e1 e2 e3 e4
  simp only [e1, e2, e3, hθ', e4, Pi.add_apply]

/-- Phase-slice identity for real scalars, on the circle. -/
theorem ae_circle_smul (a : ℝ) (u : Yq P q) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle (T := P), ∀ᵐ y ∂(volume : Measure Space),
      UnforcedLeray.B0449.jointRep (a • u) (θ, y)
        = a • UnforcedLeray.B0449.jointRep u (θ, y) := by
  filter_upwards [Lp.coeFn_smul a u] with θ hθ
  have hθ' : (a • u) θ = a • u θ := hθ
  have h1 := UnforcedLeray.B0449.jointRep_slice (a • u) θ
  have h2 := UnforcedLeray.B0449.jointRep_slice u θ
  have h4 := Lp.coeFn_smul a (u θ)
  filter_upwards [h1, h2, h4] with y e1 e2 e4
  simp only [e1, e2, hθ', e4, Pi.smul_apply]

/-- A `P`-periodic-in-phase function which vanishes a.e. on `(0, P] × Space` vanishes a.e. on the
whole product. -/
theorem ae_zero_of_periodic {G : ℝ × Space → CVec3} (hP : 0 < P) (hG : Measurable G)
    (hper : ∀ (k : ℤ) (x : ℝ × Space), G (x.1 + (k : ℝ) * P, x.2) = G x)
    (h : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ᵐ y ∂(volume : Measure Space), G (t, y) = 0) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), G x = 0 := by
  have hAm : MeasurableSet {x : ℝ × Space | ¬ G x = 0} :=
    (hG (measurableSet_singleton (0 : CVec3))).compl
  have hS0 : MeasurableSet (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  -- the bad set on the fundamental slab is null
  have hA0 : volume ({x : ℝ × Space | ¬ G x = 0} ∩ (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null (hAm.inter hS0)]
    have h' := (ae_restrict_iff' measurableSet_Ioc).1 h
    filter_upwards [h'] with t ht
    by_cases htI : t ∈ Ioc (0 : ℝ) P
    · have h0 := ae_iff.1 (ht htI)
      simp only [Pi.zero_apply]
      refine measure_mono_null ?_ h0
      intro y hy
      exact hy.1
    · simp only [Pi.zero_apply]
      have hempty : Prod.mk t ⁻¹' ({x : ℝ × Space | ¬ G x = 0} ∩
          (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) = ∅ := by
        ext y
        simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true, mem_empty_iff_false,
          iff_false, not_and]
        intro _ hmem
        exact absurd hmem htI
      rw [hempty, measure_empty]
  -- every real phase reduces to `(0, P]` by periodicity
  have hex : ∀ t : ℝ, ∃ k : ℤ, t + (k : ℝ) * P ∈ Ioc (0 : ℝ) P := by
    intro t
    refine ⟨1 - ⌈t / P⌉, ?_, ?_⟩
    · have h2 : (⌈t / P⌉ : ℝ) < t / P + 1 := Int.ceil_lt_add_one _
      have h2' : (⌈t / P⌉ : ℝ) * P < t + P := by
        have := mul_lt_mul_of_pos_right h2 hP
        rwa [add_mul, div_mul_cancel₀ t hP.ne', one_mul] at this
      push_cast
      nlinarith
    · have h1 : t / P ≤ (⌈t / P⌉ : ℝ) := Int.le_ceil _
      have h1' : t ≤ (⌈t / P⌉ : ℝ) * P := by
        have := mul_le_mul_of_nonneg_right h1 hP.le
        rwa [div_mul_cancel₀ t hP.ne'] at this
      push_cast
      nlinarith
  have hcover : {x : ℝ × Space | ¬ G x = 0} ⊆ ⋃ k : ℤ,
      (fun x : ℝ × Space => (x.1 + (k : ℝ) * P, x.2)) ⁻¹'
        ({x : ℝ × Space | ¬ G x = 0} ∩ (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) := by
    intro x hx
    obtain ⟨k, hk⟩ := hex x.1
    simp only [mem_iUnion, mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
    refine ⟨k, ?_, hk⟩
    show ¬ G (x.1 + (k : ℝ) * P, x.2) = 0
    rw [hper k x]
    exact hx
  have hT : ∀ k : ℤ, MeasurePreserving (fun x : ℝ × Space => (x.1 + (k : ℝ) * P, x.2))
      volume volume := by
    intro k
    rw [Measure.volume_eq_prod ℝ Space]
    exact (measurePreserving_add_right volume ((k : ℝ) * P)).prod (MeasurePreserving.id volume)
  have hU : volume (⋃ k : ℤ, (fun x : ℝ × Space => (x.1 + (k : ℝ) * P, x.2)) ⁻¹'
      ({x : ℝ × Space | ¬ G x = 0} ∩ (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)))) = 0 := by
    refine measure_iUnion_null fun k => ?_
    rw [(hT k).measure_preimage (hAm.inter hS0).nullMeasurableSet, hA0]
  have hfull : volume {x : ℝ × Space | ¬ G x = 0} = 0 := measure_mono_null hcover hU
  exact ae_iff.2 hfull

/-- Additivity of the joint representative almost everywhere on `ℝ × Space`. -/
theorem rep_add_ae (u v : Yq P q) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), rep (u + v) x.1 x.2 = rep u x.1 x.2 + rep v x.1 x.2 := by
  have hcirc := ae_circle_add u v
  have hline : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∀ᵐ y ∂(volume : Measure Space), rep (u + v) t y - (rep u t y + rep v t y) = 0 := by
    have h := Axi.ae_Ioc_of_ae_circle (P := P) (p := fun θ : AddCircle P =>
      ∀ᵐ y ∂(volume : Measure Space), UnforcedLeray.B0449.jointRep (u + v) (θ, y)
        = UnforcedLeray.B0449.jointRep u (θ, y) + UnforcedLeray.B0449.jointRep v (θ, y)) hcirc
    filter_upwards [h] with t ht
    filter_upwards [ht] with y hy
    show UnforcedLeray.B0449.jointRep (u + v) ((t : AddCircle P), y)
        - (UnforcedLeray.B0449.jointRep u ((t : AddCircle P), y)
          + UnforcedLeray.B0449.jointRep v ((t : AddCircle P), y)) = 0
    rw [hy, sub_self]
  have hGm : Measurable (fun x : ℝ × Space =>
      rep (u + v) x.1 x.2 - (rep u x.1 x.2 + rep v x.1 x.2)) :=
    (stronglyMeasurable_rep (u + v)).measurable.sub
      ((stronglyMeasurable_rep u).measurable.add (stronglyMeasurable_rep v).measurable)
  have hper : ∀ (k : ℤ) (x : ℝ × Space),
      (fun x : ℝ × Space => rep (u + v) x.1 x.2 - (rep u x.1 x.2 + rep v x.1 x.2))
          (x.1 + (k : ℝ) * P, x.2)
        = (fun x : ℝ × Space => rep (u + v) x.1 x.2 - (rep u x.1 x.2 + rep v x.1 x.2)) x := by
    intro k x
    simp only [rep_int_shift]
  have hG := ae_zero_of_periodic (G := fun x : ℝ × Space =>
      rep (u + v) x.1 x.2 - (rep u x.1 x.2 + rep v x.1 x.2))
    (Fact.out : 0 < P) hGm hper hline
  filter_upwards [hG] with x hx
  exact sub_eq_zero.1 hx

/-- Real homogeneity of the joint representative almost everywhere on `ℝ × Space`. -/
theorem rep_smul_ae (a : ℝ) (u : Yq P q) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), rep (a • u) x.1 x.2 = a • rep u x.1 x.2 := by
  have hcirc := ae_circle_smul a u
  have hline : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∀ᵐ y ∂(volume : Measure Space), rep (a • u) t y - a • rep u t y = 0 := by
    have h := Axi.ae_Ioc_of_ae_circle (P := P) (p := fun θ : AddCircle P =>
      ∀ᵐ y ∂(volume : Measure Space), UnforcedLeray.B0449.jointRep (a • u) (θ, y)
        = a • UnforcedLeray.B0449.jointRep u (θ, y)) hcirc
    filter_upwards [h] with t ht
    filter_upwards [ht] with y hy
    show UnforcedLeray.B0449.jointRep (a • u) ((t : AddCircle P), y)
        - a • UnforcedLeray.B0449.jointRep u ((t : AddCircle P), y) = 0
    rw [hy, sub_self]
  have hGm : Measurable (fun x : ℝ × Space => rep (a • u) x.1 x.2 - a • rep u x.1 x.2) :=
    (stronglyMeasurable_rep (a • u)).measurable.sub
      ((stronglyMeasurable_rep u).measurable.const_smul a)
  have hper : ∀ (k : ℤ) (x : ℝ × Space),
      (fun x : ℝ × Space => rep (a • u) x.1 x.2 - a • rep u x.1 x.2) (x.1 + (k : ℝ) * P, x.2)
        = (fun x : ℝ × Space => rep (a • u) x.1 x.2 - a • rep u x.1 x.2) x := by
    intro k x
    simp only [rep_int_shift]
  have hG := ae_zero_of_periodic (G := fun x : ℝ × Space =>
      rep (a • u) x.1 x.2 - a • rep u x.1 x.2)
    (Fact.out : 0 < P) hGm hper hline
  filter_upwards [hG] with x hx
  exact sub_eq_zero.1 hx

end UnforcedLeray.Short.IIb.BLRepLinAux

open UnforcedLeray.Short.IIb.BLRepLinAux UnforcedLeray.PhaseSpace UnforcedLeray.B0412 in
/-- **Target** `BLRepLin` (`P1/1/4`). -/
theorem blRepLin_proof : UnforcedLeray.Short.IIb.BLRepLin := by
  intro p f h
  constructor
  · have e : ((f + h : p.Y) : Yq p.period q0E) = (f : Yq p.period q0E) + (h : Yq p.period q0E) :=
      rfl
    rw [e]
    exact rep_add_ae _ _
  · intro a
    have e : ((a • f : p.Y) : Yq p.period q0E) = a • (f : Yq p.period q0E) := rfl
    rw [e]
    exact rep_smul_ae _ _
