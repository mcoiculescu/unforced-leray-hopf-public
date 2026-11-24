import UnforcedLeray.Units.B0289.Cutoff
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# B0289: periodic null sets and periodic measurable versions

Unit B0289 (tex lines 4771–4775). Two measure-theoretic facts about fields on the cylinder
`T_c × ℝ` represented by `c`-periodic lifts (decision D1 of the scoping plan):

* `ae_of_ae_cellMeasure`: a periodic property holding almost everywhere for the normalized cell
  measure `dq/c dη` holds almost everywhere on the plane (fundamental domain
  `Cyl.isAddFundamentalDomain_strip`);
* `periodic_version`: a jointly measurable `G` that agrees almost everywhere with periodic
  fields has a jointly measurable periodic version `(t, z) ↦ G t (wrap c z)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0289

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284

/-- Periodicity under every integer number of periods. -/
theorem IsQPeriodic.add_int_mul {β : Type*} {c : ℝ} {f : Plane → β} (hf : IsQPeriodic c f)
    (m : ℤ) (z : Plane) : f (z.1 + (m : ℝ) * c, z.2) = f z := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    calc f (z.1 + (((k : ℤ) + 1 : ℤ) : ℝ) * c, z.2)
        = f ((z.1 + ((k : ℤ) : ℝ) * c) + c, z.2) := by
          congr 2
          push_cast
          ring
      _ = f (z.1 + ((k : ℤ) : ℝ) * c, z.2) := hf (z.1 + ((k : ℤ) : ℝ) * c, z.2)
      _ = f z := ih
  | pred k ih =>
    calc f (z.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, z.2)
        = f ((z.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c) + c, z.2) :=
          (hf (z.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, z.2)).symm
      _ = f (z.1 + ((-(k : ℤ) : ℤ) : ℝ) * c, z.2) := by
          congr 2
          push_cast
          ring
      _ = f z := ih

/-- A periodic set that is null on one strip `[0,c) × ℝ` is null. -/
theorem measure_zero_of_periodic {c : ℝ} (hc : 0 < c) {S : Set Plane}
    (hS : IsQPeriodic c (· ∈ S)) (h0 : volume (S ∩ (Ico 0 c ×ˢ (univ : Set ℝ))) = 0) :
    volume S = 0 := by
  have hF := Cyl.isAddFundamentalDomain_strip hc 0
  rw [zero_add] at hF
  refine hF.measure_zero_of_invariant S ?_ h0
  rintro ⟨v, hv⟩
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
  ext z
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e : (-(⟨m • ((c, 0) : Plane), hv⟩ : AddSubgroup.zmultiples ((c, 0) : Plane)) +ᵥ z :
      Plane) = (z.1 + ((-m : ℤ) : ℝ) * c, z.2) := by
    rw [AddSubgroup.vadd_def, vadd_eq_add]
    ext <;> simp <;> ring
  rw [e]
  exact iff_of_eq (IsQPeriodic.add_int_mul hS (-m) z)

theorem volume_line_zero : volume ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- A periodic property that holds almost everywhere for `dq/c dη` holds almost everywhere on
the plane. -/
theorem ae_of_ae_cellMeasure {c : ℝ} (hc : 0 < c) {P : Plane → Prop} (hP : IsQPeriodic c P)
    (h : ∀ᵐ z ∂(cellMeasure c), P z) : ∀ᵐ z ∂(volume : Measure Plane), P z := by
  rw [ae_iff] at h ⊢
  set S : Set Plane := {z | ¬P z} with hSdef
  have hS : IsQPeriodic c (· ∈ S) := fun z => by
    simp only [hSdef, Set.mem_ofPred_eq]
    rw [hP z]
  have h1 : volume (S ∩ cell c) = 0 := by
    have h2 := h
    rw [cellMeasure, Measure.smul_apply, Measure.restrict_apply' (measurableSet_cell c),
      ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exfalso
      have : (c.toNNReal)⁻¹ ≠ 0 := inv_ne_zero (Real.toNNReal_pos.2 hc).ne'
      exact this (by exact_mod_cast h2)
    · exact h2
  refine measure_zero_of_periodic hc hS ?_
  refine measure_mono_null ?_ (measure_union_null h1 volume_line_zero)
  rintro z ⟨hzS, hz1, -⟩
  by_cases hz : z.1 = 0
  · right
    exact ⟨hz, trivial⟩
  · left
    exact ⟨hzS, ⟨lt_of_le_of_ne hz1.1 (Ne.symm hz), hz1.2.le⟩, trivial⟩

/-! ## The periodic version -/

/-- `z ↦ (q - ⌊q/c⌋ c, η)`: the representative of `z` in the strip `[0,c) × ℝ`. -/
def wrap (c : ℝ) (z : Plane) : Plane := (z.1 - (⌊z.1 / c⌋ : ℝ) * c, z.2)

theorem measurable_wrap (c : ℝ) : Measurable (wrap c) := by
  unfold wrap
  have h : Measurable fun z : Plane => ((⌊z.1 / c⌋ : ℤ) : ℝ) :=
    (Measurable.of_discrete (f := (Int.cast : ℤ → ℝ))).comp (measurable_fst.div_const c).floor
  exact (measurable_fst.sub (h.mul measurable_const)).prodMk measurable_snd

theorem wrap_eq (c : ℝ) (z : Plane) : wrap c z = (z.1 + ((-⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) := by
  simp only [wrap, Int.cast_neg]
  congr 1
  ring

theorem wrap_periodic {c : ℝ} (hc : 0 < c) : IsQPeriodic c (wrap c) := by
  intro z
  simp only [wrap]
  have : (z.1 + c) / c = z.1 / c + 1 := by field_simp
  rw [this, Int.floor_add_one]
  congr 1
  push_cast
  ring

theorem wrap_of_mem {c : ℝ} (hc : 0 < c) {z : Plane} (hz : z.1 ∈ Ico 0 c) : wrap c z = z := by
  have h0 : ⌊z.1 / c⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor
    · exact div_nonneg hz.1 hc.le
    · rw [div_lt_one hc]
      exact hz.2
  simp [wrap, h0]

/-- **Periodic version.** For jointly measurable `G`, `Ĝ t z = G t (wrap c z)` is jointly
measurable and periodic, and `Ĝ t = f` almost everywhere whenever `G t = f` almost everywhere
for a periodic `f`. -/
theorem periodic_version {c : ℝ} (hc : 0 < c) {G : ℝ → Plane → Plane}
    (hG : StronglyMeasurable (Function.uncurry G)) :
    StronglyMeasurable (Function.uncurry fun t z => G t (wrap c z)) ∧
      (∀ t, IsQPeriodic c fun z => G t (wrap c z)) ∧
      ∀ (t : ℝ) (f : Plane → Plane), IsQPeriodic c f → G t =ᵐ[volume] f →
        (fun z => G t (wrap c z)) =ᵐ[volume] f := by
  refine ⟨hG.comp_measurable (measurable_fst.prodMk ((measurable_wrap c).comp measurable_snd)),
    fun t z => by simp only; rw [wrap_periodic hc z], fun t f hf hGf => ?_⟩
  have hN : volume {z | G t z ≠ f z} = 0 := ae_iff.mp hGf
  rw [Filter.EventuallyEq, ae_iff]
  set S : Set Plane := {z | G t (wrap c z) ≠ f z} with hSdef
  have hfw : ∀ z, f (wrap c z) = f z := fun z => by
    rw [wrap_eq]
    exact IsQPeriodic.add_int_mul hf _ z
  have hS : IsQPeriodic c (· ∈ S) := fun z => by
    simp only [hSdef, Set.mem_ofPred_eq]
    rw [wrap_periodic hc z, hf z]
  refine measure_zero_of_periodic hc hS (measure_mono_null ?_ hN)
  rintro z ⟨hzS, hz1, -⟩
  have hw := wrap_of_mem hc hz1
  simp only [hSdef, Set.mem_ofPred_eq, hw] at hzS
  exact hzS

end UnforcedLeray.B0289
