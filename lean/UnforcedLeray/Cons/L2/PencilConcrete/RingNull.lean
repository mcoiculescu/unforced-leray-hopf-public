import UnforcedLeray.Cons.C07ReducedMatrix.Weak
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# C7 concrete pencil, helper: null sets of the ring chart

`paper/main.tex`, the similarity chart `s = R²/ϱ²`, `ξ = Rτ/2 - (R/2)log s`, `η = Ry₃/ϱ`
(`eq:m3-ring-lift`, lines 2073–2080) and the natural lift `𝒩_v` (`eq:m4-free-spaces`,
lines 7275–7283; `eq:stress-setup:3.1`, lines 8724–8732, B0550). The manuscript identifies
`H = L²(s^{-3/2}dς)` and `H_T = L²(s^{-1/2}dς)` with the periodic physical `L²` spaces through
the Jacobian `(R²/2)s^{-5/2}ds dη dφ` of the chart. What the pencil hypotheses of
`Cons/C07ReducedMatrix.lean` use is only the measure-class part of that identification:

* `volume_chart_preimage_null`: the chart pulls null sets of `{s > 0}` back to null sets of
  `ℝ × ℝ³` (so a.e. equal cylinder fields have a.e. equal lifts);
* `volume_null_of_chart_preimage`: conversely, a set of `{s > 0}` whose preimage off the axis
  is null is null (so a.e. equal lifts come from fields a.e. equal on `s > 0`);
* `ae_of_ae_periodSlab`: a `P`-periodic property holding a.e. on the period slab
  `(0, P] × ℝ³` holds a.e. on `ℝ × ℝ³`.

The proofs avoid the Jacobian: the chart and its inverse, completed by the coordinate `y₂`,
are differentiable maps of `ℝ⁴` (`chart4`, `chartInv4`), and differentiable maps send null sets
to null sets (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`); null sets are
transported between `ℝ × ℝ³` and `ℝ⁴` by a continuous linear equivalence (`null_image_iff`).
No measurability is assumed anywhere. Everything here is proved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Blueprint.C07.PencilConcrete

instance volume_isAddHaar_R2 : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

instance volume_isAddHaar_R3 : (volume : Measure (ℝ × ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

instance volume_isAddHaar_frame : (volume : Measure ((ℝ × ℝ × ℝ) × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

instance volume_isAddHaar_spaceTime : (volume : Measure SpaceTime).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- Null sets correspond under a continuous linear equivalence of finite-dimensional spaces
with additive Haar measures. -/
theorem null_image_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : E ≃L[ℝ] F) (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (A : Set E) : ν (L '' A) = 0 ↔ μ A = 0 := by
  have hmap : (μ.map L) (L '' A) = μ A := by
    have e : (μ.map L) = μ.map (L.toHomeomorph.toMeasurableEquiv) := rfl
    rw [e, MeasurableEquiv.map_apply]
    congr 1
    exact Set.preimage_image_eq A L.injective
  have h1 : μ.map L ≪ ν := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h2 : ν ≪ μ.map L := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  constructor
  · intro h
    rw [← hmap]
    exact h1 h
  · intro h
    exact h2 (hmap.trans h)

/-! ## The four-dimensional frame -/

/-- The frame `((τ, y₁, y₃), y₂)` of `ℝ × ℝ³`. -/
abbrev Frame := (ℝ × ℝ × ℝ) × ℝ

/-- `(τ, y) ↦ ((τ, y₁, y₃), y₂)` as a linear equivalence. -/
def frameLinear : SpaceTime ≃ₗ[ℝ] Frame where
  toFun z := ((z.1, z.2 0, z.2 2), z.2 1)
  invFun p := (p.1.1, WithLp.toLp 2 ![p.1.2.1, p.2, p.1.2.2])
  map_add' z w := by simp
  map_smul' c z := by simp
  left_inv z := by
    refine Prod.ext rfl ?_
    ext i
    fin_cases i <;> simp
  right_inv p := by simp

/-- `(τ, y) ↦ ((τ, y₁, y₃), y₂)` as a continuous linear equivalence. -/
def frameEquiv : SpaceTime ≃L[ℝ] Frame := frameLinear.toContinuousLinearEquiv

theorem frameEquiv_apply (z : SpaceTime) : frameEquiv z = ((z.1, z.2 0, z.2 2), z.2 1) := rfl

theorem frameEquiv_symm_apply (p : Frame) :
    frameEquiv.symm p = (p.1.1, WithLp.toLp 2 ![p.1.2.1, p.2, p.1.2.2]) := rfl

/-- Null sets of `ℝ × ℝ³` and of the frame correspond. -/
theorem volume_frame_image_null_iff (A : Set SpaceTime) :
    volume (frameEquiv '' A) = 0 ↔ volume A = 0 :=
  null_image_iff frameEquiv volume volume A

/-- The chart completed by `y₂`: `((τ, a, c), t) ↦ (ringChart R τ (a, t, c), t)`. -/
def chart4 (R : ℝ) (p : Frame) : Frame :=
  ((R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2),
    R * p.1.1 / 2 - (R / 2) * Real.log (R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2)),
    Real.sqrt (R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2)) * p.1.2.2), p.2)

theorem chart4_frame (R : ℝ) (z : SpaceTime) :
    chart4 R (frameEquiv z) = (ringChart R z.1 z.2, z.2 1) := rfl

/-- The inverse chart `((s, ξ, η), t) ↦ ((2ξ/R + log s, ε√(R²/s - t²), η/√s), t)`, on the
sheet `ε = ±1`. -/
def chartInv4 (R ε : ℝ) (p : Frame) : Frame :=
  ((2 * p.1.2.1 / R + Real.log p.1.1, ε * Real.sqrt (R ^ 2 / p.1.1 - p.2 ^ 2),
    p.1.2.2 / Real.sqrt p.1.1), p.2)

/-- The domain of the inverse chart. -/
def invDomain (R : ℝ) : Set Frame := {p | 0 < p.1.1 ∧ p.2 ^ 2 < R ^ 2 / p.1.1}

theorem chart4_differentiableAt {R : ℝ} (hR : R ≠ 0) {p : Frame} (hp : p.1.2.1 ≠ 0) :
    DifferentiableAt ℝ (chart4 R) p := by
  have h1 : p.1.2.1 ^ 2 + p.2 ^ 2 ≠ 0 := by positivity
  have h2 : R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2) ≠ 0 := by positivity
  have ha : DifferentiableAt ℝ (fun q : Frame => R ^ 2 / (q.1.2.1 ^ 2 + q.2 ^ 2)) p := by
    fun_prop (disch := exact h1)
  unfold chart4
  refine DifferentiableAt.prodMk (DifferentiableAt.prodMk ha
    (DifferentiableAt.prodMk ?_ ?_)) (by fun_prop)
  · exact (by fun_prop : DifferentiableAt ℝ (fun q : Frame => R * q.1.1 / 2) p).sub
      ((ha.log h2).const_mul _)
  · exact (ha.sqrt h2).mul (by fun_prop)

theorem chartInv4_differentiableAt {R : ℝ} (ε : ℝ) {p : Frame} (hp : p ∈ invDomain R) :
    DifferentiableAt ℝ (chartInv4 R ε) p := by
  obtain ⟨hs, ht⟩ := hp
  have hs0 : p.1.1 ≠ 0 := hs.ne'
  have hd : R ^ 2 / p.1.1 - p.2 ^ 2 ≠ 0 := (sub_pos.2 ht).ne'
  have hq : Real.sqrt p.1.1 ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hfst : DifferentiableAt ℝ (fun q : Frame => q.1.1) p := by fun_prop
  have hsq : DifferentiableAt ℝ (fun q : Frame => Real.sqrt q.1.1) p := hfst.sqrt hs0
  have hdiff : DifferentiableAt ℝ (fun q : Frame => R ^ 2 / q.1.1 - q.2 ^ 2) p := by
    fun_prop (disch := exact hs0)
  unfold chartInv4
  refine DifferentiableAt.prodMk (DifferentiableAt.prodMk ?_
    (DifferentiableAt.prodMk ?_ ?_)) (by fun_prop)
  · exact (by fun_prop : DifferentiableAt ℝ (fun q : Frame => 2 * q.1.2.1 / R) p).add
      (hfst.log hs0)
  · exact (hdiff.sqrt hd).const_mul _
  · fun_prop (disch := assumption)

/-- `chartInv4 ∘ chart4 = id` off the plane `a = 0`, on the sheet of the sign of `a`. -/
theorem chartInv4_chart4 {R : ℝ} (hR : R ≠ 0) {ε : ℝ} {p : Frame}
    (hε : ε * |p.1.2.1| = p.1.2.1) (hp : p.1.2.1 ≠ 0) : chartInv4 R ε (chart4 R p) = p := by
  have h1 : 0 < p.1.2.1 ^ 2 + p.2 ^ 2 := by positivity
  have hs : 0 < R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2) := by positivity
  have hsq : Real.sqrt (R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2)) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have e2 : R ^ 2 / (R ^ 2 / (p.1.2.1 ^ 2 + p.2 ^ 2)) - p.2 ^ 2 = p.1.2.1 ^ 2 := by
    field_simp
    ring
  obtain ⟨⟨τ, a, c⟩, t⟩ := p
  simp only [chart4, chartInv4] at *
  refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) rfl
  · simp only
    field_simp
    ring
  · simp only
    rw [e2, Real.sqrt_sq_eq_abs, hε]
  · simp only
    field_simp

/-- `chart4 ∘ chartInv4 = id` on the domain of the inverse chart, on either sheet. -/
theorem chart4_chartInv4 {R : ℝ} (hR : R ≠ 0) {ε : ℝ} (hε : ε ^ 2 = 1) {p : Frame}
    (hp : p ∈ invDomain R) : chart4 R (chartInv4 R ε p) = p := by
  obtain ⟨hs, ht⟩ := hp
  obtain ⟨⟨s, ξ, η⟩, t⟩ := p
  simp only at hs ht
  have hd : 0 ≤ R ^ 2 / s - t ^ 2 := (sub_pos.2 ht).le
  have hsum : (ε * Real.sqrt (R ^ 2 / s - t ^ 2)) ^ 2 + t ^ 2 = R ^ 2 / s := by
    rw [mul_pow, hε, one_mul, Real.sq_sqrt hd]
    ring
  have hRs : R ^ 2 / (R ^ 2 / s) = s := by
    field_simp
  have hq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  simp only [chart4, chartInv4, hsum, hRs]
  refine Prod.ext (Prod.ext rfl (Prod.ext ?_ ?_)) rfl
  · simp only
    field_simp
    ring
  · simp only
    field_simp

/-! ## Null sets through the chart -/

theorem volume_prod_univ_null {N : Set (ℝ × ℝ × ℝ)} (hN : volume N = 0) :
    volume (N ×ˢ (univ : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hN, zero_mul]

theorem volume_plane_null : volume {p : Frame | p.1.2.1 = 0} = 0 := by
  have e : {p : Frame | p.1.2.1 = 0} =
      ((univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (univ : Set ℝ))) ×ˢ (univ : Set ℝ) := by
    ext p
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- **The chart pulls null sets of `{s > 0}` back to null sets of `ℝ × ℝ³`.** -/
theorem volume_chart_preimage_null {R : ℝ} (hR : R ≠ 0) {N : Set (ℝ × ℝ × ℝ)}
    (hN : volume N = 0) (hpos : N ⊆ {x | 0 < x.1}) :
    volume {z : SpaceTime | ringChart R z.1 z.2 ∈ N} = 0 := by
  rw [← volume_frame_image_null_iff]
  set D := invDomain R ∩ N ×ˢ (univ : Set ℝ) with hD
  have hDnull : volume D = 0 :=
    measure_mono_null inter_subset_right (volume_prod_univ_null hN)
  have himg : ∀ ε : ℝ, volume (chartInv4 R ε '' D) = 0 := fun ε =>
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun p hp => (chartInv4_differentiableAt ε hp.1).differentiableWithinAt) hDnull
  refine measure_mono_null ?_ (measure_union_null (measure_union_null (himg 1) (himg (-1)))
    volume_plane_null)
  rintro _ ⟨z, hz, rfl⟩
  by_cases ha : z.2 0 = 0
  · exact Or.inr ha
  left
  have hsum : 0 < z.2 0 ^ 2 + z.2 1 ^ 2 := by positivity
  have hq : chart4 R (frameEquiv z) ∈ D := by
    rw [chart4_frame]
    refine ⟨⟨hpos hz, ?_⟩, hz, mem_univ _⟩
    simp only [ringChart]
    rw [div_div_cancel₀ (by positivity)]
    nlinarith [sq_pos_of_ne_zero ha]
  rcases lt_or_gt_of_ne ha with hneg | hpos'
  · right
    refine ⟨_, hq, chartInv4_chart4 hR ?_ ha⟩
    simp only [frameEquiv_apply]
    rw [abs_of_neg hneg]
    ring
  · left
    refine ⟨_, hq, chartInv4_chart4 hR ?_ ha⟩
    simp only [frameEquiv_apply]
    rw [abs_of_pos hpos']
    ring

/-- **A set of `{s > 0}` with null preimage off the axis is null.** -/
theorem volume_null_of_chart_preimage {R : ℝ} (hR : 0 < R) {N : Set (ℝ × ℝ × ℝ)}
    (h : volume {z : SpaceTime | z.2 0 ^ 2 + z.2 1 ^ 2 ≠ 0 ∧ ringChart R z.1 z.2 ∈ N} = 0) :
    volume (N ∩ {x | 0 < x.1}) = 0 := by
  set A := {z : SpaceTime | z.2 0 ^ 2 + z.2 1 ^ 2 ≠ 0 ∧ ringChart R z.1 z.2 ∈ N} with hA
  set B := frameEquiv '' A ∩ {p : Frame | 0 < p.1.2.1} with hB
  have hBnull : volume B = 0 :=
    measure_mono_null inter_subset_left ((volume_frame_image_null_iff A).2 h)
  have hCnull : volume (chart4 R '' B) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun p hp => (chart4_differentiableAt hR.ne' hp.2.ne').differentiableWithinAt) hBnull
  have hk : ∀ k : ℕ, volume (N ∩ {x | 0 < x.1 ∧ x.1 ≤ k + 1}) = 0 := by
    intro k
    set δ := R / Real.sqrt (k + 1) with hδ
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hδpos : 0 < δ := div_pos hR (Real.sqrt_pos.2 hk1)
    have hsub : (N ∩ {x | 0 < x.1 ∧ x.1 ≤ k + 1}) ×ˢ Ioo (0 : ℝ) δ ⊆ chart4 R '' B := by
      rintro ⟨x, t⟩ ⟨⟨hxN, hx0, hxk⟩, ht0, htδ⟩
      have ht2 : t ^ 2 < R ^ 2 / x.1 := by
        have h1 : t ^ 2 < δ ^ 2 := by nlinarith
        have h2 : δ ^ 2 = R ^ 2 / (k + 1) := by
          rw [hδ, div_pow, Real.sq_sqrt hk1.le]
        have h3 : R ^ 2 / (k + 1) ≤ R ^ 2 / x.1 :=
          div_le_div_of_nonneg_left (sq_nonneg R) hx0 hxk
        linarith
      have hdom : ((x, t) : Frame) ∈ invDomain R := ⟨hx0, ht2⟩
      refine ⟨chartInv4 R 1 (x, t), ⟨⟨frameEquiv.symm (chartInv4 R 1 (x, t)), ?_, by simp⟩, ?_⟩,
        chart4_chartInv4 hR.ne' (by norm_num) hdom⟩
      · have hpos : 0 < (chartInv4 R 1 (x, t)).1.2.1 := by
          simp only [chartInv4, one_mul]
          exact Real.sqrt_pos.2 (sub_pos.2 ht2)
        have hc := chart4_chartInv4 (ε := 1) hR.ne' (by norm_num) hdom
        rw [← frameEquiv.apply_symm_apply (chartInv4 R 1 (x, t)), chart4_frame] at hc
        refine ⟨?_, ?_⟩
        · rw [frameEquiv_symm_apply]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          positivity
        · have := congrArg Prod.fst hc
          simp only at this
          rw [this]
          exact hxN
      · show 0 < (chartInv4 R 1 (x, t)).1.2.1
        simp only [chartInv4, one_mul]
        exact Real.sqrt_pos.2 (sub_pos.2 ht2)
    have h0 := measure_mono_null hsub hCnull
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, sub_zero] at h0
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact h0
    · exact absurd h0 (ENNReal.ofReal_pos.2 hδpos).ne'
  refine measure_mono_null ?_ (measure_iUnion_null hk)
  rintro x ⟨hxN, hx0⟩
  obtain ⟨k, hk⟩ := exists_nat_ge x.1
  exact mem_iUnion.2 ⟨k, hxN, hx0, by linarith⟩

/-! ## From the period slab to the whole spacetime -/

/-- A property invariant under `τ ↦ τ + P` that holds a.e. on the period slab holds a.e. on
`ℝ × ℝ³` (`P > 0`). -/
theorem ae_of_ae_periodSlab {P : ℝ} (hP : 0 < P) {p : SpaceTime → Prop}
    (hp : ∀ z : SpaceTime, p (z.1 + P, z.2) ↔ p z)
    (h : ∀ᵐ z ∂(volume.restrict (periodSlab P)), p z) : ∀ᵐ z : SpaceTime, p z := by
  have hS : MeasurableSet (periodSlab P) := measurableSet_Ioc.prod MeasurableSet.univ
  have hbad : volume ({z | ¬ p z} ∩ periodSlab P) = 0 := by
    have := ae_iff.1 h
    rwa [Measure.restrict_apply' hS] at this
  have hint : ∀ (z : SpaceTime) (n : ℤ), p ((n : ℝ) * P + z.1, z.2) ↔ p z := by
    intro z n
    have hper : Function.Periodic (fun τ : ℝ => p (τ, z.2)) P := fun τ =>
      propext (hp (τ, z.2))
    have := hper.int_mul n z.1
    rw [add_comm]
    exact Iff.of_eq this
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ n : ℤ,
    (fun w : SpaceTime => (((n : ℝ) * P, 0) : SpaceTime) + w) ⁻¹' ({z | ¬ p z} ∩ periodSlab P))
    ?_ (measure_iUnion_null fun n => by rw [measure_preimage_add]; exact hbad)
  intro z hz
  refine mem_iUnion.2 ⟨-toIocDiv hP 0 z.1, ?_, ?_⟩
  · show ¬ p ((((-toIocDiv hP 0 z.1 : ℤ) : ℝ) * P, 0) + z)
    have e : ((((-toIocDiv hP 0 z.1 : ℤ) : ℝ) * P, (0 : Space)) + z) =
        (((-toIocDiv hP 0 z.1 : ℤ) : ℝ) * P + z.1, z.2) := by
      ext <;> simp
    rw [e, hint]
    exact hz
  · have hmem := toIocMod_mem_Ioc hP 0 z.1
    have e2 := self_sub_toIocDiv_zsmul hP 0 z.1
    refine ⟨?_, mem_univ _⟩
    show ((((-toIocDiv hP 0 z.1 : ℤ) : ℝ) * P, (0 : Space)) + z).1 ∈ Ioc 0 P
    rw [zero_add] at hmem
    simp only [Prod.fst_add, Int.cast_neg, neg_mul]
    rw [zsmul_eq_mul] at e2
    rw [show -(↑(toIocDiv hP 0 z.1) * P) + z.1 = z.1 - ↑(toIocDiv hP 0 z.1) * P by ring, e2]
    exact hmem

end UnforcedLeray.Blueprint.C07.PencilConcrete
