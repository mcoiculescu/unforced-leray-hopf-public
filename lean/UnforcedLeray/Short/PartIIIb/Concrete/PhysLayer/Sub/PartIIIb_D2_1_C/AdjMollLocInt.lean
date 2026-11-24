import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# Leaf `MollLocInt`: `Φ` in the adjoint graph domain is locally integrable

Source: `the November 2 reference manuscript` lines 1351-1362 (`Φ ∈ Y_2`, so
`Φ` is a.e. `P`-periodic with finite `L²` norm over one cell `(0,P] × ℝ³`) and 1556-1583.

Proof route: `Φ` is `L²` on every cell `(kP, (k+1)P] × ℝ³` with the same norm as the base cell
(a.e. periodicity and translation invariance of `volume`). A bounded set is covered by finitely
many cells, and on a set `B` of finite measure `‖Φ‖ₑ ≤ 1 + ‖Φ‖ₑ²` gives
`∫_B ‖Φ‖ₑ ≤ vol B + ∫_B ‖Φ‖ₑ² < ⊤`. The `y`-compact support hypothesis of `MollLocInt` is not
needed for this leaf.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The base phase cell `(0, P] × ℝ³`. -/
def cellBase (P : ℝ) : Set (ℝ × Space) := Ioc (0 : ℝ) P ×ˢ (univ : Set Space)

/-- The `k`-th phase cell `(kP, (k+1)P] × ℝ³`, as a translate of the base cell. -/
def cellK (P : ℝ) (k : ℤ) : Set (ℝ × Space) :=
  (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space))) ⁻¹' cellBase P

theorem measurableSet_cellBase (P : ℝ) : MeasurableSet (cellBase P) :=
  measurableSet_Ioc.prod MeasurableSet.univ

theorem measurableSet_cellK (P : ℝ) (k : ℤ) : MeasurableSet (cellK P k) :=
  (measurePreserving_sub_right (volume : Measure (ℝ × Space))
    ((k : ℝ) * P, (0 : Space))).measurable (measurableSet_cellBase P)

theorem muP_eq_cellBase (P : ℝ) : muP P = volume.restrict (cellBase P) := by
  unfold muP cellBase
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem enorm_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two]
  rcases le_total a 1 with h | h
  · exact h.trans le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := mul_le_mul_of_nonneg_left h zero_le
      _ = a ^ 2 := (sq a).symm
      _ ≤ 1 + a ^ 2 := le_add_self

/-- One real shift of the a.e. period identity. -/
theorem ae_shift_real {P : ℝ} {Φ : ℝ × Space → CVec3}
    (h : ∀ᵐ x : ℝ × Space, Φ (x.1 + P, x.2) = Φ x) (s : ℝ) :
    ∀ᵐ x : ℝ × Space, Φ (x.1 + s + P, x.2) = Φ (x.1 + s, x.2) := by
  have hq := (measurePreserving_add_right (volume : Measure (ℝ × Space))
    ((s, (0 : Space)))).quasiMeasurePreserving
  filter_upwards [hq.ae (p := fun y : ℝ × Space => Φ (y.1 + P, y.2) = Φ y) h] with x hx
  have e : x + (s, (0 : Space)) = (x.1 + s, x.2) := by ext <;> simp
  rw [e] at hx
  exact hx

/-- Integer shifts of the a.e. period identity. -/
theorem ae_shift_int {P : ℝ} {Φ : ℝ × Space → CVec3}
    (h : ∀ᵐ x : ℝ × Space, Φ (x.1 + P, x.2) = Φ x) (k : ℤ) :
    ∀ᵐ x : ℝ × Space, Φ (x.1 + (k : ℝ) * P, x.2) = Φ x := by
  induction k using Int.induction_on with
  | zero => exact Filter.Eventually.of_forall fun x => by simp
  | succ i ih =>
    filter_upwards [ih, ae_shift_real h (((i : ℤ) : ℝ) * P)] with x hx1 hx2
    have e : x.1 + (((i : ℤ) + 1 : ℤ) : ℝ) * P = x.1 + ((i : ℤ) : ℝ) * P + P := by
      push_cast; ring
    rw [e, hx2, hx1]
  | pred i ih =>
    filter_upwards [ih, ae_shift_real h ((-(i : ℝ) - 1) * P)] with x hx1 hx2
    have e1 : x.1 + ((-(i : ℤ) - 1 : ℤ) : ℝ) * P = x.1 + (-(i : ℝ) - 1) * P := by
      push_cast; ring
    have e2 : x.1 + (-(i : ℝ) - 1) * P + P = x.1 + ((-(i : ℤ) : ℤ) : ℝ) * P := by
      push_cast; ring
    rw [e1, ← hx2, e2, hx1]

theorem mem_cellK_iff (P : ℝ) (k : ℤ) (z : ℝ × Space) :
    z ∈ cellK P k ↔ (k : ℝ) * P < z.1 ∧ z.1 ≤ ((k : ℝ) + 1) * P := by
  unfold cellK cellBase
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true, Prod.fst_sub]
  have e : ((k : ℝ) + 1) * P = (k : ℝ) * P + P := by ring
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- Finitely many phase cells cover a closed ball. -/
theorem cover_closedBall (P : ℝ) (hP : 0 < P) (M : ℝ) :
    ∃ N : ℤ, Metric.closedBall (0 : ℝ × Space) M ⊆
      ⋃ k ∈ Finset.Icc (-N) N, (cellK P k : Set (ℝ × Space)) := by
  refine ⟨⌈M / P⌉ + 1, fun z hz => ?_⟩
  have hz' : ‖z‖ ≤ M := mem_closedBall_zero_iff.mp hz
  have h1 : ‖z.1‖ ≤ M := (norm_fst_le z).trans hz'
  rw [Real.norm_eq_abs, abs_le] at h1
  obtain ⟨hlo, hhi⟩ := h1
  have hc1 : z.1 / P ≤ (⌈z.1 / P⌉ : ℝ) := Int.le_ceil _
  have hc2 : (⌈z.1 / P⌉ : ℝ) < z.1 / P + 1 := Int.ceil_lt_add_one _
  have hMP : M / P ≤ (⌈M / P⌉ : ℝ) := Int.le_ceil _
  have hlo' : -M / P ≤ z.1 / P := by
    apply div_le_div_of_nonneg_right _ hP.le
    linarith
  have hhi' : z.1 / P ≤ M / P := by
    apply div_le_div_of_nonneg_right _ hP.le
    linarith
  set k : ℤ := ⌈z.1 / P⌉ - 1 with hk
  have hkR : (k : ℝ) = (⌈z.1 / P⌉ : ℝ) - 1 := by rw [hk]; push_cast; ring
  have hk1 : (k : ℝ) * P < z.1 := by
    have : (k : ℝ) < z.1 / P := by rw [hkR]; linarith
    exact (lt_div_iff₀ hP).mp this
  have hk2 : z.1 ≤ ((k : ℝ) + 1) * P := by
    have : z.1 / P ≤ (k : ℝ) + 1 := by rw [hkR]; linarith
    exact (div_le_iff₀ hP).mp this
  have hneg : -M / P = -(M / P) := by ring
  have hN1 : -((⌈M / P⌉ + 1 : ℤ) : ℝ) ≤ (k : ℝ) := by
    push_cast
    linarith
  have hN2 : (k : ℝ) ≤ ((⌈M / P⌉ + 1 : ℤ) : ℝ) := by
    push_cast
    have : (k : ℝ) < z.1 / P := by rw [hkR]; linarith
    linarith
  have hN1' : -(⌈M / P⌉ + 1) ≤ k := by exact_mod_cast hN1
  have hN2' : k ≤ ⌈M / P⌉ + 1 := by exact_mod_cast hN2
  refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_Icc.mpr ⟨hN1', hN2'⟩, ?_⟩
  exact (mem_cellK_iff P k z).mpr ⟨hk1, hk2⟩

/-- Each phase cell has the same `L²` integral as the base cell. -/
theorem setLIntegral_cellK (P : ℝ) (k : ℤ) (Φ : ℝ × Space → CVec3)
    (h : ∀ᵐ x : ℝ × Space, Φ (x.1 + P, x.2) = Φ x) :
    ∫⁻ z in cellK P k, ‖Φ z‖ₑ ^ (2 : ℝ) = ∫⁻ z in cellBase P, ‖Φ z‖ₑ ^ (2 : ℝ) := by
  have hT : MeasurePreserving (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space)))
      volume volume :=
    measurePreserving_sub_right volume _
  have hemb : MeasurableEmbedding (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space))) :=
    (Homeomorph.subRight ((k : ℝ) * P, (0 : Space))).measurableEmbedding
  have key := hT.setLIntegral_comp_preimage_emb hemb
    (fun w : ℝ × Space => ‖Φ (w + ((k : ℝ) * P, (0 : Space)))‖ₑ ^ (2 : ℝ)) (cellBase P)
  simp only [sub_add_cancel] at key
  unfold cellK
  rw [key]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_shift_int h k] with b hb
  have e : b + ((k : ℝ) * P, (0 : Space)) = (b.1 + (k : ℝ) * P, b.2) := by
    ext <;> simp
  rw [e, hb]

theorem lint_cellBase_lt_top {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hY : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) :
    ∫⁻ z in cellBase P, ‖Φ z‖ₑ ^ (2 : ℝ) < ⊤ := by
  have h := lint_lt_top_of_phaseLpNorm hP hY.meas hY.finite
  rw [muP_eq_cellBase] at h
  exact h

theorem lint_closedBall_sq_lt_top {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hY : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) (M : ℝ) :
    ∫⁻ z in Metric.closedBall (0 : ℝ × Space) M, ‖Φ z‖ₑ ^ (2 : ℝ) < ⊤ := by
  obtain ⟨N, hN⟩ := cover_closedBall P hP M
  have hmeas : AEMeasurable (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) volume :=
    (hY.meas.enorm).pow_const (2 : ℝ)
  calc ∫⁻ z in Metric.closedBall (0 : ℝ × Space) M, ‖Φ z‖ₑ ^ (2 : ℝ)
      = ∫⁻ z, (Metric.closedBall (0 : ℝ × Space) M).indicator
          (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) z :=
        (lintegral_indicator measurableSet_closedBall _).symm
    _ ≤ ∫⁻ z, ∑ k ∈ Finset.Icc (-N) N,
          (cellK P k).indicator (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) z := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ Metric.closedBall (0 : ℝ × Space) M
        · obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp (hN hz)
          calc (Metric.closedBall (0 : ℝ × Space) M).indicator
                (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) z = ‖Φ z‖ₑ ^ (2 : ℝ) :=
                indicator_of_mem hz (fun z => ‖Φ z‖ₑ ^ (2 : ℝ))
            _ = (cellK P k).indicator (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) z :=
                (indicator_of_mem hzk (fun z => ‖Φ z‖ₑ ^ (2 : ℝ))).symm
            _ ≤ ∑ j ∈ Finset.Icc (-N) N,
                  (cellK P j).indicator (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) z :=
                Finset.single_le_sum (f := fun j =>
                  (cellK P j).indicator (fun z => ‖Φ z‖ₑ ^ (2 : ℝ)) z)
                  (fun j _ => zero_le) hk
        · rw [indicator_of_notMem hz]
          exact zero_le
    _ = ∑ k ∈ Finset.Icc (-N) N, ∫⁻ z in cellK P k, ‖Φ z‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_finsetSum']
        · exact Finset.sum_congr rfl fun k _ =>
            lintegral_indicator (measurableSet_cellK P k) _
        · intro k _
          exact hmeas.indicator (measurableSet_cellK P k)
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.mpr fun k _ => ?_
        rw [setLIntegral_cellK P k Φ hY.periodic]
        exact lint_cellBase_lt_top hP hY

/-- A field in `Y_2` with period `P > 0` is locally integrable on `ℝ × ℝ³`. -/
theorem locInt_of_isInYr {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hY : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) : LocallyIntegrable Φ volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Space)).mp hK.isBounded
  have hB : ∫⁻ z in Metric.closedBall (0 : ℝ × Space) M, ‖Φ z‖ₑ < ⊤ := by
    calc ∫⁻ z in Metric.closedBall (0 : ℝ × Space) M, ‖Φ z‖ₑ
        ≤ ∫⁻ z in Metric.closedBall (0 : ℝ × Space) M, (1 + ‖Φ z‖ₑ ^ (2 : ℝ)) :=
          lintegral_mono fun z => enorm_le_one_add_sq _
      _ = volume (Metric.closedBall (0 : ℝ × Space) M)
            + ∫⁻ z in Metric.closedBall (0 : ℝ × Space) M, ‖Φ z‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
      _ < ⊤ := ENNReal.add_lt_top.mpr
          ⟨measure_closedBall_lt_top, lint_closedBall_sq_lt_top hP hY M⟩
  have hK' : ∫⁻ z in K, ‖Φ z‖ₑ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hM) hB
  exact ⟨hY.meas.restrict, hK'⟩

theorem mollLocInt : MollLocInt := by
  intro P ν μ hP _ _ _ Φ g hΦ _
  exact locInt_of_isInYr hP hΦ.mem

end UnforcedLeray.Short.PartIIIb.Concrete
