import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.NullSets
import Mathlib.MeasureTheory.Function.Jacobian

/-!


Source of record: `the November 2 reference manuscript`; the Ward source
`X₀ = W_μ - W_{μ+1}` (source 4171) with `W_μ = -S_μ(χ_o T)` (`sep:resolvent`, source 3611-3621).

`wardX0` depends on the representative `g` only through `oldPhys R c g τ z = cartLift R c g τ z`,
i.e. through `g` at the chart point `chartOf R c z τ'` with `τ' = τ + 2 log l` in the `sepW`
integral. The chart point is the `c`-periodic reduction of `Axi.chart R τ' z`. Joint phase and
space a.e. null sets of the chart (`NvCInYrHelp.chart_null_all`) give, for a.e. `l`, a.e. `z`
off the chart preimage of the null set; the change of variables `l ↦ τ0 + 2 log l` is a
differentiable image of a null set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst

namespace WardX0Congr


/-! ## The periodic hull of a chart set -/

/-- The `c`-periodic hull of a set `M1` of chart points in the cell coordinate. -/
def hullM (c : ℝ) (M1 : Set Chart) : Set Chart :=
  ⋃ k : ℤ, (fun x : Chart => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) ⁻¹' M1

lemma mem_hullM_iff (c : ℝ) (M1 : Set Chart) (x : Chart) :
    x ∈ hullM c M1 ↔ ∃ k : ℤ, (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) ∈ M1 := by
  simp [hullM]

lemma measurableSet_hullM {c : ℝ} {M1 : Set Chart} (hM1 : MeasurableSet M1) :
    MeasurableSet (hullM c M1) := by
  refine MeasurableSet.iUnion fun k => ?_
  have hT : Measurable (fun x : Chart => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) := by
    fun_prop
  exact hM1.preimage hT

lemma volume_hullM {c : ℝ} {M1 : Set Chart} (h0 : volume M1 = 0) :
    volume (hullM c M1) = 0 := by
  refine measure_iUnion_null fun k => ?_
  have hpres : MeasurePreserving (fun x : Chart => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)))
      volume volume := by
    have h2 := (measurePreserving_add_right (volume : Measure ℝ) ((k : ℝ) * c)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod h2
  exact hpres.quasiMeasurePreserving.preimage_null h0

lemma hullM_periodic (c : ℝ) (M1 : Set Chart) :
    ∀ s ξ η : ℝ, (s, (ξ + c, η)) ∈ hullM c M1 ↔ (s, (ξ, η)) ∈ hullM c M1 := by
  intro s ξ η
  simp only [mem_hullM_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [show ξ + ((k + 1 : ℤ) : ℝ) * c = ξ + c + (k : ℝ) * c by push_cast; ring]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    rw [show ξ + c + ((k - 1 : ℤ) : ℝ) * c = ξ + (k : ℝ) * c by push_cast; ring]
    exact hk

/-! ## The cell reduction and the chart identity -/

lemma qRed_mem {c : ℝ} (hc : 0 < c) (q : ℝ) :
    q - c * ⌊q / c + 1 / 2⌋ ∈ Ico (-c / 2) (c / 2) := by
  have h1 := Int.floor_le (q / c + 1 / 2)
  have h2 := Int.lt_floor_add_one (q / c + 1 / 2)
  have e : c * (q / c + 1 / 2) = q + c / 2 := by
    have hc' : c ≠ 0 := hc.ne'
    field_simp
  have h1' := mul_le_mul_of_nonneg_left h1 hc.le
  have h2' := mul_lt_mul_of_pos_left h2 hc
  rw [e] at h1' h2'
  rw [mul_add, mul_one] at h2'
  constructor <;> linarith

lemma hRad_pos {z : Space} (hz : z ∉ axis) : 0 < hRad z := by
  unfold hRad
  apply Real.sqrt_pos.2
  by_contra hneg
  apply hz
  have h0 : z 0 ^ 2 + z 1 ^ 2 ≤ 0 := not_lt.1 hneg
  have a0 : z 0 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (z 1)]) (sq_nonneg _)
  have a1 : z 1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (z 0)]) (sq_nonneg _)
  have b0 : z 0 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).1 a0
  have b1 : z 1 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).1 a1
  simp only [axis, Set.mem_setOf_eq]
  exact ⟨b0, b1⟩

lemma phase_eq_log {R : ℝ} (hR : 0 < R) {z : Space} (hz : z ∉ axis) (τ : ℝ) :
    Axi.phase R τ z = R * Real.log (ϱ z / R) + R * τ / 2 := by
  have hϱ : 0 < ϱ z := hRad_pos hz
  unfold Axi.phase Axi.age
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) (by positivity)]
  push_cast
  ring

lemma chartOf_eq {R c : ℝ} (hR : 0 < R) {z : Space} (hz : z ∉ axis) (τ : ℝ) :
    NearInst.chartOf R c z τ =
      ((Axi.chart R τ z).1, ((Axi.chart R τ z).2.1 - c * ⌊(Axi.chart R τ z).2.1 / c + 1 / 2⌋,
        (Axi.chart R τ z).2.2)) := by
  have hph := phase_eq_log hR hz τ
  show NearInst.chartOf R c z τ =
    (R ^ 2 / ϱ z ^ 2, (Axi.phase R τ z - c * ⌊Axi.phase R τ z / c + 1 / 2⌋, R * z 2 / ϱ z))
  rw [hph]
  rfl

lemma chart_mem_hull {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {N' : Set Chart} {z : Space}
    (hz : z ∉ axis) (τ : ℝ) (h : NearInst.chartOf R c z τ ∈ N') :
    Axi.chart R τ z ∈ hullM c (N' ∩ (Ioi (0 : ℝ) ×ˢ qCell c)) := by
  have hpos : 0 < (NearInst.chartOf R c z τ).1 := by
    show 0 < R ^ 2 / hRad z ^ 2
    have := hRad_pos hz
    positivity
  have hq : (NearInst.chartOf R c z τ).2.1 ∈ Ico (-c / 2) (c / 2) := by
    rw [chartOf_eq hR hz τ]
    exact qRed_mem hc (Axi.chart R τ z).2.1
  have hM1 : NearInst.chartOf R c z τ ∈ N' ∩ (Ioi (0 : ℝ) ×ˢ qCell c) := by
    refine ⟨h, hpos, ?_⟩
    unfold qCell
    exact ⟨hq, Set.mem_univ _⟩
  rw [chartOf_eq hR hz τ] at hM1
  rw [mem_hullM_iff]
  refine ⟨-⌊(Axi.chart R τ z).2.1 / c + 1 / 2⌋, ?_⟩
  have e2 : (Axi.chart R τ z).2.1 + ((-⌊(Axi.chart R τ z).2.1 / c + 1 / 2⌋ : ℤ) : ℝ) * c
      = (Axi.chart R τ z).2.1 - c * ⌊(Axi.chart R τ z).2.1 / c + 1 / 2⌋ := by
    push_cast
    ring
  rw [e2]
  exact hM1

/-! ## Null-set transfer along the phase curve -/

lemma measurableSet_qCell' (c : ℝ) : MeasurableSet (qCell c) := by
  unfold qCell
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- For a periodic null set `M1` of chart points, for every phase `τ0`, for a.e. `l ∈ (0,1)`
(Lebesgue), for a.e. `z`, the chart point `Axi.chart R (τ0 + 2 log l) z` lies outside the hull. -/
lemma ae_curve {R c τ0 : ℝ} (hR : 0 < R) (hc : 0 < c) (M1 : Set Chart)
    (hM1 : MeasurableSet M1) (h0 : volume M1 = 0) :
    ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ᵐ z : Space,
      Axi.chart R (τ0 + 2 * Real.log l) z ∉ hullM c M1 := by
  have hMm : MeasurableSet (hullM c M1) := measurableSet_hullM hM1
  have hM0 : volume (hullM c M1) = 0 := volume_hullM h0
  have hall := UnforcedLeray.Short.IIb.NvCInYrHelp.chart_null_all (P := 2 * c / R) hR hc rfl
    (hullM c M1) hMm hM0 (hullM_periodic c M1)
  have hB : volume {x : ℝ × Space | Axi.chart R x.1 x.2 ∈ hullM c M1} = 0 := by
    have := ae_iff.1 hall
    simpa using this
  have hφ : Measurable (fun p : ℝ × Space => (τ0 + 2 * Real.log p.1, p.2)) :=
    (measurable_const.add ((Real.measurable_log.comp measurable_fst).const_mul 2)).prodMk
      measurable_snd
  have hPm : MeasurableSet {p : ℝ × Space | Axi.chart R (τ0 + 2 * Real.log p.1) p.2 ∈ hullM c M1} :=
    hMm.preimage ((UnforcedLeray.Short.IIb.NvCInYrHelp.measurable_chartXY R).comp hφ)
  have hIoo : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hψ : volume ((fun x : ℝ × Space => (Real.exp ((x.1 - τ0) / 2), x.2)) ''
      {x : ℝ × Space | Axi.chart R x.1 x.2 ∈ hullM c M1}) = 0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    · apply Differentiable.differentiableOn
      fun_prop
    · exact hB
  have hsub : {p : ℝ × Space | Axi.chart R (τ0 + 2 * Real.log p.1) p.2 ∈ hullM c M1} ∩
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) ⊆
      (fun x : ℝ × Space => (Real.exp ((x.1 - τ0) / 2), x.2)) ''
        {x : ℝ × Space | Axi.chart R x.1 x.2 ∈ hullM c M1} := by
    rintro p ⟨hp, hpI⟩
    refine ⟨(τ0 + 2 * Real.log p.1, p.2), hp, ?_⟩
    have hpos : 0 < p.1 := hpI.1.1
    refine Prod.ext ?_ rfl
    show Real.exp ((τ0 + 2 * Real.log p.1 - τ0) / 2) = p.1
    rw [show (τ0 + 2 * Real.log p.1 - τ0) / 2 = Real.log p.1 by ring, Real.exp_log hpos]
  have hsplit : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure Space) =
      (volume : Measure (ℝ × Space)).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hprod : ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure Space))
      {p : ℝ × Space | Axi.chart R (τ0 + 2 * Real.log p.1) p.2 ∈ hullM c M1} = 0 := by
    rw [hsplit, Measure.restrict_apply' hIoo]
    exact measure_mono_null hsub hψ
  have hae := (Measure.measure_prod_null hPm).1 hprod
  filter_upwards [hae] with l hl
  have hl' : volume {z : Space | Axi.chart R (τ0 + 2 * Real.log l) z ∈ hullM c M1} = 0 := hl
  have hnot := measure_eq_zero_iff_ae_notMem.1 hl'
  filter_upwards [hnot] with z hz
  exact hz

/-! ## The `sepW` congruence -/

/-- `sepW` depends on the representative only through its values off an `ageμ`-null set. -/
lemma sepW_congr {R c : ℝ} (ν : ℝ) (μ : ℂ) (hR : 0 < R) (hc : 0 < c)
    (g g' : Chart → Ten3) (N' : Set Chart) (hN'm : MeasurableSet N')
    (hN'0 : Axi.ageμ c (-1 / 2) N' = 0) (hsub : {p | ¬ g p = g' p} ⊆ N') (τ0 : ℝ) (y : Space) :
    IIIa.sepW ν μ (oldPhys R c g) y τ0 = IIIa.sepW ν μ (oldPhys R c g') y τ0 := by
  have hM1m : MeasurableSet (N' ∩ (Ioi (0 : ℝ) ×ˢ qCell c)) :=
    hN'm.inter (measurableSet_Ioi.prod (measurableSet_qCell' c))
  have hM1v : volume (N' ∩ (Ioi (0 : ℝ) ×ˢ qCell c)) = 0 :=
    UnforcedLeray.Short.IIb.NvCNorm.volume_null_of_ageμ_null hc hN'0
  have hE := ae_curve (τ0 := τ0) hR hc (N' ∩ (Ioi (0 : ℝ) ×ˢ qCell c)) hM1m hM1v
  have hz := ae_not_mem_axis
  have hT : ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ᵐ z : Space,
      oldPhys R c g (τ0 + 2 * Real.log l) z = oldPhys R c g' (τ0 + 2 * Real.log l) z := by
    filter_upwards [hE] with l hl
    filter_upwards [hl, hz] with z hz1 hz2
    have hg : g (NearInst.chartOf R c z (τ0 + 2 * Real.log l)) =
        g' (NearInst.chartOf R c z (τ0 + 2 * Real.log l)) := by
      by_contra hne
      exact hz1 (chart_mem_hull hR hc hz2 _ (hsub hne))
    unfold oldPhys NearInst.cartLift
    rw [hg]
  unfold IIIa.sepW
  funext i
  congr 1
  apply integral_congr_ae
  filter_upwards [hT] with l hl
  congr 1
  apply integral_congr_ae
  filter_upwards [hl] with z hz1
  rw [hz1]

end WardX0Congr

open WardX0Congr in
/-- **`IIIb:D2/3/1/8/1/b`** (`wardX0_congr_ae`): `wardX0` depends on `g` only through its
`ageμ c (-1/2)`-class. -/
theorem wardX0_congr_ae (ν μ R c : ℝ) (hR : 0 < R) (hc : 0 < c) (g g' : Chart → Ten3)
    (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), g p = g' p) :
    wardX0 ν μ R c g = wardX0 ν μ R c g' := by
  obtain ⟨N', hsub, hN'm, hN'0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  funext τ y
  unfold wardX0
  rw [sepW_congr ν (μ : ℂ) hR hc g g' N' hN'm hN'0 hsub τ y,
    sepW_congr ν ((μ : ℂ) + 1) hR hc g g' N' hN'm hN'0 hsub τ y]

end UnforcedLeray.Short.PartIIIb.Concrete
