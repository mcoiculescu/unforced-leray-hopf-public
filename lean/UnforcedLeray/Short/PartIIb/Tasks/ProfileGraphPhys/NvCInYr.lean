import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# Part II-b, task `PartII-b:T10/1` (`NvCInYr`): the complex ring lift of a profile of `H_r` lies in `Y_r`

Source of record: `the November 2 reference manuscript`, lines 1902-1906.

Target: `nvCInYr_proof : UnforcedLeray.Short.IIb.NvCInYr`.

Proof outline. Take a measurable, everywhere `c`-periodic representative `F'` of `F`
(`periodicRepresentative`, off a periodic null set `M`). For `F'` the phase shift `τ ↦ τ + 2εc` is
the cell shift `q ↦ q + c` of the chart (`Axi.chart_add_period`), so `NvC F'` is everywhere
`2εc`-periodic and measurable (`Axi.measurable_Nv`). The chart pulls the periodic null set `M` back
to a null set of `ℝ × Space` (`chartNullPullback` on one period, then translation by `k·P`).
Hence `NvC F = NvC F'` almost everywhere, which gives periodicity, measurability, and the norm
bound from `phaseLpNorm_NvC`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace NvCInYrHelp

lemma measurable_chartXY (R : ℝ) : Measurable fun x : ℝ × Space => Axi.chart R x.1 x.2 :=
  ((Axi.measurable_age R).comp measurable_snd).prodMk
    ((Axi.measurable_phase R).prodMk ((Axi.measurable_trans R).comp measurable_snd))

lemma measurable_reM' : Measurable reM := by
  unfold reM
  fun_prop

lemma measurable_imM' : Measurable imM := by
  unfold imM
  fun_prop

lemma measurable_NvC' (R : ℝ) {b : CProf} (hb : Measurable b) : Measurable (NvC R b) := by
  have h1 : Measurable fun z => reM (b z) := measurable_reM'.comp hb
  have h2 : Measurable fun z => imM (b z) := measurable_imM'.comp hb
  have hr : Measurable B0412.realC := by
    unfold B0412.realC
    fun_prop
  have m1 : Measurable fun x : ℝ × Space => Axi.Nv R (fun z => reM (b z)) x.1 x.2 :=
    Axi.measurable_Nv R h1
  have m2 : Measurable fun x : ℝ × Space => Axi.Nv R (fun z => imM (b z)) x.1 x.2 :=
    Axi.measurable_Nv R h2
  exact (hr.comp m1).add ((hr.comp m2).const_smul Complex.I)

/-- The lift of a field which is everywhere `q`-periodic is everywhere phase-periodic. -/
lemma nvC_add_period {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) (G : CProf)
    (hG : ∀ s ξ η, G (s, (ξ + c, η)) = G (s, (ξ, η))) (τ : ℝ) (y : Space) :
    NvC R G (τ + P, y) = NvC R G (τ, y) := by
  have hchart : G (Axi.chart R (τ + P) y) = G (Axi.chart R τ y) := by
    rw [Axi.chart_add_period hR hP]
    exact hG (Axi.age R y) (Axi.phase R τ y) (Axi.trans R y)
  have h1 : reM (G (Axi.chart R (τ + P) y)) = reM (G (Axi.chart R τ y)) := by rw [hchart]
  have h2 : imM (G (Axi.chart R (τ + P) y)) = imM (G (Axi.chart R τ y)) := by rw [hchart]
  simp only [NvC, Axi.Nv, h1, h2]

/-- The shift `(τ, y) ↦ (τ + k·P, y)` moves the chart by the cell shift `q ↦ q + k c`. -/
lemma chart_add_nat {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) (M : Set Coord)
    (hMper : ∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) (y : Space) (n : ℕ) :
    ∀ σ : ℝ, Axi.chart R (σ + n * P) y ∈ M ↔ Axi.chart R σ y ∈ M := by
  induction n with
  | zero => intro σ; simp
  | succ n ih =>
    intro σ
    have h1 : σ + ((n + 1 : ℕ) : ℝ) * P = (σ + n * P) + P := by push_cast; ring
    rw [h1, Axi.chart_add_period hR hP, hMper (Axi.age R y) (Axi.phase R (σ + n * P) y)
      (Axi.trans R y)]
    exact ih σ

lemma chart_add_int {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) (M : Set Coord)
    (hMper : ∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) (y : Space) (k : ℤ) (σ : ℝ) :
    Axi.chart R (σ + k * P) y ∈ M ↔ Axi.chart R σ y ∈ M := by
  rcases Int.natAbs_eq k with h | h
  · rw [h]
    exact chart_add_nat hR hP M hMper y k.natAbs σ
  · have := chart_add_nat hR hP M hMper y k.natAbs (σ + (-(k.natAbs : ℝ)) * P)
    have e : σ + (-(k.natAbs : ℝ)) * P + (k.natAbs : ℝ) * P = σ := by ring
    rw [e] at this
    have hk : (k : ℝ) = -((k.natAbs : ℕ) : ℝ) := by exact_mod_cast h
    rw [hk]
    exact this.symm

/-- Off a periodic null set `M`, the chart pulls back to a null set of `ℝ × Space`, over all
phases. -/
lemma chart_null_all {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) (M : Set Coord)
    (hMm : MeasurableSet M) (hM0 : volume M = 0)
    (hMper : ∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) :
    ∀ᵐ x : ℝ × Space, Axi.chart R x.1 x.2 ∉ M := by
  have hP0 : 0 < P := by rw [hP]; positivity
  have hR0 : R ≠ 0 := hR.ne'
  have hnull0 := chartNullPullback R c P hR hc hP M hMm hM0 hMper
  have hmeasSet : MeasurableSet {x : ℝ × Space | Axi.chart R x.1 x.2 ∉ M} :=
    measurable_chartXY R hMm.compl
  -- the set `(0, P] × ℝ³`
  have hA : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)).restrict
      (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)), Axi.chart R x.1 x.2 ∉ M := by
    have h0 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
        ((volume : Measure Space).restrict univ), Axi.chart R x.1 x.2 ∉ M := by
      rw [Measure.restrict_univ]
      refine (Measure.ae_prod_iff_ae_ae (p := fun x : ℝ × Space => Axi.chart R x.1 x.2 ∉ M)
        hmeasSet).2 ?_
      filter_upwards [hnull0] with τ hτ
      exact hτ
    rw [Measure.prod_restrict] at h0
    exact h0
  have hS0 : MeasurableSet (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hA' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      x ∈ Ioc (0 : ℝ) P ×ˢ (univ : Set Space) → Axi.chart R x.1 x.2 ∉ M :=
    (ae_restrict_iff' hS0).1 hA
  -- translates of the cell
  have hD : ∀ k : ℤ, ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      x.1 ∈ Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P) → Axi.chart R x.1 x.2 ∉ M := by
    intro k
    have hmp : MeasurePreserving (fun x : ℝ × Space => (x.1 - (k : ℝ) * P, x.2))
        ((volume : Measure ℝ).prod (volume : Measure Space))
        ((volume : Measure ℝ).prod (volume : Measure Space)) :=
      (measurePreserving_sub_right (volume : Measure ℝ) ((k : ℝ) * P)).prod
        (MeasurePreserving.id (volume : Measure Space))
    filter_upwards [hmp.quasiMeasurePreserving.ae hA'] with x hx hxk
    have hxS : (x.1 - (k : ℝ) * P, x.2) ∈ Ioc (0 : ℝ) P ×ˢ (univ : Set Space) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩
      · linarith [hxk.1]
      · have := hxk.2
        linarith [show ((k : ℝ) + 1) * P = (k : ℝ) * P + P by ring]
    have key := chart_add_int hR0 hP M hMper x.2 k (x.1 - (k : ℝ) * P)
    rw [sub_add_cancel] at key
    rw [key]
    exact hx hxS
  have hall := ae_all_iff.2 hD
  filter_upwards [hall] with x hx
  intro hxM
  set z : ℝ := x.1 / P with hz
  have hzP : z * P = x.1 := div_mul_cancel₀ _ hP0.ne'
  have h1 : ((⌈z⌉ : ℤ) : ℝ) - 1 < z := by
    have := Int.ceil_lt_add_one z
    linarith
  have h2 : z ≤ ((⌈z⌉ : ℤ) : ℝ) := Int.le_ceil z
  apply hx (⌈z⌉ - 1)
  · push_cast
    constructor
    · have := mul_lt_mul_of_pos_right h1 hP0
      linarith
    · have := mul_le_mul_of_nonneg_right h2 hP0.le
      linarith [show ((⌈z⌉ : ℤ) : ℝ) - 1 + 1 = ((⌈z⌉ : ℤ) : ℝ) by ring]
  · exact hxM

end NvCInYrHelp

open NvCInYrHelp in
theorem nvCInYr_proof : NvCInYr := by
  intro c ε r F hc hε hr hF
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    field_simp
  obtain ⟨F', M, hF'm, hF'per, hMm, hM0, hMper, hFF'⟩ :=
    periodicRepresentative c r hc F hF.periodic hF.meas
  have hNull := chart_null_all (P := 2 * ε * c) hR hc hP M hMm hM0 hMper
  have hax : ∀ᵐ x : ℝ × Space, x.2 ∉ Axi.axis :=
    (Measure.quasiMeasurePreserving_snd).ae Axi.ae_not_mem_axis
  -- pointwise identity off the axis and off the pulled-back null set
  have heq : NvC ε⁻¹ F =ᵐ[volume] NvC ε⁻¹ F' := by
    filter_upwards [hNull, hax] with x hxM hxax
    have hpos : 0 < Axi.age ε⁻¹ x.2 := Axi.age_pos hR0 hxax
    have key := hFF' _ (show 0 < (Axi.chart ε⁻¹ x.1 x.2).1 from hpos) hxM
    simp only [NvC, Axi.Nv, key]
  have hper' : ∀ τ y, NvC ε⁻¹ F' (τ + 2 * ε * c, y) = NvC ε⁻¹ F' (τ, y) :=
    fun τ y => nvC_add_period hR0 hP F' hF'per τ y
  have hper : ∀ᵐ x : ℝ × Space, NvC ε⁻¹ F (x.1 + 2 * ε * c, x.2) = NvC ε⁻¹ F x := by
    have hmp : MeasurePreserving (fun x : ℝ × Space => (x.1 + 2 * ε * c, x.2))
        ((volume : Measure ℝ).prod (volume : Measure Space))
        ((volume : Measure ℝ).prod (volume : Measure Space)) :=
      (measurePreserving_add_right (volume : Measure ℝ) (2 * ε * c)).prod
        (MeasurePreserving.id (volume : Measure Space))
    filter_upwards [hmp.quasiMeasurePreserving.ae heq, heq] with x h1 h2
    have h1' : NvC ε⁻¹ F (x.1 + 2 * ε * c, x.2) = NvC ε⁻¹ F' (x.1 + 2 * ε * c, x.2) := h1
    rw [h1', h2]
    exact hper' x.1 x.2
  have hmeas : AEStronglyMeasurable (NvC ε⁻¹ F) volume :=
    ((measurable_NvC' ε⁻¹ hF'm).aestronglyMeasurable).congr heq.symm
  have hfin : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ F) < ⊤ := by
    rw [phaseLpNorm_NvC hc hr hε F hF.periodic hF.meas]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  exact ⟨hper, hmeas, hfin⟩

end UnforcedLeray.Short.IIb
