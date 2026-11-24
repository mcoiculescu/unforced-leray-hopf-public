import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_1

/-!
# `DictQmp` (task `PartIII-b:C/near/pins/3/5/1/1`)

Source `the November 2 reference manuscript` lines 2666-2668: the dilation
`(τ, y) ↦ (ε y, τ mod P)` is quasi-measure-preserving `ℝ × ℝ³ → PSpace P` for `ε ≠ 0`.

The map is `Prod.map (ε • ·) (coe) ∘ Prod.swap`.  Scaling by `ε ≠ 0` is quasi-measure-preserving
on `ℝ³` (`Measure.quasiMeasurePreserving_smul`), and the covering `ℝ → AddCircle P` is
quasi-measure-preserving (proved below from `AddCircle.measurePreserving_mk`, following the
pattern `UnforcedLeray.PhaseTrace.ae_comp_mk`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.B0223 (PSpace)

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- The covering map `ℝ → AddCircle P` is quasi-measure-preserving for Lebesgue measure. -/
theorem dictQmp_coe (P : ℝ) [hP : Fact (0 < P)] :
    Measure.QuasiMeasurePreserving (fun t : ℝ => (t : AddCircle P)) volume
      (volume : Measure (AddCircle P)) := by
  refine ⟨(AddCircle.measurePreserving_mk P 0).measurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
  rw [Measure.map_apply (AddCircle.measurePreserving_mk P 0).measurable hS]
  have hp' : ∀ᵐ x ∂(volume : Measure (AddCircle P)), x ∉ S :=
    (measure_eq_zero_iff_ae_notMem).1 hS0
  have h : ∀ k : ℤ, ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 + k • P) (0 + (k + 1) • P))),
      (t : AddCircle P) ∉ S := by
    intro k
    have hmp := AddCircle.measurePreserving_mk P (0 + k • P)
    have e : (0 + (k + 1) • P) = (0 + k • P) + P := by rw [add_smul, one_smul]; ring
    rw [e]
    exact hmp.quasiMeasurePreserving.ae hp'
  have hae : ∀ᵐ t : ℝ ∂volume, (t : AddCircle P) ∉ S := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← iUnion_Ioc_add_zsmul hP.out 0,
      ae_restrict_iUnion_iff]
    exact h
  exact measure_eq_zero_iff_ae_notMem.2 hae

theorem dictQmp : DictQmp := by
  intro P ε _ hε
  have hQ1 : Measure.QuasiMeasurePreserving (Prod.swap : ℝ × Space → Space × ℝ)
      (volume : Measure (ℝ × Space)) (volume : Measure (Space × ℝ)) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap.quasiMeasurePreserving
  have hQ2 : Measure.QuasiMeasurePreserving
      (Prod.map (fun y : Space => ε • y) (fun t : ℝ => (t : AddCircle P)))
      ((volume : Measure Space).prod (volume : Measure ℝ))
      ((volume : Measure Space).prod (volume : Measure (AddCircle P))) :=
    QuasiMeasurePreserving.prodMap (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure Space)) hε) (dictQmp_coe P)
  have hfun : (fun x : ℝ × Space => ((ε • x.2, (x.1 : AddCircle P)) : PSpace P)) =
      (Prod.map (fun y : Space => ε • y) (fun t : ℝ => (t : AddCircle P)) ∘ Prod.swap) := by
    funext x
    rfl
  rw [hfun]
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact hQ2.comp hQ1

end UnforcedLeray.Short.PartIIIb.NearInst
