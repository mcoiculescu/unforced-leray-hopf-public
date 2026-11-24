import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Closed.PairBoundPh
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_1

/-!
# `PairLinear` (task `PartIII-b:C/near/pins/3/3/1/3`)

Source `the November 2 reference manuscript` 2666-2668, 2683-2689, 1640-1641.
Additivity and real homogeneity of the pairing `f ↦ ⟨Φ, 𝒩_v f⟩` on measurable `L²` chart fields,
and its dependence only on the `ageμ c (-3/2)`-class of a field (for an arbitrary representative `f`
and a measurable representative `f'`).  Additivity and homogeneity come from the pointwise linearity
of `velPhys` and the `pairF` additivity lemma; the class statement uses `liftFun_congr_ae_left`
(the measurable-null-set detection of the lift) and Fubini on the phase cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Pointwise additivity of the physical velocity in the chart field. -/
theorem plp_velPhys_add (R c : ℝ) (b b' : Chart → Merid) :
    velPhys R c (b + b') = velPhys R c b + velPhys R c b' := by
  funext x
  have e : perExt c (b + b') = perExt c b + perExt c b' := rfl
  simp only [velPhys, Pi.add_apply, e, Nv_add, wda_realC_add]

/-- Pointwise real homogeneity of the physical velocity in the chart field. -/
theorem plp_velPhys_smul (R c a : ℝ) (b : Chart → Merid) :
    velPhys R c (a • b) = fun x => (a : ℂ) • velPhys R c b x := by
  funext x
  have e : perExt c (a • b) = a • perExt c b := rfl
  simp only [velPhys, e, Nv_smul, Pi.smul_apply, wda_realC_smul]

/-- Real homogeneity of `pairF` in its field slot (no integrability needed). -/
theorem plp_pairF_smul {P : ℝ} (a : ℝ) (Φ u : ℝ × Space → CVec3) :
    pairF P Φ (fun x => (a : ℂ) • u x) = a • pairF P Φ u := by
  unfold pairF phaseInt
  have h1 : ∀ x, dotL (Φ x) ((a : ℂ) • u x) = (a : ℂ) * dotL (Φ x) (u x) := fun x => by
    rw [map_smul, smul_eq_mul]
  simp only [h1, integral_const_mul, Complex.real_smul]
  ring

/-- `pairF` depends only on the field up to a.e. equality on the phase cell. -/
theorem plp_pairF_congr_ae {P : ℝ} (Φ : ℝ × Space → CVec3) {u u' : ℝ × Space → CVec3}
    (h : u =ᵐ[volume.restrict (phaseCell P)] u') : pairF P Φ u = pairF P Φ u' := by
  unfold pairF phaseInt
  congr 1
  have hprod := Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)
  have hae2 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure Space), dotL (Φ x) (u x) = dotL (Φ x) (u' x) := by
    rw [hprod]
    filter_upwards [h] with x hx
    rw [hx]
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  refine integral_congr_ae ?_
  filter_upwards [hae3] with t ht
  exact integral_congr_ae ht

theorem pairLinearPh : PairLinearPh := by
  intro c ε hc hε Φ hΦ
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP0 : 0 < 2 * ε * c := by positivity
  haveI : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hPR : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  obtain ⟨C, hC⟩ := pairBoundPh c ε hc hε Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro f f' hf hf' hfL hfL'
    have hsum : velPhys ε⁻¹ c (f + f') = velPhys ε⁻¹ c f + velPhys ε⁻¹ c f' :=
      plp_velPhys_add _ _ _ _
    have hI1 := (hC f hf hfL).1
    have hI2 := (hC f' hf' hfL').1
    have hI3 := (hC (f + f') (hf.add hf') (hfL.add hfL')).1
    rw [hsum] at hI3 ⊢
    exact pairF_add_right_of_integrable hI1 hI2 hI3
  · intro a f hf hfL
    have hsm : velPhys ε⁻¹ c (a • f) = fun x => (a : ℂ) • velPhys ε⁻¹ c f x :=
      plp_velPhys_smul _ _ _ _
    rw [hsm]
    exact plp_pairF_smul a _ _
  · intro f f' hf' hae
    apply plp_pairF_congr_ae
    have hl : liftFun ε⁻¹ c f' =ᵐ[phaseμ (2 * ε * c)] liftFun ε⁻¹ c f :=
      liftFun_congr_ae_left hR hc hPR hf' hae.symm
    rw [wda_ae_phaseμ] at hl
    filter_upwards [hl] with x hx
    rw [fwuB_velPhys_eq ε⁻¹ c hR.ne' f x, fwuB_velPhys_eq ε⁻¹ c hR.ne' f' x, hx]

end UnforcedLeray.Short.PartIIIb.NearInst
