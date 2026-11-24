import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.WindowBound

/-!
# Part II-a, task `PartII-a:N02/4/4/7/2`: Fubini on `measureH c` with `q` innermost (`NzFpHFubini`)

Route: `measureH c = s^{-3/2} ds dq dη` on `cell c = (0,∞) × (0,c] × ℝ` (Units/B0220/Chart.lean).
1. `ZeroWindowBoundAux.measureH_integral_real` turns the left side into `∫_{cell c} s^{-3/2} G`.
2. The measurable equivalence `nzfpAssocE : (s,q,η) ↦ ((s,η),q)` is measure preserving from
   `volume` to `(volume.prod volume).prod volume`, and maps `cell c` onto `S := ((0,∞) × ℝ) × (0,c]`.
3. `setIntegral_prod` on `S` gives the iterated integral with `q` innermost.
4. The inner `q`-integral over `(0,c]` is the interval integral `∫_0^c`, and the constant
   `s^{-3/2}` is pulled out.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The reassociation `(s,q,η) ↦ ((s,η),q)` as a measurable equivalence. -/
def nzfpAssocE : Profile ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm).trans
    MeasurableEquiv.prodAssoc.symm

lemma nzfpAssocE_apply (p : Profile) : nzfpAssocE p = ((p.1, p.2.2), p.2.1) := rfl

lemma nzfpAssocE_mp :
    MeasurePreserving nzfpAssocE (volume : Measure Profile)
      ((((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod Measure.measurePreserving_swap
  have h2 : MeasurePreserving MeasurableEquiv.prodAssoc.symm
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ))
  exact h2.comp h1

theorem nzFpHFubini : NzFpHFubini := by
  intro c hc G hG
  set S : Set ((ℝ × ℝ) × ℝ) := (Ioi (0 : ℝ) ×ˢ univ) ×ˢ Ioc (0 : ℝ) c with hSdef
  have hSmeas : MeasurableSet S :=
    (measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioc
  have hpre : nzfpAssocE ⁻¹' S = cell c := by
    ext p
    simp [hSdef, cell, nzfpAssocE_apply]
  have hmp := nzfpAssocE_mp.restrict_preimage hSmeas
  rw [hpre] at hmp
  set g : (ℝ × ℝ) × ℝ → ℝ := fun z => z.1.1 ^ (-(3 / 2 : ℝ)) * G (z.1.1, z.2, z.1.2) with hgdef
  -- integrability of the weighted integrand on the cell
  have hGint : Integrable (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * G p)
      (volume.restrict (cell c)) := by
    unfold measureH at hG
    have h := (integrable_withDensity_iff_integrable_smul' measurable_weightH
      (ae_weightH_lt_top c)).mp hG
    have hae : (fun x : Profile => (weightH x).toReal • G x) =ᵐ[volume.restrict (cell c)]
        (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * G p) := by
      refine (ae_restrict_iff' (measurableSet_cell c)).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      have hx1 : 0 < x.1 := hx.1
      simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hx1.le _), smul_eq_mul]
    exact h.congr hae
  have hcomp : Integrable (g ∘ nzfpAssocE) (volume.restrict (cell c)) := hGint
  have hgint : IntegrableOn g S
      ((((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))) :=
    (hmp.integrable_comp_emb nzfpAssocE.measurableEmbedding).mp hcomp
  have hS : ∫ z in S, g z ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
      (volume : Measure ℝ)) =
      ∫ x in Ioi (0 : ℝ) ×ˢ univ, ∫ y in Ioc (0 : ℝ) c, g (x, y) :=
    setIntegral_prod (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))
      g hgint
  have hL := hmp.integral_comp nzfpAssocE.measurableEmbedding g
  rw [ZeroWindowBoundAux.measureH_integral_real]
  have hL' : ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * G p = ∫ z in S, g z ∂(((volume : Measure ℝ).prod
      (volume : Measure ℝ)).prod (volume : Measure ℝ)) := hL
  rw [hL', hS]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun x _ => ?_
  show ∫ y in Ioc (0 : ℝ) c, x.1 ^ (-(3 / 2 : ℝ)) * G (x.1, y, x.2) =
    x.1 ^ (-(3 / 2 : ℝ)) * ∫ q in (0 : ℝ)..c, G (x.1, q, x.2)
  rw [intervalIntegral.integral_of_le hc.le, integral_const_mul]

end UnforcedLeray.Short.PartIIa
