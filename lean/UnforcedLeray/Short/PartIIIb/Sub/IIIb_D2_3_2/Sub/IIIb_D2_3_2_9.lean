import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.PairLinear
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Bridge

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

theorem measurable_chartTau' (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

theorem measurable_chartY' (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart => (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

theorem measurable_coefOf (R : ℝ) (F : ℝ → Space → Space)
    (hF : Continuous (fun x : ℝ × Space => F x.1 x.2)) : Measurable (coefOf R F) := by
  unfold coefOf
  have h1 : Measurable fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p) :=
    hF.measurable.comp ((measurable_chartTau' R).prodMk (measurable_chartY' R))
  have h2 : ∀ i : Fin 3, Measurable fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p) i :=
    fun i => (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.measurable.comp h1
  have h3 : Measurable fun p : Chart => (!₂[F (NearInst.chartTau R p) (NearInst.chartY R p) 0,
      F (NearInst.chartTau R p) (NearInst.chartY R p) 2] : Merid) := by
    have : Measurable fun p : Chart => (![F (NearInst.chartTau R p) (NearInst.chartY R p) 0,
      F (NearInst.chartTau R p) (NearInst.chartY R p) 2] : Fin 2 → ℝ) := by
      refine measurable_pi_lambda _ fun i => ?_
      fin_cases i
      · exact h2 0
      · exact h2 2
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp this
  exact ((Real.continuous_sqrt.measurable.comp measurable_fst).inv).smul h3


theorem velPhys_pin_ae {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {b : Chart → Merid}
    (hb : Measurable b) {F : ℝ → Space → Space}
    (hF : Continuous (fun x : ℝ × Space => F x.1 x.2)) (hL : IsAxiLift ε⁻¹ c F)
    (h : b =ᵐ[ageμ c (-3 / 2)] coefOf ε⁻¹ F) :
    velPhys ε⁻¹ c b =ᵐ[volume.restrict (phaseCell (2 * ε * c))]
      fun x => B0412.realC (F x.1 x.2) := by
  have h1 := wda_velPhys_congr hc hε hb (measurable_coefOf _ F hF) h
  filter_upwards [h1] with x hx
  rw [hx]
  exact hL x

section Lifts

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- `WardLifts` from its third clause `WardVelPhysYH` (source 4161-4174): the first two clauses
follow from the pins, the lift identities `liftH`, `liftE`, and the dependence of `pairF` only on
the a.e. class on the phase cell. -/
theorem wardLifts_of (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε)
    (hν : 0 < ν) {μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ)
    (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (ha : WardVelPhysYH B hc ε hε hν μ hχo χy U p) :
    WardLifts B hc ε hε hν μ hχo χy U p := by
  intro hW T g₁ g₂ hg1 hg2 hin Ψ
  obtain ⟨_, hh, hE⟩ := wardPinned_reg B hε.ne' hW T g₁ g₂ hg1 hg2
  refine ⟨?_, ?_, ha hW T g₁ g₂ hg1 hg2 hin⟩
  · apply NearInst.pl_pairF_congr_ae
    refine (velPhys_pin_ae hc hε (Lp.stronglyMeasurable _).measurable
      hin.smoothH.continuous hin.liftH ?_).trans
      (ae_restrict_of_ae (realC_wardHr_ae ν μ ε⁻¹ c χy U (g₁ + g₂)))
    rw [← NearInst.ae_bodyMeasure c γ ν]
    exact hh
  · apply NearInst.pl_pairF_congr_ae
    refine (velPhys_pin_ae hc hε (Lp.stronglyMeasurable _).measurable
      hin.smoothE.continuous hin.liftE ?_).trans
      (ae_restrict_of_ae (realC_wardEr_ae ν μ ε⁻¹ c χy U p (g₁ + g₂)))
    rw [← NearInst.ae_srcMeasure c]
    exact hE

end Lifts

end UnforcedLeray.Short.PartIIIb.Concrete
