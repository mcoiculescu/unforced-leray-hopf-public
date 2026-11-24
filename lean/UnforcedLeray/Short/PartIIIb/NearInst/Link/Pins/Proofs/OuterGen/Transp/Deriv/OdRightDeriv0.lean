import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdTransDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdDilDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdHeatDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdProdRule
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdRepAlg
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdExists
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdTransCont

/-!
# `OD_RightDeriv0` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/15`)

Right derivative at `0` of `r ↦ outerTransp h r Ψ`, `h = ν ε² ≥ 0`, on a smooth phase test:
the product rule over the three factors `transC(-r)`, `heatC(h(e^r-1))`, `dilN(e^{-r/2})`,
then the scalar `e^{-r/4}`; the derivative is identified with `Ψ'` by `OD_RepAlg`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem odRightDeriv0 : OD_RightDeriv0 := by
  unfold OD_RightDeriv0
  intro p ψ hψ Ψ Ψ' hΨ hΨ'
  set h : ℝ := p.ν * p.ε ^ 2 with hdef
  have hh : 0 ≤ h := mul_nonneg p.ν_pos.le (by positivity)
  -- representatives of the derivatives of ψ
  obtain ⟨Ψτ, hΨτ⟩ := odExists p (dτ ψ) hψ.dτ
  obtain ⟨ΨΔ, hΨΔ⟩ := odExists p (lapT ψ) hψ.lapT
  obtain ⟨Ψx, hΨx⟩ := odExists p (radialT ψ) hψ.radialT
  have hRep : Ψ' = ((h : ℝ) : ℂ) • ΨΔ - ((1 / 2 : ℝ) : ℂ) • Ψx - Ψ + Ψτ :=
    odRepAlg p ψ Ψ Ψτ ΨΔ Ψx Ψ' hΨ hΨτ hΨΔ hΨx hΨ'
  -- elementary facts at r = 0
  have hexp : ∀ r : ℝ, (Real.exp (r / 2))⁻¹ = Real.exp (-r / 2) := fun r => by
    rw [neg_div, Real.exp_neg]
  have hx10 : UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC)
      (Real.exp (-0 / 2)) Ψ = Ψ := by
    rw [neg_zero, zero_div, Real.exp_zero, UnforcedLeray.B0223.dilN_one]
  have hT0 : UnforcedLeray.B0223.heatC (h * (Real.exp 0 - 1))
      (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-0 / 2)) Ψ) = Ψ := by
    rw [hx10, Real.exp_zero, sub_self, mul_zero, UnforcedLeray.B0223.heatC_of_nonpos le_rfl]
  -- strong continuity of the heat factor within [0, ∞) at 0
  have hcontH : ∀ y : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period,
      ContinuousWithinAt (fun r : ℝ => UnforcedLeray.B0223.heatC (h * (Real.exp r - 1)) y)
        (Ici 0) 0 := by
    intro y
    have hg : ContinuousWithinAt (fun θ : ℝ => UnforcedLeray.B0223.heatC θ y) (Ici 0)
        (h * (Real.exp 0 - 1)) :=
      UnforcedLeray.B0223.heatC_continuousOn y _ (by simp)
    have hf : Continuous (fun r : ℝ => h * (Real.exp r - 1)) := by fun_prop
    have hmaps : MapsTo (fun r : ℝ => h * (Real.exp r - 1)) (Ici 0) (Ici 0) := by
      intro r hr
      exact mul_nonneg hh (sub_nonneg.2 (Real.one_le_exp hr))
    exact ContinuousWithinAt.comp (x := (0 : ℝ)) (f := fun r : ℝ => h * (Real.exp r - 1))
      hg hf.continuousWithinAt hmaps
  -- strong continuity of the phase translation at 0 (on the whole line)
  have hTC : ∀ y : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period,
      Continuous fun t : ℝ => UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) t y :=
    fun y => odTransCont p.period y
  -- Step A: right derivative of r ↦ heatC(h(e^r-1)) (dilN(e^{-r/2}) Ψ) at 0
  have hA : HasDerivWithinAt
      (fun r : ℝ => UnforcedLeray.B0223.heatC (h * (Real.exp r - 1))
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ))
      ((h : ℂ) • ΨΔ + (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)) (Ici 0) 0 := by
    have hHD : HasDerivWithinAt
        (fun r : ℝ => UnforcedLeray.B0223.heatC (h * (Real.exp r - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-0 / 2)) Ψ))
        ((h : ℂ) • ΨΔ) (Ici 0) 0 := by
      rw [hx10]
      exact odHeatDeriv p ψ hψ Ψ ΨΔ hΨ hΨΔ h hh
    have hDD : HasDerivWithinAt
        (fun r : ℝ => UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ)
        (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx) (Ici 0) 0 :=
      (odDilDeriv p ψ hψ Ψ Ψx hΨ hΨx).hasDerivWithinAt
    have key := odProdRule (Ici 0) 1
      (fun r : ℝ => UnforcedLeray.B0223.heatC (h * (Real.exp r - 1)))
      (fun r : ℝ => UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ)
      ((h : ℂ) • ΨΔ) (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)
      (fun r _ => UnforcedLeray.B0223.norm_heatC_le _)
      (fun y => hcontH y) hHD hDD
    have e0 : UnforcedLeray.B0223.heatC (h * (Real.exp 0 - 1))
        (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx)
        = -(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx := by
      rw [Real.exp_zero, sub_self, mul_zero, UnforcedLeray.B0223.heatC_of_nonpos le_rfl]
    rw [e0] at key
    exact key
  -- Step B: multiply by the phase translation transC(-r)
  have hTD0 : HasDerivWithinAt
      (fun r : ℝ => UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r)
        (UnforcedLeray.B0223.heatC (h * (Real.exp 0 - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-0 / 2)) Ψ)))
      Ψτ (Ici 0) 0 := by
    rw [hT0]
    exact (odTransDeriv p ψ hψ Ψ Ψτ hΨ hΨτ).hasDerivWithinAt
  have hB : HasDerivWithinAt
      (fun r : ℝ => UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r)
        (UnforcedLeray.B0223.heatC (h * (Real.exp r - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ)))
      (Ψτ + ((h : ℂ) • ΨΔ + (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx))) (Ici 0) 0 := by
    have key := odProdRule (Ici 0) 1
      (fun r : ℝ => (UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC)
        (P := p.period) (-r)).toContinuousLinearMap)
      (fun r : ℝ => UnforcedLeray.B0223.heatC (h * (Real.exp r - 1))
        (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ))
      Ψτ ((h : ℂ) • ΨΔ + (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx))
      (fun r _ => LinearIsometry.norm_toContinuousLinearMap_le _)
      (fun y => ((hTC y).comp continuous_neg).continuousWithinAt) hTD0 hA
    refine HasDerivWithinAt.congr_deriv key ?_
    simp [UnforcedLeray.B0223.transC_zero]
  -- Step C: scalar factor e^{-r/4}
  have hE : HasDerivAt (fun r : ℝ => Real.exp (-r / 4)) (-(1 / 4 : ℝ)) 0 := by
    have h1 : HasDerivAt (fun r : ℝ => -r / 4) (-(1 / 4 : ℝ)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).neg.div_const 4).congr_deriv (by norm_num)
    simpa using h1.exp
  have hEc : HasDerivAt (fun r : ℝ => ((Real.exp (-r / 4) : ℝ) : ℂ))
      ((-(1 / 4 : ℝ) : ℝ) : ℂ) 0 :=
    hE.ofReal_comp
  have hS := HasDerivWithinAt.smul hEc.hasDerivWithinAt hB
  -- identify the function with outerTransp
  have hfun : (fun r : ℝ => outerTransp h r Ψ) = (fun y : ℝ =>
      ((Real.exp (-y / 4) : ℝ) : ℂ) • UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-y)
        (UnforcedLeray.B0223.heatC (h * (Real.exp y - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-y / 2)) Ψ))) := by
    funext r
    unfold outerTransp
    rw [hexp r]
  have hS' : HasDerivWithinAt (fun y : ℝ =>
      ((Real.exp (-y / 4) : ℝ) : ℂ) • UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-y)
        (UnforcedLeray.B0223.heatC (h * (Real.exp y - 1))
          (UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-y / 2)) Ψ)))
      _ (Ici 0) 0 := hS
  rw [hfun, hRep]
  refine HasDerivWithinAt.congr_deriv hS' ?_
  rw [hT0]
  simp only [neg_zero, UnforcedLeray.B0223.transC_zero, zero_div, Real.exp_zero,
    Complex.ofReal_one, one_smul]
  push_cast
  module

end UnforcedLeray.Short.PartIIIb.NearInst
