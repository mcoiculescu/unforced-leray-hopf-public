import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs

/-!
# Continuity of the pressure gradient (source 4138-4141)

The pressure is smooth on `ℝ × ℝ³` (`IsExactProfile.smoothP`, source 4138-4141), so its
spatial gradient is jointly continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **The pressure gradient is jointly continuous** (source 4138-4141). -/
theorem presGradCont_proved : PresGradCont := by
  intro ν P U pres hU
  set F : ℝ × Space → ℝ := fun x => pres x.1 x.2 with hF
  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hU.smoothP
  have hdiff : Differentiable ℝ F := hC.differentiable (by simp)
  have hfd : ∀ (τ : ℝ) (y v : Space), fderiv ℝ (pres τ) y v = fderiv ℝ F (τ, y) (0, v) := by
    intro τ y v
    have hF' : HasFDerivAt F (fderiv ℝ F (τ, y)) (τ, y) := (hdiff (τ, y)).hasFDerivAt
    have hg : HasFDerivAt (fun y' : Space => ((τ, y') : ℝ × Space))
        (ContinuousLinearMap.inr ℝ ℝ Space) y :=
      hasFDerivAt_prodMk_right τ y
    have hc := hF'.comp y hg
    have hpres : pres τ = F ∘ (fun y' : Space => ((τ, y') : ℝ × Space)) := rfl
    rw [hpres, hc.fderiv]
    rfl
  have hcont : Continuous fun x : ℝ × Space => fderiv ℝ F x :=
    hC.continuous_fderiv (by simp)
  have hpart : ∀ j : Fin 3, Continuous fun x : ℝ × Space => fderiv ℝ F x (0, coordinateVector j) :=
    fun j => hcont.clm_apply continuous_const
  unfold physGrad
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun j => ?_)
  show Continuous fun x : ℝ × Space => fderiv ℝ (pres x.1) x.2 (coordinateVector j)
  have hEq : (fun x : ℝ × Space => fderiv ℝ (pres x.1) x.2 (coordinateVector j)) =
      fun x => fderiv ℝ F x (0, coordinateVector j) :=
    funext fun x => hfd x.1 x.2 _
  rw [hEq]
  exact hpart j

end UnforcedLeray.Short.PartIIIb.Concrete
