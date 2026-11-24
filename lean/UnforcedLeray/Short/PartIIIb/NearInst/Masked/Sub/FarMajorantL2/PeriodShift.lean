import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Period shift for `FarMajorantL2` (source 4002-4003)

Shift invariance over one period of a measurable periodic `ℝ≥0∞`-valued function.
Proof: an integral over a period window `[a, a+P)` is the integral over `AddCircle P` of the
lift, by `AddCircle.lintegral_preimage`; the shifted function lifts to the translate of the lift,
and the Haar measure of `AddCircle P` is translation invariant.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem periodShift_holds : PeriodShift := by
  intro h P a σ hP _hmeas hper
  have : Fact (0 < P) := ⟨hP⟩
  have hp : Function.Periodic h P := hper
  have hk : Function.Periodic (fun τ => h (τ + σ)) P := fun τ => by
    show h (τ + P + σ) = h (τ + σ)
    rw [add_right_comm]
    exact hp (τ + σ)
  -- window formula: the integral over `[a, a+P)` is the integral over the circle of the lift
  have window : ∀ (g : ℝ → ℝ≥0∞) (hg : Function.Periodic g P),
      ∫⁻ τ in Ico a (a + P), g τ = ∫⁻ x : AddCircle P, hg.lift x := by
    intro g hg
    rw [← AddCircle.lintegral_preimage P a hg.lift]
    rw [setLIntegral_congr (Ico_ae_eq_Ioc : Ico a (a + P) =ᵐ[volume] Ioc a (a + P))]
    rfl
  have e1 : ∫⁻ τ in Ico a (a + P), h (τ + σ) = ∫⁻ x : AddCircle P, hk.lift x :=
    window (fun τ => h (τ + σ)) hk
  have e2 : ∫⁻ τ in Ico a (a + P), h τ = ∫⁻ x : AddCircle P, hp.lift x :=
    window h hp
  rw [e1, e2]
  have hl : ∀ x : AddCircle P, hk.lift x = hp.lift (x + (σ : AddCircle P)) := by
    intro x
    obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← AddCircle.coe_add]
    rfl
  refine (lintegral_congr hl).trans ?_
  exact lintegral_add_right_eq_self (fun x : AddCircle P => hp.lift x) (σ : AddCircle P)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
