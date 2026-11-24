import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4_4
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `AdjPairCore` from `AdjSpatial` (task `PartIII-b:C/near/pins/3/5/4/4/5`)

Source `the November 2 reference manuscript`:
1339-1362, 3346-3352.

Phase assembly: for each phase `τ` the fixed-phase identity `AdjSpatial` gives the slice
`⟨∇φ(τ,·), c ∫G_a F'(τ-t, c·-w)⟩ = R(τ-t)`, where `R(σ) = ∫ ⟨adjGradT(σ,·), F'(σ,·)⟩`.
`R` is `P`-periodic, so `∫_{(0,P]} R(τ-t) dτ = ∫_{(0,P]} R dτ`.
The slice square-integrability `F'(σ-slice) ∈ L²` holds for a.e. phase by periodicity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0223 (SpaceC X outerS)

/-- The phase-slice pairing `R(σ) = ∫ ⟨adjGradT a t φ (σ,u), F'(σ,u)⟩ du`. -/
def adjR (a t : ℝ) (φ : ℝ × Space → ℂ) (F' : ℝ × Space → CVec3) (σ : ℝ) : ℂ :=
  ∫ u : Space, dotL (adjGradT a t φ (σ, u)) (F' (σ, u))

/-- A `P`-periodic a.e. property on the period window holds a.e. on `ℝ`. -/
theorem ae_all_of_periodic_aux {P : ℝ} (hP : 0 < P) {p : ℝ → Prop}
    (hp : ∀ τ, p (τ + P) ↔ p τ) (h : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), p τ) :
    ∀ᵐ τ, p τ := by
  have hper : Function.Periodic p P := fun τ => propext (hp τ)
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  have hk : ∀ k : ℤ, ∀ᵐ x, x - k * P ∈ Ioc 0 P → p x := by
    intro k
    have h1 := (measurePreserving_sub_right volume ((k : ℝ) * P)).quasiMeasurePreserving.ae h
    filter_upwards [h1] with x hx hmem
    have h2 := hx hmem
    have h3 := hper.int_mul k (x - k * P)
    rw [sub_add_cancel] at h3
    rw [h3]
    exact h2
  filter_upwards [ae_all_iff.2 hk] with x hx
  obtain ⟨m, hm, -⟩ := existsUnique_sub_zsmul_mem_Ioc hP x 0
  rw [zero_add, zsmul_eq_mul] at hm
  exact hx m hm

/-- For a.e. phase `σ`, the slice `F'(σ,·)` is square integrable. -/
theorem ae_slice_sq {P : ℝ} (hP : 0 < P) {F' : ℝ × Space → CVec3}
    (hp : ∀ τ y, F' (τ + P, y) = F' (τ, y))
    (hi : IntegrableOn (fun x : ℝ × Space => ‖F' x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ)) :
    ∀ᵐ σ : ℝ, Integrable (fun u : Space => ‖F' (σ, u)‖ ^ 2) := by
  have e : ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
      ((volume : Measure Space).restrict univ)
      = ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc (0 : ℝ) P ×ˢ univ) :=
    Measure.prod_restrict _ _
  rw [Measure.restrict_univ] at e
  have hint : Integrable (fun x : ℝ × Space => ‖F' x‖ ^ 2)
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
    rw [e]
    exact hi
  have h1 := hint.prod_right_ae
  refine ae_all_of_periodic_aux hP (p := fun σ => Integrable (fun u : Space => ‖F' (σ, u)‖ ^ 2))
    ?_ ?_
  · intro τ
    simp only [hp]
  · filter_upwards [h1] with σ hσ
    exact hσ

/-- The fixed-phase slice identity from `AdjSpatial`. -/
theorem slice_identity (h : AdjSpatial) {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ)
    {a : ℝ} (ha : 0 < a) (t : ℝ) (F' : ℝ × Space → CVec3) (τ : ℝ)
    (hfm : AEStronglyMeasurable (fun u : Space => F' (τ - t, u)) volume)
    (hf : Integrable (fun u : Space => ‖F' (τ - t, u)‖ ^ 2)) :
    ∫ y : Space, dotL (gradT φ (τ, y)) ((Real.exp (t / 2) : ℝ) • ∫ w : Euc 3,
        gaussKernel 3 a w • F' (τ - t, (Real.exp (t / 2) : ℝ) • y - w))
      = adjR a t φ F' (τ - t) := by
  obtain ⟨R, hR⟩ := hφ.gradT.bounded_support
  have hc : Continuous (fun y : Space => gradT φ (τ, y)) :=
    hφ.gradT.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  refine (h a t ha (fun y : Space => gradT φ (τ, y)) (fun u : Space => F' (τ - t, u))
    hc ⟨R, fun y hy => hR τ y hy⟩ hfm hf).trans ?_
  simp only [adjR, adjGradT, sub_add_cancel]

/-- The slice pairing `R` is `P`-periodic. -/
theorem adjR_periodic {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (a t : ℝ)
    (F' : ℝ × Space → CVec3) (hp : ∀ τ y, F' (τ + P, y) = F' (τ, y)) :
    Function.Periodic (adjR a t φ F') P := by
  intro σ
  simp only [adjR, adjGradT, add_right_comm σ P t, hφ.gradT.periodic, hp]

/-- Shifting the period window of a periodic function. -/
theorem shift_periodic {P : ℝ} (hP : 0 < P) {R : ℝ → ℂ} (hR : Function.Periodic R P) (t : ℝ) :
    ∫ τ in Ioc (0 : ℝ) P, R (τ - t) = ∫ τ in Ioc (0 : ℝ) P, R τ := by
  have h1 : ∫ τ in Ioc (0 : ℝ) P, R (τ - t) = ∫ τ in (0 : ℝ)..P, R (τ - t) :=
    (intervalIntegral.integral_of_le hP.le).symm
  have h2 : ∫ τ in Ioc (0 : ℝ) P, R τ = ∫ τ in (0 : ℝ)..P, R τ :=
    (intervalIntegral.integral_of_le hP.le).symm
  rw [h1, h2, intervalIntegral.integral_comp_sub_right, zero_sub]
  have h3 := hR.intervalIntegral_add_eq (-t) 0
  rw [zero_add, show -t + P = P - t by ring] at h3
  exact h3

/-- **Leaf C** (`AdjPairCore`): the phase assembly of the fixed-phase identity `AdjSpatial`. -/
theorem adjPairCore_of_spatial (h : AdjSpatial) : AdjPairCore := by
  intro P hPf a t ha _ φ hφ F' hm hp hi
  have hP : 0 < P := hPf.out
  have hA := ae_slice_sq hP hp hi
  have hB : ∀ᵐ τ : ℝ, Integrable (fun u : Space => ‖F' (τ - t, u)‖ ^ 2) :=
    (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae hA
  have hMa : ∀ᵐ σ : ℝ, AEStronglyMeasurable (fun u : Space => F' (σ, u)) volume :=
    hm.prodMk_left
  have hMb : ∀ᵐ τ : ℝ, AEStronglyMeasurable (fun u : Space => F' (τ - t, u)) volume :=
    (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae hMa
  have hslice : ∀ᵐ τ : ℝ, ∫ y : Space, dotL (gradT φ (τ, y)) ((Real.exp (t / 2) : ℝ) • ∫ w : Euc 3,
        gaussKernel 3 a w • F' (τ - t, (Real.exp (t / 2) : ℝ) • y - w))
      = adjR a t φ F' (τ - t) :=
    (hMb.and hB).mono fun τ hτ => slice_identity h hφ ha t F' τ hτ.1 hτ.2
  have key : ∫ τ in Ioc (0 : ℝ) P, ∫ y : Space, dotL (gradT φ (τ, y))
        ((Real.exp (t / 2) : ℝ) • ∫ w : Euc 3,
          gaussKernel 3 a w • F' (τ - t, (Real.exp (t / 2) : ℝ) • y - w))
      = ∫ τ in Ioc (0 : ℝ) P, adjR a t φ F' τ :=
    (integral_congr_ae (ae_restrict_of_ae hslice)).trans
      (shift_periodic hP (adjR_periodic hφ a t F' hp) t)
  unfold pairF phaseInt
  exact congrArg (fun z : ℂ => P⁻¹ • z) key

end UnforcedLeray.Short.PartIIIb.NearInst
