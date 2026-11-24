import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPeriodic

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/6`: calculus of the stream potential

Target (`Sub/T18_3_1_1.lean`): `DfcPotentialFormulas`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552.

With `P = ∫_{-c/2}^q φ₁` and `θ = -P + c⁻¹ ∫_{-c/2}^{c/2} P dq`, under `∫ φ₁ dq = 0`:
smoothness from `DfcQPrimSmooth`, periodicity from `DfcQPeriodic`, `∂_q θ = -φ₁` from
`DfcQPrimDeriv`, and `∂_η θ = φ₀ - c⁻¹ ∫ φ₀ dq` from `∂_η P = -(φ₀(q,η) - φ₀(-c/2,η))` (fundamental
theorem of calculus applied to `∂_q φ₀` and divergence freeness).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem dfcPotentialFormulas : UnforcedLeray.Short.IIIa.DfcPotentialFormulas := by
  unfold DfcPotentialFormulas
  intro c hc φ hφ hM
  have hc0 : c ≠ 0 := hc.ne'
  have hf1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => φ x 1) := hφ.smooth 1
  have hf0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => φ x 0) := hφ.smooth 0
  have hP : ContDiff ℝ ∞ (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) :=
    (dfcQPrimSmooth c hc _ hf1).1
  have hQP : ContDiff ℝ ∞ (dfcQInt c (dfcQPrim c (fun x : ℝ × ℝ => φ x 1))) :=
    (dfcQPrimSmooth c hc _ hP).2
  have hPd : Differentiable ℝ (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) :=
    hP.differentiable (by simp)
  have hQd : Differentiable ℝ (dfcQInt c (dfcQPrim c (fun x : ℝ × ℝ => φ x 1))) :=
    hQP.differentiable (by simp)
  have hθ : ContDiff ℝ ∞ (dfcPotential c φ) := by
    unfold dfcPotential
    exact hP.neg.add (contDiff_const.mul (hQP.comp contDiff_snd))
  -- periodicity
  have hper : ∀ x : ℝ × ℝ, dfcPotential c φ (x.1 + c, x.2) = dfcPotential c φ x := by
    intro x
    have hPer := (dfcQPeriodic c hc _ hf1 (fun x => hφ.periodic x 1)).2 hM x
    unfold dfcPotential
    dsimp only
    rw [hPer]
  -- slice derivative of `φ₀`
  have hpd0cont : Continuous (fun x : ℝ × ℝ => B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) x) :=
    (hf0.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcont0 : ∀ η : ℝ, Continuous (fun t : ℝ => B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) (t, η)) :=
    fun η => hpd0cont.comp (continuous_id.prodMk continuous_const)
  have hslope0 : ∀ η t : ℝ, HasDerivAt (fun s : ℝ => φ (s, η) 0)
      (B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) (t, η)) t := by
    intro η t
    have h1 : HasFDerivAt (fun y : ℝ × ℝ => φ y 0) (fderiv ℝ (fun y : ℝ × ℝ => φ y 0) (t, η))
        ((fun s : ℝ => (s, η)) t) :=
      ((hf0.differentiable (by simp)) (t, η)).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (s, η)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t η)
    exact h1.comp_hasDerivAt t h2
  -- `∂_η` of the primitive of `φ₁`
  have hint : ∀ (t η : ℝ), B0579.pd 1 (fun x : ℝ × ℝ => φ x 1) (t, η) =
      -(B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) (t, η)) := by
    intro t η
    have := hφ.divFree (t, η)
    linarith
  have hPd1 : ∀ s η : ℝ, B0579.pd 1 (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) (s, η) =
      -(φ (s, η) 0 - φ (-(c / 2), η) 0) := by
    intro s η
    rw [(dfcQPrimDeriv c hc _ hf1).2.1 (s, η)]
    have hF : ∫ t in (-(c / 2))..s, B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) (t, η) =
        φ (s, η) 0 - φ (-(c / 2), η) 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => φ (t, η) 0)
        (f' := fun t : ℝ => B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) (t, η))
        (fun t _ => hslope0 η t) ((hcont0 η).intervalIntegrable _ _)
    have e := intervalIntegral.integral_congr (μ := volume)
      (a := -(c / 2)) (b := s)
      (f := fun t : ℝ => B0579.pd 1 (fun x : ℝ × ℝ => φ x 1) (t, η))
      (g := fun t : ℝ => -(B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) (t, η)))
      (fun t _ => hint t η)
    show ∫ t in (-(c / 2))..s, B0579.pd 1 (fun x : ℝ × ℝ => φ x 1) (t, η) = _
    rw [e, intervalIntegral.integral_neg, hF]
  have hQdη : ∀ η : ℝ, deriv (dfcQInt c (dfcQPrim c (fun x : ℝ × ℝ => φ x 1))) η =
      -(dfcQInt c (fun y : ℝ × ℝ => φ y 0) η) + c * φ (-(c / 2), η) 0 := by
    intro η
    rw [(dfcQPrimDeriv c hc _ hP).2.2 η]
    have hcont0' : Continuous (fun t : ℝ => φ (t, η) 0) :=
      hf0.continuous.comp (continuous_id.prodMk continuous_const)
    unfold dfcQInt
    simp only [hPd1]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_sub (hcont0'.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  refine ⟨hθ, hper, ?_, ?_⟩
  · rintro ⟨q, η⟩
    rw [DfcQPrimDerivAux.pd0_eq _ q η ((hθ.differentiable (by simp)) (q, η))]
    have hPs : HasDerivAt (fun s : ℝ => dfcQPrim c (fun x : ℝ × ℝ => φ x 1) (s, η))
        (B0579.pd 0 (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) (q, η)) q := by
      have h1 := (hPd (q, η)).hasFDerivAt.comp_hasDerivAt q
        ((hasDerivAt_id q).prodMk (hasDerivAt_const q η))
      exact h1
    have hpd : B0579.pd 0 (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) (q, η) = φ (q, η) 1 :=
      (dfcQPrimDeriv c hc _ hf1).1 (q, η)
    rw [hpd] at hPs
    exact (hPs.neg.add_const (c⁻¹ * dfcQInt c (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) η)).deriv
  · rintro ⟨q, η⟩
    rw [DfcQPrimDerivAux.pd1_eq _ q η ((hθ.differentiable (by simp)) (q, η))]
    have hPt : HasDerivAt (fun t : ℝ => dfcQPrim c (fun x : ℝ × ℝ => φ x 1) (q, t))
        (B0579.pd 1 (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) (q, η)) η :=
      (hPd (q, η)).hasFDerivAt.comp_hasDerivAt η
        ((hasDerivAt_const η q).prodMk (hasDerivAt_id η))
    have hQt : HasDerivAt (fun t : ℝ => dfcQInt c (dfcQPrim c (fun x : ℝ × ℝ => φ x 1)) t)
        (deriv (dfcQInt c (dfcQPrim c (fun x : ℝ × ℝ => φ x 1))) η) η :=
      (hQd η).hasDerivAt
    have h := (hPt.neg).add (hQt.const_mul c⁻¹)
    have hsl : HasDerivAt (fun t : ℝ => dfcPotential c φ (q, t))
        (φ (q, η) 0 - c⁻¹ * dfcQInt c (fun y : ℝ × ℝ => φ y 0) η) η := by
      refine h.congr_deriv ?_
      rw [hPd1 q η, hQdη η, mul_add, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      ring
    exact hsl.deriv

end UnforcedLeray.Short.IIIa
