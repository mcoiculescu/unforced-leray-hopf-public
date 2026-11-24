import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The planar Laplacian of a cylinder test is a cylinder test (local copy of
`isCylTest_lapP`). -/
theorem co_isCylTest_lapP {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (lapP ψ) := by
  unfold lapP
  have h1 := (hψ.pd 0).pd 0
  have h2 := (hψ.pd 1).pd 1
  refine ⟨h1.smooth.add h2.smooth, fun x => ?_, ?_⟩
  · simp only [h1.periodic x, h2.periodic x]
  · obtain ⟨R, hR⟩ := h1.band
    obtain ⟨R', hR'⟩ := h2.band
    refine ⟨max R R', fun x hx => ?_⟩
    have := hR x (lt_of_le_of_lt (le_max_left _ _) hx)
    have := hR' x (lt_of_le_of_lt (le_max_right _ _) hx)
    simp [*]

/-- **The coefficient of the adjoint Volterra problem** (SP 2819-2836, 3052-3060): the transport
coefficient `Mv` and the localized interaction `K` assemble into one bounded, strongly continuous
family `A(r) w = (-v(r) w, -K_c^T(w∇E(r)))`, and the tested adjoint right-hand side splits as
`ν ∫ w Δψ + ∫ A₁ ∂ψ + ∫ A₂ ψ`. -/
theorem adjCoeffExists_of (m : ℝ) (hT : AdjTransportCoeff m) (hL : AdjLocalizedCoeff m)
    (hP : AdjPairing) : AdjCoeffExists m := by
  intro ν hν hν1 tr T C hT0 hC
  obtain ⟨Mv, hMvB, hMvCont, hMvEq⟩ := hT ν hν tr T C hT0 hC
  obtain ⟨K, βK, hKB, hKCont, hKEq⟩ := hL ν hν hν1 tr T C hT0 hC
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  let A : ℝ → AdjX (ν ^ (-2 : ℝ)) m →L[ℂ] AdjY (ν ^ (-2 : ℝ)) m := fun r =>
    (ContinuousLinearMap.pi fun j => Mv r j).prod (-(K r))
  refine ⟨A, |C| + |βK|, ?_, ?_, ?_⟩
  · -- uniform bound
    intro r hr
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      show ‖Mv r j w‖ ≤ _
      have h1 : ‖Mv r j w‖ ≤ ‖Mv r j‖ * ‖w‖ := (Mv r j).le_opNorm w
      have h2 : ‖Mv r j‖ ≤ |C| + |βK| :=
        ((hMvB r hr j).trans (le_abs_self C)).trans (by linarith [abs_nonneg βK])
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    · show ‖-(K r w)‖ ≤ _
      rw [norm_neg]
      have h1 : ‖K r w‖ ≤ ‖K r‖ * ‖w‖ := (K r).le_opNorm w
      have h2 : ‖K r‖ ≤ |C| + |βK| :=
        ((hKB r hr).trans (le_abs_self βK)).trans (by linarith [abs_nonneg C])
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  · -- strong continuity
    intro w
    have h1 : ContinuousOn (fun r => fun j => Mv r j w) (Icc 0 T) :=
      continuousOn_pi.2 fun j => hMvCont j w
    have h2 : ContinuousOn (fun r => -(K r w)) (Icc 0 T) := (hKCont w).neg
    exact h1.prodMk h2
  · -- the identity
    intro r hr w ψ uψ hψ huψ
    obtain ⟨hKint, hKid⟩ := hKEq r hr w ψ uψ hψ huψ
    have hILap : IntegrableOn (fun x => w x * (lapP ψ x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      (hP _ m hc (lapP ψ) (co_isCylTest_lapP hψ)).1 w
    have hI0 : IntegrableOn (fun x => (A r w).1 0 x * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      (hP _ m hc (B0579.pd 0 ψ) (hψ.pd 0)).1 _
    have hI1 : IntegrableOn (fun x => (A r w).1 1 x * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      (hP _ m hc (B0579.pd 1 ψ) (hψ.pd 1)).1 _
    have hI2 : IntegrableOn (fun x => (A r w).2 x * (ψ x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      (hP _ m hc ψ hψ).1 _
    -- the transport part, a.e. on the cell
    have hae0 : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
        (A r w).1 0 x = -((tr.v r x 0 : ℝ) : ℂ) * w x :=
      (B0579.ac_cellMeasure (ν ^ (-2 : ℝ)) (-m)).ae_le (hMvEq r hr 0 w)
    have hae1 : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
        (A r w).1 1 x = -((tr.v r x 1 : ℝ) : ℂ) * w x :=
      (B0579.ac_cellMeasure (ν ^ (-2 : ℝ)) (-m)).ae_le (hMvEq r hr 1 w)
    have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
        adjIntegrand tr (⇑w) r ψ uψ x =
          (((ν : ℂ) * (w x * (lapP ψ x : ℂ))) +
            ((A r w).1 0 x * (B0579.pd 0 ψ x : ℂ) + (A r w).1 1 x * (B0579.pd 1 ψ x : ℂ))) +
          -(w x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) := by
      filter_upwards [hae0, hae1] with x h0 h1
      rw [h0, h1]
      unfold adjIntegrand
      push_cast
      ring
    -- the adjoint term `A₂ ψ = -K_c(w)ψ`
    have hneg : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
        (A r w).2 x = -(K r w x) :=
      (B0579.ac_cellMeasure (ν ^ (-2 : ℝ)) (-m)).ae_le (Lp.coeFn_neg (K r w))
    have hA2 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (A r w).2 x * (ψ x : ℂ) =
        -∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          w x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
            uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) := by
      calc ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (A r w).2 x * (ψ x : ℂ)
          = ∫ x in B0579.cell (ν ^ (-2 : ℝ)), -((K r w) x * (ψ x : ℂ)) :=
            integral_congr_ae (hneg.mono fun x hx => by simp only [hx, neg_mul])
        _ = -∫ x in B0579.cell (ν ^ (-2 : ℝ)), (K r w) x * (ψ x : ℂ) := integral_neg _
        _ = _ := by rw [hKid]
    -- integrability of the three pieces
    have hF1 : IntegrableOn (fun x => (ν : ℂ) * (w x * (lapP ψ x : ℂ)))
        (B0579.cell (ν ^ (-2 : ℝ))) := Integrable.const_mul hILap _
    have hF2 : IntegrableOn (fun x => (A r w).1 0 x * (B0579.pd 0 ψ x : ℂ) +
        (A r w).1 1 x * (B0579.pd 1 ψ x : ℂ)) (B0579.cell (ν ^ (-2 : ℝ))) :=
      Integrable.add hI0 hI1
    have hF12 : IntegrableOn (fun x => (ν : ℂ) * (w x * (lapP ψ x : ℂ)) +
        ((A r w).1 0 x * (B0579.pd 0 ψ x : ℂ) + (A r w).1 1 x * (B0579.pd 1 ψ x : ℂ)))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      Integrable.add hF1 hF2
    have hF3 : IntegrableOn (fun x => -(w x * ((uψ x 0 * B0579.pd 0
        (UnforcedLeray.B0238.Ec tr r) x + uψ x 1 * B0579.pd 1
        (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)))
        (B0579.cell (ν ^ (-2 : ℝ))) := Integrable.neg hKint
    refine ⟨?_, ?_⟩
    · exact Integrable.congr (Integrable.add hF12 hF3) (hae.mono fun x hx => hx.symm)
    · rw [integral_congr_ae hae, integral_add hF12 hF3, integral_add hF1 hF2,
        integral_const_mul, integral_add hI0 hI1, integral_neg, hA2]
      ring

end UnforcedLeray.Short.IIIa
