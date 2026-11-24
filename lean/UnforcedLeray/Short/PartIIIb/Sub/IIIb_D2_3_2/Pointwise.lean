import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw6

/-!
# `WardPointwiseIdentity` from the six leaf identities (source 4225-4258)

Source: `the November 2 reference manuscript`.
Product rule (4228-4231), convection cancellation (4232-4236), pressure identity (4237-4240),
and the divergence bookkeeping (4258) combine by linear algebra on the pointwise values.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Bracket is affine in its first argument, for a difference with a negated term. -/
theorem pwp_br_negsub (A B X : Space → Space) (y : Space)
    (hA : DifferentiableAt ℝ A y) (hB : DifferentiableAt ℝ B y) :
    physBracket (fun z => -(A z) - B z) X y = -(physBracket A X y) - physBracket B X y := by
  have hfd : fderiv ℝ (fun z => -(A z) - B z) y = -(fderiv ℝ A y) - fderiv ℝ B y := by
    have hA' : DifferentiableAt ℝ (fun z => -(A z)) y := hA.neg
    rw [fderiv_fun_sub hA' hB, fderiv_fun_neg]
  unfold physBracket
  rw [hfd]
  simp only [map_sub, map_neg, sub_apply, neg_apply]
  abel

/-- The bracket of smooth fields is smooth. -/
theorem pwp_br_smo (A B : Space → Space) (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physBracket A B) := by
  unfold physBracket
  exact ((smo_fderiv hB).clm_apply hA).sub ((smo_fderiv hA).clm_apply hB)

/-- The gradient of a smooth scalar is smooth. -/
theorem pwp_grad_smo (q : Space → ℝ) (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physGrad q) := by
  have hfun : physGrad q = fun z => ∑ j : Fin 3,
      fderiv ℝ q z (coordinateVector j) • coordinateVector j := by
    funext z
    refine (pw3_sum_coord (physGrad q z)).trans (Finset.sum_congr rfl fun j _ => ?_)
    simp [physGrad]
  rw [hfun]
  exact ContDiff.sum fun j _ =>
    (((smo_fderiv hq).clm_apply contDiff_const).smul contDiff_const)

/-- **Pointwise Ward identity** (source 4225-4282), assembled from the six leaves. -/
theorem wardPointwiseIdentity_proved (ν μ : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    WardPointwiseIdentity ν μ U p := by
  intro P hP X hXs hdiv τ y
  have hUτ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U τ) :=
    pw1_smo_slice (F := U) hP.smoothU τ
  have hXτ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X τ) :=
    pw1_smo_slice (F := X) hXs τ
  have hpτ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p τ) :=
    hP.smoothP.comp (contDiff_const.prodMk contDiff_id)
  have hNd : DifferentiableAt ℝ (fun z => fderiv ℝ (U τ) z (U τ z)) y :=
    smo_diff ((smo_fderiv hUτ).clm_apply hUτ) y
  have hGd : DifferentiableAt ℝ (physGrad (p τ)) y :=
    smo_diff (pwp_grad_smo (p τ) hpτ) y
  have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physBracket (U τ) (X τ)) :=
    pwp_br_smo _ _ hUτ hXτ
  have hYs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physDmu ν (μ + 1) X τ) := by
    have e : physDmu ν (μ + 1) X τ = fun z => deriv (fun t => X t z) τ -
        (1 / 2 : ℝ) • fderiv ℝ (X τ) z z - ν • physLap (X τ) z + ((μ + 1) - 1 / 2) • X τ z :=
      rfl
    rw [e]
    exact (((pw1_smo_dt hXs τ).sub (((pw1_smo_E hXτ)).const_smul (1 / 2 : ℝ))).sub
      ((pw1_smo_lap hXτ).const_smul ν)).add (hXτ.const_smul ((μ + 1) - 1 / 2))
  have hfun : physDmu ν 0 U τ = fun z => -(fderiv ℝ (U τ) z (U τ z)) - physGrad (p τ) z := by
    funext z
    linear_combination (norm := module) hP.equation τ z
  have hA0 : physBracket (physDmu ν 0 U τ) (X τ) y =
      -(physBracket (fun z => fderiv ℝ (U τ) z (U τ z)) (X τ) y) -
        physBracket (physGrad (p τ)) (X τ) y := by
    rw [hfun]
    exact pwp_br_negsub (fun z => fderiv ℝ (U τ) z (U τ z)) (physGrad (p τ)) (X τ) y hNd hGd
  have hP1 := pwProduct_proved ν μ U X hP.smoothU hXs τ y
  have hPr := pwPressure_proved (X τ) (p τ) hXτ hpτ y
  have hCv := pwConvection_proved (U τ) (X τ) hUτ hXτ y
  have hDSh := pwDivSym_proved (U τ) (physBracket (U τ) (X τ)) hUτ hhs (hP.div_free τ)
    (pwBracketDivFree_proved (U τ) (X τ) hUτ hXτ (hP.div_free τ) (hdiv τ)) y
  have hDSY := pwDivSym_proved (U τ) (physDmu ν (μ + 1) X τ) hUτ hYs (hP.div_free τ)
    (pwDmuDivFree_proved ν (μ + 1) X hXs hdiv τ) y
  have hBr : physBracket (U τ) (physDmu ν (μ + 1) X τ) y =
      fderiv ℝ (physDmu ν (μ + 1) X τ) y (U τ y) - fderiv ℝ (U τ) y (physDmu ν (μ + 1) X τ y) :=
    rfl
  have hRes : physResidual ν μ U p X τ y =
      (2 : ℝ) • fderiv ℝ (physDmu ν (μ + 1) X τ) y (U τ y) - (2 * ν) • physCdiff (U τ) (X τ) y +
        physUUD2 (U τ) (X τ) y - physDXp (X τ) (p τ) y :=
    rfl
  linear_combination (norm := module) hP1 + hA0 + hPr + hCv + hDSh + hDSY + hBr - hRes

end UnforcedLeray.Short.PartIIIb.Concrete
