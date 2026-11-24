import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)

/-! Helpers for `phaseSolenoidalOfPointwise_of` (source 4240-4258): on each phase slice the
pairing `∫ ∇_y φ · w dy` is an integration by parts against the divergence of `w`. -/

/-- The spatial derivative of the phase slice is the `(0, e_j)` derivative of `φ`. -/
theorem pst_fderiv_slice {φ : ℝ × Space → ℂ} (hφ : Differentiable ℝ φ) (τ : ℝ) (y v : Space) :
    fderiv ℝ φ (τ, y) (0, v) = fderiv ℝ (fun y' => φ (τ, y')) y v := by
  have hs : HasFDerivAt (fun y' : Space => ((τ, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    hasFDerivAt_prodMk_right τ y
  have hc : HasFDerivAt (fun y' : Space => φ (τ, y'))
      ((fderiv ℝ φ (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    (hφ (τ, y)).hasFDerivAt.comp y hs
  rw [hc.fderiv]
  rfl

/-- The component of the slice derivative is the component of the vector derivative. -/
theorem pst_comp_fderiv {w : ℝ × Space → CVec3} (τ : ℝ)
    (hw : ContDiff ℝ 1 (fun y => w (τ, y))) (j : Fin 3) (y v : Space) :
    fderiv ℝ (fun y' => w (τ, y') j) y v = fderiv ℝ (fun y' => w (τ, y')) y v j := by
  have hd : DifferentiableAt ℝ (fun y' => w (τ, y')) y := (hw.differentiable (by norm_num)) y
  have hl : HasFDerivAt (fun y' => (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ) (w (τ, y')))
      (((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp
        (fderiv ℝ (fun y' => w (τ, y')) y)) y :=
    ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp y
      hd.hasFDerivAt
  have hfun : (fun y' => w (τ, y') j) = (fun y' => (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ)
      (w (τ, y'))) := rfl
  rw [hfun, hl.fderiv]
  rfl

/-- On one phase slice, `∫ ⟨∇φ, w⟩ dy = 0` for a divergence-free `w`. -/
theorem pst_slice_zero (P : ℝ) (φ : ℝ × Space → ℂ) (w : ℝ × Space → CVec3)
    (hφ : IsPhaseTest P φ) (τ : ℝ)
    (hw : ContDiff ℝ 1 (fun y => w (τ, y)))
    (hdiv : ∀ y, ∑ j : Fin 3, fderiv ℝ (fun y' => w (τ, y')) y (coordinateVector j) j = 0) :
    ∫ y, dotL (PhaseSpace.gradT φ (τ, y)) (w (τ, y)) = 0 := by
  have hψc : HasCompactSupport (fun y => φ (τ, y)) := hφ.hasCompactSupport_slice τ
  have hψs : ContDiff ℝ ∞ (fun y => φ (τ, y)) :=
    hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψd : Differentiable ℝ (fun y => φ (τ, y)) := hψs.differentiable (by simp)
  have hψcont : Continuous (fun y => φ (τ, y)) := hψd.continuous
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hwd : Differentiable ℝ (fun y => w (τ, y)) := hw.differentiable (by norm_num)
  have hg : ∀ j : Fin 3, ContDiff ℝ 1 (fun y => w (τ, y) j) := fun j =>
    ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hw
  have hgd : ∀ j : Fin 3, Differentiable ℝ (fun y => w (τ, y) j) := fun j =>
    (hg j).differentiable (by norm_num)
  have hgc : ∀ j : Fin 3, Continuous (fun y => w (τ, y) j) := fun j => (hgd j).continuous
  have hψfc : Continuous (fun y => fderiv ℝ (fun y' => φ (τ, y')) y) :=
    hψs.continuous_fderiv (by simp)
  have hgfc : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ (fun y' => w (τ, y') j) y) :=
    fun j => (hg j).continuous_fderiv (by norm_num)
  have hψvc : ∀ v : Space,
      HasCompactSupport (fun y => fderiv ℝ (fun y' => φ (τ, y')) y v) :=
    fun v => hψc.fderiv_apply ℝ v
  have hψvcont : ∀ v : Space, Continuous (fun y => fderiv ℝ (fun y' => φ (τ, y')) y v) :=
    fun v => hψfc.clm_apply continuous_const
  have hgvcont : ∀ j : Fin 3,
      Continuous (fun y => fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j)) :=
    fun j => (hgfc j).clm_apply continuous_const
  have int1 : ∀ j : Fin 3, Integrable (fun y => φ (τ, y) * w (τ, y) j) := fun j => by
    have hcs : HasCompactSupport ((fun y => φ (τ, y)) * (fun y => w (τ, y) j)) :=
      hψc.mul_right
    exact Continuous.integrable_of_hasCompactSupport (hψcont.mul (hgc j)) hcs
  have int2 : ∀ j : Fin 3, Integrable (fun y => φ (τ, y) *
      fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j)) := fun j => by
    have hcs : HasCompactSupport ((fun y => φ (τ, y)) *
        (fun y => fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j))) :=
      hψc.mul_right
    exact Continuous.integrable_of_hasCompactSupport (hψcont.mul (hgvcont j)) hcs
  have int3 : ∀ j : Fin 3, Integrable (fun y =>
      fderiv ℝ (fun y' => φ (τ, y')) y (coordinateVector j) * w (τ, y) j) := fun j => by
    have hcs : HasCompactSupport ((fun y => fderiv ℝ (fun y' => φ (τ, y')) y
        (coordinateVector j)) * (fun y => w (τ, y) j)) :=
      (hψvc (coordinateVector j)).mul_right
    exact Continuous.integrable_of_hasCompactSupport ((hψvcont _).mul (hgc j)) hcs
  have ibp : ∀ j : Fin 3,
      ∫ y, φ (τ, y) * fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j) =
        -∫ y, fderiv ℝ (fun y' => φ (τ, y')) y (coordinateVector j) * w (τ, y) j := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (int3 j) (int2 j) (int1 j)
      (fun y _ => hψd y) (fun y _ => hgd j y)
  have ibp' : ∀ j : Fin 3, ∫ y, fderiv ℝ (fun y' => φ (τ, y')) y (coordinateVector j) *
      w (τ, y) j = -∫ y, φ (τ, y) * fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j) :=
    fun j => by rw [ibp j, neg_neg]
  have hdot : ∀ y, dotL (PhaseSpace.gradT φ (τ, y)) (w (τ, y)) =
      ∑ j : Fin 3, fderiv ℝ (fun y' => φ (τ, y')) y (coordinateVector j) * w (τ, y) j := by
    intro y
    rw [dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← pst_fderiv_slice hφd τ y (coordinateVector i)]
    simp [PhaseSpace.gradT, PhaseSpace.dy, Pi.single_apply]
  have hzero : ∀ y, ∑ j : Fin 3, φ (τ, y) *
      fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j) = 0 := by
    intro y
    rw [← Finset.mul_sum]
    have hs : ∑ j : Fin 3, fderiv ℝ (fun y' => w (τ, y') j) y (coordinateVector j) = 0 :=
      (Finset.sum_congr rfl fun j _ => pst_comp_fderiv τ hw j y _).trans (hdiv y)
    rw [hs, mul_zero]
  simp only [hdot]
  rw [integral_finset_sum _ (fun j _ => int3 j)]
  simp only [ibp']
  rw [Finset.sum_neg_distrib, ← integral_finset_sum _ (fun j _ => int2 j)]
  simp only [hzero, integral_zero, neg_zero]

theorem phaseSolenoidalOfPointwise_of (P : ℝ) : PhaseSolenoidalOfPointwise P := by
  intro w hw hdiv φ hφ
  have hinner : ∀ τ : ℝ, ∫ y, dotL (PhaseSpace.gradT φ (τ, y)) (w (τ, y)) = 0 :=
    fun τ => pst_slice_zero P φ w hφ τ (hw τ) (hdiv τ)
  unfold pairF phaseInt
  simp only [hinner, integral_zero, smul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
