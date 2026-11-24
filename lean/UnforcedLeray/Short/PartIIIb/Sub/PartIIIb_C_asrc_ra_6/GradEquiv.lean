import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6

/-!
# `PartIII-b:C/asrc/ra/6/4` : `∇q` commutes with linear isometries for invariant scalars

Source of record: `the November 2 reference manuscript` (PhysLayer 107).

If `q ∘ g = q` then `fderiv q (g y) (g x) = fderiv q y x`, so the Riesz vector `(∂_j q)_j` is
`g`-equivariant. No differentiability is needed: both sides vanish when `q` is not differentiable,
and differentiability transfers along `g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem raG_hasFDerivAt (g : Space ≃ₗᵢ[ℝ] Space) (y : Space) :
    HasFDerivAt (fun z : Space => g z) (g.toContinuousLinearEquiv : Space →L[ℝ] Space) y :=
  (g.toContinuousLinearEquiv).hasFDerivAt

theorem raG_expand (u : Space) : u = ∑ k : Fin 3, u k • coordinateVector k := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector, EuclideanSpace.single_apply]

theorem raG_coord (x : Space) (k : Fin 3) : inner ℝ (coordinateVector k) x = x k := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

theorem raG_diff (g : Space ≃ₗᵢ[ℝ] Space) (q : Space → ℝ) (hq : ∀ z, q (g z) = q z) (w : Space)
    (hw : DifferentiableAt ℝ q w) : DifferentiableAt ℝ q (g w) := by
  have e : (fun z => q (g z)) = q := funext hq
  have h1 : DifferentiableAt ℝ (fun z => q (g z)) (g.symm (g w)) := by
    rw [LinearIsometryEquiv.symm_apply_apply, e]
    exact hw
  have h2 := h1.comp (g w) (raG_hasFDerivAt g.symm (g w)).differentiableAt
  have e2 : (fun z => q (g z)) ∘ (⇑g.symm) = q := by
    funext z
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [e2] at h2
  exact h2

theorem raG_fderiv_comp (g : Space ≃ₗᵢ[ℝ] Space) (q : Space → ℝ) (hq : ∀ z, q (g z) = q z)
    (y x : Space) : fderiv ℝ q (g y) (g x) = fderiv ℝ q y x := by
  by_cases hd : DifferentiableAt ℝ q y
  · have hd' : DifferentiableAt ℝ q (g y) := raG_diff g q hq y hd
    have hq' : (fun z => q (g z)) = q := funext hq
    have h1 : HasFDerivAt (fun z => q (g z))
        ((fderiv ℝ q (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space)) y :=
      hd'.hasFDerivAt.comp y (raG_hasFDerivAt g y)
    have h2 : HasFDerivAt (fun z => q (g z)) (fderiv ℝ q y) y := by
      rw [hq']
      exact hd.hasFDerivAt
    have h3 := h1.unique h2
    have h4 := congrArg (fun L : Space →L[ℝ] ℝ => L x) h3
    simpa using h4
  · have hsym : ∀ z, q (g.symm z) = q z := fun z => by
      have h := hq (g.symm z)
      simp only [LinearIsometryEquiv.apply_symm_apply] at h
      exact h.symm
    have hd' : ¬ DifferentiableAt ℝ q (g y) := fun h => hd (by
      have := raG_diff g.symm q hsym (g y) h
      simpa using this)
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']
    simp

theorem physGradEquiv : PhysGradEquiv := by
  intro g q hq y
  ext j
  have hL : fderiv ℝ q (g y) (coordinateVector j) = fderiv ℝ q y (g.symm (coordinateVector j)) := by
    rw [← raG_fderiv_comp g q hq y (g.symm (coordinateVector j)),
      LinearIsometryEquiv.apply_symm_apply]
  have hsym : ∀ k : Fin 3, (g.symm (coordinateVector j)) k = (g (coordinateVector k)) j := by
    intro k
    calc (g.symm (coordinateVector j)) k
        = inner ℝ (coordinateVector k) (g.symm (coordinateVector j)) := (raG_coord _ _).symm
      _ = inner ℝ (g (coordinateVector k)) (g (g.symm (coordinateVector j))) :=
          (g.inner_map_map _ _).symm
      _ = inner ℝ (g (coordinateVector k)) (coordinateVector j) := by
          rw [LinearIsometryEquiv.apply_symm_apply]
      _ = (g (coordinateVector k)) j := by
          rw [real_inner_comm]
          exact raG_coord _ _
  have hxexp : fderiv ℝ q y (g.symm (coordinateVector j)) =
      ∑ k : Fin 3, (g.symm (coordinateVector j)) k * fderiv ℝ q y (coordinateVector k) := by
    conv_lhs => rw [raG_expand (g.symm (coordinateVector j))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
  have hR : (g (physGrad q y)) j =
      ∑ k : Fin 3, (physGrad q y) k * (g (coordinateVector k)) j := by
    conv_lhs => rw [raG_expand (physGrad q y)]
    simp [map_sum, map_smul]
  show fderiv ℝ q (g y) (coordinateVector j) = (g (physGrad q y)) j
  rw [hL, hxexp, hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsym k]
  change _ * _ = fderiv ℝ q y (coordinateVector k) * _
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
