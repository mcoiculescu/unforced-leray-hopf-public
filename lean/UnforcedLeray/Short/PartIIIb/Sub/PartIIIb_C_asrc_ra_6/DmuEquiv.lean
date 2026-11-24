import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6

/-!
# `PartIII-b:C/asrc/ra/6/2` : `D_μ` commutes with linear isometries

Source of record: `the November 2 reference manuscript` 4140-4141.

`physDmu ν μ X τ (g y) = g (physDmu ν μ X τ y)` for a jointly `C²` field `X` with
`X τ (g y) = g (X τ y)`: the time derivative and the first derivative chain through `g`
(`HasFDerivAt` uniqueness), and the Laplacian is the trace of the second derivative, which is
invariant under the change of orthonormal basis `g.symm e_j`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem raD_g_hasFDerivAt (g : Space ≃ₗᵢ[ℝ] Space) (y : Space) :
    HasFDerivAt (fun z : Space => g z) (g.toContinuousLinearEquiv : Space →L[ℝ] Space) y :=
  (g.toContinuousLinearEquiv).hasFDerivAt

theorem raD_fderiv_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : Differentiable ℝ f)
    (hfg : ∀ z, f (g z) = g (f z)) (y v : Space) :
    fderiv ℝ f (g y) (g v) = g (fderiv ℝ f y v) := by
  have h1 : HasFDerivAt (fun z => f (g z))
      ((fderiv ℝ f (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space)) y :=
    (hf (g y)).hasFDerivAt.comp y (raD_g_hasFDerivAt g y)
  have h2 : HasFDerivAt (fun z => g (f z))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ f y)) y :=
    (raD_g_hasFDerivAt g (f y)).comp y (hf y).hasFDerivAt
  have h3 : (fun z => f (g z)) = fun z => g (f z) := funext hfg
  rw [h3] at h1
  have h4 := h1.unique h2
  have h5 := congrArg (fun L : Space →L[ℝ] Space => L v) h4
  simpa using h5

theorem raD_fderiv2_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : ContDiff ℝ 2 f)
    (hfg : ∀ z, f (g z) = g (f z)) (y u v : Space) :
    fderiv ℝ (fderiv ℝ f) (g y) (g u) (g v) = g (fderiv ℝ (fderiv ℝ f) y u v) := by
  have hK : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hK1 : ∀ z w, fderiv ℝ f (g z) (g w) = g (fderiv ℝ f z w) := fun z w =>
    raD_fderiv_equiv g f (hf.differentiable (by norm_num)) hfg z w
  have hA : HasFDerivAt (fun z => fderiv ℝ f (g z) (g v))
      ((ContinuousLinearMap.apply ℝ Space (g v)).comp
        ((fderiv ℝ (fderiv ℝ f) (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space))) y :=
    (ContinuousLinearMap.apply ℝ Space (g v)).hasFDerivAt.comp y
      ((hK (g y)).hasFDerivAt.comp y (raD_g_hasFDerivAt g y))
  have hB : HasFDerivAt (fun z => g (fderiv ℝ f z v))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((ContinuousLinearMap.apply ℝ Space v).comp (fderiv ℝ (fderiv ℝ f) y))) y :=
    (g.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ Space v).hasFDerivAt.comp y (hK y).hasFDerivAt)
  have hB2 : HasFDerivAt (fun z => fderiv ℝ f (g z) (g v))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((ContinuousLinearMap.apply ℝ Space v).comp (fderiv ℝ (fderiv ℝ f) y))) y := by
    have hfun : (fun z => fderiv ℝ f (g z) (g v)) = fun z => g (fderiv ℝ f z v) :=
      funext fun z => hK1 z v
    rw [hfun]
    exact hB
  have key := hA.unique hB2
  have key2 := congrArg (fun L : Space →L[ℝ] Space => L u) key
  simpa using key2

theorem raD_physPd2 (f : Space → Space) (hf : ContDiff ℝ 2 f) (j l : Fin 3) (y : Space) :
    physPd2 f j l y = fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector l) := by
  have hK : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => fderiv ℝ f y' (coordinateVector l))
      ((fderiv ℝ (fderiv ℝ f) y).flip (coordinateVector l)) y := by
    simpa using hK.clm_apply (hasFDerivAt_const (coordinateVector l) y)
  unfold physPd2 physPd
  rw [h2.fderiv]
  simp

theorem raD_trace (B : Space →L[ℝ] Space →L[ℝ] Space) (h : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j : Fin 3, B (h (coordinateVector j)) (h (coordinateVector j)) =
      ∑ j : Fin 3, B (coordinateVector j) (coordinateVector j) := by
  have hexp : ∀ u : Space, u = ∑ k : Fin 3, inner ℝ (coordinateVector k) u • coordinateVector k := by
    intro u
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector, EuclideanSpace.single_apply,
      EuclideanSpace.inner_single_left]
  have hpars : ∀ x y : Space,
      ∑ j : Fin 3, inner ℝ x (coordinateVector j) * inner ℝ (coordinateVector j) y =
        inner ℝ x y := by
    intro x y
    conv_rhs => rw [hexp y]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  have hdelta : ∀ k l : Fin 3,
      inner ℝ (coordinateVector k) (coordinateVector l) = if k = l then 1 else 0 := by
    intro k l
    simp [coordinateVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
      eq_comm]
  have gen : ∀ m j : Fin 3,
      inner ℝ (coordinateVector m) (h (coordinateVector j)) =
        inner ℝ (h.symm (coordinateVector m)) (coordinateVector j) := by
    intro m j
    conv_lhs => rw [← h.apply_symm_apply (coordinateVector m)]
    exact h.inner_map_map _ _
  have hcoef : ∀ k l : Fin 3,
      ∑ j : Fin 3, inner ℝ (coordinateVector k) (h (coordinateVector j)) *
        inner ℝ (coordinateVector l) (h (coordinateVector j)) =
        inner ℝ (coordinateVector k) (coordinateVector l) := by
    intro k l
    have e2 : ∀ j : Fin 3, inner ℝ (coordinateVector l) (h (coordinateVector j)) =
        inner ℝ (coordinateVector j) (h.symm (coordinateVector l)) := by
      intro j
      rw [gen l j, real_inner_comm]
    have hk : ∀ j : Fin 3, inner ℝ (coordinateVector k) (h (coordinateVector j)) =
        inner ℝ (h.symm (coordinateVector k)) (coordinateVector j) := fun j => gen k j
    rw [Finset.sum_congr rfl fun j _ => by rw [hk j, e2 j]]
    rw [hpars (h.symm (coordinateVector k)) (h.symm (coordinateVector l))]
    exact h.symm.inner_map_map _ _
  have hexp2 : ∀ u v : Space, B u v = ∑ k : Fin 3, ∑ l : Fin 3,
      (inner ℝ (coordinateVector k) u * inner ℝ (coordinateVector l) v) •
        B (coordinateVector k) (coordinateVector l) := by
    intro u v
    conv_lhs => rw [hexp u, hexp v]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  calc ∑ j : Fin 3, B (h (coordinateVector j)) (h (coordinateVector j))
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun j _ => hexp2 _ _
    _ = ∑ k : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) := Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, inner ℝ (coordinateVector k) (coordinateVector l) •
          B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
          rw [← Finset.sum_smul, hcoef k l]
    _ = ∑ k : Fin 3, B (coordinateVector k) (coordinateVector k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hdelta]

theorem raD_physLap_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : ContDiff ℝ 2 f)
    (hfg : ∀ z, f (g z) = g (f z)) (y : Space) :
    physLap f (g y) = g (physLap f y) := by
  unfold physLap
  simp only [raD_physPd2 f hf]
  have hw : ∀ j : Fin 3, fderiv ℝ (fderiv ℝ f) (g y) (coordinateVector j) (coordinateVector j) =
      g (fderiv ℝ (fderiv ℝ f) y (g.symm (coordinateVector j)) (g.symm (coordinateVector j))) := by
    intro j
    have := raD_fderiv2_equiv g f hf hfg y (g.symm (coordinateVector j)) (g.symm (coordinateVector j))
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    exact this
  rw [Finset.sum_congr rfl (fun j _ => hw j), ← map_sum, raD_trace (fderiv ℝ (fderiv ℝ f) y) g.symm]

theorem physDmuEquiv : PhysDmuEquiv := by
  intro ν μ g X hX hXg τ y
  have hXτ : ContDiff ℝ 2 (X τ) := hX.comp (contDiff_const.prodMk contDiff_id)
  have hXt : ContDiff ℝ 2 (fun t => X t y) := hX.comp (contDiff_id.prodMk contDiff_const)
  have hfg : ∀ z, X τ (g z) = g (X τ z) := fun z => hXg τ z
  have hT : deriv (fun t => X t (g y)) τ = g (deriv (fun t => X t y) τ) := by
    have e : (fun t => X t (g y)) = fun t => g (X t y) := funext fun t => hXg t y
    rw [e]
    exact ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp_hasDerivAt τ
      (hXt.differentiable (by norm_num) τ).hasDerivAt).deriv
  unfold physDmu
  rw [hT, raD_fderiv_equiv g (X τ) (hXτ.differentiable (by norm_num)) hfg y y,
    raD_physLap_equiv g (X τ) hXτ hfg y, hXg τ y]
  simp [map_sub, map_add, map_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
