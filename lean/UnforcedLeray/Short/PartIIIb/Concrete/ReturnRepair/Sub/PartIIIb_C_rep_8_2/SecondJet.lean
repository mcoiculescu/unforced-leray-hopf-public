import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org

/-!
# The second jet as a bilinear map (supports `coefChgDens`, `PartIII-b:C/rep/8/2/pres/4/2/lp/3/org`)

Source `the November 2 reference manuscript`
5287-5289, 2664-2672.  The coordinate sums `Σ_{j,l} ‖∂_j∂_l U‖` are not invariant under rotations
about the axis; the operator norm of the second jet is.  `secondJet f y` is the bilinear map
`(a, b) ↦ Σ a_j b_l ∂_j∂_l f(y)` built from the coordinate second derivatives `physPd2` (so it is
junk-free: it is defined for every `f`), and for `f` with `fderiv f` differentiable at `y` it is
`fderiv (fderiv f) y` (`secondJet_eq_fderiv`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eq_sum_coordinateVector (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext i
  simp [coordinateVector, Pi.single_apply]

/-- The linear map with coordinate values `m j` (`e_j ↦ m j`). -/
def jet1 (m : Fin 3 → Space) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (m j)

theorem jet1_apply (m : Fin 3 → Space) (a : Space) : jet1 m a = ∑ j : Fin 3, a j • m j := by
  simp [jet1]

theorem jet1_basis (m : Fin 3 → Space) (j : Fin 3) : jet1 m (coordinateVector j) = m j := by
  rw [jet1_apply]
  simp [coordinateVector, Pi.single_apply]

theorem eq_jet1 (A : Space →L[ℝ] Space) : A = jet1 fun j => A (coordinateVector j) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [jet1_apply]
  conv_lhs => rw [eq_sum_coordinateVector a]
  simp [map_sum]

theorem jet1_zero : jet1 (fun _ => (0 : Space)) = 0 := by
  ext a : 1
  simp [jet1_apply]

theorem continuous_jet1 : Continuous jet1 := by
  have h : jet1 = fun m => ∑ j : Fin 3,
      (ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) (m j) := by
    funext m; rfl
  rw [h]
  haveI : ContinuousAdd (Space →L[ℝ] Space) := by
    have h3 : IsTopologicalAddGroup (Space →L[ℝ] Space) := inferInstance
    exact h3.toContinuousAdd
  apply continuous_finset_sum
  intro j _
  exact (ContinuousLinearMap.continuous _).comp (continuous_apply j)

/-- The bilinear map with coordinate values `m j l` (`e_j, e_l ↦ m j l`). -/
def jet2 (m : Fin 3 → Fin 3 → Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight
    (∑ l : Fin 3, (EuclideanSpace.proj l : Space →L[ℝ] ℝ).smulRight (m j l))

theorem norm_coordinateVector_sj (j : Fin 3) : ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector]

theorem coordinateVector_proj (j i : Fin 3) :
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (coordinateVector j) = if i = j then 1 else 0 := by
  simp [coordinateVector, EuclideanSpace.single_apply]

theorem jet2_apply (m : Fin 3 → Fin 3 → Space) (a b : Space) :
    jet2 m a b = ∑ j : Fin 3, ∑ l : Fin 3, (a j * b l) • m j l := by
  simp [jet2, Finset.smul_sum, smul_smul]

theorem jet2_basis (m : Fin 3 → Fin 3 → Space) (j l : Fin 3) :
    jet2 m (coordinateVector j) (coordinateVector l) = m j l := by
  rw [jet2_apply]
  simp [coordinateVector, EuclideanSpace.single_apply, Finset.sum_ite_eq]

theorem jet2_sub (m n : Fin 3 → Fin 3 → Space) :
    jet2 m - jet2 n = jet2 (fun j l => m j l - n j l) := by
  ext a b : 2
  simp only [ContinuousLinearMap.sub_apply, jet2_apply, ← Finset.sum_sub_distrib, smul_sub]

/-- `jet2` is continuous (it is linear on a finite-dimensional space). -/
theorem continuous_jet2 : Continuous jet2 := by
  have h : jet2 = fun m => ∑ j : Fin 3,
      (ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space)
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ))
        (∑ l : Fin 3, (ContinuousLinearMap.smulRightL ℝ Space Space
          (EuclideanSpace.proj l : Space →L[ℝ] ℝ)) (m j l)) := by
    funext m; rfl
  rw [h]
  haveI : ContinuousAdd (Space →L[ℝ] Space →L[ℝ] Space) := by
    have h3 : IsTopologicalAddGroup (Space →L[ℝ] Space →L[ℝ] Space) := inferInstance
    exact h3.toContinuousAdd
  apply continuous_finset_sum
  intro j _
  refine (ContinuousLinearMap.continuous _).comp ?_
  apply continuous_finset_sum
  intro l _
  exact (ContinuousLinearMap.continuous _).comp ((continuous_apply l).comp (continuous_apply j))

theorem jet2_zero : jet2 (fun _ _ => (0 : Space)) = 0 := by
  ext a b : 2
  simp [jet2_apply]

theorem norm_le_jet2 (m : Fin 3 → Fin 3 → Space) (j l : Fin 3) : ‖m j l‖ ≤ ‖jet2 m‖ := by
  have h := ContinuousLinearMap.le_opNorm₂ (jet2 m) (coordinateVector j) (coordinateVector l)
  rw [jet2_basis, norm_coordinateVector_sj, norm_coordinateVector_sj] at h
  simpa using h

theorem clm2_ext_basis {A B : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ j l : Fin 3, A (coordinateVector j) (coordinateVector l) =
      B (coordinateVector j) (coordinateVector l)) : A = B := by
  ext a b : 2
  rw [eq_sum_coordinateVector a, eq_sum_coordinateVector b]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, h]

/-- The second jet of `f` at `y` as a bilinear map, from the coordinate second derivatives. -/
def secondJet (f : Space → Space) (y : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  jet2 fun j l => physPd2 f j l y

theorem secondJet_basis (f : Space → Space) (y : Space) (j l : Fin 3) :
    secondJet f y (coordinateVector j) (coordinateVector l) = physPd2 f j l y :=
  jet2_basis _ j l

theorem norm_physPd2_le_secondJet (f : Space → Space) (y : Space) (j l : Fin 3) :
    ‖physPd2 f j l y‖ ≤ ‖secondJet f y‖ :=
  norm_le_jet2 (fun j l => physPd2 f j l y) j l

theorem norm_physPd2_sub_le (f g : Space → Space) (y : Space) (j l : Fin 3) :
    ‖physPd2 f j l y - physPd2 g j l y‖ ≤ ‖secondJet f y - secondJet g y‖ := by
  unfold secondJet
  rw [jet2_sub]
  exact norm_le_jet2 (fun j l => physPd2 f j l y - physPd2 g j l y) j l

theorem norm_physPd_sub_le (f g : Space → Space) (y : Space) (j : Fin 3) :
    ‖physPd f j y - physPd g j y‖ ≤ ‖fderiv ℝ f y - fderiv ℝ g y‖ := by
  have h := (fderiv ℝ f y - fderiv ℝ g y).le_opNorm (coordinateVector j)
  rw [norm_coordinateVector_sj, mul_one] at h
  simpa [physPd] using h

/-- Off the singular points: `secondJet f y = fderiv (fderiv f) y` once `fderiv f` is
differentiable at `y`. -/
theorem secondJet_eq_fderiv {f : Space → Space} {y : Space}
    (h : DifferentiableAt ℝ (fun y' => fderiv ℝ f y') y) :
    secondJet f y = fderiv ℝ (fun y' => fderiv ℝ f y') y := by
  refine clm2_ext_basis fun j l => ?_
  rw [secondJet_basis]
  have hu : DifferentiableAt ℝ (fun _ : Space => coordinateVector l) y := differentiableAt_const _
  have e : fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector l)) y =
      (fderiv ℝ (fun y' => fderiv ℝ f y') y).flip (coordinateVector l) := by
    have := fderiv_clm_apply (u := fun _ : Space => coordinateVector l) h hu
    simpa using this
  show fderiv ℝ (fun y' => physPd f l y') y (coordinateVector j) = _
  have e2 : (fun y' => physPd f l y') = fun y' => fderiv ℝ f y' (coordinateVector l) := rfl
  rw [e2, e]
  rfl

theorem secondJet_zero (y : Space) : secondJet (0 : Space → Space) y = 0 := by
  have h : ∀ j l, physPd2 (0 : Space → Space) j l y = 0 := by
    intro j l
    unfold physPd2
    have : (fun y' => physPd (0 : Space → Space) l y') = 0 := by
      funext y'; simp [physPd]
    rw [this]; simp [physPd]
  unfold secondJet
  simp only [h]
  exact jet2_zero

end UnforcedLeray.Short.PartIIIb.Concrete
