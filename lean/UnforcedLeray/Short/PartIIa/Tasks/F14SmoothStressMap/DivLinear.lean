import UnforcedLeray.Short.PartIIa.Sub.F14_1

/-!
# `PartII-a:F14/1/5`: `smoothDivLinear`

Source `the November 2 reference manuscript`, lines 1537-1540.  The map
`G ↦ testElem P 2 G` on phase tests is injective (continuous slices in `L²` are determined), so
a smooth tensor determines its rows, hence its divergence; linearity follows from additivity of
`dy` on differentiable maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

theorem phaseTest_eq_of_testElem_eq {P : ℝ} [Fact (0 < P)] {F F' : ℝ × Space → CVec3}
    (hF : IsPhaseTest P F) (hF' : IsPhaseTest P F')
    (h : testElem P 2 F = testElem P 2 F') : F = F' := by
  have h1 := hF.isSliceTest 2
  have h2 := hF'.isSliceTest 2
  rw [testElem_of h1, testElem_of h2] at h
  have h3 : circleSlice h1 = circleSlice h2 := ContinuousMap.toLp_injective _ h
  have h4 : ∀ τ : ℝ, sliceMap h1.2 τ = sliceMap h2.2 τ := fun τ => by
    rw [← circleSlice_coe h1, ← circleSlice_coe h2, h3]
  funext ⟨τ, y⟩
  have h5 := h4 τ
  unfold sliceMap at h5
  rw [MemLp.toLp_eq_toLp_iff] at h5
  have h6 : (fun y => F (τ, y)) = fun y => F' (τ, y) :=
    (Continuous.ae_eq_iff_eq volume (hF.continuous_slice τ) (hF'.continuous_slice τ)).1 h5
  exact congrFun h6 y

theorem rows_eq_of_smoothTensor_eq {P : ℝ} [Fact (0 < P)] {G G' : Fin 3 → ℝ × Space → CVec3}
    (hG : ∀ i, IsPhaseTest P (G i)) (hG' : ∀ i, IsPhaseTest P (G' i))
    (h : smoothTensor P G = smoothTensor P G') : G = G' := by
  funext i
  have := congrArg (fun T : Y2Sym P => T i) h
  exact phaseTest_eq_of_testElem_eq (hG i) (hG' i) this

theorem isPhaseTest_tensorDiv {P : ℝ} (G : Fin 3 → ℝ × Space → CVec3)
    (h : ∀ i, IsPhaseTest P (G i)) : IsPhaseTest P (tensorDiv G) := by
  have key : tensorDiv G = ∑ i : Fin 3, ∑ j : Fin 3, fun p =>
      ((ContinuousLinearMap.smulRight
        ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)
        (EuclideanSpace.single i (1 : ℂ) : CVec3)) (dy j (G i) p)) := by
    funext p
    ext k
    simp [tensorDiv, Finset.sum_apply, Pi.single_apply]
  rw [key]
  refine IsPhaseTest.sum _ fun i _ => IsPhaseTest.sum _ fun j _ => ?_
  exact ((h i).dy j).clm_comp _

theorem dy_cSmul {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℂ) (j : Fin 3) :
    dy j (c • G) = c • dy j G := by
  funext p
  simp [dy, fderiv_const_smul (hG p) c]

theorem smoothDivLinear : SmoothDivLinear := by
  intro P _ hP M hMS hmem
  classical
  have hex : ∀ X : M, ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (X : Y2Sym P) :=
    fun X => (hmem X).1 X.2
  choose G hG hS hX using hex
  have hdiff : ∀ (X : M) i, Differentiable ℝ (G X i) := fun X i =>
    ((hG X i).smooth.differentiable (by simp))
  have st_add : ∀ (G₁ G₂ : Fin 3 → ℝ × Space → CVec3), (∀ i, IsPhaseTest P (G₁ i)) →
      (∀ i, IsPhaseTest P (G₂ i)) →
      smoothTensor P (fun i => G₁ i + G₂ i) = smoothTensor P G₁ + smoothTensor P G₂ := by
    intro G₁ G₂ h₁ h₂
    ext i : 1
    simp only [smoothTensor, PiLp.add_apply, WithLp.ofLp_toLp]
    exact testElem_add ((h₁ i).isSliceTest 2) ((h₂ i).isSliceTest 2)
  have st_smul : ∀ (c : ℂ) (G₁ : Fin 3 → ℝ × Space → CVec3), (∀ i, IsPhaseTest P (G₁ i)) →
      smoothTensor P (fun i => c • G₁ i) = c • smoothTensor P G₁ := by
    intro c G₁ h₁
    ext i : 1
    simp only [smoothTensor, PiLp.smul_apply, WithLp.ofLp_toLp]
    exact testElem_const_smul ((h₁ i).isSliceTest 2) c
  refine ⟨
    { toFun := fun X => testElem P 2 (tensorDiv (G X))
      map_add' := ?_
      map_smul' := ?_ }, ?_⟩
  · intro X Y
    have hsum : ∀ i, IsPhaseTest P ((fun i => G X i + G Y i) i) := fun i => (hG X i).add (hG Y i)
    have heq : G (X + Y) = fun i => G X i + G Y i :=
      rows_eq_of_smoothTensor_eq (hG _) hsum (by
        rw [hX, st_add _ _ (hG X) (hG Y), hX, hX]; rfl)
    have hd : tensorDiv (G (X + Y)) = tensorDiv (G X) + tensorDiv (G Y) := by
      rw [heq]
      funext p
      ext k
      simp only [tensorDiv, Pi.add_apply, WithLp.ofLp_toLp, PiLp.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (dy_add (hdiff X k) (hdiff Y k) j) p
      simp only [Pi.add_apply] at this
      rw [this]; rfl
    show testElem P 2 (tensorDiv (G (X + Y))) = _
    rw [hd]
    exact testElem_add ((isPhaseTest_tensorDiv _ (hG X)).isSliceTest 2)
      ((isPhaseTest_tensorDiv _ (hG Y)).isSliceTest 2)
  · intro c X
    have hsm : ∀ i, IsPhaseTest P ((fun i => c • G X i) i) := fun i => (hG X i).const_smul c
    have heq : G (c • X) = fun i => c • G X i :=
      rows_eq_of_smoothTensor_eq (hG _) hsm (by
        rw [hX, st_smul c _ (hG X), hX]; rfl)
    have hd : tensorDiv (G (c • X)) = c • tensorDiv (G X) := by
      rw [heq]
      funext p
      ext k
      simp only [tensorDiv, Pi.smul_apply, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (dy_cSmul (hdiff X k) c j) p
      simp only [Pi.smul_apply] at this
      rw [this]; rfl
    show testElem P 2 (tensorDiv (G (c • X))) = c • testElem P 2 (tensorDiv (G X))
    rw [hd]
    exact testElem_const_smul ((isPhaseTest_tensorDiv _ (hG X)).isSliceTest 2) c
  · intro X G' hG' hS' hX'
    have := rows_eq_of_smoothTensor_eq (hG' ) (hG X) (by rw [hX', hX])
    show testElem P 2 (tensorDiv (G X)) = _
    rw [this]

end UnforcedLeray.Short.PartIIa
