import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# `PartII-b:T10/6/1/4`: `GActPair` (`⟪gΦ, gu⟫ = ⟪Φ, u⟫`, SP 1912-1915)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.GActLeaf4

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem orth_leaf4 (g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space) (j k : Fin 3) :
    ∑ i : Fin 3, UnforcedLeray.B0412.gEntry g i j * UnforcedLeray.B0412.gEntry g i k
      = if j = k then 1 else 0 := by
  have h1 : ∑ i : Fin 3, UnforcedLeray.B0412.gEntry g i j * UnforcedLeray.B0412.gEntry g i k
      = inner ℝ (g (EuclideanSpace.single j 1)) (g (EuclideanSpace.single k 1)) := by
    rw [PiLp.inner_apply]
    simp [UnforcedLeray.B0412.gEntry, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [h1, LinearIsometryEquiv.inner_map_map]
  by_cases h : j = k
  · subst h; simp [PiLp.inner_apply, PiLp.single_apply]
  · simp [h, PiLp.inner_apply, PiLp.single_apply, Ne.symm h]

theorem dotL_gC_leaf4 (g : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space) (a b : CVec3) :
    dotL (UnforcedLeray.B0412.gC g a) (UnforcedLeray.B0412.gC g b) = dotL a b := by
  have hd : ∀ j : Fin 3, ∑ i : Fin 3, ((UnforcedLeray.B0412.gEntry g i j : ℝ) : ℂ) *
      ((UnforcedLeray.B0412.gEntry g i j : ℝ) : ℂ) = 1 := by
    intro j
    have h := orth_leaf4 g j j
    rw [if_pos rfl] at h
    exact_mod_cast h
  have ho : ∀ j k : Fin 3, j ≠ k → ∑ i : Fin 3, ((UnforcedLeray.B0412.gEntry g i j : ℝ) : ℂ) *
      ((UnforcedLeray.B0412.gEntry g i k : ℝ) : ℂ) = 0 := by
    intro j k hjk
    have h := orth_leaf4 g j k
    rw [if_neg hjk] at h
    exact_mod_cast h
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have o01 := ho 0 1 (by decide)
  have o02 := ho 0 2 (by decide)
  have o12 := ho 1 2 (by decide)
  simp only [Fin.sum_univ_three] at d0 d1 d2 o01 o02 o12
  rw [dotL_apply, dotL_apply]
  simp only [UnforcedLeray.B0412.gC_apply, Fin.sum_univ_three]
  linear_combination (a 0 * b 0) * d0 + (a 1 * b 1) * d1 + (a 2 * b 2) * d2
    + (a 0 * b 1 + a 1 * b 0) * o01 + (a 0 * b 2 + a 2 * b 0) * o02
    + (a 1 * b 2 + a 2 * b 1) * o12

end UnforcedLeray.Short.IIb.GActLeaf4

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem gActPair : UnforcedLeray.Short.IIb.GActPair := by
  unfold UnforcedLeray.Short.IIb.GActPair
  intro P g Φ u
  have hpt : ∀ t : ℝ,
      ∫ y, dotL (UnforcedLeray.Short.IIb.gAct g Φ (t, y)) (UnforcedLeray.Short.IIb.gAct g u (t, y))
        = ∫ y, dotL (Φ (t, y)) (u (t, y)) := by
    intro t
    simp only [UnforcedLeray.Short.IIb.gAct, UnforcedLeray.Short.IIb.GActLeaf4.dotL_gC_leaf4]
    exact (LinearIsometryEquiv.measurePreserving g.symm).integral_comp
      g.symm.toHomeomorph.measurableEmbedding (fun y => dotL (Φ (t, y)) (u (t, y)))
  unfold UnforcedLeray.Cons.C03.Concrete.pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpt t)
