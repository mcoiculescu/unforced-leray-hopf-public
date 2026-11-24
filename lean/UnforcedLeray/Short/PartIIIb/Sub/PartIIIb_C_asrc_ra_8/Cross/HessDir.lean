import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcHessUnif

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : second derivatives of `V_j` as a bilinear form

Source `the November 2 reference manuscript`
4963-4966: the basis bound `HessVjUnif` (`hessVjUnif`, `Sub/Leaves/EAcHessUnif.lean`) extends
bilinearly: `|D²V_j(x)[v][w]| ≤ 4K (1+|x_j|²)² e^{-|x_j|²/(4a)} |v||w|` (sup norms).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rc_hess_basis (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) (a b : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei a) =
      fderiv ℝ (fderiv ℝ (Vj ν s j)) x (ei a) (ei b) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ (Vj ν s j)) x :=
    (((rc_Vj_contDiff ν s j).fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
  rw [fderiv_clm_apply hD (differentiableAt_const _)]
  simp

theorem rcHessDir : RcHessDir := by
  obtain ⟨K, hK, hH⟩ := hessVjUnif
  refine ⟨4 * K, by positivity, ?_⟩
  intro ν s j x v w hν hν1 hs hsT
  set G := (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) with hG
  have hG0 : 0 ≤ G := by rw [hG]; unfold sq2; positivity
  set D := fderiv ℝ (fderiv ℝ (Vj ν s j)) x with hDdef
  have hb : ∀ a b : Fin 2, ‖D (ei a) (ei b)‖ ≤ K * G := by
    intro a b
    rw [hDdef, ← rc_hess_basis]
    exact hH ν s hν hν1 hs hsT j x a b
  have hv1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  have hw1 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
  have hw2 : |w.2| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le w
  have hv : v = v.1 • ei 0 + v.2 • ei 1 := by
    ext <;> simp [ei]
  have hw : w = w.1 • ei 0 + w.2 • ei 1 := by
    ext <;> simp [ei]
  have hexp : D v w = (v.1 * w.1) • D (ei 0) (ei 0) + (v.1 * w.2) • D (ei 0) (ei 1) +
      ((v.2 * w.1) • D (ei 1) (ei 0) + (v.2 * w.2) • D (ei 1) (ei 1)) := by
    conv_lhs => rw [hv, hw]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_add, smul_smul]
    rw [mul_comm w.1 v.1, mul_comm w.1 v.2, mul_comm w.2 v.1, mul_comm w.2 v.2]
    abel
  have hterm : ∀ (r : ℝ) (a b : Fin 2), |r| ≤ ‖v‖ * ‖w‖ →
      ‖r • D (ei a) (ei b)‖ ≤ ‖v‖ * ‖w‖ * (K * G) := by
    intro r a b hr
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hr (hb a b) (norm_nonneg _) (by positivity)
  have hp : ∀ (p q : ℝ), |p| ≤ ‖v‖ → |q| ≤ ‖w‖ → |p * q| ≤ ‖v‖ * ‖w‖ := by
    intro p q hp hq
    rw [abs_mul]
    exact mul_le_mul hp hq (abs_nonneg _) (norm_nonneg _)
  rw [hexp]
  have t1 := hterm _ 0 0 (hp _ _ hv1 hw1)
  have t2 := hterm _ 0 1 (hp _ _ hv1 hw2)
  have t3 := hterm _ 1 0 (hp _ _ hv2 hw1)
  have t4 := hterm _ 1 1 (hp _ _ hv2 hw2)
  calc ‖(v.1 * w.1) • D (ei 0) (ei 0) + (v.1 * w.2) • D (ei 0) (ei 1) +
        ((v.2 * w.1) • D (ei 1) (ei 0) + (v.2 * w.2) • D (ei 1) (ei 1))‖
      ≤ ‖(v.1 * w.1) • D (ei 0) (ei 0)‖ + ‖(v.1 * w.2) • D (ei 0) (ei 1)‖ +
        (‖(v.2 * w.1) • D (ei 1) (ei 0)‖ + ‖(v.2 * w.2) • D (ei 1) (ei 1)‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ 4 * (‖v‖ * ‖w‖ * (K * G)) := by linarith
    _ = 4 * K * (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          ‖v‖ * ‖w‖ := by rw [hG]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
