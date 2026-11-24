import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1
import UnforcedLeray.Lib.Kernels.IterApply

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- Bridge: the iterated coordinate derivative along `List.ofFn g` is `iteratedFDeriv`. -/
theorem iterD_ofFn_apply_aux (u : Plane → Vec2) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ∀ g : Fin n → Plane,
      UnforcedLeray.Sob.iterD (List.ofFn g) u = fun z => iteratedFDeriv ℝ n u z g := by
  induction n with
  | zero =>
      intro g
      funext z
      simp [UnforcedLeray.Sob.iterD, iteratedFDeriv_zero_apply]
  | succ n ih =>
      intro g
      funext z
      have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ n u) :=
        hu.iteratedFDeriv_right (m := ∞) (i := n) UnforcedLeray.Kernels.infty_add_nat_le
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n u) z :=
        (contDiff_iff_contDiffAt.mp hD z).differentiableAt (by simp)
      rw [List.ofFn_succ, UnforcedLeray.Sob.iterD_cons]
      dsimp only
      rw [ih (fun i => g i.succ), iteratedFDeriv_succ_apply_left]
      exact fderiv_continuousMultilinear_apply_const_apply hdiff (fun i => g i.succ) (g 0)

/-- Coordinate basis of the plane, indexed by `Fin 2`. -/
def coordBasis (k : Fin 2) : Plane := if k = 0 then ((1 : ℝ), (0 : ℝ)) else ((0 : ℝ), (1 : ℝ))

/-- Coordinates of a point of the plane in the coordinate basis. -/
def coordCoef (k : Fin 2) (p : Plane) : ℝ := if k = 0 then p.1 else p.2

theorem coordCoef_smul_sum (p : Plane) : ∑ k : Fin 2, coordCoef k p • coordBasis k = p := by
  rw [Fin.sum_univ_two]
  refine Prod.ext ?_ ?_ <;> simp [coordCoef, coordBasis]

theorem abs_coordCoef_le (k : Fin 2) (p : Plane) : |coordCoef k p| ≤ ‖p‖ := by
  fin_cases k
  · simp only [coordCoef]
    simp only [Fin.zero_eta, Fin.isValue, if_true]
    rw [← Real.norm_eq_abs]
    exact norm_fst_le p
  · simp only [coordCoef]
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    rw [← Real.norm_eq_abs]
    exact norm_snd_le p

theorem isCoordWord_ofFn_coordBasis {j : ℕ} (r : Fin j → Fin 2) :
    IsCoordWord (List.ofFn fun i => coordBasis (r i)) := by
  unfold IsCoordWord
  intro a ha
  rw [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  unfold coordBasis
  split_ifs <;> simp

/-- Expansion of a multilinear map on `Plane^j` in the coordinate basis. -/
theorem multilinear_expand {j : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) Vec2)
    (v : Fin j → Plane) :
    M v = ∑ r : (Fin j → Fin 2),
      (∏ i, coordCoef (r i) (v i)) • M (fun i => coordBasis (r i)) := by
  have h1 : v = fun i => ∑ k : Fin 2, coordCoef k (v i) • coordBasis k :=
    funext fun i => (coordCoef_smul_sum (v i)).symm
  conv_lhs => rw [h1]
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ]

/-- Norm of a multilinear map on `Plane^j` bounded by its values on basis tuples. -/
theorem norm_le_of_basis {j : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) Vec2)
    (B : ℝ) (hB : 0 ≤ B) (hbas : ∀ r : Fin j → Fin 2, ‖M (fun i => coordBasis (r i))‖ ≤ B) :
    ‖M‖ ≤ (2 : ℝ) ^ j * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
  intro v
  rw [multilinear_expand M v]
  calc ‖∑ r : (Fin j → Fin 2),
        (∏ i, coordCoef (r i) (v i)) • M (fun i => coordBasis (r i))‖
      ≤ ∑ r : (Fin j → Fin 2),
          ‖(∏ i, coordCoef (r i) (v i)) • M (fun i => coordBasis (r i))‖ := norm_sum_le _ _
    _ ≤ ∑ r : (Fin j → Fin 2), (∏ i, ‖v i‖) * B := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
        exact mul_le_mul
          (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => abs_coordCoef_le _ _))
          (hbas r) (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (2 : ℝ) ^ j * B * ∏ i, ‖v i‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-- **Finite-dimensional comparison of `iteratedFDeriv` with coordinate words**
(source 1684-1689). With `K = 2 ^ m`. -/
theorem iteratedFDerivByWords_proof : IteratedFDerivByWords := by
  intro m
  refine ⟨(2 : ℝ) ^ m, by positivity, ?_⟩
  intro u hu j hj x B hB
  have hB0 : 0 ≤ B := by
    have h := hB (List.ofFn fun _ : Fin j => coordBasis 0)
      (by unfold IsCoordWord; intro a ha; rw [List.mem_ofFn] at ha; obtain ⟨i, rfl⟩ := ha
          unfold coordBasis; split_ifs <;> simp)
      (by simp)
    exact le_trans (norm_nonneg _) h
  have hbas : ∀ r : Fin j → Fin 2, ‖iteratedFDeriv ℝ j u x (fun i => coordBasis (r i))‖ ≤ B := by
    intro r
    have h := hB (List.ofFn fun i => coordBasis (r i)) (isCoordWord_ofFn_coordBasis r) (by simp)
    rw [iterD_ofFn_apply_aux u hu j (fun i => coordBasis (r i))] at h
    exact h
  calc ‖iteratedFDeriv ℝ j u x‖ ≤ (2 : ℝ) ^ j * B := norm_le_of_basis _ B hB0 hbas
    _ ≤ (2 : ℝ) ^ m * B :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB0

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
