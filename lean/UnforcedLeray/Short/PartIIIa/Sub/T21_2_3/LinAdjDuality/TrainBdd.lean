import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# Time-local train bounds on the cell (`LadTrainBddAll`, SP 270-288, 2866-2873, 3050-3054)

For a BUC train with `ν ≤ ν₀`, the velocity is bounded on `[0, S] × ℝ²` and the vorticity gradient
is bounded with the weight `jb^{(m+2)/2}` on the cell `C_c`, `c = ν^{-2}`. The weight is controlled
on the cell by `jb x ≤ (1 + c²/4)(1 + η²)`, and the derivative of the vorticity is controlled by the
second derivative of the velocity: `|∂_j curl v| ≤ 2 ‖D²v‖` (`pd_curl_le`, proved here from
`B0238.curl_eq_fderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace TrainBddAux

lemma dir_norm_le (j : Fin 2) : ‖B0579.dir j‖ ≤ 1 := by
  fin_cases j <;> simp [B0579.dir, Prod.norm_def]

lemma pd_differentiableAt {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 2 g) (k : Fin 2) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y => B0579.pd k g y) x := by
  have hc : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  exact (((hc.differentiable (by norm_num)) x).clm_apply (differentiableAt_const _))

lemma pd_pd_eq {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (j k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (B0579.pd k f) x = iteratedFDeriv ℝ 2 f x ![B0579.dir j, B0579.dir k] := by
  have hc : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hcd : DifferentiableAt ℝ (fderiv ℝ f) x := (hc.differentiable (by norm_num)) x
  have h1 : fderiv ℝ (fun y => fderiv ℝ f y (B0579.dir k)) x
      = (fderiv ℝ (fderiv ℝ f) x).flip (B0579.dir k) := by
    have := fderiv_clm_apply hcd (differentiableAt_const (B0579.dir k))
    rw [this]
    simp
  have h2 : B0579.pd j (B0579.pd k f) x
      = fderiv ℝ (fun y => fderiv ℝ f y (B0579.dir k)) x (B0579.dir j) := rfl
  rw [h2, h1, ContinuousLinearMap.flip_apply, iteratedFDeriv_two_apply]
  simp

lemma abs_pd_pd_le {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (j k : Fin 2) (x : ℝ × ℝ) :
    |B0579.pd j (B0579.pd k f) x| ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [pd_pd_eq hf, ← Real.norm_eq_abs]
  have hprod : ∏ i : Fin 2, ‖(![B0579.dir j, B0579.dir k] : Fin 2 → ℝ × ℝ) i‖ ≤ 1 := by
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_le_one₀ (dir_norm_le j) (norm_nonneg _) (dir_norm_le k)
  calc ‖iteratedFDeriv ℝ 2 f x ![B0579.dir j, B0579.dir k]‖
      ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ∏ i : Fin 2, ‖(![B0579.dir j, B0579.dir k] : Fin 2 → ℝ × ℝ) i‖ :=
        (iteratedFDeriv ℝ 2 f x).le_opNorm _
    _ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ 2 f x‖ := mul_one _

lemma norm_comp_le (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hv : ContDiff ℝ ∞ v) (i : Fin 2)
    (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun w => v w i) x‖ ≤ ‖iteratedFDeriv ℝ 2 v x‖ := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj i
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
    rw [one_mul]
    exact PiLp.norm_apply_le y i
  have hn : ContDiffAt ℝ ∞ v x := hv.contDiffAt
  have hle : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
  have h := L.norm_iteratedFDeriv_comp_left hn hle
  calc ‖iteratedFDeriv ℝ 2 (fun w => v w i) x‖ = ‖iteratedFDeriv ℝ 2 (L ∘ v) x‖ := rfl
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ 2 v x‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ 2 v x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ 2 v x‖ := one_mul _

/-- **Derivative of the vorticity** (`CurlJetBound` at `j = 1`): `|∂_j curl v| ≤ 2‖D²v‖`. -/
lemma pd_curl_le (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hv : ContDiff ℝ ∞ v) (j : Fin 2)
    (x : ℝ × ℝ) :
    |B0579.pd j (UnforcedLeray.Cyl.curl v) x| ≤ 2 * ‖iteratedFDeriv ℝ 2 v x‖ := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by simp)
  have hf1 : ContDiff ℝ 2 (fun w => v w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv2
  have hf0 : ContDiff ℝ 2 (fun w => v w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv2
  have hfun : UnforcedLeray.Cyl.curl v
      = fun z => B0579.pd 0 (fun w => v w 1) z - B0579.pd 1 (fun w => v w 0) z := by
    funext z
    rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 z]
    simp [B0579.pd, B0579.dir]
  have key : ∀ (A B : ℝ × ℝ → ℝ), DifferentiableAt ℝ A x → DifferentiableAt ℝ B x →
      B0579.pd j (fun z => A z - B z) x = B0579.pd j A x - B0579.pd j B x := by
    intro A B hA hB
    unfold B0579.pd
    rw [fderiv_fun_sub hA hB]
    simp
  have hcurl : B0579.pd j (UnforcedLeray.Cyl.curl v) x
      = B0579.pd j (B0579.pd 0 (fun w => v w 1)) x - B0579.pd j (B0579.pd 1 (fun w => v w 0)) x := by
    rw [hfun]
    exact key _ _ (pd_differentiableAt hf1 0 x) (pd_differentiableAt hf0 1 x)
  rw [hcurl]
  have h1 := abs_pd_pd_le hf1 j 0 x
  have h2 := abs_pd_pd_le hf0 j 1 x
  have n1 := norm_comp_le v hv 1 x
  have n0 := norm_comp_le v hv 0 x
  calc |B0579.pd j (B0579.pd 0 (fun w => v w 1)) x - B0579.pd j (B0579.pd 1 (fun w => v w 0)) x|
      ≤ |B0579.pd j (B0579.pd 0 (fun w => v w 1)) x| + |B0579.pd j (B0579.pd 1 (fun w => v w 0)) x| :=
        abs_sub _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 (fun w => v w 1) x‖ + ‖iteratedFDeriv ℝ 2 (fun w => v w 0) x‖ :=
        add_le_add h1 h2
    _ ≤ ‖iteratedFDeriv ℝ 2 v x‖ + ‖iteratedFDeriv ℝ 2 v x‖ := add_le_add n1 n0
    _ = 2 * ‖iteratedFDeriv ℝ 2 v x‖ := by ring

/-- On the cell, `|x.1| ≤ c/2`, hence `jb x ≤ (1 + c²/4)(1 + x.2²)`. -/
lemma jb_le_cell {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) :
    B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
  have hx' : -(c / 2) ≤ x.1 ∧ x.1 < c / 2 := by
    have h := hx
    simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at h
    exact h
  have h1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx'.1, hx'.2.le⟩
  have h2 : x.1 ^ 2 ≤ (c / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  unfold B0579.jb
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg x.2), sq_nonneg x.2]

end TrainBddAux

/-- **Time-local bounds of BUC trains** (SP 270-288, 2866-2873, 3050-3054): with the polynomial
weighted jet bound `TrainWeightedJetPoly`, every BUC train with `ν ≤ ν₀` satisfies the bounds
`LadTrainBdd tr m S C` on `[0, S]` for some `C`. -/
theorem ladTrainBddAll (m : ℝ) (hW : TrainWeightedJetPoly) : LadTrainBddAll m := by
  unfold LadTrainBddAll
  obtain ⟨C', N, ν₀, hν₀, hbd⟩ := hW (⌈max 0 ((m + 2) / 2)⌉₊) 2
  refine ⟨ν₀, hν₀, fun ν hν tr htr S hS => ?_⟩
  obtain ⟨M, hM⟩ := htr.sup_bound hS
  set k : ℕ := ⌈max 0 ((m + 2) / 2)⌉₊ with hk
  refine ⟨max M ((1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (2 * (|C'| * ν⁻¹ ^ N * (1 + S) ^ N))), ?_⟩
  unfold LadTrainBdd
  intro ρ hρ x hx
  have hρ0 : 0 ≤ ρ := hρ.1
  have hρS : ρ ≤ S := hρ.2
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h1 : ‖tr.v ρ x‖ ≤ M := hM ρ hρ x
    have h2 : ‖tr.v ρ x j‖ ≤ ‖tr.v ρ x‖ := PiLp.norm_apply_le (tr.v ρ x) j
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (h1.trans (le_max_left _ _))
  · have hjb1 : 1 ≤ B0579.jb x := by
      unfold B0579.jb
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hcell := TrainBddAux.jb_le_cell (c := ν ^ (-2 : ℝ)) hx
    have hcurl : |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x|
        ≤ 2 * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖ :=
      TrainBddAux.pd_curl_le (tr.v ρ) (UnforcedLeray.B0238.contDiff_Vc tr hρ0) j x
    have hD : (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖
        ≤ C' * ν⁻¹ ^ N * (1 + ρ) ^ N :=
      hbd ν hν tr htr ρ hρ0 x
    have hpowS : (1 + ρ) ^ N ≤ (1 + S) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have hnu : 0 ≤ ν⁻¹ ^ N := pow_nonneg (inv_nonneg.2 hν.1.le) N
    have hD' : (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖
        ≤ |C'| * ν⁻¹ ^ N * (1 + S) ^ N := by
      calc (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖
          ≤ C' * ν⁻¹ ^ N * (1 + ρ) ^ N := hD
        _ ≤ |C'| * ν⁻¹ ^ N * (1 + ρ) ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C') hnu)
            (pow_nonneg (by linarith) N)
        _ ≤ |C'| * ν⁻¹ ^ N * (1 + S) ^ N :=
          mul_le_mul_of_nonneg_left hpowS (mul_nonneg (abs_nonneg _) hnu)
    have hjbe : B0579.jb x ^ ((m + 2) / 2)
        ≤ (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (1 + x.2 ^ 2) ^ k := by
      have he : (m + 2) / 2 ≤ (k : ℝ) := le_trans (le_max_right _ _) (Nat.le_ceil _)
      calc B0579.jb x ^ ((m + 2) / 2) ≤ B0579.jb x ^ (k : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hjb1 he
        _ = B0579.jb x ^ k := Real.rpow_natCast _ _
        _ ≤ ((1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) * (1 + x.2 ^ 2)) ^ k :=
          pow_le_pow_left₀ (B0579.jb_pos x).le hcell k
        _ = (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (1 + x.2 ^ 2) ^ k := mul_pow _ _ _
    have hA := mul_le_mul hjbe hcurl (abs_nonneg _) (by positivity)
    have hK : (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (1 + x.2 ^ 2) ^ k
        * (2 * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖)
        ≤ (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (2 * (|C'| * ν⁻¹ ^ N * (1 + S) ^ N)) := by
      calc (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (1 + x.2 ^ 2) ^ k
            * (2 * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖)
          = (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (2 * ((1 + x.2 ^ 2) ^ k
              * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖)) := by ring
        _ ≤ (1 + (ν ^ (-2 : ℝ)) ^ 2 / 4) ^ k * (2 * (|C'| * ν⁻¹ ^ N * (1 + S) ^ N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD' (by norm_num)) (by positivity)
    exact hA.trans (hK.trans (le_max_right _ _))
