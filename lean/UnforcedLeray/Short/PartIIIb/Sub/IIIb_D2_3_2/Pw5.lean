import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs

/-!
# `PwBracketDivFree`: the Lie bracket of solenoidal fields is solenoidal (source 4258)

Pointwise calculus in the similarity variables.  With `[a,b]_i = Σ_k a_k ∂_k b_i - Σ_k b_k ∂_k a_i`,
the cross terms `∂_j b_k ∂_k a_j` cancel after relabelling, and the second-order terms reduce to
`Σ_j ∂_j∂_k b_j = ∂_k(div b) = 0` by symmetry of mixed partials (`ContDiffAt.isSymmSndFDerivAt`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `i`-th component of a derivative in direction `v`. -/
theorem pw5_comp (f : Space → Space) (z : Space) (hf : DifferentiableAt ℝ f z) (i : Fin 3)
    (v : Space) : fderiv ℝ f z v i = fderiv ℝ (fun w => f w i) z v := by
  have h : (fun w => f w i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ f := rfl
  rw [h, fderiv_comp z (ContinuousLinearMap.differentiableAt _) hf, ContinuousLinearMap.fderiv]
  rfl

theorem pw5_physPd_apply (f : Space → Space) (j i : Fin 3) (z : Space)
    (hf : DifferentiableAt ℝ f z) :
    physPd f j z i = fderiv ℝ (fun w => f w i) z (coordinateVector j) := by
  unfold physPd
  exact pw5_comp f z hf i _

theorem pw5_decomp (g : Space → ℝ) (z v : Space) :
    fderiv ℝ g z v = ∑ k : Fin 3, v k * fderiv ℝ g z (coordinateVector k) := by
  have hv : v = ∑ k : Fin 3, v k • coordinateVector k := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

theorem pw5_fderiv_apply_const {F : Space → (Space →L[ℝ] ℝ)} {z : Space}
    (hF : DifferentiableAt ℝ F z) (u v : Space) :
    fderiv ℝ (fun w => F w u) z v = fderiv ℝ F z v u := by
  have h : (fun w => F w u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ F := rfl
  rw [h, fderiv_comp z (ContinuousLinearMap.differentiableAt _) hF]
  simp

theorem pw5_symm (g : Space → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (z u v : Space) :
    fderiv ℝ (fderiv ℝ g) z u v = fderiv ℝ (fderiv ℝ g) z v u := by
  have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g z := hg.contDiffAt
  exact (h.isSymmSndFDerivAt (by simp)).eq u v

theorem pw5_dfderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space → F}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) : Differentiable ℝ (fderiv ℝ g) :=
  (hg.fderiv_right (m := 1) (by simp)).differentiable (by simp)

theorem pw5_comp_contDiff (f : Space → Space) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (i : Fin 3) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => f w i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hf

theorem pw5_dd (g : Space → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (i : Fin 3) :
    Differentiable ℝ (fun u => fderiv ℝ g u (coordinateVector i)) :=
  (pw5_dfderiv hg).clm_apply (differentiable_const _)

/-- Derivative of `Σ_k A_k ∂_k F` in direction `v`. -/
theorem pw5_deriv_sum (A : Space → Space) (F : Space → ℝ) (hA : Differentiable ℝ A)
    (hF : Differentiable ℝ F) (hdF : Differentiable ℝ (fderiv ℝ F)) (y v : Space) :
    fderiv ℝ (fun w => ∑ k : Fin 3, A w k * fderiv ℝ F w (coordinateVector k)) y v =
      ∑ k : Fin 3, (A y k * fderiv ℝ (fderiv ℝ F) y v (coordinateVector k) +
        fderiv ℝ F y (coordinateVector k) * fderiv ℝ (fun w => A w k) y v) := by
  have hAk : ∀ k : Fin 3, Differentiable ℝ (fun w => A w k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiable.comp hA
  have hG : ∀ k : Fin 3, Differentiable ℝ (fun w => fderiv ℝ F w (coordinateVector k)) :=
    fun k => (hdF.clm_apply (differentiable_const _))
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun w => A w k * fderiv ℝ F w (coordinateVector k)) y :=
    fun k _ => ((hAk k y).mul (hG k y))
  rw [fderiv_fun_sum hterm, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_fun_mul (hAk k y) (hG k y), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    pw5_fderiv_apply_const (hdF y)]
  simp only [smul_eq_mul]

theorem pw5_diff_sum (A : Space → Space) (F : Space → ℝ) (hA : Differentiable ℝ A)
    (hF : Differentiable ℝ F) (hdF : Differentiable ℝ (fderiv ℝ F)) :
    Differentiable ℝ (fun w => ∑ k : Fin 3, A w k * fderiv ℝ F w (coordinateVector k)) := by
  have hAk : ∀ k : Fin 3, Differentiable ℝ (fun w => A w k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiable.comp hA
  have hG : ∀ k : Fin 3, Differentiable ℝ (fun w => fderiv ℝ F w (coordinateVector k)) :=
    fun k => (hdF.clm_apply (differentiable_const _))
  exact Differentiable.fun_sum (fun k _ => (hAk k).mul (hG k))

/-- The bracket-type difference `Σ_k A_k ∂_k(B_j) - Σ_k B_k ∂_k(A_j)` in direction `v`. -/
theorem pw5_bracket_deriv (A B : Space → Space) (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (j : Fin 3) (y v : Space) :
    fderiv ℝ (fun w => ∑ k : Fin 3, A w k * fderiv ℝ (fun u => B u j) w (coordinateVector k) -
        ∑ k : Fin 3, B w k * fderiv ℝ (fun u => A u j) w (coordinateVector k)) y v =
      ∑ k : Fin 3, (A y k * fderiv ℝ (fderiv ℝ (fun u => B u j)) y v (coordinateVector k) +
        fderiv ℝ (fun u => B u j) y (coordinateVector k) * fderiv ℝ (fun w => A w k) y v) -
      ∑ k : Fin 3, (B y k * fderiv ℝ (fderiv ℝ (fun u => A u j)) y v (coordinateVector k) +
        fderiv ℝ (fun u => A u j) y (coordinateVector k) * fderiv ℝ (fun w => B w k) y v) := by
  have hBj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => B u j) := pw5_comp_contDiff B hB j
  have hAj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => A u j) := pw5_comp_contDiff A hA j
  have hA' : Differentiable ℝ A := hA.differentiable (by simp)
  have hB' : Differentiable ℝ B := hB.differentiable (by simp)
  have hd1 := pw5_diff_sum A (fun u => B u j) hA' (hBj.differentiable (by simp))
    (pw5_dfderiv hBj)
  have hd2 := pw5_diff_sum B (fun u => A u j) hB' (hAj.differentiable (by simp))
    (pw5_dfderiv hAj)
  rw [fderiv_fun_sub (hd1 y) (hd2 y), ContinuousLinearMap.sub_apply,
    pw5_deriv_sum A (fun u => B u j) hA' (hBj.differentiable (by simp)) (pw5_dfderiv hBj) y v,
    pw5_deriv_sum B (fun u => A u j) hB' (hAj.differentiable (by simp)) (pw5_dfderiv hAj) y v]

theorem pwBracketDivFree_proved : PwBracketDivFree := by
  intro a b ha hb hda hdb y
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have had : Differentiable ℝ a := ha.differentiable (by simp)
  have hdfb : Differentiable ℝ (fderiv ℝ b) := pw5_dfderiv hb
  have hdfa : Differentiable ℝ (fderiv ℝ a) := pw5_dfderiv ha
  have hBd : Differentiable ℝ (physBracket a b) := by
    intro w
    exact ((hdfb.clm_apply had).sub (hdfa.clm_apply hbd)) w
  have hbi : ∀ i : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => b w i) :=
    fun i => pw5_comp_contDiff b hb i
  have hai : ∀ i : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => a w i) :=
    fun i => pw5_comp_contDiff a ha i
  -- component formula for the bracket
  have hB : ∀ (i : Fin 3) (w : Space), physBracket a b w i =
      ∑ k : Fin 3, a w k * fderiv ℝ (fun u => b u i) w (coordinateVector k) -
        ∑ k : Fin 3, b w k * fderiv ℝ (fun u => a u i) w (coordinateVector k) := by
    intro i w
    unfold physBracket
    rw [PiLp.sub_apply, pw5_comp b w (hbd w) i, pw5_comp a w (had w) i,
      pw5_decomp _ w (a w), pw5_decomp _ w (b w)]
  have hdiv_j : ∀ j : Fin 3, physPd (physBracket a b) j y j =
      fderiv ℝ (fun w => physBracket a b w j) y (coordinateVector j) :=
    fun j => pw5_physPd_apply (physBracket a b) j j y (hBd y)
  -- symmetry of mixed partials
  have hsb : ∀ j k : Fin 3, fderiv ℝ (fderiv ℝ (fun u => b u j)) y (coordinateVector j)
      (coordinateVector k) = fderiv ℝ (fderiv ℝ (fun u => b u j)) y (coordinateVector k)
        (coordinateVector j) :=
    fun j k => pw5_symm _ (hbi j) y _ _
  have hsa : ∀ j k : Fin 3, fderiv ℝ (fderiv ℝ (fun u => a u j)) y (coordinateVector j)
      (coordinateVector k) = fderiv ℝ (fderiv ℝ (fun u => a u j)) y (coordinateVector k)
        (coordinateVector j) :=
    fun j k => pw5_symm _ (hai j) y _ _
  -- divergence-free relations, differentiated in direction e_k
  have hRb : ∀ k : Fin 3, fderiv ℝ (fderiv ℝ (fun u => b u 0)) y (coordinateVector k)
      (coordinateVector 0) + fderiv ℝ (fderiv ℝ (fun u => b u 1)) y (coordinateVector k)
      (coordinateVector 1) + fderiv ℝ (fderiv ℝ (fun u => b u 2)) y (coordinateVector k)
      (coordinateVector 2) = 0 := by
    intro k
    have hfun : (fun u => ∑ j : Fin 3, fderiv ℝ (fun w => b w j) u (coordinateVector j)) =
        fun _ => (0 : ℝ) := by
      funext u
      exact (Finset.sum_congr rfl fun j _ =>
        (pw5_physPd_apply b j j u (hbd u)).symm).trans (hdb u)
    have hsum : fderiv ℝ (fun u => ∑ j : Fin 3, fderiv ℝ (fun w => b w j) u
        (coordinateVector j)) y (coordinateVector k) = 0 := by
      rw [hfun]
      simp
    rw [fderiv_fun_sum (fun j _ => (pw5_dd (fun w => b w j) (hbi j) j).differentiableAt)] at hsum
    simp only [Fin.sum_univ_three, ContinuousLinearMap.add_apply] at hsum
    rw [pw5_fderiv_apply_const (pw5_dfderiv (hbi 0) y) (coordinateVector 0) (coordinateVector k),
      pw5_fderiv_apply_const (pw5_dfderiv (hbi 1) y) (coordinateVector 1) (coordinateVector k),
      pw5_fderiv_apply_const (pw5_dfderiv (hbi 2) y) (coordinateVector 2) (coordinateVector k)] at hsum
    exact hsum
  have hRa : ∀ k : Fin 3, fderiv ℝ (fderiv ℝ (fun u => a u 0)) y (coordinateVector k)
      (coordinateVector 0) + fderiv ℝ (fderiv ℝ (fun u => a u 1)) y (coordinateVector k)
      (coordinateVector 1) + fderiv ℝ (fderiv ℝ (fun u => a u 2)) y (coordinateVector k)
      (coordinateVector 2) = 0 := by
    intro k
    have hfun : (fun u => ∑ j : Fin 3, fderiv ℝ (fun w => a w j) u (coordinateVector j)) =
        fun _ => (0 : ℝ) := by
      funext u
      exact (Finset.sum_congr rfl fun j _ =>
        (pw5_physPd_apply a j j u (had u)).symm).trans (hda u)
    have hsum : fderiv ℝ (fun u => ∑ j : Fin 3, fderiv ℝ (fun w => a w j) u
        (coordinateVector j)) y (coordinateVector k) = 0 := by
      rw [hfun]
      simp
    rw [fderiv_fun_sum (fun j _ => (pw5_dd (fun w => a w j) (hai j) j).differentiableAt)] at hsum
    simp only [Fin.sum_univ_three, ContinuousLinearMap.add_apply] at hsum
    rw [pw5_fderiv_apply_const (pw5_dfderiv (hai 0) y) (coordinateVector 0) (coordinateVector k),
      pw5_fderiv_apply_const (pw5_dfderiv (hai 1) y) (coordinateVector 1) (coordinateVector k),
      pw5_fderiv_apply_const (pw5_dfderiv (hai 2) y) (coordinateVector 2) (coordinateVector k)] at hsum
    exact hsum
  -- assemble
  rw [Fin.sum_univ_three, hdiv_j 0, hdiv_j 1, hdiv_j 2]
  simp only [hB]
  rw [pw5_bracket_deriv a b ha hb 0 y (coordinateVector 0),
    pw5_bracket_deriv a b ha hb 1 y (coordinateVector 1),
    pw5_bracket_deriv a b ha hb 2 y (coordinateVector 2)]
  simp only [Fin.sum_univ_three]
  linear_combination
    (a y 0) * (hsb 0 0 + hsb 1 0 + hsb 2 0) + (a y 1) * (hsb 0 1 + hsb 1 1 + hsb 2 1)
      + (a y 2) * (hsb 0 2 + hsb 1 2 + hsb 2 2)
      + (a y 0) * hRb 0 + (a y 1) * hRb 1 + (a y 2) * hRb 2
      - (b y 0) * (hsa 0 0 + hsa 1 0 + hsa 2 0) - (b y 1) * (hsa 0 1 + hsa 1 1 + hsa 2 1)
      - (b y 2) * (hsa 0 2 + hsa 1 2 + hsa 2 2)
      - (b y 0) * hRa 0 - (b y 1) * hRa 1 - (b y 2) * hRa 2

end UnforcedLeray.Short.PartIIIb.Concrete
