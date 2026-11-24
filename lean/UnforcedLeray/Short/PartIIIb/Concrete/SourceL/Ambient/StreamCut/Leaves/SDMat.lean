import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_5

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/5/3`: matrix bookkeeping `SDMat` (source 4917-4937)

Entrywise bookkeeping for `(s∂_s)^j` of matrix functions. The key facts are:
* on `Ioi 0` the entries of `sDerivIter j A` are `sDerivIterS j` of the entries of `A`, and are
  `C^{6-j}` there (`sdMat_aux`);
* `frob B ≤ Σ_{i,i'} |B i i'|` (`frob_le_sum_abs`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Derivative of a matrix-valued function, computed entrywise (when the entries are differentiable). -/
theorem deriv_mat_apply (F : ℝ → Mat3) (s : ℝ)
    (h : ∀ i i' : Fin 3, DifferentiableAt ℝ (fun t => F t i i') s) (i i' : Fin 3) :
    deriv F s i i' = deriv (fun t => F t i i') s := by
  have h1 : ∀ i : Fin 3, DifferentiableAt ℝ (fun t => F t i) s := fun i =>
    differentiableAt_pi.2 fun i' => h i i'
  have e1 : deriv F s = fun i => deriv (fun t => F t i) s := deriv_pi h1
  have e2 : deriv (fun t => F t i) s = fun i' => deriv (fun t => F t i i') s :=
    deriv_pi fun i' => h i i'
  simp only [e1, e2]

/-- Entrywise bound of a matrix by the sum of absolute values of its entries. -/
theorem frob_le_sum_abs (B : Mat3) :
    frob B ≤ ∑ i : Fin 3, ∑ i' : Fin 3, |B i i'| := by
  unfold frob
  have hT0 : 0 ≤ ∑ i : Fin 3, ∑ i' : Fin 3, |B i i'| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  have hle : ∀ i i' : Fin 3, |B i i'| ≤ ∑ i : Fin 3, ∑ i' : Fin 3, |B i i'| := by
    intro i i'
    have h1 : |B i i'| ≤ ∑ i' : Fin 3, |B i i'| :=
      Finset.single_le_sum (f := fun i' => |B i i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i')
    have h2 : ∑ i' : Fin 3, |B i i'| ≤ ∑ i : Fin 3, ∑ i' : Fin 3, |B i i'| :=
      Finset.single_le_sum (f := fun i => ∑ i' : Fin 3, |B i i'|)
        (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact h1.trans h2
  have hsq : ∑ i : Fin 3, ∑ j : Fin 3, B i j ^ 2 ≤
      (∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|) * (∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|) := by
    calc ∑ i : Fin 3, ∑ j : Fin 3, B i j ^ 2
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, |B i j| * (∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs, pow_two]
          exact mul_le_mul_of_nonneg_left (hle i j) (abs_nonneg _)
      _ = (∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|) * (∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|) := by
          simp only [← Finset.sum_mul]
  calc Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, B i j ^ 2)
      ≤ Real.sqrt ((∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|) *
          (∑ i : Fin 3, ∑ i' : Fin 3, |B i i'|)) := Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin 3, ∑ i' : Fin 3, |B i i'| := by
          rw [← pow_two, Real.sqrt_sq hT0]

/-- Induction for the entrywise identification of `(s∂_s)^j A` with `sDerivIterS j` of the entries. -/
theorem sdMat_aux (A : ℝ → Mat3) (hA : ∀ i i' : Fin 3, ContDiffOn ℝ 6 (fun s => A s i i') (Ioi 0)) :
    ∀ j : ℕ, j ≤ 6 →
      (∀ i i' : Fin 3, ContDiffOn ℝ ((6 - j : ℕ) : WithTop ℕ∞)
        (fun s => sDerivIter j A s i i') (Ioi 0)) ∧
      ∀ s : ℝ, 0 < s → ∀ i i' : Fin 3,
        sDerivIter j A s i i' = sDerivIterS j (fun t => A t i i') s := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun i i' => ?_, fun s _ i i' => rfl⟩
    have e : ((6 - 0 : ℕ) : WithTop ℕ∞) = 6 := by norm_num
    rw [e]
    exact hA i i'
  | succ j ih =>
    intro hj
    obtain ⟨hreg, heq⟩ := ih (by omega)
    have hdiff : ∀ i i' : Fin 3, ∀ s : ℝ, 0 < s →
        DifferentiableAt ℝ (fun t => sDerivIter j A t i i') s := by
      intro i i' s hs
      have h1 : ContDiffOn ℝ 1 (fun t => sDerivIter j A t i i') (Ioi 0) :=
        (hreg i i').of_le (by exact_mod_cast (show 1 ≤ 6 - j by omega))
      exact (h1.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hs)
    have hstep : ∀ s : ℝ, 0 < s → ∀ i i' : Fin 3,
        sDerivIter (j + 1) A s i i' = s * deriv (fun t => sDerivIter j A t i i') s := by
      intro s hs i i'
      have hmat : sDerivIter (j + 1) A s = s • deriv (sDerivIter j A) s := rfl
      rw [hmat, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [deriv_mat_apply (sDerivIter j A) s (fun i i' => hdiff i i' s hs) i i']
    refine ⟨fun i i' => ?_, fun s hs i i' => ?_⟩
    · have hd : ContDiffOn ℝ ((6 - (j + 1) : ℕ) : WithTop ℕ∞)
          (fun t => deriv (fun u => sDerivIter j A u i i') t) (Ioi 0) := by
        refine (hreg i i').deriv_of_isOpen isOpen_Ioi ?_
        have hcast : ((6 - (j + 1) : ℕ) : WithTop ℕ∞) + 1 = ((6 - j : ℕ) : WithTop ℕ∞) := by
          rw [← Nat.cast_succ, Nat.succ_eq_add_one, show 6 - (j + 1) + 1 = 6 - j by omega]
        exact hcast.le
      have hg : ContDiffOn ℝ ((6 - (j + 1) : ℕ) : WithTop ℕ∞)
          (fun t => t * deriv (fun u => sDerivIter j A u i i') t) (Ioi 0) :=
        contDiffOn_id.mul hd
      exact hg.congr fun t ht => hstep t ht i i'
    · rw [hstep s hs i i']
      have hev : (fun t => sDerivIter j A t i i') =ᶠ[nhds s]
          (fun t => sDerivIterS j (fun u => A u i i') t) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hs) fun t ht => heq t ht i i'
      rw [hev.deriv_eq]
      rfl

/-- Matrix bookkeeping: if every entry of `A : ℝ → Mat3` is `C^6` on `(0,∞)`, then for `s > 0`,
`j ≤ 6`, `(s∂_s)^j` acts entrywise and `frob B ≤ Σ_{i,i'} |B i i'|`. -/
theorem sdMat : SDMat := by
  unfold SDMat
  intro A hA s hs j hj
  obtain ⟨-, heq⟩ := sdMat_aux A hA j hj
  calc frob (sDerivIter j A s) ≤ ∑ i : Fin 3, ∑ i' : Fin 3, |sDerivIter j A s i i'| :=
        frob_le_sum_abs _
    _ = ∑ i : Fin 3, ∑ i' : Fin 3, |sDerivIterS j (fun t => A t i i') s| := by
        simp only [heq s hs]

end UnforcedLeray.Short.PartIIIb.Concrete
