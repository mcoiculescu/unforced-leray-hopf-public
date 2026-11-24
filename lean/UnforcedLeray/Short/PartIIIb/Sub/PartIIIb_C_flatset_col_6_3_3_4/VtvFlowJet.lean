import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.IterDerivBound

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem iter_le_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ × ℝ → E}
    (n : ℕ) (x : ℝ × ℝ) (m : Fin n → ℝ × ℝ) (hm : ∀ i, ‖m i‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n g x m‖ ≤ ‖iteratedFDeriv ℝ n g x‖ := by
  have hle := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ n g x) m
  have hprod : ∏ i, ‖m i‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hm i)
  exact hle.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)

theorem norm_dir_le (k : Fin 2) : ‖B0579.dir k‖ ≤ 1 := by
  fin_cases k <;> simp [B0579.dir, Prod.norm_def]

theorem vtvFlowJet : VtvFlowJet := by
  intro ν c tr hBUC s₁ s₂ hs₁
  obtain ⟨M0, hM0⟩ := UnforcedLeray.Short.PartI.IsBUCTrain.sup_bound hBUC (le_max_right s₂ 0)
  obtain ⟨M1, hM1⟩ := UnforcedLeray.Short.PartI.IsBUCTrain.deriv_bound hBUC
    (le_max_right s₂ 0) 1
  refine ⟨2 * |ν| + 2 * |M0| + 2 * |M1|, by positivity, ?_⟩
  intro s hs φ hφ M hMb x j
  have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
  have hsS : s ∈ Icc (0 : ℝ) (max s₂ 0) := ⟨hs0.le, hs.2.trans (le_max_left _ _)⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMb x 0 (by norm_num))
  have hv : ContDiff ℝ ∞ (fun y : ℝ × ℝ => tr.v s y) := by
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.mono (prod_mono (Ioi_subset_Ici le_rfl) subset_rfl)
    have hpair : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) :=
      contDiff_const.prodMk contDiff_id
    have hmem : ∀ y : ℝ × ℝ, ((s, y) : ℝ × (ℝ × ℝ)) ∈ Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) := fun y =>
      ⟨hs0, mem_univ _⟩
    exact h1.comp_contDiff hpair hmem
  have hv_at : ∀ y, HasFDerivAt (tr.v s) (fderiv ℝ (tr.v s) y) y := fun y =>
    ((hv.differentiable (by simp)) y).hasFDerivAt
  -- coordinates of the velocity
  have hcoord : ∀ (w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2),
      |(EuclideanSpace.proj (𝕜 := ℝ) i) w| ≤ ‖w‖ := fun w i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w i
  -- derivatives of `φ`
  have hPd : ∀ k : Fin 2, B0579.pd k φ = fun z => iteratedFDeriv ℝ 1 φ z ![B0579.dir k] := by
    intro k
    funext z
    simp [B0579.pd, iteratedFDeriv_one_apply]
  have hpdgen : ∀ (g : ℝ × ℝ → ℝ), ContDiff ℝ ∞ g → ∀ k : Fin 2,
      ContDiff ℝ ∞ (B0579.pd k g) := fun g hg k =>
    (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const
  have hPP : ∀ k l : Fin 2, B0579.pd k (B0579.pd l φ) =
      fun z => iteratedFDeriv ℝ 2 φ z (Fin.cons (B0579.dir k) ![B0579.dir l] : Fin 2 → ℝ × ℝ) := by
    intro k l
    funext z
    rw [hPd l]
    have h := fderiv_iteratedFDeriv_apply_eq hφ 1 z (B0579.dir k) ![B0579.dir l]
    unfold B0579.pd
    exact h
  have hcons : ∀ (k l : Fin 2) (i : Fin 2),
      ‖(Fin.cons (B0579.dir k) ![B0579.dir l] : Fin 2 → ℝ × ℝ) i‖ ≤ 1 := by
    intro k l i
    fin_cases i <;> simp [norm_dir_le]
  have hfirst : ∀ k : Fin 2, ∀ y, |B0579.pd k φ y| ≤ M := by
    intro k y
    have h := (iter_le_norm 1 y ![B0579.dir k] (by intro i; fin_cases i; simp [norm_dir_le])).trans
      (hMb y 1 (by norm_num))
    have e : B0579.pd k φ y = iteratedFDeriv ℝ 1 φ y ![B0579.dir k] := by rw [hPd k]
    rw [e, ← Real.norm_eq_abs]
    exact h
  have hD2 : ∀ k : Fin 2, ∀ d : ℝ × ℝ, ‖d‖ ≤ 1 →
      ‖fderiv ℝ (B0579.pd k φ) x d‖ ≤ M := by
    intro k d hd
    rw [hPd k]
    exact (norm_fderiv_iteratedFDeriv_apply_le hφ 1 x d ![B0579.dir k] hd
      (by intro i; fin_cases i; simp [norm_dir_le])).trans (hMb x 2 (by norm_num))
  have hD3 : ∀ k l : Fin 2, ∀ d : ℝ × ℝ, ‖d‖ ≤ 1 →
      ‖fderiv ℝ (B0579.pd k (B0579.pd l φ)) x d‖ ≤ M := by
    intro k l d hd
    rw [hPP k l]
    exact (norm_fderiv_iteratedFDeriv_apply_le hφ 2 x d _ hd (hcons k l)).trans
      (hMb x 3 (by norm_num))
  -- differentiability
  have dP : ∀ k : Fin 2, DifferentiableAt ℝ (B0579.pd k φ) x := fun k =>
    ((hpdgen φ hφ k).differentiable (by simp)) x
  have dPP : ∀ k l : Fin 2, DifferentiableAt ℝ (B0579.pd k (B0579.pd l φ)) x := fun k l =>
    ((hpdgen _ (hpdgen φ hφ l) k).differentiable (by simp)) x
  have hLapD : fderiv ℝ (UnforcedLeray.Short.IIIa.lapP φ) x (B0579.dir j) =
      fderiv ℝ (B0579.pd 0 (B0579.pd 0 φ)) x (B0579.dir j) +
        fderiv ℝ (B0579.pd 1 (B0579.pd 1 φ)) x (B0579.dir j) := by
    have h := (dPP 0 0).hasFDerivAt.add (dPP 1 1).hasFDerivAt
    have e := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (B0579.dir j)) h.fderiv
    simp only [add_apply] at e
    exact e
  have hdiffLap : DifferentiableAt ℝ (UnforcedLeray.Short.IIIa.lapP φ) x :=
    (dPP 0 0).add (dPP 1 1)
  have hv0 : HasFDerivAt (fun y => tr.v s y 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp (fderiv ℝ (tr.v s) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp x (hv_at x)
  have hv1 : HasFDerivAt (fun y => tr.v s y 1)
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp (fderiv ℝ (tr.v s) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.comp x (hv_at x)
  have hFD : HasFDerivAt
      (fun y => ν * UnforcedLeray.Short.IIIa.lapP φ y +
        (tr.v s y 0 * B0579.pd 0 φ y + tr.v s y 1 * B0579.pd 1 φ y))
      (ν • fderiv ℝ (UnforcedLeray.Short.IIIa.lapP φ) x +
        ((tr.v s x 0) • fderiv ℝ (B0579.pd 0 φ) x + (B0579.pd 0 φ x) •
          ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp (fderiv ℝ (tr.v s) x)) +
        ((tr.v s x 1) • fderiv ℝ (B0579.pd 1 φ) x + (B0579.pd 1 φ x) •
          ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp (fderiv ℝ (tr.v s) x))))) x := by
    have h1 := hdiffLap.hasFDerivAt.const_mul ν
    have h2 := (hv0.mul (dP 0).hasFDerivAt)
    have h3 := (hv1.mul (dP 1).hasFDerivAt)
    exact h1.add (h2.add h3)
  have toAbs : ∀ a : ℝ, ‖a‖ ≤ M → |a| ≤ M := fun a h => by simpa [Real.norm_eq_abs] using h
  have hcd : ∀ d : ℝ × ℝ, ‖d‖ ≤ 1 → ‖fderiv ℝ (tr.v s) x d‖ ≤ M1 := fun d hd => by
    have h := iter_le_norm (g := tr.v s) 1 x ![d] (by intro i; fin_cases i; simpa using hd)
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] at h
    exact h.trans (hM1 s hsS x)
  have hC : ∀ k : Fin 2, ∀ d : ℝ × ℝ, ‖d‖ ≤ 1 →
      |(EuclideanSpace.proj (𝕜 := ℝ) k) (fderiv ℝ (tr.v s) x d)| ≤ M1 :=
    fun k d hd => (hcoord _ k).trans (hcd d hd)
  have hKey := (hdiffLap.hasFDerivAt.const_mul ν).add
    ((hv0.mul (dP 0).hasFDerivAt).add (hv1.mul (dP 1).hasFDerivAt))
  have key : B0579.pd j (vtvFlowTest tr s φ) x =
      ν * fderiv ℝ (UnforcedLeray.Short.IIIa.lapP φ) x (B0579.dir j) +
        ((tr.v s x 0 * fderiv ℝ (B0579.pd 0 φ) x (B0579.dir j) +
            B0579.pd 0 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j))) +
          (tr.v s x 1 * fderiv ℝ (B0579.pd 1 φ) x (B0579.dir j) +
            B0579.pd 1 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j)))) := by
    have e := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (B0579.dir j)) hKey.fderiv
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul] at e
    exact e
  have ha1 : |fderiv ℝ (UnforcedLeray.Short.IIIa.lapP φ) x (B0579.dir j)| ≤ 2 * M := by
    rw [hLapD]
    have h0 := toAbs _ (hD3 0 0 _ (norm_dir_le j))
    have h1 := toAbs _ (hD3 1 1 _ (norm_dir_le j))
    have := abs_add_le (fderiv ℝ (B0579.pd 0 (B0579.pd 0 φ)) x (B0579.dir j))
      (fderiv ℝ (B0579.pd 1 (B0579.pd 1 φ)) x (B0579.dir j))
    linarith
  have hv0x : |tr.v s x 0| ≤ |M0| :=
    ((hcoord (tr.v s x) 0).trans (hM0 s hsS x)).trans (le_abs_self _)
  have hv1x : |tr.v s x 1| ≤ |M0| :=
    ((hcoord (tr.v s x) 1).trans (hM0 s hsS x)).trans (le_abs_self _)
  have hb0 := toAbs _ (hD2 0 _ (norm_dir_le j))
  have hb1 := toAbs _ (hD2 1 _ (norm_dir_le j))
  have hc0 := hC 0 _ (norm_dir_le j)
  have hc1 := hC 1 _ (norm_dir_le j)
  have hP0 := hfirst 0 x
  have hP1 := hfirst 1 x
  have t1 : |ν * fderiv ℝ (UnforcedLeray.Short.IIIa.lapP φ) x (B0579.dir j)| ≤ |ν| * (2 * M) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha1 (abs_nonneg _)
  have t2 : |tr.v s x 0 * fderiv ℝ (B0579.pd 0 φ) x (B0579.dir j)| ≤ |M0| * M := by
    rw [abs_mul]; exact mul_le_mul hv0x hb0 (abs_nonneg _) (abs_nonneg _)
  have t3 : |B0579.pd 0 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
      (fderiv ℝ (tr.v s) x (B0579.dir j))| ≤ M * |M1| := by
    rw [abs_mul]; exact mul_le_mul hP0 (hc0.trans (le_abs_self _)) (abs_nonneg _) hM
  have t4 : |tr.v s x 1 * fderiv ℝ (B0579.pd 1 φ) x (B0579.dir j)| ≤ |M0| * M := by
    rw [abs_mul]; exact mul_le_mul hv1x hb1 (abs_nonneg _) (abs_nonneg _)
  have t5 : |B0579.pd 1 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
      (fderiv ℝ (tr.v s) x (B0579.dir j))| ≤ M * |M1| := by
    rw [abs_mul]; exact mul_le_mul hP1 (hc1.trans (le_abs_self _)) (abs_nonneg _) hM
  rw [key]
  have s1 := abs_add_le (ν * fderiv ℝ (UnforcedLeray.Short.IIIa.lapP φ) x (B0579.dir j))
    (((tr.v s x 0 * fderiv ℝ (B0579.pd 0 φ) x (B0579.dir j) +
            B0579.pd 0 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j))) +
          (tr.v s x 1 * fderiv ℝ (B0579.pd 1 φ) x (B0579.dir j) +
            B0579.pd 1 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j)))))
  have s2 := abs_add_le (tr.v s x 0 * fderiv ℝ (B0579.pd 0 φ) x (B0579.dir j) +
            B0579.pd 0 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j)))
    (tr.v s x 1 * fderiv ℝ (B0579.pd 1 φ) x (B0579.dir j) +
            B0579.pd 1 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j)))
  have s3 := abs_add_le (tr.v s x 0 * fderiv ℝ (B0579.pd 0 φ) x (B0579.dir j))
    (B0579.pd 0 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j)))
  have s4 := abs_add_le (tr.v s x 1 * fderiv ℝ (B0579.pd 1 φ) x (B0579.dir j))
    (B0579.pd 1 φ x * (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
              (fderiv ℝ (tr.v s) x (B0579.dir j)))
  have hfin : |ν| * (2 * M) + |M0| * M + M * |M1| + (|M0| * M + M * |M1|) =
      (2 * |ν| + 2 * |M0| + 2 * |M1|) * M := by ring
  linarith [s1, s2, s3, s4, t1, t2, t3, t4, t5, hfin]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
