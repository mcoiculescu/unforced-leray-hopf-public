import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.FriedDeriv
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2/4`: derivative words of the slice velocity (`stVelWords`)

Source of record: `the November 2 reference manuscript` (SP), lines 270-288 and
2866-2870 (every derivative of the train is bounded).

Route: for a smooth real `K`, the word derivative is a multilinear evaluation,
`pdWordR w K = fun z => iteratedFDeriv ℝ |w| K z (svDirs w)` (`sv_pdWordR_eq`), so
`|pdWordR w K z| ≤ ‖iteratedFDeriv |w| K z‖` and `|fderiv (pdWordR w K) z h| ≤ ‖iteratedFDeriv (|w|+1) K z‖ ‖h‖`
(`sv_fderiv_pdWordR_le`).  For `K = stVel v l`, `‖iteratedFDeriv i (stVel v l)‖ ≤ ‖iteratedFDeriv i v‖ ≤ Av i`
(`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` with the coordinate projection), and the mean value
inequality gives the Lipschitz bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The coordinate directions of a word `u`: `i ↦ ∂_{u_i}` (as vectors of `ℝ × ℝ`). -/
def svDirs (u : List (Fin 2)) : Fin u.length → ℝ × ℝ := fun i => B0579.dir (u.get i)

theorem svw_dir_norm (j : Fin 2) : ‖B0579.dir j‖ = 1 := by
  fin_cases j <;> simp [B0579.dir, Prod.norm_def]

theorem svw_svDirs_norm (u : List (Fin 2)) (i : Fin u.length) : ‖svDirs u i‖ = 1 :=
  svw_dir_norm _

theorem svw_svDirs_cons (j : Fin 2) (u : List (Fin 2)) :
    svDirs (j :: u) = (Fin.cons (B0579.dir j) (svDirs u) : Fin (u.length + 1) → ℝ × ℝ) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [svDirs]
  · simp [svDirs]

theorem svw_diff_iter {K : ℝ × ℝ → ℝ} (hK : ContDiff ℝ ∞ K) (n : ℕ) :
    Differentiable ℝ (iteratedFDeriv ℝ n K) :=
  hK.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top n)

/-- Evaluation at fixed vectors commutes with the derivative of a multilinear-valued map. -/
theorem svw_fderiv_eval {n : ℕ} {F : ℝ × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℝ}
    {z : ℝ × ℝ} (hF : DifferentiableAt ℝ F z) (vs : Fin n → ℝ × ℝ) (e : ℝ × ℝ) :
    fderiv ℝ (fun y => F y vs) z e = (fderiv ℝ F z e) vs := by
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) ℝ vs).hasFDerivAt.comp
    z hF.hasFDerivAt
  rw [show (fun y => F y vs) = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) ℝ vs) ∘ F
    from rfl, hev.fderiv]
  rfl

/-- The word derivative as a multilinear evaluation. -/
theorem sv_pdWordR_eq {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ u : List (Fin 2), pdWordR u f = fun z => iteratedFDeriv ℝ u.length f z (svDirs u)
  | [] => by
    funext z
    show f z = iteratedFDeriv ℝ 0 f z (svDirs [])
    rw [iteratedFDeriv_zero_apply]
  | j :: u => by
    have ih := sv_pdWordR_eq hf u
    rw [show pdWordR (j :: u) f = B0579.pd j (pdWordR u f) from rfl, ih]
    funext z
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ u.length f) z :=
      (svw_diff_iter hf u.length) z
    unfold B0579.pd
    rw [svw_fderiv_eval hdiff (svDirs u) (B0579.dir j)]
    show _ = iteratedFDeriv ℝ (u.length + 1) f z (svDirs (j :: u))
    rw [svw_svDirs_cons, iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]

theorem sv_abs_pdWordR_le {K : ℝ × ℝ → ℝ} (hK : ContDiff ℝ ∞ K) (w : List (Fin 2))
    (x : ℝ × ℝ) : |pdWordR w K x| ≤ ‖iteratedFDeriv ℝ w.length K x‖ := by
  have hg := congrFun (sv_pdWordR_eq hK w) x
  rw [hg]
  show |iteratedFDeriv ℝ w.length K x (svDirs w)| ≤ _
  rw [← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ w.length K x (svDirs w)‖
      ≤ ‖iteratedFDeriv ℝ w.length K x‖ * ∏ i, ‖svDirs w i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ w.length K x‖ := by simp [svw_svDirs_norm]

theorem sv_fderiv_pdWordR_le {K : ℝ × ℝ → ℝ} (hK : ContDiff ℝ ∞ K) (w : List (Fin 2))
    (z h : ℝ × ℝ) :
    ‖fderiv ℝ (pdWordR w K) z h‖ ≤ ‖iteratedFDeriv ℝ (w.length + 1) K z‖ * ‖h‖ := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length K) z :=
    (svw_diff_iter hK w.length) z
  have hg : pdWordR w K = fun y => iteratedFDeriv ℝ w.length K y (svDirs w) :=
    sv_pdWordR_eq hK w
  rw [hg, svw_fderiv_eval hdiff (svDirs w) h]
  calc ‖(fderiv ℝ (iteratedFDeriv ℝ w.length K) z h) (svDirs w)‖
      ≤ ‖fderiv ℝ (iteratedFDeriv ℝ w.length K) z h‖ * ∏ i, ‖svDirs w i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ w.length K) z h‖ := by simp [svw_svDirs_norm]
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ w.length K) z‖ * ‖h‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (w.length + 1) K z‖ * ‖h‖ := by rw [norm_fderiv_iteratedFDeriv]

/-- **(4) Derivative words of the slice velocity** (SP 270-288, 2866-2870). -/
theorem stVelWords : UnforcedLeray.Short.IIIa.StVelWords := by
  intro c v Av hv u l
  have hsm : ContDiff ℝ ∞ (stVel v l) := st_vel_contDiff hv l
  have hper : ∀ x : ℝ × ℝ, stVel v l (x.1 + c, x.2) = stVel v l x := st_vel_periodic hv l
  have hW : ∀ w : List (Fin 2), ContDiff ℝ ∞ (pdWordR w (stVel v l)) ∧
      ∀ x : ℝ × ℝ, pdWordR w (stVel v l) (x.1 + c, x.2) = pdWordR w (stVel v l) x := by
    intro w
    induction w with
    | nil => exact ⟨hsm, hper⟩
    | cons j w ih => exact ⟨st_pd_contDiff ih.1 j, fun x => st_pd_periodic ih.2 j x⟩
  have hproj : ∀ (i : ℕ) (x : ℝ × ℝ),
      ‖iteratedFDeriv ℝ i (stVel v l) x‖ ≤ ‖iteratedFDeriv ℝ i v x‖ := by
    intro i x
    have hfun : stVel v l = (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ v :=
      rfl
    have hn : ‖(EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro y
      simpa using PiLp.norm_apply_le y l
    rw [hfun]
    calc ‖iteratedFDeriv ℝ i ((EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ v) x‖
        ≤ ‖(EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ i v x‖ :=
          ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hv.1.contDiffAt
            (by exact_mod_cast le_top)
      _ ≤ 1 * ‖iteratedFDeriv ℝ i v x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ i v x‖ := one_mul _
  have hbd : ∀ (i : ℕ) (x : ℝ × ℝ), ‖iteratedFDeriv ℝ i (stVel v l) x‖ ≤ Av i :=
    fun i x => (hproj i x).trans (hv.2.2.2 i x)
  have hAv0 : ∀ i : ℕ, 0 ≤ Av i := fun i => (norm_nonneg _).trans (hv.2.2.2 i 0)
  refine ⟨(hW u).1, (hW u).2, ?_, ?_⟩
  · intro x
    exact (sv_abs_pdWordR_le hsm u x).trans (hbd u.length x)
  · intro x y
    have hdiff : ∀ z ∈ (Set.univ : Set (ℝ × ℝ)),
        DifferentiableAt ℝ (pdWordR u (stVel v l)) z :=
      fun z _ => ((hW u).1.differentiable (by simp)) z
    have hbound : ∀ z ∈ (Set.univ : Set (ℝ × ℝ)),
        ‖fderiv ℝ (pdWordR u (stVel v l)) z‖ ≤ Av (u.length + 1) := by
      intro z _
      apply ContinuousLinearMap.opNorm_le_bound _ (hAv0 _)
      intro h
      refine (sv_fderiv_pdWordR_le hsm u z h).trans ?_
      exact mul_le_mul_of_nonneg_right (hbd (u.length + 1) z) (norm_nonneg _)
    have hm := Convex.norm_image_sub_le_of_norm_fderiv_le (f := pdWordR u (stVel v l))
      (s := (Set.univ : Set (ℝ × ℝ))) hdiff hbound convex_univ (Set.mem_univ x) (Set.mem_univ y)
    calc |pdWordR u (stVel v l) x - pdWordR u (stVel v l) y|
        = ‖pdWordR u (stVel v l) y - pdWordR u (stVel v l) x‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Av (u.length + 1) * ‖y - x‖ := hm
      _ = Av (u.length + 1) * ‖x - y‖ := by rw [norm_sub_rev]

end UnforcedLeray.Short.IIIa
