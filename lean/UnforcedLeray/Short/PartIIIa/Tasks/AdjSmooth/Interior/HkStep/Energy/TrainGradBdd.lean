import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel.Bridge

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/4`: the vorticity gradient satisfies the coefficient hypotheses

Source of record: `the November 2 reference manuscript` (SP), lines 270-288,
2866-2870, 3052-3058.  `B_l = ∂_l Ec(r)` is smooth and `c`-periodic on each slice, and its
weighted derivatives are the weighted derivatives of `Ec` one order higher (`TrainSTJets`,
second conjunct), through the exact slice identity of `Bridge.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem trainGradBdd : UnforcedLeray.Short.IIIa.TrainGradBdd := by
  intro ν c tr m S hS hJ i
  unfold TrainSTJets at hJ
  choose C hC using hJ
  refine ⟨∑ k ∈ Finset.range (i + 1), |C k|, fun r hr => ?_⟩
  have hr0 : 0 ≤ r := hr.1
  have hEc : ContDiff ℝ ∞ (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr r y) :=
    slice_contDiff (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (Ec_contDiffOn tr) hr0
  have hper : ∀ z : ℝ × ℝ,
      UnforcedLeray.B0238.Ec tr r (z.1 + c, z.2) = UnforcedLeray.B0238.Ec tr r z := by
    intro z
    have hp1 : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => tr.v r w 1) :=
      fun w => congrArg (fun u => u 1) (tr.isTrain.periodic_v r hr0 w)
    have hp0 : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => tr.v r w 0) :=
      fun w => congrArg (fun u => u 0) (tr.isTrain.periodic_v r hr0 w)
    unfold UnforcedLeray.B0238.Ec UnforcedLeray.Cyl.curl
    rw [hp1.partialQ z, hp0.partialEta z]
  have hdiff : ∀ l : Fin 2,
      ContDiff ℝ ∞ (UnforcedLeray.B0579.pd l (UnforcedLeray.B0238.Ec tr r)) :=
    fun l => (contDiff_infty_iff_fderiv.1 hEc).2.clm_apply contDiff_const
  have hfun : (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr r (y + ((c : ℝ), (0 : ℝ)))) =
      UnforcedLeray.B0238.Ec tr r := by
    funext y
    have e : y + ((c : ℝ), (0 : ℝ)) = (y.1 + c, y.2) := by
      ext <;> simp
    rw [e]
    exact hper y
  have hk : ∀ y : ℝ × ℝ,
      fderiv ℝ (UnforcedLeray.B0238.Ec tr r) (y + ((c : ℝ), (0 : ℝ))) =
        fderiv ℝ (UnforcedLeray.B0238.Ec tr r) y := by
    intro y
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := UnforcedLeray.B0238.Ec tr r)
      (a := ((c : ℝ), (0 : ℝ))) (x := y)
    rw [hfun] at this
    exact this.symm
  have hpperiod : ∀ (l : Fin 2) (x : ℝ × ℝ),
      UnforcedLeray.B0579.pd l (UnforcedLeray.B0238.Ec tr r) (x.1 + c, x.2) =
        UnforcedLeray.B0579.pd l (UnforcedLeray.B0238.Ec tr r) x := by
    intro l x
    unfold UnforcedLeray.B0579.pd
    have e2 : ((x.1 + c, x.2) : ℝ × ℝ) = x + ((c : ℝ), (0 : ℝ)) := by
      ext <;> simp
    rw [e2, hk]
  refine ⟨hdiff, hpperiod, ?_⟩
  intro l i' hi' x
  have hw : 0 ≤ (1 + x.2 ^ 2) ^ ((m + 1) / 2) := Real.rpow_nonneg (by positivity) _
  have hd : ‖UnforcedLeray.B0579.dir l‖ ≤ 1 := by
    fin_cases l <;> simp [UnforcedLeray.B0579.dir, Prod.norm_def]
  have h1 : ‖iteratedFDeriv ℝ i' (UnforcedLeray.B0579.pd l (UnforcedLeray.B0238.Ec tr r)) x‖ ≤
      ‖UnforcedLeray.B0579.dir l‖ * ‖iteratedFDeriv ℝ (i' + 1)
        (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr r y) x‖ := by
    have := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ (UnforcedLeray.B0238.Ec tr r))
      (c := UnforcedLeray.B0579.dir l) (x := x) (n := i')
      ((contDiff_infty_iff_fderiv.1 hEc).2.contDiffAt) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at this
    exact this
  have h2 : ‖iteratedFDeriv ℝ (i' + 1) (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr r y) x‖ ≤
      ‖iteratedFDerivWithin ℝ (i' + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (r, x)‖ :=
    slice_iteratedFDeriv_le (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (Ec_contDiffOn tr) hr0 (i' + 1) x
  have h3 := (hC i' r hr x).2
  have hA : C i' ≤ ∑ k ∈ Finset.range (i + 1), |C k| :=
    le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun k => |C k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi')))
  have h4 : ‖iteratedFDeriv ℝ i' (UnforcedLeray.B0579.pd l (UnforcedLeray.B0238.Ec tr r)) x‖ ≤
      ‖iteratedFDeriv ℝ (i' + 1) (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr r y) x‖ :=
    h1.trans (mul_le_of_le_one_left (norm_nonneg _) hd)
  have h5 := mul_le_mul_of_nonneg_left (h4.trans h2) hw
  linarith [h3, hA, h5]

end UnforcedLeray.Short.IIIa
