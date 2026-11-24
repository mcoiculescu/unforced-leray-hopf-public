import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanXHess

/-!
# `PartIII-b:C/rep/8/2/2/2/org`: second derivative of `Y = (-½y·∇ - νΔ + μ + ½)G`

Source `the November 2 reference manuscript`
5380-5387, 5438-5448.  For `G` of class `C⁴` on `ℝ³`,
`‖D²(y·∇G)(v)‖ ≤ ‖D³G(v)‖‖v‖ + 2‖D²G(v)‖` (Leibniz: `D²(DG·id)`, `D²id = 0`),
`‖D²ΔG(v)‖ ≤ 3‖D⁴G(v)‖` (the Laplacian is a sum of three evaluations of `D²G`), whence
`‖D²Y(v)‖ ≤ ½(‖D³G‖‖v‖ + 2‖D²G‖) + 3ν‖D⁴G‖ + |μ+½|‖D²G‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanYHessCalc

variable {G : Vec3 → Vec3}

theorem norm_single_le (j : Fin 3) : ‖(Pi.single j 1 : Vec3)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by
    by_cases h : k = j <;> simp [h]

theorem norm_iter2_id (v : Vec3) : ‖iteratedFDeriv ℝ 2 (id : Vec3 → Vec3) v‖ = 0 := by
  have h1 := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (id : Vec3 → Vec3)) (x := v) (n := 1))
  have h2 : fderiv ℝ (id : Vec3 → Vec3) = fun _ => ContinuousLinearMap.id ℝ Vec3 := by
    funext y; exact fderiv_id
  rw [← h1, h2, norm_iteratedFDeriv_one]
  simp

theorem A_bound (hG : ContDiff ℝ 4 G) (v : Vec3) :
    ‖iteratedFDeriv ℝ 2 (fun y => fderiv ℝ G y y) v‖ ≤
      ‖iteratedFDeriv ℝ 3 G v‖ * ‖v‖ + 2 * ‖iteratedFDeriv ℝ 2 G v‖ := by
  have hf : ContDiff ℝ 3 (fderiv ℝ G) := hG.fderiv_right (m := 3) (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply (f := fderiv ℝ G) (g := (id : Vec3 → Vec3)) (N := 3)
    (n := 2) hf contDiff_id v (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, one_mul] at h
  have e0 : ‖iteratedFDeriv ℝ (2 - 0) (id : Vec3 → Vec3) v‖ = 0 := norm_iter2_id v
  have e1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ G) v‖ = ‖iteratedFDeriv ℝ 2 G v‖ :=
    norm_iteratedFDeriv_fderiv (n := 1)
  have e2 : ‖iteratedFDeriv ℝ 2 (fderiv ℝ G) v‖ = ‖iteratedFDeriv ℝ 3 G v‖ :=
    norm_iteratedFDeriv_fderiv (n := 2)
  have e3 : ‖iteratedFDeriv ℝ 1 (id : Vec3 → Vec3) v‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one, fderiv_id]; exact ContinuousLinearMap.norm_id_le
  have e4 : ‖iteratedFDeriv ℝ 0 (id : Vec3 → Vec3) v‖ = ‖v‖ := by
    simp
  simp only [Nat.sub_zero, Nat.reduceSub, e0, e1, e2, e4] at h
  have e5 := norm_nonneg (iteratedFDeriv ℝ 2 G v)
  have e6 : 2 * ‖iteratedFDeriv ℝ 2 G v‖ * ‖iteratedFDeriv ℝ 1 (id : Vec3 → Vec3) v‖ ≤
      2 * ‖iteratedFDeriv ℝ 2 G v‖ := by
    calc _ ≤ 2 * ‖iteratedFDeriv ℝ 2 G v‖ * 1 := by gcongr
      _ = _ := by ring
  have e7 := norm_nonneg (iteratedFDeriv ℝ 0 (fderiv ℝ G) v)
  have h' : ‖iteratedFDeriv ℝ 2 (fun y => fderiv ℝ G y y) v‖ ≤
      ‖iteratedFDeriv ℝ 0 (fderiv ℝ G) v‖ * 0 +
        2 * ‖iteratedFDeriv ℝ 2 G v‖ * ‖iteratedFDeriv ℝ 1 (id : Vec3 → Vec3) v‖ +
        ‖iteratedFDeriv ℝ 3 G v‖ * ‖v‖ := h
  linarith [e6]

/-- `Δ G = Σ_j D²G(e_j, e_j)`. -/
theorem vecLap_eq (hG : ContDiff ℝ 4 G) :
    vecLap G = fun y => ∑ j : Fin 3, fderiv ℝ (fderiv ℝ G) y (Pi.single j 1) (Pi.single j 1) := by
  have hf : ContDiff ℝ 3 (fderiv ℝ G) := hG.fderiv_right (m := 3) (by norm_num)
  funext y
  unfold vecLap
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hf.differentiable (by norm_num)) y
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single j (1 : ℝ) : Vec3))]
  simp

theorem lap_contDiff (hG : ContDiff ℝ 4 G) : ContDiff ℝ 2 (vecLap G) := by
  have hf : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ G)) :=
    (hG.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)
  rw [vecLap_eq hG]
  refine ContDiff.sum fun j _ => ?_
  exact (hf.clm_apply contDiff_const).clm_apply contDiff_const

theorem lap_bound (hG : ContDiff ℝ 4 G) (v : Vec3) :
    ‖iteratedFDeriv ℝ 2 (vecLap G) v‖ ≤ 3 * ‖iteratedFDeriv ℝ 4 G v‖ := by
  have hf : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ G)) :=
    (hG.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)
  have e4 : ‖iteratedFDeriv ℝ 2 (fderiv ℝ (fderiv ℝ G)) v‖ = ‖iteratedFDeriv ℝ 4 G v‖ := by
    rw [norm_iteratedFDeriv_fderiv (n := 2)]
    exact norm_iteratedFDeriv_fderiv (n := 3)
  have term : ∀ j : Fin 3, ‖iteratedFDeriv ℝ 2
      (fun y => fderiv ℝ (fderiv ℝ G) y (Pi.single j 1) (Pi.single j 1)) v‖ ≤
      ‖iteratedFDeriv ℝ 4 G v‖ := by
    intro j
    set e : Vec3 := Pi.single j 1 with he
    have he1 : ‖e‖ ≤ 1 := norm_single_le j
    have hf2 : ContDiff ℝ 2 (fun y => fderiv ℝ (fderiv ℝ G) y e) := hf.clm_apply contDiff_const
    have h1 := norm_iteratedFDeriv_clm_apply_const (f := fun y => fderiv ℝ (fderiv ℝ G) y e)
      (c := e) (x := v) (N := 2) (n := 2) hf2.contDiffAt le_rfl
    have h2 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ (fderiv ℝ G))
      (c := e) (x := v) (N := 2) (n := 2) hf.contDiffAt le_rfl
    rw [e4] at h2
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ 4 G v‖ := norm_nonneg _
    calc _ ≤ ‖e‖ * ‖iteratedFDeriv ℝ 2 (fun y => fderiv ℝ (fderiv ℝ G) y e) v‖ := h1
      _ ≤ ‖e‖ * (‖e‖ * ‖iteratedFDeriv ℝ 4 G v‖) := by gcongr
      _ ≤ 1 * (1 * ‖iteratedFDeriv ℝ 4 G v‖) := by gcongr
      _ = _ := by ring
  rw [vecLap_eq hG]
  have hs : (fun y => ∑ j : Fin 3, fderiv ℝ (fderiv ℝ G) y (Pi.single j 1) (Pi.single j 1)) =
      ∑ j : Fin 3, (fun y => fderiv ℝ (fderiv ℝ G) y (Pi.single j 1) (Pi.single j 1)) := by
    funext y; simp
  rw [hs, iteratedFDeriv_sum_apply (fun j _ => ((hf.clm_apply contDiff_const).clm_apply
    contDiff_const).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 4 G v‖ := Finset.sum_le_sum fun j _ => term j
    _ = _ := by simp

theorem Yf_contDiff (hG : ContDiff ℝ 4 G) (ν μ : ℝ) : ContDiff ℝ 2 (JetClockCore.Yf G ν μ) := by
  have hf : ContDiff ℝ 3 (fderiv ℝ G) := hG.fderiv_right (m := 3) (by norm_num)
  have hA : ContDiff ℝ 2 (fun y => fderiv ℝ G y y) :=
    (hf.of_le (by norm_num)).clm_apply contDiff_id
  have e : JetClockCore.Yf G ν μ = fun y => (-(1 / 2 : ℝ)) • fderiv ℝ G y y - ν • vecLap G y +
      (μ + 1 / 2) • G y := rfl
  rw [e]
  exact ((hA.const_smul _).sub ((lap_contDiff hG).const_smul _)).add
    ((hG.of_le (by norm_num)).const_smul _)

theorem Yf_iter2 (hG : ContDiff ℝ 4 G) (ν μ : ℝ) (v : Vec3) :
    ‖iteratedFDeriv ℝ 2 (JetClockCore.Yf G ν μ) v‖ ≤
      (1 / 2) * (‖iteratedFDeriv ℝ 3 G v‖ * ‖v‖ + 2 * ‖iteratedFDeriv ℝ 2 G v‖) +
        |ν| * (3 * ‖iteratedFDeriv ℝ 4 G v‖) + |μ + 1 / 2| * ‖iteratedFDeriv ℝ 2 G v‖ := by
  have hf : ContDiff ℝ 3 (fderiv ℝ G) := hG.fderiv_right (m := 3) (by norm_num)
  have hA : ContDiff ℝ 2 (fun y => fderiv ℝ G y y) :=
    (hf.of_le (by norm_num)).clm_apply contDiff_id
  have hL := lap_contDiff hG
  have hG2 : ContDiff ℝ 2 G := hG.of_le (by norm_num)
  have e : JetClockCore.Yf G ν μ = (fun y => (-(1 / 2 : ℝ)) • fderiv ℝ G y y) - (fun y => ν • vecLap G y) +
      (fun y => (μ + 1 / 2) • G y) := rfl
  have c1 : ContDiffAt ℝ 2 (fun y => (-(1 / 2 : ℝ)) • fderiv ℝ G y y) v :=
    (hA.const_smul _).contDiffAt
  have c2 : ContDiffAt ℝ 2 (fun y => ν • vecLap G y) v := (hL.const_smul _).contDiffAt
  have c3 : ContDiffAt ℝ 2 (fun y => (μ + 1 / 2) • G y) v := (hG2.const_smul _).contDiffAt
  have c12 : ContDiffAt ℝ 2 ((fun y => (-(1 / 2 : ℝ)) • fderiv ℝ G y y) -
      (fun y => ν • vecLap G y)) v := c1.sub c2
  rw [e, iteratedFDeriv_add_apply c12 c3, iteratedFDeriv_sub_apply c1 c2,
    iteratedFDeriv_const_smul_apply' hA.contDiffAt, iteratedFDeriv_const_smul_apply' hL.contDiffAt,
    iteratedFDeriv_const_smul_apply' hG2.contDiffAt]
  have a1 := A_bound hG v
  have a2 := lap_bound hG v
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left a1 (by norm_num)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left a2 (abs_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs]

end MeanYHessCalc

end UnforcedLeray.Short.PartIIIb.Concrete
end
