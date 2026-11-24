import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L1.Common

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Gaussian (shiftVec)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **PartIII-b:C/rep/8/3/2/1/3.** Termwise Hessian of the summed velocity (source 4978):
the contraction of the second derivative of `gaussV` is the termwise sum, with summable terms. -/
theorem gaussSumHess : GaussSumHess := by
  intro ν s hν hs A x
  have hc := cOf_ne_zero hν
  set T : ℤ → Fin 2 → Fin 2 → ℝ × ℝ := fun n a b =>
    fderiv ℝ (fun y => fderiv ℝ (Vj ν s n) y (ei b)) x (ei a) with hT
  have hTs : ∀ a b : Fin 2, Summable (fun n : ℤ => T n a b) := by
    intro a b
    exact Summable.of_norm_bounded ((summable_td_translate hν hs x).mul_left 4)
      (fun n => td_hess ν s hν hs n x a b)
  -- step 1: the directional derivative of `gaussV` is the translate sum of `∂_b g`
  have hΦ : ∀ b : Fin 2, (fun y => fderiv ℝ (gaussV ν s) y (ei b)) =
      fun y => ∑' n : ℤ, fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b) := by
    intro b
    funext y
    have HF : HasFDerivAt (gaussV ν s)
        (∑' n : ℤ, fderiv ℝ (fun y => Vj ν s 0 (y - shiftVec (cOf ν) n)) y) y := by
      rw [gaussV_fun]
      exact UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates (C₀ := C16 ν s) (C₁ := C16 ν s)
        ((vj0_contDiff ν s).differentiable (by norm_num)) (by norm_num : (1 : ℝ) < 2) hc
        (fun z => prof_v0 hν hs z) (fun z => prof_v1 hν hs z) y
    rw [HF.fderiv]
    have hsum : Summable (fun n : ℤ => fderiv ℝ (fun y => Vj ν s 0 (y - shiftVec (cOf ν) n)) y) :=
      summable_fderiv_translates (g := Vj ν s 0) hc (fun z => prof_v1 hν hs z) y
    have e := (ContinuousLinearMap.apply ℝ (ℝ × ℝ) (ei b)).map_tsum hsum
    simp only [ContinuousLinearMap.apply_apply] at e
    rw [e]
    refine tsum_congr fun n => ?_
    rw [fderiv_comp_sub]
  -- step 2: differentiate the translate sum once more in the direction `e_a`
  have hD : ∀ b a : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ (gaussV ν s) y (ei b)) x (ei a) = ∑' n : ℤ, T n a b := by
    intro b a
    rw [hΦ b]
    have HΦ := UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates
      (g := fun y => fderiv ℝ (Vj ν s 0) y (ei b)) (hb_diff (ν := ν) (s := s) b)
      (by norm_num : (1 : ℝ) < 2) hc (C₀ := C16 ν s) (C₁ := C16 ν s)
      (fun z => prof_Hb0 hν hs b z) (fun z => prof_Hb1 hν hs b z) x
    have e1 : fderiv ℝ (fun y => ∑' n : ℤ, fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b)) x
        = ∑' n : ℤ, fderiv ℝ (fun y => fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b)) x :=
      HΦ.fderiv
    rw [e1]
    have hsumH : Summable (fun n : ℤ =>
        fderiv ℝ (fun y => fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b)) x) :=
      summable_fderiv_translates (g := fun y => fderiv ℝ (Vj ν s 0) y (ei b)) hc
        (fun z => prof_Hb1 hν hs b z) x
    have e2 : (∑' n : ℤ, fderiv ℝ (fun y => fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b)) x)
        (ei a) = ∑' n : ℤ,
          fderiv ℝ (fun y => fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b)) x (ei a) :=
      (ContinuousLinearMap.apply ℝ (ℝ × ℝ) (ei a)).map_tsum hsumH
    rw [e2]
    refine tsum_congr fun n => ?_
    have hfun : (fun y => fderiv ℝ (Vj ν s n) y (ei b)) =
        fun y => fderiv ℝ (Vj ν s 0) (y - shiftVec (cOf ν) n) (ei b) :=
      funext fun y => by rw [fderiv_Vj_shift_rep8]
    show _ = fderiv ℝ (fun y => fderiv ℝ (Vj ν s n) y (ei b)) x (ei a)
    rw [hfun]
  -- step 3: summing over the entries and over `j`
  have hS : HasSum (fun n : ℤ => ∑ a : Fin 2, ∑ b : Fin 2, A (mi a) (mi b) • T n a b)
      (∑ a : Fin 2, ∑ b : Fin 2, A (mi a) (mi b) • ∑' n : ℤ, T n a b) :=
    hasSum_sum (fun a _ => hasSum_sum (fun b _ => ((hTs a b).hasSum).const_smul _))
  refine ⟨ContinuousLinearMap.hasSum SplitEmb8321.embL hS |>.summable, ?_⟩
  refine Eq.trans ?_ (ContinuousLinearMap.hasSum SplitEmb8321.embL hS).tsum_eq.symm
  show emb (∑ a : Fin 2, ∑ b : Fin 2, A (mi a) (mi b) •
      fderiv ℝ (fun y => fderiv ℝ (gaussV ν s) y (ei b)) x (ei a)) =
    SplitEmb8321.embL (∑ a : Fin 2, ∑ b : Fin 2, A (mi a) (mi b) • ∑' n : ℤ, T n a b)
  simp only [hD]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
