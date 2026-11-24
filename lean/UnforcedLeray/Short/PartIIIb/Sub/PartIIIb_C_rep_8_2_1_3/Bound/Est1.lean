import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Chain

/-!
# One-step jet bounds for the profile operators (`PartIII-b:C/rep/8/2/1/3/b`, helper 5)

Source lines 5464-5465.  With `ω = 1 + |η|`: `J n (P_m F) ≤ 7ω J (n+1) F`, and the raised stream
and the raw profile satisfy `J n rawH ≤ 7ω J (n+1) ψ̃`, `J n b̂ ≤ J n ṽ + J n rawH`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem J_Pm {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {m : ℝ} (hm : |m| ≤ 2) {n : ℕ} (hn : n ≤ 2)
    {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    J n (Pm ε m F) z ≤ 7 * (1 + |z.2.2|) * J (n + 1) F z := by
  unfold Pm
  refine (J_Gop _ _ _ _ _ n hF z).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (J_nonneg _ _ _)
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have e1 : |(-2 * ε)| = 2 * ε := by
    rw [abs_of_nonpos (by linarith)]; ring
  have e2 : |(-ε)| = ε := by rw [abs_neg, abs_of_nonneg h0]
  have e3 : |(-(m * ε))| ≤ 2 := by
    rw [abs_neg, abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg m]
  have hη := abs_nonneg z.2.2
  rw [e1, e2]
  simp only [abs_one, abs_zero]
  nlinarith [mul_nonneg h0 hη, mul_nonneg h0 (Nat.cast_nonneg (α := ℝ) n)]

theorem J_T {m : ℝ} (hm : |m| ≤ 2) {n : ℕ} (hn : n ≤ 2) {F : Zc → E} (hF : ContDiff ℝ ∞ F)
    (z : Zc) : J n (Gop 0 2 0 1 m F) z ≤ 7 * (1 + |z.2.2|) * J (n + 1) F z := by
  refine (J_Gop _ _ _ _ _ n hF z).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (J_nonneg _ _ _)
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have hη := abs_nonneg z.2.2
  simp only [abs_one, abs_zero, abs_two, one_mul]
  nlinarith

theorem J_Zo {n : ℕ} {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    J n (Zo F) z ≤ J (n + 1) F z := by
  unfold Zo
  refine (J_Gop _ _ _ _ _ n hF z).trans ?_
  simp

theorem J_Dq {n : ℕ} {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    J n (Gop 1 0 0 0 0 F) z ≤ J (n + 1) F z := by
  refine (J_Gop _ _ _ _ _ n hF z).trans ?_
  simp

theorem J_neg' (n : ℕ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    J n (fun z => -F z) z = J n F z := by
  have h := J_smul n hF (-1) z
  simp only [neg_smul, one_smul, abs_neg, abs_one, one_mul] at h
  exact h

theorem Pm_add_smul (ε m t : ℝ) {F G : Zc → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    Pm ε m (fun z => F z + t • G z) = fun z => Pm ε m F z + t • Pm ε m G z := by
  unfold Pm
  exact Gop_add_smul _ _ _ _ _ hF hG t

theorem Zo_add_smul (t : ℝ) {F G : Zc → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    Zo (fun z => F z + t • G z) = fun z => Zo F z + t • Zo G z := by
  unfold Zo
  exact Gop_add_smul _ _ _ _ _ hF hG t

theorem Pm_eq_fun (ε m : ℝ) (F : Zc → E) :
    Pm ε m F = fun z => Gop 1 0 0 0 0 F z + (-ε) • Gop 0 2 0 1 m F z := by
  funext z
  unfold Pm Gop
  module

end

/-! ### The raised stream and the raw profile -/

theorem J_rawH (L : ReturnLevel) {n : ℕ} (hn : n ≤ 2) (z : Zc) :
    J n (rawH L) z ≤ 7 * (1 + |z.2.2|) * J (n + 1) (trainFpsi L) z := by
  have h : rawH L = fun z => -(Gop 0 2 0 1 (-1) (trainFpsi L) z) := funext (rawH_eq_Gop L)
  rw [h, J_neg' n (contDiff_Gop _ _ _ _ _ (trainFpsi_contDiff L))]
  exact J_T (by norm_num) hn (trainFpsi_contDiff L) z

theorem J_hTil (L : ReturnLevel) (n : ℕ) (z : Zc) : J n (hTil L) z ≤ J n (rawH L) z := by
  unfold J
  refine Finset.sum_le_sum fun k _ => ?_
  have hL : hTil L = (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) rawE1) ∘ rawH L := by
    funext z; simp [hTil]
  rw [hL]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left (N := ∞) _
    (contDiff_rawH L).contDiffAt (by simp)).trans ?_
  have : ‖ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) rawE1‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp [norm_smul, rawE1_norm]
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ k (rawH L) z‖ := by gcongr
    _ = _ := one_mul _

theorem J_rawPhi (L : ReturnLevel) (h1 : L.ε ≤ 1) (n : ℕ) (z : Zc) :
    J n (rawPhi L) z ≤ J n (trainFv L) z + J n (rawH L) z := by
  rw [rawPhi_eq]
  refine (J_add_le n (contDiff_trainFv L) ((contDiff_hTil L).const_smul L.ε) z).trans ?_
  have hs := J_smul n (contDiff_hTil L) L.ε z
  have := J_hTil L n z
  have hε := L.ε_pos
  rw [abs_of_pos hε] at hs
  have hJ := J_nonneg n (hTil L) z
  have : L.ε * J n (hTil L) z ≤ J n (hTil L) z := by nlinarith
  linarith [J_hTil L n z]

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
