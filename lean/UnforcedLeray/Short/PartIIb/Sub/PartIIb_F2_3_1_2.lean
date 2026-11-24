import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2.Cont
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2.Mode

/-!
# `PartII-b:F2/3/1/2`: the planar direct modes lie in `X_m` (SP 2167-2171)

Helpers: `Dil.lean` (dilation bound on `L²(⟨x⟩^{2m}dx)`), `Cont.lean` (strong continuity of the
dilation family via density of compactly supported continuous functions), `Polar.lean`
(polar coordinates), `Mode.lean` (the unit-scale mode is in `L²` when `q ∈ X_G`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open PlanarModesHelp

theorem planarModesInXm : UnforcedLeray.Short.IIb.PlanarFrozenF231.PlanarModesInXm := by
  intro m hm Sig lam q hSig hEig
  have hm0 : 0 < m := by linarith
  have hA : 1 ≤ 1 + Sig := by linarith
  set A : ℝ := 1 + Sig with hAdef
  have hg : ∀ i : Fin 2, MemLp (dirModeG q i) 2 (planeMeasure m) := fun i => memLp_Gq m hm0 hEig.memXG i
  let F : Fin 2 → ℝ → Xm m := fun i σ => lpDl m A hm0.le (hg i) (1 + σ)
  have hmaps : MapsTo (fun σ : ℝ => 1 + σ) (Icc 0 Sig) (Icc 1 A) := fun σ hσ =>
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hFc : ∀ i, ContinuousOn (F i) (Icc 0 Sig) := fun i =>
    (continuousOn_lpDl m A hm0.le hA (hg i)).comp (by fun_prop) hmaps
  let proj : Fin 2 → (E2 →L[ℝ] ℝ) := fun i => EuclideanSpace.proj i
  let ι : ℝ → (E2 →L[ℝ] Xm m) := fun σ => ∑ i : Fin 2, (proj i).smulRight (F i σ)
  set B : ℝ := ∑ i : Fin 2, (A ^ (m + 1)) ^ (1 / 2 : ℝ) * (eLpNorm (dirModeG q i) 2 (planeMeasure m)).toReal
    with hB
  have hB0 : 0 ≤ B := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    positivity
  refine ⟨max 1 B, ι, le_max_left _ _, ?_, ?_, ?_⟩
  · refine continuousOn_finset_sum _ (fun i _ => ?_)
    exact ((ContinuousLinearMap.smulRightL ℝ E2 (Xm m) (proj i)).continuous).comp_continuousOn (hFc i)
  · intro σ hσ
    refine (norm_sum_le _ _).trans ?_
    refine (le_max_right 1 B).trans' ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have hp : ‖proj i‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun α => ?_)
      simpa [proj] using PiLp.norm_apply_le α i
    calc ‖proj i‖ * ‖F i σ‖ ≤ 1 * ‖F i σ‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact norm_lpDl_le m A hm0.le hA (hg i) (1 + σ) (hmaps hσ)
  · intro σ hσ α
    have h0 := coeFn_lpDl m A hm0.le (hg 0) (1 + σ) (hmaps hσ)
    have h1 := coeFn_lpDl m A hm0.le (hg 1) (1 + σ) (hmaps hσ)
    have hι : ι σ α = α 0 • F 0 σ + α 1 • F 1 σ := by
      simp [ι, proj, Fin.sum_univ_two, ContinuousLinearMap.sum_apply]
    rw [hι]
    filter_upwards [Lp.coeFn_add (α 0 • F 0 σ) (α 1 • F 1 σ), Lp.coeFn_smul (α 0) (F 0 σ),
      Lp.coeFn_smul (α 1) (F 1 σ), h0, h1] with x hadd hs0 hs1 e0 e1
    rw [hadd, Pi.add_apply, hs0, hs1, Pi.smul_apply, Pi.smul_apply, Fin.sum_univ_two,
      mode_eq_dl, mode_eq_dl]
    have e0' : (F 0 σ : B0579.Plane → ℝ) x = dl (1 + σ) (dirModeG q 0) x := e0
    have e1' : (F 1 σ : B0579.Plane → ℝ) x = dl (1 + σ) (dirModeG q 1) x := e1
    rw [e0', e1']
    simp [smul_eq_mul]

end UnforcedLeray.Short.IIb
