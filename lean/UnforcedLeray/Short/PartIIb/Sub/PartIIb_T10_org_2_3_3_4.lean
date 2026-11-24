import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_of
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_3
import UnforcedLeray.Lib.LerayC.Complex
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `PartII-b:T10/org/2/3/3/4`: the complex curl potential (`CurlPotentialC`)

For a smooth compactly supported `F : ℝ³ → ℂ³` in `L^r`, `1 < r < ∞`, split `F` into real and
imaginary component families `fr`, `fi`, and set `A = N ∗ curl fr + i N ∗ curl fi` (componentwise).
Then `A` is smooth with the stated decay (`NewtonCurlDecay`), and
`lerayC F = curl A` a.e. (`RealLerayTestFormula`, `NewtonCurlIdentity`, `coeFn_lerayC`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Euclidean norm of a complex 3-vector is at most the sum of `|re| + |im|` over components. -/
private theorem cp4_norm_le (z : CVec3) :
    ‖z‖ ≤ ∑ k : Fin 3, (|(z k).re| + |(z k).im|) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun k _ => by positivity, ?_⟩
  calc ∑ k : Fin 3, ‖z k‖ ^ 2
      ≤ ∑ k : Fin 3, (|(z k).re| + |(z k).im|) ^ 2 :=
        Finset.sum_le_sum fun k _ =>
          pow_le_pow_left₀ (norm_nonneg _) (Complex.norm_le_abs_re_add_abs_im _) 2
    _ ≤ (∑ k : Fin 3, (|(z k).re| + |(z k).im|)) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => by positivity

/-- Coordinate expansion of a bounded linear functional on `ℝ³`. -/
private theorem cp4_sum_coord (L : Space →L[ℝ] ℝ) (v : Space) :
    L v = ∑ j : Fin 3, v j * L (coordinateVector j) := by
  have hv : v = ∑ j : Fin 3, v j • coordinateVector j := by
    ext i; simp [coordinateVector, Pi.single_apply, mul_ite]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

private theorem cp4_abs_coord_le (v : Space) (j : Fin 3) : |v j| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le v j

/-- Directional bound for a functional whose coordinate values are bounded by `M`. -/
private theorem cp4_dir_bound (L : Space →L[ℝ] ℝ) (M : ℝ)
    (hM : ∀ j : Fin 3, |L (coordinateVector j)| ≤ M) (v : Space) :
    |L v| ≤ 3 * M * ‖v‖ := by
  rw [cp4_sum_coord L v]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin 3, |v j * L (coordinateVector j)| ≤ ∑ j : Fin 3, ‖v‖ * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (cp4_abs_coord_le v j) (hM j) (abs_nonneg _) (norm_nonneg _)
    _ = 3 * M * ‖v‖ := by simp [Finset.sum_const]; ring

/-- Replace a decay constant by a nonnegative one. -/
private theorem cp4_nonneg1 {φ : Fin 3 → Space → ℝ} {p : ℝ}
    (h : ∃ C : ℝ, ∀ k x, |φ k x| ≤ C * (1 + ‖x‖) ^ p) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k x, |φ k x| ≤ D * (1 + ‖x‖) ^ p := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun k x =>
    (hC k x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

/-- Replace a decay constant by a nonnegative one (two indices). -/
private theorem cp4_nonneg2 {φ : Fin 3 → Fin 3 → Space → ℝ} {p : ℝ}
    (h : ∃ C : ℝ, ∀ k j x, |φ k j x| ≤ C * (1 + ‖x‖) ^ p) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k j x, |φ k j x| ≤ D * (1 + ‖x‖) ^ p := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun k j x =>
    (hC k j x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

theorem curlPotentialC_proof : UnforcedLeray.Short.IIb.CurlPotentialC := by
  intro r _ h1 h2 F hFs hFc hF
  obtain ⟨fr, hfr_def⟩ : ∃ fr : Fin 3 → Space → ℝ, ∀ j x, fr j x = reV (F x) j :=
    ⟨fun j x => reV (F x) j, fun _ _ => rfl⟩
  obtain ⟨fi, hfi_def⟩ : ∃ fi : Fin 3 → Space → ℝ, ∀ j x, fi j x = imV (F x) j :=
    ⟨fun j x => imV (F x) j, fun _ _ => rfl⟩
  have hfr : ∀ j, IsSpatialTest (fr j) := by
    intro j
    have e : fr j = fun x => reV (F x) j := funext (hfr_def j)
    rw [e]
    exact ⟨ContDiff.comp (contDiff_piLp_apply (p := 2) (i := j)) (reV.contDiff.comp hFs),
      hFc.comp_left (g := fun z : CVec3 => reV z j) (by simp)⟩
  have hfi : ∀ j, IsSpatialTest (fi j) := by
    intro j
    have e : fi j = fun x => imV (F x) j := funext (hfi_def j)
    rw [e]
    exact ⟨ContDiff.comp (contDiff_piLp_apply (p := 2) (i := j)) (imV.contDiff.comp hFs),
      hFc.comp_left (g := fun z : CVec3 => imV z j) (by simp)⟩
  obtain ⟨hsr, hr2, hr3⟩ := newtonCurlDecay_proof fr hfr
  obtain ⟨hsi, hi2, hi3⟩ := newtonCurlDecay_proof fi hfi
  obtain ⟨Ar2, hAr2_0, hAr2⟩ := cp4_nonneg1 (φ := newtonCurlPotential fr) hr2
  obtain ⟨Ai2, hAi2_0, hAi2⟩ := cp4_nonneg1 (φ := newtonCurlPotential fi) hi2
  obtain ⟨Ar3, hAr3_0, hAr3⟩ :=
    cp4_nonneg2 (φ := fun k j x => spatialTestDerivative j (newtonCurlPotential fr k) x) hr3
  obtain ⟨Ai3, hAi3_0, hAi3⟩ :=
    cp4_nonneg2 (φ := fun k j x => spatialTestDerivative j (newtonCurlPotential fi k) x) hi3
  -- the complex potential `A = N ∗ curl fr + i N ∗ curl fi`
  obtain ⟨A, hA⟩ : ∃ A : Space → CVec3, ∀ y, A y =
      WithLp.toLp 2 (fun k : Fin 3 => ((newtonCurlPotential fr k y : ℝ) : ℂ) +
        ((newtonCurlPotential fi k y : ℝ) : ℂ) * Complex.I) :=
    ⟨fun y => WithLp.toLp 2 (fun k : Fin 3 => ((newtonCurlPotential fr k y : ℝ) : ℂ) +
        ((newtonCurlPotential fi k y : ℝ) : ℂ) * Complex.I), fun y => rfl⟩
  have hAeq : A = fun y => WithLp.toLp 2 (fun k : Fin 3 => ((newtonCurlPotential fr k y : ℝ) : ℂ) +
        ((newtonCurlPotential fi k y : ℝ) : ℂ) * Complex.I) := funext hA
  have hAc : ContDiff ℝ ∞ A := by
    rw [hAeq]
    exact PiLp.contDiff_toLp.comp (contDiff_pi.2 fun k =>
      (Complex.ofRealCLM.contDiff.comp (hsr k)).add
        ((Complex.ofRealCLM.contDiff.comp (hsi k)).mul contDiff_const))
  have hAd : Differentiable ℝ A := hAc.differentiable (by simp)
  have hre_A : ∀ y k, (A y k).re = newtonCurlPotential fr k y := by
    intro y k; rw [hA]; simp
  have him_A : ∀ y k, (A y k).im = newtonCurlPotential fi k y := by
    intro y k; rw [hA]; simp
  -- real and imaginary parts of the derivative of `A`
  have hK1 : ∀ x v k, (fderiv ℝ A x v k).re = fderiv ℝ (newtonCurlPotential fr k) x v := by
    intro x v k
    have hR : HasFDerivAt (fun y => reV (A y)) (reV.comp (fderiv ℝ A x)) x :=
      reV.hasFDerivAt.comp x (hAd x).hasFDerivAt
    have hC : HasFDerivAt (fun y => reV (A y) k)
        ((EuclideanSpace.proj (𝕜 := ℝ) k : Space →L[ℝ] ℝ).comp (reV.comp (fderiv ℝ A x))) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) k : Space →L[ℝ] ℝ).hasFDerivAt.comp x hR
    have hfun : (fun y => reV (A y) k) = newtonCurlPotential fr k :=
      funext fun y => by simp [reV_apply, hre_A]
    rw [hfun] at hC
    have e := hC.unique ((hsr k).differentiable (by simp) x).hasFDerivAt
    rw [← e]
    simp [reV_apply]
  have hK2 : ∀ x v k, (fderiv ℝ A x v k).im = fderiv ℝ (newtonCurlPotential fi k) x v := by
    intro x v k
    have hR : HasFDerivAt (fun y => imV (A y)) (imV.comp (fderiv ℝ A x)) x :=
      imV.hasFDerivAt.comp x (hAd x).hasFDerivAt
    have hC : HasFDerivAt (fun y => imV (A y) k)
        ((EuclideanSpace.proj (𝕜 := ℝ) k : Space →L[ℝ] ℝ).comp (imV.comp (fderiv ℝ A x))) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) k : Space →L[ℝ] ℝ).hasFDerivAt.comp x hR
    have hfun : (fun y => imV (A y) k) = newtonCurlPotential fi k :=
      funext fun y => by simp [imV_apply, him_A]
    rw [hfun] at hC
    have e := hC.unique ((hsi k).differentiable (by simp) x).hasFDerivAt
    rw [← e]
    simp [imV_apply]
  -- the curl of `A`, real and imaginary parts
  have hcurl_re : ∀ x k, (curlC A x k).re = curlR (newtonCurlPotential fr) k x := by
    intro x k
    show (fderiv ℝ A x (EuclideanSpace.single (k + 1) (1 : ℝ)) (k + 2) -
      fderiv ℝ A x (EuclideanSpace.single (k + 2) (1 : ℝ)) (k + 1)).re = _
    rw [Complex.sub_re, hK1, hK1]
    rfl
  have hcurl_im : ∀ x k, (curlC A x k).im = curlR (newtonCurlPotential fi) k x := by
    intro x k
    show (fderiv ℝ A x (EuclideanSpace.single (k + 1) (1 : ℝ)) (k + 2) -
      fderiv ℝ A x (EuclideanSpace.single (k + 2) (1 : ℝ)) (k + 1)).im = _
    rw [Complex.sub_im, hK2, hK2]
    rfl
  -- decay of `A` and of its derivative
  have hAbound2 : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (1 + ‖x‖) ^ (-2 : ℝ) := by
    refine ⟨3 * (Ar2 + Ai2), fun x => ?_⟩
    calc ‖A x‖ ≤ ∑ k : Fin 3, (|(A x k).re| + |(A x k).im|) := cp4_norm_le _
      _ ≤ ∑ k : Fin 3, ((Ar2 + Ai2) * (1 + ‖x‖) ^ (-2 : ℝ)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [hre_A, him_A, add_mul]
          exact add_le_add (hAr2 k x) (hAi2 k x)
      _ = 3 * (Ar2 + Ai2) * (1 + ‖x‖) ^ (-2 : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hAbound3 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ A x‖ ≤ C * (1 + ‖x‖) ^ (-3 : ℝ) := by
    refine ⟨9 * (Ar3 + Ai3), fun x => ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)) (fun v => ?_)
    calc ‖fderiv ℝ A x v‖
        ≤ ∑ k : Fin 3, (|(fderiv ℝ A x v k).re| + |(fderiv ℝ A x v k).im|) := cp4_norm_le _
      _ = ∑ k : Fin 3, (|fderiv ℝ (newtonCurlPotential fr k) x v| +
            |fderiv ℝ (newtonCurlPotential fi k) x v|) := by simp only [hK1, hK2]
      _ ≤ ∑ k : Fin 3, (3 * (Ar3 * (1 + ‖x‖) ^ (-3 : ℝ)) * ‖v‖ +
            3 * (Ai3 * (1 + ‖x‖) ^ (-3 : ℝ)) * ‖v‖) := by
          refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
          · exact cp4_dir_bound (fderiv ℝ (newtonCurlPotential fr k) x)
              (Ar3 * (1 + ‖x‖) ^ (-3 : ℝ)) (fun j => hAr3 k j x) v
          · exact cp4_dir_bound (fderiv ℝ (newtonCurlPotential fi k) x)
              (Ai3 * (1 + ‖x‖) ^ (-3 : ℝ)) (fun j => hAi3 k j x) v
      _ = 9 * (Ar3 + Ai3) * (1 + ‖x‖) ^ (-3 : ℝ) * ‖v‖ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- the Leray projection side
  have hGae : (⇑(reV.compLpL r volume (hF.toLp F)) : Space → Space) =ᵐ[volume] vecField fr := by
    filter_upwards [reV.coeFn_compLpL (μ := volume) (p := r) (hF.toLp F),
      hF.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    ext k
    simp [vecField_apply, hfr_def]
  have hHae : (⇑(imV.compLpL r volume (hF.toLp F)) : Space → Space) =ᵐ[volume] vecField fi := by
    filter_upwards [imV.coeFn_compLpL (μ := volume) (p := r) (hF.toLp F),
      hF.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    ext k
    simp [vecField_apply, hfi_def]
  have hmr : MemLp (vecField fr) r volume :=
    MemLp.ae_eq hGae (Lp.memLp _)
  have hmi : MemLp (vecField fi) r volume :=
    MemLp.ae_eq hHae (Lp.memLp _)
  have hLr_ae : (⇑(lerayLp r h1 h2 (reV.compLpL r volume (hF.toLp F))) : Space → Space)
      =ᵐ[volume] vecField fr + gradField (lerayPotential fr) := by
    have hG : reV.compLpL r volume (hF.toLp F) = hmr.toLp (vecField fr) :=
      Lp.ext (hGae.trans hmr.coeFn_toLp.symm)
    rw [hG]
    exact realLerayTestFormula_proof r h1 h2 fr hfr hmr
  have hLi_ae : (⇑(lerayLp r h1 h2 (imV.compLpL r volume (hF.toLp F))) : Space → Space)
      =ᵐ[volume] vecField fi + gradField (lerayPotential fi) := by
    have hG : imV.compLpL r volume (hF.toLp F) = hmi.toLp (vecField fi) :=
      Lp.ext (hHae.trans hmi.coeFn_toLp.symm)
    rw [hG]
    exact realLerayTestFormula_proof r h1 h2 fi hfi hmi
  -- pointwise identities
  have hid_r : ∀ x, (vecField fr + gradField (lerayPotential fr)) x = reV (curlC A x) := by
    intro x; ext k
    simp only [Pi.add_apply, PiLp.add_apply, vecField_apply, gradField_apply, reV_apply]
    rw [hcurl_re]
    exact newtonCurlIdentity_proof fr hfr k x
  have hid_i : ∀ x, (vecField fi + gradField (lerayPotential fi)) x = imV (curlC A x) := by
    intro x; ext k
    simp only [Pi.add_apply, PiLp.add_apply, vecField_apply, gradField_apply, imV_apply]
    rw [hcurl_im]
    exact newtonCurlIdentity_proof fi hfi k x
  have hae : (⇑(lerayC r h1 h2 (hF.toLp F)) : Space → CVec3) =ᵐ[volume] curlC A := by
    filter_upwards [coeFn_lerayC h1 h2 (hF.toLp F), hLr_ae, hLi_ae] with x hx1 hx2 hx3
    rw [hx1, hx2, hx3, hid_r x, hid_i x]
    exact ofReV_reV_add_ofImV_imV _
  exact ⟨A, hAc, hAbound2, hAbound3, hae⟩

end UnforcedLeray.Short.IIb
