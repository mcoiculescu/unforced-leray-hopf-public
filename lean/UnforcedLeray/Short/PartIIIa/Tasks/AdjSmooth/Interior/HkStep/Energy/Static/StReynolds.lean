import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StCellIbp
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StVelWords
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Comm
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Algebra
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2/3`: Reynolds cancellation (`stReynolds`)

Source of record: `the November 2 reference manuscript` (SP), lines 3062-3064
(Reynolds cancellation) and 270-288 (`div v = 0`).

Route. Write `a_l = stVel v l`, `H_l = a_l F`, `Q = ipX F (stGrad a F)`.
* `Σ_l ∂_l H_l = stGrad a F` pointwise, since `Σ_l ∂_l a_l = div v = 0`.
* `ipX (∂_l F) H_l = ipX F (a_l ∂_l F)` (real coefficients move across the inner product).
* Hence `2 Q = Σ_l (ipX F (∂_l H_l) + ipX (∂_l F) H_l)`, and each bracket is bounded by
  `2|m| ‖F‖ ‖H_l‖ ≤ 2|m| Av0 ‖F‖²` (`stCellIbp`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Real coefficients move across the real part of the inner product. -/
theorem sr_ipX_rmul_left (c m : ℝ) (a : ℝ × ℝ → ℝ) (F G : ℝ × ℝ → ℂ) :
    ipX c m (fun x => ((a x : ℝ) : ℂ) * F x) G = ipX c m F (fun x => ((a x : ℝ) : ℂ) * G x) := by
  simp only [ipX]
  congr 2
  funext x
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- Multiplication by a bounded real field on `X_{-m,c}`, with the norm bound. -/
theorem sr_xNorm_rmul {c m : ℝ} {a : ℝ × ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hac : Continuous a) (ha : ∀ x : ℝ × ℝ, |a x| ≤ A) {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (B0579.cellMeasure c (-m))) :
    (xNorm c (-m) (fun x => ((a x : ℝ) : ℂ) * F x)).toReal ≤ A * (xNorm c (-m) F).toReal := by
  have hle : ∀ᵐ x ∂(B0579.cellMeasure c (-m)),
      ‖((a x : ℝ) : ℂ) * F x‖ ≤ A * ‖F x‖ := by
    refine ae_of_all _ fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _)
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hle 2
  have hfin := hF.eLpNorm_lt_top.ne
  calc (xNorm c (-m) (fun x => ((a x : ℝ) : ℂ) * F x)).toReal
      ≤ (ENNReal.ofReal A * xNorm c (-m) F).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
    _ = A * (xNorm c (-m) F).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]

/-- The derivative `∂_l (a F)` of a product with a smooth real field lies in `X_{-m,c}`. -/
theorem sr_pd_memLp {c m : ℝ} {a : ℝ × ℝ → ℝ} {A B : ℝ} (l : Fin 2) (ha : ContDiff ℝ ∞ a)
    (hab : ∀ x : ℝ × ℝ, |a x| ≤ A) (hdb : ∀ x : ℝ × ℝ, |B0579.pd l a x| ≤ B)
    {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFm : MemLp F 2 (B0579.cellMeasure c (-m)))
    (hFd : MemLp (pdCx l F) 2 (B0579.cellMeasure c (-m))) :
    MemLp (pdCx l (fun x => ((a x : ℝ) : ℂ) * F x)) 2 (B0579.cellMeasure c (-m)) := by
  have hcont : Continuous a := ha.continuous
  have hBc : Continuous (B0579.pd l a) := (st_pd_contDiff ha l).continuous
  have hpd : pdCx l (fun x => ((a x : ℝ) : ℂ) * F x) = fun x =>
      ((B0579.pd l a x : ℝ) : ℂ) * F x + ((a x : ℝ) : ℂ) * pdCx l F x :=
    st_pdCx_ofReal_mul (ha.differentiable (by simp)) (st_differentiable hF) l
  rw [hpd]
  exact (st_rmul_memLp hBc hdb hFm).add (st_rmul_memLp hcont hab hFd)

/-- One term of the Reynolds identity: `|Φ_l| ≤ 2|m| ‖F‖ · A ‖F‖` for `H = a F`. -/
theorem sr_phi {c m : ℝ} (hc : 0 < c) (l : Fin 2) {a : ℝ × ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (ha : ContDiff ℝ ∞ a) (hap : ∀ x : ℝ × ℝ, a (x.1 + c, x.2) = a x)
    (hab : ∀ x : ℝ × ℝ, |a x| ≤ A) (hdb : ∀ x : ℝ × ℝ, |B0579.pd l a x| ≤ B)
    {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFp : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x)
    (hFm : MemLp F 2 (B0579.cellMeasure c (-m)))
    (hFd : MemLp (pdCx l F) 2 (B0579.cellMeasure c (-m))) :
    |ipX c m F (pdCx l (fun x => ((a x : ℝ) : ℂ) * F x)) +
        ipX c m (pdCx l F) (fun x => ((a x : ℝ) : ℂ) * F x)| ≤
      2 * |m| * (xNorm c (-m) F).toReal * (A * (xNorm c (-m) F).toReal) := by
  have hcont : Continuous a := ha.continuous
  have hH : ContDiff ℝ ∞ (fun x => ((a x : ℝ) : ℂ) * F x) :=
    (Complex.ofRealCLM.contDiff.comp ha).mul hF
  have hHp : ∀ x : ℝ × ℝ, (fun x => ((a x : ℝ) : ℂ) * F x) (x.1 + c, x.2) =
      (fun x => ((a x : ℝ) : ℂ) * F x) x :=
    st_rmul_periodic hap hFp
  have hHm : MemLp (fun x => ((a x : ℝ) : ℂ) * F x) 2 (B0579.cellMeasure c (-m)) :=
    st_rmul_memLp hcont hab hFm
  have hHd : MemLp (pdCx l (fun x => ((a x : ℝ) : ℂ) * F x)) 2 (B0579.cellMeasure c (-m)) :=
    sr_pd_memLp l ha hab hdb hF hFm hFd
  have hcib := stCellIbp c m l F (fun x => ((a x : ℝ) : ℂ) * F x) hc hF hH hFp hHp hFm hHm hFd hHd
  have hxH := sr_xNorm_rmul hA hcont hab hFm
  have hs : 0 ≤ 2 * |m| * (xNorm c (-m) F).toReal :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg m)) ENNReal.toReal_nonneg
  exact hcib.trans (mul_le_mul_of_nonneg_left hxH hs)

/-- **Reynolds cancellation** (proved from `stCellIbp` and `stVelWords`). -/
theorem stReynolds : UnforcedLeray.Short.IIIa.StReynolds := by
  intro c m v Av F hc hv hF hFp hX
  have hFm : MemLp F 2 (B0579.cellMeasure c (-m)) := by
    have h := hX []
    simpa [adjSpatial] using h
  have hFd : ∀ l : Fin 2, MemLp (pdCx l F) 2 (B0579.cellMeasure c (-m)) := by
    intro l
    have h := hX [l]
    simpa [adjSpatial] using h
  have hFdiff : Differentiable ℝ F := st_differentiable hF
  have hac : ∀ l : Fin 2, ContDiff ℝ ∞ (stVel v l) := fun l => st_vel_contDiff hv l
  have hadiff : ∀ l : Fin 2, Differentiable ℝ (stVel v l) := fun l =>
    (hac l).differentiable (by simp)
  have hA0 : 0 ≤ Av 0 := st_Av0_nonneg hv
  have hpdb : ∀ l : Fin 2, ∀ x : ℝ × ℝ, |B0579.pd l (stVel v l) x| ≤ Av 1 := by
    intro l x
    have h := (stVelWords c v Av hv [l] l).2.2.1 x
    simpa [pdWordR] using h
  -- divergence free: `∂_0 v_0 + ∂_1 v_1 = 0`
  have hdiv : ∀ x : ℝ × ℝ, B0579.pd 0 (stVel v 0) x + B0579.pd 1 (stVel v 1) x = 0 := by
    intro x
    have h := hv.2.2.1 x
    unfold UnforcedLeray.Cyl.divergence at h
    have hd0 : Differentiable ℝ (fun w => v w 0) := (hac 0).differentiable (by simp)
    have hd1 : Differentiable ℝ (fun w => v w 1) := (hac 1).differentiable (by simp)
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hd0, UnforcedLeray.Cyl.partialEta_eq_fderiv hd1] at h
    have e0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
    have e1 : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := rfl
    unfold B0579.pd
    rw [e0, e1]
    exact h
  -- pointwise: `Σ_l ∂_l(a_l F) = stGrad a F`
  have hpt : ∀ x : ℝ × ℝ,
      pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y) x +
        pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y) x = stGrad (stVel v) F x := by
    intro x
    have e0 : pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y) x =
        ((B0579.pd 0 (stVel v 0) x : ℝ) : ℂ) * F x + ((stVel v 0 x : ℝ) : ℂ) * pdCx 0 F x :=
      congrFun (st_pdCx_ofReal_mul (hadiff 0) hFdiff 0) x
    have e1 : pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y) x =
        ((B0579.pd 1 (stVel v 1) x : ℝ) : ℂ) * F x + ((stVel v 1 x : ℝ) : ℂ) * pdCx 1 F x :=
      congrFun (st_pdCx_ofReal_mul (hadiff 1) hFdiff 1) x
    have hsum : ((B0579.pd 0 (stVel v 0) x : ℝ) : ℂ) + ((B0579.pd 1 (stVel v 1) x : ℝ) : ℂ) = 0 := by
      exact_mod_cast hdiv x
    rw [e0, e1]
    simp only [stGrad, Fin.sum_univ_two]
    linear_combination (F x) * hsum
  have hstsplit : (fun x => pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y) x +
      pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y) x) = stGrad (stVel v) F :=
    funext hpt
  have hgsplit : stGrad (stVel v) F = fun x => ((stVel v 0 x : ℝ) : ℂ) * pdCx 0 F x +
      ((stVel v 1 x : ℝ) : ℂ) * pdCx 1 F x := by
    funext x
    simp only [stGrad, Fin.sum_univ_two]
  -- the per-component memberships
  have hP0 : MemLp (pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y)) 2
      (B0579.cellMeasure c (-m)) :=
    sr_pd_memLp 0 (hac 0) (fun x => st_vel_abs_le hv 0 x) (fun x => hpdb 0 x) hF hFm (hFd 0)
  have hP1 : MemLp (pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y)) 2
      (B0579.cellMeasure c (-m)) :=
    sr_pd_memLp 1 (hac 1) (fun x => st_vel_abs_le hv 1 x) (fun x => hpdb 1 x) hF hFm (hFd 1)
  have hG0 : MemLp (fun y => ((stVel v 0 y : ℝ) : ℂ) * pdCx 0 F y) 2
      (B0579.cellMeasure c (-m)) :=
    st_velMul_memLp hv (hFd 0) 0
  have hG1 : MemLp (fun y => ((stVel v 1 y : ℝ) : ℂ) * pdCx 1 F y) 2
      (B0579.cellMeasure c (-m)) :=
    st_velMul_memLp hv (hFd 1) 1
  -- splitting the inner products
  have hQ1 : ipX c m F (stGrad (stVel v) F) =
      ipX c m F (pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y)) +
        ipX c m F (pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y)) := by
    rw [← hstsplit]
    exact st_ipX_add_right hFm hP0 hP1
  have hQ2 : ipX c m F (stGrad (stVel v) F) =
      ipX c m F (fun y => ((stVel v 0 y : ℝ) : ℂ) * pdCx 0 F y) +
        ipX c m F (fun y => ((stVel v 1 y : ℝ) : ℂ) * pdCx 1 F y) := by
    rw [hgsplit]
    exact st_ipX_add_right hFm hG0 hG1
  -- the transport-side terms move onto `F`
  have hI0 : ipX c m (pdCx 0 F) (fun x => ((stVel v 0 x : ℝ) : ℂ) * F x) =
      ipX c m F (fun y => ((stVel v 0 y : ℝ) : ℂ) * pdCx 0 F y) :=
    (st_ipX_comm c m _ _).trans (sr_ipX_rmul_left c m (stVel v 0) F (pdCx 0 F))
  have hI1 : ipX c m (pdCx 1 F) (fun x => ((stVel v 1 x : ℝ) : ℂ) * F x) =
      ipX c m F (fun y => ((stVel v 1 y : ℝ) : ℂ) * pdCx 1 F y) :=
    (st_ipX_comm c m _ _).trans (sr_ipX_rmul_left c m (stVel v 1) F (pdCx 1 F))
  -- the two Cauchy-Schwarz bounds
  have h0 := sr_phi hc 0 hA0 (hac 0) (fun x => st_vel_periodic hv 0 x)
    (fun x => st_vel_abs_le hv 0 x) (fun x => hpdb 0 x) hF hFp hFm (hFd 0)
  have h1 := sr_phi hc 1 hA0 (hac 1) (fun x => st_vel_periodic hv 1 x)
    (fun x => st_vel_abs_le hv 1 x) (fun x => hpdb 1 x) hF hFp hFm (hFd 1)
  have e : 2 * |m| * (xNorm c (-m) F).toReal * (Av 0 * (xNorm c (-m) F).toReal) =
      2 * |m| * Av 0 * (xNorm c (-m) F).toReal ^ 2 := by ring
  rw [e] at h0 h1
  -- `2 Q = Φ_0 + Φ_1`
  have hsum : ipX c m F (pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y)) +
      ipX c m (pdCx 0 F) (fun x => ((stVel v 0 x : ℝ) : ℂ) * F x) +
      (ipX c m F (pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y)) +
      ipX c m (pdCx 1 F) (fun x => ((stVel v 1 x : ℝ) : ℂ) * F x)) =
      2 * ipX c m F (stGrad (stVel v) F) := by
    linarith [hQ1, hQ2, hI0, hI1]
  have habs : |2 * ipX c m F (stGrad (stVel v) F)| ≤
      |ipX c m F (pdCx 0 (fun y => ((stVel v 0 y : ℝ) : ℂ) * F y)) +
        ipX c m (pdCx 0 F) (fun x => ((stVel v 0 x : ℝ) : ℂ) * F x)| +
      |ipX c m F (pdCx 1 (fun y => ((stVel v 1 y : ℝ) : ℂ) * F y)) +
        ipX c m (pdCx 1 F) (fun x => ((stVel v 1 x : ℝ) : ℂ) * F x)| := by
    rw [← hsum]
    exact abs_add_le _ _
  have h2 : |2 * ipX c m F (stGrad (stVel v) F)| = 2 * |ipX c m F (stGrad (stVel v) F)| := by
    rw [abs_mul, abs_two]
  rw [h2] at habs
  linarith [habs, h0, h1]

end UnforcedLeray.Short.IIIa
