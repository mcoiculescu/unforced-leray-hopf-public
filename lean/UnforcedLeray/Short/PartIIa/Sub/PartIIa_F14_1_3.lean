import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Sub.F08
import UnforcedLeray.Lib.HeatR3B.FreeLp
import UnforcedLeray.Lib.LerayC.Dilate
import UnforcedLeray.Lib.LerayC.Transfer
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent

/-!
# Part II-a, `PartII-a:F14/1/3`: the three Leray-commutation leaves of `Sub/F08.lean`

Source `the November 2 reference manuscript` lines 1358-1359 and 1498-1500
("Leray commutes with heat, dilation and phase translation").  We prove, for all exponents:

* `lerayCFreeComm` : `𝐏 S_ν(r) = S_ν(r) 𝐏` on `L^p(ℝ³;ℂ³)`
  (`S_ν(r) = e^{r/2} · dilation ∘ heat`, `freeEvolutionLp_rep_heatLp`);
* `lerayYPhaseTComm` : `𝐏 𝒯_ν(r) = 𝒯_ν(r) 𝐏` on `Y_q`;
* `lerayYResolventComm` : `𝐏 R_μ = R_μ 𝐏` for the Laplace integral `R_μ` (Bochner integral commutes
  with a bounded linear map; integrability as in `bodyResolvent_exists_of`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Real level: `𝐏 S_ν(r) = S_ν(r) 𝐏` on `L^p(ℝ³;ℝ³)`. -/
theorem lerayLp_freeSemigroupLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) (ν r : ℝ)
    (u : Lp Space p (volume : Measure Space)) :
    lerayLp p hp1 hp (B0418.freeSemigroupLp hp ν r u) =
      B0418.freeSemigroupLp hp ν r (lerayLp p hp1 hp u) := by
  have hb : 0 < Real.exp (r / 2) := Real.exp_pos _
  have key : ∀ v : Lp Space p (volume : Measure Space),
      B0418.freeSemigroupLp hp ν r v =
        Real.exp (r / 2) • dilateLp p hp hb.ne'
          (Heat.heatLp (AddMonoidHom.id Space) continuous_id (ν * (Real.exp r - 1)) v) := by
    intro v
    apply Lp.ext
    have h1 := Heat.freeEvolutionLp_rep_heatLp hp ν r v
    have h2 := coeFn_dilateLp hp hb.ne'
      (Heat.heatLp (AddMonoidHom.id Space) continuous_id (ν * (Real.exp r - 1)) v)
    have h3 := Lp.coeFn_smul (Real.exp (r / 2))
      (dilateLp p hp hb.ne'
        (Heat.heatLp (AddMonoidHom.id Space) continuous_id (ν * (Real.exp r - 1)) v))
    filter_upwards [h1, h2, h3] with x a b c
    rw [c, Pi.smul_apply, b]
    exact a
  rw [key, key, map_smul, lerayLp_dilate_apply hp1 hp hb, lerayLp_heat_apply hp1 hp]

theorem re_lerayC (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (lerayC p hp1 hp F) = lerayLp p hp1 hp (reV.compLpL p volume F) := by
  rw [lerayC_apply, map_add, B0414.reV_ofReV_compLpL, B0414.reV_ofImV_compLpL, add_zero]

theorem im_lerayC (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (lerayC p hp1 hp F) = lerayLp p hp1 hp (imV.compLpL p volume F) := by
  rw [lerayC_apply, map_add, B0414.imV_ofReV_compLpL, B0414.imV_ofImV_compLpL, zero_add]

theorem lerayCFreeComm : LerayCFreeComm := by
  intro p _ hp1 hp ν r
  ext1 F
  simp only [ContinuousLinearMap.comp_apply, B0421.freeC]
  apply B0421.ext_reim
  · rw [re_lerayC, B0421.re_cx, B0421.re_cx, re_lerayC, lerayLp_freeSemigroupLp]
  · rw [im_lerayC, B0421.im_cx, B0421.im_cx, im_lerayC, lerayLp_freeSemigroupLp]

theorem lerayYPhaseTComm : LerayYPhaseTComm := by
  intro q _ hq1 hq P _ ν r g
  have hN : ((lerayC q hq1 hq).restrictScalars ℝ).comp ((B0421.freeC hq ν r).restrictScalars ℝ) =
      ((B0421.freeC hq ν r).restrictScalars ℝ).comp ((lerayC q hq1 hq).restrictScalars ℝ) := by
    ext1 F
    exact congrArg (fun T : Lp CVec3 q (volume : Measure Space) →L[ℂ] _ => T F)
      (lerayCFreeComm q hq1 hq ν r)
  have h := lerayY_comm_slicewise (P := P) hq1 hq _ hN
  have h2 := congrArg (fun T => T (DomAddAct.mk (-(r : AddCircle P)) +ᵥ g)) h
  have h3 := lerayY_phase (P := P) hq1 hq (-(r : AddCircle P)) g
  change lerayY P q hq1 hq ((B0421.freeC hq ν r).compLpL q AddCircle.haarAddCircle
      (DomAddAct.mk (-(r : AddCircle P)) +ᵥ g)) =
    (B0421.freeC hq ν r).compLpL q AddCircle.haarAddCircle
      (DomAddAct.mk (-(r : AddCircle P)) +ᵥ lerayY P q hq1 hq g)
  rw [← h3]
  exact h2

theorem lerayYResolventComm : LerayYResolventComm := by
  intro r _ h1 h3 P _ ν hν μ hμ Rm hRm f
  have hq : r ≠ ⊤ := ne_top_of_lt h3
  have hdec : FreeCSharpDecay := freeCSharpDecay_of normLiftExists_proof freeCPointwiseLe_proof
  set a : ℝ := μ.re + gammaR r with ha
  have hnorm : ∀ t : ℝ, 0 ≤ t → ∀ f : Yq P r,
      ‖Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f‖ ≤ Real.exp (-a * t) * ‖f‖ := by
    intro t ht f
    rw [norm_smul, Complex.norm_exp]
    have hre : (-(μ * (t : ℂ))).re = -(μ.re * t) := by simp
    rw [hre]
    have h2 : ‖B0421.phaseT hq ν t f‖ ≤ Real.exp (-B0418.gammaExp r * t) * ‖f‖ :=
      ((B0421.phaseT hq ν t).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right
          ((B0421.norm_phaseT_le hq ν t).trans (hdec r hq ν t ht)) (norm_nonneg _))
    calc Real.exp (-(μ.re * t)) * ‖B0421.phaseT hq ν t f‖
        ≤ Real.exp (-(μ.re * t)) * (Real.exp (-B0418.gammaExp r * t) * ‖f‖) := by gcongr
      _ = Real.exp (-a * t) * ‖f‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        simp only [ha, gammaR, B0418.gammaExp]
        ring
  have hint : IntegrableOn
      (fun t : ℝ => Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f) (Ioi (0 : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ => Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f)
        (Ioi (0 : ℝ)) := by
      have hc1 : Continuous fun t : ℝ => Complex.exp (-(μ * (t : ℂ))) := by fun_prop
      exact hc1.continuousOn.smul
        ((B0421.continuousOn_phaseT hq hν.le f).mono Ioi_subset_Ici_self)
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine Integrable.mono' (hexp.mul_const ‖f‖) (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => hnorm t (le_of_lt ht) f)
  rw [hRm f, hRm (lerayY P r h1 hq f)]
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [map_smul]
  rw [lerayYPhaseTComm r h1 hq P ν t f]

end UnforcedLeray.Short.PartIIa
