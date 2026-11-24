import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.ErrPressureLap

/-!
# `PartIII-b:C/rep/8/3/2/2`: pointwise conversion `TrainGaussPt` (source 468-478, 2196-2216)

`Σ_jV_j = toVecL⁻¹ ∘ Train.Vc` and `Σ_jp_j = Train.pc` are equalities of functions (no termwise
differentiation), so the flat jets of `v - ΣV_j`, `p - Σp_j` are the Part I jets up to the
sup-vs-`L²` comparison and the nested-Hessian/iterated-derivative identification.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Train (toVecL toVec Vc pc isoV isoP)

theorem tvs_apply (w : UnforcedLeray.Train.Vec) : toVecL.symm w = (w 0, w 1) :=
  (toVecL.symm_apply_eq).2 (UnforcedLeray.Train.eq_toVec w)

theorem tvs_norm_pair_le (v : ℝ × ℝ) : ‖v‖ ≤ ‖toVec v‖ := by
  rw [UnforcedLeray.Train.norm_toVec, Prod.norm_def]
  refine max_le ?_ ?_
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg v.2])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg v.1])

theorem tvs_symm_norm_le (w : UnforcedLeray.Train.Vec) : ‖toVecL.symm w‖ ≤ ‖w‖ := by
  have h := tvs_norm_pair_le (w 0, w 1)
  rw [tvs_apply]
  rwa [← UnforcedLeray.Train.eq_toVec w] at h

theorem tvs_symm_opNorm_le : ‖toVecL.symm.toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    simpa using tvs_symm_norm_le w

theorem gaussV_eq (ν s : ℝ) :
    gaussV ν s = fun x => toVecL.symm (Vc ν (cOf ν) s x) := by
  funext x
  unfold gaussV Vc UnforcedLeray.Gaussian.periodize
  rw [ContinuousLinearEquiv.map_tsum]
  refine tsum_congr fun j => ?_
  rw [UnforcedLeray.Train.isoV_apply, map_smul]
  have : toVecL.symm (toVec (-(x.1 - j * cOf ν, x.2).2, (x.1 - j * cOf ν, x.2).1)) =
      (-(x.1 - j * cOf ν, x.2).2, (x.1 - j * cOf ν, x.2).1) := toVecL.symm_apply_apply _
  rw [this]
  simp only [Vj, xj, Jrot, ageA, sq2, UnforcedLeray.Train.width, Prod.smul_mk, smul_eq_mul]
  ext <;> simp

theorem gaussP_eq (ν s : ℝ) : gaussP ν s = pc ν (cOf ν) s := by
  funext x
  unfold gaussP pc UnforcedLeray.Gaussian.periodize
  refine tsum_congr fun j => ?_
  simp only [pj, xj, isoP, UnforcedLeray.B0146.isoPressure, UnforcedLeray.B0113.pExp,
    UnforcedLeray.B0113.gw, UnforcedLeray.B0113.heatWidth, ageA, sq2,
    GaussianVortex.radiusSq]
  rw [← Real.exp_add]
  have : -((1 + ν * s)⁻¹ * ((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / 4) +
      -((1 + ν * s)⁻¹ * ((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / 4) =
      -((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / (2 * (1 + ν * s)) := by
    field_simp; ring
  rw [this, inv_pow]; ring

theorem tvs_nested_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ × ℝ → E}
    (hg : ContDiff ℝ 2 g) (x u w : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y w) x u = iteratedFDeriv ℝ 2 g x ![u, w] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h1 := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp x hd.hasFDerivAt
  rw [iteratedFDeriv_two_apply]
  have h2 : fderiv ℝ (fun y => fderiv ℝ g y w) x = _ := h1.fderiv
  rw [h2]
  simp

theorem tvs_ei_norm_le (a : Fin 2) : ‖ei a‖ ≤ 1 := by
  fin_cases a <;> simp [ei, Prod.norm_def]

theorem tvs_flatHessNorm_le {f : ℝ × ℝ → UnforcedLeray.Train.Vec} (hf : ContDiff ℝ 2 f)
    (x : ℝ × ℝ) :
    flatHessNorm (fun y => toVecL.symm (f y)) x ≤ 4 * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hg : ContDiff ℝ 2 (fun y => toVecL.symm (f y)) := toVecL.symm.contDiff.comp hf
  have hD : ‖iteratedFDeriv ℝ 2 (fun y => toVecL.symm (f y)) x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
    have e : iteratedFDeriv ℝ 2 (fun y => toVecL.symm (f y)) x =
        toVecL.symm.toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ 2 f x) :=
      ContinuousLinearEquiv.iteratedFDeriv_comp_left (g := toVecL.symm) (f := f) (x := x) (i := 2)
    rw [e]
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) tvs_symm_opNorm_le)
  have hb : ∀ a b : Fin 2, ‖fderiv ℝ (fun y => fderiv ℝ (fun y => toVecL.symm (f y)) y (ei b)) x
      (ei a)‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
    intro a b
    rw [tvs_nested_eq hg]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hp : ∏ i, ‖(![ei a, ei b] : Fin 2 → ℝ × ℝ) i‖ ≤ 1 := by
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact mul_le_one₀ (tvs_ei_norm_le a) (norm_nonneg _) (tvs_ei_norm_le b)
    calc _ ≤ ‖iteratedFDeriv ℝ 2 (fun y => toVecL.symm (f y)) x‖ * 1 :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hD
  unfold flatHessNorm
  simp only [Fin.sum_univ_two]
  have := hb 0 0; have := hb 0 1; have := hb 1 0; have := hb 1 1
  linarith

theorem tvs_mgrad_le {h : ℝ × ℝ → ℝ} (hh : Differentiable ℝ h) (x : ℝ × ℝ) :
    ‖mgrad h x‖ ≤ ‖UnforcedLeray.Train.gradS h x‖ := by
  have e : mgrad h x = (UnforcedLeray.Cyl.partialQ h x, UnforcedLeray.Cyl.partialEta h x) := by
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hh, UnforcedLeray.Cyl.partialEta_eq_fderiv hh]
    rfl
  rw [e]
  exact tvs_norm_pair_le _

/-- **`TrainGaussPt`** (source 468-478, 2196-2216). -/
theorem trainGaussPt : TrainGaussPt := by
  intro L s hs x
  have hν := L.ν_pos
  have hc : 0 < cOf L.ν := inv_pos.2 (by positivity)
  have ha : 0 < UnforcedLeray.Train.width L.ν s := by
    unfold UnforcedLeray.Train.width; positivity
  have hv : ContDiff ℝ 2 (L.train.v s) := by
    have h := L.train.isTrain.smooth_v.comp_contDiff
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (s, z)))
      (fun z => ⟨hs.le, mem_univ _⟩)
    exact (contDiff_infty.1 h 2 : ContDiff ℝ 2 _)
  have hp : ContDiff ℝ 2 (L.train.p s) := by
    have h := L.train.isTrain.smooth_p.comp_contDiff
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (s, z)))
      (fun z => ⟨hs.le, mem_univ _⟩)
    exact (contDiff_infty.1 h 2 : ContDiff ℝ 2 _)
  have hVc : ContDiff ℝ 2 (Vc L.ν (cOf L.ν) s) :=
    (contDiff_infty.1 (Short.Spine.vcReg_contDiff_Vc hc ha) 2)
  have hpc : ContDiff ℝ 2 (pc L.ν (cOf L.ν) s) :=
    (contDiff_infty.1 (Short.PartI.ErrPressureLapAux.pc_contDiff hν hc hs.le) 2)
  set f : ℝ × ℝ → UnforcedLeray.Train.Vec := fun z => L.train.v s z - Vc L.ν (cOf L.ν) s z with hfdef
  set h : ℝ × ℝ → ℝ := fun w => L.train.p s w - pc L.ν (cOf L.ν) s w with hhdef
  have hf : ContDiff ℝ 2 f := hv.sub hVc
  have hh : Differentiable ℝ h := (hp.sub hpc).differentiable (by norm_num)
  have hV : trainDV L s = fun y => toVecL.symm (f y) := by
    funext y
    simp only [trainDV, trainV, gaussV_eq, hfdef, map_sub, tvs_apply]
  have hP : trainDP L s = h := by
    funext y
    simp only [trainDP, trainP, gaussP_eq, hhdef]
  have hA : ‖trainDV L s x‖ ≤ ‖f x‖ := by rw [hV]; exact tvs_symm_norm_le _
  have hB := tvs_flatHessNorm_le hf x
  have hC := tvs_mgrad_le hh x
  unfold trainGaussJet
  have e1 : flatHessNorm (trainDV L s) x = flatHessNorm (fun y => toVecL.symm (f y)) x := by
    rw [hV]
  have e2 : ‖L.train.v s x - Vc L.ν (cOf L.ν) s x‖ = ‖f x‖ := rfl
  rw [e1, hP, e2]
  have := norm_nonneg (f x)
  have := norm_nonneg (iteratedFDeriv ℝ 2 f x)
  have := norm_nonneg (UnforcedLeray.Train.gradS h x)
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
