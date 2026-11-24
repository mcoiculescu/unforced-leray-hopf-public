import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.ChartRuleGen
import UnforcedLeray.Lib.AxisymmetricB.Hessian
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# `RAConvBound` helper: the spatial derivative of a ring lift (source 5036-5039, 5045-5050)

Off the axis, `‖D(N_v α)(y)‖ ≤ 2ϱ⁻¹√s|α_r| + s(|Q_εα|_r + |∂_ηα|_r + |Q_εα|_z + |∂_ηα|_z)`,
`s = R²/ϱ²`, `ε = R⁻¹` (from `liftMerD` and the chain rule `chartAdv_dRho_dz`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rac_abs_ϱD_le (y v : Space) (hy : y ∉ Axi.axis) : |Axi.ϱD y v| ≤ ‖v‖ := by
  have h : Axi.ϱD y v = inner ℝ v (Axi.eR y) := by
    rw [Axi.ϱD_apply, Axi.inner_eR_apply]; ring
  rw [h]
  calc |inner ℝ v (Axi.eR y)| ≤ ‖v‖ * ‖Axi.eR y‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by rw [Axi.norm_eR hy, mul_one]

theorem rac_norm_eRD_le (y v : Space) (hy : y ∉ Axi.axis) :
    ‖Axi.eRD y v‖ ≤ 2 * (Axi.ϱ y)⁻¹ * ‖v‖ := by
  rw [Axi.eRD_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (Axi.ϱ_nonneg y))]
  have h1 : ‖Axi.hor v - Axi.ϱD y v • Axi.eR y‖ ≤ 2 * ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, Axi.norm_eR hy, mul_one]
    linarith [Axi.norm_hor_le v, rac_abs_ϱD_le y v hy]
  calc (Axi.ϱ y)⁻¹ * ‖Axi.hor v - Axi.ϱD y v • Axi.eR y‖ ≤ (Axi.ϱ y)⁻¹ * (2 * ‖v‖) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (Axi.ϱ_nonneg y))
    _ = _ := by ring

theorem rac_Dh_le {R : ℝ} (hR : 0 < R) {α : Chart → Merid} {τ : ℝ} {y : Space}
    (hy : y ∉ Axi.axis) (hα : DifferentiableAt ℝ α (Axi.chart R τ y)) :
    ‖fderiv ℝ (Axi.Nv R α τ) y‖ ≤
      2 * (Axi.ϱ y)⁻¹ * √((Axi.chart R τ y).1) * |α (Axi.chart R τ y) 0| +
      (Axi.chart R τ y).1 * (|(UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) 0| + |Axi.dEta α (Axi.chart R τ y) 0| +
        |(UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) 1| + |Axi.dEta α (Axi.chart R τ y) 1|) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hpne : (Axi.mer y).1 ≠ 0 := fun h => hy ((Axi.mem_axis_iff y).2 h)
  have hpos : 0 < (Axi.mer y).1 := lt_of_le_of_ne (Axi.ϱ_nonneg y) (Ne.symm hpne)
  have hbm : DifferentiableAt ℝ α (Axi.merChart R τ (Axi.mer y)) := by
    rw [← Axi.chart_eq_merChart]; exact hα
  have hG := UnforcedLeray.Short.IIb.chartAdv_sqrtProf_diffAt hR0 hpne hbm
  obtain ⟨hρ, hz⟩ := UnforcedLeray.Short.IIb.chartAdv_dRho_dz R hR α τ (Axi.mer y) hpos hbm
  rw [Axi.Nv_eq_liftMer, (Axi.hasFDerivAt_liftMer hy hG).fderiv]
  set G : ℝ × ℝ → Merid := fun p => √(R ^ 2 / p.1 ^ 2) • α (Axi.merChart R τ p) with hGdef
  have hm : Axi.chart R τ y = Axi.merChart R τ (Axi.mer y) := Axi.chart_eq_merChart R τ y
  have hs : (Axi.merChart R τ (Axi.mer y)).1 = R ^ 2 / (Axi.mer y).1 ^ 2 := rfl
  have hGv : G (Axi.mer y) 0 = √((Axi.chart R τ y).1) * α (Axi.chart R τ y) 0 := by
    simp only [hGdef, PiLp.smul_apply, smul_eq_mul]
    rw [hm, hs]
  have hsq : 0 ≤ √((Axi.chart R τ y).1) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ (Axi.chart R τ y).1 := by rw [hm, hs]; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hnv : ‖v‖ = ‖v‖ := rfl
  have hD : ∀ i : Fin 2, |(fderiv ℝ G (Axi.mer y) (Axi.merD y v)) i| ≤
      ‖v‖ * ((Axi.chart R τ y).1 * (|(UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) i| +
        |Axi.dEta α (Axi.chart R τ y) i|)) := by
    intro i
    rw [Axi.merD_apply, Axi.clm_pair]
    have e1 : fderiv ℝ G (Axi.mer y) (1, 0) = Axi.dRho G (Axi.mer y) := rfl
    have e2 : fderiv ℝ G (Axi.mer y) (0, 1) = Axi.dz G (Axi.mer y) := rfl
    rw [e1, e2, hρ, hz, ← hm]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hs' : R ^ 2 / (Axi.mer y).1 ^ 2 = (Axi.chart R τ y).1 := by rw [hm, hs]
    rw [hs']
    have a1 := rac_abs_ϱD_le y v hy
    have a2 : |v 2| ≤ ‖v‖ := by
      have := PiLp.norm_apply_le v 2
      rwa [Real.norm_eq_abs] at this
    calc _ ≤ |Axi.ϱD y v * ((Axi.chart R τ y).1 * (UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) i)| +
          |v 2 * ((Axi.chart R τ y).1 * Axi.dEta α (Axi.chart R τ y) i)| := abs_add_le _ _
      _ = |Axi.ϱD y v| * ((Axi.chart R τ y).1 * |(UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) i|) +
          |v 2| * ((Axi.chart R τ y).1 * |Axi.dEta α (Axi.chart R τ y) i|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0]
      _ ≤ _ := by
        have b1 := abs_nonneg ((UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) i)
        have b2 := abs_nonneg (Axi.dEta α (Axi.chart R τ y) i)
        nlinarith [mul_nonneg hs0 b1, mul_nonneg hs0 b2, abs_nonneg (Axi.ϱD y v), abs_nonneg (v 2),
          mul_le_mul a1 le_rfl (mul_nonneg hs0 b1) (norm_nonneg v),
          mul_le_mul a2 le_rfl (mul_nonneg hs0 b2) (norm_nonneg v)]
  have hterm : ‖Axi.liftMerD G y v‖ ≤ 2 * (Axi.ϱ y)⁻¹ * √((Axi.chart R τ y).1) *
        |α (Axi.chart R τ y) 0| * ‖v‖ +
      ‖v‖ * ((Axi.chart R τ y).1 * (|(UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) 0| +
        |Axi.dEta α (Axi.chart R τ y) 0|)) +
      ‖v‖ * ((Axi.chart R τ y).1 * (|(UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) 1| +
        |Axi.dEta α (Axi.chart R τ y) 1|)) := by
    unfold Axi.liftMerD
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs, hGv, abs_mul, abs_of_nonneg hsq]
      have := rac_norm_eRD_le y v hy
      calc √((Axi.chart R τ y).1) * |α (Axi.chart R τ y) 0| * ‖Axi.eRD y v‖
          ≤ √((Axi.chart R τ y).1) * |α (Axi.chart R τ y) 0| * (2 * (Axi.ϱ y)⁻¹ * ‖v‖) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    · rw [norm_smul, Real.norm_eq_abs, Axi.norm_eR hy, mul_one]
      exact hD 0
    · rw [norm_smul, Real.norm_eq_abs, Axi.norm_e3, mul_one]
      exact hD 1
  calc _ ≤ _ := hterm
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
