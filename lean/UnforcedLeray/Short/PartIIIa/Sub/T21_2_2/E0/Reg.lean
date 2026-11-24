import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Equiv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.ScaleMemLp
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.PdScale

/-!
# Part III-a, `PartIII-a:T21/2/2/2/3`: regularity of the moving adjoint at a fixed age
(SP 3036-3037, 3044, 3060).

For `r ∈ [t, s)`, `Φ = movingPhi ν φ r = a⁻¹ φ(r, √a ·)` with `a = clockA ν r`, on the cell of
length `d = c/√a`, `c = ν^{-2}`:
* `Φ` is `C^∞` (`mp_smooth`) and `d`-periodic (`mp_periodic`);
* `MemLp Φ 2 (cellMeasure d (-m))` by the scaling leaf `mpScaleMemLp`;
* `∇Φ = a⁻¹√a (∇φ)(√a ·)` (`mpPdScale`), again in `L²(cellMeasure d (-m))`;
* on the cell the periodic weight is dominated by `(π²/4)^m` times the density
  `⟨y⟩^{-2m}` (`adjWeightEquiv`, `hm : 8 < m`), so the `E_0`, `E_1` integrands are integrable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- A continuous `L²(cellMeasure d (-m))` function, multiplied by the periodic weight, is
integrable on the cell (`p_d ≤ (π²/4)^m ⟨y⟩^{-2m}` on the cell, `adjWeightEquiv`). -/
theorem cellWeight_integrableOn_aux (m d : ℝ) (hm : 8 < m) (hd : 0 < d)
    (F : ℝ × ℝ → ℂ) (hF : Continuous F) (hL : MemLp F 2 (B0579.cellMeasure d (-m))) :
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖F y‖ ^ 2) (B0579.cell d) := by
  have hI : Integrable (fun y => ‖F y‖ ^ 2) (B0579.cellMeasure d (-m)) :=
    hL.integrable_norm_pow (by norm_num)
  have hI' : IntegrableOn (fun y => B0579.density (-m) y • ‖F y‖ ^ 2) (B0579.cell d) :=
    (B0579.integrable_cellMeasure_iff d (-m)).mp hI
  have hbound : IntegrableOn (fun y => (Real.pi ^ 2 / 4) ^ m *
      (B0579.density (-m) y • ‖F y‖ ^ 2)) (B0579.cell d) :=
    hI'.const_mul _
  have hpwc : Continuous (periodicWeight (-m) d) := by
    unfold periodicWeight
    exact Continuous.rpow_const (by fun_prop) (fun y => Or.inl (by positivity))
  refine Integrable.mono' hbound ?_
    (ae_restrict_of_forall_mem (B0579.measurableSet_cell d) (fun y hy => ?_))
  · exact (hpwc.mul ((hF.norm).pow 2)).aestronglyMeasurable
  · have hpw0 : 0 ≤ periodicWeight (-m) d y := by
      unfold periodicWeight
      exact Real.rpow_nonneg (by positivity) _
    have hu := ((adjWeightEquiv m hm) d hd).2 y hy
    have h2 := mul_le_mul_of_nonneg_right hu (sq_nonneg ‖F y‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpw0 (sq_nonneg _))]
    simp only [NNReal.smul_def, smul_eq_mul, B0579.coe_density]
    nlinarith [h2]

theorem revPhiReg (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.E0.RevPhiReg m := by
  intro ν hν tr t s ht hts g φ hφ r hr
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr0 : 0 ≤ r := le_trans ht hr.1
  have hrI : r ∈ Icc t s := ⟨hr.1, hr.2.le⟩
  have hrS : ContDiff ℝ ∞ (φ r) := hφ.smooth r hr
  have ha : 0 < clockA ν r := by unfold clockA; nlinarith
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
    unfold cellLen
    exact div_pos hc (Real.sqrt_pos.mpr ha)
  have hcontφ : Continuous (φ r) := hrS.continuous
  have hL0 : MemLp (φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφ.memX r hrI
  have hMP : MemLp (movingPhi ν φ r) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) :=
    mpScaleMemLp m (ν ^ (-2 : ℝ)) (clockA ν r) hc ha ((clockA ν r)⁻¹) (φ r) hcontφ hL0
  have hsmM : ContDiff ℝ ∞ (movingPhi ν φ r) := mp_smooth ν r φ hrS
  have hcontM : Continuous (movingPhi ν φ r) := hsmM.continuous
  refine ⟨?_, hMP⟩
  refine ⟨hsmM.of_le (by norm_num), ?_, ?_, ?_⟩
  · exact fun y => mp_periodic ν (ν ^ (-2 : ℝ)) hc r hr0 hν φ (hφ.periodic r hr) y
  · exact cellWeight_integrableOn_aux m _ hm hd (movingPhi ν φ r) hcontM hMP
  · intro k
    have hcontpd : Continuous (pdCx k (φ r)) := by
      unfold pdCx
      exact (hrS.continuous_fderiv (by simp)).clm_apply continuous_const
    have hpdfun : pdCx k (movingPhi ν φ r) = fun y : ℝ × ℝ =>
        (((clockA ν r)⁻¹ * Real.sqrt (clockA ν r) : ℝ) : ℂ) *
          pdCx k (φ r) (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
      funext fun y => mpPdScale ν hν r hr0 φ hrS k y
    have hMPd : MemLp (fun y : ℝ × ℝ =>
        (((clockA ν r)⁻¹ * Real.sqrt (clockA ν r) : ℝ) : ℂ) *
          pdCx k (φ r) (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) :=
      mpScaleMemLp m (ν ^ (-2 : ℝ)) (clockA ν r) hc ha
        ((clockA ν r)⁻¹ * Real.sqrt (clockA ν r)) (pdCx k (φ r)) hcontpd
        (hφ.memH1 r hr k)
    have hcontF : Continuous (fun y : ℝ × ℝ =>
        (((clockA ν r)⁻¹ * Real.sqrt (clockA ν r) : ℝ) : ℂ) *
          pdCx k (φ r) (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) :=
      continuous_const.mul (hcontpd.comp ((continuous_const.mul continuous_fst).prodMk
        (continuous_const.mul continuous_snd)))
    rw [hpdfun]
    exact cellWeight_integrableOn_aux m _ hm hd _ hcontF hMPd

end UnforcedLeray.Short.IIIa.E0
