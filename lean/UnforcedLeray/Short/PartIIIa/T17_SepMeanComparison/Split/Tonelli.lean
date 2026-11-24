import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T17
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split.Periodic
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split.Scale

/-!
# Split helper: Tonelli over `(τ, λ, z)` for the thin source (T17/1)

For `thinMoment c G < ∞`, the phase integral of `∫₀¹∫|T(τ+2 log λ, z)| dz dλ` over one period is
finite (`τ`-integration over a period removes the dependence on `λ` and the radial variable).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem t17s_meas_tn (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j) :
    Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => tensorNorm (G w.1 w.2.1 w.2.2) := by
  unfold tensorNorm
  exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => (hG i j).pow_const 2)

theorem t17s_meas_coord (i : Fin 3) : Measurable fun z : Space => z i := by
  exact (EuclideanSpace.proj i).continuous.measurable

theorem t17s_meas_src (ε : ℝ) (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j) :
    Measurable fun p : ℝ × Space => srcNorm (thinSource ε G) p.1 p.2 := by
  have hm : Measurable fun p : ℝ × Space => ((ε * p.2 0, ε * p.2 1), p.2 2,
      ε⁻¹ * Real.log (ε * Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2)) + p.1 / (2 * ε)) := by
    have h0 : Measurable fun p : ℝ × Space => p.2 0 := (t17s_meas_coord 0).comp measurable_snd
    have h1 : Measurable fun p : ℝ × Space => p.2 1 := (t17s_meas_coord 1).comp measurable_snd
    have h2 : Measurable fun p : ℝ × Space => p.2 2 := (t17s_meas_coord 2).comp measurable_snd
    refine ((measurable_const.mul h0).prodMk (measurable_const.mul h1)).prodMk (h2.prodMk ?_)
    refine (measurable_const.mul (Real.measurable_log.comp (measurable_const.mul
      (Measurable.sqrt ((h0.pow_const 2).add (h1.pow_const 2)))))).add
      (measurable_fst.div_const _)
  have := (ENNReal.measurable_ofReal.comp (t17s_meas_tn G hG)).comp hm
  exact this

theorem t17s_phase_integral (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hper : ∀ x' Y q, G x' Y (q + c) = G x' Y q) (σ : ℝ) (z : Space) :
    ∫⁻ τ in Ioc 0 (2 * ε * c), srcNorm (thinSource ε G) (τ + σ) z =
      ENNReal.ofReal (2 * ε) * ∫⁻ q in Ioc 0 c,
        ENNReal.ofReal (tensorNorm (G (ε * z 0, ε * z 1) (z 2) q)) := by
  have := t17s_affine_lintegral c ε hc hε
    (fun q => ENNReal.ofReal (tensorNorm (G (ε * z 0, ε * z 1) (z 2) q)))
    (fun q => by simp [hper]) (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + σ / (2 * ε))
  rw [← this]
  refine lintegral_congr fun τ => ?_
  unfold srcNorm thinSource
  congr 3
  ring

/-- Hölder on one period: `∫_0^c f ≤ c (c⁻¹ ∫_0^c f²)^{1/2}`. -/
theorem t17s_holder (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ q, 0 ≤ f q) :
    ∫⁻ q in Ioc 0 c, ENNReal.ofReal (f q) ≤
      ENNReal.ofReal c * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q ^ 2)) ^ (1 / 2 : ℝ) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc 0 c)) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun q => ENNReal.ofReal (f q)) (g := fun _ => 1)
    (ENNReal.measurable_ofReal.comp hf).aemeasurable measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, one_mul] at hH
  have hsq : ∀ q, ENNReal.ofReal (f q) ^ (2 : ℝ) = ENNReal.ofReal (f q ^ 2) := by
    intro q
    rw [ENNReal.ofReal_rpow_of_nonneg (hf0 q) (by norm_num)]
    norm_num
  simp_rw [hsq] at hH
  refine hH.trans ?_
  have hc0 : (ENNReal.ofReal c) ≠ 0 := by simpa using hc
  have e1 : ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (f q ^ 2) =
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ioc 0 c, ENNReal.ofReal (f q ^ 2) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  have e2 : (ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) * (ENNReal.ofReal c) ^ (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2), ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le),
      inv_mul_cancel₀ hc.ne']
    simp
  have e3 : ENNReal.ofReal c = (ENNReal.ofReal c) ^ (1 / 2 : ℝ) * (ENNReal.ofReal c) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  refine le_of_eq ?_
  calc (∫⁻ q in Ioc 0 c, ENNReal.ofReal (f q ^ 2)) ^ (1 / 2 : ℝ) * ENNReal.ofReal c ^ (1 / 2 : ℝ)
      = (ENNReal.ofReal c ^ (1 / 2 : ℝ) * (ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ)) *
        ((∫⁻ q in Ioc 0 c, ENNReal.ofReal (f q ^ 2)) ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal c ^ (1 / 2 : ℝ) := by
        rw [mul_comm (ENNReal.ofReal c ^ (1 / 2 : ℝ)), e2, one_mul]
    _ = (ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal c ^ (1 / 2 : ℝ)) *
        ((ENNReal.ofReal c⁻¹) ^ (1 / 2 : ℝ) * (∫⁻ q in Ioc 0 c, ENNReal.ofReal (f q ^ 2)) ^ (1 / 2 : ℝ)) := by
        ring
    _ = _ := by rw [← e3]

end UnforcedLeray.Short.IIIa

end
