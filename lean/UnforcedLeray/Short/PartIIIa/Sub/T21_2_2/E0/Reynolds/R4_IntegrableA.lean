import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reg
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_9
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.WeightLogBounds
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff

/-!
# `PartIII-a:T21/2/2/2/2/4/3`: integrability of the weight part `reyAPart` (SP 3044-3050, 3060)

On the moving cell the weight bounds of `periodicWeightLogBounds` give `|d ∂_d w| ≤ C w` and
`|y·∇w| ≤ C w`, so `|reyAPart| ≤ ((|C|+1)/θ) w |Φ|²`, and `w|Φ|²` is integrable on the moving cell
by `RevPhiReg`. The integrand is continuous, hence measurable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- `∂_d w = w · ∂_d log w` for the periodic weight. -/
theorem wDd_eq_mul_deriv_log (m d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    wDd m d y = periodicWeight (-m) d y *
      deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d := by
  have hp := UnforcedLeray.Short.IIIa.AdjE1.pw_hasDerivAt_d (-m) d hd.ne' y
  have hl := hp.log (UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) d y).ne'
  unfold wDd
  rw [hp.deriv, hl.deriv]
  field_simp [(UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) d y).ne']

/-- `∂_k w = w · ∂_k log w` for the periodic weight. -/
theorem pd_weight_eq (m d : ℝ) (y : ℝ × ℝ) (k : Fin 2) :
    B0579.pd k (periodicWeight (-m) d) y = periodicWeight (-m) d y *
      B0579.pd k (fun x => Real.log (periodicWeight (-m) d x)) y := by
  have hf := ((UnforcedLeray.Short.IIIa.AdjE1.pw_contDiff (-m) d).differentiable (by simp)) y
  have hpos := UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) d y
  have hl := hf.hasFDerivAt.log hpos.ne'
  unfold B0579.pd
  rw [hl.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hpos.ne', one_mul]

/-- Continuity of `y ↦ ∂_d w(y)`. -/
theorem continuous_wDd (m d : ℝ) (hd : 0 < d) : Continuous (fun y => wDd m d y) := by
  have h : (fun y => wDd m d y) = fun y => WLB.DQ d y * (-m) * WLB.Qf d y ^ (-m - 1) := by
    funext y
    unfold wDd
    rw [(UnforcedLeray.Short.IIIa.AdjE1.pw_hasDerivAt_d (-m) d hd.ne' y).deriv]
  rw [h]
  have hDQ : Continuous (fun y : ℝ × ℝ => WLB.DQ d y) := by unfold WLB.DQ; fun_prop
  have hQ : Continuous (fun y : ℝ × ℝ => WLB.Qf d y) := by unfold WLB.Qf; fun_prop
  exact (hDQ.mul continuous_const).mul
    (hQ.rpow_const (fun y => Or.inl (WLB.Qf_pos d y).ne'))

/-- Continuity of `y ↦ y·∇w(y)`. -/
theorem continuous_wDil (m d : ℝ) : Continuous (fun y => wDil m d y) := by
  have hfd : Continuous (fderiv ℝ (periodicWeight (-m) d)) :=
    (UnforcedLeray.Short.IIIa.AdjE1.pw_contDiff (-m) d).continuous_fderiv (by simp)
  have hpd : ∀ k : Fin 2, Continuous (fun y => B0579.pd k (periodicWeight (-m) d) y) :=
    fun k => hfd.clm_apply continuous_const
  unfold wDil
  exact (continuous_fst.mul (hpd 0)).add (continuous_snd.mul (hpd 1))


/-- The cell-length bound `|d ∂_d w| ≤ |C| w` from the log-derivative bound. -/
theorem wDd_bound (m d C : ℝ) (hd : 0 < d) (y : ℝ × ℝ)
    (h4 : |d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d| ≤ C) :
    |d * wDd m d y| ≤ |C| * periodicWeight (-m) d y := by
  have hp := UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) d y
  rw [wDd_eq_mul_deriv_log m d hd y, show d * (periodicWeight (-m) d y *
      deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d) =
      periodicWeight (-m) d y * (d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d) by ring,
    abs_mul, abs_of_pos hp]
  calc periodicWeight (-m) d y * |d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d|
      ≤ periodicWeight (-m) d y * |C| :=
        mul_le_mul_of_nonneg_left (h4.trans (le_abs_self C)) hp.le
    _ = |C| * periodicWeight (-m) d y := mul_comm _ _

/-- The bound `|y·∇w| ≤ |C| w` from the log-gradient bound. -/
theorem wDil_bound (m d C : ℝ) (y : ℝ × ℝ)
    (h3 : |y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y +
      y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y| ≤ C) :
    |wDil m d y| ≤ |C| * periodicWeight (-m) d y := by
  have hp := UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) d y
  have e : wDil m d y = periodicWeight (-m) d y *
      (y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y +
        y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y) := by
    unfold wDil
    rw [pd_weight_eq, pd_weight_eq]
    ring
  rw [e, abs_mul, abs_of_pos hp]
  calc periodicWeight (-m) d y * |y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y +
        y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y|
      ≤ periodicWeight (-m) d y * |C| := mul_le_mul_of_nonneg_left (h3.trans (le_abs_self C)) hp.le
    _ = |C| * periodicWeight (-m) d y := mul_comm _ _

/-- Pointwise algebra: `|(d/(2θ) ∂_d w + θ⁻¹ w + (2θ)⁻¹ y·∇w) N| ≤ ((|C|+1)/θ) w N`. -/
theorem pt_bound (d wd wl w N θ C : ℝ) (hθ : 0 < θ) (hw : 0 ≤ w) (hN : 0 ≤ N)
    (h1 : |d * wd| ≤ |C| * w) (h2 : |wl| ≤ |C| * w) :
    |(d / (2 * θ) * wd + θ⁻¹ * w + (2 * θ)⁻¹ * wl) * N| ≤ ((|C| + 1) / θ) * (w * N) := by
  have hθ2 : 0 < (2 * θ)⁻¹ := inv_pos.mpr (by linarith)
  have e1 : |d / (2 * θ) * wd| ≤ |C| / (2 * θ) * w := by
    have : d / (2 * θ) * wd = (2 * θ)⁻¹ * (d * wd) := by ring
    rw [this, abs_mul, abs_of_pos hθ2]
    calc (2 * θ)⁻¹ * |d * wd| ≤ (2 * θ)⁻¹ * (|C| * w) :=
          mul_le_mul_of_nonneg_left h1 hθ2.le
      _ = |C| / (2 * θ) * w := by ring
  have e2 : |(2 * θ)⁻¹ * wl| ≤ |C| / (2 * θ) * w := by
    rw [abs_mul, abs_of_pos hθ2]
    calc (2 * θ)⁻¹ * |wl| ≤ (2 * θ)⁻¹ * (|C| * w) :=
          mul_le_mul_of_nonneg_left h2 hθ2.le
      _ = |C| / (2 * θ) * w := by ring
  have e3 : |θ⁻¹ * w| = θ⁻¹ * w := abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) hw)
  have hsum := abs_add_three (d / (2 * θ) * wd) (θ⁻¹ * w) ((2 * θ)⁻¹ * wl)
  rw [abs_mul, abs_of_nonneg hN]
  calc |d / (2 * θ) * wd + θ⁻¹ * w + (2 * θ)⁻¹ * wl| * N
      ≤ (|d / (2 * θ) * wd| + |θ⁻¹ * w| + |(2 * θ)⁻¹ * wl|) * N :=
        mul_le_mul_of_nonneg_right hsum hN
    _ ≤ (|C| / (2 * θ) * w + θ⁻¹ * w + |C| / (2 * θ) * w) * N := by
        rw [e3]
        exact mul_le_mul_of_nonneg_right (add_le_add (add_le_add e1 le_rfl) e2) hN
    _ = ((|C| + 1) / θ) * (w * N) := by
        field_simp
        ring

/-- **Leaf: integrability of the weight part (SP 3044-3050, 3060).** -/
theorem reyIntegrableA (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.E0.ReyIntegrableA m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ
  have hs : 0 ≤ s := le_trans ht hts.le
  have hζ0 : 0 < ζ := hζ.1
  have hr : revAge ν s ζ ∈ Ico t s :=
    Ioo_subset_Ico_self (UnforcedLeray.Short.IIIa.AdjE1.revAge_mem_Ioo_A hν ht hts hζ)
  have hCF := (revPhiReg m hm ν hν tr t s ht hts g φ hφ (revAge ν s ζ) hr).1
  have ha : 0 < clockA ν (revAge ν s ζ) := chgClockA_pos hν hs hζ0
  have hcpos : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hdpos : 0 < revCell ν (ν ^ (-2 : ℝ)) s ζ := by
    unfold revCell cellLen
    exact div_pos hcpos (Real.sqrt_pos.mpr ha)
  have hθ : 0 < revTheta ν s ζ := by
    unfold revTheta clockTheta
    exact inv_pos.mpr (mul_pos hν ha)
  have hint := hCF.int0
  have hC := UnforcedLeray.Short.IIIa.periodicWeightLogBounds (-m)
  obtain ⟨C, hCb⟩ := hC
  have hbd : ∀ y ∈ B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ),
      |revCell ν (ν ^ (-2 : ℝ)) s ζ * wDd m (revCell ν (ν ^ (-2 : ℝ)) s ζ) y| ≤
        |C| * periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y :=
    fun y hy => wDd_bound m _ C hdpos y ((hCb _ hdpos).2.2.2 y hy)
  have hbil : ∀ y ∈ B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ),
      |wDil m (revCell ν (ν ^ (-2 : ℝ)) s ζ) y| ≤
        |C| * periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y :=
    fun y hy => wDil_bound m _ C y ((hCb _ hdpos).2.2.1 y hy)
  have hcont : Continuous (reyAPart m ν s ζ φ) := by
    unfold reyAPart
    have hΦ : Continuous (fun y => ‖revPhi ν φ s ζ y‖ ^ 2) :=
      (hCF.smooth.continuous.norm).pow 2
    exact (((continuous_const.mul (continuous_wDd m _ hdpos)).add
      (continuous_const.mul
        (UnforcedLeray.Short.IIIa.AdjE1.pw_contDiff (-m) _).continuous)).add
      (continuous_const.mul (continuous_wDil m _))).mul hΦ
  refine Integrable.mono' (hint.const_mul ((|C| + 1) / revTheta ν s ζ))
    hcont.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (B0579.measurableSet_cell _) (fun y hy => ?_)
  rw [Real.norm_eq_abs]
  unfold reyAPart
  exact pt_bound _ _ _ _ _ _ C hθ (UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) _ y).le
    (sq_nonneg _) (hbd y hy) (hbil y hy)

end UnforcedLeray.Short.IIIa.E0
