import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.PlanarKernel

/-!
# Part II-b, task `PartII-b:F1/3`: planar interaction operator compactness and norm continuity

Proves `planarInteractionCompactStep_proof : PlanarInteractionCompactStep` (SP lines 2133–2140).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.B0579

/-! ## 1. Radius-`r` near/far planar Biot–Savart kernel split -/

/-- Near planar Biot–Savart kernel at radius `r`: `K_{ℝ²}(z) 1_{‖z‖ < r}`. -/
def kPlNearR (r : ℝ) : Plane → Cyl.Vec2 :=
  (Metric.ball (0 : Plane) r).indicator planarBSKernel

/-- Far planar Biot–Savart kernel at radius `r`: `K_{ℝ²}(z) 1_{‖z‖ ≥ r}`. -/
def kPlFarR (r : ℝ) : Plane → Cyl.Vec2 :=
  (Metric.ball (0 : Plane) r)ᶜ.indicator planarBSKernel

theorem kPlNearR_add_kPlFarR (r : ℝ) (z : Plane) :
    kPlNearR r z + kPlFarR r z = planarBSKernel z :=
  indicator_self_add_compl_apply _ _ _

theorem measurable_kPlNearR (r : ℝ) : Measurable (kPlNearR r) :=
  measurable_planarBSKernel.indicator Metric.isOpen_ball.measurableSet

theorem measurable_kPlFarR (r : ℝ) : Measurable (kPlFarR r) :=
  measurable_planarBSKernel.indicator Metric.isOpen_ball.measurableSet.compl

theorem norm_kPlFarR_le {r : ℝ} (hr : 0 < r) (z : Plane) :
    ‖kPlFarR r z‖ ≤ 2 * r⁻¹ := by
  by_cases hz : z ∈ Metric.ball (0 : Plane) r
  · rw [kPlFarR, indicator_of_notMem (Set.notMem_compl_iff.mpr hz), norm_zero]
    positivity
  · rw [kPlFarR, indicator_of_mem (mem_compl hz)]
    have hrz : r ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hrz
      linarith
    have hnear := norm_planarBSKernel_le_near hz0
    rw [Real.rpow_neg_one] at hnear
    have hinv : ‖z‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrz
    linarith

theorem norm_kPlFarR_coord_le {r : ℝ} (hr : 0 < r) (z : Plane) (i : Fin 2) :
    |kPlFarR r z i| ≤ 2 * r⁻¹ := by
  have h1 := PiLp.norm_apply_le (kPlFarR r z) i
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (norm_kPlFarR_le hr z)

theorem norm_kPlNearR_le_kPlNear {r : ℝ} (hr : r ≤ 1) (y : Plane) :
    ‖kPlNearR r y‖ₑ ≤ ‖kPlNear y‖ₑ := by
  by_cases hy : y ∈ Metric.ball (0 : Plane) r
  · have hy1 : y ∈ Metric.ball (0 : Plane) 1 := Metric.ball_subset_ball hr hy
    rw [kPlNearR, kPlNear, indicator_of_mem hy, indicator_of_mem hy1]
  · rw [kPlNearR, indicator_of_notMem hy, enorm_zero]
    exact zero_le

theorem lintegral_kPlNearR_le {r : ℝ} (hr : r ≤ 1) :
    ∫⁻ y : Plane, ‖kPlNearR r y‖ₑ ≤ ENNReal.ofReal plSplitConst :=
  (lintegral_mono fun y => norm_kPlNearR_le_kPlNear hr y).trans
    planarBSKernel_split.choose_spec.2

theorem tendsto_lintegral_kPlNearR :
    Tendsto (fun n : ℕ => ∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ) atTop (𝓝 0) := by
  have hfin : ∫⁻ y : Plane, ‖kPlNear y‖ₑ ≠ ∞ :=
    (planarBSKernel_split.choose_spec.2.trans_lt ENNReal.ofReal_lt_top).ne
  have h0 : ∀ᵐ y ∂(volume : Measure Plane), y ≠ 0 := by
    rw [ae_iff]; simp [measure_singleton]
  have hdom : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure Plane),
      ‖kPlNearR (B0061.rad n) y‖ₑ ≤ ‖kPlNear y‖ₑ := fun n =>
    Eventually.of_forall (norm_kPlNearR_le_kPlNear (B0061.rad_le_one n))
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := (volume : Measure Plane))
    (F := fun n y => ‖kPlNearR (B0061.rad n) y‖ₑ)
    (f := fun _ => 0)
    (bound := fun y => ‖kPlNear y‖ₑ)
    (fun n => (measurable_kPlNearR (B0061.rad n)).enorm)
    hdom hfin
    (by
      filter_upwards [h0] with y hy0
      have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hyp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hr : B0061.rad n < ‖y‖ := by
        refine lt_of_le_of_lt ?_ hN
        unfold B0061.rad
        gcongr
      have hnot : y ∉ Metric.ball (0 : Plane) (B0061.rad n) := by
        simpa [mem_ball_zero_iff] using hr.le
      simp [kPlNearR, indicator_of_notMem hnot])
  simpa using h

/-! ## 2. Near/far planar velocity split and `L²` Young estimate -/

theorem eLpNorm_volume_le_norm_Xm {m : ℝ} (hm : 0 ≤ m) (f : Xm m) :
    eLpNorm (f : Plane → ℝ) 2 volume ≤ ENNReal.ofReal ‖f‖ := by
  refine (eLpNorm_volume_le_planeMeasure hm f).trans (le_of_eq ?_)
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

theorem integrable_of_Xm {m : ℝ} (hm : 1 < m) (f : Xm m) :
    Integrable (f : Plane → ℝ) volume :=
  integrable_of_memLp_planeMeasure hm (Lp.stronglyMeasurable f).measurable (Lp.eLpNorm_lt_top f)

/-- Near planar Biot–Savart velocity at radius `r`: `∫ f(y) kPlNearR r (x - y) dy`. -/
def uPlNearR (r : ℝ) (f : Plane → ℝ) (x : Plane) : Cyl.Vec2 :=
  ∫ y : Plane, f y • kPlNearR r (x - y)

/-- Far planar Biot–Savart velocity at radius `r`: `∫ f(y) kPlFarR r (x - y) dy`. -/
def uPlFarR (r : ℝ) (f : Plane → ℝ) (x : Plane) : Cyl.Vec2 :=
  ∫ y : Plane, f y • kPlFarR r (x - y)

theorem uPlNearR_eq_reflect (r : ℝ) (f : Plane → ℝ) (x : Plane) :
    uPlNearR r f x = ∫ y : Plane, f (x - y) • kPlNearR r y := by
  unfold uPlNearR
  have h := integral_sub_left_eq_self (fun y : Plane => f (x - y) • kPlNearR r y) volume x
  simp only [sub_sub_cancel] at h
  exact h

theorem stronglyMeasurable_uPlNearR (r : ℝ) {f : Plane → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (uPlNearR r f) := by
  have hF : StronglyMeasurable (Function.uncurry fun x y : Plane => f y • kPlNearR r (x - y)) :=
    (hf.comp_measurable measurable_snd).smul
      ((measurable_kPlNearR r).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact hF.integral_prod_right

theorem eLpNorm_uPlNearR_le {r m : ℝ} (hm : 0 ≤ m) (f : Xm m) :
    eLpNorm (uPlNearR r f) 2 volume ≤
      (∫⁻ y : Plane, ‖kPlNearR r y‖ₑ) * ENNReal.ofReal ‖f‖ := by
  have hf_meas : Measurable (f : Plane → ℝ) := (Lp.stronglyMeasurable f).measurable
  have heq : uPlNearR r f = fun x => ∫ y : Plane, f (x - y) • kPlNearR r y :=
    funext (uPlNearR_eq_reflect r f)
  rw [heq]
  have hF : AEStronglyMeasurable
      (Function.uncurry fun x y : Plane => f (x - y) • kPlNearR r y)
      ((volume : Measure Plane).prod volume) :=
    ((hf_meas.comp (measurable_fst.sub measurable_snd)).smul
      ((measurable_kPlNearR r).comp measurable_snd)).aestronglyMeasurable
  have h1 := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hF
    (p := 2) one_le_two ENNReal.ofNat_ne_top
  have h2 : (∫⁻ y : Plane, eLpNorm (fun x => f (x - y) • kPlNearR r y) 2 volume) =
      (∫⁻ y : Plane, ‖kPlNearR r y‖ₑ) * eLpNorm (f : Plane → ℝ) 2 volume := by
    calc ∫⁻ y : Plane, eLpNorm (fun x => f (x - y) • kPlNearR r y) 2 volume
        = ∫⁻ y : Plane, ‖kPlNearR r y‖ₑ * eLpNorm (f : Plane → ℝ) 2 volume := by
          refine lintegral_congr fun y => ?_
          have e : eLpNorm (fun x => f (x - y) • kPlNearR r y) 2 volume =
              eLpNorm (‖kPlNearR r y‖ • fun x => f (x - y)) 2 volume :=
            eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
              simp only [Pi.smul_apply, norm_smul, norm_norm]; ring)
          have hshift : eLpNorm (fun x => f (x - y)) 2 volume =
              eLpNorm (f : Plane → ℝ) 2 volume :=
            eLpNorm_comp_measurePreserving (f := fun x => x - y) hf_meas.aestronglyMeasurable
              (measurePreserving_sub_right volume y)
          rw [e, eLpNorm_const_smul, enorm_norm, hshift]
      _ = (∫⁻ y : Plane, ‖kPlNearR r y‖ₑ) * eLpNorm (f : Plane → ℝ) 2 volume :=
          lintegral_mul_const _ (measurable_kPlNearR r).enorm
  exact (h1.trans_eq h2).trans
    (mul_le_mul_of_nonneg_left (eLpNorm_volume_le_norm_Xm hm f) bot_le)

theorem ae_integrable_kPlNearR {r m : ℝ} (hr : r ≤ 1) (hm : 1 < m) (f : Xm m) :
    ∀ᵐ x ∂(volume : Measure Plane),
      Integrable (fun y => f y • kPlNearR r (x - y)) volume := by
  have hf_meas : Measurable (f : Plane → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hf_int : Integrable (f : Plane → ℝ) volume := integrable_of_Xm hm f
  have h_pt : ∀ x : Plane,
      ∫⁻ y : Plane, ‖f y • kPlNearR r (x - y)‖ₑ =
        ∫⁻ y : Plane, ‖f (x - y)‖ₑ * ‖kPlNearR r y‖ₑ := by
    intro x
    have hrefl := (Measure.measurePreserving_sub_left volume x).lintegral_comp
      (f := fun w => ‖f (x - w) • kPlNearR r w‖ₑ)
      (((hf_meas.comp (measurable_const.sub measurable_id)).smul (measurable_kPlNearR r)).enorm)
    have heq : (fun y : Plane => ‖f (x - (x - y)) • kPlNearR r (x - y)‖ₑ) =
        fun y => ‖f y • kPlNearR r (x - y)‖ₑ := by
      funext y; rw [sub_sub_cancel]
    change (∫⁻ y : Plane, ‖f (x - (x - y)) • kPlNearR r (x - y)‖ₑ) = _ at hrefl
    rw [heq] at hrefl
    rw [hrefl]
    refine lintegral_congr fun y => ?_
    rw [enorm_smul]
  have h_meas_inner : Measurable fun x : Plane =>
      ∫⁻ y : Plane, ‖f y • kPlNearR r (x - y)‖ₑ := by
    have hF : Measurable fun p : Plane × Plane => ‖f p.2 • kPlNearR r (p.1 - p.2)‖ₑ :=
      ((hf_meas.comp measurable_snd).smul
        ((measurable_kPlNearR r).comp (measurable_fst.sub measurable_snd))).enorm
    exact hF.lintegral_prod_right'
  have h_tot : ∫⁻ x : Plane, ∫⁻ y : Plane, ‖f y • kPlNearR r (x - y)‖ₑ < ∞ := by
    simp_rw [h_pt]
    have hF2 : AEMeasurable (Function.uncurry fun x y : Plane =>
        ‖f (x - y)‖ₑ * ‖kPlNearR r y‖ₑ)
        ((volume : Measure Plane).prod volume) :=
      (((hf_meas.comp (measurable_fst.sub measurable_snd)).enorm).mul
        ((measurable_kPlNearR r).comp measurable_snd).enorm).aemeasurable
    rw [lintegral_lintegral_swap hF2]
    have h_shift : ∀ y : Plane,
        ∫⁻ x : Plane, ‖f (x - y)‖ₑ * ‖kPlNearR r y‖ₑ =
          (∫⁻ x : Plane, ‖f x‖ₑ) * ‖kPlNearR r y‖ₑ := by
      intro y
      have hmx : Measurable fun x : Plane => ‖f (x - y)‖ₑ :=
        (hf_meas.comp (measurable_id.sub_const y)).enorm
      rw [lintegral_mul_const _ hmx]
      congr 1
      exact (measurePreserving_sub_right volume y).lintegral_comp
        (f := fun x => ‖f x‖ₑ) hf_meas.enorm
    simp_rw [h_shift]
    rw [lintegral_const_mul _ (measurable_kPlNearR r).enorm]
    exact ENNReal.mul_lt_top hf_int.2
      ((lintegral_kPlNearR_le hr).trans_lt ENNReal.ofReal_lt_top)
  filter_upwards [ae_lt_top h_meas_inner h_tot.ne] with x hx
  refine ⟨((Lp.stronglyMeasurable f).smul
    ((measurable_kPlNearR r).comp (measurable_const.sub measurable_id)).stronglyMeasurable).aestronglyMeasurable,
    hx⟩

theorem integrable_kPlFarR {r m : ℝ} (hr : 0 < r) (hm : 1 < m) (f : Xm m) (x : Plane) :
    Integrable (fun y => f y • kPlFarR r (x - y)) volume := by
  have hf := integrable_of_Xm hm f
  refine Integrable.mono' (hf.norm.mul_const (2 * r⁻¹)) ?_ (Eventually.of_forall fun y => ?_)
  · exact ((Lp.stronglyMeasurable f).smul
      ((measurable_kPlFarR r).comp (measurable_const.sub measurable_id)).stronglyMeasurable).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_kPlFarR_le hr (x - y)) (norm_nonneg _)

theorem ae_integrable_planarBSKernel {m : ℝ} (hm : 1 < m) (f : Xm m) :
    ∀ᵐ x ∂(volume : Measure Plane),
      Integrable (fun y => f y • planarBSKernel (x - y)) volume := by
  filter_upwards [ae_integrable_kPlNearR le_rfl hm f] with x hx
  have hfar := integrable_kPlFarR zero_lt_one hm f x
  refine (hx.add hfar).congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, ← smul_add, kPlNearR_add_kPlFarR]

theorem ae_planarK_eq_uPlNearR_add_uPlFarR {r m : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hm : 1 < m) (f : Xm m) :
    ∀ᵐ x ∂(planeMeasure m), planarK f x = uPlNearR r f x + uPlFarR r f x := by
  filter_upwards [(planeMeasure_ac m).ae_le (ae_integrable_kPlNearR hr1 hm f)] with x hx
  have hfar := integrable_kPlFarR hr0 hm f x
  rw [planarK, uPlNearR, uPlFarR, ← integral_add hx hfar]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [← smul_add, kPlNearR_add_kPlFarR]

/-! ## 3. Weighted planar interaction operators and Hilbert–Schmidt approximation -/

/-- A continuous vector coefficient `b : Plane → Plane` with global weighted decay
`(|(b x).1| + |(b x).2|) * jb x ^ (m / 2 + 1) ≤ B` on `ℝ²`. -/
def IsPlanarWeightedCoeff (m B : ℝ) (b : Plane → Plane) : Prop :=
  Continuous b ∧ ∀ x : Plane, (|(b x).1| + |(b x).2|) * B0579.jb x ^ (m / 2 + 1) ≤ B

/-- Pointwise formula for the planar Biot–Savart interaction with coefficient `b`:
`-(K_{ℝ²} w)(x) · b(x)`. -/
def planarWeightedOpFun (b : Plane → Plane) (w : Plane → ℝ) (x : Plane) : ℝ :=
  -(planarK w x 0 * (b x).1 + planarK w x 1 * (b x).2)

/-- `T` realizes `w ↦ -(K_{ℝ²} w) · b` on `Xm m`. -/
def IsPlanarWeightedOp (m : ℝ) (b : Plane → Plane) (T : Xm m →L[ℝ] Xm m) : Prop :=
  ∀ f : Xm m, (T f : Plane → ℝ) =ᵐ[planeMeasure m] planarWeightedOpFun b f

theorem IsPlanarWeightedOp.unique {m : ℝ} {b : Plane → Plane} {A B : Xm m →L[ℝ] Xm m}
    (hA : IsPlanarWeightedOp m b A) (hB : IsPlanarWeightedOp m b B) : A = B := by
  ext1 f
  exact Lp.ext ((hA f).trans (hB f).symm)

theorem IsPlanarWeightedOp.sub {m : ℝ} {b₁ b₂ : Plane → Plane} {T₁ T₂ : Xm m →L[ℝ] Xm m}
    (h₁ : IsPlanarWeightedOp m b₁ T₁) (h₂ : IsPlanarWeightedOp m b₂ T₂) :
    IsPlanarWeightedOp m (fun x => b₁ x - b₂ x) (T₁ - T₂) := by
  intro f
  filter_upwards [Lp.coeFn_sub (T₁ f) (T₂ f), h₁ f, h₂ f] with x hsub ha₁ ha₂
  rw [sub_apply, hsub, Pi.sub_apply, ha₁, ha₂]
  simp only [planarWeightedOpFun, Prod.fst_sub, Prod.snd_sub]
  ring

def nearPlOpFun (r : ℝ) (b : Plane → Plane) (f : Plane → ℝ) (x : Plane) : ℝ :=
  -(uPlNearR r f x 0 * (b x).1 + uPlNearR r f x 1 * (b x).2)

def farPlOpFun (r : ℝ) (b : Plane → Plane) (f : Plane → ℝ) (x : Plane) : ℝ :=
  -(uPlFarR r f x 0 * (b x).1 + uPlFarR r f x 1 * (b x).2)

theorem ae_planarWeightedOpFun_eq_near_add_far {r m : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hm : 1 < m) (b : Plane → Plane) (f : Xm m) :
    planarWeightedOpFun b f =ᵐ[planeMeasure m]
      fun x => nearPlOpFun r b f x + farPlOpFun r b f x := by
  filter_upwards [ae_planarK_eq_uPlNearR_add_uPlFarR hr0 hr1 hm f] with x hx
  simp only [planarWeightedOpFun, nearPlOpFun, farPlOpFun, hx, PiLp.add_apply]
  ring

theorem norm_jb_mul_nearPlOpFun_le {r m B : ℝ} {b : Plane → Plane}
    (hb : IsPlanarWeightedCoeff m B b) (f : Plane → ℝ) (x : Plane) :
    ‖B0579.jb x ^ (m / 2) * nearPlOpFun r b f x‖ ≤ B * ‖uPlNearR r f x‖ := by
  have hpow : B0579.jb x ^ (m / 2) ≤ B0579.jb x ^ (m / 2 + 1) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_jb x) (by linarith)
  have h0 : |uPlNearR r f x 0| ≤ ‖uPlNearR r f x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (uPlNearR r f x) 0
  have h1 : |uPlNearR r f x 1| ≤ ‖uPlNearR r f x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (uPlNearR r f x) 1
  have hnear : |nearPlOpFun r b f x| ≤ (|(b x).1| + |(b x).2|) * ‖uPlNearR r f x‖ := by
    unfold nearPlOpFun
    rw [abs_neg]
    calc |uPlNearR r f x 0 * (b x).1 + uPlNearR r f x 1 * (b x).2|
        ≤ |uPlNearR r f x 0 * (b x).1| + |uPlNearR r f x 1 * (b x).2| := abs_add_le _ _
      _ = |uPlNearR r f x 0| * |(b x).1| + |uPlNearR r f x 1| * |(b x).2| := by
          rw [abs_mul, abs_mul]
      _ ≤ ‖uPlNearR r f x‖ * |(b x).1| + ‖uPlNearR r f x‖ * |(b x).2| := by gcongr
      _ = (|(b x).1| + |(b x).2|) * ‖uPlNearR r f x‖ := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
  calc B0579.jb x ^ (m / 2) * |nearPlOpFun r b f x|
      ≤ B0579.jb x ^ (m / 2 + 1) * ((|(b x).1| + |(b x).2|) * ‖uPlNearR r f x‖) :=
        mul_le_mul hpow hnear (abs_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le _)
    _ = ((|(b x).1| + |(b x).2|) * B0579.jb x ^ (m / 2 + 1)) * ‖uPlNearR r f x‖ := by ring
    _ ≤ B * ‖uPlNearR r f x‖ :=
        mul_le_mul_of_nonneg_right (hb.2 x) (norm_nonneg _)

theorem nearPlOpFun_memLp_and_bound {r m B : ℝ} (hr : r ≤ 1) (hm : 0 ≤ m)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (f : Xm m) :
    MemLp (nearPlOpFun r b f) 2 (planeMeasure m) ∧
      eLpNorm (nearPlOpFun r b f) 2 (planeMeasure m) ≤
        ENNReal.ofReal B * ((∫⁻ y : Plane, ‖kPlNearR r y‖ₑ) * ENNReal.ofReal ‖f‖) := by
  have hu : StronglyMeasurable (uPlNearR r f) :=
    stronglyMeasurable_uPlNearR r (Lp.stronglyMeasurable f)
  have hnear_meas : Measurable (nearPlOpFun r b f) := by
    unfold nearPlOpFun
    refine Measurable.neg (Measurable.add ?_ ?_)
    · exact ((EuclideanSpace.proj 0 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp hu.measurable).mul
        (continuous_fst.comp hb.1).measurable
    · exact ((EuclideanSpace.proj 1 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp hu.measurable).mul
        (continuous_snd.comp hb.1).measurable
  have hbd : eLpNorm (nearPlOpFun r b f) 2 (planeMeasure m) ≤
      ENNReal.ofReal B * ((∫⁻ y : Plane, ‖kPlNearR r y‖ₑ) * ENNReal.ofReal ‖f‖) := by
    rw [eLpNorm_planeMeasure]
    have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (μ := (volume : Measure Plane)) (p := 2)
      (f := fun x => B0579.jb x ^ (m / 2) * nearPlOpFun r b f x)
      (g := uPlNearR r f) (c := B)
      (Eventually.of_forall (norm_jb_mul_nearPlOpFun_le hb f))
    exact h1.trans (by gcongr; exact eLpNorm_uPlNearR_le hm f)
  refine ⟨⟨hnear_meas.aestronglyMeasurable, hbd.trans_lt ?_⟩, hbd⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ((lintegral_kPlNearR_le hr).trans_lt ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top)

instance instSFinitePlaneMeasure (m : ℝ) : SFinite (planeMeasure m) := by
  unfold planeMeasure
  infer_instance

/-- The Hilbert–Schmidt kernel of `farPlOpFun r b` on `Xm m`:
`-(kPlFarR r (x - y) · b(x)) jb(y)^{-m}`. -/
def hsPlKernel (m r : ℝ) (b : Plane → Plane) (z : Plane × Plane) : ℝ :=
  -(kPlFarR r (z.1 - z.2) 0 * (b z.1).1 + kPlFarR r (z.1 - z.2) 1 * (b z.1).2) *
    B0579.jb z.2 ^ (-m)

theorem integral_planeMeasure (m : ℝ) (g : Plane → ℝ) :
    ∫ y, g y ∂(planeMeasure m) = ∫ y : Plane, B0579.density m y • g y :=
  integral_withDensity_eq_integral_smul (B0579.measurable_density m) g

theorem integral_hsPlKernel {m r : ℝ} (hr : 0 < r) (hm : 1 < m)
    (b : Plane → Plane) (f : Xm m) (x : Plane) :
    ∫ y, hsPlKernel m r b (x, y) * f y ∂(planeMeasure m) = farPlOpFun r b f x := by
  rw [integral_planeMeasure]
  have hfar := integrable_kPlFarR hr hm f x
  have hi : ∀ i : Fin 2,
      Integrable (fun y => f y * kPlFarR r (x - y) i) volume := fun i => by
    have hcomp := (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hfar
    exact hcomp.congr (Eventually.of_forall fun y => by simp)
  have hint_eq : ∀ i : Fin 2,
      ∫ y : Plane, f y * kPlFarR r (x - y) i = uPlFarR r f x i := fun i => by
    have hcomp := (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hfar
    simpa [uPlFarR] using hcomp
  have hcongr : ∀ y : Plane,
      B0579.density m y • (hsPlKernel m r b (x, y) * f y) =
        -((f y * kPlFarR r (x - y) 0) * (b x).1 + (f y * kPlFarR r (x - y) 1) * (b x).2) := by
    intro y
    rw [NNReal.smul_def, smul_eq_mul, B0579.coe_density]
    unfold hsPlKernel
    have hjb : B0579.jb y ^ m * B0579.jb y ^ (-m) = 1 := by
      rw [B0579.jb_rpow_mul, add_neg_cancel, Real.rpow_zero]
    calc B0579.jb y ^ m * (-(kPlFarR r (x - y) 0 * (b x).1 + kPlFarR r (x - y) 1 * (b x).2) *
            B0579.jb y ^ (-m) * f y)
        = (B0579.jb y ^ m * B0579.jb y ^ (-m)) *
            (-((f y * kPlFarR r (x - y) 0) * (b x).1 + (f y * kPlFarR r (x - y) 1) * (b x).2)) := by
          ring
      _ = -((f y * kPlFarR r (x - y) 0) * (b x).1 + (f y * kPlFarR r (x - y) 1) * (b x).2) := by
          rw [hjb, one_mul]
  simp_rw [hcongr]
  rw [integral_neg, integral_add ((hi 0).mul_const _) ((hi 1).mul_const _),
    integral_mul_const, integral_mul_const, hint_eq 0, hint_eq 1, farPlOpFun]

private theorem eLpNorm_jb_neg_half_add_one_plane (m : ℝ) :
    eLpNorm (fun x : Plane => B0579.jb x ^ (-(m / 2 + 1))) 2 (planeMeasure m) ≤
      B0592.weightConst 2 := by
  apply B0592.ennreal_le_of_sq_le_sq
  rw [eLpNorm_planeMeasure, B0592.eLpNorm_two_sq, B0592.weightConst,
    B0592.ennreal_rpow_half_sq]
  refine le_of_eq (lintegral_congr fun x => ?_)
  have h1 : B0579.jb x ^ (m / 2) * B0579.jb x ^ (-(m / 2 + 1)) = B0579.jb x ^ (-1 : ℝ) := by
    rw [B0579.jb_rpow_mul]
    congr 1
    ring
  rw [h1, Real.enorm_eq_ofReal (Real.rpow_nonneg (B0579.jb_pos x).le _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos x).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  congr 2
  push_cast
  ring

private theorem eLpNorm_jb_neg_m_plane (m : ℝ) :
    eLpNorm (fun y : Plane => B0579.jb y ^ (-m)) 2 (planeMeasure m) ≤
      B0592.weightConst m := by
  apply B0592.ennreal_le_of_sq_le_sq
  rw [eLpNorm_planeMeasure, B0592.eLpNorm_two_sq, B0592.weightConst,
    B0592.ennreal_rpow_half_sq]
  refine le_of_eq (lintegral_congr fun y => ?_)
  have h1 : B0579.jb y ^ (m / 2) * B0579.jb y ^ (-m) = B0579.jb y ^ (-m / 2) := by
    rw [B0579.jb_rpow_mul]
    congr 1
    ring
  rw [h1, Real.enorm_eq_ofReal (Real.rpow_nonneg (B0579.jb_pos y).le _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos y).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos y).le]
  congr 2
  push_cast
  ring

instance sigmaFinite_planeMeasure (m : ℝ) : SigmaFinite (planeMeasure m) := by
  rw [planeMeasure]
  infer_instance

theorem memLp_hsPlKernel_and_bound {m r B : ℝ} (hm : 1 < m) (hr : 0 < r)
    (_hB : 0 ≤ B) {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) :
    MemLp (hsPlKernel m r b) 2 ((planeMeasure m).prod (planeMeasure m)) ∧
      eLpNorm (hsPlKernel m r b) 2 ((planeMeasure m).prod (planeMeasure m)) ≤
        ENNReal.ofReal (2 * r⁻¹ * B) * (B0592.weightConst 2 * B0592.weightConst m) := by
  set μ := planeMeasure m
  set u : Plane → ℝ := fun x => B0579.jb x ^ (-(m / 2 + 1))
  set v : Plane → ℝ := fun y => B0579.jb y ^ (-m)
  have hu_meas : Measurable u := (B0579.continuous_jb_rpow _).measurable
  have hv_meas : Measurable v := (B0579.continuous_jb_rpow _).measurable
  have hk_meas : Measurable (hsPlKernel m r b) := by
    unfold hsPlKernel
    refine (Measurable.neg (Measurable.add ?_ ?_)).mul (hv_meas.comp measurable_snd)
    · exact ((EuclideanSpace.proj 0 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp
        ((measurable_kPlFarR r).comp (measurable_fst.sub measurable_snd))).mul
        (continuous_fst.comp (hb.1.comp continuous_fst)).measurable
    · exact ((EuclideanSpace.proj 1 : Cyl.Vec2 →L[ℝ] ℝ).measurable.comp
        ((measurable_kPlFarR r).comp (measurable_fst.sub measurable_snd))).mul
        (continuous_snd.comp (hb.1.comp continuous_fst)).measurable
  have hprod_bound : eLpNorm (fun z : Plane × Plane => u z.1 * v z.2) 2 (μ.prod μ) ≤
      B0592.weightConst 2 * B0592.weightConst m := by
    apply B0592.ennreal_le_of_sq_le_sq
    rw [B0592.eLpNorm_two_sq]
    have hF : AEMeasurable (fun z : Plane × Plane => ‖u z.1 * v z.2‖ₑ ^ 2) (μ.prod μ) :=
      (((hu_meas.comp measurable_fst).mul (hv_meas.comp measurable_snd)).enorm.pow_const 2).aemeasurable
    rw [lintegral_prod _ hF]
    have hsplit : ∀ x : Plane,
        ∫⁻ y, ‖u x * v y‖ₑ ^ 2 ∂μ = ‖u x‖ₑ ^ 2 * ∫⁻ y, ‖v y‖ₑ ^ 2 ∂μ := by
      intro x
      have hcongr : ∀ y : Plane, ‖u x * v y‖ₑ ^ 2 = ‖u x‖ₑ ^ 2 * ‖v y‖ₑ ^ 2 := fun y => by
        rw [enorm_mul, mul_pow]
      simp_rw [hcongr]
      exact lintegral_const_mul _ (hv_meas.enorm.pow_const 2)
    simp_rw [hsplit]
    rw [lintegral_mul_const _ (hu_meas.enorm.pow_const 2), ← B0592.eLpNorm_two_sq,
      ← B0592.eLpNorm_two_sq]
    have hu2 : eLpNorm u 2 μ ^ 2 ≤ B0592.weightConst 2 ^ 2 :=
      pow_le_pow_left₀ zero_le (eLpNorm_jb_neg_half_add_one_plane m) 2
    have hv2 : eLpNorm v 2 μ ^ 2 ≤ B0592.weightConst m ^ 2 :=
      pow_le_pow_left₀ zero_le (eLpNorm_jb_neg_m_plane m) 2
    calc eLpNorm u 2 μ ^ 2 * eLpNorm v 2 μ ^ 2
        ≤ B0592.weightConst 2 ^ 2 * B0592.weightConst m ^ 2 := mul_le_mul' hu2 hv2
      _ = (B0592.weightConst 2 * B0592.weightConst m) ^ 2 := by ring
  have hpt : ∀ᵐ z : Plane × Plane ∂(μ.prod μ),
      ‖hsPlKernel m r b z‖ ≤ (2 * r⁻¹ * B) * ‖u z.1 * v z.2‖ := by
    refine Eventually.of_forall fun z => ?_
    have h0 := norm_kPlFarR_coord_le hr (z.1 - z.2) 0
    have h1 := norm_kPlFarR_coord_le hr (z.1 - z.2) 1
    have hfar_dot :
        |kPlFarR r (z.1 - z.2) 0 * (b z.1).1 + kPlFarR r (z.1 - z.2) 1 * (b z.1).2| ≤
          (2 * r⁻¹) * (|(b z.1).1| + |(b z.1).2|) := by
      calc |kPlFarR r (z.1 - z.2) 0 * (b z.1).1 + kPlFarR r (z.1 - z.2) 1 * (b z.1).2|
          ≤ |kPlFarR r (z.1 - z.2) 0| * |(b z.1).1| + |kPlFarR r (z.1 - z.2) 1| * |(b z.1).2| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ (2 * r⁻¹) * |(b z.1).1| + (2 * r⁻¹) * |(b z.1).2| := by gcongr
        _ = (2 * r⁻¹) * (|(b z.1).1| + |(b z.1).2|) := by ring
    have hb_le : |(b z.1).1| + |(b z.1).2| ≤ B * u z.1 := by
      have hmul := hb.2 z.1
      have hinv : B0579.jb z.1 ^ (m / 2 + 1) * u z.1 = 1 := by
        simp only [u]
        rw [B0579.jb_rpow_mul, add_neg_cancel, Real.rpow_zero]
      calc |(b z.1).1| + |(b z.1).2|
          = (|(b z.1).1| + |(b z.1).2|) * (B0579.jb z.1 ^ (m / 2 + 1) * u z.1) := by
            rw [hinv, mul_one]
        _ = ((|(b z.1).1| + |(b z.1).2|) * B0579.jb z.1 ^ (m / 2 + 1)) * u z.1 := by ring
        _ ≤ B * u z.1 := mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg (B0579.jb_pos z.1).le _)
    have hu_nn : 0 ≤ u z.1 := Real.rpow_nonneg (B0579.jb_pos z.1).le _
    have hv_nn : 0 ≤ v z.2 := Real.rpow_nonneg (B0579.jb_pos z.2).le _
    simp only [hsPlKernel, Real.norm_eq_abs]
    rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hu_nn, abs_of_nonneg hv_nn]
    calc |kPlFarR r (z.1 - z.2) 0 * (b z.1).1 + kPlFarR r (z.1 - z.2) 1 * (b z.1).2| * v z.2
        ≤ ((2 * r⁻¹) * (|(b z.1).1| + |(b z.1).2|)) * v z.2 :=
          mul_le_mul_of_nonneg_right hfar_dot hv_nn
      _ ≤ ((2 * r⁻¹) * (B * u z.1)) * v z.2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb_le (by positivity)) hv_nn
      _ = (2 * r⁻¹ * B) * (u z.1 * v z.2) := by ring
  have hbd : eLpNorm (hsPlKernel m r b) 2 (μ.prod μ) ≤
      ENNReal.ofReal (2 * r⁻¹ * B) * (B0592.weightConst 2 * B0592.weightConst m) := by
    have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ.prod μ) (p := 2)
      (f := hsPlKernel m r b) (g := fun z : Plane × Plane => u z.1 * v z.2)
      (c := 2 * r⁻¹ * B) hpt
    exact h1.trans (by gcongr)
  refine ⟨⟨hk_meas.aestronglyMeasurable, hbd.trans_lt ?_⟩, hbd⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (B0592.weightConst_lt_top (by norm_num)) (B0592.weightConst_lt_top hm))

/-- The far Hilbert–Schmidt planar operator at truncation index `n` (`r = B0061.rad n`). -/
def hsPlOp {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B) {b : Plane → Plane}
    (hb : IsPlanarWeightedCoeff m B b) (n : ℕ) : Xm m →L[ℝ] Xm m :=
  realKernelOperator (memLp_hsPlKernel_and_bound hm (B0061.rad_pos n) hB hb).1

theorem isCompactOperator_hsPlOp {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (n : ℕ) :
    IsCompactOperator (hsPlOp hm hB hb n) :=
  isCompactOperator_realKernelOperator _

theorem coeFn_hsPlOp {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (n : ℕ) (f : Xm m) :
    (hsPlOp hm hB hb n f : Plane → ℝ) =ᵐ[planeMeasure m]
      farPlOpFun (B0061.rad n) b f := by
  filter_upwards [coeFn_realKernelOperator
    (memLp_hsPlKernel_and_bound hm (B0061.rad_pos n) hB hb).1 f] with x hx
  rw [hsPlOp, hx, integral_hsPlKernel (B0061.rad_pos n) hm b f x]

theorem norm_hsPlOp_zero_le {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) :
    ‖hsPlOp hm hB hb 0‖ ≤
      2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B := by
  have h1 := norm_realKernelOperator_le
    (memLp_hsPlKernel_and_bound hm (B0061.rad_pos 0) hB hb).1
  have h2 := (memLp_hsPlKernel_and_bound hm (B0061.rad_pos 0) hB hb).2
  have hrad0 : 2 * (B0061.rad 0)⁻¹ = 2 := by
    unfold B0061.rad
    norm_num
  rw [hrad0] at h2
  have hfin : ENNReal.ofReal (2 * B) * (B0592.weightConst 2 * B0592.weightConst m) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (B0592.weightConst_lt_top (by norm_num)).ne
        (B0592.weightConst_lt_top hm).ne)
  have h3 := ENNReal.toReal_mono hfin h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h3
  calc ‖hsPlOp hm hB hb 0‖
      ≤ 2 * B * ((B0592.weightConst 2).toReal * (B0592.weightConst m).toReal) :=
        h1.trans h3
    _ = 2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B := by ring

theorem ae_planarWeightedOpFun_eq_near_add_hsPlOp {m B : ℝ} (hm : 1 < m)
    (hB : 0 ≤ B) {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (n : ℕ) (f : Xm m) :
    planarWeightedOpFun b f =ᵐ[planeMeasure m]
      nearPlOpFun (B0061.rad n) b f + (hsPlOp hm hB hb n f : Plane → ℝ) := by
  filter_upwards [ae_planarWeightedOpFun_eq_near_add_far (B0061.rad_pos n) (B0061.rad_le_one n)
    hm b f, coeFn_hsPlOp hm hB hb n f] with x hx1 hx2
  rw [Pi.add_apply, hx2, hx1]

theorem memLp_planarWeightedOpFun {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (f : Xm m) :
    MemLp (planarWeightedOpFun b f) 2 (planeMeasure m) := by
  have hnear := (nearPlOpFun_memLp_and_bound (B0061.rad_le_one 0) (by linarith) hb f).1
  exact (hnear.add (Lp.memLp (hsPlOp hm hB hb 0 f))).ae_eq
    (ae_planarWeightedOpFun_eq_near_add_hsPlOp hm hB hb 0 f).symm

def planarWeightedLpFun {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (f : Xm m) : Xm m :=
  (memLp_planarWeightedOpFun hm hB hb f).toLp _

theorem coeFn_planarWeightedLpFun {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (f : Xm m) :
    (planarWeightedLpFun hm hB hb f : Plane → ℝ) =ᵐ[planeMeasure m]
      planarWeightedOpFun b f :=
  MemLp.coeFn_toLp _

theorem norm_planarWeightedLpFun_sub_hsPlOp_le {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (n : ℕ) (f : Xm m) :
    ‖planarWeightedLpFun hm hB hb f - hsPlOp hm hB hb n f‖ ≤
      B * (∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ).toReal * ‖f‖ := by
  have hnear := nearPlOpFun_memLp_and_bound (B0061.rad_le_one n) (by linarith) hb f
  have hae : ((planarWeightedLpFun hm hB hb f - hsPlOp hm hB hb n f : Xm m) : Plane → ℝ)
      =ᵐ[planeMeasure m] nearPlOpFun (B0061.rad n) b f := by
    filter_upwards [Lp.coeFn_sub (planarWeightedLpFun hm hB hb f) (hsPlOp hm hB hb n f),
      coeFn_planarWeightedLpFun hm hB hb f,
      ae_planarWeightedOpFun_eq_near_add_hsPlOp hm hB hb n f] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.add_apply, add_sub_cancel_right]
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have hfin : (∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ) ≠ ∞ :=
    ((lintegral_kPlNearR_le (B0061.rad_le_one n)).trans_lt ENNReal.ofReal_lt_top).ne
  have hprod_fin :
      ENNReal.ofReal B * ((∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ) *
        ENNReal.ofReal ‖f‖) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
  calc (eLpNorm (nearPlOpFun (B0061.rad n) b f) 2 (planeMeasure m)).toReal
      ≤ (ENNReal.ofReal B * ((∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ) *
          ENNReal.ofReal ‖f‖)).toReal :=
        ENNReal.toReal_mono hprod_fin hnear.2
    _ = B * (∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ).toReal * ‖f‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
          ENNReal.toReal_ofReal (norm_nonneg _)]
        ring

theorem planarWeightedLpFun_add {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (f g : Xm m) :
    planarWeightedLpFun hm hB hb (f + g) =
      planarWeightedLpFun hm hB hb f + planarWeightedLpFun hm hB hb g := by
  apply Lp.ext
  have hfg_ae : ((f + g : Xm m) : Plane → ℝ) =ᵐ[volume] f + g :=
    (volume_ac_planeMeasure m).ae_le (Lp.coeFn_add f g)
  have hK_add : ∀ᵐ x ∂(planeMeasure m),
      planarK (f + g : Xm m) x = planarK f x + planarK g x := by
    filter_upwards [(planeMeasure_ac m).ae_le (ae_integrable_planarBSKernel hm f),
      (planeMeasure_ac m).ae_le (ae_integrable_planarBSKernel hm g)] with x hif hig
    rw [planarK, planarK, planarK, ← integral_add hif hig]
    refine integral_congr_ae ?_
    filter_upwards [hfg_ae] with y hy
    rw [hy, Pi.add_apply, add_smul]
  filter_upwards [coeFn_planarWeightedLpFun hm hB hb (f + g),
    Lp.coeFn_add (planarWeightedLpFun hm hB hb f) (planarWeightedLpFun hm hB hb g),
    coeFn_planarWeightedLpFun hm hB hb f,
    coeFn_planarWeightedLpFun hm hB hb g,
    hK_add] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4]
  simp only [planarWeightedOpFun, h5, PiLp.add_apply]
  ring

theorem planarWeightedLpFun_smul {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (a : ℝ) (f : Xm m) :
    planarWeightedLpFun hm hB hb (a • f) = a • planarWeightedLpFun hm hB hb f := by
  apply Lp.ext
  have haf_ae : ((a • f : Xm m) : Plane → ℝ) =ᵐ[volume] a • f :=
    (volume_ac_planeMeasure m).ae_le (Lp.coeFn_smul a f)
  have hK_smul : ∀ x : Plane, planarK (a • f : Xm m) x = a • planarK f x := by
    intro x
    rw [planarK, planarK, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [haf_ae] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_smul]
  filter_upwards [coeFn_planarWeightedLpFun hm hB hb (a • f),
    Lp.coeFn_smul a (planarWeightedLpFun hm hB hb f),
    coeFn_planarWeightedLpFun hm hB hb f] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  simp only [planarWeightedOpFun, hK_smul x, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Operator-norm constant `plKernelBoundConst m > 0` for `planarWeightedOp`. -/
def plKernelBoundConst (m : ℝ) : ℝ :=
  max 1 (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal + plSplitConst)

theorem plKernelBoundConst_pos (m : ℝ) : 0 < plKernelBoundConst m :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem norm_planarWeightedLpFun_le {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) (f : Xm m) :
    ‖planarWeightedLpFun hm hB hb f‖ ≤ plKernelBoundConst m * B * ‖f‖ := by
  have hsub := norm_planarWeightedLpFun_sub_hsPlOp_le hm hB hb 0 f
  have hnear0 : (∫⁻ y : Plane, ‖kPlNearR (B0061.rad 0) y‖ₑ).toReal ≤ plSplitConst := by
    have h1 := lintegral_kPlNearR_le (B0061.rad_le_one 0)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans
      (le_of_eq (ENNReal.toReal_ofReal plSplitConst_nonneg))
  have hhs0 : ‖hsPlOp hm hB hb 0 f‖ ≤
      (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B) * ‖f‖ :=
    ((hsPlOp hm hB hb 0).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (norm_hsPlOp_zero_le hm hB hb) (norm_nonneg f))
  have hsub0 : ‖planarWeightedLpFun hm hB hb f - hsPlOp hm hB hb 0 f‖ ≤
      (B * plSplitConst) * ‖f‖ :=
    hsub.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnear0 hB) (norm_nonneg f))
  have hle_max :
      2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal + plSplitConst ≤
        plKernelBoundConst m :=
    le_max_right _ _
  calc ‖planarWeightedLpFun hm hB hb f‖
      ≤ ‖hsPlOp hm hB hb 0 f‖ +
          ‖planarWeightedLpFun hm hB hb f - hsPlOp hm hB hb 0 f‖ :=
        norm_le_insert' _ _
    _ ≤ (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal * B) * ‖f‖ +
          (B * plSplitConst) * ‖f‖ :=
        add_le_add hhs0 hsub0
    _ = (2 * (B0592.weightConst 2).toReal * (B0592.weightConst m).toReal + plSplitConst) *
          B * ‖f‖ := by ring
    _ ≤ plKernelBoundConst m * B * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_max hB) (norm_nonneg f)

/-- The bounded planar weighted Biot–Savart operator `f ↦ -(K_{ℝ²} f)·b` on `Xm m`. -/
def planarWeightedOp {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) : Xm m →L[ℝ] Xm m :=
  LinearMap.mkContinuous
    { toFun := planarWeightedLpFun hm hB hb
      map_add' := planarWeightedLpFun_add hm hB hb
      map_smul' := fun a f => by
        rw [RingHom.id_apply]
        exact planarWeightedLpFun_smul hm hB hb a f }
    (plKernelBoundConst m * B)
    (norm_planarWeightedLpFun_le hm hB hb)

theorem isPlanarWeightedOp_planarWeightedOp {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) :
    IsPlanarWeightedOp m b (planarWeightedOp hm hB hb) :=
  coeFn_planarWeightedLpFun hm hB hb

theorem norm_planarWeightedOp_le {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) :
    ‖planarWeightedOp hm hB hb‖ ≤ plKernelBoundConst m * B :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (plKernelBoundConst_pos m).le hB) _

theorem isCompactOperator_planarWeightedOp {m B : ℝ} (hm : 1 < m) (hB : 0 ≤ B)
    {b : Plane → Plane} (hb : IsPlanarWeightedCoeff m B b) :
    IsCompactOperator (planarWeightedOp hm hB hb) := by
  have hL : Tendsto (fun n : ℕ =>
      B * (∫⁻ y : Plane, ‖kPlNearR (B0061.rad n) y‖ₑ).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp tendsto_lintegral_kPlNearR
    simpa using h.const_mul B
  have hT : Tendsto (fun n : ℕ => hsPlOp hm hB hb n) atTop
      (𝓝 (planarWeightedOp hm hB hb)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hB ENNReal.toReal_nonneg) fun f => ?_
    rw [show (hsPlOp hm hB hb n - planarWeightedOp hm hB hb) f =
        hsPlOp hm hB hb n f - planarWeightedLpFun hm hB hb f from rfl, norm_sub_rev]
    exact norm_planarWeightedLpFun_sub_hsPlOp_le hm hB hb n f
  exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto hT
    (Eventually.of_forall fun n => isCompactOperator_hsPlOp hm hB hb n)

/-! ## 4. Uniform continuity of `σ ↦ planarGradE σ` in the `jb x ^ (m / 2 + 1)` weight -/

theorem norm_le_jb (x : Plane) : ‖x‖ ≤ B0579.jb x := by
  have h1 : |x.1| ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_abs x.1, sq_nonneg (|x.1| - 1), sq_nonneg x.2]
  have h2 : |x.2| ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_abs x.2, sq_nonneg (|x.2| - 1), sq_nonneg x.1]
  exact max_le h1 h2

theorem continuousOn_weighted_planarGradE (k : ℝ) (Sg : ℝ) :
    ContinuousOn (fun p : ℝ × Plane =>
      (B0579.jb p.2 ^ k * (planarGradE p.1 p.2).1,
       B0579.jb p.2 ^ k * (planarGradE p.1 p.2).2)) (Icc 0 Sg ×ˢ univ) := by
  have h1σ : ∀ p ∈ Icc (0 : ℝ) Sg ×ˢ (univ : Set Plane), 1 + p.1 ≠ 0 := by
    intro p hp
    have : 0 ≤ p.1 := hp.1.1
    linarith
  have hsqrt : ∀ p ∈ Icc (0 : ℝ) Sg ×ˢ (univ : Set Plane), Real.sqrt (1 + p.1) ≠ 0 := by
    intro p hp
    have : 0 < 1 + p.1 := by linarith [hp.1.1]
    exact (Real.sqrt_pos.mpr this).ne'
  have hpow : ContinuousOn (fun p : ℝ × Plane => (1 + p.1) ^ (-5 / 2 : ℝ))
      (Icc 0 Sg ×ˢ univ) :=
    (continuousOn_const.add continuousOn_fst).rpow_const fun p hp => Or.inl (h1σ p hp)
  have hsc : ContinuousOn (fun p : ℝ × Plane => ofPlane (scalePlane (1 + p.1) p.2))
      (Icc 0 Sg ×ˢ univ) := by
    have heq : (fun p : ℝ × Plane => ofPlane (scalePlane (1 + p.1) p.2)) =
        fun p => ((p.2.1 / Real.sqrt (1 + p.1) : ℝ) : ℂ) +
          ((p.2.2 / Real.sqrt (1 + p.1) : ℝ) : ℂ) * Complex.I := by
      funext p
      exact ofPlane_eq_add_mul_I (scalePlane (1 + p.1) p.2)
    rw [heq]
    have hq : ContinuousOn (fun p : ℝ × Plane => p.2.1 / Real.sqrt (1 + p.1))
        (Icc 0 Sg ×ˢ univ) :=
      (continuous_fst.comp continuous_snd).continuousOn.div
        (Real.continuous_sqrt.comp (continuous_const.add continuous_fst)).continuousOn hsqrt
    have hη : ContinuousOn (fun p : ℝ × Plane => p.2.2 / Real.sqrt (1 + p.1))
        (Icc 0 Sg ×ˢ univ) :=
      (continuous_snd.comp continuous_snd).continuousOn.div
        (Real.continuous_sqrt.comp (continuous_const.add continuous_fst)).continuousOn hsqrt
    exact (Complex.continuous_ofReal.comp_continuousOn hq).add
      ((Complex.continuous_ofReal.comp_continuousOn hη).mul continuousOn_const)
  have hjb : ContinuousOn (fun p : ℝ × Plane => B0579.jb p.2 ^ k) (Icc 0 Sg ×ˢ univ) :=
    ((B0579.continuous_jb_rpow k).comp continuous_snd).continuousOn
  have hgrad1 : ContinuousOn (fun p : ℝ × Plane => (planarGradE p.1 p.2).1)
      (Icc 0 Sg ×ˢ univ) :=
    hpow.mul (B0009.continuous_gradE0_fst.comp_continuousOn hsc)
  have hgrad2 : ContinuousOn (fun p : ℝ × Plane => (planarGradE p.1 p.2).2)
      (Icc 0 Sg ×ˢ univ) :=
    hpow.mul (B0009.continuous_gradE0_snd.comp_continuousOn hsc)
  exact (hjb.mul hgrad1).prodMk (hjb.mul hgrad2)

theorem exists_delta_planarGradE_diff (m : ℝ) (hm : 8 < m) (Sg : ℝ) (hSg : 0 < Sg)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ₁ ∈ Icc 0 Sg, ∀ σ₂ ∈ Icc 0 Sg, dist σ₁ σ₂ < δ →
      IsPlanarWeightedCoeff m ε (fun x => planarGradE σ₁ x - planarGradE σ₂ x) := by
  set k : ℝ := m / 2 + 1
  have hk : 0 ≤ k := by dsimp [k]; linarith
  obtain ⟨M, hM, hM_bd⟩ := jb_mul_gradSum_sup_bound (k + 1) (by linarith) Sg hSg
  set R : ℝ := 2 * M / ε + 1
  have hR_pos : 0 < R := by dsimp [R]; positivity
  set Φ : ℝ × Plane → Plane := fun p =>
    (B0579.jb p.2 ^ k * (planarGradE p.1 p.2).1,
     B0579.jb p.2 ^ k * (planarGradE p.1 p.2).2)
  set K : Set (ℝ × Plane) := Icc 0 Sg ×ˢ Metric.closedBall (0 : Plane) R
  have hK_compact : IsCompact K := isCompact_Icc.prod (isCompact_closedBall (0 : Plane) R)
  have hΦ_cont : ContinuousOn Φ K :=
    (continuousOn_weighted_planarGradE k Sg).mono
      (prod_mono Subset.rfl (subset_univ _))
  have hΦ_ucont : UniformContinuousOn Φ K :=
    hK_compact.uniformContinuousOn_of_continuous hΦ_cont
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hΦ_ucont (ε / 2) (half_pos hε)
  refine ⟨δ, hδ_pos, fun σ₁ hσ₁ σ₂ hσ₂ hdist => ?_⟩
  refine ⟨(continuous_planarGradE σ₁).sub (continuous_planarGradE σ₂), fun x => ?_⟩
  by_cases hxR : x ∈ Metric.closedBall (0 : Plane) R
  · have hp₁ : (σ₁, x) ∈ K := ⟨hσ₁, hxR⟩
    have hp₂ : (σ₂, x) ∈ K := ⟨hσ₂, hxR⟩
    have hd_prod : dist (σ₁, x) (σ₂, x) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hdist
    have hΦ_dist : dist (Φ (σ₁, x)) (Φ (σ₂, x)) < ε / 2 :=
      hδ (σ₁, x) hp₁ (σ₂, x) hp₂ hd_prod
    rw [Prod.dist_eq] at hΦ_dist
    have hd1 : dist (Φ (σ₁, x)).1 (Φ (σ₂, x)).1 ≤ ε / 2 :=
      (le_max_left _ _).trans hΦ_dist.le
    have hd2 : dist (Φ (σ₁, x)).2 (Φ (σ₂, x)).2 ≤ ε / 2 :=
      (le_max_right _ _).trans hΦ_dist.le
    rw [Real.dist_eq] at hd1 hd2
    have heq1 : |(planarGradE σ₁ x - planarGradE σ₂ x).1| * B0579.jb x ^ k =
        |(Φ (σ₁, x)).1 - (Φ (σ₂, x)).1| := by
      dsimp [Φ]
      have hjb_nn : 0 ≤ B0579.jb x ^ k := Real.rpow_nonneg (B0579.jb_pos x).le _
      rw [← mul_sub (B0579.jb x ^ k), abs_mul, abs_of_nonneg hjb_nn, mul_comm]
    have heq2 : |(planarGradE σ₁ x - planarGradE σ₂ x).2| * B0579.jb x ^ k =
        |(Φ (σ₁, x)).2 - (Φ (σ₂, x)).2| := by
      dsimp [Φ]
      have hjb_nn : 0 ≤ B0579.jb x ^ k := Real.rpow_nonneg (B0579.jb_pos x).le _
      rw [← mul_sub (B0579.jb x ^ k), abs_mul, abs_of_nonneg hjb_nn, mul_comm]
    calc (|(planarGradE σ₁ x - planarGradE σ₂ x).1| +
            |(planarGradE σ₁ x - planarGradE σ₂ x).2|) * B0579.jb x ^ k
        = |(planarGradE σ₁ x - planarGradE σ₂ x).1| * B0579.jb x ^ k +
            |(planarGradE σ₁ x - planarGradE σ₂ x).2| * B0579.jb x ^ k := add_mul _ _ _
      _ = |(Φ (σ₁, x)).1 - (Φ (σ₂, x)).1| + |(Φ (σ₁, x)).2 - (Φ (σ₂, x)).2| := by
          rw [heq1, heq2]
      _ ≤ ε / 2 + ε / 2 := add_le_add hd1 hd2
      _ = ε := add_halves ε
  · have hltR : R < ‖x‖ := by simpa [mem_closedBall_zero_iff] using hxR
    have hjbR : R ≤ B0579.jb x := hltR.le.trans (norm_le_jb x)
    have htail : ∀ σ ∈ Icc 0 Sg, B0579.jb x ^ k * gradSum σ x ≤ ε / 2 := by
      intro σ hσ
      have h1 := hM_bd σ hσ x
      have hrpow : B0579.jb x ^ (k + 1) = B0579.jb x ^ k * B0579.jb x := by
        rw [Real.rpow_add (B0579.jb_pos x) k 1, Real.rpow_one]
      rw [hrpow] at h1
      have h2 : B0579.jb x ^ k * gradSum σ x * R ≤ M := by
        calc B0579.jb x ^ k * gradSum σ x * R
            ≤ B0579.jb x ^ k * gradSum σ x * B0579.jb x :=
              mul_le_mul_of_nonneg_left hjbR
                (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (gradSum_nonneg σ x))
          _ = B0579.jb x ^ k * B0579.jb x * gradSum σ x := by ring
          _ ≤ M := h1
      have h3 : M ≤ ε / 2 * R := by
        dsimp [R]
        have : ε ≠ 0 := hε.ne'
        have h4 : ε / 2 * (2 * M / ε + 1) = M + ε / 2 := by field_simp
        linarith
      exact le_of_mul_le_mul_right (h2.trans h3) hR_pos
    have habs : |(planarGradE σ₁ x - planarGradE σ₂ x).1| +
        |(planarGradE σ₁ x - planarGradE σ₂ x).2| ≤ gradSum σ₁ x + gradSum σ₂ x := by
      simp only [Prod.fst_sub, Prod.snd_sub, gradSum]
      linarith [abs_sub (planarGradE σ₁ x).1 (planarGradE σ₂ x).1,
        abs_sub (planarGradE σ₁ x).2 (planarGradE σ₂ x).2]
    have hjb_nn : 0 ≤ B0579.jb x ^ k := Real.rpow_nonneg (B0579.jb_pos x).le _
    calc (|(planarGradE σ₁ x - planarGradE σ₂ x).1| +
            |(planarGradE σ₁ x - planarGradE σ₂ x).2|) * B0579.jb x ^ k
        ≤ (gradSum σ₁ x + gradSum σ₂ x) * B0579.jb x ^ k :=
          mul_le_mul_of_nonneg_right habs hjb_nn
      _ = B0579.jb x ^ k * gradSum σ₁ x + B0579.jb x ^ k * gradSum σ₂ x := by ring
      _ ≤ ε / 2 + ε / 2 := add_le_add (htail σ₁ hσ₁) (htail σ₂ hσ₂)
      _ = ε := add_halves ε

/-! ## 5. Main theorem (`PartII-b:F1/3`): `planarInteractionCompactStep_proof` -/

theorem planarInteractionCompactStep_proof : PlanarInteractionCompactStep := by
  intro m hm Sg hSg
  have hm1 : 1 < m := by linarith
  obtain ⟨B₀, hB₀, hGrad₀⟩ := jb_mul_gradSum_sup_bound (m / 2 + 1) (by linarith) Sg hSg
  have hCoeff : ∀ σ ∈ Icc 0 Sg, IsPlanarWeightedCoeff m B₀ (planarGradE σ) := by
    intro σ hσ
    refine ⟨continuous_planarGradE σ, fun x => ?_⟩
    rw [mul_comm]
    exact hGrad₀ σ hσ x
  classical
  set AplOp : ℝ → (Xm m →L[ℝ] Xm m) := fun σ =>
    if hσ : σ ∈ Icc 0 Sg then planarWeightedOp hm1 hB₀.le (hCoeff σ hσ) else 0
  have hAplOp_eq : ∀ σ (hσ : σ ∈ Icc 0 Sg),
      AplOp σ = planarWeightedOp hm1 hB₀.le (hCoeff σ hσ) := by
    intro σ hσ
    dsimp [AplOp]
    exact dite_cond_eq_true (eq_true hσ)
  have hWOp : ∀ σ ∈ Icc 0 Sg, IsPlanarWeightedOp m (planarGradE σ) (AplOp σ) := by
    intro σ hσ
    rw [hAplOp_eq σ hσ]
    exact isPlanarWeightedOp_planarWeightedOp hm1 hB₀.le (hCoeff σ hσ)
  refine ⟨AplOp, ?_, fun σ hσ => ⟨hWOp σ hσ, ?_⟩⟩
  · rw [Metric.continuousOn_iff]
    intro σ₁ hσ₁ ε hε
    have hK_pos : 0 < plKernelBoundConst m := plKernelBoundConst_pos m
    set ε' : ℝ := ε / (plKernelBoundConst m + 1)
    have hε' : 0 < ε' := by dsimp [ε']; positivity
    obtain ⟨δ, hδ_pos, hδ⟩ := exists_delta_planarGradE_diff m hm Sg hSg hε'
    refine ⟨δ, hδ_pos, fun σ₂ hσ₂ hdist => ?_⟩
    have hb_diff := hδ σ₂ hσ₂ σ₁ hσ₁ hdist
    have hsub_w : IsPlanarWeightedOp m (fun x => planarGradE σ₂ x - planarGradE σ₁ x)
        (AplOp σ₂ - AplOp σ₁) :=
      (hWOp σ₂ hσ₂).sub (hWOp σ₁ hσ₁)
    have hsub_eq : AplOp σ₂ - AplOp σ₁ = planarWeightedOp hm1 hε'.le hb_diff :=
      hsub_w.unique (isPlanarWeightedOp_planarWeightedOp hm1 hε'.le hb_diff)
    rw [dist_eq_norm, hsub_eq]
    calc ‖planarWeightedOp hm1 hε'.le hb_diff‖
        ≤ plKernelBoundConst m * ε' := norm_planarWeightedOp_le hm1 hε'.le hb_diff
      _ < (plKernelBoundConst m + 1) * ε' := by nlinarith
      _ = ε := by
          dsimp [ε']
          exact mul_div_cancel₀ ε (by positivity)
  · rw [hAplOp_eq σ hσ]
    exact isCompactOperator_planarWeightedOp hm1 hB₀.le (hCoeff σ hσ)

end UnforcedLeray.Short.IIb

namespace Short.PartIIb

abbrev PlanarInteractionCompactStep : Prop :=
  UnforcedLeray.Short.IIb.PlanarInteractionCompactStep

theorem planarInteractionCompactStep_proof : PlanarInteractionCompactStep :=
  UnforcedLeray.Short.IIb.planarInteractionCompactStep_proof

end Short.PartIIb

end
