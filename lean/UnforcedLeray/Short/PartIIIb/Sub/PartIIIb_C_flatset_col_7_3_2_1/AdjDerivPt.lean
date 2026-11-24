import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivGaussLap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3.Bounded
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `T0adjPtDeriv` (task `PartIII-b:C/flatset/col/7/3/2/1/2/2`)

Source `the November 2 reference manuscript` 1650-1656.  For a smooth band test
`ζ`, `ν > 0`, `t > 0` and a point with age `p.1 > 0`, the formula `t0adjFormula` is differentiated
in time.  Writing `θ(s) = ν a (eˢ - 1)`, `σ(s) = eˢ a` (`a = p.1`), the formula equals
`e^{-s/2} ∫ G_{θ(s)}(y) ζ(σ(s), p.2 - y) dy`.  Differentiating under the integral (dominated
convergence in `s`) and using the planar heat equation `PlaneGaussDtLap` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.Heat (gaussDt)

/-! ### Elementary objects -/

/-- The heat time `θ(s) = ν a (eˢ - 1)`. -/
def ptTh (ν a s : ℝ) : ℝ := ν * a * (Real.exp s - 1)

/-- The dilated age `σ(s) = eˢ a`. -/
def ptSg (a s : ℝ) : ℝ := Real.exp s * a

/-- The kernel integrand `G_{θ(u)}(y) ζ(σ(u), w - ι y)`. -/
def ptFk (ν a : ℝ) (ζ : Profile → MeridC) (w : ℝ × ℝ) (u : ℝ) (y : Euc 2) : MeridC :=
  gaussKernel 2 (ptTh ν a u) y • ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y)

/-- The derivative integrand of `ptFk` in `u`. -/
def ptFp (ν a : ℝ) (ζ : Profile → MeridC) (w : ℝ × ℝ) (u : ℝ) (y : Euc 2) : MeridC :=
  gaussKernel 2 (ptTh ν a u) y •
      ((Real.exp u * a) • pdS ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y))
    + (gaussDt 2 (ptTh ν a u) y * (ν * a * Real.exp u)) • ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y)

/-- The age window on which the bounds are uniform. -/
def ptS (ν a t : ℝ) : Set ℝ :=
  {u | (ptTh ν a t / 2 < ptTh ν a u ∧ ptTh ν a u < 2 * ptTh ν a t) ∧ u ∈ Ioo (t - 1) (t + 1)}

/-- The integrable majorant. -/
def ptBd (A K M1 M2 ν a t : ℝ) (y : Euc 2) : ℝ :=
  (A * (ν * a * Real.exp (t + 1)) * M1 + K * (Real.exp (t + 1) * a) * M2)
    * Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2)

lemma ptTh_hasDerivAt (ν a s : ℝ) : HasDerivAt (ptTh ν a) (ν * a * Real.exp s) s := by
  unfold ptTh
  exact ((Real.hasDerivAt_exp s).sub_const 1).const_mul (ν * a)

lemma ptSg_hasDerivAt (a s : ℝ) : HasDerivAt (ptSg a) (Real.exp s * a) s := by
  unfold ptSg
  exact (Real.hasDerivAt_exp s).mul_const a

lemma ptTh_pos {ν a t : ℝ} (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) : 0 < ptTh ν a t := by
  unfold ptTh
  have h1 : t + 1 < Real.exp t := by linarith [Real.add_one_lt_exp ht.ne']
  exact mul_pos (mul_pos hν ha) (by linarith)

lemma ptCont_shift {ζ : Profile → MeridC} (hζc : Continuous ζ) (σ : ℝ) (w : ℝ × ℝ) :
    Continuous (fun y : Euc 2 => ζ (σ, w - UnforcedLeray.B0224.planeι y)) :=
  hζc.comp (continuous_const.prodMk
    (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))

/-- `∂_s`-type derivative of a smooth band test is again a smooth band test. -/
lemma ptPdS_meridTest {c : ℝ} {ζ : Profile → MeridC} (h : IsMeridTest c ζ) :
    IsMeridTest c (pdS ζ) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := h.band
  have hK : IsClosed {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hsub : tsupport ζ ⊆ {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    closure_minimal (fun p hp => hb p hp) hK
  refine ⟨isMeridTest_pdS_aux h, pd_periodic_aux h.periodic _, s0, s1, L, hs0, fun p hp => ?_⟩
  have hf : fderiv ℝ ζ p ≠ 0 := fun h0 => hp (by unfold pdS; rw [h0]; simp)
  exact hsub (support_fderiv_subset ℝ (Function.mem_support.mpr hf))

/-- Gaussian envelope of the heat kernel on a window of times. -/
lemma ptGaussEnv {θ0 : ℝ} (h0 : 0 < θ0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, θ0 / 2 < s → s < 2 * θ0 → ∀ y : Euc 2,
      gaussKernel 2 s y ≤ K * Real.exp (-(1 / (16 * θ0)) * ‖y‖ ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hh : 0 < θ0 / 2 := half_pos h0
  refine ⟨(4 * Real.pi * (θ0 / 2)) ^ (-((2 : ℕ) : ℝ) / 2), ?_, fun s hs1 hs2 y => ?_⟩
  · exact (Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num) hpi) hh) _).le
  have hs : 0 < s := by linarith
  rw [UnforcedLeray.Gaussian.gaussKernel_eq_exp]
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le
    (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi.le) hh.le) _)
  · apply Real.rpow_le_rpow_of_nonpos (mul_pos (mul_pos (by norm_num) hpi) hh)
    · nlinarith [Real.pi_pos]
    · norm_num
  · apply Real.exp_le_exp.mpr
    have h1 : (16 * θ0)⁻¹ ≤ (4 * s)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖y‖)
    rw [one_div]
    linarith

/-- Integrability of `G_θ · g` for a bounded continuous `g`. -/
lemma ptIntKer {θ : ℝ} (hθ : 0 < θ) {g : Euc 2 → MeridC} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun y : Euc 2 => gaussKernel 2 θ y • g y) := by
  refine ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).const_mul M).mono' ?_ ?_
  · exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) θ).smul hg).aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    have hk := UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) hθ y
    have h2 := mul_le_mul_of_nonneg_left (hM y) hk
    show ‖gaussKernel 2 θ y • g y‖ ≤ M * gaussKernel 2 θ y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk]
    linarith [mul_comm M (gaussKernel 2 θ y)]

/-- Integrability of `f · g` for an envelope `|f| ≤ C e^{-b|y|²}` and bounded continuous `g`. -/
lemma ptIntEnv {f : Euc 2 → ℝ} {g : Euc 2 → MeridC} {b C M : ℝ} (hb : 0 < b)
    (hf : Continuous f) (hg : Continuous g) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hfb : ∀ y, |f y| ≤ C * Real.exp (-b * ‖y‖ ^ 2)) (hgb : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun y : Euc 2 => f y • g y) := by
  refine ((UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) hb).const_mul
    (C * M)).mono' ?_ ?_
  · exact (hf.smul hg).aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    have hE : 0 ≤ Real.exp (-b * ‖y‖ ^ 2) := (Real.exp_pos _).le
    show ‖f y • g y‖ ≤ C * M * Real.exp (-b * ‖y‖ ^ 2)
    rw [norm_smul, Real.norm_eq_abs]
    calc |f y| * ‖g y‖ ≤ (C * Real.exp (-b * ‖y‖ ^ 2)) * M :=
          mul_le_mul (hfb y) (hgb y) (norm_nonneg _) (mul_nonneg hC hE)
      _ = C * M * Real.exp (-b * ‖y‖ ^ 2) := by ring

/-- The formula for `t0adjFormula` at positive times as a Gaussian convolution. -/
lemma ptFormula {c ν s : ℝ} {φ : Profile → MeridC} (hφ : UnforcedLeray.B0220.QPeriodic c φ)
    (hν : 0 < ν) (p : Profile) (hp : 0 < p.1) (hs : 0 < s) :
    t0adjFormula c ν s φ p = Real.exp (-s / 2) • ∫ y : Euc 2, ptFk ν p.1 φ p.2 s y := by
  have h1 : s + 1 < Real.exp s := by linarith [Real.add_one_lt_exp hs.ne']
  have hθ : 0 < ν * p.1 * (Real.exp s - 1) := mul_pos (mul_pos hν hp) (by linarith)
  simp only [t0adjFormula]
  rw [UnforcedLeray.B0220.periodize_of_periodic φ hφ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rfl

set_option maxHeartbeats 1000000 in
/-- Differentiation of the age-`s` kernel integral in `s` (dominated convergence). -/
lemma ptHasDerivG {c ν a t : ℝ} {ζ : Profile → MeridC} (hc : 0 < c) (hζ : IsMeridTest c ζ)
    (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) (w : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => ∫ y : Euc 2, ptFk ν a ζ w s y)
      (∫ y : Euc 2, ptFp ν a ζ w t y) t := by
  have hθ0 : 0 < ptTh ν a t := ptTh_pos hν ha ht
  have hcont : Continuous (ptTh ν a) := by unfold ptTh; fun_prop
  have e1 : ∀ᶠ u in 𝓝 t, ptTh ν a t / 2 < ptTh ν a u :=
    (hcont.tendsto t).eventually_const_lt (by linarith)
  have e2 : ∀ᶠ u in 𝓝 t, ptTh ν a u < 2 * ptTh ν a t :=
    (hcont.tendsto t).eventually_lt_const (by linarith)
  have e3 : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hS : ptS ν a t ∈ 𝓝 t := by
    filter_upwards [e1, e2, e3] with u h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hpdc : Continuous (pdS ζ) := (ptPdS_meridTest hζ).smooth.continuous
  obtain ⟨A, hA0, hA⟩ := UnforcedLeray.Heat.abs_gaussDt_le (d := 2) hθ0
  obtain ⟨K, hK0, hK⟩ := ptGaussEnv hθ0
  obtain ⟨M1, hM1⟩ := merid_test_bounded c hc ζ hζ
  obtain ⟨M2, hM2⟩ := merid_test_bounded c hc (pdS ζ) (ptPdS_meridTest hζ)
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hpos : 0 < 1 / (16 * ptTh ν a t) := one_div_pos.mpr (by linarith)
  -- pointwise derivative in the age parameter
  have hderiv : ∀ (y : Euc 2) (u : ℝ), u ∈ ptS ν a t →
      HasDerivAt (fun u : ℝ => ptFk ν a ζ w u y) (ptFp ν a ζ w u y) u := by
    intro y u hu
    have hu1 : ptTh ν a t / 2 < ptTh ν a u := hu.1.1
    have hθu : 0 < ptTh ν a u := by linarith
    have hc1 : HasDerivAt (fun u : ℝ => gaussKernel 2 (ptTh ν a u) y)
        (gaussDt 2 (ptTh ν a u) y * (ν * a * Real.exp u)) u :=
      (UnforcedLeray.Heat.hasDerivAt_gaussKernel_time hθu y).comp u (ptTh_hasDerivAt ν a u)
    have hsg : HasDerivAt (fun u : ℝ => (ptSg a u, w - UnforcedLeray.B0224.planeι y))
        (Real.exp u * a, (0 : ℝ × ℝ)) u :=
      (ptSg_hasDerivAt a u).prodMk (hasDerivAt_const u (w - UnforcedLeray.B0224.planeι y))
    have hζd : HasFDerivAt ζ (fderiv ℝ ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y))
        (ptSg a u, w - UnforcedLeray.B0224.planeι y) :=
      ((hζ.smooth.differentiable (by simp)) _).hasFDerivAt
    have hcomp := hζd.comp_hasDerivAt u hsg
    have hpd : fderiv ℝ ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y) (Real.exp u * a, 0, 0)
        = (Real.exp u * a) • pdS ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y) := by
      unfold pdS
      rw [show ((Real.exp u * a, 0, 0) : Profile) = (Real.exp u * a) • ((1 : ℝ), (0 : ℝ), (0 : ℝ))
        from by ext <;> simp, map_smul]
    have hd : HasDerivAt (fun u : ℝ => ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y))
        ((Real.exp u * a) • pdS ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y)) u := by
      rw [← hpd]
      exact hcomp
    unfold ptFk ptFp
    exact hc1.smul hd
  have hFk_meas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (ptFk ν a ζ w u)
      (volume : Measure (Euc 2)) :=
    Filter.Eventually.of_forall fun u =>
      ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (ptTh ν a u)).smul
        (ptCont_shift hζc (ptSg a u) w)).aestronglyMeasurable
  have hFk_int : Integrable (ptFk ν a ζ w t) (volume : Measure (Euc 2)) :=
    ptIntKer (g := fun y => ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) hθ0
      (ptCont_shift hζc (ptSg a t) w) (fun y => hM1 _)
  have hFp_cont : Continuous (ptFp ν a ζ w t) := by
    unfold ptFp
    exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (ptTh ν a t)).smul
        ((ptCont_shift hpdc (ptSg a t) w).const_smul (Real.exp t * a))).add
      ((((UnforcedLeray.Heat.continuous_gaussDt 2 (ptTh ν a t)).mul continuous_const).smul
        (ptCont_shift hζc (ptSg a t) w)))
  have hFp_meas : AEStronglyMeasurable (ptFp ν a ζ w t) (volume : Measure (Euc 2)) :=
    hFp_cont.aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ u ∈ ptS ν a t,
      ‖ptFp ν a ζ w u y‖ ≤ ptBd A K M1 M2 ν a t y := by
    refine ae_of_all _ fun y u hu => ?_
    have hu1 : ptTh ν a t / 2 < ptTh ν a u := hu.1.1
    have hu2 : ptTh ν a u < 2 * ptTh ν a t := hu.1.2
    have hu3 : u < t + 1 := hu.2.2
    have hθu : 0 < ptTh ν a u := by linarith
    have hgD := hA (ptTh ν a u) hu1 hu2 y
    have hgK := hK (ptTh ν a u) hu1 hu2 y
    have hgK0 : 0 ≤ gaussKernel 2 (ptTh ν a u) y :=
      UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) hθu y
    have hE : 0 ≤ Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2) := (Real.exp_pos _).le
    have hexp1 : Real.exp u ≤ Real.exp (t + 1) := Real.exp_le_exp.mpr hu3.le
    have hexp0 : 0 < Real.exp u := Real.exp_pos u
    have hk : 0 ≤ ν * a * Real.exp u := (mul_pos (mul_pos hν ha) hexp0).le
    have hk' : ν * a * Real.exp u ≤ ν * a * Real.exp (t + 1) :=
      mul_le_mul_of_nonneg_left hexp1 (mul_pos hν ha).le
    have hT1 : ‖(gaussDt 2 (ptTh ν a u) y * (ν * a * Real.exp u))
        • ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y)‖
        ≤ (A * Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2) * (ν * a * Real.exp (t + 1))) * M1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
      exact mul_le_mul (mul_le_mul (hA (ptTh ν a u) hu1 hu2 y) hk' hk (mul_nonneg hA0 hE))
        (hM1 _) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hA0 hE) (mul_pos (mul_pos hν ha) (Real.exp_pos _)).le)
    have hT2 : ‖gaussKernel 2 (ptTh ν a u) y •
        ((Real.exp u * a) • pdS ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y))‖
        ≤ (K * Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2) * (Real.exp (t + 1) * a)) * M2 := by
      have hea : Real.exp u * a ≤ Real.exp (t + 1) * a := mul_le_mul_of_nonneg_right hexp1 ha.le
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgK0,
        abs_of_pos (mul_pos hexp0 ha)]
      have h3 : gaussKernel 2 (ptTh ν a u) y * (Real.exp u * a *
          ‖pdS ζ (ptSg a u, w - UnforcedLeray.B0224.planeι y)‖)
          ≤ (K * Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2) * (Real.exp (t + 1) * a)) * M2 := by
        have h4 := mul_le_mul hea (hM2 (ptSg a u, w - UnforcedLeray.B0224.planeι y))
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le ha.le)
        have h5 := mul_le_mul hgK h4 (mul_nonneg (mul_nonneg hexp0.le ha.le) (norm_nonneg _))
          (mul_nonneg hK0 hE)
        linarith [h5]
      linarith [h3]
    unfold ptFp
    refine (norm_add_le _ _).trans ((add_le_add hT2 hT1).trans_eq ?_)
    unfold ptBd
    ring
  have hdiff : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ u ∈ ptS ν a t,
      HasDerivAt (fun u : ℝ => ptFk ν a ζ w u y) (ptFp ν a ζ w u y) u :=
    ae_of_all _ fun y u hu => hderiv y u hu
  have hbd_int : Integrable (ptBd A K M1 M2 ν a t) (volume : Measure (Euc 2)) :=
    (UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) hpos).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc 2)))
    (F := ptFk ν a ζ w) (F' := ptFp ν a ζ w) (bound := ptBd A K M1 M2 ν a t)
    hS hFk_meas hFk_int hFp_meas hbound hbd_int hdiff).2

/-- The time-derivative integrand splits into the `A₀*`-part and the `½`-part (heat equation). -/
lemma ptHid {c ν a t : ℝ} {ζ : Profile → MeridC} (hc : 0 < c) (hζ : IsMeridTest c ζ)
    (hν : 0 < ν) (ha : 0 < a) (ht : 0 < t) (w : ℝ × ℝ) :
    (∫ y : Euc 2, ptFp ν a ζ w t y)
      = (∫ y : Euc 2, ptFk ν a (A0adj ν ζ) w t y) + (1 / 2 : ℝ) • (∫ y : Euc 2, ptFk ν a ζ w t y) := by
  simp only [ptFp, ptFk]
  have hθ0 : 0 < ptTh ν a t := ptTh_pos hν ha ht
  have hk : 0 ≤ ν * a * Real.exp t := (mul_pos (mul_pos hν ha) (Real.exp_pos t)).le
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hpdc : Continuous (pdS ζ) := (ptPdS_meridTest hζ).smooth.continuous
  have hAζ : IsMeridTest c (A0adj ν ζ) := isMeridTest_A0adj ν hζ
  have hAζc : Continuous (A0adj ν ζ) := hAζ.smooth.continuous
  obtain ⟨A, hA0, hA⟩ := UnforcedLeray.Heat.abs_gaussDt_le (d := 2) hθ0
  obtain ⟨M1, hM1⟩ := merid_test_bounded c hc ζ hζ
  obtain ⟨M2, hM2⟩ := merid_test_bounded c hc (pdS ζ) (ptPdS_meridTest hζ)
  obtain ⟨M3, hM3⟩ := merid_test_bounded c hc (A0adj ν ζ) hAζ
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hM2n : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0)
  have hX : Integrable (fun y : Euc 2 => (gaussDt 2 (ptTh ν a t) y * (ν * a * Real.exp t))
      • ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) := by
    refine ptIntEnv (f := fun y => gaussDt 2 (ptTh ν a t) y * (ν * a * Real.exp t))
      (g := fun y => ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))
      (b := 1 / (16 * ptTh ν a t)) (C := A * (ν * a * Real.exp t)) (M := M1)
      (one_div_pos.mpr (by linarith)) ?_ (ptCont_shift hζc _ _) (mul_nonneg hA0 hk) hM1n ?_
      (fun y => hM1 _)
    · exact ((UnforcedLeray.Heat.continuous_gaussDt 2 (ptTh ν a t)).mul continuous_const)
    · intro y
      rw [abs_mul, abs_of_nonneg hk]
      have h1 := hA (ptTh ν a t) (by linarith) (by linarith) y
      calc |gaussDt 2 (ptTh ν a t) y| * (ν * a * Real.exp t)
          ≤ (A * Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2)) * (ν * a * Real.exp t) :=
            mul_le_mul_of_nonneg_right h1 hk
        _ = A * (ν * a * Real.exp t) * Real.exp (-(1 / (16 * ptTh ν a t)) * ‖y‖ ^ 2) := by ring
  have hP : Integrable (fun y : Euc 2 => gaussKernel 2 (ptTh ν a t) y •
      ((Real.exp t * a) • pdS ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))) :=
    ptIntKer (g := fun y => (Real.exp t * a) • pdS ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))
      hθ0 ((ptCont_shift hpdc _ _).const_smul (Real.exp t * a)) (M := |Real.exp t * a| * M2)
      (fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM2 _) (abs_nonneg _))
  have hB : Integrable (fun y : Euc 2 => gaussKernel 2 (ptTh ν a t) y •
      ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) :=
    ptIntKer (g := fun y => ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) hθ0
      (ptCont_shift hζc _ _) (fun y => hM1 _)
  have hC : Integrable (fun y : Euc 2 => gaussKernel 2 (ptTh ν a t) y •
      A0adj ν ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) :=
    ptIntKer (g := fun y => A0adj ν ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) hθ0
      (ptCont_shift hAζc _ _) (fun y => hM3 _)
  -- the `X`-part equals the heat-equation term
  have hXQ : ∫ y : Euc 2, (gaussDt 2 (ptTh ν a t) y * (ν * a * Real.exp t))
      • ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)
      = ∫ y : Euc 2, (ν * a * Real.exp t) • (gaussKernel 2 (ptTh ν a t) y •
          (pdQ (pdQ ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)
            + pdEta (pdEta ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y))) := by
    calc ∫ y : Euc 2, (gaussDt 2 (ptTh ν a t) y * (ν * a * Real.exp t))
          • ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)
        = ∫ y : Euc 2, (ν * a * Real.exp t) •
            (gaussDt 2 (ptTh ν a t) y • ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) := by
          congr 1
          funext y
          rw [mul_smul, smul_comm]
      _ = (ν * a * Real.exp t) • ∫ y : Euc 2,
            gaussDt 2 (ptTh ν a t) y • ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y) :=
          integral_smul _ _
      _ = (ν * a * Real.exp t) • ∫ y : Euc 2, gaussKernel 2 (ptTh ν a t) y •
            (pdQ (pdQ ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)
              + pdEta (pdEta ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)) := by
          rw [plane_gaussDt_lap c hc ζ hζ (ptTh ν a t) (ptSg a t) hθ0 w]
      _ = _ := (integral_smul _ _).symm
  -- pointwise identity for the `A₀*`-integrand
  have hpt : ∀ y : Euc 2,
      (ν * a * Real.exp t) • (gaussKernel 2 (ptTh ν a t) y •
          (pdQ (pdQ ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)
            + pdEta (pdEta ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)))
      = gaussKernel 2 (ptTh ν a t) y • A0adj ν ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)
        - gaussKernel 2 (ptTh ν a t) y • ((Real.exp t * a) •
            pdS ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))
        + (1 / 2 : ℝ) • (gaussKernel 2 (ptTh ν a t) y •
            ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)) := by
    intro y
    simp only [A0adj, ptSg]
    module
  have hQ : ∫ y : Euc 2, (ν * a * Real.exp t) • (gaussKernel 2 (ptTh ν a t) y •
          (pdQ (pdQ ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)
            + pdEta (pdEta ζ) (ptSg a t, w - UnforcedLeray.B0224.planeι y)))
      = ∫ y : Euc 2, (gaussKernel 2 (ptTh ν a t) y •
            A0adj ν ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)
          - gaussKernel 2 (ptTh ν a t) y • ((Real.exp t * a) •
            pdS ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))
          + (1 / 2 : ℝ) • (gaussKernel 2 (ptTh ν a t) y •
            ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))) := by
    congr 1
    funext y
    exact hpt y
  have hCP : Integrable (fun y : Euc 2 => gaussKernel 2 (ptTh ν a t) y •
      A0adj ν ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y)
      - gaussKernel 2 (ptTh ν a t) y • ((Real.exp t * a) •
        pdS ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))) := hC.sub hP
  have hHB : Integrable (fun y : Euc 2 => (1 / 2 : ℝ) • (gaussKernel 2 (ptTh ν a t) y •
      ζ (ptSg a t, w - UnforcedLeray.B0224.planeι y))) := hB.smul (1 / 2 : ℝ)
  rw [integral_add hP hX, hXQ, hQ, integral_add hCP hHB, integral_sub hC hP, integral_smul]
  abel

/-- **`PartIII-b:C/flatset/col/7/3/2/1/2/2`**: the pointwise time derivative of the formula. -/
theorem t0adj_pt_deriv : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0adjPtDeriv := by
  intro c ν hc hν ζ hζ t ht p hp
  have hev : (fun s : ℝ => t0adjFormula c ν s ζ p) =ᶠ[𝓝 t]
      (fun s : ℝ => Real.exp (-s / 2) • ∫ y : Euc 2, ptFk ν p.1 ζ p.2 s y) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ptFormula hζ.periodic hν p hp hs
  have hG := ptHasDerivG hc hζ hν hp ht p.2
  have hE : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (Real.exp (-t / 2) * (-(1 / 2))) t := by
    have h1 : HasDerivAt (fun s : ℝ => -s / 2) (-1 / 2) t := ((hasDerivAt_id' t).neg).div_const 2
    exact (h1.exp).congr_deriv (by ring)
  have hprod := hE.smul hG
  have hval := ptFormula (isMeridTest_A0adj ν hζ).periodic hν p hp ht
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  rw [hval]
  refine hprod.congr_deriv ?_
  rw [ptHid hc hζ hν hp ht p.2,
    show (Real.exp (-t / 2) * -(1 / 2)) • (∫ y : Euc 2, ptFk ν p.1 ζ p.2 t y)
      = -(Real.exp (-t / 2) • ((1 / 2 : ℝ) • ∫ y : Euc 2, ptFk ν p.1 ζ p.2 t y)) by
        rw [mul_neg, neg_smul, smul_smul],
    smul_add]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
