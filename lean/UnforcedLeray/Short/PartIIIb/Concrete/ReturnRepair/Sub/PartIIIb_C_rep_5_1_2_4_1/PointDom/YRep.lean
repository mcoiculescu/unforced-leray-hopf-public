import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.Gate
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.Slice
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.Congr
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.SourceFinite
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Support
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.ParamDmu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# `PDYRep`: `Y` in phase-lag form

Source `the November 2 reference manuscript` 4171, 4180-4186, 3611-3621.
Assembly of `paramDmuCausal`, `pdX0Rep`, `pdOutPrimRep`, `pdSourceFinite`, `pdFullKerReg`,
`pdSupport`: the kernel is gated by a smooth bump around the receiver so that the global
hypotheses of `ParamDmuCausal` hold, and `physDmu` only sees two slices through the point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_srcWeight_meas (μ τ : ℝ) :
    Measurable fun e : ℝ × Space => srcWeight μ (τ - e.1) e.2 := by
  have hlam : Measurable fun e : ℝ × Space => pdLam (τ - e.1) := by unfold pdLam; fun_prop
  have hz2 : Measurable fun e : ℝ × Space => e.2 2 :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable.comp measurable_snd
  unfold srcWeight
  have h1 : Measurable fun e : ℝ × Space => pdLam (τ - e.1) ^ (2 * μ + 3) :=
    hlam.pow_const _
  have h2 : Measurable fun e : ℝ × Space => ((1 + pdLam (τ - e.1) * ‖e.2‖) ^ 4)⁻¹ :=
    ((measurable_const.add (hlam.mul measurable_snd.norm)).pow_const 4).inv
  have h3 : Measurable fun e : ℝ × Space => (1 + (pdLam (τ - e.1) * e.2 2) ^ 2)⁻¹ :=
    (measurable_const.add ((hlam.mul hz2).pow_const 2)).inv
  exact h1.mul (h2.add h3)

theorem pdYRep : PDYRep := by
  intro ν μ R c δ χy g hν hR1 hc hμ0 hμ1 hχ hδ0 hδ1 hg hg0 τ y hy hage hfinMaj
  have hR : 0 < R := by linarith
  -- constants
  set ρ₀ : ℝ := Real.sqrt (5 / 6) * ϱ y with hρ₀
  have hsq : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hsq0 : 0 ≤ Real.sqrt (5 / 6) := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ ρ₀ := by positivity
  have hρy : ρ₀ < ϱ y := by
    rw [hρ₀]; nlinarith
  have hsupp0 : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z ≤ ρ₀ := by
    intro σ z hz
    by_contra hlt
    exact hz (pdSupport ν R c g hν hR hg0 y hy hage σ z (not_le.1 hlt))
  set r₁ : ℝ := (ρ₀ + ϱ y) / 2 with hr₁
  have hρ : ρ₀ < r₁ := by rw [hr₁]; linarith
  have hr₁y : r₁ < ϱ y := by rw [hr₁]; linarith
  set Y : ℝ := ‖y‖ + 1 with hY
  set ε : ℝ := min 1 (ϱ y - r₁) / 4 with hε
  have hε0 : 0 < ε := by
    rw [hε]; have : 0 < min 1 (ϱ y - r₁) := lt_min one_pos (by linarith)
    positivity
  have hε1 : ε ≤ 1 := by
    rw [hε]; have := min_le_left 1 (ϱ y - r₁); linarith
  have hε14 : ε ≤ 1 / 4 := by
    rw [hε]; have := min_le_left 1 (ϱ y - r₁); linarith
  have hε2 : 2 * ε ≤ (ϱ y - r₁) / 2 := by
    rw [hε]; have := min_le_right 1 (ϱ y - r₁); linarith
  set Ω : Set Space := {y' | r₁ < ϱ y' ∧ ‖y'‖ < Y} with hΩ
  have hΩball : Metric.closedBall y (2 * ε) ⊆ Ω := by
    intro y' hy'
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hy'
    refine ⟨?_, ?_⟩
    · have h1 := varrho_triangle y y'
      have h2 := varrho_le_norm (y - y')
      linarith
    · have h0 : ‖y'‖ ≤ ‖y‖ + ‖y - y'‖ := by
        calc ‖y'‖ = ‖y - (y - y')‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      rw [hY]; linarith
  -- bump
  let b0 : ContDiffBump y := ⟨ε, 2 * ε, hε0, by linarith⟩
  set b : Space → ℝ := fun y' => b0 y' with hb
  have hbd : ContDiff ℝ 2 b := b0.contDiff
  have hts : tsupport b ⊆ Ω := by
    have : tsupport b = Metric.closedBall y (2 * ε) := b0.tsupport_eq
    rw [this]; exact hΩball
  have hb1 : ∀ y' ∈ Metric.ball y ε, b y' = 1 := fun y' hy' =>
    b0.one_of_mem_closedBall (Metric.ball_subset_closedBall hy')
  have hballΩ : ∀ y' ∈ Metric.ball y ε, y' ∈ Ω := fun y' hy' =>
    hΩball (Metric.closedBall_subset_closedBall (by linarith)
      (Metric.ball_subset_closedBall hy'))
  -- finiteness and regularity
  have hfinW := pdSourceFinite ν μ R c δ g hν hR hc hμ0 hμ1 hδ0 hδ1 hg hg0 τ y hy hage hfinMaj ε hε0
  obtain ⟨C, hC0, hCb⟩ := pdFullKerReg ν μ R χy hν hR hμ0 hμ1 hχ r₁ ρ₀ Y hρ0 hρ
  set kk : ℝ → Space → ℝ × Space → Space := fun h y' e =>
    fullKer ν μ R χy h y' e.2 (oldPhys R c g e.1 e.2) with hkk
  have hMz : ∀ e : ℝ × Space, oldPhys R c g e.1 e.2 = 0 → ∀ h y', kk h y' e = 0 := by
    intro e he h y'; simp only [hkk, he, yr_fullKer_zero]
  have hreg : ∀ e : ℝ × Space, ∀ y' ∈ Ω, ∀ h : ℝ, 0 < h →
      ContDiffAt ℝ 2 (fun y'' => kk h y'' e) y' ∧ DifferentiableAt ℝ (fun h' => kk h' y' e) h := by
    intro e y' hy' h hh
    by_cases hM : oldPhys R c g e.1 e.2 = 0
    · have h0 : ∀ h y', kk h y' e = 0 := hMz e hM
      simp only [h0]
      exact ⟨contDiffAt_const, differentiableAt_const _⟩
    · have := (hCb e.2 (oldPhys R c g e.1 e.2) (hsupp0 _ _ hM) y' hy'.1 hy'.2).2 h hh
      exact ⟨this.1, this.2.1⟩
  have hmeas : ∀ y' ∈ Ω, ∀ s : ℝ, Measurable fun e : ℝ × Space =>
      if e.1 < s then kk (s - e.1) y' e else 0 := fun y' hy' s =>
    yr_fullKer_meas ν μ R c χy g hg s y' (fun σ z h =>
      lt_of_le_of_lt (hsupp0 σ z h) (hρ.trans hy'.1))
  obtain ⟨m1, m2, m3, m4⟩ := yr_gate_meas b kk Ω hbd hts hreg hmeas
  set k : ℝ → Space → ℝ × Space → Space := yrGate b kk with hk
  -- eventual equalities
  have ev_h : ∀ (e : ℝ × Space) (y' : Space), y' ∈ Metric.ball y ε → ∀ h : ℝ, 0 < h →
      (fun h' => k h' y' e) =ᶠ[𝓝 h] fun h' => kk h' y' e := by
    intro e y' hy' h hh
    filter_upwards [eventually_gt_nhds hh] with h' hh'
    simp [hk, yr_gate_pos b kk hh', hb1 y' hy']
  have ev_y : ∀ (e : ℝ × Space) (y' : Space), y' ∈ Metric.ball y ε → ∀ h : ℝ, 0 < h →
      (fun y'' => k h y'' e) =ᶠ[𝓝 y'] fun y'' => kk h y'' e := by
    intro e y' hy' h hh
    filter_upwards [Metric.isOpen_ball.mem_nhds hy'] with z hz
    simp [hk, yr_gate_pos b kk hh, hb1 z hz]
  -- the majorant
  set B : ℝ × Space → ℝ := fun e => 512 * C * (if e.1 < τ + ε then srcWeight μ (τ - e.1) e.2
    else 0) * IIIa.tensorNorm (oldPhys R c g e.1 e.2) with hB
  have hB0 : ∀ e, 0 ≤ B e := by
    intro e
    have := yr_srcWeight_nonneg μ (τ - e.1) e.2
    have h2 : 0 ≤ IIIa.tensorNorm (oldPhys R c g e.1 e.2) := Real.sqrt_nonneg _
    simp only [hB]
    split_ifs <;> positivity
  have hBint : Integrable B := by
    have hmB : Measurable B := by
      have hS : MeasurableSet {e : ℝ × Space | e.1 < τ + ε} :=
        measurableSet_lt measurable_fst measurable_const
      have : Measurable fun e : ℝ × Space => if e.1 < τ + ε then srcWeight μ (τ - e.1) e.2
          else 0 := Measurable.ite hS (yr_srcWeight_meas μ τ) measurable_const
      exact (measurable_const.mul this).mul (yr_tensorNorm_meas R c g hg)
    refine ⟨hmB.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∀ e : ℝ × Space, ‖B e‖ₑ = ENNReal.ofReal (512 * C) * ((if e.1 < τ + ε then
        ENNReal.ofReal (srcWeight μ (τ - e.1) e.2) else 0) *
          IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
      intro e
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hB0 e)]
      unfold IIIa.srcNorm
      by_cases h : e.1 < τ + ε
      · have := yr_srcWeight_nonneg μ (τ - e.1) e.2
        have h2 : 0 ≤ IIIa.tensorNorm (oldPhys R c g e.1 e.2) := Real.sqrt_nonneg _
        simp only [hB, if_pos h]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
      · simp [hB, h]
    simp_rw [hle]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinW
  -- domination
  have hdom : ∀ (e : ℝ × Space), ∀ τ' ∈ Metric.ball τ ε, e.1 < τ' → ∀ y' ∈ Metric.ball y ε,
      ‖k (τ' - e.1) y' e‖ ≤ B e ∧ ‖deriv (fun h => k h y' e) (τ' - e.1)‖ ≤ B e ∧
        ‖fderiv ℝ (fun y'' => k (τ' - e.1) y'' e) y'‖ ≤ B e ∧
        ‖iteratedFDeriv ℝ 2 (fun y'' => k (τ' - e.1) y'' e) y'‖ ≤ B e := by
    intro e τ' hτ' he y' hy'
    have hh : 0 < τ' - e.1 := sub_pos.2 he
    have hτ'a : |τ' - τ| < ε := by rwa [Metric.mem_ball, Real.dist_eq] at hτ'
    have hEy := ev_y e y' hy' _ hh
    have hEh := ev_h e y' hy' _ hh
    have e1 : k (τ' - e.1) y' e = kk (τ' - e.1) y' e := hEy.self_of_nhds
    have e2 : deriv (fun h => k h y' e) (τ' - e.1) = deriv (fun h => kk h y' e) (τ' - e.1) :=
      hEh.deriv_eq
    have e3 : fderiv ℝ (fun y'' => k (τ' - e.1) y'' e) y' =
        fderiv ℝ (fun y'' => kk (τ' - e.1) y'' e) y' := hEy.fderiv_eq
    have e4 : iteratedFDeriv ℝ 2 (fun y'' => k (τ' - e.1) y'' e) y' =
        iteratedFDeriv ℝ 2 (fun y'' => kk (τ' - e.1) y'' e) y' :=
      (hEy.iteratedFDeriv ℝ 2).self_of_nhds
    rw [e1, e2, e3, e4]
    by_cases hM : oldPhys R c g e.1 e.2 = 0
    · have h0 : ∀ h y', kk h y' e = 0 := hMz e hM
      have hz1 : (fun h => kk h y' e) = fun _ => 0 := funext fun h => h0 h y'
      have hz2 : (fun y'' => kk (τ' - e.1) y'' e) = fun _ => 0 := funext fun y'' => h0 _ y''
      have z1 : deriv (fun h => kk h y' e) (τ' - e.1) = 0 := by rw [hz1]; exact deriv_const _ _
      have z2 : fderiv ℝ (fun y'' => kk (τ' - e.1) y'' e) y' = 0 := by
        rw [hz2]; exact (hasFDerivAt_const (0 : Space) y').fderiv
      have z3 : iteratedFDeriv ℝ 2 (fun y'' => kk (τ' - e.1) y'' e) y' = 0 := by
        rw [hz2]; exact congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (n := 2) (E := Space)
          (F := Space)) y'
      rw [h0, z1, z2, z3]
      simp only [norm_zero]
      exact ⟨hB0 e, hB0 e, hB0 e, hB0 e⟩
    · have hbnd := (hCb e.2 (oldPhys R c g e.1 e.2) (hsupp0 _ _ hM) y' (hballΩ y' hy').1 (hballΩ y' hy').2).2
        (τ' - e.1) hh
      have hτe : e.1 < τ + ε := by have := (abs_lt.1 hτ'a).2; linarith
      have hcmp := yr_srcWeight_cmp μ hμ0 hμ1 (τ - e.1) (τ' - e.1) e.2 (by
        have : τ' - e.1 - (τ - e.1) = τ' - τ := by ring
        rw [this]; exact hτ'a.le.trans hε1)
      have hT : 0 ≤ IIIa.tensorNorm (oldPhys R c g e.1 e.2) := Real.sqrt_nonneg _
      have hfin : C * srcWeight μ (τ' - e.1) e.2 * IIIa.tensorNorm (oldPhys R c g e.1 e.2) ≤ B e := by
        simp only [hB, if_pos hτe]
        have : C * srcWeight μ (τ' - e.1) e.2 ≤ 512 * C * srcWeight μ (τ - e.1) e.2 := by
          nlinarith
        exact mul_le_mul_of_nonneg_right this hT
      obtain ⟨_, _, b1, b2, b3, b4⟩ := hbnd
      exact ⟨b1.trans hfin, b2.trans hfin, b3.trans hfin, b4.trans hfin⟩
  have hcont : ∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y' ∈ Metric.ball y ε,
      ContDiffAt ℝ 2 (fun y'' => k h y'' e) y' ∧ DifferentiableAt ℝ (fun h' => k h' y' e) h :=
    fun e h hh y' _ => ⟨(yr_gate_contDiff b kk Ω hbd hts hreg e hh).contDiffAt,
      yr_gate_diff_h b kk Ω (fun y' hy => hts (subset_tsupport _ hy)) hreg e y' hh⟩
  have htend : ∀ (e : ℝ × Space), ∀ y' ∈ Metric.ball y ε,
      Tendsto (fun h => k h y' e) (𝓝[>] 0) (𝓝 0) := by
    intro e y' hy'
    have hev : (fun h => k h y' e) =ᶠ[𝓝[>] 0] fun h => kk h y' e :=
      eventually_nhdsWithin_of_forall fun h hh => by
        have hh' : 0 < h := hh
        simp [hk, yr_gate_pos b kk hh', hb1 y' hy']
    refine Tendsto.congr' hev.symm ?_
    by_cases hM : oldPhys R c g e.1 e.2 = 0
    · have h0 : ∀ h y', kk h y' e = 0 := hMz e hM
      simp only [h0]; exact tendsto_const_nhds
    · exact (hCb e.2 (oldPhys R c g e.1 e.2) (hsupp0 _ _ hM) y' (hballΩ y' hy').1
        (hballΩ y' hy').2).1
  have key := paramDmuCausal ν (μ + 1) k τ y ε B hε0 hBint hcont htend hdom
    (fun τ' y' => (m1 τ' y').aestronglyMeasurable) m2 m3 m4
  have hslice : ∀ τ' : ℝ, |τ' - τ| < ε → ∀ x ∈ Metric.ball y ε,
      wardX ν μ R c χy g τ' x = ∫ e : ℝ × Space, if e.1 < τ' then kk (τ' - e.1) x e else 0 :=
    fun τ' hτ' x hx => yr_slice ν μ R c χy g hν hR hc hμ0 hμ1 hg hρ0 hρ hsupp0 hε1 hfinW
      τ' hτ' x (hballΩ x hx).1 (hballΩ x hx).2
  have hGeq : ∀ (t : ℝ), ∀ y' ∈ Metric.ball y ε,
      (∫ e : ℝ × Space, if e.1 < t then k (t - e.1) y' e else 0) =
        ∫ e : ℝ × Space, if e.1 < t then kk (t - e.1) y' e else 0 := by
    intro t y' hy'
    congr 1; funext e
    by_cases h : e.1 < t
    · simp [h, hk, yr_gate_pos b kk (sub_pos.2 h), hb1 y' hy']
    · simp [h]
  have hyball : y ∈ Metric.ball y ε := Metric.mem_ball_self hε0
  have hcong : physDmu ν (μ + 1) (wardX ν μ R c χy g) τ y =
      physDmu ν (μ + 1) (fun τ' y' => ∫ e : ℝ × Space,
        if e.1 < τ' then k (τ' - e.1) y' e else 0) τ y := by
    refine yr_physDmu_congr ν (μ + 1) _ _ τ y ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds τ hε0] with t ht
      rw [hslice t (by rwa [Metric.mem_ball, Real.dist_eq] at ht) y hyball, hGeq t y hyball]
    · filter_upwards [Metric.ball_mem_nhds y hε0] with y' hy'
      rw [hslice τ (by simpa using hε0) y' hy', hGeq τ y' hy']
  show physDmu ν (μ + 1) (wardX ν μ R c χy g) τ y = _
  rw [hcong, key]
  congr 1; funext e
  by_cases h : e.1 < τ
  · simp only [if_pos h]
    have hh : 0 < τ - e.1 := sub_pos.2 h
    exact yr_physDmu_congr ν (μ + 1) _ _ (τ - e.1) y (ev_h e y hyball _ hh) (ev_y e y hyball _ hh)
  · simp [h]

end UnforcedLeray.Short.PartIIIb.Concrete

end
