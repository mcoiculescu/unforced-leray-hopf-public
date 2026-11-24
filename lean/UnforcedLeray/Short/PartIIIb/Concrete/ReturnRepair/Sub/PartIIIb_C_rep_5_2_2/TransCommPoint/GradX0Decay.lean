import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_red
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L3_SepX0PhaseBound
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/rep/5/2/2/11/4/2` : `tcGradX0Decay`

Source `the November 2 reference manuscript` 4177-4192, 3603-3647.

* `tcx_fderiv_decay` : `|∇W_μ| ≤ C ϱ^{-4}` for `2 r_o ≤ ϱ` (one more inverse power than
  `SepFarDecay`): on the support `|y - l z| ≥ ϱ y / 2`, so `farMaj_1 ≤ (2/ϱ) farMaj_0`.
* `tcGradX0Decay` : `StreamDecay` from `SepFarDecay` (exponent 3) plus continuity on the compact
  near range; integrability of `ρ (y·∇X₀)_z` from the `ρ^{-4}` bound on `∇X₀` and `|(ρ,0,y₃)| ≤ ρ + |y₃|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private lemma tcx_farMaj_one_le (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hS : IIIa.IsSepSource P rOut T) (τ : ℝ)
    (y : Space) (hy : 2 * rOut ≤ ϱ y) (hr : 0 < rOut) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1)
    (z : Space) :
    farMaj μ T τ 1 y (l, z) ≤ (2 * (ϱ y)⁻¹) * farMaj μ T τ 0 y (l, z) := by
  by_cases hz : rOut < ϱ z
  · have hT : T (τ + 2 * Real.log l) z = 0 := hS.support _ _ hz
    have hn : IIIa.tensorNorm (T (τ + 2 * Real.log l) z) = 0 := by
      rw [hT]; unfold IIIa.tensorNorm; simp
    unfold farMaj
    simp [hn]
  · push Not at hz
    have hgeom := far_norm_lower rOut y z l hl hz
    have hhalf : ϱ y / 2 ≤ ‖y - l • z‖ := by linarith
    have hpos : 0 < ϱ y := by linarith
    have hx0 : 0 < ‖y - l • z‖ := by linarith
    have e : ‖y - l • z‖ ^ (-(4 + ((1 : ℕ) : ℝ))) =
        ‖y - l • z‖ ^ (-(4 + ((0 : ℕ) : ℝ))) * ‖y - l • z‖⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
      congr 1
      push_cast
      ring
    have hinv : ‖y - l • z‖⁻¹ ≤ 2 * (ϱ y)⁻¹ := by
      calc ‖y - l • z‖⁻¹ ≤ (ϱ y / 2)⁻¹ := inv_anti₀ (by positivity) hhalf
        _ = 2 * (ϱ y)⁻¹ := by field_simp
    have hA : 0 ≤ l ^ (2 * μ.re + 2) := Real.rpow_nonneg hl.1.le _
    have hB : 0 ≤ ‖y - l • z‖ ^ (-(4 + ((0 : ℕ) : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    have hN : 0 ≤ IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := Real.sqrt_nonneg _
    unfold farMaj
    simp only
    rw [e]
    have hK : 0 ≤ l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-(4 + ((0 : ℕ) : ℝ))) *
        IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by positivity
    calc l ^ (2 * μ.re + 2) * (‖y - l • z‖ ^ (-(4 + ((0 : ℕ) : ℝ))) * ‖y - l • z‖⁻¹) *
          IIIa.tensorNorm (T (τ + 2 * Real.log l) z)
        = (l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-(4 + ((0 : ℕ) : ℝ))) *
          IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) * ‖y - l • z‖⁻¹ := by ring
      _ ≤ (l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-(4 + ((0 : ℕ) : ℝ))) *
          IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) * (2 * (ϱ y)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv hK
      _ = _ := by ring

/-- `|∇ W_μ| ≤ C ϱ^{-4}` for `2 r_o ≤ ϱ` (source 4177-4192, 3604-3621). -/
private lemma tcx_fderiv_decay (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ.re)
    (hr : 0 < rOut) (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ∃ C : ℝ, ∀ (i : Fin 3) (y : Space), 2 * rOut ≤ ϱ y →
      ‖fderiv ℝ (fun y => IIIa.sepW ν μ T y τ i) y‖ ≤ C * ϱ y ^ (-4 : ℝ) := by
  obtain ⟨CA, hCA0, hAx⟩ := farPointwise IIIa.sepKernelBounds ν μ rOut P T hν hμ hr hP hS τ
  obtain ⟨CB, hBx⟩ := farMajorantBound μ rOut P T hμ hr hP hS hM τ
  refine ⟨2 * CA * CB, fun i y hy => ?_⟩
  have hgap : rOut < ϱ y := by linarith
  have hpos : 0 < ϱ y := by linarith
  obtain ⟨hint, hder⟩ := sepWFderivIntegral ν μ rOut P T hν hμ hr hP hS hM τ i y hgap
  have hB0 := hBx y hy 0 (by norm_num)
  have hc0 : 0 ≤ 2 * (ϱ y)⁻¹ * CA :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hpos.le)) hCA0
  have hint' : Integrable (fun p => (2 * (ϱ y)⁻¹ * CA) * farMaj μ T τ 0 y p) sepRho :=
    hB0.1.const_mul _
  rw [hder]
  refine (norm_integral_le_of_norm_le hint' ?_).trans ?_
  · filter_upwards [ae_mem_Ioo_sepRho] with p hp
    have h1 := (hAx i y hy p.1 hp p.2).2
    have h2 := tcx_farMaj_one_le μ rOut P T hS τ y hy hr p.1 hp p.2
    calc _ ≤ CA * farMaj μ T τ 1 y p := h1
      _ ≤ CA * ((2 * (ϱ y)⁻¹) * farMaj μ T τ 0 y p) := mul_le_mul_of_nonneg_left h2 hCA0
      _ = _ := by ring
  · rw [integral_const_mul]
    have h3 := hB0.2
    have e4 : ϱ y ^ (-4 : ℝ) = (ϱ y)⁻¹ * ϱ y ^ (-3 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hpos]; norm_num
    calc (2 * (ϱ y)⁻¹ * CA) * ∫ p, farMaj μ T τ 0 y p ∂sepRho
        ≤ (2 * (ϱ y)⁻¹ * CA) * (CB * ϱ y ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left h3 hc0
      _ = 2 * CA * CB * ϱ y ^ (-4 : ℝ) := by rw [e4]; ring

private lemma tcx_rpow (ρ : ℝ) (hρ : 0 < ρ) :
    ρ ^ (-4 : ℝ) = (ρ ^ 4)⁻¹ ∧ ρ ^ (-3 : ℝ) = (ρ ^ 3)⁻¹ ∧ ρ ^ (-2 : ℝ) = (ρ ^ 2)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hρ.le, Real.rpow_natCast]
  · rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hρ.le, Real.rpow_natCast]
  · rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hρ.le, Real.rpow_natCast]

private lemma tcx_norm_p (a b : ℝ) (ha : 0 ≤ a) : ‖(!₂[a, 0, b] : Space)‖ ≤ a + |b| := by
  have h := farNorm_sq (!₂[a, 0, b] : Space)
  rw [wardFar_varrho a b ha] at h
  have h2 : (!₂[a, 0, b] : Space) 2 = b := by simp
  rw [h2] at h
  have : ‖(!₂[a, 0, b] : Space)‖ ^ 2 ≤ (a + |b|) ^ 2 := by
    rw [h]; nlinarith [abs_nonneg b, sq_abs b, mul_nonneg ha (abs_nonneg b)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 this

theorem tcGradX0Decay : TCGradX0Decay := by
  intro σ₁ σ₂ ν μ R P T τ y ctx
  obtain ⟨hσ, hν, hν1, hR, hP, hμI, hS, hM, hAx, hyA⟩ := ctx
  have hR0 : 0 < R := by linarith
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = R * Real.sqrt (5 * ν / 6) := ⟨_, rfl⟩
  have hr0pos : 0 < r0 := by rw [hr0]; positivity
  have hS' : IIIa.IsSepSource P r0 T := by rw [hr0]; exact hS
  have hmem : ∀ y' : Space, y' ∈ youngOpen ν R ↔ r0 < ϱ y' := by
    intro y'; rw [hr0]; rfl
  have hYO : youngOpen ν R = {y : Space | r0 < ϱ y} := by
    ext y'; exact hmem y'
  have hμ0 : -(1 / 4) < μ := lt_of_lt_of_le hσ hμI.1
  have hμ' : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]; exact hμ0
  have hμ1 : -(1 / 4 : ℝ) < (((μ : ℝ) : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  -- the receiver `y` is in the young region
  have hyr : r0 < ϱ y := by
    have h1 : R * Real.sqrt ν ≤ ϱ y := hyA.1
    have h2 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have h3 : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h2 hR0
    rw [hr0]; linarith
  have hOpen : IsOpen (youngOpen ν R) := by
    unfold youngOpen
    exact isOpen_lt continuous_const Axi.continuous_ϱ
  have hG : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T y τ i)
      (youngOpen ν R) :=
    fun i => by
      rw [hYO]
      exact sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) r0 P T hν hμ' hr0pos.le hP hS' hM τ i
  have hH : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T y τ i)
      (youngOpen ν R) :=
    fun i => by
      rw [hYO]
      exact sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) r0 P T hν hμ1 hr0pos.le hP hS'
        hM τ i
  have hSm : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) := by
    rw [sepX0_eq_reL]
    exact reL.contDiff.comp_contDiffOn ((contDiffOn_pi.2 hG).sub (contDiffOn_pi.2 hH))
  have K1 : ∀ (y : Space) (i : Fin 3),
      sepX0 ν μ T τ y i =
        (IIIa.sepW ν (μ : ℂ) T y τ i - IIIa.sepW ν ((μ : ℂ) + 1) T y τ i).re := fun y i => rfl
  have hFd : ∀ y : Space, y ∈ youngOpen ν R → DifferentiableAt ℝ (sepX0 ν μ T τ) y :=
    fun y hy => (hSm.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hGd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν R →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ i) y := fun i y hy =>
    ((hG i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hHd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν R →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T x τ i) y := fun i y hy =>
    ((hH i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have Dcomp : ∀ (y v : Space) (i : Fin 3), y ∈ youngOpen ν R →
      fderiv ℝ (sepX0 ν μ T τ) y v i =
        fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i
          - IIIa.sepW ν ((μ : ℂ) + 1) T x τ i).re) y v := by
    intro y v i hy
    have hfun : (fun x => sepX0 ν μ T τ x i) =
        (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i - IIIa.sepW ν ((μ : ℂ) + 1) T x τ i).re) :=
      funext fun x => K1 x i
    rw [← wardFar_proj_fderiv _ y v i (hFd y hy), hfun]
  have Vbound : ∀ (y : Space) (i : Fin 3),
      ‖sepX0 ν μ T τ y i‖ ≤
        ‖IIIa.sepW ν (μ : ℂ) T y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T y τ i‖ := by
    intro y i
    rw [K1 y i]
    exact wardFar_re_sub_le _ _
  obtain ⟨C1, hC1⟩ := sepFarDecay ν (μ : ℂ) r0 P T hν hμ' hr0pos.le hP hS' hM τ
  obtain ⟨C2, hC2⟩ := sepFarDecay ν ((μ : ℂ) + 1) r0 P T hν hμ1 hr0pos.le hP hS' hM τ
  obtain ⟨D1, hD1⟩ := tcx_fderiv_decay ν (μ : ℂ) r0 P T hν hμ' hr0pos hP hS' hM τ
  obtain ⟨D2, hD2⟩ := tcx_fderiv_decay ν ((μ : ℂ) + 1) r0 P T hν hμ1 hr0pos hP hS' hM τ
  have hcv : ‖coordinateVector (2 : Fin 3)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  have hφ : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by fun_prop
  -- ===== part (i) : `StreamDecay` =====
  have hStream : StreamDecay ν R (sepX0 ν μ T) τ := by
    intro r z hr
    rw [← hr0] at hr
    have hLval : ∀ (y : Space) (i : Fin 3), 2 * r0 ≤ ϱ y →
        |sepX0 ν μ T τ y i| ≤ (C1 + C2) * ϱ y ^ (-3 : ℝ) := by
      intro y i h2
      calc |sepX0 ν μ T τ y i| = ‖sepX0 ν μ T τ y i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖IIIa.sepW ν (μ : ℂ) T y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T y τ i‖ := Vbound y i
        _ ≤ C1 * ϱ y ^ (-3 : ℝ) + C2 * ϱ y ^ (-3 : ℝ) :=
            add_le_add (hC1 i y h2).1 (hC2 i y h2).1
        _ = (C1 + C2) * ϱ y ^ (-3 : ℝ) := by ring
    have hLder : ∀ (y : Space), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
        |fderiv ℝ (sepX0 ν μ T τ) y (coordinateVector 2) 2| ≤ (C1 + C2) * ϱ y ^ (-3 : ℝ) := by
      intro y hyU h2
      calc |fderiv ℝ (sepX0 ν μ T τ) y (coordinateVector 2) 2|
          = ‖fderiv ℝ (sepX0 ν μ T τ) y (coordinateVector 2) 2‖ := (Real.norm_eq_abs _).symm
        _ = ‖fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T x τ 2
              - IIIa.sepW ν ((μ : ℂ) + 1) T x τ 2).re) y (coordinateVector 2)‖ := by
            rw [Dcomp y (coordinateVector 2) 2 hyU]
        _ ≤ (‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ 2) y‖
              + ‖fderiv ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T x τ 2) y‖)
              * ‖coordinateVector 2‖ :=
            wardFar_re_fderiv_le _ _ y _ (hGd 2 y hyU) (hHd 2 y hyU)
        _ ≤ (C1 * ϱ y ^ (-3 : ℝ) + C2 * ϱ y ^ (-3 : ℝ)) * 1 := by
            rw [hcv]
            simp only [mul_one]
            exact add_le_add (hC1 2 y h2).2 (hC2 2 y h2).2
        _ = (C1 + C2) * ϱ y ^ (-3 : ℝ) := by ring
    have hmaps : MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
        (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) (youngOpen ν R) := by
      rintro ⟨a, b⟩ hp
      have ha : r ≤ a := hp.1.1
      have hpos : 0 ≤ a := by linarith
      rw [hmem]
      show r0 < ϱ (!₂[a, 0, b] : Space)
      rw [wardFar_varrho a b hpos]
      linarith
    have hFc : ContinuousOn (fun p : ℝ × ℝ => sepX0 ν μ T τ (!₂[p.1, 0, p.2] : Space))
        (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
      hSm.continuousOn.comp hφ.continuousOn hmaps
    have hDc : ContinuousOn (fun p : ℝ × ℝ =>
        fderiv ℝ (sepX0 ν μ T τ) (!₂[p.1, 0, p.2] : Space))
        (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
      (hSm.continuousOn_fderiv_of_isOpen hOpen (by norm_num)).comp hφ.continuousOn hmaps
    have hSc : IsCompact (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
      isCompact_Icc.prod (ProperSpace.isCompact_closedBall z 1)
    obtain ⟨M1, hM1⟩ := hSc.exists_bound_of_continuousOn hFc
    obtain ⟨M2, hM2⟩ := hSc.exists_bound_of_continuousOn hDc.norm
    obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = (|C1| + |C2|) + (2 * r0) ^ 3 * (|M1| + |M2|) :=
      ⟨_, rfl⟩
    have hbound : ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
        ‖ρ * sepX0 ν μ T τ !₂[ρ, 0, z'] 2‖ ≤ Cc * ρ ^ (-(2 : ℝ)) ∧
        ‖ρ * fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤
          Cc * ρ ^ (-(2 : ℝ)) ∧
        ‖ρ * sepX0 ν μ T τ !₂[ρ, 0, z'] 0‖ ≤ Cc * ρ ^ (-(2 : ℝ)) := by
      intro ρ hρ z' hz'
      have hρr : r < ρ := hρ
      have hρpos : 0 < ρ := lt_trans (lt_trans hr0pos hr) hρr
      set y0 : Space := (!₂[ρ, 0, z'] : Space) with hy0
      have hyρ : ϱ y0 = ρ := by
        rw [hy0]
        exact wardFar_varrho ρ z' hρpos.le
      have hy0U : y0 ∈ youngOpen ν R := by
        rw [hmem, hyρ]
        linarith
      have hnn : 0 ≤ (2 * r0) ^ 3 * (|M1| + |M2|) := by positivity
      rcases le_total (2 * r0) ρ with h2 | h2
      · have h2' : 2 * r0 ≤ ϱ y0 := by
          rw [hyρ]
          exact h2
        have hKL : C1 + C2 ≤ Cc := by
          rw [hCc]
          linarith [le_abs_self C1, le_abs_self C2]
        have hA := hLval y0 2 h2'
        have hB := hLder y0 hy0U h2'
        have hD := hLval y0 0 h2'
        rw [hyρ] at hA hB hD
        exact ⟨wardFar_arith ρ _ _ _ hρpos hKL hA, wardFar_arith ρ _ _ _ hρpos hKL hB,
          wardFar_arith ρ _ _ _ hρpos hKL hD⟩
      · have hmemc : (ρ, z') ∈ Icc r (2 * r0) ×ˢ Metric.closedBall z 1 :=
          ⟨⟨hρr.le, h2⟩, Metric.ball_subset_closedBall hz'⟩
        have hVn : ‖sepX0 ν μ T τ y0‖ ≤ M1 := hM1 (ρ, z') hmemc
        have hDn : ‖fderiv ℝ (sepX0 ν μ T τ) y0‖ ≤ M2 := by
          simpa only [norm_norm] using hM2 (ρ, z') hmemc
        have hMM : |M1| + |M2| ≥ 0 := by positivity
        have hVal : ∀ i : Fin 3, |sepX0 ν μ T τ y0 i| ≤ |M1| + |M2| := by
          intro i
          rw [← Real.norm_eq_abs]
          refine (PiLp.norm_apply_le _ i).trans (hVn.trans ?_)
          linarith [le_abs_self M1, abs_nonneg M2]
        have hDer : |fderiv ℝ (sepX0 ν μ T τ) y0 (coordinateVector 2) 2|
            ≤ |M1| + |M2| := by
          rw [← Real.norm_eq_abs]
          refine (PiLp.norm_apply_le _ 2).trans ?_
          refine ((fderiv ℝ (sepX0 ν μ T τ) y0).le_opNorm _).trans ?_
          rw [hcv, mul_one]
          linarith [le_abs_self M2, abs_nonneg M1]
        have hKS : (2 * r0) ^ 3 * (|M1| + |M2|) ≤ Cc := by
          rw [hCc]
          linarith [abs_nonneg C1, abs_nonneg C2]
        exact ⟨wardFar_arith ρ _ _ _ hρpos hKS
            (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 2)),
          wardFar_arith ρ _ _ _ hρpos hKS
            (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM hDer),
          wardFar_arith ρ _ _ _ hρpos hKS
            (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 0))⟩
    refine ⟨⟨fun ρ => Cc * ρ ^ (-(2 : ℝ)), ?_, fun ρ hρ z' hz' =>
      ⟨(hbound ρ hρ z' hz').1, (hbound ρ hρ z' hz').2.1⟩⟩, ?_⟩
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (hr0pos.trans hr)).const_mul Cc
    · have hz : Tendsto (fun ρ : ℝ => Cc * ρ ^ (-(2 : ℝ))) atTop (nhds 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul Cc
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [eventually_gt_atTop r] with ρ hρ
      exact (hbound ρ hρ z (Metric.mem_ball_self one_pos)).2.2
  refine ⟨hStream, ?_⟩
  -- ===== part (ii) : integrability of `ρ (y·∇X₀)_z` =====
  set a : ℝ := ϱ y with ha
  have hapos : 0 < a := hr0pos.trans hyr
  set b : ℝ := max a (2 * r0) with hb
  have hab : a ≤ b := le_max_left _ _
  have hb2 : 2 * r0 ≤ b := le_max_right _ _
  have hbpos : 0 < b := lt_of_lt_of_le hapos hab
  have hmapsI : MapsTo (fun ρ : ℝ => (!₂[ρ, 0, y 2] : Space)) (Ici a) (youngOpen ν R) := by
    intro ρ hρ
    have hρ' : a ≤ ρ := hρ
    rw [hmem]
    show r0 < ϱ (!₂[ρ, 0, y 2] : Space)
    rw [wardFar_varrho ρ (y 2) (by linarith)]
    linarith
  have hpc : Continuous (fun ρ : ℝ => (!₂[ρ, 0, y 2] : Space)) := by fun_prop
  have hDcI : ContinuousOn (fun ρ : ℝ => fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space))
      (Ici a) :=
    (hSm.continuousOn_fderiv_of_isOpen hOpen (by norm_num)).comp hpc.continuousOn hmapsI
  have hAppI : ContinuousOn (fun ρ : ℝ =>
      fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space) (!₂[ρ, 0, y 2] : Space)) (Ici a) :=
    hDcI.clm_apply hpc.continuousOn
  have hFcI : ContinuousOn (fun ρ : ℝ => ρ *
      (fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space) (!₂[ρ, 0, y 2] : Space)) 2) (Ici a) :=
    continuousOn_id.mul ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn hAppI)
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℝ, Kd = |D1| + |D2| := ⟨_, rfl⟩
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  -- far bound
  have hfar : ∀ ρ : ℝ, b < ρ →
      ‖ρ * (fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space) (!₂[ρ, 0, y 2] : Space)) 2‖ ≤
        Kd * (ρ ^ (-(2 : ℝ)) + |y 2| * ρ ^ (-(3 : ℝ))) := by
    intro ρ hρ
    have hρpos : 0 < ρ := lt_trans hbpos hρ
    have hyρ : ϱ (!₂[ρ, 0, y 2] : Space) = ρ := wardFar_varrho ρ (y 2) hρpos.le
    have hy0U : (!₂[ρ, 0, y 2] : Space) ∈ youngOpen ν R := by
      rw [hmem, hyρ]; linarith
    have h2' : 2 * r0 ≤ ϱ (!₂[ρ, 0, y 2] : Space) := by rw [hyρ]; linarith
    have hn1 := hD1 2 _ h2'
    have hn2 := hD2 2 _ h2'
    rw [hyρ] at hn1 hn2
    have hcomp : ‖(fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space)
        (!₂[ρ, 0, y 2] : Space)) 2‖ ≤
        (‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ 2) (!₂[ρ, 0, y 2] : Space)‖
          + ‖fderiv ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T x τ 2)
              (!₂[ρ, 0, y 2] : Space)‖) * ‖(!₂[ρ, 0, y 2] : Space)‖ := by
      rw [Dcomp _ _ 2 hy0U]
      exact wardFar_re_fderiv_le _ _ _ _ (hGd 2 _ hy0U) (hHd 2 _ hy0U)
    have hp := tcx_norm_p ρ (y 2) hρpos.le
    obtain ⟨e4, e3, e2⟩ := tcx_rpow ρ hρpos
    have hsum : ‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ 2) (!₂[ρ, 0, y 2] : Space)‖
        + ‖fderiv ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T x τ 2) (!₂[ρ, 0, y 2] : Space)‖ ≤
        Kd * ρ ^ (-4 : ℝ) := by
      have hp4 : 0 ≤ ρ ^ (-4 : ℝ) := Real.rpow_nonneg hρpos.le _
      calc _ ≤ D1 * ρ ^ (-4 : ℝ) + D2 * ρ ^ (-4 : ℝ) := add_le_add hn1 hn2
        _ ≤ (|D1| + |D2|) * ρ ^ (-4 : ℝ) := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (add_le_add (le_abs_self _) (le_abs_self _)) hp4
        _ = Kd * ρ ^ (-4 : ℝ) := by rw [hKd]
    have hp4 : 0 ≤ ρ ^ (-4 : ℝ) := Real.rpow_nonneg hρpos.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρpos, ← Real.norm_eq_abs]
    calc ρ * ‖(fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space)
          (!₂[ρ, 0, y 2] : Space)) 2‖
        ≤ ρ * ((Kd * ρ ^ (-4 : ℝ)) * (ρ + |y 2|)) := by
          refine mul_le_mul_of_nonneg_left (hcomp.trans ?_) hρpos.le
          exact mul_le_mul hsum hp (norm_nonneg _) (mul_nonneg hKd0 hp4)
      _ = Kd * (ρ ^ (-(2 : ℝ)) + |y 2| * ρ ^ (-(3 : ℝ))) := by
          rw [e4, e3, e2]
          field_simp
  -- assemble
  have hGint : IntegrableOn (fun ρ : ℝ => Kd * (ρ ^ (-(2 : ℝ)) + |y 2| * ρ ^ (-(3 : ℝ))))
      (Ioi b) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hbpos).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) hbpos).const_mul (|y 2|))).const_mul Kd
  have hIcc : IntegrableOn (fun ρ : ℝ => ρ *
      (fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space) (!₂[ρ, 0, y 2] : Space)) 2) (Icc a b) :=
    (hFcI.mono Icc_subset_Ici_self).integrableOn_Icc
  have hIoi : IntegrableOn (fun ρ : ℝ => ρ *
      (fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space) (!₂[ρ, 0, y 2] : Space)) 2) (Ioi b) := by
    refine Integrable.mono' hGint
      ((hFcI.mono (fun x hx => le_of_lt (lt_of_le_of_lt hab hx))).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact hfar ρ hρ
  have hU : IntegrableOn (fun ρ : ℝ => ρ *
      (fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, y 2] : Space) (!₂[ρ, 0, y 2] : Space)) 2)
      (Icc a b ∪ Ioi b) := hIcc.union hIoi
  refine hU.mono_set ?_
  intro x hx
  have hx' : a < x := hx
  by_cases hxb : x ≤ b
  · exact Or.inl ⟨hx'.le, hxb⟩
  · exact Or.inr (lt_of_not_ge hxb)

end UnforcedLeray.Short.PartIIIb.Concrete

end
