import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H11

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (12): decay and partials of the primitive of `X₀`

Source of record: `the November 2 reference manuscript` (73 pages), 4176-4186.
Adapted from `wardX0FarBound_of` (`L1_red`) and `tcr_divFree` to the cut old source.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section Ctx

variable {ν μ R c : ℝ} {g : Chart → Ten3}

theorem w2_streamDecay (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) : StreamDecay ν R (wardX0 ν μ R c g) τ := by
  obtain ⟨hS, hM, hZ⟩ := w2_ctx (μ := μ) hν hR hc hg
  intro r z hr
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  have hr0pos : 0 < r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set T' := oldCutSrc R c r0 g with hT'
  have hμ' : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4 : ℝ) < (((μ : ℝ) : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hSm : ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hOpen : IsOpen (youngOpen ν R) := by
    unfold youngOpen
    exact isOpen_lt continuous_const Axi.continuous_ϱ
  have hG : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T' y τ i) (youngOpen ν R) :=
    fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) r0 (2 * c / R) T' hν hμ' hr0pos.le hP
      hS hM τ i
  have hH : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i)
      (youngOpen ν R) :=
    fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) r0 (2 * c / R) T' hν hμ1
      hr0pos.le hP hS hM τ i
  have K1 : ∀ (y : Space) (i : Fin 3),
      wardX0 ν μ R c g τ y i =
        (IIIa.sepW ν (μ : ℂ) T' y τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i).re := by
    intro y i
    rw [hZ, sepX0]
  have hFd : ∀ y : Space, y ∈ youngOpen ν R → DifferentiableAt ℝ (wardX0 ν μ R c g τ) y :=
    fun y hy => (hSm.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hGd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν R →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν (μ : ℂ) T' x τ i) y := fun i y hy =>
    ((hG i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hHd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν R →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y := fun i y hy =>
    ((hH i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have Dcomp : ∀ (y v : Space) (i : Fin 3), y ∈ youngOpen ν R →
      fderiv ℝ (wardX0 ν μ R c g τ) y v i =
        fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T' x τ i
          - IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i).re) y v := by
    intro y v i hy
    have hfun : (fun x => wardX0 ν μ R c g τ x i) =
        (fun x => (IIIa.sepW ν (μ : ℂ) T' x τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i).re) :=
      funext fun x => K1 x i
    rw [← wardFar_proj_fderiv _ y v i (hFd y hy), hfun]
  have Vbound : ∀ (y : Space) (i : Fin 3),
      ‖wardX0 ν μ R c g τ y i‖ ≤
        ‖IIIa.sepW ν (μ : ℂ) T' y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i‖ := by
    intro y i
    rw [K1 y i]
    exact wardFar_re_sub_le _ _
  obtain ⟨C1, hC1⟩ := sepFarDecay ν (μ : ℂ) r0 _ T' hν hμ' hr0pos.le hP hS hM τ
  obtain ⟨C2, hC2⟩ := sepFarDecay ν ((μ : ℂ) + 1) r0 _ T' hν hμ1 hr0pos.le hP hS hM τ
  have hcv : ‖coordinateVector (2 : Fin 3)‖ = 1 := wyl_norm_coordinateVector 2
  have hLval : ∀ (y : Space) (i : Fin 3), 2 * r0 ≤ ϱ y →
      |wardX0 ν μ R c g τ y i| ≤ (C1 + C2) * ϱ y ^ (-3:ℝ) := by
    intro y i h2
    calc |wardX0 ν μ R c g τ y i|
        = ‖wardX0 ν μ R c g τ y i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖IIIa.sepW ν (μ : ℂ) T' y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i‖ := Vbound y i
      _ ≤ C1 * ϱ y ^ (-3:ℝ) + C2 * ϱ y ^ (-3:ℝ) :=
          add_le_add (hC1 i y h2).1 (hC2 i y h2).1
      _ = (C1 + C2) * ϱ y ^ (-3:ℝ) := by ring
  have hLder : ∀ (y : Space), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |fderiv ℝ (wardX0 ν μ R c g τ) y (coordinateVector 2) 2| ≤ (C1 + C2) * ϱ y ^ (-3:ℝ) := by
    intro y hyU h2
    calc |fderiv ℝ (wardX0 ν μ R c g τ) y (coordinateVector 2) 2|
        = ‖fderiv ℝ (wardX0 ν μ R c g τ) y (coordinateVector 2) 2‖ :=
          (Real.norm_eq_abs _).symm
      _ = ‖fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T' x τ 2
            - IIIa.sepW ν ((μ : ℂ) + 1) T' x τ 2).re) y (coordinateVector 2)‖ := by
          rw [Dcomp y (coordinateVector 2) 2 hyU]
      _ ≤ (‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T' x τ 2) y‖
            + ‖fderiv ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T' x τ 2) y‖)
            * ‖coordinateVector 2‖ :=
          wardFar_re_fderiv_le _ _ y _ (hGd 2 y hyU) (hHd 2 y hyU)
      _ ≤ (C1 * ϱ y ^ (-3:ℝ) + C2 * ϱ y ^ (-3:ℝ)) * 1 := by
          rw [hcv]
          simp only [mul_one]
          exact add_le_add (hC1 2 y h2).2 (hC2 2 y h2).2
      _ = (C1 + C2) * ϱ y ^ (-3:ℝ) := by ring
  have hφ : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) (youngOpen ν R) := by
    rintro ⟨a, b⟩ hp
    have ha : r ≤ a := hp.1.1
    have hpos : 0 ≤ a := by linarith
    show r0 < ϱ (!₂[a, 0, b] : Space)
    rw [wardFar_varrho a b hpos]
    linarith
  have hFc : ContinuousOn (fun p : ℝ × ℝ => wardX0 ν μ R c g τ (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    hSm.continuousOn.comp hφ.continuousOn hmaps
  have hDc : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (wardX0 ν μ R c g τ) (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    (hSm.continuousOn_fderiv_of_isOpen hOpen (by norm_num)).comp hφ.continuousOn hmaps
  have hSc : IsCompact (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    isCompact_Icc.prod (ProperSpace.isCompact_closedBall z 1)
  obtain ⟨M1, hM1⟩ := hSc.exists_bound_of_continuousOn hFc
  obtain ⟨M2, hM2⟩ := hSc.exists_bound_of_continuousOn hDc.norm
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = (|C1| + |C2|) + (2 * r0) ^ 3 * (|M1| + |M2|) :=
    ⟨_, rfl⟩
  have hbd : ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
      ‖ρ * wardX0 ν μ R c g τ !₂[ρ, 0, z'] 2‖ ≤ Cc * ρ ^ (-(2:ℝ)) ∧
        ‖ρ * fderiv ℝ (wardX0 ν μ R c g τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤
          Cc * ρ ^ (-(2:ℝ)) ∧
        ‖ρ * wardX0 ν μ R c g τ !₂[ρ, 0, z'] 0‖ ≤ Cc * ρ ^ (-(2:ℝ)) := by
    intro ρ hρ z' hz'
    have hρr : r < ρ := hρ
    have hρpos : 0 < ρ := lt_trans (lt_trans hr0pos hr) hρr
    set y0 : Space := (!₂[ρ, 0, z'] : Space) with hy0
    have hyρ : ϱ y0 = ρ := by
      rw [hy0]
      exact wardFar_varrho ρ z' hρpos.le
    have hy0U : y0 ∈ youngOpen ν R := by
      show r0 < ϱ y0
      rw [hyρ]
      linarith
    rcases le_total (2 * r0) ρ with h2 | h2
    · have h2' : 2 * r0 ≤ ϱ y0 := by rw [hyρ]; exact h2
      have hKL : C1 + C2 ≤ Cc := by
        rw [hCc]
        have : 0 ≤ (2 * r0) ^ 3 * (|M1| + |M2|) := by positivity
        linarith [le_abs_self C1, le_abs_self C2]
      have hA := hLval y0 2 h2'
      have hB := hLder y0 hy0U h2'
      have hD := hLval y0 0 h2'
      rw [hyρ] at hA hB hD
      exact ⟨wardFar_arith ρ _ _ _ hρpos hKL hA, wardFar_arith ρ _ _ _ hρpos hKL hB,
        wardFar_arith ρ _ _ _ hρpos hKL hD⟩
    · have hmem : (ρ, z') ∈ Icc r (2 * r0) ×ˢ Metric.closedBall z 1 :=
        ⟨⟨hρr.le, h2⟩, Metric.ball_subset_closedBall hz'⟩
      have hVn : ‖wardX0 ν μ R c g τ y0‖ ≤ M1 := hM1 (ρ, z') hmem
      have hDn : ‖fderiv ℝ (wardX0 ν μ R c g τ) y0‖ ≤ M2 := by
        simpa only [norm_norm] using hM2 (ρ, z') hmem
      have hMM : |M1| + |M2| ≥ 0 := by positivity
      have hVal : ∀ i : Fin 3, |wardX0 ν μ R c g τ y0 i| ≤ |M1| + |M2| := by
        intro i
        rw [← Real.norm_eq_abs]
        refine (PiLp.norm_apply_le _ i).trans (hVn.trans ?_)
        linarith [le_abs_self M1, abs_nonneg M2]
      have hDer : |fderiv ℝ (wardX0 ν μ R c g τ) y0 (coordinateVector 2) 2| ≤ |M1| + |M2| := by
        rw [← Real.norm_eq_abs]
        refine (PiLp.norm_apply_le _ 2).trans ?_
        refine ((fderiv ℝ (wardX0 ν μ R c g τ) y0).le_opNorm _).trans ?_
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
  refine ⟨⟨fun ρ => Cc * ρ ^ (-(2:ℝ)), ?_, fun ρ hρ z' hz' =>
    ⟨(hbd ρ hρ z' hz').1, (hbd ρ hρ z' hz').2.1⟩⟩, ?_⟩
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (hr0pos.trans hr)).const_mul Cc
  · have hz : Tendsto (fun ρ : ℝ => Cc * ρ ^ (-(2:ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul Cc
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop r] with ρ hρ
    exact (hbd ρ hρ z (Metric.mem_ball_self one_pos)).2.2

end Ctx

end UnforcedLeray.Short.PartIIIb.Concrete
end
