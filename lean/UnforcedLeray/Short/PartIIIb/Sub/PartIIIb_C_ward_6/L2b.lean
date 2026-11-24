import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6.L2a
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_red
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `WardX0FactsOldL2` part (c) (`PartIII-b:C/ward/6/2`, L2b)

Source of record: `the November 2 reference manuscript` 4175-4186 (decay
4177-4179).  Port of `wardX0FarBound_of` (`PhysLayer/Sub/PartIIIb-D2_3_1/L1_red.lean` 84-251) and
`wardX0Decay_of` (`Sub/PartIII-b_IIIb-D2_3_1_3_1.lean` 38-52), with `oldL2SepReg_proved` in place
of `OldSourceReg`, `R` in place of `ε⁻¹`, and `wardX0Smooth` replaced by `WardL2a.smooth`.  The
arithmetic helpers `wardFar_*` are reused from `L1_red`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace WardL2b

/-- Far-field bound for `X₀` of an old `L²` datum (port of `wardX0FarBound_of`). -/
theorem farBound (ν μ R c : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4 : ℝ) < μ) (hg : IsOldL2 c ν g) (τ r z : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    ∃ a C : ℝ, 1 < a ∧ ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
      ‖ρ * wardX0 ν μ R c g τ !₂[ρ, 0, z'] 2‖ ≤ C * ρ ^ (-a) ∧
      ‖ρ * fderiv ℝ (wardX0 ν μ R c g τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖
        ≤ C * ρ ^ (-a) ∧
      ‖ρ * wardX0 ν μ R c g τ !₂[ρ, 0, z'] 0‖ ≤ C * ρ ^ (-a) := by
  obtain ⟨P, T', hP, hS, hM, hEq, -⟩ := oldL2SepReg_proved ν R c g hν hR hc hg
  have hr0pos : 0 < R * Real.sqrt (5 * ν / 6) := by positivity
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0def
  have hμ' : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    exact hμ
  have hμ1 : -(1 / 4 : ℝ) < (((μ : ℝ) : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hSm : ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R) :=
    WardL2a.smooth ν μ R c g hν hR hc hμ hg τ
  have hW : SepWSmoothOn := sepWSmoothOn_of IIIa.sepKernelBounds
  have hOpen : IsOpen (youngOpen ν R) := by
    unfold youngOpen
    exact isOpen_lt continuous_const Axi.continuous_ϱ
  have hG : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T' y τ i)
      (youngOpen ν R) :=
    fun i => hW ν (μ : ℂ) r0 P T' hν hμ' hr0pos.le hP hS hM τ i
  have hH : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i)
      (youngOpen ν R) :=
    fun i => hW ν ((μ : ℂ) + 1) r0 P T' hν hμ1 hr0pos.le hP hS hM τ i
  have K1 : ∀ (y : Space) (i : Fin 3),
      wardX0 ν μ R c g τ y i =
        (IIIa.sepW ν (μ : ℂ) T' y τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i).re := by
    intro y i
    simp only [wardX0, hEq, PiLp.toLp_apply]
  have hFd : ∀ y : Space, y ∈ youngOpen ν R →
      DifferentiableAt ℝ (wardX0 ν μ R c g τ) y := fun y hy =>
    (hSm.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
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
  obtain ⟨C1, hC1⟩ := sepFarDecay ν (μ : ℂ) r0 P T' hν hμ' hr0pos.le hP hS hM τ
  obtain ⟨C2, hC2⟩ := sepFarDecay ν ((μ : ℂ) + 1) r0 P T' hν hμ1 hr0pos.le hP hS hM τ
  have hcv : ‖coordinateVector (2 : Fin 3)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  have hLval : ∀ (y : Space) (i : Fin 3), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |wardX0 ν μ R c g τ y i| ≤ (C1 + C2) * ϱ y ^ (-3:ℝ) := by
    intro y i _ h2
    calc |wardX0 ν μ R c g τ y i|
        = ‖wardX0 ν μ R c g τ y i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖IIIa.sepW ν (μ : ℂ) T' y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i‖ := Vbound y i
      _ ≤ C1 * ϱ y ^ (-3:ℝ) + C2 * ϱ y ^ (-3:ℝ) :=
          add_le_add (hC1 i y h2).1 (hC2 i y h2).1
      _ = (C1 + C2) * ϱ y ^ (-3:ℝ) := by ring
  have hLder : ∀ (y : Space), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |fderiv ℝ (wardX0 ν μ R c g τ) y (coordinateVector 2) 2|
        ≤ (C1 + C2) * ϱ y ^ (-3:ℝ) := by
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
  -- the compact range and its continuity
  have hφ : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by
    fun_prop
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
  refine ⟨2, Cc, by norm_num, ?_⟩
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
  have hnn : 0 ≤ (2 * r0) ^ 3 * (|M1| + |M2|) := by positivity
  rcases le_total (2 * r0) ρ with h2 | h2
  · -- far regime `2 r_o ≤ ρ`
    have h2' : 2 * r0 ≤ ϱ y0 := by
      rw [hyρ]
      exact h2
    have hKL : C1 + C2 ≤ Cc := by
      rw [hCc]
      linarith [le_abs_self C1, le_abs_self C2]
    have hA := hLval y0 2 hy0U h2'
    have hB := hLder y0 hy0U h2'
    have hD := hLval y0 0 hy0U h2'
    rw [hyρ] at hA hB hD
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKL hA, wardFar_arith ρ _ _ _ hρpos hKL hB,
      wardFar_arith ρ _ _ _ hρpos hKL hD⟩
  · -- near regime `r < ρ ≤ 2 r_o`: compact bound
    have hmem : (ρ, z') ∈ Icc r (2 * r0) ×ˢ Metric.closedBall z 1 :=
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
    have hDer : |fderiv ℝ (wardX0 ν μ R c g τ) y0 (coordinateVector 2) 2|
        ≤ |M1| + |M2| := by
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

/-- Stream decay of `X₀` of an old `L²` datum (port of `wardX0Decay_of` and
`wardX0Decay_unconditional`). -/
theorem decay (ν μ R c : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4 : ℝ) < μ) (hg : IsOldL2 c ν g) (τ : ℝ) :
    StreamDecay ν R (wardX0 ν μ R c g) τ := by
  intro r z hr
  obtain ⟨a, C, ha, h⟩ := farBound ν μ R c g hν hR hc hμ hg τ r z hr
  refine ⟨⟨fun ρ => C * ρ ^ (-a), ?_, fun ρ hρ z' hz' =>
    ⟨(h ρ hρ z' hz').1, (h ρ hρ z' hz').2.1⟩⟩, ?_⟩
  · have hr0 : 0 < R * Real.sqrt (5 * ν / 6) := by positivity
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) (hr0.trans hr)).const_mul C
  · have hz : Tendsto (fun ρ : ℝ => C * ρ ^ (-a)) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < a)).const_mul C
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop r] with ρ hρ
    exact (h ρ hρ z (Metric.mem_ball_self one_pos)).2.2

end WardL2b

end UnforcedLeray.Short.PartIIIb.Concrete
