import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Wre

/-!
# `PartIII-b:C/rep/2/7`, decay of `Re W_μ` and the partials of its outward primitive

Source 4175-4186 (decay 4177-4179).  The argument of `wgx_sepX0_farBound` for the single response
`sepWre ν μ T`: far field by `sepFarDecay`, near field by compactness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma wgyw_re_fderiv_le (g : Space → ℂ) (y v : Space) (hg : DifferentiableAt ℝ g y) :
    ‖fderiv ℝ (fun x => (g x).re) y v‖ ≤ ‖fderiv ℝ g y‖ * ‖v‖ := by
  rw [wgyw_re_fderiv g y hg v, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans ((fderiv ℝ g y).le_opNorm v)

theorem wgyw_farBound {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ r z : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    ∃ a C : ℝ, 1 < a ∧ ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
      ‖ρ * sepWre ν μ T τ !₂[ρ, 0, z'] 2‖ ≤ C * ρ ^ (-a) ∧
      ‖ρ * fderiv ℝ (sepWre ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤ C * ρ ^ (-a) ∧
      ‖ρ * sepWre ν μ T τ !₂[ρ, 0, z'] 0‖ ≤ C * ρ ^ (-a) := by
  have hW := sepWSmoothOn_of IIIa.sepKernelBounds
  have hfar := sepFarDecay
  have hr0pos : 0 < R * Real.sqrt (5 * ν / 6) := by positivity
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0def
  have hμ' : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    exact hμ
  have hSm : ContDiffOn ℝ 2 (sepWre ν μ T τ) (youngOpen ν R) :=
    wgyw_contDiffOn hν hμ hr0pos.le hP hS hM τ
  have hOpen : IsOpen (youngOpen ν R) := by
    unfold youngOpen
    exact isOpen_lt continuous_const Axi.continuous_ϱ
  have hG : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T y τ i)
      (youngOpen ν R) :=
    fun i => hW ν (μ : ℂ) r0 P T hν hμ' hr0pos.le hP hS hM τ i
  have K1 : ∀ (y : Space) (i : Fin 3),
      sepWre ν μ T τ y i = (IIIa.sepW ν (μ : ℂ) T y τ i).re := by
    intro y i
    simp only [sepWre, PiLp.toLp_apply]
  have hFd : ∀ y : Space, y ∈ youngOpen ν R →
      DifferentiableAt ℝ (sepWre ν μ T τ) y := fun y hy =>
    (hSm.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hGd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν R →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ i) y := fun i y hy =>
    ((hG i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have Dcomp : ∀ (y v : Space) (i : Fin 3), y ∈ youngOpen ν R →
      fderiv ℝ (sepWre ν μ T τ) y v i =
        fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i).re) y v := by
    intro y v i hy
    have hfun : (fun x => sepWre ν μ T τ x i) =
        (fun x => (IIIa.sepW ν (μ : ℂ) T x τ i).re) :=
      funext fun x => K1 x i
    rw [← wardFar_proj_fderiv _ y v i (hFd y hy), hfun]
  have Vbound : ∀ (y : Space) (i : Fin 3),
      ‖sepWre ν μ T τ y i‖ ≤ ‖IIIa.sepW ν (μ : ℂ) T y τ i‖ := by
    intro y i
    rw [K1 y i, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  obtain ⟨C1, hC1⟩ := hfar ν (μ : ℂ) r0 P T hν hμ' hr0pos.le hP hS hM τ
  have hcv : ‖coordinateVector (2 : Fin 3)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  have hLval : ∀ (y : Space) (i : Fin 3), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |sepWre ν μ T τ y i| ≤ C1 * ϱ y ^ (-3:ℝ) := by
    intro y i _ h2
    calc |sepWre ν μ T τ y i|
        = ‖sepWre ν μ T τ y i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖IIIa.sepW ν (μ : ℂ) T y τ i‖ := Vbound y i
      _ ≤ C1 * ϱ y ^ (-3:ℝ) := (hC1 i y h2).1
  have hLder : ∀ (y : Space), y ∈ youngOpen ν R → 2 * r0 ≤ ϱ y →
      |fderiv ℝ (sepWre ν μ T τ) y (coordinateVector 2) 2|
        ≤ C1 * ϱ y ^ (-3:ℝ) := by
    intro y hyU h2
    calc |fderiv ℝ (sepWre ν μ T τ) y (coordinateVector 2) 2|
        = ‖fderiv ℝ (sepWre ν μ T τ) y (coordinateVector 2) 2‖ :=
          (Real.norm_eq_abs _).symm
      _ = ‖fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T x τ 2).re) y (coordinateVector 2)‖ := by
          rw [Dcomp y (coordinateVector 2) 2 hyU]
      _ ≤ ‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T x τ 2) y‖ * ‖coordinateVector 2‖ :=
          wgyw_re_fderiv_le _ y _ (hGd 2 y hyU)
      _ ≤ C1 * ϱ y ^ (-3:ℝ) * 1 := by
          rw [hcv]
          simp only [mul_one]
          exact (hC1 2 y h2).2
      _ = C1 * ϱ y ^ (-3:ℝ) := by ring
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
  have hFc : ContinuousOn (fun p : ℝ × ℝ => sepWre ν μ T τ (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    hSm.continuousOn.comp hφ.continuousOn hmaps
  have hDc : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (sepWre ν μ T τ) (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    (hSm.continuousOn_fderiv_of_isOpen hOpen (by norm_num)).comp hφ.continuousOn hmaps
  have hSc : IsCompact (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    isCompact_Icc.prod (ProperSpace.isCompact_closedBall z 1)
  obtain ⟨M1, hM1⟩ := hSc.exists_bound_of_continuousOn hFc
  obtain ⟨M2, hM2⟩ := hSc.exists_bound_of_continuousOn hDc.norm
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = |C1| + (2 * r0) ^ 3 * (|M1| + |M2|) :=
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
  · have h2' : 2 * r0 ≤ ϱ y0 := by
      rw [hyρ]
      exact h2
    have hKL : C1 ≤ Cc := by
      rw [hCc]
      linarith [le_abs_self C1]
    have hA := hLval y0 2 hy0U h2'
    have hB := hLder y0 hy0U h2'
    have hD := hLval y0 0 hy0U h2'
    rw [hyρ] at hA hB hD
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKL hA, wardFar_arith ρ _ _ _ hρpos hKL hB,
      wardFar_arith ρ _ _ _ hρpos hKL hD⟩
  · have hmem : (ρ, z') ∈ Icc r (2 * r0) ×ˢ Metric.closedBall z 1 :=
      ⟨⟨hρr.le, h2⟩, Metric.ball_subset_closedBall hz'⟩
    have hVn : ‖sepWre ν μ T τ y0‖ ≤ M1 := hM1 (ρ, z') hmem
    have hDn : ‖fderiv ℝ (sepWre ν μ T τ) y0‖ ≤ M2 := by
      simpa only [norm_norm] using hM2 (ρ, z') hmem
    have hMM : |M1| + |M2| ≥ 0 := by positivity
    have hVal : ∀ i : Fin 3, |sepWre ν μ T τ y0 i| ≤ |M1| + |M2| := by
      intro i
      rw [← Real.norm_eq_abs]
      refine (PiLp.norm_apply_le _ i).trans (hVn.trans ?_)
      linarith [le_abs_self M1, abs_nonneg M2]
    have hDer : |fderiv ℝ (sepWre ν μ T τ) y0 (coordinateVector 2) 2|
        ≤ |M1| + |M2| := by
      rw [← Real.norm_eq_abs]
      refine (PiLp.norm_apply_le _ 2).trans ?_
      refine ((fderiv ℝ (sepWre ν μ T τ) y0).le_opNorm _).trans ?_
      rw [hcv, mul_one]
      linarith [le_abs_self M2, abs_nonneg M1]
    have hKS : (2 * r0) ^ 3 * (|M1| + |M2|) ≤ Cc := by
      rw [hCc]
      linarith [abs_nonneg C1]
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 2)),
      wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM hDer),
      wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 0))⟩

theorem wgyw_streamDecay {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ : ℝ) :
    StreamDecay ν R (sepWre ν μ T) τ := by
  intro r z hr
  obtain ⟨a, C, ha, h⟩ := wgyw_farBound hν hR hμ hP hS hM τ r z hr
  refine ⟨⟨fun ρ => C * ρ ^ (-a), ?_, fun ρ hρ z' hz' =>
    ⟨(h ρ hρ z' hz').1, (h ρ hρ z' hz').2.1⟩⟩, ?_⟩
  · have hr0 : 0 < R * Real.sqrt (5 * ν / 6) := by positivity
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) (hr0.trans hr)).const_mul C
  · have hz : Tendsto (fun ρ : ℝ => C * ρ ^ (-a)) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < a)).const_mul C
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop r] with ρ hρ
    exact (h ρ hρ z (Metric.mem_ball_self one_pos)).2.2

/-- The two partial derivatives of the outward primitive of `Re W_μ`. -/
theorem wgyw_partials {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hAx : IsAxiSource T) (τ : ℝ) (r z : ℝ) (hr : R * Real.sqrt (5 * ν / 6) < r) :
    HasDerivAt (fun r' => outPrim (sepWre ν μ T) τ r' z) (r * sepWre ν μ T τ !₂[r, 0, z] 2) r ∧
      HasDerivAt (fun z' => outPrim (sepWre ν μ T) τ r z')
        (-(r * sepWre ν μ T τ !₂[r, 0, z] 0)) z := by
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hZc : ContDiffOn ℝ 2 (sepWre ν μ T τ) (youngOpen ν R) :=
    wgyw_contDiffOn hν hμ hr0 hP hS hM τ
  have hdec := wgyw_streamDecay hν hR hμ hP hS hM τ
  refine ⟨outPrimDerivR ν R (sepWre ν μ T) τ hZc hdec r z hr,
    outPrimDerivZ ν R (sepWre ν μ T) τ hZc ?_ ?_ hdec r z hr⟩
  · intro y hy
    exact wgyw_div hν hμ hr0 hP hS hM τ y hy
  · intro τ' y hy hya
    exact (wgyw_axi hν hμ hr0 hP hS hM hAx τ' y hy).1

end UnforcedLeray.Short.PartIIIb.Concrete

end
