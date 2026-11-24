import UnforcedLeray.Lib.CZL2.Decay
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far

/-!
# `wardX0DecayInf_proved` (PartIII-b:IIIb-D2/3/2/11/2/3)

Source of record: `the November 2 reference manuscript` 4177-4179.
Far field: `sepFarDecay` gives `|sepW| + |∇sepW| ≤ C ϱ^{-3}` for `2rOut ≤ ϱ`, hence
`|X₀| + |∇X₀| ≤ C' ϱ^{-3}` there; near `ϱ ∈ [r, 2rOut]` the field is bounded on a compact set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The separated field `sepW` is differentiable off the source disk. -/
lemma sepW_diffAt {ν : ℝ} {μ : ℂ} {rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ.re) (hr0 : 0 ≤ rOut) (hP : 0 < P)
    (hS1 : IIIa.IsSepSource P rOut T) (hS2 : SepMoment P T) (τ : ℝ) (i : Fin 3) (y : Space)
    (hy : rOut < ϱ y) :
    DifferentiableAt ℝ (fun y' => IIIa.sepW ν μ T y' τ i) y := by
  have hopen : IsOpen {y : Space | rOut < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hsm := sepWSmoothOn_of IIIa.sepKernelBounds ν μ rOut P T hν hμ hr0 hP hS1 hS2 τ i
  exact ((hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hy))

/-- The `(μ, μ+1)` combination `X₀` is differentiable off the source disk. -/
lemma wardX0_diffAt {ν μ R c : ℝ} {g : Chart → Ten3} {τ : ℝ} {y : Space}
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsSmoothOld c ν g)
    (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    DifferentiableAt ℝ (fun y' => wardX0 ν μ R c g τ y') y := by
  have hS := smoothOldSource_proved ν R c g hν hR hc hg
  obtain ⟨hS1, hS2⟩ := hS
  have hP : 0 < 2 * c / R := by positivity
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  rw [differentiableAt_piLp]
  intro i
  exact Complex.reCLM.differentiableAt.comp y
    ((sepW_diffAt hν hμ0 hr hP hS1 hS2 τ i y hy).sub
      (sepW_diffAt hν hμ1 hr hP hS1 hS2 τ i y hy))

/-- Far-field bound: for `2rOut ≤ ϱ y`, the components and the `e₂`-derivative of `X₀` are
bounded by `C ϱ^{-3}`. -/
lemma wardX0_far {ν μ R c : ℝ} {g : Chart → Ten3} {τ : ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsSmoothOld c ν g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, 2 * (R * Real.sqrt (5 * ν / 6)) ≤ ϱ y →
      (∀ i : Fin 3, |wardX0 ν μ R c g τ y i| ≤ C * ϱ y ^ (-3 : ℝ)) ∧
      |fderiv ℝ (fun y' => wardX0 ν μ R c g τ y') y (coordinateVector 2) 2| ≤
        C * ϱ y ^ (-3 : ℝ) := by
  have hS := smoothOldSource_proved ν R c g hν hR hc hg
  obtain ⟨hS1, hS2⟩ := hS
  have hP : 0 < 2 * c / R := by positivity
  have hr0 : 0 < R * Real.sqrt (5 * ν / 6) := by
    have : 0 < Real.sqrt (5 * ν / 6) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  obtain ⟨C1, h1⟩ := sepFarDecay ν (μ : ℂ) (R * Real.sqrt (5 * ν / 6)) (2 * c / R)
    (oldPhys R c g) hν hμ0 hr0.le hP hS1 hS2 τ
  obtain ⟨C2, h2⟩ := sepFarDecay ν ((μ : ℂ) + 1) (R * Real.sqrt (5 * ν / 6)) (2 * c / R)
    (oldPhys R c g) hν hμ1 hr0.le hP hS1 hS2 τ
  refine ⟨|C1| + |C2|, by positivity, fun y hy => ?_⟩
  have hρ : 0 ≤ ϱ y ^ (-3 : ℝ) := Real.rpow_nonneg (by
    have : 0 < R * Real.sqrt (5 * ν / 6) := hr0
    linarith) _
  have hyr : R * Real.sqrt (5 * ν / 6) < ϱ y := by
    have : 0 < R * Real.sqrt (5 * ν / 6) := hr0
    linarith
  have hA : ∀ i, ‖IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ i‖ ≤ C1 * ϱ y ^ (-3 : ℝ) := fun i =>
    (h1 i y hy).1
  have hB : ∀ i, ‖IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ i‖ ≤ C2 * ϱ y ^ (-3 : ℝ) :=
    fun i => (h2 i y hy).1
  have hC1 : C1 ≤ |C1| := le_abs_self _
  have hC2 : C2 ≤ |C2| := le_abs_self _
  have hC1' : -C1 ≤ |C1| := neg_le_abs _
  have hC2' : -C2 ≤ |C2| := neg_le_abs _
  refine ⟨fun i => ?_, ?_⟩
  · -- components
    have hw : wardX0 ν μ R c g τ y i = (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ i -
        IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ i).re := rfl
    rw [hw]
    have e1 := Complex.abs_re_le_norm (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ i -
        IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ i)
    have e2 := norm_sub_le (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ i)
        (IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ i)
    have := hA i
    have := hB i
    have hcs : C1 * ϱ y ^ (-3 : ℝ) ≤ |C1| * ϱ y ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right hC1 hρ
    have hcs2 : C2 * ϱ y ^ (-3 : ℝ) ≤ |C2| * ϱ y ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right hC2 hρ
    nlinarith [abs_nonneg C1, abs_nonneg C2]
  · -- derivative in the e₂ direction, component 2
    have hdiffA := sepW_diffAt hν hμ0 hr0.le hP hS1 hS2 τ 2 y hyr
    have hdiffB := sepW_diffAt hν hμ1 hr0.le hP hS1 hS2 τ 2 y hyr
    have hfun : fderiv ℝ (fun y' => wardX0 ν μ R c g τ y') y (coordinateVector 2) 2 =
        fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) x τ 2 -
          IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) x τ 2).re) y (coordinateVector 2) := by
      rw [coord_fderiv _ y (wardX0_diffAt hν hR hc hμ hg hyr) _ 2]
      rfl
    rw [hfun, re_sub_fderiv _ _ y hdiffA hdiffB]
    have dA : ‖fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) y
        (coordinateVector 2)‖ ≤ C1 * ϱ y ^ (-3 : ℝ) := by
      have h := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) y) (coordinateVector 2)
      rw [UnforcedLeray.RieszLp.norm_coordinateVector, mul_one] at h
      exact h.trans (h1 2 y hy).2
    have dB : ‖fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2) y
        (coordinateVector 2)‖ ≤ C2 * ϱ y ^ (-3 : ℝ) := by
      have h := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2) y) (coordinateVector 2)
      rw [UnforcedLeray.RieszLp.norm_coordinateVector, mul_one] at h
      exact h.trans (h2 2 y hy).2
    have e1 := Complex.abs_re_le_norm
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) y (coordinateVector 2) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2) y
          (coordinateVector 2))
    have e2 := norm_sub_le
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) y (coordinateVector 2))
      (fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2) y
          (coordinateVector 2))
    have hcs : C1 * ϱ y ^ (-3 : ℝ) ≤ |C1| * ϱ y ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right hC1 hρ
    have hcs2 : C2 * ϱ y ^ (-3 : ℝ) ≤ |C2| * ϱ y ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right hC2 hρ
    have hfin : |(fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) y
          (coordinateVector 2) - fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2)
            y (coordinateVector 2)).re| ≤ (|C1| + |C2|) * ϱ y ^ (-3 : ℝ) := by
      rw [add_mul]
      have := le_trans e1 e2
      linarith [abs_nonneg C1, abs_nonneg C2]
    exact hfin

lemma varrho_pt (ρ z' : ℝ) (hρ : 0 ≤ ρ) : ϱ (!₂[ρ, 0, z']) = ρ := by
  unfold ϱ
  simp [Real.sqrt_sq hρ]

/-- Continuity of the `e₂`-derivative component on the old-free region. -/
lemma sepW_fderiv_contOn {ν : ℝ} {μ : ℂ} {rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ.re) (hr0 : 0 ≤ rOut) (hP : 0 < P)
    (hS1 : IIIa.IsSepSource P rOut T) (hS2 : SepMoment P T) (τ : ℝ) (i : Fin 3) :
    ContinuousOn (fun y => fderiv ℝ (fun y' => IIIa.sepW ν μ T y' τ i) y (coordinateVector 2))
      {y : Space | rOut < ϱ y} := by
  have hopen : IsOpen {y : Space | rOut < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hsm := sepWSmoothOn_of IIIa.sepKernelBounds ν μ rOut P T hν hμ hr0 hP hS1 hS2 τ i
  exact ((hsm.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const)

lemma sepW_contOn {ν : ℝ} {μ : ℂ} {rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ.re) (hr0 : 0 ≤ rOut) (hP : 0 < P)
    (hS1 : IIIa.IsSepSource P rOut T) (hS2 : SepMoment P T) (τ : ℝ) (i : Fin 3) :
    ContinuousOn (fun y => IIIa.sepW ν μ T y τ i) {y : Space | rOut < ϱ y} := by
  have hopen : IsOpen {y : Space | rOut < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hsm := sepWSmoothOn_of IIIa.sepKernelBounds ν μ rOut P T hν hμ hr0 hP hS1 hS2 τ i
  exact hsm.continuousOn

/-- The `e₂`-derivative component of `X₀` on the old-free region. -/
lemma wardX0_fderiv2 {ν μ R c : ℝ} {g : Chart → Ten3} {τ : ℝ} {y : Space}
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsSmoothOld c ν g)
    (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    fderiv ℝ (fun y' => wardX0 ν μ R c g τ y') y (coordinateVector 2) 2 =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) y (coordinateVector 2) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2) y
          (coordinateVector 2)).re := by
  have hS := smoothOldSource_proved ν R c g hν hR hc hg
  obtain ⟨hS1, hS2⟩ := hS
  have hP : 0 < 2 * c / R := by positivity
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  exact (coord_fderiv _ y (wardX0_diffAt hν hR hc hμ hg hy) _ 2).trans
    (re_sub_fderiv _ _ y (sepW_diffAt hν hμ0 hr0 hP hS1 hS2 τ 2 y hy)
      (sepW_diffAt hν hμ1 hr0 hP hS1 hS2 τ 2 y hy) _)

lemma rpow_neg_two_eq {ρ : ℝ} (hρ : 0 < ρ) : ρ ^ (-2 : ℝ) = (ρ ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hρ.le, Real.rpow_two]

lemma rpow_mul_neg_three {ρ : ℝ} (hρ : 0 < ρ) : ρ * ρ ^ (-3 : ℝ) = ρ ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = 1 + (-3 : ℝ) by norm_num, Real.rpow_add hρ, Real.rpow_one]

/-- **`wardX0DecayInf_proved`** (source 4177-4179). -/
theorem wardX0DecayInf_proved : WardX0DecayInf := by
  intro ν μ R c g hν hR hc hμ hg τ
  unfold StreamDecay
  intro r z hr
  have hr0 : 0 < R * Real.sqrt (5 * ν / 6) := by
    have : 0 < Real.sqrt (5 * ν / 6) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hrpos : 0 < r := lt_trans hr0 hr
  obtain ⟨C, hC0, hfar⟩ := wardX0_far (τ := τ) hν hR hc hμ hg
  have hS := smoothOldSource_proved ν R c g hν hR hc hg
  obtain ⟨hS1, hS2⟩ := hS
  have hP : 0 < 2 * c / R := by positivity
  have hμ0 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hr0' : 0 ≤ R * Real.sqrt (5 * ν / 6) := hr0.le
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      (Set.Icc r (2 * (R * Real.sqrt (5 * ν / 6))) ×ˢ Metric.closedBall z 1)
      {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} := by
    intro p hp
    have hp1 : r ≤ p.1 := hp.1.1
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[p.1, 0, p.2])
    rw [varrho_pt _ _ (by linarith)]
    linarith
  have hKc : IsCompact (Set.Icc r (2 * (R * Real.sqrt (5 * ν / 6))) ×ˢ Metric.closedBall z 1) :=
    isCompact_Icc.prod (isCompact_closedBall z 1)
  have hptc : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by fun_prop
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) (!₂[p.1, 0, p.2]) τ 2 -
        IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) (!₂[p.1, 0, p.2]) τ 2).re)
      (Set.Icc r (2 * (R * Real.sqrt (5 * ν / 6))) ×ˢ Metric.closedBall z 1) := by
    have hA := (sepW_contOn hν hμ0 hr0' hP hS1 hS2 τ 2).comp hptc.continuousOn hmaps
    have hB := (sepW_contOn hν hμ1 hr0' hP hS1 hS2 τ 2).comp hptc.continuousOn hmaps
    exact continuousOn_fst.mul (Complex.continuous_re.comp_continuousOn (hA.sub hB))
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) (!₂[p.1, 0, p.2])
          (coordinateVector 2) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y' τ 2) (!₂[p.1, 0, p.2])
          (coordinateVector 2)).re)
      (Set.Icc r (2 * (R * Real.sqrt (5 * ν / 6))) ×ˢ Metric.closedBall z 1) := by
    have hA := (sepW_fderiv_contOn hν hμ0 hr0' hP hS1 hS2 τ 2).comp hptc.continuousOn hmaps
    have hB := (sepW_fderiv_contOn hν hμ1 hr0' hP hS1 hS2 τ 2).comp hptc.continuousOn hmaps
    exact continuousOn_fst.mul (Complex.continuous_re.comp_continuousOn (hA.sub hB))
  obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn hcont1.norm
  obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn hcont2.norm
  set M : ℝ := |M1| + |M2| with hMdef
  have hM0 : 0 ≤ M := by positivity
  set a : ℝ := 2 * (R * Real.sqrt (5 * ν / 6)) with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set N : ℝ := M * a ^ 2 + C with hNdef
  have hN0 : 0 ≤ N := by positivity
  refine ⟨⟨fun ρ => N * ρ ^ (-2 : ℝ), ?_, ?_⟩, ?_⟩
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hrpos).const_mul N
  · intro ρ hρ z' hz'
    have hρr : r < ρ := hρ
    have hρpos : 0 < ρ := lt_trans hrpos hρr
    have hz'K : z' ∈ Metric.closedBall z 1 := Metric.ball_subset_closedBall hz'
    by_cases hlt : ρ < a
    · have hmem : (ρ, z') ∈ Set.Icc r (2 * (R * Real.sqrt (5 * ν / 6))) ×ˢ Metric.closedBall z 1 :=
        ⟨⟨hρr.le, hlt.le⟩, hz'K⟩
      have hnear : M ≤ N * ρ ^ (-2 : ℝ) := by
        rw [rpow_neg_two_eq hρpos, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        have h1 : M * ρ ^ 2 ≤ M * a ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρpos.le hlt.le 2) hM0
        nlinarith [mul_nonneg hM0 (sq_nonneg a)]
      constructor
      · refine le_trans ?_ hnear
        have h1 := hM1 (ρ, z') hmem
        rw [norm_norm] at h1
        exact le_trans h1 (by linarith [abs_nonneg M2, le_abs_self M1])
      · have hdm : (ρ * fderiv ℝ (fun y' => wardX0 ν μ R c g τ y') (!₂[ρ, 0, z']) (coordinateVector 2) 2)
            = ρ * (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y' τ 2) (!₂[ρ, 0, z'])
                (coordinateVector 2) - fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1)
                (oldPhys R c g) y' τ 2) (!₂[ρ, 0, z']) (coordinateVector 2)).re := by
          rw [wardX0_fderiv2 hν hR hc hμ hg (by rw [varrho_pt _ _ hρpos.le]; exact lt_trans hr hρr)]
        rw [hdm]
        refine le_trans ?_ hnear
        have h2 := hM2 (ρ, z') hmem
        rw [norm_norm] at h2
        exact le_trans h2 (by linarith [abs_nonneg M1, le_abs_self M2])
    · have hϱ : 2 * (R * Real.sqrt (5 * ν / 6)) ≤ ϱ (!₂[ρ, 0, z']) := by
        rw [varrho_pt _ _ hρpos.le]; exact not_lt.1 hlt
      obtain ⟨hc1, hd1⟩ := hfar _ hϱ
      rw [varrho_pt _ _ hρpos.le] at hc1 hd1
      have hc2 := hc1 2
      constructor
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρpos]
        calc ρ * |wardX0 ν μ R c g τ (!₂[ρ, 0, z']) 2|
            ≤ ρ * (C * ρ ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hc2 hρpos.le
          _ = C * ρ ^ (-2 : ℝ) := by rw [← rpow_mul_neg_three hρpos]; ring
          _ ≤ N * ρ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right
              (by linarith [mul_nonneg hM0 (sq_nonneg a)]) (Real.rpow_nonneg hρpos.le _)
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρpos]
        calc ρ * |fderiv ℝ (fun y' => wardX0 ν μ R c g τ y') (!₂[ρ, 0, z']) (coordinateVector 2) 2|
            ≤ ρ * (C * ρ ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hd1 hρpos.le
          _ = C * ρ ^ (-2 : ℝ) := by rw [← rpow_mul_neg_three hρpos]; ring
          _ ≤ N * ρ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right
              (by linarith [mul_nonneg hM0 (sq_nonneg a)]) (Real.rpow_nonneg hρpos.le _)
  · apply squeeze_zero_norm' (a := fun ρ : ℝ => C * ρ ^ (-2 : ℝ))
    · rw [Filter.eventually_atTop]
      refine ⟨a, fun ρ hρ => ?_⟩
      have hρpos : 0 < ρ := lt_of_lt_of_le ha0 hρ
      have hϱ : 2 * (R * Real.sqrt (5 * ν / 6)) ≤ ϱ (!₂[ρ, 0, z]) := by
        rw [varrho_pt _ _ hρpos.le]; exact hρ
      obtain ⟨hc1, _⟩ := hfar _ hϱ
      have hc0 := hc1 0
      rw [varrho_pt _ _ hρpos.le] at hc0
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρpos]
      calc ρ * |wardX0 ν μ R c g τ (!₂[ρ, 0, z]) 0|
          ≤ ρ * (C * ρ ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hc0 hρpos.le
        _ = C * ρ ^ (-2 : ℝ) := by rw [← rpow_mul_neg_three hρpos]; ring
    · simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul C

end UnforcedLeray.Short.PartIIIb.Concrete
