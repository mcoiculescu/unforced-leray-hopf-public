import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.CellL2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Shift

/-!
# Helpers for `PartII-a:N05/2/2/1`: the cut-off flat heat equation on `ℝ × ℝ²`

Source: `the November 2 reference manuscript`, lines 1794-1799: "the flat body
graph follows directly by cutting off its heat equation".

For `w = R₀(μ)g` and the age cutoff `θ = timeCut σ H1` (`θ = 1` on `[σ, H1]`, supported in
`(σ/2, 2H1)`), each component of the periodic extension `u_i = θ(s) w̃_i` solves
`(∂_s - νΔ_{q,η}) u_i = f_i`, `f_i = (θ/s)(g̃_i - μ w̃_i) + θ'(s) w̃_i`, in distributions on
`ℝ × ℝ²` (`isCylHeat_uCut`). The proof periodizes the test (`perT`), uses the weak flat
equation `weak_cell` against the periodic test `θ · perT φ` placed in the component `i`, and
unfolds back. Both `u_i` and `f_i` are `q`-periodic and square integrable on one cell
(`cylHeat_hyps`), which are the hypotheses of the cylinder heat estimate `IIb.CylHeatMaxReg`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell periodize QPeriodic
  periodize_of_mem)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)
open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

/-! ### The cut-off field and its source -/

/-- `u_i = θ(s) w̃_i`, `w̃` the `c`-periodic extension of `w`. -/
def uCut (c σ H1 : ℝ) (W : Profile → MeridC) (i : Fin 2) : Coord → ℂ := fun x =>
  (timeCut σ H1 x.1 : ℂ) * periodize c W x i

/-- `f_i = (θ/s)(g̃_i - μ w̃_i) + θ'(s) w̃_i`. -/
def fCut (c σ H1 : ℝ) (μ : ℂ) (W G : Profile → MeridC) (i : Fin 2) : Coord → ℂ := fun x =>
  ((timeCut σ H1 x.1 * x.1⁻¹ : ℝ) : ℂ) * (periodize c G x i - μ * periodize c W x i) +
    ((deriv (timeCut σ H1) x.1 : ℝ) : ℂ) * periodize c W x i

theorem periodize_add_qv {c : ℝ} (hc : 0 < c) (W : Profile → MeridC) (x : Coord) :
    periodize c W (x + qv c) = periodize c W x := by
  rw [add_qv_eq]
  exact UnforcedLeray.B0220.qPeriodic_periodize hc W x

theorem uCut_periodic {c σ H1 : ℝ} (hc : 0 < c) (W : Profile → MeridC) (i : Fin 2) (x : Coord) :
    uCut c σ H1 W i (x + qv c) = uCut c σ H1 W i x := by
  simp only [uCut, add_qv_fst, periodize_add_qv hc]

theorem fCut_periodic {c σ H1 : ℝ} (hc : 0 < c) (μ : ℂ) (W G : Profile → MeridC) (i : Fin 2)
    (x : Coord) : fCut c σ H1 μ W G i (x + qv c) = fCut c σ H1 μ W G i x := by
  simp only [fCut, add_qv_fst, periodize_add_qv hc]

theorem timeCut_eq_zero_of_not_mem {σ H1 s : ℝ} (hσ : 0 < σ) (hH : 0 < H1)
    (hs : s ∉ Icc (σ / 2) (2 * H1)) : timeCut σ H1 s = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := timeCut_support hσ hH h
  exact hs ⟨h1.le, h2.le⟩

theorem deriv_timeCut_eq_zero_of_not_mem {σ H1 s : ℝ} (hσ : 0 < σ) (hH : 0 < H1)
    (hs : s ∉ Icc (σ / 2) (2 * H1)) : deriv (timeCut σ H1) s = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · exact deriv_timeCut_zero_of_lt hσ hs
  · exact deriv_timeCut_zero_of_gt hH hs

theorem uCut_zero {c σ H1 : ℝ} (hσ : 0 < σ) (hH : 0 < H1) (W : Profile → MeridC) (i : Fin 2)
    {x : Coord} (hx : x.1 ∉ Icc (σ / 2) (2 * H1)) : uCut c σ H1 W i x = 0 := by
  simp [uCut, timeCut_eq_zero_of_not_mem hσ hH hx]

theorem fCut_zero {c σ H1 : ℝ} (hσ : 0 < σ) (hH : 0 < H1) (μ : ℂ) (W G : Profile → MeridC)
    (i : Fin 2) {x : Coord} (hx : x.1 ∉ Icc (σ / 2) (2 * H1)) : fCut c σ H1 μ W G i x = 0 := by
  simp [fCut, timeCut_eq_zero_of_not_mem hσ hH hx, deriv_timeCut_eq_zero_of_not_mem hσ hH hx]

/-! ### Bounds on the age cutoffs -/

theorem abs_timeCut_div_le {σ H1 : ℝ} (hσ : 0 < σ) (hH : 0 < H1) (s : ℝ) :
    |timeCut σ H1 s * s⁻¹| ≤ 2 / σ := by
  by_cases h : timeCut σ H1 s = 0
  · rw [h, zero_mul, abs_zero]; positivity
  · obtain ⟨h1, -⟩ := timeCut_support hσ hH h
    have hs : 0 < s := lt_trans (by linarith) h1
    rw [abs_mul, abs_inv, abs_of_pos hs]
    calc |timeCut σ H1 s| * s⁻¹ ≤ 1 * s⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_timeCut_le_one σ H1 s) (inv_nonneg.2 hs.le)
      _ = s⁻¹ := one_mul _
      _ ≤ 2 / σ := by
          rw [inv_eq_one_div, div_le_div_iff₀ hs hσ]
          linarith

theorem timeCut_div_zero {σ H1 : ℝ} (hH : 0 < H1) {s : ℝ} (hs : 2 * H1 < s) :
    timeCut σ H1 s * s⁻¹ = 0 := by
  rw [timeCut_zero_of_ge hH hs.le, zero_mul]

theorem measurable_timeCut (σ H1 : ℝ) : Measurable (timeCut σ H1) :=
  (timeCut_contDiff σ H1).continuous.measurable

theorem continuous_deriv_timeCut (σ H1 : ℝ) : Continuous (deriv (timeCut σ H1)) :=
  (timeCut_contDiff σ H1).continuous_deriv (by simp)

/-! ### Square integrability on the cell -/

theorem memLp_component {μ : Measure Profile} {f : Profile → MeridC} (hf : MemLp f 2 μ)
    (i : Fin 2) : MemLp (fun p => f p i) 2 μ :=
  (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).comp_memLp' hf

theorem smul_apply_real (r : ℝ) (v : MeridC) (i : Fin 2) : (r • v) i = (r : ℂ) * v i := by
  rw [PiLp.smul_apply, Complex.real_smul]

theorem memLp_uCut {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hH : 0 < H1)
    (V : HSpace c MeridC) (i : Fin 2) :
    MemLp (uCut c σ H1 (V : Profile → MeridC) i) 2 (cellMeasure c) := by
  have h := memLp_component (memLp_ksmul (c := c) (b := 2 * H1) V (measurable_timeCut σ H1)
    (abs_timeCut_le_one σ H1) (fun s hs => timeCut_zero_of_ge hH hs.le)) i
  refine h.ae_eq ?_
  filter_upwards [ae_mem_cell c] with x hx
  simp only [uCut, periodize_of_mem hc _ hx, smul_apply_real]

theorem memLp_fCut {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hH : 0 < H1) (μ : ℂ)
    (V G : HSpace c MeridC) (i : Fin 2) :
    MemLp (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i) 2 (cellMeasure c) := by
  obtain ⟨M0, -, hM0⟩ := st_deriv_bound
  have hk1m : Measurable fun s : ℝ => timeCut σ H1 s * s⁻¹ :=
    (measurable_timeCut σ H1).mul measurable_inv
  have hG := memLp_component (memLp_ksmul (c := c) (b := 2 * H1) G hk1m
    (abs_timeCut_div_le hσ hH) (fun s hs => timeCut_div_zero hH hs)) i
  have hW1 := memLp_component (memLp_ksmul (c := c) (b := 2 * H1) V hk1m
    (abs_timeCut_div_le hσ hH) (fun s hs => timeCut_div_zero hH hs)) i
  have hW2 := memLp_component (memLp_ksmul (c := c) (b := 2 * H1) V
    (continuous_deriv_timeCut σ H1).measurable
    (abs_deriv_timeCut_le hM0 hσ hσH)
    (fun s hs => deriv_timeCut_zero_of_gt hH hs)) i
  have h := (hG.sub (hW1.const_mul μ)).add hW2
  refine h.ae_eq ?_
  filter_upwards [ae_mem_cell c] with x hx
  simp only [fCut, periodize_of_mem hc _ hx, smul_apply_real, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

/-! ### Local integrability on `ℝ × ℝ²` -/

theorem locInt_of_band {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) {F : Coord → ℂ}
    (hper : ∀ x, F (x + qv c) = F x) (hzero : ∀ x : Coord, x.1 ∉ Icc a b → F x = 0)
    (hmem : MemLp F 2 (cellMeasure c)) : LocallyIntegrable F volume := by
  refine locallyIntegrable_of_periodic hc hper fun R => ?_
  set K : Set Coord := Icc a b ×ˢ (Ioc 0 c ×ˢ Icc (-R) R) with hKdef
  have hKm : MeasurableSet K :=
    measurableSet_Icc.prod (measurableSet_Ioc.prod measurableSet_Icc)
  have hKsub : K ⊆ cell c := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1.1, hx.2.1, trivial⟩
  have hKfin : volume K < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (fun x hx => ⟨hx.1, Ioc_subset_Icc_self hx.2.1, hx.2.2⟩ :
      K ⊆ Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R))) ?_
    exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKfin.ne
  have hmK : MemLp F 2 (volume.restrict K) :=
    hmem.mono_measure (Measure.restrict_mono hKsub le_rfl)
  have hiK : IntegrableOn F K := hmK.integrable (by norm_num)
  refine hiK.of_forall_diff_eq_zero
    (MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Icc)) fun x hx => ?_
  refine hzero x fun h => hx.2 ⟨h, hx.1.2⟩

/-! ### The cut-off heat equation -/

theorem perT_eta_band {c : ℝ} {φ : Coord → ℝ} (hφ : HasCompactSupport φ) :
    ∃ T : ℝ, ∀ x : Coord, perT c φ x ≠ 0 → |x.2.2| ≤ T := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1 hφ.isCompact.isBounded
  refine ⟨R, fun x hx => ?_⟩
  by_contra hxR
  push_neg at hxR
  apply hx
  have h0 : ∀ n : ℤ, φ (x + qv (n * c)) = 0 := by
    intro n
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h
    have h2 : |(x + qv (n * c)).2.2| ≤ ‖x + qv (n * c)‖ := by
      calc |(x + qv (n * c)).2.2| = ‖(x + qv (n * c)).2.2‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖(x + qv (n * c)).2‖ := norm_snd_le _
        _ ≤ ‖x + qv (n * c)‖ := norm_snd_le _
    rw [add_qv_snd_snd] at h2
    linarith
  simp only [perT, h0, tsum_zero]

theorem fderiv_fstMul {h : ℝ → ℝ} {F : Profile → ℝ} {p : Profile} (hh : DifferentiableAt ℝ h p.1)
    (hF : DifferentiableAt ℝ F p) (v : Profile) :
    fderiv ℝ (fun q : Profile => h q.1 * F q) p v =
      deriv h p.1 * v.1 * F p + h p.1 * fderiv ℝ F p v := by
  have hh' : HasFDerivAt (fun q : Profile => h q.1)
      (deriv h p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hh.hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_fst (p := p))
  have hm : HasFDerivAt (fun q : Profile => h q.1 * F q)
      (h p.1 • fderiv ℝ F p + F p • (deriv h p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) p :=
    hh'.mul hF.hasFDerivAt
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', smul_eq_mul]
  ring

theorem cylHeatT_eq (ν : ℝ) (φ : Coord → ℝ) (x : Coord) :
    cylHeatTL ν φ x = -pdS φ x - ν * (pdQ (pdQ φ) x + pdEta (pdEta φ) x) := rfl

/-- The periodized heat transpose. -/
theorem perT_cylHeatT {c : ℝ} (hc : 0 < c) (ν : ℝ) {φ : Coord → ℝ} (hφ : IsSTTestCoordL φ) :
    perT c (cylHeatTL ν φ) = cylHeatTL ν (perT c φ) := by
  have hs := hφ.smooth
  have hk := hφ.compact
  have e0 : (fun x => cpd 0 (perT c φ) x) = perT c (fun x => cpd 0 φ x) := cpd_perT hc hs hk 0
  have e11 : (fun x => cpd 1 (fun y => cpd 1 (perT c φ) y) x) =
      perT c (fun x => cpd 1 (fun y => cpd 1 φ y) x) := by
    rw [cpd_perT hc hs hk 1]
    exact cpd_perT hc (cpd_contDiff hs 1) (cpd_hasCompactSupport hk 1) 1
  have e22 : (fun x => cpd 2 (fun y => cpd 2 (perT c φ) y) x) =
      perT c (fun x => cpd 2 (fun y => cpd 2 φ y) x) := by
    rw [cpd_perT hc hs hk 2]
    exact cpd_perT hc (cpd_contDiff hs 2) (cpd_hasCompactSupport hk 2) 2
  have hlin := perT_lincomb hc (A := fun x => cpd 0 φ x)
    (B := fun x => cpd 1 (fun y => cpd 1 φ y) x) (D := fun x => cpd 2 (fun y => cpd 2 φ y) x)
    (cpd_hasCompactSupport hk 0) (cpd_hasCompactSupport (cpd_hasCompactSupport hk 1) 1)
    (cpd_hasCompactSupport (cpd_hasCompactSupport hk 2) 2) ν
  funext x
  have h1 := congrFun hlin x
  have h0x := congrFun e0 x
  have h11x := congrFun e11 x
  have h22x := congrFun e22 x
  change perT c (fun x => -cpd 0 φ x - ν * (cpd 1 (fun y => cpd 1 φ y) x +
    cpd 2 (fun y => cpd 2 φ y) x)) x = -cpd 0 (perT c φ) x - ν * (cpd 1 (fun y => cpd 1 (perT c φ)
      y) x + cpd 2 (fun y => cpd 2 (perT c φ) y) x)
  rw [h1, h0x, h11x, h22x]

/-- **The cut-off heat equation** `(∂_s - νΔ_{q,η}) u_i = f_i` on `ℝ × ℝ²`, from the weak flat
equation of `V` with source `G` against all periodic band tests. -/
theorem isCylHeat_of_weak {c ν σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {μ : ℂ} (V G : HSpace c MeridC)
    (hweakAll : ∀ ψ : Profile → MeridC, IsMeridTest c ψ →
      μ * (∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • V p) ∂(cellMeasure c)) -
        ∫ p, inner ℂ (pdS ψ p + ν • lapQE ψ p) (V p) ∂(cellMeasure c) =
      ∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • G p) ∂(cellMeasure c))
    (i : Fin 2) :
    IsCylHeatL ν (uCut c σ H1 (V : Profile → MeridC) i)
      (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i) := by
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  set θ := timeCut σ H1 with hθdef
  have hθs : ContDiff ℝ ∞ θ := timeCut_contDiff σ H1
  have hθd : Differentiable ℝ θ := hθs.differentiable (by simp)
  obtain ⟨M0, hM0n, hM0⟩ := st_deriv_bound
  intro φ hφ
  set Φ : Coord → ℝ := perT c φ with hΦdef
  have hΦs : ContDiff ℝ ∞ Φ := perT_contDiff hc hφ.smooth hφ.compact
  have hΦd : Differentiable ℝ Φ := hΦs.differentiable (by simp)
  obtain ⟨T, hT⟩ := perT_eta_band (c := c) hφ.compact
  have hΦper : QPeriodic c Φ := fun p => by
    have := perT_periodic c φ p
    rwa [add_qv_eq] at this
  -- the periodic test `Θ = θ(s) Φ`
  set Θ : Profile → ℝ := fun p => θ p.1 * Φ p with hΘdef
  have hΘs : ContDiff ℝ ∞ Θ := (hθs.comp contDiff_fst).mul hΦs
  have hΘd : Differentiable ℝ Θ := hΘs.differentiable (by simp)
  have hΘper : QPeriodic c Θ := fun p => by simp only [hΘdef, hΦper p]
  have hΘband : ∀ p, Θ p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T := by
    intro p hp
    have h1 : θ p.1 ≠ 0 := fun h => hp (by simp [hΘdef, h])
    have h2 : Φ p ≠ 0 := fun h => hp (by simp [hΘdef, h])
    obtain ⟨a1, a2⟩ := timeCut_support hσ hH h1
    exact ⟨⟨a1.le, a2.le⟩, hT p h2⟩
  have hs0 : 0 < σ / 2 := by linarith
  -- derivatives of `Θ`
  have hpdS : ∀ p, pdS Θ p = deriv θ p.1 * Φ p + θ p.1 * pdS Φ p := by
    intro p
    have := fderiv_fstMul (hθd p.1) (hΦd p) ((1 : ℝ), (0 : ℝ), (0 : ℝ))
    simp only [mul_one] at this
    exact this
  have hpdQ : pdQ Θ = fun p => θ p.1 * pdQ Φ p := by
    funext p
    have := fderiv_fstMul (hθd p.1) (hΦd p) ((0 : ℝ), (1 : ℝ), (0 : ℝ))
    simp only [mul_zero, zero_mul, zero_add] at this
    exact this
  have hpdE : pdEta Θ = fun p => θ p.1 * pdEta Φ p := by
    funext p
    have := fderiv_fstMul (hθd p.1) (hΦd p) ((0 : ℝ), (0 : ℝ), (1 : ℝ))
    simp only [mul_zero, zero_mul, zero_add] at this
    exact this
  have hdQΦ : Differentiable ℝ (pdQ Φ) := (contDiff_pdQ' hΦs).differentiable (by simp)
  have hdEΦ : Differentiable ℝ (pdEta Φ) := (contDiff_pdEta' hΦs).differentiable (by simp)
  have hpdQQ : ∀ p, pdQ (pdQ Θ) p = θ p.1 * pdQ (pdQ Φ) p := by
    intro p
    rw [hpdQ]
    have := fderiv_fstMul (hθd p.1) (hdQΦ p) ((0 : ℝ), (1 : ℝ), (0 : ℝ))
    simp only [mul_zero, zero_mul, zero_add] at this
    exact this
  have hpdEE : ∀ p, pdEta (pdEta Θ) p = θ p.1 * pdEta (pdEta Φ) p := by
    intro p
    rw [hpdE]
    have := fderiv_fstMul (hθd p.1) (hdEΦ p) ((0 : ℝ), (0 : ℝ), (1 : ℝ))
    simp only [mul_zero, zero_mul, zero_add] at this
    exact this
  -- the pointwise identity `θ (heat transpose of Φ) = -(∂_sΘ + νΔΘ) + θ'Φ`
  have hpt : ∀ p, θ p.1 * cylHeatTL ν Φ p =
      -(pdS Θ p + ν * lapR Θ p) + deriv θ p.1 * Φ p := by
    intro p
    rw [cylHeatT_eq, hpdS, lapR, hpdQQ, hpdEE]
    ring
  -- the weak flat equation against `vecOf i Θ`
  have hψ : IsMeridTest c (vecOf i Θ) := isMeridTest_vecOf i hΘs hΘper hs0 hΘband
  set h1 : Profile → ℝ := fun q => pdS Θ q + ν * lapR Θ q with hh1def
  have hcomb : ∀ p, vecOf i (pdS Θ) p + ν • vecOf i (lapR Θ) p = vecOf i h1 p := by
    intro p
    simp only [vecOf, hh1def, smul_smul, add_smul]
  have hweak : μ * (∫ p, (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • V p) i) ∂(cellMeasure c)) -
      ∫ p, (h1 p : ℂ) * V p i ∂(cellMeasure c) =
      ∫ p, (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • G p) i) ∂(cellMeasure c) := by
    have hw := hweakAll _ hψ
    rw [pdS_vecOf i hΘd, lapQE_vecOf i hΘs] at hw
    have e1 : ∀ p : Profile, inner ℂ (vecOf i Θ p) ((p.1⁻¹ : ℝ) • V p) =
        (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • V p) i) := fun p => inner_vecOf _ _ _ _
    have e2 : ∀ p : Profile, inner ℂ (vecOf i (pdS Θ) p + ν • vecOf i (lapR Θ) p) (V p) =
        (h1 p : ℂ) * V p i := fun p => by rw [hcomb p, inner_vecOf]
    have e3 : ∀ p : Profile, inner ℂ (vecOf i Θ p) ((p.1⁻¹ : ℝ) • G p) =
        (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • G p) i) := fun p => inner_vecOf _ _ _ _
    simp only [e1, e2, e3] at hw
    exact hw
  -- bands of the auxiliary tests
  have hbandS : ∀ p, pdS Θ p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T :=
    band_fderiv hΘband _
  have hbandQQ : ∀ p, pdQ (pdQ Θ) p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T :=
    band_fderiv (band_fderiv hΘband _) _
  have hbandEE : ∀ p, pdEta (pdEta Θ) p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T :=
    band_fderiv (band_fderiv hΘband _) _
  have hband1 : ∀ p, h1 p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T := by
    intro p hp
    by_cases hS : pdS Θ p = 0
    · by_cases hQ : pdQ (pdQ Θ) p = 0
      · have hE : pdEta (pdEta Θ) p ≠ 0 := fun hE => hp (by simp [hh1def, lapR, hS, hQ, hE])
        exact hbandEE p hE
      · exact hbandQQ p hQ
    · exact hbandS p hS
  have hh1c : Continuous h1 :=
    (contDiff_pdS' hΘs).continuous.add (continuous_const.mul
      ((contDiff_pdQ' (contDiff_pdQ' hΘs)).continuous.add
        (contDiff_pdEta' (contDiff_pdEta' hΘs)).continuous))
  set h2 : Profile → ℝ := fun q => deriv θ q.1 * Φ q with hh2def
  have hband2 : ∀ p, h2 p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T := by
    intro p hp
    have ha : deriv θ p.1 ≠ 0 := fun h => hp (by simp [hh2def, h])
    have hb : Φ p ≠ 0 := fun h => hp (by simp [hh2def, h])
    refine ⟨?_, hT p hb⟩
    by_contra hn
    exact ha (deriv_timeCut_eq_zero_of_not_mem hσ hH hn)
  have hh2c : Continuous h2 :=
    ((continuous_deriv_timeCut σ H1).comp continuous_fst).mul hΦs.continuous
  -- integrability of the four pairings on the cell
  have hInvK : ∀ s ∈ Icc (σ / 2) (2 * H1), |s⁻¹| ≤ 2 / σ := by
    intro s hs
    have hs' : 0 < s := lt_of_lt_of_le hs0 hs.1
    rw [abs_inv, abs_of_pos hs', inv_eq_one_div, div_le_div_iff₀ hs' hσ]
    linarith [hs.1]
  have hOneK : ∀ s ∈ Icc (σ / 2) (2 * H1), |(fun _ : ℝ => (1 : ℝ)) s| ≤ 1 := by
    intro s _
    simp
  have hvc : ∀ {h : Profile → ℝ}, Continuous h → Continuous (vecOf i h) :=
    fun hc' => hc'.smul continuous_const
  have hvband : ∀ {h : Profile → ℝ}, (∀ p, h p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T) →
      ∀ p, vecOf i h p ≠ 0 → p.1 ∈ Icc (σ / 2) (2 * H1) ∧ |p.2.2| ≤ T :=
    fun hb p hp => hb p fun h0 => hp (by simp [vecOf, h0])
  have hI1 : Integrable (fun p => (h1 p : ℂ) * V p i) (cellMeasure c) := by
    have := integrable_inner_band (c := c) V (hvc hh1c) (hvband hband1) measurable_const hOneK
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [inner_vecOf, one_smul]
  have hI2 : Integrable (fun p => (h2 p : ℂ) * V p i) (cellMeasure c) := by
    have := integrable_inner_band (c := c) V (hvc hh2c) (hvband hband2) measurable_const hOneK
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [inner_vecOf, one_smul]
  have hI3 : Integrable (fun p => (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • G p) i)) (cellMeasure c) := by
    have := integrable_inner_band (c := c) G (hvc hΘs.continuous) (hvband hΘband)
      measurable_inv hInvK
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [inner_vecOf]
  have hI4 : Integrable (fun p => (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • V p) i)) (cellMeasure c) := by
    have := integrable_inner_band (c := c) V (hvc hΘs.continuous) (hvband hΘband)
      measurable_inv hInvK
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [inner_vecOf]
  -- unfold both sides onto the cell
  have hpos_u : ∀ x : Coord, x.1 ≤ 0 → uCut c σ H1 (V : Profile → MeridC) i x = 0 := fun x hx =>
    uCut_zero (c := c) (x := x) hσ hH (V : Profile → MeridC) i fun h => by linarith [h.1]
  have hpos_f : ∀ x : Coord, x.1 ≤ 0 → fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i x = 0 := fun x hx =>
    fCut_zero (c := c) (x := x) hσ hH μ (V : Profile → MeridC) (G : Profile → MeridC) i
      fun h => by linarith [h.1]
  have hloc_u : LocallyIntegrable (uCut c σ H1 (V : Profile → MeridC) i) volume :=
    locInt_of_band hc hs0 (uCut_periodic hc (V : Profile → MeridC) i) (fun x hx => uCut_zero (c := c) hσ hH (V : Profile → MeridC) i hx)
      (memLp_uCut hc hσ hH V i)
  have hloc_f : LocallyIntegrable (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i) volume :=
    locInt_of_band hc hs0 (fCut_periodic hc μ (V : Profile → MeridC) (G : Profile → MeridC) i) (fun x hx => fCut_zero (c := c) hσ hH μ (V : Profile → MeridC) (G : Profile → MeridC) i hx)
      (memLp_fCut hc hσ hσH hH μ V G i)
  have hcyl_c : Continuous (cylHeatTL ν φ) := by
    have h0 := (cpd_contDiff hφ.smooth 0).continuous
    have h1' := (cpd_contDiff (cpd_contDiff hφ.smooth 1) 1).continuous
    have h2' := (cpd_contDiff (cpd_contDiff hφ.smooth 2) 2).continuous
    exact h0.neg.sub (continuous_const.mul (h1'.add h2'))
  have hcyl_k : HasCompactSupport (cylHeatTL ν φ) := by
    have h0 := cpd_hasCompactSupport hφ.compact 0
    have h1' := cpd_hasCompactSupport (cpd_hasCompactSupport hφ.compact 1) 1
    have h2' := cpd_hasCompactSupport (cpd_hasCompactSupport hφ.compact 2) 2
    exact h0.neg.sub ((h1'.add h2').mul_left (f := fun _ => ν))
  rw [integral_mul_test_eq_cell hc (uCut_periodic hc (V : Profile → MeridC) i) hpos_u hloc_u hcyl_c hcyl_k,
    integral_mul_test_eq_cell hc (fCut_periodic hc μ (V : Profile → MeridC) (G : Profile → MeridC) i) hpos_f hloc_f hφ.smooth.continuous
      hφ.compact, perT_cylHeatT hc ν hφ]
  change ∫ x, uCut c σ H1 (V : Profile → MeridC) i x * (cylHeatTL ν Φ x : ℂ) ∂(cellMeasure c) =
    ∫ x, fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i x * (Φ x : ℂ) ∂(cellMeasure c)
  have hLHS : ∫ x, uCut c σ H1 (V : Profile → MeridC) i x * (cylHeatTL ν Φ x : ℂ) ∂(cellMeasure c) =
      -(∫ p, (h1 p : ℂ) * V p i ∂(cellMeasure c)) + ∫ p, (h2 p : ℂ) * V p i ∂(cellMeasure c) := by
    have hI1n : Integrable (fun p => -((h1 p : ℂ) * V p i)) (cellMeasure c) := hI1.neg
    rw [← integral_neg, ← integral_add hI1n hI2]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_cell c] with x hx
    simp only [uCut, periodize_of_mem hc (V : Profile → MeridC) hx]
    have e : θ x.1 * cylHeatTL ν Φ x = -(h1 x) + h2 x := by rw [hpt x]
    have e' : ((θ x.1 : ℝ) : ℂ) * (cylHeatTL ν Φ x : ℂ) = -((h1 x : ℝ) : ℂ) + ((h2 x : ℝ) : ℂ) := by
      exact_mod_cast e
    linear_combination (V x i) * e'
  have hRHS : ∫ x, fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i x * (Φ x : ℂ) ∂(cellMeasure c) =
      (∫ p, (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • G p) i) ∂(cellMeasure c)) -
        μ * (∫ p, (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • V p) i) ∂(cellMeasure c)) +
          ∫ p, (h2 p : ℂ) * V p i ∂(cellMeasure c) := by
    have hI34 : Integrable (fun p => (Θ p : ℂ) * (((p.1⁻¹ : ℝ) • G p) i) -
        μ * ((Θ p : ℂ) * (((p.1⁻¹ : ℝ) • V p) i))) (cellMeasure c) := hI3.sub (hI4.const_mul μ)
    rw [← integral_const_mul, ← integral_sub hI3 (hI4.const_mul μ), ← integral_add hI34 hI2]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_cell c] with x hx
    simp only [fCut, periodize_of_mem hc (V : Profile → MeridC) hx, periodize_of_mem hc (G : Profile → MeridC) hx, smul_apply_real, hΘdef,
      hh2def]
    push_cast
    ring
  rw [hLHS, hRHS]
  linear_combination hweak

theorem isCylHeat_uCut {c ν σ H1 : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (g : HSpace c MeridC) (i : Fin 2) :
    IsCylHeatL ν (uCut c σ H1 (UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC) i)
      (fCut c σ H1 μ (UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC)
        (g : Profile → MeridC) i) :=
  isCylHeat_of_weak hc hσ hσH (UnforcedLeray.B0225.R0 hc ν μ g) g
    (fun _ hψ => weak_cell hc hν hμ g hψ) i

end UnforcedLeray.Short.PartIIa.FBCLL
