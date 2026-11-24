import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.R0Transpose
import Mathlib.Tactic.Module

/-!
# Helpers for `PartII-a:N05/2/2/1`: the weak flat equation of `R₀(μ)g` against all tests

Source: `the November 2 reference manuscript`, lines 1650-1656 (the causal flat
inverse `R₀(μ)` is the Laplace transform of `T₀(t)`, generator `A₀ = -S + νsΔ_{q,η}`) and
1794-1799 (the flat heat equation is cut off and the heat estimate is applied).

* `r0_transpose_complex`: for complex `μ` with `Re μ + 1/4 > 0` and every smooth test `ζ`,
  `μ ⟨R₀(μ)g, ζ⟩_H - ⟨R₀(μ)g, A₀*ζ⟩_H = ⟨g, ζ⟩_H` (the complex form of
  `FlatSettingInst.R0TransposeIdentity`, same proof: integrate the generator identity against
  `e^{-μt}`).
* `weak_cell`: with `ζ = s^{1/2}ψ` the weights cancel and the identity becomes the weak form of
  `∂_s w + (μ/s) w - νΔ_{q,η} w = g/s` in the unweighted cell measure, against every smooth
  periodic band-supported test `ψ` (no solenoidality of `ψ` is needed: `R₀` is the componentwise
  heat flow).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure weightH cell)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (pairH A0adj pairH_eq_inner
  memLp_test_A0adj t0_generator t0_contZero)

/-! ### The complex transpose identity -/

/-- **Transpose identity of `R₀(μ)` for complex `μ`**: `μ⟨R₀g, ζ⟩ - ⟨R₀g, A₀*ζ⟩ = ⟨g, ζ⟩`. -/
theorem r0_transpose_complex {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {μ : ℂ}
    (hμ : 0 < μ.re + 1 / 4) (g : HSpace c MeridC) {ζ : Profile → MeridC}
    (hζ : IsMeridTest c ζ) :
    μ * pairH c (UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC) ζ -
        pairH c (UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC) (A0adj ν ζ) =
      pairH c (g : Profile → MeridC) ζ := by
  obtain ⟨hZm, hAm⟩ := memLp_test_A0adj c ν ζ hζ
  obtain ⟨Z, hZ⟩ : ∃ Z : HSpace c MeridC, (Z : Profile → MeridC) =ᵐ[measureH c] ζ :=
    ⟨hZm.toLp ζ, hZm.coeFn_toLp⟩
  obtain ⟨AZ, hAZ⟩ : ∃ AZ : HSpace c MeridC,
      (AZ : Profile → MeridC) =ᵐ[measureH c] A0adj ν ζ :=
    ⟨hAm.toLp _, hAm.coeFn_toLp⟩
  set V : HSpace c MeridC := (starRingEnd ℂ μ) • Z - AZ with hVdef
  have hV : ∀ y : HSpace c MeridC, inner ℂ V y = μ * inner ℂ Z y - inner ℂ AZ y := by
    intro y
    rw [hVdef, inner_sub_left, inner_smul_left, Complex.conj_conj]
  have hFz : ∀ t : ℝ, pairH c (UnforcedLeray.B0224.T0 hc ν t g : Profile → MeridC) ζ =
      inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g) := fun t => pairH_eq_inner _ Z hZ
  have hint : IntegrableOn
      (fun t : ℝ => Complex.exp (-(μ * t)) • UnforcedLeray.B0224.T0 hc ν t g) (Ioi 0) :=
    UnforcedLeray.B0225.integrableOn_lapT0 hc ν hμ g
  have hR0 : inner ℂ V (UnforcedLeray.B0225.R0 hc ν μ g) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) *
        inner ℂ V (UnforcedLeray.B0224.T0 hc ν t g) := by
    rw [UnforcedLeray.B0225.R0_apply hc ν hμ g, ← integral_inner hint]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [inner_smul_right]
  have hcont : ContinuousWithinAt
      (fun t : ℝ => Complex.exp (-(μ * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
      (Ici 0) 0 := by
    have h1 : ContinuousWithinAt
        (fun t : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g)) (Ici 0) 0 :=
      (t0_contZero c ν hc g ζ hζ).congr (fun t _ => (hFz t).symm) (hFz 0).symm
    exact (Continuous.continuousWithinAt (by fun_prop)).mul h1
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt
        (fun t : ℝ => Complex.exp (-(μ * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
        (-(Complex.exp (-(μ * x)) * inner ℂ V (UnforcedLeray.B0224.T0 hc ν x g))) x := by
    intro x hx
    have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(μ * t)))
        (Complex.exp (-(μ * x)) * (-μ)) x := by
      have h := (((hasDerivAt_id x).ofReal_comp).const_mul μ).neg.cexp
      simpa using h
    have hF : HasDerivAt (fun t : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
        (inner ℂ AZ (UnforcedLeray.B0224.T0 hc ν x g)) x := by
      have h := t0_generator c ν hc hν g ζ hζ x hx
      have hfun : (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) =
          fun s : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν s g) := funext hFz
      rw [hfun] at h
      rw [show pairH c (UnforcedLeray.B0224.T0 hc ν x g : Profile → MeridC) (A0adj ν ζ) =
          inner ℂ AZ (UnforcedLeray.B0224.T0 hc ν x g) from pairH_eq_inner _ AZ hAZ] at h
      exact h
    have hprod := hE.mul hF
    refine hprod.congr_deriv ?_
    rw [hV]
    ring
  have hfint : IntegrableOn
      (fun x : ℝ => -(Complex.exp (-(μ * x)) *
        inner ℂ V (UnforcedLeray.B0224.T0 hc ν x g))) (Ioi 0) := by
    have hI : Integrable (fun t : ℝ => (innerSL ℂ V)
        (UnforcedLeray.B0225.lapT0 hc ν μ g t)) (volume.restrict (Ioi (0 : ℝ))) :=
      ContinuousLinearMap.integrable_comp (innerSL ℂ V) hint
    refine hI.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, innerSL_apply_apply, UnforcedLeray.B0225.lapT0, inner_smul_right]
  have htend : Tendsto
      (fun t : ℝ => Complex.exp (-(μ * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(μ.re + 1 / 4) * t)) atTop (𝓝 0) := by
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop hμ (tendsto_id (x := atTop)))
      exact Tendsto.congr (fun t => by simp only [Function.comp_apply, id, neg_mul]) h2
    have hb : Tendsto (fun t : ℝ => ‖Z‖ * (‖g‖ * Real.exp (-(μ.re + 1 / 4) * t)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ((hexp.const_mul ‖g‖).const_mul ‖Z‖)
    refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hb
    have hEq : Complex.exp (-(μ * t)) * inner ℂ Z (UnforcedLeray.B0224.T0 hc ν t g) =
        inner ℂ Z (UnforcedLeray.B0225.lapT0 hc ν μ g t) := by
      simp only [UnforcedLeray.B0225.lapT0, inner_smul_right]
    rw [hEq]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (UnforcedLeray.B0225.norm_lapT0_le hc ν μ g t)
        (norm_nonneg _))
  have hfinal := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hfint htend
  have hT0g : UnforcedLeray.B0224.T0 hc ν 0 g = g := by
    rw [UnforcedLeray.B0224.T0_zero_eq]
    rfl
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, hT0g] at hfinal
  rw [integral_neg] at hfinal
  rw [pairH_eq_inner _ Z hZ, pairH_eq_inner _ AZ hAZ, pairH_eq_inner g Z hZ, ← hV, hR0]
  linear_combination -hfinal

/-! ### Derivatives of `s^{1/2} ψ` -/

/-- `Δ_{q,η} ψ = ∂_q²ψ + ∂_η²ψ`. -/
def lapQE (ψ : Profile → MeridC) : Profile → MeridC := fun p => pdQ (pdQ ψ) p + pdEta (pdEta ψ) p

theorem hasFDerivAt_sqrt_fst {p : Profile} (hp : 0 < p.1) :
    HasFDerivAt (fun q : Profile => Real.sqrt q.1)
      ((1 / (2 * Real.sqrt p.1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
  (Real.hasDerivAt_sqrt hp.ne').comp_hasFDerivAt p (hasFDerivAt_fst (p := p))

theorem fderiv_sqrt_smul_apply {F : Profile → MeridC} {p : Profile} (hp : 0 < p.1)
    (hF : DifferentiableAt ℝ F p) (v : Profile) :
    fderiv ℝ (fun q : Profile => Real.sqrt q.1 • F q) p v =
      (v.1 / (2 * Real.sqrt p.1)) • F p + Real.sqrt p.1 • fderiv ℝ F p v := by
  have h : HasFDerivAt (fun q : Profile => Real.sqrt q.1 • F q)
      (Real.sqrt p.1 • fderiv ℝ F p +
        ((1 / (2 * Real.sqrt p.1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (F p)) p :=
    (hasFDerivAt_sqrt_fst hp).smul hF.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  rw [add_comm]
  congr 1
  congr 1
  ring

theorem pdS_sqrt_smul {F : Profile → MeridC} {p : Profile} (hp : 0 < p.1)
    (hF : DifferentiableAt ℝ F p) :
    pdS (fun q : Profile => Real.sqrt q.1 • F q) p =
      (1 / (2 * Real.sqrt p.1)) • F p + Real.sqrt p.1 • pdS F p := by
  unfold pdS
  rw [fderiv_sqrt_smul_apply hp hF]

theorem pdQ_sqrt_smul {F : Profile → MeridC} {p : Profile} (hp : 0 < p.1)
    (hF : DifferentiableAt ℝ F p) :
    pdQ (fun q : Profile => Real.sqrt q.1 • F q) p = Real.sqrt p.1 • pdQ F p := by
  unfold pdQ
  rw [fderiv_sqrt_smul_apply hp hF]
  simp

theorem pdEta_sqrt_smul {F : Profile → MeridC} {p : Profile} (hp : 0 < p.1)
    (hF : DifferentiableAt ℝ F p) :
    pdEta (fun q : Profile => Real.sqrt q.1 • F q) p = Real.sqrt p.1 • pdEta F p := by
  unfold pdEta
  rw [fderiv_sqrt_smul_apply hp hF]
  simp

theorem contDiff_pdQ {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pdQ F) := by
  unfold pdQ
  exact (hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem contDiff_pdEta {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (pdEta F) := by
  unfold pdEta
  exact (hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem contDiff_pdS {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pdS F) := by
  unfold pdS
  exact (hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem pdQ_pdQ_sqrt_smul {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) {p : Profile}
    (hp : 0 < p.1) :
    pdQ (pdQ (fun q : Profile => Real.sqrt q.1 • F q)) p = Real.sqrt p.1 • pdQ (pdQ F) p := by
  have hev : pdQ (fun q : Profile => Real.sqrt q.1 • F q) =ᶠ[𝓝 p]
      fun q => Real.sqrt q.1 • pdQ F q := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
    exact pdQ_sqrt_smul hq ((hF.differentiable (by simp)) q)
  have hdF : DifferentiableAt ℝ (pdQ F) p := (contDiff_pdQ hF).differentiable (by simp) p
  change fderiv ℝ (pdQ (fun q : Profile => Real.sqrt q.1 • F q)) p ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = _
  rw [hev.fderiv_eq]
  exact pdQ_sqrt_smul hp hdF

theorem pdEta_pdEta_sqrt_smul {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) {p : Profile}
    (hp : 0 < p.1) :
    pdEta (pdEta (fun q : Profile => Real.sqrt q.1 • F q)) p =
      Real.sqrt p.1 • pdEta (pdEta F) p := by
  have hev : pdEta (fun q : Profile => Real.sqrt q.1 • F q) =ᶠ[𝓝 p]
      fun q => Real.sqrt q.1 • pdEta F q := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
    exact pdEta_sqrt_smul hq ((hF.differentiable (by simp)) q)
  have hdF : DifferentiableAt ℝ (pdEta F) p := (contDiff_pdEta hF).differentiable (by simp) p
  change fderiv ℝ (pdEta (fun q : Profile => Real.sqrt q.1 • F q)) p
    ((0 : ℝ), (0 : ℝ), (1 : ℝ)) = _
  rw [hev.fderiv_eq]
  exact pdEta_sqrt_smul hp hdF

/-- `A₀*(s^{1/2}ψ) = s^{3/2}(∂_sψ + νΔ_{q,η}ψ)` for `s > 0`. -/
theorem A0adj_sqrt_smul (ν : ℝ) {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) {p : Profile}
    (hp : 0 < p.1) :
    A0adj ν (fun q : Profile => Real.sqrt q.1 • F q) p =
      (p.1 * Real.sqrt p.1) • (pdS F p + ν • lapQE F p) := by
  have hdF : DifferentiableAt ℝ F p := (hF.differentiable (by simp)) p
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hk : p.1 * (1 / (2 * Real.sqrt p.1)) = Real.sqrt p.1 / 2 := by
    have h2 : Real.sqrt p.1 * Real.sqrt p.1 = p.1 := Real.mul_self_sqrt hp.le
    field_simp
    linarith
  unfold A0adj
  rw [pdS_sqrt_smul hp hdF, pdQ_pdQ_sqrt_smul hF hp, pdEta_pdEta_sqrt_smul hF hp]
  unfold lapQE
  simp only [smul_add, smul_smul, hk]
  module

/-- `s^{1/2}ψ` is a test when `ψ` is. -/
theorem isMeridTest_sqrt_smul {c : ℝ} {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    IsMeridTest c (fun p : Profile => Real.sqrt p.1 • ψ p) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hψ.band
  refine ⟨?_, ?_, ⟨s0, s1, L, hs0, ?_⟩⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 < s0
    · apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : MeridC)))
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
      have : ψ q = 0 := by
        by_contra h
        exact absurd (hband q h).1.1 (not_le.2 hq)
      simp [this]
    · push_neg at hp
      have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le hs0 hp).ne'
      have h1 : ContDiffAt ℝ ∞ (fun q : Profile => Real.sqrt q.1) p :=
        (Real.contDiffAt_sqrt hp0).comp p contDiff_fst.contDiffAt
      exact h1.smul hψ.smooth.contDiffAt
  · intro p
    simp only [hψ.periodic p]
  · intro p hp
    refine hband p fun h => hp ?_
    simp [h]

/-! ### The weak flat equation in the unweighted cell measure -/

theorem ae_mem_cell (c : ℝ) : ∀ᵐ p ∂(cellMeasure c), p ∈ cell c :=
  ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)

theorem toReal_weightH {p : Profile} (hp : 0 < p.1) :
    (weightH p).toReal = p.1 ^ (-(3 / 2 : ℝ)) := by
  unfold weightH
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _)

theorem inner_real_smul_left (r : ℝ) (x y : MeridC) :
    inner ℂ (r • x) y = (r : ℂ) * inner ℂ x y := by
  rw [← Complex.coe_smul r x, inner_smul_left, Complex.conj_ofReal]

theorem inner_real_smul_right (r : ℝ) (x y : MeridC) :
    inner ℂ x (r • y) = (r : ℂ) * inner ℂ x y := by
  rw [← Complex.coe_smul r y, inner_smul_right]

theorem pairH_sqrt_eq {c : ℝ} (ψ u : Profile → MeridC) :
    pairH c u (fun p : Profile => Real.sqrt p.1 • ψ p) =
      ∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • u p) ∂(cellMeasure c) := by
  unfold pairH
  rw [measureH, integral_withDensity_eq_integral_toReal_smul UnforcedLeray.B0220.measurable_weightH
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_cell c] with p hp
  have hs : 0 < p.1 := hp.1
  rw [toReal_weightH hs, inner_real_smul_left, inner_real_smul_right, Complex.real_smul]
  have hk : p.1 ^ (-(3 / 2 : ℝ)) * Real.sqrt p.1 = p.1⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs, ← Real.rpow_neg_one]
    norm_num
  rw [← mul_assoc, ← Complex.ofReal_mul, hk]

theorem pairH_A0adj_sqrt_eq {c ν : ℝ} {ψ : Profile → MeridC} (hψ : ContDiff ℝ ∞ ψ)
    (u : Profile → MeridC) :
    pairH c u (A0adj ν (fun p : Profile => Real.sqrt p.1 • ψ p)) =
      ∫ p, inner ℂ (pdS ψ p + ν • lapQE ψ p) (u p) ∂(cellMeasure c) := by
  unfold pairH
  rw [measureH, integral_withDensity_eq_integral_toReal_smul UnforcedLeray.B0220.measurable_weightH
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_cell c] with p hp
  have hs : 0 < p.1 := hp.1
  rw [toReal_weightH hs, A0adj_sqrt_smul ν hψ hs, inner_real_smul_left, Complex.real_smul]
  have hk : p.1 ^ (-(3 / 2 : ℝ)) * (p.1 * Real.sqrt p.1) = 1 := by
    rw [Real.sqrt_eq_rpow]
    have : p.1 * p.1 ^ (1 / 2 : ℝ) = p.1 ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hs.le (by norm_num)]
      norm_num
    rw [this, ← Real.rpow_add hs]
    norm_num
  rw [← mul_assoc, ← Complex.ofReal_mul, hk, Complex.ofReal_one, one_mul]

/-- **Weak flat equation of `w = R₀(μ)g` in the cell measure**: for every smooth periodic
band-supported test `ψ`,
`μ ∫⟨ψ, w/s⟩ - ∫⟨∂_sψ + νΔ_{q,η}ψ, w⟩ = ∫⟨ψ, g/s⟩`. -/
theorem weak_cell {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (g : HSpace c MeridC) {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    μ * (∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) •
        (UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC) p) ∂(cellMeasure c)) -
      ∫ p, inner ℂ (pdS ψ p + ν • lapQE ψ p)
        ((UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC) p) ∂(cellMeasure c) =
    ∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (g : Profile → MeridC) p) ∂(cellMeasure c) := by
  have hA := r0_transpose_complex hc hν hμ g (isMeridTest_sqrt_smul hψ)
  rw [pairH_sqrt_eq, pairH_A0adj_sqrt_eq hψ.smooth, pairH_sqrt_eq] at hA
  exact hA

end UnforcedLeray.Short.PartIIa.FBCLL
