import UnforcedLeray.Units.B0226.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Homotopy.HSpaces

/-!
# B0226, part 4: `D_ε b_r + ∂_η b_z = 0` in the sense of distributions (Lebesgue pairing)

Blueprint unit B0226, `paper/main.tex` lines 3398–3400. `solenoidalH ε c` (file
`B0226/Defs.lean`) is defined by the pairing of `H = L²(s^{-3/2} ds dq dη)`:
`∫ s^{-3/2} (b_r D_εΦ + b_z ∂_ηΦ) = 0` for all profile tests `Φ`. Here it is identified with the
standard distributional equation on the cylinder `(0,∞) × (ℝ/cℤ) × ℝ`, tested with the Lebesgue
pairing `ds dq dη` on one cell:
`⟨D_ε b_r + ∂_η b_z, Ψ⟩ = ∫ b_r D_εᵀΨ − b_z ∂_ηΨ = 0`, where
`D_εᵀΨ = −∂_qΨ + ε(KΨ + 3Ψ)` is the formal transpose of `D_ε = ∂_q − εK`
(`∂_sᵀ = −∂_s`, so `Kᵀ = −K − 3`), see `divDistrib` and `mem_solenoidalH_iff_distrib`.
The integrand is integrable on the cell for `b ∈ H` (`integrableOn_divDistrib`), so these are
genuine integrals. The bijection of test functions is `Ψ ↦ s^{3/2} Ψ` (`ageScale`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-- The distribution `D_ε b_r + ∂_η b_z` evaluated on a test `Ψ`:
`∫_{cell} b_r (−∂_qΨ + ε(KΨ + 3Ψ)) − b_z ∂_ηΨ ds dq dη`. -/
def divDistrib (ε c : ℝ) (b : Profile → Merid) (Ψ : Profile → ℝ) : ℝ :=
  ∫ p in cell c, (b p 0 * (-Axi.dQ Ψ p + ε * (Kop Ψ p + 3 * Ψ p)) - b p 1 * Axi.dEta Ψ p)

/-- Multiplication of a profile by the age power `s^a`. -/
def ageScale (a : ℝ) (Ψ : Profile → ℝ) (p : Profile) : ℝ := p.1 ^ a * Ψ p

theorem IsProfileTest.eq_zero_of_nonpos {c : ℝ} {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ)
    {p : Profile} (hp : p.1 ≤ 0) : Ψ p = 0 := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΨ.band
  by_contra h
  have := (hb p h).1.1
  linarith

theorem IsProfileTest.fderiv_eq_zero_of_nonpos {c : ℝ} {Ψ : Profile → ℝ}
    (hΨ : IsProfileTest c Ψ) {p : Profile} (hp : p.1 ≤ 0) : fderiv ℝ Ψ p = 0 := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΨ.band
  refine fderiv_of_notMem_tsupport ℝ fun h => ?_
  have := (tsupport_subset_band hb h).1.1
  linarith

theorem isProfileTest_ageScale {c : ℝ} (a : ℝ) {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ) :
    IsProfileTest c (ageScale a Ψ) where
  smooth := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hΨ.band
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · exact ((Real.contDiffAt_rpow_const_of_ne hp.ne').comp p contDiffAt_fst).mul
        hΨ.smooth.contDiffAt
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      have hW : IsOpen {q : Profile | q.1 < s0} := isOpen_lt continuous_fst continuous_const
      filter_upwards [hW.mem_nhds (show p.1 < s0 by linarith [not_lt.1 hp])] with q hq
      have : Ψ q = 0 := by
        by_contra h
        exact absurd (hb q h).1.1 (not_le.2 hq)
      simp [ageScale, this]
  periodic p := by
    simp only [ageScale]
    rw [hΨ.periodic p]
  band := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hΨ.band
    exact ⟨s0, s1, L, hs0, fun p hp => hb p (right_ne_zero_of_mul hp)⟩

theorem fderiv_ageScale_apply {c : ℝ} (a : ℝ) {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ)
    (p v : Profile) :
    fderiv ℝ (ageScale a Ψ) p v = p.1 ^ a * fderiv ℝ Ψ p v + Ψ p * (a * p.1 ^ (a - 1) * v.1) := by
  by_cases hp : 0 < p.1
  · have h : HasFDerivAt (ageScale a Ψ)
        ((p.1 ^ a) • fderiv ℝ Ψ p +
          Ψ p • ((a * p.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) p :=
      ((Real.hasDerivAt_rpow_const (Or.inl hp.ne')).comp_hasFDerivAt p hasFDerivAt_fst).mul
        (hΨ.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul]
  · have hp' : p.1 ≤ 0 := not_lt.1 hp
    rw [(isProfileTest_ageScale a hΨ).fderiv_eq_zero_of_nonpos hp',
      hΨ.fderiv_eq_zero_of_nonpos hp', hΨ.eq_zero_of_nonpos hp']
    simp

theorem dS_ageScale {c : ℝ} (a : ℝ) {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ) (p : Profile) :
    Axi.dS (ageScale a Ψ) p = p.1 ^ a * Axi.dS Ψ p + a * p.1 ^ (a - 1) * Ψ p := by
  simp only [Axi.dS, fderiv_ageScale_apply a hΨ]
  ring

theorem dQ_ageScale {c : ℝ} (a : ℝ) {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ) (p : Profile) :
    Axi.dQ (ageScale a Ψ) p = p.1 ^ a * Axi.dQ Ψ p := by
  simp only [Axi.dQ, fderiv_ageScale_apply a hΨ]
  ring

theorem dEta_ageScale {c : ℝ} (a : ℝ) {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ) (p : Profile) :
    Axi.dEta (ageScale a Ψ) p = p.1 ^ a * Axi.dEta Ψ p := by
  simp only [Axi.dEta, fderiv_ageScale_apply a hΨ]
  ring

/-- `s^{-3/2} D_ε(s^{3/2}Ψ) = ∂_qΨ − ε(KΨ + 3Ψ) = −D_εᵀΨ` for `s > 0`. -/
theorem weight_Deps_ageScale (ε : ℝ) {c : ℝ} {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ)
    {p : Profile} (hp : 0 < p.1) :
    p.1 ^ (-(3 / 2 : ℝ)) * Deps ε (ageScale (3 / 2) Ψ) p =
      Axi.dQ Ψ p - ε * (Kop Ψ p + 3 * Ψ p) := by
  have h1 : p.1 ^ (-(3 / 2 : ℝ)) * p.1 ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  have h2 : p.1 ^ (-(3 / 2 : ℝ)) * (p.1 * p.1 ^ ((3 / 2 : ℝ) - 1)) = 1 := by
    rw [← Real.rpow_one_add' hp.le (by norm_num), ← Real.rpow_add hp]
    norm_num
  simp only [Deps, Kop, dS_ageScale _ hΨ, dQ_ageScale _ hΨ, dEta_ageScale _ hΨ]
  linear_combination (Axi.dQ Ψ p - ε * (2 * p.1 * Axi.dS Ψ p + p.2.2 * Axi.dEta Ψ p)) * h1 -
    3 * ε * Ψ p * h2

theorem weight_dEta_ageScale {c : ℝ} {Ψ : Profile → ℝ} (hΨ : IsProfileTest c Ψ)
    {p : Profile} (hp : 0 < p.1) :
    p.1 ^ (-(3 / 2 : ℝ)) * Axi.dEta (ageScale (3 / 2) Ψ) p = Axi.dEta Ψ p := by
  have h1 : p.1 ^ (-(3 / 2 : ℝ)) * p.1 ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  rw [dEta_ageScale _ hΨ]
  linear_combination Axi.dEta Ψ p * h1

theorem ageScale_ageScale {c : ℝ} {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ) :
    ageScale (3 / 2) (ageScale (-(3 / 2)) Φ) = Φ := by
  funext p
  simp only [ageScale]
  by_cases hp : 0 < p.1
  · rw [← mul_assoc, ← Real.rpow_add hp]
    norm_num
  · rw [hΦ.eq_zero_of_nonpos (not_lt.1 hp)]
    simp

theorem ae_weightH_lt_top (c : ℝ) : ∀ᵐ p ∂cellMeasure c, weightH p < ∞ :=
  ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- `∫ s^{-3/2} (b_r D_ε(s^{3/2}Ψ) + b_z ∂_η(s^{3/2}Ψ)) ds dq dη = −⟨D_ε b_r + ∂_η b_z, Ψ⟩`. -/
theorem integral_measureH_ageScale (ε c : ℝ) (b : Profile → Merid) {Ψ : Profile → ℝ}
    (hΨ : IsProfileTest c Ψ) :
    ∫ p, (b p 0 * Deps ε (ageScale (3 / 2) Ψ) p + b p 1 * Axi.dEta (ageScale (3 / 2) Ψ) p)
        ∂measureH c = -divDistrib ε c b Ψ := by
  rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
    (ae_weightH_lt_top c), divDistrib, ← integral_neg, cellMeasure]
  refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  simp only [weightH, smul_eq_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _)]
  have e1 := weight_Deps_ageScale ε hΨ hp1
  have e2 := weight_dEta_ageScale hΨ hp1
  linear_combination b p 0 * e1 + b p 1 * e2

/-- **The exact solenoidal condition as a distributional equation** (tex lines 3398–3400):
`b ∈ H` satisfies `D_ε b_r + ∂_η b_z = 0` in the `H`-weak sense iff
`⟨D_ε b_r + ∂_η b_z, Ψ⟩ = 0` for every test `Ψ` of the cylinder (Lebesgue pairing). -/
theorem mem_solenoidalH_iff_distrib {ε c : ℝ} (b : HSpace c Merid) :
    b ∈ solenoidalH ε c ↔ ∀ Ψ : ProfileTest c, divDistrib ε c b Ψ.1 = 0 := by
  rw [mem_solenoidalH_iff]
  constructor
  · intro h Ψ
    have h1 := h ⟨ageScale (3 / 2) Ψ.1, isProfileTest_ageScale _ Ψ.2⟩
    rw [integral_measureH_ageScale ε c b Ψ.2] at h1
    exact neg_eq_zero.1 h1
  · intro h Φ
    have hΦ : ageScale (3 / 2) (ageScale (-(3 / 2)) Φ.1) = Φ.1 := ageScale_ageScale Φ.2
    have h1 := h ⟨ageScale (-(3 / 2)) Φ.1, isProfileTest_ageScale _ Φ.2⟩
    rw [← hΦ, integral_measureH_ageScale ε c b (isProfileTest_ageScale _ Φ.2), h1, neg_zero]

/-- For `b ∈ H` the pairing `⟨D_ε b_r + ∂_η b_z, Ψ⟩` is an absolutely convergent integral. -/
theorem integrableOn_divDistrib {ε c : ℝ} (b : HSpace c Merid) (Ψ : ProfileTest c) :
    IntegrableOn
      (fun p => b p 0 * (-Axi.dQ Ψ.1 p + ε * (Kop Ψ.1 p + 3 * Ψ.1 p)) - b p 1 * Axi.dEta Ψ.1 p)
      (cell c) := by
  set Φ : ProfileTest c := ⟨ageScale (3 / 2) Ψ.1, isProfileTest_ageScale _ Ψ.2⟩
  have h : Integrable (fun p => b p 0 * Deps ε Φ.1 p + b p 1 * Axi.dEta Φ.1 p) (measureH c) :=
    (L2.integrable_inner b (profileGradH ε c Φ)).congr (by
      filter_upwards [coeFn_profileGradH ε c Φ] with p hp
      rw [hp, inner_profileGrad])
  have h2 := (integrable_withDensity_iff_integrable_smul' measurable_weightH
    (ae_weightH_lt_top c)).1 h
  show Integrable _ (cellMeasure c)
  refine h2.neg.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
  have hp1 : 0 < p.1 := hp.1
  simp only [Pi.neg_apply, weightH, smul_eq_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _)]
  have e1 := weight_Deps_ageScale ε Ψ.2 hp1
  have e2 := weight_dEta_ageScale Ψ.2 hp1
  linear_combination -(b p 0 * e1 + b p 1 * e2)

end UnforcedLeray.B0226
