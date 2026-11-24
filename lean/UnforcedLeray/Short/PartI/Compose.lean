import UnforcedLeray.Short.PartI.Statements

/-!
# Part I: compiled reductions among the statements

What is proved here (no `sorry`, no axioms), from existing Lean and the statements of
`Statements.lean`:

* `compactDuhamelLemma`: Lemma `short-compact-duhamel` (lines 978-1003) from `B0104`.
* `seedXGExists`: the growing pair on `X_G` (lines 593-597) from `exists_gaussianGrowingMode`
  and the simple spectral projection of `L_0` (`Planar.exists_actual_gaussian_mode_simple_spectral_projection`).
* `seedXGSpectrum`: `σ(L₀) ∩ {Re z > 0} = {λ}` (line 602) from `Planar.spectrum_L0_rightHalf_eq_singleton`.
* `seedXGComplement`: second estimate of `short-seed-complement` (line 616) from
  `Planar.norm_exp_L0_sub_mul_one_sub_le`.
* `seedDilationGenerator_fst`: `𝓛_a = a⁻²J_a𝓛J_a⁻¹` (line 939) from `Planar.dilation_conj_sec`.
* `seedOscillator_core`: selfadjointness, nonpositivity, spectrum `{0,-1,-2,…}` of `D`
  (lines 619-621) from `B0094`.
* `seedStrainCoupling_of`: `ℓ(H) = M_q/J_q ≠ 0` (line 610) from `SeedFunctional` and
  `SeedModeRegularity` (the source's one-line computation `h·(r²k)/k·r = r³ h`).
* `partIResults_of`: all of `PartIResults` from the remaining leaf statements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-- Lemma `short-compact-duhamel` (lines 978-1003): proved in `Units/B0104`. -/
theorem compactDuhamelLemma (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) : CompactDuhamelLemma H ι := by
  intro B F F₀ A A₀ U U₀ hFb hF hFadj hAb hA hA₀c hA₀p hD hD₀ hU hU₀
  exact B0104.compact_duhamel_dyson hFb hF hFadj hAb hA hA₀c hA₀p hD hD₀ hU hU₀

/-- The growing pair exists (lines 593-597). -/
theorem seedXGExists : SeedXGExists := by
  obtain ⟨G, ℓ, hone, -, hproj⟩ := Planar.exists_actual_gaussian_mode_simple_spectral_projection
  refine ⟨G.eigenvalue, G.h, G.h_memLp_XG, ℓ, ?_⟩
  refine ⟨G.growth_pos, ?_, ?_, hone, hproj⟩
  · intro h0
    rw [h0, map_zero] at hone
    exact zero_ne_one hone
  · simpa [Planar.GaussianGrowingMode.eigenvalue] using G.L0_eigen

/-- `σ(L₀) ∩ {Re z > 0} = {λ}` on `X_G` (line 602). -/
theorem seedXGSpectrum : SeedXGSpectrum := fun _ _ _ h =>
  Planar.spectrum_L0_rightHalf_eq_singleton h.re_pos h.ne_zero h.eigen

/-- `‖e^{t(L₀-λ)}Q‖ ≤ C_η e^{-(γ-η)t}` (line 616). -/
theorem seedXGComplement : SeedXGComplement := fun _ _ _ h _ hδ =>
  Planar.norm_exp_L0_sub_mul_one_sub_le h.re_pos h.ne_zero h.eigen h.proj hδ

/-- `𝓛_a = a⁻² J_a 𝓛 J_a⁻¹` (line 939), sector by sector. -/
theorem seedDilationGenerator_fst :
    ∀ (M : ℝ) (hM : 1 < M) (a : ℝ) (ha : 0 < a) (n : ℤ),
      Planar.LsecDil hM ha n =
        (((a ^ 2)⁻¹ : ℝ) : ℂ) •
          (Planar.dilP hM ha ∘L Planar.Lsec hM n ∘L Planar.dilP hM (inv_pos.2 ha)) :=
  fun _ hM _ ha n => Planar.dilation_conj_sec hM ha n

/-- `D` is selfadjoint, nonpositive, with spectrum `{0,-1,-2,…}` (lines 619-621). -/
theorem seedOscillator_core :
    IsSelfAdjoint B0094.D ∧
    (∀ f : B0094.D.domain, (inner ℂ (f : B0010.XG) (B0094.D f)).re ≤ 0) ∧
    B0094.opSpectrum B0094.D = Set.range (fun n : ℕ => -(n : ℂ)) :=
  ⟨B0094.isSelfAdjoint_D, fun f => (B0094.D_nonpos f).1, B0094.opSpectrum_D⟩

/-- `{r | k(r) = 0}` is Lebesgue-null: `k(r) = (r²/4 - 2)e^{-r²/4}` vanishes only at `r = ±√8`. -/
theorem ae_strainK_ne_zero : ∀ᵐ r : ℝ ∂volume, Blueprint.Planar.strainK r ≠ 0 := by
  have hsub : {r : ℝ | Blueprint.Planar.strainK r = 0} ⊆ {Real.sqrt 8, -Real.sqrt 8} := by
    intro r hr
    simp only [Blueprint.Planar.strainK, mul_eq_zero] at hr
    rcases hr with h | h
    · have h8 : r ^ 2 = 8 := by linarith
      have : r = Real.sqrt 8 ∨ r = -Real.sqrt 8 := by
        have hs : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
        have : (r - Real.sqrt 8) * (r + Real.sqrt 8) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h1 | h1
        · left; linarith
        · right; linarith
      simpa using this
    · exact absurd h (Real.exp_pos _).ne'
  rw [ae_iff]
  have hfin : ({Real.sqrt 8, -Real.sqrt 8} : Set ℝ).Finite := Set.toFinite _
  have hnull : volume ({Real.sqrt 8, -Real.sqrt 8} : Set ℝ) = 0 := hfin.measure_zero volume
  refine measure_mono_null ?_ hnull
  intro r hr
  have h0 : Blueprint.Planar.strainK r = 0 := by simpa using hr
  exact hsub h0

/-- `ℓ(H) = M_q/J_q ≠ 0` (line 610): the one-line computation `h·(r²k)/k·r = r³h`. -/
theorem seedStrainCoupling_of (hreg : SeedModeRegularity) (hfun : SeedFunctional) :
    SeedStrainCoupling := by
  intro lam h hh ℓ hI
  obtain ⟨-, -, h', hae, -, -, -, -, -, -, -, hMq⟩ := hreg lam h hh ℓ hI
  obtain ⟨hJ, -, -, -, -⟩ := hfun lam h hh ℓ hI
  have hq : Blueprint.Planar.quadrupole h = Blueprint.Planar.quadrupole h' := by
    unfold Blueprint.Planar.quadrupole
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    have := (ae_restrict_iff' measurableSet_Ioi).1 hae
    filter_upwards [this] with r hr hr0
    rw [hr hr0]
  have key : seedEll h Blueprint.Planar.strainProfile = Blueprint.Planar.quadrupole h / seedJ h := by
    unfold seedEll Blueprint.Planar.quadrupole
    rw [div_eq_inv_mul]
    congr 1
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [ae_strainK_ne_zero] with r hk _
    have hk' : (Blueprint.Planar.strainK r : ℂ) ≠ 0 := by exact_mod_cast hk
    simp only [Blueprint.Planar.strainProfile]
    push_cast
    field_simp
  refine ⟨key, ?_⟩
  rw [key]
  exact div_ne_zero (hq ▸ hMq) hJ

/-- Bridge to the older interface: `TrainStrainIntegral` gives `B0278.TrainStrainFamily` (the `k = 1`
strain estimate used by `Units/B0277`, `B0278`) for the family of trains `ν ↦ train ν c`, where the
train of period `c = ν^{-ρ}` is a chosen member of the BUC class (`TrainGlobalExistence`; for
`0 < ν ≤ 1` the period `ν^{-ρ} ≥ 1`, and the family is `0` for `ν > 1`, which `TrainStrainFamily`
never inspects since it only asks for small `ν`). -/
theorem trainStrainFamily_of (hex : TrainGlobalExistence) (h : TrainStrainIntegral) (ρ : ℝ)
    (hρ : 1 / 2 < ρ) :
    B0278.TrainStrainFamily (E := Cyl.Plane) (F := Train.Vec) ρ
      (fun ν s z => if hν : 0 < ν ∧ ν ≤ 1 then
        (hex ν (trainPeriod ρ ν) hν.1
          (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν.1 hν.2 (by linarith))).choose.v s z
        else 0) := by
  obtain ⟨C1, ν₀, hC, hν₀, H⟩ := h ρ hρ 1
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, C1, fun ν hν hνle σ₀ hσ h1 => ?_⟩
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hcc : 1 ≤ trainPeriod ρ ν :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have key := H ν hν (hνle.trans (min_le_left _ _)) (hex ν (trainPeriod ρ ν) hν hcc).choose
    (hex ν (trainPeriod ρ ν) hν hcc).choose_spec σ₀ hσ h1
  simpa [hν, hν1, trainPeriod] using key

/-- All of `PartIResults` from the leaf statements that are not derived above. -/
theorem partIResults_of
    (hex : TrainGlobalExistence) (huniq : TrainUniqueness) (hcomp : TrainComparison)
    (hover : TrainOverlap) (hl2 : TrainL2Decay) (hstrain : TrainStrainIntegral)
    (hfl : TrainFluctuationIntegral) (hmean : TrainMeanEquations)
    (hfluct : TrainFluctuationDecay) (hexp : TrainMeanExpansion)
    (htail : TrainTransverseTails) (hband : TrainFixedBand)
    (hreg : SeedModeRegularity) (hfun : SeedFunctional) (hspec : SeedEulerSpectrum)
    (hcmp : SeedEulerComplement) (hosc : SeedOscillator) (hdg : SeedDilationGenerator)
    (hdp : SeedDilationProjection) (hsd : SmallDiffusionComplement)
    (hcan : CanonicalBranch) (hmel : CanonicalMellin) : PartIResults where
  trainExistence := hex
  trainUniqueness := huniq
  trainComparison := hcomp
  trainOverlap := hover
  trainL2Decay := hl2
  trainStrainIntegral := hstrain
  trainFluctuationIntegral := hfl
  trainMeanEquations := hmean
  trainFluctuationDecay := hfluct
  trainMeanExpansion := hexp
  trainTransverseTails := htail
  trainFixedBand := hband
  seedXGExists := seedXGExists
  seedModeRegularity := hreg
  seedXGSpectrum := seedXGSpectrum
  seedFunctional := hfun
  seedStrainCoupling := seedStrainCoupling_of hreg hfun
  seedEulerSpectrum := hspec
  seedEulerComplement := hcmp
  seedXGComplement := seedXGComplement
  seedOscillator := hosc
  seedDilationGenerator := hdg
  seedDilationProjection := hdp
  smallDiffusionComplement := hsd
  canonicalBranch := hcan
  canonicalMellin := hmel

end UnforcedLeray.Short.PartI
