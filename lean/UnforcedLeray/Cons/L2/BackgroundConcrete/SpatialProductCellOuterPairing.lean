import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellFixedPairing
import UnforcedLeray.Lib.Semigroups.Multiplication

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- The actual unweighted spatial slice gradient of `Φ·U` is in every finite phase-cell Lp
space, by transporting its scalar derivatives through the coordinate maps. -/
theorem memLp_scalarSliceGrad_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    MemLp (scalarSliceGrad (scalarTestBackground Φ U)) p
      (volume.restrict (phaseCell P)) := by
  let d : Fin 3 → SpaceTime → ℂ := fun j z =>
    fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
      (EuclideanSpace.single j (1 : ℝ))
  have hterm (j : Fin 3) : MemLp (fun z : SpaceTime =>
      d j z • EuclideanSpace.single j (1 : ℂ)) p (volume.restrict (phaseCell P)) := by
    let A : ℂ →L[ℝ] CVec3 :=
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ)
        (EuclideanSpace.single j (1 : ℂ))
    have hd := scalarTestBackground_spatialDerivative_memLp_cell hΦ hU hp j
    have hA := hd.continuousLinearMap_comp A
    have heq : (fun z : SpaceTime => d j z • EuclideanSpace.single j (1 : ℂ)) =ᵐ[
        volume.restrict (phaseCell P)] (fun z => A (d j z)) :=
      Eventually.of_forall fun _ => rfl
    exact (memLp_congr_ae heq).mpr hA
  have hsum := memLp_finsetSum' Finset.univ (fun j _ => hterm j)
  have heq : scalarSliceGrad (scalarTestBackground Φ U) =ᵐ[
      volume.restrict (phaseCell P)]
      (fun z => ∑ j : Fin 3, d j z • EuclideanSpace.single j (1 : ℂ)) := by
    filter_upwards with z
    simp [scalarSliceGrad, d]
  exact (memLp_congr_ae heq).mpr hsum

/-- The actual graph-solenoidal correction annihilates the unweighted spatial slice gradient of
`Φ·U`. The proof removes the phase cutoff after the fixed-cutoff mollifier limit by a genuine
Lp dominated-convergence argument on the cell. -/
theorem integral_scalarSliceGrad_pair_rep_zero {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [ENNReal.HolderTriple p q0E 1] :
    ∫ z : SpaceTime, dotL (scalarSliceGrad (scalarTestBackground Φ U) z)
      (rep w z.1 z.2) ∂(volume.restrict (phaseCell P)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let G : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  let F : SpaceTime → CVec3 := scalarSliceGrad (scalarTestBackground Φ U)
  have hF : MemLp F p μ := by
    exact memLp_scalarSliceGrad_cell hΦ hU hp
  have hG : MemLp G q0E μ := by
    simpa [G, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top w
  have hseq (n : ℕ) : MemLp (fun z : SpaceTime =>
      (phaseInteriorCutoff P n z.1) ^ 2 • F z) p μ := by
    exact memLp_cutoffSquared_scalarSliceGrad_cell hΦ hU hp n
  let g : ℕ → SpaceTime → ℂ := fun n z =>
    Complex.ofReal ((phaseInteriorCutoff P n z.1) ^ 2 - 1)
  have hg (n : ℕ) : AEStronglyMeasurable (g n) μ := by
    have hcont : Continuous (fun z : SpaceTime => g n z) := by
      apply Complex.continuous_ofReal.comp
      exact (((contDiff_phaseInteriorCutoff P n).continuous.comp continuous_fst).pow 2).sub
        continuous_const
    exact hcont.aestronglyMeasurable
  have hB : ∀ n : ℕ, ∀ᵐ z ∂μ, ‖g n z‖ ≤ 1 := by
    intro n
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    have hχ0 := phaseInteriorCutoff_nonneg (P := P) n z.1
    have hχ1 := phaseInteriorCutoff_le_one (P := P) n z.1
    change ‖Complex.ofReal ((phaseInteriorCutoff P n z.1) ^ 2 - 1)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (show phaseInteriorCutoff P n z.1 ^ 2 - 1 ≤ 0 by nlinarith)]
    nlinarith [sq_nonneg (phaseInteriorCutoff P n z.1)]
  have hτ : ∀ᵐ τ : ℝ ∂(volume : Measure ℝ), τ ≠ P := by
    simpa [ae_iff, measure_singleton]
  have hτz : ∀ᵐ z : SpaceTime ∂(volume : Measure SpaceTime), z.1 ≠ P := by
    have h : ∀ᵐ z : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        z.1 ≠ P := Measure.quasiMeasurePreserving_fst.ae hτ
    simpa [Measure.volume_eq_prod] using h
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ => g n z) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ),
      ae_restrict_of_ae hτz] with z hz hτP
    have hτlt : z.1 < P := lt_of_le_of_ne hz.1.2 hτP
    have hev := eventually_phaseInteriorCutoff_eq_one (Fact.out : 0 < P) hz.1.1 hτlt
    have hz0 : ∀ᶠ n : ℕ in atTop, g n z = 0 :=
      hev.mono fun n hn => by simp [g, hn]
    exact tendsto_const_nhds.congr' (hz0.mono fun n hn => hn.symm)
  have hmult := UnforcedLeray.Infra.Mult.tendsto_eLpNorm_smul_of_dominated
    (μ := μ) (p := p) hp (Filter.Eventually.of_forall hg)
    (Filter.Eventually.of_forall hB) hlim hF
  have herror (n : ℕ) : (fun z : SpaceTime =>
      (phaseInteriorCutoff P n z.1) ^ 2 • F z - F z) = fun z => g n z • F z := by
    funext z
    have hreal : (phaseInteriorCutoff P n z.1) ^ 2 • F z - F z =
        ((phaseInteriorCutoff P n z.1) ^ 2 - 1) • F z := by
      calc
        (phaseInteriorCutoff P n z.1) ^ 2 • F z - F z =
            (phaseInteriorCutoff P n z.1) ^ 2 • F z - (1 : ℝ) • F z := by simp
        _ = ((phaseInteriorCutoff P n z.1) ^ 2 - 1) • F z := by rw [← sub_smul]
    calc
      (phaseInteriorCutoff P n z.1) ^ 2 • F z - F z =
          ((phaseInteriorCutoff P n z.1) ^ 2 - 1) • F z := hreal
      _ = Complex.ofReal ((phaseInteriorCutoff P n z.1) ^ 2 - 1) • F z :=
        (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
      _ = g n z • F z := rfl
  have hconv : Tendsto (fun n : ℕ => eLpNorm
      ((fun z : SpaceTime => (phaseInteriorCutoff P n z.1) ^ 2 • F z) - F) p μ)
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_) hmult
    exact (congrArg (fun f : SpaceTime → CVec3 => eLpNorm f p μ) (herror n)).symm
  have hPairLimit := tendsto_integral_dotL_of_eLpNorm hF hG hseq hconv
  have hzero (n : ℕ) (hn : 2 / ((n : ℝ) + 1) ≤ P) :=
    integral_cutoffSquared_scalarSliceGrad_pair_rep_zero hw hΦ hU hp n hn
  have hhn : ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) ≤ P := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / P)
    have hNreal : 2 / P < (N : ℝ) := by exact_mod_cast hN
    have hPpos : 0 < P := Fact.out
    have hNpos : 0 < (N : ℝ) := lt_trans (by positivity) hNreal
    have hNP : (2 : ℝ) / (N : ℝ) < P := by
      apply (div_lt_iff₀ hNpos).2
      have hmul := (div_lt_iff₀ hPpos).1 hNreal
      nlinarith [hmul]
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (N : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hle : 2 / ((n : ℝ) + 1) ≤ 2 / (N : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hNpos hden
    exact hle.trans hNP.le
  have hzeroEventually : ∀ᶠ n : ℕ in atTop, ∫ z : SpaceTime,
      dotL ((phaseInteriorCutoff P n z.1) ^ 2 • F z) (G z) ∂μ = 0 :=
    hhn.mono fun n hn => hzero n hn
  have hconst : Tendsto (fun n : ℕ => ∫ z : SpaceTime,
      dotL ((phaseInteriorCutoff P n z.1) ^ 2 • F z) (G z) ∂μ) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hzeroEventually.mono fun n hn => hn.symm)
  have huniq := tendsto_nhds_unique hconst hPairLimit
  simpa [F, G, μ] using huniq.symm

#print axioms memLp_scalarSliceGrad_cell
#print axioms integral_scalarSliceGrad_pair_rep_zero

end UnforcedLeray.Cons.C03.Concrete
