import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellInletProduct
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

private theorem realC_eq_cplxV_inletOuter : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_inletOuter (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_inletOuter, UnforcedLeray.Axi.norm_cplxV]

/-- The phase-cutoff endpoint can be removed: the actual spatial gradient of `Φ·U` is
annihilated over the full period cell by a bounded, pointwise-solenoidal field. Only `L¹` for the
compactly supported gradient and `L∞` for the field are used. -/
theorem integral_scalarSliceGrad_pair_boundedSolenoidal_zero {P : ℝ}
    [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U V : ℝ → SpatialField} (hU : IsBoundedBackground U)
    (hV : IsBoundedBackground V) (hsol : ∀ τ, IsSolenoidal (V τ)) :
    ∫ z : SpaceTime, dotL (scalarSliceGrad (scalarTestBackground Φ U) z)
      (realC (V z.1 z.2)) ∂(volume.restrict (phaseCell P)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let G : SpaceTime → CVec3 := fun z => realC (V z.1 z.2)
  let F : SpaceTime → CVec3 := scalarSliceGrad (scalarTestBackground Φ U)
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hF : MemLp F 1 μ := memLp_scalarSliceGrad_cell hΦ hU (by simp)
  have hseq (n : ℕ) : MemLp
      (fun z : SpaceTime => (phaseInteriorCutoff P n z.1) ^ 2 • F z) 1 μ :=
    memLp_cutoffSquared_scalarSliceGrad_cell hΦ hU (by simp) n
  have hGmeas : AEStronglyMeasurable G μ := by
    have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hV.measurable
    have heq : (fun z : SpaceTime => UnforcedLeray.Axi.cplxV (V z.1 z.2)) = G := by
      funext z
      change UnforcedLeray.Axi.cplxV (V z.1 z.2) = realC (V z.1 z.2)
      exact congrFun realC_eq_cplxV_inletOuter.symm (V z.1 z.2)
    exact (hc.congr (ae_of_all _ fun z => congrFun heq z)).mono_measure
      Measure.restrict_le_self
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hGbound : ∀ᵐ z ∂μ, ‖G z‖ ≤ CV := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖realC (V z.1 z.2)‖ ≤ CV
    rw [norm_realC_inletOuter]
    exact (hCV z.1 z.2).1
  have hG : MemLp G ⊤ μ := memLp_top_of_bound hGmeas CV hGbound
  have hIntSeq (n : ℕ) : Integrable (fun z : SpaceTime => dotL
      ((phaseInteriorCutoff P n z.1) ^ 2 • F z) (G z)) μ :=
    integrable_dotL_of_memLp_holder (hseq n) hG
  have hIntF : Integrable (fun z : SpaceTime => dotL (F z) (G z)) μ :=
    integrable_dotL_of_memLp_holder hF hG
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
    (μ := μ) (p := (1 : ℝ≥0∞)) (by simp)
    (Filter.Eventually.of_forall hg) (Filter.Eventually.of_forall hB) hlim hF
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
        RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
      _ = g n z • F z := rfl
  have hconv : Tendsto (fun n : ℕ => eLpNorm
      ((fun z : SpaceTime => (phaseInteriorCutoff P n z.1) ^ 2 • F z) - F) 1 μ)
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_) hmult
    exact (congrArg (fun f : SpaceTime → CVec3 => eLpNorm f 1 μ) (herror n)).symm
  have hlimit := tendsto_integral_dotL_of_eLpNorm hF hG hseq hconv
  have hzero (n : ℕ) (hn : 2 / ((n : ℝ) + 1) ≤ P) :=
    integral_cutoffSquared_scalarSliceGrad_pair_boundedSolenoidal_zero
      hΦ hU hV hsol n hn
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
  have huniq := tendsto_nhds_unique hconst hlimit
  simpa [F, G, μ] using huniq.symm

#print axioms integral_scalarSliceGrad_pair_boundedSolenoidal_zero

end UnforcedLeray.Cons.C03.Concrete
