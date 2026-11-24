import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, task `PartI:T08/2/2/2/5`: `CutoffJetViscousBound`

Source of record: `the November 2 reference manuscript`, lines 286-287.
Target: `cutoffJetViscousBound_proof : CutoffJetViscousBound` (`Sub/PartI_T08_2_2/EnergyIneq.lean`).

Route. For one word `g = ∂_u h` (smooth, `c`-periodic, `|g| ≤ M`, `|∂_η g| ≤ M`), the scalar
viscous identity `vi_scalar` gives `∫ φ g Δg = -∫ φ|∇g|² - ∫ φ' g ∂_η g`, so
`∫ φ (2 g Δg) ≤ -2 ∫ φ' g ∂_η g`. Pointwise `|φ'| ≤ C₀/R` and `φ' = 0` for `2R ≤ |η|`, so the
integrand `-2 φ' g ∂_η g` is dominated by `(2C₀M²/R)` on the box `[-c/2,c/2] × [-2R,2R]`, whose
measure is `c · 4R`. The per-word bound is therefore `8 C₀ c M²`, independent of `R`. Summing over
the finitely many words `u` with `|u| ≤ j` gives `K = #wordsUpTo j · 8 C₀ c M²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Per-word estimate: for one smooth `c`-periodic `g` with `|g| ≤ M`, `|∂_η g| ≤ M`, the
cell integral of `φ_R (2 g Δg)` is at most `8 C₀ c M²`, uniformly in `R > 0`. -/
theorem cjvb_word_bound {C₀ c R M : ℝ} (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hR : 0 < R) (hM : 0 ≤ M)
    (hsm : ContDiff ℝ ∞ (etaCutoff R))
    (hφ01 : ∀ η : ℝ, 0 ≤ etaCutoff R η ∧ etaCutoff R η ≤ 1)
    (hzero : ∀ η : ℝ, 2 * R ≤ |η| → etaCutoff R η = 0)
    (hder : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R * Real.sqrt (etaCutoff R η))
    (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) (hper : Cyl.IsPeriodic c g)
    (hgM : ∀ z : Plane, |g z| ≤ M) (hgeM : ∀ z : Plane, |Cyl.partialEta g z| ≤ M) :
    ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * Train.lapS g z) ≤ 8 * C₀ * c * M ^ 2 := by
  have hR' : R ≠ 0 := hR.ne'
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h := hder η
    rw [hzero η hη, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  have hdbound : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R := by
    intro η
    have hs1 : Real.sqrt (etaCutoff R η) ≤ 1 := Real.sqrt_le_one.mpr (hφ01 η).2
    exact (hder η).trans (mul_le_of_le_one_right (div_nonneg hC₀ hR.le) hs1)
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) := hsm.continuous.comp continuous_snd
  have hdc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hsm.continuous_deriv (by simp)).comp continuous_snd
  have hgc : Continuous g := hg.continuous
  have hgeC : Continuous (Cyl.partialEta g) := (vi_partialEta_contDiff hg).continuous
  have hlapC : Continuous (Train.lapS g) := (vjl_lapS_contDiff hg).continuous
  -- scalar viscous identity
  obtain ⟨-, -, -, hE⟩ := vi_scalar hc hR cellIntegrable_of_support cellDerivZero_of_periodic
    hsm hzero hdzero g hg hper
  -- the integrand of the statement is `2 φ g Δg`
  have hTeq : ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * Train.lapS g z) =
      2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (g z * (Cyl.partialQ (Cyl.partialQ g) z + Cyl.partialEta (Cyl.partialEta g) z)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    unfold Train.lapS
    ring
  have hI2 : 0 ≤ ∫ z in Cyl.cell c,
      etaCutoff R z.2 * (Cyl.partialQ g z ^ 2 + Cyl.partialEta g z ^ 2) :=
    setIntegral_nonneg (Cyl.measurableSet_cell c)
      (fun z _ => mul_nonneg (hφ01 z.2).1 (by positivity))
  -- the boundary term `F = -2 φ' g ∂_η g`
  have hFc : Continuous (fun z : Plane =>
      (-2 : ℝ) * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z))) :=
    continuous_const.mul (hdc.mul (hgc.mul hgeC))
  have hFz : ∀ z : Plane, 2 * R ≤ |z.2| →
      (-2 : ℝ) * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)) = 0 := by
    intro z hz
    rw [hdzero z.2 hz]
    simp
  have hFint := cellIntegrable_of_support c R hc hR _ hFc hFz
  have hFeq : ∫ z in Cyl.cell c, (-2 : ℝ) * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z))
      = -2 * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z) :=
    integral_const_mul _ _
  -- the box `S` carrying the pointwise bound
  set S : Set Plane := Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hSdef
  have hS_meas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hS_fin : volume S ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hpt : ∀ z ∈ Cyl.cell c,
      (-2 : ℝ) * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)) ≤
        S.indicator (fun _ => 2 * C₀ * M ^ 2 / R) z := by
    intro z hz
    by_cases hSz : z ∈ S
    · rw [Set.indicator_of_mem hSz]
      have h1 : |deriv (etaCutoff R) z.2| ≤ C₀ / R := hdbound z.2
      have h2 : |g z * Cyl.partialEta g z| ≤ M * M := by
        rw [abs_mul]
        exact mul_le_mul (hgM z) (hgeM z) (abs_nonneg _) hM
      have h3 : |deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)| ≤ C₀ / R * (M * M) := by
        rw [abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) (div_nonneg hC₀ hR.le)
      have h4 := neg_abs_le (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z))
      have h5 : 2 * C₀ * M ^ 2 / R = 2 * (C₀ / R * (M * M)) := by ring
      rw [h5]
      linarith
    · rw [Set.indicator_of_notMem hSz]
      have hη : 2 * R ≤ |z.2| := by
        by_contra hlt
        push Not at hlt
        have hz1 := Cyl.mem_cell.mp hz
        apply hSz
        exact ⟨⟨hz1.1, hz1.2.le⟩, ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩⟩
      rw [hdzero z.2 hη]
      simp
  have hInd_int : IntegrableOn (S.indicator (fun _ : Plane => 2 * C₀ * M ^ 2 / R))
      (Cyl.cell c) :=
    ((integrable_indicator_iff hS_meas).2 (integrableOn_const hS_fin)).integrableOn
  have hF_le : ∫ z in Cyl.cell c,
      (-2 : ℝ) * (deriv (etaCutoff R) z.2 * (g z * Cyl.partialEta g z)) ≤
      ∫ z in Cyl.cell c, S.indicator (fun _ : Plane => 2 * C₀ * M ^ 2 / R) z :=
    setIntegral_mono_on hFint hInd_int (Cyl.measurableSet_cell c) hpt
  have hInd_all : Integrable (S.indicator (fun _ : Plane => 2 * C₀ * M ^ 2 / R)) :=
    (integrable_indicator_iff hS_meas).2 (integrableOn_const hS_fin)
  have hB0 : 0 ≤ 2 * C₀ * M ^ 2 / R :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) (sq_nonneg M)) hR.le
  have hind_le : ∫ z in Cyl.cell c, S.indicator (fun _ : Plane => 2 * C₀ * M ^ 2 / R) z ≤
      ∫ z, S.indicator (fun _ : Plane => 2 * C₀ * M ^ 2 / R) z :=
    setIntegral_le_integral hInd_all
      (Filter.Eventually.of_forall (fun z => Set.indicator_nonneg (fun _ _ => hB0) z))
  have hind_eq : ∫ z, S.indicator (fun _ : Plane => 2 * C₀ * M ^ 2 / R) z = 8 * C₀ * c * M ^ 2 := by
    rw [integral_indicator hS_meas, setIntegral_const, smul_eq_mul]
    have hvol : volume S = ENNReal.ofReal (c / 2 - -c / 2) * ENNReal.ofReal (2 * R - -(2 * R)) := by
      rw [hSdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    rw [Measure.real, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
    have hRR : (c / 2 - -c / 2) * (2 * R - -(2 * R)) * (2 * C₀ * M ^ 2 / R) =
        (c / 2 - -c / 2) * (2 * R - -(2 * R)) * (2 * C₀ * M ^ 2) / R := by ring
    rw [hRR, div_eq_iff hR']
    ring
  rw [hTeq]
  linarith [hE, hI2, hFeq, hF_le, hind_le, hind_eq]

/-- **Target `CutoffJetViscousBound`.** -/
theorem cutoffJetViscousBound_proof : CutoffJetViscousBound := by
  intro j c M hc
  have hcutF : EtaCutoffFacts := etaCutoffFacts
  obtain ⟨C₀, hC₀, hcut⟩ := hcutF
  refine ⟨((wordsUpTo j).card : ℝ) * (8 * C₀ * c * M ^ 2), ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) hc.le) (sq_nonneg M))
  intro R hR h hsmooth hper hbound
  have hR0 : 0 < R := by linarith
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound [] (by simp) 0)
  obtain ⟨hsm, hφ01, -, hzero, hder⟩ := hcut R hR
  have hword : ∀ u ∈ wordsUpTo j,
      ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * B0151.derivWord u h z *
        Train.lapS (B0151.derivWord u h) z) ≤ 8 * C₀ * c * M ^ 2 := by
    intro u hu
    have hlen : u.length ≤ j := mem_wordsUpTo.mp hu
    have hgs : ContDiff ℝ ∞ (B0151.derivWord u h) := B0151.contDiff_derivWord hsmooth u
    have hgp : Cyl.IsPeriodic c (B0151.derivWord u h) := by
      have hp : B0151.IsPeriodicQ c h := fun q η => hper (q, η)
      intro z
      exact B0151.periodic_derivWord hp u z.1 z.2
    have hgM : ∀ z : Plane, |B0151.derivWord u h z| ≤ M := fun z => hbound u (by omega) z
    have hgeM : ∀ z : Plane, |Cyl.partialEta (B0151.derivWord u h) z| ≤ M := fun z => by
      have := hbound (false :: u) (by simp only [List.length_cons]; omega) z
      exact this
    exact cjvb_word_bound hC₀ hc hR0 hM hsm hφ01 hzero hder _ hgs hgp hgM hgeM
  have hint : ∀ u ∈ wordsUpTo j, IntegrableOn (fun z : Plane => etaCutoff R z.2 *
      (2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z)) (Cyl.cell c) := by
    intro u _hu
    have hgc : Continuous (B0151.derivWord u h) :=
      (B0151.contDiff_derivWord hsmooth u).continuous
    have hlc : Continuous (Train.lapS (B0151.derivWord u h)) :=
      (vjl_lapS_contDiff (B0151.contDiff_derivWord hsmooth u)).continuous
    have hφc : Continuous (fun z : Plane => etaCutoff R z.2) := hsm.continuous.comp continuous_snd
    have hcont : Continuous (fun z : Plane => etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z)) :=
      hφc.mul ((continuous_const.mul hgc).mul hlc)
    refine cellIntegrable_of_support c R hc hR0 _ hcont (fun z hz => ?_)
    simp only [hzero z.2 hz, zero_mul]
  have hsum : ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
      2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z =
      ∑ u ∈ wordsUpTo j, ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z) := by
    rw [← integral_finsetSum _ hint]
    congr 1
    funext z
    rw [Finset.mul_sum]
  rw [hsum]
  refine (Finset.sum_le_sum hword).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

end UnforcedLeray.Short.PartI
