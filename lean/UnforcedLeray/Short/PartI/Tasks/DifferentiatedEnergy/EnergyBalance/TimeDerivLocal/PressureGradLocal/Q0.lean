import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_6
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.PressureGradOrder0

/-!
# Part I, task `PartI:T08/4/1/1/6/1` (`pressureGradOrder0Quant_proof`): quantitative order-0 bound

Source of record: `the November 2 reference manuscript`, lines 266-270, 326-329.
The Prop is `PressureGradOrder0Quant` in `Sub/PartI_T08_4_1_1_6.lean`.

Route. Same cutoff argument as `pressureGradOrder0_proof`, keeping the energy bound in the form
`E_R := ∫ χ_R |∇π|² ≤ 3 Q₀ + 32 c C₀² M² / R` (the strip term `(C₀M/R)² · c·4R` decays in `R`).
Fatou along `R = n + 1` (`q0_fatou`, the sequence version of `cutoffL2OfBound_proof`) then gives
`∫_cell |∇π|² ≤ 3 Q₀ ≤ 4 Q₀`, with `Q₀ = ∑_m ∫ F_m²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-- Fatou along the cutoffs `R = n + 1`: a nonnegative integrand whose truncated integrals are
bounded by `B n → Q` has cell integral at most `Q`. -/
theorem q0_fatou {c : ℝ} (hc : 0 < c) (g : Plane → ℝ) (hg : Continuous g)
    (hg0 : ∀ z, 0 ≤ g z) (B : ℕ → ℝ) (Q : ℝ) (hQ : 0 ≤ Q) (hB : Tendsto B atTop (𝓝 Q))
    (hint : ∀ n : ℕ, Integrable (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 * g z)
      (volume.restrict (Cyl.cell c)))
    (hbound : ∀ n : ℕ, ∫ z in Cyl.cell c, etaCutoff ((n : ℝ) + 1) z.2 * g z ≤ B n) :
    ∫ z in Cyl.cell c, g z ≤ Q := by
  have hnn : ∀ n : ℕ, 0 ≤ᵐ[volume.restrict (Cyl.cell c)]
      (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 * g z) := fun n =>
    Filter.Eventually.of_forall (fun z => mul_nonneg (etaCutoff_nonneg _ _) (hg0 z))
  have hlev : ∀ n : ℕ, ∫⁻ z in Cyl.cell c, ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * g z)
      ≤ ENNReal.ofReal (B n) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnn n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hlim : ∀ z : Plane, Tendsto
      (fun n : ℕ => ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * g z)) atTop
      (𝓝 (ENNReal.ofReal (g z))) := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_ge |z.2|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hab : |z.2| ≤ (n : ℝ) + 1 := by linarith
    rw [ecOne ((n : ℝ) + 1) hR z.2 hab, one_mul]
  have hmeas : ∀ n : ℕ, Measurable
      (fun z : Plane => ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * g z)) := fun n =>
    (((cehd_eta_cont _).mul hg).measurable).ennreal_ofReal
  have hfat := lintegral_liminf_le (μ := volume.restrict (Cyl.cell c)) (u := atTop) hmeas
  have hlhs : ∫⁻ a, liminf
      (fun n : ℕ => ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) a.2 * g a)) atTop
        ∂(volume.restrict (Cyl.cell c))
      = ∫⁻ a, ENNReal.ofReal (g a) ∂(volume.restrict (Cyl.cell c)) :=
    lintegral_congr (fun a => (hlim a).liminf_eq)
  have hrhs : liminf (fun n : ℕ => ∫⁻ a in Cyl.cell c,
      ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) a.2 * g a)) atTop ≤ ENNReal.ofReal Q := by
    calc liminf (fun n : ℕ => ∫⁻ a in Cyl.cell c,
          ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) a.2 * g a)) atTop
        ≤ liminf (fun n : ℕ => ENNReal.ofReal (B n)) atTop :=
          Filter.liminf_le_liminf (Eventually.of_forall hlev)
      _ = ENNReal.ofReal Q := (ENNReal.tendsto_ofReal hB).liminf_eq
  have key : ∫⁻ a, ENNReal.ofReal (g a) ∂(volume.restrict (Cyl.cell c)) ≤ ENNReal.ofReal Q :=
    le_trans (le_of_eq hlhs.symm) (hfat.trans hrhs)
  have hnn2 : 0 ≤ᵐ[volume.restrict (Cyl.cell c)] g :=
    Filter.Eventually.of_forall hg0
  rw [integral_eq_lintegral_of_nonneg_ae hnn2 hg.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hQ key

/-- Squared components of `gradS` sum to `|∇p|²`. -/
theorem q0_gradS_sq (p : Plane → ℝ) (z : Plane) :
    ∑ k : Fin 2, (Train.gradS p z k) ^ 2 = partialQ p z ^ 2 + partialEta p z ^ 2 := by
  simp [Fin.sum_univ_two, Train.gradS, Train.toVec_apply_eq_vcomp, B0146.vcomp]

/-- **`PressureGradOrder0Quant`** (quantitative order-0 bound, constant `4`). -/
theorem pressureGradOrder0Quant_proof : UnforcedLeray.Short.PartI.PressureGradOrder0Quant := by
  intro c hc π F hπ hper hbd hF hFper hlap
  obtain ⟨M, hM⟩ := hbd
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hηF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hηF
  obtain ⟨C₀, hC₀, hcut⟩ := hηF
  have hFs : ContDiff ℝ ∞ F := hF.1
  have hF0s : ContDiff ℝ ∞ (fun w => F w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hFs
  have hF1s : ContDiff ℝ ∞ (fun w => F w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hFs
  have hF0p : Cyl.IsPeriodic c (fun w => F w 0) := fun z => by
    show F (z.1 + c, z.2) 0 = F z 0
    rw [hFper z]
  have hF1p : Cyl.IsPeriodic c (fun w => F w 1) := fun z => by
    show F (z.1 + c, z.2) 1 = F z 1
    rw [hFper z]
  have hF0L : MemLp (fun w => F w 0) 2 (Cyl.cellμ c) := hF.2 [] 0
  have hF1L : MemLp (fun w => F w 1) 2 (Cyl.cellμ c) := hF.2 [] 1
  have hF0I : Integrable (fun w : Plane => F w 0 ^ 2) (Cyl.cellμ c) :=
    (memLp_two_iff_integrable_sq hF0L.aestronglyMeasurable).1 hF0L
  have hF1I : Integrable (fun w : Plane => F w 1 ^ 2) (Cyl.cellμ c) :=
    (memLp_two_iff_integrable_sq hF1L.aestronglyMeasurable).1 hF1L
  obtain ⟨Q0, hQ0⟩ : ∃ Q0 : ℝ, Q0 = ∫ z in Cyl.cell c, (F z 0 ^ 2 + F z 1 ^ 2) := ⟨_, rfl⟩
  have hFsq : Integrable (fun z : Plane => F z 0 ^ 2 + F z 1 ^ 2) (Cyl.cellμ c) :=
    hF0I.add hF1I
  have hQ0nn : 0 ≤ Q0 := by
    rw [hQ0]
    exact integral_nonneg (fun z => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hF0R : Integrable (fun w : Plane => F w 0 ^ 2) (volume.restrict (Cyl.cell c)) := hF0I
  have hF1R : Integrable (fun w : Plane => F w 1 ^ 2) (volume.restrict (Cyl.cell c)) := hF1I
  have hRHS : ∑ m : Fin 2, ∫ z in Cyl.cell c, (F z m) ^ 2 = Q0 := by
    rw [hQ0, integral_add hF0R hF1R, Fin.sum_univ_two]
  have hLp : ∀ z : Plane, partialQ (partialQ π) z + partialEta (partialEta π) z
      = -(partialQ (fun w => F w 0) z + partialEta (fun w => F w 1) z) := by
    intro z
    have := hlap z
    simp only [Train.lapS] at this
    linarith
  have hqπc : Continuous (partialQ π) := (vi_partialQ_contDiff hπ).continuous
  have hηπc : Continuous (partialEta π) := (vi_partialEta_contDiff hπ).continuous
  have hqF0c : Continuous (partialQ (fun w => F w 0)) :=
    (vi_partialQ_contDiff hF0s).continuous
  have hηF1c : Continuous (partialEta (fun w => F w 1)) :=
    (vi_partialEta_contDiff hF1s).continuous
  have hπc : Continuous π := hπ.continuous
  have hF0c : Continuous (fun w : Plane => F w 0) := hF0s.continuous
  have hF1c : Continuous (fun w : Plane => F w 1) := hF1s.continuous
  have hmain : ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2) ≤
        3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2 * (1 / R) := by
    intro R hR1
    have hR0 : 0 < R := by linarith
    obtain ⟨hsm, hφ01, -, hφz, hφd⟩ := hcut R hR1
    have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
      intro η hη
      have h0 := hφd η
      rw [hφz η hη, Real.sqrt_zero, mul_zero] at h0
      exact abs_nonpos_iff.mp h0
    have hχc : Continuous (fun z : Plane => etaCutoff R z.2) :=
      hsm.continuous.comp continuous_snd
    have hχ'c : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
      (hsm.continuous_deriv (by simp)).comp continuous_snd
    have hI : ∀ g : Plane → ℝ, Continuous g → (∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) →
        IntegrableOn g (Cyl.cell c) :=
      fun g hg hz => cellIntegrable_of_support c R hc hR0 g hg hz
    obtain ⟨Ivi1, Ivi2, Ivi3, Evi⟩ := vi_scalar hc hR0 cellIntegrable_of_support
      cellDerivZero_of_periodic hsm hφz hdzero π hπ hper
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∫ z in Cyl.cell c,
        etaCutoff R z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2) := ⟨_, rfl⟩
    rw [← hE] at Evi
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ z in Cyl.cell c,
        etaCutoff R z.2 * (partialQ π z * F z 0 + partialEta π z * F z 1) := ⟨_, rfl⟩
    obtain ⟨T2, hT2⟩ : ∃ T2 : ℝ, T2 = ∫ z in Cyl.cell c,
        deriv (etaCutoff R) z.2 * (π z * F z 1) := ⟨_, rfl⟩
    obtain ⟨T1, hT1⟩ : ∃ T1 : ℝ, T1 = ∫ z in Cyl.cell c,
        deriv (etaCutoff R) z.2 * (π z * partialEta π z) := ⟨_, rfl⟩
    have hIBQ : ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (partialQ π z * F z 0 + π z * partialQ (fun w => F w 0) z) = 0 :=
      pg0_ibp_q hc hR0 hφz π (fun w => F w 0) hπ hF0s hper hF0p
    have hIBE : ∫ z in Cyl.cell c, (deriv (etaCutoff R) z.2 * (π z * F z 1) +
        etaCutoff R z.2 * (π z * partialEta (fun w => F w 1) z + partialEta π z * F z 1)) = 0 :=
      pg0_ibp_e hc hR0 hφz π (fun w => F w 1) hπ hF1s hper hF1p
    have hYi : IntegrableOn (fun z : Plane => etaCutoff R z.2 *
        (partialQ π z * F z 0 + partialEta π z * F z 1)) (Cyl.cell c) :=
      hI _ (hχc.mul ((hqπc.mul hF0c).add (hηπc.mul hF1c))) (fun z hz => by simp [hφz z.2 hz])
    have hWi : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (π z * F z 1))
        (Cyl.cell c) :=
      hI _ (hχ'c.mul (hπc.mul hF1c)) (fun z hz => by simp [hdzero z.2 hz])
    have hIqi : IntegrableOn (fun z : Plane => etaCutoff R z.2 *
        (partialQ π z * F z 0 + π z * partialQ (fun w => F w 0) z)) (Cyl.cell c) :=
      hI _ (hχc.mul ((hqπc.mul hF0c).add (hπc.mul hqF0c))) (fun z hz => by simp [hφz z.2 hz])
    have hIei : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (π z * F z 1) +
        etaCutoff R z.2 * (π z * partialEta (fun w => F w 1) z + partialEta π z * F z 1))
        (Cyl.cell c) :=
      hI _ ((hχ'c.mul (hπc.mul hF1c)).add (hχc.mul ((hπc.mul hηF1c).add (hηπc.mul hF1c))))
        (fun z hz => by simp [hφz z.2 hz, hdzero z.2 hz])
    have hpt1 : ∀ z : Plane,
        etaCutoff R z.2 * (π z * (partialQ (partialQ π) z + partialEta (partialEta π) z))
        = ((etaCutoff R z.2 * (partialQ π z * F z 0 + partialEta π z * F z 1)
            + deriv (etaCutoff R) z.2 * (π z * F z 1))
          - etaCutoff R z.2 * (partialQ π z * F z 0 + π z * partialQ (fun w => F w 0) z))
          - (deriv (etaCutoff R) z.2 * (π z * F z 1) +
            etaCutoff R z.2 * (π z * partialEta (fun w => F w 1) z + partialEta π z * F z 1)) := by
      intro z
      rw [hLp z]
      ring
    have hdec0 : ∫ z in Cyl.cell c,
        etaCutoff R z.2 * (π z * (partialQ (partialQ π) z + partialEta (partialEta π) z))
        = ∫ z in Cyl.cell c, (((etaCutoff R z.2 * (partialQ π z * F z 0 + partialEta π z * F z 1)
            + deriv (etaCutoff R) z.2 * (π z * F z 1))
          - etaCutoff R z.2 * (partialQ π z * F z 0 + π z * partialQ (fun w => F w 0) z))
          - (deriv (etaCutoff R) z.2 * (π z * F z 1) +
            etaCutoff R z.2 * (π z * partialEta (fun w => F w 1) z + partialEta π z * F z 1))) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt1)
    have hdec : ∫ z in Cyl.cell c,
        etaCutoff R z.2 * (π z * (partialQ (partialQ π) z + partialEta (partialEta π) z))
        = A + T2 := by
      have hI1 : IntegrableOn (fun z : Plane => etaCutoff R z.2 *
          (partialQ π z * F z 0 + partialEta π z * F z 1) +
          deriv (etaCutoff R) z.2 * (π z * F z 1)) (Cyl.cell c) := hYi.add hWi
      have hI2 : IntegrableOn (fun z : Plane => etaCutoff R z.2 *
          (partialQ π z * F z 0 + partialEta π z * F z 1) +
          deriv (etaCutoff R) z.2 * (π z * F z 1) -
          etaCutoff R z.2 * (partialQ π z * F z 0 + π z * partialQ (fun w => F w 0) z))
          (Cyl.cell c) := hI1.sub hIqi
      rw [hdec0, integral_sub hI2 hIei, integral_sub hI1 hIqi, integral_add hYi hWi,
        hIBQ, hIBE, hA, hT2]
      ring
    have hEA : E = -A - T2 - T1 := by linarith [Evi, hdec, hT1]
    -- bound on `-A`
    have hr_int : IntegrableOn (fun z : Plane => (1 / 2) *
        (etaCutoff R z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2)) +
        (1 / 2) * (F z 0 ^ 2 + F z 1 ^ 2)) (Cyl.cell c) :=
      (Integrable.const_mul Ivi2 (1 / 2)).add (Integrable.const_mul hFsq (1 / 2))
    have hb1pt : ∀ z : Plane,
        -(etaCutoff R z.2 * (partialQ π z * F z 0 + partialEta π z * F z 1)) ≤
        (1 / 2) * (etaCutoff R z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2)) +
        (1 / 2) * (F z 0 ^ 2 + F z 1 ^ 2) := by
      intro z
      have h0 := (hφ01 z.2).1
      have h1 := (hφ01 z.2).2
      nlinarith [mul_nonneg h0 (sq_nonneg (partialQ π z + F z 0)),
        mul_nonneg h0 (sq_nonneg (partialEta π z + F z 1)),
        mul_nonneg (sub_nonneg.2 h1) (add_nonneg (sq_nonneg (F z 0)) (sq_nonneg (F z 1)))]
    have hb1 : ∫ z in Cyl.cell c, -(etaCutoff R z.2 *
        (partialQ π z * F z 0 + partialEta π z * F z 1)) ≤
        ∫ z in Cyl.cell c, ((1 / 2) *
        (etaCutoff R z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2)) +
        (1 / 2) * (F z 0 ^ 2 + F z 1 ^ 2)) :=
      integral_mono (Integrable.neg hYi) hr_int hb1pt
    have hrv : ∫ z in Cyl.cell c, ((1 / 2) *
        (etaCutoff R z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2)) +
        (1 / 2) * (F z 0 ^ 2 + F z 1 ^ 2)) = (1 / 2) * E + (1 / 2) * Q0 := by
      rw [integral_add (Integrable.const_mul Ivi2 (1 / 2)) (Integrable.const_mul hFsq (1 / 2)),
        integral_const_mul, integral_const_mul, hE, hQ0]
    have hnegA : ∫ z in Cyl.cell c, -(etaCutoff R z.2 *
        (partialQ π z * F z 0 + partialEta π z * F z 1)) = -A := by
      rw [integral_neg, hA]
    -- bound on the cross term `T2`
    have hχF1 : ∫ z in Cyl.cell c, etaCutoff R z.2 * F z 1 ^ 2 ≤ Q0 := by
      rw [hQ0]
      refine integral_mono (hI _ (hχc.mul (hF1c.pow 2)) (fun z hz => by simp [hφz z.2 hz]))
        hFsq (fun z => ?_)
      have h1 := mul_le_of_le_one_left (sq_nonneg (F z 1)) (hφ01 z.2).2
      nlinarith [sq_nonneg (F z 0)]
    have hb2 : -T2 ≤ (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * F z 1 ^ 2) +
        (C₀ * M / R) ^ 2 * (c * (4 * R)) := by
      rw [hT2]
      exact pg0_cross_int hc hR0 hC₀ hMnn (fun η => (hφ01 η).1) hφd hdzero π (fun z => F z 1)
        hM hWi (hI _ (hχc.mul (hF1c.pow 2)) (fun z hz => by simp [hφz z.2 hz]))
    -- bound on the cross term `T1`
    have hb3 : -T1 ≤ (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta π z ^ 2) +
        (C₀ * M / R) ^ 2 * (c * (4 * R)) := by
      rw [hT1]
      exact pg0_cross_int hc hR0 hC₀ hMnn (fun η => (hφ01 η).1) hφd hdzero π (partialEta π)
        hM Ivi3 (hI _ (hχc.mul (hηπc.pow 2)) (fun z hz => by simp [hφz z.2 hz]))
    have hb3' : ∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta π z ^ 2 ≤ E := by
      rw [hE]
      exact integral_mono (hI _ (hχc.mul (hηπc.pow 2)) (fun z hz => by simp [hφz z.2 hz]))
        Ivi2 (fun z => mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (sq_nonneg (partialQ π z))) (hφ01 z.2).1)
    -- the strip constant decays like `1 / R`
    have hK : (C₀ * M / R) ^ 2 * (c * (4 * R)) = 4 * c * C₀ ^ 2 * M ^ 2 * (1 / R) := by
      have hRne : R ≠ 0 := hR0.ne'
      field_simp
    have hb1': -A ≤ (1 / 2) * E + (1 / 2) * Q0 := by
      have h := hb1
      rw [hnegA, hrv] at h
      exact h
    have hEB : E ≤ 3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2 * (1 / R) := by
      linarith [hEA, hb1', hb2, hb3, hb3', hχF1, hK]
    rw [← hE]
    exact hEB
  -- Fatou along `R = n + 1`
  have hBt : Tendsto (fun n : ℕ => 3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2 * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (3 * Q0)) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (32 * c * C₀ ^ 2 * M ^ 2)).const_add (3 * Q0)
    simpa using this
  have hcellint : ∀ n : ℕ, Integrable
      (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 *
        (partialQ π z ^ 2 + partialEta π z ^ 2)) (volume.restrict (Cyl.cell c)) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨hsm, -, -, hφz, -⟩ := hcut ((n : ℝ) + 1) (by linarith)
    have hχc : Continuous (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2) :=
      hsm.continuous.comp continuous_snd
    exact cellIntegrable_of_support c _ hc hR0 _
      (hχc.mul ((hqπc.pow 2).add (hηπc.pow 2)))
      (fun z hz => by simp [hφz z.2 hz])
  have hbound : ∀ n : ℕ, ∫ z in Cyl.cell c,
      etaCutoff ((n : ℝ) + 1) z.2 * (partialQ π z ^ 2 + partialEta π z ^ 2) ≤
        3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact hmain ((n : ℝ) + 1) (by linarith)
  have hgnn : ∀ z : Plane, 0 ≤ partialQ π z ^ 2 + partialEta π z ^ 2 :=
    fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfin := q0_fatou hc (fun z : Plane => partialQ π z ^ 2 + partialEta π z ^ 2)
    ((hqπc.pow 2).add (hηπc.pow 2)) hgnn _ (3 * Q0) (by linarith) hBt hcellint hbound
  have hLHS : ∫ z in Cyl.cell c, ∑ k : Fin 2, (Train.gradS π z k) ^ 2
      = ∫ z in Cyl.cell c, (partialQ π z ^ 2 + partialEta π z ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => q0_gradS_sq π z))
  rw [hLHS, hRHS]
  linarith [hfin, hQ0nn]

end UnforcedLeray.Short.PartI
