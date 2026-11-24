import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3_1
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.CutoffL2OfBound

/-!
# Part I, task `PartI:T08/3/3/1/1` (`pressureGradOrder0_proof`): order-0 pressure gradient in L²

Source of record: `the November 2 reference manuscript`, lines 326-336 and 261-288.
The Prop is `PressureGradOrder0` in `Sub/PartI_T08_3_3_1.lean`.

Route. With `χ = etaCutoff R` (`R ≥ 1`), the scalar viscous identity `vi_scalar` for `f = π` gives
`E := ∫ χ |∇π|² = -∫ χ π Δπ - ∫ χ' π ∂_η π`. Replacing `Δπ = -(∂_q F₀ + ∂_η F₁)` and integrating by
parts on the cell (`CellDerivZero`) gives `E = -∫ χ(∂_qπ F₀ + ∂_ηπ F₁) - ∫ χ' π F₁ - ∫ χ' π ∂_ηπ`.
The first term is bounded by `E/2 + Q₀/2` (`Q₀ = ∫ |F|²`). The two cross terms live on the strip
`Q = [-c/2, c/2) × [-2R, 2R]` (where `χ' ≠ 0`), and there `|χ' π u| ≤ χ u²/4 + (C₀M/R)²`, so they
are bounded by `E/4 + K` and `Q₀/4 + K`, with `K |Q| ≤ 4 c C₀² M²`. Hence `E ≤ 3Q₀ + 32 c C₀² M²`
uniformly in `R`, and `cutoffL2OfBound_proof` finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-- Algebra for the cross terms: `-(d p u) ≤ χ u²/4 + (C M/R)²` when `|d| ≤ (C/R)√χ`, `|p| ≤ M`. -/
theorem pg0_cross_alg (χ d p u C M R : ℝ) (hχ0 : 0 ≤ χ) (hR : 0 < R) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hd : |d| ≤ C / R * Real.sqrt χ) (hp : |p| ≤ M) :
    -(d * (p * u)) ≤ (1 / 4) * (χ * u ^ 2) + (C * M / R) ^ 2 := by
  have hs : 0 ≤ Real.sqrt χ := Real.sqrt_nonneg χ
  have hsq : Real.sqrt χ ^ 2 = χ := Real.sq_sqrt hχ0
  have h1 : |d * (p * u)| ≤ (C * M / R) * (Real.sqrt χ * |u|) := by
    rw [abs_mul, abs_mul]
    calc |d| * (|p| * |u|) ≤ (C / R * Real.sqrt χ) * (M * |u|) :=
          mul_le_mul hd (mul_le_mul hp le_rfl (abs_nonneg _) hM)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (div_nonneg hC hR.le) hs)
      _ = (C * M / R) * (Real.sqrt χ * |u|) := by ring
  have h2 : (C * M / R) * (Real.sqrt χ * |u|) ≤
      (Real.sqrt χ * |u|) ^ 2 / 4 + (C * M / R) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt χ * |u| / 2 - C * M / R)]
  have h3 : (Real.sqrt χ * |u|) ^ 2 = χ * u ^ 2 := by
    rw [mul_pow, hsq, sq_abs]
  have h4 := neg_le_abs (d * (p * u))
  linarith [h1, h2, h3, h4]

/-- Cell integration by parts in `q` for a product of the transverse cutoff with `f g`. -/
theorem pg0_ibp_q {c R : ℝ} (hc : 0 < c) (hR0 : 0 < R)
    (hzero : ∀ η : ℝ, 2 * R ≤ |η| → etaCutoff R η = 0)
    (f g : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Cyl.IsPeriodic c f) (hgp : Cyl.IsPeriodic c g) :
    ∫ z in Cyl.cell c, etaCutoff R z.2 * (partialQ f z * g z + f z * partialQ g z) = 0 := by
  have hsm : ContDiff ℝ ∞ (etaCutoff R) := ecContDiff R hR0
  have hχd : Differentiable ℝ (fun w : Plane => etaCutoff R w.2) :=
    (hsm.differentiable (by simp)).comp differentiable_snd
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hfgd : Differentiable ℝ (fun w => f w * g w) := hfd.mul hgd
  have hG : ContDiff ℝ 1 (fun z : Plane => etaCutoff R z.2 * (f z * g z)) :=
    ((hsm.comp contDiff_snd).mul (hf.mul hg)).of_le (by simp)
  have hGp : Cyl.IsPeriodic c (fun z : Plane => etaCutoff R z.2 * (f z * g z)) := by
    intro z
    show etaCutoff R z.2 * (f (z.1 + c, z.2) * g (z.1 + c, z.2)) = etaCutoff R z.2 * (f z * g z)
    rw [hfp z, hgp z]
  have hGz : ∀ z : Plane, 2 * R ≤ |z.2| →
      (fun z : Plane => etaCutoff R z.2 * (f z * g z)) z = 0 := by
    intro z hz
    show etaCutoff R z.2 * (f z * g z) = 0
    rw [hzero z.2 hz, zero_mul]
  have hZ := (cellDerivZero_of_periodic c R hc hR0 _ hG hGp hGz).1
  have hpt : ∀ z : Plane, partialQ (fun z : Plane => etaCutoff R z.2 * (f z * g z)) z
      = etaCutoff R z.2 * (partialQ f z * g z + f z * partialQ g z) := by
    intro z
    rw [vi_partialQ_mul hχd hfgd z, vi_partialQ_cutoff, vi_partialQ_mul hfd hgd z]
    ring
  simp only [hpt] at hZ
  exact hZ

/-- Cell integration by parts in `η` for a product of the transverse cutoff with `f g`. -/
theorem pg0_ibp_e {c R : ℝ} (hc : 0 < c) (hR0 : 0 < R)
    (hzero : ∀ η : ℝ, 2 * R ≤ |η| → etaCutoff R η = 0)
    (f g : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Cyl.IsPeriodic c f) (hgp : Cyl.IsPeriodic c g) :
    ∫ z in Cyl.cell c, (deriv (etaCutoff R) z.2 * (f z * g z) +
      etaCutoff R z.2 * (f z * partialEta g z + partialEta f z * g z)) = 0 := by
  have hsm : ContDiff ℝ ∞ (etaCutoff R) := ecContDiff R hR0
  have hχd : Differentiable ℝ (fun w : Plane => etaCutoff R w.2) :=
    (hsm.differentiable (by simp)).comp differentiable_snd
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hfgd : Differentiable ℝ (fun w => f w * g w) := hfd.mul hgd
  have hG : ContDiff ℝ 1 (fun z : Plane => etaCutoff R z.2 * (f z * g z)) :=
    ((hsm.comp contDiff_snd).mul (hf.mul hg)).of_le (by simp)
  have hGp : Cyl.IsPeriodic c (fun z : Plane => etaCutoff R z.2 * (f z * g z)) := by
    intro z
    show etaCutoff R z.2 * (f (z.1 + c, z.2) * g (z.1 + c, z.2)) = etaCutoff R z.2 * (f z * g z)
    rw [hfp z, hgp z]
  have hGz : ∀ z : Plane, 2 * R ≤ |z.2| →
      (fun z : Plane => etaCutoff R z.2 * (f z * g z)) z = 0 := by
    intro z hz
    show etaCutoff R z.2 * (f z * g z) = 0
    rw [hzero z.2 hz, zero_mul]
  have hZ := (cellDerivZero_of_periodic c R hc hR0 _ hG hGp hGz).2
  have hpt : ∀ z : Plane, partialEta (fun z : Plane => etaCutoff R z.2 * (f z * g z)) z
      = deriv (etaCutoff R) z.2 * (f z * g z) +
        etaCutoff R z.2 * (f z * partialEta g z + partialEta f z * g z) := by
    intro z
    rw [vi_partialEta_mul hχd hfgd z, vi_partialEta_cutoff, vi_partialEta_mul hfd hgd z]
    ring
  simp only [hpt] at hZ
  exact hZ

/-- The strip `Q = [-c/2, c/2) × [-2R, 2R]` on which the transverse cutoff derivative lives. -/
def pg0Q (c R : ℝ) : Set Plane := Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)

theorem pg0Q_sub (c R : ℝ) : pg0Q c R ⊆ Cyl.cell c := by
  intro x hx
  unfold pg0Q at hx
  exact ⟨hx.1, Set.mem_univ _⟩

theorem pg0Q_meas (c R : ℝ) : MeasurableSet (pg0Q c R) := by
  unfold pg0Q
  exact measurableSet_Ico.prod measurableSet_Icc

theorem pg0Q_fin (c R : ℝ) : (volume : Measure Plane) (pg0Q c R) ≠ ⊤ := by
  unfold pg0Q
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem pg0Q_vol {c R : ℝ} (hc : 0 < c) (hR0 : 0 < R) :
    ((volume : Measure Plane) (pg0Q c R)).toReal = c * (4 * R) := by
  unfold pg0Q
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · ring
  all_goals linarith

/-- A function vanishing for `2R ≤ |η|` has the same cell integral as its restriction to `pg0Q`. -/
theorem pg0_cell_eq_Q {c R : ℝ} (g : Plane → ℝ) (hg : ∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) :
    ∫ z in Cyl.cell c, g z = ∫ z in pg0Q c R, g z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Cyl.measurableSet_cell c)
  · exact pg0Q_sub c R
  · intro x hx
    apply hg
    by_contra hlt
    rw [not_le] at hlt
    apply hx.2
    unfold pg0Q
    exact ⟨hx.1.1, abs_le.1 hlt.le⟩

theorem pg0_Q_le {c R : ℝ} (g : Plane → ℝ) (hg : IntegrableOn g (Cyl.cell c))
    (h0 : ∀ z, 0 ≤ g z) : ∫ z in pg0Q c R, g z ≤ ∫ z in Cyl.cell c, g z :=
  setIntegral_mono_set hg (Filter.Eventually.of_forall (fun z => h0 z))
    (pg0Q_sub c R).eventuallyLE

/-- The cross term `∫ χ' π u` (for `|π| ≤ M`) is bounded by `(1/4) ∫ χ u² + (C₀M/R)² |Q|`. -/
theorem pg0_cross_int {c R C₀ M : ℝ} (hc : 0 < c) (hR0 : 0 < R) (hC₀ : 0 ≤ C₀) (hMnn : 0 ≤ M)
    (hχ : ∀ η : ℝ, 0 ≤ etaCutoff R η)
    (hd : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R * Real.sqrt (etaCutoff R η))
    (hdz : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0)
    (p u : Plane → ℝ) (hp : ∀ z : Plane, |p z| ≤ M)
    (hW : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (p z * u z)) (Cyl.cell c))
    (hui : IntegrableOn (fun z : Plane => etaCutoff R z.2 * u z ^ 2) (Cyl.cell c)) :
    -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (p z * u z)) ≤
      (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * u z ^ 2) +
        (C₀ * M / R) ^ 2 * (c * (4 * R)) := by
  have hWz : ∀ z : Plane, 2 * R ≤ |z.2| → deriv (etaCutoff R) z.2 * (p z * u z) = 0 :=
    fun z hz => by rw [hdz z.2 hz, zero_mul]
  rw [pg0_cell_eq_Q _ hWz]
  have hQint1 : IntegrableOn (fun z : Plane => (1 / 4) * (etaCutoff R z.2 * u z ^ 2))
      (pg0Q c R) :=
    IntegrableOn.mono_set (Integrable.const_mul hui (1 / 4)) (pg0Q_sub c R)
  have hQint2 : IntegrableOn (fun _ : Plane => (C₀ * M / R) ^ 2) (pg0Q c R) :=
    integrableOn_const (pg0Q_fin c R)
  have hQint : IntegrableOn (fun z : Plane => (1 / 4) * (etaCutoff R z.2 * u z ^ 2) +
      (C₀ * M / R) ^ 2) (pg0Q c R) := hQint1.add hQint2
  have hWQ : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (p z * u z)) (pg0Q c R) :=
    IntegrableOn.mono_set hW (pg0Q_sub c R)
  have hnegQ : IntegrableOn (fun z : Plane => -(deriv (etaCutoff R) z.2 * (p z * u z)))
      (pg0Q c R) := hWQ.neg
  have h1 := setIntegral_mono_on hnegQ hQint (pg0Q_meas c R)
    (fun z _ => pg0_cross_alg _ _ _ _ _ _ _ (hχ z.2) hR0 hC₀ hMnn (hd z.2) (hp z))
  rw [integral_neg] at h1
  have hsplit : ∫ z in pg0Q c R, ((1 / 4) * (etaCutoff R z.2 * u z ^ 2) + (C₀ * M / R) ^ 2)
      = (1 / 4) * (∫ z in pg0Q c R, etaCutoff R z.2 * u z ^ 2) +
        (C₀ * M / R) ^ 2 * (c * (4 * R)) := by
    rw [integral_add hQint1 hQint2, integral_const_mul, setIntegral_const, smul_eq_mul,
      measureReal_def, pg0Q_vol hc hR0]
    ring
  have hQle : ∫ z in pg0Q c R, etaCutoff R z.2 * u z ^ 2 ≤
      ∫ z in Cyl.cell c, etaCutoff R z.2 * u z ^ 2 :=
    pg0_Q_le _ hui (fun z => mul_nonneg (hχ z.2) (sq_nonneg _))
  linarith [h1, hsplit, hQle]

/-- **`PressureGradOrder0`** (order-0 pressure gradient, bounded `π`). -/
theorem pressureGradOrder0_proof : UnforcedLeray.Short.PartI.PressureGradOrder0 := by
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
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ π z ^ 2 ≤ 3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2) ∧
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta π z ^ 2 ≤
        3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2) := by
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
    -- the constant
    have hK : (C₀ * M / R) ^ 2 * (c * (4 * R)) ≤ 4 * c * C₀ ^ 2 * M ^ 2 := by
      have hRne : R ≠ 0 := hR0.ne'
      have hR' : 1 / R ≤ 1 := by
        rw [div_le_one hR0]
        linarith
      have hpos : 0 ≤ 4 * c * C₀ ^ 2 * M ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le) (sq_nonneg _)) (sq_nonneg _)
      have heq : (C₀ * M / R) ^ 2 * (c * (4 * R)) = (4 * c * C₀ ^ 2 * M ^ 2) * (1 / R) := by
        field_simp
      rw [heq]
      exact mul_le_of_le_one_right hpos hR'
    have hb1' : -A ≤ (1 / 2) * E + (1 / 2) * Q0 := by
      have h := hb1
      rw [hnegA, hrv] at h
      exact h
    have hEB : E ≤ 3 * Q0 + 32 * c * C₀ ^ 2 * M ^ 2 := by
      linarith [hEA, hb1', hb2, hb3, hb3', hχF1, hK]
    have hq1 : ∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ π z ^ 2 ≤ E := by
      rw [hE]
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => mul_nonneg (hφ01 z.2).1 (sq_nonneg _)) Ivi2
        (Filter.Eventually.of_forall fun z =>
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (hφ01 z.2).1)
    exact ⟨le_trans hq1 hEB, le_trans hb3' hEB⟩
  exact ⟨cutoffL2OfBound_proof c _ (partialQ π) hc hqπc (fun R hR => (hmain R hR).1),
    cutoffL2OfBound_proof c _ (partialEta π) hc hηπc (fun R hR => (hmain R hR).2)⟩

end UnforcedLeray.Short.PartI
