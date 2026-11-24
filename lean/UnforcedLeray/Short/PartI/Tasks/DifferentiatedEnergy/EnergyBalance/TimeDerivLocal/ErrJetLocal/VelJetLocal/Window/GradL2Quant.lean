import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.CutoffL2OfBound
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, task `PartI:T08/2/2/4` (`gradL2OfLapL2_proof`): gradient in `L²` from the Laplacian

Source of record: `the November 2 reference manuscript`, lines 286-287.
The Prop is `GradL2OfLapL2` in `Sub/PartI_T08_2_2.lean`.

Route. Fix `R ≥ 1`, `φ = etaCutoff R`, `d = Δh`.  `vi_scalar` gives
`∫ φ (q² + η²) = -∫ φ h d - ∫ φ' h η` (`q = ∂_q h`, `η = ∂_η h`).
* `-φ h d ≤ (h² + d²)/2` pointwise, since `0 ≤ φ ≤ 1`.
* `|φ' h η| ≤ (C₀/R) M²` pointwise, and `φ' = 0` for `|η| ≥ 2R`, so the cross term reduces to the
  strip `Q = [-c/2, c/2) × [-2R, 2R]` of volume `4cR`, giving the bound `4 C₀ c M²`.
Hence `∫ φ (q² + η²) ≤ B` for all `R ≥ 1`, with `B` independent of `R`.  Then
`cutoffL2OfBound_proof` applied to `∂_q h` and `∂_η h` gives the conclusion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)

/-- **`GradL2Quant`** (proved, lines 286-287). The constant is `K = 4 C₀ c M²`, which depends only
on `c` and `M`. -/
theorem gradL2Quant_proof : UnforcedLeray.Short.PartI.GradL2Quant := by
  intro c hc M
  have hηF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hηF
  obtain ⟨C₀, hC₀, hcut⟩ := hηF
  refine ⟨4 * C₀ * c * M ^ 2, ?_⟩
  intro h hh hper hM hL2 hLap
  have hqc : ContDiff ℝ ∞ (partialQ h) := vi_partialQ_contDiff hh
  have hec : ContDiff ℝ ∞ (partialEta h) := vi_partialEta_contDiff hh
  have hqcont : Continuous (partialQ h) := hqc.continuous
  have hecont : Continuous (partialEta h) := hec.continuous
  -- integrability of the `L²` data on the cell
  have hi1 : IntegrableOn (fun z : Plane => h z ^ 2) (Cyl.cell c) := hL2.integrable_sq
  have hi2 : IntegrableOn (fun z : Plane =>
      (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) (Cyl.cell c) :=
    hLap.integrable_sq
  have hi12 : IntegrableOn (fun z : Plane =>
      (h z ^ 2 + (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) / 2)
      (Cyl.cell c) :=
    (hi1.add hi2).div_const 2
  -- the constant
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (∫ z in Cyl.cell c,
      (h z ^ 2 + (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) / 2)
      + 4 * C₀ * c * M ^ 2 := ⟨_, rfl⟩
  -- the uniform bound for every `R ≥ 1`
  have hmain : ∀ R : ℝ, 1 ≤ R →
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ h z ^ 2 ≤ B) ∧
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2 ≤ B) := by
    intro R hR1
    have hR0 : 0 < R := by linarith
    have hRne : R ≠ 0 := hR0.ne'
    obtain ⟨hsm, hφ01, -, hφz, hφd⟩ := hcut R hR1
    have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
      intro η hη
      have h0 := hφd η
      rw [hφz η hη, Real.sqrt_zero, mul_zero] at h0
      exact abs_nonpos_iff.mp h0
    obtain ⟨hV1, hV2, hV3, hV4⟩ := vi_scalar hc hR0 cellIntegrable_of_support
      cellDerivZero_of_periodic hsm hφz hdzero h hh hper
    -- the two quadratic integrands are integrable
    have hPc : Continuous (fun z : Plane => etaCutoff R z.2) := hsm.continuous.comp continuous_snd
    have hgq : IntegrableOn (fun z : Plane => etaCutoff R z.2 * partialQ h z ^ 2) (Cyl.cell c) :=
      cellIntegrable_of_support c R hc hR0 _ (hPc.mul (hqcont.pow 2))
        (fun z hz => by simp only [hφz z.2 hz, zero_mul])
    have hge : IntegrableOn (fun z : Plane => etaCutoff R z.2 * partialEta h z ^ 2) (Cyl.cell c) :=
      cellIntegrable_of_support c R hc hR0 _ (hPc.mul (hecont.pow 2))
        (fun z hz => by simp only [hφz z.2 hz, zero_mul])
    -- the first term: `-φ h d ≤ (h² + d²)/2`
    have hfirst : -(∫ z in Cyl.cell c, etaCutoff R z.2 *
        (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z))) ≤
        ∫ z in Cyl.cell c, (h z ^ 2 + (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) / 2 := by
      rw [← integral_neg]
      refine integral_mono (Integrable.neg hV1) hi12 (fun z => ?_)
      have h0 : 0 ≤ etaCutoff R z.2 := (hφ01 z.2).1
      have h1 : etaCutoff R z.2 ≤ 1 := (hφ01 z.2).2
      nlinarith [mul_nonneg (sub_nonneg.2 h1)
          (add_nonneg (sq_nonneg (h z)) (sq_nonneg (partialQ (partialQ h) z + partialEta (partialEta h) z))),
        mul_nonneg h0 (sq_nonneg (h z + (partialQ (partialQ h) z + partialEta (partialEta h) z)))]
    -- the cross term: pointwise bound
    have hA : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R := by
      intro η
      have hsq : Real.sqrt (etaCutoff R η) ≤ 1 := by
        have h1 := Real.sqrt_le_sqrt (hφ01 η).2
        rwa [Real.sqrt_one] at h1
      have h2 : C₀ / R * Real.sqrt (etaCutoff R η) ≤ C₀ / R :=
        mul_le_of_le_one_right (div_nonneg hC₀ hR0.le) hsq
      linarith [hφd η]
    have hbound : ∀ z : Plane, -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        C₀ / R * (M * M) := by
      intro z
      have hB : |h z| ≤ M := (hM z).1
      have hC : |partialEta h z| ≤ M := (hM z).2.2
      have habs : |deriv (etaCutoff R) z.2 * (h z * partialEta h z)| ≤ C₀ / R * (M * M) := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hA z.2) (mul_le_mul hB hC (abs_nonneg _) (le_trans (abs_nonneg _) hB))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (div_nonneg hC₀ hR0.le)
      exact (neg_le_abs _).trans habs
    -- the strip `Q = [-c/2, c/2) × [-2R, 2R]` carries the cross term
    set Q : Set Plane := Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hQdef
    have hQmeas : MeasurableSet Q := measurableSet_Ico.prod measurableSet_Icc
    have hQc : Q ⊆ Cyl.cell c := by
      rw [hQdef, Cyl.cell]
      exact Set.prod_mono subset_rfl (Set.subset_univ _)
    have hQfin : (volume : Measure Plane) Q ≠ ⊤ := by
      rw [hQdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hQre : ((volume : Measure Plane) Q).toReal = c * (4 * R) := by
      rw [hQdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      · ring
      all_goals linarith
    have hoffQ : ∀ x ∈ Cyl.cell c \ Q,
        deriv (etaCutoff R) x.2 * (h x * partialEta h x) = 0 := by
      intro x hx
      have hxz : 2 * R ≤ |x.2| := by
        by_contra hlt
        apply hx.2
        rw [hQdef]
        exact ⟨hx.1.1, abs_le.1 (not_le.1 hlt).le⟩
      rw [hdzero x.2 hxz, zero_mul]
    have hcellQ : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * partialEta h z) =
        ∫ z in Q, deriv (etaCutoff R) z.2 * (h z * partialEta h z) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Cyl.measurableSet_cell c) hQc hoffQ
    have hGQ : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (h z * partialEta h z)) Q :=
      hV3.mono_set hQc
    have hconst : IntegrableOn (fun _ : Plane => C₀ / R * (M * M)) Q := integrableOn_const hQfin
    have hcross : -(∫ z in Q, deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        C₀ / R * (M * M) * ((volume : Measure Plane) Q).toReal := by
      have h1 : ∫ z in Q, -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
          ∫ _ in Q, C₀ / R * (M * M) :=
        setIntegral_mono_on hGQ.neg hconst hQmeas (fun z _ => hbound z)
      rw [integral_neg, setIntegral_const, smul_eq_mul, measureReal_def] at h1
      linarith
    have hK : C₀ / R * (M * M) * ((volume : Measure Plane) Q).toReal = 4 * C₀ * c * M ^ 2 := by
      rw [hQre]
      field_simp
    -- the energy identity and the resulting bound
    have hEn : ∫ z in Cyl.cell c, etaCutoff R z.2 * (partialQ h z ^ 2 + partialEta h z ^ 2) ≤
        B := by
      rw [hBdef]
      linarith [hV4, hfirst, hcross, hK, hcellQ]
    refine ⟨?_, ?_⟩
    · refine le_trans (integral_mono hgq hV2 (fun z => ?_)) hEn
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (hφ01 z.2).1
    · refine le_trans (integral_mono hge hV2 (fun z => ?_)) hEn
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (hφ01 z.2).1
  -- the constant `B` is at most `∫h² + ∫(Δh)² + K`, since `(h²+d²)/2 ≤ h²+d²`
  have hsplit : (∫ z in Cyl.cell c,
      (h z ^ 2 + (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) / 2)
      ≤ (∫ z in Cyl.cell c, h z ^ 2)
        + (∫ z in Cyl.cell c, (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) := by
    rw [← integral_add hi1 hi2]
    exact integral_mono hi12 (hi1.add hi2) (fun z => by
      nlinarith [sq_nonneg (h z), sq_nonneg (partialQ (partialQ h) z + partialEta (partialEta h) z)])
  have hB' : B ≤ (∫ z in Cyl.cell c, h z ^ 2)
      + (∫ z in Cyl.cell c, (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2)
      + 4 * C₀ * c * M ^ 2 := by
    rw [hBdef]
    linarith [hsplit]
  -- uniform bound on the cutoff integrals of `∂_q h`, `∂_η h`
  have hmain' : ∀ R : ℝ, 1 ≤ R →
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ h z ^ 2 ≤
        (∫ z in Cyl.cell c, h z ^ 2)
        + (∫ z in Cyl.cell c, (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2)
        + 4 * C₀ * c * M ^ 2) ∧
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2 ≤
        (∫ z in Cyl.cell c, h z ^ 2)
        + (∫ z in Cyl.cell c, (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2)
        + 4 * C₀ * c * M ^ 2) :=
    fun R hR => ⟨le_trans (hmain R hR).1 hB', le_trans (hmain R hR).2 hB'⟩
  have hq := cutoffL2Quant_proof c _ (partialQ h) hc hqcont (fun R hR => (hmain' R hR).1)
  have he := cutoffL2Quant_proof c _ (partialEta h) hc hecont (fun R hR => (hmain' R hR).2)
  exact ⟨hq.1, he.1, hq.2, he.2⟩

end UnforcedLeray.Short.PartI
