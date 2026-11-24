import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3_1
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.CutoffL2OfBound

/-!
# Part I, task `PartI:T08/3/3/1/2` (`gradL2OfLapL2NoBound_proof`): gradient in `L²` from `h, Δh ∈ L²`

Source of record: `the November 2 reference manuscript`, lines 286-287.
The Prop is `GradL2OfLapL2NoBound` in `Sub/PartI_T08_3_3_1.lean`.

Route. With `χ = etaCutoff R` (`R ≥ 1`), `vi_scalar` for `f = h` gives
`E := ∫ χ |∇h|² = -∫ χ h Δh - ∫ χ' h ∂_η h`.
* `-χ h Δh ≤ (h² + (Δh)²)/2` pointwise (`0 ≤ χ ≤ 1`), so the first term is at most `(H + D)/2`
  with `H = ∫ h²`, `D = ∫ (Δh)²` (both finite, since `h, Δh ∈ L²(cell)`).
* `-χ' h ∂_η h ≤ χ (∂_η h)²/4 + (C₀/R)² h² ≤ χ (∂_η h)²/4 + C₀² h²` pointwise, using `|χ'| ≤ (C₀/R)√χ`.
  This needs no strip: the bound is integrated over the whole cell against the `L²` function `h²`.
Hence `(3/4) E ≤ (H + D)/2 + C₀² H`, so `E ≤ B` with `B` independent of `R`, and
`cutoffL2OfBound_proof` gives the two `L²` gradient components.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)

/-- Algebra: `-(d p u) ≤ χ u²/4 + C² p²` when `|d| ≤ (C/R)√χ` and `R ≥ 1`. -/
theorem gn_cross_alg (χ d p u C R : ℝ) (hχ0 : 0 ≤ χ) (hR1 : 1 ≤ R) (hC : 0 ≤ C)
    (hd : |d| ≤ C / R * Real.sqrt χ) :
    -(d * (p * u)) ≤ (1 / 4) * (χ * u ^ 2) + C ^ 2 * p ^ 2 := by
  have hR : 0 < R := by linarith
  have hs : 0 ≤ Real.sqrt χ := Real.sqrt_nonneg χ
  have hsq : Real.sqrt χ ^ 2 = χ := Real.sq_sqrt hχ0
  have ht : C / R ≤ C := div_le_self hC hR1
  have ht0 : 0 ≤ C / R := div_nonneg hC hR.le
  have h1 : |d * (p * u)| ≤ ((C / R) * |p|) * (Real.sqrt χ * |u|) := by
    rw [abs_mul, abs_mul]
    calc |d| * (|p| * |u|) ≤ (C / R * Real.sqrt χ) * (|p| * |u|) :=
          mul_le_mul_of_nonneg_right hd (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = ((C / R) * |p|) * (Real.sqrt χ * |u|) := by ring
  have h2 : ((C / R) * |p|) * (Real.sqrt χ * |u|) ≤
      (Real.sqrt χ * |u|) ^ 2 / 4 + ((C / R) * |p|) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt χ * |u| / 2 - (C / R) * |p|)]
  have h3 : (Real.sqrt χ * |u|) ^ 2 = χ * u ^ 2 := by
    rw [mul_pow, hsq, sq_abs]
  have h4 : ((C / R) * |p|) ^ 2 ≤ C ^ 2 * p ^ 2 := by
    have e1 : ((C / R) * |p|) ^ 2 = (C / R) ^ 2 * p ^ 2 := by
      rw [mul_pow, sq_abs]
    have e2 : (C / R) ^ 2 ≤ C ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul ht ht ht0 hC
    rw [e1]
    exact mul_le_mul_of_nonneg_right e2 (sq_nonneg _)
  have h5 := neg_le_abs (d * (p * u))
  linarith [h1, h2, h3, h4, h5]

/-- **`GradL2OfLapL2NoBound`** (gradient in `L²` from `h, Δh ∈ L²`, no boundedness). -/
theorem gradL2OfLapL2NoBound_proof : UnforcedLeray.Short.PartI.GradL2OfLapL2NoBound := by
  intro c h hc hh hper hL2 hLap
  have hηF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hηF
  obtain ⟨C₀, hC₀, hcut⟩ := hηF
  have hhI : Integrable (fun z : Plane => h z ^ 2) (Cyl.cellμ c) :=
    (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2
  have hΔI : Integrable (fun z : Plane =>
      (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) (Cyl.cellμ c) :=
    (memLp_two_iff_integrable_sq hLap.aestronglyMeasurable).1 hLap
  have hhIo : IntegrableOn (fun z : Plane => h z ^ 2) (Cyl.cell c) := hhI
  have hΔIo : IntegrableOn (fun z : Plane =>
      (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) (Cyl.cell c) := hΔI
  have hqc : Continuous (partialQ h) := (vi_partialQ_contDiff hh).continuous
  have hec : Continuous (partialEta h) := (vi_partialEta_contDiff hh).continuous
  have hhc : Continuous h := hh.continuous
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∫ z in Cyl.cell c, h z ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∫ z in Cyl.cell c,
      (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (4 / 3) * ((1 / 2 + C₀ ^ 2) * H + (1 / 2) * D) := ⟨_, rfl⟩
  have hmain : ∀ R : ℝ, 1 ≤ R →
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ h z ^ 2 ≤ B) ∧
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2 ≤ B) := by
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
    have hI : ∀ g : Plane → ℝ, Continuous g → (∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) →
        IntegrableOn g (Cyl.cell c) :=
      fun g hg hz => cellIntegrable_of_support c R hc hR0 g hg hz
    obtain ⟨Ivi1, Ivi2, Ivi3, Evi⟩ := vi_scalar hc hR0 cellIntegrable_of_support
      cellDerivZero_of_periodic hsm hφz hdzero h hh hper
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∫ z in Cyl.cell c,
        etaCutoff R z.2 * (partialQ h z ^ 2 + partialEta h z ^ 2) := ⟨_, rfl⟩
    rw [← hE] at Evi
    -- bound on the Laplacian term
    have hb1pt : ∀ z : Plane,
        -(etaCutoff R z.2 * (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z)))
        ≤ (1 / 2) * h z ^ 2 + (1 / 2) * (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2 := by
      intro z
      have h0 := (hφ01 z.2).1
      have h1 := (hφ01 z.2).2
      nlinarith [mul_nonneg h0 (sq_nonneg (h z + (partialQ (partialQ h) z + partialEta (partialEta h) z))),
        mul_nonneg (sub_nonneg.2 h1) (add_nonneg (sq_nonneg (h z))
          (sq_nonneg (partialQ (partialQ h) z + partialEta (partialEta h) z)))]
    have hrI : IntegrableOn (fun z : Plane => (1 / 2) * h z ^ 2 +
        (1 / 2) * (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) (Cyl.cell c) :=
      (Integrable.const_mul hhIo (1 / 2)).add (Integrable.const_mul hΔIo (1 / 2))
    have hGI : IntegrableOn (fun z : Plane => etaCutoff R z.2 * partialEta h z ^ 2)
        (Cyl.cell c) :=
      hI _ (hχc.mul (hec.pow 2)) (fun z hz => by simp [hφz z.2 hz])
    have hb1 : ∫ z in Cyl.cell c,
        -(etaCutoff R z.2 * (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z)))
        ≤ ∫ z in Cyl.cell c, ((1 / 2) * h z ^ 2 +
          (1 / 2) * (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2) :=
      integral_mono (Integrable.neg Ivi1) hrI hb1pt
    have hrv : ∫ z in Cyl.cell c, ((1 / 2) * h z ^ 2 +
        (1 / 2) * (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2)
        = (1 / 2) * H + (1 / 2) * D := by
      rw [integral_add (Integrable.const_mul hhIo (1 / 2)) (Integrable.const_mul hΔIo (1 / 2)),
        integral_const_mul, integral_const_mul, hH, hD]
    have hnegI : ∫ z in Cyl.cell c,
        -(etaCutoff R z.2 * (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z)))
        = -(∫ z in Cyl.cell c,
          etaCutoff R z.2 * (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z))) :=
      integral_neg _
    -- bound on the cross term
    have hb2pt : ∀ z : Plane,
        -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        (1 / 4) * (etaCutoff R z.2 * partialEta h z ^ 2) + C₀ ^ 2 * h z ^ 2 :=
      fun z => gn_cross_alg _ _ _ _ _ _ (hφ01 z.2).1 hR1 hC₀ (hφd z.2)
    have hb2 : ∫ z in Cyl.cell c, -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        ∫ z in Cyl.cell c, ((1 / 4) * (etaCutoff R z.2 * partialEta h z ^ 2) +
          C₀ ^ 2 * h z ^ 2) :=
      integral_mono (Integrable.neg Ivi3)
        ((Integrable.const_mul hGI (1 / 4)).add
          (Integrable.const_mul hhIo (C₀ ^ 2))) hb2pt
    have hb2' : -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2) + C₀ ^ 2 * H := by
      have hnegT : ∫ z in Cyl.cell c, -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) =
          -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * partialEta h z)) :=
        integral_neg _
      have hsplit : ∫ z in Cyl.cell c, ((1 / 4) * (etaCutoff R z.2 * partialEta h z ^ 2) +
          C₀ ^ 2 * h z ^ 2) = (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2)
          + C₀ ^ 2 * H := by
        rw [integral_add (Integrable.const_mul hGI (1 / 4)) (Integrable.const_mul hhIo (C₀ ^ 2)),
          integral_const_mul, integral_const_mul, hH]
      rw [hnegT, hsplit] at hb2
      exact hb2
    -- the gradient in `η` is dominated by the energy
    have hb3 : ∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2 ≤ E := by
      rw [hE]
      exact integral_mono (hI _ (hχc.mul (hec.pow 2)) (fun z hz => by simp [hφz z.2 hz]))
        Ivi2 (fun z => mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (sq_nonneg (partialQ h z))) (hφ01 z.2).1)
    have hEB : E ≤ B := by
      have hEv : E = -(∫ z in Cyl.cell c,
          etaCutoff R z.2 * (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z)))
          - ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * partialEta h z) := by
        linarith [Evi]
      have hb1' : -(∫ z in Cyl.cell c,
          etaCutoff R z.2 * (h z * (partialQ (partialQ h) z + partialEta (partialEta h) z)))
          ≤ (1 / 2) * H + (1 / 2) * D := by
        have hb1c := hb1
        rw [hnegI, hrv] at hb1c
        exact hb1c
      rw [hB]
      linarith [hEv, hb1', hb2', hb3]
    have hq1 : ∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ h z ^ 2 ≤ E := by
      rw [hE]
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => mul_nonneg (hφ01 z.2).1 (sq_nonneg _)) Ivi2
        (Filter.Eventually.of_forall fun z =>
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (hφ01 z.2).1)
    exact ⟨le_trans hq1 hEB, le_trans hb3 hEB⟩
  exact ⟨cutoffL2OfBound_proof c B (partialQ h) hc hqc (fun R hR => (hmain R hR).1),
    cutoffL2OfBound_proof c B (partialEta h) hc hec (fun R hR => (hmain R hR).2)⟩

end UnforcedLeray.Short.PartI
