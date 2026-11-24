import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_6
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, task `PartI:T08/4/1/1/6/2` (`gradL2QuantP_proof`): quantitative gradient bound

Source of record: `the November 2 reference manuscript`, lines 266-270, 326-329.
The Prop is `GradL2QuantP` in `Sub/PartI_T08_4_1_1_6.lean`.

Route. As `gradL2OfLapL2NoBound_proof`, with `χ = etaCutoff R`: `E := ∫ χ |∇h|² ≤ (2/3)(H + D)
+ (4/3)·C₀²(1/R)²·H`, where `H = ∫ h²`, `D = ∫ (Δh)²`; the cross term is bounded with weight
`(C₀/R)²` instead of `C₀²`, so the constant `C₀` drops out as `R → ∞` (Fatou along `R = n + 1`,
`q1_fatou`). Final constant `2/3 ≤ 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)

/-- Fatou along the cutoffs `R = n + 1`: a nonnegative integrand whose truncated integrals are
bounded by `B n → Q` has cell integral at most `Q`. -/
theorem q1_fatou {c : ℝ} (hc : 0 < c) (g : Plane → ℝ) (hg : Continuous g)
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

/-- Cross-term algebra with the weight `(C/R)²` on the `L²` factor. -/
theorem q1_cross_alg (χ d p u C R : ℝ) (hχ0 : 0 ≤ χ) (hR : 0 < R)
    (hd : |d| ≤ C / R * Real.sqrt χ) :
    -(d * (p * u)) ≤ (1 / 4) * (χ * u ^ 2) + (C / R * p) ^ 2 := by
  have hs : 0 ≤ Real.sqrt χ := Real.sqrt_nonneg χ
  have hsq : Real.sqrt χ ^ 2 = χ := Real.sq_sqrt hχ0
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
  have h4 : ((C / R) * |p|) ^ 2 = (C / R * p) ^ 2 := by
    simp [mul_pow, sq_abs]
  have h5 := neg_le_abs (d * (p * u))
  linarith [h1, h2, h3, h4, h5]

/-- **`GradL2QuantP`** (quantitative gradient bound from `h, Δh ∈ L²`). -/
theorem gradL2QuantP_proof : UnforcedLeray.Short.PartI.GradL2QuantP := by
  intro c h hc hh hper hL2 hLap
  show ∫ z in Cyl.cell c, ((partialQ h z) ^ 2 + (partialEta h z) ^ 2) ≤
    2 * ((∫ z in Cyl.cell c, (h z) ^ 2) +
      ∫ z in Cyl.cell c, (partialQ (partialQ h) z + partialEta (partialEta h) z) ^ 2)
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
  have hHnn : 0 ≤ H := by rw [hH]; exact integral_nonneg (fun z => sq_nonneg _)
  have hDnn : 0 ≤ D := by rw [hD]; exact integral_nonneg (fun z => sq_nonneg _)
  have hmain : ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * (partialQ h z ^ 2 + partialEta h z ^ 2) ≤
        (2 / 3) * (H + D) + (4 / 3) * ((C₀ ^ 2 * (1 / R) ^ 2) * H) := by
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
    -- bound on the cross term, weight `(C₀ / R)²` on `h²`
    have hKI : Integrable (fun z : Plane => (C₀ / R * h z) ^ 2) (volume.restrict (Cyl.cell c)) :=
      (hhIo.const_mul ((C₀ / R) ^ 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have hKint : ∫ z in Cyl.cell c, (C₀ / R * h z) ^ 2 = (C₀ ^ 2 * (1 / R) ^ 2) * H := by
      rw [hH, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    have hb2pt : ∀ z : Plane,
        -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        (1 / 4) * (etaCutoff R z.2 * partialEta h z ^ 2) + (C₀ / R * h z) ^ 2 :=
      fun z => q1_cross_alg _ _ _ _ _ _ (hφ01 z.2).1 hR0 (hφd z.2)
    have hb2 : ∫ z in Cyl.cell c, -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        ∫ z in Cyl.cell c, ((1 / 4) * (etaCutoff R z.2 * partialEta h z ^ 2) +
          (C₀ / R * h z) ^ 2) :=
      integral_mono (Integrable.neg Ivi3)
        ((Integrable.const_mul hGI (1 / 4)).add hKI) hb2pt
    have hb2' : -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * partialEta h z)) ≤
        (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2)
          + (C₀ ^ 2 * (1 / R) ^ 2) * H := by
      have hnegT : ∫ z in Cyl.cell c, -(deriv (etaCutoff R) z.2 * (h z * partialEta h z)) =
          -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * partialEta h z)) :=
        integral_neg _
      have hsplit : ∫ z in Cyl.cell c, ((1 / 4) * (etaCutoff R z.2 * partialEta h z ^ 2) +
          (C₀ / R * h z) ^ 2) = (1 / 4) * (∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2)
          + (C₀ ^ 2 * (1 / R) ^ 2) * H := by
        rw [integral_add (Integrable.const_mul hGI (1 / 4)) hKI, integral_const_mul, hKint]
      rw [hnegT, hsplit] at hb2
      exact hb2
    -- the gradient in `η` is dominated by the energy
    have hb3 : ∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta h z ^ 2 ≤ E := by
      rw [hE]
      exact integral_mono (hI _ (hχc.mul (hec.pow 2)) (fun z hz => by simp [hφz z.2 hz]))
        Ivi2 (fun z => mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (sq_nonneg (partialQ h z))) (hφ01 z.2).1)
    have hEB : E ≤ (2 / 3) * (H + D) + (4 / 3) * ((C₀ ^ 2 * (1 / R) ^ 2) * H) := by
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
      linarith [hEv, hb1', hb2', hb3]
    rw [← hE]
    exact hEB
  -- Fatou along `R = n + 1`
  have hBt : Tendsto (fun n : ℕ => (2 / 3) * (H + D) +
      (4 / 3) * ((C₀ ^ 2 * (1 / ((n : ℝ) + 1)) ^ 2) * H)) atTop (𝓝 ((2 / 3) * (H + D))) := by
    have h1 := ((tendsto_one_div_add_atTop_nhds_zero_nat).pow 2).const_mul (C₀ ^ 2)
    have h2 := (h1.mul_const H).const_mul (4 / 3)
    have h3 := h2.const_add ((2 / 3) * (H + D))
    simpa using h3
  have hcellint : ∀ n : ℕ, Integrable
      (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 *
        (partialQ h z ^ 2 + partialEta h z ^ 2)) (volume.restrict (Cyl.cell c)) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨hsm, -, -, hφz, -⟩ := hcut ((n : ℝ) + 1) (by linarith)
    have hχc : Continuous (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2) :=
      hsm.continuous.comp continuous_snd
    exact cellIntegrable_of_support c _ hc hR0 _
      (hχc.mul ((hqc.pow 2).add (hec.pow 2)))
      (fun z hz => by simp [hφz z.2 hz])
  have hbound : ∀ n : ℕ, ∫ z in Cyl.cell c,
      etaCutoff ((n : ℝ) + 1) z.2 * (partialQ h z ^ 2 + partialEta h z ^ 2) ≤
        (2 / 3) * (H + D) + (4 / 3) * ((C₀ ^ 2 * (1 / ((n : ℝ) + 1)) ^ 2) * H) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact hmain ((n : ℝ) + 1) (by linarith)
  have hgnn : ∀ z : Plane, 0 ≤ partialQ h z ^ 2 + partialEta h z ^ 2 :=
    fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfin := q1_fatou hc (fun z : Plane => partialQ h z ^ 2 + partialEta h z ^ 2)
    ((hqc.pow 2).add (hec.pow 2)) hgnn _ ((2 / 3) * (H + D)) (by linarith) hBt hcellint hbound
  rw [← hH, ← hD]
  linarith [hfin, hHnn, hDnn]

end UnforcedLeray.Short.PartI
