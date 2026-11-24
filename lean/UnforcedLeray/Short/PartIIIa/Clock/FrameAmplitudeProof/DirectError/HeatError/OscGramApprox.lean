import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold.Fubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Ext
import UnforcedLeray.Short.PartI.Tasks.SeedFunctionalProof
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJet
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox.DualUnfold
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox.PlanarIBP
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox.SeedPolar
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox.SeedKappa

/-!
# Part III-a, task `PartIII-a:T21/c5/2/1/2`: periodized oscillator Gram matrix approximation (`PerOscGramApprox`, SP 2893, 2905-2912, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2893,
2905-2912, and 2991-2995 (`eq:short-causal-ampl-moving`).

## Proved results in this file

1. **Planar cross-integral bound and lattice shift summability for `movD (κ.e j)`
   (`movD_seed_uniform_decay`, `contDiff_movD_seed`, `oscGramCross_int`, `oscGramCross_bound`,
   `summable_movD_shift`)**:
   * Uses `OscillatorForceSub.movD_seed_decay` (`Continuous (movD (κ.e j))` and
     `‖movD (κ.e j) y‖ ≤ C * e^{-|y|²/8}`) together with `κ.lamP_decay` and `gram_pt`
     (`Clock/FrameFacts/GramTail/Bound.lean`) to prove that for `IsSeedKernels κ`,
     `fun y => κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)` is integrable on `ℝ × ℝ` with
     `∫ y, ‖κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)‖ ≤ K / (1 + |a|) ^ 2`, and that
     `fun n : ℤ => ‖movD (κ.e j) (y.1 + n * d, y.2)‖` is summable for `d > 0`.
2. **Unfolding and `O(d⁻²)` off-diagonal tail bound for `oscGram`
   (`oscGram_unfold`, `oscGram_tail`, `oscGram_sub_zero_term_bound`)**:
   * Defines the periodized oscillator Gram pairing
     `oscGram κ d k j = ∫ x in B0579.cell d, perLam0 κ d k x * perSum d (movD (κ.e j)) x`
     and its `n`-th cross integral
     `oscGramTerm κ d k j n = ∫ y, κ.lamP k y * movD (κ.e j) (y.1 + n * d, y.2)`.
   * Proves unconditionally for `IsSeedKernels κ` and `d > 0` that `oscGramTerm κ d k j` is
     summable on `ℤ` with `oscGram κ d k j = ∑' n : ℤ, oscGramTerm κ d k j n`, and that for
     `d ≥ 1` the `n ≠ 0` tail is bounded by `C_tail / d ^ 2`, hence
     `‖oscGram κ d k j - ∫ y, κ.lamP k y * movD (κ.e j) y‖ ≤ C_tail / d ^ 2`.
3. **Periodization identity for `movOscRes` pairing and `seedEll` sector representation
   (`integral_perLam0_mul_movOscRes_eq`, `oscGram_zero_term_eq_seedEll`)**:
   * Applies `OscillatorForceSub.movOscRes_eq_perSum_movD` to show that on `movingCell ν (ν ^ (-2 : ℝ)) r`,
     `∫ y in movingCell ν (ν ^ (-2 : ℝ)) r, perLam0 κ d k y * movOscRes κ ν r j y = (clockTheta ν r : ℂ)⁻¹ * oscGram κ d k j`.
   * Applies `seedBiorthExt_proof` and `PartI.seedFunctional_proof` to express the `n = 0` planar
     pairing `∫ y, κ.lamP k y * movD (κ.e j) y` in terms of `PartI.seedEll h` on the `±2` angular
     sectors of `movD (κ.e j)`.
4. **The planar pairing (`seedPlanarOscPairing`)**: `⟨λ_k, D e_j⟩ = δ_{k,j} modeKappa P k`, from
   the polar form of `D` on the seed modes (`OscGramApprox/SeedPolar.lean`), the sector
   representation `oscGram_zero_term_eq_seedEll`, and `κ = ℓ(Dq)`
   (`OscGramApprox/SeedKappa.lean`).
5. **Assembly (`perOscGramApprox`)**: the dual periodization identity
   `movLam0DualHeat = θ⁻¹ P_d(D^# λ_k)` (SharpDecay, jets from `seedLamPJet2Decay_all`) gives
   `movLam0DirectHeat = θ⁻¹ ∫_cell P_d(D^# λ_k) P_d e_j`; this unfolds with an `O(d⁻²)` tail
   (`OscGramApprox/DualUnfold.lean`), and the `n = 0` term is `∫ (D^# λ_k) e_j = ∫ λ_k D e_j`
   (`OscGramApprox/PlanarIBP.lean`). The route avoids a moving-cell integration by parts against
   `movOscRes`: on the moving cell that pairing differs from `movLam0DirectHeat` by the
   cell-length term `∂_z G(d(z))`, which is not zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The periodized oscillator Gram matrix entry
`∫_{B0579.cell d} perLam0 κ d k x * perSum d (movD (κ.e j)) x dx` (SP 2905-2912, 2991-2995). -/
def oscGram (κ : PlanarFrameKernels) (d : ℝ) (k j : Fin 2) : ℂ :=
  ∫ x in B0579.cell d, perLam0 κ d k x * perSum d (movD (κ.e j)) x

/-- The `n`-th unfolded planar cross integral of `oscGram`:
`∫_{ℝ²} λ_k(y) (D e_j)(y₁ + n d, y₂) dy` (SP 2894-2895, 2905-2912). -/
def oscGramTerm (κ : PlanarFrameKernels) (d : ℝ) (k j : Fin 2) (n : ℤ) : ℂ :=
  ∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) (y.1 + (n : ℝ) * d, y.2)

namespace OscGramSub

open OscillatorForceSub

/-! ## 1. Planar cross-integral bound and lattice shift summability for `movD (κ.e j)` -/

/-- Uniform continuity and Gaussian `e^{-|y|²/8}` bound for `movD (κ.e j)` across `j ∈ {0, 1}`. -/
theorem movD_seed_uniform_decay {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    (∀ j : Fin 2, Continuous (movD (κ.e j))) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) (y : ℝ × ℝ),
      ‖movD (κ.e j) y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
  obtain ⟨hc0, C0, hC0_pos, hC0⟩ := movD_seed_decay hκ 0
  obtain ⟨hc1, C1, hC1_pos, hC1⟩ := movD_seed_decay hκ 1
  refine ⟨fun j => by fin_cases j <;> assumption,
    max C0 C1, le_trans hC0_pos (le_max_left _ _), fun j y => ?_⟩
  fin_cases j
  · exact (hC0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · exact (hC1 y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- `C^∞` smoothness of `movD (κ.e j)` for `IsSeedKernels κ`. -/
theorem contDiff_movD_seed {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    ContDiff ℝ ∞ (movD (κ.e j)) := by
  have hsm : ContDiff ℝ ∞ (κ.e j) := (seed_e_smooth_decay hκ).1 j
  unfold movD ladLapCx pdCx
  have hd1 : ∀ k : Fin 2, ContDiff ℝ ∞ (fun y => fderiv ℝ (κ.e j) y (B0579.dir k)) :=
    fun k => (hsm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hd2 : ∀ k : Fin 2, ContDiff ℝ ∞ (fun y =>
      fderiv ℝ (fun z => fderiv ℝ (κ.e j) z (B0579.dir k)) y (B0579.dir k)) :=
    fun k => ((hd1 k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hc1 := hd2 0
  have hc2 := hd2 1
  have hc3 := hd1 0
  have hc4 := hd1 1
  have hy1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((y.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hy2 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((y.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact ((hc1.add hc2).add
    (contDiff_const.mul ((hy1.mul hc3).add (hy2.mul hc4)))).add
    (contDiff_const.mul hsm)

/-- For `IsSeedKernels κ`, the planar cross product
`y ↦ κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)` is integrable on `ℝ × ℝ` with `L¹` norm bounded by
`K / (1 + |a|) ^ 2`. -/
theorem oscGramCross_int {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k j : Fin 2) (a : ℝ),
      Integrable (fun y : ℝ × ℝ => κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)) ∧
      ∫ y : ℝ × ℝ, ‖κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)‖ ≤ K / (1 + |a|) ^ 2 := by
  obtain ⟨C1, hC1⟩ := κ.lamP_decay
  obtain ⟨hcont_movD, C2, _, hC2⟩ := movD_seed_uniform_decay hκ
  refine ⟨|C1| * |C2| * (2080 * Real.pi), by positivity, fun k j a => ?_⟩
  have hA : 0 ≤ |C1| * |C2| := by positivity
  have hpt : ∀ y : ℝ × ℝ, ‖κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)‖ ≤
      (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) := by
    intro y
    rw [norm_mul]
    have h1 : ‖κ.lamP k y‖ ≤ |C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
      (hC1 k y).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity))
    have h2 : ‖movD (κ.e j) (y.1 + a, y.2)‖ ≤
        |C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have h := hC2 j (y.1 + a, y.2)
      have hh : Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / 8) =
          Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by norm_num
      refine h.trans ?_
      dsimp only
      rw [hh]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    calc ‖κ.lamP k y‖ * ‖movD (κ.e j) (y.1 + a, y.2)‖
        ≤ (|C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2) *
            (|C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (|C1| * |C2|) * ((1 + |y.1| + |y.2|)⁻¹ ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) := by ring
      _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
          mul_le_mul_of_nonneg_left (gram_pt a y.1 y.2) hA
  have G8 := integrable_shift_gauss (c := a) (t := 2) (by norm_num)
  have G16 := integrable_shift_gauss (c := a) (t := 4) (by norm_num)
  have hint : Integrable (fun y : ℝ × ℝ => (|C1| * |C2|) *
      (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4)))) :=
    ((G8.const_mul (4 / (1 + |a|) ^ 2)).add
      (G16.const_mul (Real.exp (-a ^ 2 / (4 * 16))))).const_mul _
  have hcont : Continuous (fun y : ℝ × ℝ => κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)) :=
    (κ.lamP_cont k).mul ((hcont_movD j).comp (by fun_prop))
  refine ⟨Integrable.mono' hint hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt), ?_⟩
  have hE := exp_neg_sq_mul_le a
  have hE' : Real.exp (-a ^ 2 / (4 * 16)) ≤ 128 / (1 + |a|) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ∫ y : ℝ × ℝ, ‖κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)‖
      ≤ ∫ y : ℝ × ℝ, (|C1| * |C2|) *
          (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          Real.exp (-a ^ 2 / (4 * 16)) * (4 * Real.pi * 4)) := by
        rw [integral_const_mul, integral_add (G8.const_mul _) (G16.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_shift_gauss (c := a) (t := 2) (by norm_num),
          integral_shift_gauss (c := a) (t := 4) (by norm_num)]
    _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          128 / (1 + |a|) ^ 2 * (4 * Real.pi * 4)) := by
        gcongr
    _ = |C1| * |C2| * (2080 * Real.pi) / (1 + |a|) ^ 2 := by ring

/-- Norm bound on the planar cross integral `∫ y, κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)`. -/
theorem oscGramCross_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k j : Fin 2) (a : ℝ),
      ‖∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) (y.1 + a, y.2)‖ ≤ K / (1 + |a|) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := oscGramCross_int hκ
  exact ⟨K, hK0, fun k j a => (norm_integral_le_integral_norm _).trans (hK k j a).2⟩

/-- Lattice shift summability for `movD (κ.e j)` at any period `d > 0`. -/
theorem summable_movD_shift {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ} (hd : 0 < d)
    (j : Fin 2) (y : ℝ × ℝ) :
    Summable (fun n : ℤ => ‖movD (κ.e j) (y.1 + n * d, y.2)‖) := by
  obtain ⟨_, C, _, hC⟩ := movD_seed_uniform_decay hκ
  have hs := (UnforcedLeray.Gaussian.summable_translate (s := 2) (c := -d) (by norm_num)
    (neg_ne_zero.2 hd.ne') y.1).mul_left (|C| * 128)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  have h1 := hC j (y.1 + n * d, y.2)
  have hq : y.1 - (n : ℝ) * (-d) = y.1 + n * d := by ring
  rw [hq]
  generalize y.1 + (n : ℝ) * d = s at h1 ⊢
  have hE := exp_neg_sq_mul_le s
  have hpos : 0 < (1 + |s|) ^ 2 := by positivity
  have hE' : Real.exp (-s ^ 2 / (4 * 16)) ≤ 128 / (1 + |s|) ^ 2 := by
    rw [le_div_iff₀ hpos]; linarith
  have h2 : Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) ≤ Real.exp (-s ^ 2 / (4 * 16)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ y.2 ^ 2 := sq_nonneg y.2
    linarith [sq_nonneg s]
  have h3 : (1 + |s|) ^ (-(2 : ℝ)) = 1 / (1 + |s|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), inv_eq_one_div]; norm_cast
  rw [h3]
  calc ‖movD (κ.e j) (s, y.2)‖ ≤ C * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) := h1
    _ ≤ |C| * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * (128 / (1 + |s|) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans hE') (abs_nonneg C)
    _ = |C| * 128 * (1 / (1 + |s|) ^ 2) := by ring

/-! ## 2. Unfolding and `O(d⁻²)` off-diagonal tail bound for `oscGram` -/

/-- **Unfolding of `oscGram`** (SP 2894-2895, 2905-2912): for `IsSeedKernels κ` and `d > 0`,
`oscGram κ d k j` is the summable series `∑' n : ℤ, oscGramTerm κ d k j n`. -/
theorem oscGram_unfold {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ} (hd : 0 < d)
    (k j : Fin 2) :
    Summable (fun n : ℤ => oscGramTerm κ d k j n) ∧
    oscGram κ d k j = ∑' n : ℤ, oscGramTerm κ d k j n := by
  obtain ⟨K, -, hK⟩ := oscGramCross_int hκ
  obtain ⟨hcont_movD, _, _, _⟩ := movD_seed_uniform_decay hκ
  set Fn : ℤ → ℝ × ℝ → ℂ :=
    fun n y => κ.lamP k y * movD (κ.e j) (y.1 + (n : ℝ) * d, y.2) with hFn
  have hint : ∀ n, Integrable (Fn n) := fun n => (hK k j ((n : ℝ) * d)).1
  have hnorm : ∀ n, ∫ y, ‖Fn n y‖ ≤ K / (1 + |(n : ℝ) * d|) ^ 2 := fun n =>
    (hK k j ((n : ℝ) * d)).2
  have hb := summable_cross_bound (K := K) hd
  have hsumI : Summable (fun n => ∫ y, ‖Fn n y‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hnorm hb
  have hsum : Summable (fun n : ℤ => oscGramTerm κ d k j n) :=
    hsumI.of_norm_bounded fun n => norm_integral_le_integral_norm _
  have hPdSum : ∀ y : ℝ × ℝ, Summable (fun n : ℤ => movD (κ.e j) (y.1 + n * d, y.2)) := fun y =>
    (summable_movD_shift hκ hd j y).of_norm
  have hPdMeas : Measurable (perSum d (movD (κ.e j))) :=
    measurable_perSum (hcont_movD j) hPdSum
  have hFsum : ∀ y, κ.lamP k y * perSum d (movD (κ.e j)) y = ∑' n : ℤ, Fn n y := by
    intro y
    simp only [perSum, hFn]
    exact tsum_mul_left.symm
  have hlin : ∀ n, ∫⁻ y, ‖Fn n y‖ₑ = ENNReal.ofReal (∫ y, ‖Fn n y‖) := fun n =>
    (ofReal_integral_norm_eq_lintegral_enorm (hint n)).symm
  have hsumL : ∑' n, ∫⁻ y, ‖Fn n y‖ₑ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun y => norm_nonneg _) hsumI]
    exact ENNReal.ofReal_ne_top
  have hmeasF : ∀ n, AEStronglyMeasurable (Fn n) volume := fun n => (hint n).1
  have hInt : Integrable (fun y => ∑' n, Fn n y) := by
    refine ⟨?_, ?_⟩
    · have : (fun y => ∑' n, Fn n y) = fun y => κ.lamP k y * perSum d (movD (κ.e j)) y :=
        funext fun y => (hFsum y).symm
      rw [this]
      exact ((κ.lamP_cont k).measurable.mul hPdMeas).aestronglyMeasurable
    · calc ∫⁻ y, ‖∑' n, Fn n y‖ₑ ≤ ∫⁻ y, ∑' n, ‖Fn n y‖ₑ :=
            lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' n, ∫⁻ y, ‖Fn n y‖ₑ := lintegral_tsum (fun n => (hmeasF n).enorm)
        _ < ⊤ := lt_top_iff_ne_top.2 hsumL
  have hcell : oscGram κ d k j = ∫ y, ∑' n, Fn n y := by
    unfold oscGram
    have h1 : ∀ x : ℝ × ℝ,
        perLam0 κ d k x * perSum d (movD (κ.e j)) x =
          perSum d (fun y => ∑' n, Fn n y) x := by
      intro x
      simp only [perLam0, perSum]
      rw [← tsum_mul_right]
      refine tsum_congr fun m => ?_
      rw [← hFsum]
      congr 1
      exact (perSum_int_period d (movD (κ.e j)) m x).symm
    rw [← integral_bcell_perSum hInt hd]
    exact setIntegral_congr_fun (measurableSet_Ico.prod MeasurableSet.univ) fun x _ => h1 x
  refine ⟨hsum, ?_⟩
  rw [hcell, integral_tsum hmeasF hsumL]
  rfl

/-- **Off-diagonal tail bound for `oscGram`** (SP 2894-2895, 2905-2912): for `IsSeedKernels κ`,
there exists `C_tail ≥ 0` such that for all `d ≥ 1` and `k, j : Fin 2`,
`‖∑' n : ℤ, (if n = 0 then 0 else oscGramTerm κ d k j n)‖ ≤ C_tail / d ^ 2`. -/
theorem oscGram_tail {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ C_tail : ℝ, 0 ≤ C_tail ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ k j : Fin 2,
      ‖∑' n : ℤ, (if n = 0 then (0 : ℂ) else oscGramTerm κ d k j n)‖ ≤ C_tail / d ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := oscGramCross_bound hκ
  have hS : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hS_nonneg : 0 ≤ ∑' n : ℤ, 1 / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => by positivity
  refine ⟨K * ∑' n : ℤ, 1 / (n : ℝ) ^ 2, mul_nonneg hK0 hS_nonneg, fun {d} hd k j => ?_⟩
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hterm : ∀ n : ℤ, ‖(if n = 0 then (0 : ℂ) else oscGramTerm κ d k j n)‖ ≤
      K / d ^ 2 * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hn, ↓reduceIte]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hb := hK k j ((n : ℝ) * d)
      unfold oscGramTerm
      have hnd : (0 : ℝ) < ((n : ℝ) * d) ^ 2 := by
        have : (n : ℝ) * d ≠ 0 := mul_ne_zero hnR hdpos.ne'
        positivity
      calc ‖∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) (y.1 + (n : ℝ) * d, y.2)‖
          ≤ K / (1 + |(n : ℝ) * d|) ^ 2 := hb
        _ ≤ K / ((n : ℝ) * d) ^ 2 := by
            apply div_le_div_of_nonneg_left hK0 hnd
            nlinarith [sq_abs ((n : ℝ) * d), abs_nonneg ((n : ℝ) * d)]
        _ = K / d ^ 2 * (1 / (n : ℝ) ^ 2) := by field_simp
  have hnorm : Summable (fun n : ℤ => ‖(if n = 0 then (0 : ℂ) else oscGramTerm κ d k j n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hS.mul_left _)
  calc ‖∑' n : ℤ, (if n = 0 then (0 : ℂ) else oscGramTerm κ d k j n)‖
      ≤ ∑' n : ℤ, ‖(if n = 0 then (0 : ℂ) else oscGramTerm κ d k j n)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℤ, K / d ^ 2 * (1 / (n : ℝ) ^ 2) :=
        hnorm.tsum_le_tsum hterm (hS.mul_left _)
    _ = K / d ^ 2 * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := tsum_mul_left
    _ = (K * ∑' n : ℤ, 1 / (n : ℝ) ^ 2) / d ^ 2 := by ring

/-- Quantitative `O(d⁻²)` approximation of `oscGram κ d k j` by its `n = 0` planar pairing
`∫ y, κ.lamP k y * movD (κ.e j) y`. -/
theorem oscGram_sub_zero_term_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ C_tail : ℝ, 0 ≤ C_tail ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ k j : Fin 2,
      ‖oscGram κ d k j - ∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) y‖ ≤ C_tail / d ^ 2 := by
  obtain ⟨C_tail, hC_tail0, htail⟩ := oscGram_tail hκ
  refine ⟨C_tail, hC_tail0, fun {d} hd k j => ?_⟩
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨hsum, hunf⟩ := oscGram_unfold hκ hd_pos k j
  have hsplit := hsum.tsum_eq_add_tsum_ite 0
  have h0 : oscGramTerm κ d k j 0 = ∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) y := by
    unfold oscGramTerm
    simp
  have hrest : oscGram κ d k j - ∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) y =
      ∑' n : ℤ, (if n = 0 then (0 : ℂ) else oscGramTerm κ d k j n) := by
    rw [hunf, hsplit, h0, add_sub_cancel_left]
  rw [hrest]
  exact htail hd k j

/-! ## 3. Periodization identity for `movOscRes` pairing and `seedEll` sector representation -/

/-- On `movingCell ν (ν ^ (-2 : ℝ)) r`, the pairing of `perLam0 κ d k` against
`OscillatorForceSub.movOscRes κ ν r j` equals `(clockTheta ν r : ℂ)⁻¹ * oscGram κ d k j`. -/
theorem integral_perLam0_mul_movOscRes_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (k j : Fin 2) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
      perLam0 κ d k y * movOscRes κ ν r j y =
      (clockTheta ν r : ℂ)⁻¹ * oscGram κ d k j := by
  intro d
  have hcell : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell d := by
    unfold movingCell B0579.cell d
    rfl
  rw [hcell]
  have hcongr : (fun y : ℝ × ℝ => perLam0 κ d k y * movOscRes κ ν r j y) =
      fun y : ℝ × ℝ =>
        (clockTheta ν r : ℂ)⁻¹ * (perLam0 κ d k y * perSum d (movD (κ.e j)) y) := by
    funext y
    rw [movOscRes_eq_perSum_movD hκ hν hr j y]
    ring
  rw [hcongr, integral_const_mul]
  rfl

/-- Complex-plane version of `movD (κ.e j)` obtained via `z ↦ (z.re, z.im)`. -/
def movDPlanar (κ : PlanarFrameKernels) (j : Fin 2) (z : ℂ) : ℂ :=
  movD (κ.e j) (z.re, z.im)

theorem movDPlanar_planeToC (κ : PlanarFrameKernels) (j : Fin 2) (y : ℝ × ℝ) :
    movDPlanar κ j (planeToC y) = movD (κ.e j) y := by
  unfold movDPlanar planeToC
  simp

theorem contDiff_movDPlanar {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    ContDiff ℝ ∞ (movDPlanar κ j) := by
  have hmovD : ContDiff ℝ ∞ (movD (κ.e j)) := contDiff_movD_seed hκ j
  have hpair : ContDiff ℝ ∞ (fun z : ℂ => (z.re, z.im)) :=
    Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  exact hmovD.comp hpair

/-- Sector representation of the `n = 0` planar pairing `∫ y, κ.lamP k y * movD (κ.e j) y` via
`seedBiorthExt_proof` and `PartI.seedFunctional_proof`. -/
theorem oscGram_zero_term_eq_seedEll {κ : PlanarFrameKernels} {lam : ℂ} {h : ℝ → ℂ}
    {hh : MemLp h 2 B0010.xGMeasure} {ℓ : B0010.XG →L[ℂ] ℂ}
    (hIS : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y))
    (he1 : ∀ y, κ.e 1 y = starRingEnd ℂ (PartI.seedPlanar h (planeToC y)))
    (hcl : ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y, κ.lamP 0 y * f (planeToC y) =
        PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
      ∫ y, κ.lamP 1 y * f (planeToC y) =
        conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r))))
    (j : Fin 2) :
    ∫ y : ℝ × ℝ, κ.lamP 0 y * movD (κ.e j) y =
      PartI.seedEll h (Planar.NUE.Polar.angularSector (movDPlanar κ j) 2) ∧
    ∫ y : ℝ × ℝ, κ.lamP 1 y * movD (κ.e j) y =
      conj (PartI.seedEll h
        (fun r => conj (Planar.NUE.Polar.angularSector (movDPlanar κ j) (-2) r))) := by
  have hκ : IsSeedKernels κ := ⟨lam, h, hh, ℓ, hIS, he0, he1, hcl⟩
  obtain ⟨hsm_e, hbd_e⟩ := seed_e_smooth_decay hκ
  have hsm_seed : ContDiff ℝ ∞ (PartI.seedPlanar h) := by
    have heq : PartI.seedPlanar h = fun z : ℂ => κ.e 0 (z.re, z.im) := by
      funext z
      have := he0 (z.re, z.im)
      unfold planeToC at this
      simp at this
      exact this.symm
    rw [heq]
    exact (hsm_e 0).comp (Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff)
  have hG_seed : ∃ C : ℝ, ∀ y : ℝ × ℝ,
      ‖PartI.seedPlanar h (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    obtain ⟨C0, _, hC0⟩ := hbd_e 0 0
    refine ⟨C0, fun y => ?_⟩
    rw [← he0 y]
    have h0 := hC0 y
    rw [norm_iteratedFDeriv_zero] at h0
    have hle : ‖κ.e 0 y‖ ≤ (1 + ‖y‖) * ‖κ.e 0 y‖ := by
      nlinarith [norm_nonneg y, norm_nonneg (κ.e 0 y)]
    exact hle.trans h0
  obtain ⟨_, C_D, _, hCD⟩ := movD_seed_uniform_decay hκ
  have hf_sm : ContDiff ℝ ∞ (movDPlanar κ j) := contDiff_movDPlanar hκ j
  have hf_bd : ∃ C : ℝ, ∀ y : ℝ × ℝ,
      ‖movDPlanar κ j (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨C_D, fun y => by rw [movDPlanar_planeToC]; exact hCD j y⟩
  have hext := seedBiorthExt_proof PartI.seedFunctional_proof lam h hh ℓ hIS hsm_seed hG_seed
    κ.lamP κ.lamP_cont κ.lamP_decay hcl (movDPlanar κ j) hf_sm hf_bd
  simp_rw [movDPlanar_planeToC] at hext
  exact hext

/-! ## 4. The planar pairing `⟨λ_k, D e_j⟩ = δ_{kj} κ_k` -/

/-- **Analytical Hypothesis 2 (`SeedPlanarOscPairing`, SP 2893, 2991-2992)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`) and a planar reference `P` (`IsPlanarReference P`),
the planar oscillator pairing `∫ y, κ.lamP k y * movD (κ.e j) y` equals `modeKappa P k` on the
diagonal (`k = j`) and `0` off the diagonal (`k ≠ j`, by angular sector `±2` orthogonality). -/
def SeedPlanarOscPairing (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ k j : Fin 2,
    ∫ y : ℝ × ℝ, κ.lamP k y * movD (κ.e j) y =
      if k = j then modeKappa P k else 0

/-- `seedEll h 0 = 0`. -/
theorem seedEll_zero (h : ℝ → ℂ) : PartI.seedEll h (fun _ => 0) = 0 := by
  unfold PartI.seedEll
  simp

/-- The seed `q = h e^{2iϑ}` is a smooth planar function. -/
theorem contDiff_seedPlanar_of {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {h : ℝ → ℂ}
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) :
    ContDiff ℝ ∞ (PartI.seedPlanar h) := by
  obtain ⟨hsm_e, -⟩ := seed_e_smooth_decay hκ
  have heq : PartI.seedPlanar h = fun z : ℂ => κ.e 0 (z.re, z.im) := by
    funext z
    have := he0 (z.re, z.im)
    unfold planeToC at this
    simp at this
    exact this.symm
  rw [heq]
  exact (hsm_e 0).comp (Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff)

/-- **The planar pairing** (SP 2893, 2991-2992): `⟨λ_k, D e_j⟩ = δ_{kj} κ_k`. The sectors of
`D e_j` are computed in polar form (`OscGramPolar.sectors_movD_seed`), `λ_k` represents `ℓ` on the
sectors `±2` (`oscGram_zero_term_eq_seedEll`), and `ℓ(Dq) = κ` (`OscGramKappa.kappa_eq_seedEll`). -/
theorem seedPlanarOscPairing (κ : PlanarFrameKernels) : SeedPlanarOscPairing κ := by
  intro hκ P hP
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, hcl⟩ := hκ
  have hκ' : IsSeedKernels κ := ⟨lam, h, hh, ℓ, hIS, he0, he1, hcl⟩
  have hsmF := contDiff_seedPlanar_of hκ' he0
  have hsm := OscGramPolar.contDiffOn_profile_of_seedPlanar hsmF
  have hkap := OscGramKappa.kappa_eq_seedEll hIS hsm P hP
  have hsec := fun r (hr : 0 < r) => OscGramPolar.sectors_movD_seed (κ := κ) he0 he1 hsmF hr
  have hmd : ∀ j : Fin 2, movDPlanar κ j = fun z : ℂ => movD (κ.e j) (z.re, z.im) :=
    fun j => rfl
  obtain ⟨hz0a, hz0b⟩ := oscGram_zero_term_eq_seedEll hIS he0 he1 hcl 0
  obtain ⟨hz1a, hz1b⟩ := oscGram_zero_term_eq_seedEll hIS he0 he1 hcl 1
  rw [hmd] at hz0a hz0b hz1a hz1b
  have hm0 : modeKappa P 0 = P.kappa := by simp [modeKappa]
  have hm1 : modeKappa P 1 = starRingEnd ℂ P.kappa := by simp [modeKappa]
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩
  · rw [if_pos rfl, hm0, hz0a, hkap]
    exact seedEll_congr h _ _ fun r hr => (hsec r hr).1
  · rw [if_neg (by decide), hz1a, ← seedEll_zero h]
    exact seedEll_congr h _ _ fun r hr => (hsec r hr).2.2.1
  · rw [if_neg (by decide), hz0b, ← map_zero (starRingEnd ℂ), ← seedEll_zero h]
    congr 1
    exact seedEll_congr h _ _ fun r hr => by rw [(hsec r hr).2.1, map_zero]
  · rw [if_pos rfl, hm1, hz1b, hkap]
    congr 1
    exact seedEll_congr h _ _ fun r hr => by rw [(hsec r hr).2.2.2, Complex.conj_conj]

end OscGramSub

/-- Top-level alias for `OscGramSub.SeedPlanarOscPairing`. -/
abbrev SeedPlanarOscPairing (κ : PlanarFrameKernels) : Prop :=
  OscGramSub.SeedPlanarOscPairing κ

/-! ## 5. Assembly of `PerOscGramApprox` through the dual kernel `D^# λ_k` -/

/-- **`PartIII-a:T21/c5/2/1/2`** (SP 2893, 2905-2912, 2991-2995): the unnormalised direct heat
pairing approximates `δ_{kj} κ_k / θ` to order `1/(θ d²)`.

By the dual periodization identity `movLam0DualHeat = θ⁻¹ P_d(D^# λ_k)`
(`ComplCouplingHeat.movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen`, with the jets of
`seedLamPJet2Decay_all`), `movLam0DirectHeat = θ⁻¹ ∫_cell P_d(D^# λ_k) P_d e_j`; the cell pairing
unfolds to `Σ_n ∫ (D^# λ_k)(y) e_j(y₁ + nd, y₂) dy` with an `O(d⁻²)` tail
(`OscGramDual.sub_zero_term_bound`), and the term `n = 0` is
`∫ (D^# λ_k) e_j = ∫ λ_k D e_j = δ_{kj} κ_k` (`OscGramIBP.integral_dualGen_mul`,
`OscGramSub.seedPlanarOscPairing`). -/
theorem perOscGramApprox (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PerOscGramApprox κ := by
  intro hκ P hP
  obtain ⟨hCD, C, hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  obtain ⟨hsm_e, hdec_e⟩ := OscillatorForceSub.seed_e_smooth_decay hκ
  have hPair := OscGramSub.seedPlanarOscPairing κ hκ P hP
  have hS0 : 0 ≤ ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := tsum_nonneg fun n => by positivity
  set Kt : ℝ := |7 / 2 * C| * |Ce| * (2080 * Real.pi) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 with hKt
  have hKt0 : 0 ≤ Kt := mul_nonneg (by positivity) hS0
  refine ⟨Kt, 1, hKt0, le_rfl, fun ν hν r hr hθ hd k j => ?_⟩
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  have hθpos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  -- the dual kernel `Ψ = D^# λ_k`
  have hΨc : Continuous (Gaussian.dualGen (κ.lamP k)) :=
    ComplCouplingHeat.continuous_dualGen (hCD k)
  have hΨb : ∀ y : ℝ × ℝ,
      ‖Gaussian.dualGen (κ.lamP k) y‖ ≤ (7 / 2 * C) * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
    fun y => ComplCouplingHeat.norm_dualGen_le_inv_sq (hCD k) (h0 k) (h1 k) (h2 k) y
  -- `movLam0DirectHeat = θ⁻¹ ∫_cell P_d(D^# λ_k) P_d e_j`
  obtain ⟨ht0, ht1, ht2⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 k) (h1 k) (h2 k)
  have hid : ∀ y, movLam0DualHeat κ ν r k y =
      (clockTheta ν r : ℂ)⁻¹ * perSum d (Gaussian.dualGen (κ.lamP k)) y := fun y =>
    ComplCouplingHeat.movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen κ hν.1 hr k (hCD k)
      ht0 ht1 ht2 y
  have hdirect : movLam0DirectHeat κ ν r k j =
      (clockTheta ν r : ℂ)⁻¹ *
        ∫ x in B0579.cell d, perSum d (Gaussian.dualGen (κ.lamP k)) x * perSum d (κ.e j) x := by
    unfold movLam0DirectHeat
    rw [← integral_const_mul]
    have hcell : movingCell ν (ν ^ (-2 : ℝ)) r = B0579.cell d := rfl
    rw [hcell]
    congr 1
    funext y
    rw [hid y]
    simp only [perE]
    ring
  -- the `O(d⁻²)` tail
  have htail := OscGramDual.sub_zero_term_bound hΨc (κ.e_cont j) hΨb (hCe j) hd
  -- the term `n = 0`: `∫ (D^# λ_k) e_j = ∫ λ_k D e_j = δ_{kj} κ_k`
  have hw1 : ∀ z : ℝ × ℝ, ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ 1 := fun z => by
    have h1z : 1 ≤ 1 + |z.1| + |z.2| := by linarith [abs_nonneg z.1, abs_nonneg z.2]
    have hi : (1 + |z.1| + |z.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1z
    have hi0 : 0 ≤ (1 + |z.1| + |z.2|)⁻¹ := by positivity
    nlinarith
  obtain ⟨B0, hB0, hb0⟩ := hdec_e j 0
  obtain ⟨B1, hB1, hb1⟩ := hdec_e j 1
  obtain ⟨B2, hB2, hb2⟩ := hdec_e j 2
  have hgw : ∀ y : ℝ × ℝ, OscGramIBP.gw y = Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := fun y => rfl
  have hzero : ∫ y : ℝ × ℝ, Gaussian.dualGen (κ.lamP k) y * κ.e j y =
      if k = j then modeKappa P k else 0 := by
    rw [OscGramIBP.integral_dualGen_mul (C := C) (B := B0 + B1 + B2) (hCD k)
      ((hsm_e j).of_le (by simp))
      (fun z => (h0 k z).trans (mul_le_of_le_one_right hC0 (hw1 z)))
      (fun z => (h1 k z).trans (mul_le_of_le_one_right hC0 (hw1 z)))
      (fun z => (h2 k z).trans (mul_le_of_le_one_right hC0 (hw1 z)))
      (fun y => by
        have := hb0 y
        rw [norm_iteratedFDeriv_zero] at this
        rw [hgw]
        nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8)])
      (fun y => by
        have := hb1 y
        rw [norm_iteratedFDeriv_one] at this
        rw [hgw]
        nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8)])
      (fun y => by
        have := hb2 y
        rw [hgw]
        nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8),
          norm_nonneg (iteratedFDeriv ℝ 2 (κ.e j) y), norm_nonneg y])]
    exact hPair k j
  have hif : (if k = j then modeKappa P k / (clockTheta ν r : ℂ) else 0) =
      (clockTheta ν r : ℂ)⁻¹ * ∫ y : ℝ × ℝ, Gaussian.dualGen (κ.lamP k) y * κ.e j y := by
    rw [hzero]
    split_ifs <;> simp [div_eq_inv_mul]
  rw [hdirect, hif, ← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hθpos.le]
  calc (clockTheta ν r)⁻¹ *
        ‖(∫ x in B0579.cell d, perSum d (Gaussian.dualGen (κ.lamP k)) x * perSum d (κ.e j) x) -
          ∫ y : ℝ × ℝ, Gaussian.dualGen (κ.lamP k) y * κ.e j y‖
      ≤ (clockTheta ν r)⁻¹ * (Kt / d ^ 2) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = Kt / (clockTheta ν r * d ^ 2) := by ring

end UnforcedLeray.Short.IIIa
