import UnforcedLeray.Short.PartIIb.Sub.T12_7

/-!
# Part II-b, task `PartII-b:T12/7/7` (`DeqAbsIntegrable`): conditional reduction

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

This file reduces `DeqAbsIntegrable` to three analytic leaves, stated as `Prop`s:

* `DeqAbsMeas`: the integrand is a.e. strongly measurable on `ℝ × Coord` (Duhamel-type
  measurability, from a strongly measurable representative of `G`);
* `DeqAbsSlice`: the `z`-integral of the integrand at a.e. age `t > 0` is bounded by
  `C t^{Re μ - 1} ‖G(t, ·)‖_{L^r(Cyl.avgμ c)}` on `t < H` and vanishes for `t ≥ H` (kernel
  convolution bound, periodic `L^r` cell bound, compact support of `flatTranspose`);
* `DeqAbsTime`: `∫_{(0,H)} t^{Re μ - 1} ‖G(t, ·)‖_{L^r} dt < ∞` (Hölder in `t` against the
  `H_r` weight, exponent `a_r > 0`).

`deqAbsIntegrable_of` (Tonelli on `ℝ × Coord`) assembles them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The integrand of `DeqAbsIntegrable` as a function of `p = (t, (s, z))`. -/
def deqAbsIntegrand (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (p : ℝ × Coord) : ℝ :=
  if 0 < p.1 ∧ p.1 < p.2.1 then
    ‖(((p.1 / p.2.1 : ℝ) : ℂ) ^ μ)‖ * p.1⁻¹ *
      ‖flatHeat (ν * (p.2.1 - p.1)) (fun w => G (p.1, w)) p.2.2‖ *
      ∑ i : Fin 2, ‖flatTranspose ν μ Ψ p.2 i‖
  else 0

theorem deqAbsIntegrand_nonneg (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ)
    (p : ℝ × Coord) : 0 ≤ deqAbsIntegrand ν μ G Ψ p := by
  unfold deqAbsIntegrand
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.2 h.1.le))
      (norm_nonneg _)) (Finset.sum_nonneg fun i _ => norm_nonneg _)
  · exact le_rfl

theorem deqAbsIntegrand_zero_of_le (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ)
    {t : ℝ} (ht : t ≤ 0) (x : Coord) : deqAbsIntegrand ν μ G Ψ (t, x) = 0 := by
  unfold deqAbsIntegrand
  split_ifs with h
  · exact absurd h.1 (not_lt.2 ht)
  · rfl

/-- Leaf (measurability): the integrand is a.e. strongly measurable on `ℝ × Coord`. -/
def DeqAbsMeas : Prop :=
  ∀ (r : ℝ), 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
      AEStronglyMeasurable (deqAbsIntegrand ν μ G Ψ) (volume : Measure (ℝ × Coord))

/-- Leaf (slice bound): for some `H` and `C`, for a.e. `t > 0` the `x`-integral of the integrand at
age `t` is at most `C · t^{Re μ - 1} ‖G(t, ·)‖_{L^r(Cyl.avgμ c)}` for `t < H`, and `0` beyond. -/
def DeqAbsSlice : Prop :=
  ∀ (r : ℝ), 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
      ∃ H C : ℝ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∫⁻ x : Coord, ENNReal.ofReal (deqAbsIntegrand ν μ G Ψ (t, x)) ≤
          ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
            (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                (UnforcedLeray.Cyl.avgμ c)) t

/-- Leaf (time integrability): the weighted `L^r` slice norms are integrable on `(0, H)`, by Hölder
against the `H_r` weight `s^{r/2 - 5/2}`; the exponent condition is exactly `a_r > 0`. -/
def DeqAbsTime : Prop :=
  ∀ (r : ℝ), 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ c : ℝ, 0 < c →
    ∀ G : CProf, InHr c r G → ∀ H : ℝ,
      ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (μ.re - 1)) *
        eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
          (UnforcedLeray.Cyl.avgμ c) < ⊤

/-- **Conditional assembly.** `DeqAbsIntegrable` follows from the measurability leaf, the slice
bound and the time integrability, by Tonelli on `ℝ × Coord`. -/
theorem deqAbsIntegrable_of (hM : DeqAbsMeas) (hB : DeqAbsSlice) (hT : DeqAbsTime) :
    DeqAbsIntegrable := by
  intro r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  obtain ⟨H, C, hB'⟩ := hB r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  have hmeas := hM r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  -- the bound holds for every `t`, since it is trivial for `t ≤ 0`
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫⁻ x : Coord, ENNReal.ofReal (deqAbsIntegrand ν μ G Ψ (t, x)) ≤
        ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
          (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c)) t := by
    have h1 := (ae_restrict_iff' measurableSet_Ioi).1 hB'
    filter_upwards [h1] with t ht
    by_cases htp : 0 < t
    · exact ht htp
    · have hz : ∀ x : Coord, ENNReal.ofReal (deqAbsIntegrand ν μ G Ψ (t, x)) = 0 := fun x => by
        rw [deqAbsIntegrand_zero_of_le ν μ G Ψ (not_lt.1 htp) x, ENNReal.ofReal_zero]
      simp [hz]
  refine ⟨hmeas, ?_⟩
  show HasFiniteIntegral (deqAbsIntegrand ν μ G Ψ) (volume : Measure (ℝ × Coord))
  unfold HasFiniteIntegral
  have hP0 : AEMeasurable (fun p : ℝ × Coord => ‖deqAbsIntegrand ν μ G Ψ p‖ₑ)
      (volume : Measure (ℝ × Coord)) := hmeas.enorm
  rw [Measure.volume_eq_prod] at hP0 ⊢
  rw [lintegral_prod _ hP0]
  have hinner : ∀ t : ℝ, ∫⁻ x : Coord, ‖deqAbsIntegrand ν μ G Ψ (t, x)‖ₑ =
      ∫⁻ x : Coord, ENNReal.ofReal (deqAbsIntegrand ν μ G Ψ (t, x)) := fun t =>
    lintegral_congr fun x => Real.enorm_of_nonneg (deqAbsIntegrand_nonneg ν μ G Ψ (t, x))
  calc ∫⁻ t : ℝ, ∫⁻ x : Coord, ‖deqAbsIntegrand ν μ G Ψ (t, x)‖ₑ ∂(volume : Measure Coord)
        ∂(volume : Measure ℝ)
      ≤ ∫⁻ t : ℝ, ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
          (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c)) t ∂(volume : Measure ℝ) :=
        lintegral_mono_ae (by
          filter_upwards [hae] with t ht
          rw [hinner t]
          exact ht)
    _ = ENNReal.ofReal C * ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (μ.re - 1)) *
          eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
            (UnforcedLeray.Cyl.avgμ c) ∂(volume : Measure ℝ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator measurableSet_Ioo]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hT r hr1 hr3 μ hμ c hc G hG H)

end UnforcedLeray.Short.IIb
