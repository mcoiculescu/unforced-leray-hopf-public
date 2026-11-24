import UnforcedLeray.Short.PartIIb.Sub.T12_6_2

/-!
# Part II-b, task `PartII-b:T12/7/7/2` (`DeqAbsSlice`): conditional reduction

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`DeqAbsSlice` follows from `BoxSlice` (the shared box slice bound of `Sub/T12_6_2.lean`, which is
also the engine of `DsolDuhamelIntegrable`) and `DeqAbsSupport` (the transpose test
`flatTranspose ν μ Ψ` is bounded and supported in a box `[σ,H] × [-R,R]²`, `σ > 0`, by
`deqTransposeTest`: compactly supported continuous functions in `{s > 0}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T12/7/7/2/1`**: `∑_i ‖flatTranspose ν μ Ψ x i‖` is bounded by `K` and vanishes
outside a box `[σ,H] × [-R,R]²` with `σ > 0` (from `deqTransposeTest`: continuous, compact
support inside `s > 0`). -/
def DeqAbsSupport : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ), IsPlanarSolTest Ψ →
    ∃ σ H R K : ℝ, 0 < σ ∧ 0 ≤ K ∧ ∀ x : Coord,
      ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖ ≤ K ∧
        (x ∉ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) →
          ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖ = 0)

theorem deqAbsIntegrand_eq (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (t : ℝ)
    (x : Coord) : deqAbsIntegrand ν μ G Ψ (t, x) =
      boxIntegrand ν μ G t x * ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖ := by
  unfold deqAbsIntegrand boxIntegrand
  by_cases h : 0 < t ∧ t < x.1
  · simp only [if_pos h]
  · simp only [if_neg h, zero_mul]

theorem deqAbsSlice_of (hB : BoxSlice) (hS : DeqAbsSupport) : DeqAbsSlice := by
  intro r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  obtain ⟨σ, H, R, K, hσ, hK, hKb⟩ := hS ν μ Ψ hΨ
  obtain ⟨C, hC⟩ := hB r hr1 hr3 μ hμ ν c hν hc G hG σ H R hσ
  refine ⟨H, K * C, ?_⟩
  filter_upwards [hC] with t ht
  have hpt : ∀ x : Coord, ENNReal.ofReal (deqAbsIntegrand ν μ G Ψ (t, x)) ≤
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)).indicator
        (fun x => ENNReal.ofReal K * ENNReal.ofReal (boxIntegrand ν μ G t x)) x := by
    intro x
    rw [deqAbsIntegrand_eq]
    have hB0 : 0 ≤ boxIntegrand ν μ G t x := by
      unfold boxIntegrand
      split_ifs
      · exact mul_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.2 (by assumption : 0 < t ∧ _).1.le))
          (norm_nonneg _)
      · exact le_rfl
    by_cases hx : x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (by
        rw [mul_comm K]; exact mul_le_mul_of_nonneg_left (hKb x).1 hB0)
    · rw [Set.indicator_of_notMem hx, (hKb x).2 hx]
      simp
  calc ∫⁻ x : Coord, ENNReal.ofReal (deqAbsIntegrand ν μ G Ψ (t, x))
      ≤ ∫⁻ x : Coord, (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)).indicator
        (fun x => ENNReal.ofReal K * ENNReal.ofReal (boxIntegrand ν μ G t x)) x :=
        lintegral_mono hpt
    _ = ENNReal.ofReal K * ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R),
          ENNReal.ofReal (boxIntegrand ν μ G t x) := by
        rw [lintegral_indicator (by measurability),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
            (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                (UnforcedLeray.Cyl.avgμ c)) t) := by gcongr
    _ = ENNReal.ofReal (K * C) * Set.indicator (Ioo (0 : ℝ) H)
            (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                (UnforcedLeray.Cyl.avgμ c)) t := by
        rw [ENNReal.ofReal_mul hK, mul_assoc]

end UnforcedLeray.Short.IIb
