import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.DiscMean
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CoverBall

/-!
# Leaf `PartII-b:T11/6/1`: an entire periodic `L^r` function is bounded

Proves `PeriodicEntireBounded` (defined in `Sub/T11_6.lean`). The argument is classical and not a
source claim (source of record: `the November 2 reference manuscript`, SP 2618 and
1923-1938).

For entire `f`, `c`-periodic in `Re z`, with `∫_{cell} ‖f‖ₑ^r ≠ ⊤` (`r ≥ 1`):

1. Mean value: `π ‖f z₀‖ₑ = ‖∫_{B(z₀,1)} f‖ₑ ≤ ∫⁻_{B(z₀,1)} ‖f‖ₑ` (`SeparateDisc`).
2. Pointwise `x ≤ 1 + x^r` for `r ≥ 1`, so `∫⁻_B ‖f‖ₑ ≤ vol(B) + ∫⁻_B ‖f‖ₑ^r`. No Hölder needed.
3. Covering: `∫⁻_B ‖f‖ₑ^r ≤ (2/c + 2) ∫⁻_{cell} ‖f‖ₑ^r` (`SeparateCover`).
4. `vol(B(z₀,1))` equals `vol(B(0,1))` by translation invariance, so the bound is uniform in `z₀`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Pointwise inequality `x ≤ 1 + x ^ r` on `ℝ≥0∞` for `r ≥ 1`. -/
theorem pebPointwise {r : ℝ} (hr : 1 ≤ r) (x : ℝ≥0∞) : x ≤ 1 + x ^ r := by
  by_cases hx : x ≤ 1
  · exact hx.trans le_self_add
  · have hx' : 1 < x := not_le.1 hx
    calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
      _ ≤ x ^ r := ENNReal.rpow_le_rpow_of_exponent_le hx'.le hr
      _ ≤ 1 + x ^ r := le_add_self

/-- Mean value bound for an entire `f`: `π ‖f z₀‖ₑ ≤ ∫⁻_{B(z₀,1)} ‖f‖ₑ`. -/
theorem pebMeanBound {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z0 : ℂ) :
    ENNReal.ofReal Real.pi * ‖f z0‖ₑ ≤ ∫⁻ w in ball z0 1, ‖f w‖ₑ := by
  have hmean := SeparateDisc.integral_ball_eq_of_differentiable hf z0 (R := 1) zero_le_one
  have hnorm : ‖(Real.pi * 1 ^ 2 : ℝ)‖ₑ = ENNReal.ofReal Real.pi := by
    rw [one_pow, mul_one, Real.enorm_eq_ofReal Real.pi_pos.le]
  calc ENNReal.ofReal Real.pi * ‖f z0‖ₑ = ‖∫ w in ball z0 1, f w‖ₑ := by
        rw [hmean, enorm_smul, hnorm]
    _ ≤ ∫⁻ w in ball z0 1, ‖f w‖ₑ := enorm_integral_le_lintegral_enorm f

/-- Covering bound: `∫⁻_{B(z₀,1)} ‖f‖ₑ^r ≤ (2/c + 2) ∫⁻_{cell} ‖f‖ₑ^r` for periodic entire `f`. -/
theorem pebCoverBound {c : ℝ} (hc : 0 < c) {r : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, f (z + (c : ℂ)) = f z) (z0 : ℂ) :
    ∫⁻ w in ball z0 1, ‖f w‖ₑ ^ r ≤
      ENNReal.ofReal (2 * 1 / c + 2) * ∫⁻ z in SeparateCover.cellC c, ‖f z‖ₑ ^ r := by
  have hG : Measurable (fun z : ℂ => ‖f z‖ₑ ^ r) :=
    (hf.continuous.measurable.enorm).pow_const r
  have hper' : ∀ z : ℂ, (fun z : ℂ => ‖f z‖ₑ ^ r) (z + (c : ℂ)) = (fun z : ℂ => ‖f z‖ₑ ^ r) z := by
    intro z
    simp only [hper z]
  exact SeparateCover.lintegral_ball_le_cellC_mul hc hG hper' z0 zero_le_one

/-- The uniform pointwise bound `π ‖f z₀‖ₑ ≤ vol(B(0,1)) + (2/c + 2) ∫⁻_{cell} ‖f‖ₑ^r`. -/
theorem pebUniformBound {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ z : ℂ, f (z + (c : ℂ)) = f z) (z0 : ℂ) :
    ENNReal.ofReal Real.pi * ‖f z0‖ₑ ≤
      volume (ball (0 : ℂ) 1) +
        ENNReal.ofReal (2 * 1 / c + 2) * ∫⁻ z in SeparateCover.cellC c, ‖f z‖ₑ ^ r := by
  calc ENNReal.ofReal Real.pi * ‖f z0‖ₑ ≤ ∫⁻ w in ball z0 1, ‖f w‖ₑ := pebMeanBound hf z0
    _ ≤ ∫⁻ w in ball z0 1, (1 + ‖f w‖ₑ ^ r) := lintegral_mono (fun w => pebPointwise hr _)
    _ = (∫⁻ w in ball z0 1, (1 : ℝ≥0∞)) + ∫⁻ w in ball z0 1, ‖f w‖ₑ ^ r :=
        lintegral_add_left measurable_const _
    _ = volume (ball (0 : ℂ) 1) + ∫⁻ w in ball z0 1, ‖f w‖ₑ ^ r := by
        rw [setLIntegral_const, one_mul, Measure.addHaar_ball_center volume z0 1]
    _ ≤ volume (ball (0 : ℂ) 1) +
          ENNReal.ofReal (2 * 1 / c + 2) * ∫⁻ z in SeparateCover.cellC c, ‖f z‖ₑ ^ r :=
        add_le_add le_rfl (pebCoverBound hc hf hper z0)

/-- A uniform extended-real bound `π ‖F z₀‖ₑ ≤ K` with `K ≠ ⊤` gives a real bound on `‖F‖`. -/
theorem pebOfMeanBound {F : ℂ → ℂ} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ z0 : ℂ, ENNReal.ofReal Real.pi * ‖F z0‖ₑ ≤ K) :
    ∃ C : ℝ, ∀ z : ℂ, ‖F z‖ ≤ C := by
  have hpi0 : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  have hpitop : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin : K * (ENNReal.ofReal Real.pi)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hK (ENNReal.inv_ne_top.2 hpi0)
  refine ⟨(K * (ENNReal.ofReal Real.pi)⁻¹).toReal, fun z0 => ?_⟩
  have hz := h z0
  have hle : ‖F z0‖ₑ ≤ K * (ENNReal.ofReal Real.pi)⁻¹ := by
    calc ‖F z0‖ₑ = (ENNReal.ofReal Real.pi)⁻¹ * (ENNReal.ofReal Real.pi * ‖F z0‖ₑ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpi0 hpitop, one_mul]
      _ ≤ (ENNReal.ofReal Real.pi)⁻¹ * K := by gcongr
      _ = K * (ENNReal.ofReal Real.pi)⁻¹ := mul_comm _ _
  calc ‖F z0‖ = (‖F z0‖ₑ).toReal := by simp
    _ ≤ (K * (ENNReal.ofReal Real.pi)⁻¹).toReal := ENNReal.toReal_mono hfin hle

/-- **Leaf `PartII-b:T11/6/1`.** An entire `f` that is `c`-periodic in `Re z` with
`∫_{-c/2 ≤ Re z < c/2} ‖f‖ₑ^r ≠ ⊤` (`c > 0`, `r ≥ 1`) is bounded. -/
theorem periodicEntireBounded : UnforcedLeray.Short.IIb.PeriodicEntireBounded := by
  unfold PeriodicEntireBounded
  intro c r f hc hr hf hper hI
  refine pebOfMeanBound (F := f)
    (K := volume (ball (0 : ℂ) 1) +
      ENNReal.ofReal (2 * 1 / c + 2) * ∫⁻ z in SeparateCover.cellC c, ‖f z‖ₑ ^ r) ?_ ?_
  · exact ENNReal.add_ne_top.2 ⟨measure_ball_lt_top.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI⟩
  · exact fun z0 => pebUniformBound hc hr hf hper z0

end UnforcedLeray.Short.IIb
