import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F03dWindowBackNorm

/-!
# Part II-a, task `PartII-a:F09/3/1/4`: `AdjointWindowBackNorm` from the scalar chart bound

Source `the November 2 reference manuscript`
lines 1426-1442, 1435-1436 (all Jacobians on the window are bounded). The vector assembly
(`‖v‖^q ≤ 3^{q-1} Σ_c |v_c|^q`, Tonelli) is the copied argument of
`Tasks/F03dWindowBackNorm.lean`; only the scalar chart estimate is chart specific.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic

/-- Component `c` of `adjWindowLap` for a scalar function `g = D c`:
`adjComp ν τ₀ g (τ,y) = ν e^{-t} g(1 - e^{-t}, e^{-t/2} y)`, `t = τ₀ - τ`, on `|τ - τ₀| < 1`,
and `0` otherwise. -/
def adjComp (ν τ₀ : ℝ) (g : PS 3 → ℂ) (z : ℝ × Space) : ℂ :=
  if |z.1 - τ₀| < 1 then
    (ν : ℂ) * ((Real.exp (-(τ₀ - z.1)) : ℝ) : ℂ) *
      g (1 - Real.exp (-(τ₀ - z.1)), Real.exp (-(τ₀ - z.1) / 2) • z.2)
  else 0

theorem adjWindowLap_apply_comp (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ) (z : ℝ × Space) (c : Fin 3) :
    adjWindowLap ν τ₀ D z c = adjComp ν τ₀ (D c) z := by
  unfold adjWindowLap adjComp
  split_ifs <;> simp

/-- **Sub-lemma D1 (measurability).** `adjComp ν τ₀ g` is a.e. measurable for a.e. strongly
measurable `g`: the chart `(τ,y) ↦ (1 - e^{-(τ₀-τ)}, e^{-(τ₀-τ)/2} y)` is quasi measure preserving
(it is a diffeomorphism of the window onto `{θ ∈ (1-e, 1-e^{-1})}`; use its density
`e^{-5t/2}` as in `wd_qmp_window`, `Tasks/F03dWindowBackNorm.lean`). -/
def AdjCompAEMeas : Prop :=
  ∀ (ν τ₀ : ℝ) (g : PS 3 → ℂ), AEStronglyMeasurable g volume →
    AEMeasurable (adjComp ν τ₀ g) volume

/-- **Sub-lemma D2 (the scalar bound).** For `q > 1` there is `K ≥ 0` (depending only on `q`) with
`∫⁻ |adjComp ν τ₀ g|^q ≤ K · ‖ν g‖_q^q` (`dy = e^{3t/2} dx`, `dτ = dθ/(1-θ)`, weight
`e^{-t}`-powers bounded on `|t| < 1`; analogue of `wd_lintegral_le`). -/
def AdjCompBound : Prop :=
  ∀ q : ℝ, 1 < q → ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν τ₀ : ℝ) (g : PS 3 → ℂ),
    AEStronglyMeasurable g volume →
      ∫⁻ z : ℝ × Space, ‖adjComp ν τ₀ g z‖ₑ ^ q ≤
        ENNReal.ofReal K * eLpNorm (fun X => (ν : ℂ) * g X) (ENNReal.ofReal q) volume ^ q

/-- **`PartII-a:F09/3/1/4`, conditional on the two scalar leaves.** -/
theorem adjointWindowBackNorm_of (hM : AdjCompAEMeas) (hB : AdjCompBound) :
    AdjointWindowBackNorm := by
  intro q hq
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨K0, hK00, hKc⟩ := hB q hq
  have hC1 : (0 : ℝ) ≤ (3 : ℝ) ^ (q - 1) := by positivity
  have hK1 : (0 : ℝ) ≤ (3 : ℝ) ^ (q - 1) * K0 := mul_nonneg hC1 hK00
  have hK0 : (0 : ℝ) ≤ ((3 : ℝ) ^ (q - 1) * K0) ^ (1 / q) := Real.rpow_nonneg hK1 _
  refine ⟨((3 : ℝ) ^ (q - 1) * K0) ^ (1 / q), hK0, ?_⟩
  intro ν τ₀ D hD
  have hKq : ENNReal.ofReal (((3 : ℝ) ^ (q - 1) * K0) ^ (1 / q)) ^ q
      = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ENNReal.ofReal K0 := by
    rw [ENNReal.ofReal_rpow_of_nonneg hK0 hq0.le, one_div,
      Real.rpow_inv_rpow hK1 hq0.ne', ENNReal.ofReal_mul hC1]
  rw [hKq]
  have hGm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
      ∑ c, ‖adjComp ν τ₀ (D c) z‖ₑ ^ q) volume := by
    exact (Finset.aemeasurable_sum Finset.univ fun c _ =>
      ((hM ν τ₀ (D c) (hD c)).enorm).pow_const q).const_mul _
  have hpt : ∀ z : ℝ × Space, ‖adjWindowLap ν τ₀ D z‖ₑ ^ q ≤
      ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ∑ c, ‖adjComp ν τ₀ (D c) z‖ₑ ^ q := by
    intro z
    have := wd_enorm_rpow_le q hq.le (adjWindowLap ν τ₀ D z)
    simpa only [adjWindowLap_apply_comp] using this
  calc ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖adjWindowLap ν τ₀ D (τ, y)‖ₑ ^ q
      ≤ ∫⁻ τ, ∫⁻ y, ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, ‖adjComp ν τ₀ (D c) (τ, y)‖ₑ ^ q :=
        le_trans (lintegral_mono fun τ => lintegral_mono fun y => hpt (τ, y))
          (setLIntegral_le_lintegral _ _)
    _ = ∫⁻ z : ℝ × Space, ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, ‖adjComp ν τ₀ (D c) z‖ₑ ^ q :=
        (lintegral_prod _ hGm).symm
    _ = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, ∫⁻ z : ℝ × Space, ‖adjComp ν τ₀ (D c) z‖ₑ ^ q := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro c _
        exact ((hM ν τ₀ (D c) (hD c)).enorm).pow_const q
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, (ENNReal.ofReal K0 *
            eLpNorm (fun X => (ν : ℂ) * D c X) (ENNReal.ofReal q) volume ^ q) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hKc ν τ₀ (D c) (hD c)) zero_le
    _ = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ENNReal.ofReal K0 *
          ∑ c, eLpNorm (fun X => (ν : ℂ) * D c X) (ENNReal.ofReal q) volume ^ q := by
        rw [← Finset.mul_sum, mul_assoc]


end UnforcedLeray.Short.PartIIa
