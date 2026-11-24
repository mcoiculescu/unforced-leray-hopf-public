import UnforcedLeray.Short.PartIIa.Sub.R02_3
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-a, task `PartII-a:R02/3/4`: the pointwise mean-remainder bound

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`, remainder bound with `p = ∞`).

Target: `meanRemPointwise_of` gives `MeanRemPointwise` (`Sub/R02_3.lean`) from

* `TrainMeanExpansion` (`hM`), read at `p = ⊤` (`1 ≤ ⊤` is `le_top`);
* `MeanRemainderSmooth` (`hSm`), giving the joint smoothness of `R_N` on `(0,∞) × ℝ`;
* `SliceDerivContinuous` (`hSC`), giving continuity of `η ↦ ∂_η^{b'} ∂_s^{l'} R_N(s, η)`;
* `EssSupPointwise` (`hES`), giving the pointwise bound from the `L^∞` bound of a continuous
  function.

Proof: fix `ν, tr, s ≥ 1`. The third conjunct of `TrainMeanExpansion` at `p = ⊤` gives the
`L^∞` bound of `η ↦ η^{m'} ∂_η^{b'} ∂_s^{l'} R_N(s, η)` by
`polyP C M ν c * s^{(m'-b'-2N-3)/2 - l' + (⊤.toReal)⁻¹/2}`, and `⊤.toReal = 0` removes the last
term. The function is continuous, the bound is nonnegative, so `EssSupPointwise` gives the
pointwise bound at each `η`. Finally `|η^{m'} d| = |η|^{m'} |d|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (meanRemainder)

theorem meanRemPointwise_of
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hSm : UnforcedLeray.Short.PartIIa.MeanRemainderSmooth)
    (hSC : UnforcedLeray.Short.PartIIa.SliceDerivContinuous)
    (hES : UnforcedLeray.Short.PartIIa.EssSupPointwise) :
    UnforcedLeray.Short.PartIIa.MeanRemPointwise := by
  intro ρ N m' b' l' hρ
  obtain ⟨C, M, ν₀, hC, hν₀, hbd⟩ := hM ρ hρ N m' b' l' ⊤ le_top
  refine ⟨C, M, ν₀, hν₀, fun ν hν hνle tr hb s hs η => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  obtain ⟨-, -, hR, -⟩ := hbd ν hν hνle tr hb
  have hR' := hR s hs
  simp only [ENNReal.toReal_top, inv_zero, zero_div, add_zero] at hR'
  have hD : Continuous (fun η : ℝ =>
      iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanRemainder tr N r e) s) η) :=
    hSC (fun r e => meanRemainder tr N r e) (hSm ν (ν ^ (-ρ)) hν hc tr hb N) b' l' s (by linarith)
  have hfc : Continuous (fun η : ℝ =>
      η ^ m' * iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanRemainder tr N r e) s) η) :=
    (continuous_pow m').mul hD
  have hbase : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.mpr hν
    linarith
  have hB0 : 0 ≤ polyConst C M ν (ν ^ (-ρ)) * s ^ (((m' : ℝ) - b' - 2 * N - 3) / 2 - l') := by
    unfold polyConst
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg hbase.le M))
      (Real.rpow_nonneg (by linarith) _)
  have hES' := hES _ hfc _ hB0 hR'
  calc |η| ^ m' * |iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanRemainder tr N r e) s) η|
      = |η ^ m' * iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanRemainder tr N r e) s) η| := by
        rw [abs_mul, abs_pow]
    _ ≤ _ := hES' η

end UnforcedLeray.Short.PartIIa
