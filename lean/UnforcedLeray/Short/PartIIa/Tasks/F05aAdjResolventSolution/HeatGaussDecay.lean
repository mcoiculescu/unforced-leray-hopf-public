import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.PhaseTestDerivBounded
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth
import UnforcedLeray.Lib.HeatR3.Decay
import UnforcedLeray.Lib.HeatR3.Bounded

/-!
# Part II-a, task `PartII-a:F05a`: Gaussian-times-compact tails of `heatGauss`

Target: `HeatGaussDecay` (defined in `Short/PartII-a/Sub/F05_1.lean`, line 153).

Source of record: `the November 2 reference manuscript`, lines 1446-1451
(the adjoint semigroup and the adjoint resolvent of a smooth compact spatial test). The
task brief cited lines 1411-1413, which contain no heat-kernel material.

Proof. Write `γ = Heat.kernel 1` and `G_ξ(p) = γ(ξ) • Φ₀(p.1, p.2 - w • ξ)`, so that
`heatGauss Φ₀ w = ∫ G_ξ dξ`. The map `p ↦ (p.1, p.2 - w • ξ)` is a translation, so
`D^k G_ξ(p) = γ(ξ) • D^kΦ₀(p.1, p.2 - w • ξ)` with no factor involving `w`. Differentiation under
the integral (`paramIntegralSmooth_proof`, with domination by `γ(ξ) M_k`) gives
`D^k heatGauss Φ₀ w (q) = ∫ γ(ξ) • D^kΦ₀(q.1, q.2 - w • ξ) dξ`.

If `‖q.2 - w • ξ‖ > R` the integrand vanishes (`D^kΦ₀` vanishes outside the ball of radius `R`).
Otherwise `‖q.2‖ ≤ R + |w| ‖ξ‖ ≤ |R| + |W| ‖ξ‖`, hence `1 + ‖q.2‖ ≤ K (1 + ‖ξ‖)` with
`K = 1 + |R| + |W|`. On this event `(K (1 + ‖ξ‖))^N (1 + ‖q.2‖)^{-N} ≥ 1`, so the integrand is
bounded by `M_k K^N (1 + ‖ξ‖)^N (1 + ‖q.2‖)^{-N} γ(ξ)`. This majorant is integrable by the
Gaussian moment bound `Heat.integrable_kernel_mul_weight`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

namespace HeatGaussDecayAux

/-- The `ξ`-th integrand of `heatGauss Φ₀ w`: `γ(ξ) • Φ₀(p.1, p.2 - w • ξ)`, `γ = Heat.kernel 1`. -/
def integrandG (Φ₀ : ℝ × Space → CVec3) (w : ℝ) (ξ : Space) (p : ℝ × Space) : CVec3 :=
  UnforcedLeray.Heat.kernel 1 ξ • Φ₀ (p.1, p.2 - w • ξ)

theorem contDiff_integrandG {Φ₀ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ₀) (w : ℝ) (ξ : Space) :
    ContDiff ℝ ∞ (integrandG Φ₀ w ξ) := by
  have hshift : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.1, p.2 - w • ξ) : ℝ × Space)) :=
    contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  have hc : ContDiff ℝ ∞ (fun _ : ℝ × Space => UnforcedLeray.Heat.kernel 1 ξ) := contDiff_const
  exact hc.smul (hΦ.comp hshift)

/-- The `k`-th derivative of the `ξ`-integrand: a translate of `D^kΦ₀`, scaled by `γ(ξ)`. -/
theorem iteratedFDeriv_integrandG {Φ₀ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ₀) (w : ℝ)
    (ξ : Space) (k : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ k (integrandG Φ₀ w ξ) p
      = UnforcedLeray.Heat.kernel 1 ξ • iteratedFDeriv ℝ k Φ₀ (p.1, p.2 - w • ξ) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space => Φ₀ (z + ((0 : ℝ), -(w • ξ)))) :=
    hΦ.comp (contDiff_id.add contDiff_const)
  have hfun : integrandG Φ₀ w ξ
      = fun z => UnforcedLeray.Heat.kernel 1 ξ • Φ₀ (z + ((0 : ℝ), -(w • ξ))) := by
    funext z
    have hz : (z.1, z.2 - w • ξ) = z + ((0 : ℝ), -(w • ξ)) :=
      Prod.ext (by simp) (by simp [sub_eq_add_neg])
    simp only [integrandG, hz]
  have hp : (p.1, p.2 - w • ξ) = p + ((0 : ℝ), -(w • ξ)) :=
    Prod.ext (by simp) (by simp [sub_eq_add_neg])
  rw [hfun, iteratedFDeriv_const_smul_apply' (hf.of_le (by exact_mod_cast le_top)).contDiffAt,
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ₀) k ((0 : ℝ), -(w • ξ)) p, hp]

/-- Differentiation under the integral sign is admissible for the family `ξ ↦ integrandG Φ₀ w ξ`:
the derivatives are continuous in `ξ`, and `‖D^kG_ξ‖ ≤ γ(ξ) M_k` with `γ` integrable. -/
theorem paramFamilyHyp_integrandG {Φ₀ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ₀)
    (hM : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × Space, ‖iteratedFDeriv ℝ k Φ₀ p‖ ≤ M) (w : ℝ) :
    ParamFamilyHyp (volume : Measure Space) (integrandG Φ₀ w) := by
  refine ⟨Filter.Eventually.of_forall fun ξ => contDiff_integrandG hΦ w ξ, ?_, ?_⟩
  · intro k p
    have hc : Continuous (iteratedFDeriv ℝ k Φ₀) :=
      hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have hsh : Continuous (fun ξ : Space => ((p.1, p.2 - w • ξ) : ℝ × Space)) :=
      continuous_const.prodMk (continuous_const.sub (continuous_id.const_smul w))
    have hcont : Continuous (fun ξ : Space =>
        UnforcedLeray.Heat.kernel 1 ξ • iteratedFDeriv ℝ k Φ₀ (p.1, p.2 - w • ξ)) :=
      (UnforcedLeray.Heat.continuous_kernel 1).smul (hc.comp hsh)
    simp only [iteratedFDeriv_integrandG hΦ w]
    exact hcont.aestronglyMeasurable
  · intro j
    obtain ⟨M, hM0, hMb⟩ := hM j
    refine ⟨fun ξ => UnforcedLeray.Heat.kernel 1 ξ * M,
      (UnforcedLeray.Heat.kernel_integrable one_pos).mul_const M,
      Filter.Eventually.of_forall fun ξ p => ?_⟩
    rw [iteratedFDeriv_integrandG hΦ w ξ j p, norm_smul,
      Real.norm_of_nonneg (UnforcedLeray.Heat.kernel_nonneg one_pos ξ)]
    exact mul_le_mul_of_nonneg_left (hMb _) (UnforcedLeray.Heat.kernel_nonneg one_pos ξ)

/-- The Gaussian-weight inequality: if `1 + t ≤ K (1 + s)` then `1 ≤ K^N (1 + s)^N (1 + t)^{-N}`. -/
theorem weight_one_le_aux {K t s : ℝ} (N : ℕ) (hK : 0 ≤ K) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h : 1 + t ≤ K * (1 + s)) :
    1 ≤ K ^ (N : ℝ) * (1 + s) ^ (N : ℝ) * (1 + t) ^ (-(N : ℝ)) := by
  have hb : 0 < 1 + t := by linarith
  have h1 : (1 + t) ^ (N : ℝ) ≤ (K * (1 + s)) ^ (N : ℝ) :=
    Real.rpow_le_rpow hb.le h (Nat.cast_nonneg N)
  rw [Real.mul_rpow hK (by linarith)] at h1
  have h2 : (1 + t) ^ (N : ℝ) * (1 + t) ^ (-(N : ℝ)) = 1 := by
    rw [← Real.rpow_add hb, add_neg_cancel, Real.rpow_zero]
  calc (1 : ℝ) = (1 + t) ^ (N : ℝ) * (1 + t) ^ (-(N : ℝ)) := h2.symm
    _ ≤ K ^ (N : ℝ) * (1 + s) ^ (N : ℝ) * (1 + t) ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hb.le _)

end HeatGaussDecayAux

/-- **Gaussian-times-compact tails of `heatGauss`**: for `P > 0` and a phase test `Φ₀`, every
`k`-th derivative of `heatGauss Φ₀ w` decays like `(1 + ‖y‖)^{-N}`, uniformly for `|w| ≤ W`. -/
theorem heatGaussDecay_proof : UnforcedLeray.Short.PartIIa.HeatGaussDecay := by
  intro P hP Φ₀ hΦ W k N
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨M, hM0, hMb⟩ := phaseTestDerivBounded_proof P hP Φ₀ hΦ k
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |R| + |W| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hI : Integrable (fun ξ : Space => UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ)) :=
    UnforcedLeray.Heat.integrable_kernel_mul_weight one_pos (Nat.cast_nonneg N)
  have hI0 : 0 ≤ ∫ ξ : Space, UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ) :=
    integral_nonneg fun ξ => mul_nonneg (UnforcedLeray.Heat.kernel_nonneg one_pos ξ)
      (Real.rpow_nonneg (by positivity) _)
  refine ⟨M * K ^ (N : ℝ) * ∫ ξ : Space, UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ),
    mul_nonneg (mul_nonneg hM0 (Real.rpow_nonneg hK0 _)) hI0, ?_⟩
  intro w hw q
  have hW : |w| ≤ |W| := hw.trans (le_abs_self W)
  have hfam := HeatGaussDecayAux.paramFamilyHyp_integrandG hΦ.smooth
    (phaseTestDerivBounded_proof P hP Φ₀ hΦ) w
  have hderiv : iteratedFDeriv ℝ k (heatGauss Φ₀ w) q
      = ∫ ξ : Space, iteratedFDeriv ℝ k (HeatGaussDecayAux.integrandG Φ₀ w ξ) q :=
    (paramIntegralSmooth_proof (ℝ × Space) Space volume
      (HeatGaussDecayAux.integrandG Φ₀ w) hfam).2 k q
  have hpt : ∀ ξ : Space,
      ‖iteratedFDeriv ℝ k (HeatGaussDecayAux.integrandG Φ₀ w ξ) q‖ ≤
        M * K ^ (N : ℝ) * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ))
          * (1 + ‖q.2‖) ^ (-(N : ℝ)) := by
    intro ξ
    rw [HeatGaussDecayAux.iteratedFDeriv_integrandG hΦ.smooth w ξ k q, norm_smul,
      Real.norm_of_nonneg (UnforcedLeray.Heat.kernel_nonneg one_pos ξ)]
    have hk : 0 ≤ UnforcedLeray.Heat.kernel 1 ξ := UnforcedLeray.Heat.kernel_nonneg one_pos ξ
    have hwt : 0 ≤ (1 + ‖ξ‖) ^ (N : ℝ) := Real.rpow_nonneg (by positivity) _
    have hKw : 0 ≤ K ^ (N : ℝ) := Real.rpow_nonneg hK0 _
    have hBn : 0 ≤ (1 + ‖q.2‖) ^ (-(N : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hRHS : 0 ≤ M * K ^ (N : ℝ) * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ))
        * (1 + ‖q.2‖) ^ (-(N : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hM0 hKw) (mul_nonneg hk hwt)) hBn
    by_cases hy : R < ‖q.2 - w • ξ‖
    · rw [PhaseTestDerivBoundedAux.iteratedFDeriv_eq_zero_of_outside hR k q.1 (q.2 - w • ξ) hy,
        norm_zero, mul_zero]
      exact hRHS
    · have hy' : ‖q.2 - w • ξ‖ ≤ R := not_lt.mp hy
      have htri : ‖q.2‖ ≤ ‖q.2 - w • ξ‖ + |w| * ‖ξ‖ := by
        calc ‖q.2‖ = ‖(q.2 - w • ξ) + w • ξ‖ := by rw [sub_add_cancel]
          _ ≤ ‖q.2 - w • ξ‖ + ‖w • ξ‖ := norm_add_le _ _
          _ = ‖q.2 - w • ξ‖ + |w| * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs]
      have hwξ : |w| * ‖ξ‖ ≤ |W| * ‖ξ‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg ξ)
      have hKξ : 1 + ‖q.2‖ ≤ K * (1 + ‖ξ‖) := by
        rw [hKdef]
        nlinarith [le_abs_self R, abs_nonneg R, abs_nonneg W, norm_nonneg ξ,
          mul_nonneg (abs_nonneg R) (norm_nonneg ξ)]
      have hone := HeatGaussDecayAux.weight_one_le_aux N hK0 (norm_nonneg _) (norm_nonneg ξ) hKξ
      have hMbound : ‖iteratedFDeriv ℝ k Φ₀ (q.1, q.2 - w • ξ)‖
          ≤ M * (K ^ (N : ℝ) * (1 + ‖ξ‖) ^ (N : ℝ) * (1 + ‖q.2‖) ^ (-(N : ℝ))) :=
        (hMb _).trans (le_mul_of_one_le_right hM0 hone)
      calc UnforcedLeray.Heat.kernel 1 ξ * ‖iteratedFDeriv ℝ k Φ₀ (q.1, q.2 - w • ξ)‖
          ≤ UnforcedLeray.Heat.kernel 1 ξ
              * (M * (K ^ (N : ℝ) * (1 + ‖ξ‖) ^ (N : ℝ) * (1 + ‖q.2‖) ^ (-(N : ℝ)))) :=
            mul_le_mul_of_nonneg_left hMbound hk
        _ = M * K ^ (N : ℝ) * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ))
              * (1 + ‖q.2‖) ^ (-(N : ℝ)) := by ring
  have hint : ‖∫ ξ : Space, iteratedFDeriv ℝ k (HeatGaussDecayAux.integrandG Φ₀ w ξ) q‖ ≤
      ∫ ξ : Space, M * K ^ (N : ℝ) * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ))
          * (1 + ‖q.2‖) ^ (-(N : ℝ)) :=
    norm_integral_le_of_norm_le ((hI.const_mul (M * K ^ (N : ℝ))).mul_const _)
      (Filter.Eventually.of_forall hpt)
  have hRHS : ∫ ξ : Space, M * K ^ (N : ℝ) * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ))
          * (1 + ‖q.2‖) ^ (-(N : ℝ))
      = M * K ^ (N : ℝ) * (∫ ξ : Space, UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (N : ℝ))
          * (1 + ‖q.2‖) ^ (-(N : ℝ)) := by
    rw [integral_mul_const, integral_const_mul]
  rw [hderiv]
  exact hint.trans_eq hRHS

end UnforcedLeray.Short.PartIIa
