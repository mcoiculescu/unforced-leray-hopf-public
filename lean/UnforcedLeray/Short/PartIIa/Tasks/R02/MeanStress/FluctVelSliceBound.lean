import UnforcedLeray.Short.PartIIa.Sub.R02_6
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.FluctVelSliceBound.Calc

/-!
# Part II-a, task `PartII-a:R02/MeanStress/FluctVelSliceBound`: the slice bound of the velocity
fluctuation (source lines 439-446, `sct:fluctuation`, velocity block)

Target: `FluctVelSliceBound` (`Sub/R02_6.lean`), from the hypotheses

* `TrainFluctuationDecay` (`Short/PartI/StatementsTrain.lean`), second block: the weighted sup norm of
  the age-spatial jet of `hfluct c (tr.v r)` at age `s`, with `c = ν^(-ρ)`;
* `SliceJetBound` (`Sub/R02_2.lean`): a nested slice derivative of a profile is bounded by the norm of
  the age-spatial jet of the profile;
* `MeanStressSmooth` (`Sub/R02_6.lean`): the components of the velocity fluctuation are smooth.

Route. Fix `ν`, `tr`, `j`, `q`, `η`, `s > 0`.
1. `hF ρ (2m') l i` gives the weighted sup norm bound of `ageJet l i (hfluct c (tr.v ·)) s`.
   `pointwise_of_wSupNorm` and `sqrt_jap_even` turn it into a pointwise bound for `(1+η²)^{m'}` times
   the norm of this jet.
2. `SliceJetBound` for the scalar profile `F r z = hfluct c (tr.v r ·_j) z` (smooth by `MeanStressSmooth`
   and `contDiffOn_trainProfile_of`) bounds the left-hand side by `‖ageJet l i F s (q,η)‖`.
3. `fvs_ageJet_proj_le` (helper `FluctVelSliceBound/Calc.lean`): the scalar profile is the `j`-th
   coordinate of the vector profile, so its jet is bounded by the jet of the vector profile.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (hfluct)

/-- **Slice bound for the velocity fluctuation** (`FluctVelSliceBound`, source lines 439-446): from the
train fluctuation decay, the slice jet bound and the smoothness of the mean stress. -/
theorem fluctVelSliceBound_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hSJ : UnforcedLeray.Short.PartIIa.SliceJetBound)
    (hSm : UnforcedLeray.Short.PartIIa.MeanStressSmooth) :
    UnforcedLeray.Short.PartIIa.FluctVelSliceBound := by
  intro ρ m' i l hρ
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, H⟩ := hF ρ hρ (2 * m') l i
  refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
  intro ν hν hνν₀ tr hb j q η s hs
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have Hs := H ν hν hνν₀ tr hb s hs
  simp only [UnforcedLeray.Short.PartI.trainPeriod] at Hs
  have hbase : 0 ≤ 1 + ν ^ (-ρ) + ν⁻¹ := by
    have := inv_pos.2 hν
    linarith
  have hB : 0 ≤ polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) :=
    mul_nonneg (mul_nonneg hC.le (pow_nonneg hbase N)) (Real.exp_pos _).le
  have hw := Hs.2.1.2
  -- pointwise bound on the weighted vector jet
  have hpt : ∀ z : ℝ × ℝ, (1 + z.2 ^ 2) ^ m' *
      ‖UnforcedLeray.Short.PartI.ageJet l i (fun r => hfluct (ν ^ (-ρ)) (tr.v r)) s z‖ ≤
        polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2)) := by
    intro z
    have h := pointwise_of_wSupNorm hB hw z
    rw [sqrt_jap_even] at h
    exact h
  -- the scalar profile of the `j`-th coordinate and its coordinate identity
  have hFG : ∀ r : ℝ, 0 < r → ∀ z : ℝ × ℝ,
      hfluct (ν ^ (-ρ)) (fun w => tr.v r w j) z = (hfluct (ν ^ (-ρ)) (tr.v r) z) j :=
    fun r hr z => fvs_hfluct_apply (ν ^ (-ρ)) (tr.v r) (fvs_slice_continuous tr hr.le) j z
  -- the vector profile is smooth on `(0,∞) × Plane`
  have hG : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => hfluct (ν ^ (-ρ)) (tr.v x.1) x.2) (Ioi 0 ×ˢ univ) := by
    refine (contDiffOn_piLp 2).2 (fun k => ?_)
    refine ((hSm ν (ν ^ (-ρ)) hν hc tr hb).2.2 k).congr (fun x hx => ?_)
    exact (fvs_hfluct_apply (ν ^ (-ρ)) (tr.v x.1)
      (fvs_slice_continuous tr (le_of_lt (Set.mem_Ioi.mp hx.1))) k x.2).symm
  -- slice bound for the scalar profile
  have hprof := contDiffOn_trainProfile_of
    (F := fun r z => hfluct (ν ^ (-ρ)) (fun w => tr.v r w j) z)
    ((hSm ν (ν ^ (-ρ)) hν hc tr hb).2.2 j)
  have hslice := hSJ (fun r z => hfluct (ν ^ (-ρ)) (fun w => tr.v r w j) z) hprof i 0 l q η s hs
  simp only [iteratedDeriv_zero, Nat.add_zero] at hslice
  have hkey := fvs_ageJet_proj_le (G := fun r z => hfluct (ν ^ (-ρ)) (tr.v r) z) hG j
    (fun r z => hfluct (ν ^ (-ρ)) (fun w => tr.v r w j) z) hFG i l hs (q, η)
  exact le_trans (mul_le_mul_of_nonneg_left (hslice.trans hkey) (by positivity)) (hpt (q, η))

end UnforcedLeray.Short.PartIIa
