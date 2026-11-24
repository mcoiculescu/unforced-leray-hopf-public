import UnforcedLeray.Short.PartIIa.Sub.N02_4
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.Pt
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.L2

/-!
# Part II-a, task `PartII-a:N02/4/1` (`NzCutoffApprox`): the cutoff approximation

Target: `nzCutoffApprox : NzCutoffApprox` (`Split.lean`, lemma (d)). Source of record
`the November 2 reference manuscript`, lines 1729-1736 (zero frequency cut-offs
`L_0 = ε^{-1}` in the source, here `L = ε^{-1/2}` with `χ(η/L) = χ(√ε η)`) and the dependence on
constants of lines 1737-1743.

Route: for `NearGradMember`/`NearStreamMember` applied to the band tests `χ(√ε η) φ` and
`χ(√ε η) ψ`, the approximants are `toLp (cgradC ε (χ φ))` and `toLp (streamC ε (χ ψ))`. The
pointwise bound (`Pt.lean`) and the `L²` bound (`L2.lean`) give
`‖toLp (cgradC 0 φ) - toLp (cgradC ε (χφ))‖ ≤ 2 K √ε Σ (moments)`, and the moments are at most
`nzPot c φ ψ`. Here `K = 3 + B1 + B2` with `B1, B2` the bounds of `χ'` and `t χ'(t)`. The number
`C = 2K` does not depend on `c`, `ε`, `φ`, `ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

lemma nzco_nzSq_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (a j : ℕ)
    (g : Profile → E) : 0 ≤ nzSq c a j g :=
  integral_nonneg fun p => by positivity

lemma nzco_momSum_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (g : Profile → E) : 0 ≤ nzMomSum c g :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ =>
    Real.rpow_nonneg (nzco_nzSq_nonneg c a j g) _

/-- One summand of `nzMomSum` (`a, j ∈ {0, 1}`) is at most the sum. -/
lemma nzco_mom_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (g : Profile → E)
    (a j : ℕ) (ha : a ∈ Finset.range 2) (hj : j ∈ Finset.range 2) :
    (nzSq c a j g) ^ (1 / 2 : ℝ) ≤ nzMomSum c g := by
  unfold nzMomSum
  calc (nzSq c a j g) ^ (1 / 2 : ℝ)
      ≤ ∑ j' ∈ Finset.range 2, (nzSq c a j' g) ^ (1 / 2 : ℝ) :=
        Finset.single_le_sum (f := fun j' => (nzSq c a j' g) ^ (1 / 2 : ℝ))
          (fun j' _ => Real.rpow_nonneg (nzco_nzSq_nonneg c a j' g) _) hj
    _ ≤ ∑ a' ∈ Finset.range 2, ∑ j' ∈ Finset.range 2, (nzSq c a' j' g) ^ (1 / 2 : ℝ) :=
        Finset.single_le_sum (f := fun a' => ∑ j' ∈ Finset.range 2, (nzSq c a' j' g) ^ (1 / 2 : ℝ))
          (fun a' _ => Finset.sum_nonneg fun j' _ => Real.rpow_nonneg (nzco_nzSq_nonneg c a' j' g) _)
          ha

/-- The two moments with `j = 0` and `a ∈ {0, 1}` together are at most `nzMomSum`. -/
lemma nzco_mom_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (g : Profile → E) :
    (nzSq c 0 0 g) ^ (1 / 2 : ℝ) + (nzSq c 1 0 g) ^ (1 / 2 : ℝ) ≤ nzMomSum c g := by
  unfold nzMomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h01 := Real.rpow_nonneg (nzco_nzSq_nonneg c 0 1 g) (1 / 2 : ℝ)
  have h11 := Real.rpow_nonneg (nzco_nzSq_nonneg c 1 1 g) (1 / 2 : ℝ)
  linarith

/-- The main theorem. -/
theorem nzCutoffApprox : NzCutoffApprox := by
  intro hgrad hstream
  obtain ⟨B1, B2, hB1, hB2, hBd⟩ := nzco_bounds
  have hK : 0 ≤ 3 + B1 + B2 := by linarith
  refine ⟨2 * (3 + B1 + B2), by linarith,
    fun c ε hc hε hε1 φ ψ hφs hψs hφp hψp hband h1 h2 h3 h4 h5 h6 hG hS => ?_⟩
  obtain ⟨s0, s1, hs0, hbandF⟩ := hband
  have hsp : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hM : 0 ≤ Real.sqrt ε * (3 + B1 + B2) := mul_nonneg (Real.sqrt_nonneg _) hK
  -- the cut-off band tests
  have hTφ : IsCTest c (nzcoCut ε φ) := by
    refine ⟨nzcoCut_contDiff ε hφs, nzcoCut_periodic c ε hφp, s0, s1, 2 / Real.sqrt ε, hs0,
      fun p hp => ?_⟩
    have hφne : φ p ≠ 0 := fun h => hp (by simp [nzcoCut, h])
    have hw : nzcoW ε p ≠ 0 := fun h => hp (by simp [nzcoCut, h])
    refine ⟨hbandF p (Or.inl hφne), ?_⟩
    have habs := nzcoW_abs_lt hw
    rw [abs_mul, abs_of_pos hsp] at habs
    rw [le_div_iff₀ hsp]
    linarith [mul_comm (Real.sqrt ε) |p.2.2|]
  have hTψ : IsCTest c (nzcoCut ε ψ) := by
    refine ⟨nzcoCut_contDiff ε hψs, nzcoCut_periodic c ε hψp, s0, s1, 2 / Real.sqrt ε, hs0,
      fun p hp => ?_⟩
    have hψne : ψ p ≠ 0 := fun h => hp (by simp [nzcoCut, h])
    have hw : nzcoW ε p ≠ 0 := fun h => hp (by simp [nzcoCut, h])
    refine ⟨hbandF p (Or.inr hψne), ?_⟩
    have habs := nzcoW_abs_lt hw
    rw [abs_mul, abs_of_pos hsp] at habs
    rw [le_div_iff₀ hsp]
    linarith [mul_comm (Real.sqrt ε) |p.2.2|]
  obtain ⟨hmG, hmemG⟩ := hgrad ε c (nzcoCut ε φ) hTφ
  obtain ⟨hmS, hmemS⟩ := hstream ε c (nzcoCut ε ψ) hTψ
  refine ⟨⟨hmG.toLp (cgradC ε (nzcoCut ε φ)), hmemG, ?_⟩,
    ⟨hmS.toLp (streamC ε (nzcoCut ε ψ)), hmemS, ?_⟩⟩
  · -- gradient part: the moments of `φ`, `∂_q φ`, `∂_η φ`
    have i1 : Integrable (fun p => ‖φ p‖ ^ 2) (measureH c) := by
      simpa using h1 0 (by simp) 0 (by simp)
    have i2 : Integrable (fun p => ‖opS φ p‖ ^ 2) (measureH c) := by
      simpa using h1 1 (by simp) 0 (by simp)
    have i3 : Integrable (fun p => (|p.2.2| * ‖pdQ φ p‖) ^ 2) (measureH c) := by
      simpa [mul_pow] using h3 0 (by simp) 1 (by simp)
    have i4 : Integrable (fun p => (|p.2.2| * ‖pdEta φ p‖) ^ 2) (measureH c) := by
      simpa [mul_pow] using h4 0 (by simp) 1 (by simp)
    have key := nzco_l2_moment (μ := measureH c) (cgradC 0 φ) (cgradC ε (nzcoCut ε φ)) hG hmG
      (Real.sqrt ε * (3 + B1 + B2)) hM (fun p => ‖φ p‖) (fun p => ‖opS φ p‖)
      (fun p => |p.2.2| * ‖pdQ φ p‖) (fun p => |p.2.2| * ‖pdEta φ p‖) i1 i2 i3 i4
      (fun p => nzco_grad_pt ε hφs hε hε1 hB1 hB2 hBd p)
    have hsum : (∫ p, ‖φ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
        (∫ p, ‖opS φ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
        (∫ p, (|p.2.2| * ‖pdQ φ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
        (∫ p, (|p.2.2| * ‖pdEta φ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) ≤ nzPot c φ ψ := by
      have e1 : (∫ p, ‖φ p‖ ^ 2 ∂measureH c) = nzSq c 0 0 φ := by simp [nzSq]
      have e2 : (∫ p, ‖opS φ p‖ ^ 2 ∂measureH c) = nzSq c 1 0 φ := by simp [nzSq]
      have e3 : (∫ p, (|p.2.2| * ‖pdQ φ p‖) ^ 2 ∂measureH c) = nzSq c 0 1 (pdQ φ) := by
        simp [nzSq, mul_pow]
      have e4 : (∫ p, (|p.2.2| * ‖pdEta φ p‖) ^ 2 ∂measureH c) = nzSq c 0 1 (pdEta φ) := by
        simp [nzSq, mul_pow]
      rw [e1, e2, e3, e4]
      have m12 := nzco_mom_pair c φ
      have m3 := nzco_mom_ge c (pdQ φ) 0 1 (by simp) (by simp)
      have m4 := nzco_mom_ge c (pdEta φ) 0 1 (by simp) (by simp)
      have n5 := nzco_momSum_nonneg c ψ
      have n6 := nzco_momSum_nonneg c (pdQ ψ)
      have n7 := nzco_momSum_nonneg c (pdEta ψ)
      unfold nzPot
      linarith
    calc ‖hG.toLp (cgradC 0 φ) - hmG.toLp (cgradC ε (nzcoCut ε φ))‖
        ≤ 2 * (Real.sqrt ε * (3 + B1 + B2)) *
          ((∫ p, ‖φ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
            (∫ p, ‖opS φ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
            (∫ p, (|p.2.2| * ‖pdQ φ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
            (∫ p, (|p.2.2| * ‖pdEta φ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ)) := key
      _ ≤ 2 * (Real.sqrt ε * (3 + B1 + B2)) * nzPot c φ ψ :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg two_pos.le hM)
      _ = 2 * (3 + B1 + B2) * Real.sqrt ε * nzPot c φ ψ := by ring
  · -- stream part: the moments of `ψ`, `∂_q ψ`, `∂_η ψ`
    have i1 : Integrable (fun p => ‖ψ p‖ ^ 2) (measureH c) := by
      simpa using h2 0 (by simp) 0 (by simp)
    have i2 : Integrable (fun p => ‖opS ψ p‖ ^ 2) (measureH c) := by
      simpa using h2 1 (by simp) 0 (by simp)
    have i3 : Integrable (fun p => (|p.2.2| * ‖pdQ ψ p‖) ^ 2) (measureH c) := by
      simpa [mul_pow] using h5 0 (by simp) 1 (by simp)
    have i4 : Integrable (fun p => (|p.2.2| * ‖pdEta ψ p‖) ^ 2) (measureH c) := by
      simpa [mul_pow] using h6 0 (by simp) 1 (by simp)
    have key := nzco_l2_moment (μ := measureH c) (streamC 0 ψ) (streamC ε (nzcoCut ε ψ)) hS hmS
      (Real.sqrt ε * (3 + B1 + B2)) hM (fun p => ‖ψ p‖) (fun p => ‖opS ψ p‖)
      (fun p => |p.2.2| * ‖pdQ ψ p‖) (fun p => |p.2.2| * ‖pdEta ψ p‖) i1 i2 i3 i4
      (fun p => nzco_stream_pt ε hψs hε hε1 hB1 hB2 hBd p)
    have hsum : (∫ p, ‖ψ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
        (∫ p, ‖opS ψ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
        (∫ p, (|p.2.2| * ‖pdQ ψ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
        (∫ p, (|p.2.2| * ‖pdEta ψ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) ≤ nzPot c φ ψ := by
      have e1 : (∫ p, ‖ψ p‖ ^ 2 ∂measureH c) = nzSq c 0 0 ψ := by simp [nzSq]
      have e2 : (∫ p, ‖opS ψ p‖ ^ 2 ∂measureH c) = nzSq c 1 0 ψ := by simp [nzSq]
      have e3 : (∫ p, (|p.2.2| * ‖pdQ ψ p‖) ^ 2 ∂measureH c) = nzSq c 0 1 (pdQ ψ) := by
        simp [nzSq, mul_pow]
      have e4 : (∫ p, (|p.2.2| * ‖pdEta ψ p‖) ^ 2 ∂measureH c) = nzSq c 0 1 (pdEta ψ) := by
        simp [nzSq, mul_pow]
      rw [e1, e2, e3, e4]
      have m12 := nzco_mom_pair c ψ
      have m3 := nzco_mom_ge c (pdQ ψ) 0 1 (by simp) (by simp)
      have m4 := nzco_mom_ge c (pdEta ψ) 0 1 (by simp) (by simp)
      have n5 := nzco_momSum_nonneg c φ
      have n6 := nzco_momSum_nonneg c (pdQ φ)
      have n7 := nzco_momSum_nonneg c (pdEta φ)
      unfold nzPot
      linarith
    calc ‖hS.toLp (streamC 0 ψ) - hmS.toLp (streamC ε (nzcoCut ε ψ))‖
        ≤ 2 * (Real.sqrt ε * (3 + B1 + B2)) *
          ((∫ p, ‖ψ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
            (∫ p, ‖opS ψ p‖ ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
            (∫ p, (|p.2.2| * ‖pdQ ψ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ) +
            (∫ p, (|p.2.2| * ‖pdEta ψ p‖) ^ 2 ∂measureH c) ^ (1 / 2 : ℝ)) := key
      _ ≤ 2 * (Real.sqrt ε * (3 + B1 + B2)) * nzPot c φ ψ :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg two_pos.le hM)
      _ = 2 * (3 + B1 + B2) * Real.sqrt ε * nzPot c φ ψ := by ring

end UnforcedLeray.Short.PartIIa
