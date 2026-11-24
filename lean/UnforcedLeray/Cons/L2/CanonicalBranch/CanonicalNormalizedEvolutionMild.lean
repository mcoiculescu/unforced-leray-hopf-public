import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedMild

/-!
# Two-time normalized evolution mild identity

The actual normalized transition satisfies a left Duhamel equation on every finite turnover
subinterval, with the gauge-conjugated Gaussian clock as free family and `L₀` as bounded
interaction. This is the form required by `Evolution.dyson_unique`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
  UnforcedLeray.ComplexODEC

/-- The actual normalized transition from turnover time `s` to `t`. -/
def actualNormalizedTurnoverEvolution (lam κ : ℂ) (R t s : ℝ) : XG →L[ℂ] XG :=
  (gauge lam κ (R - t) * gaugeInv lam κ (R - s)) • S (R - t) (R - s)

/-- The actual normalized evolution obeys its two-time turnover mild equation on any finite block. -/
theorem actualNormalizedTurnoverEvolution_mild {lam κ : ℂ} {R b₀ s t : ℝ}
    (hb₀ : 0 < b₀) (hs : 0 ≤ s) (hst : s ≤ t) (htt : t ≤ R - b₀) (x : XG) :
    actualNormalizedTurnoverEvolution lam κ R t s x =
      normalizedTurnoverFree lam κ R t s x +
        ∫ r in s..t,
          normalizedTurnoverFree lam κ R t r
            (B0012.L0 (actualNormalizedTurnoverEvolution lam κ R r s x)) := by
  have htheta : 0 < R - t := by linarith [htt, hb₀]
  have htheta' : 0 < R - s := by linarith [htt, hs, hst, hb₀]
  have htheta_le : R - t ≤ R - s := by linarith
  have hS := S_mild htheta htheta_le x
  let α := gauge lam κ (R - t) * gaugeInv lam κ (R - s)
  let g : ℝ → XG := fun r =>
    freeU (t - R) (r - R) (B0012.L0 (S (R - r) (R - s) x))
  have hS' := hS
  rw [show -(R - t) = t - R by ring, show -(R - s) = s - R by ring] at hS'
  have hshift :
      (∫ u in s - R..t - R,
          freeU (t - R) u (B0012.L0 (S (-u) (R - s) x))) =
        ∫ r in s..t, g r := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := fun u => freeU (t - R) u (B0012.L0 (S (-u) (R - s) x))) (-R)
      (a := s) (b := t)
    simpa [g, sub_eq_add_neg, add_comm] using hcomp.symm
  have hstate (r : ℝ) :
      actualNormalizedTurnoverEvolution lam κ R r s x =
        (gauge lam κ (R - r) * gaugeInv lam κ (R - s)) • S (R - r) (R - s) x := rfl
  have hscalar (r : ℝ) (hr : r ∈ Icc s t) : α =
      (gauge lam κ (R - t) * gaugeInv lam κ (R - r)) *
        (gauge lam κ (R - r) * gaugeInv lam κ (R - s)) := by
    have hrpos : 0 < R - r := by linarith [hr.2, htt, hb₀]
    dsimp [α]
    calc
      _ = gauge lam κ (R - t) *
            (gaugeInv lam κ (R - r) * gauge lam κ (R - r)) *
            gaugeInv lam κ (R - s) := by
              rw [gaugeInv_mul_gauge (lam := lam) (κ := κ) hrpos]
              simp
      _ = _ := by ring
  have hbase : α • expD (Real.log (R - s) - Real.log (R - t)) x =
      normalizedTurnoverFree lam κ R t s x := by
    simp [actualNormalizedTurnoverEvolution, normalizedTurnoverFree, freeU, α]
  have hintegral :
      (∫ r in s..t,
        normalizedTurnoverFree lam κ R t r
          (B0012.L0 (actualNormalizedTurnoverEvolution lam κ R r s x))) =
      α • ∫ r in s..t, g r := by
    calc
      _ = ∫ r in s..t, α • g r := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hst] at hr
        change (gauge lam κ (R - t) * gaugeInv lam κ (R - r)) •
            freeU (t - R) (r - R)
              (B0012.L0 (actualNormalizedTurnoverEvolution lam κ R r s x)) = α • g r
        rw [hstate r]
        simp only [map_smul, smul_smul]
        rw [← hscalar r hr]
      _ = α • ∫ r in s..t, g r := by
        rw [intervalIntegral.integral_smul α g]
  change α • S (R - t) (R - s) x = _
  rw [hS']
  simp only [smul_add]
  rw [hbase, hshift, hintegral]

end UnforcedLeray.Cons.G3b
