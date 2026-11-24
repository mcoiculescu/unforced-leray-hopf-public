import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedWeakGenerator
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeDyson

/-!
# Turnover mild identity of the actual normalized evolution

Rewrite the concrete `S_mild` Duhamel formula in normalized turnover time. The resulting base
propagator is the Gaussian diffusion clock conjugated by the exact scalar gauge ratio.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
  UnforcedLeray.ComplexODEC

/-- The gauge-conjugated diffusion propagator in turnover coordinates. -/
def normalizedTurnoverFree (lam κ : ℂ) (R t s : ℝ) : XG →L[ℂ] XG :=
  (gauge lam κ (R - t) * gaugeInv lam κ (R - s)) • freeU (t - R) (s - R)

/-- The exact normalized `S` Duhamel formula on a finite turnover block. Its scalar gauge ratio is
kept explicit, so the formula is a concrete mild equation and uses no state-domain regularity. -/
theorem normState_normalizedTurnoverFree_mild {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {R b₀ t : ℝ} (hb₀ : 0 < b₀)
    (ht0 : 0 ≤ t) (htt : t ≤ R - b₀) (f : XG) :
    normState (lamMode c) (kapMode c F) R f t =
      normalizedTurnoverFree (lamMode c) (kapMode c F) R t 0 f +
        ∫ r in (0 : ℝ)..t,
          normalizedTurnoverFree (lamMode c) (kapMode c F) R t r
            (B0012.L0 (normState (lamMode c) (kapMode c F) R f r)) := by
  have hR : 0 < R := by linarith [hb₀, htt]
  have htR : 0 < R - t := by linarith [htt, hb₀]
  have hS := S_mild htR (by linarith [ht0]) f
  let αt := gauge (lamMode c) (kapMode c F) (R - t) *
    gaugeInv (lamMode c) (kapMode c F) R
  let g : ℝ → XG := fun r =>
    freeU (t - R) (r - R) (B0012.L0 (S (R - r) R f))
  have hshift :
      (∫ u in -R..t - R,
          freeU (t - R) u (B0012.L0 (S (-u) R f))) =
        ∫ r in (0 : ℝ)..t, g r := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := fun u => freeU (t - R) u (B0012.L0 (S (-u) R f))) (-R)
      (a := (0 : ℝ)) (b := t)
    simpa [g, sub_eq_add_neg, add_comm] using hcomp.symm
  have hstate (r : ℝ) :
      normState (lamMode c) (kapMode c F) R f r =
        (gauge (lamMode c) (kapMode c F) (R - r) *
          gaugeInv (lamMode c) (kapMode c F) R) • S (R - r) R f := rfl
  have hscalar (r : ℝ) (hr : r ∈ Icc 0 t) :
      (gauge (lamMode c) (kapMode c F) (R - t) *
          gaugeInv (lamMode c) (kapMode c F) R) =
        (gauge (lamMode c) (kapMode c F) (R - t) *
          gaugeInv (lamMode c) (kapMode c F) (R - r)) *
        (gauge (lamMode c) (kapMode c F) (R - r) *
          gaugeInv (lamMode c) (kapMode c F) R) := by
    have hrpos : 0 < R - r := by linarith [hr.2, htt, hb₀]
    calc
      _ = gauge (lamMode c) (kapMode c F) (R - t) *
            (gaugeInv (lamMode c) (kapMode c F) (R - r) *
              gauge (lamMode c) (kapMode c F) (R - r)) *
            gaugeInv (lamMode c) (kapMode c F) R := by
              rw [gaugeInv_mul_gauge (lam := lamMode c) (κ := kapMode c F) hrpos]
              simp
      _ = _ := by ring
  have hbase : αt • expD (Real.log R - Real.log (R - t)) f =
      normalizedTurnoverFree (lamMode c) (kapMode c F) R t 0 f := by
    simp [normalizedTurnoverFree, freeU, αt]
  have hintegral :
      (∫ r in (0 : ℝ)..t,
        normalizedTurnoverFree (lamMode c) (kapMode c F) R t r
          (B0012.L0 (normState (lamMode c) (kapMode c F) R f r))) =
      αt • ∫ r in (0 : ℝ)..t, g r := by
    calc
      _ = ∫ r in (0 : ℝ)..t, αt • g r := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le ht0] at hr
        change (gauge (lamMode c) (kapMode c F) (R - t) *
            gaugeInv (lamMode c) (kapMode c F) (R - r)) •
            freeU (t - R) (r - R)
              (B0012.L0 (normState (lamMode c) (kapMode c F) R f r)) = αt • g r
        rw [hstate r]
        simp only [map_smul, smul_smul]
        rw [← hscalar r hr]
      _ = αt • ∫ r in (0 : ℝ)..t, g r := by
        rw [intervalIntegral.integral_smul αt g]
  change αt • S (R - t) R f = _
  have hS' := hS
  rw [show -(R - t) = t - R by ring] at hS'
  rw [hS']
  simp only [map_add, smul_add]
  rw [hbase, hshift, hintegral]

end UnforcedLeray.Cons.G3b
