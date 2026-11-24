import UnforcedLeray.Cons.L2.CanonicalBranch
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeGenerator

/-!
# The concrete backward Dyson generator on the adjoint mode

Lift the Gaussian-domain weak generator through the actual `L₀` Dyson evolution on negative time
blocks. This gives the scalar differential identity used by the normalized amplitude argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
  UnforcedLeray.Evolution UnforcedLeray.ComplexODEC

/-- A global continuous positive extension of the actual negative-time coefficient `-1/t` on
every block ending at or before `b<0`. -/
def backwardCanonicalBeta (b t : ℝ) : ℝ := 1 / max (-t) (-b)

theorem continuous_backwardCanonicalBeta (b : ℝ) (hb : b < 0) :
    Continuous (backwardCanonicalBeta b) := by
  have hd : Continuous (fun t : ℝ => max (-t) (-b)) :=
    continuous_neg.max continuous_const
  apply continuous_const.div hd
  intro t
  have hb0 : 0 < -b := by linarith
  exact ne_of_gt (lt_of_lt_of_le hb0 (le_max_right _ _))

theorem backwardCanonicalBeta_nonneg (b t : ℝ) (hb : b < 0) :
    0 ≤ backwardCanonicalBeta b t := by
  apply one_div_nonneg.mpr
  exact le_of_lt (lt_of_lt_of_le (by linarith) (le_max_right _ _))

theorem backwardCanonicalBeta_abs_le (b : ℝ) (hb : b < 0) (t : ℝ) :
    |backwardCanonicalBeta b t| ≤ 1 / (-b) := by
  have hb' : 0 < -b := by linarith
  rw [abs_of_nonneg (backwardCanonicalBeta_nonneg b t hb)]
  unfold backwardCanonicalBeta
  exact one_div_le_one_div_of_le hb' (le_max_right _ _)

theorem backwardCanonicalBeta_eq_neg_inv {b t : ℝ} (ht : t ≤ b) :
    backwardCanonicalBeta b t = -t⁻¹ := by
  have hden : max (-t) (-b) = -t := max_eq_left (by linarith)
  rw [backwardCanonicalBeta, hden]
  simp [one_div, inv_neg]

theorem integral_backwardCanonicalBeta {b s t : ℝ} (hb : b < 0)
    (hst : s ≤ t) (ht : t ≤ b) :
    (∫ r in s..t, backwardCanonicalBeta b r) = Real.log (-s) - Real.log (-t) := by
  have hs : s < 0 := lt_of_le_of_lt (hst.trans ht) hb
  have ht0 : t < 0 := lt_of_le_of_lt ht hb
  calc
    (∫ r in s..t, backwardCanonicalBeta b r) = ∫ r in s..t, -r⁻¹ := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hst] at hr
      exact backwardCanonicalBeta_eq_neg_inv (hr.2.trans ht)
    _ = -∫ r in s..t, r⁻¹ := by rw [intervalIntegral.integral_neg]
    _ = Real.log (-s) - Real.log (-t) := by
      have hratio : t / s = (-t) / (-s) := by field_simp [hs.ne', ht0.ne']
      rw [integral_inv_of_neg hs ht0, hratio,
        Real.log_div (by linarith : -t ≠ 0) (by linarith : -s ≠ 0)]
      ring

/-- The explicit Gaussian free family on a negative-time block has the weak generator
`β(t)⟪Dq†,·⟫` on the functional represented by any vector in `D.domain`. -/
theorem freeFam_hasWeakGenerator_domain {a b : ℝ} (hb : b < 0)
    (z : B0094.D.domain) :
    (freeFam a b hb).HasWeakGenerator {innerSL ℂ (z : XG)}
      (fun t _ => ((backwardCanonicalBeta b t : ℝ) : ℂ) •
        innerSL ℂ (B0094.D z)) := by
  let β := backwardCanonicalBeta b
  have hβ : Continuous β := continuous_backwardCanonicalBeta b hb
  have hβ0 : ∀ t, 0 ≤ β t := fun t => backwardCanonicalBeta_nonneg b t hb
  have hβM : ∀ t, |β t| ≤ 1 / (-b) := backwardCanonicalBeta_abs_le b hb
  let E := freeDiffusionFamily (a := a) (b := b) β
    (fun s t => hβ.intervalIntegrable s t) hβ0 (1 / (-b)) hβM
  have hEweak := freeDiffusionFamily_hasWeakGenerator_domain
    (a := a) (b := b) β hβ hβ0 (1 / (-b)) hβM z
  have hclock : ∀ s t, s ≤ t → t ≤ b →
      (∫ r in s..t, β r) = Real.log (-s) - Real.log (-t) :=
    fun s t hst ht => integral_backwardCanonicalBeta hb hst ht
  have hU : ∀ t s, a ≤ s → s ≤ t → t ≤ b → E.U t s = freeU t s := by
    intro t s has hst htb
    ext x
    simp [E, freeDiffusionFamily, freeDiffusion, freeU, hclock s t hst htb]
  intro ℓ hℓ s x hs t ht
  have h := hEweak ℓ hℓ s x hs t ht
  have hEq : ∀ u ∈ Icc s b,
      ℓ (E.U u s x) = ℓ ((freeFam a b hb).U u s x) := by
    intro u hu
    exact congrArg (fun V : XG →L[ℂ] XG => ℓ (V x)) (hU u s hs hu.1 hu.2)
  have hder := h.congr_of_mem (fun u hu => (hEq u hu).symm) ht
  rw [hU t s hs ht.1 ht.2] at hder
  simpa [β, backwardCanonicalBeta, freeFam, freeU] using hder

/-- Testing the actual first-stage backward Dyson evolution against the normalized adjoint mode
gives its concrete scalar generator, with no free-evolution hypothesis. -/
theorem S_hasWeakDerivative_qdagMode {a b : ℝ} (hb : b < 0)
    {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (x : XG) :
    HasDerivWithinAt
      (fun u => inner ℂ (qdagMode hF) (S (-u) (-s) x))
      (((backwardCanonicalBeta b t : ℝ) : ℂ) *
          inner ℂ (B0094.D ⟨qdagMode hF, qdagMode_mem_Ddomain hF⟩)
            (S (-t) (-s) x) +
        lamMode c * inner ℂ (qdagMode hF) (S (-t) (-s) x))
      (Icc s b) t := by
  let z : B0094.D.domain := ⟨qdagMode hF, qdagMode_mem_Ddomain hF⟩
  let ℓ : XG →L[ℂ] ℂ := innerSL ℂ (qdagMode hF)
  let β := backwardCanonicalBeta b
  let E := freeFam a b hb
  let A := pertL0 a b
  let U := Evolution.dyson E A
  let G : ℝ → (XG →L[ℂ] ℂ) → (XG →L[ℂ] ℂ) :=
    fun r φ => ((β r : ℝ) : ℂ) • innerSL ℂ (B0094.D z)
  have hβc : Continuous β := continuous_backwardCanonicalBeta b hb
  have hG : ∀ φ ∈ ({ℓ} : Set (XG →L[ℂ] ℂ)),
      ContinuousOn (fun r => G r φ) (Icc a b) := by
    intro φ hφ
    simp only [Set.mem_singleton_iff] at hφ
    subst φ
    exact (Complex.continuous_ofReal.comp hβc).continuousOn.smul continuousOn_const
  have hAc : ContinuousOn A.A (Icc a b) := continuousOn_const
  have hEweak : E.HasWeakGenerator {ℓ} G := by
    have h := freeFam_hasWeakGenerator_domain (a := a) hb z
    intro φ hφ s x hs t ht
    have hφeq : φ = innerSL ℂ (z : XG) := by
      simpa [ℓ, z] using hφ
    subst φ
    simpa [E, G, β, ℓ, z, backwardCanonicalBeta] using
      h (innerSL ℂ (z : XG)) (by simp) s x hs t ht
  have hUweak := Evolution.dyson_hasWeakGenerator E A hEweak hG hAc
  have hUder := hUweak ℓ (Set.mem_singleton _) s x has t ⟨hst, htb⟩
  have hSeq : ∀ u ∈ Icc s b, S (-u) (-s) = U.U u s := by
    intro u hu
    have huPos : 0 < -u := by linarith [hu.2, hb]
    have hsu : -u ≤ -s := by linarith [hu.1]
    have hEq := S_eq_dyson (a := a) hb huPos hsu (by simpa using has)
      (by simpa using hu.2)
    simpa [U, E, A, freeFam, pertL0] using hEq
  have hSeqx : ∀ u ∈ Icc s b, ℓ (S (-u) (-s) x) = ℓ (U.U u s x) := by
    intro u hu
    exact congrArg (fun V : XG →L[ℂ] XG => ℓ (V x)) (hSeq u hu)
  have hder := hUder.congr_of_mem hSeqx ⟨hst, htb⟩
  have hmode := inner_qdagMode_L0 hF (U.U t s x)
  have hmode' : ℓ (B0012.L0 ((Evolution.dyson E A).U t s x)) =
      lamMode c * ℓ ((Evolution.dyson E A).U t s x) := by
    simpa [U, ℓ] using hmode
  change HasDerivWithinAt _
      (G t ℓ ((Evolution.dyson E A).U t s x) +
        ℓ (B0012.L0 ((Evolution.dyson E A).U t s x))) (Icc s b) t at hder
  rw [hmode'] at hder
  simpa [ℓ, G, β, z, innerSL_apply_apply, hSeq t ⟨hst, htb⟩] using hder

end UnforcedLeray.Cons.G3b
