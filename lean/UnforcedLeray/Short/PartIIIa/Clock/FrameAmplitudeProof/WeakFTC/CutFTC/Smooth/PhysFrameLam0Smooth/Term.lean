import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth.Good
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_2

/-!
# The physical-variable term `g_L(r, x) = a(r) L(x/√a(r))` and its derivative

Helper for `PartIII-a:T21/c5/1/1/2/2` (SP 2891-2905).  With `a = clockA ν r = 1 + ν r` and
`ι(r, x) = a^{-1/2} x`, the term `physAdj a L x = a L(ι)` has the derivative
`v ↦ ν v₁ (EL)(ι) + √a DL(ι) v₂`, where `EL(z) = L(z) - ½ DL(z) z` (`fderiv_physTerm_apply`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.LamJetInf

/-- The Euler-corrected kernel `EL(z) = L(z) - ½ DL(z) z`. -/
def eulerK (L : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ := L z + (-(1 / 2) : ℂ) * fderiv ℝ L z z

theorem Good.eulerK {L : ℝ × ℝ → ℂ} (hL : Good L) : Good (eulerK L) :=
  hL.add (hL.euler.const_mul _)

/-- The scaled point `ι(r, x) = a(r)^{-1/2} x`. -/
def iotaP (ν : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ := (Real.sqrt (clockA ν p.1))⁻¹ • p.2

/-- One unshifted term `g_L(r, x) = physAdj (clockA ν r) L x`. -/
def physTerm (ν : ℝ) (L : ℝ × ℝ → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ := physAdj (clockA ν p.1) L p.2

theorem physAdj_eq_smul (a : ℝ) (L : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    physAdj a L y = (a : ℂ) * L ((Real.sqrt a)⁻¹ • y) := by
  simp only [physAdj, div_eq_inv_mul]
  rfl

theorem physTerm_eq (ν : ℝ) (L : ℝ × ℝ → ℂ) :
    physTerm ν L = fun p => clockA ν p.1 • L (iotaP ν p) := by
  funext p
  rw [physTerm, physAdj_eq_smul, Complex.real_smul]
  rfl

/-- The claimed derivative of `physTerm ν L` at `p`, from the chain rule. -/
def physTermD (ν : ℝ) (L : ℝ × ℝ → ℂ) (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) →L[ℝ] ℂ :=
  clockA ν p.1 • ((fderiv ℝ L (iotaP ν p)).comp
      ((Real.sqrt (clockA ν p.1))⁻¹ • ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) +
        ((-(ν * 1 / (2 * Real.sqrt (clockA ν p.1))) / Real.sqrt (clockA ν p.1) ^ 2) •
          ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight p.2)) +
    ((ν * 1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (L (iotaP ν p))

theorem hasFDerivAt_physTerm (ν : ℝ) {L : ℝ × ℝ → ℂ} (hL : Differentiable ℝ L)
    {p : ℝ × (ℝ × ℝ)} (ha : 0 < clockA ν p.1) :
    HasFDerivAt (physTerm ν L) (physTermD ν L p) p := by
  have hA : ∀ r : ℝ, HasDerivAt (fun r => clockA ν r) (ν * 1) r := fun r =>
    ((hasDerivAt_id r).const_mul ν).const_add 1
  have hsq : Real.sqrt (clockA ν p.1) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hσ : HasDerivAt (fun r => (Real.sqrt (clockA ν r))⁻¹)
      (-(ν * 1 / (2 * Real.sqrt (clockA ν p.1))) / Real.sqrt (clockA ν p.1) ^ 2) p.1 :=
    ((hA p.1).sqrt ha.ne').inv hsq
  have hσf : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => (Real.sqrt (clockA ν q.1))⁻¹)
      ((-(ν * 1 / (2 * Real.sqrt (clockA ν p.1))) / Real.sqrt (clockA ν p.1) ^ 2) •
        ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hσ.comp_hasFDerivAt (f := Prod.fst) p (hasFDerivAt_fst)
  have hι : HasFDerivAt (iotaP ν)
      ((Real.sqrt (clockA ν p.1))⁻¹ • ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) +
        ((-(ν * 1 / (2 * Real.sqrt (clockA ν p.1))) / Real.sqrt (clockA ν p.1) ^ 2) •
          ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight p.2) p :=
    hσf.smul (hasFDerivAt_snd)
  have hLι := (hL (iotaP ν p)).hasFDerivAt.comp p hι
  have haf : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => clockA ν q.1)
      ((ν * 1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hA p.1).comp_hasFDerivAt (f := Prod.fst) p (hasFDerivAt_fst)
  have h := haf.smul hLι
  rw [physTerm_eq]
  exact h

/-- The derivative formula `Dg_L(p) v = ν v₁ (EL)(ι) + √a DL(ι) v₂`. -/
theorem physTermD_apply (ν : ℝ) (L : ℝ × ℝ → ℂ) {p : ℝ × (ℝ × ℝ)} (ha : 0 < clockA ν p.1)
    (v : ℝ × (ℝ × ℝ)) :
    physTermD ν L p v = ((ν * v.1 : ℝ) : ℂ) * eulerK L (iotaP ν p) +
      ((Real.sqrt (clockA ν p.1) : ℝ) : ℂ) * fderiv ℝ L (iotaP ν p) v.2 := by
  set a := clockA ν p.1 with ha_def
  set s := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hss : s ^ 2 = a := Real.sq_sqrt ha.le
  set D := fderiv ℝ L (iotaP ν p) with hD
  have hιp : iotaP ν p = s⁻¹ • p.2 := rfl
  have hDι : D (iotaP ν p) = s⁻¹ • D p.2 := by rw [hιp, map_smul]
  simp only [physTermD, eulerK, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_add, map_smul, ← hD, ← hs,
    ← ha_def]
  rw [hDι]
  simp only [Complex.real_smul, smul_eq_mul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have haC : (a : ℂ) = (s : ℂ) ^ 2 := by rw [← hss]; push_cast; ring
  rw [haC]
  push_cast
  field_simp
  ring

end UnforcedLeray.Short.IIIa.LamJetInf
