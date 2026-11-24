import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

/-!
# Helpers for `sourceLLinear` (`PartIII-b:C/srcL/14`)

Additivity and homogeneity of the thin representative (almost everywhere for the gain measure) and
of `Lpt` in the old tensor, given that `X^mt` is additive/homogeneous and differentiable. These do not
import the `srcL_6` or `srcL_8` chains, whose duplicate declaration `chiYr_zero_of_lt` blocks a
single import of both.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The thin representative of a sum is the sum, `gainZ1Measure`-a.e. -/
theorem thinRep_add_ae {c mZ ρb γ ν : ℝ} (T T' : StrG c mZ ρb γ ν) :
    thinRep (T + T') =ᵐ[gainZ1Measure c mZ γ ν] thinRep T + thinRep T' := by
  have hc := Lp.coeFn_add (WithLp.ofLp T).1 (WithLp.ofLp T').1
  have hadd : (WithLp.ofLp (T + T')).1 = (WithLp.ofLp T).1 + (WithLp.ofLp T').1 := by
    rw [WithLp.ofLp_add]
    rfl
  have key : ∀ A B : Ten3, Ten3.toMatrix (A + B) = Ten3.toMatrix A + Ten3.toMatrix B := by
    intro A B
    ext a b
    simp [Ten3.toMatrix]
  filter_upwards [hc] with p hp
  show Ten3.toMatrix ((WithLp.ofLp (T + T')).1 p) =
    Ten3.toMatrix ((WithLp.ofLp T).1 p) + Ten3.toMatrix ((WithLp.ofLp T').1 p)
  rw [hadd, hp, Pi.add_apply, key]

/-- The thin representative of a multiple is the multiple, `gainZ1Measure`-a.e. -/
theorem thinRep_smul_ae {c mZ ρb γ ν : ℝ} (r : ℝ) (T : StrG c mZ ρb γ ν) :
    thinRep (r • T) =ᵐ[gainZ1Measure c mZ γ ν] r • thinRep T := by
  have hc := Lp.coeFn_smul r (WithLp.ofLp T).1
  have hsm : (WithLp.ofLp (r • T)).1 = r • (WithLp.ofLp T).1 := by
    rw [WithLp.ofLp_smul]
    rfl
  have key : ∀ A : Ten3, Ten3.toMatrix (r • A) = r • Ten3.toMatrix A := by
    intro A
    ext a b
    simp [Ten3.toMatrix]
  filter_upwards [hc] with p hp
  simp only [Pi.smul_apply] at hp
  show Ten3.toMatrix ((WithLp.ofLp (r • T)).1 p) = r • Ten3.toMatrix ((WithLp.ofLp T).1 p)
  rw [hsm, hp, key]

/-- `Lpt` is additive in the old tensor when `X^mt` is. -/
theorem Lpt_add_of {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} {N M M' : Chart → Mat3}
    (hM : ∀ y, DifferentiableAt ℝ (Xmt c ν ε μ χo χy M) y)
    (hM' : ∀ y, DifferentiableAt ℝ (Xmt c ν ε μ χo χy M') y)
    (hE : Xmt c ν ε μ χo χy N = Xmt c ν ε μ χo χy M + Xmt c ν ε μ χo χy M') (s : ℝ) :
    Lpt c ν ε μ χo χy N s = Lpt c ν ε μ χo χy M s + Lpt c ν ε μ χo χy M' s := by
  unfold Lpt
  by_cases hs : 0 < s
  · rw [if_pos hs, if_pos hs, if_pos hs, hE]
    have hd : fderiv ℝ (Xmt c ν ε μ χo χy M + Xmt c ν ε μ χo χy M')
        ![ε⁻¹ / Real.sqrt s, 0, 0] =
        fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] +
          fderiv ℝ (Xmt c ν ε μ χo χy M') ![ε⁻¹ / Real.sqrt s, 0, 0] :=
      fderiv_add (hM _) (hM' _)
    rw [hd]
    funext i j
    simp
  · rw [if_neg hs, if_neg hs, if_neg hs, add_zero]

/-- `Lpt` is homogeneous in the old tensor when `X^mt` is. -/
theorem Lpt_smul_of {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} {N M : Chart → Mat3} (r : ℝ)
    (hM : ∀ y, DifferentiableAt ℝ (Xmt c ν ε μ χo χy M) y)
    (hE : Xmt c ν ε μ χo χy N = r • Xmt c ν ε μ χo χy M) (s : ℝ) :
    Lpt c ν ε μ χo χy N s = r • Lpt c ν ε μ χo χy M s := by
  unfold Lpt
  by_cases hs : 0 < s
  · rw [if_pos hs, if_pos hs, hE]
    have hd : fderiv ℝ (r • Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] =
        r • fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] :=
      fderiv_const_smul (hM _) r
    rw [hd]
    funext i j
    simp
  · rw [if_neg hs, if_neg hs, smul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
