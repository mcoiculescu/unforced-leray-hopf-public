import UnforcedLeray.Short.PartIIIb.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# `closure:mixed-return` (lines 5711-5775): the real two-norm return lemma

Source: `the November 2 reference manuscript`, lines 5711-5775
(statement 5717-5742, proof 5744-5774).  The lemma is generic in the Banach spaces
`E_n`, `X_n` (the source says so: "let `E_n, X_n` be real Banach spaces"), so it is stated for
arbitrary families of real Banach spaces.  Quantities are literal:
`c_n = sup_z ‖C_n(z)‖`, `r_n = sup_z ‖R_n(z)‖`, `h_n = sup_z ‖A_n(z)‖‖B_n(z)‖ / (1 - c_n)`
(suprema over `z ∈ [-1,1]`), `K_n = a_n ℓ_n + R_n` with `a_n ℓ_n : x ↦ ℓ_n(x) a_n`.
The suprema are finite because every map is norm continuous on the compact `[-1,1]`.

Helper statements `MR_Reduce`, `MR_Crossing` are the two cheap pieces of the proof
(lines 5757-5774), stated as `Prop`s so that their types are checked.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- `closure:mixed-return`, lines 5717-5742.  Conclusion: for every large `n` there is
`z_n ∈ (-1,1)` and a nonzero solution `(x, y)` of the block system, and `z_n → 0`. -/
def MixedReturnLemma : Prop :=
  ∀ (E X : ℕ → Type)
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)] [∀ n, CompleteSpace (X n)]
    (K : ∀ n, ℝ → E n →L[ℝ] E n) (A : ∀ n, ℝ → X n →L[ℝ] E n)
    (B : ∀ n, ℝ → E n →L[ℝ] X n) (C : ∀ n, ℝ → X n →L[ℝ] X n)
    (a : ∀ n, ℝ → E n) (ℓ : ∀ n, ℝ → E n →L[ℝ] ℝ) (R : ∀ n, ℝ → E n →L[ℝ] E n) (M : ℝ),
    (∀ n, ContinuousOn (K n) (Icc (-1) 1)) → (∀ n, ContinuousOn (A n) (Icc (-1) 1)) →
    (∀ n, ContinuousOn (B n) (Icc (-1) 1)) → (∀ n, ContinuousOn (C n) (Icc (-1) 1)) →
    (∀ n, ContinuousOn (a n) (Icc (-1) 1)) → (∀ n, ContinuousOn (ℓ n) (Icc (-1) 1)) →
    (∀ n, ContinuousOn (R n) (Icc (-1) 1)) →
    (∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, K n z = (ℓ n z).smulRight (a n z) + R n z) →
    (∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, ‖a n z‖ * ‖ℓ n z‖ ≤ M) →
    (∀ n, (⨆ z : Icc (-1 : ℝ) 1, ‖C n z‖) < 1) →
    Tendsto (fun n => (⨆ z : Icc (-1 : ℝ) 1, ‖R n z‖) +
        (⨆ z : Icc (-1 : ℝ) 1, ‖A n z‖ * ‖B n z‖) / (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖C n z‖))
      atTop (𝓝 0) →
    TendstoUniformlyOn (fun n z => ℓ n z (a n z)) (fun z => Real.exp (-z)) atTop
      (Icc (-1 : ℝ) 1) →
    ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, z n ∈ Ioo (-1 : ℝ) 1 ∧
        ∃ x : E n, x ≠ 0 ∧ ∃ y : X n,
          x = K n (z n) x + A n (z n) y ∧ y = B n (z n) x + C n (z n) y

section Schur

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- `R̃ = R + A (I - C)⁻¹ B` (line 5750), with `Ring.inverse` as the inverse of `I - C`. -/
def schurTilde (A : X →L[ℝ] E) (B : E →L[ℝ] X) (C : X →L[ℝ] X) (R : E →L[ℝ] E) :
    E →L[ℝ] E :=
  R + A ∘L Ring.inverse (1 - C) ∘L B

/-- `w = (I - R̃)⁻¹ a` (line 5756). -/
def schurSol (A : X →L[ℝ] E) (B : E →L[ℝ] X) (C : X →L[ℝ] X) (R : E →L[ℝ] E) (a : E) : E :=
  Ring.inverse (1 - schurTilde A B C R) a

end Schur

/-- Helper 1 (lines 5757-5766, one frozen `z`): the Schur reduction and the deviation bound.
`‖R̃‖ ≤ r + h`, `|ℓ w - ℓ a| ≤ ‖ℓ‖‖a‖ (r+h)/(1-(r+h))`, and if `ℓ w = 1` then `w ≠ 0` and
`(w, (I-C)⁻¹ B w)` solves `x = (ℓ x) a + R x + A y`, `y = B x + C y`. -/
def MR_Reduce : Prop :=
  ∀ {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : X →L[ℝ] E) (B : E →L[ℝ] X) (C : X →L[ℝ] X) (R : E →L[ℝ] E) (a : E) (ℓ : E →L[ℝ] ℝ)
    (c r h : ℝ), ‖C‖ ≤ c → c < 1 → ‖R‖ ≤ r → ‖A‖ * ‖B‖ / (1 - c) ≤ h → r + h < 1 →
    ‖schurTilde A B C R‖ ≤ r + h ∧
    |ℓ (schurSol A B C R a) - ℓ a| ≤ ‖ℓ‖ * ‖a‖ * ((r + h) / (1 - (r + h))) ∧
    (ℓ (schurSol A B C R a) = 1 →
      schurSol A B C R a ≠ 0 ∧
      schurSol A B C R a = ℓ (schurSol A B C R a) • a + R (schurSol A B C R a)
          + A (Ring.inverse (1 - C) (B (schurSol A B C R a))) ∧
      Ring.inverse (1 - C) (B (schurSol A B C R a)) =
          B (schurSol A B C R a) + C (Ring.inverse (1 - C) (B (schurSol A B C R a))))

/-- Helper 2 (lines 5768-5774, the intermediate value argument): continuous `d_n` on `[-1,1]`
converging uniformly to `1 - e^{-z}` have zeros `z_n ∈ (-1,1)` (for large `n`), and every
choice of zeros tends to `0`. -/
def MR_Crossing : Prop :=
  ∀ d : ℕ → ℝ → ℝ, (∀ n, ContinuousOn (d n) (Icc (-1 : ℝ) 1)) →
    TendstoUniformlyOn d (fun z => 1 - Real.exp (-z)) atTop (Icc (-1 : ℝ) 1) →
    ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, z n ∈ Ioo (-1 : ℝ) 1 ∧ d n (z n) = 0

end UnforcedLeray.Short.PartIIIb
