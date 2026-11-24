import UnforcedLeray.Lib.Semigroups.BanachExp
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall

/-!
# Exponential of a skew-adjoint operator plus a bounded perturbation (INF07 T0.1)


§5, target **T0.1** (Wave 1, block 1G). Uses: tex 1424 ("Multiplication by `-2iΩ` is bounded and
skew-adjoint", `L₀ = T + A` with `T = -2iΩ`), tex 1649-1651 (`L₀ = T + A`, `T` bounded
skew-adjoint), and the bounded-generator sector semigroups of BP1 (decision D7).

If `S` is skew-adjoint (`S† = -S`) and `K` is bounded, then for `t ≥ 0`
`‖exp(t(S + K))‖ ≤ e^{t‖K‖}`.

Proof (energy, no Trotter product and no Duhamel series): for `u(s) = exp(s(S+K)) x`,
`d/ds Re⟪u, u⟫ = 2 Re⟪u, (S+K) u⟫ = 2 Re⟪u, K u⟫ ≤ 2‖K‖ ‖u‖²`, since `Re⟪u, S u⟫ = 0`;
Mathlib's Grönwall inequality `le_gronwallBound_of_liminf_deriv_right_le` gives
`‖u(t)‖² ≤ e^{2t‖K‖} ‖x‖²`.

All statements are about `NormedSpace.exp` in the Banach algebra `H →L[ℂ] H` at the complex
time `(t : ℂ)`; no junk value is involved (the exponential series converges for every operator).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Infra

section Banach

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The orbit `s ↦ exp(sA) x` of a bounded operator solves `u' = A u` (real time). -/
theorem hasDerivAt_exp_smul_apply (A : X →L[ℂ] X) (x : X) (s : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A) x)
      (A (NormedSpace.exp ((s : ℂ) • A) x)) s := by
  have h := (BanachExp.hasDerivAt_exp_smul A s).2
  have hL := ((ContinuousLinearMap.apply ℂ X x).restrictScalars ℝ).hasFDerivAt
    (x := NormedSpace.exp ((s : ℂ) • A))
  simpa [Function.comp_def] using hL.comp_hasDerivAt s h

/-- `s ↦ exp(sA) x` is continuous. -/
theorem continuous_exp_smul_apply (A : X →L[ℂ] X) (x : X) :
    Continuous (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A) x) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_apply A x s).continuousAt

end Banach

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a skew-adjoint operator, `Re ⟪x, S x⟫ = 0`. -/
theorem re_inner_apply_eq_zero_of_adjoint_eq_neg [CompleteSpace H] {S : H →L[ℂ] H}
    (hS : ContinuousLinearMap.adjoint S = -S) (x : H) : RCLike.re ⟪x, S x⟫_ℂ = 0 := by
  have h1 : ⟪x, S x⟫_ℂ = ⟪ContinuousLinearMap.adjoint S x, x⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_left S x x).symm
  rw [hS, ContinuousLinearMap.neg_apply, inner_neg_left] at h1
  have h3 : ⟪S x, x⟫_ℂ = (starRingEnd ℂ) ⟪x, S x⟫_ℂ := (inner_conj_symm (S x) x).symm
  have h2 := congrArg RCLike.re h1
  rw [map_neg, h3, RCLike.conj_re] at h2
  linarith

variable [CompleteSpace H]

/-- **T0.1** (tex 1424, 1649). If `S† = -S` and `K` is bounded then
`‖exp(t(S + K))‖ ≤ e^{t‖K‖}` for `t ≥ 0`. -/
theorem norm_exp_skew_add_le {S K : H →L[ℂ] H} (hS : ContinuousLinearMap.adjoint S = -S)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : ℂ) • (S + K))‖ ≤ Real.exp (t * ‖K‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
  set A : H →L[ℂ] H := S + K with hA
  set u : ℝ → H := fun s => NormedSpace.exp ((s : ℂ) • A) x with hu_def
  have hu : ∀ s, HasDerivAt u (A (u s)) s := fun s => hasDerivAt_exp_smul_apply A x s
  set f : ℝ → ℝ := fun s => RCLike.re ⟪u s, u s⟫_ℂ with hf_def
  have hfu : ∀ s, f s = ‖u s‖ ^ 2 := fun s => inner_self_eq_norm_sq (u s)
  have hderiv : ∀ s, HasDerivAt f (2 * RCLike.re ⟪u s, K (u s)⟫_ℂ) s := by
    intro s
    have hi := (hu s).inner ℂ (hu s)
    have hre := (RCLike.reCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt s hi
    refine hre.congr_deriv ?_
    have e1 : RCLike.re ⟪A (u s), u s⟫_ℂ = RCLike.re ⟪u s, A (u s)⟫_ℂ := by
      rw [← inner_conj_symm (A (u s)) (u s), RCLike.conj_re]
    have e2 : A (u s) = S (u s) + K (u s) := rfl
    simp only [RCLike.reCLM_apply]
    rw [map_add, e1, e2, inner_add_right, map_add, re_inner_apply_eq_zero_of_adjoint_eq_neg hS]
    ring
  have hbound : ∀ s, 2 * RCLike.re ⟪u s, K (u s)⟫_ℂ ≤ (2 * ‖K‖) * f s := by
    intro s
    rw [hfu s]
    have h1 : RCLike.re ⟪u s, K (u s)⟫_ℂ ≤ ‖u s‖ * ‖K (u s)‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h2 : ‖u s‖ * ‖K (u s)‖ ≤ ‖u s‖ * (‖K‖ * ‖u s‖) :=
      mul_le_mul_of_nonneg_left (K.le_opNorm _) (norm_nonneg _)
    nlinarith
  have hcont : ContinuousOn f (Icc 0 t) :=
    (continuous_iff_continuousAt.2 fun s => (hderiv s).continuousAt).continuousOn
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f' := fun s => 2 * RCLike.re ⟪u s, K (u s)⟫_ℂ)
    (δ := ‖x‖ ^ 2) (K := 2 * ‖K‖) (ε := 0) hcont
    (fun s _ r hr => (hderiv s).hasDerivWithinAt.liminf_right_slope_le hr)
    (by
      rw [hfu 0]
      simp [hu_def])
    (fun s _ => by simpa using hbound s) t ⟨ht, le_rfl⟩
  rw [sub_zero, gronwallBound_ε0, hfu t] at hgr
  have hsq : ‖u t‖ ^ 2 ≤ (Real.exp (t * ‖K‖) * ‖x‖) ^ 2 := by
    calc ‖u t‖ ^ 2 ≤ ‖x‖ ^ 2 * Real.exp (2 * ‖K‖ * t) := hgr
      _ = (Real.exp (t * ‖K‖) * ‖x‖) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- Corollary of T0.1: a skew-adjoint operator generates a contraction group,
`‖exp(tS)‖ ≤ 1` for `t ≥ 0`. -/
theorem norm_exp_skew_le_one {S : H →L[ℂ] H} (hS : ContinuousLinearMap.adjoint S = -S)
    {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp ((t : ℂ) • S)‖ ≤ 1 := by
  simpa using norm_exp_skew_add_le (K := 0) hS ht

end UnforcedLeray.Infra
