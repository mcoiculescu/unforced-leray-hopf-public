import UnforcedLeray.Lib.Semigroups.SkewExp
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Exponentially bounded strongly continuous semigroups (INF07 T7.1)


§5, target **T7.1** (Wave 1, block 1G), bypass BP4 (resolvents as Laplace transforms of explicit
semigroups, no generator theory) and BP1 (bounded generators sector by sector, decision D7).

An `ExpSemigroup X` is a family `T : ℝ → X →L[ℂ] X` with `T 0 = 1`, `T (s + t) = T s T t` for
`s, t ≥ 0`, `t ↦ T t x` continuous on `[0, ∞)` and `‖T t‖ ≤ M e^{ωt}` for `t ≥ 0`. Values at
negative times are not constrained (they are never used). The constant `M` is required to be
nonnegative; this is no restriction (enlarge `M`), and it is automatic on a nontrivial space
(`‖T 0‖ = 1`), but it keeps the Laplace bound `M / (Re μ - ω)` true on the zero space.

API in this file:
* `T_comm`, `norm_T_apply_le`, `T_apply_add`;
* `mono`: enlarge the constants `M`, `ω`;
* `restrict`: restriction to an invariant submodule (tex 1433: restriction of `L₀` to `ker ℓ`);
* `ofExp`: the uniformly continuous semigroup `exp(tA)` of a bounded operator, `M = 1`,
  `ω = ‖A‖` (bounded sector generators, BP1, tex 1424, 1649);
* `ofSkewAdd`: `exp(t(S + K))` with `S† = -S`, `M = 1`, `ω = ‖K‖` (T0.1).

The adjoint semigroup on a Hilbert space (`ExpSemigroup.adjoint`) is built in
`Semigroups/Adjoint.lean`, after the Laplace transform, which its strong continuity uses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace UnforcedLeray.Infra

/-- **T7.1.** An exponentially bounded strongly continuous semigroup on `X`. -/
structure ExpSemigroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The time-`t` operator. -/
  T : ℝ → X →L[ℂ] X
  T_zero : T 0 = 1
  T_add : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s ∘L T t
  T_cont : ∀ x, ContinuousOn (fun t => T t x) (Set.Ici 0)
  /-- The growth constant `M`. -/
  M : ℝ
  /-- The growth rate `ω`. -/
  ω : ℝ
  M_nonneg : 0 ≤ M
  T_le : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)

namespace ExpSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (S : ExpSemigroup X)

theorem T_zero_apply (x : X) : S.T 0 x = x := by
  rw [S.T_zero, ContinuousLinearMap.one_apply]

theorem T_apply_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    S.T (s + t) x = S.T s (S.T t x) := by
  rw [S.T_add s t hs ht, ContinuousLinearMap.comp_apply]

/-- The operators of a semigroup commute. -/
theorem T_comm {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : S.T s ∘L S.T t = S.T t ∘L S.T s := by
  rw [← S.T_add s t hs ht, ← S.T_add t s ht hs, add_comm]

theorem T_comm_apply {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    S.T s (S.T t x) = S.T t (S.T s x) := by
  simpa using congrArg (fun A : X →L[ℂ] X => A x) (S.T_comm hs ht)

theorem norm_T_apply_le {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ‖S.T t x‖ ≤ S.M * Real.exp (S.ω * t) * ‖x‖ :=
  ((S.T t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (S.T_le t ht) (norm_nonneg _))

/-- On a compact time interval `[0, b]` the semigroup is bounded by `M e^{|ω| b}`. -/
theorem norm_T_le_of_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) :
    ‖S.T t‖ ≤ S.M * Real.exp (|S.ω| * b) := by
  refine (S.T_le t ht).trans (mul_le_mul_of_nonneg_left ?_ S.M_nonneg)
  refine Real.exp_le_exp.2 ?_
  calc S.ω * t ≤ |S.ω| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht
    _ ≤ |S.ω| * b := mul_le_mul_of_nonneg_left htb (abs_nonneg _)

/-- Enlarging the growth constants. -/
def mono {M' ω' : ℝ} (hM : S.M ≤ M') (hω : S.ω ≤ ω') : ExpSemigroup X where
  T := S.T
  T_zero := S.T_zero
  T_add := S.T_add
  T_cont := S.T_cont
  M := M'
  ω := ω'
  M_nonneg := S.M_nonneg.trans hM
  T_le t ht := (S.T_le t ht).trans (mul_le_mul hM (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_right hω ht)) (Real.exp_pos _).le (S.M_nonneg.trans hM))

@[simp] theorem mono_T {M' ω' : ℝ} (hM : S.M ≤ M') (hω : S.ω ≤ ω') : (S.mono hM hω).T = S.T :=
  rfl

/-- The restriction of a time-`t` operator to an invariant submodule. -/
def restrictOp (A : X →L[ℂ] X) (V : Submodule ℂ X) (hA : ∀ x ∈ V, A x ∈ V) : V →L[ℂ] V :=
  (A.comp V.subtypeL).codRestrict V fun x => hA x x.2

@[simp] theorem coe_restrictOp_apply (A : X →L[ℂ] X) (V : Submodule ℂ X)
    (hA : ∀ x ∈ V, A x ∈ V) (x : V) : (restrictOp A V hA x : X) = A x :=
  rfl

theorem norm_restrictOp_le (A : X →L[ℂ] X) (V : Submodule ℂ X) (hA : ∀ x ∈ V, A x ∈ V) :
    ‖restrictOp A V hA‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [← Submodule.norm_coe, coe_restrictOp_apply, ← Submodule.norm_coe x]
    exact A.le_opNorm _

/-- **Restriction to an invariant submodule** (closed when completeness is needed). Times `t < 0`
are sent to `T 0` restricted (`max t 0`). -/
def restrict (V : Submodule ℂ X) (hV : ∀ t, 0 ≤ t → ∀ x ∈ V, S.T t x ∈ V) :
    ExpSemigroup V where
  T t := restrictOp (S.T (max t 0)) V (hV _ (le_max_right _ _))
  T_zero := by
    ext x
    simp [S.T_zero]
  T_add s t hs ht := by
    ext x
    simp only [coe_restrictOp_apply, ContinuousLinearMap.comp_apply, max_eq_left hs,
      max_eq_left ht, max_eq_left (add_nonneg hs ht), S.T_apply_add hs ht]
  T_cont x := by
    have h : ContinuousOn (fun t => S.T t x) (Ici 0) := S.T_cont x
    have h' : ContinuousOn (fun t => ((restrictOp (S.T (max t 0)) V
        (hV _ (le_max_right _ _)) x : V) : X)) (Ici 0) :=
      h.congr fun t ht => by simp [max_eq_left (show (0 : ℝ) ≤ t from ht)]
    exact (continuousOn_iff_continuous_restrict.2
      (continuous_induced_rng.2 (continuousOn_iff_continuous_restrict.1 h')))
  M := S.M
  ω := S.ω
  M_nonneg := S.M_nonneg
  T_le t ht := (norm_restrictOp_le _ _ _).trans (by
    rw [max_eq_left ht]
    exact S.T_le t ht)

@[simp] theorem restrict_T_apply (V : Submodule ℂ X) (hV : ∀ t, 0 ≤ t → ∀ x ∈ V, S.T t x ∈ V)
    {t : ℝ} (ht : 0 ≤ t) (x : V) : ((S.restrict V hV).T t x : X) = S.T t x := by
  simp [restrict, max_eq_left ht]

section Bounded

variable [CompleteSpace X]

/-- **The semigroup of a bounded generator** `T t = exp(tA)`, `M = 1`, `ω = ‖A‖`
(bounded sector generators of BP1; tex 1424, 1649). -/
def ofExp (A : X →L[ℂ] X) : ExpSemigroup X where
  T t := NormedSpace.exp ((t : ℂ) • A)
  T_zero := by simp
  T_add s t _ _ := by
    rw [BanachExp.exp_smul_add]
    rfl
  T_cont x := (continuous_exp_smul_apply A x).continuousOn
  M := 1
  ω := ‖A‖
  M_nonneg := zero_le_one
  T_le t ht := by
    rw [one_mul, mul_comm]
    simpa [abs_of_nonneg ht] using BanachExp.norm_exp_smul_le A t

@[simp] theorem ofExp_T (A : X →L[ℂ] X) (t : ℝ) :
    (ofExp A).T t = NormedSpace.exp ((t : ℂ) • A) :=
  rfl

end Bounded

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Skew-adjoint plus bounded** (T0.1): `exp(t(S + K))` with `S† = -S` is an `ExpSemigroup`
with `M = 1`, `ω = ‖K‖` (tex 1424, 1649: `L₀ = T + A`, `T = -2iΩ` skew-adjoint). -/
def ofSkewAdd {Sk K : H →L[ℂ] H} (hS : ContinuousLinearMap.adjoint Sk = -Sk) :
    ExpSemigroup H where
  T t := NormedSpace.exp ((t : ℂ) • (Sk + K))
  T_zero := by simp
  T_add s t _ _ := by
    rw [BanachExp.exp_smul_add]
    rfl
  T_cont x := (continuous_exp_smul_apply (Sk + K) x).continuousOn
  M := 1
  ω := ‖K‖
  M_nonneg := zero_le_one
  T_le t ht := by
    rw [one_mul, mul_comm]
    exact norm_exp_skew_add_le hS ht

@[simp] theorem ofSkewAdd_T {Sk K : H →L[ℂ] H} (hS : ContinuousLinearMap.adjoint Sk = -Sk)
    (t : ℝ) : (ofSkewAdd (K := K) hS).T t = NormedSpace.exp ((t : ℂ) • (Sk + K)) :=
  rfl

end Hilbert

end ExpSemigroup

end UnforcedLeray.Infra
