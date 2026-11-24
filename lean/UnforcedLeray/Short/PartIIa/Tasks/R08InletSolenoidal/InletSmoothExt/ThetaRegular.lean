import UnforcedLeray.Short.PartIIa.Sub.R08_2
import UnforcedLeray.Lib.Train.Profile
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# Part II-a, task `PartII-a:R08/2/1`: regularity of the periodic Gaussian profile `θ_c`

Source of record: `the November 2 reference manuscript`, lines 1330-1334
(the smooth `c`-periodic Gaussian datum).

This file proves the Prop `ThetaRegular` of `Sub/R08_2.lean` for every `c > 0`.

Method. `inletTheta c q = ∑ₙ -2 e^{-(q-nc)²/4}` is the periodization of `ψ₀` along the line
`η = 0`, since `Train.psi0 w = -2 e^{-(w₁²+w₂²)/4}`. Smoothness comes from
`Gaussian.contDiff_periodize`, with translate bounds from `Train.norm_iteratedFDeriv_psi0_le`.
Periodicity comes from `Gaussian.periodize_add_period`. A general lemma bounds the iterated
derivatives of any smooth `c`-periodic function of one variable, by continuity on one period.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Translate bound for the `k`-th derivative of `ψ₀` (uniform in the second variable). -/
theorem th_psi0_translate (k : ℕ) : ∃ C : ℝ, ∀ z : ℝ × ℝ,
    ‖iteratedFDeriv ℝ k UnforcedLeray.Train.psi0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := UnforcedLeray.Train.norm_iteratedFDeriv_psi0_le k
  obtain ⟨K, -, hk⟩ := UnforcedLeray.Train.exp_neg_sq_div_eight_le_rpow
  refine ⟨A * K, fun z => (hb z).trans ?_⟩
  have h1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ Real.exp (-z.1 ^ 2 / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg z.2])
  calc A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ A * (K * (1 + |z.1|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans (hk z.1)) hA
    _ = A * K * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

/-- The profile `θ_c` is the periodization of `ψ₀` restricted to the line `η = 0`. -/
theorem th_inletTheta_eq_periodize (c q : ℝ) :
    inletTheta c q = UnforcedLeray.Gaussian.periodize c UnforcedLeray.Train.psi0 (q, 0) := by
  unfold inletTheta UnforcedLeray.Gaussian.periodize
  refine tsum_congr fun n => ?_
  show -2 * Real.exp (-((q - (n : ℝ) * c) ^ 2 / 4)) =
    -2 * Real.exp (-((q - (n : ℝ) * c) ^ 2 + (0 : ℝ) ^ 2) / 4)
  congr 2
  ring

/-- `θ_c` is `C^∞` for `c ≠ 0`. -/
theorem th_contDiff_inletTheta {c : ℝ} (hc : c ≠ 0) : ContDiff ℝ ∞ (inletTheta c) := by
  have hP : ContDiff ℝ ∞ (UnforcedLeray.Gaussian.periodize c UnforcedLeray.Train.psi0) :=
    UnforcedLeray.Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc
      UnforcedLeray.Train.contDiff_psi0 (fun k _ => th_psi0_translate k)
  have hL : ContDiff ℝ ∞ (fun q : ℝ => ((q, (0 : ℝ)) : ℝ × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have heq : inletTheta c =
      UnforcedLeray.Gaussian.periodize c UnforcedLeray.Train.psi0 ∘
        fun q : ℝ => ((q, (0 : ℝ)) : ℝ × ℝ) := by
    funext q
    exact th_inletTheta_eq_periodize c q
  rw [heq]
  exact hP.comp hL

/-- `θ_c` is `c`-periodic. -/
theorem th_periodic_inletTheta (c : ℝ) : Function.Periodic (inletTheta c) c := by
  intro q
  rw [th_inletTheta_eq_periodize c (q + c), th_inletTheta_eq_periodize c q]
  exact UnforcedLeray.Gaussian.periodize_add_period c UnforcedLeray.Train.psi0 q 0

/-- A smooth `c`-periodic function of one variable has bounded iterated derivatives of each
order. -/
theorem th_bounded_iteratedFDeriv {g : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g c) (j : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ j g t‖ ≤ B := by
  have hfun : (fun z : ℝ => g (z + c)) = g := funext fun x => hp x
  have hper : Function.Periodic (iteratedFDeriv ℝ j g) c := fun t => by
    have h : iteratedFDeriv ℝ j (fun z : ℝ => g (z + c)) t = iteratedFDeriv ℝ j g (t + c) :=
      iteratedFDeriv_comp_add_right j c t
    rw [hfun] at h
    exact h.symm
  have hcont : Continuous (iteratedFDeriv ℝ j g) :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hper.isBounded_of_continuous hc hcont)
  exact ⟨B, fun t => hB _ ⟨t, rfl⟩⟩

/-- The derivative of a `c`-periodic function is `c`-periodic. -/
theorem th_periodic_deriv {g : ℝ → ℝ} {c : ℝ} (hp : Function.Periodic g c) :
    Function.Periodic (deriv g) c := fun t => by
  have hfun : (fun z : ℝ => g (z + c)) = g := funext fun x => hp x
  have h : deriv (fun z : ℝ => g (z + c)) t = deriv g (t + c) := deriv_comp_add_const g c t
  rw [hfun] at h
  exact h.symm

/-- **Regularity of `θ_c`** (task `PartII-a:R08/2/1`): `θ_c` is `C^∞`, and `θ_c`, `θ_c'` have
bounded iterated derivatives of every order, for every `c > 0`. -/
theorem thetaRegular : ThetaRegular := by
  unfold ThetaRegular
  intro c hc
  have hc' : c ≠ 0 := hc.ne'
  have hA : ContDiff ℝ ∞ (inletTheta c) := th_contDiff_inletTheta hc'
  have hP : Function.Periodic (inletTheta c) c := th_periodic_inletTheta c
  refine ⟨hA, fun j => th_bounded_iteratedFDeriv hc' hA hP j, ?_⟩
  have hD : ContDiff ℝ ∞ (deriv (inletTheta c)) := (contDiff_infty_iff_deriv.1 hA).2
  exact fun j => th_bounded_iteratedFDeriv hc' hD (th_periodic_deriv hP) j

end UnforcedLeray.Short.PartIIa
