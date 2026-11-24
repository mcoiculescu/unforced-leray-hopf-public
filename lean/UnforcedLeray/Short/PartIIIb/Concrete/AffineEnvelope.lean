import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import UnforcedLeray.Short.PartIIIb.Concrete.AffineBoundSpaces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAffExamples
import Mathlib.Data.Nat.Choose.Sum

/-!
# The generic envelope `M(A) ≤ C e^{1.1 a_s/ν} ‖A‖_𝒜` (source 5089-5091)

Source of record: `the November 2 reference manuscript` (73 pages).

Step (3) of `ORG:stmt/PartIII-b/GeneralAffineBounds/grad-pin`.  Source 5089-5091: "For generic
`A ∈ 𝒜`, `M(A) ≤ Ce^{1.1a_s/ν}‖A‖_𝒜`", where
`M(A) = sup_{0<s≤1.1/ν} s^{-5/2} Σ_{j≤6} |(s∂_s)^j A^y(s)|`, `A^y = χ_f A` (source 4955-4962,
`affM`), and `‖A‖_𝒜 = sup_{s>0} e^{-a_s s} s^{-5/2} Σ_{j≤6} |(s∂_s)^j A(s)|` (source 4741-4752,
`affNorm`).  The envelope feeds `PLBound` (source 5883-5890, `‖𝒫‖_{𝒜→𝓔} ≤ P_ν e^{1.1a_s/ν}`)
through the hypothesis `henv` of `affineFieldData_of` (`Concrete/ReturnInst/AffineFields.lean`).

## Proof (the source's one line, expanded)

`s∂_s` is a derivation, so on `s > 0`
`(s∂_s)^j(χ_f A) = Σ_{i+k=j} C(j,i) (s∂_s)^i χ_f · (s∂_s)^k A` (Leibniz, `SDerivIterLeibniz`).
`s∂_s` commutes with dilations: `(s∂_s)^i[χ̂_f(ν·)](s) = ((t∂_t)^i χ̂_f)(νs)`
(`sDerivIterR_comp_mul`), and on `0 ≤ νs ≤ 1.1` this is bounded by a constant `K` depending only
on the `C^6` norm of `χ̂_f` on `[0, 1.1]` (`sDerivIterR_bound`).  Hence for `0 < s ≤ 1.1/ν`
`s^{-5/2} Σ_j |(s∂_s)^j A^y(s)| ≤ C₀ s^{-5/2} Σ_k |(s∂_s)^k A(s)|
  = C₀ e^{a_s s} · e^{-a_s s} s^{-5/2} Σ_k |(s∂_s)^k A(s)| ≤ C₀ e^{1.1 a_s/ν} ‖A‖_𝒜`
for `a_s ≥ 0`.  `C₀` depends only on `χ̂_f`.

## Contents

* `matTen`, `norm_matTen` : the Frobenius norm `frob` is the norm of `Ten3`; `frob_add_le`,
  `frob_smul`, `frob_sum_le`.
* `sDerivR`, `sDerivIterR` : `t∂_t` and its iterates on real functions;
  `sDerivIterR_contDiff`, `sDerivIterR_comp_mul`, `sDerivIterR_bound` (proved).
* Leaves (tasks): `SDerivIterDiffOn` (`PartIII-b:C/env/1`), `SDerivIterLeibniz`
  (`PartIII-b:C/env/2`).
* `AffMEnvelope χ` (the statement of source 5089-5091), `affMEnvelope_of` (proved from the
  leaves), `affM_le_norm_of` (the form `M(ιA) ≤ C e^{1.1a_s/ν}‖A‖` consumed at the instance).
  The unconditional `affMEnvelope` is task `PartIII-b:C/env/3`.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open scoped BigOperators

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The Frobenius norm is the norm of `Ten3` -/

/-- A `3×3` matrix in the order `(r, φ, z)` as an element of `Ten3` (Frobenius norm). -/
def matTen (M : Mat3) : Ten3 := WithLp.toLp 2 fun ab => M ab.1 ab.2

@[simp] theorem matTen_apply (M : Mat3) (a b : Fin 3) : matTen M (a, b) = M a b := rfl

theorem matTen_add (M N : Mat3) : matTen (M + N) = matTen M + matTen N := by
  ext ab; simp [matTen]

theorem matTen_smul (c : ℝ) (M : Mat3) : matTen (c • M) = c • matTen M := by
  ext ab; simp [matTen]

/-- `|M| = ‖M‖_{Ten3}`. -/
theorem norm_matTen (M : Mat3) : ‖matTen M‖ = frob M := by
  rw [EuclideanSpace.norm_eq, frob, Fintype.sum_prod_type]
  simp [matTen, Real.norm_eq_abs, sq_abs]

theorem frob_add_le (M N : Mat3) : frob (M + N) ≤ frob M + frob N := by
  rw [← norm_matTen, ← norm_matTen, ← norm_matTen, matTen_add]
  exact norm_add_le _ _

theorem frob_smul (c : ℝ) (M : Mat3) : frob (c • M) = |c| * frob M := by
  rw [← norm_matTen, ← norm_matTen, matTen_smul, norm_smul, Real.norm_eq_abs]

theorem frob_zero' : frob 0 = 0 := by simp [frob]

theorem frob_sum_le {ι : Type} (t : Finset ι) (g : ι → Mat3) :
    frob (∑ i ∈ t, g i) ≤ ∑ i ∈ t, frob (g i) :=
  Finset.le_sum_of_subadditive frob frob_zero'.le frob_add_le t g

/-! ## 2. `t∂_t` on real functions -/

/-- `s ∂_s` on real functions. -/
def sDerivR (f : ℝ → ℝ) : ℝ → ℝ := fun s => s * deriv f s

/-- `(s ∂_s)^i` on real functions. -/
def sDerivIterR : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | i + 1, f => sDerivR (sDerivIterR i f)

/-- `(t∂_t)^i` preserves `C^∞`. -/
theorem sDerivIterR_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ∀ i : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sDerivIterR i f)
  | 0 => hf
  | i + 1 => by
    have h := sDerivIterR_contDiff hf i
    show ContDiff ℝ _ (fun s => s * deriv (sDerivIterR i f) s)
    exact contDiff_id.mul (contDiff_infty_iff_deriv.1 h).2

/-- `t∂_t` commutes with dilations: `(s∂_s)^i[χ(ν·)](s) = ((t∂_t)^i χ)(νs)` (no regularity
needed: `deriv` of `t ↦ g(νt)` is `ν g'(νt)` in Mathlib's convention). -/
theorem sDerivIterR_comp_mul (χ : ℝ → ℝ) (ν : ℝ) :
    ∀ i : ℕ, sDerivIterR i (fun t => χ (ν * t)) = fun s => sDerivIterR i χ (ν * s)
  | 0 => rfl
  | i + 1 => by
    funext s
    have ih := sDerivIterR_comp_mul χ ν i
    show s * deriv (sDerivIterR i (fun t => χ (ν * t))) s =
      (ν * s) * deriv (sDerivIterR i χ) (ν * s)
    rw [ih]
    have h := deriv_comp_mul_left ν (sDerivIterR i χ) s
    simp only [smul_eq_mul] at h
    rw [show (fun s => sDerivIterR i χ (ν * s)) = (sDerivIterR i χ <| ν * ·) from rfl, h]
    ring

/-- For a `C^∞` profile, `(t∂_t)^i χ` (`i ≤ 6`) is bounded on `[0, 1.1]` (compactness); the bound
depends only on the `C^6` norm of `χ` there. -/
theorem sDerivIterR_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i : ℕ, i ≤ 6 → ∀ t ∈ Icc (0 : ℝ) (11 / 10), |sDerivIterR i χ t| ≤ K := by
  have hb : ∀ i : ℕ, ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) (11 / 10), ‖sDerivIterR i χ t‖ ≤ K := fun i =>
    isCompact_Icc.exists_bound_of_continuousOn
      (sDerivIterR_contDiff hχ i).continuous.continuousOn
  choose K hK using hb
  refine ⟨∑ i ∈ Finset.range 7, |K i|, Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  intro i hi t ht
  calc |sDerivIterR i χ t| = ‖sDerivIterR i χ t‖ := (Real.norm_eq_abs _).symm
    _ ≤ K i := hK i t ht
    _ ≤ |K i| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range 7, |K j| :=
      Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))

/-! ## 3. Leaves -/

/-- `C/env/1`: for a matrix function that is `C^6` on `(0,∞)` (an element of `𝒜`, source
4741-4745), `(s∂_s)^k A` is differentiable on `(0,∞)` for `k < 6` (`s∂_s` maps `C^{m+1}` to
`C^m` on the open set `(0,∞)`). -/
def SDerivIterDiffOn : Prop :=
  ∀ A : ℝ → Mat3, ContDiffOn ℝ 6 A (Ioi 0) → ∀ k : ℕ, k < 6 →
    DifferentiableOn ℝ (sDerivIter k A) (Ioi 0)

/-- `C/env/2`: Leibniz rule for the derivation `s∂_s` on `(0,∞)`:
`(s∂_s)^j(f A) = Σ_{i+k=j} C(j,i) (s∂_s)^i f · (s∂_s)^k A`, given differentiability of the
iterates used (source 4955-4962: `A^y = χ_f A`, the cutoff derivative included). -/
def SDerivIterLeibniz : Prop :=
  ∀ (f : ℝ → ℝ) (A : ℝ → Mat3) (j : ℕ), (∀ i : ℕ, Differentiable ℝ (sDerivIterR i f)) →
    (∀ k : ℕ, k < j → DifferentiableOn ℝ (sDerivIter k A) (Ioi 0)) →
    EqOn (sDerivIter j (fun t => f t • A t))
      (fun s => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
        j.choose ij.1 • (sDerivIterR ij.1 f s • sDerivIter ij.2 A s)) (Ioi 0)

/-! ## 4. The envelope -/

/-- Source 5089-5091: for generic `A ∈ 𝒜`, `M(A) ≤ C e^{1.1a_s/ν} ‖A‖_𝒜`, with `C` depending
only on the cutoff profile `χ̂_f` (through its `C^6` norm on `[0,1.1]`), uniformly in `a_s ≥ 0`
and `ν > 0`. -/
def AffMEnvelope (χ : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (as ν : ℝ) (A : ℝ → Mat3), 0 ≤ as → 0 < ν → IsAffElem as A →
    affM ν χ A ≤ C * Real.exp (1.1 * as / ν) * affNorm as A

/-- `Σ_{i+k=j} C(j,i)` (the Leibniz constant). -/
def chooseSum (j : ℕ) : ℝ := ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, (j.choose ij.1 : ℝ)

theorem chooseSum_nonneg (j : ℕ) : 0 ≤ chooseSum j :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The envelope from the two leaves, for any `C^∞` cutoff profile. -/
theorem affMEnvelope_of (hD : SDerivIterDiffOn) (hL : SDerivIterLeibniz) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) : AffMEnvelope χ := by
  obtain ⟨K, hK0, hK⟩ := sDerivIterR_bound hχ
  have hC00 : 0 ≤ (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K :=
    mul_nonneg (Finset.sum_nonneg fun j _ => chooseSum_nonneg j) hK0
  refine ⟨(∑ j ∈ Finset.range (6 + 1), chooseSum j) * K, hC00, ?_⟩
  intro as ν A has hν hA
  set C0 := (∑ j ∈ Finset.range (6 + 1), chooseSum j) * K with hC0
  have hfi : ∀ i, sDerivIterR i (fun t => χ (ν * t)) = fun s => sDerivIterR i χ (ν * s) :=
    sDerivIterR_comp_mul χ ν
  have hfd : ∀ i, Differentiable ℝ (sDerivIterR i (fun t => χ (ν * t))) := by
    intro i
    rw [hfi i]
    have hg : Differentiable ℝ (sDerivIterR i χ) :=
      (sDerivIterR_contDiff hχ i).differentiable (by simp)
    intro s
    exact (hg (ν * s)).comp s (differentiableAt_id.const_mul ν)
  have hAd : ∀ k : ℕ, k < 6 → DifferentiableOn ℝ (sDerivIter k A) (Ioi 0) := hD A hA.smooth
  -- pointwise comparison of the conormal sums
  have hpt : ∀ s ∈ Ioc (0 : ℝ) ((11 / 10) / ν), affSum 6 (Ay ν χ A) s ≤ C0 * affSum 6 A s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hνs : ν * s ∈ Icc (0 : ℝ) (11 / 10) := by
      refine ⟨by positivity, ?_⟩
      have := (le_div_iff₀ hν).1 hs.2
      linarith
    have hterm : ∀ j ∈ Finset.range (6 + 1),
        frob (sDerivIter j (Ay ν χ A) s) ≤ chooseSum j * K * affSum 6 A s := by
      intro j hj
      have hj6 : j ≤ 6 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hL' := hL (fun t => χ (ν * t)) A j hfd (fun k hk => hAd k (by omega)) hs0
      have hAy : Ay ν χ A = fun t => (fun t => χ (ν * t)) t • A t := rfl
      rw [hAy, hL']
      calc frob (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, j.choose ij.1 •
              (sDerivIterR ij.1 (fun t => χ (ν * t)) s • sDerivIter ij.2 A s))
          ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, frob (j.choose ij.1 •
              (sDerivIterR ij.1 (fun t => χ (ν * t)) s • sDerivIter ij.2 A s)) :=
            frob_sum_le _ _
        _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, (j.choose ij.1 : ℝ) * (K * affSum 6 A s) := by
            apply Finset.sum_le_sum
            intro ij hij
            have hij' := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
            rw [← Nat.cast_smul_eq_nsmul ℝ, frob_smul, frob_smul,
              abs_of_nonneg (Nat.cast_nonneg _)]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            have h1 : |sDerivIterR ij.1 (fun t => χ (ν * t)) s| ≤ K := by
              rw [hfi]
              exact hK ij.1 (by omega) _ hνs
            have h2 : frob (sDerivIter ij.2 A s) ≤ affSum 6 A s :=
              Finset.single_le_sum (f := fun k => frob (sDerivIter k A s))
                (fun k _ => frob_nonneg _) (Finset.mem_range.2 (by omega))
            exact mul_le_mul h1 h2 (frob_nonneg _) hK0
        _ = chooseSum j * K * affSum 6 A s := by
            rw [chooseSum, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => by ring
    show ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s) ≤ C0 * affSum 6 A s
    calc ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s)
        ≤ ∑ j ∈ Finset.range (6 + 1), chooseSum j * K * affSum 6 A s := Finset.sum_le_sum hterm
      _ = C0 * affSum 6 A s := by rw [hC0, ← Finset.sum_mul, ← Finset.sum_mul]
  -- the supremum
  unfold affM
  apply csSup_le ((nonempty_Ioc.2 (by positivity)).image _)
  rintro _ ⟨s, hs, rfl⟩
  have hs0 : 0 < s := hs.1
  have hterm_le : affTerm as 6 A s ≤ affNorm as A := le_csSup hA.bdd ⟨s, hs0, rfl⟩
  have hexp : Real.exp (as * s) ≤ Real.exp (1.1 * as / ν) := by
    apply Real.exp_le_exp.2
    have h1 : s ≤ (11 / 10) / ν := hs.2
    rw [show (1.1 : ℝ) * as / ν = as * ((11 / 10) / ν) by norm_num; ring]
    exact mul_le_mul_of_nonneg_left h1 has
  have hid : s ^ (-(5 / 2 : ℝ)) * affSum 6 A s = Real.exp (as * s) * affTerm as 6 A s := by
    unfold affTerm
    have h1 : Real.exp (as * s) * Real.exp (-as * s) = 1 := by
      rw [← Real.exp_add, show as * s + -as * s = 0 by ring, Real.exp_zero]
    calc s ^ (-(5 / 2 : ℝ)) * affSum 6 A s
        = (Real.exp (as * s) * Real.exp (-as * s)) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 A s) := by
          rw [h1, one_mul]
      _ = _ := by ring
  have hrp : 0 ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
  calc s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s
      ≤ s ^ (-(5 / 2 : ℝ)) * (C0 * affSum 6 A s) := mul_le_mul_of_nonneg_left (hpt s hs) hrp
    _ = C0 * (Real.exp (as * s) * affTerm as 6 A s) := by rw [← hid]; ring
    _ ≤ C0 * (Real.exp (1.1 * as / ν) * affNorm as A) := by
        apply mul_le_mul_of_nonneg_left _ hC00
        exact mul_le_mul hexp hterm_le (affTerm_nonneg as 6 A s hs0) (Real.exp_pos _).le
    _ = C0 * Real.exp (1.1 * as / ν) * affNorm as A := by ring

/-- The envelope for the source cutoff `χ̂_f` (source 4953-4956), from the two leaves. -/
theorem affMEnvelope_of_cutoff (hD : SDerivIterDiffOn) (hL : SDerivIterLeibniz) {χ : ℝ → ℝ}
    (hχ : IsSourceCutoffC χ) : AffMEnvelope χ :=
  affMEnvelope_of hD hL hχ.smooth

/-- The envelope in the form consumed at the instance (`henv` of `affineFieldData_of`, with
`C_env = C e^{1.1a_s/ν}`): for an inclusion `ι` of a normed space into `𝒜` with
`‖ιA‖_𝒜 ≤ ‖A‖`, `M(ιA) ≤ C e^{1.1a_s/ν} ‖A‖`, `C` independent of `a_s, ν`. -/
theorem affM_le_norm_of {χ : ℝ → ℝ} (h : AffMEnvelope χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (as ν : ℝ) {Aff : Type} [NormedAddCommGroup Aff]
      (ι : Aff → (ℝ → Mat3)), 0 ≤ as → 0 < ν → (∀ A, IsAffElem as (ι A)) →
      (∀ A, affNorm as (ι A) ≤ ‖A‖) → ∀ A, affM ν χ (ι A) ≤ C * Real.exp (1.1 * as / ν) * ‖A‖ := by
  obtain ⟨C, hC, hM⟩ := h
  refine ⟨C, hC, ?_⟩
  intro as ν Aff _ ι has hν hι hn A
  exact (hM as ν (ι A) has hν (hι A)).trans
    (mul_le_mul_of_nonneg_left (hn A) (mul_nonneg hC (Real.exp_pos _).le))

end UnforcedLeray.Short.PartIIIb.Concrete
