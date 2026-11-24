import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs

/-!
# Decomposition of `psiWordPointwise` (task `PartIII-b:C/asrc/ra/9/1/2/9/2/1`)

Source `the November 2 reference manuscript`
lines 5063-5071, 5076-5079, 4979-4985.  Scalar mirror of `ra_9_1_2_9_1_1/Defs.lean`:
`psiM = Σ_j psiSummandM j`; every summand is `C⁴` on `s > 0`, its words of length `≤ 4` are bounded
by `C M(A) s^{5/2} envTerm`; the envelope gives a locally uniform summable majorant; termwise
conormal differentiation; envelope summability (`envSummable`, reused from the Hp chain).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The `j`-th lattice summand of `ψ^p_A` (source 4979): `(tr A^y_mer) ψ_j - (A^y_mer x_j)·∇ψ_j`. -/
def psiSummandM (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) : Chart → ℝ :=
  fun p => merTrace (Ay ν χf A p.1) * psij ν p.1 j p.2
    - fderiv ℝ (psij ν p.1 j) p.2 (merApply (Ay ν χf A p.1) (xj ν j p.2))

/-- The `(a,b)` Gaussian part of the summand: `∂_a ψ_j = a⁻² (x_j)_a e^{-|x_j|²/(4a)}`, so
`ψ-summand = Σ_{a,b} A_{ab} ( δ_{ab} ψ_j - (x_j)_b ∂_a ψ_j )`. -/
def psiSummandGauss (ν : ℝ) (j : ℤ) (a b : Fin 2) : Chart → ℝ :=
  fun p => (if a = b then -2 * (ageA ν p.1)⁻¹ * Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) else 0)
    - (ageA ν p.1)⁻¹ ^ 2 * comp2 (xj ν j p.2) a * comp2 (xj ν j p.2) b
        * Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))

/-- Locally uniform summable majorant on `s > 0` (scalar). -/
def PsiLocSumm (G : ℤ → Chart → ℝ) : Prop :=
  ∀ p ∈ UChart, ∃ N ∈ 𝓝 p, ∃ u : ℤ → ℝ, Summable u ∧ ∀ j, ∀ q ∈ N, |G j q| ≤ u j

/-- `ψ^p_A` is the lattice sum of the summands (definitional, `psipA`). -/
theorem psiSumDecomp (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    psiM ν χf A = fun p => ∑' j : ℤ, psiSummandM ν χf A j p := rfl

/-- The summand is linear in `A^y`, for `ν > 0`, `s > 0`: `psiSummandM = Σ_{a,b} A^y_{ab}(s) · psiSummandGauss a b`
(`merApply`, `merTrace` expand over the basis; `gp_fderiv_psij` in
`Concrete/ReturnInst/HpPsiTermSummable/Gauss.lean:238` gives `∇ψ_j`). -/
def PsiSummandExpand : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ), ∀ p ∈ UChart,
    psiSummandM ν χf A j p = ∑ a : Fin 2, ∑ b : Fin 2,
      Ay ν χf A p.1 (mi a) (mi b) * psiSummandGauss ν j a b p

/-- Each summand is `C⁴` on `s > 0`. -/
def PsiSummandSmooth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ j : ℤ,
    ContDiffOn ℝ 4 (psiSummandM ν χf A j) UChart

/-- Word bound on the Gaussian parts (monomials of degree `≤ 2` in `x_j` times `a⁻¹, a⁻²` times the
Gaussian; each conormal derivative raises the polynomial degree by `≤ 2`, so `m = 11` works), for
`0 < νs ≤ 1.1` (so `a ∈ [1, 2.1]`). -/
def PsiGaussWordBound : Prop :=
  ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 0 < s → ν * s ≤ 11 / 10 →
    ∀ w ∈ budgetWords, ∀ (a b : Fin 2) (x : ℝ × ℝ) (j : ℤ),
      |wordW w (psiSummandGauss ν j a b) (s, x)| ≤ C * envTerm m ν j (s, x)

/-- Word bound for one summand (source 5063-5071), for all `s > 0`. -/
def PsiSummandBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
    ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s →
      ∀ w ∈ budgetWords, ∀ (x : ℝ × ℝ) (j : ℤ),
        |wordW w (psiSummandM ν χf A j) (s, x)|
          ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x)

/-- Pointwise envelope bound gives a locally uniform summable majorant (scalar `EnvLocSumm`). -/
def PsiEnvLocSumm : Prop :=
  ∀ (m : ℕ) (ν K : ℝ), 0 < ν → ∀ G : ℤ → Chart → ℝ,
    (∀ j, ∀ p ∈ UChart, |G j p| ≤ K * p.1 ^ (5 / 2 : ℝ) * envTerm m ν j p) → PsiLocSumm G

/-- Termwise conormal differentiation (scalar `TermwiseWord`). -/
def PsiTermwiseWord : Prop :=
  ∀ F : ℤ → Chart → ℝ, (∀ j, ContDiffOn ℝ 4 (F j) UChart) →
    (∀ w ∈ budgetWords, PsiLocSumm (fun j => wordW w (F j))) →
    ∀ w ∈ budgetWords, ∀ p ∈ UChart,
      wordW w (fun q => ∑' j : ℤ, F j q) p = ∑' j : ℤ, wordW w (F j) p

/-- **Assembly**: `PsiWordPointwise` from the lemmas. -/
theorem psiWordPointwise_of (as : ℝ) (χf : ℝ → ℝ)
    (hS : PsiSummandSmooth as χf) (hB : PsiSummandBound as χf)
    (hE : EnvSummable) (hL : PsiEnvLocSumm) (hT : PsiTermwiseWord) : PsiWordPointwise as χf := by
  intro hχ
  obtain ⟨C, m, hC, H⟩ := hB hχ
  refine ⟨C, 0, m, 1, hC, one_pos, ?_⟩
  intro ν hν _ A hA s hs _ w hw x
  have hloc : ∀ w ∈ budgetWords, PsiLocSumm (fun j => wordW w (psiSummandM ν χf A j)) := by
    intro w hw
    refine hL m ν (C * affM ν χf A) hν _ ?_
    intro j p hp
    have := H ν hν A hA p.1 hp.1 w hw p.2 j
    simpa [mul_assoc] using this
  have ht := hT (psiSummandM ν χf A) (hS hχ ν hν A hA) hloc w hw (s, x) ⟨hs, Set.mem_univ _⟩
  have hsum : Summable (fun j : ℤ => C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x)) :=
    (hE m ν hν (s, x) hs).mul_left _
  have hnn : ∀ j : ℤ, ‖wordW w (psiSummandM ν χf A j) (s, x)‖
      ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x) :=
    fun j => by simpa [Real.norm_eq_abs] using H ν hν A hA s hs w hw x j
  have hnsum : Summable (fun j : ℤ => ‖wordW w (psiSummandM ν χf A j) (s, x)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnn hsum
  rw [psiSumDecomp ν χf A, ht, ← Real.norm_eq_abs]
  calc ‖∑' j : ℤ, wordW w (psiSummandM ν χf A j) (s, x)‖
      ≤ ∑' j : ℤ, ‖wordW w (psiSummandM ν χf A j) (s, x)‖ := norm_tsum_le_tsum_norm hnsum
    _ ≤ ∑' j : ℤ, C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x) :=
        hnsum.tsum_le_tsum hnn hsum
    _ = C * ν⁻¹ ^ 0 * affM ν χf A * s ^ (5 / 2 : ℝ) * latEnv m ν s x := by
        rw [tsum_mul_left]
        simp only [pow_zero, mul_one, latEnv, envTerm]

end UnforcedLeray.Short.PartIIIb.Concrete
