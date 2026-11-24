import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.Phi

/-!
# Decomposition of `PsiRingSmooth` (source 4991-4997, 5036-5039)

Source of record: `the November 2 reference manuscript`, line 4991 ("the sums and
their required derivatives converge by Gaussian decay").  `ψ^p_A(s,x) = Σ_j Ψ(s, x_j)` with the
profile `Ψ(s,y) = psiPhi ν s (A^y(s)) y` (`psipA_eq_phi`); `Ψ` is a Gaussian
`e^{-|y|²/(4a)}`, `a = 1+νs`, times a quadratic polynomial in `y` with `C²` coefficients in `s`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- (L1) Local termwise `C²` for a `tsum` over `ℤ` on an open set (Mathlib's
`contDiff_tsum_of_eventually` needs global bounds): each term is `C²` on `U`, and every point of
`U` has a neighbourhood on which `‖D^k f_j‖ ≤ u_j` (`k ≤ 2`) with `u` summable. -/
def LocalTsumC2 : Prop :=
  ∀ (f : ℤ → Chart → ℝ) (U : Set Chart), IsOpen U → (∀ j, ContDiffOn ℝ 2 (f j) U) →
    (∀ x ∈ U, ∃ u : ℤ → ℝ, Summable u ∧ ∃ V ∈ 𝓝 x, ∀ j : ℤ, ∀ y ∈ V, ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (f j) y‖ ≤ u j) →
    ContDiffOn ℝ 2 (fun p => ∑' j : ℤ, f j p) U

/-- The lattice profile as a function on the chart. -/
def psiProfile (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → ℝ :=
  fun p => psiPhi ν p.1 (Ay ν χf A p.1) p.2

/-- (L2) The profile `Ψ` is `C²` jointly on `s > 0` (`A ∈ 𝒜` is `C⁶` there, `A^y = χ_f A`). -/
def PsiProfileSmooth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 2 (psiProfile ν χf A) (Ioi 0 ×ˢ univ)

/-- (L3) Gaussian bound on the first two derivatives of the profile, uniformly for `s` in a
compact subinterval of `(0,∞)`: `‖D^k Ψ(s,y)‖ ≤ C e^{-|y|²/(8(1+2νs₀))}` for `k ≤ 2`,
`s ∈ [s₀/2, 2s₀]` (polynomial growth absorbed into the Gaussian). -/
def PsiProfileGaussBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s0 : ℝ, 0 < s0 → ∃ C : ℝ, ∀ p : Chart, p.1 ∈ Icc (s0 / 2) (2 * s0) →
      ∀ k : ℕ, k ≤ 2 →
        ‖iteratedFDeriv ℝ k (psiProfile ν χf A) p‖ ≤
          C * Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * s0)))

/-- The `j`-th lattice term as a function on the chart: `Ψ(s, x_j)`. -/
def psiTerm (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) : Chart → ℝ :=
  fun p => psiProfile ν χf A (p.1, xj ν j p.2)

/-- (L4) Summable majorant of the translated terms near any point of `s > 0` (derivatives of
order `≤ 2`), from the Gaussian bound (L3): `e^{-|x_j|²/(8a')}` with `x_j = (q - jc, η)`, `|q|`
locally bounded, is dominated by a summable sequence in `j`. -/
def PsiTermLocalBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ x ∈ (Ioi 0 ×ˢ univ : Set Chart), ∃ u : ℤ → ℝ, Summable u ∧ ∃ V ∈ 𝓝 x,
      ∀ j : ℤ, ∀ y ∈ V, ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k (psiTerm ν χf A j) y‖ ≤ u j

/-- The target follows from (L1)-(L4). -/
theorem psiRingSmooth_of (as : ℝ) (χf : ℝ → ℝ) (h1 : LocalTsumC2)
    (h2 : PsiProfileSmooth as χf) (h4 : PsiTermLocalBound as χf) : PsiRingSmooth as χf := by
  intro hχ ν hν A hA
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hprof := h2 hχ ν hν A hA
  have hterm : ∀ j : ℤ, ContDiffOn ℝ 2 (psiTerm ν χf A j) (Ioi 0 ×ˢ univ) := by
    intro j
    have hg : ContDiff ℝ 2 (fun p : Chart => ((p.1, xj ν j p.2) : Chart)) := by
      unfold xj
      fun_prop
    refine hprof.comp hg.contDiffOn ?_
    intro p hp
    exact ⟨hp.1, mem_univ _⟩
  have hsum := h1 (psiTerm ν χf A) _ hU hterm (h4 hχ ν hν A hA)
  refine hsum.congr ?_
  intro p hp
  have ha : 0 < ageA ν p.1 := by
    unfold ageA
    have := hp.1
    simp only [mem_Ioi] at this
    positivity
  unfold psiRing
  rw [psipA_eq_phi ν χf A p.1 p.2 ha]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
