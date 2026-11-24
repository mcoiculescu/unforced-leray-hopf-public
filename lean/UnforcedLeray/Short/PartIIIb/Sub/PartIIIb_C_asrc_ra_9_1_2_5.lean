import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks

/-!
# `PartIII-b:C/asrc/ra/9/1/2/5` : `latSmooth` from term smoothness, local Gaussian majorants and the
abstract local `C^n` theorem for `tsum`

Source: `the November 2 reference manuscript` lines 4979-4980 (`h^p_A`, `ψ^p_A`),
4991 ("converge by Gaussian decay"), 5076-5079 (`C⁴` on `s > 0`).

`hpM = Σ_j toMer(hTerm j)`, `psiM = Σ_j pTerm j` with explicit lattice terms; the three source facts
are: each term is `C⁴` on `s > 0` (`LatTermSmooth`), the terms and their derivatives of order `≤ 4`
have a summable majorant on a neighbourhood of every point (`LatTermMajor`, Gaussians in `x_j`), and
a `tsum` of `C^n` terms with such local majorants is `C^n` (`LocalTsumSmooth`, abstract).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th term of `h^p_A` at the chart point `(s, x)` (source 4979-4980). -/
def hTerm (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (p : Chart) : ℝ × ℝ :=
  merApply (Ay ν χf A p.1) (Vj ν p.1 j p.2)
    - fderiv ℝ (Vj ν p.1 j) p.2 (merApply (Ay ν χf A p.1) (xj ν j p.2))

/-- The `j`-th term of `ψ^p_A`. -/
def pTerm (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (p : Chart) : ℝ :=
  merTrace (Ay ν χf A p.1) * psij ν p.1 j p.2
    - fderiv ℝ (psij ν p.1 j) p.2 (merApply (Ay ν χf A p.1) (xj ν j p.2))

/-- `toMer` as a linear equivalence. -/
def toMerLE : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := toMer
  invFun := fun w => (w 0, w 1)
  map_add' := fun v w => by ext i; fin_cases i <;> simp [toMer]
  map_smul' := fun c v => by ext i; fin_cases i <;> simp [toMer]
  left_inv := fun v => by simp [toMer]
  right_inv := fun w => by ext i; fin_cases i <;> simp [toMer]

theorem toMerLE_apply (v : ℝ × ℝ) : toMerLE v = toMer v := rfl

theorem hpM_eq (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    hpM ν χf A = fun p => ∑' j : ℤ, toMer (hTerm ν χf A j p) := by
  funext p
  simp only [hpM, hpA, hTerm]
  exact ContinuousLinearEquiv.map_tsum (f := fun j : ℤ => hTerm ν χf A j p)
    (LinearEquiv.toContinuousLinearEquiv toMerLE)

theorem psiM_eq (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    psiM ν χf A = fun p => ∑' j : ℤ, pTerm ν χf A j p := by
  funext p; rfl

/-- **Abstract local `C^n` theorem for `tsum`** (Mathlib `contDiff_tsum` made local; sketch: near `p`
multiply by a `ContDiffBump` supported in `V ⊆ U` that is `1` near `p`, apply `contDiff_tsum` with
the Leibniz bound `‖iteratedFDeriv k (bump • f j)‖ ≤ C u j`). -/
def LocalTsumSmooth : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (U : Set Chart), IsOpen U → ∀ (f : ℤ → Chart → F) (n : ℕ),
    (∀ j, ContDiffOn ℝ n (f j) U) →
    (∀ p ∈ U, ∃ V ∈ 𝓝 p, V ⊆ U ∧ ∃ u : ℤ → ℝ, Summable u ∧
      ∀ j, ∀ k : ℕ, k ≤ n → ∀ x ∈ V, ‖iteratedFDeriv ℝ k (f j) x‖ ≤ u j) →
    ContDiffOn ℝ n (fun x => ∑' j, f j x) U

/-- Each lattice term is `C⁴` on `s > 0` (`Ay` is `C⁶` there, `Vj`, `ψ_j` are smooth in `(s,x)`
for `s > -1/ν`; the `fderiv` in `x` of a `C⁵` function is `C⁴`). -/
def LatTermSmooth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ j : ℤ,
    ContDiffOn ℝ 4 (fun p => toMer (hTerm ν χf A j p)) (Ioi 0 ×ˢ univ) ∧
    ContDiffOn ℝ 4 (pTerm ν χf A j) (Ioi 0 ×ˢ univ)

/-- **Local Gaussian majorants** (source 4991, 5076-5079): near every `p` with `s > 0` there is a
neighbourhood `V ⊆ {s > 0}` and a summable `u : ℤ → ℝ` bounding all derivatives of order `≤ 4` of the
`j`-th terms (polynomial times `exp(-|x_j|²/(4a))`, `a = 1+νs` bounded away from `0`, `x_j = x - jc`). -/
def LatTermMajor (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ p ∈ (Ioi 0 ×ˢ univ : Set Chart), ∃ V ∈ 𝓝 p, V ⊆ Ioi 0 ×ˢ univ ∧ ∃ u : ℤ → ℝ, Summable u ∧
      ∀ j : ℤ, ∀ k : ℕ, k ≤ 4 → ∀ x ∈ V,
        ‖iteratedFDeriv ℝ k (fun q => toMer (hTerm ν χf A j q)) x‖ ≤ u j ∧
        ‖iteratedFDeriv ℝ k (pTerm ν χf A j) x‖ ≤ u j

theorem latSmooth_of (as : ℝ) (χf : ℝ → ℝ) (h0 : LocalTsumSmooth) (h1 : LatTermSmooth as χf)
    (h2 : LatTermMajor as χf) : LatSmooth as χf := by
  intro hχ ν hν A hA
  have hU : IsOpen (Ioi 0 ×ˢ univ : Set Chart) := isOpen_Ioi.prod isOpen_univ
  have hs := h1 hχ ν hν A hA
  have hm := h2 hχ ν hν A hA
  refine ⟨?_, ?_⟩
  · rw [hpM_eq]
    refine h0 Merid _ hU (fun j p => toMer (hTerm ν χf A j p)) 4 (fun j => (hs j).1) ?_
    intro p hp
    obtain ⟨V, hV, hVU, u, hu, hb⟩ := hm p hp
    exact ⟨V, hV, hVU, u, hu, fun j k hk x hx => (hb j k hk x hx).1⟩
  · rw [psiM_eq]
    refine h0 ℝ _ hU (pTerm ν χf A) 4 (fun j => (hs j).2) ?_
    intro p hp
    obtain ⟨V, hV, hVU, u, hu, hb⟩ := hm p hp
    exact ⟨V, hV, hVU, u, hu, fun j k hk x hx => (hb j k hk x hx).2⟩

end UnforcedLeray.Short.PartIIIb.Concrete
