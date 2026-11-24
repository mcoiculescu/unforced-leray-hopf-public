import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`: `JetNormOfPartials`, decomposition

Source of record: `the November 2 reference manuscript`, lines 3060-3073 (the
adjoint is smooth with bounded jets near the end age; the jet norm is controlled by mixed partials).

Pure calculus, no PDE. With `C = 2 ^ n`: expand each of the `n` arguments of `D^n F(p)` in the basis
`stDir` (`BasisExpansion`); the value on a word `i : Fin n → Fin 3` of basis directions equals the mixed
partial `∂^w ∂_r^j φ'` with `j = ageCount i`, `w = spatWord i` (`IterSymm` to sort the arguments by a
permutation `SortPerm`, `SortedIdent` to identify the sorted word); the map `i ↦ (j, w)` is at most
`2 ^ n`-to-one (`CountWords`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The sorted argument vector of length `n`: first the spatial directions `stDir (k + 1)` of the
letters of `w` in order, then `stDir 0` (the age direction) for the remaining positions. -/
def sortedVec (w : List (Fin 2)) (n : ℕ) : Fin n → ℝ × (ℝ × ℝ) :=
  fun k => if h : k.1 < w.length then stDir (w.get ⟨k.1, h⟩).succ else stDir 0

/-- The number of age letters (`0`) in a word of basis directions. -/
def ageCount {n : ℕ} (i : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter fun k => i k = 0).card

/-- The spatial word of a word of basis directions: the letters `a ≠ 0`, replaced by `a - 1 : Fin 2`,
in order. -/
def spatWord {n : ℕ} (i : Fin n → Fin 3) : List (Fin 2) :=
  (List.ofFn i).filterMap (fun a => if h : a = 0 then none else some (a.pred h))

/-- **Basis expansion** (multilinearity): `‖M‖ ≤ Σ_{i : Fin n → Fin 3} ‖M (stDir ∘ i)‖`. (Each argument
`v = v.1 • stDir 0 + v.2.1 • stDir 1 + v.2.2 • stDir 2` with coordinates `≤ ‖v‖` in the sup norm;
`ContinuousMultilinearMap.map_sum`/`Finset.prod_univ_sum`, then `opNorm_le_bound`.) -/
def BasisExpansion : Prop :=
  ∀ (n : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (ℝ × ℝ)) ℂ),
    ‖M‖ ≤ ∑ i : Fin n → Fin 3, ‖M (fun k => stDir (i k))‖

/-- **Symmetry of the iterated derivative** of a `C^∞` function on an open set (non-analytic):
`D^n F(p) (v ∘ σ) = D^n F(p) v` for every permutation `σ`. (Bump function equal to `1` near `p`
and `UnforcedLeray.B0121.iterDirDeriv_perm`, or adjacent transpositions with
`ContDiffAt.isSymmSndFDerivAt`.) -/
def IterSymm : Prop :=
  ∀ (n : ℕ) (φ' : ℝ → ℝ × ℝ → ℂ) (U : Set (ℝ × (ℝ × ℝ))), IsOpen U →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) U → ∀ p ∈ U,
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → ℝ × (ℝ × ℝ)),
      iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p (fun k => v (σ k)) =
        iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p v

/-- **Sorted word = mixed partial**: `D^n F(p)` on the sorted vector (spatial directions of `w`, then
`j` copies of `stDir 0`) is `stPartial φ' j w p.1 p.2` (induction on `w`:
`iteratedFDeriv_succ_apply_left`, `pdCx k f y = fderiv ℝ f y (B0579.dir k)`, `stDir (k + 1) = (0, dir k)`;
induction on `j` for the age slice: `iteratedDeriv_eq_iteratedFDeriv`,
`ContinuousLinearMap.iteratedFDeriv_comp_right` along `r' ↦ (r', y)`). -/
def SortedIdent : Prop :=
  ∀ (φ' : ℝ → ℝ × ℝ → ℂ) (U : Set (ℝ × (ℝ × ℝ))), IsOpen U →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) U → ∀ p ∈ U,
    ∀ (j : ℕ) (w : List (Fin 2)) (n : ℕ), w.length + j = n →
      iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p (sortedVec w n) =
        stPartial φ' j w p.1 p.2

/-- **Sorting permutation** (finite combinatorics): the lengths add up, and some permutation of the
positions sorts `stDir ∘ i` into `sortedVec (spatWord i) n`. -/
def SortPerm : Prop :=
  ∀ (n : ℕ) (i : Fin n → Fin 3),
    (spatWord i).length + ageCount i = n ∧
      ∃ σ : Equiv.Perm (Fin n), ∀ k, stDir (i (σ k)) = sortedVec (spatWord i) n k

/-- **Counting** (finite combinatorics): `i ↦ (ageCount i, spatWord i)` takes each value
`(j, ofFn v)`, `v : Fin (n - j) → Fin 2`, at most `C(n, j) ≤ 2 ^ n` times (the fibre injects into the
set of positions of age letters). -/
def CountWords : Prop :=
  ∀ (n : ℕ) (f : ℕ → List (Fin 2) → ℝ), (∀ j w, 0 ≤ f j w) →
    ∑ i : Fin n → Fin 3, f (ageCount i) (spatWord i) ≤
      2 ^ n * ∑ j ∈ Finset.range (n + 1), ∑ v : Fin (n - j) → Fin 2, f j (List.ofFn v)

/-- Value of `D^n F(p)` on a word of basis directions. -/
theorem wordValue_of (h2 : IterSymm) (h3 : SortedIdent) (h4 : SortPerm)
    (φ' : ℝ → ℝ × ℝ → ℂ) (U : Set (ℝ × (ℝ × ℝ))) (hU : IsOpen U)
    (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) U) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ U)
    (n : ℕ) (i : Fin n → Fin 3) :
    iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p (fun k => stDir (i k)) =
      stPartial φ' (ageCount i) (spatWord i) p.1 p.2 := by
  obtain ⟨hlen, σ, hσ⟩ := h4 n i
  have hv : (fun k => stDir (i (σ k))) = sortedVec (spatWord i) n := funext hσ
  rw [← h2 n φ' U hU hsm p hp σ (fun k => stDir (i k)), hv]
  exact h3 φ' U hU hsm p hp (ageCount i) (spatWord i) n hlen

theorem jetNormOfPartials_of (h1 : BasisExpansion) (h2 : IterSymm) (h3 : SortedIdent)
    (h4 : SortPerm) (h5 : CountWords) : JetNormOfPartials := by
  intro n
  refine ⟨2 ^ n, fun φ' U hU hsm p hp => ?_⟩
  calc ‖iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p‖
      ≤ ∑ i : Fin n → Fin 3,
          ‖iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p (fun k => stDir (i k))‖ :=
        h1 n _
    _ = ∑ i : Fin n → Fin 3, ‖stPartial φ' (ageCount i) (spatWord i) p.1 p.2‖ :=
        Finset.sum_congr rfl fun i _ => by rw [wordValue_of h2 h3 h4 φ' U hU hsm p hp n i]
    _ ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∑ v : Fin (n - j) → Fin 2,
          ‖stPartial φ' j (List.ofFn v) p.1 p.2‖ :=
        h5 n (fun j w => ‖stPartial φ' j w p.1 p.2‖) (fun _ _ => norm_nonneg _)

end UnforcedLeray.Short.IIIa
