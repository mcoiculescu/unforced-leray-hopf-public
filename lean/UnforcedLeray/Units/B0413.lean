import UnforcedLeray.Lib.PhaseSpace.Leibniz
import UnforcedLeray.Units.B0412

/-!
# Unit B0413 (`unlabeled:5750`): the commutator `∂ⱼ A₀ = (A₀ − ½) ∂ⱼ`

Blueprint unit `B0413`, `paper/main.tex` lines 5750–5753 (§`sec:st18-6052`, proof of
Theorem B3), with `A₀ = T₀ − νΔ − ½` (tex 5208, 5161, 3600), `T₀ = ∂_τ − ½ y·∇` (tex 3598,
7318) and the graph `X_{q₀}` of unit B0412 (`background:eq:2.3`, tex 5085–5091):

> For `z_j = ∂_j w`, `∂_j A_0 w = (A_0 − ½) z_j`.

The blueprint statement adds the form used later: `A₀ z_j = ∂_j(A₀ w) + ½ z_j` (tex 5768,
unit B0691) and, for a multi-index `α`, `A₀ D^α w = D^α(A₀ w) + (|α|/2) D^α w` (tex 5820–5824,
unit B0694). All derivatives are distributional (tex 5085–5091).

## Formalization


README.md`; INF25 T25.12, file `Lib/PhaseSpace/Leibniz.lean`, which already proves the single
derivative identity for graph triples as `PhaseSpace.freeGraph_commutator_deriv`) and on the
operators of B0411 (`B0411.L0T`, `B0411.L0`, `B0411.L0D`). Nothing there is redefined.

| Manuscript | Lean |
|---|---|
| `A₀ = T₀ − νΔ − ½` on smooth fields | `B0411.L0 ν` (`L₀` of tex 7319 is the same operator) |
| its transpose `A₀ᵗ = T₀ᵗ − νΔ − ½` on tests | `B0411.L0T ν` |
| `∂ⱼ`, transposed: `Φ ↦ −∂ⱼΦ` | `dy j`, `dyT j` |
| `D_l = ∂_{j₁}⋯∂_{j_k}`, `l = [j₁,…,j_k]`; transposed | `Dl l`, `DT l` (`|α| = l.length`) |
| multi-index `α ∈ ℕ³`, `|α| = α₁+α₂+α₃` | `miList α` (`length_miList`) |
| `z = ∂ⱼ w`, `g = D^α w` in distributions | `HasPhaseOp (dyT j) w z`, `HasPhaseOp (DT l) w g` |
| `A₀ w = h ∈ Y_q` in distributions | `HasPhaseOp (L0T ν) w h` |

A distribution is tested against phase tests `Φ` (`IsPhaseTest`: smooth, `P`-periodic,
bounded spatial support) through `phasePair P q Φ f = ⟪Φ, f⟫`. For `w ∈ Y_q` the distribution
`A₀ w` is `Φ ↦ ⟪A₀ᵗΦ, w⟫`, the distribution `∂ⱼ T` is `Φ ↦ T(−∂ⱼΦ)`, and `D_l T` is
`Φ ↦ T(DT l Φ)`.

### Statements

* Test level (`L0T_dyT`, `L0T_DT`): `A₀ᵗ(−∂ⱼΦ) = −∂ⱼ(A₀ᵗΦ − ½Φ)` and
  `A₀ᵗ(DT l Φ) = DT l (A₀ᵗΦ − (|α|/2)Φ)` for smooth `Φ`; they come from `[∂ⱼ, y·∇] = ∂ⱼ`,
  `[∂ⱼ, Δ] = 0`, `[∂ⱼ, ∂_τ] = 0` (`PhaseSpace.dy_driftT`, `dy_lapT`).
* Smooth fields (`dy_L0`, `Dl_L0`): `∂ⱼ(A₀u) = (A₀ − ½)∂ⱼu`,
  `D_l(A₀u) = (A₀ − |α|/2) D_l u`, classically.
* **Distributions, no regularity of `w` beyond `Y_q`** (`commutator_dist`,
  `commutator_dist_multi`): if `z = ∂ⱼ w ∈ Y_q`, then `∂ⱼ(A₀ w) = (A₀ − ½) z`, i.e.
  `⟪A₀ᵗ(−∂ⱼΦ), w⟫ = ⟪A₀ᵗΦ − ½Φ, z⟫` for every test; for `g = D^α w ∈ Y_q`,
  `D^α(A₀ w) = (A₀ − |α|/2) D^α w`. The rearranged forms `A₀ z = ∂ⱼ(A₀ w) + ½ z` and
  `A₀ D^α w = D^α(A₀ w) + (|α|/2) D^α w` are `commutator_dist'`, `commutator_dist_multi'`.
* **With `Y_q` right-hand sides** (the forms used at tex 5768 and 5820–5824): if `A₀ w = h`,
  `∂ⱼ h = F` (resp. `D^α h = F`) in distributions with `h, F ∈ Y_q`, then `A₀ z = F + ½ z`
  (resp. `A₀ D^α w = F + (|α|/2) D^α w`) in distributions (`hasPhaseOp_L0T_deriv`,
  `hasPhaseOp_L0T_deriv_multi`, `hasPhaseOp_L0T_multiIndex`).
* **Inside the graph** (`hasPhaseOp_L0D_deriv`, `hasPhaseOp_L0D_deriv_multi`, and on
  `X̃_q` of B0412 `Xtilde_commutator`): if `w` and `z = ∂ⱼ w` both lie in `D_(ν,q)`, then
  `∂ⱼ(A₀ w) = A₀ z − ½ z` in distributions, both sides in `Y_q`.
* Bookkeeping for multi-indices: the order of the derivatives is irrelevant
  (`DT_perm`, `hasPhaseOp_DT_perm`), and derivatives compose (`hasPhaseOp_DT_append`).

`w`, `z`, `h`, `F` are arbitrary elements of `Y_q`, for every `P > 0`, `1 ≤ q ≤ ∞` and `ν ∈ ℝ`:
the hypotheses are weaker than the manuscript's (`w ∈ X_{q₀}`, `q₀ = 11/4`, `ν > 0`,
`0 < P ≤ 1`). Only the identity is asserted here; that `z_j` then lies in `X̃_p` (the maximal
distributional domain, tex 5769–5770) belongs to B0691/B0694.

Junk values: none enter. Pairings are continuous linear functionals on `Y_q` evaluated at
genuine phase tests, and all derivatives of tests are Fréchet derivatives of smooth functions.

Status: every asserted fact is proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0413

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ### Spatial derivatives, multi-indices, transposes (tex 5750–5753, 5820–5824) -/

section Defs

/-- The transpose of `∂ⱼ` on phase tests, `Φ ↦ −∂ⱼΦ`: `∂ⱼ w = z` in distributions is
`HasPhaseOp (dyT j) w z`, i.e. `⟪−∂ⱼΦ, w⟫ = ⟪Φ, z⟫` (tex 5750, B0413). It is the operator
`fun Φ => -dy j Φ` of `PhaseSpace.freeGraph_commutator_deriv`. -/
def dyT (j : Fin 3) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := -dy j Φ

/-- The spatial derivative `D_l u = ∂_{j₁}(∂_{j₂}(⋯ ∂_{j_k} u))` of a field, for
`l = [j₁, …, j_k]` (tex 5820–5824, B0413); its order is `|α| = l.length`. -/
def Dl (l : List (Fin 3)) (u : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  l.foldr (fun j v => dy j v) u

/-- The transpose of `D_l` on phase tests: `DT l Φ = (−∂_{j₁})(⋯(−∂_{j_k})Φ)`. `D_l w = g` in
distributions is `HasPhaseOp (DT l) w g` (tex 5820–5824, B0413). The literal transpose of
`∂_{j₁}⋯∂_{j_k}` lists the factors in the opposite order; on smooth tests the two agree
(`DT_perm`). -/
def DT (l : List (Fin 3)) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  l.foldr dyT Φ

/-- A multi-index `α ∈ ℕ³` as the list `[1,…,1, 2,…,2, 3,…,3]` (`αᵢ` copies of `i`), so that
`D^α = D_{miList α}` (tex 5820–5824, B0413). -/
def miList (α : Fin 3 → ℕ) : List (Fin 3) :=
  List.replicate (α 0) 0 ++ List.replicate (α 1) 1 ++ List.replicate (α 2) 2

/-- `|α| = α₁ + α₂ + α₃` is the length of `miList α`. -/
theorem length_miList (α : Fin 3 → ℕ) : (miList α).length = ∑ i, α i := by
  simp only [miList, List.length_append, List.length_replicate, Fin.sum_univ_three]

@[simp] theorem DT_nil (Φ : ℝ × Space → CVec3) : DT [] Φ = Φ := rfl

@[simp] theorem DT_cons (j : Fin 3) (l : List (Fin 3)) (Φ : ℝ × Space → CVec3) :
    DT (j :: l) Φ = dyT j (DT l Φ) := rfl

theorem DT_singleton (j : Fin 3) (Φ : ℝ × Space → CVec3) : DT [j] Φ = -dy j Φ := rfl

theorem DT_singleton' (j : Fin 3) : DT [j] = dyT j := by
  funext Φ
  rfl

theorem DT_append (l l' : List (Fin 3)) (Φ : ℝ × Space → CVec3) :
    DT (l ++ l') Φ = DT l (DT l' Φ) := by
  simp [DT, List.foldr_append]

@[simp] theorem Dl_nil (u : ℝ × Space → CVec3) : Dl [] u = u := rfl

@[simp] theorem Dl_cons (j : Fin 3) (l : List (Fin 3)) (u : ℝ × Space → CVec3) :
    Dl (j :: l) u = dy j (Dl l u) := rfl

end Defs

/-! ### Calculus on smooth functions -/

section Calculus

variable {Φ Ψ F G : ℝ × Space → CVec3}

private theorem diff_of {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) : Differentiable ℝ G :=
  hG.differentiable (by simp)

private theorem contDiff_smul' (c : ℝ) (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (c • G) :=
  hG.const_smul c

theorem dy_sub' (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (j : Fin 3) :
    dy j (F - G) = dy j F - dy j G := by
  funext p
  simp [dy, fderiv_sub (hF p) (hG p)]

theorem contDiff_dyT (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) : ContDiff ℝ ∞ (dyT j Φ) :=
  (contDiff_dy hΦ j).neg

theorem contDiff_DT (hΦ : ContDiff ℝ ∞ Φ) (l : List (Fin 3)) : ContDiff ℝ ∞ (DT l Φ) := by
  induction l with
  | nil => exact hΦ
  | cons j l ih => exact contDiff_dyT ih j

theorem contDiff_Dl (hΦ : ContDiff ℝ ∞ Φ) (l : List (Fin 3)) : ContDiff ℝ ∞ (Dl l Φ) := by
  induction l with
  | nil => exact hΦ
  | cons j l ih => exact contDiff_dy ih j

theorem contDiff_driftT (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (driftT Φ) := by
  have h : driftT Φ = -dτ Φ + (1 / 2 : ℝ) • radialT Φ + (3 / 2 : ℝ) • Φ := by
    funext p
    simp [driftT]
  rw [h]
  exact ((contDiff_dτ hΦ).neg.add (contDiff_smul' _ (contDiff_radialT hΦ))).add
    (contDiff_smul' _ hΦ)

theorem contDiff_L0T (ν : ℝ) (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (L0T ν Φ) := by
  unfold L0T nuLapT
  exact ((contDiff_driftT hΦ).sub (contDiff_smul' ν (contDiff_lapT hΦ))).sub
    (contDiff_smul' _ hΦ)

theorem L0_eq (ν : ℝ) (u : ℝ × Space → CVec3) :
    L0 ν u = dτ u - (1 / 2 : ℝ) • radialT u - ν • lapT u - (1 / 2 : ℝ) • u := by
  funext p
  rfl

theorem contDiff_L0 (ν : ℝ) {u : ℝ × Space → CVec3} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (L0 ν u) := by
  rw [L0_eq]
  exact (((contDiff_dτ hu).sub (contDiff_smul' _ (contDiff_radialT hu))).sub
    (contDiff_smul' ν (contDiff_lapT hu))).sub (contDiff_smul' _ hu)

theorem dyT_sub (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (j : Fin 3) :
    dyT j (F - G) = dyT j F - dyT j G := by
  rw [dyT, dyT, dyT, dy_sub' hF hG]
  abel

theorem dyT_smul (hG : Differentiable ℝ G) (c : ℝ) (j : Fin 3) :
    dyT j (c • G) = c • dyT j G := by
  rw [dyT, dyT, dy_smul hG c j, smul_neg]

theorem DT_sub (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (l : List (Fin 3)) :
    DT l (F - G) = DT l F - DT l G := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [DT_cons, DT_cons, DT_cons, ih,
      dyT_sub (diff_of (contDiff_DT hF l)) (diff_of (contDiff_DT hG l))]

theorem DT_smul (hG : ContDiff ℝ ∞ G) (c : ℝ) (l : List (Fin 3)) :
    DT l (c • G) = c • DT l G := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [DT_cons, DT_cons, ih, dyT_smul (diff_of (contDiff_DT hG l))]

/-- Derivatives of smooth tests commute: `(−∂ₐ)(−∂_b)Ψ = (−∂_b)(−∂ₐ)Ψ`. -/
theorem dyT_comm (hΨ : ContDiff ℝ ∞ Ψ) (a b : Fin 3) : dyT a (dyT b Ψ) = dyT b (dyT a Ψ) := by
  simp only [dyT, dy_neg, neg_neg]
  exact dy_dy_comm hΨ a b

/-- **The order of the derivatives in `D^α` is irrelevant** on smooth tests: `DT l Φ` depends
only on the multiset of `l`, i.e. on the multi-index `α` (tex 5820–5824). -/
theorem DT_perm {l l' : List (Fin 3)} (h : l.Perm l') (hΦ : ContDiff ℝ ∞ Φ) :
    DT l Φ = DT l' Φ := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [DT_cons, DT_cons, ih]
  | swap x y l => rw [DT_cons, DT_cons, DT_cons, DT_cons, dyT_comm (contDiff_DT hΦ l) y x]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Test-level commutator, one derivative** (tex 5750–5753): for a smooth `Φ`,
`A₀ᵗ(−∂ⱼΦ) = −∂ⱼ(A₀ᵗΦ − ½Φ)`, with `A₀ᵗ = T₀ᵗ − νΔ − ½`. It is the transpose of
`∂ⱼ A₀ = (A₀ − ½)∂ⱼ`, from `[∂ⱼ, y·∇] = ∂ⱼ` and `[∂ⱼ, Δ] = [∂ⱼ, ∂_τ] = 0`. -/
theorem L0T_dyT (ν : ℝ) (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    L0T ν (dyT j Φ) = dyT j (L0T ν Φ - (1 / 2 : ℝ) • Φ) := by
  have hdr := contDiff_driftT hΦ
  have hlap := contDiff_lapT hΦ
  have hA : driftT (dy j Φ) = dy j (driftT Φ) - (1 / 2 : ℝ) • dy j Φ := by
    rw [dy_driftT hΦ j]
    abel
  have hB : lapT (dy j Φ) = dy j (lapT Φ) := (dy_lapT hΦ j).symm
  have hR : dy j (L0T ν Φ - (1 / 2 : ℝ) • Φ) =
      dy j (driftT Φ) - ν • dy j (lapT Φ) - (1 / 2 : ℝ) • dy j Φ -
        (1 / 2 : ℝ) • dy j Φ := by
    have h1 : Differentiable ℝ (driftT Φ - ν • lapT Φ) :=
      diff_of (hdr.sub (contDiff_smul' ν hlap))
    have h2 : Differentiable ℝ (driftT Φ - ν • lapT Φ - (1 / 2 : ℝ) • Φ) :=
      diff_of ((hdr.sub (contDiff_smul' ν hlap)).sub (contDiff_smul' _ hΦ))
    simp only [L0T, nuLapT]
    rw [dy_sub' h2 (diff_of (contDiff_smul' _ hΦ)),
      dy_sub' h1 (diff_of (contDiff_smul' _ hΦ)),
      dy_sub' (diff_of hdr) (diff_of (contDiff_smul' ν hlap)),
      dy_smul (diff_of hlap), dy_smul (diff_of hΦ)]
  show L0T ν (dyT j Φ) = -dy j (L0T ν Φ - (1 / 2 : ℝ) • Φ)
  rw [hR]
  simp only [L0T, nuLapT, dyT, driftT_neg, lapT_neg, hA, hB]
  module

/-- **Test-level commutator, multi-index** (tex 5820–5824): for a smooth `Φ` and
`D_l` of order `|α| = l.length`, `A₀ᵗ(DT l Φ) = DT l (A₀ᵗΦ − (|α|/2)Φ)`. -/
theorem L0T_DT (ν : ℝ) (hΦ : ContDiff ℝ ∞ Φ) (l : List (Fin 3)) :
    L0T ν (DT l Φ) = DT l (L0T ν Φ - ((l.length : ℝ) / 2) • Φ) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hX := contDiff_L0T ν hΦ
    rw [DT_cons, DT_cons, L0T_dyT ν (contDiff_DT hΦ l) j, ih,
      DT_sub hX (contDiff_smul' _ hΦ), DT_sub hX (contDiff_smul' _ hΦ), DT_smul hΦ,
      DT_smul hΦ, List.length_cons]
    congr 1
    push_cast
    module

/-- **The commutator for smooth fields, one derivative** (tex 5750–5753):
`∂ⱼ(A₀u) = A₀(∂ⱼu) − ½ ∂ⱼu` for every smooth field `u`. -/
theorem dy_L0 (ν : ℝ) {u : ℝ × Space → CVec3} (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    dy j (L0 ν u) = L0 ν (dy j u) - (1 / 2 : ℝ) • dy j u := by
  have hτ := contDiff_dτ hu
  have hr := contDiff_radialT hu
  have hl := contDiff_lapT hu
  have h1 : Differentiable ℝ (dτ u - (1 / 2 : ℝ) • radialT u) :=
    diff_of (hτ.sub (contDiff_smul' _ hr))
  have h2 : Differentiable ℝ (dτ u - (1 / 2 : ℝ) • radialT u - ν • lapT u) :=
    diff_of ((hτ.sub (contDiff_smul' _ hr)).sub (contDiff_smul' ν hl))
  rw [L0_eq, L0_eq, dy_sub' h2 (diff_of (contDiff_smul' _ hu)),
    dy_sub' h1 (diff_of (contDiff_smul' ν hl)),
    dy_sub' (diff_of hτ) (diff_of (contDiff_smul' _ hr)),
    dy_smul (diff_of hr), dy_smul (diff_of hl), dy_smul (diff_of hu),
    dy_dτ_comm hu, dy_radialT hu, dy_lapT hu]
  module

/-- **The commutator for smooth fields, multi-index** (tex 5820–5824):
`D_l(A₀u) = A₀(D_l u) − (|α|/2) D_l u`, `|α| = l.length`, for every smooth field `u`. -/
theorem Dl_L0 (ν : ℝ) {u : ℝ × Space → CVec3} (hu : ContDiff ℝ ∞ u) (l : List (Fin 3)) :
    Dl l (L0 ν u) = L0 ν (Dl l u) - ((l.length : ℝ) / 2) • Dl l u := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hD := contDiff_Dl hu l
    rw [Dl_cons, Dl_cons, ih, dy_sub' (diff_of (contDiff_L0 ν hD))
      (diff_of (contDiff_smul' _ hD)), dy_smul (diff_of hD), dy_L0 ν hD j, List.length_cons]
    push_cast
    module

end Calculus

/-! ### The distributional commutator (tex 5750–5753, 5764–5770, 5820–5824) -/

section Distributional

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {ν : ℝ}

omit [Fact (0 < P)] in
theorem isPhaseTest_DT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (l : List (Fin 3)) :
    IsPhaseTest P (DT l Φ) := by
  induction l with
  | nil => exact hΦ
  | cons j l ih => exact (ih.dy j).neg

/-- The distributional derivative `D^α w = g` does not depend on the order of the
derivatives in `l`. -/
theorem hasPhaseOp_DT_perm {l l' : List (Fin 3)} (h : l.Perm l') {w g : Yq P q} :
    HasPhaseOp (DT l) w g ↔ HasPhaseOp (DT l') w g := by
  constructor
  · intro H Φ hΦ
    rw [← DT_perm h hΦ.smooth]
    exact H Φ hΦ
  · intro H Φ hΦ
    rw [DT_perm h hΦ.smooth]
    exact H Φ hΦ

/-- Distributional derivatives compose: `D_l w = g` and `D_{l'} g = h` give
`D_{l ++ l'} w = h` (the step `D^{α+eⱼ} = ∂ⱼ D^α` of the induction at tex 5812–5829). -/
theorem hasPhaseOp_DT_append {w g h : Yq P q} {l l' : List (Fin 3)}
    (hg : HasPhaseOp (DT l) w g) (hh : HasPhaseOp (DT l') g h) :
    HasPhaseOp (DT (l ++ l')) w h := by
  intro Φ hΦ
  rw [DT_append, hg _ (isPhaseTest_DT hΦ l'), hh Φ hΦ]

/-- **B0413** (tex 5750–5753), distributional form. Let `w ∈ Y_q` and let `z = ∂ⱼ w ∈ Y_q` in
distributions. Then `∂ⱼ(A₀ w) = (A₀ − ½) z` as distributions: for every phase test `Φ`,
`⟪A₀ᵗ(−∂ⱼΦ), w⟫ = ⟪A₀ᵗΦ − ½Φ, z⟫`. No graph regularity of `w` or `z` is assumed. -/
theorem commutator_dist {w z : Yq P q} (j : Fin 3) (hz : HasPhaseOp (dyT j) w z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q (L0T ν (dyT j Φ)) w = phasePair P q (L0T ν Φ - (1 / 2 : ℝ) • Φ) z := by
  rw [L0T_dyT ν hΦ.smooth j]
  exact hz _ ((isPhaseTest_L0T hΦ ν).sub (hΦ.const_smul _))

/-- **B0413, multi-index** (tex 5820–5824): for `w ∈ Y_q` and `g = D^α w ∈ Y_q` in
distributions (`D^α = D_l`, `|α| = l.length`), `D^α(A₀ w) = (A₀ − |α|/2) D^α w` as
distributions: `⟪A₀ᵗ(DT l Φ), w⟫ = ⟪A₀ᵗΦ − (|α|/2)Φ, g⟫` for every phase test `Φ`. -/
theorem commutator_dist_multi {w g : Yq P q} (l : List (Fin 3)) (hg : HasPhaseOp (DT l) w g)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q (L0T ν (DT l Φ)) w =
      phasePair P q (L0T ν Φ - ((l.length : ℝ) / 2) • Φ) g := by
  rw [L0T_DT ν hΦ.smooth l]
  exact hg _ ((isPhaseTest_L0T hΦ ν).sub (hΦ.const_smul _))

/-- **B0413, multi-index, rearranged** (tex 5820–5824): `A₀ D^α w = D^α(A₀ w) + (|α|/2) D^α w`
as distributions: `⟪A₀ᵗΦ, g⟫ = ⟪A₀ᵗ(DT l Φ), w⟫ + (|α|/2)⟪Φ, g⟫`. -/
theorem commutator_dist_multi' {w g : Yq P q} (l : List (Fin 3)) (hg : HasPhaseOp (DT l) w g)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q (L0T ν Φ) g =
      phasePair P q (L0T ν (DT l Φ)) w + ((l.length : ℂ) / 2) * phasePair P q Φ g := by
  rw [commutator_dist_multi (ν := ν) l hg hΦ,
    phasePair_sub (isPhaseTest_L0T hΦ ν) (hΦ.const_smul _), phasePair_real_smul hΦ]
  push_cast
  ring

/-- **B0413, rearranged** (tex 5750–5753, 5768): `A₀ z = ∂ⱼ(A₀ w) + ½ z` as distributions:
`⟪A₀ᵗΦ, z⟫ = ⟪A₀ᵗ(−∂ⱼΦ), w⟫ + ½⟪Φ, z⟫`. -/
theorem commutator_dist' {w z : Yq P q} (j : Fin 3) (hz : HasPhaseOp (dyT j) w z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q (L0T ν Φ) z =
      phasePair P q (L0T ν (dyT j Φ)) w + (1 / 2 : ℂ) * phasePair P q Φ z := by
  have h := commutator_dist_multi' (ν := ν) [j] hz hΦ
  simpa using h

/-- **B0413 with `Y_q` right-hand sides, multi-index** (the form used at tex 5820–5824): if
`D^α w = g`, `A₀ w = h` and `D^α h = F` in distributions, with `w, g, h, F ∈ Y_q`, then
`A₀ g = F + (|α|/2) g` in distributions. -/
theorem hasPhaseOp_L0T_deriv_multi {w g h F : Yq P q} (l : List (Fin 3))
    (hg : HasPhaseOp (DT l) w g) (hh : HasPhaseOp (L0T ν) w h) (hF : HasPhaseOp (DT l) h F) :
    HasPhaseOp (L0T ν) g (F + ((l.length : ℂ) / 2) • g) := by
  intro Φ hΦ
  rw [commutator_dist_multi' (ν := ν) l hg hΦ, hh _ (isPhaseTest_DT hΦ l), hF Φ hΦ, map_add,
    map_smul, smul_eq_mul]

/-- **B0413 with `Y_q` right-hand sides** (the form used at tex 5764–5770: `A₀ z_j = ∂ⱼ f −
𝔓∂ⱼN + ½ z_j`): if `∂ⱼ w = z`, `A₀ w = h` and `∂ⱼ h = F` in distributions, with
`w, z, h, F ∈ Y_q`, then `A₀ z = F + ½ z` in distributions. -/
theorem hasPhaseOp_L0T_deriv {w z h F : Yq P q} (j : Fin 3)
    (hz : HasPhaseOp (dyT j) w z) (hh : HasPhaseOp (L0T ν) w h) (hF : HasPhaseOp (dyT j) h F) :
    HasPhaseOp (L0T ν) z (F + (1 / 2 : ℂ) • z) := by
  have H := hasPhaseOp_L0T_deriv_multi (ν := ν) [j] hz hh hF
  simpa using H

/-- **B0413 with `Y_q` right-hand sides, for a multi-index `α ∈ ℕ³`** (tex 5820–5824): if
`D^α w = g`, `A₀ w = h` and `D^α h = F` in distributions, then
`A₀ D^α w = F + (|α|/2) D^α w`, `|α| = α₁ + α₂ + α₃`. -/
theorem hasPhaseOp_L0T_multiIndex {w g h F : Yq P q} (α : Fin 3 → ℕ)
    (hg : HasPhaseOp (DT (miList α)) w g) (hh : HasPhaseOp (L0T ν) w h)
    (hF : HasPhaseOp (DT (miList α)) h F) :
    HasPhaseOp (L0T ν) g (F + (((∑ i, α i : ℕ) : ℂ) / 2) • g) := by
  have H := hasPhaseOp_L0T_deriv_multi (ν := ν) (miList α) hg hh hF
  rwa [length_miList] at H

/-- **B0413 inside the graph, multi-index** (tex 5820–5824): if `w, g ∈ D_(ν,q)` and
`D^α w = g` in distributions, then `D^α(A₀ w) = A₀ g − (|α|/2) g` in distributions, both
sides in `Y_q` (`A₀ = L0D`, B0411). -/
theorem hasPhaseOp_L0D_deriv_multi {w g : D P ν q} (l : List (Fin 3))
    (hg : HasPhaseOp (DT l) (w : Yq P q) (g : Yq P q)) :
    HasPhaseOp (DT l) (L0D w) (L0D g - ((l.length : ℂ) / 2) • (g : Yq P q)) := by
  intro Φ hΦ
  rw [← hasPhaseOp_L0D w _ (isPhaseTest_DT hΦ l), commutator_dist_multi (ν := ν) l hg hΦ,
    phasePair_sub (isPhaseTest_L0T hΦ ν) (hΦ.const_smul _), phasePair_real_smul hΦ,
    hasPhaseOp_L0D g Φ hΦ, map_sub, map_smul, smul_eq_mul]
  push_cast
  ring

/-- **B0413 inside the graph** (tex 5750–5753): if `w, z ∈ D_(ν,q)` and `z = ∂ⱼ w` in
distributions, then `∂ⱼ(A₀ w) = (A₀ − ½) z` in distributions, both sides in `Y_q`. -/
theorem hasPhaseOp_L0D_deriv {w z : D P ν q} (j : Fin 3)
    (hz : HasPhaseOp (dyT j) (w : Yq P q) (z : Yq P q)) :
    HasPhaseOp (dyT j) (L0D w) (L0D z - (1 / 2 : ℂ) • (z : Yq P q)) := by
  have H := hasPhaseOp_L0D_deriv_multi [j] hz
  rw [DT_singleton'] at H
  simpa using H

/-- **B0413 on `X̃_q`** (B0412, tex 5085–5091, 5764–5770): for `w, z ∈ X̃_q` with
`z = ∂ⱼ w` in distributions, `∂ⱼ(A₀ w) = (A₀ − ½) z` in distributions. -/
theorem Xtilde_commutator {w z : B0412.Xtilde P ν q} (j : Fin 3)
    (hz : HasPhaseOp (dyT j) (w : Yq P q) (z : Yq P q)) :
    HasPhaseOp (dyT j) (L0D (B0412.XtildeToD w))
      (L0D (B0412.XtildeToD z) - (1 / 2 : ℂ) • (z : Yq P q)) :=
  hasPhaseOp_L0D_deriv (w := B0412.XtildeToD w) (z := B0412.XtildeToD z) j hz

/-- The library's form `PhaseSpace.freeGraph_commutator_deriv` (INF25 T25.12) for a graph
triple `(w, a, b)` agrees with `commutator_dist`: `A₀ w = b − a − ½w` and
`⟪−∂ⱼΦ, A₀ w⟫ = ⟪A₀ᵗΦ − ½Φ, z⟫`. -/
theorem freeGraph_commutator {w a b z : Yq P q} (hw : (w, a, b) ∈ freeGraph P ν q)
    (j : Fin 3) (hz : HasPhaseOp (dyT j) w z) {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) :
    phasePair P q (dyT j Φ) (b - a - (1 / 2 : ℂ) • w) =
      phasePair P q (L0T ν Φ - (1 / 2 : ℝ) • Φ) z := by
  have hL := hasPhaseOp_L0T (mem_freeGraph.1 hw).1 (mem_freeGraph.1 hw).2 (dyT j Φ)
    ((hΦ.dy j).neg)
  rw [← hL]
  exact commutator_dist j hz hΦ

end Distributional

/-! ### The unit, bundled -/

section Bundle

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **B0413** (`unlabeled:5750`, tex 5750–5753; with the multi-index form of tex 5820–5824),
bundled, for every `P > 0`, `1 ≤ q ≤ ∞`, `ν` (in particular `q = q₀ = 11/4`, `ν > 0`,
`P ≤ 1`). `A₀ = T₀ − νΔ − ½` acts through its transpose `L0T ν`.
1. Smooth fields: `∂ⱼ(A₀u) = (A₀ − ½)∂ⱼu` and `D_l(A₀u) = (A₀ − |α|/2)D_l u`.
2. Tests: `A₀ᵗ(−∂ⱼΦ) = −∂ⱼ(A₀ᵗΦ − ½Φ)` and `A₀ᵗ(DT l Φ) = DT l (A₀ᵗΦ − (|α|/2)Φ)`.
3. Distributions, `z = ∂ⱼ w ∈ Y_q`: `∂ⱼ(A₀ w) = (A₀ − ½) z`, i.e. `A₀ z = ∂ⱼ(A₀ w) + ½ z`.
4. Distributions, `g = D^α w ∈ Y_q`: `A₀ D^α w = D^α(A₀ w) + (|α|/2) D^α w`.
5. With `A₀ w = h` and `∂ⱼ h = F` (resp. `D^α h = F`) in `Y_q`: `A₀ z = F + ½ z`
   (resp. `A₀ D^α w = F + (|α|/2) D^α w`).
6. Inside `D_(ν,q)`: `∂ⱼ(A₀ w) = A₀ z − ½ z` and `D^α(A₀ w) = A₀ D^α w − (|α|/2) D^α w`
   in distributions, with both sides in `Y_q`.
7. `D^α` does not depend on the order of the derivatives. -/
theorem B0413_spec (ν : ℝ) :
    (∀ u : ℝ × Space → CVec3, ContDiff ℝ ∞ u → ∀ j : Fin 3,
      dy j (L0 ν u) = L0 ν (dy j u) - (1 / 2 : ℝ) • dy j u) ∧
    (∀ u : ℝ × Space → CVec3, ContDiff ℝ ∞ u → ∀ l : List (Fin 3),
      Dl l (L0 ν u) = L0 ν (Dl l u) - ((l.length : ℝ) / 2) • Dl l u) ∧
    (∀ Φ : ℝ × Space → CVec3, ContDiff ℝ ∞ Φ → ∀ j : Fin 3,
      L0T ν (dyT j Φ) = dyT j (L0T ν Φ - (1 / 2 : ℝ) • Φ)) ∧
    (∀ Φ : ℝ × Space → CVec3, ContDiff ℝ ∞ Φ → ∀ l : List (Fin 3),
      L0T ν (DT l Φ) = DT l (L0T ν Φ - ((l.length : ℝ) / 2) • Φ)) ∧
    (∀ (w z : Yq P q) (j : Fin 3), HasPhaseOp (dyT j) w z →
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
        phasePair P q (L0T ν (dyT j Φ)) w = phasePair P q (L0T ν Φ - (1 / 2 : ℝ) • Φ) z ∧
        phasePair P q (L0T ν Φ) z =
          phasePair P q (L0T ν (dyT j Φ)) w + (1 / 2 : ℂ) * phasePair P q Φ z) ∧
    (∀ (w g : Yq P q) (l : List (Fin 3)), HasPhaseOp (DT l) w g →
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
        phasePair P q (L0T ν Φ) g =
          phasePair P q (L0T ν (DT l Φ)) w + ((l.length : ℂ) / 2) * phasePair P q Φ g) ∧
    (∀ (w z h F : Yq P q) (j : Fin 3), HasPhaseOp (dyT j) w z → HasPhaseOp (L0T ν) w h →
      HasPhaseOp (dyT j) h F → HasPhaseOp (L0T ν) z (F + (1 / 2 : ℂ) • z)) ∧
    (∀ (w g h F : Yq P q) (l : List (Fin 3)), HasPhaseOp (DT l) w g →
      HasPhaseOp (L0T ν) w h → HasPhaseOp (DT l) h F →
        HasPhaseOp (L0T ν) g (F + ((l.length : ℂ) / 2) • g)) ∧
    (∀ (w g h F : Yq P q) (α : Fin 3 → ℕ), HasPhaseOp (DT (miList α)) w g →
      HasPhaseOp (L0T ν) w h → HasPhaseOp (DT (miList α)) h F →
        HasPhaseOp (L0T ν) g (F + (((∑ i, α i : ℕ) : ℂ) / 2) • g)) ∧
    (∀ (w z : D P ν q) (j : Fin 3), HasPhaseOp (dyT j) (w : Yq P q) (z : Yq P q) →
      HasPhaseOp (dyT j) (L0D w) (L0D z - (1 / 2 : ℂ) • (z : Yq P q))) ∧
    (∀ (w g : D P ν q) (l : List (Fin 3)), HasPhaseOp (DT l) (w : Yq P q) (g : Yq P q) →
      HasPhaseOp (DT l) (L0D w) (L0D g - ((l.length : ℂ) / 2) • (g : Yq P q))) ∧
    (∀ (l l' : List (Fin 3)), l.Perm l' → ∀ w g : Yq P q,
      (HasPhaseOp (DT l) w g ↔ HasPhaseOp (DT l') w g)) :=
  ⟨fun _ hu j => dy_L0 ν hu j, fun _ hu l => Dl_L0 ν hu l,
    fun _ hΦ j => L0T_dyT ν hΦ j, fun _ hΦ l => L0T_DT ν hΦ l,
    fun _ _ j hz _ hΦ => ⟨commutator_dist j hz hΦ, commutator_dist' j hz hΦ⟩,
    fun _ _ l hg _ hΦ => commutator_dist_multi' l hg hΦ,
    fun _ _ _ _ j hz hh hF => hasPhaseOp_L0T_deriv j hz hh hF,
    fun _ _ _ _ l hg hh hF => hasPhaseOp_L0T_deriv_multi l hg hh hF,
    fun _ _ _ _ α hg hh hF => hasPhaseOp_L0T_multiIndex α hg hh hF,
    fun _ _ j hz => hasPhaseOp_L0D_deriv j hz,
    fun _ _ l hg => hasPhaseOp_L0D_deriv_multi l hg,
    fun _ _ h _ _ => hasPhaseOp_DT_perm h⟩

end Bundle

end UnforcedLeray.B0413
