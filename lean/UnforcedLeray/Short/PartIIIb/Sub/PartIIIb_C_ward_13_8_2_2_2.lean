import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2

/-!
# `PartIII-b:C/ward/13/8/2/2/2`: decomposition of `UnitAnnularPoincare`

Source `the November 2 reference manuscript`

by convex subsets) is impossible: a convex subset of `{1 <= |y| <= 4}` meets the inner sphere in at
most one point, so finitely many cannot cover a neighbourhood of the sphere. Correct route: six
conical pieces `P(k, s) = {1 <= |y| <= 4, |y| <= 2 s y_k}` (cover, since `max_k |y_k| >= |y|/sqrt 3`),
each the image of a convex set (cone slab `{1<=c<=4, a^2+b^2 <= 3 c^2/4}`) under the bi-Lipschitz
diffeomorphism `y |-> (y_i, y_j, |y|)`, so `PoincOn` transfers from `ConvexPoincare`; then chain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain

/-- The closed unit annulus `{1 <= |y| <= 4}`. -/
def ann : Set UnforcedLeray.Space := {y | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 4}

/-- Poincare inequality on a set `S`. -/
def PoincOn (S : Set UnforcedLeray.Space) : Prop :=
  ∃ C : ℝ, ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ 1 p → ∃ m : ℝ,
    ∫ y in S, (p y - m) ^ 2 ≤ C * ∫ y in S, ‖physGrad p y‖ ^ 2

/-- Conical piece of the annulus, `s = +1` for `true`, `-1` for `false`. -/
def cone (k : Fin 3) (σ : Bool) : Set UnforcedLeray.Space :=
  {y | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 4 ∧ ‖y‖ ≤ 2 * ((if σ then (1:ℝ) else -1) * y k)}

/-- Abstract chaining (source 117-118): finitely many measurable pieces of `ann` with Poincare
inequality, covering `ann`, with connected positive-overlap graph, give Poincare on `ann`.
Route: `|m_i - m_j|^2 vol(K_i cap K_j) <= 2 int_{K_i}(p-m_i)^2 + 2 int_{K_j}(p-m_j)^2`, walk
induction on the graph for `(m_i - m_0)^2 <= A_i * E`, then `(p-m_0)^2 <= 2(p-m_i)^2 + 2(m_i-m_0)^2`. -/
def AbstractChain : Prop :=
  ∀ {ι : Type} [Fintype ι] (K : ι → Set UnforcedLeray.Space),
    (∀ i, MeasurableSet (K i) ∧ K i ⊆ ann ∧ PoincOn (K i)) →
    ann ⊆ ⋃ i, K i →
    (SimpleGraph.fromRel fun i j => 0 < (volume (K i ∩ K j)).toReal).Connected →
    PoincOn ann

/-- Poincare on each conical piece (via the diffeo `y |-> (y_i, y_j, |y|)` onto a convex cone slab
and `ConvexPoincare`; change of variables with Jacobian bounded above and below). -/
def ConePieces : Prop := ∀ (k : Fin 3) (σ : Bool), PoincOn (cone k σ)

/-- Geometry of the six pieces: measurable, inside `ann`, covering `ann`, and the positive-overlap
graph on `Fin 3 × Bool` is connected (pieces with different axes overlap in an open set). -/
def ConeGeometry : Prop :=
  (∀ i : Fin 3 × Bool, MeasurableSet (cone i.1 i.2) ∧ cone i.1 i.2 ⊆ ann) ∧
  ann ⊆ ⋃ i : Fin 3 × Bool, cone i.1 i.2 ∧
  (SimpleGraph.fromRel fun i j : Fin 3 × Bool =>
      0 < (volume (cone i.1 i.2 ∩ cone j.1 j.2)).toReal).Connected

theorem unitAnnularPoincare_of (h1 : AbstractChain) (h2 : ConePieces) (h3 : ConeGeometry) :
    UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.UnitAnnularPoincare :=
  h1 (fun i : Fin 3 × Bool => cone i.1 i.2)
    (fun i => ⟨(h3.1 i).1, (h3.1 i).2, h2 i.1 i.2⟩) h3.2.1 h3.2.2

end UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain
