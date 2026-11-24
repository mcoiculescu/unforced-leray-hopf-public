import UnforcedLeray.Lib.PhaseSpace.Test
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Unit B0412, helper: the action of `𝒪` on the phase space `Y_q` and the class (2.2)

Blueprint unit `B0412` (`background:eq:2.3`, `paper/main.tex` lines 5085–5091) restricts the
correction graph to the class (2.2) (`background:eq:2.2`, tex 5081–5084, blueprint unit
B0416):
`g · U(τ) = U(τ)` for every `g ∈ 𝒪`,
where (tex 112–115) `𝒪` is the group of orthogonal maps of `ℝ³` fixing `e₃`, acting on fields by
`(g · u)(y) = g u(g⁻¹ y)`. B0416 has no draft, so the action and the class are built here.

* `𝒪` is `{g : Space ≃ₗᵢ[ℝ] Space // FixesAxis g}` with `FixesAxis` from the audited
  `lean/UnforcedLeray/Statement.lean` (the reflections in planes through the axis are included).
* The phase space is complex (decision D2, `Lib/PhaseSpace/Test.lean`), so `g` acts on `ℂ³` by
  its complexification `gC g`, the real matrix `gᵢⱼ = (g eⱼ)ᵢ` applied componentwise
  (`gC_apply`); on real vectors it is `g` itself (`gC_realC`).
* `spatialAct q g : L^q(ℝ³; ℂ³) → L^q(ℝ³; ℂ³)` is `u ↦ g u(g⁻¹ ·)` (`coeFn_spatialAct`), and
  `act P q g : Y_q → Y_q` applies it at every phase (`coeFn_act`).
* `IsOInvariant w` is `g · w = w` in `Y_q` for every `g ∈ 𝒪`; `isOInvariant_iff` unfolds it to
  the manuscript's form: for every `g ∈ 𝒪`, for a.e. phase `τ`, `g w(τ)(g⁻¹ y) = w(τ)(y)` for
  a.e. `y`. (Elements of `Y_q` are classes, so "every `τ`" is "a.e. `τ`".)
* `Osym P q` is the subspace of `𝒪`-invariant elements; it is closed (`isClosed_Osym`).

Junk values: none. Every map here is a genuine continuous linear map; no integral, inverse or
division is involved.

Status: every declaration is proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0412

open UnforcedLeray.PhaseSpace

/-! ### The complexified matrix of `g ∈ O(3)` -/

/-- The matrix entry `gᵢⱼ = (g eⱼ)ᵢ` of a linear isometry `g` of `ℝ³`. -/
def gEntry (g : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) : ℝ := g (EuclideanSpace.single j 1) i

/-- The complexification of `g`: the real matrix `(gᵢⱼ)` acting on `ℂ³`. This is how `g ∈ 𝒪`
acts on the values of the complex fields of `Y_q` (tex 113, `(g·u)(x) = g u(g⁻¹x)`). -/
def gC (g : Space ≃ₗᵢ[ℝ] Space) : CVec3 →L[ℂ] CVec3 :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).smulRight
    (∑ i : Fin 3, ((gEntry g i j : ℝ) : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3))

/-- `(gC g v)ᵢ = ∑ⱼ gᵢⱼ vⱼ`. -/
theorem gC_apply (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) (i : Fin 3) :
    gC g v i = ∑ j : Fin 3, ((gEntry g i j : ℝ) : ℂ) * v j := by
  simp [gC, Pi.single_apply, mul_comm]

/-- A real vector of `ℝ³` seen in `ℂ³`. -/
def realC (x : Space) : CVec3 :=
  ∑ i : Fin 3, ((x i : ℝ) : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3)

theorem realC_apply (x : Space) (i : Fin 3) : realC x i = ((x i : ℝ) : ℂ) := by
  simp [realC, Pi.single_apply]

/-- On real vectors the complexification is `g` itself: `gC g x = g x`. -/
theorem gC_realC (g : Space ≃ₗᵢ[ℝ] Space) (x : Space) : gC g (realC x) = realC (g x) := by
  have hx : x = ∑ j : Fin 3, x j • (EuclideanSpace.single j (1 : ℝ) : Space) := by
    ext k
    simp [Pi.single_apply]
  ext i
  rw [gC_apply, realC_apply]
  conv_rhs => rw [hx]
  simp [realC_apply, gEntry, map_sum, map_smul, mul_comm]

/-! ### The action on `L^q(ℝ³; ℂ³)` and on `Y_q` -/

section Action

variable (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- The action `u ↦ g · u = g u(g⁻¹ ·)` of `g` on `L^q(ℝ³; ℂ³)` (tex 113). -/
def spatialAct (g : Space ≃ₗᵢ[ℝ] Space) :
    Lp CVec3 q (volume : Measure Space) →L[ℂ] Lp CVec3 q (volume : Measure Space) :=
  ((gC g).compLpL q (volume : Measure Space)).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (⇑g.symm) g.symm.measurePreserving).toContinuousLinearMap

variable {q}

/-- `(g · u)(y) = g u(g⁻¹ y)` for a.e. `y`. -/
theorem coeFn_spatialAct (g : Space ≃ₗᵢ[ℝ] Space) (u : Lp CVec3 q (volume : Measure Space)) :
    spatialAct q g u =ᵐ[volume] fun y => gC g (u (g.symm y)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := (volume : Measure Space)) (gC g)
    (Lp.compMeasurePreserving (⇑g.symm) g.symm.measurePreserving u)
  have h2 := Lp.coeFn_compMeasurePreserving u g.symm.measurePreserving
  filter_upwards [h1, h2] with y hy1 hy2
  exact hy1.trans (congrArg (gC g) hy2)

end Action

section ActionY

variable (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- The action of `g` on `Y_q`, phase by phase: `(g · w)(τ) = g · w(τ)`. -/
def act (g : Space ≃ₗᵢ[ℝ] Space) : Yq P q →L[ℂ] Yq P q :=
  (spatialAct q g).compLpL q (AddCircle.haarAddCircle (T := P))

variable {P q}

/-- `(g · w)(τ) = g · w(τ)` for a.e. phase `τ`. -/
theorem coeFn_act (g : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    act P q g w =ᵐ[AddCircle.haarAddCircle] fun τ => spatialAct q g (w τ) :=
  ContinuousLinearMap.coeFn_compLpL _ _

end ActionY

/-! ### The class (2.2): `𝒪`-invariant elements of `Y_q` -/

section Invariant

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **The class (2.2)** (`background:eq:2.2`, tex 5081–5084; `𝒪` as in tex 112–115):
`g · w = w` in `Y_q` for every `g ∈ 𝒪`, i.e. every linear isometry of `ℝ³` fixing `e₃`. -/
def IsOInvariant (w : Yq P q) : Prop :=
  ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → act P q g w = w

/-- `g · w = w` in `L^q(ℝ³)` means `g u(g⁻¹ y) = u(y)` for a.e. `y`. -/
theorem spatialAct_eq_iff (g : Space ≃ₗᵢ[ℝ] Space) (u : Lp CVec3 q (volume : Measure Space)) :
    spatialAct q g u = u ↔ ∀ᵐ y ∂(volume : Measure Space), gC g (u (g.symm y)) = u y := by
  constructor
  · intro h
    filter_upwards [coeFn_spatialAct g u] with y hy
    rw [← hy, h]
  · intro h
    apply Lp.ext
    filter_upwards [coeFn_spatialAct g u, h] with y hy1 hy2
    rw [hy1, hy2]

/-- **The class (2.2), unfolded** (tex 5083, with the action of tex 113): `w` is
`𝒪`-invariant iff for every `g ∈ 𝒪`, for a.e. phase `τ`, `g w(τ)(g⁻¹ y) = w(τ)(y)` for a.e.
`y ∈ ℝ³`. -/
theorem isOInvariant_iff (w : Yq P q) :
    IsOInvariant w ↔ ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        ∀ᵐ y ∂(volume : Measure Space), gC g (w τ (g.symm y)) = w τ y := by
  refine forall_congr' fun g => forall_congr' fun _ => ?_
  constructor
  · intro h
    filter_upwards [coeFn_act g w] with τ hτ
    rw [← spatialAct_eq_iff, ← hτ, h]
  · intro h
    apply Lp.ext
    filter_upwards [coeFn_act g w, h] with τ hτ1 hτ2
    rw [hτ1, (spatialAct_eq_iff g (w τ)).2 hτ2]

variable (P q) in
/-- The subspace of `𝒪`-invariant elements of `Y_q` (the class (2.2)). -/
def Osym : Submodule ℂ (Yq P q) where
  carrier := {w | IsOInvariant w}
  add_mem' := by
    intro a b ha hb g hg
    change act P q g (a + b) = a + b
    rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := by
    intro c w hw g hg
    change act P q g (c • w) = c • w
    rw [map_smul, hw g hg]

theorem mem_Osym {w : Yq P q} : w ∈ Osym P q ↔ IsOInvariant w := Iff.rfl

/-- The class (2.2) is a closed subspace of `Y_q`. -/
theorem isClosed_Osym : IsClosed (Osym P q : Set (Yq P q)) := by
  have h : (Osym P q : Set (Yq P q)) =
      ⋂ g : Space ≃ₗᵢ[ℝ] Space, ⋂ (_ : FixesAxis g), {w | act P q g w = w} := by
    ext w
    simp only [SetLike.mem_coe, mem_Osym, IsOInvariant, mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun g => isClosed_iInter fun _ =>
    isClosed_eq (act P q g).continuous continuous_id

end Invariant

end UnforcedLeray.B0412
