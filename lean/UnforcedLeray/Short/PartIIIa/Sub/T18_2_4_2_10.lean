import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Lib.TrainB.P0WeakProjection

/-!
# PartIII-a: `P0CommWeakL2` reduced to three packaging lemmas (task `PartIII-a:T18/2/4/2/10`)

Source: `the November 2 reference manuscript`, lines 3442-3465 (`P_0` commutes with
the gradient).

`P0CommWeakL2` follows from the existing `TrainB.hasWeakDeriv_P0_q_of_vecH1`,
`TrainB.hasWeakDeriv_P0_eta_of_vecH1` once an `L²` field with `L²` weak gradient is packaged as an
element of `VecH1 c` (`ExistsVecH1OfWeak`) and the displayed pairing identities are converted to
and from `Sob.HasWeakDeriv` (`SobWeakOfPairing`, `PairingOfSobWeak`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Packaging** (lines 3442-3465): an `L²` field `f` with `L²` weak derivatives `w 0`, `w 1`
(`Sob.HasWeakDeriv` along `(1,0)` and `(0,1)`) is the value of some `x : VecH1 c` whose value,
`q`-derivative and `η`-derivative cell classes are `f`, `w 0`, `w 1`. Sketch: `Sob.W.ofFields`
(`Lib/Sobolev/Space.lean:228`) with `value_ofFields`/`deriv_ofFields`; the integrability clauses of
`HasWeakDeriv` for `L²` classes and the a.e. transfer along `weightedToCellL2Isometry`
(`vecH1_measure_eq_cell`) are the content. -/
def ExistsVecH1OfWeak : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : UnforcedLeray.Cyl.L2v c) (w : Fin 2 → UnforcedLeray.Cyl.L2v c),
    (∀ j : Fin 2, UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c)
      [UnforcedLeray.Sob.cylDir j] (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
      (w j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)) →
    ∃ x : UnforcedLeray.TrainB.VecH1 c,
      UnforcedLeray.TrainB.vecH1ValueCellCLM_MP x = f ∧
      UnforcedLeray.TrainB.vecH1DqCellCLM_MP x = w 0 ∧
      UnforcedLeray.TrainB.vecH1DetaCellCLM_MP x = w 1

/-- **Pairing to `Sob.HasWeakDeriv`** (lines 3442-3465; uses `testBridge` and `Cyl.cellμ_eq`):
the displayed integration-by-parts identities against `B0579.IsCylTest` functions give the weak
derivative in the `Sob` sense (integrability clauses from `L²` on the cell and test regularity). -/
def SobWeakOfPairing : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (f g : UnforcedLeray.Cyl.L2v c),
    (∀ (i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c, (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x) →
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) [UnforcedLeray.Sob.cylDir j]
      (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)

/-- **`Sob.HasWeakDeriv` to pairing** (lines 3442-3465; uses `testBridge`): converse of
`SobWeakOfPairing`, for arbitrary functions `F`, `G`. -/
def PairingOfSobWeak : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (F G : ℝ × ℝ → UnforcedLeray.Cyl.Vec2),
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) [UnforcedLeray.Sob.cylDir j] F G →
    ∀ (i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, F x i * B0579.pd j ψ x = -∫ x in B0579.cell c, G x i * ψ x

theorem p0CommWeakL2_of (h1 : ExistsVecH1OfWeak) (h2 : SobWeakOfPairing)
    (h3 : PairingOfSobWeak) : P0CommWeakL2 := by
  intro c hc f w hw
  have hS : ∀ j : Fin 2, UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c)
      [UnforcedLeray.Sob.cylDir j] (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
      (w j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) :=
    fun j => h2 c j f (w j) (fun i ψ hψ => hw j i ψ hψ)
  obtain ⟨x, hx0, hx1, hx2⟩ := h1 c hc f w hS
  have q := UnforcedLeray.TrainB.hasWeakDeriv_P0_q_of_vecH1 hc x
  have e := UnforcedLeray.TrainB.hasWeakDeriv_P0_eta_of_vecH1 hc x
  rw [hx0, hx1] at q
  rw [hx0, hx2] at e
  intro j i ψ hψ
  fin_cases j
  · exact h3 c 0 _ _ (by simpa [UnforcedLeray.Sob.cylDir] using q) i ψ hψ
  · exact h3 c 1 _ _ (by simpa [UnforcedLeray.Sob.cylDir] using e) i ψ hψ

end UnforcedLeray.Short.IIIa
