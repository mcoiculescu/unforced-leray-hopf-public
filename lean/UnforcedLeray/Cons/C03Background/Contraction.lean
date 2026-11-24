import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Theorem B3: the nonlinear closure `background:eq:2.43` and the symmetric class

`paper/main.tex`, lines 5693–5730 (Section `sec:st18-6544`); blueprint units B0685
(`background:eq:2.43`, the contraction) and the symmetry remark of lines 5725–5727
("iteration from zero therefore stays in the real class (2.2)", B0686 in the ledger of
B0705). This file is pure functional analysis: no Navier–Stokes object enters.

**Manuscript.** "Apply (2.31) with terminal value zero to the negative of the raw residual and
the quadratic terms in (2.42). With `δ = Pε^{3/11}`, `M = Pe^{m/ν}`, contraction on the ball
of radius `2Mδ` follows from `4PM²δ < 1`" (lines 5714–5721).

**Lean form.** `Z` is the state space (`X_{q₀} × ℝ²` with `‖(w,A)‖ = ‖w‖_X + |A|`, line 5698),
`Y` the body source space `Y_{q₀}`; `inv : Y →L Z` is the augmented inverse (2.31) at terminal
value `β = 0`, with `‖inv‖ ≤ M`; `quad : Z →L Z →L Y` is the quadratic source of (2.42)
(polarized, "the polarized difference estimates have the same polynomial constant",
line 5713), with `‖quad‖ ≤ P`; `F` is the projected raw residual `𝔓F_R` of (2.15), with
`‖F‖ ≤ δ`. The closure map is `Φ(z) = inv(-(F + quad z z))` (`closureMap`).

* `exists_fixedPoint_closureMap`: if `4PM²δ < 1`, then `Φ` has a fixed point in the closed
  ball of radius `2Mδ` (the reference form of (2.4)–(2.6)), unique in that ball; and if `Φ`
  maps `S ∩ ball` into a closed set `S ∋ 0` (the symmetric class (2.2)), the fixed point lies
  in `S` (lines 5725–5727). The proof is the manuscript's: `‖Φz‖ ≤ M(δ + P(2Mδ)²)
  = Mδ(1 + 4PM²δ) ≤ 2Mδ` and `‖Φx - Φy‖ ≤ MP(‖x‖ + ‖y‖)‖x - y‖ ≤ 4PM²δ‖x - y‖`.

The compiled criterion `QuadraticContraction.existsUnique_fixedPoint`
(`lean/UnforcedLeray/Analysis/QuadraticContraction.lean`) needs `2ρ‖B‖ + ‖L‖ + ‖G‖/ρ < 1`,
which at `ρ = 2Mδ` is `4PM²δ < 1/2`; the direct proof here gives the manuscript's exact
condition `4PM²δ < 1`. The Banach fixed point step follows that file's use of
`ContractingWith.exists_fixedPoint'`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.Cons.C03

variable {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The closure map of `background:eq:2.43` (lines 5714–5716): the augmented inverse (2.31),
at terminal value zero, applied to the negative raw residual and the quadratic terms,
`Φ(z) = 𝒜⁻¹(-(𝔓F_R + 𝒬(z,z)), 0)`. -/
def closureMap (inv : Y →L[ℝ] Z) (quad : Z →L[ℝ] Z →L[ℝ] Y) (F : Y) (z : Z) : Z :=
  inv (-(F + quad z z))

/-- `‖Φz‖ ≤ ‖inv‖(‖F‖ + ‖quad‖ρ²)` on the ball of radius `ρ`. -/
theorem norm_closureMap_le (inv : Y →L[ℝ] Z) (quad : Z →L[ℝ] Z →L[ℝ] Y) (F : Y) {ρ : ℝ}
    {z : Z} (hz : ‖z‖ ≤ ρ) :
    ‖closureMap inv quad F z‖ ≤ ‖inv‖ * (‖F‖ + ‖quad‖ * ρ ^ 2) := by
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hq : ‖quad z z‖ ≤ ‖quad‖ * ρ ^ 2 := by
    calc ‖quad z z‖ ≤ ‖quad‖ * ‖z‖ * ‖z‖ := quad.le_opNorm₂ z z
      _ ≤ ‖quad‖ * ρ * ρ := by gcongr
      _ = ‖quad‖ * ρ ^ 2 := by ring
  calc ‖closureMap inv quad F z‖ ≤ ‖inv‖ * ‖-(F + quad z z)‖ := inv.le_opNorm _
    _ ≤ ‖inv‖ * (‖F‖ + ‖quad‖ * ρ ^ 2) := by
      rw [norm_neg]
      gcongr
      exact (norm_add_le _ _).trans (add_le_add le_rfl hq)

/-- `Φx - Φy = -inv(quad(x - y) x + quad y (x - y))`. -/
theorem closureMap_sub (inv : Y →L[ℝ] Z) (quad : Z →L[ℝ] Z →L[ℝ] Y) (F : Y) (x y : Z) :
    closureMap inv quad F x - closureMap inv quad F y =
      -inv (quad (x - y) x + quad y (x - y)) := by
  simp only [closureMap, map_sub, sub_apply, map_neg, map_add]
  abel

/-- The polarized difference bound `‖Φx - Φy‖ ≤ ‖inv‖‖quad‖(‖x‖ + ‖y‖)‖x - y‖`. -/
theorem norm_closureMap_sub_le (inv : Y →L[ℝ] Z) (quad : Z →L[ℝ] Z →L[ℝ] Y) (F : Y)
    (x y : Z) :
    ‖closureMap inv quad F x - closureMap inv quad F y‖ ≤
      ‖inv‖ * ‖quad‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  rw [closureMap_sub, norm_neg]
  have h1 : ‖quad (x - y) x‖ ≤ ‖quad‖ * ‖x - y‖ * ‖x‖ := quad.le_opNorm₂ _ _
  have h2 : ‖quad y (x - y)‖ ≤ ‖quad‖ * ‖y‖ * ‖x - y‖ := quad.le_opNorm₂ _ _
  calc ‖inv (quad (x - y) x + quad y (x - y))‖
      ≤ ‖inv‖ * ‖quad (x - y) x + quad y (x - y)‖ := inv.le_opNorm _
    _ ≤ ‖inv‖ * (‖quad‖ * ‖x - y‖ * ‖x‖ + ‖quad‖ * ‖y‖ * ‖x - y‖) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = ‖inv‖ * ‖quad‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

/-- **The nonlinear closure `background:eq:2.43`** (lines 5714–5727, unit B0685, with the
symmetry remark of lines 5725–5727). If `‖inv‖ ≤ M` ((2.31) at `β = 0`), `‖quad‖ ≤ P`
((2.42)), `‖F‖ ≤ δ` ((2.15)) and `4PM²δ < 1`, then the closure map has a fixed point `z`
with `‖z‖ ≤ 2Mδ`, the only fixed point in that ball. If moreover `Φ` maps the part of a
closed set `S ∋ 0` (the real symmetric class (2.2)) inside the ball into `S`, the fixed point
lies in `S` ("iteration from zero therefore stays in the real class"). -/
theorem exists_fixedPoint_closureMap [CompleteSpace Z] (inv : Y →L[ℝ] Z)
    (quad : Z →L[ℝ] Z →L[ℝ] Y) (F : Y) {M P δ : ℝ} (hM : ‖inv‖ ≤ M) (hP : ‖quad‖ ≤ P)
    (hF : ‖F‖ ≤ δ) (hsmall : 4 * P * M ^ 2 * δ < 1) {S : Set Z} (hS : IsClosed S)
    (h0 : (0 : Z) ∈ S)
    (hinv : ∀ z ∈ S, ‖z‖ ≤ 2 * M * δ → closureMap inv quad F z ∈ S) :
    ∃ z ∈ S, ‖z‖ ≤ 2 * M * δ ∧ closureMap inv quad F z = z ∧
      ∀ z' : Z, ‖z'‖ ≤ 2 * M * δ → closureMap inv quad F z' = z' → z' = z := by
  have hM0 : 0 ≤ M := (inv.opNorm_nonneg).trans hM
  have hP0 : 0 ≤ P := (quad.opNorm_nonneg).trans hP
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hF
  set ρ : ℝ := 2 * M * δ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set Φ := closureMap inv quad F with hΦ
  set K : ℝ := 4 * P * M ^ 2 * δ with hK
  have hK0 : 0 ≤ K := by positivity
  -- the self-map bound `‖Φz‖ ≤ Mδ(1 + 4PM²δ) ≤ 2Mδ`
  have hball : ∀ z : Z, ‖z‖ ≤ ρ → ‖Φ z‖ ≤ ρ := by
    intro z hz
    have h1 := norm_closureMap_le inv quad F hz
    have h2 : ‖inv‖ * (‖F‖ + ‖quad‖ * ρ ^ 2) ≤ M * (δ + P * ρ ^ 2) := by
      gcongr
    have h3 : M * (δ + P * ρ ^ 2) = M * δ * (1 + K) := by
      rw [hρ, hK]; ring
    have h4 : M * δ * (1 + K) ≤ M * δ * 2 := by
      have : 0 ≤ M * δ := mul_nonneg hM0 hδ0
      nlinarith
    calc ‖Φ z‖ ≤ ‖inv‖ * (‖F‖ + ‖quad‖ * ρ ^ 2) := h1
      _ ≤ M * (δ + P * ρ ^ 2) := h2
      _ = M * δ * (1 + K) := h3
      _ ≤ M * δ * 2 := h4
      _ = ρ := by rw [hρ]; ring
  -- the Lipschitz bound `‖Φx - Φy‖ ≤ 4PM²δ‖x - y‖` on the ball
  have hlip : ∀ x y : Z, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ → ‖Φ x - Φ y‖ ≤ K * ‖x - y‖ := by
    intro x y hx hy
    have h1 := norm_closureMap_sub_le inv quad F x y
    have h2 : ‖inv‖ * ‖quad‖ * (‖x‖ + ‖y‖) * ‖x - y‖ ≤ M * P * (ρ + ρ) * ‖x - y‖ := by
      gcongr
    calc ‖Φ x - Φ y‖ ≤ ‖inv‖ * ‖quad‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := h1
      _ ≤ M * P * (ρ + ρ) * ‖x - y‖ := h2
      _ = K * ‖x - y‖ := by rw [hρ, hK]; ring
  -- Banach's fixed point theorem on `S ∩ closedBall 0 ρ`
  set T : Set Z := S ∩ closedBall 0 ρ with hT
  have hTc : IsComplete T := (hS.inter isClosed_closedBall).isComplete
  have hmaps : MapsTo Φ T T := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz.2
    exact ⟨hinv z hz.1 hz', mem_closedBall_zero_iff.mpr (hball z hz')⟩
  let Kn : NNReal := ⟨K, hK0⟩
  have hcontr : ContractingWith Kn (hmaps.restrict Φ T T) := by
    constructor
    · show K < 1
      exact hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (Φ x.val) (Φ y.val) ≤ K * dist x.val y.val
      simp only [dist_eq_norm]
      exact hlip _ _ (mem_closedBall_zero_iff.mp x.property.2)
        (mem_closedBall_zero_iff.mp y.property.2)
  have h0T : (0 : Z) ∈ T := ⟨h0, mem_closedBall_self hρ0⟩
  obtain ⟨z, hzT, hfix, -, -⟩ :=
    ContractingWith.exists_fixedPoint' hTc hmaps hcontr h0T (edist_ne_top _ _)
  have hzρ : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hzT.2
  refine ⟨z, hzT.1, hzρ, hfix, ?_⟩
  -- uniqueness in the ball
  intro z' hz' hfix'
  have hd := hlip z' z hz' hzρ
  rw [hfix', hfix] at hd
  have hnorm : ‖z' - z‖ = 0 := by
    have hn := norm_nonneg (z' - z)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end UnforcedLeray.Cons.C03
