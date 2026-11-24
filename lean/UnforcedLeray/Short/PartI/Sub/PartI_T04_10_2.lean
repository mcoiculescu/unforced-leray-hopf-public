import UnforcedLeray.Short.PartI.Sub.PartI_T04_10

/-!
# Part I, `PartI:T04/10/2`: `APLevel3Static`, reduced to the two slice-level terms

Source of record: `the November 2 reference manuscript`, lines 285-288
(`[∂², v·∇]ω = ∂²v·∇ω + 2∂v·∇∂ω`).  The commutator majorant `commJet2` splits as
`16 (∫ t1 + 2 ∫ t2)` with
`t1 = |D²ω| |D²v| |Dω|` and `t2 = |D²ω|² |Dv|`.  Each term is bounded on a time slice by
`ν ‖D³ω‖² + K (1 + ‖D²ω‖²)`.

* `SliceT1Bound`: `t1` (Hölder `L³ × L² × L⁶`, `cylGN_proof` `m = 3` for `l = 2, 1`,
  `‖D²v‖₂² ≤ K₁‖Dω‖₂²` from `apElliptic`, Young);
* `SliceT2Bound`: `t2` (Hölder `L³ × L³ × L³`, `cylGN_proof` `m = 3`, `l = 2`;
  `‖Dv‖₃³ ≤ ‖Dv‖_∞ ‖Dv‖₂²`, `‖Dv‖_∞² ≲ ‖Dv‖₂ ‖D³v‖₂ + ...` from `CylSupInterp`,
  `‖D³v‖² ≤ K₂ ‖D²ω‖²` from `apElliptic`; Young with exponents `3/2, 3`).

`apLevel3Static_of` closes `APLevel3Static` from these two.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Hypotheses on one time slice `u = v(r)` of a classical a priori solution: smooth, `c`-periodic,
divergence free, all derivatives bounded, all derivatives in `L²(cell)`. -/
def SliceOK (c : ℝ) (u : Plane → Vec) : Prop :=
  ContDiff ℝ ∞ u ∧ Cyl.IsPeriodic c u ∧ (∀ z, Cyl.divergence u z = 0) ∧
    (∀ i : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ i u z‖ ≤ M) ∧
    ∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i u z‖ ^ 2) (Cyl.cell c)

/-- Integrand `|D²ω| |D²u| |Dω|` of the first commutator term. -/
def commT1 (u : Plane → Vec) (z : Plane) : ℝ :=
  ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ *
    (‖iteratedFDeriv ℝ 2 u z‖ * ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖)

/-- Integrand `|D²ω|² |Du|` of the second commutator term. -/
def commT2 (u : Plane → Vec) (z : Plane) : ℝ :=
  ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ * (‖iteratedFDeriv ℝ 1 u z‖ *
    ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖)

/-- **Leaf (first commutator term)** (lines 285-288).  For `ν > 0` and `A` there is `K ≥ 0` such
that for every slice with `‖u‖₂², ‖ω‖₂², ‖Dω‖₂², |ω| ≤ A`: `t1` is integrable on the cell and
`∫ t1 ≤ ν ‖D³ω‖₂² + K (1 + ‖D²ω‖₂²)`.
Route: Hölder `‖D²ω‖₃ ‖D²u‖₂ ‖Dω‖₆`; `cylGN_proof` (`m = 3`, `l = 2` and `l = 1`):
`‖D²ω‖₃ ≤ C|ω|_∞^{1/3}‖D³ω‖₂^{2/3}`, `‖Dω‖₆ ≤ C|ω|_∞^{2/3}‖D³ω‖₂^{1/3}`; `‖D²u‖₂² ≤ K₁‖Dω‖₂²`
(`apElliptic`, `j = 1`); then `∫ t1 ≤ C A ‖D³ω‖₂ ‖Dω‖₂` and Young. -/
def SliceT1Bound : Prop :=
  ∀ ν A : ℝ, 0 < ν → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℝ) (u : Plane → Vec), 1 ≤ c → SliceOK c u →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 u z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∀ z : Plane, |Cyl.curl u z| ≤ A) →
      IntegrableOn (fun z => commT1 u z) (Cyl.cell c) ∧
      (∫ z in Cyl.cell c, commT1 u z) ≤
        ν * (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 3 (Cyl.curl u) z‖ ^ 2) +
          K * (1 + ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ ^ 2)

/-- **Leaf (second commutator term)** (lines 285-288).  Same hypotheses as `SliceT1Bound`:
`t2` is integrable on the cell and `∫ t2 ≤ ν ‖D³ω‖₂² + K (1 + ‖D²ω‖₂²)`.
Route: Hölder `‖Dv‖₃ ‖D²ω‖₃²`; `cylGN_proof` (`m = 3`, `l = 2`): `‖D²ω‖₃² ≤ C A^{2/3}‖D³ω‖₂^{4/3}`;
`‖Dv‖₃³ ≤ ‖Dv‖_∞ ‖Dv‖₂²` with `‖Dv‖_∞` from `CylSupInterp`/`cylinder_interpolation_uniform`
applied to the components of `Dv` and `‖D^{j+1}v‖² ≤ K_j ‖D^jω‖²` (`apElliptic`), giving
`‖Dv‖₃⁶ ≲ A^{c₁} (1 + ‖D²ω‖₂²)^{1/2}`-type growth; Young with exponents `3/2` and `3` absorbs
`‖D³ω‖₂²` (the remaining power of `1 + ‖D²ω‖₂²` is at most `1`). -/
def SliceT2Bound : Prop :=
  ∀ ν A : ℝ, 0 < ν → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℝ) (u : Plane → Vec), 1 ≤ c → SliceOK c u →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 u z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖ ^ 2) ≤ A →
    (∀ z : Plane, |Cyl.curl u z| ≤ A) →
      IntegrableOn (fun z => commT2 u z) (Cyl.cell c) ∧
      (∫ z in Cyl.cell c, commT2 u z) ≤
        ν * (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 3 (Cyl.curl u) z‖ ^ 2) +
          K * (1 + ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ ^ 2)

/-- `PartI:T04/10/2`, conditional on the two slice-level leaves. -/
theorem apLevel3Static_of (h1 : SliceT1Bound) (h2 : SliceT2Bound) : APLevel3Static := by
  intro ν A ε _hν hε
  obtain ⟨K1, hK1, hT1⟩ := h1 (ε / 48) A (by positivity)
  obtain ⟨K2, hK2, hT2⟩ := h2 (ε / 48) A (by positivity)
  refine ⟨16 * (K1 + 2 * K2), by positivity, ?_⟩
  intro c T v p hc hcls r hr hA0 hW0 hW1 hsup
  have hu : ContDiff ℝ ∞ (v r) := by
    have h := hcls.classical.smooth_v.comp_contDiff
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => r)).prodMk contDiff_id :
        ContDiff ℝ ∞ (fun z : Plane => ((r, z) : ℝ × Plane)))
      (fun z => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ univ))
    exact h
  have hslice : SliceOK c (v r) := by
    refine ⟨hu, hcls.classical.periodic_v r hr, hcls.classical.solenoidal r hr, fun i => ?_,
      fun i => ?_⟩
    · obtain ⟨M, hM⟩ := hcls.bounded i
      exact ⟨M, fun z => hM r hr z⟩
    · obtain ⟨K, hK⟩ := hcls.jet_l2 i
      exact (hK r hr).1
  obtain ⟨i1, b1⟩ := hT1 c (v r) hc hslice hA0 hW0 hW1 hsup
  obtain ⟨i2, b2⟩ := hT2 c (v r) hc hslice hA0 hW0 hW1 hsup
  have hcomm : commJet2 c v r = 16 * ((∫ z in Cyl.cell c, commT1 (v r) z) +
      2 * ∫ z in Cyl.cell c, commT2 (v r) z) := by
    unfold commJet2
    congr 1
    rw [← integral_const_mul, ← integral_add i1 (i2.const_mul 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [commT1, commT2]
    ring
  have hY2 : vortJet c 2 v r = ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2 :=
    rfl
  have hY3 : vortJet c 3 v r = ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 3 (Cyl.curl (v r)) z‖ ^ 2 :=
    rfl
  have hY2n : 0 ≤ vortJet c 2 v r := integral_nonneg fun z => sq_nonneg _
  have hY3n : 0 ≤ vortJet c 3 v r := integral_nonneg fun z => sq_nonneg _
  rw [hcomm]
  rw [← hY2, ← hY3] at b1 b2
  nlinarith [b1, b2, hY2n, hY3n, hK1, hK2]

end UnforcedLeray.Short.PartI
