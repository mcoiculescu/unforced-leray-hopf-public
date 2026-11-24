import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_1.Growth
import UnforcedLeray.Short.PartIIb.Sub.T22_4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Cutoff

/-!
# `PartIII-a:T21/c2/2/5/2`: `FmrIBPDiff`, decomposed (SP 2950-2954)

For a weight `p` with the symmetries of `movWeight` (`CellWt`) and `G = g²`, Green's second
identity on the cell with the cut-off `χ(η)`:
`∫χ²(pΔG - GΔp) + ∫2χχ'(p∂_ηG - G∂_ηp) = [flux]_{q=-c/2}^{q=c/2} = -2∫χ² G ∂_q p(c/2,η) dη ≤ 0`
(`p` even, `∂_q p` odd in `q`, `G`, `∂_qG` periodic, `∂_q p(c/2) ≥ 0`, `G ≥ 0`).  Removing the
cut-off with the `η`-decay of `g` gives `∫ pΔ(g²) ≤ ∫ g²Δp`, and `pΔ(g²) = 2 g Δg p + 2p|∇g|² ≥
2 g Δg p`.

Proved here: `movWeight_cellWt`, `fmrIBPDiff_of`.
Leaves: `DiffGreenCut`, `DiffSqLap`, `DiffLimitStmt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The symmetries and growth of a weight `p` on the cell `|q| ≤ c/2` that the integration by
parts uses; satisfied by `movWeight m a` (`movWeight_cellWt`). -/
structure CellWt (c m : ℝ) (p : B0579.Plane → ℝ) : Prop where
  smooth : ContDiff ℝ 2 p
  nonneg : ∀ x, 0 ≤ p x
  even : ∀ η, p (-c / 2, η) = p (c / 2, η)
  oddq : ∀ η, B0579.pd 0 p (-c / 2, η) = -B0579.pd 0 p (c / 2, η)
  seam_nonneg : ∀ η, 0 ≤ B0579.pd 0 p (c / 2, η)
  growth : ∃ K : ℝ, ∀ x : B0579.Plane,
    |p x| + |B0579.pd 0 p x| + |B0579.pd 1 p x| + |lapP p x| ≤ K * B0579.jb x ^ m

theorem movWeight_cellWt (c m a : ℝ) (hc : 0 < c) (hm : 0 ≤ m) (ha : 0 < a) :
    CellWt c m (movWeight m a) := by
  have hsq : (-c / 2) ^ 2 = (c / 2) ^ 2 := by ring
  refine ⟨movWeight_contDiff2 m a ha, fun x => ?_, fun η => ?_, fun η => ?_, fun η => ?_,
    mwGrowth m a hm ha⟩
  · exact Real.rpow_nonneg (movWeight_base_pos a ha x).le m
  · unfold movWeight; simp only [hsq]
  · rw [fmrIso_pd0 m a ha, fmrIso_pd0 m a ha]
    simp only [hsq]
    ring
  · rw [fmrIso_pd0 m a ha]
    simp only
    have h1 := Real.rpow_nonneg (movWeight_base_pos a ha (c / 2, η)).le (m - 1)
    positivity

/-- **Leaf `DiffGreenCut`** (SP 2950-2954; template `PartII-b` `DbCutId`
(`Tasks/CylEnergy/DiffusionBound/CutId.lean`) with the weight `jb^m` replaced by `p`):
the cut-off Green inequality for `G ∈ C²`, `c`-periodic in `q`, `G ≥ 0`, and a weight `p` with
`CellWt c m p`; `χ` smooth with compact support.  The fields are
`F₁ = χ²(p ∂_qG - G ∂_qp)`, `F₂ = χ²(p ∂_ηG - G ∂_ηp)`; `∫_cell ∂_qF₁ = F₁(c/2) - F₁(-c/2)
= -2∫ χ² G ∂_qp(c/2,·) ≤ 0` (`Lib.Cylinder.IBP.integral_cell_deriv_q`) and `∫_cell ∂_ηF₂ = 0`
(`integral_cell_deriv_eta`). -/
def DiffGreenCut : Prop :=
  ∀ (c m : ℝ) (p : B0579.Plane → ℝ), 0 < c → CellWt c m p →
    ∀ G : B0579.Plane → ℝ, ContDiff ℝ 2 G → (∀ x : B0579.Plane, G (x.1 + c, x.2) = G x) →
      (∀ x, 0 ≤ G x) → ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
        ∫ x in B0579.cell c, χ x.2 ^ 2 * (p x * lapP G x - G x * lapP p x) ≤
          -(∫ x in B0579.cell c, 2 * χ x.2 * deriv χ x.2 *
              (p x * B0579.pd 1 G x - G x * B0579.pd 1 p x))

/-- **Leaf `DiffSqLap`** (SP 2950-2954; product rule): for `g ∈ C²`, `g²` is `C²` and
`Δ(g²) = 2 g Δg + 2(|∂_q g|² + |∂_η g|²)`, `∂_η(g²) = 2 g ∂_η g`. -/
def DiffSqLap : Prop :=
  ∀ g : B0579.Plane → ℝ, ContDiff ℝ 2 g → ContDiff ℝ 2 (fun y => g y ^ 2) ∧
    (∀ x, lapP (fun y => g y ^ 2) x =
      2 * g x * lapP g x + 2 * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)) ∧
    (∀ x, B0579.pd 1 (fun y => g y ^ 2) x = 2 * g x * B0579.pd 1 g x)

/-- The target for a general weight with `CellWt`. -/
def DiffGenBound : Prop :=
  ∀ (c m : ℝ) (p : B0579.Plane → ℝ), 0 < c → CellWt c m p →
    ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
      2 * ∫ x in B0579.cell c, g x * lapP g x * p x ≤
        ∫ x in B0579.cell c, g x ^ 2 * lapP p x

/-- **Leaf `DiffLimitStmt`** (SP 2950-2954, `η`-decay; template `PartII-b` `dbLimit`,
`Tasks/CylEnergy/DiffusionBound/Limit.lean`, using `dbl_cut_tendsto`, `dbl_E_tendsto`,
`dbCutoff`): remove the cut-off in `DiffGreenCut` for `G = g²`, `g ∈ CylSmoothDecay c`:
`∫ pΔ(g²) ≤ ∫ g²Δp` (all integrands are dominated by `K · dbS² · jb^m`, `DbCommon.cell_int_dbS`;
`|χ_n'| ≤ K/(n+1)`), then `pΔ(g²) = 2gΔg p + 2p|∇g|² ≥ 2 g Δg p` (`p ≥ 0`), with integrability of
`g Δg p` by `cell_int_dbS`. -/
def DiffLimitStmt : Prop := DiffGreenCut → DiffSqLap → DbCutoff → DiffGenBound

theorem fmrIBPDiff_of (h1 : DiffGreenCut) (h2 : DiffSqLap) (h3 : DiffLimitStmt) : FmrIBPDiff := by
  intro c hc m a hm ha g hg
  exact h3 h1 h2 dbCutoff c m (movWeight m a) hc (movWeight_cellWt c m a hc hm ha) g hg

end UnforcedLeray.Short.IIIa
