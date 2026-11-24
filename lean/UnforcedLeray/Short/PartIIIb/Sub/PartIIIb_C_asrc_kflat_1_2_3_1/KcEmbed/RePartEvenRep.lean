import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.RePartEvenCirc
import UnforcedLeray.Short.PartIIIa.CanonicalTransfer

/-!
# Pointwise-even representative of the real part (replacement for `rePart_even_zeroCirc`)

Source: `the November 2 reference manuscript` 3176-3184, 3228-3240.
`IsCentrallyEven` is pointwise on `ℝ × ℝ`, while `xFn_even` holds only a.e. on the cell, so the
literal statement for `fun x => ((xFn ξ x).re : ℂ)` is not provable (arbitrary representative).
Here the symmetrised representative `g p = Re ((xFn ξ p + xFn ξ (-p)) / 2)` is pointwise even,
agrees a.e. on the cell (hence a.e. for `cellMeasure`) with `Re (xFn ξ)`, and has zero circulation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- The symmetrised real part of `xFn ξ`. -/
def reSym {c m : ℝ} [Fact (1 < m)] (ξ : Xmc c m) : ℝ × ℝ → ℂ :=
  fun x => ((((xFn ξ x).re + (xFn ξ (-x)).re) / 2 : ℝ) : ℂ)

theorem reSym_ae {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    reSym ξ =ᵐ[volume.restrict (B0579.cell c)] fun x => (((xFn ξ x).re : ℝ) : ℂ) := by
  filter_upwards [xFn_even ξ] with p hp
  simp only [reSym, hp]
  congr 1
  ring

theorem reSym_even {c m : ℝ} [Fact (1 < m)] (ξ : Xmc c m) :
    UnforcedLeray.Short.IIIa.IsCentrallyEven (reSym ξ) := by
  intro x
  simp only [reSym, neg_neg]
  congr 1
  ring

theorem rePart_evenRep_zeroCirc {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    ∃ g : ℝ × ℝ → ℂ, g =ᵐ[volume.restrict (B0579.cell c)] (fun x => (((xFn ξ x).re : ℝ) : ℂ)) ∧
      g =ᵐ[B0579.cellMeasure c m] (fun x => (((xFn ξ x).re : ℝ) : ℂ)) ∧
      UnforcedLeray.Short.IIIa.IsCentrallyEven g ∧
      UnforcedLeray.Short.IIIa.HasZeroCirculation c g := by
  have h1 := reSym_ae ξ
  have h2 := rePart_zeroCirc_aux ξ
  refine ⟨reSym ξ, h1, ae_cellMeasure_of_ae_cell h1, reSym_even ξ, ?_⟩
  exact ⟨h2.1.congr h1.symm, by rw [integral_congr_ae h1]; exact h2.2⟩

end UnforcedLeray.Short.PartIIIb.Concrete
