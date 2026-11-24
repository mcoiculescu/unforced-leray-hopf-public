import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Space
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H4
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4

/-!
# Part III-b, KcEmbed: `J_a⁻¹` of the real part of `xFn ξ`

Source of record: `the November 2 reference manuscript` (SP), eq:ct-embeddings,
lines 3228-3240, and 3176-3184. For `1 ≤ a`, the rescaled real part `J_a⁻¹ (Re xFn ξ)` lies in
`L²` of the moving cell `cellMeasure (cellLen c a) m`, and its weighted norm is dominated by that
of `J_a⁻¹ (xFn ξ)`, because `|Re z| ≤ ‖z‖` pointwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

theorem jscaleInv_rePart_memLp_le {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (a : ℝ) (ha : 1 ≤ a) (ξ : Xmc c m) : MemLp (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) ∧ IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) ≤ IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
  have hm1 : (1 : ℝ) < m := Fact.out
  have hm : 0 ≤ m := by linarith
  have hg : MemLp (xFn ξ) 2 (B0579.cellMeasure c m) := xFn_memLp ξ
  have hgn : IIIa.xNorm c m (xFn ξ) ≠ ⊤ := hg.eLpNorm_lt_top.ne
  -- finiteness of the weighted norm of `J_a⁻¹ (xFn ξ)` on the moving cell
  have hxn : IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgn)
      (IIIa.xNorm_JscaleInv_le c m a hm ha (xFn ξ) hg)
  have hxFn : MemLp (IIIa.JscaleInv a (xFn ξ)) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) :=
    ⟨IIIa.aesm_JscaleInv ha hg, lt_top_iff_ne_top.2 hxn⟩
  -- the real part, as a complex-valued `L²` function on the cell
  have hF : MemLp (fun x => (((xFn ξ x).re : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    (hg.re).ofReal
  have hJF : AEStronglyMeasurable (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ)))
      (B0579.cellMeasure (IIIa.cellLen c a) m) :=
    IIIa.aesm_JscaleInv ha hF
  -- pointwise domination `‖J_a⁻¹ (Re xFn) y‖ ≤ ‖J_a⁻¹ (xFn) y‖`
  have hpt : ∀ y : ℝ × ℝ, ‖IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ)) y‖ ≤
      ‖IIIa.JscaleInv a (xFn ξ) y‖ := by
    intro y
    simp only [IIIa.JscaleInv, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hJle : IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ)))
      ≤ IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
    unfold IIIa.xNorm
    exact eLpNorm_mono hpt
  exact ⟨MemLp.of_le hxFn hJF (ae_of_all _ hpt), hJle⟩

end UnforcedLeray.Short.PartIIIb.Concrete
