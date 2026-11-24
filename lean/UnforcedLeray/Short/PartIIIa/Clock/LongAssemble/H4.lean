import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L1
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4

/-!
# Part III-a long assembly, H4: measurability of `J_a⁻¹ g` on the moving cell

If `g ∈ L²(cellMeasure c m)` and `1 ≤ a`, then `J_a⁻¹ g` is a.e.-strongly measurable for the
moving cell measure `cellMeasure (cellLen c a) m`. Proof: replace `g` by a measurable a.e.
representative `h` (L1) and transport the a.e. equality along `y ↦ √a • y` (L4).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma aesm_JscaleInv {c m a : ℝ} {g : ℝ × ℝ → ℂ} (ha : 1 ≤ a)
    (hg : MemLp g 2 (UnforcedLeray.B0579.cellMeasure c m)) :
    AEStronglyMeasurable (JscaleInv a g) (UnforcedLeray.B0579.cellMeasure (cellLen c a) m) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨h, hmeas, hgh, -⟩ := ae_representative_xNorm c m g hg
  have hgh' : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), g x = h x :=
    (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le hgh
  have hae := jscale_ae_of_ae c a ha0 g h hgh'
  have hae2 : JscaleInv a g =ᵐ[UnforcedLeray.B0579.cellMeasure (cellLen c a) m] JscaleInv a h :=
    (UnforcedLeray.B0579.cellMeasure_ac (cellLen c a) m).ae_le hae
  have hJ : Measurable (JscaleInv a h) := by
    unfold JscaleInv
    exact measurable_const.mul (hmeas.comp
      ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)))
  exact hJ.aestronglyMeasurable.congr hae2.symm

end UnforcedLeray.Short.IIIa
