import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_5
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1

/-!
# `PartIII-a:T21/2/7/1/7/5/1`: the kernel adjoint is an element of `X_{-m,c}`

Proves `LocKerAdjElt` (`Sub/PartIII-a_T21_2_7_1_7_5.lean`) from `KernelAdjointBound`
(`Sub/PartIIIa_T21_2_1.lean`, SP 2875-2896, 3055-3057), `LocWeakMeas` (`Sub/PartIII-a_T21_2_7_1_7_4.lean`).

Route. `KernelAdjointBound` gives, for `c ≥ 1`, a weak-derivative pair `(χ₀, g)` with
`h1Norm c m χ₀ g ≤ C Σ_j (‖F_j‖₁ + ‖F_j‖₂)` and the duality identity on cylinder tests. `LocWeakMeas`
makes `χ₀` a.e.-strongly measurable on the cell; `xNorm c (-m) χ₀ ≤ h1Norm c m χ₀ g < ∞` gives
`MemLp χ₀ 2 (cellMeasure c (-m))`. The element `χ := (MemLp).toLp χ₀` of `AdjX c m` has the
same norm and the same integrals (a.e. equality transfers through `ac_cellMeasure`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem locKerAdjElt (m : ℝ) (hm : 8 < m) (hK : KernelAdjointBound m) (hW : LocWeakMeas) :
    LocKerAdjElt m := by
  unfold KernelAdjointBound at hK
  unfold LocWeakMeas at hW
  unfold LocKerAdjElt
  obtain ⟨C, hC0, hC⟩ := hK (by linarith : (1 : ℝ) < m)
  refine ⟨C, hC0, fun c hc F hF => ?_⟩
  obtain ⟨χ₀, gχ, hder, hh1, hdual⟩ := hC c hc F hF
  -- measurability of `χ₀` on the cell, hence w.r.t. the weighted cell measure
  have hmeas : AEStronglyMeasurable χ₀ (volume.restrict (B0579.cell c)) :=
    hW c hc 0 χ₀ (gχ 0) (hder 0)
  have hmeasμ : AEStronglyMeasurable χ₀ (B0579.cellMeasure c (-m)) :=
    hmeas.mono_ac (B0579.cellMeasure_ac c (-m))
  -- the weighted `L²` norm of `χ₀` is bounded by the `H¹` norm
  have key : xNorm c (-m) χ₀ ≤ h1Norm c m χ₀ gχ := by
    unfold h1Norm
    calc xNorm c (-m) χ₀ = (xNorm c (-m) χ₀ ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
      _ ≤ (xNorm c (-m) χ₀ ^ 2 + ∑ j, xNorm c (-m) (gχ j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_self_add (by norm_num)
  -- finiteness of the right-hand side of the bound
  have hfin1 : ∀ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) ≠ ⊤ := fun j => by
    have h1 : MemLp (F j) 1 (volume.restrict (B0579.cell c)) :=
      memLp_one_iff_integrable.2 (hF j).1
    exact h1.eLpNorm_ne_top
  have hfin2 : ∀ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell c)) ≠ ⊤ := fun j =>
    (hF j).2.eLpNorm_ne_top
  have hS : ENNReal.ofReal C * ∑ j : Fin 2,
      (eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
        eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.add_ne_top.2 ⟨hfin1 j, hfin2 j⟩)
  have hxfin : xNorm c (-m) χ₀ < ⊤ := lt_of_le_of_lt (key.trans hh1) (lt_top_iff_ne_top.2 hS)
  have hmem : MemLp χ₀ 2 (B0579.cellMeasure c (-m)) := ⟨hmeasμ, hxfin⟩
  refine ⟨hmem.toLp χ₀, ?_, ?_⟩
  · -- the norm bound
    rw [Lp.enorm_def]
    calc eLpNorm (hmem.toLp χ₀) 2 (B0579.cellMeasure c (-m))
        = eLpNorm χ₀ 2 (B0579.cellMeasure c (-m)) :=
          eLpNorm_congr_ae (MemLp.coeFn_toLp hmem)
      _ = xNorm c (-m) χ₀ := rfl
      _ ≤ h1Norm c m χ₀ gχ := key
      _ ≤ ENNReal.ofReal C * ∑ j : Fin 2,
          (eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
            eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) := hh1
  · -- the duality identity
    intro ψ uψ hψ huψ
    have hae : (⇑(hmem.toLp χ₀)) =ᵐ[volume.restrict (B0579.cell c)] χ₀ :=
      (B0579.ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp hmem)
    calc ∫ x in B0579.cell c, hmem.toLp χ₀ x * (ψ x : ℂ)
        = ∫ x in B0579.cell c, χ₀ x * (ψ x : ℂ) :=
          integral_congr_ae (hae.mono fun x hx => by simp only [hx])
      _ = ∫ x in B0579.cell c, ∑ j : Fin 2, F j x * ((uψ x j : ℝ) : ℂ) :=
          hdual ψ uψ hψ huψ

end UnforcedLeray.Short.IIIa
