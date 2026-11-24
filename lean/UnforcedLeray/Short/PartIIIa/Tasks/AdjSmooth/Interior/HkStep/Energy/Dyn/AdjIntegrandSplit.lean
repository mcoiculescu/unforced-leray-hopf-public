import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakOf

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem adjIntegrandSplit (m : ℝ) (hX : UnforcedLeray.Short.IIIa.XMulTestInt)
    (hV : UnforcedLeray.Short.IIIa.VelMulMemX m) : UnforcedLeray.Short.IIIa.AdjIntegrandSplit m := by
  intro ν tr t s g φ a b χ hctx r hr ψ uψ hψ hK
  have hctx' := hctx
  obtain ⟨hν, -, -, -, -, hW, -, hta, hab, hbs, hChi⟩ := hctx'
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hrI : r ∈ Icc t s := ⟨le_trans hta hr.1.le, le_trans hr.2.le hbs.le⟩
  have hφm : MemLp (φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    hW.memX r hrI
  have hlap : IntegrableOn (fun x => φ r x * (lapP ψ x : ℂ)) (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (φ r) (lapP ψ) hc hφm (isCylTest_lapP hψ)
  have hv : ∀ l : Fin 2, IntegrableOn
      (fun x => ((tr.v r x l : ℝ) : ℂ) * φ r x * (B0579.pd l ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    fun l => hX (ν ^ (-2 : ℝ)) m (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) (B0579.pd l ψ) hc
      ((hV ν tr t s g φ a b χ hctx r hr l).2) (hψ.pd l)
  have hVint : IntegrableOn
      (fun x => φ r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) := by
    refine ((hv 0).add (hv 1)).congr_fun ?_ (B0579.measurableSet_cell _)
    intro x _
    simp only [Pi.add_apply]
    push_cast
    ring
  have hUint : IntegrableOn
      (fun x => φ r x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
        uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    ((hChi r (Set.Ioo_subset_Icc_self hr)).2.2 ψ uψ hψ hK).1
  have key : ∀ x : ℝ × ℝ, adjIntegrand tr (φ r) r ψ uψ x =
      (ν : ℂ) * (φ r x * (lapP ψ x : ℂ)) -
        φ r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) -
        φ r x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
          uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) := by
    intro x
    unfold adjIntegrand
    push_cast
    ring
  have hA : IntegrableOn (fun x => (ν : ℂ) * (φ r x * (lapP ψ x : ℂ)))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    Integrable.const_mul hlap (ν : ℂ)
  simp_rw [key]
  have hAV : IntegrableOn (fun x => (ν : ℂ) * (φ r x * (lapP ψ x : ℂ)) -
      φ r x * ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) := hA.sub hVint
  rw [MeasureTheory.integral_sub hAV hUint,
    MeasureTheory.integral_sub hA hVint, MeasureTheory.integral_const_mul]

end UnforcedLeray.Short.IIIa
