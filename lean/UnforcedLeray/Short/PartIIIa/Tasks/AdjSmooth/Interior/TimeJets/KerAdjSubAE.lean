import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerAdjXBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Bdd
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Meas
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.CylUniq

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **(13) The kernel adjoint is linear almost everywhere** (SP 3052-3058): both sides lie in
`X_{-2,d}` by `KerAdjXBound 2`, and have the same cylinder test pairings by `KerAdjFubini`;
`locCylUniq` then gives equality of the `X_{-2,d}` difference. -/
theorem kerAdjSubAE : KerAdjSubAE := by
  intro d hd F F' hF hF' α β
  have hd0 : 0 < d := by linarith
  set G : Fin 2 → ℝ × ℝ → ℂ := fun l y => α * F l y + β * F' l y with hG
  have hGI : ∀ l, IntegrableOn (G l) (B0579.cell d) := fun l =>
    ((hF l).1.const_mul α).add ((hF' l).1.const_mul β)
  have hGL : ∀ l, MemLp (G l) 2 (volume.restrict (B0579.cell d)) := fun l =>
    ((hF l).2.const_mul α).add ((hF' l).2.const_mul β)
  have hGall : ∀ l, IntegrableOn (G l) (B0579.cell d) ∧
      MemLp (G l) 2 (volume.restrict (B0579.cell d)) := fun l => ⟨hGI l, hGL l⟩
  obtain ⟨C, hC0, hX⟩ := kerAdjXBound 2 one_lt_two
  have hXF := hX d hd F hF
  have hXF' := hX d hd F' hF'
  have hXG := hX d hd G hGall
  set h : ℝ × ℝ → ℂ := fun x => α * kerAdj d F x + β * kerAdj d F' x - kerAdj d G x with hh_def
  have hhM : MemLp h 2 (B0579.cellMeasure d (-2)) :=
    ((hXF.1.const_mul α).add (hXF'.1.const_mul β)).sub hXG.1
  have hFub : KerAdjFubini := kerAdjFubini_of kerNearFar
  -- the pairing of `h` with every cylinder test vanishes
  have hpair : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
      ∫ x in B0579.cell d, (hhM.toLp h) x * (ψ x : ℂ) = 0 := by
    intro ψ hψ
    have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), (hhM.toLp h) x = h x :=
      (Measure.ae_le_iff_absolutelyContinuous.2 (B0579.ac_cellMeasure d (-2)))
        (hhM.coeFn_toLp)
    have hint_eq : ∫ x in B0579.cell d, (hhM.toLp h) x * (ψ x : ℂ) =
        ∫ x in B0579.cell d, h x * (ψ x : ℂ) :=
      integral_congr_ae (hae.mono fun x hx => by dsimp only; rw [hx])
    obtain ⟨hIF, hEF⟩ := hFub d hd F (fun l => (hF l).1) ψ hψ
    obtain ⟨hIF', hEF'⟩ := hFub d hd F' (fun l => (hF' l).1) ψ hψ
    obtain ⟨hIG, hEG⟩ := hFub d hd G (fun l => (hGall l).1) ψ hψ
    have hV : ∀ H : Fin 2 → ℝ × ℝ → ℂ, (∀ l, IntegrableOn (H l) (B0579.cell d)) →
        Integrable (fun x => ∑ j, H j x * ((kerVel d ψ x j : ℝ) : ℂ))
          (volume.restrict (B0579.cell d)) := by
      intro H hH
      refine integrable_finsetSum _ fun j _ => ?_
      obtain ⟨B, hB⟩ := kerVelBdd d hd ψ hψ
      refine (hH j).mul_bdd (c := B) ?_ ?_
      · exact Complex.continuous_ofReal.comp_aestronglyMeasurable (kerVelMeas d hd ψ hψ j)
      · exact Filter.Eventually.of_forall fun x => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact hB x j
    have hsplit : ∫ x in B0579.cell d, h x * (ψ x : ℂ) =
        α * (∫ x in B0579.cell d, kerAdj d F x * (ψ x : ℂ)) +
          β * (∫ x in B0579.cell d, kerAdj d F' x * (ψ x : ℂ)) -
          (∫ x in B0579.cell d, kerAdj d G x * (ψ x : ℂ)) := by
      have e : (fun x => h x * (ψ x : ℂ)) = fun x =>
          α * (kerAdj d F x * (ψ x : ℂ)) + β * (kerAdj d F' x * (ψ x : ℂ)) -
            kerAdj d G x * (ψ x : ℂ) := by
        funext x
        simp only [hh_def]
        ring
      have hI1 : Integrable (fun x => α * (kerAdj d F x * (ψ x : ℂ)) +
          β * (kerAdj d F' x * (ψ x : ℂ))) (volume.restrict (B0579.cell d)) :=
        (hIF.const_mul α).add (hIF'.const_mul β)
      rw [e, integral_sub hI1 hIG,
        integral_add (hIF.const_mul α) (hIF'.const_mul β), integral_const_mul, integral_const_mul]
    have hGsum : ∫ x in B0579.cell d, ∑ j, G j x * ((kerVel d ψ x j : ℝ) : ℂ) =
        α * (∫ x in B0579.cell d, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ)) +
          β * (∫ x in B0579.cell d, ∑ j, F' j x * ((kerVel d ψ x j : ℝ) : ℂ)) := by
      have e2 : (fun x => ∑ j, G j x * ((kerVel d ψ x j : ℝ) : ℂ)) = fun x =>
          α * (∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ)) +
            β * (∑ j, F' j x * ((kerVel d ψ x j : ℝ) : ℂ)) := by
        funext x
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        ring
      have hA : Integrable (fun x => α * (∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ)) +
          β * (∑ j, F' j x * ((kerVel d ψ x j : ℝ) : ℂ))) (volume.restrict (B0579.cell d)) :=
        ((hV F (fun l => (hF l).1)).const_mul α).add ((hV F' (fun l => (hF' l).1)).const_mul β)
      rw [e2, integral_add ((hV F (fun l => (hF l).1)).const_mul α)
        ((hV F' (fun l => (hF' l).1)).const_mul β), integral_const_mul, integral_const_mul]
    rw [hint_eq, hsplit, hEF, hEF', hEG, hGsum]
    ring
  have hzero := locCylUniq d 2 hd0 (hhM.toLp h) hpair
  have h1 : h =ᵐ[B0579.cellMeasure d (-2)] 0 := by
    have hc := hhM.coeFn_toLp
    rw [hzero] at hc
    exact hc.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have hz : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), h x = 0 :=
    (Measure.ae_le_iff_absolutelyContinuous.2 (B0579.ac_cellMeasure d (-2))) h1
  filter_upwards [hz] with x hx
  exact sub_eq_zero.1 hx

end UnforcedLeray.Short.IIIa
