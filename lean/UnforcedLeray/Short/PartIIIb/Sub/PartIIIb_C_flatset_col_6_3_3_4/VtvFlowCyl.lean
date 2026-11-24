import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvFlowCyl : VtvFlowCyl := by
  intro ν c tr s hs φ hφ
  -- the velocity is smooth in the plane variable at age `s > 0`
  have hv : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v s x) := by
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.mono (prod_mono (Ioi_subset_Ici le_rfl) subset_rfl)
    have hpair : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((s, x) : ℝ × (ℝ × ℝ))) :=
      contDiff_const.prodMk contDiff_id
    have hmem : ∀ x : ℝ × ℝ, ((s, x) : ℝ × (ℝ × ℝ)) ∈ Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) := fun x =>
      ⟨hs, mem_univ _⟩
    exact h1.comp_contDiff hpair hmem
  have hv0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v s x 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hv
  have hv1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v s x 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hv
  have hL : ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.lapP φ) :=
    ((hφ.pd 0).pd 0).smooth.add ((hφ.pd 1).pd 1).smooth
  refine ⟨?_, ?_, ?_⟩
  · exact (contDiff_const.mul hL).add
      ((hv0.mul (hφ.pd 0).smooth).add (hv1.mul (hφ.pd 1).smooth))
  · intro x
    have h1 := ((hφ.pd 0).pd 0).periodic x
    have h2 := ((hφ.pd 1).pd 1).periodic x
    have h3 := (hφ.pd 0).periodic x
    have h4 := (hφ.pd 1).periodic x
    have hv' := tr.isTrain.periodic_v s hs.le x
    show ν * (B0579.pd 0 (B0579.pd 0 φ) (x.1 + c, x.2) + B0579.pd 1 (B0579.pd 1 φ) (x.1 + c, x.2)) +
        (tr.v s (x.1 + c, x.2) 0 * B0579.pd 0 φ (x.1 + c, x.2) +
          tr.v s (x.1 + c, x.2) 1 * B0579.pd 1 φ (x.1 + c, x.2)) =
      ν * (B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x) +
        (tr.v s x 0 * B0579.pd 0 φ x + tr.v s x 1 * B0579.pd 1 φ x)
    rw [h1, h2, h3, h4, hv']
  · obtain ⟨R1, hR1⟩ := (hφ.pd 0).band
    obtain ⟨R2, hR2⟩ := (hφ.pd 1).band
    obtain ⟨R3, hR3⟩ := ((hφ.pd 0).pd 0).band
    obtain ⟨R4, hR4⟩ := ((hφ.pd 1).pd 1).band
    refine ⟨max (max R1 R2) (max R3 R4), fun x hx => ?_⟩
    have hx1 : R1 < |x.2| := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2 : R2 < |x.2| := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx3 : R3 < |x.2| := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hx4 : R4 < |x.2| := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    show ν * (B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x) +
        (tr.v s x 0 * B0579.pd 0 φ x + tr.v s x 1 * B0579.pd 1 φ x) = 0
    rw [hR1 x hx1, hR2 x hx2, hR3 x hx3, hR4 x hx4]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
