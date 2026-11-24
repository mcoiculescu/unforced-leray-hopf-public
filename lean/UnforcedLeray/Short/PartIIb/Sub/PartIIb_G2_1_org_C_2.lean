import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C

/-!
# Part II-b, `PartII-b:G2/1/org/C/2`: `PhysHpRep`

Source of record: `the November 2 reference manuscript`, lines 1902-1906,
2432-2437.  Every `H_p`-profile `g₀` with vanishing imaginary part is represented almost
everywhere on `hMeas c bgp` by `MemLp.toLp (reM ∘ g₀) : HpR c`, with matching norm.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

private theorem liftM_reM_of_im_zero {v : CMerid} (h : ∀ i, (v i).im = 0) :
    liftM (reM v) = v := by
  ext i
  simp only [liftM, reM, WithLp.ofLp_toLp]
  exact Complex.ext (by simp) (by simp [h i])

theorem physHpRep : PhysHpRep := by
  intro c hc g₀ hg₀ hre
  let r₀ : Coord → Axi.Merid := fun x => reM (g₀ x)
  have hlift : ∀ x, liftM (r₀ x) = g₀ x := fun x => liftM_reM_of_im_zero (hre x)
  have hnorm : ∀ x, ‖r₀ x‖ = ‖g₀ x‖ := fun x => by
    rw [← liftM_norm (r₀ x), hlift x]
  have hmeas : AEStronglyMeasurable r₀ (hMeas c bgp) :=
    continuous_reM.comp_aestronglyMeasurable hg₀.meas
  have heLp : eLpNorm r₀ (ENNReal.ofReal bgp) (hMeas c bgp) = hNorm c bgp g₀ := by
    unfold hNorm
    exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hnorm)
  have hmem : MemLp r₀ (ENNReal.ofReal bgp) (hMeas c bgp) :=
    ⟨hmeas, by rw [heLp]; exact hg₀.finite⟩
  let g : HpR c := hmem.toLp r₀
  have hae : toProf c g =ᵐ[hMeas c bgp] g₀ := by
    filter_upwards [toProf_ae_eq hc g, hmem.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, hlift x]
  refine ⟨g, hae, ?_⟩
  have hne : hNorm c bgp g₀ = ‖g‖ₑ := by
    calc hNorm c bgp g₀ = hNorm c bgp (toProf c g) :=
          eLpNorm_congr_ae hae.symm
      _ = ‖g‖ₑ := hNorm_toProf hc g
  rw [hne, toReal_enorm]

end UnforcedLeray.Short.IIb
