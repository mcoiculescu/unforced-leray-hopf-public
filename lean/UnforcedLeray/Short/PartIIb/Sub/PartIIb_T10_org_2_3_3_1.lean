import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_of

/-!
# `PartII-b:T10/org/2/3/3/1`: the real Leray formula on test fields

`𝐏f = f + ∇ψ`, `ψ = N ∗ div f`, for smooth compactly supported real fields in `L^r`, `1 < r < ∞`
(`RealLerayTestFormula`).  The field `f + ∇ψ` is solenoidal and in `L^r`, hence fixed by `𝐏`
(`lerayLp_eq_self`); `∇ψ` is killed by `𝐏` (`lerayLp_gradient_eq_zero`, using `ψ ∈ L²` from the
decay bound); linearity of `𝐏` gives the formula.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Solenoidality is invariant under a.e. equality of fields. -/
theorem isSolenoidal_congr_ae_aux {f g : SpatialField} (hf : IsSolenoidal f)
    (hfg : f =ᵐ[volume] g) : IsSolenoidal g where
  integrable φ hφ := (hf.integrable φ hφ).congr (hfg.mono fun x hx => by simp only [hx])
  identity φ hφ := by
    rw [← hf.identity φ hφ]
    exact integral_congr_ae (hfg.mono fun x hx => by simp only [hx])

theorem realLerayTestFormula_proof : UnforcedLeray.Short.IIb.RealLerayTestFormula := by
  intro r hr h1 h2 f hf hm
  have hG : MemLp (gradField (lerayPotential f)) r volume :=
    memLp_gradField_lerayPotential' hf h1
  have hV : MemLp (vecField f + gradField (lerayPotential f)) r volume :=
    (memLp_vecField hf r).add hG
  obtain ⟨M, hM, -⟩ := lerayPotential_decay hf
  have hψ2 : MemLp (lerayPotential f) 2 volume :=
    MemLp.of_le (memLp_decayWeight.const_mul M)
      (lerayPotential_contDiff hf).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        exact (hM x).trans (le_abs_self _))
  have hsol : IsSolenoidal (vecField f + gradField (lerayPotential f)) :=
    isSolenoidal_vecField_add_gradField hf
  have hVc : (hV.toLp (vecField f + gradField (lerayPotential f)) : SpatialField) =ᵐ[volume]
      vecField f + gradField (lerayPotential f) :=
    hV.coeFn_toLp
  have hGc : (hG.toLp (gradField (lerayPotential f)) : SpatialField) =ᵐ[volume]
      gradField (lerayPotential f) :=
    hG.coeFn_toLp
  have e1 : lerayLp r h1 h2 (hV.toLp (vecField f + gradField (lerayPotential f))) =
      hV.toLp (vecField f + gradField (lerayPotential f)) :=
    lerayLp_eq_self h1 h2 _ (isSolenoidal_congr_ae_aux hsol hVc.symm)
  have e2 : lerayLp r h1 h2 (hG.toLp (gradField (lerayPotential f))) = 0 :=
    lerayLp_gradient_eq_zero h1 h2 (lerayPotential_contDiff hf) (by norm_num) hψ2 hG
  have hF : hm.toLp (vecField f) = hV.toLp (vecField f + gradField (lerayPotential f)) -
      hG.toLp (gradField (lerayPotential f)) := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, Lp.coeFn_sub (hV.toLp (vecField f + gradField (lerayPotential f)))
      (hG.toLp (gradField (lerayPotential f))), hVc, hGc] with x a b c d
    rw [a, b, Pi.sub_apply, c, d]
    simp
  have hL : lerayLp r h1 h2 (hm.toLp (vecField f)) =
      hV.toLp (vecField f + gradField (lerayPotential f)) := by
    rw [hF, map_sub, e1, e2, sub_zero]
  rw [hL]
  exact hVc

end UnforcedLeray.Short.IIb
