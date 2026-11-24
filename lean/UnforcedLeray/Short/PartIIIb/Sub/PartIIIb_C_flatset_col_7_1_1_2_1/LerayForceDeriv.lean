import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# `ForceFieldDeriv` (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/leray/21`)

The componentwise directional derivative `∂_v F` of a force field is again a force field: smooth
(`ContDiff.fderiv_right` and `clm_apply`), `c`-periodic in `q` (`fderiv_comp_add_right` applied to
the periodicity of `F`), and supported in the same closed band (a derivative of a function vanishing
on an open set vanishes there, `Filter.EventuallyEq.fderiv_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The derivative of a force field is a force field. -/
theorem forceFieldDeriv : ForceFieldDeriv := by
  intro c F hF v
  obtain ⟨hsm, hper, s0, s1, L, hs0, hsupp⟩ := hF
  -- `F` vanishes off the closed band, componentwise
  have hbandF : ∀ x : Chart, ¬(x.1 ∈ Icc s0 s1 ∧ |x.2.2| ≤ L) → ∀ i, F x i = 0 := by
    intro x hx i
    by_contra hne
    apply hx
    apply hsupp x
    intro h0
    apply hne
    simp [h0]
  have hclosed : IsClosed {x : Chart | x.1 ∈ Icc s0 s1 ∧ |x.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hopen := hclosed.isOpen_compl
  -- each component's derivative vanishes off the band
  have hloc : ∀ (i : Fin 2) (p : Chart), ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
      fderiv ℝ (fun p' => F p' i) p = 0 := by
    intro i p hp
    have hev : (fun p' => F p' i) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hp] with x hx
      exact hbandF x hx i
    rw [hev.fderiv_eq]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hg : ContDiff ℝ ∞ (fun p' => F p' i) := hsm i
    have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ (fun p' => F p' i) p) :=
      hg.fderiv_right (m := ∞) le_rfl
    exact hd.clm_apply contDiff_const
  · intro s q η
    funext i
    have hshift : ∀ x : Chart,
        fderiv ℝ (fun p' => F p' i) (x + (0, (c, (0 : ℝ)))) =
          fderiv ℝ (fun p' => F p' i) x := by
      intro x
      have hfun : (fun z : Chart => F (z + (0, (c, (0 : ℝ)))) i) = fun z => F z i := by
        funext z
        obtain ⟨s', q', η'⟩ := z
        simp only [Prod.mk_add_mk, add_zero]
        exact congrFun (hper s' q' η') i
      have h := fderiv_comp_add_right (𝕜 := ℝ) (f := fun p' => F p' i) (0, (c, (0 : ℝ))) (x := x)
      rw [hfun] at h
      exact h.symm
    have hp : ((s, (q + c, η)) : Chart) = (s, (q, η)) + (0, (c, (0 : ℝ))) := by
      simp
    show fderiv ℝ (fun p' => F p' i) (s, (q + c, η)) v =
      fderiv ℝ (fun p' => F p' i) (s, (q, η)) v
    rw [hp, hshift]
  · refine ⟨s0, s1, L, hs0, ?_⟩
    intro p hp
    by_contra hnot
    apply hp
    funext i
    simp only [Pi.zero_apply]
    rw [hloc i p hnot, zero_apply]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
