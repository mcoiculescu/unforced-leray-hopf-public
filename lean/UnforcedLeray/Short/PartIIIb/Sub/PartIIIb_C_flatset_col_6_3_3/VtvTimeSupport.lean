import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3

/-!
# Band support of the two time integrands (source 4610, stream test band)

For a stream test `η` with band `[s₁,s₂]`: for `s < s₁` or `s₂ < s` the function
`s' ↦ η s' x` vanishes on a neighbourhood of `s`, so its derivative at `s` is `0`; and
`η s = 0`, so `R(s,η s) = 0`.  Both integrands therefore vanish outside the band.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate
open UnforcedLeray.Short.IIIa (flowIntegrand lapP)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Band support** (stream test `η` with `η = 0` for `s < s₁` or `s > s₂`). -/
theorem vtvTimeSupport : VtvTimeSupport := by
  intro ν c μ tr ω g b G f H η hη
  obtain ⟨_hsm, _hcyl, s₁, s₂, R, hs₁, hband⟩ := hη
  refine ⟨s₁, s₂, hs₁, fun s hs => ?_⟩
  have hη0 : ∀ x, η s x = 0 := fun x => by
    rcases hs with h | h
    · exact hband s x (Or.inl h)
    · exact hband s x (Or.inr (Or.inl h))
  have hd : (fun x => deriv (fun s' => η s' x) s) = fun _ => (0 : ℝ) := by
    funext x
    rcases hs with h | h
    · have hev : (fun s' => η s' x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_lt_nhds h] with s' hs'
        exact hband s' x (Or.inl hs')
      rw [hev.deriv_eq, deriv_const]
    · have hev : (fun s' => η s' x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds h] with s' hs'
        exact hband s' x (Or.inr (Or.inl hs'))
      rw [hev.deriv_eq, deriv_const]
  have hfun0 : η s = fun _ => (0 : ℝ) := funext fun x => hη0 x
  constructor
  · rw [hd]
    unfold vtvY
    simp
  · have hpd : ∀ j, B0579.pd j (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := fun j => by
      funext x
      simp [B0579.pd]
    have hlap : lapP (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext x
      simp [lapP, hpd]
    rw [hfun0]
    unfold vtvR flowIntegrand
    simp [hpd, hlap]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
