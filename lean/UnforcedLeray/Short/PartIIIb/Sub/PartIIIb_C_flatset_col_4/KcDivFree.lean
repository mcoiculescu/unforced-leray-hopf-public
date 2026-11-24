import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4

/-!
# `KcDivFree` (leaf 2 of `PartIII-b:C/flatset/col/4`)

Source of record `the November 2 reference manuscript` 3236-3240 (`K_c = grad-perp
Delta^{-1}` is divergence free).  The div clause of `IsBiotSavart` for `K_c xi` holds for every
`xi` (no reality assumption is needed: the Biot-Savart velocity of the real part `reX xi`), by the
same route as `isBiotSavart_kc` in `Setting.lean`, with the reality hypothesis dropped.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution (realPartVelocityCLM
  realPartVelocityCLM_apply coeFn_realPartVelocityLp)

/-- `K_c ξ` is the Biot-Savart velocity of the real part `reX ξ` for every `ξ ∈ X_{m,c}`
(the proof of `isBiotSavart_kc` without its reality hypothesis). -/
theorem kcBS_any {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    IIIa.IsBiotSavart c (fun x => ((reX ξ.1 x : ℝ) : ℂ)) (kcC ξ) := by
  have h0 := IIIa.BSAux.isBS_re (IIIa.CTE.velocityIsBiotSavart_one c m one_le_of_fact
    (reX ξ.1) (reX_circ ξ))
  exact IIIa.BSAux.isBS_congr (v := kcC ξ) h0 (fun j => by
    filter_upwards [coeFn_realPartVelocityLp (UnforcedLeray.B0583.velocity c one_le_of_fact
      (reX ξ.1) (reX_circ ξ)), kcMer_ae ξ] with x hx hk
    have e : kcC ξ x j = ((kcMer ξ x j : ℝ) : ℂ) := rfl
    rw [e, hk]
    have e2 : (kcLp ξ : ℝ × ℝ → Merid) x = realPartVelocityCLM
        ((UnforcedLeray.B0583.velocity c one_le_of_fact (reX ξ.1) (reX_circ ξ) :
          ℝ × ℝ → UnforcedLeray.B0581.Vel) x) := hx
    rw [e2, realPartVelocityCLM_apply])

/-- **(2) `K_cξ(s)` is divergence free** (source 3236-3240). -/
theorem kcDivFree : KcDivFree := by
  unfold KcDivFree
  intro c m _ _ ξ _ s _ ψ hψ
  exact (kcBS_any (ξ s)).2.1 ψ hψ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
