import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique

/-!
# Proof of `FcvDuhamelDatum` (source 2819-2836, 4464-4467)

For `g = gBD D B t` (real) and `t ≤ s`, the weak identity of `IIIa.IsLinearisedFlow` gives
`⟨𝒰(s,t)g, φ⟩ = ⟨g, φ⟩ + ∫_t^s ℓ_ρ(𝒰(ρ,t)g) dρ`.  The velocity `u ρ` of the flow is the
Biot-Savart velocity of `𝒰(ρ,t)g` (real by `TrainEvolution.real`), hence equal a.e. to `K_c` of it
(`IIIa.CTE.isBiotSavart_unique`, `isBiotSavart_kc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fcvDuhamelDatum : FcvDuhamelDatum := by
  unfold FcvDuhamelDatum
  intro κ ν c m hm hc tr D B φ hφ t ht s hts
  obtain ⟨u, hu⟩ := D.ev.flow t ht.le (gBD D B t)
  have hreal : ∀ r, conjX (D.ev.U r t (gBD D B t)) = D.ev.U r t (gBD D B t) := by
    intro r
    rw [D.ev.real r t (gBD D B t), gBD_real D B t]
  have hu_eq : ∀ r, t ≤ r → ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      u r x = kcC (D.ev.U r t (gBD D B t)) x := by
    intro r hr
    have h1 := hu.biotSavart r hr
    have h2 := isBiotSavart_kc (hreal r)
    exact IIIa.CTE.isBiotSavart_unique c hc.out _ (u r) _ h1 h2
  have I_eq : ∀ r, t ≤ r →
      (∫ x in B0579.cell c, IIIa.flowIntegrand tr (xFn (D.ev.U r t (gBD D B t))) (u r) r φ x) =
        ellFn tr φ r (D.ev.U r t (gBD D B t)) := by
    intro r hr
    unfold ellFn
    refine integral_congr_ae ?_
    filter_upwards [hu_eq r hr] with x hx
    unfold IIIa.flowIntegrand
    rw [congrFun hx 0, congrFun hx 1]
  have hI : IntegrableOn (fun ρ : ℝ => ellFn tr φ ρ (D.ev.U ρ t (gBD D B t))) (Ioc t s) := by
    have h0 := hu.timeIntegrable φ hφ s hts
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hts] at h0
    exact h0.congr_fun (fun r hr => I_eq r hr.1.le) measurableSet_Ioc
  refine ⟨hI, ?_⟩
  have hw := hu.weak φ hφ s hts
  rw [intervalIntegral.integral_of_le hts,
    setIntegral_congr_fun measurableSet_Ioc (fun r hr => I_eq r hr.1.le)] at hw
  exact hw

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
