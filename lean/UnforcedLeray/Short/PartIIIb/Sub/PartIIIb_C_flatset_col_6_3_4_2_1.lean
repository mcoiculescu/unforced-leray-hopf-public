import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvDerivCyl

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/1` (`vtvFubiniMeas`): decomposition

Source of record: `the November 2 reference manuscript`
(line 4610: the integrated Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`, `R(r,φ) = r^μ(⟨g,φ⟩ +
∫flowIntegrand)`).

The raw `ω` and `g` are only measurable in `x` for each age, so `R(r,φ)` is rewritten through `f`
(curl clause of `VtvHyps`, an exact identity for every `r > 0`) and through `b` (Biot-Savart clause
`⟨ω,ψ⟩ = ∫ b·∇^⊥ψ`, applied to the cylinder test `ψ = νΔφ + v·∇φ`):

* `VtvFlowRep`: `∫ flowIntegrand = ∫ vtvFlowRHS` for every `r > 0` and cylinder test `φ`.
* `VtvKfMeas`, `VtvKflowMeas`: the two cell integrands are jointly a.e. strongly measurable in
  `((s,r),x)` for the stream test `η` (`f` is `L²` on every age band, `b` is measurable, the train
  is smooth, `∂_sη` and its derivatives are jointly continuous).
* Assembly (`vtvFubiniMeas_of`): `integral_prod_right'`, the indicator `{r ≤ s}` and `r^μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (flowIntegrand lapP)

/-- The `b`-form of the flow integrand (source 4610): with `ψ = νΔφ + v·∇φ`,
`b₀∂_ηψ - b₁∂_qψ - (b·∇E)φ`. -/
def vtvFlowRHS {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (b : Chart → Fin 2 → ℂ)
    (r : ℝ) (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  b (r, x) 0 * (B0579.pd 1 (fun y => ν * lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)) x : ℂ) -
    b (r, x) 1 * (B0579.pd 0 (fun y => ν * lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)) x : ℂ) -
    (b (r, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
      b (r, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)

/-- The `f`-form of `⟨g(r),φ_s⟩` (curl clause), as a function of `((s,r),x)`. -/
def vtvKf (f : Chart → Fin 2 → ℂ) (φs : ℝ → ℝ × ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ × ℝ) : ℂ :=
  f (p.2, x) 0 * (B0579.pd 1 (φs p.1) x : ℂ) - f (p.2, x) 1 * (B0579.pd 0 (φs p.1) x : ℂ)

/-- The flow kernel as a function of `((s,r),x)`. -/
def vtvKflow {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (b : Chart → Fin 2 → ℂ)
    (φs : ℝ → ℝ × ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ × ℝ) : ℂ :=
  vtvFlowRHS tr b p.2 (φs p.1) x

/-- **Flow representation** (source 4610): for `r > 0` and a cylinder test `φ`,
`ψ = νΔφ + v·∇φ` is a cylinder test (`v` smooth, `c`-periodic, bounded derivatives; `∇φ` band
supported), so `⟨ω(r),ψ⟩ = ∫ b(r)·∇^⊥ψ` (third clause of `IsBiotSavart`); `ω ψ` and
`(b·∇E)φ` are integrable on the cell (`VtvHyps` last clause; `b ∈ L²`, `∇E` bounded, `φ` band
supported), hence `∫ flowIntegrand = ∫ vtvFlowRHS`. -/
def VtvFlowRep : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ r : ℝ, 0 < r → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
      ∫ x in B0579.cell c, flowIntegrand tr (ω r) (fun x => b (r, x)) r φ x =
        ∫ x in B0579.cell c, vtvFlowRHS tr b r φ x

/-- **Joint measurability of the `f`-kernel** (source 4610): `f` is `L²` on every `[s₁,s₂]×cell`,
`s₁ > 0` (clause 6 of `VtvHyps`), hence a.e. strongly measurable on `(0,∞)×cell` (countable union
of bands); `(s,x) ↦ pd j (∂_sη(s)) x` is jointly continuous (joint smoothness of `η`). -/
def VtvKfMeas : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      AEStronglyMeasurable
        (fun q : (ℝ × ℝ) × (ℝ × ℝ) => vtvKf f (fun s x => deriv (fun s' => η s' x) s) q.1 q.2)
        (((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
          (volume.restrict (B0579.cell c)))

/-- **Joint measurability of the flow kernel**: `b` is measurable (`IsEnergyField.measurable`);
`(r,x) ↦ tr.v r x i` and `(r,x) ↦ pd j (Ec tr r) x` are jointly continuous (smooth train; the
`Ec`-derivative is a `v`-derivative); `(s,x) ↦ φ_s x`, `pd j φ_s x`, `pd j (pd k φ_s) x` are jointly
continuous (joint smoothness of `η`). -/
def VtvKflowMeas : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      AEStronglyMeasurable
        (fun q : (ℝ × ℝ) × (ℝ × ℝ) => vtvKflow tr b (fun s x => deriv (fun s' => η s' x) s) q.1 q.2)
        (((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
          (volume.restrict (B0579.cell c)))

theorem vtvFubiniMeas_of (hR : VtvFlowRep) (hF : VtvKfMeas) (hW : VtvKflowMeas) :
    VtvFubiniMeas := by
  intro ν c μ tr ω g b G f H η hη
  set φs : ℝ → ℝ × ℝ → ℝ := fun s x => deriv (fun s' => η s' x) s with hφs
  have hcyl : ∀ s, B0579.IsCylTest c (φs s) := fun s => vtvDerivCyl c η hη s
  have hI1 := (hF ν c μ tr ω g b G f H η hη).integral_prod_right'
  have hI2 := (hW ν c μ tr ω g b G f H η hη).integral_prod_right'
  have hrμ : Measurable (fun p : ℝ × ℝ => ((p.2 : ℂ)) ^ (μ : ℂ)) :=
    (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  have hG : AEStronglyMeasurable
      ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p : ℝ × ℝ => ((p.2 : ℂ)) ^ (μ : ℂ) *
        ((∫ x in B0579.cell c, vtvKf f φs p x) + ∫ x in B0579.cell c, vtvKflow tr b φs p x)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (hrμ.aestronglyMeasurable.mul (hI1.add hI2)).indicator hset
  refine hG.congr ?_
  rw [Measure.prod_restrict]
  have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)), p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
    ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  filter_upwards [hmem] with p hp
  have hs : 0 < p.1 := hp.1
  have hr : 0 < p.2 := hp.2
  by_cases hle : p.2 ≤ p.1
  · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from hle), if_pos hle]
    show _ = _
    simp only [vtvR]
    congr 1
    rw [hR ν c μ tr ω g b G f H p.2 hr (φs p.1) (hcyl p.1)]
    have hcurl := H.2.2.2.2.2.2.1 p.2 hr (φs p.1) (hcyl p.1)
    rw [hcurl]
    rfl
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 ≤ p.1} from hle), if_neg hle]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
