import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly

/-!
# `BodyColumnFlat` from four source facts (decomposition of `PartIII-b:C/flatset/col/7`)

Source of record `the November 2 reference manuscript`: 1650-1656
(`A₀ = -S + νsΔ`, `T₀ = (μ - A₀)⁻¹P₀`), 1684-1689 (the flat equation, coercive pairing with
`s^{-1/2}b̄`, constant `Re μ + 1/4`), and `Units/B0225.lean` (`R0_Ms_ae`, `R0_apply`, `R0_ae_eq`).

The free body column `R₀h` is produced in two steps.  `BodyColumnEnergy` gives a representative in
the energy class with `divFree`, `weakGrad` only for almost every age; `EnergyNullModification`
removes the null set of ages; `BodyColumnWeak` is the tested equation for `R₀h` itself, and
`forcedIntegrand_congr_ae` transports it to the modified representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest vnorm2 tnorm2 HasWeakCellDerivC)

/-- The energy class of `IsEnergyField` with `divFree`, `weakGrad` required only for almost every
age `s` (the class closed under `L²` limits; compare `IIIa.IsCausalEnergySolutionAE`). -/
structure IsEnergyFieldAE (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  zeroEntrance : ∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
    ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤
  divFreeAE : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGradAE : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)

/-- **Null-set redefinition of the energy class** (source 3426-3430, as `IIIa.CausalNullModification`
`Short/PartIII-a/Sub/T18_2.lean`, but keeping the field a.e.-equal).  Let `N` be a measurable
null set of ages containing the bad ages of `divFreeAE`, `weakGradAE`
(`exists_measurable_superset_of_null`); put `b' p = 0`, `G' p = 0` for `p.1 ∈ N`, and `(b', G') = (b, G)`
otherwise.  The zero slice is divergence free with weak gradient `0`; `{p | p.1 ∈ N}` is null for
`ageμ c (-3/2)` (it is the product of a null set with the cell measure), so `b' = b` a.e. and the
`lintegral` clauses (`energyLoc`, `zeroEntrance`) are unchanged; measurability is preserved. -/
def EnergyNullModification : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    IsEnergyFieldAE c b G →
      ∃ (b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
        b' =ᵐ[ageμ c (-3 / 2)] b ∧ IsEnergyField c b' G'

/-- **The free body column lies in the energy class** (source 1684-1689: "Pairing it with
`s^{-1/2}b̄` gives the coercive constant `Re μ + 1/4`"; 3426-3430).  If `R0` is the real form of
`T0flat = B0225.R0 ∘ P₀` (`IsBodyTransport`) and `h = s f` a.e., then `R0 h` has a representative
`b` with a weak gradient `G`, measurable, locally of finite energy, with finite `𝓗`-energy near
age `0`, and with `divFree`, `weakGrad` for a.e. age.  Route: approximate `h` in `H` by smooth
compactly supported forces `h_k` for which `b_k = R0 h_k` is classical (`B0225.R0_Ms_ae`:
`R₀(μ)M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ)dσ`), use
`(Re μ + 1/4)‖b_k‖²_H + ν‖∇b_k‖²_{H_T} ≤ ‖h_k‖_H‖b_k‖_H` (pair with `s^{-1/2}b̄_k`) to get a
Cauchy sequence in `H_T`; the limit gradient `G ∈ L²(s^{-1/2})` and an a.e. subsequence give
`divFreeAE`, `weakGradAE`; `zeroEntrance` from `b ∈ H`. -/
def BodyColumnEnergy : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ R0 : Hsp c →L[ℝ] Hsp c,
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) →
    ∀ (h : Hsp c) (f : Chart → Fin 2 → ℂ),
      (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i) →
      ∃ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 h) ∧ IsEnergyFieldAE c b G

/-- **The weak equation of the free body column** (source 1650-1656, 1684-1689; `B0225.R0_Ms_ae`,
`R0_apply`, `R0_ae_eq`): with `h' = merC ∘ h ∘ NearInst.cellPt c`, `NearInst.IsBodyTransport` gives
`T0flat hc ν μ h' = B0225.R0 (PepsC 0 c h')`; for a divergence-free test `Φ` and `ζ = Φ` in the
complex chart, `⟨R₀(μ)P₀h', (μ - A₀*)ζ⟩_H = ⟨P₀h', ζ⟩_H = ⟨h', ζ⟩_H` (`PepsC 0 c` is the orthogonal
projection onto `solenoidalHC 0 c`, and `s^{1/2}Φ(s)` is orthogonal to the gradients `cgrad 0`
of profile tests); unwinding the weights (`H` has `s^{-3/2}ds`) and `h = s f` this is
`∫∫ forcedIntegrand ν μ 0 f (velC (R0 h)) Φ = 0`.  The identity itself is the Laplace transform of
`d/dt ⟨T₀(t)f, ζ⟩ = ⟨T₀(t)f, A₀*ζ⟩` for the explicit semigroup (`B0224.T0_apply_ae`). -/
def BodyColumnWeak : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → ∀ R0 : Hsp c →L[ℝ] Hsp c,
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) →
    ∀ (h : Hsp c) (f : Chart → Fin 2 → ℂ),
      (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i) →
      ∀ Φ, IsFlatTest c Φ →
        IntegrableOn (forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC (R0 h)) Φ)
            (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
            forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC (R0 h)) Φ p = 0

/-- The forced integrand depends only on the a.e. class of `b`. -/
theorem forcedIntegrand_congr_ae {c ν : ℝ} (hc : 0 < c) {μ : ℂ}
    {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ} {f b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (h : b =ᵐ[ageμ c (-3 / 2)] b') :
    forcedIntegrand ν μ vel f b Φ =ᵐ[(volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ B0579.cell c)] forcedIntegrand ν μ vel f b' Φ := by
  have h' := (volCyl_ac_ageμ hc (-3 / 2)).ae_le h
  filter_upwards [h'] with p hp
  unfold forcedIntegrand IIIa.flatIntegrand
  rw [hp]

/-- **`BodyColumnFlat`** from the energy class, the null-set redefinition and the weak equation. -/
theorem bodyColumnFlat_of (hE : BodyColumnEnergy) (hN : EnergyNullModification)
    (hW : BodyColumnWeak) : BodyColumnFlat := by
  intro c ν μ hc hν hμ R0 hR h f hhf
  obtain ⟨b₁, G₁, hb₁, hE₁⟩ := hE c ν μ hc hν hμ R0 hR h f hhf
  obtain ⟨b', G', hb', hE'⟩ := hN c hc b₁ G₁ hE₁
  have hbb : b' =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 h) := hb'.trans hb₁
  refine ⟨b', G', hbb, { toIsEnergyField := hE', integrable := ?_, weak := ?_ }⟩
  · intro Φ hΦ
    have := (hW c ν μ hc hν hμ R0 hR h f hhf Φ hΦ).1
    exact this.congr (forcedIntegrand_congr_ae hc Φ hbb.symm)
  · intro Φ hΦ
    have := (hW c ν μ hc hν hμ R0 hR h f hhf Φ hΦ).2
    rw [← this]
    exact integral_congr_ae (forcedIntegrand_congr_ae hc Φ hbb)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
