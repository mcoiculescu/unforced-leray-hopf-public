import UnforcedLeray.Short.PartI.Sub.PartI_C08_1
import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1_2

/-!
# `PartI:C08/1/3`: decomposition of `FullMildImpliesCoupled`

Source `the November 2 reference manuscript`
lines 1094-1125 ("Conversely every normalized solution satisfies the integrals"): the converse of
`PartI_C07_1_1_2` (`CoupledImpliesFullMild`).  The chain is reversed step by step:

1. `FullMildToBwd` (leaf): `FullMildEq` is the free backward Duhamel form with coefficient `L₀`.
2. `BwdGaugeConverse` (leaf): multiplying by the normalization `e^{λθ}θ^κ` gives the free Duhamel
   form of `W` with coefficient `canonicalFullGen`.
3. `AmplitudeConverse` (leaf): applying `ℓ` (`ℓ L₀ = λ ℓ`, `ℓ D = ⟨Dq†,·⟩`) to that form gives the
   integrated amplitude equation `A(θ) = A(s₀) + ∫ ℓ(Dr)/s`.
4. `bwdMild_sub` and `canonicalGen_algebra` (proved here) subtract the `Aq` piece (using
   `AmplitudeFreeDuhamel`) and give the free Duhamel form of `r` with the complementary coefficient.
5. `ComplementConverse` (leaf): that form, with the mild complementary evolution `U`, is the
   `r`-equation `r(θ) = S(θ,s₀)r(s₀) + ∫ S(θ,s) y A(s)/s ds` (Gronwall uniqueness).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

/-- **Leaf 1** (source 1117-1119, converse of `fullMildEq_of_bwdMild`): for `b > 0` and `V`
continuous on `[b,∞)`, `FullMildEq b V` is the backward Duhamel form `BwdMild b (fun _ => L₀) 0 V`.
Sketch: reverse the change of variables `u = -σ` (`intervalIntegral.integral_comp_neg`, as in
`fullMildEq_of_bwdMild`); integrability from `Short.Spine.CanonicalMild.intervalIntegrable_expD_log`
and continuity of `V`, `L₀`. -/
def FullMildToBwd : Prop :=
  ∀ (b : ℝ) (V : ℝ → B0010.XG), 0 < b → ContinuousOn V (Ici b) → FullMildEq b V →
    BwdMild b (fun _ => Planar.L0) 0 V

/-- **Leaf 2** (line 1095, converse of `BwdGauge`; source 1094-1125): if `W` is continuous on
`[b,∞)` and `e^{-λθ}θ^{-κ}W` solves the free Duhamel form with coefficient `L₀`, then `W` solves it
with coefficient `canonicalFullGen λ κ` (`L₀ - λ - κ/σ`).  Sketch: with `c = canonicalGauge λ κ`,
`W = c⁻¹ (c W)`; differentiate `τ ↦ c(τ)⁻¹ E(θ,τ)...` exactly as in `BwdGauge` using
`hasDerivAt_canonicalGauge` (here `c⁻¹ = canonicalW`-gauge `exp(λτ + κ log τ)`), or conjugate the
whole identity: `E(θ,τ)` commutes with scalars. -/
def BwdGaugeConverse : Prop :=
  ∀ (lam κ : ℂ) (b : ℝ), 0 < b → ∀ W : ℝ → B0010.XG, ContinuousOn W (Ici b) →
    BwdMild b (fun _ => Planar.L0) 0 (fun θ => canonicalGauge lam κ θ • W θ) →
      BwdMild b (canonicalFullGen lam κ) 0 W

/-- **Leaf 3** (source 1097-1101, 1117-1119: `-A' = θ⁻¹ℓ(Dr)` in integrated form): if `W` is
continuous on `[b,∞)` and solves the free Duhamel form with coefficient `canonicalFullGen`, then
`A = ℓW` and `r = W - Aq` satisfy `A(θ) = A(s₀) + ∫_θ^{s₀} ℓ(Dr(s))/s ds`
(with `ℓ D = ⟨Dq†,·⟩ = seedLD`).  Sketch: pair the Duhamel identity with `qd ∈ 𝒟(D)`:
`ℓ(E(θ,s)w) = ⟨E(θ,s)qd, w⟩` (`D` self-adjoint, `B0123.inner_expD`), `ℓ L₀ = λ ℓ` (Riesz
projection, `IsSeedXG`), and differentiate in `θ` with `hasDerivAt_expD_logSub_domain`. -/
def AmplitudeConverse : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ W : ℝ → B0010.XG, ContinuousOn W (Ici b) →
      BwdMild b (canonicalFullGen lam (seedKappa l q hq)) 0 W →
        ∀ θ s₀ : ℝ, b ≤ θ → θ ≤ s₀ →
          l (W θ) = l (W s₀) + ∫ s in θ..s₀, seedLD qd hqd (W s - l (W s) • q) / (s : ℂ)

/-- **Leaf 4** (source 1117-1124: "uniqueness follows from the bounded coupling maps and
Gronwall", converse of `complementFreeDuhamel`): if `U` is the mild complementary evolution for
the clock `canonicalClock b` and `r` is continuous on `[b,∞)` and solves the free Duhamel form with
coefficient `canonicalCplGen` and source `A/σ · y`, then
`r(θ) = S(θ,s₀) r(s₀) + ∫_θ^{s₀} (A(s)/s) S(θ,s) y ds`, `S = canonicalS U`.
Sketch: `S(θ,s)x` also solves the free Duhamel form (`complementFreeDuhamel` for `y = 0`); the
difference of `r` and the Duhamel-variation expression solves the homogeneous form with zero final
data, so vanishes by Gronwall (`B_β` bounded: `norm_canonicalCplGen_le`). -/
def ComplementConverse : Prop :=
  ∀ (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG) (Rf : B0010.XG →L[ℂ] B0010.XG)
    (b : ℝ), 0 < b →
    ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG,
      IsMildComplementEvolution lam κ l q Rf (canonicalClock b) U →
      ∀ (y : B0010.XG) (A : ℝ → ℂ) (r : ℝ → B0010.XG), ContinuousOn A (Ici b) →
        ContinuousOn r (Ici b) →
        BwdMild b (fun σ => canonicalCplGen lam κ l q Rf b (-σ)) (fun σ => (A σ / σ) • y) r →
          ∀ θ s₀ : ℝ, b ≤ θ → θ ≤ s₀ →
            r θ = canonicalS U θ s₀ (r s₀) + ∫ s in θ..s₀, (A s / s) • canonicalS U θ s y

/-- **Subtraction** of backward Duhamel forms whose integrands subtract. -/
theorem bwdMild_sub {b : ℝ} {K K₁ K₂ : ℝ → B0010.XG →L[ℂ] B0010.XG}
    {g g₁ g₂ X X₁ X₂ : ℝ → B0010.XG}
    (h : BwdMild b K g X) (h₁ : BwdMild b K₁ g₁ X₁)
    (hX : ∀ θ, b ≤ θ → X₂ θ = X θ - X₁ θ)
    (hK : ∀ σ, b ≤ σ → K₂ σ (X₂ σ) + g₂ σ = (K σ (X σ) + g σ) - (K₁ σ (X₁ σ) + g₁ σ)) :
    BwdMild b K₂ g₂ X₂ := by
  intro θ s₀ hθ hθs
  obtain ⟨i₁, e₁⟩ := h θ s₀ hθ hθs
  obtain ⟨i₂, e₂⟩ := h₁ θ s₀ hθ hθs
  have hEq : EqOn (fun σ => B0123.expD (Real.log σ - Real.log θ) (K₂ σ (X₂ σ) + g₂ σ))
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (K σ (X σ) + g σ) -
        B0123.expD (Real.log σ - Real.log θ) (K₁ σ (X₁ σ) + g₁ σ)) (uIcc θ s₀) := by
    intro σ hσ
    rw [uIcc_of_le hθs] at hσ
    simp only [hK σ (hθ.trans hσ.1), map_sub]
  refine ⟨(intervalIntegrable_congr (hEq.mono uIoc_subset_uIcc)).mpr (i₁.sub i₂), ?_⟩
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_sub i₁ i₂, hX θ hθ,
    hX s₀ (hθ.trans hθs), map_sub, e₁, e₂]
  abel

/-- **`FullMildImpliesCoupled` from the four leaves** (lines 1094-1125). -/
theorem fullMildImpliesCoupled_of (h1 : FullMildToBwd) (h2 : BwdGaugeConverse)
    (h3 : AmplitudeConverse) (h4 : ComplementConverse) (hAmp : AmplitudeFreeDuhamel) :
    FullMildImpliesCoupled := by
  intro lam q l hI qd hl hq hqd b hb U hU V hVc hFM
  have hWc := continuousOn_canonicalW hb lam (seedKappa l q hq) hVc
  have hAc : ContinuousOn (fun θ => l (canonicalW lam (seedKappa l q hq) V θ)) (Ici b) :=
    l.continuous.comp_continuousOn hWc
  have hrc : ContinuousOn (fun θ => canonicalW lam (seedKappa l q hq) V θ -
      l (canonicalW lam (seedKappa l q hq) V θ) • q) (Ici b) :=
    hWc.sub (hAc.smul continuousOn_const)
  have hV1 := h1 b V hb hVc hFM
  have hV2 : BwdMild b (fun _ => Planar.L0) 0
      (fun θ => canonicalGauge lam (seedKappa l q hq) θ •
        canonicalW lam (seedKappa l q hq) V θ) :=
    bwdMild_congr hV1 fun θ hθ =>
      (canonicalGauge_smul_canonicalW lam (seedKappa l q hq) V (hb.trans_le hθ)).symm
  have hW := h2 lam (seedKappa l q hq) b hb _ hWc hV2
  have hAeq := h3 lam q l hI qd hl hq hqd b hb _ hWc hW
  have hfc : ContinuousOn (fun σ : ℝ => seedLD qd hqd (canonicalW lam (seedKappa l q hq) V σ -
      l (canonicalW lam (seedKappa l q hq) V σ) • q) / (σ : ℂ)) (Ici b) :=
    ((seedLD qd hqd).continuous.comp_continuousOn hrc).div
      Complex.continuous_ofReal.continuousOn
      fun σ hσ => Complex.ofReal_ne_zero.mpr (hb.trans_le hσ).ne'
  have hAm := hAmp q hq b hb _ _ hAc hfc hAeq
  have hR : BwdMild b (fun σ => canonicalCplGen lam (seedKappa l q hq) l q
      (seedRf l q qd hq hqd) b (-σ)) (fun σ => (l (canonicalW lam (seedKappa l q hq) V σ) / σ) •
        seedQDq l q hq) (fun θ => canonicalW lam (seedKappa l q hq) V θ -
          l (canonicalW lam (seedKappa l q hq) V θ) • q) := by
    refine bwdMild_sub hW hAm (fun θ _ => rfl) fun σ hσ => ?_
    simp only [Pi.zero_apply, add_zero, ContinuousLinearMap.zero_apply, zero_add]
    rw [canonicalGen_algebra hI hq hqd hσ _]
    abel
  exact fun θ s₀ hθ hθs => ⟨h4 lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) b hb U hU
    (seedQDq l q hq) _ _ hAc hrc hR θ s₀ hθ hθs, hAeq θ s₀ hθ hθs⟩

end UnforcedLeray.Short.PartI
