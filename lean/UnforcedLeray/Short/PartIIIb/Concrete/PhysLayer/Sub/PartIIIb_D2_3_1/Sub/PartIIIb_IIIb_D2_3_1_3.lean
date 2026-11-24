import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

/-!
# Decomposition of `OutPrimStream` (`PartIII-b:IIIb-D2/3/1/3`)

Source of record: `the November 2 reference manuscript` 4175-4186.  The outward
primitive `Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,z) dρ` is a stream function of `Z` once (i) the integrals
converge locally uniformly in `z` together with their `z`-derivative (decay of the separated
kernels, 4177-4179), and (ii) `ρ Z_r → 0` at infinity; `∂_rΨ = r Z_z` is the fundamental theorem
of calculus, `∂_zΨ = -r Z_r` follows from `div Z = 0` in cylindrical form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Decay of the field** `Z` at infinity on the half plane (source 4177-4179), at phase `τ`, for
the receiver region `ϱ > R√(5ν/6)`: for each `r` in the region and `z` there is an integrable
majorant `B` on `(r,∞)` of `ρ Z_z(ρ,0,z')` and of its `z`-derivative `ρ ∂_zZ_z(ρ,0,z')` for `z'` in
the unit ball about `z`, and `ρ Z_r(ρ,0,z) → 0` as `ρ → ∞`. -/
def StreamDecay (ν R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ) : Prop :=
  ∀ r z : ℝ, R * Real.sqrt (5 * ν / 6) < r →
    (∃ B : ℝ → ℝ, IntegrableOn B (Ioi r) ∧
      ∀ ρ ∈ Ioi r, ∀ z' ∈ Metric.ball z 1,
        ‖ρ * Z τ !₂[ρ, 0, z'] 2‖ ≤ B ρ ∧
          ‖ρ * fderiv ℝ (Z τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤ B ρ) ∧
    Tendsto (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 0) atTop (nhds 0)

/-- **Source fact (decay for `X₀`)** (source 4177-4179, from `SepKernelBounds`
`|D^jW| ≤ C r^{-4-j+3/b}` for old sources in `Y₂ = L²_τL²` (4155-4156; the actual thin `N₁` and
repair `L²_τL^{22/19}` sources of 4156-4158 are special cases), supported in the old cylinder): the
Ward field `X₀` satisfies `StreamDecay` on the young region, for `c, ρ_b > 0`, `m_Z ≥ 0` (`Defs.lean`,
*Parameters*). -/
def WardX0Decay (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      ∀ τ, StreamDecay ν ε⁻¹ (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ

/-- **Generic `r`-derivative** (source 4178, fundamental theorem of calculus): for `Z` that is `C²`
on the young region with `StreamDecay`, `∂_rΨ_Z = r Z_z`. -/
def OutPrimDerivR : Prop :=
  ∀ (ν R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ),
    ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) → StreamDecay ν R Z τ →
    ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim Z τ r' z) (r * Z τ !₂[r, 0, z] 2) r

/-- **Generic `z`-derivative** (source 4178-4179): for `Z` that is `C²`, divergence free and
axisymmetric swirl-free on the young region with `StreamDecay`, `∂_zΨ_Z = -r Z_r`
(`∂_ρ(ρ Z_r) + ρ ∂_z Z_z = 0`, differentiation under the integral, vanishing of `ρ Z_r` at ∞). -/
def OutPrimDerivZ : Prop :=
  ∀ (ν R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ),
    ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) →
    (∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0) →
    AxiNoSwirlOn (youngOpen ν R) Z → StreamDecay ν R Z τ →
    ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun z' => outPrim Z τ r z') (-(r * Z τ !₂[r, 0, z] 0)) z

/-- `OutPrimStream` from the smoothness/structure of `X₀`, its decay, and the two generic
derivative statements. -/
theorem outPrimStream_of_aux (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (h1 : WardX0Smooth c mZ ρb γ ν ε μ hχo) (h2 : WardX0Structure c mZ ρb γ ν ε μ hχo)
    (hD : WardX0Decay c mZ ρb γ ν ε μ hχo) (hR : OutPrimDerivR) (hZ : OutPrimDerivZ) :
    OutPrimStream c mZ ρb γ ν ε μ hχo := by
  intro hc hρ hm hν hε hμ T g₁ g₂ e₁ e₂ τ r z hr
  have a1 := h1 hc hρ hm hν hε hμ T g₁ g₂ e₁ e₂ τ
  obtain ⟨a2, -, a4⟩ := h2 hc hρ hm hν hε hμ T g₁ g₂ e₁ e₂
  have a3 := hD hc hρ hm hν hε hμ T g₁ g₂ e₁ e₂ τ
  exact ⟨hR ν ε⁻¹ _ τ a1 a3 r z hr, hZ ν ε⁻¹ _ τ a1 (a2 τ) a4 a3 r z hr⟩

end UnforcedLeray.Short.PartIIIb.Concrete
