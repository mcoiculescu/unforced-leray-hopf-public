import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks

/-!
# `PartIII-b:C/asrc/ra/9/1/2/8` : `GeoGPointwise` from the `Dc Θ` and `ringRem` bounds

Source of record: `the November 2 reference manuscript`, lines 5034-5039, 4979-4980.
`G = Dc ν μ Θ + ringRem ν ε b`; each piece is dominated by the conormal words of `h^p_A, ψ^p_A`
by the product rule (weights `1+s⁻¹` from `∂_s = s⁻¹ (s∂_s)`, `(1+|η|)³` from at most three `𝒦`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Bound of `(∂_s + μ/s - νΔ_{q,η}) Θ` (source 5034-5039): `Θ = (0, ψ - 𝒦ψ)`, so
`∂_sΘ, νΔΘ` are words of length `≤ 3` on `ψ` (with `η`-weight `≤ 1+|η|`), `(μ/s)Θ` a word of length `≤ 1`. -/
def GeoDcThetaBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ (IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → ν ≤ 1 → |μ| ≤ 1 → 0 < ε → ε ≤ 1 →
    ∀ A : ℝ → Mat3, IsAffElem as A →
      ContDiffOn ℝ 4 (hpM ν χf A) (Ioi 0 ×ˢ univ) → ContDiffOn ℝ 4 (psiM ν χf A) (Ioi 0 ×ˢ univ) →
      ∀ q : Chart, 0 < q.1 →
        ‖Dc ν μ (thetaM ν χf A) q‖ ≤ C * (1 + q.1⁻¹) * (1 + |q.2.2|) ^ 3 *
          ∑ w ∈ budgetWords, (‖wordW w (hpM ν χf A) q‖ + |wordW w (psiM ν χf A) q|))

/-- Bound of `ringRem ν ε (hbM)` (source 5034-5039): `ν[2(𝒦+1)∂_q b - ε(𝒦+1)²b + ε b_r e_r]`,
`b = h^p_A + εΘ`; at most three `𝒦`'s in total, derivative order `≤ 4`. -/
def GeoRingRemBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ (IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → ν ≤ 1 → |μ| ≤ 1 → 0 < ε → ε ≤ 1 →
    ∀ A : ℝ → Mat3, IsAffElem as A →
      ContDiffOn ℝ 4 (hpM ν χf A) (Ioi 0 ×ˢ univ) → ContDiffOn ℝ 4 (psiM ν χf A) (Ioi 0 ×ˢ univ) →
      ∀ q : Chart, 0 < q.1 →
        ‖ringRem ν ε (hbM ν ε χf A) q‖ ≤ C * (1 + q.1⁻¹) * (1 + |q.2.2|) ^ 3 *
          ∑ w ∈ budgetWords, (‖wordW w (hpM ν χf A) q‖ + |wordW w (psiM ν χf A) q|))

theorem geoGPointwise_of (as : ℝ) (χf : ℝ → ℝ) (h1 : GeoDcThetaBound as χf)
    (h2 : GeoRingRemBound as χf) : GeoGPointwise as χf := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  refine ⟨C1 + C2, add_nonneg hC1 hC2, fun hχ ν μ ε hν hν1 hμ hε hε1 A hA hh hp q hq => ?_⟩
  have a := H1 hχ ν μ ε hν hν1 hμ hε hε1 A hA hh hp q hq
  have b := H2 hχ ν μ ε hν hν1 hμ hε hε1 A hA hh hp q hq
  have : geoDG ν μ ε χf A q = Dc ν μ (thetaM ν χf A) q + ringRem ν ε (hbM ν ε χf A) q := rfl
  rw [this]
  calc _ ≤ ‖Dc ν μ (thetaM ν χf A) q‖ + ‖ringRem ν ε (hbM ν ε χf A) q‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith [a, b]

end UnforcedLeray.Short.PartIIIb.Concrete
