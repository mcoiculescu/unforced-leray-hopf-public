import UnforcedLeray.Short.PartIIb.Sub.T12_1

/-!
# Nice case and the uniqueness step

`cylHelmholtz_of_nice`: a planar Helmholtz pair for a nice field (`CylLp c r`, `CylLp c 2`) is a
cylinder Helmholtz pair (`CylOfPlaneProps`).

`cyl_diff_ae_eq`: if `G₁, G₂, G'` are cylinder Helmholtz companions of `F₁, F₂, F₁ - F₂`, then
`G₁ - G₂ =ᵐ G'` (the difference `G₁ - G₂ - G'` is weakly divergence free, orthogonal to solenoidal
tests, and in `L^r`, so it vanishes a.e. by `CylHelmholtzUnique`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cylHelmholtz_of_nice (hCOP : CylOfPlaneProps) {c r C : ℝ} (hc : 0 < c) (hr : 1 < r)
    (hnice : ∀ F : ℝ × ℝ → CMerid, CylLp c r F → CylLp c 2 F →
      ∃ G : ℝ × ℝ → CMerid, CylLp c r G ∧ IsPlaneHelmholtz F G ∧
        eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
    (F : ℝ × ℝ → CMerid) (hF : CylLp c r F) (hF2 : CylLp c 2 F) :
    ∃ G : ℝ × ℝ → CMerid, IsCylHelmholtz c r F G ∧
      eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
  obtain ⟨G, hGL, hPH, hb⟩ := hnice F hF hF2
  exact ⟨G, hCOP c r hc hr F G hF hGL hPH, hb⟩

/-- Integral of a three-term combination `A - B - C`. -/
theorem integral_comb_sub3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B C : α → ℂ}
    (iA : Integrable A μ) (iB : Integrable B μ) (iC : Integrable C μ) :
    ∫ z, (A z - B z - C z) ∂μ = ∫ z, A z ∂μ - ∫ z, B z ∂μ - ∫ z, C z ∂μ := by
  have h1 := integral_sub (iA.sub iB) iC
  have h2 := integral_sub iA iB
  simp only [Pi.sub_apply] at h1
  rw [h1, h2]

/-- Integral of a combination `-A + B + C`. -/
theorem integral_comb_neg3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B C : α → ℂ}
    (iA : Integrable A μ) (iB : Integrable B μ) (iC : Integrable C μ) :
    ∫ z, (-A z + B z + C z) ∂μ = -∫ z, A z ∂μ + ∫ z, B z ∂μ + ∫ z, C z ∂μ := by
  have iAB : Integrable (fun z => -A z + B z) μ := iA.neg.add iB
  have h1 := integral_add iAB iC
  have h2 : ∫ z, (-A z + B z) ∂μ = ∫ z, -A z ∂μ + ∫ z, B z ∂μ := integral_add iA.neg iB
  rw [integral_neg] at h2
  rw [h1, h2]

theorem cyl_diff_ae_eq (hU : CylHelmholtzUnique) {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    {F₁ F₂ G₁ G₂ G' : ℝ × ℝ → CMerid}
    (h₁ : IsCylHelmholtz c r F₁ G₁) (h₂ : IsCylHelmholtz c r F₂ G₂)
    (h' : IsCylHelmholtz c r (F₁ - F₂) G') :
    G₁ - G₂ =ᵐ[UnforcedLeray.Cyl.avgμ c] G' := by
  have hDL : CylLp c r (G₁ - G₂ - G') := cylLp_sub (cylLp_sub h₁.1 h₂.1) h'.1
  have hD := hU c r hc hr (G₁ - G₂ - G') hDL ?_ ?_
  · filter_upwards [hD] with z hz
    have hz' : G₁ z - G₂ z - G' z = 0 := by simpa using hz
    exact sub_eq_zero.1 hz'
  · intro φ hφ
    obtain ⟨iA, eA⟩ := h₁.2.1 φ hφ
    obtain ⟨iB, eB⟩ := h₂.2.1 φ hφ
    obtain ⟨iC, eC⟩ := h'.2.1 φ hφ
    calc ∫ z, ((G₁ - G₂ - G') z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
          (G₁ - G₂ - G') z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∂(UnforcedLeray.Cyl.avgμ c)
        = ∫ z, ((G₁ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G₁ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) -
            (G₂ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G₂ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) -
            (G' z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G' z 1 * (fderiv ℝ φ z (0, 1) : ℂ)))
            ∂(UnforcedLeray.Cyl.avgμ c) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [Pi.sub_apply, PiLp.sub_apply]
          ring
      _ = (∫ z, (G₁ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G₁ z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c)) -
          (∫ z, (G₂ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G₂ z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c)) -
          (∫ z, (G' z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G' z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c)) :=
          integral_comb_sub3 iA iB iC
      _ = 0 := by rw [eA, eB, eC]; simp
  · intro Ψ hΨ
    obtain ⟨iA, eA⟩ := h₁.2.2 Ψ hΨ
    obtain ⟨iB, eB⟩ := h₂.2.2 Ψ hΨ
    obtain ⟨iC, eC⟩ := h'.2.2 Ψ hΨ
    calc ∫ z, ∑ i : Fin 2, (G₁ - G₂ - G') z i * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c)
        = ∫ z, ((-(∑ i : Fin 2, (F₁ z i - G₁ z i) * (Ψ z i : ℂ)) +
            ∑ i : Fin 2, (F₂ z i - G₂ z i) * (Ψ z i : ℂ)) +
            ∑ i : Fin 2, ((F₁ - F₂) z i - G' z i) * (Ψ z i : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [Fin.sum_univ_two, Pi.sub_apply, PiLp.sub_apply]
          ring
      _ = -(∫ z, ∑ i : Fin 2, (F₁ z i - G₁ z i) * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c)) +
          (∫ z, ∑ i : Fin 2, (F₂ z i - G₂ z i) * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c)) +
          ∫ z, ∑ i : Fin 2, ((F₁ - F₂) z i - G' z i) * (Ψ z i : ℂ)
            ∂(UnforcedLeray.Cyl.avgμ c) :=
          integral_comb_neg3 iA iB iC
      _ = 0 := by rw [eA, eB, eC]; simp

end UnforcedLeray.Short.IIb
