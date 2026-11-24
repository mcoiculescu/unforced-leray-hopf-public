import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2

/-!
# `PartII-b:T10/2/1` (`ProfileMeasOfLift`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1902-1906.

The azimuth-0 section `Ψ(z, θ)` of the chart `(τ, y) ↦ (s, ξ, η)` over a chart point `z = (s, ξ, η)`
with `s > 0` is `y = (ϱ cos θ, ϱ sin θ, η ϱ / R)`, `ϱ = R/√s`, `τ = 2ξ/R + log s`; the chart does not
see the azimuth `θ`.  Measurability of `b ∘ chart` on `ℝ × ℝ³` (from `N_v b ∈ Y_r`) transports to
`(z, θ) ↦ b z` through `Ψ` (a quasi-measure-preserving map), and the azimuth is integrated out.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-- The azimuth-`θ` point of the ring over the chart point `z = (s, ξ, η)`:
`(ϱ cos θ, ϱ sin θ, η ϱ / R)`, `ϱ = R / √s`. -/
def psiSpace (R : ℝ) (z : Coord) (θ : ℝ) : Space :=
  !₂[R / Real.sqrt z.1 * Real.cos θ, R / Real.sqrt z.1 * Real.sin θ,
    z.2.2 * (R / Real.sqrt z.1) / R]

/-- The phase time `τ = 2ξ/R + log s` of the section over `z`. -/
def psiTau (R : ℝ) (z : Coord) : ℝ := 2 * z.2.1 / R + Real.log z.1

/-- **`T10/2/1/1`** (SP 1902-1906): the section lands on `z`:
`chart R (psiTau R z) (psiSpace R z θ) = z` for `s > 0` (`age = R²/ϱ² = s`, `trans = R y₃/ϱ = η`,
`phase = Rτ/2 - (R/2) log s = ξ`). -/
def ChartSectionEq : Prop :=
  ∀ (R : ℝ) (z : Coord) (θ : ℝ), 0 < R → 0 < z.1 →
    Axi.chart R (psiTau R z) (psiSpace R z θ) = z

/-- **`T10/2/1/2`** (SP 1902-1906): if `N_v b` is a.e. strongly measurable on `ℝ × ℝ³` then so is
`b ∘ chart`.  Route: `N_v b = √s (b_r e_r + b_z e_z)(chart)` with `s > 0` off the axis; recover the
components of `b ∘ chart` as `⟪N_v b, frame⟫ / √s` (`Axi.measurable_eR`, `Axi.merChart`,
`Axi.age_pos`, `Axi.ae_not_mem_axis`) for real and imaginary parts. -/
def ChartCompAesm : Prop :=
  ∀ (R : ℝ) (b : CProf), 0 < R → AEStronglyMeasurable (NvC R b) volume →
    AEStronglyMeasurable (fun x : ℝ × Space => b (Axi.chart R x.1 x.2)) volume

/-- **`T10/2/1/3`** (SP 1902-1906): `(z, θ) ↦ (psiTau R z, psiSpace R z θ)` is quasi measure
preserving from `hMeas c r ⊗ dθ|_{(0,2π)}` to `volume` on `ℝ × ℝ³`.  Route: `hMeas ≪ volume` and
carried by `s > 0` (`ageμ_ae_pos`, `ageμ_ac_volume`); on `s > 0`, `θ ∈ (0, 2π)` the map is smooth,
injective, with smooth inverse `(τ, y) ↦ (chart R τ y, azimuth y)` between open sets of `ℝ⁴`, so
preimages of Lebesgue-null sets are null
(`Measure.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). -/
def PsiQMP : Prop :=
  ∀ (c r R : ℝ), 0 < R → 0 < c →
    Measure.QuasiMeasurePreserving (fun p : Coord × ℝ => (psiTau R p.1, psiSpace R p.1 p.2))
      ((hMeas c r).prod (volume.restrict (Ioo 0 (2 * Real.pi)))) volume

/-- **`ProfileMeasOfLift` from the three chart facts.** -/
theorem profileMeasOfLift_of (h1 : ChartSectionEq) (h2 : ChartCompAesm) (h3 : PsiQMP) :
    ProfileMeasOfLift := by
  intro c ε r b hc hε hr hY
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hfun := h2 ε⁻¹ b hR hY.meas
  set ν : Measure ℝ := volume.restrict (Ioo 0 (2 * Real.pi)) with hν
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ]
    simp [ENNReal.mul_lt_top]⟩
  have hcomp := hfun.comp_quasiMeasurePreserving (h3 c r ε⁻¹ hR hc)
  have hpos : ∀ᵐ p : Coord × ℝ ∂((hMeas c r).prod ν), 0 < p.1.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := hMeas c r) (ν := ν)).ae
      (ageμ_ae_pos c (r / 2 - 5 / 2))
  have hcongr : (fun p : Coord × ℝ => b p.1) =ᵐ[(hMeas c r).prod ν]
      ((fun x : ℝ × Space => b (Axi.chart ε⁻¹ x.1 x.2)) ∘
        fun p : Coord × ℝ => (psiTau ε⁻¹ p.1, psiSpace ε⁻¹ p.1 p.2)) := by
    filter_upwards [hpos] with p hp
    simp only [Function.comp]
    rw [h1 ε⁻¹ p.1 p.2 hR hp]
  have hb1 : AEStronglyMeasurable (fun p : Coord × ℝ => b p.1) ((hMeas c r).prod ν) :=
    hcomp.congr hcongr.symm
  have hint := hb1.integral_prod_right'
  have hconst : (fun z : Coord => ∫ θ, b z ∂ν) = fun z => ν.real univ • b z := by
    funext z; simp [integral_const]
  simp only at hint
  rw [hconst] at hint
  have hne : ν.real univ ≠ 0 := by
    rw [hν, Measure.real, Measure.restrict_apply_univ]
    simp [ENNReal.toReal_ofReal Real.pi_pos.le, Real.pi_pos.ne']
  have := hint.const_smul (ν.real univ)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp [smul_smul, inv_mul_cancel₀ hne]

end UnforcedLeray.Short.IIb
