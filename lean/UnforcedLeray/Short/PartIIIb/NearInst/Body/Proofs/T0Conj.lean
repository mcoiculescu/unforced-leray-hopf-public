import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# `T0Conj` (source 1655-1656, 1686-1689)

The flat cylinder semigroup is `T_0(t) = H_{θ_t} ∘ D_{e^{-t}}` (`B0224.T0`): the age dilation
`D_a F(s, q, η) = F(a s, q, η)` and the fibrewise plane heat operator `H_θ` with a real kernel.
Both commute with componentwise conjugation:

* `dil` is composition with a map of the domain (pointwise `dil a (conj F) = conj (dil a F)`);
* `fiberHeat` is a Gaussian average over the fibres with a real kernel, or the identity; the
  componentwise conjugation commutes with the Bochner integral by
  `LinearIsometry.integral_comp_comm`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst
open UnforcedLeray.B0220 (HSpace measureH Profile cell)
open UnforcedLeray.B0224 (dilH heatH fiberHeat planeHeat dil planeι coeFn_dilH coeFn_heatH
  fiberHeat_congr_ae dil_congr_ae measurable_heatTime)

/-- Componentwise conjugation commutes with the plane heat operator `planeHeat θ`. -/
theorem t0_planeHeat_conjV (θ : ℝ) (u : ℝ × ℝ → EuclideanSpace ℂ (Fin 2)) (x : ℝ × ℝ) :
    planeHeat θ (fun w => conjV 2 (u w)) x = conjV 2 (planeHeat θ u x) := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
    have h := LinearIsometry.integral_comp_comm
      (μ := (volume : Measure (UnforcedLeray.Gaussian.Euc 2)))
      (conjVR 2).toLinearIsometry
      (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - planeι y))
    have e : ∀ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • conjV 2 (u (x - planeι y)) =
          (conjVR 2).toLinearIsometry
            (UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - planeι y)) :=
      fun y => ((conjVR 2).map_smul _ _).symm
    change ∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • conjV 2 (u (x - planeι y)) =
      conjV 2 (∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - planeι y))
    simp only [e]
    exact h
  · simp only [UnforcedLeray.B0224.planeHeat, hθ, ↓reduceIte]

/-- The fibrewise heat operator commutes with componentwise conjugation. -/
theorem t0_fiberHeat_conjV {c : ℝ} (θ : ℝ → ℝ) (g : Profile → EuclideanSpace ℂ (Fin 2))
    (p : Profile) :
    fiberHeat c θ (fun q => conjV 2 (g q)) p = conjV 2 (fiberHeat c θ g p) := by
  unfold fiberHeat
  exact t0_planeHeat_conjV (θ p.1) (fun z => UnforcedLeray.B0220.periodize c g (p.1, z)) p.2

/-- Conjugation commutes with the age dilation `dilH`, `a > 0`. -/
theorem t0_dilH_cjLp {c : ℝ} {a : ℝ} (ha : 0 < a) (f : HSpace c (EuclideanSpace ℂ (Fin 2))) :
    dilH ha (cjLp (measureH c) 2 f) = cjLp (measureH c) 2 (dilH ha f) := by
  apply Lp.ext
  have hsm : StronglyMeasurable (fun p => conjV 2 (f p)) :=
    (conjV 2).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable f)
  filter_upwards [coeFn_dilH ha (cjLp (measureH c) 2 f),
    dil_congr_ae ha (Lp.stronglyMeasurable (cjLp (measureH c) 2 f)) hsm
      (coeFn_cjLp (measureH c) 2 f),
    coeFn_cjLp (measureH c) 2 (dilH ha f), coeFn_dilH ha f] with p h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  rfl

/-- Conjugation commutes with the heat operator `heatH` for any measurable heat time. -/
theorem t0_heatH_cjLp {c : ℝ} (hc : 0 < c) {θ : ℝ → ℝ} (hθ : Measurable θ)
    (g : HSpace c (EuclideanSpace ℂ (Fin 2))) :
    heatH hc hθ (cjLp (measureH c) 2 g) = cjLp (measureH c) 2 (heatH hc hθ g) := by
  apply Lp.ext
  have hsm : StronglyMeasurable (fun q => conjV 2 (g q)) :=
    (conjV 2).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable g)
  filter_upwards [coeFn_heatH hc hθ (cjLp (measureH c) 2 g),
    fiberHeat_congr_ae hc hθ (Lp.stronglyMeasurable (cjLp (measureH c) 2 g)) hsm
      (coeFn_cjLp (measureH c) 2 g),
    coeFn_cjLp (measureH c) 2 (heatH hc hθ g), coeFn_heatH hc hθ g] with p h1 h2 h3 h4
  rw [h1, h2, t0_fiberHeat_conjV, h3, h4]

/-- **The flat cylinder semigroup is real** (source 1655-1656, 1686-1689):
`T_0(t)\bar f = \overline{T_0(t)f}`. -/
theorem t0Conj : T0Conj := by
  intro c ν t hc f
  simp only [UnforcedLeray.B0224.T0, ContinuousLinearMap.comp_apply]
  rw [t0_dilH_cjLp, t0_heatH_cjLp]

end UnforcedLeray.Short.PartIIIb.NearInst.Body
