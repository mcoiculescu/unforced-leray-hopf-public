import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# `OuterSConj` (source 1675-1677)

The outer semigroup `S_ε(t) = B0223.outerS` is `e^{-t/4} · dilN(e^{t/2}) · e^{h(e^t-1)Δ} · transC t`
(`B0223.Sop_apply`, `h = νε²`).  Each factor commutes with the complex conjugation `cjLp`:

* the phase translation `transC t` (composition with the measure-preserving shift);
* the spatial heat semigroup `heatC θ` (for `θ > 0` the Gaussian average `heatConv` with a real
  kernel, `LinearIsometry.integral_comp_comm` for the componentwise conjugation; for `θ ≤ 0` the
  identity);
* the dilation `dilN a`, `a > 0` (composition with `(x, τ) ↦ (a x, τ)` and the real factor
  `a^{3/2}`);
* the real scalar `e^{-t/4}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile cell)

/-- A real scalar acts compatibly with componentwise conjugation. -/
theorem os_conjV_real_smul (r : ℝ) (v : EuclideanSpace ℂ (Fin 3)) :
    conjV 3 (r • v) = r • conjV 3 v :=
  (conjVR 3).map_smul r v

/-- Componentwise conjugation commutes with the Gaussian average `heatConv`. -/
theorem os_heatConv_conjV {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (ι : UnforcedLeray.Gaussian.Euc d →+ G) (θ : ℝ) (u : G → EuclideanSpace ℂ (Fin 3))
    (x : G) :
    Heat.heatConv ι θ (fun w => conjV 3 (u w)) x = conjV 3 (Heat.heatConv ι θ u x) := by
  have h := LinearIsometry.integral_comp_comm (μ := (volume : Measure (UnforcedLeray.Gaussian.Euc d)))
    (conjVR 3).toLinearIsometry
    (fun y : UnforcedLeray.Gaussian.Euc d => UnforcedLeray.Gaussian.gaussKernel d θ y • u (x - ι y))
  have e : ∀ y : UnforcedLeray.Gaussian.Euc d, UnforcedLeray.Gaussian.gaussKernel d θ y • conjV 3 (u (x - ι y)) =
      (conjVR 3).toLinearIsometry (UnforcedLeray.Gaussian.gaussKernel d θ y • u (x - ι y)) :=
    fun y => ((conjVR 3).map_smul _ _).symm
  change ∫ y : UnforcedLeray.Gaussian.Euc d, UnforcedLeray.Gaussian.gaussKernel d θ y • conjV 3 (u (x - ι y)) =
    conjV 3 (∫ y : UnforcedLeray.Gaussian.Euc d, UnforcedLeray.Gaussian.gaussKernel d θ y • u (x - ι y))
  simp only [e]
  exact h

/-- Conjugation commutes with the phase translation `transC t`. -/
theorem os_transC_cjLp {P : ℝ} [Fact (0 < P)] (t : ℝ) (F : X SpaceC P) :
    transC t (cjLp (volume : Measure (PSpace P)) 3 F) =
      cjLp (volume : Measure (PSpace P)) 3 (transC t F) := by
  apply Lp.ext
  filter_upwards [coeFn_transC t (cjLp (volume : Measure (PSpace P)) 3 F),
    coeFn_cjLp (volume : Measure (PSpace P)) 3 (transC t F), coeFn_transC t F,
    (mp_shiftT t).quasiMeasurePreserving.ae_eq_comp
      (coeFn_cjLp (volume : Measure (PSpace P)) 3 F)] with z h1 h2 h3 h4
  rw [h1, h2, h3]
  exact h4

/-- Conjugation commutes with the spatial heat semigroup `heatC θ` (both cases of the sign of
`θ`). -/
theorem os_heatC_cjLp {P : ℝ} [Fact (0 < P)] (θ : ℝ) (G : X SpaceC P) :
    heatC θ (cjLp (volume : Measure (PSpace P)) 3 G) =
      cjLp (volume : Measure (PSpace P)) 3 (heatC θ G) := by
  by_cases hθ : 0 < θ
  · apply Lp.ext
    have h1 := heatC_rep hθ (cjLp (volume : Measure (PSpace P)) 3 G)
    have h2 := Heat.heatConv_congr_ae (ιx P) continuous_ιx.measurable θ
      (coeFn_cjLp (volume : Measure (PSpace P)) 3 G)
    have h3 := heatC_rep hθ G
    have h4 := coeFn_cjLp (volume : Measure (PSpace P)) 3 (heatC θ G)
    filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
    rw [hz1, hz4, hz3, hz2]
    exact os_heatConv_conjV (ιx P) θ _ z
  · rw [heatC_of_nonpos (not_lt.mp hθ), heatC_of_nonpos (not_lt.mp hθ)]

/-- Conjugation commutes with the dilation `dilN a`, `a > 0`. -/
theorem os_dilN_cjLp {P : ℝ} [Fact (0 < P)] {a : ℝ} (ha : 0 < a) (G : X SpaceC P) :
    dilN a (cjLp (volume : Measure (PSpace P)) 3 G) =
      cjLp (volume : Measure (PSpace P)) 3 (dilN a G) := by
  apply Lp.ext
  filter_upwards [dilN_ae ha (coeFn_cjLp (volume : Measure (PSpace P)) 3 G),
    coeFn_cjLp (volume : Measure (PSpace P)) 3 (dilN a G), coeFn_dilN ha G] with z h1 h2 h3
  rw [h1, h2, h3]
  exact (os_conjV_real_smul _ _).symm

/-- Conjugation commutes with a real complex scalar. -/
theorem os_cjLp_ofReal_smul {P : ℝ} [Fact (0 < P)] (r : ℝ) (G : X SpaceC P) :
    cjLp (volume : Measure (PSpace P)) 3 (((r : ℝ) : ℂ) • G) =
      ((r : ℝ) : ℂ) • cjLp (volume : Measure (PSpace P)) 3 G := by
  rw [map_smulₛₗ, Complex.conj_ofReal]

/-- **The outer semigroup is real** (source 1675-1677): `S_ε(t)\bar F = \overline{S_ε(t)F}` for
`t > 0`. -/
theorem outerSConj : OuterSConj := by
  intro P ν ε _ hν t ht F
  simp only [outerS_T, Sop_apply]
  rw [os_transC_cjLp, os_heatC_cjLp, os_dilN_cjLp (Real.exp_pos _), os_cjLp_ofReal_smul]

end UnforcedLeray.Short.PartIIIb.NearInst.Body
