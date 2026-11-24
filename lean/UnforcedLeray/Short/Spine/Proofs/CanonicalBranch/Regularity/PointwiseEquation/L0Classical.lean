import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5

/-!
# Spine leaf 2: `L₀` acts by `generatorL0` (`L0ClassicalAe`)

Proves the Prop `UnforcedLeray.Short.Spine.L0ClassicalAe` of `Sub/SP_CAN4_5.lean` exactly as stated.
Source: `the November 2 reference manuscript` line 1086; `eq:st18-t00006`
(`L₀ = -2iΩ + 2ikR`).

Proof. For `f ∈ X_G` and a profile `g` with `g =ᵐ f` and `g` continuous on `(0, ∞)`:
* `L₀ f =ᵐ L0Fun f =ᵐ L0Fun g` (`B0012.coeFn_L0`, `B0012.L0Fun_congr`), and
  `L0Fun g = generatorL0 g` everywhere (`Cons.G3b.generatorL0_eq_L0Fun`);
* on `(0, ∞)` the Green formula satisfies `R g r = R f r` (`B0012.R_congr`, with the a.e. equality
  transported to `volume.restrict (Ioi 0)` by `B0012.restrict_ac`), so `generatorL0 g` agrees on
  `(0, ∞)` with `r ↦ -2i Ω(r) g(r) + 2i k(r) (R f)(r)`, which is continuous there
  (`B0012.continuous_radialOmega`, `B0012.continuous_radialK`, `B0012.continuousOn_R`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 2, `L₀` acts by `generatorL0`.** -/
theorem l0ClassicalAe_proof : UnforcedLeray.Short.Spine.L0ClassicalAe := by
  intro f g hg hgc
  -- a.e. equality on `(0, ∞)` for the Lebesgue restriction, used by the Green formula `R`
  have hgf : g =ᵐ[volume.restrict (Ioi (0 : ℝ))] (⇑f : ℝ → ℂ) :=
    UnforcedLeray.B0012.restrict_ac.ae_le hg
  constructor
  · -- first conjunct: `L₀ f =ᵐ L0Fun f =ᵐ L0Fun g = generatorL0 g`
    filter_upwards [UnforcedLeray.B0012.coeFn_L0 f,
      UnforcedLeray.B0012.L0Fun_congr hg.symm] with r h1 h2
    rw [h1, h2, UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun g r]
  · -- second conjunct: continuity of `generatorL0 g` on `(0, ∞)`
    have hωc : Continuous fun r : ℝ => ((UnforcedLeray.GaussianVortex.radialOmega r : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp UnforcedLeray.B0012.continuous_radialOmega
    have hkc : Continuous fun r : ℝ => ((UnforcedLeray.GaussianVortex.radialK r : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp UnforcedLeray.B0012.continuous_radialK
    have hcont : ContinuousOn (fun r : ℝ =>
        -2 * Complex.I * ((UnforcedLeray.GaussianVortex.radialOmega r : ℝ) : ℂ) * g r +
          2 * Complex.I * ((UnforcedLeray.GaussianVortex.radialK r : ℝ) : ℂ) *
            UnforcedLeray.B0011.R (⇑f : ℝ → ℂ) r) (Ioi 0) :=
      ((continuousOn_const.mul hωc.continuousOn).mul hgc).add
        ((continuousOn_const.mul hkc.continuousOn).mul (UnforcedLeray.B0012.continuousOn_R f))
    refine hcont.congr fun r hr => ?_
    have hr' : (0 : ℝ) < r := hr
    rw [UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun g r, UnforcedLeray.B0012.L0Fun,
      UnforcedLeray.B0012.R_congr hgf hr']

end UnforcedLeray.Short.Spine

end
