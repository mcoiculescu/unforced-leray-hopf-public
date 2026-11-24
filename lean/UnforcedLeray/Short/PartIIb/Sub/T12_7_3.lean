import UnforcedLeray.Short.PartIIb.Sub.T12_7

/-!
# Part II-b, task `PartII-b:T12/7/3` (`DeqHeatSymm`): decomposition into leaves

Source: `the November 2 reference manuscript` lines 1923-1927 (the heat semigroup
is self-adjoint).  Three leaves: absolute integrability of the Fubini integrand (the analytic
core), identification of `flatHeat` with the coordinatewise convolution integral, and the Fubini
/ translation / evenness computation.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `T12/7/3/a`** (the analytic core, SP 1923-1927): for a `DeqSliceGood` slice `g`
(a.e. `q`-periodic, finite cell `L^r` norm), `θ > 0` and `ψ` continuous with compact support, the
integrand `K_θ(w) ‖g(z-w)‖ |ψ(z)|` (and its coordinate versions `K_θ(w) |g_i(z-w)| |ψ(z)|`) is
integrable on `(ℝ×ℝ) × (ℝ×ℝ)`.  Route: Tonelli turns the `z`-integral against `|ψ|` into a
lintegral over a box `B ⊇ supp ψ`; the lintegral form of `Cyl.eLpNorm_conv_periodic_le`
(`Lib/CylinderB/Periodize.lean`, `ν = volume.withDensity (ofReal K_θ)`, applied to `‖g'‖` with `g'`
the periodic representative, as in `Tasks/FlatCausal/FlatHeatContraction.lean`) gives that
`K_θ ⋆ ‖g‖` is in `L^r(cell)`; `B` meets finitely many cells, so Hölder on `B` bounds the integral. -/
def DeqhsAbsInt : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ → ∀ ψ : ℝ × ℝ → ℝ, Continuous ψ → HasCompactSupport ψ →
      Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|)
          (volume.prod volume) ∧
        ∀ i : Fin 2, Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          (flatHeatKernel θ p.2 : ℂ) * g (p.1 - p.2) i * (ψ p.1 : ℂ)) (volume.prod volume)

/-- **Leaf `T12/7/3/b`** (SP 1923-1927): under the integrability of `DeqhsAbsInt`, for a.e. `z` with
`ψ z ≠ 0` the vector `w ↦ K_θ(w) g(z-w)` is Bochner integrable (Fubini, `Integrable.prod_right_ae`,
`K_θ ≥ 0`), so `(flatHeat θ g z) i = ∫ w, K_θ(w) g_i(z-w)`
(`ContinuousLinearMap.integral_comp_comm` with the coordinate functional); the remaining `z`
(null, or `ψ z = 0`) do not contribute to `∫ dz`. -/
def DeqhsIdent : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ → ∀ ψ : ℝ × ℝ → ℝ, Continuous ψ → HasCompactSupport ψ →
      (Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => flatHeatKernel θ p.2 * ‖g (p.1 - p.2)‖ * |ψ p.1|)
          (volume.prod volume)) → ∀ i : Fin 2,
        ∫ z : ℝ × ℝ, flatHeat θ g z i * (ψ z : ℂ) =
          ∫ z : ℝ × ℝ, (∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * g (z - w) i) * (ψ z : ℂ)

/-- **Leaf `T12/7/3/c`** (Fubini + translation + evenness, SP 1923-1927): for a measurable
`f : ℝ×ℝ → ℂ` and `K = flatHeatKernel θ` (even), `ψ` bounded, with
`(z,w) ↦ K(w) f(z-w) ψ(z)` integrable on the product,
`∫ z, (∫ w, K w * f (z-w)) * ψ z = ∫ z, f z * ∫ w, K w * ψ (z-w)`.
Proof: `integral_integral_swap`, the measure preserving shift `z ↦ z + w`
(`integral_add_right_eq_self`), `K(-w) = K(w)` (`integral_neg_eq_self`), `integral_integral_swap`
again. -/
def DeqhsFubini : Prop :=
  ∀ (θ : ℝ), 0 < θ → ∀ (f : ℝ × ℝ → ℂ), AEStronglyMeasurable f volume →
    ∀ ψ : ℝ × ℝ → ℝ, Continuous ψ → HasCompactSupport ψ →
      Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          (flatHeatKernel θ p.2 : ℂ) * f (p.1 - p.2) * (ψ p.1 : ℂ)) (volume.prod volume) →
        ∫ z : ℝ × ℝ, (∫ w : ℝ × ℝ, (flatHeatKernel θ w : ℂ) * f (z - w)) * (ψ z : ℂ) =
          ∫ z : ℝ × ℝ, f z * ((∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (z - w) : ℝ) : ℂ)

theorem deqHeatSymm_of (h1 : DeqhsAbsInt) (h2 : DeqhsIdent) (h3 : DeqhsFubini) : DeqHeatSymm := by
  intro c r g hc hr hg θ hθ ψ hψ hψc i
  obtain ⟨hn, hi⟩ := h1 c r g hc hr hg θ hθ ψ hψ hψc
  rw [h2 c r g hc hr hg θ hθ ψ hψ hψc hn i]
  exact h3 θ hθ (fun u => g u i)
    (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable hg.2.1)
    ψ hψ hψc (hi i)

end UnforcedLeray.Short.IIb
