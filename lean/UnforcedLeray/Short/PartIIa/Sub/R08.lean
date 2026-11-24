import UnforcedLeray.Short.PartIIa.StatementsRing

/-!
# Part II-a, task `PartII-a:R08`: the raw inlet is solenoidal (conditional)

Source of record: `the November 2 reference manuscript`, lines 1328-1336 ("At `t = 0`
use the same stream formula with the Gaussian inlet. Each derivative costs `C/r`; all powers of
`|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`. ... Flux across a sphere of radius `h` is
`O(h)`, proving distributional solenoidality").

The field `a_raw = inletRaw c R` has the singularity `|a_raw(x)| ≤ C/|x|` at the origin, is smooth on
`{x ≠ 0}` (also at nonzero axis points, where it is flat), and is divergence free there. These give
distributional solenoidality across the origin because the flux through a sphere of radius `h` is
`O(h)`. The decomposition into leaf Props:

* `InletBound` : `|a(x)| ≤ C/|x|` for every extension `a` continuous on `{x ≠ 0}`;
* `InletSmoothExt` : a `C^∞` extension `a` on `{x ≠ 0}` of `inletRaw` (the smoothness conjunct of
  `RingInlet`, reused by `PartII-a:R10`);
* `InletDivZero` : the pointwise divergence of such an extension vanishes on `{x ≠ 0}`;
* `InvNormLocInt` : `|x|⁻¹` is locally integrable on `ℝ³`;
* `SolenoidalCriterion` : a `C¹` field on `{x ≠ 0}` with zero divergence and `|b(x)| ≤ C/|x|` is
  distributionally solenoidal on `ℝ³`.

The axis is a null set (`Axi.volume_axis`), so `inletRaw` and its extension agree almost everywhere.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **Inlet bound** (source lines 1331-1332): every extension of `inletRaw` that is continuous on
`{x ≠ 0}` satisfies `‖a(x)‖ ≤ C / ‖x‖` for `x ≠ 0`. Off the axis, with `r = ϱ x`, `q = R log(r/R)`,
`η = R z / r` and `trainDatum c q η = e^{-η²/4} θ(q)`, `θ(q) = -2 Σₙ e^{-(q - nc)²/4}` smooth
`c`-periodic: `u_r = (R/r)(η/2) e^{-η²/4} θ(q)`, `u_z = r⁻¹ e^{-η²/4} [θ + R θ' + (η²/2) θ]`, and
`r ≥ ‖x‖/(1 + |η|/R)`; the bound at axis points follows by continuity. -/
def InletBound : Prop :=
  ∀ c R : ℝ, 0 < c → 2 ≤ R → ∀ a : Space → Space, ContinuousOn a {x : Space | x ≠ 0} →
    (∀ x : Space, x ∉ Axi.axis → a x = inletRaw c R x) →
      ∃ C : ℝ, ∀ x : Space, x ≠ 0 → ‖a x‖ ≤ C / ‖x‖

/-- **Smooth extension of the inlet** (source lines 1332-1334, "including smoothness at nonzero axis
points"): `inletRaw c R` agrees off the axis with a field `C^∞` on `{x ≠ 0}`. At axis points with
`z ≠ 0` all terms carry the flat factor `e^{-R²z²/(4ϱ²)}` (`Axi.contDiff_flat_extension`). -/
def InletSmoothExt : Prop :=
  ∀ c R : ℝ, 0 < c → 2 ≤ R → ∃ a : Space → Space, ContDiffOn ℝ ∞ a {x : Space | x ≠ 0} ∧
    ∀ x : Space, x ∉ Axi.axis → a x = inletRaw c R x

/-- **Pointwise divergence** (source line 1210 stream form): a `C¹` extension `a` of `inletRaw` on
`{x ≠ 0}` has `div a = 0` on `{x ≠ 0}`. Off the axis this is `∂_r(r u_r) + ∂_z(r u_z) = 0` for
`r u_r = -∂_z 𝒫`, `r u_z = ∂_r 𝒫` (`B0185.streamForm_divergence_eq_zero`, equality of mixed partials of
`𝒫 = inletStream c R`); at axis points `x ≠ 0` it follows by continuity of `div a` and density of the
complement of the axis. -/
def InletDivZero : Prop :=
  ∀ c R : ℝ, 0 < c → 2 ≤ R → ∀ a : Space → Space, ContDiffOn ℝ 1 a {x : Space | x ≠ 0} →
    (∀ x : Space, x ∉ Axi.axis → a x = inletRaw c R x) →
      ∀ x : Space, x ≠ 0 → ∑ i : Fin 3, fderiv ℝ a x (coordinateVector i) i = 0

/-- `‖x‖⁻¹` is integrable on every ball about `0` in `ℝ³`. (Polar coordinates, or the dyadic
shell estimate `∫_{2^{-k-1} ≤ |x| < 2^{-k}} |x|⁻¹ ≤ C 4^{-k}`; check
`Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean` and `Analysis/Distribution/Sobolev.lean`
for an existing `‖x‖^(-s)` ball-integrability lemma.) -/
def InvNormLocInt : Prop :=
  ∀ r : ℝ, 0 < r → IntegrableOn (fun x : Space => ‖x‖⁻¹) (Metric.ball (0 : Space) r) volume

/-- **Solenoidality criterion across a point singularity** (source lines 1335-1336, "flux across a
sphere of radius `h` is `O(h)`"): if `b` is `C¹` on `{x ≠ 0}`, divergence free there, and
`‖b(x)‖ ≤ C / ‖x‖`, then `b` is distributionally divergence free on `ℝ³`. Proof: `b` is locally
integrable (`InvNormLocInt`); for a test function `φ` and a smooth radial cutoff `χ_h(x) = χ(‖x‖/h)`
(`0` near the origin), `∫ b · ∇(φ(1 - χ_h)) = 0` by integration by parts on `{x ≠ 0}`
(`MeasureTheory.integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), and
`|∫ b · ∇(φ χ_h)| ≤ C h² sup|∇φ| + C h sup|φ| → 0` (dominated convergence). -/
def SolenoidalCriterion : Prop :=
  ∀ (b : Space → Space) (C : ℝ), ContDiffOn ℝ 1 b {x : Space | x ≠ 0} →
    (∀ x : Space, x ≠ 0 → ∑ i : Fin 3, fderiv ℝ b x (coordinateVector i) i = 0) →
    (∀ x : Space, x ≠ 0 → ‖b x‖ ≤ C / ‖x‖) → IsSolenoidal b

/-- **`PartII-a:R08`, conditional**: the raw inlet is distributionally solenoidal. -/
theorem ringInlet_solenoidal_of (hb : InletBound) (hs : InletSmoothExt) (hd : InletDivZero)
    (hcrit : SolenoidalCriterion) (c R : ℝ) (hc : 0 < c) (hR : 2 ≤ R) :
    IsSolenoidal (inletRaw c R) := by
  obtain ⟨a, ha1, haeq⟩ := hs c R hc hR
  have ha1' : ContDiffOn ℝ 1 a {x : Space | x ≠ 0} := ha1.of_le (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hb c R hc hR a ha1'.continuousOn haeq
  have hsol : IsSolenoidal a := hcrit a C ha1' (hd c R hc hR a ha1' haeq) hC
  have hnull : volume {x : Space | ¬ inletRaw c R x = a x} = 0 := by
    refine measure_mono_null (fun x hx => ?_) Axi.volume_axis
    by_contra hxa
    exact hx (haeq x hxa).symm
  have hae : inletRaw c R =ᵐ[volume] a := ae_iff.2 hnull
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · refine (hsol.integrable φ hφ).congr ?_
    filter_upwards [hae] with x hx
    simp only [hx]
  · rw [← hsol.identity φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hx]

end UnforcedLeray.Short.PartIIa
