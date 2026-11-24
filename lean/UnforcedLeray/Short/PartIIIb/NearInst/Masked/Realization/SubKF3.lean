import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1
import UnforcedLeray.Analysis.Pressure.Spatial

/-!
# Leaves of `KF3` (source 3586-3601, 3617-3618; Leray projection 117-120)

Source of record: `the November 2 reference manuscript`.

`KF3` (`Sub1.lean`) is the heat-Leray identity `e^{θΔ}P_3D div M = ∇K_θ : M` for a smooth outer
tensor `M(x, τ) = T(τ, ε⁻¹x)` ("We begin with smooth tensors", 3594-3596; the heat-Leray kernel
`K_t = δG_t + ∂∂∫_t^∞G_a da`, 3597-3601; "integrate the tensor divergence by parts", 3617-3618).
`P_3D = B0226.P3D` is the orthogonal projection onto `B0226.physSolenoidal` (the `L²(dx dτ)`
complement of the gradients of the physical tests), the Cartesian Leray projection `𝐏` (117-120).

## Route

1. **The projection, explicitly** (`(a)` of the organizer spec).  For `g = div M` put
   `p = Σ_i ∂_iN * g_i` with `N = (4π|x|)⁻¹` (`lerayPres`, built from the library's literal
   Newtonian convolution `PressureAnalysis.newtonComponent`), so `Δp = -div g`
   (`PressureAnalysis.newtonComponent_laplacian_test`), and `V = g + ∇p` (`lerayField`).
   `V` is divergence free (`KF3SolSlice`), in `L²` (`KF3PresDecay`, `KF3MemLpDecay`), and `∇p`
   lies in the closure of the test gradients (`KF3GradOrth`, a cutoff argument), hence
   `P_3D g = V` (`p3d_cartDiv_eq`).
2. **Slices** (`(e)`).  `toX` of the class of `V` has, for a.e. phase `s`, the slice `V(·, τ_s)`
   a.e. in `x`, so the heat integral of the representative equals that of `V(·, τ_s)` for every
   `x, θ` (`KF3Slice`).  No continuity upgrade is needed because `V` is explicit.
3. **The heat integral of `V`** (`(b)-(d)`).  `G_θ * div M = ∇G_θ : M` (`KF3HeatDiv`, one
   integration by parts); `G_θ * ∇p = ∇∂∂(∫_θ^∞G_a) : M` (`KF3HeatPres`, from
   `G_θ * ∂_jN = ∂_j∫_θ^∞G_a` and two integrations by parts); `∇K_θ = δ∇G_θ + ∇∂∂∫_θ^∞G_a`
   (`KF3FDerivK`).  Together: `∫G_θ(y)V_i(x-y,τ)dy = Σ_{jk}∫∂_kK_{θ,ij}(x-z)M_{jk}(z,τ)dz`, the real
   form of `convTerm` (`heat_lerayField_eq_convTerm`).

`kf3_of` assembles `KF3` from the top leaves `KF3PresSmooth`, `KF3PresDecay`, `KF3GradOrth`,
`KF3SolSlice`, `KF3MemLpDecay`, `KF3Slice`, `KF3HeatDiv`, `KF3HeatPres`, `KF3FDerivK`.  The
remaining Props (`KF3PresGrad`, `KF3TailSmooth`, `KF3TailFDeriv`, `KF3HeatGConvFDeriv`,
`KF3HeatNewtonGrad`, `KF3HeatNewtonComp`, `KF3TailIBP`) are lower leaves used by the proofs of
the top ones.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-! ## Objects -/

/-- **Smooth outer tensors** (source 3594-3596, "We begin with smooth tensors"): a tensor field
`M(x, τ)` of the outer variables, each entry smooth in `(x, τ)`, `P`-periodic in `τ`, with bounded
spatial support.  `outerField R T` of a smooth Cartesian tensor `T` (`IsCartTest`) is one
(`isOuterTest_outerField`). -/
structure IsOuterTest (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  smooth : ∀ i j : Fin 3, ContDiff ℝ ∞ fun y : Space × ℝ => M y i j
  periodic : ∀ (x : Space) (τ : ℝ), M (x, τ + P) = M (x, τ)
  bounded : ∃ r : ℝ, ∀ y : Space × ℝ, M y ≠ 0 → ‖y.1‖ ≤ r

/-- **The Leray pressure** of `div M` (source 117-120, the Cartesian Leray projection; 3609-3611,
`K_0 = D²(4π|x|)⁻¹` with its local part): `p(x, τ) = Σ_i ∫ ∂_iN(x - y) (div M)_i(y, τ) dy`,
`N = (4π|x|)⁻¹` (`PressureAnalysis.newtonComponent`, `newtonGradientKernel i = ∂_iN`).  It solves
`Δp = -div div M` (`PressureAnalysis.newtonComponent_laplacian_test`), so `div M + ∇p` is the
Leray projection of `div M`. -/
def lerayPres (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (y : Space × ℝ) : ℝ :=
  ∑ i : Fin 3, UnforcedLeray.PressureAnalysis.newtonComponent i (fun x => cartDiv M (x, y.2) i) y.1

/-- **The projected divergence** `P_3D div M = div M + ∇ₓp` (`p = lerayPres M`; source 117-120,
3586-3589). -/
def lerayField (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) : Space × ℝ → Space :=
  cartDiv M + UnforcedLeray.B0226.gradX (lerayPres M)

/-! ## The leaves: the projection (step 1) -/

/-- **Leaf: smoothness of the Leray pressure** (source 117-120, 3594-3596).  For a smooth outer
tensor, `lerayPres M` is `C^∞` jointly in `(x, τ)`.
Route: `newtonComponent i f x = ∫ ∂_iN(x - y) f(y) dy = (∂_iN ⋆ f)(x)` (substitute `y ↦ x - y`,
`integral_sub_left_eq_self`); `∂_iN = PressureAnalysis.newtonGradientKernel i` is locally integrable
(`PressureAnalysis.newtonGradientKernel_locallyIntegrable`); `(τ, x) ↦ (div M)_i(x, τ)` is smooth
with `x`-support in a fixed closed ball (`IsOuterTest.bounded`).  Mathlib's
`MeasureTheory.contDiffOn_convolution_right_with_param` (with `L = ContinuousLinearMap.lsmul ℝ ℝ`,
parameter `τ`, `s = univ`, `k = closedBall 0 r`) gives smoothness of `(τ, x) ↦ (∂_iN ⋆ g_i(·, τ))(x)`;
compose with `Prod.swap` and sum over `i`. -/
def KF3PresSmooth : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsOuterTest P M →
    ContDiff ℝ ∞ (lerayPres M)

/-- **Leaf: the pressure gradient is the Newtonian convolution of `∇ div M`** (source 117-120,
3617-3618).  `(∇ₓp)_i(x, τ) = Σ_j (∂_jN ⋆ ∂_i(div M)_j(·, τ))(x)`.
Route: `(gradX φ y) i = fderiv φ y (e_i, 0)` (`B0226.inner_gradX` with `w = e_i`, `EuclideanSpace.inner_single_right`),
which is `fderiv (fun x => φ (x, τ)) x e_i` (chain rule with `hasFDerivAt_prodMk_left`, smoothness
from `KF3PresSmooth`); then `HasCompactSupport.hasFDerivAt_convolution_right` (Mathlib,
`Analysis/Calculus/ContDiff/Convolution.lean`) for `∂_jN ⋆ g_j(·, τ)` with `g_j` smooth and compactly
supported, and the substitution of `KF3PresSmooth` back to `newtonComponent`. -/
def KF3PresGrad : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsOuterTest P M →
    ∀ (x : Space) (τ : ℝ) (i : Fin 3),
      UnforcedLeray.B0226.gradX (lerayPres M) (x, τ) i =
        ∑ j : Fin 3, UnforcedLeray.PressureAnalysis.newtonComponent j
          (fun z => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
            (UnforcedLeray.coordinateVector i)) x

/-- **Leaf: decay of the Leray pressure and its gradient** (source 3602-3606 for the kernel decay
`|∂N(x)| ≤ C|x|^{-2}`).  For `P > 0` there is `C` with `|p(x, τ)| ≤ C/(1 + |x|)` and
`|∇ₓp(x, τ)| ≤ C/(1 + |x|)²` for all `(x, τ)`.
Route: `PressureAnalysis.norm_newtonGradientKernel_le` (`|∂_iN(w)| ≤ (4π)⁻¹|w|^{-2}`); with `h`
supported in `closedBall 0 r` and `|h| ≤ B`: for `|x| ≥ 2r + 1`, `|x - y| ≥ |x|/2` on the support,
so `|(∂_iN ⋆ h)(x)| ≤ (4π)⁻¹·4|x|^{-2}·B·vol(B_r)`; for `|x| ≤ 2r + 1`,
`|(∂_iN ⋆ h)(x)| ≤ B ∫_{|w| ≤ 3r+1} |∂_iN(w)| dw < ∞` (`PressureAnalysis.newtonGradientKernel_locallyIntegrable`).
Apply to `h = (div M)_i(·, τ)` and (via `KF3PresGrad`) to `h = ∂_i(div M)_j(·, τ)`; the bounds
`B` are uniform in `τ` because these functions are continuous, `P`-periodic in `τ` and supported in
a fixed ball (bounded on the compact `closedBall 0 r ×ˢ Icc 0 P`). -/
def KF3PresDecay : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), 0 < P → IsOuterTest P M →
    ∃ C : ℝ, ∀ y : Space × ℝ, |lerayPres M y| ≤ C / (1 + ‖y.1‖) ∧
      ‖UnforcedLeray.B0226.gradX (lerayPres M) y‖ ≤ C / (1 + ‖y.1‖) ^ 2

/-- **Leaf: gradients of decaying periodic functions are orthogonal to the solenoidal fields**
(source 117-120: the complement of `B0226.physSolenoidal` is the closure of the test gradients).
For `p` smooth, `2εc`-periodic in `τ`, with `|p| ≤ C/(1 + |x|)` and `∇ₓp ∈ L²(dx dτ)`, the class of
`∇ₓp` lies in `(physSolenoidal ε c)ᗮ`.
Route (cutoff): fix `χ` smooth, `χ = 1` on `closedBall 0 1`, `χ = 0` off `ball 0 2` (`ContDiffBump`),
`χ_n(x) = χ(x/n)`.  `φ_n = χ_n p` is an `IsPhysTest (2εc)` (smooth, periodic, bounded support), so
`physGrad φ_n ∈ (physSolenoidal)ᗮ` (`B0226.physGrad_mem_orthogonal`).
`∇ₓφ_n = χ_n∇ₓp + p∇χ_n`; `‖(1-χ_n)∇ₓp‖_{L²} → 0` by dominated convergence, and
`‖p∇χ_n‖²_{L²(physMeasure)} ≤ 2εc·‖∇χ‖²_∞ n^{-2}·∫_{n ≤ |x| ≤ 2n} C²(1+|x|)^{-2} dx = O(1/n) → 0`.
The orthogonal complement is closed (`Submodule.isClosed_orthogonal`), so the limit lies in it
(`IsClosed.mem_of_tendsto`).  If `2εc ≤ 0` the measure is zero and every class is `0`.  Model:
`Cons.C09.tendsto_hessL2_cutoff` (`Cons/C09PressureProjection/Cutoff.lean`). -/
def KF3GradOrth : Prop :=
  ∀ (ε c : ℝ) (p : Space × ℝ → ℝ), ContDiff ℝ ∞ p →
    (∀ (x : Space) (τ : ℝ), p (x, τ + 2 * ε * c) = p (x, τ)) →
    (∃ C : ℝ, ∀ y : Space × ℝ, |p y| ≤ C / (1 + ‖y.1‖)) →
    ∀ hp : MemLp (UnforcedLeray.B0226.gradX p) 2 (UnforcedLeray.B0220.physMeasure ε c),
      hp.toLp (UnforcedLeray.B0226.gradX p) ∈ (UnforcedLeray.B0226.physSolenoidal ε c)ᗮ

/-- **Leaf: the projected divergence is divergence free, slice by slice** (source 117-120,
3586-3589).  For a physical test `φ` and every phase `τ`,
`∫ (div M + ∇ₓp)(x, τ) · ∇ₓφ(x, τ) dx = 0`.
Route: `B0226.inner_gradX_eq_sum` writes the integrand as `Σ_i V_i ∂_iφ(·, τ)`; `φ(·, τ)` is an
`IsSpatialTest` (smooth, support in a closed ball).  Integrate by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, `p(·, τ)` smooth by `KF3PresSmooth`):
`∫ ∂_ip ∂_iφ = -∫ p ∂_i∂_iφ`, so `Σ_i ∫ ∂_ip ∂_iφ = -∫ p Δφ` (`Heat.laplacian`)
`= -Σ_j ∫ newtonComponent j g_j · Δφ = -Σ_j ∫ g_j ∂_jφ`
(`PressureAnalysis.newtonComponent_laplacian_test`, `g_j = (div M)_j(·, τ) ∈ L¹`,
integrability `PressureAnalysis.newtonComponent_laplacian_test_integrable`), which cancels
`Σ_j ∫ g_j ∂_jφ`. -/
def KF3SolSlice : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsOuterTest P M →
    ∀ φ : Space × ℝ → ℝ, UnforcedLeray.B0226.IsPhysTest P φ → ∀ τ : ℝ,
      ∫ x : Space, inner ℝ (lerayField M (x, τ)) (UnforcedLeray.B0226.gradX φ (x, τ)) = 0

/-- **Leaf: `L²` from decay** (measure theory).  A continuous field with
`|f(x, τ)| ≤ C/(1 + |x|)²` is in `L²(dx dτ)` over one period.
Route: `physMeasure ε c = volume.restrict (univ ×ˢ Ioc 0 (2εc))` (`B0220.physDomain`); the bound
`C²(1+|x|)^{-4}` is integrable on `ℝ³` (`integrable_one_add_norm` with exponent `4 > 3`) and the
`τ`-interval has finite measure (`Measure.prod_restrict`, `Integrable.prod_mul`/`integrable_prod_iff`),
then `MemLp.of_le`/`memLp_two_iff_integrable_sq_norm` with `Continuous.aestronglyMeasurable`. -/
def KF3MemLpDecay : Prop :=
  ∀ (ε c : ℝ) (f : Space × ℝ → Space), Continuous f →
    (∃ C : ℝ, ∀ y : Space × ℝ, ‖f y‖ ≤ C / (1 + ‖y.1‖) ^ 2) →
    MemLp f 2 (UnforcedLeray.B0220.physMeasure ε c)

/-! ## The leaves: slices (step 2) -/

/-- **Leaf: the heat integral of a representative, phase by phase** (bookkeeping for 3613-3616:
`e^{θΔ}F(x, s) = ∫ G_θ(y) F(x - y, s) dy`).  For `V ∈ L²(dx dτ)`, `F = toX hP [V]`: for a.e. phase
`s`, for every `x, θ, i`, the heat integral of `F(·, s)` equals that of `V(·, τ_s)`,
`τ_s = (toCell P (0, s)).2`.
Route: `toX_ae` and `MemLp.coeFn_toLp` (transported by `(mp_toCell_phys hP).quasiMeasurePreserving.ae`)
give `F =ᵐ fun w => cplx3 (V (toCell P w))` on `PSpace P = Space × AddCircle P`, whose volume is
`volume.prod volume`; swap and slice (`Measure.ae_ae_of_ae_prod` after `Measure.prod_swap`, or
`Measure.ae_prod_iff_ae_ae`) to get, for a.e. `s`, `F(·, s) =ᵐ cplx3 (V(·, τ_s))`
(`toCell P (x, s) = (x, τ_s)` by definition).  For fixed `x`, `y ↦ x - y` preserves null sets
(`Measure.measurePreserving_sub_left`), so the integrands agree a.e. (`integral_congr_ae`);
`cplx3_apply`. -/
def KF3Slice : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c) (V : Space × ℝ → Space)
    (hV : MemLp V 2 (UnforcedLeray.B0220.physMeasure ε c)),
    ∀ᵐ s : AddCircle P ∂volume, ∀ (x : Space) (θ : ℝ) (i : Fin 3),
      ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((toX hP (hV.toLp V) : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC)
            (x - y, s)) i =
        ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((V (x - y, (UnforcedLeray.B0223.toCell P (0, s)).2) i : ℝ) : ℂ)

/-! ## The leaves: the heat integral (step 3) -/

/-- **Leaf: the heat integral of `div M`** (source 3617-3618, "integrate the tensor divergence by
parts").  `∫ G_θ(y)(div M)_i(x - y, τ) dy = ∫ Σ_k ∂_kG_θ(x - z) M_{ik}(z, τ) dz`, both integrands
integrable.
Route: substitute `y = x - z` (`integral_sub_left_eq_self`); `(div M)_i = Σ_k ∂_kM_{ik}`
(`cartDiv`); for each `k` integrate by parts (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`;
`M(·, τ)` smooth with compact support): `∂_{z_k}[G_θ(x - z)] = -∂_kG_θ(x - z)` (chain rule).
`heatG θ` is smooth (`heatG_eq_heatKernel`, `UnforcedLeray.Heat.kernel`) and integrable;
continuous × compactly supported continuous is integrable. -/
def KF3HeatDiv : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsOuterTest P M →
    ∀ (τ : ℝ) (x : Space) (θ : ℝ), 0 < θ → ∀ i : Fin 3,
      Integrable (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y * cartDiv M (x - y, τ) i) ∧
      Integrable (fun z : Space => ∑ k : Fin 3,
        fderiv ℝ (UnforcedLeray.Short.IIIa.heatG θ) (x - z) (UnforcedLeray.coordinateVector k) *
          M (z, τ) i k) ∧
      ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y * cartDiv M (x - y, τ) i =
        ∫ z : Space, ∑ k : Fin 3,
          fderiv ℝ (UnforcedLeray.Short.IIIa.heatG θ) (x - z) (UnforcedLeray.coordinateVector k) *
            M (z, τ) i k

/-- **Leaf: the heat tail is smooth for positive time** (source 3597-3601).  For `θ > 0`,
`x ↦ ∫_θ^∞ G_a(x) da` is `C^∞` on all of `ℝ³` (including the origin).
Route: as `IIIa.heatTailIterated` (`PartIII-a/T15_SepKernelBounds/HeatTailIterated.lean`, which
works off the origin with `t ≥ 0`), but with the global bounds
`‖D^mG_a(x)‖ ≤ C_m a^{-(3+m)/2}` (`IIIa.heatGBound`, `HeatGBound`), integrable on `(θ, ∞)` since
`(3+m)/2 > 1`: induction on `m` with `hasFDerivAt_integral_of_dominated_of_fderiv_le`, then
`contDiff_of_differentiable_iteratedFDeriv`. -/
def KF3TailSmooth : Prop :=
  ∀ θ : ℝ, 0 < θ → ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.heatTail θ)

/-- **Leaf: the first derivative of the heat tail** (source 3597-3601).  For `θ > 0`,
`∂_j∫_θ^∞G_a(x) da = ∫_θ^∞ ∂_jG_a(x) da` at every `x`.
Route: `hasFDerivAt_integral_of_dominated_of_fderiv_le` on `Ioi θ` with the bound
`‖DG_a(y)‖ ≤ C_1 a^{-2}` (`IIIa.heatGBound` with `m = 1`), integrable on `(θ, ∞)`; evaluate the
derivative at `e_j` (`ContinuousLinearMap.integral_apply`).  Cf. `IIIa.heatTailStep` (off the
origin). -/
def KF3TailFDeriv : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ (x : Space) (j : Fin 3),
    fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) x (UnforcedLeray.coordinateVector j) =
      ∫ a in Ioi θ, fderiv ℝ (UnforcedLeray.Short.IIIa.heatG a) x (UnforcedLeray.coordinateVector j)

/-- **Leaf: the heat semigroup on a derivative** (source 3613-3616).  `G_θ * ∂_jG_b = ∂_jG_{θ+b}`
for `θ, b > 0`.
Route: `UnforcedLeray.Heat.integral_kernel_product` (`∫ G_s(y)G_t(x - y) dy = G_{s+t}(x)`,
`Analysis/Heat/KernelSemigroup.lean`) with `heatG_eq_heatKernel`; substitute to
`∫ G_θ(y) G_b(x - y) dy` and differentiate in `x` under the integral
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`, `‖DG_b‖ ≤ C b^{-2}` bounded, `G_θ` integrable);
substitute back `y ↦ x - y` (`integral_sub_left_eq_self`). -/
def KF3HeatGConvFDeriv : Prop :=
  ∀ θ b : ℝ, 0 < θ → 0 < b → ∀ (x : Space) (j : Fin 3),
    ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ (x - y) *
        fderiv ℝ (UnforcedLeray.Short.IIIa.heatG b) y (UnforcedLeray.coordinateVector j) =
      fderiv ℝ (UnforcedLeray.Short.IIIa.heatG (θ + b)) x (UnforcedLeray.coordinateVector j)

/-- **Leaf: the heat flow of the Newtonian gradient** (source 3597-3601, 3609-3611:
`∫_0^∞G_a = (4π|x|)⁻¹`, `K_0 = D²(4π|x|)⁻¹`).  `G_θ * ∂_jN = ∂_j∫_θ^∞G_a da` for `θ > 0`
(and the integrand is integrable).
Route: for `y ≠ 0`, `∂_jN(y) = ∫_0^∞ ∂_jG_b(y) db` (`PressureAnalysis.integral_fderiv_heatKernel_time`,
`heatG_eq_heatKernel`, `newtonGradientKernel`); Fubini on `ℝ³ × (0, ∞)`
(Tonelli bound `∫_0^∞|∂_jG_b(y)| db ≤ C|y|^{-2}`, `PressureAnalysis.integral_norm_fderiv_heatKernel_time`,
and `∫ G_θ(x - y)|y|^{-2} dy < ∞`); the inner integral is `∂_jG_{θ+b}(x)` (`KF3HeatGConvFDeriv`);
`∫_0^∞ ∂_jG_{θ+b}(x) db = ∫_θ^∞ ∂_jG_a(x) da` (`integral_comp_add_right`-type shift on `Ioi`) `=
∂_j heatTail θ x` (`KF3TailFDeriv`). -/
def KF3HeatNewtonGrad : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ (x : Space) (j : Fin 3),
    Integrable (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ (x - y) *
      UnforcedLeray.PressureAnalysis.newtonGradientKernel j y) ∧
    ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ (x - y) *
        UnforcedLeray.PressureAnalysis.newtonGradientKernel j y =
      fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) x (UnforcedLeray.coordinateVector j)

/-- **Leaf: the heat flow of a Newtonian convolution** (source 3597-3601, 3617-3618).  For a
spatial test `h` and `θ > 0`, `∫ G_θ(y) (∂_jN ⋆ h)(x - y) dy = ∫ ∂_j(∫_θ^∞G_a)(x - z) h(z) dz`
(and the left integrand is integrable).
Route: unfold `newtonComponent`; Fubini (`integral_integral_swap`; absolute integrability from
`|∂_jN(w)| ≤ (4π)⁻¹|w|^{-2}`, `PressureAnalysis.norm_newtonGradientKernel_le`, `h` bounded with
compact support, `G_θ` integrable and bounded); the inner integral `∫ G_θ(y) ∂_jN(x - z - y) dy`
is `∫ G_θ(x - z - w) ∂_jN(w) dw` (`integral_sub_left_eq_self`) `= ∂_j heatTail θ (x - z)`
(`KF3HeatNewtonGrad`). -/
def KF3HeatNewtonComp : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ h : Space → ℝ, UnforcedLeray.IsSpatialTest h → ∀ (x : Space) (j : Fin 3),
    Integrable (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y *
      UnforcedLeray.PressureAnalysis.newtonComponent j h (x - y)) ∧
    ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y *
        UnforcedLeray.PressureAnalysis.newtonComponent j h (x - y) =
      ∫ z : Space, fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) (x - z)
        (UnforcedLeray.coordinateVector j) * h z

/-- **Leaf: moving the divergences onto the heat tail** (source 3617-3618, "integrate the tensor
divergence by parts").  With `H = ∫_θ^∞G_a`:
`Σ_j ∫ ∂_jH(x - z) ∂_i(div M)_j(z, τ) dz = ∫ Σ_{jk} ∂_k(∂_i∂_jH)(x - z) M_{jk}(z, τ) dz`
(and the right integrand is integrable).
Route: two integrations by parts in `z` (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`;
`M(·, τ)` and its derivatives smooth with compact support, `H` smooth by `KF3TailSmooth`):
`∂_{z_i}[f(x - z)] = -(∂_if)(x - z)`, first with `f = ∂_jH` (`∂_i∂_jH = IIIa.part2 H i j`), then,
after `(div M)_j = Σ_k ∂_kM_{jk}` (`cartDiv`), with `f = part2 H i j` in direction `e_k`. -/
def KF3TailIBP : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsOuterTest P M →
    ∀ (τ : ℝ) (x : Space) (θ : ℝ), 0 < θ → ∀ i : Fin 3,
      Integrable (fun z : Space => ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) (x - z)
          (UnforcedLeray.coordinateVector k) * M (z, τ) j k) ∧
      ∑ j : Fin 3, ∫ z : Space,
          fderiv ℝ (UnforcedLeray.Short.IIIa.heatTail θ) (x - z) (UnforcedLeray.coordinateVector j) *
            fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z (UnforcedLeray.coordinateVector i) =
        ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
          fderiv ℝ (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) (x - z)
            (UnforcedLeray.coordinateVector k) * M (z, τ) j k

/-- **Leaf: the heat integral of the pressure gradient** (source 3597-3601, 3617-3618).
`∫ G_θ(y) ∂_ip(x - y, τ) dy = ∫ Σ_{jk} ∂_k(∂_i∂_j∫_θ^∞G_a)(x - z) M_{jk}(z, τ) dz`, both integrands
integrable.
Route: `KF3PresGrad` writes `∂_ip(·, τ) = Σ_j ∂_jN ⋆ h_j` with `h_j = ∂_i(div M)_j(·, τ)`, an
`IsSpatialTest` (smooth slice of a smooth function, support in the ball of `IsOuterTest.bounded`);
split the finite sum (`integral_finset_sum`, integrability from `KF3HeatNewtonComp`), apply
`KF3HeatNewtonComp` to each `h_j`, and conclude with `KF3TailIBP`. -/
def KF3HeatPres : Prop :=
  ∀ (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ), IsOuterTest P M →
    ∀ (τ : ℝ) (x : Space) (θ : ℝ), 0 < θ → ∀ i : Fin 3,
      Integrable (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y *
        UnforcedLeray.B0226.gradX (lerayPres M) (x - y, τ) i) ∧
      Integrable (fun z : Space => ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) (x - z)
          (UnforcedLeray.coordinateVector k) * M (z, τ) j k) ∧
      ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y *
          UnforcedLeray.B0226.gradX (lerayPres M) (x - y, τ) i =
        ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
          fderiv ℝ (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) (x - z)
            (UnforcedLeray.coordinateVector k) * M (z, τ) j k

/-- **Leaf: the gradient of the heat-Leray kernel** (source 3597-3601).  For `θ > 0`,
`∂_k(K_θ)_{ij} = δ_{ij}∂_kG_θ + ∂_k(∂_i∂_j∫_θ^∞G_a)`.
Route: unfold `IIIa.heatLerayK`; `fderiv_add` (both summands differentiable: `heatG θ` is smooth,
`heatG_eq_heatKernel`; `part2 (heatTail θ) i j` is smooth since `heatTail θ` is, `KF3TailSmooth`,
`ContDiff.fderiv_right`, `ContDiff.clm_apply`); split on `i = j` (`fderiv_const` when `i ≠ j`). -/
def KF3FDerivK : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ (i j k : Fin 3) (x : Space),
    fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK θ i j y) x
        (UnforcedLeray.coordinateVector k) =
      (if i = j then
          fderiv ℝ (UnforcedLeray.Short.IIIa.heatG θ) x (UnforcedLeray.coordinateVector k)
        else 0) +
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) x
          (UnforcedLeray.coordinateVector k)

/-! ## Assembly -/

/-- The outer field of a smooth Cartesian tensor is a smooth outer tensor. -/
theorem isOuterTest_outerField {P R : ℝ} (hR : R ≠ 0)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hT : IsCartTest P T) :
    IsOuterTest P (outerField R T) where
  smooth i j := by
    have hL : ContDiff ℝ ∞ (fun y : Space × ℝ => ((R • y.1, y.2) : Space × ℝ)) :=
      (contDiff_fst.const_smul R).prodMk contDiff_snd
    exact (hT.smooth i j).comp hL
  periodic x τ := hT.periodic τ (R • x)
  bounded := by
    obtain ⟨r, hr⟩ := hT.bounded
    refine ⟨r / |R|, fun y hy => ?_⟩
    have h1 := hr y.2 (R • y.1) hy
    rw [norm_smul, Real.norm_eq_abs] at h1
    rw [le_div_iff₀ (abs_pos.2 hR)]
    linarith [mul_comm (|R|) ‖y.1‖]

theorem cartDiv_periodic {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hM : ∀ (x : Space) (τ : ℝ), M (x, τ + P) = M (x, τ)) (x : Space) (τ : ℝ) :
    cartDiv M (x, τ + P) = cartDiv M (x, τ) := by
  unfold cartDiv
  simp only [hM]

theorem lerayPres_periodic {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hM : ∀ (x : Space) (τ : ℝ), M (x, τ + P) = M (x, τ)) (x : Space) (τ : ℝ) :
    lerayPres M (x, τ + P) = lerayPres M (x, τ) := by
  unfold lerayPres
  simp only [cartDiv_periodic hM]

/-- Divergence free in the `L²(dx dτ)` sense from the slice identity (Fubini). -/
theorem kf3Sol_of (h : KF3SolSlice) (ε c : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hMo : IsOuterTest (2 * ε * c) M) (φ : UnforcedLeray.B0226.PhysTest ε c) :
    ∫ y, inner ℝ (lerayField M y) (UnforcedLeray.B0226.gradX φ.1 y)
      ∂UnforcedLeray.B0220.physMeasure ε c = 0 := by
  set f : Space × ℝ → ℝ := fun y => inner ℝ (lerayField M y) (UnforcedLeray.B0226.gradX φ.1 y)
    with hf
  have hm : UnforcedLeray.B0220.physMeasure ε c =
      ((volume : Measure Space).restrict univ).prod
        ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  rw [hm]
  by_cases hi : Integrable f (((volume : Measure Space).restrict univ).prod
      ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))))
  · rw [integral_prod_symm f hi]
    have h0 : ∀ τ : ℝ, ∫ x, f (x, τ) ∂(volume : Measure Space).restrict univ = 0 := fun τ => by
      rw [Measure.restrict_univ]
      exact h _ M hMo φ.1 φ.2 τ
    simp only [h0, integral_zero]
  · exact integral_undef hi

/-- **(a)**: `P_3D div M = div M + ∇ₓp`. -/
theorem p3d_cartDiv_eq (hPS : KF3PresSmooth) (hPD : KF3PresDecay) (hGO : KF3GradOrth)
    (hSS : KF3SolSlice) (hML : KF3MemLpDecay) {ε c : ℝ} (hP : 0 < 2 * ε * c)
    {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hMo : IsOuterTest (2 * ε * c) M)
    (hM : MemLp (cartDiv M) 2 (UnforcedLeray.B0220.physMeasure ε c)) :
    ∃ hV : MemLp (lerayField M) 2 (UnforcedLeray.B0220.physMeasure ε c),
      UnforcedLeray.B0226.P3D ε c (hM.toLp (cartDiv M)) = hV.toLp (lerayField M) := by
  have hp : ContDiff ℝ ∞ (lerayPres M) := hPS _ M hMo
  obtain ⟨C, hC⟩ := hPD _ M hP hMo
  have hGm : MemLp (UnforcedLeray.B0226.gradX (lerayPres M)) 2
      (UnforcedLeray.B0220.physMeasure ε c) :=
    hML ε c _ (UnforcedLeray.B0226.continuous_gradX hp) ⟨C, fun y => (hC y).2⟩
  have hVm : MemLp (lerayField M) 2 (UnforcedLeray.B0220.physMeasure ε c) := hM.add hGm
  refine ⟨hVm, ?_⟩
  have hS : hVm.toLp (lerayField M) ∈ UnforcedLeray.B0226.physSolenoidal ε c := by
    rw [UnforcedLeray.B0226.mem_physSolenoidal_iff]
    intro φ
    rw [← kf3Sol_of hSS ε c M hMo φ]
    refine integral_congr_ae ?_
    filter_upwards [hVm.coeFn_toLp] with y hy
    rw [hy]
  have hO : hGm.toLp (UnforcedLeray.B0226.gradX (lerayPres M)) ∈
      (UnforcedLeray.B0226.physSolenoidal ε c)ᗮ :=
    hGO ε c (lerayPres M) hp (lerayPres_periodic hMo.periodic) ⟨C, fun y => (hC y).1⟩ hGm
  have hsplit : hM.toLp (cartDiv M) =
      hVm.toLp (lerayField M) - hGm.toLp (UnforcedLeray.B0226.gradX (lerayPres M)) := by
    rw [← MemLp.toLp_sub]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => ?_)
    simp [lerayField]
  rw [hsplit, map_sub, UnforcedLeray.B0226.P3D, Submodule.starProjection_eq_self_iff.mpr hS,
    (Submodule.starProjection_apply_eq_zero_iff
      (K := UnforcedLeray.B0226.physSolenoidal ε c)).mpr hO, sub_zero]

/-- **(b)-(d)**: the heat integral of `P_3D div M` at a phase is `∇K_θ : M` (`convTerm`). -/
theorem heat_lerayField_eq_convTerm (hHD : KF3HeatDiv) (hHP : KF3HeatPres) (hFK : KF3FDerivK)
    {P R : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hMo : IsOuterTest P (outerField R T))
    (τ : ℝ) (x : Space) {θ : ℝ} (hθ : 0 < θ) (i : Fin 3) :
    ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
        ((lerayField (outerField R T) (x - y, τ) i : ℝ) : ℂ) = convTerm θ R T x τ i := by
  obtain ⟨hi1, hi2, he1⟩ := hHD P _ hMo τ x θ hθ i
  obtain ⟨hj1, hj2, he2⟩ := hHP P _ hMo τ x θ hθ i
  have hreal : ∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y *
        lerayField (outerField R T) (x - y, τ) i =
      ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (x - z)
          (UnforcedLeray.coordinateVector k) * T τ (R • z) j k := by
    have e1 : (fun y : Space => UnforcedLeray.Short.IIIa.heatG θ y *
        lerayField (outerField R T) (x - y, τ) i) = fun y =>
          UnforcedLeray.Short.IIIa.heatG θ y * cartDiv (outerField R T) (x - y, τ) i +
          UnforcedLeray.Short.IIIa.heatG θ y *
            UnforcedLeray.B0226.gradX (lerayPres (outerField R T)) (x - y, τ) i := by
      funext y
      simp only [lerayField, Pi.add_apply, PiLp.add_apply, mul_add]
    rw [e1, integral_add hi1 hj1, he1, he2, ← integral_add hi2 hj2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFK θ hθ, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have hL : ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
        ((lerayField (outerField R T) (x - y, τ) i : ℝ) : ℂ) =
      ((∫ y : Space, UnforcedLeray.Short.IIIa.heatG θ y *
        lerayField (outerField R T) (x - y, τ) i : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have hR : convTerm θ R T x τ i = ((∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (x - z)
          (UnforcedLeray.coordinateVector k) * T τ (R • z) j k : ℝ) : ℂ) := by
    rw [convTerm, ← integral_complex_ofReal]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hL, hR, hreal]

/-- **`KF3` from the leaves.** -/
theorem kf3_of (hPS : KF3PresSmooth) (hPD : KF3PresDecay) (hGO : KF3GradOrth)
    (hSS : KF3SolSlice) (hML : KF3MemLpDecay) (hSl : KF3Slice) (hHD : KF3HeatDiv)
    (hHP : KF3HeatPres) (hFK : KF3FDerivK) : KF3 := by
  intro ν ε c P _ hν hε hc hP T hT hM
  have hPpos : 0 < P := Fact.out
  have hMo : IsOuterTest P (outerField ε⁻¹ T) := isOuterTest_outerField (inv_ne_zero hε.ne') hT
  have hMo' : IsOuterTest (2 * ε * c) (outerField ε⁻¹ T) := hP ▸ hMo
  obtain ⟨hVm, hP3D⟩ := p3d_cartDiv_eq hPS hPD hGO hSS hML (hP ▸ hPpos) hMo' hM
  filter_upwards [hSl ε c P hP _ hVm] with s hs
  intro x θ hθ i
  rw [hP3D, hs x θ i]
  exact heat_lerayField_eq_convTerm hHD hHP hFK hMo _ x hθ i

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
