import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, task `PartII-b:T12/7` (`DuhamelEquation`): conditional assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the causal
formula `T_0F(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} P_0F(t) dt/t`, which solves
`(μ + S - νsΔ_{q,η}) b = P_0F`). Target: `DuhamelEquation` (`Sub/T12.lean`), unchanged.

## Route

Fix `1 < r < 3`, `a_r > 0`, `G ∈ H_r` with `b = flatDuhamel ν μ G ∈ H_r`, and a planar solenoidal
test `Ψ`. Write `P = flatTranspose ν μ Ψ` and `h_{t,s} = flatHeat (ν (s - t)) (G(t, ·))`.

1. *Integrability* of `b·P` and of `cdot G Ψ`: both `b` and `G` are in `H_r`, and `P_i`, `Ψ_i` are
   continuous, compactly supported in `{s > 0}`. This is `deqIntegrableMul` (proved below from the
   accepted box integrability `hrBoxIntegrable`, `PartII-b:T11/1/4`) together with
   `deqTransposeTest` (`P_i` is such a test; proved below).
2. *Fubini*. `DeqSwap` (which uses the absolute integrability `DeqAbsIntegrable`, i.e. `a_r > 0`)
   turns `∫ b·P` into the iterated integral `∫_t t⁻¹ ∫_{s>t} (t/s)^μ ∫_z h_{t,s}·P(s,z)`.
3. *Slice identity*. For a.e. `t > 0` (`DeqSliceAe`: the slice `G(t, ·)` is a periodic `L^r`
   function), `DeqSliceIdentity` says that the inner `s`-integral is `t ∫_z G(t,z)·Ψ(t,z)`; it is the
   fundamental theorem of calculus in `s` for `φ(s) = s^{1-μ}⟨h_{t,s}, Ψ(s)⟩`, with `φ' = -s^{-μ}⟨h,
   PΨ⟩` (self-adjointness `DeqHeatSymm`, derivative of the smoothed pairing `DeqPairDeriv` from the
   heat equation `DeqHeatDeriv`) and boundary value `t^{1-μ}⟨G(t), Ψ(t)⟩` at `s = t+`
   (`DeqHeatPair`).
4. *Closing*: `t⁻¹ · t = 1`, then Fubini on `Coord = ℝ × (ℝ × ℝ)` for the integrable `cdot G Ψ`,
   `Ψ = 0` for `s ≤ 0`.

## Proved here

`duhamelEquation_of`: `DuhamelEquation` from `DeqSliceAe`, `DeqSliceIdentity` and `DeqSwap` (the
Props below; the remaining Props `DeqHeatDeriv`, `DeqHeatSymm`, `DeqHeatPair`, `DeqPairDeriv`,
`DeqAbsIntegrable` are inputs of the leaf tasks proving `DeqSliceIdentity` and `DeqSwap`, not
hypotheses of `duhamelEquation_of`).
`deqIntegrableMul` and `deqTransposeTest` are proved in this file.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## The Props -/

/-- A planar slice `g = G(t, ·)` of an `H_r` profile: `c`-periodic in `q` a.e., a.e. strongly
measurable for Lebesgue measure on the plane, and in `L^r` of the cylinder cell
(`Cyl.avgμ c = c⁻¹ dq dη` on `q ∈ [-c/2, c/2)`, `η ∈ ℝ`). These are the hypotheses of
`FlatHeatContraction` (`Sub/T12.lean`). -/
def DeqSliceGood (c r : ℝ) (g : ℝ × ℝ → CMerid) : Prop :=
  (∀ᵐ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) ∧ AEStronglyMeasurable g volume ∧
    eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤

/-- The `s`-slice pairing `∫_z ⟨e^{ν(s-t)Δ} g, (flatTranspose ν μ Ψ)(s, ·)⟩ dz` (the Lebesgue
integral over the plane `(q, η)`; `Ψ` has compact support). -/
def deqPair (ν : ℝ) (μ : ℂ) (g : ℝ × ℝ → CMerid) (Ψ : Coord → Fin 2 → ℝ) (t s : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ, ∑ i : Fin 2, flatHeat (ν * (s - t)) g z i * flatTranspose ν μ Ψ (s, z) i

/-- The planar Laplacian `∂_q² ψ + ∂_η² ψ` of a scalar function on the plane. -/
def planarLap (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ ψ y (1, 0)) z (1, 0) + fderiv ℝ (fun y => fderiv ℝ ψ y (0, 1)) z (0, 1)

/-- **Leaf `PartII-b:T12/7/1`** (Fubini slices of `H_r`; SP 1900-1903, 1923-1927). For `G ∈ H_r`,
for a.e. `t > 0` the slice `G(t, ·)` is `DeqSliceGood`. Proof: `QPeriodic` is an a.e. statement on
`Coord`, so for a.e. `t` the slice is a.e. periodic (Fubini on the null set); `hMeas c r =
ageμ c (r/2 - 5/2)` is a product of `s^a ds` and `Cyl.avgμ c`, so a strongly measurable
representative of `G` has a.e. strongly measurable `t`-slices on the cell, and periodicity extends
this from the `q`-cell to the plane (compare `redQ`/`redCoord` in
`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`); finally `∫⁻ N(t)^r t^{r/2-5/2} dt < ∞` with
`N(t) = ‖G(t, ·)‖_{L^r(Cyl.avgμ c)}` (Tonelli, `lintegral_ageμ`/`ageMu_eq_withDensity` in
`Tasks/HilbertEnergy/SPeriodic.lean`) forces `N(t) < ∞` for a.e. `t > 0`. -/
def DeqSliceAe : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 1 < r → InHr c r G →
    ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), DeqSliceGood c r (fun z => G (t, z))

/-- `H_r` profiles pair integrably with compactly supported tests (SP 1900-1903). If `G ∈ H_r`
(`r > 1`) and `f` is continuous, compactly supported in `{s > 0}`, then `G_i f` is Lebesgue
integrable on `Coord`. Proved below (`deqIntegrableMul`) from `hrBoxIntegrable`. -/
def DeqIntegrableMul : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 1 < r → InHr c r G →
    ∀ (i : Fin 2) (f : Coord → ℂ), Continuous f → HasCompactSupport f →
      tsupport f ⊆ Ioi (0 : ℝ) ×ˢ univ → Integrable (fun x => G x i * f x)

/-- **Leaf `PartII-b:T12/7/2`** (planar heat equation for a test function; SP 1923-1927; input of
`PartII-b:T12/7/5`). For `ψ` smooth with compact support on the plane and `z` fixed,
`θ ↦ ∫ K_θ(w) ψ(z - w) dw` has derivative `∫ K_θ(w) Δψ(z - w) dw` at every `θ > 0`
(`flatHeatKernel`). Proof: the kernel is `C^∞` in `(θ, w)` for `θ > 0` and solves `∂_θ K = ΔK`
(explicit computation); differentiate under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, Gaussian domination on `[θ/2, 2θ]`), then
integrate by parts twice in `w` (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) to move `Δ`
from `K` to `ψ(z - ·)`. Compare `Tasks/FlatUnique/HeatStream/Cpd.lean` (differentiation under the
Gaussian integral) and `Tasks/FlatUnique/HeatStream/Smooth.lean`. -/
def DeqHeatDeriv : Prop :=
  ∀ (ψ : ℝ × ℝ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ (z : ℝ × ℝ) (θ : ℝ), 0 < θ →
    HasDerivAt (fun θ : ℝ => ∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (z - w))
      (∫ w : ℝ × ℝ, flatHeatKernel θ w * planarLap ψ (z - w)) θ

/-- **Leaf `PartII-b:T12/7/3`** (the heat flow is self-adjoint; SP 1923-1927; input of
`PartII-b:T12/7/6`). For a `DeqSliceGood` slice `g`, `θ > 0` and a continuous compactly supported
test `ψ`: `∫ (e^{θΔ} g)_i ψ dz = ∫ g_i (K_θ ⋆ ψ) dz`. Proof: for a.e. `z` the vector
`w ↦ K_θ(w) g(z - w)` is integrable, so `(flatHeat θ g z) i = ∫ K_θ(w) g_i(z - w) dw`
(`ContinuousLinearMap.integral_comp_comm`); Fubini over `(z, w)` (absolute integrability: `g` is
`q`-periodic with finite cell `L^r` norm, hence uniformly `L^1` on unit boxes, `ψ` has compact
support, `K_θ` is Gaussian; the periodic cell bound
`UnforcedLeray.Cyl.eLpNorm_planarConv_periodic_le` of `Tasks/FlatCausal/FlatHeatContraction.lean`
helps), translation `z ↦ z + w` and the symmetry `K_θ(-w) = K_θ(w)`. -/
def DeqHeatSymm : Prop :=
  ∀ (c r : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ θ : ℝ, 0 < θ → ∀ ψ : ℝ × ℝ → ℝ, Continuous ψ → HasCompactSupport ψ → ∀ i : Fin 2,
      ∫ z : ℝ × ℝ, flatHeat θ g z i * (ψ z : ℂ) =
        ∫ z : ℝ × ℝ, g z i * ((∫ w : ℝ × ℝ, flatHeatKernel θ w * ψ (z - w) : ℝ) : ℂ)

/-- The smoothed slice test `U(s, z) = ∫ K_{ν(s-t)}(w) Ψ_i(s, z - w) dw` (`Ψ_i(s, ·)` smoothed by
the heat kernel of age `ν(s - t)`). -/
def deqSmooth (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (i : Fin 2) (t s : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i

/-- `(∂_s + νΔ_{q,η}) Ψ_i` smoothed by the heat kernel of age `ν(s - t)`: the `s`-derivative of
`deqSmooth` (by the heat equation `∂_θ K = ΔK`). -/
def deqSmoothD (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (i : Fin 2) (t s : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w *
    (cpd 0 (fun y => Ψ y i) (s, z - w) +
      ν * (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w) +
        cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w)))

/-- **Leaf `PartII-b:T12/7/4`** (the heat flow is an approximate identity, with a varying test;
SP 1923-1927; input of `PartII-b:T12/7/6`). For a `DeqSliceGood` slice `g` and a planar test `Ψ`,
`s ↦ ∫ g_i(z) U_i(s, z) dz` tends to `∫ g_i(z) Ψ_i(t, z) dz` as `s → t+`. Proof:
`|U(s, z) - Ψ_i(t, z)| ≤ ∫ K_{ν(s-t)}(w) |Ψ_i(s, z - w) - Ψ_i(t, z)| dw`; `Ψ_i` is uniformly
continuous with compact support, so `U(s, ·) → Ψ_i(t, ·)` uniformly with Gaussian tails
(support in a fixed box `B`; outside `2B` the tail is `≤ C e^{-d²/(8ν(s-t))}`); `g` is `q`-periodic
with finite cell `L^r` norm, hence uniformly `L^1` on unit boxes (periodic `L^r`-cell bound of
`Tasks/FlatCausal/FlatHeatContraction.lean`); dominated convergence or an `ε/3` argument. -/
def DeqHeatPair : Prop :=
  ∀ (ν c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2,
        Tendsto (fun s : ℝ => ∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s z : ℂ)) (𝓝[>] t)
          (𝓝 (∫ z : ℝ × ℝ, g z i * (Ψ (t, z) i : ℂ)))

/-- **Leaf `PartII-b:T12/7/5`** (derivative of the smoothed pairing; SP 1923-1927; uses
`DeqHeatDeriv`; input of `PartII-b:T12/7/6`). For a `DeqSliceGood` slice `g`, a planar test `Ψ` and
`s > t`: `s ↦ ∫ g_i U_i(s, ·)` has derivative `∫ g_i (deqSmoothD)(s, ·)`. Proof: differentiate under
the `z`-integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with a Gaussian-tail
dominating function against the periodic `L^r` slice `g` (uniformly `L^1` on unit boxes); the
`s`-derivative of `U(s, z)` is `∫ ν (ΔK)(ν(s-t), w) Ψ_i(s, z-w) + K ∂_sΨ_i(s, z - w) dw`
(differentiation under the `w`-integral, Gaussian domination, the heat equation `∂_θ K = ΔK`),
and `DeqHeatDeriv` moves `Δ` onto `Ψ_i(s, z - ·)`, where
`Δ_z Ψ_i(s, z) = (cpd 1 ∘ cpd 1 + cpd 2 ∘ cpd 2) Ψ_i (s, z)` (slice/chain rule: compare
`partialDerivSlice` in `Short/PartII-a/Tasks/N02LerayComparison/StreamMember/PartialDerivSlice.lean`). -/
def DeqPairDeriv : Prop :=
  ∀ (ν c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2, ∀ s : ℝ, t < s →
        HasDerivAt (fun s' : ℝ => ∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s' z : ℂ))
          (∫ z : ℝ × ℝ, g z i * (deqSmoothD ν Ψ i t s z : ℂ)) s

/-- **Leaf `PartII-b:T12/7/6`** (slice identity; SP 1923-1927; uses `DeqHeatSymm`, `DeqHeatPair`,
`DeqPairDeriv`). For a `DeqSliceGood` slice `g` at age `t > 0` and a planar solenoidal test `Ψ`,
`∫_t^∞ (t/s)^μ ⟨e^{ν(s-t)Δ} g, (flatTranspose ν μ Ψ)(s)⟩ ds = t ⟨g, Ψ(t)⟩`.
Proof: put `Φ_i(s) = ∫ g_i U_i(s, ·)` and `φ(s) = s^{1-μ} Σ_i Φ_i(s)` for `s > t`. By `DeqHeatSymm`
(applied to the three tests `Ψ_i(s, ·)`, `(cpd 0 Ψ_i)(s, ·)`, `(Δ Ψ_i)(s, ·)`),
`deqPair ν μ g Ψ t s = Σ_i [(μ-1)Φ_i(s) - s ∫ g_i deqSmoothD_i(s, ·)]`
(`flatTranspose = (μ-1)Ψ - sΨ_s - νsΔΨ`), and `DeqPairDeriv` gives
`φ'(s) = (1-μ)s^{-μ} Σ Φ_i + s^{1-μ} Σ ∫ g_i deqSmoothD_i = -s^{-μ} deqPair ν μ g Ψ t s`.
`φ = 0` for `s ≥ H` (compact support of `Ψ`; `U(s, ·) = 0` there), and `φ(s) → t^{1-μ} ⟨g, Ψ(t)⟩`
as `s → t+` by `DeqHeatPair`. The fundamental theorem of calculus on `(t, ∞)`
(`integral_Ioi_of_hasDerivAt_of_tendsto`) and `(t/s)^μ = t^μ s^{-μ}` give the claim. No
solenoidality of `Ψ` is used. -/
def DeqSliceIdentity : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
        ∫ s in Ioi t, (((t / s : ℝ) : ℂ) ^ μ) * deqPair ν μ g Ψ t s =
          (t : ℂ) * ∫ z : ℝ × ℝ, ∑ i : Fin 2, g z i * (Ψ (t, z) i : ℂ)

/-- **Leaf `PartII-b:T12/7/7`** (joint absolute integrability for Fubini; SP 1923-1927, uses
`a_r > 0`). With `κ(t, s) = (t/s)^μ t⁻¹` on `{0 < t < s}`:
`(t, s, z) ↦ |κ(t,s)| ‖e^{ν(s-t)Δ}(G(t, ·))(z)‖ ∑_i |P_i(s, z)|` is Lebesgue integrable on
`ℝ × Coord`, where `P = flatTranspose ν μ Ψ`. Proof: `P` has compact support in
`[σ, H] × [-Q, Q] × [-L, L]`, `σ > 0` (`deqTransposeTest`); Hölder in `z` against the periodic cell
norm and the heat contraction (`Tasks/FlatCausal/FlatHeatContraction.lean`) bound the `z`-integral
by `C ‖G(t, ·)‖_{L^r(Cyl.avgμ c)}` uniformly in `s ∈ [σ, H]`, `s > t`; then
`∫_0^H t^{Re μ - 1} N(t) dt ≤ (∫ t^{(Re μ - 1) r'} t^{-(r/2-5/2)r'/r} dt)^{1/r'} ‖G‖_{H_r} < ∞`
because the exponent is `> -1` exactly when `Re μ + (3/r - 1)/2 > 0`. -/
def DeqAbsIntegrable : Prop :=
  ∀ (r : ℝ), 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
      Integrable (fun p : ℝ × Coord =>
        if 0 < p.1 ∧ p.1 < p.2.1 then
          ‖(((p.1 / p.2.1 : ℝ) : ℂ) ^ μ)‖ * p.1⁻¹ *
            ‖flatHeat (ν * (p.2.1 - p.1)) (fun w => G (p.1, w)) p.2.2‖ *
            ∑ i : Fin 2, ‖flatTranspose ν μ Ψ p.2 i‖
        else 0) volume

/-- **Leaf `PartII-b:T12/7/8`** (Fubini swap; SP 1923-1927; uses `DeqAbsIntegrable`).
`∫ b·P = ∫_{t>0} t⁻¹ ∫_{s>t} (t/s)^μ ∫_z ⟨h_{t,s}, P(s,z)⟩` for `b = flatDuhamel ν μ G`,
`G ∈ H_r`, `a_r > 0`. Proof: `flatDuhamel_eq_integral` (`Tasks/FlatCausal/DuhamelMeasurable.lean`)
writes `b(x)` as `∫_t` of an indicator integrand; pair with `P` (a continuous linear functional
on `CMerid`, `ContinuousLinearMap.integral_comp_comm`, integrability in `t` for a.e. `x` from
`DeqAbsIntegrable` and Fubini `Integrable.prod_right_ae`), swap `x = (s, z)` and `t`
(`integral_integral_swap`, measurability from `stronglyMeasurable_duhamelBody` for a strongly
measurable representative of `G` (`exists_periodic_rep` in
`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`) and `flatDuhamel_congr_of_ae`), and use
`integral_const_mul` to move `t⁻¹ (t/s)^μ` outside. -/
def DeqSwap : Prop :=
  ∀ (r : ℝ), 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
      ∫ x, ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i =
        ∫ t in Ioi (0 : ℝ), ((t⁻¹ : ℝ) : ℂ) * ∫ s in Ioi t, (((t / s : ℝ) : ℂ) ^ μ) *
          deqPair ν μ (fun z => G (t, z)) Ψ t s

/-! ## `flatTranspose Ψ` of a planar test is a test (proved) -/

theorem deqT_cpd_contDiff {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun y => cpd j φ y) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := ContDiff.fderiv_right (m := ∞) hφ (by simp)
  exact h1.clm_apply contDiff_const

theorem deqT_cpd_vanish {U : Set Coord} (hU : IsOpen U) {φ : Coord → ℝ}
    (h : ∀ y ∈ U, φ y = 0) (j : Fin 3) : ∀ y ∈ U, cpd j φ y = 0 := by
  intro y hy
  have hev : φ =ᶠ[𝓝 y] (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact h z hz
  have hd : fderiv ℝ φ y = fderiv ℝ (fun _ : Coord => (0 : ℝ)) y := hev.fderiv_eq
  unfold cpd
  rw [hd, fderiv_const_apply]
  simp

/-- `flatTranspose ν μ Ψ · i` is continuous, vanishes outside `tsupport (Ψ · i)`, hence is compactly
supported in `{s > 0}`. -/
theorem deqTransposeTest (ν : ℝ) (μ : ℂ) {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    (i : Fin 2) :
    Continuous (fun x => flatTranspose ν μ Ψ x i) ∧
      HasCompactSupport (fun x => flatTranspose ν μ Ψ x i) ∧
      tsupport (fun x => flatTranspose ν μ Ψ x i) ⊆ Ioi (0 : ℝ) ×ˢ univ := by
  have hi := hΨ.smooth i
  have hs : ContDiff ℝ ∞ (fun z => Ψ z i) := hi.smooth
  have s0 : Continuous (fun x => cpd 0 (fun y => Ψ y i) x) := (deqT_cpd_contDiff hs 0).continuous
  have s1 : Continuous (fun x => cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x) :=
    (deqT_cpd_contDiff (deqT_cpd_contDiff hs 1) 1).continuous
  have s2 : Continuous (fun x => cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x) :=
    (deqT_cpd_contDiff (deqT_cpd_contDiff hs 2) 2).continuous
  have s3 : Continuous (fun x => Ψ x i) := hs.continuous
  have hcont : Continuous (fun x => flatTranspose ν μ Ψ x i) := by
    unfold flatTranspose
    fun_prop
  -- vanishing off `tsupport`
  have hvan : ∀ x, x ∉ tsupport (fun z => Ψ z i) → flatTranspose ν μ Ψ x i = 0 := by
    intro x hx
    have hU : IsOpen (tsupport (fun z => Ψ z i))ᶜ := (isClosed_tsupport _).isOpen_compl
    have hφ : ∀ y ∈ (tsupport (fun z => Ψ z i))ᶜ, (fun z => Ψ z i) y = 0 :=
      fun y hy => image_eq_zero_of_notMem_tsupport (f := fun z => Ψ z i) hy
    have c0 := deqT_cpd_vanish hU (φ := fun z => Ψ z i) hφ 0 x hx
    have d1 := deqT_cpd_vanish hU (φ := fun y => cpd 1 (fun z => Ψ z i) y)
      (deqT_cpd_vanish hU (φ := fun z => Ψ z i) hφ 1) 1 x hx
    have d2 := deqT_cpd_vanish hU (φ := fun y => cpd 2 (fun z => Ψ z i) y)
      (deqT_cpd_vanish hU (φ := fun z => Ψ z i) hφ 2) 2 x hx
    have e0 : Ψ x i = 0 := hφ x hx
    unfold flatTranspose
    rw [e0, c0, d1, d2]
    simp
  refine ⟨hcont, HasCompactSupport.intro hi.compact (fun x hx => hvan x hx), ?_⟩
  have hsub : tsupport (fun x => flatTranspose ν μ Ψ x i) ⊆ tsupport (fun z => Ψ z i) :=
    closure_minimal (fun x hx => by
      by_contra hxt
      exact hx (hvan x hxt)) (isClosed_tsupport _)
  exact hsub.trans hi.supp

/-- A real coordinate test, viewed as a complex function, is a test for `DeqIntegrableMul`. -/
theorem deq_ofReal_test {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    Continuous (fun x => (φ x : ℂ)) ∧ HasCompactSupport (fun x => (φ x : ℂ)) ∧
      tsupport (fun x => (φ x : ℂ)) ⊆ Ioi (0 : ℝ) ×ˢ univ := by
  refine ⟨Complex.continuous_ofReal.comp hφ.smooth.continuous, ?_, ?_⟩
  · exact HasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) hφ.compact (by simp)
  · exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) (by simp) φ).trans hφ.supp

/-- **`DeqIntegrableMul`** from the accepted box integrability `hrBoxIntegrable`. -/
theorem deqIntegrableMul : DeqIntegrableMul := by
  intro c r G hc hr hG i f hfc hfk hfs
  by_cases hK : (tsupport f).Nonempty
  swap
  · have hf0 : f = 0 := by
      ext x
      by_contra h
      exact hK ⟨x, subset_tsupport f h⟩
    simp [hf0]
  have hcK : IsCompact (tsupport f) := hfk
  obtain ⟨x0, hx0, hmin⟩ := hcK.exists_isMinOn hK
    (f := fun x : Coord => x.1) (continuous_fst (X := ℝ) (Y := ℝ × ℝ)).continuousOn
  have hσ : 0 < x0.1 := (hfs hx0).1
  obtain ⟨C, hC⟩ := hcK.isBounded.exists_norm_le
  have hsub : tsupport f ⊆ Icc x0.1 C ×ˢ (Icc (-C) C ×ˢ Icc (-C) C) := by
    intro x hx
    have h1 : x0.1 ≤ x.1 := isMinOn_iff.mp hmin x hx
    have hn := hC x hx
    have b1 : ‖x.1‖ ≤ C := (norm_fst_le x).trans hn
    have b2 : ‖x.2.1‖ ≤ C := ((norm_fst_le x.2).trans (norm_snd_le x)).trans hn
    have b3 : ‖x.2.2‖ ≤ C := ((norm_snd_le x.2).trans (norm_snd_le x)).trans hn
    rw [Real.norm_eq_abs, abs_le] at b1 b2 b3
    exact ⟨⟨h1, b1.2⟩, ⟨b2.1, b2.2⟩, ⟨b3.1, b3.2⟩⟩
  have hBc : IsCompact (Icc x0.1 C ×ˢ (Icc (-C) C ×ˢ Icc (-C) C)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hint := hrBoxIntegrable c r G hc hr hG x0.1 C C C hσ i
  have h1 := hint.mul_continuousOn hfc.continuousOn hBc
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro x hx
  apply hsub
  apply subset_tsupport
  intro h0
  exact hx (by simp [h0])

/-! ## Conditional assembly -/

/-- **Assembly (fully proved).** `DuhamelEquation` follows from the Fubini slices (`DeqSliceAe`),
the slice identity (`DeqSliceIdentity`) and the Fubini
swap (`DeqSwap`). -/
theorem duhamelEquation_of (h0 : DeqSliceAe) (h4 : DeqSliceIdentity) (h6 : DeqSwap) :
    DuhamelEquation := by
  have h1 := deqIntegrableMul
  intro r hr1 hr3 μ hμ ν c hν hc G hG hb Ψ hΨ
  -- integrability of both pairings
  have hcdot : Integrable (cdot G Ψ) := by
    have hi : ∀ i : Fin 2, Integrable (fun x => G x i * (Ψ x i : ℂ)) := fun i => by
      obtain ⟨a1, a2, a3⟩ := deq_ofReal_test (hΨ.smooth i)
      exact h1 c r G hc hr1 hG i _ a1 a2 a3
    have := (hi 0).add (hi 1)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [cdot, Fin.sum_univ_two]
  have hbP : Integrable
      (fun x => ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i) := by
    have hi : ∀ i : Fin 2,
        Integrable (fun x => flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i) := fun i => by
      obtain ⟨a1, a2, a3⟩ := deqTransposeTest ν μ hΨ i
      exact h1 c r (flatDuhamel ν μ G) hc hr1 hb i _ a1 a2 a3
    have := (hi 0).add (hi 1)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [Fin.sum_univ_two]
  refine ⟨hbP, hcdot, ?_⟩
  -- Fubini swap
  rw [h6 r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ]
  -- the slice identity for a.e. `t > 0`
  have hsl := h0 c r G hc hr1 hG
  have hae : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ((t⁻¹ : ℝ) : ℂ) * ∫ s in Ioi t, (((t / s : ℝ) : ℂ) ^ μ) *
          deqPair ν μ (fun z => G (t, z)) Ψ t s =
        ∫ z : ℝ × ℝ, cdot G Ψ (t, z) := by
    filter_upwards [hsl, ae_restrict_mem measurableSet_Ioi] with t ht htpos
    have ht0 : 0 < t := htpos
    rw [h4 ν μ c r t hν ht0 hc hr1 _ ht Ψ hΨ, ← mul_assoc]
    have : ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) = 1 := by
      rw [Complex.ofReal_inv]
      exact inv_mul_cancel₀ (by exact_mod_cast ht0.ne')
    rw [this, one_mul]
    rfl
  rw [integral_congr_ae hae]
  -- restrict to `t > 0` is harmless: `Ψ = 0` for `t ≤ 0`
  have hz : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → ∫ z : ℝ × ℝ, cdot G Ψ (t, z) = 0 := by
    intro t ht
    have h0' : ∀ z : ℝ × ℝ, cdot G Ψ (t, z) = 0 := by
      intro z
      have hΨ0 : ∀ i : Fin 2, Ψ (t, z) i = 0 := fun i => by
        apply image_eq_zero_of_notMem_tsupport (f := fun x => Ψ x i)
        intro hmem
        exact ht (((hΨ.smooth i).supp hmem).1)
      simp [cdot, hΨ0]
    simp [h0']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  -- Fubini on `Coord = ℝ × (ℝ × ℝ)`
  have hvol : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    rfl
  rw [hvol] at hcdot ⊢
  rw [integral_prod _ hcdot]

end UnforcedLeray.Short.IIb
