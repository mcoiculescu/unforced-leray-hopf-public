import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs

/-!
# `WardYPointDom`: the phase-lag kernels and the leaves of the pointwise domination

Source `the November 2 reference manuscript` 3600-3621 (`sep:kernel`,
`sep:resolvent`), 3700-3713 (the factor `1 - λ²` of `X₀`, "It costs no inverse"), 4161-4205 (the
Ward fields, the outward primitive, `ward:shifted-resolvent`), 5585-5593 (the bin bound).

## The phase-lag form of `sep:resolvent`

In `sep:resolvent` (3611-3617) substitute `σ = τ + 2 log λ`, i.e. `λ = e^{-h/2}` with the phase lag
`h = τ - σ > 0`, `dλ = (λ/2) dσ`.  Then
`W_μ(y,τ) = ∫_{σ<τ} ∫ wKer(τ-σ, y - λz) : T(z,σ) dz dσ` and
`X₀ = W_μ - W_{μ+1} = ∫_{σ<τ} ∫ xKer(τ-σ, y - λz) : T(z,σ) dz dσ` with

* `wKer ν μ h x M = -λ^{2μ+3} (∇K_{ν(1-λ²)}(x) : M)`,
* `xKer ν μ h x M = -(λ^{2μ+3} - λ^{2μ+5}) (∇K_{ν(1-λ²)}(x) : M)` (the factor `1 - λ²`, 3708);

the source time `σ` no longer moves with `τ`, so `∂_τ` falls on the kernel only, and the factor
`1 - λ²` makes the kernel vanish at `h = 0` (no boundary term, 3708-3709, 4198-4201).
`(∇K_t(x) : M)_i = ∑_{j,k} ∂_k(K_t)_{ij}(x) M_{jk}` as in `IIIa.sepW`.

The outward primitive (4178-4179) and the stream cutoff (4180-4186) act on the kernel:
`sKer` is `Ψ` of the `X₀`-kernel, `fullKer` is the kernel of `X = 𝒞_y X₀` (same formula as
`wardStreamCut`).

## The kernel form of `ward:shifted-resolvent`

`D_{μ+1} = ∂_h - ½ x·∇_x - νΔ_x + μ + ½` applied to `xKer` (as a function of `(h, x)`) is exactly
`wKer` (`PDKerShifted`; heat equation `∂_tK_t = ΔK_t` and the parabolic homogeneity
`x·∇F + 2t∂_tF = -4F` of `F = ∇K_t`): this is `D_{μ+1}X₀ = W_μ` (4198-4201) kernel by kernel,
and it is why the transport `-½ y·∇` costs nothing (the `y`- and `λz`-parts recombine into
`x = y - λz`).

## Leaves

* `PDKerShifted`, `PDKerBounds` : the kernel identity and the order-four bounds (3604-3610);
* `ParamDmuCausal` : `D_{μ+1}` under a causal (`σ < τ`) parametric integral;
* `PDX0Rep`, `PDOutPrimRep` : `wardX0` and its outward primitive in phase-lag form;
* `PDSourceFinite` : finiteness of the majorants at one point controls a neighbourhood
  (periodicity of `oldPhys` in the phase);
* `PDFullKerReg` : regularity and crude bounds of `fullKer`;
* `PDYRep` : `Y(τ,y) = ∫_{σ<τ} D_{μ+1}[fullKer](τ-σ, y, z) : T(z,σ)`;
* `PDYKerBound` : `|D_{μ+1}[fullKer]| ≤ C λ^{2μ+3}(|y-λz|^{-4} + ϱ^{-2}(ϱ² + (y₃-λz₃)²)^{-1})|M|`;
* `PDSigmaToLambda` : back from the phase-lag form to the `λ`-form of the majorants.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Kernels -/

/-- The dilation `λ = e^{-h/2}` of `sep:resolvent` at phase lag `h = τ - σ` (source 3611-3617). -/
def pdLam (h : ℝ) : ℝ := Real.exp (-(h / 2))

/-- The contraction `(∇K_t(x) : M)_i = ∑_{j,k} ∂_k(K_t)_{ij}(x) M_{jk}` (source 3611-3617, as in
`IIIa.sepW`). -/
def gradKCon (t : ℝ) (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) : Space :=
  WithLp.toLp 2 fun i => ∑ j : Fin 3, ∑ k : Fin 3,
    fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x (coordinateVector k) * M j k

/-- Phase-lag kernel of `W_μ` (source 3611-3617 with `σ = τ + 2 log λ`):
`-λ^{2μ+3} (∇K_{ν(1-λ²)}(x) : M)`, `λ = e^{-h/2}`. -/
def wKer (ν μ h : ℝ) (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) : Space :=
  (-(pdLam h ^ (2 * μ + 3))) • gradKCon (ν * (1 - pdLam h ^ 2)) x M

/-- Phase-lag kernel of `X₀ = W_μ - W_{μ+1}` (source 3611-3617, 3708 the factor `1 - λ²`, 4171):
`-(λ^{2μ+3} - λ^{2μ+5}) (∇K_{ν(1-λ²)}(x) : M)`. -/
def xKer (ν μ h : ℝ) (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) : Space :=
  (-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))) • gradKCon (ν * (1 - pdLam h ^ 2)) x M

/-- The outward primitive of the `X₀`-kernel (source 4178-4179, `Ψ_Z(r,z) = -∫_r^∞ ρ Z_z dρ` on the
half plane `φ = 0`), for a source point `z` with tensor `M` at phase lag `h`. -/
def sKer (ν μ h r y3 : ℝ) (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -∫ ρ in Ioi r, ρ * xKer ν μ h (!₂[ρ, 0, y3] - pdLam h • z) M 2

/-- The kernel of `X = 𝒞_y X₀` (source 4171, 4180-4186; the formula of `wardStreamCut`). -/
def fullKer (ν μ R : ℝ) (χy : ℝ → ℝ) (h : ℝ) (y z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Space :=
  χy (ν * age R y) • xKer ν μ h (y - pdLam h • z) M +
    (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y * sKer ν μ h (ϱ y) (y 2) z M) •
      coordinateVector 2

/-- The crude source weight used for domination near a receiver: `λ^{2μ+3}((1+λ|z|)^{-4} +
(1+(λz₃)²)^{-1})`, `λ = e^{-h/2}` (order-four kernel and its outward primitive, receiver in a
compact set off the old disk). -/
def srcWeight (μ h : ℝ) (z : Space) : ℝ :=
  pdLam h ^ (2 * μ + 3) * (((1 + pdLam h * ‖z‖) ^ 4)⁻¹ + (1 + (pdLam h * z 2) ^ 2)⁻¹)

/-! ## 2. Kernel leaves -/

/-- **`ward:shifted-resolvent` kernel by kernel** (source 4198-4201, 3604-3610, 3708-3709):
`(∂_h - ½x·∇_x - νΔ_x + μ + ½) xKer = wKer` for `h > 0`, i.e.
`physDmu ν (μ+1)` of `(h, x) ↦ xKer ν μ h x M` is `wKer ν μ h x M`.  Proof: with
`F = ∇K_t : M`, `t = ν(1-λ²)`, `∂_hλ = -λ/2`, `∂_ht = νλ²`; the heat equation `∂_tK_t = ΔK_t` (from
`K_t = δG_t + ∂∂∫_t^∞G_a da`, `∂_tG = ΔG`) and the homogeneity `K_t(x) = t^{-3/2}K_1(x/√t)`
(`HeatLerayScale`), which gives `x·∇F = -2t∂_tF - 4F`; the `∂_tF` terms cancel
(`νλ² + t - ν = 0`) and the `F` terms sum to `-λ^{2μ+3}F`. -/
def PDKerShifted : Prop :=
  ∀ (ν μ h : ℝ), 0 < ν → 0 < h → ∀ (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ),
    physDmu ν (μ + 1) (fun h' x' => xKer ν μ h' x' M) h x = wKer ν μ h x M

/-- **`sep:kernel` for the phase-lag kernels** (source 3604-3610 with `j ≤ 2`; `∂_t∇K_t = Δ∇K_t`;
`μ ∈ (-1/4, 1]` bounds the `h`-derivative of `λ^{2μ+3} - λ^{2μ+5}` by a multiple of `λ^{2μ+3}`):
smoothness and order-four bounds, uniform in `ν > 0`, `h > 0`, `μ ∈ (-1/4, 1]`. -/
def PDKerBounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
      ContDiff ℝ 2 (fun x' => xKer ν μ h x' M) ∧
      (∀ x : Space, DifferentiableAt ℝ (fun h' => xKer ν μ h' x M) h) ∧
      ∀ x : Space, x ≠ 0 →
        ‖xKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M ∧
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M ∧
        ‖iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M ∧
        ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M ∧
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M

/-! ## 3. Differentiation under the causal integral -/

/-- **`D_{μ'}` under a causal parametric integral** (pure analysis; used for 3611-3621, 4171-4186).
`G(τ, y) = ∫_{e.1 < τ} k(τ - e.1, y, e) de` over `e = (σ, z) ∈ ℝ × Space`.  If the kernel is `C²` in
`y` and differentiable in `h > 0`, tends to `0` as `h ↓ 0`, and it and its derivatives are dominated
near `(τ₀, y₀)` by one integrable `B`, then `physDmu` passes under the integral.  (Time: the
integrand is Lipschitz in `τ` with constant `B e` and differentiable at `τ₀` off the null set
`e.1 = τ₀`, `hasDerivAt_integral_of_dominated_loc_of_lip`; space:
`hasFDerivAt_integral_of_dominated_of_fderiv_le` twice.) -/
def ParamDmuCausal : Prop :=
  ∀ (ν μ' : ℝ) (k : ℝ → Space → ℝ × Space → Space) (τ₀ : ℝ) (y₀ : Space) (ε : ℝ)
    (B : ℝ × Space → ℝ), 0 < ε → Integrable B →
    (∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y ∈ Metric.ball y₀ ε,
      ContDiffAt ℝ 2 (fun y' => k h y' e) y ∧ DifferentiableAt ℝ (fun h' => k h' y e) h) →
    (∀ e : ℝ × Space, ∀ y ∈ Metric.ball y₀ ε, Tendsto (fun h => k h y e) (𝓝[>] 0) (𝓝 0)) →
    (∀ e : ℝ × Space, ∀ τ ∈ Metric.ball τ₀ ε, e.1 < τ → ∀ y ∈ Metric.ball y₀ ε,
      ‖k (τ - e.1) y e‖ ≤ B e ∧ ‖deriv (fun h => k h y e) (τ - e.1)‖ ≤ B e ∧
        ‖fderiv ℝ (fun y' => k (τ - e.1) y' e) y‖ ≤ B e ∧
        ‖iteratedFDeriv ℝ 2 (fun y' => k (τ - e.1) y' e) y‖ ≤ B e) →
    (∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then k (τ - e.1) y e else 0) volume) →
    (∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then deriv (fun h => k h y e) (τ - e.1) else 0) volume) →
    (∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then fderiv ℝ (fun y' => k (τ - e.1) y' e) y else 0)
      volume) →
    (∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space =>
        if e.1 < τ then iteratedFDeriv ℝ 2 (fun y' => k (τ - e.1) y' e) y else 0) volume) →
    physDmu ν μ' (fun τ y => ∫ e : ℝ × Space, if e.1 < τ then k (τ - e.1) y e else 0) τ₀ y₀ =
      ∫ e : ℝ × Space, if e.1 < τ₀ then physDmu ν μ' (fun h y => k h y e) (τ₀ - e.1) y₀ else 0

/-! ## 4. Phase-lag representations -/

/-- **`X₀` in phase-lag form** (source 3611-3617, 3708, 4171): for a receiver `x` off the old disk
(every source point with `T ≠ 0` has `ϱ z < ϱ x`, so `x ≠ λz` for `λ ∈ (0,1)`) and a finite
order-four phase-lag integral, `wardX0 = ∫_{σ<τ} xKer(τ-σ, x - λz) : T(σ,z)`.  (`sepW_eq_integral`,
the change of variables `l = e^{-(τ-σ)/2}`, `(l:ℂ)^{2μ+2} = l^{2μ+2}` for `l > 0`, linearity and
the real part.) -/
def PDX0Rep : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → μ ≤ 1 →
    Measurable g →
    ∀ (τ : ℝ) (x : Space), (∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < ϱ x) →
      ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
          (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ →
      wardX0 ν μ R c g τ x = ∫ e : ℝ × Space,
        if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)
        else 0

/-- **The outward primitive in phase-lag form** (source 4178-4186 "The separated-kernel estimates
prove convergence of this primitive"): for `r > 0` beyond every source radius and a finite
`ρ`-weighted phase-lag integral, `outPrim (wardX0) τ r y₃ = ∫_{σ<τ} sKer(τ-σ, r, y₃, z) : T(σ,z)`
(`PDX0Rep` at each `(ρ, 0, y₃)`, `ρ > r`, and Fubini). -/
def PDOutPrimRep : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → μ ≤ 1 →
    Measurable g →
    ∀ (τ r y3 : ℝ), 0 < r → (∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < r) →
      ∫⁻ ρ in Ioi r, ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
          (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) * (‖!₂[ρ, 0, y3] - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
          else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ →
      outPrim (wardX0 ν μ R c g) τ r y3 = ∫ e : ℝ × Space,
        if e.1 < τ then sKer ν μ (τ - e.1) r y3 e.2 (oldPhys R c g e.1 e.2) else 0

/-- **Back to the `λ`-form** (change of variables `σ = τ + 2 log λ`, `dσ = 2dλ/λ`): for measurable
`Φ`, `∫_{σ<τ} λ Φ(σ, z) = 2 ∫₀¹ ∫ Φ(τ + 2 log λ, z)`, `λ = e^{-(τ-σ)/2}`. -/
def PDSigmaToLambda : Prop :=
  ∀ (τ : ℝ) (Φ : ℝ × Space → ℝ≥0∞), Measurable Φ →
    ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0) * Φ e =
      2 * ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, Φ (τ + 2 * Real.log l, z)

/-- **Finiteness spreads to a neighbourhood** (source 2667 the period `P = 2c/R` of the lift;
3631-3646 the dilated source).  At a young receiver `y₀` (`0 < ϱ y₀`, `ν·age ≤ 1`), if the two
majorants are finite at `(τ₀, y₀)`, then for every `ε > 0` the crude source weight is integrable
against `|𝒩_T g|` over `σ < τ₀ + ε`.  (For `σ < τ₀`: `|y₀ - λz| ≤ C(1 + λ|z|)` and
`ϱ(y₀)²(ϱ(y₀)² + (y₀₃ - λz₃)²) ≤ C(1 + (λz₃)²)`, `λ^{2μ+3} ≤ λ`, `PDSigmaToLambda`; sources outside
`ϱ z < θ ϱ y₀` vanish; for `σ ∈ [τ₀, τ₀+ε)` the periodicity `oldPhysPeriodic` moves the source by
whole periods into `σ < τ₀`, where `λ` changes by a bounded factor.) -/
def PDSourceFinite : Prop :=
  ∀ (ν μ R c δ : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → μ ≤ 1 →
    0 < δ → δ < Real.log (12 / 11) → Measurable g → (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) →
    ∀ (τ₀ : ℝ) (y₀ : Space), 0 < ϱ y₀ → ν * age R y₀ ≤ 1 →
      wardYKerMaj R c (Real.exp (-(δ / 2))) g τ₀ y₀ +
          wardYStreamMaj R c (Real.exp (-(δ / 2))) g τ₀ y₀ < ⊤ →
      ∀ ε : ℝ, 0 < ε →
        ∫⁻ e : ℝ × Space, (if e.1 < τ₀ + ε then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2)
          else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤

/-- **Regularity and crude bounds of `fullKer`** (source 3604-3610, 4178-4186): for receivers in
`{r₁ < ϱ y, ‖y‖ < Y}` and sources in the disk `ϱ z ≤ ρ₀ < r₁`, the kernel is `C²` in `y`,
differentiable in `h > 0`, tends to `0` as `h ↓ 0` (factor `1 - λ²`), and it, its `h`-derivative
and its first two `y`-derivatives are bounded by `C · srcWeight · |M|` (`|y - λz| ≥ c(1 + λ|z|)`
across the gap; `∫_r^∞ ρ |(ρ,0,y₃) - λz|^{-4-j} dρ ≤ C(1 + (λz₃)²)^{-1}`; the `h`-derivative at
fixed `y` brings `λz·∇`, and `λ|z| ≤ |y - λz| + Y`). -/
def PDFullKerReg : Prop :=
  ∀ (ν μ R : ℝ) (χy : ℝ → ℝ), 0 < ν → 0 < R → -(1 / 4) < μ → μ ≤ 1 → IsYoungCutoff χy →
    ∀ (r₁ ρ₀ Y : ℝ), 0 ≤ ρ₀ → ρ₀ < r₁ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ), ϱ z ≤ ρ₀ → ∀ y : Space, r₁ < ϱ y → ‖y‖ < Y →
        Tendsto (fun h => fullKer ν μ R χy h y z M) (𝓝[>] 0) (𝓝 0) ∧
        ∀ h : ℝ, 0 < h →
          ContDiffAt ℝ 2 (fun y' => fullKer ν μ R χy h y' z M) y ∧
          DifferentiableAt ℝ (fun h' => fullKer ν μ R χy h' y z M) h ∧
          ‖fullKer ν μ R χy h y z M‖ ≤ C * srcWeight μ h z * IIIa.tensorNorm M ∧
          ‖deriv (fun h' => fullKer ν μ R χy h' y z M) h‖ ≤
            C * srcWeight μ h z * IIIa.tensorNorm M ∧
          ‖fderiv ℝ (fun y' => fullKer ν μ R χy h y' z M) y‖ ≤
            C * srcWeight μ h z * IIIa.tensorNorm M ∧
          ‖iteratedFDeriv ℝ 2 (fun y' => fullKer ν μ R χy h y' z M) y‖ ≤
            C * srcWeight μ h z * IIIa.tensorNorm M

/-- **`Y` in phase-lag form** (source 4171, 4180-4186, 3611-3621; assembly of `ParamDmuCausal`,
`PDX0Rep`, `PDOutPrimRep`, `PDSourceFinite`, `PDFullKerReg`): at a young receiver with finite
majorants, `Y(τ,y) = ∫_{σ<τ} D_{μ+1}[fullKer](τ - σ, y, z) : T(σ, z)`.  (`wardX` agrees with the
causal integral of `fullKer` on the slices `{y} × (τ-ε, τ+ε)` and `{τ} × B(y, ε)`, where every
receiver lies beyond the old disk `ϱ z ≤ R√(5ν/6)`; `physDmu` depends only on these slices.) -/
def PDYRep : Prop :=
  ∀ (ν μ R c δ : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3), 0 < ν → 1 ≤ R → 0 < c → -(1 / 4) < μ →
    μ ≤ 1 → IsYoungCutoff χy → 0 < δ → δ < Real.log (12 / 11) → Measurable g →
    (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) →
    ∀ (τ : ℝ) (y : Space), 0 < ϱ y → ν * age R y ≤ 1 →
      wardYKerMaj R c (Real.exp (-(δ / 2))) g τ y +
          wardYStreamMaj R c (Real.exp (-(δ / 2))) g τ y < ⊤ →
      wardY ν μ R c χy g τ y = ∫ e : ℝ × Space, if e.1 < τ then
        physDmu ν (μ + 1) (fun h y' => fullKer ν μ R χy h y' e.2 (oldPhys R c g e.1 e.2))
          (τ - e.1) y else 0

/-- **The kernel bound for `Y`** (source 4198-4205, 3700-3713, 4178-4186, 5592).  For a young
receiver (`0 < ϱ y`, `ν·age ≤ 1`, so `ϱ y ≥ R√ν`) and a source point in the old disk
`ϱ z ≤ √(5/6) ϱ y`: `|D_{μ+1}[fullKer]| ≤ C λ^{2μ+3}(|y-λz|^{-4} + ϱ^{-2}(ϱ² + (y₃-λz₃)²)^{-1})|M|`,
`C` depending only on the cutoff (`R ≥ 1` gives `νϱ^{-2} ≤ R^{-2} ≤ 1`).  The `χ_y X₀` part is
`χ_y wKer` (`PDKerShifted`) plus commutators `-½(y·∇χ)`, `-νΔχ`, `-2ν∇χ·∇` (each `≤ C|x|^{-4}`); in
the stream part `(χ_y'/r)Ψ e_z`, `(∂_h - ½y·∇)Ψ` is `Ψ` of `(∂_h - ½x·∇_x)xKer = wKer + νΔxKer -
(μ+½)xKer` minus `Ψ` (dilation `ρ ↦ e^sρ`), and every `Ψ` of an order-`(4+j)` kernel is
`≤ C ϱ^{-j}(ϱ² + h²)^{-1}` by `∫_r^∞ ρ((ρ - √(5/6)r)² + h²)^{-2} dρ`. -/
def PDYKerBound : Prop :=
  ∀ χy : ℝ → ℝ, IsYoungCutoff χy → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ R : ℝ), 0 < ν → 1 ≤ R → -(1 / 4) < μ → μ ≤ 1 →
      ∀ (h : ℝ), 0 < h → ∀ (y z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ), 0 < ϱ y →
        ν * age R y ≤ 1 → ϱ z ≤ Real.sqrt (5 / 6) * ϱ y →
        ‖physDmu ν (μ + 1) (fun h' y' => fullKer ν μ R χy h' y' z M) h y‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖y - pdLam h • z‖ ^ 4)⁻¹ +
            (ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - pdLam h * z 2) ^ 2))⁻¹) * IIIa.tensorNorm M

/-! ## 5. Support, window, and the uniform pointwise statement -/

/-- **(c) Support of the old source at a young receiver** (source 4163-4167: `χ_o = 0` for
`s ≤ 1.2/ν`, `χ_y = 0` for `s ≥ 1/ν`; the old disk `r ≤ R√(ν/1.2)` is separated from the young
receiver `r ≥ R√ν`): if `ν·age R y ≤ 1` then `oldPhys R c g σ z = 0` whenever
`ϱ z > √(5/6) ϱ y` (then `chartOf`'s age `R²/ϱ(z)² < 6/(5ν)`, where `g = 0`). -/
def PDSupport : Prop :=
  ∀ (ν R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) →
    ∀ y : Space, 0 < ϱ y → ν * age R y ≤ 1 →
      ∀ (σ : ℝ) (z : Space), Real.sqrt (5 / 6) * ϱ y < ϱ z → oldPhys R c g σ z = 0

/-- **The radial gap is automatic** (source 5588-5589, `e^δ < 12/11 < 6/5`):
`√(5/6) < θ = e^{-δ/2}` for `δ < log(12/11)`. -/
def PDTheta : Prop :=
  ∀ δ : ℝ, δ < Real.log (12 / 11) → Real.sqrt (5 / 6) < Real.exp (-(δ / 2))

/-- **The window stays below `1`** (source 5946, `μ_n(z) = σ₀ + z/(2|log ν_n|)`, `σ₀ < 1/4`). -/
def MuWinLeOne : Prop :=
  ∀ (D : SeqData) {dm dp : ℝ}, D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ≤ 1

/-- **(e) The pointwise domination, uniformly** (source 5585-5589, 4161-4205): for a young cutoff
`χy` one constant serves every `ν > 0`, `R ≥ 1`, `c > 0`, `μ ∈ (-1/4, 1]`, `δ ∈ (0, log(12/11))`.
(`ν·age > 1`: `wardY_eq_zero_of_one_lt`; majorants infinite: trivial; otherwise `PDYRep`,
`PDYKerBound` on the support `PDSupport`, `λ^{2μ+3} ≤ λ`, `PDSigmaToLambda`, `PDTheta` for the
region `ϱ z < θ ϱ y` of the majorants; `C = 2C₀ + 1`, `k = 0`.) -/
def WardYPointDomUniform : Prop :=
  ∀ χy : ℝ → ℝ, IsYoungCutoff χy → ∃ (C : ℝ) (k : ℕ),
    ∀ (ν μ R c δ : ℝ), 1 ≤ R → μ ≤ 1 → WardYPointDom ν μ R c δ χy C k

end UnforcedLeray.Short.PartIIIb.Concrete

end
