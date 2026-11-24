import UnforcedLeray.Short.PartIIb.Sub.T11
import UnforcedLeray.Units.B0284.Defs

/-!
# Part II-b, leaf `PartII-b:T11/3` (`HeatStreamDual`): heat flow of a nice stream (conditional)

Source of record: `the November 2 reference manuscript`, the cylinder heat
semigroup `e^{ν(s-t)Δ}` of the causal formula at line 1924 (`T_0F(s) = ∫_0^s (t/s)^μ
e^{ν(s-t)Δ} P_0F(t) dt/t`); the planar heat kernel `(4πθ)^{-1} exp(-|w|²/(4θ))` is the kernel of
`e^{θΔ}` and is not written out in the source. The facts below are classical properties of Gaussian
convolution; the source does not write them out.

## Witness

`H(τ, q, η) = ∫_{ℝ²} G_{ντ}(w) ζ((q, η) - w) dw` for `τ > 0` (`G_θ = heatKernel2 θ` of
`Units/B0284/Defs.lean`, unit mass, `∂_θ G = ΔG` by `Lib/HeatCylinder/HeatKernelAgeLaplacian.lean`),
and `H = 0` for `τ ≤ 0` (`heatStreamH`).

## Proof structure

All derivatives of a nice stream are again nice (`NiceStreamClosure`), derivatives pass under the
convolution (`HeatConvCpd`), `∂_τ H = νΔH` (`HeatConvEq`), `H` is smooth on `τ > 0`
(`HeatConvSmooth`), `q`-periodic (proved here by the change of variables
`ζ(z + (c, 0) - w) = ζ(z - w)`), and `L^p`-contractive and strongly continuous at `τ = 0` as a
convolution with a unit-mass Gaussian (`HeatConvContraction`, `HeatConvTendsto`, general
`f` continuous, `c`-periodic, `η`-compact). The `L^{r'}` membership of the derivatives of order
`≤ 3` (`HeatDerivMemLp`) follows from a pointwise domination of `D^n H` by finitely many heat flows
of nice streams (`HeatDerivDomination`, induction on `n` using `HeatConvCpd`, `HeatConvEq`) and the
Gaussian `η`-tail of the heat flow of a bounded `η`-compact datum (`HeatConvTail`).

Proved here: `heatStreamDual_of` from `HeatConvSmooth`, `HeatConvCpd`, `NiceStreamClosure`,
`HeatConvEq`, `HeatConvContraction`, `HeatConvTendsto`, `HeatDerivMemLp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The planar heat flow of a stream: `H(τ, z) = ∫ G_{ντ}(w) ζ(z - w) dw` for `τ > 0`, `0` for
`τ ≤ 0`; `G_θ = heatKernel2 θ` is the kernel of `e^{θΔ}` (unit mass, `∂_θ G = ΔG`). -/
def heatStreamH (ν : ℝ) (ζ : ℝ × ℝ → ℝ) (x : Coord) : ℝ :=
  if 0 < x.1 then ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * ζ (x.2 - w)
  else 0

/-- `∂_q ζ`. -/
def qDer (ζ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ ζ p (1, 0)

/-- `∂_η ζ`. -/
def etaDer (ζ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ ζ p (0, 1)

/-- The `i`-th component of `∇^⊥ζ = (∂_ηζ, -∂_qζ)` as a scalar function. -/
def perpGradComp (ζ : ℝ × ℝ → ℝ) : Fin 2 → ℝ × ℝ → ℝ := ![etaDer ζ, fun p => -qDer ζ p]

theorem perpGrad_eq_perpGradComp (ζ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (i : Fin 2) :
    perpGrad ζ p i = perpGradComp ζ i p := by
  fin_cases i <;> rfl

/-- **Leaf `PartII-b:T11/3/1`** (nice streams are closed under `∂_q`, `∂_η`, sums, scalar
multiples). Derivative of a smooth function is smooth; `ζ(p + (c, 0)) = ζ p` differentiates to the
same for `fderiv ζ`; if `ζ = 0` for `|η| ≥ L` then `ζ = 0` on the open set `|η| > L`, so
`fderiv ζ = 0` for `|η| ≥ L + 1`. -/
def NiceStreamClosure : Prop :=
  ∀ (c : ℝ) (ζ ξ : ℝ × ℝ → ℝ) (a : ℝ), NiceStream c ζ → NiceStream c ξ →
    NiceStream c (qDer ζ) ∧ NiceStream c (etaDer ζ) ∧ NiceStream c (ζ + ξ) ∧
      NiceStream c (fun p => a * ζ p)

/-- **Leaf `PartII-b:T11/3/2`** (smoothness of the heat flow on `τ > 0`). The map
`(τ, z) ↦ ∫ G_{ντ}(w) ζ(z - w) dw` is `C^∞` on `(0, ∞) × ℝ²`. Proof: differentiate under the
integral sign (`Lib/Kernels/ParamIntegral.lean`, `contDiffOn_integral`); `(θ, w) ↦ G_θ(w)` is smooth
on `θ > 0`; locally in `τ ∈ [τ₁, τ₂]` and `z` the derivatives are dominated by
`C (1 + |w|)^m G_{ντ₁}(w)`-type Gaussian majorants (`Lib/HeatCylinder/HeatKernelAgeMajorant.lean`)
times `sup|ζ|` (a nice stream is bounded). Alternatively substitute `w = √(2ντ) u`:
`H(τ, z) = ∫ g(u) ζ(z - √(2ντ) u) du` with `g` the standard planar Gaussian, whose integrand is
visibly smooth in `(τ, z)` with polynomially bounded derivatives. -/
def HeatConvSmooth : Prop :=
  ∀ (c ν : ℝ) (ζ : ℝ × ℝ → ℝ), 0 < c → 0 < ν → NiceStream c ζ →
    ContDiffOn ℝ ∞ (heatStreamH ν ζ) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))

/-- **Leaf `PartII-b:T11/3/3`** (spatial derivatives pass under the convolution). For a nice
stream `ζ` and `τ > 0`, the partial derivatives of the heat flow in `q` and `η` are the heat flows
of `∂_qζ` and `∂_ηζ`. Proof: `∂_{z_j}∫ G(w) ζ(z - w) dw = ∫ G(w) ∂_jζ(z - w) dw`, differentiation under
the integral (`Lib/TrainB/P0GaussianKernelIBP.lean` `integral_heatKernel2_fderiv_mul_comp_sub` or
`hasFDerivAt_integral_of_dominated_of_fderiv_le`); `∂_jζ` is bounded and `G` is integrable.
Here `cpd 1`, `cpd 2` are the partial derivatives in `q`, `η` of a function on `Coord`. -/
def HeatConvCpd : Prop :=
  ∀ (c ν : ℝ) (ζ : ℝ × ℝ → ℝ), 0 < c → 0 < ν → NiceStream c ζ → ∀ x : Coord, 0 < x.1 →
    cpd 1 (heatStreamH ν ζ) x = heatStreamH ν (qDer ζ) x ∧
      cpd 2 (heatStreamH ν ζ) x = heatStreamH ν (etaDer ζ) x

/-- **Leaf `PartII-b:T11/3/4`** (the heat equation `∂_τH = νΔH`; uses `T11/3/3`, `T11/3/1`). For
`τ > 0`, `cpd 0 H = ν (cpd 1 (cpd 1 H) + cpd 2 (cpd 2 H))`. Proof: by `HeatConvCpd` applied to `ζ`
and to `∂_qζ`, `∂_ηζ`, the right side is `ν ∫ G_{ντ}(w) Δζ(z - w) dw`; the left side is, by the chain
rule for `τ ↦ ντ` and differentiation under the integral, `ν ∫ (∂_θ G)_{ντ}(w) ζ(z - w) dw` with
`∂_θ G = ΔG` (`heatKernel2AgeDerivative_eq_spatialLaplacian`, `Lib/HeatCylinder/
HeatKernelAgeLaplacian.lean`), and `∫ ΔG(w) ζ(z - w) dw = ∫ G(w) Δζ(z - w) dw` by two integrations by
parts (`integral_heatKernel2_fderiv_mul_comp_sub`, `Lib/TrainB/P0GaussianKernelIBP.lean`). -/
def HeatConvEq : Prop :=
  ∀ (c ν : ℝ) (ζ : ℝ × ℝ → ℝ), 0 < c → 0 < ν → NiceStream c ζ → ∀ x : Coord, 0 < x.1 →
    cpd 0 (heatStreamH ν ζ) x =
      ν * (cpd 1 (cpd 1 (heatStreamH ν ζ)) x + cpd 2 (cpd 2 (heatStreamH ν ζ)) x)

/-- **Leaf `PartII-b:T11/3/5`** (`L^p` contraction of Gaussian convolution on the cylinder). For `f`
continuous, `c`-periodic in `q`, vanishing for `|η|` large, `θ > 0`, `p ≥ 1`:
`∫_cell |G_θ * f|^p ≤ ∫_cell |f|^p` (normalized cell measure `Cyl.avgμ c`).
Proof: `Lib/CylinderB/Periodize.lean` `eLpNorm_planarConv_periodic_le` with `k = G_θ`,
`eLpNorm G_θ 1 = ∫ G_θ = 1` (`integral_heatKernel2`, `heatKernel2_nonneg`), then
`eLpNorm_eq_lintegral_rpow_enorm` to pass between `eLpNorm` and `∫⁻ ‖·‖ₑ ^ p`; the factor `c⁻¹` is
common to both sides (`Cyl.avgμ c = ofReal c⁻¹ • Cyl.cellμ c`). -/
def HeatConvContraction : Prop :=
  ∀ (c θ p : ℝ) (f : ℝ × ℝ → ℝ), 0 < c → 0 < θ → 1 ≤ p → Continuous f →
    (∀ z : ℝ × ℝ, f (z.1 + c, z.2) = f z) → (∃ L : ℝ, ∀ z : ℝ × ℝ, L ≤ |z.2| → f z = 0) →
      ∫⁻ z, ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)‖ₑ ^ p ∂(Cyl.avgμ c) ≤
        ∫⁻ z, ‖f z‖ₑ ^ p ∂(Cyl.avgμ c)

/-- **Leaf `PartII-b:T11/3/6`** (approximate identity in `L^p(cell)`). For `f` continuous,
`c`-periodic, vanishing for `|η|` large, and `p > 0`, `G_θ * f → f` in `L^p(Cyl.avgμ c)` as
`θ → 0+`. Proof: `f` is uniformly continuous and bounded (periodic in `q`, compact in `η`), so
`sup_z |G_θ * f(z) - f(z)| ≤ ω_f(δ) + 2‖f‖_∞ ∫_{|w|>δ} G_θ → 0`; both `f` and `G_θ * f` are
controlled on `|η| ≤ L + 1` (finite cell measure there) and for `|η| > L + 1` one has
`|G_θ * f| ≤ ‖f‖_∞ ∫_{|w₂| > |η| - L} G_θ` (Gaussian tail), integrable in `η` uniformly for
`θ ≤ 1`, so dominated convergence applies; or use the `p = 2` route of
`Lib/HeatCylinder/HeatVecApproxIdentity.lean` / `HeatVecGaussianApprox.lean` as a template. -/
def HeatConvTendsto : Prop :=
  ∀ (c p : ℝ) (f : ℝ × ℝ → ℝ), 0 < c → 0 < p → Continuous f →
    (∀ z : ℝ × ℝ, f (z.1 + c, z.2) = f z) → (∃ L : ℝ, ∀ z : ℝ × ℝ, L ≤ |z.2| → f z = 0) →
      Tendsto (fun θ : ℝ =>
        ∫⁻ z, ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) - f z‖ₑ ^ p
          ∂(Cyl.avgμ c)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- **Leaf `PartII-b:T11/3/7`** (Gaussian `η`-tail of the heat flow of a bounded `η`-compact datum).
For a nice stream `g` (bounded, zero for `|η| ≥ L`) and `0 < τ ≤ τ₂`,
`|H_g(τ, q, η)| ≤ C exp(-(max 0 (|η| - L))² / (8 ν τ₂))`. Proof: `g(z - w) = 0` unless
`|w₂| ≥ |η| - L`, so `|H_g| ≤ ‖g‖_∞ ∫_{|w₂| ≥ a} G_{ντ}(w₂) dw₂ ≤ 2‖g‖_∞ exp(-a²/(4ντ))`
(Gaussian tail, e.g. Chernoff: `∫_{|x|≥a} G_θ ≤ 2 e^{-a²/(4θ)}`), and `ντ ≤ ντ₂`. -/
def HeatConvTail : Prop :=
  ∀ (c ν : ℝ) (g : ℝ × ℝ → ℝ) (τ₂ : ℝ), 0 < c → 0 < ν → NiceStream c g → 0 < τ₂ →
    ∃ C L : ℝ, ∀ x : Coord, 0 < x.1 → x.1 ≤ τ₂ →
      |heatStreamH ν g x| ≤ C * Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * ν * τ₂))

/-- **Leaf `PartII-b:T11/3/8`** (pointwise domination of the Fréchet derivatives of the heat flow
by heat flows of nice streams; uses `T11/3/3`, `T11/3/4`, `T11/3/1`). For every `n` there are
finitely many nice streams `g_j` with `‖D^n H_ζ(x)‖ ≤ Σ_j |H_{g_j}(x)|` for all `x` with `τ > 0`.
Proof: induction on `n`, for all nice `ζ` simultaneously. `n = 0`: `‖D^0 H x‖ = |H x|`. Step:
`D^{n+1} H = D^n (fderiv H)` up to a linear isometry
(`iteratedFDeriv_succ_eq_comp_right`), and `fderiv H = Σ_{j=0}^{2} (cpd j H) • e_j^*` with `‖e_j^*‖ ≤ 1`
for the product (max) norm of `Coord`, so `‖D^{n+1} H x‖ ≤ Σ_j ‖D^n (cpd j H) x‖`. On the open set
`τ > 0` one has `cpd 1 H_ζ = H_{∂_qζ}`, `cpd 2 H_ζ = H_{∂_ηζ}` (`HeatConvCpd`) and
`cpd 0 H_ζ = ν(cpd 1 cpd 1 + cpd 2 cpd 2)H_ζ = H_{ν(∂_q²ζ+∂_η²ζ)}` (`HeatConvEq`, `HeatConvCpd`,
linearity of `ζ ↦ H_ζ` for bounded `ζ`); local equality of functions on an open set gives equality
of `iteratedFDeriv` (`Filter.EventuallyEq.iteratedFDeriv_eq`); then apply the induction hypothesis
to the nice streams `∂_qζ`, `∂_ηζ`, `ν Δζ` (`NiceStreamClosure`) and sum the finite families. -/
def HeatDerivDomination : Prop :=
  ∀ (c ν : ℝ) (ζ : ℝ × ℝ → ℝ) (n : ℕ), 0 < c → 0 < ν → NiceStream c ζ →
    ∃ (m : ℕ) (g : Fin m → ℝ × ℝ → ℝ), (∀ j, NiceStream c (g j)) ∧
      ∀ x : Coord, 0 < x.1 →
        ‖iteratedFDeriv ℝ n (heatStreamH ν ζ) x‖ ≤ ∑ j, |heatStreamH ν (g j) x|

/-- **Leaf `PartII-b:T11/3/9`** (`L^{r'}` membership of the derivatives; uses `T11/3/2`,
`T11/3/7`, `T11/3/8`). For `0 < τ₁ ≤ τ₂` and `n ≤ 3`, `x ↦ D^n H_ζ(x)` is in `L^{r'}` of the
restriction of `ageμ c 0` to `[τ₁, τ₂] × ℝ_q × ℝ_η`. Proof: `D^n H` is continuous on the open set
`τ > 0` (`HeatConvSmooth`, `ContDiffOn.continuousOn_iteratedFDerivWithin`,
`iteratedFDerivWithin_of_isOpen`), hence a.e.-strongly measurable on the restricted measure;
`HeatDerivDomination` and `HeatConvTail` bound `‖D^n H x‖` by `Φ(η) = C exp(-(max 0 (|η| - L))²/(8ντ₂))`,
which is in `L^{r'}(dη)` (Gaussian tail beyond a bounded interval); `ageμ c 0 = c⁻¹ ds dq dη`
(`CellPart.ageμ_zero_eq` in `Tasks/FlatUnique/CellStream/AgeCell.lean`) restricted to
`[τ₁, τ₂] × cell × ℝ` is a product with finite `(τ, q)` mass, so `∫ Φ^{r'} < ∞`
(`MemLp.of_bound`-type argument via `memLp_of_le` / `MemLp.mono`). -/
def HeatDerivMemLp : Prop :=
  ∀ (c ν r' : ℝ) (ζ : ℝ × ℝ → ℝ), 0 < c → 0 < ν → 1 < r' → NiceStream c ζ →
    ∀ n : ℕ, n ≤ 3 → ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₂ →
      MemLp (fun x : Coord => iteratedFDeriv ℝ n (heatStreamH ν ζ) x) (ENNReal.ofReal r')
        ((Axi.ageμ c 0).restrict (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ))))

/-- Restricting `F : Coord → ℝ` to a slice `τ` = const commutes with `cpd` (chain rule). -/
theorem slice_fderiv {F : Coord → ℝ} {τ : ℝ} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F (τ, p))
    (v : ℝ × ℝ) : fderiv ℝ (fun z : ℝ × ℝ => F (τ, z)) p v = fderiv ℝ F (τ, p) (0, v) := by
  have hmap : HasFDerivAt (fun z : ℝ × ℝ => ((τ, z) : Coord))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_const τ p).prodMk (hasFDerivAt_id p)
  have h := hF.hasFDerivAt.comp p hmap
  rw [show (fun z : ℝ × ℝ => F (τ, z)) = F ∘ (fun z : ℝ × ℝ => ((τ, z) : Coord)) from rfl,
    h.fderiv]
  rfl

/-- `heatStreamH` is the convolution formula for positive times. -/
theorem heatStreamH_of_pos {ν : ℝ} (ζ : ℝ × ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ) (p : ℝ × ℝ) :
    heatStreamH ν ζ (τ, p) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * ζ (p - w) := by
  simp [heatStreamH, hτ]

/-- **The heat flow of a nice stream** (`PartII-b:T11/3`, conditional). -/
theorem heatStreamDual_of (h1 : NiceStreamClosure) (h2 : HeatConvSmooth) (h3 : HeatConvCpd)
    (h4 : HeatConvEq) (h5 : HeatConvContraction) (h6 : HeatConvTendsto)
    (h9 : HeatDerivMemLp) : HeatStreamDual := by
  intro c ν r' ζ hc hν hr' hζ
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    isOpen_Ioi.prod isOpen_univ
  -- periodicity
  have hper : ∀ x : Coord, 0 < x.1 → heatStreamH ν ζ (qShift c x) = heatStreamH ν ζ x := by
    intro x hx
    have hx' : 0 < (qShift c x).1 := hx
    simp only [heatStreamH, hx, hx', ↓reduceIte]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have e : (qShift c x).2 - w = ((x.2 - w).1 + c, (x.2 - w).2) := by
      simp only [qShift, Prod.fst_sub, Prod.snd_sub]
      ext <;> simp <;> ring
    show UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * ζ ((qShift c x).2 - w) =
      UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * ζ (x.2 - w)
    rw [e, hζ.periodic]
  -- the slice derivative identity
  have hdiff : ∀ τ : ℝ, 0 < τ → ∀ p : ℝ × ℝ,
      DifferentiableAt ℝ (heatStreamH ν ζ) (τ, p) := by
    intro τ hτ p
    exact ((h2 c ν ζ hc hν hζ).contDiffAt (hopen.mem_nhds (show ((τ, p) : Coord) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from ⟨hτ, mem_univ p⟩))).differentiableAt
      (by simp)
  have hperp : ∀ τ : ℝ, 0 < τ → ∀ (p : ℝ × ℝ) (i : Fin 2),
      perpGrad (fun z => heatStreamH ν ζ (τ, z)) p i =
        ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w) := by
    intro τ hτ p i
    have hd := hdiff τ hτ p
    have e0 := (h3 c ν ζ hc hν hζ (τ, p) hτ)
    fin_cases i
    · show fderiv ℝ (fun z => heatStreamH ν ζ (τ, z)) p (0, 1) = _
      rw [slice_fderiv hd]
      have : fderiv ℝ (heatStreamH ν ζ) (τ, p) (0, (0, 1)) = cpd 2 (heatStreamH ν ζ) (τ, p) := rfl
      rw [this, e0.2, heatStreamH_of_pos _ hτ]
      rfl
    · show -fderiv ℝ (fun z => heatStreamH ν ζ (τ, z)) p (1, 0) = _
      rw [slice_fderiv hd]
      have : fderiv ℝ (heatStreamH ν ζ) (τ, p) (0, (1, 0)) = cpd 1 (heatStreamH ν ζ) (τ, p) := rfl
      rw [this, e0.1, heatStreamH_of_pos _ hτ, ← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp [perpGradComp]
  -- the components are continuous, periodic, `η`-compact
  have hcomp : ∀ i : Fin 2, Continuous (perpGradComp ζ i) ∧
      (∀ z : ℝ × ℝ, perpGradComp ζ i (z.1 + c, z.2) = perpGradComp ζ i z) ∧
      (∃ L : ℝ, ∀ z : ℝ × ℝ, L ≤ |z.2| → perpGradComp ζ i z = 0) := by
    intro i
    obtain ⟨hq, he, -, -⟩ := h1 c ζ ζ 1 hζ hζ
    fin_cases i
    · exact ⟨he.smooth.continuous, he.periodic, he.compact⟩
    · refine ⟨hq.smooth.continuous.neg, fun z => ?_, ?_⟩
      · show -qDer ζ (z.1 + c, z.2) = -qDer ζ z
        rw [hq.periodic]
      · obtain ⟨L, hL⟩ := hq.compact
        exact ⟨L, fun z hz => by
          show -qDer ζ z = 0
          rw [hL z hz, neg_zero]⟩
  refine ⟨heatStreamH ν ζ, ⟨h2 c ν ζ hc hν hζ, hper, fun x hx => h4 c ν ζ hc hν hζ x hx.1, ?_⟩, ?_, ?_⟩
  · intro n hn τ₁ τ₂ h₁ h₁₂
    exact h9 c ν r' ζ hc hν hr' hζ n hn τ₁ τ₂ h₁ h₁₂
  · -- contraction
    intro τ hτ i
    obtain ⟨hcont, hpp, hcpt⟩ := hcomp i
    have hp1 : (1 : ℝ) ≤ r' := hr'.le
    have key := h5 c (ν * τ) r' (perpGradComp ζ i) hc (mul_pos hν hτ) hp1 hcont hpp hcpt
    have e1 : ∀ p, ‖perpGrad (fun z => heatStreamH ν ζ (τ, z)) p i‖ₑ ^ r' =
        ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w)‖ₑ ^ r' := by
      intro p; rw [hperp τ hτ p i]
    have e2 : ∀ p, ‖perpGrad ζ p i‖ₑ ^ r' = ‖perpGradComp ζ i p‖ₑ ^ r' := by
      intro p; rw [perpGrad_eq_perpGradComp]
    simp only [e1, e2]
    exact key
  · -- convergence at `τ → 0+`
    intro i
    obtain ⟨hcont, hpp, hcpt⟩ := hcomp i
    have hlim := h6 c r' (perpGradComp ζ i) hc (by linarith) hcont hpp hcpt
    have hmap : Tendsto (fun τ : ℝ => ν * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun τ : ℝ => ν * τ) (𝓝 (0 : ℝ)) (𝓝 (ν * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact mul_pos hν hτ
    refine (hlim.comp hmap).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : 0 < τ := hτ
    refine lintegral_congr fun p => ?_
    show ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w)) -
        perpGradComp ζ i p‖ₑ ^ r' = _
    rw [← hperp τ hτ' p i, ← perpGrad_eq_perpGradComp]

end UnforcedLeray.Short.IIb
