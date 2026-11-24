import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable

/-!
# Part II-b, task `PartII-b:T12/6` (`DuhamelSolenoidal`): the heat flow preserves weak
solenoidality (conditional assembly and sub-leaves)

Source of record: `the November 2 reference manuscript`, line 1924 ("the heat flow
preserves solenoidality, `P_0 G = G`") inside the causal formula of lines 1920-1930. The target is
`DuhamelSolenoidal` of `Sub/T12.lean`.

## Why the target splits this way

Write `b = flatDuhamel ν μ G` and `x = (s, z)`, `z = (q, η)`. The proof has three layers.

1. **Slice solenoidality** (`DsolSliceAll`, `DsolSliceGauss`, `DsolGaussExtend`). Testing the weak
   solenoidality of `G` against tensor tests `g(s) ψ(z)` and using the fundamental lemma in `s`
   shows: for a.e. `t > 0` the slice `G(t, ·)` is weakly divergence free on the plane, against all
   `ψ ∈ C_c^∞(ℝ²)` at once (a countable `C¹`-dense family, `DsolCountableDense`), and then also
   against smooth `ψ` with Gaussian decay of `ψ, ∇ψ` (cutoff and dominated convergence), because
   `G(t, ·)` has Gaussian-weighted integrability (`H_r` plus `q`-periodicity).
2. **The heat flow commutes with the divergence** (`DsolHeatAdjoint`, `DsolHeatSmooth`,
   `DsolHeatDecay`). For `φ ∈ C_c^∞(ℝ²)` the planar heat flow is self-adjoint:
   `∫ (e^{θΔ} g)_i ρ_i = ∫ g_i (K_θ * ρ_i)`, and `K_θ * ∂_iφ = ∂_i (K_θ * φ)` with `K_θ * φ`
   smooth and of Gaussian decay. Hence `∫ (e^{θΔ} G(t,·)) · ∇φ = ∫ G(t,·) · ∇(K_θ * φ) = 0`
   (`dsol_inner_zero`, proved below from the previous layer).
3. **Fubini** (`DsolDuhamelIntegrable`, `DsolSwap`, `DsolIntegrable`). The pairing
   `∫ b · ∇φ` equals `∫_t (1/t) ∫_{s>t} (t/s)^μ [∫_z e^{ν(s-t)Δ} G(t) · ∇φ(s, ·)] ds dt`, whose inner
   bracket vanishes; this needs the absolute integrability of the Duhamel body on the support of
   `φ`, which is exactly where `a_r = Re μ + (3/r - 1)/2 > 0` enters (Hölder in `t`).

Proved here: `duhamelSolenoidal_of`, the conditional assembly of `DuhamelSolenoidal` from the eight
leaves `DsolIntegrable`, `DsolSwap`, `DsolSliceAll`, `DsolSliceGauss`, `DsolGaussExtend`,
`DsolHeatAdjoint`, `DsolHeatSmooth`, `DsolHeatDecay` (the leaves `DsolDuhamelIntegrable` and
`DsolCountableDense` are internal inputs of `DsolSwap` and `DsolSliceAll`, not hypotheses of the
assembly).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Notation -/

/-- The slice pairing integrand `G(x)_0 ∂_qψ(x.2) + G(x)_1 ∂_ηψ(x.2)` on `Coord`. -/
def dsolF (G : CProf) (ψ : ℝ × ℝ → ℝ) (x : Coord) : ℂ :=
  G x 0 * (fderiv ℝ ψ x.2 (1, 0) : ℂ) + G x 1 * (fderiv ℝ ψ x.2 (0, 1) : ℂ)

/-- Gaussian-weighted integrability of a planar field: `y ↦ e^{-a|y|²} g(y)` is integrable (hence
`g` is a.e. strongly measurable) for every `a > 0`. -/
def DsolGaussInt (g : ℝ × ℝ → CMerid) : Prop :=
  ∀ a : ℝ, 0 < a → Integrable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) • g y)

/-- The Gaussian average `K_θ * φ` with the heat kernel (the kernel is even, so this is the heat
flow `e^{θΔ} φ`): `y ↦ ∫ K_θ(w) φ(y + w) dw`. -/
def dsolHeatConv (θ : ℝ) (φ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, flatHeatKernel θ w * φ (y + w)

/-! ## Layer 3: integrability and the Fubini swap -/

/-- **Leaf `PartII-b:T12/6/1`** (Hölder on the support of the test; SP 1924). A `c`-periodic
`b ∈ H_r` (`1 < r < 3`, `c > 0`) paired with `cpd j φ`, `φ` a coordinate test, is integrable on
`Coord`: `supp φ ⊂ [σ,H] × [-Q,Q] × [-L,L]` with `σ > 0`, the weight `s^{r/2-5/2}` is bounded above
and below on `[σ, H]`, `q`-periodicity covers `[-Q,Q]` by finitely many cells, so `b ∈ L^r` of a
compact set, and `cpd j φ` is bounded. -/
def DsolIntegrable : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → r < 3 → InHr c r b →
    ∀ φ : Coord → ℝ, IsCoordTest φ → ∀ (i : Fin 2) (j : Fin 3),
      Integrable (fun x : Coord => b x i * (cpd j φ x : ℂ))

/-- **Leaf `PartII-b:T12/6/2`** (SP 1924; this is where `a_r > 0` is used). The Duhamel body
`(x, t) ↦ 1_{0<t<s} (t/s)^μ t⁻¹ e^{ν(s-t)Δ} G(t)(z)` is integrable on `B × ℝ` for every box
`B = [σ,H] × [-R,R]²` with `σ > 0`. Proof: `|(t/s)^μ| = (t/s)^{Re μ}`; for `s ∈ [σ, H]` the factor
`s^{-Re μ}` is bounded; the heat contraction on `L^r` of the cylinder (`flatHeatContraction`,
accepted) and periodicity bound `∫_B |e^{θΔ} G(t)| dz ≤ C g(t)` with
`g(t) = ‖G(t)‖_{L^r(cell × ℝ)}`, `∫ g^r t^{r/2-5/2} dt < ∞`; Hölder in `t` against `t^{Re μ - 1}`
needs `(Re μ - 3/2 + 5/(2r)) r' > -1`, i.e. exactly `a_r > 0`. Measurability: pass to the
strongly measurable periodic representative (`exists_periodic_rep`, `flatDuhamel_congr_of_ae`,
`stronglyMeasurable_duhamelBody`, all in `Tasks/FlatCausal/DuhamelMeasurable*`). -/
def DsolDuhamelIntegrable : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (G : CProf), 0 < c → 1 < r → r < 3 → 0 < ν →
    0 < μ.re + (3 / r - 1) / 2 → InHr c r G →
    ∀ σ H R : ℝ, 0 < σ →
      Integrable (duhamelS.indicator (duhamelBody ν μ G))
        ((volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))).prod (volume : Measure ℝ))

/-- **Leaf `PartII-b:T12/6/3`** (Fubini swap; uses `DsolDuhamelIntegrable`). For a coordinate test
`φ`, the pairing of the Duhamel integral with `(∂_qφ, ∂_ηφ)` equals the `t`-integral of the
`s`-integral of the planar pairings of `e^{ν(s-t)Δ} G(t)` with `∇_{q,η} φ(s, ·)`:
`∫ b·∇φ = ∫_{t>0} ∫_{s>t} (t/s)^μ t⁻¹ [∫_z e^{ν(s-t)Δ}G(t)(z)·∇_zφ(s,z) dz] ds dt`.
Proof: `flatDuhamel_eq_integral` writes `b(x) = ∫ 1_S(x,t) body(x,t) dt`; on the box `B ⊇ supp φ` the
body is integrable on `B × ℝ` (`dsolDuhamelIntegrable`), so `Integrable.prod_right_ae` lets one pull
the componentwise `i`-th coordinate and the bounded factor `cpd (i+1) φ` inside, then
`integral_prod_symm` swaps `x` and `t`, the indicator restricts to `0 < t < s`, and for fixed `t`
`integral_prod` splits `x = (s, z)`. The integrability hypotheses hold for a.e. `t`; the exceptional
null set does not change the outer integral. -/
def DsolSwap : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (G : CProf), 0 < c → 1 < r → r < 3 → 0 < ν →
    0 < μ.re + (3 / r - 1) / 2 → InHr c r G →
    ∀ φ : Coord → ℝ, IsCoordTest φ →
      ∫ x : Coord, (flatDuhamel ν μ G x 0 * (cpd 1 φ x : ℂ) + flatDuhamel ν μ G x 1 * (cpd 2 φ x : ℂ)) =
        ∫ t in Ioi (0 : ℝ), ∫ s in Ioi t, (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
          ∫ z : ℝ × ℝ, (flatHeat (ν * (s - t)) (fun z => G (t, z)) z 0 * (cpd 1 φ (s, z) : ℂ) +
              flatHeat (ν * (s - t)) (fun z => G (t, z)) z 1 * (cpd 2 φ (s, z) : ℂ))

/-! ## Layer 1: slice solenoidality -/

/-- **Leaf `PartII-b:T12/6/4`** (separability of `C_c^∞(ℝ²)` in the `C¹` topology). There is a
countable family `D` of `C_c^∞` functions such that every `C_c^∞` function `ψ` is, for some radius
`R`, the `C¹`-uniform limit of members of `D` supported in `‖y‖ ≤ R`. Proof: for `R ∈ ℕ` the set of
smooth functions vanishing for `‖y‖ > R` embeds isometrically (`ψ ↦ (ψ, Dψ)` on `closedBall 0 R`)
into the separable space `C(closedBall 0 R, ℝ × ((ℝ×ℝ) →L[ℝ] ℝ))`
(`TopologicalSpace.IsSeparable` of a subset, `IsSeparable.exists_countable_dense_subset`), and take
the union over `R`. -/
def DsolCountableDense : Prop :=
  ∃ D : Set (ℝ × ℝ → ℝ), D.Countable ∧
    (∀ ψ ∈ D, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ) ∧
    ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∃ R : ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ ψ' ∈ D, (∀ y : ℝ × ℝ, R < ‖y‖ → ψ' y = 0) ∧
        ∀ y : ℝ × ℝ, |ψ y - ψ' y| + ‖fderiv ℝ ψ y - fderiv ℝ ψ' y‖ ≤ ε

/-- **Leaf `PartII-b:T12/6/5`** (Gaussian-weighted integrability of a.e. slice; SP 1924, `H_r`
and `q`-periodicity). For `G ∈ H_r` and a.e. `t > 0` the slice `G(t, ·)` satisfies `DsolGaussInt`.
Proof: Tonelli on the finite `hNorm c r G` gives `∫⁻_{cell × ℝ} ‖G(t,·)‖^r < ∞` and a.e.
`q`-periodicity of the slice for a.e. `t`; split `ℝ²` into the cells `[nc, (n+1)c) × ℝ`, Hölder on
each cell against `e^{-a|y|²}` (which lies in every `L^{r'}`) and sum the convergent series in `n`;
a.e. strong measurability of the slice from `AEStronglyMeasurable.prodMk_left`-type Fubini. -/
def DsolSliceGauss : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 1 < r → r < 3 → InHr c r G →
    ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) → DsolGaussInt (fun y => G (t, y))

/-- **Leaf `PartII-b:T12/6/6`** (SP 1924; uses `DsolCountableDense`, `DsolSliceGauss` and the
fixed-test slice lemma `dsol_slice_ae` of `Tasks/FlatCausal/DuhamelSolenoidal/SliceAe.lean`):
a weakly solenoidal `G ∈ H_r` has, for a.e. `t > 0`, `∫_y G(t,y)·∇ψ(y) dy = 0` for ALL
`ψ ∈ C_c^∞(ℝ²)` simultaneously. Proof: for the countable family `D` take the countable
intersection (`ae_all_iff`) of the null sets of `dsol_slice_ae` and the exceptional set of
`dsolSliceGauss`; for arbitrary `ψ` pick `ψ' ∈ D` with `‖ψ - ψ'‖_{C¹} ≤ ε`, supported in a fixed
ball, and bound `|∫ G·∇(ψ - ψ')| ≤ ε ∫_{‖y‖ ≤ R} ‖G(t,y)‖ dy`, finite by `DsolGaussInt`. -/
def DsolSliceAll : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 1 < r → r < 3 → InHr c r G → WeakSolenoidal G →
    ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) → ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y : ℝ × ℝ, dsolF G ψ (t, y) = 0

/-- **Leaf `PartII-b:T12/6/7`** (extension from compactly supported to Gaussian-decaying tests).
If the slice `G(t, ·)` is weakly divergence free against all `C_c^∞` tests and has
Gaussian-weighted integrability, it is weakly divergence free against every smooth `ψ` with
`‖ψ y‖ + ‖Dψ y‖ ≤ C e^{-a|y|²}`. Proof: cutoffs `χ_R = χ(·/R)` (`ContDiffBump`), apply the
hypothesis to `χ_R ψ`; `∫ χ_R G·∇ψ → ∫ G·∇ψ` by dominated convergence (dominator
`C ‖G‖ e^{-a|y|²}`), and the term `∫ ψ G·∇χ_R` is `O(1/R)` against the same dominator. -/
def DsolGaussExtend : Prop :=
  ∀ (G : CProf) (t : ℝ),
    (∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y : ℝ × ℝ, dsolF G ψ (t, y) = 0) →
    DsolGaussInt (fun y => G (t, y)) →
    ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ →
      (∃ a C : ℝ, 0 < a ∧ ∀ y : ℝ × ℝ,
        ‖ψ y‖ + ‖fderiv ℝ ψ y‖ ≤ C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) →
      ∫ y : ℝ × ℝ, dsolF G ψ (t, y) = 0

/-! ## Layer 2: the heat flow and the divergence -/

/-- **Leaf `PartII-b:T12/6/8`** (self-adjointness of the planar heat flow). For `θ > 0`, a field
`g` with `DsolGaussInt g` and a continuous compactly supported `ρ`, both pairings are integrable and
`∫ (e^{θΔ} g)_i ρ = ∫ g_i (K_θ * ρ)`. Proof: `flatHeat θ g z = ∫ K_θ(w) g(z - w) dw` converges
absolutely (`K_θ(w) ≤ C_z e^{-a|z-w|²}` for `a ≤ 1/(8θ)`); Fubini on `ℝ² × ℝ²` with the
substitution `y = z - w`, using the Gaussian decay of `y ↦ ∫ K_θ(w) 1_{supp ρ}(y + w) dw`; the
`i`-th component commutes with the Bochner integral. -/
def DsolHeatAdjoint : Prop :=
  ∀ (θ : ℝ) (g : ℝ × ℝ → CMerid) (ρ : ℝ × ℝ → ℝ) (i : Fin 2), 0 < θ → DsolGaussInt g →
    Continuous ρ → HasCompactSupport ρ →
      Integrable (fun z : ℝ × ℝ => flatHeat θ g z i * (ρ z : ℂ)) ∧
      Integrable (fun y : ℝ × ℝ => g y i * ((dsolHeatConv θ ρ y : ℝ) : ℂ)) ∧
      ∫ z : ℝ × ℝ, flatHeat θ g z i * (ρ z : ℂ) =
        ∫ y : ℝ × ℝ, g y i * ((dsolHeatConv θ ρ y : ℝ) : ℂ)

/-- **Leaf `PartII-b:T12/6/9`** (smoothness of the heat flow of a test and the derivative
formula). For `θ > 0` and `φ ∈ C_c^∞(ℝ²)`, `K_θ * φ` is `C^∞` and `D(K_θ * φ)(y) e =
(K_θ * Dφ(·) e)(y)`. Proof: convolution of the integrable kernel `K_θ` with a compactly supported
smooth function (`HasCompactSupport.contDiff_convolution_right`, `hasFDerivAt_convolution_right`),
and evenness of `K_θ` to turn `y + w` into `y - w`. -/
def DsolHeatSmooth : Prop :=
  ∀ (θ : ℝ) (φ : ℝ × ℝ → ℝ), 0 < θ → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ContDiff ℝ ∞ (dsolHeatConv θ φ) ∧
      ∀ y e : ℝ × ℝ, fderiv ℝ (dsolHeatConv θ φ) y e =
        dsolHeatConv θ (fun z => fderiv ℝ φ z e) y

/-- **Leaf `PartII-b:T12/6/10`** (Gaussian decay of the heat flow of a test; uses
`DsolHeatSmooth`). For `θ > 0` and `φ ∈ C_c^∞(ℝ²)` there are `a, C` with
`‖K_θ * φ (y)‖ + ‖D(K_θ * φ)(y)‖ ≤ C e^{-a|y|²}`. Proof: `supp φ ⊂ closedBall 0 R`; for `‖y‖ ≥ 2R`
only `‖w‖ ≥ ‖y‖/2` contributes, where `K_θ(w) ≤ (4πθ)⁻¹ e^{-‖y‖²/(16θ)}`, and the area of the ball is
finite; on `‖y‖ ≤ 2R` use boundedness; the derivative is `K_θ * Dφ` by `dsolHeatSmooth`. -/
def DsolHeatDecay : Prop :=
  ∀ (θ : ℝ) (φ : ℝ × ℝ → ℝ), 0 < θ → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∃ a C : ℝ, 0 < a ∧ ∀ y : ℝ × ℝ,
      ‖dsolHeatConv θ φ y‖ + ‖fderiv ℝ (dsolHeatConv θ φ) y‖ ≤
        C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))

/-! ## Conditional assembly -/

/-- The partials of a coordinate test along the slice `z ↦ φ(s, z)`. -/
theorem dsol_cpd_slice {φ : Coord → ℝ} (hφ : Differentiable ℝ φ) (s : ℝ) (z : ℝ × ℝ) :
    cpd 1 φ (s, z) = fderiv ℝ (fun z' : ℝ × ℝ => φ (s, z')) z (1, 0) ∧
      cpd 2 φ (s, z) = fderiv ℝ (fun z' : ℝ × ℝ => φ (s, z')) z (0, 1) := by
  have hin : HasFDerivAt (fun z' : ℝ × ℝ => ((s, z') : Coord))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) z := hasFDerivAt_prodMk_right s z
  have hcomp : HasFDerivAt (fun z' : ℝ × ℝ => φ (s, z'))
      ((fderiv ℝ φ (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) z :=
    (hφ (s, z)).hasFDerivAt.comp z hin
  rw [hcomp.fderiv]
  constructor
  · simp [cpd, cdir]
  · simp [cpd, cdir]

/-- The slice of a coordinate test is a compactly supported smooth function of the plane. -/
theorem dsol_slice_test {φ : Coord → ℝ} (hφ : IsCoordTest φ) (s : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => φ (s, z)) ∧ HasCompactSupport (fun z : ℝ × ℝ => φ (s, z)) := by
  refine ⟨hφ.smooth.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  refine HasCompactSupport.intro (hφ.compact.image continuous_snd) ?_
  intro z hz
  have : ((s, z) : Coord) ∉ tsupport φ := fun h => hz ⟨(s, z), h, rfl⟩
  exact image_eq_zero_of_notMem_tsupport this

/-- **Inner vanishing.** For a slice `G(t, ·)` that is weakly divergence free against all
compactly supported tests and Gaussian integrable, and every `θ > 0`, the heat flow of the slice is
weakly divergence free against every planar test. -/
theorem dsol_inner_zero (hExt : DsolGaussExtend) (hAdj : DsolHeatAdjoint)
    (hSm : DsolHeatSmooth) (hDec : DsolHeatDecay) {G : CProf} {t : ℝ}
    (h0 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y : ℝ × ℝ, dsolF G ψ (t, y) = 0)
    (hg : DsolGaussInt (fun y => G (t, y))) {θ : ℝ} (hθ : 0 < θ) {φ' : ℝ × ℝ → ℝ}
    (hφ' : ContDiff ℝ ∞ φ') (hφc : HasCompactSupport φ') :
    ∫ z : ℝ × ℝ, (flatHeat θ (fun z => G (t, z)) z 0 * (fderiv ℝ φ' z (1, 0) : ℂ) +
        flatHeat θ (fun z => G (t, z)) z 1 * (fderiv ℝ φ' z (0, 1) : ℂ)) = 0 := by
  set g : ℝ × ℝ → CMerid := fun z => G (t, z) with hgdef
  have hρc : ∀ e : ℝ × ℝ, Continuous (fun z : ℝ × ℝ => fderiv ℝ φ' z e) := fun e =>
    (hφ'.continuous_fderiv (by simp)).clm_apply continuous_const
  have hρk : ∀ e : ℝ × ℝ, HasCompactSupport (fun z : ℝ × ℝ => fderiv ℝ φ' z e) := fun e =>
    hφc.fderiv_apply ℝ e
  obtain ⟨hA0, hB0, hE0⟩ := hAdj θ g _ 0 hθ hg (hρc (1, 0)) (hρk (1, 0))
  obtain ⟨hA1, hB1, hE1⟩ := hAdj θ g _ 1 hθ hg (hρc (0, 1)) (hρk (0, 1))
  obtain ⟨hψs, hψd⟩ := hSm θ φ' hθ hφ' hφc
  have hdec := hDec θ φ' hθ hφ' hφc
  have hzero := hExt G t h0 hg (dsolHeatConv θ φ') hψs hdec
  have hderiv : ∀ y : ℝ × ℝ, dsolF G (dsolHeatConv θ φ') (t, y) =
      g y 0 * ((dsolHeatConv θ (fun z => fderiv ℝ φ' z (1, 0)) y : ℝ) : ℂ) +
        g y 1 * ((dsolHeatConv θ (fun z => fderiv ℝ φ' z (0, 1)) y : ℝ) : ℂ) := by
    intro y
    unfold dsolF
    simp only [hgdef]
    rw [hψd y (1, 0), hψd y (0, 1)]
  rw [integral_add hA0 hA1, hE0, hE1, ← integral_add hB0 hB1]
  rw [← hzero]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact (hderiv y).symm

/-- **Conditional `DuhamelSolenoidal`** (SP 1924: the heat flow preserves solenoidality). -/
theorem duhamelSolenoidal_of (h1 : DsolIntegrable) (h2 : DsolSwap) (h3 : DsolSliceAll)
    (h4 : DsolSliceGauss) (h5 : DsolGaussExtend) (h6 : DsolHeatAdjoint)
    (h7 : DsolHeatSmooth) (h8 : DsolHeatDecay) : DuhamelSolenoidal := by
  intro r hr1 hr3 μ ha ν c hν hc G hG hW hb φ hφ
  refine ⟨?_, ?_⟩
  · exact (h1 c r _ hc hr1 hr3 hb φ hφ 0 1).add (h1 c r _ hc hr1 hr3 hb φ hφ 1 2)
  · rw [h2 c r ν μ G hc hr1 hr3 hν ha hG φ hφ]
    have hdiff : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hae : ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) → ∀ s ∈ Ioi t,
        ∫ z : ℝ × ℝ, (flatHeat (ν * (s - t)) (fun z => G (t, z)) z 0 * (cpd 1 φ (s, z) : ℂ) +
          flatHeat (ν * (s - t)) (fun z => G (t, z)) z 1 * (cpd 2 φ (s, z) : ℂ)) = 0 := by
      filter_upwards [h3 c r G hc hr1 hr3 hG hW, h4 c r G hc hr1 hr3 hG] with t hs hgau ht s hs'
      have hθ : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 hs')
      obtain ⟨hsm, hsc⟩ := dsol_slice_test hφ s
      have := dsol_inner_zero h5 h6 h7 h8 (hs ht) (hgau ht) hθ hsm hsc
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [(dsol_cpd_slice hdiff s z).1, (dsol_cpd_slice hdiff s z).2]
    refine integral_eq_zero_of_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with t ht ht0
    simp only [Pi.zero_apply]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    rw [ht ht0 s hs, mul_zero]

end UnforcedLeray.Short.IIb
