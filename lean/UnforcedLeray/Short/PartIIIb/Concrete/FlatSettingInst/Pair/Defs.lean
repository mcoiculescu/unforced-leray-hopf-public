import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting

/-!
# The frozen pair of the flat setting: objects on the cell `c` and leaves
(source 2894-2912, 4352-4356, 3030-3035, 593-610, 4349-4350)

Source of record: `the November 2 reference manuscript` (73 pages).

`FrozenPairExists` (`Leaves.lean`) asks for the pinned `FrozenPair κ ν c m` (`Setting.lean`): the
elements `q_{±,s} ∈ X_{m,c}` whose planar functions are `frozenQ`, the bounded functionals
`ℓ_{±,s}` given by `frozenEll`, `ℓ_{i,s}q_{j,s} = δ_{ij}` (4354-4355: "This Gram normalization only
makes `ℓ_{i,s}q_{j,s} = δ_{ij}`"), the conjugation laws, and continuity in the age.  On the band
`a = 1 + ν·bandAge ∈ [1, 3]`, `d = c/√a` (4344-4346, 4352-4354).  The reduction (`Of.lean`) works on
the original cell `c`:

* `qFun κ ν c k s = J_a P_d e_k` (`frozenQ κ ν c j s = qFun κ ν c (pmIdx j) s`; 2894-2896, 3030:
  `J_aW(x) = a⁻²W(x/√a)`);
* `lam0Ker`, `ellKer`: the kernels on the cell `c` of the unnormalized and of the Gram-normalized
  periodized dual rows, `x ↦ a Λ⁰_{d,k}(x/√a)` and `x ↦ a Λ_{d,k}(x/√a)` (2896-2902); the change of
  variables `x = √a y` (`IntegralCellDilate`) turns `∫_{cell d} Λ(y) J_a⁻¹f(y) dy` (`frozenEll`) into
  `∫_{cell c} a Λ(x/√a) f(x) dx`;
* `dualVec m g = ḡ ⟨x⟩^{-2m}`: the Riesz vector in `X_{m,c} = L²(cell, ⟨x⟩^{2m}dx)` of the functional
  `f ↦ ∫_cell g f`.

The leaves below are: continuity and bounds of these explicit functions (Gaussian tails of `e_k`,
the `O(|y|⁻²)` decay of the planar dual kernels `λ_k`, 2896-2899), zero circulation of `q`
(`∫ q = 0`, 597), the symmetries of the Part I seed (`q = h(r)e^{2iϑ}`, `e₁ = q̄`, 597-610), the
conjugation symmetry of the Gram normalization, the change of variables on cells, and dominated
convergence in `L²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-! ## The objects on the cell `c` -/

/-- `q_{k,s} = J_a P_d e_k` as a planar function, `k ∈ Fin 2` (source 2894-2896, 4352-4354;
`a = bandA ν s`, `d = bandD ν c s = c/√a`). -/
def qFun (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2) (s : ℝ) : ℝ × ℝ → ℂ :=
  IIIa.Jscale (bandA ν s) (IIIa.perE κ (bandD ν c s) k)

theorem frozenQ_eq_qFun (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (j : Bool) (s : ℝ) :
    frozenQ κ ν c j s = qFun κ ν c (pmIdx j) s := rfl

/-- The kernel on the cell `c` of the unnormalized periodized dual row `Λ⁰_k = P_dλ_k`:
`x ↦ a Λ⁰_{d,k}(x/√a)` (source 2896-2899). -/
def lam0Ker (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2) (s : ℝ) (x : ℝ × ℝ) : ℂ :=
  (bandA ν s : ℂ) * IIIa.perLam0 κ (bandD ν c s) k
    (x.1 / Real.sqrt (bandA ν s), x.2 / Real.sqrt (bandA ν s))

/-- The kernel on the cell `c` of the Gram-normalized dual row `Λ_k = (G⁻¹Λ⁰)_k`:
`x ↦ a Λ_{d,k}(x/√a)` (source 2896-2902, 4353-4356). -/
def ellKer (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2) (s : ℝ) (x : ℝ × ℝ) : ℂ :=
  (bandA ν s : ℂ) * IIIa.perLam κ (bandD ν c s) k
    (x.1 / Real.sqrt (bandA ν s), x.2 / Real.sqrt (bandA ν s))

/-- The Riesz vector `ḡ⟨x⟩^{-2m}` of the functional `f ↦ ∫_cell g f` on
`X_{m,c} = L²(cell, ⟨x⟩^{2m}dx)` (`⟨x⟩² = B0579.jb x`). -/
def dualVec (m : ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  conj (g x) * ((B0579.jb x ^ (-m) : ℝ) : ℂ)

/-! ## Leaves: regularity and bounds of the explicit functions -/

/-- **The periodized growing vectors are continuous** (source 2894-2899: "direct columns have
Gaussian tails"): for `d > 0`, `E_k = P_de_k = IIIa.perE κ d k` is continuous.  Route: `perSum d f y
= Σ_n f(y₁ + nd, y₂)` is `Gaussian.periodize d f y = Σ_n f(y₁ - nd, y₂)` after `n ↦ -n`
(`(Equiv.neg ℤ).tsum_eq`); `κ.e_cont`; the Gaussian bound `κ.e_decay` gives
`‖e_k y‖ ≤ C'(1+|y₁|)^{-2}` (`e^{-t²/8}(1+|t|)² ≤ 9`, say); then
`UnforcedLeray.Gaussian.continuous_tsum_translates` (`Lib/Gaussian/Periodization.lean`). -/
def PerEContinuous : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (d : ℝ) (k : Fin 2), 0 < d → Continuous (IIIa.perE κ d k)

/-- **The unnormalized periodized dual rows are continuous** (source 2896-2899: "The planar dual
kernels and their fixed derivatives have the `O(|y|^{-2-j})` decay"): for `d > 0`,
`Λ⁰_k = P_dλ_k = IIIa.perLam0 κ d k` is continuous.  Route: as `PerEContinuous`, with `κ.lamP_cont`
and `κ.lamP_decay` (`(1+|y₁|+|y₂|)⁻¹ ≤ (1+|y₁|)⁻¹`), `s = 2` in
`Gaussian.continuous_tsum_translates`. -/
def PerLam0Continuous : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (d : ℝ) (k : Fin 2), 0 < d → Continuous (IIIa.perLam0 κ d k)

/-- **`q_{k,s}(x)` is continuous in the age** (source 4352-4356, 4650-4654: the pair depends
continuously on `s`).  Route: with `a = bandA ν s ∈ [1, 3]` (continuous in `s`; `bandAge` is a clamp),
`qFun κ ν c k s x = a^{-2}Σ_n e_k((x₁ + nc)/√a, x₂/√a)` (`x₁/√a + n(c/√a) = (x₁+nc)/√a`); each term is
continuous in `s`, and `‖e_k((x₁+nc)/√a, x₂/√a)‖ ≤ C e^{-(x₁+nc)²/24}` uniformly in `s` (`κ.e_decay`,
`a ≤ 3`), summable in `n`; `continuous_tsum`. -/
def QFunPtCont : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2) (x : ℝ × ℝ), 0 < ν → 16 ≤ c →
    Continuous fun s => qFun κ ν c k s x

/-- **`a Λ⁰_{d,k}(x/√a)` is continuous in the age** (source 2896-2899, 4352-4356).  Route: as
`QFunPtCont`: `lam0Ker κ ν c k s x = a Σ_n λ_k((x₁ + nc)/√a, x₂/√a)`, and
`‖λ_k((x₁+nc)/√a, ·)‖ ≤ C(1 + |x₁+nc|/√3)^{-2} ≤ 3C(1+|x₁+nc|)^{-2}` uniformly in `s`
(`κ.lamP_decay`, `a ≤ 3`), summable in `n` (`Gaussian.summable_translate`); `continuous_tsum`. -/
def Lam0KerPtCont : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2) (x : ℝ × ℝ), 0 < ν → 16 ≤ c →
    Continuous fun s => lam0Ker κ ν c k s x

/-- **Gaussian tails of `q_{k,s}`, uniform in the age** (source 2894-2899: "direct columns have
Gaussian tails").  Route: `‖e_k y‖ ≤ C e^{-|y|²/8}` (`κ.e_decay`, `C ≥ 0`) and `1 ≤ a ≤ 3` give
`‖qFun κ ν c k s x‖ ≤ a^{-2}Σ_n ‖e_k((x₁+nc)/√a, x₂/√a)‖ ≤ Σ_n C e^{-((x₁+nc)² + x₂²)/24}`
(`norm_tsum_le_tsum_norm`; `x₁/√a + n(c/√a) = (x₁+nc)/√a`); the last sum is `≤ 10C e^{-x₂²/24}` by
`UnforcedLeray.Gaussian.norm_periodize_le_of_gauss` (`Lib/Gaussian/Periodization.lean`) applied to
the real function `z ↦ C e^{-(z₁²+z₂²)/24}` (`4a' = 24`, `a' = 6 ≤ c²`; reindex `n ↦ -n`).
Take `A = 10C`. -/
def QFunGaussBound : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2), 0 < ν → 16 ≤ c →
    ∃ A : ℝ, ∀ s x, ‖qFun κ ν c k s x‖ ≤ A * Real.exp (-(x.2 ^ 2) / 24)

/-- **A transverse Gaussian lies in `X_{m,c}`** (source 2828, 4349-4350: `X_{m,c} =
L²(cell, ⟨x⟩^{2m}dx)`; the cell `[-c/2, c/2) × ℝ` has bounded width).  Route:
`memLp_two_iff_integrable_sq` (the function is continuous), `B0579.cellMeasure` is
`(volume.restrict (cell c)).withDensity (density m)`, `integrable_withDensity_iff_integrable_smul`;
on the cell `⟨x⟩^{2m} ≤ (1 + c²)^{|m|}(1 + x₂²)^{|m|}` (`|x₁| ≤ c/2`; for `m < 0` the weight is `≤ 1`)
and `(1+η²)^{|m|}e^{-η²/12} ≤ K e^{-η²/24}`; a bounded interval in `x₁` times an integrable
Gaussian in `x₂` (`integrable_exp_neg_mul_sq`, `Integrable.mul_prod`, `Measure.volume_eq_prod`,
`Integrable.mono'`).  For `c ≤ 0` the cell is empty. -/
def GaussStripMemLp : Prop :=
  ∀ (c m A : ℝ),
    MemLp (fun x : ℝ × ℝ => A * Real.exp (-(x.2 ^ 2) / 24)) 2 (B0579.cellMeasure c m)

/-- **The dual kernels are bounded on the cell, uniformly in the age** (source 2896-2899: the
`O(|y|⁻²)` decay of the planar dual kernels; their periodizations are bounded).  Route: for
`x ∈ cell c` (`|x₁| ≤ c/2`) and `n ≠ 0`, `|x₁ + nc|/√a ≥ |n|c/(2√3) ≥ |n|` (`c ≥ 16`, `a ≤ 3`), so
`‖λ_k((x₁+nc)/√a, x₂/√a)‖ ≤ C(1+|n|)^{-2}` for every `n` (`κ.lamP_decay`), and
`‖lam0Ker κ ν c k s x‖ ≤ 3C Σ_n (1+|n|)^{-2}` (`norm_tsum_le_tsum_norm`,
`Gaussian.summable_one_add_abs_int_rpow`). -/
def Lam0KerBdd : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2), 0 < ν → 16 ≤ c →
    ∃ M : ℝ, ∀ s x, x ∈ B0579.cell c → ‖lam0Ker κ ν c k s x‖ ≤ M

/-- **`q_{k,s}` has zero circulation** (source 4349-4350: `X_{m,c}` is the zero-circulation
subspace; 597: `∫ q = 0`).  Route: `qFun κ ν c k s = P_c(J_a e_k)` pointwise
(`a^{-2}e_k(x₁/√a + n c/√a, x₂/√a) = J_ae_k(x₁ + nc, x₂)`, then `n ↦ -n` to the form of
`Cyl.periodize`); `UnforcedLeray.Cyl.integral_cell_periodize_mul` with the periodic `g = 1`
(`Cyl.cell c = B0579.cell c`, `neg_div`) gives `∫_cell P_c(J_ae_k) = ∫_{ℝ²} J_ae_k`
(`J_ae_k` continuous, integrable by `κ.e_decay`); `∫ J_ae_k = a^{-2}∫ e_k(a^{-1/2} • y) dy
= a^{-1}∫ e_k = 0` (`Measure.integral_comp_smul`, `finrank ℝ (ℝ × ℝ) = 2`). -/
def QFunCirc : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c : ℝ) (k : Fin 2) (s : ℝ), 0 < ν → 16 ≤ c →
    ∫ y, κ.e k y = 0 → ∫ x in B0579.cell c, qFun κ ν c k s x = 0

/-! ## Leaves: the change of variables and dominated convergence -/

/-- **The heat-scaling change of variables on the cells** (source 2858-2864, 3030-3035: `d = c/√a`,
`x = √a y`): `∫_{cell d} F(√a y) dy = a⁻¹∫_{cell c} F`.  Route: `y ∈ cell (c/√a) ↔ √a • y ∈ cell c`,
so the left side is `∫ (cell c).indicator F (√a • y) dy`; `Measure.integral_comp_smul`
(`volume` on `ℝ × ℝ` is an additive Haar measure, `finrank ℝ (ℝ × ℝ) = 2`, `|(√a²)⁻¹| = a⁻¹`);
`integral_indicator`. -/
def IntegralCellDilate : Prop :=
  ∀ (F : ℝ × ℝ → ℂ) (a c : ℝ), 0 < a → 0 < c →
    ∫ y in B0579.cell (IIIa.cellLen c a), F (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      (a : ℂ)⁻¹ * ∫ x in B0579.cell c, F x

/-- **Continuity into `L²` by dominated convergence** (used for the continuity in the age of
`q_{±,s}` and `ℓ_{±,s}`, source 4352-4356).  Route: `‖(hF s).toLp - (hF t).toLp‖ =
(eLpNorm (F s - F t) 2 μ).toReal` (`Lp.dist_def`/`Lp.norm_toLp`, `MemLp.toLp_sub`); at each `t`,
`‖F s x - F t x‖ ^ 2 ≤ (2 g x) ^ 2` (integrable, `MemLp g 2 μ`) and `→ 0` a.e. as `s → t`;
`tendsto_lintegral_filter_of_dominated_convergence` (`𝓝 t` is countably generated). -/
def ContinuousToLpOfDominated : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (F : ℝ → ℝ × ℝ → ℂ) (hF : ∀ s, MemLp (F s) 2 μ) (g : ℝ × ℝ → ℝ),
    MemLp g 2 μ → (∀ s, ∀ᵐ x ∂μ, ‖F s x‖ ≤ g x) → (∀ᵐ x ∂μ, Continuous fun s => F s x) →
      Continuous fun s => (hF s).toLp (F s)

/-! ## Leaves: the symmetries of the Part I seed -/

/-- **The planar growing vectors are centrally even** (source 597: `q = h(r)e^{2iϑ}`, `e₁ = q̄`).
Route: `IIIa.IsSeedKernels`: `κ.e 0 y = PartI.seedPlanar h (planeToC y)`, `κ.e 1 y = conj (...)`;
`planeToC (-y) = -planeToC y`; `seedPlanar h (-z) = h ‖-z‖ * (-z/‖-z‖)^2 = seedPlanar h z`
(`Planar.NUE.Ang.ofProfile`, `angPhase`; `norm_neg`, `neg_div`, `Even.neg_zpow`). -/
def SeedKernelEven : Prop :=
  ∀ κ : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ →
    ∀ (k : Fin 2) (y : ℝ × ℝ), κ.e k (-y) = κ.e k y

/-- **The planar growing vectors have zero mass** (source 597: "`∫ q = 0`").  Route: with
`R(y₁, y₂) = (-y₂, y₁)`, `planeToC (R y) = I * planeToC y` and `seedPlanar h (I z) = -seedPlanar h z`
(`(Iz/‖Iz‖)² = I²(z/‖z‖)²`, `‖Iz‖ = ‖z‖`); `R` preserves Lebesgue measure on `ℝ × ℝ`
(`Prod.swap` and a coordinate negation, `MeasurePreserving.integral_comp'` with the
`MeasurableEquiv`), so `∫ e₀ = ∫ e₀ ∘ R = -∫ e₀` (no integrability needed); `∫ e₁ = conj ∫ e₀`
(`integral_conj`). -/
def SeedKernelMeanZero : Prop :=
  ∀ κ : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ → ∀ k : Fin 2, ∫ y, κ.e k y = 0

/-- **Conjugation of the angular sectors** (source 601-604: `f₂` is the angular-two sector,
`02_prelim.tex:30-31` convention of `Planar.NUE.Polar.angularSector`): the conjugate of the sector
`-2` of `f` is the sector `2` of `f̄`.  Route: unfold `angularSector`
(`(2π)⁻¹∫_0^{2π} g(re^{iθ})e^{-iℓθ}dθ`); `conj ((2π : ℂ)⁻¹) = (2π : ℂ)⁻¹`; the interval integral
commutes with `conj` (`intervalIntegral.integral_of_le` and `integral_conj`, no integrability
needed); `conj (exp (2θI)) = exp (-2θI)` (`Complex.exp_conj`, `map_mul`, `Complex.conj_I`,
`Complex.conj_ofReal`). -/
def AngularSectorConj : Prop :=
  ∀ (f : ℂ → ℂ) (r : ℝ), conj (Planar.NUE.Polar.angularSector f (-2) r) =
    Planar.NUE.Polar.angularSector (fun z => conj (f z)) 2 r

/-- **The planar dual kernels are conjugate** (source 601-610, 2896-2899: `λ₁` represents the
conjugate functional on the sector `-2`).  Route: `D := κ.lamP 1 - conj ∘ κ.lamP 0` is continuous;
for `f : ℂ → ℂ` smooth with compact support, `fun r => conj (angularSector f (-2) r) =
angularSector (conj ∘ f) 2` (`AngularSectorConj`), so by the two identities of
`IIIa.IsSeedKernels` (the first one applied to `conj ∘ f`, smooth with compact support),
`∫ lamP 1 · f = conj ∫ lamP 0 · conj f = ∫ conj (lamP 0) · f` (`integral_conj`); for a real smooth
compactly supported `g` on `ℝ × ℝ` take `f z = g (z.re, z.im)` (so `f (planeToC y) = g y`):
`∫ g • D = 0` (`Continuous.integrable_of_hasCompactSupport`, `integral_sub`);
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, then `D = 0` everywhere by continuity
(`Continuous.ae_eq_iff_eq`). -/
def SeedDualConj : Prop :=
  ∀ κ : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ →
    ∀ y : ℝ × ℝ, κ.lamP 1 y = conj (κ.lamP 0 y)

/-- **The Gram normalization preserves the conjugation symmetry** (source 2894-2896, 4353-4356:
`q_- = q̄_+` forces `ℓ_- = ℓ̄_+`).  If `e₁ = ē₀` and `λ₁ = λ̄₀`, then `Λ⁰₁ = Λ̄⁰₀`, `E₁ = Ē₀`
(`Complex.conj_tsum`), the Gram matrix has the form `G = [[p, q], [q̄, p̄]]` (`integral_conj`, no
integrability needed), `det G = |p|² - |q|²` is real, and `G⁻¹ = det⁻¹ [[p̄, -q], [-q̄, p]]`
(`Matrix.inv_def`, `Matrix.adjugate_fin_two`, `Matrix.det_fin_two`, `Ring.inverse_eq_inv'`), so
`Λ₁ = Λ̄₀` (`Fin.sum_univ_two`). -/
def PerLamConj : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (d : ℝ), (∀ y, κ.e 1 y = conj (κ.e 0 y)) →
    (∀ y, κ.lamP 1 y = conj (κ.lamP 0 y)) →
      ∀ y, IIIa.perLam κ d 1 y = conj (IIIa.perLam κ d 0 y)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
