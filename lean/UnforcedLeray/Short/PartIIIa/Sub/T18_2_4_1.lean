import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4
import UnforcedLeray.Units.B0284.Defs

/-!
# Part III-a, task `PartIII-a:T18/2/4/1`: the unprojected classical solve (conditional)

Target (`Sub/T18_2_4.lean`): `HeatCellClassical`. For `c, ν > 0`, `μ ∈ ℂ` and a nice force `F`
there is a globally smooth, `c`-periodic `u` with `u = 0` for `s ≤ a`, solving
`u_s + (μ/s) u - νΔu = div F` classically for `s > 0`, with Gaussian decay in `η`
(locally uniformly in `s`).
Source of record: `the November 2 reference manuscript`, lines 3427-3440
("start from zero at `s = δ`, let `δ ↓ 0`"; the free instance of the energy argument).

## Decomposition


in the library. It splits into a scalar heat problem and a bookkeeping reduction.

1. (*Scalar heat Duhamel*, four leaves about one explicit function `duhamelHeat`.) For a *nice
   scalar source* `h` (`NiceScalar`: smooth, `c`-periodic in `q`, zero for `s < a`, `s > B`,
   `|η| > R`, `a > 0`),
   `w(s, x) = ∫_{r > 0} ∫_{ℝ²} G_{νr}(z) h(s - r, x - z) dz dr` (`G_θ` = `B0284.heatKernel2 θ`)
   is `C^∞`, `c`-periodic, vanishes for `s ≤ a`, solves `w_s - νΔw = h`, and has Gaussian decay
   in `η` for `w` and `∇_x w` uniformly in `s ≤ s₂`:
   `DuhamelSmooth`, `DuhamelPeriodicZero`, `DuhamelHeatEq`, `DuhamelDecay`.
2. (*Source is nice*, `DivSourceNice`) for a `NiceForce` `F` the scalar `h_i = t^μ Σ_j ∂_j F_ij`
   is a nice scalar source (the derivative of a function vanishing on an open set vanishes there).
3. (*Cpow reduction*, `CpowScale`) `u = s^{-μ} w` is smooth, solves
   `u_s + (μ/s) u - νΔu = s^{-μ}(w_s - νΔw)` for `s > 0`, and keeps the Gaussian decay.

Proved here: `heatNiceScalar_of` (the four Duhamel leaves give a scalar solve with all the
properties) and `heatCellClassical_of` (the wiring: apply the scalar solve to `h_0, h_1`, the cpow
reduction to each, and use `s^{-μ} s^{μ} = 1`). The unconditional leaves are the tasks
`PartIII-a:T18/2/4/1/1 ... /6`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Definitions -/

/-- A *nice scalar source* on `ℝ × (ℝ × ℝ)`: `ℂ`-valued, jointly smooth in `(s, q, η)`,
`c`-periodic in `q`, vanishing for `s < a` (some `a > 0`), `s > B` and `|η| > R`. -/
def NiceScalar (c : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ContDiff ℝ ∞ h ∧ (∀ s x, h (s, (x.1 + c, x.2)) = h (s, x)) ∧
    ∃ a B R : ℝ, 0 < a ∧ ∀ s x, (s < a ∨ B < s ∨ R < |x.2|) → h (s, x) = 0

/-- The scalar Duhamel solution of the planar heat equation with source `h`:
`w(s, x) = ∫_{r > 0} ∫_{ℝ²} G_{νr}(z) h(s - r, x - z) dz dr`, where `G_θ` is the planar heat kernel
`B0284.heatKernel2 θ` (`(4πθ)^{-1} e^{-|z|²/(4θ)}`). For a nice source and `ν > 0` the integrand
vanishes unless `0 < r ≤ s - a`, so both integrals are genuine (no junk value is used). -/
def duhamelHeat (ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ) (s : ℝ) (x : ℝ × ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
    ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s - r, (x.1 - z.1, x.2 - z.2))

/-- `w_s - νΔw = h` pointwise, for the scalar `ℂ`-valued `w` (`lapC` is the planar Laplacian in
`x`, `deriv` the derivative in `s`). -/
def IsScalarHeatSol (ν : ℝ) (w h : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ (s : ℝ) (x : ℝ × ℝ),
    deriv (fun s' => w (s', x)) s - (ν : ℂ) * lapC (fun y => w (s, y)) x = h (s, x)

/-- Scalar version of `GaussianDecayLoc`: for every `s₂` there are `C` and `κ > 0` with
`‖w(s,x)‖ + ‖∇_x w(s,x)‖ ≤ C e^{-κ η²}` for all `s ≤ s₂`. -/
def ScalarGaussDecayLoc (w : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ s₂ : ℝ, ∃ C κ : ℝ, 0 < κ ∧ ∀ (s : ℝ) (x : ℝ × ℝ), s ≤ s₂ →
    ‖w (s, x)‖ + ‖fderiv ℝ (fun y => w (s, y)) x‖ ≤ C * Real.exp (-κ * x.2 ^ 2)

/-! ## The leaf statements -/

/-- **Leaf 1: smoothness of the Duhamel solution** (`PartIII-a:T18/2/4/1/1`; SP 3427-3440). For a
nice scalar source `h`, `(s, x) ↦ duhamelHeat ν h s x` is `C^∞` on `ℝ × (ℝ × ℝ)`.
Proof idea: substitute `z ↦ x - z`; the integrand `G_{νr}(x - y) h(s - r, y)` is smooth in `(s, x)`
for each `r`, all derivatives of `h` are bounded (periodic in `q`, compactly supported in `(s, η)`,
so supported in a compact set modulo `q`-translation), `G_{νr}` has unit mass, and for `s ≤ S`
the integrand vanishes for `r > S - a`: differentiate under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) iteratively; the derivatives fall on `h`. -/
def DuhamelSmooth : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h →
    ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => duhamelHeat ν h p.1 p.2

/-- **Leaf 2: periodicity and the zero entrance** (`PartIII-a:T18/2/4/1/2`; SP 3427-3440). The
Duhamel solution is `c`-periodic in `q` and vanishes for `s ≤ a` (the `a > 0` of the source).
Proof idea: periodicity of `h` in `q` after the substitution `x - z`; for `s ≤ a` and `r > 0`,
`s - r < a`, so the integrand is identically `0`. -/
def DuhamelPeriodicZero : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h →
    (∀ s x, duhamelHeat ν h s (x.1 + c, x.2) = duhamelHeat ν h s x) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ s x, s ≤ a → duhamelHeat ν h s x = 0

/-- **Leaf 3: the heat equation** (`PartIII-a:T18/2/4/1/3`; SP 3427-3440). The Duhamel solution
satisfies `w_s - νΔw = h` at every `(s, x)` (`deriv` in `s`, `lapC` in `x`).
Proof idea: `φ(r) = (G_{νr} * h(s - r))(x)` has `φ'(r) = (G_{νr} * (νΔh - ∂_t h)(s - r))(x)` by
`∂_θ G_θ = ΔG_θ` (`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean`,
`heatKernel2AgeDerivative_eq_spatialLaplacian`), and `w_s - νΔw = ∫_0^∞ (G_{νr} * (∂_t h - νΔh)
(s - r)) dr = -∫_0^∞ φ' = φ(0⁺) - φ(∞) = h(s, x)`, since `φ(r) = 0` for `r > s - a` and
`φ(r) → h(s, x)` as `r → 0⁺` (approximate identity). Uses `DuhamelSmooth` to differentiate
under the integral sign. -/
def DuhamelHeatEq : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h →
    IsScalarHeatSol ν (fun p : ℝ × (ℝ × ℝ) => duhamelHeat ν h p.1 p.2) h

/-- **Leaf 4: Gaussian decay** (`PartIII-a:T18/2/4/1/4`; SP 3427-3440). The Duhamel solution and
its `x`-gradient have Gaussian decay in `η`, locally uniformly in `s`.
Proof idea: derivatives in `x` fall on `h` (convolution commutes with `∂_j`), so it suffices to
bound `|(G_{νr} * g)(x)|` for `g` bounded with `g(s - r, ·) = 0` for `|η| > R` and
`r ≤ s₂ - a`: for `|η| ≥ 2R` the support forces `|z₂| ≥ |η|/2`, and the Gaussian tail
`∫_{|z₂| ≥ A} (4πθ)^{-1/2} e^{-z₂²/(4θ)} dz₂ ≤ 2 e^{-A²/(8θ)}` with `θ = νr ≤ ν(s₂ - a)` gives
`C e^{-η²/(32 ν (s₂ - a))}`; for `|η| ≤ 2R` use the bound `‖g‖∞ (s₂ - a)`. -/
def DuhamelDecay : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h →
    ScalarGaussDecayLoc (fun p : ℝ × (ℝ × ℝ) => duhamelHeat ν h p.1 p.2)

/-- **Leaf 5: the scalar sources of a nice force are nice** (`PartIII-a:T18/2/4/1/5`;
SP 3427-3440). For `F` a `NiceForce`, `h_i(s, x) = s^μ Σ_j ∂_j F_ij(s, x)` is a `NiceScalar`.
Proof idea: `Σ_j ∂_j F_ij(s,x) = Σ_j fderiv ℝ (F · i j) (s, x) (0, e_j)` is jointly smooth and
`c`-periodic; it vanishes when `s < a` or `s > B` (the slice `F(s, ·) i j` is identically `0`, so
its derivative is `0`) and when `|η| > R` (the slice vanishes on the open set `{|η| > R}`,
`Filter.EventuallyEq.fderiv_eq`); `s ↦ (s : ℂ)^μ` is smooth on `s > 0` and `h_i = 0` on the open set
`s < a`, `a > 0`, so `h_i` is smooth on `ℝ × plane` (glue the open sets `{s > 0}`, `{s < a}`). -/
def DivSourceNice : Prop :=
  ∀ (c : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), NiceForce c F → ∀ i : Fin 2,
    NiceScalar c (fun p : ℝ × (ℝ × ℝ) =>
      (p.1 : ℂ) ^ μ * ∑ j : Fin 2, pdC j (fun y => F (p.1, y) i j) p.2)

/-- **Leaf 6: the cpow reduction** (`PartIII-a:T18/2/4/1/6`; SP 3427-3440). If `w` is smooth,
`c`-periodic, zero for `s ≤ a` (`a > 0`), solves `w_s - νΔw = h` and has Gaussian decay, then
`u = s^{-μ} w` is smooth on all of `ℝ × plane`; for `s > 0` it solves
`u_s + (μ/s) u - νΔu = s^{-μ} h`; and it has Gaussian decay.
Proof idea: `u = 0` on the open set `s < a`, so smoothness is only needed on `s > 0` where
`(s : ℂ)^{-μ}` is smooth (`Complex.ofReal_cpow`, `exp (-μ log s)`); glue. The equation:
`d/ds s^{-μ} = -μ s^{-μ-1}` (`hasDerivAt_ofReal_cpow_const`), `s^{-μ-1} = s^{-μ}/s`,
and `lapC (c • f) = c * lapC f`, `fderiv (c • f) = c • fderiv f` for smooth `f`. Decay:
`‖u‖ + ‖∇u‖ = |s^{-μ}| (‖w‖ + ‖∇w‖)`, `|s^{-μ}| = s^{-Re μ}`
(`Complex.norm_cpow_eq_rpow_re_of_pos`) is bounded on `[a, s₂]` by continuity, and `u = 0`
for `s ≤ a`. -/
def CpowScale : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (a : ℝ) (h w : ℝ × (ℝ × ℝ) → ℂ), 0 < a →
    ContDiff ℝ ∞ w → (∀ s x, w (s, (x.1 + c, x.2)) = w (s, x)) → (∀ s x, s ≤ a → w (s, x) = 0) →
    IsScalarHeatSol ν w h → ScalarGaussDecayLoc w →
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ((p.1 : ℂ) ^ (-μ)) * w p) ∧
    (∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      deriv (fun s' : ℝ => ((s' : ℂ) ^ (-μ)) * w (s', x)) s +
          (μ / (s : ℂ)) * (((s : ℂ) ^ (-μ)) * w (s, x)) -
        (ν : ℂ) * lapC (fun y => ((s : ℂ) ^ (-μ)) * w (s, y)) x =
      ((s : ℂ) ^ (-μ)) * h (s, x)) ∧
    ScalarGaussDecayLoc (fun p : ℝ × (ℝ × ℝ) => ((p.1 : ℂ) ^ (-μ)) * w p)

/-- The scalar heat problem for a nice source, with all the properties (assembled from the four
Duhamel leaves). -/
def HeatNiceScalar : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h →
    ∃ (a : ℝ) (w : ℝ × (ℝ × ℝ) → ℂ), 0 < a ∧ ContDiff ℝ ∞ w ∧
      (∀ s x, w (s, (x.1 + c, x.2)) = w (s, x)) ∧ (∀ s x, s ≤ a → w (s, x) = 0) ∧
      IsScalarHeatSol ν w h ∧ ScalarGaussDecayLoc w

/-! ## The conditional assembly -/

/-- The four Duhamel leaves give the scalar heat problem with all properties. -/
theorem heatNiceScalar_of (h1 : DuhamelSmooth) (h2 : DuhamelPeriodicZero)
    (h3 : DuhamelHeatEq) (h4 : DuhamelDecay) : HeatNiceScalar := by
  intro c ν h hc hν hn
  obtain ⟨hper, a, ha, hz⟩ := h2 c ν h hc hν hn
  exact ⟨a, fun p => duhamelHeat ν h p.1 p.2, ha, h1 c ν h hc hν hn,
    fun s x => hper s x, fun s x hs => hz s x hs, h3 c ν h hc hν hn, h4 c ν h hc hν hn⟩

/-- Monotonicity of a Gaussian bound: a bound `L ≤ C e^{-κ t}` with `t ≥ 0` gives
`L ≤ C' e^{-κ' t}` for `κ' ≤ κ` and `|C| ≤ C'`. -/
theorem heatCC_decay_mono {L C κ C' κ' t : ℝ} (hκ : κ' ≤ κ) (hC : |C| ≤ C') (ht : 0 ≤ t)
    (h : L ≤ C * Real.exp (-κ * t)) : L ≤ C' * Real.exp (-κ' * t) := by
  have hexp : Real.exp (-κ * t) ≤ Real.exp (-κ' * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc L ≤ C * Real.exp (-κ * t) := h
    _ ≤ |C| * Real.exp (-κ * t) := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)
    _ ≤ |C| * Real.exp (-κ' * t) := mul_le_mul_of_nonneg_left hexp (abs_nonneg C)
    _ ≤ C' * Real.exp (-κ' * t) := mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)

/-- **`HeatCellClassical`, conditional on the six leaves.** -/
theorem heatCellClassical_of (h1 : DuhamelSmooth) (h2 : DuhamelPeriodicZero)
    (h3 : DuhamelHeatEq) (h4 : DuhamelDecay) (hD : DivSourceNice) (hB : CpowScale) :
    HeatCellClassical := by
  intro c ν μ hc hν F hF
  have hS : HeatNiceScalar := heatNiceScalar_of h1 h2 h3 h4
  choose a w ha hw hper hzero heq hdec using
    fun i : Fin 2 => hS c ν _ hc hν (hD c μ F hF i)
  have hBi := fun i : Fin 2 =>
    hB c ν μ (a i) _ (w i) (ha i) (hw i) (hper i) (hzero i) (heq i) (hdec i)
  refine ⟨fun p i => ((p.1 : ℂ) ^ (-μ)) * w i p, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hBi i).1
  · intro s x i
    show ((s : ℂ) ^ (-μ)) * w i (s, (x.1 + c, x.2)) = ((s : ℂ) ^ (-μ)) * w i (s, x)
    rw [hper i s x]
  · refine ⟨min (a 0) (a 1), lt_min (ha 0) (ha 1), ?_⟩
    intro s x i hs
    have hsi : s ≤ a i := by
      fin_cases i
      · exact hs.trans (min_le_left _ _)
      · exact hs.trans (min_le_right _ _)
    show ((s : ℂ) ^ (-μ)) * w i (s, x) = 0
    rw [hzero i s x hsi, mul_zero]
  · intro s hs x i
    have hmain := (hBi i).2.1 s hs x
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    have hne : (s : ℂ) ^ μ ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hs0 h.1
    show deriv (fun s' : ℝ => ((s' : ℂ) ^ (-μ)) * w i (s', x)) s +
          (μ / (s : ℂ)) * (((s : ℂ) ^ (-μ)) * w i (s, x)) -
        (ν : ℂ) * lapC (fun y => ((s : ℂ) ^ (-μ)) * w i (s, y)) x =
      ∑ j : Fin 2, pdC j (fun y => F (s, y) i j) x
    rw [hmain]
    show ((s : ℂ) ^ (-μ)) * ((s : ℂ) ^ μ * ∑ j : Fin 2, pdC j (fun y => F (s, y) i j) x) = _
    rw [Complex.cpow_neg, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · intro s₂
    obtain ⟨C0, κ0, hκ0, h0⟩ := (hBi 0).2.2 s₂
    obtain ⟨C1, κ1, hκ1, h1'⟩ := (hBi 1).2.2 s₂
    refine ⟨|C0| + |C1|, min κ0 κ1, lt_min hκ0 hκ1, ?_⟩
    intro s x i hs
    have ht : 0 ≤ x.2 ^ 2 := sq_nonneg _
    fin_cases i
    · exact heatCC_decay_mono (min_le_left _ _) (by linarith [abs_nonneg C1]) ht (h0 s x hs)
    · exact heatCC_decay_mono (min_le_right _ _) (by linarith [abs_nonneg C0]) ht (h1' s x hs)

end UnforcedLeray.Short.IIIa

end
