import UnforcedLeray.Short.PartIIa.Sub.N02_4

/-!
# Part II-a, task `PartII-a:N02/4/4` (`NzFinPotentials`): decomposition into per-mode lemma Props

Source of record: `the November 2 reference manuscript`, lines 1713-1727 (on each
nonzero `q`-frequency the flat field is `(φ_q, φ_η) + (-ψ_η, ψ_q)`; the inverse `q`-derivative costs
`c/(2π)`; one `η`-moment costs a fixed power of `c`) and 1744-1745 (finite Fourier sums, Schwartz
transverse profiles).

For a finite-mode test `f = Σ_{n ∈ M} e^{i k_n q} a_n(s, η)`, `k_n = 2πn/c`, the potentials are
`φ = Σ e^{i k_n q} φ_n`, `ψ = Σ e^{i k_n q} ψ_n` where, for each mode, `(φ_n, ψ_n)` solves the ODE system
```
  i k φ - ∂_η ψ = a,      ∂_η φ + i k ψ = b        (k = k_n, (a, b) = a_n components)
```
(`f_r = (φ_q) + (-ψ_η)`, `f_z = φ_η + ψ_q`). The four Props below are the ingredients:

* `NzModeSolve`: existence of a smooth, `s`-band supported, exponentially decaying solution, with
  smooth dependence on the parameter `s` (explicit Green kernel `e^{-|k||η|}/(2|k|)`);
* `NzEnergy1D`: the energy identity
  `∫ |a|² + |b|² = ∫ k²|φ|² + |φ'|² + k²|ψ|² + |ψ'|²` (the cross term is `-2 Re(i k (φ ψ̄)')`);
* `NzModeBounds`: the weighted moment bounds in `S` and `η`, from the energy identity applied to
  `(S^α φ, S^α ψ)` and to `(η S^α φ, η S^α ψ)` with data `(η a - ψ, η b + φ)`;
* `NzQParseval`: `q`-orthogonality of the modes on one period.

The assembly (`NzFinPotentials` from these four) is the remaining task `PartII-a:N02/4/4`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Two-variable (`s`, `η`) notions for one `q`-mode -/

/-- `S = s ∂_s` on functions of `(s, η)`. -/
def nzS2 (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => x.1 • fderiv ℝ g x (1, 0)

/-- `(∫_{s > 0} ∫_ℝ (|η|^j)² ‖S^α g‖² s^{-3/2} dη ds)^{1/2}`: the `H`-moment of a one-mode coefficient
(`g(s, η)`; the `q`-factor is handled by `NzQParseval`). -/
def nzMom2 (j α : ℕ) (g : ℝ × ℝ → ℂ) : ℝ :=
  (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      (|x.2| ^ j) ^ 2 * ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ^ (1 / 2 : ℝ)

/-- Band and compact `η`-support (`s ∈ [s₀, s₁]`, `s₀ > 0`, `|η| ≤ L`). -/
def NzBand2 (a : ℝ × ℝ → ℂ) : Prop :=
  ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, a x ≠ 0 → x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L

/-- A one-mode potential: smooth, supported in an `s`-band, and all derivatives of order `≤ 2` decay
exponentially in `η`, uniformly in `s`. -/
def NzDecay2 (φ : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, φ x ≠ 0 → x.1 ∈ Icc s0 s1) ∧
    ∃ κ C : ℝ, 0 < κ ∧ ∀ (x : ℝ × ℝ) (m : ℕ), m ≤ 2 →
      ‖iteratedFDeriv ℝ m φ x‖ ≤ C * Real.exp (-κ * |x.2|)

/-- The one-mode flat Hodge equations `i k φ - ∂_η ψ = a`, `∂_η φ + i k ψ = b`. -/
def NzModeEq (k : ℝ) (a b φ ψ : ℝ × ℝ → ℂ) : Prop :=
  ∀ x : ℝ × ℝ, Complex.I * (k : ℂ) * φ x - fderiv ℝ ψ x (0, 1) = a x ∧
    fderiv ℝ φ x (0, 1) + Complex.I * (k : ℂ) * ψ x = b x

/-! ### The four lemma Props -/

/-- **Lemma NzModeSolve: one-mode potentials.** For `k ≠ 0` and smooth band-supported data `(a, b)` there
are smooth band-supported exponentially decaying `φ, ψ` solving the one-mode equations. Explicitly
`φ = i k G_k * a + G_k' * b`, `ψ = i k G_k * b - G_k' * a` (convolution in `η`, `s` a parameter),
`G_k(η) = -e^{-|k||η|}/(2|k|)`, `G_k'(η) = sgn(η) e^{-|k||η|}/2`; derivatives fall on the data (smooth,
compactly supported), `G_k'' = k² G_k + δ` gives the equations, decay is `e^{-|k|(|η| - L)}`. -/
def NzModeSolve : Prop :=
  ∀ (k : ℝ), k ≠ 0 → ∀ (a b : ℝ × ℝ → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    NzBand2 a → NzBand2 b →
    ∃ φ ψ : ℝ × ℝ → ℂ, NzDecay2 φ ∧ NzDecay2 ψ ∧ NzModeEq k a b φ ψ

/-- **Lemma NzEnergy1D: the one-mode energy identity.** For `C¹` exponentially decaying `φ, ψ : ℝ → ℂ`
solving `i k φ - ψ' = a`, `φ' + i k ψ = b`:
`∫ |a|² + |b|² = ∫ k²|φ|² + |φ'|² + k²|ψ|² + |ψ'|²`. Expand the squares; the cross terms combine to
`-2 Re(i k (φ ψ̄)')`, which integrates to `0` because `φ ψ̄ → 0` at `±∞`. -/
def NzEnergy1D : Prop :=
  ∀ (k : ℝ) (φ ψ a b : ℝ → ℂ), ContDiff ℝ 1 φ → ContDiff ℝ 1 ψ →
    (∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖φ t‖ ≤ C * Real.exp (-κ * |t|) ∧ ‖deriv φ t‖ ≤ C * Real.exp (-κ * |t|) ∧
        ‖ψ t‖ ≤ C * Real.exp (-κ * |t|) ∧ ‖deriv ψ t‖ ≤ C * Real.exp (-κ * |t|)) →
    (∀ t : ℝ, Complex.I * (k : ℂ) * φ t - deriv ψ t = a t) →
    (∀ t : ℝ, deriv φ t + Complex.I * (k : ℂ) * ψ t = b t) →
    ∫ t : ℝ, (‖a t‖ ^ 2 + ‖b t‖ ^ 2) =
      ∫ t : ℝ, (k ^ 2 * ‖φ t‖ ^ 2 + ‖deriv φ t‖ ^ 2 + k ^ 2 * ‖ψ t‖ ^ 2 + ‖deriv ψ t‖ ^ 2)

/-- **Lemma NzModeBounds: one-mode moment bounds** (source lines 1722-1727: the inverse `q`-derivative
costs `|k|⁻¹ ≤ c/(2π)`, one `η`-moment costs a fixed power of it). With a universal constant `C`: for a
solution `(φ, ψ)` of the one-mode equations with data `(a, b)`, every `S^α`, `η^j` moment
(`α, j ∈ {0, 1}`) of `φ, ∂_ηφ, kφ, ψ, ∂_ηψ, kψ` is at most `C (1 + |k|⁻¹)²` times the sum of the
moments of `(a, b)` of orders `i ∈ {0, 1}`. Proof: the equations have `s`-independent coefficients, so
`(S^α φ, S^α ψ)` solves them with data `(S^α a, S^α b)`; apply `NzEnergy1D` for each `s` and integrate
against `s^{-3/2} ds` for `j = 0` (so `‖kφ‖, ‖φ_η‖, ‖kψ‖, ‖ψ_η‖ ≤ ‖(a,b)‖` and `‖φ‖ ≤ |k|⁻¹‖(a,b)‖`);
for `j = 1` apply it to `(η S^α φ, η S^α ψ)`, which solves the system with data
`(η S^α a - S^α ψ, η S^α b + S^α φ)`, and use `η φ_η = (η φ)_η - φ`. -/
def NzModeBounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℝ), k ≠ 0 → ∀ (a b φ ψ : ℝ × ℝ → ℂ),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → NzBand2 a → NzBand2 b → NzDecay2 φ → NzDecay2 ψ →
    NzModeEq k a b φ ψ →
    ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
      ∀ g ∈ ({φ, fun x => fderiv ℝ φ x (0, 1), fun x => (k : ℂ) * φ x,
          ψ, fun x => fderiv ℝ ψ x (0, 1), fun x => (k : ℂ) * ψ x} : Set (ℝ × ℝ → ℂ)),
        nzMom2 j α g ≤
          C * (1 + |k|⁻¹) ^ 2 * ∑ i ∈ Finset.range 2, (nzMom2 i α a + nzMom2 i α b)

/-- **Lemma NzQParseval: orthogonality of `q`-modes on one period.** For a finite set `M` of integers and
vectors `v_n ∈ ℂ²`: `∫_0^c ‖Σ_{n∈M} e^{2π i n q / c} v_n‖² dq = c Σ_{n∈M} ‖v_n‖²`
(`∫_0^c e^{2π i (n - m) q / c} dq = c δ_{nm}`). -/
def NzQParseval : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (v : ℤ → MeridC),
    ∫ q in (0 : ℝ)..c,
        ‖∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v n‖ ^ 2 =
      c * ∑ n ∈ M, ‖v n‖ ^ 2

end UnforcedLeray.Short.PartIIa
