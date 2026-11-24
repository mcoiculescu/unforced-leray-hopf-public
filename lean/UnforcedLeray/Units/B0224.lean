import UnforcedLeray.Units.B0224.NormEq
import UnforcedLeray.Units.B0224.Semigroup

/-!
# B0224: the explicit limiting cylinder semigroup `T_0(t)` and its `H`-adjoint

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379
(§`sec:st18-2379`, "Actual causality emerges in the limit"). On
`H = L²(s^{-3/2} ds dq dη)`, `q` in one period cell `(0, c]` (tex lines 3305–3308; B0220
`HSpace c E`, functions on the cell, extended `c`-periodically in `q` by `B0220.periodize`):

  `T_0(t)f(s)   = e^{νs(1-e^{-t})Δ_{q,η}} f(se^{-t})`,
  `T_0(t)^*f(s) = e^{-t/2} e^{νs(e^t-1)Δ_{q,η}} f(se^t)`,          (eq:st18-t00117)

and "both have norm `e^{-t/4}` on `H`" (tex line 3376).

Lean objects (namespace `UnforcedLeray.B0224`, helper modules `Units/B0224/*`):

| Manuscript | Lean |
|---|---|
| `e^{θΔ_{q,η}}`, heat of the cylinder `(ℝ/cℤ) × ℝ` | `planeHeat θ u` (`= Heat.heatConv planeι θ u` for `θ > 0`, the planar Gaussian average of the periodic field `u`, decision D1/D17; `= u` for `θ ≤ 0`) |
| `T_0(t)` | `T0 hc ν t : HSpace c E →L[ℝ] HSpace c E`, formula `T0_apply_ae` |
| `T_0(t)^*` | `T0adj hc ν t`, formula `T0adj_apply_ae` |
| `T_0(t)^*` is the `H`-adjoint | `adjoint_T0_eq` |
| `‖T_0(t)‖ = ‖T_0(t)^*‖ = e^{-t/4}` | `norm_T0_eq`, `norm_T0adj_eq` |
| semigroup law, `T_0(0) = 1` | `T0_zero_eq`, `T0_add_eq` |
| the whole unit | `B0224_statement` |

Construction (blueprint proof outline): `T_0(t) = H_{θ_t} D_{e^{-t}}`, where `D_a f(s) = f(as)`
(`dilH`, `‖D_a f‖ = a^{1/4}‖f‖` by the substitution `σ = as`, `D_a^† = a^{1/2}D_{1/a}`) and
`H_θ` is the cylinder heat at the age-dependent time `θ(s)` (`heatH`, a self-adjoint contraction
of `H`: Jensen, conservation of the strip mass, Fubini and the symmetry of the Gaussian). The
lower bound `‖T_0(t)‖ ≥ e^{-t/4}` uses the test functions `1_{(δ,2δ]}(s)s^{3/4}V(η)`, `δ → 0`,
and the strong continuity of the heat at time `0` (`Heat.tendsto_heatLp_sub`).

Conventions and scope:
* `E` is any real Hilbert space (`ℝ` for the scalar operator, `Merid = ℝ²` for the meridional
  vector operator, where the heat acts componentwise); the adjoint is the Hilbert adjoint of `H`.
  The norm identity needs `E ≠ 0` (for `E = 0`, `H = 0`).
* The formulas, the adjoint identity and the norm identity hold for every real `t` and `ν`
  (the manuscript states them for `t ≥ 0`, `ν > 0`); the semigroup law is stated for
  `t, t' ≥ 0`, `ν ≥ 0`. `B0224_statement` carries the manuscript's hypotheses `ν > 0`, `t ≥ 0`.
* `c > 0` is needed for the cell (`hc`).

Not formalized here: that `T_0` is the semigroup *generated* by `A_0 = -S + νsΔ_{q,η}`
(B0221; differentiating at `t = 0` on smooth tests, blueprint proof outline), and the strong
continuity of `t ↦ T_0(t)f`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.B0220

variable {c : ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **`T_0(t)f(s) = e^{νs(1-e^{-t})Δ_{q,η}} f(se^{-t})`** (tex line 3373), almost everywhere on
the cell, with the `c`-periodic extension of `f` in `q`. -/
theorem T0_apply_ae (hc : 0 < c) (ν t : ℝ) (f : HSpace c E) :
    T0 hc ν t f =ᵐ[measureH c] fun p => planeHeat (ν * p.1 * (1 - Real.exp (-t)))
      (fun z => periodize c (f : Profile → E) (Real.exp (-t) * p.1, z)) p.2 :=
  coeFn_T0 hc ν t f

/-- **`T_0(t)^*f(s) = e^{-t/2} e^{νs(e^t-1)Δ_{q,η}} f(se^t)`** (tex line 3374). -/
theorem T0adj_apply_ae (hc : 0 < c) (ν t : ℝ) (f : HSpace c E) :
    T0adj hc ν t f =ᵐ[measureH c] fun p => Real.exp (-t / 2) •
      planeHeat (ν * p.1 * (Real.exp t - 1))
        (fun z => periodize c (f : Profile → E) (Real.exp t * p.1, z)) p.2 :=
  coeFn_T0adj hc ν t f

/-- **`T_0(t)^*` is the `H`-adjoint of `T_0(t)`** (tex lines 3371–3375). -/
theorem adjoint_T0_eq (hc : 0 < c) (ν t : ℝ) :
    ContinuousLinearMap.adjoint (T0 hc ν t : HSpace c E →L[ℝ] HSpace c E) = T0adj hc ν t :=
  adjoint_T0 hc ν t

/-- **`‖T_0(t)‖ = e^{-t/4}`** on `H` (tex line 3376). -/
theorem norm_T0_eq [Nontrivial E] (hc : 0 < c) (ν t : ℝ) :
    ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ = Real.exp (-t / 4) :=
  norm_T0 hc ν t

/-- **`‖T_0(t)^*‖ = e^{-t/4}`** on `H` (tex line 3376). -/
theorem norm_T0adj_eq [Nontrivial E] (hc : 0 < c) (ν t : ℝ) :
    ‖(T0adj hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ = Real.exp (-t / 4) := by
  rw [norm_T0adj_eq_norm_T0, norm_T0]

/-- `T_0(0) = 1`. -/
theorem T0_zero_eq (hc : 0 < c) (ν : ℝ) : (T0 hc ν 0 : HSpace c E →L[ℝ] HSpace c E) = 1 :=
  T0_zero hc ν

/-- The semigroup law `T_0(t + t') = T_0(t) T_0(t')`, `t, t' ≥ 0`, `ν ≥ 0`. -/
theorem T0_add_eq (hc : 0 < c) {ν t t' : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    (T0 hc ν (t + t') : HSpace c E →L[ℝ] HSpace c E) = T0 hc ν t ∘L T0 hc ν t' :=
  T0_add hc hν ht ht'

/-- **Unit B0224** (tex lines 3370–3379), with the manuscript's hypotheses `ν > 0`, `t ≥ 0`
(`c > 0`, `E ≠ 0` a real Hilbert space): the two formulas, the adjoint relation, both norms
equal to `e^{-t/4}`, and the semigroup law of the family `T_0`. -/
theorem B0224_statement [Nontrivial E] (hc : 0 < c) {ν : ℝ} (hν : 0 < ν) {t : ℝ}
    (ht : 0 ≤ t) :
    (∀ f : HSpace c E, T0 hc ν t f =ᵐ[measureH c] fun p =>
        planeHeat (ν * p.1 * (1 - Real.exp (-t)))
          (fun z => periodize c (f : Profile → E) (Real.exp (-t) * p.1, z)) p.2) ∧
    (∀ f : HSpace c E, T0adj hc ν t f =ᵐ[measureH c] fun p => Real.exp (-t / 2) •
        planeHeat (ν * p.1 * (Real.exp t - 1))
          (fun z => periodize c (f : Profile → E) (Real.exp t * p.1, z)) p.2) ∧
    ContinuousLinearMap.adjoint (T0 hc ν t : HSpace c E →L[ℝ] HSpace c E) = T0adj hc ν t ∧
    ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ = Real.exp (-t / 4) ∧
    ‖(T0adj hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ = Real.exp (-t / 4) ∧
    (T0 hc ν 0 : HSpace c E →L[ℝ] HSpace c E) = 1 ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      (T0 hc ν (t₁ + t₂) : HSpace c E →L[ℝ] HSpace c E) = T0 hc ν t₁ ∘L T0 hc ν t₂) := by
  have _ := ht
  exact ⟨T0_apply_ae hc ν t, T0adj_apply_ae hc ν t, adjoint_T0_eq hc ν t, norm_T0_eq hc ν t,
    norm_T0adj_eq hc ν t, T0_zero_eq hc ν,
    fun t₁ t₂ h₁ h₂ => T0_add_eq hc hν.le h₁ h₂⟩

end UnforcedLeray.B0224
