import UnforcedLeray.Units.B0225.Pointwise
import UnforcedLeray.Units.B0225.Substitution

/-!
# B0225: the causal formula `R_0(μ)M_s g(s) = ∫_0^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} g(σ) dσ`

Blueprint unit B0225 (label `eq:st18-t00118`), `paper/main.tex` lines 3379–3392
(§`sec:st18-2379`, "Actual causality emerges in the limit"), depending on B0224
(`eq:st18-t00117`, the limiting semigroup `T_0(t)`, tex lines 3370–3379) and B0223
(`eq:st18-t00116`, the free inverses, tex lines 3341–3368). The manuscript states (tex lines
3379–3386): integrating `eq:st18-t00117` gives

  `R_0(μ)M_s g(s) = ∫_0^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} g(σ) dσ`,        (eq:st18-t00118)

"thus the limit is exactly the causal cylinder heat inverse, with no missing factor of `s` or
`σ`". Here `R_0(μ)` is the `ε = 0` member of the inverses `R_ε(μ) = (μ - A_ε)^{-1}` of
`eq:st18-t00116`, for `γ = Re μ + 1/4 > 0` (tex line 3357), and `M_s : H_g → H` is the
isometry `g ↦ s g` of B0220 (tex line 3309).

## Formalization map

| Manuscript | Lean |
|---|---|
| `H`, `H_g`, `M_s` | B0220 `HSpace c E`, `HgSpace c E`, `Ms c E` (`E` complex: `ℂ` scalar, `ℂ²` meridional, heat componentwise) |
| `T_0(t)` | B0224 `T0 hc ν t` (formula `T0_apply_ae`) |
| `R_0(μ) = ∫_0^∞ e^{-μt} T_0(t) dt` | `R0 hc ν μ : HSpace c E →L[ℂ] HSpace c E` (Laplace transform, bypass BP4 as for B0223 `physRes`), `R0_apply`, `integrableOn_lapT0` |
| `‖R_0(μ)‖ ≤ γ⁻¹` | `norm_R0_le` (the `ε = 0` case of `eq:st18-t00116`) |
| `e^{θΔ_{q,η}}` | B0224 `planeHeat θ` applied to the `c`-periodic extension (`periodize`) |
| `(σ/s)^μ` | `((σ / s : ℝ) : ℂ) ^ μ` (complex power of a positive real) |
| `eq:st18-t00118` | `R0_Ms_ae` (a.e. in `H`; with a.e. integrability of the `σ`-integrand) |
| "causal": the value at age `s` sees the force only at ages `σ ≤ s` | `R0_Ms_causal` |
| the whole unit | `B0225_statement` |

Proof (blueprint outline): `R_0(μ)f(p) = ∫_0^∞ e^{-μt} (T_0(t)f)(p) dt` for a.e. `p`
(`R0_ae_eq`, file `B0225/Pointwise.lean`, Fubini against sets of finite measure); for
`f = M_s g`, `(T_0(t)M_s g)(s) = (se^{-t}) e^{ν(s - se^{-t})Δ} g(se^{-t})`
(`jointRep_Ms`), and the substitution `σ = se^{-t}` (`dt = -dσ/σ`, `e^{-μt} = (σ/s)^μ`) turns the
time integral into `∫_0^s` (`integral_substitution`, file `B0225/Substitution.lean`); the
factor `σ` of `M_s` cancels the Jacobian `1/σ`.

## Scope

* `R_0(μ)` is defined as the Laplace transform of `T_0`. That it is the two-sided inverse of
  `μ - A_0` (`A_0 = -S + νsΔ_{q,η}`, tex line 3336) is not proved here: it needs the strong
  continuity of `T_0` and the identification of its generator with `A_0`, which B0224 does not
  formalize (B0224 module docstring, "Not formalized here").
* Hypotheses: `c > 0`, `ν > 0` (used only in `B0225_statement`; the identity holds for every
  real `ν` with B0224's convention `planeHeat θ = id` for `θ ≤ 0`), `Re μ > -1/4`, `g ∈ H_g`.
* The remark of tex lines 3388–3392 (at finite `ε` the exact physical inverse is not triangular
  in actual age) is a caveat with no proof obligation (blueprint) and is not formalized.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.B0225

open UnforcedLeray.B0220 UnforcedLeray.B0224

variable {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **The causal cylinder heat operator** (right side of `eq:st18-t00118`, tex lines 3380–3383)
at `p = (s, q, η)`: `∫_0^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} g̃(σ, ·)(q, η) dσ`, `g̃` the `c`-periodic
extension of `g` in `q`. -/
def causalHeat (c ν : ℝ) (μ : ℂ) (g : Profile → E) (p : Profile) : E :=
  ∫ σ in (0 : ℝ)..p.1, ((σ / p.1 : ℝ) : ℂ) ^ μ •
    planeHeat (ν * (p.1 - σ)) (fun z => periodize c g (σ, z)) p.2

/-- `(T_0(t)M_s g)(s) = (se^{-t}) e^{ν(s - se^{-t})Δ} g̃(se^{-t})`: the factor `σ = se^{-t}` of
`M_s`, pulled out of the heat. -/
theorem jointRep_Ms (c ν : ℝ) (g : Profile → E) (t : ℝ) (p : Profile) :
    jointRep c ν (fun p => p.1 • g p) (t, p) =
      (Real.exp (-t) * p.1) • planeHeat (ν * (p.1 - Real.exp (-t) * p.1))
        (fun z => periodize c g (Real.exp (-t) * p.1, z)) p.2 := by
  have h1 : ν * p.1 * (1 - Real.exp (-t)) = ν * (p.1 - Real.exp (-t) * p.1) := by ring
  change planeHeat (ν * p.1 * (1 - Real.exp (-t)))
    (fun z => (Real.exp (-t) * p.1) • periodize c g (Real.exp (-t) * p.1, z)) p.2 = _
  rw [planeHeat_smul, h1]

theorem stronglyMeasurable_ageMul (g : HgSpace c E) :
    StronglyMeasurable fun p : Profile => p.1 • (g : Profile → E) p :=
  measurable_fst.stronglyMeasurable.smul (Lp.stronglyMeasurable g)

/-- **`eq:st18-t00118`** (tex lines 3379–3383): for `Re μ > -1/4` and `g ∈ H_g`, for a.e.
`p = (s, q, η)` the integrand `σ ↦ (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} g(σ)` is integrable on `(0, s)`
and `R_0(μ)M_s g(p) = ∫_0^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} g(σ) dσ`. -/
theorem R0_Ms_ae (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (g : HgSpace c E) :
    (∀ᵐ p ∂measureH c, IntervalIntegrable (fun σ => ((σ / p.1 : ℝ) : ℂ) ^ μ •
      planeHeat (ν * (p.1 - σ)) (fun z => periodize c (g : Profile → E) (σ, z)) p.2)
      volume 0 p.1) ∧
    (R0 hc ν μ (Ms c E g) : Profile → E) =ᵐ[measureH c] fun p =>
      ∫ σ in (0 : ℝ)..p.1, ((σ / p.1 : ℝ) : ℂ) ^ μ •
        planeHeat (ν * (p.1 - σ)) (fun z => periodize c (g : Profile → E) (σ, z)) p.2 := by
  obtain ⟨h1, h2⟩ := R0_ae_eq hc ν hμ (Ms c E g) (stronglyMeasurable_ageMul g)
    (coeFn_Ms c g).symm
  constructor
  · filter_upwards [h1, ae_cell_measureH c] with p hp hcell
    simp_rw [jointRep_Ms] at hp
    exact (integrableOn_substitution_iff (E := E) hcell.1 μ (fun σ =>
      planeHeat (ν * (p.1 - σ)) (fun z => periodize c (g : Profile → E) (σ, z)) p.2)).1 hp
  · filter_upwards [h2, ae_cell_measureH c] with p hp hcell
    rw [hp]
    simp_rw [jointRep_Ms]
    exact integral_substitution (E := E) hcell.1 μ (fun σ =>
      planeHeat (ν * (p.1 - σ)) (fun z => periodize c (g : Profile → E) (σ, z)) p.2)

/-- `eq:st18-t00118` with the right side written as `causalHeat`. -/
theorem R0_Ms_ae_causalHeat (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (g : HgSpace c E) :
    (R0 hc ν μ (Ms c E g) : Profile → E) =ᵐ[measureH c] causalHeat c ν μ (g : Profile → E) :=
  (R0_Ms_ae hc ν hμ g).2

/-! ### Causality -/

theorem planeHeat_zero (θ : ℝ) : planeHeat θ (fun _ : ℝ × ℝ => (0 : E)) = fun _ => 0 := by
  funext x
  by_cases hθ : 0 < θ
  · simp only [planeHeat_of_pos hθ, smul_zero, integral_zero]
  · simp only [planeHeat_of_nonpos (not_lt.1 hθ)]

/-- **Causality** (tex lines 3385–3386, "the limit is exactly the causal cylinder heat
inverse"): if two forces `g, g' ∈ H_g` agree at all ages `σ ≤ s₀`, then `R_0(μ)M_s g` and
`R_0(μ)M_s g'` agree at all ages `s ≤ s₀`. -/
theorem R0_Ms_causal (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) {s₀ : ℝ}
    {g g' : HgSpace c E} (h : ∀ᵐ p ∂measureHg c, p.1 ≤ s₀ → g p = g' p) :
    ∀ᵐ p ∂measureH c, p.1 ≤ s₀ →
      (R0 hc ν μ (Ms c E g) : Profile → E) p = (R0 hc ν μ (Ms c E g') : Profile → E) p := by
  set d : HgSpace c E := g - g' with hd_def
  have hd : ∀ᵐ p ∂measureHg c, p.1 ≤ s₀ → (d : Profile → E) p = 0 := by
    filter_upwards [h, Lp.coeFn_sub g g'] with p hp hsub hle
    rw [hsub, Pi.sub_apply, hp hle, sub_self]
  set G : Profile → E := {p : Profile | s₀ < p.1}.indicator (d : Profile → E) with hG_def
  have hGm : StronglyMeasurable G :=
    (Lp.stronglyMeasurable d).indicator (measurableSet_lt measurable_const measurable_fst)
  have hGd : G =ᵐ[measureHg c] d := by
    filter_upwards [hd] with p hp
    by_cases hlt : s₀ < p.1
    · simp only [hG_def, indicator_of_mem (show p ∈ {p : Profile | s₀ < p.1} from hlt)]
    · rw [hG_def, indicator_of_notMem (show p ∉ {p : Profile | s₀ < p.1} from hlt),
        hp (not_lt.1 hlt)]
  have hGd' : G =ᵐ[measureH c] d := by
    rw [← measureHg_withDensity_inv_sq c]
    exact (withDensity_absolutelyContinuous _ _).ae_le hGd
  have hFm : StronglyMeasurable fun p : Profile => p.1 • G p :=
    measurable_fst.stronglyMeasurable.smul hGm
  have hF : (fun p : Profile => p.1 • G p) =ᵐ[measureH c] Ms c E d := by
    filter_upwards [hGd', coeFn_Ms c d] with p hp1 hp2
    rw [hp2, hp1]
  have hR := (R0_ae_eq hc ν hμ (Ms c E d) hFm hF).2
  have hsub : R0 hc ν μ (Ms c E d) = R0 hc ν μ (Ms c E g) - R0 hc ν μ (Ms c E g') := by
    rw [hd_def, map_sub, map_sub]
  filter_upwards [hR, Lp.coeFn_sub (R0 hc ν μ (Ms c E g)) (R0 hc ν μ (Ms c E g')),
    ae_cell_measureH c] with p hp hs hcell hle
  have hzero : (R0 hc ν μ (Ms c E d) : Profile → E) p = 0 := by
    rw [hp]
    have hint : ∀ t ∈ Ioi (0 : ℝ),
        Complex.exp (-(μ * t)) • jointRep c ν (fun p => p.1 • G p) (t, p) = 0 := by
      intro t ht
      have hage : ¬ s₀ < Real.exp (-t) * p.1 := by
        have h1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by simp only [mem_Ioi] at ht; linarith)
        have h2 : 0 < p.1 := hcell.1
        nlinarith
      have hfun : (fun z => periodize c (fun p : Profile => p.1 • G p)
          (Real.exp (-t) * p.1, z)) = fun _ => (0 : E) := by
        funext z
        simp only [periodize, hG_def,
          indicator_of_notMem (show ((Real.exp (-t) * p.1, reduceIoc c z.1, z.2) : Profile) ∉
            {p : Profile | s₀ < p.1} from hage), smul_zero]
      change Complex.exp (-(μ * t)) • planeHeat _
        (fun z => periodize c (fun p : Profile => p.1 • G p) (Real.exp (-t) * p.1, z)) p.2 = 0
      rw [hfun, planeHeat_zero, smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hint, integral_zero]
  rw [hsub] at hzero
  rw [hs, Pi.sub_apply] at hzero
  exact sub_eq_zero.1 hzero

/-! ### The unit -/

/-- **Unit B0225** (tex lines 3379–3392), with the manuscript's hypotheses `c > 0`, `ν > 0`,
`γ = Re μ + 1/4 > 0`, `g ∈ H_g` (`E` a complex separable Banach space of field values):
`R_0(μ) = ∫_0^∞ e^{-μt} T_0(t) dt` is a well-defined bounded operator of norm `≤ γ⁻¹`, and
`R_0(μ)M_s g(s) = ∫_0^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} g(σ) dσ` a.e., the integrand being integrable
on `(0, s)` for a.e. `(s, q, η)`; the result at ages `s ≤ s₀` depends only on `g` at ages
`σ ≤ s₀` (causality). -/
theorem B0225_statement (hc : 0 < c) {ν : ℝ} (hν : 0 < ν) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) :
    (∀ f : HSpace c E, IntegrableOn (fun t : ℝ => Complex.exp (-(μ * t)) • T0 hc ν t f) (Ioi 0) ∧
      R0 hc ν μ f = ∫ t : ℝ in Ioi 0, Complex.exp (-(μ * t)) • T0 hc ν t f) ∧
    ‖(R0 hc ν μ : HSpace c E →L[ℂ] HSpace c E)‖ ≤ (μ.re + 1 / 4)⁻¹ ∧
    (∀ g : HgSpace c E,
      (∀ᵐ p ∂measureH c, IntervalIntegrable (fun σ => ((σ / p.1 : ℝ) : ℂ) ^ μ •
        planeHeat (ν * (p.1 - σ)) (fun z => periodize c (g : Profile → E) (σ, z)) p.2)
        volume 0 p.1) ∧
      (R0 hc ν μ (Ms c E g) : Profile → E) =ᵐ[measureH c] fun p =>
        ∫ σ in (0 : ℝ)..p.1, ((σ / p.1 : ℝ) : ℂ) ^ μ •
          planeHeat (ν * (p.1 - σ)) (fun z => periodize c (g : Profile → E) (σ, z)) p.2) ∧
    (∀ (s₀ : ℝ) (g g' : HgSpace c E), (∀ᵐ p ∂measureHg c, p.1 ≤ s₀ → g p = g' p) →
      ∀ᵐ p ∂measureH c, p.1 ≤ s₀ →
        (R0 hc ν μ (Ms c E g) : Profile → E) p = (R0 hc ν μ (Ms c E g') : Profile → E) p) := by
  have _ := hν
  exact ⟨fun f => ⟨integrableOn_lapT0 hc ν hμ f, R0_apply hc ν hμ f⟩, norm_R0_le hc ν hμ,
    fun g => R0_Ms_ae hc ν hμ g, fun _ _ _ h => R0_Ms_causal hc ν hμ h⟩

end UnforcedLeray.B0225
