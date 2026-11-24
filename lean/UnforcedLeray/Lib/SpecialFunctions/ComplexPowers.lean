import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Complex powers of positive reals and the exact factors `F_±` (INF20 T20.8)

Blueprint target INF20 T20.8 of the scoping note `INF19-INF20-INF29-INF30-Algebra.md`
(§5 Level 3). Every complex power below has a **positive real** base, where Mathlib's principal
`cpow` is `exp(w log x)` with the real logarithm (`ofReal_cpow_eq_cexp`), the "real-log powers"
of the manuscript. Uses:

* tex 3379–3392 (`eq:st18-t00118`, B0225) and 14094–14121 (`eq:st18-t00428`, B0909):
  `(σ/s)^μ` and `|t^μ| = t^{Re μ}` (`ofReal_div_cpow`, `norm_ofReal_cpow`);
* tex 6245–6254 (`eq:st18-t00335`, B0325): the exact factors
  `F₊(s,t) = exp[(λ/ν)(1/(1+νt) - 1/(1+νs))] ((1+νs)/(1+νt))^κ`, `F₋ = conj F₊`,
  `∂_s F₊ = [λ/(1+νs)² + νκ/(1+νs)] F₊`, `F₊(t,t) = 1`, `|F₊/F₋| = 1`;
* tex 12642–12646 (`eq:affine-4-105`, B0642): `F₊(t,0)^{-1} = exp[-λt/(1+νt)] (1+νt)^{-κ}`;
* tex 13011–13032 (`eq:observer:P6-3c`, B0653): `|F₊(t,0)|^{-1} ≤ C e^{-γt/(1+Σ)}` using
  `1 ≤ 1+νt ≤ 1+Σ`;
* tex 794, 10334, 13222–13227 (`eq:m2-gain-band`, B0884): `N_ν = e^{λ/ν} ν^{-κ}`,
  `|N_ν| = e^{Re λ/ν} ν^{-Re κ}`;
* tex 6900–6921 and 7014–7021 (`eq:st18-t00380`–`eq:st18-t00381`, B0376, B0378, B0390): the
  substitution `u = (1-νθ)/(ν²θ)`, `du = -ν^{-2}θ^{-2}dθ`, and the power identity
  `u^{-ζ-5/2} ν^{-2}θ^{-2} = ν^{3+2ζ} θ^{ζ+1/2} (1-νθ)^{-ζ-5/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex

namespace UnforcedLeray.Special

/-! ### Powers of positive reals -/

/-- A complex power of a positive real is the exponential of the real logarithm. -/
theorem ofReal_cpow_eq_cexp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = cexp (w * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

/-- `|t^μ| = t^{Re μ}` for `t > 0` (INF20 T20.8; tex 14094–14121, B0909). -/
theorem norm_ofReal_cpow {t : ℝ} (ht : 0 < t) (μ : ℂ) : ‖(t : ℂ) ^ μ‖ = t ^ μ.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos ht μ

/-- A positive real is the exponential of its logarithm, in `ℂ`. -/
theorem ofReal_eq_cexp_log {x : ℝ} (hx : 0 < x) : (x : ℂ) = cexp (Real.log x) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

/-- `(t/s)^μ = t^μ / s^μ` for `t, s > 0` (INF20 T20.8; tex 3379–3392, B0225; tex 14094–14121,
B0909). -/
theorem ofReal_div_cpow {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (μ : ℂ) :
    ((t / s : ℝ) : ℂ) ^ μ = (t : ℂ) ^ μ / (s : ℂ) ^ μ := by
  rw [ofReal_cpow_eq_cexp (div_pos ht hs), ofReal_cpow_eq_cexp ht, ofReal_cpow_eq_cexp hs,
    Real.log_div ht.ne' hs.ne', ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- `|(t/s)^μ| = (t/s)^{Re μ}` (B0909). -/
theorem norm_ofReal_div_cpow {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (μ : ℂ) :
    ‖((t / s : ℝ) : ℂ) ^ μ‖ = (t / s) ^ μ.re :=
  norm_ofReal_cpow (div_pos ht hs) μ

/-- **The normalisation `N_ν = e^{λ/ν} ν^{-κ}`** (tex 794, 10334) has modulus
`e^{Re λ/ν} ν^{-Re κ}` (INF20 T20.8; tex 13222–13227, `eq:m2-gain-band`, B0884). -/
theorem norm_cexp_div_mul_cpow {lam κ : ℂ} {ν : ℝ} (hν : 0 < ν) :
    ‖cexp (lam / ν) * (ν : ℂ) ^ (-κ)‖ = Real.exp (lam.re / ν) * ν ^ (-κ.re) := by
  rw [norm_mul, Complex.norm_exp, norm_ofReal_cpow hν, Complex.div_ofReal_re, Complex.neg_re]

/-! ### The exact factors `F₊`, `F₋` -/

/-- The exact factor `F₊(s,t)` of tex 6245–6254 (`eq:st18-t00335`, B0325), with the real-log
power of the positive real `(1+νs)/(1+νt)`. -/
def Fplus (lam κ : ℂ) (ν s t : ℝ) : ℂ :=
  cexp (lam / ν * (1 / (1 + ν * t) - 1 / (1 + ν * s))) * (((1 + ν * s) / (1 + ν * t) : ℝ) : ℂ) ^ κ

/-- `F₋ = conj F₊` (tex 6245–6254, B0325). -/
def Fminus (lam κ : ℂ) (ν s t : ℝ) : ℂ := (starRingEnd ℂ) (Fplus lam κ ν s t)

/-- `F₊` as a single exponential (`1 + νs > 0`, `1 + νt > 0`). -/
theorem Fplus_eq_cexp {lam κ : ℂ} {ν s t : ℝ} (hs : 0 < 1 + ν * s) (ht : 0 < 1 + ν * t) :
    Fplus lam κ ν s t = cexp (lam / ν * (((1 + ν * t)⁻¹ - (1 + ν * s)⁻¹ : ℝ) : ℂ) +
      κ * ((Real.log (1 + ν * s) - Real.log (1 + ν * t) : ℝ) : ℂ)) := by
  rw [Fplus, ofReal_cpow_eq_cexp (div_pos hs ht), Real.log_div hs.ne' ht.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `F₊(t,t) = 1` (B0325). -/
theorem Fplus_self {lam κ : ℂ} {ν t : ℝ} (ht : 0 < 1 + ν * t) : Fplus lam κ ν t t = 1 := by
  rw [Fplus, sub_self, mul_zero, Complex.exp_zero, div_self ht.ne', Complex.ofReal_one,
    Complex.one_cpow, one_mul]

/-- `F₊(s,t) ≠ 0` (B0325). -/
theorem Fplus_ne_zero {lam κ : ℂ} {ν s t : ℝ} (hs : 0 < 1 + ν * s) (ht : 0 < 1 + ν * t) :
    Fplus lam κ ν s t ≠ 0 := by
  rw [Fplus_eq_cexp hs ht]
  exact Complex.exp_ne_zero _

/-- `|F₊/F₋| = 1` (INF20 T20.8; tex 6245–6254, B0325: "their ratio has modulus one"). -/
theorem norm_Fplus_div_Fminus {lam κ : ℂ} {ν s t : ℝ} (hs : 0 < 1 + ν * s)
    (ht : 0 < 1 + ν * t) : ‖Fplus lam κ ν s t / Fminus lam κ ν s t‖ = 1 := by
  rw [Fminus, norm_div, Complex.norm_conj, div_self]
  exact norm_ne_zero_iff.2 (Fplus_ne_zero hs ht)

/-- **The `s`-derivative of `F₊`** (INF20 T20.8; tex 6245–6254, B0325):
`∂_s F₊(s,t) = [λ/(1+νs)² + νκ/(1+νs)] F₊(s,t)`, for `ν ≠ 0`, `1 + νs > 0`, `1 + νt > 0`. -/
theorem hasDerivAt_Fplus {lam κ : ℂ} {ν s t : ℝ} (hν : ν ≠ 0) (hs : 0 < 1 + ν * s)
    (ht : 0 < 1 + ν * t) :
    HasDerivAt (fun s : ℝ => Fplus lam κ ν s t)
      ((lam / (1 + ν * s) ^ 2 + ν * κ / (1 + ν * s)) * Fplus lam κ ν s t) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + ν * s) ν s := by
    simpa using ((hasDerivAt_id s).const_mul ν).const_add 1
  have hr₁ : HasDerivAt (fun s : ℝ => (1 + ν * t)⁻¹ - (1 + ν * s)⁻¹) (ν / (1 + ν * s) ^ 2) s := by
    have h2 := (hasDerivAt_const s ((1 + ν * t)⁻¹)).sub (h1.inv hs.ne')
    exact h2.congr_deriv (by ring)
  have hr₂ : HasDerivAt (fun s : ℝ => Real.log (1 + ν * s) - Real.log (1 + ν * t))
      (ν / (1 + ν * s)) s :=
    (h1.log hs.ne').sub_const _
  have hphase := ((hr₁.ofReal_comp).const_mul (lam / (ν : ℂ))).add
    ((hr₂.ofReal_comp).const_mul κ)
  have hexp := hphase.cexp
  have hev : ∀ᶠ s' in 𝓝 s, 0 < 1 + ν * s' :=
    ((by fun_prop : Continuous fun s' : ℝ => 1 + ν * s').tendsto s).eventually (lt_mem_nhds hs)
  have heq : (fun s : ℝ => Fplus lam κ ν s t) =ᶠ[𝓝 s] (fun s : ℝ =>
      cexp (lam / ν * (((1 + ν * t)⁻¹ - (1 + ν * s)⁻¹ : ℝ) : ℂ) +
        κ * ((Real.log (1 + ν * s) - Real.log (1 + ν * t) : ℝ) : ℂ))) := by
    filter_upwards [hev] with s' hs'
    exact Fplus_eq_cexp hs' ht
  refine (hexp.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [Fplus_eq_cexp hs ht, mul_comm]
  congr 1
  have hν' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hν
  have hs' : (1 + (ν : ℂ) * s) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

/-- `F₊(t,0) = exp[λt/(1+νt)] (1+νt)^κ` (tex 12642–12646, B0642). -/
theorem Fplus_zero_eq {lam κ : ℂ} {ν t : ℝ} (hν : ν ≠ 0) (ht : 0 < 1 + ν * t) :
    Fplus lam κ ν t 0 = cexp (lam * t / (1 + ν * t)) * ((1 + ν * t : ℝ) : ℂ) ^ κ := by
  have hν' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hν
  have ht' : (1 + (ν : ℂ) * t) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Fplus]
  congr 1
  · congr 1
    push_cast
    field_simp
    ring
  · congr 2
    simp

/-- **The exact diagonal ratio** (INF20 T20.8; tex 12642–12646, `eq:affine-4-105`, B0642):
`F₊(t,0)^{-1} = exp[-λt/(1+νt)] (1+νt)^{-κ}`. -/
theorem Fplus_zero_inv {lam κ : ℂ} {ν t : ℝ} (hν : ν ≠ 0) (ht : 0 < 1 + ν * t) :
    (Fplus lam κ ν t 0)⁻¹ = cexp (-(lam * t / (1 + ν * t))) * ((1 + ν * t : ℝ) : ℂ) ^ (-κ) := by
  rw [Fplus_zero_eq hν ht, mul_inv, ← Complex.exp_neg, Complex.cpow_neg]

/-- `|F₊(t,0)|^{-1} = exp[-Re λ t/(1+νt)] (1+νt)^{-Re κ}` (B0642, B0653). -/
theorem norm_Fplus_zero_inv {lam κ : ℂ} {ν t : ℝ} (hν : ν ≠ 0) (ht : 0 < 1 + ν * t) :
    ‖(Fplus lam κ ν t 0)⁻¹‖ =
      Real.exp (-(lam.re * t / (1 + ν * t))) * (1 + ν * t) ^ (-κ.re) := by
  rw [Fplus_zero_inv hν ht, norm_mul, Complex.norm_exp, norm_ofReal_cpow ht, Complex.neg_re,
    Complex.neg_re]
  congr 2
  have : ((1 : ℂ) + (ν : ℂ) * t) = ((1 + ν * t : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.div_ofReal_re, Complex.re_mul_ofReal]

/-- **The observer bound** (INF20 T20.8; tex 13011–13032, `eq:observer:P6-3c`, B0653): for
`ν > 0`, `t ≥ 0`, `νt ≤ S` (the manuscript's `Σ`) and `Re λ ≥ 0`,
`|F₊(t,0)|^{-1} ≤ e^{-Re λ · t/(1+S)} max(1, (1+S)^{-Re κ})`, a bound independent of `ν`. -/
theorem norm_Fplus_zero_inv_le {lam κ : ℂ} {ν t S : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    (hS : ν * t ≤ S) (hlam : 0 ≤ lam.re) :
    ‖(Fplus lam κ ν t 0)⁻¹‖ ≤
      Real.exp (-(lam.re * t / (1 + S))) * max 1 ((1 + S) ^ (-κ.re)) := by
  have hνt : 0 ≤ ν * t := mul_nonneg hν.le ht
  have hpos : 0 < 1 + ν * t := by linarith
  rw [norm_Fplus_zero_inv hν.ne' hpos]
  have hexp : Real.exp (-(lam.re * t / (1 + ν * t))) ≤ Real.exp (-(lam.re * t / (1 + S))) := by
    apply Real.exp_le_exp.2
    have : lam.re * t / (1 + S) ≤ lam.re * t / (1 + ν * t) :=
      div_le_div_of_nonneg_left (mul_nonneg hlam ht) hpos (by linarith)
    linarith
  have hpow : (1 + ν * t) ^ (-κ.re) ≤ max 1 ((1 + S) ^ (-κ.re)) := by
    rcases le_total 0 (-κ.re) with hk | hk
    · exact (Real.rpow_le_rpow hpos.le (by linarith) hk).trans (le_max_right _ _)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hk).trans (le_max_left _ _)
  exact mul_le_mul hexp hpow (Real.rpow_nonneg hpos.le _) (Real.exp_pos _).le

/-! ### The turnover substitution `u = (1 - νθ)/(ν²θ)` -/

/-- The power identity of the turnover substitution (INF20 T20.8; tex 6900–6921,
`eq:st18-t00380`–`eq:st18-t00381`, B0376, B0378, B0390): for `ν > 0`, `0 < θ < 1/ν` and complex
`ζ`, with `u = (1-νθ)/(ν²θ)`,
`u^{-ζ-5/2} · ν^{-2}θ^{-2} = ν^{3+2ζ} θ^{ζ+1/2} (1-νθ)^{-ζ-5/2}`. -/
theorem turnover_cpow_identity {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) (hθν : ν * θ < 1) (ζ : ℂ) :
    (((1 - ν * θ) / (ν ^ 2 * θ) : ℝ) : ℂ) ^ (-ζ - 5 / 2) * ((1 / (ν ^ 2 * θ ^ 2) : ℝ) : ℂ) =
      (ν : ℂ) ^ (3 + 2 * ζ) * (θ : ℂ) ^ (ζ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-ζ - 5 / 2) := by
  have h1 : 0 < 1 - ν * θ := by linarith
  have hν2θ : 0 < ν ^ 2 * θ := by positivity
  have hν2θ2 : 0 < 1 / (ν ^ 2 * θ ^ 2) := by positivity
  rw [ofReal_cpow_eq_cexp (div_pos h1 hν2θ), ofReal_eq_cexp_log hν2θ2, ofReal_cpow_eq_cexp hν,
    ofReal_cpow_eq_cexp hθ, ofReal_cpow_eq_cexp h1, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  rw [Real.log_div h1.ne' hν2θ.ne', Real.log_mul (by positivity) hθ.ne', Real.log_pow,
    one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- The turnover map `θ ↦ (1-νθ)/(ν²θ)` sends `(0, θ_o)` onto `(u_o, ∞)`, where
`θ_o = 1/(ν + ν² u_o)` (tex 6896–6898, `eq:st18-t00378`). -/
theorem image_turnover {ν u₀ : ℝ} (hν : 0 < ν) (hu₀ : 0 ≤ u₀) :
    (fun θ : ℝ => (1 - ν * θ) / (ν ^ 2 * θ)) '' Ioo 0 (1 / (ν + ν ^ 2 * u₀)) = Ioi u₀ := by
  have hD : 0 < ν + ν ^ 2 * u₀ := by positivity
  ext u
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    show u₀ < (1 - ν * θ) / (ν ^ 2 * θ)
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ hD] at hθ1
    nlinarith
  · intro hu
    have hu' : u₀ < u := hu
    have hD' : 0 < ν + ν ^ 2 * u := by
      have : 0 < u := lt_of_le_of_lt hu₀ hu'
      positivity
    refine ⟨1 / (ν + ν ^ 2 * u), ⟨by positivity, ?_⟩, ?_⟩
    · apply one_div_lt_one_div_of_lt hD
      have : ν ^ 2 * u₀ < ν ^ 2 * u := mul_lt_mul_of_pos_left hu' (by positivity)
      linarith
    · show (1 - ν * (1 / (ν + ν ^ 2 * u))) / (ν ^ 2 * (1 / (ν + ν ^ 2 * u))) = u
      have h1u : 0 < 1 + ν * u := by
        have : 0 < u := lt_of_le_of_lt hu₀ hu'
        positivity
      have hsplit : ν + ν ^ 2 * u = ν * (1 + ν * u) := by ring
      rw [hsplit]
      field_simp
      ring

/-- **The turnover change of variables** (INF20 T20.8; tex 6900–6921, `eq:st18-t00380`, B0376,
B0378, B0390): for `ν > 0`, `u₀ ≥ 0`, `θ_o = 1/(ν + ν²u₀)` and any `g`,
`∫_{u₀}^∞ g(u) du = ∫_0^{θ_o} ν^{-2}θ^{-2} g((1-νθ)/(ν²θ)) dθ` (Bochner integrals; the two
integrands are integrable together, by the change of variables). -/
theorem integral_Ioi_eq_integral_turnover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν u₀ : ℝ} (hν : 0 < ν) (hu₀ : 0 ≤ u₀) (g : ℝ → E) :
    ∫ u in Ioi u₀, g u =
      ∫ θ in Ioo 0 (1 / (ν + ν ^ 2 * u₀)), (1 / (ν ^ 2 * θ ^ 2)) • g ((1 - ν * θ) / (ν ^ 2 * θ)) := by
  set f : ℝ → ℝ := fun θ => (1 - ν * θ) / (ν ^ 2 * θ) with hf
  set f' : ℝ → ℝ := fun θ => -(1 / (ν ^ 2 * θ ^ 2)) with hf'
  have hderiv : ∀ θ ∈ Ioo 0 (1 / (ν + ν ^ 2 * u₀)),
      HasDerivWithinAt f (f' θ) (Ioo 0 (1 / (ν + ν ^ 2 * u₀))) θ := by
    intro θ hθ
    have hθ0 : θ ≠ 0 := hθ.1.ne'
    have hν0 : ν ≠ 0 := hν.ne'
    have hd : HasDerivAt (fun θ : ℝ => (ν ^ 2)⁻¹ * θ⁻¹ - ν⁻¹) (-(1 / (ν ^ 2 * θ ^ 2))) θ := by
      have := ((hasDerivAt_inv hθ0).const_mul ((ν ^ 2)⁻¹)).sub_const (ν⁻¹)
      exact this.congr_deriv (by rw [one_div, mul_inv]; ring)
    have heq : (fun θ : ℝ => (ν ^ 2)⁻¹ * θ⁻¹ - ν⁻¹) =ᶠ[𝓝 θ] f := by
      filter_upwards [eventually_ne_nhds hθ0] with x hx
      simp only [hf]
      field_simp
    exact (hd.congr_of_eventuallyEq heq.symm).hasDerivWithinAt
  have hinj : InjOn f (Ioo 0 (1 / (ν + ν ^ 2 * u₀))) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := hx.1.ne'
    have hy0 : y ≠ 0 := hy.1.ne'
    simp only [hf] at hxy
    rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
    have hν2 : ν ^ 2 ≠ 0 := by positivity
    have : ν ^ 2 * (y - x) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hν2
    · linarith
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [image_turnover hν hu₀] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  simp only [hf', abs_neg]
  rw [abs_of_pos (by have := hθ.1; positivity)]

/-- **The turnover substitution with complex powers** (INF20 T20.8; tex 6900–6921,
`eq:st18-t00381`, B0376, B0378; tex 7014–7021, B0390): for `ν > 0`, `u₀ ≥ 0`,
`θ_o = 1/(ν + ν²u₀)`, complex `ζ` and any `h`,
`∫_{u₀}^∞ u^{-ζ-5/2} h(u) du = ν^{3+2ζ} ∫_0^{θ_o} θ^{ζ+1/2} (1-νθ)^{-ζ-5/2} h((1-νθ)/(ν²θ)) dθ`
(Bochner integrals; the integrands are integrable together, by the change of variables). -/
theorem integral_Ioi_cpow_turnover {ν u₀ : ℝ} (hν : 0 < ν) (hu₀ : 0 ≤ u₀) (ζ : ℂ)
    (h : ℝ → ℂ) :
    ∫ u in Ioi u₀, (u : ℂ) ^ (-ζ - 5 / 2) * h u =
      (ν : ℂ) ^ (3 + 2 * ζ) * ∫ θ : ℝ in Ioo 0 (1 / (ν + ν ^ 2 * u₀)),
        (θ : ℂ) ^ (ζ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-ζ - 5 / 2) *
          h ((1 - ν * θ) / (ν ^ 2 * θ)) := by
  rw [integral_Ioi_eq_integral_turnover hν hu₀, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hθ0 : 0 < θ := hθ.1
  have hD : 0 < ν + ν ^ 2 * u₀ := by positivity
  have hθ1 : θ * (ν + ν ^ 2 * u₀) < 1 := by
    have := hθ.2
    rwa [lt_div_iff₀ hD] at this
  have hνθ : ν * θ < 1 := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ν) hu₀) hθ0.le]
  have key := turnover_cpow_identity hν hθ0 hνθ ζ
  simp only [Complex.real_smul]
  calc ((1 / (ν ^ 2 * θ ^ 2) : ℝ) : ℂ) *
        ((((1 - ν * θ) / (ν ^ 2 * θ) : ℝ) : ℂ) ^ (-ζ - 5 / 2) * h ((1 - ν * θ) / (ν ^ 2 * θ)))
      = ((((1 - ν * θ) / (ν ^ 2 * θ) : ℝ) : ℂ) ^ (-ζ - 5 / 2) *
          ((1 / (ν ^ 2 * θ ^ 2) : ℝ) : ℂ)) * h ((1 - ν * θ) / (ν ^ 2 * θ)) := by ring
    _ = _ := by rw [key]; ring

end UnforcedLeray.Special
