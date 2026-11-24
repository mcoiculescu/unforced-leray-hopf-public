import UnforcedLeray.Units.B0123.Multiplier
import UnforcedLeray.Units.B0121.Spectral
import UnforcedLeray.Lib.Semigroups.Multiplication

/-!
# B0123 (`eq:st18-t00101`): one-derivative smoothing of `e^{aD}`

Blueprint unit B0123, label `eq:st18-t00101`, `paper/main.tex` lines 1873--1878 (proof of
finite-order regularity, Section `sec:st18-2021`). Dependency: B0094 (`eq:st18-t00068`,
`Units/B0094.lean`: `D` is selfadjoint and `≤ 0` on `X_G`, with orthonormal eigenbasis `oscBasis`,
`D (oscBasis ℓ) = -ℓ · oscBasis ℓ`, and `D = diagOp oscBasis`). Infrastructure INF31 (spectral
calculus of `D`, or the diagonal model).

## The manuscript's claim (tex lines 1873--1878)

"Spectral calculus for `D ≤ 0` gives
`‖e^{aD}‖_{X_{G,j} → X_{G,j+1}} ≤ C_j a^{-1/2}`, `0 < a ≤ 1`",
where (tex line 748, `eq:st18-t00014`) `X_{G,j} = 𝒟((I - D)^{j/2})` with its graph norm
(tex line 1858: "the squared graph norm on `X_{G,j}`").

## What is formalized

* **Spectral calculus of `D`** (`specCalc φ`, for `φ : ℝ → ℂ`): since `D` has the orthonormal
  eigenbasis `oscBasis` with eigenvalues `-ℓ` (B0094), `φ(D) f = ∑_ℓ φ(-ℓ) ⟪oscBasis ℓ, f⟫ oscBasis ℓ`
  on its maximal domain `{f : ∑_ℓ |φ(-ℓ)|² |⟪oscBasis ℓ, f⟫|² < ∞}`. Sanity checks:
  `specCalc_id` (`φ(x) = x` gives back `D` itself, domain included) and `specCalc_eigen`
  (`φ(D) f = φ(μ) f` on every eigenvector `D f = μ f`).
* **`(I - D)^s`** (`IDpow s`, the calculus of `(1 - x)^s`, `IDpow_eq_specCalc`; on the spectrum
  `1 - x ≥ 1 > 0`, so no `rpow` junk): `IDpow_one_domain`, `IDpow_one_apply`
  (`(I - D)^1 = I - D`, domain included) and the composition law `IDpow_mem_domain_iff`,
  `IDpow_comp_apply` (`(I - D)^s (I - D)^t = (I - D)^{s+t}`).
* **`X_{G,j}`** (`XGj j := 𝒟((I - D)^{j/2})`, tex line 748) with the graph norm
  `xgjNorm j f = (‖f‖² + ‖(I - D)^{j/2} f‖²)^{1/2}`; `mem_XGj_iff`
  (`∑ (1 + ℓ)^j |f_ℓ|² < ∞`), `hasSum_xgjNorm_sq`, `XGj_zero` (`X_{G,0} = X_G`), `XGj_two`
  (`X_{G,2} = 𝒟(D)`), `XGj_succ_le`.
* **`e^{aD}`** (`expD a`, bounded, for `a ≥ 0`): `expD_eq_specCalc` (it is the calculus of
  `e^{ax}`), `expD_eigen` (`e^{aD} f = e^{aμ} f` for `D f = μ f`), `eq_expD_of_eigen` (it is the
  **unique** bounded operator with this property, so the definition is intrinsic to `D`),
  `expD_zero`, `expD_add` (semigroup law), `norm_expD_le` (contraction, from `D ≤ 0`).
* **The claim**: `expD_smoothing` (with the explicit constant `C_j = 1` for the graph norms) and
  `eq_st18_t00101` (the manuscript's form: for each `j` there is `C_j`).

## Conventions and deviations

* `expD a` is defined for every real `a` through `e^{-max(a,0) ℓ}`; for `a < 0` (never used,
  `e^{aD}` is unbounded there) this is a junk value. All statements assume `0 ≤ a` or `0 < a`.
* The operator-norm bound `‖e^{aD}‖_{X_{G,j} → X_{G,j+1}} ≤ C_j a^{-1/2}` is stated in its
  meaning: `e^{aD}` maps `X_{G,j}` into `X_{G,j+1}` and
  `‖e^{aD} f‖_{X_{G,j+1}} ≤ C_j a^{-1/2} ‖f‖_{X_{G,j}}` for all `f ∈ X_{G,j}`.
* The scalar inequality behind the proof (`smoothing_scalar`,
  `(1 + ℓ) e^{-2aℓ} ≤ a^{-1}` for `0 < a ≤ 1`) is the square of
  `UnforcedLeray.Infra.Mult.sqrt_one_add_mul_exp_neg_le`

  `(1 + ℓ)^{1/2} e^{-aℓ} ≤ a^{-1/2}`), which is reused.

## Agreement with B0121

The sibling unit B0121 (`eq:st18-t00100`, `Units/B0121/Spectral.lean`) also builds
`X_{G,j} = 𝒟((I - D)^{j/2})` from B0094, as `B0121.XGj`, `B0121.fracPow` and the squared graph
norm `B0121.graphNormSq`. The last section proves that the two constructions coincide
(`XGj_eq_B0121`, `IDpow_half_eq_fracPow`, `xgjNorm_sq_eq_graphNormSq`) and restates the claim in
B0121's terms (`eq_st18_t00101_graphNormSq`), so later units can use either.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal

namespace UnforcedLeray.B0123

open UnforcedLeray.B0010 UnforcedLeray.B0094

/-! ## Coefficients of `D` (B0094) -/

/-- The coefficients of `D f` in the eigenbasis: `⟪oscBasis ℓ, D f⟫ = -ℓ ⟪oscBasis ℓ, f⟫`
(B0094, tex lines 1506--1510). -/
theorem inner_D (f : D.domain) (n : ℕ) :
    ⟪oscBasis n, D f⟫_ℂ = -(n : ℂ) * ⟪oscBasis n, (f : XG)⟫_ℂ := by
  have h : ∀ T : XG →ₗ.[ℂ] XG, T = diagOp oscBasis → ∀ f : T.domain,
      ⟪oscBasis n, T f⟫_ℂ = -(n : ℂ) * ⟪oscBasis n, (f : XG)⟫_ℂ := by
    rintro T rfl f
    exact inner_diagOp oscBasis f n
  exact h D D_eq_diagOp f

theorem mem_D_domain_iff_memℓp (f : XG) :
    f ∈ D.domain ↔ Memℓp (fun n : ℕ => (n : ℂ) * ⟪oscBasis n, f⟫_ℂ) 2 := by
  rw [D_eq_diagOp]
  exact mem_diagOp_domain_iff oscBasis f

theorem memℓp_coeff (f : XG) : Memℓp (fun n : ℕ => ⟪oscBasis n, f⟫_ℂ) 2 := by
  have h : ⇑(oscBasis.repr f) = fun n : ℕ => ⟪oscBasis n, f⟫_ℂ :=
    funext fun n => oscBasis.repr_apply_apply f n
  rw [← h]
  exact lp.memℓp _

/-! ## Spectral calculus of `D` (INF31) -/

/-- **Spectral calculus of `D`** (tex line 1873, INF31): for `φ : ℝ → ℂ`,
`φ(D) f = ∑_ℓ φ(-ℓ) ⟪oscBasis ℓ, f⟫ oscBasis ℓ` on the maximal domain
`∑_ℓ |φ(-ℓ)|² |⟪oscBasis ℓ, f⟫|² < ∞`; `D` has the orthonormal eigenbasis `oscBasis` with
eigenvalues `-ℓ` (B0094). -/
def specCalc (φ : ℝ → ℂ) : XG →ₗ.[ℂ] XG := mulOp oscBasis fun n : ℕ => φ (-(n : ℝ))

theorem mem_specCalc_domain_iff (φ : ℝ → ℂ) (f : XG) :
    f ∈ (specCalc φ).domain ↔
      Summable fun n : ℕ => ‖φ (-(n : ℝ))‖ ^ 2 * ‖⟪oscBasis n, f⟫_ℂ‖ ^ 2 :=
  mem_mulOp_domain_iff_summable oscBasis _ f

theorem inner_specCalc (φ : ℝ → ℂ) (f : (specCalc φ).domain) (n : ℕ) :
    ⟪oscBasis n, specCalc φ f⟫_ℂ = φ (-(n : ℝ)) * ⟪oscBasis n, (f : XG)⟫_ℂ :=
  inner_mulOp oscBasis _ f n

theorem specCalc_graph_iff (φ : ℝ → ℂ) (x y : XG) :
    (∃ hx : x ∈ (specCalc φ).domain, specCalc φ ⟨x, hx⟩ = y) ↔
      ∀ n : ℕ, ⟪oscBasis n, y⟫_ℂ = φ (-(n : ℝ)) * ⟪oscBasis n, x⟫_ℂ :=
  mulOp_graph_iff oscBasis _ x y

/-- **Consistency of the calculus**: the identity function gives back `D` (domain included). -/
theorem specCalc_id : specCalc (fun x : ℝ => (x : ℂ)) = D := by
  have hdom : (specCalc fun x : ℝ => (x : ℂ)).domain = D.domain := by
    ext f
    rw [mem_D_domain_iff_memℓp]
    change Memℓp (fun n : ℕ => (((-(n : ℝ)) : ℝ) : ℂ) * ⟪oscBasis n, f⟫_ℂ) 2 ↔ _
    have hfun : (fun n : ℕ => (((-(n : ℝ)) : ℝ) : ℂ) * ⟪oscBasis n, f⟫_ℂ) =
        -(fun n : ℕ => (n : ℂ) * ⟪oscBasis n, f⟫_ℂ) := by
      funext n
      simp only [Complex.ofReal_neg, Complex.ofReal_natCast, Pi.neg_apply, neg_mul]
    rw [hfun]
    exact ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
  refine LinearPMap.ext hdom fun x hx hy => ?_
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_specCalc, inner_D]
  push_cast
  ring

/-- **The calculus on eigenvectors**: if `D f = μ f` then `f ∈ 𝒟(φ(D))` and `φ(D) f = φ(μ) f`
(eigenvalues of the selfadjoint `D` are real, B0094). -/
theorem specCalc_eigen (φ : ℝ → ℂ) (f : D.domain) (μ : ℝ) (hf : D f = (μ : ℂ) • (f : XG)) :
    ∃ h : (f : XG) ∈ (specCalc φ).domain, specCalc φ ⟨f, h⟩ = φ μ • (f : XG) := by
  rw [specCalc_graph_iff]
  intro n
  have hn : -(n : ℂ) * ⟪oscBasis n, (f : XG)⟫_ℂ = (μ : ℂ) * ⟪oscBasis n, (f : XG)⟫_ℂ := by
    rw [← inner_D, hf, inner_smul_right]
  rw [inner_smul_right]
  by_cases hc : ⟪oscBasis n, (f : XG)⟫_ℂ = 0
  · rw [hc, mul_zero, mul_zero]
  · have hμ : (μ : ℂ) = -(n : ℂ) := (mul_right_cancel₀ hc hn).symm
    have hμ' : μ = -(n : ℝ) := by exact_mod_cast hμ
    rw [hμ']

/-! ## The fractional powers `(I - D)^s` and the spaces `X_{G,j}` -/

/-- The multiplier `(1 + ℓ)^s` of `(I - D)^s` on the `ℓ`-th eigenvector. -/
def idMult (s : ℝ) (n : ℕ) : ℂ := (((1 + (n : ℝ)) ^ s : ℝ) : ℂ)

/-- **`(I - D)^s`** (tex line 748), on the maximal domain `∑ (1 + ℓ)^{2s} |f_ℓ|² < ∞`. -/
def IDpow (s : ℝ) : XG →ₗ.[ℂ] XG := mulOp oscBasis (idMult s)

/-- `(I - D)^s` is the spectral calculus of `(1 - x)^s` (`1 - x ≥ 1` on the spectrum). -/
theorem IDpow_eq_specCalc (s : ℝ) :
    IDpow s = specCalc fun x : ℝ => (((1 - x) ^ s : ℝ) : ℂ) := by
  unfold IDpow specCalc
  congr 1
  funext n
  simp only [idMult, sub_neg_eq_add]

theorem inner_IDpow (s : ℝ) (f : (IDpow s).domain) (n : ℕ) :
    ⟪oscBasis n, IDpow s f⟫_ℂ = idMult s n * ⟪oscBasis n, (f : XG)⟫_ℂ :=
  inner_mulOp oscBasis (idMult s) f n

theorem norm_idMult (s : ℝ) (n : ℕ) : ‖idMult s n‖ = (1 + (n : ℝ)) ^ s := by
  rw [idMult, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) s)]

theorem hasSum_norm_IDpow_sq (s : ℝ) (f : (IDpow s).domain) :
    HasSum (fun n : ℕ => ((1 + (n : ℝ)) ^ s) ^ 2 * ‖⟪oscBasis n, (f : XG)⟫_ℂ‖ ^ 2)
      (‖IDpow s f‖ ^ 2) := by
  have h := hasSum_norm_mulOp_sq oscBasis (idMult s) f
  simp only [norm_idMult] at h
  exact h

theorem one_add_rpow_half_sq (j n : ℕ) :
    ((1 + (n : ℝ)) ^ ((j : ℝ) / 2)) ^ 2 = (1 + (n : ℝ)) ^ j := by
  rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast (1 + (n : ℝ)) j]
  congr 1
  push_cast
  ring

theorem idMult_mul (s t : ℝ) : idMult s * idMult t = idMult (s + t) := by
  funext n
  simp only [Pi.mul_apply, idMult]
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]

/-- `(I - D)^s (I - D)^t = (I - D)^{s+t}`, domains. -/
theorem IDpow_mem_domain_iff (s t : ℝ) (f : (IDpow t).domain) :
    IDpow t f ∈ (IDpow s).domain ↔ (f : XG) ∈ (IDpow (s + t)).domain := by
  have h := mulOp_mem_domain_iff oscBasis (idMult s) (idMult t) f
  rw [idMult_mul] at h
  exact h

/-- `(I - D)^s (I - D)^t = (I - D)^{s+t}`, values. -/
theorem IDpow_comp_apply (s t : ℝ) (f : (IDpow t).domain) (h₁ : IDpow t f ∈ (IDpow s).domain)
    (h : (f : XG) ∈ (IDpow (s + t)).domain) :
    IDpow s ⟨IDpow t f, h₁⟩ = IDpow (s + t) ⟨f, h⟩ := by
  apply ext_inner_basis oscBasis
  intro n
  simp only [inner_IDpow]
  rw [← idMult_mul, Pi.mul_apply, mul_assoc]

/-- `𝒟((I - D)^1) = 𝒟(D)`. -/
theorem IDpow_one_domain : (IDpow 1).domain = D.domain := by
  ext f
  have hfun : (fun n : ℕ => idMult 1 n * ⟪oscBasis n, f⟫_ℂ) =
      (fun n : ℕ => ⟪oscBasis n, f⟫_ℂ) + fun n : ℕ => (n : ℂ) * ⟪oscBasis n, f⟫_ℂ := by
    funext n
    rw [idMult, Real.rpow_one, Pi.add_apply]
    push_cast
    ring
  rw [mem_D_domain_iff_memℓp]
  change Memℓp (fun n : ℕ => idMult 1 n * ⟪oscBasis n, f⟫_ℂ) 2 ↔ _
  rw [hfun]
  constructor
  · intro h
    simpa only [add_sub_cancel_left] using h.sub (memℓp_coeff f)
  · intro h
    exact (memℓp_coeff f).add h

/-- `(I - D)^1 f = f - D f`. -/
theorem IDpow_one_apply (f : (IDpow 1).domain) (hf : (f : XG) ∈ D.domain) :
    IDpow 1 f = (f : XG) - D ⟨f, hf⟩ := by
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_IDpow, inner_sub_right, inner_D, idMult, Real.rpow_one]
  push_cast
  ring

/-- **The space `X_{G,j} = 𝒟((I - D)^{j/2})`** (tex line 748, `eq:st18-t00014`). -/
abbrev XGj (j : ℕ) : Submodule ℂ XG := (IDpow ((j : ℝ) / 2)).domain

/-- **The graph norm of `X_{G,j}`** (tex line 1858):
`‖f‖_{X_{G,j}} = (‖f‖² + ‖(I - D)^{j/2} f‖²)^{1/2}`. -/
def xgjNorm (j : ℕ) (f : XGj j) : ℝ :=
  Real.sqrt (‖(f : XG)‖ ^ 2 + ‖IDpow ((j : ℝ) / 2) f‖ ^ 2)

theorem xgjNorm_nonneg (j : ℕ) (f : XGj j) : 0 ≤ xgjNorm j f := Real.sqrt_nonneg _

/-- `f ∈ X_{G,j}` iff `∑_ℓ (1 + ℓ)^j |⟪oscBasis ℓ, f⟫|² < ∞`. -/
theorem mem_XGj_iff (j : ℕ) (f : XG) :
    f ∈ XGj j ↔ Summable fun n : ℕ => (1 + (n : ℝ)) ^ j * ‖⟪oscBasis n, f⟫_ℂ‖ ^ 2 := by
  show f ∈ (IDpow ((j : ℝ) / 2)).domain ↔ _
  rw [IDpow, mem_mulOp_domain_iff_summable]
  simp only [norm_idMult, one_add_rpow_half_sq]

/-- `‖f‖²_{X_{G,j}} = ∑_ℓ (1 + (1 + ℓ)^j) |⟪oscBasis ℓ, f⟫|²`. -/
theorem hasSum_xgjNorm_sq (j : ℕ) (f : XGj j) :
    HasSum (fun n : ℕ => (1 + (1 + (n : ℝ)) ^ j) * ‖⟪oscBasis n, (f : XG)⟫_ℂ‖ ^ 2)
      (xgjNorm j f ^ 2) := by
  rw [xgjNorm, Real.sq_sqrt (by positivity)]
  have h := (hasSum_norm_inner_sq oscBasis (f : XG)).add (hasSum_norm_IDpow_sq ((j : ℝ) / 2) f)
  simp only [one_add_rpow_half_sq] at h
  convert h using 1
  funext n
  ring

/-- `X_{G,0} = X_G`. -/
theorem XGj_zero : XGj 0 = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [mem_XGj_iff]
  simpa only [pow_zero, one_mul] using (hasSum_norm_inner_sq oscBasis f).summable

/-- `X_{G,2} = 𝒟(D)`. -/
theorem XGj_two : XGj 2 = D.domain := by
  show (IDpow (((2 : ℕ) : ℝ) / 2)).domain = D.domain
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num]
  exact IDpow_one_domain

/-- `X_{G,j+1} ⊆ X_{G,j}`. -/
theorem XGj_succ_le (j : ℕ) : XGj (j + 1) ≤ XGj j := by
  intro f hf
  rw [mem_XGj_iff] at hf ⊢
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hf
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (Nat.le_succ j))
    (by positivity)

/-! ## The semigroup `e^{aD}` -/

/-- The multiplier `e^{-aℓ}` of `e^{aD}` on the `ℓ`-th eigenvector (`a ≥ 0`; `max a 0` makes it
bounded for every real `a`, a junk value for `a < 0`). -/
def expMult (a : ℝ) (n : ℕ) : ℂ := ((Real.exp (-(max a 0 * n)) : ℝ) : ℂ)

theorem norm_expMult_le (a : ℝ) (n : ℕ) : ‖expMult a n‖ ≤ 1 := by
  rw [expMult, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have : 0 ≤ max a 0 * (n : ℝ) := mul_nonneg (le_max_right a 0) n.cast_nonneg
  linarith

/-- **`e^{aD}`** (tex line 1875), `a ≥ 0`: the bounded operator `diag(e^{-aℓ})` in the eigenbasis
of `D`. -/
def expD (a : ℝ) : XG →L[ℂ] XG := diagCLM oscBasis (expMult a) 1 (norm_expMult_le a)

theorem inner_expD (a : ℝ) (f : XG) (n : ℕ) :
    ⟪oscBasis n, expD a f⟫_ℂ = expMult a n * ⟪oscBasis n, f⟫_ℂ :=
  inner_diagCLM oscBasis _ _ _ f n

theorem expMult_of_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    expMult a n = Complex.exp ((a : ℂ) * ((-(n : ℝ) : ℝ) : ℂ)) := by
  rw [expMult, max_eq_left ha, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `e^{aD}` is the spectral calculus of `x ↦ e^{ax}` (`a ≥ 0`). -/
theorem expD_eq_specCalc {a : ℝ} (ha : 0 ≤ a) (f : XG) :
    ∃ h : f ∈ (specCalc fun x : ℝ => Complex.exp ((a : ℂ) * x)).domain,
      specCalc (fun x : ℝ => Complex.exp ((a : ℂ) * x)) ⟨f, h⟩ = expD a f := by
  rw [specCalc_graph_iff]
  intro n
  rw [inner_expD, expMult_of_nonneg ha]

/-- `e^{aD} f = e^{aμ} f` on every eigenvector `D f = μ f` (`a ≥ 0`). -/
theorem expD_eigen {a : ℝ} (ha : 0 ≤ a) (f : D.domain) (μ : ℝ)
    (hf : D f = (μ : ℂ) • (f : XG)) :
    expD a f = Complex.exp ((a : ℂ) * μ) • (f : XG) := by
  obtain ⟨_, e1⟩ := specCalc_eigen (fun x : ℝ => Complex.exp ((a : ℂ) * x)) f μ hf
  obtain ⟨_, e2⟩ := expD_eq_specCalc ha (f : XG)
  rw [← e2]
  exact e1

/-- **Uniqueness**: `e^{aD}` is the only bounded operator acting as `e^{aμ}` on every eigenvector
`D f = μ f` of `D`. So `expD` is determined by `D` alone. -/
theorem eq_expD_of_eigen {a : ℝ} (ha : 0 ≤ a) (T : XG →L[ℂ] XG)
    (hT : ∀ (f : D.domain) (μ : ℝ), D f = (μ : ℂ) • (f : XG) →
      T f = Complex.exp ((a : ℂ) * μ) • (f : XG)) :
    T = expD a := by
  have hd : Dense (Submodule.span ℂ (Set.range oscBasis) : Set XG) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 oscBasis.dense_span
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨n, rfl⟩
  obtain ⟨hn, hD⟩ := D_oscBasis n
  have hD' : D ⟨oscBasis n, hn⟩ = (((-(n : ℝ)) : ℝ) : ℂ) • oscBasis n := by
    rw [hD, Complex.ofReal_neg, Complex.ofReal_natCast]
  exact (hT ⟨_, hn⟩ _ hD').trans (expD_eigen ha ⟨_, hn⟩ _ hD').symm

/-- `e^{0 D} = I`. -/
theorem expD_zero : expD 0 = 1 := by
  ext f : 1
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_expD]
  simp [expMult]

theorem expMult_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    expMult (a + b) n = expMult a n * expMult b n := by
  simp only [expMult, max_eq_left ha, max_eq_left hb, max_eq_left (add_nonneg ha hb)]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- Semigroup law `e^{(a+b)D} = e^{aD} e^{bD}` (`a, b ≥ 0`). -/
theorem expD_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    expD (a + b) = (expD a).comp (expD b) := by
  ext f : 1
  apply ext_inner_basis oscBasis
  intro n
  rw [ContinuousLinearMap.comp_apply, inner_expD, inner_expD, inner_expD, expMult_add ha hb,
    mul_assoc]

/-- `‖e^{aD}‖ ≤ 1` (`D ≤ 0`). -/
theorem norm_expD_le (a : ℝ) : ‖expD a‖ ≤ 1 := by
  unfold expD diagCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## The smoothing estimate -/

/-- The multiplier bound: `(1 + (1+ℓ)^{j+1}) e^{-2aℓ} ≤ a^{-1} (1 + (1+ℓ)^j)` for `0 < a ≤ 1`
(the unit's notes: `sup_ℓ (1+ℓ)^{1/2} e^{-aℓ} ≤ C a^{-1/2}`). -/
theorem smoothing_scalar {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (j n : ℕ) :
    (1 + (1 + (n : ℝ)) ^ (j + 1)) * ‖expMult a n‖ ^ 2 ≤ a⁻¹ * (1 + (1 + (n : ℝ)) ^ j) := by
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hE : ‖expMult a n‖ ^ 2 = Real.exp (-(2 * a * n)) := by
    rw [expMult, max_eq_left ha.le, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      sq, ← Real.exp_add]
    congr 1
    ring
  rw [hE]
  have key : (1 + (n : ℝ)) * Real.exp (-(2 * a * n)) ≤ a⁻¹ := by
    -- the square of `(1 + ℓ)^{1/2} e^{-aℓ} ≤ a^{-1/2}` (Lib, `Infra.Mult`)
    have h := UnforcedLeray.Infra.Mult.sqrt_one_add_mul_exp_neg_le ha ha1 hn
    have hsq := pow_le_pow_left₀ (UnforcedLeray.Infra.Mult.sqrt_one_add_mul_exp_neg_nonneg a n)
      h 2
    have e : Real.exp (-(2 * a * n)) = Real.exp (-(a * n)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc (1 + (n : ℝ)) * Real.exp (-(2 * a * n))
        = (Real.sqrt (1 + n) * Real.exp (-(a * n))) ^ 2 := by
          rw [e, mul_pow, Real.sq_sqrt (by linarith)]
      _ ≤ (1 / Real.sqrt a) ^ 2 := hsq
      _ = a⁻¹ := by rw [div_pow, one_pow, Real.sq_sqrt ha.le, one_div]
  have hpow : 1 + (1 + (n : ℝ)) ^ (j + 1) ≤ (1 + n) * (1 + (1 + n) ^ j) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + n) j]
  calc (1 + (1 + (n : ℝ)) ^ (j + 1)) * Real.exp (-(2 * a * n))
      ≤ (1 + n) * (1 + (1 + n) ^ j) * Real.exp (-(2 * a * n)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ((1 + n) * Real.exp (-(2 * a * n))) * (1 + (1 + n) ^ j) := by ring
    _ ≤ a⁻¹ * (1 + (1 + n) ^ j) := mul_le_mul_of_nonneg_right key (by positivity)

/-- **`eq:st18-t00101`, explicit form** (tex lines 1873--1878): for `0 < a ≤ 1`, `e^{aD}` maps
`X_{G,j}` into `X_{G,j+1}` and `‖e^{aD} f‖_{X_{G,j+1}} ≤ a^{-1/2} ‖f‖_{X_{G,j}}`
(graph norms; the constant is `C_j = 1`). -/
theorem expD_smoothing (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (f : XGj j) :
    ∃ h : expD a (f : XG) ∈ XGj (j + 1),
      xgjNorm (j + 1) ⟨expD a f, h⟩ ≤ a ^ (-(1 / 2 : ℝ)) * xgjNorm j f := by
  have hf := hasSum_xgjNorm_sq j f
  have hle : ∀ n : ℕ, (1 + (1 + (n : ℝ)) ^ (j + 1)) * ‖⟪oscBasis n, expD a (f : XG)⟫_ℂ‖ ^ 2 ≤
      a⁻¹ * ((1 + (1 + (n : ℝ)) ^ j) * ‖⟪oscBasis n, (f : XG)⟫_ℂ‖ ^ 2) := by
    intro n
    rw [inner_expD, norm_mul, mul_pow, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (smoothing_scalar ha ha1 j n) (by positivity)
  have hmem : expD a (f : XG) ∈ XGj (j + 1) := by
    rw [mem_XGj_iff]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hf.summable.mul_left a⁻¹)
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) (hle n)
    linarith
  refine ⟨hmem, ?_⟩
  have hg := hasSum_xgjNorm_sq (j + 1) ⟨expD a f, hmem⟩
  have hsq : xgjNorm (j + 1) ⟨expD a f, hmem⟩ ^ 2 ≤ a⁻¹ * xgjNorm j f ^ 2 :=
    hasSum_le hle hg (hf.mul_left a⁻¹)
  have h0 : 0 ≤ a ^ (-(1 / 2 : ℝ)) * xgjNorm j f :=
    mul_nonneg (Real.rpow_nonneg ha.le _) (xgjNorm_nonneg j f)
  apply le_of_pow_le_pow_left₀ two_ne_zero h0
  rw [mul_pow, ← Real.rpow_mul_natCast ha.le,
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
  exact hsq

/-- **`eq:st18-t00101`** (tex lines 1873--1878, blueprint unit B0123): for each `j ≥ 0` there is
`C_j` with `‖e^{aD}‖_{X_{G,j} → X_{G,j+1}} ≤ C_j a^{-1/2}` for `0 < a ≤ 1`, i.e. `e^{aD}` maps
`X_{G,j}` into `X_{G,j+1}` with `‖e^{aD} f‖_{X_{G,j+1}} ≤ C_j a^{-1/2} ‖f‖_{X_{G,j}}`. -/
theorem eq_st18_t00101 (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ f : XGj j,
      ∃ h : expD a (f : XG) ∈ XGj (j + 1),
        xgjNorm (j + 1) ⟨expD a f, h⟩ ≤ C * a ^ (-(1 / 2 : ℝ)) * xgjNorm j f := by
  refine ⟨1, zero_le_one, fun a ha ha1 f => ?_⟩
  obtain ⟨h, hh⟩ := expD_smoothing j ha ha1 f
  exact ⟨h, by rwa [one_mul]⟩

/-! ## Agreement with B0121's `X_{G,j}` -/

/-- **`X_{G,j}` here is B0121's `X_{G,j}`** (`Units/B0121/Spectral.lean`, `B0121.XGj`): both are
`𝒟((I - D)^{j/2})` (tex line 748, `eq:st18-t00014`) built from B0094's eigenbasis. -/
theorem XGj_eq_B0121 (j : ℕ) : XGj j = B0121.XGj j := by
  ext f
  rw [mem_XGj_iff, B0121.mem_XGj_iff]

/-- `(I - D)^{j/2}` here is B0121's `fracPow j`, domain and values included. -/
theorem IDpow_half_eq_fracPow (j : ℕ) : IDpow ((j : ℝ) / 2) = B0121.fracPow j := by
  refine LinearPMap.ext (XGj_eq_B0121 j) fun x hx hy => ?_
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_IDpow, B0121.inner_fracPow]
  rfl

/-- The graph norms agree: `‖f‖²_{X_{G,j}} = B0121.graphNormSq j f`
(`= ‖f‖² + ‖(I - D)^{j/2} f‖²`, tex line 1858). -/
theorem xgjNorm_sq_eq_graphNormSq (j : ℕ) (f : XGj j) :
    xgjNorm j f ^ 2 = B0121.graphNormSq j ⟨f, (XGj_eq_B0121 j).le f.2⟩ := by
  rw [B0121.graphNormSq_eq]
  exact (hasSum_xgjNorm_sq j f).tsum_eq.symm

/-- The graph norms agree, read from B0121's side. -/
theorem graphNormSq_eq_xgjNorm_sq (j : ℕ) (f : (B0121.fracPow j).domain) :
    B0121.graphNormSq j f = xgjNorm j ⟨f, (XGj_eq_B0121 j).ge f.2⟩ ^ 2 := by
  rw [B0121.graphNormSq_eq]
  exact (hasSum_xgjNorm_sq j ⟨f, (XGj_eq_B0121 j).ge f.2⟩).tsum_eq

/-- **`eq:st18-t00101` in B0121's terms** (tex lines 1873--1878, blueprint unit B0123): for
`0 < a ≤ 1`, `e^{aD}` maps `B0121.XGj j = 𝒟(B0121.fracPow j)` into `B0121.XGj (j + 1)`, and the
squared graph norms satisfy `graphNormSq (j + 1) (e^{aD} f) ≤ a⁻¹ graphNormSq j f` (the square of
`‖e^{aD} f‖_{X_{G,j+1}} ≤ C_j a^{-1/2} ‖f‖_{X_{G,j}}` with `C_j = 1`). -/
theorem eq_st18_t00101_graphNormSq (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (f : (B0121.fracPow j).domain) :
    ∃ h : expD a (f : XG) ∈ (B0121.fracPow (j + 1)).domain,
      B0121.graphNormSq (j + 1) ⟨expD a f, h⟩ ≤ a⁻¹ * B0121.graphNormSq j f := by
  have hf : (f : XG) ∈ XGj j := (XGj_eq_B0121 j).ge f.2
  obtain ⟨h, hh⟩ := expD_smoothing j ha ha1 ⟨f, hf⟩
  refine ⟨(XGj_eq_B0121 (j + 1)).le h, ?_⟩
  have hsq : xgjNorm (j + 1) ⟨expD a f, h⟩ ^ 2 ≤ a⁻¹ * xgjNorm j ⟨f, hf⟩ ^ 2 := by
    have h2 := pow_le_pow_left₀ (xgjNorm_nonneg _ _) hh 2
    rwa [mul_pow, ← Real.rpow_mul_natCast ha.le,
      show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one] at h2
  rw [graphNormSq_eq_xgjNorm_sq, graphNormSq_eq_xgjNorm_sq]
  exact hsq

end UnforcedLeray.B0123
