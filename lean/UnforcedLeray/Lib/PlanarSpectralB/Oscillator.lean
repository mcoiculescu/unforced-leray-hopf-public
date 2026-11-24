import UnforcedLeray.Units.B0094
import UnforcedLeray.Units.B0121
import UnforcedLeray.Units.B0122
import UnforcedLeray.Units.B0123
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import UnforcedLeray.Lib.Semigroups.Dunford.Defs

/-!
# The Gaussian oscillator `D` on `X_G`: classical action, semigroup, Sobolev norms
(INF10 targets H3–H6)


§5, Level H (targets **H3**–**H6**) and bypass B6 of §4 (a Laguerre diagonal model of `D` on
`X_G`). Manuscript (`paper/main.tex`): `D = Δ + ½ y·∇ + 2` (`eq:st18-t00011`, line 740); the
conjugation to the oscillator `eq:st18-t00067` (lines 1498–1502, unit `B0093`); `D` selfadjoint,
`D ≤ 0`, spectrum `{0, -1, -2, …}` (`eq:st18-t00068`, lines 1503–1515, unit `B0094`); the bounded
extensions of `PD`, `DP` (`eq:st18-t00069`, lines 1518–1524, unit `B0097`); the Gaussian class
`𝒢₂` (lines 1526–1539, unit `B0098`); Yosida (line 1667) and the free evolutions (lines
1660–1700); the graph norms of `X_{G,j}` (`eq:st18-t00100`, lines 1856–1865, unit `B0121`); `L₀`
on `X_{G,j}` (lines 1867–1871, unit `B0122`); one-derivative smoothing (`eq:st18-t00101`, lines
1873–1878, unit `B0123`).

This module is the library layer over the compiled unit drafts `Units/B0093`, `B0094`, `B0121`,
`B0122`, `B0123`, which carry the analysis; it adds the Gaussian class, the Yosida approximants
and the free evolutions, and restates the unit results under the scoping-note names.

| Target | Declarations |
|---|---|
| H3 | `IsGaussClass` (`𝒢₂`), `gaussInv`, `exists_schwartz_gaussInv_smul`, `exists_schwartz_conjG`, `isAngularTwo_conjG`, `D_classical_schwartz`, **`D_classical_laguerre`**, `D_symmetric` |
| H4 | `Dsemigroup`, `inner_Dsemigroup`, `Dsemigroup_zero`, `Dsemigroup_add`, `norm_Dsemigroup_le`, **`norm_Dsemigroup_smoothing`**, `D_nonpos'`, `yosidaMult`, `Dyosida`, `inner_Dyosida`, `norm_Dyosida_le`, **`tendsto_Dyosida`**, `freeEvolD`, `freeEvolD_self`, `freeEvolD_comp`, `norm_freeEvolD_le`, `inner_freeEvolD`, `exists_bounded_PD`, `exists_bounded_DP` |
| H5 | **`sum_words_norm_deriv_sq`** (alias of `B0121.sum_words_gaussNormSq_eq`), `graphNorm_equiv_gauss` (alias of `B0121.graphNorm_equiv`) |
| H6 | **`L0_bounded_XGj`** (alias of `B0122.L0_mem_XGj`, conditional), `omega_bounded_XGj` (alias of `B0122.omegaOp_mem_XGj`, unconditional) |

**Conventions.** `𝒢₂` (tex line 1527: "smooth angular-two functions with
`|∂^α f| ≤ C_α (1+|y|)^{N_α} G`") is stated with the full `n`-th derivative
`iteratedFDeriv ℝ n f`, whose norm dominates every `∂^α f` with `|α| = n` and is dominated by
their sum; the two classes coincide. The `X_G` element of an angular-two function `f` is its
profile `f(r, 0)` (B0010's `angularTwoField`).

**Named hypothesis (H6).** `L0_bounded_XGj` is conditional on `B0122.GreenEllipticRegularity j`,
the global elliptic estimate `‖Rf‖_{H^j} ≤ C_j(‖f‖_{H^{j-2}} + ‖f‖_{X_G})` of tex line 1869
(Fourier multipliers on `ℝ²`, INF11 S9a / INF21, not built). Multiplication by `Ω` is
unconditional (`omega_bounded_XGj`).

Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap InnerProductSpace ComplexConjugate ContDiff Nat Real ENNReal

namespace UnforcedLeray.PlanarSpectral

open UnforcedLeray.GaussianVortex (radiusSq planarGaussian)

/-! ## H3: the Gaussian class and the classical action of `D` -/

/-- **The Gaussian class `𝒢₂`** without the angular condition (tex lines 1526–1528): smooth
functions on `ℝ²` with `‖Dⁿ f(y)‖ ≤ C_n (1 + |y|)^{N_n} G(y)` for every `n`. -/
def IsGaussClass (f : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ z : ℝ × ℝ,
    ‖iteratedFDeriv ℝ n f z‖ ≤ C * (1 + ‖z‖) ^ N * B0093.gaussianWeight z

/-- `e^{|y|²/8}` (so that `U_G f = f / √G = (4π)^{1/2} e^{|y|²/8} f`). -/
def gaussInv : ℝ × ℝ → ℝ := Real.exp ∘ (-B0094.gaussExp)

theorem hasTemperateGrowth_neg_gaussExp : Function.HasTemperateGrowth (-B0094.gaussExp) :=
  B0094.hasTemperateGrowth_gaussExp.neg

theorem contDiff_gaussInv : ContDiff ℝ ∞ gaussInv :=
  Real.contDiff_exp.comp hasTemperateGrowth_neg_gaussExp.1

theorem gaussInv_apply (z : ℝ × ℝ) : gaussInv z = Real.exp ((z.1 ^ 2 + z.2 ^ 2) / 8) := by
  simp only [gaussInv, Function.comp_apply, Pi.neg_apply, B0094.gaussExp, neg_neg]

theorem gaussInv_nonneg (z : ℝ × ℝ) : 0 ≤ gaussInv z := (Real.exp_pos _).le

/-- `e^{|y|²/8} G(y) = (4π)⁻¹ e^{-|y|²/8} ≤ (4π)⁻¹ e^{-‖y‖²/8}`. -/
theorem gaussInv_mul_gaussianWeight_le (z : ℝ × ℝ) :
    gaussInv z * B0093.gaussianWeight z ≤ (4 * π)⁻¹ * Real.exp (-(‖z‖ ^ 2 / 8)) := by
  have e1 : gaussInv z * B0093.gaussianWeight z =
      (4 * π)⁻¹ * Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) := by
    rw [gaussInv_apply, B0093.gaussianWeight, planarGaussian, radiusSq, mul_left_comm,
      ← Real.exp_add]
    congr 2
    ring
  rw [e1]
  have h := B0094.norm_sq_le_sz z
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)

/-- Derivative bounds of `e^{|y|²/8}` (Faà di Bruno, as for B0094's `gaussS`). -/
theorem norm_iteratedFDeriv_gaussInv_le (n : ℕ) : ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ i, i ≤ n → ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ i gaussInv z‖ ≤ i ! * gaussInv z * ((1 + C) * (1 + ‖z‖) ^ m) ^ i := by
  obtain ⟨m, C, hC, hb⟩ := hasTemperateGrowth_neg_gaussExp.norm_iteratedFDeriv_le_uniform n
  refine ⟨m, C, hC, fun i hi z => ?_⟩
  set Dz : ℝ := (1 + C) * (1 + ‖z‖) ^ m with hDz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hDz1 : 1 ≤ Dz :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
  have hD : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j (-B0094.gaussExp) z‖ ≤ Dz ^ j := by
    intro j hj hji
    calc ‖iteratedFDeriv ℝ j (-B0094.gaussExp) z‖ ≤ C * (1 + ‖z‖) ^ m := hb j (hji.trans hi) z
      _ ≤ Dz := by
        rw [hDz]
        gcongr
        linarith
      _ ≤ Dz ^ j := le_self_pow₀ hDz1 (by omega)
  have hE : ∀ j, j ≤ i → ‖iteratedFDeriv ℝ j Real.exp ((-B0094.gaussExp) z)‖ ≤
      Real.exp ((-B0094.gaussExp) z) := fun j _ => (B0094.norm_iteratedFDeriv_exp j _).le
  exact norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp
    hasTemperateGrowth_neg_gaussExp.1 (by exact_mod_cast le_top) z hE hD

/-- **`e^{|y|²/8} g` is Schwartz** for every smooth `g` with Gaussian derivative bounds. -/
theorem exists_schwartz_gaussInv_smul {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hA : ∀ j : ℕ, ∃ A : ℝ, ∃ N : ℕ, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j g z‖ ≤ A * (1 + ‖z‖) ^ N * B0093.gaussianWeight z) :
    ∃ ψ : 𝓢(ℝ × ℝ, ℂ), ∀ z, ψ z = gaussInv z • g z := by
  choose Af Nf hAf using hA
  choose K hK using B0094.poly_gauss_bound
  refine ⟨{ toFun := fun z => gaussInv z • g z
            smooth' := contDiff_gaussInv.smul hg
            decay' := fun k n => ?_ }, fun z => rfl⟩
  obtain ⟨m, C, hC, hb⟩ := norm_iteratedFDeriv_gaussInv_le n
  set B : ℕ → ℝ := fun i => (n.choose i : ℝ) * i ! * (1 + C) ^ i * |Af (n - i)| *
    (4 * π)⁻¹ * K (k + m * i + Nf (n - i)) with hBdef
  refine ⟨∑ i ∈ Finset.range (n + 1), B i, fun z => ?_⟩
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hL := norm_iteratedFDeriv_smul_le (N := ∞) contDiff_gaussInv hg z (n := n)
    (by exact_mod_cast le_top)
  have term : ∀ i, i < n + 1 → ‖z‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i gaussInv z‖ *
      ‖iteratedFDeriv ℝ (n - i) g z‖) ≤ B i := by
    intro i hi
    have h1 := hb i (by omega) z
    have h2 : ‖iteratedFDeriv ℝ (n - i) g z‖ ≤
        |Af (n - i)| * (1 + ‖z‖) ^ Nf (n - i) * B0093.gaussianWeight z := by
      refine (hAf (n - i) z).trans ?_
      have hw : 0 ≤ (1 + ‖z‖) ^ Nf (n - i) * B0093.gaussianWeight z :=
        mul_nonneg (by positivity) (B0093.gaussianWeight_pos z).le
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hw
    have h3 := hK (k + m * i + Nf (n - i)) ‖z‖ hz0
    rw [pow_add, pow_add] at h3
    have hGi := gaussInv_mul_gaussianWeight_le z
    have hzk : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k := by
      gcongr
      linarith
    have hG0 : 0 ≤ B0093.gaussianWeight z := (B0093.gaussianWeight_pos z).le
    have hgi0 := gaussInv_nonneg z
    calc ‖z‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i gaussInv z‖ *
          ‖iteratedFDeriv ℝ (n - i) g z‖)
        ≤ (1 + ‖z‖) ^ k * ((n.choose i : ℝ) * (i ! * gaussInv z * ((1 + C) * (1 + ‖z‖) ^ m) ^ i) *
          (|Af (n - i)| * (1 + ‖z‖) ^ Nf (n - i) * B0093.gaussianWeight z)) := by
          gcongr
      _ = (n.choose i : ℝ) * i ! * (1 + C) ^ i * |Af (n - i)| *
          ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ (m * i) * (1 + ‖z‖) ^ Nf (n - i) *
            (gaussInv z * B0093.gaussianWeight z)) := by
          rw [mul_pow, ← pow_mul]
          ring
      _ ≤ (n.choose i : ℝ) * i ! * (1 + C) ^ i * |Af (n - i)| *
          ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ (m * i) * (1 + ‖z‖) ^ Nf (n - i) *
            ((4 * π)⁻¹ * Real.exp (-(‖z‖ ^ 2 / 8)))) := by
          gcongr
      _ = (n.choose i : ℝ) * i ! * (1 + C) ^ i * |Af (n - i)| * (4 * π)⁻¹ *
          ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ (m * i) * (1 + ‖z‖) ^ Nf (n - i) *
            Real.exp (-(‖z‖ ^ 2 / 8))) := by ring
      _ ≤ B i := by
          simp only [hBdef]
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  change ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => gaussInv y • g y) z‖ ≤ _
  calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => gaussInv y • g y) z‖
      ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i gaussInv z‖ * ‖iteratedFDeriv ℝ (n - i) g z‖ :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), ‖z‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i gaussInv z‖ * ‖iteratedFDeriv ℝ (n - i) g z‖) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), B i :=
        Finset.sum_le_sum fun i hi => term i (Finset.mem_range.1 hi)

/-- `(√G)⁻¹ = (4π)^{1/2} e^{|y|²/8}`. -/
theorem inv_halfGaussian (z : ℝ × ℝ) :
    (B0093.halfGaussian B0093.sqrtConst z)⁻¹ = B0093.sqrtConst⁻¹ * gaussInv z := by
  rw [B0093.halfGaussian, mul_inv, ← Real.exp_neg, gaussInv_apply, radiusSq, neg_neg]

/-- **`U_G` maps `𝒢₂` into the Schwartz class** (tex lines 1516–1517, 1526–1539): for `f` in the
Gaussian class, `U_G f = f/√G` is a Schwartz function. -/
theorem exists_schwartz_conjG {f : ℝ × ℝ → ℂ} (hf : IsGaussClass f) :
    ∃ ψ : 𝓢(ℝ × ℝ, ℂ), (ψ : ℝ × ℝ → ℂ) = B0093.conjG f := by
  set c : ℝ := B0093.sqrtConst⁻¹ with hc
  have hg : ContDiff ℝ ∞ (c • f) := hf.1.const_smul c
  have hA : ∀ j : ℕ, ∃ A : ℝ, ∃ N : ℕ, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (c • f) z‖ ≤ A * (1 + ‖z‖) ^ N * B0093.gaussianWeight z := by
    intro j
    obtain ⟨C, N, hCN⟩ := hf.2 j
    refine ⟨|c| * C, N, fun z => ?_⟩
    have hd : ContDiffAt ℝ j f z := (hf.1.contDiffAt).of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_const_smul_apply hd, norm_smul, Real.norm_eq_abs, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [← mul_assoc]; exact hCN z) (abs_nonneg c)
  obtain ⟨ψ, hψ⟩ := exists_schwartz_gaussInv_smul hg hA
  refine ⟨ψ, funext fun z => ?_⟩
  simp only [hψ z, B0093.conjG_eq, Pi.smul_apply, smul_smul, inv_halfGaussian]
  congr 1
  rw [hc]
  ring

theorem halfGaussian_rot (c θ : ℝ) (z : ℝ × ℝ) :
    B0093.halfGaussian c (B0094.rot θ z) = B0093.halfGaussian c z := by
  have h : radiusSq (B0094.rot θ z) = radiusSq z := B0094.sz_rot θ z
  rw [B0093.halfGaussian, B0093.halfGaussian, h]

/-- `U_G` preserves angular weight two (`G` is radial). -/
theorem isAngularTwo_conjG {f : ℝ × ℝ → ℂ} (h : B0094.IsAngularTwo f) :
    B0094.IsAngularTwo (B0093.conjG f) := by
  intro θ z
  rw [B0093.conjG_eq]
  simp only
  rw [h θ z, halfGaussian_rot, mul_smul_comm]

/-- **H3 on the Schwartz class** (B0094, tex lines 1503–1515): for `ψ ∈ 𝓢(ℝ²)` of angular weight
two, `U_G⁻¹ψ ∈ 𝒟(D)`, `D(U_G⁻¹ψ) = U_G⁻¹(osc ψ)`, which is the classical
`Δ + ½ y·∇ + 2` applied to `U_G⁻¹ψ`, and the Laguerre coefficients scale by `-ℓ`. -/
theorem D_classical_schwartz (ψ : 𝓢(ℝ × ℝ, ℂ)) (hψ : B0094.IsAngularTwo ψ) :
    ∃ h : (B0094.memLp_schProf ψ).toLp (B0094.schProf ψ) ∈ B0094.D.domain,
      B0094.D ⟨_, h⟩ =
          (B0094.memLp_schProf (B0094.oscS ψ)).toLp (B0094.schProf (B0094.oscS ψ)) ∧
        B0010.angularTwoField (B0094.schProf (B0094.oscS ψ)) =
          B0093.gaussianOperator (B0010.angularTwoField (B0094.schProf ψ)) ∧
        ∀ ℓ : ℕ, ⟪B0094.oscBasis ℓ, B0094.D ⟨_, h⟩⟫_ℂ =
          -(ℓ : ℂ) * ⟪B0094.oscBasis ℓ, (B0094.memLp_schProf ψ).toLp (B0094.schProf ψ)⟫_ℂ := by
  obtain ⟨h, hD⟩ := B0094.schwartz_mem_D ψ hψ
  exact ⟨h, hD, B0094.angularTwoField_schProf_oscS ψ hψ, fun ℓ => B0123.inner_D ⟨_, h⟩ ℓ⟩

/-- **H3** (`D_classical_laguerre`, scoping note §5, Level H): for `f ∈ 𝒢₂` of angular weight
two (tex lines 1526–1539), the element `F ∈ X_G` with profile `f(r, 0)` lies in `𝒟(D)`, `D F`
has the profile of the classical `Df = Δf + ½ y·∇f + 2f` (`eq:st18-t00011`), and
`⟪e_ℓ, D F⟫ = -ℓ ⟪e_ℓ, F⟫` for the Laguerre eigenbasis `e_ℓ = oscBasis ℓ`. -/
theorem D_classical_laguerre {f : ℝ × ℝ → ℂ} (hf : IsGaussClass f)
    (ha : B0094.IsAngularTwo f) :
    ∃ (F DF : B0010.XG) (hF : F ∈ B0094.D.domain),
      B0094.D ⟨F, hF⟩ = DF ∧
      (∃ F₂ DF₂ : ℝ → ℂ, B0010.angularTwoField F₂ = f ∧
        B0010.angularTwoField DF₂ = B0093.gaussianOperator f ∧
        ⇑F =ᵐ[B0010.xGMeasure] F₂ ∧ ⇑DF =ᵐ[B0010.xGMeasure] DF₂) ∧
      ∀ ℓ : ℕ, ⟪B0094.oscBasis ℓ, DF⟫_ℂ = -(ℓ : ℂ) * ⟪B0094.oscBasis ℓ, F⟫_ℂ := by
  obtain ⟨ψ, hψeq⟩ := exists_schwartz_conjG hf
  have hψ : B0094.IsAngularTwo ψ := by
    intro θ z
    have := isAngularTwo_conjG ha θ z
    rw [hψeq]
    exact this
  obtain ⟨h, hD, hcl, hco⟩ := D_classical_schwartz ψ hψ
  refine ⟨_, _, h, hD, ⟨B0094.schProf ψ, B0094.schProf (B0094.oscS ψ), ?_, ?_,
    (B0094.memLp_schProf ψ).coeFn_toLp, (B0094.memLp_schProf _).coeFn_toLp⟩, fun ℓ => ?_⟩
  · rw [B0094.angularTwoField_schProf hψ, hψeq, B0093.conjGInv_conjG]
  · rw [hcl, B0094.angularTwoField_schProf hψ, hψeq, B0093.conjGInv_conjG]
  · rw [← hD]
    exact hco ℓ

/-- **H3, symmetry**: `⟪D f, g⟫ = ⟪f, D g⟫` on `𝒟(D)` (B0094). -/
theorem D_symmetric (f g : B0094.D.domain) :
    ⟪B0094.D f, (g : B0010.XG)⟫_ℂ = ⟪(f : B0010.XG), B0094.D g⟫_ℂ :=
  B0094.D_symm f g

/-! ## H4: the semigroup, the Yosida approximants, the free evolutions -/

/-- **H4.** `e^{aD} = diag(e^{-aℓ})` on `X_G` (`a ≥ 0`; B0123's `expD`, tex line 1875). For
`a < 0` it is the junk value `1` (B0123 uses `e^{-max(a,0)ℓ}`); the coefficient, semigroup and
smoothing statements assume `a ≥ 0` (`a > 0`). -/
def Dsemigroup (a : ℝ) : B0010.XG →L[ℂ] B0010.XG := B0123.expD a

theorem inner_Dsemigroup {a : ℝ} (ha : 0 ≤ a) (f : B0010.XG) (ℓ : ℕ) :
    ⟪B0094.oscBasis ℓ, Dsemigroup a f⟫_ℂ =
      ((Real.exp (-(a * ℓ)) : ℝ) : ℂ) * ⟪B0094.oscBasis ℓ, f⟫_ℂ := by
  rw [Dsemigroup, B0123.inner_expD, B0123.expMult, max_eq_left ha]

theorem Dsemigroup_zero : Dsemigroup 0 = 1 := B0123.expD_zero

theorem Dsemigroup_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Dsemigroup (a + b) = (Dsemigroup a).comp (Dsemigroup b) := B0123.expD_add ha hb

theorem norm_Dsemigroup_le (a : ℝ) : ‖Dsemigroup a‖ ≤ 1 := B0123.norm_expD_le a

/-- **H4, smoothing** (`eq:st18-t00101`, tex lines 1873–1878): `e^{aD}` maps `X_{G,j}` into
`X_{G,j+1}` with `‖e^{aD}f‖_{X_{G,j+1}} ≤ C_j a^{-1/2} ‖f‖_{X_{G,j}}` for `0 < a ≤ 1`. -/
theorem norm_Dsemigroup_smoothing (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ f : B0123.XGj j,
      ∃ h : Dsemigroup a (f : B0010.XG) ∈ B0123.XGj (j + 1),
        B0123.xgjNorm (j + 1) ⟨Dsemigroup a f, h⟩ ≤
          C * a ^ (-(1 / 2 : ℝ)) * B0123.xgjNorm j f :=
  B0123.eq_st18_t00101 j

/-- **H4, `D ≤ 0`** (tex line 1509). -/
theorem D_nonpos' (f : B0094.D.domain) :
    (⟪(f : B0010.XG), B0094.D f⟫_ℂ).re ≤ 0 ∧ (⟪(f : B0010.XG), B0094.D f⟫_ℂ).im = 0 :=
  B0094.D_nonpos f

/-- The Yosida multipliers `-ℓn/(n + ℓ)` (bypass B6; tex line 1667). -/
def yosidaMult (n ℓ : ℕ) : ℂ := -((((ℓ : ℝ) * n / (n + ℓ)) : ℝ) : ℂ)

theorem yosida_val_nonneg (n ℓ : ℕ) : 0 ≤ (ℓ : ℝ) * n / (n + ℓ) := by positivity

theorem yosida_val_le (n ℓ : ℕ) : (ℓ : ℝ) * n / (n + ℓ) ≤ n := by
  rw [mul_comm, mul_div_assoc]
  have h : (ℓ : ℝ) / (n + ℓ) ≤ 1 := div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    (by positivity)
  calc (n : ℝ) * ((ℓ : ℝ) / (n + ℓ)) ≤ n * 1 :=
        mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    _ = n := mul_one _

theorem yosida_val_le_self (n ℓ : ℕ) : (ℓ : ℝ) * n / (n + ℓ) ≤ ℓ := by
  rw [mul_div_assoc]
  have h : (n : ℝ) / (n + ℓ) ≤ 1 :=
    div_le_one_of_le₀ (by linarith [(ℓ.cast_nonneg : (0 : ℝ) ≤ ℓ)]) (by positivity)
  calc (ℓ : ℝ) * ((n : ℝ) / (n + ℓ)) ≤ ℓ * 1 := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg ℓ)
    _ = ℓ := mul_one _

theorem norm_yosidaMult_le (n ℓ : ℕ) : ‖yosidaMult n ℓ‖ ≤ n := by
  rw [yosidaMult, norm_neg, Complex.norm_real, Real.norm_of_nonneg (yosida_val_nonneg n ℓ)]
  exact yosida_val_le n ℓ

/-- **H4, Yosida approximants** `D_n = diag(-ℓn/(n + ℓ))`, bounded by `n`. -/
def Dyosida (n : ℕ) : B0010.XG →L[ℂ] B0010.XG :=
  B0094.diagCLM B0094.oscBasis (yosidaMult n) n (norm_yosidaMult_le n)

theorem inner_Dyosida (n : ℕ) (f : B0010.XG) (ℓ : ℕ) :
    ⟪B0094.oscBasis ℓ, Dyosida n f⟫_ℂ = yosidaMult n ℓ * ⟪B0094.oscBasis ℓ, f⟫_ℂ :=
  B0094.inner_diagCLM B0094.oscBasis _ _ _ f ℓ

theorem norm_Dyosida_le (n : ℕ) : ‖Dyosida n‖ ≤ n := by
  unfold Dyosida B0094.diagCLM
  exact LinearMap.mkContinuous_norm_le _ (Nat.cast_nonneg n) _

/-- **H4, Yosida convergence**: `D_n f → D f` for `f ∈ 𝒟(D)`. -/
theorem tendsto_Dyosida (f : B0094.D.domain) :
    Tendsto (fun n : ℕ => Dyosida n f) atTop (𝓝 (B0094.D f)) := by
  set c : ℕ → ℂ := fun ℓ => ⟪B0094.oscBasis ℓ, (f : B0010.XG)⟫_ℂ with hc
  set r : ℕ → ℕ → ℝ := fun n ℓ => (ℓ : ℝ) - (ℓ : ℝ) * n / (n + ℓ) with hr
  have hcoef : ∀ n ℓ, ⟪B0094.oscBasis ℓ, Dyosida n f - B0094.D f⟫_ℂ = (r n ℓ : ℂ) * c ℓ := by
    intro n ℓ
    rw [inner_sub_right, inner_Dyosida, B0123.inner_D]
    simp only [yosidaMult, hr, hc]
    push_cast
    ring
  have hr0 : ∀ n ℓ, 0 ≤ r n ℓ := by
    intro n ℓ
    simp only [hr]
    linarith [yosida_val_le_self n ℓ]
  have hrle : ∀ n ℓ, r n ℓ ≤ ℓ := by
    intro n ℓ
    simp only [hr]
    linarith [yosida_val_nonneg n ℓ]
  have hrlim : ∀ ℓ : ℕ, Tendsto (fun n => r n ℓ) atTop (𝓝 0) := by
    intro ℓ
    have h := (tendsto_natCast_div_add_atTop (ℓ : ℝ)).const_mul (ℓ : ℝ)
    rw [mul_one] at h
    have h2 := (tendsto_const_nhds (x := (ℓ : ℝ))).sub h
    rw [sub_self] at h2
    refine h2.congr fun n => ?_
    simp only [hr]
    ring
  have hmem := (B0123.mem_D_domain_iff_memℓp (f : B0010.XG)).1 f.2
  have hsum : Summable fun ℓ : ℕ => ‖(ℓ : ℂ) * c ℓ‖ ^ 2 := by
    have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 hmem
    simpa [Real.rpow_two] using h
  have hsq : ∀ n, HasSum (fun ℓ => ‖(r n ℓ : ℂ) * c ℓ‖ ^ 2) (‖Dyosida n f - B0094.D f‖ ^ 2) := by
    intro n
    have h := B0123.hasSum_norm_inner_sq B0094.oscBasis (Dyosida n f - B0094.D f)
    simp_rw [hcoef] at h
    exact h
  have hlim : Tendsto (fun n => ‖Dyosida n f - B0094.D f‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun n ℓ => ‖(r n ℓ : ℂ) * c ℓ‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun ℓ => ‖(ℓ : ℂ) * c ℓ‖ ^ 2) hsum ?_ ?_
    · simp only [tsum_zero] at h
      refine h.congr fun n => ?_
      exact (hsq n).tsum_eq
    · intro ℓ
      have h1 := ((Complex.continuous_ofReal.tendsto 0).comp (hrlim ℓ))
      simp only [Function.comp_def, Complex.ofReal_zero] at h1
      have h2 := ((h1.mul_const (c ℓ)).norm.pow 2)
      simpa using h2
    · refine Eventually.of_forall fun n ℓ => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast,
        Real.norm_of_nonneg (hr0 n ℓ)]
      exact mul_le_mul_of_nonneg_right (hrle n ℓ) (norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h3 := ((Real.continuous_sqrt.tendsto 0).comp hlim)
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at h3
  exact h3

/-- **H4, free evolution** `E_β(t, s) = e^{(∫_s^t β) D} = diag(exp(-ℓ∫_s^t β))` (bypass B6;
tex lines 1660–1700). Meaningful for `s ≤ t` and `β ≥ 0`; for `s > t` it is a junk value. -/
def freeEvolD (β : ℝ → ℝ) (t s : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  Dsemigroup (∫ τ in s..t, β τ)

theorem freeEvolD_self (β : ℝ → ℝ) (t : ℝ) : freeEvolD β t t = 1 := by
  rw [freeEvolD, intervalIntegral.integral_same, Dsemigroup_zero]

/-- The evolution law `E_β(t, s) E_β(s, r) = E_β(t, r)`, `r ≤ s ≤ t`, for `β ≥ 0`. -/
theorem freeEvolD_comp {β : ℝ → ℝ} (hβ : ∀ τ, 0 ≤ β τ)
    (hβi : ∀ a b : ℝ, IntervalIntegrable β volume a b) {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    (freeEvolD β t s).comp (freeEvolD β s r) = freeEvolD β t r := by
  unfold freeEvolD
  rw [← Dsemigroup_add (intervalIntegral.integral_nonneg hst fun τ _ => hβ τ)
    (intervalIntegral.integral_nonneg hrs fun τ _ => hβ τ), add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hβi r s) (hβi s t)]

theorem norm_freeEvolD_le (β : ℝ → ℝ) (t s : ℝ) : ‖freeEvolD β t s‖ ≤ 1 :=
  norm_Dsemigroup_le _

theorem inner_freeEvolD {β : ℝ → ℝ} (hβ : ∀ τ, 0 ≤ β τ) {s t : ℝ} (hst : s ≤ t)
    (f : B0010.XG) (ℓ : ℕ) :
    ⟪B0094.oscBasis ℓ, freeEvolD β t s f⟫_ℂ =
      ((Real.exp (-((∫ τ in s..t, β τ) * ℓ)) : ℝ) : ℂ) * ⟪B0094.oscBasis ℓ, f⟫_ℂ :=
  inner_Dsemigroup (intervalIntegral.integral_nonneg hst fun τ _ => hβ τ) f ℓ

/-- **H4, `PD` is bounded** (`eq:st18-t00069`, tex lines 1518–1524): for `ℓ = ⟪q†, ·⟫` with
`q† ∈ 𝒟(D)`, `f ↦ ℓ(D f) q` extends from `𝒟(D)` to the bounded operator `f ↦ ⟪D q†, f⟫ q`. -/
theorem exists_bounded_PD (q : B0010.XG) (qd : B0094.D.domain) :
    ∃ T : B0010.XG →L[ℂ] B0010.XG, ∀ f : B0094.D.domain,
      T f = ⟪(qd : B0010.XG), B0094.D f⟫_ℂ • q := by
  refine ⟨Infra.Dunford.rankOneProj (innerSL ℂ (B0094.D qd)) q, fun f => ?_⟩
  rw [Infra.Dunford.rankOneProj_apply, innerSL_apply_apply, B0094.D_symm qd f]

/-- **H4, `DP` is bounded**: for `q ∈ 𝒟(D)`, `f ↦ ℓ(f) D q` is the rank-one operator
`ℓ(·) Dq`. -/
theorem exists_bounded_DP (ℓ : B0010.XG →L[ℂ] ℂ) (q : B0094.D.domain) :
    ∃ T : B0010.XG →L[ℂ] B0010.XG, ∀ f : B0010.XG, T f = ℓ f • B0094.D q :=
  ⟨Infra.Dunford.rankOneProj ℓ (B0094.D q), fun _ => rfl⟩

/-! ## H5: Gaussian Sobolev norms and `X_{G,j}` -/

/-- **H5** (`sum_words_norm_deriv_sq`, tex lines 1856–1865, unit B0121): the sum over all
ordered products `∂_{w 0} ⋯ ∂_{w (k-1)}`, `k ≤ j`, of the squared `L²(G⁻¹ dy)` norms of the weak
derivatives equals `2π ∑_ℓ (∑_{k≤j} ∏_{m<k} (2 + ℓ + m/2)) |⟪e_ℓ, f⟫|²`
(`B0121.sum_words_gaussNormSq_eq`). -/
alias sum_words_norm_deriv_sq := B0121.sum_words_gaussNormSq_eq

/-- **H5, norm equivalence** (`eq:st18-t00100`, unit B0121): on angular-two functions, weak
derivatives in `L²(G⁻¹dy)` up to order `j` characterize `X_{G,j}`, with
`π/2^j ‖f‖²_{X_{G,j}} ≤ ∑_{|α|≤j} ‖∂^α f‖² ≤ 2π(j+1)(j+2)^j ‖f‖²_{X_{G,j}}`
(`B0121.graphNorm_equiv`). -/
alias graphNorm_equiv_gauss := B0121.graphNorm_equiv

/-! ## H6: `L₀` on `X_{G,j}` -/

/-- **H6** (`L0_bounded_XGj`, tex lines 1867–1871, unit B0122): `L₀` maps `X_{G,j}` boundedly
into itself, **given** the global elliptic estimate `B0122.GreenEllipticRegularity j`
(`B0122.L0_mem_XGj`). -/
alias L0_bounded_XGj := B0122.L0_mem_XGj

/-- **H6, transport part** (unconditional): multiplication by `Ω` is bounded on every
`X_{G,j}` (`B0122.omegaOp_mem_XGj`). -/
alias omega_bounded_XGj := B0122.omegaOp_mem_XGj

end UnforcedLeray.PlanarSpectral
