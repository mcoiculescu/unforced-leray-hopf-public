import UnforcedLeray.Short.PartIIIa.Sub.T20

/-!
# Part III-a, task `PartIII-a:T20/3`: the uniform nonzero-mode velocity bound (conditional)

Target (`Sub/T20.lean`): `CTE.NonzeroVelUniform`. For `m > 2` there is `C ≥ 0` such that for all
`c ≥ 1` and all `ω ∈ X_{m,c}` with zero circulation,
`‖K_c (ω_ne)‖₂ ≤ C ‖ω‖_{X_m}` (`B0581.velNe c (B0581.nonzeroPart c (B0581.ofX c m _ ω))`).
Source of record: `the November 2 reference manuscript`, lines 3236-3240
("zero mass gives `|f^(ξ)| ≤ |ξ| ∫ |y||f|` at low cylindrical frequencies. In Plancherel, the
`O(d)` horizontal frequencies of modulus at most one cancel the measure factor `d⁻¹`; the high
frequencies are bounded by `‖f‖₂`").

## Mathematical proof

Write `u = ofX ω ∈ L²(cell)`, `g_k = (modes u)_k ∈ L²(ℝ)` (`= √c · ω_k`), `κ_k = 2πk/c`,
`ζ = 2πξ`, `M = ∫_cell (|q|+|η|)|ω|`. Then
`‖K_c u‖² = ∑_k ‖bsModeCLM c k g_k‖²` (`norm_velNe_sq_eq_tsum`, proved here) and by Plancherel
`‖bsModeCLM c k g_k‖² = ∫ |𝓕 g_k(ξ)|² / (κ_k² + ζ²) dξ`.

* High modes `|κ_k| ≥ 1`: the symbol has modulus `≤ 1`, so the contribution is `≤ ‖g_k‖²`.
* Low modes `0 < |κ_k| < 1`: zero mass gives `|𝓕 g_k(ξ)| ≤ c^{-1/2} (|κ_k| + 2π|ξ|) M`
  (leaf `ZeroMassModeBound`), hence on `|ζ| ≤ 1` the integrand is `≤ 2M²/c`, and on `|ζ| > 1`
  the symbol has modulus `≤ 1`. So the contribution is `≤ ‖g_k‖² + 2M²/(πc)`
  (`perModeNormSq_of`, from the leaves `FourierL2Formulas` and `WeightedIntegralBound`).
* There are at most `c/π` low modes (`exists_lowModeSet`), so
  `‖K_c u‖² ≤ ∑_k ‖g_k‖² + (c/π)(2M²/(πc)) ≤ ‖ω‖² + M²` and `M ≤ K ‖ω‖_{X_m}`
  (leaf `FirstMomentBound`, uses `m > 2`), with `K` depending on `m` only. `C = 1 + K`.

## What is proved here (compiled, no placeholders)

`nonzeroVelUniform_of (hA : FirstMomentBound) (hC : L1Integrable) (hB : ZeroMassModeBound)
(hD1 : FourierL2Formulas) (hD2 : WeightedIntegralBound) : NonzeroVelUniform`, together with
`perModeNormSq_of`, `norm_velNe_sq_eq_tsum`, `norm_modes_sq_eq_tsum`, `summable_modes_sq` and
`exists_lowModeSet`.

## Leaf Props (each is a true statement with an elementary proof; dependencies in brackets)

* `WeightedHolder` (task `/1`): weighted Cauchy-Schwarz on the cell.
* `FirstMomentBound` (`/2`, from `WeightedHolder`), `L1Integrable` (`/3`, from `WeightedHolder`).
* `FourierModeFormula` (`/4`) and `ZeroMassPhaseBound` (`/5`): Fubini formula for the `η`-Fourier
  transform of the `k`-th horizontal mode, and the zero-mass estimate of the resulting integral.
* `ZeroMassModeBound` (`/6`, from `/4`, `/5` and `T20_3_NonzeroVelUniform/Bridge.lean`).
* `FourierL2Formulas` (`/7`): the `L²` Plancherel identities for one mode.
* `WeightedIntegralBound` (`/8`): an elementary integral estimate on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa

namespace CTE

namespace T20_3

/-- The first moment `M₁(ω) = ∫_cell (|q| + |η|) |ω|` of `ω ∈ X_{m,c}`. -/
def firstMoment (c m : ℝ) (ω : B0579.X c m) : ℝ :=
  ∫ x, (|x.1| + |x.2|) * |(ω : B0579.Plane → ℝ) x| ∂(B0581.cellVol c)

/-- **Weighted Cauchy-Schwarz on the cell** (task `PartIII-a:T20/3/1`; SP 3239-3240, "first
moment bounded by `‖ω‖_{X_m}`"). For `ω ∈ X_{m,c} = L²(cell, ⟨x⟩^{2m})`, `m ≥ 0`, and a measurable
`g ≥ 0` with `∫_cell g² ⟨x⟩^{-2m} < ∞` (`jb x = ⟨x⟩²`, so `jb^{-m} = ⟨x⟩^{-2m}`):
`∫_cell g |ω| ≤ (∫_cell g² jb^{-m})^{1/2} ‖ω‖_{X_m}`, and `g|ω|` is integrable on the cell. -/
def WeightedHolder : Prop :=
  ∀ (c m : ℝ) (ω : B0579.X c m) (g : B0579.Plane → ℝ), 0 ≤ m → (∀ x, 0 ≤ g x) → Measurable g →
    Integrable (fun x => g x ^ 2 * B0579.jb x ^ (-m)) (B0581.cellVol c) →
    Integrable (fun x => g x * |(ω : B0579.Plane → ℝ) x|) (B0581.cellVol c) ∧
    ∫ x, g x * |(ω : B0579.Plane → ℝ) x| ∂(B0581.cellVol c) ≤
      (∫ x, g x ^ 2 * B0579.jb x ^ (-m) ∂(B0581.cellVol c)) ^ (1 / 2 : ℝ) * ‖ω‖

/-- **First-moment bound** (task `/2`; SP 3239-3240; uses `m > 2`). There is `K = K_m ≥ 0`,
independent of `c > 0`, with `(|q|+|η|)|ω|` integrable on the cell and
`∫_cell (|q|+|η|)|ω| ≤ K ‖ω‖_{X_m}`. Proof: `WeightedHolder` with `g = |q| + |η|`, and
`∫_{ℝ²} (|q|+|η|)² jb^{-m} < ∞` iff `2(m-1) > 2`, i.e. `m > 2`; `cellVol ≤ volume`. -/
def FirstMomentBound : Prop :=
  ∀ m : ℝ, 2 < m → ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℝ), 0 < c → ∀ ω : B0579.X c m,
    Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) * |(ω : B0579.Plane → ℝ) x|)
        (B0581.cellVol c) ∧
      firstMoment c m ω ≤ K * ‖ω‖

/-- **`X_m ⊂ L¹(cell)`** (task `/3`; SP 3237-3239; `m > 1`). Proof: `WeightedHolder` with `g = 1`,
`∫_{ℝ²} jb^{-m} < ∞` for `m > 1`. -/
def L1Integrable : Prop :=
  ∀ m : ℝ, 1 < m → ∀ (c : ℝ), 0 < c → ∀ ω : B0579.X c m,
    Integrable (fun x : B0579.Plane => ((ω : B0579.Plane → ℝ) x)) (B0581.cellVol c)

/-- **Fubini formula for the `η`-Fourier transform of a horizontal mode** (task `/4`; SP 3236-3238).
For `u ∈ L¹(cell; ℂ)` the `k`-th mode integrand `g(η) = ∫_{qInt} (√c)⁻¹ e^{-iκ_k q} u(q,η) dq`
(`B0581.coeffIntegrand`; equal a.e. to `(modes u)_k`, `B0581.modes_apply_ae_integral`) is integrable
on `ℝ`, and `𝓕 g (ξ) = (√c)⁻¹ ∫_cell e^{-i(κ_k q + 2πξη)} u(q,η) d(q,η)` for every `ξ`
(`Real.fourierIntegral` = `∫ e^{-2πi η ξ} g(η) dη`; `cellVol = (μq c).prod volume`,
`B0581.cellVol_eq`). -/
def FourierModeFormula : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (k : ℤ) (u : B0579.Plane → ℂ), Integrable u (B0581.cellVol c) →
    Integrable (fun η : ℝ => ∫ q in B0581.qInt c, B0581.coeffIntegrand c k u (q, η)) volume ∧
    ∀ ξ : ℝ, 𝓕 (fun η : ℝ => ∫ q in B0581.qInt c, B0581.coeffIntegrand c k u (q, η)) ξ =
      (((Real.sqrt c)⁻¹ : ℝ) : ℂ) •
        ∫ x, Complex.exp (-(Complex.I * ((B0581.kappa c k * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ))) * u x
          ∂(B0581.cellVol c)

/-- **Zero-mass estimate** (task `/5`; SP 3236-3237, "zero mass gives `|f^(ξ)| ≤ |ξ| ∫|y||f|`").
For `u ∈ L¹(cell)` with `(|q|+|η|)|u| ∈ L¹` and `∫ u = 0`:
`|∫ e^{-i(κq + 2πξη)} u| ≤ (|κ| + 2π|ξ|) ∫ (|q|+|η|)|u|`. Proof: subtract `∫ u = 0`, use
`‖e^{-iA} - 1‖ ≤ |A|` (`Complex.norm_exp_I_mul_ofReal_sub_one_le`) and
`|κq + 2πξη| ≤ (|κ| + 2π|ξ|)(|q| + |η|)`. -/
def ZeroMassPhaseBound : Prop :=
  ∀ (c : ℝ) (κ ξ : ℝ) (u : B0579.Plane → ℂ), Integrable u (B0581.cellVol c) →
    Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) * ‖u x‖) (B0581.cellVol c) →
    ∫ x, u x ∂(B0581.cellVol c) = 0 →
    ‖∫ x, Complex.exp (-(Complex.I * ((κ * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ))) * u x
          ∂(B0581.cellVol c)‖ ≤
      (|κ| + 2 * π * |ξ|) * ∫ x, (|x.1| + |x.2|) * ‖u x‖ ∂(B0581.cellVol c)

/-- **Low-frequency Fourier bound of one horizontal mode** (task `/6`; SP 3236-3238). For
`U ∈ L²(cell; ℂ) ∩ L¹` with `(|q|+|η|)‖U‖ ∈ L¹` and zero mass, every mode `g_k = (modes U)_k`
satisfies `‖𝓕 g_k (ξ)‖ ≤ (√c)⁻¹ (|κ_k| + 2π|ξ|) ∫ (|q|+|η|)‖U‖` for a.e. `ξ`
(`𝓕` the `L²` Fourier transform). Proof: `g_k =ᵐ` the integrand of `FourierModeFormula`
(`B0581.modes_apply_ae_integral`), `g_k ∈ L¹ ∩ L²`, so the `L²` transform agrees a.e. with the
integral transform (`T20_3.fourier_toLp_ae_eq` in `T20_3_NonzeroVelUniform/Bridge.lean`); then
`FourierModeFormula` and `ZeroMassPhaseBound`. -/
def ZeroMassModeBound : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (U : Lp ℂ 2 (B0581.cellVol c)),
    Integrable (fun x : B0579.Plane => (U : B0579.Plane → ℂ) x) (B0581.cellVol c) →
    Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) * ‖(U : B0579.Plane → ℂ) x‖)
      (B0581.cellVol c) →
    ∫ x, (U : B0579.Plane → ℂ) x ∂(B0581.cellVol c) = 0 →
    ∀ k : ℤ, ∀ᵐ ξ : ℝ,
      ‖((𝓕 ((B0581.modes c U : B0581.ModeSeq ℂ) k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ≤
        (Real.sqrt c)⁻¹ * (|B0581.kappa c k| + 2 * π * |ξ|) *
          ∫ x, (|x.1| + |x.2|) * ‖(U : B0579.Plane → ℂ) x‖ ∂(B0581.cellVol c)

/-- **Plancherel formulas for one mode** (task `/7`; SP 3238-3240, "In Plancherel ..."). For
`k ≠ 0` and `h ∈ L²(ℝ; ℂ)`, with `φ(ξ) = ‖𝓕 h (ξ)‖²`: `φ` is integrable, `‖h‖² = ∫ φ`
(Plancherel, `Lp.fourierTransformₗᵢ` is an isometry), and
`‖bsModeCLM c k h‖² = ∫ φ(ξ) / (κ_k² + (2πξ)²)` (`bsModeCLM c k h = 𝓕⁻¹(bsSymbol c k · 𝓕 h)`,
`‖bsSymbol c k ξ‖² = 1/(κ_k² + (2πξ)²)` by `B0581.norm_sq_bsSym`, `fourier_bsModeCLM`). -/
def FourierL2Formulas : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (k : ℤ), k ≠ 0 → ∀ h : Lp ℂ 2 (volume : Measure ℝ),
    Integrable (fun ξ : ℝ => ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2) volume ∧
    ‖h‖ ^ 2 = ∫ ξ, ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 ∧
    ‖B0581.bsModeCLM c k h‖ ^ 2 =
      ∫ ξ, ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 /
        (B0581.kappa c k ^ 2 + (2 * π * ξ) ^ 2)

/-- **Low/high frequency split** (task `/8`; SP 3238-3240). For `κ ≠ 0`, `A ≥ 0` and an integrable
`φ ≥ 0` with `φ(ξ) ≤ A² (|κ| + 2π|ξ|)²` a.e.:
`∫ φ/(κ² + (2πξ)²) ≤ ∫ φ + (if |κ| < 1 then 2A²/π else 0)`. Proof: if `|κ| ≥ 1` the weight is
`≤ 1`. If `|κ| < 1`, on `|2πξ| ≤ 1` the integrand is `≤ A²(|κ|+|ζ|)²/(κ²+ζ²) ≤ 2A²`
(`(a+b)² ≤ 2(a²+b²)`) over a set of measure `1/π`; on `|2πξ| > 1` the weight is `≤ 1`. -/
def WeightedIntegralBound : Prop :=
  ∀ (κ A : ℝ) (φ : ℝ → ℝ), κ ≠ 0 → 0 ≤ A → Integrable φ volume → (∀ ξ, 0 ≤ φ ξ) →
    (∀ᵐ ξ : ℝ, φ ξ ≤ A ^ 2 * (|κ| + 2 * π * |ξ|) ^ 2) →
    ∫ ξ, φ ξ / (κ ^ 2 + (2 * π * ξ) ^ 2) ≤
      (∫ ξ, φ ξ) + (if |κ| < 1 then 2 * A ^ 2 / π else 0)

/-- **Per-mode energy bound** (glue; proved by `perModeNormSq_of` from `FourierL2Formulas` and
`WeightedIntegralBound`). -/
def PerModeNormSq : Prop :=
  ∀ (c : ℝ) [Fact (0 < c)] (k : ℤ), k ≠ 0 → ∀ (h : Lp ℂ 2 (volume : Measure ℝ)) (A : ℝ), 0 ≤ A →
    (∀ᵐ ξ : ℝ, ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ≤
        A * (|B0581.kappa c k| + 2 * π * |ξ|)) →
    ‖B0581.bsModeCLM c k h‖ ^ 2 ≤ ‖h‖ ^ 2 + (if |B0581.kappa c k| < 1 then 2 * A ^ 2 / π else 0)

/-- `PerModeNormSq` from the two Plancherel leaves. -/
theorem perModeNormSq_of (h₁ : FourierL2Formulas) (h₂ : WeightedIntegralBound) : PerModeNormSq := by
  intro c _ k hk h A hA hbd
  obtain ⟨hint, hnorm, hbs⟩ := h₁ c k hk h
  have hκ : B0581.kappa c k ≠ 0 := B0581.kappa_ne_zero (Fact.out) hk
  have hle := h₂ (B0581.kappa c k) A (fun ξ => ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2)
    hκ hA hint (fun ξ => sq_nonneg _) (by
      filter_upwards [hbd] with ξ hξ
      calc ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2
          ≤ (A * (|B0581.kappa c k| + 2 * π * |ξ|)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hξ 2
        _ = A ^ 2 * (|B0581.kappa c k| + 2 * π * |ξ|) ^ 2 := by ring)
  rw [hbs, hnorm]
  exact hle

/-- `‖K_c u‖² = ∑ₖ ‖(bs-multiplier of the k-th mode)‖²` (isometry of `synth`, `ℓ²` norm). -/
theorem norm_velNe_sq_eq_tsum (c : ℝ) [Fact (0 < c)] (u : Lp ℂ 2 (B0581.cellVol c)) :
    ‖B0581.velNe c u‖ ^ 2 =
      ∑' k : ℤ, ‖B0581.bsModeCLM c k ((B0581.modes c u : B0581.ModeSeq ℂ) k)‖ ^ 2 := by
  rw [B0581.velNe_apply, LinearIsometry.norm_map]
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (B0581.velModes c (B0581.modes c u))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  simp only [B0581.velModes_apply]

/-- The `ℓ²` norm of the mode sequence as a sum of squares. -/
theorem norm_modes_sq_eq_tsum (c : ℝ) [Fact (0 < c)] (u : Lp ℂ 2 (B0581.cellVol c)) :
    ‖B0581.modes c u‖ ^ 2 = ∑' k : ℤ, ‖(B0581.modes c u : B0581.ModeSeq ℂ) k‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (B0581.modes c u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h

/-- Summability of the squared mode norms. -/
theorem summable_modes_sq (c : ℝ) [Fact (0 < c)] (u : Lp ℂ 2 (B0581.cellVol c)) :
    Summable fun k : ℤ => ‖(B0581.modes c u : B0581.ModeSeq ℂ) k‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hs := (lp.memℓp (B0581.modes c u)).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  exact hs

/-- The low horizontal modes (`0 < |κ_k| < 1`) lie in a finite set of cardinality `≤ c/π`. -/
theorem exists_lowModeSet (c : ℝ) (hc : 0 < c) :
    ∃ S : Finset ℤ, (∀ k : ℤ, k ≠ 0 → |B0581.kappa c k| < 1 → k ∈ S) ∧
      (S.card : ℝ) ≤ c / π := by
  set N : ℤ := ⌊c / (2 * π)⌋ with hN
  have hpi : 0 < π := Real.pi_pos
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr (by positivity)
  have hNle : (N : ℝ) ≤ c / (2 * π) := Int.floor_le _
  refine ⟨(Finset.Icc (-N) N).erase 0, ?_, ?_⟩
  · intro k hk hκ
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨hk, ?_, ?_⟩
    all_goals
      have h1 : |B0581.kappa c k| = 2 * π * |(k : ℝ)| / c := by
        rw [B0581.kappa, abs_div, abs_mul, abs_of_pos hc, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      rw [h1, div_lt_one hc] at hκ
      have h2 : |(k : ℝ)| < c / (2 * π) := by
        rw [lt_div_iff₀ (by positivity)]; nlinarith
      have h3 : (k : ℝ) ≤ c / (2 * π) := (le_abs_self _).trans h2.le
      have h4 : (-k : ℝ) ≤ c / (2 * π) := (neg_le_abs _).trans h2.le
    · have : (-k : ℤ) ≤ N := by
        rw [hN]; exact Int.le_floor.mpr (by push_cast; exact h4)
      omega
    · exact Int.le_floor.mpr h3
  · have h0 : (0 : ℤ) ∈ Finset.Icc (-N) N := by rw [Finset.mem_Icc]; omega
    rw [Finset.card_erase_of_mem h0, Int.card_Icc]
    have : ((N + 1 - -N).toNat - 1 : ℕ) = (2 * N).toNat := by omega
    rw [this]
    have h5 : (((2 * N).toNat : ℕ) : ℝ) = 2 * (N : ℝ) := by
      have : ((2 * N).toNat : ℤ) = 2 * N := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [h5]
    calc 2 * (N : ℝ) ≤ 2 * (c / (2 * π)) := by linarith
      _ = c / π := by field_simp

/-- **`NonzeroVelUniform` from the five leaves** (SP 3236-3240). -/
theorem nonzeroVelUniform_of (hA : FirstMomentBound) (hC : L1Integrable)
    (hB : ZeroMassModeBound) (hD1 : FourierL2Formulas) (hD2 : WeightedIntegralBound) :
    NonzeroVelUniform := by
  intro m hm
  obtain ⟨K, hK0, hK⟩ := hA m hm
  refine ⟨1 + K, by positivity, ?_⟩
  intro c hcF hc1 ω hω
  have hc0 : 0 < c := hcF.out
  have hm0 : (0 : ℝ) ≤ m := by linarith
  rw [B0581.velNe_nonzeroPart]
  set U : Lp ℂ 2 (B0581.cellVol c) := B0581.ofX c m hm0 ω with hUdef
  have hU_ae : (U : B0579.Plane → ℂ) =ᵐ[B0581.cellVol c] fun x => (((ω : B0579.Plane → ℝ) x : ℝ) : ℂ) :=
    B0581.coeFn_ofX c m hm0 ω
  -- hypotheses of the leaf `hB`
  have hω1 := hC m (by linarith) c hc0 ω
  have hUint : Integrable (fun x : B0579.Plane => (U : B0579.Plane → ℂ) x) (B0581.cellVol c) :=
    (hω1.ofReal (𝕜 := ℂ)).congr hU_ae.symm
  obtain ⟨hAint, hAle⟩ := hK c hc0 ω
  have hnorm_ae : ∀ᵐ x ∂(B0581.cellVol c),
      (|x.1| + |x.2|) * ‖(U : B0579.Plane → ℂ) x‖ = (|x.1| + |x.2|) * |(ω : B0579.Plane → ℝ) x| := by
    filter_upwards [hU_ae] with x hx
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
  have hUw : Integrable (fun x : B0579.Plane => (|x.1| + |x.2|) * ‖(U : B0579.Plane → ℂ) x‖)
      (B0581.cellVol c) := hAint.congr (hnorm_ae.mono fun x hx => hx.symm)
  have hUmass : ∫ x, (U : B0579.Plane → ℂ) x ∂(B0581.cellVol c) = 0 := by
    rw [integral_congr_ae hU_ae, integral_complex_ofReal]
    have : ∫ x, (ω : B0579.Plane → ℝ) x ∂(B0581.cellVol c) = 0 := hω
    rw [this]; simp
  set M : ℝ := ∫ x, (|x.1| + |x.2|) * ‖(U : B0579.Plane → ℂ) x‖ ∂(B0581.cellVol c) with hM
  have hM_eq : M = firstMoment c m ω := by
    rw [hM, firstMoment]
    exact integral_congr_ae hnorm_ae
  have hM0 : 0 ≤ M := integral_nonneg (fun x => by positivity)
  have hMle : M ≤ K * ‖ω‖ := by rw [hM_eq]; exact hAle
  -- the per-mode estimate
  set A : ℝ := (Real.sqrt c)⁻¹ * M with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hper := perModeNormSq_of hD1 hD2
  obtain ⟨S, hS, hScard⟩ := exists_lowModeSet c hc0
  set B : ℝ := 2 * A ^ 2 / π with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ k : ℤ, ‖B0581.bsModeCLM c k ((B0581.modes c U : B0581.ModeSeq ℂ) k)‖ ^ 2 ≤
      ‖(B0581.modes c U : B0581.ModeSeq ℂ) k‖ ^ 2 + (if k ∈ S then B else 0) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [B0581.bsModeCLM_zero, ContinuousLinearMap.zero_apply, norm_zero]
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [this]
      split_ifs <;> positivity
    · have hbd : ∀ᵐ ξ : ℝ,
          ‖((𝓕 ((B0581.modes c U : B0581.ModeSeq ℂ) k) : Lp ℂ 2 (volume : Measure ℝ)) :
              ℝ → ℂ) ξ‖ ≤ A * (|B0581.kappa c k| + 2 * π * |ξ|) := by
        filter_upwards [hB c U hUint hUw hUmass k] with ξ hξ
        calc _ ≤ (Real.sqrt c)⁻¹ * (|B0581.kappa c k| + 2 * π * |ξ|) * M := hξ
          _ = A * (|B0581.kappa c k| + 2 * π * |ξ|) := by rw [hAdef]; ring
      have h1 := hper c k hk _ A hA0 hbd
      refine h1.trans (add_le_add le_rfl ?_)
      by_cases hκ : |B0581.kappa c k| < 1
      · rw [if_pos hκ, if_pos (hS k hk hκ)]
      · rw [if_neg hκ]; split_ifs <;> positivity
  have hs1 := summable_modes_sq c U
  have hs2 : Summable fun k : ℤ => (if k ∈ S then B else 0) :=
    summable_of_ne_finset_zero (s := S) (fun k hk => if_neg hk)
  have hsum_le : ∑' k : ℤ, ‖B0581.bsModeCLM c k ((B0581.modes c U : B0581.ModeSeq ℂ) k)‖ ^ 2 ≤
      ∑' k : ℤ, (‖(B0581.modes c U : B0581.ModeSeq ℂ) k‖ ^ 2 + (if k ∈ S then B else 0)) := by
    refine Summable.tsum_le_tsum hterm ?_ (hs1.add hs2)
    exact Summable.of_nonneg_of_le (fun k => by positivity) hterm (hs1.add hs2)
  rw [Summable.tsum_add hs1 hs2, ← norm_modes_sq_eq_tsum] at hsum_le
  have hite : ∑' k : ℤ, (if k ∈ S then B else 0) = (S.card : ℝ) * B := by
    rw [tsum_eq_sum (s := S) (fun k hk => if_neg hk)]
    rw [Finset.sum_congr rfl (fun k hk => if_pos hk), Finset.sum_const, nsmul_eq_mul]
  rw [hite] at hsum_le
  have hmodes : ‖B0581.modes c U‖ ≤ ‖ω‖ := (B0581.norm_modes_le c U).trans (B0581.norm_ofX_le c m hm0 ω)
  have hmodes2 : ‖B0581.modes c U‖ ^ 2 ≤ ‖ω‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmodes 2
  have hsq := norm_velNe_sq_eq_tsum c U
  -- `S.card * B ≤ M²`
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hAsq : A ^ 2 = M ^ 2 / c := by
    rw [hAdef, mul_pow, inv_pow, Real.sq_sqrt hc0.le]; ring
  have hcardB : (S.card : ℝ) * B ≤ M ^ 2 := by
    have h1 : (S.card : ℝ) * B ≤ (c / π) * B := mul_le_mul_of_nonneg_right hScard hB0
    have h2 : (c / π) * B = 2 * M ^ 2 / π ^ 2 := by
      rw [hBdef, hAsq]; field_simp
    have h3 : 2 * M ^ 2 / π ^ 2 ≤ M ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hπ2 : (2 : ℝ) ≤ π ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hπ2)]
    exact h1.trans (h2.le.trans h3)
  have hM2 : M ^ 2 ≤ K ^ 2 * ‖ω‖ ^ 2 := by
    calc M ^ 2 ≤ (K * ‖ω‖) ^ 2 := pow_le_pow_left₀ hM0 hMle 2
      _ = K ^ 2 * ‖ω‖ ^ 2 := by ring
  have hfin : ‖B0581.velNe c U‖ ^ 2 ≤ ((1 + K) * ‖ω‖) ^ 2 := by
    rw [hsq]
    have hω0 : 0 ≤ ‖ω‖ := norm_nonneg _
    nlinarith [mul_nonneg hK0 (sq_nonneg ‖ω‖)]
  have hnn : 0 ≤ (1 + K) * ‖ω‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp hfin

end T20_3

end CTE

end UnforcedLeray.Short.IIIa
