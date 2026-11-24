import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge
import UnforcedLeray.Short.PartIIb.Sub.G4
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Part III-a, `PartIII-a:T23/3/org`: the inlet coefficient bounds (reduction)

Source of record: `the November 2 reference manuscript`, lines 2711-2727
(`stress-short:coefficients`, "the compact-age inlet construction", "The finite inlet is absorbed
by `P_ν`"), with the inlet construction at 2347-2358 (the Gaussian angular-two eigenstream, its
periodization: "the actual periodized stream and every fixed derivative have exponential
transverse decay, with polynomial `c` costs") and the cutoff lift `e_ε = e₀ + εe₁`,
`e₀ = χ(-ψ_η, ψ_q)`, `e₁ = (0, (χ - 2sχ')ψ - χηψ_η)` (2356-2362).

## The objects

* the inlet column `E_i = p.inlet i = 𝒩_v e_i`, `e_i = p.inletProfile i =
  ringStreamProfile R (χ(s) ψ_i(q, η))` (`Cons/L2/BackgroundConcrete/Fields.lean`), with the
  age cutoff `χ = ageCutoff H`, `H = Σ/ν`, vanishing for `s ≥ H/2` (`ageCutoff_eq_zero`), and the
  frozen streams `ψ_0 = 2 Re P_c Δ⁻¹q`, `ψ_1 = -2 Im P_c Δ⁻¹q` (`Params.frozenStream`,
  `P_c Δ⁻¹ q = periodicStream q c`);
* the chart coefficient `v_i = s^{-1/2} E_i = chartCoeff p.R (p.inlet i)` equals `e_i` at `s > 0`
  (`chartCoeff_Nv`, `Sub/T23_1_org/Bridge.lean`).

## The quantifiers (statement defect of `StressInputs.InletCoeffBounds`)

`p.mode` (`q`) and `p.ageCut` (`Σ`) are free fields of `Params`, unconstrained by `BgRegime`; the
inlet is linear in `p.mode`, so `StressInputs.InletCoeffBounds` (constants chosen before `∀ p`) is
false for `p.mode := M • q`, `M → ∞`. The defect and its fix are the pending organizer item
`ORG:stmt/PartIII-a/ParamsWideQuantifiers` (insert `∀ Sig lam q, 0 < Sig → IsGrowingEigenpair lam
q →` before the constants and `p.ageCut = Sig → p.mode = q →` after `p.ν ≤ ν₀ →`, as in
`Short/PartII-b/Sub/G4.lean`). `InletCoeffBoundsSlow` below is exactly that corrected statement.

## The only analytic input

`IIb.FrozenStreamBounds` (`Short/PartII-b/Sub/G4.lean`, task `PartII-b:G4/2`, SP 2347-2358): the
periodized eigenstream `periodicStream q c` is `C^∞` and `‖D^j periodicStream q c (ξ, η)‖ ≤
C c^N e^{-κ|η|/c}` for `c ≥ 1`. It is reused here (j = 0, 1), not restated.

## Proved here (no sorry)

* `T23Inlet.deriv_smoothTransition_bound`, `T23Inlet.abs_mul_deriv_ageCutoff_le`: `|sχ'(s)| ≤ 2C`
  (the cutoff derivative has scale `1/H` and lives on `[H/4, H/2]`);
* `T23Inlet.inletProfile_eq_zero`: `e_i(s, ·) = 0` for `s > H/2` (compact age support);
* `T23Inlet.norm_ringStreamProfile_cut_le`: `|e| ≤ (3+4C)(1+|η|)(|ψ| + |Dψ|)` (item (b) of the
  organizer spec, from `ringStreamProfile_cutoff`);
* `T23Inlet.one_le_absorb`, `T23Inlet.sqrt_le_absorb`: for `0 ≤ s ≤ H/2 = Σ/(2ν)`, `0 < ν ≤ 1`:
  `1 ≤ (1+Σ)ν⁻¹(1+s)^{-3/4}` and `√s ≤ (1+Σ)ν⁻¹` (item (c): the inlet's age decay is absorbed);
* `T23Inlet.jap_pow_mul_exp_le`: `(1+η²)^n e^{-κ|η|/c} ≤ B c^{2n}` (exponential transverse decay
  gives every polynomial weight at polynomial `c` cost);
* `T23Inlet.weighted_cutProfile_le`, `T23Inlet.etaL2QSup_le_of_pointwise`;
* `inletCoeffBounds_of (hF : IIb.FrozenStreamBounds) : InletCoeffBoundsSlow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb UnforcedLeray.Blueprint

/-- **The finite inlet is absorbed by `P_ν`** (SP 2711-2727, with the inlet construction
2347-2362), at fixed slow data: a slow terminal age `Σ > 0` and the growing eigenpair `(λ, q)`
(G1), the constants depending on them. This is `StressInputs.InletCoeffBounds` with the binders of
`ORG:stmt/PartIII-a/ParamsWideQuantifiers` (`∀ Sig lam q, 0 < Sig → IsGrowingEigenpair lam q →`
before the constants, `p.ageCut = Sig → p.mode = q →` after `p.ν ≤ ν₀ →`). For each inlet column
`E_i`: `√s W|v_i| ≤ P_ν`, `√s W|v_i| ≤ P_ν√s` for `s ≤ 1`, and
`‖W v_i(s)‖_{L²_ηL^∞_q} ≤ P_ν(1+s)^{-3/4}` for every `s > 0`. -/
def InletCoeffBoundsSlow : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2,
      (∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
          C * (p.ν⁻¹) ^ k) ∧
      (∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 ≤ 1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
          C * (p.ν⁻¹) ^ k * Real.sqrt pt.1) ∧
      (∀ s : ℝ, 0 < s → etaL2QSup p.c mZ (chartCoeff p.R (p.inlet i)) s ≤
        ENNReal.ofReal (C * (p.ν⁻¹) ^ k * (1 + s) ^ (-3 / 4 : ℝ)))

namespace T23Inlet

/-! ## The age cutoff (SP 2356-2362; `Fields.lean` 150-170) -/

theorem deriv_smoothTransition_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq]
  simp

theorem deriv_smoothTransition_of_gt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [h.deriv_eq]
  simp

/-- The derivative of the smooth transition is bounded (continuous, supported in `[0, 1]`). -/
theorem deriv_smoothTransition_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have := hC x hx
    rwa [Real.norm_eq_abs] at this
  · have h0 : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.1 hx with h | h
      · exact deriv_smoothTransition_of_neg (not_le.1 h)
      · exact deriv_smoothTransition_of_gt (not_le.1 h)
    rw [h0, abs_zero]
    exact hC0

theorem abs_ageCutoff_le_one (H s : ℝ) : |ageCutoff H s| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2 - 4 * s / H)
  have h1 := Real.smoothTransition.le_one (2 - 4 * s / H)
  exact abs_le.2 ⟨by unfold ageCutoff; linarith, h1⟩

theorem deriv_ageCutoff {H : ℝ} (s : ℝ) :
    deriv (ageCutoff H) s = deriv Real.smoothTransition (2 - 4 * s / H) * (-(4 * 1 / H)) := by
  have hg : HasDerivAt (fun x : ℝ => 2 - 4 * x / H) (-(4 * 1 / H)) s :=
    (((hasDerivAt_id s).const_mul 4).div_const H).const_sub 2
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (2 - 4 * s / H)) (2 - 4 * s / H) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h := hst.comp s hg
  exact h.deriv

/-- **The cutoff derivative has scale `1/H`** (SP 2356-2362, `H = Σ/ν`): `|sχ'(s)| ≤ 2C` for
every `s`, since `χ'` lives on `H/4 ≤ s ≤ H/2`. -/
theorem abs_mul_deriv_ageCutoff_le {H Cst : ℝ} (hH : 0 < H)
    (hCst : ∀ x, |deriv Real.smoothTransition x| ≤ Cst) (s : ℝ) :
    |s * deriv (ageCutoff H) s| ≤ 2 * Cst := by
  have hCst0 : 0 ≤ Cst := (abs_nonneg _).trans (hCst 0)
  rw [deriv_ageCutoff]
  by_cases h0 : deriv Real.smoothTransition (2 - 4 * s / H) = 0
  · rw [h0, zero_mul, mul_zero, abs_zero]
    linarith
  · have hlo : 0 ≤ 2 - 4 * s / H := by
      by_contra h
      exact h0 (deriv_smoothTransition_of_neg (not_le.1 h))
    have hhi : 2 - 4 * s / H ≤ 1 := by
      by_contra h
      exact h0 (deriv_smoothTransition_of_gt (not_le.1 h))
    have h4 : 0 ≤ 4 * s / H := by linarith
    have hs : 0 ≤ s := by
      have h' : 0 ≤ 4 * s / H * H := mul_nonneg h4 hH.le
      rw [div_mul_cancel₀ _ hH.ne'] at h'
      linarith
    have hpos : 0 < 4 * 1 / H := div_pos (by norm_num) hH
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs, abs_of_pos hpos]
    calc s * (|deriv Real.smoothTransition (2 - 4 * s / H)| * (4 * 1 / H))
        = (4 * s / H) * |deriv Real.smoothTransition (2 - 4 * s / H)| := by ring
      _ ≤ 2 * Cst := mul_le_mul (by linarith) (hCst _) (abs_nonneg _) (by norm_num)

/-! ## Compact age support of the inlet (SP 2711-2716, "compact-age inlet construction") -/

/-- The inlet profile vanishes for ages `s > H/2` (the cutoff stream vanishes near such points). -/
theorem inletProfile_eq_zero (p : Params) (i : Fin 2) {m : ℝ × (ℝ × ℝ)} (hm : p.H / 2 < m.1) :
    p.inletProfile i m = 0 := by
  have hev : p.cutStream i =ᶠ[𝓝 m] fun _ => (0 : ℝ) := by
    have ho : IsOpen {n : ℝ × (ℝ × ℝ) | p.H / 2 < n.1} := isOpen_lt continuous_const continuous_fst
    filter_upwards [ho.mem_nhds hm] with n hn
    show ageCutoff p.H n.1 * p.frozenStream i n.2 = 0
    rw [ageCutoff_eq_zero p.H_pos (le_of_lt hn), zero_mul]
  have hd : fderiv ℝ (p.cutStream i) m = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  have h0 : p.cutStream i m = 0 := hev.eq_of_nhds
  show ringStreamProfile p.R (p.cutStream i) m = 0
  simp only [ringStreamProfile, Axi.dEta, Axi.dQ, Axi.dS, hd, h0, ContinuousLinearMap.zero_apply,
    neg_zero, zero_smul, mul_zero, sub_zero, add_zero, zero_add]

/-! ## The ring-stream chart bound (item (b); SP 2356-2362, `Stream.lean` 360-445) -/

theorem norm_smul_m0_add_smul_m1_le (a b : ℝ) : ‖a • m0 + b • m1‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, m0, m1, PiLp.norm_single, PiLp.norm_single,
    norm_one, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]

theorem abs_fderiv_apply_le {ψ : ℝ × ℝ → ℝ} (x : ℝ × ℝ) (a b : ℝ) (hab : ‖((a, b) : ℝ × ℝ)‖ ≤ 1) :
    |fderiv ℝ ψ x (a, b)| ≤ ‖fderiv ℝ ψ x‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ ψ x (a, b)‖ ≤ ‖fderiv ℝ ψ x‖ * ‖((a, b) : ℝ × ℝ)‖ :=
        (fderiv ℝ ψ x).le_opNorm _
    _ ≤ ‖fderiv ℝ ψ x‖ * 1 := mul_le_mul_of_nonneg_left hab (norm_nonneg _)
    _ = ‖fderiv ℝ ψ x‖ := mul_one _

/-- **The cut ring-stream profile is controlled by the stream and its gradient** (SP 2356-2362):
`|e_ε| ≤ (3+4C)(1+|η|)(|ψ| + |Dψ|)` for `e_ε = (−χψ_η, χψ_q + ε[(χ − 2sχ')ψ − χηψ_η])`,
`0 ≤ ε = R⁻¹ ≤ 1`, `|χ| ≤ 1`, `|sχ'| ≤ 2C`. -/
theorem norm_ringStreamProfile_cut_le {R H Cst : ℝ} (hR0 : 0 ≤ R⁻¹) (hR1 : R⁻¹ ≤ 1) (hH : 0 < H)
    (hCst : ∀ x, |deriv Real.smoothTransition x| ≤ Cst) {ψ : ℝ × ℝ → ℝ} {m : ℝ × (ℝ × ℝ)}
    (hψ : DifferentiableAt ℝ ψ m.2) :
    ‖ringStreamProfile R (fun n => ageCutoff H n.1 * ψ n.2) m‖ ≤
      (3 + 4 * Cst) * (1 + |m.2.2|) * (|ψ m.2| + ‖fderiv ℝ ψ m.2‖) := by
  have hχd : DifferentiableAt ℝ (ageCutoff H) m.1 :=
    (contDiff_ageCutoff H (n := 1)).differentiable one_ne_zero _
  rw [ringStreamProfile_cutoff R hχd hψ]
  have hCst0 : 0 ≤ Cst := (abs_nonneg _).trans (hCst 0)
  have hχ : |ageCutoff H m.1| ≤ 1 := abs_ageCutoff_le_one H m.1
  have hsχ : |m.1 * deriv (ageCutoff H) m.1| ≤ 2 * Cst := abs_mul_deriv_ageCutoff_le hH hCst m.1
  have hη : |fderiv ℝ ψ m.2 (0, 1)| ≤ ‖fderiv ℝ ψ m.2‖ :=
    abs_fderiv_apply_le m.2 0 1 (by simp [Prod.norm_def])
  have hq : |fderiv ℝ ψ m.2 (1, 0)| ≤ ‖fderiv ℝ ψ m.2‖ :=
    abs_fderiv_apply_le m.2 1 0 (by simp [Prod.norm_def])
  set χ := ageCutoff H m.1 with hχdef
  set χ' := deriv (ageCutoff H) m.1 with hχ'def
  set D := ‖fderiv ℝ ψ m.2‖ with hDdef
  set a := fderiv ℝ ψ m.2 (0, 1) with hadef
  set b := fderiv ℝ ψ m.2 (1, 0) with hbdef
  set y := ψ m.2 with hydef
  set η := m.2.2 with hηdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hη0 : 0 ≤ |η| := abs_nonneg _
  have hy0 : 0 ≤ |y| := abs_nonneg _
  have e1 : |-(χ * a)| ≤ D := by
    rw [abs_neg, abs_mul]
    calc |χ| * |a| ≤ 1 * |a| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
      _ ≤ D := by linarith
  have e2 : |χ * b| ≤ D := by
    rw [abs_mul]
    calc |χ| * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
      _ ≤ D := by linarith
  have e3 : |(χ - 2 * m.1 * χ') * y| ≤ (1 + 4 * Cst) * |y| := by
    rw [abs_mul]
    have : |χ - 2 * m.1 * χ'| ≤ 1 + 4 * Cst := by
      have h2 : 2 * m.1 * χ' = 2 * (m.1 * χ') := by ring
      rw [h2]
      calc |χ - 2 * (m.1 * χ')| ≤ |χ| + |2 * (m.1 * χ')| := abs_sub _ _
        _ = |χ| + 2 * |m.1 * χ'| := by rw [abs_mul, abs_two]
        _ ≤ 1 + 4 * Cst := by linarith
    exact mul_le_mul_of_nonneg_right this hy0
  have e4 : |χ * η * a| ≤ |η| * D := by
    rw [abs_mul, abs_mul]
    calc |χ| * |η| * |a| ≤ 1 * |η| * D :=
          mul_le_mul (mul_le_mul_of_nonneg_right hχ hη0) hη (abs_nonneg _) (by positivity)
      _ = |η| * D := by ring
  have e5 : |R⁻¹ * ((χ - 2 * m.1 * χ') * y - χ * η * a)| ≤
      (1 + 4 * Cst) * |y| + |η| * D := by
    rw [abs_mul, abs_of_nonneg hR0]
    have hs : |(χ - 2 * m.1 * χ') * y - χ * η * a| ≤ (1 + 4 * Cst) * |y| + |η| * D :=
      (abs_sub _ _).trans (add_le_add e3 e4)
    have hnn : 0 ≤ |(χ - 2 * m.1 * χ') * y - χ * η * a| := abs_nonneg _
    calc R⁻¹ * |(χ - 2 * m.1 * χ') * y - χ * η * a|
        ≤ 1 * |(χ - 2 * m.1 * χ') * y - χ * η * a| := mul_le_mul_of_nonneg_right hR1 hnn
      _ ≤ (1 + 4 * Cst) * |y| + |η| * D := by linarith
  refine (norm_smul_m0_add_smul_m1_le _ _).trans ?_
  have e6 : |χ * b + R⁻¹ * ((χ - 2 * m.1 * χ') * y - χ * η * a)| ≤
      D + ((1 + 4 * Cst) * |y| + |η| * D) := (abs_add_le _ _).trans (add_le_add e2 e5)
  nlinarith [mul_nonneg hCst0 hD0, mul_nonneg hη0 hy0, mul_nonneg hη0 hD0,
    mul_nonneg (mul_nonneg hCst0 hη0) hy0, mul_nonneg (mul_nonneg hCst0 hη0) hD0,
    mul_nonneg hCst0 hy0]

/-! ## The frozen streams are real parts of the periodized eigenstream (`Fields.lean` 190-200) -/

theorem frozenStream_eq (p : Params) (i : Fin 2) : ∃ (a : ℝ) (L : ℂ →L[ℝ] ℝ), |a| ≤ 2 ∧ ‖L‖ ≤ 1 ∧
    p.frozenStream i = fun x => a * L (periodicStream p.mode p.c x) := by
  fin_cases i
  · refine ⟨2, Complex.reCLM, by norm_num, Complex.reCLM_norm.le, ?_⟩
    funext x
    simp [Params.frozenStream]
  · refine ⟨-2, Complex.imCLM, by norm_num, Complex.imCLM_norm.le, ?_⟩
    funext x
    simp [Params.frozenStream]

theorem scalar_comp_bounds {P : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hP : DifferentiableAt ℝ P x) (a : ℝ)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    DifferentiableAt ℝ (fun y => a * L (P y)) x ∧ |a * L (P x)| ≤ |a| * ‖P x‖ ∧
      ‖fderiv ℝ (fun y => a * L (P y)) x‖ ≤ |a| * ‖fderiv ℝ P x‖ := by
  have hd : HasFDerivAt (fun y => a * L (P y)) (a • L.comp (fderiv ℝ P x)) x :=
    (L.hasFDerivAt.comp x hP.hasFDerivAt).const_mul a
  refine ⟨hd.differentiableAt, ?_, ?_⟩
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    rw [← Real.norm_eq_abs]
    calc ‖L (P x)‖ ≤ ‖L‖ * ‖P x‖ := L.le_opNorm _
      _ ≤ 1 * ‖P x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ = ‖P x‖ := one_mul _
  · rw [hd.fderiv, norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    calc ‖L.comp (fderiv ℝ P x)‖ ≤ ‖L‖ * ‖fderiv ℝ P x‖ := L.opNorm_comp_le _
      _ ≤ 1 * ‖fderiv ℝ P x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ = ‖fderiv ℝ P x‖ := one_mul _

/-! ## Age absorption (item (c); SP 2726: the inlet lives at ages `s ≤ H/2 = Σ/(2ν)`) -/

theorem one_add_le_absorb {ν Sig s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hSig : 0 < Sig)
    (hs : s ≤ Sig / ν / 2) : 1 + s ≤ (1 + Sig) * ν⁻¹ := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have h2 : Sig / ν / 2 ≤ Sig * ν⁻¹ := by
    rw [div_eq_mul_inv Sig ν]
    have : 0 ≤ Sig * ν⁻¹ := mul_nonneg hSig.le (inv_nonneg.2 hν.le)
    linarith
  nlinarith

/-- **The inlet's age decay is absorbed by `P_ν`** (SP 2726): for `0 ≤ s ≤ H/2 = Σ/(2ν)` and
`0 < ν ≤ 1`, `1 ≤ (1+Σ)ν⁻¹(1+s)^{-3/4}` (equivalently `(1+s)^{-3/4} ≥ (1+Σ)⁻¹ν`). -/
theorem one_le_absorb {ν Sig s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hSig : 0 < Sig) (hs0 : 0 ≤ s)
    (hs : s ≤ Sig / ν / 2) : 1 ≤ (1 + Sig) * ν⁻¹ * (1 + s) ^ (-3 / 4 : ℝ) := by
  have hX := one_add_le_absorb hν hν1 hSig hs
  have h1s : 0 < 1 + s := by linarith
  have h1 : (1 : ℝ) ≤ 1 + s := by linarith
  have hpow : (1 + s) ^ (3 / 4 : ℝ) ≤ 1 + s := by
    calc (1 + s) ^ (3 / 4 : ℝ) ≤ (1 + s) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = 1 + s := Real.rpow_one _
  have hpos : 0 < (1 + s) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos h1s _
  have hneg : (1 + s) ^ (-3 / 4 : ℝ) = ((1 + s) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [show (-3 / 4 : ℝ) = -(3 / 4) by norm_num, Real.rpow_neg h1s.le]
  rw [hneg, le_mul_inv_iff₀ hpos, one_mul]
  linarith

theorem sqrt_le_absorb {ν Sig s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hSig : 0 < Sig) (hs0 : 0 ≤ s)
    (hs : s ≤ Sig / ν / 2) : Real.sqrt s ≤ (1 + Sig) * ν⁻¹ := by
  have hX := one_add_le_absorb hν hν1 hSig hs
  have h1 : 1 ≤ (1 + Sig) * ν⁻¹ := by linarith
  have hsq : s ≤ ((1 + Sig) * ν⁻¹) ^ 2 := by nlinarith
  calc Real.sqrt s ≤ Real.sqrt (((1 + Sig) * ν⁻¹) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (1 + Sig) * ν⁻¹ := Real.sqrt_sq (by linarith)

/-! ## Transverse weights (SP 2696, 2717-2730) -/

theorem transWeight_nonneg' (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) : 0 ≤ transWeight mZ p := by
  unfold transWeight
  positivity

/-- `W ≤ (1+η²)^n` for `n ≥ ⌈m_Z/2⌉`, `m_Z ≥ 0`, `s ≥ 0`. -/
theorem transWeight_le_pow {mZ s : ℝ} {n : ℕ} (hmZ : 0 ≤ mZ) (hn : ⌈mZ / 2⌉₊ ≤ n) (hs : 0 ≤ s)
    (q η : ℝ) : transWeight mZ (s, (q, η)) ≤ (1 + η ^ 2) ^ n := by
  unfold transWeight
  show (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2) ≤ (1 + η ^ 2) ^ n
  have h1s : 0 < 1 + s := by linarith
  have hx : (η / Real.sqrt (1 + s)) ^ 2 = η ^ 2 / (1 + s) := by
    rw [div_pow, Real.sq_sqrt h1s.le]
  rw [hx]
  have hx0 : 0 ≤ η ^ 2 / (1 + s) := div_nonneg (sq_nonneg η) h1s.le
  have hle : 1 + η ^ 2 / (1 + s) ≤ 1 + η ^ 2 := by
    have := div_le_self (sq_nonneg η) (show (1 : ℝ) ≤ 1 + s by linarith)
    linarith
  have hb1 : 1 ≤ 1 + η ^ 2 := by nlinarith [sq_nonneg η]
  calc (1 + η ^ 2 / (1 + s)) ^ (mZ / 2) ≤ (1 + η ^ 2) ^ (mZ / 2) :=
        Real.rpow_le_rpow (by linarith) hle (by linarith)
    _ ≤ (1 + η ^ 2) ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 ((Nat.le_ceil _).trans (by exact_mod_cast hn))
    _ = (1 + η ^ 2) ^ n := Real.rpow_natCast _ _

/-- **Exponential transverse decay gives every polynomial weight at polynomial `c` cost**
(SP 2353-2355): `(1+η²)^n e^{-κ|η|/c} ≤ B c^{2n}` for `c ≥ 1`. -/
theorem jap_pow_mul_exp_le (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, 1 ≤ c → ∀ η : ℝ,
      (1 + η ^ 2) ^ n * Real.exp (-(κ * |η| / c)) ≤ B * c ^ (2 * n) := by
  refine ⟨2 ^ n * (1 + ((2 * n).factorial : ℝ) / κ ^ (2 * n)),
    mul_nonneg (by positivity) (add_nonneg zero_le_one (div_nonneg (by positivity)
      (pow_nonneg hκ.le _))), ?_⟩
  intro c hc η
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  set t := κ * |η| / c with ht
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hκ.le (abs_nonneg _)) hc0.le
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have h1 : (1 + η ^ 2) ^ n ≤ 2 ^ n * (1 + (η ^ 2) ^ n) := by
    have hp0 : 0 ≤ (η ^ 2) ^ n := by positivity
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rcases le_total (η ^ 2) 1 with h | h
    · calc (1 + η ^ 2) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
        _ ≤ 2 ^ n * (1 + (η ^ 2) ^ n) := by nlinarith
    · calc (1 + η ^ 2) ^ n ≤ (2 * η ^ 2) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
        _ = 2 ^ n * (η ^ 2) ^ n := mul_pow _ _ _
        _ ≤ 2 ^ n * (1 + (η ^ 2) ^ n) := by nlinarith
  have hfac : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
  have hte : t ^ (2 * n) * Real.exp (-t) ≤ (2 * n).factorial := by
    have hf := Real.pow_div_factorial_le_exp t ht0 (2 * n)
    have hf' : t ^ (2 * n) ≤ Real.exp t * (2 * n).factorial := (div_le_iff₀ hfac).1 hf
    calc t ^ (2 * n) * Real.exp (-t) ≤ (Real.exp t * (2 * n).factorial) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hf' he0.le
      _ = (2 * n).factorial := by
          rw [mul_comm (Real.exp t), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
            mul_one]
  have heq : (η ^ 2) ^ n = t ^ (2 * n) * (c / κ) ^ (2 * n) := by
    have htc : t * (c / κ) = |η| := by
      rw [ht]
      field_simp [hκ.ne', hc0.ne']
    rw [← mul_pow, htc, pow_mul, sq_abs]
  have h2 : (η ^ 2) ^ n * Real.exp (-t) ≤
      ((2 * n).factorial : ℝ) / κ ^ (2 * n) * c ^ (2 * n) := by
    rw [heq]
    have hck : (0 : ℝ) ≤ (c / κ) ^ (2 * n) := pow_nonneg (div_nonneg hc0.le hκ.le) _
    calc t ^ (2 * n) * (c / κ) ^ (2 * n) * Real.exp (-t)
        = (t ^ (2 * n) * Real.exp (-t)) * (c / κ) ^ (2 * n) := by ring
      _ ≤ (2 * n).factorial * (c / κ) ^ (2 * n) := mul_le_mul_of_nonneg_right hte hck
      _ = ((2 * n).factorial : ℝ) / κ ^ (2 * n) * c ^ (2 * n) := by rw [div_pow]; ring
  have hc1 : 1 ≤ c ^ (2 * n) := one_le_pow₀ hc
  have hF0 : 0 ≤ ((2 * n).factorial : ℝ) / κ ^ (2 * n) :=
    div_nonneg (by positivity) (pow_nonneg hκ.le _)
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  calc (1 + η ^ 2) ^ n * Real.exp (-t)
      ≤ 2 ^ n * (1 + (η ^ 2) ^ n) * Real.exp (-t) := mul_le_mul_of_nonneg_right h1 he0.le
    _ = 2 ^ n * (Real.exp (-t) + (η ^ 2) ^ n * Real.exp (-t)) := by ring
    _ ≤ 2 ^ n * (c ^ (2 * n) + ((2 * n).factorial : ℝ) / κ ^ (2 * n) * c ^ (2 * n)) := by
        refine mul_le_mul_of_nonneg_left ?_ h2n
        linarith
    _ = 2 ^ n * (1 + ((2 * n).factorial : ℝ) / κ ^ (2 * n)) * c ^ (2 * n) := by ring

/-- **The weighted inlet profile** (SP 2716-2727): with the periodized stream `P` and its
gradient bounded by `A e^{-κ|η|/c}` and `ψ = a L∘P` (`|a| ≤ 2`, `‖L‖ ≤ 1`), the weighted cut
ring-stream profile satisfies `W|e| ≤ 4(3+4C) A B' (1+η²)⁻¹` at every age `s ≥ 0`, where
`(1+η²)^{n+2} e^{-κ|η|/c} ≤ B'`. -/
theorem weighted_cutProfile_le {R H Cst c κ A B' mZ : ℝ} {n0 : ℕ} (hmZ : 0 ≤ mZ)
    (hn0 : ⌈mZ / 2⌉₊ ≤ n0) (hR0 : 0 ≤ R⁻¹) (hR1 : R⁻¹ ≤ 1) (hH : 0 < H)
    (hCst : ∀ x, |deriv Real.smoothTransition x| ≤ Cst) {P : ℝ × ℝ → ℂ}
    (hPd : Differentiable ℝ P)
    (hPb : ∀ x : ℝ × ℝ, ‖P x‖ + ‖fderiv ℝ P x‖ ≤ A * Real.exp (-(κ * |x.2| / c)))
    (hB : ∀ η : ℝ, (1 + η ^ 2) ^ (n0 + 2) * Real.exp (-(κ * |η| / c)) ≤ B')
    (a : ℝ) (L : ℂ →L[ℝ] ℝ) (ha : |a| ≤ 2) (hL : ‖L‖ ≤ 1) {s : ℝ} (hs : 0 ≤ s) (q η : ℝ) :
    transWeight mZ (s, (q, η)) *
        ‖ringStreamProfile R (fun n => ageCutoff H n.1 * (a * L (P n.2))) (s, (q, η))‖ ≤
      4 * (3 + 4 * Cst) * A * B' * (1 + η ^ 2)⁻¹ := by
  have hCst0 : 0 ≤ Cst := (abs_nonneg _).trans (hCst 0)
  obtain ⟨hψd, hψ0, hψ1⟩ := scalar_comp_bounds (hPd (q, η)) a L hL
  have hb := norm_ringStreamProfile_cut_le (ψ := fun y => a * L (P y)) (m := (s, (q, η)))
    hR0 hR1 hH hCst hψd
  simp only at hb
  set E := Real.exp (-(κ * |η| / c)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hPx := hPb (q, η)
  simp only at hPx
  have hA0 : 0 ≤ A := by
    have : 0 ≤ A * E := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hPx
    exact nonneg_of_mul_nonneg_left this hE0
  have hψs : |a * L (P (q, η))| + ‖fderiv ℝ (fun y => a * L (P y)) (q, η)‖ ≤ 2 * (A * E) := by
    have h2 : |a| * ‖P (q, η)‖ + |a| * ‖fderiv ℝ P (q, η)‖ ≤ 2 * (A * E) := by
      rw [← mul_add]
      exact mul_le_mul ha hPx (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    linarith
  have hW := transWeight_le_pow hmZ hn0 hs q η
  have hW0 := transWeight_nonneg' mZ (s, (q, η))
  have hJ1 : 1 ≤ 1 + η ^ 2 := by nlinarith [sq_nonneg η]
  have hJ0 : 0 < 1 + η ^ 2 := by linarith
  have h1η : 1 + |η| ≤ 2 * (1 + η ^ 2) := by
    nlinarith [sq_nonneg (|η| - 1), sq_abs η, abs_nonneg η]
  have hK0 : 0 ≤ 3 + 4 * Cst := by linarith
  have hBE := hB η
  have hnorm0 : 0 ≤ ‖ringStreamProfile R (fun n => ageCutoff H n.1 * (a * L (P n.2)))
      (s, (q, η))‖ := norm_nonneg _
  have hpowpos : 0 ≤ (1 + η ^ 2) ^ n0 := by positivity
  calc transWeight mZ (s, (q, η)) *
        ‖ringStreamProfile R (fun n => ageCutoff H n.1 * (a * L (P n.2))) (s, (q, η))‖
      ≤ (1 + η ^ 2) ^ n0 * ((3 + 4 * Cst) * (1 + |η|) *
          (|a * L (P (q, η))| + ‖fderiv ℝ (fun y => a * L (P y)) (q, η)‖)) :=
        mul_le_mul hW hb hnorm0 hpowpos
    _ ≤ (1 + η ^ 2) ^ n0 * ((3 + 4 * Cst) * (2 * (1 + η ^ 2)) * (2 * (A * E))) := by
        refine mul_le_mul_of_nonneg_left ?_ hpowpos
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1η hK0) hψs
          (add_nonneg (abs_nonneg _) (norm_nonneg _)) (mul_nonneg hK0 (by positivity))
    _ = 4 * (3 + 4 * Cst) * A * ((1 + η ^ 2) ^ (n0 + 2) * E) * (1 + η ^ 2)⁻¹ := by
        have hpw : (1 + η ^ 2) ^ (n0 + 2) * (1 + η ^ 2)⁻¹ = (1 + η ^ 2) ^ n0 * (1 + η ^ 2) := by
          rw [pow_succ, mul_assoc, mul_inv_cancel₀ hJ0.ne', mul_one, pow_succ]
        rw [show 4 * (3 + 4 * Cst) * A * ((1 + η ^ 2) ^ (n0 + 2) * E) * (1 + η ^ 2)⁻¹ =
          4 * (3 + 4 * Cst) * A * E * ((1 + η ^ 2) ^ (n0 + 2) * (1 + η ^ 2)⁻¹) by ring, hpw]
        ring
    _ ≤ 4 * (3 + 4 * Cst) * A * B' * (1 + η ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hJ0.le)
        exact mul_le_mul_of_nonneg_left hBE (mul_nonneg (mul_nonneg (by norm_num) hK0) hA0)

/-- The `L²_η L^∞_q` norm from a pointwise bound `W|v| ≤ D(1+η²)⁻¹`:
`‖W v(s)‖_{L²_ηL^∞_q} ≤ D√π`. -/
theorem etaL2QSup_le_of_pointwise {c mZ D s : ℝ} {v : ℝ × (ℝ × ℝ) → Merid} (hD : 0 ≤ D)
    (h : ∀ q η : ℝ, transWeight mZ (s, (q, η)) * ‖v (s, (q, η))‖ ≤ D * (1 + η ^ 2)⁻¹) :
    etaL2QSup c mZ v s ≤ ENNReal.ofReal (D * Real.sqrt Real.pi) := by
  have hpt : ∀ η q : ℝ, ENNReal.ofReal (transWeight mZ (s, (q, η))) * ‖v (s, (q, η))‖ₑ ≤
      ENNReal.ofReal (D * (1 + η ^ 2)⁻¹) := by
    intro η q
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (transWeight_nonneg' _ _)]
    exact ENNReal.ofReal_le_ofReal (h q η)
  have hess : ∀ η : ℝ, essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
      ‖v (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2))) ≤
        ENNReal.ofReal (D * (1 + η ^ 2)⁻¹) := fun η =>
    essSup_le_of_ae_le _ (Eventually.of_forall fun q => hpt η q)
  have hsq : ∀ η : ℝ, ENNReal.ofReal (D * (1 + η ^ 2)⁻¹) ^ (2 : ℝ) ≤
      ENNReal.ofReal (D ^ 2) * ENNReal.ofReal ((1 + η ^ 2)⁻¹) := by
    intro η
    have hJ1 : 1 ≤ 1 + η ^ 2 := by nlinarith [sq_nonneg η]
    have hi0 : 0 ≤ (1 + η ^ 2)⁻¹ := inv_nonneg.2 (by linarith)
    have hi1 : (1 + η ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hJ1
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hD hi0) (by norm_num),
      ← ENNReal.ofReal_mul (sq_nonneg D)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_two, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg D)
    nlinarith
  have hint : ∫⁻ η : ℝ, ENNReal.ofReal (D ^ 2) * ENNReal.ofReal ((1 + η ^ 2)⁻¹) =
      ENNReal.ofReal (D ^ 2 * Real.pi) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
        (Eventually.of_forall fun η => by positivity),
      integral_univ_inv_one_add_sq, ← ENNReal.ofReal_mul (sq_nonneg D)]
  have hmono : etaL2QSup c mZ v s ≤ ENNReal.ofReal (D ^ 2 * Real.pi) ^ (1 / 2 : ℝ) := by
    unfold etaL2QSup
    rw [← hint]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    apply lintegral_mono
    intro η
    exact (ENNReal.rpow_le_rpow (hess η) (by norm_num)).trans (hsq η)
  refine hmono.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]

end T23Inlet

open T23Inlet in
/-- **`PartIII-a:T23/3`, conditional form** (SP 2711-2727 with 2347-2362): the exponential
transverse decay of the periodized eigenstream (`IIb.FrozenStreamBounds`, SP 2353-2355) and the
compact-age cutoff lift give the inlet coefficient bounds at fixed slow data `(Σ, λ, q)`. -/
theorem inletCoeffBounds_of (hF : FrozenStreamBounds) : InletCoeffBoundsSlow := by
  intro dm dp hdm mZ hmZ Sig lam q hSig hq
  have hmZ0 : 0 ≤ mZ := by linarith
  obtain ⟨C0, κ0, N0, hC0, hκ0, h0⟩ := hF lam q hq 0
  obtain ⟨C1, κ1, N1, hC1, hκ1, h1⟩ := hF lam q hq 1
  obtain ⟨Cst, hCst0, hCst⟩ := deriv_smoothTransition_bound
  set n0 := ⌈mZ / 2⌉₊ with hn0
  set κ := min κ0 κ1 with hκdef
  have hκ : 0 < κ := lt_min hκ0 hκ1
  obtain ⟨B, hB0, hB⟩ := jap_pow_mul_exp_le (n0 + 2) hκ
  set M := 4 * (3 + 4 * Cst) * (C0 + C1) * B with hMdef
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hB0
  set k0 := N0 + N1 + 2 * (n0 + 2) with hk0def
  have hπ0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  refine ⟨M * (1 + Sig) * (1 + Real.sqrt Real.pi), 2 * k0 + 1, 1, one_pos, ?_⟩
  intro p d hreg hν hSigp hqp i
  subst hSigp hqp
  have hν0 : 0 < p.ν := p.ν_pos
  have hε1 : p.ε ≤ 1 := by
    have hd : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg hd.le hν0.le)
  have hRinv : p.R⁻¹ = p.ε := by rw [Params.R, inv_inv]
  have hR0 : 0 ≤ p.R⁻¹ := by rw [hRinv]; exact p.ε_pos.le
  have hR1 : p.R⁻¹ ≤ 1 := by rw [hRinv]; exact hε1
  have hνi : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hν0).2 hν
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq]
    exact (one_le_inv₀ (pow_pos hν0 2)).2 (pow_le_one₀ hν0.le hν)
  have hcpow : ∀ k : ℕ, p.c ^ k = p.ν⁻¹ ^ (2 * k) := by
    intro k
    rw [hreg.c_eq, ← inv_pow, ← pow_mul]
  -- the periodized eigenstream at the level
  set P := periodicStream p.mode p.c with hPdef
  obtain ⟨hPs, hP0⟩ := h0 p.c hc1
  obtain ⟨-, hP1⟩ := h1 p.c hc1
  have hPd : Differentiable ℝ P := hPs.differentiable (by simp)
  set A := (C0 + C1) * p.c ^ (N0 + N1) with hAdef
  have hPb : ∀ x : ℝ × ℝ, ‖P x‖ + ‖fderiv ℝ P x‖ ≤ A * Real.exp (-(κ * |x.2| / p.c)) := by
    intro x
    have e0 := hP0 x
    have e1 := hP1 x
    rw [norm_iteratedFDeriv_zero] at e0
    rw [norm_iteratedFDeriv_one] at e1
    have hc0 : 0 < p.c := lt_of_lt_of_le one_pos hc1
    have hexp : ∀ κ' : ℝ, κ ≤ κ' →
        Real.exp (-(κ' * |x.2| / p.c)) ≤ Real.exp (-(κ * |x.2| / p.c)) := by
      intro κ' hκ'
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ hc0.le
      exact mul_le_mul_of_nonneg_right hκ' (abs_nonneg _)
    have hp0 : p.c ^ N0 ≤ p.c ^ (N0 + N1) := pow_le_pow_right₀ hc1 (Nat.le_add_right _ _)
    have hp1 : p.c ^ N1 ≤ p.c ^ (N0 + N1) := pow_le_pow_right₀ hc1 (Nat.le_add_left _ _)
    have hE0 : 0 ≤ Real.exp (-(κ * |x.2| / p.c)) := (Real.exp_pos _).le
    have f0 : C0 * p.c ^ N0 * Real.exp (-(κ0 * |x.2| / p.c)) ≤
        C0 * p.c ^ (N0 + N1) * Real.exp (-(κ * |x.2| / p.c)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp0 hC0.le) (hexp κ0 (min_le_left _ _))
        (Real.exp_pos _).le (mul_nonneg hC0.le (pow_nonneg hc0.le _))
    have f1 : C1 * p.c ^ N1 * Real.exp (-(κ1 * |x.2| / p.c)) ≤
        C1 * p.c ^ (N0 + N1) * Real.exp (-(κ * |x.2| / p.c)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp1 hC1.le) (hexp κ1 (min_le_right _ _))
        (Real.exp_pos _).le (mul_nonneg hC1.le (pow_nonneg hc0.le _))
    calc ‖P x‖ + ‖fderiv ℝ P x‖
        ≤ C0 * p.c ^ (N0 + N1) * Real.exp (-(κ * |x.2| / p.c)) +
          C1 * p.c ^ (N0 + N1) * Real.exp (-(κ * |x.2| / p.c)) :=
          add_le_add (e0.trans f0) (e1.trans f1)
      _ = A * Real.exp (-(κ * |x.2| / p.c)) := by rw [hAdef]; ring
  -- the frozen stream and the inlet profile
  obtain ⟨a, L, ha, hL, hfz⟩ := frozenStream_eq p i
  have hprof : ∀ m : ℝ × (ℝ × ℝ), p.inletProfile i m =
      ringStreamProfile p.R (fun n => ageCutoff p.H n.1 * (a * L (P n.2))) m := by
    intro m
    show ringStreamProfile p.R (fun n => ageCutoff p.H n.1 * p.frozenStream i n.2) m = _
    rw [hfz]
  have hcoef : ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 →
      chartCoeff p.R (p.inlet i) pt = p.inletProfile i pt := fun pt hs =>
    chartCoeff_Nv p.R_pos (p.inletProfile i) hs
  -- the core pointwise bound
  have hνinv0 : 0 ≤ p.ν⁻¹ := inv_nonneg.2 hν0.le
  set G := M * p.ν⁻¹ ^ (2 * k0) with hGdef
  have hG0 : 0 ≤ G := mul_nonneg hM0 (pow_nonneg hνinv0 _)
  have hcore : ∀ s : ℝ, 0 < s → ∀ q' η : ℝ,
      transWeight mZ (s, (q', η)) * ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖ ≤
        G * (1 + η ^ 2)⁻¹ := by
    intro s hs q' η
    rw [hcoef (s, (q', η)) hs, hprof]
    have hBc : ∀ η' : ℝ, (1 + η' ^ 2) ^ (n0 + 2) * Real.exp (-(κ * |η'| / p.c)) ≤
        B * p.c ^ (2 * (n0 + 2)) := fun η' => hB p.c hc1 η'
    have h := weighted_cutProfile_le hmZ0 le_rfl hR0 hR1 p.H_pos hCst hPd hPb hBc a L ha hL
      hs.le q' η
    refine h.trans (le_of_eq ?_)
    rw [hGdef, hMdef, hAdef, hk0def, ← hcpow]
    ring
  have hzero : ∀ s : ℝ, p.H / 2 < s → ∀ q' η : ℝ,
      ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖ = 0 := by
    intro s hs q' η
    have hs0 : 0 < s := lt_of_le_of_lt (div_nonneg p.H_pos.le (by norm_num)) hs
    rw [hcoef (s, (q', η)) hs0, inletProfile_eq_zero p i (m := (s, (q', η))) hs, norm_zero]
  have hH2 : p.H / 2 = p.ageCut / p.ν / 2 := rfl
  have hJinv : ∀ η : ℝ, (1 + η ^ 2)⁻¹ ≤ 1 := fun η =>
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg η])
  have hJinv0 : ∀ η : ℝ, 0 ≤ (1 + η ^ 2)⁻¹ := fun η => inv_nonneg.2 (by positivity)
  have hcore' : ∀ s : ℝ, 0 < s → ∀ q' η : ℝ,
      transWeight mZ (s, (q', η)) * ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖ ≤ G := by
    intro s hs q' η
    calc _ ≤ G * (1 + η ^ 2)⁻¹ := hcore s hs q' η
      _ ≤ G * 1 := mul_le_mul_of_nonneg_left (hJinv η) hG0
      _ = G := mul_one _
  have hSig1 : 1 ≤ 1 + p.ageCut := by linarith [p.ageCut_pos]
  have hSig0 : 0 ≤ 1 + p.ageCut := by linarith
  have hpi1 : 1 ≤ 1 + Real.sqrt Real.pi := by linarith
  have hCf0 : 0 ≤ M * (1 + p.ageCut) * (1 + Real.sqrt Real.pi) :=
    mul_nonneg (mul_nonneg hM0 hSig0) (by linarith)
  have hνk : p.ν⁻¹ ^ (2 * k0) ≤ p.ν⁻¹ ^ (2 * k0 + 1) := pow_le_pow_right₀ hνi (by omega)
  have hνk' : p.ν⁻¹ ^ (2 * k0 + 1) = p.ν⁻¹ ^ (2 * k0) * p.ν⁻¹ := pow_succ _ _
  refine ⟨?_, ?_, ?_⟩
  · -- `√s W|v_i| ≤ P_ν`
    intro pt hs
    obtain ⟨s, q', η⟩ := pt
    simp only at hs ⊢
    have hW0 := transWeight_nonneg' mZ (s, (q', η))
    rcases le_or_gt s (p.H / 2) with hsH | hsH
    · have hsq := sqrt_le_absorb hν0 hν p.ageCut_pos hs.le hsH
      have hc := hcore' s hs q' η
      have hX0 : 0 ≤ transWeight mZ (s, (q', η)) * ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖ :=
        mul_nonneg hW0 (norm_nonneg _)
      calc Real.sqrt s * transWeight mZ (s, (q', η)) * ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖
          = Real.sqrt s * (transWeight mZ (s, (q', η)) *
              ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖) := by ring
        _ ≤ ((1 + p.ageCut) * p.ν⁻¹) * G := mul_le_mul hsq hc hX0 (mul_nonneg hSig0 hνinv0)
        _ = M * (1 + p.ageCut) * 1 * p.ν⁻¹ ^ (2 * k0 + 1) := by rw [hGdef, hνk']; ring
        _ ≤ M * (1 + p.ageCut) * (1 + Real.sqrt Real.pi) * p.ν⁻¹ ^ (2 * k0 + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hνinv0 _)
            exact mul_le_mul_of_nonneg_left hpi1 (mul_nonneg hM0 hSig0)
    · rw [hzero s hsH q' η, mul_zero]
      exact mul_nonneg hCf0 (pow_nonneg hνinv0 _)
  · -- `√s W|v_i| ≤ P_ν √s` for `s ≤ 1`
    intro pt hs _
    obtain ⟨s, q', η⟩ := pt
    simp only at hs ⊢
    have hc := hcore' s hs q' η
    have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
    have hGle : G ≤ M * (1 + p.ageCut) * (1 + Real.sqrt Real.pi) * p.ν⁻¹ ^ (2 * k0 + 1) := by
      rw [hGdef]
      have h1 : M ≤ M * (1 + p.ageCut) * (1 + Real.sqrt Real.pi) := by
        have : 1 ≤ (1 + p.ageCut) * (1 + Real.sqrt Real.pi) := by nlinarith
        nlinarith
      exact mul_le_mul h1 hνk (pow_nonneg hνinv0 _) hCf0
    calc Real.sqrt s * transWeight mZ (s, (q', η)) * ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖
        = (transWeight mZ (s, (q', η)) * ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖) *
            Real.sqrt s := by ring
      _ ≤ G * Real.sqrt s := mul_le_mul_of_nonneg_right hc hsq0
      _ ≤ _ := mul_le_mul_of_nonneg_right hGle hsq0
  · -- `‖W v_i(s)‖_{L²_ηL^∞_q} ≤ P_ν(1+s)^{-3/4}`
    intro s hs
    set Ds := M * (1 + p.ageCut) * p.ν⁻¹ ^ (2 * k0 + 1) * (1 + s) ^ (-3 / 4 : ℝ) with hDsdef
    have h1s : 0 < 1 + s := by linarith
    have hDs0 : 0 ≤ Ds :=
      mul_nonneg (mul_nonneg (mul_nonneg hM0 hSig0) (pow_nonneg hνinv0 _))
        (Real.rpow_nonneg h1s.le _)
    have hpt : ∀ q' η : ℝ, transWeight mZ (s, (q', η)) *
        ‖chartCoeff p.R (p.inlet i) (s, (q', η))‖ ≤ Ds * (1 + η ^ 2)⁻¹ := by
      intro q' η
      rcases le_or_gt s (p.H / 2) with hsH | hsH
      · have hab := one_le_absorb hν0 hν p.ageCut_pos hs.le hsH
        have hGD : G ≤ Ds := by
          rw [hGdef, hDsdef, hνk']
          have hX : 0 ≤ M * p.ν⁻¹ ^ (2 * k0) := mul_nonneg hM0 (pow_nonneg hνinv0 _)
          calc M * p.ν⁻¹ ^ (2 * k0) = M * p.ν⁻¹ ^ (2 * k0) * 1 := (mul_one _).symm
            _ ≤ M * p.ν⁻¹ ^ (2 * k0) * ((1 + p.ageCut) * p.ν⁻¹ * (1 + s) ^ (-3 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_left hab hX
            _ = _ := by ring
        exact (hcore s hs q' η).trans (mul_le_mul_of_nonneg_right hGD (hJinv0 η))
      · rw [hzero s hsH q' η, mul_zero]
        exact mul_nonneg hDs0 (hJinv0 η)
    refine (etaL2QSup_le_of_pointwise hDs0 hpt).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpi : Real.sqrt Real.pi ≤ 1 + Real.sqrt Real.pi := by linarith
    calc Ds * Real.sqrt Real.pi ≤ Ds * (1 + Real.sqrt Real.pi) :=
          mul_le_mul_of_nonneg_left hpi hDs0
      _ = _ := by rw [hDsdef]; ring

end UnforcedLeray.Short.IIIa
