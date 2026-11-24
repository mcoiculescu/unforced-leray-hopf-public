import UnforcedLeray.Short.PartIIb.StatementsNonlinear
import UnforcedLeray.Cons.C03Background.Contraction

/-!
# Part II-b, composition: from the numbered results of `short-background.tex` to the exact inverse
# and the exact background

Source: SP 2430-2524 (`short-bg:global-operator-comparison` and the Neumann perturbation
`R_ε = R_0[I + (𝔄_ε - 𝔄_0)R_0]⁻¹`, `‖R_ε‖ ≤ 2M`, SP 2476-2492; the contraction of SP 2505-2524;
the interpolation exponents `λ = 8/77`, `λ/28 = 2/539` of SP 1992-2005).

Proved here (no `sorry`, no hypothesis beyond the stated Props):

* `neumann_rightInverse`: the Banach-space perturbation lemma of SP 2476-2492;
* `exists_fixed_closure`: the contraction of SP 2510-2524, from `closureMap`;
* `interp_weights`, `interp_rate`: the exponent arithmetic and rate bookkeeping of SP 1992-2005;
* `poly_exp_small`, `analytic_core`: the parameter bookkeeping "`MΔ_ν < 1/2` for small `ν`" and
  "`4𝒫M²δ < 1`" of SP 2440-2470 and 2510-2524;
* `exactInverse_of`: `FlatInverse ∧ GlobalOperatorComparison ∧ PhysicalRowReduction → ExactInverse`;
* `backgroundResult_of`: `ExactInverse ∧ QuadraticFamily ∧ RawResidualFamily → BackgroundResult`.

The slow data: all statements fix the growing eigenpair `q = p.mode` and the slow age
`Σ = p.ageCut` before their constants (`StatementsNonlinear.lean`, "Quantifiers over the slow
data"). `exactInverse_of` takes the threshold `Σ₀` of `FlatInverse` at the decreased `m'`, and
`backgroundResult_of` the threshold of `ExactInverse`; `GlobalOperatorComparison` and
`QuadraticFamily` are used at that same `Σ`, and `N` is chosen before `Σ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## The Neumann perturbation (SP 2476-2492) -/

/-- If `R_0` is a right inverse of `𝔄_0` with `‖R_0‖ ≤ M` and `‖(𝔄_ε - 𝔄_0)R_0‖ ≤ 1/2`, then
`R_ε = R_0[I + (𝔄_ε - 𝔄_0)R_0]⁻¹` is a right inverse of `𝔄_ε` with `‖R_ε‖ ≤ 2M`. -/
theorem neumann_rightInverse {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A0 Ae : Z →L[ℝ] Y) (R0 : Y →L[ℝ] Z) {M : ℝ}
    (h0 : A0.comp R0 = 1) (hM : ‖R0‖ ≤ M) (hΔ : ‖(Ae - A0).comp R0‖ ≤ 1 / 2) :
    ∃ Re : Y →L[ℝ] Z, Ae.comp Re = 1 ∧ ‖Re‖ ≤ 2 * M := by
  set E : Y →L[ℝ] Y := (Ae - A0).comp R0 with hE
  have hEn : ‖-E‖ < 1 := by rw [norm_neg]; linarith
  obtain ⟨U, hU1, hU2⟩ : ∃ U : Y →L[ℝ] Y, U * (1 + E) = 1 ∧ (1 + E) * U = 1 := by
    refine ⟨↑(Units.oneSub (-E) hEn)⁻¹, ?_, ?_⟩
    · have h := (Units.oneSub (-E) hEn).inv_mul
      rw [Units.val_oneSub, sub_neg_eq_add] at h
      exact h
    · have h := (Units.oneSub (-E) hEn).mul_inv
      rw [Units.val_oneSub, sub_neg_eq_add] at h
      exact h
  have hUn : ‖U‖ ≤ 2 := by
    have h1 : U = 1 - U * E := by
      have h : U * (1 + E) = U + U * E := by rw [mul_add, mul_one]
      rw [h] at hU1
      exact eq_sub_of_add_eq hU1
    have h3 : ‖(1 : Y →L[ℝ] Y)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 : ‖U‖ ≤ ‖(1 : Y →L[ℝ] Y)‖ + ‖U‖ * ‖E‖ := by
      calc ‖U‖ = ‖1 - U * E‖ := by rw [← h1]
        _ ≤ ‖(1 : Y →L[ℝ] Y)‖ + ‖U * E‖ := norm_sub_le _ _
        _ ≤ ‖(1 : Y →L[ℝ] Y)‖ + ‖U‖ * ‖E‖ := add_le_add le_rfl (norm_mul_le _ _)
    nlinarith [norm_nonneg U, mul_le_mul_of_nonneg_left hΔ (norm_nonneg U)]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hAR : Ae.comp R0 = 1 + E := by
    have h : E = Ae.comp R0 - A0.comp R0 := by rw [hE, ContinuousLinearMap.sub_comp]
    rw [h, h0]
    abel
  refine ⟨R0.comp U, ?_, ?_⟩
  · calc Ae.comp (R0.comp U) = (Ae.comp R0).comp U := by rw [ContinuousLinearMap.comp_assoc]
      _ = (1 + E).comp U := by rw [hAR]
      _ = 1 := hU2
  · calc ‖R0.comp U‖ ≤ ‖R0‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * 2 := mul_le_mul hM hUn (norm_nonneg _) hM0
      _ = 2 * M := by ring

/-! ## The contraction (SP 2510-2524) -/

/-- The fixed point of the closure map `z ↦ T(-(F + Q(z,z)))` on the ball of radius `2Mδ`,
`4PM²δ < 1`. -/
theorem exists_fixed_closure {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Y →L[ℝ] Z) (Q : Z →L[ℝ] Z →L[ℝ] Y) (F : Y) {M P δ : ℝ}
    (hM : ‖T‖ ≤ M) (hQ : ‖Q‖ ≤ P) (hF : ‖F‖ ≤ δ) (hs : 4 * P * M ^ 2 * δ < 1) :
    ∃ z : Z, ‖z‖ ≤ 2 * M * δ ∧ T (-(F + Q z z)) = z := by
  obtain ⟨z, -, hz, hfix, -⟩ :=
    UnforcedLeray.Cons.C03.exists_fixedPoint_closureMap T Q F hM hQ hF hs
      (S := Set.univ) isClosed_univ (Set.mem_univ 0) (fun _ _ _ => Set.mem_univ _)
  exact ⟨z, hz, hfix⟩

/-! ## Exponent arithmetic (SP 1992-2005) -/

/-- `λ = (1/p - 1/r)/(1/2 - 1/r) = 8/77`, `λ/28 = 2/539`, `1/p = λ/2 + (1-λ)/r`
for `p = 11/4`, `r = 23/8`. -/
theorem interp_weights :
    (8 / 77 : ℝ) = (1 / bgp - 1 / bgr) / (1 / 2 - 1 / bgr) ∧ (8 / 77 : ℝ) / 28 = 2 / 539 ∧
      1 / bgp = (8 / 77) / 2 + (1 - 8 / 77) / bgr := by
  norm_num [bgp, bgr]

/-- Rate bookkeeping for the interpolation `‖T‖ ≤ ‖T_2‖^λ‖T_r‖^{1-λ}`: if the Hilbert endpoint is
`≤ Aε^{1/28}` and the `L^r` endpoint is `≤ B`, the `L^p` norm is `≤ A^λB^{1-λ}ε^{λ/28}`. -/
theorem interp_rate {Np N2 Nr A B ε lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hN2 : 0 ≤ N2) (hNr : 0 ≤ Nr)
    (h2 : N2 ≤ A * ε ^ (1 / 28 : ℝ)) (hr : Nr ≤ B)
    (hp : Np ≤ N2 ^ lam * Nr ^ (1 - lam)) :
    Np ≤ A ^ lam * B ^ (1 - lam) * ε ^ (lam / 28) := by
  have e1 : N2 ^ lam ≤ (A * ε ^ (1 / 28 : ℝ)) ^ lam := Real.rpow_le_rpow hN2 h2 hlam0
  have e2 : Nr ^ (1 - lam) ≤ B ^ (1 - lam) := Real.rpow_le_rpow hNr hr (by linarith)
  have e3 : (A * ε ^ (1 / 28 : ℝ)) ^ lam = A ^ lam * ε ^ (lam / 28) := by
    rw [Real.mul_rpow hA (Real.rpow_nonneg hε _), ← Real.rpow_mul hε]
    congr 2
    ring
  calc Np ≤ N2 ^ lam * Nr ^ (1 - lam) := hp
    _ ≤ (A ^ lam * ε ^ (lam / 28)) * B ^ (1 - lam) := by
        rw [← e3]
        exact mul_le_mul e1 e2 (Real.rpow_nonneg hNr _)
          (Real.rpow_nonneg (mul_nonneg hA (Real.rpow_nonneg hε _)) _)
    _ = A ^ lam * B ^ (1 - lam) * ε ^ (lam / 28) := by ring

/-! ## Parameter bookkeeping -/

/-- A polynomial in `ν⁻¹` times `e^{-a/ν}` is `< 1` for small `ν`. -/
theorem poly_exp_small (K : ℕ) (a C : ℝ) (ha : 0 < a) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      |C| * (ν ^ K)⁻¹ * Real.exp (-a / ν) < 1 := by
  have h0 : Tendsto (fun x : ℝ => x ^ K * Real.exp (-x)) atTop (𝓝 0) := by
    first
      | exact Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K
      | exact tendsto_pow_mul_exp_neg_atTop_nhds_zero K
  have h1 : Tendsto (fun x : ℝ => (a * x) ^ K * Real.exp (-(a * x))) atTop (𝓝 0) :=
    h0.comp (tendsto_id.const_mul_atTop ha)
  have h2 : Tendsto (fun x : ℝ => (|C| * (a ^ K)⁻¹) * ((a * x) ^ K * Real.exp (-(a * x))))
      atTop (𝓝 0) := by
    simpa using h1.const_mul (|C| * (a ^ K)⁻¹)
  obtain ⟨X, hX⟩ := (h2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists_forall_of_atTop
  refine ⟨1 / max X 1, by positivity, fun ν hν hνle => ?_⟩
  have hX1 : (0 : ℝ) < max X 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hx : X ≤ ν⁻¹ := by
    have : max X 1 ≤ ν⁻¹ := by
      rw [le_inv_comm₀ hX1 hν]
      simpa [one_div] using hνle
    exact le_trans (le_max_left _ _) this
  have key := hX ν⁻¹ hx
  have ha' : a ^ K ≠ 0 := pow_ne_zero _ ha.ne'
  have hinv : (a ^ K)⁻¹ * a ^ K = 1 := inv_mul_cancel₀ ha'
  have e : |C| * (ν ^ K)⁻¹ * Real.exp (-a / ν) =
      (|C| * (a ^ K)⁻¹) * ((a * ν⁻¹) ^ K * Real.exp (-(a * ν⁻¹))) := by
    calc |C| * (ν ^ K)⁻¹ * Real.exp (-a / ν)
        = |C| * ((a ^ K)⁻¹ * a ^ K) * (ν⁻¹) ^ K * Real.exp (-(a * ν⁻¹)) := by
          rw [hinv, inv_pow, show -a / ν = -(a * ν⁻¹) by ring]; ring
      _ = (|C| * (a ^ K)⁻¹) * ((a * ν⁻¹) ^ K * Real.exp (-(a * ν⁻¹))) := by
          rw [mul_pow]; ring
  rw [e]
  exact key

/-- The analytic core of `MΔ_ν < 1/2` (SP 2440-2470): with `M = |C_F|ν^{-k_F}e^{m'/ν}` and
`Δ = |C_G|ν^{-k_G}(4e^{-dmζ/ν} + e^{-D/ν})`, `D = 2m'`, `m' ≤ dmζ/4`, the product is `≤ 1/2` for
small `ν`. -/
theorem analytic_core (CF CG : ℝ) (kF kG : ℕ) (m' dm ζ D : ℝ) (hm' : 0 < m') (hdm : 0 < dm)
    (hζ : 0 < ζ) (hm'le : m' ≤ dm * ζ / 4) (hD : D = 2 * m') :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      (|CF| * (ν ^ kF)⁻¹ * Real.exp (m' / ν)) *
        (|CG| * (ν ^ kG)⁻¹ * (4 * Real.exp (-(dm * ζ) / ν) + Real.exp (-D / ν))) ≤ 1 / 2 := by
  obtain ⟨ν₀, hν₀, hsmall⟩ := poly_exp_small (kF + kG) m' (10 * |CF| * |CG|) hm'
  refine ⟨ν₀, hν₀, fun ν hν hνle => ?_⟩
  have hsm := hsmall ν hν hνle
  have hdz : 0 < dm * ζ := mul_pos hdm hζ
  have e1 : Real.exp (m' / ν) * Real.exp (-(dm * ζ) / ν) ≤ Real.exp (-m' / ν) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : m' / ν + -(dm * ζ) / ν = -m' / ν + (2 * m' - dm * ζ) / ν := by ring
    rw [this]
    have : (2 * m' - dm * ζ) / ν ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le
    linarith
  have e2 : Real.exp (m' / ν) * Real.exp (-D / ν) = Real.exp (-m' / ν) := by
    rw [← Real.exp_add, hD]
    congr 1
    ring
  have hpow : (ν ^ kF)⁻¹ * (ν ^ kG)⁻¹ = (ν ^ (kF + kG))⁻¹ := by
    rw [pow_add, mul_inv]
  have hE : 0 ≤ Real.exp (-m' / ν) := (Real.exp_pos _).le
  have hCF : 0 ≤ |CF| := abs_nonneg _
  have hCG : 0 ≤ |CG| := abs_nonneg _
  have hp1 : 0 ≤ (ν ^ kF)⁻¹ := by positivity
  have hp2 : 0 ≤ (ν ^ kG)⁻¹ := by positivity
  calc (|CF| * (ν ^ kF)⁻¹ * Real.exp (m' / ν)) *
        (|CG| * (ν ^ kG)⁻¹ * (4 * Real.exp (-(dm * ζ) / ν) + Real.exp (-D / ν)))
      = (|CF| * |CG| * ((ν ^ kF)⁻¹ * (ν ^ kG)⁻¹)) *
          (4 * (Real.exp (m' / ν) * Real.exp (-(dm * ζ) / ν)) +
            Real.exp (m' / ν) * Real.exp (-D / ν)) := by ring
    _ ≤ (|CF| * |CG| * ((ν ^ kF)⁻¹ * (ν ^ kG)⁻¹)) * (4 * Real.exp (-m' / ν) + Real.exp (-m' / ν)) := by
        rw [e2]
        gcongr
    _ = 5 * (|CF| * |CG|) * (ν ^ (kF + kG))⁻¹ * Real.exp (-m' / ν) := by rw [hpow]; ring
    _ ≤ 1 / 2 := by
        have h10 : abs (10 * |CF| * |CG|) = 10 * |CF| * |CG| := abs_of_nonneg (by positivity)
        rw [h10] at hsm
        linarith [hsm]

/-! ## The row operator -/

theorem rowOp_sub_le {c : ℝ} (K K' : HpR c →L[ℝ] HpR c) (C C' : E2 →L[ℝ] HpR c) :
    ‖rowOp K C - rowOp K' C'‖ ≤ ‖K - K'‖ + ‖C - C'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    fun y => ?_
  have hy : ‖y‖ = ‖y.fst‖ + ‖y.snd‖ := WithLp.prod_norm_eq_of_L1 y
  have happ : (rowOp K C - rowOp K' C') y = (K - K') y.fst + (C - C') y.snd := by
    first
      | (simp only [rowOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, WithLp.fstL_apply, WithLp.sndL_apply,
          ContinuousLinearMap.id_apply]; abel)
      | (simp [rowOp]; abel)
      | simp [rowOp]
  rw [happ, hy]
  calc ‖(K - K') y.fst + (C - C') y.snd‖ ≤ ‖(K - K') y.fst‖ + ‖(C - C') y.snd‖ := norm_add_le _ _
    _ ≤ ‖K - K'‖ * ‖y.fst‖ + ‖C - C'‖ * ‖y.snd‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ (‖K - K'‖ + ‖C - C'‖) * (‖y.fst‖ + ‖y.snd‖) := by
        nlinarith [norm_nonneg (K - K'), norm_nonneg (C - C'), norm_nonneg y.fst,
          norm_nonneg y.snd]

/-! ## Regime facts -/

theorem eps_rpow_le {p : Params} {d dm dp : ℝ} (h : BgRegime p d dm dp) {x : ℝ} (hx : 0 ≤ x) :
    p.ε ^ x ≤ Real.exp (-(dm * x) / p.ν) := by
  rw [h.eps_eq, ← Real.exp_mul]
  apply Real.exp_le_exp.2
  have hν := p.ν_pos
  have h1 : dm * x ≤ d * x := mul_le_mul_of_nonneg_right h.dm_le hx
  have : -d / p.ν * x = -(d * x) / p.ν := by ring
  rw [this]
  first
    | exact div_le_div_of_nonneg_right (by linarith) hν.le
    | exact div_le_div_of_le_right (by linarith) hν.le
    | (apply div_le_div_of_nonneg_right <;> linarith)

theorem eps_rpow_le_zeta {p : Params} {d dm dp : ℝ} (h : BgRegime p d dm dp) {x ζ : ℝ}
    (hζ : 0 ≤ ζ) (hx : ζ ≤ x) : p.ε ^ x ≤ Real.exp (-(dm * ζ) / p.ν) := by
  refine le_trans (eps_rpow_le h (le_trans hζ hx)) (Real.exp_le_exp.2 ?_)
  have hν := p.ν_pos
  have h1 : dm * ζ ≤ dm * x := mul_le_mul_of_nonneg_left hx h.dm_pos.le
  first
    | exact div_le_div_of_nonneg_right (by linarith) hν.le
    | exact div_le_div_of_le_right (by linarith) hν.le
    | (apply div_le_div_of_nonneg_right <;> linarith)


theorem div_le_div_r {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc)

/-! ## The exact inverse (SP 2430-2504) -/

/-- The window exponents: `a = b = θ/(4(N+1))`, `ζ = a/2` (SP 2455-2462: "choose `a, b` so
`θ - N(a+b) > 0`"). -/
theorem exponent_choice (N : ℕ) :
    ∃ a ζ : ℝ, 0 < a ∧ 0 < ζ ∧ ζ ≤ a / 2 ∧ ζ ≤ 1 ∧ ζ ≤ (2 / 539 : ℝ) - N * (a + a) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h4N : (4 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (2 / 539 : ℝ) / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haθ : a * (4 * ((N : ℝ) + 1)) = 2 / 539 := by
    rw [ha_def]; exact div_mul_cancel₀ _ h4N
  have haN : 0 ≤ a * N := mul_nonneg ha0.le hN0
  refine ⟨a, a / 2, ha0, by positivity, le_rfl, ?_, ?_⟩
  · linarith
  · linarith

/-- The `ε`-terms of `GlobalOperatorComparison` are dominated by `e^{-d_-ζ/ν}`. -/
theorem eps_terms_le {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) {a ζ D : ℝ} {N : ℕ}
    (hζ0 : 0 ≤ ζ) (h1 : ζ ≤ a / 2) (h2 : ζ ≤ 1) (h3 : ζ ≤ (2 / 539 : ℝ) - N * (a + a)) :
    p.ε ^ (a / 2) + p.ε ^ (a / 2) + p.ε + p.ε ^ ((2 / 539 : ℝ) - N * (a + a)) +
        Real.exp (-D / p.ν) ≤ 4 * Real.exp (-(dm * ζ) / p.ν) + Real.exp (-D / p.ν) := by
  have e1 := eps_rpow_le_zeta hreg hζ0 h1
  have e2 := eps_rpow_le_zeta hreg hζ0 h3
  have e3 : p.ε ≤ Real.exp (-(dm * ζ) / p.ν) := by
    have := eps_rpow_le_zeta hreg hζ0 h2
    simpa using this
  linarith

/-- The period `P = 2εc ≤ 1` for small `ν` (`c = ν⁻²`, `ε = e^{-d/ν}`, `d ≥ d_-`). -/
theorem period_le_one_of {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (h : |(2 : ℝ)| * (p.ν ^ 2)⁻¹ * Real.exp (-dm / p.ν) < 1) : p.period ≤ 1 := by
  have hεle : p.ε ≤ Real.exp (-dm / p.ν) := by
    have := eps_rpow_le hreg (x := 1) zero_le_one
    simpa using this
  have hc : 0 ≤ (p.ν ^ 2)⁻¹ := by have := p.ν_pos; positivity
  unfold Params.period
  rw [hreg.c_eq]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith [mul_le_mul_of_nonneg_left hεle hc]

set_option maxHeartbeats 800000 in
/-- The operator algebra of the exact inverse at one parameter point: the Neumann series
`R_ε = R_0[I + (𝔄_ε - 𝔄_0)R_0]⁻¹` (SP 2476-2492) and the physical normalization `T = ΘR_εJ`. -/
theorem exact_inverse_point (p : Params)
    (Ke K0 : HpR p.c →L[ℝ] HpR p.c) (Ce C0 : E2 →L[ℝ] HpR p.c)
    (R0 : HpR p.c →L[ℝ] RowSpace p.c) (Θ : RowSpace p.c →L[ℝ] p.Z) (J : p.Y →L[ℝ] HpR p.c)
    {Dl M CP s : ℝ} (hR0 : ∀ F, rowOp K0 C0 (R0 F) = F) (hM : ‖R0‖ ≤ M)
    (hΔ : ‖Ke - K0‖ + ‖Ce - C0‖ ≤ Dl) (hMD : M * Dl ≤ 1 / 2)
    (hs0 : 0 < s) (hΘn : ‖Θ‖ ≤ CP * s) (hJn : ‖J‖ ≤ s⁻¹)
    (hΘJ : ∀ (y : RowSpace p.c) (f : p.Y), rowOp Ke Ce y = J f →
      p.OrdRel (Θ y) (f : Yq p.period q0E)) :
    ∃ T : p.Y →L[ℝ] p.Z, (∀ f : p.Y, p.OrdRel (T f) (f : Yq p.period q0E)) ∧
      ‖T‖ ≤ 2 * CP * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg R0) hM
  have hCP : 0 ≤ CP := by
    have h : 0 ≤ CP * s := le_trans (norm_nonneg Θ) hΘn
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos_of_neg_of_neg hneg (neg_neg_of_pos hs0)]
  have hAe : ‖rowOp Ke Ce - rowOp K0 C0‖ ≤ Dl := le_trans (rowOp_sub_le Ke K0 Ce C0) hΔ
  have hR0comp : (rowOp K0 C0).comp R0 = 1 := by
    refine ContinuousLinearMap.ext fun F => ?_
    simpa using hR0 F
  have hprod : ‖(rowOp Ke Ce - rowOp K0 C0).comp R0‖ ≤ 1 / 2 := by
    have h1 := ContinuousLinearMap.opNorm_comp_le (rowOp Ke Ce - rowOp K0 C0) R0
    have h2 : ‖rowOp Ke Ce - rowOp K0 C0‖ * ‖R0‖ ≤ Dl * M :=
      mul_le_mul hAe hM (norm_nonneg R0)
        (le_trans (norm_nonneg (rowOp Ke Ce - rowOp K0 C0)) hAe)
    have h3 : Dl * M = M * Dl := mul_comm _ _
    linarith
  obtain ⟨Re, hRe, hRen⟩ := neumann_rightInverse (rowOp K0 C0) (rowOp Ke Ce) R0 hR0comp hM hprod
  refine ⟨Θ.comp (Re.comp J), ?_, ?_⟩
  · intro f
    have hy : rowOp Ke Ce (Re (J f)) = J f := by
      simpa using congrArg (fun L : HpR p.c →L[ℝ] HpR p.c => L (J f)) hRe
    exact hΘJ (Re (J f)) f hy
  · calc ‖Θ.comp (Re.comp J)‖ ≤ ‖Θ‖ * ‖Re.comp J‖ :=
          ContinuousLinearMap.opNorm_comp_le Θ (Re.comp J)
      _ ≤ ‖Θ‖ * (‖Re‖ * ‖J‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le Re J) (norm_nonneg Θ)
      _ ≤ (CP * s) * ((2 * M) * s⁻¹) :=
          mul_le_mul hΘn (mul_le_mul hRen hJn (norm_nonneg J) (by positivity))
            (mul_nonneg (norm_nonneg Re) (norm_nonneg J)) (mul_nonneg hCP hs0.le)
      _ = 2 * CP * M := by field_simp

set_option maxHeartbeats 800000 in
/-- **`FlatInverse ∧ GlobalOperatorComparison ∧ PhysicalRowReduction → ExactInverse`**: choose
`a = b = θ/(4(N+1))`, `ζ = a/2`, `m' = min(m, d_-ζ/4)`, `D = 2m'`; then `MΔ_ν ≤ 1/2` for small `ν`
(`analytic_core`), the Neumann series gives `R_ε` with `‖R_ε‖ ≤ 2M` (`neumann_rightInverse`) and
the physical normalization `T = Θ R_ε J` has norm `≤ 2C_PM`. -/
theorem exactInverse_of (hF : FlatInverse) (hG : GlobalOperatorComparison)
    (hP : PhysicalRowReduction) : ExactInverse := by
  intro lam q hq m hm dm dp hdm
  obtain ⟨N, hN⟩ := hG
  obtain ⟨a, ζ, ha0, hζ0, hζa, hζ1, hζθ⟩ := exponent_choice N
  obtain ⟨m', hm'_def⟩ : ∃ m', m' = min m (dm * ζ / 4) := ⟨_, rfl⟩
  have hm'0 : 0 < m' := by rw [hm'_def]; exact lt_min hm (by positivity)
  have hm'm : m' ≤ m := by rw [hm'_def]; exact min_le_left _ _
  have hm'z : m' ≤ dm * ζ / 4 := by rw [hm'_def]; exact min_le_right _ _
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * m' := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  obtain ⟨Sig₀, hSig₀, hFS⟩ := hF lam q hq m' hm'0 dm dp hdm
  refine ⟨Sig₀, hSig₀, fun Sig hSig => ?_⟩
  have hSig0 : 0 < Sig := lt_of_lt_of_le hSig₀ hSig
  obtain ⟨CG, kG, νG, hCG, hνG, hGp⟩ := hN Sig lam q hSig0 hq D hD0 a a ha0 ha0 dm dp hdm
  obtain ⟨CF, kF, ν₁, hCF, hν₁, hFp⟩ := hFS Sig hSig
  obtain ⟨CP, hCP, hPp⟩ := hP dm dp hdm
  obtain ⟨ν₂, hν₂, hcore⟩ := analytic_core CF CG kF kG m' dm ζ D hm'0 hdm hζ0 hm'z hD
  obtain ⟨ν₃, hν₃, hper⟩ := poly_exp_small 2 dm 2 hdm
  refine ⟨2 * CP * CF, kF, min (min ν₁ νG) (min ν₂ (min ν₃ 1)), by positivity,
    lt_min (lt_min hν₁ hνG) (lt_min hν₂ (lt_min hν₃ zero_lt_one)), ?_⟩
  intro p d hreg hν hSg hmode
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ ν₁ := le_trans hν (le_trans (min_le_left _ _) (min_le_left _ _))
  have hνG' : p.ν ≤ νG := le_trans hν (le_trans (min_le_left _ _) (min_le_right _ _))
  have hν2 : p.ν ≤ ν₂ := le_trans hν (le_trans (min_le_right _ _) (min_le_left _ _))
  have hν3 : p.ν ≤ ν₃ :=
    le_trans hν (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hνle1 : p.ν ≤ 1 :=
    le_trans hν (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hperiod : p.period ≤ 1 := period_le_one_of hreg (hper p.ν hνp hν3)
  obtain ⟨⟨K0, C0, hK0, hC0⟩, hinv⟩ := hFp p d hreg hν1 hSg hmode
  obtain ⟨R0, hR0, hR0n⟩ := hinv K0 C0 hK0 hC0
  obtain ⟨⟨Ke, Ce, hKe, hCe⟩, hcmp⟩ := hGp p d hreg hνG' hSg hmode
  have hΔ := hcmp Ke K0 Ce C0 hKe hK0 hCe hC0
  obtain ⟨Θ, J, hΘn, hJn, -, hΘJ⟩ :=
    hPp p d hreg hperiod hνle1 lam (by rw [hmode]; exact hq) Ke Ce hKe hCe
  have hterms := eps_terms_le hreg (D := D) (N := N) hζ0.le hζa hζ1 hζθ
  have hpow : 0 ≤ (p.ν ^ kG)⁻¹ := by positivity
  have hΔle : ‖Ke - K0‖ + ‖Ce - C0‖ ≤
      CG * (p.ν ^ kG)⁻¹ * (4 * Real.exp (-(dm * ζ) / p.ν) + Real.exp (-D / p.ν)) :=
    le_trans hΔ (mul_le_mul_of_nonneg_left hterms (mul_nonneg hCG.le hpow))
  have hcore' := hcore p.ν hνp hν2
  rw [abs_of_pos hCF, abs_of_pos hCG] at hcore'
  have hs0 : 0 < (Real.pi * p.R ^ 2) ^ (1 / bgp) :=
    Real.rpow_pos_of_pos (by have := p.R_pos; positivity) _
  obtain ⟨T, hT, hTn⟩ := exact_inverse_point p Ke K0 Ce C0 R0 Θ J
    (Dl := CG * (p.ν ^ kG)⁻¹ * (4 * Real.exp (-(dm * ζ) / p.ν) + Real.exp (-D / p.ν)))
    (M := CF * (p.ν ^ kF)⁻¹ * Real.exp (m' / p.ν)) (CP := CP)
    (s := (Real.pi * p.R ^ 2) ^ (1 / bgp)) hR0 hR0n hΔle hcore' hs0 hΘn hJn hΘJ
  refine ⟨T, hT, le_trans hTn ?_⟩
  have hexpm : Real.exp (m' / p.ν) ≤ Real.exp (m / p.ν) :=
    Real.exp_le_exp.2 (div_le_div_r hm'm hνp.le)
  have h0 : 0 ≤ 2 * CP * CF * (p.ν ^ kF)⁻¹ := by positivity
  calc 2 * CP * (CF * (p.ν ^ kF)⁻¹ * Real.exp (m' / p.ν))
      = 2 * CP * CF * (p.ν ^ kF)⁻¹ * Real.exp (m' / p.ν) := by ring
    _ ≤ 2 * CP * CF * (p.ν ^ kF)⁻¹ * Real.exp (m / p.ν) := mul_le_mul_of_nonneg_left hexpm h0

/-! ## The exact background (SP 2505-2524) -/

/-- The smallness `4𝒫M²δ < 1` for small `ν` (SP 2519-2524): `2m' ≤ dm/5 < 3dm/11`. -/
theorem smallness_real (CE CQ CR : ℝ) (kE kQ kR : ℕ) (m' dm : ℝ) (hCE : 0 < CE) (hCQ : 0 < CQ)
    (hCR : 0 < CR) (hdm : 0 < dm) (hm'd : m' ≤ dm / 10) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν e : ℝ, 0 < ν → ν ≤ ν₀ → 0 ≤ e →
      e ≤ Real.exp (-(dm * (3 / 11)) / ν) →
      4 * (CQ * (ν ^ kQ)⁻¹) * (CE * (ν ^ kE)⁻¹ * Real.exp (m' / ν)) ^ 2 *
        (CR * (ν ^ kR)⁻¹ * e) < 1 := by
  obtain ⟨ν₀, hν₀, hsm⟩ := poly_exp_small (kQ + 2 * kE + kR) (4 * dm / 55)
    (4 * CQ * CE ^ 2 * CR) (by positivity)
  refine ⟨ν₀, hν₀, fun ν e hν hνle he0 he => ?_⟩
  have hsm' := hsm ν hν hνle
  have hCabs : abs (4 * CQ * CE ^ 2 * CR) = 4 * CQ * CE ^ 2 * CR := abs_of_pos (by positivity)
  rw [hCabs] at hsm'
  have e1 : Real.exp (m' / ν) ^ 2 * Real.exp (-(dm * (3 / 11)) / ν) ≤
      Real.exp (-(4 * dm / 55) / ν) := by
    have h2 : Real.exp (m' / ν) ^ 2 = Real.exp (2 * (m' / ν)) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h3 : 2 * (m' / ν) + -(dm * (3 / 11)) / ν =
        -(4 * dm / 55) / ν + (2 * m' - dm / 5) / ν := by ring
    rw [h3]
    have h4 : (2 * m' - dm / 5) / ν ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le
    linarith
  have hpw : (ν ^ kQ)⁻¹ * ((ν ^ kE)⁻¹) ^ 2 * (ν ^ kR)⁻¹ = (ν ^ (kQ + 2 * kE + kR))⁻¹ := by
    have h : ν ^ (kQ + 2 * kE + kR) = ν ^ kQ * (ν ^ kE) ^ 2 * ν ^ kR := by ring
    rw [h, mul_inv, mul_inv, inv_pow]
  calc 4 * (CQ * (ν ^ kQ)⁻¹) * (CE * (ν ^ kE)⁻¹ * Real.exp (m' / ν)) ^ 2 *
        (CR * (ν ^ kR)⁻¹ * e)
      = (4 * CQ * CE ^ 2 * CR) * ((ν ^ kQ)⁻¹ * ((ν ^ kE)⁻¹) ^ 2 * (ν ^ kR)⁻¹) *
          (Real.exp (m' / ν) ^ 2 * e) := by ring
    _ ≤ (4 * CQ * CE ^ 2 * CR) * ((ν ^ kQ)⁻¹ * ((ν ^ kE)⁻¹) ^ 2 * (ν ^ kR)⁻¹) *
          Real.exp (-(4 * dm / 55) / ν) :=
        mul_le_mul_of_nonneg_left
          (le_trans (mul_le_mul_of_nonneg_left he (by positivity)) e1) (by positivity)
    _ = (4 * CQ * CE ^ 2 * CR) * (ν ^ (kQ + 2 * kE + kR))⁻¹ * Real.exp (-(4 * dm / 55) / ν) := by
        rw [hpw]
    _ < 1 := hsm'

/-- The contraction at one parameter point (SP 2510-2524): the fixed point of
`z ↦ T(-(𝔓F_R + 𝒬(z,z)))` solves the projected equation `𝔓F_R + 𝓛z + 𝒬(z,z) = 0`. -/
theorem contraction_point (p : Params) (T : p.Y →L[ℝ] p.Z)
    (hT : ∀ f : p.Y, p.OrdRel (T f) (f : Yq p.period q0E))
    (Q : p.Z →L[ℝ] p.Z →L[ℝ] p.Y) (hQrel : ∀ z z', p.QuadRel z z' (Q z z'))
    (g : p.Y) (hg : p.RawRel g) {M P δ : ℝ} (hM : ‖T‖ ≤ M) (hQn : ‖Q‖ ≤ P) (hgn : ‖g‖ ≤ δ)
    (hs : 4 * P * M ^ 2 * δ < 1) :
    ∃ z : p.Z, ProjectedEquation p z ∧ ‖z‖ ≤ 2 * M * δ := by
  obtain ⟨z, hzn, hzfix⟩ := exists_fixed_closure T Q g hM hQn hgn hs
  refine ⟨z, ?_, hzn⟩
  have hz := hT (-(g + Q z z))
  rw [hzfix] at hz
  refine ⟨(g : Yq p.period q0E), ((-(g + Q z z) : p.Y) : Yq p.period q0E),
    ((Q z z : p.Y) : Yq p.period q0E), hg, hz, hQrel z z, ?_⟩
  first
    | (push_cast; abel)
    | (simp only [Submodule.coe_neg, Submodule.coe_add]; abel)
    | simp

/-- **`ExactInverse ∧ QuadraticFamily ∧ RawResidualFamily → BackgroundResult`**: the contraction
`z = T(-(𝔓F_R + 𝒬(z,z)))` on the ball of radius `2Mδ`, `4𝒫M²δ < 1` for small `ν` since
`2m' ≤ dm/5 < 3dm/11`. -/
theorem backgroundResult_of (hE : ExactInverse) (hQ : QuadraticFamily)
    (hR : RawResidualFamily) : BackgroundResult := by
  intro lam q hq m hm dm dp hdm
  obtain ⟨m', hm'_def⟩ : ∃ m', m' = min m (dm / 10) := ⟨_, rfl⟩
  have hm'0 : 0 < m' := by rw [hm'_def]; exact lt_min hm (by positivity)
  have hm'm : m' ≤ m := by rw [hm'_def]; exact min_le_left _ _
  have hm'd : m' ≤ dm / 10 := by rw [hm'_def]; exact min_le_right _ _
  obtain ⟨Sig₀, hSig₀, hES⟩ := hE lam q hq m' hm'0 dm dp hdm
  refine ⟨Sig₀, hSig₀, fun Sig hSig => ?_⟩
  have hSig0 : 0 < Sig := lt_of_lt_of_le hSig₀ hSig
  obtain ⟨CE, kE, νE, hCE, hνE, hEp⟩ := hES Sig hSig
  obtain ⟨CQ, kQ, νQ, hCQ, hνQ, hQp⟩ := hQ Sig lam q hSig0 hq dm dp hdm
  obtain ⟨CR, kR, νR, hCR, hνR, hRp⟩ := hR dm dp hdm
  obtain ⟨ν₄, hν₄, hsm⟩ := smallness_real CE CQ CR kE kQ kR m' dm hCE hCQ hCR hdm hm'd
  refine ⟨2 * CE * CR, kE + kR, min νE (min νQ (min νR ν₄)), by positivity,
    lt_min hνE (lt_min hνQ (lt_min hνR hν₄)), ?_⟩
  intro p d hreg hν hSg hmode
  have hνp : 0 < p.ν := p.ν_pos
  have hνE' : p.ν ≤ νE := le_trans hν (min_le_left _ _)
  have hνQ' : p.ν ≤ νQ := le_trans hν (le_trans (min_le_right _ _) (min_le_left _ _))
  have hνR' : p.ν ≤ νR :=
    le_trans hν (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hν4 : p.ν ≤ ν₄ :=
    le_trans hν (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨T, hT, hTn⟩ := hEp p d hreg hνE' hSg hmode
  obtain ⟨Q, hQrel, hQn⟩ := hQp p d hreg hνQ' hSg hmode
  obtain ⟨g, hgrel, hgn⟩ := hRp p d hreg hνR'
  have hε : p.ε ^ (3 / 11 : ℝ) ≤ Real.exp (-(dm * (3 / 11)) / p.ν) :=
    eps_rpow_le hreg (by norm_num)
  have hε0 : 0 ≤ p.ε ^ (3 / 11 : ℝ) := Real.rpow_nonneg p.ε_pos.le _
  have hsmall := hsm p.ν (p.ε ^ (3 / 11 : ℝ)) hνp hν4 hε0 hε
  obtain ⟨z, hz, hzn⟩ := contraction_point p T hT Q hQrel g hgrel hTn hQn hgn hsmall
  refine ⟨z, hz, ?_⟩
  have hexpm : Real.exp (m' / p.ν) ≤ Real.exp (m / p.ν) :=
    Real.exp_le_exp.2 (div_le_div_r hm'm hνp.le)
  have h0 : 0 ≤ 2 * CE * CR * ((p.ν ^ kE)⁻¹ * (p.ν ^ kR)⁻¹) * p.ε ^ (3 / 11 : ℝ) := by
    positivity
  calc ‖z‖ ≤ 2 * (CE * (p.ν ^ kE)⁻¹ * Real.exp (m' / p.ν)) *
        (CR * (p.ν ^ kR)⁻¹ * p.ε ^ (3 / 11 : ℝ)) := hzn
    _ = (2 * CE * CR * ((p.ν ^ kE)⁻¹ * (p.ν ^ kR)⁻¹) * p.ε ^ (3 / 11 : ℝ)) *
          Real.exp (m' / p.ν) := by ring
    _ ≤ (2 * CE * CR * ((p.ν ^ kE)⁻¹ * (p.ν ^ kR)⁻¹) * p.ε ^ (3 / 11 : ℝ)) *
          Real.exp (m / p.ν) := mul_le_mul_of_nonneg_left hexpm h0
    _ = 2 * CE * CR * (p.ν ^ (kE + kR))⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
        rw [pow_add, mul_inv]; ring

/-- **The composed scope output**: the exact solution of the projected equation (SP 2505-2524) from
the leaf results `FlatInverse` (SP 2342), `GlobalOperatorComparison` (SP 2430-2470),
`PhysicalRowReduction` (SP 2493-2504), `QuadraticFamily` (SP 2505-2518) and `RawResidualFamily`
(Part I, SP 2042-2046). -/
theorem backgroundResult_of_leaves (hF : FlatInverse) (hG : GlobalOperatorComparison)
    (hP : PhysicalRowReduction) (hQ : QuadraticFamily) (hR : RawResidualFamily) :
    BackgroundResult :=
  backgroundResult_of (exactInverse_of hF hG hP) hQ hR

end UnforcedLeray.Short.IIb
