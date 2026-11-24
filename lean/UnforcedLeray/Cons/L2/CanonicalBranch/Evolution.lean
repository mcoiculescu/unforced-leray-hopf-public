import UnforcedLeray.Units.B0123
import UnforcedLeray.Units.B0012
import UnforcedLeray.Lib.EvolutionFamilies

/-!
# G3b, part 1: the backward canonical evolution `S(θ, θ')` on `X_G`

`paper/main.tex`, Theorem G3b (lines 735–760), proof lines 1809–1840 (`eq:st18-t00095`–
`eq:st18-t00098`); blueprint units B0125 (G3b), B0118 (`eq:st18-t00096`), B0119
(`eq:st18-t00097`–`t00098`), with B0012 (`L₀` bounded on `X_G`, `eq:st18-t00006`), B0094
(`D ≤ 0` selfadjoint, eigenbasis `oscBasis`, `eq:st18-t00068`) and B0123 (`e^{aD}`,
`eq:st18-t00101`).

The canonical equation `-∂_θV = (L₀ + θ⁻¹D)V` (`eq:st18-t00013`) is solved backward in `θ`.
In the forward time `u = -θ < 0` it reads `∂_uV = (β(u)D + L₀)V` with `β(u) = -1/u = 1/θ`; this is
the manuscript's forward problem `W_t = (L₀ + βD)W` of `eq:st18-t00088` with `β(t) = 1/(R - t)`,
`θ = R - t` (B0114, B0115), and, after `τ = log(b₀/θ)`, the problem `∂_τV = DV + θL₀V` of
`eq:st18-t00097` (B0119). The free part is the diagonal evolution
`E_β(u, u') = exp[D ∫_{u'}^u β] = e^{log(θ'/θ) D}` (tex lines 1655–1667, B0106–B0107), a
contraction (`D ≤ 0`); `L₀` is a bounded perturbation, and the full evolution is its Dyson series
(bounded-perturbation Duhamel iteration, tex lines 1597–1617, 1830–1832; library
`Evolution.dyson`, INF08 T8.2).

## Main declarations (namespace `UnforcedLeray.Cons.G3b`)

* `continuous_expD_apply`: the semigroup `a ↦ e^{aD}x` of B0123 is strongly continuous.
* `freeU`, `freeFam`: the free family `e^{log(θ'/θ)D}` in the forward time `u = -θ`.
* `pertL0`: the constant bounded interaction `L₀` (B0012).
* **`S θ θ'`**: the backward evolution of `-∂_θV = (L₀ + θ⁻¹D)V` from `θ'` down to `θ`
  (`0 < θ ≤ θ'`); `S_eq_dyson` (it is the Dyson evolution on every enclosing interval),
  `S_self`, **`S_comp`** (`S(θ,θ')S(θ',θ'') = S(θ,θ'')`), **`norm_S_le`**
  (`‖S(θ,θ')‖ ≤ e^{‖L₀‖(θ' - θ)}`, the energy bound of `eq:st18-t00098`), `S_mild`
  (the Duhamel form), `continuousOn_S_left` (strong continuity in the final time `θ`).

Everything here is proved; no hypothesis is introduced.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123 UnforcedLeray.Evolution

/-! ## Strong continuity of `e^{aD}` -/

theorem continuous_expMult (n : ℕ) : Continuous fun a : ℝ => expMult a n := by
  unfold expMult
  fun_prop

theorem norm_expMult_sub_le (a a₀ : ℝ) (n : ℕ) : ‖expMult a n - expMult a₀ n‖ ≤ 2 :=
  (norm_sub_le _ _).trans (by linarith [norm_expMult_le a n, norm_expMult_le a₀ n])

/-- `‖e^{aD}x - e^{a₀D}x‖² = ∑ₙ |e^{-aₙ} - e^{-a₀ n}|² |⟪eₙ, x⟫|²` (Parseval in the eigenbasis of
`D`, B0094). -/
theorem hasSum_norm_expD_sub_sq (a a₀ : ℝ) (x : XG) :
    HasSum (fun n : ℕ => ‖(expMult a n - expMult a₀ n) * ⟪oscBasis n, x⟫_ℂ‖ ^ 2)
      (‖expD a x - expD a₀ x‖ ^ 2) := by
  have h := hasSum_norm_inner_sq oscBasis (expD a x - expD a₀ x)
  refine h.congr_fun fun n => ?_
  rw [inner_sub_right, inner_expD, inner_expD, sub_mul]

/-- **`e^{aD}` is strongly continuous** in `a ∈ ℝ` (tex line 1830: "the contraction semigroup of
`D`"; B0094, B0123). -/
theorem continuous_expD_apply (x : XG) : Continuous fun a : ℝ => expD a x := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Summable fun n : ℕ => 4 * ‖⟪oscBasis n, x⟫_ℂ‖ ^ 2 :=
    (hasSum_norm_inner_sq oscBasis x).summable.mul_left 4
  have hcont : Continuous fun a : ℝ =>
      ∑' n : ℕ, ‖(expMult a n - expMult a₀ n) * ⟪oscBasis n, x⟫_ℂ‖ ^ 2 := by
    refine continuous_tsum (fun n => ?_) hsum (fun n a => ?_)
    · exact (((continuous_expMult n).sub continuous_const).mul continuous_const).norm.pow 2
    · rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
      have h2 : ‖expMult a n - expMult a₀ n‖ ^ 2 ≤ 4 := by
        have := norm_expMult_sub_le a a₀ n
        nlinarith [norm_nonneg (expMult a n - expMult a₀ n)]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h0 : (∑' n : ℕ, ‖(expMult a₀ n - expMult a₀ n) * ⟪oscBasis n, x⟫_ℂ‖ ^ 2) = 0 := by
    simp
  have hsq : Tendsto (fun a : ℝ => ‖expD a x - expD a₀ x‖ ^ 2) (𝓝 a₀) (𝓝 0) := by
    have := hcont.tendsto a₀
    rw [h0] at this
    refine this.congr fun a => ?_
    exact (hasSum_norm_expD_sub_sq a a₀ x).tsum_eq
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun a => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)

/-! ## The free family in the forward time `u = -θ` -/

/-- The free evolution `E(u, u') = e^{log(θ'/θ) D}` from the forward time `u' = -θ'` to
`u = -θ` (tex lines 1655–1667: `E_β(t,s) = exp[D ∫_s^t β]` with `β = 1/θ`, so
`∫_{u'}^u β = log(θ'/θ)`). -/
def freeU (t s : ℝ) : XG →L[ℂ] XG := expD (Real.log (-s) - Real.log (-t))

theorem log_sub_nonneg {s t : ℝ} (hst : s ≤ t) (ht : t < 0) :
    0 ≤ Real.log (-s) - Real.log (-t) := by
  have : Real.log (-t) ≤ Real.log (-s) := Real.log_le_log (by linarith) (by linarith)
  linarith

/-- The free family on `[a, b]`, `b < 0`: a contraction evolution family. -/
def freeFam (a b : ℝ) (hb : b < 0) : EvolutionFamily XG a b where
  U := freeU
  U_diag t _ := by simp [freeU, expD_zero]
  U_comp s r t _ hsr hrt htb := by
    have ht : t < 0 := lt_of_le_of_lt htb hb
    have hr : r < 0 := lt_of_le_of_lt hrt ht
    unfold freeU
    rw [← expD_add (log_sub_nonneg hrt ht) (log_sub_nonneg hsr hr)]
    congr 1
    ring
  U_cont x := by
    have hlog : ContinuousOn (fun p : ℝ × ℝ => Real.log (-p.1) - Real.log (-p.2))
        {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} := by
      refine ContinuousOn.sub ?_ ?_
      · refine ContinuousOn.log (continuous_fst.neg.continuousOn) fun p hp => ?_
        have : p.1 < 0 := lt_of_le_of_lt (hp.2.1.trans hp.2.2) hb
        linarith
      · refine ContinuousOn.log (continuous_snd.neg.continuousOn) fun p hp => ?_
        have : p.2 < 0 := lt_of_le_of_lt hp.2.2 hb
        linarith
    exact (continuous_expD_apply x).comp_continuousOn hlog
  U_bdd := ⟨1, fun _ _ _ _ _ => norm_expD_le _⟩

theorem norm_freeU_le (t s : ℝ) : ‖freeU t s‖ ≤ 1 := norm_expD_le _

/-- The constant bounded interaction `L₀` (B0012, `eq:st18-t00006`). -/
def pertL0 (a b : ℝ) : BoundedPert XG a b where
  A := fun _ => B0012.L0
  meas _ := aestronglyMeasurable_const
  bdd := ⟨‖B0012.L0‖, fun _ _ => le_rfl⟩

/-! ## The Dyson terms do not depend on the enclosing interval -/

theorem dysonTerm_freeFam_eq {a b a' b' : ℝ} (hb : b < 0) (hb' : b' < 0) (k : ℕ) (t s : ℝ)
    (x : XG) :
    dysonTerm (freeFam a b hb) (pertL0 a b) k t s x =
      dysonTerm (freeFam a' b' hb') (pertL0 a' b') k t s x := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [dysonTerm_succ, dysonTerm_succ]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [ih r]
    rfl

/-- The Dyson evolution on `[a, b]` at a pair `(t, s)` of the triangle does not depend on
`[a, b]`. -/
theorem dyson_freeFam_eq {a b a' b' : ℝ} (hb : b < 0) (hb' : b' < 0) {s t : ℝ}
    (h : a ≤ s ∧ s ≤ t ∧ t ≤ b) (h' : a' ≤ s ∧ s ≤ t ∧ t ≤ b') :
    (dyson (freeFam a b hb) (pertL0 a b)).U t s =
      (dyson (freeFam a' b' hb') (pertL0 a' b')).U t s := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [(hasSum_dyson _ _ h x).tsum_eq.symm, (hasSum_dyson _ _ h' x).tsum_eq.symm]
  exact tsum_congr fun k => dysonTerm_freeFam_eq hb hb' k t s x

/-! ## The backward canonical evolution `S(θ, θ')` -/

/-- **The backward canonical evolution** `S(θ, θ')`, `0 < θ ≤ θ'`: the solution operator of
`-∂_θV = (L₀ + θ⁻¹D)V` (`eq:st18-t00013`) from `θ'` down to `θ`, as the Dyson evolution of the
free family `e^{log(θ'/θ)D}` perturbed by `L₀` on the forward-time interval `[-θ', -θ]`
(lines 1830–1832: "a bounded nonautonomous perturbation of the contraction semigroup of `D`.
Its Dyson series exists on every finite interval"). For `θ ≤ 0` it is the junk value `1`; it is
used only for `0 < θ ≤ θ'`. -/
def S (θ θ' : ℝ) : XG →L[ℂ] XG :=
  if h : 0 < θ then (dyson (freeFam (-θ') (-θ) (by linarith)) (pertL0 (-θ') (-θ))).U (-θ) (-θ')
  else 1

/-- `S(θ, θ')` is the Dyson evolution on every enclosing forward-time interval `[a, b]`,
`b < 0`. -/
theorem S_eq_dyson {a b : ℝ} (hb : b < 0) {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ')
    (ha : a ≤ -θ') (hbθ : -θ ≤ b) :
    S θ θ' = (dyson (freeFam a b hb) (pertL0 a b)).U (-θ) (-θ') := by
  rw [S, dite_cond_eq_true (eq_true hθ)]
  exact dyson_freeFam_eq _ hb ⟨le_rfl, by linarith, le_rfl⟩ ⟨ha, by linarith, hbθ⟩

theorem S_self {θ : ℝ} (hθ : 0 < θ) : S θ θ = 1 := by
  rw [S_eq_dyson (a := -θ) (b := -θ) (by linarith) hθ le_rfl le_rfl le_rfl]
  exact (dyson _ _).U_diag _ ⟨le_rfl, le_rfl⟩

/-- **Evolution law** `S(θ, θ') S(θ', θ'') = S(θ, θ'')` for `0 < θ ≤ θ' ≤ θ''`. -/
theorem S_comp {θ θ' θ'' : ℝ} (hθ : 0 < θ) (h1 : θ ≤ θ') (h2 : θ' ≤ θ'') :
    (S θ θ').comp (S θ' θ'') = S θ θ'' := by
  have hb : -θ < 0 := by linarith
  rw [S_eq_dyson (a := -θ'') hb hθ h1 (by linarith) le_rfl,
    S_eq_dyson (a := -θ'') hb (by linarith) h2 le_rfl (by linarith),
    S_eq_dyson (a := -θ'') hb hθ (h1.trans h2) le_rfl le_rfl]
  exact (dyson _ _).U_comp le_rfl (by linarith) (by linarith) le_rfl

theorem S_comp_apply {θ θ' θ'' : ℝ} (hθ : 0 < θ) (h1 : θ ≤ θ') (h2 : θ' ≤ θ'') (x : XG) :
    S θ θ' (S θ' θ'' x) = S θ θ'' x := by
  rw [← S_comp hθ h1 h2, ContinuousLinearMap.comp_apply]

/-- **The energy bound** (`eq:st18-t00098`, B0119): `‖S(θ, θ')‖ ≤ e^{‖L₀‖(θ' - θ)}`. The free
part is a contraction (`D ≤ 0`) and the interaction has norm `‖L₀‖`. -/
theorem norm_S_le {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    ‖S θ θ'‖ ≤ Real.exp (‖B0012.L0‖ * (θ' - θ)) := by
  have hb : -θ < 0 := by linarith
  rw [S_eq_dyson hb hθ hθθ' le_rfl le_rfl]
  have h := norm_dyson_le (freeFam (-θ') (-θ) hb) (pertL0 (-θ') (-θ)) (M := 1) (ω := 0)
    (C := ‖B0012.L0‖) (fun s t _ _ _ => by
      simp only [zero_mul, Real.exp_zero, mul_one]; exact norm_freeU_le t s)
    (fun _ _ => le_rfl) (-θ') (-θ) le_rfl (by linarith) le_rfl
  simp only [one_mul, zero_add] at h
  rwa [show -θ - -θ' = θ' - θ by ring] at h

/-- Strong continuity in the final time: `θ ↦ S(θ, θ₁)x` is continuous on `[ε, θ₁]`, `ε > 0`. -/
theorem continuousOn_S_left {ε θ₁ : ℝ} (hε : 0 < ε) (x : XG) :
    ContinuousOn (fun θ => S θ θ₁ x) (Icc ε θ₁) := by
  have hb : -ε < 0 := by linarith
  set E := dyson (freeFam (-θ₁) (-ε) hb) (pertL0 (-θ₁) (-ε))
  have hE : ContinuousOn (fun t => E.U t (-θ₁) x) (Icc (-θ₁) (-ε)) := E.continuousOn_fst le_rfl x
  have hneg : ContinuousOn (fun θ : ℝ => -θ) (Icc ε θ₁) := continuous_neg.continuousOn
  have hmaps : MapsTo (fun θ : ℝ => -θ) (Icc ε θ₁) (Icc (-θ₁) (-ε)) := fun θ hθ =>
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  refine (hE.comp hneg hmaps).congr fun θ hθ => ?_
  simp only [Function.comp_apply]
  exact congrArg (fun T : XG →L[ℂ] XG => T x)
    (S_eq_dyson hb (hε.trans_le hθ.1) hθ.2 le_rfl (by linarith [hθ.1]))

/-- **The Duhamel (mild) form** of `S` (tex lines 1830–1832; `dyson_left`): in the forward
time, `S(θ, θ')x = E(θ, θ')x + ∫_{-θ'}^{-θ} E(-θ, u) L₀ S(-u, θ')x du`, where
`E(θ, θ') = e^{log(θ'/θ)D}`. -/
theorem S_mild {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (x : XG) :
    S θ θ' x = expD (Real.log θ' - Real.log θ) x +
      ∫ u in (-θ')..(-θ), freeU (-θ) u (B0012.L0 (S (-u) θ' x)) := by
  have hb : -θ < 0 := by linarith
  rw [S_eq_dyson hb hθ hθθ' le_rfl le_rfl, dyson_left _ _ ⟨le_rfl, by linarith, le_rfl⟩ x]
  congr 1
  · simp [freeFam, freeU]
  · refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    show freeU (-θ) u (B0012.L0 _) = freeU (-θ) u (B0012.L0 _)
    congr 2
    have hu0 : 0 < -u := by linarith [hu.2]
    rw [S_eq_dyson hb hu0 (by linarith [hu.1]) le_rfl (by linarith [hu.2])]
    try simp only [neg_neg]

end UnforcedLeray.Cons.G3b
