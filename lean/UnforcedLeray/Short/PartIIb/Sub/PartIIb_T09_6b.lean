import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_6a
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.Holder
import UnforcedLeray.Lib.Sobolev.Axis

/-!
# Part II-b, task `PartII-b:T09/6b` (`LapAxisRemove`): removing the axis by cutting off the test

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`s = R²/ρ²`; the domains of `A_ε` and its adjoint are the exact Cartesian domains under the lifts,
no boundary is introduced at either age end) and 1902-1921 (`H_r`, the graph class `b ∈ H_r`,
`√s Q_ε b ∈ H_r`; `∂_ρ(√s b) = s Q_ε b`).

Let `aₙ = Sob.axisCut n` (`Lib/Sobolev/Axis.lean`, the cutoff of the removable-axis lemma
`HasWeakDeriv.of_bdd_off_axis`): `aₙ(y) = η((n+1)² q(y))`, `q = y₀² + y₁²`, `η = 0` on `(-∞, 1]`,
`η = 1` on `[2, ∞)`; so `aₙ = 0` for `ϱ ≤ 1/(n+1)`, `aₙ = 1` for `ϱ² ≥ 2/(n+1)²`, and
`∂_j aₙ = wₙ y_j` (`j = 0, 1`), `∂_2 aₙ = 0` with `wₙ = 2(n+1)² η'((n+1)² q)` (`axisCutW`).  With `E_h = y₀∂₀ + y₁∂₁` (`hEuler`) and
`T_h F = ∂₀(y₀F) + ∂₁(y₁F)` (`hEulerT`, the transpose of `-E_h`),
`Δ(aₙΦ) = aₙΔΦ + wₙ E_hΦ + T_h(wₙΦ)` (`OffCutLeibniz`).  On `ϱ > 0`, `E_h = ϱ∂_ϱ` and
`∂_ϱ N_v b = N_v(√s Q_ε b)` (SP 1920), so `⟪T_h F, N_v b⟫ = -⟪ϱF, N_v(√s Q_ε b)⟫` for off-axis
`F` (`RadialIBP`).  Hence, for the off-axis tests `aₙΦ`,
`⟪νΔ(aₙΦ), N_v b⟫ = ν(⟪aₙΔΦ, N_v b⟫ + ⟪wₙE_hΦ, N_v b⟫ - ⟪ϱwₙΦ, N_v(√s Q_ε b)⟫)`.
`|wₙ| ϱ ≤ M(n+1)` (`axisCutW_bound`) and all the remainders are supported in the tube
`(n+1)²ϱ² ≤ 2`, `‖y‖ ≤ Rad`, of volume `O((n+1)⁻²)`; by Hölder they are `O((n+1)^{2/r-1}) → 0` for
`r > 2` (`TubeSmall`).  So both sides of the off-axis identity converge, to the two sides of the
identity for `Φ`.

Leaves (new): `OffCutLeibniz` (`T09/6b/3`), `TubeSmall` (`/4`), `PairNvCAdd` (`/5`),
`RadialIBP` (`/6`, decomposed in `Sub/PartIIb_T09_6b_6.lean`).  Proved here: the cutoff facts
`contDiff_axisCutW`, `fderiv_axisCut_eq`, `axisCutW_bound`, ..., `cutLimit`, `lapAxisRemove_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-! ## Definitions -/

/-- `wₙ(y) = 2(n+1)² η'((n+1)² q(y))` (`η = Sob.axisEta`, `q = Sob.axisQ`), so that
`∂_j (Sob.axisCut n) = wₙ y_j` (`j = 0, 1`), `∂_2 (Sob.axisCut n) = 0`. -/
def axisCutW (n : ℕ) (y : Space) : ℝ :=
  2 * ((n : ℝ) + 1) ^ 2 * deriv Sob.axisEta (((n : ℝ) + 1) ^ 2 * Sob.axisQ y)

/-- Multiplication of a phase-space field by a function of `y`. -/
def ySmul (g : Space → ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := fun p => g p.2 • Φ p

/-- The horizontal Euler operator `E_h Φ = y₀ ∂₀Φ + y₁ ∂₁Φ` (`= ϱ ∂_ϱ Φ` off the axis). -/
def hEuler (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => p.2 0 • dy 0 Φ p + p.2 1 • dy 1 Φ p

/-- `T_h F = ∂₀(y₀ F) + ∂₁(y₁ F)`, the transpose of `-E_h`. -/
def hEulerT (F : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => dy 0 (fun q => q.2 0 • F q) p + dy 1 (fun q => q.2 1 • F q) p

/-- `ϱ F`. -/
def rhoT (F : ℝ × Space → CVec3) : ℝ × Space → CVec3 := fun p => Axi.ϱ p.2 • F p

/-! ## Leaves -/

/-- **Leaf `T09/6b/3`** (Leibniz rule for the cut test).  For smooth `Φ`,
`Δ(aₙΦ) = aₙΔΦ + wₙ E_hΦ + T_h(wₙΦ)`.  Proof: `∂_j(gΦ) = (∂_j g)Φ + g ∂_jΦ` (`fderiv_smul`, `g` a
function of `y`); `∂_j aₙ = wₙ y_j` for `j = 0, 1` and `∂_2 aₙ = 0` (`fderiv_axisCut_eq`; smoothness
`Sob.contDiff_axisCut`, `contDiff_axisCutW`);
so `Δ(aₙΦ) = (Σ_{j<2} ∂_j(wₙy_j))Φ + 2wₙE_hΦ + aₙΔΦ` and
`T_h(wₙΦ) = (Σ_{j<2} ∂_j(wₙy_j))Φ + wₙE_hΦ`. -/
def OffCutLeibniz : Prop :=
  ∀ (n : ℕ) (Φ : ℝ × Space → CVec3), ContDiff ℝ ∞ Φ → ∀ p : ℝ × Space,
    lapT (ySmul (Sob.axisCut n) Φ) p =
      ySmul (Sob.axisCut n) (lapT Φ) p +
        (axisCutW n p.2 • hEuler Φ p + hEulerT (ySmul (axisCutW n) Φ) p)

/-- **Leaf `T09/6b/4`** (Hölder on a shrinking tube; SP 1902-1911: `‖N_v f‖_{Y_r} = (πR²)^{1/r}
‖f‖_{H_r}`).  If `‖Gₙ‖ ≤ C(n+1)` on the slab and `Gₙ` vanishes off the tube
`Tₙ = {(n+1)² q ≤ 2, ‖y‖ ≤ Rad}` (`q = Sob.axisQ = y₀² + y₁²`), then `⟪Gₙ, N_v f⟫ → 0` for `f ∈ H_r`, `r > 2`.  Proof: replace
`f` by a measurable periodic representative (`pairCont_rep`, `Tasks/DriftNvC/PairCont.lean`); by
Hölder (`holder_abstract`, `holder_integral`, `Tasks/DriftNvC/PairCont/HolderBound.lean`) with the
majorant `C(n+1)‖dotL‖ 1_{Tₙ}`,
`|⟪Gₙ, N_v f⟫| ≤ K (n+1) (P |Tₙ|)^{1/r'} ‖N_v f‖_{Y_r}` (`r' = r/(r-1)`); `Tₙ` lies in the box
`Sob.axisBox (2/(n+1)) Rad` (`|y₀|, |y₁| ≤ 2/(n+1)` as in the proof of `Sob.axisCut_deriv_bound`,
`|y₂| ≤ ‖y‖`; `Sob.mem_axisBox`) of volume `(4/(n+1))² (2 Rad)` (`Sob.volume_axisBox`), and `‖N_v f‖_{Y_r} < ∞` (`phaseLpNorm_NvC`);
so the bound is `K' (n+1)^{1 - 2/r'} = K'(n+1)^{2/r - 1} → 0`. -/
def TubeSmall : Prop :=
  ∀ (c ε r : ℝ) (f : CProf) (G : ℕ → ℝ × Space → CVec3) (C Rad : ℝ), 0 < c → 0 < ε → 2 < r →
    InHr c r f → (∀ n, Measurable (G n)) →
    (∀ (n : ℕ), ∀ τ ∈ Icc (0 : ℝ) (2 * ε * c), ∀ y : Space, ‖G n (τ, y)‖ ≤ C * ((n : ℝ) + 1)) →
    (∀ (n : ℕ) (τ : ℝ) (y : Space),
      (2 < ((n : ℝ) + 1) ^ 2 * Sob.axisQ y ∨ Rad < ‖y‖) → G n (τ, y) = 0) →
    Tendsto (fun n => pairF (2 * ε * c) (G n) (NvC ε⁻¹ f)) atTop (𝓝 0)

/-- **Leaf `T09/6b/5`** (additivity of the pairing in the test).  For phase tests `Φ, Ψ` and
`f ∈ H_r` the two integrands are integrable on the slab `(0, P] × ℝ³` (`phase_holder_bound`,
after `pairCont_rep`), so `phaseInt_eq_slab` and `integral_add` apply. -/
def PairNvCAdd : Prop :=
  ∀ (c r ε : ℝ) (f : CProf) (Φ Ψ : ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → InHr c r f →
    IsPhaseTest (2 * ε * c) Φ → IsPhaseTest (2 * ε * c) Ψ →
    pairF (2 * ε * c) (Φ + Ψ) (NvC ε⁻¹ f) =
      pairF (2 * ε * c) Φ (NvC ε⁻¹ f) + pairF (2 * ε * c) Ψ (NvC ε⁻¹ f)

/-- **Leaf `T09/6b/6`** (SP 1919-1921: `∂_ρ(√s b) = s Q_ε b`, so `E_h N_v b = ϱ ∂_ϱ N_v b =
ϱ N_v(√s Q_ε b)` off the axis): for graph data and an off-axis phase test `F`,
`⟪T_h F, N_v b⟫ = -⟪ϱ F, N_v(√s Q_ε b)⟫`.  Decomposed in `Sub/PartIIb_T09_6b_6.lean` (classical
identity for nice `b`, window approximation, fixed cutoff, locality). -/
def RadialIBP : Prop :=
  ∀ (c ε r ν : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < c → 0 < ε → 2 < r →
    LapData c r ε ν b Qb Eb Q2b E2b → ∀ (δ : ℝ) (F : ℝ × Space → CVec3),
      OffAxisTest (2 * ε * c) δ F →
      pairF (2 * ε * c) (hEulerT F) (NvC ε⁻¹ b) =
        -pairF (2 * ε * c) (rhoT F) (NvC ε⁻¹ (sqrtS Qb))

/-! ## Elementary facts -/

theorem isPhaseTest_ySmul {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) : IsPhaseTest P (ySmul g Φ) where
  smooth := (hg.comp contDiff_snd).smul hΦ.smooth
  periodic τ y := by simp [ySmul, hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [ySmul, hR τ y hy]⟩

theorem isPhaseTest_hEuler {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (hEuler Φ) := by
  have h : hEuler Φ = (fun p => p.2 0 • dy 0 Φ p) + (fun p => p.2 1 • dy 1 Φ p) := by
    funext p; rfl
  rw [h]
  exact ((hΦ.dy 0).coord_smul 0).add ((hΦ.dy 1).coord_smul 1)

theorem isPhaseTest_hEulerT {P : ℝ} {F : ℝ × Space → CVec3} (hF : IsPhaseTest P F) :
    IsPhaseTest P (hEulerT F) := by
  have h : hEulerT F = dy 0 (fun q => q.2 0 • F q) + dy 1 (fun q => q.2 1 • F q) := by
    funext p; rfl
  rw [h]
  exact ((hF.coord_smul 0).dy 0).add ((hF.coord_smul 1).dy 1)

theorem dotL_rsmul_left (a : ℝ) (v w : CVec3) : dotL (a • v) w = (a : ℂ) * dotL v w := by
  rw [dotL_apply, dotL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

theorem dotL_rsmul_right (a : ℝ) (v w : CVec3) : dotL v (a • w) = (a : ℂ) * dotL v w := by
  rw [dotL_apply, dotL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

/-- Real scalars come out of the pairing (no integrability needed). -/
theorem pairF_real_smul (P a : ℝ) (Φ u : ℝ × Space → CVec3) :
    pairF P (a • Φ) u = (a : ℂ) * pairF P Φ u := by
  unfold pairF phaseInt
  simp only [Pi.smul_apply, dotL_rsmul_left, integral_const_mul, Complex.real_smul]
  ring

theorem abs_y0_le_rho (y : Space) : |y 0| ≤ Axi.ϱ y := by
  unfold Axi.ϱ
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 1)])

theorem abs_y1_le_rho (y : Space) : |y 1| ≤ Axi.ϱ y := by
  unfold Axi.ϱ
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 0)])

theorem axisQ_eq_rho_sq (y : Space) : Sob.axisQ y = Axi.ϱ y ^ 2 := by
  rw [Axi.ϱ_sq]
  unfold Sob.axisQ
  ring

theorem rho_lt_imp (n : ℕ) (y : Space) (h : Axi.ϱ y < 1 / ((n : ℝ) + 1)) :
    ((n : ℝ) + 1) ^ 2 * Sob.axisQ y < 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h0 := Axi.ϱ_nonneg y
  have h1 : ((n : ℝ) + 1) * Axi.ϱ y < 1 := by
    rw [lt_div_iff₀ hn] at h
    linarith
  have h2 : (((n : ℝ) + 1) * Axi.ϱ y) ^ 2 < 1 :=
    pow_lt_one₀ (mul_nonneg hn.le h0) h1 two_ne_zero
  rw [mul_pow, ← axisQ_eq_rho_sq] at h2
  exact h2

/-! ## The cutoff (`Sob.axisCut`, `Lib/Sobolev/Axis.lean`) -/

theorem contDiff_axisCutW (n : ℕ) : ContDiff ℝ ∞ (axisCutW n) := by
  have hd : ContDiff ℝ ∞ (deriv Sob.axisEta) :=
    (contDiff_infty_iff_deriv.1 Sob.contDiff_axisEta).2
  exact contDiff_const.mul (hd.comp (contDiff_const.mul Sob.contDiff_axisQ))

theorem axisCut_eq_zero_of {n : ℕ} {y : Space} (h : ((n : ℝ) + 1) ^ 2 * Sob.axisQ y < 1) :
    Sob.axisCut n y = 0 :=
  Sob.axisEta_eq_zero h.le

theorem axisCutW_eq_zero_of_lt {n : ℕ} {y : Space} (h : ((n : ℝ) + 1) ^ 2 * Sob.axisQ y < 1) :
    axisCutW n y = 0 := by
  simp [axisCutW, Sob.deriv_axisEta_eq_zero (Or.inl h)]

theorem axisCut_eq_one_of {n : ℕ} {y : Space} (h : 2 < ((n : ℝ) + 1) ^ 2 * Sob.axisQ y) :
    Sob.axisCut n y = 1 :=
  Sob.axisEta_eq_one h.le

theorem axisCutW_eq_zero_of_gt {n : ℕ} {y : Space} (h : 2 < ((n : ℝ) + 1) ^ 2 * Sob.axisQ y) :
    axisCutW n y = 0 := by
  simp [axisCutW, Sob.deriv_axisEta_eq_zero (Or.inr h)]

/-- `∂_v aₙ = wₙ (y₀v₀ + y₁v₁)`. -/
theorem fderiv_axisCut_eq (n : ℕ) (y v : Space) :
    fderiv ℝ (Sob.axisCut n) y v = axisCutW n y * (y 0 * v 0 + y 1 * v 1) := by
  rw [Sob.fderiv_axisCut_apply]
  simp only [axisCutW]
  ring

/-- `|wₙ| ϱ ≤ M (n+1)`: `wₙ = 0` unless `(n+1)²ϱ² ≤ 2`, and then `(n+1)ϱ ≤ 3/2`. -/
theorem axisCutW_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (y : Space),
    |axisCutW n y| * Axi.ϱ y ≤ M * ((n : ℝ) + 1) := by
  obtain ⟨B, hB0, hB⟩ := Sob.exists_bound_deriv_axisEta
  refine ⟨3 * B, by positivity, fun n y => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hϱ := Axi.ϱ_nonneg y
  by_cases h : 2 < ((n : ℝ) + 1) ^ 2 * Sob.axisQ y
  · rw [axisCutW_eq_zero_of_gt h, abs_zero, zero_mul]
    positivity
  · push Not at h
    have h2 : (((n : ℝ) + 1) * Axi.ϱ y) ^ 2 ≤ 2 := by
      rw [mul_pow, ← axisQ_eq_rho_sq]
      exact h
    have hx : 0 ≤ ((n : ℝ) + 1) * Axi.ϱ y := mul_nonneg hn.le hϱ
    have h3 : ((n : ℝ) + 1) * Axi.ϱ y ≤ 3 / 2 := by nlinarith
    have hw : |axisCutW n y| ≤ 2 * ((n : ℝ) + 1) ^ 2 * B := by
      unfold axisCutW
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1) ^ 2)]
      exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
    calc |axisCutW n y| * Axi.ϱ y ≤ 2 * ((n : ℝ) + 1) ^ 2 * B * Axi.ϱ y :=
          mul_le_mul_of_nonneg_right hw hϱ
      _ = 2 * B * ((n : ℝ) + 1) * (((n : ℝ) + 1) * Axi.ϱ y) := by ring
      _ ≤ 2 * B * ((n : ℝ) + 1) * (3 / 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 * B * ((n : ℝ) + 1) := by ring

/-- A test multiplied by a smooth function of `y` vanishing for `(n+1)² q < 1` is off the axis. -/
theorem offAxis_ySmul {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (n : ℕ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg0 : ∀ y : Space, ((n : ℝ) + 1) ^ 2 * Sob.axisQ y < 1 → g y = 0) :
    OffAxisTest P (1 / ((n : ℝ) + 1)) (ySmul g Φ) :=
  ⟨isPhaseTest_ySmul hΦ hg, by positivity, fun τ y hy => by
    simp [ySmul, hg0 y (rho_lt_imp n y hy)]⟩

/-- `⟪aₙΨ, N_v f⟫ → ⟪Ψ, N_v f⟫`: the difference `⟪(1 - aₙ)Ψ, N_v f⟫` is a tube term. -/
theorem cutLimit (hT : TubeSmall) (hAdd : PairNvCAdd) {c ε r : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r) {f : CProf} (hf : InHr c r f)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest (2 * ε * c) Ψ) :
    Tendsto (fun n : ℕ => pairF (2 * ε * c) (ySmul (Sob.axisCut n) Ψ) (NvC ε⁻¹ f)) atTop
      (𝓝 (pairF (2 * ε * c) Ψ (NvC ε⁻¹ f))) := by
  obtain ⟨C, Rad, hC0, -, hRad, hCb⟩ := phaseTest_bound (2 * ε * c) Ψ hΨ
  have hr1 : 1 < r := by linarith
  have hGs : ∀ n : ℕ, IsPhaseTest (2 * ε * c) (ySmul (fun y => 1 - Sob.axisCut n y) Ψ) :=
    fun n => isPhaseTest_ySmul hΨ (contDiff_const.sub (Sob.contDiff_axisCut n))
  have hsplit : ∀ n : ℕ, pairF (2 * ε * c) Ψ (NvC ε⁻¹ f) =
      pairF (2 * ε * c) (ySmul (Sob.axisCut n) Ψ) (NvC ε⁻¹ f) +
        pairF (2 * ε * c) (ySmul (fun y => 1 - Sob.axisCut n y) Ψ) (NvC ε⁻¹ f) := by
    intro n
    have e : Ψ = ySmul (Sob.axisCut n) Ψ + ySmul (fun y => 1 - Sob.axisCut n y) Ψ := by
      funext p
      simp only [Pi.add_apply, ySmul]
      rw [← add_smul]
      simp
    conv_lhs => rw [e]
    exact hAdd c r ε f _ _ hc hε hr1 hf (isPhaseTest_ySmul hΨ (Sob.contDiff_axisCut n)) (hGs n)
  have hG0 : Tendsto (fun n : ℕ => pairF (2 * ε * c) (ySmul (fun y => 1 - Sob.axisCut n y) Ψ)
      (NvC ε⁻¹ f)) atTop (𝓝 0) := by
    refine hT c ε r f (fun n => ySmul (fun y => 1 - Sob.axisCut n y) Ψ) C Rad hc hε hr hf
      (fun n => (hGs n).continuous.measurable) ?_ ?_
    · intro n τ hτ y
      have hab : |1 - Sob.axisCut n y| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [Sob.axisCut_nonneg n y, Sob.axisCut_le_one n y]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := n.cast_nonneg (α := ℝ)
        linarith
      calc ‖ySmul (fun y => 1 - Sob.axisCut n y) Ψ (τ, y)‖ =
            |1 - Sob.axisCut n y| * ‖Ψ (τ, y)‖ := by
            simp only [ySmul, norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * C := mul_le_mul hab (hCb τ hτ y) (norm_nonneg _) zero_le_one
        _ = C * 1 := by ring
        _ ≤ C * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hn1 hC0
    · intro n τ y h
      rcases h with h | h
      · simp [ySmul, axisCut_eq_one_of h]
      · simp [ySmul, hRad τ y h]
  have e : (fun n : ℕ => pairF (2 * ε * c) (ySmul (Sob.axisCut n) Ψ) (NvC ε⁻¹ f)) =
      fun n => pairF (2 * ε * c) Ψ (NvC ε⁻¹ f) -
        pairF (2 * ε * c) (ySmul (fun y => 1 - Sob.axisCut n y) Ψ) (NvC ε⁻¹ f) := by
    funext n
    rw [hsplit n]
    ring
  rw [e]
  simpa using (tendsto_const_nhds (x := pairF (2 * ε * c) Ψ (NvC ε⁻¹ f))).sub hG0

/-! ## Assembly -/

/-- **`LapAxisRemove` from the leaves.** -/
theorem lapAxisRemove_of (hLb : OffCutLeibniz) (hT : TubeSmall) (hAdd : PairNvCAdd)
    (hRad : RadialIBP) : LapAxisRemove := by
  intro c ε r ν b Qb Eb Q2b E2b hc hε hr hd hoff Φ hΦ
  have hr1 : 1 < r := by linarith
  obtain ⟨M, hM0, hM⟩ := axisCutW_bound
  -- the cut tests are off the axis, so the identity holds for them
  have hid : ∀ n : ℕ, pairF (2 * ε * c) (nuLapT ν (ySmul (Sob.axisCut n) Φ)) (NvC ε⁻¹ b) =
      pairF (2 * ε * c) (ySmul (Sob.axisCut n) Φ) (NvC ε⁻¹ (lapProf ν ε b Q2b E2b)) := fun n =>
    hoff _ _ (offAxis_ySmul hΦ n (Sob.contDiff_axisCut n) (fun y hy => axisCut_eq_zero_of hy))
  -- right-hand side
  have hlimR := cutLimit hT hAdd hc hε hr hd.inLap hΦ
  -- left-hand side: Leibniz rule and the radial integration by parts
  have hWoff : ∀ n : ℕ, OffAxisTest (2 * ε * c) (1 / ((n : ℝ) + 1)) (ySmul (axisCutW n) Φ) :=
    fun n => offAxis_ySmul hΦ n (contDiff_axisCutW n) (fun y hy => axisCutW_eq_zero_of_lt hy)
  have hdecomp : ∀ n : ℕ, pairF (2 * ε * c) (nuLapT ν (ySmul (Sob.axisCut n) Φ)) (NvC ε⁻¹ b) =
      (ν : ℂ) * (pairF (2 * ε * c) (ySmul (Sob.axisCut n) (lapT Φ)) (NvC ε⁻¹ b) +
        (pairF (2 * ε * c) (ySmul (axisCutW n) (hEuler Φ)) (NvC ε⁻¹ b) -
          pairF (2 * ε * c) (rhoT (ySmul (axisCutW n) Φ)) (NvC ε⁻¹ (sqrtS Qb)))) := by
    intro n
    have e1 : nuLapT ν (ySmul (Sob.axisCut n) Φ) = ν • (ySmul (Sob.axisCut n) (lapT Φ) +
        (ySmul (axisCutW n) (hEuler Φ) + hEulerT (ySmul (axisCutW n) Φ))) := by
      funext p
      simp only [nuLapT, Pi.smul_apply, Pi.add_apply]
      rw [hLb n Φ hΦ.smooth p]
      rfl
    have hA1 : IsPhaseTest (2 * ε * c) (ySmul (Sob.axisCut n) (lapT Φ)) :=
      isPhaseTest_ySmul hΦ.lapT (Sob.contDiff_axisCut n)
    have hA2 : IsPhaseTest (2 * ε * c) (ySmul (axisCutW n) (hEuler Φ)) :=
      isPhaseTest_ySmul (isPhaseTest_hEuler hΦ) (contDiff_axisCutW n)
    have hA3 : IsPhaseTest (2 * ε * c) (hEulerT (ySmul (axisCutW n) Φ)) :=
      isPhaseTest_hEulerT (hWoff n).1
    rw [e1, pairF_real_smul, hAdd c r ε b _ _ hc hε hr1 hd.div.inHr hA1 (hA2.add hA3),
      hAdd c r ε b _ _ hc hε hr1 hd.div.inHr hA2 hA3,
      hRad c ε r ν b Qb Eb Q2b E2b hc hε hr hd _ _ (hWoff n)]
    ring
  -- the three limits
  have L1 := cutLimit hT hAdd hc hε hr hd.div.inHr hΦ.lapT
  obtain ⟨C0, R0, hC00, -, hR0, hC0b⟩ := phaseTest_bound (2 * ε * c) (dy 0 Φ) (hΦ.dy 0)
  obtain ⟨C1, R1, hC10, -, hR1, hC1b⟩ := phaseTest_bound (2 * ε * c) (dy 1 Φ) (hΦ.dy 1)
  obtain ⟨CΦ, RΦ, hCΦ0, -, hRΦ, hCΦb⟩ := phaseTest_bound (2 * ε * c) Φ hΦ
  have L2 : Tendsto (fun n : ℕ => pairF (2 * ε * c) (ySmul (axisCutW n) (hEuler Φ))
      (NvC ε⁻¹ b)) atTop (𝓝 0) := by
    refine hT c ε r b (fun n => ySmul (axisCutW n) (hEuler Φ)) (M * (C0 + C1)) (max R0 R1)
      hc hε hr hd.div.inHr
      (fun n => (isPhaseTest_ySmul (isPhaseTest_hEuler hΦ) (contDiff_axisCutW n)).continuous.measurable)
      ?_ ?_
    · intro n τ hτ y
      have hw := hM n y
      have hy0 := abs_y0_le_rho y
      have hy1 := abs_y1_le_rho y
      have hd0 := hC0b τ hτ y
      have hd1 := hC1b τ hτ y
      have hnorm : ‖ySmul (axisCutW n) (hEuler Φ) (τ, y)‖ ≤
          |axisCutW n y| * (|y 0| * C0 + |y 1| * C1) := by
        simp only [ySmul, hEuler, norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (abs_nonneg _)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact add_le_add (mul_le_mul_of_nonneg_left hd0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hd1 (abs_nonneg _))
      calc ‖ySmul (axisCutW n) (hEuler Φ) (τ, y)‖
          ≤ |axisCutW n y| * (|y 0| * C0 + |y 1| * C1) := hnorm
        _ ≤ |axisCutW n y| * (Axi.ϱ y * C0 + Axi.ϱ y * C1) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_right hy0 hC00
          · exact mul_le_mul_of_nonneg_right hy1 hC10
        _ = (|axisCutW n y| * Axi.ϱ y) * (C0 + C1) := by ring
        _ ≤ (M * ((n : ℝ) + 1)) * (C0 + C1) :=
          mul_le_mul_of_nonneg_right hw (add_nonneg hC00 hC10)
        _ = M * (C0 + C1) * ((n : ℝ) + 1) := by ring
    · intro n τ y h
      rcases h with h | h
      · simp [ySmul, axisCutW_eq_zero_of_gt h]
      · have h0 : dy 0 Φ (τ, y) = 0 := hR0 τ y (lt_of_le_of_lt (le_max_left _ _) h)
        have h1 : dy 1 Φ (τ, y) = 0 := hR1 τ y (lt_of_le_of_lt (le_max_right _ _) h)
        simp [ySmul, hEuler, h0, h1]
  have L3 : Tendsto (fun n : ℕ => pairF (2 * ε * c) (rhoT (ySmul (axisCutW n) Φ))
      (NvC ε⁻¹ (sqrtS Qb))) atTop (𝓝 0) := by
    refine hT c ε r (sqrtS Qb) (fun n => rhoT (ySmul (axisCutW n) Φ)) (M * CΦ) RΦ hc hε hr
      hd.div.inQ (fun n => ?_) ?_ ?_
    · exact ((Axi.continuous_ϱ.comp continuous_snd).smul
        (isPhaseTest_ySmul hΦ (contDiff_axisCutW n)).continuous).measurable
    · intro n τ hτ y
      have hw := hM n y
      have hΦb := hCΦb τ hτ y
      have hϱ := Axi.ϱ_nonneg y
      calc ‖rhoT (ySmul (axisCutW n) Φ) (τ, y)‖ = (|axisCutW n y| * Axi.ϱ y) * ‖Φ (τ, y)‖ := by
            simp only [rhoT, ySmul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hϱ]
            ring
        _ ≤ (M * ((n : ℝ) + 1)) * CΦ :=
          mul_le_mul hw hΦb (norm_nonneg _) (mul_nonneg hM0 (by positivity))
        _ = M * CΦ * ((n : ℝ) + 1) := by ring
    · intro n τ y h
      rcases h with h | h
      · simp [rhoT, ySmul, axisCutW_eq_zero_of_gt h]
      · simp [rhoT, ySmul, hRΦ τ y h]
  have hlimL : Tendsto (fun n : ℕ => pairF (2 * ε * c) (nuLapT ν (ySmul (Sob.axisCut n) Φ))
      (NvC ε⁻¹ b)) atTop (𝓝 (pairF (2 * ε * c) (nuLapT ν Φ) (NvC ε⁻¹ b))) := by
    simp only [hdecomp]
    have h := (L1.add (L2.sub L3)).const_mul (ν : ℂ)
    simp only [sub_zero, add_zero] at h
    rw [show nuLapT ν Φ = ν • lapT Φ from rfl, pairF_real_smul]
    exact h
  simp only [hid] at hlimL
  exact tendsto_nhds_unique hlimL hlimR

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.lapAxisRemove_of
