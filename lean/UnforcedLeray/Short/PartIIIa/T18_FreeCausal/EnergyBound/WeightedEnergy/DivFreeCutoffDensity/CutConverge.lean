import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/11`: `H¹(cell)` convergence of the cut-off fields

Target (`Sub/T18_3_1_1.lean`): `DfcCutConverge`. Uses `dfcCutPd` (`CutPd.lean`).
Source of record: `the November 2 reference manuscript`, lines 3541-3552.

Route: by `dfcCutPd` and `DfcPotential.pd0` (`∂_q θ = -φ₁`), the integrand equals a polynomial
`dfcConvE a a₁ a₂ ...` in `a = u_k(η)`, `a₁ = u_k'(η)`, `a₂ = u_k''(η)` and the eight fixed atoms
`φ₀, φ₁, ∂_qφ₀, ∂_ηφ₀, ∂_qφ₁, ∂_ηφ₁, θ, ∂_ηθ` at `x`. The polynomial is linear in
`(a - 1, a₁, a₂)`, so it tends to `0` pointwise. Domination: `0 ≤ u_k ≤ 1` and the uniform bounds
on `u_k'`, `u_k''` give `|a - 1|, |a₁|, |a₂| ≤ M`, hence the integrand is at most
`24 M² G(x)` with `G = φ₀² + φ₁² + |∇φ|² + θ² + (∂_ηθ)²`, which is integrable on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DfcCutConvAux

theorem apply0 (u : ℕ → ℝ → ℝ) (k : ℕ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    dfcCut u k φ θ y 0 = u k y.2 * φ y 0 + deriv (u k) y.2 * θ y := rfl

theorem apply1 (u : ℕ → ℝ → ℝ) (k : ℕ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    dfcCut u k φ θ y 1 = u k y.2 * φ y 1 := rfl

/-- Smoothness of the two components of the cut-off field. -/
theorem comp_smooth (u : ℕ → ℝ → ℝ) (hu : ∀ k, ContDiff ℝ ∞ (u k)) (k : ℕ)
    (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ fun x => φ x i)
    (hθ : ContDiff ℝ ∞ θ) (i : Fin 2) :
    ContDiff ℝ ∞ fun y => dfcCut u k φ θ y i := by
  have hdu : ContDiff ℝ ∞ (deriv (u k)) := (contDiff_infty_iff_deriv.mp (hu k)).2
  have hus : ContDiff ℝ ∞ (fun y : ℝ × ℝ => u k y.2) := (hu k).comp contDiff_snd
  have hdus : ContDiff ℝ ∞ (fun y : ℝ × ℝ => deriv (u k) y.2) := hdu.comp contDiff_snd
  have h0 : ContDiff ℝ ∞ fun y : ℝ × ℝ => dfcCut u k φ θ y 0 := by
    show ContDiff ℝ ∞ fun y : ℝ × ℝ => u k y.2 * φ y 0 + deriv (u k) y.2 * θ y
    exact (hus.mul (hφ 0)).add (hdus.mul hθ)
  have h1 : ContDiff ℝ ∞ fun y : ℝ × ℝ => dfcCut u k φ θ y 1 := by
    show ContDiff ℝ ∞ fun y : ℝ × ℝ => u k y.2 * φ y 1
    exact hus.mul (hφ 1)
  fin_cases i
  · exact h0
  · exact h1

/-- Continuity of a `∂_j` of a smooth function. -/
theorem pd_cont {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (j : Fin 2) :
    Continuous fun x => B0579.pd j g x := by
  unfold B0579.pd
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

theorem sq_four (p q r s : ℝ) : (p + q + r + s) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r),
    sq_nonneg (q - s), sq_nonneg (r - s)]

theorem sq_two (p q : ℝ) : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
  nlinarith [sq_nonneg (p - q)]

theorem sq_mul_le (c t M : ℝ) (hc : |c| ≤ M) : (c * t) ^ 2 ≤ M ^ 2 * t ^ 2 := by
  have h : c ^ 2 ≤ M ^ 2 := by
    have h0 : 0 ≤ |c| := abs_nonneg c
    nlinarith [sq_abs c]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg t)

theorem two_term (c₁ c₂ t₁ t₂ M : ℝ) (h₁ : |c₁| ≤ M) (h₂ : |c₂| ≤ M) :
    (c₁ * t₁ + c₂ * t₂) ^ 2 ≤ 2 * M ^ 2 * (t₁ ^ 2 + t₂ ^ 2) := by
  have h := sq_two (c₁ * t₁) (c₂ * t₂)
  have e1 := sq_mul_le c₁ t₁ M h₁
  have e2 := sq_mul_le c₂ t₂ M h₂
  nlinarith [h, e1, e2]

theorem four_term (c₁ c₂ c₃ c₄ t₁ t₂ t₃ t₄ M : ℝ) (h₁ : |c₁| ≤ M) (h₂ : |c₂| ≤ M)
    (h₃ : |c₃| ≤ M) (h₄ : |c₄| ≤ M) :
    (c₁ * t₁ + c₂ * t₂ + c₃ * t₃ + c₄ * t₄) ^ 2 ≤ 4 * M ^ 2 * (t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 + t₄ ^ 2) := by
  have h := sq_four (c₁ * t₁) (c₂ * t₂) (c₃ * t₃) (c₄ * t₄)
  have e1 := sq_mul_le c₁ t₁ M h₁
  have e2 := sq_mul_le c₂ t₂ M h₂
  have e3 := sq_mul_le c₃ t₃ M h₃
  have e4 := sq_mul_le c₄ t₄ M h₄
  nlinarith [h, e1, e2, e3, e4]

/-- The integrand as a polynomial in `a = u_k(η)`, `a₁ = u_k'(η)`, `a₂ = u_k''(η)` and the atoms
`f₀ = φ₀, f₁ = φ₁, g₀₀ = ∂_qφ₀, g₀₁ = ∂_ηφ₀, g₁₀ = ∂_qφ₁, g₁₁ = ∂_ηφ₁, th = θ, tg = ∂_ηθ`. -/
def dfcConvE (a a1 a2 f0 f1 g00 g01 g10 g11 th tg : ℝ) : ℝ :=
  (a * f0 + a1 * th - f0) ^ 2 + ((a * g00 + a1 * (-f1)) - g00) ^ 2 +
    (a1 * f0 + a * g01 + a2 * th + a1 * tg - g01) ^ 2 +
    ((a * f1 - f1) ^ 2 + ((a * g10 - g10) ^ 2 + (a1 * f1 + a * g11 - g11) ^ 2))

/-- The integrand of `DfcCutConverge` at `(k, x)`. -/
def dfcConvR (u : ℕ → ℝ → ℝ) (k : ℕ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 2, ((dfcCut u k φ θ x i - φ x i) ^ 2 +
    ∑ j : Fin 2, (B0579.pd j (fun y => dfcCut u k φ θ y i) x - B0579.pd j (fun y => φ y i) x) ^ 2)

/-- The dominating function `G = φ₀² + φ₁² + |∇φ|² + θ² + (∂_ηθ)²`. -/
def dfcConvG (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  φ x 0 ^ 2 + φ x 1 ^ 2 + B0579.pd 0 (fun y => φ y 0) x ^ 2 + B0579.pd 1 (fun y => φ y 0) x ^ 2 +
    B0579.pd 0 (fun y => φ y 1) x ^ 2 + B0579.pd 1 (fun y => φ y 1) x ^ 2 + θ x ^ 2 +
    B0579.pd 1 θ x ^ 2

theorem pointwise (a a1 a2 M f0 f1 g00 g01 g10 g11 th tg : ℝ) (ha : |a - 1| ≤ M)
    (ha1 : |a1| ≤ M) (ha2 : |a2| ≤ M) :
    dfcConvE a a1 a2 f0 f1 g00 g01 g10 g11 th tg ≤
      24 * M ^ 2 * (f0 ^ 2 + f1 ^ 2 + g00 ^ 2 + g01 ^ 2 + g10 ^ 2 + g11 ^ 2 + th ^ 2 + tg ^ 2) := by
  unfold dfcConvE
  have h1 := two_term (a - 1) a1 f0 th M ha ha1
  have h2 := two_term (a - 1) a1 g00 (-f1) M ha ha1
  have h3 := four_term a1 (a - 1) a2 a1 f0 g01 th tg M ha1 ha ha2 ha1
  have h4 := sq_mul_le (a - 1) f1 M ha
  have h5 := sq_mul_le (a - 1) g10 M ha
  have h6 := two_term a1 (a - 1) f1 g11 M ha1 ha
  nlinarith [h1, h2, h3, h4, h5, h6, mul_nonneg (sq_nonneg M) (sq_nonneg f0),
    mul_nonneg (sq_nonneg M) (sq_nonneg f1), mul_nonneg (sq_nonneg M) (sq_nonneg g00),
    mul_nonneg (sq_nonneg M) (sq_nonneg g01), mul_nonneg (sq_nonneg M) (sq_nonneg g10),
    mul_nonneg (sq_nonneg M) (sq_nonneg g11), mul_nonneg (sq_nonneg M) (sq_nonneg th),
    mul_nonneg (sq_nonneg M) (sq_nonneg tg)]

/-- The integrand is the polynomial `dfcConvE` (by `dfcCutPd` and `∂_qθ = -φ₁`). -/
theorem R_eq (u : ℕ → ℝ → ℝ) (hus : ∀ k, ContDiff ℝ ∞ (u k)) (φ : ℝ × ℝ → Fin 2 → ℝ)
    (θ : ℝ × ℝ → ℝ) (hφs : ∀ i, ContDiff ℝ ∞ fun x => φ x i) (hθs : ContDiff ℝ ∞ θ)
    (hθpd : ∀ x, B0579.pd 0 θ x = -φ x 1) (k : ℕ) (x : ℝ × ℝ) :
    dfcConvR u k φ θ x =
      dfcConvE (u k x.2) (deriv (u k) x.2) (deriv (deriv (u k)) x.2) (φ x 0) (φ x 1)
        (B0579.pd 0 (fun y => φ y 0) x) (B0579.pd 1 (fun y => φ y 0) x)
        (B0579.pd 0 (fun y => φ y 1) x) (B0579.pd 1 (fun y => φ y 1) x) (θ x) (B0579.pd 1 θ x) := by
  obtain ⟨e00, e10, e01, e11⟩ := dfcCutPd u hus φ θ hφs hθs k x
  unfold dfcConvR dfcConvE
  simp only [Fin.sum_univ_two]
  rw [e00, e10, e01, e11, hθpd x, DfcCutConvAux.apply0 u k φ θ x,
    DfcCutConvAux.apply1 u k φ θ x]
  ring

theorem R_le (u : ℕ → ℝ → ℝ) (M : ℝ) (hA : ∀ k t, |u k t - 1| ≤ M)
    (hA1 : ∀ k t, |deriv (u k) t| ≤ M) (hA2 : ∀ k t, |deriv (deriv (u k)) t| ≤ M)
    (hus : ∀ k, ContDiff ℝ ∞ (u k)) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ)
    (hφs : ∀ i, ContDiff ℝ ∞ fun x => φ x i) (hθs : ContDiff ℝ ∞ θ)
    (hθpd : ∀ x, B0579.pd 0 θ x = -φ x 1) (k : ℕ) (x : ℝ × ℝ) :
    dfcConvR u k φ θ x ≤ 24 * M ^ 2 * dfcConvG φ θ x := by
  rw [R_eq u hus φ θ hφs hθs hθpd k x]
  have h := pointwise (u k x.2) (deriv (u k) x.2) (deriv (deriv (u k)) x.2) M (φ x 0) (φ x 1)
    (B0579.pd 0 (fun y => φ y 0) x) (B0579.pd 1 (fun y => φ y 0) x)
    (B0579.pd 0 (fun y => φ y 1) x) (B0579.pd 1 (fun y => φ y 1) x) (θ x) (B0579.pd 1 θ x)
    (hA k x.2) (hA1 k x.2) (hA2 k x.2)
  unfold dfcConvG
  linarith [h]

theorem R_cont (u : ℕ → ℝ → ℝ) (hus : ∀ k, ContDiff ℝ ∞ (u k)) (φ : ℝ × ℝ → Fin 2 → ℝ)
    (θ : ℝ × ℝ → ℝ) (hφs : ∀ i, ContDiff ℝ ∞ fun x => φ x i) (hθs : ContDiff ℝ ∞ θ) (k : ℕ) :
    Continuous (dfcConvR u k φ θ) := by
  unfold dfcConvR
  apply continuous_finsetSum
  intro i _
  apply Continuous.add
  · apply Continuous.pow
    apply Continuous.sub
    · exact (comp_smooth u hus k φ θ hφs hθs i).continuous
    · exact (hφs i).continuous
  · apply continuous_finsetSum
    intro j _
    apply Continuous.pow
    apply Continuous.sub
    · exact pd_cont (comp_smooth u hus k φ θ hφs hθs i) j
    · exact pd_cont (hφs i) j

/-- A continuous function of `p` tending to the value `0` at `(1,0,0)` along `T`. -/
theorem tendsto_of_cont_zero (F : ℝ × ℝ × ℝ → ℝ) (hF : Continuous F) (h0 : F (1, 0, 0) = 0)
    {T : ℕ → ℝ × ℝ × ℝ} (hT : Tendsto T atTop (𝓝 (1, 0, 0))) :
    Tendsto (fun k => F (T k)) atTop (𝓝 0) := by
  have h := (hF.tendsto (1, 0, 0)).comp hT
  rw [h0] at h
  exact h

theorem R_tendsto (u : ℕ → ℝ → ℝ) (hu : DfcScaled u) (φ : ℝ × ℝ → Fin 2 → ℝ)
    (θ : ℝ × ℝ → ℝ) (hφs : ∀ i, ContDiff ℝ ∞ fun x => φ x i) (hθs : ContDiff ℝ ∞ θ)
    (hθpd : ∀ x, B0579.pd 0 θ x = -φ x 1) (x : ℝ × ℝ) :
    Tendsto (fun k => dfcConvR u k φ θ x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => u k x.2) atTop (𝓝 1) := by
    refine (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' ?_
    exact (hu.lim_one x.2).mono fun k hk => hk.symm
  have T : Tendsto (fun k => (u k x.2, deriv (u k) x.2, deriv (deriv (u k)) x.2)) atTop
      (𝓝 (1, 0, 0)) :=
    h1.prodMk_nhds ((hu.lim_d1 x.2).prodMk_nhds (hu.lim_d2 x.2))
  have hg : Continuous (fun p : ℝ × ℝ × ℝ =>
      dfcConvE p.1 p.2.1 p.2.2 (φ x 0) (φ x 1)
        (B0579.pd 0 (fun y => φ y 0) x) (B0579.pd 1 (fun y => φ y 0) x)
        (B0579.pd 0 (fun y => φ y 1) x) (B0579.pd 1 (fun y => φ y 1) x) (θ x) (B0579.pd 1 θ x)) := by
    unfold dfcConvE
    fun_prop
  have h0 : (fun p : ℝ × ℝ × ℝ =>
      dfcConvE p.1 p.2.1 p.2.2 (φ x 0) (φ x 1)
        (B0579.pd 0 (fun y => φ y 0) x) (B0579.pd 1 (fun y => φ y 0) x)
        (B0579.pd 0 (fun y => φ y 1) x) (B0579.pd 1 (fun y => φ y 1) x) (θ x) (B0579.pd 1 θ x))
      (1, 0, 0) = 0 := by
    unfold dfcConvE
    ring
  have h2 := tendsto_of_cont_zero _ hg h0 T
  exact Tendsto.congr (fun k => (R_eq u hu.smooth φ θ hφs hθs hθpd k x).symm) h2

end DfcCutConvAux

/-- **`H¹(cell)` convergence of the cut-off fields** (`PartIII-a:T18/3/1/1/11`). Proves
`DfcCutConverge` by dominated convergence (`tendsto_lintegral_of_dominated_convergence`). -/
theorem dfcCutConverge : UnforcedLeray.Short.IIIa.DfcCutConverge := by
  unfold UnforcedLeray.Short.IIIa.DfcCutConverge
  intro c hc u hu φ θ hφ hθ
  obtain ⟨C1, hC1⟩ := hu.bound1
  obtain ⟨C2, hC2⟩ := hu.bound2
  have hC1nn : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0 0)
  have hC2nn : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0 0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + C1 + C2 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith
  have hA : ∀ k t, |u k t - 1| ≤ M := by
    intro k t
    have h0 := hu.range k t
    rw [abs_le]
    constructor <;> linarith [h0.1, h0.2]
  have hA1 : ∀ k t, |deriv (u k) t| ≤ M :=
    fun k t => (hC1 k t).trans (by rw [hMdef]; linarith)
  have hA2 : ∀ k t, |deriv (deriv (u k)) t| ≤ M :=
    fun k t => (hC2 k t).trans (by rw [hMdef]; linarith)
  have hφs := hφ.smooth
  have hθs := hθ.smooth
  have hθpd := hθ.pd0
  have IG : Integrable (DfcCutConvAux.dfcConvG φ θ) (volume.restrict (B0579.cell c)) := by
    unfold DfcCutConvAux.dfcConvG
    exact ((((((((hφ.l2 0).integrable_sq.add (hφ.l2 1).integrable_sq).add
      (hφ.l2grad 0 0).integrable_sq).add (hφ.l2grad 0 1).integrable_sq).add
      (hφ.l2grad 1 0).integrable_sq).add (hφ.l2grad 1 1).integrable_sq).add
      hθ.l2.integrable_sq).add hθ.l2_pd1.integrable_sq)
  have hfin : ∫⁻ x in B0579.cell c, ENNReal.ofReal (24 * M ^ 2 * DfcCutConvAux.dfcConvG φ θ x) ≠ ⊤ :=
    ((IG.const_mul (24 * M ^ 2)).lintegral_lt_top).ne
  have hmeas : ∀ k, Measurable (fun x => ENNReal.ofReal (DfcCutConvAux.dfcConvR u k φ θ x)) :=
    fun k => ENNReal.measurable_ofReal.comp
      (DfcCutConvAux.R_cont u hu.smooth φ θ hφs hθs k).measurable
  have hbound : ∀ k, (fun x => ENNReal.ofReal (DfcCutConvAux.dfcConvR u k φ θ x)) ≤ᵐ[volume.restrict (B0579.cell c)]
      (fun x => ENNReal.ofReal (24 * M ^ 2 * DfcCutConvAux.dfcConvG φ θ x)) :=
    fun k => ae_of_all _ (fun x =>
      ENNReal.ofReal_le_ofReal (DfcCutConvAux.R_le u M hA hA1 hA2 hu.smooth φ θ hφs hθs hθpd k x))
  have hlim : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Tendsto (fun k => ENNReal.ofReal (DfcCutConvAux.dfcConvR u k φ θ x)) atTop (𝓝 0) :=
    ae_of_all _ (fun x => by
      have h := ENNReal.tendsto_ofReal (DfcCutConvAux.R_tendsto u hu φ θ hφs hθs hθpd x)
      rwa [ENNReal.ofReal_zero] at h)
  have hD : Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (DfcCutConvAux.dfcConvR u k φ θ x))
      atTop (𝓝 (∫⁻ _ in B0579.cell c, (0 : ℝ≥0∞))) :=
    tendsto_lintegral_of_dominated_convergence
      (fun x => ENNReal.ofReal (24 * M ^ 2 * DfcCutConvAux.dfcConvG φ θ x)) hmeas hbound hfin hlim
  rw [lintegral_zero] at hD
  exact hD

end UnforcedLeray.Short.IIIa
