import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6

/-!
# Decomposition of `XSStreamPsi` (task `PartIII-b:C/srcL/6/3`)

Source 4178-4186, 4917-4937: smoothness of the outward primitive
`Ψ_Z(y) = -∫_{r}^∞ ρ Z_z(rayPt y ρ) dρ` on `{b < r²}`.  After the substitution `ρ = r σ` the
domain is `σ ∈ (1,∞)`, and the integrand `σ Z_z(σ y₁, σ y₂, y₃)` is differentiated under the
integral sign.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The horizontal dilation `y ↦ (σ y₁, σ y₂, y₃)` (so `rayPt y (cylR y * σ) = scaleXY σ y`). -/
def scaleXY (σ : ℝ) (y : Vec3) : Vec3 := ![σ * y 0, σ * y 1, y 2]

/-- Substitution `ρ = r σ` (source 4178-4186). -/
def XSPsiReparam : Prop :=
  ∀ (Z : Vec3 → Vec3) (y : Vec3), 0 < cylR y →
    streamPsi Z y = -(cylR y) ^ 2 * ∫ σ in Ioi (1 : ℝ), σ * Z (scaleXY σ y) 2

/-- Differentiation under the integral sign on an open set, for families smooth only on that
set (the iterated parametric-integral theorem `Kernels.contDiffOn_integral` needs global
smoothness of each member; localise by a bump function to reduce to it). -/
def XSParamSmoothOpen : Prop :=
  ∀ (U : Set Vec3) (F : ℝ → Vec3 → ℝ), IsOpen U →
    (∀ σ ∈ Ioi (1 : ℝ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F σ) U) →
    (∀ (n : ℕ) (y : Vec3), y ∈ U →
      AEStronglyMeasurable (fun σ => iteratedFDeriv ℝ n (F σ) y) (volume.restrict (Ioi (1 : ℝ)))) →
    (∀ (n : ℕ), ∀ y ∈ U, ∃ s ∈ nhds y, ∃ g : ℝ → ℝ, IntegrableOn g (Ioi (1 : ℝ)) ∧
      ∀ σ ∈ Ioi (1 : ℝ), ∀ y' ∈ s, ‖iteratedFDeriv ℝ n (F σ) y'‖ ≤ g σ) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ σ in Ioi (1 : ℝ), F σ y) U

/-- Hypotheses of `XSStreamPsi` (smoothness and decay of `Z`). -/
def XSPsiHyp (b : ℝ) (Z : Vec3 → Vec3) : Prop :=
  0 < b ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2} ∧
  (∀ a : ℝ, b < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
      ‖iteratedFDeriv ℝ k Z w‖ ≤ C * (1 + ‖w‖) ^ (-(4 + (k : ℝ))))

/-- Each member `y ↦ σ Z_z(scaleXY σ y)`, `σ > 1`, is `C^∞` on `{b < r²}` (the dilation maps the
region into itself since `cylR (scaleXY σ y) = σ cylR y`). -/
def XSPsiFamSmooth : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), XSPsiHyp b Z → ∀ σ ∈ Ioi (1 : ℝ),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => σ * Z (scaleXY σ y) 2) {y | b < cylR y ^ 2}

/-- Measurability in `σ` of the iterated derivatives of the family at fixed `y` in the region
(for `σ > 1` they are `σ`-continuous: `D^n[Z ∘ scaleXY σ](y) = D^n Z (scaleXY σ y) ∘ (scaleXY-linear part)^n`). -/
def XSPsiFamMeas : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), XSPsiHyp b Z → ∀ (n : ℕ) (y : Vec3), b < cylR y ^ 2 →
    AEStronglyMeasurable
      (fun σ : ℝ => iteratedFDeriv ℝ n (fun y' => σ * Z (scaleXY σ y') 2) y)
      (volume.restrict (Ioi (1 : ℝ)))

/-- Local domination (source 4917-4937): `‖D^j_y[σ Z_z(scaleXY σ y)]‖ ≲ σ · σ^j (1+σ r)^{-(4+j)}
≲ σ^{-3}` locally uniformly in `y` (use `a` strictly between `b` and `cylR y ^ 2`, the dilation's
linear part has norm `≤ σ`, and the Leibniz/chain-rule bound
`ContinuousLinearMap.norm_iteratedFDeriv_comp_right_le`-type estimate; the integrable dominating
function is `C σ^{-3}` on `(1,∞)`). -/
def XSPsiDomination : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), XSPsiHyp b Z → ∀ (n : ℕ), ∀ y ∈ {y | b < cylR y ^ 2},
    ∃ s ∈ nhds y, ∃ g : ℝ → ℝ, IntegrableOn g (Ioi (1 : ℝ)) ∧
      ∀ σ ∈ Ioi (1 : ℝ), ∀ y' ∈ s,
        ‖iteratedFDeriv ℝ n (fun y'' => σ * Z (scaleXY σ y'') 2) y'‖ ≤ g σ

theorem rayPt_eq_scaleXY (y : Vec3) (σ : ℝ) (h : 0 < cylR y) :
    rayPt y (cylR y * σ) = scaleXY σ y := by
  unfold rayPt scaleXY
  ext i
  fin_cases i <;> simp <;> field_simp

theorem xsPsiReparam : XSPsiReparam := by
  intro Z y hy
  unfold streamPsi
  have h := MeasureTheory.integral_comp_mul_left_Ioi'
    (fun ρ : ℝ => ρ * Z (rayPt y ρ) 2) 1 hy
  simp only [mul_one] at h
  rw [← h]
  have : ∀ σ : ℝ, (cylR y * σ) * Z (rayPt y (cylR y * σ)) 2
      = cylR y * (σ * Z (scaleXY σ y) 2) := by
    intro σ; rw [rayPt_eq_scaleXY y σ hy]; ring
  simp_rw [this, MeasureTheory.integral_const_mul, smul_eq_mul]
  ring

theorem cylR_sq (y : Vec3) : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  unfold cylR; exact Real.sq_sqrt (by positivity)

/-- `XSStreamPsi` from the five pieces. -/
theorem neg_pow_two_aux (y : Vec3) : -(cylR y) ^ 2 = -(y 0 ^ 2 + y 1 ^ 2) := by
  rw [← cylR_sq y]

theorem xsStreamPsi_of (h1 : XSPsiReparam) (h2 : XSParamSmoothOpen) (h3 : XSPsiFamSmooth)
    (h4 : XSPsiFamMeas) (h5 : XSPsiDomination) : XSStreamPsi := by
  intro b Z hb hZ hdec
  have hH : XSPsiHyp b Z := ⟨hb, hZ, hdec⟩
  have hU : IsOpen {y : Vec3 | b < cylR y ^ 2} :=
    isOpen_lt continuous_const (continuous_cylR.pow 2)
  have hI := h2 {y : Vec3 | b < cylR y ^ 2} (fun σ y => σ * Z (scaleXY σ y) 2) hU
    (h3 b Z hH) (fun n y hy => h4 b Z hH n y hy) (fun n y hy => h5 b Z hH n y hy)
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vec3 => -(cylR y) ^ 2)
      {y | b < cylR y ^ 2} := by
    have : (fun y : Vec3 => -(cylR y) ^ 2) = fun y => -(y 0 ^ 2 + y 1 ^ 2) := by
      funext y; rw [neg_pow_two_aux y]
    rw [this]
    exact (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Vec3 => -(y 0 ^ 2 + y 1 ^ 2)).contDiffOn
  refine (hc.mul hI).congr ?_
  intro y hy
  have hpos : 0 < cylR y := by
    have h0 : 0 ≤ cylR y := Real.sqrt_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso; have := hy; simp only [mem_setOf_eq] at this; rw [← h] at this; nlinarith
  exact h1 Z y hpos

end UnforcedLeray.Short.PartIIIb.Concrete
