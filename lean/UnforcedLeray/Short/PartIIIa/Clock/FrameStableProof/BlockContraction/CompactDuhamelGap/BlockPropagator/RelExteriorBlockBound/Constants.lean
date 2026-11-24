import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.Exterior

/-!
# Clock constants of the exterior block (helper for `RelExteriorBlockBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2979-2980 and
2998-2999 (`clockN = e^{Re λ (θ_t - θ_s)} (θ_t/θ_s)^{Re κ}`).

Along a block `movingZ t₂ - movingZ t₁ = B` one has `θ₁ - θ₂ = B` and `1 ≤ θ₁/θ₂ ≤ e^{B/b}` on
`b ≤ θ₂`, hence `(clockN)⁻¹ e^{3B/(2b)} ≤ e^{-Re λ B} e^{(|Re κ| + 3/2)B/b} ≤ C₀ e^{-hB} + δ` once
`b ≥ (|Re κ| + 3/2) B / log (1 + δ)`, `h ≤ Re λ`, `C₀ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

namespace RelExteriorSub

theorem clockTheta_sub_eq {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    clockTheta ν t₁ - clockTheta ν t₂ = movingZ ν t₂ - movingZ ν t₁ := by
  have ha₁ : 0 < clockA ν t₁ := by unfold clockA; positivity
  have ha₂ : 0 < clockA ν t₂ := by unfold clockA; positivity
  unfold clockTheta movingZ
  field_simp
  unfold clockA
  ring

/-- Lower bound of the clock normaliser along a block. -/
theorem clockN_lower {P : PlanarData} {ν t₁ t₂ b B : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (hb0 : 0 < b) (hbt : b ≤ clockTheta ν t₂) (hB : 0 ≤ B)
    (hBeq : movingZ ν t₂ - movingZ ν t₁ = B) :
    Real.exp (P.eigenvalue.re * B) * Real.exp (-(|P.kappa.re| * B / b)) ≤ clockN P ν t₁ t₂ := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  set θ₁ := clockTheta ν t₁ with hθ₁
  set θ₂ := clockTheta ν t₂ with hθ₂
  have hθ₂pos : 0 < θ₂ := theta_pos hν ht₂
  have hθ : θ₁ - θ₂ = B := by rw [hθ₁, hθ₂, clockTheta_sub_eq hν ht₁ ht₂, hBeq]
  set x : ℝ := θ₁ / θ₂ with hx
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ hθ₂pos]
    linarith
  have hxe : x ≤ Real.exp (B / b) := by
    have h1 : x = 1 + B / θ₂ := by
      rw [hx, ← hθ]
      field_simp
      ring
    have h2 : B / θ₂ ≤ B / b := div_le_div_of_nonneg_left hB hb0 hbt
    have h3 := Real.add_one_le_exp (B / b)
    linarith
  set κr := P.kappa.re with hκr
  have hxκ : Real.exp (-(|κr| * B / b)) ≤ x ^ κr := by
    have h1 : x ^ (-|κr|) ≤ x ^ κr :=
      Real.rpow_le_rpow_of_exponent_le hx1 (neg_abs_le κr)
    have h2 : x ^ |κr| ≤ Real.exp (B / b) ^ |κr| :=
      Real.rpow_le_rpow (by linarith) hxe (abs_nonneg _)
    have h3 : Real.exp (B / b) ^ |κr| = Real.exp (|κr| * B / b) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    have hxpos : 0 < x ^ |κr| := Real.rpow_pos_of_pos (by linarith) _
    have h4 : Real.exp (-(|κr| * B / b)) ≤ (x ^ |κr|)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hxpos (h2.trans h3.le)
    rw [Real.rpow_neg (by linarith)] at h1
    exact h4.trans h1
  have hN : clockN P ν t₁ t₂ = Real.exp (P.eigenvalue.re * B) * x ^ κr := by
    unfold clockN
    rw [← hθ₁, ← hθ₂, hθ]
  rw [hN]
  exact mul_le_mul_of_nonneg_left hxκ (Real.exp_pos _).le

/-- **The exterior constant.** `(clockN)⁻¹ e^{3B/(2b)} ≤ C₀ e^{-hB} + δ`. -/
theorem exterior_constant {P : PlanarData} {ν t₁ t₂ b B C₀ h δ : ℝ} (hν : 0 < ν)
    (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hb0 : 0 < b) (hbt : b ≤ clockTheta ν t₂) (hB : 0 < B)
    (hBeq : movingZ ν t₂ - movingZ ν t₁ = B) (hh : 0 < h) (hhl : h ≤ P.eigenvalue.re)
    (hC₀ : 1 ≤ C₀) (hδ : 0 < δ)
    (hbB : (|P.kappa.re| + 3 / 2) * B / Real.log (1 + δ) ≤ b) :
    0 < clockN P ν t₁ t₂ ∧
      (clockN P ν t₁ t₂)⁻¹ * Real.exp (3 / (2 * b) * B) ≤ C₀ * Real.exp (-h * B) + δ := by
  have hlow := clockN_lower (P := P) hν ht₁ h12 hb0 hbt hB.le hBeq
  have hN0 : 0 < Real.exp (P.eigenvalue.re * B) * Real.exp (-(|P.kappa.re| * B / b)) := by
    positivity
  have hNpos : 0 < clockN P ν t₁ t₂ := hN0.trans_le hlow
  refine ⟨hNpos, ?_⟩
  have hNinv : (clockN P ν t₁ t₂)⁻¹ ≤
      Real.exp (-(P.eigenvalue.re * B)) * Real.exp (|P.kappa.re| * B / b) := by
    have := inv_anti₀ hN0 hlow
    rwa [mul_inv, ← Real.exp_neg, ← Real.exp_neg, neg_neg] at this
  have hlog : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hcb : (|P.kappa.re| + 3 / 2) * B / b ≤ Real.log (1 + δ) := by
    rw [div_le_iff₀ hlog] at hbB
    rw [div_le_iff₀ hb0]
    linarith
  have hexp : Real.exp (|P.kappa.re| * B / b) * Real.exp (3 / (2 * b) * B) =
      Real.exp ((|P.kappa.re| + 3 / 2) * B / b) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
  have he1 : Real.exp ((|P.kappa.re| + 3 / 2) * B / b) ≤ 1 + δ := by
    calc Real.exp ((|P.kappa.re| + 3 / 2) * B / b) ≤ Real.exp (Real.log (1 + δ)) :=
          Real.exp_le_exp.2 hcb
      _ = 1 + δ := Real.exp_log (by linarith)
  have hBl : h * B ≤ P.eigenvalue.re * B := mul_le_mul_of_nonneg_right hhl hB.le
  have hl0 : 0 ≤ P.eigenvalue.re * B := mul_nonneg (hh.le.trans hhl) hB.le
  have he2 : Real.exp (-(P.eigenvalue.re * B)) ≤ Real.exp (-h * B) :=
    Real.exp_le_exp.2 (by linarith)
  have he3 : Real.exp (-(P.eigenvalue.re * B)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  have hC : Real.exp (-h * B) ≤ C₀ * Real.exp (-h * B) :=
    le_mul_of_one_le_left (Real.exp_pos _).le hC₀
  have hE := (Real.exp_pos (-(P.eigenvalue.re * B))).le
  calc (clockN P ν t₁ t₂)⁻¹ * Real.exp (3 / (2 * b) * B)
      ≤ (Real.exp (-(P.eigenvalue.re * B)) * Real.exp (|P.kappa.re| * B / b)) *
          Real.exp (3 / (2 * b) * B) :=
        mul_le_mul_of_nonneg_right hNinv (Real.exp_pos _).le
    _ = Real.exp (-(P.eigenvalue.re * B)) * Real.exp ((|P.kappa.re| + 3 / 2) * B / b) := by
        rw [mul_assoc, hexp]
    _ ≤ Real.exp (-(P.eigenvalue.re * B)) * (1 + δ) := mul_le_mul_of_nonneg_left he1 hE
    _ = Real.exp (-(P.eigenvalue.re * B)) + Real.exp (-(P.eigenvalue.re * B)) * δ := by ring
    _ ≤ C₀ * Real.exp (-h * B) + 1 * δ :=
        add_le_add (he2.trans hC) (mul_le_mul_of_nonneg_right he3 hδ.le)
    _ = C₀ * Real.exp (-h * B) + δ := by ring

end RelExteriorSub

end UnforcedLeray.Short.IIIa
