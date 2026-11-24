import UnforcedLeray.Blueprint.Localization.Spaces

/-!
# B0005, part 1: similarity variables (tex 136–137)

Blueprint unit B0005 (`unlabeled:136`), `paper/main.tex` lines 136–137: "In similarity
variables `y = x/√t`, `τ = log t`". The change of variables is the bijection
`(t, x) ↦ (log t, x/√t)` of `(0, ∞) × ℝ³` onto `ℝ × ℝ³`, with inverse
`(τ, y) ↦ (e^τ, e^{τ/2} y)`.

The interface layer uses the same convention:
* `Blueprint.heatProfile` (`Blueprint/Package.lean`, tex 159–163) is
  `H_h[u](y, τ) = e^{τ/2} [e^{h e^τ Δ} u](e^{τ/2} y)`, the similarity profile `√t · v(t, x)` of
  the physical field `v(t, x) = e^{htΔ}u(x)` at `(t, x) = (e^τ, e^{τ/2} y)`
  (`heatProfile_eq_profile`);
* `Blueprint.physicalDilation` (`Blueprint/Localization/Spaces.lean`, tex 525–538) is
  `F ↦ t^{-1/2} F(· t^{-1/2})`, the inverse profile map, and `t^{-1/2} = 1/√t`
  (`rpow_neg_half_eq`, `simY_eq_rpow`).

`simY t x = (√t)⁻¹ • x` uses `Real.sqrt`; for `t ≤ 0` both `log t` and `√t` are Lean junk
values, so every statement assumes `0 < t`.

Status: definitions with their inverse laws. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.B0005

/-- The similarity phase `τ = log t` (tex 136). Meaningful for `t > 0`. -/
def simTau (t : ℝ) : ℝ := Real.log t

/-- The similarity variable `y = x/√t` (tex 136). Meaningful for `t > 0`. -/
def simY (t : ℝ) (x : Space) : Space := (Real.sqrt t)⁻¹ • x

/-- The physical time `t = e^τ` of the phase `τ`. -/
def physTime (τ : ℝ) : ℝ := Real.exp τ

/-- The physical point `x = e^{τ/2} y` of `(τ, y)`. -/
def physPoint (τ : ℝ) (y : Space) : Space := Real.exp (τ / 2) • y

/-- The change of variables `(t, x) ↦ (τ, y) = (log t, x/√t)`. -/
def toSimilarity (p : ℝ × Space) : ℝ × Space := (simTau p.1, simY p.1 p.2)

/-- The inverse change of variables `(τ, y) ↦ (t, x) = (e^τ, e^{τ/2} y)`. -/
def fromSimilarity (p : ℝ × Space) : ℝ × Space := (physTime p.1, physPoint p.1 p.2)

theorem sqrt_exp (τ : ℝ) : Real.sqrt (Real.exp τ) = Real.exp (τ / 2) := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]
  ring_nf

theorem physTime_pos (τ : ℝ) : 0 < physTime τ := Real.exp_pos τ

theorem simTau_physTime (τ : ℝ) : simTau (physTime τ) = τ := Real.log_exp τ

theorem physTime_simTau {t : ℝ} (ht : 0 < t) : physTime (simTau t) = t := Real.exp_log ht

theorem simY_physPoint (τ : ℝ) (y : Space) : simY (physTime τ) (physPoint τ y) = y := by
  simp only [simY, physTime, physPoint, sqrt_exp, smul_smul]
  rw [inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]

theorem physPoint_simY {t : ℝ} (ht : 0 < t) (x : Space) :
    physPoint (simTau t) (simY t x) = x := by
  have h : Real.exp (simTau t / 2) = Real.sqrt t := by
    rw [← sqrt_exp]
    exact congrArg Real.sqrt (physTime_simTau ht)
  simp only [physPoint, simY, smul_smul, h]
  rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr ht).ne', one_smul]

theorem toSimilarity_fromSimilarity (p : ℝ × Space) : toSimilarity (fromSimilarity p) = p := by
  obtain ⟨τ, y⟩ := p
  simp only [toSimilarity, fromSimilarity, simTau_physTime, simY_physPoint]

theorem fromSimilarity_toSimilarity {p : ℝ × Space} (hp : 0 < p.1) :
    fromSimilarity (toSimilarity p) = p := by
  obtain ⟨t, x⟩ := p
  simp only [toSimilarity, fromSimilarity, physTime_simTau hp, physPoint_simY hp]

theorem fromSimilarity_mem (p : ℝ × Space) : fromSimilarity p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Space) :=
  ⟨physTime_pos p.1, mem_univ _⟩

/-- **Similarity variables** (tex 136): `(t, x) ↦ (log t, x/√t)` is a bijection of
`(0, ∞) × ℝ³` onto `ℝ × ℝ³` with inverse `(τ, y) ↦ (e^τ, e^{τ/2} y)`. -/
theorem bijOn_toSimilarity :
    BijOn toSimilarity (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) univ := by
  refine InvOn.bijOn ⟨fun p hp => fromSimilarity_toSimilarity hp.1,
    fun p _ => toSimilarity_fromSimilarity p⟩ (fun _ _ => mem_univ _)
    (fun p _ => fromSimilarity_mem p)

/-- `t^{-1/2} = 1/√t` for `t > 0` (the exponent of `Blueprint.physicalDilation`). -/
theorem rpow_neg_half_eq {t : ℝ} (ht : 0 < t) : t ^ (-1 / 2 : ℝ) = (Real.sqrt t)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]
  norm_num

/-- `y = x/√t = t^{-1/2} x`, as in `Blueprint.physicalDilation`. -/
theorem simY_eq_rpow {t : ℝ} (ht : 0 < t) (x : Space) : simY t x = t ^ (-1 / 2 : ℝ) • x := by
  rw [simY, rpow_neg_half_eq ht]

/-- The similarity profile `U(τ, y) = √t · u(t, x)` at `(t, x) = (e^τ, e^{τ/2} y)` of a physical
field `u(t, x)`; the scaling of `u(x,t) = t^{-1/2} U(x/√t, log t)`. -/
def toProfile (u : ℝ → SpatialField) (τ : ℝ) (y : Space) : Space :=
  Real.sqrt (physTime τ) • u (physTime τ) (physPoint τ y)

/-- The physical field `u(t, x) = t^{-1/2} U(log t, x/√t)` of a profile `U(τ, y)`. -/
def ofProfile (U : ℝ → SpatialField) (t : ℝ) (x : Space) : Space :=
  (Real.sqrt t)⁻¹ • U (simTau t) (simY t x)

theorem toProfile_ofProfile (U : ℝ → SpatialField) (τ : ℝ) (y : Space) :
    toProfile (ofProfile U) τ y = U τ y := by
  simp only [toProfile, ofProfile, simTau_physTime, simY_physPoint, smul_smul]
  rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (physTime_pos τ)).ne', one_smul]

theorem ofProfile_toProfile (u : ℝ → SpatialField) {t : ℝ} (ht : 0 < t) (x : Space) :
    ofProfile (toProfile u) t x = u t x := by
  simp only [toProfile, ofProfile, physTime_simTau ht, physPoint_simY ht, smul_smul]
  rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr ht).ne', one_smul]

/-- `Blueprint.heatProfile` (tex 159–163) is the similarity profile of the physical heat
solution `v(t, x) = [e^{htΔ}u](x)`. -/
theorem heatProfile_eq_profile (h : ℝ) (u : SpatialField) (τ : ℝ) (y : Space) :
    Blueprint.heatProfile h u τ y =
      toProfile (fun t x => Heat.average (h * t) u x) τ y := by
  simp only [Blueprint.heatProfile, toProfile, physTime, physPoint, sqrt_exp]

end UnforcedLeray.B0005
