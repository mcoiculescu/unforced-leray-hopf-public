import UnforcedLeray.Lib.HeatR3.HeatDecay

/-!
# The heat profile in similarity variables (INF04 T10, part)


Unit B0697 (tex 5923–5934): with `a_τ(y) = e^{τ/2}a(e^{τ/2}y)`, the heat profile is
`H_a(τ) = e^{hΔ}a_τ = e^{τ/2}[e^{he^τΔ}a](e^{τ/2}y)` (heat time `h`, the manuscript's `ν`), and
the DSS identity for `a` makes `H_a` periodic in `τ`.

Main results:
* `simHeat`, `simHeat_eq` (the scaling identity, for every field, `h > 0`);
* `simHeat_periodic` (DSS periodicity, B0697);
* `simHeat_contDiff` (`C^∞` in `y` for admissible data);
* `norm_simHeat_le` (`|H_a(τ, y)| ≤ C e^{τ/2}(1 + e^{τ/2}|y|)^β` for `|a| ≤ M(1+|y|)^β`);
* `simHeat_decay` (B0710, tex 275–278): for `u ∈ 𝒦₂(C)`, `|D^j H_h[u](τ, y)| ≤ K⟨y⟩^{-1-j}`,
  `j ≤ 2`, uniformly in `τ ∈ ℝ` (from `InvDistClass.heat_decay`).

Not proved here: the `C₀` and `L³` continuity in `τ`, solenoidality and the profile equation.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff

/-- **INF04 T10 `simHeat`.** `H_h[u](τ, y) = e^{τ/2} (e^{h e^τ Δ}u)(e^{τ/2} y)`. -/
def simHeat (h : ℝ) (u : SpatialField) (τ : ℝ) (y : Space) : Space :=
  Real.exp (τ / 2) • average (h * Real.exp τ) u (Real.exp (τ / 2) • y)

/-- **INF04 T10 `simHeat_eq`.** `H_h[u](τ) = e^{hΔ}[e^{τ/2}u(e^{τ/2}·)]` for `h > 0` and every
field `u` (B0697). -/
theorem simHeat_eq {h : ℝ} (hh : 0 < h) (u : SpatialField) (τ : ℝ) :
    simHeat h u τ = average h (fun y => Real.exp (τ / 2) • u (Real.exp (τ / 2) • y)) := by
  rw [average_dilate' (Real.exp_pos _) hh]
  funext y
  simp only [simHeat]
  congr 2
  rw [← Real.exp_nat_mul, mul_comm]
  congr 1
  ring_nf

/-- **INF04 T10 `simHeat_periodic`.** If `u(e^{T/2}x) = e^{-T/2}u(x)` (discrete self-similarity
with period `T`), then `H_h[u]` is `T`-periodic in `τ` (B0697). -/
theorem simHeat_periodic {h : ℝ} (hh : 0 < h) {u : SpatialField} {T : ℝ}
    (hdss : ∀ x, u (Real.exp (T / 2) • x) = Real.exp (-T / 2) • u x) (τ : ℝ) :
    simHeat h u (τ + T) = simHeat h u τ := by
  rw [simHeat_eq hh, simHeat_eq hh]
  congr 1
  funext y
  have h1 : Real.exp ((τ + T) / 2) • y = Real.exp (T / 2) • (Real.exp (τ / 2) • y) := by
    rw [smul_smul, ← Real.exp_add]; ring_nf
  rw [h1, hdss, smul_smul, ← Real.exp_add]
  ring_nf

/-- The profile is `C^∞` in space for admissible data. -/
theorem simHeat_contDiff {h : ℝ} (hh : 0 < h) {u : SpatialField} (hu : HeatAdmissible u)
    (τ : ℝ) : ContDiff ℝ ∞ (simHeat h u τ) := by
  have h1 : ContDiff ℝ ∞ (average (h * Real.exp τ) u) :=
    contDiff_average hu (mul_pos hh (Real.exp_pos τ))
  exact (h1.comp (contDiff_const_smul _)).const_smul _

/-- **INF04 T10, size bound.** If `|u(y)| ≤ M(1 + |y|)^β`, then
`|H_h[u](τ, y)| ≤ momentConst |β| (h e^τ) · M e^{τ/2} (1 + e^{τ/2}|y|)^β`. -/
theorem norm_simHeat_le {h : ℝ} (hh : 0 < h) {u : SpatialField} {M β : ℝ}
    (hu : ∀ y, ‖u y‖ ≤ M * (1 + ‖y‖) ^ β) (τ : ℝ) (y : Space) :
    ‖simHeat h u τ y‖ ≤
      Real.exp (τ / 2) * (momentConst |β| (h * Real.exp τ) * M *
        (1 + Real.exp (τ / 2) * ‖y‖) ^ β) := by
  rw [simHeat, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  gcongr
  have := norm_average_le_weight (mul_pos hh (Real.exp_pos τ)) le_rfl hu
    (Real.exp (τ / 2) • y)
  rwa [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at this

/-- **INF04 T10 `simHeat_decay`** (B0710, tex 275–278). For `u ∈ 𝒦₂(C)`, `h > 0`, `j ≤ 2`:
`|D^j H_h[u](τ, y)| ≤ K (1 + |y|)^{-1-j}` for all `τ ∈ ℝ` and `y` (uniformly in the phase). -/
theorem simHeat_decay {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 2 C u) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ τ : ℝ, ∀ y : Space,
      ‖iteratedFDeriv ℝ j (simHeat h u τ) y‖ ≤ K * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := InvDistClass.heat_decay (E := Space) C hj
  set c := min 1 (Real.sqrt h) with hc
  have hc0 : 0 < c := lt_min one_pos (Real.sqrt_pos.mpr hh)
  refine ⟨K * ((c ^ (1 + j))⁻¹), fun τ y => ?_⟩
  set a := Real.exp (τ / 2) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have hfun : simHeat h u τ = fun y => a • average (h * Real.exp τ) u (a • y) := rfl
  rw [hfun, Gaussian.iteratedFDeriv_comp_smul j (average (h * Real.exp τ) u) a a y, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  have h1 := hK u hu (h * Real.exp τ) (mul_pos hh (Real.exp_pos τ)) (a • y)
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos (by positivity) _)
  have hsq : Real.sqrt (h * Real.exp τ) = a * Real.sqrt h := by
    rw [Real.sqrt_mul hh.le, mul_comm, ha]
    congr 1
    rw [show Real.exp τ = Real.exp (τ / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
      Real.sqrt_sq (Real.exp_pos _).le]
  have hnorm : ‖a • y‖ + Real.sqrt (h * Real.exp τ) = a * (‖y‖ + Real.sqrt h) := by
    rw [norm_smul, Real.norm_of_nonneg ha0.le, hsq]; ring
  rw [hnorm] at h1
  have hA : 0 < ‖y‖ + Real.sqrt h := by
    have := Real.sqrt_pos.mpr hh; positivity
  have hcy : c * (1 + ‖y‖) ≤ ‖y‖ + Real.sqrt h := by
    have h1' : c ≤ 1 := min_le_left _ _
    have h2' : c ≤ Real.sqrt h := min_le_right _ _
    nlinarith [norm_nonneg y]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at h1 ⊢
  have hstep : a * a ^ j * (K * ((a * (‖y‖ + Real.sqrt h)) ^ (1 + j))⁻¹) =
      K * ((‖y‖ + Real.sqrt h) ^ (1 + j))⁻¹ := by
    rw [mul_pow, pow_add, pow_one]; field_simp
  have hmono : ((‖y‖ + Real.sqrt h) ^ (1 + j))⁻¹ ≤ ((c * (1 + ‖y‖)) ^ (1 + j))⁻¹ := by
    gcongr
  calc a * a ^ j * ‖iteratedFDeriv ℝ j (average (h * Real.exp τ) u) (a • y)‖
      ≤ a * a ^ j * (K * ((a * (‖y‖ + Real.sqrt h)) ^ (1 + j))⁻¹) := by gcongr
    _ = K * ((‖y‖ + Real.sqrt h) ^ (1 + j))⁻¹ := hstep
    _ ≤ K * ((c * (1 + ‖y‖)) ^ (1 + j))⁻¹ := by gcongr
    _ = K * (c ^ (1 + j))⁻¹ * ((1 + ‖y‖) ^ (1 + j))⁻¹ := by rw [mul_pow, mul_inv]; ring

end UnforcedLeray.Heat
