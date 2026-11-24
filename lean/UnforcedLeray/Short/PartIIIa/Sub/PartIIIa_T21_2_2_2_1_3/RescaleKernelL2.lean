import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.Dil
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# `PartIII-a:T21/2/2/2/1/3` leaf `RescaleKernelL2` (SP 2875-2896, 3052-3057)

The `L²` clause of the kernel Biot-Savart velocity. With `s = √a`, `d = c/s`, the circulation
satisfies `∫_{C_c} ψ(·/s) = a ∫_{C_d} ψ` (`ChangeVar.integral_cell_scale`), and the mean shear
satisfies `s · meanShear d Γ (x/s) = meanShear c (aΓ) x`, so the rescaled field is
`s f(s⁻¹ ·)` with `f = u - meanShear d Γ` in `L²(C_d)`. The `L²` transfer is the pushforward
identity `map (s⁻¹ •) (restrict C_c) = a • restrict C_d` (`Dil.map_dilate_restrict`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
open UnforcedLeray
open UnforcedLeray.Short.IIIa

lemma sign_div_pos_aux {s : ℝ} (hs : 0 < s) (t : ℝ) : Real.sign (t / s) = Real.sign t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (div_neg_of_neg_of_pos h hs)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (div_pos h hs)]

lemma aux_sq_rescale {s c Γ : ℝ} (hs : 0 < s) (hc : 0 < c) :
    s * (-(Γ / (2 * (c / s)))) = -((s ^ 2 * Γ) / (2 * c)) := by
  field_simp

theorem rescaleKernelL2 : UnforcedLeray.Short.IIIa.E0.RescaleKernelL2 := by
  intro c a hc ha ψ u hu j
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  -- circulation: `∫_{C_c} ψ(·/s) = a ∫_{C_{c/s}} ψ`
  have hΓ : ∫ y in B0579.cell c, ψ (y.1 / Real.sqrt a, y.2 / Real.sqrt a) =
      a * ∫ y in B0579.cell (cellLen c a), ψ y := by
    have h := UnforcedLeray.Short.IIIa.integral_cell_scale c a ha
      (fun x : ℝ × ℝ => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a))
    have e : ∀ y : ℝ × ℝ, ψ ((Real.sqrt a * y.1) / Real.sqrt a, (Real.sqrt a * y.2) / Real.sqrt a) =
        ψ y := by
      intro y
      rw [mul_div_cancel_left₀ _ hs.ne', mul_div_cancel_left₀ _ hs.ne']
    simp only [e] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  -- mean shear: `√a · meanShear d Γ (x/√a) = meanShear c (aΓ) x`
  have hmean : ∀ (Γ : ℝ) (x : ℝ × ℝ), Real.sqrt a *
      meanShear (cellLen c a) Γ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) j =
        meanShear c (a * Γ) x j := by
    intro Γ x
    unfold meanShear
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos hj]
      dsimp only
      rw [sign_div_pos_aux hs]
      have key := aux_sq_rescale (Γ := Γ) hs hc
      rw [hs2] at key
      show Real.sqrt a * (-(Γ / (2 * (c / Real.sqrt a))) * Real.sign x.2) =
        -(a * Γ / (2 * c)) * Real.sign x.2
      linear_combination (Real.sign x.2) * key
    · rw [if_neg hj, if_neg hj, mul_zero]
  -- the rescaled field is `s f(s⁻¹ ·)`
  have hfun : (fun x : ℝ × ℝ => Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) j -
        meanShear c (∫ y in B0579.cell c, ψ (y.1 / Real.sqrt a, y.2 / Real.sqrt a)) x j) =
      (fun y : ℝ × ℝ => Real.sqrt a * (u y j -
          meanShear (cellLen c a) (∫ z in B0579.cell (cellLen c a), ψ z) y j)) ∘
        (fun x : ℝ × ℝ => (Real.sqrt a)⁻¹ • x) := by
    funext x
    simp only [Function.comp_apply]
    have hx : (Real.sqrt a)⁻¹ • x = (x.1 / Real.sqrt a, x.2 / Real.sqrt a) := by
      ext <;> simp [div_eq_inv_mul]
    rw [hx, hΓ, mul_sub, hmean]
  have hT' : Measurable (fun x : ℝ × ℝ => (Real.sqrt a)⁻¹ • x) := measurable_const_smul _
  have hg : MemLp (fun y : ℝ × ℝ => Real.sqrt a * (u y j -
        meanShear (cellLen c a) (∫ z in B0579.cell (cellLen c a), ψ z) y j)) 2
      (Measure.map (fun x : ℝ × ℝ => (Real.sqrt a)⁻¹ • x) (volume.restrict (B0579.cell c))) := by
    rw [UnforcedLeray.Short.IIIa.E0.RsDil.map_dilate_restrict ha]
    exact ((hu j).const_mul (Real.sqrt a)).smul_measure ENNReal.ofReal_ne_top
  rw [hfun]
  exact MemLp.comp_of_map hg hT'.aemeasurable
