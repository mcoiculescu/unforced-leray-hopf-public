import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.SpaceSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.PlanarDisc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.QuarticLine

/-!
# Row bound of the Schur kernel (`PartIII-b:C/near/masked/14/2/3/2/1/6`; source 3996-4011)

`∫ K(y,z) w(z) dz ≤ A w(y)` with `A = π² θ /(R (1-θ)³)`, `θ = e^{-δ/2}`.

On the support `|z'| < θ ρ(y)` (`ρ(y) = |y'|`), the planar distance `a = |y'-z'|` satisfies
`a ≥ (1-θ)ρ(y)`; the `z₂`-integral is `(π/2) a^{-3} ≤ (π/2)((1-θ)ρ)^{-3}` by `lintegral_quartic_line`;
the planar disc integral of `ρ⁻¹` is `2πθρ` by `lintegral_planar_disc`.
Source: `the November 2 reference manuscript` 3996-4011.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb

lemma kerA_vec0 (p : ℝ × ℝ) (t : ℝ) :
    (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) 0 = p.1 := by
  simp [UnforcedLeray.Axi.vecSp]

lemma kerA_vec1 (p : ℝ × ℝ) (t : ℝ) :
    (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) 1 = p.2 := by
  simp [UnforcedLeray.Axi.vecSp]

lemma kerA_vec2 (p : ℝ × ℝ) (t : ℝ) :
    (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) 2 = t := by
  simp [UnforcedLeray.Axi.vecSp]

lemma kerA_norm_sq (x : UnforcedLeray.Space) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

lemma kerA_norm_rpow (x : UnforcedLeray.Space) :
    ‖x‖ ^ (-4 : ℝ) = (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (-2 : ℝ) := by
  have h : ‖x‖ ^ (-4 : ℝ) = (‖x‖ ^ (2 : ℝ)) ^ (-2 : ℝ) := by
    rw [← Real.rpow_mul (norm_nonneg x)]
    norm_num
  rw [h, Real.rpow_two, kerA_norm_sq]

lemma kerA_theta2 (δ : ℝ) : Real.exp (-δ / 2) ^ 2 * Real.exp δ = 1 := by
  have h : Real.exp (-δ / 2) * Real.exp (-δ / 2) = Real.exp (-δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [sq, h, ← Real.exp_add]
  simp

lemma kerA_schurK_vec (R δ : ℝ) (y : UnforcedLeray.Space) (p : ℝ × ℝ) (t : ℝ) :
    schurK R δ y (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) =
      ENNReal.ofReal (rhoP y / R) *
        (if Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) < R ^ 2 / (p.1 ^ 2 + p.2 ^ 2)
          then ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + (y 2 - t) ^ 2) ^ (-2 : ℝ))
          else 0) := by
  unfold schurK
  simp only [kerA_norm_rpow, PiLp.sub_apply, kerA_vec0, kerA_vec1, kerA_vec2]

lemma kerA_schurW_vec (p : ℝ × ℝ) (t : ℝ) (hq : p.1 ^ 2 + p.2 ^ 2 ≠ 0) :
    schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) =
      ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ := by
  unfold schurW rhoP
  simp only [kerA_vec0, kerA_vec1]
  rw [if_neg hq]

/-- Positivity of the planar radius of `z` and the disc condition `|z'| < θ ρ(y)`. -/
lemma kerA_cond (R δ θ : ℝ) (hR : 0 < R) (hθ0 : 0 < θ) (hθ2 : θ ^ 2 * Real.exp δ = 1)
    (y : UnforcedLeray.Space) (hy : 0 < y 0 ^ 2 + y 1 ^ 2) (p : ℝ × ℝ)
    (hc : Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) < R ^ 2 / (p.1 ^ 2 + p.2 ^ 2)) :
    0 < p.1 ^ 2 + p.2 ^ 2 ∧ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < θ * rhoP y := by
  have hq : 0 < p.1 ^ 2 + p.2 ^ 2 := by
    rcases (show (0 : ℝ) ≤ p.1 ^ 2 + p.2 ^ 2 by positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, div_zero] at hc
      have : 0 ≤ Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) := by positivity
      linarith
  refine ⟨hq, ?_⟩
  have hρsq : rhoP y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold rhoP
    exact Real.sq_sqrt hy.le
  have hρpos : 0 < rhoP y := by
    unfold rhoP
    exact Real.sqrt_pos.2 hy
  have h1 : Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) = Real.exp δ * R ^ 2 / (y 0 ^ 2 + y 1 ^ 2) :=
    (mul_div_assoc _ _ _).symm
  rw [h1, div_lt_div_iff₀ hy hq] at hc
  have hR2 : 0 < R ^ 2 := by positivity
  have h2 : Real.exp δ * (p.1 ^ 2 + p.2 ^ 2) < y 0 ^ 2 + y 1 ^ 2 :=
    lt_of_mul_lt_mul_left
      (by nlinarith [hc] : R ^ 2 * (Real.exp δ * (p.1 ^ 2 + p.2 ^ 2)) < R ^ 2 * (y 0 ^ 2 + y 1 ^ 2))
      hR2.le
  have h3 : p.1 ^ 2 + p.2 ^ 2 < (θ * rhoP y) ^ 2 := by
    have e : θ ^ 2 * (Real.exp δ * (p.1 ^ 2 + p.2 ^ 2)) = p.1 ^ 2 + p.2 ^ 2 := by
      rw [← mul_assoc, hθ2, one_mul]
    have hlt : θ ^ 2 * (Real.exp δ * (p.1 ^ 2 + p.2 ^ 2)) < θ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) :=
      mul_lt_mul_of_pos_left h2 (by positivity)
    rw [mul_pow, hρsq]
    linarith
  exact (Real.sqrt_lt' (mul_pos hθ0 hρpos)).2 h3

/-- The planar distance `a = |y' - z'|` satisfies `a ≥ (1-θ)ρ(y)` on the disc. -/
lemma kerA_Q_bound (θ : ℝ) (hθ1 : θ < 1) (y : UnforcedLeray.Space) (p : ℝ × ℝ)
    (hs : Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < θ * rhoP y) :
    ((1 - θ) * rhoP y) ^ 2 ≤ (y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 := by
  have hρ0 : 0 ≤ rhoP y := Real.sqrt_nonneg _
  have hρsq : rhoP y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold rhoP
    exact Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ 2 = p.1 ^ 2 + p.2 ^ 2 := Real.sq_sqrt (by positivity)
  set ρ := rhoP y with hρdef
  set s := Real.sqrt (p.1 ^ 2 + p.2 ^ 2) with hsdef
  have hCS2 : (y 0 * p.1 + y 1 * p.2) ^ 2 ≤ (ρ * s) ^ 2 := by
    rw [mul_pow, hρsq, hs2]
    nlinarith [sq_nonneg (y 0 * p.2 - y 1 * p.1)]
  have hCS : y 0 * p.1 + y 1 * p.2 ≤ ρ * s := by
    nlinarith [mul_nonneg hρ0 hs0]
  have hQ : (ρ - s) ^ 2 ≤ (y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 := by
    nlinarith [hCS, hρsq, hs2]
  have hge : (1 - θ) * ρ ≤ ρ - s := by
    nlinarith
  have h0 : 0 ≤ (1 - θ) * ρ := mul_nonneg (by linarith) hρ0
  exact le_trans (pow_le_pow_left₀ h0 hge 2) hQ

/-- Fibre bound: the `z₂`-integral over one planar column. -/
lemma kerA_inner (R δ θ : ℝ) (hR : 0 < R) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθ2 : θ ^ 2 * Real.exp δ = 1) (y : UnforcedLeray.Space) (hy : 0 < y 0 ^ 2 + y 1 ^ 2)
    (p : ℝ × ℝ) :
    ∫⁻ t : ℝ, schurK R δ y (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) *
        schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t])
      ≤ ENNReal.ofReal (rhoP y / R * (Real.pi / 2 * ((1 - θ) * rhoP y) ^ (-3 : ℝ))) *
        (if Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < θ * rhoP y
          then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ else 0) := by
  have hρ0 : 0 < rhoP y := by
    unfold rhoP
    exact Real.sqrt_pos.2 hy
  have h1θ : 0 < 1 - θ := by linarith
  have hpos1 : 0 < (1 - θ) * rhoP y := mul_pos h1θ hρ0
  by_cases hc : Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) < R ^ 2 / (p.1 ^ 2 + p.2 ^ 2)
  · obtain ⟨hq, hs⟩ := kerA_cond R δ θ hR hθ0 hθ2 y hy p hc
    rw [if_pos hs]
    have hQb := kerA_Q_bound θ hθ1 y p hs
    have hQnn : 0 ≤ (y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 := by positivity
    have hgeQ : (1 - θ) * rhoP y ≤ Real.sqrt ((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2) := by
      calc (1 - θ) * rhoP y = Real.sqrt (((1 - θ) * rhoP y) ^ 2) := (Real.sqrt_sq hpos1.le).symm
        _ ≤ Real.sqrt ((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2) := Real.sqrt_le_sqrt hQb
    have ha : 0 < Real.sqrt ((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2) := lt_of_lt_of_le hpos1 hgeQ
    have hq4 := lintegral_quartic_line _ ha
    rw [Real.sq_sqrt hQnn] at hq4
    have htr : ∫⁻ t : ℝ, ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + (y 2 - t) ^ 2) ^ (-2 : ℝ))
        = ∫⁻ t : ℝ, ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + t ^ 2) ^ (-2 : ℝ)) :=
      lintegral_sub_left_eq_self
        (fun s : ℝ => ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + s ^ 2) ^ (-2 : ℝ))) (y 2)
    have hle : ENNReal.ofReal (Real.pi / 2 *
          Real.sqrt ((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2) ^ (-3 : ℝ))
        ≤ ENNReal.ofReal (Real.pi / 2 * ((1 - θ) * rhoP y) ^ (-3 : ℝ)) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hpos1 hgeQ (by norm_num)) (by positivity))
    have hCne : ENNReal.ofReal (rhoP y / R) * ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    calc ∫⁻ t : ℝ, schurK R δ y (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) *
            schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t])
        = ∫⁻ t : ℝ, (ENNReal.ofReal (rhoP y / R) * ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹) *
            ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + (y 2 - t) ^ 2) ^ (-2 : ℝ)) := by
          refine lintegral_congr fun t => ?_
          rw [kerA_schurK_vec, kerA_schurW_vec p t hq.ne', if_pos hc]
          ring
      _ = (ENNReal.ofReal (rhoP y / R) * ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹) *
            ∫⁻ t : ℝ, ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + (y 2 - t) ^ 2) ^ (-2 : ℝ)) :=
          lintegral_const_mul' _ _ hCne
      _ = (ENNReal.ofReal (rhoP y / R) * ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹) *
            ∫⁻ t : ℝ, ENNReal.ofReal (((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2 + t ^ 2) ^ (-2 : ℝ)) := by
          rw [htr]
      _ = (ENNReal.ofReal (rhoP y / R) * ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹) *
            ENNReal.ofReal (Real.pi / 2 *
              Real.sqrt ((y 0 - p.1) ^ 2 + (y 1 - p.2) ^ 2) ^ (-3 : ℝ)) := by
          rw [hq4]
      _ ≤ (ENNReal.ofReal (rhoP y / R) * ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹) *
            ENNReal.ofReal (Real.pi / 2 * ((1 - θ) * rhoP y) ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hle zero_le
      _ = ENNReal.ofReal (rhoP y / R * (Real.pi / 2 * ((1 - θ) * rhoP y) ^ (-3 : ℝ))) *
            ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ := by
          rw [ENNReal.ofReal_mul (div_nonneg hρ0.le hR.le)]
          ring
  · have hz : ∀ t : ℝ, schurK R δ y (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) *
        schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) = 0 := by
      intro t
      rw [kerA_schurK_vec, if_neg hc]
      simp
    simp only [hz, lintegral_zero]
    exact zero_le

theorem schurKerA : UnforcedLeray.Short.PartIIIb.NearInst.Masked.SchurKerA := by
  intro R δ hR hδ
  refine ⟨ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-δ / 2) / (R * (1 - Real.exp (-δ / 2)) ^ 3)),
    ENNReal.ofReal_ne_top, fun y => ?_⟩
  by_cases hy : y 0 ^ 2 + y 1 ^ 2 = 0
  · have hrho : rhoP y = 0 := by
      unfold rhoP
      rw [hy, Real.sqrt_zero]
    have hz : ∀ z : UnforcedLeray.Space, schurK R δ y z * schurW z = 0 := by
      intro z
      unfold schurK
      rw [hrho, zero_div, ENNReal.ofReal_zero, zero_mul, zero_mul]
    simp only [hz, lintegral_zero]
    exact zero_le
  · have hy' : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
    have hθ0 : 0 < Real.exp (-δ / 2) := Real.exp_pos _
    have hθ1 : Real.exp (-δ / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hθ2 := kerA_theta2 δ
    have hρ0 : 0 < rhoP y := by
      unfold rhoP
      exact Real.sqrt_pos.2 hy'
    have hρne : rhoP y ≠ 0 := hρ0.ne'
    have hRne : R ≠ 0 := hR.ne'
    have h1θ : 0 < 1 - Real.exp (-δ / 2) := by linarith
    have h1θne : 1 - Real.exp (-δ / 2) ≠ 0 := h1θ.ne'
    have hpos1 : 0 < (1 - Real.exp (-δ / 2)) * rhoP y := mul_pos h1θ hρ0
    have hF : Measurable (fun z : UnforcedLeray.Space => schurK R δ y z * schurW z) :=
      ((schurK_measurable R δ).comp (measurable_const.prodMk measurable_id)).mul schurW_measurable
    have hsy : schurW y = ENNReal.ofReal (rhoP y)⁻¹ := by
      unfold schurW
      rw [if_neg hy]
    have hX : 0 ≤ rhoP y / R * (Real.pi / 2 * ((1 - Real.exp (-δ / 2)) * rhoP y) ^ (-3 : ℝ)) :=
      mul_nonneg (div_nonneg hρ0.le hR.le)
        (mul_nonneg (by positivity) (Real.rpow_nonneg hpos1.le _))
    have hA : 0 ≤ Real.pi ^ 2 * Real.exp (-δ / 2) / (R * (1 - Real.exp (-δ / 2)) ^ 3) :=
      div_nonneg (mul_nonneg (by positivity) hθ0.le) (mul_nonneg hR.le (pow_nonneg h1θ.le 3))
    rw [hsy]
    calc ∫⁻ z : UnforcedLeray.Space, schurK R δ y z * schurW z
        = ∫⁻ p : ℝ × ℝ, ∫⁻ t : ℝ, schurK R δ y (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) *
            schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) :=
          lintegral_space_split (fun z => schurK R δ y z * schurW z) hF
      _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (rhoP y / R * (Real.pi / 2 * ((1 - Real.exp (-δ / 2)) * rhoP y) ^ (-3 : ℝ))) *
            (if Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < Real.exp (-δ / 2) * rhoP y
              then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ else 0) :=
          lintegral_mono fun p => kerA_inner R δ _ hR hθ0 hθ1 hθ2 y hy' p
      _ = ENNReal.ofReal (rhoP y / R * (Real.pi / 2 * ((1 - Real.exp (-δ / 2)) * rhoP y) ^ (-3 : ℝ))) *
            ∫⁻ p : ℝ × ℝ, (if Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < Real.exp (-δ / 2) * rhoP y
              then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ else 0) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (rhoP y / R * (Real.pi / 2 * ((1 - Real.exp (-δ / 2)) * rhoP y) ^ (-3 : ℝ))) *
            ENNReal.ofReal (2 * Real.pi * (Real.exp (-δ / 2) * rhoP y)) := by
          rw [lintegral_planar_disc _ (mul_pos hθ0 hρ0)]
      _ = ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-δ / 2) / (R * (1 - Real.exp (-δ / 2)) ^ 3)) *
            ENNReal.ofReal (rhoP y)⁻¹ := by
          rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hA]
          congr 1
          rw [quarticLine_pow_neg_three _ hpos1.le]
          field_simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
