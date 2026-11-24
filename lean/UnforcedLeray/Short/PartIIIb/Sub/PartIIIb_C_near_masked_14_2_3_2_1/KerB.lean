import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.SpaceSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.PlanarExterior
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.QuarticLine

/-!
# Column bound of the Schur kernel (`PartIII-b:C/near/masked/14/2/3/2/1/7`; source 3996-4011)

`∫ K(y,z) w(y) dy ≤ B w(z)` with `B = K₀ · 2πθ`, `K₀ = R⁻¹ (π/2) (1-θ)^{-3}`, `θ = e^{-δ/2}`.

For `z' ≠ 0` the indicator forces `|z'| < θ ρ(y)`, hence the planar distance `a = |y'-z'|`
satisfies `a ≥ (1-θ)ρ(y)`; the `y₂`-integral is `(π/2) a^{-3} ≤ (π/2)((1-θ)ρ)^{-3}`, and the
exterior planar integral `∫_{ρ > r} ρ^{-3} = 2π/r` with `r = |z'|/θ` gives `2πθ/|z'| = 2πθ w(z)`.
Source: `the November 2 reference manuscript` 3996-4011.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb

lemma kerB_vec0 (p : ℝ × ℝ) (t : ℝ) :
    (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) 0 = p.1 := by
  simp [UnforcedLeray.Axi.vecSp]

lemma kerB_vec1 (p : ℝ × ℝ) (t : ℝ) :
    (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) 1 = p.2 := by
  simp [UnforcedLeray.Axi.vecSp]

lemma kerB_vec2 (p : ℝ × ℝ) (t : ℝ) :
    (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) 2 = t := by
  simp [UnforcedLeray.Axi.vecSp]

lemma kerB_norm_sq (x : UnforcedLeray.Space) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

lemma kerB_norm_rpow (x : UnforcedLeray.Space) :
    ‖x‖ ^ (-4 : ℝ) = (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (-2 : ℝ) := by
  have h : ‖x‖ ^ (-4 : ℝ) = (‖x‖ ^ (2 : ℝ)) ^ (-2 : ℝ) := by
    rw [← Real.rpow_mul (norm_nonneg x)]
    norm_num
  rw [h, Real.rpow_two, kerB_norm_sq]

lemma kerB_theta2 (δ : ℝ) : Real.exp (-δ / 2) ^ 2 * Real.exp δ = 1 := by
  have h : Real.exp (-δ / 2) * Real.exp (-δ / 2) = Real.exp (-δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [sq, h, ← Real.exp_add]
  simp

lemma kerB_schurK_vec (R δ : ℝ) (z : UnforcedLeray.Space) (p : ℝ × ℝ) (t : ℝ) :
    schurK R δ (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) z =
      ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) / R) *
        (if Real.exp δ * (R ^ 2 / (p.1 ^ 2 + p.2 ^ 2)) < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
          then ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + (t - z 2) ^ 2) ^ (-2 : ℝ))
          else 0) := by
  unfold schurK rhoP
  simp only [kerB_norm_rpow, PiLp.sub_apply, kerB_vec0, kerB_vec1, kerB_vec2]

lemma kerB_schurW_vec (p : ℝ × ℝ) (t : ℝ) (hq : p.1 ^ 2 + p.2 ^ 2 ≠ 0) :
    schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) =
      ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ := by
  unfold schurW rhoP
  simp only [kerB_vec0, kerB_vec1]
  rw [if_neg hq]

/-- The disc condition: `e^δ q_y / ... ` forces `|z'| < θ |y'|`. -/
lemma kerB_cond (R δ θ : ℝ) (hR : 0 < R) (hθ0 : 0 < θ) (hθ2 : θ ^ 2 * Real.exp δ = 1)
    (qy qz : ℝ) (hqy : 0 < qy) (hqz : 0 < qz)
    (hc : Real.exp δ * (R ^ 2 / qy) < R ^ 2 / qz) :
    Real.sqrt qz < θ * Real.sqrt qy := by
  have h1 : Real.exp δ * (R ^ 2 / qy) = Real.exp δ * R ^ 2 / qy := (mul_div_assoc _ _ _).symm
  rw [h1, div_lt_div_iff₀ hqy hqz] at hc
  have hR2 : 0 < R ^ 2 := by positivity
  have h2 : Real.exp δ * qz < qy :=
    lt_of_mul_lt_mul_left
      (by nlinarith [hc] : R ^ 2 * (Real.exp δ * qz) < R ^ 2 * qy) hR2.le
  have e : θ ^ 2 * (Real.exp δ * qz) = qz := by
    rw [← mul_assoc, hθ2, one_mul]
  have hlt : θ ^ 2 * (Real.exp δ * qz) < θ ^ 2 * qy :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  have h3 : qz < (θ * Real.sqrt qy) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hqy.le]
    linarith
  exact (Real.sqrt_lt' (mul_pos hθ0 (Real.sqrt_pos.2 hqy))).2 h3

/-- Planar triangle bound: `|a' - b'| ≥ (1-θ)|a'|` when `|b'| < θ |a'|`. -/
lemma kerB_tri (θ a0 a1 b0 b1 : ℝ) (hθ1 : θ < 1)
    (hs : Real.sqrt (b0 ^ 2 + b1 ^ 2) < θ * Real.sqrt (a0 ^ 2 + a1 ^ 2)) :
    ((1 - θ) * Real.sqrt (a0 ^ 2 + a1 ^ 2)) ^ 2 ≤ (a0 - b0) ^ 2 + (a1 - b1) ^ 2 := by
  have hρ0 : 0 ≤ Real.sqrt (a0 ^ 2 + a1 ^ 2) := Real.sqrt_nonneg _
  have hρsq : Real.sqrt (a0 ^ 2 + a1 ^ 2) ^ 2 = a0 ^ 2 + a1 ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (b0 ^ 2 + b1 ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (b0 ^ 2 + b1 ^ 2) ^ 2 = b0 ^ 2 + b1 ^ 2 := Real.sq_sqrt (by positivity)
  set ρ := Real.sqrt (a0 ^ 2 + a1 ^ 2) with hρdef
  set s := Real.sqrt (b0 ^ 2 + b1 ^ 2) with hsdef
  have hCS2 : (a0 * b0 + a1 * b1) ^ 2 ≤ (ρ * s) ^ 2 := by
    rw [mul_pow, hρsq, hs2]
    nlinarith [sq_nonneg (a0 * b1 - a1 * b0)]
  have hCS : a0 * b0 + a1 * b1 ≤ ρ * s := by
    nlinarith [mul_nonneg hρ0 hs0]
  have hQ : (ρ - s) ^ 2 ≤ (a0 - b0) ^ 2 + (a1 - b1) ^ 2 := by
    nlinarith [hCS, hρsq, hs2]
  have hge : (1 - θ) * ρ ≤ ρ - s := by
    nlinarith
  have h0 : 0 ≤ (1 - θ) * ρ := mul_nonneg (by linarith) hρ0
  exact le_trans (pow_le_pow_left₀ h0 hge 2) hQ

/-- Fibre bound: the `y₂`-integral over one planar column `y' = p`. -/
lemma kerB_fiber (R δ θ : ℝ) (hR : 0 < R) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθ2 : θ ^ 2 * Real.exp δ = 1) (z : UnforcedLeray.Space) (hz : 0 < z 0 ^ 2 + z 1 ^ 2)
    (p : ℝ × ℝ) :
    ∫⁻ t : ℝ, schurK R δ (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) z *
        schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t])
      ≤ ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - θ) ^ (-3 : ℝ))) *
        (if Real.sqrt (z 0 ^ 2 + z 1 ^ 2) / θ < Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
          then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (-3 : ℝ)) else 0) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hK0nn : 0 ≤ 1 / R * (Real.pi / 2 * (1 - θ) ^ (-3 : ℝ)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.rpow_nonneg h1θ.le _))
  by_cases hqy : p.1 ^ 2 + p.2 ^ 2 = 0
  · have hz0 : ∀ t : ℝ, schurK R δ (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) z *
        schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) = 0 := by
      intro t
      rw [kerB_schurK_vec, hqy, Real.sqrt_zero, zero_div, ENNReal.ofReal_zero, zero_mul, zero_mul]
    simp only [hz0, lintegral_zero]
    exact zero_le
  · have hqy' : 0 < p.1 ^ 2 + p.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hqy)
    have hsp : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.2 hqy'
    have hsne : Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ≠ 0 := hsp.ne'
    by_cases hc : Real.exp δ * (R ^ 2 / (p.1 ^ 2 + p.2 ^ 2)) < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
    · have hs : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) < θ * Real.sqrt (p.1 ^ 2 + p.2 ^ 2) :=
        kerB_cond R δ θ hR hθ0 hθ2 (p.1 ^ 2 + p.2 ^ 2) (z 0 ^ 2 + z 1 ^ 2) hqy' hz hc
      have hr : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) / θ < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
        rw [div_lt_iff₀ hθ0]
        linarith
      rw [if_pos hr]
      have hQb := kerB_tri θ p.1 p.2 (z 0) (z 1) hθ1 hs
      have hQnn : 0 ≤ (p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 := by positivity
      have hgeQ : (1 - θ) * Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ≤
          Real.sqrt ((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2) := by
        calc (1 - θ) * Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
            = Real.sqrt (((1 - θ) * Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ 2) :=
              (Real.sqrt_sq (mul_nonneg h1θ.le hsp.le)).symm
          _ ≤ Real.sqrt ((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2) := Real.sqrt_le_sqrt hQb
      have ha : 0 < Real.sqrt ((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2) :=
        lt_of_lt_of_le (mul_pos h1θ hsp) hgeQ
      have hq4 := lintegral_quartic_line _ ha
      rw [Real.sq_sqrt hQnn] at hq4
      have htr : ∫⁻ t : ℝ, ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + (t - z 2) ^ 2) ^ (-2 : ℝ))
          = ∫⁻ t : ℝ, ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + t ^ 2) ^ (-2 : ℝ)) :=
        lintegral_sub_right_eq_self
          (fun u : ℝ => ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + u ^ 2) ^ (-2 : ℝ)))
          (z 2)
      have hle : ENNReal.ofReal (Real.pi / 2 *
            Real.sqrt ((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2) ^ (-3 : ℝ))
          ≤ ENNReal.ofReal (Real.pi / 2 * ((1 - θ) * Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ (-3 : ℝ)) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (mul_pos h1θ hsp) hgeQ (by norm_num)) (by positivity))
      have key : ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) / R) *
          ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))⁻¹ = ENNReal.ofReal (1 / R) := by
        rw [← ENNReal.ofReal_mul (div_nonneg hsp.le hR.le)]
        congr 1
        field_simp
      calc ∫⁻ t : ℝ, schurK R δ (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) z *
              schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t])
          = ∫⁻ t : ℝ, ENNReal.ofReal (1 / R) *
              ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + (t - z 2) ^ 2) ^ (-2 : ℝ)) := by
            refine lintegral_congr fun t => ?_
            rw [kerB_schurK_vec, kerB_schurW_vec p t hqy, if_pos hc, ← key]
            ring
        _ = ENNReal.ofReal (1 / R) *
              ∫⁻ t : ℝ, ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + (t - z 2) ^ 2) ^ (-2 : ℝ)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (1 / R) *
              ∫⁻ t : ℝ, ENNReal.ofReal (((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2 + t ^ 2) ^ (-2 : ℝ)) := by
            rw [htr]
        _ = ENNReal.ofReal (1 / R) *
              ENNReal.ofReal (Real.pi / 2 *
                Real.sqrt ((p.1 - z 0) ^ 2 + (p.2 - z 1) ^ 2) ^ (-3 : ℝ)) := by
            rw [hq4]
        _ ≤ ENNReal.ofReal (1 / R) *
              ENNReal.ofReal (Real.pi / 2 * ((1 - θ) * Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hle zero_le
        _ = ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - θ) ^ (-3 : ℝ))) *
              ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (-3 : ℝ)) := by
            rw [Real.mul_rpow h1θ.le hsp.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / R),
              ← ENNReal.ofReal_mul hK0nn]
            congr 1
            ring
    · have hz0 : ∀ t : ℝ, schurK R δ (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) z *
          schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) = 0 := by
        intro t
        rw [kerB_schurK_vec, if_neg hc]
        simp
      simp only [hz0, lintegral_zero]
      exact zero_le

theorem schurKerB : UnforcedLeray.Short.PartIIIb.NearInst.Masked.SchurKerB := by
  intro R δ hR hδ
  have hθ0 : 0 < Real.exp (-δ / 2) := Real.exp_pos _
  have hθ1 : Real.exp (-δ / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hθ2 := kerB_theta2 δ
  have h1θ : 0 < 1 - Real.exp (-δ / 2) := by linarith
  have hK0nn : 0 ≤ 1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.rpow_nonneg h1θ.le _))
  have hBnn : 0 ≤ 1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ)) *
      (2 * Real.pi * Real.exp (-δ / 2)) :=
    mul_nonneg hK0nn (by positivity)
  refine ⟨ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ)) *
      (2 * Real.pi * Real.exp (-δ / 2))), ENNReal.ofReal_ne_top, fun z => ?_⟩
  by_cases hz : z 0 ^ 2 + z 1 ^ 2 = 0
  · have hz0 : ∀ y : UnforcedLeray.Space, schurK R δ y z * schurW y = 0 := by
      intro y
      have hnn : 0 ≤ Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) := by positivity
      unfold schurK
      rw [hz, div_zero, if_neg (not_lt.2 hnn)]
      simp
    simp only [hz0, lintegral_zero]
    exact zero_le
  · have hzpos : 0 < z 0 ^ 2 + z 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
    have hsZ : 0 < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := Real.sqrt_pos.2 hzpos
    have hWz : schurW z = ENNReal.ofReal (Real.sqrt (z 0 ^ 2 + z 1 ^ 2))⁻¹ := by
      unfold schurW rhoP
      rw [if_neg hz]
    have hF : Measurable (fun y : UnforcedLeray.Space => schurK R δ y z * schurW y) :=
      ((schurK_measurable R δ).comp (measurable_id.prodMk measurable_const)).mul schurW_measurable
    rw [hWz]
    calc ∫⁻ y : UnforcedLeray.Space, schurK R δ y z * schurW y
        = ∫⁻ p : ℝ × ℝ, ∫⁻ t : ℝ, schurK R δ (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) z *
            schurW (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) :=
          lintegral_space_split (fun y => schurK R δ y z * schurW y) hF
      _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ))) *
            (if Real.sqrt (z 0 ^ 2 + z 1 ^ 2) / Real.exp (-δ / 2) < Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
              then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (-3 : ℝ)) else 0) :=
          lintegral_mono fun p => kerB_fiber R δ _ hR hθ0 hθ1 hθ2 z hzpos p
      _ = ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ))) *
            ∫⁻ p : ℝ × ℝ, (if Real.sqrt (z 0 ^ 2 + z 1 ^ 2) / Real.exp (-δ / 2) < Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
              then ENNReal.ofReal (Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (-3 : ℝ)) else 0) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ))) *
            ENNReal.ofReal (2 * Real.pi / (Real.sqrt (z 0 ^ 2 + z 1 ^ 2) / Real.exp (-δ / 2))) := by
          rw [lintegral_planar_exterior _ (div_pos hsZ hθ0)]
      _ = ENNReal.ofReal (1 / R * (Real.pi / 2 * (1 - Real.exp (-δ / 2)) ^ (-3 : ℝ)) *
            (2 * Real.pi * Real.exp (-δ / 2))) * ENNReal.ofReal (Real.sqrt (z 0 ^ 2 + z 1 ^ 2))⁻¹ := by
          rw [← ENNReal.ofReal_mul hK0nn, ← ENNReal.ofReal_mul hBnn]
          congr 1
          field_simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
