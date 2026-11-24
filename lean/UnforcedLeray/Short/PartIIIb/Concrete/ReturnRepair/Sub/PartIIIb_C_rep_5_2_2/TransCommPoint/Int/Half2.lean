import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Half

/-!
# Half-plane majorants for `X₀`, `∂_τX₀`, `y·∇X₀`, `ΔX₀`

Source `the November 2 reference manuscript` 4181-4192 (the separated-kernel
estimates prove convergence of the primitive and its differentiated versions).
At `(ρ,0,z)`, `ρ ≥ r > r_o`, every one of the integrands `ρ · (·)_z` is bounded by
`C (1+|z|) (ρ - r_o)^{-3/2}`, uniformly in the phase.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcd_alg1 {ρ D w κ C u : ℝ} (hDw : D * w = 1) (hρ : ρ ≤ κ * D) (hC : 0 ≤ C) (hu : 0 ≤ u)
    (hw : 0 ≤ w) (j : ℕ) :
    ρ * (C * (u * w ^ (1 + j))) ≤ κ * C * u * w ^ j := by
  calc ρ * (C * (u * w ^ (1 + j))) ≤ (κ * D) * (C * (u * w ^ (1 + j))) :=
        mul_le_mul_of_nonneg_right hρ (by positivity)
    _ = κ * C * u * w ^ j * (D * w) := by ring
    _ = κ * C * u * w ^ j := by rw [hDw, mul_one]

theorem tcd_alg2 {ρ D w κ C u z : ℝ} (hDw : D * w = 1) (hρ : ρ ≤ κ * D) (hρ0 : 0 ≤ ρ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hw : 0 ≤ w) (hD : 0 ≤ D) (hκ : 0 ≤ κ) :
    ρ * (C * (u * w ^ 2) * (ρ + |z|)) ≤ C * u * κ * (κ + |z| * w) := by
  have h1 : ρ + |z| ≤ κ * D + |z| := by linarith
  calc ρ * (C * (u * w ^ 2) * (ρ + |z|)) ≤ (κ * D) * (C * (u * w ^ 2) * (κ * D + |z|)) := by
        apply mul_le_mul hρ _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * u * κ * (κ * (D * w) ^ 2 + |z| * w * (D * w)) := by ring
    _ = C * u * κ * (κ + |z| * w) := by rw [hDw]; ring

theorem tcd_half {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) {r : ℝ} (hrr : rOut < r) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (τ ρ z : ℝ), r ≤ ρ →
      |ρ * sepX0 ν μ T τ (!₂[ρ, 0, z] : Space) 2| ≤ Cb * (ρ - rOut) ^ (-(3 / 2 : ℝ)) ∧
      |ρ * sepX0 ν μ T τ (!₂[ρ, 0, z] : Space) 0| ≤ Cb * (ρ - rOut) ^ (-(3 / 2 : ℝ)) ∧
      |ρ * fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, z] : Space)
          (UnforcedLeray.coordinateVector 2) 2| ≤ Cb * (ρ - rOut) ^ (-(3 / 2 : ℝ)) ∧
      |ρ * fderiv ℝ (sepX0 ν μ T τ) (!₂[ρ, 0, z] : Space) (!₂[ρ, 0, z] : Space) 2| ≤
        Cb * (1 + |z|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)) ∧
      |ρ * physLap (sepX0 ν μ T τ) (!₂[ρ, 0, z] : Space) 2| ≤
        Cb * (1 + |z|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)) ∧
      |ρ * deriv (fun s => sepX0 ν μ T s (!₂[ρ, 0, z] : Space)) τ 2| ≤
        Cb * (1 + |z|) * (ρ - rOut) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hb⟩ := tcd_X0_bound hν hμ hr hP hT hM
  have hD1 : 0 < r - rOut := by linarith
  set w1 : ℝ := (r - rOut)⁻¹ with hw1
  have hw1p : 0 < w1 := inv_pos.2 hD1
  set κ : ℝ := r / (r - rOut) with hκ
  have hr0 : 0 < r := lt_of_le_of_lt hr hrr
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨κ * C * (2 + κ + w1 + 3 * ν * w1 ^ 2 + 3 * w1 ^ 2 + |μ + 1 / 2|), by positivity, ?_⟩
  intro τ ρ z hρr
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr0 hρr
  set p : Space := (!₂[ρ, 0, z] : Space) with hp
  have hϱ : ϱ p = ρ := tcd_varrho hρ0.le
  have hy : rOut < ϱ p := by rw [hϱ]; linarith
  set D : ℝ := ρ - rOut with hD
  have hDp : 0 < D := by rw [hD]; linarith
  set w : ℝ := D⁻¹ with hw
  have hwp : 0 < w := inv_pos.2 hDp
  have hDw : D * w = 1 := mul_inv_cancel₀ hDp.ne'
  have hwle : w ≤ w1 := by
    rw [hw, hw1]
    exact inv_anti₀ hD1 (by rw [hD]; linarith)
  have hρκ : ρ ≤ κ * D := by
    rw [hκ, hD, div_mul_eq_mul_div, le_div_iff₀ hD1]
    nlinarith
  set u : ℝ := D ^ (-(3 / 2 : ℝ)) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hDp.le _
  obtain ⟨hj, hW⟩ := hb τ p hy
  rw [hϱ] at hj hW
  have sp : ∀ j : ℕ, (ρ - rOut) ^ (-(5 / 2 : ℝ) - j) = u * w ^ (1 + j) := fun j =>
    tcd_rpow_split D hDp j
  have a0 : ‖sepX0 ν μ T τ p‖ ≤ C * (u * w ^ 1) := by
    have := hj 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    have e := sp 0
    simp only [Nat.cast_zero, sub_zero] at this e
    rw [e] at this
    simpa using this
  have a1 : ‖fderiv ℝ (sepX0 ν μ T τ) p‖ ≤ C * (u * w ^ 2) := by
    have := hj 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at this
    have e := sp 1
    simp only [Nat.cast_one] at this e
    rw [e] at this
    simpa using this
  have a2 : ‖iteratedFDeriv ℝ 2 (sepX0 ν μ T τ) p‖ ≤ C * (u * w ^ 3) := by
    have := hj 2 (by norm_num)
    have e := sp 2
    simp only [Nat.cast_ofNat] at this e
    rw [e] at this
    simpa using this
  have a3 : ‖IIIa.sepW ν (μ : ℂ) T p τ‖ ≤ C * (u * w ^ 1) := by
    have e := sp 0
    simp only [Nat.cast_zero, sub_zero] at e
    rw [e] at hW
    simpa using hW
  have hcd : ContDiffAt ℝ 2 (sepX0 ν μ T τ) p := tcd_X0_cd hν hμ hr hP hT hM τ hy
  have comp : ∀ (v : Space) (i : Fin 3), |v i| ≤ ‖v‖ := fun v i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hpn : ‖p‖ ≤ ρ + |z| := tcd_norm_pt ρ z hρ0.le
  -- the five basic weighted bounds
  have b_i : ∀ i : Fin 3, |ρ * sepX0 ν μ T τ p i| ≤ κ * C * u := by
    intro i
    rw [abs_mul, abs_of_pos hρ0]
    calc ρ * |sepX0 ν μ T τ p i| ≤ ρ * (C * (u * w ^ 1)) :=
          mul_le_mul_of_nonneg_left ((comp _ i).trans a0) hρ0.le
      _ ≤ κ * C * u * w ^ 0 := tcd_alg1 hDw hρκ hC0 hu0 hwp.le 0
      _ = κ * C * u := by ring
  have b_v : |ρ * fderiv ℝ (sepX0 ν μ T τ) p (UnforcedLeray.coordinateVector 2) 2| ≤
      κ * C * w1 * u := by
    rw [abs_mul, abs_of_pos hρ0]
    have h1 : |fderiv ℝ (sepX0 ν μ T τ) p (UnforcedLeray.coordinateVector 2) 2| ≤
        C * (u * w ^ 2) := by
      refine (comp _ 2).trans ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [tcd_norm_cv, mul_one]
      exact a1
    calc ρ * |fderiv ℝ (sepX0 ν μ T τ) p (UnforcedLeray.coordinateVector 2) 2|
        ≤ ρ * (C * (u * w ^ 2)) := mul_le_mul_of_nonneg_left h1 hρ0.le
      _ ≤ κ * C * u * w ^ 1 := tcd_alg1 hDw hρκ hC0 hu0 hwp.le 1
      _ ≤ κ * C * u * w1 := by
          rw [pow_one]; exact mul_le_mul_of_nonneg_left hwle (by positivity)
      _ = κ * C * w1 * u := by ring
  have b_g : |ρ * fderiv ℝ (sepX0 ν μ T τ) p p 2| ≤ C * u * κ * (κ + |z| * w1) := by
    rw [abs_mul, abs_of_pos hρ0]
    have h1 : |fderiv ℝ (sepX0 ν μ T τ) p p 2| ≤ C * (u * w ^ 2) * (ρ + |z|) := by
      refine (comp _ 2).trans ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul a1 hpn (norm_nonneg _) (by positivity)
    calc ρ * |fderiv ℝ (sepX0 ν μ T τ) p p 2| ≤ ρ * (C * (u * w ^ 2) * (ρ + |z|)) :=
          mul_le_mul_of_nonneg_left h1 hρ0.le
      _ ≤ C * u * κ * (κ + |z| * w) := tcd_alg2 hDw hρκ hρ0.le hC0 hu0 hwp.le hDp.le hκ0
      _ ≤ C * u * κ * (κ + |z| * w1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := mul_le_mul_of_nonneg_left hwle (abs_nonneg z)
          linarith
  have b_l : |ρ * physLap (sepX0 ν μ T τ) p 2| ≤ 3 * κ * C * w1 ^ 2 * u := by
    rw [abs_mul, abs_of_pos hρ0]
    have h1 : |physLap (sepX0 ν μ T τ) p 2| ≤ 3 * (C * (u * w ^ 3)) :=
      (comp _ 2).trans ((tcd_physLap_norm hcd).trans (by linarith))
    calc ρ * |physLap (sepX0 ν μ T τ) p 2| ≤ ρ * (3 * (C * (u * w ^ 3))) :=
          mul_le_mul_of_nonneg_left h1 hρ0.le
      _ = 3 * (ρ * (C * (u * w ^ (1 + 2)))) := by ring
      _ ≤ 3 * (κ * C * u * w ^ 2) :=
          mul_le_mul_of_nonneg_left (tcd_alg1 hDw hρκ hC0 hu0 hwp.le 2) (by norm_num)
      _ ≤ 3 * (κ * C * u * w1 ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hwp.le hwle 2) (by positivity)
      _ = 3 * κ * C * w1 ^ 2 * u := by ring
  have hq : 0 ≤ κ * C * u := by positivity
  have b_t : |ρ * deriv (fun s => sepX0 ν μ T s p) τ 2| ≤
      κ * C * u * (1 + (1 / 2) * (κ + |z| * w1) + 3 * ν * w1 ^ 2 + |μ + 1 / 2|) := by
    rw [tcd_freeEq hν hμ hr hP hT hM τ hy]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hWc : |ρ * sepWre ν μ T τ p 2| ≤ κ * C * u := by
      rw [abs_mul, abs_of_pos hρ0]
      have h1 : |sepWre ν μ T τ p 2| ≤ C * (u * w ^ 1) := by
        have e1 : |sepWre ν μ T τ p 2| ≤ ‖IIIa.sepW ν (μ : ℂ) T p τ‖ := by
          simp only [sepWre, PiLp.toLp_apply, Real.norm_eq_abs]
          exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm (IIIa.sepW ν (μ : ℂ) T p τ) 2)
        exact e1.trans a3
      calc ρ * |sepWre ν μ T τ p 2| ≤ ρ * (C * (u * w ^ 1)) :=
            mul_le_mul_of_nonneg_left h1 hρ0.le
        _ ≤ κ * C * u * w ^ 0 := tcd_alg1 hDw hρκ hC0 hu0 hwp.le 0
        _ = κ * C * u := by ring
    have hX := b_i 2
    have hG := b_g
    have hL := b_l
    have e : ρ * (sepWre ν μ T τ p 2 + 1 / 2 * fderiv ℝ (sepX0 ν μ T τ) p p 2 +
        ν * physLap (sepX0 ν μ T τ) p 2 - (μ + 1 - 1 / 2) * sepX0 ν μ T τ p 2) =
        ρ * sepWre ν μ T τ p 2 + 1 / 2 * (ρ * fderiv ℝ (sepX0 ν μ T τ) p p 2) +
        ν * (ρ * physLap (sepX0 ν μ T τ) p 2) + -((μ + 1 / 2) * (ρ * sepX0 ν μ T τ p 2)) := by
      ring
    rw [e]
    have t1 := abs_add_le (ρ * sepWre ν μ T τ p 2 + 1 / 2 * (ρ * fderiv ℝ (sepX0 ν μ T τ) p p 2) +
        ν * (ρ * physLap (sepX0 ν μ T τ) p 2)) (-((μ + 1 / 2) * (ρ * sepX0 ν μ T τ p 2)))
    have t2 := abs_add_le (ρ * sepWre ν μ T τ p 2 + 1 / 2 * (ρ * fderiv ℝ (sepX0 ν μ T τ) p p 2))
        (ν * (ρ * physLap (sepX0 ν μ T τ) p 2))
    have t3 := abs_add_le (ρ * sepWre ν μ T τ p 2)
        (1 / 2 * (ρ * fderiv ℝ (sepX0 ν μ T τ) p p 2))
    have m1 : |1 / 2 * (ρ * fderiv ℝ (sepX0 ν μ T τ) p p 2)| ≤ 1 / 2 * (C * u * κ * (κ + |z| * w1)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left hG (by norm_num)
    have m2 : |ν * (ρ * physLap (sepX0 ν μ T τ) p 2)| ≤ ν * (3 * κ * C * w1 ^ 2 * u) := by
      rw [abs_mul, abs_of_pos hν]
      exact mul_le_mul_of_nonneg_left hL hν.le
    have m3 : |(μ + 1 / 2) * (ρ * sepX0 ν μ T τ p 2)| ≤ |μ + 1 / 2| * (κ * C * u) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    rw [abs_neg] at t1
    have h := t1.trans (add_le_add (t2.trans (add_le_add (t3.trans (add_le_add hWc m1)) m2)) m3)
    refine h.trans (le_of_eq ?_)
    ring
  have hE1 : (1 : ℝ) ≤ 2 + κ + w1 + 3 * ν * w1 ^ 2 + 3 * w1 ^ 2 + |μ + 1 / 2| := by
    have := abs_nonneg (μ + 1 / 2)
    have : 0 ≤ 3 * ν * w1 ^ 2 := by positivity
    have : 0 ≤ 3 * w1 ^ 2 := by positivity
    linarith
  set E : ℝ := 2 + κ + w1 + 3 * ν * w1 ^ 2 + 3 * w1 ^ 2 + |μ + 1 / 2| with hE
  have hz := abs_nonneg z
  have hqE : κ * C * u ≤ κ * C * E * u := by nlinarith [mul_nonneg hq (sub_nonneg.2 hE1)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (b_i 2).trans hqE
  · exact (b_i 0).trans hqE
  · refine b_v.trans ?_
    have : 0 ≤ κ * C * u * (E - w1) := by
      apply mul_nonneg hq; rw [hE]
      have : 0 ≤ 3 * ν * w1 ^ 2 := by positivity
      have : 0 ≤ 3 * w1 ^ 2 := by positivity
      have := abs_nonneg (μ + 1 / 2)
      linarith
    nlinarith
  · have h1 : 0 ≤ κ * C * u * (E - κ) := by
      apply mul_nonneg hq; rw [hE]
      have : 0 ≤ 3 * ν * w1 ^ 2 := by positivity
      have : 0 ≤ 3 * w1 ^ 2 := by positivity
      have := abs_nonneg (μ + 1 / 2)
      linarith
    have h2 : 0 ≤ κ * C * u * (E - w1) := by
      apply mul_nonneg hq; rw [hE]
      have : 0 ≤ 3 * ν * w1 ^ 2 := by positivity
      have : 0 ≤ 3 * w1 ^ 2 := by positivity
      have := abs_nonneg (μ + 1 / 2)
      linarith
    nlinarith [mul_nonneg h2 hz]
  · have h1 : 0 ≤ κ * C * u * (E - 3 * w1 ^ 2) := by
      apply mul_nonneg hq; rw [hE]
      have : 0 ≤ 3 * ν * w1 ^ 2 := by positivity
      have := abs_nonneg (μ + 1 / 2)
      have : 0 ≤ κ := hκ0
      linarith
    nlinarith [mul_nonneg hq hz, mul_nonneg h1 hz]
  · have h1 : 0 ≤ κ * C * u * (E - 1 - (1 / 2) * κ - 3 * ν * w1 ^ 2 - |μ + 1 / 2|) := by
      apply mul_nonneg hq; rw [hE]
      have : 0 ≤ 3 * w1 ^ 2 := by positivity
      have : 0 ≤ κ := hκ0
      have := hw1p.le
      linarith
    have h2 : 0 ≤ κ * C * u * (E - (1 / 2) * w1) := by
      apply mul_nonneg hq; rw [hE]
      have : 0 ≤ 3 * ν * w1 ^ 2 := by positivity
      have : 0 ≤ 3 * w1 ^ 2 := by positivity
      have := abs_nonneg (μ + 1 / 2)
      have : 0 ≤ κ := hκ0
      linarith
    refine b_t.trans ?_
    nlinarith [mul_nonneg h2 hz, mul_nonneg h1 hz]

end UnforcedLeray.Short.PartIIIb.Concrete

end
