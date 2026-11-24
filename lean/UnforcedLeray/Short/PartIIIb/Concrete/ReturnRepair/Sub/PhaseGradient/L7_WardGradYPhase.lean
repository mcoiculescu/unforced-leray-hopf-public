import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Pt2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Jet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L3_SepX0PhaseBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L4_OutPrimPhaseBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.AxisNull

/-!
# `PartIII-b:C/rep/2/7`: `WardGradYPhase`

Source `the November 2 reference manuscript` 4171, 4192-4200, 4203-4214, 5212-5223.
`Y = 𝒞_y Re W_μ + [D_{μ+1}, 𝒞_y]X₀` (free equation `D_{μ+1}X₀ = Re W_μ`, task `/6`), so `DY` is
pointwise bounded (`wgyPointwise`) by jets of `Re W_μ` (`j ≤ 1`), of `X₀` (`j ≤ 2`) and the outward
primitives; the slice norms are bounded by `SepWPhaseSup` (`wgy_jet_phase`), `SepX0PhaseBound` and
`OutPrimPhaseBound`, with `L⁻² ≤ ν⁻¹` (`L = R√ν`, `R ≥ 1`) for the two terms with `L⁻²` extra.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma wgy_lq_add {f g : Space → ℝ≥0∞} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    {a b : ℝ≥0∞} (h1 : lqNorm (22 / 3) f ≤ a) (h2 : lqNorm (22 / 3) g ≤ b) :
    lqNorm (22 / 3) (fun y => f y + g y) ≤ a + b :=
  (lqNorm_add_le (by norm_num) hf hg).trans (add_le_add h1 h2)

lemma wgy_term (κ B M Y : ℝ) (F : ℝ≥0∞) {g : Space → ℝ≥0∞} (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hk : κ * B ≤ M * Y) (hg : lqNorm (22 / 3) g ≤ ENNReal.ofReal B * F) :
    lqNorm (22 / 3) (fun y => ENNReal.ofReal κ * g y) ≤ ENNReal.ofReal (M * Y) * F := by
  rw [lqNorm_const_mul (by norm_num) _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal κ * lqNorm (22 / 3) g ≤ ENNReal.ofReal κ * (ENNReal.ofReal B * F) :=
        mul_le_mul_of_nonneg_left hg zero_le
    _ = ENNReal.ofReal (κ * B) * F := by rw [← mul_assoc, ← ENNReal.ofReal_mul hκ]
    _ ≤ ENNReal.ofReal (M * Y) * F := by gcongr

lemma wgy_k (κ D c0 L e Y M0 : ℝ) (hD : 0 ≤ D) (hc0 : 0 ≤ c0) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (h : κ * L ^ e ≤ M0 * Y) : κ * (D * (c0 * L) ^ e) ≤ (M0 * (D * c0 ^ e)) * Y := by
  rw [Real.mul_rpow hc0 hL]
  have h0 : 0 ≤ D * c0 ^ e := mul_nonneg hD (Real.rpow_nonneg hc0 _)
  calc κ * (D * (c0 ^ e * L ^ e)) = (D * c0 ^ e) * (κ * L ^ e) := by ring
    _ ≤ (D * c0 ^ e) * (M0 * Y) := mul_le_mul_of_nonneg_left h h0
    _ = (M0 * (D * c0 ^ e)) * Y := by ring

lemma wgy_sum (k1 k2 k3 C2 m4 m5 m6 m7 m8 Y : ℝ) (F : ℝ≥0∞) (h1 : 0 ≤ k1) (h2 : 0 ≤ k2)
    (h3 : 0 ≤ k3) (hC : 0 ≤ C2) (h4 : 0 ≤ m4) (h5 : 0 ≤ m5) (h6 : 0 ≤ m6) (h7 : 0 ≤ m7)
    (h8 : 0 ≤ m8) (hY : 0 ≤ Y) :
    ENNReal.ofReal (k1 * Y) * F + ENNReal.ofReal (k2 * Y) * F + ENNReal.ofReal (k3 * Y) * F +
      ENNReal.ofReal C2 * (ENNReal.ofReal (m4 * Y) * F + ENNReal.ofReal (m5 * Y) * F +
        ENNReal.ofReal (m6 * Y) * F + ENNReal.ofReal (m7 * Y) * F +
        ENNReal.ofReal (m8 * Y) * F) =
      ENNReal.ofReal ((k1 + k2 + k3 + C2 * (m4 + m5 + m6 + m7 + m8)) * Y) * F := by
  have e : (k1 + k2 + k3 + C2 * (m4 + m5 + m6 + m7 + m8)) * Y =
      k1 * Y + k2 * Y + k3 * Y + C2 * (m4 * Y + m5 * Y + m6 * Y + m7 * Y + m8 * Y) := by ring
  rw [e, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul hC, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [add_mul, mul_add, mul_assoc]

/-- **`WardGradYPhase` (source 4171, 4192-4200, 5212-5223).** -/
theorem wardGradYPhase : WardGradYPhase := by
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨C1, C2, hC1, hC2, hPt⟩ := wgyPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨CW0, hCW0, HW0⟩ := wgy_jet_phase σ₁ σ₂ hσ 0 (by norm_num)
  obtain ⟨CW1, hCW1, HW1⟩ := wgy_jet_phase σ₁ σ₂ hσ 1 (by norm_num)
  obtain ⟨D0, hD0, H0⟩ := sepX0PhaseBound σ₁ σ₂ hσ 0 (by norm_num)
  obtain ⟨D1, hD1, H1⟩ := sepX0PhaseBound σ₁ σ₂ hσ 1 (by norm_num)
  obtain ⟨D2, hD2, H2⟩ := sepX0PhaseBound σ₁ σ₂ hσ 2 (by norm_num)
  obtain ⟨Co, hCo, Ho⟩ := outPrimPhaseBound σ₁ σ₂ hσ
  set c0 : ℝ := 1 - Real.sqrt (5 / 6) with hc0
  have hs56 : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hc0pos : 0 < c0 := by rw [hc0]; linarith
  set e0 : ℝ := -4 - ((0 : ℕ) : ℝ) + 9 / 11 with he0
  set e1 : ℝ := -4 - ((1 : ℕ) : ℝ) + 9 / 11 with he1
  set e2 : ℝ := -4 - ((2 : ℕ) : ℝ) + 9 / 11 with he2
  refine ⟨(CW1 * c0 ^ e1 + C1 * (CW0 * c0 ^ e0) + C1 * Co) +
      C2 * ((D0 * c0 ^ e0) + (D1 * c0 ^ e1) + (D2 * c0 ^ e2) + (D1 * c0 ^ e1) + Co), 1,
    by positivity, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set F : ℝ≥0∞ := IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) with hF
  have hLsq : ν * R ^ 2 = L ^ 2 := by
    rw [hL, mul_pow, Real.sq_sqrt hν.le]; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * L := by
    rw [hL, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hD : L - R * Real.sqrt (5 * ν / 6) = c0 * L := by rw [hrO, hc0]; ring
  have hrOnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hlt : R * Real.sqrt (5 * ν / 6) < L := by
    have : 0 < c0 * L := mul_pos hc0pos hLpos
    linarith
  -- the common size `Y = ν⁻¹ L^{-46/11}`
  set X : ℝ := L ^ (-(46 / 11 : ℝ)) with hX
  set Y : ℝ := ν⁻¹ * X with hY
  have hX0 : 0 ≤ X := Real.rpow_nonneg hLpos.le _
  have hν1' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : X ≤ Y := by
    calc X = 1 * X := (one_mul X).symm
      _ ≤ ν⁻¹ * X := mul_le_mul_of_nonneg_right hν1' hX0
  have hY2 : L ^ (-(68 / 11 : ℝ)) ≤ Y := by
    have h2 : L ^ (-(68 / 11 : ℝ)) = L ^ (-2 : ℝ) * X := by
      rw [hX, ← Real.rpow_add hLpos]; congr 1; norm_num
    have h3 : L ^ (-2 : ℝ) ≤ ν⁻¹ := by
      have : L ^ (-2 : ℝ) = (L ^ 2)⁻¹ := by
        rw [Real.rpow_neg hLpos.le]; norm_cast
      rw [this, ← hLsq]
      refine inv_anti₀ hν ?_
      nlinarith [mul_pos hν (pow_pos hR 2), sq_nonneg R, mul_nonneg hν.le (sq_nonneg (R - 1)),
        mul_nonneg hν.le (sq_nonneg R)]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h3 hX0
  have hLinv : L⁻¹ = L ^ (-1 : ℝ) := (Real.rpow_neg_one L).symm
  have hLinv2 : L⁻¹ ^ 2 = L ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hLinv3 : L⁻¹ ^ 3 = L ^ (-3 : ℝ) := by
    rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hmul : ∀ a b c : ℝ, a + b = c → L ^ a * L ^ b = L ^ c := fun a b c h => by
    rw [← Real.rpow_add hLpos, h]
  refine Filter.Eventually.of_forall (fun τ => ?_)
  obtain ⟨m1, m0, mP⟩ := wgxMeas ν μ R P hν hR hP0 T hT hSM τ
  obtain ⟨w1, w0, wP⟩ := wgyMeas_W ν μ R P T hT τ
  have m2 := wgyMeas_X2 ν μ L T τ
  have hq : (1 : ℝ) ≤ 22 / 3 := by norm_num
  have hq0 : (0 : ℝ) < 22 / 3 := by norm_num
  have haxis : ∀ᵐ y : Space, 0 < ϱ y := by
    have : ∀ᵐ y : Space, y ∉ {y : Space | ϱ y = 0} :=
      measure_eq_zero_iff_ae_notMem.1 wgxAxisNull
    filter_upwards [this] with y hy
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hy h.symm)
  -- the slice bounds
  have eW1 := HW1 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have eW0 := HW0 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have hE1 := H1 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have hE0 := H0 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have hE2 := H2 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  obtain ⟨eoW, eoX⟩ := Ho ν μ R P hν hR hP0 hP1 hμ T hT hSM τ
  rw [hD] at eW1 eW0 hE1 hE0 hE2
  have eoW' : lqNorm (22 / 3) (wgyWPsi ν μ R T τ) ≤
      ENNReal.ofReal (Co * L ^ (-(13 / 11 : ℝ))) * F := eoW
  have eoX' : lqNorm (22 / 3) (wgxPsi ν μ R T τ) ≤
      ENNReal.ofReal (Co * L ^ (-(13 / 11 : ℝ))) * F := eoX
  have eW1' : lqNorm (22 / 3) (wgyWJet 1 ν μ L T τ) ≤
      ENNReal.ofReal (CW1 * (c0 * L) ^ e1) * F := eW1
  have eW0' : lqNorm (22 / 3) (wgyWJet 0 ν μ L T τ) ≤
      ENNReal.ofReal (CW0 * (c0 * L) ^ e0) * F := eW0
  have e1' : lqNorm (22 / 3) (wgxJet 1 ν μ L T τ) ≤
      ENNReal.ofReal (D1 * (c0 * L) ^ e1) * F := hE1
  have e0' : lqNorm (22 / 3) (wgxJet 0 ν μ L T τ) ≤
      ENNReal.ofReal (D0 * (c0 * L) ^ e0) * F := hE0
  have e2' : lqNorm (22 / 3) (wgxJet 2 ν μ L T τ) ≤
      ENNReal.ofReal (D2 * (c0 * L) ^ e2) * F := hE2
  -- exponent bookkeeping
  have x1 : L ^ e1 = X := by rw [hX, he1]; congr 1; norm_num
  have x0 : L ^ (-1 : ℝ) * L ^ e0 = X := by
    rw [hmul _ _ (-(46 / 11)) (by rw [he0]; norm_num)]
  have x2 : L⁻¹ * L ^ e2 = L ^ (-(68 / 11 : ℝ)) := by
    rw [hLinv, hmul _ _ (-(68 / 11)) (by rw [he2]; norm_num)]
  have x4 : L ^ (-2 : ℝ) * L ^ e1 = L ^ (-(68 / 11 : ℝ)) := by
    rw [hmul _ _ (-(68 / 11)) (by rw [he1]; norm_num)]
  have x3 : L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ)) = X := by
    rw [hX, hmul _ _ (-(46 / 11)) (by norm_num)]
  have x5 : L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ)) = X := x3
  have hc0n : 0 ≤ c0 := hc0pos.le
  -- the eight term bounds
  have t1 : lqNorm (22 / 3) (wgyWJet 1 ν μ L T τ) ≤
      ENNReal.ofReal ((1 * (CW1 * c0 ^ e1)) * Y) * F := by
    have := wgy_term 1 (CW1 * (c0 * L) ^ e1) (1 * (CW1 * c0 ^ e1)) Y F (g := wgyWJet 1 ν μ L T τ)
      zero_le_one (mul_nonneg hCW1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k 1 CW1 c0 L e1 Y 1 hCW1 hc0n hLpos.le zero_le_one (by rw [x1, one_mul, one_mul]; exact hY1))
      eW1'
    simpa using this
  have t2 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (C1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y) ≤
      ENNReal.ofReal ((C1 * (CW0 * c0 ^ e0)) * Y) * F :=
    wgy_term (C1 * L ^ (-1 : ℝ)) (CW0 * (c0 * L) ^ e0) (C1 * (CW0 * c0 ^ e0)) Y F
      (by positivity) (mul_nonneg hCW0 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ CW0 c0 L e0 Y C1 hCW0 hc0n hLpos.le (by positivity) (by
        rw [mul_assoc, x0]; exact mul_le_mul_of_nonneg_left hY1 hC1)) eW0'
  have t3 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (C1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) ≤
      ENNReal.ofReal ((C1 * Co) * Y) * F :=
    wgy_term (C1 * L ^ (-3 : ℝ)) (Co * L ^ (-(13 / 11 : ℝ))) (C1 * Co) Y F
      (by positivity) (by positivity)
      (by
        calc C1 * L ^ (-3 : ℝ) * (Co * L ^ (-(13 / 11 : ℝ))) =
            (C1 * Co) * (L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ))) := by ring
          _ ≤ (C1 * Co) * Y := by rw [x3]; exact mul_le_mul_of_nonneg_left hY1 (by positivity))
      eoW'
  have q1 : lqNorm (22 / 3) (fun y => ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D0 * c0 ^ e0)) * Y) * F :=
    wgy_term L⁻¹ (D0 * (c0 * L) ^ e0) (1 * (D0 * c0 ^ e0)) Y F (inv_nonneg.2 hLpos.le)
      (mul_nonneg hD0 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D0 c0 L e0 Y 1 hD0 hc0n hLpos.le (inv_nonneg.2 hLpos.le) (by
        rw [hLinv, x0, one_mul]; exact hY1)) e0'
  have q2 : lqNorm (22 / 3) (wgxJet 1 ν μ L T τ) ≤
      ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F := by
    have := wgy_term 1 (D1 * (c0 * L) ^ e1) (1 * (D1 * c0 ^ e1)) Y F (g := wgxJet 1 ν μ L T τ)
      zero_le_one (mul_nonneg hD1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k 1 D1 c0 L e1 Y 1 hD1 hc0n hLpos.le zero_le_one (by rw [x1, one_mul, one_mul]; exact hY1))
      e1'
    simpa using this
  have q3 : lqNorm (22 / 3) (fun y => ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D2 * c0 ^ e2)) * Y) * F :=
    wgy_term L⁻¹ (D2 * (c0 * L) ^ e2) (1 * (D2 * c0 ^ e2)) Y F (inv_nonneg.2 hLpos.le)
      (mul_nonneg hD2 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D2 c0 L e2 Y 1 hD2 hc0n hLpos.le (inv_nonneg.2 hLpos.le) (by
        rw [x2, one_mul]; exact hY2)) e2'
  have q4 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F :=
    wgy_term (L⁻¹ ^ 2) (D1 * (c0 * L) ^ e1) (1 * (D1 * c0 ^ e1)) Y F (by positivity)
      (mul_nonneg hD1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D1 c0 L e1 Y 1 hD1 hc0n hLpos.le (by positivity) (by
        rw [hLinv2, x4, one_mul]; exact hY2)) e1'
  have q5 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) ≤
      ENNReal.ofReal ((1 * Co) * Y) * F :=
    wgy_term (L⁻¹ ^ 3) (Co * L ^ (-(13 / 11 : ℝ))) (1 * Co) Y F (by positivity) (by positivity)
      (by
        rw [hLinv3]
        calc L ^ (-3 : ℝ) * (Co * L ^ (-(13 / 11 : ℝ))) =
            Co * (L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ))) := by ring
          _ ≤ (1 * Co) * Y := by
              rw [x3, one_mul]
              calc Co * X ≤ Co * Y := mul_le_mul_of_nonneg_left hY1 hCo
                _ = Co * Y := rfl)
      eoX'
  -- Minkowski
  have mA2 : AEMeasurable (fun y => ENNReal.ofReal (C1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y)
      volume := w0.const_mul _
  have mA3 : AEMeasurable (fun y => ENNReal.ofReal (C1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y)
      volume := wP.const_mul _
  have mB1 : AEMeasurable (fun y => ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y) volume :=
    m0.const_mul _
  have mB3 : AEMeasurable (fun y => ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y) volume :=
    m2.const_mul _
  have mB4 : AEMeasurable (fun y => ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y) volume :=
    m1.const_mul _
  have mB5 : AEMeasurable (fun y => ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) volume :=
    mP.const_mul _
  have bA := wgy_lq_add ((w1.add mA2)) mA3 (wgy_lq_add w1 mA2 t1 t2) t3
  have bB := wgy_lq_add ((((mB1.add m1).add mB3).add mB4)) mB5
    (wgy_lq_add (((mB1.add m1).add mB3)) mB4
      (wgy_lq_add ((mB1.add m1)) mB3 (wgy_lq_add mB1 m1 q1 q2) q3) q4) q5
  unfold sliceLq
  calc lqNorm (22 / 3) (fun y => ENNReal.ofReal |‖fderiv ℝ (sepWY ν μ R χy T τ) y‖|)
      ≤ lqNorm (22 / 3) (fun y =>
          (wgyWJet 1 ν μ L T τ y + ENNReal.ofReal (C1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y +
            ENNReal.ofReal (C1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) +
          ENNReal.ofReal C2 *
            (ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
              ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y +
              ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y +
              ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y)) := by
        refine lqNorm_mono_ae hq0 ?_
        filter_upwards [haxis] with y hy
        have := hPt ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy
        rw [abs_of_nonneg (norm_nonneg _)]
        exact this
    _ ≤ lqNorm (22 / 3) (fun y => wgyWJet 1 ν μ L T τ y +
            ENNReal.ofReal (C1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y +
            ENNReal.ofReal (C1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) +
        lqNorm (22 / 3) (fun y => ENNReal.ofReal C2 *
            (ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
              ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y +
              ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y +
              ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y)) :=
        lqNorm_add_le hq ((w1.add mA2).add mA3)
          (AEMeasurable.const_mul ((((mB1.add m1).add mB3).add mB4).add mB5) (ENNReal.ofReal C2))
    _ ≤ (ENNReal.ofReal ((1 * (CW1 * c0 ^ e1)) * Y) * F +
          ENNReal.ofReal ((C1 * (CW0 * c0 ^ e0)) * Y) * F +
          ENNReal.ofReal ((C1 * Co) * Y) * F) +
        ENNReal.ofReal C2 * (ENNReal.ofReal ((1 * (D0 * c0 ^ e0)) * Y) * F +
          ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F +
          ENNReal.ofReal ((1 * (D2 * c0 ^ e2)) * Y) * F +
          ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F +
          ENNReal.ofReal ((1 * Co) * Y) * F) := by
        refine add_le_add bA ?_
        rw [lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top]
        exact mul_le_mul_of_nonneg_left bB zero_le
    _ = ENNReal.ofReal (((1 * (CW1 * c0 ^ e1)) + (C1 * (CW0 * c0 ^ e0)) + (C1 * Co) +
          C2 * ((1 * (D0 * c0 ^ e0)) + (1 * (D1 * c0 ^ e1)) + (1 * (D2 * c0 ^ e2)) +
            (1 * (D1 * c0 ^ e1)) + (1 * Co))) * Y) * F :=
        wgy_sum _ _ _ _ _ _ _ _ _ Y F (by positivity) (by positivity) (by positivity) hC2
          (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hY0
    _ = _ := by
        congr 2
        rw [hY, pow_one]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
