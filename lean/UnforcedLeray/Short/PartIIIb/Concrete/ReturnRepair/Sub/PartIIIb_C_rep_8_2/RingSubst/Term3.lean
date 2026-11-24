import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6

/-!
# Term 3 of the four-term substitution (`PartIII-b:C/rep/8/2/6/3`)

Source `the November 2 reference manuscript` 5473-5475: `(U⊗U):D²X` is an error.
`|U| ≤ √s(|v| + ε𝔴₃) ≲ √s 𝔴₃` (ring-chart rules), `|D²X| ≤ ε⁴s³N` (mean jets), and
`𝔴₃² ≤ P_ν 𝔴₄` because `𝔴₃ ≤ 𝔴₄ ≤ P_ν` on the young range (`TrainMomentAt`), `s ≤ 1/ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem norm_vecSp_le (w : Vec3) : ‖vecSp w‖ ≤ 2 * ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM := norm_nonneg w
  have h : ∀ i, ‖(vecSp w) i‖ ^ 2 ≤ ‖w‖ ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (by simpa [vecSp] using norm_le_pi_norm w i) 2
  calc √(∑ i, ‖(vecSp w) i‖ ^ 2) ≤ √((2 * ‖w‖) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [Fin.sum_univ_three]
        nlinarith [h 0, h 1, h 2]
    _ = 2 * ‖w‖ := Real.sqrt_sq (by positivity)

theorem norm_meridPair_le (a : Space) : ‖(!₂[a 0, a 2] : Merid)‖ ≤ ‖a‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_three]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [sq_nonneg ‖a 1‖]

theorem trainWeight_three_le_four (L : ReturnLevel) (p : Chart) :
    trainWeight 3 L p ≤ trainWeight 4 L p := by
  unfold trainWeight
  refine mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [abs_nonneg p.2.2]) (by norm_num)) ?_
  exact Finset.sum_nonneg fun j _ => by positivity

theorem rpow_five_half (s : ℝ) (hs : 0 ≤ s) : s ^ (5 / 2 : ℝ) = Real.sqrt s ^ 5 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num

section Pointwise

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- The ring-chart rules bound `U_raw` by `√s 𝔴₃`. -/
theorem norm_rawU_le {C : ℝ} {k : ℕ} (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (h1 : RingChartRulesAt Pl L C k) {p : Chart} (hp : 0 < p.1) (hp1 : p.1 ≤ 1 / L.ν) :
    ‖rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
      (2 + |C|) * L.ν⁻¹ ^ k * Real.sqrt p.1 * trainWeight 3 L p := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP : 1 ≤ L.ν⁻¹ ^ k := one_le_pow₀ ((one_le_inv₀ hν).2 hν1)
  have hP0 : 0 ≤ L.ν⁻¹ ^ k := by positivity
  have hs := Real.sqrt_nonneg p.1
  have hW := trainWeight_nonneg 3 L p
  have hv := trainV_le_weight 3 L hp
  have e1 := (h1 p hp hp1).1
  have e2 : ‖Real.sqrt p.1 • vecSp (emb (trainV L p.1 p.2))‖ ≤
      2 * Real.sqrt p.1 * trainWeight 3 L p := by
    rw [norm_smul, Real.norm_of_nonneg hs]
    have := (norm_vecSp_le (emb (trainV L p.1 p.2))).trans
      (mul_le_mul_of_nonneg_left ((norm_emb_le _).trans hv) (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have e3 : C * L.ν⁻¹ ^ k * L.ε * Real.sqrt p.1 * trainWeight 3 L p ≤
      |C| * L.ν⁻¹ ^ k * Real.sqrt p.1 * trainWeight 3 L p := by
    have : C * L.ν⁻¹ ^ k * L.ε ≤ |C| * L.ν⁻¹ ^ k := by
      calc C * L.ν⁻¹ ^ k * L.ε ≤ |C| * L.ν⁻¹ ^ k * L.ε :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hP0) hε.le
        _ ≤ |C| * L.ν⁻¹ ^ k * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
        _ = _ := mul_one _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hs) hW
  have e4 : 2 * Real.sqrt p.1 * trainWeight 3 L p ≤
      2 * L.ν⁻¹ ^ k * Real.sqrt p.1 * trainWeight 3 L p := by
    have : 2 * Real.sqrt p.1 * trainWeight 3 L p * 1 ≤
        2 * Real.sqrt p.1 * trainWeight 3 L p * L.ν⁻¹ ^ k :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  have := norm_le_insert' (rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p))
    (Real.sqrt p.1 • vecSp (emb (trainV L p.1 p.2)))
  nlinarith

/-- **Term 3 at one regime** (source 5473-5475). -/
theorem ringTerm3At_of {C1 C2 C3 : ℝ} {k1 k2 k3 : ℕ} (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (h1 : RingChartRulesAt Pl L C1 k1) (h2 : MeanJetAt Pl K L μ C2 k2)
    (h3 : TrainMomentAt L C3 k3) :
    RingTerm3At Pl K L μ (9 * (2 + |C1|) ^ 2 * |C3| * |C2|) (2 * k1 + k3 + k2 + 1) := by
  intro T p hp hp1
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hsp : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hrr : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hp.le
  have hU := norm_rawU_le Pl L hν1 hε1 h1 hp hp1
  have h3r : p.1 ^ (3 : ℝ) = Real.sqrt p.1 ^ 6 := by
    have : Real.sqrt p.1 ^ 6 = (Real.sqrt p.1 ^ 2) ^ 3 := by ring
    rw [this, hrr]; norm_cast
  have h52 : p.1 ^ (5 / 2 : ℝ) = Real.sqrt p.1 ^ 5 := rpow_five_half p.1 hp.le
  set r := Real.sqrt p.1 with hr
  set Uf := rawU Pl L (NearInst.chartTau L.ε⁻¹ p) with hUf
  set U := Uf (NearInst.chartY L.ε⁻¹ p) with hUdef
  set W3 := trainWeight 3 L p with hW3
  set W4 := trainWeight 4 L p with hW4
  have hW30 : 0 ≤ W3 := trainWeight_nonneg 3 L p
  have hW34 : W3 ≤ W4 := trainWeight_three_le_four L p
  have hW4b : W4 ≤ |C3| * L.ν⁻¹ ^ k3 :=
    (h3.2.1 p hp hp1).trans (mul_le_mul_of_nonneg_right (le_abs_self C3) (by positivity))
  have hW3sq : W3 ^ 2 ≤ |C3| * L.ν⁻¹ ^ k3 * W4 := by
    rw [sq]
    exact mul_le_mul (hW34.trans hW4b) hW34 hW30 (by positivity)
  set MU := (2 + |C1|) * L.ν⁻¹ ^ k1 * r * W3 with hMU
  have hMU0 : 0 ≤ MU := by positivity
  have hDX := (h2 T p hp hp1).2.2
  have hUj : ∀ j : Fin 3, ‖U j‖ₑ ≤ ENNReal.ofReal MU := fun j => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((PiLp.norm_apply_le U j).trans hU)
  set b : ℝ := |C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4 * p.1 ^ (3 : ℝ) with hb
  have hb0 : 0 ≤ b := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal b * oldN1 Pl K L T with hB
  have hbC : C2 * L.ν⁻¹ ^ k2 * L.ε ^ 4 * p.1 ^ (3 : ℝ) ≤ b := by
    have e0 : 0 ≤ L.ν⁻¹ ^ k2 := by positivity
    have e1 : 0 ≤ L.ε ^ 4 := by positivity
    have e2 : 0 ≤ p.1 ^ (3 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C2) e0) e1) e2
  have hDB : ∀ j l : Fin 3,
      ‖physPd2 (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j l
          (NearInst.chartY L.ε⁻¹ p)‖ₑ ≤ B := fun j l =>
    (hDX j l).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hbC) _)
  set a := physUUD2 Uf (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
    (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) with ha
  have hc : ‖wardC3 Pl K L μ T p‖ₑ ≤ ENNReal.ofReal r⁻¹ * ‖a‖ₑ := by
    unfold wardC3 coefOf
    rw [enorm_smul, Real.enorm_of_nonneg (inv_nonneg.2 hsp.le)]
    refine mul_le_mul_right ?_ _
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_meridPair_le a)
  have hsum : ‖a‖ₑ ≤ 9 * (ENNReal.ofReal MU * ENNReal.ofReal MU * B) := by
    calc ‖a‖ₑ = ‖∑ j : Fin 3, ∑ l : Fin 3, (U j * U l) •
          physPd2 (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p))
            j l (NearInst.chartY L.ε⁻¹ p)‖ₑ := rfl
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖(U j * U l) •
          physPd2 (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p))
            j l (NearInst.chartY L.ε⁻¹ p)‖ₑ :=
          (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => enorm_sum_le _ _)
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ENNReal.ofReal MU * ENNReal.ofReal MU * B := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
          rw [enorm_smul, enorm_mul]
          exact mul_le_mul' (mul_le_mul' (hUj j) (hUj l)) (hDB j l)
      _ = 9 * (ENNReal.ofReal MU * ENNReal.ofReal MU * B) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hkey : r ^ 7 * W3 ^ 2 ≤ r ^ 5 * (L.ν⁻¹ * (|C3| * L.ν⁻¹ ^ k3 * W4)) := by
    have h2s : r ^ 2 ≤ L.ν⁻¹ := by
      rw [hrr]; simpa [one_div] using hp1
    have : r ^ 7 * W3 ^ 2 = r ^ 5 * (r ^ 2 * W3 ^ 2) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul h2s hW3sq (by positivity) (by positivity)
  have hreal : r⁻¹ * (9 * (MU * MU * b)) ≤ 9 * (2 + |C1|) ^ 2 * |C3| * |C2| *
      L.ν⁻¹ ^ (2 * k1 + k3 + k2 + 1) * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * W4 := by
    have hpow : L.ν⁻¹ ^ (2 * k1 + k3 + k2 + 1) =
        (L.ν⁻¹ ^ k1) ^ 2 * L.ν⁻¹ ^ k3 * L.ν⁻¹ ^ k2 * L.ν⁻¹ := by ring
    have hX : 0 ≤ 9 * (2 + |C1|) ^ 2 * (L.ν⁻¹ ^ k1) ^ 2 * |C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4 := by
      positivity
    calc r⁻¹ * (9 * (MU * MU * b))
        = (9 * (2 + |C1|) ^ 2 * (L.ν⁻¹ ^ k1) ^ 2 * |C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4) *
            (r ^ 7 * W3 ^ 2) := by
          rw [hMU, hb, h3r]; field_simp
      _ ≤ (9 * (2 + |C1|) ^ 2 * (L.ν⁻¹ ^ k1) ^ 2 * |C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4) *
            (r ^ 5 * (L.ν⁻¹ * (|C3| * L.ν⁻¹ ^ k3 * W4))) := mul_le_mul_of_nonneg_left hkey hX
      _ = _ := by rw [hpow, h52]; ring
  have hfin : ENNReal.ofReal r⁻¹ * (9 * (ENNReal.ofReal MU * ENNReal.ofReal MU * B)) ≤
      ENNReal.ofReal (9 * (2 + |C1|) ^ 2 * |C3| * |C2| * L.ν⁻¹ ^ (2 * k1 + k3 + k2 + 1) *
        L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * W4) * oldN1 Pl K L T := by
    have e : ENNReal.ofReal (r⁻¹ * (9 * (MU * MU * b))) =
        ENNReal.ofReal r⁻¹ * (9 * (ENNReal.ofReal MU * ENNReal.ofReal MU * ENNReal.ofReal b)) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hsp.le), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hMU0, ENNReal.ofReal_ofNat]
    calc ENNReal.ofReal r⁻¹ * (9 * (ENNReal.ofReal MU * ENNReal.ofReal MU * B))
        = ENNReal.ofReal (r⁻¹ * (9 * (MU * MU * b))) * oldN1 Pl K L T := by
          rw [e, hB]; ring
      _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
  exact hc.trans ((mul_le_mul_right hsum _).trans hfin)

end Pointwise

/-- **Term 3 along the sequence** (source 5473-5475). -/
theorem ringTerm3_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h6 : D.ActualJet) (h7 : D.JetClock) (h1 : D.RingChartRules) (h2 : D.MeanJet)
    (h3 : D.TrainMoment) : D.RingTerm3 := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  obtain ⟨C3, k3, e3⟩ := h3
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨9 * (2 + |C1|) ^ 2 * |C3| * |C2|, 2 * k1 + k3 + k2 + 1, ?_⟩
  filter_upwards [e1, e2, e3, hle] with n a1 a2 a3 hν z hz
  exact ringTerm3At_of D.Pl D.K (D.level n) (D.mu n z) hν.1 hν.2 a1 (a2 z hz) a3

end UnforcedLeray.Short.PartIIIb.Concrete
