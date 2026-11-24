import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.L2Conv

/-!
# `L²(srcMeasure)` bounds for the jet terms `vrJetV` and `vrJetP` (`PartIII-b:C/rep/3/2`)

Source: `the November 2 reference manuscript`, 5233-5253.
Combines the pointwise `L^∞_τ L^∞_y` jet bound on `(DX, D²X)` with the `Y_2` bounds on `vCoefDens V`
and `‖∇p_V‖` via `ringL2Conv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The spatial first-and-second-derivative sum of `X` at `y`. -/
def vrXJetSum (X : Space → Space) (y : Space) : ℝ :=
  ∑ j : Fin 3, ‖physPd X j y‖ + ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖

theorem vrXJetSum_nonneg (X : Space → Space) (y : Space) : 0 ≤ vrXJetSum X y := by
  unfold vrXJetSum; positivity

theorem vrCoefDens_nonneg (V : Space → Space) (y : Space) : 0 ≤ vCoefDens V y := by
  unfold vCoefDens; positivity

theorem vr_xjet_bounds (X : Space → Space) (y : Space) :
    (∀ j : Fin 3, ‖physPd X j y‖ ≤ vrXJetSum X y) ∧
      (∀ j l : Fin 3, ‖physPd2 X j l y‖ ≤ vrXJetSum X y) := by
  have hS1 : 0 ≤ ∑ j : Fin 3, ‖physPd X j y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨fun j => ?_, fun j l => ?_⟩
  · have h : ‖physPd X j y‖ ≤ ∑ j' : Fin 3, ‖physPd X j' y‖ :=
      Finset.single_le_sum (f := fun j' => ‖physPd X j' y‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)
    unfold vrXJetSum; linarith
  · have h : ‖physPd2 X j l y‖ ≤ ∑ j' : Fin 3, ∑ l' : Fin 3, ‖physPd2 X j' l' y‖ :=
      chgPt_single_le (f := fun j' l' => ‖physPd2 X j' l' y‖) (fun _ _ => norm_nonneg _) j l
    unfold vrXJetSum; linarith

theorem vr_vcoef_bounds (V : Space → Space) (y : Space) :
    ‖V y‖ ^ 2 ≤ vCoefDens V y ∧
      (∀ j : Fin 3, ‖physPd V j y‖ ≤ vCoefDens V y) ∧
      (∀ j l : Fin 3, ‖physPd2 V j l y‖ ≤ vCoefDens V y) := by
  have h0 : 0 ≤ ‖V y‖ ^ 2 := sq_nonneg _
  have hS1 : 0 ≤ ∑ j : Fin 3, ‖physPd V j y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 V j l y‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨by unfold vCoefDens; linarith, fun j => ?_, fun j l => ?_⟩
  · have h : ‖physPd V j y‖ ≤ ∑ j' : Fin 3, ‖physPd V j' y‖ :=
      Finset.single_le_sum (f := fun j' => ‖physPd V j' y‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)
    unfold vCoefDens; linarith
  · have h : ‖physPd2 V j l y‖ ≤ ∑ j' : Fin 3, ∑ l' : Fin 3, ‖physPd2 V j' l' y‖ :=
      chgPt_single_le (f := fun j' l' => ‖physPd2 V j' l' y‖) (fun _ _ => norm_nonneg _) j l
    unfold vCoefDens; linarith

/-- Pointwise bound on `vrJetV`: `‖-2νC_diff(V, X) + (V⊗V):D²X‖ ≤ (36|ν| + 9) vCoefDens V · J_X`. -/
theorem vr_jetV_pt (ν : ℝ) (V X : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    ‖vrJetV ν V X τ y‖ ≤ (36 * |ν| + 9) * vCoefDens (V τ) y * vrXJetSum (X τ) y := by
  set c := vCoefDens (V τ) y
  set J := vrXJetSum (X τ) y
  have hc0 : 0 ≤ c := vrCoefDens_nonneg (V τ) y
  have hJ0 : 0 ≤ J := vrXJetSum_nonneg (X τ) y
  obtain ⟨hV0, hV1, hV2⟩ := vr_vcoef_bounds (V τ) y
  obtain ⟨hX1, hX2⟩ := vr_xjet_bounds (X τ) y
  have hcdiff : ‖physCdiff (V τ) (X τ) y‖ ≤ 18 * c * J := by
    have hterm : ∀ j l : Fin 3,
        ‖(physPd (V τ) j y) l • physPd2 (X τ) j l y -
          (physPd (X τ) j y) l • physPd2 (V τ) j l y‖ ≤ 2 * c * J := by
      intro j l
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have a1 : |(physPd (V τ) j y) l| ≤ c := (chgPt_abs_coord_le _ l).trans (hV1 j)
      have a2 : |(physPd (X τ) j y) l| ≤ J := (chgPt_abs_coord_le _ l).trans (hX1 j)
      calc |(physPd (V τ) j y) l| * ‖physPd2 (X τ) j l y‖ +
            |(physPd (X τ) j y) l| * ‖physPd2 (V τ) j l y‖
          ≤ c * J + J * c :=
            add_le_add (mul_le_mul a1 (hX2 j l) (norm_nonneg _) hc0)
              (mul_le_mul a2 (hV2 j l) (norm_nonneg _) hJ0)
        _ = 2 * c * J := by ring
    unfold physCdiff
    calc ‖∑ j : Fin 3, ∑ l : Fin 3, _‖
        ≤ ∑ j : Fin 3, ‖∑ l : Fin 3, _‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖_‖ := Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, 2 * c * J :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
      _ = 18 * c * J := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have huud2 : ‖physUUD2 (V τ) (X τ) y‖ ≤ 9 * c * J := by
    have hterm : ∀ j l : Fin 3,
        ‖(V τ y j * V τ y l) • physPd2 (X τ) j l y‖ ≤ c * J := by
      intro j l
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      have b1 : |V τ y j| * |V τ y l| ≤ c := by
        calc |V τ y j| * |V τ y l|
            ≤ ‖V τ y‖ * ‖V τ y‖ :=
              mul_le_mul (chgPt_abs_coord_le _ j) (chgPt_abs_coord_le _ l) (abs_nonneg _)
                (norm_nonneg _)
          _ = ‖V τ y‖ ^ 2 := (sq _).symm
          _ ≤ c := hV0
      exact mul_le_mul b1 (hX2 j l) (norm_nonneg _) hc0
    unfold physUUD2
    calc ‖∑ j : Fin 3, ∑ l : Fin 3, _‖
        ≤ ∑ j : Fin 3, ‖∑ l : Fin 3, _‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖_‖ := Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, c * J :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
      _ = 9 * c * J := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  unfold vrJetV
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
  have h1 : 2 * |ν| * ‖physCdiff (V τ) (X τ) y‖ ≤ 36 * |ν| * c * J := by
    calc 2 * |ν| * ‖physCdiff (V τ) (X τ) y‖
        ≤ 2 * |ν| * (18 * c * J) := mul_le_mul_of_nonneg_left hcdiff (by positivity)
      _ = 36 * |ν| * c * J := by ring
  linarith

/-- Pointwise bound on `vrJetP`: `‖-(DX + DXᵀ)∇p_V‖ ≤ 18 J_X ‖∇p_V‖`. -/
theorem vr_jetP_pt (X : ℝ → Space → Space) (pV : ℝ → Space → ℝ) (τ : ℝ) (y : Space) :
    ‖vrJetP X pV τ y‖ ≤ 18 * ‖physGrad (pV τ) y‖ * vrXJetSum (X τ) y := by
  set J := vrXJetSum (X τ) y
  have hJ0 : 0 ≤ J := vrXJetSum_nonneg (X τ) y
  obtain ⟨hX1, _⟩ := vr_xjet_bounds (X τ) y
  have h0g : physGrad (fun _ : Space => (0 : ℝ)) y = 0 := by
    ext j
    simp [physGrad]
  have h0dxp : physDXp (X τ) (fun _ : Space => (0 : ℝ)) y = 0 := by
    ext i
    simp [physDXp]
  have h := chgPt_dxp (X τ) (pV τ) (fun _ => 0) y J ‖physGrad (pV τ) y‖ hJ0 hX1 (norm_nonneg _)
    (by rw [h0g, sub_zero])
  rw [h0dxp, sub_zero] at h
  unfold vrJetP
  rw [norm_neg]
  linarith

/-- `L²(srcMeasure)` bound for `vrJetV` and `vrJetP` at a regime when `F_r < ⊤`. -/
theorem vr_jet_bounds_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {pV : ℝ → Space → ℝ} (hν1 : L.ν ≤ 1) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    {k₁ k₂ : ℕ} {w : LVel Pl L}
    (hXjet : ∀ (τ : ℝ) (y : Space),
      ENNReal.ofReal (vrXJetSum (repX Pl K L μ w τ) y) ≤
        ENNReal.ofReal (C₁ * L.ν⁻¹ ^ k₁ * L.ε ^ (101 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w))
    (hV2 : ENNReal.ofReal L.ε * eLpNorm (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ)) 2
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C₂ * L.ν⁻¹ ^ k₂))
    (hpV2 : ENNReal.ofReal L.ε * eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖physGrad (pV τ) y‖) 2
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C₂ * L.ν⁻¹ ^ k₂))
    (hFr : phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) ≠ ⊤) :
    eLpNorm (coefOf L.ε⁻¹ (vrJetV L.ν L.V (repX Pl K L μ w))) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (45 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) ∧
      eLpNorm (coefOf L.ε⁻¹ (vrJetP (repX Pl K L μ w) pV)) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (18 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  set X := repX Pl K L μ w
  set Fr := phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w)
  set A₁ : ℝ := C₁ * L.ν⁻¹ ^ k₁ * L.ε ^ (101 / 22 : ℝ)
  have hA₁0 : 0 ≤ A₁ := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal A₁ * Fr
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFr
  set b : ℝ := B.toReal
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hBb : ENNReal.ofReal b = B := ENNReal.ofReal_toReal hBt
  have hJpt : ∀ τ y, vrXJetSum (X τ) y ≤ b := fun τ y =>
    (ENNReal.ofReal_le_iff_le_toReal hBt).1 (hXjet τ y)
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν)
  constructor
  · set gV : ℝ → Space → ℝ := fun τ y => (45 * b) * vCoefDens (L.V τ) y
    have hptV : ∀ p : Chart, 0 < p.1 →
        ‖vrJetV L.ν L.V X (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
          ringRead L.ε⁻¹ gV p := by
      intro p _
      set τ := NearInst.chartTau L.ε⁻¹ p
      set y := NearInst.chartY L.ε⁻¹ p
      have h1 := vr_jetV_pt L.ν L.V X τ y
      have h36 : 36 * |L.ν| + 9 ≤ 45 := by rw [abs_of_pos hν]; linarith
      have hc0 := vrCoefDens_nonneg (L.V τ) y
      calc ‖vrJetV L.ν L.V X τ y‖
          ≤ (36 * |L.ν| + 9) * vCoefDens (L.V τ) y * vrXJetSum (X τ) y := h1
        _ ≤ 45 * vCoefDens (L.V τ) y * b :=
            mul_le_mul (mul_le_mul_of_nonneg_right h36 hc0) (hJpt τ y)
              (vrXJetSum_nonneg _ _) (by positivity)
        _ = ringRead L.ε⁻¹ gV p := by unfold gV ringRead; ring
    have hL2 := ringL2Conv L.ε⁻¹ (cOf L.ν) hR hc (vrJetV L.ν L.V X) gV hptV
    have hrgV : ringRead L.ε⁻¹ gV = (45 * b) • ringRead L.ε⁻¹ (fun τ => vCoefDens (L.V τ)) := by
      funext p; rfl
    rw [inv_inv, hrgV, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity : 0 ≤ 45 * b)] at hL2
    calc eLpNorm (coefOf L.ε⁻¹ (vrJetV L.ν L.V X)) 2 (srcMeasure (cOf L.ν))
        ≤ ENNReal.ofReal L.ε *
            (ENNReal.ofReal (45 * b) *
              eLpNorm (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ)) 2 μp) := hL2
      _ = ENNReal.ofReal (45 * b) *
            (ENNReal.ofReal L.ε *
              eLpNorm (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ)) 2 μp) := by ring
      _ ≤ ENNReal.ofReal (45 * b) * ENNReal.ofReal (C₂ * L.ν⁻¹ ^ k₂) :=
          mul_le_mul' le_rfl hV2
      _ = ENNReal.ofReal (45 * (C₂ * L.ν⁻¹ ^ k₂)) * B := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 45),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 45), hBb]
          ring
      _ = ENNReal.ofReal (45 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) * Fr := by
          unfold B A₁
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [pow_add]
          ring
  · set gP : ℝ → Space → ℝ := fun τ y => (18 * b) * ‖physGrad (pV τ) y‖
    have hptP : ∀ p : Chart, 0 < p.1 →
        ‖vrJetP X pV (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
          ringRead L.ε⁻¹ gP p := by
      intro p _
      set τ := NearInst.chartTau L.ε⁻¹ p
      set y := NearInst.chartY L.ε⁻¹ p
      have h1 := vr_jetP_pt X pV τ y
      calc ‖vrJetP X pV τ y‖
          ≤ 18 * ‖physGrad (pV τ) y‖ * vrXJetSum (X τ) y := h1
        _ ≤ 18 * ‖physGrad (pV τ) y‖ * b :=
            mul_le_mul_of_nonneg_left (hJpt τ y) (by positivity)
        _ = ringRead L.ε⁻¹ gP p := by unfold gP ringRead; ring
    have hL2 := ringL2Conv L.ε⁻¹ (cOf L.ν) hR hc (vrJetP X pV) gP hptP
    have hrgP : ringRead L.ε⁻¹ gP =
        (18 * b) • ringRead L.ε⁻¹ (fun τ y => ‖physGrad (pV τ) y‖) := by
      funext p; rfl
    rw [inv_inv, hrgP, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity : 0 ≤ 18 * b)] at hL2
    calc eLpNorm (coefOf L.ε⁻¹ (vrJetP X pV)) 2 (srcMeasure (cOf L.ν))
        ≤ ENNReal.ofReal L.ε *
            (ENNReal.ofReal (18 * b) *
              eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖physGrad (pV τ) y‖) 2 μp) := hL2
      _ = ENNReal.ofReal (18 * b) *
            (ENNReal.ofReal L.ε *
              eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖physGrad (pV τ) y‖) 2 μp) := by ring
      _ ≤ ENNReal.ofReal (18 * b) * ENNReal.ofReal (C₂ * L.ν⁻¹ ^ k₂) :=
          mul_le_mul' le_rfl hpV2
      _ = ENNReal.ofReal (18 * (C₂ * L.ν⁻¹ ^ k₂)) * B := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18), hBb]
          ring
      _ = ENNReal.ofReal (18 * C₁ * C₂ * L.ν⁻¹ ^ (k₁ + k₂) * L.ε ^ (101 / 22 : ℝ)) * Fr := by
          unfold B A₁
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [pow_add]
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
