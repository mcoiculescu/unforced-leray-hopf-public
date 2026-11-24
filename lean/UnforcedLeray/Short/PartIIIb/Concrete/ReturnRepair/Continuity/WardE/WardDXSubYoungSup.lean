import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.SepWSubDom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_4

/-!
# `PartIII-b:C/cont/WE/4`: `WardDXSubYoungSup`, `μ`-Lipschitz `L^∞` bound of `DX` on the young support

Source of record: `the November 2 reference manuscript`
(73 pages), lines 3603-3629 (`sep:kernel`), 4178-4186, 5238-5244, 5701-5704.

Follows `wardDXYoungSup_proved` (`Sub/PartIII-b_C_ward_11_4.lean` and
`Sub/PartIII-b_C_ward_11_4/H1..H2.lean`): uses `wardX_eq_cut_add_corr`, `w114_scalar`, and
`sepWSubDom_proved` at orders `j = 0, 1` with the `L^∞` Cauchy-Schwarz kernel estimate
(`w114_w2Dom_sup`) across the gap `R√ν(1 - √(5/6))` at the fixed weight `a₀ = 2(-1/8) + 2 = 7/4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Order-zero comparison for `sepWre ν m T τ y - sepWre ν m' T τ y`. -/
private theorem sepWre_sub_norm0 {ν : ℝ} (m m' : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ ≤
      ‖w10Re‖ * ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
        iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ := by
  have heq : sepWre ν m T τ y - sepWre ν m' T τ y =
      w10Re ((iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
        iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y) 0) := by
    simp only [sub_apply, iteratedFDeriv_zero_apply, map_sub,
      w10_sepWre_eq, Function.comp_apply]
  rw [heq]
  refine (w10Re.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simpa using (iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
    iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y).le_opNorm 0

/-- Order-one comparison for `physPd (sepWre ν m T τ) j y - physPd (sepWre ν m' T τ) j y`. -/
private theorem sepWre_sub_norm1 {ν : ℝ} (m m' : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) (j : Fin 3)
    (hA : DifferentiableAt ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y)
    (hA' : DifferentiableAt ℝ (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y) :
    ‖physPd (sepWre ν m T τ) j y - physPd (sepWre ν m' T τ) j y‖ ≤
      ‖w10Re‖ * ‖iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
        iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ := by
  have h1 := (w10Re.hasFDerivAt.comp y hA.hasFDerivAt).fderiv
  have h1' := (w10Re.hasFDerivAt.comp y hA'.hasFDerivAt).fderiv
  have heq : physPd (sepWre ν m T τ) j y - physPd (sepWre ν m' T τ) j y =
      w10Re ((iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
        iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y)
        (fun _ : Fin 1 => coordinateVector j)) := by
    unfold physPd
    rw [w10_sepWre_eq m, w10_sepWre_eq m', h1, h1']
    simp only [ContinuousLinearMap.comp_apply, ← map_sub, sub_apply,
      iteratedFDeriv_one_apply]
  rw [heq]
  refine (w10Re.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have hop := (iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
    iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y).le_opNorm
    (fun _ : Fin 1 => coordinateVector j)
  simpa [wyl_norm_coordinateVector] using hop

/-- Single-pair `(m, m')` pointwise sup bound on `sepWre` and `physPd (sepWre ...)` on `R√ν ≤ ϱ y`
for `m, m' ≥ 0`. -/
private theorem w114_sub_single_sup (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
          ‖sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y -
              sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y‖ ≤
            C * |m - m'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal ∧
          ∀ j : Fin 3,
            ‖physPd (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) j y -
                physPd (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) j y‖ ≤
              C * |m - m'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  have hr0 : 0 ≤ r0 := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0
  have hD : 0 < D := sub_pos.2 hrr
  set P : ℝ := 2 * c / R
  have hP : 0 < P := by positivity
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  have ha0 : 1 / 2 < a0 := by simp only [a0]; norm_num
  obtain ⟨K0, hK0, hSup0⟩ := w114_w2Dom_sup (IIIa.sepKd_measurable 0 D)
    (w114_sepKd_sq_ne_top 0 hD) ha0 hP
  obtain ⟨K1, hK1, hSup1⟩ := w114_w2Dom_sup (IIIa.sepKd_measurable 1 D)
    (w114_sepKd_sq_ne_top 1 hD) ha0 hP
  obtain ⟨Cd0, hCd0, hdom0⟩ := sepWSubDom_proved 0
  obtain ⟨Cd1, hCd1, hdom1⟩ := sepWSubDom_proved 1
  set S : ℝ := Real.sqrt (Real.pi * R ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set C0 : ℝ := ‖w10Re‖ * Cd0 * K0 * S
  set C1 : ℝ := ‖w10Re‖ * Cd1 * K1 * S
  have hC0 : 0 ≤ C0 := by positivity
  have hC1 : 0 ≤ C1 := by positivity
  set C : ℝ := max C0 C1
  refine ⟨C, le_trans hC0 (le_max_left _ _), fun m m' hm hm' g hg τ y hy => ?_⟩
  obtain ⟨hSep, hM, -⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c r0 g
  set G := IIIa.srcNorm T
  have hGm : Measurable (Function.uncurry G) := w2_srcNorm_measurable hSep
  have hGper : ∀ s z, G (s + P) z = G s z := fun s z => by
    unfold G IIIa.srcNorm; rw [hSep.periodic]
  have hsrc := w114_src_ltauLq_le r0 hR hc hg.measurable
  have hltau_top : IIIa.ltauLq P 2 G ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.memLp.eLpNorm_lt_top.ne) hsrc
  have hW0_le : IIIa.sepDom a0 0 D G τ y ≤ ENNReal.ofReal K0 * IIIa.ltauLq P 2 G := by
    rw [w2_sepDom_eq]
    exact hSup0 G hGm hGper τ y
  have hW0_lt : IIIa.sepDom a0 0 D G τ y < ⊤ :=
    lt_of_le_of_lt hW0_le (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hltau_top.lt_top)
  have hW1_le : IIIa.sepDom a0 1 D G τ y ≤ ENNReal.ofReal K1 * IIIa.ltauLq P 2 G := by
    rw [w2_sepDom_eq]
    exact hSup1 G hGm hGper τ y
  have hd0 := hdom0 ν m m' r0 (R * Real.sqrt ν) P hν hm hm' hr0 hrr hP T hSep τ y hy hW0_lt
  have hd1 := hdom1 ν m m' r0 (R * Real.sqrt ν) P hν hm hm' hr0 hrr hP T hSep τ y hy hW0_lt
  set N : ℝ := (eLpNorm g 2 (ageμ c (-1 / 2))).toReal
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  refine ⟨?_, fun j => ?_⟩
  · have hb0 : ENNReal.ofReal ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ ≤
        ENNReal.ofReal (C0 * |m - m'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
      have he : ENNReal.ofReal ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ ≤
          ENNReal.ofReal ‖w10Re‖ *
            ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
              iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (sepWre_sub_norm0 m m' T τ y)
      calc ENNReal.ofReal ‖sepWre ν m T τ y - sepWre ν m' T τ y‖
          ≤ ENNReal.ofReal ‖w10Re‖ *
              ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
                iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := he
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
              (ENNReal.ofReal (Cd0 * |m - m'|) * IIIa.sepDom a0 0 D G τ y) :=
            mul_le_mul' le_rfl hd0
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
              (ENNReal.ofReal (Cd0 * |m - m'|) * (ENNReal.ofReal K0 * IIIa.ltauLq P 2 G)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hW0_le)
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
              (ENNReal.ofReal (Cd0 * |m - m'|) * (ENNReal.ofReal K0 *
                (ENNReal.ofReal S * eLpNorm g 2 (ageμ c (-1 / 2))))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsrc))
        _ = ENNReal.ofReal (C0 * |m - m'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
            simp only [C0]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity)]
            ring
    exact (w114_ofReal_le_toReal (mul_nonneg hC0 (abs_nonneg _)) hg hb0).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C0 C1) (abs_nonneg _)) hN0)
  · have hy' : r0 < ϱ y := lt_of_lt_of_le hrr hy
    have hA := w10_diffA (m := m) hν (by linarith) hr0 hP hSep hM τ hy'
    have hA' := w10_diffA (m := m') hν (by linarith) hr0 hP hSep hM τ hy'
    have hb1 : ENNReal.ofReal ‖physPd (sepWre ν m T τ) j y - physPd (sepWre ν m' T τ) j y‖ ≤
        ENNReal.ofReal (C1 * |m - m'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
      have he : ENNReal.ofReal ‖physPd (sepWre ν m T τ) j y - physPd (sepWre ν m' T τ) j y‖ ≤
          ENNReal.ofReal ‖w10Re‖ *
            ‖iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
              iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (sepWre_sub_norm1 m m' T τ y j hA hA')
      calc ENNReal.ofReal ‖physPd (sepWre ν m T τ) j y - physPd (sepWre ν m' T τ) j y‖
          ≤ ENNReal.ofReal ‖w10Re‖ *
              ‖iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
                iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := he
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
              (ENNReal.ofReal (Cd1 * |m - m'|) * IIIa.sepDom a0 1 D G τ y) :=
            mul_le_mul' le_rfl hd1
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
              (ENNReal.ofReal (Cd1 * |m - m'|) * (ENNReal.ofReal K1 * IIIa.ltauLq P 2 G)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hW1_le)
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
              (ENNReal.ofReal (Cd1 * |m - m'|) * (ENNReal.ofReal K1 *
                (ENNReal.ofReal S * eLpNorm g 2 (ageμ c (-1 / 2))))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsrc))
        _ = ENNReal.ofReal (C1 * |m - m'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
            simp only [C1]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity)]
            ring
    exact (w114_ofReal_le_toReal (mul_nonneg hC1 (abs_nonneg _)) hg hb1).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C0 C1) (abs_nonneg _)) hN0)

/-- `μ`-Lipschitz sup bound on `wardX0` and `physPd (wardX0)` on `R√ν ≤ ϱ y` for `μ, μ' ≥ 0`. -/
private theorem w114_wardX0SubDSup (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
          ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ ≤
            C * |μ - μ'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal ∧
          ∀ j : Fin 3,
            ‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ ≤
              C * |μ - μ'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  obtain ⟨Cs, hCs, hS⟩ := w114_sub_single_sup ν R c hν hR hc
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  refine ⟨2 * Cs, by positivity, fun μ μ' hμ hμ' g hg τ y hy => ?_⟩
  obtain ⟨hSep, hM, -⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  have hr0 : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set T := oldCutSrc R c r0 g
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  have hX0' := w10_X0_eq (μ := μ') hν hR hc hg
  obtain ⟨ha0, ha1⟩ := hS μ μ' hμ hμ' g hg τ y hy
  obtain ⟨hb0, hb1⟩ := hS (μ + 1) (μ' + 1) (by linarith) (by linarith) g hg τ y hy
  rw [show (μ + 1) - (μ' + 1) = μ - μ' by ring] at hb0 hb1
  refine ⟨?_, fun j => ?_⟩
  · have heq : wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y =
        (sepWre ν μ T τ y - sepWre ν μ' T τ y) -
          (sepWre ν (μ + 1) T τ y - sepWre ν (μ' + 1) T τ y) := by
      rw [hX0, hX0', sepX0_eq_sub, sepX0_eq_sub]
      abel
    rw [heq]
    calc ‖(sepWre ν μ T τ y - sepWre ν μ' T τ y) -
            (sepWre ν (μ + 1) T τ y - sepWre ν (μ' + 1) T τ y)‖
        ≤ ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ +
            ‖sepWre ν (μ + 1) T τ y - sepWre ν (μ' + 1) T τ y‖ := norm_sub_le _ _
      _ ≤ 2 * Cs * |μ - μ'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by linarith
  · have hpd : ∀ m : ℝ, -(1 / 4) < m →
        physPd (wardX0 ν m R c g τ) j y =
          physPd (sepWre ν m T τ) j y - physPd (sepWre ν (m + 1) T τ) j y := by
      intro m hm
      have hda : DifferentiableAt ℝ (sepWre ν m T τ) y := w10_diffV hν hm hr0 hP hSep hM τ hyU
      have hdb : DifferentiableAt ℝ (sepWre ν (m + 1) T τ) y :=
        w10_diffV hν (by linarith) hr0 hP hSep hM τ hyU
      have hfun : wardX0 ν m R c g τ = fun x => sepWre ν m T τ x - sepWre ν (m + 1) T τ x := by
        rw [w10_X0_eq (μ := m) hν hR hc hg]
        funext x
        exact sepX0_eq_sub _ _ _ _ _
      unfold physPd
      rw [hfun, fderiv_fun_sub hda hdb, sub_apply]
    have heq : physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y =
        (physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y) -
          (physPd (sepWre ν (μ + 1) T τ) j y - physPd (sepWre ν (μ' + 1) T τ) j y) := by
      rw [hpd μ (by linarith), hpd μ' (by linarith)]
      abel
    rw [heq]
    calc ‖(physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y) -
            (physPd (sepWre ν (μ + 1) T τ) j y - physPd (sepWre ν (μ' + 1) T τ) j y)‖
        ≤ ‖physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y‖ +
            ‖physPd (sepWre ν (μ + 1) T τ) j y - physPd (sepWre ν (μ' + 1) T τ) j y‖ :=
          norm_sub_le _ _
      _ ≤ 2 * Cs * |μ - μ'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
          linarith [ha1 j, hb1 j]

/-- Unconditional order-0 `μ`-Lipschitz domination of `sepW`. -/
private theorem w114_sub_wdom :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν μ μ' rOut rIn P : ℝ),
      0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T →
      ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
        ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
            iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y‖ₑ ≤
          ENNReal.ofReal (C0 * |μ - μ'|) *
            IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y := by
  obtain ⟨C0, hC0, hSub0⟩ := sepWSubDom_proved 0
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy
  by_cases hmu : μ = μ'
  · subst hmu; simp
  by_cases hfin : IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤
  · refine (hSub0 ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy hfin).trans ?_
    gcongr
    linarith
  · have hpos : 0 < (C0 + 1) * |μ - μ'| := mul_pos (by linarith) (abs_pos.2 (sub_ne_zero.2 hmu))
    rw [not_lt_top_iff.1 hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top

/-- `μ`-Lipschitz domination of `outPrim (wardX0 ν μ R c g) - outPrim (wardX0 ν μ' R c g)` by the
cylinder majorant `w2Dom (w2k ...)` at `a₀ = 2(-1/8) + 2`. -/
private theorem w2_psi_sub_dom {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (r2 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space),
        R * Real.sqrt ν ≤ ϱ y → ϱ y ≤ r2 →
          ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
              outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| ≤
            ENNReal.ofReal (C * |μ - μ'|) * w2Dom (w2k (R * Real.sqrt (5 * ν / 6))
              (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (r2 + R * Real.sqrt (5 * ν / 6)))
              (2 * (-1 / 8 : ℝ) + 2)
              (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y := by
  obtain ⟨C0, hC0, hdom⟩ := w114_sub_wdom
  refine ⟨2 * ‖w10Re‖ * C0, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg τ y hy1 hy2
  obtain ⟨hS, -, -⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  set T := oldCutSrc R c r0 g with hT
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0 with hD
  have hDpos : 0 < D := sub_pos.2 hrr
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  have hX0' := w10_X0_eq (μ := μ') hν hR hc hg
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  set G := IIIa.srcNorm T
  have hpt : ∀ p : Space, R * Real.sqrt ν ≤ ϱ p →
      ENNReal.ofReal |(wardX0 ν μ R c g τ p - wardX0 ν μ' R c g τ p) 2| ≤
        ENNReal.ofReal (2 * ‖w10Re‖ * C0 * |μ - μ'|) * w2Dom (IIIa.sepKd 0 D) a0 G τ p := by
    intro p hp
    have e1 : |(wardX0 ν μ R c g τ p - wardX0 ν μ' R c g τ p) 2| ≤
        ‖sepWre ν μ T τ p - sepWre ν μ' T τ p‖ +
          ‖sepWre ν (μ + 1) T τ p - sepWre ν (μ' + 1) T τ p‖ := by
      have heq : wardX0 ν μ R c g τ p - wardX0 ν μ' R c g τ p =
          (sepWre ν μ T τ p - sepWre ν μ' T τ p) -
            (sepWre ν (μ + 1) T τ p - sepWre ν (μ' + 1) T τ p) := by
        rw [hX0, hX0', sepX0_eq_sub, sepX0_eq_sub]
        abel
      calc |(wardX0 ν μ R c g τ p - wardX0 ν μ' R c g τ p) 2|
          ≤ ‖wardX0 ν μ R c g τ p - wardX0 ν μ' R c g τ p‖ := wyl_abs_apply_le _ 2
        _ ≤ _ := by rw [heq]; exact norm_sub_le _ _
    have d1 := hdom ν μ μ' r0 (R * Real.sqrt ν) (2 * c / R) hν hμ hμ' hr0nn hrr hP T hS τ p hp
    have d2 := hdom ν (μ + 1) (μ' + 1) r0 (R * Real.sqrt ν) (2 * c / R) hν (by linarith)
      (by linarith) hr0nn hrr hP T hS τ p hp
    rw [show (μ + 1) - (μ' + 1) = μ - μ' by ring, w2_sepDom_eq] at d2
    rw [w2_sepDom_eq] at d1
    have m1 : ‖sepWre ν μ T τ p - sepWre ν μ' T τ p‖ₑ ≤
        ENNReal.ofReal ‖w10Re‖ *
          ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) p -
            iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) p‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (sepWre_sub_norm0 μ μ' T τ p)
    have m2 : ‖sepWre ν (μ + 1) T τ p - sepWre ν (μ' + 1) T τ p‖ₑ ≤
        ENNReal.ofReal ‖w10Re‖ *
          ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν ((μ + 1 : ℝ) : ℂ) T y' τ) p -
            iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν ((μ' + 1 : ℝ) : ℂ) T y' τ) p‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (sepWre_sub_norm0 (μ + 1) (μ' + 1) T τ p)
    calc ENNReal.ofReal |(wardX0 ν μ R c g τ p - wardX0 ν μ' R c g τ p) 2|
        ≤ ENNReal.ofReal (‖sepWre ν μ T τ p - sepWre ν μ' T τ p‖ +
            ‖sepWre ν (μ + 1) T τ p - sepWre ν (μ' + 1) T τ p‖) :=
          ENNReal.ofReal_le_ofReal e1
      _ = ‖sepWre ν μ T τ p - sepWre ν μ' T τ p‖ₑ +
            ‖sepWre ν (μ + 1) T τ p - sepWre ν (μ' + 1) T τ p‖ₑ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]
      _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal (C0 * |μ - μ'|) * w2Dom (IIIa.sepKd 0 D) a0 G τ p) +
          ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal (C0 * |μ - μ'|) * w2Dom (IIIa.sepKd 0 D) a0 G τ p) := by
          gcongr
          · exact m1.trans (mul_le_mul' le_rfl d1)
          · exact m2.trans (mul_le_mul' le_rfl d2)
      _ = ENNReal.ofReal (2 * ‖w10Re‖ * C0 * |μ - μ'|) * w2Dom (IIIa.sepKd 0 D) a0 G τ p := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_ofNat]
          ring
  have hInt1 := xa_outPrim_integrable hc hν hR (by linarith : -(1 / 4) < μ) hg τ (y 2) (ϱ y)
    (lt_of_lt_of_le hrr hy1)
  have hInt2 := xa_outPrim_integrable hc hν hR (by linarith : -(1 / 4) < μ') hg τ (y 2) (ϱ y)
    (lt_of_lt_of_le hrr hy1)
  have hop : outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
      outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2) =
      -∫ ρ in Ioi (ϱ y),
        ρ * (wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) -
          wardX0 ν μ' R c g τ (!₂[ρ, 0, y 2] : Space)) 2 := by
    unfold outPrim
    have e : (fun ρ : ℝ =>
        ρ * (wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) -
          wardX0 ν μ' R c g τ (!₂[ρ, 0, y 2] : Space)) 2) =
        fun ρ => ρ * wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) 2 -
          ρ * wardX0 ν μ' R c g τ (!₂[ρ, 0, y 2] : Space) 2 := by
      funext ρ
      simp only [PiLp.sub_apply]
      ring
    rw [e, integral_sub hInt1 hInt2]
    ring
  have hnorm : ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
        outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| ≤
      ∫⁻ ρ in Ioi (ϱ y),
        ‖ρ * (wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) -
          wardX0 ν μ' R c g τ (!₂[ρ, 0, y 2] : Space)) 2‖ₑ := by
    rw [hop, ← Real.enorm_eq_ofReal_abs, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _
  refine hnorm.trans ?_
  calc ∫⁻ ρ in Ioi (ϱ y),
        ‖ρ * (wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) -
          wardX0 ν μ' R c g τ (!₂[ρ, 0, y 2] : Space)) 2‖ₑ
      ≤ ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal (2 * ‖w10Re‖ * C0 * |μ - μ'|) *
          (ENNReal.ofReal ρ * w2Dom (IIIa.sepKd 0 D) a0 G τ (!₂[ρ, 0, y 2] : Space)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ' : ϱ y < ρ := hρ
        have hρ0 : 0 ≤ ρ := (ϱ_nonneg y).trans hρ'.le
        have hϱ : ϱ (!₂[ρ, 0, y 2] : Space) = ρ := wardFar_varrho ρ (y 2) hρ0
        have := hpt (!₂[ρ, 0, y 2] : Space) (by rw [hϱ]; linarith)
        rw [enorm_mul, Real.enorm_of_nonneg hρ0, ← ofReal_norm, Real.norm_eq_abs]
        calc ENNReal.ofReal ρ *
              ENNReal.ofReal |(wardX0 ν μ R c g τ (!₂[ρ, 0, y 2] : Space) -
                wardX0 ν μ' R c g τ (!₂[ρ, 0, y 2] : Space)) 2|
            ≤ ENNReal.ofReal ρ * (ENNReal.ofReal (2 * ‖w10Re‖ * C0 * |μ - μ'|) *
                w2Dom (IIIa.sepKd 0 D) a0 G τ (!₂[ρ, 0, y 2] : Space)) := by gcongr
          _ = _ := by ring
    _ = ENNReal.ofReal (2 * ‖w10Re‖ * C0 * |μ - μ'|) *
          ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal ρ *
            w2Dom (IIIa.sepKd 0 D) a0 G τ (!₂[ρ, 0, y 2] : Space) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact w2_tonelli hr0nn hDpos a0 (w2_srcNorm_measurable hS)
          (fun τ' z hz => w2_srcNorm_zero hS τ' hz) τ hy2 (by rw [hD]; linarith)

/-- Pointwise difference bound for `physPd (wardStreamCorr ν R χy (wardX0 ν m R c g) τ) j y`. -/
private theorem w2_corr_sub_pd_bound {ν μ μ' R c : ℝ} {g : Chart → Ten3} {χy : ℝ → ℝ}
    (hχ : IsYoungCutoff χy) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3) {y : Space} (hy : y ∈ youngOpen ν R) :
    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
        physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ ≤
      |deriv (w2a ν R χy) (ϱ y)| *
          |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| +
        |w2a ν R χy (ϱ y)| *
          (2 * ϱ y * ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖) := by
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hy'
  have hwd : HasDerivAt (w2a ν R χy) (deriv (w2a ν R χy) (ϱ y)) (ϱ y) :=
    (((w2a_contDiffOn (ν := ν) (R := R) hχ).contDiffAt (Ioi_mem_nhds hρ)).differentiableAt
      one_ne_zero).hasDerivAt
  have hpd_eq : ∀ m : ℝ, -(1 / 4) < m →
      physPd (wardStreamCorr ν R χy (wardX0 ν m R c g) τ) j y =
        (w2a ν R χy (ϱ y) *
            (ϱ y * wardX0 ν m R c g τ (meridPt y) 2 * ϱD y (coordinateVector j) +
              -(ϱ y * wardX0 ν m R c g τ (meridPt y) 0) * coordinateVector j 2) +
          outPrim (wardX0 ν m R c g) τ (ϱ y) (y 2) *
            (deriv (w2a ν R χy) (ϱ y) * ϱD y (coordinateVector j))) •
          coordinateVector 2 := by
    intro m hm
    have hΨ := w2_psi_hasFDeriv hν hR hc hm hg τ hy
    have hA := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ
    have hC := hA.smul_const (coordinateVector 2)
    have hfun : wardStreamCorr ν R χy (wardX0 ν m R c g) τ =
        fun x : Space => ((w2a ν R χy ∘ ϱ) x * outPrim (wardX0 ν m R c g) τ (ϱ x) (x 2)) •
          coordinateVector 2 := by
      funext x; rfl
    unfold physPd
    rw [hfun]
    exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hC.fderiv
  rw [hpd_eq μ hμ, hpd_eq μ' hμ', ← sub_smul, norm_smul, wyl_norm_coordinateVector, mul_one,
    Real.norm_eq_abs]
  set Ψ := outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) - outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)
  set w := w2a ν R χy (ϱ y)
  set w' := deriv (w2a ν R χy) (ϱ y)
  set d := ϱD y (coordinateVector j)
  set e := coordinateVector j 2
  set Z := wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)
  set Z2 := Z 2
  set Z0 := Z 0
  set N := ‖Z‖
  have hm2 : |Z2| ≤ N := wyl_abs_apply_le Z 2
  have hm0 : |Z0| ≤ N := wyl_abs_apply_le Z 0
  have hD := w2_abs_ϱD y hy' j
  have hE := w2_abs_cv2 j
  have halg : (w * (ϱ y * wardX0 ν μ R c g τ (meridPt y) 2 * d +
        -(ϱ y * wardX0 ν μ R c g τ (meridPt y) 0) * e) +
      outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) * (w' * d)) -
      (w * (ϱ y * wardX0 ν μ' R c g τ (meridPt y) 2 * d +
        -(ϱ y * wardX0 ν μ' R c g τ (meridPt y) 0) * e) +
      outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2) * (w' * d)) =
      w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + Ψ * (w' * d) := by
    simp only [Z2, Z0, Z, Ψ, PiLp.sub_apply]
    ring
  rw [halg]
  have hPb : |ϱ y * Z2 * d| ≤ ϱ y * N := by
    rw [abs_mul, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z2| * |d| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm2 hρ.le) hD (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hQb : |-(ϱ y * Z0) * e| ≤ ϱ y * N := by
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z0| * |e| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm0 hρ.le) hE (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hsum : |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ 2 * ϱ y * N := by
    calc _ ≤ |ϱ y * Z2 * d| + |-(ϱ y * Z0) * e| := abs_add_le _ _
      _ ≤ 2 * ϱ y * N := by linarith
  calc |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + Ψ * (w' * d)|
      ≤ |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e)| + |Ψ * (w' * d)| := abs_add_le _ _
    _ ≤ |w'| * |Ψ| + |w| * (2 * ϱ y * N) := by
        rw [abs_mul, abs_mul, abs_mul]
        have h1 : |w| * |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ |w| * (2 * ϱ y * N) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        have h2 : |Ψ| * (|w'| * |d|) ≤ |w'| * |Ψ| := by
          calc |Ψ| * (|w'| * |d|) ≤ |Ψ| * (|w'| * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD (abs_nonneg _))
                  (abs_nonneg _)
            _ = |w'| * |Ψ| := by ring
        linarith

/-- `μ`-Lipschitz sup bound on `physPd (wardStreamCorr ...)` on `R√ν ≤ ϱ y` for `μ, μ' ≥ 0`. -/
private theorem w114_wardCorrSubDSup (ν R c : ℝ) (χy : ℝ → ℝ) (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
          ∀ j : Fin 3,
            ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
                physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ ≤
              C * |μ - μ'| * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  obtain ⟨CX0, hCX0, hX0⟩ := w114_wardX0SubDSup ν R c hν hR hc
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  have hr0 : 0 ≤ r0 := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0
  have hD : 0 < D := sub_pos.2 hrr
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2 : 0 ≤ r2 := by positivity
  set P : ℝ := 2 * c / R
  have hP : 0 < P := by positivity
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  have ha0 : 1 / 2 < a0 := by simp only [a0]; norm_num
  obtain ⟨Cpsi, hCpsi, hPsiDom⟩ := w2_psi_sub_dom hν hR hc r2
  obtain ⟨Kpsi, hKpsi, hSupPsi⟩ := w114_w2Dom_sup (w2k_measurable r0 D (r2 + r0))
    (w114_w2k_sq_ne_top hr0 hD (r2 + r0)) ha0 hP
  obtain ⟨Ca, Cb, hCa, hCb, hab⟩ := w2a_bound hχ hν hR
  set S : ℝ := Real.sqrt (Real.pi * R ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set C_P : ℝ := Cpsi * Kpsi * S
  have hC_P : 0 ≤ C_P := by positivity
  refine ⟨Cb * C_P + 2 * Ca * r2 * CX0, by positivity, fun μ μ' hμ hμ' g hg τ y hy j => ?_⟩
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hb := w2_corr_sub_pd_bound hχ hν hR hc (by linarith : -(1 / 4) < μ)
    (by linarith : -(1 / 4) < μ') hg τ j hyU
  refine hb.trans ?_
  set N : ℝ := (eLpNorm g 2 (ageμ c (-1 / 2))).toReal
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  by_cases h2 : ϱ y ≤ r2
  · obtain ⟨hw, hw'⟩ := hab (ϱ y) hy h2
    obtain ⟨hSep, -, -⟩ := w10_ctx hν hR hc hg
    set G := IIIa.srcNorm (oldCutSrc R c r0 g)
    have hGm : Measurable (Function.uncurry G) := w2_srcNorm_measurable hSep
    have hGper : ∀ s z, G (s + P) z = G s z := fun s z => by
      unfold G IIIa.srcNorm; rw [hSep.periodic]
    have hsrc := w114_src_ltauLq_le r0 hR hc hg.measurable
    have hpsi_e : ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
          outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| ≤
        ENNReal.ofReal (C_P * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
      calc ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
              outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)|
          ≤ ENNReal.ofReal (Cpsi * |μ - μ'|) * w2Dom (w2k r0 D (r2 + r0)) a0 G τ y :=
            hPsiDom μ μ' hμ hμ' g hg τ y hy h2
        _ ≤ ENNReal.ofReal (Cpsi * |μ - μ'|) * (ENNReal.ofReal Kpsi * IIIa.ltauLq P 2 G) :=
            mul_le_mul' le_rfl (hSupPsi G hGm hGper τ y)
        _ ≤ ENNReal.ofReal (Cpsi * |μ - μ'|) *
              (ENNReal.ofReal Kpsi * (ENNReal.ofReal S * eLpNorm g 2 (ageμ c (-1 / 2)))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hsrc)
        _ = ENNReal.ofReal (C_P * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
            simp only [C_P]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            ring
    have hpsi_r : |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
          outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| ≤ C_P * |μ - μ'| * N :=
      w114_ofReal_le_toReal (mul_nonneg hC_P (abs_nonneg _)) hg hpsi_e
    have hy_merid : R * Real.sqrt ν ≤ ϱ (meridPt y) := by
      rw [w10_varrho_meridPt]; exact hy
    have hX0_r : ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖ ≤
        CX0 * |μ - μ'| * N :=
      (hX0 μ μ' hμ hμ' g hg τ (meridPt y) hy_merid).1
    have e1 : |deriv (w2a ν R χy) (ϱ y)| *
          |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| ≤
        Cb * (C_P * |μ - μ'| * N) :=
      mul_le_mul hw' hpsi_r (abs_nonneg _) hCb
    have hρ0 : 0 ≤ ϱ y := ϱ_nonneg y
    have h2r : 2 * ϱ y * ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖ ≤
        2 * r2 * (CX0 * |μ - μ'| * N) := by
      calc 2 * ϱ y * ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖
          ≤ 2 * r2 * ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖ := by
            nlinarith [norm_nonneg (wardX0 ν μ R c g τ (meridPt y) -
              wardX0 ν μ' R c g τ (meridPt y))]
        _ ≤ 2 * r2 * (CX0 * |μ - μ'| * N) := mul_le_mul_of_nonneg_left hX0_r (by positivity)
    have e2 : |w2a ν R χy (ϱ y)| *
          (2 * ϱ y * ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖) ≤
        Ca * (2 * r2 * (CX0 * |μ - μ'| * N)) :=
      mul_le_mul hw h2r (by positivity) hCa
    linarith
  · have h2' := not_le.1 h2
    rw [w2a_zero_of_gt hχ hν hR h2', w2a_deriv_zero_of_gt hχ hν hR h2']
    simp only [abs_zero, zero_mul, add_zero]
    positivity

/-- **`μ`-Lipschitz `L^∞` bound of `DX_μ - DX_{μ'}` on the young support**
(`PartIII-b:C/cont/WE/4`, source lines 3603-3629, 4178-4186, 5238-5244, 5701-5704). -/
theorem wardDXSubYoungSup_proved : WardDXSubYoungSup := by
  intro a b ν R c χy ha _hb hχ hν hR hc
  obtain ⟨C1, hC1, h1⟩ := w114_wardX0SubDSup ν R c hν hR hc
  obtain ⟨C2, hC2, h2⟩ := w114_wardCorrSubDSup ν R c χy hχ hν hR hc
  obtain ⟨M, hM⟩ := w114_scalar hχ hν hR
  refine ⟨C1 + M * C1 + C2, fun μ hμ μ' hμ' g hg τ y hy j => ?_⟩
  have hμ0 : 0 ≤ μ := le_trans ha.le hμ.1
  have hμ'0 : 0 ≤ μ' := le_trans ha.le hμ'.1
  set N := (eLpNorm g 2 (ageμ c (-1 / 2))).toReal
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  obtain ⟨hb0, hb1⟩ := h1 μ μ' hμ0 hμ'0 g hg τ y hy
  have hb2 := h2 μ μ' hμ0 hμ'0 g hg τ y hy j
  obtain ⟨hds, hMs⟩ := hM y hy
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hE : ∀ m : ℝ, -(1 / 4) < m →
      physPd (wardX ν m R c χy g τ) j y =
        χy (ν * age R y) • physPd (wardX0 ν m R c g τ) j y +
          (fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
            wardX0 ν m R c g τ y +
          physPd (wardStreamCorr ν R χy (wardX0 ν m R c g) τ) j y := by
    intro m hm
    have hd1 : DifferentiableAt ℝ (wardX0 ν m R c g τ) y :=
      ((w2_smooth hν hR hc hm hg τ).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by simp)
    have hd2 : DifferentiableAt ℝ (wardStreamCorr ν R χy (wardX0 ν m R c g) τ) y :=
      w2_corr_diff hχ hν hR hc hm hg τ hyU
    have hfun : wardX ν m R c χy g τ =
        (fun y' => χy (ν * age R y') • wardX0 ν m R c g τ y') +
          wardStreamCorr ν R χy (wardX0 ν m R c g) τ :=
      funext fun y' => wardX_eq_cut_add_corr ν m R c χy g τ y'
    have hdc : DifferentiableAt ℝ (fun y' => χy (ν * age R y') • wardX0 ν m R c g τ y') y :=
      hds.smul hd1
    unfold physPd
    have hsm : HasFDerivAt (fun y' => χy (ν * age R y') • wardX0 ν m R c g τ y')
        (χy (ν * age R y) • fderiv ℝ (wardX0 ν m R c g τ) y +
          (fderiv ℝ (fun y' => χy (ν * age R y')) y).smulRight (wardX0 ν m R c g τ y)) y :=
      hds.hasFDerivAt.smul hd1.hasFDerivAt
    rw [hfun, fderiv_add hdc hd2, hsm.fderiv]
    simp [add_assoc]
  have hsub : physPd (wardX ν μ R c χy g τ) j y - physPd (wardX ν μ' R c χy g τ) j y =
      χy (ν * age R y) • (physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) +
        (fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
          (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) +
        (physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y) := by
    rw [hE μ (by linarith), hE μ' (by linarith), smul_sub, smul_sub]
    abel
  have hr := hχ.range (ν * age R y)
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hMs j)
  rw [hsub]
  calc _ ≤ ‖χy (ν * age R y) •
              (physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) +
            (fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
              (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y)‖ +
          ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
            physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ := norm_add_le _ _
    _ ≤ (‖χy (ν * age R y) •
              (physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y)‖ +
            ‖(fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
              (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y)‖) +
          C2 * |μ - μ'| * N := by
        gcongr
        · exact norm_add_le _ _
    _ ≤ (C1 * |μ - μ'| * N + M * (C1 * |μ - μ'| * N)) + C2 * |μ - μ'| * N := by
        gcongr
        · rw [norm_smul, Real.norm_of_nonneg hr.1]
          calc _ ≤ 1 * ‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ := by
                gcongr; exact hr.2
            _ ≤ C1 * |μ - μ'| * N := by rw [one_mul]; exact hb1 j
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hMs j) hb0 (norm_nonneg _) hMn
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
end
