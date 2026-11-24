import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_4.H1

/-!
# Helpers for `wardDXYoungSup_proved` (2): proofs of `WardX0DSup` and `WardCorrDSup`

Source of record: `the November 2 reference manuscript` (73 pages), 3603-3629,
3687-3713, 4178-4186, 5238-5244.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Helper to convert an `ENNReal.ofReal` inequality against `eLpNorm g 2` into a real inequality. -/
lemma w114_ofReal_le_toReal {c ν X K : ℝ} (hK : 0 ≤ K) {g : Chart → Ten3} (hg : IsOldL2 c ν g)
    (h : ENNReal.ofReal X ≤ ENNReal.ofReal K * eLpNorm g 2 (ageμ c (-1 / 2))) :
    X ≤ K * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  by_cases hX : 0 ≤ X
  · have htop : eLpNorm g 2 (ageμ c (-1 / 2)) ≠ ⊤ := hg.memLp.eLpNorm_lt_top.ne
    have h' : ENNReal.ofReal X ≤
        ENNReal.ofReal (K * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal) := by
      calc ENNReal.ofReal X ≤ ENNReal.ofReal K * eLpNorm g 2 (ageμ c (-1 / 2)) := h
        _ = ENNReal.ofReal K * ENNReal.ofReal (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
            rw [ENNReal.ofReal_toReal htop]
        _ = ENNReal.ofReal (K * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal) := by
            rw [← ENNReal.ofReal_mul hK]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK ENNReal.toReal_nonneg)).1 h'
  · linarith [mul_nonneg hK (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm g 2 (ageμ c (-1 / 2))).toReal)]

/-- Single-`m` pointwise sup bound on `sepWre` and `physPd (sepWre ...)` on `R√ν ≤ ϱ y`. -/
theorem w114_single_sup (m : ℝ) (hm : -(1 / 4) < m) (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R)
    (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
        ‖sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y‖ ≤
          C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal ∧
        ∀ j : Fin 3,
          ‖physPd (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) j y‖ ≤
            C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  have hr0 : 0 ≤ r0 := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0
  have hD : 0 < D := sub_pos.2 hrr
  set P : ℝ := 2 * c / R
  have hP : 0 < P := by positivity
  set a : ℝ := 2 * m + 2
  have ha : 1 / 2 < a := by simp only [a]; linarith
  obtain ⟨K0, hK0, hSup0⟩ := w114_w2Dom_sup (IIIa.sepKd_measurable 0 D)
    (w114_sepKd_sq_ne_top 0 hD) ha hP
  obtain ⟨K1, hK1, hSup1⟩ := w114_w2Dom_sup (IIIa.sepKd_measurable 1 D)
    (w114_sepKd_sq_ne_top 1 hD) ha hP
  obtain ⟨Cd0, hCd0, hdom0⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 0
  obtain ⟨Cd1, hCd1, hdom1⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 1
  set S : ℝ := Real.sqrt (Real.pi * R ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set C0 : ℝ := ‖w10Re‖ * Cd0 * K0 * S
  set C1 : ℝ := ‖w10Re‖ * Cd1 * K1 * S
  have hC0 : 0 ≤ C0 := by positivity
  have hC1 : 0 ≤ C1 := by positivity
  set C : ℝ := max C0 C1
  refine ⟨C, le_trans hC0 (le_max_left _ _), fun g hg τ y hy => ?_⟩
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
  have hW0_le : IIIa.sepDom (2 * (m : ℂ).re + 2) 0 D G τ y ≤
      ENNReal.ofReal K0 * IIIa.ltauLq P 2 G := by
    have : 2 * (m : ℂ).re + 2 = a := by simp [a]
    rw [this, w2_sepDom_eq]
    exact hSup0 G hGm hGper τ y
  have hW0_lt : IIIa.sepDom (2 * (m : ℂ).re + 2) 0 D G τ y < ⊤ :=
    lt_of_le_of_lt hW0_le (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hltau_top.lt_top)
  have hW1_le : IIIa.sepDom (2 * (m : ℂ).re + 2) 1 D G τ y ≤
      ENNReal.ofReal K1 * IIIa.ltauLq P 2 G := by
    have : 2 * (m : ℂ).re + 2 = a := by simp [a]
    rw [this, w2_sepDom_eq]
    exact hSup1 G hGm hGper τ y
  have hm' : -(1 / 4) < (m : ℂ).re := by simpa using hm
  have hd0 := hdom0 ν hν (m : ℂ) hm' r0 (R * Real.sqrt ν) P hr0 hrr hP T hSep τ y hy hW0_lt
  have hd1 := hdom1 ν hν (m : ℂ) hm' r0 (R * Real.sqrt ν) P hr0 hrr hP T hSep τ y hy hW0_lt
  set N : ℝ := (eLpNorm g 2 (ageμ c (-1 / 2))).toReal
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  refine ⟨?_, fun j => ?_⟩
  · have hb0 : ENNReal.ofReal ‖sepWre ν m T τ y‖ ≤
        ENNReal.ofReal C0 * eLpNorm g 2 (ageμ c (-1 / 2)) := by
      calc ENNReal.ofReal ‖sepWre ν m T τ y‖
          = ‖sepWre ν m T τ y‖ₑ := ofReal_norm _
        _ ≤ ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 0 τ y :=
            w2_enorm_sepWre m T τ y
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal Cd0 * IIIa.sepDom (2 * (m : ℂ).re + 2) 0 D G τ y) :=
            mul_le_mul' le_rfl hd0
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal Cd0 * (ENNReal.ofReal K0 * IIIa.ltauLq P 2 G)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hW0_le)
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal Cd0 * (ENNReal.ofReal K0 *
              (ENNReal.ofReal S * eLpNorm g 2 (ageμ c (-1 / 2))))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsrc))
        _ = ENNReal.ofReal C0 * eLpNorm g 2 (ageμ c (-1 / 2)) := by
            simp only [C0]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity)]
            ring
    exact (w114_ofReal_le_toReal hC0 hg hb0).trans
      (mul_le_mul_of_nonneg_right (le_max_left C0 C1) hN0)
  · have hy' : r0 < ϱ y := lt_of_lt_of_le hrr hy
    have hA := w10_diffA (m := m) hν hm hr0 hP hSep hM τ hy'
    have h1 := w10_norm1V m T τ y hA
    have hpd_le : ‖physPd (sepWre ν m T τ) j y‖ ≤
        ‖w10Re‖ * ‖fderiv ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y‖ := by
      unfold physPd
      calc ‖fderiv ℝ (sepWre ν m T τ) y (coordinateVector j)‖
          ≤ ‖fderiv ℝ (sepWre ν m T τ) y‖ * ‖(coordinateVector j : Space)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (sepWre ν m T τ) y‖ := by rw [wyl_norm_coordinateVector, mul_one]
        _ ≤ ‖w10Re‖ * ‖fderiv ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y‖ := h1
    have hb1 : ENNReal.ofReal ‖physPd (sepWre ν m T τ) j y‖ ≤
        ENNReal.ofReal C1 * eLpNorm g 2 (ageμ c (-1 / 2)) := by
      have he : ENNReal.ofReal ‖physPd (sepWre ν m T τ) j y‖ ≤
          ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 1 τ y := by
        unfold IIIa.wDerivNorm
        rw [← ofReal_norm, norm_iteratedFDeriv_one, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hpd_le
      calc ENNReal.ofReal ‖physPd (sepWre ν m T τ) j y‖
          ≤ ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 1 τ y := he
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal Cd1 * IIIa.sepDom (2 * (m : ℂ).re + 2) 1 D G τ y) :=
            mul_le_mul' le_rfl hd1
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal Cd1 * (ENNReal.ofReal K1 * IIIa.ltauLq P 2 G)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hW1_le)
        _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal Cd1 * (ENNReal.ofReal K1 *
              (ENNReal.ofReal S * eLpNorm g 2 (ageμ c (-1 / 2))))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsrc))
        _ = ENNReal.ofReal C1 * eLpNorm g 2 (ageμ c (-1 / 2)) := by
            simp only [C1]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity)]
            ring
    exact (w114_ofReal_le_toReal hC1 hg hb1).trans
      (mul_le_mul_of_nonneg_right (le_max_right C0 C1) hN0)

/-- Proof of `WardX0DSup` (`PartIII-b:C/ward/11/4` first leaf). -/
theorem w114_wardX0DSup_proved :
    ∀ (ν μ R c : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
      ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
        ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
          DifferentiableAt ℝ (wardX0 ν μ R c g τ) y ∧
          ‖wardX0 ν μ R c g τ y‖ ≤ C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal ∧
          ∀ j : Fin 3,
            ‖physPd (wardX0 ν μ R c g τ) j y‖ ≤ C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  intro ν μ R c hν hR hc hμ
  have hμ1 : -(1 / 4) < μ + 1 := by linarith
  obtain ⟨Ca, hCa, hSa⟩ := w114_single_sup μ hμ ν R c hν hR hc
  obtain ⟨Cb, hCb, hSb⟩ := w114_single_sup (μ + 1) hμ1 ν R c hν hR hc
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  refine ⟨Ca + Cb, fun g hg τ y hy => ?_⟩
  obtain ⟨hSep, hM, -⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  have hr0 : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set T := oldCutSrc R c r0 g
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  obtain ⟨ha0, ha1⟩ := hSa g hg τ y hy
  obtain ⟨hb0, hb1⟩ := hSb g hg τ y hy
  refine ⟨?_, ?_, fun j => ?_⟩
  · exact ((w2_smooth hν hR hc hμ hg τ).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by simp)
  · rw [hX0, sepX0_eq_sub]
    calc ‖sepWre ν μ T τ y - sepWre ν (μ + 1) T τ y‖
        ≤ ‖sepWre ν μ T τ y‖ + ‖sepWre ν (μ + 1) T τ y‖ := norm_sub_le _ _
      _ ≤ (Ca + Cb) * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by linarith
  · have hda : DifferentiableAt ℝ (sepWre ν μ T τ) y := w10_diffV hν hμ hr0 hP hSep hM τ hyU
    have hdb : DifferentiableAt ℝ (sepWre ν (μ + 1) T τ) y :=
      w10_diffV hν hμ1 hr0 hP hSep hM τ hyU
    have hfun : wardX0 ν μ R c g τ = fun x => sepWre ν μ T τ x - sepWre ν (μ + 1) T τ x := by
      rw [hX0]; funext x; exact sepX0_eq_sub _ _ _ _ _
    have hpd : physPd (wardX0 ν μ R c g τ) j y =
        physPd (sepWre ν μ T τ) j y - physPd (sepWre ν (μ + 1) T τ) j y := by
      unfold physPd
      rw [hfun, fderiv_fun_sub hda hdb, sub_apply]
    rw [hpd]
    calc ‖physPd (sepWre ν μ T τ) j y - physPd (sepWre ν (μ + 1) T τ) j y‖
        ≤ ‖physPd (sepWre ν μ T τ) j y‖ + ‖physPd (sepWre ν (μ + 1) T τ) j y‖ := norm_sub_le _ _
      _ ≤ (Ca + Cb) * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by linarith [ha1 j, hb1 j]

/-- Proof of `WardCorrDSup` (`PartIII-b:C/ward/11/4` second leaf). -/
theorem w114_wardCorrDSup_proved :
    ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
      ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
        ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
          DifferentiableAt ℝ (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) y ∧
          ∀ j : Fin 3, ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ ≤
            C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal := by
  intro ν μ R c χy hχ hν hR hc hμ
  obtain ⟨CX0, hX0⟩ := w114_wardX0DSup_proved ν μ R c hν hR hc hμ
  set CX0' : ℝ := max CX0 0
  have hCX0' : 0 ≤ CX0' := le_max_right _ _
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
  set a : ℝ := 2 * μ + 2
  have ha : 1 / 2 < a := by simp only [a]; linarith
  obtain ⟨Cpsi, hCpsi, hPsiDom⟩ := w2_psi_dom hν hR hc hμ r2
  obtain ⟨Kpsi, hKpsi, hSupPsi⟩ := w114_w2Dom_sup (w2k_measurable r0 D (r2 + r0))
    (w114_w2k_sq_ne_top hr0 hD (r2 + r0)) ha hP
  obtain ⟨Ca, Cb, hCa, hCb, hab⟩ := w2a_bound hχ hν hR
  set S : ℝ := Real.sqrt (Real.pi * R ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set C_P : ℝ := Cpsi * Kpsi * S
  have hC_P : 0 ≤ C_P := by positivity
  refine ⟨Cb * C_P + 2 * Ca * r2 * CX0', fun g hg τ y hy => ?_⟩
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  refine ⟨w2_corr_diff hχ hν hR hc hμ hg τ hyU, fun j => ?_⟩
  have hb := w2_corr_pd_bound hχ hν hR hc hμ hg τ j hyU
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
    have hpsi_e : ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| ≤
        ENNReal.ofReal C_P * eLpNorm g 2 (ageμ c (-1 / 2)) := by
      calc ENNReal.ofReal |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)|
          ≤ ENNReal.ofReal Cpsi * w2Dom (w2k r0 D (r2 + r0)) a G τ y :=
            hPsiDom g hg τ y hy h2
        _ ≤ ENNReal.ofReal Cpsi * (ENNReal.ofReal Kpsi * IIIa.ltauLq P 2 G) :=
            mul_le_mul' le_rfl (hSupPsi G hGm hGper τ y)
        _ ≤ ENNReal.ofReal Cpsi *
            (ENNReal.ofReal Kpsi * (ENNReal.ofReal S * eLpNorm g 2 (ageμ c (-1 / 2)))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hsrc)
        _ = ENNReal.ofReal C_P * eLpNorm g 2 (ageμ c (-1 / 2)) := by
            simp only [C_P]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            ring
    have hpsi_r : |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| ≤ C_P * N :=
      w114_ofReal_le_toReal hC_P hg hpsi_e
    have hX0_r : ‖wardX0 ν μ R c g τ y‖ ≤ CX0' * N :=
      ((hX0 g hg τ y hy).2.1).trans (mul_le_mul_of_nonneg_right (le_max_left CX0 0) hN0)
    have e1 : |deriv (w2a ν R χy) (ϱ y)| * |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| ≤
        Cb * (C_P * N) :=
      mul_le_mul hw' hpsi_r (abs_nonneg _) hCb
    have hρ0 : 0 ≤ ϱ y := ϱ_nonneg y
    have h2r : 2 * ϱ y * ‖wardX0 ν μ R c g τ y‖ ≤ 2 * r2 * (CX0' * N) := by
      calc 2 * ϱ y * ‖wardX0 ν μ R c g τ y‖
          ≤ 2 * r2 * ‖wardX0 ν μ R c g τ y‖ := by nlinarith [norm_nonneg (wardX0 ν μ R c g τ y)]
        _ ≤ 2 * r2 * (CX0' * N) := mul_le_mul_of_nonneg_left hX0_r (by positivity)
    have e2 : |w2a ν R χy (ϱ y)| * (2 * ϱ y * ‖wardX0 ν μ R c g τ y‖) ≤
        Ca * (2 * r2 * (CX0' * N)) :=
      mul_le_mul hw h2r (by positivity) hCa
    linarith
  · have h2' := not_le.1 h2
    rw [w2a_zero_of_gt hχ hν hR h2', w2a_deriv_zero_of_gt hχ hν hR h2']
    simp only [abs_zero, zero_mul, add_zero]
    positivity

end UnforcedLeray.Short.PartIIIb.Concrete
end
