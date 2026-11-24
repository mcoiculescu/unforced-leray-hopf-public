import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.SepWSubDom
import UnforcedLeray.Short.PartIIIa.T16_SepYoung
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_3

/-!
# Helpers for `wardDXSubYoungL2_proved` (1): `μ`-Lipschitz bounds for `sepWre` and `wardX0`

Source of record: `the November 2 reference manuscript`
lines 3633-3648 (`sep:young`), 4171-4174, 4194-4196, 5701-5704.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `sep:young` (`p = q = 2`, `b = 1`) for a transfer field `w10Fn R ν N` dominated at the
meridian point by the `j`-th derivative difference of `sepW`, via `sepWSubDom_proved`. -/
theorem wSub_gtl (j : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν R c m m' : ℝ), 0 < ν → 0 < R → 0 < c → 0 ≤ m → 0 ≤ m' →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6)) T →
      SepMoment (2 * c / R) T →
      ∀ (K : ℝ) (N : ℝ → Space → ℝ), 0 ≤ K → Measurable (fun x : ℝ × Space => N x.1 x.2) →
      (∀ τ y, N (τ + 2 * c / R) y = N τ y) → (∀ τ y, 0 ≤ N τ y) →
      (∀ τ y, R * Real.sqrt ν ≤ ϱ y →
        ENNReal.ofReal (N τ (meridPt y)) ≤
          ENNReal.ofReal K *
            ‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
              iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ) →
      ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
          (ENNReal.ofReal K * (ENNReal.ofReal (C0 *
            (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - (j : ℝ) + 3 / 1) * |m - m'|) *
            IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T))) ^ (2 : ℝ) := by
  obtain ⟨Cj, hCj, hSub⟩ := sepWSubDom_proved j
  obtain ⟨Cb, hCb, hB'⟩ := _root_.sepDomYoung j 2 2 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cz, _, hBz⟩ := _root_.sepDomYoung 0 2 2 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cj * Cb, mul_nonneg hCj hCb, ?_⟩
  intro ν R c m m' hν hR hc hm hm' T hT hM K N hK hNm hNp hN0 hDom
  have hP : 0 < 2 * c / R := by positivity
  have hper : ∀ τ y, w10Fn R ν N (τ + 2 * c / R) y = w10Fn R ν N τ y :=
    w10Fn_periodic R ν _ hNp
  have hTr := chartYoungTransport R c ν hR hc hν (w10Fn R ν N) (w10Fn_measurable R ν hNm)
    (w10Fn_axi R ν N) hper
  refine hTr.trans ?_
  gcongr
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  have hrO : 0 ≤ r0 := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0
  have hD : 0 < D := sub_pos.2 hrr
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  have ha0 : 0 ≤ a0 := by norm_num [a0]
  have hδ0 : (1 / 2 : ℝ) ≤ a0 - 2 + 3 / 2 := by norm_num [a0]
  have hgm : Measurable (Function.uncurry (IIIa.srcNorm T)) := IIIa.sepAE_measurable_srcNorm hT
  have hTper : ∀ τ z, IIIa.srcNorm T (τ + 2 * c / R) z = IIIa.srcNorm T τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hT.periodic]
  have h0 : IIIa.ltauLq (2 * c / R) 2 (IIIa.sepDom a0 0 D (IIIa.srcNorm T)) < ⊤ :=
    (hBz a0 ha0 hδ0 D (2 * c / R) hD hP _ hgm hTper).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM)
  have hae := IIIa.sepAE_lt_top_of_ltauLq (2 * c / R) 2 two_pos
    (IIIa.sepAE_measurable_sepDom a0 0 D hgm) h0
  calc IIIa.ltauLq (2 * c / R) 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖w10Fn R ν N τ y‖ₑ else 0)
      ≤ IIIa.ltauLq (2 * c / R) 2 (fun τ y =>
          (ENNReal.ofReal K * ENNReal.ofReal (Cj * |m - m'|)) *
            IIIa.sepDom a0 j D (IIIa.srcNorm T) τ y) := by
        refine IIIa.sepAE_ltauLq_mono (2 * c / R) 2 two_pos ?_
        filter_upwards [hae] with τ hτ
        filter_upwards [hτ] with y hy
        by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
        · rw [if_pos h]
          have h' : R * Real.sqrt ν ≤ ϱ y := h
          rw [w10Fn_enorm hN0 τ h', mul_assoc]
          exact (hDom τ y h').trans (mul_le_mul' le_rfl
            (hSub ν m m' r0 (R * Real.sqrt ν) (2 * c / R) hν hm hm' hrO hrr hP T hT τ y h hy))
        · rw [if_neg h]
          exact bot_le
    _ = (ENNReal.ofReal K * ENNReal.ofReal (Cj * |m - m'|)) *
          IIIa.ltauLq (2 * c / R) 2 (IIIa.sepDom a0 j D (IIIa.srcNorm T)) :=
        IIIa.ltauLq_const_mul _ 2 two_pos _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) _
    _ ≤ (ENNReal.ofReal K * ENNReal.ofReal (Cj * |m - m'|)) *
          (ENNReal.ofReal (Cb * D ^ (-4 - (j : ℝ) + 3 / 1)) *
            IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T)) := by
        gcongr
        exact hB' a0 ha0 hδ0 D (2 * c / R) hD hP _ hgm hTper
    _ = ENNReal.ofReal K * (ENNReal.ofReal (Cj * Cb *
          D ^ (-4 - (j : ℝ) + 3 / 1) * |m - m'|) *
          IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T)) := by
        rw [mul_assoc (ENNReal.ofReal K), ← mul_assoc (ENNReal.ofReal (Cj * |m - m'|)),
          ← ENNReal.ofReal_mul (mul_nonneg hCj (abs_nonneg _))]
        congr 3
        ring

/-- Order-`0` `μ`-Lipschitz young bound for `sepWre ν m T - sepWre ν m' T` (`0 ≤ m, m'`). -/
theorem wSub_single0 (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' → ∀ g : Chart → Ten3, IsOldL2 c ν g →
      WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R (fun τ y =>
          sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y -
            sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y))
        (C * |m - m'|) := by
  obtain ⟨C0, hC0, hG⟩ := wSub_gtl 0
  set b : ℝ := C0 * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((0 : ℕ) : ℝ) + 3 / 1)
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hb0 : 0 ≤ b := mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  refine ⟨‖w10Re‖ * b, mul_nonneg (norm_nonneg _) hb0, ?_⟩
  intro m m' hm hm' g hg
  have hm4 : -(1 / 4) < m := by linarith
  have hm'4 : -(1 / 4) < m' := by linarith
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set V : ℝ → Space → Space := fun τ y => sepWre ν m T τ y - sepWre ν m' T τ y
  have hVm : Measurable (fun x : ℝ × Space => V x.1 x.2) :=
    (sepWre_measurable ν m hν T hS.measurable).sub (sepWre_measurable ν m' hν T hS.measurable)
  have hNm : Measurable (fun x : ℝ × Space => ‖V x.1 x.2‖) := hVm.norm
  refine ⟨(w10_read_meas hVm).aestronglyMeasurable, ?_⟩
  have hDom : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal ‖V τ (meridPt y)‖ ≤
        ENNReal.ofReal ‖w10Re‖ *
          ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
            iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := by
    intro τ y hy
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrr hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy'
    obtain ⟨M, hMo, hTM, hmer, _⟩ := w10_rotdatum hAx hρ
    have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
      rw [w10_varrho_meridPt]; exact hy'
    have e1 := w10_equivV hν hm4 hr hP hS hM hMo hTM τ (meridPt y) hmU
    have e2 := w10_equivV hν hm'4 hr hP hS hM hMo hTM τ (meridPt y) hmU
    rw [hmer] at e1 e2
    have hn : ‖V τ (meridPt y)‖ = ‖V τ y‖ := by
      show ‖sepWre ν m T τ (meridPt y) - sepWre ν m' T τ (meridPt y)‖ =
        ‖sepWre ν m T τ y - sepWre ν m' T τ y‖
      rw [e1, e2, ← w2_actM_sub, norm_actM hMo]
    rw [hn, ← ofReal_norm]
    have h0eq : ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
          iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ =
        ‖IIIa.sepW ν (m : ℂ) T y τ - IIIa.sepW ν (m' : ℂ) T y τ‖ := by
      rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp_apply, ← map_sub]
      exact (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).symm.norm_map _
    rw [h0eq, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hVre : V τ y = w10Re (IIIa.sepW ν (m : ℂ) T y τ - IIIa.sepW ν (m' : ℂ) T y τ) := by
      show sepWre ν m T τ y - sepWre ν m' T τ y = _
      rw [w10_sepWre_eq, w10_sepWre_eq, Function.comp_apply, Function.comp_apply, ← map_sub]
    rw [hVre]
    exact w10Re.le_opNorm _
  have hI := hG ν R c m m' hν hR hc hm hm' T hS hM ‖w10Re‖ (fun τ y => ‖V τ y‖)
    (norm_nonneg _) hNm
    (fun τ y => by
      simp only [V, sepWre_periodic ν m _ T hS.periodic, sepWre_periodic ν m' _ T hS.periodic])
    (fun τ y => norm_nonneg _) hDom
  have hfin := w10_final hν hR hc g hg.measurable _ (fun τ y => norm_nonneg _)
    (F := V) (fun τ y _ => le_rfl) ‖w10Re‖ (b * |m - m'|) (norm_nonneg _)
    (mul_nonneg hb0 (abs_nonneg _)) hI
  rwa [← mul_assoc] at hfin

/-- Order-`1` `μ`-Lipschitz young bound for `physPd (sepWre ν m T τ) k - physPd (sepWre ν m' T τ) k`
(`0 ≤ m, m'`). -/
theorem wSub_single1 (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' → ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ k : Fin 3,
        WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
          (wardYoungRead ν R (fun τ y =>
            physPd (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) k y -
              physPd (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) k y))
          (C * |m - m'|) := by
  obtain ⟨C0, hC0, hG⟩ := wSub_gtl 1
  set b : ℝ := C0 * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((1 : ℕ) : ℝ) + 3 / 1)
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hb0 : 0 ≤ b := mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  refine ⟨‖w10Re‖ * b, mul_nonneg (norm_nonneg _) hb0, ?_⟩
  intro m m' hm hm' g hg k
  have hm4 : -(1 / 4) < m := by linarith
  have hm'4 : -(1 / 4) < m' := by linarith
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set V : ℝ → Space → Space := fun τ y => sepWre ν m T τ y - sepWre ν m' T τ y
  have hVm : Measurable (fun x : ℝ × Space => V x.1 x.2) :=
    (sepWre_measurable ν m hν T hS.measurable).sub (sepWre_measurable ν m' hν T hS.measurable)
  set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hUm : MeasurableSet U := hUo.measurableSet
  have hperV : ∀ τ, V (τ + 2 * c / R) = V τ := fun τ => by
    funext y
    simp only [V, sepWre_periodic ν m _ T hS.periodic, sepWre_periodic ν m' _ T hS.periodic]
  have hdV : ∀ τ y, y ∈ U → DifferentiableAt ℝ (V τ) y := fun τ y hy =>
    (w10_diffV hν hm4 hr hP hS hM τ hy).sub (w10_diffV hν hm'4 hr hP hS hM τ hy)
  have hPd := w10_meas_pd hVm hUm hdV k
  set N : ℝ → Space → ℝ := fun τ y => ‖if y ∈ U then physPd (V τ) k y else 0‖ with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := hPd.norm
  have hread : wardYoungRead ν R (fun τ y =>
        physPd (sepWre ν m T τ) k y - physPd (sepWre ν m' T τ) k y) =
      wardYoungRead ν R (fun τ y => if y ∈ U then physPd (V τ) k y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hsub : physPd (V τ) k y =
        physPd (sepWre ν m T τ) k y - physPd (sepWre ν m' T τ) k y := by
      unfold physPd V
      rw [fderiv_fun_sub (w10_diffV hν hm4 hr hP hS hM τ hyU)
        (w10_diffV hν hm'4 hr hP hS hM τ hyU)]
      rfl
    simp [hyU, hsub]
  refine ⟨?_, ?_⟩
  · rw [hread]
    exact (w10_read_meas hPd).aestronglyMeasurable
  have hDom : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤
        ENNReal.ofReal ‖w10Re‖ *
          ‖iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
            iteratedFDeriv ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := by
    intro τ y hy
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrr hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy'
    obtain ⟨M, hMo, hTM, hmer, hMϱ⟩ := w10_rotdatum hAx hρ
    have hmU : meridPt y ∈ U := by
      show R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y)
      rw [w10_varrho_meridPt]; exact hy'
    have hrot := w10_fderiv_rot (f := V τ) hUo hMo
      (fun z hz => by
        show R * Real.sqrt (5 * ν / 6) < ϱ (actM M z)
        rw [hMϱ]; exact hz)
      (fun z hz => hdV τ z hz)
      (fun z hz => by
        show sepWre ν m T τ (actM M z) - sepWre ν m' T τ (actM M z) =
          actM M (sepWre ν m T τ z - sepWre ν m' T τ z)
        rw [w10_equivV hν hm4 hr hP hS hM hMo hTM τ z hz,
          w10_equivV hν hm'4 hr hP hS hM hMo hTM τ z hz, w2_actM_sub])
      hmU (coordinateVector k)
    rw [hmer] at hrot
    set A : Space → Fin 3 → ℂ :=
      fun y' => IIIa.sepW ν (m : ℂ) T y' τ - IIIa.sepW ν (m' : ℂ) T y' τ
    have hAm : ContDiffAt ℝ 1 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y :=
      ((contDiffOn_pi.2 fun i => sepW_contDiffOn_top ν (m : ℂ) _ _ T hν (by simpa using hm4) hr hP
        hS hM τ i).contDiffAt (hUo.mem_nhds hy')).of_le (by exact_mod_cast le_top)
    have hAm' : ContDiffAt ℝ 1 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y :=
      ((contDiffOn_pi.2 fun i => sepW_contDiffOn_top ν (m' : ℂ) _ _ T hν (by simpa using hm'4) hr hP
        hS hM τ i).contDiffAt (hUo.mem_nhds hy')).of_le (by exact_mod_cast le_top)
    have hAd : DifferentiableAt ℝ A y :=
      (hAm.differentiableAt one_ne_zero).sub (hAm'.differentiableAt one_ne_zero)
    have hVA : V τ = w10Re ∘ A := by
      funext y'
      show sepWre ν m T τ y' - sepWre ν m' T τ y' = w10Re (A y')
      rw [w10_sepWre_eq, w10_sepWre_eq, Function.comp_apply, Function.comp_apply, ← map_sub]
    have h1 : ‖fderiv ℝ (V τ) y‖ ≤ ‖w10Re‖ * ‖fderiv ℝ A y‖ := by
      rw [hVA, (w10Re.hasFDerivAt.comp y hAd.hasFDerivAt).fderiv]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hNn : N τ (meridPt y) = ‖physPd (V τ) k (meridPt y)‖ := by
      simp only [hN, if_pos hmU]
    have hle : N τ (meridPt y) ≤ ‖w10Re‖ * ‖iteratedFDeriv ℝ 1 A y‖ := by
      rw [hNn, norm_iteratedFDeriv_one]
      refine le_trans hrot ?_
      rw [wyl_norm_coordinateVector, mul_one]
      exact h1
    rw [← ofReal_norm, ← iteratedFDeriv_sub_apply hAm hAm',
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  have hI := hG ν R c m m' hν hR hc hm hm' T hS hM ‖w10Re‖ N (norm_nonneg _) hNm
    (fun τ y => by simp only [hN, hperV]) (fun τ y => norm_nonneg _) hDom
  rw [hread]
  have hfin := w10_final hν hR hc g hg.measurable _ (fun τ y => norm_nonneg _)
    (F := fun τ y => if y ∈ U then physPd (V τ) k y else 0)
    (fun τ y _ => le_rfl) ‖w10Re‖ (b * |m - m'|) (norm_nonneg _)
    (mul_nonneg hb0 (abs_nonneg _)) hI
  rwa [← mul_assoc] at hfin

/-- `μ`-Lipschitz young `L²` bounds for `wardX0` and `physPd (wardX0)` (`0 ≤ μ, μ'`). -/
theorem wSub_wardX0YoungL2 (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' → ∀ g : Chart → Ten3, IsOldL2 c ν g →
      YoungL2Le c ν R (C * |μ - μ'|)
        (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) g ∧
      ∀ j : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) g := by
  obtain ⟨C0, hC0, h0⟩ := wSub_single0 ν R c hν hR hc
  obtain ⟨D0, hD0, d0⟩ := wSub_single1 ν R c hν hR hc
  refine ⟨2 * C0 + 2 * D0, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg
  have hμ4 : -(1 / 4) < μ := by linarith
  have hμ'4 : -(1 / 4) < μ' := by linarith
  have hμ1 : 0 ≤ μ + 1 := by linarith
  have hμ'1 : 0 ≤ μ' + 1 := by linarith
  have hμ14 : -(1 / 4) < μ + 1 := by linarith
  have hμ'14 : -(1 / 4) < μ' + 1 := by linarith
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  have hX0' := w10_X0_eq (μ := μ') hν hR hc hg
  have hsub_eq : (μ + 1) - (μ' + 1) = μ - μ' := by ring
  have h0a := h0 μ μ' hμ hμ' g hg
  have h0b := h0 (μ + 1) (μ' + 1) hμ1 hμ'1 g hg
  rw [hsub_eq] at h0b
  refine ⟨?_, fun j => ?_⟩
  · refine w10_young_of_sum
      (A := fun τ y => sepWre ν μ T τ y - sepWre ν μ' T τ y)
      (B := fun τ y => sepWre ν (μ + 1) T τ y - sepWre ν (μ' + 1) T τ y)
      ?_ h0a h0b (mul_nonneg hC0 (abs_nonneg _)) (mul_nonneg hC0 (abs_nonneg _))
      (by nlinarith [abs_nonneg (μ - μ')]) ?_
    · exact (w10_read_meas
        ((wardX0_measurable_of_measurable ν μ R c g hg.measurable).sub
          (wardX0_measurable_of_measurable ν μ' R c g hg.measurable))).aestronglyMeasurable
    · refine w10_read_dom hν hR fun τ y _ => ?_
      have heq : wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y =
          (sepWre ν μ T τ y - sepWre ν μ' T τ y) -
            (sepWre ν (μ + 1) T τ y - sepWre ν (μ' + 1) T τ y) := by
        rw [hX0, hX0', sepX0_eq_sub, sepX0_eq_sub]
        abel
      rw [heq]
      exact norm_sub_le _ _
  · set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y}
    have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
    have hdV : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ y, y ∈ U → DifferentiableAt ℝ (sepWre ν m T τ) y :=
      fun m hm τ y hy => w10_diffV hν hm hr hP hS hM τ hy
    set ZSub : ℝ → Space → Space := fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y
    have hdZ : ∀ τ y, y ∈ U → DifferentiableAt ℝ (ZSub τ) y := by
      intro τ y hy
      have e1 : wardX0 ν μ R c g τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z := by
        funext z; rw [hX0]; exact sepX0_eq_sub ν μ T τ z
      have e2 : wardX0 ν μ' R c g τ = fun z => sepWre ν μ' T τ z - sepWre ν (μ' + 1) T τ z := by
        funext z; rw [hX0']; exact sepX0_eq_sub ν μ' T τ z
      show DifferentiableAt ℝ (fun z => wardX0 ν μ R c g τ z - wardX0 ν μ' R c g τ z) y
      rw [e1, e2]
      exact ((hdV μ hμ4 τ y hy).sub (hdV (μ + 1) hμ14 τ y hy)).sub
        ((hdV μ' hμ'4 τ y hy).sub (hdV (μ' + 1) hμ'14 τ y hy))
    have hZm : Measurable (fun x : ℝ × Space => ZSub x.1 x.2) :=
      (wardX0_measurable_of_measurable ν μ R c g hg.measurable).sub
        (wardX0_measurable_of_measurable ν μ' R c g hg.measurable)
    have hPd := w10_meas_pd hZm hUo.measurableSet hdZ j
    have hread : wardYoungRead ν R
          (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) =
        wardYoungRead ν R (fun τ y => if y ∈ U then physPd (ZSub τ) j y else 0) := by
      refine w10_read_congr hν hR fun τ y hy => ?_
      have hyU : y ∈ U := lt_of_lt_of_le hrr hy
      have hd1 : DifferentiableAt ℝ (wardX0 ν μ R c g τ) y := by
        have e1 : wardX0 ν μ R c g τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z := by
          funext z; rw [hX0]; exact sepX0_eq_sub ν μ T τ z
        rw [e1]
        exact (hdV μ hμ4 τ y hyU).sub (hdV (μ + 1) hμ14 τ y hyU)
      have hd2 : DifferentiableAt ℝ (wardX0 ν μ' R c g τ) y := by
        have e2 : wardX0 ν μ' R c g τ = fun z => sepWre ν μ' T τ z - sepWre ν (μ' + 1) T τ z := by
          funext z; rw [hX0']; exact sepX0_eq_sub ν μ' T τ z
        rw [e2]
        exact (hdV μ' hμ'4 τ y hyU).sub (hdV (μ' + 1) hμ'14 τ y hyU)
      have hsub : physPd (ZSub τ) j y =
          physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y := by
        unfold physPd ZSub
        rw [fderiv_fun_sub hd1 hd2]
        rfl
      simp [hyU, hsub]
    have d0a := d0 μ μ' hμ hμ' g hg j
    have d0b := d0 (μ + 1) (μ' + 1) hμ1 hμ'1 g hg j
    rw [hsub_eq] at d0b
    refine w10_young_of_sum
      (A := fun τ y => physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y)
      (B := fun τ y => physPd (sepWre ν (μ + 1) T τ) j y - physPd (sepWre ν (μ' + 1) T τ) j y)
      ?_ d0a d0b (mul_nonneg hD0 (abs_nonneg _)) (mul_nonneg hD0 (abs_nonneg _))
      (by nlinarith [abs_nonneg (μ - μ')]) ?_
    · rw [hread]
      exact (w10_read_meas hPd).aestronglyMeasurable
    · refine w10_read_dom hν hR fun τ y hy => ?_
      have hyU : y ∈ U := lt_of_lt_of_le hrr hy
      have e1 : wardX0 ν μ R c g τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z := by
        funext z; rw [hX0]; exact sepX0_eq_sub ν μ T τ z
      have e2 : wardX0 ν μ' R c g τ = fun z => sepWre ν μ' T τ z - sepWre ν (μ' + 1) T τ z := by
        funext z; rw [hX0']; exact sepX0_eq_sub ν μ' T τ z
      have hp1 : physPd (wardX0 ν μ R c g τ) j y =
          physPd (sepWre ν μ T τ) j y - physPd (sepWre ν (μ + 1) T τ) j y := by
        unfold physPd
        rw [e1, fderiv_fun_sub (hdV μ hμ4 τ y hyU) (hdV (μ + 1) hμ14 τ y hyU)]
        rfl
      have hp2 : physPd (wardX0 ν μ' R c g τ) j y =
          physPd (sepWre ν μ' T τ) j y - physPd (sepWre ν (μ' + 1) T τ) j y := by
        unfold physPd
        rw [e2, fderiv_fun_sub (hdV μ' hμ'4 τ y hyU) (hdV (μ' + 1) hμ'14 τ y hyU)]
        rfl
      have hp : physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y =
          (physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y) -
            (physPd (sepWre ν (μ + 1) T τ) j y - physPd (sepWre ν (μ' + 1) T τ) j y) := by
        rw [hp1, hp2]; abel
      rw [hp]
      exact norm_sub_le _ _

end UnforcedLeray.Short.PartIIIb.Concrete
end
