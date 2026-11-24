import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDXSubYoungL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_2

/-!
# `PartIII-b:C/cont/WE/2`: `WardD2XSubYoungL2`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Vector-valued second-derivative transformation under an orthogonal equivariance on an
invariant open set. -/
theorem w112_fderiv2_rot_eq {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hUinv : ∀ z ∈ U, actM M z ∈ U)
    (hf : ContDiffOn ℝ 2 f U)
    (he : ∀ z ∈ U, f (actM M z) = actM M (f z)) {z0 : Space} (hz0 : z0 ∈ U) (u v : Space) :
    actM M (fderiv ℝ (fun z => fderiv ℝ f z u) z0 v) =
      fderiv ℝ (fun w => fderiv ℝ f w (actM M u)) (actM M z0) (actM M v) := by
  have hd : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hd1 : ∀ (w0 : Space), w0 ∈ U → ∀ (u0 : Space),
      DifferentiableAt ℝ (fun w => fderiv ℝ f w u0) w0 := by
    intro w0 hw0 u0
    have h2 : ContDiffAt ℝ 2 f w0 := hf.contDiffAt (hU.mem_nhds hw0)
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) w0 := h2.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u0)
  have he1 : ∀ z ∈ U, fderiv ℝ f (actM M z) (actM M u) = actM M (fderiv ℝ f z u) := by
    intro z hz
    have hL : HasFDerivAt (f ∘ clmOf M) ((fderiv ℝ f (clmOf M z)).comp (clmOf M)) z :=
      (hd _ (hUinv z hz)).hasFDerivAt.comp z (clmOf M).hasFDerivAt
    have hR : HasFDerivAt (clmOf M ∘ f) ((clmOf M).comp (fderiv ℝ f z)) z :=
      (clmOf M).hasFDerivAt.comp z (hd z hz).hasFDerivAt
    have hev : (f ∘ clmOf M) =ᶠ[𝓝 z] (clmOf M ∘ f) := by
      filter_upwards [hU.mem_nhds hz] with z' hz'
      exact he z' hz'
    have huniq := (hR.congr_of_eventuallyEq hev).unique hL
    have h3 := congrArg (fun L : Space →L[ℝ] Space => L u) huniq
    simpa only [ContinuousLinearMap.comp_apply, clmOf_apply] using h3.symm
  set g1 : Space → Space := fun w => fderiv ℝ f w (actM M u)
  set g2 : Space → Space := fun z => fderiv ℝ f z u
  have hL2 : HasFDerivAt (g1 ∘ clmOf M) ((fderiv ℝ g1 (clmOf M z0)).comp (clmOf M)) z0 :=
    (hd1 _ (hUinv z0 hz0) (actM M u)).hasFDerivAt.comp z0 (clmOf M).hasFDerivAt
  have hR2 : HasFDerivAt (clmOf M ∘ g2) ((clmOf M).comp (fderiv ℝ g2 z0)) z0 :=
    (clmOf M).hasFDerivAt.comp z0 (hd1 z0 hz0 u).hasFDerivAt
  have hev2 : (g1 ∘ clmOf M) =ᶠ[𝓝 z0] (clmOf M ∘ g2) := by
    filter_upwards [hU.mem_nhds hz0] with z hz
    exact he1 z hz
  have huniq2 := (hR2.congr_of_eventuallyEq hev2).unique hL2
  have h4 := congrArg (fun L : Space →L[ℝ] Space => L v) huniq2
  simpa only [ContinuousLinearMap.comp_apply, clmOf_apply] using h4

theorem w112_norm_fderiv2_re_sub {A₁ A₂ : Space → (Fin 3 → ℂ)} {U : Set Space} (hUo : IsOpen U)
    (hA₁ : ContDiffOn ℝ 2 A₁ U) (hA₂ : ContDiffOn ℝ 2 A₂ U) {y : Space} (hy : y ∈ U)
    (u v : Space) :
    ‖fderiv ℝ (fun w => fderiv ℝ (w10Re ∘ A₁) w u) y v -
        fderiv ℝ (fun w => fderiv ℝ (w10Re ∘ A₂) w u) y v‖ ≤
      ‖w10Re‖ * (‖iteratedFDeriv ℝ 2 A₁ y - iteratedFDeriv ℝ 2 A₂ y‖ * ‖v‖ * ‖u‖) := by
  rw [w112_fderiv2_re hUo hA₁ hy u v, w112_fderiv2_re hUo hA₂ hy u v, ← map_sub]
  refine (w10Re.le_opNorm _).trans ?_
  gcongr
  have h := (iteratedFDeriv ℝ 2 A₁ y - iteratedFDeriv ℝ 2 A₂ y).le_opNorm ![v, u]
  simpa [Fin.prod_univ_two, mul_assoc] using h

/-- `WylBd` for `physPd2 (sepWre ν m T τ) j l - physPd2 (sepWre ν m' T τ) j l` for `0 ≤ m, m'`. -/
theorem wSub_single2 (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j l : Fin 3,
        WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
          (wardYoungRead ν R
            (fun τ y =>
              physPd2 (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) j l y -
                physPd2 (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) j l y))
          (C * |m - m'|) := by
  obtain ⟨C0, hC0, hG⟩ := wSub_gtl 2
  set b : ℝ := C0 * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((2 : ℕ) : ℝ) + 3 / 1)
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hb0 : 0 ≤ b := mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  refine ⟨‖w10Re‖ * b, mul_nonneg (norm_nonneg _) hb0, ?_⟩
  intro m m' hm hm' g hg j l
  have hm_gt : -(1 / 4) < m := by linarith
  have hm'_gt : -(1 / 4) < m' := by linarith
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hVm1 := sepWre_measurable ν m hν T hS.measurable
  have hVm2 := sepWre_measurable ν m' hν T hS.measurable
  set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hperV1 : ∀ τ, sepWre ν m T (τ + 2 * c / R) = sepWre ν m T τ := fun τ =>
    funext (sepWre_periodic ν m _ T hS.periodic τ)
  have hperV2 : ∀ τ, sepWre ν m' T (τ + 2 * c / R) = sepWre ν m' T τ := fun τ =>
    funext (sepWre_periodic ν m' _ T hS.periodic τ)
  have hV3_1 : ∀ τ, ContDiffOn ℝ 3 (sepWre ν m T τ) U := fun τ =>
    (w112_smoothV hν hm_gt hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hV3_2 : ∀ τ, ContDiffOn ℝ 3 (sepWre ν m' T τ) U := fun τ =>
    (w112_smoothV hν hm'_gt hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hPd2_1 := w112_meas_pd2 hVm1 hUo hV3_1 j l
  have hPd2_2 := w112_meas_pd2 hVm2 hUo hV3_2 j l
  have hPd2 := hPd2_1.sub hPd2_2
  set F : ℝ → Space → Space := fun τ y =>
    (if y ∈ U then physPd2 (sepWre ν m T τ) j l y else 0) -
      (if y ∈ U then physPd2 (sepWre ν m' T τ) j l y else 0)
  set N : ℝ → Space → ℝ := fun τ y => ‖F τ y‖ with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := hPd2.norm
  have hread : wardYoungRead ν R
      (fun τ y => physPd2 (sepWre ν m T τ) j l y - physPd2 (sepWre ν m' T τ) j l y) =
      wardYoungRead ν R F := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [F, this]
  refine ⟨?_, ?_⟩
  · rw [hread]
    exact (w10_read_meas hPd2).aestronglyMeasurable
  have hDom : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤
        ENNReal.ofReal ‖w10Re‖ *
          ‖iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
            iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := by
    intro τ y hy
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrr hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy'
    obtain ⟨M, hMo, hTM, hmer, hMϱ⟩ := w10_rotdatum hAx hρ
    have hmU : meridPt y ∈ U := by
      show R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y)
      rw [w10_varrho_meridPt]; exact hy'
    have hyU : y ∈ U := hy'
    have hV2_1 : ContDiffOn ℝ 2 (sepWre ν m T τ) U := (hV3_1 τ).of_le (by norm_num)
    have hV2_2 : ContDiffOn ℝ 2 (sepWre ν m' T τ) U := (hV3_2 τ).of_le (by norm_num)
    have hA2_1 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (m : ℂ) T z τ) U :=
      (w112_smoothA hν hm_gt hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
    have hA2_2 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (m' : ℂ) T z τ) U :=
      (w112_smoothA hν hm'_gt hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
    have hUinv : ∀ z ∈ U, actM M z ∈ U := fun z hz => by
      show R * Real.sqrt (5 * ν / 6) < ϱ (actM M z)
      rw [hMϱ]; exact hz
    have hrot1 := w112_fderiv2_rot_eq hUo hUinv hV2_1
      (fun z hz => w10_equivV hν hm_gt hr hP hS hM hMo hTM τ z hz)
      hmU (coordinateVector l) (coordinateVector j)
    have hrot2 := w112_fderiv2_rot_eq hUo hUinv hV2_2
      (fun z hz => w10_equivV hν hm'_gt hr hP hS hM hMo hTM τ z hz)
      hmU (coordinateVector l) (coordinateVector j)
    rw [hmer] at hrot1 hrot2
    have hNn : N τ (meridPt y) =
        ‖physPd2 (sepWre ν m T τ) j l (meridPt y) -
          physPd2 (sepWre ν m' T τ) j l (meridPt y)‖ := by
      simp only [hN, F, if_pos hmU]
    have hle : N τ (meridPt y) ≤
        ‖w10Re‖ * ‖iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
          iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ := by
      rw [hNn]
      unfold physPd2 physPd
      rw [← norm_actM hMo (fderiv ℝ _ (meridPt y) _ - fderiv ℝ _ (meridPt y) _),
        w2_actM_sub, hrot1, hrot2, w10_sepWre_eq, w10_sepWre_eq]
      refine (w112_norm_fderiv2_re_sub hUo hA2_1 hA2_2 hyU _ _).trans ?_
      rw [norm_actM hMo, norm_actM hMo, wyl_norm_coordinateVector, wyl_norm_coordinateVector,
        mul_one, mul_one]
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  have hI := hG ν R c m m' hν hR hc hm hm' T hS hM ‖w10Re‖ N (norm_nonneg _) hNm
    (fun τ y => by simp only [hN, F, hperV1, hperV2]) (fun τ y => norm_nonneg _)
    hDom
  rw [hread]
  have hb_mu : 0 ≤ b * |m - m'| := mul_nonneg hb0 (abs_nonneg _)
  have hfin := w10_final hν hR hc g hg.measurable _ (fun τ y => norm_nonneg _)
    (F := F) (fun τ y _ => le_rfl) ‖w10Re‖ (b * |m - m'|) (norm_nonneg _) hb_mu hI
  rwa [show ‖w10Re‖ * (b * |m - m'|) = ‖w10Re‖ * b * |m - m'| by ring] at hfin

/-- **`D²X₀` `μ`-difference in the young `L²` norm**. -/
theorem wSub_wardD2X0YoungL2 (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        ∀ j l : Fin 3,
          YoungL2Le c ν R (C * |μ - μ'|)
            (fun τ y =>
              physPd2 (wardX0 ν μ R c g τ) j l y - physPd2 (wardX0 ν μ' R c g τ) j l y) g := by
  obtain ⟨D0, hD0, d0⟩ := wSub_single2 ν R c hν hR hc
  refine ⟨2 * D0, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg j l
  have hμ1 : 0 ≤ μ + 1 := by linarith
  have hμ'1 : 0 ≤ μ' + 1 := by linarith
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  have hμ1_gt : -(1 / 4) < μ + 1 := by linarith
  have hμ'1_gt : -(1 / 4) < μ' + 1 := by linarith
  have hsub_eq : |(μ + 1) - (μ' + 1)| = |μ - μ'| := by ring_nf
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hX0_1 := w10_X0_eq (μ := μ) hν hR hc hg
  have hX0_2 := w10_X0_eq (μ := μ') hν hR hc hg
  set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hV3 : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ, ContDiffOn ℝ 3 (sepWre ν m T τ) U := fun m hm τ =>
    (w112_smoothV hν hm hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hX3 : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ, ContDiffOn ℝ 3 (wardX0 ν m R c g τ) U := by
    intro m hm τ
    rw [w10_X0_eq (μ := m) hν hR hc hg]
    have e : sepX0 ν m T τ = fun z => sepWre ν m T τ z - sepWre ν (m + 1) T τ z :=
      funext fun z => sepX0_eq_sub ν m T τ z
    rw [e]
    exact (hV3 m hm τ).sub (hV3 (m + 1) (by linarith) τ)
  have hPd2_1 := w112_meas_pd2 (wardX0_measurable_of_measurable ν μ R c g hg.measurable) hUo
    (hX3 μ hμ_gt) j l
  have hPd2_2 := w112_meas_pd2 (wardX0_measurable_of_measurable ν μ' R c g hg.measurable) hUo
    (hX3 μ' hμ'_gt) j l
  have hread : wardYoungRead ν R
      (fun τ y => physPd2 (wardX0 ν μ R c g τ) j l y - physPd2 (wardX0 ν μ' R c g τ) j l y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ U then physPd2 (wardX0 ν μ R c g τ) j l y else 0) -
          (if y ∈ U then physPd2 (wardX0 ν μ' R c g τ) j l y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  have b1 := d0 μ μ' hμ hμ' g hg j l
  have b2 := d0 (μ + 1) (μ' + 1) hμ1 hμ'1 g hg j l
  rw [hsub_eq] at b2
  have hD_mu : 0 ≤ D0 * |μ - μ'| := mul_nonneg hD0 (abs_nonneg _)
  refine w10_young_of_sum
    (A := fun τ y => physPd2 (sepWre ν μ T τ) j l y - physPd2 (sepWre ν μ' T τ) j l y)
    (B := fun τ y => physPd2 (sepWre ν (μ + 1) T τ) j l y - physPd2 (sepWre ν (μ' + 1) T τ) j l y)
    ?_ b1 b2 hD_mu hD_mu (by linarith) ?_
  · rw [hread]
    exact (w10_read_meas (hPd2_1.sub hPd2_2)).aestronglyMeasurable
  · refine w10_read_dom hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hdecomp : ∀ (m : ℝ), -(1 / 4) < m →
        physPd2 (wardX0 ν m R c g τ) j l y =
          physPd2 (sepWre ν m T τ) j l y - physPd2 (sepWre ν (m + 1) T τ) j l y := by
      intro m hm
      have hm1 : -(1 / 4) < m + 1 := by linarith
      have hX0_m := w10_X0_eq (μ := m) hν hR hc hg
      have hsub := WardCalc.physPd2_sum_pt (A := sepWre ν m T τ)
        (B := fun z => -sepWre ν (m + 1) T τ z) (C := wardX0 ν m R c g τ) hUo
        (hV3 m hm τ) ((hV3 (m + 1) hm1 τ).neg)
        (fun z _ => by rw [hX0_m, sepX0_eq_sub, sub_eq_add_neg]) hyU j l
      have hneg : physPd2 (fun z => -sepWre ν (m + 1) T τ z) j l y =
          -physPd2 (sepWre ν (m + 1) T τ) j l y := by
        have h0 := WardCalc.physPd2_sum_pt (A := sepWre ν (m + 1) T τ)
          (B := fun z => -sepWre ν (m + 1) T τ z) (C := fun _ => 0) hUo
          (hV3 (m + 1) hm1 τ) ((hV3 (m + 1) hm1 τ).neg) (fun z _ => (add_neg_cancel _).symm) hyU j l
        have hc0 : physPd2 (fun _ : Space => (0 : Space)) j l y = 0 := by
          simp [physPd2, physPd]
        rw [hc0] at h0
        exact eq_neg_of_add_eq_zero_right h0.symm
      rw [hsub, hneg, ← sub_eq_add_neg]
    rw [hdecomp μ hμ_gt, hdecomp μ' hμ'_gt]
    have heq : (physPd2 (sepWre ν μ T τ) j l y - physPd2 (sepWre ν (μ + 1) T τ) j l y) -
        (physPd2 (sepWre ν μ' T τ) j l y - physPd2 (sepWre ν (μ' + 1) T τ) j l y) =
        (physPd2 (sepWre ν μ T τ) j l y - physPd2 (sepWre ν μ' T τ) j l y) -
          (physPd2 (sepWre ν (μ + 1) T τ) j l y - physPd2 (sepWre ν (μ' + 1) T τ) j l y) := by
      abel
    rw [heq]
    exact norm_sub_le _ _

/-- Differentiability and bounds of the first and second partials of
`Ψ_{X₀,μ}(ϱ y, y_2) - Ψ_{X₀,μ'}(ϱ y, y_2)`. -/
theorem w112_psiSub_jet {ν μ μ' R c : ℝ} {g : Chart → Ten3}
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : y ∈ youngOpen ν R) :
    DifferentiableAt ℝ
        (fun x : Space =>
          outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ x) (x 2)) y ∧
      (∀ l : Fin 3,
        DifferentiableAt ℝ
          (fun x : Space =>
            w112_sd1
              (fun x' : Space =>
                outPrim (wardX0 ν μ R c g) τ (ϱ x') (x' 2) -
                  outPrim (wardX0 ν μ' R c g) τ (ϱ x') (x' 2)) l x) y ∧
        |w112_sd1
            (fun x : Space =>
              outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2) -
                outPrim (wardX0 ν μ' R c g) τ (ϱ x) (x 2)) l y| ≤
          2 * ϱ y * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) ∧
      (∀ j l : Fin 3,
        |w112_sd2
            (fun x : Space =>
              outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2) -
                outPrim (wardX0 ν μ' R c g) τ (ϱ x) (x 2)) j l y| ≤
          4 * ϱ y * ‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ +
            4 * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) := by
  set Z₁ : Space → Space := wardX0 ν μ R c g τ
  set Z₂ : Space → Space := wardX0 ν μ' R c g τ
  set Z : Space → Space := fun x => Z₁ x - Z₂ x
  set Ψ₁ : Space → ℝ := fun x => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)
  set Ψ₂ : Space → ℝ := fun x => outPrim (wardX0 ν μ' R c g) τ (ϱ x) (x 2)
  set Ψ : Space → ℝ := fun x => Ψ₁ x - Ψ₂ x
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hZ₁ : DifferentiableAt ℝ Z₁ y :=
    ((w2_smooth hν hR hc hμ hg τ).contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
  have hZ₂ : DifferentiableAt ℝ Z₂ y :=
    ((w2_smooth hν hR hc hμ' hg τ).contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
  have hZ : DifferentiableAt ℝ Z y := hZ₁.sub hZ₂
  have hΨd : DifferentiableAt ℝ Ψ y :=
    (w2_psi_hasFDeriv hν hR hc hμ hg τ hy).differentiableAt.sub
      (w2_psi_hasFDeriv hν hR hc hμ' hg τ hy).differentiableAt
  have hy0 : |y 0| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have hy1 : |y 1| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  have hρ0 : 0 ≤ ϱ y := ϱ_nonneg y
  have hd_ab : ∀ a b : Fin 3, HasFDerivAt (fun x : Space => x a * Z x b)
      (y a • ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) +
        Z y b • (EuclideanSpace.proj a : Space →L[ℝ] ℝ)) y :=
    fun a b => w112_hasFDerivAt_coord_mul hZ a b
  have hpdZ : ∀ j : Fin 3, physPd Z j y = physPd Z₁ j y - physPd Z₂ j y := fun j => by
    unfold physPd Z
    rw [fderiv_fun_sub hZ₁ hZ₂, sub_apply]
  have hbd_ab : ∀ (a : Fin 3), |y a| ≤ ϱ y → ∀ (b j : Fin 3),
      |(y a • ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) +
        Z y b • (EuclideanSpace.proj a : Space →L[ℝ] ℝ)) (coordinateVector j)| ≤
        ϱ y * ‖physPd Z j y‖ + ‖Z y‖ := by
    intro a hya b j
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, EuclideanSpace.proj,
      PiLp.proj_apply, smul_eq_mul]
    have h1 : |y a * physPd Z j y b| ≤ ϱ y * ‖physPd Z j y‖ := by
      rw [abs_mul]
      exact mul_le_mul hya (wyl_abs_apply_le _ b) (abs_nonneg _) hρ0
    have h2 : |Z y b * coordinateVector j a| ≤ ‖Z y‖ := by
      rw [abs_mul]
      calc |Z y b| * |coordinateVector j a| ≤ ‖Z y‖ * 1 :=
            mul_le_mul (wyl_abs_apply_le _ b) (w112_coord_abs_le j a) (abs_nonneg _) (norm_nonneg _)
        _ = ‖Z y‖ := mul_one _
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hsd1_eq : ∀ (l : Fin 3) {x : Space}, x ∈ youngOpen ν R →
      w112_sd1 Ψ l x =
        (x 0 * Z x 2) * coordinateVector l 0 + (x 1 * Z x 2) * coordinateVector l 1 -
          ((x 0 * Z x 0) * coordinateVector l 2 + (x 1 * Z x 1) * coordinateVector l 2) := by
    intro l x hx
    have hd1 : DifferentiableAt ℝ Ψ₁ x :=
      (w2_psi_hasFDeriv hν hR hc hμ hg τ hx).differentiableAt
    have hd2 : DifferentiableAt ℝ Ψ₂ x :=
      (w2_psi_hasFDeriv hν hR hc hμ' hg τ hx).differentiableAt
    have hsub : w112_sd1 Ψ l x = w112_sd1 Ψ₁ l x - w112_sd1 Ψ₂ l x := by
      unfold w112_sd1 Ψ
      rw [fderiv_fun_sub hd1 hd2, sub_apply]
    rw [hsub, w112_psi_sd1_eq hν hR hc hμ hg τ l hx, w112_psi_sd1_eq hν hR hc hμ' hg τ l hx]
    simp only [Z, Z₁, Z₂, PiLp.sub_apply]
    ring
  have hstep : ∀ l : Fin 3,
      DifferentiableAt ℝ (fun x => w112_sd1 Ψ l x) y ∧
      |w112_sd1 Ψ l y| ≤ 2 * ϱ y * ‖Z y‖ ∧
      ∀ j : Fin 3, |w112_sd2 Ψ j l y| ≤ 4 * ϱ y * ‖physPd Z₁ j y - physPd Z₂ j y‖ + 4 * ‖Z y‖ := by
    intro l
    have hev : (fun x => w112_sd1 Ψ l x) =ᶠ[𝓝 y] fun x =>
        (x 0 * Z x 2) * coordinateVector l 0 + (x 1 * Z x 2) * coordinateVector l 1 -
          ((x 0 * Z x 0) * coordinateVector l 2 + (x 1 * Z x 1) * coordinateVector l 2) := by
      filter_upwards [hUo.mem_nhds hy] with x hx
      exact hsd1_eq l hx
    have hd := (((hd_ab 0 2).mul_const (coordinateVector l 0)).add
      ((hd_ab 1 2).mul_const (coordinateVector l 1))).sub
      (((hd_ab 0 0).mul_const (coordinateVector l 2)).add
        ((hd_ab 1 1).mul_const (coordinateVector l 2)))
    have hd' := hd.congr_of_eventuallyEq hev
    refine ⟨hd'.differentiableAt, ?_, fun j => ?_⟩
    · rw [hsd1_eq l hy]
      have z0 := wyl_abs_apply_le (Z y) 0
      have z1 := wyl_abs_apply_le (Z y) 1
      have z2 := wyl_abs_apply_le (Z y) 2
      fin_cases l <;> simp [coordinateVector]
      · exact (mul_le_mul hy0 z2 (abs_nonneg _) hρ0).trans (by nlinarith [norm_nonneg (Z y)])
      · exact (mul_le_mul hy1 z2 (abs_nonneg _) hρ0).trans (by nlinarith [norm_nonneg (Z y)])
      · refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_neg, abs_mul, abs_mul]
        have m0 := mul_le_mul hy0 z0 (abs_nonneg _) hρ0
        have m1 := mul_le_mul hy1 z1 (abs_nonneg _) hρ0
        linarith
    · unfold w112_sd2
      rw [hd'.fderiv, ← hpdZ j]
      simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
      have b02 := hbd_ab 0 hy0 2 j
      have b12 := hbd_ab 1 hy1 2 j
      have b00 := hbd_ab 0 hy0 0 j
      have b11 := hbd_ab 1 hy1 1 j
      have c0 := w112_coord_abs_le l 0
      have c1 := w112_coord_abs_le l 1
      have c2 := w112_coord_abs_le l 2
      set B := ϱ y * ‖physPd Z j y‖ + ‖Z y‖
      have hB0 : 0 ≤ B := by positivity
      have hcm : ∀ {c d : ℝ}, |c| ≤ 1 → |d| ≤ B → |c * d| ≤ B := fun {c d} hc hd => by
        rw [abs_mul]
        calc |c| * |d| ≤ 1 * B := mul_le_mul hc hd (abs_nonneg _) zero_le_one
          _ = B := one_mul B
      calc _ ≤ (B + B) + (B + B) := by
            refine (abs_sub _ _).trans (add_le_add ?_ ?_)
            · exact (abs_add_le _ _).trans (add_le_add (hcm c0 b02) (hcm c1 b12))
            · exact (abs_add_le _ _).trans (add_le_add (hcm c2 b00) (hcm c2 b11))
        _ = 4 * ϱ y * ‖physPd Z j y‖ + 4 * ‖Z y‖ := by simp only [B]; ring
  exact ⟨hΨd, fun l => ⟨(hstep l).1, (hstep l).2.1⟩, fun j l => (hstep l).2.2 j⟩

lemma w112_physPd_sub_eq {U : Set Space} (hUo : IsOpen U) {F₁ F₂ : Space → Space}
    (hF₁ : ContDiffOn ℝ 2 F₁ U) (hF₂ : ContDiffOn ℝ 2 F₂ U)
    (k : Fin 3) {y : Space} (hy : y ∈ U) :
    physPd (fun x => F₁ x - F₂ x) k y = physPd F₁ k y - physPd F₂ k y := by
  have hd1 : DifferentiableAt ℝ F₁ y :=
    (hF₁.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ F₂ y :=
    (hF₂.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by norm_num)
  show fderiv ℝ (fun x => F₁ x - F₂ x) y (coordinateVector k) =
    fderiv ℝ F₁ y (coordinateVector k) - fderiv ℝ F₂ y (coordinateVector k)
  rw [fderiv_fun_sub hd1 hd2, sub_apply]

lemma w112_physPd2_sub_eq {U : Set Space} (hUo : IsOpen U) {F₁ F₂ : Space → Space}
    (hF₁ : ContDiffOn ℝ 2 F₁ U) (hF₂ : ContDiffOn ℝ 2 F₂ U)
    (j l : Fin 3) {y : Space} (hy : y ∈ U) :
    physPd2 (fun x => F₁ x - F₂ x) j l y = physPd2 F₁ j l y - physPd2 F₂ j l y := by
  have hF₁' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) F₁ U := hF₁
  have hF₂' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) F₂ U := hF₂
  have hd1 : DifferentiableAt ℝ (physPd F₁ l) y := by
    have hf1 : ContDiffOn ℝ 1 (fderiv ℝ F₁) U :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hF₁').2.2
    have hpd1 : ContDiffOn ℝ 1 (physPd F₁ l) U :=
      (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).contDiff.comp_contDiffOn hf1
    exact (hpd1.contDiffAt (hUo.mem_nhds hy)).differentiableAt one_ne_zero
  have hd2 : DifferentiableAt ℝ (physPd F₂ l) y := by
    have hf2 : ContDiffOn ℝ 1 (fderiv ℝ F₂) U :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hF₂').2.2
    have hpd2 : ContDiffOn ℝ 1 (physPd F₂ l) U :=
      (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).contDiff.comp_contDiffOn hf2
    exact (hpd2.contDiffAt (hUo.mem_nhds hy)).differentiableAt one_ne_zero
  have hev : physPd (fun x => F₁ x - F₂ x) l =ᶠ[𝓝 y] fun w => physPd F₁ l w - physPd F₂ l w :=
    Filter.mem_of_superset (hUo.mem_nhds hy) fun w hw => w112_physPd_sub_eq hUo hF₁ hF₂ l hw
  change fderiv ℝ (physPd (fun x => F₁ x - F₂ x) l) y (coordinateVector j) =
    fderiv ℝ (physPd F₁ l) y (coordinateVector j) - fderiv ℝ (physPd F₂ l) y (coordinateVector j)
  rw [hev.fderiv_eq, fderiv_fun_sub hd1 hd2, sub_apply]

/-- Pointwise bound on `‖physPd2 (wardX ν μ ...) j l y - physPd2 (wardX ν μ' ...) j l y‖` on
`R√ν ≤ ϱ y`. -/
theorem w112_wardXSub_pd2_pt_bound {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    {C₁ C₂ : ℝ} (_hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcut : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      |χy (ν * age R y)| ≤ C₁ ∧
        (∀ k : Fin 3, |w112_sd1 (fun x => χy (ν * age R x)) k y| ≤ C₁) ∧
        (∀ j l : Fin 3, |w112_sd2 (fun x => χy (ν * age R x)) j l y| ≤ C₁))
    (hw2a_bd : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      |w2a ν R χy (ϱ y)| ≤ C₂ ∧
        (∀ k : Fin 3, |w112_sd1 (fun x => w2a ν R χy (ϱ x)) k y| ≤ C₂) ∧
        (∀ j l : Fin 3, |w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y| ≤ C₂))
    (hw2a_gt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
      w2a ν R χy (ϱ y) = 0 ∧
        (∀ k : Fin 3, w112_sd1 (fun x => w2a ν R χy (ϱ x)) k y = 0) ∧
        (∀ j l : Fin 3, w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y = 0))
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j l : Fin 3)
    {y : Space} (hy : R * Real.sqrt ν ≤ ϱ y) :
    ‖physPd2 (wardX ν μ R c χy g τ) j l y - physPd2 (wardX ν μ' R c χy g τ) j l y‖ ≤
      C₁ * ‖physPd2 (wardX0 ν μ R c g τ) j l y - physPd2 (wardX0 ν μ' R c g τ) j l y‖ +
        (C₁ + 4 * C₂ * (R * Real.sqrt (5 * ν / 4))) *
          ‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ +
        C₁ * ‖physPd (wardX0 ν μ R c g τ) l y - physPd (wardX0 ν μ' R c g τ) l y‖ +
        (C₁ + 4 * C₂ + 4 * C₂ * (R * Real.sqrt (5 * ν / 4))) *
          ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ +
        C₂ * w2NSub ν μ μ' R c (R * Real.sqrt (5 * ν / 4)) g τ y := by
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  set Z₁ : Space → Space := wardX0 ν μ R c g τ
  set Z₂ : Space → Space := wardX0 ν μ' R c g τ
  set Z : Space → Space := fun x => Z₁ x - Z₂ x
  set φ₁ : Space → ℝ := fun x => χy (ν * age R x)
  set φ₂ : Space → ℝ := fun x => w2a ν R χy (ϱ x)
  set Ψ₁ : Space → ℝ := fun x => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)
  set Ψ₂ : Space → ℝ := fun x => outPrim (wardX0 ν μ' R c g) τ (ϱ x) (x 2)
  set Ψ : Space → ℝ := fun x => Ψ₁ x - Ψ₂ x
  set G : Space → Space := fun x => Ψ x • (coordinateVector 2 : Space)
  have hne : ∀ w ∈ youngOpen ν R, ϱ w ≠ 0 := fun w hw => by
    have hp := t9_thr_pos hν hR
    have hw' : R * Real.sqrt (5 * ν / 6) < ϱ w := hw
    linarith
  have hϱ2 : ContDiffOn ℝ 2 (fun w : Space => ϱ w) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun w hw => t9_not_axis hν hR hw)
  have hage2 : ContDiffOn ℝ 2 (fun w : Space => ν * age R w) (youngOpen ν R) :=
    contDiffOn_const.mul
      (ContDiffOn.div contDiffOn_const (hϱ2.pow 2) (fun w hw => pow_ne_zero 2 (hne w hw)))
  have hφ₁c : ContDiffOn ℝ 2 φ₁ (youngOpen ν R) :=
    (hχy.smooth.of_le (WithTop.coe_le_coe.2 le_top)).comp_contDiffOn hage2
  have hdχ2 : ContDiff ℝ 2 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
      (WithTop.coe_le_coe.2 le_top)
  have hφ₂c : ContDiffOn ℝ 2 φ₂ (youngOpen ν R) := by
    have h1 : ContDiffOn ℝ 2 (fun w : Space => ν * (R ^ 2 / ϱ w ^ 2)) (youngOpen ν R) := hage2
    have hdA := hdχ2.comp_contDiffOn h1
    have hK : ContDiffOn ℝ 2 (fun w : Space => -2 * ν * R ^ 2 / ϱ w ^ 3) (youngOpen ν R) :=
      ContDiffOn.div contDiffOn_const (hϱ2.pow 3) (fun w hw => pow_ne_zero 3 (hne w hw))
    exact (hdA.mul hK).div hϱ2 hne
  have hZ₁c3 : ContDiffOn ℝ 3 Z₁ (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hZ₂c3 : ContDiffOn ℝ 3 Z₂ (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ' hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hZ₁c2 : ContDiffOn ℝ 2 Z₁ (youngOpen ν R) := hZ₁c3.of_le (by norm_num)
  have hZ₂c2 : ContDiffOn ℝ 2 Z₂ (youngOpen ν R) := hZ₂c3.of_le (by norm_num)
  have hZc2 : ContDiffOn ℝ 2 Z (youngOpen ν R) := hZ₁c2.sub hZ₂c2
  have hΨ₁c2 : ContDiffOn ℝ 2 Ψ₁ (youngOpen ν R) :=
    (xc_outPrim_c3 hν hR hZ₁c3 (w2_hdr hν hR hc hμ hg τ)).of_le (by norm_num)
  have hΨ₂c2 : ContDiffOn ℝ 2 Ψ₂ (youngOpen ν R) :=
    (xc_outPrim_c3 hν hR hZ₂c3 (w2_hdr hν hR hc hμ' hg τ)).of_le (by norm_num)
  have hΨc2 : ContDiffOn ℝ 2 Ψ (youngOpen ν R) := hΨ₁c2.sub hΨ₂c2
  have hGc2 : ContDiffOn ℝ 2 G (youngOpen ν R) := hΨc2.smul contDiffOn_const
  have hF₁c2 : ContDiffOn ℝ 2 (fun x => φ₁ x • Z x) (youngOpen ν R) := hφ₁c.smul hZc2
  have hF₂c2 : ContDiffOn ℝ 2 (fun x => φ₂ x • G x) (youngOpen ν R) := hφ₂c.smul hGc2
  have hX₁c2 : ContDiffOn ℝ 2 (wardX ν μ R c χy g τ) (youngOpen ν R) :=
    (((wardXDiff_proved ν μ R c χy hχy hν hR hc hμ g hg τ).1).mono
      (fun w hw => t9_not_axis hν hR hw)).of_le (by norm_num)
  have hX₂c2 : ContDiffOn ℝ 2 (wardX ν μ' R c χy g τ) (youngOpen ν R) :=
    (((wardXDiff_proved ν μ' R c χy hχy hν hR hc hμ' g hg τ).1).mono
      (fun w hw => t9_not_axis hν hR hw)).of_le (by norm_num)
  have hX_sub_eq : (fun x => wardX ν μ R c χy g τ x - wardX ν μ' R c χy g τ x) =
      fun x => φ₁ x • Z x + φ₂ x • G x := by
    funext x
    rw [wardX_eq_cut_add_corr, wardX_eq_cut_add_corr, wardStreamCorr_eq, wardStreamCorr_eq,
      mul_smul, mul_smul]
    simp only [Z, G, Ψ, sub_smul, smul_sub]
    abel
  have hadd := w112_physPd2_add_norm_le hUo hF₁c2 hF₂c2 j l hyU
  rw [← hX_sub_eq, w112_physPd2_sub_eq hUo hX₁c2 hX₂c2 j l hyU] at hadd
  have hsm1 := w112_physPd2_smul_norm_le_c2 hUo hφ₁c hZc2 j l hyU
  rw [w112_physPd2_sub_eq hUo hZ₁c2 hZ₂c2 j l hyU,
    w112_physPd_sub_eq hUo hZ₁c2 hZ₂c2 j hyU,
    w112_physPd_sub_eq hUo hZ₁c2 hZ₂c2 l hyU] at hsm1
  have hsm2 := w112_physPd2_smul_norm_le_c2 hUo hφ₂c hGc2 j l hyU
  obtain ⟨hG0, hG1, hG2⟩ := w112_smul_e2_jets hUo hΨc2 hyU
  rw [hG0, hG1 j, hG1 l, hG2 j l] at hsm2
  obtain ⟨hc0, hc1, hc2⟩ := hcut y hy
  have hb1 : ‖physPd2 (fun x => φ₁ x • Z x) j l y‖ ≤
      C₁ * ‖physPd2 Z₁ j l y - physPd2 Z₂ j l y‖ +
        C₁ * ‖physPd Z₁ j y - physPd Z₂ j y‖ +
        C₁ * ‖physPd Z₁ l y - physPd Z₂ l y‖ +
        C₁ * ‖Z y‖ := by
    refine hsm1.trans ?_
    have e1 := mul_le_mul_of_nonneg_right hc0 (norm_nonneg (physPd2 Z₁ j l y - physPd2 Z₂ j l y))
    have e2 := mul_le_mul_of_nonneg_right (hc1 l) (norm_nonneg (physPd Z₁ j y - physPd Z₂ j y))
    have e3 := mul_le_mul_of_nonneg_right (hc1 j) (norm_nonneg (physPd Z₁ l y - physPd Z₂ l y))
    have e4 := mul_le_mul_of_nonneg_right (hc2 j l) (norm_nonneg (Z y))
    linarith
  have hb2 : ‖physPd2 (fun x => φ₂ x • G x) j l y‖ ≤
      (4 * C₂ * r2) * ‖physPd Z₁ j y - physPd Z₂ j y‖ +
        (4 * C₂ + 4 * C₂ * r2) * ‖Z y‖ +
        C₂ * w2NSub ν μ μ' R c r2 g τ y := by
    refine hsm2.trans ?_
    by_cases hle : ϱ y ≤ r2
    · obtain ⟨hw0, hw1, hw2⟩ := hw2a_bd y hy
      obtain ⟨_, hψ1, hψ2⟩ := w112_psiSub_jet hν hR hc hμ hμ' hg τ hyU
      have hN : w2NSub ν μ μ' R c r2 g τ y = |Ψ y| := by
        unfold w2NSub Ψ Ψ₁ Ψ₂; simp only [hle, ↓reduceIte]
      rw [hN]
      have hρ0 : 0 ≤ ϱ y := ϱ_nonneg y
      have hp2 : |w112_sd2 Ψ j l y| ≤
          4 * r2 * ‖physPd Z₁ j y - physPd Z₂ j y‖ + 4 * ‖Z y‖ := by
        refine (hψ2 j l).trans ?_
        nlinarith [norm_nonneg (physPd Z₁ j y - physPd Z₂ j y)]
      have hp1l : |w112_sd1 Ψ l y| ≤ 2 * r2 * ‖Z y‖ := by
        refine (hψ1 l).2.trans ?_
        nlinarith [norm_nonneg (Z y)]
      have hp1j : |w112_sd1 Ψ j y| ≤ 2 * r2 * ‖Z y‖ := by
        refine (hψ1 j).2.trans ?_
        nlinarith [norm_nonneg (Z y)]
      have m1 : |φ₂ y| * |w112_sd2 Ψ j l y| ≤
          C₂ * (4 * r2 * ‖physPd Z₁ j y - physPd Z₂ j y‖ + 4 * ‖Z y‖) :=
        mul_le_mul hw0 hp2 (abs_nonneg _) hC₂
      have m2 : |w112_sd1 φ₂ j y| * |w112_sd1 Ψ l y| ≤ C₂ * (2 * r2 * ‖Z y‖) :=
        mul_le_mul (hw1 j) hp1l (abs_nonneg _) hC₂
      have m3 : |w112_sd1 φ₂ l y| * |w112_sd1 Ψ j y| ≤ C₂ * (2 * r2 * ‖Z y‖) :=
        mul_le_mul (hw1 l) hp1j (abs_nonneg _) hC₂
      have m4 : |w112_sd2 φ₂ j l y| * |Ψ y| ≤ C₂ * |Ψ y| :=
        mul_le_mul_of_nonneg_right (hw2 j l) (abs_nonneg _)
      linarith
    · obtain ⟨hz0, hz1, hz2⟩ := hw2a_gt y (not_le.1 hle)
      change |w2a ν R χy (ϱ y)| * _ + |w112_sd1 (fun x => w2a ν R χy (ϱ x)) j y| * _ +
        |w112_sd1 (fun x => w2a ν R χy (ϱ x)) l y| * _ +
        |w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y| * _ ≤ _
      rw [hz0, hz1 j, hz1 l, hz2 j l]
      simp only [abs_zero, zero_mul, add_zero]
      have hZ0 := norm_nonneg (Z y)
      have hZj := norm_nonneg (physPd Z₁ j y - physPd Z₂ j y)
      have hN0 := w2NSub_nonneg ν μ μ' R c r2 g τ y
      positivity
  linarith

/-- **`D²X_μ - D²X_{μ'} ∈ Y₂` on the young support** (`PartIII-b:C/cont/WE/2`). -/
theorem wardD2XSubYoungL2_proved : WardD2XSubYoungL2 := by
  classical
  intro a b ν R c χy ha _ hχy hν hR hc
  obtain ⟨CX0, hCX0, hX0⟩ := wSub_wardX0YoungL2 ν R c hν hR hc
  obtain ⟨CD2, hCD2, hD2⟩ := wSub_wardD2X0YoungL2 ν R c hν hR hc
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiSubBd hν hR hc r2
  obtain ⟨C₁, hC₁, hcut⟩ := w112_cut_jet2_bound hχy hν hR
  obtain ⟨C₂, hC₂, hw2a_bd, hw2a_gt⟩ := w112_w2a_jet2_bound hχy hν hR
  set a1 : ℝ := C₁
  set a2 : ℝ := C₁ + 4 * C₂ * r2
  set a3 : ℝ := C₁
  set a4 : ℝ := C₁ + 4 * C₂ + 4 * C₂ * r2
  set a5 : ℝ := C₂
  have ha1 : 0 ≤ a1 := hC₁
  have ha2 : 0 ≤ a2 := by positivity
  have ha3 : 0 ≤ a3 := hC₁
  have ha4 : 0 ≤ a4 := by positivity
  have ha5 : 0 ≤ a5 := hC₂
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  refine ⟨a1 * CD2 + a2 * CX0 + a3 * CX0 + a4 * CX0 + a5 * K,
    fun μ hμ_ab μ' hμ'_ab g hg j l => ?_⟩
  have hμ : 0 ≤ μ := by linarith [hμ_ab.1]
  have hμ' : 0 ≤ μ' := by linarith [hμ'_ab.1]
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  obtain ⟨hX0_val, hX0_pd⟩ := hX0 μ μ' hμ hμ' g hg
  have hD2_jl := hD2 μ μ' hμ hμ' g hg j l
  have hCD2_mu : 0 ≤ CD2 * |μ - μ'| := mul_nonneg hCD2 (abs_nonneg _)
  have hCX0_mu : 0 ≤ CX0 * |μ - μ'| := mul_nonneg hCX0 (abs_nonneg _)
  have hK_mu : 0 ≤ K * |μ - μ'| := mul_nonneg hK (abs_nonneg _)
  have b1 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a1 * wardYoungRead ν R
        (fun τ y => physPd2 (wardX0 ν μ R c g τ) j l y - physPd2 (wardX0 ν μ' R c g τ) j l y) q)
      (a1 * (CD2 * |μ - μ'|)) := by
    have := (wyl_bd_of_young hD2_jl).const_mul a1
    rwa [abs_of_nonneg ha1, max_eq_left hCD2_mu] at this
  have b2 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a2 * wardYoungRead ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q)
      (a2 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hX0_pd j)).const_mul a2
    rwa [abs_of_nonneg ha2, max_eq_left hCX0_mu] at this
  have b3 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a3 * wardYoungRead ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) l y - physPd (wardX0 ν μ' R c g τ) l y) q)
      (a3 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hX0_pd l)).const_mul a3
    rwa [abs_of_nonneg ha3, max_eq_left hCX0_mu] at this
  have b4 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a4 * wardYoungRead ν R
        (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q)
      (a4 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young hX0_val).const_mul a4
    rwa [abs_of_nonneg ha4, max_eq_left hCX0_mu] at this
  have b5 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a5 * wardYoungRead ν R (w2PhiSub ν μ μ' R c r2 g) q)
      (a5 * (K * |μ - μ'|)) := by
    simpa [abs_of_nonneg ha5] using (hΨ μ μ' hμ hμ' g hg).const_mul a5
  have hc1 : 0 ≤ a1 * (CD2 * |μ - μ'|) := mul_nonneg ha1 hCD2_mu
  have hc2 : 0 ≤ a2 * (CX0 * |μ - μ'|) := mul_nonneg ha2 hCX0_mu
  have hc3 : 0 ≤ a3 * (CX0 * |μ - μ'|) := mul_nonneg ha3 hCX0_mu
  have hc4 : 0 ≤ a4 * (CX0 * |μ - μ'|) := mul_nonneg ha4 hCX0_mu
  have hc5 : 0 ≤ a5 * (K * |μ - μ'|) := mul_nonneg ha5 hK_mu
  have b12 := b1.add b2 hc1 hc2
  have b123 := b12.add b3 (add_nonneg hc1 hc2) hc3
  have b1234 := b123.add b4 (add_nonneg (add_nonneg hc1 hc2) hc3) hc4
  have b12345 := b1234.add b5 (add_nonneg (add_nonneg (add_nonneg hc1 hc2) hc3) hc4) hc5
  have hXm1 := w3_wardX_measurable ν μ R c hχy hg
  have hXm2 := w3_wardX_measurable ν μ' R c hχy hg
  have hX3_1 : ∀ τ, ContDiffOn ℝ 3 (wardX ν μ R c χy g τ) (youngOpen ν R) :=
    fun τ => ((wardXDiff_proved ν μ R c χy hχy hν hR hc hμ_gt g hg τ).1).mono
      (fun y hy => t9_not_axis hν hR hy)
  have hX3_2 : ∀ τ, ContDiffOn ℝ 3 (wardX ν μ' R c χy g τ) (youngOpen ν R) :=
    fun τ => ((wardXDiff_proved ν μ' R c χy hχy hν hR hc hμ'_gt g hg τ).1).mono
      (fun y hy => t9_not_axis hν hR hy)
  have hPd2m1 := w112_meas_pd2 hXm1 hUo hX3_1 j l
  have hPd2m2 := w112_meas_pd2 hXm2 hUo hX3_2 j l
  have hread : wardYoungRead ν R
      (fun τ y => physPd2 (wardX ν μ R c χy g τ) j l y - physPd2 (wardX ν μ' R c χy g τ) j l y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ youngOpen ν R then physPd2 (wardX ν μ R c χy g τ) j l y else 0) -
          (if y ∈ youngOpen ν R then physPd2 (wardX ν μ' R c χy g τ) j l y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
    simp [this]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R
        (fun τ y => physPd2 (wardX ν μ R c χy g τ) j l y - physPd2 (wardX ν μ' R c χy g τ) j l y))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas (hPd2m1.sub hPd2m2)).aestronglyMeasurable
  refine ⟨hFm, (eLpNorm_mono_real (fun q => ?_)).trans
    (b12345.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))⟩
  rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos _ hs]
      have r1 := wyl_youngRead_nonneg ν R
        (fun τ y => physPd2 (wardX0 ν μ R c g τ) j l y - physPd2 (wardX0 ν μ' R c g τ) j l y) q
      have r2' := wyl_youngRead_nonneg ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q
      have r3 := wyl_youngRead_nonneg ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) l y - physPd (wardX0 ν μ' R c g τ) l y) q
      have r4 := wyl_youngRead_nonneg ν R
        (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q
      have r5 := wyl_youngRead_nonneg ν R (w2PhiSub ν μ μ' R c r2 g) q
      positivity
    · rw [wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq, w2PhiSub_norm]
      set τ := NearInst.chartTau R q
      set y := NearInst.chartY R q
      have hy : R * Real.sqrt ν ≤ ϱ y := wyl_young_ϱ hν hR hs hq
      have hpt := w112_wardXSub_pd2_pt_bound hχy hν hR hc hμ_gt hμ'_gt hC₁ hC₂ hcut hw2a_bd
        hw2a_gt hg τ j l hy
      have hinv : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hpt hinv
      linarith
  · have hqS : q ∉ wardYoungSet ν := hq
    have h0 : wardYoungRead ν R
        (fun τ y => physPd2 (wardX ν μ R c χy g τ) j l y -
          physPd2 (wardX ν μ' R c χy g τ) j l y) q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem hqS]
    rw [h0]
    have r1 := wyl_youngRead_nonneg ν R
      (fun τ y => physPd2 (wardX0 ν μ R c g τ) j l y - physPd2 (wardX0 ν μ' R c g τ) j l y) q
    have r2' := wyl_youngRead_nonneg ν R
      (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q
    have r3 := wyl_youngRead_nonneg ν R
      (fun τ y => physPd (wardX0 ν μ R c g τ) l y - physPd (wardX0 ν μ' R c g τ) l y) q
    have r4 := wyl_youngRead_nonneg ν R
      (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q
    have r5 := wyl_youngRead_nonneg ν R (w2PhiSub ν μ μ' R c r2 g) q
    positivity

end UnforcedLeray.Short.PartIIIb.Concrete
end
