import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YHAdd.Calc

/-!
# Helpers for `wardD2XYoungL2_proved` (1): `D²X₀ ∈ Y₂` on the young support

Source of record: `the November 2 reference manuscript` (73 pages),
3631-3646 (`sep:young`, `j = 2`), 4171-4174, 4194-4196, 5225-5235.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Second derivative of a composition with `w10Re` applied to vectors `u, v`. -/
theorem w112_fderiv2_re {A : Space → (Fin 3 → ℂ)} {U : Set Space} (hUo : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {y : Space} (hy : y ∈ U) (u v : Space) :
    fderiv ℝ (fun w => fderiv ℝ (w10Re ∘ A) w u) y v =
      w10Re (iteratedFDeriv ℝ 2 A y ![v, u]) := by
  have hAy : ContDiffAt ℝ 2 A y := hA.contDiffAt (hUo.mem_nhds hy)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ A) y := hAy.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ A) y := h1.differentiableAt (by norm_num)
  have hAu : HasFDerivAt (fun w => fderiv ℝ A w u) ((fderiv ℝ (fderiv ℝ A) y).flip u) y := by
    have h0 := (hd.clm_apply (differentiableAt_const u)).hasFDerivAt
    have e : fderiv ℝ (fun w => fderiv ℝ A w u) y = (fderiv ℝ (fderiv ℝ A) y).flip u := by
      rw [fderiv_clm_apply hd (differentiableAt_const u)]
      simp
    rwa [e] at h0
  have hRe : HasFDerivAt (fun w => w10Re (fderiv ℝ A w u))
      (w10Re.comp ((fderiv ℝ (fderiv ℝ A) y).flip u)) y :=
    w10Re.hasFDerivAt.comp y hAu
  have hev : (fun w => fderiv ℝ (w10Re ∘ A) w u) =ᶠ[𝓝 y] fun w => w10Re (fderiv ℝ A w u) := by
    filter_upwards [hUo.mem_nhds hy] with w hw
    have hAw : DifferentiableAt ℝ A w :=
      (hA.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by norm_num)
    rw [(w10Re.hasFDerivAt.comp w hAw.hasFDerivAt).fderiv]
    rfl
  have hf := (hRe.congr_of_eventuallyEq hev).fderiv
  have happ := congrArg (fun L : Space →L[ℝ] Space => L v) hf
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at happ
  rw [happ, iteratedFDeriv_two_apply]
  rfl

theorem w112_norm_fderiv2_re {A : Space → (Fin 3 → ℂ)} {U : Set Space} (hUo : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {y : Space} (hy : y ∈ U) (u v : Space) :
    ‖fderiv ℝ (fun w => fderiv ℝ (w10Re ∘ A) w u) y v‖ ≤
      ‖w10Re‖ * (‖iteratedFDeriv ℝ 2 A y‖ * ‖v‖ * ‖u‖) := by
  rw [w112_fderiv2_re hUo hA hy u v]
  refine (w10Re.le_opNorm _).trans ?_
  gcongr
  have h := (iteratedFDeriv ℝ 2 A y).le_opNorm ![v, u]
  simpa [Fin.prod_univ_two, mul_assoc] using h

/-- Second-derivative transformation under an orthogonal equivariance on an invariant open set. -/
theorem w112_fderiv2_rot {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hMo : M * M.transpose = 1)
    (hUinv : ∀ z ∈ U, actM M z ∈ U)
    (hf : ContDiffOn ℝ 2 f U)
    (he : ∀ z ∈ U, f (actM M z) = actM M (f z)) {z0 : Space} (hz0 : z0 ∈ U) (u v : Space) :
    ‖fderiv ℝ (fun z => fderiv ℝ f z u) z0 v‖ =
      ‖fderiv ℝ (fun w => fderiv ℝ f w (actM M u)) (actM M z0) (actM M v)‖ := by
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
  simp only [ContinuousLinearMap.comp_apply, clmOf_apply] at h4
  calc ‖fderiv ℝ g2 z0 v‖ = ‖actM M (fderiv ℝ g2 z0 v)‖ := (norm_actM hMo _).symm
    _ = ‖fderiv ℝ g1 (actM M z0) (actM M v)‖ := by rw [h4]

theorem w112_smoothA {ν m : ℝ} (hν : 0 < ν) (hm : -(1 / 4) < m) {P rOut : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν (m : ℂ) T z τ)
      {y : Space | rOut < ϱ y} :=
  contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν (m : ℂ) rOut P T hν (by simpa using hm) hr hP
    hT hM τ i)

theorem w112_smoothV {ν m : ℝ} (hν : 0 < ν) (hm : -(1 / 4) < m) {P rOut : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sepWre ν m T τ) {y : Space | rOut < ϱ y} := by
  rw [w10_sepWre_eq]
  exact w10Re.contDiff.comp_contDiffOn (w112_smoothA hν hm hr hP hT hM τ)

open scoped Classical in
theorem w112_meas_pd2 {X : ℝ → Space → Space} (hX : Measurable (fun x : ℝ × Space => X x.1 x.2))
    {U : Set Space} (hUo : IsOpen U)
    (hX3 : ∀ τ, ContDiffOn ℝ 3 (X τ) U) (j l : Fin 3) :
    Measurable (fun x : ℝ × Space => if x.2 ∈ U then physPd2 (X x.1) j l x.2 else 0) := by
  have hUm : MeasurableSet U := hUo.measurableSet
  have hd0 : ∀ τ y, y ∈ U → DifferentiableAt ℝ (X τ) y := fun τ y hy =>
    WardCalc.diffAt_of_contDiffOn hUo (hX3 τ) hy
  set F1 : ℝ → Space → Space := fun τ y => if y ∈ U then physPd (X τ) l y else 0
  have hF1m : Measurable (fun x : ℝ × Space => F1 x.1 x.2) := w10_meas_pd hX hUm hd0 l
  have hd1 : ∀ τ y, y ∈ U → DifferentiableAt ℝ (F1 τ) y := by
    intro τ y hy
    have hev : F1 τ =ᶠ[𝓝 y] fun z => physPd (X τ) l z := by
      filter_upwards [hUo.mem_nhds hy] with z hz
      simp [F1, hz]
    exact (WardCalc.differentiableAt_physPd hUo (hX3 τ) hy l).congr_of_eventuallyEq hev
  have hF2m := w10_meas_pd hF1m hUm hd1 j
  have heq : (fun x : ℝ × Space => if x.2 ∈ U then physPd2 (X x.1) j l x.2 else 0) =
      fun x : ℝ × Space => if x.2 ∈ U then physPd (F1 x.1) j x.2 else 0 := by
    funext x
    by_cases hx : x.2 ∈ U
    · simp only [hx, ↓reduceIte]
      have hev : F1 x.1 =ᶠ[𝓝 x.2] fun z => physPd (X x.1) l z := by
        filter_upwards [hUo.mem_nhds hx] with z hz
        simp [F1, hz]
      exact (WardCalc.physPd_congr_pt hev j).symm
    · simp [hx]
  rw [heq]
  exact hF2m

theorem w112_single2 (m : ℝ) (hm : -(1 / 4) < m) (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R)
    (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j l : Fin 3,
      WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R
          (fun τ => physPd2 (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) j l)) C := by
  obtain ⟨C0, hC0, hG⟩ := w10_gtl m hm 2
  set b : ℝ := C0 * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((2 : ℕ) : ℝ) + 3 / 1)
    with hb
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hb0 : 0 ≤ b := mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  refine ⟨‖w10Re‖ * b, mul_nonneg (norm_nonneg _) hb0, ?_⟩
  intro g hg j l
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hT
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hVm := sepWre_measurable ν m hν T hS.measurable
  set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hperV : ∀ τ, sepWre ν m T (τ + 2 * c / R) = sepWre ν m T τ := fun τ =>
    funext (sepWre_periodic ν m _ T hS.periodic τ)
  have hV3 : ∀ τ, ContDiffOn ℝ 3 (sepWre ν m T τ) U := fun τ =>
    (w112_smoothV hν hm hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hPd2 := w112_meas_pd2 hVm hUo hV3 j l
  set N : ℝ → Space → ℝ := fun τ y =>
    ‖if y ∈ U then physPd2 (sepWre ν m T τ) j l y else 0‖ with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := hPd2.norm
  have hread : wardYoungRead ν R (fun τ => physPd2 (sepWre ν m T τ) j l) =
      wardYoungRead ν R (fun τ y => if y ∈ U then physPd2 (sepWre ν m T τ) j l y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  refine ⟨?_, ?_⟩
  · rw [hread]
    exact (w10_read_meas hPd2).aestronglyMeasurable
  have hDom : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤
        ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 2 τ y := by
    intro τ y hy
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrr hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy'
    obtain ⟨M, hMo, hTM, hmer, hMϱ⟩ := w10_rotdatum hAx hρ
    have hmU : meridPt y ∈ U := by
      show R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y)
      rw [w10_varrho_meridPt]; exact hy'
    have hyU : y ∈ U := hy'
    have hV2 : ContDiffOn ℝ 2 (sepWre ν m T τ) U := (hV3 τ).of_le (by norm_num)
    have hA2 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (m : ℂ) T z τ) U :=
      (w112_smoothA hν hm hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
    have hrot := w112_fderiv2_rot hUo hMo
      (fun z hz => by
        show R * Real.sqrt (5 * ν / 6) < ϱ (actM M z)
        rw [hMϱ]; exact hz)
      hV2
      (fun z hz => w10_equivV hν hm hr hP hS hM hMo hTM τ z hz)
      hmU (coordinateVector l) (coordinateVector j)
    rw [hmer] at hrot
    have hNn : N τ (meridPt y) = ‖physPd2 (sepWre ν m T τ) j l (meridPt y)‖ := by
      simp only [hN, if_pos hmU]
    have hle : N τ (meridPt y) ≤
        ‖w10Re‖ * ‖iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y‖ := by
      rw [hNn]
      unfold physPd2 physPd
      rw [hrot, w10_sepWre_eq]
      refine (w112_norm_fderiv2_re hUo hA2 hyU _ _).trans ?_
      rw [norm_actM hMo, norm_actM hMo, wyl_norm_coordinateVector, wyl_norm_coordinateVector,
        mul_one, mul_one]
    unfold IIIa.wDerivNorm
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  have hI := hG ν R c hν hR hc T hS ‖w10Re‖ N (norm_nonneg _) hNm
    (fun τ y => by simp only [hN, hperV]) (fun τ y => norm_nonneg _)
    hDom
  rw [hread]
  exact w10_final hν hR hc g hg.measurable _ (fun τ y => norm_nonneg _)
    (F := fun τ y => if y ∈ U then physPd2 (sepWre ν m T τ) j l y else 0)
    (fun τ y _ => le_rfl) ‖w10Re‖ b (norm_nonneg _) hb0 hI

/-- **`D²X₀` on the young support** (`sep:young` 3633-3648 with `j = 2`). -/
theorem wardD2X0YoungL2_proved (ν μ R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ j l : Fin 3, YoungL2Le c ν R C (fun τ => physPd2 (wardX0 ν μ R c g τ) j l) g := by
  have hμ1 : -(1 / 4) < μ + 1 := by linarith
  obtain ⟨D1, hD1, d1⟩ := w112_single2 μ hμ ν R c hν hR hc
  obtain ⟨D2, hD2, d2⟩ := w112_single2 (μ + 1) hμ1 ν R c hν hR hc
  refine ⟨D1 + D2, fun g hg j l => ?_⟩
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hV3 : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ, ContDiffOn ℝ 3 (sepWre ν m T τ) U := fun m hm τ =>
    (w112_smoothV hν hm hr hP hS hM τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hX3 : ∀ τ, ContDiffOn ℝ 3 (wardX0 ν μ R c g τ) U := by
    intro τ
    rw [hX0]
    have e : sepX0 ν μ T τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z :=
      funext fun z => sepX0_eq_sub ν μ T τ z
    rw [e]
    exact (hV3 μ hμ τ).sub (hV3 (μ + 1) hμ1 τ)
  have hPd2 := w112_meas_pd2 (wardX0_measurable_of_measurable ν μ R c g hg.measurable) hUo hX3 j l
  have hread : wardYoungRead ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j l) =
      wardYoungRead ν R (fun τ y => if y ∈ U then physPd2 (wardX0 ν μ R c g τ) j l y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  refine w10_young_of_sum
    (A := fun τ => physPd2 (sepWre ν μ T τ) j l)
    (B := fun τ => physPd2 (sepWre ν (μ + 1) T τ) j l)
    ?_ (d1 g hg j l) (d2 g hg j l) hD1 hD2 le_rfl ?_
  · rw [hread]
    exact (w10_read_meas hPd2).aestronglyMeasurable
  · refine w10_read_dom hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hsub := WardCalc.physPd2_sum_pt (A := sepWre ν μ T τ) (B := fun z => -sepWre ν (μ + 1) T τ z)
      (C := wardX0 ν μ R c g τ) hUo (hV3 μ hμ τ) ((hV3 (μ + 1) hμ1 τ).neg)
      (fun z _ => by rw [hX0, sepX0_eq_sub, sub_eq_add_neg]) hyU j l
    have hneg : physPd2 (fun z => -sepWre ν (μ + 1) T τ z) j l y =
        -physPd2 (sepWre ν (μ + 1) T τ) j l y := by
      have h0 := WardCalc.physPd2_sum_pt (A := sepWre ν (μ + 1) T τ)
        (B := fun z => -sepWre ν (μ + 1) T τ z) (C := fun _ => 0) hUo
        (hV3 (μ + 1) hμ1 τ) ((hV3 (μ + 1) hμ1 τ).neg) (fun z _ => (add_neg_cancel _).symm) hyU j l
      have hc0 : physPd2 (fun _ : Space => (0 : Space)) j l y = 0 := by
        simp [physPd2, physPd]
      rw [hc0] at h0
      exact eq_neg_of_add_eq_zero_right h0.symm
    rw [hsub, hneg, ← sub_eq_add_neg]
    exact norm_sub_le _ _

end UnforcedLeray.Short.PartIIIb.Concrete
end
