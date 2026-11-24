import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Pt2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound.ZActJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound.StreamCutHess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Rad.Basic

/-!
# `PartIII-b:C/rep/3/1/3`: Pointwise cutoff decomposition for `sepWX` and `sepWY`

Source of record: `the November 2 reference manuscript`, lines 4181-4200,
5203-5210, 5238-5244, 5267.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SepWXWYDecompAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open GeomXAsm GeomXAsm.StreamCutAlgAux StreamCutHessAux

/-! ## Clause 1: Beyond the transition annulus (`R * √(5ν/4) < ϱ y`) -/

/-- Where `R * √(5ν/4) < ϱ z`, `wardStreamCut ν R χy Z τ` agrees with `Z τ`. -/
lemma wardStreamCut_eq_of_gt {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (Z : ℝ → Space → Space) (τ : ℝ) {z : Space}
    (hz : R * Real.sqrt (5 * ν / 4) < ϱ z) :
    wardStreamCut ν R χy Z τ z = Z τ z := by
  have hQ0 : 0 < R * Real.sqrt (5 * ν / 4) := by positivity
  have hz0 : 0 < ϱ z := lt_trans hQ0 hz
  have ht : ν * age R z < 4 / 5 := by
    unfold age
    rw [← mul_div_assoc, div_lt_iff₀ (pow_pos hz0 2)]
    have hQs : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h2 : (R * Real.sqrt (5 * ν / 4)) ^ 2 < ϱ z ^ 2 :=
      pow_lt_pow_left₀ hz hQ0.le two_ne_zero
    nlinarith [hQs]
  unfold wardStreamCut
  rw [hχ.one _ ht.le, (wgx_deriv_zero_lt hχ ht).1]
  simp

/-- Eventually `wardStreamCut ν R χy Z τ =ᶠ[𝓝 y] Z τ` when `R * √(5ν/4) < ϱ y`. -/
lemma wardStreamCut_eventuallyEq_of_gt {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (Z : ℝ → Space → Space) (τ : ℝ) {y : Space}
    (hb : R * Real.sqrt (5 * ν / 4) < ϱ y) :
    wardStreamCut ν R χy Z τ =ᶠ[𝓝 y] Z τ := by
  have hU : IsOpen {z : Space | R * Real.sqrt (5 * ν / 4) < ϱ z} :=
    isOpen_lt continuous_const continuous_ϱ
  filter_upwards [hU.mem_nhds hb] with z hz
  exact wardStreamCut_eq_of_gt hχ hν hR Z τ hz

/-- Clause 1 of `SepWXWYPointwiseDecomp`: beyond `R * √(5ν/4)`, `sepWX = sepX0` and
`sepWY = sepWre` in a neighborhood of `y`. -/
theorem sepWXWY_beyond_ann {σ₁ σ₂ ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hσ : -(1 / 4 : ℝ) < σ₁) (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R) (hP0 : 0 < P)
    (hμ : μ ∈ Icc σ₁ σ₂) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hSM : SepMoment P T)
    (hAx : IsAxiSource T) (τ : ℝ) (y : Space) (hb : R * Real.sqrt (5 * ν / 4) < ϱ y) :
    ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤ wgxJet 1 ν μ (ϱ y) T τ y ∧
      ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖ ≤ wgyWJet 1 ν μ (ϱ y) T τ y := by
  have hR : 0 < R := by linarith
  have hy : 0 < ϱ y := lt_trans (by positivity) hb
  have hevX : sepWX ν μ R χy T τ =ᶠ[𝓝 y] sepX0 ν μ T τ :=
    wardStreamCut_eventuallyEq_of_gt hχ hν hR (sepX0 ν μ T) τ hb
  have hevW : wardStreamCut ν R χy (sepWre ν μ T) τ =ᶠ[𝓝 y] sepWre ν μ T τ :=
    wardStreamCut_eventuallyEq_of_gt hχ hν hR (sepWre ν μ T) τ hb
  have hpos : ∀ᶠ z in 𝓝 y, 0 < ϱ z := continuous_ϱ.continuousAt.eventually (lt_mem_nhds hy)
  have hYev : sepWY ν μ R χy T τ =ᶠ[𝓝 y]
      fun z => wardStreamCut ν R χy (sepWre ν μ T) τ z + tcComm ν R χy (sepX0 ν μ T) τ z := by
    filter_upwards [hpos] with z hz
    exact wgy_Y_eq hχ hσ hν hν1 hR1 hP0 hμ hT hSM hAx τ hz
  have hnotAnn : y ∉ streamAnn ν R := fun h => not_lt.2 h.2 hb
  have hout := (Sub8_1_1_2_3.tcOut_iff_not_mem hν hR hy).2 hnotAnn
  have hzComm := Sub8_1_1_2_3.tcComm_eventually_zero hχ (sepX0 ν μ T) τ hy hout
  have hevY : sepWY ν μ R χy T τ =ᶠ[𝓝 y] sepWre ν μ T τ := by
    filter_upwards [hYev, hevW, hzComm] with z h1 h2 h3
    rw [h1, h2, h3, add_zero]
  refine ⟨?_, ?_⟩
  · rw [hevX.fderiv_eq]
    unfold wgxJet
    rw [if_pos le_rfl, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_one]
  · rw [hevY.fderiv_eq]
    unfold wgyWJet
    rw [if_pos le_rfl, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_one]

/-! ## Vanishing of `gradSize` and `hessSize` on the inner cylinder `{y | ϱ y < R * √ν}` -/

private lemma varrho_eq_zero_iff (z : Space) : ϱ z = 0 ↔ z 0 = 0 ∧ z 1 = 0 := by
  rw [← mem_axis_iff]
  rfl

private lemma varrho_add_smul_of_axis {z w : Space} (hz : ϱ z = 0) (hw : ϱ w = 1) (t : ℝ) :
    ϱ (z + t • w) = |t| := by
  obtain ⟨hz0, hz1⟩ := (varrho_eq_zero_iff z).1 hz
  have hw2 : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    have := congrArg (· ^ 2) hw
    simpa [ϱ, Real.sq_sqrt (by positivity : 0 ≤ w 0 ^ 2 + w 1 ^ 2)] using this
  unfold ϱ
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hz0, hz1, zero_add]
  have heq : (t * w 0) ^ 2 + (t * w 1) ^ 2 = t ^ 2 * (w 0 ^ 2 + w 1 ^ 2) := by ring
  rw [heq, hw2, mul_one, Real.sqrt_sq_eq_abs]

private lemma varrho_e0 : ϱ (coordinateVector 0 : Space) = 1 := by
  simp [ϱ, coordinateVector]

private lemma varrho_e1 : ϱ (coordinateVector 1 : Space) = 1 := by
  simp [ϱ, coordinateVector]

private lemma varrho_e0_add_e2 :
    ϱ ((coordinateVector 0 : Space) + (coordinateVector 2 : Space)) = 1 := by
  simp [ϱ, coordinateVector]

/-- If `f` vanishes on `{z | 0 < ϱ z ∧ ϱ z < L}` (`0 < L`), then `fderiv ℝ f z = 0` at every
point `z` with `ϱ z < L` (including axis points `ϱ z = 0`). -/
lemma fderiv_eq_zero_on_cyl {f : Space → Space} {L : ℝ} (hL : 0 < L)
    (hf0 : ∀ z : Space, 0 < ϱ z → ϱ z < L → f z = 0) {z : Space} (hz : ϱ z < L) :
    fderiv ℝ f z = 0 := by
  by_cases hzpos : 0 < ϱ z
  · have hU : IsOpen {w : Space | 0 < ϱ w ∧ ϱ w < L} :=
      (isOpen_lt continuous_const continuous_ϱ).inter (isOpen_lt continuous_ϱ continuous_const)
    have hev : f =ᶠ[𝓝 z] fun _ => (0 : Space) := by
      filter_upwards [hU.mem_nhds ⟨hzpos, hz⟩] with w hw
      exact hf0 w hw.1 hw.2
    rw [hev.fderiv_eq, fderiv_const_apply]
  · have hz0 : ϱ z = 0 := le_antisymm (not_lt.1 hzpos) (Real.sqrt_nonneg _)
    by_cases hd : DifferentiableAt ℝ f z
    · -- First show `f z = 0` by continuity along `z + t • e_0` as `t → 0+`
      have hfz : f z = 0 := by
        have hcont : ContinuousAt (fun t : ℝ => f (z + t • (coordinateVector 0 : Space))) 0 := by
          have h1 : ContinuousAt (fun t : ℝ => z + t • (coordinateVector 0 : Space)) 0 := by
            fun_prop
          exact ContinuousAt.comp (by simpa using hd.continuousAt) h1
        have hlim : Tendsto (fun t : ℝ => f (z + t • (coordinateVector 0 : Space)))
            (𝓝[Ioo 0 L] 0) (𝓝 (f z)) := by
          simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
        have heq0 : ∀ t ∈ Ioo 0 L, f (z + t • (coordinateVector 0 : Space)) = 0 := by
          intro t ht
          have hρt : ϱ (z + t • (coordinateVector 0 : Space)) = |t| :=
            varrho_add_smul_of_axis hz0 varrho_e0 t
          rw [abs_of_pos ht.1] at hρt
          exact hf0 _ (by linarith [ht.1]) (by linarith [ht.2])
        have hlim0 : Tendsto (fun t : ℝ => f (z + t • (coordinateVector 0 : Space)))
            (𝓝[Ioo 0 L] 0) (𝓝 0) :=
          tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (heq0 t ht).symm)
        have hne : (𝓝[Ioo 0 L] (0 : ℝ)).NeBot :=
          mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_Ioo hL.ne]; exact left_mem_Icc.2 hL.le)
        exact tendsto_nhds_unique hlim hlim0
      -- Next show `fderiv ℝ f z w = 0` for any `w` with `ϱ w = 1`
      have hdir : ∀ w : Space, ϱ w = 1 → fderiv ℝ f z w = 0 := by
        intro w hw
        have hpath : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
        have hD : HasDerivAt (fun t : ℝ => f (z + t • w)) (fderiv ℝ f z w) 0 :=
          hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
        have hev : (fun t : ℝ => f (z + t • w)) =ᶠ[𝓝 0] fun _ => (0 : Space) := by
          filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hL) hL] with t ht
          by_cases ht0 : t = 0
          · subst ht0; simpa using hfz
          · have hρt : ϱ (z + t • w) = |t| := varrho_add_smul_of_axis hz0 hw t
            have habs0 : 0 < |t| := abs_pos.2 ht0
            have habsL : |t| < L := abs_lt.2 ht
            exact hf0 _ (by linarith) (by linarith)
        have hD0 : HasDerivAt (fun t : ℝ => f (z + t • w)) 0 0 :=
          (hasDerivAt_const (0 : ℝ) (0 : Space)).congr_of_eventuallyEq hev
        exact hD.unique hD0
      have he0 : fderiv ℝ f z (coordinateVector 0) = 0 := hdir _ varrho_e0
      have he1 : fderiv ℝ f z (coordinateVector 1) = 0 := hdir _ varrho_e1
      have he02 : fderiv ℝ f z (coordinateVector 0 + coordinateVector 2) = 0 :=
        hdir _ varrho_e0_add_e2
      have he2 : fderiv ℝ f z (coordinateVector 2) = 0 := by
        calc fderiv ℝ f z (coordinateVector 2)
            = fderiv ℝ f z (coordinateVector 0 + coordinateVector 2) -
                fderiv ℝ f z (coordinateVector 0) := by
              rw [← map_sub, add_sub_cancel_left]
          _ = 0 := by rw [he02, he0, sub_zero]
      ext v i
      have hv : v = v 0 • (coordinateVector 0 : Space) + v 1 • (coordinateVector 1 : Space) +
          v 2 • (coordinateVector 2 : Space) := by
        ext k; fin_cases k <;> simp [coordinateVector]
      rw [hv, map_add, map_add, map_smul, map_smul, map_smul, he0, he1, he2]
      simp
    · exact fderiv_zero_of_not_differentiableAt hd

/-- On `{y | ϱ y < R * √ν}`, both `gradSize (sepWX ...)` and `hessSize (sepWX ...)` vanish. -/
theorem sepWX_grad_hess_zero_of_lt {ν μ R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    {y : Space} (hy : ϱ y < R * Real.sqrt ν) :
    gradSize (sepWX ν μ R χy T τ) y = 0 ∧ hessSize (sepWX ν μ R χy T τ) y = 0 := by
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := by rw [hLdef]; positivity
  have hLsq : ν * R ^ 2 = L ^ 2 := by rw [hLdef, mul_pow, Real.sq_sqrt hν.le]; ring
  have hf0 : ∀ z : Space, 0 < ϱ z → ϱ z < L → sepWX ν μ R χy T τ z = 0 := by
    intro z hz0 hzL
    have ht : 1 < ν * age R z := by
      unfold age
      rw [← mul_div_assoc, hLsq]
      exact (one_lt_div (pow_pos hz0 2)).2 (pow_lt_pow_left₀ hzL hz0.le two_ne_zero)
    show wardStreamCut ν R χy (sepX0 ν μ T) τ z = 0
    unfold wardStreamCut
    rw [hχ.zero _ ht.le, (wgx_deriv_zero_gt hχ ht).1]
    simp
  have hfd : ∀ z : Space, ϱ z < L → fderiv ℝ (sepWX ν μ R χy T τ) z = 0 :=
    fun z hz => fderiv_eq_zero_on_cyl hL hf0 hz
  have hU : IsOpen {z : Space | ϱ z < L} := isOpen_lt continuous_ϱ continuous_const
  have hpd_ev : ∀ l : Fin 3, physPd (sepWX ν μ R χy T τ) l =ᶠ[𝓝 y] fun _ => (0 : Space) := by
    intro l
    filter_upwards [hU.mem_nhds hy] with z hz
    unfold physPd
    rw [hfd z hz]
    simp
  refine ⟨?_, ?_⟩
  · unfold gradSize physPd
    rw [hfd y hy]
    simp
  · unfold hessSize physPd2
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
    change ‖fderiv ℝ (physPd (sepWX ν μ R χy T τ) l) y (coordinateVector j)‖ = 0
    rw [(hpd_ev l).fderiv_eq]
    simp

/-! ## Clause 2 beyond the annulus (`R * √(5ν/4) < ϱ y`) -/

theorem sepWX_hess_beyond_ann {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (H : TCH ν R μ P T) (τ : ℝ)
    {y : Space} (hb : R * Real.sqrt (5 * ν / 4) < ϱ y) :
    hessSize (sepWX ν μ R χy T τ) y ≤ 9 * ‖iteratedFDeriv ℝ 2 (sepX0 ν μ T τ) y‖ := by
  have hU : IsOpen {z : Space | R * Real.sqrt (5 * ν / 4) < ϱ z} :=
    isOpen_lt continuous_const continuous_ϱ
  have hev : ∀ z ∈ {z : Space | R * Real.sqrt (5 * ν / 4) < ϱ z},
      sepWX ν μ R χy T τ =ᶠ[𝓝 z] sepX0 ν μ T τ :=
    fun z hz => wardStreamCut_eventuallyEq_of_gt hχ H.hν H.hR (sepX0 ν μ T) τ hz
  have hpd_ev : ∀ l : Fin 3,
      physPd (sepWX ν μ R χy T τ) l =ᶠ[𝓝 y] physPd (sepX0 ν μ T τ) l := by
    intro l
    filter_upwards [hU.mem_nhds hb] with z hz
    unfold physPd
    rw [(hev z hz).fderiv_eq]
  have hhess_eq : hessSize (sepWX ν μ R χy T τ) y = hessSize (sepX0 ν μ T τ) y := by
    unfold hessSize physPd2
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    change ‖fderiv ℝ (physPd (sepWX ν μ R χy T τ) l) y (coordinateVector j)‖ =
      ‖fderiv ℝ (physPd (sepX0 ν μ T τ) l) y (coordinateVector j)‖
    rw [(hpd_ev l).fderiv_eq]
  rw [hhess_eq]
  have h56_pos : 0 ≤ 5 * ν / 6 := div_nonneg (mul_nonneg (by norm_num) H.hν.le) (by norm_num)
  have hlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt (5 * ν / 4) :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt h56_pos (by linarith [H.hν])) H.hR
  have hyU : y ∈ youngOpen ν R := lt_trans hlt hb
  exact ZActJetAux.hessSize_le_iteratedFDeriv (isOpen_lt continuous_const continuous_ϱ)
    (tcb_smooth' H τ) hyU

/-! ## Clause 2 on the transition annulus (`y ∈ streamAnn ν R`) -/

private lemma abs_coord_le_varrho (y : Space) : |y 0| ≤ ϱ y ∧ |y 1| ≤ ϱ y := by
  unfold ϱ
  refine ⟨?_, ?_⟩
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 0)])

/-- First and second partials of `y' ↦ g (ϱ y')` at any off-axis point `y` (`0 < ϱ y`). -/
lemma comp_varrho_partials_any {g : ℝ → ℝ} {y : Space} (hy : 0 < ϱ y)
    (hg : ContDiffAt ℝ 2 g (ϱ y)) :
    (∀ l : Fin 3, |fderiv ℝ (fun y' => g (ϱ y')) y (coordinateVector l)| ≤ |deriv g (ϱ y)|) ∧
    (∀ j l : Fin 3,
      |fderiv ℝ (fun y' => fderiv ℝ (fun y'' => g (ϱ y'')) y' (coordinateVector l))
        y (coordinateVector j)| ≤ |deriv (deriv g) (ϱ y)| + 2 * (ϱ y)⁻¹ * |deriv g (ϱ y)|) := by
  set r := ϱ y
  have hgd : DifferentiableAt ℝ g r := hg.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (deriv g) r := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ g) r :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have : deriv g = fun s => fderiv ℝ g s 1 := rfl
    rw [this]
    exact h1.clm_apply (differentiableAt_const _)
  obtain ⟨hy0, hy1⟩ := abs_coord_le_varrho y
  have hc : ∀ j l : Fin 3, |(coordinateVector j : Space) l| ≤ 1 := fun j l => by
    fin_cases j <;> fin_cases l <;> simp [coordinateVector]
  refine ⟨?_, ?_⟩
  · intro l
    rw [tcle_fderiv_comp hy hgd]
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [coordinateVector, PiLp.single_apply, ↓reduceIte, mul_one,
        show (1 : Fin 3) ≠ 0 by decide, mul_zero, add_zero]
      rw [abs_mul, abs_div, abs_of_pos hy]
      calc |deriv g r| * (|y 0| / r) ≤ |deriv g r| * (r / r) := by gcongr
        _ = |deriv g r| := by rw [div_self hy.ne', mul_one]
    · simp only [coordinateVector, PiLp.single_apply, show (0 : Fin 3) ≠ 1 by decide, ↓reduceIte,
        mul_zero, zero_add, mul_one]
      rw [abs_mul, abs_div, abs_of_pos hy]
      calc |deriv g r| * (|y 1| / r) ≤ |deriv g r| * (r / r) := by gcongr
        _ = |deriv g r| := by rw [div_self hy.ne', mul_one]
    · simp [coordinateVector]
  · set κ : ℝ → ℝ := fun s => deriv g s / s with hκ
    have hκd : HasDerivAt κ (deriv (deriv g) r / r - deriv g r / r ^ 2) r := by
      have := hdg.hasDerivAt.div (hasDerivAt_id r) hy.ne'
      have e : (deriv (deriv g) r * id r - deriv g r * 1) / id r ^ 2 =
          deriv (deriv g) r / r - deriv g r / r ^ 2 := by
        simp only [id]; field_simp
      rw [e] at this
      exact this
    have hev : ∀ᶠ y' in 𝓝 y, 0 < ϱ y' ∧ DifferentiableAt ℝ g (ϱ y') := by
      have e1 : ∀ᶠ y' in 𝓝 y, 0 < ϱ y' := continuous_ϱ.continuousAt.eventually (lt_mem_nhds hy)
      have e2 : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (ϱ y') := by
        have : ∀ᶠ s in 𝓝 r, DifferentiableAt ℝ g s :=
          (hg.eventually (by simp)).mono fun s hs => hs.differentiableAt (by norm_num)
        exact continuous_ϱ.continuousAt.eventually this
      exact e1.and e2
    have hk : DifferentiableAt ℝ (fun y' => κ (ϱ y')) y :=
      (tcle_hasFDeriv_comp (g := κ) hy hκd.differentiableAt).differentiableAt
    have hl : ∀ l : Fin 3, (fun y' => fderiv ℝ (fun y'' => g (ϱ y'')) y' (coordinateVector l)) =ᶠ[𝓝 y]
        fun y' => if l = 0 then y' 0 * κ (ϱ y') else if l = 1 then y' 1 * κ (ϱ y') else 0 := by
      intro l
      filter_upwards [hev] with y' ⟨hy', hgy'⟩
      rw [tcle_fderiv_comp hy' hgy']
      fin_cases l
      · simp [coordinateVector, hκ]; field_simp
      · simp [coordinateVector, hκ]; field_simp
      · simp [coordinateVector]
    intro j l
    rw [(hl l).fderiv_eq]
    have hd := hκd.deriv
    have hnn1 : 0 ≤ |deriv (deriv g) r| := abs_nonneg _
    have hnn2 : 0 ≤ 2 * r⁻¹ * |deriv g r| := by positivity
    have hκ_le : |deriv κ r| ≤ |deriv (deriv g) r| / r + |deriv g r| / r ^ 2 := by
      rw [hd, sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_div, abs_div, abs_of_pos hy, abs_of_pos (pow_pos hy 2)]
    have hfd_κ : |fderiv ℝ (fun y' => κ (ϱ y')) y (coordinateVector j)| ≤ |deriv κ r| := by
      rw [tcle_fderiv_comp (g := κ) hy hκd.differentiableAt (coordinateVector j)]
      rcases (by fin_cases j <;> decide : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp only [coordinateVector, PiLp.single_apply, ↓reduceIte, mul_one,
          show (1 : Fin 3) ≠ 0 by decide, mul_zero, add_zero]
        rw [abs_mul, abs_div, abs_of_pos hy]
        calc |deriv κ r| * (|y 0| / r) ≤ |deriv κ r| * (r / r) := by gcongr
          _ = |deriv κ r| := by rw [div_self hy.ne', mul_one]
      · simp only [coordinateVector, PiLp.single_apply, show (0 : Fin 3) ≠ 1 by decide, ↓reduceIte,
          mul_zero, zero_add, mul_one]
        rw [abs_mul, abs_div, abs_of_pos hy]
        calc |deriv κ r| * (|y 1| / r) ≤ |deriv κ r| * (r / r) := by gcongr
          _ = |deriv κ r| := by rw [div_self hy.ne', mul_one]
      · simp [coordinateVector]
    have hκr : |κ r| = r⁻¹ * |deriv g r| := by
      dsimp only [κ]
      rw [div_eq_inv_mul, abs_mul, abs_of_pos (inv_pos.2 hy)]
    have hmul_κ : r * |deriv κ r| + |κ r| ≤ |deriv (deriv g) r| + 2 * r⁻¹ * |deriv g r| := by
      calc r * |deriv κ r| + |κ r|
          ≤ r * (|deriv (deriv g) r| / r + |deriv g r| / r ^ 2) + r⁻¹ * |deriv g r| := by
            gcongr
            exact le_of_eq hκr
        _ = |deriv (deriv g) r| + 2 * r⁻¹ * |deriv g r| := by
            field_simp
            ring
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [↓reduceIte]
      rw [tcl_fd_mul 0 hk (coordinateVector j)]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |y 0| * |fderiv ℝ (fun y' => κ (ϱ y')) y (coordinateVector j)| +
            |κ r| * |(coordinateVector j : Space) 0|
          ≤ r * |deriv κ r| + |κ r| * 1 := by
            gcongr
            exact hc j 0
        _ = r * |deriv κ r| + |κ r| := by ring
        _ ≤ |deriv (deriv g) r| + 2 * r⁻¹ * |deriv g r| := hmul_κ
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
      rw [tcl_fd_mul 1 hk (coordinateVector j)]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |y 1| * |fderiv ℝ (fun y' => κ (ϱ y')) y (coordinateVector j)| +
            |κ r| * |(coordinateVector j : Space) 1|
          ≤ r * |deriv κ r| + |κ r| * 1 := by
            gcongr
            exact hc j 1
        _ = r * |deriv κ r| + |κ r| := by ring
        _ ≤ |deriv (deriv g) r| + 2 * r⁻¹ * |deriv g r| := hmul_κ
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte,
        fderiv_const_apply, zero_apply, abs_zero]
      exact add_nonneg hnn1 hnn2

/-- On `youngOpen ν R`, the partials of `outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)` are given by
polynomials in `y'` and `sepX0 ν μ T τ y'`, eliminating `meridPt`. -/
lemma sepX0_outPrim_partials_eq {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y' : Space} (hy' : y' ∈ youngOpen ν R) (l : Fin 3) :
    fderiv ℝ (fun y'' : Space => outPrim (sepX0 ν μ T) τ (ϱ y'') (y'' 2)) y' (coordinateVector l) =
      if l = 0 then y' 0 * sepX0 ν μ T τ y' 2
      else if l = 1 then y' 1 * sepX0 ν μ T τ y' 2
      else -(y' 0 * sepX0 ν μ T τ y' 0 + y' 1 * sepX0 ν μ T τ y' 1) := by
  have hy_gt : R * Real.sqrt (5 * ν / 6) < ϱ y' := hy'
  have hρ : 0 < ϱ y' := lt_of_le_of_lt H.ha hy_gt
  have hρ2 : ϱ y' ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨r0, r1, r2⟩ := tcb_rep H.hν H.hμ H.ha H.hP H.hT H.hM H.hA τ hy_gt
  rw [tcb_du H τ hy_gt (coordinateVector l)]
  rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · simp [coordinateVector, r2]
  · simp [coordinateVector, r2]
  · simp only [coordinateVector, PiLp.single_apply, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte, mul_zero, add_zero, mul_one, zero_mul,
      zero_sub, neg_inj]
    rw [r0, r1]
    have hne : ϱ y' ≠ 0 := hρ.ne'
    calc ϱ y' * sepX0 ν μ T τ (meridPt y') 0
        = (ϱ y' ^ 2 / ϱ y') * sepX0 ν μ T τ (meridPt y') 0 := by field_simp
      _ = ((y' 0 ^ 2 + y' 1 ^ 2) / ϱ y') * sepX0 ν μ T τ (meridPt y') 0 := by rw [hρ2]
      _ = y' 0 * (y' 0 / ϱ y' * sepX0 ν μ T τ (meridPt y') 0) +
            y' 1 * (y' 1 / ϱ y' * sepX0 ν μ T τ (meridPt y') 0) := by ring

/-- First and second partials of `psiFld (sepX0 ν μ T) τ` at any point `y ∈ youngOpen ν R`. -/
lemma psiFld_partials_sepX0 {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hyU : y ∈ youngOpen ν R) :
    ContDiffAt ℝ 2 (psiFld (sepX0 ν μ T) τ) y ∧
    ‖psiFld (sepX0 ν μ T) τ y‖ = |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)| ∧
    (∀ l : Fin 3, ‖physPd (psiFld (sepX0 ν μ T) τ) l y‖ ≤ 2 * ϱ y * ‖sepX0 ν μ T τ y‖) ∧
    (∀ j l : Fin 3,
      ‖physPd2 (psiFld (sepX0 ν μ T) τ) j l y‖ ≤
        2 * (‖sepX0 ν μ T τ y‖ + ϱ y * gradSize (sepX0 ν μ T τ) y)) := by
  set Z := sepX0 ν μ T
  set r := ϱ y
  have hr : 0 < r := lt_of_le_of_lt H.ha hyU
  have hU : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hΨc : ContDiffOn ℝ 2 (fun y' : Space => outPrim Z τ (ϱ y') (y' 2)) (youngOpen ν R) :=
    tcb_u_c2 H τ
  have hΨat : ContDiffAt ℝ 2 (fun y' : Space => outPrim Z τ (ϱ y') (y' 2)) y :=
    hΨc.contDiffAt (hU.mem_nhds hyU)
  have hpsiat : ContDiffAt ℝ 2 (psiFld Z τ) y := hΨat.smul contDiffAt_const
  have hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) := tcb_smooth' H τ
  have hZd : DifferentiableAt ℝ (Z τ) y :=
    (hZc.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
  obtain ⟨hy0, hy1⟩ := abs_coord_le_varrho y
  have hZ_comp : ∀ m : Fin 3, |Z τ y m| ≤ ‖Z τ y‖ :=
    fun m => by simpa using PiLp.norm_apply_le (Z τ y) m
  have hZ0 : 0 ≤ ‖Z τ y‖ := norm_nonneg _
  have hG0 : 0 ≤ gradSize (Z τ) y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨hpsiat, ?_, ?_, ?_⟩
  · unfold psiFld
    rw [norm_smul, norm_e2, mul_one, Real.norm_eq_abs]
  · intro l
    unfold physPd psiFld
    rw [fderiv_smul_const (hΨat.differentiableAt (by norm_num)),
      ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one, Real.norm_eq_abs,
      sepX0_outPrim_partials_eq H τ hyU l]
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [↓reduceIte, abs_mul]
      calc |y 0| * |Z τ y 2| ≤ r * ‖Z τ y‖ := mul_le_mul hy0 (hZ_comp 2) (abs_nonneg _) hr.le
        _ ≤ 2 * r * ‖Z τ y‖ := by nlinarith [mul_nonneg hr.le hZ0]
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, abs_mul]
      calc |y 1| * |Z τ y 2| ≤ r * ‖Z τ y‖ := mul_le_mul hy1 (hZ_comp 2) (abs_nonneg _) hr.le
        _ ≤ 2 * r * ‖Z τ y‖ := by nlinarith [mul_nonneg hr.le hZ0]
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte,
        abs_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |y 0| * |Z τ y 0| + |y 1| * |Z τ y 1|
          ≤ r * ‖Z τ y‖ + r * ‖Z τ y‖ :=
            add_le_add (mul_le_mul hy0 (hZ_comp 0) (abs_nonneg _) hr.le)
              (mul_le_mul hy1 (hZ_comp 1) (abs_nonneg _) hr.le)
        _ = 2 * r * ‖Z τ y‖ := by ring
  · intro j l
    unfold physPd2 physPd psiFld
    have hev : (fun y' => fderiv ℝ (fun y'' => outPrim Z τ (ϱ y'') (y'' 2) •
        (coordinateVector 2 : Space)) y' (coordinateVector l)) =ᶠ[𝓝 y]
        fun y' => (if l = 0 then y' 0 * Z τ y' 2
          else if l = 1 then y' 1 * Z τ y' 2
          else -(y' 0 * Z τ y' 0 + y' 1 * Z τ y' 1)) • (coordinateVector 2 : Space) := by
      filter_upwards [hU.mem_nhds hyU] with y' hy'
      have hd' : DifferentiableAt ℝ (fun y'' : Space => outPrim Z τ (ϱ y'') (y'' 2)) y' :=
        (hΨc.contDiffAt (hU.mem_nhds hy')).differentiableAt (by norm_num)
      rw [fderiv_smul_const hd', ContinuousLinearMap.smulRight_apply,
        sepX0_outPrim_partials_eq H τ hy' l]
    rw [hev.fderiv_eq]
    have hdZm : ∀ m : Fin 3, DifferentiableAt ℝ (fun y' : Space => Z τ y' m) y := fun m =>
      ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZd.hasFDerivAt).differentiableAt
    have hfdZm_le : ∀ m : Fin 3,
        |fderiv ℝ (fun y' : Space => Z τ y' m) y (coordinateVector j)| ≤ gradSize (Z τ) y := by
      intro m
      rw [tcg_proj_fderiv (Z τ) hZd m (coordinateVector j)]
      have h1 : |fderiv ℝ (Z τ) y (coordinateVector j) m| ≤ ‖physPd (Z τ) j y‖ := by
        simpa [physPd] using PiLp.norm_apply_le (physPd (Z τ) j y) m
      exact h1.trans (Finset.single_le_sum (fun i _ => norm_nonneg (physPd (Z τ) i y))
        (Finset.mem_univ j))
    have hc : ∀ k : Fin 3, |(coordinateVector j : Space) k| ≤ 1 := fun k => by
      fin_cases j <;> fin_cases k <;> simp [coordinateVector]
    have hprod_le : ∀ k m : Fin 3, |y k| ≤ r →
        |fderiv ℝ (fun y' : Space => y' k * Z τ y' m) y (coordinateVector j)| ≤
          ‖Z τ y‖ + r * gradSize (Z τ) y := by
      intro k m hyk
      rw [tcl_fd_mul k (hdZm m) (coordinateVector j)]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |y k| * |fderiv ℝ (fun y' => Z τ y' m) y (coordinateVector j)| +
            |Z τ y m| * |(coordinateVector j : Space) k|
          ≤ r * gradSize (Z τ) y + ‖Z τ y‖ * 1 :=
            add_le_add (mul_le_mul hyk (hfdZm_le m) (abs_nonneg _) hr.le)
              (mul_le_mul (hZ_comp m) (hc k) (abs_nonneg _) hZ0)
        _ = ‖Z τ y‖ + r * gradSize (Z τ) y := by ring
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [↓reduceIte]
      have hd : DifferentiableAt ℝ (fun y' : Space => y' 0 * Z τ y' 2) y :=
        ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt).mul (hdZm 2)
      rw [fderiv_smul_const hd, ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one,
        Real.norm_eq_abs]
      exact (hprod_le 0 2 hy0).trans (by linarith [mul_nonneg hr.le hG0])
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
      have hd : DifferentiableAt ℝ (fun y' : Space => y' 1 * Z τ y' 2) y :=
        ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt).mul (hdZm 2)
      rw [fderiv_smul_const hd, ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one,
        Real.norm_eq_abs]
      exact (hprod_le 1 2 hy1).trans (by linarith [mul_nonneg hr.le hG0])
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
      have hd0 : DifferentiableAt ℝ (fun y' : Space => y' 0 * Z τ y' 0) y :=
        ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt).mul (hdZm 0)
      have hd1 : DifferentiableAt ℝ (fun y' : Space => y' 1 * Z τ y' 1) y :=
        ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt).mul (hdZm 1)
      have hfd_neg : fderiv ℝ (fun y' : Space => -(y' 0 * Z τ y' 0 + y' 1 * Z τ y' 1)) y =
          -(fderiv ℝ (fun y' : Space => y' 0 * Z τ y' 0) y +
            fderiv ℝ (fun y' : Space => y' 1 * Z τ y' 1) y) :=
        ((hd0.hasFDerivAt.fun_add hd1.hasFDerivAt).neg).fderiv
      have hd : DifferentiableAt ℝ
          (fun y' : Space => -(y' 0 * Z τ y' 0 + y' 1 * Z τ y' 1)) y := (hd0.add hd1).neg
      rw [fderiv_smul_const hd, ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one,
        Real.norm_eq_abs, hfd_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
        abs_neg]
      refine (abs_add_le _ _).trans ?_
      have b0 := hprod_le 0 0 hy0
      have b1 := hprod_le 1 1 hy1
      linarith

/-- Second-derivative bound for `sepWX` at any point `y ∈ streamAnn ν R`. -/
theorem sepWX_hess_on_ann {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
        (H : TCH ν R μ P T) (τ : ℝ) {y : Space}, y ∈ streamAnn ν R →
        hessSize (sepWX ν μ R χy T τ) y ≤
          C₀ * (hessSize (sepX0 ν μ T τ) y +
            (R * Real.sqrt ν)⁻¹ * gradSize (sepX0 ν μ T τ) y +
            (R * Real.sqrt ν)⁻¹ ^ 2 * ‖sepX0 ν μ T τ y‖ +
            (R * Real.sqrt ν)⁻¹ ^ 4 * |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|) := by
  obtain ⟨d0, d1, d2, M, hM, hb₁, hb₂, hb₃⟩ := stream_cutoff_const3 χy hχ
  refine ⟨1800 * M, by positivity, ?_⟩
  intro ν R μ P T H τ y hyann
  set Z := sepX0 ν μ T
  set L := R * Real.sqrt ν with hLdef
  set r := ϱ y
  have hL : 0 < L := by rw [hLdef]; exact mul_pos H.hR (Real.sqrt_pos.2 H.hν)
  have hr : 0 < r := lt_of_lt_of_le hL hyann.1
  have h56_pos : 0 ≤ 5 * ν / 6 := div_nonneg (mul_nonneg (by norm_num) H.hν.le) (by norm_num)
  have hrL : R * Real.sqrt (5 * ν / 6) < L := by
    rw [hLdef]
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt h56_pos (by linarith [H.hν])) H.hR
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrL hyann.1
  have ht1 : ν * (R ^ 2 / r ^ 2) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one (pow_pos hr 2)]
    have hL2 : L ^ 2 = ν * R ^ 2 := by rw [hLdef, mul_pow, Real.sq_sqrt H.hν.le]; ring
    rw [← hL2]
    exact pow_le_pow_left₀ hL.le hyann.1 2
  have hU : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hZat : ContDiffAt ℝ 2 (Z τ) y := (tcb_smooth' H τ).contDiffAt (hU.mem_nhds hyU)
  obtain ⟨hpsiat, hpsi0, hpsi1, hpsi2⟩ := psiFld_partials_sepX0 H τ hyU
  have hcc : ContDiffAt ℝ 2 (tcC0 ν R χy) r := tcle_c0_smooth hχ ν R hr.ne'
  have hff : ContDiffAt ℝ 2 (tcF0 ν R χy) r := tcle_f0_smooth hχ ν R hr.ne'
  have hya : y ∉ axis := tcle_notaxis hr
  have hϱc : ContDiffAt ℝ 2 ϱ y := contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds hya)
  have hC : ContDiffAt ℝ 2 (fun y' => tcC0 ν R χy (ϱ y')) y :=
    (show ContDiffAt ℝ 2 (tcC0 ν R χy) (ϱ y) from hcc).comp y hϱc
  have hF : ContDiffAt ℝ 2 (fun y' => tcF0 ν R χy (ϱ y')) y :=
    (show ContDiffAt ℝ 2 (tcF0 ν R χy) (ϱ y) from hff).comp y hϱc
  obtain ⟨bC0, bC1, bC2, bF0, bF1, bF2⟩ :=
    tc_radial_bounds hχ d0 d1 d2 hM hb₁ hb₂ hb₃ H.hν hr ht1
  obtain ⟨cC1, cC2⟩ := comp_varrho_partials_any hr hcc
  obtain ⟨cF1, cF2⟩ := comp_varrho_partials_any hr hff
  have hWf : sepWX ν μ R χy T τ = fun y' =>
      tcC0 ν R χy (ϱ y') • Z τ y' + tcF0 ν R χy (ϱ y') • psiFld Z τ y' :=
    funext fun y' => tcle_wsc_eq ν R χy Z τ y'
  set i := r⁻¹
  have hi0 : 0 < i := inv_pos.2 hr
  have hri : r * i = 1 := mul_inv_cancel₀ hr.ne'
  have hM0 : 0 ≤ M := by linarith
  set Hs := hessSize (Z τ) y
  set Gs := gradSize (Z τ) y
  set Zn := ‖Z τ y‖
  set Pn := |outPrim Z τ r (y 2)|
  have hH0 : 0 ≤ Hs := hessSize_nonneg _ _
  have hG0 : 0 ≤ Gs := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZ0 : 0 ≤ Zn := norm_nonneg _
  have hP0 : 0 ≤ Pn := abs_nonneg _
  have hjl : ∀ j l : Fin 3,
      ‖physPd2 (sepWX ν μ R χy T τ) j l y‖ ≤
        M * ‖physPd2 (Z τ) j l y‖ +
        2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖) +
        (4 * M * i * Gs + 66 * M * i ^ 2 * Zn + 116 * M * i ^ 4 * Pn) := by
    intro j l
    rw [hWf, physPd2_add_at (f := fun y' => tcC0 ν R χy (ϱ y') • Z τ y')
      (g := fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') (hC.smul hZat) (hF.smul hpsiat) j l]
    have m1 := norm_physPd2_smul_le hC hZat
      (A₀ := 1) (A₁ := 2 * M * i) (A₂ := 14 * M * i ^ 2)
      bC0
      (fun k => (cC1 k).trans bC1)
      (fun j' l' => (cC2 j' l').trans (by
        calc |deriv (deriv (tcC0 ν R χy)) r| + 2 * i * |deriv (tcC0 ν R χy) r|
            ≤ 10 * M * i ^ 2 + 2 * i * (2 * M * i) :=
              add_le_add bC2 (mul_le_mul_of_nonneg_left bC1 (by positivity))
          _ = 14 * M * i ^ 2 := by ring)) j l
    have m2 := norm_physPd2_smul_le hF hpsiat
      (A₀ := 2 * M * i ^ 2) (A₁ := 12 * M * i ^ 3) (A₂ := 116 * M * i ^ 4)
      bF0
      (fun k => (cF1 k).trans bF1)
      (fun j' l' => (cF2 j' l').trans (by
        calc |deriv (deriv (tcF0 ν R χy)) r| + 2 * i * |deriv (tcF0 ν R χy) r|
            ≤ 92 * M * i ^ 4 + 2 * i * (12 * M * i ^ 3) :=
              add_le_add bF2 (mul_le_mul_of_nonneg_left bF1 (by positivity))
          _ = 116 * M * i ^ 4 := by ring)) j l
    rw [hpsi0] at m2
    have m2' : ‖physPd2 (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') j l y‖ ≤
        116 * M * i ^ 4 * Pn + 12 * M * i ^ 3 * (2 * r * Zn + 2 * r * Zn) +
          2 * M * i ^ 2 * (2 * (Zn + r * Gs)) := by
      refine m2.trans ?_
      have hj1 := hpsi1 j
      have hl1 := hpsi1 l
      have hjl2 := hpsi2 j l
      gcongr
    have he1 : 12 * M * i ^ 3 * (2 * r * Zn + 2 * r * Zn) = 48 * M * i ^ 2 * Zn := by
      calc 12 * M * i ^ 3 * (2 * r * Zn + 2 * r * Zn) = 48 * M * (r * i) * i ^ 2 * Zn := by ring
        _ = 48 * M * i ^ 2 * Zn := by rw [hri]; ring
    have he2 : 2 * M * i ^ 2 * (2 * (Zn + r * Gs)) = 4 * M * i ^ 2 * Zn + 4 * M * i * Gs := by
      calc 2 * M * i ^ 2 * (2 * (Zn + r * Gs)) =
            4 * M * i ^ 2 * Zn + 4 * M * (r * i) * i * Gs := by ring
        _ = 4 * M * i ^ 2 * Zn + 4 * M * i * Gs := by rw [hri]; ring
    have hpdM : 1 * ‖physPd2 (Z τ) j l y‖ ≤ M * ‖physPd2 (Z τ) j l y‖ :=
      mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    calc ‖physPd2 (fun y' => tcC0 ν R χy (ϱ y') • Z τ y') j l y +
            physPd2 (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') j l y‖
        ≤ ‖physPd2 (fun y' => tcC0 ν R χy (ϱ y') • Z τ y') j l y‖ +
          ‖physPd2 (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') j l y‖ := norm_add_le _ _
      _ ≤ (14 * M * i ^ 2 * Zn + 2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖) +
            1 * ‖physPd2 (Z τ) j l y‖) +
          (116 * M * i ^ 4 * Pn + 12 * M * i ^ 3 * (2 * r * Zn + 2 * r * Zn) +
            2 * M * i ^ 2 * (2 * (Zn + r * Gs))) := add_le_add m1 m2'
      _ ≤ _ := by rw [he1, he2]; linarith
  have hsum : hessSize (sepWX ν μ R χy T τ) y ≤
      ∑ j : Fin 3, ∑ l : Fin 3,
        (M * ‖physPd2 (Z τ) j l y‖ +
          2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖) +
          (4 * M * i * Gs + 66 * M * i ^ 2 * Zn + 116 * M * i ^ 4 * Pn)) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hjl j l
  have hs1 : (∑ j : Fin 3, ∑ l : Fin 3, M * ‖physPd2 (Z τ) j l y‖) = M * Hs := by
    simp only [Hs, hessSize, Finset.mul_sum]
  have hs2 : (∑ j : Fin 3, ∑ l : Fin 3, 2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖)) =
      12 * M * i * Gs := by
    simp only [Gs, gradSize, Fin.sum_univ_three]
    ring
  have hsum' : hessSize (sepWX ν μ R χy T τ) y ≤
      1800 * M * (Hs + i * Gs + i ^ 2 * Zn + i ^ 4 * Pn) := by
    refine hsum.trans ?_
    simp only [Finset.sum_add_distrib, hs1, hs2, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
    have pH : 0 ≤ M * Hs := by positivity
    have pG : 0 ≤ M * i * Gs := by positivity
    have pZ : 0 ≤ M * i ^ 2 * Zn := by positivity
    have pP : 0 ≤ M * i ^ 4 * Pn := by positivity
    linarith
  have hiL : i ≤ L⁻¹ := inv_anti₀ hL hyann.1
  have hiL2 : i ^ 2 ≤ L⁻¹ ^ 2 := pow_le_pow_left₀ hi0.le hiL 2
  have hiL4 : i ^ 4 ≤ L⁻¹ ^ 4 := pow_le_pow_left₀ hi0.le hiL 4
  refine hsum'.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  gcongr

/-! ## Global pointwise decomposition with `L⁻⁴ * wgxPsi` -/

/-- Complete proof of `SepWXWYPointwiseDecomp` including the `((R * √ν)⁻¹ ^ 4) * wgxPsi`
second-derivative stream-cutoff term. -/
theorem sepWXWYPointwiseDecomp_with_L4 :
    ∀ (σ₁ σ₂ : ℝ), -(1 / 4 : ℝ) < σ₁ → ∀ (χy : ℝ → ℝ), IsStreamCutoff χy →
      ∃ (C : ℝ), 0 ≤ C ∧
        ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
          ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
            ∀ (τ : ℝ) (y : Space),
              (R * Real.sqrt (5 * ν / 4) < ϱ y →
                ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤
                    wgxJet 1 ν μ (ϱ y) T τ y ∧
                  ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖ ≤
                    wgyWJet 1 ν μ (ϱ y) T τ y) ∧
              ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y + hessSize (sepWX ν μ R χy T τ) y) ≤
                ENNReal.ofReal C *
                  (wgxJet 2 ν μ (R * Real.sqrt ν) T τ y +
                    wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
                    ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
                      wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
                    ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
                      wgxJet 0 ν μ (R * Real.sqrt ν) T τ y +
                    ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 2) *
                      wgxJet 0 ν μ (R * Real.sqrt ν) T τ y +
                    ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 3) *
                      wgxPsi ν μ R T τ y +
                    ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 4) *
                      wgxPsi ν μ R T τ y) := by
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨Cx, hCx, hPtX⟩ := wgxPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨Ch, hCh, hAnnH⟩ := sepWX_hess_on_ann hχ
  set C : ℝ := 3 * (Cx + 1) + 9 * (Ch + 1) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨C, hC0, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := by rw [hLdef]; positivity
  refine ⟨fun hb => sepWXWY_beyond_ann hχ hσ hν hν1 hR1 hP0 hμ hT hSM hAx τ y hb, ?_⟩
  by_cases ha : ϱ y < L
  · obtain ⟨hg0, hh0⟩ := sepWX_grad_hess_zero_of_lt hχ hν hR T τ ha
    rw [hg0, hh0, add_zero, ENNReal.ofReal_zero]
    exact zero_le
  · have hL1 : L ≤ ϱ y := not_lt.1 ha
    have hy0 : 0 < ϱ y := lt_of_lt_of_le hL hL1
    set J2 := ‖iteratedFDeriv ℝ 2 (sepX0 ν μ T τ) y‖
    set J1 := ‖iteratedFDeriv ℝ 1 (sepX0 ν μ T τ) y‖
    set J0 := ‖iteratedFDeriv ℝ 0 (sepX0 ν μ T τ) y‖
    have hj2 : wgxJet 2 ν μ L T τ y = ENNReal.ofReal J2 := by
      unfold wgxJet; rw [if_pos hL1, ← ofReal_norm_eq_enorm]
    have hj1 : wgxJet 1 ν μ L T τ y = ENNReal.ofReal J1 := by
      unfold wgxJet; rw [if_pos hL1, ← ofReal_norm_eq_enorm]
    have hj0 : wgxJet 0 ν μ L T τ y = ENNReal.ofReal J0 := by
      unfold wgxJet; rw [if_pos hL1, ← ofReal_norm_eq_enorm]
    have hJ0_eq : ‖sepX0 ν μ T τ y‖ = J0 :=
      (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := sepX0 ν μ T τ) (x := y)).symm
    have hH : TCH ν R μ P T := ⟨hν, hR, lt_of_lt_of_le hσ hμ.1, hP0, hT, hSM, hAx⟩
    -- Bound on `gradSize (sepWX ...)`
    have hgrad_le : ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y) ≤
        ENNReal.ofReal (3 * (Cx + 1)) *
          (wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) := by
      have hg1 : gradSize (sepWX ν μ R χy T τ) y ≤
          3 * ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ := by
        simpa [norm_iteratedFDeriv_one] using
          ZActJetAux.gradSize_le_iteratedFDeriv (sepWX ν μ R χy T τ) y
      have hpX := hPtX ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy0
      rw [← hLdef, wgx_rpow_neg_one, wgx_rpow_neg_three hL] at hpX
      have hCx1 : ENNReal.ofReal (Cx * L⁻¹) ≤
          ENNReal.ofReal (Cx + 1) * ENNReal.ofReal L⁻¹ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [inv_pos.2 hL])
      have hCx3 : ENNReal.ofReal (Cx * L⁻¹ ^ 3) ≤
          ENNReal.ofReal (Cx + 1) * ENNReal.ofReal (L⁻¹ ^ 3) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [pow_pos (inv_pos.2 hL) 3])
      have h1 : ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ ≤
          ENNReal.ofReal (Cx + 1) *
            (wgxJet 1 ν μ L T τ y +
              ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
              ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) := by
        refine hpX.trans ?_
        rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc]
        refine add_le_add (add_le_add ?_ (mul_le_mul_of_nonneg_right hCx1 zero_le))
          (mul_le_mul_of_nonneg_right hCx3 zero_le)
        calc wgxJet 1 ν μ L T τ y = 1 * wgxJet 1 ν μ L T τ y := (one_mul _).symm
          _ ≤ ENNReal.ofReal (Cx + 1) * wgxJet 1 ν μ L T τ y := by
              gcongr
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (by linarith)
      calc ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y)
          ≤ ENNReal.ofReal (3 * ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖) :=
            ENNReal.ofReal_le_ofReal hg1
        _ = ENNReal.ofReal 3 * ENNReal.ofReal ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖ :=
            ENNReal.ofReal_mul (by norm_num)
        _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal (Cx + 1) *
              (wgxJet 1 ν μ L T τ y +
                ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
                ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y)) :=
            mul_le_mul_of_nonneg_left h1 zero_le
        _ = ENNReal.ofReal (3 * (Cx + 1)) *
              (wgxJet 1 ν μ L T τ y +
                ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
                ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    -- Bound on `hessSize (sepWX ...)`
    have hhess_le : ENNReal.ofReal (hessSize (sepWX ν μ R χy T τ) y) ≤
        ENNReal.ofReal (9 * (Ch + 1)) *
          (wgxJet 2 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y) := by
      by_cases hb : R * Real.sqrt (5 * ν / 4) < ϱ y
      · have hh := sepWX_hess_beyond_ann hχ hH τ hb
        calc ENNReal.ofReal (hessSize (sepWX ν μ R χy T τ) y)
            ≤ ENNReal.ofReal (9 * J2) := ENNReal.ofReal_le_ofReal hh
          _ ≤ ENNReal.ofReal (9 * (Ch + 1) * J2) :=
              ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 (sepX0 ν μ T τ) y)])
          _ = ENNReal.ofReal (9 * (Ch + 1)) * wgxJet 2 ν μ L T τ y := by
              rw [ENNReal.ofReal_mul (by positivity), hj2]
          _ ≤ ENNReal.ofReal (9 * (Ch + 1)) *
                (wgxJet 2 ν μ L T τ y +
                  ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
                  ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
                  ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y) := by
              gcongr
              exact le_self_add.trans (le_self_add.trans le_self_add)
      · have hmem : y ∈ streamAnn ν R := ⟨hL1, not_lt.1 hb⟩
        have h56_pos : 0 ≤ 5 * ν / 6 := div_nonneg (mul_nonneg (by norm_num) hν.le) (by norm_num)
        have hrL : R * Real.sqrt (5 * ν / 6) < L := by
          rw [hLdef]
          exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt h56_pos (by linarith)) hR
        have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrL hL1
        have hh := hAnnH hH τ hmem
        rw [← hLdef] at hh
        have hH2 : hessSize (sepX0 ν μ T τ) y ≤ 9 * J2 :=
          ZActJetAux.hessSize_le_iteratedFDeriv (isOpen_lt continuous_const continuous_ϱ)
            (tcb_smooth' hH τ) hyU
        have hG1 : gradSize (sepX0 ν μ T τ) y ≤ 3 * J1 :=
          ZActJetAux.gradSize_le_iteratedFDeriv (sepX0 ν μ T τ) y
        set Pn := |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|
        have hψ : wgxPsi ν μ R T τ y = ENNReal.ofReal Pn := by
          unfold wgxPsi; rw [Set.indicator_of_mem hmem]
        have hh' : hessSize (sepWX ν μ R χy T τ) y ≤
            9 * (Ch + 1) * (J2 + L⁻¹ * J1 + L⁻¹ ^ 2 * J0 + L⁻¹ ^ 4 * Pn) := by
          have b1 : Ch * (hessSize (sepX0 ν μ T τ) y + L⁻¹ * gradSize (sepX0 ν μ T τ) y +
              L⁻¹ ^ 2 * ‖sepX0 ν μ T τ y‖ + L⁻¹ ^ 4 * Pn) ≤
              Ch * (9 * J2 + L⁻¹ * (3 * J1) + L⁻¹ ^ 2 * J0 + L⁻¹ ^ 4 * Pn) := by
            rw [hJ0_eq]
            gcongr
          have pJ2 : 0 ≤ J2 := norm_nonneg _
          have pJ1 : 0 ≤ L⁻¹ * J1 := mul_nonneg (inv_nonneg.2 hL.le) (norm_nonneg _)
          have pJ0 : 0 ≤ L⁻¹ ^ 2 * J0 := mul_nonneg (pow_nonneg (inv_nonneg.2 hL.le) 2) (norm_nonneg _)
          have pPn : 0 ≤ L⁻¹ ^ 4 * Pn := mul_nonneg (pow_nonneg (inv_nonneg.2 hL.le) 4) (abs_nonneg _)
          nlinarith [hh, b1, mul_nonneg hCh pJ2, mul_nonneg hCh pJ1, mul_nonneg hCh pJ0,
            mul_nonneg hCh pPn]
        rw [hj2, hj1, hj0, hψ]
        have pJ2 : 0 ≤ J2 := norm_nonneg _
        have pJ1 : 0 ≤ L⁻¹ * J1 := mul_nonneg (inv_nonneg.2 hL.le) (norm_nonneg _)
        have pJ0 : 0 ≤ L⁻¹ ^ 2 * J0 := mul_nonneg (pow_nonneg (inv_nonneg.2 hL.le) 2) (norm_nonneg _)
        have pPn : 0 ≤ L⁻¹ ^ 4 * Pn := mul_nonneg (pow_nonneg (inv_nonneg.2 hL.le) 4) (abs_nonneg _)
        calc ENNReal.ofReal (hessSize (sepWX ν μ R χy T τ) y)
            ≤ ENNReal.ofReal (9 * (Ch + 1) * (J2 + L⁻¹ * J1 + L⁻¹ ^ 2 * J0 + L⁻¹ ^ 4 * Pn)) :=
              ENNReal.ofReal_le_ofReal hh'
          _ = ENNReal.ofReal (9 * (Ch + 1)) *
                (ENNReal.ofReal J2 +
                  ENNReal.ofReal L⁻¹ * ENNReal.ofReal J1 +
                  ENNReal.ofReal (L⁻¹ ^ 2) * ENNReal.ofReal J0 +
                  ENNReal.ofReal (L⁻¹ ^ 4) * ENNReal.ofReal Pn) := by
              rw [ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_add (by positivity) pPn,
                ENNReal.ofReal_add (by positivity) pJ0,
                ENNReal.ofReal_add pJ2 pJ1,
                ENNReal.ofReal_mul (inv_nonneg.2 hL.le),
                ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hL.le) 2),
                ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hL.le) 4)]
    -- Combine `gradSize` and `hessSize`
    set S := wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
      ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
      ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
      ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
      ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y +
      ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y
    have hS_grad : wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y ≤ S := by
      dsimp only [S]
      have h1 : wgxJet 1 ν μ L T τ y ≤
          wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y :=
        le_add_self.trans le_self_add
      have h2 : wgxJet 1 ν μ L T τ y + ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y ≤
          wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y :=
        (add_le_add h1 le_rfl).trans le_self_add
      exact (add_le_add h2 le_rfl).trans le_self_add
    have hS_hess : wgxJet 2 ν μ L T τ y +
        ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 4) * wgxPsi ν μ R T τ y ≤ S := by
      dsimp only [S]
      have h1 : wgxJet 2 ν μ L T τ y ≤ wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y :=
        le_self_add
      have h2 : wgxJet 2 ν μ L T τ y + ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y ≤
          wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y :=
        (add_le_add h1 le_rfl).trans le_self_add
      have h3 : wgxJet 2 ν μ L T τ y + ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
          ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y ≤
          wgxJet 2 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
            ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
            ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y :=
        (add_le_add h2 le_rfl).trans le_self_add
      exact add_le_add h3 le_rfl
    have hg0 : 0 ≤ gradSize (sepWX ν μ R χy T τ) y :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hh0 : 0 ≤ hessSize (sepWX ν μ R χy T τ) y := hessSize_nonneg _ _
    rw [ENNReal.ofReal_add hg0 hh0]
    calc ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y) +
          ENNReal.ofReal (hessSize (sepWX ν μ R χy T τ) y)
        ≤ ENNReal.ofReal (3 * (Cx + 1)) * S + ENNReal.ofReal (9 * (Ch + 1)) * S :=
          add_le_add (hgrad_le.trans (mul_le_mul_of_nonneg_left hS_grad zero_le))
            (hhess_le.trans (mul_le_mul_of_nonneg_left hS_hess zero_le))
      _ = ENNReal.ofReal C * S := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), ← hCdef]

end SepWXWYDecompAux

theorem sepWXWYPointwiseDecomp : SepWXWYPointwiseDecomp :=
  SepWXWYDecompAux.sepWXWYPointwiseDecomp_with_L4

end UnforcedLeray.Short.PartIIIb.Concrete
end
