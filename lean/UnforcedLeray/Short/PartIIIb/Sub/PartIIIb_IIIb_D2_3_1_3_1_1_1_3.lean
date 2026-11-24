import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L6

/-!
# `farMajorantBound` reduced to two leaves (`PartIII-b:IIIb-D2/3/1/3/1/1/1/3`; `farMajorantBound_of`)

Source `the November 2 reference manuscript`
4155-4186, 3631-3646.  The proof is: Cauchy-Schwarz in `z` against `f(τ') = ‖T(τ',·)‖_{L²_z}`
using the cylinder kernel bound `FarKernelL2` (`‖ |y - l ·|^{-4-n} 1_cyl ‖²_{L²_z} ≲ l⁻¹ ϱ^{-6}`),
then `l = e^s` and the periodic block sum (`l5ChangeVar`, `l5PerSum`, `l5Moment`, already proved).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma farMaj_nonneg' (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ)
    (y : Space) (l : ℝ) (z : Space) (hl : 0 < l) : 0 ≤ farMaj μ T τ n y (l, z) := by
  unfold farMaj IIIa.tensorNorm
  simp only
  positivity

/-- Measurability of the far majorant on `ℝ × Space` (`T` jointly measurable). -/
def FarMeas : Prop :=
  ∀ (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    IIIa.IsSepSource P rOut T → ∀ (τ : ℝ) (n : ℕ) (y : Space), Measurable (farMaj μ T τ n y)

/-- **Cylinder kernel bound** (3631-3646 with `p = 2`, 4155-4186): for `0 < rOut`, `n ≤ 1`, there is
`C ≥ 0` with, for `2 rOut ≤ ϱ y` and `l ∈ (0,1)`,
`∫_z (1_{ϱ z ≤ rOut} |y - l z|^{-(4+n)})² dz ≤ C l⁻¹ ϱ(y)^{-6}`.
(On the cylinder `|y - l z|² ≥ (ϱ y/2)² + (y₂ - l z₂)²`; horizontal area `≤ π rOut²`; the vertical
integral `∫_ℝ (a² + u²)^{-(4+n)} du = c a^{1-2(4+n)}`, `u = l z₂`; `a = ϱ y / 2 ≥ rOut`.) -/
def FarKernelL2 : Prop :=
  ∀ n : ℕ, n ≤ 1 → ∀ rOut : ℝ, 0 < rOut → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, 2 * rOut ≤ ϱ y →
    ∀ l ∈ Ioo (0 : ℝ) 1,
      ∫⁻ z : Space, (Set.indicator {z : Space | ϱ z ≤ rOut}
          (fun z => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ))))) z) ^ (2 : ℝ) ≤
        ENNReal.ofReal (C * l ^ (-1 : ℝ) * ϱ y ^ (-6 : ℝ))

theorem far_single (hMeas : FarMeas) (hKer : FarKernelL2) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hμ : -(1 / 4) < μ.re) (hr : 0 < rOut)
    (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) (n : ℕ)
    (hn : n ≤ 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, 2 * rOut ≤ ϱ y →
      Integrable (farMaj μ T τ n y) sepRho ∧ ∫ p, farMaj μ T τ n y p ∂sepRho ≤ C * ϱ y ^ (-3 : ℝ) := by
  obtain ⟨C0, hC0, hk⟩ := hKer n hn rOut hr
  obtain ⟨hfm, hfp, hfi⟩ := l5Moment P rOut T hP hS hM
  set a : ℝ := 2 * μ.re + 3 / 2 with ha
  have hfin := l5PerSum P hP (fMom T) hfm hfp hfi (a + 1) (by rw [ha]; linarith) τ
  rw [← l5ChangeVar (fMom T) hfm a τ] at hfin
  set I : ℝ≥0∞ := ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)
    with hI
  have hIt : I ≠ ⊤ := hfin.ne
  refine ⟨Real.sqrt C0 * I.toReal, by positivity, fun y hy => ?_⟩
  have hmeas : Measurable (fun p => ENNReal.ofReal (farMaj μ T τ n y p)) :=
    (hMeas μ P rOut T hS τ n y).ennreal_ofReal
  have hnn : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → 0 ≤ farMaj μ T τ n y p := by
    intro p hp
    exact farMaj_nonneg' μ T τ n y p.1 p.2 hp.1
  have hbound : ∫⁻ p, ENNReal.ofReal (farMaj μ T τ n y p) ∂sepRho ≤
      ENNReal.ofReal (Real.sqrt C0 * ϱ y ^ (-3 : ℝ)) * I := by
    calc ∫⁻ p, ENNReal.ofReal (farMaj μ T τ n y p) ∂sepRho
        = ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal (farMaj μ T τ n y (l, z)) := by
          unfold sepRho
          exact lintegral_prod _ hmeas.aemeasurable
      _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt C0 * ϱ y ^ (-3 : ℝ)) *
            (ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)) := by
          refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
          have hl0 : 0 < l := hl.1
          have hpt : ∀ z : Space, ENNReal.ofReal (farMaj μ T τ n y (l, z)) =
              ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
                (Set.indicator {z : Space | ϱ z ≤ rOut}
                  (fun z => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ))))) z *
                  IIIa.srcNorm T (τ + 2 * Real.log l) z) := by
            intro z
            by_cases hz : ϱ z ≤ rOut
            · rw [Set.indicator_of_mem (show z ∈ {z : Space | ϱ z ≤ rOut} from hz)]
              unfold farMaj IIIa.srcNorm
              simp only
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
            · have hz' : rOut < ϱ z := lt_of_not_ge hz
              have hT : T (τ + 2 * Real.log l) z = 0 := hS.support _ _ hz'
              have : IIIa.tensorNorm (T (τ + 2 * Real.log l) z) = 0 := by
                rw [hT]; unfold IIIa.tensorNorm; simp
              unfold farMaj IIIa.srcNorm
              simp [this]
          simp only [hpt]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          have hF : Measurable (IIIa.srcNorm T (τ + 2 * Real.log l)) := by
            unfold IIIa.srcNorm IIIa.tensorNorm
            have hm : ∀ i j, Measurable fun z : Space => T (τ + 2 * Real.log l) z i j :=
              fun i j => (hS.measurable i j).comp (measurable_const.prodMk measurable_id)
            fun_prop
          have hkm : Measurable (Set.indicator {z : Space | ϱ z ≤ rOut}
              (fun z : Space => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ)))))) := by
            have hs : MeasurableSet {z : Space | ϱ z ≤ rOut} := by
              unfold ϱ
              exact measurableSet_le (by fun_prop) measurable_const
            refine Measurable.indicator ?_ hs
            exact ((measurable_const.sub (measurable_const_smul l |>.comp measurable_id)).norm.pow_const _).ennreal_ofReal
          have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
            Real.HolderConjugate.two_two hkm.aemeasurable hF.aemeasurable
          have hK2 := hk y hy l hl
          have hK2' : (∫⁻ z : Space, (Set.indicator {z : Space | ϱ z ≤ rOut}
              (fun z => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ))))) z) ^ (2 : ℝ)) ^
                (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Real.sqrt C0 * l ^ (-(1 / 2 : ℝ)) *
                  ϱ y ^ (-3 : ℝ)) := by
            refine (ENNReal.rpow_le_rpow hK2 (by norm_num)).trans ?_
            have hX : 0 ≤ C0 * l ^ (-1 : ℝ) * ϱ y ^ (-6 : ℝ) := by
              have : 0 ≤ ϱ y := ϱ_nonneg y
              positivity
            rw [ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)]
            refine le_of_eq (congrArg ENNReal.ofReal ?_)
            have hϱ : 0 ≤ ϱ y := ϱ_nonneg y
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_mul hC0]
            have e1 : Real.sqrt (l ^ (-1 : ℝ)) = l ^ (-(1 / 2 : ℝ)) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hl0.le]; norm_num
            have e2 : Real.sqrt (ϱ y ^ (-6 : ℝ)) = ϱ y ^ (-3 : ℝ) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hϱ]; norm_num
            rw [e1, e2]
          calc ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
                ∫⁻ z, Set.indicator {z : Space | ϱ z ≤ rOut}
                  (fun z => ENNReal.ofReal (‖y - l • z‖ ^ (-(4 + (n : ℝ))))) z *
                    IIIa.srcNorm T (τ + 2 * Real.log l) z
              ≤ ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
                (ENNReal.ofReal (Real.sqrt C0 * l ^ (-(1 / 2 : ℝ)) * ϱ y ^ (-3 : ℝ)) *
                  fMom T (τ + 2 * Real.log l)) := by
                refine mul_le_mul' le_rfl (hCS.trans ?_)
                exact mul_le_mul' hK2' le_rfl
            _ = ENNReal.ofReal (Real.sqrt C0 * ϱ y ^ (-3 : ℝ)) *
                (ENNReal.ofReal (l ^ a) * fMom T (τ + 2 * Real.log l)) := by
                have hpw : l ^ (2 * μ.re + 2) * (Real.sqrt C0 * l ^ (-(1 / 2 : ℝ)) *
                    ϱ y ^ (-3 : ℝ)) = (Real.sqrt C0 * ϱ y ^ (-3 : ℝ)) * l ^ a := by
                  have : l ^ a = l ^ (2 * μ.re + 2) * l ^ (-(1 / 2 : ℝ)) := by
                    rw [← Real.rpow_add hl0, ha]; ring_nf
                  rw [this]; ring
                have hϱ : 0 ≤ ϱ y := ϱ_nonneg y
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpw,
                  ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ = ENNReal.ofReal (Real.sqrt C0 * ϱ y ^ (-3 : ℝ)) * I := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfinite : ∫⁻ p, ENNReal.ofReal (farMaj μ T τ n y p) ∂sepRho < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIt.lt_top)
  have hint : Integrable (farMaj μ T τ n y) sepRho := by
    refine ⟨(hMeas μ P rOut T hS τ n y).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖farMaj μ T τ n y p‖ₑ ∂sepRho
        = ∫⁻ p, ENNReal.ofReal (farMaj μ T τ n y p) ∂sepRho := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_mem_Ioo_sepRho] with p hp
          exact Real.enorm_of_nonneg (hnn p hp)
      _ < ⊤ := hfinite
  refine ⟨hint, ?_⟩
  have hnn' : 0 ≤ᵐ[sepRho] farMaj μ T τ n y := by
    filter_upwards [ae_mem_Ioo_sepRho] with p hp using hnn p hp
  rw [integral_eq_lintegral_of_nonneg_ae hnn' hint.aestronglyMeasurable]
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt) hbound
  refine h1.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := ϱ_nonneg y; positivity)]
  ring

theorem farMajorantBound_of (hMeas : FarMeas) (hKer : FarKernelL2) : FarMajorantBound := by
  intro μ rOut P T hμ hr hP hS hM τ
  obtain ⟨C0, hC00, h0⟩ := far_single hMeas hKer μ rOut P T hμ hr hP hS hM τ 0 (by norm_num)
  obtain ⟨C1, hC10, h1⟩ := far_single hMeas hKer μ rOut P T hμ hr hP hS hM τ 1 (by norm_num)
  refine ⟨max C0 C1, fun y hy n hn => ?_⟩
  have hp : 0 ≤ ϱ y ^ (-3 : ℝ) := Real.rpow_nonneg (ϱ_nonneg y) _
  interval_cases n
  · refine ⟨(h0 y hy).1, (h0 y hy).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  · refine ⟨(h1 y hy).1, (h1 y hy).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hp

end UnforcedLeray.Short.PartIIIb.Concrete
