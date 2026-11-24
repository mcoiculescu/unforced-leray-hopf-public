import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.MemLp
import UnforcedLeray.Short.PartIIIa.T16_SepYoung
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_4

/-!
# `PartIII-b:C/cont/WY/3`: `WardYWSubChart`, the young-chart `L²` `μ`-Lipschitz bound of `χ_yW_μ`

Source of record: `the November 2 reference manuscript`
(73 pages), lines 3631-3648 (`sep:young`, `p = q = 2`, `b = 1`, `j = 0`), 2683-2689 (lift identity),
5701-5704.

The `μ`-difference analogue of `wardYWYoungL2_proved` (`Sub/PartIII-b_C_ward_9/L2.lean`): from
`SepWSubDom` at `j = 0` and `IIIa.sepDomYoung` at `p = q = 2, b = 1, a₀ = 2(-1/8) + 2 = 7/4`,
together with `chartYoungTransport` applied to `sepYoungCut R ν μ T - sepYoungCut R ν μ' T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem l2_euclid_re_le (w : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 fun i => (w i).re : Space)‖ ≤ Real.sqrt 3 * ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    intro i
    have h1 : ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ≤ ‖w i‖ := by
      simpa using Complex.abs_re_le_norm (w i)
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (norm_le_pi_norm w i)) 2
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin 3, ‖w‖ ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)
    _ = Real.sqrt 3 * ‖w‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
      norm_num

private theorem norm_iteratedFDeriv_zero_sub {f g : Space → Fin 3 → ℂ} (y : Space) :
    ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 g y‖ = ‖f y - g y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply, ← map_sub]
  exact (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).symm.norm_map _

/-- `sep:young` (`p = q = 2`, `b = 1`, `j = 0`) for the `μ`-difference `sepWre ν μ T - sepWre ν μ' T`,
from `SepWSubDom` at `j = 0` and `IIIa.sepDomYoung` at `a₀ = 2(-1/8) + 2`. -/
private theorem l2_sepWreSubYoung (hSub : SepWSubDom) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν μ μ' R P : ℝ, 0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 < R → 0 < P →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T →
      IIIa.ltauLq P 2 (IIIa.srcNorm T) < ⊤ →
      IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ₑ else 0) ≤
        ENNReal.ofReal (C * (R * Real.sqrt ν)⁻¹ * |μ - μ'|) * IIIa.ltauLq P 2 (IIIa.srcNorm T) := by
  obtain ⟨C0, hC0, hSub0⟩ := hSub 0
  obtain ⟨Cb, hCb, hB'⟩ := _root_.sepDomYoung 0 2 2 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hs : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  set c : ℝ := 1 - Real.sqrt (5 / 6) with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  refine ⟨Real.sqrt 3 * C0 * Cb * c⁻¹, by positivity, ?_⟩
  intro ν μ μ' R P hν hμ hμ' hR hP T hT htop
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrOut : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hrIn : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) = c * (R * Real.sqrt ν) := by
    rw [hrOut, hcdef]; ring
  have hlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have : 0 < c * (R * Real.sqrt ν) := mul_pos hc hrIn
    linarith
  have hnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  set a0 : ℝ := 2 * (-1 / 8 : ℝ) + 2
  have ha0 : 0 ≤ a0 := by norm_num [a0]
  have hδ0 : (1 / 2 : ℝ) ≤ a0 - 2 + 3 / 2 := by norm_num [a0]
  have hgm : Measurable (Function.uncurry (IIIa.srcNorm T)) := IIIa.sepAE_measurable_srcNorm hT
  have hper : ∀ τ z, IIIa.srcNorm T (τ + P) z = IIIa.srcNorm T τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hT.periodic]
  have hdomB := hB' a0 ha0 hδ0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) P (by linarith)
    hP _ hgm hper
  have h0 : IIIa.ltauLq P 2 (IIIa.sepDom a0 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
      (IIIa.srcNorm T)) < ⊤ :=
    hdomB.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top htop)
  have hae := IIIa.sepAE_lt_top_of_ltauLq P 2 two_pos (IIIa.sepAE_measurable_sepDom a0 0 _ hgm) h0
  have he : (-4 - ((0 : ℕ) : ℝ) + 3 / 1 : ℝ) = -1 := by norm_num
  rw [hD, he, Real.rpow_neg_one, mul_inv] at hdomB
  have hK0 : 0 ≤ Real.sqrt 3 * (C0 * |μ - μ'|) := by positivity
  calc IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ₑ else 0)
      ≤ IIIa.ltauLq P 2 (fun τ y => ENNReal.ofReal (Real.sqrt 3 * (C0 * |μ - μ'|)) *
          IIIa.sepDom a0 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (IIIa.srcNorm T) τ y) := by
        refine IIIa.sepAE_ltauLq_mono P 2 two_pos ?_
        filter_upwards [hae] with τ hτ
        filter_upwards [hτ] with y hy
        split_ifs with h
        · have hsub := hSub0 ν μ μ' (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P
            hν hμ hμ' hnn hlt hP T hT τ y h hy
          have hre : sepWre ν μ T τ y - sepWre ν μ' T τ y =
              WithLp.toLp 2 fun i => (IIIa.sepW ν (μ : ℂ) T y τ - IIIa.sepW ν (μ' : ℂ) T y τ) i
                |>.re := by
            ext i
            simp [sepWre]
          have hle1 : ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ₑ ≤
              ENNReal.ofReal (Real.sqrt 3) *
                ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
                  iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero_sub,
              ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hre]
            exact ENNReal.ofReal_le_ofReal (l2_euclid_re_le _)
          calc ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ₑ
              ≤ ENNReal.ofReal (Real.sqrt 3) *
                  (ENNReal.ofReal (C0 * |μ - μ'|) *
                    IIIa.sepDom a0 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
                      (IIIa.srcNorm T) τ y) :=
                hle1.trans (mul_le_mul' le_rfl hsub)
            _ = _ := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        · exact bot_le
    _ = ENNReal.ofReal (Real.sqrt 3 * (C0 * |μ - μ'|)) *
          IIIa.ltauLq P 2 (IIIa.sepDom a0 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
            (IIIa.srcNorm T)) :=
        IIIa.ltauLq_const_mul P 2 two_pos _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (Real.sqrt 3 * (C0 * |μ - μ'|)) *
          (ENNReal.ofReal (Cb * (c⁻¹ * (R * Real.sqrt ν)⁻¹)) * IIIa.ltauLq P 2 (IIIa.srcNorm T)) :=
        by rw [hD]; gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK0]
        congr 2
        ring

private theorem l2_bridge (R c ν : ℝ) (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν)
    (g : Chart → Ten3) (hg : IsOldL2 c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6))
        (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      IsAxiSource (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      (∀ (μ : ℂ) (y : Space) (τ : ℝ),
        IIIa.sepW ν μ (oldPhys R c g) y τ =
          IIIa.sepW ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) y τ) ∧
      IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) ≤
        ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
  have hgm := hg.measurable
  have hpull := chartOfNullPullback R c hR hc _ (ae_iff.1 hg.old)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (R * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf R c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (R ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  have hper : ∀ τ z, oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / R) z =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic R c g τ z]
  have hsupp : ∀ τ z, R * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ R * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  refine ⟨⟨oldCutMeasurable R c _ g hgm, hper, hsupp⟩, ?_,
    fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ, ?_⟩
  · unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold oldCutSrc
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco R c g τ z
      · simp
    · unfold oldCutSrc
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv R c g τ z
      · simp
  · set P : ℝ := 2 * c / R with hPdef
    have hP0 : 0 < P := div_pos (mul_pos two_pos hc) hR
    set I : ℝ≥0∞ := ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) with hI
    have hG2 : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hgm.enorm.pow_const 2
    have hFm : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 :=
      ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG2
    have hAW : ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) = I :=
      ageWeightShift c hc _ hG2
    have hMain := chartPhaseLIntegral R c hR hc _ hFm
    rw [hAW] at hMain
    have hB : ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal P * (ENNReal.ofReal (Real.pi * R ^ 2) * I) := by
      rw [← mul_assoc, ← hMain]
      refine lintegral_mono fun τ => ?_
      rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
      exact lintegral_mono fun z => oldCut_sq_le R c _ g τ z
    have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
    have hX : (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal (Real.pi * R ^ 2) * I := by
      calc _ ≤ (ENNReal.ofReal P)⁻¹ * (ENNReal.ofReal P *
            (ENNReal.ofReal (Real.pi * R ^ 2) * I)) := by gcongr
        _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hPne ENNReal.ofReal_ne_top, one_mul]
    unfold IIIa.ltauLq
    calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (Real.pi * R ^ 2) * I) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
            congr 1
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
          · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
            simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hI]

private theorem l2_meridPt_chartY {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    meridPt (NearInst.chartY R q) = NearInst.chartY R q := by
  have h := wyl_ϱ_chartY hR hs
  unfold meridPt
  rw [h]
  ext i
  fin_cases i <;> simp [NearInst.chartY]

private theorem l2_chartY_not_axis {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    NearInst.chartY R q ∉ axis := by
  intro h
  have h' : NearInst.chartY R q 0 = 0 ∧ NearInst.chartY R q 1 = 0 := h
  have h1 : NearInst.chartY R q 0 = R / Real.sqrt q.1 := by simp [NearInst.chartY]
  have hne : R / Real.sqrt q.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hs).ne'
  exact hne (h1 ▸ h'.1)

private theorem l2_norm_eq {R : ℝ} (hR : 0 < R) {F : ℝ → Space → Space} (hax : AxiNoSwirl F)
    {q : Chart} (hs : 0 < q.1) :
    ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ = Real.sqrt q.1 * ‖coefOf R F q‖ := by
  have hy := l2_chartY_not_axis hR hs
  have hm := l2_meridPt_chartY hR hs
  have h := hax (NearInst.chartTau R q) (NearInst.chartY R q) (mem_univ _) hy
  rw [hm] at h
  have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
  unfold coefOf
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq.le), ← mul_assoc,
    mul_inv_cancel₀ hsq.ne', one_mul]
  conv_lhs => rw [h]
  exact norm_frameL hy _

private theorem l2_cond {R ν : ℝ} (hR : 0 < R) (hν : 0 < ν) {q : Chart} (hs : 0 < q.1)
    (hp : ν * q.1 ≤ 1) :
    R * Real.sqrt ν ≤ Real.sqrt (NearInst.chartY R q 0 ^ 2 + NearInst.chartY R q 1 ^ 2) := by
  have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
  have hY0 : (NearInst.chartY R q) 0 = R / Real.sqrt q.1 := by simp [NearInst.chartY]
  have hY1 : (NearInst.chartY R q) 1 = 0 := by simp [NearInst.chartY]
  rw [hY0, hY1]
  have hpos : 0 ≤ R / Real.sqrt q.1 := by positivity
  rw [show (R / Real.sqrt q.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt q.1) ^ 2 by ring,
    Real.sqrt_sq hpos, le_div_iff₀ hsq]
  have h1 : Real.sqrt ν * Real.sqrt q.1 ≤ 1 := by
    rw [← Real.sqrt_mul hν.le]
    exact Real.sqrt_le_one.2 hp
  nlinarith

private theorem axiNoSwirl_sub {F₁ F₂ : ℝ → Space → Space} (h1 : AxiNoSwirl F₁)
    (h2 : AxiNoSwirl F₂) : AxiNoSwirl (fun τ y => F₁ τ y - F₂ τ y) := by
  intro τ y hy hax
  have e1 := h1 τ y hy hax
  have e2 := h2 τ y hy hax
  dsimp only
  have em : (!₂[(F₁ τ (meridPt y) - F₂ τ (meridPt y)) 0,
      (F₁ τ (meridPt y) - F₂ τ (meridPt y)) 2] : Merid) =
      !₂[F₁ τ (meridPt y) 0, F₁ τ (meridPt y) 2] -
        !₂[F₂ τ (meridPt y) 0, F₂ τ (meridPt y) 2] := by
    ext i
    fin_cases i <;> simp
  rw [em, map_sub, ← e1, ← e2]

/-- **Leaf 3** (`PartIII-b:C/cont/WY/3`): `WardYWSubChart` from `SepWSubDom`. -/
theorem wardYWSubChart_proved (hSub : SepWSubDom) : WardYWSubChart := by
  intro ν R c χy hχy hν hR hc
  obtain ⟨C0, hC0, hY⟩ := l2_sepWreSubYoung hSub
  refine ⟨C0 * (R * Real.sqrt ν)⁻¹, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg
  obtain ⟨hS, hAx, hresp, hB⟩ := l2_bridge R c ν hR hc hν g hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hW1 : wardW ν μ R c g = sepWre ν μ T :=
    funext fun τ => funext fun y => by simp only [wardW, sepWre, hresp]
  have hW2 : wardW ν μ' R c g = sepWre ν μ' T :=
    funext fun τ => funext fun y => by simp only [wardW, sepWre, hresp]
  set N : ℝ≥0∞ := eLpNorm g 2 (ageμ c (-1 / 2)) with hNdef
  have hN : N < ⊤ := hg.memLp.eLpNorm_lt_top
  have hmom : SepMoment (2 * c / R) T :=
    lt_of_le_of_lt hB (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)
  have hsrc := hY ν μ μ' R (2 * c / R) hν hμ hμ' hR hP T hS hmom
  set G : ℝ → Space → Space :=
    fun τ y => sepYoungCut R ν μ T τ y - sepYoungCut R ν μ' T τ y with hGdef
  have hGm : Measurable fun p : ℝ × Space => G p.1 p.2 :=
    (sepYoungCut_measurable R ν μ hν T (fun i j => hS.measurable i j)).sub
      (sepYoungCut_measurable R ν μ' hν T (fun i j => hS.measurable i j))
  have hGax : AxiNoSwirl G :=
    axiNoSwirl_sub
      (sepYoungCut_axi R ν μ (2 * c / R) hR hν (by linarith) T hP hS hmom sepWEquivariance hAx)
      (sepYoungCut_axi R ν μ' (2 * c / R) hR hν (by linarith) T hP hS hmom sepWEquivariance hAx)
  have hGper : ∀ τ y, G (τ + 2 * c / R) y = G τ y := fun τ y => by
    simp only [G, sepYoungCut_periodic _ _ _ _ T hS.periodic]
  have hYT := chartYoungTransport R c ν hR hc hν G hGm hGax hGper
  have hcutG : (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖G τ y‖ₑ else 0) =
      (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ₑ else 0) := by
    funext τ y
    by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    · simp only [G, sepYoungCut, if_pos h]
    · simp only [if_neg h]
  rw [hcutG] at hYT
  set A : ℝ≥0∞ := IIIa.ltauLq (2 * c / R) 2 (fun τ y =>
    if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ₑ else 0)
  have hAle : A ≤ ENNReal.ofReal (C0 * (R * Real.sqrt ν)⁻¹ * |μ - μ'|) *
      (ENNReal.ofReal (Real.sqrt Real.pi * R) * N) := hsrc.trans (by gcongr)
  have hSm : MeasurableSet {p : Chart | ν * p.1 ≤ 1} :=
    measurableSet_le (measurable_fst.const_mul ν) measurable_const
  have hpt : ∀ q : Chart,
      ‖wardYoungRead ν R (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y)
        q‖ₑ ^ (2 : ℝ) ≤
      {p : Chart | ν * p.1 ≤ 1}.indicator (fun p => ‖coefOf R G p‖ₑ ^ (2 : ℝ)) q := by
    intro q
    by_cases hq : ν * q.1 ≤ 1
    · rw [indicator_of_mem (show q ∈ {p : Chart | ν * p.1 ≤ 1} from hq)]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rcases le_or_gt q.1 0 with hs | hs
      · rw [wyl_youngRead_zero_of_nonpos _ hs]
        simp
      · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ _),
          wyl_youngRead_of_young _ hq]
        have hsq0 : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
        have hc1 : R * Real.sqrt ν ≤ Real.sqrt (NearInst.chartY R q 0 ^ 2 +
            NearInst.chartY R q 1 ^ 2) := l2_cond hR hν hs hq
        have hcut : G (NearInst.chartTau R q) (NearInst.chartY R q) =
            sepWre ν μ T (NearInst.chartTau R q) (NearInst.chartY R q) -
              sepWre ν μ' T (NearInst.chartTau R q) (NearInst.chartY R q) := by
          simp only [G, sepYoungCut, if_pos hc1]
        have hnorm := l2_norm_eq hR hGax hs (q := q)
        have hχ := hχy.range (ν * age R (NearInst.chartY R q))
        have hle : ‖wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) -
              wardYoungW ν μ' R c χy g (NearInst.chartTau R q) (NearInst.chartY R q)‖ ≤
            ‖sepWre ν μ T (NearInst.chartTau R q) (NearInst.chartY R q) -
              sepWre ν μ' T (NearInst.chartTau R q) (NearInst.chartY R q)‖ := by
          simp only [wardYoungW, hW1, hW2, ← smul_sub]
          rw [norm_smul, Real.norm_of_nonneg hχ.1]
          exact mul_le_of_le_one_left (norm_nonneg _) hχ.2
        calc (Real.sqrt q.1)⁻¹ *
              ‖wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) -
                wardYoungW ν μ' R c χy g (NearInst.chartTau R q) (NearInst.chartY R q)‖
            ≤ (Real.sqrt q.1)⁻¹ * ‖G (NearInst.chartTau R q) (NearInst.chartY R q)‖ := by
              rw [hcut]
              exact mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hsq0.le)
          _ = ‖coefOf R G q‖ := by
              rw [hnorm, ← mul_assoc, inv_mul_cancel₀ hsq0.ne', one_mul]
    · rw [indicator_of_notMem (show q ∉ {p : Chart | ν * p.1 ≤ 1} from hq)]
      have : wardYoungRead ν R
          (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y) q = 0 := by
        unfold wardYoungRead
        rw [indicator_of_notMem (show q ∉ wardYoungSet ν from hq)]
      rw [this]
      simp
  have hint : ∫⁻ q, ‖wardYoungRead ν R
        (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y) q‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤ ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * A ^ (2 : ℝ) := by
    calc _ ≤ ∫⁻ q, {p : Chart | ν * p.1 ≤ 1}.indicator
          (fun p => ‖coefOf R G p‖ₑ ^ (2 : ℝ)) q ∂(ageμ c (-3 / 2)) :=
          lintegral_mono hpt
      _ = ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R G p‖ₑ ^ (2 : ℝ)
          ∂(ageμ c (-3 / 2)) := lintegral_indicator hSm _
      _ ≤ _ := hYT
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ q, ‖wardYoungRead ν R
        (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y) q‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2))) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * A ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal (1 / (Real.sqrt Real.pi * R)) * A := by
        have key : ENNReal.ofReal (1 / (Real.pi * R ^ 2)) ^ (1 / (2 : ℝ)) =
            ENNReal.ofReal (1 / (Real.sqrt Real.pi * R)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, Real.sqrt_mul Real.pi_pos.le,
            Real.sqrt_sq hR.le, one_div]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), key, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ ENNReal.ofReal (1 / (Real.sqrt Real.pi * R)) *
          (ENNReal.ofReal (C0 * (R * Real.sqrt ν)⁻¹ * |μ - μ'|) *
            (ENNReal.ofReal (Real.sqrt Real.pi * R) * N)) := by gcongr
    _ = ENNReal.ofReal (C0 * (R * Real.sqrt ν)⁻¹ * |μ - μ'|) * N := by
        have hk : 0 < Real.sqrt Real.pi * R := mul_pos (Real.sqrt_pos.2 Real.pi_pos) hR
        rw [← mul_assoc, mul_comm (ENNReal.ofReal (1 / _)) (ENNReal.ofReal _), mul_assoc,
          ← mul_assoc (ENNReal.ofReal (1 / _)), ← ENNReal.ofReal_mul (by positivity),
          one_div, inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one, one_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
