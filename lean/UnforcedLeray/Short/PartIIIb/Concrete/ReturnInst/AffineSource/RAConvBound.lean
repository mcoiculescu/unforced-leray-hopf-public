import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradCoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAConvBound.GradId
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_2_meas

/-!
# `PartIII-b:C/asrc/ra/10`: `RAConvBound` (source 5045-5050, 5009-5013)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5045-5050
("The remaining convection difference is exactly `(U-U_raw)·∇ĥ_A + ĥ_A·∇(U-U_raw)`, which is bounded
by `δ_U` times the asserted energy norm") and 5009-5013 (first line of `ret:general-affine-bounds`).

Proof outline:
1. `rac_convCoef_meas` proves `AEStronglyMeasurable (convCoef p μ χf U A) (srcMeasure p.c)` from
   joint `C¹` regularity of `U` and `hLift` (via `measurable_coefOf`) and continuity on `s > 0`
   of the raw convection coefficient (`conv_term1_cont`, `aestronglyMeasurable_of_continuousOn_pos`).
2. `rac_convCoef_norm_le` (`RAConvBound/GradId.lean`) bounds `‖convCoef p μ χf U A (s, x)‖` for
   `s > 0` by `24 δU (‖hAcoef (s, x)‖ + √s ‖gradAcoef (s, x)‖)`.
3. `rac_lintegral_srcMeasure_mul_fst` identifies the `s`-weighted `srcMeasure` integral with the
   `gradMeasure` integral, and `hhatCoefBound` + `gradCoefBound` bound the two `L²` norms by
   `P_ν M(A)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Continuity of `physDivSym (U τ) (W τ) y` for jointly `C¹` fields `U, W`. -/
theorem rac_physDivSym_cont {U W : ℝ → Space → Space}
    (hU : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ 1 (fun x : ℝ × Space => W x.1 x.2)) :
    Continuous (fun x : ℝ × Space => physDivSym (U x.1) (W x.1) x.2) := by
  have heq : (fun x : ℝ × Space => physDivSym (U x.1) (W x.1) x.2) =
      fun x => WithLp.toLp 2 (fun i => ∑ j : Fin 3,
        fderiv ℝ (fun z : ℝ × Space => U z.1 z.2 j * W z.1 z.2 i + W z.1 z.2 j * U z.1 z.2 i)
          x (0, coordinateVector j)) := by
    funext x
    exact ibpcC_div_joint hU hW x.1 x.2
  rw [heq]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_finsetSum _ fun j _ =>
    ((ibpcC_divPsi hU hW i j).continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- `convCoef` is the difference of the chart coefficients of `physDivSym` on `U` and `p.raw`. -/
theorem rac_convCoef_eq_sub (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (U : ℝ → SpatialField)
    (A : ℝ → Mat3) :
    convCoef p μ χf U A =
      coefOf p.ε⁻¹ (fun τ y => physDivSym (U τ) (hLift p.ν p.ε p.c χf A τ) y) -
        coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y) := by
  funext q
  have h1 := coefOf_comb p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A))
    (fun τ y => physDivSym (U τ) (hLift p.ν p.ε p.c χf A τ) y)
    (feLift p.ν μ p.ε p.c χf A) (fun τ y => physGrad (psiLift p.ν p.ε χf A τ) y) q
  have h2 := coefOf_comb p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A))
    (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y)
    (feLift p.ν μ p.ε p.c χf A) (fun τ y => physGrad (psiLift p.ν p.ε χf A τ) y) q
  unfold convCoef rAcoef rAPhys
  rw [Pi.sub_apply, Pi.sub_apply, h1, h2]
  abel

/-- `convCoef` is a.e. strongly measurable on `srcMeasure p.c`. -/
theorem rac_convCoef_meas {as : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf)
    {p : Params} {d dm dp : ℝ} (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    (μ : ℝ) {U : ℝ → SpatialField} {pr : ℝ → Space → ℝ}
    (hU : IsExactProfile p.ν p.period U pr) {A : ℝ → Mat3} (hA : IsAffElem as A) :
    AEStronglyMeasurable (convCoef p μ χf U A) (srcMeasure p.c) := by
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hL : ContDiff ℝ 1 (fun x : ℝ × Space => hLift p.ν p.ε p.c χf A x.1 x.2) := by
    rw [hc]
    exact ((affineLiftReg as χf hχ p.ν μ p.ε p.ν_pos p.ε_pos A hA).1).of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2) := hU.smoothU.of_le (by norm_num)
  have hm1 : Measurable (coefOf p.ε⁻¹ (fun τ y => physDivSym (U τ) (hLift p.ν p.ε p.c χf A τ) y)) :=
    measurable_coefOf _ _ (rac_physDivSym_cont hU1 hL)
  have hm2 : AEStronglyMeasurable
      (coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y))
      (srcMeasure p.c) :=
    aestronglyMeasurable_of_continuousOn_pos (conv_term1_cont p d dm dp hreg _ hL)
  rw [rac_convCoef_eq_sub]
  exact hm1.aestronglyMeasurable.sub hm2

/-- `(ageμ c (-3/2)).withDensity (s) = ageμ c (-1/2)`. -/
theorem rac_ageμ_withDensity_fst (c : ℝ) :
    (ageμ c (-3 / 2)).withDensity (fun p : Chart => ENNReal.ofReal p.1) = ageμ c (-1 / 2) := by
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by unfold UnforcedLeray.Cyl.avgμ; infer_instance
  have hf1 : Measurable (fun z : Chart => ENNReal.ofReal (z.1 ^ (-3 / 2 : ℝ))) :=
    (measurable_ofReal_rpow (-3 / 2)).comp measurable_fst
  have hf2 : Measurable (fun p : Chart => ENNReal.ofReal p.1) :=
    ENNReal.measurable_ofReal.comp measurable_fst
  unfold ageμ
  rw [prod_withDensity_left (measurable_ofReal_rpow (-3 / 2)),
      prod_withDensity_left (measurable_ofReal_rpow (-1 / 2)),
      ← withDensity_mul _ hf1 hf2]
  refine withDensity_congr_ae ?_
  have h1 : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 < s := ae_restrict_mem measurableSet_Ioi
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1] with p (hp : 0 < p.1)
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _)]
  congr 1
  have : p.1 ^ (-1 / 2 : ℝ) = p.1 ^ (-3 / 2 : ℝ) * p.1 ^ (1 : ℝ) := by
    rw [← Real.rpow_add hp]; norm_num
  rw [this, Real.rpow_one]

/-- Integrating `s · F(s, x)` against `srcMeasure c` equals integrating `F` against `gradMeasure c`. -/
theorem rac_lintegral_srcMeasure_mul_fst (c : ℝ) {F : Chart → ℝ≥0∞}
    (hF : AEMeasurable F (gradMeasure c)) :
    ∫⁻ p, ENNReal.ofReal p.1 * F p ∂(srcMeasure c) = ∫⁻ p, F p ∂(gradMeasure c) := by
  have hk : ENNReal.ofReal Real.pi ≠ 0 := by simpa using Real.pi_pos
  have hac : ageμ c (-1 / 2) ≪ gradMeasure c := by
    unfold gradMeasure
    exact Measure.absolutelyContinuous_smul hk
  have hF' : AEMeasurable F ((ageμ c (-3 / 2)).withDensity (fun p : Chart => ENNReal.ofReal p.1)) := by
    rw [rac_ageμ_withDensity_fst]
    exact hF.mono_ac hac
  have hw : Measurable (fun p : Chart => ENNReal.ofReal p.1) :=
    ENNReal.measurable_ofReal.comp measurable_fst
  unfold srcMeasure gradMeasure
  rw [lintegral_smul_measure, lintegral_smul_measure,
    ← rac_ageμ_withDensity_fst, lintegral_withDensity_eq_lintegral_mul₀' hw.aemeasurable hF']
  rfl

/-- Bound on `∫⁻ ‖F‖²` from an `eLpNorm F 2 m ≤ ENNReal.ofReal B` bound. -/
theorem rac_lintegral_sq_le {E : Type*} [NormedAddCommGroup E] {m : Measure Chart}
    {F : Chart → E} {B : ℝ} (hB : 0 ≤ B) (hle : eLpNorm F 2 m ≤ ENNReal.ofReal B) :
    ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m ≤ ENNReal.ofReal (B ^ 2) := by
  have h1 : ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m = ∫⁻ p, ‖F p‖ₑ ^ (ENNReal.toReal 2) ∂m := by
    refine lintegral_congr fun p => ?_
    rw [ENNReal.toReal_ofNat, ← ofReal_norm, ENNReal.rpow_ofNat,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : eLpNorm F 2 m = (∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h1,
      ENNReal.toReal_ofNat]
  calc ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m
      = ((∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ = (eLpNorm F 2 m) ^ (2 : ℝ) := by rw [← h2]
    _ ≤ (ENNReal.ofReal B) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (B ^ 2) := by
        rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hB]

/-- `MemLp F 2 m` and `eLpNorm F 2 m ≤ ENNReal.ofReal B` from `∫⁻ ‖F‖² ≤ ENNReal.ofReal (B²)`. -/
theorem rac_memLp_of_lintegral_sq_le {E : Type*} [NormedAddCommGroup E] {m : Measure Chart}
    {F : Chart → E} {B : ℝ} (hB : 0 ≤ B) (hm : AEStronglyMeasurable F m)
    (hI : ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m ≤ ENNReal.ofReal (B ^ 2)) :
    MemLp F 2 m ∧ eLpNorm F 2 m ≤ ENNReal.ofReal B := by
  have hnorm : eLpNorm F 2 m ≤ ENNReal.ofReal B := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ∫⁻ p, ‖F p‖ₑ ^ (ENNReal.toReal 2) ∂m = ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂m := by
      refine lintegral_congr fun p => ?_
      rw [ENNReal.toReal_ofNat, ← ofReal_norm, ENNReal.rpow_ofNat,
        ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [h2]
    have hsq : ENNReal.ofReal (B ^ 2) = ENNReal.ofReal B ^ (2 : ℝ) := by
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hB]
    calc _ ≤ (ENNReal.ofReal B ^ (2 : ℝ)) ^ (1 / ENNReal.toReal 2) := by
          gcongr
          exact hI.trans hsq.le
      _ = ENNReal.ofReal B := by
          rw [← ENNReal.rpow_mul, ENNReal.toReal_ofNat]; norm_num
  exact ⟨⟨hm, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩, hnorm⟩

/-- **The convection difference bound** (source 5045-5050, 5009-5013). -/
theorem raConvBound (as : ℝ) (χf : ℝ → ℝ) : RAConvBound as χf := by
  intro hχ _K _hK _hKs dm dp hdm
  obtain ⟨Ch, kh, hCh, Hh⟩ := hhatCoefBound as χf hχ
  obtain ⟨Cg, kg, hCg, Hg⟩ := gradCoefBound as χf hχ
  refine ⟨48 * (Ch + Cg), max kh kg, 1, one_pos,
    fun p d hreg hν1 μ _hμ U pr hU δU hδU A hA => ?_⟩
  have hν0 : 0 < p.ν := p.ν_pos
  have hε0 : 0 < p.ε := p.ε_pos
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    have : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hν0.le
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hδ0 : 0 ≤ δU := (norm_nonneg _).trans (hδU 0 0).1
  have hM0 : 0 ≤ affM p.ν χf A := affM_nonneg p.ν χf A
  obtain ⟨hmH, hbH⟩ := Hh p.ν p.ε hν0 hν1 hε0 hε1 A hA
  obtain ⟨hmG, hbG⟩ := Hg p.ν p.ε hν0 hν1 hε0 hε1 A hA
  rw [← hc] at hmH hbH hmG hbG
  set Bh := Ch * p.ν⁻¹ ^ kh * affM p.ν χf A
  set Bg := Cg * p.ν⁻¹ ^ kg * affM p.ν χf A
  have hBh0 : 0 ≤ Bh := by positivity
  have hBg0 : 0 ≤ Bg := by positivity
  have hIH := rac_lintegral_sq_le hBh0 hbH
  have hIG := rac_lintegral_sq_le hBg0 hbG
  have haeH : AEMeasurable (fun q : Chart => ENNReal.ofReal (‖hAcoef p.ν p.ε χf A q‖ ^ 2))
      (srcMeasure p.c) :=
    (hmH.aestronglyMeasurable.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have haeG : AEMeasurable (fun q : Chart => ENNReal.ofReal (‖gradAcoef p.ν p.ε χf A q‖ ^ 2))
      (gradMeasure p.c) :=
    (hmG.aestronglyMeasurable.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hpt : ∀ᵐ q ∂(srcMeasure p.c),
      ENNReal.ofReal (‖convCoef p μ χf U A q‖ ^ 2) ≤
        ENNReal.ofReal ((48 * δU) ^ 2) * ENNReal.ofReal (‖hAcoef p.ν p.ε χf A q‖ ^ 2) +
          ENNReal.ofReal ((48 * δU) ^ 2) *
            (ENNReal.ofReal q.1 * ENNReal.ofReal (‖gradAcoef p.ν p.ε χf A q‖ ^ 2)) := by
    filter_upwards [ae_srcMeasure_fst_pos p.c] with q (hq : 0 < q.1)
    rw [← ENNReal.ofReal_mul (hq.le), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := rac_convCoef_norm_le (μ := μ) hχ hdm hreg hU hδU hA hq q.2
    have hsq1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    set a := ‖hAcoef p.ν p.ε χf A q‖
    set b := Real.sqrt q.1 * ‖gradAcoef p.ν p.ε χf A q‖
    have hb2 : b ^ 2 = q.1 * ‖gradAcoef p.ν p.ε χf A q‖ ^ 2 := by
      simp only [b, mul_pow, Real.sq_sqrt hq.le]
    calc ‖convCoef p μ χf U A q‖ ^ 2 ≤ (24 * δU * (a + b)) ^ 2 := hsq1
      _ ≤ (48 * δU) ^ 2 * a ^ 2 + (48 * δU) ^ 2 * b ^ 2 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a * δU), sq_nonneg (b * δU)]
      _ = (48 * δU) ^ 2 * a ^ 2 + (48 * δU) ^ 2 * (q.1 * ‖gradAcoef p.ν p.ε χf A q‖ ^ 2) := by
          rw [hb2]
  set B := 48 * (Ch + Cg) * p.ν⁻¹ ^ max kh kg * δU * affM p.ν χf A
  have hB0 : 0 ≤ B := by positivity
  refine rac_memLp_of_lintegral_sq_le hB0 (rac_convCoef_meas hχ hreg μ hU hA) ?_
  calc ∫⁻ q, ENNReal.ofReal (‖convCoef p μ χf U A q‖ ^ 2) ∂(srcMeasure p.c)
      ≤ ∫⁻ q, (ENNReal.ofReal ((48 * δU) ^ 2) * ENNReal.ofReal (‖hAcoef p.ν p.ε χf A q‖ ^ 2) +
          ENNReal.ofReal ((48 * δU) ^ 2) *
            (ENNReal.ofReal q.1 * ENNReal.ofReal (‖gradAcoef p.ν p.ε χf A q‖ ^ 2)))
          ∂(srcMeasure p.c) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((48 * δU) ^ 2) *
          ∫⁻ q, ENNReal.ofReal (‖hAcoef p.ν p.ε χf A q‖ ^ 2) ∂(srcMeasure p.c) +
        ENNReal.ofReal ((48 * δU) ^ 2) *
          ∫⁻ q, ENNReal.ofReal q.1 * ENNReal.ofReal (‖gradAcoef p.ν p.ε χf A q‖ ^ 2)
            ∂(srcMeasure p.c) := by
        rw [lintegral_add_left' (haeH.const_mul _),
          lintegral_const_mul'' _ haeH,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((48 * δU) ^ 2) *
          ∫⁻ q, ENNReal.ofReal (‖hAcoef p.ν p.ε χf A q‖ ^ 2) ∂(srcMeasure p.c) +
        ENNReal.ofReal ((48 * δU) ^ 2) *
          ∫⁻ q, ENNReal.ofReal (‖gradAcoef p.ν p.ε χf A q‖ ^ 2) ∂(gradMeasure p.c) := by
        rw [rac_lintegral_srcMeasure_mul_fst p.c haeG]
    _ ≤ ENNReal.ofReal ((48 * δU) ^ 2) * ENNReal.ofReal (Bh ^ 2) +
        ENNReal.ofReal ((48 * δU) ^ 2) * ENNReal.ofReal (Bg ^ 2) := by gcongr
    _ = ENNReal.ofReal ((48 * δU) ^ 2 * Bh ^ 2 + (48 * δU) ^ 2 * Bg ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (B ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hi : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv_iff₀.2 ⟨hν0, hν1⟩
        have pk1 : p.ν⁻¹ ^ kh ≤ p.ν⁻¹ ^ max kh kg := pow_le_pow_right₀ hi (le_max_left _ _)
        have pk2 : p.ν⁻¹ ^ kg ≤ p.ν⁻¹ ^ max kh kg := pow_le_pow_right₀ hi (le_max_right _ _)
        have le1 : Bh ≤ Ch * p.ν⁻¹ ^ max kh kg * affM p.ν χf A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pk1 hCh) hM0
        have le2 : Bg ≤ Cg * p.ν⁻¹ ^ max kh kg * affM p.ν χf A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pk2 hCg) hM0
        have sq1 : Bh ^ 2 ≤ (Ch * p.ν⁻¹ ^ max kh kg * affM p.ν χf A) ^ 2 :=
          pow_le_pow_left₀ hBh0 le1 2
        have sq2 : Bg ^ 2 ≤ (Cg * p.ν⁻¹ ^ max kh kg * affM p.ν χf A) ^ 2 :=
          pow_le_pow_left₀ hBg0 le2 2
        have hsum : Bh ^ 2 + Bg ^ 2 ≤
            ((Ch + Cg) * p.ν⁻¹ ^ max kh kg * affM p.ν χf A) ^ 2 := by
          have h01 : 0 ≤ Ch * p.ν⁻¹ ^ max kh kg * affM p.ν χf A := by positivity
          have h02 : 0 ≤ Cg * p.ν⁻¹ ^ max kh kg * affM p.ν χf A := by positivity
          nlinarith [mul_nonneg h01 h02]
        calc (48 * δU) ^ 2 * Bh ^ 2 + (48 * δU) ^ 2 * Bg ^ 2
            = (48 * δU) ^ 2 * (Bh ^ 2 + Bg ^ 2) := by ring
          _ ≤ (48 * δU) ^ 2 * ((Ch + Cg) * p.ν⁻¹ ^ max kh kg * affM p.ν χf A) ^ 2 :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = B ^ 2 := by simp only [B]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
