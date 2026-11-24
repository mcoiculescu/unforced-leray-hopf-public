import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Jet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.VSup
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RbForm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_chart

/-!
# Proof of `RepPresGradY2`: the pressure-gradient leaf of background hypothesis (H)
(`PartIII-b:C/rep/3/4/2`)

Source of record: `the November 2 reference manuscript`, lines 5245-5247,
2607-2612, 2641-2642, 2681-2689, 5131-5139.

Proves `RepPresGradY2 D` under `D.RepairStanding dm dp`:
1. Axisymmetry and periodicity of `|∇p|` (`azimuthRot_proved`, `presGradEquivar_of`,
   `IsExactProfile.periodicP`) identify the ring-chart `L²(ringPhysμ)` norm of `|∇p|` with
   `phaseLr P 2 (‖∇p‖)` (`phaseLr_eq_eLpNorm_ringRead`).
2. At every phase `τ`, `∇p(τ) = -(I - ℙ)(U·∇U)(τ)` a.e. (`bgPresLeray_proved`, `bgUL4_proved`,
   `prodL2OfL4_proved` at `IsActualLevel.ball`) and `‖(I - ℙ)F‖₂ ≤ ‖F‖₂`
   (`lerayComplNormLe_proved`), bounding `phaseLr P 2 (‖∇p‖)` by `phaseLr P 2 (‖U·∇U‖)`.
3. Off the axis (`U = V + r_b`), `|U·∇U|` splits into:
   - `(|V| + |r_b|)|DV|`: bounded via `vSupBound`, `ExactSplitII.energy` (`‖r_b‖_∞ ≤ ρ_b ≤ P_ν`),
     and `repVJetY2` (`ε‖DV‖_{Y_2} ≤ P_ν`);
   - `|V||Dr_b|`: bounded via `L^{22/3} × L^{11/4} → L²` Hölder, interpolating `‖V‖_{Y_{22/3}}`
     between `‖V‖_{Y_4}` (`repVBg_vSq`) and `‖V‖_∞` (`vSupBound`) against `RepairDerivBound`;
   - `|r_b||Dr_b|`: bounded via `L⁴ × L⁴ → L²` Hölder, interpolating `r_b` and `Dr_b` between
     `L^{11/4}` and `L^∞` (`ExactSplitII.energy`, `RepairDerivBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.VBgSq

/-! ## 1. `phaseLr` Hölder, `L^∞` interpolation, and slice comparison helpers -/

private theorem phaseLr_two_eq_eLpNorm_ringRead {R c P : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hP : P = 2 * c / R) (F : ℝ → Space → ℝ)
    (hF : Measurable fun x : ℝ × Space => F x.1 x.2)
    (haxi : ∀ (τ : ℝ) (y : Space), y ∉ axis → F τ y = F τ (WithLp.toLp 2 ![ϱ y, 0, y 2]))
    (hper : ∀ (τ : ℝ) (y : Space), F (τ + P) y = F τ y) :
    phaseLr P 2 (fun x => F x.1 x.2) = eLpNorm (ringRead R F) 2 (ringPhysμ R c) := by
  have h := phaseLr_eq_eLpNorm_ringRead hR hc hP (by norm_num : (0 : ℝ) < 2) F hF haxi hper
  simpa using h

private theorem phaseLr_mono_ae {P r : ℝ} (hr : 0 < r) {F G : ℝ × Space → ℝ}
    (h : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure Space), |F (t, y)| ≤ |G (t, y)|) :
    phaseLr P r F ≤ phaseLr P r G := by
  unfold phaseLr
  refine ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (one_div_nonneg.2 hr.le)
  refine lintegral_mono fun t => lintegral_mono_ae ?_
  filter_upwards [h t] with y hy
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hy) hr.le

private theorem phaseLr_two_mul_le {P p0 q0 : ℝ} (hP : 0 < P) (hpq : p0.HolderConjugate q0)
    {F G : ℝ × Space → ℝ} (hF : Measurable F) (hG : Measurable G) :
    phaseLr P 2 (fun x => F x * G x) ≤ phaseLr P (2 * p0) F * phaseLr P (2 * q0) G := by
  have hp1 : 1 < p0 := (Real.holderConjugate_iff.1 hpq).1
  have hq1 : 1 < q0 := (Real.holderConjugate_iff.1 hpq.symm).1
  have hinv : p0⁻¹ + q0⁻¹ = 1 := (Real.holderConjugate_iff.1 hpq).2
  have hp0_pos : 0 < p0 := zero_lt_one.trans hp1
  have hq0_pos : 0 < q0 := zero_lt_one.trans hq1
  set μP : Measure (ℝ × Space) := (volume.restrict (Ioc (0 : ℝ) P)).prod volume
  set f : ℝ × Space → ℝ≥0∞ := fun x => ENNReal.ofReal |F x| ^ (2 : ℝ)
  set g : ℝ × Space → ℝ≥0∞ := fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)
  have hf : Measurable f :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hF)).pow_const 2
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hG)).pow_const 2
  have hfg_eq : (fun x => ENNReal.ofReal |F x * G x| ^ (2 : ℝ)) = f * g := funext fun x => by
    simp only [Pi.mul_apply, f, g]
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hhol := ENNReal.lintegral_mul_le_Lp_mul_Lq μP hpq hf.aemeasurable hg.aemeasurable
  have hI : (∫⁻ x, ENNReal.ofReal |F x * G x| ^ (2 : ℝ) ∂μP) ^ (1 / (2 : ℝ)) ≤
      (∫⁻ x, ENNReal.ofReal |F x| ^ (2 * p0) ∂μP) ^ (1 / (2 * p0)) *
        (∫⁻ x, ENNReal.ofReal |G x| ^ (2 * q0) ∂μP) ^ (1 / (2 * q0)) := by
    have h1 : ∫⁻ x, ENNReal.ofReal |F x * G x| ^ (2 : ℝ) ∂μP ≤
        (∫⁻ x, f x ^ p0 ∂μP) ^ (1 / p0) * (∫⁻ x, g x ^ q0 ∂μP) ^ (1 / q0) := by
      rw [hfg_eq]
      exact hhol
    refine (ENNReal.rpow_le_rpow h1 (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    congr 1
    · rw [← ENNReal.rpow_mul, show (1 / p0) * (1 / (2 : ℝ)) = 1 / (2 * p0) by ring]
      congr 1
      refine lintegral_congr fun x => ?_
      simp only [f, ← ENNReal.rpow_mul]
    · rw [← ENNReal.rpow_mul, show (1 / q0) * (1 / (2 : ℝ)) = 1 / (2 * q0) by ring]
      congr 1
      refine lintegral_congr fun x => ?_
      simp only [g, ← ENNReal.rpow_mul]
  have hP_exp : ENNReal.ofReal P⁻¹ ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal P⁻¹ ^ (1 / (2 * p0)) * ENNReal.ofReal P⁻¹ ^ (1 / (2 * q0)) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne' ENNReal.ofReal_ne_top]
    congr 1
    have : (2 * p0)⁻¹ + (2 * q0)⁻¹ = (2 : ℝ)⁻¹ * (p0⁻¹ + q0⁻¹) := by ring
    simp only [one_div]
    rw [this, hinv, mul_one]
  rw [phaseLr_eq_mul_prod_rpow P 2 (by norm_num) (F := fun x => F x * G x) (hF.mul hG),
    phaseLr_eq_mul_prod_rpow P (2 * p0) (by positivity) hF,
    phaseLr_eq_mul_prod_rpow P (2 * q0) (by positivity) hG, hP_exp]
  calc (ENNReal.ofReal P⁻¹ ^ (1 / (2 * p0)) * ENNReal.ofReal P⁻¹ ^ (1 / (2 * q0))) *
        (∫⁻ x, ENNReal.ofReal |F x * G x| ^ (2 : ℝ) ∂μP) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal P⁻¹ ^ (1 / (2 * p0)) * ENNReal.ofReal P⁻¹ ^ (1 / (2 * q0))) *
          ((∫⁻ x, ENNReal.ofReal |F x| ^ (2 * p0) ∂μP) ^ (1 / (2 * p0)) *
            (∫⁻ x, ENNReal.ofReal |G x| ^ (2 * q0) ∂μP) ^ (1 / (2 * q0))) := by gcongr
    _ = _ := by ring

private theorem phaseLr_interp_ae {P r q M : ℝ} (hr : 0 < r) (hrq : r ≤ q) (hM : 0 ≤ M)
    {F : ℝ × Space → ℝ} (hsup : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure Space), |F (t, y)| ≤ M) :
    phaseLr P q F ≤ ENNReal.ofReal (M ^ ((q - r) / q)) * phaseLr P r F ^ (r / q) := by
  have hq : 0 < q := hr.trans_le hrq
  have hqr : 0 ≤ q - r := sub_nonneg.2 hrq
  set K : ℝ≥0∞ := ENNReal.ofReal (M ^ (q - r))
  have hK_ne : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hin : ∀ t : ℝ, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ q ≤
      K * ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r := by
    intro t
    rw [← lintegral_const_mul' _ _ hK_ne]
    refine lintegral_mono_ae ?_
    filter_upwards [hsup t] with y hy
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_lt_of_le (abs_nonneg (F (t, y))) with h0 | hpos
    · rw [← h0, Real.zero_rpow hq.ne', Real.zero_rpow hr.ne', mul_zero]
    · have heq : |F (t, y)| ^ q = |F (t, y)| ^ (q - r) * |F (t, y)| ^ r := by
        rw [← Real.rpow_add hpos, sub_add_cancel]
      rw [heq]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hy hqr)
        (Real.rpow_nonneg (abs_nonneg _) _)
  have hout : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ q ≤
      K * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r) := by
    calc ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ q
        ≤ ENNReal.ofReal P⁻¹ *
            ∫⁻ t in Ioc (0 : ℝ) P, K * ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r :=
          mul_le_mul_of_nonneg_left (lintegral_mono hin) (by positivity)
      _ = ENNReal.ofReal P⁻¹ * (K * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r) := by
          rw [lintegral_const_mul' _ _ hK_ne]
      _ = K * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r) := by
          ring
  unfold phaseLr
  refine (ENNReal.rpow_le_rpow hout (one_div_nonneg.2 hq.le)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hq.le)]
  congr 1
  · simp only [K]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hM _) (one_div_nonneg.2 hq.le),
      ← Real.rpow_mul hM, mul_one_div]
  · rw [← ENNReal.rpow_mul, show (1 / r) * (r / q) = 1 / q by field_simp]

private theorem phaseLr_interp_self {P r q M : ℝ} (hr : 0 < r) (hrq : r ≤ q) (hM : 0 ≤ M)
    {F : ℝ × Space → ℝ} (hsup : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure Space), |F (t, y)| ≤ M)
    (hLr : phaseLr P r F ≤ ENNReal.ofReal M) :
    phaseLr P q F ≤ ENNReal.ofReal M := by
  have hq : 0 < q := hr.trans_le hrq
  refine (phaseLr_interp_ae hr hrq hM hsup).trans ?_
  rcases eq_or_lt_of_le hM with rfl | hMpos
  · rw [ENNReal.ofReal_zero] at hLr ⊢
    have h0 : phaseLr P r F = 0 := nonpos_iff_eq_zero.1 hLr
    rw [h0, ENNReal.zero_rpow_of_pos (div_pos hr hq), mul_zero]
  · refine (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hLr (div_nonneg hr.le hq.le))
      (by positivity)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg hMpos.le (div_nonneg hr.le hq.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _), ← Real.rpow_add hMpos,
      show (q - r) / q + r / q = 1 by field_simp; ring, Real.rpow_one]

private theorem phaseLr_four_eq_sq_rpow (P : ℝ) (f : ℝ × Space → Space) :
    phaseLr P 4 (fun x => ‖f x‖) = phaseLr P 2 (fun x => ‖f x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  unfold phaseLr
  rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * (1 / 2) = 1 / 4 by norm_num]
  congr 2
  refine lintegral_congr fun t => lintegral_congr fun y => ?_
  dsimp only
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (sq_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
  congr 1
  rw [Real.rpow_two]
  have h4 : (4 : ℝ) = (4 : ℕ) := by norm_num
  rw [h4, Real.rpow_natCast]
  ring

private theorem phaseLr_two_le_of_slice_l2 (P : ℝ) (A B : ℝ → Space → Space)
    (h : ∀ τ : ℝ, eLpNorm (A τ) 2 volume ≤ eLpNorm (B τ) 2 volume) :
    phaseLr P 2 (fun x => ‖A x.1 x.2‖) ≤ phaseLr P 2 (fun x => ‖B x.1 x.2‖) := by
  have hsl : ∀ (g : Space → Space),
      ∫⁻ y : Space, ENNReal.ofReal |‖g y‖| ^ (2 : ℝ) = eLpNorm g 2 volume ^ (2 : ℝ) := by
    intro g
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
      ← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one]
    refine lintegral_congr fun y => ?_
    rw [abs_of_nonneg (norm_nonneg _), ofReal_norm]
  unfold phaseLr
  refine ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by norm_num)
  refine lintegral_mono fun τ => ?_
  rw [hsl (A τ), hsl (B τ)]
  exact ENNReal.rpow_le_rpow (h τ) (by norm_num)

/-! ## 2. Jet norm and ball-level instantiation helpers -/

private theorem norm_fderiv_le_vJetDens (f : Space → Space) (y : Space) :
    ‖fderiv ℝ f y‖ ≤ vJetDens f y := by
  have h1 : ‖fderiv ℝ f y‖ ≤ ∑ j : Fin 3, ‖physPd f j y‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => norm_nonneg _) fun a => ?_
    calc ‖fderiv ℝ f y a‖
        = ‖∑ j : Fin 3, a j • physPd f j y‖ := by
            conv_lhs => rw [eq_sum_coordinateVector a]
            simp [map_sum, physPd]
      _ ≤ ∑ j : Fin 3, ‖a j • physPd f j y‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ‖a‖ * ‖physPd f j y‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le a j) (norm_nonneg _)
      _ = (∑ j : Fin 3, ‖physPd f j y‖) * ‖a‖ := by rw [← Finset.mul_sum]; ring
  unfold vJetDens
  have h2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 f j l y‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => norm_nonneg _
  linarith

private theorem measurable_pwN1 (f : ℝ → Space → Space)
    (hf : Measurable fun x : ℝ × Space => f x.1 x.2)
    (hC2 : ∀ τ, ContDiffOn ℝ 2 (f τ) axisᶜ) :
    Measurable (pwN1 f) := by
  have hdiff : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (f τ) y :=
    fun τ y hy => rby_diff_of_contDiffOn (hC2 τ) hy
  have hc : Continuous fun m : Fin 3 → Space => ‖jet1 m‖ :=
    (continuous_norm (E := Space →L[ℝ] Space)).comp continuous_jet1
  refine hc.measurable.comp (measurable_pi_lambda _ fun j => ?_)
  unfold pw1
  exact rby_meas_pw1 f hf hdiff (coordinateVector j)

private theorem eventually_of_atBallLevels (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    {Φ : UnforcedLeray.Cons.C03.Concrete.Params → (ℝ → SpatialField) → (ℝ → SpatialField) →
      (ℝ → Space → ℝ) → Prop}
    (hΦ : AtBallLevels Φ) :
    ∀ᶠ n : ℕ in atTop,
      Φ ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.level n).pres := by
  obtain ⟨ν₀, hν₀, H⟩ := hΦ D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos hst.planar.eigenpair
    D.K.m0 hst.m0_pos dm dp hst.dm_pos hst.m0_ball D.K.C0 D.K.k0 hst.C0_pos
  filter_upwards [hst.actual, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀)] with
    n hn hν
  set L := D.level n
  have hP : (L.params D.Pl).period = 2 * L.ε * cOf L.ν := by
    rw [UnforcedLeray.Cons.C03.Concrete.Params.period_eq]
    change 2 * cOf L.ν / L.ε⁻¹ = 2 * L.ε * cOf L.ν
    rw [div_inv_eq_mul]; ring
  have hprof : IsExactProfile (L.params D.Pl).ν (L.params D.Pl).period
      (fun τ y => L.V τ y + L.rb τ y) L.pres := by
    rw [hP]
    exact hn.profile
  exact H (L.params D.Pl) _ hn.regime hν rfl rfl L.V L.rb L.pres hn.ball hprof

/-! ## 3. Convective `Y_2` bound at a fixed level -/

private theorem phaseLr_V22_bound {ε P Bv : ℝ} {V : ℝ → SpatialField}
    (hε : 0 < ε) (hBv1 : 1 ≤ Bv)
    (hV_pt : ∀ τ y, ‖V τ y‖ ≤ Bv)
    (hVsq_Y2 : ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖V x.1 x.2‖ ^ 2) ≤ ENNReal.ofReal Bv) :
    phaseLr P (22 / 3) (fun x => ‖V x.1 x.2‖) ≤
      ENNReal.ofReal (Bv * (ε⁻¹) ^ (3 / 11 : ℝ)) := by
  have hBv0 : 0 ≤ Bv := zero_le_one.trans hBv1
  have hV4 : phaseLr P 4 (fun x => ‖V x.1 x.2‖) ≤
      ENNReal.ofReal ((ε⁻¹ * Bv) ^ (1 / 2 : ℝ)) := by
    have hinv : ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε.le), inv_mul_cancel₀ hε.ne', ENNReal.ofReal_one]
    have hsq_le : phaseLr P 2 (fun x => ‖V x.1 x.2‖ ^ 2) ≤ ENNReal.ofReal (ε⁻¹ * Bv) := by
      calc phaseLr P 2 (fun x => ‖V x.1 x.2‖ ^ 2)
          = (ENNReal.ofReal ε⁻¹ * ENNReal.ofReal ε) *
              phaseLr P 2 (fun x => ‖V x.1 x.2‖ ^ 2) := by rw [hinv, one_mul]
        _ = ENNReal.ofReal ε⁻¹ *
              (ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖V x.1 x.2‖ ^ 2)) := mul_assoc _ _ _
        _ ≤ ENNReal.ofReal ε⁻¹ * ENNReal.ofReal Bv :=
              mul_le_mul_of_nonneg_left hVsq_Y2 zero_le
        _ = ENNReal.ofReal (ε⁻¹ * Bv) := (ENNReal.ofReal_mul (inv_nonneg.2 hε.le)).symm
    rw [phaseLr_four_eq_sq_rpow P (fun x => V x.1 x.2)]
    exact (ENNReal.rpow_le_rpow hsq_le (by norm_num)).trans
      (le_of_eq (ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (inv_nonneg.2 hε.le) hBv0) (by norm_num)))
  have hint := phaseLr_interp_ae (P := P) (r := 4) (q := 22 / 3) (M := Bv) (by norm_num)
    (by norm_num) hBv0 (F := fun x => ‖V x.1 x.2‖) fun t =>
    Eventually.of_forall fun y => by rw [abs_of_nonneg (norm_nonneg _)]; exact hV_pt t y
  have hexp1 : ((22 / 3 : ℝ) - 4) / (22 / 3) = 5 / 11 := by norm_num
  have hexp2 : (4 : ℝ) / (22 / 3) = 6 / 11 := by norm_num
  rw [hexp1, hexp2] at hint
  refine hint.trans ?_
  refine (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hV4 (by norm_num)) zero_le).trans ?_
  have h1 : 0 ≤ (ε⁻¹ * Bv) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (inv_nonneg.2 hε.le) hBv0) _
  have h2 : 0 ≤ Bv ^ (5 / 11 : ℝ) := Real.rpow_nonneg hBv0 _
  rw [ENNReal.ofReal_rpow_of_nonneg h1 (by norm_num), ← ENNReal.ofReal_mul h2]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.rpow_mul (mul_nonneg (inv_nonneg.2 hε.le) hBv0),
    show (1 / (2 : ℝ)) * (6 / 11) = 3 / 11 by norm_num,
    Real.mul_rpow (inv_nonneg.2 hε.le) hBv0]
  calc Bv ^ (5 / 11 : ℝ) * ((ε⁻¹) ^ (3 / 11 : ℝ) * Bv ^ (3 / 11 : ℝ))
      = (Bv ^ (5 / 11 : ℝ) * Bv ^ (3 / 11 : ℝ)) * (ε⁻¹) ^ (3 / 11 : ℝ) := by ring
    _ = Bv ^ (8 / 11 : ℝ) * (ε⁻¹) ^ (3 / 11 : ℝ) := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hBv1)]
        norm_num
    _ ≤ Bv ^ (1 : ℝ) * (ε⁻¹) ^ (3 / 11 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hBv1 (by norm_num))
          (Real.rpow_nonneg (inv_nonneg.2 hε.le) _)
    _ = Bv * (ε⁻¹) ^ (3 / 11 : ℝ) := by rw [Real.rpow_one]

private theorem conv_pointwise_split {P Bv ρb : ℝ} {U V rb : ℝ → SpatialField}
    (hBv0 : 0 ≤ Bv) (hρb0 : 0 ≤ ρb)
    (hU_eq : ∀ τ y, U τ y = V τ y + rb τ y)
    (hC2_V : ∀ τ, ContDiffOn ℝ 2 (V τ) axisᶜ)
    (hC2_rb : ∀ τ, ContDiffOn ℝ 2 (rb τ) axisᶜ)
    (hV_pt : ∀ τ y, ‖V τ y‖ ≤ Bv)
    (hrb_ae : ∀ τ : ℝ, ∀ᵐ y ∂(volume : Measure Space), ‖rb τ y‖ ≤ ρb) :
    phaseLr P 2 (fun x => ‖fderiv ℝ (U x.1) x.2 (U x.1 x.2)‖) ≤
      phaseLr P 2 (fun x =>
        ((Bv + ρb) * pwN1 V x + ‖V x.1 x.2‖ * pwN1 rb x) + pwN1 rb x * ‖rb x.1 x.2‖) := by
  have hae_off : ∀ᵐ y ∂(volume : Measure Space), y ∉ axis :=
    UnforcedLeray.Sob.ae_offAxis.mono fun y hy => (UnforcedLeray.Axi.mem_offAxis_iff y).1 hy
  refine phaseLr_mono_ae (by norm_num) fun τ => ?_
  filter_upwards [hae_off, hrb_ae τ] with y hy hrb_y
  have hUτ : U τ = V τ + rb τ := funext fun z => hU_eq τ z
  have hdV : DifferentiableAt ℝ (V τ) y := rby_diff_of_contDiffOn (hC2_V τ) hy
  have hdrb : DifferentiableAt ℝ (rb τ) y := rby_diff_of_contDiffOn (hC2_rb τ) hy
  have hfd : fderiv ℝ (U τ) y = fderiv ℝ (V τ) y + fderiv ℝ (rb τ) y := by
    rw [hUτ]
    exact (hdV.hasFDerivAt.add hdrb.hasFDerivAt).fderiv
  have hpwV : ‖fderiv ℝ (V τ) y‖ = pwN1 V (τ, y) := by
    unfold pwN1; rw [rby_pw1_eq V τ hy]
  have hpwRb : ‖fderiv ℝ (rb τ) y‖ = pwN1 rb (τ, y) := by
    unfold pwN1; rw [rby_pw1_eq rb τ hy]
  have h0V : 0 ≤ pwN1 V (τ, y) := by unfold pwN1; exact norm_nonneg _
  have h0Rb : 0 ≤ pwN1 rb (τ, y) := by unfold pwN1; exact norm_nonneg _
  have hT_nn : 0 ≤ ((Bv + ρb) * pwN1 V (τ, y) + ‖V τ y‖ * pwN1 rb (τ, y)) +
      pwN1 rb (τ, y) * ‖rb τ y‖ :=
    add_nonneg (add_nonneg (mul_nonneg (add_nonneg hBv0 hρb0) h0V)
      (mul_nonneg (norm_nonneg _) h0Rb)) (mul_nonneg h0Rb (norm_nonneg _))
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hT_nn]
  calc ‖fderiv ℝ (U τ) y (U τ y)‖
      ≤ ‖fderiv ℝ (U τ) y‖ * ‖U τ y‖ := (fderiv ℝ (U τ) y).le_opNorm _
    _ ≤ (‖fderiv ℝ (V τ) y‖ + ‖fderiv ℝ (rb τ) y‖) * (‖V τ y‖ + ‖rb τ y‖) := by
        rw [hfd, hU_eq τ y]
        exact mul_le_mul (norm_add_le _ _) (norm_add_le _ _) (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ((‖V τ y‖ + ‖rb τ y‖) * pwN1 V (τ, y) +
          ‖V τ y‖ * pwN1 rb (τ, y)) + pwN1 rb (τ, y) * ‖rb τ y‖ := by
        rw [hpwV, hpwRb]; ring
    _ ≤ ((Bv + ρb) * pwN1 V (τ, y) +
          ‖V τ y‖ * pwN1 rb (τ, y)) + pwN1 rb (τ, y) * ‖rb τ y‖ :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right (add_le_add (hV_pt τ y) hrb_y) h0V) le_rfl) le_rfl

private theorem conv_T1_bound {ε P Bv ρb Cbv C0 Cjet a : ℝ} {kbv k0 kjet k : ℕ}
    {V : ℝ → SpatialField}
    (hCbv1 : 1 ≤ Cbv) (hBv : Bv = Cbv * a ^ kbv) (hBv0 : 0 ≤ Bv)
    (hC0 : 0 < C0) (hCjet : 0 ≤ Cjet) (ha1 : 1 ≤ a)
    (hρb0 : 0 ≤ ρb) (hρb_le : ρb ≤ C0 * a ^ k0)
    (hk1 : max kbv k0 + kjet ≤ k)
    (hdV_Y2 : ENNReal.ofReal ε * phaseLr P 2 (pwN1 V) ≤ ENNReal.ofReal (Cjet * a ^ kjet)) :
    ENNReal.ofReal ε * phaseLr P 2 (fun x => (Bv + ρb) * pwN1 V x) ≤
      ENNReal.ofReal ((Cbv + C0) * Cjet * a ^ k) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha1
  have hsum0 : 0 ≤ Bv + ρb := add_nonneg hBv0 hρb0
  have hsm : phaseLr P 2 (fun x => (Bv + ρb) * pwN1 V x) ≤
      ENNReal.ofReal (Bv + ρb) * phaseLr P 2 (pwN1 V) := by
    refine phaseLr_mono_smul (by norm_num) hsum0 fun x => ?_
    have h0 : 0 ≤ pwN1 V x := by unfold pwN1; exact norm_nonneg _
    rw [abs_of_nonneg (mul_nonneg hsum0 h0), abs_of_nonneg h0]
  calc ENNReal.ofReal ε * phaseLr P 2 (fun x => (Bv + ρb) * pwN1 V x)
      ≤ ENNReal.ofReal ε * (ENNReal.ofReal (Bv + ρb) * phaseLr P 2 (pwN1 V)) :=
        mul_le_mul_of_nonneg_left hsm zero_le
    _ = ENNReal.ofReal (Bv + ρb) * (ENNReal.ofReal ε * phaseLr P 2 (pwN1 V)) :=
        mul_left_comm _ _ _
    _ ≤ ENNReal.ofReal (Bv + ρb) * ENNReal.ofReal (Cjet * a ^ kjet) :=
        mul_le_mul_of_nonneg_left hdV_Y2 zero_le
    _ = ENNReal.ofReal ((Bv + ρb) * (Cjet * a ^ kjet)) :=
        (ENNReal.ofReal_mul hsum0).symm
    _ ≤ ENNReal.ofReal ((Cbv + C0) * Cjet * a ^ k) := by
        refine ENNReal.ofReal_le_ofReal ?_
        set km : ℕ := max kbv k0
        have hCbv0 : 0 ≤ Cbv := zero_le_one.trans hCbv1
        have he1 : Bv ≤ Cbv * a ^ km := by
          rw [hBv]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 (le_max_left _ _)) hCbv0
        have he2 : ρb ≤ C0 * a ^ km :=
          hρb_le.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 (le_max_right _ _)) hC0.le)
        have hsum : Bv + ρb ≤ (Cbv + C0) * a ^ km :=
          (add_le_add he1 he2).trans_eq (by ring)
        calc (Bv + ρb) * (Cjet * a ^ kjet)
            ≤ ((Cbv + C0) * a ^ km) * (Cjet * a ^ kjet) :=
              mul_le_mul_of_nonneg_right hsum (mul_nonneg hCjet (pow_nonneg ha0 _))
          _ = (Cbv + C0) * Cjet * a ^ (km + kjet) := by rw [pow_add]; ring
          _ ≤ (Cbv + C0) * Cjet * a ^ k :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 hk1)
                (mul_nonneg (add_nonneg hCbv0 hC0.le) hCjet)

private theorem conv_T2_bound {ε P Bv Cbv Cdr a rho : ℝ} {kbv kdr k : ℕ}
    {V rb : ℝ → SpatialField}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPpos : 0 < P)
    (hCbv1 : 1 ≤ Cbv) (hBv : Bv = Cbv * a ^ kbv) (hBv0 : 0 ≤ Bv)
    (hCdr : 0 ≤ Cdr) (ha1 : 1 ≤ a) (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1)
    (hk2 : kbv + kdr ≤ k)
    (hm_V : Measurable fun x : ℝ × Space => ‖V x.1 x.2‖)
    (hm_drb : Measurable (pwN1 rb))
    (hV22 : phaseLr P (22 / 3) (fun x => ‖V x.1 x.2‖) ≤
      ENNReal.ofReal (Bv * (ε⁻¹) ^ (3 / 11 : ℝ)))
    (hdrb_Y11 : phaseLr P (11 / 4) (pwN1 rb) ≤ ENNReal.ofReal (Cdr * a ^ kdr * rho)) :
    ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖V x.1 x.2‖ * pwN1 rb x) ≤
      ENNReal.ofReal (Cbv * Cdr * a ^ k) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha1
  set Mdr : ℝ := Cdr * a ^ kdr * rho
  have hV22_0 : 0 ≤ Bv * (ε⁻¹) ^ (3 / 11 : ℝ) :=
    mul_nonneg hBv0 (Real.rpow_nonneg (inv_nonneg.2 hε.le) _)
  have hpq : (11 / 3 : ℝ).HolderConjugate (11 / 8) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hhol := phaseLr_two_mul_le hPpos hpq hm_V hm_drb
  have h2p : (2 : ℝ) * (11 / 3) = 22 / 3 := by norm_num
  have h2q : (2 : ℝ) * (11 / 8) = 11 / 4 := by norm_num
  rw [h2p, h2q] at hhol
  have hprod : phaseLr P 2 (fun x => ‖V x.1 x.2‖ * pwN1 rb x) ≤
      ENNReal.ofReal (Bv * (ε⁻¹) ^ (3 / 11 : ℝ)) * ENNReal.ofReal Mdr :=
    hhol.trans (mul_le_mul hV22 hdrb_Y11 zero_le zero_le)
  calc ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖V x.1 x.2‖ * pwN1 rb x)
      ≤ ENNReal.ofReal ε *
          (ENNReal.ofReal (Bv * (ε⁻¹) ^ (3 / 11 : ℝ)) * ENNReal.ofReal Mdr) :=
        mul_le_mul_of_nonneg_left hprod zero_le
    _ = ENNReal.ofReal (ε * (Bv * (ε⁻¹) ^ (3 / 11 : ℝ)) * Mdr) := by
        rw [← ENNReal.ofReal_mul hV22_0, ← ENNReal.ofReal_mul hε.le]
        congr 1; ring
    _ ≤ ENNReal.ofReal (Cbv * Cdr * a ^ k) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have heps : ε * (ε⁻¹) ^ (3 / 11 : ℝ) ≤ 1 := by
          calc ε * (ε⁻¹) ^ (3 / 11 : ℝ)
              = ε ^ (1 : ℝ) * ε ^ (-(3 / 11 : ℝ)) := by
                rw [Real.rpow_one, Real.inv_rpow hε.le, Real.rpow_neg hε.le]
            _ = ε ^ (8 / 11 : ℝ) := by
                rw [← Real.rpow_add hε]
                norm_num
            _ ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
        calc ε * (Bv * (ε⁻¹) ^ (3 / 11 : ℝ)) * Mdr
            = (Bv * (Cdr * a ^ kdr)) * ((ε * (ε⁻¹) ^ (3 / 11 : ℝ)) * rho) := by
              simp only [Mdr]; ring
          _ ≤ (Bv * (Cdr * a ^ kdr)) * (1 * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul heps hρ1 hρ0 zero_le_one)
                (mul_nonneg hBv0 (mul_nonneg hCdr (pow_nonneg ha0 _)))
          _ = Cbv * Cdr * a ^ (kbv + kdr) := by rw [hBv, pow_add]; ring
          _ ≤ Cbv * Cdr * a ^ k :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 hk2)
                (mul_nonneg (zero_le_one.trans hCbv1) hCdr)

private theorem conv_T3_bound {ε P ρb C0 Cdr a rho : ℝ} {k0 kdr k : ℕ}
    {rb : ℝ → SpatialField}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPpos : 0 < P)
    (hC0 : 0 < C0) (hCdr : 0 ≤ Cdr) (ha1 : 1 ≤ a)
    (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1)
    (hρb0 : 0 ≤ ρb) (hρb_le : ρb ≤ C0 * a ^ k0)
    (hk3 : kdr + k0 ≤ k)
    (hm_rb : Measurable fun x : ℝ × Space => ‖rb x.1 x.2‖)
    (hm_drb : Measurable (pwN1 rb))
    (hrb_ae : ∀ τ : ℝ, ∀ᵐ y ∂(volume : Measure Space), ‖rb τ y‖ ≤ ρb)
    (hrb_Y11 : phaseLr P (11 / 4) (fun x => ‖rb x.1 x.2‖) ≤ ENNReal.ofReal ρb)
    (hdrb_pt : ∀ τ y, pwN1 rb (τ, y) ≤ Cdr * a ^ kdr * rho)
    (hdrb_Y11 : phaseLr P (11 / 4) (pwN1 rb) ≤ ENNReal.ofReal (Cdr * a ^ kdr * rho)) :
    ENNReal.ofReal ε * phaseLr P 2 (fun x => pwN1 rb x * ‖rb x.1 x.2‖) ≤
      ENNReal.ofReal (Cdr * C0 * a ^ k) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha1
  set Mdr : ℝ := Cdr * a ^ kdr * rho
  have hMdr0 : 0 ≤ Mdr := mul_nonneg (mul_nonneg hCdr (pow_nonneg ha0 _)) hρ0
  have hMdr_le : Mdr ≤ Cdr * a ^ kdr := by
    calc Cdr * a ^ kdr * rho
        ≤ Cdr * a ^ kdr * 1 :=
          mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hCdr (pow_nonneg ha0 _))
      _ = Cdr * a ^ kdr := mul_one _
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hhol := phaseLr_two_mul_le hPpos hpq hm_drb hm_rb
  have h22 : (2 : ℝ) * 2 = 4 := by norm_num
  rw [h22] at hhol
  have hdrb4 : phaseLr P 4 (pwN1 rb) ≤ ENNReal.ofReal Mdr :=
    phaseLr_interp_self (r := 11 / 4) (by norm_num) (by norm_num) hMdr0
      (fun t => Eventually.of_forall fun y => by
        have h0 : 0 ≤ pwN1 rb (t, y) := by unfold pwN1; exact norm_nonneg _
        rw [abs_of_nonneg h0]; exact hdrb_pt t y) hdrb_Y11
  have hrb4 : phaseLr P 4 (fun x => ‖rb x.1 x.2‖) ≤ ENNReal.ofReal ρb :=
    phaseLr_interp_self (r := 11 / 4) (by norm_num) (by norm_num) hρb0
      (fun t => (hrb_ae t).mono fun y hy => by rw [abs_of_nonneg (norm_nonneg _)]; exact hy)
      hrb_Y11
  have hprod : phaseLr P 2 (fun x => pwN1 rb x * ‖rb x.1 x.2‖) ≤
      ENNReal.ofReal Mdr * ENNReal.ofReal ρb :=
    hhol.trans (mul_le_mul hdrb4 hrb4 zero_le zero_le)
  calc ENNReal.ofReal ε * phaseLr P 2 (fun x => pwN1 rb x * ‖rb x.1 x.2‖)
      ≤ ENNReal.ofReal ε * (ENNReal.ofReal Mdr * ENNReal.ofReal ρb) :=
        mul_le_mul_of_nonneg_left hprod zero_le
    _ = ENNReal.ofReal (ε * (Mdr * ρb)) := by
        rw [← ENNReal.ofReal_mul hMdr0, ← ENNReal.ofReal_mul hε.le]
    _ ≤ ENNReal.ofReal (Cdr * C0 * a ^ k) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ε * (Mdr * ρb)
            ≤ 1 * ((Cdr * a ^ kdr) * (C0 * a ^ k0)) :=
              mul_le_mul hε1
                (mul_le_mul hMdr_le hρb_le hρb0 (mul_nonneg hCdr (pow_nonneg ha0 _)))
                (mul_nonneg hMdr0 hρb0) zero_le_one
          _ = Cdr * C0 * a ^ (kdr + k0) := by rw [pow_add]; ring
          _ ≤ Cdr * C0 * a ^ k :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 hk3)
                (mul_nonneg hCdr hC0.le)

private theorem conv_phaseLr_bound {ε P Bv ρb Cbv C0 Cjet Cdr a rho : ℝ}
    {kbv k0 kjet kdr k : ℕ} {U V rb : ℝ → SpatialField}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPpos : 0 < P)
    (hCbv1 : 1 ≤ Cbv) (hBv : Bv = Cbv * a ^ kbv)
    (hC0 : 0 < C0) (hCjet : 0 ≤ Cjet) (hCdr : 0 ≤ Cdr)
    (ha1 : 1 ≤ a) (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1)
    (hρb0 : 0 ≤ ρb) (hρb_le : ρb ≤ C0 * a ^ k0)
    (hk1 : max kbv k0 + kjet ≤ k) (hk2 : kbv + kdr ≤ k) (hk3 : kdr + k0 ≤ k)
    (hU_eq : ∀ τ y, U τ y = V τ y + rb τ y)
    (hcont_V : Continuous fun x : ℝ × Space => V x.1 x.2)
    (hcont_rb : Continuous fun x : ℝ × Space => rb x.1 x.2)
    (hC2_V : ∀ τ, ContDiffOn ℝ 2 (V τ) axisᶜ)
    (hC2_rb : ∀ τ, ContDiffOn ℝ 2 (rb τ) axisᶜ)
    (hV_pt : ∀ τ y, ‖V τ y‖ ≤ Bv)
    (hrb_ae : ∀ τ : ℝ, ∀ᵐ y ∂(volume : Measure Space), ‖rb τ y‖ ≤ ρb)
    (hrb_Y11 : phaseLr P (11 / 4) (fun x => ‖rb x.1 x.2‖) ≤ ENNReal.ofReal ρb)
    (hdrb_pt : ∀ τ y, pwN1 rb (τ, y) ≤ Cdr * a ^ kdr * rho)
    (hdrb_Y11 : phaseLr P (11 / 4) (pwN1 rb) ≤ ENNReal.ofReal (Cdr * a ^ kdr * rho))
    (hdV_Y2 : ENNReal.ofReal ε * phaseLr P 2 (pwN1 V) ≤ ENNReal.ofReal (Cjet * a ^ kjet))
    (hVsq_Y2 : ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖V x.1 x.2‖ ^ 2) ≤ ENNReal.ofReal Bv) :
    ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖fderiv ℝ (U x.1) x.2 (U x.1 x.2)‖) ≤
      ENNReal.ofReal (((Cbv + C0) * Cjet + Cbv * Cdr + Cdr * C0) * a ^ k) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha1
  have hCbv0 : 0 ≤ Cbv := zero_le_one.trans hCbv1
  have hBv1 : 1 ≤ Bv := by rw [hBv]; exact one_le_mul_of_one_le_of_one_le hCbv1 (one_le_pow₀ ha1)
  have hBv0 : 0 ≤ Bv := zero_le_one.trans hBv1
  have hm_V : Measurable fun x : ℝ × Space => ‖V x.1 x.2‖ := hcont_V.norm.measurable
  have hm_rb : Measurable fun x : ℝ × Space => ‖rb x.1 x.2‖ := hcont_rb.norm.measurable
  have hm_dV : Measurable (pwN1 V) := measurable_pwN1 V hcont_V.measurable hC2_V
  have hm_drb : Measurable (pwN1 rb) := measurable_pwN1 rb hcont_rb.measurable hC2_rb
  have hV22 := phaseLr_V22_bound hε hBv1 hV_pt hVsq_Y2
  have hsplit_U := conv_pointwise_split (P := P) hBv0 hρb0 hU_eq hC2_V hC2_rb hV_pt hrb_ae
  have hB1 := conv_T1_bound hCbv1 hBv hBv0 hC0 hCjet ha1 hρb0 hρb_le hk1 hdV_Y2
  have hB2 := conv_T2_bound hε hε1 hPpos hCbv1 hBv hBv0 hCdr ha1 hρ0 hρ1 hk2
    hm_V hm_drb hV22 hdrb_Y11
  have hB3 := conv_T3_bound hε hε1 hPpos hC0 hCdr ha1 hρ0 hρ1 hρb0 hρb_le hk3
    hm_rb hm_drb hrb_ae hrb_Y11 hdrb_pt hdrb_Y11
  set T1 : ℝ × Space → ℝ := fun x => (Bv + ρb) * pwN1 V x
  set T2 : ℝ × Space → ℝ := fun x => ‖V x.1 x.2‖ * pwN1 rb x
  set T3 : ℝ × Space → ℝ := fun x => pwN1 rb x * ‖rb x.1 x.2‖
  have hm_T1 : Measurable T1 := measurable_const.mul hm_dV
  have hm_T2 : Measurable T2 := hm_V.mul hm_drb
  have hm_T3 : Measurable T3 := hm_drb.mul hm_rb
  have hmink : phaseLr P 2 (fun x => (T1 x + T2 x) + T3 x) ≤
      (phaseLr P 2 T1 + phaseLr P 2 T2) + phaseLr P 2 T3 :=
    (phaseLr_add_le hPpos (by norm_num) (hm_T1.add hm_T2) hm_T3).trans
      (add_le_add (phaseLr_add_le hPpos (by norm_num) hm_T1 hm_T2) le_rfl)
  have hak0 : 0 ≤ a ^ k := pow_nonneg ha0 _
  have h1_0 : 0 ≤ (Cbv + C0) * Cjet * a ^ k :=
    mul_nonneg (mul_nonneg (add_nonneg hCbv0 hC0.le) hCjet) hak0
  have h2_0 : 0 ≤ Cbv * Cdr * a ^ k := mul_nonneg (mul_nonneg hCbv0 hCdr) hak0
  have h3_0 : 0 ≤ Cdr * C0 * a ^ k := mul_nonneg (mul_nonneg hCdr hC0.le) hak0
  calc ENNReal.ofReal ε * phaseLr P 2 (fun x => ‖fderiv ℝ (U x.1) x.2 (U x.1 x.2)‖)
      ≤ ENNReal.ofReal ε * phaseLr P 2 (fun x => (T1 x + T2 x) + T3 x) :=
        mul_le_mul_of_nonneg_left hsplit_U zero_le
    _ ≤ ENNReal.ofReal ε * ((phaseLr P 2 T1 + phaseLr P 2 T2) + phaseLr P 2 T3) :=
        mul_le_mul_of_nonneg_left hmink zero_le
    _ = (ENNReal.ofReal ε * phaseLr P 2 T1 + ENNReal.ofReal ε * phaseLr P 2 T2) +
          ENNReal.ofReal ε * phaseLr P 2 T3 := by rw [mul_add, mul_add]
    _ ≤ (ENNReal.ofReal ((Cbv + C0) * Cjet * a ^ k) + ENNReal.ofReal (Cbv * Cdr * a ^ k)) +
          ENNReal.ofReal (Cdr * C0 * a ^ k) :=
        add_le_add (add_le_add hB1 hB2) hB3
    _ = ENNReal.ofReal (((Cbv + C0) * Cjet + Cbv * Cdr + Cdr * C0) * a ^ k) := by
        rw [← ENNReal.ofReal_add h1_0 h2_0, ← ENNReal.ofReal_add (add_nonneg h1_0 h2_0) h3_0]
        congr 1
        ring

/-! ## 4. Main theorem `repPresGradY2` -/

/-- **Proved leaf `RepPresGradY2`** (`PartIII-b:C/rep/3/4/2`): the `Y_2` bound on the exact
background pressure gradient `∇p` along the concrete sequence (source lines 5245-5247, 2607-2612,
2641-2642). -/
theorem repPresGradY2 (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : RepPresGradY2 D := by
  obtain ⟨Cv0, kv, hVsup⟩ := vSupBound D hst
  obtain ⟨Csq0, ksq, hCsq0, hVsq⟩ := repVBg_vSq D hst
  obtain ⟨Cjet0, kjet, hVjet⟩ := repVJetY2 D hst
  obtain ⟨Cdr0, kdr, hDrb⟩ := hst.repairDeriv
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hρ1 := rhoRep_le_one_eventually D hst
  have hlim : Tendsto (retNu D.Pl D.σ₀) atTop (nhds 0) := retNu_tendsto D.σ₀ hst.omega_ne
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < dm ^ 3 / 12 :=
    hlim.eventually (gt_mem_nhds (by have := hst.dm_pos; positivity))
  have hAxiU := eventually_of_atBallLevels D hst
    (atBallLevels_axi (bgAxiLevels_of UnforcedLeray.Short.IIb.strongRegularity_proof))
  have hUL4 := eventually_of_atBallLevels D hst bgUL4_proved
  have hLer := eventually_of_atBallLevels D hst bgPresLeray_proved
  set Cv : ℝ := |Cv0| + 1
  set Csq : ℝ := Csq0 + 1
  set Cbv : ℝ := max Cv Csq
  set Cjet : ℝ := |Cjet0| + 1
  set Cdr : ℝ := |Cdr0| + 1
  set kbv : ℕ := max kv ksq
  set k : ℕ := max (max kbv D.K.k0 + kjet) (max (kbv + kdr) (kdr + D.K.k0))
  set C : ℝ := (Cbv + D.K.C0) * Cjet + Cbv * Cdr + Cdr * D.K.C0
  refine ⟨C, k, ?_⟩
  filter_upwards [hst.actual, hle1, hρ1, hsmall, hVsup, hVsq, hVjet, hDrb, hAxiU, hUL4, hLer] with
    n hact hle1_n hρ1_n hsmall_n hVsup_n hVsq_n hVjet_n hDrb_n hAxiU_n hUL4_n hLer_n
  set L := D.level n
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hν1 : L.ν ≤ 1 := hle1_n.1
  have hε1 : L.ε ≤ 1 := hle1_n.2
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  set a : ℝ := L.ν⁻¹
  have ha1 : 1 ≤ a := (one_le_inv₀ hν).2 hν1
  have hapos : 0 < a := zero_lt_one.trans_le ha1
  set P : ℝ := 2 * L.ε * cOf L.ν
  have hPpos : 0 < P := by positivity
  have hPeq : P = 2 * cOf L.ν / L.ε⁻¹ := by
    simp only [P]
    rw [div_inv_eq_mul]; ring
  have hC0 : 0 < D.K.C0 := hst.C0_pos
  have hρ0 : 0 ≤ rhoRep D.K L := rhoRep_nonneg D.K L
  -- Step 1: chart `L²(ringPhysμ)` norm of `|∇p|` equals `phaseLr P 2 (‖∇p‖)`
  have hpres_chart : eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖physGrad (L.pres τ) y‖) 2
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) = phaseLr P 2 (fun x => ‖physGrad (L.pres x.1) x.2‖) := by
    refine (phaseLr_two_eq_eLpNorm_ringRead hR hc hPeq (fun τ y => ‖physGrad (L.pres τ) y‖)
      (presGradCont_proved _ _ _ _ hact.profile).norm.measurable ?_ ?_).symm
    · intro τ y _hy
      obtain ⟨g, hg, hgy⟩ := azimuthRot_proved y
      have heq : physGrad (L.pres τ) (g y) = g (physGrad (L.pres τ) y) :=
        presGradEquivar_of physLapEquivar_proved _ _ _ _ hact.profile hAxiU_n g hg τ y
      have hgy' : g y = WithLp.toLp 2 ![ϱ y, 0, y 2] := hgy
      rw [← hgy', heq, LinearIsometryEquiv.norm_map]
    · intro τ y
      have hpt : L.pres (τ + P) = L.pres τ := funext fun z => hact.profile.periodicP τ z
      rw [hpt]
  -- Step 2: Leray projection slice bound `‖∇p‖_{Y_2} ≤ ‖U·∇U‖_{Y_2}`
  have hpres_le_U : phaseLr P 2 (fun x => ‖physGrad (L.pres x.1) x.2‖) ≤
      phaseLr P 2 (fun x => ‖fderiv ℝ (L.U x.1) x.2 (L.U x.1 x.2)‖) := by
    refine phaseLr_two_le_of_slice_l2 P (fun τ y => physGrad (L.pres τ) y)
      (fun τ y => fderiv ℝ (L.U τ) y (L.U τ y)) fun τ => ?_
    obtain ⟨Cu, hCu⟩ := hUL4_n
    have hWs : ContDiff ℝ 1 (L.U τ) := by
      have h1 := hact.profile.smoothU.comp
        (contDiff_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := Space) τ)
      exact h1.of_le (by simp)
    obtain ⟨hmem, -⟩ := prodL2OfL4_proved (L.U τ) Cu hWs (hCu τ).1 (hCu τ).2
    set F : Space → Space := fun y => fderiv ℝ (L.U τ) y (L.U τ y)
    have hLe := hLer_n τ hmem
    rw [eLpNorm_congr_ae hLe, ← Lp.enorm_def, enorm_neg, ← ofReal_norm]
    have htL : UnforcedLeray.toL2 F = hmem.toLp F := UnforcedLeray.toL2_of_memLp hmem
    calc ENNReal.ofReal ‖UnforcedLeray.toL2 F - UnforcedLeray.Leray.projection (UnforcedLeray.toL2 F)‖
        ≤ ENNReal.ofReal ‖UnforcedLeray.toL2 F‖ :=
          ENNReal.ofReal_le_ofReal (lerayComplNormLe_proved _)
      _ = eLpNorm F 2 volume := by
          rw [htL, Lp.norm_toLp, ENNReal.ofReal_toReal hmem.eLpNorm_lt_top.ne]
  -- Step 3: Continuity, off-axis `C²`, periodicity, and axisymmetry of `rb` and `V`
  obtain ⟨z, -, hVz, hrbz, -⟩ := hact.split.state
  have hrbf : ∀ τ, L.rb τ = ((L.params D.Pl).corr z) τ := fun τ => congrFun hrbz τ
  have hP1 : (L.params D.Pl).period ≤ 1 :=
    bgCorr_period_le_one hact.regime hsmall_n.le
  have hcont_rb : Continuous fun x : ℝ × Space => L.rb x.1 x.2 := by
    have e : (fun x : ℝ × Space => L.rb x.1 x.2) =
        fun x => (L.params D.Pl).corr z x.1 x.2 := funext fun x => by rw [hrbf x.1]
    rw [e]
    exact UnforcedLeray.Short.IIIa.corr_continuous _ hP1 z
  have hcont_U : Continuous fun x : ℝ × Space => L.U x.1 x.2 := hact.profile.smoothU.continuous
  have hV_sub : ∀ τ y, L.V τ y = L.U τ y - L.rb τ y := fun τ y => by
    simp [ReturnLevel.U]
  have hcont_V : Continuous fun x : ℝ × Space => L.V x.1 x.2 := by
    have e : (fun x : ℝ × Space => L.V x.1 x.2) =
        fun x => L.U x.1 x.2 - L.rb x.1 x.2 := funext fun x => hV_sub x.1 x.2
    rw [e]
    exact hcont_U.sub hcont_rb
  have hC2_rb : ∀ τ, ContDiffOn ℝ 2 (L.rb τ) axisᶜ := by
    intro τ
    rw [hrbf τ]
    refine bgCorr_contDiffOn_offAxis (V := L.V) (pres := L.pres) hst.planar.eigenpair
      hact.regime hν1 rfl z hVz ?_ τ
    have e : (fun t y => L.V t y + (L.params D.Pl).corr z t y) = L.U := by
      funext t y
      simp only [ReturnLevel.U, ← hrbf t]
    rw [e]
    exact hact.profile
  have hC2_V : ∀ τ, ContDiffOn ℝ 2 (L.V τ) axisᶜ := by
    intro τ
    have hU2 : ContDiff ℝ 2 (L.U τ) :=
      (hact.profile.smoothU.comp
        (contDiff_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := Space) τ)).of_le (by simp)
    have e : L.V τ = fun y => L.U τ y - L.rb τ y := funext fun y => hV_sub τ y
    rw [e]
    exact hU2.contDiffOn.sub (hC2_rb τ)
  have hper_rb : ∀ τ, L.rb (τ + P) = L.rb τ := by
    intro τ
    have hperiod : (L.params D.Pl).period = P := by
      rw [UnforcedLeray.Cons.C03.Concrete.Params.period_eq]
      exact hPeq.symm
    rw [hrbf, hrbf, ← hperiod]
    exact ((L.params D.Pl).corr_periodic z) τ
  have hper_V : ∀ τ, L.V (τ + P) = L.V τ := by
    intro τ
    funext y
    have hpU : L.U (τ + P) y = L.U τ y := hact.profile.periodicU τ y
    rw [hV_sub, hV_sub, hpU, congrFun (hper_rb τ) y]
  have hax_rb : ∀ τ, AxiNoSwirlPt (L.rb τ) := by
    intro τ
    have hcτ : Continuous (L.rb τ) :=
      hcont_rb.comp (continuous_const.prodMk continuous_id)
    refine axiNoSwirlPt_of_ae hcτ ?_
    rw [hrbf τ]
    exact (L.params D.Pl).corr_isAxisymmetricNoSwirl hP1 z τ
  have hax_V : ∀ τ, AxiNoSwirlPt (L.V τ) := by
    intro τ g hg x
    have haU : g (L.U τ (g.symm x)) = L.U τ x := hAxiU_n τ g hg x
    rw [hV_sub, hV_sub, map_sub, haU, hax_rb τ g hg x]
  -- Step 4: Bounds on `V`, `rb`, and chart-to-physical norms
  set Bv : ℝ := Cbv * a ^ kbv
  have hCbv1 : 1 ≤ Cbv := le_trans (by simp [Cv] : (1 : ℝ) ≤ Cv) (le_max_left _ _)
  have hV_pt : ∀ τ y, ‖L.V τ y‖ ≤ Bv := by
    intro τ y
    refine (hVsup_n τ y).trans ?_
    have h1 : Cv0 ≤ Cbv := (le_abs_self Cv0).trans
      ((by simp [Cv] : |Cv0| ≤ Cv).trans (le_max_left _ _))
    have h2 : a ^ kv ≤ a ^ kbv := pow_le_pow_right₀ ha1 (le_max_left _ _)
    exact mul_le_mul h1 h2 (by positivity) (zero_le_one.trans hCbv1)
  set ρb : ℝ := L.ρb D.Pl D.K
  have hρb_eq : ρb = D.K.C0 * a ^ D.K.k0 * rhoRep D.K L := by
    change UnforcedLeray.Short.IIb.rhoB (L.params D.Pl) D.K.m0 D.K.C0 D.K.k0 = _
    unfold UnforcedLeray.Short.IIb.rhoB rhoRep
    have hpow : (((L.params D.Pl).ν ^ D.K.k0)⁻¹ : ℝ) = a ^ D.K.k0 := by
      change (L.ν ^ D.K.k0)⁻¹ = a ^ D.K.k0
      rw [inv_pow]
    rw [hpow]
    change D.K.C0 * a ^ D.K.k0 * Real.exp (D.K.m0 / L.ν) * L.ε ^ (3 / 11 : ℝ) = _
    ring
  have hρb0 : 0 ≤ ρb := by rw [hρb_eq]; positivity
  have hρb_le : ρb ≤ D.K.C0 * a ^ D.K.k0 := by
    rw [hρb_eq]
    calc D.K.C0 * a ^ D.K.k0 * rhoRep D.K L
        ≤ D.K.C0 * a ^ D.K.k0 * 1 := mul_le_mul_of_nonneg_left hρ1_n (by positivity)
      _ = D.K.C0 * a ^ D.K.k0 := mul_one _
  have hrb_ae : ∀ τ : ℝ, ∀ᵐ y ∂(volume : Measure Space), ‖L.rb τ y‖ ≤ ρb := by
    intro τ
    have htop : eLpNormEssSup (L.rb τ) volume ≤ ENNReal.ofReal ρb := by
      rw [← eLpNorm_exponent_top]
      exact (le_add_of_nonneg_left zero_le).trans (hact.split.energy τ)
    filter_upwards [ae_le_eLpNormEssSup (f := L.rb τ) (μ := volume)] with y hy
    have hle := hy.trans htop
    rw [← ofReal_norm] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hρb0).1 hle
  have hrb_Y11 : phaseLr P (11 / 4) (fun x => ‖L.rb x.1 x.2‖) ≤ ENNReal.ofReal ρb := by
    refine phaseLr_le_of_slice (F := fun τ y => ‖L.rb τ y‖) hPpos (by norm_num)
      (ENNReal.ofReal ρb) fun τ => ?_
    change eLpNorm (fun y => ‖L.rb τ y‖) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
      ENNReal.ofReal ρb
    rw [eLpNorm_norm]
    exact (le_add_of_nonneg_right zero_le).trans (hact.split.energy τ)
  have hdr_le_Mdr : Cdr0 * a ^ kdr * rhoRep D.K L ≤ Cdr * a ^ kdr * rhoRep D.K L := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hρ0
    exact (le_abs_self Cdr0).trans (by simp [Cdr])
  have hdrb_pt : ∀ τ y, pwN1 L.rb (τ, y) ≤ Cdr * a ^ kdr * rhoRep D.K L := fun τ y =>
    (rby_norm_pw1_le L.rb (τ, y)).trans ((hDrb_n.1 τ y).trans hdr_le_Mdr)
  have hdrb_Y11 : phaseLr P (11 / 4) (pwN1 L.rb) ≤
      ENNReal.ofReal (Cdr * a ^ kdr * rhoRep D.K L) := by
    have h1 : phaseLr P (11 / 4) (pwN1 L.rb) ≤
        ENNReal.ofReal 1 * phaseLr P (11 / 4) (fun x => ‖fderiv ℝ (L.rb x.1) x.2‖) := by
      refine phaseLr_mono_smul (by norm_num) zero_le_one fun x => ?_
      have h0 : 0 ≤ pwN1 L.rb x := by unfold pwN1; exact norm_nonneg _
      rw [one_mul, abs_of_nonneg h0, abs_of_nonneg (norm_nonneg _)]
      exact rby_norm_pw1_le L.rb x
    rw [ENNReal.ofReal_one, one_mul] at h1
    exact h1.trans (hDrb_n.2.1.trans (ENNReal.ofReal_le_ofReal hdr_le_Mdr))
  have hm_V : Measurable fun x : ℝ × Space => ‖L.V x.1 x.2‖ := hcont_V.norm.measurable
  have hm_dV : Measurable (pwN1 L.V) := measurable_pwN1 L.V hcont_V.measurable hC2_V
  have hdV_Y2 : ENNReal.ofReal L.ε * phaseLr P 2 (pwN1 L.V) ≤
      ENNReal.ofReal (Cjet * a ^ kjet) := by
    have hdV_chart : phaseLr P 2 (pwN1 L.V) =
        eLpNorm (ringRead L.ε⁻¹ fun τ y => pwN1 L.V (τ, y)) 2 (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
      refine phaseLr_two_eq_eLpNorm_ringRead hR hc hPeq (fun τ y => pwN1 L.V (τ, y)) hm_dV ?_ ?_
      · intro τ y hy
        have hQ := LpChartForm.azimuth_not_mem_axis hy
        unfold pwN1
        rw [rby_pw1_eq L.V τ hy, rby_pw1_eq L.V τ hQ]
        exact (axiDens_azimuth (hax_V τ) y).2.1
      · intro τ y
        have heq : ∀ j, pw1 L.V j (τ + P, y) = pw1 L.V j (τ, y) := fun j => by
          unfold pw1
          simp only [hper_V τ]
        unfold pwN1
        simp only [heq]
    rw [hdV_chart]
    have hmono : eLpNorm (ringRead L.ε⁻¹ fun τ y => pwN1 L.V (τ, y)) 2
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
        eLpNorm (ringRead L.ε⁻¹ fun τ => vJetDens (L.V τ)) 2 (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
      refine eLpNorm_mono_enorm fun p => ?_
      have h0 : 0 ≤ pwN1 L.V (NearInst.chartTau L.ε⁻¹ p, NearInst.chartY L.ε⁻¹ p) := by
        unfold pwN1; exact norm_nonneg _
      have h1 : pwN1 L.V (NearInst.chartTau L.ε⁻¹ p, NearInst.chartY L.ε⁻¹ p) ≤
          vJetDens (L.V (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) :=
        (rby_norm_pw1_le L.V _).trans (norm_fderiv_le_vJetDens _ _)
      simp only [ringRead, Real.enorm_eq_ofReal h0, Real.enorm_eq_ofReal (h0.trans h1)]
      exact ENNReal.ofReal_le_ofReal h1
    refine (mul_le_mul_of_nonneg_left hmono zero_le).trans (hVjet_n.trans ?_)
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_abs_self Cjet0).trans (by simp [Cjet])
  have hVsq_Y2 : ENNReal.ofReal L.ε * phaseLr P 2 (fun x => ‖L.V x.1 x.2‖ ^ 2) ≤
      ENNReal.ofReal Bv := by
    have hVsq_chart : phaseLr P 2 (fun x => ‖L.V x.1 x.2‖ ^ 2) =
        eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖L.V τ y‖ ^ 2) 2 (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
      refine phaseLr_two_eq_eLpNorm_ringRead hR hc hPeq (fun τ y => ‖L.V τ y‖ ^ 2)
        (hm_V.pow_const 2) ?_ ?_
      · intro τ y _hy
        rw [(axiDens_azimuth (hax_V τ) y).1]
      · intro τ y
        rw [congrFun (hper_V τ) y]
    rw [hVsq_chart]
    refine hVsq_n.trans (ENNReal.ofReal_le_ofReal ?_)
    have hc1 : Csq0 ≤ Cbv := (by simp [Csq] : Csq0 ≤ Csq).trans (le_max_right _ _)
    have hk1 : a ^ ksq ≤ a ^ kbv := pow_le_pow_right₀ ha1 (le_max_right _ _)
    exact mul_le_mul hc1 hk1 (by positivity) (zero_le_one.trans hCbv1)
  rw [hpres_chart]
  refine (mul_le_mul_of_nonneg_left hpres_le_U zero_le).trans ?_
  exact conv_phaseLr_bound hε hε1 hPpos hCbv1 rfl hC0 (by positivity) (by positivity)
    ha1 hρ0 hρ1_n hρb0 hρb_le (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
    (fun _ _ => rfl) hcont_V hcont_rb hC2_V hC2_rb hV_pt hrb_ae hrb_Y11 hdrb_pt hdrb_Y11
    hdV_Y2 hVsq_Y2

end UnforcedLeray.Short.PartIIIb.Concrete.VBgSq

end
