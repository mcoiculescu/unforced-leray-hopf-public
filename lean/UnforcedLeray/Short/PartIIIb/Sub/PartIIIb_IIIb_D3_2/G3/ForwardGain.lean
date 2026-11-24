import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.DatumNorm
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.PhysFromMoving
import UnforcedLeray.Short.PartIIIa.T06_ScalingJa
import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual

/-!


Source: `the November 2 reference manuscript` (73 pp), lines 2836-2846
(`prop:short-full-clock`), 3020-3023 (`eq:short-causal-long-forward`), 3031-3035
(`eq:short-causal-scales`), and 4677-4679 (earlier-old part).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst

/-- Scaling bound `IIIa.ScalingBounds` assembled from its three proved parts. -/
private theorem scalingBounds_proved : IIIa.ScalingBounds :=
  IIIa.scalingBounds_of_parts IIIa.scalingJa IIIa.scalingJaInv IIIa.scalingJaInvDual

/-- On `0 < ν ≤ 1` and `0 ≤ s ≤ ν^{-3/2}`, `clockA ν s ≤ 2 * ν⁻¹`. -/
private theorem clockA_le_two_inv {ν s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hs : s ≤ ν ^ (-(3 / 2 : ℝ))) : IIIa.clockA ν s ≤ 2 * ν⁻¹ := by
  have h1 : ν ^ (-(3 / 2 : ℝ)) ≤ ν ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hν hν1 (by norm_num)
  have h2 : ν * s ≤ ν⁻¹ := by
    calc ν * s ≤ ν * ν ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left (hs.trans h1) hν.le
      _ = ν ^ (1 : ℝ) * ν ^ (-2 : ℝ) := by rw [Real.rpow_one]
      _ = ν ^ ((1 : ℝ) + (-2 : ℝ)) := (Real.rpow_add hν 1 (-2)).symm
      _ = ν⁻¹ := by
        rw [show (1 : ℝ) + (-2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h3 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  unfold IIIa.clockA
  linarith

/-- If `0 < ν`, `1 ≤ b`, `b * (Real.sqrt ν + ν) ≤ 1`, and `s ≤ ν^{-3/2}`, then
`b ≤ clockTheta ν s`. -/
private theorem le_clockTheta_of_le_uo {ν b s : ℝ} (hν : 0 < ν) (hb : 1 ≤ b)
    (hsmall : b * (Real.sqrt ν + ν) ≤ 1) (hs0 : 0 ≤ s) (hs : s ≤ ν ^ (-(3 / 2 : ℝ))) :
    b ≤ IIIa.clockTheta ν s := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have ha1 : 1 ≤ IIIa.clockA ν s := IIIa.one_le_clockA hν.le hs0
  have hapos : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos ha1
  have hνs : ν * s ≤ (Real.sqrt ν)⁻¹ := by
    have e1 : ν * ν ^ (-(3 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ := by
      have := Real.rpow_add hν (1 : ℝ) (-(3 / 2 : ℝ))
      rw [Real.rpow_one] at this
      rw [← this, Real.sqrt_eq_rpow, ← Real.rpow_neg hν.le]
      norm_num
    calc ν * s ≤ ν * ν ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hs hν.le
      _ = (Real.sqrt ν)⁻¹ := e1
  have hν2s : ν * (ν * s) ≤ Real.sqrt ν := by
    have hr : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
    calc ν * (ν * s) ≤ ν * (Real.sqrt ν)⁻¹ := mul_le_mul_of_nonneg_left hνs hν.le
      _ = Real.sqrt ν * Real.sqrt ν * (Real.sqrt ν)⁻¹ := by rw [Real.mul_self_sqrt hν.le]
      _ = Real.sqrt ν := by field_simp
  have hprod : b * (ν * IIIa.clockA ν s) ≤ 1 := by
    have h4 : ν * IIIa.clockA ν s ≤ Real.sqrt ν + ν := by
      unfold IIIa.clockA
      linarith
    calc b * (ν * IIIa.clockA ν s) ≤ b * (Real.sqrt ν + ν) :=
          mul_le_mul_of_nonneg_left h4 hb0.le
      _ ≤ 1 := hsmall
  have hpos : 0 < ν * IIIa.clockA ν s := mul_pos hν hapos
  unfold IIIa.clockTheta
  calc b = b * (ν * IIIa.clockA ν s) * (ν * IIIa.clockA ν s)⁻¹ := by
        rw [mul_inv_cancel_right₀ hpos.ne']
    _ ≤ 1 * (ν * IIIa.clockA ν s)⁻¹ :=
        mul_le_mul_of_nonneg_right hprod (inv_nonneg.2 hpos.le)
    _ = (ν * IIIa.clockA ν s)⁻¹ := one_mul _

/-- Identity `exp(γ(θ_t - θ_s)) = gainG γ ν s / gainG γ ν t` for `ν > 0` and `t, s ≥ 0`. -/
private theorem exp_clockTheta_sub_eq_gainG {γ ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.exp (γ * (IIIa.clockTheta ν t - IIIa.clockTheta ν s)) =
      IIIa.gainG γ ν s / IIIa.gainG γ ν t := by
  have hat : 0 < 1 + ν * t := by nlinarith
  have has : 0 < 1 + ν * s := by nlinarith
  have hνne : ν ≠ 0 := hν.ne'
  have hatne : 1 + ν * t ≠ 0 := hat.ne'
  have hasne : 1 + ν * s ≠ 0 := has.ne'
  unfold IIIa.gainG IIIa.clockTheta IIIa.clockA
  rw [← Real.exp_sub]
  congr 1
  field_simp
  ring

/-- Ratio bound `(θ_t / θ_s)^r ≤ 2^⌈|r|⌉₊ * (ν⁻¹)^⌈|r|⌉₊` for `0 < t ≤ s ≤ ν^{-3/2}` and `0 < ν ≤ 1`. -/
private theorem clockTheta_ratio_rpow_le {ν t s r : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ ν ^ (-(3 / 2 : ℝ))) :
    (IIIa.clockTheta ν t / IIIa.clockTheta ν s) ^ r ≤
      (2 : ℝ) ^ ⌈|r|⌉₊ * (ν⁻¹) ^ ⌈|r|⌉₊ := by
  have hat1 : 1 ≤ IIIa.clockA ν t := IIIa.one_le_clockA hν.le ht
  have has1 : 1 ≤ IIIa.clockA ν s := IIIa.one_le_clockA hν.le (ht.trans hts)
  have hat0 : 0 < IIIa.clockA ν t := lt_of_lt_of_le one_pos hat1
  have has0 : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos has1
  have htsA : IIIa.clockA ν t ≤ IIIa.clockA ν s := IIIa.clockA_mono hν.le hts
  have hrat_eq : IIIa.clockTheta ν t / IIIa.clockTheta ν s = IIIa.clockA ν s / IIIa.clockA ν t := by
    unfold IIIa.clockTheta
    have hνne : ν ≠ 0 := hν.ne'
    have hatne : IIIa.clockA ν t ≠ 0 := hat0.ne'
    have hasne : IIIa.clockA ν s ≠ 0 := has0.ne'
    field_simp
  have hrat1 : 1 ≤ IIIa.clockA ν s / IIIa.clockA ν t := (one_le_div hat0).2 htsA
  have hrat_le : IIIa.clockA ν s / IIIa.clockA ν t ≤ 2 * ν⁻¹ := by
    have hdiv : IIIa.clockA ν s / IIIa.clockA ν t ≤ IIIa.clockA ν s :=
      div_le_self has0.le hat1
    exact hdiv.trans (clockA_le_two_inv hν hν1 hs)
  have hceil : r ≤ (⌈|r|⌉₊ : ℝ) := (le_abs_self r).trans (Nat.le_ceil |r|)
  rw [hrat_eq]
  calc (IIIa.clockA ν s / IIIa.clockA ν t) ^ r
      ≤ (IIIa.clockA ν s / IIIa.clockA ν t) ^ (⌈|r|⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hrat1 hceil
    _ ≤ (2 * ν⁻¹) ^ (⌈|r|⌉₊ : ℝ) :=
        Real.rpow_le_rpow (by positivity) hrat_le (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ ⌈|r|⌉₊ * (ν⁻¹) ^ ⌈|r|⌉₊ := by
        rw [Real.rpow_natCast, mul_pow]

/-- **Full forward gain estimate on actual flat sequences** (source 2836-2846, 3020-3023,
3031-3035, 4677-4679). -/
theorem forwardGain_of (D : SeqData) (hL : UnforcedLeray.Short.IIIa.FullClockLongForward) :
    G3.ForwardGain D := by
  intro dm dp hst κ hκ m _ hm S hS
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨b₀, hb₀⟩ := hL D.Pl hst.planar m hm
  set b : ℝ := max b₀ 1 with hbdef
  have hb1 : 1 ≤ b := le_max_right _ _
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨C, ν₀, hν₀, hC⟩ := hb₀ b (le_max_left _ _)
  set ν₁ : ℝ := min (min ν₀ 1) ((2 * b)⁻¹ ^ 2) with hν₁def
  have hν₁pos : 0 < ν₁ := lt_min (lt_min hν₀ one_pos) (pow_pos (inv_pos.2 (by positivity)) 2)
  have hev : ∀ᶠ n : ℕ in atTop,
      (∃ FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n),
        S n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)) ∧
      nu D n < ν₁ :=
    hS.and ((retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₁pos))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set km : ℕ := ⌈(m - 3) / 2⌉₊ with hkm
  set kκ : ℕ := ⌈|D.Pl.kappa.re|⌉₊ with hkκ
  set C' : ℝ := (2 : ℝ) ^ km * max C 0 * (2 : ℝ) ^ kκ * (2.1 : ℝ) ^ ((3 : ℝ) / 2) with hC'
  refine ⟨C', km + kκ, N, fun n hn t s ht htT hs1 hs2 => ?_⟩
  obtain ⟨⟨FI, hFI⟩, hνlt⟩ := hN n hn
  set ν := nu D n with hνdef
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hνa : ν ≤ ν₀ := hνlt.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hνlt.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνb_sq : ν ≤ (2 * b)⁻¹ ^ 2 := hνlt.le.trans (min_le_right _ _)
  have hsmall : b * (Real.sqrt ν + ν) ≤ 1 := by
    have hsq1 : Real.sqrt ν ≤ (2 * b)⁻¹ := by
      calc Real.sqrt ν ≤ Real.sqrt ((2 * b)⁻¹ ^ 2) := Real.sqrt_le_sqrt hνb_sq
        _ = (2 * b)⁻¹ := Real.sqrt_sq (by positivity)
    have hsq2 : ν ≤ Real.sqrt ν := by
      have hr1 : Real.sqrt ν ≤ 1 := by
        simpa using Real.sqrt_le_sqrt hν1
      calc ν = Real.sqrt ν * Real.sqrt ν := (Real.mul_self_sqrt hν.le).symm
        _ ≤ 1 * Real.sqrt ν := mul_le_mul_of_nonneg_right hr1 (Real.sqrt_nonneg ν)
        _ = Real.sqrt ν := one_mul _
    have hsum : Real.sqrt ν + ν ≤ 2 * (2 * b)⁻¹ := by linarith
    calc b * (Real.sqrt ν + ν) ≤ b * (2 * (2 * b)⁻¹) := mul_le_mul_of_nonneg_left hsum hbpos.le
      _ = 1 := by field_simp
  have hts : t ≤ s := by
    have : 1.1 / ν ≤ 1.2 / ν := div_le_div_of_nonneg_right (by norm_num) hν.le
    linarith
  have hs0 : 0 ≤ s := le_trans ht.le hts
  have hθb : b ≤ IIIa.clockTheta ν s := le_clockTheta_of_le_uo hν hb1 hsmall hs0 hs2
  have hcOf : cOf ν = ν ^ (-2 : ℝ) := by
    rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI : FlatInstData κ ν c m tr) (x : Xmc c m),
      ‖FI.ev.U s t x‖ ≤ C' * ν⁻¹ ^ (km + kκ) *
        (IIIa.gainG D.Pl.eigenvalue.re ν s / IIIa.gainG D.Pl.eigenvalue.re ν t) * ‖x‖ := by
    intro c hc hfact tr hbuc FI' x
    subst hc
    obtain ⟨-, hLong⟩ := hC ν ⟨hν, hνa⟩ tr hbuc
    obtain ⟨u', hu'⟩ := FI'.ev.flow t ht.le x
    have hLF1 := hLong t s ht.le hts hθb (xFn x) (xFn_memLp x) (xFn_zeroCirc x) _ _ hu'
    have hat1 : 1 ≤ IIIa.clockA ν t := IIIa.one_le_clockA hν.le ht.le
    have has1 : 1 ≤ IIIa.clockA ν s := IIIa.one_le_clockA hν.le hs0
    have hat0 : 0 < IIIa.clockA ν t := lt_of_lt_of_le one_pos hat1
    have has0 : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos has1
    have hcpos : (0 : ℝ) < ν ^ (-2 : ℝ) := Fact.out
    have hdS : 0 < IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s) :=
      div_pos hcpos (Real.sqrt_pos.2 has0)
    have hdcS : IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s) * Real.sqrt (IIIa.clockA ν s) =
        ν ^ (-2 : ℝ) := by
      unfold IIIa.cellLen
      field_simp [(Real.sqrt_pos.2 has0).ne']
    have hs1_scale := IIIa.xNorm_scale_le scalingBounds_proved hm0 has1 hdS hdcS
      (xFn_memLp (FI'.ev.U s t x))
    have hs2_scale := IIIa.xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (IIIa.clockA ν t) hm0 hat1
      (xFn x) (xFn_memLp x)
    rw [xNorm_xFn_eq] at hs1_scale hs2_scale
    set A : ℝ := IIIa.clockA ν s ^ ((m - 3) / 2)
    set B : ℝ := max C 0 *
      Real.exp (D.Pl.eigenvalue.re * (IIIa.clockTheta ν t - IIIa.clockTheta ν s)) *
      (IIIa.clockTheta ν t / IIIa.clockTheta ν s) ^ D.Pl.kappa.re
    set D0 : ℝ := IIIa.clockA ν t ^ ((3 : ℝ) / 2)
    have hA0 : 0 ≤ A := Real.rpow_nonneg has0.le _
    have hθdiv0 : 0 ≤ (IIIa.clockTheta ν t / IIIa.clockTheta ν s) ^ D.Pl.kappa.re :=
      Real.rpow_nonneg (div_nonneg (IIIa.theta_pos hν ht.le).le (IIIa.theta_pos hν hs0).le) _
    have hB0 : 0 ≤ B :=
      mul_nonneg (mul_nonneg (le_max_right C 0) (Real.exp_pos _).le) hθdiv0
    have hD0 : 0 ≤ D0 := Real.rpow_nonneg hat0.le _
    have hBle : C * Real.exp (D.Pl.eigenvalue.re * (IIIa.clockTheta ν t - IIIa.clockTheta ν s)) *
        (IIIa.clockTheta ν t / IIIa.clockTheta ν s) ^ D.Pl.kappa.re ≤ B := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
        (Real.exp_pos _).le) hθdiv0
    have hcalc : ENNReal.ofReal ‖FI'.ev.U s t x‖ ≤ ENNReal.ofReal (A * B * D0 * ‖x‖) := by
      calc ENNReal.ofReal ‖FI'.ev.U s t x‖
          ≤ ENNReal.ofReal A * IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
              (IIIa.JscaleInv (IIIa.clockA ν s) (xFn (FI'.ev.U s t x))) := hs1_scale
        _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B *
              (ENNReal.ofReal D0 * ENNReal.ofReal ‖x‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ bot_le
            refine (hLF1.trans (mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal hBle) bot_le)).trans ?_
            exact mul_le_mul_of_nonneg_left hs2_scale bot_le
        _ = ENNReal.ofReal (A * B * D0 * ‖x‖) := by
            rw [← ENNReal.ofReal_mul hD0, ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hA0]
            congr 1
            ring
    have hreal : ‖FI'.ev.U s t x‖ ≤ A * B * D0 * ‖x‖ :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc
    have hA_le : A ≤ (2 : ℝ) ^ km * (ν⁻¹) ^ km := by
      have hm_le : (m - 3) / 2 ≤ (km : ℝ) := Nat.le_ceil _
      calc IIIa.clockA ν s ^ ((m - 3) / 2)
          ≤ IIIa.clockA ν s ^ (km : ℝ) := Real.rpow_le_rpow_of_exponent_le has1 hm_le
        _ ≤ (2 * ν⁻¹) ^ (km : ℝ) :=
            Real.rpow_le_rpow has0.le (clockA_le_two_inv hν hν1 hs2) (Nat.cast_nonneg _)
        _ = (2 : ℝ) ^ km * (ν⁻¹) ^ km := by rw [Real.rpow_natCast, mul_pow]
    have hB_le : B ≤ max C 0 * (IIIa.gainG D.Pl.eigenvalue.re ν s /
        IIIa.gainG D.Pl.eigenvalue.re ν t) * ((2 : ℝ) ^ kκ * (ν⁻¹) ^ kκ) := by
      dsimp [B]
      rw [exp_clockTheta_sub_eq_gainG hν ht.le hs0]
      refine mul_le_mul_of_nonneg_left (clockTheta_ratio_rpow_le hν hν1 ht.le hts hs2) ?_
      exact mul_nonneg (le_max_right C 0) (div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    have hD0_le : D0 ≤ (2.1 : ℝ) ^ ((3 : ℝ) / 2) := by
      have hat21 : IIIa.clockA ν t ≤ 2.1 := by
        unfold IIIa.clockA
        have : ν * t ≤ 1.1 := by
          calc ν * t ≤ ν * (1.1 / ν) := mul_le_mul_of_nonneg_left htT hν.le
            _ = 1.1 := by field_simp
        linarith
      exact Real.rpow_le_rpow hat0.le hat21 (by norm_num)
    have hgp : 0 ≤ IIIa.gainG D.Pl.eigenvalue.re ν s / IIIa.gainG D.Pl.eigenvalue.re ν t :=
      div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hABD : A * B * D0 ≤ C' * ν⁻¹ ^ (km + kκ) *
        (IIIa.gainG D.Pl.eigenvalue.re ν s / IIIa.gainG D.Pl.eigenvalue.re ν t) := by
      calc A * B * D0
          ≤ ((2 : ℝ) ^ km * (ν⁻¹) ^ km) *
              (max C 0 * (IIIa.gainG D.Pl.eigenvalue.re ν s /
                IIIa.gainG D.Pl.eigenvalue.re ν t) * ((2 : ℝ) ^ kκ * (ν⁻¹) ^ kκ)) *
              (2.1 : ℝ) ^ ((3 : ℝ) / 2) := by
            refine mul_le_mul (mul_le_mul hA_le hB_le hB0 (by positivity)) hD0_le hD0 (by positivity)
        _ = C' * ν⁻¹ ^ (km + kκ) *
              (IIIa.gainG D.Pl.eigenvalue.re ν s / IIIa.gainG D.Pl.eigenvalue.re ν t) := by
            rw [hC', pow_add]
            ring
    exact hreal.trans (mul_le_mul_of_nonneg_right hABD (norm_nonneg x))
  rw [hFI]
  intro x
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  exact key (cOf ν) hcOf (D.train n) (D.train_buc n) FI x

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
