import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBareOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.ForwardGain

/-!


Source: `the November 2 reference manuscript` (73 pp), lines 2836-2846
(`prop:short-full-clock`) and 4421-4426.
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

/-- **Forward operator bound at `H = 2/ν`** (source 2836-2846, 4421-4426). -/
theorem bandForwardAtH_of (D : SeqData) (hL : UnforcedLeray.Short.IIIa.FullClockLongForward) :
    G3.BandForwardAtH D := by
  intro dm dp hst κ _hκ m _ hm
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨b₀, hb₀⟩ := hL D.Pl hst.planar m hm
  set b : ℝ := max b₀ 1 with hbdef
  have hb1 : 1 ≤ b := le_max_right _ _
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨C, ν₀, hν₀, hC⟩ := hb₀ b (le_max_left _ _)
  set ν₁ : ℝ := min ν₀ ((3 * b)⁻¹) with hν₁def
  have hν₁pos : 0 < ν₁ := lt_min hν₀ (inv_pos.2 (by positivity))
  set C' : ℝ := (3 : ℝ) ^ ((m - 3) / 2) * max C 0 with hC'
  refine ⟨C', ν₁, by positivity, hν₁pos, fun ν hν hνle => ?_⟩
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  have hνa : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  have hνb : ν ≤ (3 * b)⁻¹ := hνle.trans (min_le_right _ _)
  set s : ℝ := 2 / ν with hsdef
  have hs0 : 0 ≤ s := div_nonneg zero_le_two hν.le
  have ha0 : IIIa.clockA ν 0 = 1 := by
    unfold IIIa.clockA
    ring
  have has : IIIa.clockA ν s = 3 := by
    unfold IIIa.clockA
    dsimp [s]
    have hνne : ν ≠ 0 := hν.ne'
    field_simp
    ring
  have hθb : b ≤ IIIa.clockTheta ν s := by
    have hprod : b * (ν * 3) ≤ 1 := by
      calc b * (ν * 3) = (3 * b) * ν := by ring
        _ ≤ (3 * b) * (3 * b)⁻¹ := mul_le_mul_of_nonneg_left hνb (by positivity)
        _ = 1 := mul_inv_cancel₀ (by positivity)
    have hpos : 0 < ν * 3 := by positivity
    unfold IIIa.clockTheta
    rw [has]
    calc b = b * (ν * 3) * (ν * 3)⁻¹ := by rw [mul_inv_cancel_right₀ hpos.ne']
      _ ≤ 1 * (ν * 3)⁻¹ := mul_le_mul_of_nonneg_right hprod (inv_nonneg.2 hpos.le)
      _ = (ν * 3)⁻¹ := one_mul _
  have hFpm : Real.exp (D.Pl.eigenvalue.re * (IIIa.clockTheta ν 0 - IIIa.clockTheta ν s)) *
      (IIIa.clockTheta ν 0 / IIIa.clockTheta ν s) ^ D.Pl.kappa.re =
      ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s 0‖ := by
    rw [fpm_true_eq]
    have has' : 0 < aOf ν s := aOf_pos_of_nonneg ν s hν hs0
    have hat' : 0 < aOf ν 0 := aOf_pos_of_nonneg ν 0 hν le_rfl
    rw [fpm_norm_formula D.Pl.eigenvalue D.Pl.kappa ν s 0 (div_pos has' hat')]
    unfold IIIa.clockTheta zOf aOf IIIa.clockA
    have hνne : ν ≠ 0 := hν.ne'
    have hasne : 1 + ν * s ≠ 0 := has'.ne'
    have hatne : 1 + ν * 0 ≠ 0 := hat'.ne'
    have hdiff : (ν * (1 + ν * 0))⁻¹ - (ν * (1 + ν * s))⁻¹ =
        s / (1 + ν * s) - 0 / (1 + ν * 0) := by
      field_simp
      ring
    have hrat : (ν * (1 + ν * 0))⁻¹ / (ν * (1 + ν * s))⁻¹ = (1 + ν * s) / (1 + ν * 0) := by
      field_simp
    rw [hdiff, hrat]
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI : FlatInstData κ ν c m tr) (x : Xmc c m),
      ‖FI.ev.U s 0 x‖ ≤ C' * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s 0‖ * ‖x‖ := by
    intro c hc hfact tr hbuc FI x
    subst hc
    obtain ⟨-, hLong⟩ := hC ν ⟨hν, hνa⟩ tr hbuc
    obtain ⟨u', hu'⟩ := FI.ev.flow 0 le_rfl x
    have hLF1 := hLong 0 s le_rfl hs0 hθb (xFn x) (xFn_memLp x) (xFn_zeroCirc x) _ _ hu'
    have hat1 : 1 ≤ IIIa.clockA ν 0 := IIIa.one_le_clockA hν.le le_rfl
    have has1 : 1 ≤ IIIa.clockA ν s := IIIa.one_le_clockA hν.le hs0
    have hat0 : 0 < IIIa.clockA ν 0 := lt_of_lt_of_le one_pos hat1
    have has0 : 0 < IIIa.clockA ν s := lt_of_lt_of_le one_pos has1
    have hcpos : (0 : ℝ) < ν ^ (-2 : ℝ) := Fact.out
    have hdS : 0 < IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s) :=
      div_pos hcpos (Real.sqrt_pos.2 has0)
    have hdcS : IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s) * Real.sqrt (IIIa.clockA ν s) =
        ν ^ (-2 : ℝ) := by
      unfold IIIa.cellLen
      field_simp [(Real.sqrt_pos.2 has0).ne']
    have hs1_scale := IIIa.xNorm_scale_le scalingBounds_proved hm0 has1 hdS hdcS
      (xFn_memLp (FI.ev.U s 0 x))
    have hs2_scale := IIIa.xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (IIIa.clockA ν 0) hm0 hat1
      (xFn x) (xFn_memLp x)
    rw [xNorm_xFn_eq] at hs1_scale hs2_scale
    set A : ℝ := IIIa.clockA ν s ^ ((m - 3) / 2)
    set B : ℝ := max C 0 *
      Real.exp (D.Pl.eigenvalue.re * (IIIa.clockTheta ν 0 - IIIa.clockTheta ν s)) *
      (IIIa.clockTheta ν 0 / IIIa.clockTheta ν s) ^ D.Pl.kappa.re
    set D0 : ℝ := IIIa.clockA ν 0 ^ ((3 : ℝ) / 2)
    have hA0 : 0 ≤ A := Real.rpow_nonneg has0.le _
    have hθdiv0 : 0 ≤ (IIIa.clockTheta ν 0 / IIIa.clockTheta ν s) ^ D.Pl.kappa.re :=
      Real.rpow_nonneg (div_nonneg (IIIa.theta_pos hν le_rfl).le (IIIa.theta_pos hν hs0).le) _
    have hB0 : 0 ≤ B :=
      mul_nonneg (mul_nonneg (le_max_right C 0) (Real.exp_pos _).le) hθdiv0
    have hD0 : 0 ≤ D0 := Real.rpow_nonneg hat0.le _
    have hBle : C * Real.exp (D.Pl.eigenvalue.re * (IIIa.clockTheta ν 0 - IIIa.clockTheta ν s)) *
        (IIIa.clockTheta ν 0 / IIIa.clockTheta ν s) ^ D.Pl.kappa.re ≤ B := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
        (Real.exp_pos _).le) hθdiv0
    have hcalc : ENNReal.ofReal ‖FI.ev.U s 0 x‖ ≤ ENNReal.ofReal (A * B * D0 * ‖x‖) := by
      calc ENNReal.ofReal ‖FI.ev.U s 0 x‖
          ≤ ENNReal.ofReal A * IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
              (IIIa.JscaleInv (IIIa.clockA ν s) (xFn (FI.ev.U s 0 x))) := hs1_scale
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
    have hreal : ‖FI.ev.U s 0 x‖ ≤ A * B * D0 * ‖x‖ :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc
    have hA_eq : A = (3 : ℝ) ^ ((m - 3) / 2) := by
      dsimp [A]
      rw [has]
    have hB_eq : B = max C 0 * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s 0‖ := by
      dsimp [B]
      rw [mul_assoc, hFpm]
    have hD0_eq : D0 = 1 := by
      dsimp [D0]
      rw [ha0, Real.one_rpow]
    calc ‖FI.ev.U s 0 x‖ ≤ A * B * D0 * ‖x‖ := hreal
      _ = C' * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν s 0‖ * ‖x‖ := by
        rw [hA_eq, hB_eq, hD0_eq, hC']
        ring
  intro tr hbuc FI x
  exact key (cOf ν) (cOf_eq_rpow hν) tr hbuc FI x

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
