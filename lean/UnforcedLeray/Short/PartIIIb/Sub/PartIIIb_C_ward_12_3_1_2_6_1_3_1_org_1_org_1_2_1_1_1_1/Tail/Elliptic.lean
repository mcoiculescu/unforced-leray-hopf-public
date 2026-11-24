import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceEnergyIdentity
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceWirtinger
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.HalfLineMaxPrinciple
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.GoodSliceSup

/-!
# Quantitative transverse tail of a zero-mean solution of `Δw = f + h(η)` on the cylinder

Helper of `Tail.lean` (task `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/2/1/1/1/1`).
Source `the November 2 reference manuscript`
496-502: the nonzero `q`-modes of the stream are obtained from the vorticity by the inverse of
`∂_η² - k²`, `|k| ≥ 2π/c`, and inherit the transverse tail of the source ("splitting the
convolution at distance `l/2`").  Here the same statement is proved for all nonzero modes at once,
in `L²` on the slices `η = const` (no Fourier inversion):

* `m(η) = ∫_{-c/2}^{c/2} w(q,η)² dq` satisfies `m'' = 2∫ w_η² + 2∫ w_q² + 2∫ w Δw`
  (`PartI.sliceEnergyIdentity`); Wirtinger on zero-mean slices (`PartI.sliceWirtinger`,
  `λ = 2π/c`) and `∫ w h(η) dq = 0` give `m'' ≥ λ² m - c ε²/λ²` where `|f| ≤ ε`;
* the half-line maximum principle (`PartI.LerayPressureGauge.halfLine_nonpos`) against the
  barrier `B e^{-λ(η-η₁)} + K/λ²` gives `m(η) ≤ c M² e^{-λ(|η|-η₁)} + c ε²/λ⁴` for `|η| ≥ η₁`
  (`slice_energy_tail`);
* the one-dimensional Sobolev bound `w² ≤ 2c⁻¹ m + c ∫ (∂_q w)²` (`PartI.goodSlice_sup_sq_le`),
  applied with the same estimate for `w₁ = ∂_q w`, gives the pointwise tail
  (`zeroMean_sq_tail`).

The term `h(η)` is any function of `η` alone: it is the contribution of the mean stream, which
is orthogonal to the zero-mean slices.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FluctTail

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **One-dimensional comparison on `[η₁, ∞)`**: if `m'' ≥ λ² m - K` and `m ≤ B` there, then
`m(η) ≤ B e^{-λ(η-η₁)} + K/λ²`. -/
theorem ode_upper {lam B K η₁ : ℝ} (hlam : 0 < lam) (hB0 : 0 ≤ B) (hK : 0 ≤ K)
    {m m1 m2 : ℝ → ℝ}
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hineq : ∀ η, η₁ ≤ η → lam ^ 2 * m η - K ≤ m2 η)
    (hB : ∀ η, η₁ ≤ η → m η ≤ B) :
    ∀ η, η₁ ≤ η → m η ≤ B * Real.exp (-(lam * (η - η₁))) + K / lam ^ 2 := by
  have hEd : ∀ η, HasDerivAt (fun x => Real.exp (-(lam * (x - η₁))))
      (-lam * Real.exp (-(lam * (η - η₁)))) η := by
    intro η
    have h1 : HasDerivAt (fun x : ℝ => -(lam * (x - η₁))) (-(lam * 1)) η :=
      (((hasDerivAt_id' η).sub_const η₁).const_mul lam).neg
    exact h1.exp.congr_deriv (by ring)
  have hEd1 : ∀ η, HasDerivAt (fun x => B * (-lam * Real.exp (-(lam * (x - η₁)))))
      (B * (lam ^ 2 * Real.exp (-(lam * (η - η₁))))) η := by
    intro η
    exact (((hEd η).const_mul (-lam)).const_mul B).congr_deriv (by ring)
  have hK2 : 0 ≤ K / lam ^ 2 := div_nonneg hK (by positivity)
  have hlam2 : lam ^ 2 * (K / lam ^ 2) = K := by field_simp
  have key := UnforcedLeray.Short.PartI.LerayPressureGauge.halfLine_nonpos hlam
    (R := η₁) (M := B)
    (D := fun η => m η - (B * Real.exp (-(lam * (η - η₁))) + K / lam ^ 2))
    (D1 := fun η => m1 η - B * (-lam * Real.exp (-(lam * (η - η₁)))))
    (D2 := fun η => m2 η - B * (lam ^ 2 * Real.exp (-(lam * (η - η₁)))))
    (fun η => (hm η).sub (((hEd η).const_mul B).add_const (K / lam ^ 2)))
    (fun η => (hm1 η).sub (hEd1 η))
    (fun η hη => by
      have h1 := hineq η hη
      have h2 : lam ^ 2 * (m η - (B * Real.exp (-(lam * (η - η₁))) + K / lam ^ 2)) =
          lam ^ 2 * m η - B * (lam ^ 2 * Real.exp (-(lam * (η - η₁)))) -
            lam ^ 2 * (K / lam ^ 2) := by ring
      show lam ^ 2 * (m η - (B * Real.exp (-(lam * (η - η₁))) + K / lam ^ 2)) ≤
        m2 η - B * (lam ^ 2 * Real.exp (-(lam * (η - η₁))))
      rw [h2, hlam2]
      linarith)
    (fun η hη => by
      have h1 := hB η hη
      have h2 : 0 ≤ B * Real.exp (-(lam * (η - η₁))) := mul_nonneg hB0 (Real.exp_pos _).le
      show m η - (B * Real.exp (-(lam * (η - η₁))) + K / lam ^ 2) ≤ B
      linarith)
    (by
      have h1 := hB η₁ le_rfl
      show m η₁ - (B * Real.exp (-(lam * (η₁ - η₁))) + K / lam ^ 2) ≤ 0
      rw [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      linarith)
  intro η hη
  have h := key η hη
  have h' : m η - (B * Real.exp (-(lam * (η - η₁))) + K / lam ^ 2) ≤ 0 := h
  linarith

/-- **One-dimensional comparison on `(-∞, -η₁]`** (reflection of `ode_upper`). -/
theorem ode_lower {lam B K η₁ : ℝ} (hlam : 0 < lam) (hB0 : 0 ≤ B) (hK : 0 ≤ K)
    {m m1 m2 : ℝ → ℝ}
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hineq : ∀ η, η ≤ -η₁ → lam ^ 2 * m η - K ≤ m2 η)
    (hB : ∀ η, η ≤ -η₁ → m η ≤ B) :
    ∀ η, η ≤ -η₁ → m η ≤ B * Real.exp (-(lam * (-η - η₁))) + K / lam ^ 2 := by
  have hm' : ∀ η, HasDerivAt (fun x => m (-x)) (-m1 (-η)) η := by
    intro η
    have h := (hm (-η)).comp η (hasDerivAt_neg η)
    have h' : HasDerivAt (fun x => m (-x)) (m1 (-η) * -1) η := h
    exact h'.congr_deriv (by ring)
  have hm1' : ∀ η, HasDerivAt (fun x => -m1 (-x)) (m2 (-η)) η := by
    intro η
    have h := ((hm1 (-η)).comp η (hasDerivAt_neg η)).neg
    have h' : HasDerivAt (fun x => -m1 (-x)) (-(m2 (-η) * -1)) η := h
    exact h'.congr_deriv (by ring)
  have key := ode_upper (η₁ := η₁) (m := fun x => m (-x)) (m1 := fun x => -m1 (-x))
    (m2 := fun x => m2 (-x)) hlam hB0 hK hm' hm1'
    (fun η hη => by
      have h := hineq (-η) (by linarith)
      exact h)
    (fun η hη => hB (-η) (by linarith))
  intro η hη
  have h := key (-η) (by linarith)
  simp only [neg_neg] at h
  exact h

/-- **Two-sided comparison**: `m(η) ≤ B e^{-λ(|η|-η₁)} + K/λ²` for `|η| ≥ η₁`. -/
theorem ode_abs {lam B K η₁ : ℝ} (hlam : 0 < lam) (hB0 : 0 ≤ B) (hK : 0 ≤ K)
    {m m1 m2 : ℝ → ℝ}
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hineq : ∀ η, η₁ ≤ |η| → lam ^ 2 * m η - K ≤ m2 η)
    (hB : ∀ η, η₁ ≤ |η| → m η ≤ B) :
    ∀ η, η₁ ≤ |η| → m η ≤ B * Real.exp (-(lam * (|η| - η₁))) + K / lam ^ 2 := by
  intro η hη
  rcases le_or_gt 0 η with h0 | h0
  · have hu := ode_upper (η₁ := η₁) hlam hB0 hK hm hm1
      (fun x hx => hineq x (hx.trans (le_abs_self x)))
      (fun x hx => hB x (hx.trans (le_abs_self x)))
    rw [abs_of_nonneg h0] at hη ⊢
    exact hu η hη
  · have hl := ode_lower (η₁ := η₁) hlam hB0 hK hm hm1
      (fun x hx => hineq x (by have := neg_le_abs x; linarith))
      (fun x hx => hB x (by have := neg_le_abs x; linarith))
    rw [abs_of_neg h0] at hη ⊢
    exact hl η (by linarith)

/-- The `q`-slices of a continuous function are continuous. -/
theorem slice_cont {f : Plane → ℝ} (hf : Continuous f) (η : ℝ) :
    Continuous (fun q : ℝ => f (q, η)) :=
  hf.comp (continuous_id.prodMk continuous_const)

/-- **Slice-energy tail.** For `w` of class `C²`, `c`-periodic, with zero `q`-mean on every slice,
`Δw = f + h(η)`, `|w| ≤ M` and `|f| ≤ ε` on `|η| ≥ η₁`: the slice energy satisfies
`∫ w(q,η)² dq ≤ c M² e^{-λ(|η|-η₁)} + c ε²/λ⁴` for `|η| ≥ η₁`, `λ = 2π/c`. -/
theorem slice_energy_tail {c M ε η₁ : ℝ} (hc : 0 < c) {w f : Plane → ℝ} {h : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hper : Cyl.IsPeriodic c w)
    (hmean : ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), w (q, η) = 0)
    (hlap : ∀ z : Plane, Train.lapS w z = f z + h z.2)
    (hM : ∀ z : Plane, η₁ ≤ |z.2| → |w z| ≤ M)
    (hf : ∀ z : Plane, η₁ ≤ |z.2| → |f z| ≤ ε) :
    ∀ η : ℝ, η₁ ≤ |η| → ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2 ≤
      c * M ^ 2 * Real.exp (-((2 * π / c) * (|η| - η₁))) + c * ε ^ 2 / (2 * π / c) ^ 4 := by
  set lam : ℝ := 2 * π / c with hlam_def
  have hlam : 0 < lam := by positivity
  obtain ⟨m1, m2, hm, hm1, hid⟩ := UnforcedLeray.Short.PartI.sliceEnergyIdentity c w hc hw hper
  have hwc : Continuous w := hw.continuous
  have hlc : Continuous (Train.lapS w) := UnforcedLeray.Short.PartI.osc_lapS_continuous hw
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  set m : ℝ → ℝ := fun η => ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2 with hm_def
  -- the bound `m ≤ c M²`
  have hmb : ∀ η, η₁ ≤ |η| → m η ≤ c * M ^ 2 := by
    intro η hη
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => w (q, η) ^ 2) (C := M ^ 2) (by simp) (fun q _ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM (q, η) hη) 2)
    rw [hvol, Real.norm_eq_abs] at hb
    have : m η ≤ M ^ 2 * c := (le_abs_self _).trans hb
    linarith
  -- the energy inequality `m'' ≥ λ² m - c ε²/λ²`
  have hineq : ∀ η, η₁ ≤ |η| → lam ^ 2 * m η - c * ε ^ 2 / lam ^ 2 ≤ m2 η := by
    intro η hη
    have hQ : 0 ≤ ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta w (q, η) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc (fun q _ => sq_nonneg _)
    have hP : lam ^ 2 * m η ≤ ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2 := by
      have hW := UnforcedLeray.Short.PartI.sliceWirtinger c w hc (hw.of_le (by norm_num)) hper
        hmean η
      have e : lam ^ 2 * (c / (2 * π)) ^ 2 = 1 := by rw [hlam_def]; field_simp
      calc lam ^ 2 * m η ≤ lam ^ 2 * ((c / (2 * π)) ^ 2 *
            ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2) :=
            mul_le_mul_of_nonneg_left hW (sq_nonneg _)
        _ = _ := by rw [← mul_assoc, e, one_mul]
    -- pointwise: `0 ≤ 2 w Δw + λ² w² + ε²/λ² - 2 h(η) w`
    have hpt : ∀ q : ℝ, 0 ≤ 2 * (w (q, η) * Train.lapS w (q, η)) + lam ^ 2 * w (q, η) ^ 2 +
        ε ^ 2 / lam ^ 2 - 2 * h η * w (q, η) := by
      intro q
      have hfq := hf (q, η) hη
      have hl := hlap (q, η)
      simp only at hl
      rw [hl]
      have hsq : 0 ≤ (lam * |w (q, η)| - ε / lam) ^ 2 := sq_nonneg _
      have hexp : (lam * |w (q, η)| - ε / lam) ^ 2 =
          lam ^ 2 * w (q, η) ^ 2 - 2 * |w (q, η)| * ε + ε ^ 2 / lam ^ 2 := by
        have hl0 : lam ≠ 0 := hlam.ne'
        rw [sub_sq, mul_pow, sq_abs]
        field_simp
      have hwf : -(|w (q, η)| * ε) ≤ w (q, η) * f (q, η) := by
        have h1 : |w (q, η) * f (q, η)| ≤ |w (q, η)| * ε := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hfq (abs_nonneg _)
        have h2 := neg_abs_le (w (q, η) * f (q, η))
        linarith
      nlinarith
    have hwl : Integrable (fun q : ℝ => w (q, η) * Train.lapS w (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((slice_cont hwc η).mul (slice_cont hlc η)).integrableOn_Ioc
    have hw2 : Integrable (fun q : ℝ => w (q, η) ^ 2) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((slice_cont hwc η).pow 2).integrableOn_Ioc
    have hw1 : Integrable (fun q : ℝ => w (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      (slice_cont hwc η).integrableOn_Ioc
    have hcst : Integrable (fun _ : ℝ => ε ^ 2 / lam ^ 2) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      integrable_const _
    have hnn : 0 ≤ ∫ q in Ioc (-c / 2) (c / 2), (2 * (w (q, η) * Train.lapS w (q, η)) +
        lam ^ 2 * w (q, η) ^ 2 + ε ^ 2 / lam ^ 2 - 2 * h η * w (q, η)) :=
      setIntegral_nonneg measurableSet_Ioc (fun q _ => hpt q)
    have i1 : Integrable (fun q : ℝ => 2 * (w (q, η) * Train.lapS w (q, η)))
        (volume.restrict (Ioc (-c / 2) (c / 2))) := hwl.const_mul 2
    have i2 : Integrable (fun q : ℝ => lam ^ 2 * w (q, η) ^ 2)
        (volume.restrict (Ioc (-c / 2) (c / 2))) := hw2.const_mul _
    have i3 : Integrable (fun q : ℝ => 2 * h η * w (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) := hw1.const_mul _
    have i12 : Integrable (fun q : ℝ => 2 * (w (q, η) * Train.lapS w (q, η)) +
        lam ^ 2 * w (q, η) ^ 2) (volume.restrict (Ioc (-c / 2) (c / 2))) := i1.add i2
    have i123 : Integrable (fun q : ℝ => 2 * (w (q, η) * Train.lapS w (q, η)) +
        lam ^ 2 * w (q, η) ^ 2 + ε ^ 2 / lam ^ 2) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      i12.add hcst
    rw [integral_sub i123 i3, integral_add i12 hcst,
      integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul,
      setIntegral_const, hvol, hmean η, smul_eq_mul] at hnn
    have hm2 := hid η
    have hmη : m η = ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2 := rfl
    rw [hmη] at hP ⊢
    rw [hm2]
    have e2 : c * (ε ^ 2 / lam ^ 2) = c * ε ^ 2 / lam ^ 2 := by ring
    nlinarith
  have hK : 0 ≤ c * ε ^ 2 / lam ^ 2 := by positivity
  have hB0 : 0 ≤ c * M ^ 2 := by positivity
  have hfin := ode_abs hlam hB0 hK hm hm1 hineq hmb
  intro η hη
  have h1 := hfin η hη
  have e : c * ε ^ 2 / lam ^ 2 / lam ^ 2 = c * ε ^ 2 / lam ^ 4 := by
    rw [div_div, ← pow_add]
  rw [e] at h1
  exact h1

/-- **Pointwise transverse tail of a zero-mean solution.** With `w₁ = ∂_q w` satisfying the same
hypotheses (with `Δw₁ = f₁ + h₁(η)`), for `|η| ≥ η₁`:
`w(q,η)² ≤ (2 + c²) (M² e^{-λ(|η|-η₁)} + ε²/λ⁴)`, `λ = 2π/c`. -/
theorem zeroMean_sq_tail {c M ε η₁ : ℝ} (hc : 0 < c) {w w₁ f f₁ : Plane → ℝ} {h h₁ : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hw₁ : ContDiff ℝ 2 w₁)
    (hper : Cyl.IsPeriodic c w) (hper₁ : Cyl.IsPeriodic c w₁)
    (hmean : ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), w (q, η) = 0)
    (hmean₁ : ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), w₁ (q, η) = 0)
    (hq : ∀ z : Plane, Cyl.partialQ w z = w₁ z)
    (hlap : ∀ z : Plane, Train.lapS w z = f z + h z.2)
    (hlap₁ : ∀ z : Plane, Train.lapS w₁ z = f₁ z + h₁ z.2)
    (hM : ∀ z : Plane, η₁ ≤ |z.2| → |w z| ≤ M) (hM₁ : ∀ z : Plane, η₁ ≤ |z.2| → |w₁ z| ≤ M)
    (hf : ∀ z : Plane, η₁ ≤ |z.2| → |f z| ≤ ε) (hf₁ : ∀ z : Plane, η₁ ≤ |z.2| → |f₁ z| ≤ ε) :
    ∀ z : Plane, η₁ ≤ |z.2| →
      w z ^ 2 ≤ (2 + c ^ 2) *
        (M ^ 2 * Real.exp (-((2 * π / c) * (|z.2| - η₁))) + ε ^ 2 / (2 * π / c) ^ 4) := by
  intro z hz
  have hs := UnforcedLeray.Short.PartI.goodSlice_sup_sq_le hc hw hper z
  have hqf : Cyl.partialQ w = w₁ := funext hq
  rw [hqf] at hs
  have e0 := slice_energy_tail hc hw hper hmean hlap hM hf z.2 hz
  have e1 := slice_energy_tail hc hw₁ hper₁ hmean₁ hlap₁ hM₁ hf₁ z.2 hz
  set X : ℝ := M ^ 2 * Real.exp (-((2 * π / c) * (|z.2| - η₁))) + ε ^ 2 / (2 * π / c) ^ 4
    with hX
  have hX' : c * M ^ 2 * Real.exp (-((2 * π / c) * (|z.2| - η₁))) +
      c * ε ^ 2 / (2 * π / c) ^ 4 = c * X := by rw [hX]; ring
  rw [hX'] at e0 e1
  have hci : 0 ≤ 2 * c⁻¹ := by positivity
  calc w z ^ 2 ≤ 2 * c⁻¹ * (∫ q in Ioc (-c / 2) (c / 2), w (q, z.2) ^ 2) +
        c * ∫ q in Ioc (-c / 2) (c / 2), w₁ (q, z.2) ^ 2 := hs
    _ ≤ 2 * c⁻¹ * (c * X) + c * (c * X) := by
        gcongr
    _ = (2 + c ^ 2) * X := by
        have e : 2 * c⁻¹ * (c * X) = 2 * X := by field_simp
        rw [e]; ring

end UnforcedLeray.Short.PartIIIb.Concrete.FluctTail
