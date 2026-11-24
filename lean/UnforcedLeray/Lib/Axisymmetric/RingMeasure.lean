import UnforcedLeray.Lib.Axisymmetric.Measure
import UnforcedLeray.Lib.Axisymmetric.RingChart
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# AX03 (measure): `dy = πR² s^{-5/2} ds dη` and the phase-averaged ring-chart integral


§5 Layer 3, target AX03 (`Axi/RingChart.lean`), measure part; bypass BP10 (§4). Blueprint
units served: B0197 (`eq:st18-t00198`, tex 2994–3003: `dy = πR² s^{-5/2} ds dη`), B0219
(`eq:m3-cylinder-measure`, tex 3256–3268), B0550 (tex 8724–8732), B0782 (tex 11237–11243).

`lintegral_ringChart`: for nonnegative measurable `g` on `(s, η)`,
`∫_{ℝ³} g(s(y), η(y)) dy = πR² ∫_{s>0} ∫_η s^{-5/2} g(s, η)` (the full azimuthal integral is
taken, tex 3001). Proof (BP10): cylindrical coordinates (`lintegral_axisymm`), then `z = ηρ/R`
at fixed `ρ`, then `ρ = R s^{-1/2}`.

`phaseAvg_ringChart`: the period average over `τ ∈ (0, P]`, `P = 2c/R` (= `2εc`, tex 2076),
of `∫ G(s, ξ, η) dy` for `G` that is `c`-periodic in `ξ` equals
`πR² ∫_{s>0} ∫_{cell} s^{-5/2} G ds dξ/c dη` (tex 2096: "the period-average cylinder measure
is `dξ/c`"). The cell is the centred `[−c/2, c/2) × ℝ` (`qCell c`), definitionally the
`Cyl.cell c` of target CY01 (decision D1 of `scoping/README.md`); it is defined here so that
this module does not wait for CY01.

The one-dimensional substitution `lintegral_comp_div_pos` is copied from the unit draft

proof); the periodic substitution follows `lintegral_period_shift` there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- The centred cylinder cell `[−c/2, c/2) × ℝ` in the variables `(ξ, η)`; definitionally
`Cyl.cell c` of target CY01. -/
def qCell (c : ℝ) : Set (ℝ × ℝ) := Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)

/-! ### Measurability of the chart -/

theorem measurable_age (R : ℝ) : Measurable (age R) :=
  measurable_const.div (measurable_ϱ.pow_const 2)

theorem measurable_trans (R : ℝ) : Measurable (trans R) :=
  (measurable_const.mul (measurable_coord 2)).div measurable_ϱ

theorem measurable_phase (R : ℝ) : Measurable fun x : ℝ × Space => phase R x.1 x.2 :=
  ((measurable_const.mul measurable_fst).div_const 2).sub
    (measurable_const.mul (Real.measurable_log.comp ((measurable_age R).comp measurable_snd)))

/-! ### One-dimensional substitutions -/

/-- `∫ K(z/k) dz = k ∫ K(η) dη` for `k > 0` (copied from
`Units/B0220/ChangeOfVariables.lean`, `lintegral_comp_div_pos`). -/
theorem lintegral_comp_div_pos {k : ℝ} (hk : 0 < k) (K : ℝ → ℝ≥0∞) :
    ∫⁻ z, K (z / k) = ENNReal.ofReal k * ∫⁻ η, K η := by
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun η => k * η) k univ x :=
    fun x _ => (by simpa using (hasDerivAt_id' x).const_mul k :
      HasDerivAt (fun η : ℝ => k * η) k x).hasDerivWithinAt
  have hinj : InjOn (fun η : ℝ => k * η) univ := fun x _ y _ h =>
    mul_left_cancel₀ hk.ne' h
  have himage : (fun η : ℝ => k * η) '' univ = univ := by
    ext z; simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨z / k, by field_simp⟩
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hderiv hinj
    (fun z => K (z / k))
  rw [himage, Measure.restrict_univ] at hjac
  rw [hjac, abs_of_pos hk, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 2
  funext η
  congr 1
  field_simp

theorem rpow_neg_five_halves {s : ℝ} (hs : 0 < s) : s ^ (-(5 / 2 : ℝ)) = (√s ^ 5)⁻¹ := by
  rw [Real.rpow_neg hs.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  norm_num

/-- The age substitution `s = R²/ρ²`:
`∫_{s>0} s^{-5/2} N(s) ds = ∫_{ρ>0} (2ρ²/R³) N(R²/ρ²) dρ`. -/
theorem lintegral_age_sub {R : ℝ} (hR : 0 < R) (N : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * N s =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 * r ^ 2 / R ^ 3) * N (R ^ 2 / r ^ 2) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => R ^ 2 / r ^ 2) (-(2 * R ^ 2 / x ^ 3)) (Ioi 0) x :=
    fun x hx => (hasDerivAt_sq_div R (ne_of_gt hx)).hasDerivWithinAt
  have hinj : InjOn (fun r : ℝ => R ^ 2 / r ^ 2) (Ioi 0) := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := hx
    have hy0 : (0 : ℝ) < y := hy
    have h1 : R ^ 2 * y ^ 2 = R ^ 2 * x ^ 2 := by
      have := hxy
      simp only at this
      rwa [div_eq_div_iff (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 hy0.ne')] at this
    have h2 : x ^ 2 = y ^ 2 := (mul_left_cancel₀ (pow_ne_zero 2 hR.ne') h1).symm
    exact (pow_left_inj₀ hx0.le hy0.le two_ne_zero).1 h2
  have himage : (fun r : ℝ => R ^ 2 / r ^ 2) '' Ioi 0 = Ioi 0 := by
    ext s
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact div_pos (pow_pos hR 2) (pow_pos hr 2)
    · intro hs
      refine ⟨R / √s, div_pos hR (Real.sqrt_pos.2 hs), ?_⟩
      rw [div_pow, Real.sq_sqrt hs.le]
      field_simp
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun s => ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * N s)
  rw [himage] at hjac
  rw [hjac]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hs0 : (0 : ℝ) < R ^ 2 / r ^ 2 := div_pos (pow_pos hR 2) (pow_pos hr0 2)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  have hsq : √(R ^ 2 / r ^ 2) = R / r := by
    rw [show R ^ 2 / r ^ 2 = (R / r) ^ 2 by ring, Real.sqrt_sq (div_pos hR hr0).le]
  rw [abs_neg, abs_of_pos (div_pos (mul_pos two_pos (pow_pos hR 2)) (pow_pos hr0 3)),
    rpow_neg_five_halves hs0, hsq]
  first
  | (field_simp; done)
  | (field_simp; ring)

/-! ### `dy = πR² s^{-5/2} ds dη` -/

/-- **AX03 `lintegral_ringChart`** (B0197, tex 3001: `dy = πR² s^{-5/2} ds dη`, full azimuthal
integral taken). -/
theorem lintegral_ringChart {R : ℝ} (hR : 0 < R) (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (age R y, trans R y) =
      ENNReal.ofReal (π * R ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) * g p := by
  have hGm : Measurable fun p : ℝ × ℝ => g (R ^ 2 / p.1 ^ 2, R * p.2 / p.1) :=
    hg.comp ((measurable_const.div (measurable_fst.pow_const 2)).prodMk
      ((measurable_const.mul measurable_snd).div measurable_fst))
  have h1 : ∫⁻ y, g (age R y, trans R y) =
      ENNReal.ofReal (2 * π) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal p.1 * g (R ^ 2 / p.1 ^ 2, R * p.2 / p.1) :=
    lintegral_axisymm _ hGm
  have hH : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * g (R ^ 2 / p.1 ^ 2, R * p.2 / p.1) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul hGm
  have hH2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) * g p :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hg
  rw [h1, Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ _ hH, setLIntegral_prod_univ _ hH2]
  have hL1 : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ z, ENNReal.ofReal r * g (R ^ 2 / r ^ 2, R * z / r) =
      ENNReal.ofReal (R ^ 2 / 2) *
        (ENNReal.ofReal (2 * r ^ 2 / R ^ 3) * ∫⁻ η, g (R ^ 2 / r ^ 2, η)) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hz : ∫⁻ z, g (R ^ 2 / r ^ 2, R * z / r) =
        ENNReal.ofReal (r / R) * ∫⁻ η, g (R ^ 2 / r ^ 2, η) := by
      rw [← lintegral_comp_div_pos (div_pos hr0 hR) (fun η => g (R ^ 2 / r ^ 2, η))]
      refine lintegral_congr fun z => ?_
      congr 2
      field_simp
    rw [hz, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hr0.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ R ^ 2 / 2)]
    congr 2
    first
    | (field_simp; done)
    | (field_simp; ring)
  have hR1 : ∀ s : ℝ, ∫⁻ η, ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * g (s, η) =
      ENNReal.ofReal (s ^ (-(5 / 2 : ℝ))) * ∫⁻ η, g (s, η) :=
    fun s => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [setLIntegral_congr_fun measurableSet_Ioi hL1, lintegral_congr hR1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_age_sub hR, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
  congr 2
  ring

/-! ### The phase-averaged ring-chart integral -/

theorem phase_eq (R τ : ℝ) (y : Space) :
    phase R τ y = (R / 2) * τ + (-(R / 2) * Real.log (age R y)) := by
  unfold phase
  ring

/-- One period of an affine substitution of a `c`-periodic function, onto the centred
cell: `∫_{(0, c/k]} h(kτ + a) dτ = k⁻¹ ∫_{[−c/2, c/2)} h`. -/
theorem lintegral_periodic_affine {c k : ℝ} (hc : 0 < c) (hk : 0 < k) (h : ℝ → ℝ≥0∞)
    (hper : Function.Periodic h c) (a : ℝ) :
    ∫⁻ τ in Ioc 0 (c / k), h (k * τ + a) =
      ENNReal.ofReal k⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), h q := by
  have hderiv : ∀ x ∈ Ioc 0 (c / k),
      HasDerivWithinAt (fun τ : ℝ => k * τ + a) k (Ioc 0 (c / k)) x := fun x _ => by
    have := ((hasDerivAt_id' x).const_mul k).add_const a
    simpa using this.hasDerivWithinAt
  have hinj : InjOn (fun τ : ℝ => k * τ + a) (Ioc 0 (c / k)) := fun x _ y _ hxy => by
    simp only [add_left_inj] at hxy
    exact mul_left_cancel₀ hk.ne' hxy
  have himage : (fun τ : ℝ => k * τ + a) '' Ioc 0 (c / k) = Ioc a (a + c) := by
    ext x
    simp only [mem_image, mem_Ioc]
    constructor
    · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
      have h3 : k * τ ≤ c := by rwa [le_div_iff₀ hk, mul_comm] at h2
      exact ⟨by nlinarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(x - a) / k, ⟨div_pos (by linarith) hk, ?_⟩, ?_⟩
      · exact div_le_div_of_nonneg_right (by linarith) hk.le
      · field_simp
        ring
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj h
  rw [himage, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos hk] at hjac
  have hcircle : ∫⁻ q in Ioc a (a + c), h q = ∫⁻ q in Ico (-c / 2) (c / 2), h q := by
    have : Fact (0 < c) := ⟨hc⟩
    have e1 := AddCircle.lintegral_preimage (T := c) a hper.lift
    have e2 := AddCircle.lintegral_preimage (T := c) (-c / 2) hper.lift
    simp only [Function.Periodic.lift_coe] at e1 e2
    rw [e1, ← e2, show -c / 2 + c = c / 2 by ring]
    exact (setLIntegral_congr Ico_ae_eq_Ioc).symm
  rw [hcircle] at hjac
  rw [hjac, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hk.le), inv_mul_cancel₀ hk.ne',
    ENNReal.ofReal_one, one_mul]

/-- Fubini on the cell: `∫_{cell} H = ∫_η ∫_{[−c/2,c/2)} H(ξ, η) dξ dη`. -/
theorem lintegral_qCell (c : ℝ) {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x in qCell c, H x = ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), H (q, η) := by
  rw [qCell, Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ _ hH]
  exact lintegral_lintegral_swap (f := fun q η => H (q, η)) hH.aemeasurable

/-- **AX03 `phaseAvg_ringChart`** (B0219, tex 3256–3268; tex 2096). For `G(s, (ξ, η))`
nonnegative, measurable and `c`-periodic in `ξ`, and `P = 2c/R`,
`P⁻¹ ∫_{(0,P]} ∫_{ℝ³} G(s, ξ, η) dy dτ = πR² ∫_{s>0} ∫_{cell} s^{-5/2} G ds dξ/c dη`. -/
theorem phaseAvg_ringChart {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (G : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hG : Measurable G)
    (hper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η))) :
    (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, G (age R y, (phase R τ y, trans R y)) =
      ENNReal.ofReal (π * R ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p := by
  have hk : 0 < R / 2 := by positivity
  have hP0 : 0 < P := by rw [hP]; exact div_pos (mul_pos two_pos hc) hR
  have hPk : P = c / (R / 2) := by rw [hP]; field_simp
  -- measurability
  have hGm : Measurable fun x : ℝ × Space => G (age R x.2, (phase R x.1 x.2, trans R x.2)) :=
    hG.comp (((measurable_age R).comp measurable_snd).prodMk
      ((measurable_phase R).prodMk ((measurable_trans R).comp measurable_snd)))
  have hgm : Measurable fun p : ℝ × ℝ => ∫⁻ q in Ico (-c / 2) (c / 2), G (p.1, (q, p.2)) :=
    (hG.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).lintegral_prod_right'
  -- Step 1: Tonelli, then one phase period at fixed `y`
  rw [lintegral_lintegral_swap (f := fun τ y => G (age R y, (phase R τ y, trans R y)))
    hGm.aemeasurable]
  have hstep : ∀ y : Space, ∫⁻ τ in Ioc 0 P, G (age R y, (phase R τ y, trans R y)) =
      ENNReal.ofReal (R / 2)⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), G (age R y, (q, trans R y)) := by
    intro y
    have hper1 : Function.Periodic (fun q => G (age R y, (q, trans R y))) c :=
      fun q => hper _ _ _
    have := lintegral_periodic_affine hc hk _ hper1 (-(R / 2) * Real.log (age R y))
    rw [hPk]
    simp only [phase_eq]
    exact this
  rw [lintegral_congr hstep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Step 2: the ring-chart integral
  have h3 : ∫⁻ y, ∫⁻ q in Ico (-c / 2) (c / 2), G (age R y, (q, trans R y)) =
      ENNReal.ofReal (π * R ^ 2) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) *
          ∫⁻ q in Ico (-c / 2) (c / 2), G (p.1, (q, p.2)) :=
    lintegral_ringChart hR _ hgm
  rw [h3]
  -- Step 3: the right side as an iterated integral
  have hF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const _))).mul hG
  have hK : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) *
      ∫⁻ q in Ico (-c / 2) (c / 2), G (p.1, (q, p.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hgm
  have hRHS : ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p =
      ENNReal.ofReal c⁻¹ * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) *
          ∫⁻ q in Ico (-c / 2) (c / 2), G (p.1, (q, p.2)) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
      lintegral_prod _ hF.aemeasurable, Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ _ hK,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [← Measure.volume_eq_prod ℝ ℝ, lintegral_qCell c
      (H := fun x : ℝ × ℝ => ENNReal.ofReal (c⁻¹ * (s, x).1 ^ (-(5 / 2 : ℝ))) * G (s, x))
      (hF.comp measurable_prodMk_left), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun η => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun q => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  rw [hRHS]
  have hconst : (ENNReal.ofReal P)⁻¹ * ENNReal.ofReal (R / 2)⁻¹ = ENNReal.ofReal c⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hP0, ← ENNReal.ofReal_mul (inv_nonneg.2 hP0.le), hPk,
      inv_div, div_mul_eq_mul_div, mul_inv_cancel₀ hk.ne', one_div]
  rw [← mul_assoc, hconst, mul_left_comm]

end UnforcedLeray.Axi
