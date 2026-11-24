import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_9

/-!
# `PartIII-a:T21/2/2/3/5/3/2` leaf `PhysWDeriv`: calculus of the weight

Source of record: `the November 2 reference manuscript` (SP) lines 2860 (`d_z/d = -1/(2θ)`),
3044-3047 (`p_d`). With `a = clockA ν r`, `d = c/√a`, `K = a y₂² + (c/π)² sin²(π√a y₁/c)`:
`physW(r', √a y) = (1 + K/a(r'))^{-m}` and `Q_d(y) = 1 + K/a` (`Qf_cell_eq`), and the identity
`d ∂_dQ_d + y·∇Q_d = 2(Q_d - 1)` (`hT` below) closes the computation.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-- Algebra of the rescaling `x = √a y`, `d' = c/√a'`. -/
theorem alg_scaled (a a' c y1 y2 : ℝ) (ha : 0 < a) (ha' : 0 < a') (hc : 0 < c) :
    1 + (Real.sqrt a * y2 / Real.sqrt a') ^ 2 +
        (c / Real.sqrt a' / Real.pi) ^ 2 *
          Real.sin (Real.pi * (Real.sqrt a * y1 / Real.sqrt a') / (c / Real.sqrt a')) ^ 2 =
      1 + (a * y2 ^ 2 + (c / Real.pi) ^ 2 * Real.sin (Real.pi * (Real.sqrt a * y1) / c) ^ 2) / a' := by
  have hs' : Real.sqrt a' ≠ 0 := (Real.sqrt_pos.mpr ha').ne'
  have hθ : Real.pi * (Real.sqrt a * y1 / Real.sqrt a') / (c / Real.sqrt a') =
      Real.pi * (Real.sqrt a * y1) / c := by
    field_simp
  have h1 : (Real.sqrt a * y2 / Real.sqrt a') ^ 2 = a * y2 ^ 2 / a' := by
    rw [div_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt ha'.le]
  have h2 : (c / Real.sqrt a' / Real.pi) ^ 2 = (c / Real.pi) ^ 2 / a' := by
    simp only [div_pow, Real.sq_sqrt ha'.le]
    ring
  rw [h1, h2, hθ]
  ring

/-- The fixed-cell weight at `√a y` is `(1 + K/a')^{-m}`. -/
theorem physW_smul_eq (ν c m r' r : ℝ) (y : ℝ × ℝ) (hc : 0 < c) (ha : 0 < clockA ν r)
    (ha' : 0 < clockA ν r') :
    physW ν c m r' (Real.sqrt (clockA ν r) • y) =
      (1 + (clockA ν r * y.2 ^ 2 + (c / Real.pi) ^ 2 *
          Real.sin (Real.pi * (Real.sqrt (clockA ν r) * y.1) / c) ^ 2) / clockA ν r') ^ (-m) := by
  unfold physW periodicWeight cellLen
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  congr 1
  exact alg_scaled (clockA ν r) (clockA ν r') c y.1 y.2 ha ha' hc

/-- `Q_d(y) = 1 + K/a` for `d = c/√a`. -/
theorem Qf_cell_eq (c a : ℝ) (hc : 0 < c) (ha : 0 < a) (y : ℝ × ℝ) :
    WLB.Qf (cellLen c a) y = 1 + (a * y.2 ^ 2 + (c / Real.pi) ^ 2 *
          Real.sin (Real.pi * (Real.sqrt a * y.1) / c) ^ 2) / a := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hθ : Real.pi * y.1 / cellLen c a = Real.pi * (Real.sqrt a * y.1) / c := by
    unfold cellLen
    field_simp
  have h2 : (cellLen c a / Real.pi) ^ 2 = (c / Real.pi) ^ 2 / a := by
    unfold cellLen
    simp only [div_pow, Real.sq_sqrt ha.le]
    ring
  unfold WLB.Qf
  rw [hθ, h2]
  field_simp
  ring

theorem physWDeriv (m : ℝ) : PhysWDeriv m := by
  unfold PhysWDeriv
  intro ν c r y hc ha
  set K : ℝ := clockA ν r * y.2 ^ 2 + (c / Real.pi) ^ 2 *
    Real.sin (Real.pi * (Real.sqrt (clockA ν r) * y.1) / c) ^ 2 with hKdef
  set d : ℝ := cellLen c (clockA ν r) with hd_def
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ clockA ν r * y.2 ^ 2 := mul_nonneg ha.le (sq_nonneg _)
    have h2 : 0 ≤ (c / Real.pi) ^ 2 *
        Real.sin (Real.pi * (Real.sqrt (clockA ν r) * y.1) / c) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [hKdef]
    linarith
  have hpos : ∀ᶠ r' in 𝓝 r, 0 < clockA ν r' := by
    have hcont : Continuous (fun r' => clockA ν r') := by
      unfold clockA
      fun_prop
    exact (hcont.tendsto r).eventually (lt_mem_nhds ha)
  have hev : ∀ᶠ r' in 𝓝 r, physW ν c m r' (Real.sqrt (clockA ν r) • y) =
      (1 + K / clockA ν r') ^ (-m) := by
    filter_upwards [hpos] with r' hr'
    exact physW_smul_eq ν c m r' r y hc ha hr'
  have hA : HasDerivAt (fun r' => clockA ν r') ν r := by
    have h := ((hasDerivAt_id r).const_mul ν).const_add 1
    simpa [clockA] using h
  have hgpos : 0 < 1 + K / clockA ν r := by
    have := div_nonneg hK0 ha.le
    linarith
  have hp : HasDerivAt (fun r' => (1 + K / clockA ν r') ^ (-m))
      ((((0 : ℝ) * clockA ν r - K * ν) / clockA ν r ^ 2) * (-m) * (1 + K / clockA ν r) ^ (-m - 1)) r :=
    ((((hasDerivAt_const r K).div hA ha.ne').const_add 1).rpow_const (Or.inl hgpos.ne'))
  have hfin := hp.congr_of_eventuallyEq hev
  rw [hfin.deriv]
  have hd : d ≠ 0 := (div_pos hc (Real.sqrt_pos.mpr ha)).ne'
  have hQ : WLB.Qf d y = 1 + K / clockA ν r := Qf_cell_eq c (clockA ν r) hc ha y
  rw [← hQ]
  have hdt : dtW m d (ν * clockA ν r) y =
      WLB.DQ d y * (-m) * WLB.Qf d y ^ (-m - 1) * (d * (ν * clockA ν r) / 2) := by
    unfold dtW
    rw [(pw_hasDerivAt_d (-m) d hd y).deriv]
  have hlog0 : (fun x => Real.log (periodicWeight (-m) d x)) =
      fun z => (-m) * Real.log (WLB.Qf d z) :=
    funext fun z => WLB.logW (-m) d z
  have hp0 : B0579.pd 0 (periodicWeight (-m) d) y =
      WLB.Qf d y ^ (-m) * ((-m) * (WLB.Pf d y / WLB.Qf d y)) := by
    rw [pw_pd_eq, hlog0, WLB.F1 (-m) d hd y, pw_eq_Qf]
  have hp1 : B0579.pd 1 (periodicWeight (-m) d) y =
      WLB.Qf d y ^ (-m) * ((-m) * (2 * y.2 / WLB.Qf d y)) := by
    rw [pw_pd_eq, hlog0, WLB.F2 (-m) d y, pw_eq_Qf]
  have hT : d * WLB.DQ d y + y.1 * WLB.Pf d y + y.2 * (2 * y.2) = 2 * (WLB.Qf d y - 1) := by
    unfold WLB.DQ WLB.Pf WLB.Qf
    field_simp
    ring
  have hK : K = clockA ν r * (WLB.Qf d y - 1) := by
    rw [hQ]
    field_simp
    ring
  have hE : WLB.Qf d y ^ (-m - 1) = WLB.Qf d y ^ (-m) * (WLB.Qf d y)⁻¹ := by
    rw [Real.rpow_sub_one (WLB.Qf_pos d y).ne', div_eq_mul_inv]
  rw [hdt, hp0, hp1, hE]
  linear_combination (-((clockA ν r)⁻¹ ^ 2 * (-m) * (WLB.Qf d y ^ (-m) * (WLB.Qf d y)⁻¹) * ν)) * hK +
    ((clockA ν r)⁻¹ ^ 2 * (-m) * (WLB.Qf d y ^ (-m) * (WLB.Qf d y)⁻¹) * ν * (clockA ν r / 2)) * hT

end UnforcedLeray.Short.IIIa.AdjE1
