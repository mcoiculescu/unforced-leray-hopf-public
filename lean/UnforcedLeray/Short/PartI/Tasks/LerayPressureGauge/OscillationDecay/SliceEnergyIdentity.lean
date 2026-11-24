import UnforcedLeray.Short.PartI.Sub.T02_2_4
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceIntegralCalculus

/-!
# Part I, task `PartI:T02/2/4/2`: the slice energy identity `SliceEnergyIdentity`

Source of record: `the November 2 reference manuscript`, line 447 (the `L²`-in-`q`
energy of the zero-mean part: `m'' = 2∫|∇w|² + 2∫ wΔw`). Statement: `SliceEnergyIdentity`
(`Short/PartI/Sub/T02_2_4.lean`, line 117).

Proof. Write `m(η) = ∫ w(q,η)² dq` over `Ioc (-c/2) (c/2)`.

* `F₁ = w²` is `C¹` and `∂_η F₁ = 2 w ∂_η w`, so `m' = m₁` with `m₁ η = ∫ ∂_η F₁(q,η) dq`
  (`sliceIntegralCalculus`, part 1).
* `F₂ = 2 w ∂_η w` is `C¹` (`w` is `C²`) and `∂_η F₂ = 2 (∂_η w)² + 2 w ∂_η² w`, so
  `m₁' = ∫ ∂_η F₂ dq` (again `sliceIntegralCalculus`, part 1).
* `∂_η² w = Δw - ∂_q² w`, and for each `η` the one-dimensional integration by parts on the
  period `[-c/2, c/2]` (no boundary term, by periodicity of `w` and of `∂_q w`) gives
  `∫ w ∂_q² w = -∫ (∂_q w)²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **The slice energy identity** (source line 447): for `w` of class `C²` and `c`-periodic in `q`,
the slice energy `m(η) = ∫_{-c/2}^{c/2} w(q,η)² dq` is twice differentiable with
`m' = m₁`, `m₁' = m₂`, where `m₂ = 2∫(∂_η w)² + 2∫(∂_q w)² + 2∫ w Δw`. -/
theorem sliceEnergyIdentity : SliceEnergyIdentity := by
  intro c w hc hw hper
  -- regularity of `w` and of its first derivatives
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) w := by rw [one_add_one_eq_two]; exact hw
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hC2 := Cyl.C2.of_contDiff hw
  have hpe1 : ContDiff ℝ 1 (Cyl.partialEta w) := Cyl.contDiff_partialEta h2
  have hpe1d : Differentiable ℝ (Cyl.partialEta w) := hpe1.differentiable (by norm_num)
  have hlap : ∀ q η : ℝ, Train.lapS w (q, η)
      = Cyl.partialQ (Cyl.partialQ w) (q, η) + Cyl.partialEta (Cyl.partialEta w) (q, η) :=
    fun _ _ => rfl
  -- the `η`-derivative of `w²`
  have hsq : ∀ z : ℝ × ℝ, Cyl.partialEta (fun p => w p ^ 2) z = 2 * w z * Cyl.partialEta w z := by
    intro z
    have h2' : HasDerivAt (fun η => w (z.1, η) ^ 2)
        (Cyl.partialEta w z * w z + w z * Cyl.partialEta w z) z.2 := by
      have h := (Cyl.hasDerivAt_sliceEta hwd z.1 z.2).fun_mul (Cyl.hasDerivAt_sliceEta hwd z.1 z.2)
      simpa only [sq] using h
    have h3 : Cyl.partialEta (fun p => w p ^ 2) z
        = Cyl.partialEta w z * w z + w z * Cyl.partialEta w z := h2'.deriv
    rw [h3]
    ring
  -- the `C¹` integrands
  have hF1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => w p ^ 2) := hw1.pow 2
  have hF2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => 2 * w p * Cyl.partialEta w p) :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × ℝ => (2 : ℝ))).mul hw1).mul hpe1
  -- one-dimensional integration by parts in `q` on one period (no boundary term)
  have hIBP : ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Cyl.partialQ (Cyl.partialQ w) (q, η)
      = -∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2 := by
    intro η
    have hle : -c / 2 ≤ c / 2 := by linarith
    have hd : ∀ x ∈ uIcc (-c / 2) (c / 2),
        HasDerivAt (fun q => w (q, η) * Cyl.partialQ w (q, η))
          (Cyl.partialQ w (x, η) ^ 2 + w (x, η) * Cyl.partialQ (Cyl.partialQ w) (x, η)) x := by
      intro x _
      have h := (Cyl.hasDerivAt_sliceQ hwd x η).fun_mul (Cyl.hasDerivAt_sliceQ hC2.diffQ x η)
      simpa only [sq] using h
    have hint : IntervalIntegrable
        (fun q => Cyl.partialQ w (q, η) ^ 2 + w (q, η) * Cyl.partialQ (Cyl.partialQ w) (q, η))
        volume (-c / 2) (c / 2) :=
      (((osc_slice_continuous hC2.contQ η).pow 2).add
        ((osc_slice_continuous hC2.cont η).mul (osc_slice_continuous hC2.contQQ η))).intervalIntegrable
          _ _
    have hFTC : ∫ x in (-c / 2)..(c / 2),
        (Cyl.partialQ w (x, η) ^ 2 + w (x, η) * Cyl.partialQ (Cyl.partialQ w) (x, η))
          = w (c / 2, η) * Cyl.partialQ w (c / 2, η)
            - w (-c / 2, η) * Cyl.partialQ w (-c / 2, η) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    have hi1 : Integrable (fun q : ℝ => Cyl.partialQ w (q, η) ^ 2)
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hC2.contQ η).pow 2).integrableOn_Ioc
    have hi2 : Integrable (fun q : ℝ => w (q, η) * Cyl.partialQ (Cyl.partialQ w) (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hC2.cont η).mul (osc_slice_continuous hC2.contQQ η)).integrableOn_Ioc
    rw [hper.neg_half η, hper.partialQ.neg_half η, sub_self, intervalIntegral.integral_of_le hle,
      integral_add hi1 hi2] at hFTC
    linarith
  -- the integrand of `m₁` is `∂_η F₂`
  have hkey : ∀ η : ℝ,
      ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta (fun p : ℝ × ℝ => 2 * w p * Cyl.partialEta w p) (q, η)
        = 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta w (q, η) ^ 2)
          + 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2)
          + 2 * (∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η)) := by
    intro η
    -- pointwise: `∂_η (2 w ∂_η w) = 2 (∂_η w)² + 2 w ∂_η² w`
    have hpt : ∀ q : ℝ, Cyl.partialEta (fun p : ℝ × ℝ => 2 * w p * Cyl.partialEta w p) (q, η)
        = 2 * Cyl.partialEta w (q, η) ^ 2
          + 2 * (w (q, η) * Cyl.partialEta (Cyl.partialEta w) (q, η)) := by
      intro q
      have hd := ((hasDerivAt_const η (2 : ℝ)).fun_mul (Cyl.hasDerivAt_sliceEta hwd q η)).fun_mul
        (Cyl.hasDerivAt_sliceEta hpe1d q η)
      have h3 : Cyl.partialEta (fun p : ℝ × ℝ => 2 * w p * Cyl.partialEta w p) (q, η) = _ :=
        hd.deriv
      rw [h3]
      ring
    have hi_a : Integrable (fun q : ℝ => Cyl.partialEta w (q, η) ^ 2)
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hC2.contEta η).pow 2).integrableOn_Ioc
    have hi_b : Integrable (fun q : ℝ => w (q, η) * Cyl.partialEta (Cyl.partialEta w) (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hC2.cont η).mul (osc_slice_continuous hC2.contEtaEta η)).integrableOn_Ioc
    have hi_c : Integrable (fun q : ℝ => w (q, η) * Train.lapS w (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hC2.cont η).mul
        (osc_slice_continuous (osc_lapS_continuous hw) η)).integrableOn_Ioc
    have hi_d : Integrable (fun q : ℝ => w (q, η) * Cyl.partialQ (Cyl.partialQ w) (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((osc_slice_continuous hC2.cont η).mul (osc_slice_continuous hC2.contQQ η)).integrableOn_Ioc
    -- `∫ w ∂_η² w = ∫ w Δw + ∫ (∂_q w)²`, using `∂_η² w = Δw - ∂_q² w` and `hIBP`
    have hB : ∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Cyl.partialEta (Cyl.partialEta w) (q, η)
        = (∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η))
          + ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2 := by
      have hpt2 : ∀ q : ℝ, w (q, η) * Cyl.partialEta (Cyl.partialEta w) (q, η)
          = w (q, η) * Train.lapS w (q, η)
            - w (q, η) * Cyl.partialQ (Cyl.partialQ w) (q, η) := by
        intro q
        rw [hlap q]
        ring
      simp only [hpt2]
      rw [integral_sub hi_c hi_d, hIBP η]
      ring
    simp only [hpt]
    rw [integral_add (hi_a.const_mul 2) (hi_b.const_mul 2), integral_const_mul,
      integral_const_mul, hB]
    ring
  -- assemble the three conditions
  refine ⟨fun η => ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta (fun p => w p ^ 2) (q, η),
    fun η => 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta w (q, η) ^ 2)
      + 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2)
      + 2 * (∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η)), ?_, ?_, fun η => rfl⟩
  · intro η
    exact (sliceIntegralCalculus c hc).1 (fun p => w p ^ 2) hF1 η
  · intro η
    have hD2 := (sliceIntegralCalculus c hc).1
      (fun p : ℝ × ℝ => 2 * w p * Cyl.partialEta w p) hF2 η
    have hm1 : (fun η' => ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta (fun p => w p ^ 2) (q, η'))
        = fun η' => ∫ q in Ioc (-c / 2) (c / 2), 2 * w (q, η') * Cyl.partialEta w (q, η') := by
      funext η'
      simp only [hsq]
    rw [hm1]
    exact hD2.congr_deriv (hkey η)

end UnforcedLeray.Short.PartI
