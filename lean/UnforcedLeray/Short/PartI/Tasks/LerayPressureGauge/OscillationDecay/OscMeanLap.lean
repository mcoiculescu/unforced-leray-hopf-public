import UnforcedLeray.Short.PartI.Sub.T02_2_4
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceIntegralCalculus

/-!
# Part I, task `PartI:T02/2/4` leaf: `OscMeanLap` (smoothness and Laplacian of the fluctuation)

Source of record: `the November 2 reference manuscript`, line 447 (the fluctuation
`w = u - ū` of a bounded periodic `C²` function and its Laplacian). Target: `OscMeanLap`
(`Short/PartI/Sub/T02_2_4.lean`, line 375).

Proof. Write `h = hmean c u`.

* `sliceIntegralCalculus` (applied to `u`, then to `∂_η u`) gives `h' = hmean c (∂_η u)` and
  `h'' = hmean c (∂_η² u)` with `h''` continuous; hence `h` is `C²`.
* The periodic `q`-mean of `∂_q² u` vanishes (`oscMeanLap_integral_partialQ_zero`, applied to the
  `C¹`, `c`-periodic function `∂_q u`); so `h'' = hmean c (Δu)`.
* For `w = u - h(η)`: `∂_q w = ∂_q u`, `∂_η w = ∂_η u - h'(η)` and `∂_η² w = ∂_η² u - h''(η)`;
  hence `Δw = Δu - hmean c (Δu)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The `q`-integral over one period of `∂_q F` vanishes for a `C¹`, `c`-periodic `F`. -/
theorem oscMeanLap_integral_partialQ_zero {c : ℝ} {F : Plane → ℝ} (hc : 0 < c)
    (hF : ContDiff ℝ 1 F) (hper : Cyl.IsPeriodic c F) (η : ℝ) :
    ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ F (q, η) = 0 := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hcont : Continuous (Cyl.partialQ F) := (Cyl.C1_partial_of_contDiff hF).1
  have hftc : ∫ q in (-c / 2)..(c / 2), Cyl.partialQ F (q, η)
      = F (c / 2, η) - F (-c / 2, η) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun q => F (q, η))
      (f' := fun q => Cyl.partialQ F (q, η))
      (fun q _ => Cyl.hasDerivAt_sliceQ hd q η)
      ((hcont.comp (continuous_id.prodMk (continuous_const (y := η)))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith)] at hftc
  rw [hftc, hper.neg_half η, sub_self]

/-- **Smoothness and Laplacian of the fluctuation** (source line 447). -/
theorem oscMeanLap : OscMeanLap := by
  intro c u hc hu hper
  have hSIC := sliceIntegralCalculus c hc
  have hu11 : ContDiff ℝ (1 + 1) u := by rwa [one_add_one_eq_two]
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hEu : ContDiff ℝ 1 (Cyl.partialEta u) := Cyl.contDiff_partialEta hu11
  have hQu : ContDiff ℝ 1 (Cyl.partialQ u) := Cyl.contDiff_partialQ hu11
  have hEuD : Differentiable ℝ (Cyl.partialEta u) := hEu.differentiable (by norm_num)
  have hEEcont : Continuous (Cyl.partialEta (Cyl.partialEta u)) :=
    (Cyl.C1_partial_of_contDiff hEu).2
  have hQQcont : Continuous (Cyl.partialQ (Cyl.partialQ u)) :=
    (Cyl.C1_partial_of_contDiff hQu).1
  -- first and second horizontal derivatives of the average `hmean c u`
  have hderiv0 : ∀ η : ℝ, HasDerivAt (hmean c u) (hmean c (Cyl.partialEta u) η) η :=
    fun η => (hSIC.1 u hu1 η).const_smul c⁻¹
  have hderiv1 : ∀ η : ℝ, HasDerivAt (hmean c (Cyl.partialEta u))
      (hmean c (Cyl.partialEta (Cyl.partialEta u)) η) η :=
    fun η => (hSIC.1 (Cyl.partialEta u) hEu η).const_smul c⁻¹
  have hcont2 : Continuous (hmean c (Cyl.partialEta (Cyl.partialEta u))) :=
    (hSIC.2 _ hEEcont).const_smul c⁻¹
  have hdeq : deriv (hmean c u) = hmean c (Cyl.partialEta u) :=
    funext fun η => (hderiv0 η).deriv
  have hdeq1 : deriv (hmean c (Cyl.partialEta u)) = hmean c (Cyl.partialEta (Cyl.partialEta u)) :=
    funext fun η => (hderiv1 η).deriv
  -- `hmean c u` is `C²`
  have hC2 : ContDiff ℝ 2 (hmean c u) := by
    have hd0 : Differentiable ℝ (hmean c u) := fun η => (hderiv0 η).differentiableAt
    have hdC1 : ContDiff ℝ 1 (deriv (hmean c u)) := by
      rw [hdeq]
      exact contDiff_one_iff_deriv.2
        ⟨fun η => (hderiv1 η).differentiableAt, by rw [hdeq1]; exact hcont2⟩
    have key : ContDiff ℝ (1 + 1) (hmean c u) :=
      (contDiff_succ_iff_deriv (n := 1)).2 ⟨hd0, fun h => absurd h (by decide), hdC1⟩
    rwa [one_add_one_eq_two] at key
  -- the fluctuation `w = u - hmean c u (η)` is `C²`
  have hw : ContDiff ℝ 2 (fun z : Plane => u z - hmean c u z.2) :=
    hu.sub (hC2.comp contDiff_snd)
  -- partial derivatives of the fluctuation
  have hQw : ∀ z : Plane,
      Cyl.partialQ (fun z : Plane => u z - hmean c u z.2) z = Cyl.partialQ u z := by
    intro z
    show deriv (fun q : ℝ => u (q, z.2) - hmean c u z.2) z.1 = deriv (fun q : ℝ => u (q, z.2)) z.1
    rw [deriv_sub_const]
  have hQfun : Cyl.partialQ (fun z : Plane => u z - hmean c u z.2) = Cyl.partialQ u :=
    funext hQw
  have hQQ : Cyl.partialQ (Cyl.partialQ (fun z : Plane => u z - hmean c u z.2))
      = Cyl.partialQ (Cyl.partialQ u) := by
    rw [hQfun]
  have hEw : ∀ z : Plane,
      Cyl.partialEta (fun z : Plane => u z - hmean c u z.2) z
        = Cyl.partialEta u z - hmean c (Cyl.partialEta u) z.2 := by
    intro z
    exact ((Cyl.hasDerivAt_sliceEta hud z.1 z.2).sub (hderiv0 z.2)).deriv
  have hEEw : ∀ z : Plane,
      Cyl.partialEta (Cyl.partialEta (fun z : Plane => u z - hmean c u z.2)) z
        = Cyl.partialEta (Cyl.partialEta u) z
          - hmean c (Cyl.partialEta (Cyl.partialEta u)) z.2 := by
    intro z
    have hfun : (fun η : ℝ => Cyl.partialEta (fun z : Plane => u z - hmean c u z.2) (z.1, η))
        = fun η : ℝ => Cyl.partialEta u (z.1, η) - hmean c (Cyl.partialEta u) η :=
      funext fun η => hEw (z.1, η)
    show deriv (fun η : ℝ => Cyl.partialEta (fun z : Plane => u z - hmean c u z.2) (z.1, η)) z.2
      = _
    rw [hfun]
    exact ((Cyl.hasDerivAt_sliceEta hEuD z.1 z.2).sub (hderiv1 z.2)).deriv
  -- the `q`-mean of `∂_q² u` vanishes, so `hmean c (Δu) = h''`
  have hsplit : ∀ η : ℝ,
      hmean c (Train.lapS u) η = hmean c (Cyl.partialEta (Cyl.partialEta u)) η := by
    intro η
    have hQ0 : ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ (Cyl.partialQ u) (q, η) = 0 :=
      oscMeanLap_integral_partialQ_zero hc hQu (Cyl.IsPeriodic.partialQ hper) η
    have hcq : Continuous (fun q : ℝ => Cyl.partialQ (Cyl.partialQ u) (q, η)) :=
      hQQcont.comp (continuous_id.prodMk (continuous_const (y := η)))
    have hce : Continuous (fun q : ℝ => Cyl.partialEta (Cyl.partialEta u) (q, η)) :=
      hEEcont.comp (continuous_id.prodMk (continuous_const (y := η)))
    have hint : (∫ q in Ioc (-c / 2) (c / 2), Train.lapS u (q, η))
        = (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ (Cyl.partialQ u) (q, η))
          + (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta (Cyl.partialEta u) (q, η)) := by
      show (∫ q in Ioc (-c / 2) (c / 2),
          (Cyl.partialQ (Cyl.partialQ u) (q, η) + Cyl.partialEta (Cyl.partialEta u) (q, η)))
        = _
      exact integral_add hcq.integrableOn_Ioc hce.integrableOn_Ioc
    unfold hmean
    rw [hint, hQ0, zero_add]
  refine ⟨hw, fun z => ?_⟩
  rw [hsplit z.2]
  unfold Train.lapS
  rw [hQQ, hEEw z]
  ring

end UnforcedLeray.Short.PartI
