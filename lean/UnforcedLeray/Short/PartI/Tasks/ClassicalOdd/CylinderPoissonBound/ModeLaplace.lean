import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/ModeLaplace`: the `q`-mode of the Laplacian (leaf O2)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the Fourier
modes in `q` of the bounded periodic pressure equation `Δq = -∂_i u_j ∂_j u_i`).

Target: `CylPoisModeLaplace` (`Short/PartI/Sub/T02_3_8.lean`, leaf O2): for a real `C²` `c`-periodic
`q` and `n ≠ 0`, the `n`-th `q`-mode of `Δq` is the mode of `∂_η²` minus `(2πn/c)²` times the mode
of `q`.

Proof.  Put `f = (q : ℂ)`.  The coercion commutes with `∂_q` and `∂_η`
(`cpML_partialQ_ofReal`, `cpML_partialEta_ofReal`), so `Δ(q : ℂ)` is the sum of two continuous
terms.  Modes are additive on continuous summands (`cpML_qMode_add`).  Applying
`Cyl.qMode_partialQ` twice gives the factor `(2πin/c)² = -(2πn/c)²`.

All auxiliary names start with `cpML`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The coercion of a real function commutes with the classical `q`-derivative. -/
theorem cpML_partialQ_ofReal (g : Plane → ℝ) (hg : Differentiable ℝ g) :
    Cyl.partialQ (fun z => ((g z : ℝ) : ℂ)) = fun z => ((Cyl.partialQ g z : ℝ) : ℂ) := by
  funext z
  exact (Cyl.hasDerivAt_sliceQ hg z.1 z.2).ofReal_comp.deriv

/-- The coercion of a real function commutes with the classical `η`-derivative. -/
theorem cpML_partialEta_ofReal (g : Plane → ℝ) (hg : Differentiable ℝ g) :
    Cyl.partialEta (fun z => ((g z : ℝ) : ℂ)) = fun z => ((Cyl.partialEta g z : ℝ) : ℂ) := by
  funext z
  exact (Cyl.hasDerivAt_sliceEta hg z.1 z.2).ofReal_comp.deriv

/-- The `n`-th `q`-mode is additive on continuous summands. -/
theorem cpML_qMode_add {c : ℝ} (hc : 0 < c) (n : ℤ) {A B : Plane → ℂ}
    (hA : Continuous A) (hB : Continuous B) (η : ℝ) :
    Cyl.qMode c hc n (fun z => A z + B z) η = Cyl.qMode c hc n A η + Cyl.qMode c hc n B η := by
  have hfo : Continuous (fun x : ℝ => fourier (-n) (x : AddCircle (c / 2 - -c / 2))) :=
    (fourier (-n)).continuous.comp (AddCircle.continuous_mk' (c / 2 - -c / 2))
  have hA' : Continuous
      (fun x : ℝ => fourier (-n) (x : AddCircle (c / 2 - -c / 2)) • A (x, η)) :=
    hfo.smul (hA.comp (continuous_id.prodMk continuous_const))
  have hB' : Continuous
      (fun x : ℝ => fourier (-n) (x : AddCircle (c / 2 - -c / 2)) • B (x, η)) :=
    hfo.smul (hB.comp (continuous_id.prodMk continuous_const))
  have hAi : IntervalIntegrable
      (fun x : ℝ => fourier (-n) (x : AddCircle (c / 2 - -c / 2)) • A (x, η))
      MeasureTheory.volume (-c / 2) (c / 2) := hA'.intervalIntegrable _ _
  have hBi : IntervalIntegrable
      (fun x : ℝ => fourier (-n) (x : AddCircle (c / 2 - -c / 2)) • B (x, η))
      MeasureTheory.volume (-c / 2) (c / 2) := hB'.intervalIntegrable _ _
  simp only [Cyl.qMode_eq_integral, smul_add]
  rw [intervalIntegral.integral_add hAi hBi, smul_add]

/-- **Leaf O2** (`CylPoisModeLaplace`): the `n`-th `q`-mode of `Δq` is the mode of `∂_η²` minus
`(2πn/c)²` times the mode of `q`, for `n ≠ 0`. -/
theorem cylPoisModeLaplace : CylPoisModeLaplace := by
  unfold CylPoisModeLaplace
  intro c hc n q hq hper hn η
  have hf2 : ContDiff ℝ 2 (fun z : Plane => ((q z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hfper : Cyl.IsPeriodic c (fun z : Plane => ((q z : ℝ) : ℂ)) :=
    hper.comp (fun x : ℝ => (x : ℂ))
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hq1 : ContDiff ℝ (1 + 1) q := by rwa [one_add_one_eq_two]
  have hdQ : ContDiff ℝ 1 (Cyl.partialQ q) := Cyl.contDiff_partialQ hq1
  have hdE : ContDiff ℝ 1 (Cyl.partialEta q) := Cyl.contDiff_partialEta hq1
  have hdQd : Differentiable ℝ (Cyl.partialQ q) := hdQ.differentiable (by norm_num)
  have hdEd : Differentiable ℝ (Cyl.partialEta q) := hdE.differentiable (by norm_num)
  have e1 : Cyl.partialQ (fun z : Plane => ((q z : ℝ) : ℂ))
      = fun z => ((Cyl.partialQ q z : ℝ) : ℂ) :=
    cpML_partialQ_ofReal q hqd
  have e2 : Cyl.partialEta (fun z : Plane => ((q z : ℝ) : ℂ))
      = fun z => ((Cyl.partialEta q z : ℝ) : ℂ) :=
    cpML_partialEta_ofReal q hqd
  have e3 : Cyl.partialQ (Cyl.partialQ (fun z : Plane => ((q z : ℝ) : ℂ)))
      = fun z => ((Cyl.partialQ (Cyl.partialQ q) z : ℝ) : ℂ) := by
    rw [e1]
    exact cpML_partialQ_ofReal _ hdQd
  have e4 : Cyl.partialEta (Cyl.partialEta (fun z : Plane => ((q z : ℝ) : ℂ)))
      = fun z => ((Cyl.partialEta (Cyl.partialEta q) z : ℝ) : ℂ) := by
    rw [e2]
    exact cpML_partialEta_ofReal _ hdEd
  have hlap : (fun z : Plane => ((Train.lapS q z : ℝ) : ℂ)) =
      fun z => Cyl.partialQ (Cyl.partialQ (fun w : Plane => ((q w : ℝ) : ℂ))) z
        + Cyl.partialEta (Cyl.partialEta (fun w : Plane => ((q w : ℝ) : ℂ))) z := by
    rw [e3, e4]
    funext z
    simp only [Train.lapS, Complex.ofReal_add]
  have hC2 := Cyl.C2.of_contDiff hf2
  have hQQc : Continuous (Cyl.partialQ (Cyl.partialQ (fun z : Plane => ((q z : ℝ) : ℂ)))) :=
    hC2.contQQ
  have hEEc : Continuous (Cyl.partialEta (Cyl.partialEta (fun z : Plane => ((q z : ℝ) : ℂ)))) :=
    hC2.contEtaEta
  have hd1 : ContDiff ℝ 1 (fun z : Plane => ((q z : ℝ) : ℂ)) := hf2.of_le (by norm_num)
  have hf11 : ContDiff ℝ (1 + 1) (fun z : Plane => ((q z : ℝ) : ℂ)) := by
    rwa [one_add_one_eq_two]
  have hdQf : ContDiff ℝ 1 (Cyl.partialQ (fun z : Plane => ((q z : ℝ) : ℂ))) :=
    Cyl.contDiff_partialQ hf11
  have hperQf : Cyl.IsPeriodic c (Cyl.partialQ (fun z : Plane => ((q z : ℝ) : ℂ))) :=
    hfper.partialQ
  have step1 := Cyl.qMode_partialQ hc hdQf hperQf hn η
  have step2 := Cyl.qMode_partialQ hc hd1 hfper hn η
  have key : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ))
      * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ))
      = -(((2 * Real.pi * n / c) ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination ((2 * (Real.pi : ℂ) * (n : ℂ) / (c : ℂ)) ^ 2) * Complex.I_mul_I
  have hQQ : Cyl.qMode c hc n (Cyl.partialQ (Cyl.partialQ (fun z : Plane => ((q z : ℝ) : ℂ)))) η
      = -(((2 * Real.pi * n / c) ^ 2 : ℝ) : ℂ)
        * Cyl.qMode c hc n (fun z : Plane => ((q z : ℝ) : ℂ)) η := by
    rw [step1, step2]
    linear_combination (Cyl.qMode c hc n (fun z : Plane => ((q z : ℝ) : ℂ)) η) * key
  rw [hlap, cpML_qMode_add hc n hQQc hEEc η, hQQ]
  ring

end UnforcedLeray.Short.PartI
