import UnforcedLeray.Short.PartIIb.Sub.T22_2_1

/-!


Source: `the November 2 reference manuscript`
(the weak identity of `IsFreeCylFlow` against time-independent tests; the separated-sum step is
the time slicing of `CylSepSum`).

For one term `χ_k(r) ψ_k(x)`, the `weak` field of `IsFreeCylFlow` gives
`G_k(s) = G_k(t₀) + ∫_{t₀}^s H_k` with `G_k(s) = ∫_cell ω_s ψ_k` and
`H_k(r) = ∫_cell cylFreeIntegrand … ψ_k`. Integration by parts against `χ_k ∈ C¹` (`sep_ibp`)
gives the time-dependent identity term by term; `initial` identifies `f` with `ω t₀` on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- Integrability of `g · φ` on the cell for `g` in the weighted space and a cylinder test. -/
theorem sep_integrableOn_test {c m : ℝ} {g φ : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun x => g x * φ x) (B0579.cell c) := by
  have h := B0579.integrableOn_mul_neg c m (hg.toLp g) ((hφ.memLp (-m)).toLp φ)
  refine h.congr_fun_ae ?_
  filter_upwards [B0579.ac_cellMeasure c m |>.ae_le (MemLp.coeFn_toLp hg),
    B0579.ac_cellMeasure c (-m) |>.ae_le (MemLp.coeFn_toLp (hφ.memLp (-m)))] with x h1 h2
  rw [h1, h2]

/-- Integration by parts against a `C¹` function for a primitive `G = G₀ + ∫ H`. -/
theorem sep_ibp {t₀ t₁ G₀ : ℝ} (ht : t₀ ≤ t₁) (χ H G : ℝ → ℝ)
    (hχ : ContDiffOn ℝ 1 χ (Icc t₀ t₁)) (hH : IntervalIntegrable H volume t₀ t₁)
    (hG : ∀ s ∈ Icc t₀ t₁, G s = G₀ + ∫ r in t₀..s, H r) :
    IntervalIntegrable (fun r => deriv χ r * G r + χ r * H r) volume t₀ t₁ ∧
      χ t₁ * G t₁ - χ t₀ * G₀ = ∫ r in t₀..t₁, (deriv χ r * G r + χ r * H r) := by
  have huIcc : uIcc t₀ t₁ = Icc t₀ t₁ := uIcc_of_le ht
  have hχu : ContDiffOn ℝ 1 χ (uIcc t₀ t₁) := huIcc ▸ hχ
  have hAχ : AbsolutelyContinuousOnInterval χ t₀ t₁ := hχu.absolutelyContinuousOnInterval
  have hI : AbsolutelyContinuousOnInterval (fun s => ∫ r in t₀..s, H r) t₀ t₁ :=
    hH.absolutelyContinuousOnInterval_intervalIntegral (c := t₀) left_mem_uIcc
  have hderI : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc t₀ t₁ →
      deriv (fun s => ∫ r in t₀..s, H r) x = H x := by
    filter_upwards [hH.ae_hasDerivAt_integral] with x hx hxI
    exact (hx (uIoc_subset_uIcc hxI) t₀ left_mem_uIcc).deriv
  have hdI : ∫ x in t₀..t₁, deriv (fun s => ∫ r in t₀..s, H r) x * χ x
      = ∫ x in t₀..t₁, χ x * H x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderI] with x hx hxI
    rw [hx hxI, mul_comm]
  have hIBP := hI.integral_mul_deriv_eq_deriv_mul hAχ
  simp only [intervalIntegral.integral_same, zero_mul, sub_zero] at hIBP
  rw [hdI] at hIBP
  -- hIBP : ∫ I x * deriv χ x = I t₁ * χ t₁ - ∫ χ x * H x
  have hP : ∫ x in t₀..t₁, (∫ s in t₀..x, H s) * deriv χ x
      = ∫ x in t₀..t₁, deriv χ x * (∫ s in t₀..x, H s) :=
    intervalIntegral.integral_congr (fun x _ => mul_comm _ _)
  have hGeq : EqOn G (fun s => G₀ + ∫ r in t₀..s, H r) (uIcc t₀ t₁) :=
    fun s hs => hG s (huIcc ▸ hs)
  have hIc : ContinuousOn (fun s => ∫ r in t₀..s, H r) (uIcc t₀ t₁) := hI.continuousOn
  have hGc : ContinuousOn G (uIcc t₀ t₁) := (continuousOn_const.add hIc).congr hGeq
  have hχc : ContinuousOn χ (uIcc t₀ t₁) := hχu.continuousOn
  have hdχ : IntervalIntegrable (deriv χ) volume t₀ t₁ := hAχ.intervalIntegrable_deriv
  have hi1 : IntervalIntegrable (fun r => deriv χ r * G r) volume t₀ t₁ :=
    hdχ.mul_continuousOn hGc
  have hi2 : IntervalIntegrable (fun r => χ r * H r) volume t₀ t₁ :=
    hH.continuousOn_mul hχc
  have hiI : IntervalIntegrable (fun r => deriv χ r * (∫ s in t₀..r, H s)) volume t₀ t₁ :=
    hdχ.mul_continuousOn hIc
  have e1 : ∫ r in t₀..t₁, (deriv χ r * G r + χ r * H r)
      = ∫ r in t₀..t₁, (G₀ * deriv χ r + (deriv χ r * (∫ s in t₀..r, H s) + χ r * H r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [hGeq hr]
    ring
  have hint2 : IntervalIntegrable (fun r => deriv χ r * (∫ s in t₀..r, H s) + χ r * H r)
      volume t₀ t₁ := hiI.add hi2
  have e2 : ∫ r in t₀..t₁, (G₀ * deriv χ r + (deriv χ r * (∫ s in t₀..r, H s) + χ r * H r))
      = G₀ * (χ t₁ - χ t₀) + ((∫ r in t₀..t₁, deriv χ r * (∫ s in t₀..r, H s))
          + ∫ r in t₀..t₁, χ r * H r) := by
    rw [intervalIntegral.integral_add (hdχ.const_mul G₀) hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiI hi2,
      hAχ.integral_deriv_eq_sub]
  have hGt1 : G t₁ = G₀ + ∫ r in t₀..t₁, H r := hG t₁ (right_mem_Icc.2 ht)
  have hGt0 : G t₀ = G₀ := by
    rw [hG t₀ (left_mem_Icc.2 ht)]
    simp
  have hintI : IntervalIntegrable (fun r => deriv χ r * G r + χ r * H r) volume t₀ t₁ := by
    apply IntervalIntegrable.add
    · exact hi1
    · exact hi2
  refine ⟨hintI, ?_⟩
  have hIBP' : ∫ r in t₀..t₁, deriv χ r * (∫ s in t₀..r, H s)
      = (∫ r in t₀..t₁, H r) * χ t₁ - ∫ x in t₀..t₁, χ x * H x := by
    rw [← hP]
    exact hIBP
  rw [e1, e2, hGt1]
  linear_combination (-1 : ℝ) * hIBP'


/-- Partial derivatives commute with finite linear combinations of test functions. -/
theorem sep_pd_sum {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, Differentiable ℝ (ψ k)) (j : Fin 2) (y : B0579.Plane) :
    B0579.pd j (fun y => ∑ k, a k * ψ k y) y = ∑ k, a k * B0579.pd j (ψ k) y := by
  have h : HasFDerivAt (fun y => ∑ k, a k * ψ k y) (∑ k, a k • fderiv ℝ (ψ k) y) y :=
    HasFDerivAt.fun_sum (fun k _ => ((hψ k y).hasFDerivAt).const_mul (a k))
  unfold B0579.pd
  rw [h.fderiv]
  simp [smul_eq_mul]

/-- The planar Laplacian of a finite linear combination of test functions. -/
theorem sep_lapP {c : ℝ} {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, B0579.IsCylTest c (ψ k)) (x : B0579.Plane) :
    lapP (fun y => ∑ k, a k * ψ k y) x = ∑ k, a k * lapP (ψ k) x := by
  unfold lapP
  have hd : ∀ k, Differentiable ℝ (ψ k) := fun k => (hψ k).differentiable
  have hd0 : ∀ k, Differentiable ℝ (B0579.pd 0 (ψ k)) := fun k => ((hψ k).pd 0).differentiable
  have hd1 : ∀ k, Differentiable ℝ (B0579.pd 1 (ψ k)) := fun k => ((hψ k).pd 1).differentiable
  have h1 : B0579.pd 0 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 0 (ψ k) y :=
    funext fun y => sep_pd_sum a ψ hd 0 y
  have h2 : B0579.pd 1 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 1 (ψ k) y :=
    funext fun y => sep_pd_sum a ψ hd 1 y
  have h3 : B0579.pd 0 (fun y => ∑ k, a k * B0579.pd 0 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 0 (B0579.pd 0 (ψ k)) y :=
    funext fun y => sep_pd_sum a (fun k => B0579.pd 0 (ψ k)) hd0 0 y
  have h4 : B0579.pd 1 (fun y => ∑ k, a k * B0579.pd 1 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 1 (B0579.pd 1 (ψ k)) y :=
    funext fun y => sep_pd_sum a (fun k => B0579.pd 1 (ψ k)) hd1 1 y
  rw [h1, h2, h3, h4]
  simp only [mul_add, Finset.sum_add_distrib]

/-- Pointwise form of the tested right-hand side for a finite sum at a fixed age. -/
theorem sep_pointwise {ν c : ℝ} (tr : B0140.TrainSol ν c) (w : B0579.Plane → ℝ) (r : ℝ)
    {n : ℕ} (χ : Fin n → ℝ → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, B0579.IsCylTest c (ψ k)) (hχ : ∀ k, DifferentiableAt ℝ (χ k) r)
    (x : B0579.Plane) :
    w x * (deriv (fun r' => ∑ k, χ k r' * ψ k x) r
        + ν * lapP (fun y => ∑ k, χ k r * ψ k y) x
        + (tr.v r x 0 * B0579.pd 0 (fun y => ∑ k, χ k r * ψ k y) x
          + tr.v r x 1 * B0579.pd 1 (fun y => ∑ k, χ k r * ψ k y) x))
      = ∑ k, (deriv (χ k) r * (w x * ψ k x)
          + χ k r * cylFreeIntegrand tr w r (ψ k) x) := by
  have hd : deriv (fun r' => ∑ k, χ k r' * ψ k x) r = ∑ k, deriv (χ k) r * ψ k x := by
    apply HasDerivAt.deriv
    exact HasDerivAt.fun_sum (fun k _ => ((hχ k).hasDerivAt).mul_const (ψ k x))
  have hpd0 : B0579.pd 0 (fun y => ∑ k, χ k r * ψ k y) x = ∑ k, χ k r * B0579.pd 0 (ψ k) x :=
    sep_pd_sum (fun k => χ k r) ψ (fun k => (hψ k).differentiable) 0 x
  have hpd1 : B0579.pd 1 (fun y => ∑ k, χ k r * ψ k y) x = ∑ k, χ k r * B0579.pd 1 (ψ k) x :=
    sep_pd_sum (fun k => χ k r) ψ (fun k => (hψ k).differentiable) 1 x
  rw [hd, sep_lapP (fun k => χ k r) ψ hψ x, hpd0, hpd1]
  unfold cylFreeIntegrand
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cylTdSeparated : UnforcedLeray.Short.IIb.CylTdSeparated := by
  intro m hm ν c tr t₀ f ω hc hfl t₁ φ ht hφ
  obtain ⟨n, χ, ψ, hχ, hψ, hφe⟩ := hφ
  have hφfun : φ = fun r x => ∑ k, χ k r * ψ k x := funext fun r => funext fun x => hφe r x
  subst hφfun
  have hmem : ∀ s, t₀ ≤ s → ∀ k, IntegrableOn (fun x => ω s x * ψ k x) (B0579.cell c) :=
    fun s hs k => sep_integrableOn_test (hfl.memX s hs) (hψ k)
  have hinit : ∀ g : B0579.Plane → ℝ,
      ∫ x in B0579.cell c, f x * g x = ∫ x in B0579.cell c, ω t₀ x * g x := by
    intro g
    refine integral_congr_ae ?_
    filter_upwards [hfl.initial] with x hx
    rw [hx]
  have hL1 : ∀ s, t₀ ≤ s → ∫ x in B0579.cell c, ω s x * (∑ k, χ k s * ψ k x)
      = ∑ k, χ k s * ∫ x in B0579.cell c, ω s x * ψ k x := by
    intro s hs
    have hpt : ∀ x, ω s x * (∑ k, χ k s * ψ k x) = ∑ k, χ k s * (ω s x * ψ k x) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hpt]
    rw [integral_finset_sum _ fun k _ => Integrable.const_mul (hmem s hs k) (χ k s)]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hweak : ∀ k, ∀ s ∈ Icc t₀ t₁, (∫ x in B0579.cell c, ω s x * ψ k x)
      = (∫ x in B0579.cell c, ω t₀ x * ψ k x)
        + ∫ r in t₀..s, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x := by
    intro k s hs
    have h := hfl.weak (ψ k) (hψ k) s hs.1
    rw [h, hinit (ψ k)]
  unfold cylTdLhs cylTdRhs
  dsimp only
  rw [hL1 t₁ ht, hinit, hL1 t₀ le_rfl, ← Finset.sum_sub_distrib]
  have hterm := fun k : Fin n => sep_ibp (G₀ := ∫ x in B0579.cell c, ω t₀ x * ψ k x) ht (χ k)
    (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x)
    (fun s => ∫ x in B0579.cell c, ω s x * ψ k x) (hχ k)
    (hfl.timeIntegrable (ψ k) (hψ k) t₁ ht) (fun s hs => hweak k s hs)
  rw [intervalIntegral.integral_congr_ae (g := fun r => ∑ k, (deriv (χ k) r
      * (∫ x in B0579.cell c, ω r x * ψ k x)
      + χ k r * ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x)) ?_]
  · rw [intervalIntegral.integral_finset_sum fun k _ => (hterm k).1]
    exact Finset.sum_congr rfl fun k _ => (hterm k).2
  · have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t₁ := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with r hr hrI
    rw [uIoc_of_le ht] at hrI
    have hrI' : r ∈ Ioo t₀ t₁ := ⟨hrI.1, lt_of_le_of_ne hrI.2 hr⟩
    have hdiff : ∀ k, DifferentiableAt ℝ (χ k) r := fun k =>
      ((hχ k).differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds hrI'.1 hrI'.2)
    have I1 : ∀ k, IntegrableOn (fun x => deriv (χ k) r * (ω r x * ψ k x)) (B0579.cell c) :=
      fun k => Integrable.const_mul (sep_integrableOn_test (hfl.memX r hrI'.1.le) (hψ k)) _
    have I2 : ∀ k, IntegrableOn (fun x => χ k r * cylFreeIntegrand tr (ω r) r (ψ k) x)
        (B0579.cell c) :=
      fun k => Integrable.const_mul (hfl.integrable (ψ k) (hψ k) r hrI'.1.le) _
    rw [integral_congr_ae (ae_of_all _ fun x => sep_pointwise tr (ω r) r χ ψ hψ hdiff x),
      integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_add (I1 k) (I2 k), integral_const_mul, integral_const_mul]
    · intro k _
      exact Integrable.add (I1 k) (I2 k)

end UnforcedLeray.Short.IIb
