import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Units.B0140
import UnforcedLeray.Units.B0190

/-!
# Part II-a, task `PartII-a:R09`: the raw inlet is discretely self-similar and nonzero

Source of record: `the November 2 reference manuscript`, lines 1226-1229 (the
raw inlet statement) and 1334-1336 (the `t = 0` stream formula; the datum is nonzero on the
central ring core).

Target: `ringInlet_dss_nonzero`, the two conjuncts of `RingInlet` (in `StatementsRing.lean`)
for a fixed `c > 0`, `R ≥ 2`:

* discrete self-similarity of `inletRaw` under the dilation `x ↦ e^{c/R} x`, with factor
  `(e^{c/R})⁻¹`, at points off the axis;
* existence of a point where `inletRaw c R x ≠ 0`.

Proof outline.

1. `trainDatum c q η = B0140.trainStream c (q, η)` (the Gaussian sum of `StatementsRing.lean`
   is the `tsum` of `B0140`), so the `c`-periodicity in `q` is `B0140.trainStream_periodic`.
2. `inletStream` satisfies `inletStream (λ r) (λ z) = λ inletStream r z` for `λ = e^{c/R}`:
   the `q`-argument shifts by `R log λ = c` and the `η`-argument is invariant.
3. Derivatives transfer through such a scaling identity (`deriv_scale_eq`), giving
   `inletRaw (λ x) = λ⁻¹ • inletRaw x`.
4. At `x = (R, 0, 0)` the `e_z` component of `inletRaw` is `R⁻¹ ∂_r 𝒫(R, 0)`, which equals
   `R⁻¹ trainStream c (0, 0)` because `∂_q trainStream c (0, 0) = 0` (the velocity vanishes at
   the origin by `trainVelocity_neg`), and `trainStream c (0,0) < 0` (all terms are negative).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- The Gaussian datum of `StatementsRing.lean` is the `B0140` train stream. -/
theorem trainDatum_eq_trainStream (c q η : ℝ) :
    trainDatum c q η = UnforcedLeray.B0140.trainStream c (q, η) := by
  simp only [trainDatum, UnforcedLeray.B0140.trainStream_apply, tsum_mul_left, neg_div]

/-- The datum is `c`-periodic in `q` (source line 1334-1336 uses this for the scaling). -/
theorem trainDatum_add_period (c q η : ℝ) :
    trainDatum c (q + c) η = trainDatum c q η := by
  rw [trainDatum_eq_trainStream, trainDatum_eq_trainStream]
  exact UnforcedLeray.B0140.trainStream_periodic c (q, η)

/-- The discrete scaling of the `t = 0` stream: `𝒫(λr, λz) = λ 𝒫(r, z)` for `λ = e^{c/R}`. -/
theorem inletStream_dilate {c R : ℝ} (hR : R ≠ 0) (r z : ℝ) :
    inletStream c R (Real.exp (c / R) * r) (Real.exp (c / R) * z) =
      Real.exp (c / R) * inletStream c R r z := by
  by_cases hr : r = 0
  · subst hr
    simp [inletStream]
  · have hl : Real.exp (c / R) ≠ 0 := (Real.exp_pos _).ne'
    have hq : R * Real.log (Real.exp (c / R) * r / R) = c + R * Real.log (r / R) := by
      rw [show Real.exp (c / R) * r / R = Real.exp (c / R) * (r / R) by ring,
        Real.log_mul hl (div_ne_zero hr hR), Real.log_exp, mul_add]
      congr 1
      field_simp
    have he : R * (Real.exp (c / R) * z) / (Real.exp (c / R) * r) = R * z / r := by
      rw [show R * (Real.exp (c / R) * z) = Real.exp (c / R) * (R * z) by ring,
        mul_div_mul_left _ _ hl]
    unfold inletStream
    rw [hq, he, add_comm c, trainDatum_add_period]
    ring

/-- Transfer of derivatives through a scaling identity `f (l w) = l g w`. -/
theorem deriv_scale_eq {l : ℝ} (hl : l ≠ 0) (f g : ℝ → ℝ)
    (h : ∀ w, f (l * w) = l * g w) (w : ℝ) :
    deriv f (l * w) = deriv g w := by
  have hf : f = fun v => l * g (l⁻¹ * v) := by
    funext v
    have := h (l⁻¹ * v)
    rwa [mul_inv_cancel_left₀ hl] at this
  have hg : deriv (fun v => g (l⁻¹ * v)) (l * w) = l⁻¹ * deriv g w := by
    have := deriv_comp_mul_left l⁻¹ g (l * w)
    rw [smul_eq_mul, inv_mul_cancel_left₀ hl] at this
    exact this
  rw [hf, deriv_const_mul_field, hg, ← mul_assoc, mul_inv_cancel₀ hl, one_mul]

/-- Discrete self-similarity of the raw inlet: `inletRaw (λ x) = λ⁻¹ inletRaw x`
for `λ = e^{c/R}`, `R ≠ 0`. -/
theorem inletRaw_dilate {c R : ℝ} (hR : R ≠ 0) (x : Space) :
    inletRaw c R (Real.exp (c / R) • x) = (Real.exp (c / R))⁻¹ • inletRaw c R x := by
  have hl : 0 < Real.exp (c / R) := Real.exp_pos _
  have hl0 : Real.exp (c / R) ≠ 0 := hl.ne'
  unfold inletRaw
  rw [UnforcedLeray.B0190.ϱ_dilate hl x, UnforcedLeray.B0190.apply_two_dilate,
    Axi.eR_smul hl x]
  have D1 : deriv (fun z => inletStream c R (Real.exp (c / R) * Axi.ϱ x) z)
        (Real.exp (c / R) * x 2) =
      deriv (fun z => inletStream c R (Axi.ϱ x) z) (x 2) :=
    deriv_scale_eq hl0 _ _ (fun w => inletStream_dilate hR (Axi.ϱ x) w) (x 2)
  have D2 : deriv (fun r => inletStream c R r (Real.exp (c / R) * x 2))
        (Real.exp (c / R) * Axi.ϱ x) =
      deriv (fun r => inletStream c R r (x 2)) (Axi.ϱ x) :=
    deriv_scale_eq hl0 _ _ (fun w => inletStream_dilate hR w (x 2)) (Axi.ϱ x)
  rw [D1, D2]
  module

/-- The raw inlet is nonzero somewhere: at `x = (R, 0, 0)` its `e_z` component is
`R⁻¹ trainStream c (0,0) ≠ 0`. -/
theorem inletRaw_exists_ne {c R : ℝ} (hc : c ≠ 0) (hR : 2 ≤ R) :
    ∃ x : Space, inletRaw c R x ≠ 0 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hR0 : R ≠ 0 := hRpos.ne'
  -- the datum `trainStream c (0,0)` is strictly negative
  have hsf : ∀ w : ℝ × ℝ, UnforcedLeray.GaussianVortex.streamfunction w ≤ 0 := by
    intro w
    obtain ⟨q, η⟩ := w
    rw [UnforcedLeray.B0140.streamfunction_apply]
    have := Real.exp_pos (-(q ^ 2 + η ^ 2) / 4)
    linarith
  have hlt : UnforcedLeray.B0140.trainStream c (0, 0) < 0 := by
    refine hasSum_lt (f := fun n : ℤ => UnforcedLeray.GaussianVortex.streamfunction
        ((0, 0).1 - n * c, (0, 0).2)) (g := fun _ : ℤ => (0 : ℝ)) (i := 0)
      (fun n => hsf _) ?_ (UnforcedLeray.B0140.hasSum_trainStream hc (0, 0)) hasSum_zero
    norm_num [UnforcedLeray.B0140.streamfunction_apply]
  have hpos : UnforcedLeray.B0140.trainStream c (0, 0) ≠ 0 := hlt.ne
  -- the stream restricted to the line `η = 0`
  have hfun : (fun r : ℝ => inletStream c R r 0) =
      fun r => r * UnforcedLeray.B0140.trainStream c (R * Real.log (r / R), 0) := by
    funext r
    simp only [inletStream, mul_zero, zero_div]
    rw [trainDatum_eq_trainStream]
  -- `r ↦ R log (r/R)` has derivative `1` at `r = R`
  have hlogR : HasDerivAt (fun r : ℝ => R * Real.log (r / R)) 1 R := by
    have h1 : HasDerivAt (fun r : ℝ => r / R) (1 / R) R := (hasDerivAt_id R).div_const R
    have h2 : HasDerivAt (fun r : ℝ => Real.log (r / R)) ((1 / R) / (R / R)) R :=
      h1.log (by simp [hR0])
    have h3 := h2.const_mul R
    have e : R * ((1 / R) / (R / R)) = 1 := by
      rw [div_self hR0, div_one]
      field_simp
    rw [e] at h3
    exact h3
  -- the `q`-derivative of the datum vanishes at the origin (odd velocity)
  have hv2 : (UnforcedLeray.B0140.trainVelocity c 0).2 = 0 := by
    have h := UnforcedLeray.B0140.trainVelocity_neg c 0
    rw [neg_zero] at h
    have h' := congrArg Prod.snd h
    simp only [Prod.snd_neg] at h'
    linarith
  have hg0 : HasDerivAt (fun t : ℝ => UnforcedLeray.B0140.trainStream c (t, 0))
      (UnforcedLeray.B0140.trainVelocity c 0).2 0 :=
    UnforcedLeray.B0140.hasDerivAt_trainStream_q hc (0, 0)
  have hval : R * Real.log (R / R) = 0 := by simp [div_self hR0]
  have hg : HasDerivAt (fun t : ℝ => UnforcedLeray.B0140.trainStream c (t, 0))
      (UnforcedLeray.B0140.trainVelocity c 0).2 (R * Real.log (R / R)) := by
    rw [hval]
    exact hg0
  have hcomp := hg.comp R hlogR
  have hprod := (hasDerivAt_id' R).mul hcomp
  have hD2 : deriv (fun r => inletStream c R r 0) R = UnforcedLeray.B0140.trainStream c (0, 0) := by
    rw [hfun]
    refine (hprod.congr_deriv ?_).deriv
    simp only [Function.comp_apply]
    rw [hval, hv2]
    ring
  -- the point `x = (R, 0, 0)`
  set x : Space := !₂[R, 0, 0] with hx
  have hx2 : x 2 = 0 := by simp [hx]
  have hϱ : Axi.ϱ x = R := by
    unfold Axi.ϱ
    have hx0 : x 0 = R := by simp [hx]
    have hx1 : x 1 = 0 := by simp [hx]
    rw [hx0, hx1]
    simp [Real.sqrt_sq hRpos.le]
  refine ⟨x, ?_⟩
  intro h
  have hcoord : inletRaw c R x 2 = (1 / R) * UnforcedLeray.B0140.trainStream c (0, 0) := by
    unfold inletRaw
    rw [hϱ, hx2, hD2]
    simp [Axi.eR, Axi.hor, Axi.e3, hϱ]
  exact mul_ne_zero (one_div_ne_zero hR0) hpos (by rw [← hcoord, h]; simp)

/-- **Task `PartII-a:R09`.** For `c > 0` and `R ≥ 2`, the raw inlet `inletRaw c R` is discretely
self-similar with ratio `e^{c/R}` (factor `(e^{c/R})⁻¹`, at points off the axis), and is nonzero
at some point. This is the statement `ringInlet_dss_nonzero`; it is the second and third
conjuncts of `RingInlet` in `StatementsRing.lean`. -/
theorem ringInlet_dss_nonzero (c R : ℝ) (hc : 0 < c) (hR : 2 ≤ R) :
    (∀ x : Space, Axi.ϱ x ≠ 0 →
      inletRaw c R (Real.exp (c / R) • x) = (Real.exp (c / R))⁻¹ • inletRaw c R x) ∧
    (∃ x : Space, inletRaw c R x ≠ 0) :=
  ⟨fun x _ => inletRaw_dilate (by linarith : (0 : ℝ) < R).ne' x,
    inletRaw_exists_ne hc.ne' hR⟩

end UnforcedLeray.Short.PartIIa
