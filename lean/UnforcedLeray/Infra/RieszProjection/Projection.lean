import UnforcedLeray.Infra.RieszProjection.Basic

/-!
# Riesz projections, II: idempotence and the outer inverse

Let `X` be a complex Banach space, `T : X →L[ℂ] X` and `r > 0` with the circle `|z| = r` in the
resolvent set. This file proves

* `isIdempotentElem_rieszProj`: the Riesz projection `P = (2πi)⁻¹ ∮_{|z|=r} (z - T)⁻¹ dz` is
  idempotent;
* `mul_rieszOuterInv`, `rieszOuterInv_mul`: the outer inverse
  `S = -(2πi)⁻¹ ∮_{|z|=r} z⁻¹ (z - T)⁻¹ dz` satisfies `T S = S T = 1 - P`;
* `rieszOuterInv_mul_rieszProj`, `rieszProj_mul_rieszOuterInv`: `S P = P S = 0`;
* `rieszOuterInv_pow_succ`: `S ^ (m + 1) = -(2πi)⁻¹ ∮_{|z|=r} z^{-(m+1)} (z - T)⁻¹ dz`.

The proofs avoid Fubini. For `|z| = r₁ < r₂` the first resolvent identity gives
`(z - T)⁻¹ P_{r₂} = (z - T)⁻¹ - G(z)` with the Cauchy integral
`G(z) = (2πi)⁻¹ ∮_{|w|=r₂} (w - z)⁻¹ (w - T)⁻¹ dw` (`resolvent_mul_rieszProj`). `G` is holomorphic
on `|z| < r₂` (`hasFPowerSeriesOn_cauchy_integral`), so `∮_{|z|=r₁} G = 0` (Cauchy), and the
Taylor coefficients of `G` at `0` computed on the two circles agree
(`circleIntegral_inv_pow_smul_cauchyFn`, uniqueness of power series). The radius is then moved
through an annulus free of spectrum (`contourOp_eq_of_annulus`).
-/

set_option autoImplicit false

noncomputable section

open Metric Complex
open scoped Real NNReal

namespace UnforcedLeray.Infra.RieszProjection

/-! ### The Cauchy integral on a circle and its Taylor coefficients -/

section Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Cauchy integral `w ↦ (2πi)⁻¹ ∮_{|z|=R} (z - w)⁻¹ F(z) dz` over the circle `|z| = R`. -/
def cauchyFn (F : ℂ → E) (R : ℝ) (w : ℂ) : E :=
  (2 * π * I)⁻¹ • ∮ z in C(0, R), (z - w)⁻¹ • F z

/-- The Cauchy integral is holomorphic inside the circle. -/
theorem differentiableOn_cauchyFn {F : ℂ → E} {R : ℝ} (hR : 0 < R)
    (hF : CircleIntegrable F 0 R) : DifferentiableOn ℂ (cauchyFn F R) (ball 0 R) := by
  lift R to ℝ≥0 using hR.le
  have h := hasFPowerSeriesOn_cauchy_integral hF (by exact_mod_cast hR)
  have h' := h.differentiableOn
  rw [Metric.eball_coe] at h'
  exact h'

/-- `∮_{|z|=r₁} G(z) dz = 0` for the Cauchy integral `G` on a larger circle `|w| = r₂`. -/
theorem circleIntegral_cauchyFn_eq_zero {F : ℂ → E} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hF : CircleIntegrable F 0 r₂) : (∮ z in C(0, r₁), cauchyFn F r₂ z) = 0 := by
  have hd := differentiableOn_cauchyFn (h0.trans h12) hF
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable h0.le Set.countable_empty
    (hd.continuousOn.mono (closedBall_subset_ball h12)) (fun z hz => ?_)
  exact hd.differentiableAt (isOpen_ball.mem_nhds ((ball_subset_ball h12.le) hz.1))

/-- The Taylor coefficients at `0` of the Cauchy integral `G` of `F` on `|w| = r₂`, computed on a
smaller circle `|z| = r₁`, are those of `F`:
`∮_{|z|=r₁} z^{-(m+1)} G(z) dz = ∮_{|w|=r₂} w^{-(m+1)} F(w) dw`. -/
theorem circleIntegral_inv_pow_smul_cauchyFn {F : ℂ → E} {r₁ r₂ : ℝ} (h0 : 0 < r₁)
    (h12 : r₁ < r₂) (hF : CircleIntegrable F 0 r₂) (m : ℕ) :
    (∮ z in C(0, r₁), z⁻¹ ^ (m + 1) • cauchyFn F r₂ z) =
      ∮ w in C(0, r₂), w⁻¹ ^ (m + 1) • F w := by
  have hd : DifferentiableOn ℂ (cauchyFn F r₂) (closedBall 0 r₁) :=
    (differentiableOn_cauchyFn (h0.trans h12) hF).mono (closedBall_subset_ball h12)
  lift r₁ to ℝ≥0 using h0.le
  lift r₂ to ℝ≥0 using (h0.trans h12).le
  have h2 : HasFPowerSeriesOnBall (cauchyFn F r₂) (cauchyPowerSeries F 0 r₂) 0 r₂ :=
    hasFPowerSeriesOn_cauchy_integral hF (by exact_mod_cast h0.trans h12)
  have h1 := hd.hasFPowerSeriesOnBall (by exact_mod_cast h0)
  have heq := h1.hasFPowerSeriesAt.eq_formalMultilinearSeries h2.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ E => p m (fun _ => 1)) heq
  simp only [cauchyPowerSeries_apply, sub_zero, one_div] at hc
  have hc' := smul_right_injective E (inv_ne_zero two_pi_I_ne_zero) hc
  have e : ∀ (z : ℂ) (v : E), z⁻¹ ^ (m + 1) • v = z⁻¹ ^ m • z⁻¹ • v := fun z v => by
    rw [pow_succ, mul_smul]
  simp only [e]
  exact hc'

end Cauchy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-! ### Products with the Riesz projection -/

section Products

theorem ne_zero_of_mem_sphere_zero {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) :
    z ≠ 0 :=
  ne_of_mem_sphere hz hr.ne'

theorem continuousOn_inv_pow_sphere {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContinuousOn (fun z : ℂ => z⁻¹ ^ n) (sphere (0 : ℂ) r) :=
  (continuousOn_inv₀.mono (fun _ hz => ne_zero_of_mem_sphere_zero hr hz)).pow n

omit [CompleteSpace X] in
theorem contourOp_congr {T : X →L[ℂ] X} {r : ℝ} (hr : 0 ≤ r) {f g : ℂ → ℂ}
    (h : Set.EqOn f g (sphere (0 : ℂ) r)) : contourOp T r f = contourOp T r g := by
  unfold contourOp
  congr 1
  refine circleIntegral.integral_congr hr (fun z hz => ?_)
  simp only [h hz]

/-- `(z - T)⁻¹ P_{r₂} = (z - T)⁻¹ - G(z)` for `|z| < r₂`, where
`G(z) = (2πi)⁻¹ ∮_{|w|=r₂} (w - z)⁻¹ (w - T)⁻¹ dw` (first resolvent identity). -/
theorem resolvent_mul_rieszProj {T : X →L[ℂ] X} {r₂ : ℝ} (hr₂ : 0 < r₂)
    (hT₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ T) {z : ℂ} (hz : z ∈ resolventSet ℂ T)
    (hzr : ‖z‖ < r₂) :
    resolvent T z * rieszProj T r₂ = resolvent T z - cauchyFn (resolvent T) r₂ z := by
  have hcont := continuousOn_resolvent hT₂
  have hne : ∀ w ∈ sphere (0 : ℂ) r₂, w - z ≠ 0 := fun w hw => by
    refine sub_ne_zero.2 ?_
    rintro rfl
    rw [mem_sphere_zero_iff_norm] at hw
    linarith
  have hinv : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere (0 : ℂ) r₂) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hint0 : CircleIntegrable (resolvent T) 0 r₂ := hcont.circleIntegrable hr₂.le
  have hint1 : CircleIntegrable (fun w => (w - z)⁻¹ • resolvent T z) 0 r₂ :=
    (hinv.smul continuousOn_const).circleIntegrable hr₂.le
  have hint2 : CircleIntegrable (fun w => (w - z)⁻¹ • resolvent T w) 0 r₂ :=
    (hinv.smul hcont).circleIntegrable hr₂.le
  have hcongr : Set.EqOn (fun w => resolvent T z * resolvent T w)
      (fun w => (w - z)⁻¹ • resolvent T z - (w - z)⁻¹ • resolvent T w) (sphere (0 : ℂ) r₂) := by
    intro w hw
    simp only
    rw [← smul_sub, resolvent_sub_resolvent_eq hz (hT₂ hw), smul_smul,
      inv_mul_cancel₀ (hne w hw), one_smul]
  rw [rieszProj, mul_smul_comm, ← circleIntegral_mul_left _ hint0,
    circleIntegral.integral_congr hr₂.le hcongr, circleIntegral.integral_sub hint1 hint2,
    circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.2 hzr), smul_sub, smul_smul,
    inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  rfl

/-- `contourOp T r₁ f ∘ P_{r₂} = contourOp T r₁ f - (2πi)⁻¹ ∮_{|z|=r₁} f(z) G(z) dz` for
`r₁ < r₂`. -/
theorem contourOp_mul_rieszProj {T : X →L[ℂ] X} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hT₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ T) (hT₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ T)
    {f : ℂ → ℂ} (hf : ContinuousOn f (sphere (0 : ℂ) r₁)) :
    contourOp T r₁ f * rieszProj T r₂ = contourOp T r₁ f -
      (2 * π * I)⁻¹ • ∮ z in C(0, r₁), f z • cauchyFn (resolvent T) r₂ z := by
  have hr₂ : 0 < r₂ := h0.trans h12
  have hint := circleIntegrable_smul_resolvent h0.le hT₁ hf
  have hint0 : CircleIntegrable (resolvent T) 0 r₂ :=
    (continuousOn_resolvent hT₂).circleIntegrable hr₂.le
  have hG : ContinuousOn (cauchyFn (resolvent T) r₂) (sphere (0 : ℂ) r₁) :=
    (differentiableOn_cauchyFn hr₂ hint0).continuousOn.mono
      (sphere_subset_closedBall.trans (closedBall_subset_ball h12))
  have hint1 : CircleIntegrable (fun z => f z • cauchyFn (resolvent T) r₂ z) 0 r₁ :=
    (hf.smul hG).circleIntegrable h0.le
  have hcongr : Set.EqOn (fun z => (f z • resolvent T z) * rieszProj T r₂)
      (fun z => f z • resolvent T z - f z • cauchyFn (resolvent T) r₂ z) (sphere (0 : ℂ) r₁) := by
    intro z hz
    simp only
    rw [smul_mul_assoc, resolvent_mul_rieszProj hr₂ hT₂ (hT₁ hz)
      (by rw [mem_sphere_zero_iff_norm.1 hz]; exact h12), smul_sub]
  rw [contourOp, smul_mul_assoc, ← circleIntegral_mul_right _ hint,
    circleIntegral.integral_congr h0.le hcongr, circleIntegral.integral_sub hint hint1, smul_sub]

/-- `P_{r₁} P_{r₂} = P_{r₁}` for `r₁ < r₂` (both circles in the resolvent set). -/
theorem rieszProj_mul_rieszProj_of_lt {T : X →L[ℂ] X} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hT₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ T) (hT₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ T) :
    rieszProj T r₁ * rieszProj T r₂ = rieszProj T r₁ := by
  have hint0 : CircleIntegrable (resolvent T) 0 r₂ :=
    (continuousOn_resolvent hT₂).circleIntegrable (h0.trans h12).le
  have h := contourOp_mul_rieszProj h0 h12 hT₁ hT₂ (f := fun _ => 1) continuousOn_const
  rw [← rieszProj_eq_contourOp] at h
  rw [h]
  simp only [one_smul]
  rw [circleIntegral_cauchyFn_eq_zero h0 h12 hint0, smul_zero, sub_zero]

/-- `contourOp T r₁ (z^{-(m+1)}) ∘ P_{r₂} = contourOp T r₁ (z^{-(m+1)}) - contourOp T r₂ (z^{-(m+1)})`
for `r₁ < r₂`. -/
theorem contourOp_inv_pow_mul_rieszProj_of_lt {T : X →L[ℂ] X} {r₁ r₂ : ℝ} (h0 : 0 < r₁)
    (h12 : r₁ < r₂) (hT₁ : sphere (0 : ℂ) r₁ ⊆ resolventSet ℂ T)
    (hT₂ : sphere (0 : ℂ) r₂ ⊆ resolventSet ℂ T) (m : ℕ) :
    contourOp T r₁ (fun z => z⁻¹ ^ (m + 1)) * rieszProj T r₂ =
      contourOp T r₁ (fun z => z⁻¹ ^ (m + 1)) - contourOp T r₂ (fun z => z⁻¹ ^ (m + 1)) := by
  have hint0 : CircleIntegrable (resolvent T) 0 r₂ :=
    (continuousOn_resolvent hT₂).circleIntegrable (h0.trans h12).le
  rw [contourOp_mul_rieszProj h0 h12 hT₁ hT₂ (continuousOn_inv_pow_sphere h0 (m + 1)),
    circleIntegral_inv_pow_smul_cauchyFn h0 h12 hint0 m]
  rfl

end Products

/-! ### The Riesz projection at one radius -/

section OneRadius

variable {T : X →L[ℂ] X} {r : ℝ}

omit [CompleteSpace X] in
/-- Every circle of radius in `[r - δ, r + δ]` lies in the resolvent set when the closed annulus
`r - δ ≤ |z| ≤ r + δ` does. -/
theorem sphere_subset_of_annulus {δ : ℝ}
    (hann : ∀ z : ℂ, r - δ ≤ ‖z‖ → ‖z‖ ≤ r + δ → z ∈ resolventSet ℂ T) {s : ℝ}
    (h1 : r - δ ≤ s) (h2 : s ≤ r + δ) : sphere (0 : ℂ) s ⊆ resolventSet ℂ T := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  exact hann z (hz ▸ h1) (hz ▸ h2)

/-- `P_r = P_{r + δ}` when the annulus `r ≤ |z| ≤ r + δ` is free of spectrum. -/
theorem rieszProj_eq_of_annulus {δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hann : ∀ z : ℂ, r - δ ≤ ‖z‖ → ‖z‖ ≤ r + δ → z ∈ resolventSet ℂ T) :
    rieszProj T r = rieszProj T (r + δ) := by
  rw [rieszProj_eq_contourOp, rieszProj_eq_contourOp]
  exact contourOp_eq_of_annulus hr (by linarith) (fun z h1 h2 => hann z (by linarith) h2)
    (fun _ _ _ => differentiableAt_const _)

/-- **The Riesz projection is idempotent**: `P ^ 2 = P`. -/
theorem isIdempotentElem_rieszProj (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    IsIdempotentElem (rieszProj T r) := by
  obtain ⟨δ, hδ, -, hann⟩ := exists_annulus_subset_resolventSet T hr hT
  have heq := rieszProj_eq_of_annulus hr hδ.le hann
  have hT₂ := sphere_subset_of_annulus hann (s := r + δ) (by linarith) le_rfl
  unfold IsIdempotentElem
  calc rieszProj T r * rieszProj T r = rieszProj T r * rieszProj T (r + δ) := by rw [← heq]
    _ = rieszProj T r := rieszProj_mul_rieszProj_of_lt hr (by linarith) hT hT₂

theorem rieszProj_mul_self (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    rieszProj T r * rieszProj T r = rieszProj T r :=
  isIdempotentElem_rieszProj hr hT

/-- `Q = 1 - P` is idempotent. -/
theorem isIdempotentElem_one_sub_rieszProj (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) : IsIdempotentElem (1 - rieszProj T r) :=
  (isIdempotentElem_rieszProj hr hT).one_sub

/-- `P (1 - P) = 0`. -/
theorem rieszProj_mul_one_sub (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    rieszProj T r * (1 - rieszProj T r) = 0 := by
  rw [mul_sub, mul_one, rieszProj_mul_self hr hT, sub_self]

/-- `(1 - P) P = 0`. -/
theorem one_sub_mul_rieszProj (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    (1 - rieszProj T r) * rieszProj T r = 0 := by
  rw [sub_mul, one_mul, rieszProj_mul_self hr hT, sub_self]

/-- `contourOp T r (z^{-(m+1)}) ∘ P = 0`. -/
theorem contourOp_inv_pow_mul_rieszProj (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T)
    (m : ℕ) : contourOp T r (fun z => z⁻¹ ^ (m + 1)) * rieszProj T r = 0 := by
  obtain ⟨δ, hδ, -, hann⟩ := exists_annulus_subset_resolventSet T hr hT
  have heq := rieszProj_eq_of_annulus hr hδ.le hann
  have hT₂ := sphere_subset_of_annulus hann (s := r + δ) (by linarith) le_rfl
  have hmove : contourOp T r (fun z => z⁻¹ ^ (m + 1)) =
      contourOp T (r + δ) (fun z => z⁻¹ ^ (m + 1)) := by
    refine contourOp_eq_of_annulus hr (by linarith) (fun z h1 h2 => hann z (by linarith) h2)
      (fun z h1 _ => ?_)
    have hz : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      linarith
    exact (differentiableAt_inv hz).pow (m + 1)
  rw [heq, contourOp_inv_pow_mul_rieszProj_of_lt hr (by linarith) hT hT₂ m, hmove, sub_self]

/-! ### The outer inverse -/

theorem commute_rieszOuterInv {B : X →L[ℂ] X} (hB : Commute B T) (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) : Commute B (rieszOuterInv T r) :=
  (commute_contourOp hB hr.le hT (by simpa using continuousOn_inv_pow_sphere hr 1)).neg_right

/-- `T S = 1 - P`. -/
theorem mul_rieszOuterInv (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    T * rieszOuterInv T r = 1 - rieszProj T r := by
  have hf : ContinuousOn (fun z : ℂ => z⁻¹) (sphere (0 : ℂ) r) := by
    simpa using continuousOn_inv_pow_sphere hr 1
  have hcongr : contourOp T r (fun z => z * z⁻¹) = rieszProj T r := by
    rw [rieszProj_eq_contourOp]
    exact contourOp_congr hr.le (fun z hz => mul_inv_cancel₀ (ne_zero_of_mem_sphere_zero hr hz))
  rw [rieszOuterInv, mul_neg, mul_contourOp hr.le hT hf, circleIntegral_inv_eq hr,
    inv_mul_cancel₀ two_pi_I_ne_zero, one_smul, hcongr, neg_sub]

/-- `S T = 1 - P`. -/
theorem rieszOuterInv_mul (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    rieszOuterInv T r * T = 1 - rieszProj T r := by
  rw [← (commute_rieszOuterInv (Commute.refl T) hr hT).eq, mul_rieszOuterInv hr hT]

/-- `S P = 0`. -/
theorem rieszOuterInv_mul_rieszProj (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    rieszOuterInv T r * rieszProj T r = 0 := by
  have h := contourOp_inv_pow_mul_rieszProj hr hT 0
  simp only [zero_add, pow_one] at h
  rw [rieszOuterInv, neg_mul, h, neg_zero]

/-- `P S = 0`. -/
theorem rieszProj_mul_rieszOuterInv (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    rieszProj T r * rieszOuterInv T r = 0 := by
  rw [(commute_rieszOuterInv (commute_self_rieszProj hr.le hT).symm hr hT).eq,
    rieszOuterInv_mul_rieszProj hr hT]

/-- `S (1 - P) = S`. -/
theorem rieszOuterInv_mul_one_sub (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    rieszOuterInv T r * (1 - rieszProj T r) = rieszOuterInv T r := by
  rw [mul_sub, mul_one, rieszOuterInv_mul_rieszProj hr hT, sub_zero]

/-- `(1 - P) S = S`. -/
theorem one_sub_mul_rieszOuterInv (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    (1 - rieszProj T r) * rieszOuterInv T r = rieszOuterInv T r := by
  rw [sub_mul, one_mul, rieszProj_mul_rieszOuterInv hr hT, sub_zero]

/-- `T ∘ contourOp T r (z^{-(m+2)}) = contourOp T r (z^{-(m+1)})`. -/
theorem mul_contourOp_inv_pow (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) (m : ℕ) :
    T * contourOp T r (fun z => z⁻¹ ^ (m + 2)) = contourOp T r (fun z => z⁻¹ ^ (m + 1)) := by
  rw [mul_contourOp hr.le hT (continuousOn_inv_pow_sphere hr (m + 2)),
    circleIntegral_inv_pow_eq_zero, mul_zero, zero_smul, sub_zero]
  refine contourOp_congr hr.le (fun z hz => ?_)
  have hz0 := ne_zero_of_mem_sphere_zero hr hz
  show z * z⁻¹ ^ (m + 2) = z⁻¹ ^ (m + 1)
  rw [pow_succ, ← mul_assoc, mul_comm z, mul_assoc, mul_inv_cancel₀ hz0, mul_one]

/-- **Powers of the outer inverse**: `S ^ (m + 1) = -(2πi)⁻¹ ∮_{|z|=r} z^{-(m+1)} (z - T)⁻¹ dz`. -/
theorem rieszOuterInv_pow_succ (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) (m : ℕ) :
    rieszOuterInv T r ^ (m + 1) = -contourOp T r (fun z => z⁻¹ ^ (m + 1)) := by
  induction m with
  | zero =>
    rw [Nat.zero_add, pow_one]
    simp only [rieszOuterInv, pow_one]
  | succ m ih =>
    have hPC : Commute (rieszProj T r) (contourOp T r (fun z => z⁻¹ ^ (m + 2))) :=
      commute_contourOp (commute_self_rieszProj hr.le hT).symm hr.le hT
        (continuousOn_inv_pow_sphere hr (m + 2))
    rw [pow_succ', ih, ← mul_contourOp_inv_pow hr hT m, mul_neg, ← mul_assoc,
      rieszOuterInv_mul hr hT, sub_mul, one_mul, hPC.eq,
      contourOp_inv_pow_mul_rieszProj hr hT (m + 1), sub_zero]

end OneRadius

end UnforcedLeray.Infra.RieszProjection
