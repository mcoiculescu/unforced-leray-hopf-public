import UnforcedLeray.Short.PartIIIa.Targets
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound

/-!
# Part III-a, task `PartIII-a:T15`: the kernel bounds `sep:kernel` (conditional)

Target (`SeparatedKernels.lean`): `SepKernelBounds` (SP 3604-3610): for each `j` there is `C_j`
with, for `x ≠ 0` and all `i, k`,
`|D^{j+1}(K_t)_{ik}(x)| ≤ C_j |x|^{-4-j}` (all `t > 0`, and `K_0`), and
`|D^j(K_t - K_0)_{ik}(x)| ≤ C_j t |x|^{-5-j}`, where `(K_t)_{ik} = δ_{ik}G_t + ∂_i∂_k H_t`,
`H_t = ∫_t^∞ G_a da` (`heatTail t`) and `K_0 = D²(4π|x|)^{-1}`.

## Mathematical proof (SP 3604-3610)

Write `r = |x|`, `H_t = heatTail t` (also for `t = 0`: `H_0(x) = ∫_0^∞ G_a(x) da = (4π|x|)^{-1}`
for `x ≠ 0`, `HeatTailZero`).

1. (*Differentiation under the integral.*) For `t ≥ 0` and `x ≠ 0`, `H_t` is `C^∞` at `x` and
   `D^m H_t(x) = ∫_t^∞ D^m G_a(x) da` (`HeatTailStep`, `HeatTailIterated`): the integrand and its
   `x`-derivative are dominated, on the ball `B(x, r/2)`, by `C a^{-(3+m)/2} e^{-r²/(32a)}`
   (`HeatGBound`, T14), integrable on `(0, ∞)`.
2. (*Decay.*) `|D^m H_t(x)| ≤ ∫_0^∞ C a^{-(3+m)/2} e^{-r²/(8a)} da = C' r^{-1-m}`
   (`GaussInvIntegral`, T04, with `s = (3+m)/2`; `HeatTailBound`). With `m = j+3`, this bounds the
   `∂_i∂_k H_t` part of `D^{j+1}K_t` and of `D^{j+1}K_0` by `r^{-4-j}`.
3. (*The `G_t` part.*) `|D^m G_t(x)| ≤ C t^{-(3+m)/2}e^{-r²/(8t)} ≤ C' r^{-3-m}`, and
   `≤ C' t r^{-5-m}` (`HeatGDecay` from T14 and `GaussSup`, `sup_{u>0} u^s e^{-u/8} < ∞`).
4. (*The difference.*) `H_t - H_0 = -∫_0^t G_a da` off the origin, so
   `|D^m(H_t - H_0)(x)| ≤ ∫_0^t C a^{-(3+m)/2}e^{-r²/(8a)} da ≤ C' t r^{-3-m}`
   (`HeatTailDiffBound`); with `m = j+2` this is the `t r^{-5-j}` bound of `D^j(K_t - K_0)`.
5. (*Bookkeeping.*) `D^n ∂_i∂_k f` is bounded by `D^{n+2} f` and `∂_i∂_k` is linear and local
   (`Part2Calculus`, `Part2Congr`); `K_0 = ∂_i∂_k H_0` near `x ≠ 0` by `HeatTailZero`.

Proved here, from the Props below: `sepKernelBounds_of` (steps 2-5 assembled, with the choice of
constants). The unconditional leaves are queued as tasks `PartIII-a:T15/1 ... T15/9`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The leaf statements -/

/-- **Elementary Gaussian supremum** (`PartIII-a:T15/1`; SP 3604-3606, "`a^{-s}e^{-r²/(8a)} ≤
C r^{-2s}`"): for `s ≥ 0` there is `C ≥ 0` with
`a^{-s} e^{-r²/(8a)} ≤ C r^{-2s}` for all `a, r > 0`. Substitute `u = r²/(8a)`:
`a^{-s} = (8u)^s r^{-2s}` and `sup_{u>0} u^s e^{-u} < ∞` (e.g. `u^s e^{-u} ≤ (s/e)^s`, or
`Real.rpow_le...`/`one_add_pow_mul_exp_le`-type bounds). -/
def GaussSup : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ a r : ℝ, 0 < a → 0 < r →
    a ^ (-s) * Real.exp (-r ^ 2 / (8 * a)) ≤ C * r ^ (-2 * s)

/-- **Decay of the heat kernel and its derivatives** (`PartIII-a:T15/2`; SP 3604-3610): for each `m`
there is `C ≥ 0` with, for `t > 0` and `x ≠ 0`, `‖D^m G_t(x)‖ ≤ C ‖x‖^{-3-m}` and
`‖D^m G_t(x)‖ ≤ C t ‖x‖^{-5-m}`. From `HeatGBound` (T14) and `GaussSup`:
`t^{-(3+m)/2}e^{-r²/(8t)} ≤ C_s r^{-(3+m)}` (`s = (3+m)/2`) and
`t^{-(3+m)/2} = t · t^{-(5+m)/2}` with `s = (5+m)/2`. -/
def HeatGDecay : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ m (heatG t) x‖ ≤ C * ‖x‖ ^ (-3 - (m : ℝ)) ∧
    ‖iteratedFDeriv ℝ m (heatG t) x‖ ≤ C * t * ‖x‖ ^ (-5 - (m : ℝ))

/-- **One step of differentiation under the integral** (`PartIII-a:T15/3`; SP 3604-3606): for
`t ≥ 0`, `m : ℕ` and `x ≠ 0`, `y ↦ ∫_t^∞ D^m G_a(y) da` (a function into the space of continuous
`m`-linear maps) is Fréchet differentiable at `x` with derivative `∫_t^∞ D(D^m G_a)(x) da`.
Proof: `hasFDerivAt_integral_of_dominated_of_fderiv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean`) on the ball `B(x, ‖x‖/2)` with bound
`C_{m+1} a^{-(4+m)/2} e^{-‖x‖²/(32a)}` (`HeatGBound` T14 for `m+1`, norm of
`fderiv (iteratedFDeriv m f) = ‖iteratedFDeriv (m+1) f‖`, `norm_fderiv_iteratedFDeriv`), which is
integrable on `(0,∞)` (`GaussInvIntegral` T04, or `gInv_finite`); the integrand is measurable in
`a` by `Kernels.continuousOn_iteratedFDeriv_heatKernel`
(`Lib/Kernels/GaussDeriv.lean`) and `heatG_eq_heatKernel` (T14). -/
def HeatTailStep : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ (m : ℕ) (x : Space), x ≠ 0 →
    HasFDerivAt (fun y => ∫ a in Ioi t, iteratedFDeriv ℝ m (heatG a) y)
      (∫ a in Ioi t, fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) x) x

/-- **Derivatives of the heat tail** (`PartIII-a:T15/4`; SP 3604-3606): for `t ≥ 0` and `x ≠ 0`,
`heatTail t` is `C^∞` at `x` and `D^m(heatTail t)(x) = ∫_t^∞ D^m G_a(x) da` for every `m`.
Proof from `HeatTailStep`: induction on `m` on the open set `{y ≠ 0}` using
`iteratedFDeriv_succ_eq_comp_left` and `Filter.EventuallyEq.fderiv_eq`; commute the continuous
linear (curry) equivalence with the Bochner integral (`ContinuousLinearMap.integral_comp_comm`,
integrability from `HeatGBound` + `GaussInvIntegral`); smoothness from
`contDiffOn_of_differentiableOn` on the open set `{y ≠ 0}`. -/
def HeatTailIterated : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ≠ 0 →
    ContDiffAt ℝ ∞ (heatTail t) x ∧
    ∀ m : ℕ, iteratedFDeriv ℝ m (heatTail t) x = ∫ a in Ioi t, iteratedFDeriv ℝ m (heatG a) x

/-- **Decay of the heat tail** (`PartIII-a:T15/5`; SP 3604-3606): for each `m` there is `C ≥ 0` with
`‖D^m(heatTail t)(x)‖ ≤ C ‖x‖^{-1-m}` for all `t ≥ 0`, `x ≠ 0`. From `HeatTailIterated`,
`‖∫‖ ≤ ∫ ‖·‖ ≤ ∫_0^∞ C a^{-(3+m)/2}e^{-‖x‖²/(8a)} da` (`HeatGBound` T14) and
`GaussInvIntegral` (T04) with `s = (3+m)/2`, `r = ‖x‖`: `r^{2-2s} = r^{-1-m}`. -/
def HeatTailBound : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ m (heatTail t) x‖ ≤ C * ‖x‖ ^ (-1 - (m : ℝ))

/-- **The difference `heatTail t - heatTail 0`** (`PartIII-a:T15/6`; SP 3608, "`K_t - K_0 =
-∫_0^t ΔK_a da`"): for each `m` there is `C ≥ 0` with
`‖D^m(heatTail t - heatTail 0)(x)‖ ≤ C t ‖x‖^{-3-m}` for `t > 0`, `x ≠ 0`. From `HeatTailIterated`
at `t` and `0` (`iteratedFDeriv_sub_apply`), `∫_{(t,∞)} - ∫_{(0,∞)} = -∫_{(0,t]}` (additivity of
the integral over `Ioi 0 = Ioc 0 t ∪ Ioi t`, integrability from `HeatGBound` + `GaussInvIntegral`),
`‖D^mG_a(x)‖ ≤ C a^{-(3+m)/2}e^{-‖x‖²/(8a)} ≤ C' ‖x‖^{-3-m}` (`GaussSup`, `s = (3+m)/2`). -/
def HeatTailDiffBound : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ m (fun y => heatTail t y - heatTail 0 y) x‖ ≤ C * t * ‖x‖ ^ (-3 - (m : ℝ))

/-- **The Newtonian potential as a heat integral** (`PartIII-a:T15/7`; SP 3604-3606):
`∫_0^∞ G_a(x) da = (4π‖x‖)⁻¹` for `x ≠ 0`. Substitution `u = ‖x‖²/(4a)`:
`∫_0^∞ (4πa)^{-3/2}e^{-r²/(4a)} da = (4π r)^{-1} Γ(1/2)/√π = (4π r)⁻¹`
(`Real.Gamma_one_half_eq`, `Real.integral_rpow_mul_exp_neg_mul_rpow` or
`Real.Gamma_eq_integral`, `integral_comp_inv_Ioi`-type change of variables). -/
def HeatTailZero : Prop :=
  ∀ x : Space, x ≠ 0 → heatTail 0 x = (4 * Real.pi * ‖x‖)⁻¹

/-- **Second partials: calculus** (`PartIII-a:T15/8`): for `f, g` that are `C^∞` at `x`,
(a) `part2 f i k` is `C^∞` at `x`; (b) `‖D^n(part2 f i k)(x)‖ ≤ ‖D^{n+2}f(x)‖` (the coordinate
vectors have norm `1`; `part2 f i k = (evaluation at the coordinate vectors) ∘ fderiv (fderiv f)`
near `x`, `norm_iteratedFDeriv_fderiv`, `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`);
(c) `part2 (f - g) i k = part2 f i k - part2 g i k` near `x`. -/
def Part2Calculus : Prop :=
  ∀ (f g : Space → ℝ) (x : Space), ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x → ∀ i k : Fin 3,
    ContDiffAt ℝ ∞ (part2 f i k) x ∧
    (∀ n : ℕ, ‖iteratedFDeriv ℝ n (part2 f i k) x‖ ≤ ‖iteratedFDeriv ℝ (n + 2) f x‖) ∧
    (part2 (fun y => f y - g y) i k =ᶠ[𝓝 x] fun y => part2 f i k y - part2 g i k y)

/-- **Second partials are local** (`PartIII-a:T15/9`): if `f = g` near `x`, then
`part2 f i k = part2 g i k` near `x` (`Filter.EventuallyEq.fderiv_eq` twice; no smoothness). -/
def Part2Congr : Prop :=
  ∀ (f g : Space → ℝ) (x : Space), f =ᶠ[𝓝 x] g → ∀ i k : Fin 3,
    part2 f i k =ᶠ[𝓝 x] part2 g i k

/-! ## The assembly -/

/-- The `δ_{ik}G_t` part of `K_t`: its iterated derivative is bounded by that of `G_t`. -/
theorem norm_iteratedFDeriv_delta_le (t : ℝ) (i k : Fin 3) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => if i = k then heatG t y else 0) x‖ ≤
      ‖iteratedFDeriv ℝ n (heatG t) x‖ := by
  by_cases h : i = k
  · simp [h]
  · simp [h]

/-- The `δ_{ik}G_t` part is `C^∞`. -/
theorem contDiffAt_delta (t : ℝ) (i k : Fin 3) (x : Space) :
    ContDiffAt ℝ ∞ (fun y => if i = k then heatG t y else 0) x := by
  by_cases h : i = k
  · simp only [h, ite_true]
    rw [heatG_eq_heatKernel]
    exact (UnforcedLeray.Kernels.heatKernel_smooth t).contDiffAt
  · simp only [h, ite_false]
    exact contDiffAt_const

theorem contDiffAt_nat {f : Space → ℝ} {x : Space} (h : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ContDiffAt ℝ (n : WithTop ℕ∞) f x :=
  h.of_le (by exact_mod_cast le_top)

/-- **`sep:kernel`, assembled** (SP 3604-3610): the seven analytic leaves give `SepKernelBounds`
with `C_j = C_{G,j+1} + C_{B,j+3} + C_{G,j} + C_{D,j+2}`. -/
theorem sepKernelBounds_of (hG : HeatGDecay) (hIt : HeatTailIterated) (hB : HeatTailBound)
    (hD : HeatTailDiffBound) (hN : HeatTailZero) (hP : Part2Calculus) (hC : Part2Congr) :
    SepKernelBounds := by
  intro j
  obtain ⟨CG1, hCG1, hG1⟩ := hG (j + 1)
  obtain ⟨CG0, hCG0, hG0⟩ := hG j
  obtain ⟨CB, hCB, hBd⟩ := hB (j + 3)
  obtain ⟨CD, hCD, hDd⟩ := hD (j + 2)
  refine ⟨CG1 + CB + CG0 + CD, fun x hx i k => ?_⟩
  have hr4 : 0 ≤ ‖x‖ ^ (-4 - (j : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hr5 : 0 ≤ ‖x‖ ^ (-5 - (j : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have e31 : (-3 - ((j + 1 : ℕ) : ℝ)) = -4 - (j : ℝ) := by push_cast; ring
  have e13 : (-1 - ((j + 3 : ℕ) : ℝ)) = -4 - (j : ℝ) := by push_cast; ring
  have e32 : (-3 - ((j + 2 : ℕ) : ℝ)) = -5 - (j : ℝ) := by push_cast; ring
  have hfg : (fun y : Space => (4 * Real.pi * ‖y‖)⁻¹) =ᶠ[𝓝 x] heatTail 0 := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact (hN y hy).symm
  have h0 := hC _ _ x hfg i k
  have hH0 : ContDiffAt ℝ ∞ (heatTail 0) x := (hIt 0 le_rfl x hx).1
  refine ⟨?_, ?_, ?_⟩
  · -- `D^{j+1} K_t`
    intro t ht
    have hH : ContDiffAt ℝ ∞ (heatTail t) x := (hIt t ht.le x hx).1
    have h2 := hP (heatTail t) (heatTail t) x hH hH i k
    have hsum : (fun y => heatLerayK t i k y) =
        (fun y => if i = k then heatG t y else 0) + part2 (heatTail t) i k := rfl
    rw [hsum, iteratedFDeriv_add_apply (contDiffAt_nat (contDiffAt_delta t i k x) _)
      (contDiffAt_nat h2.1 _)]
    have hb1 := (hG1 t ht x hx).1
    have hb2 := hBd t ht.le x hx
    have hc := h2.2.1 (j + 1)
    have hd := norm_iteratedFDeriv_delta_le t i k (j + 1) x
    rw [e31] at hb1
    rw [show j + 1 + 2 = j + 3 from rfl] at hc
    rw [e13] at hb2
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (fun y => if i = k then heatG t y else 0) x‖ +
          ‖iteratedFDeriv ℝ (j + 1) (part2 (heatTail t) i k) x‖ := norm_add_le _ _
      _ ≤ CG1 * ‖x‖ ^ (-4 - (j : ℝ)) + CB * ‖x‖ ^ (-4 - (j : ℝ)) :=
          add_le_add (hd.trans hb1) (hc.trans hb2)
      _ ≤ _ := by nlinarith [mul_nonneg hCG0 hr4, mul_nonneg hCD hr4]
  · -- `D^{j+1} K_0`
    have h2 := hP (heatTail 0) (heatTail 0) x hH0 hH0 i k
    have hev : (fun y => heatLerayK0 i k y) =ᶠ[𝓝 x] part2 (heatTail 0) i k := h0
    rw [(hev.iteratedFDeriv ℝ (j + 1)).eq_of_nhds]
    have hc := h2.2.1 (j + 1)
    have hb2 := hBd 0 le_rfl x hx
    rw [show j + 1 + 2 = j + 3 from rfl] at hc
    rw [e13] at hb2
    calc _ ≤ CB * ‖x‖ ^ (-4 - (j : ℝ)) := hc.trans hb2
      _ ≤ _ := by nlinarith [mul_nonneg hCG1 hr4, mul_nonneg hCG0 hr4, mul_nonneg hCD hr4]
  · -- `D^j (K_t - K_0)`
    intro t ht
    have hH : ContDiffAt ℝ ∞ (heatTail t) x := (hIt t ht.le x hx).1
    have h2 := hP (heatTail t) (heatTail 0) x hH hH0 i k
    have h3 := hP (fun y => heatTail t y - heatTail 0 y) (heatTail 0) x (hH.sub hH0) hH0 i k
    have hev : (fun y => heatLerayK t i k y - heatLerayK0 i k y) =ᶠ[𝓝 x]
        (fun y => if i = k then heatG t y else 0) +
          part2 (fun y => heatTail t y - heatTail 0 y) i k := by
      filter_upwards [h0, h2.2.2] with y hy1 hy2
      show (if i = k then heatG t y else 0) + part2 (heatTail t) i k y -
          part2 (fun y => (4 * Real.pi * ‖y‖)⁻¹) i k y =
        (if i = k then heatG t y else 0) + part2 (fun y => heatTail t y - heatTail 0 y) i k y
      rw [hy2, hy1]
      ring
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds,
      iteratedFDeriv_add_apply (contDiffAt_nat (contDiffAt_delta t i k x) _)
        (contDiffAt_nat h3.1 _)]
    have hb1 := (hG0 t ht x hx).2
    have hb2 := hDd t ht x hx
    have hc := h3.2.1 j
    have hd := norm_iteratedFDeriv_delta_le t i k j x
    rw [e32] at hb2
    calc _ ≤ ‖iteratedFDeriv ℝ j (fun y => if i = k then heatG t y else 0) x‖ +
          ‖iteratedFDeriv ℝ j (part2 (fun y => heatTail t y - heatTail 0 y) i k) x‖ :=
          norm_add_le _ _
      _ ≤ CG0 * t * ‖x‖ ^ (-5 - (j : ℝ)) + CD * t * ‖x‖ ^ (-5 - (j : ℝ)) :=
          add_le_add (hd.trans hb1) (hc.trans hb2)
      _ ≤ _ := by
          have := mul_nonneg (mul_nonneg hCG1 ht.le) hr5
          have := mul_nonneg (mul_nonneg hCB ht.le) hr5
          nlinarith [mul_nonneg (mul_nonneg hCG1 ht.le) hr5, mul_nonneg (mul_nonneg hCB ht.le) hr5]

end UnforcedLeray.Short.IIIa
