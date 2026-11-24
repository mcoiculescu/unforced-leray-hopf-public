import UnforcedLeray.Lib.HeatR3.Smooth
import UnforcedLeray.Lib.Gaussian.LpNorm

/-!
# Weighted heat bounds and the scale-invariant class `|D^j u| ≤ C|x|^{-1-j}` (INF04 T9, part)


bypass BP3 (Peetre's inequality). Covers the weighted heat steps of units B0306, B0698, B0710
(tex 275–278), B0722 (tex 468–491), B0572 and B0300.

Main results:
* `peetre_sharp`, `peetre`: `(1 + |x|)^β ≤ (1 + |x - y|)^{|β|}(1 + |y|)^β`, and the scoping note's
  form with the extra (harmless) factor `2^{|β|}`;
* `integrable_kernel_mul_weight`, `integral_kernel_mul_weight_le`: Gaussian moments
  `∫ G_θ(y)(1 + |y|)^b dy ≤ momentConst b Θ` uniformly for `0 < θ ≤ Θ`;
* `norm_average_le_weight`: `|f(y)| ≤ M(1 + |y|)^β` gives
  `|e^{θΔ}f(x)| ≤ momentConst |β| Θ · M (1 + |x|)^β` for `0 < θ ≤ Θ` (every real `β`);
* `InvDistClass`, `InvDistClass.dilate` (the class is invariant under `u ↦ λu(λ·)` with the
  same constant), `InvDistClass.heatAdmissible`.

* `heat_vanishing_tail`: if `d = 0` on `B(0, 2ε)`, every derivative of `e^{tΔ}d` is `O(t^N)` on
  `B̄(0, ε)` for `t ∈ (0, 1]` (B1028).

Not proved here (see the status report): `InvDistClass.heat_decay`, `heat_sub_self_decay` (2.48).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Gaussian (Euc gaussKernel)

section Peetre

variable {F : Type*} [SeminormedAddCommGroup F]

/-- **Peetre's inequality**, sharp form for the weight `1 + |x|`:
`(1 + |x|)^β ≤ (1 + |x - y|)^{|β|} (1 + |y|)^β` for every real `β`. -/
theorem peetre_sharp (β : ℝ) (x y : F) :
    (1 + ‖x‖) ^ β ≤ (1 + ‖x - y‖) ^ |β| * (1 + ‖y‖) ^ β := by
  rcases le_total 0 β with hβ | hβ
  · rw [abs_of_nonneg hβ, ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hβ
    have h := one_add_norm_le_mul y x
    rw [norm_sub_rev] at h
    linarith [h, mul_comm (1 + ‖y‖) (1 + ‖x - y‖)]
  · rw [abs_of_nonpos hβ]
    have h := one_add_norm_sub_rpow_neg_le (m := -β) (by linarith) (x - y) (-y)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, neg_neg] at h
    exact h

/-- **INF04 T9 `peetre`** in the scoping note's form (INF22 A2 is `Conv.peetre` for the weight
`(1 + |x|²)^{1/2}`). -/
theorem peetre (β : ℝ) (x y : F) :
    (1 + ‖x‖) ^ β ≤ 2 ^ |β| * (1 + ‖x - y‖) ^ |β| * (1 + ‖y‖) ^ β := by
  have h2 : 1 ≤ (2 : ℝ) ^ |β| := Real.one_le_rpow (by norm_num) (abs_nonneg β)
  calc (1 + ‖x‖) ^ β ≤ (1 + ‖x - y‖) ^ |β| * (1 + ‖y‖) ^ β := peetre_sharp β x y
    _ ≤ 2 ^ |β| * ((1 + ‖x - y‖) ^ |β| * (1 + ‖y‖) ^ β) :=
        le_mul_of_one_le_left (by positivity) h2
    _ = 2 ^ |β| * (1 + ‖x - y‖) ^ |β| * (1 + ‖y‖) ^ β := by ring

end Peetre

/-! ### Gaussian moments -/

theorem integrable_kernel_mul_weight {θ : ℝ} (hθ : 0 < θ) {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun y : Space => kernel θ y * (1 + ‖y‖) ^ b) := by
  obtain ⟨C, hC, hK⟩ := gaussKernel_le_weight 3 hθ (m := b + 4) (by positivity)
  have hfin : (Module.finrank ℝ Space : ℝ) < 4 := by
    rw [show Module.finrank ℝ Space = 3 by simp [Space]]; norm_num
  refine ((integrable_one_add_norm (μ := (volume : Measure Space)) hfin).const_mul C).mono'
    (((continuous_kernel θ).mul ((continuous_const.add continuous_norm).rpow_const
      (fun _ => Or.inr hb))).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (kernel_nonneg hθ y) (Real.rpow_nonneg hpos.le _))]
  have hk : kernel θ y ≤ C * (1 + ‖y‖) ^ (-(b + 4)) := by
    rw [← Gaussian.gaussKernel_three_eq]; exact hK y
  calc kernel θ y * (1 + ‖y‖) ^ b ≤ C * (1 + ‖y‖) ^ (-(b + 4)) * (1 + ‖y‖) ^ b := by
        gcongr
    _ = C * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; ring_nf

/-- The moment constant `(1 + √Θ)^b ∫ G_1(z)(1 + |z|)^b dz`. -/
def momentConst (b Θ : ℝ) : ℝ :=
  (1 + Real.sqrt Θ) ^ b * ∫ z : Space, kernel 1 z * (1 + ‖z‖) ^ b

theorem momentConst_nonneg {b : ℝ} (Θ : ℝ) : 0 ≤ momentConst b Θ :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (integral_nonneg fun z => mul_nonneg (kernel_nonneg one_pos z)
      (Real.rpow_nonneg (by positivity) _))

/-- **Gaussian moments, uniformly in `0 < θ ≤ Θ`:**
`∫ G_θ(y)(1 + |y|)^b dy ≤ momentConst b Θ` (`b ≥ 0`). Proof: the scaling `y = √θ z`. -/
theorem integral_kernel_mul_weight_le {θ Θ b : ℝ} (hθ : 0 < θ) (hΘ : θ ≤ Θ) (hb : 0 ≤ b) :
    ∫ y : Space, kernel θ y * (1 + ‖y‖) ^ b ≤ momentConst b Θ := by
  set R := Real.sqrt θ with hR
  have hR0 : 0 < R := Real.sqrt_pos.mpr hθ
  have hRθ : R ^ 2 = θ := Real.sq_sqrt hθ.le
  have hRΘ : R ≤ Real.sqrt Θ := Real.sqrt_le_sqrt hΘ
  set f : Space → ℝ := fun y => kernel θ y * (1 + ‖y‖) ^ b with hf
  have hJac := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) f R (hR := hR0.le)
  rw [show Module.finrank ℝ Space = 3 by simp [Space]] at hJac
  have hscale : ∀ z : Space, f (R • z) = (R ^ 3)⁻¹ * (kernel 1 z * (1 + R * ‖z‖) ^ b) := by
    intro z
    simp only [hf]
    have hk : kernel θ (R • z) = (R ^ 3)⁻¹ * kernel 1 z := by
      rw [← Gaussian.gaussKernel_three_eq, ← hRθ,
        show R ^ 2 = R ^ 2 * 1 by ring, Gaussian.gaussKernel_scale hR0 one_pos,
        Real.rpow_neg hR0.le, show ((3 : ℕ) : ℝ) = (3 : ℕ) by rfl, Real.rpow_natCast]
    rw [hk, norm_smul, Real.norm_of_nonneg hR0.le]; ring
  have hint : ∫ y : Space, f y = ∫ z : Space, kernel 1 z * (1 + R * ‖z‖) ^ b := by
    have h1 : ∫ z : Space, f (R • z) =
        (R ^ 3)⁻¹ * ∫ z : Space, kernel 1 z * (1 + R * ‖z‖) ^ b := by
      simp_rw [hscale]; rw [integral_const_mul]
    rw [h1, smul_eq_mul] at hJac
    have hR3 : (R ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hR0.ne')
    exact (mul_left_cancel₀ hR3 hJac).symm
  rw [hint, momentConst, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z => mul_nonneg
      (kernel_nonneg one_pos z) (Real.rpow_nonneg (by positivity) _))
    ((integrable_kernel_mul_weight one_pos hb).const_mul _) (Eventually.of_forall fun z => ?_)
  have h1 : 1 + R * ‖z‖ ≤ (1 + Real.sqrt Θ) * (1 + ‖z‖) := by
    nlinarith [norm_nonneg z, Real.sqrt_nonneg Θ, mul_le_mul_of_nonneg_right hRΘ (norm_nonneg z)]
  calc kernel 1 z * (1 + R * ‖z‖) ^ b ≤ kernel 1 z * ((1 + Real.sqrt Θ) * (1 + ‖z‖)) ^ b := by
        gcongr
        exact kernel_nonneg one_pos z
    _ = (1 + Real.sqrt Θ) ^ b * (kernel 1 z * (1 + ‖z‖) ^ b) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **INF04 T9 `norm_average_le_weight`.** If `|f(y)| ≤ M (1 + |y|)^β` everywhere (`β ∈ ℝ`),
then `|e^{θΔ}f(x)| ≤ momentConst |β| Θ · M · (1 + |x|)^β` for `0 < θ ≤ Θ` and every `x`
(BP3; B0710, B0722, B0572). No measurability hypothesis is needed. -/
theorem norm_average_le_weight {θ Θ β M : ℝ} (hθ : 0 < θ) (hΘ : θ ≤ Θ) {f : Space → E}
    (hf : ∀ y, ‖f y‖ ≤ M * (1 + ‖y‖) ^ β) (x : Space) :
    ‖average θ f x‖ ≤ momentConst |β| Θ * M * (1 + ‖x‖) ^ β := by
  have hM : 0 ≤ M := by
    have := (norm_nonneg _).trans (hf 0)
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos (by positivity) _)
  have hint : Integrable (fun y : Space =>
      M * (1 + ‖x‖) ^ β * (kernel θ y * (1 + ‖y‖) ^ |β|)) :=
    (integrable_kernel_mul_weight hθ (abs_nonneg β)).const_mul _
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg hθ y)]
    have hp : (1 + ‖x - y‖) ^ β ≤ (1 + ‖y‖) ^ |β| * (1 + ‖x‖) ^ β := by
      have h := peetre_sharp β (x - y) x
      simpa only [sub_sub_cancel_left, norm_neg] using h
    calc kernel θ y * ‖f (x - y)‖ ≤ kernel θ y * (M * (1 + ‖x - y‖) ^ β) :=
          mul_le_mul_of_nonneg_left (hf _) (kernel_nonneg hθ y)
      _ ≤ kernel θ y * (M * ((1 + ‖y‖) ^ |β| * (1 + ‖x‖) ^ β)) := by
          gcongr; exact kernel_nonneg hθ y
      _ = M * (1 + ‖x‖) ^ β * (kernel θ y * (1 + ‖y‖) ^ |β|) := by ring
  · rw [integral_const_mul]
    calc M * (1 + ‖x‖) ^ β * ∫ y : Space, kernel θ y * (1 + ‖y‖) ^ |β|
        ≤ M * (1 + ‖x‖) ^ β * momentConst |β| Θ := by
          gcongr
          exact integral_kernel_mul_weight_le hθ hΘ (abs_nonneg β)
      _ = momentConst |β| Θ * M * (1 + ‖x‖) ^ β := by ring

/-! ### The scale-invariant class -/

/-- **INF04 T9 `InvDistClass`.** `u` is `C^k` off the origin with
`‖D^j u(x)‖ ≤ C |x|^{-(1+j)}` for `j ≤ k`, `x ≠ 0` (the class `𝒦_k(C)` of BP3; the DSS datum,
tex 275–278, B0710). -/
structure InvDistClass (k : ℕ) (C : ℝ) (u : Space → E) : Prop where
  smooth : ContDiffOn ℝ k u {0}ᶜ
  bound : ∀ j ≤ k, ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ j u x‖ ≤ C * ‖x‖ ^ (-(1 + j : ℝ))

/-- **INF04 T9 `InvDistClass.dilate`.** The class is invariant under `u ↦ λu(λ·)`, `λ > 0`, with
the same constant (`λ^{1+j}|λx|^{-1-j} = |x|^{-1-j}`). -/
theorem InvDistClass.dilate {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u)
    {lam : ℝ} (hlam : 0 < lam) : InvDistClass k C (fun y => lam • u (lam • y)) where
  smooth := by
    have h1 : ContDiffOn ℝ k (fun y : Space => lam • y) {0}ᶜ :=
      (contDiff_const_smul lam).contDiffOn
    have hmaps : MapsTo (fun y : Space => lam • y) {0}ᶜ {0}ᶜ := fun y hy => by
      simp only [mem_compl_iff, mem_singleton_iff] at hy ⊢
      exact smul_ne_zero hlam.ne' hy
    exact (hu.smooth.comp h1 hmaps).const_smul lam
  bound j hj x hx := by
    rw [Gaussian.iteratedFDeriv_comp_smul j u lam lam x, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    have hlx : lam • x ≠ 0 := smul_ne_zero hlam.ne' hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc lam * lam ^ j * ‖iteratedFDeriv ℝ j u (lam • x)‖
        ≤ lam * lam ^ j * (C * ‖lam • x‖ ^ (-(1 + j : ℝ))) := by
          gcongr; exact hu.bound j hj _ hlx
      _ = C * ‖x‖ ^ (-(1 + j : ℝ)) := by
          rw [norm_smul, Real.norm_of_nonneg hlam.le,
            Real.mul_rpow hlam.le hnx.le]
          have : lam * lam ^ j * lam ^ (-(1 + j : ℝ)) = 1 := by
            rw [← Real.rpow_natCast, ← Real.rpow_one_add' hlam.le (by positivity),
              ← Real.rpow_add hlam]
            simp
          calc lam * lam ^ j * (C * (lam ^ (-(1 + j : ℝ)) * ‖x‖ ^ (-(1 + j : ℝ))))
              = (lam * lam ^ j * lam ^ (-(1 + j : ℝ))) * (C * ‖x‖ ^ (-(1 + j : ℝ))) := by ring
            _ = C * ‖x‖ ^ (-(1 + j : ℝ)) := by rw [this, one_mul]

/-- Fields of the class are heat-admissible. -/
theorem InvDistClass.heatAdmissible {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u) :
    HeatAdmissible u := by
  have hcont : ContinuousOn u {0}ᶜ := hu.smooth.continuousOn
  have hm : AEStronglyMeasurable u volume := by
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure Space))
      (measurableSet_singleton (0 : Space)).compl
    rwa [Measure.restrict_eq_self_of_ae_mem (by
      filter_upwards [Measure.ae_ne volume (0 : Space)] with y hy
      exact hy)] at h
  refine HeatAdmissible.of_inv_bound hm (C := C) fun x hx => ?_
  have h := hu.bound 0 (Nat.zero_le k) x hx
  rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero, Real.rpow_neg_one] at h

/-! ### Small-time decay away from the support -/

/-- `t^{-q} e^{-A/t} ≤ C t^N` on `(0, 1]` (`A > 0`, `q ≥ 0`). -/
theorem rpow_neg_mul_exp_le_pow {A q : ℝ} (hA : 0 < A) (hq : 0 ≤ q) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ^ (-q) * Real.exp (-(A / t)) ≤ C * t ^ N := by
  obtain ⟨C₀, hC₀, hC⟩ := Gaussian.rpow_mul_exp_neg_le (p := q + N) (by positivity)
  refine ⟨A ^ (-(q + N)) * C₀, by positivity, fun t ht => ?_⟩
  have h1 := hC (A / t) (by positivity)
  have hs : (A / t) ^ (q + N) = A ^ (q + N) * t ^ (-(q + N)) := by
    rw [Real.div_rpow hA.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  have hAq : 0 < A ^ (q + N) := Real.rpow_pos_of_pos hA _
  rw [hs] at h1
  have key : t ^ (-(q + N)) * Real.exp (-(A / t)) ≤ A ^ (-(q + N)) * C₀ := by
    rw [Real.rpow_neg hA.le, ← div_eq_inv_mul, le_div_iff₀ hAq]
    linarith [h1, mul_comm (A ^ (q + N)) (t ^ (-(q + N)))]
  have hsplit : t ^ (-q) = t ^ (-(q + N)) * t ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]; ring_nf
  rw [hsplit]
  calc t ^ (-(q + N)) * t ^ N * Real.exp (-(A / t))
      = (t ^ (-(q + N)) * Real.exp (-(A / t))) * t ^ N := by ring
    _ ≤ A ^ (-(q + N)) * C₀ * t ^ N := by gcongr

/-- **INF04 T9 `heat_vanishing_tail`.** If `d` is admissible and vanishes on `B(0, 2ε)`, then
for every `j` and `N` there is `C` with `‖D^j e^{tΔ}d(x)‖ ≤ C t^N` for `t ∈ (0, 1]` and
`|x| ≤ ε` (B1028: the defect field does not reach the core at small times). -/
theorem heat_vanishing_tail {d : Space → E} {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ y ∈ Metric.ball (0 : Space) (2 * ε), d y = 0) (hadm : HeatAdmissible d)
    (j N : ℕ) : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : Space) ε,
      ‖iteratedFDeriv ℝ j (average t d) x‖ ≤ C * t ^ N := by
  obtain ⟨m, hm⟩ := hadm.integrable_norm
  obtain ⟨C₁, hC₁0, hC₁⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le 3 j
  obtain ⟨C₂, hC₂0, hC₂⟩ := rpow_neg_mul_exp_le_pow (A := ε ^ 2 / 16)
    (q := ((3 : ℕ) + (j : ℝ)) / 2) (by positivity) (by positivity) N
  obtain ⟨C₃, hC₃0, hC₃⟩ := one_add_rpow_mul_exp_le (m := (m : ℝ)) (b := 1 / 64)
    (by positivity) (by norm_num)
  set I := ∫ y : Space, (1 + ‖y‖) ^ (-(m : ℝ)) * ‖d y‖ with hI
  refine ⟨C₁ * C₂ * C₃ * I, fun t ht x hx => ?_⟩
  obtain ⟨ht0, ht1⟩ := ht
  have hxε : ‖x‖ ≤ ε := by simpa using hx
  refine (norm_iteratedFDeriv_average_le_kernel hadm ht0 j x).trans ?_
  have hbound : ∀ y : Space, ‖iteratedFDeriv ℝ j (kernel t) (x - y)‖ * ‖d y‖ ≤
      C₁ * C₂ * C₃ * t ^ N * ((1 + ‖y‖) ^ (-(m : ℝ)) * ‖d y‖) := by
    intro y
    by_cases hy : ‖y‖ < 2 * ε
    · rw [hd y (by simpa using hy), norm_zero, mul_zero, mul_zero, mul_zero]
    · push_neg at hy
      have hxy1 : ‖y‖ / 2 ≤ ‖x - y‖ := by
        have := norm_sub_norm_le y x
        rw [norm_sub_rev] at this
        linarith
      have hxy2 : ε ≤ ‖x - y‖ := by linarith
      have hK := hC₁ ht0 (x - y)
      rw [← Gaussian.gaussKernel_three_eq] at *
      have hexp : Real.exp (-‖x - y‖ ^ 2 / (8 * t)) ≤
          Real.exp (-(ε ^ 2 / 16 / t)) * Real.exp (-(1 / 64 * ‖y‖ ^ 2)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h1 : ε ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hε.le hxy2 2
        have h2 : ‖y‖ ^ 2 / 4 ≤ ‖x - y‖ ^ 2 := by
          nlinarith [pow_le_pow_left₀ (by positivity) hxy1 2]
        have h3 : ‖y‖ ^ 2 / 4 / (16 * t) ≥ ‖y‖ ^ 2 / 64 := by
          rw [ge_iff_le, div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [sq_nonneg ‖y‖]
        have h4 : -‖x - y‖ ^ 2 / (8 * t) =
            -(‖x - y‖ ^ 2 / (16 * t)) - ‖x - y‖ ^ 2 / (16 * t) := by
          field_simp; ring
        rw [h4]
        have h5 : ε ^ 2 / 16 / t ≤ ‖x - y‖ ^ 2 / (16 * t) := by
          rw [div_div]; exact div_le_div_of_nonneg_right h1 (by positivity)
        have h6 : ‖y‖ ^ 2 / 4 / (16 * t) ≤ ‖x - y‖ ^ 2 / (16 * t) :=
          div_le_div_of_nonneg_right h2 (by positivity)
        linarith
      have hw : Real.exp (-(1 / 64 * ‖y‖ ^ 2)) ≤ C₃ * (1 + ‖y‖) ^ (-(m : ℝ)) := by
        have := hC₃ ‖y‖ (norm_nonneg y)
        have hpos : 0 < (1 + ‖y‖) ^ (m : ℝ) := Real.rpow_pos_of_pos (by positivity) _
        rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith [mul_comm ((1 + ‖y‖) ^ (m : ℝ)) (Real.exp (-(1 / 64 * ‖y‖ ^ 2)))]
      have ht2 := hC₂ t ht0
      have hq : t ^ (-((((3 : ℕ) : ℝ) + j) / 2)) = t ^ (-(((3 : ℕ) + (j : ℝ)) / 2)) := rfl
      calc ‖iteratedFDeriv ℝ j (gaussKernel 3 t) (x - y)‖ * ‖d y‖
          ≤ C₁ * t ^ (-((((3 : ℕ) : ℝ) + j) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) *
              ‖d y‖ := by gcongr
        _ ≤ C₁ * t ^ (-((((3 : ℕ) : ℝ) + j) / 2)) *
              (Real.exp (-(ε ^ 2 / 16 / t)) * Real.exp (-(1 / 64 * ‖y‖ ^ 2))) * ‖d y‖ := by
            gcongr
        _ = C₁ * (t ^ (-((((3 : ℕ) : ℝ) + j) / 2)) * Real.exp (-(ε ^ 2 / 16 / t))) *
              Real.exp (-(1 / 64 * ‖y‖ ^ 2)) * ‖d y‖ := by ring
        _ ≤ C₁ * (C₂ * t ^ N) * (C₃ * (1 + ‖y‖) ^ (-(m : ℝ))) * ‖d y‖ := by
            gcongr
        _ = C₁ * C₂ * C₃ * t ^ N * ((1 + ‖y‖) ^ (-(m : ℝ)) * ‖d y‖) := by ring
  calc ∫ y : Space, ‖iteratedFDeriv ℝ j (kernel t) (x - y)‖ * ‖d y‖
      ≤ ∫ y : Space, C₁ * C₂ * C₃ * t ^ N * ((1 + ‖y‖) ^ (-(m : ℝ)) * ‖d y‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hm.const_mul _)
          (Eventually.of_forall hbound)
    _ = C₁ * C₂ * C₃ * I * t ^ N := by rw [integral_const_mul, hI]; ring

end UnforcedLeray.Heat
