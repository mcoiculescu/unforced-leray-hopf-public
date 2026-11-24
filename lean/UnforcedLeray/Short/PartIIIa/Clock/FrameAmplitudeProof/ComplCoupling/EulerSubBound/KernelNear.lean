import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.Lattice

/-!
# Comparison of the cylinder and planar adjoint interactions (helper for `PartIII-a:T21/c5/3/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2876-2889:
for `|y| ≤ d/8` the localized interaction `K_d^T(Φ ∇E)` differs from the planar `K_∞^T(λ∇E₀)` by
`O(d⁻² ⟨y⟩²)`, when `Φ - λ = O(d⁻²)`, `∇E - ∇E₀ = O(d⁻² ⟨x⟩⁻⁴)` on the cell and `∇E₀` is Gaussian.
The cell is split into `N = {|x| < d/5}`, where the image expansion `K_d - K_∞ = O(d⁻²|x - y|)`
applies, and its complement, where the source is Gaussian-small and `|K_∞(x - y)| ≤ 3/d`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerSubCore

theorem continuous_planeToC : Continuous planeToC := by
  have h : planeToC = fun z : ℝ × ℝ => (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := funext planeToC_eq
  rw [h]; fun_prop

theorem planeToC_sub (x y : ℝ × ℝ) : planeToC (x - y) = planeToC x - planeToC y := by
  apply Complex.ext <;> simp [planeToC]

theorem jb_eq_norm (x : ℝ × ℝ) : B0579.jb x = 1 + ‖planeToC x‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [B0579.jb, planeToC]; ring

theorem norm_planeToC_le_jb (x : ℝ × ℝ) : ‖planeToC x‖ ≤ B0579.jb x := by
  rw [jb_eq_norm]; nlinarith [sq_nonneg (‖planeToC x‖ - 1), norm_nonneg (planeToC x)]

theorem one_le_jb (x : ℝ × ℝ) : 1 ≤ B0579.jb x := by
  rw [jb_eq_norm]; nlinarith [sq_nonneg ‖planeToC x‖]

theorem sq_norm_planeToC (x : ℝ × ℝ) : ‖planeToC x‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  have := jb_eq_norm x; simp only [B0579.jb] at this; linarith

theorem mem_cell_of_norm_lt {d : ℝ} {x : ℝ × ℝ} (hx : ‖planeToC x‖ < d / 2) :
    x ∈ B0579.cell d := by
  have h1 : |x.1| ≤ ‖planeToC x‖ := by
    have := Complex.abs_re_le_norm (planeToC x); simpa [planeToC] using this
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · linarith [neg_abs_le x.1]
  · linarith [le_abs_self x.1]

theorem measurable_kerPl (j : Fin 2) : Measurable fun z => kerPl z j := by
  have hc : Measurable fun z : ℝ × ℝ =>
      (2 * Real.pi * Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I))⁻¹ := by
    refine Measurable.inv ?_
    fun_prop
  fin_cases j
  · exact Complex.measurable_re.comp hc
  · exact (Complex.measurable_im.comp hc).neg

theorem measurable_kerD {d : ℝ} (hd : 1 ≤ d) (j : Fin 2) : Measurable fun z => kerD d z j := by
  obtain ⟨_, _, h⟩ := kerNearFar
  exact (h d hd).1 j

theorem measurable_pd (f : ℝ × ℝ → ℝ) (l : Fin 2) : Measurable fun x => B0579.pd l f x :=
  measurable_fderiv_apply_const ℝ f (B0579.dir l)

/-- `e^{-s/16} ≤ 16/s` for `s > 0`. -/
theorem exp_neg_div_sixteen_le {s : ℝ} (hs : 0 < s) : Real.exp (-(s / 16)) ≤ 16 / s := by
  have h := Real.add_one_le_exp (s / 16)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  linarith

/-- **Uniform bound of the localized interaction**: `jb² |Φ ∂E| ≤ B₀ C_E` gives
`|K_d^T(Φ∇E)| ≤ C_K' B₀ C_E` everywhere, with the component integrals integrable. -/
theorem kernel_unif : ∃ K : ℝ, 0 ≤ K ∧ ∀ (d B₀ C_E : ℝ), 1 ≤ d → 0 ≤ B₀ → 0 ≤ C_E →
    ∀ (Φ : ℝ × ℝ → ℂ) (E : ℝ × ℝ → ℝ), Continuous Φ →
    (∀ x ∈ B0579.cell d, ‖Φ x‖ ≤ B₀) →
    (∀ (l : Fin 2), ∀ x ∈ B0579.cell d, B0579.jb x ^ 2 * |B0579.pd l E x| ≤ C_E) →
    ∀ y : ℝ × ℝ,
      (∀ l : Fin 2, IntegrableOn (fun w => Φ w * ((B0579.pd l E w : ℝ) : ℂ) *
        ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d)) ∧
      ‖kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y‖ ≤ K * (B₀ * C_E) := by
  obtain ⟨C_K, hCK0, hKer⟩ := DirectEulerSub.kerAdj_term_integrableOn_and_bound
  refine ⟨2 * C_K, by positivity, fun d B₀ C_E hd hB₀ hCE Φ E hΦc hΦ hE y => ?_⟩
  have hb : ∀ l : Fin 2, ∀ w ∈ B0579.cell d,
      B0579.jb w ^ 2 * ‖Φ w * ((B0579.pd l E w : ℝ) : ℂ)‖ ≤ B₀ * C_E := by
    intro l w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hΦ w hw
    have h2 := hE l w hw
    have hj : 0 ≤ B0579.jb w ^ 2 := by positivity
    calc B0579.jb w ^ 2 * (‖Φ w‖ * |B0579.pd l E w|)
        = ‖Φ w‖ * (B0579.jb w ^ 2 * |B0579.pd l E w|) := by ring
      _ ≤ B₀ * C_E := mul_le_mul h1 h2 (by positivity) hB₀
  have hm : ∀ l : Fin 2, AEStronglyMeasurable (fun w => Φ w * ((B0579.pd l E w : ℝ) : ℂ))
      (volume.restrict (B0579.cell d)) := fun l =>
    (hΦc.measurable.mul (Complex.measurable_ofReal.comp (measurable_pd E l))).aestronglyMeasurable
  have hK := fun l => hKer hd (by positivity) (hm l) (hb l) y l
  refine ⟨fun l => (hK l).1, ?_⟩
  unfold kerAdj
  rw [integral_finsetSum _ (fun l _ => (hK l).1)]
  calc ‖∑ l : Fin 2, ∫ x in B0579.cell d, Φ x * ((B0579.pd l E x : ℝ) : ℂ) *
        ((kerD d (x - y) l : ℝ) : ℂ)‖
      ≤ ∑ l : Fin 2, ‖∫ x in B0579.cell d, Φ x * ((B0579.pd l E x : ℝ) : ℂ) *
        ((kerD d (x - y) l : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin 2, C_K * (B₀ * C_E) := Finset.sum_le_sum fun l _ => (hK l).2
    _ = 2 * C_K * (B₀ * C_E) := by simp; ring

/-- The near region `N = {|x| < d/5}` of the comparison. -/
def nearSet (d : ℝ) : Set (ℝ × ℝ) := {x | ‖planeToC x‖ < d / 5}

theorem measurableSet_nearSet (d : ℝ) : MeasurableSet (nearSet d) :=
  (isOpen_lt (continuous_norm.comp continuous_planeToC) continuous_const).measurableSet

theorem nearSet_subset_cell {d : ℝ} (hd : 0 < d) : nearSet d ⊆ B0579.cell d := fun _ hx =>
  mem_cell_of_norm_lt (lt_of_lt_of_le hx (by linarith))

/-- Off the near region, `jb² e^{-|x|²/8} ≤ 1026 · 400 / d²`. -/
theorem jb_sq_exp_le_of_not_mem {d : ℝ} (hd : 0 < d) {x : ℝ × ℝ} (hx : x ∉ nearSet d) :
    B0579.jb x ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) ≤ 1026 * (400 / d ^ 2) := by
  have hs : d ^ 2 / 25 ≤ x.1 ^ 2 + x.2 ^ 2 := by
    have h1 : d / 5 ≤ ‖planeToC x‖ := le_of_not_gt hx
    rw [← sq_norm_planeToC]
    nlinarith [norm_nonneg (planeToC x)]
  have hs0 : 0 < x.1 ^ 2 + x.2 ^ 2 := lt_of_lt_of_le (by positivity) hs
  refine (jb_sq_mul_exp_le x).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have h := exp_neg_div_sixteen_le hs0
  rw [show -(x.1 ^ 2 + x.2 ^ 2) / 16 = -((x.1 ^ 2 + x.2 ^ 2) / 16) by ring]
  refine h.trans ?_
  rw [div_le_div_iff₀ hs0 (by positivity)]
  nlinarith

/-- `jb² e^{-|x|²/8} ≤ 1026`. -/
theorem jb_sq_exp_le_const (x : ℝ × ℝ) :
    B0579.jb x ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) ≤ 1026 := by
  have h3 : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x.1, sq_nonneg x.2])
  have := jb_sq_mul_exp_le x
  linarith

/-- The source error `G = Φ∂E - 1_N λ ∂E₀` is `O(d⁻² jb⁻²)` on the cell. -/
theorem source_err_bound {d B₀ Cl C₁ C_E : ℝ} (hd : 1 ≤ d) (hB₀ : 0 ≤ B₀) (hCl : 0 ≤ Cl)
    (hC₁ : 0 ≤ C₁) (hCE : 0 ≤ C_E) {Φ lamF : ℝ × ℝ → ℂ} {e e0 : ℝ × ℝ → ℝ}
    {x : ℝ × ℝ} (hx : x ∈ B0579.cell d) (hΦ : ‖Φ x‖ ≤ B₀) (hl : ‖lamF x‖ ≤ Cl)
    (hΦl : ‖Φ x - lamF x‖ ≤ C₁ / d ^ 2)
    (he0 : |e0 x| ≤ C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8))
    (hee0 : B0579.jb x ^ 2 * |e x - e0 x| ≤ C_E / d ^ 2) (he : B0579.jb x ^ 2 * |e x| ≤ C_E) :
    B0579.jb x ^ 2 * ‖Φ x * ((e x : ℝ) : ℂ) -
      (nearSet d).indicator (fun z => lamF z * ((e0 z : ℝ) : ℂ)) x‖ ≤
      (C₁ + Cl + 410401 * B₀) * C_E / d ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d ^ 2 := by positivity
  have hj : 0 ≤ B0579.jb x ^ 2 := by positivity
  by_cases hxN : x ∈ nearSet d
  · rw [Set.indicator_of_mem hxN]
    have hGx : Φ x * ((e x : ℝ) : ℂ) - lamF x * ((e0 x : ℝ) : ℂ) =
        (Φ x - lamF x) * ((e x : ℝ) : ℂ) + lamF x * ((e x - e0 x : ℝ) : ℂ) := by
      push_cast; ring
    rw [hGx]
    have hn : ‖(Φ x - lamF x) * ((e x : ℝ) : ℂ) + lamF x * ((e x - e0 x : ℝ) : ℂ)‖ ≤
        ‖Φ x - lamF x‖ * |e x| + ‖lamF x‖ * |e x - e0 x| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    have e1 : ‖Φ x - lamF x‖ * (B0579.jb x ^ 2 * |e x|) ≤ C₁ / d ^ 2 * C_E :=
      mul_le_mul hΦl he (by positivity) (by positivity)
    have e2 : ‖lamF x‖ * (B0579.jb x ^ 2 * |e x - e0 x|) ≤ Cl * (C_E / d ^ 2) :=
      mul_le_mul hl hee0 (by positivity) hCl
    have e3 : C₁ / d ^ 2 * C_E + Cl * (C_E / d ^ 2) ≤ (C₁ + Cl + 410401 * B₀) * C_E / d ^ 2 := by
      rw [show C₁ / d ^ 2 * C_E + Cl * (C_E / d ^ 2) = (C₁ * C_E + Cl * C_E) / d ^ 2 by ring]
      apply div_le_div_of_nonneg_right _ hd2.le
      nlinarith [mul_nonneg hB₀ hCE]
    calc B0579.jb x ^ 2 * ‖(Φ x - lamF x) * ((e x : ℝ) : ℂ) + lamF x * ((e x - e0 x : ℝ) : ℂ)‖
        ≤ B0579.jb x ^ 2 * (‖Φ x - lamF x‖ * |e x| + ‖lamF x‖ * |e x - e0 x|) :=
          mul_le_mul_of_nonneg_left hn hj
      _ = ‖Φ x - lamF x‖ * (B0579.jb x ^ 2 * |e x|) +
            ‖lamF x‖ * (B0579.jb x ^ 2 * |e x - e0 x|) := by ring
      _ ≤ C₁ / d ^ 2 * C_E + Cl * (C_E / d ^ 2) := add_le_add e1 e2
      _ ≤ (C₁ + Cl + 410401 * B₀) * C_E / d ^ 2 := e3
  · rw [Set.indicator_of_notMem hxN, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hexp := jb_sq_exp_le_of_not_mem hd0 hxN
    have hE0x : B0579.jb x ^ 2 * |e0 x| ≤ C_E * (1026 * (400 / d ^ 2)) := by
      calc B0579.jb x ^ 2 * |e0 x|
          ≤ B0579.jb x ^ 2 * (C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) :=
            mul_le_mul_of_nonneg_left he0 hj
        _ = C_E * (B0579.jb x ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by ring
        _ ≤ C_E * (1026 * (400 / d ^ 2)) := mul_le_mul_of_nonneg_left hexp hCE
    have htri : |e x| ≤ |e x - e0 x| + |e0 x| := by
      have := abs_add_le (e x - e0 x) (e0 x)
      rwa [sub_add_cancel] at this
    have hEtot : B0579.jb x ^ 2 * |e x| ≤ C_E / d ^ 2 + C_E * (1026 * (400 / d ^ 2)) := by
      have := mul_le_mul_of_nonneg_left htri hj
      linarith
    calc B0579.jb x ^ 2 * (‖Φ x‖ * |e x|)
        = ‖Φ x‖ * (B0579.jb x ^ 2 * |e x|) := by ring
      _ ≤ B₀ * (C_E / d ^ 2 + C_E * (1026 * (400 / d ^ 2))) :=
          mul_le_mul hΦ hEtot (by positivity) hB₀
      _ = 410401 * B₀ * C_E / d ^ 2 := by ring
      _ ≤ (C₁ + Cl + 410401 * B₀) * C_E / d ^ 2 := by
          apply div_le_div_of_nonneg_right _ hd2.le
          nlinarith [mul_nonneg hC₁ hCE, mul_nonneg hCl hCE]

/-- Pointwise bound on the near region for the image-expansion term. -/
theorem near_pointwise {d C_I Cl C_E : ℝ} (hd : 1 ≤ d) (hCI : 0 ≤ C_I) (hCl : 0 ≤ Cl)
    (hCE : 0 ≤ C_E) {f : ℂ} {x y : ℝ × ℝ} (l : Fin 2)
    (hf : ‖f‖ ≤ Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8))
    (himg : |kerD d (x - y) l - kerPl (x - y) l| ≤ C_I * ‖planeToC (x - y)‖ / d ^ 2) :
    ‖f * (((kerD d (x - y) l : ℝ) : ℂ) - ((kerPl (x - y) l : ℝ) : ℂ))‖ ≤
      2 * Cl * C_E * C_I * B0579.jb y / d ^ 2 *
        (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
  have hxy2 : ‖planeToC (x - y)‖ ≤ 2 * B0579.jb x * B0579.jb y := by
    rw [planeToC_sub]
    have h1 := norm_sub_le (planeToC x) (planeToC y)
    have h2 := norm_planeToC_le_jb x
    have h3 := norm_planeToC_le_jb y
    have h4 := one_le_jb x
    have h5 := one_le_jb y
    nlinarith
  have hk : ((kerD d (x - y) l : ℝ) : ℂ) - ((kerPl (x - y) l : ℝ) : ℂ) =
      ((kerD d (x - y) l - kerPl (x - y) l : ℝ) : ℂ) := by push_cast; ring
  rw [hk, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hEx := Real.exp_pos (-(x.1 ^ 2 + x.2 ^ 2) / 8)
  have hd2 : 0 < d ^ 2 := by positivity
  calc ‖f‖ * |kerD d (x - y) l - kerPl (x - y) l|
      ≤ (Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) *
          (C_I * ‖planeToC (x - y)‖ / d ^ 2) :=
        mul_le_mul hf himg (abs_nonneg _) (by positivity)
    _ ≤ (Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) *
          (C_I * (2 * B0579.jb x * B0579.jb y) / d ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ hd2.le
        exact mul_le_mul_of_nonneg_left hxy2 hCI
    _ = 2 * Cl * C_E * C_I * B0579.jb y / d ^ 2 *
          (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by ring

/-- Pointwise bound off the near region for the planar kernel term (`|y| ≤ d/8`). -/
theorem far_pointwise {d Cl C_E : ℝ} (hd : 1 ≤ d) (hCl : 0 ≤ Cl) (hCE : 0 ≤ C_E) {f : ℂ}
    {x y : ℝ × ℝ} (l : Fin 2) (hy : ‖planeToC y‖ ≤ d / 8) (hx : x ∉ nearSet d)
    (hf : ‖f‖ ≤ Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) :
    ‖f * ((kerPl (x - y) l : ℝ) : ℂ)‖ ≤
      75 * Cl * C_E / d ^ 3 * (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
  have hd0 : 0 < d := by linarith
  have hx' : d / 5 ≤ ‖planeToC x‖ := le_of_not_gt hx
  have hz : 3 * d / 40 ≤ ‖planeToC (x - y)‖ := by
    rw [planeToC_sub]
    have := norm_sub_norm_le (planeToC x) (planeToC y)
    linarith
  have hzpos : 0 < ‖planeToC (x - y)‖ := lt_of_lt_of_le (by positivity) hz
  have hkpb : |kerPl (x - y) l| ≤ 3 / d := by
    refine (abs_kerPl_le _ _).trans ?_
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
    have hpi := Real.pi_gt_three
    have := mul_le_mul hpi.le hz (by positivity) (by positivity)
    nlinarith
  have hjbx : d ^ 2 / 25 ≤ B0579.jb x := by
    rw [jb_eq_norm]; nlinarith [norm_nonneg (planeToC x)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hEx := Real.exp_pos (-(x.1 ^ 2 + x.2 ^ 2) / 8)
  have h25 : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) ≤
      25 / d ^ 2 * (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
    have h1 : 1 ≤ 25 / d ^ 2 * B0579.jb x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    calc Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) = 1 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) := by ring
      _ ≤ (25 / d ^ 2 * B0579.jb x) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) :=
          mul_le_mul_of_nonneg_right h1 hEx.le
      _ = 25 / d ^ 2 * (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by ring
  calc ‖f‖ * |kerPl (x - y) l|
      ≤ (Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) * (3 / d) :=
        mul_le_mul hf hkpb (abs_nonneg _) (by positivity)
    _ ≤ (Cl * C_E * (25 / d ^ 2 * (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)))) *
          (3 / d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h25 (by positivity)
    _ = 75 * Cl * C_E / d ^ 3 * (B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
        field_simp; ring

/-- The integrable Gaussian majorant `jb e^{-|x|²/8}` and its integral. -/
theorem integrable_g₁ :
    Integrable (fun x : ℝ × ℝ => B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
  have := integrable_jb_gauss (m := 1) zero_le_one
  simpa only [Real.rpow_one] using this

/-- One component of the comparison of the localized interactions (SP 2876-2889). -/
theorem kernel_near_comp : ∃ K : ℝ, 0 ≤ K ∧ ∀ (d B₀ Cl C₁ C_E : ℝ), 1 ≤ d → 0 ≤ B₀ → 0 ≤ Cl →
    0 ≤ C₁ → 0 ≤ C_E → ∀ (Φ lamF : ℝ × ℝ → ℂ) (E E0 : ℝ × ℝ → ℝ), Continuous Φ →
    Continuous lamF →
    (∀ x ∈ B0579.cell d, ‖Φ x‖ ≤ B₀) → (∀ x, ‖lamF x‖ ≤ Cl) →
    (∀ x ∈ B0579.cell d, ‖Φ x - lamF x‖ ≤ C₁ / d ^ 2) → ∀ l : Fin 2,
    (∀ x : ℝ × ℝ, |B0579.pd l E0 x| ≤ C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) →
    (∀ x ∈ B0579.cell d,
      B0579.jb x ^ 2 * |B0579.pd l E x - B0579.pd l E0 x| ≤ C_E / d ^ 2) →
    (∀ x ∈ B0579.cell d, B0579.jb x ^ 2 * |B0579.pd l E x| ≤ C_E) →
    ∀ y : ℝ × ℝ, ‖planeToC y‖ ≤ d / 8 →
      IntegrableOn (fun x => Φ x * ((B0579.pd l E x : ℝ) : ℂ) * ((kerD d (x - y) l : ℝ) : ℂ))
        (B0579.cell d) ∧
      Integrable (fun x => lamF x * ((B0579.pd l E0 x : ℝ) : ℂ) * ((kerPl (x - y) l : ℝ) : ℂ)) ∧
      ‖(∫ x in B0579.cell d, Φ x * ((B0579.pd l E x : ℝ) : ℂ) * ((kerD d (x - y) l : ℝ) : ℂ)) -
        ∫ x, lamF x * ((B0579.pd l E0 x : ℝ) : ℂ) * ((kerPl (x - y) l : ℝ) : ℂ)‖ ≤
        K * ((B₀ + Cl + C₁) * C_E) * B0579.jb y / d ^ 2 := by
  obtain ⟨C_K, hCK0, hKer⟩ := DirectEulerSub.kerAdj_term_integrableOn_and_bound
  obtain ⟨C_I, hCI0, hImg⟩ := kerD_sub_kerPl_le
  set g₁ : ℝ × ℝ → ℝ := fun x => B0579.jb x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) with hg₁
  have hg₁i : Integrable g₁ := integrable_g₁
  have hg₁0 : ∀ x, 0 ≤ g₁ x := fun x => mul_nonneg (B0579.jb_pos x).le (Real.exp_pos _).le
  set I₁ : ℝ := ∫ x, g₁ x with hI₁def
  have hI₁ : 0 ≤ I₁ := integral_nonneg hg₁0
  refine ⟨C_K * 410402 + 2 * C_I * I₁ + 75 * I₁, by positivity, ?_⟩
  intro d B₀ Cl C₁ C_E hd hB₀ hCl hC₁ hCE Φ lamF E E0 hΦc hlc hΦ hl hΦl l hE0 hEE0 hE y hy
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d ^ 2 := by positivity
  set N : Set (ℝ × ℝ) := nearSet d with hN
  have hNm : MeasurableSet N := measurableSet_nearSet d
  have hNcell : N ⊆ B0579.cell d := nearSet_subset_cell hd0
  have hjby : 1 ≤ B0579.jb y := one_le_jb y
  set F0 : ℝ × ℝ → ℂ := fun x => lamF x * ((B0579.pd l E0 x : ℝ) : ℂ) with hF0
  have hFdm : Measurable fun x => Φ x * ((B0579.pd l E x : ℝ) : ℂ) :=
    hΦc.measurable.mul (Complex.measurable_ofReal.comp (measurable_pd E l))
  have hF0m : Measurable F0 :=
    hlc.measurable.mul (Complex.measurable_ofReal.comp (measurable_pd E0 l))
  have hkdm : Measurable fun x => ((kerD d (x - y) l : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_kerD hd l).comp (measurable_id.sub_const y))
  have hkpm : Measurable fun x => ((kerPl (x - y) l : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_kerPl l).comp (measurable_id.sub_const y))
  have hF0b : ∀ x, ‖F0 x‖ ≤ Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) := by
    intro x
    rw [hF0, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hl x) (hE0 x) (abs_nonneg _) hCl
  have hF0jb : ∀ x, B0579.jb x ^ 2 * ‖N.indicator F0 x‖ ≤ Cl * C_E * 1026 := by
    intro x
    have h1 : ‖N.indicator F0 x‖ ≤ ‖F0 x‖ := norm_indicator_le_norm_self _ _
    calc B0579.jb x ^ 2 * ‖N.indicator F0 x‖
        ≤ B0579.jb x ^ 2 * (Cl * C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_left (h1.trans (hF0b x)) (by positivity)
      _ = Cl * C_E * (B0579.jb x ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by ring
      _ ≤ Cl * C_E * 1026 := mul_le_mul_of_nonneg_left (jb_sq_exp_le_const x) (by positivity)
  set M_G : ℝ := (C₁ + Cl + 410401 * B₀) * C_E with hMG
  -- the three kernel facts on the cell
  have hKd : IntegrableOn (fun x => Φ x * ((B0579.pd l E x : ℝ) : ℂ) *
      ((kerD d (x - y) l : ℝ) : ℂ)) (B0579.cell d) := by
    refine (hKer (G := fun x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) hd (M := B₀ * C_E)
      (by positivity) hFdm.aestronglyMeasurable (fun w hw => ?_) y l).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc B0579.jb w ^ 2 * (‖Φ w‖ * |B0579.pd l E w|)
        = ‖Φ w‖ * (B0579.jb w ^ 2 * |B0579.pd l E w|) := by ring
      _ ≤ B₀ * C_E := mul_le_mul (hΦ w hw) (hE w hw) (by positivity) hB₀
  have hKG := hKer (G := fun x => Φ x * ((B0579.pd l E x : ℝ) : ℂ) - N.indicator F0 x) hd
    (M := M_G / d ^ 2) (by positivity)
    ((hFdm.sub (hF0m.indicator hNm)).aestronglyMeasurable)
    (fun x hx => source_err_bound hd hB₀ hCl hC₁ hCE hx (hΦ x hx) (hl x) (hΦl x hx) (hE0 x)
      (hEE0 x hx) (hE x hx)) y l
  have hKN := hKer (G := N.indicator F0) hd (M := Cl * C_E * 1026) (by positivity)
    ((hF0m.indicator hNm).aestronglyMeasurable) (fun w _ => hF0jb w) y l
  -- integrability of the planar integrand
  have hgB : Integrable (fun x => 2 * Cl * C_E * C_I * B0579.jb y / d ^ 2 * g₁ x) :=
    hg₁i.const_mul _
  have hgC : Integrable (fun x => 75 * Cl * C_E / d ^ 3 * g₁ x) := hg₁i.const_mul _
  have hBpt : ∀ x ∈ N, ‖F0 x * (((kerD d (x - y) l : ℝ) : ℂ) - ((kerPl (x - y) l : ℝ) : ℂ))‖ ≤
      2 * Cl * C_E * C_I * B0579.jb y / d ^ 2 * g₁ x := by
    intro x hx
    have hxy : ‖planeToC (x - y)‖ ≤ d / 2 := by
      rw [planeToC_sub]
      have := norm_sub_le (planeToC x) (planeToC y)
      have hx' : ‖planeToC x‖ < d / 5 := hx
      linarith
    exact near_pointwise hd hCI0 hCl hCE l (hF0b x) (hImg d hd (x - y) hxy l)
  have hCpt : ∀ x ∉ N, ‖F0 x * ((kerPl (x - y) l : ℝ) : ℂ)‖ ≤
      75 * Cl * C_E / d ^ 3 * g₁ x := fun x hx =>
    far_pointwise hd hCl hCE l hy hx (hF0b x)
  have hNkd : IntegrableOn (fun x => F0 x * ((kerD d (x - y) l : ℝ) : ℂ)) N := by
    refine (hKN.1.mono_set hNcell).congr_fun (fun x hx => ?_) hNm
    simp only [Set.indicator_of_mem hx]
  have hNB : IntegrableOn (fun x => F0 x * (((kerD d (x - y) l : ℝ) : ℂ) -
      ((kerPl (x - y) l : ℝ) : ℂ))) N :=
    Integrable.mono' hgB.integrableOn (hF0m.mul (hkdm.sub hkpm)).aestronglyMeasurable
      ((ae_restrict_iff' hNm).2 (Eventually.of_forall fun x hx => hBpt x hx))
  have hNkp : IntegrableOn (fun x => F0 x * ((kerPl (x - y) l : ℝ) : ℂ)) N :=
    (hNkd.sub hNB).congr_fun (fun x _ => by simp only [Pi.sub_apply]; ring) hNm
  have hNckp : IntegrableOn (fun x => F0 x * ((kerPl (x - y) l : ℝ) : ℂ)) Nᶜ :=
    Integrable.mono' hgC.integrableOn (hF0m.mul hkpm).aestronglyMeasurable
      ((ae_restrict_iff' hNm.compl).2 (Eventually.of_forall fun x hx => hCpt x hx))
  have hkpInt : Integrable (fun x => F0 x * ((kerPl (x - y) l : ℝ) : ℂ)) := by
    rw [← integrableOn_univ, ← Set.union_compl_self N]
    exact integrableOn_union.2 ⟨hNkp, hNckp⟩
  refine ⟨hKd, hkpInt, ?_⟩
  -- the splitting identity
  have hId : (∫ x in B0579.cell d, Φ x * ((B0579.pd l E x : ℝ) : ℂ) *
        ((kerD d (x - y) l : ℝ) : ℂ)) =
      (∫ x in B0579.cell d, (Φ x * ((B0579.pd l E x : ℝ) : ℂ) - N.indicator F0 x) *
        ((kerD d (x - y) l : ℝ) : ℂ)) + ∫ x in N, F0 x * ((kerD d (x - y) l : ℝ) : ℂ) := by
    have h1 := integral_add hKG.1 hKN.1
    have h2 : (fun x => (Φ x * ((B0579.pd l E x : ℝ) : ℂ) - N.indicator F0 x) *
          ((kerD d (x - y) l : ℝ) : ℂ) + N.indicator F0 x * ((kerD d (x - y) l : ℝ) : ℂ)) =
        fun x => Φ x * ((B0579.pd l E x : ℝ) : ℂ) * ((kerD d (x - y) l : ℝ) : ℂ) := by
      funext x; ring
    have h3 : (∫ x in B0579.cell d, N.indicator F0 x * ((kerD d (x - y) l : ℝ) : ℂ)) =
        ∫ x in N, F0 x * ((kerD d (x - y) l : ℝ) : ℂ) := by
      have : (fun x => N.indicator F0 x * ((kerD d (x - y) l : ℝ) : ℂ)) =
          N.indicator (fun x => F0 x * ((kerD d (x - y) l : ℝ) : ℂ)) := by
        funext x; exact (Set.indicator_mul_left N F0 (fun x => ((kerD d (x - y) l : ℝ) : ℂ))).symm
      rw [this, setIntegral_indicator hNm, Set.inter_eq_right.2 hNcell]
    rw [h2] at h1
    rw [h1, h3]
  have hIp : (∫ x, F0 x * ((kerPl (x - y) l : ℝ) : ℂ)) =
      (∫ x in N, F0 x * ((kerPl (x - y) l : ℝ) : ℂ)) +
        ∫ x in Nᶜ, F0 x * ((kerPl (x - y) l : ℝ) : ℂ) :=
    (integral_add_compl hNm hkpInt).symm
  have hNsub : (∫ x in N, F0 x * ((kerD d (x - y) l : ℝ) : ℂ)) -
      ∫ x in N, F0 x * ((kerPl (x - y) l : ℝ) : ℂ) =
      ∫ x in N, F0 x * (((kerD d (x - y) l : ℝ) : ℂ) - ((kerPl (x - y) l : ℝ) : ℂ)) := by
    rw [← integral_sub hNkd hNkp]
    congr 1; funext x; ring
  set IA := ∫ x in B0579.cell d, (Φ x * ((B0579.pd l E x : ℝ) : ℂ) - N.indicator F0 x) *
    ((kerD d (x - y) l : ℝ) : ℂ) with hIA
  set IB := ∫ x in N, F0 x * (((kerD d (x - y) l : ℝ) : ℂ) - ((kerPl (x - y) l : ℝ) : ℂ))
    with hIB
  set IC := ∫ x in Nᶜ, F0 x * ((kerPl (x - y) l : ℝ) : ℂ) with hIC
  have htot : (∫ x in B0579.cell d, Φ x * ((B0579.pd l E x : ℝ) : ℂ) *
        ((kerD d (x - y) l : ℝ) : ℂ)) - ∫ x, F0 x * ((kerPl (x - y) l : ℝ) : ℂ) =
      IA + IB - IC := by
    rw [hId, hIp, ← hNsub]; ring
  have hA : ‖IA‖ ≤ C_K * (M_G / d ^ 2) := hKG.2
  have hB : ‖IB‖ ≤ 2 * Cl * C_E * C_I * B0579.jb y / d ^ 2 * I₁ := by
    refine (norm_integral_le_of_norm_le hgB.integrableOn
      ((ae_restrict_iff' hNm).2 (Eventually.of_forall fun x hx => hBpt x hx))).trans ?_
    refine (setIntegral_le_integral hgB (Eventually.of_forall fun x =>
      mul_nonneg (by positivity) (hg₁0 x))).trans (le_of_eq ?_)
    rw [integral_const_mul]
  have hC : ‖IC‖ ≤ 75 * Cl * C_E / d ^ 3 * I₁ := by
    refine (norm_integral_le_of_norm_le hgC.integrableOn
      ((ae_restrict_iff' hNm.compl).2 (Eventually.of_forall fun x hx => hCpt x hx))).trans ?_
    refine (setIntegral_le_integral hgC (Eventually.of_forall fun x =>
      mul_nonneg (by positivity) (hg₁0 x))).trans (le_of_eq ?_)
    rw [integral_const_mul]
  rw [htot]
  have hsum : ‖IA + IB - IC‖ ≤ ‖IA‖ + ‖IB‖ + ‖IC‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  refine hsum.trans ?_
  set P : ℝ := (B₀ + Cl + C₁) * C_E with hP
  have hP0 : 0 ≤ P := by positivity
  have hClCE : Cl * C_E ≤ P := by rw [hP]; nlinarith [mul_nonneg hB₀ hCE, mul_nonneg hC₁ hCE]
  have hMGle : M_G ≤ 410402 * P := by
    rw [hMG, hP]; nlinarith [mul_nonneg hB₀ hCE, mul_nonneg hCl hCE, mul_nonneg hC₁ hCE]
  have hjP : P ≤ P * B0579.jb y := le_mul_of_one_le_right hP0 hjby
  have e1 : C_K * (M_G / d ^ 2) ≤ C_K * 410402 * P * B0579.jb y / d ^ 2 := by
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hd2.le
    calc C_K * M_G ≤ C_K * (410402 * P) := mul_le_mul_of_nonneg_left hMGle hCK0
      _ ≤ C_K * (410402 * (P * B0579.jb y)) := by gcongr
      _ = C_K * 410402 * P * B0579.jb y := by ring
  have e2 : 2 * Cl * C_E * C_I * B0579.jb y / d ^ 2 * I₁ ≤
      2 * C_I * I₁ * P * B0579.jb y / d ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd2.le
    have h2 : 0 ≤ 2 * C_I * I₁ * B0579.jb y := by positivity
    calc 2 * Cl * C_E * C_I * B0579.jb y * I₁ = (Cl * C_E) * (2 * C_I * I₁ * B0579.jb y) := by ring
      _ ≤ P * (2 * C_I * I₁ * B0579.jb y) := mul_le_mul_of_nonneg_right hClCE h2
      _ = 2 * C_I * I₁ * P * B0579.jb y := by ring
  have e3 : 75 * Cl * C_E / d ^ 3 * I₁ ≤ 75 * I₁ * P * B0579.jb y / d ^ 2 := by
    have hd3 : d ^ 2 ≤ d ^ 3 := by nlinarith
    have h0 : 0 ≤ 75 * Cl * C_E * I₁ := by positivity
    calc 75 * Cl * C_E / d ^ 3 * I₁ = 75 * Cl * C_E * I₁ / d ^ 3 := by ring
      _ ≤ 75 * Cl * C_E * I₁ / d ^ 2 := div_le_div_of_nonneg_left h0 hd2 hd3
      _ ≤ 75 * I₁ * P * B0579.jb y / d ^ 2 := by
          apply div_le_div_of_nonneg_right _ hd2.le
          have h3 : 0 ≤ 75 * I₁ := by positivity
          calc 75 * Cl * C_E * I₁ = (75 * I₁) * (Cl * C_E) := by ring
            _ ≤ (75 * I₁) * (P * B0579.jb y) := mul_le_mul_of_nonneg_left (hClCE.trans hjP) h3
            _ = 75 * I₁ * P * B0579.jb y := by ring
  have hfin : C_K * 410402 * P * B0579.jb y / d ^ 2 + 2 * C_I * I₁ * P * B0579.jb y / d ^ 2 +
      75 * I₁ * P * B0579.jb y / d ^ 2 =
      (C_K * 410402 + 2 * C_I * I₁ + 75 * I₁) * P * B0579.jb y / d ^ 2 := by ring
  linarith [hA.trans e1, hB.trans e2, hC.trans e3]

/-- **Comparison of the localized interactions** (SP 2876-2889), for `|y| ≤ d/8`. -/
theorem kernel_near : ∃ K : ℝ, 0 ≤ K ∧ ∀ (d B₀ Cl C₁ C_E : ℝ), 1 ≤ d → 0 ≤ B₀ → 0 ≤ Cl →
    0 ≤ C₁ → 0 ≤ C_E → ∀ (Φ lamF : ℝ × ℝ → ℂ) (E E0 : ℝ × ℝ → ℝ), Continuous Φ →
    Continuous lamF →
    (∀ x ∈ B0579.cell d, ‖Φ x‖ ≤ B₀) → (∀ x, ‖lamF x‖ ≤ Cl) →
    (∀ x ∈ B0579.cell d, ‖Φ x - lamF x‖ ≤ C₁ / d ^ 2) →
    (∀ (l : Fin 2) (x : ℝ × ℝ),
      |B0579.pd l E0 x| ≤ C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) →
    (∀ (l : Fin 2), ∀ x ∈ B0579.cell d,
      B0579.jb x ^ 2 * |B0579.pd l E x - B0579.pd l E0 x| ≤ C_E / d ^ 2) →
    (∀ (l : Fin 2), ∀ x ∈ B0579.cell d, B0579.jb x ^ 2 * |B0579.pd l E x| ≤ C_E) →
    ∀ y : ℝ × ℝ, ‖planeToC y‖ ≤ d / 8 →
      ‖kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y -
        kerAdjPl (fun l x => lamF x * ((B0579.pd l E0 x : ℝ) : ℂ)) y‖ ≤
        K * ((B₀ + Cl + C₁) * C_E) * B0579.jb y / d ^ 2 := by
  obtain ⟨K, hK0, hcomp⟩ := kernel_near_comp
  refine ⟨2 * K, by positivity, ?_⟩
  intro d B₀ Cl C₁ C_E hd hB₀ hCl hC₁ hCE Φ lamF E E0 hΦc hlc hΦ hl hΦl hE0 hEE0 hE y hy
  have key := fun l : Fin 2 => hcomp d B₀ Cl C₁ C_E hd hB₀ hCl hC₁ hCE Φ lamF E E0 hΦc hlc hΦ hl
    hΦl l (hE0 l) (hEE0 l) (hE l) y hy
  have hsplitd : kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y =
      ∑ l : Fin 2, ∫ x in B0579.cell d, Φ x * ((B0579.pd l E x : ℝ) : ℂ) *
        ((kerD d (x - y) l : ℝ) : ℂ) := by
    unfold kerAdj
    exact integral_finsetSum _ (fun l _ => (key l).1)
  have hsplitp : kerAdjPl (fun l x => lamF x * ((B0579.pd l E0 x : ℝ) : ℂ)) y =
      ∑ l : Fin 2, ∫ x, lamF x * ((B0579.pd l E0 x : ℝ) : ℂ) * ((kerPl (x - y) l : ℝ) : ℂ) := by
    unfold kerAdjPl
    exact integral_finsetSum _ (fun l _ => (key l).2.1)
  rw [hsplitd, hsplitp, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_two]
  have h0 := (key 0).2.2
  have h1 := (key 1).2.2
  have : 2 * K * ((B₀ + Cl + C₁) * C_E) * B0579.jb y / d ^ 2 =
      K * ((B₀ + Cl + C₁) * C_E) * B0579.jb y / d ^ 2 +
        K * ((B₀ + Cl + C₁) * C_E) * B0579.jb y / d ^ 2 := by ring
  rw [this]
  exact add_le_add h0 h1

end EulerSubCore

end UnforcedLeray.Short.IIIa
