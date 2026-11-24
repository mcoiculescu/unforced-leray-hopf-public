import UnforcedLeray.Lib.CZCore.Decomp
import UnforcedLeray.Lib.CZCore.WeakType
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Weak type `(1,1)` of anisotropic Calderón–Zygmund convolution operators (INF01 T10)


target T10; §4.9 and decision D4 of `scoping/README.md` §3 (one anisotropic CZ core, no maximal
function). This is the weak-type input of the `L^q` bounds of the Leray projection (blueprint
unit B0414, `paper/main.tex` lines 7336–7344, Grafakos Cor. 5.2.8) and of the parabolic
estimate eq:free-stress-11 (unit B0423, lines 7447–7477).

* `IsCZConvolution a T K B`: `T` is a bounded operator on `L²(ℝ^N)`, the kernel `K` is
  measurable, `|K x| ≤ B ρ(x)^{-|a|}` for `x ≠ 0` (no condition at `x = 0`), the Hörmander
  condition `∫_{ρ(x) > 2ρ(y)} |K(x-y) - K(x)| dx ≤ B` holds, and off a compact set containing the
  support of `f`, `T f (x) = ∫ K(x-y) f(y) dy`.
* `lintegral_far_le`: for `u` with mean zero supported in a compact set `S ⊆ {ρ(· - c) ≤ r}`,
  `∫_{ρ(x-c) > 2r} |T u| ≤ B ‖u‖₁` (cancellation plus Hörmander).
* `weak11_of_isCZConvolution` (**T10**): `HasWeakType11 volume T (czConst a ‖T‖₊ B)` with
  `czConst a M B = 4·2^{|a|} M² + 2^{N+|a|} + 4B`. Proof: the Calderón–Zygmund decomposition
  (T9) of a continuous compactly supported `g` at height `t`; Chebyshev in `L²` for the good
  part; the expanded boxes; `lintegral_far_le` for the bad parts; then the density extension
  `hasWeakType11_of_dense` (T6).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {N : ℕ} (a : Fin N → ℕ+)

/-- **T10 (INF01 §5, Level 1).** `T` is an anisotropic Calderón–Zygmund convolution operator
with kernel `K` and constant `B`. The size bound is asked only for `x ≠ 0`. -/
structure IsCZConvolution
    (T : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin N → ℝ)))
    (K : (Fin N → ℝ) → ℝ) (B : ℝ≥0) : Prop where
  measurable : Measurable K
  size : ∀ x, x ≠ 0 → |K x| ≤ B * anisoNorm a x ^ (-(homDim a : ℝ))
  hormander : ∀ y, ∫⁻ x in {x | 2 * anisoNorm a y < anisoNorm a x}, ‖K (x - y) - K x‖ₑ ≤ B
  offSupport : ∀ f : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∀ S : Set (Fin N → ℝ), IsCompact S →
    (∀ᵐ y, y ∉ S → f y = 0) → ∀ᵐ x, x ∉ S → T f x = ∫ y, K (x - y) * f y

/-- The weak `(1,1)` constant `4·2^{|a|} M² + 2^{N+|a|} + 4B`. -/
def czConst (M B : ℝ≥0) : ℝ≥0 := 4 * 2 ^ homDim a * M ^ 2 + 2 ^ (N + homDim a) + 4 * B

variable {a}
variable {T : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin N → ℝ))}
  {K : (Fin N → ℝ) → ℝ} {B : ℝ≥0}

/-- The Hörmander integral over the far region of a ball, after translation. -/
theorem lintegral_far_kernel_le (hT : IsCZConvolution a T K B) {c y : Fin N → ℝ} {r : ℝ}
    (hyr : anisoNorm a (y - c) ≤ r) :
    ∫⁻ x in {x | 2 * r < anisoNorm a (x - c)}, ‖K (x - y) - K (x - c)‖ₑ ≤ B := by
  rw [← lintegral_indicator (measurableSet_anisoFar_sub a c _),
    ← lintegral_add_right_eq_self (μ := volume) _ c]
  have h : ∀ x' : Fin N → ℝ,
      {x | 2 * r < anisoNorm a (x - c)}.indicator (fun x => ‖K (x - y) - K (x - c)‖ₑ) (x' + c) =
        {x' | 2 * r < anisoNorm a x'}.indicator (fun x' => ‖K (x' - (y - c)) - K x'‖ₑ) x' := by
    intro x'
    simp only [indicator, mem_ofPred_eq, add_sub_cancel_right]
    rw [show x' + c - y = x' - (y - c) by abel]
  simp_rw [h]
  rw [lintegral_indicator (measurableSet_lt measurable_const (measurable_anisoNorm a))]
  refine (lintegral_mono_set ?_).trans (hT.hormander (y - c))
  intro x' hx'
  simp only [mem_ofPred_eq] at hx' ⊢
  linarith

/-- **Cancellation estimate.** For `u ∈ L²` with mean zero, integrable, vanishing off a compact
set `S ⊆ {ρ(· - c) ≤ r}`: `∫_{ρ(x-c) > 2r} |T u| ≤ B ‖u‖₁`. -/
theorem lintegral_far_le (hT : IsCZConvolution a T K B) (u : Lp ℝ 2 (volume : Measure (Fin N → ℝ)))
    {c : Fin N → ℝ} {r : ℝ} (hr : 0 < r) {S : Set (Fin N → ℝ)} (hS : IsCompact S)
    (hSr : ∀ y ∈ S, anisoNorm a (y - c) ≤ r) (hsupp : ∀ᵐ y, y ∉ S → u y = 0)
    (hu1 : Integrable (u : (Fin N → ℝ) → ℝ)) (hmean : ∫ y, u y = 0) :
    ∫⁻ x in {x | 2 * r < anisoNorm a (x - c)}, ‖T u x‖ₑ ≤ B * eLpNorm u 1 volume := by
  set A := {x : Fin N → ℝ | 2 * r < anisoNorm a (x - c)} with hAdef
  have hA : MeasurableSet A := measurableSet_anisoFar_sub a c _
  have hum : Measurable (u : (Fin N → ℝ) → ℝ) := (Lp.stronglyMeasurable u).measurable
  have hd : -(homDim a : ℝ) ≤ 0 := by have := (Nat.cast_nonneg (homDim a) : (0 : ℝ) ≤ _); linarith
  have hpt : ∀ᵐ x, x ∈ A → ‖T u x‖ₑ ≤ ∫⁻ y, ‖K (x - y) - K (x - c)‖ₑ * ‖u y‖ₑ := by
    filter_upwards [hT.offSupport u S hS hsupp] with x hx hxA
    have hxA' : 2 * r < anisoNorm a (x - c) := hxA
    have hxS : x ∉ S := fun h => by have := hSr x h; linarith
    rw [hx hxS]
    have hint : Integrable (fun y => K (x - y) * u y) := by
      refine Integrable.mono' (hu1.norm.const_mul (B * r ^ (-(homDim a : ℝ))))
        ((hT.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
          hu1.aestronglyMeasurable) ?_
      filter_upwards [hsupp] with y hy
      by_cases hyS : y ∈ S
      · have hρ : r < anisoNorm a (x - y) := by
          have h1 := anisoNorm_sub_le_sub a (x - c) (y - c)
          have h2 := hSr y hyS
          rw [show x - c - (y - c) = x - y by abel] at h1
          linarith
        have hne : x - y ≠ 0 := fun h => by
          rw [h, anisoNorm_zero] at hρ; linarith
        simp only [norm_mul, Real.norm_eq_abs]
        gcongr
        refine (hT.size _ hne).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hρ.le hd) B.coe_nonneg
      · rw [hy hyS]; simp
    have hsplit : ∫ y, K (x - y) * u y = ∫ y, (K (x - y) - K (x - c)) * u y := by
      have : ∫ y, (K (x - y) - K (x - c)) * u y =
          (∫ y, K (x - y) * u y) - ∫ y, K (x - c) * u y := by
        simp_rw [sub_mul]; exact integral_sub hint (hu1.const_mul (K (x - c)))
      rw [this, integral_const_mul, hmean, mul_zero, sub_zero]
    rw [hsplit]
    calc ‖∫ y, (K (x - y) - K (x - c)) * u y‖ₑ
        ≤ ∫⁻ y, ‖(K (x - y) - K (x - c)) * u y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖K (x - y) - K (x - c)‖ₑ * ‖u y‖ₑ := by simp_rw [enorm_mul]
  have hF : Measurable (Function.uncurry fun x y : Fin N → ℝ =>
      ‖K (x - y) - K (x - c)‖ₑ * ‖u y‖ₑ) := by
    have h1 : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) => K (p.1 - p.2) :=
      hT.measurable.comp (measurable_fst.sub measurable_snd)
    have h2 : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) => K (p.1 - c) :=
      hT.measurable.comp (measurable_fst.sub_const c)
    exact ((h1.sub h2).enorm).mul (hum.comp measurable_snd).enorm
  calc ∫⁻ x in A, ‖T u x‖ₑ
      ≤ ∫⁻ x in A, ∫⁻ y, ‖K (x - y) - K (x - c)‖ₑ * ‖u y‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hpt, ae_restrict_mem hA] with x hx hxA using hx hxA
    _ = ∫⁻ y, ∫⁻ x in A, ‖K (x - y) - K (x - c)‖ₑ * ‖u y‖ₑ :=
        lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ y, B * ‖u y‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsupp] with y hy
        by_cases hyS : y ∈ S
        · have hK' : Measurable fun x : Fin N → ℝ => ‖K (x - y) - K (x - c)‖ₑ :=
            ((hT.measurable.comp (measurable_id.sub_const y)).sub
              (hT.measurable.comp (measurable_id.sub_const c))).enorm
          rw [lintegral_mul_const _ hK']
          gcongr
          exact lintegral_far_kernel_le hT (hSr y hyS)
        · rw [hy hyS]; simp
    _ = B * eLpNorm u 1 volume := by
        rw [lintegral_const_mul _ hum.enorm, eLpNorm_one_eq_lintegral_enorm]

section Aux

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `⇑(Σ F i) = Σ ⇑(F i)` almost everywhere, for a finite sum in `L²`. -/
theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 μ
  | insert i s hi ih =>
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x h1 h2
    rw [Finset.sum_insert hi, h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-- `⇑(T (Σ F i)) = Σ ⇑(T (F i))` almost everywhere, for a finite sum in `L²`. -/
theorem coeFn_map_finset_sum {ι : Type*} (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (s : Finset ι)
    (F : ι → Lp ℝ 2 μ) : ⇑(T (∑ i ∈ s, F i)) =ᵐ[μ] fun x => ∑ i ∈ s, T (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero]; exact Lp.coeFn_zero ℝ 2 μ
  | insert i s hi ih =>
    filter_upwards [Lp.coeFn_add (T (F i)) (T (∑ j ∈ s, F j)), ih] with x h1 h2
    rw [Finset.sum_insert hi, map_add, h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-- `‖h‖₂² ≤ M ‖h‖₁` when `|h| ≤ M`. -/
theorem eLpNorm_two_rpow_two_le {h : α → ℝ} {M : ℝ} (hM : ∀ x, |h x| ≤ M) :
    eLpNorm h 2 μ ^ (2 : ℝ) ≤ ENNReal.ofReal M * eLpNorm h 1 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    ENNReal.rpow_one, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [ENNReal.rpow_two, sq]
  gcongr
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hM x)

/-- Arithmetic of the Chebyshev step: `(τ/2)² m ≤ τ X ⟹ τ m ≤ 4 X`. -/
theorem ennreal_cheb_aux {τ m X : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτ : τ ≠ ⊤)
    (h : (τ / 2) ^ (2 : ℝ) * m ≤ τ * X) : τ * m ≤ 4 * X := by
  have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  have e : (τ / 2) ^ (2 : ℝ) * m = τ * (τ * 2⁻¹ ^ 2 * m) := by
    rw [ENNReal.rpow_two, div_eq_mul_inv]; ring
  rw [e] at h
  have h' := (ENNReal.mul_le_mul_iff_right hτ0 hτ).1 h
  calc τ * m = (2 * 2⁻¹) ^ 2 * (τ * m) := by rw [h2, one_pow, one_mul]
    _ = 4 * (τ * 2⁻¹ ^ 2 * m) := by ring
    _ ≤ 4 * X := by gcongr

end Aux

/-- **T10 (INF01 §5, Level 1).** An anisotropic Calderón–Zygmund convolution operator is of weak
type `(1,1)` with constant `czConst a ‖T‖₊ B = 4·2^{|a|}‖T‖² + 2^{N+|a|} + 4B` (`N ≥ 1`). -/
theorem weak11_of_isCZConvolution [NeZero N] (hT : IsCZConvolution a T K B) :
    HasWeakType11 volume T (czConst a ‖T‖₊ B) := by
  refine hasWeakType11_of_dense fun g hg2 hgc hgs t ht => ?_
  obtain ⟨D⟩ := exists_czDecomp a hgc hgs ht
  set M : ℝ≥0∞ := (‖T‖₊ : ℝ≥0∞) with hMdef
  set L : ℝ≥0∞ := eLpNorm g 1 volume with hLdef
  set τ : ℝ≥0∞ := ENNReal.ofReal t with hτdef
  have hτ0 : τ ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hτ : τ ≠ ⊤ := ENNReal.ofReal_ne_top
  set F : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) := hg2.toLp g with hFdef
  set BQ : ℤ × (Fin N → ℤ) → Lp ℝ 2 (volume : Measure (Fin N → ℝ)) :=
    fun Q => (D.memLp_bad Q 2).toLp (D.bad Q) with hBQdef
  set G : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) := F - ∑ Q ∈ D.boxes, BQ Q with hGdef
  -- almost-everywhere identities
  have hTF : ∀ᵐ x, T F x = T G x + ∑ Q ∈ D.boxes, T (BQ Q) x := by
    have hFG : F = G + ∑ Q ∈ D.boxes, BQ Q := by rw [hGdef, sub_add_cancel]
    filter_upwards [Lp.coeFn_add (T G) (T (∑ Q ∈ D.boxes, BQ Q)),
      coeFn_map_finset_sum T D.boxes BQ] with x hx1 hx2
    rw [hFG, map_add, hx1, Pi.add_apply, hx2]
  have hBQ : ∀ᵐ x, ∀ Q ∈ D.boxes, BQ Q x = D.bad Q x :=
    (Filter.eventually_all_finset D.boxes).2 fun Q _ => (D.memLp_bad Q 2).coeFn_toLp
  have hGgood : (G : (Fin N → ℝ) → ℝ) =ᵐ[volume] D.good := by
    filter_upwards [Lp.coeFn_sub F (∑ Q ∈ D.boxes, BQ Q), hg2.coeFn_toLp,
      coeFn_finset_sum D.boxes BQ, hBQ] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, Finset.sum_congr rfl h4, D.decomp x]
    ring
  -- the good part (Chebyshev in `L²`)
  have hG2 : eLpNorm G 2 volume ^ (2 : ℝ) ≤ ENNReal.ofReal (2 ^ homDim a * t) * L := by
    rw [eLpNorm_congr_ae hGgood]
    exact (eLpNorm_two_rpow_two_le D.abs_good_le).trans (by gcongr; exact D.eLpNorm_good_le)
  have hE1 : τ * volume {x | t / 2 ≤ |T G x|} ≤
      4 * (M ^ 2 * ENNReal.ofReal (2 ^ homDim a) * L) := by
    refine ennreal_cheb_aux hτ0 hτ ?_
    have hcheb := ofReal_rpow_two_mul_meas_le (μ := volume) (Lp.aestronglyMeasurable (T G)) (t / 2)
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat] at hcheb
    calc (τ / 2) ^ (2 : ℝ) * volume {x | t / 2 ≤ |T G x|}
        ≤ eLpNorm (T G) 2 volume ^ (2 : ℝ) := hcheb
      _ ≤ (M * eLpNorm G 2 volume) ^ (2 : ℝ) := by gcongr; exact eLpNorm_apply_le T G
      _ = M ^ 2 * eLpNorm G 2 volume ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two M]
      _ ≤ M ^ 2 * (ENNReal.ofReal (2 ^ homDim a * t) * L) := by gcongr
      _ = τ * (M ^ 2 * ENNReal.ofReal (2 ^ homDim a) * L) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring
  -- the expanded boxes
  set Qs : ℤ × (Fin N → ℤ) → Set (Fin N → ℝ) :=
    fun Q => {x | anisoNorm a (x - dyCenter a Q.1 Q.2) ≤ 2 * dyLen Q.1} with hQsdef
  set Ωs := ⋃ Q ∈ D.boxes, Qs Q with hΩsdef
  have hΩs : MeasurableSet Ωs :=
    D.boxes.measurableSet_biUnion fun Q _ => measurableSet_dyStar a _ _
  have hE2 : τ * volume Ωs ≤ 2 ^ (N + homDim a) * L := by
    calc τ * volume Ωs ≤ τ * ∑ Q ∈ D.boxes, volume (Qs Q) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ = 2 ^ (N + homDim a) * (τ * ∑ Q ∈ D.boxes, volume (dyadicBox a Q.1 Q.2)) := by
          simp only [hQsdef, volume_dyStar]
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 ^ (N + homDim a) * L := by gcongr; exact D.measure_le
  -- the bad parts off the expanded boxes
  set H : (Fin N → ℝ) → ℝ≥0∞ := fun x => ∑ Q ∈ D.boxes, ‖T (BQ Q) x‖ₑ with hHdef
  have hHm : ∀ Q, Measurable fun x => ‖T (BQ Q) x‖ₑ :=
    fun Q => (Lp.stronglyMeasurable _).measurable.enorm
  have hfarQ : ∀ Q ∈ D.boxes,
      ∫⁻ x in Ωsᶜ, ‖T (BQ Q) x‖ₑ ≤ B * eLpNorm (D.bad Q) 1 volume := by
    intro Q hQ
    have hsub : Ωsᶜ ⊆ {x | 2 * dyLen Q.1 < anisoNorm a (x - dyCenter a Q.1 Q.2)} := by
      intro x hx
      by_contra h
      exact hx (mem_biUnion hQ (not_lt.1
        (show ¬ (2 * dyLen Q.1 < anisoNorm a (x - dyCenter a Q.1 Q.2)) from h)))
    have hae := (D.memLp_bad Q 2).coeFn_toLp
    have h1 : Integrable (BQ Q : (Fin N → ℝ) → ℝ) :=
      (memLp_one_iff_integrable.1 (D.memLp_bad Q 1)).congr hae.symm
    have hmean : ∫ y, BQ Q y = 0 := by rw [integral_congr_ae hae]; exact D.integral_bad Q
    have hsupp : ∀ᵐ y, y ∉ dyadicBoxClosed a Q.1 Q.2 → BQ Q y = 0 := by
      filter_upwards [hae] with y hy hyS
      rw [hy]
      exact D.bad_eq_zero Q y fun h => hyS (dyadicBox_subset_closed a _ _ h)
    calc ∫⁻ x in Ωsᶜ, ‖T (BQ Q) x‖ₑ
        ≤ ∫⁻ x in {x | 2 * dyLen Q.1 < anisoNorm a (x - dyCenter a Q.1 Q.2)}, ‖T (BQ Q) x‖ₑ :=
          lintegral_mono_set hsub
      _ ≤ B * eLpNorm (BQ Q) 1 volume :=
          lintegral_far_le hT (BQ Q) (dyLen_pos _) (isCompact_dyadicBoxClosed a _ _)
            (fun y hy => anisoNorm_sub_dyCenter_le a hy) hsupp h1 hmean
      _ = B * eLpNorm (D.bad Q) 1 volume := by rw [eLpNorm_congr_ae hae]
  have hE3 : τ * volume ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ) ≤ 4 * B * L := by
    have hmk := mul_meas_ge_le_lintegral₀ (μ := volume.restrict Ωsᶜ)
      (Finset.measurable_sum D.boxes fun Q _ => hHm Q).aemeasurable (ENNReal.ofReal (t / 2))
    rw [Measure.restrict_apply' hΩs.compl] at hmk
    have hint : ∫⁻ x in Ωsᶜ, H x ≤ B * (2 * L) := by
      rw [hHdef, lintegral_finsetSum _ (fun Q _ => hHm Q)]
      calc ∑ Q ∈ D.boxes, ∫⁻ x in Ωsᶜ, ‖T (BQ Q) x‖ₑ
          ≤ ∑ Q ∈ D.boxes, B * eLpNorm (D.bad Q) 1 volume := Finset.sum_le_sum hfarQ
        _ = B * ∑ Q ∈ D.boxes, eLpNorm (D.bad Q) 1 volume := (Finset.mul_sum _ _ _).symm
        _ ≤ B * (2 * L) := by gcongr; exact D.sum_eLpNorm_bad_le
    have hτ2 : τ = 2 * ENNReal.ofReal (t / 2) := by
      rw [hτdef, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    calc τ * volume ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ)
        = 2 * (ENNReal.ofReal (t / 2) * volume ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ)) := by
          rw [hτ2, mul_assoc]
      _ ≤ 2 * (B * (2 * L)) := mul_le_mul_right (hmk.trans hint) 2
      _ = 4 * B * L := by ring
  -- the level set
  have hcover : ∀ᵐ x, x ∈ {x | t < |T F x|} →
      x ∈ {x | t / 2 ≤ |T G x|} ∪ Ωs ∪ ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ) := by
    filter_upwards [hTF] with x hx hxE
    have hxE' : t < |T F x| := hxE
    by_cases h1 : t / 2 ≤ |T G x|
    · exact Or.inl (Or.inl h1)
    by_cases h2 : x ∈ Ωs
    · exact Or.inl (Or.inr h2)
    refine Or.inr ⟨?_, h2⟩
    push Not at h1
    have htri : |T F x| ≤ |T G x| + ∑ Q ∈ D.boxes, |T (BQ Q) x| := by
      rw [hx]
      exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have hsum : t / 2 ≤ ∑ Q ∈ D.boxes, |T (BQ Q) x| := by linarith
    show ENNReal.ofReal (t / 2) ≤ ∑ Q ∈ D.boxes, ‖T (BQ Q) x‖ₑ
    have hH : ∑ Q ∈ D.boxes, ‖T (BQ Q) x‖ₑ = ENNReal.ofReal (∑ Q ∈ D.boxes, |T (BQ Q) x|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun Q _ => abs_nonneg _)]
      simp_rw [Real.enorm_eq_ofReal_abs]
    rw [hH]
    exact ENNReal.ofReal_le_ofReal hsum
  have hmeas : volume {x | t < |T F x|} ≤ volume {x | t / 2 ≤ |T G x|} + volume Ωs +
      volume ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ) :=
    (measure_mono_ae hcover).trans
      ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
  calc τ * volume {x | t < |T F x|}
      ≤ τ * (volume {x | t / 2 ≤ |T G x|} + volume Ωs +
          volume ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ)) := by gcongr
    _ = τ * volume {x | t / 2 ≤ |T G x|} + τ * volume Ωs +
          τ * volume ({x | ENNReal.ofReal (t / 2) ≤ H x} ∩ Ωsᶜ) := by ring
    _ ≤ 4 * (M ^ 2 * ENNReal.ofReal (2 ^ homDim a) * L) + 2 ^ (N + homDim a) * L +
          4 * B * L := add_le_add (add_le_add hE1 hE2) hE3
    _ = (czConst a ‖T‖₊ B : ℝ≥0∞) * L := by
        rw [czConst, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        push_cast
        ring

end UnforcedLeray.CZ
