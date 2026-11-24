import UnforcedLeray.Lib.HeatR3.Similarity
import UnforcedLeray.Lib.HeatR3.FTC
import UnforcedLeray.Lib.HeatR3.Joint
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# The profile equation of the similarity heat profile (INF04 T10, `simHeat_equation`)


item `simHeat_equation`. Unit B0697 (tex 5923–5934, "`H_a` ... solves `A_0 H_a = 0`") and the
profile of `loc:eq:dss` (tex 150–163): for `u ∈ 𝒦₂(C)` (the class `InvDistClass 2 C`) and `h > 0`,
`H(τ, y) = e^{τ/2}[e^{h e^τ Δ}u](e^{τ/2} y)` satisfies

`∂_τ H = h ΔH + ½ (y·∇)H + ½ H`.

Route.
1. `InvDistClass.hasDerivAt_average_time`: the heat equation `∂_t e^{tΔ}u = Δ e^{tΔ}u`, `t > 0`,
   for singular data of the class: near `t₀` write `e^{tΔ}u = e^{(t - t₀/2)Δ}w` with
   `w = e^{(t₀/2)Δ}u ∈ C²_b` (`InvDistClass.heat_decay`) and use the `C²_b` heat equation
   (`hasDerivAt_average_time`, `vlap_average`).
2. `continuousAt_vlap_joint`, `continuousAt_fderiv_joint`: the same representation and the joint
   continuity of the heat flow of bounded continuous data (`continuousOn_average_joint`).
3. `hasStrictFDerivAt_average_joint`: Mathlib's `hasStrictFDerivAt_uncurry_coprod` (continuous
   partial derivatives) gives the joint derivative of `(t, x) ↦ e^{tΔ}u(x)` on `(0, ∞) × ℝ³`.
4. `simHeat_equation`: the chain rule along `τ ↦ (h e^τ, e^{τ/2} y)` and the scaling of the
   spatial derivatives of `y ↦ e^{τ/2} F(e^{τ/2} y)`.

Hypothesis: `InvDistClass 2 C u` (bounds up to order 2; the manuscript's datum has order 4,
tex 152–156).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Bounded derivatives at positive times -/

/-- For `u ∈ 𝒦₂(C)` and `t > 0`, the derivatives of order `≤ 2` of `e^{tΔ}u` are bounded. -/
theorem InvDistClass.bdd_average {C : ℝ} {u : Space → E} (hu : InvDistClass 2 C u) {t : ℝ}
    (ht : 0 < t) : ∃ M : ℝ, ∀ k ≤ 2, ∀ x : Space, ‖iteratedFDeriv ℝ k (average t u) x‖ ≤ M := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have key : ∀ (j : ℕ) (K : ℝ), (∀ x : Space, ‖iteratedFDeriv ℝ j (average t u) x‖ ≤
      K * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ))) →
      ∀ x : Space, ‖iteratedFDeriv ℝ j (average t u) x‖ ≤
        |K| * Real.sqrt t ^ (-((1 + j : ℕ) : ℝ)) := by
    intro j K hK x
    refine (hK x).trans ?_
    have hn : -((1 + j : ℕ) : ℝ) ≤ 0 := by
      have : (0 : ℝ) ≤ ((1 + j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h1 : (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ)) ≤
        Real.sqrt t ^ (-((1 + j : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hs (by linarith [norm_nonneg x]) hn
    calc K * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ))
        ≤ |K| * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (by positivity) _)
      _ ≤ |K| * Real.sqrt t ^ (-((1 + j : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
  obtain ⟨K0, hK0⟩ := InvDistClass.heat_decay (E := E) C (j := 0) (by norm_num)
  obtain ⟨K1, hK1⟩ := InvDistClass.heat_decay (E := E) C (j := 1) (by norm_num)
  obtain ⟨K2, hK2⟩ := InvDistClass.heat_decay (E := E) C (j := 2) (by norm_num)
  have b0 := key 0 K0 (hK0 u hu t ht)
  have b1 := key 1 K1 (hK1 u hu t ht)
  have b2 := key 2 K2 (hK2 u hu t ht)
  refine ⟨max (max (|K0| * Real.sqrt t ^ (-((1 + 0 : ℕ) : ℝ)))
    (|K1| * Real.sqrt t ^ (-((1 + 1 : ℕ) : ℝ)))) (|K2| * Real.sqrt t ^ (-((1 + 2 : ℕ) : ℝ))),
    fun k hk x => ?_⟩
  interval_cases k
  · exact (b0 x).trans (le_max_of_le_left (le_max_left _ _))
  · exact (b1 x).trans (le_max_of_le_left (le_max_right _ _))
  · exact (b2 x).trans (le_max_right _ _)

/-- `e^{sΔ}u = e^{(s - t₀/2)Δ}(e^{(t₀/2)Δ}u)` for `s > t₀/2` (semigroup law). -/
theorem InvDistClass.average_eq_shift {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u)
    {t₀ s : ℝ} (ht₀ : 0 < t₀) (hs : t₀ / 2 < s) :
    average s u = average (s - t₀ / 2) (average (t₀ / 2) u) := by
  have h := average_add_time' hu.heatAdmissible (sub_pos.mpr hs) (half_pos ht₀)
  rwa [sub_add_cancel] at h

theorem contDiff_two_average {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u) {t : ℝ}
    (ht : 0 < t) : ContDiff ℝ 2 (average t u) :=
  by exact_mod_cast contDiff_infty.mp (contDiff_average hu.heatAdmissible ht) 2

/-! ### The heat equation for singular data -/

/-- **The heat equation for `𝒦₂` data.** For `u ∈ 𝒦₂(C)`, `t > 0` and every `x`:
`∂_t e^{tΔ}u(x) = Δ(e^{tΔ}u)(x)` (tex 5923–5934, B0697). -/
theorem InvDistClass.hasDerivAt_average_time {C : ℝ} {u : Space → E} (hu : InvDistClass 2 C u)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s => average s u x) (vlap (average t u) x) t := by
  have ht2 : 0 < t / 2 := half_pos ht
  obtain ⟨M, hM⟩ := hu.bdd_average ht2
  have hwc : ContDiff ℝ 2 (average (t / 2) u) := contDiff_two_average hu ht2
  have h1 := UnforcedLeray.Heat.hasDerivAt_average_time hwc hM ht2 x
  have h2 : HasDerivAt (fun s => average (s - t / 2) (average (t / 2) u) x)
      (average (t / 2) (vlap (average (t / 2) u)) x) t := by
    have h1' : HasDerivAt (fun r => average r (average (t / 2) u) x)
        (average (t / 2) (vlap (average (t / 2) u)) x) (t - t / 2) := by
      rwa [show t - t / 2 = t / 2 by ring]
    exact h1'.comp_sub_const t (t / 2)
  have heq : (fun s => average (s - t / 2) (average (t / 2) u) x) =ᶠ[𝓝 t]
      fun s => average s u x := by
    filter_upwards [lt_mem_nhds (half_lt_self ht)] with s hs
    rw [hu.average_eq_shift ht hs]
  have hv : vlap (average t u) x = average (t / 2) (vlap (average (t / 2) u)) x := by
    rw [hu.average_eq_shift ht (half_lt_self ht), show t - t / 2 = t / 2 by ring]
    exact vlap_average ht2 hwc hM x
  rw [hv]
  exact h2.congr_of_eventuallyEq heq.symm

/-! ### Joint continuity of the partial derivatives -/

theorem continuous_vlap {w : Space → E} (hw : ContDiff ℝ 2 w) : Continuous (vlap w) := by
  unfold vlap
  exact continuous_finsetSum _ fun i _ =>
    (continuous_eval_const _).comp (hw.continuous_iteratedFDeriv le_rfl)

/-- Heat flow of bounded continuous data is admissible. -/
theorem heatAdmissible_of_bound {g : Space → E} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) : HeatAdmissible g :=
  HeatAdmissible.of_memLp le_top
    (memLp_top_of_bound hg.aestronglyMeasurable M (Eventually.of_forall hM))

/-- Joint continuity at `(t₀, x₀)` of `e^{(t - t₀/2)Δ}g(x)` for bounded continuous `g`. -/
theorem continuousAt_average_shift {g : Space → E} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : Space) :
    ContinuousAt (fun z : ℝ × Space => average (z.1 - t₀ / 2) g z.2) (t₀, x₀) := by
  have hj := continuousOn_average_joint (heatAdmissible_of_bound hg hM)
  have hjat : ContinuousAt (fun z : ℝ × Space => average z.1 g z.2) (t₀ - t₀ / 2, x₀) :=
    hj.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      ⟨by simp only [mem_Ioi]; linarith, mem_univ _⟩)
  have hm : ContinuousAt (fun z : ℝ × Space => (z.1 - t₀ / 2, z.2)) (t₀, x₀) := by fun_prop
  exact ContinuousAt.comp_of_eq (g := fun z : ℝ × Space => average z.1 g z.2)
    (f := fun z : ℝ × Space => (z.1 - t₀ / 2, z.2)) hjat hm rfl

/-- `(t, x) ↦ Δ(e^{tΔ}u)(x)` is continuous at every `(t₀, x₀)`, `t₀ > 0`, for `u ∈ 𝒦₂(C)`. -/
theorem InvDistClass.continuousAt_vlap_joint {C : ℝ} {u : Space → E} (hu : InvDistClass 2 C u)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : Space) :
    ContinuousAt (fun z : ℝ × Space => vlap (average z.1 u) z.2) (t₀, x₀) := by
  have ht2 : 0 < t₀ / 2 := half_pos ht₀
  obtain ⟨M, hM⟩ := hu.bdd_average ht2
  have hwc : ContDiff ℝ 2 (average (t₀ / 2) u) := contDiff_two_average hu ht2
  have hc := continuousAt_average_shift (continuous_vlap hwc)
    (fun x => norm_vlap_le (hM 2 le_rfl) x) ht₀ x₀
  refine hc.congr ?_
  filter_upwards [(continuous_fst.tendsto (t₀, x₀)).eventually (lt_mem_nhds (half_lt_self ht₀))]
    with z hz
  rw [hu.average_eq_shift ht₀ hz]
  exact (vlap_average (sub_pos.mpr hz) hwc hM z.2).symm

/-- `(t, x) ↦ D(e^{tΔ}u)(x)` is continuous at every `(t₀, x₀)`, `t₀ > 0`, for `u ∈ 𝒦₂(C)`. -/
theorem InvDistClass.continuousAt_fderiv_joint {C : ℝ} {u : Space → E}
    (hu : InvDistClass 2 C u) {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : Space) :
    ContinuousAt (fun z : ℝ × Space => fderiv ℝ (average z.1 u) z.2) (t₀, x₀) := by
  have ht2 : 0 < t₀ / 2 := half_pos ht₀
  obtain ⟨M, hM⟩ := hu.bdd_average ht2
  have hwc : ContDiff ℝ 2 (average (t₀ / 2) u) := contDiff_two_average hu ht2
  have hw1 : ContDiff ℝ 1 (average (t₀ / 2) u) := hwc.of_le (by norm_num)
  have hb0 : ∀ x, ‖average (t₀ / 2) u x‖ ≤ M := fun x => by
    simpa only [norm_iteratedFDeriv_zero] using hM 0 (by norm_num) x
  have hb1 : ∀ x, ‖fderiv ℝ (average (t₀ / 2) u) x‖ ≤ M := fun x => by
    simpa only [norm_iteratedFDeriv_one] using hM 1 (by norm_num) x
  have hc := continuousAt_average_shift (hw1.continuous_fderiv one_ne_zero) hb1 ht₀ x₀
  refine hc.congr ?_
  filter_upwards [(continuous_fst.tendsto (t₀, x₀)).eventually (lt_mem_nhds (half_lt_self ht₀))]
    with z hz
  rw [hu.average_eq_shift ht₀ hz, fderiv_average (sub_pos.mpr hz) hw1 hb0 hb1]

/-- **Joint differentiability of the heat flow of `𝒦₂` data.** On `(0, ∞) × ℝ³`,
`(t, x) ↦ e^{tΔ}u(x)` is strictly differentiable with derivative
`(s, v) ↦ s Δ(e^{tΔ}u)(x) + D(e^{tΔ}u)(x) v`. -/
theorem InvDistClass.hasStrictFDerivAt_average_joint {C : ℝ} {u : Space → E}
    (hu : InvDistClass 2 C u) {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : Space) :
    HasStrictFDerivAt (fun z : ℝ × Space => average z.1 u z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (vlap (average t₀ u) x₀)).coprod
        (fderiv ℝ (average t₀ u) x₀)) (t₀, x₀) := by
  have hpos : ∀ᶠ z : ℝ × Space in 𝓝 (t₀, x₀), 0 < z.1 :=
    (continuous_fst.tendsto (t₀, x₀)).eventually (lt_mem_nhds ht₀)
  refine hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (t₀, x₀))
    (f := fun t x => average t u x)
    (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (vlap (average t u) x))
    (f₂ := fun t x => fderiv ℝ (average t u) x) ?_ ?_ ?_ ?_
  · filter_upwards [hpos] with z hz
    exact hasDerivAt_iff_hasFDerivAt.mp (hu.hasDerivAt_average_time hz z.2)
  · filter_upwards [hpos] with z hz
    exact (((contDiff_two_average hu hz).differentiable two_ne_zero) z.2).hasFDerivAt
  · exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.continuousAt.comp
      (hu.continuousAt_vlap_joint ht₀ x₀)
  · exact hu.continuousAt_fderiv_joint ht₀ x₀

/-! ### Spatial derivatives of a rescaled field -/

theorem hasFDerivAt_rescale {F : Space → E} {a : ℝ} {y : Space} (hF : DifferentiableAt ℝ F (a • y)) :
    HasFDerivAt (fun z : Space => a • F (a • z))
      (a • (fderiv ℝ F (a • y)).comp (a • ContinuousLinearMap.id ℝ Space)) y := by
  have hs : HasFDerivAt (fun z : Space => a • z) (a • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul a
  exact (hF.hasFDerivAt.comp y hs).const_smul a

theorem fderiv_rescale_apply {F : Space → E} {a : ℝ} {y : Space}
    (hF : DifferentiableAt ℝ F (a • y)) (v : Space) :
    fderiv ℝ (fun z : Space => a • F (a • z)) y v = (a * a) • fderiv ℝ F (a • y) v := by
  rw [(hasFDerivAt_rescale hF).fderiv]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul]

theorem vlap_rescale (F : Space → E) (a : ℝ) (y : Space) :
    vlap (fun z : Space => a • F (a • z)) y = (a * a ^ 2) • vlap F (a • y) := by
  simp only [vlap, Gaussian.iteratedFDeriv_comp_smul 2 F a a y,
    ContinuousMultilinearMap.smul_apply, Finset.smul_sum]

/-! ### The profile equation -/

/-- **INF04 T10 `simHeat_equation`** (B0697, tex 5923–5934; profile of tex 159–163). For `h > 0`
and `u ∈ 𝒦₂(C)`, the similarity heat profile `H = simHeat h u` solves
`∂_τ H(τ, y) = h ΔH(τ, y) + ½ DH(τ, y) y + ½ H(τ, y)` at every `τ` and `y`. -/
theorem simHeat_equation {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 2 C u) (τ : ℝ) (y : Space) :
    HasDerivAt (fun σ => simHeat h u σ y)
      (h • vlap (simHeat h u τ) y + (1 / 2 : ℝ) • fderiv ℝ (simHeat h u τ) y y +
        (1 / 2 : ℝ) • simHeat h u τ y) τ := by
  set a := Real.exp (τ / 2) with ha
  have hT : 0 < h * Real.exp τ := mul_pos hh (Real.exp_pos τ)
  have hexp : Real.exp τ = a * a := by rw [ha, ← Real.exp_add]; ring_nf
  -- the curve `σ ↦ (h e^σ, e^{σ/2} y)`
  have hhalf : HasDerivAt (fun σ : ℝ => Real.exp (σ / 2)) (a * (1 / 2)) τ := by
    have h1 : HasDerivAt (fun σ : ℝ => σ / 2) (1 / 2) τ := by
      simpa using (hasDerivAt_id τ).div_const 2
    exact (Real.hasDerivAt_exp (τ / 2)).comp τ h1
  have hγ : HasDerivAt (fun σ : ℝ => (h * Real.exp σ, Real.exp (σ / 2) • y))
      (h * Real.exp τ, (a * (1 / 2)) • y) τ :=
    ((Real.hasDerivAt_exp τ).const_mul h).prodMk (hhalf.smul_const y)
  have hA := (hu.hasStrictFDerivAt_average_joint hT (a • y)).hasFDerivAt
  have hcomp := hA.comp_hasDerivAt τ hγ
  have hfull := hhalf.fun_smul hcomp
  have hdiff : DifferentiableAt ℝ (average (h * Real.exp τ) u) (a • y) :=
    ((contDiff_two_average hu hT).differentiable two_ne_zero) _
  have hfun : simHeat h u τ = fun z => a • average (h * Real.exp τ) u (a • z) := rfl
  refine hfull.congr_deriv ?_
  rw [hfun, vlap_rescale, fderiv_rescale_apply hdiff]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    map_smul, smul_add, smul_smul, hexp, Function.comp_apply, ← ha]
  rw [show h * (a * a ^ 2) = a * (h * (a * a)) by ring,
    show (1 / 2 : ℝ) * (a * a) = a * (a * (1 / 2)) by ring,
    show (1 / 2 : ℝ) * a = a * (1 / 2) by ring]

end UnforcedLeray.Heat
