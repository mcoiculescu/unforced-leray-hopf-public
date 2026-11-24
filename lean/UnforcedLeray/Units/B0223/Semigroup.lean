import UnforcedLeray.Units.B0223.Dilation
import UnforcedLeray.Lib.Semigroups.Laplace

/-!
# B0223 helper: the outer semigroup `S_ε(t)` and its Laplace resolvent

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3341–3368.

With heat coefficient `h = νε²` (tex line 3346, diffusion `νε²` in `x`, tex line 3266),
`S_ε(t)F(x, τ) = e^{t/2} [e^{h(e^t - 1)Δ} F(·, τ - t)](e^{t/2} x)` (tex lines 3350–3352) is
built as `Sop h t = e^{-t/4} · dilN (e^{t/2}) ∘ heatC (h(e^t - 1)) ∘ transC t` on the periodic
`L²` (`X E P`). This file proves:

* `Sop_rep`: the literal formula of the manuscript, almost everywhere, for `t > 0`, `h > 0`;
* `norm_Sop_le`: `‖S_ε(t)‖ ≤ e^{-t/4}` (tex line 3353);
* `Sop_zero`, `Sop_add`: the semigroup law (`h ≥ 0`, `s, t ≥ 0`);
* `Sop_continuousOn`: strong continuity on `[0, ∞)`;
* `outerSemigroup`: the package as an `Infra.ExpSemigroup` with `M = 1`, `ω = -1/4`
  (`Lib/Semigroups/ExpSemigroup.lean`, INF07 T7.1), whose Laplace transform
  `R(μ) = ∫_0^∞ e^{-μt} S_ε(t) dt` is the resolvent (bypass BP4 of the scoping plan:
  resolvents are Laplace transforms of the explicit semigroups).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0223

variable {P : ℝ} [Fact (0 < P)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **The outer semigroup** `S_ε(t)` of `h Δ_x + x·∇/2 + 1/2 - ∂_τ` with `h = νε²`
(tex lines 3346–3352): `e^{-t/4} dilN (e^{t/2}) e^{h(e^t-1)Δ} transC t`. -/
def Sop (h t : ℝ) : X E P →L[ℂ] X E P :=
  ((Real.exp (-t / 4) : ℝ) : ℂ) •
    ((dilN (Real.exp (t / 2))).comp ((heatC (h * (Real.exp t - 1))).comp
      (transC t).toContinuousLinearMap))

theorem Sop_apply (h t : ℝ) (u : X E P) :
    Sop h t u = ((Real.exp (-t / 4) : ℝ) : ℂ) •
      dilN (Real.exp (t / 2)) (heatC (h * (Real.exp t - 1)) (transC t u)) := rfl

/-- **`‖S_ε(t)‖ ≤ e^{-t/4}`** on `L²(dx dτ)` (tex line 3353), for every `t` and `h`. -/
theorem norm_Sop_le (h t : ℝ) : ‖(Sop h t : X E P →L[ℂ] X E P)‖ ≤ Real.exp (-t / 4) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun u => by
    rw [Sop_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      norm_dilN_apply]
    gcongr
    exact (norm_heatC_apply_le _ _).trans (le_of_eq ((transC t).norm_map u))

theorem Sop_zero (h : ℝ) : (Sop h 0 : X E P →L[ℂ] X E P) = 1 := by
  ext1 u
  rw [Sop_apply]
  change _ = u
  simp only [neg_zero, zero_div, Real.exp_zero, sub_self, mul_zero, Complex.ofReal_one, one_smul]
  rw [transC_zero, heatC_of_nonpos le_rfl, dilN_one]

theorem heatTime_nonneg {h : ℝ} (hh : 0 ≤ h) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ h * (Real.exp t - 1) :=
  mul_nonneg hh (by linarith [Real.add_one_le_exp t])

/-- **The semigroup law** `S_ε(s + t) = S_ε(s) S_ε(t)`, `s, t ≥ 0`, `h ≥ 0`. -/
theorem Sop_add {h : ℝ} (hh : 0 ≤ h) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (Sop h (s + t) : X E P →L[ℂ] X E P) = Sop h s ∘L Sop h t := by
  ext1 u
  have ha : ∀ r : ℝ, 0 < Real.exp (r / 2) := fun r => Real.exp_pos _
  rw [ContinuousLinearMap.comp_apply, Sop_apply, Sop_apply, Sop_apply]
  simp only [map_smul]
  rw [transC_dilN (ha t), ← heatC_transC, ← transC_add, heatC_dilN (ha t),
    ← heatC_add (s := Real.exp (t / 2) ^ 2 * (h * (Real.exp s - 1)))
      (t := h * (Real.exp t - 1)) (by have := heatTime_nonneg hh hs; positivity)
      (heatTime_nonneg hh ht),
    dilN_mul (ha s) (ha t), smul_smul]
  have hsq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]; ring_nf
  have e1 : Real.exp ((s + t) / 2) = Real.exp (s / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : h * (Real.exp (s + t) - 1) =
      Real.exp (t / 2) ^ 2 * (h * (Real.exp s - 1)) + h * (Real.exp t - 1) := by
    rw [hsq, Real.exp_add]; ring
  have e3 : ((Real.exp (-(s + t) / 4) : ℝ) : ℂ) =
      ((Real.exp (-s / 4) : ℝ) : ℂ) * ((Real.exp (-t / 4) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; ring_nf
  rw [e1, e2, e3]

/-- The formula of `S_ε(t)` with any representative `f` of `F`. -/
theorem Sop_rep' {h t : ℝ} (hh : 0 < h) (ht : 0 < t) {u : X E P} {f : PSpace P → E}
    (hf : (u : PSpace P → E) =ᵐ[volume] f) :
    (Sop h t u : PSpace P → E) =ᵐ[volume] fun z => Real.exp (t / 2) •
      Heat.heatConv (ιx P) (h * (Real.exp t - 1))
        (fun w => f (w.1, w.2 - (t : AddCircle P))) (Real.exp (t / 2) • z.1, z.2) := by
  have hθ : 0 < h * (Real.exp t - 1) := mul_pos hh (by linarith [Real.add_one_lt_exp ht.ne'])
  have hs : (fun z => (u : PSpace P → E) (shiftT P t z)) =ᵐ[volume] fun z => f (shiftT P t z) :=
    (mp_shiftT t).quasiMeasurePreserving.ae_eq_comp hf
  have h1 : (heatC (h * (Real.exp t - 1)) (transC t u) : PSpace P → E) =ᵐ[volume]
      Heat.heatConv (ιx P) (h * (Real.exp t - 1)) (fun w => f (w.1, w.2 - (t : AddCircle P))) := by
    refine (heatC_rep hθ _).trans ?_
    refine (Heat.heatConv_congr_ae (ιx P) continuous_ιx.measurable _
      ((coeFn_transC t u).trans hs)).trans ?_
    refine Eventually.of_forall fun z => ?_
    simp only [shiftT_apply]
  have h2 := dilN_ae (Real.exp_pos (t / 2)) h1
  filter_upwards [Lp.coeFn_smul (((Real.exp (-t / 4) : ℝ) : ℂ))
    (dilN (Real.exp (t / 2)) (heatC (h * (Real.exp t - 1)) (transC t u))), h2] with z hz1 hz2
  rw [Sop_apply, hz1, Pi.smul_apply, hz2, Complex.coe_smul, smul_smul, ← Real.exp_mul,
    ← Real.exp_add]
  congr 2
  ring

/-- **The formula of the manuscript** (tex lines 3350–3352): for `h = νε² > 0` and `t > 0`,
`S_ε(t)F(x, τ) = e^{t/2} [e^{h(e^t - 1)Δ} F(·, τ - t)](e^{t/2} x)` almost everywhere, the heat
operator being the Gaussian integral `Heat.heatConv` in the spatial variable. -/
theorem Sop_rep {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (u : X E P) :
    (Sop h t u : PSpace P → E) =ᵐ[volume] fun z => Real.exp (t / 2) •
      Heat.heatConv (ιx P) (h * (Real.exp t - 1))
        (fun w => u (w.1, w.2 - (t : AddCircle P))) (Real.exp (t / 2) • z.1, z.2) :=
  Sop_rep' hh ht EventuallyEq.rfl

/-! ### Strong continuity -/

theorem tendsto_clm_apply {α : Type*} {l : Filter α} {A : α → X E P →L[ℂ] X E P}
    {A0 : X E P →L[ℂ] X E P} {v : α → X E P} {v0 : X E P} (hA : ∀ i, ‖A i‖ ≤ 1)
    (hAv : Tendsto (fun i => A i v0) l (𝓝 (A0 v0))) (hv : Tendsto v l (𝓝 v0)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (A0 v0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hAv hv ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa using hv.add hAv)
  calc ‖A i (v i) - A0 v0‖ = ‖A i (v i - v0) + (A i v0 - A0 v0)‖ := by
        rw [map_sub]; abel_nf
    _ ≤ ‖A i (v i - v0)‖ + ‖A i v0 - A0 v0‖ := norm_add_le _ _
    _ ≤ ‖v i - v0‖ + ‖A i v0 - A0 v0‖ := by
        gcongr
        calc ‖A i (v i - v0)‖ ≤ ‖A i‖ * ‖v i - v0‖ := (A i).le_opNorm _
          _ ≤ 1 * ‖v i - v0‖ := mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)
          _ = ‖v i - v0‖ := one_mul _

/-- `b ↦ dilN b F` is continuous at every `a₀ > 0`. -/
theorem tendsto_dilN_at {a0 : ℝ} (ha0 : 0 < a0) {α : Type*} {l : Filter α} {a : α → ℝ}
    (ha : Tendsto a l (𝓝 a0)) (hpos : ∀ᶠ i in l, 0 < a i) (w : X E P) :
    Tendsto (fun i => dilN (a i) w) l (𝓝 (dilN a0 w)) := by
  have hq : Tendsto (fun i => a i / a0) l (𝓝 1) := by
    simpa [div_self ha0.ne'] using ha.div_const a0
  have h1 := ((dilN a0).continuous.tendsto w).comp ((tendsto_dilN w).comp hq)
  refine h1.congr' ?_
  filter_upwards [hpos] with i hi
  simp only [Function.comp_apply]
  rw [dilN_mul ha0 (div_pos hi ha0), mul_div_cancel₀ _ ha0.ne']

/-- **Strong continuity** of `t ↦ S_ε(t)F` on `[0, ∞)` (`h ≥ 0`). -/
theorem Sop_continuousOn {h : ℝ} (hh : 0 ≤ h) (u : X E P) :
    ContinuousOn (fun t => Sop h t u) (Ici 0) := by
  intro t0 ht0
  have hv : Tendsto (fun t => transC t u) (𝓝[Ici 0] t0) (𝓝 (transC t0 u)) :=
    ((continuous_transC u).tendsto t0).mono_left nhdsWithin_le_nhds
  have hθc : ContinuousWithinAt (fun t : ℝ => h * (Real.exp t - 1)) (Ici 0) t0 :=
    (continuous_const.mul (Real.continuous_exp.sub continuous_const)).continuousWithinAt
  have hmaps : MapsTo (fun t : ℝ => h * (Real.exp t - 1)) (Ici 0) (Ici 0) :=
    fun t ht => heatTime_nonneg hh ht
  have hH : Tendsto (fun t => heatC (h * (Real.exp t - 1)) (transC t0 u)) (𝓝[Ici 0] t0)
      (𝓝 (heatC (h * (Real.exp t0 - 1)) (transC t0 u))) :=
    ContinuousWithinAt.comp (f := fun t : ℝ => h * (Real.exp t - 1))
      (g := fun θ => heatC θ (transC t0 u)) ((heatC_continuousOn (transC t0 u)) _ (hmaps ht0))
      hθc hmaps
  have hw := tendsto_clm_apply (fun t => norm_heatC_le (E := E) (P := P) _) hH hv
  have ha : Tendsto (fun t : ℝ => Real.exp (t / 2)) (𝓝[Ici 0] t0) (𝓝 (Real.exp (t0 / 2))) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).tendsto t0).mono_left
      nhdsWithin_le_nhds
  have hD := tendsto_dilN_at (Real.exp_pos (t0 / 2)) ha
    (Eventually.of_forall fun t => Real.exp_pos (t / 2))
    (heatC (h * (Real.exp t0 - 1)) (transC t0 u))
  have hx := tendsto_clm_apply (fun t => norm_dilN_le (E := E) (P := P) _) hD hw
  have hc : Tendsto (fun t : ℝ => ((Real.exp (-t / 4) : ℝ) : ℂ)) (𝓝[Ici 0] t0)
      (𝓝 ((Real.exp (-t0 / 4) : ℝ) : ℂ)) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_neg.div_const 4))).tendsto t0).mono_left nhdsWithin_le_nhds
  exact hc.smul hx

/-- **`S_ε` as an exponentially bounded strongly continuous semigroup** with `M = 1`,
`ω = -1/4` (`Infra.ExpSemigroup`, INF07 T7.1), for `h = νε² ≥ 0`. -/
def outerSemigroup (h : ℝ) (hh : 0 ≤ h) : Infra.ExpSemigroup (X E P) where
  T := Sop h
  T_zero := Sop_zero h
  T_add _ _ hs ht := Sop_add hh hs ht
  T_cont := Sop_continuousOn hh
  M := 1
  ω := -1 / 4
  M_nonneg := zero_le_one
  T_le t _ := by
    rw [one_mul]
    convert norm_Sop_le h t using 2
    ring

@[simp] theorem outerSemigroup_T (h : ℝ) (hh : 0 ≤ h) :
    (outerSemigroup (E := E) (P := P) h hh).T = Sop h := rfl

@[simp] theorem outerSemigroup_ω (h : ℝ) (hh : 0 ≤ h) :
    (outerSemigroup (E := E) (P := P) h hh).ω = -1 / 4 := rfl

@[simp] theorem outerSemigroup_M (h : ℝ) (hh : 0 ≤ h) :
    (outerSemigroup (E := E) (P := P) h hh).M = 1 := rfl

end UnforcedLeray.B0223
