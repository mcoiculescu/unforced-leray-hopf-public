import UnforcedLeray.Lib.HeatR3.SimEquation
import UnforcedLeray.Lib.HeatR3.SubSelf
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Continuity in phase of the similarity heat profile (INF04 T10)


items `simHeat_continuous_C0` and `simHeat_grad_continuous_L3`, with the Hessian in `L²`
(`simHeat_hessian_continuous_L2`). Units B0710 and B0711 (tex 274–290: "`U_* ∈ C_per(ℝ; C₀)`,
`∇U_* ∈ C_per(ℝ; L³)`", from `|D^j H_h[u_dss]| ≤ C_j⟨y⟩^{-1-j}`, `j ≤ 2`). This is the heat part
of the localization hypothesis `HeatProfileRegularity` (`Loc/L01Coefficient.lean`), which is

the same route (there with the cutoff smoothing of `Units/B0306`; here with
`InvDistClass.heat_decay` of `Lib/HeatR3/HeatDecay`).

Route. `H_h[u](τ) = e^{hΔ}u_τ` with `u_τ = e^{τ/2}u(e^{τ/2}·)` (`simHeat_eq`). For
`u ∈ 𝒦₃(C)` the difference `u_σ - u_τ` lies in `𝒦₂(2C|σ - τ|)` (`InvDistClass.dil_sub`: the
mean value theorem in the phase; the derivative of `r ↦ D^j u_r(x)` at `r = s` is that of the
dilation family of `u_s ∈ 𝒦₃(C)` at `0`, bounded by `(1 + j/2) C |x|^{-1-j}`). The heat decay
estimate is linear in the class constant (`InvDistClass.heat_decay_lin`), so
`|D^j(H(σ) - H(τ))(y)| ≤ L|σ - τ|(1 + |y|)^{-1-j}`, `j ≤ 2`: Lipschitz continuity in `C₀`
(`j = 0`), in `L³` (`j = 1`, `(1 + |y|)^{-2} ∈ L³`) and in `L²` (`j = 2`).

Hypothesis: `InvDistClass 3 C u` (one derivative more than the decay estimate; the manuscript's
datum has `|α| ≤ 4`, tex 152–156). Neither the self-similarity law nor solenoidality is used.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff

instance fact_one_le_three_heatR3 : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### The class: monotonicity, order, scalar multiples -/

theorem InvDistClass.mono {k : ℕ} {C C' : ℝ} {u : Space → E} (hu : InvDistClass k C u)
    (h : C ≤ C') : InvDistClass k C' u where
  smooth := hu.smooth
  bound j hj x hx := (hu.bound j hj x hx).trans
    (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (norm_nonneg x) _))

theorem InvDistClass.of_le {k k' : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k' C u)
    (h : k ≤ k') : InvDistClass k C u where
  smooth := hu.smooth.of_le (by exact_mod_cast h)
  bound j hj x hx := hu.bound j (hj.trans h) x hx

theorem InvDistClass.contDiffAt {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u)
    {x : Space} (hx : x ≠ 0) : ContDiffAt ℝ k u x :=
  hu.smooth.contDiffAt (isOpen_compl_singleton.mem_nhds hx)

theorem InvDistClass.smul {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u) (a : ℝ) :
    InvDistClass k (|a| * C) (a • u) where
  smooth := hu.smooth.const_smul a
  bound j hj x hx := by
    rw [iteratedFDeriv_const_smul_apply ((hu.contDiffAt hx).of_le (by exact_mod_cast hj)),
      norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu.bound j hj x hx) (abs_nonneg a)

/-! ### The dilation family `u_τ = e^{τ/2}u(e^{τ/2}·)` -/

/-- The rescaled datum `u_τ(x) = e^{τ/2}u(e^{τ/2}x)` (tex 5923–5934). -/
def simDil (τ : ℝ) (u : Space → E) : Space → E :=
  fun x => Real.exp (τ / 2) • u (Real.exp (τ / 2) • x)

theorem simDil_add (s r : ℝ) (u : Space → E) : simDil (s + r) u = simDil r (simDil s u) := by
  funext x
  simp only [simDil, smul_smul, ← Real.exp_add]
  rw [show r / 2 + s / 2 = (s + r) / 2 by ring, show s / 2 + r / 2 = (s + r) / 2 by ring]

theorem InvDistClass.simDilClass {k : ℕ} {C : ℝ} {u : Space → E} (hu : InvDistClass k C u) (τ : ℝ) :
    InvDistClass k C (simDil τ u) :=
  hu.dilate (Real.exp_pos (τ / 2))

/-- The phase derivative of `r ↦ D^j u_r(x)` at `r = 0` is bounded by `2C|x|^{-1-j}`,
`j ≤ 2`, for `u ∈ 𝒦₃(C)`. -/
theorem InvDistClass.hasDerivAt_dil_zero {C : ℝ} {v : Space → E} (hv : InvDistClass 3 C v)
    {j : ℕ} (hj : j ≤ 2) {x : Space} (hx : x ≠ 0) :
    ∃ D, HasDerivAt (fun r => iteratedFDeriv ℝ j (simDil r v) x) D 0 ∧
      ‖D‖ ≤ 2 * C * ‖x‖ ^ (-(1 + j : ℝ)) := by
  have hC : 0 ≤ C := hv.const_nonneg'
  have hc0 : Real.exp ((0 : ℝ) / 2) = 1 := by simp
  have hhalf : HasDerivAt (fun r : ℝ => Real.exp (r / 2)) (1 / 2) 0 := by
    have h1 : HasDerivAt (fun σ : ℝ => σ / 2) (1 / 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
    have h2 := (Real.hasDerivAt_exp ((0 : ℝ) / 2)).comp (0 : ℝ) h1
    rwa [hc0, one_mul] at h2
  have hc : HasDerivAt (fun r : ℝ => Real.exp (r / 2) * Real.exp (r / 2) ^ j)
      ((1 + j : ℝ) / 2) 0 := by
    have h := hhalf.mul (hhalf.pow j)
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply, hc0, one_pow, one_mul, mul_one]
    ring
  have hca : ContDiffAt ℝ 3 v x := hv.contDiffAt hx
  have hdj : DifferentiableAt ℝ (iteratedFDeriv ℝ j v) x :=
    (hca.iteratedFDeriv_right (m := 1) (i := j) (by exact_mod_cast (by omega : 1 + j ≤ 3))).differentiableAt
      one_ne_zero
  have hψ : HasDerivAt (fun r : ℝ => iteratedFDeriv ℝ j v (Real.exp (r / 2) • x))
      (fderiv ℝ (iteratedFDeriv ℝ j v) x ((1 / 2 : ℝ) • x)) 0 := by
    have hg : HasDerivAt (fun r : ℝ => Real.exp (r / 2) • x) ((1 / 2 : ℝ) • x) 0 :=
      hhalf.smul_const x
    have hF : HasFDerivAt (iteratedFDeriv ℝ j v) (fderiv ℝ (iteratedFDeriv ℝ j v) x)
        (Real.exp ((0 : ℝ) / 2) • x) := by
      rw [hc0, one_smul]; exact hdj.hasFDerivAt
    exact hF.comp_hasDerivAt (0 : ℝ) hg
  refine ⟨fderiv ℝ (iteratedFDeriv ℝ j v) x ((1 / 2 : ℝ) • x) +
    ((1 + j : ℝ) / 2) • iteratedFDeriv ℝ j v x, ?_, ?_⟩
  · have h := hc.fun_smul hψ
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)).congr_deriv ?_
    · exact Gaussian.iteratedFDeriv_comp_smul j v _ _ x
    · simp only [hc0, one_pow, mul_one, one_smul]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hb1 : ‖fderiv ℝ (iteratedFDeriv ℝ j v) x‖ ≤ C * ‖x‖ ^ (-(1 + (j + 1 : ℕ) : ℝ)) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hv.bound (j + 1) (by omega) x hx
    have hb0 : ‖iteratedFDeriv ℝ j v x‖ ≤ C * ‖x‖ ^ (-(1 + j : ℝ)) :=
      hv.bound j (by omega) x hx
    have hpow : ‖x‖ ^ (-(1 + (j + 1 : ℕ) : ℝ)) * ‖x‖ = ‖x‖ ^ (-(1 + j : ℝ)) := by
      rw [← Real.rpow_add_one hx0.ne']
      congr 1
      push_cast
      ring
    have hjr : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have hX : 0 ≤ C * ‖x‖ ^ (-(1 + j : ℝ)) := mul_nonneg hC (Real.rpow_nonneg hx0.le _)
    calc ‖fderiv ℝ (iteratedFDeriv ℝ j v) x ((1 / 2 : ℝ) • x) +
          ((1 + j : ℝ) / 2) • iteratedFDeriv ℝ j v x‖
        ≤ ‖fderiv ℝ (iteratedFDeriv ℝ j v) x‖ * ‖(1 / 2 : ℝ) • x‖ +
            ‖((1 + j : ℝ) / 2)‖ * ‖iteratedFDeriv ℝ j v x‖ :=
          (norm_add_le _ _).trans (add_le_add ((fderiv ℝ _ x).le_opNorm _) (norm_smul _ _).le)
      _ ≤ C * ‖x‖ ^ (-(1 + (j + 1 : ℕ) : ℝ)) * ((1 / 2) * ‖x‖) +
            ((1 + j : ℝ) / 2) * (C * ‖x‖ ^ (-(1 + j : ℝ))) := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
            Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + j : ℝ) / 2)]
          gcongr
      _ = ((2 + j : ℝ) / 2) * (C * ‖x‖ ^ (-(1 + j : ℝ))) := by
          rw [show C * ‖x‖ ^ (-(1 + (j + 1 : ℕ) : ℝ)) * ((1 / 2) * ‖x‖) =
            (1 / 2) * C * (‖x‖ ^ (-(1 + (j + 1 : ℕ) : ℝ)) * ‖x‖) by ring, hpow]
          ring
      _ ≤ 2 * (C * ‖x‖ ^ (-(1 + j : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
      _ = 2 * C * ‖x‖ ^ (-(1 + j : ℝ)) := by ring

/-- **Phase differences of the dilation family.** For `u ∈ 𝒦₃(C)` and all phases `σ, τ`:
`u_σ - u_τ ∈ 𝒦₂(2C|σ - τ|)`. -/
theorem InvDistClass.dil_sub {C : ℝ} {u : Space → E} (hu : InvDistClass 3 C u) (σ τ : ℝ) :
    InvDistClass 2 (2 * C * |σ - τ|) (simDil σ u - simDil τ u) where
  smooth := ((hu.simDilClass σ).smooth.sub (hu.simDilClass τ).smooth).of_le (by norm_num)
  bound j hj x hx := by
    have hcda : ∀ s, ContDiffAt ℝ j (simDil s u) x := fun s =>
      ((hu.simDilClass s).contDiffAt hx).of_le (by exact_mod_cast (by omega : j ≤ 3))
    rw [iteratedFDeriv_sub_apply (hcda σ) (hcda τ)]
    have key : ∀ s, ∃ D, HasDerivAt (fun r => iteratedFDeriv ℝ j (simDil r u) x) D s ∧
        ‖D‖ ≤ 2 * C * ‖x‖ ^ (-(1 + j : ℝ)) := by
      intro s
      have hus : InvDistClass 3 C (simDil s u) := hu.simDilClass s
      obtain ⟨D, hD, hDb⟩ := hus.hasDerivAt_dil_zero hj hx
      refine ⟨D, ?_, hDb⟩
      have h0 : HasDerivAt (fun r => iteratedFDeriv ℝ j (simDil r (simDil s u)) x) D (s - s) := by
        rwa [sub_self]
      refine (h0.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
      simp only
      rw [← simDil_add, add_sub_cancel]
    choose D hD hDb using key
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => iteratedFDeriv ℝ j (simDil r u) x) (fun s _ => (hD s).hasDerivWithinAt)
      (fun s _ => hDb s) (mem_univ τ) (mem_univ σ)
    rw [Real.norm_eq_abs] at h
    calc ‖iteratedFDeriv ℝ j (simDil σ u) x - iteratedFDeriv ℝ j (simDil τ u) x‖
        ≤ 2 * C * ‖x‖ ^ (-(1 + j : ℝ)) * |σ - τ| := h
      _ = 2 * C * |σ - τ| * ‖x‖ ^ (-(1 + j : ℝ)) := by ring

/-! ### The heat decay estimate is linear in the class constant -/

/-- `|D^j e^{tΔ}v(x)| ≤ c K (|x| + √t)^{-1-j}` for `v ∈ 𝒦₂(c)`, `c > 0`, with `K = K(j)`. -/
theorem InvDistClass.heat_decay_lin {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 < c → ∀ v : Space → E, InvDistClass 2 c v → ∀ t : ℝ, 0 < t →
      ∀ x : Space, ‖iteratedFDeriv ℝ j (average t v) x‖ ≤
        c * K * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := InvDistClass.heat_decay (E := E) 1 hj
  refine ⟨|K|, abs_nonneg K, fun c hc v hv t ht x => ?_⟩
  have hv1 : InvDistClass 2 1 (c⁻¹ • v) := by
    refine (hv.smul c⁻¹).mono (le_of_eq ?_)
    rw [abs_of_pos (inv_pos.mpr hc), inv_mul_cancel₀ hc.ne']
  have hvrep : v = c • (c⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have havg : average t v = c • average t (c⁻¹ • v) := by
    conv_lhs => rw [hvrep]
    exact average_smul t c _
  have hcd : ContDiffAt ℝ j (average t (c⁻¹ • v)) x :=
    ((contDiff_average hv1.heatAdmissible ht).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [havg, iteratedFDeriv_const_smul_apply hcd, norm_smul, Real.norm_of_nonneg hc.le]
  have h1 := hK _ hv1 t ht x
  have hw : 0 ≤ (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  calc c * ‖iteratedFDeriv ℝ j (average t (c⁻¹ • v)) x‖
      ≤ c * (|K| * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hw)) hc.le
    _ = c * |K| * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ)) := by ring

theorem weight_sqrt_le {h : ℝ} (hh : 0 < h) (n : ℕ) (y : Space) :
    (‖y‖ + Real.sqrt h) ^ (-(n : ℝ)) ≤
      ((min 1 (Real.sqrt h)) ^ n)⁻¹ * (1 + ‖y‖) ^ (-(n : ℝ)) := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hc0 : 0 < min 1 (Real.sqrt h) := lt_min one_pos hs
  have hcy : min 1 (Real.sqrt h) * (1 + ‖y‖) ≤ ‖y‖ + Real.sqrt h := by
    have h1 : min 1 (Real.sqrt h) ≤ 1 := min_le_left _ _
    have h2 : min 1 (Real.sqrt h) ≤ Real.sqrt h := min_le_right _ _
    nlinarith [norm_nonneg y]
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
    Real.rpow_natCast, ← mul_inv, ← mul_pow]
  gcongr

/-! ### Lipschitz bounds for the profile -/

theorem simHeat_sub_eq {h : ℝ} (hh : 0 < h) {k : ℕ} {C : ℝ} {u : SpatialField}
    (hu : InvDistClass k C u) (σ τ : ℝ) :
    simHeat h u σ - simHeat h u τ = average h (simDil σ u - simDil τ u) := by
  rw [simHeat_eq hh, simHeat_eq hh]
  exact (average_sub' (hu.simDilClass σ).heatAdmissible (hu.simDilClass τ).heatAdmissible hh).symm

/-- `|D^j(H_h[u](σ) - H_h[u](τ))(y)| ≤ L|σ - τ|(1 + |y|)^{-1-j}`, `j ≤ 2`, for `u ∈ 𝒦₃(C)`. -/
theorem norm_iteratedFDeriv_simHeat_sub_le {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 3 C u) {j : ℕ} (hj : j ≤ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ σ τ : ℝ, ∀ y : Space,
      ‖iteratedFDeriv ℝ j (simHeat h u σ - simHeat h u τ) y‖ ≤
        L * |σ - τ| * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by
  set C' := max C 1 with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hu' : InvDistClass 3 C' u := hu.mono (le_max_left _ _)
  obtain ⟨K, hK0, hK⟩ := InvDistClass.heat_decay_lin (E := Space) hj
  set m := min 1 (Real.sqrt h)
  have hm0 : 0 < m := lt_min one_pos (Real.sqrt_pos.mpr hh)
  refine ⟨2 * C' * K * (m ^ (1 + j))⁻¹, by positivity, fun σ τ y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  rcases eq_or_ne σ τ with rfl | hne
  · rw [sub_self, sub_self, abs_zero, mul_zero, zero_mul,
      show (0 : Space → Space) = fun _ => (0 : Space) from rfl, iteratedFDeriv_fun_zero]
    simp
  have hc : 0 < 2 * C' * |σ - τ| := by
    have := abs_pos.mpr (sub_ne_zero.mpr hne); positivity
  rw [simHeat_sub_eq hh hu' σ τ]
  refine (hK _ hc _ (hu'.dil_sub σ τ) h hh y).trans ?_
  have h2 := weight_sqrt_le hh (1 + j) y
  calc 2 * C' * |σ - τ| * K * (‖y‖ + Real.sqrt h) ^ (-((1 + j : ℕ) : ℝ))
      ≤ 2 * C' * |σ - τ| * K * ((m ^ (1 + j))⁻¹ * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ))) := by
        gcongr
    _ = 2 * C' * K * (m ^ (1 + j))⁻¹ * |σ - τ| * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by ring

/-! ### Continuity in `C₀` -/

theorem tendsto_weight_cocompact {K a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : Space => K * (1 + ‖y‖) ^ (-a)) (cocompact Space) (𝓝 0) := by
  have h1 : Tendsto (fun y : Space => 1 + ‖y‖) (cocompact Space) atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_norm_cocompact_atTop (E := Space))
  have h2 := (tendsto_rpow_neg_atTop ha).comp h1
  simpa using h2.const_mul K

/-- **INF04 T10 `simHeat_continuous_C0`** (B0711, tex 279–290: `U_* ∈ C_per(ℝ; C₀(ℝ³))`, heat
part). For `h > 0` and `u ∈ 𝒦₃(C)`, every phase of the profile `H_h[u](τ)` is a `C₀` field and
`τ ↦ H_h[u](τ)` is continuous (indeed Lipschitz) for the sup norm. -/
theorem simHeat_continuous_C0 {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 3 C u) :
    ∃ V : ℝ → ZeroAtInftyContinuousMap Space Space, Continuous V ∧
      ∀ τ, (V τ : Space → Space) = simHeat h u τ := by
  have hu2 : InvDistClass 2 C u := hu.of_le (by norm_num)
  obtain ⟨K, hK⟩ := simHeat_decay hh hu2 (j := 0) (by norm_num)
  have htend : ∀ τ, Tendsto (simHeat h u τ) (cocompact Space) (𝓝 0) := by
    intro τ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_)
      (tendsto_weight_cocompact (K := K) (a := ((1 + 0 : ℕ) : ℝ)) (by norm_num))
    have := hK τ y
    rwa [norm_iteratedFDeriv_zero] at this
  obtain ⟨L, hL0, hL⟩ := norm_iteratedFDeriv_simHeat_sub_le hh hu (j := 0) (by norm_num)
  refine ⟨fun τ => ⟨⟨simHeat h u τ, (simHeat_contDiff hh hu.heatAdmissible τ).continuous⟩,
    htend τ⟩, ?_, fun τ => rfl⟩
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) fun σ τ => ?_).continuous
  rw [Real.coe_toNNReal _ hL0, Real.dist_eq, ← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist,
    BoundedContinuousFunction.dist_le (by positivity)]
  intro y
  have h1 := hL σ τ y
  rw [norm_iteratedFDeriv_zero] at h1
  rw [dist_eq_norm]
  have hw : (1 + ‖y‖) ^ (-((1 + 0 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
  calc ‖simHeat h u σ y - simHeat h u τ y‖
      ≤ L * |σ - τ| * (1 + ‖y‖) ^ (-((1 + 0 : ℕ) : ℝ)) := h1
    _ ≤ L * |σ - τ| * 1 := by gcongr
    _ = L * |σ - τ| := mul_one _

/-! ### Continuity in `L^p` -/

/-- `(1 + |y|)^{-a} ∈ L^p(ℝ³)` for `ap > 3`, `0 < p < ∞`. -/
theorem memLp_weight_rpow {a : ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hap : 3 < a * p.toReal) : MemLp (fun y : Space => (1 + ‖y‖) ^ (-a)) p volume := by
  have hmeas : AEStronglyMeasurable (fun y : Space => (1 + ‖y‖) ^ (-a)) volume :=
    (continuous_weight a).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas hp0 hpt]
  have hfin : (Module.finrank ℝ Space : ℝ) < a * p.toReal := by
    rw [show Module.finrank ℝ Space = 3 by simp [Space]]; exact_mod_cast hap
  refine (integrable_one_add_norm (μ := (volume : Measure Space)) hfin).congr
    (Eventually.of_forall fun y => ?_)
  simp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), ← Real.rpow_mul (by positivity)]
  ring_nf

/-- A family of fields dominated by an `L^p` weight and Lipschitz in the parameter against it
defines a continuous (Lipschitz) path in `L^p`. -/
theorem exists_continuous_Lp_of_lipschitz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℝ → Space → F} {w : Space → ℝ} (hw : MemLp w p volume)
    (hmeas : ∀ τ, AEStronglyMeasurable (f τ) volume) {K L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ τ y, ‖f τ y‖ ≤ K * ‖w y‖) (hlip : ∀ σ τ y, ‖f σ y - f τ y‖ ≤ L * |σ - τ| * ‖w y‖) :
    ∃ W : ℝ → Lp F p volume, Continuous W ∧ ∀ τ, (W τ : Space → F) =ᵐ[volume] f τ := by
  have hmem : ∀ τ, MemLp (f τ) p volume := fun τ =>
    hw.of_le_mul (hmeas τ) (Eventually.of_forall (hb τ))
  refine ⟨fun τ => (hmem τ).toLp (f τ), ?_, fun τ => (hmem τ).coeFn_toLp⟩
  have hK : 0 ≤ L * (eLpNorm w p volume).toReal := mul_nonneg hL ENNReal.toReal_nonneg
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (L * (eLpNorm w p volume).toReal))
    fun σ τ => ?_).continuous
  rw [Real.coe_toNNReal _ hK, Real.dist_eq, Lp.dist_def]
  have he : (⇑((hmem σ).toLp (f σ)) - ⇑((hmem τ).toLp (f τ))) =ᵐ[volume] (f σ - f τ) :=
    (hmem σ).coeFn_toLp.sub (hmem τ).coeFn_toLp
  rw [eLpNorm_congr_ae he]
  have hc : 0 ≤ L * |σ - τ| := mul_nonneg hL (abs_nonneg _)
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (f := f σ - f τ) (g := w)
    (c := L * |σ - τ|) (Eventually.of_forall fun y => hlip σ τ y) p
  calc (eLpNorm (f σ - f τ) p volume).toReal
      ≤ (ENNReal.ofReal (L * |σ - τ|) * eLpNorm w p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw.eLpNorm_ne_top) h1
    _ = L * (eLpNorm w p volume).toReal * |σ - τ| := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]; ring

/-- **INF04 T10 `simHeat_grad_continuous_L3`** (B0711, tex 279–290: `∇U_* ∈ C_per(ℝ; L³)`,
heat part). For `h > 0` and `u ∈ 𝒦₃(C)`, the gradient `DH_h[u](τ)` lies in `L³(ℝ³)` and is
continuous (indeed Lipschitz) in the phase `τ`. -/
theorem simHeat_grad_continuous_L3 {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 3 C u) :
    ∃ W : ℝ → Lp (Space →L[ℝ] Space) 3 volume, Continuous W ∧
      ∀ τ, (W τ : Space → Space →L[ℝ] Space) =ᵐ[volume] fderiv ℝ (simHeat h u τ) := by
  have hu2 : InvDistClass 2 C u := hu.of_le (by norm_num)
  obtain ⟨K, hK⟩ := simHeat_decay hh hu2 (j := 1) (by norm_num)
  obtain ⟨L, hL0, hL⟩ := norm_iteratedFDeriv_simHeat_sub_le hh hu (j := 1) (by norm_num)
  have hsm : ∀ τ, ContDiff ℝ ∞ (simHeat h u τ) := simHeat_contDiff hh hu.heatAdmissible
  have hw : MemLp (fun y : Space => (1 + ‖y‖) ^ (-((1 + 1 : ℕ) : ℝ))) 3 volume :=
    memLp_weight_rpow (by norm_num) (by norm_num) (by norm_num)
  have hwn : ∀ y : Space, ‖(1 + ‖y‖) ^ (-((1 + 1 : ℕ) : ℝ))‖ =
      (1 + ‖y‖) ^ (-((1 + 1 : ℕ) : ℝ)) := fun y =>
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
  refine exists_continuous_Lp_of_lipschitz (K := K) hw
    (fun τ => ((hsm τ).continuous_fderiv (by simp)).aestronglyMeasurable) hL0
    (fun τ y => ?_) (fun σ τ y => ?_)
  · rw [hwn, ← norm_iteratedFDeriv_one]; exact hK τ y
  · have hd : ∀ s, DifferentiableAt ℝ (simHeat h u s) y := fun s =>
      ((hsm s).differentiable (by simp)) y
    have e : fderiv ℝ (simHeat h u σ - simHeat h u τ) y =
        fderiv ℝ (simHeat h u σ) y - fderiv ℝ (simHeat h u τ) y :=
      ((hd σ).hasFDerivAt.sub (hd τ).hasFDerivAt).fderiv
    rw [hwn, ← e, ← norm_iteratedFDeriv_one]
    exact hL σ τ y

/-- **INF04 T10, Hessian** (B0711, tex 279–290; second weak derivatives in `L²`, the third
component of `HeatProfileRegularity`). For `h > 0` and `u ∈ 𝒦₃(C)`, `D²H_h[u](τ) ∈ L²(ℝ³)`,
continuous (indeed Lipschitz) in `τ`. -/
theorem simHeat_hessian_continuous_L2 {h : ℝ} (hh : 0 < h) {C : ℝ} {u : SpatialField}
    (hu : InvDistClass 3 C u) :
    ∃ Y : ℝ → Lp (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space) 2 volume,
      Continuous Y ∧ ∀ τ, (Y τ : Space → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space)
        =ᵐ[volume] iteratedFDeriv ℝ 2 (simHeat h u τ) := by
  have hu2 : InvDistClass 2 C u := hu.of_le (by norm_num)
  obtain ⟨K, hK⟩ := simHeat_decay hh hu2 (j := 2) (by norm_num)
  obtain ⟨L, hL0, hL⟩ := norm_iteratedFDeriv_simHeat_sub_le hh hu (j := 2) (by norm_num)
  have hsm : ∀ τ, ContDiff ℝ ∞ (simHeat h u τ) := simHeat_contDiff hh hu.heatAdmissible
  have hw : MemLp (fun y : Space => (1 + ‖y‖) ^ (-((1 + 2 : ℕ) : ℝ))) 2 volume :=
    memLp_weight_rpow (by norm_num) (by norm_num) (by norm_num)
  have hwn : ∀ y : Space, ‖(1 + ‖y‖) ^ (-((1 + 2 : ℕ) : ℝ))‖ =
      (1 + ‖y‖) ^ (-((1 + 2 : ℕ) : ℝ)) := fun y =>
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
  refine exists_continuous_Lp_of_lipschitz (K := K) hw
    (fun τ => ((hsm τ).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable) hL0
    (fun τ y => ?_) (fun σ τ y => ?_)
  · rw [hwn]; exact hK τ y
  · have hcd : ∀ s, ContDiffAt ℝ 2 (simHeat h u s) y := fun s =>
      (contDiff_infty.mp (hsm s) 2).contDiffAt
    rw [hwn, ← iteratedFDeriv_sub_apply (hcd σ) (hcd τ)]
    exact hL σ τ y

end UnforcedLeray.Heat
