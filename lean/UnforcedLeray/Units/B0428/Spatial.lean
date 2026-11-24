import UnforcedLeray.Lib.HeatR3B.Interp
import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# Spatial heat interpolation of the gradient in `L^q(ℝ³; ℂ³)` (helper for B0428)

Blueprint unit **B0428** (`eq:free-stress-19`, `paper/main.tex` lines 7541–7548): "Spatial
elliptic interpolation gives `∇w ∈ Y_q` whenever `w, Δw ∈ Y_q`, and
`‖∇w‖_{Y_q} ≤ C_q ‖w‖_{Y_q}^{1/2} ‖Δw‖_{Y_q}^{1/2}`." This file is the spatial step, at one
phase: target S9b (`gradient_interp`, decision D15) of

of `scoping/INF01-CZ.md` §4.4 (bypass of the Calderón–Zygmund argument):

`∂ₑv = ∂ₑe^{tΔ}v - ∫_0^t ∂ₑe^{sΔ}Δv ds`, `‖∂ₑe^{sΔ}‖_{q→q} ≤ c s^{-1/2}|e|`, then optimise `t`.

The smooth case is the drafted `Heat.eLpNorm_fderiv_le_interp` (`Lib/HeatR3B/Interp.lean`); the
identity `Δe^{θΔ}u = e^{θΔ}Λ` for a distributional pair is `Heat.vlap_average_eq`
(`Lib/HeatR3B/WeakLap.lean`). Here the smooth bound is transferred to a distributional pair
`u, Λ = Δu ∈ L^q`:

* `dHeat θ hθ e u = ∂ₑ e^{θΔ}u ∈ L^q` (`θ > 0`), additive and Lipschitz in `u`
  (`dHeat_sub`, `continuous_dHeat`);
* `norm_dHeat_sub_le`: `‖∂ₑ(e^{θΔ}u - e^{θ'Δ}u)‖ ≤ c t^{-1/2}|e|‖e^{θΔ}u - e^{θ'Δ}u‖
  + 2c t^{1/2}|e|‖e^{θΔ}Λ - e^{θ'Δ}Λ‖`, so `∂ₑe^{θₙΔ}u` (`θₙ = 1/(n+1)`) is Cauchy;
* `gradL e u`: its limit, the weak derivative `∂ₑu ∈ L^q` (`tendsto_gradL`,
  `innerPair_gradL`: `⟪Ψ, ∂ₑu⟫ = -⟪∂ₑΨ, u⟫` for `C¹` compactly supported `Ψ : ℝ³ → ℂ³`);
* `norm_gradL_le`: `‖∂ₑu‖_q ≤ c t^{-1/2}|e|‖u‖_q + 2c t^{1/2}|e|‖Λ‖_q` for every `t > 0`.

Conventions: `1 ≤ q < ∞` (`[Fact (1 ≤ q)]`, `q ≠ ⊤`); `c = Gaussian.derivLpConst 3 1 1`
(`= ‖∇G_1‖_{L¹}`, the heat constant of `Heat.eLpNorm_fderiv_average_apply_le`), independent of
`q`. Fields are `ℂ³`-valued (`PhaseSpace.CVec3`, the values of `Y_q`), viewed as a real Banach
space for the heat calculus.

Status: helper for B0428; Theorem A is not proved in Lean.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0428

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.Heat UnforcedLeray.PhaseSpace

/-- The heat constant `c = ‖∇G_1‖_{L¹(ℝ³)}` of `‖∂ₑe^{sΔ}‖_{q→q} ≤ c s^{-1/2}|e|`. -/
abbrev cHeat : ℝ := Gaussian.derivLpConst 3 1 1

theorem cHeat_nonneg : 0 ≤ cHeat := ENNReal.toReal_nonneg

/-- Heat times `θₙ = 1/(n+1) → 0`. -/
def θs (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem θs_pos (n : ℕ) : 0 < θs n := by unfold θs; positivity

theorem tendsto_θs : Tendsto θs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

section Spatial

variable {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- The heat operator `e^{θΔ}` on `L^q(ℝ³; ℂ³)`: the frozen interface `heatLp` (D17). -/
def heat (θ : ℝ) :
    Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q (volume : Measure Space) :=
  heatLp (AddMonoidHom.id Space) continuous_id θ

theorem heat_ae {θ : ℝ} (hθ : 0 < θ) (u : Lp CVec3 q (volume : Measure Space)) :
    (heat θ u : Space → CVec3) =ᵐ[volume] average θ (u : Space → CVec3) := by
  have h := heatLp_rep (AddMonoidHom.id Space) continuous_id hθ u
  rwa [heatConv_space_eq_average] at h

theorem norm_heat_le (θ : ℝ) (u : Lp CVec3 q (volume : Measure Space)) :
    ‖heat θ u‖ ≤ ‖u‖ :=
  norm_heatLp_apply_le (AddMonoidHom.id Space) continuous_id θ u

/-- `e^{θΔ}u → u` in `L^q` along `θₙ → 0`, `q < ∞`. -/
theorem tendsto_heat (hqt : q ≠ ⊤) (u : Lp CVec3 q (volume : Measure Space)) :
    Tendsto (fun n => heat (θs n) u) atTop (𝓝 u) := by
  have h := (tendsto_heatLp_sub (AddMonoidHom.id Space) continuous_id hqt u).comp tendsto_θs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def, toReal_enorm, heat] using h2

/-! ### The smooth interpolation inequality for `L^q` classes -/

/-- `eLpNorm_fderiv_le_interp` for `L^q` classes: if `V, Λ, D ∈ L^q` represent `v`, `Δv` and
`∂ₑv` of a `C³` field with bounded derivatives, then
`‖D‖ ≤ c t^{-1/2}|e|‖V‖ + 2c t^{1/2}|e|‖Λ‖`. -/
theorem norm_le_of_smooth (hqt : q ≠ ⊤) {v : Space → CVec3} (hv : ContDiff ℝ 3 v) {M : ℝ}
    (hb : ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M) (e : Space)
    {V Λ D : Lp CVec3 q (volume : Measure Space)} (hV : (V : Space → CVec3) =ᵐ[volume] v)
    (hΛ : (Λ : Space → CVec3) =ᵐ[volume] vlap v)
    (hD : (D : Space → CVec3) =ᵐ[volume] fun x => fderiv ℝ v x e) {t : ℝ} (ht : 0 < t) :
    ‖D‖ ≤ cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖ * ‖V‖ +
      2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖ * ‖Λ‖ := by
  have hvq : MemLp v q volume := (Lp.memLp V).ae_eq hV
  have hΛq : MemLp (vlap v) q volume := (Lp.memLp Λ).ae_eq hΛ
  have h := eLpNorm_fderiv_le_interp hv hb hq.out hqt hvq hΛq ht e
  rw [← eLpNorm_congr_ae hD, ← eLpNorm_congr_ae hV, ← eLpNorm_congr_ae hΛ] at h
  have ha : 0 ≤ cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖ := by
    have := cHeat_nonneg; positivity
  have hb' : 0 ≤ 2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖ := by
    have := cHeat_nonneg; positivity
  have hfin : ENNReal.ofReal (cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖) * eLpNorm V q volume +
      ENNReal.ofReal (2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖) * eLpNorm Λ q volume ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top V),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top Λ)⟩
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def]
  calc (eLpNorm D q volume).toReal
      ≤ (ENNReal.ofReal (cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖) * eLpNorm V q volume +
          ENNReal.ofReal (2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖) * eLpNorm Λ q volume).toReal :=
        ENNReal.toReal_mono hfin h
    _ = _ := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top V))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top Λ)),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
          ENNReal.toReal_ofReal hb']

/-! ### `∂ₑe^{θΔ}` on `L^q` -/

theorem heatAdmissible (u : Lp CVec3 q (volume : Measure Space)) :
    HeatAdmissible (u : Space → CVec3) :=
  HeatAdmissible.of_memLp hq.out (Lp.memLp u)

theorem contDiff_avg (u : Lp CVec3 q (volume : Measure Space)) {θ : ℝ} (hθ : 0 < θ) :
    ContDiff ℝ ∞ (average θ (u : Space → CVec3)) :=
  contDiff_average (heatAdmissible u) hθ

theorem differentiable_avg (u : Lp CVec3 q (volume : Measure Space)) {θ : ℝ} (hθ : 0 < θ) :
    Differentiable ℝ (average θ (u : Space → CVec3)) :=
  (contDiff_avg u hθ).differentiable (by simp)

theorem continuous_fderiv_avg_apply (u : Lp CVec3 q (volume : Measure Space)) {θ : ℝ}
    (hθ : 0 < θ) (e : Space) :
    Continuous fun x => fderiv ℝ (average θ (u : Space → CVec3)) x e :=
  ((contDiff_avg u hθ).continuous_fderiv (by simp)).clm_apply continuous_const

theorem memLp_fderiv_avg (u : Lp CVec3 q (volume : Measure Space)) {θ : ℝ} (hθ : 0 < θ)
    (e : Space) :
    MemLp (fun x => fderiv ℝ (average θ (u : Space → CVec3)) x e) q volume :=
  ⟨(continuous_fderiv_avg_apply u hθ e).aestronglyMeasurable,
    (eLpNorm_fderiv_average_apply_le hq.out (Lp.memLp u) hθ e).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top u))⟩

/-- `∂ₑ e^{θΔ}u` as an element of `L^q(ℝ³; ℂ³)`, `θ > 0`. -/
def dHeat (θ : ℝ) (hθ : 0 < θ) (e : Space) (u : Lp CVec3 q (volume : Measure Space)) :
    Lp CVec3 q (volume : Measure Space) :=
  (memLp_fderiv_avg u hθ e).toLp _

theorem dHeat_ae {θ : ℝ} (hθ : 0 < θ) (e : Space) (u : Lp CVec3 q (volume : Measure Space)) :
    (dHeat θ hθ e u : Space → CVec3) =ᵐ[volume]
      fun x => fderiv ℝ (average θ (u : Space → CVec3)) x e :=
  MemLp.coeFn_toLp _

theorem avg_sub_eq (u v : Lp CVec3 q (volume : Measure Space)) {θ : ℝ} (hθ : 0 < θ) :
    average θ ((u - v : Lp CVec3 q (volume : Measure Space)) : Space → CVec3) =
      average θ (u : Space → CVec3) - average θ (v : Space → CVec3) := by
  rw [average_congr_ae (Lp.coeFn_sub u v) θ]
  exact average_sub' (heatAdmissible u) (heatAdmissible v) hθ

theorem dHeat_sub {θ : ℝ} (hθ : 0 < θ) (e : Space) (u v : Lp CVec3 q (volume : Measure Space)) :
    dHeat θ hθ e (u - v) = dHeat θ hθ e u - dHeat θ hθ e v := by
  unfold dHeat
  rw [← MemLp.toLp_sub]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rw [avg_sub_eq u v hθ, fderiv_sub (differentiable_avg u hθ x) (differentiable_avg v hθ x),
    ContinuousLinearMap.sub_apply]

theorem norm_dHeat_le {θ : ℝ} (hθ : 0 < θ) (e : Space) (u : Lp CVec3 q (volume : Measure Space)) :
    ‖dHeat θ hθ e u‖ ≤ cHeat * θ ^ (-(1 : ℝ) / 2) * ‖e‖ * ‖u‖ := by
  rw [dHeat, Lp.norm_toLp, Lp.norm_def]
  have h := eLpNorm_fderiv_average_apply_le hq.out (Lp.memLp u) hθ e
  have ha : 0 ≤ cHeat * θ ^ (-(1 : ℝ) / 2) * ‖e‖ := by
    have := cHeat_nonneg; positivity
  calc (eLpNorm (fun x => fderiv ℝ (average θ (u : Space → CVec3)) x e) q volume).toReal
      ≤ (ENNReal.ofReal (cHeat * θ ^ (-(1 : ℝ) / 2) * ‖e‖) * eLpNorm u q volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]

/-- `u ↦ ∂ₑe^{θΔ}u` is Lipschitz on `L^q`. -/
theorem continuous_dHeat {θ : ℝ} (hθ : 0 < θ) (e : Space) :
    Continuous (dHeat (q := q) θ hθ e) := by
  have hK : 0 ≤ cHeat * θ ^ (-(1 : ℝ) / 2) * ‖e‖ := by
    have := cHeat_nonneg; positivity
  refine (LipschitzWith.of_dist_le_mul (K := ⟨_, hK⟩) fun u v => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← dHeat_sub]
  exact norm_dHeat_le hθ e (u - v)

/-! ### The interpolation bounds for a distributional pair `Λ = Δu` -/

theorem vlap_sub {f g : Space → CVec3} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space) :
    vlap (f - g) x = vlap f x - vlap g x := by
  simp only [vlap]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt, ContinuousMultilinearMap.sub_apply]

theorem bounded_derivs_avg (hqt : q ≠ ⊤) (u : Lp CVec3 q (volume : Measure Space)) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k (average θ (u : Space → CVec3)) x‖ ≤ M :=
  bounded_derivs_average hq.out hqt (Lp.memLp u) hθ

theorem vlap_avg_eq {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) {θ : ℝ} (hθ : 0 < θ) :
    vlap (average θ (u : Space → CVec3)) = average θ (Λ : Space → CVec3) :=
  funext fun x => vlap_average_eq hWL (heatAdmissible u) (heatAdmissible Λ) hθ x

/-- **Single bound.** `‖∂ₑe^{θΔ}u‖ ≤ c t^{-1/2}|e|‖u‖ + 2c t^{1/2}|e|‖Λ‖` for `Λ = Δu`. -/
theorem norm_dHeat_le_interp (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) {θ : ℝ} (hθ : 0 < θ)
    (e : Space) {t : ℝ} (ht : 0 < t) :
    ‖dHeat θ hθ e u‖ ≤ cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖ * ‖u‖ +
      2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖ * ‖Λ‖ := by
  obtain ⟨M, hM⟩ := bounded_derivs_avg hqt u hθ
  have hv : ContDiff ℝ 3 (average θ (u : Space → CVec3)) := contDiff_infty.1 (contDiff_avg u hθ) 3
  have hΛ : (heat θ Λ : Space → CVec3) =ᵐ[volume] vlap (average θ (u : Space → CVec3)) := by
    rw [vlap_avg_eq hWL hθ]; exact heat_ae hθ Λ
  have h := norm_le_of_smooth hqt hv hM e (heat_ae hθ u) hΛ (dHeat_ae hθ e u) ht
  have ha : 0 ≤ cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖ := by
    have := cHeat_nonneg; positivity
  have hb : 0 ≤ 2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖ := by
    have := cHeat_nonneg; positivity
  refine h.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left (norm_heat_le θ u) ha
  · exact mul_le_mul_of_nonneg_left (norm_heat_le θ Λ) hb

/-- **Difference bound.** `‖∂ₑ(e^{θΔ}u - e^{θ'Δ}u)‖ ≤ c t^{-1/2}|e|‖e^{θΔ}u - e^{θ'Δ}u‖
+ 2c t^{1/2}|e|‖e^{θΔ}Λ - e^{θ'Δ}Λ‖` for `Λ = Δu`. -/
theorem norm_dHeat_sub_le (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) {θ θ' : ℝ} (hθ : 0 < θ)
    (hθ' : 0 < θ') (e : Space) {t : ℝ} (ht : 0 < t) :
    ‖dHeat θ hθ e u - dHeat θ' hθ' e u‖ ≤
      cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖ * ‖heat θ u - heat θ' u‖ +
        2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖ * ‖heat θ Λ - heat θ' Λ‖ := by
  obtain ⟨M₁, hM₁⟩ := bounded_derivs_avg hqt u hθ
  obtain ⟨M₂, hM₂⟩ := bounded_derivs_avg hqt u hθ'
  set a := average θ (u : Space → CVec3) with ha_def
  set b := average θ' (u : Space → CVec3) with hb_def
  have hca : ContDiff ℝ ∞ a := contDiff_avg u hθ
  have hcb : ContDiff ℝ ∞ b := contDiff_avg u hθ'
  have hv : ContDiff ℝ 3 (a - b) := contDiff_infty.1 (hca.sub hcb) 3
  have hb : ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k (a - b) x‖ ≤ M₁ + M₂ := fun k hk x => by
    rw [iteratedFDeriv_sub_apply (contDiff_infty.1 hca k).contDiffAt (contDiff_infty.1 hcb k).contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add (hM₁ k hk x) (hM₂ k hk x))
  have hV : ((heat θ u - heat θ' u : Lp CVec3 q (volume : Measure Space)) : Space → CVec3)
      =ᵐ[volume] a - b := by
    filter_upwards [Lp.coeFn_sub (heat θ u) (heat θ' u), heat_ae hθ u, heat_ae hθ' u]
      with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
  have hΛ : ((heat θ Λ - heat θ' Λ : Lp CVec3 q (volume : Measure Space)) : Space → CVec3)
      =ᵐ[volume] vlap (a - b) := by
    filter_upwards [Lp.coeFn_sub (heat θ Λ) (heat θ' Λ), heat_ae hθ Λ, heat_ae hθ' Λ]
      with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, vlap_sub (contDiff_infty.1 hca 2) (contDiff_infty.1 hcb 2),
      ha_def, hb_def, vlap_avg_eq hWL hθ, vlap_avg_eq hWL hθ']
  have hD : ((dHeat θ hθ e u - dHeat θ' hθ' e u : Lp CVec3 q (volume : Measure Space)) :
      Space → CVec3) =ᵐ[volume] fun x => fderiv ℝ (a - b) x e := by
    filter_upwards [Lp.coeFn_sub (dHeat θ hθ e u) (dHeat θ' hθ' e u), dHeat_ae hθ e u,
      dHeat_ae hθ' e u] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, fderiv_sub (differentiable_avg u hθ x)
      (differentiable_avg u hθ' x), ContinuousLinearMap.sub_apply]
  exact norm_le_of_smooth hqt hv hb e hV hΛ hD ht

/-- The sequence `∂ₑe^{θₙΔ}u` is Cauchy in `L^q` when `Δu ∈ L^q`. -/
theorem cauchySeq_dHeat (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) (e : Space) :
    CauchySeq fun n => dHeat (θs n) (θs_pos n) e u := by
  set A : ℝ := cHeat * ‖e‖ with hA
  have hA0 : 0 ≤ A := by have := cHeat_nonneg; positivity
  have hbd : ∀ m n, dist (dHeat (θs m) (θs_pos m) e u) (dHeat (θs n) (θs_pos n) e u) ≤
      A * dist (heat (θs m) u) (heat (θs n) u) +
        2 * A * dist (heat (θs m) Λ) (heat (θs n) Λ) := fun m n => by
    have h := norm_dHeat_sub_le hqt hWL (θs_pos m) (θs_pos n) e one_pos
    simp only [Real.one_rpow, mul_one] at h
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hA]
    linarith
  have hu := (tendsto_heat hqt u).cauchySeq
  have hΛ := (tendsto_heat hqt Λ).cauchySeq
  rw [Metric.cauchySeq_iff] at hu hΛ ⊢
  intro ε hε
  set δ : ℝ := ε / (3 * A + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N₁, hN₁⟩ := hu δ hδ0
  obtain ⟨N₂, hN₂⟩ := hΛ δ hδ0
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  have h1 := hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  have h2 := hN₂ m (le_of_max_le_right hm) n (le_of_max_le_right hn)
  have h3 : 3 * A * δ < ε := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  calc dist (dHeat (θs m) (θs_pos m) e u) (dHeat (θs n) (θs_pos n) e u)
      ≤ A * dist (heat (θs m) u) (heat (θs n) u) +
          2 * A * dist (heat (θs m) Λ) (heat (θs n) Λ) := hbd m n
    _ ≤ A * δ + 2 * A * δ := by
        gcongr
    _ < ε := by linarith

/-- The weak derivative `∂ₑu`: the `L^q` limit of `∂ₑe^{θₙΔ}u` (junk if the limit does not
exist; `tendsto_gradL` shows that it does when `Δu ∈ L^q`). -/
def gradL (e : Space) (u : Lp CVec3 q (volume : Measure Space)) :
    Lp CVec3 q (volume : Measure Space) :=
  limUnder atTop fun n => dHeat (θs n) (θs_pos n) e u

theorem tendsto_gradL (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) (e : Space) :
    Tendsto (fun n => dHeat (θs n) (θs_pos n) e u) atTop (𝓝 (gradL e u)) :=
  (cauchySeq_dHeat hqt hWL e).tendsto_limUnder

/-- **Heat interpolation of the gradient** (S9b): `‖∂ₑu‖_q ≤ c t^{-1/2}|e|‖u‖_q
+ 2c t^{1/2}|e|‖Δu‖_q` for every `t > 0`. -/
theorem norm_gradL_le (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) (e : Space) {t : ℝ}
    (ht : 0 < t) :
    ‖gradL e u‖ ≤ cHeat * t ^ (-(1 : ℝ) / 2) * ‖e‖ * ‖u‖ +
      2 * cHeat * t ^ (1 / 2 : ℝ) * ‖e‖ * ‖Λ‖ :=
  le_of_tendsto (tendsto_gradL hqt hWL e).norm
    (Eventually.of_forall fun n => norm_dHeat_le_interp hqt hWL (θs_pos n) e ht)

/-! ### `gradL e u` is the distributional derivative -/

/-- The bilinear dot product as a real bilinear map (for integration by parts). -/
def dotR : CVec3 →L[ℝ] CVec3 →L[ℝ] ℂ := dotL.bilinearRestrictScalars ℝ

theorem dotR_apply (a b : CVec3) : dotR a b = dotL a b := rfl

theorem continuous_dotR_comp {α : Type*} [TopologicalSpace α] {f g : α → CVec3}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => dotL (f x) (g x) :=
  (dotR.continuous.comp hf).clm_apply hg

theorem hasCompactSupport_dotL_left {f g : Space → CVec3} (hf : HasCompactSupport f) :
    HasCompactSupport fun x => dotL (f x) (g x) :=
  hf.mono fun x hx => by
    intro h0
    apply hx
    simp only at h0 ⊢
    rw [h0, map_zero, ContinuousLinearMap.zero_apply]

/-- Integration by parts against `e^{θΔ}u`: `∫ Ψ · ∂ₑv = -∫ ∂ₑΨ · v`, `v = e^{θΔ}u`. -/
theorem integral_dotL_fderiv_avg {Ψ : Space → CVec3} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨc : HasCompactSupport Ψ) (u : Lp CVec3 q (volume : Measure Space)) {θ : ℝ} (hθ : 0 < θ)
    (e : Space) :
    ∫ x, dotL (Ψ x) (fderiv ℝ (average θ (u : Space → CVec3)) x e) =
      -∫ x, dotL (fderiv ℝ Ψ x e) (average θ (u : Space → CVec3) x) := by
  set g := average θ (u : Space → CVec3)
  have hgc : Continuous g := (differentiable_avg u hθ).continuous
  have hΨ' : Continuous fun x => fderiv ℝ Ψ x e :=
    (hΨ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdΨc : HasCompactSupport fun x => fderiv ℝ Ψ x e := hΨc.fderiv_apply ℝ e
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume) (B := dotR)
    (f := Ψ) (g := g) (v := e)
    ((continuous_dotR_comp hΨ' hgc).integrable_of_hasCompactSupport
      (hasCompactSupport_dotL_left hdΨc))
    ((continuous_dotR_comp hΨ.continuous (continuous_fderiv_avg_apply u hθ e)).integrable_of_hasCompactSupport
      (hasCompactSupport_dotL_left hΨc))
    ((continuous_dotR_comp hΨ.continuous hgc).integrable_of_hasCompactSupport
      (hasCompactSupport_dotL_left hΨc))
    (fun x _ => (hΨ.differentiable one_ne_zero) x) (fun x _ => differentiable_avg u hθ x)
  simpa only [dotR_apply] using h

theorem memLp_test {Ψ : Space → CVec3} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (r : ℝ≥0∞) : MemLp Ψ r volume :=
  hΨ.memLp_of_hasCompactSupport hΨc

theorem memLp_fderiv_test {Ψ : Space → CVec3} (hΨ : ContDiff ℝ 1 Ψ) (hΨc : HasCompactSupport Ψ)
    (e : Space) (r : ℝ≥0∞) : MemLp (fun x => fderiv ℝ Ψ x e) r volume :=
  memLp_test ((hΨ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hΨc.fderiv_apply ℝ e) r

/-- **`gradL e u` is the weak derivative `∂ₑu`**: `⟪Ψ, ∂ₑu⟫ = -⟪∂ₑΨ, u⟫` for every `C¹`
compactly supported `Ψ : ℝ³ → ℂ³` (bilinear pairing `innerPair`), when `Δu ∈ L^q`. -/
theorem innerPair_gradL (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) (e : Space)
    {Ψ : Space → CVec3} (hΨ : ContDiff ℝ 1 Ψ) (hΨc : HasCompactSupport Ψ) :
    innerPair q ((memLp_test hΨ.continuous hΨc (conjExp q)).toLp Ψ) (gradL e u) =
      -innerPair q ((memLp_fderiv_test hΨ hΨc e (conjExp q)).toLp _) u := by
  set ψL := (memLp_test hΨ.continuous hΨc (conjExp q)).toLp Ψ
  set dψL := (memLp_fderiv_test hΨ hΨc e (conjExp q)).toLp (fun x => fderiv ℝ Ψ x e)
  have hn : ∀ n, innerPair q ψL (dHeat (θs n) (θs_pos n) e u) =
      -innerPair q dψL (heat (θs n) u) := fun n => by
    rw [innerPair_apply, innerPair_apply]
    have h1 : ∫ y, dotL (ψL y) (dHeat (θs n) (θs_pos n) e u y) =
        ∫ y, dotL (Ψ y) (fderiv ℝ (average (θs n) (u : Space → CVec3)) y e) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_test hΨ.continuous hΨc (conjExp q)),
        dHeat_ae (θs_pos n) e u] with y h1 h2
      rw [h1, h2]
    have h2 : ∫ y, dotL (dψL y) (heat (θs n) u y) =
        ∫ y, dotL (fderiv ℝ Ψ y e) (average (θs n) (u : Space → CVec3) y) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_fderiv_test hΨ hΨc e (conjExp q)),
        heat_ae (θs_pos n) u] with y h1 h2
      rw [h1, h2]
    rw [h1, h2]
    exact integral_dotL_fderiv_avg hΨ hΨc u (θs_pos n) e
  have hL : Tendsto (fun n => innerPair q ψL (dHeat (θs n) (θs_pos n) e u)) atTop
      (𝓝 (innerPair q ψL (gradL e u))) :=
    ((innerPair q ψL).continuous.tendsto _).comp (tendsto_gradL hqt hWL e)
  have hR : Tendsto (fun n => -innerPair q dψL (heat (θs n) u)) atTop
      (𝓝 (-innerPair q dψL u)) :=
    (((innerPair q dψL).continuous.tendsto _).comp (tendsto_heat hqt u)).neg
  simp only [hn] at hL
  exact tendsto_nhds_unique hL hR

end Spatial

end UnforcedLeray.B0428
