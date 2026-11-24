import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainClass.LkOneSided

/-!
# Part I, task `PartI:TC/4`: decay of the mean stress for a BUC train

Source of record: `the November 2 reference manuscript`, lines 261-288 and 397-404.
The Prop `BUCMeanStressDecay` is defined in `Short/PartI/Sub/T01Class.lean`; this file proves it.

Route, for `s ≥ 0` fixed:

* `v₂ = ∂_q ψ` on the slice `s` (`IsTrain.stream`, `toVec_one`), so `q ↦ ψ(s,q,η)` has derivative
  `q ↦ v₂(s,q,η)`, which is `C^∞` (`smooth_v`); hence `q ↦ ψ(s,q,η)` is `C²`.
* `|∂_q v₂| ≤ M₁` (order `1` of `IsBUCTrain`), so `LkOneSided` applies to `q ↦ ψ(s,q,η)` with
  `B = M₁` and the tail bound `m` of `stream_decay`; this gives `sup_q |v₂(s,q,η)| → 0` as `η → ∞`.
* `|v₁| ≤ M₀` (order `0`), and the horizontal average of a function bounded by `K` on the line
  `η` is bounded by `K` (`hmean` over a cell of length `c`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_one)

/-- The horizontal average of a function bounded by `K` on the line `η` is bounded by `K`. -/
theorem bucStress_hmean_abs_le {c : ℝ} (hc : 0 < c) (F : Plane → ℝ) (η K : ℝ)
    (h : ∀ q : ℝ, |F (q, η)| ≤ K) : |hmean c F η| ≤ K := by
  unfold hmean
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (-c / 2) (c / 2)) (f := fun q : ℝ => F (q, η)) (C := K)
    measure_Ioc_lt_top (fun q _ => by rw [Real.norm_eq_abs]; exact h q)
  rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring] at hint
  rw [Real.norm_eq_abs] at hint
  rw [smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
  have h1 : c⁻¹ * |∫ q in Ioc (-c / 2) (c / 2), F (q, η)| ≤ c⁻¹ * (K * c) :=
    mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hc.le)
  have h2 : c⁻¹ * (K * c) = K := by field_simp
  linarith

/-- The velocity restricted to a fixed age `s ≥ 0` is `C^∞` in the spatial variable. -/
theorem bucStress_vslice_contDiff {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (fun z : Plane => tr.v s z) := by
  have h := tr.isTrain.smooth_v
  have hmap : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have h2 : ContDiffOn ℝ ∞ (fun z : Plane => tr.v s z) univ :=
    h.comp hmap.contDiffOn (fun z _ => ⟨hs, mem_univ z⟩)
  exact contDiffOn_univ.1 h2

/-- The `q`-derivative of `q ↦ ψ(s,q,η)` is the second velocity component `v₂(s,q,η)`. -/
theorem bucStress_deriv_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (η q : ℝ) :
    HasDerivAt (fun x : ℝ => tr.ψ s (x, η)) (tr.v s (q, η) 1) q := by
  have hpath : DifferentiableAt ℝ (fun x : ℝ => ((x, η) : Plane)) q :=
    differentiableAt_id.prodMk (differentiableAt_const η)
  have hd : DifferentiableAt ℝ (fun x : ℝ => tr.ψ s (x, η)) q :=
    (tr.isTrain.stream_differentiable s hs (q, η)).comp q hpath
  have hval : tr.v s (q, η) 1 = deriv (fun x : ℝ => tr.ψ s (x, η)) q := by
    rw [tr.isTrain.stream s hs (q, η), toVec_one]
    rfl
  rw [hval]
  exact hd.hasDerivAt

/-- `q ↦ ψ(s,q,η)` is `C²`. -/
theorem bucStress_contDiff2 {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (η : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => tr.ψ s (x, η)) := by
  have hderiv : deriv (fun x : ℝ => tr.ψ s (x, η)) = fun q => tr.v s (q, η) 1 :=
    funext fun q => (bucStress_deriv_eq tr hs η q).deriv
  have hcurve : ContDiff ℝ ∞ (fun q : ℝ => tr.v s (q, η)) :=
    (bucStress_vslice_contDiff tr hs).comp (contDiff_id.prodMk contDiff_const)
  have hcomp : ContDiff ℝ ∞ (fun q : ℝ => tr.v s (q, η) 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hcurve
  have hC : ContDiff ℝ 1 (deriv (fun x : ℝ => tr.ψ s (x, η))) := by
    rw [hderiv]
    exact hcomp.of_le (by simp)
  have hdiff : Differentiable ℝ (fun x : ℝ => tr.ψ s (x, η)) :=
    fun q => (bucStress_deriv_eq tr hs η q).differentiableAt
  exact (contDiff_succ_iff_deriv (n := 1)).2 ⟨hdiff, fun h => by simp at h, hC⟩

/-- The `q`-derivative of the second velocity component is bounded by the first order bound. -/
theorem bucStress_v2_deriv_bound {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    {M1 : ℝ} (hM1 : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ ≤ M1) (η t : ℝ) :
    |deriv (fun q : ℝ => tr.v s (q, η) 1) t| ≤ M1 := by
  have hdiffv : DifferentiableAt ℝ (tr.v s) (t, η) :=
    ((bucStress_vslice_contDiff tr hs).differentiable (by simp)) (t, η)
  have hw : HasDerivAt (fun q : ℝ => tr.v s (q, η)) (fderiv ℝ (tr.v s) (t, η) (1, 0)) t :=
    hdiffv.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t η))
  have hL : HasDerivAt (fun q : ℝ => tr.v s (q, η) 1)
      (fderiv ℝ (tr.v s) (t, η) (1, 0) 1) t :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hw
  rw [hL.deriv]
  have hcomp : |fderiv ℝ (tr.v s) (t, η) (1, 0) 1| ≤ ‖fderiv ℝ (tr.v s) (t, η) (1, 0)‖ := by
    have := PiLp.norm_apply_le (fderiv ℝ (tr.v s) (t, η) (1, 0)) 1
    simpa [Real.norm_eq_abs] using this
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hop : ‖fderiv ℝ (tr.v s) (t, η) (1, 0)‖ ≤
      ‖fderiv ℝ (tr.v s) (t, η)‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
    (fderiv ℝ (tr.v s) (t, η)).le_opNorm _
  have hfd : ‖fderiv ℝ (tr.v s) (t, η)‖ ≤ M1 := by
    rw [← norm_iteratedFDeriv_one]
    exact hM1 _
  rw [h10, mul_one] at hop
  linarith

/-- **Uniform decay of the second velocity component on lines `η ≥ R`.** -/
theorem bucStress_v2_sup_decay {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    {M1 : ℝ} (hM1 : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ ≤ M1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ η : ℝ, R ≤ η → ∀ q : ℝ, |tr.v s (q, η) 1| ≤ δ := by
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 0)
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = δ / (2 * (M1 + 1)) := ⟨_, rfl⟩
  have hM1p : 0 < M1 + 1 := by linarith
  have hh : 0 < h := by rw [hh_def]; exact div_pos hδ (by linarith)
  have hMh : (M1 + 1) * h = δ / 2 := by
    rw [hh_def]; field_simp
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = δ * h / 4 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; positivity
  have hm2 : 2 * m / h = δ / 2 := by
    rw [hm_def]; field_simp; norm_num
  have hdec := Metric.tendsto_nhds.1 (tr.isTrain.stream_decay s hs) m hm
  rw [Filter.eventually_comap] at hdec
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hdec
  refine ⟨R, fun η hη q => ?_⟩
  have hbd : ∀ x : ℝ, |tr.ψ s (x, η)| ≤ m := by
    intro x
    have h1 := hR |η| (le_trans hη (le_abs_self η)) (x, η) rfl
    rw [dist_zero_right, Real.norm_eq_abs] at h1
    exact h1.le
  have hderiv : deriv (fun x : ℝ => tr.ψ s (x, η)) = fun q => tr.v s (q, η) 1 :=
    funext fun q => (bucStress_deriv_eq tr hs η q).deriv
  have h2 : iteratedDeriv 2 (fun x : ℝ => tr.ψ s (x, η)) =
      deriv (fun q : ℝ => tr.v s (q, η) 1) := by
    rw [show iteratedDeriv 2 (fun x : ℝ => tr.ψ s (x, η)) =
      iteratedDeriv (1 + 1) (fun x : ℝ => tr.ψ s (x, η)) from rfl, iteratedDeriv_succ,
      iteratedDeriv_one, hderiv]
  have hiter : ∀ t : ℝ, |iteratedDeriv 2 (fun x : ℝ => tr.ψ s (x, η)) t| ≤ M1 := by
    intro t
    rw [congrFun h2 t]
    exact bucStress_v2_deriv_bound tr hs hM1 η t
  have hL := lkOneSided (fun x : ℝ => tr.ψ s (x, η)) q M1 m h
    (bucStress_contDiff2 tr hs η) hM1nn hm.le hh hiter (fun t _ => hbd t)
  rw [(bucStress_deriv_eq tr hs η q).deriv] at hL
  have hMle : M1 * h ≤ (M1 + 1) * h := by nlinarith
  rw [hm2] at hL
  have : M1 * h / 2 ≤ δ / 4 := by linarith
  linarith

/-- **`PartI:TC/4`. Decay of the mean stress** (BUC train, `s ≥ 0`): `g(s,η) → 0` as `η → +∞`. -/
theorem bucMeanStressDecay : BUCMeanStressDecay := by
  intro ν c _hν hc tr hb s hs
  obtain ⟨M0, hM0⟩ := hb.sup_bound hs
  obtain ⟨M1, hM1'⟩ := hb.deriv_bound hs 1
  have hM1 : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ ≤ M1 := fun z => hM1' s ⟨hs, le_rfl⟩ z
  have hM0' : ∀ z : Plane, ‖tr.v s z‖ ≤ M0 := fun z => hM0 s ⟨hs, le_rfl⟩ z
  have hM0nn : 0 ≤ M0 := le_trans (norm_nonneg _) (hM0' 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (2 * (M0 + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hε (by linarith)
  obtain ⟨R, hR⟩ := bucStress_v2_sup_decay tr hs hM1 δ hδpos
  refine Filter.eventually_atTop.2 ⟨R, fun η hη => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have habs : |meanStress tr s η| ≤ M0 * δ := by
    unfold meanStress
    apply bucStress_hmean_abs_le hc
    intro q
    rw [abs_mul]
    have h0 : |tr.v s (q, η) 0| ≤ M0 := by
      have := PiLp.norm_apply_le (tr.v s (q, η)) 0
      simp only [Real.norm_eq_abs] at this
      exact le_trans this (hM0' _)
    exact mul_le_mul h0 (hR η hη q) (abs_nonneg _) hM0nn
  have hlt : M0 * δ < ε := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ (mul_pos two_pos (by linarith))]
    nlinarith
  linarith

end UnforcedLeray.Short.PartI
