import UnforcedLeray.Lib.Kernels.HeatTimePotential

/-!
# INF22 K2: Newton derivatives and Taylor remainders


(§5, bypass BP5). The Newton potential N(x) = (4π|x|)^{-1} is the compiled
`PressureAnalysis.newtonPotential`; off the origin it coincides with Φ₀ = ∫_0^∞ G_a da
(`heatTimePotential_zero`), so its derivatives are integrals of heat-kernel derivatives and obey the
K1 bound. This module proves:

* `contDiffAt_newton`: N is smooth off the origin;
* `norm_iteratedFDeriv_newton_le`: ‖Dᵏ N(x)‖ ≤ Cₖ |x|^{-(1+k)} for x ≠ 0;
* `norm_iteratedFDeriv_newton_sub_le`: ‖Dᵏ N(x − y) − Dᵏ N(x)‖ ≤ Cₖ |y| |x|^{-(2+k)} when
  2|y| ≤ |x| (mean-value inequality along a segment at distance ≥ |x|/2 from 0);
* `norm_iteratedFDeriv_newton_taylor_le`: the first-order Taylor remainder
  ‖Dᵏ N(x − y) − Dᵏ N(x) + D^{k+1} N(x)·y‖ ≤ Cₖ |y|² |x|^{-(3+k)} under the same separation.

These are the multipole-remainder inputs of blueprint units B0567 (tex 9035–9104), B0827
(tex 12233–12244) and B0840 (tex 12398–12412). Harmonicity off the origin is in
`Lib/Kernels/NewtonJets.lean` (it follows from the explicit second-derivative formula).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Nat

namespace UnforcedLeray.Kernels

/-- Off the origin, Φ₀ and N agree on a neighbourhood. -/
theorem heatTimePotential_zero_eventuallyEq {x : Space} (hx : x ≠ 0) :
    heatTimePotential 0 =ᶠ[𝓝 x] PressureAnalysis.newtonPotential :=
  Filter.eventually_of_mem ((isOpen_ne (x := (0 : Space))).mem_nhds hx)
    fun _ hy => heatTimePotential_zero hy

theorem iteratedFDeriv_newton_eventuallyEq (n : ℕ) {x : Space} (hx : x ≠ 0) :
    iteratedFDeriv ℝ n PressureAnalysis.newtonPotential =ᶠ[𝓝 x]
      iteratedFDeriv ℝ n (heatTimePotential 0) :=
  ((heatTimePotential_zero_eventuallyEq hx).iteratedFDeriv ℝ n).symm

/-- Dⁿ N(x) = Dⁿ Φ₀(x) for x ≠ 0. -/
theorem iteratedFDeriv_newton_eq_potential (n : ℕ) {x : Space} (hx : x ≠ 0) :
    iteratedFDeriv ℝ n PressureAnalysis.newtonPotential x =
      iteratedFDeriv ℝ n (heatTimePotential 0) x :=
  (iteratedFDeriv_newton_eventuallyEq n hx).eq_of_nhds

/-- N is smooth off the origin (INF22 K2). -/
theorem contDiffAt_newton {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ PressureAnalysis.newtonPotential x :=
  (contDiffAt_heatTimePotential le_rfl (Or.inl hx)).congr_of_eventuallyEq
    (heatTimePotential_zero_eventuallyEq hx).symm

theorem potentialConst_nonneg (n : ℕ) : 0 ≤ potentialConst n := by
  unfold potentialConst
  have h1 := heatDerivConst_pos n
  have h2 : 0 < Real.Gamma ((1 + n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- ‖Dᵏ N(x)‖ ≤ Cₖ |x|^{-(1+k)} with the explicit constant of K1. -/
theorem norm_iteratedFDeriv_newton_le' (k : ℕ) {x : Space} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential x‖ ≤
      potentialConst k * ‖x‖ ^ (-(1 + k : ℝ)) := by
  rw [iteratedFDeriv_newton_eq_potential k hx]
  exact norm_iteratedFDeriv_heatTimePotential_le' k le_rfl hx

/-- INF22 K2 `norm_iteratedFDeriv_newton_le` (BP5): ‖Dᵏ N(x)‖ ≤ Cₖ |x|^{-(1+k)} for x ≠ 0. -/
theorem norm_iteratedFDeriv_newton_le (k : ℕ) : ∃ C, ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential x‖ ≤ C * ‖x‖ ^ (-(1 + k : ℝ)) :=
  ⟨potentialConst k, fun _ hx => norm_iteratedFDeriv_newton_le' k hx⟩

/-! ### Segments that stay away from the origin -/

theorem half_le_norm_of_mem_closedBall {x y z : Space} (hxy : 2 * ‖y‖ ≤ ‖x‖)
    (hz : z ∈ closedBall x ‖y‖) : ‖x‖ / 2 ≤ ‖z‖ := by
  have h1 : ‖z - x‖ ≤ ‖y‖ := by rw [← dist_eq_norm]; exact hz
  have h2 := norm_sub_norm_le x z
  rw [norm_sub_rev] at h2
  linarith

theorem ne_zero_of_mem_closedBall {x y z : Space} (hx : x ≠ 0) (hxy : 2 * ‖y‖ ≤ ‖x‖)
    (hz : z ∈ closedBall x ‖y‖) : z ≠ 0 := by
  have h := half_le_norm_of_mem_closedBall hxy hz
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- `z^{-s} ≤ 2^s x^{-s}` when `x/2 ≤ z`, `x > 0`, `s ≥ 0`. -/
theorem rpow_neg_le_of_half_le {x z : ℝ} (hx : 0 < x) (hz : x / 2 ≤ z) {s : ℝ} (hs : 0 ≤ s) :
    z ^ (-s) ≤ 2 ^ s * x ^ (-s) := by
  have h1 : z ^ (-s) ≤ (x / 2) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hz (by linarith)
  have h2 : (x / 2) ^ (-s) = 2 ^ s * x ^ (-s) := by
    rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) s,
      div_inv_eq_mul, mul_comm]
  rw [h2] at h1
  exact h1

theorem self_mem_closedBall_norm (x y : Space) : x ∈ closedBall x ‖y‖ :=
  mem_closedBall_self (norm_nonneg y)

theorem sub_mem_closedBall_norm (x y : Space) : x - y ∈ closedBall x ‖y‖ := by
  rw [mem_closedBall, dist_eq_norm]
  simp

/-- Differentiability of `Dᵏ N` off the origin. -/
theorem differentiableAt_iteratedFDeriv_newton (k : ℕ) {z : Space} (hz : z ≠ 0) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ k PressureAnalysis.newtonPotential) z :=
  (contDiffAt_newton hz).differentiableAt_iteratedFDeriv
    (mod_cast ENat.natCast_lt_top k)

/-- The mean-value bound with explicit constant. -/
theorem norm_iteratedFDeriv_newton_sub_le' (k : ℕ) {x y : Space} (hxy : 2 * ‖y‖ ≤ ‖x‖)
    (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (x - y) -
        iteratedFDeriv ℝ k PressureAnalysis.newtonPotential x‖ ≤
      2 ^ (2 + k : ℝ) * potentialConst (k + 1) * ‖y‖ * ‖x‖ ^ (-(2 + k : ℝ)) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hbound : ∀ z ∈ closedBall x ‖y‖,
      ‖fderiv ℝ (iteratedFDeriv ℝ k PressureAnalysis.newtonPotential) z‖ ≤
        2 ^ (2 + k : ℝ) * potentialConst (k + 1) * ‖x‖ ^ (-(2 + k : ℝ)) := by
    intro z hz
    have hz0 := ne_zero_of_mem_closedBall hx hxy hz
    rw [norm_fderiv_iteratedFDeriv]
    refine (norm_iteratedFDeriv_newton_le' (k + 1) hz0).trans ?_
    have h1 := rpow_neg_le_of_half_le hx' (half_le_norm_of_mem_closedBall hxy hz)
      (s := 2 + k) (by positivity)
    have h2 : (-(1 + ((k + 1 : ℕ) : ℝ))) = -(2 + k : ℝ) := by push_cast; ring
    rw [h2]
    have h3 := potentialConst_nonneg (k + 1)
    calc potentialConst (k + 1) * ‖z‖ ^ (-(2 + k : ℝ))
        ≤ potentialConst (k + 1) * (2 ^ (2 + k : ℝ) * ‖x‖ ^ (-(2 + k : ℝ))) := by gcongr
      _ = _ := by ring
  have h := (convex_closedBall x ‖y‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => differentiableAt_iteratedFDeriv_newton k
      (ne_zero_of_mem_closedBall hx hxy hz)) hbound
    (self_mem_closedBall_norm x y) (sub_mem_closedBall_norm x y)
  rw [show x - y - x = -y by abel, norm_neg] at h
  calc _ ≤ 2 ^ (2 + k : ℝ) * potentialConst (k + 1) * ‖x‖ ^ (-(2 + k : ℝ)) * ‖y‖ := h
    _ = _ := by ring

/-- INF22 K2 `norm_iteratedFDeriv_newton_sub_le`: for 2|y| ≤ |x|, x ≠ 0,
‖Dᵏ N(x − y) − Dᵏ N(x)‖ ≤ Cₖ |y| |x|^{-(2+k)} (BP5; used by B0840, tex 12398–12412). -/
theorem norm_iteratedFDeriv_newton_sub_le (k : ℕ) : ∃ C, ∀ x y : Space, 2 * ‖y‖ ≤ ‖x‖ → x ≠ 0 →
    ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (x - y) -
        iteratedFDeriv ℝ k PressureAnalysis.newtonPotential x‖ ≤
      C * ‖y‖ * ‖x‖ ^ (-(2 + k : ℝ)) :=
  ⟨2 ^ (2 + k : ℝ) * potentialConst (k + 1), fun _ _ hxy hx =>
    norm_iteratedFDeriv_newton_sub_le' k hxy hx⟩

/-- The first-order Taylor remainder with explicit constant. -/
theorem norm_iteratedFDeriv_newton_taylor_le' (k : ℕ) {x y : Space} (hxy : 2 * ‖y‖ ≤ ‖x‖)
    (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (x - y) -
        iteratedFDeriv ℝ k PressureAnalysis.newtonPotential x +
        fderiv ℝ (iteratedFDeriv ℝ k PressureAnalysis.newtonPotential) x y‖ ≤
      2 ^ (3 + k : ℝ) * potentialConst (k + 2) * ‖y‖ ^ 2 * ‖x‖ ^ (-(3 + k : ℝ)) := by
  set f := iteratedFDeriv ℝ k PressureAnalysis.newtonPotential with hf_def
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  set g := iteratedFDeriv ℝ (k + 1) PressureAnalysis.newtonPotential with hg_def
  -- `g = D^{k+1} N` is Lipschitz on the ball, with constant from D^{k+2} N
  have hbound2 : ∀ z ∈ closedBall x ‖y‖, ‖fderiv ℝ g z‖ ≤
      2 ^ (3 + k : ℝ) * potentialConst (k + 2) * ‖x‖ ^ (-(3 + k : ℝ)) := by
    intro z hz
    have hz0 := ne_zero_of_mem_closedBall hx hxy hz
    rw [hg_def, norm_fderiv_iteratedFDeriv]
    refine (norm_iteratedFDeriv_newton_le' (k + 1 + 1) hz0).trans ?_
    have h1 := rpow_neg_le_of_half_le hx' (half_le_norm_of_mem_closedBall hxy hz)
      (s := 3 + k) (by positivity)
    have h2 : (-(1 + ((k + 1 + 1 : ℕ) : ℝ))) = -(3 + k : ℝ) := by push_cast; ring
    rw [h2]
    have h3 := potentialConst_nonneg (k + 2)
    calc potentialConst (k + 1 + 1) * ‖z‖ ^ (-(3 + k : ℝ))
        ≤ potentialConst (k + 2) * (2 ^ (3 + k : ℝ) * ‖x‖ ^ (-(3 + k : ℝ))) := by gcongr
      _ = _ := by ring
  have hdiff2 : ∀ z ∈ closedBall x ‖y‖, DifferentiableAt ℝ g z := fun z hz =>
    differentiableAt_iteratedFDeriv_newton (k + 1) (ne_zero_of_mem_closedBall hx hxy hz)
  set K := 2 ^ (3 + k : ℝ) * potentialConst (k + 2) * ‖x‖ ^ (-(3 + k : ℝ)) with hK
  -- `fderiv f w` is `g w` up to the currying isometry
  have hfd : ∀ w, fderiv ℝ f w =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) ℝ (g w) := by
    intro w
    rw [hg_def, iteratedFDeriv_succ_eq_comp_left]
    simp [hf_def]
  -- ‖fderiv f z - fderiv f x‖ ≤ K ‖y‖ on the ball
  have hbound1 : ∀ z ∈ closedBall x ‖y‖, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ K * ‖y‖ := by
    intro z hz
    have h := (convex_closedBall x ‖y‖).norm_image_sub_le_of_norm_fderiv_le hdiff2 hbound2
      (self_mem_closedBall_norm x y) hz
    rw [hfd z, hfd x, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
    refine h.trans ?_
    have : ‖z - x‖ ≤ ‖y‖ := by rw [← dist_eq_norm]; exact hz
    have hK0 : 0 ≤ K := by
      have := potentialConst_nonneg (k + 2)
      have : 0 ≤ ‖x‖ ^ (-(3 + k : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      positivity
    gcongr
  have hdiff1 : ∀ z ∈ closedBall x ‖y‖, DifferentiableAt ℝ f z := fun z hz =>
    differentiableAt_iteratedFDeriv_newton k (ne_zero_of_mem_closedBall hx hxy hz)
  have h := (convex_closedBall x ‖y‖).norm_image_sub_le_of_norm_fderiv_le' hdiff1 hbound1
    (self_mem_closedBall_norm x y) (sub_mem_closedBall_norm x y)
  rw [show x - y - x = -y by abel, norm_neg, map_neg, sub_neg_eq_add] at h
  calc _ ≤ K * ‖y‖ * ‖y‖ := h
    _ = _ := by rw [hK]; ring

/-- INF22 K2, first-order Taylor remainder (used in B0567 and B0827): for 2|y| ≤ |x|, x ≠ 0,
‖Dᵏ N(x − y) − Dᵏ N(x) + D^{k+1} N(x)·y‖ ≤ Cₖ |y|² |x|^{-(3+k)}. -/
theorem norm_iteratedFDeriv_newton_taylor_le (k : ℕ) : ∃ C, ∀ x y : Space, 2 * ‖y‖ ≤ ‖x‖ →
    x ≠ 0 →
    ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (x - y) -
        iteratedFDeriv ℝ k PressureAnalysis.newtonPotential x +
        fderiv ℝ (iteratedFDeriv ℝ k PressureAnalysis.newtonPotential) x y‖ ≤
      C * ‖y‖ ^ 2 * ‖x‖ ^ (-(3 + k : ℝ)) :=
  ⟨2 ^ (3 + k : ℝ) * potentialConst (k + 2), fun _ _ hxy hx =>
    norm_iteratedFDeriv_newton_taylor_le' k hxy hx⟩

end UnforcedLeray.Kernels
