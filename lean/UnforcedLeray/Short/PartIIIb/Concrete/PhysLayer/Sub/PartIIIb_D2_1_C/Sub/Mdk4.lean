import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2

/-!
# `DyPerK`: differentiation of the locally finite periodisation of the reflected kernel

Source: `the November 2 reference manuscript` lines 1351-1362.
Near a fixed point `w0`, only finitely many `k` contribute to `φ_x(w) = ∑_k κ_x(w + (kP, 0))`,
because `κ_x` is supported in a closed ball. So `φ_x` is a finite sum of translates of `κ_x`
on a neighbourhood of `w0`, and its derivative is the termwise sum.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem dyPerK : DyPerK := by
  intro ρ x P hP j w0
  have hκ1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed.of_le (by exact_mod_cast le_top)
  have hκd : Differentiable ℝ (ρ.normed volume) := hκ1.differentiable (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |x.1 - w0.1| + ρ.rOut + 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ⌈A / P⌉ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S = Finset.Icc (-N) N := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℝ × Space → ℂ,
      F = fun (k : ℤ) (w : ℝ × Space) => reflK ρ x (w + ((k : ℝ) * P, (0 : Space))) := ⟨_, rfl⟩
  -- outside the window, the translated kernel vanishes near w0
  have hvanish : ∀ w ∈ Metric.ball w0 1, ∀ k : ℤ, k ∉ S → F k w = 0 := by
    intro w hw k hk
    by_contra hne
    apply hk
    have hreflne : ρ.normed volume (x - (w + ((k : ℝ) * P, (0 : Space)))) ≠ 0 := by
      intro h0
      apply hne
      rw [hF]
      show ((ρ.normed volume (x - (w + ((k : ℝ) * P, (0 : Space)))) : ℝ) : ℂ) = 0
      rw [h0]
      simp
    have hmem : x - (w + ((k : ℝ) * P, (0 : Space))) ∈ Metric.closedBall (0 : ℝ × Space) ρ.rOut := by
      by_contra hn
      exact hreflne (normed_eq_zero_of_not_mem ρ hn)
    have hnorm : ‖x - (w + ((k : ℝ) * P, (0 : Space)))‖ ≤ ρ.rOut :=
      mem_closedBall_zero_iff.mp hmem
    have h1 : |x.1 - (w.1 + (k : ℝ) * P)| ≤ ρ.rOut := by
      have h := norm_fst_le (x - (w + ((k : ℝ) * P, (0 : Space))))
      simp only [Prod.fst_sub, Prod.fst_add, Real.norm_eq_abs] at h
      linarith
    have hw1 : |w.1 - w0.1| ≤ 1 := by
      have h := norm_fst_le (w - w0)
      rw [Metric.mem_ball, dist_eq_norm] at hw
      simp only [Prod.fst_sub, Real.norm_eq_abs] at h
      linarith
    have hkP : |(k : ℝ) * P| ≤ A := by
      rw [hA, abs_le]
      have hb1 := abs_le.mp h1
      have hb2 := abs_le.mp hw1
      constructor <;> linarith [neg_abs_le (x.1 - w0.1), le_abs_self (x.1 - w0.1), hb1.1, hb1.2,
        hb2.1, hb2.2]
    have hk1 : (k : ℝ) ≤ A / P := (le_div_iff₀ hP).mpr (by linarith [le_abs_self ((k : ℝ) * P)])
    have hk2 : -(k : ℝ) ≤ A / P := (le_div_iff₀ hP).mpr (by linarith [neg_abs_le ((k : ℝ) * P)])
    have hk1' : (k : ℝ) ≤ (N : ℝ) := by
      rw [hN]
      exact hk1.trans (Int.le_ceil _)
    have hk2' : -(k : ℝ) ≤ (N : ℝ) := by
      rw [hN]
      exact hk2.trans (Int.le_ceil _)
    have hk1'' : k ≤ N := by exact_mod_cast hk1'
    have hk2'' : -k ≤ N := by exact_mod_cast hk2'
    rw [hS, Finset.mem_Icc]
    constructor <;> omega
  -- the translated kernels are differentiable
  have hFd : ∀ k : ℤ, DifferentiableAt ℝ (F k) w0 := by
    intro k
    have h1 : DifferentiableAt ℝ
        ((ρ.normed volume) ∘ (fun w : ℝ × Space => x - (w + ((k : ℝ) * P, (0 : Space))))) w0 :=
      DifferentiableAt.comp w0 (hκd (x - (w0 + ((k : ℝ) * P, (0 : Space)))))
        (by fun_prop)
    rw [hF]
    exact (Complex.ofRealCLM.differentiableAt).comp w0 h1
  -- translation identity for the derivative of each term
  have hTr : ∀ k : ℤ, fderiv ℝ (F k) w0
      = fderiv ℝ (reflK ρ x) (w0 + ((k : ℝ) * P, (0 : Space))) := by
    intro k
    simp only [hF]
    exact fderiv_comp_add_right _
  -- the periodisation agrees with the finite sum near w0
  have hev2 : perK ρ x P =ᶠ[𝓝 w0] (∑ k ∈ S, F k) := by
    filter_upwards [Metric.ball_mem_nhds w0 one_pos] with w hw
    have e : perK ρ x P w = ∑' k : ℤ, F k w := by
      rw [hF]
      rfl
    rw [e, Finset.sum_apply]
    exact tsum_eq_sum (s := S) (fun k hk => hvanish w hw k hk)
  have hF0 : ∀ k : ℤ, k ∉ S → fderiv ℝ (F k) w0 = 0 := by
    intro k hk
    have hev : F k =ᶠ[𝓝 w0] (fun _ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds w0 one_pos] with w hw
      exact hvanish w hw k hk
    rw [hev.fderiv_eq]
    simp
  have hRHS : ∑' k : ℤ, fderiv ℝ (reflK ρ x) (w0 + ((k : ℝ) * P, (0 : Space))) (0, coordinateVector j)
      = ∑ k ∈ S, fderiv ℝ (F k) w0 (0, coordinateVector j) := by
    calc ∑' k : ℤ, fderiv ℝ (reflK ρ x) (w0 + ((k : ℝ) * P, (0 : Space))) (0, coordinateVector j)
        = ∑' k : ℤ, fderiv ℝ (F k) w0 (0, coordinateVector j) :=
          tsum_congr fun k => by rw [hTr k]
      _ = ∑ k ∈ S, fderiv ℝ (F k) w0 (0, coordinateVector j) :=
          tsum_eq_sum (s := S) fun k hk => by rw [hF0 k hk, zero_apply]
  unfold UnforcedLeray.PhaseSpace.dy
  rw [hev2.fderiv_eq, fderiv_sum (fun k _ => hFd k), ContinuousLinearMap.sum_apply, hRHS]
