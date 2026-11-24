import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.GradSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.L0Far
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.SliceBridge
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# Far-field pointwise bound for the inlet source (helper for `ProdHom`)

Source `the November 2 reference manuscript`
lines 2542-2549 (`∂_j L₀E = -ν∂_jΔE` on the drift-free far set), 2563-2569 (slice bridge),
1206-1222 (homogeneous raw field). At a far point `z` with `ρ = ϱ(z.2) ≥ 1`, `s = 1 + |z.2₃|/ρ`,
the derivative `∂_j` of `L₀E + (u·∇)E + (E·∇)G` is bounded by `K ρ^{-3} s^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProdHom

theorem contDiff_dtau_fn (E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (hE : ContDiff ℝ ∞ E) : ContDiff ℝ ∞ (dτ E) := by
  unfold dτ
  exact (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem diff_L0 (ν : ℝ) (E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (hE : ContDiff ℝ ∞ E) (z : ℝ × UnforcedLeray.Space) :
    DifferentiableAt ℝ (UnforcedLeray.B0411.L0 ν E) z := by
  have h1 : ContDiff ℝ ∞ (dτ E) := contDiff_dtau_fn E hE
  have h2 : ContDiff ℝ ∞ (fun p => (1 / 2 : ℝ) • UnforcedLeray.PhaseSpace.radialT E p) :=
    (UnforcedLeray.PhaseSpace.contDiff_radialT hE).const_smul (1 / 2 : ℝ)
  have h3 : ContDiff ℝ ∞ (fun p => ν • UnforcedLeray.PhaseSpace.lapT E p) :=
    (UnforcedLeray.PhaseSpace.contDiff_lapT hE).const_smul ν
  have h4 : ContDiff ℝ ∞ (fun p => (1 / 2 : ℝ) • E p) := hE.const_smul (1 / 2 : ℝ)
  have hc : ContDiff ℝ ∞ (fun p => (dτ E p - (1 / 2 : ℝ) • UnforcedLeray.PhaseSpace.radialT E p)
      - ν • UnforcedLeray.PhaseSpace.lapT E p - (1 / 2 : ℝ) • E p) :=
    ((h1.sub h2).sub h3).sub h4
  exact (hc.differentiable (by simp)) z

theorem dy_add_pt (j : Fin 3)
    (f g : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (x : ℝ × UnforcedLeray.Space)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dy j (fun z => f z + g z) x = dy j f x + dy j g x := by
  simp only [dy]
  rw [fderiv_fun_add hf hg]
  simp

theorem sum_fin3_le (f : Fin 3 → UnforcedLeray.PhaseSpace.CVec3) (K : ℝ)
    (h : ∀ k, ‖f k‖ ≤ K) : ‖∑ k, f k‖ ≤ 3 * K := by
  calc ‖∑ k, f k‖ ≤ ∑ k, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 3, K := Finset.sum_le_sum (fun k _ => h k)
    _ = 3 * K := by simp

/-- Coordinate of a `ℂ³`-valued derivative: `|∂_j(G·k)| ≤ |∂_j G|`. -/
theorem norm_dy_apply_k_le (j k : Fin 3)
    (G : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (x : ℝ × UnforcedLeray.Space)
    (hG : DifferentiableAt ℝ G x) :
    ‖dy j (fun z => G z k) x‖ ≤ ‖dy j G x‖ := by
  rw [dy_apply_k j k G x hG]
  exact norm_apply_k_le _ k

/-- Real-valued component of `∂_j(realC∘G)`: bounded by `|∂_jG|`. -/
theorem norm_dy_realC_apply_k_le (j k : Fin 3)
    (G : ℝ × UnforcedLeray.Space → UnforcedLeray.Space) (x : ℝ × UnforcedLeray.Space)
    (hG : DifferentiableAt ℝ G x) :
    ‖dy j (fun z => UnforcedLeray.B0412.realC (G z) k) x‖ ≤ ‖dy j G x‖ := by
  have hR : DifferentiableAt ℝ (fun z => UnforcedLeray.B0412.realC (G z)) x :=
    (realCLI.toContinuousLinearMap.differentiableAt).comp x hG
  rw [dy_apply_k j k (fun z => UnforcedLeray.B0412.realC (G z)) x hR,
    dy_realC_pt j G x hG]
  calc ‖UnforcedLeray.B0412.realC (dy j G x) k‖ ≤ ‖UnforcedLeray.B0412.realC (dy j G x)‖ :=
        norm_apply_k_le _ k
    _ = ‖dy j G x‖ := norm_realC_eq _

/-- **Far pointwise bound for `∂_j` of the inlet source.** Assumes the far-field raw bounds
(`hR`, `k ≤ 2`) and inlet bounds (`hEb`, `k ≤ 3`) at the slice through `z`, drift cancellation
on the open set `U`, and `ρ, s ≥ 1`. -/
theorem far_point (ν : ℝ) (j : Fin 3)
    (E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (G : ℝ × UnforcedLeray.Space → UnforcedLeray.Space)
    (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U) (hE : ContDiff ℝ ∞ E)
    (hGU : ContDiffOn ℝ ∞ G U)
    (hdrift : ∀ x ∈ U, dτ E x - (1 / 2 : ℝ) • radialT E x - (1 / 2 : ℝ) • E x = 0)
    (z : ℝ × UnforcedLeray.Space) (hz : z ∈ U) (M : ℕ) (CR CE ρ s : ℝ)
    (hρ : 1 ≤ ρ) (hs : 1 ≤ s) (hCR : 0 ≤ CR) (hCE : 0 ≤ CE)
    (hR : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun w => G (z.1, w)) z.2‖ ≤
      CR * (ρ ^ (-(1 + (k : ℝ))) * s ^ M))
    (hEb : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (fun w => E (z.1, w)) z.2‖ ≤
      CE * (ρ ^ (-(1 + (k : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :
    ‖dy j (fun w => UnforcedLeray.B0411.L0 ν E w +
        UnforcedLeray.Cons.C03.Concrete.advT (fun x => UnforcedLeray.B0412.realC (G x)) E w +
        gradAlong (fun t y => G (t, y)) E w) z‖ ≤
      (|ν| * (3 * CE) + 12 * (CR * CE)) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  set P : ℝ := ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hρ0 : 0 < ρ := by linarith
  have hs0 : 0 < s := by linarith
  have hGz : DifferentiableAt ℝ G z := (hGU.differentiableOn (by simp)).differentiableAt
    (hU.mem_nhds hz)
  have hEz : DifferentiableAt ℝ E z := (hE.differentiable (by simp)) z
  -- raw and inlet slice bounds through `z`
  have hR0 : ‖G z‖ ≤ CR * (ρ ^ (-(1 + ((0 : ℕ) : ℝ))) * s ^ M) := by
    have h := hR 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  have hE0 : ‖E z‖ ≤ CE * (ρ ^ (-(1 + ((0 : ℕ) : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ))) := by
    have h := hEb 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  have hRd : ∀ k : Fin 3, ‖dy k G z‖ ≤ CR * (ρ ^ (-(1 + ((1 : ℕ) : ℝ))) * s ^ M) := by
    intro k
    exact ((sliceBridge UnforcedLeray.Space G U hU hGU z hz k k k).1).trans (hR 1 (by norm_num))
  have hRdd : ∀ k : Fin 3, ‖dy j (dy k G) z‖ ≤ CR * (ρ ^ (-(1 + ((2 : ℕ) : ℝ))) * s ^ M) := by
    intro k
    exact ((sliceBridge UnforcedLeray.Space G U hU hGU z hz j k k).2.1).trans (hR 2 (by norm_num))
  have hEd1 : ∀ k : Fin 3, ‖dy k E z‖ ≤ CE * (ρ ^ (-(1 + ((1 : ℕ) : ℝ))) *
      s ^ (-((M + 2 : ℕ) : ℝ))) := by
    intro k
    exact ((sliceBridge UnforcedLeray.PhaseSpace.CVec3 E U hU hE.contDiffOn z hz k k k).1).trans
      (hEb 1 (by norm_num))
  have hEd2 : ∀ k : Fin 3, ‖dy j (dy k E) z‖ ≤
      CE * (ρ ^ (-(1 + ((2 : ℕ) : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ))) := by
    intro k
    exact ((sliceBridge UnforcedLeray.PhaseSpace.CVec3 E U hU hE.contDiffOn z hz j k k).2.1).trans
      (hEb 2 (by norm_num))
  have hEd3 : ∀ k : Fin 3, ‖dy j (dy k (dy k E)) z‖ ≤
      CE * (ρ ^ (-(1 + ((3 : ℕ) : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ))) := by
    intro k
    exact ((sliceBridge UnforcedLeray.PhaseSpace.CVec3 E U hU hE.contDiffOn z hz j k k).2.2).trans
      (hEb 3 (by norm_num))
  -- differentiability
  have hdk : ∀ k : Fin 3, DifferentiableAt ℝ (fun w => UnforcedLeray.B0412.realC (dy k G w)) z :=
    fun k => (realCLI.toContinuousLinearMap.differentiableAt).comp z
      (diffAt_dy_of_contDiffOn G U hU hGU k z hz)
  have hdEE : ∀ k : Fin 3, DifferentiableAt ℝ (dy k (dy k E)) z := fun k =>
    diff_dy_of_contDiff (dy k E) (dy_contDiff k E hE) k z
  have huz : DifferentiableAt ℝ (fun w => UnforcedLeray.B0412.realC (G w)) z :=
    (realCLI.toContinuousLinearMap.differentiableAt).comp z hGz
  have hu : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z :=
    fun k => diffAt_apply_k k _ z huz
  have hadv : DifferentiableAt ℝ (UnforcedLeray.Cons.C03.Concrete.advT
      (fun x => UnforcedLeray.B0412.realC (G x)) E) z := by
    have hfun : UnforcedLeray.Cons.C03.Concrete.advT (fun x => UnforcedLeray.B0412.realC (G x)) E =
        fun w => ∑ k : Fin 3, (fun x => UnforcedLeray.B0412.realC (G x)) w k • dy k E w := rfl
    rw [hfun]
    exact DifferentiableAt.fun_sum (fun k _ => (hu k).smul (diff_dy_of_contDiff E hE k z))
  have hgrad : DifferentiableAt ℝ (gradAlong (fun t y => G (t, y)) E) z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (gradAlong_eq_nhds G E U hU hGU z hz)
    exact DifferentiableAt.fun_sum (fun k _ => (diffAt_apply_k k E z hEz).smul (hdk k))
  have hL0 := diff_L0 ν E hE z
  have e1 := dy_add_pt j (fun w => UnforcedLeray.B0411.L0 ν E w +
      UnforcedLeray.Cons.C03.Concrete.advT (fun x => UnforcedLeray.B0412.realC (G x)) E w)
    (gradAlong (fun t y => G (t, y)) E) z (hL0.fun_add hadv) hgrad
  have e2 := dy_add_pt j (UnforcedLeray.B0411.L0 ν E)
    (UnforcedLeray.Cons.C03.Concrete.advT (fun x => UnforcedLeray.B0412.realC (G x)) E) z hL0 hadv
  have hdecomp : dy j (fun w => UnforcedLeray.B0411.L0 ν E w +
        UnforcedLeray.Cons.C03.Concrete.advT (fun x => UnforcedLeray.B0412.realC (G x)) E w +
        gradAlong (fun t y => G (t, y)) E w) z =
      -(ν • dy j (lapT E) z) +
        (∑ k : Fin 3, (fun x => UnforcedLeray.B0412.realC (G x)) z k • dy j (dy k E) z +
          ∑ k : Fin 3, dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z •
            dy k E z) +
        ∑ k : Fin 3, (dy j (fun w => E w k) z • UnforcedLeray.B0412.realC (dy k G z) +
          E z k • UnforcedLeray.B0412.realC (dy j (dy k G) z)) := by
    rw [e1, e2, dy_L0_far ν E U hU hE hdrift j z hz,
      dy_advT_pt j (fun x => UnforcedLeray.B0412.realC (G x)) E z hu hE,
      dy_gradAlong_pt j G E U hU hGU hE z hz]
  -- bounds
  have hLap : ‖dy j (lapT E) z‖ ≤ 3 * (CE * P) := by
    have hEq : dy j (lapT E) z = ∑ k : Fin 3, dy j (dy k (dy k E)) z :=
      dy_finset_sum_pt Finset.univ (fun k p => dy k (dy k E) p) z j (fun k _ => hdEE k)
    rw [hEq]
    apply sum_fin3_le
    intro k
    exact single_bound _ CE ρ s (M + 2) (by omega) hρ hs hCE (hEd3 k)
  have hL0b : ‖-(ν • dy j (lapT E) z)‖ ≤ |ν| * (3 * (CE * P)) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hLap (abs_nonneg ν)
  have hT1 : ∀ k : Fin 3, ‖(fun x => UnforcedLeray.B0412.realC (G x)) z k • dy j (dy k E) z‖ ≤
      (CR * CE) * P := by
    intro k
    rw [norm_smul]
    have hX : ‖(fun x => UnforcedLeray.B0412.realC (G x)) z k‖ ≤
        CR * (ρ ^ (-(1 + ((0 : ℕ) : ℝ))) * s ^ M) :=
      (norm_apply_k_le _ k).trans (by rw [norm_realC_eq]; exact hR0)
    exact prod_bound _ _ CR CE ρ s M 0 2 (by norm_num) hρ hs hCR hCE (norm_nonneg _) hX (hEd2 k)
  have hT2 : ∀ k : Fin 3, ‖dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z •
      dy k E z‖ ≤ (CR * CE) * P := by
    intro k
    rw [norm_smul]
    have hX : ‖dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z‖ ≤
        CR * (ρ ^ (-(1 + ((1 : ℕ) : ℝ))) * s ^ M) :=
      (norm_dy_realC_apply_k_le j k G z hGz).trans (hRd j)
    exact prod_bound _ _ CR CE ρ s M 1 1 (by norm_num) hρ hs hCR hCE (norm_nonneg _) hX (hEd1 k)
  have hT3 : ∀ k : Fin 3, ‖dy j (fun w => E w k) z • UnforcedLeray.B0412.realC (dy k G z)‖ ≤
      (CR * CE) * P := by
    intro k
    have h := prod_bound (‖dy k G z‖) (‖dy j (fun w => E w k) z‖) CR CE ρ s M 1 1
      (by norm_num) hρ hs hCR hCE (norm_nonneg _) (hRd k)
      ((norm_dy_apply_k_le j k E z hEz).trans (hEd1 j))
    rw [norm_smul, norm_realC_eq]
    linarith [mul_comm ‖dy j (fun w => E w k) z‖ ‖dy k G z‖]
  have hT4 : ∀ k : Fin 3, ‖E z k • UnforcedLeray.B0412.realC (dy j (dy k G) z)‖ ≤
      (CR * CE) * P := by
    intro k
    have h := prod_bound (‖dy j (dy k G) z‖) (‖E z k‖) CR CE ρ s M 2 0
      (by norm_num) hρ hs hCR hCE (norm_nonneg _) (hRdd k) ((norm_apply_k_le _ k).trans hE0)
    rw [norm_smul, norm_realC_eq]
    linarith [mul_comm ‖E z k‖ ‖dy j (dy k G) z‖]
  have hB1 := sum_fin3_le (fun k => (fun x => UnforcedLeray.B0412.realC (G x)) z k •
      dy j (dy k E) z) ((CR * CE) * P) hT1
  have hB2 := sum_fin3_le (fun k => dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k)
      z • dy k E z) ((CR * CE) * P) hT2
  have hC := sum_fin3_le (fun k => dy j (fun w => E w k) z • UnforcedLeray.B0412.realC (dy k G z) +
      E z k • UnforcedLeray.B0412.realC (dy j (dy k G) z)) (2 * ((CR * CE) * P))
    (fun k => by
      have h1 := norm_add_le (dy j (fun w => E w k) z • UnforcedLeray.B0412.realC (dy k G z))
        (E z k • UnforcedLeray.B0412.realC (dy j (dy k G) z))
      linarith [hT3 k, hT4 k])
  rw [hdecomp]
  have hsplit1 := norm_add_le (-(ν • dy j (lapT E) z) + (∑ k : Fin 3,
      (fun x => UnforcedLeray.B0412.realC (G x)) z k • dy j (dy k E) z +
        ∑ k : Fin 3, dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z •
          dy k E z))
    (∑ k : Fin 3, (dy j (fun w => E w k) z • UnforcedLeray.B0412.realC (dy k G z) +
      E z k • UnforcedLeray.B0412.realC (dy j (dy k G) z)))
  have hsplit2 := norm_add_le (-(ν • dy j (lapT E) z))
    (∑ k : Fin 3, (fun x => UnforcedLeray.B0412.realC (G x)) z k • dy j (dy k E) z +
        ∑ k : Fin 3, dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z •
          dy k E z)
  have hsplit3 := norm_add_le (∑ k : Fin 3, (fun x => UnforcedLeray.B0412.realC (G x)) z k •
      dy j (dy k E) z)
    (∑ k : Fin 3, dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z • dy k E z)
  calc _ ≤ ‖-(ν • dy j (lapT E) z)‖ + (‖∑ k : Fin 3, (fun x => UnforcedLeray.B0412.realC (G x)) z k •
      dy j (dy k E) z‖ + ‖∑ k : Fin 3, dy j (fun w => (fun x => UnforcedLeray.B0412.realC (G x)) w k) z •
      dy k E z‖) + ‖∑ k : Fin 3, (dy j (fun w => E w k) z • UnforcedLeray.B0412.realC (dy k G z) +
      E z k • UnforcedLeray.B0412.realC (dy j (dy k G) z))‖ := by
        linarith
    _ ≤ |ν| * (3 * (CE * P)) + (3 * ((CR * CE) * P) + 3 * ((CR * CE) * P)) +
        3 * (2 * ((CR * CE) * P)) := by linarith
    _ = (|ν| * (3 * CE) + 12 * (CR * CE)) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
        rw [hP]; ring

end UnforcedLeray.Short.PartIIIb.Concrete.ProdHom
