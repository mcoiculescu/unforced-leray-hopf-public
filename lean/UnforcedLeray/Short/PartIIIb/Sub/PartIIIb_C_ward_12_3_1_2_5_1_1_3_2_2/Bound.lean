import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.Smul

/-!
The pointwise slice-level product-rule bound for the inlet source (helper for `inletSrcDerivBound`).
Source `the November 2 reference manuscript`
2545-2551, 2563-2569.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Jets

open UnforcedLeray UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412 (realC)

/-- The coordinate unit vector. -/
abbrev ek (k : Fin 3) : UnforcedLeray.Space := EuclideanSpace.single k 1

/-- The time slice of `inletSrc` written with spatial derivatives only. -/
def Sfun (e d : UnforcedLeray.Space → CVec3) (r : UnforcedLeray.Space → UnforcedLeray.Space)
    (ν : ℝ) (x : UnforcedLeray.Space) : CVec3 :=
  d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • fderiv ℝ e x (ek k)
    - ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)
    - (1 / 2 : ℝ) • e x
    + ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)
    + ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (ek k))

theorem arith_bound (ny a0 a1 a2 a3 d0 d1 b0 b1 b2 ν : ℝ) (hny : 0 ≤ ny) (ha0 : 0 ≤ a0)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hb0 : 0 ≤ b0)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hν : |ν| ≤ 1) :
    d1 + (1 / 2) * (3 * (ny * a2 + a1)) + |ν| * (3 * a3) + (1 / 2) * a1 +
      3 * (b0 * a2 + b1 * a1) + 3 * (a0 * b2 + a1 * b1) ≤
    20 * (1 + ny) * (1 + (b0 + b1 + b2)) * ((a0 + a1 + a2 + a3) + (d0 + d1)) := by
  have hA : 0 ≤ (a0 + a1 + a2 + a3) + (d0 + d1) := by positivity
  have h1 : |ν| * (3 * a3) ≤ 3 * a3 := by nlinarith [abs_nonneg ν]
  have h2 : 0 ≤ ny * ((a0 + a1 + a3) + (d0 + d1)) := by positivity
  have h3 : 0 ≤ b0 * ((a0 + a1 + a3) + (d0 + d1)) := by positivity
  have h4 : 0 ≤ b1 * ((a0 + a2 + a3) + (d0 + d1)) := by positivity
  have h5 : 0 ≤ b2 * ((a1 + a2 + a3) + (d0 + d1)) := by positivity
  have h6 : 0 ≤ ny * (b0 + b1 + b2) * ((a0 + a1 + a2 + a3) + (d0 + d1)) := by positivity
  have h7 : 0 ≤ b0 * ((a0 + a1 + a2 + a3) + (d0 + d1)) := by positivity
  have h8 : 0 ≤ b1 * ((a0 + a1 + a2 + a3) + (d0 + d1)) := by positivity
  have h9 : 0 ≤ b2 * ((a0 + a1 + a2 + a3) + (d0 + d1)) := by positivity
  nlinarith


theorem norm6_le {W : Type*} [NormedAddCommGroup W] (a b c d f g : W) :
    ‖a - b - c - d + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (a - b - c - d + f) g
  have h2 := norm_add_le (a - b - c - d) f
  have h3 := norm_sub_le (a - b - c) d
  have h4 := norm_sub_le (a - b) c
  have h5 := norm_sub_le a b
  linarith

theorem sum3_le (c : ℝ) (f : Fin 3 → ℝ) (h : ∀ k, f k ≤ c) : ∑ k, f k ≤ 3 * c := by
  calc ∑ k, f k ≤ ∑ _k : Fin 3, c := Finset.sum_le_sum fun k _ => h k
    _ = 3 * c := by simp

set_option maxHeartbeats 1600000 in
theorem norm_fderiv_Sfun_le {e d : UnforcedLeray.Space → CVec3}
    {r : UnforcedLeray.Space → UnforcedLeray.Space}
    (he : ContDiff ℝ ∞ e) (hd : ContDiff ℝ ∞ d) (hr : ContDiff ℝ ∞ r) {ν : ℝ} (hν : |ν| ≤ 1)
    (y : UnforcedLeray.Space) (j : Fin 3) :
    ‖fderiv ℝ (Sfun e d r ν) y (ek j)‖ ≤ 20 * (1 + ‖y‖) *
      (1 + ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k r y‖) *
      ((∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k e y‖) +
        ∑ k ∈ Finset.range 2, ‖iteratedFDeriv ℝ k d y‖) := by
  have hdf : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : UnforcedLeray.Space → V},
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ (fderiv ℝ F) :=
    fun hF => hF.fderiv_right (m := ∞) (by simp)
  have hGk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => fderiv ℝ e z (ek k)) :=
    fun k => (hdf he).clm_apply contDiff_const
  have hHk : ∀ k : Fin 3, ContDiff ℝ ∞
      (fun z => fderiv ℝ (fun w => fderiv ℝ e w (ek k)) z (ek k)) :=
    fun k => (hdf (hGk k)).clm_apply contDiff_const
  have hRk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => fderiv ℝ r z (ek k)) :=
    fun k => (hdf hr).clm_apply contDiff_const
  have hrk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => ((r z k : ℝ) : ℂ)) := fun k =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply (p := 2) (i := k)).comp hr)
  have hek : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => e z k) := fun k =>
    (contDiff_piLp_apply (p := 2) (i := k)).comp he
  have hxk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => z k) := fun k =>
    contDiff_piLp_apply (p := 2) (i := k)
  have hrealR : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => realC (fderiv ℝ r z (ek k))) := fun k => by
    have : (fun z => realC (fderiv ℝ r z (ek k))) = fun z => realCL (fderiv ℝ r z (ek k)) := by
      funext z; rw [realCL_apply]
    rw [this]; exact realCL.contDiff.comp (hRk k)
  -- derivative pieces
  have h2 : HasFDerivAt (fun x => ∑ k : Fin 3, (x k) • fderiv ℝ e x (ek k))
      (∑ k : Fin 3, fderiv ℝ (fun x => (x k) • fderiv ℝ e x (ek k)) y) y :=
    HasFDerivAt.fun_sum fun k _ =>
      (((hxk k).smul (hGk k)).differentiable (by simp) y).hasFDerivAt
  have h3 : HasFDerivAt (fun x => ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k))
      (∑ k : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y) y :=
    HasFDerivAt.fun_sum fun k _ => ((hHk k).differentiable (by simp) y).hasFDerivAt
  have h5 : HasFDerivAt (fun x => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k))
      (∑ k : Fin 3, fderiv ℝ (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) y) y :=
    HasFDerivAt.fun_sum fun k _ =>
      (((hrk k).smul (hGk k)).differentiable (by simp) y).hasFDerivAt
  have h6 : HasFDerivAt (fun x => ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (ek k)))
      (∑ k : Fin 3, fderiv ℝ (fun x => e x k • realC (fderiv ℝ r x (ek k))) y) y :=
    HasFDerivAt.fun_sum fun k _ =>
      (((hek k).smul (hrealR k)).differentiable (by simp) y).hasFDerivAt
  have hS : HasFDerivAt (Sfun e d r ν)
      (fderiv ℝ d y - (1 / 2 : ℝ) • (∑ k : Fin 3, fderiv ℝ (fun x => (x k) • fderiv ℝ e x (ek k)) y)
        - ν • (∑ k : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y)
        - (1 / 2 : ℝ) • fderiv ℝ e y
        + ∑ k : Fin 3, fderiv ℝ (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) y
        + ∑ k : Fin 3, fderiv ℝ (fun x => e x k • realC (fderiv ℝ r x (ek k))) y) y := by
    have g1 : HasFDerivAt d (fderiv ℝ d y) y := (hd.differentiable (by simp) y).hasFDerivAt
    have g4 : HasFDerivAt e (fderiv ℝ e y) y := (he.differentiable (by simp) y).hasFDerivAt
    have k2 := g1.sub (h2.const_smul (1 / 2 : ℝ))
    have k3 := k2.sub (h3.const_smul ν)
    have k4 := k3.sub (g4.const_smul (1 / 2 : ℝ))
    have k5 := k4.add h5
    have k6 := k5.add h6
    exact k6
  rw [hS.fderiv]
  simp only [add_apply, sub_apply,
    smul_apply, sum_apply]
  -- notation for jets
  have hej : ‖ek j‖ = 1 := norm_single_one j
  have hek1 : ∀ k : Fin 3, ‖ek k‖ = 1 := fun k => norm_single_one k
  set a0 := ‖iteratedFDeriv ℝ 0 e y‖ with ha0
  set a1 := ‖iteratedFDeriv ℝ 1 e y‖ with ha1
  set a2 := ‖iteratedFDeriv ℝ 2 e y‖ with ha2
  set a3 := ‖iteratedFDeriv ℝ 3 e y‖ with ha3
  set d0 := ‖iteratedFDeriv ℝ 0 d y‖ with hd0
  set d1 := ‖iteratedFDeriv ℝ 1 d y‖ with hd1
  set b0 := ‖iteratedFDeriv ℝ 0 r y‖ with hb0
  set b1 := ‖iteratedFDeriv ℝ 1 r y‖ with hb1
  set b2 := ‖iteratedFDeriv ℝ 2 r y‖ with hb2
  have n_a0 : 0 ≤ a0 := norm_nonneg _
  have n_a1 : 0 ≤ a1 := norm_nonneg _
  have n_a2 : 0 ≤ a2 := norm_nonneg _
  have n_a3 : 0 ≤ a3 := norm_nonneg _
  have n_d0 : 0 ≤ d0 := norm_nonneg _
  have n_d1 : 0 ≤ d1 := norm_nonneg _
  have n_b0 : 0 ≤ b0 := norm_nonneg _
  have n_b1 : 0 ≤ b1 := norm_nonneg _
  have n_b2 : 0 ≤ b2 := norm_nonneg _
  have n_y : 0 ≤ ‖y‖ := norm_nonneg _
  have e0 : ‖e y‖ = a0 := by rw [ha0, norm_iteratedFDeriv_zero]
  have r0 : ‖r y‖ = b0 := by rw [hb0, norm_iteratedFDeriv_zero]
  -- first-order bounds
  have bE1 : ∀ k : Fin 3, ‖fderiv ℝ e y (ek k)‖ ≤ a1 := fun k => by
    have := norm_jet1 (F := e) y (ek k); rwa [hek1, mul_one] at this
  have bD1 : ‖fderiv ℝ d y (ek j)‖ ≤ d1 := by
    have := norm_jet1 (F := d) y (ek j); rwa [hej, mul_one] at this
  have bR1 : ∀ k : Fin 3, ‖fderiv ℝ r y (ek k)‖ ≤ b1 := fun k => by
    have := norm_jet1 (F := r) y (ek k); rwa [hek1, mul_one] at this
  have bE2 : ∀ k : Fin 3, ‖fderiv ℝ (fun z => fderiv ℝ e z (ek k)) y (ek j)‖ ≤ a2 := fun k => by
    have := norm_jet2 he (ek k) y (ek j); rwa [hek1, hej, mul_one, mul_one] at this
  have bR2 : ∀ k : Fin 3, ‖fderiv ℝ (fun z => fderiv ℝ r z (ek k)) y (ek j)‖ ≤ b2 := fun k => by
    have := norm_jet2 hr (ek k) y (ek j); rwa [hek1, hej, mul_one, mul_one] at this
  have bE3 : ∀ k : Fin 3, ‖fderiv ℝ (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y
      (ek j)‖ ≤ a3 := fun k => by
    have := norm_jet3 he (ek k) y (ek j); rwa [hek1, hej, mul_one, mul_one, mul_one] at this
  -- piece 2
  have P2 : ∀ k : Fin 3, ‖fderiv ℝ (fun x => (x k) • fderiv ℝ e x (ek k)) y (ek j)‖ ≤
      ‖y‖ * a2 + a1 := fun k => by
    refine (norm_fderiv_smul_le (𝕜 := ℝ) ((hxk k).differentiable (by simp) y)
      (((hGk k).differentiable (by simp)) y) (ek j)).trans ?_
    have c1 : ‖y k‖ ≤ ‖y‖ := by
      have := abs_coord_le (𝕜 := ℝ) y k; simpa using this
    have c2 : ‖fderiv ℝ (fun x : UnforcedLeray.Space => x k) y (ek j)‖ ≤ 1 := by
      have := fderiv_coord (𝕜 := ℝ) (f := fun z : UnforcedLeray.Space => z) (y := y)
        (differentiableAt_id) k (ek j)
      simp only [fderiv_fun_id] at this
      show ‖fderiv ℝ (fun x : UnforcedLeray.Space => x k) y (ek j)‖ ≤ 1
      rw [this]
      calc _ ≤ ‖ek j‖ := by simpa using abs_coord_le (𝕜 := ℝ) (ek j) k
        _ = 1 := hej
    calc _ ≤ ‖y‖ * a2 + 1 * a1 := by
          gcongr
          · exact (bE2 k)
          · exact bE1 k
      _ = _ := by ring
  have P5 : ∀ k : Fin 3, ‖fderiv ℝ (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) y (ek j)‖ ≤
      b0 * a2 + b1 * a1 := fun k => by
    refine (norm_fderiv_smul_le (𝕜 := ℂ) ((hrk k).differentiable (by simp) y)
      (((hGk k).differentiable (by simp)) y) (ek j)).trans ?_
    have c1 : ‖((r y k : ℝ) : ℂ)‖ ≤ b0 := by
      rw [← r0]; simpa using abs_coord_le (𝕜 := ℝ) (r y) k
    have c2 : ‖fderiv ℝ (fun x => ((r x k : ℝ) : ℂ)) y (ek j)‖ ≤ b1 := by
      rw [fderiv_ofReal_coord (hr.differentiable (by simp) y)]
      calc _ ≤ ‖fderiv ℝ r y (ek j)‖ := by
              simpa using abs_coord_le (𝕜 := ℝ) (fderiv ℝ r y (ek j)) k
        _ ≤ b1 := bR1 j
    gcongr
    · exact bE2 k
    · exact bE1 k
  have P6 : ∀ k : Fin 3, ‖fderiv ℝ (fun x => e x k • realC (fderiv ℝ r x (ek k))) y (ek j)‖ ≤
      a0 * b2 + a1 * b1 := fun k => by
    refine (norm_fderiv_smul_le (𝕜 := ℂ) ((hek k).differentiable (by simp) y)
      ((hrealR k).differentiable (by simp) y) (ek j)).trans ?_
    have c1 : ‖e y k‖ ≤ a0 := by rw [← e0]; exact abs_coord_le (𝕜 := ℂ) (e y) k
    have c2 : ‖fderiv ℝ (fun x => e x k) y (ek j)‖ ≤ a1 := by
      rw [fderiv_coord (he.differentiable (by simp) y)]
      exact (abs_coord_le (𝕜 := ℂ) _ k).trans (bE1 j)
    have c3 : ‖fderiv ℝ (fun x => realC (fderiv ℝ r x (ek k))) y (ek j)‖ ≤ b2 := by
      rw [fderiv_realC ((hRk k).differentiable (by simp) y), norm_realC]
      exact bR2 k
    have c4 : ‖realC (fderiv ℝ r y (ek k))‖ ≤ b1 := by
      rw [norm_realC]; exact bR1 k
    gcongr
  have s2 := sum3_le _ _ P2
  have s5 := sum3_le _ _ P5
  have s6 := sum3_le _ _ P6
  have s3 := sum3_le a3 _ bE3
  have n2 : ‖∑ k : Fin 3, fderiv ℝ (fun x => (x k) • fderiv ℝ e x (ek k)) y (ek j)‖ ≤
      3 * (‖y‖ * a2 + a1) := (norm_sum_le _ _).trans s2
  have n3 : ‖∑ k : Fin 3, fderiv ℝ
      (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y (ek j)‖ ≤ 3 * a3 :=
    (norm_sum_le _ _).trans s3
  have n5 : ‖∑ k : Fin 3, fderiv ℝ (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) y (ek j)‖ ≤
      3 * (b0 * a2 + b1 * a1) := (norm_sum_le _ _).trans s5
  have n6 : ‖∑ k : Fin 3, fderiv ℝ (fun x => e x k • realC (fderiv ℝ r x (ek k))) y (ek j)‖ ≤
      3 * (a0 * b2 + a1 * b1) := (norm_sum_le _ _).trans s6
  have n4 : ‖fderiv ℝ e y (ek j)‖ ≤ a1 := bE1 j
  have total : ‖fderiv ℝ d y (ek j) - (1 / 2 : ℝ) • (∑ k : Fin 3, fderiv ℝ (fun x => (x k) • fderiv ℝ e x (ek k)) y (ek j))
        - ν • (∑ k : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y (ek j))
        - (1 / 2 : ℝ) • fderiv ℝ e y (ek j)
        + ∑ k : Fin 3, fderiv ℝ (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) y (ek j)
        + ∑ k : Fin 3, fderiv ℝ (fun x => e x k • realC (fderiv ℝ r x (ek k))) y (ek j)‖ ≤
      d1 + (1 / 2) * (3 * (‖y‖ * a2 + a1)) + |ν| * (3 * a3) + (1 / 2) * a1 +
        3 * (b0 * a2 + b1 * a1) + 3 * (a0 * b2 + a1 * b1) := by
    refine (norm6_le _ _ _ _ _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := mul_le_mul_of_nonneg_left n2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have := mul_le_mul_of_nonneg_left n3 (abs_nonneg ν)
    have := mul_le_mul_of_nonneg_left n4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith
  refine total.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have := arith_bound ‖y‖ a0 a1 a2 a3 d0 d1 b0 b1 b2 ν n_y n_a0 n_a1 n_a2 n_a3 n_d0 n_d1 n_b0 n_b1 n_b2 hν
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete.Jets

end
