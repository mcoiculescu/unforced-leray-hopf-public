import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftTestPhase

/-!
# `ShiftTestOpEq`: the operator on the periodised translate of a bump

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
Near a point `w` the periodised sum is a finite sum over a window `Icc (-N) N`; all derivatives
are then computed by the chain rule on translates `w ↦ κ(x - w + (kP, 0))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Far translates: for `w` in the unit ball about `w0` and `k` outside the window, the translate
lies outside the support radius. -/
lemma far_of_notMem {R0 P : ℝ} (hP : 0 < P) (x w w0 : ℝ × Space) (hw : w ∈ Metric.ball w0 1)
    (N : ℕ) (hN : (R0 + ‖x‖ + ‖w0‖ + 1) / P ≤ N) (k : ℤ) (hk : k ∉ Finset.Icc (-(N : ℤ)) N) :
    R0 < ‖x - w + ((k : ℝ) * P, 0)‖ := by
  by_contra hle
  push_neg at hle
  have hwn : ‖w‖ ≤ ‖w0‖ + 1 := by
    have h1 := mem_ball_iff_norm.1 hw
    have h2 := norm_sub_norm_le w w0
    linarith
  set v := x - w + ((k : ℝ) * P, 0) with hvdef
  have hfst : (k : ℝ) * P = v.1 - x.1 + w.1 := by
    simp [hvdef]
    ring
  have hb1 : ‖(k : ℝ) * P‖ ≤ R0 + ‖x‖ + ‖w0‖ + 1 := by
    rw [hfst]
    have a1 := norm_add_le (v.1 - x.1) w.1
    have a2 := norm_sub_le v.1 x.1
    have a3 := norm_fst_le v
    have a4 := norm_fst_le x
    have a6 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hP] at hb1
  have hk2 : |(k : ℝ)| ≤ (N : ℝ) := by
    have : |(k : ℝ)| ≤ (R0 + ‖x‖ + ‖w0‖ + 1) / P := by
      rw [le_div_iff₀ hP]
      linarith
    linarith
  have hk3 : |k| ≤ (N : ℤ) := by
    have h' : ((|k| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
      rw [Int.cast_abs]; push_cast; exact hk2
    exact_mod_cast h'
  exact hk (Finset.mem_Icc.2 (abs_le.1 hk3))

/-- Near `w`, the periodised sum equals its window sum. -/
lemma shiftSum_eventually_Icc {κ : ℝ × Space → ℝ} {R0 P : ℝ} (hP : 0 < P)
    (hR0 : ∀ z, κ z ≠ 0 → ‖z‖ ≤ R0) (x w : ℝ × Space) (N : ℕ)
    (hN : (R0 + ‖x‖ + ‖w‖ + 1) / P ≤ N) :
    ∀ᶠ p in 𝓝 w, ∑' k : ℤ, κ (x - p + ((k : ℝ) * P, 0))
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, κ (x - p + ((k : ℝ) * P, 0)) := by
  filter_upwards [Metric.ball_mem_nhds w one_pos] with p hp
  apply tsum_eq_sum
  intro k hk
  have hfar := far_of_notMem hP x p w hp N hN k hk
  by_contra h
  exact absurd (hR0 _ h) (not_le.2 hfar)

/-- Vanishing of a kernel and of its derivatives at points far from the support. -/
lemma kernel_vanish_far {κ : ℝ × Space → ℝ} {R0 : ℝ} (hR0 : ∀ z, κ z ≠ 0 → ‖z‖ ≤ R0)
    {z : ℝ × Space} (hz : R0 < ‖z‖) :
    κ z = 0 ∧ kerDτ κ z = 0 ∧ (∀ v : Space, kerDv κ v z = 0) ∧ kerLap κ z = 0 := by
  have h : κ =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with y hy
    by_contra hne
    have h1 := hR0 y hne
    have hy' : R0 < ‖y‖ := hy
    linarith
  have hfz : fderiv ℝ κ =ᶠ[𝓝 z] fderiv ℝ (fun _ : ℝ × Space => (0 : ℝ)) := h.fderiv
  have hd : ∀ᶠ y in 𝓝 z, fderiv ℝ κ y = 0 := by
    filter_upwards [hfz] with y hy
    simpa using hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.eq_of_nhds
  · unfold kerDτ
    rw [hfz.eq_of_nhds]
    simp
  · intro v
    unfold kerDv
    rw [hfz.eq_of_nhds]
    simp
  · unfold kerLap
    apply Finset.sum_eq_zero
    intro j _
    have h2 : (fun y => fderiv ℝ κ y (0, coordinateVector j)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hd] with y hy
      simp [hy]
    rw [h2.fderiv_eq]
    simp

/-- Linear decomposition of the spatial derivative kernel. -/
lemma kerDv_eq_sum (κ : ℝ × Space → ℝ) (v : Space) (z : ℝ × Space) :
    kerDv κ v z = ∑ j : Fin 3, v j * kerDv κ (coordinateVector j) z := by
  unfold kerDv
  have hv : v = ∑ j : Fin 3, v j • coordinateVector j := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  have h : ((0 : ℝ), v) = ∑ j : Fin 3, v j • ((0 : ℝ), coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_mk]
      exact hv
  rw [h, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- Chain rule on a translate. -/
lemma fderiv_translate (g : ℝ × Space → ℝ) (hg : Differentiable ℝ g) (x c w v : ℝ × Space) :
    fderiv ℝ (fun p : ℝ × Space => g (x - p + c)) w v = -(fderiv ℝ g (x - w + c) v) := by
  have h1 : HasFDerivAt (fun p : ℝ × Space => x - p + c)
      (-(ContinuousLinearMap.id ℝ (ℝ × Space))) w :=
    ((hasFDerivAt_id w).const_sub x).add_const c
  have h2 : HasFDerivAt (fun p : ℝ × Space => g (x - p + c))
      ((fderiv ℝ g (x - w + c)).comp (-(ContinuousLinearMap.id ℝ (ℝ × Space)))) w :=
    (hg (x - w + c)).hasFDerivAt.comp w h1
  rw [h2.fderiv]
  simp

/-- Chain rule on a finite sum of translates. -/
lemma fderiv_translate_sum (g : ℝ × Space → ℝ) (hg : Differentiable ℝ g) (x w v : ℝ × Space)
    (S : Finset ℤ) (c : ℤ → ℝ × Space) :
    fderiv ℝ (fun p : ℝ × Space => ∑ k ∈ S, g (x - p + c k)) w v
      = ∑ k ∈ S, -(fderiv ℝ g (x - w + c k) v) := by
  have hd : ∀ k, Differentiable ℝ (fun p : ℝ × Space => g (x - p + c k)) :=
    fun k => hg.comp (f := fun p : ℝ × Space => x - p + c k) (by fun_prop)
  rw [fderiv_fun_sum (fun k _ => hd k w), ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => fderiv_translate g hg x (c k) w v)

/-- Derivative of a negated function applied to a vector. -/
lemma fderiv_neg_apply' (f : ℝ × Space → ℝ) (hf : Differentiable ℝ f) (z v : ℝ × Space) :
    fderiv ℝ (fun y => -f y) z v = -(fderiv ℝ f z v) := by
  have h : HasFDerivAt (fun y => -f y) (-(fderiv ℝ f z)) z := (hf z).hasFDerivAt.neg
  rw [h.fderiv]
  simp

/-! ### Eventual equality and the operators -/

lemma dτ_congr_nhds {U V : ℝ × Space → CVec3} {w : ℝ × Space} (h : U =ᶠ[𝓝 w] V) :
    PhaseSpace.dτ U w = PhaseSpace.dτ V w := by
  simp only [PhaseSpace.dτ]
  rw [h.fderiv_eq]

lemma dy_eventuallyEq {U V : ℝ × Space → CVec3} {w : ℝ × Space} (h : U =ᶠ[𝓝 w] V) (j : Fin 3) :
    PhaseSpace.dy j U =ᶠ[𝓝 w] PhaseSpace.dy j V := by
  have hfd : fderiv ℝ U =ᶠ[𝓝 w] fderiv ℝ V := h.fderiv
  filter_upwards [hfd] with p hp
  simp only [PhaseSpace.dy]
  rw [hp]

lemma radialT_congr_nhds {U V : ℝ × Space → CVec3} {w : ℝ × Space} (h : U =ᶠ[𝓝 w] V) :
    PhaseSpace.radialT U w = PhaseSpace.radialT V w := by
  simp only [PhaseSpace.radialT]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(dy_eventuallyEq h j).eq_of_nhds]

lemma lapT_congr_nhds {U V : ℝ × Space → CVec3} {w : ℝ × Space} (h : U =ᶠ[𝓝 w] V) :
    PhaseSpace.lapT U w = PhaseSpace.lapT V w := by
  simp only [PhaseSpace.lapT]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(dy_eventuallyEq (dy_eventuallyEq h j) j).eq_of_nhds]

lemma L0_congr_nhds {ν : ℝ} {U V : ℝ × Space → CVec3} {w : ℝ × Space} (h : U =ᶠ[𝓝 w] V) :
    L0 ν U w = L0 ν V w := by
  simp only [B0411.L0, B0411.T0]
  rw [dτ_congr_nhds h, radialT_congr_nhds h, lapT_congr_nhds h, h.eq_of_nhds]

/-- Complex scalar multiplication of a real multiple of a vector. -/
lemma cmul_real_smul_vec (μ r : ℝ) (e : CVec3) : (μ : ℂ) • (r • e) = (μ * r) • e := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r e, smul_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (μ * r) e]
  congr 1
  push_cast
  rfl

/-- Scalar bookkeeping for `final_vec`. -/
lemma scalar_sum_identity (S : Finset ℤ) (a d : ℤ → ℝ) (b c : Fin 3 → ℤ → ℝ)
    (w2 : Fin 3 → ℝ) (μ ν : ℝ) :
    (∑ k ∈ S, -(a k)) - (∑ j : Fin 3, ∑ k ∈ S, (1 / 2 : ℝ) * (w2 j * -(b j k)))
        - (∑ j : Fin 3, ∑ k ∈ S, ν * c j k) - (∑ k ∈ S, (1 / 2 : ℝ) * d k)
        + (∑ k ∈ S, μ * d k)
      = ∑ k ∈ S, ((μ - 1 / 2) * d k - a k + (1 / 2 : ℝ) * (∑ j : Fin 3, w2 j * b j k)
          - ν * (∑ j : Fin 3, c j k)) := by
  rw [Finset.sum_comm (f := fun j k => (1 / 2 : ℝ) * (w2 j * -(b j k)))]
  rw [Finset.sum_comm (f := fun j k => ν * c j k)]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, sub_mul, mul_sub,
    Finset.sum_neg_distrib, mul_neg, neg_mul, mul_add, add_mul]
  ring

/-- The scalar identity behind `ShiftTestOpEq`, collected over the window. -/
lemma final_vec (e : CVec3) (μ ν : ℝ) (S : Finset ℤ) (a d : ℤ → ℝ) (b c : Fin 3 → ℤ → ℝ)
    (w2 : Fin 3 → ℝ) :
    ((∑ k ∈ S, -(a k)) • e - (1 / 2 : ℝ) • (∑ j : Fin 3, w2 j • ((∑ k ∈ S, -(b j k)) • e))
        - ν • (∑ j : Fin 3, (∑ k ∈ S, c j k) • e) - (1 / 2 : ℝ) • ((∑ k ∈ S, d k) • e)
        + (μ : ℂ) • ((∑ k ∈ S, d k) • e))
      = (∑ k ∈ S, ((μ - 1 / 2) * d k - a k + (1 / 2 : ℝ) * (∑ j : Fin 3, w2 j * b j k)
          - ν * (∑ j : Fin 3, c j k))) • e := by
  rw [cmul_real_smul_vec]
  simp only [Finset.mul_sum, Finset.sum_smul, Finset.smul_sum, smul_smul, sub_smul, add_smul,
    Fin.sum_univ_three, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  module

/-- Far points: the testing expression vanishes outside the window. -/
lemma testExpr_zero_far {κ : ℝ × Space → ℝ} {R0 P : ℝ} (hR0 : ∀ z, κ z ≠ 0 → ‖z‖ ≤ R0)
    (hP : 0 < P) (x w : ℝ × Space) (ν μ : ℝ) (N : ℕ) (hN : (R0 + ‖x‖ + ‖w‖ + 1) / P ≤ N)
    (k : ℤ) (hk : k ∉ Finset.Icc (-(N : ℤ)) N) :
    (μ - 1 / 2) * κ (x - w + ((k : ℝ) * P, 0)) - kerDτ κ (x - w + ((k : ℝ) * P, 0))
      + (1 / 2 : ℝ) * kerDv κ (x.2 - (x - w + ((k : ℝ) * P, 0)).2) (x - w + ((k : ℝ) * P, 0))
      - ν * kerLap κ (x - w + ((k : ℝ) * P, 0)) = 0 := by
  have hfar := far_of_notMem hP x w w (Metric.mem_ball_self one_pos) N hN k hk
  obtain ⟨h1, h2, h3, h4⟩ := kernel_vanish_far hR0 hfar
  rw [h1, h2, h3, h4]
  ring

/-- The pointwise identity for a general kernel. -/
lemma shift_pointwise {κ : ℝ × Space → ℝ} (hκs : ContDiff ℝ ∞ κ) {R0 P : ℝ}
    (hR0 : ∀ z, κ z ≠ 0 → ‖z‖ ≤ R0) (hP : 0 < P) (ν μ : ℝ) (x w : ℝ × Space) (e : CVec3) :
    L0 ν (fun p : ℝ × Space => (∑' k : ℤ, κ (x - p + ((k : ℝ) * P, 0))) • e) w
        + (μ : ℂ) • (fun p : ℝ × Space => (∑' k : ℤ, κ (x - p + ((k : ℝ) * P, 0))) • e) w
      = (∑' k : ℤ, ((μ - 1 / 2) * κ (x - w + ((k : ℝ) * P, 0))
          - kerDτ κ (x - w + ((k : ℝ) * P, 0))
          + (1 / 2 : ℝ) * kerDv κ (x.2 - (x - w + ((k : ℝ) * P, 0)).2) (x - w + ((k : ℝ) * P, 0))
          - ν * kerLap κ (x - w + ((k : ℝ) * P, 0)))) • e := by
  have hκd : Differentiable ℝ κ := hκs.differentiable (by simp)
  have hκfd : Differentiable ℝ (fderiv ℝ κ) :=
    (hκs.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  obtain ⟨N, hN⟩ := exists_nat_ge ((R0 + ‖x‖ + ‖w‖ + 1) / P)
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hS
  set FS : ℝ × Space → ℝ := fun p => ∑ k ∈ S, κ (x - p + ((k : ℝ) * P, 0)) with hFS
  set V : ℝ × Space → CVec3 := fun p => FS p • e with hV
  have hUV : (fun p : ℝ × Space => (∑' k : ℤ, κ (x - p + ((k : ℝ) * P, 0))) • e) =ᶠ[𝓝 w] V := by
    filter_upwards [shiftSum_eventually_Icc hP hR0 x w N hN] with p hp
    show (∑' k : ℤ, κ (x - p + ((k : ℝ) * P, 0))) • e = FS p • e
    rw [hp]
  have hFSd : Differentiable ℝ FS := by
    show Differentiable ℝ (fun p : ℝ × Space => ∑ k ∈ S, κ (x - p + ((k : ℝ) * P, 0)))
    exact Differentiable.fun_sum (fun k _ =>
      hκd.comp (f := fun p : ℝ × Space => x - p + ((k : ℝ) * P, 0)) (by fun_prop))
  have hFSfd : ∀ p v, fderiv ℝ FS p v = ∑ k ∈ S, -(fderiv ℝ κ (x - p + ((k : ℝ) * P, 0)) v) := by
    intro p v
    exact fderiv_translate_sum κ hκd x p v S (fun k : ℤ => ((k : ℝ) * P, (0 : Space)))
  have hVd : ∀ p v, fderiv ℝ V p v = (fderiv ℝ FS p v) • e := by
    intro p v
    have hVeq : V = fun y => FS y • e := rfl
    rw [hVeq, fderiv_smul_const (hFSd p) e, ContinuousLinearMap.smulRight_apply]
  have hdτV : PhaseSpace.dτ V w = (∑ k ∈ S, -(kerDτ κ (x - w + ((k : ℝ) * P, 0)))) • e := by
    simp only [PhaseSpace.dτ, kerDτ]
    rw [hVd, hFSfd]
  have hdyfun : ∀ j : Fin 3, PhaseSpace.dy j V = fun p : ℝ × Space =>
      (∑ k ∈ S, -(kerDv κ (coordinateVector j) (x - p + ((k : ℝ) * P, 0)))) • e := by
    intro j
    funext p
    simp only [PhaseSpace.dy, kerDv]
    rw [hVd, hFSfd]
  have hdyw : ∀ j : Fin 3, PhaseSpace.dy j V w
      = (∑ k ∈ S, -(kerDv κ (coordinateVector j) (x - w + ((k : ℝ) * P, 0)))) • e :=
    fun j => congrFun (hdyfun j) w
  have hrad : PhaseSpace.radialT V w = ∑ j : Fin 3, (w.2 j) •
      ((∑ k ∈ S, -(kerDv κ (coordinateVector j) (x - w + ((k : ℝ) * P, 0)))) • e) := by
    simp only [PhaseSpace.radialT]
    exact Finset.sum_congr rfl (fun j _ => by rw [hdyw j])
  have hkd : ∀ j : Fin 3,
      Differentiable ℝ (fun z : ℝ × Space => fderiv ℝ κ z (0, coordinateVector j)) :=
    fun j => hκfd.clm_apply (differentiable_const _)
  have hgd : ∀ j : Fin 3,
      Differentiable ℝ (fun z : ℝ × Space => -(kerDv κ (coordinateVector j) z)) :=
    fun j => (hkd j).neg
  have hGd : ∀ j : Fin 3, Differentiable ℝ (fun p : ℝ × Space =>
      ∑ k ∈ S, -(kerDv κ (coordinateVector j) (x - p + ((k : ℝ) * P, 0)))) := by
    intro j
    exact Differentiable.fun_sum (fun k _ =>
      (hgd j).comp (f := fun p : ℝ × Space => x - p + ((k : ℝ) * P, 0)) (by fun_prop))
  have hdydy : ∀ j : Fin 3, PhaseSpace.dy j (PhaseSpace.dy j V) w
      = (∑ k ∈ S, fderiv ℝ (fun z' : ℝ × Space => fderiv ℝ κ z' (0, coordinateVector j))
          (x - w + ((k : ℝ) * P, 0)) (0, coordinateVector j)) • e := by
    intro j
    rw [hdyfun j]
    simp only [PhaseSpace.dy]
    rw [fderiv_smul_const (hGd j w) e, ContinuousLinearMap.smulRight_apply]
    congr 1
    refine (fderiv_translate_sum (fun z : ℝ × Space => -(kerDv κ (coordinateVector j) z))
      (hgd j) x w (0, coordinateVector j) S (fun k : ℤ => ((k : ℝ) * P, (0 : Space)))).trans ?_
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hn := fderiv_neg_apply' (fun z : ℝ × Space => fderiv ℝ κ z (0, coordinateVector j))
      (hkd j) (x - w + ((k : ℝ) * P, 0)) (0, coordinateVector j)
    simp only [kerDv] at hn ⊢
    rw [hn, neg_neg]
  have hlap : PhaseSpace.lapT V w = ∑ j : Fin 3, (∑ k ∈ S,
      fderiv ℝ (fun z' : ℝ × Space => fderiv ℝ κ z' (0, coordinateVector j))
        (x - w + ((k : ℝ) * P, 0)) (0, coordinateVector j)) • e := by
    simp only [PhaseSpace.lapT]
    exact Finset.sum_congr rfl (fun j _ => hdydy j)
  have hVw : V w = (∑ k ∈ S, κ (x - w + ((k : ℝ) * P, 0))) • e := rfl
  have hk : ∀ k : ℤ, kerDv κ (x.2 - (x - w + ((k : ℝ) * P, 0)).2) (x - w + ((k : ℝ) * P, 0))
      = ∑ j : Fin 3, w.2 j * kerDv κ (coordinateVector j) (x - w + ((k : ℝ) * P, 0)) := by
    intro k
    have e2 : (x - w + ((k : ℝ) * P, 0)).2 = x.2 - w.2 := by simp
    rw [e2, sub_sub_cancel]
    exact kerDv_eq_sum κ w.2 _
  beta_reduce
  rw [L0_congr_nhds hUV, hUV.eq_of_nhds]
  rw [tsum_eq_sum (s := S) (fun k hk' => testExpr_zero_far hR0 hP x w ν μ N hN k hk')]
  simp only [hk, kerLap]
  simp only [B0411.L0, B0411.T0]
  rw [hdτV, hrad, hlap, hVw]
  exact final_vec e μ ν S (fun k => kerDτ κ (x - w + ((k : ℝ) * P, 0)))
    (fun k => κ (x - w + ((k : ℝ) * P, 0)))
    (fun j k => kerDv κ (coordinateVector j) (x - w + ((k : ℝ) * P, 0)))
    (fun j k => fderiv ℝ (fun z' : ℝ × Space => fderiv ℝ κ z' (0, coordinateVector j))
      (x - w + ((k : ℝ) * P, 0)) (0, coordinateVector j))
    (fun j => w.2 j)

/-- (B3) The operator on the periodised translate. -/
theorem shiftTestOpEq : ShiftTestOpEq := by
  intro P ν μ hP ρ x e
  funext w
  have hκc : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  obtain ⟨R0, hR0⟩ := exists_radius_of_hasCompactSupport hκc
  have hκs : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have key := shift_pointwise hκs hR0 hP ν μ x w e
  simp only [shiftTestOp, testKer, shiftTest, shiftKer]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
