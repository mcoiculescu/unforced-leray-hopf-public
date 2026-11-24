import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.A
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.B
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L1_Smooth
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `FarKerDt` (task `PartIII-b:C/rep/8/1/1/1/2/1/1`)

Source `shorter-proof-2026-11-02.tex` lines 3604-3610 (`sep:kernel`) and 5400-5427.
The age derivative of `∇_k K_t` is `∇_k ΔK_t` (heat equation), a derivative of `K_t` of order `n+3`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray.Short.IIIa

/-- Schwarz step: the `s`-derivative of the `x`-gradient is the `x`-gradient of the `s`-derivative. -/
lemma farKer_swap (F : ℝ × Space → ℝ)
    (hF : ContDiffOn ℝ 3 F {p : ℝ × Space | 0 < p.1}) {t : ℝ} (ht : 0 < t) (y v : Space) :
    deriv (fun s : ℝ => fderiv ℝ (fun x' : Space => F (s, x')) y v) t =
      fderiv ℝ (fun y' : Space => fderiv ℝ F (t, y') ((1 : ℝ), (0 : Space))) y v := by
  have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hdiffAt : ∀ s : ℝ, 0 < s → ∀ z : Space, ContDiffAt ℝ 3 F (s, z) := fun s hs z =>
    hF.contDiffAt (hopen.mem_nhds (show (s, z) ∈ {p : ℝ × Space | 0 < p.1} from hs))
  have hC : ContDiffAt ℝ 3 F (t, y) := hdiffAt t ht y
  have hD : DifferentiableAt ℝ (fderiv ℝ F) (t, y) :=
    (hC.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ F (t, y) := hC.isSymmSndFDerivAt (by norm_num)
  have hL : HasDerivAt (fun s : ℝ => fderiv ℝ F (s, y) ((0 : ℝ), v))
      (fderiv ℝ (fderiv ℝ F) (t, y) ((1 : ℝ), (0 : Space)) ((0 : ℝ), v)) t := by
    have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t y)
    have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ F (s, y))
        (fderiv ℝ (fderiv ℝ F) (t, y) ((1 : ℝ), (0 : Space))) t :=
      hD.hasFDerivAt.comp_hasDerivAt t h1
    have h4 := h3.clm_apply (hasDerivAt_const t ((0 : ℝ), v))
    simpa using h4
  have hEq : (fun s : ℝ => fderiv ℝ (fun x' : Space => F (s, x')) y v) =ᶠ[𝓝 t]
      (fun s : ℝ => fderiv ℝ F (s, y) ((0 : ℝ), v)) := by
    filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds ht] with s hs
    have hc : HasFDerivAt (fun x' : Space => ((s, x') : ℝ × Space))
        (ContinuousLinearMap.inr ℝ ℝ Space) y :=
      hasFDerivAt_prodMk_right s y
    have hd : HasFDerivAt (fun x' : Space => F (s, x'))
        ((fderiv ℝ F (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
      (hdiffAt s (show (0 : ℝ) < s from hs) y).differentiableAt (by norm_num) |>.hasFDerivAt.comp y hc
    rw [hd.fderiv]
    simp
  have hR : HasFDerivAt (fun y' : Space => fderiv ℝ F (t, y'))
      ((fderiv ℝ (fderiv ℝ F) (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hD.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  have hR2 := hR.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) y)
  rw [hEq.deriv_eq, hL.deriv, hR2.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.inr_apply,
    map_zero, zero_add]
  exact hsymm _ _

/-- The age derivative of `K_t` at `t > 0` is the Laplacian, written as a Hessian functional. -/
lemma farKer_fderiv_time (i j : Fin 3) {t : ℝ} (ht : 0 < t) (y : Space) :
    fderiv ℝ (fun p : ℝ × Space => heatLerayK p.1 i j p.2) (t, y) ((1 : ℝ), (0 : Space)) =
      ∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK t i j x') z
        (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l) := by
  have hH := heatLerayK_heat t ht i j y
  have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hC : ContDiffAt ℝ 3 (fun p : ℝ × Space => heatLerayK p.1 i j p.2) (t, y) :=
    (heatLerayK_jointC3 i j).contDiffAt
      (hopen.mem_nhds (show (t, y) ∈ {p : ℝ × Space | 0 < p.1} from ht))
  have hd : DifferentiableAt ℝ (fun p : ℝ × Space => heatLerayK p.1 i j p.2) (t, y) :=
    hC.differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t y)
  have h2 := hd.hasFDerivAt.comp_hasDerivAt t h1
  exact h2.unique hH

/-- Directional derivative bound: `‖D^n (∂_w h)‖ ≤ ‖w‖ ‖D^{n+1} h‖` (one order per derivative). -/
lemma farKer_dir {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (w x : Space) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ h y w) x‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℝ w‖ * ‖iteratedFDeriv ℝ (n + 1) h x‖ := by
  have e1 : (fun y => fderiv ℝ h y w) = (ContinuousLinearMap.apply ℝ ℝ w) ∘ (fderiv ℝ h) := rfl
  rw [e1]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℝ w)
    (hh.fderiv_right (m := ∞) (by simp)).contDiffAt (n := n) (by simp)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]

/-- The Laplacian term of the age derivative, differentiated once in a direction `v`, costs three orders. -/
lemma farKer_lap {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (v x : Space) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y'
          (UnforcedLeray.coordinateVector l)) y v) x‖ ≤
      (‖ContinuousLinearMap.apply ℝ ℝ v‖ * ∑ l : Fin 3,
        (‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖ *
          ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖)) *
        ‖iteratedFDeriv ℝ (n + 3) g x‖ := by
  have hG : ∀ l : Fin 3, ContDiff ℝ ∞ (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) :=
    fun l => (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hH : ∀ l : Fin 3, ContDiff ℝ ∞ (fun y' => fderiv ℝ
      (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) :=
    fun l => ((hG l).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hsum : (fun y' : Space => ∑ l : Fin 3, fderiv ℝ
      (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) =
      ∑ l : Fin 3, (fun y' : Space => fderiv ℝ
        (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) := by
    funext y'
    simp [Finset.sum_apply]
  rw [hsum]
  have hfd : (fun y : Space => fderiv ℝ (∑ l : Fin 3, (fun y' : Space => fderiv ℝ
      (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l))) y v) =
      fun y => ∑ l : Fin 3, fderiv ℝ (fun y' : Space => fderiv ℝ
        (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) y v := by
    funext y
    rw [fderiv_sum (fun l _ => ((hH l).differentiable (by simp)) y)]
    simp
  rw [hfd]
  have hI := iteratedFDeriv_sum (𝕜 := ℝ) (i := n) (u := Finset.univ)
    (f := fun (l : Fin 3) (y : Space) => fderiv ℝ (fun y' : Space => fderiv ℝ
      (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) y v)
    (fun l _ => ((((hH l).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)).of_le (by simp))
  rw [congrFun hI x, Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum (fun l _ => ?_)
  have b1 := farKer_dir (h := fun y' : Space => fderiv ℝ
      (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l))
    (hH l) v x n
  have b2 := farKer_dir (h := fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) (hG l)
    (UnforcedLeray.coordinateVector l) x (n + 1)
  have b3 := farKer_dir (h := g) hg (UnforcedLeray.coordinateVector l) x (n + 2)
  have c3 : ‖iteratedFDeriv ℝ (n + 2) (fun z => fderiv ℝ g z (UnforcedLeray.coordinateVector l)) x‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖ *
        ‖iteratedFDeriv ℝ (n + 3) g x‖ := b3
  refine b1.trans ?_
  refine (mul_le_mul_of_nonneg_left b2 (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c3 (by positivity)) (by positivity)).trans ?_
  exact le_of_eq (by ring)

/-- Uniform bound for one order `n`. -/
lemma farKer_n (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j k : Fin 3) (t : ℝ), 0 < t → ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ n (fun y => deriv (fun s => fderiv ℝ (fun x' => heatLerayK s i j x') y
      (UnforcedLeray.coordinateVector k)) t) x‖ ≤ C * ‖x‖ ^ (-6 - (n : ℝ)) := by
  obtain ⟨C0, hC0⟩ := sepKernelBounds (n + 2)
  have hS0 : 0 ≤ ∑ k : Fin 3, ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k)‖ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hK0 : 0 ≤ ∑ l : Fin 3, (‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖ *
      ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨(∑ k : Fin 3, ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k)‖) *
    (∑ l : Fin 3, (‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖ *
      ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖)) * |C0|, by positivity, ?_⟩
  intro i j k t ht x hx
  have hexp : (-4 - (((n + 2 : ℕ)) : ℝ)) = -6 - (n : ℝ) := by push_cast; ring
  have hFi : ContDiffOn ℝ 3 (fun p : ℝ × Space => heatLerayK p.1 i j p.2)
      {p : ℝ × Space | 0 < p.1} := heatLerayK_jointC3 i j
  have hK : ContDiff ℝ ∞ (fun y => heatLerayK t i j y) := heatLerayKSmoothAll t ht i j
  have hFun : (fun y' : Space => fderiv ℝ (fun p : ℝ × Space => heatLerayK p.1 i j p.2) (t, y')
      ((1 : ℝ), (0 : Space))) = fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK t i j x') z (UnforcedLeray.coordinateVector l)) y'
          (UnforcedLeray.coordinateVector l) :=
    funext fun y' => farKer_fderiv_time i j ht y'
  have hfun : (fun y => deriv (fun s => fderiv ℝ (fun x' => heatLerayK s i j x') y
      (UnforcedLeray.coordinateVector k)) t) =
      fun y => fderiv ℝ (fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK t i j x') z (UnforcedLeray.coordinateVector l)) y'
          (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector k) := by
    funext y
    rw [← hFun]
    exact farKer_swap (fun p : ℝ × Space => heatLerayK p.1 i j p.2) hFi ht y _
  rw [hfun]
  have hmain := farKer_lap (g := fun x' => heatLerayK t i j x') hK (UnforcedLeray.coordinateVector k) x n
  have hD0 : ‖iteratedFDeriv ℝ (n + 3) (fun y => heatLerayK t i j y) x‖ ≤ C0 * ‖x‖ ^ (-6 - (n : ℝ)) := by
    have h := (hC0 x hx i j).1 t ht
    rw [← hexp]
    exact h
  have hk : ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k)‖ ≤
      ∑ k' : Fin 3, ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k')‖ :=
    Finset.single_le_sum (f := fun k' : Fin 3 =>
      ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k')‖)
      (fun _ _ => by positivity) (Finset.mem_univ k)
  have hp : 0 ≤ ‖x‖ ^ (-6 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have step1 := mul_le_mul (mul_le_mul_of_nonneg_right hk hK0) hD0 (norm_nonneg _)
    (mul_nonneg hS0 hK0)
  have step2 : ((∑ k' : Fin 3, ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k')‖) *
      (∑ l : Fin 3, (‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖ *
        ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖))) * (C0 * ‖x‖ ^ (-6 - (n : ℝ))) ≤
      (∑ k' : Fin 3, ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k')‖) *
      (∑ l : Fin 3, (‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖ *
        ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector l)‖)) * |C0| * ‖x‖ ^ (-6 - (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C0) hp) (mul_nonneg hS0 hK0)
    calc _ ≤ _ := h
      _ = _ := by ring
  exact hmain.trans (step1.trans step2)

theorem farKerDt : FarKerDt := by
  obtain ⟨C0, h0, hb0⟩ := farKer_n 0
  obtain ⟨C1, h1, hb1⟩ := farKer_n 1
  refine ⟨C0 + C1, add_nonneg h0 h1, ?_⟩
  intro i j k t ht x hx n hn
  interval_cases n
  · have := hb0 i j k t ht x hx
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))
  · have := hb1 i j k t ht x hx
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

end
