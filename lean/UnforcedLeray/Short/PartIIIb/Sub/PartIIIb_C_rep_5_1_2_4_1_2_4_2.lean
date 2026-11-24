import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4

/-!
# `PartIII-b:C/rep/5/1/2/4/1/2/4/2`: `KernelPartialHeat` from four tail/Gaussian facts

Source `the November 2 reference manuscript`
3600-3610: `K_t = δ G_t + ∂_i∂_j ∫_t^∞ G_a da`, `∂_t G = ΔG`, `∂_t ∫_t^∞ G_a = -G_t`,
`Δ ∫_t^∞ G_a = -G_t`.  Here `∂_k K_t = δ ∂_kG_t + ∂_k∂_i∂_j T_t` with `T_t = ∫_t^∞ G_a da`, and
the four facts below give `∂_t(∂_kK) = Δ(∂_kK)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KPH

open UnforcedLeray.Short.IIIa

/-- (1) For `t > 0` the tail `∫_t^∞ G_a da` is smooth and its `n`-th Fréchet derivative is the
integral of the `n`-th Fréchet derivatives of `G_a` (each `‖D^nG_a(x)‖ ≤ C_n a^{-3/2-n/2}`). -/
def TailIterated : Prop :=
  ∀ t : ℝ, 0 < t → ContDiff ℝ ∞ (heatTail t) ∧
    ∀ (n : ℕ) (x : Space), iteratedFDeriv ℝ n (heatTail t) x =
      ∫ a in Ioi t, iteratedFDeriv ℝ n (heatG a) x

/-- (2) The Gaussian heat equation, first for the first partial derivative in the nested form used
by `KernelPartialHeat`, then for all iterated derivatives:
`∂_a D^nG_a(x)(v) = Σ_l D^{n+2}G_a(x)(e_l, e_l, v)`. -/
def GaussHeat : Prop :=
  (∀ t : ℝ, 0 < t → ∀ (k : Fin 3) (x : Space),
    HasDerivAt (fun t' => fderiv ℝ (fun y => heatG t' y) x (coordinateVector k))
      (∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) y (coordinateVector l)) x
        (coordinateVector l)) t) ∧
  ∀ (n : ℕ) (a : ℝ), 0 < a → ∀ (x : Space) (v : Fin n → Space),
    HasDerivAt (fun a' => iteratedFDeriv ℝ n (heatG a') x v)
      (∑ l : Fin 3, iteratedFDeriv ℝ (n + 2) (heatG a) x
        (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v))) a

/-- (3) `∂_t` of `∂_k∂_i∂_j ∫_t^∞ G_a da` is `-∂_k∂_i∂_j G_t` (FTC in the lower limit). -/
def TailPartDt : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (i j k : Fin 3) (x : Space),
    HasDerivAt (fun t' => fderiv ℝ (fun y => part2 (heatTail t') i j y) x (coordinateVector k))
      (-(fderiv ℝ (fun y => part2 (heatG t) i j y) x (coordinateVector k))) t

/-- (4) `Δ ∂_k∂_i∂_j ∫_t^∞ G_a da = -∂_k∂_i∂_j G_t`. -/
def TailLapPart : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (i j k : Fin 3) (x : Space),
    ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
      fderiv ℝ (fun y'' => part2 (heatTail t) i j y'') y' (coordinateVector k)) y
        (coordinateVector l)) x (coordinateVector l) =
      -(fderiv ℝ (fun y => part2 (heatG t) i j y) x (coordinateVector k))

theorem contDiff_heatG {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (heatG t) := by
  unfold heatG
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)

theorem contDiff_part2 {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) :
    ContDiff ℝ ∞ (part2 f i j) := by
  unfold part2
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (coordinateVector j)) :=
    h1.clm_apply contDiff_const
  have h3 : ContDiff ℝ ∞ (fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j))) :=
    h2.fderiv_right (by simp)
  exact h3.clm_apply contDiff_const

theorem contDiff_fderiv_apply {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem kernel_split {t : ℝ} (ht : 0 < t) (hT : ContDiff ℝ ∞ (heatTail t)) (i j : Fin 3)
    (y v : Space) :
    fderiv ℝ (fun z => heatLerayK t i j z) y v =
      (if i = j then fderiv ℝ (fun z => heatG t z) y v else 0) +
        fderiv ℝ (fun z => part2 (heatTail t) i j z) y v := by
  have hG := contDiff_heatG ht
  have hP := contDiff_part2 hT i j
  have e : (fun z => heatLerayK t i j z) =
      fun z => (if i = j then heatG t z else 0) + part2 (heatTail t) i j z := rfl
  rw [e]
  have hd : DifferentiableAt ℝ (fun z => if i = j then heatG t z else 0) y := by
    split_ifs
    · exact (hG.differentiable (by simp)) y
    · exact differentiableAt_const _
  rw [fderiv_fun_add hd ((hP.differentiable (by simp)) y)]
  split_ifs <;> simp

theorem kernelPartialHeat_of (h1 : TailIterated) (h2 : GaussHeat) (h3 : TailPartDt)
    (h4 : TailLapPart) : KernelPartialHeat := by
  intro t ht i j k x
  have hTt := (h1 t ht).1
  have hG := contDiff_heatG ht
  have hP := contDiff_part2 hTt i j
  -- the nested derivative of the split
  have hin : (fun y' => fderiv ℝ (fun z => heatLerayK t i j z) y' (coordinateVector k)) =
      fun y' => (if i = j then fderiv ℝ (fun z => heatG t z) y' (coordinateVector k) else 0) +
        fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k) := by
    funext y'; exact kernel_split ht hTt i j y' _
  have hdG : ContDiff ℝ ∞ (fun y' => fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) :=
    contDiff_fderiv_apply hG _
  have hdP : ContDiff ℝ ∞
      (fun y' => fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k)) :=
    contDiff_fderiv_apply hP _
  have hLap : ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatLerayK t i j z) y' (coordinateVector k)) y (coordinateVector l))
        x (coordinateVector l) =
      (if i = j then ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) y (coordinateVector l)) x
        (coordinateVector l) else 0) +
      ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k)) y
          (coordinateVector l)) x (coordinateVector l) := by
    rw [hin]
    have hd1 : DifferentiableAt ℝ (fun y' => if i = j then
        fderiv ℝ (fun z => heatG t z) y' (coordinateVector k) else 0) x := by
      split_ifs
      · exact (hdG.differentiable (by simp)) x
      · exact differentiableAt_const _
    have hsplit : ∀ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        (if i = j then fderiv ℝ (fun z => heatG t z) y' (coordinateVector k) else 0) +
        fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k)) y
          (coordinateVector l)) x (coordinateVector l) =
      (if i = j then fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) y (coordinateVector l)) x
          (coordinateVector l) else 0) +
      fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k)) y
          (coordinateVector l)) x (coordinateVector l) := by
      intro l
      have a1 : ∀ y, DifferentiableAt ℝ (fun y' => if i = j then
          fderiv ℝ (fun z => heatG t z) y' (coordinateVector k) else 0) y := by
        intro y; split_ifs
        · exact (hdG.differentiable (by simp)) y
        · exact differentiableAt_const _
      have e1 : (fun y => fderiv ℝ (fun y' =>
          (if i = j then fderiv ℝ (fun z => heatG t z) y' (coordinateVector k) else 0) +
          fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k)) y
            (coordinateVector l)) = fun y =>
          (if i = j then fderiv ℝ (fun y' => fderiv ℝ (fun z => heatG t z) y'
            (coordinateVector k)) y (coordinateVector l) else 0) +
          fderiv ℝ (fun y' => fderiv ℝ (fun z => part2 (heatTail t) i j z) y'
            (coordinateVector k)) y (coordinateVector l) := by
        funext y
        rw [fderiv_fun_add (a1 y) ((hdP.differentiable (by simp)) y)]
        split_ifs <;> simp
      rw [e1]
      have a2 : DifferentiableAt ℝ (fun y => if i = j then
          fderiv ℝ (fun y' => fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) y
            (coordinateVector l) else 0) x := by
        split_ifs
        · exact ((contDiff_fderiv_apply hdG _).differentiable (by simp)) x
        · exact differentiableAt_const _
      have a3 : DifferentiableAt ℝ (fun y => fderiv ℝ (fun y' =>
          fderiv ℝ (fun z => part2 (heatTail t) i j z) y' (coordinateVector k)) y
            (coordinateVector l)) x :=
        ((contDiff_fderiv_apply hdP _).differentiable (by simp)) x
      rw [fderiv_fun_add a2 a3]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib]
    split_ifs <;> simp
  rw [hLap, h4 t ht i j k x]
  have hd : HasDerivAt (fun t' => fderiv ℝ (fun y => heatLerayK t' i j y) x (coordinateVector k))
      ((if i = j then ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) y (coordinateVector l)) x
        (coordinateVector l) else 0) +
        -(fderiv ℝ (fun y => part2 (heatG t) i j y) x (coordinateVector k))) t := by
    have hA := (h2.1 t ht k x)
    have hB := h3 t ht i j k x
    have hsum : HasDerivAt (fun t' =>
        (if i = j then fderiv ℝ (fun y => heatG t' y) x (coordinateVector k) else 0) +
        fderiv ℝ (fun y => part2 (heatTail t') i j y) x (coordinateVector k))
        ((if i = j then ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
          fderiv ℝ (fun z => heatG t z) y' (coordinateVector k)) y (coordinateVector l)) x
          (coordinateVector l) else 0) +
          -(fderiv ℝ (fun y => part2 (heatG t) i j y) x (coordinateVector k))) t := by
      refine HasDerivAt.add ?_ hB
      split_ifs
      · exact hA
      · exact hasDerivAt_const _ _
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with t' ht'
    exact kernel_split ht' (h1 t' ht').1 i j x _
  convert hd using 1

end UnforcedLeray.Short.PartIIIb.Concrete.KPH
end
