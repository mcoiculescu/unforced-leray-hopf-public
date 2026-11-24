import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# `L` is linear on `G_μ, G_{μ+1}` (`LkerKdSplit`, source 3603-3610, 3800-3807)

`y ↦ G_m(h,y,z)` is `C²` for `h > 0` since `K_t` is `C³` (`heatLerayKSmooth`, `t = ν(1-e^{-h}) > 0`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

lemma gker_contDiff (ν : ℝ) (m : ℂ) (hν : 0 < ν) (h : ℝ) (hh : 0 < h) (z : Space) (i j k : Fin 3) :
    ContDiff ℝ 2 (fun y : Space => Gker ν m h y z i j k) := by
  have ht : 0 < ν * (1 - Real.exp (-h)) := by
    have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact mul_pos hν (by linarith)
  have hf := heatLerayKSmooth _ ht i j
  have h1 : ContDiff ℝ 2 (fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)) :=
    hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 2 (fun y : Space => fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)
      (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector k)) :=
    (h1.comp (contDiff_id.sub contDiff_const)).clm_apply contDiff_const
  have h3 : ContDiff ℝ 2 (fun y : Space => (((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)
      (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector k) : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h2
  exact contDiff_const.mul h3

lemma lker_sub_aux (ν : ℝ) (Φ Ψ : Space → ℂ) (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ) (y : Space) :
    (1 / 2 : ℂ) * fderiv ℝ (fun y' => Φ y' - Ψ y') y y +
      (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Φ y'' - Ψ y'') y'
        (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l) =
    ((1 / 2 : ℂ) * fderiv ℝ Φ y y +
      (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l)) -
    ((1 / 2 : ℂ) * fderiv ℝ Ψ y y +
      (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ Ψ y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l)) := by
  have hd1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have e1 : ∀ y', fderiv ℝ (fun y'' => Φ y'' - Ψ y'') y' = fderiv ℝ Φ y' - fderiv ℝ Ψ y' :=
    fun y' => fderiv_sub (hd1 y') (hd2 y')
  have hΦ' : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hΨ' : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hl : ∀ (l : Fin 3), fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Φ y'' - Ψ y'') y'
        (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l) =
      fderiv ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l) -
      fderiv ℝ (fun y' => fderiv ℝ Ψ y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l) := by
    intro l
    have dΦ : DifferentiableAt ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y :=
      ((hΦ'.clm_apply contDiff_const).differentiable (by norm_num)) y
    have dΨ : DifferentiableAt ℝ (fun y' => fderiv ℝ Ψ y' (UnforcedLeray.coordinateVector l)) y :=
      ((hΨ'.clm_apply contDiff_const).differentiable (by norm_num)) y
    have : (fun y' => fderiv ℝ (fun y'' => Φ y'' - Ψ y'') y' (UnforcedLeray.coordinateVector l)) =
        fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l) -
          fderiv ℝ Ψ y' (UnforcedLeray.coordinateVector l) := by
      funext y'; rw [e1 y']; rfl
    rw [this, fderiv_fun_sub dΦ dΨ]; rfl
  have e2 : fderiv ℝ (fun y' => Φ y' - Ψ y') y = fderiv ℝ Φ y - fderiv ℝ Ψ y := e1 y
  simp only [hl, e2, Finset.sum_sub_distrib, sub_apply]
  ring

theorem lkerKdSplit : UnforcedLeray.Short.PartIIIb.Concrete.LkerKdSplit := by
  intro ν μ hν h hh y z i j k
  have := lker_sub_aux ν (fun y' => Gker ν (μ : ℂ) h y' z i j k)
    (fun y' => Gker ν ((μ : ℂ) + 1) h y' z i j k)
    (gker_contDiff ν _ hν h hh z i j k) (gker_contDiff ν _ hν h hh z i j k) y
  unfold Lker Kd
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete
