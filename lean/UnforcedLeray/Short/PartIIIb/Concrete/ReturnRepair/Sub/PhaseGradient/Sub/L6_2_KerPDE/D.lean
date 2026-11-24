import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.A
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.B
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.C
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.D.Calc

/-!
# `(∂_h - L + m - ½) G_m = 0` (`GkerHasDerivH`, source 3800-3807, 3611-3621)

`G_m(h,y,z) = e^{-(m+3/2)h} D_k(t(h), y - e^{-h/2}z)` with `D_k = ∂_kK`, `t(h) = ν(1-e^{-h})`.
Chain rule (`t' = νe^{-h}`, `d/dh(y - e^{-h/2}z) = ½(y-x)`, `x = y - e^{-h/2}z`), the heat
equation `∂_tD_k = ΔD_k` and Euler form `x·∇D_k + 2t∂_tD_k = -4D_k` for `D_k`
(`D/Calc.lean`, from `heatLerayK_jointC3`, `heatLerayK_heat`, `heatLerayK_euler`), and
`νe^{-h} + t(h) = ν`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi KerCalc

lemma ker_fderiv_cexp (c : ℂ) (g : Space → ℝ) (hg : Differentiable ℝ g) (a y w : Space) :
    fderiv ℝ (fun y' : Space => c * ((g (y' - a) : ℝ) : ℂ)) y w =
      c * ((fderiv ℝ g (y - a) w : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y' : Space => y' - a) (ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).sub_const a
  have h2 := (hg (y - a)).hasFDerivAt.comp y h1
  have h3 := (Complex.ofRealCLM.hasFDerivAt (x := g (y - a))).comp y h2
  have h4 := h3.const_mul c
  have h5 : HasFDerivAt (fun y' : Space => c * ((g (y' - a) : ℝ) : ℂ)) _ y := h4
  rw [h5.fderiv]
  simp

theorem gkerHasDerivH : UnforcedLeray.Short.PartIIIb.Concrete.GkerHasDerivH := by
  have hC := heatLerayK_jointC3
  have hH := heatLerayK_heat
  have hE := heatLerayK_euler
  intro ν m hν h hh y z i j k
  have hP := hC i j
  set τ : ℝ := ν * (1 - Real.exp (-h)) with hτdef
  have hexp : Real.exp (-h) < 1 := by
    have := Real.exp_lt_exp.mpr (show -h < 0 by linarith)
    simpa using this
  have hτ : 0 < τ := mul_pos hν (by linarith)
  set r : ℝ := Real.exp (-h / 2) with hr
  set x : Space := y - r • z with hx
  have hU : (τ, x) ∈ U := mem_U hτ
  have hd : DifferentiableAt ℝ (DK i j k) (τ, x) := eval_differentiable (diff1 hP hU) _
  -- Gker as a function near h
  have hGeq : (fun h' => Gker ν m h' y z i j k) =ᶠ[nhds h]
      fun h' => Complex.exp (-(m + 3 / 2) * (h' : ℂ)) *
        ((DK i j k (ν * (1 - Real.exp (-h')), y - Real.exp (-h' / 2) • z) : ℝ) : ℂ) := by
    have hτc : ContinuousAt (fun h' : ℝ => ν * (1 - Real.exp (-h'))) h := by fun_prop
    have hev : ∀ᶠ h' in nhds h, 0 < ν * (1 - Real.exp (-h')) :=
      hτc.eventually (isOpen_Ioi.mem_nhds hτ)
    filter_upwards [hev] with h' hh'
    unfold Gker
    rw [slice_eq hC i j hh']
    rfl
  -- derivative of the inner path
  have hφ : HasDerivAt (fun h' : ℝ => (ν * (1 - Real.exp (-h')), y - Real.exp (-h' / 2) • z))
      (ν * Real.exp (-h), -((Real.exp (-h / 2) * (-1 / 2)) • z)) h := by
    have h1 : HasDerivAt (fun h' : ℝ => Real.exp (-h')) (Real.exp (-h) * -1) h :=
      (hasDerivAt_id h).neg.exp
    have h2 : HasDerivAt (fun h' : ℝ => ν * (1 - Real.exp (-h')))
        (ν * -(Real.exp (-h) * -1)) h := (h1.const_sub 1).const_mul ν
    have h3 : HasDerivAt (fun h' : ℝ => Real.exp (-h' / 2)) (Real.exp (-h / 2) * (-1 / 2)) h := by
      have := ((hasDerivAt_id h).neg.div_const 2).exp
      simpa using this
    have h4 := (h3.smul_const z).const_sub y
    have := h2.prodMk h4
    convert this using 1
    simp
  have hD := hd.hasFDerivAt.comp_hasDerivAt h hφ
  have hDc := hD.ofReal_comp
  have hc : HasDerivAt (fun h' : ℝ => Complex.exp (-(m + 3 / 2) * (h' : ℂ)))
      (Complex.exp (-(m + 3 / 2) * (h : ℂ)) * (-(m + 3 / 2))) h := by
    have := ((hasDerivAt_id h).ofReal_comp.const_mul (-(m + 3 / 2))).cexp
    simpa using this
  have hprod := hc.mul hDc
  refine (hprod.congr_of_eventuallyEq hGeq).congr_deriv ?_
  -- spatial structure of `Gker`
  set c0 : ℂ := Complex.exp (-(m + 3 / 2) * (h : ℂ)) with hc0
  set DKτ : Space → ℝ := fun x' => DK i j k (τ, x') with hDKτ
  have hdiff : ∀ x' : Space, DifferentiableAt ℝ (DK i j k) (τ, x') := fun x' =>
    eval_differentiable (diff1 hP (mem_U hτ)) _
  have hDiffτ : Differentiable ℝ DKτ := fun x' =>
    (hdiff x').comp x' ((differentiableAt_const τ).prodMk differentiableAt_id)
  have hfd : ∀ (x' : Space) (w : Space), fderiv ℝ DKτ x' w =
      fderiv ℝ (fderiv ℝ (Pk i j)) (τ, x') (0, w) (0, UnforcedLeray.coordinateVector k) := by
    intro x' w
    rw [hDKτ, slice_fderiv (hdiff x') w]
    exact fderiv_Dl hP (mem_U hτ) _ _
  have hDiff2 : ∀ l : Fin 3, Differentiable ℝ
      (fun x' => fderiv ℝ DKτ x' (UnforcedLeray.coordinateVector l)) := by
    intro l
    have : (fun x' => fderiv ℝ DKτ x' (UnforcedLeray.coordinateVector l)) =
        fun x' => (fun q => fderiv ℝ (fderiv ℝ (Pk i j)) q (0, UnforcedLeray.coordinateVector l)
          (0, UnforcedLeray.coordinateVector k)) (τ, x') := funext fun x' => hfd x' _
    rw [this]
    intro x'
    exact (eval_differentiable (eval_differentiable (diff2 hP (mem_U hτ)) _) _).comp x'
      ((differentiableAt_const τ).prodMk differentiableAt_id)
  have hGy : ∀ y' : Space, Gker ν m h y' z i j k = c0 * ((DKτ (y' - r • z) : ℝ) : ℂ) := by
    intro y'
    unfold Gker
    rw [slice_eq hC i j hτ]
    rfl
  have hGfun : (fun y' : Space => Gker ν m h y' z i j k) =
      fun y' => c0 * ((DKτ (y' - r • z) : ℝ) : ℂ) := funext hGy
  have l1 : fderiv ℝ (fun y' : Space => Gker ν m h y' z i j k) y y =
      c0 * ((fderiv ℝ DKτ x y : ℝ) : ℂ) := by
    rw [hGfun]; exact ker_fderiv_cexp c0 DKτ hDiffτ (r • z) y y
  have l2 : ∀ l : Fin 3, fderiv ℝ (fun y' : Space => fderiv ℝ (fun y'' : Space =>
      Gker ν m h y'' z i j k) y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l) =
      c0 * ((fderiv ℝ (fun x' => fderiv ℝ DKτ x' (UnforcedLeray.coordinateVector l)) x
        (UnforcedLeray.coordinateVector l) : ℝ) : ℂ) := by
    intro l
    have : (fun y' : Space => fderiv ℝ (fun y'' : Space => Gker ν m h y'' z i j k) y'
        (UnforcedLeray.coordinateVector l)) =
        fun y' => c0 * (((fun x' => fderiv ℝ DKτ x' (UnforcedLeray.coordinateVector l))
          (y' - r • z) : ℝ) : ℂ) := by
      funext y'
      rw [hGfun]
      exact ker_fderiv_cexp c0 DKτ hDiffτ (r • z) y' _
    rw [this]
    exact ker_fderiv_cexp c0 _ (hDiff2 l) (r • z) y _
  have hLker : Lker ν (Gker ν m) h y z i j k =
      c0 * ((1 / 2 : ℂ) * ((fderiv ℝ (DK i j k) (τ, x) (0, y) : ℝ) : ℂ) +
        (ν : ℂ) * ((fderiv ℝ (DK i j k) (τ, x) (1, 0) : ℝ) : ℂ)) := by
    unfold Lker
    rw [l1, slice_fderiv hd]
    simp only [l2]
    have hheat : fderiv ℝ (DK i j k) (τ, x) (1, 0) = ∑ l : Fin 3, fderiv ℝ
        (fun x' => fderiv ℝ DKτ x' (UnforcedLeray.coordinateVector l)) x
        (UnforcedLeray.coordinateVector l) := DK_heat hC hH i j k hτ x
    rw [hheat]
    push_cast
    rw [← Finset.mul_sum]
    ring
  have hG0 : Gker ν m h y z i j k = c0 * ((DK i j k (τ, x) : ℝ) : ℂ) := by
    have := hGy y
    exact this
  have hdec : ((ν * Real.exp (-h), -((Real.exp (-h / 2) * (-1 / 2)) • z)) : ℝ × Space) =
      (ν * Real.exp (-h)) • ((1 : ℝ), (0 : Space)) +
        (1 / 2 : ℝ) • (((0 : ℝ), y) - ((0 : ℝ), x)) := by
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_zero, zero_add, hx, ← hr]
    module
  rw [hdec]
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  have hD0 : (DK i j k ∘ fun h' : ℝ => (ν * (1 - Real.exp (-h')), y - Real.exp (-h' / 2) • z)) h =
      DK i j k (τ, x) := rfl
  rw [hD0, hLker, hG0]
  have Ec := DK_euler hC hE i j k hτ x
  have Ec' : ((fderiv ℝ (DK i j k) (τ, x) (0, x) : ℝ) : ℂ) +
      2 * (τ : ℂ) * ((fderiv ℝ (DK i j k) (τ, x) (1, 0) : ℝ) : ℂ) =
      -4 * ((DK i j k (τ, x) : ℝ) : ℂ) := by exact_mod_cast Ec
  rw [hτdef] at Ec'
  push_cast at Ec' ⊢
  linear_combination (c0 * (-1 / 2)) * Ec'

end UnforcedLeray.Short.PartIIIb.Concrete
