import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_1

/-!
# Part II-b, task `PartII-b:T13/1/4/3/2` (`chmMollEq`): reduction to `ChmLocInt`

Source: `the November 2 reference manuscript` lines 1933-1935.

`chmMollEq_of : ChmLocInt → ChmMollEq`.  The weak equation is tested against the translated and
reflected mollifier `w ↦ ρ_n(x - w)`; `cylHeatT` of it is the kernel `∂_sρ - ν(∂_q²+∂_η²)ρ`
evaluated at `x - z` (two sign flips cancel in the second order term).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Convolution

theorem cpd_reflect {ρ : Coord → ℝ} (hρ : Differentiable ℝ ρ) (x z : Coord) (j : Fin 3) :
    cpd j (fun w => ρ (x - w)) z = - cpd j ρ (x - z) := by
  have h : HasFDerivAt (fun w => ρ (x - w))
      ((fderiv ℝ ρ (x - z)).comp (-ContinuousLinearMap.id ℝ Coord)) z :=
    (hρ (x - z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
  simp [cpd, h.fderiv]

theorem cpd_neg_fun (h : Coord → ℝ) (z : Coord) (j : Fin 3) :
    cpd j (fun y => - h y) z = - cpd j h z := by
  simp [cpd, fderiv_fun_neg]

theorem chm_cylHeat_translate {ρ : Coord → ℝ} (hρ : ContDiff ℝ ∞ ρ) (ν : ℝ) (x z : Coord) :
    cylHeatT ν (fun w => ρ (x - w)) z =
      cpd 0 ρ (x - z) - ν * (cpd 1 (fun y => cpd 1 ρ y) (x - z) + cpd 2 (fun y => cpd 2 ρ y) (x - z)) := by
  have hd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hd' : ∀ j : Fin 3, Differentiable ℝ (cpd j ρ) := fun j =>
    (cpd_contDiff hρ j).differentiable (by simp)
  have second : ∀ j : Fin 3, cpd j (fun y => cpd j (fun w => ρ (x - w)) y) z =
      cpd j (fun y => cpd j ρ y) (x - z) := by
    intro j
    have : (fun y => cpd j (fun w => ρ (x - w)) y) = fun y => - cpd j ρ (x - y) :=
      funext fun y => cpd_reflect hd x y j
    rw [this, cpd_neg_fun, cpd_reflect (hd' j) x z j]
    ring
  unfold cylHeatT
  rw [cpd_reflect hd x z 0, second 1, second 2]
  ring

theorem chmMollEq_of (hL : ChmLocInt) : ChmMollEq := by
  intro r hr c ν hc hν u f hup hfp hum hfm hun hfn hheat n
  have hloc := hL c hc r hr u hup hum hun
  set ρ := chmRho n with hρdef
  have hρ : ContDiff ℝ ∞ ρ := chmRho_contDiff n
  have hcs : HasCompactSupport ρ := chmRho_compact n
  have hd1 : ∀ j : Fin 3, cdv j (chmConv ρ u) = chmConv (cpd j ρ) u :=
    fun j => funext fun x => chm_cdvConv_aux hρ hcs hloc j x
  have hd2 : ∀ j : Fin 3, ∀ x, cdv j (cdv j (chmConv ρ u)) x =
      chmConv (cpd j (fun y => cpd j ρ y)) u x := by
    intro j x
    rw [hd1 j]
    exact chm_cdvConv_aux (cpd_contDiff hρ j) (cpd_compact hcs j) hloc j x
  funext x
  -- integrability of the three integrands
  have hint : ∀ {K : Coord → ℝ}, ContDiff ℝ ∞ K → HasCompactSupport K →
      Integrable (fun y => (K y : ℂ) * u (x - y)) volume := by
    intro K hK hKc
    have := hKc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)
      hK.continuous hloc x
    simpa [ConvolutionExistsAt, Complex.real_smul] using this
  have k1s : ContDiff ℝ ∞ (cpd 1 (cpd 1 ρ)) := cpd_contDiff (cpd_contDiff hρ 1) 1
  have k1c : HasCompactSupport (cpd 1 (cpd 1 ρ)) := cpd_compact (cpd_compact hcs 1) 1
  have k2s : ContDiff ℝ ∞ (cpd 2 (cpd 2 ρ)) := cpd_contDiff (cpd_contDiff hρ 2) 2
  have k2c : HasCompactSupport (cpd 2 (cpd 2 ρ)) := cpd_compact (cpd_compact hcs 2) 2
  have h0 := hint (cpd_contDiff hρ 0) (cpd_compact hcs 0)
  have h1 := hint k1s k1c
  have h2 := hint k2s k2c
  set kk : Coord → ℝ := fun y => cpd 0 ρ y - ν * (cpd 1 (cpd 1 ρ) y + cpd 2 (cpd 2 ρ) y) with hkk
  have e1 : chmRhs ν (chmConv ρ u) x = ∫ y, (kk y : ℂ) * u (x - y) := by
    unfold chmRhs
    rw [hd1 0, hd2 1, hd2 2]
    unfold chmConv
    simp only [hkk]
    have : ∀ y, ((cpd 0 ρ y - ν * (cpd 1 (cpd 1 ρ) y + cpd 2 (cpd 2 ρ) y) : ℝ) : ℂ) * u (x - y) =
        (cpd 0 ρ y : ℂ) * u (x - y) - (ν : ℂ) * ((cpd 1 (cpd 1 ρ) y : ℂ) * u (x - y) +
          (cpd 2 (cpd 2 ρ) y : ℂ) * u (x - y)) := by
      intro y; push_cast; ring
    simp_rw [this]
    have h12 : Integrable (fun y => (ν : ℂ) * ((cpd 1 (cpd 1 ρ) y : ℂ) * u (x - y) +
        (cpd 2 (cpd 2 ρ) y : ℂ) * u (x - y))) volume := (h1.add h2).const_mul _
    symm
    rw [integral_sub h0 h12, integral_const_mul, integral_add h1 h2]
  have e2 : ∫ y, (kk y : ℂ) * u (x - y) = ∫ z, u z * (cylHeatT ν (fun w => ρ (x - w)) z : ℂ) := by
    rw [← integral_sub_left_eq_self (fun y => (kk y : ℂ) * u (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel]
    rw [chm_cylHeat_translate hρ ν x z]
    simp only [hkk]
    ring
  have htest : IsSTTestCoord (fun w => ρ (x - w)) :=
    ⟨hρ.comp (contDiff_const.sub contDiff_id), by
      have := hcs.comp_homeomorph ((Homeomorph.neg Coord).trans (Homeomorph.addLeft x))
      exact this⟩
  have e3 := hheat _ htest
  have e4 : chmConv ρ f x = ∫ z, f z * ((fun w => ρ (x - w)) z : ℂ) := by
    unfold chmConv
    rw [← integral_sub_left_eq_self (fun y => (ρ y : ℂ) * f (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel]
    ring
  rw [e1, e2, e3, e4]

end UnforcedLeray.Short.IIb
