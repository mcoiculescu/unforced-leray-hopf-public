import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPGradC1.C1Calculus
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_2

/-!
# `IBPAdjointC2`: `L₀ᵗ + μ` is the transpose of `D_μ` on `C²` periodic fields (source 4140-4141, 5001-5008)

`C²` version of `ibpAdjoint_proved` and `ibpBridge_proved`
(`Short/PartIII-b/Sub/IIIb-D2_3_2/Sub/IIIb-D2_3_2_8_{1,2}.lean`): the Lagrange identity
`L₀ᵗΦ·u - Φ·L₀u = ∂_τ(…) + Σ_j ∂_{y_j}(…)` needs only two derivatives of `u`; the slab integrals of
the `C¹` divergence terms vanish by `c1_slab_dtau` and `c1_slab_dy` (`IBPGradC1/C1Calculus.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.IIb

/-- `∂_{y_j}` of a `C²` function is `C¹`. -/
theorem c2_cd_dy {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : ℝ × Space → F}
    (hG : ContDiff ℝ 2 G) (j : Fin 3) : ContDiff ℝ 1 (dy j G) :=
  (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem c2_cont_dτ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : ℝ × Space → F}
    (hG : ContDiff ℝ 1 G) : Continuous (dτ G) :=
  (hG.continuous_fderiv (by simp)).clm_apply continuous_const

theorem c2_cont_dy {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : ℝ × Space → F}
    (hG : ContDiff ℝ 1 G) (j : Fin 3) : Continuous (dy j G) :=
  (hG.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Lagrange identity for `Δ`, `u ∈ C²`. -/
theorem c2_lagrange_lap {Φ u : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (hu : ContDiff ℝ 2 u)
    (p : ℝ × Space) :
    dotL (lapT Φ p) (u p) - dotL (Φ p) (lapT u p) =
      ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) p := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdyΦ : ∀ j, Differentiable ℝ (dy j Φ) := fun j =>
    (UnforcedLeray.PhaseSpace.contDiff_dy hΦ j).differentiable (by simp)
  have hdyu : ∀ j, Differentiable ℝ (dy j u) := fun j =>
    (c2_cd_dy hu j).differentiable (by simp)
  have hsub : ∀ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) p =
      dy j (dotFn (dy j Φ) u) p - dy j (dotFn Φ (dy j u)) p := fun j => by
    have h : HasFDerivAt (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p)
        (fderiv ℝ (dotFn (dy j Φ) u) p - fderiv ℝ (dotFn Φ (dy j u)) p) p :=
      ((differentiable_dotFn (hdyΦ j) hud) p).hasFDerivAt.sub
        ((differentiable_dotFn hΦd (hdyu j)) p).hasFDerivAt
    simp only [dy]
    rw [h.fderiv]
    rfl
  simp only [hsub, dy_dotFn (hdyΦ _) hud, dy_dotFn hΦd (hdyu _)]
  simp [lapT, dotL_apply, Fin.sum_univ_three]
  ring

/-- Lagrange identity for `L₀`, `u ∈ C²`. -/
theorem c2_lagrange_L0 (ν : ℝ) {Φ u : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (hu : ContDiff ℝ 2 u) (p : ℝ × Space) :
    dotL (L0T ν Φ p) (u p) - dotL (Φ p) (L0 ν u p) =
      -dτ (dotFn Φ u) p +
        (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) p -
        (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) p := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  rw [← lagrange_T0 hΦd hud p, ← c2_lagrange_lap hΦ hu p]
  simp only [L0T, L0, nuLapT, Pi.sub_apply, Pi.smul_apply]
  simp [dotL_apply, Fin.sum_univ_three, Complex.real_smul]
  ring

set_option maxHeartbeats 1000000 in
theorem c2_dotFn_contDiff {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ 1 A)
    (hB : ContDiff ℝ 1 B) : ContDiff ℝ 1 (dotFn A B) := by
  have h := (UnforcedLeray.B0005.dotR.isBoundedBilinearMap.contDiff (n := 1)).comp (hA.prodMk hB)
  exact h

/-- **The core identity** for a `C²` periodic complex field `U`. -/
theorem ibpAdjointC2_core (P ν μ : ℝ) (hP : 0 < P) (U : ℝ × Space → CVec3)
    (hU : ContDiff ℝ 2 U) (hper : ∀ x : ℝ × Space, U (x.1 + P, x.2) = U x)
    (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) U =
      pairF P Φ (fun x => L0 ν U x + (μ : ℂ) • U x) := by
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hΦ1 : ContDiff ℝ 1 Φ := hΦc.of_le (by simp)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hbil : ∀ {A B : ℝ × Space → CVec3}, ContDiff ℝ 1 A → ContDiff ℝ 1 B →
      ContDiff ℝ 1 (dotFn A B) := fun hA hB => c2_dotFn_contDiff hA hB
  have hD : ContDiff ℝ 1 (dotFn Φ U) := hbil hΦ1 hU1
  have hDper : ∀ τ y, dotFn Φ U (τ + P, y) = dotFn Φ U (τ, y) := by
    intro τ y
    show dotL (Φ (τ + P, y)) (U (τ + P, y)) = dotL (Φ (τ, y)) (U (τ, y))
    rw [hΦ.periodic τ y, hper (τ, y)]
  have hDR : ∀ τ y, R < ‖y‖ → dotFn Φ U (τ, y) = 0 := fun τ y hy => by
    simp [dotFn, hR τ y hy]
  have hτ := c1_slab_dtau hP hD hDper hDR
  have hY : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) ∧
        ∫ z, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ 1 (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) :=
      (Complex.ofRealCLM.contDiff.comp
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd)).mul hD
    exact c1_slab_dy (R := R) hK (fun τ y hy => by simp [hDR τ y hy]) j
  have hN : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z)
        (srwfSlab P) ∧
        ∫ z, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ 1 (fun p : ℝ × Space => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) :=
      (hbil ((UnforcedLeray.PhaseSpace.contDiff_dy hΦc j).of_le (by simp)) hU1).sub
        (hbil hΦ1 (c2_cd_dy hU j))
    exact c1_slab_dy (R := R) hK
      (fun τ y hy => by simp [dotFn, hR τ y hy, srwf_dy_bdd hR j τ y hy]) j
  have hlag : ∀ z : ℝ × Space,
      dotL (L0T ν Φ z) (U z) - dotL (Φ z) (L0 ν U z) = srwf_lagRHS ν Φ U z :=
    fun z => c2_lagrange_L0 ν hΦc hU z
  have i1 : Integrable (fun z => -dτ (dotFn Φ U) z) (srwfSlab P) := hτ.1.neg
  have i2 : Integrable (fun z => (1 / 2 : ℂ) *
      ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) :=
    (integrable_finsetSum _ fun j _ => (hY j).1).const_mul _
  have i3 : Integrable (fun z => (ν : ℂ) *
      ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z)
      (srwfSlab P) :=
    (integrable_finsetSum _ fun j _ => (hN j).1).const_mul _
  have hRHSint : Integrable (srwf_lagRHS ν Φ U) (srwfSlab P) := (i1.add i2).sub i3
  have hRHSzero : ∫ z, srwf_lagRHS ν Φ U z ∂(srwfSlab P) = 0 := by
    have e : (fun z => srwf_lagRHS ν Φ U z) = fun z =>
        (-dτ (dotFn Φ U) z + (1 / 2 : ℂ) *
          ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) -
        (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) U p - dotFn Φ (dy j U) p) z :=
      rfl
    have i12 : Integrable (fun z => -dτ (dotFn Φ U) z + (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ U p) z) (srwfSlab P) :=
      i1.add i2
    rw [e, integral_sub i12 i3, integral_add i1 i2, integral_neg,
      integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun j _ => (hY j).1,
      integral_finsetSum _ fun j _ => (hN j).1,
      Finset.sum_eq_zero fun j _ => (hY j).2, Finset.sum_eq_zero fun j _ => (hN j).2, hτ.2]
    simp
  -- continuity and integrability of `Φ·(L₀U + μU)`
  have hL0c : Continuous (L0 ν U) := by
    have hdyc : ∀ j, Continuous (dy j U) := fun j => c2_cont_dy hU1 j
    have hrad : Continuous (radialT U) := by
      unfold radialT
      exact continuous_finsetSum _ fun j _ =>
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp continuous_snd).smul (hdyc j)
    have hlap : Continuous (lapT U) := by
      unfold lapT
      exact continuous_finsetSum _ fun j _ => c2_cont_dy (c2_cd_dy hU j) j
    unfold L0 T0
    exact (((c2_cont_dτ hU1).sub (hrad.const_smul (1 / 2 : ℝ))).sub
      (hlap.const_smul ν)).sub (hU1.continuous.const_smul (1 / 2 : ℝ))
  have hgc : Continuous (fun z => dotL (Φ z) (L0 ν U z + (μ : ℂ) • U z)) :=
    (dotL.continuous.comp hΦc.continuous).clm_apply
      (hL0c.add (hU1.continuous.const_smul (μ : ℂ)))
  have hgint : Integrable (fun z => dotL (Φ z) (L0 ν U z + (μ : ℂ) • U z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hgc (R := R)
      (fun t y hy => by simp [hR t y hy])
  have hdiff : ∀ z : ℝ × Space,
      dotL (L0T ν Φ z + (μ : ℂ) • Φ z) (U z) =
        dotL (Φ z) (L0 ν U z + (μ : ℂ) • U z) + srwf_lagRHS ν Φ U z := by
    intro z
    have h := hlag z
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination h
  have hsum : Integrable (fun z => dotL (Φ z) (L0 ν U z + (μ : ℂ) • U z) +
      srwf_lagRHS ν Φ U z) (srwfSlab P) := hgint.add hRHSint
  show phaseInt P (fun x => dotL (L0T ν Φ x + (μ : ℂ) • Φ x) (U x)) =
    phaseInt P (fun x => dotL (Φ x) (L0 ν U x + (μ : ℂ) • U x))
  rw [show (fun x => dotL (L0T ν Φ x + (μ : ℂ) • Φ x) (U x)) =
      fun x => dotL (Φ x) (L0 ν U x + (μ : ℂ) • U x) + srwf_lagRHS ν Φ U x from funext hdiff]
  rw [srwf_phaseInt_eq hsum, srwf_phaseInt_eq hgint, integral_add hgint hRHSint, hRHSzero,
    add_zero]

/-! ## The `C²` bridge `L₀ + μ = D_μ` -/

theorem c2_br_dtau (H : ℝ → Space → Space) (hH : ContDiff ℝ 2 (fun x : ℝ × Space => H x.1 x.2))
    (x : ℝ × Space) :
    dτ (realCf H) x = br_RC (deriv (fun t => H t x.2) x.1) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by norm_num)
  have hs : fderiv ℝ (fun t => H t x.2) x.1 =
      (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x).comp (ContinuousLinearMap.inl ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_time (hd x)
  have hdev : deriv (fun t => H t x.2) x.1 = fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x (1, 0) := by
    rw [← fderiv_apply_one_eq_deriv, hs]
    rfl
  show fderiv ℝ (realCf H) x (1, 0) = _
  rw [br_realCf_eq H, br_fderiv_RC (fun w => H w.1 w.2) hd x (1, 0), hdev]

theorem c2_br_dy (H : ℝ → Space → Space) (hH : ContDiff ℝ 2 (fun x : ℝ × Space => H x.1 x.2))
    (j : Fin 3) (x : ℝ × Space) :
    dy j (realCf H) x = br_RC (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x (0, coordinateVector j)) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by norm_num)
  show fderiv ℝ (realCf H) x (0, coordinateVector j) = _
  rw [br_realCf_eq H, br_fderiv_RC (fun w => H w.1 w.2) hd x (0, coordinateVector j)]

theorem c2_br_radialT (H : ℝ → Space → Space)
    (hH : ContDiff ℝ 2 (fun x : ℝ × Space => H x.1 x.2)) (x : ℝ × Space) :
    radialT (realCf H) x = br_RC (fderiv ℝ (H x.1) x.2 x.2) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by norm_num)
  have hsl : ∀ j : Fin 3, fderiv ℝ (H x.1) x.2 (coordinateVector j) =
      fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x (0, coordinateVector j) := by
    intro j
    have hs : fderiv ℝ (fun y => H x.1 y) x.2 =
        (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
      UnforcedLeray.B0005.fderiv_slice_space (hd x)
    rw [show fderiv ℝ (H x.1) x.2 = fderiv ℝ (fun y => H x.1 y) x.2 from rfl, hs]
    rfl
  have hv : fderiv ℝ (H x.1) x.2 x.2 = ∑ j : Fin 3, x.2 j • fderiv ℝ (H x.1) x.2 (coordinateVector j) := by
    calc fderiv ℝ (H x.1) x.2 x.2
        = fderiv ℝ (H x.1) x.2 (∑ j : Fin 3, x.2 j • coordinateVector j) := by
          rw [← br_expand x.2]
      _ = ∑ j : Fin 3, x.2 j • fderiv ℝ (H x.1) x.2 (coordinateVector j) := by
          rw [map_sum]
          simp [map_smul]
  unfold radialT
  simp only [c2_br_dy H hH, ← hsl]
  rw [hv, map_sum]
  simp only [map_smul]

theorem c2_br_lapT (H : ℝ → Space → Space) (hH : ContDiff ℝ 2 (fun x : ℝ × Space => H x.1 x.2))
    (x : ℝ × Space) :
    lapT (realCf H) x = br_RC (physLap (H x.1) x.2) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by norm_num)
  have hK : ∀ j : Fin 3, ContDiff ℝ 1 (fun w : ℝ × Space =>
      fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w (0, coordinateVector j)) := fun j =>
    (hH.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hKd : ∀ j : Fin 3, Differentiable ℝ (fun w : ℝ × Space =>
      fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w (0, coordinateVector j)) := fun j =>
    (hK j).differentiable (by simp)
  have hlap : lapT (realCf H) x = ∑ j : Fin 3, br_RC (fderiv ℝ (fun w : ℝ × Space =>
      fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w (0, coordinateVector j)) x
        (0, coordinateVector j)) := by
    unfold lapT
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : dy j (realCf H) = fun w => br_RC (fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w
        (0, coordinateVector j)) := funext fun w => c2_br_dy H hH j w
    rw [e]
    unfold dy
    rw [br_fderiv_RC _ (hKd j) x (0, coordinateVector j)]
  rw [hlap, ← map_sum]
  congr 1
  unfold physLap physPd2 physPd
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun y' => fderiv ℝ (H x.1) y' (coordinateVector j)) =
      fun y' => fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) (x.1, y') (0, coordinateVector j) := by
    funext y'
    have hs : fderiv ℝ (fun y => H x.1 y) y' =
        (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) (x.1, y')).comp
          (ContinuousLinearMap.inr ℝ ℝ Space) :=
      UnforcedLeray.B0005.fderiv_slice_space (hd (x.1, y'))
    rw [show fderiv ℝ (H x.1) y' = fderiv ℝ (fun y => H x.1 y) y' from rfl, hs]
    rfl
  rw [e1]
  have hs2 : fderiv ℝ (fun y' => fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) (x.1, y')
      (0, coordinateVector j)) x.2 =
      (fderiv ℝ (fun w : ℝ × Space => fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w
        (0, coordinateVector j)) x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_space ((hKd j) x)
  rw [hs2]
  rfl

theorem c2_bridge (ν μ : ℝ) (H : ℝ → Space → Space)
    (hH : ContDiff ℝ 2 (fun x : ℝ × Space => H x.1 x.2)) (x : ℝ × Space) :
    L0 ν (realCf H) x + (μ : ℂ) • realCf H x = realCf (physDmu ν μ H) x := by
  unfold L0 T0
  rw [c2_br_dtau H hH x, c2_br_radialT H hH x, c2_br_lapT H hH x]
  rw [show realCf H x = br_RC (H x.1 x.2) from rfl,
    show realCf (physDmu ν μ H) x = br_RC (physDmu ν μ H x.1 x.2) from rfl]
  unfold physDmu
  rw [Complex.coe_smul]
  simp only [map_sub, map_add, map_smul]
  module

theorem ibpAdjointC2 : IBPAdjointC2 := by
  intro P ν μ hP u hu hper Φ hΦ
  have hU : ContDiff ℝ 2 (realCf u) := br_RC.contDiff.comp hu
  have hUp : ∀ x : ℝ × Space, realCf u (x.1 + P, x.2) = realCf u x := fun x => by
    show br_RC (u (x.1 + P) x.2) = br_RC (u x.1 x.2)
    rw [hper]
  have h := ibpAdjointC2_core P ν μ hP (realCf u) hU hUp Φ hΦ
  rw [h]
  unfold pairF
  congr 2
  funext x
  exact congrArg (dotL (Φ x)) (c2_bridge ν μ u hu x)

end UnforcedLeray.Short.PartIIIb.Concrete
