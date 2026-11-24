import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12

/-!
# `CrossDriftCalc`: product rule for `driftT (∇c × Θ)` (source 1351-1362, 1470-1480)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The map `v ↦ a × v` as an `ℝ`-linear map. -/
def cdcLin (a : CVec3) : CVec3 →ₗ[ℝ] CVec3 where
  toFun v := crossC a v
  map_add' v w := by
    ext i; fin_cases i <;> simp [crossC] <;> ring
  map_smul' r v := by
    ext i; fin_cases i <;> simp [crossC] <;> ring

/-- The map `v ↦ a × v` as a continuous `ℝ`-linear map. -/
def cdcL (a : CVec3) : CVec3 →L[ℝ] CVec3 := LinearMap.toContinuousLinearMap (cdcLin a)

theorem cdcL_apply (a v : CVec3) : cdcL a v = crossC a v := rfl

theorem cdc_crossC_sub (a b v : CVec3) : crossC (a - b) v = crossC a v - crossC b v := by
  ext i; fin_cases i <;> simp [crossC] <;> ring

theorem cdc_crossC_gradC (c : Space → ℝ) (y : Space) (b : CVec3) :
    crossC (gradC c y) b = ∑ j : Fin 3, (sd j c y) • crossC (EuclideanSpace.single j (1 : ℂ)) b := by
  ext i
  fin_cases i <;> simp [crossC, gradC, Fin.sum_univ_three] <;> ring

theorem cdc_dy_clm {Θ : ℝ × Space → CVec3} (hΘ : Differentiable ℝ Θ) (a : CVec3) (j : Fin 3)
    (p : ℝ × Space) :
    dy j (fun q => cdcL a (Θ q)) p = cdcL a (dy j Θ p) := by
  have h : HasFDerivAt (fun q => cdcL a (Θ q)) ((cdcL a).comp (fderiv ℝ Θ p)) p :=
    (cdcL a).hasFDerivAt.comp p (hΘ p).hasFDerivAt
  show fderiv ℝ (fun q => cdcL a (Θ q)) p (0, coordinateVector j)
      = cdcL a (fderiv ℝ Θ p (0, coordinateVector j))
  rw [h.fderiv]
  rfl

theorem cdc_dτ_clm {Θ : ℝ × Space → CVec3} (hΘ : Differentiable ℝ Θ) (a : CVec3)
    (p : ℝ × Space) :
    dτ (fun q => cdcL a (Θ q)) p = cdcL a (dτ Θ p) := by
  have h : HasFDerivAt (fun q => cdcL a (Θ q)) ((cdcL a).comp (fderiv ℝ Θ p)) p :=
    (cdcL a).hasFDerivAt.comp p (hΘ p).hasFDerivAt
  show fderiv ℝ (fun q => cdcL a (Θ q)) p (1, 0) = cdcL a (fderiv ℝ Θ p (1, 0))
  rw [h.fderiv]
  rfl

/-- `driftT` commutes with a constant cross product. -/
theorem cdc_driftT_clm {Θ : ℝ × Space → CVec3} (hΘ : ContDiff ℝ ∞ Θ) (a : CVec3) (p : ℝ × Space) :
    driftT (fun q => cdcL a (Θ q)) p = cdcL a (driftT Θ p) := by
  have hd : Differentiable ℝ Θ := hΘ.differentiable (by simp)
  simp only [driftT, radialT, cdc_dτ_clm hd, cdc_dy_clm hd, map_add, map_neg, map_sum, map_smul]

theorem cdc_dτ_add {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) :
    dτ (A + B) = dτ A + dτ B := by
  funext p
  simp [dτ, fderiv_add (hA p) (hB p)]

theorem cdc_driftT_add {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    driftT (A + B) = driftT A + driftT B := by
  have hdA : Differentiable ℝ A := hA.differentiable (by simp)
  have hdB : Differentiable ℝ B := hB.differentiable (by simp)
  funext p
  simp only [driftT, radialT, Pi.add_apply, cdc_dτ_add hdA hdB, dy_add hdA hdB, smul_add,
    Finset.sum_add_distrib]
  abel

/-- `∂_a ∂_b` commute on smooth scalar functions. -/
theorem cdc_fderiv_fderiv_apply {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) (v w y : Space) :
    fderiv ℝ (fun y' => fderiv ℝ c y' w) y v = fderiv ℝ (fderiv ℝ c) y v w := by
  have hd : Differentiable ℝ (fderiv ℝ c) :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y' => fderiv ℝ c y' w) ((fderiv ℝ (fderiv ℝ c) y).flip w) y := by
    simpa using (hd y).hasFDerivAt.clm_apply (hasFDerivAt_const w y)
  rw [hx.fderiv]
  rfl

theorem cdc_sd_sd_comm {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) (j k : Fin 3) (y : Space) :
    sd j (sd k c) y = sd k (sd j c) y := by
  have hsymm : IsSymmSndFDerivAt ℝ c y := (hc.contDiffAt : ContDiffAt ℝ ∞ c y).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun y' => fderiv ℝ c y' (coordinateVector k)) y (coordinateVector j)
      = fderiv ℝ (fun y' => fderiv ℝ c y' (coordinateVector j)) y (coordinateVector k)
  rw [cdc_fderiv_fderiv_apply hc, cdc_fderiv_fderiv_apply hc]
  exact hsymm.eq _ _

theorem cdc_sd_radS {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) (j : Fin 3) (y : Space) :
    sd j (radS c) y = sd j c y + radS (sd j c) y := by
  have hterm : ∀ k : Fin 3, HasFDerivAt (fun y' : Space => y' k * sd k c y')
      (y k • fderiv ℝ (sd k c) y + sd k c y • (EuclideanSpace.proj k : Space →L[ℝ] ℝ)) y := by
    intro k
    have h1 : HasFDerivAt (fun y' : Space => y' k) (EuclideanSpace.proj k : Space →L[ℝ] ℝ) y :=
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt
    have h2 : HasFDerivAt (sd k c) (fderiv ℝ (sd k c) y) y :=
      ((contDiff_sd hc k).differentiable (by simp) y).hasFDerivAt
    exact h1.mul h2
  have hsum : HasFDerivAt (fun y' : Space => ∑ k : Fin 3, y' k * sd k c y')
      (∑ k : Fin 3, (y k • fderiv ℝ (sd k c) y + sd k c y • (EuclideanSpace.proj k : Space →L[ℝ] ℝ))) y :=
    HasFDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  have hr : radS c = fun y' : Space => ∑ k : Fin 3, y' k * sd k c y' := rfl
  show fderiv ℝ (radS c) y (coordinateVector j) = _
  rw [hr, hsum.fderiv]
  simp [radS, Finset.sum_add_distrib, sd, coordinateVector]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun z => y k * z) (cdc_sd_sd_comm hc j k y)

theorem cdc_radS_sd {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) (j : Fin 3) (y : Space) :
    radS (sd j c) y = sd j (radS c) y - sd j c y := by
  rw [cdc_sd_radS hc j y]
  ring

/-- **Calculus** (product rule): for smooth `c` and smooth `Θ`,
`driftT (∇c × Θ) = ∇c × driftT Θ + ½ (∇(y·∇c) - ∇c) × Θ`. -/
theorem crossDriftCalc : CrossDriftCalc := by
  intro c hc Θ hΘ p
  have hG : ∀ j : Fin 3, ContDiff ℝ ∞
      (fun q : ℝ × Space => cdcL (EuclideanSpace.single j (1 : ℂ)) (Θ q)) :=
    fun j => (cdcL _).contDiff.comp hΘ
  have hM : ∀ j : Fin 3, ContDiff ℝ ∞
      (mulT (sd j c) (fun q : ℝ × Space => cdcL (EuclideanSpace.single j (1 : ℂ)) (Θ q))) :=
    fun j => contDiff_mulT (contDiff_sd hc j) (hG j)
  have hF : (fun q : ℝ × Space => crossC (gradC c q.2) (Θ q)) =
      mulT (sd 0 c) (fun q : ℝ × Space => cdcL (EuclideanSpace.single 0 (1 : ℂ)) (Θ q))
        + mulT (sd 1 c) (fun q : ℝ × Space => cdcL (EuclideanSpace.single 1 (1 : ℂ)) (Θ q))
        + mulT (sd 2 c) (fun q : ℝ × Space => cdcL (EuclideanSpace.single 2 (1 : ℂ)) (Θ q)) := by
    funext q
    rw [cdc_crossC_gradC c q.2 (Θ q), Fin.sum_univ_three]
    simp only [Pi.add_apply, mulT, cdcL_apply]
  have hAB : ContDiff ℝ ∞ (mulT (sd 0 c) (fun q : ℝ × Space => cdcL (EuclideanSpace.single 0 (1 : ℂ)) (Θ q))
      + mulT (sd 1 c) (fun q : ℝ × Space => cdcL (EuclideanSpace.single 1 (1 : ℂ)) (Θ q))) :=
    (hM 0).add (hM 1)
  rw [hF, cdc_driftT_add hAB (hM 2), cdc_driftT_add (hM 0) (hM 1)]
  simp only [Pi.add_apply]
  rw [driftT_mulT_apply (contDiff_sd hc 0) (hG 0), driftT_mulT_apply (contDiff_sd hc 1) (hG 1),
    driftT_mulT_apply (contDiff_sd hc 2) (hG 2)]
  rw [cdc_driftT_clm hΘ, cdc_driftT_clm hΘ, cdc_driftT_clm hΘ]
  simp only [cdcL_apply]
  rw [cdc_crossC_gradC c p.2 (driftT Θ p), cdc_crossC_sub, cdc_crossC_gradC (radS c) p.2 (Θ p),
    cdc_crossC_gradC c p.2 (Θ p)]
  rw [cdc_radS_sd hc 0 p.2, cdc_radS_sd hc 1 p.2, cdc_radS_sd hc 2 p.2]
  simp only [Fin.sum_univ_three]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
