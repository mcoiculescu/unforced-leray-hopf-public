import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Proof of `SCPsiF_meas` (source 4178-4186, 4917-4937)

For `t > 1` and `x ∈ psiU ν`, the `k`-th jet of `y ↦ t Z_z(L_t y)` at `x` is
`t • (D^k Z_z(L_t x)).compContinuousLinearMap (fun _ => L_t)`, where `L_t = t P₁ + P₀` is linear in
`t`.  Each factor is continuous in `t` on `(1,∞)`, hence so is the jet, and a continuous function on
`Ioi 1` is a.e.-strongly measurable for the restricted measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PsiFMeasAux

/-- The linear part `y ↦ (y₀, y₁, 0)`. -/
def P1 : Vec3 →L[ℝ] Vec3 :=
  ContinuousLinearMap.pi ![(ContinuousLinearMap.proj 0 : Vec3 →L[ℝ] ℝ),
    (ContinuousLinearMap.proj 1 : Vec3 →L[ℝ] ℝ), 0]

/-- The linear part `y ↦ (0, 0, y₂)`. -/
def P0 : Vec3 →L[ℝ] Vec3 :=
  ContinuousLinearMap.pi ![0, 0, (ContinuousLinearMap.proj 2 : Vec3 →L[ℝ] ℝ)]

/-- `L_t = t P₁ + P₀`. -/
def Lt (t : ℝ) : Vec3 →L[ℝ] Vec3 := t • P1 + P0

theorem Lt_apply (t : ℝ) (y : Vec3) : Lt t y = ![t * y 0, t * y 1, y 2] := by
  funext i
  fin_cases i <;> simp [Lt, P1, P0]

theorem Lt_continuous : Continuous fun t : ℝ => Lt t :=
  (continuous_id.smul continuous_const).add continuous_const

/-- `S_ν = {eucSq > 11ν/12}`. -/
def SetS (ν : ℝ) : Set Vec3 := {w | ν * (11 / 12) < eucSq w}

theorem SetS_isOpen (ν : ℝ) : IsOpen (SetS ν) := by
  unfold SetS
  exact isOpen_lt continuous_const (by unfold eucSq; fun_prop)

theorem Lt_mem_SetS (ν t : ℝ) (ht : 1 < t) (y : Vec3) (hy : y ∈ psiU ν) :
    Lt t y ∈ SetS ν := by
  have h1 : ν * (11 / 12) < eucSq y := hy.1
  show ν * (11 / 12) < eucSq (Lt t y)
  rw [Lt_apply]
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hE : eucSq (![t * y 0, t * y 1, y 2] : Vec3)
      = t ^ 2 * (y 0) ^ 2 + t ^ 2 * (y 1) ^ 2 + (y 2) ^ 2 := by
    simp [eucSq, Fin.sum_univ_three]
    ring
  have hE' : eucSq y = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
    simp [eucSq, Fin.sum_univ_three]
  rw [hE']at h1
  rw [hE]
  nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sq_nonneg (y 0)),
    mul_nonneg (sub_nonneg.2 ht2) (sq_nonneg (y 1)), sq_nonneg (y 0), sq_nonneg (y 1)]

end PsiFMeasAux

open PsiFMeasAux

theorem scPsiF_meas : SCPsiF_meas := by
  unfold SCPsiF_meas
  intro ν B Z hν hB hZ k hk x hx
  have hk7 : (k : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hk
  have hZc : ContDiffOn ℝ 7 Z (SetS ν) := hZ.1
  have hZ2 : ContDiffOn ℝ 7 (fun w : Vec3 => Z w 2) (SetS ν) :=
    (contDiff_apply ℝ ℝ (2 : Fin 3)).comp_contDiffOn hZc
  -- the jet formula
  have hformula : ∀ t : ℝ, 1 < t →
      iteratedFDeriv ℝ k (psiF Z t) x =
        t • ((iteratedFDeriv ℝ k (fun w : Vec3 => Z w 2) (Lt t x)).compContinuousLinearMap
          (fun _ => Lt t)) := by
    intro t ht
    have hLc : ContDiffOn ℝ 7 (fun y : Vec3 => (Lt t y)) (psiU ν) :=
      (Lt t).contDiff.contDiffOn
    have hmapT : MapsTo (fun y : Vec3 => Lt t y) (psiU ν) (SetS ν) :=
      fun y hy => Lt_mem_SetS ν t ht y hy
    have hcomp7 : ContDiffOn ℝ 7 (fun y : Vec3 => Z (Lt t y) 2) (psiU ν) :=
      (contDiff_apply ℝ ℝ (2 : Fin 3)).comp_contDiffOn (hZc.comp hLc hmapT)
    have hcomp7x : ContDiffAt ℝ k (fun y : Vec3 => Z (Lt t y) 2) x :=
      ((hcomp7.contDiffAt ((psiU_isOpen ν).mem_nhds hx)).of_le hk7)
    have e1 : psiF Z t = fun y => t • (fun y : Vec3 => Z (Lt t y) 2) y := by
      funext y
      simp only [psiF, Lt_apply, smul_eq_mul]
    rw [e1, iteratedFDeriv_const_smul_apply' hcomp7x]
    congr 1
    -- chain rule with the linear map `Lt t`
    have hpre : IsOpen ((Lt t) ⁻¹' SetS ν) := (SetS_isOpen ν).preimage (Lt t).continuous
    have hxpre : x ∈ (Lt t) ⁻¹' SetS ν := Lt_mem_SetS ν t ht x hx
    have hchain := ContinuousLinearMap.iteratedFDerivWithin_comp_right (Lt t) hZ2
      (SetS_isOpen ν).uniqueDiffOn hpre.uniqueDiffOn hxpre (i := k) hk7
    rw [iteratedFDerivWithin_of_isOpen k hpre hxpre,
      iteratedFDerivWithin_of_isOpen k (SetS_isOpen ν) hxpre] at hchain
    exact hchain
  -- continuity in `t` of the jet on `Ioi 1`
  have hLx : ContinuousOn (fun t : ℝ => Lt t x) (Ioi (1 : ℝ)) :=
    (Lt_continuous.clm_apply continuous_const).continuousOn
  have hmapx : MapsTo (fun t : ℝ => Lt t x) (Ioi (1 : ℝ)) (SetS ν) :=
    fun t ht => Lt_mem_SetS ν t ht x hx
  have hJ : ContinuousOn (iteratedFDeriv ℝ k (fun w : Vec3 => Z w 2)) (SetS ν) :=
    ContinuousOn.continuousOn_iteratedFDeriv hZ2 (SetS_isOpen ν) hk7
  have hM : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ k (fun w : Vec3 => Z w 2) (Lt t x))
      (Ioi (1 : ℝ)) :=
    hJ.comp hLx hmapx
  have hAn := ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap
    (𝕜 := ℝ) (Fm := fun _ : Fin k => Vec3) (Em := fun _ : Fin k => Vec3) (G := ℝ)
    (t := (Set.univ : Set ((Π _ : Fin k, Vec3 →L[ℝ] Vec3) ×
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec3) ℝ))))
  have hΦ : ContinuousOn (fun t : ℝ => fun _ : Fin k => Lt t) (Ioi (1 : ℝ)) :=
    (continuous_pi fun _ => Lt_continuous).continuousOn
  have hQ : ContinuousOn (fun t : ℝ =>
      (iteratedFDeriv ℝ k (fun w : Vec3 => Z w 2) (Lt t x)).compContinuousLinearMap
        (fun _ => Lt t)) (Ioi (1 : ℝ)) := by
    have h := hAn.continuousOn.comp (ContinuousOn.prodMk hΦ hM) (mapsTo_univ _ _)
    exact h
  have hcont : ContinuousOn (fun t : ℝ => t • ((iteratedFDeriv ℝ k (fun w : Vec3 => Z w 2)
      (Lt t x)).compContinuousLinearMap (fun _ => Lt t))) (Ioi (1 : ℝ)) :=
    ContinuousOn.smul continuousOn_id hQ
  have hEq : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ k (psiF Z t) x) (Ioi (1 : ℝ)) :=
    hcont.congr (fun t ht => hformula t ht)
  exact hEq.aestronglyMeasurable measurableSet_Ioi

end UnforcedLeray.Short.PartIIIb.Concrete
