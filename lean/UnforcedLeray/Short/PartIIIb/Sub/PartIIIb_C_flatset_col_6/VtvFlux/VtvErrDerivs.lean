import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvThetaFacts
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/11`: derivatives of the flux remainder `E_R`

Target (`VtvFluxLemmas.lean`): `VtvErrDerivs`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

`E_R(s,x) = (F(s) θ'(η/R)/R, 0)` with `F = vtvFluxF Φ R₀`, `θ = vtvTheta`.  Its only nonzero
component is `0`, and it depends on `x` only through `x.2`, so every `∂_q`-derivative vanishes and
the `∂_η`-derivatives are obtained from the one-variable chain rule for `t ↦ g(t/R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest flatDt flatGrad flatLap)

/-- `(dir 0).2 = 0`. -/
theorem vtvErrD_dir0_snd : (B0579.dir 0).2 = 0 := by simp [B0579.dir]

/-- `(dir 1).2 = 1`. -/
theorem vtvErrD_dir1_snd : (B0579.dir 1).2 = 1 := by simp [B0579.dir]

/-- Chain rule for `u ↦ g(u/R)`. -/
theorem vtvErrD_hasDerivAt_scale (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (R t : ℝ) (hR : R ≠ 0) : HasDerivAt (fun u => g (u / R)) (g' (t / R) / R) t := by
  have h1 : HasDerivAt (fun u : ℝ => u / R) (1 / R) t :=
    (hasDerivAt_id' (x := t)).div_const R
  have h2 : HasDerivAt (fun u : ℝ => g (u / R)) (g' (t / R) * (1 / R)) t :=
    (hg (t / R)).comp t h1
  have e : g' (t / R) / R = g' (t / R) * (1 / R) := by ring
  rw [e]
  exact h2

/-- Partial derivative of `y ↦ A * H(y.2)` for a one-variable `H` with derivative `H'`. -/
theorem vtvErrD_pd_snd (H H' : ℝ → ℝ) (hH : ∀ t, HasDerivAt H (H' t) t) (A : ℝ) (j : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd j (fun y => A * H y.2) x = A * (H' x.2 * (B0579.dir j).2) := by
  have hF : HasFDerivAt (fun y : ℝ × ℝ => H y.2) (H' x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hH x.2).comp_hasFDerivAt x hasFDerivAt_snd
  have hF3 : HasFDerivAt (fun y : ℝ × ℝ => A * H y.2)
      (A • (H' x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := hF.const_mul A
  unfold B0579.pd
  rw [hF3.fderiv]
  simp [smul_eq_mul]

/-- Target: `VtvErrDerivs`. -/
theorem vtvErrDerivs : VtvErrDerivs := by
  intro c Φ s₁ s₂ R₀ hS R hR s x
  have hΦ : IsFlatTest c Φ := hS.1
  -- smoothness of the flux `F(s) = Z(s, 0, R₀+1)`
  have hZ := vtvZpSmooth c Φ hΦ R₀
  have hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vtvFluxF Φ R₀) :=
    hZ.comp (contDiff_id.prodMk contDiff_const)
  have hFd : Differentiable ℝ (vtvFluxF Φ R₀) := hFc.differentiable (by simp)
  -- smoothness of the cutoff profile
  obtain ⟨hθc, -⟩ := vtvThetaFacts
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv vtvTheta) :=
    (contDiff_infty_iff_deriv.1 hθc).2
  have hDD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv vtvTheta)) :=
    (contDiff_infty_iff_deriv.1 hD).2
  have hθd : Differentiable ℝ (deriv vtvTheta) := hD.differentiable (by simp)
  have hDDd : Differentiable ℝ (deriv (deriv vtvTheta)) := hDD.differentiable (by simp)
  -- the two components of `E_R`
  have hE0 : ∀ s' y, vtvErr Φ R₀ R s' y 0 = vtvFluxF Φ R₀ s' * (deriv vtvTheta (y.2 / R) / R) := by
    intro s' y
    unfold vtvErr
    rw [if_pos rfl, mul_div_assoc]
  have hE1 : ∀ s' y, vtvErr Φ R₀ R s' y 1 = 0 := by
    intro s' y
    unfold vtvErr
    rw [if_neg (by decide)]
  -- the `∂_η` derivatives of the profile `y ↦ g(y.2/R)/R`
  have hH0 : ∀ t, HasDerivAt (fun u => deriv vtvTheta (u / R) / R)
      (deriv (deriv vtvTheta) (t / R) / R / R) t := fun t =>
    ((vtvErrD_hasDerivAt_scale (deriv vtvTheta) (deriv (deriv vtvTheta))
      (fun t => (hθd t).hasDerivAt) R t hR).div_const R)
  have hH1 : ∀ t, HasDerivAt (fun u => deriv (deriv vtvTheta) (u / R) / R / R)
      (deriv (deriv (deriv vtvTheta)) (t / R) / R / R / R) t := fun t =>
    (((vtvErrD_hasDerivAt_scale (deriv (deriv vtvTheta)) (deriv (deriv (deriv vtvTheta)))
      (fun t => (hDDd t).hasDerivAt) R t hR).div_const R).div_const R)
  have hp0 : ∀ (A : ℝ) (j : Fin 2) (x : ℝ × ℝ),
      B0579.pd j (fun y => A * (deriv vtvTheta (y.2 / R) / R)) x =
        A * (deriv (deriv vtvTheta) (x.2 / R) / R / R * (B0579.dir j).2) :=
    fun A j x => vtvErrD_pd_snd (fun u => deriv vtvTheta (u / R) / R)
      (fun t => deriv (deriv vtvTheta) (t / R) / R / R) hH0 A j x
  have hp1 : ∀ (A : ℝ) (j : Fin 2) (x : ℝ × ℝ),
      B0579.pd j (fun y => A * (deriv (deriv vtvTheta) (y.2 / R) / R / R)) x =
        A * (deriv (deriv (deriv vtvTheta)) (x.2 / R) / R / R / R * (B0579.dir j).2) :=
    fun A j x => vtvErrD_pd_snd (fun u => deriv (deriv vtvTheta) (u / R) / R / R)
      (fun t => deriv (deriv (deriv vtvTheta)) (t / R) / R / R / R) hH1 A j x
  have hc0 : ∀ x : ℝ × ℝ, B0579.pd 0 (fun _ : ℝ × ℝ => (0 : ℝ)) x = 0 := fun x => by
    simp [B0579.pd]
  have hz0 : B0579.pd 0 (fun y => vtvErr Φ R₀ R s y 0) = fun _ => 0 := by
    funext y
    simp only [hE0]
    rw [hp0, vtvErrD_dir0_snd]
    ring
  have hz1 : B0579.pd 1 (fun y => vtvErr Φ R₀ R s y 0) =
      fun y => vtvFluxF Φ R₀ s * (deriv (deriv vtvTheta) (y.2 / R) / R / R) := by
    funext y
    simp only [hE0]
    rw [hp0, vtvErrD_dir1_snd]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `∂_s E_R` in component 0
    unfold flatDt
    simp only [hE0]
    rw [((hFd s).hasDerivAt.mul_const _).deriv]
    ring
  · -- `∂_q E_R` in component 0
    unfold flatGrad
    simp only [hE0]
    rw [hp0, vtvErrD_dir0_snd]
    ring
  · -- `∂_η E_R` in component 0
    unfold flatGrad
    simp only [hE0]
    rw [hp0, vtvErrD_dir1_snd]
    ring
  · -- `Δ E_R` in component 0
    unfold flatLap UnforcedLeray.Short.IIIa.lapP
    rw [hz0, hz1, hc0, hp1, vtvErrD_dir1_snd]
    ring
  · -- `∂_s E_R` in component 1
    unfold flatDt
    simp only [hE1]
    simp
  · -- `∂_j E_R` in component 1
    intro j
    unfold flatGrad
    simp only [hE1]
    simp [B0579.pd]
  · -- `Δ E_R` in component 1
    unfold flatLap UnforcedLeray.Short.IIIa.lapP
    have hcz : ∀ j : Fin 2, B0579.pd j (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 :=
      fun j => funext fun y => by simp [B0579.pd]
    simp only [hE1, hcz, add_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
