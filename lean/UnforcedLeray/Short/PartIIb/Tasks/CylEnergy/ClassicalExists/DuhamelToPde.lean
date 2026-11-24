import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.FreePart
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TranspClass
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv

/-!


Source of record: `the November 2 reference manuscript`, lines 2074-2093 and
2103-2105. Uses `freePart` (`/12`), `transpClass` (`/13`), `convRegular` (`/10`) and
`convTimeDeriv` (`/11`). The derivative of `u = free - G` in `σ` is the derivative of the free
part minus the time derivative of the Duhamel convolution `G` (`ConvTimeDeriv`), and the spatial
Laplacian of `G` is the sum of the kernel integrals (`ConvRegular`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

theorem duhamelToPde_pd_sub {f g : Pl → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) :
    B0579.pd j (fun y => f y - g y) = fun y => B0579.pd j f y - B0579.pd j g y := by
  funext y
  unfold B0579.pd
  rw [fderiv_fun_sub (hf y) (hg y)]
  rfl

theorem duhamelToPde_pd_diff {f : Pl → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    Differentiable ℝ (B0579.pd j f) := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact hfd.clm_apply (differentiable_const _)

theorem duhamelToPde_lapP_sub {f g : Pl → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : Pl) : lapP (fun y => f y - g y) x = lapP f x - lapP g x := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have e0 : ∀ y : Pl, B0579.pd 0 (B0579.pd 0 (fun z => f z - g z)) y =
      B0579.pd 0 (B0579.pd 0 f) y - B0579.pd 0 (B0579.pd 0 g) y := by
    intro y
    rw [duhamelToPde_pd_sub hf1 hg1 0,
      duhamelToPde_pd_sub (duhamelToPde_pd_diff hf 0) (duhamelToPde_pd_diff hg 0) 0]
  have e1 : ∀ y : Pl, B0579.pd 1 (B0579.pd 1 (fun z => f z - g z)) y =
      B0579.pd 1 (B0579.pd 1 f) y - B0579.pd 1 (B0579.pd 1 g) y := by
    intro y
    rw [duhamelToPde_pd_sub hf1 hg1 1,
      duhamelToPde_pd_sub (duhamelToPde_pd_diff hf 1) (duhamelToPde_pd_diff hg 1) 1]
  unfold lapP
  rw [e0 x, e1 x]
  ring

theorem duhamelToPde : UnforcedLeray.Short.IIb.CylPDE.DuhamelToPde := by
  intro c ν s T v hc hν hs hsT hv f hf u hu σ hσ x
  obtain ⟨B, hB⟩ := hu.cls
  have hB0 : 0 ≤ B := by
    have h := hB.bound s ⟨le_rfl, hsT⟩ 0
    have hW : 0 ≤ W2 (u s) 0 := by unfold W2; positivity
    have h2 : 0 ≤ W2 (u s) 0 * Real.cosh (0 : Pl).2 := mul_nonneg hW (Real.cosh_pos _).le
    linarith
  obtain ⟨K, hK0, hTr⟩ := transpClass c s T v hv hs hsT
  obtain ⟨hFR, hFW⟩ := hTr u (fun _ => B) (fun σ' hσ' => hB.c2 σ' hσ') hB.cont0 hB.cont1
    hB.cont2 (fun σ' hσ' y => hB.bound σ' hσ' y)
  have hFW' : ∀ r ∈ Icc s T, WB (K * B) (transp v u r) ∧
      ∀ j : Fin 2, WB (K * B) (B0579.pd j (transp v u r)) :=
    fun r hr => ⟨(hFW r hr).1, fun j => (hFW r hr).2 j⟩
  obtain ⟨_K2, -, hCR⟩ := convRegular ν s T hν hsT
  obtain ⟨hreg, -, -, -, -, -⟩ := hCR (transp v u) hFR (fun _ => K * B) continuousOn_const
    (fun r _ => mul_nonneg hK0 hB0) (fun r hr => hFW' r hr)
  obtain ⟨hGc2, -, hGd2⟩ := hreg σ hσ
  obtain ⟨hfc2, -, -, -, -, -, -, -, hfder⟩ := freePart c ν s T f hc hν hsT hf
  have hGt := convTimeDeriv ν s T hν hsT (K * B) (transp v u) hFR hFW' σ hσ x
  have hEq : ∀ r ∈ Icc s T, u r x = heatSG (ν * (r - s)) f x -
      duhamelConv ν s (transp v u) r x :=
    fun r hr => hu.duhamel r hr x
  have hD := (hfder σ hσ x).sub hGt
  have hcong : HasDerivWithinAt (fun r => u r x)
      (ν * lapP (heatSG (ν * (σ - s)) f) x -
        (transp v u σ x + ν * ∑ i : Fin 2,
          ∫ r in s..σ, heatSGd i (ν * (σ - r)) (B0579.pd i (transp v u r)) x))
      (Icc s T) σ :=
    hD.congr (fun r hr => hEq r hr) (hEq σ hσ)
  have hfun : u σ = fun y => heatSG (ν * (σ - s)) f y -
      duhamelConv ν s (transp v u) σ y :=
    funext fun y => hu.duhamel σ hσ y
  have hlap : lapP (u σ) x = lapP (heatSG (ν * (σ - s)) f) x -
      lapP (duhamelConv ν s (transp v u) σ) x := by
    rw [hfun]
    exact duhamelToPde_lapP_sub (hfc2 σ hσ) hGc2 x
  have hlapG : lapP (duhamelConv ν s (transp v u) σ) x =
      ∑ i : Fin 2, ∫ r in s..σ, heatSGd i (ν * (σ - r)) (B0579.pd i (transp v u r)) x := by
    unfold lapP
    rw [hGd2 0 0 x, hGd2 1 1 x, Fin.sum_univ_two]
  have hval : ν * lapP (heatSG (ν * (σ - s)) f) x -
      (transp v u σ x + ν * ∑ i : Fin 2,
        ∫ r in s..σ, heatSGd i (ν * (σ - r)) (B0579.pd i (transp v u r)) x) =
      ν * lapP (u σ) x - (v σ x 0 * B0579.pd 0 (u σ) x + v σ x 1 * B0579.pd 1 (u σ) x) := by
    rw [hlap, hlapG]
    unfold transp
    ring
  exact hcong.congr_deriv hval

end UnforcedLeray.Short.IIb.CylPDE

end
