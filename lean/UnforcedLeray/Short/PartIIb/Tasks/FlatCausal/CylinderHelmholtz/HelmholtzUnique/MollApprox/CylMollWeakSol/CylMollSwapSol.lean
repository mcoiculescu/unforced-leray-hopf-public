import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv.Int1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv.Int2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylMollWeakDiv.CylMollSwapDiv.MollComp

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
Same Fubini + cell-shift argument as `CylMollSwapDiv`, with the weights `g_i = Ψ_i` (components of
a `CylSolTest`) in place of `∂_q φ`, `∂_η φ`. Each `Ψ_i` is a `CylTest`, hence a `SwapGood` weight.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A `CylTest` is a `SwapGood` weight. -/
theorem swapGood_of_cylTest {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) : SwapGood c φ := by
  refine ⟨?_, ?_, ?_⟩
  · exact hφ.smooth.continuous
  · intro w
    exact hφ.periodic w
  · exact hφ.bounded

/-- The Fubini and cell-shift core of the swap identity, for two arbitrary `SwapGood` weights.
This is the proof of `cylMollSwapDiv_of`, with `g0`, `g1` as variables. -/
theorem cylSolSwapCore (h1 : CylSwapInt1) (h2 : CylSwapInt2) (h3 : CylMollComp)
    {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (D : ℝ × ℝ → CMerid) (hD : CylLp c r D)
    (ρ : ContDiffBump (0 : ℝ × ℝ)) (g0 g1 : ℝ × ℝ → ℝ) (G0 : SwapGood c g0) (G1 : SwapGood c g1) :
    ∫ z, (cylMoll ρ D z 0 * ((g0 z : ℝ) : ℂ) + cylMoll ρ D z 1 * ((g1 z : ℝ) : ℂ))
        ∂(UnforcedLeray.Cyl.avgμ c) =
      ∫ u, (D u 0 * ((∫ y, ρ.normed volume y * g0 (u + y) : ℝ) : ℂ) +
          D u 1 * ((∫ y, ρ.normed volume y * g1 (u + y) : ℝ) : ℂ))
        ∂(UnforcedLeray.Cyl.avgμ c) := by
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  have hper : UnforcedLeray.Cyl.IsPeriodic c D := hD.1
  -- integrability of the `z`-integrands
  have L0 : Integrable
      (fun z => (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 0) * ((g0 z : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h1 c r hc hr D hD ρ g0 G0 0).integral_prod_left
    refine this.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    exact integral_mul_const _ _
  have L1 : Integrable
      (fun z => (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 1) * ((g1 z : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h1 c r hc hr D hD ρ g1 G1 1).integral_prod_left
    refine this.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    exact integral_mul_const _ _
  have R0 : Integrable (fun u => D u 0 * ((∫ y, ρ.normed volume y * g0 (u + y) : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h2 c r hc hr D hD ρ g0 G0 0).integral_prod_left
    refine this.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    have h : ((∫ y, ρ.normed volume y * g0 (u + y) : ℝ) : ℂ)
        = ∫ y, ((ρ.normed volume y * g0 (u + y) : ℝ) : ℂ) := integral_ofReal.symm
    rw [h, ← integral_const_mul]
  have R1 : Integrable (fun u => D u 1 * ((∫ y, ρ.normed volume y * g1 (u + y) : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h2 c r hc hr D hD ρ g1 G1 1).integral_prod_left
    refine this.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    have h : ((∫ y, ρ.normed volume y * g1 (u + y) : ℝ) : ℂ)
        = ∫ y, ((ρ.normed volume y * g1 (u + y) : ℝ) : ℂ) := integral_ofReal.symm
    rw [h, ← integral_const_mul]
  have e0 := Swap.swap_component hc D hper 0 ρ g0 G0.2.1 (h1 c r hc hr D hD ρ g0 G0 0)
    (h2 c r hc hr D hD ρ g0 G0 0)
  have e1 := Swap.swap_component hc D hper 1 ρ g1 G1.2.1 (h1 c r hc hr D hD ρ g1 G1 1)
    (h2 c r hc hr D hD ρ g1 G1 1)
  have hL : (fun z => cylMoll ρ D z 0 * ((g0 z : ℝ) : ℂ)
        + cylMoll ρ D z 1 * ((g1 z : ℝ) : ℂ))
      = fun z => (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 0) * ((g0 z : ℝ) : ℂ)
        + (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 1) * ((g1 z : ℝ) : ℂ) := by
    funext z
    rw [h3 c r hc hr D hD ρ z 0, h3 c r hc hr D hD ρ z 1]
  rw [hL, integral_add L0 L1, integral_add R0 R1, e0, e1]

theorem cylMollSwapSol : UnforcedLeray.Short.IIb.CylMollSwapSol := by
  intro c r hc hr D hD ρ Ψ hΨ
  have G0 : SwapGood c (fun z => Ψ z 0) := swapGood_of_cylTest (hΨ.comp 0)
  have G1 : SwapGood c (fun z => Ψ z 1) := swapGood_of_cylTest (hΨ.comp 1)
  have key := cylSolSwapCore CylSwapInt1Proof.cylSwapInt1 CylSwapInt2Proof.cylSwapInt2 cylMollComp
    hc hr D hD ρ (fun z => Ψ z 0) (fun z => Ψ z 1) G0 G1
  simp only [Fin.sum_univ_two]
  exact key

end UnforcedLeray.Short.IIb
