import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_5

/-!
# Part II-b, leaf `PartII-b:T11/2/2/5/1` (bridge `DualPerpBridge`)

For `x.1 < s` the point `(s - x.1, x.2)` lies in `Ioi 0 ×ˢ univ`, where `H` is smooth
(`HeatSol.smooth`).  The chain rule gives the `q`- and `η`-partials of `H(s - ·, ·)`
as partials of `H` at `(s - x.1, x.2)` in the directions `(0, (0,1))` and `(0, (1,0))`,
which are the partials of `p ↦ H(s - x.1, p)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dualPerpBridge_proof : UnforcedLeray.Short.IIb.DualPerpBridge := by
  intro c ν r' H s hc hν hHeat x i hx
  have hpos : s - x.1 ∈ Ioi (0 : ℝ) := by
    simp only [mem_Ioi]; linarith
  have hq : (s - x.1, x.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    mk_mem_prod hpos (mem_univ _)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    isOpen_Ioi.prod isOpen_univ
  have hdiffH : DifferentiableAt ℝ H (s - x.1, x.2) :=
    (hHeat.smooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hHd : HasFDerivAt H (fderiv ℝ H (s - x.1, x.2)) (s - x.1, x.2) :=
    hdiffH.hasFDerivAt
  -- the affine change of variables `z ↦ (s - z.1, z.2)`
  have hφ : HasFDerivAt (fun z : Coord => (s - z.1, z.2))
      ((-ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    HasFDerivAt.prodMk (hasFDerivAt_fst.const_sub s) hasFDerivAt_snd
  have hg : HasFDerivAt (fun z : Coord => H (s - z.1, z.2))
      ((fderiv ℝ H (s - x.1, x.2)).comp
        ((-ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) x :=
    HasFDerivAt.comp x hHd hφ
  have hψ : HasFDerivAt (fun z : Coord => ((H (s - z.1, z.2) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ H (s - x.1, x.2)).comp
        ((-ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hg
  have key1 : ∀ v : Coord, fderiv ℝ (fun z : Coord => ((H (s - z.1, z.2) : ℝ) : ℂ)) x v =
      ((fderiv ℝ H (s - x.1, x.2) (-v.1, v.2) : ℝ) : ℂ) := by
    intro v
    rw [hψ.fderiv]
    simp
  -- the `(q, η)`-slice `p ↦ H(s - x.1, p)`
  have hζ : HasFDerivAt (fun p : ℝ × ℝ => H (s - x.1, p))
      ((fderiv ℝ H (s - x.1, x.2)).comp
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x.2 :=
    HasFDerivAt.comp x.2 hHd ((hasFDerivAt_const (s - x.1) x.2).prodMk (hasFDerivAt_id x.2))
  have key2 : ∀ w : ℝ × ℝ, fderiv ℝ (fun p : ℝ × ℝ => H (s - x.1, p)) x.2 w =
      fderiv ℝ H (s - x.1, x.2) (0, w) := by
    intro w
    rw [hζ.fderiv]
    simp
  fin_cases i
  · simp [perpC, perpGrad, cpdC, cdir, key1, key2]
  · simp [perpC, perpGrad, cpdC, cdir, key1, key2]

end UnforcedLeray.Short.IIb
