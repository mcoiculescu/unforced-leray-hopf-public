import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs

/-!
# The mean velocity is the transverse derivative of the mean stream (source 397-404, `sct:mean`)

`PartI.TrainMeanEquations` gives `hmean c (tr.v s · 0) η = -∂_η S(s, η)` and
`hmean c (tr.v s · 1) η = 0`, so the horizontal mean velocity `\bar v(s, η)` has norm
`|∂_η S(s, η)|` (`MeanVelNorm`, `Defs.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- The horizontal mean commutes with a coordinate functional (copy of
`PartII-a` `fvs_hmean_apply`). -/
theorem meanVel_hmean_apply (c : ℝ) (a : ℝ × ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Continuous a) (η : ℝ) (j : Fin 2) :
    (UnforcedLeray.Short.PartI.hmean c a η) j =
      UnforcedLeray.Short.PartI.hmean c (fun z => a z j) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).integral_comp_comm hint
  unfold UnforcedLeray.Short.PartI.hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

/-- **The mean velocity norm** (source 397-404, `sct:mean`: `\bar v₁ = -S_η`, `\bar v₂ = 0`). -/
theorem meanVelNorm_of (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) :
    MeanVelNorm := by
  intro ν c hν hc tr hbuc s hs η
  obtain ⟨-, hE2⟩ := hE ν c hν hc tr hbuc
  obtain ⟨-, h0, h1⟩ := hE2 s hs η
  have hcont : Continuous (fun z : ℝ × ℝ => tr.v s z) := by
    have h : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici (0 : ℝ) ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hc' : Continuous (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) :=
      continuous_const.prodMk continuous_id
    exact h.comp_continuous hc' (fun z => mk_mem_prod (mem_Ici.mpr hs.le) (mem_univ _))
  have e0 := meanVel_hmean_apply c (tr.v s) hcont η 0
  have e1 := meanVel_hmean_apply c (tr.v s) hcont η 1
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1, h0, h1]
  simp [Real.sqrt_sq_eq_abs]

end UnforcedLeray.Short.PartIIIb.NearInst
