import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_smooth_6

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Shift, joint continuity** (decomposition leaf for `ShiftJointCont`). -/
theorem shiftJointCont : ShiftJointCont := by
  intro ρ hρ n
  have hWo : IsOpen (univ ×ˢ (Ioi (0 : ℝ) ×ˢ univ) : Set (ℝ × (ℝ × (ℝ × ℝ)))) :=
    isOpen_univ.prod (isOpen_Ioi.prod isOpen_univ)
  have hL : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (z.2.1, z.1)) := by fun_prop
  have hmaps : MapsTo (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (z.2.1, z.1))
      (univ ×ˢ (Ioi (0 : ℝ) ×ˢ univ)) (Ioi (0 : ℝ) ×ˢ univ) := by
    intro z hz
    exact ⟨hz.2.1, mem_univ _⟩
  have hPs : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1))
      (univ ×ˢ (Ioi (0 : ℝ) ×ˢ univ)) :=
    hρ.comp hL.contDiffOn hmaps
  have hPc : ContinuousOn (fun z : ℝ × (ℝ × (ℝ × ℝ)) =>
      iteratedFDeriv ℝ n (fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) z)
      (univ ×ˢ (Ioi (0 : ℝ) ×ˢ univ)) := by
    refine ContinuousOn.congr ?_ (fun z hz => (iteratedFDerivWithin_of_isOpen n hWo hz).symm)
    exact hPs.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hWo.uniqueDiffOn
  let hC : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (ℝ × (ℝ × ℝ))) ℂ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (ℝ × ℝ)) ℂ :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)))
  have hCapp : ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (ℝ × (ℝ × ℝ))) ℂ,
      hC M = M.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) :=
    fun M => rfl
  have hLm : Continuous (⇑hC) := hC.continuous
  have hslice : ∀ (τ : ℝ) (y : ℝ × (ℝ × ℝ)), 0 < y.1 →
      iteratedFDeriv ℝ n (fun y' : ℝ × (ℝ × ℝ) => ρ (y'.1, τ)) y =
        (iteratedFDeriv ℝ n (fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) (τ, y)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) := by
    intro τ y hy
    have hSfo : IsOpen {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1} :=
      isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
    have hfc : ContDiffOn ℝ ∞
        ((fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) ∘
          (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (τ, (0 : ℝ × (ℝ × ℝ))) + z))
        {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1} := by
      refine hPs.comp (contDiff_const.add contDiff_id).contDiffOn ?_
      intro z hz
      exact ⟨mem_univ _, by simpa using hz, mem_univ _⟩
    have hadd : (τ, (0 : ℝ × (ℝ × ℝ))) + ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) y = (τ, y) := by
      simp
    have hcompadd : iteratedFDeriv ℝ n
        ((fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) ∘
          (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (τ, (0 : ℝ × (ℝ × ℝ))) + z))
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) y) =
        iteratedFDeriv ℝ n (fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) (τ, y) := by
      have key := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) n (τ, (0 : ℝ × (ℝ × ℝ)))
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) y)
      rw [hadd] at key
      exact key
    have hVo : IsOpen (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) ⁻¹'
        {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1}) :=
      hSfo.preimage (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))).continuous
    have hyV : y ∈ ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) ⁻¹'
        {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1} := by
      show 0 < (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) y).2.1
      simpa using hy
    have hxS : ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) y ∈
        {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1} := hyV
    have hcomp : (fun y' : ℝ × (ℝ × ℝ) => ρ (y'.1, τ)) =
        ((fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) ∘
          (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (τ, (0 : ℝ × (ℝ × ℝ))) + z)) ∘
          ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) := by
      funext y'
      simp
    calc iteratedFDeriv ℝ n (fun y' : ℝ × (ℝ × ℝ) => ρ (y'.1, τ)) y
        = iteratedFDeriv ℝ n
            (((fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) ∘
              (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (τ, (0 : ℝ × (ℝ × ℝ))) + z)) ∘
              ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) y := by
          rw [hcomp]
      _ = iteratedFDerivWithin ℝ n
            (((fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) ∘
              (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (τ, (0 : ℝ × (ℝ × ℝ))) + z)) ∘
              ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)))
            (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) ⁻¹' {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1}) y :=
          (iteratedFDerivWithin_of_isOpen n hVo hyV).symm
      _ = (iteratedFDerivWithin ℝ n
            ((fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) ∘
              (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (τ, (0 : ℝ × (ℝ × ℝ))) + z))
            {z : ℝ × (ℝ × (ℝ × ℝ)) | 0 < z.2.1}
            (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)) y)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) :=
          ContinuousLinearMap.iteratedFDerivWithin_comp_right _ hfc hSfo.uniqueDiffOn
            hVo.uniqueDiffOn hxS (by exact_mod_cast le_top)
      _ = (iteratedFDeriv ℝ n (fun z : ℝ × (ℝ × (ℝ × ℝ)) => ρ (z.2.1, z.1)) (τ, y)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) := by
          rw [iteratedFDerivWithin_of_isOpen n hSfo hxS, hcompadd]
  refine (hLm.comp_continuousOn hPc).congr (fun q hq => ?_)
  rw [hslice q.1 q.2 hq.2.1, Function.comp_apply, hCapp]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
