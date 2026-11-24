import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellMollifiedDerivative

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.Sob
open UnforcedLeray.B0448

/-- At each fixed interior phase cutoff, the actual spatial derivative of the nested cutoff
mollifications converges in the cell dual norm to the derivative of the squared cutoff product. -/
theorem tendsto_nestedCutoff_spatialDerivative_cellLp
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (n : ℕ) (j : Fin 3) (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    Tendsto (fun k => eLpNorm
      (fun z : SpaceTime =>
        PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z -
          (phaseInteriorCutoff P n z.1) ^ 2 •
            fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
              (EuclideanSpace.single j (1 : ℝ))) p
      (volume.restrict (phaseCell P))) atTop (𝓝 0) := by
  let χ : ℝ → ℝ := phaseInteriorCutoff P n
  let g : SpaceTime → ℂ := fun z =>
    fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
      (EuclideanSpace.single j (1 : ℝ))
  let G : SpaceTime → ℂ := fun z => phaseCutoffSpaceTime χ z • g z
  let GH : ST → ℂ := G ∘ spacetimeHilbertEquiv.symm
  have hcell : MemLp g p (volume.restrict (phaseCell P)) :=
    scalarTestBackground_spatialDerivative_memLp_cell hΦ hU hp j
  have hG : MemLp G p volume := by
    change MemLp (fun z : SpaceTime => phaseCutoffSpaceTime χ z • g z) p volume
    simpa [χ, g, phaseCutoffSpaceTime] using
      (memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hcell n)
  have hGH : MemLp GH p volume := memLp_spacetimeHilbertPullback hG
  have hconv : Tendsto (fun k : ℕ => eLpNorm
      (moll (spacetimeShrinkBump k) volume GH - GH) p volume)
      atTop (𝓝 0) := tendsto_spacetimeMollification hp hGH
  have hMcd : ∀ k, ContDiff ℝ ∞ (mollifiedPhaseCutoffScalarProduct P n k Φ U) := by
    intro k
    have h2 : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    letI := h2
    have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hbase := scalarTestBackground_memLp_cell (p := 2) hΦ hU h2top
    have hcut : MemLp (phaseCutoffScalarProduct P n Φ U) 2 volume := by
      change MemLp (fun z : SpaceTime => phaseCutoffSpaceTime
        (phaseInteriorCutoff P n) z • scalarTestBackground Φ U z) 2 volume
      simpa [phaseCutoffSpaceTime] using
        (memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hbase n)
    exact (contDiff_spacetimeMollification (memLp_spacetimeHilbertPullback hcut) k).comp
      spacetimeHilbertEquiv.contDiff
  have hdy (k : ℕ) (z : SpaceTime) :
      PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z =
        phaseCutoffSpaceTime χ z •
          (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) := by
    obtain ⟨hNcd, _, _, _⟩ := nestedCutoffMollification_isCompactInteriorTest hΦ hU hn
    have hs := fderiv_scalarSlice_eq_spatial (hNcd.differentiable (by simp)) z.1 z.2
      (coordinateVector j)
    have hfun : (fun x : Space => nestedCutoffMollification P n k Φ U (z.1, x)) =
        (fun x : Space => χ z.1 • mollifiedPhaseCutoffScalarProduct P n k Φ U
          (z.1, x)) := by
      funext x
      simp [nestedCutoffMollification, phaseCutoffSpaceTime, χ]
    rw [hfun] at hs
    have hMdiffAt : DifferentiableAt ℝ
        (mollifiedPhaseCutoffScalarProduct P n k Φ U) (z.1, z.2) :=
      (hMcd k).differentiable (by simp) (z.1, z.2)
    have hmap : DifferentiableAt ℝ (fun x : Space => (z.1, x)) z.2 :=
      ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)).differentiableAt
    have hMslice : DifferentiableAt ℝ
        (fun x : Space => mollifiedPhaseCutoffScalarProduct P n k Φ U (z.1, x)) z.2 :=
      hMdiffAt.comp z.2 hmap
    rw [fderiv_fun_const_smul hMslice (χ z.1)] at hs
    have he : coordinateVector j = EuclideanSpace.single j (1 : ℝ) := by
      ext i
      simp [coordinateVector]
    rw [he, ContinuousLinearMap.smul_apply] at hs
    rw [spatialDerivative_mollifiedPhaseCutoffScalarProduct hΦ hU n k j z.1 z.2] at hs
    simpa [PhaseSpace.dy, G, GH, χ, phaseCutoffSpaceTime, g, he] using hs.symm
  have hpoint (k : ℕ) : ∀ᵐ z ∂(volume.restrict (phaseCell P)),
      ‖(fun z : SpaceTime =>
          PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z -
            (phaseInteriorCutoff P n z.1) ^ 2 • g z) z‖ ≤
        ‖((moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)‖ := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    have hχ0 := phaseInteriorCutoff_nonneg (P := P) n z.1
    have hχ1 := phaseInteriorCutoff_le_one (P := P) n z.1
    rw [hdy k z]
    have hreal : phaseCutoffSpaceTime χ z = phaseInteriorCutoff P n z.1 := rfl
    rw [hreal]
    have halg : phaseInteriorCutoff P n z.1 •
        (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) -
          (phaseInteriorCutoff P n z.1) ^ 2 • g z =
        phaseInteriorCutoff P n z.1 •
          ((moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z) := by
      simp [G, phaseCutoffSpaceTime, χ, smul_sub, pow_two]
      ring
    rw [halg]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hχ1
  have hcellbound (k : ℕ) :
      eLpNorm (fun z : SpaceTime =>
        PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z -
          (phaseInteriorCutoff P n z.1) ^ 2 • g z) p
        (volume.restrict (phaseCell P)) ≤
      eLpNorm (fun z : SpaceTime =>
        (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)
        p (volume.restrict (phaseCell P)) := eLpNorm_mono_ae (hpoint k)
  have hnormeq (k : ℕ) :
      eLpNorm (fun z : SpaceTime =>
        (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)
        p volume = eLpNorm (moll (spacetimeShrinkBump k) volume GH - GH) p volume := by
    have hmeas : AEStronglyMeasurable
        (fun x : ST => moll (spacetimeShrinkBump k) volume GH x - GH x) volume := by
      have hcont := contDiff_spacetimeMollification hGH k
      exact hcont.continuous.aestronglyMeasurable.sub hGH.aestronglyMeasurable
    have h := eLpNorm_comp_measurePreserving (p := p) hmeas measurePreserving_ofLp.symm
    exact h
  have hfull : Tendsto (fun k : ℕ => eLpNorm
      (fun z : SpaceTime =>
        (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)
      p volume) atTop (𝓝 0) := by
    exact hconv.congr (fun k => (hnormeq k).symm)
  have hcellmono (k : ℕ) : eLpNorm
      (fun z : SpaceTime =>
        (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)
      p (volume.restrict (phaseCell P)) ≤ eLpNorm
        (fun z : SpaceTime =>
          (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)
        p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
  have hcellconv : Tendsto (fun k : ℕ => eLpNorm
      (fun z : SpaceTime =>
        (moll (spacetimeShrinkBump k) volume GH) (spacetimeHilbertEquiv z) - G z)
      p (volume.restrict (phaseCell P))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfull
      (fun k => bot_le) hcellmono
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcellconv
    (fun k => bot_le) hcellbound

#print axioms tendsto_nestedCutoff_spatialDerivative_cellLp

end UnforcedLeray.Cons.C03.Concrete
