import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/1/2`: chart bridge for the train velocity

Source of record: `the November 2 reference manuscript` (SP) 2419-2423.

`Axi.dS/dQ/dEta` of the chart function `trainProf p = v` are fderivatives of `(s,z) ↦ v s z` in
the unit directions `(1,0,0)`, `(0,1,0)`, `(0,0,1)`.  At `s > 0` the function is `C^∞` by
`TrainVelSmooth`, so the age derivative is `deriv (fun r => v r z) s` (`ageJet 1 0`, a norm-preserving
`iteratedDeriv`), and the spatial derivatives are fderivatives of the slice `w ↦ v s w`
(`ageJet 0 1`, `norm_iteratedFDeriv_one`) evaluated at unit vectors of `ℝ × ℝ` (sup norm, norm `1`).
The value bound is `norm_iteratedFDeriv_zero`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartI

/-- Age derivative: `‖Axi.dS F (s,z)‖ = ‖∂_s v‖` for the chart function `F (s,z) = v s z`. -/
lemma trainBridge_dS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → UnforcedLeray.Cyl.Plane → E)
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => v x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (z : UnforcedLeray.Cyl.Plane) :
    ‖Axi.dS (fun x : Coord => v x.1 x.2) (s, z)‖ ≤ ‖ageJet 1 0 v s z‖ := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Cyl.Plane => v x.1 x.2) (s, z) :=
    (hv.differentiableOn (by simp)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (s, z) ∈ Ioi 0 ×ˢ univ from ⟨hs, trivial⟩))
  have hγ : HasDerivAt (fun r : ℝ => ((r, z) : ℝ × UnforcedLeray.Cyl.Plane))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s z)
  have h := HasFDerivAt.comp_hasDerivAt s hdiff.hasFDerivAt hγ
  have h' : HasDerivAt (fun r : ℝ => v r z) (Axi.dS (fun x : Coord => v x.1 x.2) (s, z)) s := by
    unfold Axi.dS
    exact h
  have hA : ‖ageJet 1 0 v s z‖ = ‖deriv (fun r : ℝ => v r z) s‖ := by
    simp only [PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_zero, iteratedDeriv_one]
  rw [h'.deriv] at hA
  exact hA.symm.le

/-- Spatial derivatives: `‖fderiv F (s,z) (0,e)‖ ≤ ‖∂_q^{…} v‖` for a unit direction `e` of the
spatial plane, where `ageJet 0 1 v s z` is the spatial derivative of the slice `w ↦ v s w`. -/
lemma trainBridge_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → UnforcedLeray.Cyl.Plane → E)
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => v x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (z e : UnforcedLeray.Cyl.Plane) (he : ‖e‖ ≤ 1) :
    ‖fderiv ℝ (fun x : Coord => v x.1 x.2) (s, z) (0, e)‖ ≤ ‖ageJet 0 1 v s z‖ := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Cyl.Plane => v x.1 x.2) (s, z) :=
    (hv.differentiableOn (by simp)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (s, z) ∈ Ioi 0 ×ˢ univ from ⟨hs, trivial⟩))
  have hG : HasFDerivAt (fun w : UnforcedLeray.Cyl.Plane => v s w)
      ((fderiv ℝ (fun x : Coord => v x.1 x.2) (s, z)).comp
        ((0 : UnforcedLeray.Cyl.Plane →L[ℝ] ℝ).prod
          (ContinuousLinearMap.id ℝ UnforcedLeray.Cyl.Plane))) z :=
    hdiff.hasFDerivAt.comp z ((hasFDerivAt_const s z).prodMk (hasFDerivAt_id z))
  have hq : fderiv ℝ (fun w : UnforcedLeray.Cyl.Plane => v s w) z e =
      fderiv ℝ (fun x : Coord => v x.1 x.2) (s, z) (0, e) := by
    rw [hG.fderiv]
    simp
  have hAge : ‖ageJet 0 1 v s z‖ = ‖fderiv ℝ (fun w : UnforcedLeray.Cyl.Plane => v s w) z‖ := by
    simp only [PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero, norm_iteratedFDeriv_one]
  have h1 := (fderiv ℝ (fun w : UnforcedLeray.Cyl.Plane => v s w) z).le_opNorm e
  rw [hq] at h1
  rw [hAge]
  exact h1.trans (mul_le_of_le_one_right (norm_nonneg _) he)

/-- **Chart bridge for the velocity** (`TrainChartBridge`, SP 2419-2423). -/
theorem trainChartBridge_of (hS : UnforcedLeray.Short.IIb.TrainVelSmooth) :
    UnforcedLeray.Short.IIb.TrainChartBridge := by
  intro p d dm dp hBG x hx
  have hv := hS p d dm dp hBG
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ‖p.train.v x.1 x.2‖ ≤ ‖ageJet 0 0 p.train.v x.1 x.2‖
    have h0 : ‖ageJet 0 0 p.train.v x.1 x.2‖ = ‖p.train.v x.1 x.2‖ := by
      simp only [PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero, norm_iteratedFDeriv_zero]
    exact h0.ge
  · exact trainBridge_dS p.train.v hv hx x.2
  · exact trainBridge_dir p.train.v hv hx x.2 (1, 0) (by simp [Prod.norm_def])
  · exact trainBridge_dir p.train.v hv hx x.2 (0, 1) (by simp [Prod.norm_def])

end UnforcedLeray.Short.IIb
