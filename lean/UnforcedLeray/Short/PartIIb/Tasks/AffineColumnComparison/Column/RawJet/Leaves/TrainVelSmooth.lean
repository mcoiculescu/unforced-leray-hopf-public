import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/1/1`: joint smoothness of the train velocity

Source of record: `the November 2 reference manuscript` (SP) 261-291 (the stream
relation `v = ∇^⊥ψ`), 397 (`BgRegime.train_stream_smooth`).

Proof. On `U = (0,∞) × ℝ²` the stream `Ψ(s,z) = ψ(s,z)` is `C^∞` (`BgRegime.train_stream_smooth`).
Its fibre partial derivatives `∂_q ψ, ∂_η ψ` at `s > 0` are the Fréchet derivative of `Ψ` in the
fixed directions `(0,(1,0))`, `(0,(0,1))`, and these are `C^∞` on `U`. The velocity is
`v(s,z) = toVec (-∂_η ψ, ∂_q ψ)` for `s ≥ 0` (`IsTrain.stream`), a linear image of a `C^∞` pair.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.GaussianVortex (perpendicularGradient partialX partialY)

/-- A fixed-direction Fréchet derivative of a `C^∞` function on `(0,∞) × ℝ²` is `C^∞` there. -/
lemma trainVel_fderiv_dir_contDiffOn {Ψ : ℝ × (ℝ × ℝ) → ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)))) (e : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ x (0, e))
      (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hD : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Ψ x) (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) :=
    hΨ.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (by simp)
  exact hD.clm_apply contDiffOn_const

/-- The `q`-partial derivative of the slice `ψ s` is the Fréchet derivative in direction `(0,(1,0))`. -/
lemma trainVel_partialX_eq {ψ : ℝ → ℝ × ℝ → ℝ}
    (hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))))
    {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    partialX (ψ s) z = fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, z) (0, (1, 0)) := by
  obtain ⟨q, η⟩ := z
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (q, η)) :=
    (hΨ.differentiableOn (by simp)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  have hγ : HasDerivAt (fun x : ℝ => (s, (x, η))) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) q :=
    (hasDerivAt_const q s).prodMk ((hasDerivAt_id' q).prodMk (hasDerivAt_const q η))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt q hγ
  unfold partialX
  exact h.deriv

/-- The `η`-partial derivative of the slice `ψ s` is the Fréchet derivative in direction `(0,(0,1))`. -/
lemma trainVel_partialY_eq {ψ : ℝ → ℝ × ℝ → ℝ}
    (hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))))
    {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    partialY (ψ s) z = fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, z) (0, (0, 1)) := by
  obtain ⟨q, η⟩ := z
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (q, η)) :=
    (hΨ.differentiableOn (by simp)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  have hγ : HasDerivAt (fun y : ℝ => (s, (q, y))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
    (hasDerivAt_const η s).prodMk ((hasDerivAt_const η q).prodMk (hasDerivAt_id' η))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt η hγ
  unfold partialY
  exact h.deriv

/-- **Joint smoothness of the train velocity** (`TrainVelSmooth`, SP 261-291, 397). -/
theorem trainVelSmooth_core : UnforcedLeray.Short.IIb.TrainVelSmooth := by
  intro p d dm dp hBG
  have hΨ := hBG.train_stream_smooth
  have hpair : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) =>
        ((-(fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) x (0, (0, 1)))),
          fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) x (0, (1, 0))))
      (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) :=
    (trainVel_fderiv_dir_contDiffOn hΨ (0, 1)).neg.prodMk (trainVel_fderiv_dir_contDiffOn hΨ (1, 0))
  refine ((UnforcedLeray.Train.toVecL.toContinuousLinearMap.contDiff).comp_contDiffOn hpair).congr ?_
  rintro ⟨s, z⟩ hx
  have hs : 0 < s := hx.1
  show p.train.v s z = UnforcedLeray.Train.toVec _
  rw [p.train.isTrain.stream s hs.le z]
  unfold perpendicularGradient
  rw [trainVel_partialY_eq hΨ hs z, trainVel_partialX_eq hΨ hs z]

end UnforcedLeray.Short.IIb

/-- The target: joint smoothness of the train velocity, stated at the root namespace. -/
theorem trainVelSmooth_proof : UnforcedLeray.Short.IIb.TrainVelSmooth :=
  UnforcedLeray.Short.IIb.trainVelSmooth_core
