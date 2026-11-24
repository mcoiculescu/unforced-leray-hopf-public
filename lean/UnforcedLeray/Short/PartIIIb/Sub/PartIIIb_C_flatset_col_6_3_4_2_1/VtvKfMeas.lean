import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/1/2` (`vtvKfMeas`): joint measurability of the `f`-kernel

Source of record: `the November 2 reference manuscript` (line 4610).
`f` is `L²` on every band `[s₁,s₂] × cell` (clause 6 of `VtvHyps`), so it is a.e. strongly
measurable on `(0,∞) × cell` (countable union of bands); the composition with the quasi
measure preserving projection `((s,r),x) ↦ (r,x)` gives the `f`-factor, and the `x`-derivatives of
the age derivative `∂_sη` are jointly continuous (joint smoothness of `η`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The age-derivative of the uncurried stream test as a function of `(s, x)`. -/
def vtvKf_K (η : ℝ → ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) p ((1 : ℝ), (0 : ℝ × ℝ))

theorem vtvKf_K_contDiff (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) :
    ContDiff ℝ ∞ (vtvKf_K η) :=
  (contDiff_infty_iff_fderiv.1 hsm).2.clm_apply contDiff_const

theorem vtvKf_deriv_eq (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (s : ℝ) (x : ℝ × ℝ) :
    deriv (fun s' => η s' x) s = vtvKf_K η (s, x) := by
  have hGdiff : Differentiable ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) :=
    hsm.differentiable (by simp)
  have hG : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x)) (s, x) :=
    (hGdiff (s, x)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  have hcomp := hG.comp_hasDerivAt s hline
  exact hcomp.deriv

theorem vtvKf_pd_eq (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (s : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    B0579.pd j (fun y => deriv (fun s' => η s' y) s) x =
      fderiv ℝ (vtvKf_K η) (s, x) ((0 : ℝ), B0579.dir j) := by
  have hfun : (fun y : ℝ × ℝ => deriv (fun s' => η s' y) s) =
      fun y => vtvKf_K η (s, y) :=
    funext fun y => vtvKf_deriv_eq η hsm s y
  rw [hfun]
  have hKd : DifferentiableAt ℝ (vtvKf_K η) (s, x) :=
    ((vtvKf_K_contDiff η hsm).differentiable (by simp)) (s, x)
  have hd : HasFDerivAt (fun y : ℝ × ℝ => vtvKf_K η (s, y))
      ((fderiv ℝ (vtvKf_K η) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
    hKd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  unfold B0579.pd
  rw [hd.fderiv]
  rfl

theorem vtvKf_pd_cont (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (j : Fin 2) :
    Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      B0579.pd j (fun x => deriv (fun s' => η s' x) q.1.1) q.2) := by
  have hfe : (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      B0579.pd j (fun x => deriv (fun s' => η s' x) q.1.1) q.2) =
      fun q => fderiv ℝ (vtvKf_K η) (q.1.1, q.2) ((0 : ℝ), B0579.dir j) :=
    funext fun q => vtvKf_pd_eq η hsm q.1.1 q.2 j
  rw [hfe]
  have hc : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => fderiv ℝ (vtvKf_K η) (q.1.1, q.2)) :=
    (contDiff_infty_iff_fderiv.1 (vtvKf_K_contDiff η hsm)).2.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact hc.clm_apply continuous_const

theorem vtvKf_cover (c : ℝ) :
    Ioi (0 : ℝ) ×ˢ B0579.cell c = ⋃ N : ℕ, Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) ×ˢ B0579.cell c := by
  ext ⟨s, x⟩
  simp only [mem_prod, mem_iUnion, mem_Ioi, mem_Icc]
  constructor
  · rintro ⟨hs, hx⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (max s (1 / s))
    have h1s : 1 / s < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    have h2 : 1 < (N : ℝ) * s := by rwa [div_lt_iff₀ hs] at h1s
    have h3 : s < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    refine ⟨N, ⟨?_, ?_⟩, hx⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
    · linarith
  · rintro ⟨N, ⟨h1, _⟩, hx⟩
    exact ⟨lt_of_lt_of_le (by positivity) h1, hx⟩

theorem vtvKfMeas : VtvKfMeas := by
  intro ν c μ tr om g b G f H η hη
  have hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) := hη.1
  have hfi : ∀ i : Fin 2, AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => f p i)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
    intro i
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, vtvKf_cover c, aestronglyMeasurable_iUnion_iff]
    intro N
    have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    exact (H.2.2.2.2.2.1 (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) hpos i).aestronglyMeasurable
  have hQ : Measure.QuasiMeasurePreserving (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1.2, q.2))
      (((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
        (volume.restrict (B0579.cell c)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioi (0 : ℝ)))
        (ν := volume.restrict (Ioi (0 : ℝ))))
      (Measure.QuasiMeasurePreserving.id (volume.restrict (B0579.cell c)))
  have hA : ∀ i : Fin 2, AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => f (q.1.2, q.2) i)
      (((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
        (volume.restrict (B0579.cell c))) :=
    fun i => (hfi i).comp_quasiMeasurePreserving hQ
  have hH0 : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((B0579.pd 0 (fun x => deriv (fun s' => η s' x) q.1.1) q.2 : ℝ) : ℂ))
      (((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
        (volume.restrict (B0579.cell c))) :=
    (Complex.continuous_ofReal.comp (vtvKf_pd_cont η hsm 0)).aestronglyMeasurable
  have hH1 : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((B0579.pd 1 (fun x => deriv (fun s' => η s' x) q.1.1) q.2 : ℝ) : ℂ))
      (((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
        (volume.restrict (B0579.cell c))) :=
    (Complex.continuous_ofReal.comp (vtvKf_pd_cont η hsm 1)).aestronglyMeasurable
  exact ((hA 0).mul hH1).sub ((hA 1).mul hH0)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
