import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceBounds
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntFderivFormula.Helpers

/-!
# `PartII-a:N01/9/1/3/3/2/1/2/1`: `GradSliceMeas`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383.  Joint measurability of `(σ,x) ↦ gradE c ν F s i j σ x` (the
strip indicator is then measurable).  The plane heat semigroup applied to the slice derivative
is jointly continuous in `(σ,x)` on all of `ℝ × ℝ²`, because the slice is jointly `C¹` and its
`w`-derivative is jointly continuous and uniformly bounded (`heatSliceBounds`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

/-- For a `C¹` function on `ℝ × ℝ²`, the partial `w`-derivative is the full derivative in the
direction `(0, v)`. -/
theorem gsm_fderiv_slice (G : ℝ × (ℝ × ℝ) → ℂ) (hG : Differentiable ℝ G) (t : ℝ) (w v : ℝ × ℝ) :
    fderiv ℝ (fun w' : ℝ × ℝ => G (t, w')) w v = fderiv ℝ G (t, w) (0, v) := by
  have h1 : HasFDerivAt (fun w' : ℝ × ℝ => ((t, w') : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w :=
    hasFDerivAt_prodMk_right t w
  have h2 : HasFDerivAt (fun w' : ℝ × ℝ => G (t, w'))
      ((fderiv ℝ G (t, w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) w :=
    (hG (t, w)).hasFDerivAt.comp w h1
  rw [h2.fderiv]
  rfl

/-- Joint continuity in `(t,w)` of the `w`-derivative in a fixed direction. -/
theorem gsm_cont_D (G : ℝ × (ℝ × ℝ) → ℂ) (hG : ContDiff ℝ 1 G) (v : ℝ × ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun w' : ℝ × ℝ => G (p.1, w')) p.2 v) := by
  have hfd : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have e : (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun w' : ℝ × ℝ => G (p.1, w')) p.2 v) =
      fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G p (0, v) :=
    funext fun p => gsm_fderiv_slice G (hG.differentiable (by norm_num)) p.1 p.2 v
  rw [e]
  exact hfd.clm_apply continuous_const

/-- Joint continuity of `(t,x) ↦ planeHeat (θ t) (D t ·) x` for a jointly continuous, uniformly
bounded `D`. -/
theorem gsm_continuous_planeHeat (θ : ℝ → ℝ) (hθ : Continuous θ) (D : ℝ × (ℝ × ℝ) → ℂ)
    (hD : Continuous D) (M : ℝ) (hM : ∀ q, ‖D q‖ ≤ M) :
    Continuous (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.B0224.planeHeat (θ p.1) (fun z : ℝ × ℝ => D (p.1, z)) p.2) := by
  have hK : (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.B0224.planeHeat (θ p.1) (fun z : ℝ × ℝ => D (p.1, z)) p.2) =
      fun p : ℝ × (ℝ × ℝ) => ∫ z : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 1 z •
          D (p.1, p.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max (θ p.1) 0) • z)) :=
    funext fun p => UnforcedLeray.Short.PartIIa.N01.HIFD.planeHeat_eq_dilate_gen (θ p.1)
      (fun z : ℝ × ℝ => D (p.1, z)) p.2
  rw [hK]
  have hsq : Continuous fun p : ℝ × (ℝ × ℝ) => Real.sqrt (max (θ p.1) 0) :=
    Real.continuous_sqrt.comp ((hθ.comp continuous_fst).max continuous_const)
  refine MeasureTheory.continuous_of_dominated
    (bound := fun z : UnforcedLeray.Gaussian.Euc 2 => UnforcedLeray.Gaussian.gaussKernel 2 1 z * M)
    ?_ ?_ ?_ ?_
  · intro p
    apply Continuous.aestronglyMeasurable
    refine (UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul ?_
    refine hD.comp (continuous_const.prodMk (continuous_const.sub ?_))
    exact UnforcedLeray.B0224.continuous_planeι.comp
      (continuous_id.const_smul (Real.sqrt (max (θ p.1) 0)))
  · intro p
    refine ae_of_all _ fun z => ?_
    rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z)]
    exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z)
  · exact (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const M
  · refine ae_of_all _ fun z => ?_
    have hc0 : Continuous fun _ : ℝ × (ℝ × ℝ) => UnforcedLeray.Gaussian.gaussKernel 2 1 z :=
      continuous_const
    refine hc0.smul ?_
    refine hD.comp (continuous_fst.prodMk (continuous_snd.sub ?_))
    exact UnforcedLeray.B0224.continuous_planeι.comp (hsq.smul continuous_const)

theorem gradSliceMeas : UnforcedLeray.Short.PartIIa.N01.HIGS.GradSliceMeas := by
  intro c ν hc hν F hF s _hs i j
  obtain ⟨-, hcd, M, hM0, hM1⟩ := UnforcedLeray.Short.PartIIa.N01.heatSliceBounds c hc F hF
  have hGc : ContDiff ℝ 1
      (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Short.PartIIa.N01.heatSlice c F p.1 p.2 i) :=
    hcd i
  have hDc : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun w' : ℝ × ℝ => UnforcedLeray.Short.PartIIa.N01.heatSlice c F p.1 w' i)
        p.2 (UnforcedLeray.B0579.dir j)) :=
    gsm_cont_D (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Short.PartIIa.N01.heatSlice c F p.1 p.2 i)
      hGc (UnforcedLeray.B0579.dir j)
  have hDb : ∀ q : ℝ × (ℝ × ℝ),
      ‖fderiv ℝ (fun w' : ℝ × ℝ => UnforcedLeray.Short.PartIIa.N01.heatSlice c F q.1 w' i)
        q.2 (UnforcedLeray.B0579.dir j)‖ ≤ M * ‖UnforcedLeray.B0579.dir j‖ := by
    intro q
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM1 i q.1 q.2) (norm_nonneg _))
  have hPc := gsm_continuous_planeHeat (fun t : ℝ => ν * (s - t))
    (continuous_const.mul (continuous_const.sub continuous_id))
    (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun w' : ℝ × ℝ => UnforcedLeray.Short.PartIIa.N01.heatSlice c F q.1 w' i)
        q.2 (UnforcedLeray.B0579.dir j))
    hDc (M * ‖UnforcedLeray.B0579.dir j‖) hDb
  have hG : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.Short.PartIIa.N01.HIGS.gradE c ν F s i j p.1 p.2) :=
    hPc.measurable.enorm
  exact hG.indicator (measurableSet_Ioo.prod MeasurableSet.univ)
