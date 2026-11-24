import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2

/-!
# Differentiation under the Gaussian average (`T0gDiffParam`)

Source `the November 2 reference manuscript`
lines 1640-1656. The integrand `G1(w) • K x w` is dominated, together with its
`x`-derivative, by `C (1+‖w‖)^N G1(w)` (polynomial moments, `T0gPolyGauss`), so
Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` applies with the
neighbourhood `univ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem t0g_diffParam :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gDiffParam := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gDiffParam
  intro hpoly X V _ _ _ _ _ _ K hK hKb hKd x
  obtain ⟨C, N, hC⟩ := hKb
  obtain ⟨D, M, hD⟩ := hKd
  have hG0 : ∀ w : UnforcedLeray.Gaussian.Euc 2,
      0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 w :=
    fun w => UnforcedLeray.Gaussian.gaussKernel_nonneg zero_lt_one w
  have hgC : Continuous (fun p : X × UnforcedLeray.Gaussian.Euc 2 => K p.1 p.2) :=
    hK.continuous
  have hKc : ∀ y : X, Continuous fun w : UnforcedLeray.Gaussian.Euc 2 => K y w :=
    fun y => hgC.comp (continuous_const.prodMk continuous_id)
  have hdiffK : ∀ w : UnforcedLeray.Gaussian.Euc 2, Differentiable ℝ (fun y : X => K y w) :=
    fun w => (hK.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have hfd : Continuous fun p : X × UnforcedLeray.Gaussian.Euc 2 =>
      fderiv ℝ (fun q : X × UnforcedLeray.Gaussian.Euc 2 => K q.1 q.2) p :=
    hK.continuous_fderiv (by simp)
  have hfdx : ∀ w : UnforcedLeray.Gaussian.Euc 2,
      fderiv ℝ (fun y : X => K y w) x =
        (fderiv ℝ (fun q : X × UnforcedLeray.Gaussian.Euc 2 => K q.1 q.2) (x, w)).comp
          ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] UnforcedLeray.Gaussian.Euc 2)) := by
    intro w
    have h1 : HasFDerivAt (fun y : X => (y, w))
        ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] UnforcedLeray.Gaussian.Euc 2)) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const w x)
    have h2 := ((hK.differentiable (by simp)) (x, w)).hasFDerivAt.comp x h1
    exact h2.fderiv
  have hcontw : Continuous fun w : UnforcedLeray.Gaussian.Euc 2 =>
      fderiv ℝ (fun y : X => K y w) x := by
    have hc2 : Continuous fun w : UnforcedLeray.Gaussian.Euc 2 =>
        (fderiv ℝ (fun q : X × UnforcedLeray.Gaussian.Euc 2 => K q.1 q.2) (x, w)).comp
          ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] UnforcedLeray.Gaussian.Euc 2)) :=
      (hfd.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
    exact hc2.congr fun w => (hfdx w).symm
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y w => UnforcedLeray.Gaussian.gaussKernel 2 1 w • fderiv ℝ (fun z => K z w) y)
    (bound := fun w => D * ((1 + ‖w‖) ^ M * UnforcedLeray.Gaussian.gaussKernel 2 1 w))
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul (hKc y)).aestronglyMeasurable
  · refine ((hpoly N).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul
        (hKc x)).aestronglyMeasurable
    · rw [norm_smul, Real.norm_of_nonneg (hG0 w)]
      calc _ ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 w * (C * (1 + ‖w‖) ^ N) :=
            mul_le_mul_of_nonneg_left (hC x w) (hG0 w)
        _ = C * ((1 + ‖w‖) ^ N * UnforcedLeray.Gaussian.gaussKernel 2 1 w) := by ring
  · exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul
      hcontw).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun w y _ => ?_
    rw [norm_smul, Real.norm_of_nonneg (hG0 w)]
    calc _ ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 w * (D * (1 + ‖w‖) ^ M) :=
          mul_le_mul_of_nonneg_left (hD y w) (hG0 w)
      _ = D * ((1 + ‖w‖) ^ M * UnforcedLeray.Gaussian.gaussKernel 2 1 w) := by ring
  · exact (hpoly M).const_mul D
  · exact Filter.Eventually.of_forall fun w y _ =>
      ((hdiffK w y).hasFDerivAt).const_smul (UnforcedLeray.Gaussian.gaussKernel 2 1 w)

end
