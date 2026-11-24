import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_N
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_2_1_final
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_2

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2`: the frame leaves of `ComplMildTested`

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2945
(`\bar F(z,t) = I_z F(z,t) R_t + S(z,t)(I - Π_t)`, `S f(y) = ρ⁴ f(ρ y)`, `ρ = d(t)/d(z)`).

Proved here: `frelDiag : FrelDiag` (`\bar F_{rel}(t,t) = I`, SP 2941). At equal ages `ρ = 1`, so
the exterior term is the identity on `(I - Π_t)`, the normaliser is `N(s,s) = 1`, and the pinned
free cylinder flow starts at its datum (`freeCylSmoothExists_proof`, `ω₀ s = f`). Hence
`F_rel τ τ` fixes every datum agreeing on the cell with `J_a⁻¹ f` for a real cylinder test `f`
(`frel_diag_of_pin`): the zero-extended cylinder tests `testW` (`frel_diag_testW`) and the data
vanishing on the cell (`f = 0`, `ω₀ = 0`, `frel_diag_ext`). By density of
`testW φ₁ + i testW φ₂` in the cell-supported data (`exists_test_approx_cell`) and continuity,
`F_rel τ τ` fixes cell-supported data (`frel_diag_cell`); the cell projection `cellProjW` splits a
general datum into the two parts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub BlockPropagatorInteriorSub

namespace ComplMildTestedSplit

namespace FrelDiagSub

/-- The normaliser at equal ages: `N(s, s) = 1`. -/
theorem clockN_self (P : PlanarData) {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    clockN P ν s s = 1 := by
  have hθ : clockTheta ν s ≠ 0 := by
    unfold clockTheta clockA
    positivity
  unfold clockN
  rw [sub_self, mul_zero, Real.exp_zero, div_self hθ, Real.one_rpow, mul_one]

/-- **Pin at equal ages** (SP 2941-2943): `F_rel τ τ` fixes every datum that agrees on the cell
with `J_a⁻¹ f` for a real cylinder test `f` whose free cylinder flow starts exactly at `f`. -/
theorem frel_diag_of_pin {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτB : τ ≤ B) (hs : 0 ≤ ageAt ν t₁ τ)
    (f : B0579.Plane → ℝ) (hf : B0579.IsCylTest (ν ^ (-2 : ℝ)) f)
    (ω₀ : ℝ → B0579.Plane → ℝ)
    (hω₀ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ τ) f ω₀)
    (hω₀s : ω₀ (ageAt ν t₁ τ) = f) (W : Planar.L2w m)
    (hW : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) →
        (W : ℂ → ℂ) z =
          JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((f x : ℝ) : ℂ)) (cToPlane z)) :
    F_rel τ τ W = W := by
  have h := hF τ τ hτ0 le_rfl hτB f hf ω₀ hω₀ W hW
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) :=
    RelExteriorSub.cellLen_pos hν hs
  have hN : clockN P ν (ageAt ν t₁ τ) (ageAt ν t₁ τ) = 1 := clockN_self P hν hs
  refine Lp.ext ((Planar.wMeasure_ac m).ae_le ?_)
  filter_upwards [h, hW] with z hz hzW
  rw [hz, hN, hω₀s]
  unfold periodizedExt extDilCocycle
  rw [div_self hd.ne']
  simp only [Complex.ofReal_one, inv_one, one_mul, one_pow]
  by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
  · have hcp : ((cToPlane z).1, (cToPlane z).2) = cToPlane z := rfl
    simp only [cellZeroExt, Set.indicator_of_mem hmem, hcp, planeToC_cToPlane]
    rw [hzW hmem]
    ring
  · have hcp : ((cToPlane z).1, (cToPlane z).2) = cToPlane z := rfl
    simp only [cellZeroExt, Set.indicator_of_notMem hmem, hcp, planeToC_cToPlane]
    ring

/-- `F_rel τ τ` fixes the zero-extended real cylinder tests of period `d(s)`. -/
theorem frel_diag_testW {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (hm : 8 < m)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτB : τ ≤ B) (hs : 0 ≤ ageAt ν t₁ τ) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) φ) :
    F_rel τ τ (RelBlockDiagonalSub.testW m hφ) = RelBlockDiagonalSub.testW m hφ := by
  have ha : 0 < clockA ν (ageAt ν t₁ τ) := by unfold clockA; positivity
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hf := RelBlockDiagonalSub.isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha hφ
  obtain ⟨ω₀, hω₀, hω₀s, -⟩ := UnforcedLeray.Short.IIb.freeCylSmoothExists_proof m ν
    (ν ^ (-2 : ℝ)) hm hν hc tr htr (ageAt ν t₁ τ) hs _ hf
  have hV := RelBlockDiagonalSub.coeFn_testW m hφ
  refine frel_diag_of_pin hF hν hτ0 hτB hs _ hf ω₀ hω₀ hω₀s _ ?_
  filter_upwards [(Planar.volume_ac m).ae_le hV] with z hz hmem
  rw [hz, RelBlockDiagonalSub.jscaleInv_rescale ha φ, cellZeroExt, Set.indicator_of_mem hmem]

/-- `F_rel τ τ` fixes the data vanishing on the cell (`f = 0`, `ω₀ = 0`). -/
theorem frel_diag_ext {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτB : τ ≤ B) (hs : 0 ≤ ageAt ν t₁ τ) (W : Planar.L2w m)
    (hW : OrgSplit.IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) W) :
    F_rel τ τ W = W := by
  refine frel_diag_of_pin hF hν hτ0 hτB hs (fun _ => 0) (RelExteriorSub.isCylTest_zero _)
    (fun _ _ => 0) (RelExteriorSub.isFreeCylFlow_zero m tr _) rfl W ?_
  filter_upwards [hW] with z hz hmem
  rw [hz hmem]
  simp [JscaleInv]

/-- `F_rel τ τ` fixes the cell-supported data (density of `testW φ₁ + i testW φ₂`). -/
theorem frel_diag_cell {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (hm : 8 < m)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτB : τ ≤ B) (hs : 0 ≤ ageAt ν t₁ τ) (W : Planar.L2w m)
    (hW : IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) W) :
    F_rel τ τ W = W := by
  have hd := RelExteriorSub.cellLen_pos hν hs
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hδ : 0 < ε / (‖F_rel τ τ‖ + 1) := by positivity
  obtain ⟨φ₁, φ₂, h₁, h₂, happrox⟩ :=
    RelBlockDiagonalSub.exists_test_approx_cell (m := m) hd W hW hδ
  have hA : F_rel τ τ (RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂) =
      RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂ := by
    rw [map_add, map_smul, frel_diag_testW hF hν hm htr hτ0 hτB hs h₁,
      frel_diag_testW hF hν hm htr hτ0 hτB hs h₂]
  set A := RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂ with hAdef
  rw [dist_eq_norm]
  have hsplit : F_rel τ τ W - W = F_rel τ τ (W - A) - (W - A) := by
    rw [map_sub, hA]
    abel
  rw [hsplit]
  calc ‖F_rel τ τ (W - A) - (W - A)‖ ≤ ‖F_rel τ τ (W - A)‖ + ‖W - A‖ := norm_sub_le _ _
    _ ≤ ‖F_rel τ τ‖ * ‖W - A‖ + ‖W - A‖ := by
        gcongr
        exact (F_rel τ τ).le_opNorm _
    _ = (‖F_rel τ τ‖ + 1) * ‖W - A‖ := by ring
    _ ≤ (‖F_rel τ τ‖ + 1) * (ε / (‖F_rel τ τ‖ + 1)) := by
        gcongr
    _ = ε := by
        field_simp

end FrelDiagSub

open FrelDiagSub in
/-- **`FrelDiag`** (SP 2941): the periodized relative free evolution is the identity at equal ages
of the block. -/
theorem frelDiag : FrelDiag := by
  intro P _hP m hm B b _hB _hb ν hν tr htr t₁ t₂ ht₁ ht₁₂ _hbθ hZ F_rel hF τ hτ X
  have hs : 0 ≤ ageAt ν t₁ τ :=
    RelExteriorSub.ageAt_nonneg hν ht₁ (ht₁.trans ht₁₂) hτ.1 (by rw [hZ]; exact hτ.2)
  have h1 := frel_diag_cell hF hν hm htr hτ.1 hτ.2 hs
    (OrgSplit3.cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) X)
    (RelFreeNormSub.cellProjW_cellSupported _ X)
  have h2 := frel_diag_ext hF hν hτ.1 hτ.2 hs
    (X - OrgSplit3.cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) X)
    (RelFreeNormSub.sub_cellProjW_exteriorSupported _ X)
  calc F_rel τ τ X
      = F_rel τ τ (OrgSplit3.cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) X) +
          F_rel τ τ (X - OrgSplit3.cellProjW m
            (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) X) := by
        rw [← map_add, add_sub_cancel]
    _ = X := by rw [h1, h2, add_sub_cancel]

/-- Assembly of the three frame leaves from `frelDiag` and the two remaining analytic leaves. -/
theorem frameLeaves_of (κ : PlanarFrameKernels) (h1 : FrameTestedDuhamel κ)
    (h2 : AmplMovingFTC κ) : FrelDiag ∧ FrameTestedDuhamel κ ∧ AmplMovingFTC κ :=
  ⟨frelDiag, h1, h2⟩

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa

theorem modeTestedDuhamelRegime (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.ModeTestedDuhamelRegime κ :=
  UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.modeTestedDuhamelRegime_of κ
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.frelDiag
    (frameTestedDuhamel κ)
    (amplMovingFTCRegime κ)
