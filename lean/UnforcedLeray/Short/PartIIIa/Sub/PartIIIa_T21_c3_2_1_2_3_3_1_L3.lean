import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Op
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Package
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.Exterior
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/3`: the rough extension `ARelRough` of the damped interaction

Source of record: `the November 2 reference manuscript` (SP), lines 2914-2925
(`eq:short-causal-damped-complement`: all added terms bounded finite rank), 2974-2978 (the
interaction is bounded on `X_{m,d}`).

Proved here:
* `aRel_rough_of_goodAt`: at a block age `r = s(σ)` where the good-age package
  `RelIntA.GoodAt κ P m K_A tr r` holds (`X_{m,d(r)}` bound of `movDampedComplInt` with constant
  `K_A` and a.e. additivity), `A_rel σ` acts on every cell-supported datum `X = I_d Φ` by the pinned
  formula `I_d movDampedComplInt Φ`. Proof: `RelIntA.exists_op` gives a bounded `T` on `L²_m` with
  `T x = I_d movDampedComplInt (x|cell)` for every `x`; `A_rel σ` and `T` agree on smooth compactly
  supported data (the pin `IsDampedComplBlockInt` and `movDampedComplInt_congr`), hence everywhere
  by density (`clm_eq_of_smooth`); finally `X|cell = Φ` a.e. on the cell.
* `aRelRough_of_goodAtBlock`: `GoodAtBlock κ → ARelRough κ`.

Not proved: `GoodAtBlock κ` is the good-age package at every age of the regime
`ν > 0, 1 ≤ b ≤ θ(r)` of `ARelRough`; the proved `RelIntA.goodAt_package` gives it only for
`b ≥ b₀`, `ν ≤ ν₀` (it rests on `movLamDualHeatBound`, `movLamDualEulerSubBound`,
`complModeForceOscillator`, `trainCoeff_bounds`, all in that regime).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub BlockPropagatorInteriorSub

namespace ComplMildTestedSplit

namespace ARelRoughSub

/-- Two bounded operators on `L²_m` that agree on smooth compactly supported data are equal. -/
theorem clm_eq_of_smooth {m : ℝ} (S T : Planar.L2w m →L[ℂ] Planar.L2w m)
    (h : ∀ (Ψ₀ : ℂ → ℂ), HasCompactSupport Ψ₀ → ContDiff ℝ ∞ Ψ₀ →
      ∀ hmem : MemLp Ψ₀ 2 (Planar.wMeasure m), S (hmem.toLp Ψ₀) = T (hmem.toLp Ψ₀)) :
    S = T := by
  have : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  refine ContinuousLinearMap.ext fun V => ?_
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hδ : 0 < ε / (‖S‖ + ‖T‖ + 1) := by positivity
  obtain ⟨Ψ₀, hΨc, hΨs, hΨerr⟩ := (Lp.memLp V).exist_eLpNorm_sub_le (p := 2)
    ENNReal.ofNat_ne_top (by norm_num) hδ
  have hΨmem : MemLp Ψ₀ 2 (Planar.wMeasure m) :=
    hΨs.continuous.memLp_of_hasCompactSupport hΨc
  have hVX : ‖V - hΨmem.toLp Ψ₀‖ ≤ ε / (‖S‖ + ‖T‖ + 1) := by
    rw [Lp.norm_def]
    have he : eLpNorm (⇑(V - hΨmem.toLp Ψ₀)) 2 (Planar.wMeasure m) =
        eLpNorm (⇑V - Ψ₀) 2 (Planar.wMeasure m) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub V (hΨmem.toLp Ψ₀), hΨmem.coeFn_toLp] with z h1 h2
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply]
    rw [he]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le hΨerr
  have hST := h Ψ₀ hΨc hΨs hΨmem
  rw [dist_eq_norm]
  have hsplit : S V - T V = S (V - hΨmem.toLp Ψ₀) - T (V - hΨmem.toLp Ψ₀) := by
    rw [map_sub, map_sub, hST]
    abel
  rw [hsplit]
  have hn := norm_nonneg (V - hΨmem.toLp Ψ₀)
  calc ‖S (V - hΨmem.toLp Ψ₀) - T (V - hΨmem.toLp Ψ₀)‖
      ≤ ‖S (V - hΨmem.toLp Ψ₀)‖ + ‖T (V - hΨmem.toLp Ψ₀)‖ := norm_sub_le _ _
    _ ≤ ‖S‖ * ‖V - hΨmem.toLp Ψ₀‖ + ‖T‖ * ‖V - hΨmem.toLp Ψ₀‖ :=
        add_le_add (S.le_opNorm _) (T.le_opNorm _)
    _ ≤ (‖S‖ + ‖T‖ + 1) * ‖V - hΨmem.toLp Ψ₀‖ := by nlinarith
    _ ≤ (‖S‖ + ‖T‖ + 1) * (ε / (‖S‖ + ‖T‖ + 1)) := by gcongr
    _ = ε := by field_simp

/-- **Rough extension at a good age** (SP 2974-2978): where the good-age package holds, `A_rel σ`
acts on every cell-supported datum `X = I_d Φ` by the pinned formula. -/
theorem aRel_rough_of_goodAt {κ : PlanarFrameKernels} {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hA : IsDampedComplBlockInt κ P ν m tr t₁ B A_rel) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) B)
    {K_A : ℝ} (hK : 0 ≤ K_A)
    (hG : OrgSplit.RelIntA.GoodAt κ P m K_A tr (ageAt ν t₁ σ))
    (Φ : ℝ × ℝ → ℂ) (X : Planar.L2w m)
    (hX : ⇑X =ᵐ[volume] fun z : ℂ =>
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) Φ (cToPlane z)) :
    ⇑(A_rel σ X) =ᵐ[volume] fun z : ℂ =>
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
        (movDampedComplInt κ P tr (ageAt ν t₁ σ) Φ) (cToPlane z) := by
  obtain ⟨T, hT, -⟩ := OrgSplit.RelIntA.exists_op κ P tr (ageAt ν t₁ σ) hK hG
  have hAT : A_rel σ = T := by
    refine clm_eq_of_smooth _ _ fun Ψ₀ hΨc hΨs hΨmem => ?_
    have hΦs : ContDiff ℝ ∞ (fun y => Ψ₀ (planeToC y)) :=
      hΨs.comp RelExteriorSub.contDiff_planeToC
    have hΦc : HasCompactSupport (fun y => Ψ₀ (planeToC y)) := by
      refine HasCompactSupport.intro (K := cToPlane '' tsupport Ψ₀)
        (hΨc.isCompact.image RelExteriorSub.continuous_cToPlane) fun y hy => ?_
      have : planeToC y ∉ tsupport Ψ₀ := fun h => hy ⟨planeToC y, h, cToPlane_planeToC y⟩
      exact image_eq_zero_of_notMem_tsupport this
    have hXn : ⇑(hΨmem.toLp Ψ₀) =ᵐ[volume]
        fun z => (fun y => Ψ₀ (planeToC y)) (cToPlane z) := by
      filter_upwards [(Planar.volume_ac m).ae_le hΨmem.coeFn_toLp] with z hz
      rw [hz, planeToC_cToPlane]
    have h1 := hA σ hσ _ hΦs hΦc (hΨmem.toLp Ψ₀) hXn
    have h2 := hT (hΨmem.toLp Ψ₀)
    have hc : OrgSplit.RelIntA.cylRep (hΨmem.toLp Ψ₀)
        =ᵐ[volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))))]
        fun y => Ψ₀ (planeToC y) :=
      OrgSplit.RelIntA.cylRep_ae_of hΨmem.coeFn_toLp
    have hcong := OrgSplit.RelIntA.movDampedComplInt_congr κ P tr (ageAt ν t₁ σ) hc
    refine Lp.ext ?_
    filter_upwards [(Planar.wMeasure_ac m).ae_le h1, h2] with z hz1 hz2
    rw [hz1, hz2]
    unfold OrgSplit.RelIntA.opFun
    rw [hcong]
  have hc : OrgSplit.RelIntA.cylRep X
      =ᵐ[volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))))] Φ := by
    have h0 := OrgSplit.RelIntA.cylRep_ae_of
      (d := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) ((Planar.wMeasure_ac m).ae_le hX)
    filter_upwards [h0, ae_restrict_mem (B0579.measurableSet_cell
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))))] with y hy hmem
    unfold OrgSplit.RelIntA.cylRep
    rw [hy, cToPlane_planeToC, cellZeroExt, Set.indicator_of_mem hmem]
  have hcong := OrgSplit.RelIntA.movDampedComplInt_congr κ P tr (ageAt ν t₁ σ) hc
  rw [hAT]
  filter_upwards [(Planar.volume_ac m).ae_le (hT X)] with z hz
  rw [hz]
  unfold OrgSplit.RelIntA.opFun
  rw [hcong]

end ARelRoughSub

/-- **Good-age package on the whole regime of `ARelRough`** (analytic leaf): at every age `r` with
`1 ≤ b ≤ θ(r)`, `movDampedComplInt` is bounded on `X_{m,d(r)}` and a.e. additive. The proved
`OrgSplit.RelIntA.goodAt_package` gives this only for `b ≥ b₀`, `ν ≤ ν₀`. -/
def GoodAtBlock (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K b : ℝ, 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∃ K_A : ℝ, 0 ≤ K_A ∧ OrgSplit.RelIntA.GoodAt κ P m K_A tr r

open ARelRoughSub in
/-- `ARelRough` from the good-age package on the block regime. -/
theorem aRelRough_of_goodAtBlock (κ : PlanarFrameKernels) (hG : GoodAtBlock κ) :
    ARelRough κ := by
  intro hκ P hP m hm K B b _hB hb ν hν hF tr htr t₁ t₂ ht₁ ht₁₂ hbθ hZ A_rel hA σ hσ Φ _hΦ X hX
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht₁₂
  have hs : 0 ≤ ageAt ν t₁ σ :=
    RelExteriorSub.ageAt_nonneg hν ht₁ ht₂ hσ.1 (by rw [hZ]; exact hσ.2)
  have hle : ageAt ν t₁ σ ≤ t₂ := by
    have h := ageAt_mono_on_block hν ht₁ ht₂ hZ hσ.1 hσ.2 le_rfl
    rwa [ageAt_eq_of_movingZ_sub hν ht₂ hZ] at h
  have hθ : b ≤ clockTheta ν (ageAt ν t₁ σ) :=
    hbθ.trans (clockTheta_le_of_le hν hs hle)
  obtain ⟨K_A, hK, hGA⟩ := hG hκ P hP m hm K b hb ν hν hF tr htr _ hs hθ
  exact aRel_rough_of_goodAt hA hσ hK hGA Φ X hX

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
