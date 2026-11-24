import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_1_org
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_N
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelBlockDiagonal.Support

/-!
# `PartIII-a:T21/c3/2/1/2/2/1/1`: leaf `RelB3s`

Source of record: `the November 2 reference manuscript` (SP) 2919-2921, 2941.

Route: split `W = P W + (W - P W)` with `P = cellProjW m d` the cell projection (`d = d(s)`).
The cell part is approximated by `testW φ₁ + I testW φ₂` with real cylinder tests of period `d`
(`exists_test_approx_cell`); the rescaled tests `x ↦ a⁻² φ_i(x/√a)` are cylinder tests of period
`c = ν⁻²`, carry free cylinder flows (`free_cyl_exists_unique`), and `JscaleInv a` returns `φ_i`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  BlockPropagatorInteriorSub VariationOfConstantsMildSub RelRegularityOrg
namespace RelRegularityOrg2

/-- Rescaling a cylinder test of period `d = c/√a` to period `c`. -/
theorem isCylTest_rescale {c a : ℝ} (ha : 0 < a) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest (c / Real.sqrt a) φ) :
    B0579.IsCylTest c (fun x => (a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun x : B0579.Plane => (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by
      fun_prop
    exact contDiff_const.mul (hφ.smooth.comp h1)
  · intro x
    have : (x.1 + c) / Real.sqrt a = x.1 / Real.sqrt a + c / Real.sqrt a := by ring
    simp only [this]
    rw [hφ.periodic (x.1 / Real.sqrt a, x.2 / Real.sqrt a)]
  · obtain ⟨R, hR⟩ := hφ.band
    refine ⟨R * Real.sqrt a, fun x hx => ?_⟩
    have : R < |x.2 / Real.sqrt a| := by
      rw [abs_div, abs_of_pos hs, lt_div_iff₀ hs]; exact hx
    show _ * _ = 0
    rw [hR (x.1 / Real.sqrt a, x.2 / Real.sqrt a) this, mul_zero]

theorem relB3s_leaf (κ : PlanarFrameKernels) : RelB3s κ := by
  intro P m K B b ν tr t₁ t₂ ctx σ hσ
  obtain ⟨_, _, hm, hB, hb, hν, _, htr, ht₁, ht₁₂, hbt, hBz⟩ := ctx
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht₁₂
  have hs0 : 0 ≤ ageAt ν t₁ σ :=
    RelExteriorSub.ageAt_nonneg hν ht₁ ht₂ hσ.1 (by rw [hBz]; exact hσ.2)
  set s := ageAt ν t₁ σ with hs
  set a := clockA ν s with ha
  have ha0 : 0 < a := by rw [ha]; unfold clockA; positivity
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  set d := cellLen (ν ^ (-2 : ℝ)) a with hd
  have hd0 : 0 < d := div_pos hc (Real.sqrt_pos.2 ha0)
  rw [Metric.dense_iff]
  intro W δ hδ
  set V := BlockPropagatorInteriorSub.OrgSplit3.cellProjW m d W with hV
  have hVs : IsCellSupportedW d V := RelFreeNormSub.cellProjW_cellSupported d W
  obtain ⟨φ₁, φ₂, h₁, h₂, hlt⟩ :=
    RelBlockDiagonalSub.exists_test_approx_cell hd0 V hVs hδ
  have h₁' := isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha0 h₁
  have h₂' := isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha0 h₂
  refine ⟨(W - V) + (RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    have : W - ((W - V) + (RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂)) = V - (RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂) := by abel
    rw [this]; exact hlt
  · -- membership in the class
    refine ⟨_, _, h₁', h₂', ?_, ?_, ?_⟩
    · exact (UnforcedLeray.Short.IIb.free_cyl_exists_unique m ν (ν ^ (-2 : ℝ)) hm hν hc tr htr s hs0 _
        (h₁'.memLp m)).1
    · exact (UnforcedLeray.Short.IIb.free_cyl_exists_unique m ν (ν ^ (-2 : ℝ)) hm hν hc tr htr s hs0 _
        (h₂'.memLp m)).1
    · have hVc : (V : ℂ → ℂ) =ᵐ[volume] _ :=
        (Planar.volume_ac m).ae_le
          (((Lp.memLp W).indicator
            (BlockPropagatorInteriorSub.OrgSplit3.measurableSet_cellC d)).coeFn_toLp)
      filter_upwards [hVc,
        (Planar.volume_ac m).ae_le (Lp.coeFn_add (W - V) (RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂)),
        (Planar.volume_ac m).ae_le (Lp.coeFn_sub W V),
        (Planar.volume_ac m).ae_le (Lp.coeFn_add (RelBlockDiagonalSub.testW m h₁)
          (Complex.I • RelBlockDiagonalSub.testW m h₂)),
        (Planar.volume_ac m).ae_le (Lp.coeFn_smul Complex.I (RelBlockDiagonalSub.testW m h₂)),
        (Planar.volume_ac m).ae_le (RelBlockDiagonalSub.coeFn_testW m h₁),
        (Planar.volume_ac m).ae_le (RelBlockDiagonalSub.coeFn_testW m h₂)]
        with z e0 e1 e2 e3 e4 e5 e6
      intro hz
      have hz' : z ∈ {z : ℂ | cToPlane z ∈ B0579.cell d} := hz
      rw [Set.indicator_of_mem hz'] at e0
      rw [e1, Pi.add_apply, e2, Pi.sub_apply, e3, Pi.add_apply, e4, Pi.smul_apply, e5, e6,
        smul_eq_mul, e0]
      have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha0).ne'
      have h2 : (a ^ 2 : ℝ) ≠ 0 := by positivity
      have hz'' : cToPlane z ∈ B0579.cell d := hz
      simp only [cellZeroExt, JscaleInv, Set.indicator_of_mem hz'']
      have e7 : ∀ x : ℝ, Real.sqrt (clockA ν (ageAt ν t₁ σ)) * x / Real.sqrt a = x := by
        intro x
        show Real.sqrt a * x / Real.sqrt a = x
        field_simp
      simp only [e7]
      have e9 : (clockA ν (ageAt ν t₁ σ)) = a := rfl
      rw [e9]
      have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
      push_cast
      field_simp
      ring
