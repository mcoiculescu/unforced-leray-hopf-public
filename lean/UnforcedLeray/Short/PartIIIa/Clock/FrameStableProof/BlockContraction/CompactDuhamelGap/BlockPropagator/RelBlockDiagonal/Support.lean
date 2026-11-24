import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.Exterior
import UnforcedLeray.Short.PartIIb.Tasks.CylExistence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# `PartIII-a:T21/c3/2/1/1/org/2`, helpers: cell-supported data in `L²_m`

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2945.

* `extRes m d`: restriction of `L²_m` data to the exterior of the cell `B0579.cell d`;
  `IsCellSupportedW d V ↔ extRes m d V = 0`, so the cell-supported data form a closed subspace,
  stable under Bochner interval integrals (`isCellSupportedW_intervalIntegral`) and under limits
  (`isCellSupportedW_of_approx`).
* `exists_test_approx_cell`: real cylinder tests of period `d`, zero-extended off the cell
  (`testW`), are dense in the cell-supported data (`free_cyl_test_approx` applied to the real and
  imaginary parts of the cell restriction).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub

namespace RelBlockDiagonalSub

/-! ### The exterior restriction and the closed subspace of cell-supported data -/

/-- The exterior of the cell `B0579.cell d`, as a subset of `ℂ`. -/
def extSet (d : ℝ) : Set ℂ := {z : ℂ | cToPlane z ∉ B0579.cell d}

theorem measurableSet_extSet (d : ℝ) : MeasurableSet (extSet d) :=
  ((B0579.measurableSet_cell d).preimage measurable_cToPlane).compl

/-- Restriction of `L²_m` data to the exterior of the cell `B0579.cell d`. -/
def extRes (m d : ℝ) : Planar.L2w m →L[ℂ] Lp ℂ 2 ((Planar.wMeasure m).restrict (extSet d)) :=
  LpToLpRestrictCLM ℂ ℂ ℂ (Planar.wMeasure m) 2 (extSet d)

theorem isCellSupportedW_iff {m d : ℝ} (V : Planar.L2w m) :
    IsCellSupportedW d V ↔ extRes m d V = 0 := by
  have hcoe : (extRes m d V : ℂ → ℂ) =ᵐ[(Planar.wMeasure m).restrict (extSet d)] V :=
    LpToLpRestrictCLM_coeFn ℂ (extSet d) V
  constructor
  · intro hV
    have h1 : ∀ᵐ z ∂(Planar.wMeasure m), z ∈ extSet d → (V : ℂ → ℂ) z = 0 :=
      (Planar.wMeasure_ac m).ae_le hV
    have h2 : (V : ℂ → ℂ) =ᵐ[(Planar.wMeasure m).restrict (extSet d)] 0 :=
      (ae_restrict_iff' (measurableSet_extSet d)).2 h1
    exact Lp.ext (hcoe.trans (h2.trans (Lp.coeFn_zero _ _ _).symm))
  · intro h0
    have h2 : (V : ℂ → ℂ) =ᵐ[(Planar.wMeasure m).restrict (extSet d)] 0 := by
      refine hcoe.symm.trans ?_
      rw [h0]
      exact Lp.coeFn_zero _ _ _
    have h1 : ∀ᵐ z ∂(Planar.wMeasure m), z ∈ extSet d → (V : ℂ → ℂ) z = 0 :=
      (ae_restrict_iff' (measurableSet_extSet d)).1 h2
    exact (Planar.volume_ac m).ae_le h1

theorem isClosed_cellSupported (m d : ℝ) :
    IsClosed {V : Planar.L2w m | IsCellSupportedW d V} := by
  have h : {V : Planar.L2w m | IsCellSupportedW d V} = (extRes m d) ⁻¹' {0} := by
    ext V
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    exact isCellSupportedW_iff V
  rw [h]
  exact isClosed_singleton.preimage (extRes m d).continuous

theorem isCellSupportedW_add {m d : ℝ} {V W : Planar.L2w m} (hV : IsCellSupportedW d V)
    (hW : IsCellSupportedW d W) : IsCellSupportedW d (V + W) := by
  rw [isCellSupportedW_iff] at hV hW ⊢
  rw [map_add, hV, hW, add_zero]

theorem isCellSupportedW_smul {m d : ℝ} (a : ℂ) {V : Planar.L2w m}
    (hV : IsCellSupportedW d V) : IsCellSupportedW d (a • V) := by
  rw [isCellSupportedW_iff] at hV ⊢
  rw [map_smul, hV, smul_zero]

theorem isCellSupportedW_intervalIntegral {m d a b : ℝ} {g : ℝ → Planar.L2w m}
    (hg : IntervalIntegrable g volume a b) (h : ∀ r ∈ uIcc a b, IsCellSupportedW d (g r)) :
    IsCellSupportedW d (∫ r in a..b, g r) := by
  rw [isCellSupportedW_iff, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hg]
  have h0 : EqOn (fun r => extRes m d (g r)) (fun _ => 0) (uIcc a b) :=
    fun r hr => (isCellSupportedW_iff _).1 (h r hr)
  rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero]

/-- Cell-supported data are closed under limits. -/
theorem isCellSupportedW_of_approx {m d : ℝ} {V : Planar.L2w m}
    (h : ∀ ε : ℝ, 0 < ε → ∃ X : Planar.L2w m, IsCellSupportedW d X ∧ ‖V - X‖ < ε) :
    IsCellSupportedW d V := by
  have hmem : V ∈ closure {X : Planar.L2w m | IsCellSupportedW d X} :=
    Metric.mem_closure_iff.2 fun ε hε => by
      obtain ⟨X, hX, hVX⟩ := h ε hε
      exact ⟨X, hX, by rw [dist_eq_norm]; exact hVX⟩
  rw [(isClosed_cellSupported m d).closure_eq] at hmem
  exact hmem

/-! ### Density of zero-extended cylinder tests in the cell-supported data -/

/-- A real cylinder test of period `d`, zero-extended off `B0579.cell d`, as an element of
`L²_m`. -/
def testW (m : ℝ) {d : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ) : Planar.L2w m :=
  (memLp_cellZeroExt_cToPlane d m ((hφ.memLp m).ofReal (K := ℂ))).toLp _

theorem coeFn_testW (m : ℝ) {d : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ) :
    (testW m hφ : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z) :=
  MemLp.coeFn_toLp _

/-- The cell restriction of `W ∈ L²_m` lies in `X_{m,d}`. -/
theorem memLp_planeToC_cell (m d : ℝ) (W : Planar.L2w m) :
    MemLp (fun y => (W : ℂ → ℂ) (planeToC y)) 2 (B0579.cellMeasure d m) := by
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable (fun y => (W : ℂ → ℂ) (planeToC y))
        (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) :=
      (Lp.aestronglyMeasurable W).comp_measurePreserving (measurePreserving_planeToC_wMeasure m)
    unfold B0579.cellMeasure
    rw [← restrict_withDensity (B0579.measurableSet_cell d)]
    exact h1.restrict
  · have h := xNorm_planeToC_le_norm d m W
    unfold xNorm at h
    exact h.trans_lt ENNReal.ofReal_lt_top

/-- **Density** (SP 2974-2977): cell-supported data are approximated in `L²_m` by
`testW φ₁ + i testW φ₂` with real cylinder tests `φ₁, φ₂` of period `d`. -/
theorem exists_test_approx_cell {m d : ℝ} (hd : 0 < d) (W : Planar.L2w m)
    (hW : IsCellSupportedW d W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (φ₁ φ₂ : ℝ × ℝ → ℝ) (h₁ : B0579.IsCylTest d φ₁) (h₂ : B0579.IsCylTest d φ₂),
      ‖W - (testW m h₁ + Complex.I • testW m h₂)‖ < δ := by
  set g : ℝ × ℝ → ℂ := fun y => (W : ℂ → ℂ) (planeToC y) with hgdef
  have hg : MemLp g 2 (B0579.cellMeasure d m) := memLp_planeToC_cell m d W
  have hRe : MemLp (fun y => (g y).re) 2 (B0579.cellMeasure d m) := hg.re
  have hIm : MemLp (fun y => (g y).im) 2 (B0579.cellMeasure d m) := hg.im
  obtain ⟨u, hu, hulim⟩ := UnforcedLeray.Short.IIb.free_cyl_test_approx d m hd _ hRe
  obtain ⟨v, hv, hvlim⟩ := UnforcedLeray.Short.IIb.free_cyl_test_approx d m hd _ hIm
  have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨n, hn1, hn2⟩ :=
    ((hulim.eventually (gt_mem_nhds hδ2)).and (hvlim.eventually (gt_mem_nhds hδ2))).exists
  refine ⟨u n, v n, hu n, hv n, ?_⟩
  set G : ℝ × ℝ → ℂ := fun y => g y - (((u n y : ℝ) : ℂ) + Complex.I * ((v n y : ℝ) : ℂ))
    with hGdef
  have hcu : Continuous fun y => ((u n y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hu n).continuous
  have hcv : Continuous fun y => ((v n y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hv n).continuous
  have hGm : AEStronglyMeasurable G (B0579.cellMeasure d m) :=
    hg.1.sub (hcu.add (continuous_const.mul hcv)).aestronglyMeasurable
  have hD : ((W - (testW m (hu n) + Complex.I • testW m (hv n)) : Planar.L2w m) : ℂ → ℂ)
      =ᵐ[Planar.wMeasure m] fun z => cellZeroExt d G (cToPlane z) := by
    have hW' := (Planar.wMeasure_ac m).ae_le hW
    filter_upwards [Lp.coeFn_sub W (testW m (hu n) + Complex.I • testW m (hv n)),
      Lp.coeFn_add (testW m (hu n)) (Complex.I • testW m (hv n)),
      Lp.coeFn_smul Complex.I (testW m (hv n)), coeFn_testW m (hu n), coeFn_testW m (hv n),
      hW'] with z h1 h2 h3 h4 h5 h6
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul]
    by_cases hz : cToPlane z ∈ B0579.cell d
    · simp only [cellZeroExt, Set.indicator_of_mem hz, hGdef, hgdef, planeToC_cToPlane]
    · simp only [cellZeroExt, Set.indicator_of_notMem hz, h6 hz]
      ring
  have hnorm : ENNReal.ofReal ‖W - (testW m (hu n) + Complex.I • testW m (hv n))‖ =
      xNorm d m G := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae hD,
      eLpNorm_cellZeroExt_cToPlane d m hGm]
  -- real and imaginary parts
  set G₁ : ℝ × ℝ → ℂ := fun y => (((g y).re - u n y : ℝ) : ℂ) with hG₁def
  set G₂ : ℝ × ℝ → ℂ := fun y => Complex.I * (((g y).im - v n y : ℝ) : ℂ) with hG₂def
  have hGsplit : G = G₁ + G₂ := by
    funext y
    apply Complex.ext <;> simp [hGdef, hG₁def, hG₂def]
  have hm1 : AEStronglyMeasurable G₁ (B0579.cellMeasure d m) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hRe.1.sub (hu n).continuous.aestronglyMeasurable)
  have hm2 : AEStronglyMeasurable G₂ (B0579.cellMeasure d m) :=
    aestronglyMeasurable_const.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hIm.1.sub (hv n).continuous.aestronglyMeasurable))
  have he1 : eLpNorm G₁ 2 (B0579.cellMeasure d m) =
      eLpNorm (u n - fun y => (g y).re) 2 (B0579.cellMeasure d m) := by
    rw [eLpNorm_sub_comm]
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
      show ‖(((g y).re - u n y : ℝ) : ℂ)‖ = ‖(g y).re - u n y‖
      exact Complex.norm_real _)
  have he2 : eLpNorm G₂ 2 (B0579.cellMeasure d m) =
      eLpNorm (v n - fun y => (g y).im) 2 (B0579.cellMeasure d m) := by
    rw [eLpNorm_sub_comm]
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
      show ‖Complex.I * (((g y).im - v n y : ℝ) : ℂ)‖ = ‖(g y).im - v n y‖
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real])
  have hlt : ENNReal.ofReal ‖W - (testW m (hu n) + Complex.I • testW m (hv n))‖ <
      ENNReal.ofReal δ := by
    rw [hnorm]
    unfold xNorm
    calc eLpNorm G 2 (B0579.cellMeasure d m)
        ≤ eLpNorm G₁ 2 (B0579.cellMeasure d m) + eLpNorm G₂ 2 (B0579.cellMeasure d m) := by
          rw [hGsplit]; exact eLpNorm_add_le hm1 hm2 (by norm_num)
      _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
          rw [he1, he2]; exact ENNReal.add_lt_add hn1 hn2
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 hlt

end RelBlockDiagonalSub

end UnforcedLeray.Short.IIIa
