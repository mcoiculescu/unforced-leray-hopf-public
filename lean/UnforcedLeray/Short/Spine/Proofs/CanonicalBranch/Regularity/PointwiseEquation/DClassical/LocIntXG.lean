import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3

/-!
# Leaf 6 proof: `v w` is locally integrable on `(0, ∞)` for `v ∈ X_G` (task `Spine:SP-CAN/4/5/3`)

Proves `LocIntXGMulW` (`Sub/SP_CAN4_5_3.lean`). For a compact `K ⊆ (0, ∞)`:

* `xGMeasure.restrict K = (volume.restrict K).withDensity xGDensity` (the density measure
  restricted to `K ⊆ (0, ∞)`);
* `xGMeasure K < ∞`, since the density is continuous and `K` is compact;
* `v ∈ L²(xGMeasure)` gives `v ∈ L¹(xGMeasure.restrict K)`, because the restricted measure is
  finite;
* `integrable_withDensity_iff_integrable_smul` turns this into integrability of
  `xGDensity • v` for `volume.restrict K`, and on `K` this is `v * wC` (`xGDensity r = wDens r`
  for `r > 0`).

Source of record: `the November 2 reference manuscript` lines 1086 and 1134-1140.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

/-- **Leaf 6, proof.** `v w` is locally integrable on `(0, ∞)` for every `v ∈ X_G`. -/
theorem locIntXGMulW_proof : UnforcedLeray.Short.Spine.LocIntXGMulW := by
  intro v
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hKsub hKc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  -- The density `xGDensity` is continuous (it is `toNNReal` of a continuous function).
  have hcont : Continuous xGDensity := by
    have h : xGDensity = fun r : ℝ => Real.toNNReal (4 * Real.pi * Real.exp (r ^ 2 / 4) * r) :=
      funext xGDensity_eq
    rw [h]
    exact continuous_real_toNNReal.comp
      (by fun_prop : Continuous fun r : ℝ => 4 * Real.pi * Real.exp (r ^ 2 / 4) * r)
  -- Step 1: the restriction of `xGMeasure` to `K` is the density measure on `K`.
  have hres : xGMeasure.restrict K =
      (volume.restrict K).withDensity (fun r => ((xGDensity r : NNReal) : ENNReal)) := by
    rw [xGMeasure, restrict_withDensity hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.mpr hKsub]
  -- Step 2: `xGMeasure K` is finite, since `K` is compact and the density is continuous.
  have hKvol : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  have hfin : xGMeasure K ≠ ⊤ := by
    rw [xGMeasure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.mpr hKsub]
    exact (setLIntegral_lt_top_of_isCompact hKvol hKc hcont).ne
  have : IsFiniteMeasure (xGMeasure.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hfin⟩
  -- Step 3: `v` is integrable for the finite restricted measure (`L² ⊆ L¹` on finite measures).
  have hv : Integrable (v : ℝ → ℂ) (xGMeasure.restrict K) :=
    ((Lp.memLp v).restrict K).integrable (by norm_num)
  rw [hres] at hv
  -- Step 4: transfer to Lebesgue measure on `K`, with the density as a scalar factor.
  have hw : IntegrableOn (fun r : ℝ => xGDensity r • (v : ℝ → ℂ) r) K volume :=
    (integrable_withDensity_iff_integrable_smul measurable_xGDensity).mp hv
  refine hw.congr_fun (fun r hr => ?_) hKm
  have hr0 : (0 : ℝ) < r := hKsub hr
  have hnn : (0 : ℝ) ≤ 4 * Real.pi * Real.exp (r ^ 2 / 4) * r := (wDens_pos hr0).le
  have hc : ((xGDensity r : NNReal) : ℝ) = wDens r := by
    rw [xGDensity_eq]
    exact Real.coe_toNNReal _ hnn
  show xGDensity r • (v : ℝ → ℂ) r = (v : ℝ → ℂ) r * wC r
  rw [NNReal.smul_def, Complex.real_smul, hc, wC, mul_comm]

end UnforcedLeray.Short.Spine
