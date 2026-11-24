import UnforcedLeray.Units.B0005.Bridge.Commute

/-!
# B0005 bridge: the interface's periodic graph is the graph `𝒱₂` of the phase model

Blueprint unit B0005 (`paper/main.tex` 136–147) is used twice in the Lean development: in the
Bochner model of decision D2 (`PhaseSpace.Yq`, `PhaseSpace.solenoidalFreeGraph`; consumers
B0440, B0411–B0447) and in the interface layer `Blueprint/Package.lean` (`IsY2Div`,
`InPeriodicGraph`; consumers B1007, B1009, B1034). This file proves that the two encodings
agree for real fields:

* `isY2Div_iff`: `Blueprint.IsY2Div 𝒯 f ↔ IsY2 𝒯 f ∧ toY 𝒯 f ∈ 𝒴_{2,div}`;
* `inPeriodicGraph_iff`: for `h ≠ 0`,
  `Blueprint.InPeriodicGraph 𝒯 b a d ↔ IsY2 b ∧ IsY2 a ∧ IsY2 d ∧
     (toY b, h · toY a, toY d) ∈ 𝒱₂ = V 𝒯 2 h`;
  in particular `hΔb` and `𝒯₀b` are automatically solenoidal (`Commute.lean`), as
  `loc:eq:graph` (tex 173–179) states and B0005's `𝒱_q` (tex 141) does not require;
* `norm_toY_sq`: `‖toY 𝒯 f‖² = 𝒯⁻¹ ∫_{(0,𝒯]×ℝ³} |f|²`, the norm `L²([0,𝒯], dτ/𝒯; L²)` of
  tex 138; `toY_eq_zero_iff`: `toY 𝒯 f = 0` iff `f = 0` a.e. on the period slab (the
  interface's `bstar_nonzero`).

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)]

/-- `Blueprint.IsY2Div` is membership of the realized field in `𝒴_{2,div}`. -/
theorem isY2Div_iff {f : ℝ → SpatialField} :
    Blueprint.IsY2Div 𝒯 f ↔ IsY2 𝒯 f ∧ toY 𝒯 f ∈ Ydiv 𝒯 2 := by
  constructor
  · intro hf
    exact ⟨hf.isY2, hf.isY2.isPhaseSolenoidal_of_ae hf.solenoidal⟩
  · rintro ⟨hf, hdiv⟩
    exact ⟨hf.periodic, hf.measurable, hf.memL2, hf.ae_isSolenoidal_of_phase hdiv⟩

/-- **Agreement of the periodic graph** (B0005 tex 141–145 with `loc:eq:graph`, tex 173–179).
For `h ≠ 0` (the manuscript has `h > 0`), the interface predicate
`Blueprint.InPeriodicGraph 𝒯 b a d` (`b, Δb = a, 𝒯₀b = d` in `𝒴_{2,div}`) holds iff the three
real fields are periodic, measurable and square integrable on the period slab and
`(b, hΔb, 𝒯₀b) = (toY b, h · toY a, toY d)` lies in the graph `𝒱₂` of the phase model. -/
theorem inPeriodicGraph_iff {h : ℝ} (hh : h ≠ 0) {b a d : ℝ → SpatialField} :
    Blueprint.InPeriodicGraph 𝒯 b a d ↔
      IsY2 𝒯 b ∧ IsY2 𝒯 a ∧ IsY2 𝒯 d ∧
        (toY 𝒯 b, (h : ℂ) • toY 𝒯 a, toY 𝒯 d) ∈ V 𝒯 2 h := by
  constructor
  · intro G
    have hb := G.value.isY2
    have ha := G.laplacian.isY2
    have hd := G.drift.isY2
    refine ⟨hb, ha, hd, mem_V_iff.mpr ⟨hb.isPhaseSolenoidal_of_ae G.value.solenoidal, ?_, ?_⟩⟩
    · exact (hasHLap_iff hh).mpr ((hb.laplacianPairing_iff ha).mp G.laplacian_weak)
    · exact (hb.driftPairing_iff hd).mp G.drift_weak
  · rintro ⟨hb, ha, hd, hV⟩
    obtain ⟨hdiv, hlap, hT0⟩ := mem_V_iff.mp hV
    have hlap' : HasPhaseOp lapT (toY 𝒯 b) (toY 𝒯 a) := (hasHLap_iff hh).mp hlap
    exact
      { value := ⟨hb.periodic, hb.measurable, hb.memL2, hb.ae_isSolenoidal_of_phase hdiv⟩
        laplacian := ⟨ha.periodic, ha.measurable, ha.memL2,
          ha.ae_isSolenoidal_of_phase (IsPhaseSolenoidal.of_hasPhaseOp_lapT hdiv hlap')⟩
        drift := ⟨hd.periodic, hd.measurable, hd.memL2,
          hd.ae_isSolenoidal_of_phase (IsPhaseSolenoidal.of_hasT0 hdiv hT0)⟩
        laplacian_weak := (hb.laplacianPairing_iff ha).mpr hlap'
        drift_weak := (hb.driftPairing_iff hd).mpr hT0 }

/-! ### Norms -/

theorem norm_sq_Lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    (g : Lp E 2 μ) : ‖g‖ ^ 2 = ∫ y, ‖g y‖ ^ 2 ∂μ := by
  have hI : 0 ≤ ∫ y, ‖g y‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun _ => by positivity
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    (Lp.memLp g), ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

/-- **Norm agreement** (tex 138): `‖toY 𝒯 f‖² = 𝒯⁻¹ ∫_{(0,𝒯] × ℝ³} |f|²`. -/
theorem IsY2.norm_toY_sq {f : ℝ → SpatialField} (hf : IsY2 𝒯 f) :
    ‖toY 𝒯 f‖ ^ 2 =
      𝒯⁻¹ * ∫ z in Blueprint.periodSlab 𝒯, ‖f z.1 z.2‖ ^ 2 := by
  have h1 := norm_rpow_eq (q := 2) ENNReal.ofNat_ne_top (toY 𝒯 f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
  rw [h1]
  congr 1
  have hint : Integrable (fun z : ℝ × Space => ‖f z.1 z.2‖ ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 𝒯)).prod (volume : Measure Space)) := by
    rw [← IsY2.slab_eq]
    have := hf.memL2.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa [Real.rpow_two] using this
  rw [IsY2.slab_eq, integral_prod _ hint]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hf.toY_ae, hf.ae_pathOf_eq hT.out] with t ht ht'
  show ‖toY 𝒯 f (t : AddCircle 𝒯)‖ ^ 2 = ∫ y, ‖f t y‖ ^ 2
  rw [ht, norm_sq_Lp]
  refine integral_congr_ae ?_
  filter_upwards [ht'] with y hy
  rw [hy, jointC, norm_cplxL]

/-- `toY 𝒯 f = 0` iff `f = 0` almost everywhere on the period slab (the interface's
`bstar_nonzero` is `toY 𝒯 b_* ≠ 0`). -/
theorem IsY2.toY_eq_zero_iff {f : ℝ → SpatialField} (hf : IsY2 𝒯 f) :
    toY 𝒯 f = 0 ↔
      (fun z : SpaceTime => f z.1 z.2) =ᵐ[volume.restrict (Blueprint.periodSlab 𝒯)] 0 := by
  have hint : Integrable (fun z : SpaceTime => ‖f z.1 z.2‖ ^ 2)
      (volume.restrict (Blueprint.periodSlab 𝒯)) := by
    have := hf.memL2.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa [Real.rpow_two] using this
  rw [← norm_eq_zero, ← sq_eq_zero_iff (a := ‖toY 𝒯 f‖), hf.norm_toY_sq,
    mul_eq_zero, or_iff_right (inv_ne_zero hT.out.ne'),
    integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint]
  constructor
  · intro h
    filter_upwards [h] with z hz
    simpa using hz
  · intro h
    filter_upwards [h] with z hz
    simp [hz]

end UnforcedLeray.B0005
