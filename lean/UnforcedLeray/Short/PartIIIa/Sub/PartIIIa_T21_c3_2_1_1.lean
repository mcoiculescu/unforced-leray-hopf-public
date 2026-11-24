import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1
import UnforcedLeray.Lib.PlanarSectorsB.DilationPlane

/-!
# Part III-a, sub-infrastructure for `PartIII-a:T21/c3/2/1/1` (`BlockPropagator.lean`, SP 2926-2982)

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925,
2937-2945, and 2962-2982 (`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

## Mathematical content and proved infrastructure

This module develops the operator-norm and Hilbert-space infrastructure for
`DampedComplBlockPropagator κ` (`PartIII-a:T21/c3/2/1/1`) on `Planar.L2w m`:

1. **Ambient `Planar.L2w m` vs. cylinder `B0579.cellMeasure d m` isometric bridge (SP 2937-2940)**:
   * `cToPlane_eq_equiv`, `planeToC_eq_equiv_symm`, `measurePreserving_cToPlane_volume`,
     `measurePreserving_planeToC_volume`: coordinate identification `ℂ ≃ᵐ ℝ × ℝ`.
   * `jb_cToPlane`, `density_cToPlane`, `measurePreserving_cToPlane_wMeasure`,
     `measurePreserving_planeToC_wMeasure`: measure-preserving equivalence between
     `Planar.wMeasure m` and `volume.withDensity (B0579.density m)`.
   * `eLpNorm_cellZeroExt_cToPlane`, `memLp_cellZeroExt_cToPlane`, `xNorm_planeToC_le_norm`:
     isometric zero-extension `I_z : X_{m, d(z)} → Planar.L2w m` and contractive restriction
     `R_z : Planar.L2w m → X_{m, d(z)}` (`‖I_z V‖_{L2w m} = ‖V‖_{X_{m, d(z)}}`,
     `‖R_z W‖_{X_{m, d(z)}} ≤ ‖W‖_{L2w m}`).

2. **Exterior dilation operator `extDilW` on `Planar.L2w m` (SP 2941-2945)**:
   * `extDilW`: continuous linear realization of the exterior dilation cocycle `S(z, t)` on
     `Planar.L2w m` via `Planar.dilW hm (a := ((d_s / d_t) ^ 2)⁻¹)`.
   * `norm_extDilW_le_cube`, `norm_extDilW_cellLen_le_exp`: operator-norm bounds
     `‖extDilW‖ ≤ (d_s / d_t) ^ 3 ≤ Real.exp ((3 / (2 * b)) * (movingZ ν t - movingZ ν s))`.

3. **Limiting relative transport `planarRelTransportW` and adjoint-strong convergence identity
   (SP 2964-2972)**:
   * `planarRelTransportW_self`, `planarRelTransportW_comp`, `norm_planarRelTransportW_le_one`:
     evolution family laws and contraction bound on `Planar.L2w m`.
   * `norm_adjoint_sub_sq_eq`, `norm_adjoint_sub_sq_le_of_coisometry`: the Hilbert-space identity
     and inequality `‖(F† - T†) f‖² ≤ (‖F‖² - 1)‖f‖² + 2‖f‖‖F (T† f) - f‖` used in SP 2969-2972
     to deduce strong convergence of `F_rel(t, s)†` from strong convergence of `F_rel(t, s)` and
     `limsup ‖F_rel(t, s)‖ ≤ 1`.

4. **Analytical sub-leaves and conditional assembly `dampedComplBlockPropagator_of`**:
   * `PeriodizedRelFreeBlockExists` (`PartIII-a:T21/c3/2/1/1/1`): existence and uniform sub-block /
     full-block bounds for the periodized relative free block evolution `F_rel`
     (`IsPeriodizedRelFreeBlockEvol`).
   * `DampedComplBlockIntAndDuhamel` (`PartIII-a:T21/c3/2/1/1/2`): existence of the damped
     complement interaction `A_rel` (`IsDampedComplBlockInt`) and perturbed Duhamel evolution
     `U_rel` satisfying the Compact Duhamel full-block bound
     `‖U_rel B 0‖ ≤ C₀ * e^{-h B} + ‖F_rel B 0‖ + δ_gap`.
   * `dampedComplBlockPropagator_of`: combines the sub-leaves to establish
     `DampedComplBlockPropagator κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorSub

/-! ## 1. Ambient `Planar.L2w m` vs. cylinder `B0579.cellMeasure d m` isometric bridge -/

theorem cToPlane_eq_equiv : (cToPlane : ℂ → ℝ × ℝ) = ⇑Complex.measurableEquivRealProd :=
  rfl

theorem planeToC_eq_equiv_symm :
    (planeToC : ℝ × ℝ → ℂ) = ⇑Complex.measurableEquivRealProd.symm :=
  rfl

theorem measurable_cToPlane : Measurable cToPlane :=
  Complex.measurableEquivRealProd.measurable

theorem measurable_planeToC : Measurable planeToC :=
  Complex.measurableEquivRealProd.symm.measurable

theorem measurePreserving_cToPlane_volume :
    MeasurePreserving cToPlane (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) :=
  Complex.volume_preserving_equiv_real_prod

theorem measurePreserving_planeToC_volume :
    MeasurePreserving planeToC (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
  Complex.volume_preserving_equiv_real_prod.symm

/-- `B0579.jb (cToPlane z)` coincides with `1 + ‖z‖ ^ 2`. -/
theorem jb_cToPlane (z : ℂ) : B0579.jb (cToPlane z) = 1 + ‖z‖ ^ 2 := by
  simp only [B0579.jb, cToPlane, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The cylinder weight `B0579.density m (cToPlane z)` coincides with `Planar.wDensity m z`. -/
theorem density_cToPlane (m : ℝ) (z : ℂ) :
    (B0579.density m (cToPlane z) : ℝ≥0∞) = Planar.wDensity m z := by
  rw [← ENNReal.ofReal_coe_nnreal, B0579.coe_density, jb_cToPlane, Planar.wDensity]

/-- The planar weight `Planar.wDensity m (planeToC y)` coincides with `B0579.density m y`. -/
theorem wDensity_planeToC (m : ℝ) (y : ℝ × ℝ) :
    Planar.wDensity m (planeToC y) = (B0579.density m y : ℝ≥0∞) := by
  rw [← density_cToPlane m (planeToC y), cToPlane_planeToC]

/-- `cToPlane` is measure-preserving from `Planar.wMeasure m` to
`volume.withDensity (B0579.density m)`. -/
theorem measurePreserving_cToPlane_wMeasure (m : ℝ) :
    MeasurePreserving cToPlane (Planar.wMeasure m)
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) := by
  refine ⟨measurable_cToPlane, ?_⟩
  ext s hs
  change Measure.map cToPlane (volume.withDensity (Planar.wDensity m)) s =
    (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) s
  rw [Measure.map_apply measurable_cToPlane hs,
    withDensity_apply _ (measurable_cToPlane hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_cToPlane hs), ← lintegral_indicator hs]
  have hind : ∀ z : ℂ,
      (cToPlane ⁻¹' s).indicator (Planar.wDensity m) z =
        s.indicator (fun y => (B0579.density m y : ℝ≥0∞)) (cToPlane z) := by
    intro z
    by_cases hz : cToPlane z ∈ s
    · rw [indicator_of_mem (show z ∈ cToPlane ⁻¹' s from hz), indicator_of_mem hz,
        density_cToPlane]
    · rw [indicator_of_notMem (show z ∉ cToPlane ⁻¹' s from hz), indicator_of_notMem hz]
  simp_rw [hind]
  exact measurePreserving_cToPlane_volume.lintegral_comp
    ((B0579.measurable_density m).coe_nnreal_ennreal.indicator hs)

/-- `planeToC` is measure-preserving from `volume.withDensity (B0579.density m)` to
`Planar.wMeasure m`. -/
theorem measurePreserving_planeToC_wMeasure (m : ℝ) :
    MeasurePreserving planeToC
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞))
      (Planar.wMeasure m) := by
  refine ⟨measurable_planeToC, ?_⟩
  ext s hs
  change Measure.map planeToC (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) s =
    (volume.withDensity (Planar.wDensity m)) s
  rw [Measure.map_apply measurable_planeToC hs,
    withDensity_apply _ (measurable_planeToC hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_planeToC hs), ← lintegral_indicator hs]
  have hind : ∀ y : ℝ × ℝ,
      (planeToC ⁻¹' s).indicator (fun x => (B0579.density m x : ℝ≥0∞)) y =
        s.indicator (Planar.wDensity m) (planeToC y) := by
    intro y
    by_cases hy : planeToC y ∈ s
    · rw [indicator_of_mem (show y ∈ planeToC ⁻¹' s from hy), indicator_of_mem hy,
        wDensity_planeToC]
    · rw [indicator_of_notMem (show y ∉ planeToC ⁻¹' s from hy), indicator_of_notMem hy]
  simp_rw [hind]
  exact measurePreserving_planeToC_volume.lintegral_comp
    ((Planar.measurable_wDensity m).indicator hs)

/-- Isometric property of `cellZeroExt d`: for any strongly measurable `V` on `B0579.cell d`,
the ambient `Planar.wMeasure m` `L²`-norm of `z ↦ cellZeroExt d V (cToPlane z)` equals
`xNorm d m V` (SP 2938-2940). -/
theorem eLpNorm_cellZeroExt_cToPlane (d m : ℝ) {V : ℝ × ℝ → ℂ}
    (hV : AEStronglyMeasurable V (B0579.cellMeasure d m)) :
    eLpNorm (fun z : ℂ => cellZeroExt d V (cToPlane z)) 2 (Planar.wMeasure m) =
      xNorm d m V := by
  have hV_ind : AEStronglyMeasurable (cellZeroExt d V)
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) := by
    unfold cellZeroExt
    rw [aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell d),
      restrict_withDensity (B0579.measurableSet_cell d)]
    exact hV
  change eLpNorm (cellZeroExt d V ∘ cToPlane) 2 (Planar.wMeasure m) = xNorm d m V
  rw [eLpNorm_comp_measurePreserving hV_ind (measurePreserving_cToPlane_wMeasure m)]
  unfold xNorm B0579.cellMeasure cellZeroExt
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (B0579.measurableSet_cell d),
    restrict_withDensity (B0579.measurableSet_cell d)]

/-- If `V ∈ L²(B0579.cellMeasure d m)`, then its zero-extension `z ↦ cellZeroExt d V (cToPlane z)`
belongs to `MemLp · 2 (Planar.wMeasure m)` (SP 2938-2940). -/
theorem memLp_cellZeroExt_cToPlane (d m : ℝ) {V : ℝ × ℝ → ℂ}
    (hV : MemLp V 2 (B0579.cellMeasure d m)) :
    MemLp (fun z : ℂ => cellZeroExt d V (cToPlane z)) 2 (Planar.wMeasure m) := by
  have hV_ind : MemLp (cellZeroExt d V) 2
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) := by
    unfold cellZeroExt
    rw [memLp_indicator_iff_restrict (B0579.measurableSet_cell d),
      restrict_withDensity (B0579.measurableSet_cell d)]
    exact hV
  exact hV_ind.comp_measurePreserving (measurePreserving_cToPlane_wMeasure m)

/-- Contractive property of cell restriction `R_d`: for every `W : Planar.L2w m`,
`xNorm d m (fun y => W (planeToC y)) ≤ ENNReal.ofReal ‖W‖` (SP 2939-2940). -/
theorem xNorm_planeToC_le_norm (d m : ℝ) (W : Planar.L2w m) :
    xNorm d m (fun y => (W : ℂ → ℂ) (planeToC y)) ≤ ENNReal.ofReal ‖W‖ := by
  unfold xNorm B0579.cellMeasure
  rw [← restrict_withDensity (B0579.measurableSet_cell d)]
  have hle : eLpNorm (fun y => (W : ℂ → ℂ) (planeToC y)) 2
      ((volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)).restrict (B0579.cell d)) ≤
      eLpNorm (fun y => (W : ℂ → ℂ) (planeToC y)) 2
        (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) :=
    eLpNorm_restrict_le _ _ _ _
  have heq : eLpNorm (fun y => (W : ℂ → ℂ) (planeToC y)) 2
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) =
      eLpNorm (W : ℂ → ℂ) 2 (Planar.wMeasure m) :=
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable W)
      (measurePreserving_planeToC_wMeasure m)
  have hnorm : eLpNorm (W : ℂ → ℂ) 2 (Planar.wMeasure m) = ENNReal.ofReal ‖W‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top W)]
  exact hle.trans_eq (heq.trans hnorm)

/-! ## 2. Exterior dilation operator `extDilW` on `Planar.L2w m` and block growth bound (SP 2941-2945) -/

/-- Continuous linear realization on `Planar.L2w m` of the dilation `y ↦ (d_s / d_t) y` with
prefactor `(d_s / d_t) ^ 4` via `Planar.dilW hm` at parameter `a = ((d_s / d_t) ^ 2)⁻¹`
(SP 2941-2945). -/
def extDilW {m : ℝ} (hm : 1 < m) {d_s d_t : ℝ} (hds : 0 < d_s) (hdt : 0 < d_t) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  Planar.dilW hm (inv_pos.2 (sq_pos_of_pos (div_pos hds hdt)))

/-- When `0 < d_t ≤ d_s`, the exterior dilation operator `extDilW hm hds hdt` on `Planar.L2w m`
has operator norm bounded by `(d_s / d_t) ^ 3` (SP 2944). -/
theorem norm_extDilW_le_cube {m : ℝ} (hm : 1 < m) {d_s d_t : ℝ}
    (hds : 0 < d_s) (hdt : 0 < d_t) (hle : d_t ≤ d_s) :
    ‖extDilW hm hds hdt‖ ≤ (d_s / d_t) ^ 3 := by
  unfold extDilW
  have h1 : 1 ≤ d_s / d_t := (one_le_div hdt).2 hle
  have hsq : 1 ≤ (d_s / d_t) ^ 2 := by nlinarith
  have hbd := Planar.norm_dilW_inv_le_of_one_le (M := m) hm hsq
  have hrpow : ((d_s / d_t) ^ 2) ^ (3 / 2 : ℝ) = (d_s / d_t) ^ 3 := by
    have hpos : 0 ≤ d_s / d_t := (div_pos hds hdt).le
    rw [← Real.rpow_natCast (d_s / d_t) 2, ← Real.rpow_mul hpos]
    norm_num
  exact hbd.trans_eq hrpow

/-- Over any sub-interval `0 ≤ s ≤ t` with `0 < b ≤ clockTheta ν t`, the exterior dilation operator
between `d_s = cellLen c (clockA ν s)` and `d_t = cellLen c (clockA ν t)` satisfies
`‖extDilW‖ ≤ Real.exp ((3 / (2 * b)) * (movingZ ν t - movingZ ν s))` (SP 2944-2945). -/
theorem norm_extDilW_cellLen_le_exp {m c ν s t b : ℝ}
    (hm : 1 < m) (hc : 0 < c) (hν : 0 < ν) (hs : 0 ≤ s) (hst : s ≤ t)
    (hb0 : 0 < b) (hbt : b ≤ clockTheta ν t) :
    have hds : 0 < cellLen c (clockA ν s) :=
      div_pos hc (Real.sqrt_pos.2 (by unfold clockA; positivity))
    have hdt : 0 < cellLen c (clockA ν t) :=
      div_pos hc (Real.sqrt_pos.2 (by have ht : 0 ≤ t := hs.trans hst; unfold clockA; positivity))
    ‖extDilW hm hds hdt‖ ≤ Real.exp ((3 / (2 * b)) * (movingZ ν t - movingZ ν s)) := by
  intro hds hdt
  have hle : cellLen c (clockA ν t) ≤ cellLen c (clockA ν s) :=
    (one_le_div hdt).1 (one_le_cellLen_div_cellLen hc.ne' hν hs hst)
  exact (norm_extDilW_le_cube hm hds hdt hle).trans
    (cellLen_div_cellLen_cube_le_exp hc.ne' hν hs hst hb0 hbt)

/-! ## 3. Relative planar transport `planarRelTransportW` and adjoint-strong convergence identity -/

/-- Identity property `planarRelTransportW P m t t = 1` on `Planar.L2w m`. -/
@[simp] theorem planarRelTransportW_self (P : PlanarData) (m t : ℝ) :
    planarRelTransportW P m t t = 1 := by
  unfold planarRelTransportW
  rw [sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Planar.transportGroupW_zero,
    one_smul]

/-- Evolution-group composition law for `planarRelTransportW P m`:
`planarRelTransportW P m t r ∘L planarRelTransportW P m r s = planarRelTransportW P m t s`. -/
theorem planarRelTransportW_comp (P : PlanarData) (m r s t : ℝ) :
    planarRelTransportW P m t r ∘L planarRelTransportW P m r s =
      planarRelTransportW P m t s := by
  unfold planarRelTransportW
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
    ← Complex.exp_add, ← Planar.transportGroupW_add]
  have h1 : -P.eigenvalue * ((t - r : ℝ) : ℂ) + -P.eigenvalue * ((r - s : ℝ) : ℂ) =
      -P.eigenvalue * ((t - s : ℝ) : ℂ) := by
    push_cast
    ring
  have h2 : (t - r) + (r - s) = t - s := by ring
  rw [h1, h2]

/-- Contraction bound `‖planarRelTransportW P m t s‖ ≤ 1` when `0 ≤ P.eigenvalue.re` and `s ≤ t`
(SP 2968). -/
theorem norm_planarRelTransportW_le_one (P : PlanarData) (m : ℝ) {s t : ℝ}
    (hre : 0 ≤ P.eigenvalue.re) (hst : s ≤ t) :
    ‖planarRelTransportW P m t s‖ ≤ 1 := by
  refine (norm_planarRelTransportW_le P m t s).trans ?_
  rw [Real.exp_le_one_iff]
  have hsub : 0 ≤ t - s := sub_nonneg.2 hst
  nlinarith

/-- **Hilbert-space adjoint-strong convergence identity** (SP 2969-2970):
For bounded operators `F, T : H →L[ℂ] H` on a complex Hilbert space `H` and any `f : H`,
`‖(F† - T†) f‖ ^ 2 = ‖F† f‖ ^ 2 - 2 * RCLike.re ⟪f, F (T† f)⟫_ℂ + ‖T† f‖ ^ 2`. -/
theorem norm_adjoint_sub_sq_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F T : H →L[ℂ] H) (f : H) :
    ‖(ContinuousLinearMap.adjoint F - ContinuousLinearMap.adjoint T) f‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint F f‖ ^ 2 -
        2 * RCLike.re ⟪f, F (ContinuousLinearMap.adjoint T f)⟫_ℂ +
        ‖ContinuousLinearMap.adjoint T f‖ ^ 2 := by
  rw [sub_apply, norm_sub_sq (𝕜 := ℂ)]
  have hadj : ⟪ContinuousLinearMap.adjoint F f, ContinuousLinearMap.adjoint T f⟫_ℂ =
      ⟪f, F (ContinuousLinearMap.adjoint T f)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left F (ContinuousLinearMap.adjoint T f) f
  rw [hadj]

/-- **Hilbert-space adjoint-strong convergence inequality for contractions/coisometries**
(SP 2969-2972): if `T (T† f) = f` and `‖T† f‖ ≤ ‖f‖`, then
`‖(F† - T†) f‖ ^ 2 ≤ (‖F‖ ^ 2 - 1) * ‖f‖ ^ 2 + 2 * ‖f‖ * ‖F (T† f) - f‖`. -/
theorem norm_adjoint_sub_sq_le_of_coisometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F T : H →L[ℂ] H) (f : H)
    (_hco : T (ContinuousLinearMap.adjoint T f) = f)
    (hT_le : ‖ContinuousLinearMap.adjoint T f‖ ≤ ‖f‖) :
    ‖(ContinuousLinearMap.adjoint F - ContinuousLinearMap.adjoint T) f‖ ^ 2 ≤
      (‖F‖ ^ 2 - 1) * ‖f‖ ^ 2 + 2 * ‖f‖ * ‖F (ContinuousLinearMap.adjoint T f) - f‖ := by
  rw [norm_adjoint_sub_sq_eq]
  have hF_adj : ‖ContinuousLinearMap.adjoint F f‖ ^ 2 ≤ ‖F‖ ^ 2 * ‖f‖ ^ 2 := by
    have h1 : ‖ContinuousLinearMap.adjoint F f‖ ≤ ‖F‖ * ‖f‖ := by
      simpa [ContinuousLinearMap.adjoint.norm_map] using
        (ContinuousLinearMap.adjoint F).le_opNorm f
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint F f), norm_nonneg F, norm_nonneg f]
  have hT_sq : ‖ContinuousLinearMap.adjoint T f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint T f), norm_nonneg f]
  have hinner_split :
      ⟪f, F (ContinuousLinearMap.adjoint T f)⟫_ℂ =
        ⟪f, f⟫_ℂ + ⟪f, F (ContinuousLinearMap.adjoint T f) - f⟫_ℂ := by
    rw [← inner_add_right, add_sub_cancel]
  have hre_self : RCLike.re ⟪f, f⟫_ℂ = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hre_sub : -RCLike.re ⟪f, F (ContinuousLinearMap.adjoint T f) - f⟫_ℂ ≤
      ‖f‖ * ‖F (ContinuousLinearMap.adjoint T f) - f‖ := by
    have h1 : -RCLike.re ⟪f, F (ContinuousLinearMap.adjoint T f) - f⟫_ℂ ≤
        ‖⟪f, F (ContinuousLinearMap.adjoint T f) - f⟫_ℂ‖ := by
      have hle := RCLike.re_le_norm (-⟪f, F (ContinuousLinearMap.adjoint T f) - f⟫_ℂ)
      simpa only [map_neg, norm_neg] using hle
    exact h1.trans (norm_inner_le_norm f _)
  have hre_eq : RCLike.re ⟪f, F (ContinuousLinearMap.adjoint T f)⟫_ℂ =
      ‖f‖ ^ 2 + RCLike.re ⟪f, F (ContinuousLinearMap.adjoint T f) - f⟫_ℂ := by
    rw [hinner_split, map_add, hre_self]
  linarith

/-! ## 4. Analytical sub-leaves and conditional assembly for `DampedComplBlockPropagator` -/

/-- **Sub-leaf 1a (`PeriodizedRelFreeBlockExists`, `PartIII-a:T21/c3/2/1/1/1`, SP 2937-2972)**:
Given the relative free moving energy bound `α_free` on blocks of moving length `B` and any gap
tolerance `δ_free > 0`, there exist a uniform sub-block bound `M_free ≥ 0` and thresholds
`b_free ≥ 1`, `ν_free > 0` such that on any block `[t₁, t₂]` of moving length `B` with
`b ≥ b_free`, `ν ∈ (0, ν_free]`, and `b ≤ clockTheta ν t₂`, there exists a periodized relative free
block evolution `F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m` satisfying
`IsPeriodizedRelFreeBlockEvol`, `‖F_rel τ σ‖ ≤ M_free` for `σ ≤ τ ≤ σ + B`, and
`‖F_rel B 0‖ ≤ α_free + δ_free`. -/
def PeriodizedRelFreeBlockExists : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ B α_free δ_free : ℝ, 0 < B → 0 < α_free → 0 < δ_free →
    (∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
      ∀ ν ∈ Ioc 0 ν_f, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (JscaleInv (clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal α_free *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                      (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ))))) →
    ∃ M_free b_free : ℝ, 0 ≤ M_free ∧ 1 ≤ b_free ∧
      ∀ b : ℝ, b_free ≤ b →
        ∃ ν_free : ℝ, 0 < ν_free ∧
          ∀ ν ∈ Ioc 0 ν_free, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
              movingZ ν t₂ - movingZ ν t₁ = B →
              ∃ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
                IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
                (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) ∧
                ‖F_rel B 0‖ ≤ α_free + δ_free

/-- **Sub-leaf 1b (`DampedComplBlockIntAndDuhamel`, `PartIII-a:T21/c3/2/1/1/2`, SP 2920-2925, 2973-2982)**:
Given the planar seed-complement decay `(C₀, h)` and the existence of periodized relative free
block evolutions (`PeriodizedRelFreeBlockExists`), for any gap tolerance `δ_gap > 0`, there exist a
uniform interaction bound `K_A ≥ 0` and thresholds `b_prop ≥ 1`, `ν_prop > 0` such that the damped
complement interaction `A_rel` (`IsDampedComplBlockInt`) and the perturbed Duhamel evolution `U_rel`
satisfy `‖A_rel τ‖ ≤ K_A` and the Compact Duhamel full-block bound
`‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + ‖F_rel B 0‖ + δ_gap` (via `compact_duhamel_opNorm_bound`). -/
def DampedComplBlockIntAndDuhamel (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B M_free b_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 ≤ M_free → 1 ≤ b_free → 0 < δ_gap →
    (∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h_prof) ℓ ∧
      (∀ y, κ.e 0 y = PartI.seedPlanar h_prof (planeToC y)) ∧
      (∀ y, κ.e 1 y = conj (PartI.seedPlanar h_prof (planeToC y))) ∧
      (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, κ.lamP 0 y * f (planeToC y) =
          PartI.seedEll h_prof (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, κ.lamP 1 y * f (planeToC y) =
          conj (PartI.seedEll h_prof
            (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) ∧
      (∀ (hm1 : 1 < m) (t : ℝ), 0 ≤ t → ∀ f : B0008.XjM 0 m,
        ∃ (u : Planar.L2w m) (g : B0008.XjM 0 m),
          (⇑u =ᵐ[volume] fun y =>
            PartI.xValue f y - PartI.seedProjFun h_prof (PartI.xValue f) y) ∧
          PartI.xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hm1 t u) ∧
          Real.exp (-P.eigenvalue.re * t) * ‖g‖ ≤ C₀ * Real.exp (-h * t) * ‖f‖)) →
    (∀ b : ℝ, b_free ≤ b →
      ∃ ν_free : ℝ, 0 < ν_free ∧
        ∀ ν ∈ Ioc 0 ν_free, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ = B →
            ∃ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
              IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
              (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free)) →
    ∃ K_A b_prop : ℝ, 0 ≤ K_A ∧ b_free ≤ b_prop ∧
      ∀ b : ℝ, b_prop ≤ b →
        ∃ ν_prop : ℝ, 0 < ν_prop ∧
          ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
                  IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
                  (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) →
                  ∃ (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                    (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
                    IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                    UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
                      (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) ∧
                    (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                    ‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + ‖F_rel B 0‖ + δ_gap

/-- **Conditional assembly of `DampedComplBlockPropagator κ` (`PartIII-a:T21/c3/2/1/1`)**:
Combines `PeriodizedRelFreeBlockExists` and `DampedComplBlockIntAndDuhamel κ` to establish
`DampedComplBlockPropagator κ` with zero sorry. -/
theorem dampedComplBlockPropagator_of (κ : PlanarFrameKernels)
    (hFree : PeriodizedRelFreeBlockExists)
    (hDuh : DampedComplBlockIntAndDuhamel κ) :
    DampedComplBlockPropagator κ := by
  intro hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  have hδ2 : 0 < δ_gap / 2 := half_pos hδ
  obtain ⟨M_free, b_free, hM_free, hb_free, hF_b⟩ :=
    hFree P hP m hm B α_free (δ_gap / 2) hB hα hδ2 hFreeRel
  have hF_b_weak : ∀ b : ℝ, b_free ≤ b →
      ∃ ν_free : ℝ, 0 < ν_free ∧
        ∀ ν ∈ Ioc 0 ν_free, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ = B →
            ∃ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
              IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
              (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) := by
    intro b hb
    obtain ⟨ν_free, hν_free, hF_ν⟩ := hF_b b hb
    refine ⟨ν_free, hν_free, fun ν hν tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq => ?_⟩
    obtain ⟨F_rel, hF_rel, hF_sub, _⟩ := hF_ν ν hν tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    exact ⟨F_rel, hF_rel, hF_sub⟩
  obtain ⟨K_A, b_prop, hK_A, hb_prop_le, hU_b⟩ :=
    hDuh hκ P hP m hm K C₀ h B M_free b_free (δ_gap / 2)
      hC₀ hh hh_le hB hM_free hb_free hδ2 hSeedDecay hF_b_weak
  refine ⟨M_free, K_A, b_prop, hM_free, hK_A, hb_free.trans hb_prop_le, fun b hb => ?_⟩
  obtain ⟨ν_free, hν_free, hF_ν⟩ := hF_b b (hb_prop_le.trans hb)
  obtain ⟨ν_uh, hν_uh, hU_ν⟩ := hU_b b hb
  refine ⟨min ν_free ν_uh, lt_min hν_free hν_uh,
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq => ?_⟩
  have hν_f : ν ∈ Ioc 0 ν_free := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_u : ν ∈ Ioc 0 ν_uh := ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  obtain ⟨F_rel, hF_rel, hF_sub, hF_B0⟩ := hF_ν ν hν_f tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
  obtain ⟨A_rel, U_rel, hA_rel, hDuh_rel, hA_bdd, hU_B0⟩ :=
    hU_ν ν hν_u hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq F_rel hF_rel hF_sub
  refine ⟨F_rel, A_rel, U_rel, hF_rel, hA_rel, hDuh_rel, hF_sub, hA_bdd, ?_⟩
  linarith

end BlockPropagatorSub

end UnforcedLeray.Short.IIIa
