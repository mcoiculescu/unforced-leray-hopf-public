import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.JointMeas2

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: the operator on `Planar.L2w m`

At a good age `r` (`GoodAt`), `x ↦ cellZeroExt d(r) (movDampedComplInt κ P tr r x)` is a bounded
`ℂ`-linear operator on `Planar.L2w m` with norm at most `K_A` (SP 2937-2943, 2974-2978).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

open UnforcedLeray.Short.IIIa.CompactDuhamelGapSub UnforcedLeray.Short.IIIa.BlockPropagatorSub

/-- The cylinder representative `y ↦ x(y₁ + i y₂)` of `x ∈ Planar.L2w m`. -/
def cylRep {m : ℝ} (x : Planar.L2w m) : ℝ × ℝ → ℂ := fun y => (x : ℂ → ℂ) (planeToC y)

/-- The ambient representative of the damped complement interaction applied to `x`. -/
def opFun (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) {m : ℝ}
    (x : Planar.L2w m) : ℂ → ℂ :=
  fun z => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (movDampedComplInt κ P tr r (cylRep x)) (cToPlane z)

theorem measurable_cylRep {m : ℝ} (x : Planar.L2w m) : Measurable (cylRep x) :=
  (Lp.stronglyMeasurable x).measurable.comp measurable_planeToC

theorem memLp_cylRep {d m : ℝ} (x : Planar.L2w m) :
    MemLp (cylRep x) 2 (B0579.cellMeasure d m) :=
  ⟨(measurable_cylRep x).aestronglyMeasurable,
    (xNorm_planeToC_le_norm d m x).trans_lt ENNReal.ofReal_lt_top⟩

theorem volume_ac_wMeasure (m : ℝ) : (volume : Measure ℂ) ≪ Planar.wMeasure m := by
  unfold Planar.wMeasure
  refine withDensity_absolutelyContinuous' (by fun_prop) (Eventually.of_forall fun y => ?_)
  have : 0 < (1 + ‖y‖ ^ 2) ^ m := Real.rpow_pos_of_pos (by positivity) m
  simpa using this

/-- An a.e. identity in `Planar.L2w m` transfers to the cylinder representatives on a cell. -/
theorem cylRep_ae_of {m d : ℝ} {f g : ℂ → ℂ} (h : f =ᵐ[Planar.wMeasure m] g) :
    (fun y => f (planeToC y)) =ᵐ[volume.restrict (B0579.cell d)] fun y => g (planeToC y) := by
  have h1 : (fun y => f (planeToC y)) =ᵐ[volume.withDensity
      fun y => (B0579.density m y : ℝ≥0∞)] fun y => g (planeToC y) :=
    (measurePreserving_planeToC_wMeasure m).quasiMeasurePreserving.ae_eq_comp h
  have h2 := ae_restrict_of_ae (s := B0579.cell d) h1
  rw [restrict_withDensity (B0579.measurableSet_cell d)] at h2
  exact (B0579.ac_cellMeasure d m).ae_le h2

/-- An a.e. identity on the cell transfers to the zero-extensions on `ℂ`. -/
theorem cellZeroExt_ae_of {m d : ℝ} {V₁ V₂ : ℝ × ℝ → ℂ}
    (h : V₁ =ᵐ[B0579.cellMeasure d m] V₂) :
    (fun z => cellZeroExt d V₁ (cToPlane z)) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt d V₂ (cToPlane z) := by
  have h1 : cellZeroExt d V₁ =ᵐ[volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)]
      cellZeroExt d V₂ := by
    unfold cellZeroExt
    have h' : V₁ =ᵐ[(volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)).restrict
        (B0579.cell d)] V₂ := by
      rw [restrict_withDensity (B0579.measurableSet_cell d)]
      exact h
    exact (ae_restrict_iff' (B0579.measurableSet_cell d)).1 h' |>.mono fun y hy => by
      by_cases hc : y ∈ B0579.cell d
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc, hy hc]
      · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc]
  exact (measurePreserving_cToPlane_wMeasure m).quasiMeasurePreserving.ae_eq_comp h1

theorem cellZeroExt_add (d : ℝ) (V₁ V₂ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    cellZeroExt d (fun w => V₁ w + V₂ w) y = cellZeroExt d V₁ y + cellZeroExt d V₂ y := by
  unfold cellZeroExt
  by_cases hc : y ∈ B0579.cell d
  · simp [Set.indicator_of_mem hc]
  · simp [Set.indicator_of_notMem hc]

theorem cellZeroExt_smul (d : ℝ) (c : ℂ) (V : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    cellZeroExt d (fun w => c * V w) y = c * cellZeroExt d V y := by
  unfold cellZeroExt
  by_cases hc : y ∈ B0579.cell d
  · simp [Set.indicator_of_mem hc]
  · simp [Set.indicator_of_notMem hc]

theorem exists_op (κ : PlanarFrameKernels) (P : PlanarData) {ν m K_A : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (hK : 0 ≤ K_A)
    (hg : GoodAt κ P m K_A tr r) :
    ∃ T : Planar.L2w m →L[ℂ] Planar.L2w m,
      (∀ x, (T x : ℂ → ℂ) =ᵐ[Planar.wMeasure m] opFun κ P tr r x) ∧ ‖T‖ ≤ K_A := by
  obtain ⟨hd, hbd, hadd⟩ := hg
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  have hmem : ∀ x : Planar.L2w m, MemLp (opFun κ P tr r x) 2 (Planar.wMeasure m) := fun x =>
    memLp_cellZeroExt_cToPlane d m (hbd _ (memLp_cylRep x)).1
  have hnorm : ∀ x : Planar.L2w m, ‖(hmem x).toLp _‖ ≤ K_A * ‖x‖ := by
    intro x
    rw [Lp.norm_toLp]
    have h1 : eLpNorm (opFun κ P tr r x) 2 (Planar.wMeasure m) =
        xNorm d m (movDampedComplInt κ P tr r (cylRep x)) :=
      eLpNorm_cellZeroExt_cToPlane d m (hbd _ (memLp_cylRep x)).1.1
    have h2 : xNorm d m (movDampedComplInt κ P tr r (cylRep x)) ≤
        ENNReal.ofReal (K_A * ‖x‖) := by
      calc xNorm d m (movDampedComplInt κ P tr r (cylRep x))
          ≤ ENNReal.ofReal K_A * xNorm d m (cylRep x) := (hbd _ (memLp_cylRep x)).2
        _ ≤ ENNReal.ofReal K_A * ENNReal.ofReal ‖x‖ := by
            gcongr
            exact xNorm_planeToC_le_norm d m x
        _ = ENNReal.ofReal (K_A * ‖x‖) := (ENNReal.ofReal_mul hK).symm
    rw [h1]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  have hadd' : ∀ x y : Planar.L2w m, opFun κ P tr r (x + y) =ᵐ[Planar.wMeasure m]
      fun z => opFun κ P tr r x z + opFun κ P tr r y z := by
    intro x y
    have hc : cylRep (x + y) =ᵐ[volume.restrict (B0579.cell d)]
        fun w => cylRep x w + cylRep y w :=
      cylRep_ae_of (Lp.coeFn_add x y)
    have hcong := movDampedComplInt_congr κ P tr r hc
    have hsum := hadd (cylRep x) (cylRep y) (memLp_cylRep x) (memLp_cylRep y)
    have h3 := cellZeroExt_ae_of (m := m) (d := d) (hcong ▸ hsum)
    refine h3.trans (Eventually.of_forall fun z => ?_)
    exact cellZeroExt_add d _ _ (cToPlane z)
  have hsmul' : ∀ (c : ℂ) (x : Planar.L2w m), opFun κ P tr r (c • x) =ᵐ[Planar.wMeasure m]
      fun z => c * opFun κ P tr r x z := by
    intro c x
    have hc : cylRep (c • x) =ᵐ[volume.restrict (B0579.cell d)] fun w => c * cylRep x w :=
      cylRep_ae_of (Lp.coeFn_smul c x)
    have hcong := movDampedComplInt_congr κ P tr r hc
    refine Eventually.of_forall fun z => ?_
    unfold opFun
    rw [hcong]
    have h4 : movDampedComplInt κ P tr r (fun w => c * cylRep x w) =
        fun w => c * movDampedComplInt κ P tr r (cylRep x) w :=
      funext fun w => movDampedComplInt_smul κ P tr r c (cylRep x) w
    rw [h4]
    exact cellZeroExt_smul d c _ (cToPlane z)
  let L : Planar.L2w m →ₗ[ℂ] Planar.L2w m :=
    { toFun := fun x => (hmem x).toLp _
      map_add' := fun x y => by
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp (hmem (x + y))).trans ?_
        refine (hadd' x y).trans ?_
        filter_upwards [MemLp.coeFn_toLp (hmem x), MemLp.coeFn_toLp (hmem y),
          Lp.coeFn_add ((hmem x).toLp _) ((hmem y).toLp _)] with z hx hy hxy
        rw [hxy, Pi.add_apply, hx, hy]
      map_smul' := fun c x => by
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp (hmem (c • x))).trans ?_
        refine (hsmul' c x).trans ?_
        filter_upwards [MemLp.coeFn_toLp (hmem x),
          Lp.coeFn_smul c ((hmem x).toLp _)] with z hx hcx
        rw [RingHom.id_apply, hcx, Pi.smul_apply, hx, smul_eq_mul] }
  refine ⟨L.mkContinuous K_A hnorm, fun x => ?_, LinearMap.mkContinuous_norm_le _ hK _⟩
  exact MemLp.coeFn_toLp (hmem x)

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
