import UnforcedLeray.Lib.HeatCylinder.H3Output
import UnforcedLeray.Lib.HeatCylinder.Linearity
import UnforcedLeray.Units.B0289.Periodize

/-!
# Linearity and quotient independence of the actual H³ heat output

The Gaussian heat output is first built from smooth periodic representatives. These lemmas show
that the resulting Sobolev element respects the actual convolution's linearity, so the graph norm
estimate can be applied to differences of smooth approximants.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem isQPeriodic_of_cylSmooth {c : ℝ} {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    UnforcedLeray.B0284.IsQPeriodic c T := by
  intro z
  have h := hT.periodic z
  simpa [Prod.add_def] using h

private theorem isCylSmooth_add {c : ℝ} {T U : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => T z + U z) := by
  refine ⟨hT.smooth.add hU.smooth, ?_, ?_⟩
  · intro z
    simp [hT.periodic z, hU.periodic z]
  · obtain ⟨R, hR⟩ := hT.bounded
    obtain ⟨S, hS⟩ := hU.bounded
    refine ⟨max R S, fun z hz => ?_⟩
    rw [hR z (lt_of_le_of_lt (le_max_left R S) hz),
      hS z (lt_of_le_of_lt (le_max_right R S) hz), add_zero]

private theorem periodic_ae_of_cellMeasure {c : ℝ} (hc : 0 < c) {P : Plane → Prop}
    (hper : UnforcedLeray.B0284.IsQPeriodic c P)
    (h : ∀ᵐ z ∂(UnforcedLeray.B0284.cellMeasure c), P z) :
    ∀ᵐ z ∂(volume : Measure Plane), P z :=
  UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper h

private theorem ae_of_centered_cell_periodic {c : ℝ} (hc : 0 < c) {P : Plane → Prop}
    (hper : UnforcedLeray.B0284.IsQPeriodic c P)
    (h : ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c), P z) :
    ∀ᵐ z ∂(volume : Measure Plane), P z := by
  let S : Set Plane := {z | ¬ P z}
  have hSper : UnforcedLeray.B0284.IsQPeriodic c (· ∈ S) := by
    intro z
    simp [S, hper z]
  have hcenter : volume (S ∩ UnforcedLeray.Cyl.cell c) = 0 := by
    have hnull : volume.restrict (UnforcedLeray.Cyl.cell c) S = 0 := by
      have h' := ae_iff.mp h
      simpa [S, UnforcedLeray.Cyl.cellμ] using h'
    rw [Measure.restrict_apply' (UnforcedLeray.Cyl.measurableSet_cell c)] at hnull
    simpa [S, Set.inter_comm] using hnull
  have hnull := (UnforcedLeray.Cyl.isAddFundamentalDomain_cell hc).measure_zero_of_invariant
    S ?_ hcenter
  · exact ae_iff.mpr (by simpa [S] using hnull)
  · rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have e : (-(⟨m • ((c, 0) : Plane), hv⟩ : AddSubgroup.zmultiples ((c, 0) : Plane)) +ᵥ z :
        Plane) = (z.1 + ((-m : ℤ) : ℝ) * c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp <;> ring
    rw [e]
    exact iff_of_eq (UnforcedLeray.B0289.IsQPeriodic.add_int_mul hSper (-m) z)

private theorem heatDiv_add_ae_volume {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Plane × Plane}
    (hTper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hUper : UnforcedLeray.B0284.IsQPeriodic c U)
    (hTm : AEStronglyMeasurable T volume) (hUm : AEStronglyMeasurable U volume)
    (hT : MemLp T 2 (UnforcedLeray.B0284.cellMeasure c))
    (hU : MemLp U 2 (UnforcedLeray.B0284.cellMeasure c)) :
    UnforcedLeray.B0296.heatDiv θ (fun z => T z + U z) =ᵐ[volume]
      fun z => UnforcedLeray.B0296.heatDiv θ T z + UnforcedLeray.B0296.heatDiv θ U z := by
  have hcell := heatDiv_add_ae hc hθ hTper hUper hTm hUm hT hU
  have hperT := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hTper
  have hperU := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hUper
  have hperInputSum : UnforcedLeray.B0284.IsQPeriodic c (fun z => T z + U z) := by
    intro z
    simp [hTper z, hUper z]
  have hperOutputSum := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hperInputSum
  have hper : UnforcedLeray.B0284.IsQPeriodic c (fun z =>
      UnforcedLeray.B0296.heatDiv θ (fun x => T x + U x) z =
        UnforcedLeray.B0296.heatDiv θ T z + UnforcedLeray.B0296.heatDiv θ U z) := by
    intro z
    simp [hperOutputSum z, hperT z, hperU z]
  exact periodic_ae_of_cellMeasure hc hper hcell

/-- The actual H³ heat output is additive on smooth periodic compact-axial tensor inputs. -/
theorem heatDivH3_add {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    heatDivH3 hc hθ (isCylSmooth_add hT hU) =
      heatDivH3 hc hθ hT + heatDivH3 hc hθ hU := by
  apply UnforcedLeray.Sob.W.ext
  rw [map_add]
  apply Lp.ext
  have hTper := isQPeriodic_of_cylSmooth hT
  have hUper := isQPeriodic_of_cylSmooth hU
  have hTm : AEStronglyMeasurable T volume :=
    hT.smooth.continuous.measurable.aestronglyMeasurable
  have hUm : AEStronglyMeasurable U volume :=
    hU.smooth.continuous.measurable.aestronglyMeasurable
  have hTmem := memLp_tensor_iterD_cylSmooth_normalized hc hT []
  have hUmem := memLp_tensor_iterD_cylSmooth_normalized hc hU []
  have hsum := heatDiv_add_ae_volume hc hθ hTper hUper hTm hUm
    (by simpa using hTmem) (by simpa using hUmem)
  have hvalT := heatDivH3_value_ae hc hθ hT
  have hvalU := heatDivH3_value_ae hc hθ hU
  have hvalSum := heatDivH3_value_ae hc hθ (isCylSmooth_add hT hU)
  have hmeasure : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
    rw [UnforcedLeray.Cyl.wμ_ρwW]
    simp [UnforcedLeray.Cyl.wμ]
  have hsumCell : UnforcedLeray.B0296.heatDiv θ (fun z => T z + U z) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      fun z => UnforcedLeray.B0296.heatDiv θ T z + UnforcedLeray.B0296.heatDiv θ U z := by
    rw [hmeasure]
    filter_upwards [ae_restrict_of_ae hsum] with z hz
    exact hz
  filter_upwards [hvalSum, hvalT, hvalU, hsumCell,
    Lp.coeFn_add (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hT))
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hU))]
      with z hzSum hzT hzU hAdd hplus
  calc
    (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
      (heatDivH3 hc hθ (isCylSmooth_add hT hU))) z) =
        UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ (fun x => T x + U x) z) := hzSum
    _ = UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z +
        UnforcedLeray.B0296.heatDiv θ U z) := congrArg UnforcedLeray.Train.toVec hAdd
    _ = UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z) +
        UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ U z) :=
      UnforcedLeray.Train.toVecL.map_add _ _
    _ = (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hT)) z) +
        (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hU)) z) := by
      rw [← hzT, ← hzU]
    _ = (⇑((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hT)) +
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hU))) z) :=
      hplus.symm

/-- The actual H³ heat output is independent of the chosen smooth periodic representative when
those representatives agree almost everywhere on the centered train cell. -/
theorem heatDivH3_congr_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (hU : UnforcedLeray.Sob.IsCylSmooth c U)
    (hTU : T =ᵐ[UnforcedLeray.Cyl.cellμ c] U) :
    heatDivH3 hc hθ hT = heatDivH3 hc hθ hU := by
  apply UnforcedLeray.Sob.W.ext
  apply Lp.ext
  have hTper := isQPeriodic_of_cylSmooth hT
  have hUper := isQPeriodic_of_cylSmooth hU
  have hEqPer : UnforcedLeray.B0284.IsQPeriodic c (fun z => T z = U z) := by
    intro z
    simp [hTper z, hUper z]
  have hTUvol := ae_of_centered_cell_periodic hc hEqPer hTU
  have hTm : AEStronglyMeasurable T volume :=
    hT.smooth.continuous.measurable.aestronglyMeasurable
  have hUm : AEStronglyMeasurable U volume :=
    hU.smooth.continuous.measurable.aestronglyMeasurable
  have hTmem := memLp_tensor_iterD_cylSmooth_normalized hc hT []
  have hUmem := memLp_tensor_iterD_cylSmooth_normalized hc hU []
  have hheatCell := heatDiv_congr_ae hc hθ hTper hUper hTm hUm
    (by simpa using hTmem) (by simpa using hUmem) hTUvol
  have hperHeatT := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hTper
  have hperHeatU := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hUper
  have hheatEqPer : UnforcedLeray.B0284.IsQPeriodic c (fun z =>
      UnforcedLeray.B0296.heatDiv θ T z = UnforcedLeray.B0296.heatDiv θ U z) := by
    intro z
    simp [hperHeatT z, hperHeatU z]
  have hheatVol := periodic_ae_of_cellMeasure hc hheatEqPer hheatCell
  have hmeasure : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
    rw [UnforcedLeray.Cyl.wμ_ρwW]
    simp [UnforcedLeray.Cyl.wμ]
  have hheat : UnforcedLeray.B0296.heatDiv θ T =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      UnforcedLeray.B0296.heatDiv θ U := by
    rw [hmeasure]
    exact ae_restrict_of_ae hheatVol
  have hvalT := heatDivH3_value_ae hc hθ hT
  have hvalU := heatDivH3_value_ae hc hθ hU
  filter_upwards [hvalT, hvalU, hheat] with z hzT hzU hzHeat
  calc
    (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hT)) z) =
        UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z) := hzT
    _ = UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ U z) :=
      congrArg UnforcedLeray.Train.toVec hzHeat
    _ = (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hU)) z) := hzU.symm

private theorem isCylSmooth_smul {c r : ℝ} {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => r • T z) := by
  have hconst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Plane => r) := contDiff_const
  refine ⟨hconst.smul hT.smooth, ?_, ?_⟩
  · intro z
    simp [hT.periodic z]
  · obtain ⟨R, hR⟩ := hT.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, smul_zero]⟩

/-- The actual H³ heat output respects real scalar multiplication on smooth inputs. -/
theorem heatDivH3_smul {c θ r : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    heatDivH3 hc hθ (isCylSmooth_smul (r := r) hT) = r • heatDivH3 hc hθ hT := by
  apply UnforcedLeray.Sob.W.ext
  rw [map_smul]
  apply Lp.ext
  have hTper := isQPeriodic_of_cylSmooth hT
  have hTm : AEStronglyMeasurable T volume :=
    hT.smooth.continuous.measurable.aestronglyMeasurable
  have hTmem := memLp_tensor_iterD_cylSmooth_normalized hc hT []
  have hcell := heatDiv_smul_ae (r := r) hc hθ hTper hTm (by simpa using hTmem)
  have hperT := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hTper
  have hperSmulInput : UnforcedLeray.B0284.IsQPeriodic c (fun z => r • T z) := by
    intro z
    simp [hTper z]
  have hperSmul := UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hperSmulInput
  have hperEq : UnforcedLeray.B0284.IsQPeriodic c (fun z =>
      UnforcedLeray.B0296.heatDiv θ (fun z => r • T z) z =
        r • UnforcedLeray.B0296.heatDiv θ T z) := by
    intro z
    simp [hperSmul z, hperT z]
  have hheatVol := periodic_ae_of_cellMeasure hc hperEq hcell
  have hmeasure : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
    rw [UnforcedLeray.Cyl.wμ_ρwW]
    simp [UnforcedLeray.Cyl.wμ]
  have hheat : UnforcedLeray.B0296.heatDiv θ (fun z => r • T z) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      fun z => r • UnforcedLeray.B0296.heatDiv θ T z := by
    rw [hmeasure]
    exact ae_restrict_of_ae hheatVol
  have hvalT := heatDivH3_value_ae hc hθ hT
  have hvalSmul := heatDivH3_value_ae hc hθ (isCylSmooth_smul (r := r) hT)
  let hvalue := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hT)
  filter_upwards [hvalSmul, hvalT, hheat, Lp.coeFn_smul r hvalue]
    with z hzSmul hzT hzHeat hzLp
  calc
    (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
      (heatDivH3 hc hθ (isCylSmooth_smul (r := r) hT))) z) =
        UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ (fun x => r • T x) z) := hzSmul
    _ = UnforcedLeray.Train.toVec (r • UnforcedLeray.B0296.heatDiv θ T z) :=
      congrArg UnforcedLeray.Train.toVec hzHeat
    _ = r • UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z) :=
      UnforcedLeray.Train.toVecL.map_smulₛₗ _ _
    _ = r • (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatDivH3 hc hθ hT)) z) := by
      rw [hzT]
    _ = (⇑(r • hvalue) z) := by
      change r • (⇑hvalue z) = ⇑(r • hvalue) z
      exact hzLp.symm

/-- Negation is respected by the actual H³ heat output on smooth inputs. -/
theorem heatDivH3_neg {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    heatDivH3 hc hθ (isCylSmooth_smul (r := -1) hT) = -heatDivH3 hc hθ hT := by
  simpa using heatDivH3_smul (c := c) (θ := θ) (r := -1) hc hθ hT

/-- Subtraction is respected by the actual H³ heat output on smooth inputs. -/
theorem heatDivH3_sub {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (hU : UnforcedLeray.Sob.IsCylSmooth c U)
    (hsub : UnforcedLeray.Sob.IsCylSmooth c (fun z => T z - U z)) :
    heatDivH3 hc hθ hsub = heatDivH3 hc hθ hT - heatDivH3 hc hθ hU := by
  have hsmul := heatDivH3_smul (c := c) (θ := θ) (r := -1) hc hθ hU
  have hsumSmooth := isCylSmooth_add hT (isCylSmooth_smul (r := -1) hU)
  have hfields : (fun z => T z - U z) = (fun z => T z + (-1 : ℝ) • U z) := by
    funext z
    simp [sub_eq_add_neg, neg_one_smul]
  have hcongr := heatDivH3_congr_ae hc hθ hsub hsumSmooth
    (Filter.Eventually.of_forall fun z => congrFun hfields z)
  rw [hcongr, heatDivH3_add hc hθ hT (isCylSmooth_smul (r := -1) hU), hsmul]
  simp [sub_eq_add_neg]

/-- The graph-norm difference of actual heat outputs is bounded by the Gaussian coefficient
and the complete centered-cell derivative-energy distance of their smooth tensor inputs. -/
theorem norm_heatDivH3_sub_le_energy {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (hU : UnforcedLeray.Sob.IsCylSmooth c U)
    (hsub : UnforcedLeray.Sob.IsCylSmooth c (fun z => T z - U z)) :
    ‖heatDivH3 hc hθ hT - heatDivH3 hc hθ hU‖ ≤
      ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)).toReal) *
        Real.sqrt (∑ α : UnforcedLeray.Sob.Idx 2 3,
          (eLpNorm (UnforcedLeray.Sob.iterD
            ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z))
            2 (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2) := by
  let K : ℝ := (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
    ENNReal.ofReal (heatDivL2Coeff θ)).toReal
  let E : ℝ := ∑ α : UnforcedLeray.Sob.Idx 2 3,
    (eLpNorm (UnforcedLeray.Sob.iterD
      ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z))
      2 (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2
  have hsq : ‖heatDivH3 hc hθ hT - heatDivH3 hc hθ hU‖ ^ 2 ≤ K ^ 2 * E := by
    rw [← heatDivH3_sub hc hθ hT hU hsub]
    exact norm_heatDivH3_le_energy hc hθ hsub
  have hK : 0 ≤ K := by
    dsimp [K]
    exact ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun α _ => sq_nonneg _
  have hRhs : 0 ≤ K * Real.sqrt E := mul_nonneg hK (Real.sqrt_nonneg E)
  have hsq' : ‖heatDivH3 hc hθ hT - heatDivH3 hc hθ hU‖ ^ 2 ≤
      (K * Real.sqrt E) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hE]
    exact hsq
  have hleft : 0 ≤ ‖heatDivH3 hc hθ hT - heatDivH3 hc hθ hU‖ := norm_nonneg _
  have hnorm : ‖heatDivH3 hc hθ hT - heatDivH3 hc hθ hU‖ ≤ K * Real.sqrt E := by
    nlinarith [hsq', hleft, hRhs]
  simpa [K, E] using hnorm


end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatDivH3_add
#print axioms UnforcedLeray.HeatCylinder.heatDivH3_congr_ae
#print axioms UnforcedLeray.HeatCylinder.heatDivH3_smul
#print axioms UnforcedLeray.HeatCylinder.heatDivH3_neg
#print axioms UnforcedLeray.HeatCylinder.heatDivH3_sub
#print axioms UnforcedLeray.HeatCylinder.norm_heatDivH3_sub_le_energy
