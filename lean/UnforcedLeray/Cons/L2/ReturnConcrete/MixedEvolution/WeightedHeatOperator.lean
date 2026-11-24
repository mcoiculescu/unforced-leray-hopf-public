import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatS0
import UnforcedLeray.Lib.HeatCylinder.HeatL2Linearity
import UnforcedLeray.Lib.HeatCylinder.HeatL2ContinuousOn

/-!
# Weighted zero-order heat operator bridge

This leaf starts the fixed-cylinder weighted S₀ construction by embedding actual `X_m` columns
into the normalized unweighted periodic heat carrier. All representatives remain the concrete
centered-periodic lifts used by the B0284 Gaussian convolution.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.B0579

/-- The concrete periodic planar lift of an `X_m` column is unweighted cell `L²` when `m≥1`. -/
theorem memLp_xColumnHeatLift_cyl {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (f : X c m) : MemLp (xColumnHeatLift hc f) 2 (Cyl.cellμ c) := by
  let rep := xColumnPeriodicRep hc f
  let lift := xColumnHeatLift hc f
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have hfRad : MemLp (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
      (volume.restrict (B0579.cell c)) :=
    (B0579.memLp_cellMeasure_iff c m).1 (Lp.memLp f)
  have hrepAE : rep =ᵐ[volume.restrict (B0579.cell c)] (f : Plane → ℝ) := by
    simpa only [hleft, rep] using xColumnPeriodicRep_ae_eq hc f
  have hfRadRep : MemLp (fun z => bracket z ^ m * rep z) 2
      (Cyl.cellμ c) := by
    have hfun : ((fun z : Plane => bracket z ^ m) * rep) =
        (fun z => bracket z ^ m * rep z) := by
      funext z
      rfl
    have hrep : MemLp ((fun z : Plane => bracket z ^ m) * rep) 2
        (volume.restrict (B0579.cell c)) :=
      hfRad.congr_enorm
        ((continuous_bracket_rpow m).aestronglyMeasurable.mul
          (stronglyMeasurable_xColumnPeriodicRep hc f).aestronglyMeasurable)
        (by
          filter_upwards [hrepAE] with z hz
          calc
            ‖bracket z ^ m * (f : Plane → ℝ) z‖ₑ =
                ‖bracket z ^ m * rep z‖ₑ := by rw [← hz]
            _ = ‖((fun x : Plane => bracket x ^ m) * rep) z‖ₑ := by rfl)
    simpa only [hleft, hfun] using hrep
  have hRepMeas : Measurable rep := (stronglyMeasurable_xColumnPeriodicRep hc f).measurable
  have hUnweighted : MemLp rep 2 (Cyl.cellμ c) := by
    refine hfRadRep.of_le hRepMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
    have hz' : z ∈ B0579.cell c := by
      simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
      exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
    have hweight : 1 ≤ bracket z ^ m := by
      rw [bracket_rpow]
      apply Real.one_le_rpow
      · rw [jb]
        nlinarith [sq_nonneg z.1, sq_nonneg z.2]
      · linarith
    have hweight0 : 0 ≤ bracket z ^ m := le_trans (by norm_num) hweight
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg hweight0]
    calc
      |rep z| = 1 * |rep z| := by ring
      _ ≤ bracket z ^ m * |rep z| :=
        mul_le_mul_of_nonneg_right hweight (abs_nonneg (rep z))
  have hLiftMeas : Measurable lift := hRepMeas.prodMk measurable_const
  have hLiftCyl : MemLp lift 2 (Cyl.cellμ c) := by
    refine hUnweighted.of_le hLiftMeas.aestronglyMeasurable ?_
    filter_upwards [] with z
    change ‖(rep z, (0 : ℝ))‖ ≤ ‖rep z‖
    simp [Prod.norm_def]
  exact hLiftCyl

/-- The same concrete lift belongs to B0284's normalized periodic-cell `L²` carrier. -/
theorem memLp_xColumnHeatLift_normalized {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (f : X c m) : MemLp (xColumnHeatLift hc f) 2 (B0284.cellMeasure c) := by
  have hmeas : Measurable (xColumnHeatLift hc f) :=
    (stronglyMeasurable_xColumnHeatLift hc f).measurable
  exact HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc hmeas
    (periodic_xColumnHeatLift hc f) (memLp_xColumnHeatLift_cyl hc hm f)

/-- The normalized unweighted `L²` class of the exact centered periodic representative used by
the weighted positive-age output. -/
def xColumnHeatInput {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (f : X c m) :
    Lp Plane 2 (B0284.cellMeasure c) :=
  (memLp_xColumnHeatLift_normalized hc hm f).toLp (xColumnHeatLift hc f)

theorem coeFn_xColumnHeatInput {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (f : X c m) :
    (xColumnHeatInput hc hm f : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      xColumnHeatLift hc f :=
  (memLp_xColumnHeatLift_normalized hc hm f).coeFn_toLp

private theorem ae_eq_volume_of_periodic_of_cylCell {c : ℝ} (hc : 0 < c)
    {E : Type*} {f g : Plane → E} (hf : B0284.IsQPeriodic c f) (hg : B0284.IsQPeriodic c g)
    (hfg : f =ᵐ[Cyl.cellμ c] g) : f =ᵐ[volume] g := by
  let S : Set Plane := {z | f z ≠ g z}
  have hSper : B0284.IsQPeriodic c (· ∈ S) := by
    intro z
    change (f (z.1 + c, z.2) ≠ g (z.1 + c, z.2)) = (f z ≠ g z)
    rw [hf z, hg z]
  have hEq : ∀ᵐ z ∂Cyl.cellμ c, f z = g z := hfg
  have hzeroCell : volume (S ∩ Cyl.cell c) = 0 := by
    have hzeroRestrict : volume.restrict (Cyl.cell c) S = 0 := by
      have hzero := ae_iff.mp hEq
      simpa [S, Cyl.cellμ] using hzero
    rw [Measure.restrict_apply' (Cyl.measurableSet_cell c)] at hzeroRestrict
    simpa [S, Set.inter_comm] using hzeroRestrict
  have hzero := (Cyl.isAddFundamentalDomain_cell hc).measure_zero_of_invariant S ?_ hzeroCell
  · exact ae_iff.mpr (by simpa [S] using hzero)
  · rintro ⟨v, hv⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : (-(⟨k • ((c, 0) : Plane), hv⟩ :
        AddSubgroup.zmultiples ((c, 0) : Plane)) +ᵥ z : Plane) =
        (z.1 + ((-k : ℤ) : ℝ) * c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp <;> ring
    rw [heq]
    exact iff_of_eq (B0289.IsQPeriodic.add_int_mul hSper (-k) z)

private theorem ae_cellMeasure_to_cyl {c m : ℝ} {f g : Plane → ℝ}
    (h : f =ᵐ[B0579.cellMeasure c m] g) : f =ᵐ[Cyl.cellμ c] g := by
  have h0 := (B0579.cellMeasure_ac_cellMeasure c 0 m).ae_le h
  have hμ : B0579.cellMeasure c 0 = Cyl.cellμ c := by
    rw [cellMeasure_zero_eq_cellVol, B0581.cellVol]
    simp [B0579.cell, Cyl.cell, Cyl.cellμ, show -(c / 2) = -c / 2 by ring]
  rw [hμ] at h0
  exact h0

/-- The weighted positive-age heat element and the sibling unweighted heat CLM have the same
actual first-coordinate representative on the normalized cell. -/
theorem xColumnHeatS0Positive_periodicRep_eq_heatL2CLMRep {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) =ᵐ[volume]
      fun z => (HeatCylinder.planeRep hc
        (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) z).1 := by
  let x := xColumnHeatInput hc hm f
  let r := HeatCylinder.planeRep hc x
  have hr := HeatCylinder.planeRep_spec hc x
  have hclass : r =ᵐ[B0284.cellMeasure c] xColumnHeatLift hc f := by
    exact hr.2.2.trans (coeFn_xColumnHeatInput hc hm f)
  have hglobal : r =ᵐ[volume] xColumnHeatLift hc f := by
    apply B0289.ae_of_ae_cellMeasure hc
    · intro z
      apply propext
      constructor
      · intro hz
        calc
          r z = r (z.1 + c, z.2) := (hr.2.1 z).symm
          _ = xColumnHeatLift hc f (z.1 + c, z.2) := hz
          _ = xColumnHeatLift hc f z := periodic_xColumnHeatLift hc f z
      · intro hz
        calc
          r (z.1 + c, z.2) = r z := hr.2.1 z
          _ = xColumnHeatLift hc f z := hz
          _ = xColumnHeatLift hc f (z.1 + c, z.2) :=
            (periodic_xColumnHeatLift hc f z).symm
    · exact hclass
  have hheatMem : MemLp (B0284.heat θ r) 2 (B0284.cellMeasure c) := by
    refine ⟨B0296.aestronglyMeasurable_heat c θ hr.1.aestronglyMeasurable, ?_⟩
    have hp : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    have hp' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    have hcontract := B0284.eLpNorm_heat_le (θ := θ) hc hr.2.1
      hr.1.aestronglyMeasurable hp hp'
    exact lt_of_le_of_lt hcontract (HeatCylinder.memLp_planeRep hc x).eLpNorm_ne_top.lt_top
  have hheatL2 : (HeatCylinder.heatL2CLM hc θ x : Plane → Plane) =ᵐ[
      B0284.cellMeasure c] B0284.heat θ r := by
    change (HeatCylinder.heatL2 hc θ x : Plane → Plane) =ᵐ[
      B0284.cellMeasure c] B0284.heat θ r
    change hheatMem.toLp (B0284.heat θ r) =ᵐ[
      B0284.cellMeasure c] B0284.heat θ r
    exact hheatMem.coeFn_toLp
  have hactual := coeFn_xColumnHeatS0Positive hc hm hθ hθ1 f
  have hactual0 :
      (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[B0579.cellMeasure c 0]
        fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 :=
    (B0579.cellMeasure_ac_cellMeasure c 0 m).ae_le hactual
  have hactualCyl :
      (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[Cyl.cellμ c]
        fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 := by
    simpa [cellMeasure_zero_eq_cellVol, B0581.cellVol, B0579.cell, Cyl.cellμ,
      Cyl.cell, show -(c / 2) = -c / 2 by ring] using hactual0
  have hrepOutput : xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) =ᵐ[
      Cyl.cellμ c] fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 :=
    (xColumnPeriodicRep_ae_eq hc (xColumnHeatS0Positive hc hm hθ hθ1 f)).trans hactualCyl
  have hrepOutputGlobal : xColumnPeriodicRep hc
      (xColumnHeatS0Positive hc hm hθ hθ1 f) =ᵐ[volume]
        fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 := by
    exact ae_eq_volume_of_periodic_of_cylCell (c := c) hc
      (f := xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f))
      (g := fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1)
      (by
        intro z
        change xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f)
          (z.1 + c, z.2) = xColumnPeriodicRep hc
            (xColumnHeatS0Positive hc hm hθ hθ1 f) z
        exact periodic_xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) z)
      (fun z => congrArg Prod.fst (B0284.heat_periodic
        (periodic_xColumnHeatLift hc f) z)) hrepOutput
  let y := HeatCylinder.heatL2CLM hc θ x
  let ry := HeatCylinder.planeRep hc y
  have hry := HeatCylinder.planeRep_spec hc y
  have hrepHeat : ry =ᵐ[B0284.cellMeasure c] B0284.heat θ r := hry.2.2.trans hheatL2
  have hrepHeatGlobal : ry =ᵐ[volume] B0284.heat θ r := by
    apply B0289.ae_of_ae_cellMeasure hc
    · intro z
      apply propext
      constructor
      · intro hz
        calc
          ry z = ry (z.1 + c, z.2) := (hry.2.1 z).symm
          _ = B0284.heat θ r (z.1 + c, z.2) := hz
          _ = B0284.heat θ r z := B0284.heat_periodic hr.2.1 z
      · intro hz
        calc
          ry (z.1 + c, z.2) = ry z := hry.2.1 z
          _ = B0284.heat θ r z := hz
          _ = B0284.heat θ r (z.1 + c, z.2) :=
            (B0284.heat_periodic hr.2.1 z).symm
    · exact hrepHeat
  have hrepHeatInput : ry =ᵐ[volume] B0284.heat θ (xColumnHeatLift hc f) := by
    filter_upwards [hrepHeatGlobal] with z hz
    exact hz.trans (congrFun (B0289.heat_congr_ae hθ hglobal) z)
  have hrepHeatInputFst : (fun z => (ry z).1) =ᵐ[volume]
      fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 :=
    hrepHeatInput.mono fun z hz => congrArg Prod.fst hz
  calc
    xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) =ᵐ[volume]
        fun z => (B0284.heat θ (xColumnHeatLift hc f) z).1 := hrepOutputGlobal
    _ =ᵐ[volume] fun z => (ry z).1 := hrepHeatInputFst.symm
    _ =ᵐ[volume] fun z =>
        (HeatCylinder.planeRep hc (HeatCylinder.heatL2CLM hc θ x) z).1 := by
      rfl

/-- The concrete centered periodic representative is additive as an element of the normalized
unweighted heat carrier. This packages the representative's quotient-independence into a real
linear input map on `X_m`. -/
noncomputable def xColumnHeatInputLinear {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) :
    X c m →ₗ[ℝ] Lp Plane 2 (B0284.cellMeasure c) where
  toFun := xColumnHeatInput hc hm
  map_add' := by
    intro f g
    apply Lp.ext
    have hsumRep : xColumnPeriodicRep hc (f + g) =ᵐ[Cyl.cellμ c]
        fun z => xColumnPeriodicRep hc f z + xColumnPeriodicRep hc g z := by
      have h0 := xColumnPeriodicRep_ae_eq hc (f + g)
      have h1 := ae_cellMeasure_to_cyl (c := c) (m := m) (Lp.coeFn_add f g)
      have h2 := xColumnPeriodicRep_ae_eq hc f
      have h3 := xColumnPeriodicRep_ae_eq hc g
      filter_upwards [h0, h1, h2, h3] with z hz0 hz1 hz2 hz3
      rw [hz0, hz1]
      simpa only [Pi.add_apply] using (congrArg₂ (· + ·) hz2 hz3).symm
    have hsumLift : xColumnHeatLift hc (f + g) =ᵐ[Cyl.cellμ c]
        fun z => xColumnHeatLift hc f z + xColumnHeatLift hc g z := by
      filter_upwards [hsumRep] with z hz
      simp [xColumnHeatLift, hz]
    have hsumLiftGlobal : xColumnHeatLift hc (f + g) =ᵐ[volume]
        fun z => xColumnHeatLift hc f z + xColumnHeatLift hc g z :=
      ae_eq_volume_of_periodic_of_cylCell hc
        (by
          intro z
          change xColumnHeatLift hc (f + g) (z.1 + c, z.2) =
            xColumnHeatLift hc (f + g) z
          exact periodic_xColumnHeatLift hc (f + g) z)
        (by
          intro z
          simp [periodic_xColumnHeatLift hc f z, periodic_xColumnHeatLift hc g z])
        hsumLift
    have hsumLiftNorm := (B0284.cellMeasure_ac c).ae_le hsumLiftGlobal
    filter_upwards [coeFn_xColumnHeatInput hc hm (f + g),
      coeFn_xColumnHeatInput hc hm f, coeFn_xColumnHeatInput hc hm g,
      hsumLiftNorm, Lp.coeFn_add (xColumnHeatInput hc hm f) (xColumnHeatInput hc hm g)]
      with z h0 h1 h2 h3 h4
    change (xColumnHeatInput hc hm (f + g) : Plane → Plane) z =
      (xColumnHeatInput hc hm f + xColumnHeatInput hc hm g :
        Lp Plane 2 (B0284.cellMeasure c)) z
    calc
      (xColumnHeatInput hc hm (f + g) : Plane → Plane) z =
          xColumnHeatLift hc (f + g) z := h0
      _ = xColumnHeatLift hc f z + xColumnHeatLift hc g z := h3
      _ = ((xColumnHeatInput hc hm f : Plane → Plane) z +
          (xColumnHeatInput hc hm g : Plane → Plane) z) := by rw [h1, h2]
      _ = (xColumnHeatInput hc hm f + xColumnHeatInput hc hm g :
          Lp Plane 2 (B0284.cellMeasure c)) z := h4.symm
  map_smul' := by
    intro a f
    apply Lp.ext
    have hsmulRep : xColumnPeriodicRep hc (a • f) =ᵐ[Cyl.cellμ c]
        fun z => a • xColumnPeriodicRep hc f z := by
      have h0 := xColumnPeriodicRep_ae_eq hc (a • f)
      have h1 := ae_cellMeasure_to_cyl (c := c) (m := m) (Lp.coeFn_smul a f)
      have h2 := xColumnPeriodicRep_ae_eq hc f
      filter_upwards [h0, h1, h2] with z hz0 hz1 hz2
      rw [hz0, hz1, hz2]
      simp only [Pi.smul_apply]
    have hsmulLift : xColumnHeatLift hc (a • f) =ᵐ[Cyl.cellμ c]
        fun z => a • xColumnHeatLift hc f z := by
      filter_upwards [hsmulRep] with z hz
      simp [xColumnHeatLift, hz]
    have hsmulLiftGlobal : xColumnHeatLift hc (a • f) =ᵐ[volume]
        fun z => a • xColumnHeatLift hc f z :=
      ae_eq_volume_of_periodic_of_cylCell hc
        (by
          intro z
          change xColumnHeatLift hc (a • f) (z.1 + c, z.2) =
            xColumnHeatLift hc (a • f) z
          exact periodic_xColumnHeatLift hc (a • f) z)
        (by
          intro z
          simp [periodic_xColumnHeatLift hc f z]) hsmulLift
    have hsmulLiftNorm := (B0284.cellMeasure_ac c).ae_le hsmulLiftGlobal
    filter_upwards [coeFn_xColumnHeatInput hc hm (a • f),
      coeFn_xColumnHeatInput hc hm f, hsmulLiftNorm,
      Lp.coeFn_smul a (xColumnHeatInput hc hm f)] with z h0 h1 h2 h3
    change (xColumnHeatInput hc hm (a • f) : Plane → Plane) z =
      (a • xColumnHeatInput hc hm f : Lp Plane 2 (B0284.cellMeasure c)) z
    calc
      (xColumnHeatInput hc hm (a • f) : Plane → Plane) z =
          xColumnHeatLift hc (a • f) z := h0
      _ = a • xColumnHeatLift hc f z := h2
      _ = a • (xColumnHeatInput hc hm f : Plane → Plane) z := by rw [h1]
      _ = (a • xColumnHeatInput hc hm f : Lp Plane 2 (B0284.cellMeasure c)) z := h3.symm

/-- For cylinders with `c≥1`, the normalized unweighted heat input has norm at most the actual
`X_m` norm. This is the exact `1/c` cell normalization together with the radial weight `≥1`. -/
theorem norm_xColumnHeatInput_le {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (f : X c m) : ‖xColumnHeatInput hc hm f‖ ≤ ‖f‖ := by
  let lift := xColumnHeatLift hc f
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have hrepAE : xColumnPeriodicRep hc f =ᵐ[Cyl.cellμ c] (f : Plane → ℝ) :=
    xColumnPeriodicRep_ae_eq hc f
  have hpoint : ∀ᵐ z ∂Cyl.cellμ c,
      ‖lift z‖ₑ ≤ ‖bracket z ^ m * (f : Plane → ℝ) z‖ₑ := by
    filter_upwards [hrepAE, ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz hzcell
    have hweight : 1 ≤ bracket z ^ m := by
      rw [bracket_rpow]
      apply Real.one_le_rpow
      · rw [jb]
        nlinarith [sq_nonneg z.1, sq_nonneg z.2]
      · linarith
    have hweight0 : 0 ≤ bracket z ^ m := le_trans (by norm_num) hweight
    have hpair : ‖(xColumnPeriodicRep hc f z, (0 : ℝ))‖ₑ =
        ‖xColumnPeriodicRep hc f z‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      congr 1
      rw [Prod.norm_def]
      simp
    rw [show lift z = (xColumnPeriodicRep hc f z, (0 : ℝ)) by rfl, hpair, hz]
    calc
      ‖(f : Plane → ℝ) z‖ₑ = ENNReal.ofReal |(f : Plane → ℝ) z| :=
        Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (bracket z ^ m * |(f : Plane → ℝ) z|) :=
        ENNReal.ofReal_le_ofReal (by
          calc
            |(f : Plane → ℝ) z| = 1 * |(f : Plane → ℝ) z| := by ring
            _ ≤ bracket z ^ m * |(f : Plane → ℝ) z| :=
              mul_le_mul_of_nonneg_right hweight (abs_nonneg _))
      _ = ‖bracket z ^ m * (f : Plane → ℝ) z‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hweight0]
  have hradBound : eLpNorm lift 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
        (Cyl.cellμ c) := eLpNorm_mono_enorm_ae hpoint
  have hradBound' : eLpNorm lift 2 (Cyl.cellμ c) ≤
      eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m) := by
    calc
      eLpNorm lift 2 (Cyl.cellμ c) ≤
          eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
            (Cyl.cellμ c) := hradBound
      _ = eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
            (volume.restrict (B0579.cell c)) := by rw [hleft]
      _ = eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m) := by
        simpa only [B0579.bracket_rpow] using
          (B0579.eLpNorm_cellMeasure c m (f : Plane → ℝ)).symm
  have hLiftMeas : Measurable lift :=
    (stronglyMeasurable_xColumnHeatLift hc f).measurable
  have hLiftPer : B0284.IsQPeriodic c lift := periodic_xColumnHeatLift hc f
  have hsq := HeatCylinder.eLpNorm_sq_cellMeasure_eq_cyl hc hLiftMeas hLiftPer
  have hinfin : eLpNorm lift 2 (B0284.cellMeasure c) ≠ ⊤ :=
    (memLp_xColumnHeatLift_normalized hc hm f).eLpNorm_ne_top
  have hfin : eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m) ≠ ⊤ :=
    (Lp.memLp f).eLpNorm_ne_top
  have hsqle : (eLpNorm lift 2 (B0284.cellMeasure c)) ^ 2 ≤
      (eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m)) ^ 2 := by
    rw [hsq]
    have hcENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
      simpa using ENNReal.ofReal_le_ofReal hc1
    have hinv : (ENNReal.ofReal c)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hcENN
    calc
      (ENNReal.ofReal c)⁻¹ * (eLpNorm lift 2 (Cyl.cellμ c)) ^ 2 ≤
          1 * (eLpNorm lift 2 (Cyl.cellμ c)) ^ 2 :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = (eLpNorm lift 2 (Cyl.cellμ c)) ^ 2 := by simp
      _ ≤ (eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m)) ^ 2 :=
        pow_le_pow_left' hradBound' 2
  have hto := ENNReal.toReal_mono (ENNReal.pow_ne_top hfin) hsqle
  have hnormInput : ‖xColumnHeatInput hc hm f‖ =
      (eLpNorm lift 2 (B0284.cellMeasure c)).toReal := by
    change ‖(memLp_xColumnHeatLift_normalized hc hm f).toLp
      (xColumnHeatLift hc f)‖ = _
    rw [Lp.norm_toLp]
  have hnormF : ‖f‖ =
      (eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m)).toReal := by
    rw [Lp.norm_def]
  have hto' : (eLpNorm lift 2 (B0284.cellMeasure c)).toReal ^ 2 ≤
      (eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m)).toReal ^ 2 := by
    simpa only [ENNReal.toReal_pow] using hto
  rw [← hnormInput, ← hnormF] at hto'
  nlinarith [norm_nonneg (xColumnHeatInput hc hm f), norm_nonneg f]

/-- The concrete weighted-column embedding into the normalized unweighted cylinder heat space,
now as a continuous linear map. -/
noncomputable def xColumnHeatInputCLM {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) : X c m →L[ℝ] Lp Plane 2 (B0284.cellMeasure c) :=
  (xColumnHeatInputLinear hc hm).mkContinuous 1 (fun f => by
    rw [one_mul]
    exact norm_xColumnHeatInput_le hc hc1 hm f)

/-- The actual normalized-cell Gaussian heat family on an `X_m` input, with output retained in
the unweighted cylinder carrier. This is the concrete heat CLM composed with the actual periodic
lift, not an abstract heat supplier. -/
noncomputable def xColumnHeatL2CLM {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (θ : ℝ) : X c m →L[ℝ] Lp Plane 2 (B0284.cellMeasure c) :=
  (HeatCylinder.heatL2CLM hc θ).comp (xColumnHeatInputCLM hc hc1 hm)

theorem norm_xColumnHeatL2CLM_apply_le {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (f : X c m) : ‖xColumnHeatL2CLM hc hc1 hm θ f‖ ≤ ‖f‖ := by
  change ‖HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)‖ ≤ ‖f‖
  calc
    ‖HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)‖ ≤
        ‖xColumnHeatInput hc hm f‖ := by
      rw [HeatCylinder.heatL2CLM_apply]
      exact HeatCylinder.norm_heatL2_le hc _
    _ ≤ ‖f‖ := norm_xColumnHeatInput_le hc hc1 hm f

theorem xColumnHeatL2CLM_apply_eq_actual_heat {c m θ : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    (fun z => (HeatCylinder.planeRep hc (xColumnHeatL2CLM hc hc1 hm θ f) z).1) =ᵐ[volume]
      xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) := by
  change (fun z => (HeatCylinder.planeRep hc
      (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) z).1) =ᵐ[volume] _
  exact (xColumnHeatS0Positive_periodicRep_eq_heatL2CLMRep
    hc hm hθ hθ1 f).symm

/-- Positive-age continuity of the concrete normalized-cell heat orbit generated by an actual
weighted column. This is unweighted `L²` continuity; weighted strong continuity at age zero is a
separate estimate. -/
theorem continuousOn_xColumnHeatL2CLM_positive {c m : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (f : X c m) :
    ContinuousOn (fun θ => xColumnHeatL2CLM hc hc1 hm θ f) (Set.Ioi 0) := by
  simpa [xColumnHeatL2CLM, ContinuousLinearMap.comp_apply] using
    (HeatCylinder.continuousOn_heatL2CLM_positive hc (xColumnHeatInputCLM hc hc1 hm f))

/-- Strong measurability of the actual positive-age heat orbit for each `X_m` input. -/
theorem aestronglyMeasurable_xColumnHeatL2CLM_positive {c m : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (f : X c m) :
    AEStronglyMeasurable (fun θ => xColumnHeatL2CLM hc hc1 hm θ f)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  exact (continuousOn_xColumnHeatL2CLM_positive hc hc1 hm f).aestronglyMeasurable
    measurableSet_Ioi

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.memLp_xColumnHeatLift_cyl
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.memLp_xColumnHeatLift_normalized
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0Positive_periodicRep_eq_heatL2CLMRep
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatInputLinear
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatInput_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatInputCLM
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatL2CLM_apply_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatL2CLM_apply_eq_actual_heat
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.continuousOn_xColumnHeatL2CLM_positive
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.aestronglyMeasurable_xColumnHeatL2CLM_positive
