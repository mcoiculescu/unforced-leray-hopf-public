import UnforcedLeray.Lib.HeatCylinder.PeriodicLift
import UnforcedLeray.Lib.HeatCylinder.Gradient
import UnforcedLeray.Lib.HeatCylinder.Linearity
import UnforcedLeray.Lib.HeatCylinder.BochnerPath

/-!
# The heat-divergence operator on the normalized cylinder `L²` quotient

A canonical measurable periodic representative is selected from each cell `L²` class, and the
actual B0296 Gaussian convolution is then descended to the quotient. Representative independence
is proved using the concrete convolution theorem, so the quotient map is not defined by an oracle.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

/-- Every normalized-cell tensor `L²` class has a globally strongly measurable periodic
representative on the plane. -/
theorem exists_periodic_tensor_rep {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    ∃ T : Plane → Plane × Plane,
      AEStronglyMeasurable T volume ∧ IsQPeriodic c T ∧
        T =ᵐ[cellMeasure c] (x : Plane → Plane × Plane) := by
  let u : ℝ → Lp (Plane × Plane) 2 (cellMeasure c) := fun _ => x
  have hu : StronglyMeasurable u := stronglyMeasurable_const
  obtain ⟨F, hF, hslice, hper, hrep⟩ :=
    exists_stronglyMeasurable_periodic_tensor_rep hc hu
  refine ⟨fun z => F (0, z), hslice 0, hper 0, ?_⟩
  simpa [u] using hrep 0

/-- The periodic representative of a single cell `L²` class can be chosen globally measurable,
not only a.e. strongly measurable. -/
theorem exists_measurable_periodic_tensor_rep {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    ∃ T : Plane → Plane × Plane,
      Measurable T ∧ IsQPeriodic c T ∧
        T =ᵐ[cellMeasure c] (x : Plane → Plane × Plane) := by
  let u : ℝ → Lp (Plane × Plane) 2 (cellMeasure c) := fun _ => x
  have hu : StronglyMeasurable u := stronglyMeasurable_const
  obtain ⟨F, hF, hslice, hper, hrep⟩ :=
    exists_stronglyMeasurable_periodic_tensor_rep hc hu
  have hFm : Measurable F := hF.measurable
  refine ⟨fun z => F (0, z), hFm.comp (measurable_const.prodMk measurable_id), hper 0, ?_⟩
  simpa [u] using hrep 0

/-- A selected globally measurable periodic representative of an `L²` class. Its choice is used
only to define an actual convolution; later lemmas show the output class is independent of it. -/
noncomputable def tensorRep {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) : Plane → Plane × Plane :=
  Classical.choose (exists_measurable_periodic_tensor_rep hc x)

theorem tensorRep_spec {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    AEStronglyMeasurable (tensorRep hc x) volume ∧
      IsQPeriodic c (tensorRep hc x) ∧
        tensorRep hc x =ᵐ[cellMeasure c] (x : Plane → Plane × Plane) := by
  have h := Classical.choose_spec (exists_measurable_periodic_tensor_rep hc x)
  exact ⟨h.1.aestronglyMeasurable, h.2.1, h.2.2⟩

theorem tensorRep_measurable {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) : Measurable (tensorRep hc x) :=
  (Classical.choose_spec (exists_measurable_periodic_tensor_rep hc x)).1

/-- The canonical periodic representative has the same `L²` norm as its quotient class. -/
theorem eLpNorm_tensorRep_eq {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    eLpNorm (tensorRep hc x) 2 (cellMeasure c) = ‖x‖ₑ := by
  rw [eLpNorm_congr_ae (tensorRep_spec hc x).2.2, Lp.enorm_def]

/-- The selected representative is in cell `L²`. -/
theorem memLp_tensorRep {c : ℝ} (hc : 0 < c)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    MemLp (tensorRep hc x) 2 (cellMeasure c) := by
  have hx := Lp.memLp x
  refine ⟨hx.1.congr (tensorRep_spec hc x).2.2.symm, ?_⟩
  calc
    eLpNorm (tensorRep hc x) 2 (cellMeasure c) =
        eLpNorm (x : Plane → Plane × Plane) 2 (cellMeasure c) :=
      eLpNorm_congr_ae (tensorRep_spec hc x).2.2
    _ < ⊤ := hx.2

/-- The actual heat-divergence convolution, descended to normalized-cell `L²` as an `L²` class. -/
noncomputable def heatDivL2 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    Lp (Plane × Plane) 2 (cellMeasure c) → Lp Plane 2 (cellMeasure c) :=
  fun x =>
    let T := tensorRep hc x
    let hmem := memLp_tensorRep hc x
    let hper := (tensorRep_spec hc x).2.1
    let hmeas := (tensorRep_spec hc x).1
    let hout := UnforcedLeray.B0296.memLp_heatDiv hc hθ hper hmeas
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
    hout.toLp (UnforcedLeray.B0296.heatDiv θ T)

/-- Norm bound for the quotient-valued actual Gaussian heat-divergence operator. -/
theorem norm_heatDivL2_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    ‖heatDivL2 hc hθ x‖ ≤ heatDivL2Coeff θ * ‖x‖ := by
  let T := tensorRep hc x
  let hmem := memLp_tensorRep hc x
  let hper := (tensorRep_spec hc x).2.1
  let hmeas := (tensorRep_spec hc x).1
  let hout := UnforcedLeray.B0296.memLp_heatDiv hc hθ hper hmeas
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  have hclass : hmem.toLp T = x := by
    apply Lp.ext
    filter_upwards [hmem.coeFn_toLp, (tensorRep_spec hc x).2.2] with z hzT hzx
    exact hzT.trans hzx
  change ‖hout.toLp (UnforcedLeray.B0296.heatDiv θ T)‖ ≤
    heatDivL2Coeff θ * ‖x‖
  calc
    ‖hout.toLp (UnforcedLeray.B0296.heatDiv θ T)‖ ≤
        heatDivL2Coeff θ * ‖hmem.toLp T‖ :=
      norm_heatDivL2_slice_le hc hθ hper hmeas hmem hout
    _ = heatDivL2Coeff θ * ‖x‖ := by rw [hclass]

/-- The quotient-valued actual Gaussian operator is additive. The proof compares the selected
representatives only almost everywhere, promotes that equality to the full plane by periodicity,
and then invokes the concrete integral additivity theorem. -/
theorem heatDivL2_add {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x y : Lp (Plane × Plane) 2 (cellMeasure c)) :
    heatDivL2 hc hθ (x + y) = heatDivL2 hc hθ x + heatDivL2 hc hθ y := by
  let Txy := tensorRep hc (x + y)
  let Tx := tensorRep hc x
  let Ty := tensorRep hc y
  have hxy := tensorRep_spec hc (x + y)
  have hx := tensorRep_spec hc x
  have hy := tensorRep_spec hc y
  have hperiodic : IsQPeriodic c (fun z => Txy z = Tx z + Ty z) := by
    intro z
    have hxyper : Txy (z.1 + c, z.2) = Txy z := by
      dsimp [Txy]
      exact hxy.2.1 z
    have hxper : Tx (z.1 + c, z.2) = Tx z := by
      dsimp [Tx]
      exact hx.2.1 z
    have hyper : Ty (z.1 + c, z.2) = Ty z := by
      dsimp [Ty]
      exact hy.2.1 z
    change (Txy (z.1 + c, z.2) = Tx (z.1 + c, z.2) + Ty (z.1 + c, z.2)) =
      (Txy z = Tx z + Ty z)
    apply propext
    constructor
    · intro h
      calc
        Txy z = Txy (z.1 + c, z.2) := hxyper.symm
        _ = Tx (z.1 + c, z.2) + Ty (z.1 + c, z.2) := h
        _ = Tx z + Ty z := by rw [hxper, hyper]
    · intro h
      calc
        Txy (z.1 + c, z.2) = Txy z := hxyper
        _ = Tx z + Ty z := h
        _ = Tx (z.1 + c, z.2) + Ty (z.1 + c, z.2) := by rw [← hxper, ← hyper]
  have haeCell : Txy =ᵐ[cellMeasure c] fun z => Tx z + Ty z := by
    filter_upwards [hxy.2.2, hx.2.2, hy.2.2, Lp.coeFn_add x y] with z hxyz hxz hyz hadd
    calc
      Txy z = (x + y : Lp (Plane × Plane) 2 (cellMeasure c)) z := hxyz
      _ = x z + y z := hadd
      _ = Tx z + Ty z := by rw [← hxz, ← hyz]
  have haeVol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperiodic haeCell
  have hmemxy := memLp_tensorRep hc (x + y)
  have hmemx := memLp_tensorRep hc x
  have hmemy := memLp_tensorRep hc y
  have hmemsum : MemLp (fun z => Tx z + Ty z) 2 (cellMeasure c) := hmemx.add hmemy
  have hmeassum : AEStronglyMeasurable (fun z => Tx z + Ty z) volume :=
    (hx.1.add hy.1)
  have hperSum : IsQPeriodic c (fun z => Tx z + Ty z) := by
    intro z
    have hxper : Tx (z.1 + c, z.2) = Tx z := by
      dsimp [Tx]
      exact hx.2.1 z
    have hyper : Ty (z.1 + c, z.2) = Ty z := by
      dsimp [Ty]
      exact hy.2.1 z
    change Tx (z.1 + c, z.2) + Ty (z.1 + c, z.2) = Tx z + Ty z
    rw [hxper, hyper]
  have hcongr := heatDiv_congr_ae hc hθ hxy.2.1
    hperSum hxy.1 hmeassum hmemxy hmemsum haeVol
  have hadd := heatDiv_add_ae hc hθ hx.2.1 hy.2.1 hx.1 hy.1 hmemx hmemy
  let Hxy := UnforcedLeray.B0296.memLp_heatDiv hc hθ hxy.2.1 hxy.1
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmemxy.eLpNorm_ne_top
  let Hx := UnforcedLeray.B0296.memLp_heatDiv hc hθ hx.2.1 hx.1
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmemx.eLpNorm_ne_top
  let Hy := UnforcedLeray.B0296.memLp_heatDiv hc hθ hy.2.1 hy.1
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmemy.eLpNorm_ne_top
  have hsum : UnforcedLeray.B0296.heatDiv θ Txy =ᵐ[cellMeasure c]
      fun z => UnforcedLeray.B0296.heatDiv θ Tx z +
        UnforcedLeray.B0296.heatDiv θ Ty z := hcongr.trans hadd
  change Hxy.toLp (UnforcedLeray.B0296.heatDiv θ Txy) =
    Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx) +
      Hy.toLp (UnforcedLeray.B0296.heatDiv θ Ty)
  apply Lp.ext
  filter_upwards [Hxy.coeFn_toLp, Hx.coeFn_toLp, Hy.coeFn_toLp, hsum,
    Lp.coeFn_add (Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx))
      (Hy.toLp (UnforcedLeray.B0296.heatDiv θ Ty))] with z hxyOut hxOut hyOut hsumz haddOut
  calc
    (Hxy.toLp (UnforcedLeray.B0296.heatDiv θ Txy)) z =
        UnforcedLeray.B0296.heatDiv θ Txy z := hxyOut
    _ = UnforcedLeray.B0296.heatDiv θ Tx z + UnforcedLeray.B0296.heatDiv θ Ty z := hsumz
    _ = (Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx)) z +
        (Hy.toLp (UnforcedLeray.B0296.heatDiv θ Ty)) z := by rw [← hxOut, ← hyOut]
    _ = (Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx) +
        Hy.toLp (UnforcedLeray.B0296.heatDiv θ Ty)) z := haddOut.symm


/-- The quotient-valued actual Gaussian operator respects real scalar multiplication. -/
theorem heatDivL2_smul {c θ r : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    heatDivL2 hc hθ (r • x) = r • heatDivL2 hc hθ x := by
  let Tr := tensorRep hc (r • x)
  let Tx := tensorRep hc x
  have hr := tensorRep_spec hc (r • x)
  have hx := tensorRep_spec hc x
  have hperiodic : IsQPeriodic c (fun z => Tr z = r • Tx z) := by
    intro z
    have hrper : Tr (z.1 + c, z.2) = Tr z := by
      dsimp [Tr]
      exact hr.2.1 z
    have hxper : Tx (z.1 + c, z.2) = Tx z := by
      dsimp [Tx]
      exact hx.2.1 z
    change (Tr (z.1 + c, z.2) = r • Tx (z.1 + c, z.2)) =
      (Tr z = r • Tx z)
    apply propext
    constructor
    · intro h
      calc
        Tr z = Tr (z.1 + c, z.2) := hrper.symm
        _ = r • Tx (z.1 + c, z.2) := h
        _ = r • Tx z := by rw [hxper]
    · intro h
      calc
        Tr (z.1 + c, z.2) = Tr z := hrper
        _ = r • Tx z := h
        _ = r • Tx (z.1 + c, z.2) := by rw [← hxper]
  have haeCell : Tr =ᵐ[cellMeasure c] fun z => r • Tx z := by
    filter_upwards [hr.2.2, hx.2.2, Lp.coeFn_smul r x] with z hrz hxz hsmul
    calc
      Tr z = (r • x : Lp (Plane × Plane) 2 (cellMeasure c)) z := hrz
      _ = r • x z := hsmul
      _ = r • Tx z := by rw [← hxz]
  have haeVol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperiodic haeCell
  have hmemr := memLp_tensorRep hc (r • x)
  have hmemx := memLp_tensorRep hc x
  have hmemsmul : MemLp (fun z => r • Tx z) 2 (cellMeasure c) := hmemx.const_smul r
  have hmeassmul : AEStronglyMeasurable (fun z => r • Tx z) volume := hx.1.const_smul r
  have hperSmul : IsQPeriodic c (fun z => r • Tx z) := by
    intro z
    have hxper : Tx (z.1 + c, z.2) = Tx z := by
      dsimp [Tx]
      exact hx.2.1 z
    change r • Tx (z.1 + c, z.2) = r • Tx z
    rw [hxper]
  have hcongr := heatDiv_congr_ae hc hθ hr.2.1 hperSmul hr.1 hmeassmul hmemr hmemsmul haeVol
  have hsmul : UnforcedLeray.B0296.heatDiv θ (fun z => r • Tx z) =ᵐ[cellMeasure c]
      fun z => r • UnforcedLeray.B0296.heatDiv θ Tx z :=
    heatDiv_smul_ae (c := c) (θ := θ) (r := r) hc hθ hx.2.1 hx.1 hmemx
  have hsum : UnforcedLeray.B0296.heatDiv θ Tr =ᵐ[cellMeasure c]
      fun z => r • UnforcedLeray.B0296.heatDiv θ Tx z := hcongr.trans hsmul
  let Hr := UnforcedLeray.B0296.memLp_heatDiv hc hθ hr.2.1 hr.1
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmemr.eLpNorm_ne_top
  let Hx := UnforcedLeray.B0296.memLp_heatDiv hc hθ hx.2.1 hx.1
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmemx.eLpNorm_ne_top
  change Hr.toLp (UnforcedLeray.B0296.heatDiv θ Tr) =
    r • Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx)
  apply Lp.ext
  filter_upwards [Hr.coeFn_toLp, Hx.coeFn_toLp, hsum,
    Lp.coeFn_smul r (Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx))] with z hrOut hxOut hsumz hsmulOut
  calc
    (Hr.toLp (UnforcedLeray.B0296.heatDiv θ Tr)) z =
        UnforcedLeray.B0296.heatDiv θ Tr z := hrOut
    _ = r • UnforcedLeray.B0296.heatDiv θ Tx z := hsumz
    _ = r • (Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx)) z := by rw [← hxOut]
    _ = (r • Hx.toLp (UnforcedLeray.B0296.heatDiv θ Tx)) z := hsmulOut.symm

/-- The quotient heat-divergence operator as a continuous linear map between the native
normalized-cell `L²` spaces. -/
noncomputable def heatDivL2CLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    Lp (Plane × Plane) 2 (cellMeasure c) →L[ℝ] Lp Plane 2 (cellMeasure c) :=
  (let L : Lp (Plane × Plane) 2 (cellMeasure c) →ₗ[ℝ] Lp Plane 2 (cellMeasure c) := {
    toFun := heatDivL2 hc hθ
    map_add' := heatDivL2_add hc hθ
    map_smul' := fun r x => heatDivL2_smul (c := c) (θ := θ) (r := r) hc hθ x
  }
  L.mkContinuous (heatDivL2Coeff θ) (norm_heatDivL2_le hc hθ))

@[simp] theorem heatDivL2CLM_apply {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    heatDivL2CLM hc hθ x = heatDivL2 hc hθ x := rfl

@[simp] theorem heatDivL2CLM_norm_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    ‖heatDivL2CLM hc hθ x‖ ≤ heatDivL2Coeff θ * ‖x‖ :=
  norm_heatDivL2_le hc hθ x

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.norm_heatDivL2_le

#print axioms UnforcedLeray.HeatCylinder.heatDivL2CLM
#print axioms UnforcedLeray.HeatCylinder.heatDivL2_add
#print axioms UnforcedLeray.HeatCylinder.heatDivL2_smul
