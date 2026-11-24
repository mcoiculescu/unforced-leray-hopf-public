import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.RealBiotSavart
import UnforcedLeray.Units.B0610
import UnforcedLeray.Units.B0238
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp

/-!
# Concrete real mixed-flux source

For a real weighted vorticity `w`, the velocity in this file is the actual B0583 cylinder
Biot–Savart reconstruction from `RealBiotSavart`. The flux is the physical real vector
`v*w + (K_c w)*E`. Boundedness assumptions are stated on the actual coefficient functions; no
abstract velocity or source witness is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open Filter
open UnforcedLeray.B0579
open UnforcedLeray.B0581 (cellVol)
open UnforcedLeray.Train (Vec)

/-- The actual real linearized vorticity flux for a real train velocity `v` and curl `E`. -/
def physicalFlux {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0) : Plane → Vec :=
  fun x => w x • v x + E x • realBiotSavart hm w hcirc x

/-- The actual real Biot–Savart velocity obeys the B0583 H¹ estimate, since the real projection
is contractive on the unweighted cylinder `L²` space. -/
theorem norm_realBiotSavart_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (w : X c m) (hcirc : ∫ x in cell c, w x = 0) :
    ‖realBiotSavart hm w hcirc‖ ≤ 5 * (1 + c) * ‖w‖ := by
  let U := UnforcedLeray.B0583.velocity c hm w hcirc
  have hreal : ‖realBiotSavart hm w hcirc‖ ≤ ‖U‖ := by
    simpa [realBiotSavart, U] using norm_realPartVelocityLp_le U
  have hH1 := UnforcedLeray.B0583.h1Norm_velocity_le c hm w hcirc
  have hL2 : ‖U‖ ≤ UnforcedLeray.B0583.h1Norm U
      (UnforcedLeray.B0583.velGradQ c hm w)
      (UnforcedLeray.B0583.velGradEta c hm w hcirc) := by
    unfold UnforcedLeray.B0583.h1Norm
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [sq_nonneg (‖UnforcedLeray.B0583.velGradQ c hm w‖),
      sq_nonneg (‖UnforcedLeray.B0583.velGradEta c hm w hcirc‖)]
  exact hreal.trans (hL2.trans hH1)

/-- Each component of the physical flux belongs to the real weighted space `X_m` provided the
train velocity is bounded and the background curl has bounded `⟨x⟩^m` weight. -/
theorem memLp_physicalFlux {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (_hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    ∀ i : Fin 2, MemLp (fun x => physicalFlux hm v E w hcirc x i) 2
      (cellMeasure c m) := by
  intro i
  let K : Lp Vec 2 (cellVol c) := realBiotSavart hm w hcirc
  have hK : MemLp (fun x => K x i) 2 (volume.restrict (cell c)) := by
    have hvec : MemLp (fun x => K x) 2 (cellVol c) := Lp.memLp K
    have hproj := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp_memLp' hvec
    convert hproj using 1 <;> rfl
  have hFirst : MemLp (fun x => v x i * w x) 2 (cellMeasure c m) := by
    have hvComp : Continuous fun x => v x i :=
      (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp hv
    have hmul := memLp_mulR hvComp (fun x => hvBound x i) w
    simpa [mul_comm] using hmul
  have hWeightedK : MemLp (fun x => (bracket x ^ m * E x) * K x i) 2
      (volume.restrict (cell c)) := by
    have hmult : MemLp (fun x => (bracket x ^ m * E x) * K x i) 2
        (volume.restrict (cell c)) := by
      refine (hK.const_mul CE).of_le
        (((continuous_bracket_rpow m).mul hE).aestronglyMeasurable.mul hK.1)
        (ae_restrict_of_forall_mem (measurableSet_cell c) fun x hx => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc |(bracket x ^ m * E x) * K x i| ≤ CE * |K x i| := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hEBound x hx) (abs_nonneg _)
        _ = |CE * K x i| := by rw [abs_mul, abs_of_nonneg hCE]
    exact hmult
  have hSecond : MemLp (fun x => E x * K x i) 2 (cellMeasure c m) := by
    apply (memLp_cellMeasure_iff c m).2
    have heq : (fun x => bracket x ^ m * (E x * K x i)) =
        fun x => (bracket x ^ m * E x) * K x i := by
      funext x
      ring
    rw [heq]
    exact hWeightedK
  have hsum : MemLp (fun x => v x i * w x + E x * K x i) 2 (cellMeasure c m) :=
    hFirst.add hSecond
  have heq : (fun x => physicalFlux hm v E w hcirc x i) =ᵐ[cellMeasure c m]
      fun x => v x i * w x + E x * K x i := by
    filter_upwards [(cellMeasure_ac c m).ae_le (coeFn_realPartVelocityLp
      (UnforcedLeray.B0583.velocity c hm w hcirc))] with x hx
    simp [physicalFlux, realBiotSavart, K, hx, realPartVelocityCLM_apply,
      smul_eq_mul, mul_comm]
  exact (memLp_congr_ae heq).mpr hsum

/-- The physical train flux at age `s`, with coefficients taken from the actual B0238 train
solution and its vorticity `Ec = curl(Vc)`. -/
def trainPhysicalFlux {ν c m : ℝ} [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c)
    (s : ℝ) (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0) : Plane → Vec :=
  physicalFlux hm (UnforcedLeray.B0238.Vc tr s) (UnforcedLeray.B0238.Ec tr s) w hcirc

/-- The actual train flux is in `X_m²` once its coefficients satisfy the stated weighted bounds.
Continuity is supplied from the train's proved smoothness and the identity `Ec = curl(Vc)`. -/
theorem memLp_trainPhysicalFlux {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    ∀ i : Fin 2, MemLp (fun x => trainPhysicalFlux tr s hm w hcirc x i) 2
      (cellMeasure c m) := by
  have hvsmooth := UnforcedLeray.B0238.contDiff_Vc tr hs
  have hv : Continuous (UnforcedLeray.B0238.Vc tr s) := hvsmooth.continuous
  have hE : Continuous (UnforcedLeray.B0238.Ec tr s) := by
    unfold UnforcedLeray.B0238.Ec
    exact UnforcedLeray.B0238.continuous_curl (hvsmooth.of_le (by norm_num))
  simpa [trainPhysicalFlux] using
    memLp_physicalFlux hm (UnforcedLeray.B0238.Vc tr s) (UnforcedLeray.B0238.Ec tr s)
      w hcirc hCv hCE hv hE hvBound hEBound

/-- The actual train flux as a pair of `X_m` elements. -/
def trainPhysicalFluxX {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) : Fin 2 → X c m :=
  fun i =>
    (memLp_trainPhysicalFlux tr hs hm w hcirc hCv hCE hvBound hEBound i).toLp _

/-- Rotated train flux used by B0610's curl convention to represent the negative divergence of
the physical transport flux. -/
def trainRotatedFluxX {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) : Fin 2 → X c m :=
  let F := trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound
  ![-F 1, F 0]

/-- The actual linearized vorticity source at age `s`, formed by applying B0610's `curlSource`
to the flux of the B0238 train and the B0583 real K_c reconstruction. -/
def trainPhysicalSource {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) : Hneg c m :=
  UnforcedLeray.B0610.curlSource c m
    (trainRotatedFluxX tr hs hm w hcirc hCv hCE hvBound hEBound)

/-- Weak pairing of the actual train source is exactly `∫ F·∇ψ`, i.e. the distribution
`-div(F)` for the physical transport flux `F=v w+(K_cw)E`. -/
theorem trainPhysicalSource_apply {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (ψ : H1 c (-m)) :
    trainPhysicalSource tr hs hm w hcirc hCv hCE hvBound hEBound ψ =
      (∫ x in cell c, trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 0 x *
        ψ.der 0 x) +
      ∫ x in cell c, trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 x *
        ψ.der 1 x := by
  rw [trainPhysicalSource, UnforcedLeray.B0610.curlSource_apply]
  simp only [trainRotatedFluxX, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrot : (fun x : Plane =>
      (-trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 : X c m) x *
        ψ.der 1 x) =ᵐ[volume.restrict (cell c)] fun x =>
      -(trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 x * ψ.der 1 x) := by
    filter_upwards [(ac_cellMeasure c m).ae_le (Lp.coeFn_neg
      (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1))] with x hx
    rw [hx]
    simp only [Pi.neg_apply]
    ring
  have hneg : ∫ x in cell c,
      (-trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 : X c m) x *
        ψ.der 1 x = -∫ x in cell c,
          trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 x * ψ.der 1 x := by
    calc ∫ x in cell c,
          (-trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 : X c m) x *
            ψ.der 1 x
        = ∫ x in cell c,
            -(trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 x * ψ.der 1 x) := by
              apply integral_congr_ae
              filter_upwards [hrot] with x hx
              exact hx
      _ = _ := by rw [integral_neg]
  rw [hneg]
  ring

/-- The actual train linearized source has zero circulation in the B0610 weighted pivot. -/
theorem trainPhysicalSource_hasZeroCirculation {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (hmhalf : 1 / 2 < m) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    UnforcedLeray.B0610.HasZeroCirculation c m hmhalf
      (trainPhysicalSource tr hs hm w hcirc hCv hCE hvBound hEBound) :=
  UnforcedLeray.B0610.hasZeroCirculation_curlSource hmhalf _

/-- B0610's norm estimate for the actual train source, in terms of its two physical flux columns. -/
theorem norm_trainPhysicalSource_le {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    ‖trainPhysicalSource tr hs hm w hcirc hCv hCE hvBound hEBound‖ ≤
      ‖trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 0‖ +
      ‖trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1‖ := by
  have h := UnforcedLeray.B0610.norm_curlSource_le
    (trainRotatedFluxX tr hs hm w hcirc hCv hCE hvBound hEBound)
  simpa [trainPhysicalSource, trainRotatedFluxX, add_comm] using h

/-- The physical flux, realized componentwise as an actual pair of elements of `X_m`. -/
def physicalFluxX {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) : Fin 2 → X c m :=
  fun i => (memLp_physicalFlux hm v E w hcirc hCv hCE hv hE hvBound hEBound i).toLp _

/-- Rotate the transport flux `F` to `(-F_η,F_q)` before passing it to B0610's scalar-curl
source. This is the orientation for which `curlSource (J F) = -div F` distributionally. -/
def rotatedPhysicalFluxX {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) : Fin 2 → X c m := by
  let F := physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound
  exact ![-F 1, F 0]

@[simp] theorem rotatedPhysicalFluxX_zero {c m : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0) {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E) (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    rotatedPhysicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 0 =
      -physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 := rfl

@[simp] theorem rotatedPhysicalFluxX_one {c m : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0) {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E) (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    rotatedPhysicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 =
      physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 0 := rfl

/-- The resulting actual zero-circulation linearized source `-curl(physicalFlux)`. -/
def physicalLinearizedSource {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) : Hneg c m :=
  UnforcedLeray.B0610.curlSource c m
    (rotatedPhysicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound)

/-- Pairing identity that fixes the orientation: the source generated from the rotated physical
transport flux is the weak distribution `-div(F)`. -/
theorem physicalLinearizedSource_apply {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (w : X c m)
    (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) (ψ : H1 c (-m)) :
    physicalLinearizedSource hm v E w hcirc hCv hCE hv hE hvBound hEBound ψ =
      (∫ x in cell c,
        physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 0 x * ψ.der 0 x) +
      ∫ x in cell c,
        physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 x * ψ.der 1 x := by
  rw [physicalLinearizedSource, UnforcedLeray.B0610.curlSource_apply]
  simp only [rotatedPhysicalFluxX, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrot : (fun x : Plane =>
      (-physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 : X c m) x *
        ψ.der 1 x) =ᵐ[volume.restrict (cell c)] fun x =>
      -(physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 x * ψ.der 1 x) := by
    filter_upwards [(ac_cellMeasure c m).ae_le (Lp.coeFn_neg
      (physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1))] with x hx
    rw [hx]
    simp only [Pi.neg_apply]
    ring
  have hneg : ∫ x in cell c,
      (-physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 : X c m) x *
        ψ.der 1 x = -∫ x in cell c,
          physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 x * ψ.der 1 x := by
    calc ∫ x in cell c,
          (-physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 : X c m) x *
            ψ.der 1 x
        = ∫ x in cell c,
            -(physicalFluxX hm v E w hcirc hCv hCE hv hE hvBound hEBound 1 x * ψ.der 1 x) := by
              apply integral_congr_ae
              filter_upwards [hrot] with x hx
              exact hx
      _ = _ := by rw [integral_neg]
  rw [hneg]
  ring

/-- B0610's topological zero-circulation fact applies to the concrete physical source. -/
theorem physicalLinearizedSource_hasZeroCirculation {c m : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (hmhalf : 1 / 2 < m) (v : Plane → Vec) (E : Plane → ℝ)
    (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hv : Continuous v) (hE : Continuous E)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    UnforcedLeray.B0610.HasZeroCirculation c m hmhalf
      (physicalLinearizedSource hm v E w hcirc hCv hCE hv hE hvBound hEBound) :=
  UnforcedLeray.B0610.hasZeroCirculation_curlSource hmhalf _

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
