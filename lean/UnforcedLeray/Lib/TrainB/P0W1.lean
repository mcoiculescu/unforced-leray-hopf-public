import UnforcedLeray.Lib.TrainB.P0Quotient
import UnforcedLeray.Lib.SobolevC.CylDensity

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The unweighted first-order cylinder Sobolev graph for the actual train velocity carrier. -/
abbrev VecH1 (c : ℝ) := Cyl.H ℝ Vec2 c 0 1

/-- At exponent zero, the H¹ value measure is exactly the centered unnormalized cell measure. -/
theorem vecH1_measure_eq_cell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW, Cyl.wμ]
  have h : (fun z => ENNReal.ofReal (Cyl.ρw c z ^ (0 : ℝ))) = 1 := by
    funext z
    simp
  rw [h, withDensity_one]

/-- Equality of measures gives the canonical isometric equivalence of their L² carriers. -/
noncomputable def lpVecMeasureEquiv {μ ν : Measure UnforcedLeray.Cyl.Plane}
    (hμ : μ = ν) : Lp UnforcedLeray.Cyl.Vec2 2 μ ≃ₗᵢ[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2 ν := by
  cases hμ
  exact LinearIsometryEquiv.refl ℝ _

/-- The zero-order component of `VecH1`, viewed in the actual cylinder `L²` carrier. -/
noncomputable def vecH1ValueCell {c : ℝ} (x : VecH1 c) : UnforcedLeray.Cyl.L2v c := by
  let v : Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ UnforcedLeray.Cyl.Vec2 1 2 x
  have hType :
      (Lp UnforcedLeray.Cyl.Vec2 2
        (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) : Type) =
      (Lp UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c) : Type) :=
    congrArg (fun μ : Measure UnforcedLeray.Cyl.Plane =>
      (Lp UnforcedLeray.Cyl.Vec2 2 μ : Type)) (vecH1_measure_eq_cell c)
  exact hType.mp v

/-- The horizontal weak derivative component of `VecH1`, viewed in cylinder `L²`. -/
noncomputable def vecH1DqCell {c : ℝ} (x : VecH1 c) : UnforcedLeray.Cyl.L2v c := by
  let v : Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ UnforcedLeray.Cyl.Vec2 1 2
      (Sob.Idx.cons 0 Sob.Idx.zero) x
  have hType :
      (Lp UnforcedLeray.Cyl.Vec2 2
        (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) : Type) =
      (Lp UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c) : Type) :=
    congrArg (fun μ : Measure UnforcedLeray.Cyl.Plane =>
      (Lp UnforcedLeray.Cyl.Vec2 2 μ : Type)) (vecH1_measure_eq_cell c)
  exact hType.mp v

/-- The axial weak derivative component of `VecH1`, viewed in cylinder `L²`. -/
noncomputable def vecH1DetaCell {c : ℝ} (x : VecH1 c) : UnforcedLeray.Cyl.L2v c := by
  let v : Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ UnforcedLeray.Cyl.Vec2 1 2
      (Sob.Idx.cons 1 Sob.Idx.zero) x
  have hType :
      (Lp UnforcedLeray.Cyl.Vec2 2
        (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) : Type) =
      (Lp UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c) : Type) :=
    congrArg (fun μ : Measure UnforcedLeray.Cyl.Plane =>
      (Lp UnforcedLeray.Cyl.Vec2 2 μ : Type)) (vecH1_measure_eq_cell c)
  exact hType.mp v

/-- Continuous linear value projection from `VecH1` into actual cylinder `L²`. -/
noncomputable def vecH1ValueCellCLM {c : ℝ} : VecH1 c →L[ℝ] UnforcedLeray.Cyl.L2v c := by
  let hVal : VecH1 c →L[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2
        (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Sob.W.value (Sob.cylinder c)
      (Cyl.ρwW c ^ (0 : ℝ)) ℝ UnforcedLeray.Cyl.Vec2 1 2
  let hIso : Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) →L[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c) :=
    (lpVecMeasureEquiv (vecH1_measure_eq_cell c)).toLinearIsometry.toContinuousLinearMap
  exact hIso.comp hVal

/-- Continuous linear horizontal derivative projection into actual cylinder `L²`. -/
noncomputable def vecH1DqCellCLM {c : ℝ} : VecH1 c →L[ℝ] UnforcedLeray.Cyl.L2v c := by
  let hDq : VecH1 c →L[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2
        (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ
      UnforcedLeray.Cyl.Vec2 1 2 (Sob.Idx.cons 0 Sob.Idx.zero)
  let hIso : Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) →L[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c) :=
    (lpVecMeasureEquiv (vecH1_measure_eq_cell c)).toLinearIsometry.toContinuousLinearMap
  exact hIso.comp hDq

/-- Continuous linear axial derivative projection into actual cylinder `L²`. -/
noncomputable def vecH1DetaCellCLM {c : ℝ} : VecH1 c →L[ℝ] UnforcedLeray.Cyl.L2v c := by
  let hDeta : VecH1 c →L[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2
        (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ
      UnforcedLeray.Cyl.Vec2 1 2 (Sob.Idx.cons 1 Sob.Idx.zero)
  let hIso : Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) →L[ℝ]
      Lp UnforcedLeray.Cyl.Vec2 2 (UnforcedLeray.Cyl.cellμ c) :=
    (lpVecMeasureEquiv (vecH1_measure_eq_cell c)).toLinearIsometry.toContinuousLinearMap
  exact hIso.comp hDeta

/-- Smooth cylinder density with the actual smooth representative retained as an equality in
`VecH1`. -/
theorem exists_smoothVecH1_sequence {c : ℝ} (hc : 0 < c) (x : VecH1 c) :
    ∃ y : ℕ → VecH1 c, ∃ f : ℕ → UnforcedLeray.Cyl.Plane → Vec2,
      ∃ hf : ∀ n, Sob.IsCylSmooth c (f n),
      (∀ n, y n = Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (f n) (hf n)) ∧
      Tendsto y atTop (𝓝 x) := by
  obtain ⟨y, hy, hlim⟩ := Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := 1) (p := 2) hc (by norm_num) x
  choose f hf hrep using hy
  refine ⟨y, f, hf, ?_, hlim⟩
  intro n
  apply Sob.W.value_injective
  apply Lp.ext
  have hrepW := (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ
    (Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
  filter_upwards [hrepW,
    Sob.W.value_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (f n) (hf n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.vecH1_measure_eq_cell
#print axioms UnforcedLeray.TrainB.lpVecMeasureEquiv
#print axioms UnforcedLeray.TrainB.vecH1ValueCellCLM
#print axioms UnforcedLeray.TrainB.vecH1DqCellCLM
#print axioms UnforcedLeray.TrainB.vecH1DetaCellCLM
#print axioms UnforcedLeray.TrainB.vecH1ValueCell
#print axioms UnforcedLeray.TrainB.vecH1DqCell
#print axioms UnforcedLeray.TrainB.vecH1DetaCell
#print axioms UnforcedLeray.TrainB.exists_smoothVecH1_sequence
