import UnforcedLeray.Lib.HeatCylinder.HeatL2Density
import UnforcedLeray.Lib.TrainB.TensorBridge

/-!
# Smooth periodic density for the actual kernel tensor carrier

Every centered-cell two-column tensor L² class is the value of an order-zero cylinder Sobolev
field. Applying the existing cylinder smooth-density theorem gives compact-axial periodic tensor
approximants. This is the density supplier needed to extend the bounded-input kernel covariance.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.TrainB (TensorVal)

abbrev TensorW0 (c : ℝ) :=
  UnforcedLeray.Sob.W (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2

private theorem wμ_zero_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private noncomputable def centeredTensorRep {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) : Plane → TensorVal :=
  UnforcedLeray.HeatCylinder.centeredPerLift hc
    (AEStronglyMeasurable.mk (x : Plane → TensorVal) (Lp.aestronglyMeasurable x))

private theorem centeredTensorRep_ae {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) :
    centeredTensorRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c] (x : Plane → TensorVal) := by
  filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c),
    (Lp.aestronglyMeasurable x).ae_eq_mk] with z hzcell hrep
  change UnforcedLeray.HeatCylinder.centeredPerLift hc
    (AEStronglyMeasurable.mk (x : Plane → TensorVal) (Lp.aestronglyMeasurable x)) z =
      (x : Plane → TensorVal) z
  rw [UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell hc _ hzcell]
  exact hrep.symm

private theorem memLp_centeredTensorRep {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) :
    MemLp (centeredTensorRep hc x) 2 (UnforcedLeray.Cyl.cellμ c) :=
  (memLp_congr_ae (centeredTensorRep_ae hc x)).mpr (Lp.memLp x)

private theorem centeredTensorRep_memLpWμ {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) :
    MemLp (centeredTensorRep hc x) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [wμ_zero_eq_cell]
  exact memLp_centeredTensorRep hc x

private theorem idx20_eq_zero (α : UnforcedLeray.Sob.Idx 2 0) :
    α = UnforcedLeray.Sob.Idx.zero := by
  rcases α with ⟨j, w⟩
  have hj : j = 0 := by omega
  subst j
  have hw : w = fun i => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  subst w
  rfl

private theorem centeredTensorRep_weak0 {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) []
      (centeredTensorRep hc x) (centeredTensorRep hc x) := by
  apply UnforcedLeray.Sob.HasWeakDeriv.nil
  intro φ hφ
  exact UnforcedLeray.Sob.integrable_smul_of_memLp
    (UnforcedLeray.Sob.CompactlyBounded.of_adm hφ)
    (centeredTensorRep_memLpWμ hc x)

/-- An arbitrary centered-cell kernel tensor class as an order-zero Sobolev graph. -/
noncomputable def centeredTensorW0 {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) : TensorW0 c :=
  UnforcedLeray.Sob.W.ofFields (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal) (k := 0) (p := 2)
    (fun _ => centeredTensorRep hc x) (fun _ => centeredTensorRep_memLpWμ hc x) (by
      intro α
      have hα : α = UnforcedLeray.Sob.Idx.zero := idx20_eq_zero α
      subst α
      rw [UnforcedLeray.Cyl.word_zero]
      exact centeredTensorRep_weak0 hc x)

/-- Every kernel tensor class has a sequence of compact-axial smooth periodic approximants. -/
theorem exists_smooth_centeredTensorW0_sequence {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) :
    ∃ y : ℕ → TensorW0 c, ∃ u : ℕ → Plane → TensorVal,
      ∃ hu : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (u n),
        (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := TensorVal) (k := 0)
          (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)) ∧
        Tendsto y atTop (𝓝 (centeredTensorW0 hc x)) := by
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal)
    (k := 0) (p := 2) hc (by norm_num) (centeredTensorW0 hc x)
  choose u hu hrep using hy
  refine ⟨y, u, hu, ?_, hlim⟩
  intro n
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have hrepW := (UnforcedLeray.Sob.ae_eq_wμ_iff
    (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
  filter_upwards [hrepW,
    UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal) (k := 0)
      (p := 2) hc (u n) (hu n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

/-- The value of the constructed order-zero tensor graph is the original centered-cell class. -/
theorem centeredTensorW0_value_ae {c : ℝ} (hc : 0 < c)
    (x : Lp TensorVal 2 (UnforcedLeray.Cyl.cellμ c)) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 (centeredTensorW0 hc x) :
        Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c] (x : Plane → TensorVal) := by
  change ((centeredTensorRep_memLpWμ hc x).toLp (centeredTensorRep hc x) :
      Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c] (x : Plane → TensorVal)
  have hcoe := (centeredTensorRep_memLpWμ hc x).coeFn_toLp
  have hcoe' : ((centeredTensorRep_memLpWμ hc x).toLp (centeredTensorRep hc x) :
      Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c] centeredTensorRep hc x := by
    simpa only [wμ_zero_eq_cell] using hcoe
  exact hcoe'.trans (centeredTensorRep_ae hc x)

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.exists_smooth_centeredTensorW0_sequence
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.centeredTensorW0_value_ae
