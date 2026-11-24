import UnforcedLeray.Lib.HeatCylinder.PeriodicLift
import UnforcedLeray.Lib.CylinderB.Space
import UnforcedLeray.Lib.SobolevC.CylDensity
import UnforcedLeray.Lib.Train.Ops

/-!
# Smooth periodic density in centered-cell vector `L²`

An arbitrary centered-cell `L²` class is extended by its actual measurable periodic lift, then
viewed as an order-zero Sobolev graph. The weak identity is the empty-word identity, and the
cylinder smooth-density theorem gives compact-axial periodic approximants.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private abbrev W0 (c : ℝ) :=
  UnforcedLeray.Sob.W (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2

private theorem wμ_zero_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private noncomputable def centeredVecRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) : Plane → Vec :=
  centeredPerLift hc (AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x))

private theorem centeredVecRep_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) :
    centeredVecRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c] (x : Plane → Vec) := by
  filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c),
    (Lp.aestronglyMeasurable x).ae_eq_mk] with z hzcell hrep
  change centeredPerLift hc
    (AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x)) z =
      (x : Plane → Vec) z
  rw [centeredPerLift_eq_on_cell hc _ hzcell]
  exact hrep.symm

private theorem memLp_centeredVecRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) :
    MemLp (centeredVecRep hc x) 2 (UnforcedLeray.Cyl.cellμ c) :=
  (memLp_congr_ae (centeredVecRep_ae hc x)).mpr (Lp.memLp x)

private theorem centeredVecRep_memLpWμ {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) :
    MemLp (centeredVecRep hc x) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [wμ_zero_eq_cell]
  exact memLp_centeredVecRep hc x

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

private theorem centeredVecRep_weak0 {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) []
      (centeredVecRep hc x) (centeredVecRep hc x) := by
  apply UnforcedLeray.Sob.HasWeakDeriv.nil
  intro φ hφ
  exact UnforcedLeray.Sob.integrable_smul_of_memLp
    (UnforcedLeray.Sob.CompactlyBounded.of_adm hφ)
    (centeredVecRep_memLpWμ hc x)

/-- Every centered-cell vector `L²` class gives an order-zero cylinder Sobolev graph. -/
noncomputable def centeredVecW0 {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) : W0 c :=
  UnforcedLeray.Sob.W.ofFields (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2)
    (fun _ => centeredVecRep hc x) (fun _ => centeredVecRep_memLpWμ hc x) (by
      intro α
      have hα : α = UnforcedLeray.Sob.Idx.zero := idx20_eq_zero α
      subst α
      rw [UnforcedLeray.Cyl.word_zero]
      exact centeredVecRep_weak0 hc x)


/-- The value of the constructed order-zero graph is the original centered-cell `L²` class. -/
theorem centeredVecW0_value_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2 (centeredVecW0 hc x) : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] (x : Plane → Vec) := by
  change ((centeredVecRep_memLpWμ hc x).toLp (centeredVecRep hc x) : Plane → Vec) =ᵐ[
    UnforcedLeray.Cyl.cellμ c] (x : Plane → Vec)
  have hcoe := (centeredVecRep_memLpWμ hc x).coeFn_toLp
  have hcoe' : ((centeredVecRep_memLpWμ hc x).toLp (centeredVecRep hc x) : Plane → Vec) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] centeredVecRep hc x := by
    simpa only [wμ_zero_eq_cell] using hcoe
  exact hcoe'.trans (centeredVecRep_ae hc x)

#print axioms UnforcedLeray.HeatCylinder.centeredVecW0
#print axioms UnforcedLeray.HeatCylinder.centeredVecW0_value_ae

/-- Smooth compact-axial periodic fields approximate every centered-cell vector `L²` class
through the genuine order-zero Sobolev graph. -/
theorem exists_smooth_centeredVecW0_sequence {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) :
    ∃ y : ℕ → W0 c, ∃ u : ℕ → Plane → Vec,
      ∃ hu : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (u n),
        (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)) ∧
        Tendsto y atTop (𝓝 (centeredVecW0 hc x)) := by
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec)
    (k := 0) (p := 2) hc (by norm_num) (centeredVecW0 hc x)
  choose u hu hrep using hy
  refine ⟨y, u, hu, ?_, hlim⟩
  intro n
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have hrepW := (UnforcedLeray.Sob.ae_eq_wμ_iff
    (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
  filter_upwards [hrepW,
    UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2)
      hc (u n) (hu n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.exists_smooth_centeredVecW0_sequence
