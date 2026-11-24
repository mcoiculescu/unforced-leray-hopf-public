import UnforcedLeray.Statement
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Jointly measurable representatives in the vocabulary of `UnforcedLeray.Statement`

`UnforcedLeray.IsTheoremASolution` (`lean/UnforcedLeray/Statement.lean`) asks for

* `velocity_measurable : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
    (volume.restrict (slab T))`,
* `gradient_measurable : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G z.1 i z.2)
    (volume.restrict (slab T))`,

while the analysis produces fields that are `L²`-continuous in time. This file applies the
abstract `exists_stronglyMeasurable_rep_of_continuousOn` (`Infra/JointMeasurableRep.lean`) to
`u : Velocity`, to families of spatial fields indexed by any type (in particular `Fin 3` for
`FirstDerivatives` and `Fin 3 × Fin 3` for `SecondDerivatives`), and records the shapes used by
`IsTheoremASolution`: the velocity is continuous on `Icc 0 T`, the derivatives only on every
`Icc δ T` with `δ > 0`, and both shapes give measurability on `slab T`.

The modified field `ũ` agrees with `u` a.e. at **every** time of `s`, and literally off `s`;
`toL2_congr_ae` and `l2Norm_congr_ae` show that the quantities of the statement built from
`toL2` and `l2Norm` do not change.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Infra.JointMeasurableRep

open UnforcedLeray

/-- `toL2` depends only on the a.e. class of the field. -/
theorem toL2_congr_ae {f g : SpatialField} (h : f =ᵐ[volume] g) : toL2 f = toL2 g := by
  by_cases hf : MemLp f 2 volume
  · have hg : MemLp g 2 volume := hf.ae_eq h
    rw [toL2_of_memLp hf, toL2_of_memLp hg]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 h
  · have hg : ¬ MemLp g 2 volume := fun h' => hf (h'.ae_eq h.symm)
    unfold toL2
    rw [dite_eq_right hf, dite_eq_right hg]

/-- `l2Norm` depends only on the a.e. class of the field. -/
theorem l2Norm_congr_ae {f g : SpatialField} (h : f =ᵐ[volume] g) : l2Norm f = l2Norm g := by
  unfold l2Norm
  rw [eLpNorm_congr_ae h]

/-- A modification that is a.e. equal at every time of `s` keeps `L²`-continuity on `s`. -/
theorem continuousOn_toL2_congr {u ũ : Velocity} {s : Set ℝ}
    (h : ∀ t ∈ s, ũ t =ᵐ[volume] u t) (hcont : ContinuousOn (fun t => toL2 (u t)) s) :
    ContinuousOn (fun t => toL2 (ũ t)) s :=
  hcont.congr fun t ht => toL2_congr_ae (h t ht)

/-- A modification that is a.e. equal at every time of `s` keeps `MemLp` on `s`. -/
theorem memLp_congr {u ũ : Velocity} {s : Set ℝ} (h : ∀ t ∈ s, ũ t =ᵐ[volume] u t)
    (hmem : ∀ t ∈ s, MemLp (u t) 2 volume) : ∀ t ∈ s, MemLp (ũ t) 2 volume :=
  fun t ht => (hmem t ht).ae_eq (h t ht).symm

/-- **Jointly measurable velocity.** Let `s ⊆ ℝ` be measurable and `u : Velocity` with
`u t ∈ L²` for `t ∈ s` and `t ↦ toL2 (u t)` continuous on `s`. Then there is `ũ : Velocity`
with `ũ t =ᵐ u t` for every `t ∈ s`, `ũ t = u t` for `t ∉ s`, and `(t, x) ↦ ũ t x` a.e.
strongly measurable on `s × ℝ³`, hence on `Ioo a b × ℝ³` whenever `Ioo a b ⊆ s`. -/
theorem exists_jointRep_velocity {u : Velocity} {s : Set ℝ} (hs : MeasurableSet s)
    (hmem : ∀ t ∈ s, MemLp (u t) 2 volume) (hcont : ContinuousOn (fun t => toL2 (u t)) s) :
    ∃ ũ : Velocity, (∀ t ∈ s, ũ t =ᵐ[volume] u t) ∧ (∀ t, t ∉ s → ũ t = u t) ∧
      AEStronglyMeasurable (fun z : SpaceTime => ũ z.1 z.2) (volume.restrict (s ×ˢ univ)) ∧
      ∀ a b : ℝ, Ioo a b ⊆ s →
        AEStronglyMeasurable (fun z : SpaceTime => ũ z.1 z.2)
          (volume.restrict (Ioo a b ×ˢ univ)) := by
  classical
  obtain ⟨F, hFm, hF⟩ :=
    exists_stronglyMeasurable_rep_of_continuousOn (μ := (volume : Measure Space)) hs hcont
  let ũ : Velocity := fun t x => if t ∈ s then F (t, x) else u t x
  have hũs : ∀ t ∈ s, ũ t = fun x => F (t, x) := fun t ht => by
    funext x
    simp [ũ, ht]
  have hmeas : AEStronglyMeasurable (fun z : SpaceTime => ũ z.1 z.2)
      (volume.restrict (s ×ˢ univ)) := by
    refine hFm.aestronglyMeasurable.congr ?_
    refine ae_restrict_of_forall_mem (hs.prod MeasurableSet.univ) fun z hz => ?_
    have hz1 : z.1 ∈ s := hz.1
    simp [ũ, hz1]
  refine ⟨ũ, fun t ht => ?_, fun t ht => ?_, hmeas, fun a b hab =>
    hmeas.mono_set (prod_mono hab subset_rfl)⟩
  · rw [hũs t ht]
    have h1 : (fun x => F (t, x)) =ᵐ[volume] (toL2 (u t) : SpatialField) := hF t ht
    exact h1.trans (coeFn_toL2 (hmem t ht))
  · funext x
    simp [ũ, ht]

/-- **Jointly measurable families.** The version of `exists_jointRep_velocity` for a family
`u : ℝ → ι → SpatialField` indexed by an arbitrary type `ι`, each member continuous in `L²` on
`s`; the same `ũ` serves all indices. -/
theorem exists_jointRep_family {ι : Type*} {u : ℝ → ι → SpatialField} {s : Set ℝ}
    (hs : MeasurableSet s) (hmem : ∀ t ∈ s, ∀ i, MemLp (u t i) 2 volume)
    (hcont : ∀ i, ContinuousOn (fun t => toL2 (u t i)) s) :
    ∃ ũ : ℝ → ι → SpatialField, (∀ t ∈ s, ∀ i, ũ t i =ᵐ[volume] u t i) ∧
      (∀ t, t ∉ s → ũ t = u t) ∧
      (∀ i, AEStronglyMeasurable (fun z : SpaceTime => ũ z.1 i z.2)
        (volume.restrict (s ×ˢ univ))) ∧
      ∀ a b : ℝ, Ioo a b ⊆ s → ∀ i,
        AEStronglyMeasurable (fun z : SpaceTime => ũ z.1 i z.2)
          (volume.restrict (Ioo a b ×ˢ univ)) := by
  have hex := fun i => exists_jointRep_velocity (u := fun t => u t i) hs
    (fun t ht => hmem t ht i) (hcont i)
  choose v hv1 hv2 hv3 hv4 using hex
  exact ⟨fun t i => v i t, fun t ht i => hv1 i t ht, fun t ht => funext fun i => hv2 i t ht,
    hv3, fun a b hab i => hv4 i a b hab⟩

/-- **Jointly measurable first derivatives** (`ι = Fin 3`, the shape of `FirstDerivatives`). -/
theorem exists_jointRep_firstDerivatives {G : FirstDerivatives} {s : Set ℝ}
    (hs : MeasurableSet s) (hmem : ∀ t ∈ s, ∀ i, MemLp (G t i) 2 volume)
    (hcont : ∀ i, ContinuousOn (fun t => toL2 (G t i)) s) :
    ∃ G' : FirstDerivatives, (∀ t ∈ s, ∀ i, G' t i =ᵐ[volume] G t i) ∧
      (∀ t, t ∉ s → G' t = G t) ∧
      (∀ i, AEStronglyMeasurable (fun z : SpaceTime => G' z.1 i z.2)
        (volume.restrict (s ×ˢ univ))) ∧
      ∀ a b : ℝ, Ioo a b ⊆ s → ∀ i,
        AEStronglyMeasurable (fun z : SpaceTime => G' z.1 i z.2)
          (volume.restrict (Ioo a b ×ˢ univ)) :=
  exists_jointRep_family hs hmem hcont

/-- **Jointly measurable second derivatives** (`Fin 3 × Fin 3`, the shape of
`SecondDerivatives`). -/
theorem exists_jointRep_secondDerivatives {H : SecondDerivatives} {s : Set ℝ}
    (hs : MeasurableSet s) (hmem : ∀ t ∈ s, ∀ i j, MemLp (H t i j) 2 volume)
    (hcont : ∀ i j, ContinuousOn (fun t => toL2 (H t i j)) s) :
    ∃ H' : SecondDerivatives, (∀ t ∈ s, ∀ i j, H' t i j =ᵐ[volume] H t i j) ∧
      (∀ t, t ∉ s → H' t = H t) ∧
      (∀ i j, AEStronglyMeasurable (fun z : SpaceTime => H' z.1 i j z.2)
        (volume.restrict (s ×ˢ univ))) ∧
      ∀ a b : ℝ, Ioo a b ⊆ s → ∀ i j,
        AEStronglyMeasurable (fun z : SpaceTime => H' z.1 i j z.2)
          (volume.restrict (Ioo a b ×ˢ univ)) := by
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_jointRep_family
    (u := fun t (ij : Fin 3 × Fin 3) => H t ij.1 ij.2) hs
    (fun t ht ij => hmem t ht ij.1 ij.2) (fun ij => hcont ij.1 ij.2)
  refine ⟨fun t i j => v t (i, j), fun t ht i j => hv1 t ht (i, j), fun t ht => ?_,
    fun i j => hv3 (i, j), fun a b hab i j => hv4 a b hab (i, j)⟩
  funext i j
  exact congrFun (hv2 t ht) (i, j)

/-! ### The shapes used by `IsTheoremASolution` -/

/-- Continuity on every `Icc δ T` with `0 < δ < T` (the form of
`positive_gradient_continuity`) gives continuity on `Ioc 0 T`. -/
theorem continuousOn_Ioc_of_forall_Icc {X : Type*} [TopologicalSpace X] {f : ℝ → X} {T : ℝ}
    (h : ∀ δ, 0 < δ → δ < T → ContinuousOn f (Icc δ T)) : ContinuousOn f (Ioc 0 T) := by
  intro t ht
  have hδ0 : 0 < t / 2 := half_pos ht.1
  have hδt : t / 2 < t := half_lt_self ht.1
  have hδT : t / 2 < T := hδt.trans_le ht.2
  have hmem : Icc (t / 2) T ∈ 𝓝[Ioc 0 T] t := by
    refine mem_nhdsWithin.2 ⟨Ioi (t / 2), isOpen_Ioi, hδt, ?_⟩
    rintro y ⟨hy1, hy2⟩
    exact ⟨le_of_lt hy1, hy2.2⟩
  exact (h (t / 2) hδ0 hδT t ⟨hδt.le, ht.2⟩).mono_of_mem_nhdsWithin hmem

/-- **`velocity_measurable` from `memL2` and `continuousL2`.** The hypotheses are the fields
`memL2` and `continuousL2` of `IsTheoremASolution`; the conclusion gives a modification `ũ`,
equal a.e. to `u` at every `t ∈ [0, T]` and equal to `u` elsewhere, satisfying
`velocity_measurable`. -/
theorem exists_jointRep_velocity_slab {T : ℝ} {u : Velocity}
    (hmem : ∀ t ∈ Icc (0 : ℝ) T, MemLp (u t) 2 volume)
    (hcont : ContinuousOn (fun t => toL2 (u t)) (Icc (0 : ℝ) T)) :
    ∃ ũ : Velocity, (∀ t ∈ Icc (0 : ℝ) T, ũ t =ᵐ[volume] u t) ∧
      (∀ t, t ∉ Icc (0 : ℝ) T → ũ t = u t) ∧
      AEStronglyMeasurable (fun z : SpaceTime => ũ z.1 z.2) (volume.restrict (slab T)) := by
  obtain ⟨ũ, h1, h2, -, h4⟩ := exists_jointRep_velocity measurableSet_Icc hmem hcont
  exact ⟨ũ, h1, h2, h4 0 T Ioo_subset_Icc_self⟩

/-- **`gradient_measurable` from `gradient_memL2` and `positive_gradient_continuity`.** The
hypotheses are those fields of `IsTheoremASolution`; the conclusion gives a modification `G'`,
equal a.e. to `G` at every `t ∈ (0, T]` and equal to `G` elsewhere, satisfying
`gradient_measurable`. -/
theorem exists_jointRep_gradient_slab {T : ℝ} {G : FirstDerivatives}
    (hmem : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hcont : ∀ δ, 0 < δ → δ < T → ∀ i, ContinuousOn (fun t => toL2 (G t i)) (Icc δ T)) :
    ∃ G' : FirstDerivatives, (∀ t ∈ Ioc (0 : ℝ) T, ∀ i, G' t i =ᵐ[volume] G t i) ∧
      (∀ t, t ∉ Ioc (0 : ℝ) T → G' t = G t) ∧
      ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G' z.1 i z.2)
        (volume.restrict (slab T)) := by
  obtain ⟨G', h1, h2, -, h4⟩ := exists_jointRep_firstDerivatives measurableSet_Ioc hmem
    (fun i => continuousOn_Ioc_of_forall_Icc fun δ hδ hδT => hcont δ hδ hδT i)
  exact ⟨G', h1, h2, h4 0 T Ioo_subset_Ioc_self⟩

/-- The second-derivative analogue of `exists_jointRep_gradient_slab`, from `second_memL2` and
`positive_second_continuity`. -/
theorem exists_jointRep_second_slab {T : ℝ} {H : SecondDerivatives}
    (hmem : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i j, MemLp (H t i j) 2 volume)
    (hcont : ∀ δ, 0 < δ → δ < T → ∀ i j, ContinuousOn (fun t => toL2 (H t i j)) (Icc δ T)) :
    ∃ H' : SecondDerivatives, (∀ t ∈ Ioc (0 : ℝ) T, ∀ i j, H' t i j =ᵐ[volume] H t i j) ∧
      (∀ t, t ∉ Ioc (0 : ℝ) T → H' t = H t) ∧
      ∀ i j, AEStronglyMeasurable (fun z : SpaceTime => H' z.1 i j z.2)
        (volume.restrict (slab T)) := by
  obtain ⟨H', h1, h2, -, h4⟩ := exists_jointRep_secondDerivatives measurableSet_Ioc hmem
    (fun i j => continuousOn_Ioc_of_forall_Icc fun δ hδ hδT => hcont δ hδ hδT i j)
  exact ⟨H', h1, h2, h4 0 T Ioo_subset_Ioc_self⟩

end UnforcedLeray.Infra.JointMeasurableRep
