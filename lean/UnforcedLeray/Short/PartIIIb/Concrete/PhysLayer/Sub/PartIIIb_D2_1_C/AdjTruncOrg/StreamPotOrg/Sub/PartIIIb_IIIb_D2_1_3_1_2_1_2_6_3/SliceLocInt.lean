import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PotLocIntCell
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.YrLocIntCell
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PotMeasPeriodic
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.AePeriodicExtend

/-!
# SliceLocInt

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of
the stream potential) and 1334-1337 (`Y_r`).

Slices of `bsPot Φ` and `Dψ j` are locally integrable on one period by `potLocIntCell` and
`yrLocIntCell` (Fubini on the product of the period with a ball). The statement is then extended to
all `t` by `aePeriodicExtend`, using a.e. periodicity of the slices.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.IIb (IsInYr HasPtwOp)

theorem sliceLocInt : SliceLocInt := by
  intro P Φ Dψ hW
  unfold WGHyp at hW
  obtain ⟨hP, hΦ, hD⟩ := hW
  have hDj : ∀ j : Fin 3, IsInYr P 2 (Dψ j) := fun j => (hD j).1
  -- slices over one period: a.e. `t ∈ (0,P]`, integrable on every ball `B_N`, `N : ℕ`
  have slice_ae : ∀ (F : ℝ × Space → CVec3) (R : ℝ),
      IntegrableOn F (Ioc 0 P ×ˢ closedBall (0 : Space) R) volume →
      ∀ᵐ t ∂(volume.restrict (Ioc 0 P)),
        IntegrableOn (fun y : Space => F (t, y)) (closedBall (0 : Space) R) volume := by
    intro F R hF
    have hprod : Integrable F
        ((volume.restrict (Ioc 0 P)).prod (volume.restrict (closedBall (0 : Space) R))) := by
      rw [Measure.prod_restrict]
      exact hF
    exact hprod.prod_right_ae
  have hΦae : ∀ N : ℕ, ∀ᵐ t ∂(volume.restrict (Ioc 0 P)),
      IntegrableOn (fun y : Space => bsPot Φ (t, y)) (closedBall (0 : Space) (N : ℝ)) volume :=
    fun N => slice_ae _ _ (potLocIntCell P hP Φ hΦ (N : ℝ))
  have hDae : ∀ j : Fin 3, ∀ N : ℕ, ∀ᵐ t ∂(volume.restrict (Ioc 0 P)),
      IntegrableOn (fun y : Space => Dψ j (t, y)) (closedBall (0 : Space) (N : ℝ)) volume :=
    fun j N => slice_ae _ _ (yrLocIntCell P hP (Dψ j) (hDj j) (N : ℝ))
  have hΦall : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), ∀ N : ℕ,
      IntegrableOn (fun y : Space => bsPot Φ (t, y)) (closedBall (0 : Space) (N : ℝ)) volume :=
    ae_all_iff.2 hΦae
  have hDall : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), ∀ j : Fin 3, ∀ N : ℕ,
      IntegrableOn (fun y : Space => Dψ j (t, y)) (closedBall (0 : Space) (N : ℝ)) volume :=
    ae_all_iff.2 (fun j => ae_all_iff.2 (hDae j))
  have hbase : ∀ᵐ t ∂(volume.restrict (Ioc 0 P)), ∀ R : ℝ,
      IntegrableOn (fun y : Space => bsPot Φ (t, y)) (closedBall (0 : Space) R) volume ∧
        ∀ j : Fin 3, IntegrableOn (fun y : Space => Dψ j (t, y)) (closedBall (0 : Space) R) volume := by
    filter_upwards [hΦall, hDall] with t h1 h2
    intro R
    refine ⟨?_, ?_⟩
    · exact (h1 ⌈R⌉₊).mono_set (closedBall_subset_closedBall (Nat.le_ceil R))
    · intro j
      exact (h2 j ⌈R⌉₊).mono_set (closedBall_subset_closedBall (Nat.le_ceil R))
  -- a.e. periodicity of the slices
  have hΦPer : ∀ᵐ t : ℝ, ∀ᵐ y : Space, bsPot Φ (t + P, y) = bsPot Φ (t, y) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => bsPot Φ (z.1 + P, z.2) = bsPot Φ z)
      (potMeasPeriodic P hP Φ hΦ).2
  have hDPer : ∀ᵐ t : ℝ, ∀ j : Fin 3, ∀ᵐ y : Space, Dψ j (t + P, y) = Dψ j (t, y) :=
    ae_all_iff.2 (fun j =>
      Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => Dψ j (z.1 + P, z.2) = Dψ j z)
        (hDj j).periodic)
  have transfer : ∀ (F G : Space → CVec3) (S : Set Space), F =ᵐ[volume] G →
      (IntegrableOn F S volume ↔ IntegrableOn G S volume) := by
    intro F G S h
    exact ⟨fun hF => hF.congr_fun_ae (ae_restrict_of_ae h),
      fun hG => hG.congr_fun_ae (ae_restrict_of_ae h.symm)⟩
  refine aePeriodicExtend P hP
    (fun t : ℝ => ∀ R : ℝ, IntegrableOn (fun y : Space => bsPot Φ (t, y)) (closedBall (0 : Space) R)
        volume ∧
      ∀ j : Fin 3, IntegrableOn (fun y : Space => Dψ j (t, y)) (closedBall (0 : Space) R) volume)
    hbase ?_
  filter_upwards [hΦPer, hDPer] with t hΦt hDt
  exact forall_congr' (fun R => and_congr
    (transfer (fun y => bsPot Φ (t + P, y)) (fun y => bsPot Φ (t, y)) _ hΦt)
    (forall_congr' (fun j => transfer (fun y => Dψ j (t + P, y)) (fun y => Dψ j (t, y)) _
      (hDt j))))
