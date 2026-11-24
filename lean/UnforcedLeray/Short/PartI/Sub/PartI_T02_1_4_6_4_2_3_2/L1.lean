import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

theorem leafCellTestPartialCH_proof : UnforcedLeray.Short.PartI.LeafCellTestPartialCH := by
  unfold LeafCellTestPartialCH
  intro c ψ hψ
  unfold IsCellTest at hψ ⊢
  obtain ⟨hsm, hper, R, hR⟩ := hψ
  -- smoothness of the partials
  have hsmQ : ContDiff ℝ ∞ (Cyl.partialQ ψ) := by
    refine contDiff_infty.2 fun n => ?_
    exact Cyl.contDiff_partialQ (n := (n : WithTop ℕ∞))
      (by have h := contDiff_infty.1 hsm (n + 1); exact_mod_cast h)
  have hsmE : ContDiff ℝ ∞ (Cyl.partialEta ψ) := by
    refine contDiff_infty.2 fun n => ?_
    exact Cyl.contDiff_partialEta (n := (n : WithTop ℕ∞))
      (by have h := contDiff_infty.1 hsm (n + 1); exact_mod_cast h)
  -- vanishing for large |η|
  have hzQ : ∀ z : Plane, R < |z.2| → Cyl.partialQ ψ z = 0 := by
    intro z hz
    have hfun : (fun q : ℝ => ψ (q, z.2)) = fun _ => 0 :=
      funext fun q => hR (q, z.2) hz
    show deriv (fun q : ℝ => ψ (q, z.2)) z.1 = 0
    rw [hfun, deriv_const]
  have hzE : ∀ z : Plane, R < |z.2| → Cyl.partialEta ψ z = 0 := by
    intro z hz
    have hev : (fun η : ℝ => ψ (z.1, η)) =ᶠ[𝓝 z.2] fun _ => 0 := by
      have h1 : ∀ᶠ η in 𝓝 z.2, R < |η| :=
        (continuous_abs.tendsto z.2).eventually (lt_mem_nhds hz)
      filter_upwards [h1] with η hη
      exact hR (z.1, η) hη
    show deriv (fun η : ℝ => ψ (z.1, η)) z.2 = 0
    rw [hev.deriv_eq, deriv_const]
  exact ⟨⟨hsmQ, Cyl.IsPeriodic.partialQ hper, R, hzQ⟩,
    ⟨hsmE, Cyl.IsPeriodic.partialEta hper, R, hzE⟩⟩
