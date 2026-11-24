import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

theorem leafParamIntIntegrableCH_proof : UnforcedLeray.Short.PartI.LeafParamIntIntegrableCH := by
  unfold LeafParamIntIntegrableCH
  intro c _hc ψ G hψ x
  unfold IsCellTest at hψ
  obtain ⟨hsm, _hper, R, hR⟩ := hψ
  have hcont : Continuous (fun z : Plane => ψ (z - x)) :=
    hsm.continuous.comp (continuous_id.sub continuous_const)
  have hv : Cyl.VanishesOutside (R + |x.2|) (fun z : Plane => ψ (z - x)) := by
    intro z hz
    apply hR
    show R < |(z - x).2|
    rw [Prod.snd_sub]
    have h1 := abs_sub_abs_le_abs_sub z.2 x.2
    linarith
  have hF : MemLp (fun z : Plane => ψ (z - x)) 2 (Cyl.cellμ c) :=
    Cyl.memLp_of_vanishes hcont hv 2
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hF.toLp _) G).congr ?_
  filter_upwards [MemLp.coeFn_toLp hF] with z hz
  simp only [hz]
