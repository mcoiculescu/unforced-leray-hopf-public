import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.SmoothSeq_Sub

/-!
# Part I, task `PartI:T02/1/2/3/1/2/2/1`: smooth approximation of `H³` classes

Source of record: `the November 2 reference manuscript`, lines 261-288.

Proves the leaf `BdpSmoothFun` from `Short/PartI/Sub/PartI_T02_1_2_3_1_2/SmoothSeq_Sub.lean`.
Take the smooth periodic `f n` of `TrainB.exists_h3_uniform_representative_sequence`:
* `Fseq n = f n` converges uniformly to a bounded continuous `F`, so the `f n` and `F` are
  bounded by a common `M = max C ‖F‖`; `F` equals the `H³` value of `x` a.e. on `cellμ c`.
* the `H³` convergence `xseq → x` gives `L²` convergence of `f n` to the value of `x`,
  since `Sob.W.value` is continuous into `L²` and `W.value_ofCylSmooth` identifies its
  value on the smooth elements with `f n` a.e.
* `(Sob.cylinder c).μ = cellμ c` and the weight `ρwW c ^ 0` is `1`, so the measure of
  the value space is `(Sob.cylinder c).μ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem bdp_smoothFun : UnforcedLeray.Short.PartI.BdpSmoothFun := by
  intro c hc x
  obtain ⟨xseq, f, hf, F, Fseq, hxrep, hFseq, hFlim, hFae, hxlim⟩ :=
    exists_h3_uniform_representative_sequence hc x
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto Fseq hFlim)
  have hMC : C ≤ max C ‖F‖ := le_max_left _ _
  have hMF : ‖F‖ ≤ max C ‖F‖ := le_max_right _ _
  -- transport an `ae` statement from `cellμ c` to `(Sob.cylinder c).μ`
  have hcyl : ∀ P : Plane → Prop, (∀ᵐ z ∂Cyl.cellμ c, P z) →
      ∀ᵐ z ∂(Sob.cylinder c).μ, P z := by
    intro P h
    rw [Cyl.cylinder_μ_eq]
    exact h
  -- the value measure of `H³` at weight exponent zero is `(Sob.cylinder c).μ`
  have hmeas : Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = (Sob.cylinder c).μ := by
    rw [scalarH2_measure_eq_cell, Cyl.cylinder_μ_eq]
  have hE : ∀ g : Plane → ℝ,
      eLpNorm g 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) =
        eLpNorm g 2 (Sob.cylinder c).μ :=
    fun g => congrArg (fun m => eLpNorm g 2 m) hmeas
  -- `H³` convergence gives `L²` convergence of the values
  have hVlim : Tendsto (fun n => Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ ℝ 3 2 (xseq n)) atTop
      (𝓝 (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x)) :=
    ((Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2).continuous.tendsto x).comp
      hxlim
  have hVf : ∀ n, (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (xseq n) :
      Plane → ℝ) =ᵐ[Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))] f n := by
    intro n
    rw [hxrep n]
    exact Sob.W.value_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ) (k := 3)
      (p := 2) (by linarith) (f n) (hf n)
  have hEq : ∀ n, eLpNorm (f n - (Cyl.H.val x : Plane → ℝ)) 2 (Sob.cylinder c).μ =
      edist (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (xseq n))
        (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) := by
    intro n
    rw [Lp.edist_def, ← hE]
    exact eLpNorm_congr_ae ((hVf n).symm.sub Filter.EventuallyEq.rfl)
  have hLp : Tendsto (fun n => edist (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ ℝ 3 2 (xseq n))
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.mp hVlim
  refine ⟨f, hf, max C ‖F‖, ?_, ?_, ?_, ?_⟩
  · exact Tendsto.congr hxrep hxlim
  · refine hcyl (fun z => |(Cyl.H.val x : Plane → ℝ) z| ≤ max C ‖F‖) ?_
    filter_upwards [hFae] with z hz
    have h1 : |(F : Plane → ℝ) z| ≤ max C ‖F‖ := by
      have h := (BoundedContinuousFunction.norm_coe_le_norm F z).trans hMF
      rwa [Real.norm_eq_abs] at h
    rw [hz] at h1
    exact h1
  · intro n
    refine ae_of_all _ (fun z => ?_)
    have h1 := (BoundedContinuousFunction.norm_coe_le_norm (Fseq n) z).trans (hC _ ⟨n, rfl⟩)
    rw [hFseq n z, Real.norm_eq_abs] at h1
    exact h1.trans hMC
  · exact Tendsto.congr (fun n => (hEq n).symm) hLp

end UnforcedLeray.Short.PartI
