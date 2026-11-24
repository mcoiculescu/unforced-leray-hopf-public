import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ActualValue
import UnforcedLeray.Lib.HeatCylinder.H3Operator
import UnforcedLeray.Lib.HeatCylinder.SmoothCLM

/-!
# Actual ordinary heat on arbitrary centered vector H³ classes

The smooth Gaussian convolution extends by its proved graph contraction, and the normalized-cell
value of the extension is the actual quotient-valued Gaussian heat CLM.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem ofCylSmooth_vec_sub_eq {c : ℝ} (hc : 0 < c)
    {T U : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc (fun z => T z - U z)
      (isCylSmooth_sub hT hU) =
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc T hT -
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc U hU := by
  let X := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc T hT
  let Y := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc U hU
  have hmap := map_sub (UnforcedLeray.Sob.W.value
      (UnforcedLeray.Sob.cylinder c) (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      ℝ Vec 3 2) X Y
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc (fun z => T z - U z)
      (isCylSmooth_sub hT hU),
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc T hT,
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc U hU,
    Lp.coeFn_sub
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 X)
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 Y)] with z hDiff hTval hUval hsub
  have hmapz := congrArg (fun f : Lp Vec 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → Vec) z) hmap
  simp only [Pi.sub_apply] at hsub
  rw [hmapz, hDiff, hsub, hTval, hUval]


private theorem vectorH3NormalizedValue_sub_local {c : ℝ} (hc : 0 < c)
    (x y : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    vectorH3NormalizedValue hc (x - y) =
      vectorH3NormalizedValue hc x - vectorH3NormalizedValue hc y := by
  rw [sub_eq_add_neg, vectorH3NormalizedValue_add hc]
  have hneg := vectorH3NormalizedValue_smul hc (-1) y
  have hneg' : vectorH3NormalizedValue hc (-y) = -vectorH3NormalizedValue hc y := by
    simpa only [neg_one_smul] using hneg
  rw [hneg']
  rfl

/-- The smooth ordinary heat response is linear in its actual periodic input. -/
theorem heatVecH3_sub {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    heatVecH3 hc hθ (isCylSmooth_sub hT hU) = heatVecH3 hc hθ hT - heatVecH3 hc hθ hU := by
  apply vectorH3NormalizedValue_injective hc
  rw [vectorH3NormalizedValue_heatVecH3 hc hθ (isCylSmooth_sub hT hU),
    vectorH3NormalizedValue_sub_local hc,
    ofCylSmooth_vec_sub_eq hc hT hU,
    vectorH3NormalizedValue_sub_local hc,
    vectorH3NormalizedValue_heatVecH3 hc hθ hT,
    vectorH3NormalizedValue_heatVecH3 hc hθ hU,
    map_sub]

private noncomputable def smoothHeatVecH3Sequence {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : ℕ → Plane → Vec} (hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n)) :
    ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
  fun n => heatVecH3 (c := c) (θ := θ) hc hθ (hT n)

/-- Smooth Gaussian heat outputs along any actual dense vector-H³ approximation converge in
centered H³, and their limit has the actual normalized quotient heat value. -/
theorem exists_tendsto_smoothHeatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    ∃ y : ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3,
    ∃ T : ℕ → Plane → Vec,
    ∃ hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n),
      (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc (T n) (hT n)) ∧
      Tendsto y atTop (𝓝 x) ∧
      ∃ Y : UnforcedLeray.Cyl.H ℝ Vec c 0 3,
        Tendsto (smoothHeatVecH3Sequence hc hθ hT) atTop (𝓝 Y) ∧
        vectorH3NormalizedValue hc Y =
          heatVecL2CLM hc θ (vectorH3NormalizedValue hc x) := by
  obtain ⟨y, T, hT, hyrep, hyLim⟩ := exists_smoothVectorH3_sequence hc x
  let u : ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
    smoothHeatVecH3Sequence hc hθ hT
  have hu : CauchySeq u := by
    refine (Metric.cauchySeq_iff (u := u)).2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hyLim.cauchySeq) ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hnorm : ‖u m - u n‖ ≤ ‖y m - y n‖ := by
      change ‖heatVecH3 (c := c) (θ := θ) hc hθ (hT m) -
        heatVecH3 (c := c) (θ := θ) hc hθ (hT n)‖ ≤ _
      rw [← heatVecH3_sub (c := c) (θ := θ) (T := T m) (U := T n)
        hc hθ (hT m) (hT n)]
      calc
        ‖heatVecH3 hc hθ (isCylSmooth_sub (hT m) (hT n))‖ ≤
            ‖UnforcedLeray.Sob.W.ofCylSmooth
              (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
              (F := Vec) (k := 3) (p := 2) hc
              (fun z => T m z - T n z) (isCylSmooth_sub (hT m) (hT n))‖ :=
          norm_heatVecH3_le_ofCylSmooth hc hθ (isCylSmooth_sub (hT m) (hT n))
        _ = ‖y m - y n‖ := by
          rw [ofCylSmooth_vec_sub_eq hc (hT m) (hT n), hyrep m, hyrep n]
    calc
      dist (u m) (u n) ≤ dist (y m) (y n) := by
        rw [dist_eq_norm, dist_eq_norm]
        exact hnorm
      _ < ε := hN m hm n hn
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hu
  have hvalueLim := tendsto_vectorH3NormalizedValue_of_tendsto hc hY
  have hinputLim := tendsto_vectorH3NormalizedValue_of_tendsto hc hyLim
  have hkernelLim := (heatVecL2CLM hc θ).continuous.tendsto
    (vectorH3NormalizedValue hc x) |>.comp hinputLim
  have hseq : (fun n => vectorH3NormalizedValue hc (u n)) =
      fun n => heatVecL2CLM hc θ (vectorH3NormalizedValue hc (y n)) := by
    funext n
    have h := vectorH3NormalizedValue_heatVecH3 hc hθ (hT n)
    simpa only [u, smoothHeatVecH3Sequence, hyrep n] using h
  have hkernelOut : Tendsto
      (fun n => vectorH3NormalizedValue hc (u n)) atTop
      (𝓝 (heatVecL2CLM hc θ (vectorH3NormalizedValue hc x))) := by
    rw [hseq]
    exact hkernelLim
  have hYvalue := tendsto_nhds_unique hvalueLim hkernelOut
  exact ⟨y, T, hT, hyrep, hyLim, Y, hY, hYvalue⟩

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3_sub
#print axioms UnforcedLeray.HeatCylinder.exists_tendsto_smoothHeatVecH3
