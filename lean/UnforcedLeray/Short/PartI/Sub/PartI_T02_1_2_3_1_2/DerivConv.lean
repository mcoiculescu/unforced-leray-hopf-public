import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.SmoothSeq_Sub

/-!
# Part I, task `PartI:T02/1/2/3/1/2/2/3`: convergence of smooth derivatives

Source of record: `the November 2 reference manuscript`, lines 261-288.

Proves the leaf `BdpDerivConv` from `Short/PartI/Sub/PartI_T02_1_2_3_1_2/SmoothSeq_Sub.lean`.
* `W.deriv (cons j zero)` is continuous, so `W.deriv (ofCylSmooth (f n)) → W.deriv x` in `L²`.
* `W.deriv_ofCylSmooth` identifies `W.deriv (ofCylSmooth (f n))` a.e. with the classical
  `fderiv (f n) · (dir j)` (`Sob.iterD` of the one-letter word `[dir j]`).
* `x'` is the weak `∂_j`-derivative of `x`, and `W.deriv (cons j zero) x` is another one;
  `HasWeakDeriv.ae_unique` identifies them a.e.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem bdp_derivConv : UnforcedLeray.Short.PartI.BdpDerivConv := by
  intro c hc j x x' hx f hf hfx
  -- the weak `∂_j` derivative of `x` computed by `W.deriv`
  have hw := Sob.W.hasWeakDeriv x (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at hw
  have hxloc : LocallyIntegrable (Cyl.H.val x' : Plane → ℝ) (Sob.cylinder c).μ :=
    Sob.locallyIntegrable_of_memLp (Lp.memLp _)
  have hdloc : LocallyIntegrable
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x : Plane → ℝ) (Sob.cylinder c).μ :=
    Sob.locallyIntegrable_of_memLp (Lp.memLp _)
  have hae := hx.ae_unique hw hxloc hdloc
  -- transport the `ae` identity from `(Sob.cylinder c).μ` to the value measure
  have hae' : ∀ μ' : Measure Plane, μ' = (Sob.cylinder c).μ →
      (Cyl.H.val x' : Plane → ℝ) =ᵐ[μ']
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
          (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x : Plane → ℝ) := by
    intro μ' h
    subst h
    exact hae
  -- the value measure of `H³` at weight exponent zero is `(Sob.cylinder c).μ`
  have hmeas : Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = (Sob.cylinder c).μ := by
    rw [scalarH2_measure_eq_cell, Cyl.cylinder_μ_eq]
  have hE : ∀ g : Plane → ℝ,
      eLpNorm g 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) =
        eLpNorm g 2 (Sob.cylinder c).μ :=
    fun g => congrArg (fun m => eLpNorm g 2 m) hmeas
  have hae'' : (Cyl.H.val x' : Plane → ℝ) =ᵐ[Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))]
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x : Plane → ℝ) :=
    hae' _ hmeas
  -- the one-letter word `[dir j]` gives the classical directional derivative
  have hiter : ∀ u : Plane → ℝ,
      Sob.iterD ((Sob.cylinder c).word (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))) u =
        fun z => fderiv ℝ u z ((Sob.cylinder c).dir j) := by
    intro u
    rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero, Sob.iterD_cons, Sob.iterD_nil]
  have hD : ∀ n, (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
      (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith) (f n) (hf n)) : Plane → ℝ) =ᵐ[Sob.wμ (Sob.cylinder c).μ
          (Cyl.ρwW c ^ (0 : ℝ))]
        (fun z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j)) := by
    intro n
    have h := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ) (k := 3)
      (p := 2) (by linarith) (f n) (hf n) (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
    rw [hiter (f n)] at h
    exact h
  -- `L²` convergence of the derivatives in the value space
  have hlimD : Tendsto (fun n => Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
      (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith) (f n) (hf n))) atTop
      (𝓝 (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x)) :=
    ((Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
      (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))).continuous.tendsto x).comp hfx
  have hEq : ∀ n, eLpNorm ((fun z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j)) -
      (Cyl.H.val x' : Plane → ℝ)) 2 (Sob.cylinder c).μ =
      edist (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
          (by linarith) (f n) (hf n)))
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
          (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x) := by
    intro n
    rw [Lp.edist_def, ← hE]
    exact eLpNorm_congr_ae ((hD n).symm.sub hae'')
  exact Tendsto.congr (fun n => (hEq n).symm) (tendsto_iff_edist_tendsto_0.mp hlimD)

end UnforcedLeray.Short.PartI
