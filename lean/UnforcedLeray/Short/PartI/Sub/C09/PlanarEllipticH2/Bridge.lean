import UnforcedLeray.Short.PartI.Sub.C09.PlanarEllipticH2.Tests

/-!
# From `W^{2,2}(ℝ²)` derivatives to planar weak derivatives (helper for `PartI:PlanarEllipticH2`)

* `planar_bridge`: a component `∂^α x` of `x ∈ W^{2,2}(Eucl 2)` with field `u ∘ toPlane` is the
  planar weak derivative `∂^β u` on `ℝ × ℝ` (complex tests, the whole plane), whenever the word of
  `α` pushed along `toPlane` is the direction list `pdListR β`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Sob

/-- **Bridge.** Each component of a `W^{2,2}` element with field `u ∘ toPlane` is a planar weak
derivative of `u` (for the direction list matching the word under `toPlane`). -/
theorem planar_bridge (x : W (wholeSpace 2) 1 ℂ ℂ 2 2) {u : ℝ × ℝ → ℂ}
    (hxu : toVol (W.value (wholeSpace 2) 1 ℂ ℂ 2 2 x) =ᵐ[volume] fun y => u (toPlane y))
    (α : Idx 2 2) {β : ℕ × ℕ}
    (hβ : ((wholeSpace 2).word α).map toPlane = UnforcedLeray.B0121.pdListR β) :
    UnforcedLeray.PlanarBS.Sob.HasWeakDerivOn Set.univ (UnforcedLeray.B0121.pdListR β) u
      (fun z => (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 α x) : Eucl 2 → ℂ) (toPlane.symm z)) := by
  intro φ hφ
  have hφs : ContDiff ℝ ∞ φ := hφ.smooth
  have hψs : ContDiff ℝ ∞ (fun y : Eucl 2 => φ (toPlane y)) :=
    hφs.comp toPlane.contDiff
  have hψc : HasCompactSupport (fun y : Eucl 2 => φ (toPlane y)) :=
    hφ.compact.comp_homeomorph toPlane.toHomeomorph
  have hW' : HasWeakDeriv (wholeSpace 2) ((wholeSpace 2).word α)
      (toVol (W.value (wholeSpace 2) 1 ℂ ℂ 2 2 x) : Eucl 2 → ℂ)
      (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 α x) : Eucl 2 → ℂ) :=
    (W.hasWeakDeriv x α).congr_ae (coeFn_toVol _).symm (coeFn_toVol _).symm
  have key := hasWeakDeriv_complex_test hW' hψs hψc
  -- the planar derivatives of `φ` at `toPlane y` are the Euclidean ones of `φ ∘ toPlane`
  have hchain : ∀ y : Eucl 2,
      UnforcedLeray.PlanarBS.Sob.iterDirDeriv (UnforcedLeray.B0121.pdListR β) φ (toPlane y) =
        UnforcedLeray.PlanarBS.Sob.iterDirDeriv ((wholeSpace 2).word α)
          (fun y : Eucl 2 => φ (toPlane y)) y := by
    intro y
    have ch := congrFun (UnforcedLeray.Sob.iterD_comp_clm
      (toPlane : Eucl 2 →L[ℝ] ℝ × ℝ) hφs ((wholeSpace 2).word α)) y
    simp only [ContinuousLinearEquiv.coe_coe, Function.comp_apply] at ch
    rw [hβ] at ch
    exact ch.symm
  have cv : ∀ G : ℝ × ℝ → ℂ, ∫ y, G (toPlane y) = ∫ z, G z := fun G =>
    UnforcedLeray.Sob.measurePreserving_toPlane.integral_comp
      UnforcedLeray.Sob.measurableEmbedding_toPlane G
  have hL : ∫ z, u z * UnforcedLeray.PlanarBS.Sob.iterDirDeriv (UnforcedLeray.B0121.pdListR β) φ z =
      ∫ y : Eucl 2, u (toPlane y) * UnforcedLeray.PlanarBS.Sob.iterDirDeriv ((wholeSpace 2).word α)
        (fun w : Eucl 2 => φ (toPlane w)) y := by
    calc ∫ z, u z * UnforcedLeray.PlanarBS.Sob.iterDirDeriv (UnforcedLeray.B0121.pdListR β) φ z
        = ∫ y : Eucl 2, u (toPlane y) * UnforcedLeray.PlanarBS.Sob.iterDirDeriv
            (UnforcedLeray.B0121.pdListR β) φ (toPlane y) := (cv _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => by
          dsimp only
          rw [hchain y])
  have hB : ∫ y : Eucl 2, u (toPlane y) * UnforcedLeray.PlanarBS.Sob.iterDirDeriv
        ((wholeSpace 2).word α) (fun w : Eucl 2 => φ (toPlane w)) y =
      ∫ y : Eucl 2, UnforcedLeray.PlanarBS.Sob.iterDirDeriv ((wholeSpace 2).word α)
        (fun w : Eucl 2 => φ (toPlane w)) y *
          (toVol (W.value (wholeSpace 2) 1 ℂ ℂ 2 2 x) : Eucl 2 → ℂ) y := by
    refine integral_congr_ae ?_
    filter_upwards [hxu] with w hw
    rw [hw, mul_comm]
  have hR : ∫ z, (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 α x) : Eucl 2 → ℂ) (toPlane.symm z) *
        φ z =
      ∫ y : Eucl 2, (fun w : Eucl 2 => φ (toPlane w)) y *
        (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 α x) : Eucl 2 → ℂ) y := by
    calc ∫ z, (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 α x) : Eucl 2 → ℂ) (toPlane.symm z) * φ z
        = ∫ y : Eucl 2, (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 α x) : Eucl 2 → ℂ)
            (toPlane.symm (toPlane y)) * φ (toPlane y) := (cv _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => by
          dsimp only
          rw [ContinuousLinearEquiv.symm_apply_apply, mul_comm])
  have hlen : (UnforcedLeray.B0121.pdListR β).length = ((wholeSpace 2).word α).length := by
    rw [← hβ, List.length_map]
  rw [hL, hB, key, hlen, hR]

end UnforcedLeray.Short.PartI
