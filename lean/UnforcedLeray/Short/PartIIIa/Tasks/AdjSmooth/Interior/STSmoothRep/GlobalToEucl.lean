import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs
import UnforcedLeray.Lib.SobolevC.CylTransfer
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `PartIII-a:T21/2/7/2/1/1/8/2`: `H^∞(ℝ × ℝ²)` transfers to `H^∞(ℝ³)` (`stGlobalToEucl`)

The measure-preserving linear equivalence `toSpace : Eucl 3 ≃L ℝ × (ℝ × ℝ)` carries the
coordinate words `stDir` to the coordinate words `e`, so weak derivatives transfer
(`Sob.hasWeakDeriv_comp_toPlane` with three coordinates).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Sob

theorem toSpace_apply (y : Eucl 3) : toSpace y = (y 0, (y 1, y 2)) := rfl

theorem toSpace_e (i : Fin 3) : toSpace (e i) = stDir i := by
  fin_cases i <;> simp [toSpace_apply, e, stDir]

theorem toSpace_symm_stDir (i : Fin 3) : toSpace.symm (stDir i) = e i := by
  rw [← toSpace_e, toSpace.symm_apply_apply]

theorem toSpace_word (l : List (Fin 3)) : (l.map stDir).map toSpace.symm = l.map e := by
  rw [List.map_map]
  congr 1
  funext i
  exact toSpace_symm_stDir i

theorem measurePreserving_toSpace : MeasurePreserving toSpace volume volume := by
  have h : ⇑toSpace = (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘ WithLp.ofLp := by
    funext y
    rfl
  rw [h]
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := PiLp.volume_preserving_ofLp (Fin 3)
  exact (h1.comp h2).comp h3

theorem hasWeakDeriv_comp_toSpace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {vs : List (ℝ × (ℝ × ℝ))} {f g : ℝ × (ℝ × ℝ) → F}
    (h : HasWeakDeriv (wholeSpaceOf (ℝ × (ℝ × ℝ)) volume stDir) vs f g) :
    HasWeakDeriv (wholeSpace 3) (vs.map toSpace.symm) (f ∘ toSpace) (g ∘ toSpace) := by
  have hmp := measurePreserving_toSpace
  have hemb := toSpace.toHomeomorph.measurableEmbedding
  have hadm : ∀ φ : Eucl 3 → ℝ, (wholeSpace 3).Adm φ →
      (wholeSpaceOf (ℝ × (ℝ × ℝ)) volume stDir).Adm (φ ∘ toSpace.symm) := fun φ hφ =>
    ⟨hφ.1.comp toSpace.symm.contDiff, hφ.2.comp_homeomorph toSpace.symm.toHomeomorph⟩
  have hit : ∀ φ : Eucl 3 → ℝ, (wholeSpace 3).Adm φ → ∀ ws : List (ℝ × (ℝ × ℝ)),
      iterDirDeriv ws (φ ∘ toSpace.symm) = iterDirDeriv (ws.map toSpace.symm) φ ∘ toSpace.symm :=
    fun φ hφ ws => iterDirDeriv_comp_clm (toSpace.symm : (ℝ × (ℝ × ℝ)) →L[ℝ] Eucl 3) hφ.1 ws
  have hfun : ∀ (a : Eucl 3 → ℝ) (u : ℝ × (ℝ × ℝ) → F),
      (fun z => (a ∘ toSpace.symm) z • u z) ∘ toSpace = fun y => a y • (u ∘ toSpace) y := by
    intro a u
    funext y
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have h1 := h.int_left _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    have h2 := (hmp.integrable_comp_emb hemb).mpr h1
    rw [hfun] at h2
    exact h2
  · have h1 := h.int_right _ (hadm φ hφ)
    have h2 := (hmp.integrable_comp_emb hemb).mpr h1
    rw [hfun] at h2
    exact h2
  · have h1 := h.identity _ (hadm φ hφ)
    rw [hit φ hφ] at h1
    simp only [wholeSpaceOf_μ] at h1
    simp only [wholeSpace_μ, List.length_map, Function.comp_apply]
    have e1 := hmp.integral_comp hemb
      (fun z => (iterDirDeriv (vs.map toSpace.symm) φ ∘ toSpace.symm) z • f z)
    have e2 := hmp.integral_comp hemb (fun z => (φ ∘ toSpace.symm) z • g z)
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] at e1 e2
    rw [e1, e2]
    exact h1

theorem stGlobalToEucl : STGlobalToEucl := by
  intro f hf
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨hf1.comp_measurePreserving measurePreserving_toSpace, fun l => ?_⟩
  obtain ⟨g, hg, hw⟩ := hf2 l
  refine ⟨g ∘ toSpace, hg.comp_measurePreserving measurePreserving_toSpace, ?_⟩
  have := hasWeakDeriv_comp_toSpace hw
  rwa [toSpace_word] at this

end UnforcedLeray.Short.IIIa
