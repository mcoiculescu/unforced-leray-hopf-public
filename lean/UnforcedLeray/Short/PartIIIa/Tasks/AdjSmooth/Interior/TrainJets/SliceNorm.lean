import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The derivative within `tjU` in a direction `(0, w)` of a field, at a point `(ρ, y)` with
`ρ ≥ 0`, is the derivative of its spatial slice `z ↦ F (ρ, z)`. -/
theorem fderivWithin_slice_tj {F : ℝ × (ℝ × ℝ) → ℝ} {ρ : ℝ} {y : ℝ × ℝ} (hρ : 0 ≤ ρ)
    (hF : DifferentiableWithinAt ℝ F tjU (ρ, y)) (w : ℝ × ℝ) :
    fderivWithin ℝ F tjU (ρ, y) ((0 : ℝ), w) = fderiv ℝ (fun z : ℝ × ℝ => F (ρ, z)) y w := by
  have hι : HasFDerivAt (fun z : ℝ × ℝ => ((ρ, z) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_const (𝕜 := ℝ) ρ y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have hmaps : MapsTo (fun z : ℝ × ℝ => ((ρ, z) : ℝ × (ℝ × ℝ))) univ tjU :=
    fun _ _ => ⟨mem_Ici.2 hρ, mem_univ _⟩
  have hcomp := hF.hasFDerivWithinAt.comp y hι.hasFDerivWithinAt hmaps
  have hfull := hasFDerivWithinAt_univ.1 hcomp
  rw [show (fun z : ℝ × ℝ => F (ρ, z)) = F ∘ Prod.mk ρ from rfl, hfull.fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- The word of a field `C^∞` on `tjU` along the age-free direction `a` is the slice derivative. -/
theorem tjW_slice_eq (h : ℝ × (ℝ × ℝ) → ℝ) (hh : ContDiffOn ℝ ∞ h tjU) :
    ∀ L : List (Fin 3), 0 ∉ L → ∀ ρ : ℝ, 0 ≤ ρ → ∀ y : ℝ × ℝ,
      tjW L h (ρ, y) = iteratedFDeriv ℝ L.length (fun z : ℝ × ℝ => h (ρ, z)) y
        (fun i => (stDir (L.get i)).2) := by
  intro L
  induction L with
  | nil =>
    intro _ ρ _ y
    simp [tjW_nil, iteratedFDeriv_zero_apply]
  | cons a L ih =>
    intro hL ρ hρ y
    have ha : a ≠ 0 := fun h0 => hL (by simp [h0])
    have hL' : (0 : Fin 3) ∉ L := fun h0 => hL (List.mem_cons_of_mem _ h0)
    have hdiffL : DifferentiableWithinAt ℝ (tjW L h) tjU (ρ, y) :=
      ((tjW_contDiffOn hh L).differentiableOn (by simp)) _ ⟨mem_Ici.2 hρ, mem_univ y⟩
    have hs : stDir a = ((0 : ℝ), (stDir a).2) := by
      fin_cases a
      · exact absurd rfl ha
      · rfl
      · rfl
    have e2 : fderivWithin ℝ (tjW L h) tjU (ρ, y) (stDir a) =
        fderiv ℝ (fun z : ℝ × ℝ => tjW L h (ρ, z)) y (stDir a).2 := by
      conv_lhs => rw [hs]
      exact fderivWithin_slice_tj hρ hdiffL _
    have hfun : (fun z : ℝ × ℝ => tjW L h (ρ, z)) =
        (fun z : ℝ × ℝ => iteratedFDeriv ℝ L.length (fun w : ℝ × ℝ => h (ρ, w)) z
          (fun i => (stDir (L.get i)).2)) :=
      funext fun z => ih hL' ρ hρ z
    have hslice : ContDiff ℝ ∞ (fun z : ℝ × ℝ => h (ρ, z)) := by
      have : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => h (ρ, z)) univ :=
        hh.comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun z _ => ⟨mem_Ici.2 hρ, mem_univ _⟩)
      exact contDiffOn_univ.1 this
    have hdiffn : DifferentiableAt ℝ (iteratedFDeriv ℝ L.length
        (fun w : ℝ × ℝ => h (ρ, w))) y :=
      (hslice.differentiable_iteratedFDeriv (m := L.length) (by
        exact_mod_cast ENat.natCast_lt_top _)) y
    have step := DifferentiableAt.iteratedFDeriv_succ_apply_left' (f := fun w : ℝ × ℝ => h (ρ, w))
      (x := y) (m := Fin.cons (stDir a).2 (fun i : Fin L.length => (stDir (L.get i)).2)) hdiffn
    simp only [Fin.tail_cons, Fin.cons_zero] at step
    have hm : (fun i : Fin (a :: L).length => (stDir ((a :: L).get i)).2) =
        Fin.cons (stDir a).2 (fun i : Fin L.length => (stDir (L.get i)).2) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    show fderivWithin ℝ (tjW L h) tjU (ρ, y) (stDir a) = _
    rw [e2, hfun, hm]
    exact step.symm

/-- **Words with no age letter are bounded by the spatial jets** (calculus; SP 2866-2870, the
spatial words of `TjSliceNorm`): see the statement in `Sub/AdjInterior/Train/Defs.lean`. -/
theorem tjSliceNorm : TjSliceNorm := by
  intro h hh L hL ρ hρ x
  rw [tjW_slice_eq h hh L hL ρ hρ x, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have key : ∀ b : Fin 3, b ≠ 0 → ‖(stDir b).2‖ ≤ 1 := by
    intro b hb
    fin_cases b
    · exact absurd rfl hb
    · simp [stDir, Prod.norm_def]
    · simp [stDir, Prod.norm_def]
  have hb : ∀ i : Fin L.length, ‖(stDir (L.get i)).2‖ ≤ 1 := by
    intro i
    have hne : L.get i ≠ 0 := fun h0 => hL (h0 ▸ List.get_mem L i)
    exact key _ hne
  have hprod : ∏ i : Fin L.length, ‖(stDir (L.get i)).2‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hb i)
  exact mul_le_of_le_one_right (norm_nonneg _) hprod

end UnforcedLeray.Short.IIIa
