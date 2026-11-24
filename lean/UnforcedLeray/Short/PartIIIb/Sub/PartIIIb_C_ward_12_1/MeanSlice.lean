import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets.Calc
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `MeanSliceJet` (source 439-459, 5461-5464): age-jets of a function of `η` alone

Helper lemmas for `meanSliceJet : MeanSliceJet`. The age derivative of the slice
`r ↦ g r e` is the directional derivative `dW (replicate ℓ (1,0)) G`, which is `C^∞` on `{s > 0}`;
the spatial jet of `z ↦ h z.2` is bounded by the jet of `h` since the projection has norm `≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI.AgeDeriv (dW dW_contDiffOn dW_cons)
open UnforcedLeray.Short.PartI (ageJet)

/-- The time derivative of the slice `r ↦ g r e` is the directional derivative along `(1,0)`. -/
theorem iteratedDeriv_slice_eq_dW (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ∀ ℓ : ℕ, ∀ r e : ℝ, 0 < r →
      iteratedDeriv ℓ (fun t => g t e) r =
        dW (List.replicate ℓ ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2) (r, e) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  intro ℓ
  induction ℓ with
  | zero => intro r e _; simp [dW]
  | succ n ih =>
    intro r e hr
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (fun t => g t e) =ᶠ[𝓝 r]
        fun t => dW (List.replicate n ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2) (t, e) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
      exact ih t e ht
    rw [hev.deriv_eq]
    have hC : ContDiffAt ℝ ∞ (dW (List.replicate n ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2))
        (r, e) :=
      ((dW_contDiffOn (g := fun x : ℝ × ℝ => g x.1 x.2) hU hg _).contDiffAt
        (hU.mem_nhds (show (r, e) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hr, trivial⟩)))
    have hd := (hC.differentiableAt (by simp)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => (t, e)) ((1 : ℝ), (0 : ℝ)) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r e)
    have hdl : HasDerivAt (fun t : ℝ => dW (List.replicate n ((1 : ℝ), (0 : ℝ)))
        (fun x : ℝ × ℝ => g x.1 x.2) (t, e))
        (fderiv ℝ (dW (List.replicate n ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2)) (r, e)
          ((1 : ℝ), (0 : ℝ))) r :=
      hd.comp_hasDerivAt r hline
    rw [hdl.deriv, List.replicate_succ, dW_cons]

/-- For `s > 0` the slice derivative `e ↦ ∂_s^ℓ g(s,e)` is `C^∞` on `ℝ`. -/
theorem contDiff_iteratedDeriv_slice (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ)) (ℓ : ℕ) (s : ℝ)
    (hs : 0 < s) :
    ContDiff ℝ ∞ (fun e => iteratedDeriv ℓ (fun t => g t e) s) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hC : ContDiffOn ℝ ∞ (dW (List.replicate ℓ ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2))
      (Ioi 0 ×ˢ univ) := dW_contDiffOn (g := fun x : ℝ × ℝ => g x.1 x.2) hU hg _
  have hmap : ContDiffOn ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) univ :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hcomp : ContDiffOn ℝ ∞
      (fun e : ℝ => dW (List.replicate ℓ ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2) (s, e))
      univ :=
    hC.comp hmap (fun e _ => ⟨hs, trivial⟩)
  have heq : (fun e => iteratedDeriv ℓ (fun t => g t e) s) =
      fun e => dW (List.replicate ℓ ((1 : ℝ), (0 : ℝ))) (fun x : ℝ × ℝ => g x.1 x.2) (s, e) := by
    funext e
    exact iteratedDeriv_slice_eq_dW g hg ℓ s e hs
  rw [heq]
  exact contDiffOn_univ.mp hcomp

/-- Projection onto the second factor does not increase the `j`-th Fréchet derivative norm. -/
theorem norm_iteratedFDeriv_snd_comp (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (j : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ × ℝ => u z.2) z‖ ≤ ‖iteratedFDeriv ℝ j u z.2‖ := by
  have h : iteratedFDeriv ℝ j (fun z : ℝ × ℝ => u z.2) z =
      (iteratedFDeriv ℝ j u z.2).compContinuousLinearMap
        (fun _ : Fin j => ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ ℝ ℝ) hu z
      (by exact_mod_cast le_top)
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro _ _
    exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  calc ‖iteratedFDeriv ℝ j u z.2‖ * ∏ _i : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ ‖iteratedFDeriv ℝ j u z.2‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j u z.2‖ := mul_one _

/-- **`MeanSliceJet`**: age-jets of a function of `η` alone are bounded by the `η`-derivatives of
its age-derivative. -/
theorem meanSliceJet : MeanSliceJet := by
  intro g hg ℓ j s hs z
  have hu := contDiff_iteratedDeriv_slice g hg ℓ s hs
  have hA : ageJet ℓ j (fun r z => g r z.2) s z =
      iteratedFDeriv ℝ j (fun z : ℝ × ℝ => (fun e => iteratedDeriv ℓ (fun t => g t e) s) z.2) z :=
    rfl
  rw [hA]
  refine (norm_iteratedFDeriv_snd_comp _ hu j z).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]

end UnforcedLeray.Short.PartIIIb.Concrete
