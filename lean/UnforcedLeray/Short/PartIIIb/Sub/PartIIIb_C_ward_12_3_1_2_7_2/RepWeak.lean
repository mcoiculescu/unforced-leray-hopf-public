import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `gEQRepWeak` (source 2525-2531): weak `y_j`-derivative of the representative of `w`

Test `Φ = φ e_i` in `HasPhaseOp (-∂_j) f G`; `phasePair_eq_pairF_rep` on both sides.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params rep pairF phaseInt phasePair_eq_pairF_rep)

theorem phaseInt_neg_fun (P : ℝ) (f : ℝ × UnforcedLeray.Space → ℂ) :
    phaseInt P (fun x => -f x) = -phaseInt P f := by
  unfold phaseInt
  simp [integral_neg, smul_neg]

theorem dotL_smul_single_fun (c : ℂ) (i : Fin 3) (u : UnforcedLeray.PhaseSpace.CVec3) :
    dotL (c • EuclideanSpace.single i (1 : ℂ)) u = c * u i := by
  simp [dotL_apply, EuclideanSpace.single_apply]

theorem gEQRepWeak_aux (P : ℝ) [Fact (0 < P)] (g : Yq P UnforcedLeray.B0412.q0E) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep g x.1 x.2) UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) P)).prod volume) := by
  have h := UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell
    UnforcedLeray.B0412.q0E_ne_top g
  have hm : ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)) =
      (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
        (Ioc (0 : ℝ) P ×ˢ (univ : Set UnforcedLeray.Space)) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure UnforcedLeray.Space)),
      Measure.prod_restrict]
    rfl
  rw [hm]
  exact h

theorem gEQRepWeak_comp (P : ℝ) [Fact (0 < P)] (g : Yq P UnforcedLeray.B0412.q0E) (i : Fin 3) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep g x.1 x.2 i) UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) P)).prod volume) := by
  have h := ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)
    (gEQRepWeak_aux P g)
  simpa [Function.comp_def] using h

theorem gEQRepWeak : GEQRepWeak := by
  intro P _ j f G hG
  refine fun i => ⟨?_, gEQRepWeak_comp P f i, gEQRepWeak_comp P G i⟩
  intro φ hφ
  have hΦ : IsPhaseTest P (fun x : ℝ × UnforcedLeray.Space => φ x • EuclideanSpace.single i (1 : ℂ)) :=
    { smooth := hφ.smooth.smul contDiff_const
      periodic := fun τ y => by simp [hφ.periodic]
      bounded_support := by
        obtain ⟨R, hR⟩ := hφ.bounded_support
        exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩ }
  set Φ : ℝ × UnforcedLeray.Space → CVec3 :=
    fun x => φ x • EuclideanSpace.single i (1 : ℂ) with hΦdef
  have hdy : dy j Φ = fun x => dy j φ x • EuclideanSpace.single i (1 : ℂ) := by
    funext x
    simp only [dy, hΦdef]
    rw [fderiv_smul_const (hφ.smooth.differentiable (by simp) x)]
    simp
  have hneg : IsPhaseTest P (-dy j Φ) := (hΦ.dy j).neg
  have H := hG Φ hΦ
  simp only at H
  rw [phasePair_eq_pairF_rep hneg, phasePair_eq_pairF_rep hΦ] at H
  unfold pairF at H
  have hL : (fun x : ℝ × UnforcedLeray.Space => dotL ((-dy j Φ) x) (rep f x.1 x.2)) =
      fun x => -(dy j φ x * rep f x.1 x.2 i) := by
    funext x
    simp only [Pi.neg_apply, hdy]
    rw [← neg_smul, dotL_smul_single_fun]
    ring
  have hR : (fun x : ℝ × UnforcedLeray.Space => dotL (Φ x) (rep G x.1 x.2)) =
      fun x => φ x * rep G x.1 x.2 i := by
    funext x
    simp only [hΦdef]
    rw [dotL_smul_single_fun]
  unfold phaseInt at H
  rw [hL, hR] at H
  have H2 : phaseInt P (fun x => -(dy j φ x * rep f x.1 x.2 i)) =
      phaseInt P (fun x => φ x * rep G x.1 x.2 i) := by
    unfold phaseInt
    exact H
  rw [phaseInt_neg_fun] at H2
  linear_combination -H2

end UnforcedLeray.Short.PartIIIb.Concrete
