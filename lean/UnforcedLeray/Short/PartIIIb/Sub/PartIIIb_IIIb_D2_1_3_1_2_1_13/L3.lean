import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_2

/-!
# `truncCurlMove`: the weak curl move `⟪Θ, curl(χₙψ)⟫ = ⟪χₙ curl Θ, ψ⟫`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Product rule `curl(χΘ) = χ curl Θ + ∇χ × Θ`, the triple product identity, and the weak curl
`HasPtwOp curlT ψ Φ` applied to the phase test `χₙΘ`. Integrability on the phase cell comes from
`wcm_integrable_dotL` (`LocL2` of `Φ` and of the Hardy quotient of `ψ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

theorem dotL_real_smul' (c : ℝ) (a b : CVec3) : dotL (c • a) b = dotL a (c • b) := by
  simp only [dotL_apply, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem triple_dotL' (v a w : CVec3) : dotL v (crossC a w) = -dotL (crossC a v) w := by
  simp only [dotL_apply]
  simp [crossC, Fin.sum_univ_three] <;> ring

theorem phaseInt_neg' (P : ℝ) (f : ℝ × Space → ℂ) :
    phaseInt P (fun x => -f x) = -phaseInt P f := by
  simp [phaseInt, integral_neg, smul_neg]

theorem crossC_gradC_sum' (c : Space → ℝ) (y : Space) (b : CVec3) :
    crossC (gradC c y) b = ∑ j : Fin 3, (sd j c y) • crossC (EuclideanSpace.single j (1 : ℂ)) b := by
  ext i
  fin_cases i <;> simp [crossC, gradC, Fin.sum_univ_three] <;> ring

theorem curlT_apply' (G : ℝ × Space → CVec3) (x : ℝ × Space) :
    curlT G x = ∑ j : Fin 3, crossCR (EuclideanSpace.single j (1 : ℂ)) (dy j G x) := rfl

theorem curlT_cut_product' {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (n : ℕ) :
    curlT (fun x => cutχ n x.2 • Θ x) =
      fun x => cutχ n x.2 • curlT Θ x + crossC (gradC (cutχ n) x.2) (Θ x) := by
  have ha : Differentiable ℝ (cutχ n) := (contDiff_cutχ n).differentiable (by simp)
  have hd : ∀ j : Fin 3, ∀ x : ℝ × Space,
      dy j (fun x => cutχ n x.2 • Θ x) x = cutχ n x.2 • dy j Θ x + sd j (cutχ n) x.2 • Θ x := by
    intro j x
    have h := dy_mulT ha (hΘ.smooth.differentiable (by simp)) j
    exact congrFun h x
  funext x
  rw [curlT_apply' ((fun x => cutχ n x.2 • Θ x)), crossC_gradC_sum', curlT_apply' Θ,
    Finset.smul_sum]
  simp only [hd, map_add, map_smul, Finset.sum_add_distrib]
  rfl

theorem truncCurlMove : TruncCurlMove := by
  intro hCut P ν μ hP hP1 hν hμ D hD n Θ hΘ
  have hP' : 0 < P := hP
  haveI : Fact (0 < P) := ⟨hP'⟩
  obtain ⟨C, hC0, hC⟩ := hCut
  have hzeroY : ∀ y : Space, 2 * ((n : ℝ) + 1) < ‖y‖ → cutχ n y = 0 :=
    fun y hy => cutχ_eq_zero n hy.le
  have hgrad0 : ∀ y : Space, 2 * ((n : ℝ) + 1) < ‖y‖ → gradC (cutχ n) y = 0 :=
    fun y hy => ((hC n y).1 (Or.inr hy)).1
  have hΘc : IsPhaseTest P (fun x => cutχ n x.2 • Θ x) := by
    refine ⟨((contDiff_cutχ n).comp contDiff_snd).smul hΘ.smooth, ?_, ?_⟩
    · intro τ y
      simp [hΘ.periodic τ y]
    · obtain ⟨R, hR⟩ := hΘ.bounded_support
      exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩
  have hcurl := hD.spΦ.curl _ hΘc
  have hcurlΘ : Continuous (curlT Θ) := (isPhaseTest_curlT hΘ).continuous
  have hcont_cut : Continuous (fun x : ℝ × Space => cutχ n x.2) :=
    (contDiff_cutχ n).continuous.comp continuous_snd
  have hA_cont : Continuous (fun x : ℝ × Space => cutχ n x.2 • curlT Θ x) :=
    hcont_cut.smul hcurlΘ
  have hB_cont : Continuous (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (Θ x)) := by
    have e : (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (Θ x)) =
        fun x => ∑ j : Fin 3, (sd j (cutχ n) x.2) • crossC (EuclideanSpace.single j (1 : ℂ)) (Θ x) := by
      funext x
      rw [crossC_gradC_sum']
    rw [e]
    exact continuous_finset_sum _ fun j _ =>
      ((contDiff_sd (contDiff_cutχ n) j).continuous.comp continuous_snd).smul
        ((crossCR (EuclideanSpace.single j (1 : ℂ))).continuous.comp hΘ.continuous)
  have hA_supp : ∃ R : ℝ, ∀ τ y, R < ‖y‖ → cutχ n y • curlT Θ (τ, y) = 0 :=
    ⟨2 * ((n : ℝ) + 1), fun τ y hy => by simp [hzeroY y hy]⟩
  have hB_supp : ∃ R : ℝ, ∀ τ y, R < ‖y‖ →
      crossC (gradC (cutχ n) y) (Θ (τ, y)) = 0 :=
    ⟨2 * ((n : ℝ) + 1), fun τ y hy => by simp [hgrad0 y hy, crossC]⟩
  have hψL : UnforcedLeray.Short.PartIIIb.Concrete.LocL2 P D.ψ := Or.inr hD.spΦ.hardy
  have hΦL : UnforcedLeray.Short.PartIIIb.Concrete.LocL2 P D.Φ := Or.inl hD.dom.mem
  have iA := wcm_integrable_dotL hP' hA_cont hA_supp hψL
  have iB := wcm_integrable_dotL hP' hB_cont hB_supp hψL
  have iCΦ : Integrable (fun x : ℝ × Space => dotL (Θ x) (cutχ n x.2 • D.Φ x))
      (volume.restrict (phaseCell P)) := by
    have h := wcm_integrable_dotL hP' hΘc.continuous ⟨2 * ((n : ℝ) + 1), fun τ y hy => by
      simp [hzeroY y hy]⟩ hΦL
    refine Integrable.congr h (ae_of_all _ fun x => ?_)
    exact dotL_real_smul' _ _ _
  have iXΘ : Integrable (fun x : ℝ × Space => dotL (Θ x) (crossC (gradC (cutχ n) x.2) (D.ψ x)))
      (volume.restrict (phaseCell P)) := by
    refine Integrable.congr iB.neg (ae_of_all _ fun x => ?_)
    exact (triple_dotL' _ _ _).symm
  have iAB : Integrable (fun x : ℝ × Space => dotL (cutχ n x.2 • curlT Θ x +
      crossC (gradC (cutχ n) x.2) (Θ x)) (D.ψ x)) (volume.restrict (phaseCell P)) := by
    refine Integrable.congr (iA.add iB) (ae_of_all _ fun x => ?_)
    simp [dotL_apply]
  have iSum : Integrable (fun x : ℝ × Space => dotL (Θ x)
      (cutχ n x.2 • D.Φ x + crossC (gradC (cutχ n) x.2) (D.ψ x)))
      (volume.restrict (phaseCell P)) := by
    refine Integrable.congr (iCΦ.add iXΘ) (ae_of_all _ fun x => ?_)
    simp [map_add]
  have e1 : pairF P Θ (truncPhi n D) = pairF P Θ (fun x => cutχ n x.2 • D.Φ x) +
      pairF P Θ (fun x => crossC (gradC (cutχ n) x.2) (D.ψ x)) :=
    UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable iCΦ iXΘ iSum
  have e2 : pairF P Θ (fun x => cutχ n x.2 • D.Φ x) = pairF P (fun x => cutχ n x.2 • Θ x) D.Φ := by
    simp only [pairF]
    congr 1
    funext x
    exact (dotL_real_smul' _ _ _).symm
  have e3 : pairF P Θ (fun x => crossC (gradC (cutχ n) x.2) (D.ψ x)) =
      -pairF P (fun x => crossC (gradC (cutχ n) x.2) (Θ x)) D.ψ := by
    simp only [pairF]
    rw [← phaseInt_neg']
    congr 1
    funext x
    exact triple_dotL' _ _ _
  have e5 : pairF P (curlT (fun x => cutχ n x.2 • Θ x)) D.ψ =
      pairF P (fun x => cutχ n x.2 • curlT Θ x) D.ψ +
        pairF P (fun x => crossC (gradC (cutχ n) x.2) (Θ x)) D.ψ := by
    rw [curlT_cut_product' hΘ n]
    exact UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable iA iB iAB
  show pairF P Θ (truncPhi n D) = _
  rw [e1, e2, e3, ← hcurl, e5]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
