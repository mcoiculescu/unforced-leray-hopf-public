import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_1

/-!


Second spatial bounds for the chart derivatives `D_η ∂_ηΨ` and `D_q ∂_ηΨ` (SP 2419-2423).
Since `∂_ηΨ = DΨ(·)(0,(0,1))`, the chart second derivative in the directions `(0,a)`, `(0,(0,1))`
is the plane second derivative of `ψ s` at `η`, which is bounded by the spatial jet `ageJet 0 2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.IIb

private lemma psiChart_contDiffAt_js {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : ContDiffAt ℝ 2 (psiChart ψ) y := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) :=
    isOpen_Ioi.prod isOpen_univ
  exact (hψ.contDiffAt (hopen.mem_nhds (Set.mk_mem_prod hy (mem_univ _)))).of_le (by simp)

private lemma fderiv_apply_const_js {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {y : E} (hF : DifferentiableAt ℝ (fderiv ℝ F) y) (v e : E) :
    fderiv ℝ (fun z => fderiv ℝ F z v) y e = fderiv ℝ (fderiv ℝ F) y e v := by
  rw [fderiv_clm_apply hF (differentiableAt_const v)]
  simp

/-- Second derivative of a chart function in the `(0,a),(0,b)` directions is the second
derivative of its slice `z ↦ f (s,z)` at `z`. -/
private lemma slice_second_js {f : Coord → ℝ}
    (hf : ∀ y : Coord, 0 < y.1 → ContDiffAt ℝ 2 f y)
    {s : ℝ} (hs : 0 < s) (z a b : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ f) ((s, z) : Coord) (0, a) (0, b) =
      fderiv ℝ (fderiv ℝ (fun w : ℝ × ℝ => f (s, w))) z a b := by
  have hA : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 f ((s, w) : Coord) := fun w => hf ((s, w) : Coord) hs
  have hσ : ∀ w : ℝ × ℝ, HasFDerivAt (fun v : ℝ × ℝ => ((s, v) : Coord))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w := fun w =>
    (hasFDerivAt_const s w).prodMk (hasFDerivAt_id w)
  have hh : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 (fun v : ℝ × ℝ => f (s, v)) w := fun w =>
    (hA w).comp w ((contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => s) w).prodMk
      contDiffAt_id)
  have hD : ∀ w : ℝ × ℝ, DifferentiableAt ℝ (fderiv ℝ (fun v : ℝ × ℝ => f (s, v))) w :=
    fun w => ((hh w).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgrad : ∀ w b : ℝ × ℝ,
      fderiv ℝ (fun v : ℝ × ℝ => f (s, v)) w b = fderiv ℝ f ((s, w) : Coord) (0, b) := by
    intro w b
    have hd : HasFDerivAt (fun v : ℝ × ℝ => f (s, v))
        ((fderiv ℝ f ((s, w) : Coord)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) w :=
      ((hA w).differentiableAt (by norm_num)).hasFDerivAt.comp w (hσ w)
    rw [hd.fderiv]
    simp
  have hGd : ∀ b w : ℝ × ℝ,
      DifferentiableAt ℝ (fun y : Coord => fderiv ℝ f y (0, b)) ((s, w) : Coord) := by
    intro b w
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) ((s, w) : Coord) :=
      ((hA w).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hfd.clm_apply (differentiableAt_const _)
  have hchain : ∀ b a : ℝ × ℝ,
      fderiv ℝ (fun v : ℝ × ℝ => fderiv ℝ f ((s, v) : Coord) (0, b)) z a =
        fderiv ℝ (fun y : Coord => fderiv ℝ f y (0, b)) ((s, z) : Coord) (0, a) := by
    intro b a
    have hcomp := fderiv_comp z (hGd b z) (hσ z).differentiableAt
    rw [(hσ z).fderiv] at hcomp
    have hfun : (fun v : ℝ × ℝ => fderiv ℝ f ((s, v) : Coord) (0, b)) =
        (fun y : Coord => fderiv ℝ f y (0, b)) ∘ (fun v : ℝ × ℝ => ((s, v) : Coord)) := rfl
    rw [hfun, hcomp]
    simp
  have hfdf : DifferentiableAt ℝ (fderiv ℝ f) ((s, z) : Coord) :=
    ((hA z).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have H2 : fderiv ℝ (fderiv ℝ f) ((s, z) : Coord) (0, a) (0, b) =
      fderiv ℝ (fun y : Coord => fderiv ℝ f y (0, b)) ((s, z) : Coord) (0, a) :=
    (fderiv_apply_const_js hfdf (0, b) (0, a)).symm
  have H1 : fderiv ℝ (fderiv ℝ (fun v : ℝ × ℝ => f (s, v))) z a b =
      fderiv ℝ (fun v : ℝ × ℝ => fderiv ℝ (fun v' : ℝ × ℝ => f (s, v')) v b) z a :=
    (fderiv_apply_const_js (hD z) b a).symm
  have hfun2 : (fun v : ℝ × ℝ => fderiv ℝ (fun v' : ℝ × ℝ => f (s, v')) v b) =
      fun v : ℝ × ℝ => fderiv ℝ f ((s, v) : Coord) (0, b) :=
    funext fun v => hgrad v b
  rw [H2, H1, hfun2, hchain b a]

theorem raisedJetSecond_proof : UnforcedLeray.Short.IIb.RaisedJetSecond := by
  intro ψ hψ x hx
  obtain ⟨s, z⟩ := x
  show |fderiv ℝ (Axi.dEta (psiChart ψ)) ((s, z) : Coord) (0, (0, 1))| ≤ ‖ageJet 0 2 ψ s z‖ ∧
      |fderiv ℝ (Axi.dEta (psiChart ψ)) ((s, z) : Coord) (0, (1, 0))| ≤ ‖ageJet 0 2 ψ s z‖
  have hs : (0 : ℝ) < s := hx
  have hf : ∀ y : Coord, 0 < y.1 → ContDiffAt ℝ 2 (psiChart ψ) y :=
    fun y hy => psiChart_contDiffAt_js hψ hy
  have hfdf : DifferentiableAt ℝ (fderiv ℝ (psiChart ψ)) ((s, z) : Coord) :=
    ((hf ((s, z) : Coord) hs).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have eEta : ∀ a : ℝ × ℝ, fderiv ℝ (Axi.dEta (psiChart ψ)) ((s, z) : Coord) (0, a) =
      fderiv ℝ (fderiv ℝ (psiChart ψ)) ((s, z) : Coord) (0, a) (0, (0, 1)) := by
    intro a
    have e1 : Axi.dEta (psiChart ψ) = fun y : Coord => fderiv ℝ (psiChart ψ) y (0, (0, 1)) :=
      rfl
    rw [e1]
    exact fderiv_apply_const_js hfdf (0, (0, 1)) (0, a)
  have hbound : ∀ a w : ℝ × ℝ,
      |fderiv ℝ (fderiv ℝ (psiChart ψ)) ((s, z) : Coord) (0, a) (0, w)| ≤
        ‖ageJet 0 2 ψ s z‖ * ‖a‖ * ‖w‖ := by
    intro a w
    rw [slice_second_js hf hs z a w]
    have hA : ageJet 0 2 ψ s z =
        iteratedFDeriv ℝ 2 (fun v : ℝ × ℝ => psiChart ψ (s, v)) z := by
      unfold ageJet
      simp only [iteratedDeriv_zero]
      rfl
    rw [hA]
    have e2 : fderiv ℝ (fderiv ℝ (fun v : ℝ × ℝ => psiChart ψ (s, v))) z a w =
        iteratedFDeriv ℝ 2 (fun v : ℝ × ℝ => psiChart ψ (s, v)) z ![a, w] := by
      rw [iteratedFDeriv_two_apply]
      rfl
    rw [e2]
    have hit := ContinuousMultilinearMap.le_opNorm
      (iteratedFDeriv ℝ 2 (fun v : ℝ × ℝ => psiChart ψ (s, v)) z) ![a, w]
    rw [Fin.prod_univ_two] at hit
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hit
    rw [← Real.norm_eq_abs]
    exact hit.trans (le_of_eq (by ring))
  have n1 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have n10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  refine ⟨?_, ?_⟩
  · rw [eEta]
    have h11 := hbound ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))
    rw [n1] at h11
    linarith
  · rw [eEta]
    have h10 := hbound ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
    rw [n10, n1] at h10
    linarith

end UnforcedLeray.Short.IIb
