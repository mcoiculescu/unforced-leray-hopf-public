import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayCellIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegKerCalc
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Regularised Green identity (`RegKerIBP`)

Source `the November 2 reference manuscript` 1676.  For a cylinder test `h` the identity
`∫_cell K_i^ε Δh = -∫_cell ρ_ε ∂_i h` follows from `CellIBP` (cell integration by parts), the
symmetry of second derivatives of smooth functions, and `RegKerCalc`
(`K_i^ε = ∂_i Γ_ε`, `Δ Γ_ε = ρ_ε`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

lemma rki_cellC_eq (c : ℝ) : cellC c = Ioc (-(c / 2)) (-(c / 2) + c) ×ˢ (univ : Set ℝ) := by
  rw [cellC, show -(c / 2) + c = c / 2 by ring]

lemma rki_integrableOn_cellC (F : ℝ × ℝ → ℝ) (hF : Continuous F) (c L : ℝ)
    (hz : ∀ y : ℝ × ℝ, L < |y.2| → F y = 0) : IntegrableOn F (cellC c) := by
  rw [rki_cellC_eq]
  exact integrableOn_cellS F hF (-(c / 2)) c L hz

lemma rki_cellIBP (c : ℝ) (hc : 0 < c) (A B : ℝ × ℝ → ℝ) (hA : ContDiff ℝ 1 A)
    (hB : ContDiff ℝ 1 B)
    (hAper : ∀ y : ℝ × ℝ, A (y.1 + c, y.2) = A y) (hBper : ∀ y : ℝ × ℝ, B (y.1 + c, y.2) = B y)
    (L : ℝ) (hL : ∀ y : ℝ × ℝ, L < |y.2| → B y = 0) (i : Fin 2) :
    ∫ y in cellC c, A y * pd2 i B y = -∫ y in cellC c, pd2 i A y * B y := by
  rw [rki_cellC_eq]
  exact cellIBP c hc (-(c / 2)) A B hA hB hAper hBper ⟨L, hL⟩ i

lemma rki_contDiff_pd2 (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (j : Fin 2) :
    ContDiff ℝ ∞ (pd2 j g) := by
  unfold pd2
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma rki_differentiable_pd2 (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (j : Fin 2) :
    Differentiable ℝ (pd2 j g) :=
  (rki_contDiff_pd2 g hg j).differentiable (by simp)

lemma rki_periodic_pd2 (c : ℝ) (g : ℝ × ℝ → ℝ)
    (hper : ∀ y : ℝ × ℝ, g (y.1 + c, y.2) = g y) (j : Fin 2) :
    ∀ y : ℝ × ℝ, pd2 j g (y.1 + c, y.2) = pd2 j g y := by
  intro y
  set a : ℝ × ℝ := ((c : ℝ), (0 : ℝ)) with ha
  have hfun : (fun z : ℝ × ℝ => g (z + a)) = g := by
    funext z
    have e : z + a = (z.1 + c, z.2) := by
      ext <;> simp [ha]
    rw [e]
    exact hper z
  have h1 : fderiv ℝ g (y + a) = fderiv ℝ g y := by
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := y) a
    rw [hfun] at h
    exact h.symm
  have e' : (y.1 + c, y.2) = y + a := by
    ext <;> simp [ha]
  unfold pd2
  rw [e', h1]

lemma rki_periodic_lap (c : ℝ) (g : ℝ × ℝ → ℝ)
    (hper : ∀ y : ℝ × ℝ, g (y.1 + c, y.2) = g y) :
    ∀ y : ℝ × ℝ, lap2 g (y.1 + c, y.2) = lap2 g y := by
  intro y
  unfold lap2
  rw [rki_periodic_pd2 c (pd2 0 g) (rki_periodic_pd2 c g hper 0) 0 y,
    rki_periodic_pd2 c (pd2 1 g) (rki_periodic_pd2 c g hper 1) 1 y]

lemma rki_pd2_pd2_formula (X : ℝ × ℝ → ℝ) (hX : ContDiff ℝ ∞ X) (i j : Fin 2) (y : ℝ × ℝ) :
    pd2 i (pd2 j X) y = fderiv ℝ (fderiv ℝ X) y (dir2 i) (dir2 j) := by
  have hD : Differentiable ℝ (fderiv ℝ X) :=
    (hX.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)
  have hdj : fderiv ℝ (fun z => fderiv ℝ X z (dir2 j)) y =
      (fderiv ℝ (fderiv ℝ X) y).flip (dir2 j) := by
    have h := (hD y).hasFDerivAt.clm_apply (hasFDerivAt_const (dir2 j) y)
    refine h.fderiv.trans ?_
    simp
  unfold pd2
  rw [hdj]
  simp

lemma rki_pd2_comm (X : ℝ × ℝ → ℝ) (hX : ContDiff ℝ ∞ X) (i j : Fin 2) :
    pd2 i (pd2 j X) = pd2 j (pd2 i X) := by
  funext y
  rw [rki_pd2_pd2_formula X hX i j y, rki_pd2_pd2_formula X hX j i y]
  have hc : ContDiffAt ℝ ∞ X y := hX.contDiffAt
  have hs : IsSymmSndFDerivAt ℝ X y := hc.isSymmSndFDerivAt (by simp)
  exact hs.eq _ _

lemma rki_pd2_add (f g : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) : pd2 j (fun z => f z + g z) = fun y => pd2 j f y + pd2 j g y := by
  funext y
  unfold pd2
  have h := fderiv_add (hf y) (hg y)
  rw [show (fun z => f z + g z) = f + g from rfl, h]
  rfl

lemma rki_comm3 (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (i j : Fin 2) :
    pd2 j (pd2 j (pd2 i g)) = pd2 i (pd2 j (pd2 j g)) := by
  rw [rki_pd2_comm g hg j i, rki_pd2_comm (pd2 j g) (rki_contDiff_pd2 g hg j) j i]

lemma rki_lap2_pd2_comm (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (i : Fin 2) :
    lap2 (pd2 i g) = pd2 i (lap2 g) := by
  have hL : lap2 g = fun z => pd2 0 (pd2 0 g) z + pd2 1 (pd2 1 g) z := rfl
  rw [hL, rki_pd2_add _ _ (rki_differentiable_pd2 _ (rki_contDiff_pd2 g hg 0) 0)
    (rki_differentiable_pd2 _ (rki_contDiff_pd2 g hg 1) 1) i]
  funext y
  show pd2 0 (pd2 0 (pd2 i g)) y + pd2 1 (pd2 1 (pd2 i g)) y =
    pd2 i (pd2 0 (pd2 0 g)) y + pd2 i (pd2 1 (pd2 1 g)) y
  rw [rki_comm3 g hg i 0, rki_comm3 g hg i 1]

lemma rki_lap_ibp (c : ℝ) (hc : 0 < c) (A h : ℝ × ℝ → ℝ) (hA : ContDiff ℝ ∞ A)
    (hAper : ∀ y : ℝ × ℝ, A (y.1 + c, y.2) = A y) (hh : IsCylTest2 c h) :
    ∫ y in cellC c, A y * lap2 h y = ∫ y in cellC c, lap2 A y * h y := by
  obtain ⟨hhsm, hhper, L, hL⟩ := hh
  have hz1 : ∀ j : Fin 2, ∀ y : ℝ × ℝ, L < |y.2| → pd2 j h y = 0 :=
    fun j y hy => pd2_zero_far h L hL j y hy
  have hz2 : ∀ j k : Fin 2, ∀ y : ℝ × ℝ, L < |y.2| → pd2 k (pd2 j h) y = 0 :=
    fun j k y hy => pd2_zero_far (pd2 j h) L (fun z hz => hz1 j z hz) k y hy
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by simp)
  have hh1 : ContDiff ℝ 1 h := hhsm.of_le (by simp)
  -- one term of the Laplacian
  have T : ∀ j : Fin 2, ∫ y in cellC c, A y * pd2 j (pd2 j h) y =
      ∫ y in cellC c, pd2 j (pd2 j A) y * h y := by
    intro j
    have h1 := rki_cellIBP c hc A (pd2 j h) hA1
      ((rki_contDiff_pd2 h hhsm j).of_le (by simp)) hAper
      (rki_periodic_pd2 c h hhper j) L (hz1 j) j
    have h2 := rki_cellIBP c hc (pd2 j A) h
      ((rki_contDiff_pd2 A hA j).of_le (by simp)) hh1 (rki_periodic_pd2 c A hAper j)
      hhper L hL j
    rw [h1, h2, neg_neg]
  have I0 : IntegrableOn (fun y => A y * pd2 0 (pd2 0 h) y) (cellC c) := by
    apply rki_integrableOn_cellC _ _ c L
    · intro y hy
      simp only [hz2 0 0 y hy, mul_zero]
    · exact hA.continuous.mul (rki_contDiff_pd2 _ (rki_contDiff_pd2 h hhsm 0) 0).continuous
  have I1 : IntegrableOn (fun y => A y * pd2 1 (pd2 1 h) y) (cellC c) := by
    apply rki_integrableOn_cellC _ _ c L
    · intro y hy
      simp only [hz2 1 1 y hy, mul_zero]
    · exact hA.continuous.mul (rki_contDiff_pd2 _ (rki_contDiff_pd2 h hhsm 1) 1).continuous
  have J0 : IntegrableOn (fun y => pd2 0 (pd2 0 A) y * h y) (cellC c) := by
    apply rki_integrableOn_cellC _ _ c L
    · intro y hy
      simp only [hL y hy, mul_zero]
    · exact (rki_contDiff_pd2 _ (rki_contDiff_pd2 A hA 0) 0).continuous.mul hhsm.continuous
  have J1 : IntegrableOn (fun y => pd2 1 (pd2 1 A) y * h y) (cellC c) := by
    apply rki_integrableOn_cellC _ _ c L
    · intro y hy
      simp only [hL y hy, mul_zero]
    · exact (rki_contDiff_pd2 _ (rki_contDiff_pd2 A hA 1) 1).continuous.mul hhsm.continuous
  have s1 : ∫ y in cellC c, A y * lap2 h y =
      (∫ y in cellC c, A y * pd2 0 (pd2 0 h) y) + (∫ y in cellC c, A y * pd2 1 (pd2 1 h) y) := by
    calc ∫ y in cellC c, A y * lap2 h y
        = ∫ y in cellC c, (A y * pd2 0 (pd2 0 h) y + A y * pd2 1 (pd2 1 h) y) := by
          congr 1
          funext y
          unfold lap2
          ring
      _ = _ := integral_add I0 I1
  have s2 : ∫ y in cellC c, lap2 A y * h y =
      (∫ y in cellC c, pd2 0 (pd2 0 A) y * h y) + (∫ y in cellC c, pd2 1 (pd2 1 A) y * h y) := by
    calc ∫ y in cellC c, lap2 A y * h y
        = ∫ y in cellC c, (pd2 0 (pd2 0 A) y * h y + pd2 1 (pd2 1 A) y * h y) := by
          congr 1
          funext y
          unfold lap2
          ring
      _ = _ := integral_add J0 J1
  rw [s1, s2, T 0, T 1]

theorem regKerIBP : RegKerIBP := by
  intro c ε hc hε h hh i
  have hcalc := regKerCalc c ε hc hε
  obtain ⟨hΓs, hΓper, hK, hρ⟩ := hcalc
  have hKf : cylKerReg c ε i = pd2 i (cylGreenReg c ε) := funext fun y => (hK i y).symm
  have hRf : cylRho c ε = lap2 (cylGreenReg c ε) := funext fun y => (hρ y).symm
  rw [hKf, hRf]
  obtain ⟨hhsm, hhper, L, hL⟩ := hh
  have hLΓ : ContDiff ℝ ∞ (lap2 (cylGreenReg c ε)) := by
    show ContDiff ℝ ∞ (fun y => pd2 0 (pd2 0 (cylGreenReg c ε)) y +
      pd2 1 (pd2 1 (cylGreenReg c ε)) y)
    exact (rki_contDiff_pd2 _ (rki_contDiff_pd2 _ hΓs 0) 0).add
      (rki_contDiff_pd2 _ (rki_contDiff_pd2 _ hΓs 1) 1)
  have step1 := rki_lap_ibp c hc (pd2 i (cylGreenReg c ε)) h
    (rki_contDiff_pd2 _ hΓs i) (rki_periodic_pd2 c _ hΓper i) ⟨hhsm, hhper, L, hL⟩
  have step2 := rki_lap2_pd2_comm (cylGreenReg c ε) hΓs i
  have step3 := rki_cellIBP c hc (lap2 (cylGreenReg c ε)) h
    (hLΓ.of_le (by simp)) (hhsm.of_le (by simp)) (rki_periodic_lap c _ hΓper) hhper L hL i
  rw [step1, step2, ← neg_neg (∫ y in cellC c, lap2 (cylGreenReg c ε) y * pd2 i h y), step3]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
