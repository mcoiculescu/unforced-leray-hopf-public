import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.OrderClosed

/-!
# Integration by parts on a period cell (`CellIBP`)

Source-free generic calculus.  The cell integral over `Ioc t (t+c) ×ˢ univ` is an iterated integral
(`integral_prod`, `integral_prod_symm`).  For `i = 0` the `q`-slices are integrated by parts on
`[t, t+c]` with vanishing boundary term by periodicity; for `i = 1` the `η`-slices are integrated by
parts on `[-M, M]`, `M = L + 1`, where `B` and `∂B` vanish for `|η| > L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

lemma hasDerivAt_slice0 (F : ℝ × ℝ → ℝ) (hF : Differentiable ℝ F) (q η : ℝ) :
    HasDerivAt (fun x => F (x, η)) (pd2 0 F (q, η)) q := by
  have hl : HasDerivAt (fun x : ℝ => ((x, η) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q :=
    (hasDerivAt_id' q).prodMk (hasDerivAt_const q η)
  have hc : HasFDerivAt F (fderiv ℝ F (q, η)) (q, η) := (hF (q, η)).hasFDerivAt
  have h2 := hc.comp_hasDerivAt q hl
  have hdir : pd2 0 F (q, η) = fderiv ℝ F (q, η) ((1 : ℝ), (0 : ℝ)) := by
    simp [pd2, dir2]
  rw [hdir]
  exact h2

lemma hasDerivAt_slice1 (F : ℝ × ℝ → ℝ) (hF : Differentiable ℝ F) (q η : ℝ) :
    HasDerivAt (fun x => F (q, x)) (pd2 1 F (q, η)) η := by
  have hl : HasDerivAt (fun x : ℝ => ((q, x) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id' η)
  have hc : HasFDerivAt F (fderiv ℝ F (q, η)) (q, η) := (hF (q, η)).hasFDerivAt
  have h2 := hc.comp_hasDerivAt η hl
  have hdir : pd2 1 F (q, η) = fderiv ℝ F (q, η) ((0 : ℝ), (1 : ℝ)) := by
    simp [pd2, dir2]
  rw [hdir]
  exact h2

lemma pd2_cont (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 1 F) (j : Fin 2) : Continuous (pd2 j F) := by
  unfold pd2
  exact (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma pd2_zero_far (B : ℝ × ℝ → ℝ) (L : ℝ) (hL : ∀ y : ℝ × ℝ, L < |y.2| → B y = 0)
    (j : Fin 2) (y : ℝ × ℝ) (hy : L < |y.2|) : pd2 j B y = 0 := by
  have hopen : IsOpen {z : ℝ × ℝ | L < |z.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : B =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact hL z hz
  have hfd : fderiv ℝ B y = 0 := by
    rw [hev.fderiv_eq]
    simp
  unfold pd2
  rw [hfd]
  simp

lemma integrableOn_cellS (F : ℝ × ℝ → ℝ) (hF : Continuous F) (t c L : ℝ)
    (hz : ∀ y : ℝ × ℝ, L < |y.2| → F y = 0) :
    IntegrableOn F (Ioc t (t + c) ×ˢ (univ : Set ℝ)) := by
  set K : Set (ℝ × ℝ) := Icc t (t + c) ×ˢ Icc (-L) L with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKint : IntegrableOn F K := hF.continuousOn.integrableOn_compact hKc
  have hKmeas : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hind : Integrable (K.indicator F) := (integrable_indicator_iff hKmeas).2 hKint
  refine IntegrableOn.congr_fun hind.integrableOn ?_ (measurableSet_Ioc.prod MeasurableSet.univ)
  intro y hy
  by_cases hyK : y ∈ K
  · rw [indicator_of_mem hyK]
  · rw [indicator_of_notMem hyK]
    symm
    apply hz
    by_contra hcon
    push_neg at hcon
    exact hyK ⟨⟨hy.1.1.le, hy.1.2⟩, abs_le.1 hcon⟩

lemma restrict_cellS_eq (t c : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Ioc t (t + c) ×ˢ (univ : Set ℝ)) =
      (volume.restrict (Ioc t (t + c))).prod volume := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Iterated form with the `η`-integral inside (`integral_prod_symm`). -/
lemma cellS_eq_iter_eta (F : ℝ × ℝ → ℝ) (t c : ℝ)
    (hF : IntegrableOn F (Ioc t (t + c) ×ˢ (univ : Set ℝ))) :
    ∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), F y =
      ∫ η : ℝ, ∫ q in Ioc t (t + c), F (q, η) := by
  rw [IntegrableOn, restrict_cellS_eq] at hF
  rw [restrict_cellS_eq]
  exact integral_prod_symm F hF

/-- Iterated form with the `q`-integral inside (`integral_prod`). -/
lemma cellS_eq_iter_q (F : ℝ × ℝ → ℝ) (t c : ℝ)
    (hF : IntegrableOn F (Ioc t (t + c) ×ˢ (univ : Set ℝ))) :
    ∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), F y =
      ∫ q in Ioc t (t + c), ∫ η : ℝ, F (q, η) := by
  rw [IntegrableOn, restrict_cellS_eq] at hF
  rw [restrict_cellS_eq]
  exact integral_prod F hF

/-- The `q`-slice identity: periodicity kills the boundary term. -/
lemma slice_ibp0 (A B : ℝ × ℝ → ℝ) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) (c t : ℝ)
    (hAper : ∀ y : ℝ × ℝ, A (y.1 + c, y.2) = A y) (hBper : ∀ y : ℝ × ℝ, B (y.1 + c, y.2) = B y)
    (η : ℝ) :
    ∫ q in t..(t + c), A (q, η) * pd2 0 B (q, η) =
      -∫ q in t..(t + c), pd2 0 A (q, η) * B (q, η) := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hBd : Differentiable ℝ B := hB.differentiable (by norm_num)
  have hcont1 : Continuous (fun q : ℝ => pd2 0 A (q, η)) :=
    (pd2_cont A hA 0).comp (continuous_id.prodMk continuous_const)
  have hcont2 : Continuous (fun q : ℝ => pd2 0 B (q, η)) :=
    (pd2_cont B hB 0).comp (continuous_id.prodMk continuous_const)
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := t) (b := t + c) (u := fun q => A (q, η)) (v := fun q => B (q, η))
    (u' := fun q => pd2 0 A (q, η)) (v' := fun q => pd2 0 B (q, η))
    (fun x _ => hasDerivAt_slice0 A hAd x η) (fun x _ => hasDerivAt_slice0 B hBd x η)
    (hcont1.intervalIntegrable t (t + c)) (hcont2.intervalIntegrable t (t + c))
  have h1 : A (t + c, η) = A (t, η) := hAper (t, η)
  have h2 : B (t + c, η) = B (t, η) := hBper (t, η)
  rw [key, h1, h2]
  ring

/-- The `η`-slice identity on `ℝ` for a function vanishing for `|η| > L`. -/
lemma slice_ibp1 (A B : ℝ × ℝ → ℝ) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) (L : ℝ)
    (hL : ∀ y : ℝ × ℝ, L < |y.2| → B y = 0) (q : ℝ) :
    ∫ η : ℝ, A (q, η) * pd2 1 B (q, η) = -∫ η : ℝ, pd2 1 A (q, η) * B (q, η) := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hBd : Differentiable ℝ B := hB.differentiable (by norm_num)
  set M : ℝ := |L| + 1 with hM
  have hMpos : L < M := by rw [hM]; linarith [le_abs_self L]
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hMabs : |M| = M := abs_of_nonneg hM0
  have hcont1 : Continuous (fun η : ℝ => pd2 1 A (q, η)) :=
    (pd2_cont A hA 1).comp (continuous_const.prodMk continuous_id)
  have hcont2 : Continuous (fun η : ℝ => pd2 1 B (q, η)) :=
    (pd2_cont B hB 1).comp (continuous_const.prodMk continuous_id)
  have hMM : -M ≤ M := by linarith
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -M) (b := M) (u := fun η => A (q, η)) (v := fun η => B (q, η))
    (u' := fun η => pd2 1 A (q, η)) (v' := fun η => pd2 1 B (q, η))
    (fun x _ => hasDerivAt_slice1 A hAd q x) (fun x _ => hasDerivAt_slice1 B hBd q x)
    (hcont1.intervalIntegrable (-M) M) (hcont2.intervalIntegrable (-M) M)
  have hBM : B (q, M) = 0 := hL (q, M) (by show L < |M|; rw [hMabs]; exact hMpos)
  have hBnM : B (q, -M) = 0 := hL (q, -M) (by show L < |-M|; rw [abs_neg, hMabs]; exact hMpos)
  -- zero outside `Ioc (-M) M`
  have hlt_of : ∀ η : ℝ, η ∉ Ioc (-M) M → L < |η| := by
    intro η hη
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hη
    rcases hη with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hzf : ∀ η : ℝ, η ∉ Ioc (-M) M → A (q, η) * pd2 1 B (q, η) = 0 := by
    intro η hη
    rw [pd2_zero_far B L hL 1 (q, η) (hlt_of η hη), mul_zero]
  have hzg : ∀ η : ℝ, η ∉ Ioc (-M) M → pd2 1 A (q, η) * B (q, η) = 0 := by
    intro η hη
    rw [hL (q, η) (hlt_of η hη), mul_zero]
  rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzf).symm,
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzg).symm]
  rw [← intervalIntegral.integral_of_le hMM, ← intervalIntegral.integral_of_le hMM]
  rw [key, hBM, hBnM]
  ring

lemma cellIBP_zero (c t : ℝ) (hc : 0 < c) (A B : ℝ × ℝ → ℝ) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (hAper : ∀ y : ℝ × ℝ, A (y.1 + c, y.2) = A y) (hBper : ∀ y : ℝ × ℝ, B (y.1 + c, y.2) = B y)
    (L : ℝ) (hL : ∀ y : ℝ × ℝ, L < |y.2| → B y = 0) :
    ∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), A y * pd2 0 B y =
      -∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), pd2 0 A y * B y := by
  have hAc : Continuous A := hA.continuous
  have hBc : Continuous B := hB.continuous
  have hf : Continuous (fun y : ℝ × ℝ => A y * pd2 0 B y) := hAc.mul (pd2_cont B hB 0)
  have hg : Continuous (fun y : ℝ × ℝ => pd2 0 A y * B y) := (pd2_cont A hA 0).mul hBc
  have hfi := integrableOn_cellS _ hf t c L
    (fun y hy => by
      show A y * pd2 0 B y = 0
      rw [pd2_zero_far B L hL 0 y hy, mul_zero])
  have hgi := integrableOn_cellS _ hg t c L
    (fun y hy => by
      show pd2 0 A y * B y = 0
      rw [hL y hy, mul_zero])
  rw [cellS_eq_iter_eta _ t c hfi, cellS_eq_iter_eta _ t c hgi, ← MeasureTheory.integral_neg]
  congr 1
  funext η
  rw [← intervalIntegral.integral_of_le (by linarith : t ≤ t + c),
    ← intervalIntegral.integral_of_le (by linarith : t ≤ t + c)]
  exact slice_ibp0 A B hA hB c t hAper hBper η

lemma cellIBP_one (c t : ℝ) (hc : 0 < c) (A B : ℝ × ℝ → ℝ) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (L : ℝ) (hL : ∀ y : ℝ × ℝ, L < |y.2| → B y = 0) :
    ∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), A y * pd2 1 B y =
      -∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), pd2 1 A y * B y := by
  have hAc : Continuous A := hA.continuous
  have hBc : Continuous B := hB.continuous
  have hf : Continuous (fun y : ℝ × ℝ => A y * pd2 1 B y) := hAc.mul (pd2_cont B hB 1)
  have hg : Continuous (fun y : ℝ × ℝ => pd2 1 A y * B y) := (pd2_cont A hA 1).mul hBc
  have hfi := integrableOn_cellS _ hf t c L
    (fun y hy => by
      show A y * pd2 1 B y = 0
      rw [pd2_zero_far B L hL 1 y hy, mul_zero])
  have hgi := integrableOn_cellS _ hg t c L
    (fun y hy => by
      show pd2 1 A y * B y = 0
      rw [hL y hy, mul_zero])
  rw [cellS_eq_iter_q _ t c hfi, cellS_eq_iter_q _ t c hgi, ← MeasureTheory.integral_neg]
  congr 1
  funext q
  exact slice_ibp1 A B hA hB L hL q

theorem cellIBP : CellIBP := by
  intro c hc t A B hA hB hAper hBper hBcpt i
  obtain ⟨L, hL⟩ := hBcpt
  fin_cases i
  · exact cellIBP_zero c t hc A B hA hB hAper hBper L hL
  · exact cellIBP_one c t hc A B hA hB L hL

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
