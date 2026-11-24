import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2

/-!
# Helper for `PartII-b:T11/2/2/2`: real/imaginary splitting of `flatTransposeC (perpC ψ)`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem contDiff_cpdC (F : Coord → ℂ) (hF : ContDiff ℝ ∞ F) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => cpdC j F x) := by
  unfold cpdC
  exact (hF.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const

theorem contDiff_cpd (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => cpd j f x) := by
  unfold cpd
  exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const

theorem cpd_re (F : Coord → ℂ) (hF : ContDiff ℝ ∞ F) (j : Fin 3) (x : Coord) :
    cpd j (fun z => (F z).re) x = (cpdC j F x).re := by
  have h : HasFDerivAt (fun z => (F z).re) (Complex.reCLM.comp (fderiv ℝ F x)) x :=
    Complex.reCLM.hasFDerivAt.comp x ((hF.differentiable (by simp)) x).hasFDerivAt
  rw [cpd, h.fderiv]; rfl

theorem cpd_im (F : Coord → ℂ) (hF : ContDiff ℝ ∞ F) (j : Fin 3) (x : Coord) :
    cpd j (fun z => (F z).im) x = (cpdC j F x).im := by
  have h : HasFDerivAt (fun z => (F z).im) (Complex.imCLM.comp (fderiv ℝ F x)) x :=
    Complex.imCLM.hasFDerivAt.comp x ((hF.differentiable (by simp)) x).hasFDerivAt
  rw [cpd, h.fderiv]; rfl

theorem cpdC_eq (F : Coord → ℂ) (hF : ContDiff ℝ ∞ F) (j : Fin 3) (x : Coord) :
    cpdC j F x = ((cpd j (fun z => (F z).re) x : ℝ) : ℂ) +
      Complex.I * ((cpd j (fun z => (F z).im) x : ℝ) : ℂ) := by
  rw [cpd_re F hF, cpd_im F hF]
  apply Complex.ext <;> simp

theorem dualEqCpdCCpdCEq (G : Coord → ℂ) (hG : ContDiff ℝ ∞ G) (j k : Fin 3) (x : Coord) :
    cpdC j (fun y => cpdC k G y) x =
      ((cpd j (fun y => cpd k (fun z => (G z).re) y) x : ℝ) : ℂ) +
        Complex.I * ((cpd j (fun y => cpd k (fun z => (G z).im) y) x : ℝ) : ℂ) := by
  rw [cpdC_eq _ (contDiff_cpdC G hG k) j x]
  have e1 : (fun z => (cpdC k G z).re) = fun y => cpd k (fun z => (G z).re) y :=
    funext fun y => (cpd_re G hG k y).symm
  have e2 : (fun z => (cpdC k G z).im) = fun y => cpd k (fun z => (G z).im) y :=
    funext fun y => (cpd_im G hG k y).symm
  simp only [e1, e2]

/-- real scalar form of `flatTranspose` -/
def flatScalar (ν : ℝ) (μ : ℂ) (g : Coord → ℝ) (x : Coord) : ℂ :=
  (μ - 1) * (g x : ℂ) - ((x.1 * cpd 0 g x : ℝ) : ℂ) -
    ((ν * x.1 * (cpd 1 (fun y => cpd 1 g y) x + cpd 2 (fun y => cpd 2 g y) x) : ℝ) : ℂ)

theorem flatScalar_split (ν : ℝ) (μ : ℂ) (G : Coord → ℂ) (hG : ContDiff ℝ ∞ G) (x : Coord) :
    (μ - 1) * G x - (x.1 : ℂ) * cpdC 0 G x -
      (ν : ℂ) * (x.1 : ℂ) * (cpdC 1 (fun y => cpdC 1 G y) x + cpdC 2 (fun y => cpdC 2 G y) x) =
    flatScalar ν μ (fun z => (G z).re) x + Complex.I * flatScalar ν μ (fun z => (G z).im) x := by
  rw [dualEqCpdCCpdCEq G hG 1 1 x, dualEqCpdCCpdCEq G hG 2 2 x, cpdC_eq G hG 0 x]
  unfold flatScalar
  have hG' : G x = (((G x).re : ℝ) : ℂ) + Complex.I * (((G x).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hG']
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- real-part stream field -/
def dtStream (ψ : Coord → ℝ) : Coord → Fin 2 → ℝ := fun y => ![cpd 2 ψ y, -cpd 1 ψ y]

theorem flatTranspose_eq_scalar (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) :
    flatTranspose ν μ Ψ x i = flatScalar ν μ (fun y => Ψ y i) x := rfl

theorem perpC_smooth (ψ : Coord → ℂ) (hψ : ContDiff ℝ ∞ ψ) (i : Fin 2) :
    ContDiff ℝ ∞ (fun y => perpC ψ y i) := by
  fin_cases i
  · exact contDiff_cpdC ψ hψ 2
  · exact (contDiff_cpdC ψ hψ 1).neg

theorem perpC_re (ψ : Coord → ℂ) (hψ : ContDiff ℝ ∞ ψ) (i : Fin 2) :
    (fun y => (perpC ψ y i).re) = fun y => dtStream (fun z => (ψ z).re) y i := by
  funext y
  fin_cases i
  · simp [perpC, dtStream, cpd_re ψ hψ]
  · simp [perpC, dtStream, cpd_re ψ hψ]

theorem perpC_im (ψ : Coord → ℂ) (hψ : ContDiff ℝ ∞ ψ) (i : Fin 2) :
    (fun y => (perpC ψ y i).im) = fun y => dtStream (fun z => (ψ z).im) y i := by
  funext y
  fin_cases i
  · simp [perpC, dtStream, cpd_im ψ hψ]
  · simp [perpC, dtStream, cpd_im ψ hψ]

theorem flatTransposeC_perpC_split (ν : ℝ) (μ : ℂ) (ψ : Coord → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (x : Coord) (i : Fin 2) :
    flatTransposeC ν μ (perpC ψ) x i =
      flatTranspose ν μ (dtStream (fun z => (ψ z).re)) x i +
        Complex.I * flatTranspose ν μ (dtStream (fun z => (ψ z).im)) x i := by
  unfold flatTransposeC
  rw [flatScalar_split ν μ (fun y => perpC ψ y i) (perpC_smooth ψ hψ i) x]
  rw [flatTranspose_eq_scalar, flatTranspose_eq_scalar]
  rw [perpC_re ψ hψ i, perpC_im ψ hψ i]

/-! ### locally vanishing functions -/

theorem cpd_zero_on (U : Set Coord) (hU : IsOpen U) (f : Coord → ℝ) (hf : ∀ y ∈ U, f y = 0)
    (j : Fin 3) : ∀ x ∈ U, cpd j f x = 0 := by
  intro x hx
  have h : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy using hf y hy
  simp [cpd, h.fderiv_eq]

theorem flatTranspose_dtStream_zero (ν : ℝ) (μ : ℂ) (U : Set Coord) (hU : IsOpen U)
    (ψ : Coord → ℝ) (hψ : ∀ y ∈ U, ψ y = 0) (x : Coord) (hx : x ∈ U) (i : Fin 2) :
    flatTranspose ν μ (dtStream ψ) x i = 0 := by
  have h1 := cpd_zero_on U hU ψ hψ 1
  have h2 := cpd_zero_on U hU ψ hψ 2
  have h11 := cpd_zero_on U hU _ h1
  have h22 := cpd_zero_on U hU _ h2
  have h12 := cpd_zero_on U hU _ h2
  have hneg : ∀ y ∈ U, -cpd 1 ψ y = 0 := fun y hy => by rw [h1 y hy]; simp
  fin_cases i
  · have a0 := cpd_zero_on U hU _ h2 0 x hx
    have a1 := cpd_zero_on U hU _ (cpd_zero_on U hU _ h2 1) 1 x hx
    have a2 := cpd_zero_on U hU _ (cpd_zero_on U hU _ h2 2) 2 x hx
    simp only [flatTranspose, dtStream]
    simp [h2 x hx, a0, a1, a2]
  · have a0 := cpd_zero_on U hU _ hneg 0 x hx
    have a1 := cpd_zero_on U hU _ (cpd_zero_on U hU _ hneg 1) 1 x hx
    have a2 := cpd_zero_on U hU _ (cpd_zero_on U hU _ hneg 2) 2 x hx
    simp only [flatTranspose, dtStream]
    simp [hneg x hx, a0, a1, a2]

theorem flatTranspose_dtStream_continuous (ν : ℝ) (μ : ℂ) (ψ : Coord → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin 2) : Continuous fun x => flatTranspose ν μ (dtStream ψ) x i := by
  have hs : ContDiff ℝ ∞ (fun y => dtStream ψ y i) := by
    fin_cases i
    · exact contDiff_cpd ψ hψ 2
    · exact (contDiff_cpd ψ hψ 1).neg
  rw [show (fun x => flatTranspose ν μ (dtStream ψ) x i) =
    fun x => flatScalar ν μ (fun y => dtStream ψ y i) x from rfl]
  unfold flatScalar
  set g := fun y => dtStream ψ y i
  have c0 := (contDiff_cpd g hs 0).continuous
  have c1 := (contDiff_cpd _ (contDiff_cpd g hs 1) 1).continuous
  have c2 := (contDiff_cpd _ (contDiff_cpd g hs 2) 2).continuous
  have cg := hs.continuous
  have hx1 : Continuous fun x : Coord => x.1 := continuous_fst
  fun_prop

end UnforcedLeray.Short.IIb
