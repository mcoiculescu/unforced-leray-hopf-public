import UnforcedLeray.Units.B0418
import UnforcedLeray.Units.B0414.Orthogonal

/-!
# B0421 helper: the free similarity semigroup `S_ν(r)` on complex fields `L^q(ℝ³; ℂ³)`

Blueprint unit B0421 (`eq:free-stress-9`, `eq:free-stress-10`), `paper/main.tex` lines
7427–7445. The phase space `Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` of tex 7313–7317 has complex

while the drafted semigroup `B0418.freeSemigroupLp` (unit B0418, tex 7411–7427) acts on real
fields `L^q(ℝ³; ℝ³)`. The manuscript applies `S_ν(r)` to complex fields componentwise; this
file makes that precise.

* `cx A`: the complexification `F ↦ A(Re F) + i A(Im F)` of a real bounded operator `A` on
  `L^q(ℝ³; ℝ³)`, a `ℂ`-linear bounded operator on `L^q(ℝ³; ℂ³)` (the construction of
  `RieszLp.lerayC`, `Lib/LerayC/Complex.lean`, made generic). `cx_comp`, `cx_id`: it is
  multiplicative; `norm_cx_le`: `‖cx A‖ ≤ 2‖A‖`; `norm_cx_two_le`: `‖cx A‖ ≤ ‖A‖` at `q = 2`
  (Pythagoras through `B0414.re_inner_L2C`).
* `freeC hq ν r = cx (B0418.freeSemigroupLp hq ν r)`: `S_ν(r)` on `L^q(ℝ³; ℂ³)`, with
  `coeFn_freeC` (the literal formula of `eq:free-stress-7` on real and imaginary parts),
  `freeC_zero`, `freeC_add` (semigroup law, `ν ≥ 0`), `continuousOn_freeC` (strong continuity),
  `norm_freeC_le` (`‖S_ν(r)‖ ≤ 2e^{-γ_q r}`, from `eq:free-stress-8`, B0419) and
  `norm_freeC_two_le` (`‖S_ν(r)‖_{L²→L²} ≤ e^{-r/4}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0421

open UnforcedLeray.RieszLp UnforcedLeray.B0414 UnforcedLeray.B0418
open UnforcedLeray.AncientLocalization
open UnforcedLeray.PhaseSpace (CVec3)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Real and imaginary parts on `L^p` -/

/-- `F = Re F + i Im F` on `L^p(ℝ³; ℂ³)`. -/
theorem ofRe_re_add_ofIm_im (F : Lp CVec3 p (volume : Measure Space)) :
    ofReV.compLpL p volume (reV.compLpL p volume F) +
      ofImV.compLpL p volume (imV.compLpL p volume F) = F := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofReV.compLpL p volume (reV.compLpL p volume F))
      (ofImV.compLpL p volume (imV.compLpL p volume F)),
    ofReV.coeFn_compLpL (μ := (volume : Measure Space)) (p := p) (reV.compLpL p volume F),
    ofImV.coeFn_compLpL (μ := (volume : Measure Space)) (p := p) (imV.compLpL p volume F),
    reV.coeFn_compLpL (μ := (volume : Measure Space)) (p := p) F,
    imV.coeFn_compLpL (μ := (volume : Measure Space)) (p := p) F] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, h4, h5, ofReV_reV_add_ofImV_imV]

/-- Two complex fields with equal real and imaginary parts are equal. -/
theorem ext_reim {F G : Lp CVec3 p (volume : Measure Space)}
    (h1 : reV.compLpL p volume F = reV.compLpL p volume G)
    (h2 : imV.compLpL p volume F = imV.compLpL p volume G) : F = G := by
  rw [← ofRe_re_add_ofIm_im F, ← ofRe_re_add_ofIm_im G, h1, h2]

/-! ### Complexification of a real operator -/

/-- The real-linear complexification `F ↦ A(Re F) + i A(Im F)`. -/
def cxR (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space)) :
    Lp CVec3 p (volume : Measure Space) →L[ℝ] Lp CVec3 p (volume : Measure Space) :=
  (ofReV.compLpL p volume).comp (A.comp (reV.compLpL p volume)) +
    (ofImV.compLpL p volume).comp (A.comp (imV.compLpL p volume))

theorem cxR_apply (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    (F : Lp CVec3 p (volume : Measure Space)) :
    cxR A F = ofReV.compLpL p volume (A (reV.compLpL p volume F)) +
      ofImV.compLpL p volume (A (imV.compLpL p volume F)) := rfl

set_option maxHeartbeats 1600000 in
theorem cxR_I_smul (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    (F : Lp CVec3 p (volume : Measure Space)) :
    cxR A (Complex.I • F) = Complex.I • cxR A F := by
  rw [cxR_apply, cxR_apply]
  rw [reV_compLpL_I_smul]
  rw [imV_compLpL_I_smul]
  rw [A.map_neg (imV.compLpL p volume F)]
  rw [(ofReV.compLpL p volume).map_neg (A (imV.compLpL p volume F))]
  rw [smul_add]
  rw [I_smul_ofReV_compLpL]
  rw [I_smul_ofImV_compLpL]
  abel

theorem cxR_smul (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    (c : ℂ) (F : Lp CVec3 p (volume : Measure Space)) :
    cxR A (c • F) = c • cxR A F := by
  rw [smul_eq_re_add_im c F, smul_eq_re_add_im c (cxR A F), map_add, map_smul, map_smul,
    cxR_I_smul]

/-- The complexification as a `ℂ`-linear map. -/
def cxLin (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space)) :
    Lp CVec3 p (volume : Measure Space) →ₗ[ℂ] Lp CVec3 p (volume : Measure Space) where
  toFun := cxR A
  map_add' := map_add _
  map_smul' c F := cxR_smul A c F

/-- **The complexification** `cx A F = A(Re F) + i A(Im F)` of a real bounded operator on
`L^p(ℝ³; ℝ³)`: a `ℂ`-linear bounded operator on `L^p(ℝ³; ℂ³)` acting componentwise on real
and imaginary parts. -/
def cx (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space)) :
    Lp CVec3 p (volume : Measure Space) →L[ℂ] Lp CVec3 p (volume : Measure Space) :=
  LinearMap.mkContinuous (cxLin A) ‖cxR A‖ fun F => (cxR A).le_opNorm F

theorem cx_apply (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    (F : Lp CVec3 p (volume : Measure Space)) :
    cx A F = ofReV.compLpL p volume (A (reV.compLpL p volume F)) +
      ofImV.compLpL p volume (A (imV.compLpL p volume F)) := rfl

/-- `Re (cx A F) = A (Re F)`. -/
theorem re_cx (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    (F : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (cx A F) = A (reV.compLpL p volume F) := by
  rw [cx_apply, map_add, reV_ofReV_compLpL, reV_ofImV_compLpL, add_zero]

/-- `Im (cx A F) = A (Im F)`. -/
theorem im_cx (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    (F : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (cx A F) = A (imV.compLpL p volume F) := by
  rw [cx_apply, map_add, imV_ofReV_compLpL, imV_ofImV_compLpL, zero_add]

theorem cx_comp (A B : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space)) :
    cx (A.comp B) = (cx A).comp (cx B) := by
  ext1 F
  refine ext_reim ?_ ?_
  · simp only [ContinuousLinearMap.comp_apply]
    rw [re_cx, re_cx, re_cx]
    rfl
  · simp only [ContinuousLinearMap.comp_apply]
    rw [im_cx, im_cx, im_cx]
    rfl

theorem cx_id : cx (ContinuousLinearMap.id ℝ (Lp Space p (volume : Measure Space))) = 1 := by
  ext1 F
  refine ext_reim ?_ ?_
  · rw [re_cx, ContinuousLinearMap.id_apply, one_apply_eq_self]
  · rw [im_cx, ContinuousLinearMap.id_apply, one_apply_eq_self]

/-- `‖cx A‖ ≤ 2 ‖A‖` for every exponent. -/
theorem norm_cx_le (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space)) :
    ‖cx A‖ ≤ 2 * ‖A‖ := by
  have hre : ‖reV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_reV_le
  have him : ‖imV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_imV_le
  have hore : ‖ofReV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_ofReV_le
  have hoim : ‖ofImV.compLpL p (volume : Measure Space)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans norm_ofImV_le
  have hA := norm_nonneg A
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
  rw [cx_apply]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖ofReV.compLpL p volume (A (reV.compLpL p volume F))‖ ≤ ‖A‖ * ‖F‖ := by
    have a1 := (ofReV.compLpL p volume).le_opNorm (A (reV.compLpL p volume F))
    have a2 := A.le_opNorm (reV.compLpL p volume F)
    have a3 := (reV.compLpL p volume).le_opNorm F
    have n1 := norm_nonneg (A (reV.compLpL p volume F))
    have n3 := norm_nonneg F
    calc _ ≤ 1 * ‖A (reV.compLpL p volume F)‖ := a1.trans (mul_le_mul_of_nonneg_right hore n1)
      _ ≤ ‖A‖ * ‖reV.compLpL p volume F‖ := by rw [one_mul]; exact a2
      _ ≤ ‖A‖ * ‖F‖ := mul_le_mul_of_nonneg_left (a3.trans (by nlinarith)) hA
  have h2 : ‖ofImV.compLpL p volume (A (imV.compLpL p volume F))‖ ≤ ‖A‖ * ‖F‖ := by
    have a1 := (ofImV.compLpL p volume).le_opNorm (A (imV.compLpL p volume F))
    have a2 := A.le_opNorm (imV.compLpL p volume F)
    have a3 := (imV.compLpL p volume).le_opNorm F
    have n1 := norm_nonneg (A (imV.compLpL p volume F))
    have n3 := norm_nonneg F
    calc _ ≤ 1 * ‖A (imV.compLpL p volume F)‖ := a1.trans (mul_le_mul_of_nonneg_right hoim n1)
      _ ≤ ‖A‖ * ‖imV.compLpL p volume F‖ := by rw [one_mul]; exact a2
      _ ≤ ‖A‖ * ‖F‖ := mul_le_mul_of_nonneg_left (a3.trans (by nlinarith)) hA
  calc _ ≤ ‖A‖ * ‖F‖ + ‖A‖ * ‖F‖ := add_le_add h1 h2
    _ = 2 * ‖A‖ * ‖F‖ := by ring

/-- Pythagoras in `L²(ℝ³; ℂ³)`: `‖F‖² = ‖Re F‖² + ‖Im F‖²`. -/
theorem norm_sq_eq_re_im (F : Lp CVec3 2 (volume : Measure Space)) :
    ‖F‖ ^ 2 = ‖reV.compLpL 2 volume F‖ ^ 2 + ‖imV.compLpL 2 volume F‖ ^ 2 := by
  have h := re_inner_L2C F F
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) F
  rw [RCLike.re_to_complex] at h2
  rw [← h2, h]

/-- At `q = 2`, `‖cx A‖ ≤ ‖A‖`. -/
theorem norm_cx_two_le
    (A : Lp Space 2 (volume : Measure Space) →L[ℝ] Lp Space 2 (volume : Measure Space)) :
    ‖cx A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun F => ?_
  have hsq : ‖cx A F‖ ^ 2 ≤ (‖A‖ * ‖F‖) ^ 2 := by
    rw [norm_sq_eq_re_im (cx A F), re_cx, im_cx, mul_pow, norm_sq_eq_re_im F, mul_add]
    have e1 : ‖A (reV.compLpL 2 volume F)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖reV.compLpL 2 volume F‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    have e2 : ‖A (imV.compLpL 2 volume F)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖imV.compLpL 2 volume F‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-! ### The free semigroup on complex fields -/

/-- **`S_ν(r)` on `L^p(ℝ³; ℂ³)`** (tex 7414–7417, applied componentwise to complex fields):
the complexification of the B0418 operator `freeSemigroupLp hp ν r`. -/
def freeC (hp : p ≠ ∞) (ν r : ℝ) :
    Lp CVec3 p (volume : Measure Space) →L[ℂ] Lp CVec3 p (volume : Measure Space) :=
  cx (freeSemigroupLp hp ν r)

/-- The literal formula `eq:free-stress-7`: `S_ν(r)F = S_ν(r)(Re F) + i S_ν(r)(Im F)` with
`S_ν(r)h(y) = e^{r/2} [e^{ν(e^r-1)Δ}h](e^{r/2}y)` (`AncientLocalization.freeEvolution`). -/
theorem coeFn_freeC (hp : p ≠ ∞) (ν r : ℝ) (F : Lp CVec3 p (volume : Measure Space)) :
    (freeC hp ν r F : Space → CVec3) =ᵐ[volume] fun y =>
      ofReV (freeEvolution ν r (reV.compLpL p volume F : SpatialField) y) +
        ofImV (freeEvolution ν r (imV.compLpL p volume F : SpatialField) y) := by
  rw [freeC, cx_apply]
  filter_upwards [Lp.coeFn_add
      (ofReV.compLpL p volume (freeSemigroupLp hp ν r (reV.compLpL p volume F)))
      (ofImV.compLpL p volume (freeSemigroupLp hp ν r (imV.compLpL p volume F))),
    ofReV.coeFn_compLpL (μ := (volume : Measure Space)) (p := p)
      (freeSemigroupLp hp ν r (reV.compLpL p volume F)),
    ofImV.coeFn_compLpL (μ := (volume : Measure Space)) (p := p)
      (freeSemigroupLp hp ν r (imV.compLpL p volume F)),
    coeFn_freeSemigroupLp hp ν r (reV.compLpL p volume F),
    coeFn_freeSemigroupLp hp ν r (imV.compLpL p volume F)] with y h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, h4, h5]

theorem re_freeC (hp : p ≠ ∞) (ν r : ℝ) (F : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (freeC hp ν r F) = freeSemigroupLp hp ν r (reV.compLpL p volume F) :=
  re_cx _ F

theorem im_freeC (hp : p ≠ ∞) (ν r : ℝ) (F : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (freeC hp ν r F) = freeSemigroupLp hp ν r (imV.compLpL p volume F) :=
  im_cx _ F

/-- `S_ν(0) = I`. -/
theorem freeC_zero (hp : p ≠ ∞) (ν : ℝ) : freeC hp ν 0 = 1 := by
  rw [freeC, freeSemigroupLp_zero, cx_id]

/-- The semigroup law `S_ν(r₁ + r₂) = S_ν(r₁) S_ν(r₂)`, `r₁, r₂ ≥ 0`, `ν ≥ 0`. -/
theorem freeC_add (hp : p ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hr₂ : 0 ≤ r₂) : freeC hp ν (r₁ + r₂) = (freeC hp ν r₁).comp (freeC hp ν r₂) := by
  rw [freeC, freeSemigroupLp_add hp hν hr₁ hr₂, cx_comp]
  rfl

/-- Strong continuity on `[0, ∞)` ("It is strongly continuous", tex 7427). -/
theorem continuousOn_freeC (hp : p ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν)
    (F : Lp CVec3 p (volume : Measure Space)) :
    ContinuousOn (fun r => freeC hp ν r F) (Ici 0) := by
  have h1 := continuousOn_freeSemigroupLp hp hν (reV.compLpL p volume F)
  have h2 := continuousOn_freeSemigroupLp hp hν (imV.compLpL p volume F)
  exact ((ofReV.compLpL p (volume : Measure Space)).continuous.comp_continuousOn h1).add
    ((ofImV.compLpL p (volume : Measure Space)).continuous.comp_continuousOn h2)

/-- `‖S_ν(r)‖_{L^p(ℂ³) → L^p(ℂ³)} ≤ 2 e^{-γ_p r}` (from `eq:free-stress-8`, B0419). -/
theorem norm_freeC_le (hp : p ≠ ∞) (ν r : ℝ) :
    ‖freeC hp ν r‖ ≤ 2 * Real.exp (-gammaExp p * r) :=
  (norm_cx_le _).trans (by gcongr; exact norm_freeSemigroupLp_le hp ν r)

/-- At `q = 2`: `‖S_ν(r)‖_{L²(ℂ³) → L²(ℂ³)} ≤ e^{-γ_2 r} = e^{-r/4}`. -/
theorem norm_freeC_two_le (ν r : ℝ) :
    ‖freeC (p := 2) ENNReal.ofNat_ne_top ν r‖ ≤ Real.exp (-gammaExp 2 * r) :=
  (norm_cx_two_le _).trans (norm_freeSemigroupLp_le _ ν r)

end UnforcedLeray.B0421
