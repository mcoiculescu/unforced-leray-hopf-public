import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2_1

/-!
# Real-to-complex weak derivative bridge (`WeakDerBridge`)

Source `the November 2 reference manuscript` lines 1351-1362.
A complex test `θ` splits as `reV θ + I * imLc θ` with both parts real vector tests; a real field
`f` kills the imaginary part of the pairing, so the real weak-derivative identity for `G` gives the
complex one for `embR G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Imaginary part of a `ℂ³`-field, as a continuous linear map to `ℝ³`. -/
def imLc : CVec3 →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => (x i).im
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

theorem reV_contDiff' {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (reV θ) := by
  rw [reV_eq]
  exact D2SliceRe.reL.contDiff.comp hθ

theorem reV_compact' {θ : Space → CVec3} (hθ : HasCompactSupport θ) :
    HasCompactSupport (reV θ) := by
  rw [reV_eq]
  exact HasCompactSupport.comp_left (g := ⇑D2SliceRe.reL) hθ (map_zero D2SliceRe.reL)

theorem imLc_compact' {θ : Space → CVec3} (hθ : HasCompactSupport θ) :
    HasCompactSupport (fun y => imLc (θ y)) :=
  HasCompactSupport.comp_left (g := ⇑imLc) hθ (map_zero imLc)

theorem memLp_of_vTest' {φ : Space → Space} (hφ : UnforcedLeray.Blueprint.IsVectorTest φ) :
    MemLp φ 2 volume :=
  hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact

/-- Coordinates commute with the derivative. -/
theorem fderiv_coord' (u : Space → Space) (y : Space) (hu : DifferentiableAt ℝ u y) (i : Fin 3)
    (v : Space) : fderiv ℝ (fun z => u z i) y v = fderiv ℝ u y v i := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i : Space →L[ℝ] ℝ).hasFDerivAt (x := u y)).comp y
    hu.hasFDerivAt
  rw [show (fun z => u z i) = (EuclideanSpace.proj (𝕜 := ℝ) i : Space →L[ℝ] ℝ) ∘ u from rfl,
    h.fderiv]
  rfl

/-- Real and imaginary parts of a complex derivative. -/
theorem fderiv_re_im' (g : Space → ℂ) (x : Space) (hg : DifferentiableAt ℝ g x) (v : Space) :
    fderiv ℝ g x v = ((fderiv ℝ (fun z => (g z).re) x v : ℝ) : ℂ)
      + Complex.I * ((fderiv ℝ (fun z => (g z).im) x v : ℝ) : ℂ) := by
  have h1 : fderiv ℝ (fun z => (g z).re) x v = (fderiv ℝ g x v).re := by
    rw [show (fun z => (g z).re) = Complex.reCLM ∘ g from rfl,
      (Complex.reCLM.hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
    rfl
  have h2 : fderiv ℝ (fun z => (g z).im) x v = (fderiv ℝ g x v).im := by
    rw [show (fun z => (g z).im) = Complex.imCLM ∘ g from rfl,
      (Complex.imCLM.hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
    rfl
  rw [h1, h2]
  conv_lhs => rw [← Complex.re_add_im (fderiv ℝ g x v)]
  ring

theorem inner_sum_apply' (x u : Space) : inner ℝ x u = ∑ i : Fin 3, x i * u i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem integrable_inner_L2' (u v : Space → Space) (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) : Integrable (fun y => inner ℝ (u y) (v y)) volume :=
  by
  refine (hu.norm.integrable_mul hv.norm).mono' (hu.1.inner hv.1)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

theorem weakDerBridge : WeakDerBridge := by
  intro f G j hf mf mG hyp
  unfold WeakDer
  intro θ hθ hcθ
  have hci : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => θ z i) := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).contDiff.comp hθ
  have hdθ : ∀ i : Fin 3, ∀ y : Space, DifferentiableAt ℝ (fun z => θ z i) y := fun i y =>
    (hci i).differentiable (by simp) y
  have ha : UnforcedLeray.Blueprint.IsVectorTest (reV θ) :=
    ⟨reV_contDiff' hθ, reV_compact' hcθ⟩
  have hb : UnforcedLeray.Blueprint.IsVectorTest (fun y => imLc (θ y)) :=
    ⟨imLc.contDiff.comp hθ, imLc_compact' hcθ⟩
  have hA := UnforcedLeray.Blueprint.ModeId.isVectorTest_testPartial ha j
  have hB := UnforcedLeray.Blueprint.ModeId.isVectorTest_testPartial hb j
  have iPa : Integrable (fun y => inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (reV θ) j y)) :=
    integrable_inner_L2' _ _ (memLp_reV mf) (memLp_of_vTest' hA)
  have iPb : Integrable (fun y => inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (fun z => imLc (θ z)) j y)) :=
    integrable_inner_L2' _ _ (memLp_reV mf) (memLp_of_vTest' hB)
  have iGa : Integrable (fun y => inner ℝ (G y) (reV θ y)) :=
    integrable_inner_L2' _ _ mG (memLp_of_vTest' ha)
  have iGb : Integrable (fun y => inner ℝ (G y) (imLc (θ y))) :=
    integrable_inner_L2' _ _ mG (memLp_of_vTest' hb)
  have hHa : -(∫ y, inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (reV θ) j y)) = ∫ y, inner ℝ (G y) (reV θ y) :=
    hyp (reV θ) ha
  have hHb : -(∫ y, inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (fun z => imLc (θ z)) j y))
        = ∫ y, inner ℝ (G y) (imLc (θ y)) :=
    hyp (fun z => imLc (θ z)) hb
  -- pointwise: the complex pairing splits into the real and imaginary parts
  have hT : ∀ y : Space,
      (∑ i : Fin 3, f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        = ((inner ℝ (reV f y) (UnforcedLeray.Blueprint.testPartial (reV θ) j y) : ℝ) : ℂ)
          + Complex.I * ((inner ℝ (reV f y)
              (UnforcedLeray.Blueprint.testPartial (fun z => imLc (θ z)) j y) : ℝ) : ℂ) := by
    intro y
    have hfr : ∀ i, f y i = (((f y i).re : ℝ) : ℂ) := fun i =>
      Complex.ext (by simp) (by simpa using hf y i)
    have hsplit : ∀ i : Fin 3, fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))
        = ((fderiv ℝ (reV θ) y (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ)
          + Complex.I * ((fderiv ℝ (fun z => imLc (θ z)) y
              (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) := by
      intro i
      have h := fderiv_re_im' (fun z => θ z i) y (hdθ i y) (EuclideanSpace.single j (1 : ℝ))
      dsimp only at h
      have hre : fderiv ℝ (fun z => (θ z i).re) y (EuclideanSpace.single j (1 : ℝ))
          = fderiv ℝ (reV θ) y (EuclideanSpace.single j (1 : ℝ)) i :=
        fderiv_coord' (reV θ) y (ha.smooth.differentiable (by simp) y) i _
      have him : fderiv ℝ (fun z => (θ z i).im) y (EuclideanSpace.single j (1 : ℝ))
          = fderiv ℝ (fun z => imLc (θ z)) y (EuclideanSpace.single j (1 : ℝ)) i :=
        fderiv_coord' (fun z => imLc (θ z)) y (hb.smooth.differentiable (by simp) y) i _
      rw [hre, him] at h
      exact h
    have step : ∀ i : Fin 3, f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))
        = ((((f y i).re * fderiv ℝ (reV θ) y (EuclideanSpace.single j (1 : ℝ)) i : ℝ)) : ℂ)
          + Complex.I * ((((f y i).re * fderiv ℝ (fun z => imLc (θ z)) y
              (EuclideanSpace.single j (1 : ℝ)) i : ℝ)) : ℂ) := by
      intro i
      rw [hsplit i]
      conv_lhs => rw [hfr i]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Complex.ofReal_sum, ← Complex.ofReal_sum]
    rw [inner_sum_apply' (reV f y), inner_sum_apply' (reV f y)]
    rfl
  -- pointwise: the complex right-hand side splits likewise
  have hR : ∀ y : Space, (∑ i : Fin 3, embR G y i * θ y i)
      = ((inner ℝ (G y) (reV θ y) : ℝ) : ℂ)
        + Complex.I * ((inner ℝ (G y) (imLc (θ y)) : ℝ) : ℂ) := by
    intro y
    have hpt : ∀ i : Fin 3, embR G y i * θ y i
        = ((G y i * reV θ y i : ℝ) : ℂ) + Complex.I * ((G y i * imLc (θ y) i : ℝ) : ℂ) := by
      intro i
      have e1 : reV θ y i = (θ y i).re := rfl
      have e2 : imLc (θ y) i = (θ y i).im := rfl
      have e3 : embR G y i = ((G y i : ℝ) : ℂ) := rfl
      rw [e1, e2, e3]
      conv_lhs => rw [← Complex.re_add_im (θ y i)]
      push_cast
      ring
    rw [inner_sum_apply' (G y) (reV θ y), inner_sum_apply' (G y) (imLc (θ y))]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Complex.ofReal_sum, ← Complex.ofReal_sum]
  have hHa' : -((∫ y, inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (reV θ) j y) : ℝ) : ℂ)
        = ((∫ y, inner ℝ (G y) (reV θ y) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, hHa]
  have hHb' : -((∫ y, inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (fun z => imLc (θ z)) j y) : ℝ) : ℂ)
        = ((∫ y, inner ℝ (G y) (imLc (θ y)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, hHb]
  have cPa : Integrable (fun y => ((inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (reV θ) j y) : ℝ) : ℂ)) := iPa.ofReal
  have cPb : Integrable (fun y => ((inner ℝ (reV f y)
      (UnforcedLeray.Blueprint.testPartial (fun z => imLc (θ z)) j y) : ℝ) : ℂ)) := iPb.ofReal
  have cGa : Integrable (fun y => ((inner ℝ (G y) (reV θ y) : ℝ) : ℂ)) := iGa.ofReal
  have cGb : Integrable (fun y => ((inner ℝ (G y) (imLc (θ y)) : ℝ) : ℂ)) := iGb.ofReal
  simp_rw [hT, hR]
  rw [integral_add cPa (cPb.const_mul Complex.I),
    integral_add cGa (cGb.const_mul Complex.I),
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]
  linear_combination hHa' + Complex.I * hHb'

end UnforcedLeray.Short.PartIIIb.Concrete
