import UnforcedLeray.Lib.Cylinder.Seam

/-!
# Complex forms of the seam inequality and of transport antisymmetry (INF13, CY05)


§5 CY05: `re_weighted_laplacian_le_seam` and `transport_antisymm` with `Re ∫ … conj w …`, for
the complexified spaces of decision D11.  Both follow from the real forms in `Seam.lean`
applied to the real and imaginary parts.

`paper/main.tex` lines 4171-4184 (B0242) and 6494-6518 (B0343).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped ComplexConjugate

namespace UnforcedLeray.Cyl

/-! ### Partial derivatives of real and imaginary parts -/

theorem partialQ_re {g : Plane → ℂ} (hg : Differentiable ℝ g) (z : Plane) :
    partialQ (fun z => (g z).re) z = (partialQ g z).re := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.1 (hasDerivAt_sliceQ hg z.1 z.2)
  simp only [Complex.reCLM_apply, Prod.mk.eta] at h
  exact h.deriv

theorem partialQ_im {g : Plane → ℂ} (hg : Differentiable ℝ g) (z : Plane) :
    partialQ (fun z => (g z).im) z = (partialQ g z).im := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt z.1 (hasDerivAt_sliceQ hg z.1 z.2)
  simp only [Complex.imCLM_apply, Prod.mk.eta] at h
  exact h.deriv

theorem partialEta_re {g : Plane → ℂ} (hg : Differentiable ℝ g) (z : Plane) :
    partialEta (fun z => (g z).re) z = (partialEta g z).re := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.2 (hasDerivAt_sliceEta hg z.1 z.2)
  simp only [Complex.reCLM_apply, Prod.mk.eta] at h
  exact h.deriv

theorem partialEta_im {g : Plane → ℂ} (hg : Differentiable ℝ g) (z : Plane) :
    partialEta (fun z => (g z).im) z = (partialEta g z).im := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt z.2 (hasDerivAt_sliceEta hg z.1 z.2)
  simp only [Complex.imCLM_apply, Prod.mk.eta] at h
  exact h.deriv

theorem laplacian_re {g : Plane → ℂ} (hg : C2 g) (z : Plane) :
    laplacian (fun z => (g z).re) z = (laplacian g z).re := by
  have h1 : partialQ (fun z => (g z).re) = fun z => (partialQ g z).re :=
    funext (partialQ_re hg.diff)
  have h2 : partialEta (fun z => (g z).re) = fun z => (partialEta g z).re :=
    funext (partialEta_re hg.diff)
  rw [laplacian, laplacian, h1, h2, partialQ_re hg.diffQ, partialEta_re hg.diffEta,
    Complex.add_re]

theorem laplacian_im {g : Plane → ℂ} (hg : C2 g) (z : Plane) :
    laplacian (fun z => (g z).im) z = (laplacian g z).im := by
  have h1 : partialQ (fun z => (g z).im) = fun z => (partialQ g z).im :=
    funext (partialQ_im hg.diff)
  have h2 : partialEta (fun z => (g z).im) = fun z => (partialEta g z).im :=
    funext (partialEta_im hg.diff)
  rw [laplacian, laplacian, h1, h2, partialQ_im hg.diffQ, partialEta_im hg.diffEta,
    Complex.add_im]

theorem sq_norm_eq_re_im (x : ℂ) : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-! ### The complex seam inequality -/

/-- **The seam inequality, complex form** (CY05 `re_weighted_laplacian_le_seam`; B0242,
tex 4171-4184; B0343, tex 6494-6518).  For `m ≥ 0`, a `C²`, `c`-periodic `w : Plane → ℂ` with
compact support in `η`, and the centred weight `ρc^m` on the cell:
`2 Re ∫_cell Δw · conj w · ρc^m ≤ -2∫_cell |∇w|² ρc^m + ∫_cell |w|² Δ(ρc^m)`. -/
theorem re_weighted_laplacian_le_seam {c m R : ℝ} (hc : 0 < c) (hm : 0 ≤ m) {w : Plane → ℂ}
    (hw : ContDiff ℝ 2 w) (hper : IsPeriodic c w) (hR : VanishesOutside R w) :
    2 * (∫ z in cell c, laplacian w z * conj (w z) * ((ρc z ^ m : ℝ) : ℂ)).re ≤
      -2 * (∫ z in cell c, (‖partialQ w z‖ ^ 2 + ‖partialEta w z‖ ^ 2) * ρc z ^ m)
        + ∫ z in cell c, ‖w z‖ ^ 2 * laplacian (fun z => ρc z ^ m) z := by
  set a : Plane → ℝ := fun z => (w z).re
  set b : Plane → ℝ := fun z => (w z).im
  have hw2 := C2.of_contDiff hw
  have ha : ContDiff ℝ 2 a := Complex.reCLM.contDiff.comp hw
  have hb : ContDiff ℝ 2 b := Complex.imCLM.contDiff.comp hw
  have ha2 := C2.of_contDiff ha
  have hb2 := C2.of_contDiff hb
  have hap : IsPeriodic c a := hper.fun_comp Complex.re
  have hbp : IsPeriodic c b := hper.fun_comp Complex.im
  have haR : VanishesOutside R a := fun z hz => by simp [a, hR z hz]
  have hbR : VanishesOutside R b := fun z hz => by simp [b, hR z hz]
  have Ha := weighted_laplacian_le_seam hc hm ha hap haR
  have Hb := weighted_laplacian_le_seam hc hm hb hbp hbR
  have hp2 : C2 (fun z => ρc z ^ m) := C2.of_contDiff (contDiff_rpow_ρc m)
  -- continuity facts
  have c0 := hw2.cont; have c3 := hw2.contQQ; have c4 := hw2.contEtaEta
  have ca0 := ha2.cont; have ca1 := ha2.contQ; have ca2 := ha2.contEta
  have ca3 := ha2.contQQ; have ca4 := ha2.contEtaEta
  have cb0 := hb2.cont; have cb1 := hb2.contQ; have cb2 := hb2.contEta
  have cb3 := hb2.contQQ; have cb4 := hb2.contEtaEta
  have d0 := hp2.cont; have d3 := hp2.contQQ; have d4 := hp2.contEtaEta
  have cρ : Continuous fun z => ρc z ^ m := continuous_rpow_ρc m
  have haRq := haR.partialQ; have haRη := haR.partialEta
  have hbRq := hbR.partialQ; have hbRη := hbR.partialEta
  -- the left side
  have iL : IntegrableOn (fun z => laplacian w z * conj (w z) * ((ρc z ^ m : ℝ) : ℂ)) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz])
      (by simp only [laplacian]; fun_prop) c
  have iLa : IntegrableOn (fun z => laplacian a z * a z * ρc z ^ m) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [haR z hz])
      (by simp only [laplacian]; fun_prop) c
  have iLb : IntegrableOn (fun z => laplacian b z * b z * ρc z ^ m) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hbR z hz])
      (by simp only [laplacian]; fun_prop) c
  have eL : (∫ z in cell c, laplacian w z * conj (w z) * ((ρc z ^ m : ℝ) : ℂ)).re =
      (∫ z in cell c, laplacian a z * a z * ρc z ^ m) +
        ∫ z in cell c, laplacian b z * b z * ρc z ^ m := by
    have hre := Complex.reCLM.integral_comp_comm iL
    simp only [Complex.reCLM_apply] at hre
    rw [← hre, ← integral_add iLa iLb]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [laplacian_re hw2, laplacian_im hw2, a, b]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im]
    ring
  -- the gradient term
  have iGa : IntegrableOn (fun z => (partialQ a z ^ 2 + partialEta a z ^ 2) * ρc z ^ m)
      (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [haRq z hz, haRη z hz])
      (by fun_prop) c
  have iGb : IntegrableOn (fun z => (partialQ b z ^ 2 + partialEta b z ^ 2) * ρc z ^ m)
      (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hbRq z hz, hbRη z hz])
      (by fun_prop) c
  have eG : ∫ z in cell c, (‖partialQ w z‖ ^ 2 + ‖partialEta w z‖ ^ 2) * ρc z ^ m =
      (∫ z in cell c, (partialQ a z ^ 2 + partialEta a z ^ 2) * ρc z ^ m) +
        ∫ z in cell c, (partialQ b z ^ 2 + partialEta b z ^ 2) * ρc z ^ m := by
    rw [← integral_add iGa iGb]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [a, b, partialQ_re hw2.diff, partialQ_im hw2.diff, partialEta_re hw2.diff,
      partialEta_im hw2.diff, sq_norm_eq_re_im]
    ring
  -- the weight term
  have iPa : IntegrableOn (fun z => a z ^ 2 * laplacian (fun z => ρc z ^ m) z) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [haR z hz])
      (by simp only [laplacian]; fun_prop) c
  have iPb : IntegrableOn (fun z => b z ^ 2 * laplacian (fun z => ρc z ^ m) z) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hbR z hz])
      (by simp only [laplacian]; fun_prop) c
  have eP : ∫ z in cell c, ‖w z‖ ^ 2 * laplacian (fun z => ρc z ^ m) z =
      (∫ z in cell c, a z ^ 2 * laplacian (fun z => ρc z ^ m) z) +
        ∫ z in cell c, b z ^ 2 * laplacian (fun z => ρc z ^ m) z := by
    rw [← integral_add iPa iPb]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [a, b, sq_norm_eq_re_im]
    ring
  rw [eL, eG, eP]
  linarith

/-! ### Complex transport antisymmetry -/

/-- **Transport antisymmetry, complex form** (CY05 `transport_antisymm`):
`Re ∫_cell (v·∇w) conj w ρ = -½ ∫_cell |w|² (v·∇ρ)`. -/
theorem re_transport_antisymm {c R : ℝ} (hc : 0 < c) {v : Plane → Vec2} {w : Plane → ℂ}
    {ρ : Plane → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) (hρ : ContDiff ℝ 1 ρ)
    (hvp : IsPeriodic c v) (hwp : IsPeriodic c w)
    (hρseam : ∀ η, ρ (-c / 2, η) = ρ (c / 2, η))
    (hdiv : ∀ z, divergence v z = 0) (hR : VanishesOutside R w) :
    (∫ z in cell c, ((v z 0 : ℂ) * partialQ w z + (v z 1 : ℂ) * partialEta w z) *
        conj (w z) * (ρ z : ℂ)).re =
      -(1 / 2) * ∫ z in cell c, ‖w z‖ ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z) := by
  set a : Plane → ℝ := fun z => (w z).re
  set b : Plane → ℝ := fun z => (w z).im
  have hwd := hw.differentiable one_ne_zero
  have ha : ContDiff ℝ 1 a := Complex.reCLM.contDiff.comp hw
  have hb : ContDiff ℝ 1 b := Complex.imCLM.contDiff.comp hw
  have haR : VanishesOutside R a := fun z hz => by simp [a, hR z hz]
  have hbR : VanishesOutside R b := fun z hz => by simp [b, hR z hz]
  have Ha := transport_antisymm hc hv ha hρ hvp (hwp.fun_comp Complex.re) hρseam hdiv haR
  have Hb := transport_antisymm hc hv hb hρ hvp (hwp.fun_comp Complex.im) hρseam hdiv hbR
  have hv0 : ContDiff ℝ 1 fun z => v z 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ).contDiff.comp hv
  have hv1 : ContDiff ℝ 1 fun z => v z 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ).contDiff.comp hv
  have cv0 := hv0.continuous; have cv1 := hv1.continuous
  have cw := hw.continuous; have cρ := hρ.continuous
  obtain ⟨cwq, cwη⟩ := C1_partial_of_contDiff hw
  obtain ⟨caq, caη⟩ := C1_partial_of_contDiff ha
  obtain ⟨cbq, cbη⟩ := C1_partial_of_contDiff hb
  obtain ⟨cρq, cρη⟩ := C1_partial_of_contDiff hρ
  have ca := ha.continuous; have cb := hb.continuous
  have iL : IntegrableOn (fun z => ((v z 0 : ℂ) * partialQ w z + (v z 1 : ℂ) * partialEta w z) *
      conj (w z) * (ρ z : ℂ)) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  have iLa : IntegrableOn (fun z => (v z 0 * partialQ a z + v z 1 * partialEta a z) * a z * ρ z)
      (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [haR z hz]) (by fun_prop) c
  have iLb : IntegrableOn (fun z => (v z 0 * partialQ b z + v z 1 * partialEta b z) * b z * ρ z)
      (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hbR z hz]) (by fun_prop) c
  have eL : (∫ z in cell c, ((v z 0 : ℂ) * partialQ w z + (v z 1 : ℂ) * partialEta w z) *
        conj (w z) * (ρ z : ℂ)).re =
      (∫ z in cell c, (v z 0 * partialQ a z + v z 1 * partialEta a z) * a z * ρ z) +
        ∫ z in cell c, (v z 0 * partialQ b z + v z 1 * partialEta b z) * b z * ρ z := by
    have hre := Complex.reCLM.integral_comp_comm iL
    simp only [Complex.reCLM_apply] at hre
    rw [← hre, ← integral_add iLa iLb]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [a, b, partialQ_re hwd, partialQ_im hwd, partialEta_re hwd, partialEta_im hwd]
    simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have iSa : IntegrableOn (fun z => a z ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z))
      (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [haR z hz]) (by fun_prop) c
  have iSb : IntegrableOn (fun z => b z ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z))
      (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hbR z hz]) (by fun_prop) c
  have eS : ∫ z in cell c, ‖w z‖ ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z) =
      (∫ z in cell c, a z ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z)) +
        ∫ z in cell c, b z ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z) := by
    rw [← integral_add iSa iSb]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [a, b, sq_norm_eq_re_im]
    ring
  rw [eL, eS, Ha, Hb]
  ring

end UnforcedLeray.Cyl
