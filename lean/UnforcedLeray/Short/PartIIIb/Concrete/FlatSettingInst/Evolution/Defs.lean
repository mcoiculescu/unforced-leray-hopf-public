import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting
import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon

/-!
# The actual train evolution on `X_{m,c}`: reflection and complexification
(source 2819-2836, 4349-4352, 287-288)

Source of record: `the November 2 reference manuscript` (73 pages).

The full evolution `U(s,t)` of the source (2819-2836) is built in Lean by the Volterra iteration
`Exist.horizonEvolution` (`Short/PartIII-a/Sub/T21_3_Horizon.lean`) on the *real* zero-circulation
state space `ActualVorticity hm` (`Cons/.../MixedEvolution/Volterra.lean`).  The pinned operator
`TrainEvolution.U` of the flat setting acts on the complex, centrally even, zero-circulation space
`X_{m,c}` (`Xmc c m`, source 4349-4352).  This file defines the two bridges:

* the reflection `x ↦ -x`: `reflR` on the real weighted space, `reflV` on the state space (zero
  circulation is preserved), `reflF` on fluxes (`F ↦ -F(-·)`, a vector field changes sign).  The
  actual train is odd, `v(-q,-η,s) = -v(q,η,s)` (source 287-288), so its vorticity is even
  (`ec_even`) and the linearised equation commutes with these reflections;
* the complexification: `ofR` (real functions as complex ones), `reA`, `imA` (real and imaginary
  parts), `reV`, `imV : X_{m,c} → ActualVorticity` (an element of `X_{m,c}` has zero circulation, so
  do its real and imaginary parts), and `cx A hA : X_{m,c} →L[ℂ] X_{m,c}`,
  `cx A x = A(Re x) + i A(Im x)`, for a real operator `A` commuting with the reflection (this
  keeps central evenness, source 4349-4350).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution (ActualVorticity ActualFlux
  zeroCirculationSubmodule mem_zeroCirculationSubmodule_iff)
open UnforcedLeray.Short.IIIa.Exist (vortFn fluxFn cplx stripVel)

/-! ## 1. Reflection -/

section Refl

variable {c m : ℝ}

/-- The reflection `f ↦ f(-·)` of the real weighted space `B0579.X c m` (the weight is even and
the cell is symmetric up to a null set, `mp_neg_cellMeasure`). -/
def reflR (c m : ℝ) : B0579.X c m →ₗᵢ[ℝ] B0579.X c m :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ × ℝ => -x) (mp_neg_cellMeasure c m)

theorem coeFn_reflR (f : B0579.X c m) :
    (reflR c m f : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (mp_neg_cellMeasure c m)

theorem reflR_reflR (f : B0579.X c m) : reflR c m (reflR c m f) = f := by
  refine Lp.ext ?_
  have h1 := coeFn_reflR (reflR c m f)
  have h2 := (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae (coeFn_reflR f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, neg_neg]

/-- `∫_cell g(-x) dx = ∫_cell g(x) dx`. -/
theorem integral_cell_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ × ℝ → E) : ∫ x in B0579.cell c, g (-x) = ∫ x in B0579.cell c, g x :=
  (mp_neg_cell c).integral_comp' (f := MeasurableEquiv.neg (ℝ × ℝ)) g

variable [Fact (0 < c)] (hm : 1 ≤ m)

theorem reflR_mem (w : ActualVorticity (c := c) (m := m) hm) :
    reflR c m w.1 ∈ ActualVorticity (c := c) (m := m) hm := by
  refine (mem_zeroCirculationSubmodule_iff (by linarith) _).2 ?_
  have h0 : ∫ x in B0579.cell c, (w.1 : ℝ × ℝ → ℝ) x = 0 :=
    (mem_zeroCirculationSubmodule_iff (by linarith) w.1).1 w.2
  calc ∫ x in B0579.cell c, (reflR c m w.1 : ℝ × ℝ → ℝ) x
      = ∫ x in B0579.cell c, (w.1 : ℝ × ℝ → ℝ) (-x) :=
        integral_congr_ae (ae_cell_of_ae_cellMeasure (coeFn_reflR w.1))
    _ = ∫ x in B0579.cell c, (w.1 : ℝ × ℝ → ℝ) x := integral_cell_comp_neg _
    _ = 0 := h0

/-- **The reflection of the actual state space** `ω ↦ ω(-·)` (zero circulation is preserved). -/
def reflV : ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualVorticity (c := c) (m := m) hm :=
  ((reflR c m).toContinuousLinearMap.comp
    (ActualVorticity (c := c) (m := m) hm).subtypeL).codRestrict _ (fun w => reflR_mem hm w)

theorem reflV_val (w : ActualVorticity (c := c) (m := m) hm) :
    ((reflV hm w : ActualVorticity (c := c) (m := m) hm) : B0579.X c m) = reflR c m w.1 := rfl

theorem reflV_reflV (w : ActualVorticity (c := c) (m := m) hm) : reflV hm (reflV hm w) = w :=
  Subtype.ext (reflR_reflR w.1)

theorem vortFn_reflV (w : ActualVorticity (c := c) (m := m) hm) :
    vortFn hm (reflV hm w) =ᵐ[volume.restrict (B0579.cell c)] fun x => vortFn hm w (-x) :=
  ae_cell_of_ae_cellMeasure (coeFn_reflR w.1)

/-- **The reflection of fluxes** `F ↦ -F(-·)` (componentwise; the flux `vω + E K_cω` of an even
vorticity is an odd vector field). -/
def reflF : ActualFlux (c := c) (m := m) →L[ℝ] ActualFlux (c := c) (m := m) :=
  ContinuousLinearMap.pi fun i =>
    -((reflR c m).toContinuousLinearMap.comp (ContinuousLinearMap.proj i))

theorem reflF_apply (F : ActualFlux (c := c) (m := m)) (i : Fin 2) :
    reflF F i = -(reflR c m (F i)) := rfl

theorem fluxFn_reflF (F : ActualFlux (c := c) (m := m)) (i : Fin 2) :
    fluxFn (reflF F) i =ᵐ[volume.restrict (B0579.cell c)] fun x => -fluxFn F i (-x) := by
  have h1 : ((reflF F i : B0579.X c m) : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m]
      fun x => -(reflR c m (F i) : ℝ × ℝ → ℝ) x := by
    rw [reflF_apply]
    exact Lp.coeFn_neg _
  filter_upwards [ae_cell_of_ae_cellMeasure h1,
    ae_cell_of_ae_cellMeasure (coeFn_reflR (F i))] with x hx1 hx2
  change ((reflF F i : B0579.X c m) : ℝ × ℝ → ℝ) x = -((F i : B0579.X c m) : ℝ × ℝ → ℝ) (-x)
  rw [hx1, hx2]

end Refl

/-- **The vorticity of the actual train is even** (source 287-288: "Uniqueness gives
`v(-q,-η,s) = -v(q,η,s)`"; `B0140.IsTrain.odd`): `E(s,-x) = E(s,x)` for `s ≥ 0`, `E = curl v`. -/
theorem ec_even {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (x : ℝ × ℝ) : UnforcedLeray.B0238.Ec tr r (-x) = UnforcedLeray.B0238.Ec tr r x := by
  have hodd : ∀ z : ℝ × ℝ, ∀ i, tr.v r (-z) i = -tr.v r z i := fun z i => by
    rw [tr.isTrain.odd r hr z]
    rfl
  have h1 : (fun q : ℝ => tr.v r (q, (-x).2) 1) = fun q => -tr.v r (-q, x.2) 1 := by
    funext q
    rw [← hodd]
    simp
  have h2 : (fun η : ℝ => tr.v r ((-x).1, η) 0) = fun η => -tr.v r (x.1, -η) 0 := by
    funext η
    rw [← hodd]
    simp
  simp only [UnforcedLeray.B0238.Ec, UnforcedLeray.Cyl.curl, UnforcedLeray.Cyl.partialQ,
    UnforcedLeray.Cyl.partialEta]
  rw [h1, h2]
  have e1 : deriv (fun q : ℝ => -tr.v r (-q, x.2) 1) (-x).1 =
      deriv (fun q : ℝ => tr.v r (q, x.2) 1) x.1 := by
    rw [show (fun q : ℝ => -tr.v r (-q, x.2) 1) = -(fun q : ℝ => tr.v r (-q, x.2) 1) from rfl,
      deriv.neg, deriv_comp_neg (f := fun q : ℝ => tr.v r (q, x.2) 1)]
    simp
  have e2 : deriv (fun η : ℝ => -tr.v r (x.1, -η) 0) (-x).2 =
      deriv (fun η : ℝ => tr.v r (x.1, η) 0) x.2 := by
    rw [show (fun η : ℝ => -tr.v r (x.1, -η) 0) = -(fun η : ℝ => tr.v r (x.1, -η) 0) from rfl,
      deriv.neg, deriv_comp_neg (f := fun η : ℝ => tr.v r (x.1, η) 0)]
    simp
  rw [e1, e2]

/-! ## 2. Complexification -/

section Cx

variable {c m : ℝ}

/-- Real functions as complex functions, `L²(cell, ⟨x⟩^{2m}dx; ℝ) → X_amb`. -/
def ofR : B0579.X c m →L[ℝ] XAmb c m :=
  Complex.ofRealCLM.compLpL 2 (B0579.cellMeasure c m)

/-- The real part `X_amb → L²(cell, ⟨x⟩^{2m}dx; ℝ)`. -/
def reA : XAmb c m →L[ℝ] B0579.X c m :=
  Complex.reCLM.compLpL 2 (B0579.cellMeasure c m)

/-- The imaginary part `X_amb → L²(cell, ⟨x⟩^{2m}dx; ℝ)`. -/
def imA : XAmb c m →L[ℝ] B0579.X c m :=
  Complex.imCLM.compLpL 2 (B0579.cellMeasure c m)

theorem coeFn_ofR (w : B0579.X c m) :
    (ofR w : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] fun x => ((w x : ℝ) : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c m) w]
    with x hx
  exact hx

theorem coeFn_reA (f : XAmb c m) :
    (reA f : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] fun x => (f x).re := by
  filter_upwards [Complex.reCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c m) f]
    with x hx
  exact hx

theorem coeFn_imA (f : XAmb c m) :
    (imA f : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] fun x => (f x).im := by
  filter_upwards [Complex.imCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c m) f]
    with x hx
  exact hx

theorem norm_ofR_le (w : B0579.X c m) : ‖ofR w‖ ≤ ‖w‖ := by
  refine ((ofR (c := c) (m := m)).le_opNorm w).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
  exact Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)

theorem norm_reA_le (f : XAmb c m) : ‖reA f‖ ≤ ‖f‖ := by
  refine ((reA (c := c) (m := m)).le_opNorm f).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
  exact Complex.reCLM.opNorm_le_bound zero_le_one (fun x => by
    simpa using Complex.abs_re_le_norm x)

theorem norm_imA_le (f : XAmb c m) : ‖imA f‖ ≤ ‖f‖ := by
  refine ((imA (c := c) (m := m)).le_opNorm f).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
  exact Complex.imCLM.opNorm_le_bound zero_le_one (fun x => by
    simpa using Complex.abs_im_le_norm x)

variable [hm1 : Fact (1 < m)]

theorem reA_circ (x : Xmc c m) :
    ∫ p in B0579.cell c, (reA (x : XAmb c m) : ℝ × ℝ → ℝ) p = 0 := by
  have h : ∫ p in B0579.cell c, (reA (x : XAmb c m) : ℝ × ℝ → ℝ) p =
      ∫ p in B0579.cell c, (xFn x p).re :=
    integral_congr_ae (ae_cell_of_ae_cellMeasure (coeFn_reA _))
  rw [h, IIIa.BSAux.integral_re' (xFn_integrableOn x), xFn_circ, Complex.zero_re]

theorem imA_circ (x : Xmc c m) :
    ∫ p in B0579.cell c, (imA (x : XAmb c m) : ℝ × ℝ → ℝ) p = 0 := by
  have h : ∫ p in B0579.cell c, (imA (x : XAmb c m) : ℝ × ℝ → ℝ) p =
      ∫ p in B0579.cell c, (xFn x p).im :=
    integral_congr_ae (ae_cell_of_ae_cellMeasure (coeFn_imA _))
  have h2 : ∫ p in B0579.cell c, (xFn x p).im = (∫ p in B0579.cell c, xFn x p).im :=
    integral_im (xFn_integrableOn x)
  rw [h, h2, xFn_circ, Complex.zero_im]

variable [Fact (0 < c)]

/-- `Re : X_{m,c} → ActualVorticity` (the real part of a zero-circulation field has zero
circulation). -/
def reV : Xmc c m →L[ℝ] ActualVorticity (c := c) (m := m) one_le_of_fact :=
  (reA.comp ((xmcSub c m).subtypeL.restrictScalars ℝ)).codRestrict _
    (fun x => (mem_zeroCirculationSubmodule_iff (by linarith [hm1.out]) _).2 (reA_circ x))

/-- `Im : X_{m,c} → ActualVorticity`. -/
def imV : Xmc c m →L[ℝ] ActualVorticity (c := c) (m := m) one_le_of_fact :=
  (imA.comp ((xmcSub c m).subtypeL.restrictScalars ℝ)).codRestrict _
    (fun x => (mem_zeroCirculationSubmodule_iff (by linarith [hm1.out]) _).2 (imA_circ x))

theorem reV_val (x : Xmc c m) :
    ((reV x : ActualVorticity (c := c) (m := m) one_le_of_fact) : B0579.X c m) =
      reA (x : XAmb c m) := rfl

theorem imV_val (x : Xmc c m) :
    ((imV x : ActualVorticity (c := c) (m := m) one_le_of_fact) : B0579.X c m) =
      imA (x : XAmb c m) := rfl

theorem vortFn_reV (x : Xmc c m) :
    vortFn one_le_of_fact (reV x) =ᵐ[volume.restrict (B0579.cell c)] fun p => (xFn x p).re :=
  ae_cell_of_ae_cellMeasure (coeFn_reA _)

theorem vortFn_imV (x : Xmc c m) :
    vortFn one_le_of_fact (imV x) =ᵐ[volume.restrict (B0579.cell c)] fun p => (xFn x p).im :=
  ae_cell_of_ae_cellMeasure (coeFn_imA _)

/-- **`x = Re x + i Im x`** a.e. on the cell. -/
theorem xFn_eq_reV_imV (x : Xmc c m) :
    xFn x =ᵐ[volume.restrict (B0579.cell c)] fun p =>
      cplx (vortFn one_le_of_fact (reV x)) p +
        Complex.I * cplx (vortFn one_le_of_fact (imV x)) p := by
  filter_upwards [vortFn_reV x, vortFn_imV x] with p h1 h2
  simp only [cplx, h1, h2]
  exact (Complex.re_add_im (xFn x p)).symm.trans (by ring)

theorem norm_reV_le (x : Xmc c m) : ‖reV x‖ ≤ ‖x‖ := norm_reA_le (x : XAmb c m)

theorem norm_imV_le (x : Xmc c m) : ‖imV x‖ ≤ ‖x‖ := norm_imA_le (x : XAmb c m)

local notation "AV" => ActualVorticity (c := c) (m := m) (one_le_of_fact (m := m))

/-- The real-linear complexification `x ↦ A(Re x) + i A(Im x)` into the ambient space. -/
def cxR (A : AV →L[ℝ] AV) : Xmc c m →L[ℝ] XAmb c m :=
  ofR.comp ((AV).subtypeL.comp (A.comp reV)) +
    Complex.I • ofR.comp ((AV).subtypeL.comp (A.comp imV))

theorem cxR_apply (A : AV →L[ℝ] AV) (x : Xmc c m) :
    cxR A x = ofR ((A (reV x) : AV) : B0579.X c m) +
      Complex.I • ofR ((A (imV x) : AV) : B0579.X c m) := rfl

theorem coeFn_cxR (A : AV →L[ℝ] AV) (x : Xmc c m) :
    (cxR A x : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] fun p =>
      (((A (reV x) : AV) : B0579.X c m) p : ℂ) +
        Complex.I * (((A (imV x) : AV) : B0579.X c m) p : ℂ) := by
  rw [cxR_apply]
  filter_upwards [Lp.coeFn_add (ofR ((A (reV x) : AV) : B0579.X c m))
      (Complex.I • ofR ((A (imV x) : AV) : B0579.X c m)),
    Lp.coeFn_smul Complex.I (ofR ((A (imV x) : AV) : B0579.X c m)),
    coeFn_ofR ((A (reV x) : AV) : B0579.X c m), coeFn_ofR ((A (imV x) : AV) : B0579.X c m)]
    with p h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

/-- The ambient reflection on real functions. -/
theorem reflX_ofR (w : B0579.X c m) : reflX c m (ofR w) = ofR (reflR c m w) := by
  refine Lp.ext ?_
  have e1 := coeFn_reflX (ofR w)
  have e2 := (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae (coeFn_ofR w)
  filter_upwards [e1, e2, coeFn_ofR (reflR c m w), coeFn_reflR w] with p h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem reflV_reV (x : Xmc c m) : reflV one_le_of_fact (reV x) = reV x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [reflV_val, reV_val]
  have hev : reflX c m (x : XAmb c m) = x := (mem_xmcSub.1 x.2).2
  have e1 := coeFn_reflR (reA (x : XAmb c m))
  have e2 := (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae (coeFn_reA (x : XAmb c m))
  have e3 := coeFn_reflX (x : XAmb c m)
  rw [hev] at e3
  filter_upwards [e1, e2, e3, coeFn_reA (x : XAmb c m)] with p h1 h2 h3 h4
  rw [h1, h2, h4, h3]

theorem reflV_imV (x : Xmc c m) : reflV one_le_of_fact (imV x) = imV x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [reflV_val, imV_val]
  have hev : reflX c m (x : XAmb c m) = x := (mem_xmcSub.1 x.2).2
  have e1 := coeFn_reflR (imA (x : XAmb c m))
  have e2 := (mp_neg_cellMeasure c m).quasiMeasurePreserving.ae (coeFn_imA (x : XAmb c m))
  have e3 := coeFn_reflX (x : XAmb c m)
  rw [hev] at e3
  filter_upwards [e1, e2, e3, coeFn_imA (x : XAmb c m)] with p h1 h2 h3 h4
  rw [h1, h2, h4, h3]

theorem circC_ofR (w : AV) : circC hm1.out (ofR (w : B0579.X c m)) = 0 := by
  rw [circC_apply]
  have h0 : ∫ x in B0579.cell c, (w.1 : ℝ × ℝ → ℝ) x = 0 :=
    (mem_zeroCirculationSubmodule_iff (by linarith [hm1.out]) w.1).1 w.2
  calc ∫ p in B0579.cell c, (ofR (w : B0579.X c m) : ℝ × ℝ → ℂ) p
      = ∫ p in B0579.cell c, (((w : B0579.X c m) p : ℝ) : ℂ) :=
        integral_congr_ae (ae_cell_of_ae_cellMeasure (coeFn_ofR _))
    _ = ((∫ p in B0579.cell c, (w : B0579.X c m) p : ℝ) : ℂ) := integral_complex_ofReal
    _ = 0 := by rw [h0, Complex.ofReal_zero]

theorem cxR_mem (A : AV →L[ℝ] AV) (hA : ∀ w, A (reflV one_le_of_fact w) = reflV one_le_of_fact (A w))
    (x : Xmc c m) : cxR A x ∈ xmcSub c m := by
  refine mem_xmcSub.2 ⟨?_, ?_⟩
  · have h := circC_ofR (A (reV x))
    have h' := circC_ofR (A (imV x))
    rw [← circC_apply hm1.out, cxR_apply, map_add, map_smul, h, h', smul_zero, add_zero]
  · rw [cxR_apply, map_add, map_smul, reflX_ofR, reflX_ofR]
    have e1 : reflR c m ((A (reV x) : AV) : B0579.X c m) = ((A (reV x) : AV) : B0579.X c m) := by
      rw [← reflV_val, ← hA, reflV_reV]
    have e2 : reflR c m ((A (imV x) : AV) : B0579.X c m) = ((A (imV x) : AV) : B0579.X c m) := by
      rw [← reflV_val, ← hA, reflV_imV]
    rw [e1, e2]

/-- `Re (i x) = -Im x`. -/
theorem reV_I_smul (x : Xmc c m) : reV (Complex.I • x) = -imV x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [reV_val, Submodule.coe_neg, imV_val, Submodule.coe_smul]
  filter_upwards [coeFn_reA (Complex.I • (x : XAmb c m)), Lp.coeFn_smul Complex.I (x : XAmb c m),
    Lp.coeFn_neg (imA (x : XAmb c m)), coeFn_imA (x : XAmb c m)] with p h1 h2 h3 h4
  rw [h1, h2, h3, Pi.neg_apply, h4, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re,
    Complex.I_im]
  ring

/-- `Im (i x) = Re x`. -/
theorem imV_I_smul (x : Xmc c m) : imV (Complex.I • x) = reV x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [imV_val, reV_val, Submodule.coe_smul]
  filter_upwards [coeFn_imA (Complex.I • (x : XAmb c m)), Lp.coeFn_smul Complex.I (x : XAmb c m),
    coeFn_reA (x : XAmb c m)] with p h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem cxR_I_smul (A : AV →L[ℝ] AV) (x : Xmc c m) :
    cxR A (Complex.I • x) = Complex.I • cxR A x := by
  rw [cxR_apply, cxR_apply, reV_I_smul, imV_I_smul, map_neg, Submodule.coe_neg, map_neg,
    smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

/-- `(r : ℂ) • y = r • y` in a complex space with a compatible real action. -/
theorem ofReal_smul_eq {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (y : E) : ((r : ℂ)) • y = r • y := by
  rw [← smul_one_smul ℂ r y, Complex.real_smul, mul_one]

/-- `z • y = (Re z) • y + (Im z) • (i y)`. -/
theorem smul_eq_re_im {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (z : ℂ) (y : E) :
    z • y = z.re • y + z.im • (Complex.I • y) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, ofReal_smul_eq, ofReal_smul_eq]

theorem cxR_smul (A : AV →L[ℝ] AV) (z : ℂ) (x : Xmc c m) : cxR A (z • x) = z • cxR A x := by
  rw [smul_eq_re_im z x, map_add, map_smul, map_smul, cxR_I_smul, ← smul_eq_re_im z (cxR A x)]

/-- **The complexification** `x ↦ A(Re x) + i A(Im x)` of a real operator on the actual state
space commuting with the reflection, as a complex-linear operator on `X_{m,c}`. -/
def cx (A : AV →L[ℝ] AV) (hA : ∀ w, A (reflV one_le_of_fact w) = reflV one_le_of_fact (A w)) :
    Xmc c m →L[ℂ] Xmc c m where
  toFun x := ⟨cxR A x, cxR_mem A hA x⟩
  map_add' x y := Subtype.ext (map_add (cxR A) x y)
  map_smul' z x := Subtype.ext (cxR_smul A z x)
  cont := (cxR A).continuous.subtype_mk _

theorem cx_val (A : AV →L[ℝ] AV) (hA) (x : Xmc c m) : ((cx A hA x : Xmc c m) : XAmb c m) = cxR A x :=
  rfl

theorem cx_congr {A B : AV →L[ℝ] AV} (h : A = B) (hA) (hB) : cx A hA = cx B hB := by
  subst h
  rfl

/-- The planar function of `cx A x` is `A(Re x) + i A(Im x)`. -/
theorem xFn_cx (A : AV →L[ℝ] AV) (hA) (x : Xmc c m) :
    xFn (cx A hA x) =ᵐ[volume.restrict (B0579.cell c)] fun p =>
      cplx (vortFn one_le_of_fact (A (reV x))) p +
        Complex.I * cplx (vortFn one_le_of_fact (A (imV x))) p :=
  ae_cell_of_ae_cellMeasure (coeFn_cxR A x)

theorem reV_cx (A : AV →L[ℝ] AV) (hA) (x : Xmc c m) : reV (cx A hA x) = A (reV x) := by
  refine Subtype.ext (Lp.ext ?_)
  rw [reV_val, cx_val]
  filter_upwards [coeFn_reA (cxR A x), coeFn_cxR A x] with p h1 h2
  rw [h1, h2]
  simp

theorem imV_cx (A : AV →L[ℝ] AV) (hA) (x : Xmc c m) : imV (cx A hA x) = A (imV x) := by
  refine Subtype.ext (Lp.ext ?_)
  rw [imV_val, cx_val]
  filter_upwards [coeFn_imA (cxR A x), coeFn_cxR A x] with p h1 h2
  rw [h1, h2]
  simp

/-- `x = Re x + i Im x` in `X_{m,c}`. -/
theorem ofR_reV_add (x : Xmc c m) :
    ofR ((reV x : AV) : B0579.X c m) + Complex.I • ofR ((imV x : AV) : B0579.X c m) =
      (x : XAmb c m) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (ofR ((reV x : AV) : B0579.X c m))
      (Complex.I • ofR ((imV x : AV) : B0579.X c m)),
    Lp.coeFn_smul Complex.I (ofR ((imV x : AV) : B0579.X c m)),
    coeFn_ofR ((reV x : AV) : B0579.X c m), coeFn_ofR ((imV x : AV) : B0579.X c m),
    coeFn_reA (x : XAmb c m), coeFn_imA (x : XAmb c m)] with p h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, reV_val, imV_val, h5, h6, smul_eq_mul]
  exact (Complex.re_add_im _).symm.trans (by ring) |>.symm

theorem cx_id (hA) : cx (ContinuousLinearMap.id ℝ AV) hA = ContinuousLinearMap.id ℂ (Xmc c m) := by
  ext1 x
  exact Subtype.ext (ofR_reV_add x)

theorem cx_comp (A B : AV →L[ℝ] AV) (hA) (hB) (hAB) :
    (cx A hA).comp (cx B hB) = cx (A.comp B) hAB := by
  ext1 x
  refine Subtype.ext ?_
  rw [ContinuousLinearMap.comp_apply, cx_val, cx_val, cxR_apply, cxR_apply, reV_cx, imV_cx]
  rfl

/-- The cocycle law passes to the complexifications. -/
theorem cx_comp_eq (A B C : AV →L[ℝ] AV) (hA) (hB) (hC) (h : ∀ w, A (B w) = C w) :
    (cx A hA).comp (cx B hB) = cx C hC := by
  rw [cx_comp A B hA hB (fun w => by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hB, hA])]
  exact cx_congr (ContinuousLinearMap.ext h) _ _

theorem vortFn_neg (w : AV) :
    vortFn one_le_of_fact (-w) =ᵐ[volume.restrict (B0579.cell c)]
      fun p => -vortFn one_le_of_fact w p := by
  filter_upwards [ae_cell_of_ae_cellMeasure (Lp.coeFn_neg (w : B0579.X c m))] with p hp
  exact hp

theorem reV_conjX (x : Xmc c m) : reV (conjX x) = reV x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [reV_val, reV_val]
  filter_upwards [coeFn_reA (conjX x : XAmb c m), coeFn_reA (x : XAmb c m),
    coeFn_conjAmb (x : XAmb c m)] with p h1 h2 h3
  rw [h1, h2]
  change (conjAmb (x : XAmb c m) p).re = _
  rw [h3, Complex.conj_re]

theorem imV_conjX (x : Xmc c m) : imV (conjX x) = -imV x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [imV_val, Submodule.coe_neg, imV_val]
  filter_upwards [coeFn_imA (conjX x : XAmb c m), Lp.coeFn_neg (imA (x : XAmb c m)),
    coeFn_imA (x : XAmb c m), coeFn_conjAmb (x : XAmb c m)] with p h1 h2 h3 h4
  rw [h1, h2, Pi.neg_apply, h3]
  change (conjAmb (x : XAmb c m) p).im = _
  rw [h4, Complex.conj_im]

/-- **`cx A` has real coefficients**: it commutes with complex conjugation. -/
theorem conjX_cx (A : AV →L[ℝ] AV) (hA) (x : Xmc c m) : conjX (cx A hA x) = cx A hA (conjX x) := by
  refine xmc_ext ?_
  filter_upwards [xFn_conjX (cx A hA x), xFn_cx A hA x, xFn_cx A hA (conjX x),
    vortFn_neg (A (imV x))] with p h1 h2 h3 h4
  rw [h1, h2, h3, reV_conjX, imV_conjX, map_neg]
  simp only [cplx]
  rw [h4]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem norm_cx_apply_le (A : AV →L[ℝ] AV) (hA) (x : Xmc c m) :
    ‖cx A hA x‖ ≤ ‖A (reV x)‖ + ‖A (imV x)‖ := by
  change ‖cxR A x‖ ≤ _
  rw [cxR_apply]
  refine (norm_add_le _ _).trans (add_le_add (norm_ofR_le _) ?_)
  rw [norm_smul, Complex.norm_I, one_mul]
  exact norm_ofR_le _

/-- `‖cx A‖ ≤ 2‖A‖`. -/
theorem norm_cx_le (A : AV →L[ℝ] AV) (hA) : ‖cx A hA‖ ≤ 2 * ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine (norm_cx_apply_le A hA x).trans ?_
  have h1 := (A.le_opNorm (reV x)).trans (mul_le_mul_of_nonneg_left (norm_reV_le x) (norm_nonneg A))
  have h2 := (A.le_opNorm (imV x)).trans (mul_le_mul_of_nonneg_left (norm_imV_le x) (norm_nonneg A))
  linarith

/-- The difference of two complexifications at one point. -/
theorem norm_cx_sub_cx_le (A B : AV →L[ℝ] AV) (hA) (hB) (x : Xmc c m) :
    ‖cx A hA x - cx B hB x‖ ≤ ‖A (reV x) - B (reV x)‖ + ‖A (imV x) - B (imV x)‖ := by
  change ‖cxR A x - cxR B x‖ ≤ _
  rw [cxR_apply, cxR_apply]
  have e : ofR ((A (reV x) : AV) : B0579.X c m) + Complex.I • ofR ((A (imV x) : AV) : B0579.X c m) -
      (ofR ((B (reV x) : AV) : B0579.X c m) + Complex.I • ofR ((B (imV x) : AV) : B0579.X c m)) =
      ofR ((A (reV x) - B (reV x) : AV) : B0579.X c m) +
        Complex.I • ofR ((A (imV x) - B (imV x) : AV) : B0579.X c m) := by
    rw [Submodule.coe_sub, Submodule.coe_sub, map_sub, map_sub, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (norm_ofR_le _) ?_)
  rw [norm_smul, Complex.norm_I, one_mul]
  exact norm_ofR_le _

end Cx

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
