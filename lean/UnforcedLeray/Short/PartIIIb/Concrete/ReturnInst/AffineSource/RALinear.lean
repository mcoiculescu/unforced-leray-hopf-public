import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefLinear
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_closure
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RALinear.PsiLin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RALinear.PhysLin

/-!
# `PartIII-b:C/asrc/ra/9`-leaf : `RALinear` (target `raLinear`)

Source of record: `the November 2 reference manuscript` line 4985 ("All these maps
depend linearly on `A`").  The coefficient `rAcoef = coefOf ε⁻¹ 𝔯_A` is additive and homogeneous in
`A ∈ 𝒜` at every chart point with `s > 0`, because:

* `hAcoef`, `FAcoef`, `EAcoef` are linear (`hhatCoefLinear`, `faCoefLinear`, `eaCoefLinear`), and
  vanish at `s ≤ 0` since `(√s)⁻¹ = 0`;
* `Ψ_A` is linear (`psiA_add_pt`, `psiA_smul_pt`, helper `PsiLin`);
* the physical operators `D_μ`, `div(a⊗b+b⊗a)`, `∇` are additive/homogeneous on the `C²`/`C¹`
  fields of `affineLiftReg` (helper `PhysLin`);
* `coefOf` is additive/homogeneous pointwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma ra_merOf_zero : merOf 0 = 0 := by
  ext i; fin_cases i <;> simp [merOf]

lemma ra_sqrt_inv_zero {s : ℝ} (h : s ≤ 0) : (Real.sqrt s)⁻¹ = 0 := by
  rw [Real.sqrt_eq_zero'.mpr h, inv_zero]

lemma ra_hAcoef_add_all (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν ε : ℝ) (hν : 0 < ν)
    (A A' : ℝ → Mat3) (hA : IsAffElem as A) (hA' : IsAffElem as A') (p : Chart) :
    hAcoef ν ε χf (A + A') p = hAcoef ν ε χf A p + hAcoef ν ε χf A' p := by
  by_cases h : 0 < p.1
  · exact ((hhatCoefLinear as χf hχ) ν ε hν A A' 0 hA hA' p h).1
  · have hs : p.1 ≤ 0 := le_of_not_gt h
    unfold hAcoef
    rw [ra_sqrt_inv_zero hs]
    simp [ra_merOf_zero]

lemma ra_hAcoef_smul_all (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν ε : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (r : ℝ) (p : Chart) :
    hAcoef ν ε χf (r • A) p = r • hAcoef ν ε χf A p := by
  by_cases h : 0 < p.1
  · exact ((hhatCoefLinear as χf hχ) ν ε hν A A r hA hA p h).2
  · have hs : p.1 ≤ 0 := le_of_not_gt h
    unfold hAcoef
    rw [ra_sqrt_inv_zero hs]
    simp [ra_merOf_zero]

lemma ra_FAcoef_add_all (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A A' : ℝ → Mat3) (hA : IsAffElem as A) (hA' : IsAffElem as A') (p : Chart) :
    FAcoef ν μ χf (A + A') p = FAcoef ν μ χf A p + FAcoef ν μ χf A' p := by
  by_cases h : 0 < p.1
  · exact ((faCoefLinear as χf hχ) ν μ hν A A' 0 hA hA' p h).1
  · have hs : p.1 ≤ 0 := le_of_not_gt h
    unfold FAcoef
    rw [ra_sqrt_inv_zero hs]
    simp [ra_merOf_zero]

lemma ra_FAcoef_smul_all (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (r : ℝ) (p : Chart) :
    FAcoef ν μ χf (r • A) p = r • FAcoef ν μ χf A p := by
  by_cases h : 0 < p.1
  · exact ((faCoefLinear as χf hχ) ν μ hν A A r hA hA p h).2
  · have hs : p.1 ≤ 0 := le_of_not_gt h
    unfold FAcoef
    rw [ra_sqrt_inv_zero hs]
    simp [ra_merOf_zero]

lemma ra_EAcoef_add_all (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A A' : ℝ → Mat3) (hA : IsAffElem as A) (hA' : IsAffElem as A') (p : Chart) :
    EAcoef ν μ χf (A + A') p = EAcoef ν μ χf A p + EAcoef ν μ χf A' p := by
  by_cases h : 0 < p.1
  · exact ((eaCoefLinear as χf hχ) ν μ hν A A' 0 hA hA' p h).1
  · have hs : p.1 ≤ 0 := le_of_not_gt h
    unfold EAcoef
    rw [ra_sqrt_inv_zero hs]
    simp [ra_merOf_zero]

lemma ra_EAcoef_smul_all (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (r : ℝ) (p : Chart) :
    EAcoef ν μ χf (r • A) p = r • EAcoef ν μ χf A p := by
  by_cases h : 0 < p.1
  · exact ((eaCoefLinear as χf hχ) ν μ hν A A r hA hA p h).2
  · have hs : p.1 ≤ 0 := le_of_not_gt h
    unfold EAcoef
    rw [ra_sqrt_inv_zero hs]
    simp [ra_merOf_zero]

/-! ## Lifts, `F_A + E_A` and `sΨ_A` -/

lemma ra_hLift_add (ν ε c : ℝ) (χf : ℝ → ℝ) (A A' : ℝ → Mat3)
    (h : ∀ p : Chart, hAcoef ν ε χf (A + A') p = hAcoef ν ε χf A p + hAcoef ν ε χf A' p)
    (τ : ℝ) (y : Space) :
    hLift ν ε c χf (A + A') τ y = hLift ν ε c χf A τ y + hLift ν ε c χf A' τ y := by
  unfold hLift
  have e : perExt c (hAcoef ν ε χf (A + A')) =
      perExt c (hAcoef ν ε χf A) + perExt c (hAcoef ν ε χf A') := by
    funext q
    unfold Axi.perExt
    exact h _
  rw [e, Nv_add]

lemma ra_hLift_smul (ν ε c : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (r : ℝ)
    (h : ∀ p : Chart, hAcoef ν ε χf (r • A) p = r • hAcoef ν ε χf A p) (τ : ℝ) (y : Space) :
    hLift ν ε c χf (r • A) τ y = r • hLift ν ε c χf A τ y := by
  unfold hLift
  have e : perExt c (hAcoef ν ε χf (r • A)) = r • perExt c (hAcoef ν ε χf A) := by
    funext q
    unfold Axi.perExt
    exact h _
  rw [e, Nv_smul]

lemma ra_feLift_add (ν μ ε c : ℝ) (χf : ℝ → ℝ) (A A' : ℝ → Mat3)
    (h : ∀ p : Chart, FAcoef ν μ χf (A + A') p + EAcoef ν μ χf (A + A') p =
      (FAcoef ν μ χf A p + EAcoef ν μ χf A p) + (FAcoef ν μ χf A' p + EAcoef ν μ χf A' p))
    (τ : ℝ) (y : Space) :
    feLift ν μ ε c χf (A + A') τ y = feLift ν μ ε c χf A τ y + feLift ν μ ε c χf A' τ y := by
  unfold feLift
  have e : perExt c (FAcoef ν μ χf (A + A') + EAcoef ν μ χf (A + A')) =
      perExt c (FAcoef ν μ χf A + EAcoef ν μ χf A) +
        perExt c (FAcoef ν μ χf A' + EAcoef ν μ χf A') := by
    funext q
    unfold Axi.perExt
    exact h _
  rw [e, Nv_add]

lemma ra_feLift_smul (ν μ ε c : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (r : ℝ)
    (h : ∀ p : Chart, FAcoef ν μ χf (r • A) p + EAcoef ν μ χf (r • A) p =
      r • (FAcoef ν μ χf A p + EAcoef ν μ χf A p))
    (τ : ℝ) (y : Space) :
    feLift ν μ ε c χf (r • A) τ y = r • feLift ν μ ε c χf A τ y := by
  unfold feLift
  have e : perExt c (FAcoef ν μ χf (r • A) + EAcoef ν μ χf (r • A)) =
      r • perExt c (FAcoef ν μ χf A + EAcoef ν μ χf A) := by
    funext q
    unfold Axi.perExt
    exact h _
  rw [e, Nv_smul]

/-- `sΨ_A` is additive in `A` at every chart point (source 5024, 5040-5043). -/
lemma ra_psiLift_add (ν ε : ℝ) (χf : ℝ → ℝ) (hν : 0 < ν) (A A' : ℝ → Mat3) (τ : ℝ) (y : Space) :
    psiLift ν ε χf (A + A') τ y = psiLift ν ε χf A τ y + psiLift ν ε χf A' τ y := by
  unfold psiLift sPsiPhys
  have hn : 0 ≤ (chart ε⁻¹ τ y).1 := by
    unfold chart
    exact UnforcedLeray.Axi.age_nonneg _ _
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · rw [psiA_add_pt ν χf A A' _ _ hν hpos]
    ring

/-- `sΨ_A` is homogeneous in `A`. -/
lemma ra_psiLift_smul (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (r : ℝ) (τ : ℝ) (y : Space) :
    psiLift ν ε χf (r • A) τ y = r * psiLift ν ε χf A τ y := by
  unfold psiLift sPsiPhys
  rw [psiA_smul_pt]
  ring

/-! ## Coefficients -/

lemma ra_coefOf_add (R : ℝ) (F G : ℝ → Space → Space) (p : Chart) :
    coefOf R (fun τ y => F τ y + G τ y) p = coefOf R F p + coefOf R G p := by
  unfold coefOf
  rw [← smul_add]
  congr 1
  ext i
  fin_cases i <;> simp

lemma ra_coefOf_smul (R r : ℝ) (F : ℝ → Space → Space) (p : Chart) :
    coefOf R (fun τ y => r • F τ y) p = r • coefOf R F p := by
  unfold coefOf
  ext i
  fin_cases i <;> simp <;> ring

/-! ## The linearity theorem -/

set_option maxHeartbeats 1000000 in
/-- Slices of a jointly `C²` field are `C²`-differentiable. -/
lemma ra_slice_diff2 {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 2 (fun x : ℝ × Space => f x.1 x.2)) (τ : ℝ) : Differentiable ℝ (f τ) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)

/-- Slices of a jointly `C¹` field are differentiable. -/
lemma ra_slice_diff1 {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun x : ℝ × Space => f x.1 x.2)) (τ : ℝ) : Differentiable ℝ (f τ) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)

/-- Slices of a jointly `C¹` scalar field are differentiable. -/
lemma ra_slice_diff1s {f : ℝ → Space → ℝ}
    (hf : ContDiff ℝ 1 (fun x : ℝ × Space => f x.1 x.2)) (τ : ℝ) : Differentiable ℝ (f τ) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)

/-- **`A ↦ 𝔯_A` is linear on `𝒜`** (source 4985): the target `raLinear`. -/
theorem raLinear (as : ℝ) (χf : ℝ → ℝ) : RALinear as χf := by
  intro hχ ν μ ε hν hε U hU A A' r hA hA' p hp
  have hcν : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  obtain ⟨hL, hPs, _⟩ := affineLiftReg as χf hχ ν μ ε hν hε A hA
  obtain ⟨hL', hPs', _⟩ := affineLiftReg as χf hχ ν μ ε hν hε A' hA'
  have hAA : IsAffElem as (A + A') := isAffElem_add_aux as A A' hA hA'
  have hrA : IsAffElem as (r • A) := isAffElem_smul_aux as r A hA
  -- differentiability of the slices
  have dL : ∀ τ, Differentiable ℝ (hLift ν ε (cOf ν) χf A τ) := fun τ =>
    ra_slice_diff2 (f := hLift ν ε (cOf ν) χf A) hL τ
  have dL' : ∀ τ, Differentiable ℝ (hLift ν ε (cOf ν) χf A' τ) := fun τ =>
    ra_slice_diff2 (f := hLift ν ε (cOf ν) χf A') hL' τ
  have dP : ∀ τ, Differentiable ℝ (psiLift ν ε χf A τ) := fun τ =>
    ra_slice_diff1s (f := psiLift ν ε χf A) hPs τ
  have dP' : ∀ τ, Differentiable ℝ (psiLift ν ε χf A' τ) := fun τ =>
    ra_slice_diff1s (f := psiLift ν ε χf A') hPs' τ
  have dU : ∀ τ, Differentiable ℝ (U τ) := fun τ => ra_slice_diff1 (f := U) hU τ
  -- pointwise linearity of the coefficients and lifts
  have hAdd : ∀ q : Chart, hAcoef ν ε χf (A + A') q = hAcoef ν ε χf A q + hAcoef ν ε χf A' q :=
    fun q => ra_hAcoef_add_all as χf hχ ν ε hν A A' hA hA' q
  have hSmul : ∀ q : Chart, hAcoef ν ε χf (r • A) q = r • hAcoef ν ε χf A q :=
    fun q => ra_hAcoef_smul_all as χf hχ ν ε hν A hA r q
  have hFEadd : ∀ q : Chart, FAcoef ν μ χf (A + A') q + EAcoef ν μ χf (A + A') q =
      (FAcoef ν μ χf A q + EAcoef ν μ χf A q) + (FAcoef ν μ χf A' q + EAcoef ν μ χf A' q) := by
    intro q
    rw [ra_FAcoef_add_all as χf hχ ν μ hν A A' hA hA' q,
      ra_EAcoef_add_all as χf hχ ν μ hν A A' hA hA' q]
    abel
  have hFEsmul : ∀ q : Chart, FAcoef ν μ χf (r • A) q + EAcoef ν μ χf (r • A) q =
      r • (FAcoef ν μ χf A q + EAcoef ν μ χf A q) := by
    intro q
    rw [ra_FAcoef_smul_all as χf hχ ν μ hν A hA r q,
      ra_EAcoef_smul_all as χf hχ ν μ hν A hA r q]
    module
  have hLadd : ∀ τ y, hLift ν ε (cOf ν) χf (A + A') τ y =
      hLift ν ε (cOf ν) χf A τ y + hLift ν ε (cOf ν) χf A' τ y :=
    fun τ y => ra_hLift_add ν ε (cOf ν) χf A A' hAdd τ y
  have hLsmul : ∀ τ y, hLift ν ε (cOf ν) χf (r • A) τ y = r • hLift ν ε (cOf ν) χf A τ y :=
    fun τ y => ra_hLift_smul ν ε (cOf ν) χf A r hSmul τ y
  have hFEadd' : ∀ τ y, feLift ν μ ε (cOf ν) χf (A + A') τ y =
      feLift ν μ ε (cOf ν) χf A τ y + feLift ν μ ε (cOf ν) χf A' τ y :=
    fun τ y => ra_feLift_add ν μ ε (cOf ν) χf A A' hFEadd τ y
  have hFEsmul' : ∀ τ y, feLift ν μ ε (cOf ν) χf (r • A) τ y = r • feLift ν μ ε (cOf ν) χf A τ y :=
    fun τ y => ra_feLift_smul ν μ ε (cOf ν) χf A r hFEsmul τ y
  have hPsadd : ∀ τ y, psiLift ν ε χf (A + A') τ y = psiLift ν ε χf A τ y + psiLift ν ε χf A' τ y :=
    fun τ y => ra_psiLift_add ν ε χf hν A A' τ y
  have hPssmul : ∀ τ y, psiLift ν ε χf (r • A) τ y = r * psiLift ν ε χf A τ y :=
    fun τ y => ra_psiLift_smul ν ε χf A r τ y
  -- the residual is additive and homogeneous in A pointwise
  have hRAadd : ∀ τ y, rAPhys ν μ ε (cOf ν) χf U (A + A') τ y =
      rAPhys ν μ ε (cOf ν) χf U A τ y + rAPhys ν μ ε (cOf ν) χf U A' τ y := by
    intro τ y
    have e2 : hLift ν ε (cOf ν) χf (A + A') τ = fun y => hLift ν ε (cOf ν) χf A τ y +
        hLift ν ε (cOf ν) χf A' τ y := funext fun y => hLadd τ y
    have e1 : hLift ν ε (cOf ν) χf (A + A') = fun t y => hLift ν ε (cOf ν) χf A t y +
        hLift ν ε (cOf ν) χf A' t y := funext fun t => funext fun y => hLadd t y
    have e3 : psiLift ν ε χf (A + A') τ = fun y => psiLift ν ε χf A τ y +
        psiLift ν ε χf A' τ y := funext fun y => hPsadd τ y
    unfold rAPhys
    rw [e2, e1, e3, ra_physDmu_add ν μ _ _ (hL) (hL') τ y,
      physDivSym_add (dU τ) (dL τ) (dL' τ) y, hFEadd' τ y,
      ra_physGrad_add _ _ (dP τ) (dP' τ) y]
    abel
  have hRAsmul : ∀ τ y, rAPhys ν μ ε (cOf ν) χf U (r • A) τ y =
      r • rAPhys ν μ ε (cOf ν) χf U A τ y := by
    intro τ y
    have e2 : hLift ν ε (cOf ν) χf (r • A) τ = fun y => r • hLift ν ε (cOf ν) χf A τ y :=
      funext fun y => hLsmul τ y
    have e1 : hLift ν ε (cOf ν) χf (r • A) = fun t y => r • hLift ν ε (cOf ν) χf A t y :=
      funext fun t => funext fun y => hLsmul t y
    have e3 : psiLift ν ε χf (r • A) τ = fun y => r * psiLift ν ε χf A τ y :=
      funext fun y => hPssmul τ y
    unfold rAPhys
    rw [e2, e1, e3, ra_physDmu_smul ν μ _ hL r τ y,
      ra_physDivSym_smul (U τ) (hLift ν ε (cOf ν) χf A τ) (dU τ) (dL τ) r y, hFEsmul' τ y,
      ra_physGrad_mul _ (dP τ) r y]
    module
  have hfAdd : rAPhys ν μ ε (cOf ν) χf U (A + A') =
      fun τ y => rAPhys ν μ ε (cOf ν) χf U A τ y + rAPhys ν μ ε (cOf ν) χf U A' τ y :=
    funext fun τ => funext fun y => hRAadd τ y
  have hfSmul : rAPhys ν μ ε (cOf ν) χf U (r • A) =
      fun τ y => r • rAPhys ν μ ε (cOf ν) χf U A τ y :=
    funext fun τ => funext fun y => hRAsmul τ y
  constructor
  · unfold rAcoef
    rw [hfAdd]
    exact ra_coefOf_add _ _ _ p
  · unfold rAcoef
    rw [hfSmul]
    exact ra_coefOf_smul _ r _ p

end UnforcedLeray.Short.PartIIIb.Concrete
