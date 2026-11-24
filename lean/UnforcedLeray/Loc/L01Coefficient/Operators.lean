import UnforcedLeray.Loc.L01Coefficient.Leibniz

/-!
# Step L1, helpers: the coefficient operators `f ↦ div(U ⊗ f + f ⊗ U)`

Support for `Loc/L01Coefficient.lean` (step L1, `paper/main.tex` lines 268–290,
`loc:eq:coefficient-maps`, blueprint units B0709, B0711).

A coefficient is a triple `c = (U, ∇U, ∇²U) ∈ L^∞ × (L³)³ × (L²)^{3×3}` (`Coef`). The
operators are bounded bilinear in `(c, f)`, built from Mathlib's Hölder maps
`ContinuousLinearMap.holderL`:
* `colX j c f` is the column `𝕋_{·j} = f_j U + U_j f` of `U ⊗ f + f ⊗ U` (line 271),
  in `L²` because `U ∈ L^∞`;
* `dcolX j k c f` is its `k`-th derivative `(∂ₖf)_j U + f_j ∂ₖU + (∂ₖU)_j f + U_j ∂ₖf`,
  in `L²` by `‖U‖_∞‖∇f‖₂ + ‖∇U‖₃‖f‖₆` (line 282, with the compiled `H¹ ⊂ L⁶`);
* `Gop c f = ∑ⱼ ∂ⱼ𝕋_{·j} = div(U ⊗ f + f ⊗ U)`;
* `GkOp k c g` is `∂ₖ div(U ⊗ g + g ⊗ U)` for `g ∈ Z = H²_div`, in `L²` by
  `‖∇²U‖₂‖g‖_∞ + ‖∇U‖₃‖∇g‖₆ + ‖U‖_∞‖∇²g‖₂` (lines 284–285; `‖g‖_∞` needs `H² ⊂ L^∞`, which
  enters as the parameter `E`).

When `c` is consistent (`∇U`, `∇²U` are the weak derivatives), the weak product rule
(`Leibniz.lean`) identifies `dcolX` and `GkOp` as genuine weak derivatives
(`colX_dcolX_mem`, `Gop_GkOp_mem`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L01

open SobolevGraph SobolevEmbedding

/-! ## Coefficients -/

/-- A coefficient `(U, ∇U, ∇²U) ∈ L^∞ × (L³)³ × (L²)^{3×3}`. -/
abbrev Coef := LinfSpace × (Fin 3 → L3Space) × (Fin 3 → Fin 3 → L2Space)

/-- `U`. -/
def πv : Coef →L[ℝ] LinfSpace := ContinuousLinearMap.fst ℝ _ _

/-- `∂ⱼU`. -/
def πw (j : Fin 3) : Coef →L[ℝ] L3Space :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

/-- `∂ₖ∂ⱼU`. -/
def πy (j k : Fin 3) : Coef →L[ℝ] L2Space :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => L2Space) k).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → L2Space) j).comp
      ((ContinuousLinearMap.snd ℝ (Fin 3 → L3Space) (Fin 3 → Fin 3 → L2Space)).comp
        (ContinuousLinearMap.snd ℝ LinfSpace _)))

@[simp] theorem πv_apply (c : Coef) : πv c = c.1 := rfl
@[simp] theorem πw_apply (j : Fin 3) (c : Coef) : πw j c = c.2.1 j := rfl
@[simp] theorem πy_apply (j k : Fin 3) (c : Coef) : πy j k c = c.2.2 j k := rfl

/-- `∇U` and `∇²U` are the weak derivatives of `U`. -/
structure IsConsistentCoef (c : Coef) : Prop where
  dv : ∀ k, HasWeakSpatialDerivative k (c.1 : SpatialField) (c.2.1 k : SpatialField)
  dw : ∀ j k, HasWeakSpatialDerivative k (c.2.1 j : SpatialField) (c.2.2 j k : SpatialField)

theorem locL2_Linf (v : LinfSpace) : LocL2 (v : SpatialField) := fun _ hφ =>
  test_smul_memLp (s := 2) hφ (Lp.memLp v)

theorem locL2_L3 (w : L3Space) : LocL2 (w : SpatialField) := fun _ hφ =>
  test_smul_memLp (s := 6) hφ (Lp.memLp w)

theorem locL2_L2 (y : L2Space) : LocL2 (y : SpatialField) := fun _ hφ =>
  test_smul_memLp (s := ∞) hφ (Lp.memLp y)

/-! ## The column product `P_j(u, v) = u_j v` -/

/-- `P_j(u, v) = u_j v`: column `j` of `v ⊗ u` is `P_j(u, v)`. -/
def prodJ (j : Fin 3) : Space →L[ℝ] Space →L[ℝ] Space :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (EuclideanSpace.proj j : Space →L[ℝ] ℝ)

@[simp] theorem prodJ_apply (j : Fin 3) (u v : Space) : prodJ j u v = u j • v := rfl

/-- The Hölder product `L^p × L^q → L²` of `P_j`. -/
def hol (j : Fin 3) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple p q 2] :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space q (volume : Measure Space) →L[ℝ]
      L2Space :=
  (prodJ j).holderL (volume : Measure Space) p q 2

theorem coeFn_hol (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 2] (f : Lp Space p (volume : Measure Space))
    (g : Lp Space q (volume : Measure Space)) :
    (hol j p q f g : SpatialField) =ᵐ[volume] fun x => prodJ j (f x) (g x) := by
  simp only [hol, ContinuousLinearMap.holderL_apply_apply]
  exact (prodJ j).coeFn_holder f g

section Terms

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- A term `P_j(coefficient, function)`, bilinear in `(c, m)`. -/
def cf (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple p q 2]
    (πc : Coef →L[ℝ] Lp Space p (volume : Measure Space))
    (πm : M →L[ℝ] Lp Space q (volume : Measure Space)) : Coef →L[ℝ] M →L[ℝ] L2Space :=
  (hol j p q).bilinearComp πc πm

/-- A term `P_j(function, coefficient)`, bilinear in `(c, m)`. -/
def fc (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple p q 2]
    (πm : M →L[ℝ] Lp Space p (volume : Measure Space))
    (πc : Coef →L[ℝ] Lp Space q (volume : Measure Space)) : Coef →L[ℝ] M →L[ℝ] L2Space :=
  ((hol j p q).bilinearComp πm πc).flip

theorem cf_apply (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 2] (πc : Coef →L[ℝ] Lp Space p (volume : Measure Space))
    (πm : M →L[ℝ] Lp Space q (volume : Measure Space)) (c : Coef) (m : M) :
    cf j πc πm c m = hol j p q (πc c) (πm m) := rfl

theorem fc_apply (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 2] (πm : M →L[ℝ] Lp Space p (volume : Measure Space))
    (πc : Coef →L[ℝ] Lp Space q (volume : Measure Space)) (c : Coef) (m : M) :
    fc j πm πc c m = hol j p q (πm m) (πc c) := rfl

theorem coeFn_cf (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 2] (πc : Coef →L[ℝ] Lp Space p (volume : Measure Space))
    (πm : M →L[ℝ] Lp Space q (volume : Measure Space)) (c : Coef) (m : M) :
    (cf j πc πm c m : SpatialField) =ᵐ[volume] fun x => prodJ j (πc c x) (πm m x) :=
  coeFn_hol j _ _

theorem coeFn_fc (j : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderTriple p q 2] (πm : M →L[ℝ] Lp Space p (volume : Measure Space))
    (πc : Coef →L[ℝ] Lp Space q (volume : Measure Space)) (c : Coef) (m : M) :
    (fc j πm πc c m : SpatialField) =ᵐ[volume] fun x => prodJ j (πm m x) (πc c x) :=
  coeFn_hol j _ _

end Terms

/-! ## Function factors -/

/-- `f ↦ f` in `L²`. -/
def xv : X →L[ℝ] L2Space := H1.valueCLM.comp Xincl
/-- `f ↦ ∂ₖf` in `L²`. -/
def xd (k : Fin 3) : X →L[ℝ] L2Space := (H1.derivativeCLM k).comp Xincl
/-- `f ↦ f` in `L⁶` (the compiled `H¹ ⊂ L⁶`). -/
def x6 : X →L[ℝ] L6Space := h1ToL6CLM.comp Xincl

theorem xv_apply (f : X) : xv f = Xclass f := rfl
theorem xd_apply (k : Fin 3) (f : X) : xd k f = f.toH1.derivative k := rfl

theorem coeFn_x6 (f : X) : (x6 f : SpatialField) =ᵐ[volume] Xval f :=
  coeFn_h1ToL6 f.toH1

/-- The ambient tuple `(∂ⱼF, ∂ⱼ∂·F)` of an `H²` field. -/
def h2FirstAmbient (j : Fin 3) : H2 →L[ℝ] H1Ambient :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => L2Space)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (Fin.cons (H2.firstCLM j) (fun k => H2.secondCLM j k) : Fin 4 → (H2 →L[ℝ] L2Space)))

theorem h2FirstAmbient_mem (j : Fin 3) (F : H2) : h2FirstAmbient j F ∈ H1Sub := by
  rw [mem_H1Sub_iff]
  intro i
  exact F.hasWeakSecond j i

/-- `∂ⱼ : H² → H¹`. -/
def h2FirstToH1 (j : Fin 3) : H2 →L[ℝ] H1 :=
  (h2FirstAmbient j).codRestrict H1Sub (h2FirstAmbient_mem j)

@[simp] theorem h2FirstToH1_value (j : Fin 3) (F : H2) : (h2FirstToH1 j F).value = F.first j :=
  rfl

@[simp] theorem h2FirstToH1_derivative (j k : Fin 3) (F : H2) :
    (h2FirstToH1 j F).derivative k = F.second j k := rfl

theorem ιZ_toH1_value (g : Z) : (ιZ g).toH1.value = g.toH2.value := rfl
theorem ιZ_toH1_derivative (g : Z) (k : Fin 3) : (ιZ g).toH1.derivative k = g.toH2.first k :=
  rfl

/-- `g ↦ ∂ₖ∂ⱼg` in `L²`. -/
def zdd (j k : Fin 3) : Z →L[ℝ] L2Space := (H2.secondCLM j k).comp Zincl
/-- `g ↦ ∂ⱼg` in `L⁶`. -/
def zd6 (j : Fin 3) : Z →L[ℝ] L6Space := h1ToL6CLM.comp ((h2FirstToH1 j).comp Zincl)
/-- `g ↦ g` in `L^∞`, given `E : H² → C₀`. -/
def zinf (E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space) : Z →L[ℝ] LinfSpace :=
  toLinf.comp (E.comp Zincl)

theorem zdd_apply (j k : Fin 3) (g : Z) : zdd j k g = g.toH2.second j k := rfl

theorem coeFn_zd6 (j : Fin 3) (g : Z) :
    (zd6 j g : SpatialField) =ᵐ[volume] (g.toH2.first j : SpatialField) :=
  coeFn_h1ToL6 (h2FirstToH1 j g.toH2)

theorem coeFn_zinf (E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space)
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) (g : Z) :
    (zinf E g : SpatialField) =ᵐ[volume] (g.toH2.value : SpatialField) :=
  (coeFn_toLinf (E g.toH2)).trans (hE g.toH2)

/-! ## The operators -/

/-- Column `j` of `U ⊗ f + f ⊗ U`: `f_j U + U_j f`. -/
def colX (j : Fin 3) : Coef →L[ℝ] X →L[ℝ] L2Space :=
  fc j xv πv + cf j πv xv

/-- `∂ₖ` of column `j`: `(∂ₖf)_j U + f_j ∂ₖU + (∂ₖU)_j f + U_j ∂ₖf`. -/
def dcolX (j k : Fin 3) : Coef →L[ℝ] X →L[ℝ] L2Space :=
  fc j (xd k) πv + fc j x6 (πw k) + cf j (πw k) x6 + cf j πv (xd k)

/-- `div(U ⊗ f + f ⊗ U) = ∑ⱼ ∂ⱼ 𝕋_{·j}`. -/
def Gop : Coef →L[ℝ] X →L[ℝ] L2Space := ∑ j : Fin 3, dcolX j j

/-- `∂ₖ` of the four terms of `∂ⱼ 𝕋_{·j}`, for `g ∈ Z`. -/
def dT (E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space) (j k : Fin 3) :
    Coef →L[ℝ] Z →L[ℝ] L2Space :=
  (fc j (zd6 j) (πw k) + fc j (zdd j k) πv) +
  (fc j (zinf E) (πy j k) + fc j (zd6 k) (πw j)) +
  (cf j (πy j k) (zinf E) + cf j (πw j) (zd6 k)) +
  (cf j (πw k) (zd6 j) + cf j πv (zdd j k))

/-- `∂ₖ div(U ⊗ g + g ⊗ U)` for `g ∈ Z`. -/
def GkOp (E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space) (k : Fin 3) :
    Coef →L[ℝ] Z →L[ℝ] L2Space :=
  ∑ j : Fin 3, dT E j k

/-! ## Weak derivatives -/

/-- A Leibniz term gives a pair in the weak derivative graph. -/
theorem graph_of_leibniz (B : Space →L[ℝ] Space →L[ℝ] Space) (k : Fin 3) {a a' : SpatialField}
    (ha : HasWeakSpatialDerivative k a a') (hla : LocL2 a) (hla' : LocL2 a') (F : H1)
    {T T' : L2Space} (hT : (T : SpatialField) =ᵐ[volume] fun x => B (a x) (F.value x))
    (hT' : (T' : SpatialField) =ᵐ[volume]
      fun x => B (a' x) (F.value x) + B (a x) (F.derivative k x)) :
    (T, T') ∈ derivativeGraph k :=
  (mem_derivativeGraph_iff k T T').mpr ((leibniz B k ha hla hla' F).congr hT.symm hT'.symm)

theorem flip_prodJ_apply (j : Fin 3) (u v : Space) : (prodJ j).flip u v = v j • u := rfl

/-- First order: `(𝕋_{·j}, ∂ₖ𝕋_{·j})` is in the weak derivative graph. -/
theorem colX_dcolX_mem {c : Coef}
    (hc : ∀ k, HasWeakSpatialDerivative k (c.1 : SpatialField) (c.2.1 k : SpatialField))
    (j k : Fin 3) (f : X) : (colX j c f, dcolX j k c f) ∈ derivativeGraph k := by
  have e1 : (colX j c f, dcolX j k c f) =
      (fc j xv πv c f, fc j (xd k) πv c f + fc j x6 (πw k) c f) +
      (cf j πv xv c f, cf j (πw k) x6 c f + cf j πv (xd k) c f) := by
    simp only [colX, dcolX, add_apply, Prod.mk_add_mk]
    congr 1
    abel
  rw [e1]
  refine Submodule.add_mem _ ?_ ?_
  · -- `f_j U`: `B = P_j.flip`, coefficient `U`, `H¹` factor `f`
    refine graph_of_leibniz (prodJ j).flip k (hc k) (locL2_Linf c.1) (locL2_L3 _) f.toH1 ?_ ?_
    · filter_upwards [coeFn_fc j xv πv c f] with x hx
      rw [hx, πv_apply, xv_apply, flip_prodJ_apply, prodJ_apply]
      rfl
    · filter_upwards [Lp.coeFn_add (fc j (xd k) πv c f) (fc j x6 (πw k) c f),
        coeFn_fc j (xd k) πv c f, coeFn_fc j x6 (πw k) c f, coeFn_x6 f]
        with x h0 h1 h2 h3
      rw [h0, Pi.add_apply, h1, h2, h3, πv_apply, πw_apply, xd_apply,
        flip_prodJ_apply, flip_prodJ_apply, prodJ_apply, prodJ_apply]
      exact add_comm _ _
  · -- `U_j f`: `B = P_j`, coefficient `U`, `H¹` factor `f`
    refine graph_of_leibniz (prodJ j) k (hc k) (locL2_Linf c.1) (locL2_L3 _) f.toH1 ?_ ?_
    · filter_upwards [coeFn_cf j πv xv c f] with x hx
      rw [hx, πv_apply, xv_apply]
      rfl
    · filter_upwards [Lp.coeFn_add (cf j (πw k) x6 c f) (cf j πv (xd k) c f),
        coeFn_cf j (πw k) x6 c f, coeFn_cf j πv (xd k) c f, coeFn_x6 f]
        with x h0 h1 h2 h3
      rw [h0, Pi.add_apply, h1, h2, h3, πv_apply, πw_apply, xd_apply]
      rfl

/-- The `H¹` field `𝕋_{·j}` with its derivatives. -/
def colH1 {c : Coef}
    (hc : ∀ k, HasWeakSpatialDerivative k (c.1 : SpatialField) (c.2.1 k : SpatialField))
    (j : Fin 3) (f : X) : H1 :=
  H1.ofWeakDerivatives (colX j c f) (fun k => dcolX j k c f)
    (fun k => (mem_derivativeGraph_iff k _ _).mp (colX_dcolX_mem hc j k f))

end UnforcedLeray.Blueprint.L01
