import UnforcedLeray.Loc.L01Coefficient.SecondOrder

/-!
# Step L1, helpers: the maps `𝓑_*(τ) : X → L²_div` and `Z → X` from a coefficient path

Support for `Loc/L01Coefficient.lean` (step L1, `paper/main.tex` lines 268–290,
`loc:eq:coefficient-maps`, blueprint units B0709, B0711).

* `Bop c f = -𝔓 div(U ⊗ f + f ⊗ U)` (line 271), a bounded linear map `X → L²_div`,
  continuous (even linear) in the coefficient `c` (line 282).
* `BZop hc hE g`: the same expression for `g ∈ Z`, as an element of `X = H¹_div`. Its value
  is `Bop c g`; its derivatives are `-𝔓 ∂ₖ div(U ⊗ g + g ⊗ U)`, using the compiled
  `Leray.h1Projection` (the Leray multiplier commutes with derivatives, lines 288–290; the
  compiled projection replaces the Grafakos citation for this `L²`-based use).
* `Bop_weak`: the literal weak characterization `IsMinusLerayDiv` of the blueprint.
* `isCoefficients_of_path`: a continuous periodic consistent coefficient path representing
  `U_*` gives `IsCoefficients`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L01

open SobolevGraph

/-! ## `X → L²_div` -/

theorem neg_projection_mem (F : L2Space) : -Leray.projection F ∈ Leray.solenoidalSubspace :=
  neg_mem (Leray.projection_mem F)

/-- `-𝔓 div(U ⊗ f + f ⊗ U)` as a map `X → L²` of the coefficient. -/
def BopAmb : Coef →L[ℝ] X →L[ℝ] L2Space :=
  (ContinuousLinearMap.compL ℝ X L2Space L2Space (-Leray.projection)).comp Gop

theorem BopAmb_apply (c : Coef) (f : X) : BopAmb c f = -Leray.projection (Gop c f) := rfl

/-- `𝓑(c) f = -𝔓 div(U ⊗ f + f ⊗ U)`, a bounded map `X → L²_div` (line 271). -/
def Bop (c : Coef) : X →L[ℝ] L2div :=
  (BopAmb c).codRestrict Leray.solenoidalSubspace (fun f => neg_projection_mem (Gop c f))

theorem Lclass_Bop (c : Coef) (f : X) : Lclass (Bop c f) = -Leray.projection (Gop c f) := rfl

theorem continuous_Bop : Continuous Bop :=
  continuous_codRestrict_family Leray.solenoidalSubspace (fun c => BopAmb c)
    BopAmb.continuous (fun c f => neg_projection_mem (Gop c f))

/-! ## `Z → X` -/

/-- The ambient `H¹` tuple `(div 𝕋, ∂₁ div 𝕋, ∂₂ div 𝕋, ∂₃ div 𝕋)` of `g ∈ Z`. -/
def DZamb (E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space) (c : Coef) :
    Z →L[ℝ] H1Ambient :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => L2Space)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (Fin.cons ((Gop c).comp ιZ) (fun k => GkOp E k c) : Fin 4 → (Z →L[ℝ] L2Space)))

theorem DZamb_mem {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) (g : Z) :
    DZamb E c g ∈ H1Sub := by
  rw [mem_H1Sub_iff]
  intro i
  exact (mem_derivativeGraph_iff i _ _).mp (Gop_GkOp_mem hc hE i g)

/-- `div(U ⊗ g + g ⊗ U) ∈ H¹` for `g ∈ Z`. -/
def DZ {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) : Z →L[ℝ] H1 :=
  (DZamb E c).codRestrict H1Sub (DZamb_mem hc hE)

theorem DZ_value {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) (g : Z) :
    (DZ hc hE g).value = Gop c (ιZ g) := rfl

theorem neg_h1Projection_mem (F : H1) : -(Leray.h1Projection F) ∈ Xsub := by
  change H1.valueCLM (-(Leray.h1Projection F)) ∈ Leray.solenoidalSubspace
  rw [map_neg, H1.valueCLM_apply, Leray.value_h1Projection]
  exact neg_projection_mem _

/-- `𝓑(c) g = -𝔓 div(U ⊗ g + g ⊗ U)` as a bounded map `Z → X` (lines 284–290). -/
def BZop {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) : Z →L[ℝ] X :=
  ((-Leray.h1Projection).comp (DZ hc hE)).codRestrict Xsub
    (fun g => neg_h1Projection_mem (DZ hc hE g))

theorem BZop_congr {c c' : Coef} (h : c = c') (hc : IsConsistentCoef c)
    (hc' : IsConsistentCoef c') {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) :
    BZop hc hE = BZop hc' hE := by
  subst h
  rfl

/-- `ιX ∘ 𝓑_Z = 𝓑 ∘ ιZ`. -/
theorem ιX_BZop {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) (g : Z) :
    ιX (BZop hc hE g) = Bop c (ιZ g) := by
  apply Subtype.ext
  change (-(Leray.h1Projection (DZ hc hE g))).value = -Leray.projection (Gop c (ιZ g))
  rw [← H1.valueCLM_apply, map_neg, H1.valueCLM_apply, Leray.value_h1Projection, DZ_value]

/-- A continuous path of consistent coefficients gives a continuous path of `𝓑_Z`. -/
theorem continuous_BZop_path {c : ℝ → Coef} (hcont : Continuous c)
    (hc : ∀ τ, IsConsistentCoef (c τ)) {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField)) :
    Continuous (fun τ => BZop (hc τ) hE) := by
  -- the ambient tuple
  have hpi : Continuous (fun τ => ContinuousLinearMap.pi
      (Fin.cons ((Gop (c τ)).comp ιZ) (fun k => GkOp E k (c τ)) :
        Fin 4 → (Z →L[ℝ] L2Space))) := by
    refine continuous_pi_family (fun i τ => (Fin.cons ((Gop (c τ)).comp ιZ)
      (fun k => GkOp E k (c τ)) : Fin 4 → (Z →L[ℝ] L2Space)) i) (fun i => ?_)
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero]
      exact ((ContinuousLinearMap.compL ℝ Z X L2Space).flip ιZ).continuous.comp
        (Gop.continuous.comp hcont)
    · simp only [Fin.cons_succ]
      exact (GkOp E k).continuous.comp hcont
  have hamb : Continuous (fun τ => DZamb E (c τ)) :=
    (ContinuousLinearMap.compL ℝ Z _ H1Ambient
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => L2Space)).symm.toContinuousLinearMap
      ).continuous.comp hpi
  have hDZ : Continuous (fun τ => DZ (hc τ) hE) :=
    continuous_codRestrict_family H1Sub (fun τ => DZamb E (c τ)) hamb
      (fun τ g => DZamb_mem (hc τ) hE g)
  have hneg : Continuous (fun τ => (-Leray.h1Projection).comp (DZ (hc τ) hE)) :=
    (ContinuousLinearMap.compL ℝ Z H1 H1 (-Leray.h1Projection)).continuous.comp hDZ
  exact continuous_codRestrict_family Xsub
    (fun τ => (-Leray.h1Projection).comp (DZ (hc τ) hE)) hneg
    (fun τ g => neg_h1Projection_mem (DZ (hc τ) hE g))

/-! ## The weak characterization -/

theorem coeFn_colX (j : Fin 3) (c : Coef) (f : X) :
    (colX j c f : SpatialField) =ᵐ[volume]
      fun x => (Xval f x) j • (c.1 : SpatialField) x + ((c.1 : SpatialField) x) j • Xval f x := by
  filter_upwards [Lp.coeFn_add (fc j xv πv c f) (cf j πv xv c f), coeFn_fc j xv πv c f,
    coeFn_cf j πv xv c f] with x h0 h1 h2
  simp only [colX, add_apply, h0, Pi.add_apply, h1, h2, πv_apply, xv_apply, prodJ_apply, Xval]

/-- **The weak characterization** (line 271 with the literal pairing of lines 107–110):
`𝓑(c) f = -𝔓 div(U ⊗ f + f ⊗ U)` tested against every vector test. -/
theorem Bop_weak {c : Coef}
    (hc : ∀ k, HasWeakSpatialDerivative k (c.1 : SpatialField) (c.2.1 k : SpatialField))
    {U : SpatialField} (hU : (c.1 : SpatialField) =ᵐ[volume] U) (f : X) :
    IsMinusLerayDiv (symTensorColumns U (Xval f)) (Lclass (Bop c f)) := by
  have hcol : ∀ j, symTensorColumns U (Xval f) j =ᵐ[volume] (colX j c f : SpatialField) := by
    intro j
    filter_upwards [coeFn_colX j c f, hU] with x h1 h2
    rw [h1, h2]
    rfl
  have hmem : ∀ j, MemLp (symTensorColumns U (Xval f) j) 2 volume :=
    fun j => (Lp.memLp (colX j c f)).ae_eq (hcol j).symm
  have htoL2 : ∀ j, toL2 (symTensorColumns U (Xval f) j) = colX j c f :=
    fun j => Lp.ext ((coeFn_toL2 (hmem j)).trans (hcol j))
  refine ⟨hmem, fun φ hφ => ?_⟩
  have hG : Gop c f = ∑ j : Fin 3, (colH1 hc j f).derivative j := by
    simp only [Gop, sum_apply]
    rfl
  have hterm : ∀ j : Fin 3, inner ℝ (Leray.projection ((colH1 hc j f).derivative j)) (toL2 φ) =
      -inner ℝ (colX j c f) (Leray.projection (toL2 (testPartial φ j))) := by
    intro j
    have h := H1_inner_testPartial (Leray.h1Projection (colH1 hc j f)) hφ j
    have hv : (colH1 hc j f).value = colX j c f := rfl
    rw [Leray.value_h1Projection, Leray.derivative_h1Projection, hv] at h
    rw [eq_neg_iff_add_eq_zero, ← Leray.projection_selfadjoint, h]
    exact add_neg_cancel _
  rw [Lclass_Bop, hG, map_sum, inner_neg_left, sum_inner, lerayDivPairing, neg_neg]
  simp only [hterm, htoL2, Finset.sum_neg_distrib, neg_neg]

/-! ## From a coefficient path to `IsCoefficients` -/

/-- A continuous `𝒯`-periodic path of consistent coefficients `(U, ∇U, ∇²U)` with
`U = U_*(τ)` a.e., and a continuous `𝒯`-periodic `C₀` representative of `U_*`, give the
coefficient maps of `loc:eq:coefficient-maps`. -/
theorem isCoefficients_of_path (D : BackgroundData)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField))
    (c : ℝ → Coef) (hcont : Continuous c) (hper : Function.Periodic c D.period)
    (hcons : ∀ τ, IsConsistentCoef (c τ))
    (hU : ∀ τ, ((c τ).1 : SpatialField) =ᵐ[volume] D.Ustar τ)
    (V : ℝ → ZeroAtInftyContinuousMap Space Space) (hV : Continuous V)
    (hVp : Function.Periodic V D.period)
    (hVU : ∀ τ, (V τ : SpatialField) =ᵐ[volume] D.Ustar τ) :
    IsCoefficients D ⟨fun τ => Bop (c τ), fun τ => BZop (hcons τ) hE⟩ where
  Ustar_C0 := ⟨V, hV, hVp, hVU⟩
  gradient_L3 := ⟨fun τ => (c τ).2.1, (continuous_fst.comp continuous_snd).comp hcont,
    fun τ => by simp only [hper τ],
    fun τ i => ((hcons τ).dv i).congr (hU τ) (ae_eq_refl _)⟩
  B_continuous := continuous_Bop.comp hcont
  B_periodic := fun τ => by simp only [hper τ]
  BZ_continuous := continuous_BZop_path hcont hcons hE
  BZ_periodic := fun τ => BZop_congr (hper τ) (hcons (τ + D.period)) (hcons τ) hE
  B_weak := fun τ f => Bop_weak (hcons τ).dv (hU τ) f
  BZ_compat := fun τ g => ιX_BZop (hcons τ) hE g

end UnforcedLeray.Blueprint.L01
