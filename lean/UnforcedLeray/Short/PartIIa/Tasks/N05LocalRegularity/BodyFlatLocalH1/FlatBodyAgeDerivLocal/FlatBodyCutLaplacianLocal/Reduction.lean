import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.CellRel

/-!
# `PartII-a:N05/2/2/1`: reduction of `FlatBodyCutLaplacianLocal` to the cylinder heat estimate

Source: `the November 2 reference manuscript`, lines 1794-1799.

`w = T₀ b = R₀(μ)P₀b`. For each component `i`, `u_i = θ(s) w̃_i` solves the cylinder heat
equation with source `f_i` (`isCylHeat_uCut`); the cylinder heat estimate (`CylHeatMaxRegL`, the
local copy of `IIb.CylHeatMaxReg`) gives weak second derivatives `D2 i j j` with
`‖ν D2 i j j‖ ≤ C ‖f_i‖`. With `L = ν(∂_q² + ∂_η²)w` assembled from them, `S_lap = s χ L̃`
(`L̃` the periodic extension) is the localized scaled Laplacian: on the cell
`∫ ⟨ψ, L⟩ = ν ∫ ⟨Δψ, w⟩` for tests in the box (`cell_rel`, `cell_rel_inner`), which together
with the weak flat equation (`weak_cell`) is the identity of `FlatBodyCutLaplacianLocal`, and
`‖S_lap‖ ≤ 4 C (8 + 6M₀) Γ⁶ ‖b‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell periodize QPeriodic
  periodize_of_mem)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta IsNearCutoff IsLargerCutoff Gamma
  GammaBox cNorm8 cNorm8_nonneg T0flat PepsC dsFromS cellL2Norm FlatBodyCutLaplacianLocal)
open UnforcedLeray.Short.PartIIa.N05_2_2Aux (flatCutAgeDriftTerm flatCutAgeForceTerm)
open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

/-! ### Real and imaginary parts of components -/

/-- `v ↦ Re v_i`. -/
def reL (i : Fin 2) : MeridC →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)

/-- `v ↦ Im v_i`. -/
def imL (i : Fin 2) : MeridC →L[ℝ] ℝ :=
  Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)

theorem reL_apply (i : Fin 2) (v : MeridC) : reL i v = (v i).re := rfl

theorem imL_apply (i : Fin 2) (v : MeridC) : imL i v = (v i).im := rfl

theorem inner_decomp (v w : MeridC) :
    inner ℂ v w = ∑ i : Fin 2, (((reL i v : ℝ) : ℂ) * w i - Complex.I * (((imL i v : ℝ) : ℂ) * w i)) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, reL_apply, imL_apply]
  conv_lhs => rw [← Complex.re_add_im (v i)]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem fderiv_clm_comp (L : MeridC →L[ℝ] ℝ) {F : Profile → MeridC} {p : Profile}
    (hF : DifferentiableAt ℝ F p) (w : Profile) :
    fderiv ℝ (fun q => L (F q)) p w = L (fderiv ℝ F p w) := by
  have h := L.hasFDerivAt.comp p hF.hasFDerivAt
  rw [show (fun q => L (F q)) = L ∘ F from rfl, h.fderiv]
  rfl

theorem pdQ_clm (L : MeridC →L[ℝ] ℝ) {F : Profile → MeridC} (hF : Differentiable ℝ F) :
    pdQ (fun q => L (F q)) = fun q => L (pdQ F q) :=
  funext fun p => fderiv_clm_comp L (hF p) _

theorem pdEta_clm (L : MeridC →L[ℝ] ℝ) {F : Profile → MeridC} (hF : Differentiable ℝ F) :
    pdEta (fun q => L (F q)) = fun q => L (pdEta F q) :=
  funext fun p => fderiv_clm_comp L (hF p) _

theorem lapR_clm (L : MeridC →L[ℝ] ℝ) {F : Profile → MeridC} (hF : ContDiff ℝ ∞ F) :
    lapR (fun q => L (F q)) = fun q => L (lapQE F q) := by
  have hd : Differentiable ℝ F := hF.differentiable (by simp)
  have hdQ : Differentiable ℝ (pdQ F) := (contDiff_pdQ' hF).differentiable (by simp)
  have hdE : Differentiable ℝ (pdEta F) := (contDiff_pdEta' hF).differentiable (by simp)
  funext p
  simp only [lapR, lapQE]
  rw [pdQ_clm L hd, pdQ_clm L hdQ, pdEta_clm L hd, pdEta_clm L hdE, map_add]

/-- **Componentwise to vector**: scalar weak relations for real tests give the vector relation
`∫ ⟨ψ, Lp⟩ = ∫ ⟨Δψ, Vf⟩`. -/
theorem cell_rel_inner {c σ H1 L : ℝ} {Lp Vf : Profile → MeridC}
    (hrel : ∀ (i : Fin 2) (a : Profile → ℝ), ContDiff ℝ ∞ a → QPeriodic c a →
      (∀ p, a p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L) →
      Integrable (fun x => (a x : ℂ) * Lp x i) (cellMeasure c) ∧
        Integrable (fun x => (lapR a x : ℂ) * Vf x i) (cellMeasure c) ∧
        ∫ x, (a x : ℂ) * Lp x i ∂(cellMeasure c) = ∫ x, (lapR a x : ℂ) * Vf x i ∂(cellMeasure c))
    {ψ : Profile → MeridC} (hψs : ContDiff ℝ ∞ ψ) (hψp : QPeriodic c ψ)
    (hband : ∀ p, ψ p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L) :
    ∫ x, inner ℂ (ψ x) (Lp x) ∂(cellMeasure c) =
      ∫ x, inner ℂ (lapQE ψ x) (Vf x) ∂(cellMeasure c) := by
  have hcond : ∀ (Λ : MeridC →L[ℝ] ℝ), ContDiff ℝ ∞ (fun x => Λ (ψ x)) ∧
      QPeriodic c (fun x => Λ (ψ x)) ∧
      (∀ p, Λ (ψ p) ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L) := by
    intro Λ
    refine ⟨Λ.contDiff.comp hψs, fun p => by simp only [hψp p], fun p hp => hband p fun h => ?_⟩
    exact hp (by rw [h, map_zero])
  have hR : ∀ i : Fin 2, _ := fun i => hrel i _ (hcond (reL i)).1 (hcond (reL i)).2.1
    (hcond (reL i)).2.2
  have hI : ∀ i : Fin 2, _ := fun i => hrel i _ (hcond (imL i)).1 (hcond (imL i)).2.1
    (hcond (imL i)).2.2
  simp only [lapR_clm _ hψs] at hR hI
  have e1 : ∀ x, inner ℂ (ψ x) (Lp x) = ∑ i : Fin 2,
      (((reL i (ψ x) : ℝ) : ℂ) * Lp x i - Complex.I * (((imL i (ψ x) : ℝ) : ℂ) * Lp x i)) :=
    fun x => inner_decomp _ _
  have e2 : ∀ x, inner ℂ (lapQE ψ x) (Vf x) = ∑ i : Fin 2,
      (((reL i (lapQE ψ x) : ℝ) : ℂ) * Vf x i -
        Complex.I * (((imL i (lapQE ψ x) : ℝ) : ℂ) * Vf x i)) :=
    fun x => inner_decomp _ _
  simp only [e1, e2, Fin.sum_univ_two]
  obtain ⟨hR0a, hR0b, hR0⟩ := hR 0
  obtain ⟨hR1a, hR1b, hR1⟩ := hR 1
  obtain ⟨hI0a, hI0b, hI0⟩ := hI 0
  obtain ⟨hI1a, hI1b, hI1⟩ := hI 1
  have hA0 : Integrable (fun x => ((reL 0 (ψ x) : ℝ) : ℂ) * Lp x 0 -
      Complex.I * (((imL 0 (ψ x) : ℝ) : ℂ) * Lp x 0)) (cellMeasure c) :=
    hR0a.sub (hI0a.const_mul _)
  have hA1 : Integrable (fun x => ((reL 1 (ψ x) : ℝ) : ℂ) * Lp x 1 -
      Complex.I * (((imL 1 (ψ x) : ℝ) : ℂ) * Lp x 1)) (cellMeasure c) :=
    hR1a.sub (hI1a.const_mul _)
  have hB0 : Integrable (fun x => ((reL 0 (lapQE ψ x) : ℝ) : ℂ) * Vf x 0 -
      Complex.I * (((imL 0 (lapQE ψ x) : ℝ) : ℂ) * Vf x 0)) (cellMeasure c) :=
    hR0b.sub (hI0b.const_mul _)
  have hB1 : Integrable (fun x => ((reL 1 (lapQE ψ x) : ℝ) : ℂ) * Vf x 1 -
      Complex.I * (((imL 1 (lapQE ψ x) : ℝ) : ℂ) * Vf x 1)) (cellMeasure c) :=
    hR1b.sub (hI1b.const_mul _)
  rw [integral_add hA0 hA1, integral_add hB0 hB1,
    integral_sub hR0a (hI0a.const_mul _), integral_sub hR1a (hI1a.const_mul _),
    integral_sub hR0b (hI0b.const_mul _), integral_sub hR1b (hI1b.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hR0, hR1, hI0, hI1]

/-! ### Conversions to `cellL2Norm` -/

theorem cellL2Norm_le_of_eLpNorm {c X : ℝ} {u : Profile → MeridC} (hu : MemLp u 2 (cellMeasure c))
    (hX : 0 ≤ X) (h : eLpNorm u 2 (cellMeasure c) ≤ ENNReal.ofReal X) : cellL2Norm c u ≤ X := by
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hu.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hle : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤ ENNReal.ofReal (X ^ 2) := by
    rw [← eLpNorm_two_rpow_two]
    calc eLpNorm u 2 (cellMeasure c) ^ (2 : ℝ) ≤ ENNReal.ofReal X ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = ENNReal.ofReal (X ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hX (by norm_num), Real.rpow_two]
  have hint_le : ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) ≤ X ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact hle
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (X ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = X := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hX]

end UnforcedLeray.Short.PartIIa.FBCLL
