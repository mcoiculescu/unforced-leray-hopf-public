import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/4`: `inletAdvTranspose1_of`

Source `the November 2 reference manuscript`
lines 2385-2387.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseInt)
open UnforcedLeray.B0411 (dotFn)
open UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.PartIIIb.Concrete

private def realCLI' : UnforcedLeray.Space →ₗᵢ[ℝ] CVec3 where
  toFun := UnforcedLeray.B0412.realC
  map_add' x y := by
    ext i
    simp [UnforcedLeray.B0412.realC_apply]
  map_smul' c x := by
    ext i
    simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, UnforcedLeray.B0412.realC_apply, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]

private def gradLr' : UnforcedLeray.Space →L[ℝ] CVec3 := realCLI'.toContinuousLinearMap

private theorem gradLr'_apply_coord (v : UnforcedLeray.Space) (i : Fin 3) :
    gradLr' v i = ((v i : ℝ) : ℂ) := by
  show realCLI' v i = _
  exact UnforcedLeray.B0412.realC_apply v i

private theorem fderiv_slice_aux' {R : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hR : Differentiable ℝ R) (τ : ℝ) (y v : UnforcedLeray.Space) :
    fderiv ℝ (fun x : UnforcedLeray.Space => R (τ, x)) y v = fderiv ℝ R (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : UnforcedLeray.Space => (τ, x))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hR (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

private theorem dy_gradVj' (V : ℝ → UnforcedLeray.SpatialField)
    (hV : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    (k : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space) :
    dy k (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) (τ, y)
      = fderiv ℝ (V τ) y (EuclideanSpace.single k 1) := by
  unfold dy
  rw [← fderiv_slice_aux' (hV.differentiable (by simp)) τ y (UnforcedLeray.coordinateVector k)]
  rfl

private theorem dy_gradLr' (g : ℝ × UnforcedLeray.Space → UnforcedLeray.Space) (hg : ContDiff ℝ ∞ g)
    (j : Fin 3) (p : ℝ × UnforcedLeray.Space) :
    dy j (fun q => gradLr' (g q)) p = gradLr' (dy j g p) := by
  have hd := (gradLr'.hasFDerivAt.comp p (hg.differentiable (by simp) p).hasFDerivAt).fderiv
  unfold dy
  rw [show (fun q => gradLr' (g q)) = gradLr' ∘ g from rfl, hd]
  rfl

private theorem gradAlong_eq_advT (V : ℝ → UnforcedLeray.SpatialField)
    (hV : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    (E : ℝ × UnforcedLeray.Space → CVec3) :
    gradAlong V E = advT E (fun x => UnforcedLeray.B0412.realC (V x.1 x.2)) := by
  funext ⟨τ, y⟩
  ext i
  unfold gradAlong advT
  rw [WithLp.ofLp_sum]
  simp only [WithLp.ofLp_toLp, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := dy_gradLr' (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) hV k (τ, y)
  have h2 : (fun q : ℝ × UnforcedLeray.Space => gradLr' (V q.1 q.2)) =
      fun x => UnforcedLeray.B0412.realC (V x.1 x.2) := rfl
  rw [← h2, h1, dy_gradVj' V hV k τ y, gradLr'_apply_coord]

private theorem contDiff_raw_of_realC'' {p : Params}
    (hRC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2))) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) := by
  apply (contDiff_piLp 2).2
  intro k
  have hcoord : (fun x : ℝ × UnforcedLeray.Space => (p.raw x.1 x.2).ofLp k) =
      fun x : ℝ × UnforcedLeray.Space => (UnforcedLeray.B0412.realC (p.raw x.1 x.2) k).re := by
    funext x
    simp [UnforcedLeray.B0412.realC_apply]
  rw [hcoord]
  exact Complex.reCLM.contDiff.comp ((contDiff_piLp_apply (p := 2) (i := k)).comp hRC)

private theorem advT_div_identity {A Φ B : ℝ × UnforcedLeray.Space → CVec3}
    (hA : ContDiff ℝ ∞ A) (hΦ : ContDiff ℝ ∞ Φ) (hB : ContDiff ℝ ∞ B)
    (hdiv : ∀ x : ℝ × UnforcedLeray.Space, ∑ j : Fin 3, dy j A x j = 0)
    (z : ℝ × UnforcedLeray.Space) :
    ∑ k : Fin 3, dy k (fun w => A w k * dotFn Φ B w) z =
      dotL (advT A Φ z) (B z) + dotL (Φ z) (advT A B z) := by
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hBd : Differentiable ℝ B := hB.differentiable (by simp)
  have hk : ∀ k : Fin 3, dy k (fun w => A w k * dotFn Φ B w) z =
      dy k A z k * dotFn Φ B z + A z k * (dotL (dy k Φ z) (B z) + dotL (Φ z) (dy k B z)) := by
    intro k
    rw [srwf_dy_mul ((srwf_coord_contDiff hA k).differentiable (by simp))
      (UnforcedLeray.B0411.differentiable_dotFn hΦd hBd) k z,
      srwf_dy_coord hAd k k z, UnforcedLeray.B0411.dy_dotFn hΦd hBd k z]
  simp only [hk]
  have hd := hdiv z
  simp only [Fin.sum_univ_three] at hd
  simp only [Fin.sum_univ_three, advT, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, dotL_apply, PiLp.add_apply, PiLp.smul_apply]
  linear_combination (dotFn Φ B z) * hd

private theorem pairF_advT_transpose {P : ℝ} {A Φ B : ℝ × UnforcedLeray.Space → CVec3}
    (hA : ContDiff ℝ ∞ A) (hΦ : IsPhaseTest P Φ) (hB : ContDiff ℝ ∞ B)
    (hdiv : ∀ x : ℝ × UnforcedLeray.Space, ∑ j : Fin 3, dy j A x j = 0) :
    pairF P (advT A Φ) B = -pairF P Φ (advT A B) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hD : ContDiff ℝ ∞ (dotFn Φ B) := srwf_dotFn_contDiff hΦc hB
  have hAdvc : Continuous (advT A Φ) := by
    unfold advT
    exact continuous_finset_sum _ fun k _ =>
      (srwf_coord_contDiff hA k).continuous.smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hΦc k).continuous
  have hB_int : Integrable (fun z => dotL (advT A Φ z) (B z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hAdvc).clm_apply hB.continuous) (R := R)
      (fun t y hy => by
        have h0 : advT A Φ (t, y) = 0 := by
          unfold advT
          exact Finset.sum_eq_zero fun k _ => by rw [srwf_dy_bdd hR k t y hy, smul_zero]
        simp [h0])
  have hK'p : ∀ k : Fin 3,
      Integrable (fun z => dy k (fun w => A w k * dotFn Φ B w) z) (srwfSlab P) ∧
        ∫ z, dy k (fun w => A w k * dotFn Φ B w) z ∂(srwfSlab P) = 0 := by
    intro k
    exact srwf_slab_dy (R := R) ((srwf_coord_contDiff hA k).mul hD)
      (fun τ y hy => by simp [dotFn, hR τ y hy]) k
  have hDd_int : Integrable (fun z => dotL (Φ z) (advT A B z)) (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (advT A B z)) =
        fun z => (∑ k : Fin 3, dy k (fun w => A w k * dotFn Φ B w) z) -
          dotL (advT A Φ z) (B z) := by
      funext z
      rw [advT_div_identity hA hΦc hB hdiv z]
      ring
    rw [e]
    exact (integrable_finsetSum _ fun k _ => (hK'p k).1).sub hB_int
  have hBD : ∫ z, dotL (advT A Φ z) (B z) ∂(srwfSlab P) +
      ∫ z, dotL (Φ z) (advT A B z) ∂(srwfSlab P) = 0 := by
    rw [← integral_add hB_int hDd_int]
    have e : (fun z => dotL (advT A Φ z) (B z) + dotL (Φ z) (advT A B z)) =
        fun z => ∑ k : Fin 3, dy k (fun w => A w k * dotFn Φ B w) z :=
      funext fun z => (advT_div_identity hA hΦc hB hdiv z).symm
    rw [e, integral_finsetSum _ fun k _ => (hK'p k).1,
      Finset.sum_eq_zero fun k _ => (hK'p k).2]
  unfold pairF
  rw [srwf_phaseInt_eq hB_int, srwf_phaseInt_eq hDd_int]
  have hneg : ∫ z, dotL (advT A Φ z) (B z) ∂(srwfSlab P) =
      -∫ z, dotL (Φ z) (advT A B z) ∂(srwfSlab P) := eq_neg_of_add_eq_zero_left hBD
  rw [hneg, smul_neg]

theorem inletAdvTranspose1_of (hReg : InletFieldRegular) : InletAdvTranspose1 := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := hReg lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i ψ hψ => ?_⟩
  obtain ⟨hRC, _, hE⟩ := H0 p d hreg hν hm z g hg
  obtain ⟨hEs, _, hEdiv⟩ := hE i
  have hR := contDiff_raw_of_realC'' hRC
  rw [gradAlong_eq_advT p.raw hR (p.Efun i)]
  exact pairF_advT_transpose hEs hψ hRC hEdiv

end UnforcedLeray.Short.PartIIIb.Concrete
