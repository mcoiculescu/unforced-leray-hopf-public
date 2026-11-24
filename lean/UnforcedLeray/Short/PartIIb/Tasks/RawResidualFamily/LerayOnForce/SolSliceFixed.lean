import UnforcedLeray.Short.PartIIb.Sub.R1_3

/-!


Target (`Sub/R1_3.lean`, `def SolSliceFixed`):
`theorem solSliceFixed : UnforcedLeray.Short.IIb.SolSliceFixed`.

Source of record: `the November 2 reference manuscript`, lines 2519-2524;
`paper/main.tex` lines 7364-7387 (B0439) and 11539-11560 (B0797).

Route:
1. `ssf_isSolenoidal_of_divFree`: a real `C^∞` field with compact support and pointwise zero
   divergence is `IsSolenoidal` (integration by parts, one coordinate at a time).
2. Apply it to `reV ∘ φ` and `imV ∘ φ`; `isSolenoidalC_iff` then gives `IsSolenoidalC φ`.
3. `lerayC_apply` and `lerayLp_eq_self` on the real and imaginary parts, then
   `ofReV_reV_add_ofImV_imV`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray UnforcedLeray.RieszLp UnforcedLeray.B0414
open UnforcedLeray.PhaseSpace (CVec3)

namespace UnforcedLeray.Short.IIb

/-! ## Calculus -/

/-- The coordinate projection `ℝ³ → ℝ`, `x ↦ x i`. -/
def ssfCoord (i : Fin 3) : Space →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ) (𝕜 := ℝ) i

/-- Chain rule for a continuous linear map applied after a differentiable map. -/
theorem ssf_fderiv_clm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) {φ : Space → E}
    (hφ : Differentiable ℝ φ) (y v : Space) :
    fderiv ℝ (fun x => L (φ x)) y v = L (fderiv ℝ φ y v) := by
  have h := L.hasFDerivAt.comp y (hφ y).hasFDerivAt
  have h2 := congrArg (fun T : Space →L[ℝ] G => T v) h.fderiv
  exact h2

/-- The `i`-th coordinate of a derivative. -/
theorem ssf_fderiv_coord {F : Space → Space} (hF : Differentiable ℝ F) (i : Fin 3) (y v : Space) :
    fderiv ℝ (fun x => F x i) y v = fderiv ℝ F y v i :=
  ssf_fderiv_clm (ssfCoord i) hF y v

theorem ssf_contDiff_coord {F : Space → Space} (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => F x i) :=
  (ssfCoord i).contDiff.comp hF

/-- Integrability from continuity and vanishing off a compact set. -/
theorem ssf_integrable {h : Space → ℝ} {K : Set Space} (hK : IsCompact K) (hc : Continuous h)
    (hz : ∀ x, x ∉ K → h x = 0) : Integrable h :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hK hz)

/-- Solenoidality is invariant under almost-everywhere equality. -/
theorem ssf_isSolenoidal_congr {f g : Space → Space} (hf : IsSolenoidal f)
    (hfg : f =ᵐ[volume] g) : IsSolenoidal g where
  integrable ψ hψ := (hf.integrable ψ hψ).congr (hfg.mono fun x hx => by simp only [hx])
  identity ψ hψ :=
    (integral_congr_ae (hfg.symm.mono fun x hx => by simp only [hx])).trans (hf.identity ψ hψ)

/-! ## Integration by parts -/

/-- A compactly supported `C^∞` field with pointwise zero divergence is solenoidal. -/
theorem ssf_isSolenoidal_of_divFree {F : Space → Space} (hFs : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F)
    (hdiv : ∀ y : Space, ∑ j : Fin 3, fderiv ℝ F y (coordinateVector j) j = 0) :
    IsSolenoidal F := by
  have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
  have hFz : ∀ x, x ∉ tsupport F → F x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hFi : ∀ i : Fin 3, Continuous (fun x => F x i) := fun i =>
    (ssf_contDiff_coord hFs i).continuous
  have hFi_der : ∀ i : Fin 3,
      Continuous (fun x => fderiv ℝ (fun y => F y i) x (coordinateVector i)) := fun i =>
    ((ssf_contDiff_coord hFs i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_der : ∀ ψ : Space → ℝ, IsSpatialTest ψ → ∀ i : Fin 3,
      Continuous (fun x => spatialTestDerivative i ψ x) := fun ψ hψ i =>
    (hψ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  -- integrability of the three products used by integration by parts
  have hA : ∀ ψ : Space → ℝ, IsSpatialTest ψ → ∀ i : Fin 3,
      Integrable (fun x => F x i * spatialTestDerivative i ψ x) := fun ψ hψ i =>
    ssf_integrable hFc.isCompact ((hFi i).mul (hψ_der ψ hψ i))
      (fun x hx => by simp [hFz x hx])
  have hB : ∀ ψ : Space → ℝ, IsSpatialTest ψ → ∀ i : Fin 3,
      Integrable (fun x => fderiv ℝ (fun y => F y i) x (coordinateVector i) * ψ x) :=
    fun ψ hψ i =>
      ssf_integrable hψ.compact.isCompact ((hFi_der i).mul hψ.smooth.continuous)
        (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hC : ∀ ψ : Space → ℝ, IsSpatialTest ψ → ∀ i : Fin 3,
      Integrable (fun x => F x i * ψ x) := fun ψ hψ i =>
    ssf_integrable hFc.isCompact ((hFi i).mul hψ.smooth.continuous)
      (fun x hx => by simp [hFz x hx])
  -- one coordinate at a time
  have ibp : ∀ ψ : Space → ℝ, IsSpatialTest ψ → ∀ i : Fin 3,
      ∫ x, F x i * spatialTestDerivative i ψ x =
        -∫ x, fderiv ℝ (fun y => F y i) x (coordinateVector i) * ψ x := by
    intro ψ hψ i
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (hB ψ hψ i) (hA ψ hψ i) (hC ψ hψ i)
      (fun x _ => ((ssf_contDiff_coord hFs i).differentiable (by simp)) x)
      (fun x _ => (hψ.smooth.differentiable (by simp)) x)
  have key : ∀ ψ : Space → ℝ, IsSpatialTest ψ →
      ∫ x, ∑ i : Fin 3, F x i * spatialTestDerivative i ψ x = 0 := by
    intro ψ hψ
    have hdivψ : ∀ x : Space,
        ∑ i : Fin 3, fderiv ℝ (fun y => F y i) x (coordinateVector i) * ψ x = 0 := by
      intro x
      rw [← Finset.sum_mul]
      simp only [ssf_fderiv_coord hFd]
      rw [hdiv x, zero_mul]
    calc ∫ x, ∑ i : Fin 3, F x i * spatialTestDerivative i ψ x
        = ∑ i : Fin 3, ∫ x, F x i * spatialTestDerivative i ψ x :=
          integral_finsetSum _ (fun i _ => hA ψ hψ i)
      _ = ∑ i : Fin 3, -∫ x, fderiv ℝ (fun y => F y i) x (coordinateVector i) * ψ x :=
          Finset.sum_congr rfl (fun i _ => ibp ψ hψ i)
      _ = -∫ x, ∑ i : Fin 3, fderiv ℝ (fun y => F y i) x (coordinateVector i) * ψ x := by
          rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hB ψ hψ i)]
      _ = 0 := by simp only [hdivψ, integral_zero, neg_zero]
  exact ⟨fun ψ hψ => integrable_finsetSum _ (fun i _ => hA ψ hψ i), fun ψ hψ => key ψ hψ⟩

/-! ## The complex field -/

/-- A smooth compactly supported complex field with pointwise zero divergence is `IsSolenoidalC`. -/
theorem ssf_isSolenoidalC {φ : Space → CVec3} (hφs : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hdiv : ∀ y : Space, ∑ j : Fin 3, fderiv ℝ φ y (coordinateVector j) j = 0) :
    IsSolenoidalC φ := by
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  have hre : IsSolenoidal (fun x => reV (φ x)) := by
    refine ssf_isSolenoidal_of_divFree (reV.contDiff.comp hφs)
      (hφc.comp_left (map_zero reV)) ?_
    intro y
    have h := congrArg Complex.re (hdiv y)
    simp only [Complex.re_sum, Complex.zero_re] at h
    simpa [ssf_fderiv_clm reV hφd] using h
  have him : IsSolenoidal (fun x => imV (φ x)) := by
    refine ssf_isSolenoidal_of_divFree (imV.contDiff.comp hφs)
      (hφc.comp_left (map_zero imV)) ?_
    intro y
    have h := congrArg Complex.im (hdiv y)
    simp only [Complex.im_sum, Complex.zero_im] at h
    simpa [ssf_fderiv_clm imV hφd] using h
  exact (isSolenoidalC_iff φ).2 ⟨hre, him⟩

/-- `𝔓_p` fixes a smooth compactly supported divergence-free complex field, `1 < p < ∞`. -/
theorem ssf_lerayC_fixed {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : Space → CVec3)
    (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hdiv : ∀ y : Space, ∑ j : Fin 3, fderiv ℝ φ y (coordinateVector j) j = 0)
    (hm : MemLp φ p volume) :
    lerayC p hp1 hp (hm.toLp φ) = hm.toLp φ := by
  obtain ⟨hR, hI⟩ := (isSolenoidalC_iff φ).1 (ssf_isSolenoidalC hφs hφc hdiv)
  have hGe : (hm.toLp φ : Space → CVec3) =ᵐ[volume] φ := hm.coeFn_toLp
  have hfR : (fun x => reV (φ x)) =ᵐ[volume] ⇑(reV.compLpL p volume (hm.toLp φ)) := by
    filter_upwards [reV.coeFn_compLpL (μ := volume) (p := p) (hm.toLp φ), hGe] with x h1 h2
    simp only [h1, h2]
  have hfI : (fun x => imV (φ x)) =ᵐ[volume] ⇑(imV.compLpL p volume (hm.toLp φ)) := by
    filter_upwards [imV.coeFn_compLpL (μ := volume) (p := p) (hm.toLp φ), hGe] with x h1 h2
    simp only [h1, h2]
  have hRe : lerayLp p hp1 hp (reV.compLpL p volume (hm.toLp φ)) =
      reV.compLpL p volume (hm.toLp φ) :=
    lerayLp_eq_self hp1 hp (reV.compLpL p volume (hm.toLp φ)) (ssf_isSolenoidal_congr hR hfR)
  have hIm : lerayLp p hp1 hp (imV.compLpL p volume (hm.toLp φ)) =
      imV.compLpL p volume (hm.toLp φ) :=
    lerayLp_eq_self hp1 hp (imV.compLpL p volume (hm.toLp φ)) (ssf_isSolenoidal_congr hI hfI)
  rw [lerayC_apply, hRe, hIm]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofReV.compLpL p volume (reV.compLpL p volume (hm.toLp φ)))
      (ofImV.compLpL p volume (imV.compLpL p volume (hm.toLp φ))),
    ofReV.coeFn_compLpL (μ := volume) (p := p) (reV.compLpL p volume (hm.toLp φ)),
    ofImV.coeFn_compLpL (μ := volume) (p := p) (imV.compLpL p volume (hm.toLp φ)),
    reV.coeFn_compLpL (μ := volume) (p := p) (hm.toLp φ),
    imV.coeFn_compLpL (μ := volume) (p := p) (hm.toLp φ)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply, h1, h2, h3, h4, h5, ofReV_reV_add_ofImV_imV]

/-! ## The target -/

/-- **Leaf `PartII-b:R1/3/2`: `𝔓` fixes smooth compactly supported divergence-free fields.** -/
theorem solSliceFixed : UnforcedLeray.Short.IIb.SolSliceFixed := by
  intro φ hφs hφc hdiv hm
  exact ssf_lerayC_fixed _ _ φ hφs hφc hdiv hm

end UnforcedLeray.Short.IIb
