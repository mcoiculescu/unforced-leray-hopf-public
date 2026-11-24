import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.ThinSrc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.Diff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point

/-!
# Entrywise decomposition of `thinSource` and `sepDiffF` (helper for `OscFarPt`)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray UnforcedLeray.Short.IIIa

/-- The `(j₀, k₀)` matrix-entry projection of `F`. -/
def entryF (j₀ k₀ : Fin 3) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x' Y q j k => if j = j₀ ∧ k = k₀ then F x' Y q j₀ k₀ else 0

lemma thinHyp_entryF {c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (h : ThinHyp c ρo F) (j₀ k₀ : Fin 3) : ThinHyp c ρo (entryF j₀ k₀ F) where
  meas i j := by
    unfold entryF
    by_cases hij : i = j₀ ∧ j = k₀
    · simp only [hij, ite_true]; exact h.meas j₀ k₀
    · simp only [hij, ite_false]; exact measurable_const
  per x' Y q := by
    ext j k; unfold entryF; rw [h.per]
  supp x' Y q hρ := by
    ext j k; unfold entryF; simp [h.supp x' Y q hρ]

lemma tensorNorm_entryF_le (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (j₀ k₀ : Fin 3) (x' : ℝ × ℝ) (Y q : ℝ) :
    tensorNorm (entryF j₀ k₀ F x' Y q) ≤ tensorNorm (F x' Y q) := by
  unfold tensorNorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_)
  change (if j = j₀ ∧ k = k₀ then F x' Y q j₀ k₀ else 0) ^ 2 ≤ F x' Y q j k ^ 2
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩; exact le_rfl
  · simp [sq_nonneg]

lemma thinMoment_entryF_le (c : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (j₀ k₀ : Fin 3) : thinMoment c (entryF j₀ k₀ F) ≤ thinMoment c F := by
  unfold thinMoment
  refine lintegral_mono fun w => ?_
  refine mul_le_mul_right (ENNReal.rpow_le_rpow (lintegral_mono fun q => ?_) (by norm_num)) _
  refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (tensorNorm_entryF_le F j₀ k₀ w.1 w.2 q) 2

lemma sepDom_thin_lt_top {ε c ρo ρi : ℝ} {μ : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (h : ThinHyp c ρo F) (hN : thinMoment c F ≠ ⊤) (τ : ℝ) (y : Space) :
    sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (srcNorm (thinSource ε F)) τ y < ⊤ := by
  have hD : 0 < ρi / ε - ρo / ε := by
    rw [← sub_div]; exact div_pos (by linarith) hε
  set D := ρi / ε - ρo / ε
  have ha : -1 < 2 * μ.re + 2 := by linarith
  calc sepDom (2 * μ.re + 2) 0 D (srcNorm (thinSource ε F)) τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
          (ENNReal.ofReal (D ^ (-4 : ℝ)) *
            ∫⁻ z : Space, srcNorm (thinSource ε F) (τ + 2 * Real.log l) z) := by
        unfold sepDom
        refine lintegral_mono fun l => mul_le_mul_right ?_ _
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_mono fun z => mul_le_mul_left (sepKd_zero_le D hD _) _
    _ = ENNReal.ofReal (D ^ (-4 : ℝ)) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
            ∫⁻ z : Space, srcNorm (thinSource ε F) (τ + 2 * Real.log l) z := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun l => ?_
        ring
    _ ≤ ENNReal.ofReal (D ^ (-4 : ℝ)) *
          (ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * μ.re + 2 + 1) * c)))) *
            ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * thinMoment c F)) := by
        gcongr
        exact thin_total hε hc h (2 * μ.re + 2) ha τ
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN))
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

lemma thinSource_entryF (ε : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (j₀ k₀ : Fin 3) (σ : ℝ) (z : Space) (j k : Fin 3) :
    thinSource ε (entryF j₀ k₀ F) σ z j k =
      if j = j₀ ∧ k = k₀ then thinSource ε F σ z j₀ k₀ else 0 := rfl

lemma sepDiffF_entryF (ν ε : ℝ) (μ : ℂ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (j₀ k₀ : Fin 3) (p : ℝ × Space) (y' : Space) (i : Fin 3) :
    sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y' i =
      -2 * ((p.1 : ℂ) ^ (2 * μ + 2) *
        (((fderiv ℝ (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j₀ x) (y' - p.1 • p.2)
          (UnforcedLeray.coordinateVector k₀) : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log p.1) p.2 j₀ k₀ : ℝ) : ℂ))) := by
  unfold sepDiffF
  congr 2
  rw [Finset.sum_eq_single j₀]
  · rw [Finset.sum_eq_single k₀]
    · simp [thinSource_entryF]
    · intro k _ hk; simp [thinSource_entryF, hk]
    · intro hk₀; exact absurd (Finset.mem_univ k₀) hk₀
  · intro j _ hj
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [thinSource_entryF, hj]
  · intro hj₀; exact absurd (Finset.mem_univ j₀) hj₀

lemma sepDiffF_sum_entryF (ν ε : ℝ) (μ : ℂ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (p : ℝ × Space) :
    sepDiffF ν μ (thinSource ε F) τ p =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3, sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p := by
  ext y' i
  simp only [Finset.sum_apply, sepDiffF_entryF]
  unfold sepDiffF
  simp only [Finset.mul_sum]

lemma fderiv_sepDiffF_sum_entryF {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    {p : ℝ × Space} (hp : p.1 ∈ Ioo (0 : ℝ) 1) (y0 : Space) :
    fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p) y0 =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
  have hdiff : ∀ j₀ k₀ : Fin 3,
      DifferentiableAt ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
    intro j₀ k₀
    have hsm := sepDiffF_contDiff heatLerayKSmoothAll ν μ (thinSource ε (entryF j₀ k₀ F)) τ hν p hp
    exact ((contDiff_pi.2 hsm).differentiable (by simp)) y0
  have hd : HasFDerivAt (sepDiffF ν μ (thinSource ε F) τ p)
      (∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0) y0 := by
    rw [sepDiffF_sum_entryF]
    exact HasFDerivAt.sum fun j₀ _ => HasFDerivAt.sum fun k₀ _ => (hdiff j₀ k₀).hasFDerivAt
  exact hd.fderiv

lemma fderiv_sepDiffF_entryF {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (j₀ k₀ : Fin 3)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (z y0 w : Space) (i : Fin 3) :
    (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 w) i =
      (-2 : ℂ) * ((l : ℂ) ^ (2 * μ + 2) *
        ((fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
          (y' - l • z) (UnforcedLeray.coordinateVector k₀)) y0 w : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)) := by
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  have hsm := sepDiffF_contDiff heatLerayKSmoothAll ν μ (thinSource ε (entryF j₀ k₀ F)) τ hν (l, z) hl
  have hdiff : Differentiable ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) :=
    (contDiff_pi.2 hsm).differentiable (by simp)
  have hcomp : HasFDerivAt (fun y' => sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y' i)
      ((ContinuousLinearMap.proj i).comp
        (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0)) y0 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).hasFDerivAt.comp y0
      (hdiff y0).hasFDerivAt
  set g : Space → ℝ := fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
    (y' - l • z) (UnforcedLeray.coordinateVector k₀)
  have hg : DifferentiableAt ℝ g y0 := by
    have hG := (h2_smooth i j₀ k₀ hs).differentiable (by simp)
    exact (hG (y0 - l • z)).comp y0 ((differentiableAt_id).sub_const (l • z))
  have hg' : HasFDerivAt (fun y' => ((g y' : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ g y0)) y0 :=
    Complex.ofRealCLM.hasFDerivAt.comp y0 hg.hasFDerivAt
  have hscal : HasFDerivAt (fun y' => sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y' i)
      ((-2 : ℂ) • ((l : ℂ) ^ (2 * μ + 2) •
        (((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ) •
          (Complex.ofRealCLM.comp (fderiv ℝ g y0))))) y0 := by
    have h1 := ((hg'.mul_const ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)).const_mul
      ((l : ℂ) ^ (2 * μ + 2))).const_mul (-2 : ℂ)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun y' => ?_)
    exact sepDiffF_entryF ν ε μ F τ j₀ k₀ (l, z) y' i
  have heq := congrArg (fun L => L w) (hcomp.unique hscal)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul] at heq
  rw [heq]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
