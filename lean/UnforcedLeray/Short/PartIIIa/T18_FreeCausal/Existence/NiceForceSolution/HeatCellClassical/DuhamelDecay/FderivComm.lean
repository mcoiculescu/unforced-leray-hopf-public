import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_4
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelSmooth

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4/5`: the x-derivative of the Duhamel solution

Target: `duhDecFderivComm : DuhDecFderivComm` (`Sub/PartIIIa_T18_2_4_1_4.lean`, leaf 5 of the
Duhamel decay; SP 3427-3440 of `the November 2 reference manuscript`).

`fderiv ℝ (y ↦ duhamelHeat ν h s y) x e = duhamelHeat ν (duhDecDirDeriv e h) s x`.

Proof. Write the Duhamel solution as the product-measure integral
`∫ α, G_α * h (p - α)` (`DuhamelSmooth`, `integral_prod`). Differentiate in the direction `e`
under the integral with `hasDerivAt_integral_of_dominated_loc_of_deriv_le`: the `t`-derivative of
`h((s, x + t e) - α)` is `duhDecDirDeriv e h ((s, x + t e) - α)`, bounded by `‖e‖ K₁` and
vanishing for `α.1 > s - a` (the source vanishes for `s - α.1 < a`). The identity
`fderiv f x e = derivative of t ↦ f (x + t e)` (chain rule) identifies the two derivatives.
Domination and measurability reuse the product-measure facts of `DuhamelSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem fdc_slice {h : ℝ × (ℝ × ℝ) → ℂ} (hh : Differentiable ℝ h) (s : ℝ) (x e : ℝ × ℝ) :
    fderiv ℝ (fun y => h (s, y)) x e = fderiv ℝ h (s, x) (0, e) := by
  have hd : HasFDerivAt (fun y : ℝ × ℝ => h (s, y))
      ((fderiv ℝ h (s, x)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x :=
    (hh (s, x)).hasFDerivAt.comp x ((hasFDerivAt_const s x).prodMk (hasFDerivAt_id x))
  rw [hd.fderiv]
  simp

theorem fdc_dd {h : ℝ × (ℝ × ℝ) → ℂ} (hh : Differentiable ℝ h) (e : ℝ × ℝ) (q : ℝ × (ℝ × ℝ)) :
    duhDecDirDeriv e h q = fderiv ℝ h q (0, e) := by
  obtain ⟨s, x⟩ := q
  exact fdc_slice hh s x e

theorem fdc_meas {ν : ℝ} (g : ℝ × (ℝ × ℝ) → ℂ) (hg : Continuous g) (p : ℝ × (ℝ × ℝ)) :
    AEStronglyMeasurable (fun α : ℝ × (ℝ × ℝ) => ((duhSm_G ν α : ℝ) : ℂ) * g (p - α)) duhSm_μ :=
  ((Complex.measurable_ofReal.comp (duhSm_G_measurable ν)).mul
    (hg.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable

theorem fdc_int {ν : ℝ} (hν : 0 < ν) (g : ℝ × (ℝ × ℝ) → ℂ) (hg : Continuous g) (M a : ℝ)
    (hM : ∀ q, ‖g q‖ ≤ M) (hz : ∀ q : ℝ × (ℝ × ℝ), q.1 < a → g q = 0)
    (p : ℝ × (ℝ × ℝ)) :
    Integrable (fun α : ℝ × (ℝ × ℝ) => ((duhSm_G ν α : ℝ) : ℂ) * g (p - α)) duhSm_μ := by
  refine ((duhSm_int_ind hν (p.1 - a)).const_mul M).mono' (fdc_meas g hg p) ?_
  rw [duhSm_μ_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with α hα
  have hpos : 0 < α.1 := hα.1
  have hG : 0 ≤ duhSm_G ν α := UnforcedLeray.B0284.heatKernel2_nonneg (mul_pos hν hpos) α.2
  try dsimp only
  by_cases hr : α.1 ≤ p.1 - a
  · have hmem : α ∈ Ioc (0 : ℝ) (p.1 - a) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨⟨hpos, hr⟩, mem_univ _⟩
    rw [indicator_of_mem hmem, norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
    calc duhSm_G ν α * ‖g (p - α)‖ ≤ duhSm_G ν α * M :=
          mul_le_mul_of_nonneg_left (hM _) hG
      _ = M * duhSm_G ν α := mul_comm _ _
  · have hnot : α ∉ Ioc (0 : ℝ) (p.1 - a) ×ˢ (univ : Set (ℝ × ℝ)) := fun hm => hr hm.1.2
    rw [indicator_of_notMem hnot, mul_zero]
    have hpa : (p - α).1 < a := by
      show p.1 - α.1 < a
      linarith [not_le.mp hr]
    rw [hz (p - α) hpa]
    simp

theorem fdc_D {ν : ℝ} (hν : 0 < ν) (g : ℝ × (ℝ × ℝ) → ℂ) (hg : Continuous g) (M a : ℝ)
    (hM : ∀ q, ‖g q‖ ≤ M) (hz : ∀ q : ℝ × (ℝ × ℝ), q.1 < a → g q = 0)
    (p : ℝ × (ℝ × ℝ)) :
    duhamelHeat ν g p.1 p.2 = ∫ α, ((duhSm_G ν α : ℝ) : ℂ) * g (p - α) ∂duhSm_μ := by
  have hint := fdc_int hν g hg M a hM hz p
  unfold duhamelHeat
  exact (integral_prod (fun α : ℝ × (ℝ × ℝ) => ((duhSm_G ν α : ℝ) : ℂ) * g (p - α)) hint).symm

theorem duhDecFderivComm : UnforcedLeray.Short.IIIa.DuhDecFderivComm := by
  intro c ν h hc hν hn s x e
  obtain ⟨hsm, -, a, B, R, ha, hvan⟩ := duhSm_unfold hn
  have hdiff : Differentiable ℝ h := hsm.differentiable (by simp)
  have hcont : Continuous h := hsm.continuous
  have hzh : ∀ q : ℝ × (ℝ × ℝ), q.1 < a → h q = 0 := fun q hq => hvan q.1 q.2 (Or.inl hq)
  obtain ⟨K0, hK0⟩ := duhSm_bound hc hn 0
  obtain ⟨K1, hK1⟩ := duhSm_bound hc hn 1
  have hM : ∀ q, ‖h q‖ ≤ K0 := fun q => by
    have := hK0 q
    rwa [norm_iteratedFDeriv_zero] at this
  have hK1nn : 0 ≤ K1 := (norm_nonneg _).trans (hK1 0)
  have hfdb : ∀ q, ‖fderiv ℝ h q‖ ≤ K1 := fun q => by
    have := hK1 q
    rwa [norm_iteratedFDeriv_one] at this
  have hE : ‖((0 : ℝ), e)‖ ≤ ‖e‖ := by
    rw [Prod.norm_def]
    simp
  have hDb : ∀ q, ‖duhDecDirDeriv e h q‖ ≤ K1 * ‖e‖ := fun q => by
    rw [fdc_dd hdiff e q]
    exact ((fderiv ℝ h q).le_opNorm _).trans (mul_le_mul (hfdb q) hE (norm_nonneg _) hK1nn)
  have hzD : ∀ q : ℝ × (ℝ × ℝ), q.1 < a → duhDecDirDeriv e h q = 0 := fun q hq => by
    show fderiv ℝ (fun y => h (q.1, y)) q.2 e = 0
    have hz : (fun y : ℝ × ℝ => h (q.1, y)) = fun _ => 0 :=
      funext fun y => hvan q.1 y (Or.inl hq)
    rw [hz]
    simp
  have hDcont : Continuous (duhDecDirDeriv e h) := by
    have hfun : duhDecDirDeriv e h = fun p => fderiv ℝ h p (0, e) :=
      funext fun q => fdc_dd hdiff e q
    rw [hfun]
    exact (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsmD : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => duhamelHeat ν h p.1 p.2) :=
    duhamelSmooth c ν h hc hν hn
  have hfd : DifferentiableAt ℝ (fun y : ℝ × ℝ => duhamelHeat ν h s y) x := by
    have hc2 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => duhamelHeat ν h s y) :=
      hsmD.comp ((contDiff_const (c := s)).prodMk contDiff_id)
    exact (hc2.differentiable (by simp)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const e).const_add x
  have hF : HasFDerivAt (fun y : ℝ × ℝ => duhamelHeat ν h s y)
      (fderiv ℝ (fun y : ℝ × ℝ => duhamelHeat ν h s y) x) (x + (0 : ℝ) • e) := by
    rw [zero_smul, add_zero]
    exact hfd.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt 0 hline
  have hbound : ∀ᵐ α ∂duhSm_μ, ∀ t ∈ (univ : Set ℝ),
      ‖((duhSm_G ν α : ℝ) : ℂ) * duhDecDirDeriv e h ((s, x + t • e) - α)‖
        ≤ (K1 * ‖e‖) * (Ioc (0 : ℝ) (s - a) ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) α := by
    rw [duhSm_μ_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with α hα t _
    have hpos : 0 < α.1 := hα.1
    have hG : 0 ≤ duhSm_G ν α := UnforcedLeray.B0284.heatKernel2_nonneg (mul_pos hν hpos) α.2
    by_cases hr : α.1 ≤ s - a
    · have hmem : α ∈ Ioc (0 : ℝ) (s - a) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨⟨hpos, hr⟩, mem_univ _⟩
      rw [indicator_of_mem hmem, norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
      nlinarith [mul_le_mul_of_nonneg_left (hDb ((s, x + t • e) - α)) hG]
    · have hnot : α ∉ Ioc (0 : ℝ) (s - a) ×ˢ (univ : Set (ℝ × ℝ)) := fun hm => hr hm.1.2
      rw [indicator_of_notMem hnot, mul_zero]
      have hlt : ((s, x + t • e) - α).1 < a := by
        show s - α.1 < a
        linarith [not_le.mp hr]
      rw [hzD _ hlt]
      simp
  have hdiffae : ∀ᵐ α ∂duhSm_μ, ∀ t ∈ (univ : Set ℝ),
      HasDerivAt (fun τ : ℝ => ((duhSm_G ν α : ℝ) : ℂ) * h ((s, x + τ • e) - α))
        (((duhSm_G ν α : ℝ) : ℂ) * duhDecDirDeriv e h ((s, x + t • e) - α)) t := by
    refine ae_of_all _ fun α t _ => ?_
    have hline2 : HasDerivAt (fun τ : ℝ => ((s, x) - α) + τ • ((0 : ℝ), e)) ((0 : ℝ), e) t := by
      simpa using ((hasDerivAt_id' t).smul_const ((0 : ℝ), e)).const_add ((s, x) - α)
    have hcomp2 := (hdiff (((s, x) - α) + t • ((0 : ℝ), e))).hasFDerivAt.comp_hasDerivAt t hline2
    have hcomp3 := hcomp2.const_mul ((duhSm_G ν α : ℝ) : ℂ)
    have hfn : (fun τ : ℝ => ((duhSm_G ν α : ℝ) : ℂ) * h ((s, x + τ • e) - α)) =
        fun y : ℝ => ((duhSm_G ν α : ℝ) : ℂ) *
          (h ∘ fun τ : ℝ => ((s, x) - α) + τ • ((0 : ℝ), e)) y := by
      funext τ
      have hφ : (s, x + τ • e) - α = ((s, x) - α) + τ • ((0 : ℝ), e) := by
        ext <;> simp <;> ring
      simp only [Function.comp, hφ]
    have hval : ((duhSm_G ν α : ℝ) : ℂ) * duhDecDirDeriv e h ((s, x + t • e) - α)
        = ((duhSm_G ν α : ℝ) : ℂ) *
          fderiv ℝ h (((s, x) - α) + t • ((0 : ℝ), e)) ((0 : ℝ), e) := by
      have hφ : (s, x + t • e) - α = ((s, x) - α) + t • ((0 : ℝ), e) := by
        ext <;> simp <;> ring
      rw [hφ, fdc_dd hdiff e]
    rw [hfn, hval]
    exact hcomp3
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := duhSm_μ)
    (F := fun t α => ((duhSm_G ν α : ℝ) : ℂ) * h ((s, x + t • e) - α))
    (F' := fun t α => ((duhSm_G ν α : ℝ) : ℂ) * duhDecDirDeriv e h ((s, x + t • e) - α))
    (x₀ := (0 : ℝ)) (s := univ) univ_mem
    (Filter.Eventually.of_forall fun t => fdc_meas h hcont (s, x + t • e))
    (fdc_int hν h hcont K0 a hM hzh (s, x + (0 : ℝ) • e))
    (fdc_meas (duhDecDirDeriv e h) hDcont (s, x + (0 : ℝ) • e))
    hbound ((duhSm_int_ind hν (s - a)).const_mul (K1 * ‖e‖)) hdiffae
  have hd1 : HasDerivAt ((fun y : ℝ × ℝ => duhamelHeat ν h s y) ∘ fun t : ℝ => x + t • e)
      (∫ α, ((duhSm_G ν α : ℝ) : ℂ) * duhDecDirDeriv e h ((s, x + (0 : ℝ) • e) - α) ∂duhSm_μ) 0 := by
    have hfn2 : (fun n : ℝ => ∫ α, ((duhSm_G ν α : ℝ) : ℂ) * h ((s, x + n • e) - α) ∂duhSm_μ)
        = (fun y : ℝ × ℝ => duhamelHeat ν h s y) ∘ fun t : ℝ => x + t • e := by
      funext n
      exact (fdc_D hν h hcont K0 a hM hzh (s, x + n • e)).symm
    rw [← hfn2]
    exact hderiv.2
  have key := hcomp.unique hd1
  have hD' : duhamelHeat ν (duhDecDirDeriv e h) s x
      = ∫ α, ((duhSm_G ν α : ℝ) : ℂ) * duhDecDirDeriv e h ((s, x) - α) ∂duhSm_μ :=
    fdc_D hν (duhDecDirDeriv e h) hDcont (K1 * ‖e‖) a hDb hzD (s, x)
  rw [key, hD']
  simp only [zero_smul, add_zero]

end UnforcedLeray.Short.IIIa
