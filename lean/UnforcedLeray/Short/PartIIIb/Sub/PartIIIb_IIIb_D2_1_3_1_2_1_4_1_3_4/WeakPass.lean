import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4

/-!
# `selWeakPass`: passage to the limit in the slice weak-derivative identity

Source `the November 2 reference manuscript` lines 1334-1337, 1341-1344, 1351-1362.
For a fixed slice, `L²` convergence of `ψ k` and `d k` passes through the pairing with a smooth
compactly supported test (Hölder with a bounded compactly supported factor), so both sides of
`-(∫ ψ k ∂ⱼθ) = ∫ d k θ` converge; uniqueness of limits gives the identity for `(φ0, f0)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The squared `L²` mass of a continuous compactly supported scalar function is finite. -/
private lemma lint_v_lt_top (v : Space → ℂ) (hv : Continuous v) (hvc : HasCompactSupport v) :
    ∫⁻ y, ‖v y‖ₑ ^ (2 : ℝ) < ⊤ := by
  have hm : MemLp v 2 volume := hv.memLp_of_hasCompactSupport hvc
  have h := hm.eLpNorm_lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2] at h
  exact h

/-- Hölder bound for the pairing of an `L²` function with a fixed `L²` factor. -/
private lemma holder_mul (f v : Space → ℂ) (hf : AEStronglyMeasurable f volume) (hv : Continuous v) :
    ∫⁻ y, ‖f y * v y‖ₑ ≤
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ y, ‖v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun y => ‖f y‖ₑ) (g := fun y => ‖v y‖ₑ)
    (hf.aemeasurable.enorm) (hv.enorm.measurable.aemeasurable)
  simpa only [Pi.mul_apply, enorm_mul] using h

/-- An `L²` function times a continuous compactly supported function is integrable. -/
private lemma integrable_mul_v (f v : Space → ℂ) (hf : AEStronglyMeasurable f volume)
    (hv : Continuous v) (hvc : HasCompactSupport v) (hfin : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) < ⊤) :
    Integrable (fun y => f y * v y) volume := by
  refine ⟨hf.mul hv.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  exact lt_of_le_of_lt (holder_mul f v hf hv)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lint_v_lt_top v hv hvc).ne))

/-- Scalar passage to the limit: `L²` convergence of `u k` tested against a fixed `v`. -/
private lemma scalar_conv (v : Space → ℂ) (hv : Continuous v) (hvc : HasCompactSupport v)
    (u : ℕ → Space → ℂ) (u0 : Space → ℂ)
    (hu : ∀ k, AEStronglyMeasurable (u k) volume ∧ ∫⁻ y, ‖u k y‖ₑ ^ (2 : ℝ) < ⊤)
    (hu0 : AEStronglyMeasurable u0 volume ∧ ∫⁻ y, ‖u0 y‖ₑ ^ (2 : ℝ) < ⊤)
    (hconv : Tendsto (fun k => ∫⁻ y, ‖u k y - u0 y‖ₑ ^ (2 : ℝ)) atTop (nhds 0)) :
    Tendsto (fun k => ∫ y, u k y * v y) atTop (nhds (∫ y, u0 y * v y)) := by
  have hC : (∫⁻ y, ‖v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lint_v_lt_top v hv hvc).ne).ne
  have hw : Tendsto (fun k => (∫⁻ y, ‖u k y - u0 y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) atTop (nhds 0) := by
    have h0 : (0 : ENNReal) ^ (1 / (2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hconv
    rw [h0] at h
    exact h
  have hsmall0 := ENNReal.Tendsto.mul_const hw (Or.inr hC)
  rw [zero_mul] at hsmall0
  have hsmall : Tendsto (fun k => ∫⁻ y, ‖(u k y - u0 y) * v y‖ₑ) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsmall0 (fun k => zero_le)
      (fun k => holder_mul (fun y => u k y - u0 y) v ((hu k).1.sub hu0.1) hv)
  have hbd : ∀ k, ‖∫ y, (u k y - u0 y) * v y‖ ≤ (∫⁻ y, ‖(u k y - u0 y) * v y‖ₑ).toReal := by
    intro k
    have hm : AEStronglyMeasurable (fun y => (u k y - u0 y) * v y) volume :=
      ((hu k).1.sub hu0.1).mul hv.aestronglyMeasurable
    calc ‖∫ y, (u k y - u0 y) * v y‖ ≤ ∫ y, ‖(u k y - u0 y) * v y‖ := norm_integral_le_integral_norm _
      _ = (∫⁻ y, ‖(u k y - u0 y) * v y‖ₑ).toReal := integral_norm_eq_lintegral_enorm hm
  have hsq : Tendsto (fun k => (∫⁻ y, ‖(u k y - u0 y) * v y‖ₑ).toReal) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall
    rw [ENNReal.toReal_zero] at h
    exact h
  have hdiff : Tendsto (fun k => ∫ y, (u k y - u0 y) * v y) atTop (nhds 0) :=
    squeeze_zero_norm hbd hsq
  have hsub : ∀ k, ∫ y, (u k y - u0 y) * v y = (∫ y, u k y * v y) - ∫ y, u0 y * v y := by
    intro k
    simp_rw [sub_mul]
    exact integral_sub (integrable_mul_v (u k) v (hu k).1 hv hvc (hu k).2)
      (integrable_mul_v u0 v hu0.1 hv hvc hu0.2)
  exact tendsto_sub_nhds_zero_iff.1 (by simpa only [← hsub] using hdiff)

/-- Pointwise domination of a component: `|f_i| ≤ |f|` inside the slice `L²` integral. -/
private lemma comp_diff_le (f g : Space → CVec3) (i : Fin 3) :
    ∫⁻ y, ‖f y i - g y i‖ₑ ^ (2 : ℝ) ≤ ∫⁻ y, ‖f y - g y‖ₑ ^ (2 : ℝ) := by
  refine lintegral_mono (fun y => ?_)
  have h := PiLp.enorm_apply_le (f y - g y) i
  rw [PiLp.sub_apply] at h
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- A component of an `L²` vector field is an `L²` scalar field. -/
private lemma comp_lint (f : Space → CVec3)
    (hf : AEStronglyMeasurable f volume ∧ ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) < ⊤) (i : Fin 3) :
    AEStronglyMeasurable (fun y => f y i) volume ∧ ∫⁻ y, ‖f y i‖ₑ ^ (2 : ℝ) < ⊤ := by
  have hpr : Continuous fun z : CVec3 => z i := by fun_prop
  refine ⟨hpr.comp_aestronglyMeasurable hf.1, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono (fun y => ?_)) hf.2
  exact ENNReal.rpow_le_rpow (PiLp.enorm_apply_le (f y) i) (by norm_num)

/-- Pairing a vector `L²` field componentwise against scalar test functions. -/
private lemma sum_int (w : Space → CVec3) (vs : Fin 3 → Space → ℂ)
    (hint : ∀ i, Integrable (fun y => w y i * vs i y) volume) :
    ∫ y, ∑ i, w y i * vs i y = ∑ i, ∫ y, w y i * vs i y :=
  integral_finsetSum _ (fun i _ => hint i)

/-- Component of a smooth function is smooth. -/
private lemma comp_smooth (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z => θ z i) := by
  have hpr : ContDiff ℝ ∞ fun z : CVec3 => z i := by fun_prop
  exact hpr.comp hθ

/-- Component of a compactly supported function is compactly supported. -/
private lemma comp_cs (θ : Space → CVec3) (hc : HasCompactSupport θ) (i : Fin 3) :
    HasCompactSupport (fun z => θ z i) :=
  hc.comp_left (g := fun z : CVec3 => z i) (by simp)

/-- The directional derivative `∂ⱼ θ_i`. -/
private def dirD (θ : Space → CVec3) (j : Fin 3) (i : Fin 3) : Space → ℂ :=
  fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))

private lemma dirD_cont (θ : Space → CVec3) (hθ : ContDiff ℝ ∞ θ) (j i : Fin 3) :
    Continuous (dirD θ j i) := by
  have hs := comp_smooth θ hθ i
  exact (hs.continuous_fderiv (by simp)).clm_apply continuous_const

private lemma dirD_c (θ : Space → CVec3) (hc : HasCompactSupport θ) (j i : Fin 3) :
    HasCompactSupport (dirD θ j i) := by
  have h := (comp_cs θ hc i).fderiv (𝕜 := ℝ)
  exact h.comp_left (g := fun L : Space →L[ℝ] ℂ => L (EuclideanSpace.single j (1 : ℝ))) (by simp)

theorem selWeakPass : SelWeakPass := by
  intro ψ d φ0 f0 j hψ hd hφ hf hψc hdc hweak θ hθ hc
  have hψi : ∀ k i, AEStronglyMeasurable (fun y => ψ k y i) volume ∧
      ∫⁻ y, ‖ψ k y i‖ₑ ^ (2 : ℝ) < ⊤ := fun k i => comp_lint (ψ k) (hψ k) i
  have hdi : ∀ k i, AEStronglyMeasurable (fun y => d k y i) volume ∧
      ∫⁻ y, ‖d k y i‖ₑ ^ (2 : ℝ) < ⊤ := fun k i => comp_lint (d k) (hd k) i
  have hφi : ∀ i, AEStronglyMeasurable (fun y => φ0 y i) volume ∧
      ∫⁻ y, ‖φ0 y i‖ₑ ^ (2 : ℝ) < ⊤ := fun i => comp_lint φ0 hφ i
  have hfi : ∀ i, AEStronglyMeasurable (fun y => f0 y i) volume ∧
      ∫⁻ y, ‖f0 y i‖ₑ ^ (2 : ℝ) < ⊤ := fun i => comp_lint f0 hf i
  have hψconv : ∀ i, Tendsto (fun k => ∫⁻ y, ‖ψ k y i - φ0 y i‖ₑ ^ (2 : ℝ)) atTop (nhds 0) :=
    fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hψc (fun k => zero_le)
      (fun k => comp_diff_le (ψ k) φ0 i)
  have hdconv : ∀ i, Tendsto (fun k => ∫⁻ y, ‖d k y i - f0 y i‖ₑ ^ (2 : ℝ)) atTop (nhds 0) :=
    fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdc (fun k => zero_le)
      (fun k => comp_diff_le (d k) f0 i)
  have hθi_cont : ∀ i : Fin 3, Continuous (fun y => θ y i) :=
    fun i => (comp_smooth θ hθ i).continuous
  have hA : ∀ i, Tendsto (fun k => ∫ y, ψ k y i * dirD θ j i y) atTop
      (nhds (∫ y, φ0 y i * dirD θ j i y)) :=
    fun i => scalar_conv (dirD θ j i) (dirD_cont θ hθ j i) (dirD_c θ hc j i)
      (fun k y => ψ k y i) (fun y => φ0 y i) (fun k => hψi k i) (hφi i) (hψconv i)
  have hB : ∀ i, Tendsto (fun k => ∫ y, d k y i * θ y i) atTop
      (nhds (∫ y, f0 y i * θ y i)) :=
    fun i => scalar_conv (fun y => θ y i) (hθi_cont i) (comp_cs θ hc i)
      (fun k y => d k y i) (fun y => f0 y i) (fun k => hdi k i) (hfi i) (hdconv i)
  have hAsum : Tendsto (fun k => ∫ y, ∑ i, ψ k y i * dirD θ j i y) atTop
      (nhds (∫ y, ∑ i, φ0 y i * dirD θ j i y)) := by
    have e1 : (fun k => ∫ y, ∑ i, ψ k y i * dirD θ j i y)
        = fun k => ∑ i, ∫ y, ψ k y i * dirD θ j i y :=
      funext (fun k => sum_int (ψ k) (dirD θ j) (fun i =>
        integrable_mul_v _ _ (hψi k i).1 (dirD_cont θ hθ j i) (dirD_c θ hc j i) (hψi k i).2))
    have e2 : ∫ y, ∑ i, φ0 y i * dirD θ j i y = ∑ i, ∫ y, φ0 y i * dirD θ j i y :=
      sum_int φ0 (dirD θ j) (fun i =>
        integrable_mul_v _ _ (hφi i).1 (dirD_cont θ hθ j i) (dirD_c θ hc j i) (hφi i).2)
    rw [e1, e2]
    exact tendsto_finsetSum _ (fun i _ => hA i)
  have hBsum : Tendsto (fun k => ∫ y, ∑ i, d k y i * θ y i) atTop
      (nhds (∫ y, ∑ i, f0 y i * θ y i)) := by
    have e1 : (fun k => ∫ y, ∑ i, d k y i * θ y i)
        = fun k => ∑ i, ∫ y, d k y i * θ y i :=
      funext (fun k => sum_int (d k) (fun i y => θ y i) (fun i =>
        integrable_mul_v _ _ (hdi k i).1 (hθi_cont i) (comp_cs θ hc i) (hdi k i).2))
    have e2 : ∫ y, ∑ i, f0 y i * θ y i = ∑ i, ∫ y, f0 y i * θ y i :=
      sum_int f0 (fun i y => θ y i) (fun i =>
        integrable_mul_v _ _ (hfi i).1 (hθi_cont i) (comp_cs θ hc i) (hfi i).2)
    rw [e1, e2]
    exact tendsto_finsetSum _ (fun i _ => hB i)
  have hBneg : Tendsto (fun k => ∫ y, ∑ i, d k y i * θ y i) atTop
      (nhds (-(∫ y, ∑ i, φ0 y i * dirD θ j i y))) :=
    hAsum.neg.congr (fun k => hweak k θ hθ hc)
  exact (tendsto_nhds_unique hBsum hBneg).symm

end UnforcedLeray.Short.PartIIIb.Concrete
