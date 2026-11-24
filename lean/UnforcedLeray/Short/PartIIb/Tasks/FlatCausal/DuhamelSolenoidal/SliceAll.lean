import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.SliceAe
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.CountableDense
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.SliceGauss
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.GaussExtend

/-!
# Part II-b, task `PartII-b:T12/6/6` (`DsolSliceAll`): slice solenoidality against all planar tests

Source of record: `the November 2 reference manuscript`, SP 1924 (the heat flow
preserves solenoidality). Target: `DsolSliceAll` of `Sub/T12_6.lean`.

Proof. Let `D` be the countable family of `DsolCountableDense`. For `ψ ∈ D` the fixed-test lemma
`dsol_slice_ae` gives a null set; the countable union of these null sets, together with the
exceptional set of `dsolSliceGauss`, is null (`ae_ball_iff`). Fix a good `t > 0` and a smooth
compactly supported `ψ`. Take `R` from `DsolCountableDense` and let `M = max R M_ψ`, where `M_ψ`
bounds the support of `ψ`. For `ε > 0` pick `ψ' ∈ D` with `|ψ - ψ'| + |Dψ - Dψ'| ≤ ε` and
`ψ' = 0` off the ball of radius `R`. Then `∫ dsolF ψ = ∫ dsolF ψ' + ∫ dsolF (ψ - ψ')`, the first term
vanishes by the choice of `t`, and the second is bounded by `ε K` where
`K = ∫ 2 e^{2M²} e^{-|y|²} ‖G(t,y)‖ dy` is finite by `DsolGaussInt`. Since `ε` is arbitrary the
integral vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Elementary helpers -/

lemma dsa_fderiv_vanish {f : ℝ × ℝ → ℝ} {M : ℝ} (h : ∀ y : ℝ × ℝ, M < ‖y‖ → f y = 0)
    {y : ℝ × ℝ} (hy : M < ‖y‖) : fderiv ℝ f y = 0 := by
  have hev : f =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact h z hz
  rw [hev.fderiv_eq]
  simp

lemma dsa_compact_vanish {f : ℝ × ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ M : ℝ, ∀ y : ℝ × ℝ, M < ‖y‖ → f y = 0 := by
  obtain ⟨M, hM⟩ := (hf.isCompact.isBounded).subset_closedBall (0 : ℝ × ℝ)
  refine ⟨M, fun y hy => image_eq_zero_of_notMem_tsupport ?_⟩
  intro h
  have h2 := hM h
  rw [mem_closedBall_zero_iff] at h2
  linarith

lemma dsa_zero_of_bound {a K : ℝ} (hK : 0 ≤ K) (h : ∀ ε : ℝ, 0 < ε → a ≤ ε * K) : a ≤ 0 := by
  by_contra hne
  push_neg at hne
  have hK1 : K + 1 ≠ 0 := (by linarith : (0 : ℝ) < K + 1).ne'
  have hε : 0 < a / (2 * (K + 1)) := div_pos hne (by linarith)
  have h1 := h _ hε
  have h2 : a / (2 * (K + 1)) * (K + 1) = a / 2 := by
    field_simp
  have h3 : a / (2 * (K + 1)) * K ≤ a / (2 * (K + 1)) * (K + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  linarith

lemma dsa_fderiv_sub (ψ ψ' : ℝ × ℝ → ℝ) (hψ : Differentiable ℝ ψ)
    (hψ' : Differentiable ℝ ψ') (y : ℝ × ℝ) :
    fderiv ℝ (fun z => ψ z - ψ' z) y = fderiv ℝ ψ y - fderiv ℝ ψ' y :=
  fderiv_sub (hψ y) (hψ' y)

lemma dsa_split (G : CProf) (ψ ψ' : ℝ × ℝ → ℝ) (hψ : Differentiable ℝ ψ)
    (hψ' : Differentiable ℝ ψ') (x : Coord) :
    dsolF G (fun z => ψ z - ψ' z) x = dsolF G ψ x - dsolF G ψ' x := by
  unfold dsolF
  rw [dsa_fderiv_sub ψ ψ' hψ hψ' x.2]
  simp only [ContinuousLinearMap.sub_apply, Complex.ofReal_sub]
  ring

/-! ## Pointwise and integral bounds on the slice -/

/-- Pointwise bound of the slice pairing by the Gaussian-weighted norm of the slice. -/
lemma dsa_pt_bound (G : CProf) (t : ℝ) {χ : ℝ × ℝ → ℝ} {M C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : ℝ × ℝ, ‖fderiv ℝ χ y‖ ≤ C) (hM : ∀ y : ℝ × ℝ, M < ‖y‖ → fderiv ℝ χ y = 0)
    (y : ℝ × ℝ) :
    ‖dsolF G χ (t, y)‖ ≤
      C * (2 * Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖)) := by
  have hpair : ‖dsolF G χ (t, y)‖ ≤
      ‖G (t, y)‖ * (|fderiv ℝ χ y (1, 0)| + |fderiv ℝ χ y (0, 1)|) := by
    have := dsol_pair_norm_le (G (t, y)) (fderiv ℝ χ y (1, 0)) (fderiv ℝ χ y (0, 1))
    unfold dsolF
    exact this
  have hRHS0 : 0 ≤ C * (2 * Real.exp (2 * M ^ 2) *
      (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖)) :=
    mul_nonneg hC0 (mul_nonneg (by positivity) (mul_nonneg (by positivity) (norm_nonneg _)))
  by_cases hy : M < ‖y‖
  · have h1 : fderiv ℝ χ y (1, 0) = 0 := by simp [hM y hy]
    have h2 : fderiv ℝ χ y (0, 1) = 0 := by simp [hM y hy]
    rw [h1, h2, abs_zero, add_zero, mul_zero] at hpair
    linarith
  · push_neg at hy
    have h1 : ‖y.1‖ ≤ M := (norm_fst_le y).trans hy
    have h2 : ‖y.2‖ ≤ M := (norm_snd_le y).trans hy
    rw [Real.norm_eq_abs] at h1 h2
    have a1 : y.1 ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs y.1, abs_nonneg y.1]
    have a2 : y.2 ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs y.2, abs_nonneg y.2]
    have hs : y.1 ^ 2 + y.2 ^ 2 ≤ 2 * M ^ 2 := by linarith
    have hexp : Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * Real.exp (y.1 ^ 2 + y.2 ^ 2) = 1 := by
      rw [← Real.exp_add, show (-1 * (y.1 ^ 2 + y.2 ^ 2) + (y.1 ^ 2 + y.2 ^ 2)) = 0 by ring,
        Real.exp_zero]
    have hexp_le : Real.exp (y.1 ^ 2 + y.2 ^ 2) ≤ Real.exp (2 * M ^ 2) := Real.exp_le_exp.2 hs
    have hE : 0 ≤ Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    have hG : ‖G (t, y)‖ ≤
        Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := by
      have heq : ‖G (t, y)‖ = Real.exp (y.1 ^ 2 + y.2 ^ 2) *
          (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := by
        have hre : Real.exp (y.1 ^ 2 + y.2 ^ 2) *
            (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) =
            (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * Real.exp (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖ := by
          ring
        rw [hre, hexp, one_mul]
      calc ‖G (t, y)‖ = Real.exp (y.1 ^ 2 + y.2 ^ 2) *
            (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := heq
        _ ≤ Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) :=
          mul_le_mul_of_nonneg_right hexp_le hE
    have ha : |fderiv ℝ χ y (1, 0)| ≤ C :=
      (dsol_abs_fderiv_le χ y (1, 0) dsol_norm_e0_le).trans (hC y)
    have hb : |fderiv ℝ χ y (0, 1)| ≤ C :=
      (dsol_abs_fderiv_le χ y (0, 1) dsol_norm_e1_le).trans (hC y)
    have hG2 : ‖G (t, y)‖ * (|fderiv ℝ χ y (1, 0)| + |fderiv ℝ χ y (0, 1)|) ≤
        ‖G (t, y)‖ * (2 * C) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left hG (mul_nonneg zero_le_two hC0)
    calc ‖dsolF G χ (t, y)‖ ≤ ‖G (t, y)‖ * (|fderiv ℝ χ y (1, 0)| + |fderiv ℝ χ y (0, 1)|) := hpair
      _ ≤ ‖G (t, y)‖ * (2 * C) := hG2
      _ ≤ C * (2 * Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖)) := by
        linarith [h3]

/-- Integrability of the slice pairing of a smooth compactly supported test. -/
lemma dsa_slice_integrable (G : CProf) (t : ℝ) (hg : DsolGaussInt (fun y : ℝ × ℝ => G (t, y)))
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    Integrable (fun y : ℝ × ℝ => dsolF G χ (t, y)) := by
  obtain ⟨M, hM⟩ := dsa_compact_vanish hχc
  obtain ⟨C, hC⟩ := (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hχc.fderiv (𝕜 := ℝ))
  have hMvan : ∀ y : ℝ × ℝ, M < ‖y‖ → fderiv ℝ χ y = 0 := fun y hy => dsa_fderiv_vanish hM hy
  have hC' : ∀ y : ℝ × ℝ, ‖fderiv ℝ χ y‖ ≤ max C 0 := fun y => (hC y).trans (le_max_left _ _)
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  have hint : Integrable (fun y : ℝ × ℝ => max C 0 *
      (2 * Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖))) :=
    ((dsol_gauss_norm_integrable hg one_pos).const_mul (2 * Real.exp (2 * M ^ 2))).const_mul
      (max C 0)
  exact hint.mono' (dsolE_aesm G t (dsol_gauss_aesm hg) hχ)
    (ae_of_all _ fun y => dsa_pt_bound G t hC'0 hC' hMvan y)

/-- The slice pairing of a test is bounded by `C K`, with `K` independent of the test. -/
lemma dsa_slice_norm_bound (G : CProf) (t : ℝ) (hg : DsolGaussInt (fun y : ℝ × ℝ => G (t, y)))
    (M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (χ : ℝ × ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ y : ℝ × ℝ, ‖fderiv ℝ χ y‖ ≤ C) →
      (∀ y : ℝ × ℝ, M < ‖y‖ → fderiv ℝ χ y = 0) →
        ‖∫ y : ℝ × ℝ, dsolF G χ (t, y)‖ ≤ C * K := by
  refine ⟨∫ y : ℝ × ℝ, 2 * Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖),
    integral_nonneg (fun y => mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (norm_nonneg _))), fun χ C hC0 hC hM => ?_⟩
  have hint : Integrable (fun y : ℝ × ℝ => C *
      (2 * Real.exp (2 * M ^ 2) * (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖))) :=
    ((dsol_gauss_norm_integrable hg one_pos).const_mul (2 * Real.exp (2 * M ^ 2))).const_mul C
  calc ‖∫ y : ℝ × ℝ, dsolF G χ (t, y)‖
      ≤ ∫ y : ℝ × ℝ, C * (2 * Real.exp (2 * M ^ 2) *
          (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖)) :=
        norm_integral_le_of_norm_le hint (ae_of_all _ fun y => dsa_pt_bound G t hC0 hC hM y)
    _ = C * ∫ y : ℝ × ℝ, 2 * Real.exp (2 * M ^ 2) *
          (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := integral_const_mul C _

/-! ## The leaf -/

/-- **Leaf `PartII-b:T12/6/6`** (SP 1924). For a weakly solenoidal `G ∈ H_r`, for a.e. `t > 0`
the slice `G(t, ·)` is weakly divergence free against all smooth compactly supported planar tests
at once. -/
theorem dsolSliceAll : DsolSliceAll := by
  unfold DsolSliceAll
  intro c r G hc hr1 hr3 hG hW
  obtain ⟨D, hDc, hDreg, hDapp⟩ := dsolCountableDense
  have hAeD : ∀ᵐ t : ℝ, ∀ ψ ∈ D, t ∈ Ioi (0 : ℝ) → ∫ y : ℝ × ℝ, dsolF G ψ (t, y) = 0 := by
    refine (ae_ball_iff hDc).2 fun ψ hψ => ?_
    exact dsol_slice_ae hW (hDreg ψ hψ).1 (hDreg ψ hψ).2
  filter_upwards [hAeD, dsolSliceGauss c r G hc hr1 hr3 hG] with t hD hGt ht ψ hψ hψc
  have hg : DsolGaussInt (fun y : ℝ × ℝ => G (t, y)) := hGt ht
  have hD0 : ∀ ψ' ∈ D, ∫ y : ℝ × ℝ, dsolF G ψ' (t, y) = 0 := fun ψ' h => hD ψ' h ht
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  obtain ⟨R, hR⟩ := hDapp ψ hψ hψc
  obtain ⟨Mψ, hMψ⟩ := dsa_compact_vanish hψc
  obtain ⟨K, hK0, hKb⟩ := dsa_slice_norm_bound G t hg (max R Mψ)
  have hψM : ∀ y : ℝ × ℝ, max R Mψ < ‖y‖ → ψ y = 0 :=
    fun y hy => hMψ y (lt_of_le_of_lt (le_max_right _ _) hy)
  have hψint : Integrable (fun y : ℝ × ℝ => dsolF G ψ (t, y)) :=
    dsa_slice_integrable G t hg hψ hψc
  have key : ∀ ε : ℝ, 0 < ε →
      ‖∫ y : ℝ × ℝ, dsolF G ψ (t, y)‖ ≤ ε * K := by
    intro ε hε
    obtain ⟨ψ', hψ'D, hψ'van, hψ'ap⟩ := hR ε hε
    obtain ⟨hψ's, hψ'c⟩ := hDreg ψ' hψ'D
    have hψ'd : Differentiable ℝ ψ' := hψ's.differentiable (by simp)
    have hψ'M : ∀ y : ℝ × ℝ, max R Mψ < ‖y‖ → ψ' y = 0 :=
      fun y hy => hψ'van y (lt_of_le_of_lt (le_max_left _ _) hy)
    have hψ'int : Integrable (fun y : ℝ × ℝ => dsolF G ψ' (t, y)) :=
      dsa_slice_integrable G t hg hψ's hψ'c
    have hχc : HasCompactSupport (fun z => ψ z - ψ' z) := hψc.sub hψ'c
    have hχs : ContDiff ℝ ∞ (fun z => ψ z - ψ' z) := hψ.sub hψ's
    have hχint : Integrable (fun y : ℝ × ℝ => dsolF G (fun z => ψ z - ψ' z) (t, y)) :=
      dsa_slice_integrable G t hg hχs hχc
    have hχC : ∀ y : ℝ × ℝ, ‖fderiv ℝ (fun z => ψ z - ψ' z) y‖ ≤ ε := by
      intro y
      rw [dsa_fderiv_sub ψ ψ' hψd hψ'd y]
      have h1 := hψ'ap y
      have h2 := abs_nonneg (ψ y - ψ' y)
      linarith
    have hχM : ∀ y : ℝ × ℝ, max R Mψ < ‖y‖ → fderiv ℝ (fun z => ψ z - ψ' z) y = 0 := by
      intro y hy
      rw [dsa_fderiv_sub ψ ψ' hψd hψ'd y, dsa_fderiv_vanish hψM hy, dsa_fderiv_vanish hψ'M hy,
        sub_zero]
    have hsplit : ∀ y : ℝ × ℝ, dsolF G ψ (t, y) =
        dsolF G ψ' (t, y) + dsolF G (fun z => ψ z - ψ' z) (t, y) := fun y => by
      rw [dsa_split G ψ ψ' hψd hψ'd (t, y)]
      ring
    have hsum : (∫ y : ℝ × ℝ, dsolF G ψ (t, y)) =
        (∫ y : ℝ × ℝ, dsolF G ψ' (t, y)) + (∫ y : ℝ × ℝ, dsolF G (fun z => ψ z - ψ' z) (t, y)) := by
      rw [← integral_add hψ'int hχint]
      exact integral_congr_ae (ae_of_all _ fun y => hsplit y)
    rw [hsum, hD0 ψ' hψ'D, zero_add]
    exact hKb _ ε hε.le hχC hχM
  have h0 : ‖∫ y : ℝ × ℝ, dsolF G ψ (t, y)‖ ≤ 0 := dsa_zero_of_bound hK0 key
  exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _))

end UnforcedLeray.Short.IIb
