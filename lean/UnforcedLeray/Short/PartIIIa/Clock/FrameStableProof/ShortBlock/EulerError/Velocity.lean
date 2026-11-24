import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Tail

/-!
# Cylinder versus planar velocity of a Gaussian source (helper for `PartIII-a:T21/c3/3/3`)

Source of record: `the November 2 reference manuscript` (SP), lines 2875-2888:
for `|x| ≤ d/8` the paired-image kernel satisfies `K_d - K_∞ = O(d⁻²|x - y|)`, the source tail
is Gaussian-small and the far kernel costs `O(d⁻¹)`; hence the localized velocity error is
`O(d⁻²)`.

`vel_compare`: let `e` be continuous with `|e(z)| ≤ C_e e^{-|z|²/8}` and `W` continuous with
`|W - e| ≤ T d⁻² e^{-|z|²/16}` on the cell. For `|y| ≤ d/8`,
`|K_d W(y) - K_∞ e(y)| ≤ K (T + C_e)(1 + |y|) d⁻²`. The cell integral is split as
`∫_cell (W - e) K_d + ∫_N e (K_d - K_∞) + ∫_{cell∖N} e K_d - ∫_{Nᶜ} e K_∞`,
`N = {|z| < d/5}`: the first and third terms by `cellKer_bound`, the second by the image
expansion `IIb.norm_bsKernel_sub_planarBSKernel_le_of_norm_le`, the fourth by
`|K_∞(y - z)| ≤ 3/d` off `N`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerErrorTail

theorem continuous_planeToC : Continuous planeToC :=
  (Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ).continuous

theorem norm_planeToC_sq' (z : ℝ × ℝ) : z.1 ^ 2 + z.2 ^ 2 = ‖planeToC z‖ ^ 2 :=
  (OscillatorForceSub.norm_planeToC_sq z).symm

theorem kerD_zero_vec {d : ℝ} (hd : 1 ≤ d) (k : Fin 2) : kerD d 0 k = 0 := by
  obtain ⟨C, _, hNF⟩ := kerNearFar
  have h := (hNF d hd).2.2.1 0 k
  rw [neg_zero] at h
  linarith

theorem planarBSKernel_zero_vec (k : Fin 2) : IIb.planarBSKernel 0 k = 0 := by
  rw [planarBSKernel_apply]
  have h0 : planeToC (0 : ℝ × ℝ) = 0 := Complex.ext (by simp [planeToC]) (by simp [planeToC])
  rw [h0]
  fin_cases k <;> simp [B0009.kernel, B0009.perpComp]

/-- Gaussian splitting `e^{-r²/8} ≤ e^{-r²/16} e^{-ρ²/16}` for `ρ ≤ r`. -/
theorem exp_split {r ρ : ℝ} (h : ρ ^ 2 ≤ r ^ 2) :
    Real.exp (-(r ^ 2) / 8) ≤ Real.exp (-(r ^ 2) / 16) * Real.exp (-(ρ ^ 2) / 16) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith

/-- Pointwise near-zone bound. -/
theorem near_pointwise {d : ℝ} (hd : 1 ≤ d) {e : ℝ × ℝ → ℂ} {C_e : ℝ} (hCe : 0 ≤ C_e)
    (he : ∀ z, ‖e z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) {y z : ℝ × ℝ}
    (hy : ‖planeToC y‖ ≤ d / 8) (hz : ‖planeToC z‖ < d / 5) (k : Fin 2) :
    ‖e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z‖ ≤
      IIb.pairedImageConst * C_e * (1 + ‖planeToC y‖) / d ^ 2 *
        (4 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) := by
  have hd0 : 0 < d := by linarith
  set c := IIb.pairedImageConst with hc
  have hc0 : 0 ≤ c := IIb.pairedImageConst_pos.le
  rw [kernel_planeToC_eq]
  have hfac : e z * ((kerD d (y - z) k : ℝ) : ℂ) - ((IIb.planarBSKernel (y - z) k : ℝ) : ℂ) * e z =
      e z * ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k : ℝ) : ℂ) := by
    push_cast; ring
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hYZ : ‖planeToC (y - z)‖ ≤ ‖planeToC y‖ + ‖planeToC z‖ := by
    rw [planeToC_sub]; exact norm_sub_le _ _
  have hkd : |kerD d (y - z) k - IIb.planarBSKernel (y - z) k| ≤
      c * (1 / d ^ 2) * ‖planeToC (y - z)‖ := by
    by_cases h0 : y - z = 0
    · rw [h0, kerD_zero_vec hd, planarBSKernel_zero_vec]
      simp only [sub_self, abs_zero]
      positivity
    · have hle : IIb.euclidNorm (y - z) ≤ d / 2 := by
        rw [← IIb.norm_ofPlane]
        change ‖planeToC (y - z)‖ ≤ d / 2
        linarith
      have h1 := IIb.norm_bsKernel_sub_planarBSKernel_le_of_norm_le hd0 h0 hle
      have h2 : |kerD d (y - z) k - IIb.planarBSKernel (y - z) k| ≤
          ‖Cyl.bsKernel d (y - z) - IIb.planarBSKernel (y - z)‖ := by
        have := PiLp.norm_apply_le (Cyl.bsKernel d (y - z) - IIb.planarBSKernel (y - z)) k
        rw [Real.norm_eq_abs] at this
        exact this
      have h3 : d ^ (-(2 : ℝ)) = 1 / d ^ 2 := by
        rw [Real.rpow_neg hd0.le, Real.rpow_two, one_div]
      have h4 : IIb.euclidNorm (y - z) = ‖planeToC (y - z)‖ := by
        rw [← IIb.norm_ofPlane]; rfl
      rw [h3, h4] at h1
      exact h2.trans h1
  have hez := he z
  rw [norm_planeToC_sq' z] at hez ⊢
  set r := ‖planeToC z‖ with hr
  set ρ := ‖planeToC y‖ with hρ
  have hr0 : 0 ≤ r := norm_nonneg _
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hsplit : Real.exp (-(r ^ 2) / 8) = Real.exp (-(r ^ 2) / 16) * Real.exp (-(r ^ 2) / 16) := by
    rw [← Real.exp_add]; ring_nf
  have hpoly := one_add_mul_exp_le hr0
  have hE := Real.exp_pos (-(r ^ 2) / 16)
  have hdq : 0 < 1 / d ^ 2 := by positivity
  calc ‖e z‖ * |kerD d (y - z) k - IIb.planarBSKernel (y - z) k|
      ≤ (C_e * Real.exp (-(r ^ 2) / 8)) * (c * (1 / d ^ 2) * (ρ + r)) := by
        refine mul_le_mul hez (hkd.trans ?_) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hYZ (by positivity)
    _ ≤ (C_e * Real.exp (-(r ^ 2) / 8)) * (c * (1 / d ^ 2) * ((1 + ρ) * (1 + r))) := by
        gcongr; nlinarith
    _ = c * C_e * (1 + ρ) * (1 / d ^ 2) *
          (((1 + r) * Real.exp (-(r ^ 2) / 16)) * Real.exp (-(r ^ 2) / 16)) := by
        rw [hsplit]; ring
    _ ≤ c * C_e * (1 + ρ) * (1 / d ^ 2) * (4 * Real.exp (-(r ^ 2) / 16)) := by
        gcongr
    _ = c * C_e * (1 + ρ) / d ^ 2 * (4 * Real.exp (-(r ^ 2) / 16)) := by ring

/-- The far set `{|z| ≥ d/5}` gives the Gaussian factor `e^{-d²/400} ≤ 400/d²`. -/
theorem far_gauss {d : ℝ} (hd : 1 ≤ d) {z : ℝ × ℝ} (hz : ¬ ‖planeToC z‖ < d / 5) :
    Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤
      (400 / d ^ 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
  have hd0 : 0 < d := by linarith
  push_neg at hz
  rw [norm_planeToC_sq' z]
  set r := ‖planeToC z‖
  have hr : (d / 5) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
  have h1 := exp_split (r := r) (ρ := d / 5) hr
  have h2 : Real.exp (-((d / 5) ^ 2) / 16) ≤ 400 / d ^ 2 := by
    have := exp_neg_le_inv (x := d ^ 2 / 400) (by positivity)
    calc Real.exp (-((d / 5) ^ 2) / 16) = Real.exp (-(d ^ 2 / 400)) := by ring_nf
      _ ≤ 1 / (d ^ 2 / 400) := this
      _ = 400 / d ^ 2 := by field_simp
  calc Real.exp (-(r ^ 2) / 8) ≤ Real.exp (-(r ^ 2) / 16) * Real.exp (-((d / 5) ^ 2) / 16) := h1
    _ ≤ Real.exp (-(r ^ 2) / 16) * (400 / d ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (400 / d ^ 2) * Real.exp (-(r ^ 2) / 16) := by ring

/-- Pointwise far-zone bound of the planar term. -/
theorem far_pointwise {d : ℝ} (hd : 1 ≤ d) {e : ℝ × ℝ → ℂ} {C_e : ℝ} (hCe : 0 ≤ C_e)
    (he : ∀ z, ‖e z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) {y : ℝ × ℝ}
    (hy : ‖planeToC y‖ ≤ d / 8) (k : Fin 2) (z : ℝ × ℝ) :
    ‖B0009.kernel k (planeToC (y - z)) * {x : ℝ × ℝ | ‖planeToC x‖ < d / 5}ᶜ.indicator e z‖ ≤
      3 * C_e * (400 / d ^ 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
  have hd0 : 0 < d := by linarith
  by_cases hz : ‖planeToC z‖ < d / 5
  · have hmem : z ∉ {x : ℝ × ℝ | ‖planeToC x‖ < d / 5}ᶜ := by simpa using hz
    rw [indicator_of_notMem hmem, mul_zero, norm_zero]
    positivity
  · have hmem : z ∈ {x : ℝ × ℝ | ‖planeToC x‖ < d / 5}ᶜ := by simpa using hz
    rw [indicator_of_mem hmem, norm_mul]
    have hz' : d / 5 ≤ ‖planeToC z‖ := le_of_not_gt hz
    have hdist : 3 * d / 40 ≤ ‖planeToC (y - z)‖ := by
      rw [planeToC_sub]
      have := norm_sub_norm_le (planeToC z) (planeToC y)
      rw [norm_sub_rev] at this
      linarith
    have hpos : 0 < ‖planeToC (y - z)‖ := lt_of_lt_of_le (by positivity) hdist
    have hk : ‖B0009.kernel k (planeToC (y - z))‖ ≤ 3 := by
      refine (B0009.norm_kernel_le k _).trans ?_
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have hpi := Real.pi_gt_three
      nlinarith
    have hez := (he z).trans (mul_le_mul_of_nonneg_left (far_gauss hd hz) hCe)
    calc ‖B0009.kernel k (planeToC (y - z))‖ * ‖e z‖
        ≤ 3 * (C_e * ((400 / d ^ 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16))) :=
          mul_le_mul hk hez (norm_nonneg _) (by norm_num)
      _ = 3 * C_e * (400 / d ^ 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by ring

theorem jb_far_bound {d : ℝ} (hd : 1 ≤ d) {e : ℝ × ℝ → ℂ} {C_e : ℝ} (hCe : 0 ≤ C_e)
    (he : ∀ z, ‖e z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) (w : ℝ × ℝ) :
    B0579.jb w ^ 2 * ‖{x : ℝ × ℝ | ‖planeToC x‖ < d / 5}ᶜ.indicator e w‖ ≤
      C_e * 1024 * (400 / d ^ 2) := by
  have hd0 : 0 < d := by linarith
  have hj : 0 ≤ B0579.jb w ^ 2 := by positivity
  by_cases hz : ‖planeToC w‖ < d / 5
  · have hmem : w ∉ {x : ℝ × ℝ | ‖planeToC x‖ < d / 5}ᶜ := by simpa using hz
    rw [indicator_of_notMem hmem, norm_zero, mul_zero]
    positivity
  · have hmem : w ∈ {x : ℝ × ℝ | ‖planeToC x‖ < d / 5}ᶜ := by simpa using hz
    rw [indicator_of_mem hmem]
    have hez := (he w).trans (mul_le_mul_of_nonneg_left (far_gauss hd hz) hCe)
    have hJ := jb_sq_exp_le w
    calc B0579.jb w ^ 2 * ‖e w‖
        ≤ B0579.jb w ^ 2 * (C_e * ((400 / d ^ 2) * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16))) :=
          mul_le_mul_of_nonneg_left hez hj
      _ = C_e * (400 / d ^ 2) * (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) := by
          ring
      _ ≤ C_e * (400 / d ^ 2) * 1024 := mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = C_e * 1024 * (400 / d ^ 2) := by ring

theorem exp8_le_exp16 (z : ℝ × ℝ) :
    Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
  apply Real.exp_le_exp.2
  have : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
  linarith

theorem jb_gauss_bound {e : ℝ × ℝ → ℂ} {C_e : ℝ} (hCe : 0 ≤ C_e)
    (he : ∀ z, ‖e z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) (w : ℝ × ℝ) :
    B0579.jb w ^ 2 * ‖e w‖ ≤ C_e * 1024 := by
  have hj : 0 ≤ B0579.jb w ^ 2 := by positivity
  calc B0579.jb w ^ 2 * ‖e w‖
      ≤ B0579.jb w ^ 2 * (C_e * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) :=
        mul_le_mul_of_nonneg_left ((he w).trans
          (mul_le_mul_of_nonneg_left (exp8_le_exp16 w) hCe)) hj
    _ = C_e * (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) := by ring
    _ ≤ C_e * 1024 := mul_le_mul_of_nonneg_left (jb_sq_exp_le w) hCe

/-- **Cylinder versus planar velocity** (SP 2875-2888). -/
theorem vel_compare :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ {e W : ℝ × ℝ → ℂ} {C_e T : ℝ}, 0 ≤ C_e → 0 ≤ T →
      Continuous e → Continuous W →
      (∀ z, ‖e z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) →
      (∀ z ∈ B0579.cell d, ‖W z - e z‖ ≤ T / d ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) →
      ∀ (y : ℝ × ℝ) (k : Fin 2), ‖planeToC y‖ ≤ d / 8 →
        ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ ≤
          K * (T + C_e) * (1 + ‖planeToC y‖) / d ^ 2 := by
  obtain ⟨C_K, hCK, hKer⟩ := cellKer_bound
  set I16 : ℝ := ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) with hI16
  have hI16_nn : 0 ≤ I16 := integral_nonneg (fun z => (Real.exp_pos _).le)
  have hG16 : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) :=
    integrable_gauss (by norm_num)
  set c := IIb.pairedImageConst with hc
  have hc0 : 0 ≤ c := IIb.pairedImageConst_pos.le
  set K : ℝ := C_K * 1024 + C_K * 409600 + 4 * c * I16 + 1200 * I16 with hK
  refine ⟨K, by positivity, fun {d} hd {e W} {C_e T} hCe hT he_c hW_c he hWe y k hy => ?_⟩
  have hd0 : 0 < d := by linarith
  set N : Set (ℝ × ℝ) := {x : ℝ × ℝ | ‖planeToC x‖ < d / 5} with hNdef
  have hN_meas : MeasurableSet N :=
    measurableSet_lt (continuous_norm.comp continuous_planeToC).measurable measurable_const
  have hN_cell : N ⊆ B0579.cell d := by
    intro z hz
    simp only [hNdef, mem_setOf_eq] at hz
    have h1 : |z.1| ≤ ‖planeToC z‖ := by
      have := Complex.abs_re_le_norm (planeToC z)
      simpa [planeToC] using this
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
    constructor <;> [linarith [neg_abs_le z.1]; linarith [le_abs_self z.1]]
  set eN : ℝ × ℝ → ℂ := N.indicator e with heN
  set eF : ℝ × ℝ → ℂ := Nᶜ.indicator e with heF
  have hsplit : ∀ z, e z = eN z + eF z := fun z => (indicator_self_add_compl_apply N e z).symm
  -- jb-bounds of the sources on the cell
  have hjbWe : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖W w - e w‖ ≤ T * 1024 / d ^ 2 := by
    intro w hw
    have hj : 0 ≤ B0579.jb w ^ 2 := by positivity
    calc B0579.jb w ^ 2 * ‖W w - e w‖
        ≤ B0579.jb w ^ 2 * (T / d ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) :=
          mul_le_mul_of_nonneg_left (hWe w hw) hj
      _ = T / d ^ 2 * (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) := by ring
      _ ≤ T / d ^ 2 * 1024 := mul_le_mul_of_nonneg_left (jb_sq_exp_le w) (by positivity)
      _ = T * 1024 / d ^ 2 := by ring
  have hjbN : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖eN w‖ ≤ C_e * 1024 := by
    intro w _
    have hle : ‖eN w‖ ≤ ‖e w‖ := norm_indicator_le_norm_self e w
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans (jb_gauss_bound hCe he w)
  have hjbF : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖eF w‖ ≤ C_e * 1024 * (400 / d ^ 2) :=
    fun w _ => jb_far_bound hd hCe he w
  have hjbE : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖e w‖ ≤ C_e * 1024 :=
    fun w _ => jb_gauss_bound hCe he w
  have hm_We : AEStronglyMeasurable (fun w => W w - e w) (volume.restrict (B0579.cell d)) :=
    (hW_c.sub he_c).aestronglyMeasurable
  have hm_e : AEStronglyMeasurable e (volume.restrict (B0579.cell d)) :=
    he_c.aestronglyMeasurable
  have hm_eN : AEStronglyMeasurable eN (volume.restrict (B0579.cell d)) :=
    he_c.aestronglyMeasurable.indicator hN_meas
  have hm_eF : AEStronglyMeasurable eF (volume.restrict (B0579.cell d)) :=
    he_c.aestronglyMeasurable.indicator hN_meas.compl
  obtain ⟨hI_We, hB_We⟩ := hKer hd (by positivity) hm_We hjbWe y k
  obtain ⟨hI_eN, -⟩ := hKer hd (by positivity) hm_eN hjbN y k
  obtain ⟨hI_eF, hB_eF⟩ := hKer hd (by positivity) hm_eF hjbF y k
  obtain ⟨hI_e, -⟩ := hKer hd (by positivity) hm_e hjbE y k
  -- planar integrability
  have he_sup : ∀ z, ‖e z‖ ≤ C_e := fun z =>
    (he z).trans (mul_le_of_le_one_right hCe (Real.exp_le_one_iff.2 (by
      have : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
      linarith)))
  have he_int : Integrable e :=
    Integrable.mono' ((integrable_gauss (a := 8) (by norm_num)).const_mul C_e)
      he_c.aestronglyMeasurable (Eventually.of_forall he)
  have hP : Integrable (fun z => B0009.kernel k (planeToC (y - z)) * e z) := integrable_kernel_planar he_c he_sup he_int k y
  have hPN : Integrable (fun z => B0009.kernel k (planeToC (y - z)) * eN z) := by
    refine (hP.indicator hN_meas).congr (Eventually.of_forall fun z => ?_)
    simp only [heN]
    exact indicator_mul_right N (fun z => B0009.kernel k (planeToC (y - z))) e
  have hPF : Integrable (fun z => B0009.kernel k (planeToC (y - z)) * eF z) := by
    refine (hP.indicator hN_meas.compl).congr (Eventually.of_forall fun z => ?_)
    simp only [heF]
    exact indicator_mul_right Nᶜ (fun z => B0009.kernel k (planeToC (y - z))) e
  -- decompositions
  have hI_NF : IntegrableOn (fun z => eN z * ((kerD d (y - z) k : ℝ) : ℂ) +
      eF z * ((kerD d (y - z) k : ℝ) : ℂ)) (B0579.cell d) := hI_eN.add hI_eF
  have hV : kerVelCx d W y k = (∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)) +
      ((∫ z in B0579.cell d, eN z * ((kerD d (y - z) k : ℝ) : ℂ)) +
        ∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)) := by
    unfold kerVelCx
    have h1 : ∫ z in B0579.cell d, W z * ((kerD d (y - z) k : ℝ) : ℂ) =
        ∫ z in B0579.cell d, ((W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ) +
          (eN z * ((kerD d (y - z) k : ℝ) : ℂ) + eF z * ((kerD d (y - z) k : ℝ) : ℂ))) := by
      congr 1
      funext z
      rw [hsplit z]
      ring
    rw [h1, integral_add hI_We hI_NF, integral_add hI_eN hI_eF]
  have hU : kerVelPlanarCx e y k = (∫ z, B0009.kernel k (planeToC (y - z)) * eN z) +
      ∫ z, B0009.kernel k (planeToC (y - z)) * eF z := by
    rw [kerVelPlanarCx_eq, ← integral_add hPN hPF]
    congr 1
    funext z
    rw [hsplit z]
    ring
  have hN1 : ∫ z in B0579.cell d, eN z * ((kerD d (y - z) k : ℝ) : ℂ) = ∫ z in N, e z * ((kerD d (y - z) k : ℝ) : ℂ) := by
    have : (fun z => eN z * ((kerD d (y - z) k : ℝ) : ℂ)) = N.indicator (fun z => e z * ((kerD d (y - z) k : ℝ) : ℂ)) := by
      funext z; simp only [heN]; exact (indicator_mul_left N e (fun z => ((kerD d (y - z) k : ℝ) : ℂ))).symm
    rw [this, setIntegral_indicator hN_meas, inter_eq_right.2 hN_cell]
  have hN2 : ∫ z, B0009.kernel k (planeToC (y - z)) * eN z = ∫ z in N, B0009.kernel k (planeToC (y - z)) * e z := by
    have : (fun z => B0009.kernel k (planeToC (y - z)) * eN z) = N.indicator (fun z => B0009.kernel k (planeToC (y - z)) * e z) := by
      funext z; simp only [heN]; exact (indicator_mul_right N (fun z => B0009.kernel k (planeToC (y - z))) e).symm
    rw [this, integral_indicator hN_meas]
  have hIN1 : IntegrableOn (fun z => e z * ((kerD d (y - z) k : ℝ) : ℂ)) N := hI_e.mono_set hN_cell
  have hIN2 : IntegrableOn (fun z => B0009.kernel k (planeToC (y - z)) * e z) N := hP.integrableOn
  have hdiffN : (∫ z in N, e z * ((kerD d (y - z) k : ℝ) : ℂ)) - ∫ z in N, B0009.kernel k (planeToC (y - z)) * e z =
      ∫ z in N, (e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z) := (integral_sub hIN1 hIN2).symm
  -- the four bounds
  have hq : 0 < 1 / d ^ 2 := by positivity
  have b1 : ‖∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)‖ ≤ C_K * 1024 * T * (1 / d ^ 2) := by
    refine hB_We.trans (le_of_eq ?_); ring
  have b2 : ‖∫ z in N, (e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z)‖ ≤
      4 * c * I16 * C_e * (1 + ‖planeToC y‖) * (1 / d ^ 2) := by
    set g : ℝ × ℝ → ℝ := fun z : ℝ × ℝ => c * C_e * (1 + ‖planeToC y‖) / d ^ 2 *
      (4 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) with hg
    have hg_int : Integrable g := (hG16.const_mul 4).const_mul _
    have hg_nn : 0 ≤ᵐ[volume] g := Eventually.of_forall fun z => by
      simp only [hg, Pi.zero_apply]; positivity
    have h1 : ‖∫ z in N, (e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z)‖ ≤ ∫ z in N, g z :=
      norm_integral_le_of_norm_le hg_int.integrableOn
        (ae_restrict_of_forall_mem hN_meas fun z hz => near_pointwise hd hCe he hy hz k)
    have h2 : ∫ z in N, g z ≤ ∫ z, g z := setIntegral_le_integral hg_int hg_nn
    have h3 : ∫ z, g z = 4 * c * I16 * C_e * (1 + ‖planeToC y‖) * (1 / d ^ 2) := by
      simp only [hg]
      rw [integral_const_mul, integral_const_mul]
      ring
    linarith
  have b3 : ‖∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)‖ ≤ C_K * 409600 * C_e * (1 / d ^ 2) := by
    refine hB_eF.trans (le_of_eq ?_); ring
  have b4 : ‖∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ ≤ 1200 * I16 * C_e * (1 / d ^ 2) := by
    have h1 : ‖∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ ≤
        ∫ z : ℝ × ℝ, 3 * C_e * (400 / d ^ 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) :=
      norm_integral_le_of_norm_le (hG16.const_mul _)
        (Eventually.of_forall fun z => far_pointwise hd hCe he hy k z)
    rw [integral_const_mul] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  -- assembly
  have hY0 : 0 ≤ ‖planeToC y‖ := norm_nonneg _
  have heq : kerVelCx d W y k - kerVelPlanarCx e y k =
      (∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)) +
        (∫ z in N, (e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z)) +
        (∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)) - ∫ z, B0009.kernel k (planeToC (y - z)) * eF z := by
    rw [hV, hU, hN1, hN2, ← hdiffN]
    ring
  rw [heq]
  have htri : ‖(∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)) +
        (∫ z in N, (e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z)) +
        (∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)) - ∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ ≤
      ‖∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)‖ + ‖∫ z in N, (e z * ((kerD d (y - z) k : ℝ) : ℂ) - B0009.kernel k (planeToC (y - z)) * e z)‖ +
        ‖∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)‖ + ‖∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  refine htri.trans ?_
  have hfin : K * (T + C_e) * (1 + ‖planeToC y‖) / d ^ 2 =
      K * (T + C_e) * (1 + ‖planeToC y‖) * (1 / d ^ 2) := by ring
  rw [hfin]
  have hX : C_K * 1024 * T * (1 / d ^ 2) + 4 * c * I16 * C_e * (1 + ‖planeToC y‖) * (1 / d ^ 2) +
      C_K * 409600 * C_e * (1 / d ^ 2) + 1200 * I16 * C_e * (1 / d ^ 2) ≤
      K * (T + C_e) * (1 + ‖planeToC y‖) * (1 / d ^ 2) := by
    rw [hK]
    have h1 : 0 ≤ C_K * 1024 * T * ‖planeToC y‖ := by positivity
    have h2 : 0 ≤ C_K * 409600 * C_e * ‖planeToC y‖ := by positivity
    have h3 : 0 ≤ 1200 * I16 * C_e * ‖planeToC y‖ := by positivity
    have h4 : 0 ≤ (C_K * 409600 + 4 * c * I16 + 1200 * I16) * T * (1 + ‖planeToC y‖) := by
      positivity
    have h5 : 0 ≤ C_K * 1024 * C_e * (1 + ‖planeToC y‖) := by positivity
    have hsum : C_K * 1024 * T + 4 * c * I16 * C_e * (1 + ‖planeToC y‖) +
        C_K * 409600 * C_e + 1200 * I16 * C_e ≤
        (C_K * 1024 + C_K * 409600 + 4 * c * I16 + 1200 * I16) * (T + C_e) *
          (1 + ‖planeToC y‖) := by
      nlinarith
    have := mul_le_mul_of_nonneg_right hsum hq.le
    linarith
  linarith

end EulerErrorTail

end UnforcedLeray.Short.IIIa
