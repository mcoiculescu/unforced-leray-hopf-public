import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.WeightGrad
import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.WeightedCS

/-!
# `PartIII-a:T21/2/7/2/1/1/5`: the interpolation inequality for smooth periodic fields (`CellInterpSmooth`)

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3050.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Calculus of `pdCx` -/

theorem cie_pdCx_mul (k : Fin 2) {u v : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (x : ℝ × ℝ) :
    pdCx k (fun y => u y * v y) x = pdCx k u x * v x + u x * pdCx k v x := by
  unfold pdCx
  rw [show fderiv ℝ (fun y => u y * v y) x = _ from ((hu x).hasFDerivAt.mul (hv x).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem cie_pdCx_ofReal (k : Fin 2) {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (x : ℝ × ℝ) :
    pdCx k (fun y => ((φ y : ℝ) : ℂ)) x = ((B0579.pd k φ x : ℝ) : ℂ) := by
  unfold pdCx B0579.pd
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x (hφ x).hasFDerivAt).fderiv
  rw [show (fun y => ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h]
  simp

theorem cie_pdCx_conj (k : Fin 2) {u : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u) (x : ℝ × ℝ) :
    pdCx k (fun y => (starRingEnd ℂ) (u y)) x = (starRingEnd ℂ) (pdCx k u x) := by
  unfold pdCx
  have h := (hu x).hasFDerivAt.star.fderiv
  rw [show (fun y => (starRingEnd ℂ) (u y)) = (fun y => star (u y)) from rfl, h]
  simp [Complex.star_def]

theorem cie_pdCx_periodic (k : Fin 2) {c : ℝ} (Φ : ℝ × ℝ → ℂ)
    (hper : ∀ x : ℝ × ℝ, Φ (x.1 + c, x.2) = Φ x) :
    ∀ x : ℝ × ℝ, pdCx k Φ (x.1 + c, x.2) = pdCx k Φ x := by
  intro x
  have hfun : (fun y : ℝ × ℝ => Φ (y + ((c, 0) : ℝ × ℝ))) = Φ := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have h1 : fderiv ℝ (fun y : ℝ × ℝ => Φ (y + ((c, 0) : ℝ × ℝ))) x
      = fderiv ℝ Φ (x + ((c, 0) : ℝ × ℝ)) := fderiv_comp_add_right _
  rw [hfun] at h1
  have hx : (x.1 + c, x.2) = x + ((c, 0) : ℝ × ℝ) := by ext <;> simp
  unfold pdCx
  rw [hx, ← h1]

theorem cie_contDiff_pdCx {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k F) := by
  unfold pdCx
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ## The weight `⟨x⟩^{-2m}` -/

theorem cie_contDiff_w (m : ℝ) : ContDiff ℝ ∞ (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) := by
  have hj : ContDiff ℝ ∞ (fun y : ℝ × ℝ => B0579.jb y) := by
    unfold B0579.jb
    fun_prop
  exact hj.rpow_const_of_ne (fun y => (B0579.jb_pos y).ne')

theorem cie_contDiff_wc (m : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((B0579.jb y ^ (-m) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (cie_contDiff_w m)

/-- The product rule for the integrand `G = w F conj(∂_j F)` of the integration by parts. -/
theorem cie_pdCx_G (m : ℝ) (j : Fin 2) {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x : ℝ × ℝ) :
    pdCx j (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (pdCx j F y)) x
      = ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j F x)
        + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx j F x * (starRingEnd ℂ) (pdCx j F x)
        + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j (pdCx j F) x) := by
  have hwd : Differentiable ℝ (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) :=
    (cie_contDiff_w m).differentiable (by simp)
  have hwcd : Differentiable ℝ (fun y : ℝ × ℝ => ((B0579.jb y ^ (-m) : ℝ) : ℂ)) :=
    (cie_contDiff_wc m).differentiable (by simp)
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hdF : Differentiable ℝ (pdCx j F) := (cie_contDiff_pdCx hF j).differentiable (by simp)
  have hcdF : Differentiable ℝ (fun y => (starRingEnd ℂ) (pdCx j F y)) := by
    intro y
    exact ((hdF y).hasFDerivAt.star).differentiableAt
  have hwF : Differentiable ℝ (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y) :=
    hwcd.mul hFd
  have h1 := cie_pdCx_mul j hwF hcdF x
  have h2 := cie_pdCx_mul j hwcd hFd x
  have h3 := cie_pdCx_ofReal j hwd x
  have h4 := cie_pdCx_conj j hdF x
  rw [h1, h2, h3, h4]
  ring

/-! ## Integrability on the cell and the weighted norms -/

/-- Integrability with respect to the cell measure transfers to the Lebesgue integrability of the
weighted function on the cell. -/
theorem cie_integrable_weight {c m : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : Integrable k (B0579.cellMeasure c (-m))) :
    Integrable (fun x => B0579.jb x ^ (-m) * k x) (volume.restrict (B0579.cell c)) := by
  unfold B0579.cellMeasure at hk
  have hmeas : Measurable (fun x => ((B0579.density (-m) x : ℝ≥0) : ℝ≥0∞)) :=
    (B0579.measurable_density (-m)).coe_nnreal_ennreal
  have hfin : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ((B0579.density (-m) x : ℝ≥0) : ℝ≥0∞) < ⊤ :=
    ae_of_all _ fun x => ENNReal.coe_lt_top
  have h := (integrable_withDensity_iff_integrable_smul' hmeas hfin).1 hk
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [B0579.coe_density, smul_eq_mul]

/-- A pointwise domination by a weighted product of two `X_{-m,c}` fields gives integrability on
the cell. -/
theorem cie_int_dom {c m : ℝ} {h u v : ℝ × ℝ → ℂ} {C : ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (B0579.cell c)))
    (hu : MemLp u 2 (B0579.cellMeasure c (-m))) (hv : MemLp v 2 (B0579.cellMeasure c (-m)))
    (hC : ∀ x, ‖h x‖ ≤ C * (B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖))) :
    IntegrableOn h (B0579.cell c) := by
  have hk : Integrable (fun x => ‖u x‖ * ‖v x‖) (B0579.cellMeasure c (-m)) :=
    hu.norm.integrable_mul hv.norm
  have hdom := (cie_integrable_weight hk).const_mul C
  exact hdom.mono' hh (ae_of_all _ fun x => hC x)

/-- The integral against the weighted measure, for an arbitrary weight exponent. -/
theorem cie_integral_cellMeasure (c p : ℝ) (u : ℝ × ℝ → ℝ) :
    ∫ x, u x ∂(B0579.cellMeasure c p) = ∫ x in B0579.cell c, B0579.jb x ^ p * u x := by
  unfold B0579.cellMeasure
  rw [integral_withDensity_eq_integral_smul (B0579.measurable_density p)]
  simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]

/-- `‖u‖²_{X_{p,c}} = ∫_{C_c} ⟨x⟩^{p} |u|²`. -/
theorem cie_xNorm_sq (c p : ℝ) {u : ℝ × ℝ → ℂ} (hu : MemLp u 2 (B0579.cellMeasure c p)) :
    (xNorm c p u) ^ 2 = ENNReal.ofReal (∫ x in B0579.cell c, B0579.jb x ^ p * ‖u x‖ ^ 2) := by
  have hsq : Integrable (fun x => ‖u x‖ ^ 2) (B0579.cellMeasure c p) := hu.norm.integrable_sq
  have hnn : 0 ≤ᵐ[B0579.cellMeasure c p] (fun x => ‖u x‖ ^ 2) :=
    ae_of_all _ fun x => sq_nonneg _
  have hI := ofReal_integral_eq_lintegral_ofReal hsq hnn
  have e := cie_integral_cellMeasure c p (fun x => ‖u x‖ ^ 2)
  rw [e] at hI
  rw [hI]
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The weighted Cauchy-Schwarz inequality on the cell, for real values:
`∫_{C_c} ⟨x⟩^{-m} |u||v| ≤ ‖v‖_{X_{-m,c}} ‖u‖_{X_{-m,c}}`. -/
theorem cie_cs_real {c m : ℝ} {u v : ℝ × ℝ → ℂ} (hu : MemLp u 2 (B0579.cellMeasure c (-m)))
    (hv : MemLp v 2 (B0579.cellMeasure c (-m))) :
    ∫ x in B0579.cell c, B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖) ≤
      (xNorm c (-m) v).toReal * (xNorm c (-m) u).toReal := by
  have hw : Continuous fun x : ℝ × ℝ => B0579.jb x ^ (-m) := B0579.continuous_jb_rpow _
  have hAu : AEStronglyMeasurable (fun x => ‖u x‖) (volume.restrict (B0579.cell c)) :=
    (hu.aestronglyMeasurable.norm).mono_ac (B0579.ac_cellMeasure c (-m))
  have hAv : AEStronglyMeasurable (fun x => ‖v x‖) (volume.restrict (B0579.cell c)) :=
    (hv.aestronglyMeasurable.norm).mono_ac (B0579.ac_cellMeasure c (-m))
  have hB : AEStronglyMeasurable (fun x => B0579.jb x ^ (-m) * ‖u x‖)
      (volume.restrict (B0579.cell c)) :=
    (hw.aestronglyMeasurable.mul hAu)
  have hBm : AEStronglyMeasurable (fun x => B0579.jb x ^ (-m) * ‖u x‖) (B0579.cellMeasure c m) :=
    hB.mono_ac (B0579.cellMeasure_ac c m)
  have hCS := weightedCS c m v (fun x => B0579.jb x ^ (-m) * ‖u x‖)
    (hv.aestronglyMeasurable) hBm
  -- the weighted norm of `B` is the norm of `u` on `X_{-m,c}`
  have hEq : eLpNorm (fun x => B0579.jb x ^ (-m) * ‖u x‖) 2 (B0579.cellMeasure c m) =
      xNorm c (-m) u := by
    unfold xNorm
    rw [B0579.eLpNorm_cellMeasure c m, eLpNorm_cellMeasure_cx]
    have hr : ∀ x, B0579.jb x ^ (m / 2) * (B0579.jb x ^ (-m) * ‖u x‖)
        = ‖((B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) * u x‖ := by
      intro x
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
      have h2 : B0579.jb x ^ (m / 2) * B0579.jb x ^ (-m) = B0579.jb x ^ ((-m) / 2) := by
        rw [← Real.rpow_add (B0579.jb_pos x)]
        congr 1
        ring
      rw [← mul_assoc, h2]
    rw [show (fun x => B0579.jb x ^ (m / 2) * (B0579.jb x ^ (-m) * ‖u x‖))
        = fun x => ‖((B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) * u x‖ from funext hr]
    exact eLpNorm_norm _
  rw [hEq] at hCS
  have hpt : ∀ x, ENNReal.ofReal (B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)) =
      ‖v x‖ₑ * ‖B0579.jb x ^ (-m) * ‖u x‖‖ₑ := by
    intro x
    have hw0 : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg (B0579.jb_pos x).le _
    rw [Real.enorm_of_nonneg (mul_nonneg hw0 (norm_nonneg _)), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    ring
  have h0 : 0 ≤ᵐ[volume.restrict (B0579.cell c)]
      (fun x => B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)) :=
    ae_of_all _ fun x => mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hfm : AEStronglyMeasurable (fun x => B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖))
      (volume.restrict (B0579.cell c)) :=
    hw.aestronglyMeasurable.mul (hAu.mul hAv)
  have hvfin : xNorm c (-m) v ≠ ⊤ := hv.eLpNorm_lt_top.ne
  have hufin : xNorm c (-m) u ≠ ⊤ := hu.eLpNorm_lt_top.ne
  calc ∫ x in B0579.cell c, B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)
      = (∫⁻ x in B0579.cell c, ‖v x‖ₑ * ‖B0579.jb x ^ (-m) * ‖u x‖‖ₑ).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae h0 hfm]
        congr 1
        exact lintegral_congr hpt
    _ ≤ (xNorm c (-m) v * xNorm c (-m) u).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hvfin hufin) hCS
    _ = (xNorm c (-m) v).toReal * (xNorm c (-m) u).toReal := ENNReal.toReal_mul

/-! ## Smoothness, derivatives along the coordinate lines, and the cell integrations by parts -/

theorem cie_contDiff_pdR {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : Fin 2) :
    ContDiff ℝ ∞ (fun y => ((B0579.pd k φ y : ℝ) : ℂ)) := by
  unfold B0579.pd
  exact Complex.ofRealCLM.contDiff.comp ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem cie_contDiff_G (m : ℝ) (j : Fin 2) {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (pdCx j F y)) :=
  ((cie_contDiff_wc m).mul hF).mul (Complex.conjCLE.contDiff.comp (cie_contDiff_pdCx hF j))

theorem cie_cancel {c : ℝ} (H : ℝ × ℝ → ℂ) (hH : ∀ x : ℝ × ℝ, H (x.1 + c, x.2) = H x) (η : ℝ) :
    H (c / 2, η) = H (-c / 2, η) := by
  have h := hH (-c / 2, η)
  dsimp only at h
  rw [show -c / 2 + c = c / 2 by ring] at h
  exact h

theorem cie_hasDerivAt_q {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (q η : ℝ) : HasDerivAt (fun q' => F (q', η)) (pdCx 0 F (q, η)) q := by
  have hl : HasDerivAt (fun q' : ℝ => ((q', η) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
  have h := ((hF.differentiable (by simp)) (q, η)).hasFDerivAt.comp_hasDerivAt q hl
  unfold pdCx
  have e : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]
  rw [e]
  exact h

theorem cie_hasDerivAt_eta {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (q η : ℝ) :
    HasDerivAt (fun η' => F (q, η')) (pdCx 1 F (q, η)) η := by
  have hl : HasDerivAt (fun η' : ℝ => ((q, η') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
  have h := ((hF.differentiable (by simp)) (q, η)).hasFDerivAt.comp_hasDerivAt η hl
  unfold pdCx
  have e : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]
  rw [e]
  exact h

theorem cie_cell_eq (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

/-- The pointwise norm bound of the three terms of the product rule. -/
theorem cie_norm_bound_T1 (m : ℝ) (j : Fin 2) {F : ℝ × ℝ → ℂ} (x : ℝ × ℝ) :
    ‖((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j F x)‖
      ≤ 2 * |m| * (B0579.jb x ^ (-m) * (‖F x‖ * ‖pdCx j F x‖)) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  have hp : |B0579.pd j (fun y => B0579.jb y ^ (-m)) x| ≤ 2 * |m| * B0579.jb x ^ (-m) :=
    adjWeightGrad m x j
  have h0 : 0 ≤ ‖F x‖ * ‖pdCx j F x‖ := by positivity
  calc |B0579.pd j (fun y => B0579.jb y ^ (-m)) x| * ‖F x‖ * ‖pdCx j F x‖
      = |B0579.pd j (fun y => B0579.jb y ^ (-m)) x| * (‖F x‖ * ‖pdCx j F x‖) := by ring
    _ ≤ (2 * |m| * B0579.jb x ^ (-m)) * (‖F x‖ * ‖pdCx j F x‖) :=
        mul_le_mul_of_nonneg_right hp h0
    _ = 2 * |m| * (B0579.jb x ^ (-m) * (‖F x‖ * ‖pdCx j F x‖)) := by ring

theorem cie_norm_bound_prod (m : ℝ) {u v : ℝ × ℝ → ℂ} (x : ℝ × ℝ) :
    ‖((B0579.jb x ^ (-m) : ℝ) : ℂ) * u x * (starRingEnd ℂ) (v x)‖
      ≤ 1 * (B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)) := by
  rw [one_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _), Complex.norm_conj]
  exact le_of_eq (by ring)

/-- Integrability of the weighted product `⟨x⟩^{-m} ‖u‖ ‖v‖` on the cell. -/
theorem cie_integrable_wprod {c m : ℝ} {u v : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (B0579.cellMeasure c (-m))) (hv : MemLp v 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn (fun x => B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)) (B0579.cell c) :=
  cie_integrable_weight (hu.norm.integrable_mul hv.norm)

theorem cie_ibp_q {c : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hint : IntegrableOn (pdCx 0 G) (B0579.cell c))
    (hz : ∀ η : ℝ, G (c / 2, η) = G (-c / 2, η)) :
    ∫ x in B0579.cell c, pdCx 0 G x = 0 := by
  rw [cie_cell_eq c] at hint ⊢
  have key := UnforcedLeray.Cyl.integral_cell_deriv_q (F := G) (F' := pdCx 0 G) hc
    (fun q η => cie_hasDerivAt_q hG q η) hint
  rw [key]
  simp only [hz, sub_self, integral_zero]

theorem cie_ibp_eta {c : ℝ} {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGi : IntegrableOn G (B0579.cell c)) (hint : IntegrableOn (pdCx 1 G) (B0579.cell c)) :
    ∫ x in B0579.cell c, pdCx 1 G x = 0 := by
  rw [cie_cell_eq c] at hGi hint ⊢
  exact UnforcedLeray.Cyl.integral_cell_deriv_eta (F := G) (F' := pdCx 1 G)
    (fun q η => cie_hasDerivAt_eta hG q η) hGi hint

/-- **The interpolation inequality for smooth periodic fields** (SP 3044-3050). -/
theorem cellInterpSmooth : UnforcedLeray.Short.IIIa.CellInterpSmooth := by
  intro c m j F hc hF hFper hmem
  have hFC : ContDiff ℝ ∞ F := hF
  have hdF : ContDiff ℝ ∞ (pdCx j F) := cie_contDiff_pdCx hF j
  have hddF : ContDiff ℝ ∞ (pdCx j (pdCx j F)) := cie_contDiff_pdCx hdF j
  have hF0 : MemLp F 2 (B0579.cellMeasure c (-m)) := by simpa [adjSpatial] using hmem []
  have hF1 : MemLp (pdCx j F) 2 (B0579.cellMeasure c (-m)) := by
    simpa [adjSpatial] using hmem [j]
  have hF2 : MemLp (pdCx j (pdCx j F)) 2 (B0579.cellMeasure c (-m)) := by
    simpa [adjSpatial] using hmem [j, j]
  have hcG := cie_contDiff_G m j hFC
  -- integrability of `G` and of the three terms of its derivative
  have hGint : IntegrableOn (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y *
      (starRingEnd ℂ) (pdCx j F y)) (B0579.cell c) :=
    cie_int_dom (C := 1) (hcG.continuous.aestronglyMeasurable)
      hF0 hF1 (fun x => cie_norm_bound_prod m x)
  have hT2 : IntegrableOn (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * pdCx j F y *
      (starRingEnd ℂ) (pdCx j F y)) (B0579.cell c) :=
    cie_int_dom (C := 1)
      (((cie_contDiff_wc m).continuous.mul hdF.continuous).mul
        (Complex.continuous_conj.comp hdF.continuous)).aestronglyMeasurable
      hF1 hF1 (fun x => cie_norm_bound_prod m x)
  have hT3 : IntegrableOn (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y *
      (starRingEnd ℂ) (pdCx j (pdCx j F) y)) (B0579.cell c) :=
    cie_int_dom (C := 1)
      (((cie_contDiff_wc m).continuous.mul hFC.continuous).mul
        (Complex.continuous_conj.comp hddF.continuous)).aestronglyMeasurable
      hF0 hF2 (fun x => cie_norm_bound_prod m x)
  have hT1 : IntegrableOn (fun y => ((B0579.pd j (fun y => B0579.jb y ^ (-m)) y : ℝ) : ℂ) *
      F y * (starRingEnd ℂ) (pdCx j F y)) (B0579.cell c) :=
    cie_int_dom (C := 2 * |m|)
      (((cie_contDiff_pdR (cie_contDiff_w m) j).continuous.mul hFC.continuous).mul
        (Complex.continuous_conj.comp hdF.continuous)).aestronglyMeasurable
      hF0 hF1 (fun x => cie_norm_bound_T1 m j x)
  have hGd : IntegrableOn (pdCx j (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y *
      (starRingEnd ℂ) (pdCx j F y))) (B0579.cell c) := by
    have e : pdCx j (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y *
        (starRingEnd ℂ) (pdCx j F y)) = fun x =>
        ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
          (starRingEnd ℂ) (pdCx j F x)
        + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx j F x * (starRingEnd ℂ) (pdCx j F x)
        + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j (pdCx j F) x) :=
      funext fun x => cie_pdCx_G m j hFC x
    rw [e]
    exact (hT1.add hT2).add hT3
  -- the integration by parts on the cell: `∫_{C_c} ∂_j G = 0`
  have hibp : ∫ x in B0579.cell c, pdCx j (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y *
      (starRingEnd ℂ) (pdCx j F y)) x = 0 := by
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
    · refine cie_ibp_q hc hcG hGd (fun η => ?_)
      have hjb : B0579.jb (c / 2, η) = B0579.jb (-c / 2, η) := by
        show (1 + (c / 2) ^ 2 + η ^ 2 : ℝ) = 1 + (-c / 2) ^ 2 + η ^ 2
        ring
      rw [hjb, cie_cancel F hFper η, cie_cancel (pdCx 0 F) (cie_pdCx_periodic 0 F hFper) η]
    · exact cie_ibp_eta hcG hGint hGd
  -- the real identity of the energy
  set A : ℝ := ∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖pdCx j F x‖ ^ 2 with hA_def
  have hT2eq : ∀ x, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx j F x * (starRingEnd ℂ) (pdCx j F x)
      = ((B0579.jb x ^ (-m) * ‖pdCx j F x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
  have hT2int : ∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx j F x *
      (starRingEnd ℂ) (pdCx j F x) = (A : ℂ) := by
    rw [hA_def, integral_congr_ae (ae_of_all _ hT2eq)]
    exact integral_ofReal
  have hsplitInt : ∫ x in B0579.cell c, pdCx j (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y *
      (starRingEnd ℂ) (pdCx j F y)) x = (∫ x in B0579.cell c,
        ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j F x))
        + (∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx j F x *
          (starRingEnd ℂ) (pdCx j F x))
        + ∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x *
          (starRingEnd ℂ) (pdCx j (pdCx j F) x) := by
    have hT12 : IntegrableOn (fun x => ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) *
        F x * (starRingEnd ℂ) (pdCx j F x) + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx j F x *
          (starRingEnd ℂ) (pdCx j F x)) (B0579.cell c) := hT1.add hT2
    rw [integral_congr_ae (ae_of_all _ fun x => cie_pdCx_G m j hFC x)]
    rw [integral_add hT12 hT3, integral_add hT1 hT2]
  have hzero := hibp
  rw [hsplitInt, hT2int] at hzero
  have hA : (A : ℂ) = -((∫ x in B0579.cell c,
        ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j F x))
        + ∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x *
          (starRingEnd ℂ) (pdCx j (pdCx j F) x)) := by
    linear_combination hzero
  have hnormA : A ≤ (∫ x in B0579.cell c, ‖((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) *
        F x * (starRingEnd ℂ) (pdCx j F x)‖)
      + ∫ x in B0579.cell c, ‖((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x *
          (starRingEnd ℂ) (pdCx j (pdCx j F) x)‖ := by
    have h1 : ‖(A : ℂ)‖ ≤ ‖∫ x in B0579.cell c, ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) *
        F x * (starRingEnd ℂ) (pdCx j F x)‖ + ‖∫ x in B0579.cell c,
        ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j (pdCx j F) x)‖ := by
      rw [hA, norm_neg]
      exact norm_add_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    have e1 := norm_integral_le_integral_norm (μ := volume.restrict (B0579.cell c))
      (fun x => ((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
        (starRingEnd ℂ) (pdCx j F x))
    have e3 := norm_integral_le_integral_norm (μ := volume.restrict (B0579.cell c))
      (fun x => ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx j (pdCx j F) x))
    have := le_abs_self A
    linarith
  -- the two bounds
  have hb1 : ∫ x in B0579.cell c, ‖((B0579.pd j (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) *
        F x * (starRingEnd ℂ) (pdCx j F x)‖
      ≤ 2 * |m| * ((xNorm c (-m) (pdCx j F)).toReal * (xNorm c (-m) F).toReal) := by
    have h := integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
      ((cie_integrable_wprod hF0 hF1).const_mul (2 * |m|))
      (ae_of_all _ fun x => cie_norm_bound_T1 m j x)
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left (cie_cs_real hF0 hF1) (by positivity))
  have hb3 : ∫ x in B0579.cell c, ‖((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x *
        (starRingEnd ℂ) (pdCx j (pdCx j F) x)‖
      ≤ (xNorm c (-m) (pdCx j (pdCx j F))).toReal * (xNorm c (-m) F).toReal := by
    have h := integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
      (cie_integrable_wprod hF0 hF2)
      (ae_of_all _ fun x => (cie_norm_bound_prod (u := F) (v := pdCx j (pdCx j F)) m x).trans_eq
        (one_mul _))
    exact h.trans (cie_cs_real hF0 hF2)
  -- the real inequality
  have hreal : A ≤ 2 * |m| * ((xNorm c (-m) (pdCx j F)).toReal * (xNorm c (-m) F).toReal)
      + (xNorm c (-m) (pdCx j (pdCx j F))).toReal * (xNorm c (-m) F).toReal := by
    linarith
  -- back to the extended reals
  have hFfin : xNorm c (-m) F ≠ ⊤ := hF0.eLpNorm_lt_top.ne
  have hAfin : xNorm c (-m) (pdCx j F) ≠ ⊤ := hF1.eLpNorm_lt_top.ne
  have hCfin : xNorm c (-m) (pdCx j (pdCx j F)) ≠ ⊤ := hF2.eLpNorm_lt_top.ne
  rw [cie_xNorm_sq c (-m) hF1]
  rw [← hA_def]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (xNorm c (-m) (pdCx j F)).toReal := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (xNorm c (-m) F).toReal := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (xNorm c (-m) (pdCx j (pdCx j F))).toReal := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := hb ▸ ENNReal.toReal_nonneg
  have hd0 : 0 ≤ d := hd ▸ ENNReal.toReal_nonneg
  have hxa : xNorm c (-m) (pdCx j F) = ENNReal.ofReal a := by
    rw [ha, ENNReal.ofReal_toReal hAfin]
  have hxb : xNorm c (-m) F = ENNReal.ofReal b := by
    rw [hb, ENNReal.ofReal_toReal hFfin]
  have hxd : xNorm c (-m) (pdCx j (pdCx j F)) = ENNReal.ofReal d := by
    rw [hd, ENNReal.ofReal_toReal hCfin]
  have h2m : (0 : ℝ) ≤ 2 * |m| := by positivity
  have eqR : ENNReal.ofReal b * (ENNReal.ofReal (2 * |m|) * ENNReal.ofReal a
      + ENNReal.ofReal d) = ENNReal.ofReal (b * (2 * |m| * a + d)) := by
    rw [ENNReal.ofReal_mul hb0, ENNReal.ofReal_add (mul_nonneg h2m ha0) hd0,
      ENNReal.ofReal_mul h2m]
  rw [hxa, hxb, hxd, eqR]
  apply ENNReal.ofReal_le_ofReal
  rw [ha, hb, hd] at *
  nlinarith [hreal]

end UnforcedLeray.Short.IIIa
