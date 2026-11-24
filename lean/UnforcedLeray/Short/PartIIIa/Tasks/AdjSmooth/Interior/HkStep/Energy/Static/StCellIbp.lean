import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Algebra
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.WeightGrad
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2/2`: the weighted cell integration by parts (`stCellIbp`)

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3050
(the weight `jb^{-m}` and its logarithmic derivative, `adjWeightGrad`) and 3067-3068 (the
diffusion-weight errors).  With `w = jb^{-m}` and `Φ = w F conj(H)`, the product rule and the
integral of `∂_l Φ` over the cell (`Cyl.integral_cell_deriv_q` / `_eta`) give
`ipX F (∂_l H) + ipX (∂_l F) H = -Re ∫_{C_c} (∂_l w) F conj(H)`, which is bounded by
`2|m| ‖F‖ ‖H‖` (Hölder on the cell).

Helpers are copies of the `CellInterpSmooth` draft (`Tasks/AdjSmooth/Interior/HkStep/CellInterpSmooth.lean`)
under the prefix `sbi_`, plus a complex conversion `sbi_ipX_cell` of the `X_{-m,c}` integral to the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Calculus of `pdCx` -/

theorem sbi_pdCx_mul (k : Fin 2) {u v : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (x : ℝ × ℝ) :
    pdCx k (fun y => u y * v y) x = pdCx k u x * v x + u x * pdCx k v x := by
  unfold pdCx
  rw [show fderiv ℝ (fun y => u y * v y) x = _ from
    ((hu x).hasFDerivAt.mul (hv x).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem sbi_pdCx_ofReal (k : Fin 2) {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (x : ℝ × ℝ) :
    pdCx k (fun y => ((φ y : ℝ) : ℂ)) x = ((B0579.pd k φ x : ℝ) : ℂ) := by
  unfold pdCx B0579.pd
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x (hφ x).hasFDerivAt).fderiv
  rw [show (fun y => ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h]
  simp

theorem sbi_pdCx_conj (k : Fin 2) {u : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u) (x : ℝ × ℝ) :
    pdCx k (fun y => (starRingEnd ℂ) (u y)) x = (starRingEnd ℂ) (pdCx k u x) := by
  unfold pdCx
  have h := (hu x).hasFDerivAt.star.fderiv
  rw [show (fun y => (starRingEnd ℂ) (u y)) = (fun y => star (u y)) from rfl, h]
  simp [Complex.star_def]

theorem sbi_contDiff_pdCx {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k F) := by
  unfold pdCx
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ## The weight `⟨x⟩^{-2m}` -/

theorem sbi_contDiff_w (m : ℝ) : ContDiff ℝ ∞ (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) := by
  have hj : ContDiff ℝ ∞ (fun y : ℝ × ℝ => B0579.jb y) := by
    unfold B0579.jb
    fun_prop
  exact hj.rpow_const_of_ne (fun y => (B0579.jb_pos y).ne')

theorem sbi_contDiff_wc (m : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((B0579.jb y ^ (-m) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (sbi_contDiff_w m)

theorem sbi_contDiff_pdR {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : Fin 2) :
    ContDiff ℝ ∞ (fun y => ((B0579.pd k φ y : ℝ) : ℂ)) := by
  unfold B0579.pd
  exact Complex.ofRealCLM.contDiff.comp
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

/-! ## Integrability on the cell and the weighted norms -/

theorem sbi_integrable_weight {c m : ℝ} {k : ℝ × ℝ → ℝ}
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

theorem sbi_int_dom {c m : ℝ} {h u v : ℝ × ℝ → ℂ} {C : ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (B0579.cell c)))
    (hu : MemLp u 2 (B0579.cellMeasure c (-m))) (hv : MemLp v 2 (B0579.cellMeasure c (-m)))
    (hC : ∀ x, ‖h x‖ ≤ C * (B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖))) :
    IntegrableOn h (B0579.cell c) := by
  have hk : Integrable (fun x => ‖u x‖ * ‖v x‖) (B0579.cellMeasure c (-m)) :=
    hu.norm.integrable_mul hv.norm
  have hdom := (sbi_integrable_weight hk).const_mul C
  exact hdom.mono' hh (ae_of_all _ fun x => hC x)

theorem sbi_integrable_wprod {c m : ℝ} {u v : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (B0579.cellMeasure c (-m))) (hv : MemLp v 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn (fun x => B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)) (B0579.cell c) :=
  sbi_integrable_weight (hu.norm.integrable_mul hv.norm)

/-- The integral against the weighted measure, real valued. -/
theorem sbi_integral_cellMeasure (c p : ℝ) (u : ℝ × ℝ → ℝ) :
    ∫ x, u x ∂(B0579.cellMeasure c p) = ∫ x in B0579.cell c, B0579.jb x ^ p * u x := by
  unfold B0579.cellMeasure
  rw [integral_withDensity_eq_integral_smul (B0579.measurable_density p)]
  simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]

/-- The `X_{-m,c}` inner product integrand, converted to the cell with the weight `jb^{-m}`. -/
theorem sbi_ipX_cell (c m : ℝ) (f g : ℝ × ℝ → ℂ) :
    ∫ x, f x * (starRingEnd ℂ) (g x) ∂(B0579.cellMeasure c (-m)) =
      ∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * f x * (starRingEnd ℂ) (g x) := by
  unfold B0579.cellMeasure
  rw [integral_withDensity_eq_integral_smul (B0579.measurable_density (-m))]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [NNReal.smul_def, B0579.coe_density, Complex.real_smul, mul_assoc]

/-- Hölder on the cell: `∫ ⟨x⟩^{-m} ‖F‖‖H‖ ≤ ‖F‖ ‖H‖` in `X_{-m,c}`. -/
theorem sbi_holder {c m : ℝ} {F H : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c (-m)))
    (hH : MemLp H 2 (B0579.cellMeasure c (-m))) :
    ∫ x, ‖F x‖ * ‖H x‖ ∂(B0579.cellMeasure c (-m)) ≤
      (xNorm c (-m) F).toReal * (xNorm c (-m) H).toReal := by
  have hfn : MemLp (fun x => ‖F x‖) (ENNReal.ofReal 2) (B0579.cellMeasure c (-m)) := by
    rw [ENNReal.ofReal_ofNat]; exact hF.norm
  have hgn : MemLp (fun x => ‖H x‖) (ENNReal.ofReal 2) (B0579.cellMeasure c (-m)) := by
    rw [ENNReal.ofReal_ofNat]; exact hH.norm
  have h3 := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun x => norm_nonneg (F x)) (ae_of_all _ fun x => norm_nonneg (H x)) hfn hgn
  rw [st_integral_sq_rpow hF, st_integral_sq_rpow hH] at h3
  exact h3

/-! ## Pointwise bounds -/

theorem sbi_norm_wFc (m : ℝ) {u v : ℝ × ℝ → ℂ} (x : ℝ × ℝ) :
    ‖((B0579.jb x ^ (-m) : ℝ) : ℂ) * u x * (starRingEnd ℂ) (v x)‖
      ≤ 1 * (B0579.jb x ^ (-m) * (‖u x‖ * ‖v x‖)) := by
  rw [one_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _), Complex.norm_conj]
  exact le_of_eq (by ring)

theorem sbi_norm_T1 (m : ℝ) (l : Fin 2) {F H : ℝ × ℝ → ℂ} (x : ℝ × ℝ) :
    ‖((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (H x)‖
      ≤ 2 * |m| * (B0579.jb x ^ (-m) * (‖F x‖ * ‖H x‖)) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  have hp : |B0579.pd l (fun y => B0579.jb y ^ (-m)) x| ≤ 2 * |m| * B0579.jb x ^ (-m) :=
    adjWeightGrad m x l
  have h0 : 0 ≤ ‖F x‖ * ‖H x‖ := by positivity
  calc |B0579.pd l (fun y => B0579.jb y ^ (-m)) x| * ‖F x‖ * ‖H x‖
      = |B0579.pd l (fun y => B0579.jb y ^ (-m)) x| * (‖F x‖ * ‖H x‖) := by ring
    _ ≤ (2 * |m| * B0579.jb x ^ (-m)) * (‖F x‖ * ‖H x‖) :=
        mul_le_mul_of_nonneg_right hp h0
    _ = 2 * |m| * (B0579.jb x ^ (-m) * (‖F x‖ * ‖H x‖)) := by ring

/-! ## Integrations by parts on the cell -/

theorem sbi_cell_eq (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem sbi_cancel {c : ℝ} (H : ℝ × ℝ → ℂ) (hH : ∀ x : ℝ × ℝ, H (x.1 + c, x.2) = H x) (η : ℝ) :
    H (c / 2, η) = H (-c / 2, η) := by
  have h := hH (-c / 2, η)
  dsimp only at h
  rw [show -c / 2 + c = c / 2 by ring] at h
  exact h

theorem sbi_hasDerivAt_q {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (q η : ℝ) : HasDerivAt (fun q' => F (q', η)) (pdCx 0 F (q, η)) q := by
  have hl : HasDerivAt (fun q' : ℝ => ((q', η) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
  have h := ((hF.differentiable (by simp)) (q, η)).hasFDerivAt.comp_hasDerivAt q hl
  unfold pdCx
  have e : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]
  rw [e]
  exact h

theorem sbi_hasDerivAt_eta {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (q η : ℝ) :
    HasDerivAt (fun η' => F (q, η')) (pdCx 1 F (q, η)) η := by
  have hl : HasDerivAt (fun η' : ℝ => ((q, η') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
  have h := ((hF.differentiable (by simp)) (q, η)).hasFDerivAt.comp_hasDerivAt η hl
  unfold pdCx
  have e : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]
  rw [e]
  exact h

theorem sbi_ibp_q {c : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hint : IntegrableOn (pdCx 0 G) (B0579.cell c))
    (hz : ∀ η : ℝ, G (c / 2, η) = G (-c / 2, η)) :
    ∫ x in B0579.cell c, pdCx 0 G x = 0 := by
  rw [sbi_cell_eq c] at hint ⊢
  have key := UnforcedLeray.Cyl.integral_cell_deriv_q (F := G) (F' := pdCx 0 G) hc
    (fun q η => sbi_hasDerivAt_q hG q η) hint
  rw [key]
  simp only [hz, sub_self, integral_zero]

theorem sbi_ibp_eta {c : ℝ} {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGi : IntegrableOn G (B0579.cell c)) (hint : IntegrableOn (pdCx 1 G) (B0579.cell c)) :
    ∫ x in B0579.cell c, pdCx 1 G x = 0 := by
  rw [sbi_cell_eq c] at hGi hint ⊢
  exact UnforcedLeray.Cyl.integral_cell_deriv_eta (F := G) (F' := pdCx 1 G)
    (fun q η => sbi_hasDerivAt_eta hG q η) hGi hint

/-! ## The leaf `stCellIbp` -/

/-- **(2) Weighted integration by parts on the cell** (SP 3044-3050, 3067-3068). -/
theorem stCellIbp : UnforcedLeray.Short.IIIa.StCellIbp := by
  intro c m l F H hc hF hH hFp hHp hF0 hH0 hF1 hH1
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hHd : Differentiable ℝ H := hH.differentiable (by simp)
  have hdF : ContDiff ℝ ∞ (pdCx l F) := sbi_contDiff_pdCx hF l
  have hdH : ContDiff ℝ ∞ (pdCx l H) := sbi_contDiff_pdCx hH l
  have hwcd : Differentiable ℝ (fun y : ℝ × ℝ => ((B0579.jb y ^ (-m) : ℝ) : ℂ)) :=
    (sbi_contDiff_wc m).differentiable (by simp)
  have hwd : Differentiable ℝ (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) :=
    (sbi_contDiff_w m).differentiable (by simp)
  have hcH : Differentiable ℝ (fun y => (starRingEnd ℂ) (H y)) := by
    intro y
    exact ((hHd y).hasFDerivAt.star).differentiableAt
  have hPhiC : ContDiff ℝ ∞
      (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y)) :=
    ((sbi_contDiff_wc m).mul hF).mul (Complex.conjCLE.contDiff.comp hH)
  -- the product rule for `Φ = w F conj(H)`
  have hPR : ∀ x : ℝ × ℝ,
      pdCx l (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y)) x
        = ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (H x)
          + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx l F x * (starRingEnd ℂ) (H x)
          + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx l H x) := by
    intro x
    have hwF : Differentiable ℝ (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y) :=
      hwcd.mul hFd
    have h1 := sbi_pdCx_mul l hwF hcH x
    have h2 := sbi_pdCx_mul l hwcd hFd x
    have h3 := sbi_pdCx_ofReal l hwd x
    have h4 := sbi_pdCx_conj l hHd x
    rw [h1, h2, h3, h4]
    ring
  -- integrability of `Φ` and of its three terms on the cell
  have hPhiI : IntegrableOn
      (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y))
      (B0579.cell c) :=
    sbi_int_dom (C := 1)
      (((sbi_contDiff_wc m).continuous.mul hF.continuous).mul
        (Complex.continuous_conj.comp hH.continuous)).aestronglyMeasurable
      hF0 hH0 (fun x => sbi_norm_wFc m (u := F) (v := H) x)
  have hg1I : IntegrableOn
      (fun y => ((B0579.pd l (fun y => B0579.jb y ^ (-m)) y : ℝ) : ℂ) * F y *
        (starRingEnd ℂ) (H y)) (B0579.cell c) :=
    sbi_int_dom (C := 2 * |m|)
      (((sbi_contDiff_pdR (sbi_contDiff_w m) l).continuous.mul hF.continuous).mul
        (Complex.continuous_conj.comp hH.continuous)).aestronglyMeasurable
      hF0 hH0 (fun x => sbi_norm_T1 m l (F := F) (H := H) x)
  have hg2I : IntegrableOn
      (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * pdCx l F y * (starRingEnd ℂ) (H y))
      (B0579.cell c) :=
    sbi_int_dom (C := 1)
      (((sbi_contDiff_wc m).continuous.mul hdF.continuous).mul
        (Complex.continuous_conj.comp hH.continuous)).aestronglyMeasurable
      hF1 hH0 (fun x => sbi_norm_wFc m (u := pdCx l F) (v := H) x)
  have hg3I : IntegrableOn
      (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (pdCx l H y))
      (B0579.cell c) :=
    sbi_int_dom (C := 1)
      (((sbi_contDiff_wc m).continuous.mul hF.continuous).mul
        (Complex.continuous_conj.comp hdH.continuous)).aestronglyMeasurable
      hF0 hH1 (fun x => sbi_norm_wFc m (u := F) (v := pdCx l H) x)
  have hdPhiI : IntegrableOn
      (pdCx l (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y)))
      (B0579.cell c) := by
    have e : pdCx l (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y))
        = fun x => ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (H x)
          + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx l F x * (starRingEnd ℂ) (H x)
          + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx l H x) :=
      funext hPR
    rw [e]
    exact (hg1I.add hg2I).add hg3I
  -- the integral of `∂_l Φ` over the cell vanishes
  have hzero : ∫ x in B0579.cell c,
      pdCx l (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y)) x = 0 := by
    rcases (show l = 0 ∨ l = 1 by fin_cases l <;> simp) with rfl | rfl
    · refine sbi_ibp_q hc hPhiC hdPhiI (fun η => ?_)
      have hjb : B0579.jb (c / 2, η) = B0579.jb (-c / 2, η) := by
        show (1 + (c / 2) ^ 2 + η ^ 2 : ℝ) = 1 + (-c / 2) ^ 2 + η ^ 2
        ring
      try dsimp only
      rw [hjb, sbi_cancel F hFp η, sbi_cancel H hHp η]
    · exact sbi_ibp_eta hPhiC hPhiI hdPhiI
  -- split the integral of `∂_l Φ`
  have hEq : ∫ x in B0579.cell c,
      pdCx l (fun y => ((B0579.jb y ^ (-m) : ℝ) : ℂ) * F y * (starRingEnd ℂ) (H y)) x
      = (∫ x in B0579.cell c, ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (H x))
        + (∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx l F x *
            (starRingEnd ℂ) (H x))
        + (∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (pdCx l H x)) := by
    have hA : IntegrableOn (fun x => ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) *
        F x * (starRingEnd ℂ) (H x) + ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx l F x *
        (starRingEnd ℂ) (H x)) (B0579.cell c) := hg1I.add hg2I
    rw [integral_congr_ae (ae_of_all _ hPR), integral_add hA hg3I, integral_add hg1I hg2I]
  have hsum : (∫ x in B0579.cell c, ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) *
            F x * (starRingEnd ℂ) (H x))
        + (∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx l F x *
            (starRingEnd ℂ) (H x))
        + (∫ x in B0579.cell c, ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (pdCx l H x)) = 0 := by
    rw [← hEq]
    exact hzero
  -- the two inner products as cell integrals
  have hipX1 : ipX c m F (pdCx l H) = (∫ x in B0579.cell c,
      ((B0579.jb x ^ (-m) : ℝ) : ℂ) * F x * (starRingEnd ℂ) (pdCx l H x)).re := by
    unfold ipX
    rw [sbi_ipX_cell c m F (pdCx l H)]
  have hipX2 : ipX c m (pdCx l F) H = (∫ x in B0579.cell c,
      ((B0579.jb x ^ (-m) : ℝ) : ℂ) * pdCx l F x * (starRingEnd ℂ) (H x)).re := by
    unfold ipX
    rw [sbi_ipX_cell c m (pdCx l F) H]
  have hLHS : ipX c m F (pdCx l H) + ipX c m (pdCx l F) H = -(∫ x in B0579.cell c,
      ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (H x)).re := by
    rw [hipX1, hipX2, ← Complex.add_re, ← Complex.neg_re]
    congr 1
    linear_combination hsum
  -- the remainder term is bounded by Hölder
  have hI3b : ‖∫ x in B0579.cell c,
      ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x * (starRingEnd ℂ) (H x)‖
        ≤ 2 * |m| * ((xNorm c (-m) F).toReal * (xNorm c (-m) H).toReal) := by
    have hdom := sbi_integrable_wprod (c := c) (m := m) hF0 hH0
    calc ‖∫ x in B0579.cell c,
          ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (H x)‖
        ≤ ∫ x in B0579.cell c, ‖((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (H x)‖ :=
          norm_integral_le_integral_norm (μ := volume.restrict (B0579.cell c)) _
      _ ≤ ∫ x in B0579.cell c, 2 * |m| * (B0579.jb x ^ (-m) * (‖F x‖ * ‖H x‖)) :=
          integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
            (hdom.const_mul (2 * |m|))
            (ae_of_all _ fun x => sbi_norm_T1 m l (F := F) (H := H) x)
      _ = 2 * |m| * ∫ x in B0579.cell c, B0579.jb x ^ (-m) * (‖F x‖ * ‖H x‖) :=
          integral_const_mul _ _
      _ = 2 * |m| * ∫ x, ‖F x‖ * ‖H x‖ ∂(B0579.cellMeasure c (-m)) := by
          rw [sbi_integral_cellMeasure c (-m) (fun x => ‖F x‖ * ‖H x‖)]
      _ ≤ 2 * |m| * ((xNorm c (-m) F).toReal * (xNorm c (-m) H).toReal) :=
          mul_le_mul_of_nonneg_left (sbi_holder hF0 hH0) (by positivity)
  calc |ipX c m F (pdCx l H) + ipX c m (pdCx l F) H|
      = |(∫ x in B0579.cell c,
          ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (H x)).re| := by
        rw [hLHS, abs_neg]
    _ ≤ ‖∫ x in B0579.cell c,
          ((B0579.pd l (fun y => B0579.jb y ^ (-m)) x : ℝ) : ℂ) * F x *
            (starRingEnd ℂ) (H x)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 2 * |m| * ((xNorm c (-m) F).toReal * (xNorm c (-m) H).toReal) := hI3b
    _ = 2 * |m| * (xNorm c (-m) F).toReal * (xNorm c (-m) H).toReal := by ring

end UnforcedLeray.Short.IIIa
