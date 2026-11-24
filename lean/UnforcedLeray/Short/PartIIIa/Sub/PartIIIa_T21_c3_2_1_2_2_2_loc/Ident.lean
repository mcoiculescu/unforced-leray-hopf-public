import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.PlanarDil
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.Periodize

/-!
# Pointwise identities for the pinned relative free evolution (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2941-2970.  The cell part
`I_t J_{a_t}^{-1} ω(t)` of `\bar F_rel` is the dilation `J_{1/a_t}` of the zero-extended cell flow,
and the exterior part `S(t,s)(I - Π_s) W` is the dilation `J_{(d_t/d_s)^2}` of the exterior field.
For a real field `Φ` vanishing near the cell boundary lines, `fData` gives the rescaled cell
restriction as a cylinder test.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.RelB4locAux

open CompactDuhamelGapSub

theorem cToPlane_smul (r : ℝ) (z : ℂ) : cToPlane (r • z) = (r * z.re, r * z.im) := by
  simp [cToPlane, Complex.smul_re, Complex.smul_im]

theorem planeToC_mul (r : ℝ) (z : ℂ) : planeToC (r * z.re, r * z.im) = r • z := by
  apply Complex.ext <;> simp [planeToC]

/-- The cell part of the pinned expression is a planar dilation of the lifted cell flow. -/
theorem cellZeroExt_JscaleInv_eq {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (g : ℝ × ℝ → ℝ) (z : ℂ) :
    cellZeroExt (cellLen c a) (JscaleInv a (fun x => ((g x : ℝ) : ℂ))) (cToPlane z) =
      Planar.dilWFun a⁻¹ (liftFun c g) z := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hd : 0 < cellLen c a := div_pos hc hsa
  have hratio : c / cellLen c a = Real.sqrt a := by unfold cellLen; field_simp
  have hmem : cToPlane z ∈ B0579.cell (cellLen c a) ↔
      (Real.sqrt a * z.re, Real.sqrt a * z.im) ∈ B0579.cell c := by
    have h := scaleMem_cell_iff hc hd (cToPlane z)
    rw [hratio] at h
    exact h.symm
  have hs : (Real.sqrt a⁻¹)⁻¹ = Real.sqrt a := by rw [Real.sqrt_inv, inv_inv]
  have hpow : ((a⁻¹ ^ 2)⁻¹ : ℝ) = a ^ 2 := by rw [inv_pow, inv_inv]
  simp only [Planar.dilWFun, liftFun, hs, hpow, cToPlane_smul, cellZeroExt]
  by_cases h : cToPlane z ∈ B0579.cell (cellLen c a)
  · rw [indicator_of_mem h, indicator_of_mem (hmem.1 h)]
    simp [JscaleInv, cToPlane]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.2 h')), mul_zero]

/-- The exterior part of the pinned expression is a planar dilation of the exterior field. -/
theorem extDil_eq_dilWFun {d_s d_t : ℝ} (hds : 0 < d_s) (hdt : 0 < d_t) (W : ℂ → ℂ) (z : ℂ) :
    extDilCocycle d_s d_t
        (fun x => W (planeToC x) - cellZeroExt d_s (fun y => W (planeToC y)) x) (cToPlane z) =
      Planar.dilWFun ((d_s / d_t) ^ 2)⁻¹
        (fun w => W w - cellZeroExt d_s (fun y => W (planeToC y)) (cToPlane w)) z := by
  have hρ : 0 < d_s / d_t := div_pos hds hdt
  have hs : (Real.sqrt ((d_s / d_t) ^ 2)⁻¹)⁻¹ = d_s / d_t := by
    rw [Real.sqrt_inv, inv_inv, Real.sqrt_sq hρ.le]
  have hpow : ((((d_s / d_t) ^ 2)⁻¹ ^ 2)⁻¹ : ℝ) = (d_s / d_t) ^ 4 := by
    rw [inv_pow, inv_inv, ← pow_mul]
  simp only [extDilCocycle, Planar.dilWFun, hs, hpow, cToPlane_smul]
  rw [show ((d_s / d_t) * (cToPlane z).1, (d_s / d_t) * (cToPlane z).2) =
    ((d_s / d_t) * z.re, (d_s / d_t) * z.im) from rfl, planeToC_mul]

/-! ## The rescaled cell data -/

/-- Rescaled cell values `a^{-2} Φ(x/√a)` of a real planar field. -/
def hFun (Φr : ℂ → ℝ) (a : ℝ) (x : ℝ × ℝ) : ℝ :=
  (a ^ 2)⁻¹ * Φr (planeToC ((Real.sqrt a)⁻¹ * x.1, (Real.sqrt a)⁻¹ * x.2))

/-- The cylinder datum: periodization of the rescaled cell values. -/
def fData (c : ℝ) (Φr : ℂ → ℝ) (a : ℝ) : ℝ × ℝ → ℝ := cellPer c (hFun Φr a)

theorem contDiff_planeToC : ContDiff ℝ ∞ planeToC := by
  have : planeToC = fun y : ℝ × ℝ => (y.1 : ℂ) + (y.2 : ℂ) * Complex.I := by
    funext y; apply Complex.ext <;> simp [planeToC]
  rw [this]
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

theorem contDiff_hFun {Φr : ℂ → ℝ} (hΦ : ContDiff ℝ ∞ Φr) (a : ℝ) :
    ContDiff ℝ ∞ (hFun Φr a) :=
  contDiff_const.mul (hΦ.comp (contDiff_planeToC.comp
    ((contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))))

theorem hFun_cToPlane (Φr : ℂ → ℝ) (a : ℝ) (z : ℂ) :
    hFun Φr a (cToPlane z) = (a ^ 2)⁻¹ * Φr ((Real.sqrt a)⁻¹ • z) := by
  rw [hFun, show ((Real.sqrt a)⁻¹ * (cToPlane z).1, (Real.sqrt a)⁻¹ * (cToPlane z).2) =
    ((Real.sqrt a)⁻¹ * z.re, (Real.sqrt a)⁻¹ * z.im) from rfl, planeToC_mul]

theorem hFun_vanish {c a d₀ δ : ℝ} (hc : 0 < c) (ha : 0 < a) (hδ : 0 < δ)
    (hd : |cellLen c a - d₀| < δ / 2) {Φr : ℂ → ℝ}
    (hv : ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φr z = 0) :
    ∀ x : ℝ × ℝ, c / 2 - min (δ * Real.sqrt a / 4) (c / 2) < |x.1| → |x.1| ≤ c / 2 →
      hFun Φr a x = 0 := by
  intro x h1 h2
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hcd : c = cellLen c a * Real.sqrt a := by unfold cellLen; field_simp
  have hmin : min (δ * Real.sqrt a / 4) (c / 2) ≤ δ * Real.sqrt a / 4 := min_le_left _ _
  have hd' := abs_lt.1 hd
  have hre : (planeToC ((Real.sqrt a)⁻¹ * x.1, (Real.sqrt a)⁻¹ * x.2)).re =
      (Real.sqrt a)⁻¹ * x.1 := rfl
  have habs : |(Real.sqrt a)⁻¹ * x.1| * Real.sqrt a = |x.1| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hsa)]; field_simp
  unfold hFun
  rw [hv _ ?_ ?_, mul_zero]
  · rw [hre]
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hsa.le
    rw [habs] at this
    nlinarith
  · rw [hre]
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hsa.le
    rw [habs] at this
    nlinarith

theorem exists_band_of_hasCompactSupport {Φr : ℂ → ℝ} (hΦc : HasCompactSupport Φr) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → Φr z = 0 := by
  obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hz => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have := hR hmem
  rw [mem_closedBall_zero_iff] at this
  linarith

theorem hFun_band {Φr : ℂ → ℝ} {R : ℝ} (hR : ∀ z : ℂ, R < ‖z‖ → Φr z = 0) {a : ℝ}
    (ha : 0 < a) : ∀ x : ℝ × ℝ, R * Real.sqrt a < |x.2| → hFun Φr a x = 0 := by
  intro x hx
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  unfold hFun
  rw [hR _ ?_, mul_zero]
  refine lt_of_lt_of_le ?_ (Complex.abs_im_le_norm _)
  show R < |(Real.sqrt a)⁻¹ * x.2|
  rw [abs_mul, abs_of_pos (inv_pos.2 hsa), inv_mul_eq_div, lt_div_iff₀ hsa]
  exact hx

theorem isCylTest_fData {c a d₀ δ : ℝ} (hc : 0 < c) (ha : 0 < a) (hδ : 0 < δ)
    (hd : |cellLen c a - d₀| < δ / 2) {Φr : ℂ → ℝ} (hΦs : ContDiff ℝ ∞ Φr)
    (hΦc : HasCompactSupport Φr)
    (hv : ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φr z = 0) :
    B0579.IsCylTest c (fData c Φr a) := by
  obtain ⟨R, hR⟩ := exists_band_of_hasCompactSupport hΦc
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hη : 0 < min (δ * Real.sqrt a / 4) (c / 2) := lt_min (by positivity) (by positivity)
  have hηc : min (δ * Real.sqrt a / 4) (c / 2) < c := (min_le_right _ _).trans_lt (by linarith)
  exact isCylTest_cellPer hc hη hηc (contDiff_hFun hΦs a) (hFun_vanish hc ha hδ hd hv)
    (hFun_band hR ha)

/-- Vanishing of the periodized datum in the boundary layer of the cell. -/
theorem cellPer_vanish {c η : ℝ} (hc : 0 < c) (hη : 0 < η) {h : ℝ × ℝ → ℝ}
    (hvan : ∀ x : ℝ × ℝ, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → h x = 0) :
    ∀ x : ℝ × ℝ, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → cellPer c h x = 0 := by
  intro x h1 h2
  unfold cellPer
  apply hvan _ _ (abs_cellReduce_le hc x)
  rcases eq_or_ne x.1 (c / 2) with hx | hx
  · have h1' : c / 2 / c + 1 / 2 = 1 := by field_simp; ring
    show c / 2 - η < |x.1 - c * ⌊x.1 / c + 1 / 2⌋|
    rw [hx, h1', Int.floor_one]
    push_cast
    rw [show c / 2 - c * 1 = -(c / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  · have hmem : x ∈ B0579.cell c := by
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
      have := abs_le.1 h2
      exact ⟨this.1, lt_of_le_of_ne this.2 hx⟩
    rw [cellReduce_of_mem hc hmem]
    exact h1

theorem fData_vanish {c a d₀ δ : ℝ} (hc : 0 < c) (ha : 0 < a) (hδ : 0 < δ)
    (hd : |cellLen c a - d₀| < δ / 2) {Φr : ℂ → ℝ}
    (hv : ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φr z = 0) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧
      ∀ x : ℝ × ℝ, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → fData c Φr a x = 0 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  refine ⟨min (δ * Real.sqrt a / 4) (c / 2), lt_min (by positivity) (by positivity),
    (min_le_right _ _).trans_lt (by linarith), ?_⟩
  exact cellPer_vanish hc (lt_min (by positivity) (by positivity)) (hFun_vanish hc ha hδ hd hv)

/-- The rescaled datum reproduces the field on the cell `d = c/√a` (the pinning condition). -/
theorem JscaleInv_fData {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (Φr : ℂ → ℝ) {y : ℝ × ℝ}
    (hy : y ∈ B0579.cell (cellLen c a)) :
    JscaleInv a (fun x => ((fData c Φr a x : ℝ) : ℂ)) y = ((Φr (planeToC y) : ℝ) : ℂ) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hd : 0 < cellLen c a := div_pos hc hsa
  have hratio : c / cellLen c a = Real.sqrt a := by unfold cellLen; field_simp
  have hmem : (Real.sqrt a * y.1, Real.sqrt a * y.2) ∈ B0579.cell c := by
    have h := (scaleMem_cell_iff hc hd y).2 hy
    rwa [hratio] at h
  simp only [JscaleInv, fData, cellPer_of_mem hc _ hmem, hFun]
  have e1 : (Real.sqrt a)⁻¹ * (Real.sqrt a * y.1) = y.1 := by field_simp
  have e2 : (Real.sqrt a)⁻¹ * (Real.sqrt a * y.2) = y.2 := by field_simp
  have ha2 : a ^ 2 ≠ 0 := by positivity
  rw [e1, e2, ← Complex.ofReal_mul, ← mul_assoc, mul_inv_cancel₀ ha2, one_mul]

/-- Pointwise bound of the lifted difference of two data by the difference of planar dilations. -/
theorem norm_liftFun_fData_sub_le {c : ℝ} (hc : 0 < c) (Φr : ℂ → ℝ) (a a' : ℝ) (z : ℂ) :
    ‖liftFun c (fData c Φr a - fData c Φr a') z‖ ≤
      ‖Planar.dilWFun a (fun w => ((Φr w : ℝ) : ℂ)) z -
        Planar.dilWFun a' (fun w => ((Φr w : ℝ) : ℂ)) z‖ := by
  simp only [liftFun, cellZeroExt]
  by_cases h : cToPlane z ∈ B0579.cell c
  · rw [indicator_of_mem h]
    simp only [Pi.sub_apply, fData, cellPer_of_mem hc _ h, hFun_cToPlane, Planar.dilWFun]
    push_cast
    exact le_rfl
  · rw [indicator_of_notMem h, norm_zero]
    exact norm_nonneg _

end UnforcedLeray.Short.IIIa.RelB4locAux
