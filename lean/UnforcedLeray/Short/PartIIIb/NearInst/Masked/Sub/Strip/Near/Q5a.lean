import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Split
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16

/-!
# `PartIII-b:C/near/masked/22/2/5a`: the `L²_τ L²_y` bound of the receiver truncation (source 4000-4003)

Route. `sep:young` (`IIIa.SepYoung`) at `K = Kset`, `j = 0`, `p = q = 2`, `b = 1`, `δ = 3/2`, gives
`‖1_young W‖_{L²_τL²} ≤ C_y D^{-1} ‖T‖_{L²_τL²}` for an `P = 2c/R`-periodic separated source with
`rOut = R/√(e^δ l)`, `rIn = R/√r`. The pointwise bound `|nearM| ≤ √3 · UnforcedLeray.Short.IIIa.youngDerivNorm` (Euclidean vs
sup norm on `ℂ³`) and the gap `D ≥ (1 - e^{-δ/4}) R/√r` (from `r ≤ e^{δ/2} l`) finish the estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem q5a_enorm_eq {E : Type*} [NormedAddCommGroup E] (v : E) :
    ‖v‖ₑ = ENNReal.ofReal ‖v‖ :=
  (ofReal_norm v).symm

theorem q5a_euclid (W : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 W : EuclideanSpace ℂ (Fin 3))‖ ≤ Real.sqrt 3 * ‖W‖ := by
  have h : ∀ i, ‖W i‖ ^ 2 ≤ ‖W‖ ^ 2 := fun i => by
    have := norm_le_pi_norm W i
    nlinarith [norm_nonneg (W i), norm_nonneg W]
  have hS : ∑ i, ‖(WithLp.toLp 2 W : EuclideanSpace ℂ (Fin 3)) i‖ ^ 2 ≤ 3 * ‖W‖ ^ 2 := by
    simp only [PiLp.toLp_apply, Fin.sum_univ_three]
    linarith [h 0, h 1, h 2]
  rw [EuclideanSpace.norm_eq]
  refine le_trans (Real.sqrt_le_sqrt hS) ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)]

theorem q5a_pt (R c r ν μ : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : UnforcedLeray.Space) :
    nearM ν μ R c r g τ y ≤ ENNReal.ofReal (Real.sqrt 3) *
      UnforcedLeray.Short.IIIa.youngDerivNorm ν (μ : ℂ) (NearInst.cartLift R c g) 0 (R / Real.sqrt r) τ y := by
  unfold nearM
  split_ifs with hrad
  · have hyr : R / Real.sqrt r ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
      unfold hRad at hrad
      exact hrad.le
    unfold UnforcedLeray.Short.IIIa.youngDerivNorm
    rw [if_pos hyr]
    unfold nearEN UnforcedLeray.Short.IIIa.wDerivNorm
    rw [q5a_enorm_eq, norm_iteratedFDeriv_zero, ← ENNReal.ofReal_mul (Real.sqrt_nonneg 3)]
    dsimp only
    apply ENNReal.ofReal_le_ofReal
    exact q5a_euclid _
  · exact zero_le

theorem q5a_gap (R δ l r : ℝ) (hR : 0 < R) (hl : 0 < l) (hr : 0 < r) (hδ : 0 < δ)
    (hrl : r ≤ Real.exp (δ / 2) * l) :
    R / Real.sqrt (Real.exp δ * l) ≤ Real.exp (-δ / 4) * (R / Real.sqrt r) := by
  have hlam : 0 < Real.exp δ * l := mul_pos (Real.exp_pos _) hl
  have hslam : 0 < Real.sqrt (Real.exp δ * l) := Real.sqrt_pos.2 hlam
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have h2 : Real.exp (-δ / 4) ^ 2 * Real.exp δ = Real.exp (δ / 2) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsq : r ≤ (Real.exp (-δ / 4) * Real.sqrt (Real.exp δ * l)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hlam.le]
    have e1 : Real.exp (-δ / 4) ^ 2 * (Real.exp δ * l) =
        (Real.exp (-δ / 4) ^ 2 * Real.exp δ) * l := by ring
    rw [e1, h2]
    exact hrl
  have hkey : Real.sqrt r ≤ Real.exp (-δ / 4) * Real.sqrt (Real.exp δ * l) := by
    calc Real.sqrt r ≤ Real.sqrt ((Real.exp (-δ / 4) * Real.sqrt (Real.exp δ * l)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.exp (-δ / 4) * Real.sqrt (Real.exp δ * l) :=
          Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le hslam.le)
  rw [div_le_iff₀ hslam]
  have e2 : Real.exp (-δ / 4) * (R / Real.sqrt r) * Real.sqrt (Real.exp δ * l) =
      R * (Real.exp (-δ / 4) * Real.sqrt (Real.exp δ * l)) / Real.sqrt r := by ring
  rw [e2, le_div_iff₀ hsr]
  exact mul_le_mul_of_nonneg_left hkey hR.le

theorem nearYoungLtau (hY : UnforcedLeray.Short.IIIa.SepYoung) (Kset : Set ℝ) (hKc : IsCompact Kset)
    (hKs : Kset ⊆ Set.Ioo (0 : ℝ) (1 / 4)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R c ν μ l r : ℝ) (g : Chart → Ten3), 0 < R → 0 < c → 0 < ν → μ ∈ Kset →
      0 < l → l < r → r ≤ Real.exp (δ / 2) * l → IsBoxTensor g →
      (∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1) →
      UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2 (nearM ν μ R c r g) ≤
        ENNReal.ofReal (C * (Real.sqrt r / R)) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
            (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g)) := by
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Kset with hKdef
  have hKc' : IsCompact K := hKc.image Complex.continuous_ofReal
  have hK1 : ∀ w ∈ K, -(1 / 4) < w.re := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have := (hKs hx).1
    simp only [Complex.ofReal_re]
    linarith
  have hδ' : ∃ δ' : ℝ, 0 < δ' ∧ ∀ w ∈ K, δ' ≤ 2 * w.re + 3 / (2 : ℝ) := by
    refine ⟨3 / 2, by norm_num, ?_⟩
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have := (hKs hx).1
    simp only [Complex.ofReal_re]
    linarith
  obtain ⟨Cy, hCy0, hCy⟩ := hY K hKc' hK1 0 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ'
  have he : Real.exp (-δ / 4) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  refine ⟨Real.sqrt 3 * Cy / (1 - Real.exp (-δ / 4)), ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCy0) (by linarith)
  · intro R c ν μ l r g hR hc hν hμ hl hlr hrl hg hsupp
    have hr : 0 < r := hl.trans hlr
    have hlam : 0 < Real.exp δ * l := mul_pos (Real.exp_pos _) hl
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    have hslam : 0 < Real.sqrt (Real.exp δ * l) := Real.sqrt_pos.2 hlam
    have hrel : R ^ 2 = Real.exp δ * l * (R / Real.sqrt (Real.exp δ * l)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hlam.le]
      field_simp
    have hsrc := sp_isSepSource_cartLift R c hR hc (Real.exp δ * l)
      (R / Real.sqrt (Real.exp δ * l)) hlam (div_pos hR hslam) hrel g hg hsupp
    have hlt : R / Real.sqrt (Real.exp δ * l) < R / Real.sqrt r := by
      apply div_lt_div_of_pos_left hR hsr
      apply Real.sqrt_lt_sqrt hr.le
      have h1 : Real.exp (δ / 2) < Real.exp δ := Real.exp_lt_exp.2 (by linarith)
      nlinarith [mul_lt_mul_of_pos_right h1 hl]
    have hP : 0 < 2 * c / R := by positivity
    have hYi := hCy ν hν (μ : ℂ) ⟨μ, hμ, rfl⟩ (R / Real.sqrt (Real.exp δ * l)) (R / Real.sqrt r)
      (2 * c / R) (div_pos hR hslam).le hlt hP (NearInst.cartLift R c g) hsrc
    have hexp : ∀ x : ℝ, x ^ ((-4 : ℝ) - ((0 : ℕ) : ℝ) + 3 / 1) = x⁻¹ := fun x => by
      norm_num [Real.rpow_neg_one]
    rw [hexp] at hYi
    have hpos1 : 0 < 1 - Real.exp (-δ / 4) := by linarith
    have hgap := q5a_gap R δ l r hR hl hr hδ hrl
    have hRs : 0 < R / Real.sqrt r := div_pos hR hsr
    have hD : (1 - Real.exp (-δ / 4)) * (R / Real.sqrt r) ≤
        R / Real.sqrt r - R / Real.sqrt (Real.exp δ * l) := by
      have e3 : (1 - Real.exp (-δ / 4)) * (R / Real.sqrt r) =
          R / Real.sqrt r - Real.exp (-δ / 4) * (R / Real.sqrt r) := by ring
      rw [e3]
      linarith
    have hm : 0 < (1 - Real.exp (-δ / 4)) * (R / Real.sqrt r) := mul_pos hpos1 hRs
    have hDinv : (R / Real.sqrt r - R / Real.sqrt (Real.exp δ * l))⁻¹ ≤
        Real.sqrt r / (R * (1 - Real.exp (-δ / 4))) := by
      have h1 := inv_anti₀ hm hD
      have h2 : ((1 - Real.exp (-δ / 4)) * (R / Real.sqrt r))⁻¹ =
          Real.sqrt r / (R * (1 - Real.exp (-δ / 4))) := by
        have hne : (1 - Real.exp (-δ / 4)) ≠ 0 := hpos1.ne'
        have hRne : R ≠ 0 := hR.ne'
        have hsne : Real.sqrt r ≠ 0 := hsr.ne'
        field_simp
      exact h1.trans_eq h2
    have hstep1 : UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2 (nearM ν μ R c r g) ≤
        UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
          (fun τ y => ENNReal.ofReal (Real.sqrt 3) *
            UnforcedLeray.Short.IIIa.youngDerivNorm ν (μ : ℂ) (NearInst.cartLift R c g) 0 (R / Real.sqrt r) τ y) :=
      UnforcedLeray.Short.IIIa.ltauLq_mono _ _ (by norm_num) (fun τ y => q5a_pt R c r ν μ g τ y)
    have hstep2 := UnforcedLeray.Short.IIIa.ltauLq_const_mul (2 * c / R) 2 (by norm_num)
      (ENNReal.ofReal (Real.sqrt 3)) ENNReal.ofReal_ne_top
      (UnforcedLeray.Short.IIIa.youngDerivNorm ν (μ : ℂ) (NearInst.cartLift R c g) 0 (R / Real.sqrt r))
    calc UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2 (nearM ν μ R c r g)
        ≤ UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
          (fun τ y => ENNReal.ofReal (Real.sqrt 3) *
            UnforcedLeray.Short.IIIa.youngDerivNorm ν (μ : ℂ) (NearInst.cartLift R c g) 0 (R / Real.sqrt r) τ y) := hstep1
      _ = ENNReal.ofReal (Real.sqrt 3) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
            (UnforcedLeray.Short.IIIa.youngDerivNorm ν (μ : ℂ) (NearInst.cartLift R c g) 0 (R / Real.sqrt r)) := hstep2
      _ ≤ ENNReal.ofReal (Real.sqrt 3) *
          (ENNReal.ofReal (Cy * (R / Real.sqrt r - R / Real.sqrt (Real.exp δ * l))⁻¹) *
            UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
              (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g))) :=
          by gcongr
      _ = ENNReal.ofReal (Real.sqrt 3 * (Cy * (R / Real.sqrt r - R / Real.sqrt (Real.exp δ * l))⁻¹)) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
            (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg 3)]
      _ ≤ ENNReal.ofReal (Real.sqrt 3 * Cy / (1 - Real.exp (-δ / 4)) * (Real.sqrt r / R)) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
            (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g)) := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          apply ENNReal.ofReal_le_ofReal
          have hne : (1 - Real.exp (-δ / 4)) ≠ 0 := hpos1.ne'
          have hRne : R ≠ 0 := hR.ne'
          have hC : Real.sqrt 3 * Cy / (1 - Real.exp (-δ / 4)) * (Real.sqrt r / R) =
              Real.sqrt 3 * (Cy * (Real.sqrt r / (R * (1 - Real.exp (-δ / 4))))) := by
            field_simp
          rw [hC]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDinv hCy0)
            (Real.sqrt_nonneg 3)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
