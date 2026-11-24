import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.FarDomChart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.ChartPhysL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.SepDomFacts
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepFarBox.Ident

/-!
# `PartIII-b:C/rep/5/2/1/4`: `RepFarBox` from the four leaves

Source `the November 2 reference manuscript` 3631-3664 (`sep:young`,
`sep:repair-energy`: `p = 22/19`, `q = 2`, kernel exponent `b = 11/7`, `1 + 1/2 = 19/22 + 7/11`,
`D^{-4+21/11} = D^{-23/11}`), 3905-3912, 5585-5603.

Leaves: `farDomChart` (pointwise gap majorant), `chartPhysL2` (change of variables),
`sepDomFacts` (measurability, periodicity, axisymmetry), `IIIa.sepDomYoung` (Young in `y`).
`repBox_core` is the analytic composition with all parameters explicit; `repFarBox` instantiates it.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `A ≤ B^2 → A^{1/2} ≤ B` in `ℝ≥0∞`. -/
theorem repBox_sq_half {A B : ℝ≥0∞} (h : A ≤ B ^ (2 : ℝ)) : A ^ (1 / 2 : ℝ) ≤ B := by
  calc A ^ (1 / 2 : ℝ) ≤ (B ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = B := by rw [← ENNReal.rpow_mul]; norm_num

/-- The analytic core of the box bound, all parameters explicit. -/
theorem repBox_core (C0 CY R c S ν μ δ : ℝ) (f : Chart → Ten3)
    (hC0 : 0 < C0) (hCY0 : 0 ≤ CY) (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R) (hc : 0 < c)
    (hδ : 0 < δ) (hS : 0 < S) (hf : NearInst.IsBoxTensor f)
    (hB : ∀ p : Chart, 0 < p.1 → p.1 < S →
      ‖NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f)
          (NearInst.chartY R p) (NearInst.chartTau R p))‖ₑ ≤
        ENNReal.ofReal C0 * UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
          ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S)
          (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))
          (NearInst.chartTau R p) (NearInst.chartY R p))
    (hY : ∀ a : ℝ, 0 ≤ a → 1 ≤ a - 2 + 3 / (22 / 19 : ℝ) → ∀ D P : ℝ, 0 < D → 0 < P →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
        (∀ τ z, g (τ + P) z = g τ z) →
        UnforcedLeray.Short.IIIa.ltauLq P 2 (UnforcedLeray.Short.IIIa.sepDom a 0 D g) ≤
          ENNReal.ofReal (CY * D ^ (-4 - ((0 : ℕ) : ℝ) + 3 / (11 / 7 : ℝ))) *
            UnforcedLeray.Short.IIIa.ltauLq P (22 / 19) g) :
    eLpNorm (fun p : Chart => if p.1 < S then (Real.sqrt p.1)⁻¹ •
        NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f)
          (NearInst.chartY R p) (NearInst.chartTau R p)) else 0) 2 (srcMeasure c) ≤
      ENNReal.ofReal (C0 * R⁻¹ * (CY * ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) ^
        (-(23 / 11) : ℝ))) * phaseL2Lr (2 * c / R) (22 / 19) (strPhys R c f) := by
  have hRi0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hSq : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have he1 : Real.exp (-(δ / 2)) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(δ / 2) < 0 by linarith)
    simpa using this
  have he0 : 0 < 1 - Real.exp (-(δ / 2)) := by linarith
  have hDm : 0 < (1 - Real.exp (-(δ / 2))) * R / Real.sqrt S := div_pos (mul_pos he0 hR) hSq
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  -- pointwise bound of the pinned function
  have hpt : ∀ p : Chart,
      ‖(if p.1 < S then (Real.sqrt p.1)⁻¹ • NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1
          (NearInst.cartLift R c f) (NearInst.chartY R p) (NearInst.chartTau R p)) else 0)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal C0 ^ (2 : ℝ) * (ENNReal.ofReal p.1⁻¹ *
          UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S)
            (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))
            (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)) := by
    intro p
    by_cases hps : p.1 < S
    · by_cases hp0 : 0 < p.1
      · rw [if_pos hps]
        have hb := hB p hp0 hps
        rw [enorm_smul, Real.enorm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
        have hsq : ENNReal.ofReal (Real.sqrt p.1)⁻¹ ^ 2 = ENNReal.ofReal p.1⁻¹ := by
          rw [← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_pow,
            Real.sq_sqrt hp0.le]
        simp only [ENNReal.rpow_two]
        refine le_trans (pow_le_pow_left₀ zero_le (mul_le_mul_of_nonneg_left hb zero_le) 2) (le_of_eq ?_)
        rw [mul_pow, mul_pow, hsq]
        ring
      · rw [if_pos hps, Real.sqrt_eq_zero'.2 (not_lt.1 hp0)]
        simp
    · rw [if_neg hps]
      simp
  -- change of variables and Young in `y`
  obtain ⟨m1, m2, m3, m4, m5⟩ := sepDomFacts (2 * μ + 2) 0
    ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) R c hR hc f hf.measurable
  have hCPL := chartPhysL2 R c hR hc _ m1 m4 m5
  have hz : phaseL2Lr (2 * c / R) (22 / 19) (strPhys R c f) =
      UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) (22 / 19)
        (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f)) := by
    unfold phaseL2Lr UnforcedLeray.Short.IIIa.ltauLq
    rw [ENNReal.ofReal_inv_of_pos hP]
    rfl
  have hYle : UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
      (UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S)
        (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))) ≤
      ENNReal.ofReal (CY * ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S) ^ (-(23 / 11) : ℝ)) *
        phaseL2Lr (2 * c / R) (22 / 19) (strPhys R c f) := by
    rw [hz]
    have h := hY (2 * μ + 2) (by linarith) (by norm_num; linarith) _ (2 * c / R) hDm hP _ m2 m3
    have he : (-4 - ((0 : ℕ) : ℝ) + 3 / (11 / 7 : ℝ)) = -(23 / 11) := by norm_num
    rw [he] at h
    exact h
  -- the identity of constants
  have hkey : Real.sqrt (C0 ^ 2) = C0 := Real.sqrt_sq hC0.le
  -- assemble
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  apply repBox_sq_half
  have hne : ENNReal.ofReal C0 ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine ((lintegral_mono hpt).trans (le_of_eq (lintegral_const_mul' _ _ hne))).trans ?_
  refine (mul_le_mul_of_nonneg_left hCPL zero_le).trans ?_
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (ENNReal.rpow_le_rpow hYle (by norm_num)) zero_le) zero_le).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg hC0.le hRi0), ENNReal.ofReal_mul hC0.le,
    ENNReal.ofReal_pow hRi0]
  simp only [ENNReal.rpow_two]
  ring

theorem repFarBox : RepFarBox := by
  intro δ hδ
  obtain ⟨C0, hC0, hD⟩ := farDomChart
  obtain ⟨CY, hCY0, hY⟩ := sepDomYoung 0 (22 / 19) 2 (11 / 7) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) one_pos
  refine ⟨Real.sqrt (C0 ^ 2) * CY * (1 - Real.exp (-(δ / 2))) ^ (-(23 / 11) : ℝ), ?_⟩
  intro Pl K L μ hKδ hμ
  subst hKδ
  unfold RepFarBoxAt
  intro Sf hSf F f hf hFf
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hS : 0 < L.Scut K := by
    unfold ReturnLevel.Scut
    exact Real.rpow_pos_of_pos L.ε_pos _
  have key := repBox_core C0 CY (L.ε⁻¹) (cOf L.ν) (L.Scut K) L.ν μ K.δ f hC0 hCY0 hν hμ hR hc
    hδ hS hf (fun p h0 h1 => hD L.ν hν μ hμ _ _ _ _ hR hc hδ hS f hf p h0 h1) hY
  have he1 : Real.exp (-(K.δ / 2)) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(K.δ / 2) < 0 by linarith)
    simpa using this
  have he0 : 0 < 1 - Real.exp (-(K.δ / 2)) := by linarith
  have hPeq : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by
    rw [div_eq_mul_inv, inv_inv]; ring
  have hae : (Sf F : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] (fun p : Chart =>
      if p.1 < L.Scut K then (Real.sqrt p.1)⁻¹ • NearInst.merRe
          (-NearInst.sepWfar L.ν (μ : ℂ) L.ε⁻¹ K.δ p.1 (NearInst.cartLift L.ε⁻¹ (cOf L.ν) f)
            (NearInst.chartY L.ε⁻¹ p) (NearInst.chartTau L.ε⁻¹ p)) else 0) := by
    unfold srcMeasure
    rw [Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 Real.pi_pos).ne']
    exact hSf F f hf hFf
  have hdm := RepFarBoxIdent.dm_identity L.ε⁻¹ (1 - Real.exp (-(K.δ / 2))) (L.Scut K) hR he0 hS
  rw [inv_inv] at hdm
  have hk : C0 * L.ε⁻¹⁻¹ * (CY * ((1 - Real.exp (-(K.δ / 2))) * L.ε⁻¹ / Real.sqrt (L.Scut K)) ^
      (-(23 / 11) : ℝ)) = Real.sqrt (C0 ^ 2) * CY * (1 - Real.exp (-(K.δ / 2))) ^ (-(23 / 11) : ℝ) *
        L.ε ^ (34 / 11 : ℝ) * (L.Scut K) ^ (23 / 22 : ℝ) := by
    rw [inv_inv, Real.sqrt_sq hC0.le]
    linear_combination (C0 * CY) * hdm
  rw [eLpNorm_congr_ae hae]
  refine key.trans (le_of_eq ?_)
  rw [hPeq, hk]

end UnforcedLeray.Short.PartIIIb.Concrete
