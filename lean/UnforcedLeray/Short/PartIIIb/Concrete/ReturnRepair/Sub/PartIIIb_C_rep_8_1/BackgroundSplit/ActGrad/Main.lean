import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad.Arith
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_1_5

/-!
# `ActGrad` helpers: the regime estimate (source 5203-5217, 5267-5268, 5282-5289)

Source `the November 2 reference manuscript` 5203-5217 (`repair:phase-gradient`,
gradient kernel `L^{22/3}` norm `C D^{-101/22}`), 5267-5268 (`D²X` has an additional curvature
power), 5282-5289 (the general thin-source estimate `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22} N₁`).

At every phase, the jet density `|DY| + |DX| + |D²X|` of the actual thin Ward response, read on
the meridian, is dominated by one normalized majorant `agG` (separated majorants `sepDom` of order
`0,1,2` and the vertical reduction of the outward primitive) with coefficient
`(R√ν)^{-101/22}(1 + (R√ν)^{-2})`; `‖agG‖_{L^{22/3}} ≤ C ∫‖S(·,z)‖_{L²_τ}dz ≤ C πR² N₁`
(`L¹` source, `p = 1`), and `(R√ν)^{-101/22} R² ≤ ν^{-3} ε^{57/22}` (`R = ε⁻¹`).
`ag_main` is `ActGradAt` with constants uniform over the regimes `ν, ε ≤ 1`, `P ≤ 1`,
`μ ∈ [σ₁, σ₂]`, `σ₁ > -1/4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The normalized majorant -/

/-- The normalized majorant of the jet density at one phase. -/
def agG (a D Lr Λ : ℝ) (g : ℝ → Space → ℝ≥0∞) (ν R τ : ℝ) (z : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (Λ * Lr)⁻¹ * IIIa.sepDom a 0 D g τ z +
    ENNReal.ofReal Λ⁻¹ * IIIa.sepDom a 1 D g τ z +
    ENNReal.ofReal (Λ * Lr⁻¹)⁻¹ * IIIa.sepDom a 2 D g τ z +
    ENNReal.ofReal (Λ * Lr ^ 3)⁻¹ *
      (streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2)) z

section Majorant

variable {a D Lr Λ : ℝ} {g : ℝ → Space → ℝ≥0∞} {ν R τ : ℝ}

theorem agG_unit0 (h : 0 < Λ * Lr) (z : Space) :
    IIIa.sepDom a 0 D g τ z ≤ ENNReal.ofReal (Λ * Lr) * agG a D Lr Λ g ν R τ z :=
  ag_unweight h (le_add_right (le_add_right (le_add_right le_rfl)))

theorem agG_unit1 (h : 0 < Λ) (z : Space) :
    IIIa.sepDom a 1 D g τ z ≤ ENNReal.ofReal Λ * agG a D Lr Λ g ν R τ z :=
  ag_unweight h (le_add_right (le_add_right (le_add_left le_rfl)))

theorem agG_unit2 (h : 0 < Λ * Lr⁻¹) (z : Space) :
    IIIa.sepDom a 2 D g τ z ≤ ENNReal.ofReal (Λ * Lr⁻¹) * agG a D Lr Λ g ν R τ z :=
  ag_unweight h (le_add_right (le_add_left le_rfl))

theorem agG_unitV (h : 0 < Λ * Lr ^ 3) (z : Space) :
    (streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2)) z ≤
      ENNReal.ofReal (Λ * Lr ^ 3) * agG a D Lr Λ g ν R τ z :=
  ag_unweight h (le_add_left le_rfl)

theorem ag_weighted_lq {κ c : ℝ} (hκ : 0 < κ) {f : Space → ℝ≥0∞} {M : ℝ≥0∞}
    (h : lqNorm (22 / 3) f ≤ ENNReal.ofReal (c * κ) * M) :
    lqNorm (22 / 3) (fun z => ENNReal.ofReal κ⁻¹ * f z) ≤ ENNReal.ofReal c * M := by
  rw [lqNorm_const_mul (by norm_num) _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal κ⁻¹ * lqNorm (22 / 3) f
      ≤ ENNReal.ofReal κ⁻¹ * (ENNReal.ofReal (c * κ) * M) := mul_le_mul' le_rfl h
    _ = ENNReal.ofReal c * M := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hκ.le)]
        congr 2
        rw [mul_comm c κ, ← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]

theorem ag_streamAnn_meas (ν R : ℝ) : MeasurableSet (streamAnn ν R) := by
  have e : streamAnn ν R = {y : Space | R * Real.sqrt ν ≤ ϱ y} ∩
      {y : Space | ϱ y ≤ R * Real.sqrt (5 * ν / 4)} := rfl
  rw [e]
  exact (measurableSet_le measurable_const measurable_ϱ).inter
    (measurableSet_le measurable_ϱ measurable_const)

theorem agG_lq {M : ℝ≥0∞} {c0 c1 c2 cV : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hcV : 0 ≤ cV) (hκ0 : 0 < Λ * Lr) (hκ1 : 0 < Λ) (hκ2 : 0 < Λ * Lr⁻¹) (hκV : 0 < Λ * Lr ^ 3)
    (hg : Measurable (Function.uncurry g))
    (h0 : lqNorm (22 / 3) (IIIa.sepDom a 0 D g τ) ≤ ENNReal.ofReal (c0 * (Λ * Lr)) * M)
    (h1 : lqNorm (22 / 3) (IIIa.sepDom a 1 D g τ) ≤ ENNReal.ofReal (c1 * Λ) * M)
    (h2 : lqNorm (22 / 3) (IIIa.sepDom a 2 D g τ) ≤ ENNReal.ofReal (c2 * (Λ * Lr⁻¹)) * M)
    (hV : lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2))) ≤
      ENNReal.ofReal (cV * (Λ * Lr ^ 3)) * M) :
    lqNorm (22 / 3) (agG a D Lr Λ g ν R τ) ≤ ENNReal.ofReal (c0 + c1 + c2 + cV) * M := by
  have hq : (1 : ℝ) ≤ 22 / 3 := by norm_num
  have m : ∀ j : ℕ, Measurable (IIIa.sepDom a j D g τ) := fun j =>
    (IIIa.sepAE_measurable_sepDom a j D hg).of_uncurry_left
  have mV : Measurable ((streamAnn ν R).indicator (fun y : Space => vertRed a Lr D g τ (y 2))) :=
    (((vertMeasurable g hg).2 a Lr D).of_uncurry_left.comp outRed_coord2).indicator
      (ag_streamAnn_meas ν R)
  have mc : ∀ (c : ℝ) (f : Space → ℝ≥0∞), Measurable f →
      AEMeasurable (fun z => ENNReal.ofReal c * f z) volume :=
    fun c f hf => (hf.const_mul _).aemeasurable
  have e0 := ag_weighted_lq hκ0 h0
  have e1 := ag_weighted_lq hκ1 h1
  have e2 := ag_weighted_lq hκ2 h2
  have eV := ag_weighted_lq hκV hV
  unfold agG
  calc lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr)⁻¹ * IIIa.sepDom a 0 D g τ z +
        ENNReal.ofReal Λ⁻¹ * IIIa.sepDom a 1 D g τ z +
        ENNReal.ofReal (Λ * Lr⁻¹)⁻¹ * IIIa.sepDom a 2 D g τ z +
        ENNReal.ofReal (Λ * Lr ^ 3)⁻¹ *
          (streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2)) z)
      ≤ lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr)⁻¹ * IIIa.sepDom a 0 D g τ z +
          ENNReal.ofReal Λ⁻¹ * IIIa.sepDom a 1 D g τ z +
          ENNReal.ofReal (Λ * Lr⁻¹)⁻¹ * IIIa.sepDom a 2 D g τ z) +
        lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr ^ 3)⁻¹ *
          (streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2)) z) :=
        lqNorm_add_le hq ((((m 0).const_mul _).add ((m 1).const_mul _)).add
          ((m 2).const_mul _)).aemeasurable (mc _ _ mV)
    _ ≤ (lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr)⁻¹ * IIIa.sepDom a 0 D g τ z +
          ENNReal.ofReal Λ⁻¹ * IIIa.sepDom a 1 D g τ z) +
        lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr⁻¹)⁻¹ * IIIa.sepDom a 2 D g τ z)) +
        lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr ^ 3)⁻¹ *
          (streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2)) z) := by
        gcongr
        exact lqNorm_add_le hq ((((m 0).const_mul _).add ((m 1).const_mul _))).aemeasurable
          (mc _ _ (m 2))
    _ ≤ ((lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr)⁻¹ * IIIa.sepDom a 0 D g τ z) +
          lqNorm (22 / 3) (fun z => ENNReal.ofReal Λ⁻¹ * IIIa.sepDom a 1 D g τ z)) +
        lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr⁻¹)⁻¹ * IIIa.sepDom a 2 D g τ z)) +
        lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * Lr ^ 3)⁻¹ *
          (streamAnn ν R).indicator (fun y => vertRed a Lr D g τ (y 2)) z) := by
        gcongr
        exact lqNorm_add_le hq (mc _ _ (m 0)) (mc _ _ (m 1))
    _ ≤ ((ENNReal.ofReal c0 * M + ENNReal.ofReal c1 * M) + ENNReal.ofReal c2 * M) +
          ENNReal.ofReal cV * M := by
        gcongr
    _ = ENNReal.ofReal (c0 + c1 + c2 + cV) * M := by
        rw [ENNReal.ofReal_add (by positivity) hcV, ENNReal.ofReal_add (by positivity) hc2,
          ENNReal.ofReal_add hc0 hc1]
        ring

end Majorant

/-! ## 2. Meridional jets -/

theorem ag_wgxJet_merid {j : ℕ} {Cj ν μ R a D τ : ℝ}
    {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hAx : IsAxiSource S)
    (hb : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y → IIIa.sepDom a 0 D (IIIa.srcNorm S) τ y < ⊤ →
      ‖iteratedFDeriv ℝ j (sepX0 ν μ S τ) y‖ₑ ≤
        ENNReal.ofReal Cj * IIIa.sepDom a j D (IIIa.srcNorm S) τ y)
    {z : Space} (hfin : IIIa.sepDom a 0 D (IIIa.srcNorm S) τ z < ⊤) :
    wgxJet j ν μ (R * Real.sqrt ν) S τ (meridPt z) ≤
      ENNReal.ofReal Cj * IIIa.sepDom a j D (IIIa.srcNorm S) τ z := by
  unfold wgxJet
  split_ifs with h
  · rw [← ag_sepDom_merid hAx a j D τ z]
    exact hb (meridPt z) h (by rw [ag_sepDom_merid hAx]; exact hfin)
  · exact zero_le

theorem ag_wgyWJet_merid {j : ℕ} {Cj ν μ R a D τ : ℝ}
    {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hAx : IsAxiSource S)
    (hb : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y → IIIa.sepDom a 0 D (IIIa.srcNorm S) τ y < ⊤ →
      ‖iteratedFDeriv ℝ j (sepWre ν μ S τ) y‖ₑ ≤
        ENNReal.ofReal Cj * IIIa.sepDom a j D (IIIa.srcNorm S) τ y)
    {z : Space} (hfin : IIIa.sepDom a 0 D (IIIa.srcNorm S) τ z < ⊤) :
    wgyWJet j ν μ (R * Real.sqrt ν) S τ (meridPt z) ≤
      ENNReal.ofReal Cj * IIIa.sepDom a j D (IIIa.srcNorm S) τ z := by
  unfold wgyWJet
  split_ifs with h
  · rw [← ag_sepDom_merid hAx a j D τ z]
    exact hb (meridPt z) h (by rw [ag_sepDom_merid hAx]; exact hfin)
  · exact zero_le

/-! ## 3. Scale identities -/

theorem ag_id0 {c₀ L : ℝ} (hc : 0 < c₀) (hL : 0 < L) :
    (c₀ * L) ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) =
      c₀ ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) * (L ^ (-(101 / 22 : ℝ)) * L) := by
  rw [Real.mul_rpow hc.le hL.le, ← Real.rpow_add_one hL.ne']
  congr 2
  norm_num

theorem ag_id1 {c₀ L : ℝ} (hc : 0 < c₀) (hL : 0 < L) :
    (c₀ * L) ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) =
      c₀ ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) * L ^ (-(101 / 22 : ℝ)) := by
  rw [Real.mul_rpow hc.le hL.le]
  congr 2
  norm_num

theorem ag_id2 {c₀ L : ℝ} (hc : 0 < c₀) (hL : 0 < L) :
    (c₀ * L) ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) =
      c₀ ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) * (L ^ (-(101 / 22 : ℝ)) * L⁻¹) := by
  rw [Real.mul_rpow hc.le hL.le, ← Real.rpow_neg_one, ← Real.rpow_add hL]
  congr 2
  norm_num

theorem ag_idV {c₀ L R ν : ℝ} (hc : 0 < c₀) (hL : 0 < L) (hν : 0 < ν)
    (hLR : L = R * Real.sqrt ν) (Cv : ℝ) :
    (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) * (Cv * (L / (c₀ * L)) * (c₀ * L) ^ (-2 + 3 / 22 : ℝ)) =
      ((Real.pi / 4) ^ (3 / 22 : ℝ) * (Cv * c₀⁻¹ * c₀ ^ (-2 + 3 / 22 : ℝ))) *
        (L ^ (-(101 / 22 : ℝ)) * L ^ 3) := by
  have hL2 : Real.pi * ν * R ^ 2 / 4 = Real.pi / 4 * L ^ 2 := by
    rw [hLR, mul_pow, Real.sq_sqrt hν.le]; ring
  have hpow : (L ^ 2) ^ (3 / 22 : ℝ) = L ^ (3 / 11 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; norm_num
  have hdiv : L / (c₀ * L) = c₀⁻¹ := by field_simp
  have hexp : L ^ (3 / 11 : ℝ) * L ^ (-2 + 3 / 22 : ℝ) = L ^ (-(101 / 22 : ℝ)) * L ^ 3 := by
    rw [← Real.rpow_natCast L 3, ← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    norm_num
  rw [hL2, Real.mul_rpow (by positivity) (by positivity), hpow, hdiv,
    Real.mul_rpow hc.le hL.le, ← hexp]
  ring

/-- The final scale inequality: `Λ (1 + (R√ν)^{-2}) K C πR² ≤ (2KCπ + 1) ν^{-4} ε^{57/22}`. -/
theorem ag_final_real {ν ε Kc Cg : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hKc : 0 ≤ Kc) (hCg : 0 ≤ Cg) :
    (ε⁻¹ * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) * (1 + (ε⁻¹ * Real.sqrt ν)⁻¹ ^ 2) * Kc * Cg *
        (Real.pi * (ε⁻¹) ^ 2) ≤
      (2 * Kc * Cg * Real.pi + 1) * ν⁻¹ ^ 4 * ε ^ (57 / 22 : ℝ) := by
  have h1 := ag_scale_le hν hν1 hε
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hνi : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have h2 : (ε⁻¹ * Real.sqrt ν)⁻¹ ^ 2 ≤ ν⁻¹ := by
    rw [inv_pow, mul_pow, inv_pow, Real.sq_sqrt hν.le]
    rw [inv_le_inv₀ (by positivity) hν]
    have : 1 ≤ (ε ^ 2)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]
      nlinarith
    nlinarith
  have h3 : 1 + (ε⁻¹ * Real.sqrt ν)⁻¹ ^ 2 ≤ 2 * ν⁻¹ := by linarith
  have hA : 0 ≤ (ε⁻¹ * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) * (ε⁻¹) ^ 2 := by positivity
  have hB : 0 ≤ 1 + (ε⁻¹ * Real.sqrt ν)⁻¹ ^ 2 := by positivity
  have hKCπ : 0 ≤ Kc * Cg * Real.pi := by positivity
  have hE : 0 ≤ ν⁻¹ ^ 3 * ε ^ (57 / 22 : ℝ) := by positivity
  calc (ε⁻¹ * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) * (1 + (ε⁻¹ * Real.sqrt ν)⁻¹ ^ 2) * Kc * Cg *
        (Real.pi * (ε⁻¹) ^ 2)
      = ((ε⁻¹ * Real.sqrt ν) ^ (-(101 / 22 : ℝ)) * (ε⁻¹) ^ 2) *
          (1 + (ε⁻¹ * Real.sqrt ν)⁻¹ ^ 2) * (Kc * Cg * Real.pi) := by ring
    _ ≤ (ν⁻¹ ^ 3 * ε ^ (57 / 22 : ℝ)) * (2 * ν⁻¹) * (Kc * Cg * Real.pi) := by
        gcongr
    _ = (2 * Kc * Cg * Real.pi) * ν⁻¹ ^ 4 * ε ^ (57 / 22 : ℝ) := by ring
    _ ≤ (2 * Kc * Cg * Real.pi + 1) * ν⁻¹ ^ 4 * ε ^ (57 / 22 : ℝ) := by
        gcongr
        linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
