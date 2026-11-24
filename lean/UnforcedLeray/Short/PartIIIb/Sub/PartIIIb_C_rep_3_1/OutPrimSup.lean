import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1

/-!
# `PartIII-b:C/rep/3/1/2`: `outPrimPointwiseSup` (`OutPrimPointwiseSup`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
3687-3713, 4178-4186, 5238-5244.

On `streamAnn ν R` (and zero outside by definition of `wgyWPsi`, `wgxPsi`), we combine
`outPrimPointwise_of`, `outMajReduce`, 1D Hölder `(22/3, 22/19)` in the vertical variable with
`vertKernLb223` and `vertDil`, `periodicDilationSum_proved` over `l ∈ (0, 1)`, and `vprofHolder`
to bound `wgyWPsi` and `wgxPsi` uniformly in `(τ, y)` by
`(R * Real.sqrt ν) ^ (-35/22) * ‖T‖_{L²_τ L^{22/19}}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `22/3`-power of the vertical kernel. -/
private theorem ops_vkl223_pow_eq (rIn D t : ℝ) (hr : 0 < rIn) (hD : 0 < D) :
    vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ)) *
        ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ))) := by
  have hq : 0 < D ^ 2 + t ^ 2 := by positivity
  have hA : 0 < rIn / (2 * D) := by positivity
  have hnn : 0 ≤ rIn / (2 * D * (D ^ 2 + t ^ 2)) := by positivity
  have hx : rIn / (2 * D * (D ^ 2 + t ^ 2)) = (rIn / (2 * D)) * (D ^ 2 + t ^ 2) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    field_simp
  have key : (rIn / (2 * D * (D ^ 2 + t ^ 2))) ^ (22 / 3 : ℝ) =
      (rIn / (2 * D)) ^ (22 / 3 : ℝ) * (D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ)) := by
    rw [hx, Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul hq.le]
    norm_num
  unfold vertKern
  rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num), key,
    ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]

/-- The lintegral of `(D²+t²)^{-22/3}` in terms of the reference integral. -/
private theorem ops_vkl223_integral_eq {D : ℝ} (hD : 0 < D) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ))) =
      ENNReal.ofReal (D ^ (-(41 / 3 : ℝ))) *
        ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [vkl_lintegral_scale hD _ hmeas]
  have hpt : ∀ u : ℝ, ENNReal.ofReal ((D ^ 2 + (D * u) ^ 2) ^ (-(22 / 3 : ℝ))) =
      ENNReal.ofReal (D ^ (-(44 / 3 : ℝ))) * ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) := by
    intro u
    have h1 : D ^ 2 + (D * u) ^ 2 = D ^ 2 * (1 + u ^ 2) := by ring
    rw [h1, Real.mul_rpow (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := (D ^ 2) ^ (-(22 / 3 : ℝ))) (by positivity)]
    congr 2
    rw [← Real.rpow_natCast D 2, ← Real.rpow_mul hD.le]
    norm_num
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul hD.le,
    show D * D ^ (-(44 / 3 : ℝ)) = D ^ (-(41 / 3 : ℝ)) by
      rw [show (-(41 / 3 : ℝ)) = 1 + -(44 / 3 : ℝ) by norm_num, Real.rpow_add hD, Real.rpow_one]]

/-- The vertical kernel in `L^{22/3}(ℝ)` (source 3683-3701). -/
private theorem ops_vertKernLb223 :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D →
      lqNorm1 (22 / 3) (vertKern rIn D) ≤ ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) := by
  have hint : MeasureTheory.Integrable (fun u : ℝ => (1 + u ^ 2) ^ (-(22 / 3 : ℝ))) := by
    have h2 : (fun u : ℝ => (1 + u ^ 2) ^ (-(22 / 3 : ℝ))) =
        fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(44 / 3 : ℝ) / 2) := by
      funext u
      rw [Real.norm_eq_abs, sq_abs]
      norm_num
    rw [h2]
    exact integrable_rpow_neg_one_add_norm_sq (r := 44 / 3) (by
      simp only [Module.finrank_self, Nat.cast_one]
      norm_num)
  have hJ : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) ≠ ⊤ :=
    (hint.lintegral_lt_top).ne
  refine ⟨(1 / 2) * (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal ^ (3 / 22 : ℝ),
    mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _), ?_⟩
  intro rIn D hr hD
  have hA : 0 < rIn / (2 * D) := by positivity
  have hIt : ∫⁻ t : ℝ, vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ)) *
        (ENNReal.ofReal (D ^ (-(41 / 3 : ℝ))) *
          ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))) := by
    simp_rw [ops_vkl223_pow_eq rIn D _ hr hD]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ops_vkl223_integral_eq hD]
  have hIr : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) =
      ENNReal.ofReal (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal :=
    (ENNReal.ofReal_toReal hJ).symm
  have hQ : ∫⁻ t : ℝ, vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ) * D ^ (-(41 / 3 : ℝ)) *
        (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal) := by
    rw [hIt]
    conv_lhs => rw [hIr]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  have heq : ((rIn / (2 * D)) ^ (22 / 3 : ℝ) * D ^ (-(41 / 3 : ℝ)) *
        (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal) ^ (1 / (22 / 3 : ℝ)) =
      (1 / 2) * (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal ^ (3 / 22 : ℝ) *
        (rIn / D) * D ^ (-(41 / 22 : ℝ)) := by
    rw [show (1 / (22 / 3 : ℝ)) = 3 / 22 by norm_num,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hA.le, ← Real.rpow_mul hD.le,
      show (22 / 3 : ℝ) * (3 / 22) = 1 by norm_num,
      show (-(41 / 3 : ℝ)) * (3 / 22) = -(41 / 22) by norm_num, Real.rpow_one]
    ring
  unfold lqNorm1
  rw [hQ, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), heq]
  apply ENNReal.ofReal_le_ofReal
  rw [show (-2 + 3 / 22 : ℝ) = -(41 / 22) by norm_num]

/-- Pointwise 1D Hölder `(22/3, 22/19)` with dilation `w = l * s` for the vertical kernel. -/
private theorem ops_vertHolderScaled :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D → ∀ l : ℝ, 0 < l → l < 1 →
      ∀ g' : ℝ → ℝ≥0∞, Measurable g' → ∀ z : ℝ,
        ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * g' s ≤
          ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
            (ENNReal.ofReal (l ^ (-(3 / 22 : ℝ))) * lqNorm1 (22 / 19) g') := by
  obtain ⟨c, hc, hKb⟩ := ops_vertKernLb223
  refine ⟨c, hc, ?_⟩
  intro rIn D hrIn hD0 l hl0 _hl1 g' hg' z
  obtain ⟨hD1, hD2⟩ := vertDil l hl0
  set S := vertKern rIn D with hS
  set gl : ℝ → ℝ≥0∞ := fun w => g' (l⁻¹ * w) with hgl
  have hSm : Measurable S := by
    rw [hS]; unfold vertKern
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hSz : AEMeasurable (fun w : ℝ => S (z - w)) volume :=
    (hSm.comp (measurable_const.sub measurable_id)).aemeasurable
  have hglm : AEMeasurable gl volume :=
    (hg'.comp (measurable_const.mul measurable_id)).aemeasurable
  have hconj : (22 / 3 : ℝ).HolderConjugate (22 / 19) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hH : ∫⁻ w : ℝ, S (z - w) * gl w ≤ lqNorm1 (22 / 3) (fun w => S (z - w)) * lqNorm1 (22 / 19) gl :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hSz hglm
  have htrans : lqNorm1 (22 / 3) (fun w => S (z - w)) = lqNorm1 (22 / 3) S := by
    unfold lqNorm1
    congr 1
    exact lintegral_sub_left_eq_self (fun t => S t ^ (22 / 3 : ℝ)) z
  have hdil : lqNorm1 (22 / 19) gl = ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) * lqNorm1 (22 / 19) g' :=
    hD2 (22 / 19) (by norm_num) g'
  have hid : ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) =
      ENNReal.ofReal (l ^ (-(3 / 22 : ℝ))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_neg_one, ← Real.rpow_add hl0]
    norm_num
  rw [hD1 S g' z]
  calc ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * gl w
      ≤ ENNReal.ofReal l⁻¹ * (lqNorm1 (22 / 3) (fun w => S (z - w)) * lqNorm1 (22 / 19) gl) :=
        mul_le_mul_of_nonneg_left hH zero_le
    _ = ENNReal.ofReal l⁻¹ * (lqNorm1 (22 / 3) S *
          (ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) * lqNorm1 (22 / 19) g')) := by
        rw [htrans, hdil]
    _ ≤ ENNReal.ofReal l⁻¹ * (ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          (ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) * lqNorm1 (22 / 19) g')) := by
        gcongr
        exact hKb rIn D hrIn hD0
    _ = ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          ((ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ)))) * lqNorm1 (22 / 19) g') := by
        ring
    _ = _ := by rw [hid]

/-- Pointwise bound on `vertRedH a rIn D h τ z` via `ops_vertHolderScaled` and `periodicDilationSum_proved`. -/
private theorem ops_vertPointwiseSup :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a rIn D P : ℝ), 3 / 2 ≤ a → 0 < D → 0 < rIn → 0 < P → P ≤ 1 →
      ∀ h : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry h) → (∀ τ s, h (τ + P) s = h τ s) →
        ∀ (τ z : ℝ), vertRedH a rIn D h τ z ≤
          ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * ltauLq1 P (22 / 19) h := by
  obtain ⟨C1, hC1, hH⟩ := ops_vertHolderScaled
  obtain ⟨C2, hC2, hS⟩ := periodicDilationSum_proved 1 one_pos
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro a rIn D P ha hD hrIn hP hP1 h hhm hper τ z
  set G : ℝ → ℝ≥0∞ := fun s => lqNorm1 (22 / 19) (h s) with hG
  have hGm : Measurable G := by
    simp only [hG]
    unfold lqNorm1
    have : Measurable fun s => ∫⁻ y, h s y ^ (22 / 19 : ℝ) :=
      (hhm.pow_const (22 / 19 : ℝ)).lintegral_prod_right'
    exact this.pow_const _
  have hGper : ∀ s, G (s + P) = G s := by
    intro s
    have h' := funext (hper s)
    simp only [hG, h']
  have hhτ : ∀ l : ℝ, Measurable (h (τ + 2 * Real.log l)) := fun l =>
    hhm.comp (measurable_const.prodMk measurable_id)
  have hc : (1 : ℝ) - 1 ≤ a - 3 / 22 := by linarith
  calc vertRedH a rIn D h τ z
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          (ENNReal.ofReal (l ^ (a - 3 / 22)) * G (τ + 2 * Real.log l)) := by
        unfold vertRedH
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have h1 := hH rIn D hrIn hD l hl.1 hl.2 _ (hhτ l) z
        calc ENNReal.ofReal (l ^ a) *
              ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s
            ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
                (ENNReal.ofReal (l ^ (-(3 / 22 : ℝ))) * G (τ + 2 * Real.log l))) :=
              mul_le_mul' le_rfl h1
          _ = ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
                (ENNReal.ofReal (l ^ (a - 3 / 22)) * G (τ + 2 * Real.log l)) := by
              have : l ^ (a - 3 / 22) = l ^ a * l ^ (-(3 / 22 : ℝ)) := by
                rw [sub_eq_add_neg, Real.rpow_add hl.1]
              rw [this, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
              ring
    _ = ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 / 22)) * G (τ + 2 * Real.log l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          (ENNReal.ofReal C2 * IIIa.ltauAt P G) :=
        mul_le_mul' le_rfl (hS (a - 3 / 22) hc P hP hP1 G hGm hGper τ)
    _ = ENNReal.ofReal (C1 * C2 * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          ltauLq1 P (22 / 19) h := by
        rw [ltauAt_lqNorm1_eq P (22 / 19) h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- Scalar exponent identity for `OutPrimPointwiseSup`: `(-2 + 3/22) + 3/11 = -35/22`. -/
private theorem ops_alg (Cy R ν : ℝ) (hν : 0 < ν) (hR : 0 < R) :
    (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
        (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 22 : ℝ)) *
        (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) =
      Cy * ((Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) *
        (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ)) := by
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  have hsq56 : Real.sqrt (5 / 6 : ℝ) ^ 2 = 5 / 6 := Real.sq_sqrt (by norm_num)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hG : Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2 =
      (Real.pi * (5 / 6)) * (R * Real.sqrt ν) ^ 2 := by
    rw [hrO, mul_pow (Real.sqrt (5 / 6 : ℝ)), hsq56]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hB : (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) =
      (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) := by
    rw [hG, Real.mul_rpow (mul_nonneg Real.pi_pos.le (by norm_num)) (sq_nonneg _),
      outAnn7_alg_pow _ hrIn0]
  have hDp : (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 22 : ℝ) =
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) *
        (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ) := by
    rw [hD, Real.mul_rpow hd0.le hrIn0.le]
  have hq : (R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) =
      (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ := by
    rw [hD, mul_comm (1 - Real.sqrt (5 / 6 : ℝ)),
      div_mul_eq_div_div, div_self hrIn0.ne', one_div]
  have hexp : (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) =
      (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ)) := by
    rw [← Real.rpow_add hrIn0]
    congr 1; norm_num
  rw [hB, hDp, hq]
  calc (Cy * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ *
        ((1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) *
          (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ))) *
        ((Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ))
      = Cy * ((Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
          (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) *
          ((R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ)) := by ring
    _ = _ := by rw [hexp]

/-- Pointwise bound on `outMaj` for `r ≥ R * Real.sqrt ν`. -/
private theorem ops_outMajPointwiseSup :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R P a : ℝ), 0 < ν → 0 < R → 0 < P → P ≤ 1 → 3 / 2 ≤ a →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
        (∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        ∀ (τ r z : ℝ), R * Real.sqrt ν ≤ r →
          outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ r z ≤
            ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
              IIIa.ltauLq P (22 / 19) g := by
  obtain ⟨Cy, hCy, hY⟩ := ops_vertPointwiseSup
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  set K : ℝ := (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
    (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (mul_nonneg Real.pi_pos.le (by norm_num)) _)
    (Real.rpow_nonneg hd0.le _)) (inv_nonneg.2 hd0.le)
  refine ⟨Cy * K, mul_nonneg hCy hK0, ?_⟩
  intro ν R P a hν hR hP0 hP1 ha g hgm hper hsupp τ r z hr
  set rIn := R * Real.sqrt ν
  set rOut := R * Real.sqrt (5 * ν / 6)
  set D := rIn - rOut
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < rIn := mul_pos hR hsν
  have hrOut0 : 0 ≤ rOut := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hrr : rOut < rIn := by
    have : 5 * ν / 6 < ν := by linarith
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by linarith) this) hR
  have hD0 : 0 < D := sub_pos.2 hrr
  have hvm := (vertMeasurable g hgm).1
  have hvper : ∀ t s, vprof g (t + P) s = vprof g t s := by
    intro t s; unfold vprof; simp only [hper]
  have hred := outMajReduce a rOut rIn hrOut0 hrr g hgm hsupp τ r z hr
  have hy := hY a rIn D P ha hD0 hrIn0 hP0 hP1 (vprof g) hvm hvper τ z
  have hvh := vprofHolder rOut P hrOut0 hP0 g hgm hsupp
  have hB0 : 0 ≤ Cy * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ) :=
    mul_nonneg (mul_nonneg hCy (div_nonneg hrIn0.le hD0.le)) (Real.rpow_nonneg hD0.le _)
  have hG0 : 0 ≤ (Real.pi * rOut ^ 2) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _
  calc outMaj a D g τ r z
      ≤ vertRed a rIn D g τ z := hred
    _ ≤ ENNReal.ofReal (Cy * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          ltauLq1 P (22 / 19) (vprof g) := hy
    _ ≤ ENNReal.ofReal (Cy * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          (ENNReal.ofReal ((Real.pi * rOut ^ 2) ^ (3 / 22 : ℝ)) *
            IIIa.ltauLq P (22 / 19) g) :=
        mul_le_mul_of_nonneg_left hvh zero_le
    _ = ENNReal.ofReal ((Cy * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          (Real.pi * rOut ^ 2) ^ (3 / 22 : ℝ)) * IIIa.ltauLq P (22 / 19) g := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hB0]
    _ = ENNReal.ofReal (Cy * K * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
          IIIa.ltauLq P (22 / 19) g := by
        rw [ops_alg Cy R ν hν hR]

/-- **Leaf 2 (`PartIII-b:C/rep/3/1/2`): pointwise `L^∞_{τ,y}` bounds on `wgyWPsi` and `wgxPsi`**
(source 3687-3713, 4178-4186, 5238-5244). -/
theorem outPrimPointwiseSup : OutPrimPointwiseSup := by
  intro σ₁ σ₂ hσ
  obtain ⟨C0, hC0, hpt⟩ := outPrimPointwise_of IIIa.sepWDominated IIIa.sepKernelBounds σ₁ σ₂ hσ
  obtain ⟨C, hC, hann⟩ := ops_outMajPointwiseSup
  refine ⟨2 * C0 * C, by positivity, ?_⟩
  intro ν μ R P hν hR hP0 hP1 hμ T hT _hmom τ y
  have hrO0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by nlinarith)) hR
  have ha : 3 / 2 ≤ 2 * μ + 2 := by linarith [hμ.1]
  have hX0 : 0 ≤ (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ)) := by positivity
  by_cases hy : y ∈ streamAnn ν R
  · obtain ⟨hW, hX⟩ := hpt ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hrO0 hlt hP0
      T hT τ (ϱ y) (y 2) hy.1
    have hM := hann ν R P (2 * μ + 2) hν hR hP0 hP1 ha (IIIa.srcNorm T) (srcNorm_measurable hT)
      (fun s z => by simp only [IIIa.srcNorm, hT.periodic s z])
      (fun s z hz => by simp [IIIa.srcNorm, hT.support s z hz, IIIa.tensorNorm])
      τ (ϱ y) (y 2) hy.1
    unfold wgyWPsi wgxPsi
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    refine ⟨?_, ?_⟩
    · calc ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)|
          ≤ ENNReal.ofReal C0 *
              outMaj (2 * μ + 2) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
                (IIIa.srcNorm T) τ (ϱ y) (y 2) := hW
        _ ≤ ENNReal.ofReal C0 *
              (ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) :=
            mul_le_mul_of_nonneg_left hM zero_le
        _ = ENNReal.ofReal (C0 * C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hC0, mul_assoc]
        _ ≤ ENNReal.ofReal (2 * C0 * C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
            gcongr
            nlinarith
    · have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      calc ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|
          ≤ ENNReal.ofReal C0 * (2 *
              outMaj (2 * μ + 2) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
                (IIIa.srcNorm T) τ (ϱ y) (y 2)) := hX
        _ ≤ ENNReal.ofReal C0 * (2 *
              (ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM zero_le) zero_le
        _ = ENNReal.ofReal (2 * C0 * C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
            rw [h2, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hC0,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring
  · unfold wgyWPsi wgxPsi
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    exact ⟨zero_le, zero_le⟩

end UnforcedLeray.Short.PartIIIb.Concrete

end
