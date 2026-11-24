import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3

/-!


Source of record: `the November 2 reference manuscript`, lines 1684-1689.

The Prop `LimitStep` says: if the weak divergence and curl pairings of an `L²(cell)` field `w`
vanish on cylinder tests `ψ'` arbitrarily `W^{1,2}`-close to `ψ`, they vanish at `ψ`.
The proof bounds `|divI w ψ| = |divI w ψ - divI w ψ'|` by `(‖w₀‖ + ‖w₁‖) · ‖∇ψ - ∇ψ'‖_{L²(cell)}`
(Hölder with exponents 2, 2 on the cell), and lets the `W^{1,2}`-distance tend to zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

/-- The complex norm of a real number, as an extended norm. -/
private lemma ls_enorm_ofReal (a : ℝ) : ‖(a : ℂ)‖ₑ = ‖a‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

/-- Hölder (exponents `2, 2`) for the paired integrand `w₀ α + w₁ β` with `|α|, |β| ≤ ℓ`. -/
private lemma ls_key {μ : Measure (ℝ × ℝ)} (w0 w1 : ℝ × ℝ → ℂ)
    (hw0 : MemLp w0 2 μ) (hw1 : MemLp w1 2 μ) (α β : ℝ × ℝ → ℝ) (ℓ : ℝ × ℝ → ℝ≥0∞)
    (hℓ : AEMeasurable ℓ μ) (hα : ∀ z, ‖α z‖ₑ ≤ ℓ z) (hβ : ∀ z, ‖β z‖ₑ ≤ ℓ z) :
    ‖∫ z, (w0 z * (α z : ℂ) + w1 z * (β z : ℂ)) ∂μ‖ₑ ≤
      (eLpNorm w0 2 μ + eLpNorm w1 2 μ) * (∫⁻ z, ℓ z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  have hpt : ∀ z, ‖w0 z * (α z : ℂ) + w1 z * (β z : ℂ)‖ₑ ≤ ‖w0 z‖ₑ * ℓ z + ‖w1 z‖ₑ * ℓ z := by
    intro z
    calc ‖w0 z * (α z : ℂ) + w1 z * (β z : ℂ)‖ₑ
        ≤ ‖w0 z * (α z : ℂ)‖ₑ + ‖w1 z * (β z : ℂ)‖ₑ := enorm_add_le _ _
      _ = ‖w0 z‖ₑ * ‖α z‖ₑ + ‖w1 z‖ₑ * ‖β z‖ₑ := by
          rw [enorm_mul, enorm_mul, ls_enorm_ofReal, ls_enorm_ofReal]
      _ ≤ ‖w0 z‖ₑ * ℓ z + ‖w1 z‖ₑ * ℓ z :=
          add_le_add (mul_le_mul_of_nonneg_left (hα z) (by positivity)) (mul_le_mul_of_nonneg_left (hβ z) (by positivity))
  have hm0 : AEMeasurable (fun z => ‖w0 z‖ₑ) μ := hw0.aestronglyMeasurable.aemeasurable.enorm
  have hm1 : AEMeasurable (fun z => ‖w1 z‖ₑ) μ := hw1.aestronglyMeasurable.aemeasurable.enorm
  have e0 : eLpNorm w0 2 μ = (∫⁻ z, ‖w0 z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  have e1 : eLpNorm w1 2 μ = (∫⁻ z, ‖w1 z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  have hH0 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hm0 hℓ
  have hH1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hm1 hℓ
  have hA : ∫⁻ z, ‖w0 z‖ₑ * ℓ z ∂μ ≤
      eLpNorm w0 2 μ * (∫⁻ z, ℓ z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [e0]
    exact hH0
  have hB : ∫⁻ z, ‖w1 z‖ₑ * ℓ z ∂μ ≤
      eLpNorm w1 2 μ * (∫⁻ z, ℓ z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [e1]
    exact hH1
  have hsplit : ∫⁻ z, (‖w0 z‖ₑ * ℓ z + ‖w1 z‖ₑ * ℓ z) ∂μ =
      (∫⁻ z, ‖w0 z‖ₑ * ℓ z ∂μ) + ∫⁻ z, ‖w1 z‖ₑ * ℓ z ∂μ :=
    lintegral_add_left' (hm0.mul hℓ) _
  calc ‖∫ z, (w0 z * (α z : ℂ) + w1 z * (β z : ℂ)) ∂μ‖ₑ
      ≤ ∫⁻ z, ‖w0 z * (α z : ℂ) + w1 z * (β z : ℂ)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z, (‖w0 z‖ₑ * ℓ z + ‖w1 z‖ₑ * ℓ z) ∂μ := lintegral_mono hpt
    _ = (∫⁻ z, ‖w0 z‖ₑ * ℓ z ∂μ) + ∫⁻ z, ‖w1 z‖ₑ * ℓ z ∂μ := hsplit
    _ ≤ eLpNorm w0 2 μ * (∫⁻ z, ℓ z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) +
          eLpNorm w1 2 μ * (∫⁻ z, ℓ z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := add_le_add hA hB
    _ = (eLpNorm w0 2 μ + eLpNorm w1 2 μ) * (∫⁻ z, ℓ z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
          (add_mul _ _ _).symm

/-- A quantity bounded by `K √ε` for every `ε > 0`, with `K` finite, vanishes. -/
private lemma ls_eq_zero_of_small (x : ℂ) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ‖x‖ₑ ≤ K * ENNReal.ofReal (Real.sqrt ε)) : x = 0 := by
  rw [← enorm_eq_zero]
  refine le_antisymm ?_ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rw [zero_add]
  have hδ' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hK0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hKe : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hK
  have htpos : 0 < (δ : ℝ) / (K.toReal + 1) := div_pos hδ' (by linarith)
  have h1 := h (((δ : ℝ) / (K.toReal + 1)) ^ 2) (by positivity)
  rw [Real.sqrt_sq htpos.le] at h1
  have key : K.toReal * ((δ : ℝ) / (K.toReal + 1)) ≤ (δ : ℝ) := by
    rw [mul_div_assoc', div_le_iff₀ (show (0 : ℝ) < K.toReal + 1 by linarith)]
    nlinarith
  have hK' : K * ENNReal.ofReal ((δ : ℝ) / (K.toReal + 1)) =
      ENNReal.ofReal (K.toReal * ((δ : ℝ) / (K.toReal + 1))) := by
    rw [ENNReal.ofReal_mul hK0, hKe]
  refine h1.trans (le_of_eq_of_le hK' ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal key

/-- The paired cell integral of two cylinder tests, passing from `ψ'` to `ψ`. -/
private lemma ls_bound {c : ℝ} (w0 w1 : ℝ × ℝ → ℂ)
    (hw0 : MemLp w0 2 (UnforcedLeray.Cyl.cellμ c)) (hw1 : MemLp w1 2 (UnforcedLeray.Cyl.cellμ c))
    (v0 v1 : ℝ × ℝ) (hv0 : ‖v0‖ ≤ 1) (hv1 : ‖v1‖ ≤ 1)
    {ψ ψ' : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.Sob.IsCylTest c ψ)
    (hψ' : UnforcedLeray.Sob.IsCylTest c ψ')
    (hG' : ∫ z in UnforcedLeray.Cyl.cell c,
      (w0 z * (fderiv ℝ ψ' z v0 : ℂ) + w1 z * (fderiv ℝ ψ' z v1 : ℂ)) = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hlt : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ^ 2
      < ENNReal.ofReal ε) :
    ‖∫ z in UnforcedLeray.Cyl.cell c,
      (w0 z * (fderiv ℝ ψ z v0 : ℂ) + w1 z * (fderiv ℝ ψ z v1 : ℂ))‖ₑ ≤
      (eLpNorm w0 2 (UnforcedLeray.Cyl.cellμ c) + eLpNorm w1 2 (UnforcedLeray.Cyl.cellμ c)) *
        ENNReal.ofReal (Real.sqrt ε) := by
  have hA0 : IntegrableOn (fun z => w0 z * (fderiv ℝ ψ z v0 : ℂ)) (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Short.IIIa.CTE.T20_2.integrableOn_test_mul_C (hψ.dirDeriv v0) hw0
  have hA1 : IntegrableOn (fun z => w1 z * (fderiv ℝ ψ z v1 : ℂ)) (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Short.IIIa.CTE.T20_2.integrableOn_test_mul_C (hψ.dirDeriv v1) hw1
  have hB0 : IntegrableOn (fun z => w0 z * (fderiv ℝ ψ' z v0 : ℂ)) (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Short.IIIa.CTE.T20_2.integrableOn_test_mul_C (hψ'.dirDeriv v0) hw0
  have hB1 : IntegrableOn (fun z => w1 z * (fderiv ℝ ψ' z v1 : ℂ)) (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Short.IIIa.CTE.T20_2.integrableOn_test_mul_C (hψ'.dirDeriv v1) hw1
  have hsumA : IntegrableOn (fun z => w0 z * (fderiv ℝ ψ z v0 : ℂ) +
      w1 z * (fderiv ℝ ψ z v1 : ℂ)) (UnforcedLeray.Cyl.cell c) := hA0.add hA1
  have hsumB : IntegrableOn (fun z => w0 z * (fderiv ℝ ψ' z v0 : ℂ) +
      w1 z * (fderiv ℝ ψ' z v1 : ℂ)) (UnforcedLeray.Cyl.cell c) := hB0.add hB1
  have hFint : IntegrableOn (fun z => w0 z * ((fderiv ℝ ψ z v0 - fderiv ℝ ψ' z v0 : ℝ) : ℂ) +
      w1 z * ((fderiv ℝ ψ z v1 - fderiv ℝ ψ' z v1 : ℝ) : ℂ)) (UnforcedLeray.Cyl.cell c) := by
    refine (hsumA.sub hsumB).congr_fun ?_ (measurableSet_Ico.prod MeasurableSet.univ)
    intro z _
    simp only [Pi.sub_apply, Pi.add_apply, Complex.ofReal_sub]
    ring
  have hsplit : ∫ z in UnforcedLeray.Cyl.cell c,
      (w0 z * (fderiv ℝ ψ z v0 : ℂ) + w1 z * (fderiv ℝ ψ z v1 : ℂ)) =
      ∫ z in UnforcedLeray.Cyl.cell c, (w0 z * ((fderiv ℝ ψ z v0 - fderiv ℝ ψ' z v0 : ℝ) : ℂ) +
        w1 z * ((fderiv ℝ ψ z v1 - fderiv ℝ ψ' z v1 : ℝ) : ℂ)) := by
    have hpt : ∫ z in UnforcedLeray.Cyl.cell c,
        (w0 z * (fderiv ℝ ψ z v0 : ℂ) + w1 z * (fderiv ℝ ψ z v1 : ℂ)) =
        ∫ z in UnforcedLeray.Cyl.cell c, ((w0 z * ((fderiv ℝ ψ z v0 - fderiv ℝ ψ' z v0 : ℝ) : ℂ) +
          w1 z * ((fderiv ℝ ψ z v1 - fderiv ℝ ψ' z v1 : ℝ) : ℂ)) +
          (w0 z * (fderiv ℝ ψ' z v0 : ℂ) + w1 z * (fderiv ℝ ψ' z v1 : ℂ))) := by
      congr 1
      funext z
      push_cast
      ring
    rw [hpt, integral_add hFint hsumB, hG', add_zero]
  rw [hsplit]
  have hbound : ∀ v : ℝ × ℝ, ‖v‖ ≤ 1 → ∀ z, ‖fderiv ℝ ψ z v - fderiv ℝ ψ' z v‖ₑ ≤
      ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ := by
    intro v hv z
    rw [← ContinuousLinearMap.sub_apply, ← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    calc ‖(fderiv ℝ ψ z - fderiv ℝ ψ' z) v‖
        ≤ ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ := mul_one _
  have hcont : Continuous (fun z => fderiv ℝ ψ z - fderiv ℝ ψ' z) :=
    (hψ.smooth.continuous_fderiv (by simp)).sub (hψ'.smooth.continuous_fderiv (by simp))
  have hℓm : AEMeasurable (fun z => ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ)
      (UnforcedLeray.Cyl.cellμ c) := hcont.enorm.aemeasurable
  refine (ls_key w0 w1 hw0 hw1 (fun z => fderiv ℝ ψ z v0 - fderiv ℝ ψ' z v0)
    (fun z => fderiv ℝ ψ z v1 - fderiv ℝ ψ' z v1) (fun z => ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ)
    hℓm (hbound v0 hv0) (hbound v1 hv1)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hlt' : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ^ (2 : ℝ)
      < ENNReal.ofReal ε := by
    simpa only [ENNReal.rpow_two] using hlt
  refine (ENNReal.rpow_le_rpow hlt'.le (by norm_num)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg hε.le (by norm_num), Real.sqrt_eq_rpow]

/-- The Prop `LimitStep` (source lines 1684-1689). -/
theorem limitStep : UnforcedLeray.Short.PartIIa.N01.Sub.LimitStep := by
  intro c hc w hw ψ hψ happrox
  have hK : eLpNorm (fun z => w z 0) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (fun z => w z 1) 2 (UnforcedLeray.Cyl.cellμ c) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(hw 0).eLpNorm_lt_top.ne, (hw 1).eLpNorm_lt_top.ne⟩
  have hcurl_eq : ∀ φ : ℝ × ℝ → ℝ, curlI c w φ = ∫ z in UnforcedLeray.Cyl.cell c,
      (w z 0 * (fderiv ℝ φ z (0, 1) : ℂ) + w z 1 * (fderiv ℝ φ z (-(1, 0)) : ℂ)) := by
    intro φ
    unfold curlI
    congr 1
    funext z
    rw [map_neg]
    push_cast
    ring
  constructor
  · refine ls_eq_zero_of_small (divI c w ψ) _ hK ?_
    intro ε hε
    obtain ⟨ψ', hψ't, hd, -, hlt⟩ := happrox ε hε
    exact ls_bound (fun z => w z 0) (fun z => w z 1) (hw 0) (hw 1) (1, 0) (0, 1)
      (by simp [Prod.norm_def]) (by simp [Prod.norm_def]) hψ hψ't hd ε hε hlt
  · refine ls_eq_zero_of_small (curlI c w ψ) _ hK ?_
    intro ε hε
    obtain ⟨ψ', hψ't, -, hd, hlt⟩ := happrox ε hε
    rw [hcurl_eq ψ'] at hd
    rw [hcurl_eq ψ]
    exact ls_bound (fun z => w z 0) (fun z => w z 1) (hw 0) (hw 1) (0, 1) (-(1, 0))
      (by simp [Prod.norm_def]) (by simp [Prod.norm_def]) hψ hψ't hd ε hε hlt

end UnforcedLeray.Short.PartIIa.N01.Sub
