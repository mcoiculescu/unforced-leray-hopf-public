import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound.Young
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_4

/-!
# `L²` bound of the residual `Ẽ_μ` on the young support (`PartIII-b:C/ward/11`; source 4271-4294,
5196-5260, 5296-5297, 2683-2689)

Source of record: `the November 2 reference manuscript` (73 pages).

`Ẽ_μ = 2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX + DXᵀ)∇p` (4276-4280).  Every term contains a derivative
of `X` or `Y` (5296-5297), so `Ẽ_μ` vanishes near the chart points with `νs > 1` (4306-4311).  On the
young receiver region `ϱ ≥ R√ν`:

* the three velocity terms are bounded pointwise by the sup clause of `WardBgBoundL` times
  `|∂Y|, |∂²X|, |∂X|` (5225-5235), whose young chart readings are in `L²(s^{-3/2}dς)`
  (`WardXYoungL2`, `WardD2XYoungL2`, `WardDYYoungL2`);
* the pressure term is not bounded pointwise: `|(DX + DXᵀ)∇p| ≤ 18 max_j|∂_jX|·|∇p|`, and the source
  pairs the `L^∞_τL^∞_y` bound of `DX` on the young support (`WardDXYoungSup`, 5238-5244) with the
  `Y₂` clause of `∇p` (conjunct (2) of `WardBgBoundL`, 5245-5260).

The young chart reading of `∇p` need not be measurable (no regularity of `p` is assumed in
`WardEBoundL`), so the last step uses Minkowski's inequality with one measurable summand
(`web_eLpNorm_le_add`: the lower integral is attained by a measurable minorant).

* `web_eLpNorm_le_add`: `‖F‖₂ ≤ ‖G‖₂ + ‖P‖₂` when `|F| ≤ G + P`, `G` measurable;
* `web_pointwise`: the pointwise bound of the four-term residual;
* `wardEBoundL_of`: `WardEBoundL` from the four leaves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Minkowski with one measurable summand -/

/-- **Minkowski's inequality with one measurable summand**: if `|F| ≤ G + P` with `G ≥ 0`
measurable and `P ≥ 0` arbitrary, then `‖F‖₂ ≤ ‖G‖₂ + ‖P‖₂`.  The lower integral of `(G + P)²` is
that of a measurable minorant `φ`; `(√φ - G)₊` is a measurable minorant of `P` with
`φ ≤ (G + (√φ - G)₊)²`. -/
theorem web_eLpNorm_le_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] {F : α → E} {G P : α → ℝ}
    (hG : AEStronglyMeasurable G μ) (hG0 : ∀ x, 0 ≤ G x) (hP0 : ∀ x, 0 ≤ P x)
    (h : ∀ x, ‖F x‖ ≤ G x + P x) :
    eLpNorm F 2 μ ≤ eLpNorm G 2 μ + eLpNorm P 2 μ := by
  have hF : eLpNorm F 2 μ ≤ eLpNorm (fun x => G x + P x) 2 μ := eLpNorm_mono_real h
  refine hF.trans ?_
  have e2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have et : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal e2 et, ENNReal.toReal_ofNat]
  have hGe : ∀ x, ‖G x‖ₑ = ENNReal.ofReal (G x) := fun x => Real.enorm_of_nonneg (hG0 x)
  have hPe : ∀ x, ‖P x‖ₑ = ENNReal.ofReal (P x) := fun x => Real.enorm_of_nonneg (hP0 x)
  have hSe : ∀ x, ‖G x + P x‖ₑ = ENNReal.ofReal (G x) + ENNReal.ofReal (P x) := fun x => by
    rw [Real.enorm_of_nonneg (add_nonneg (hG0 x) (hP0 x)), ENNReal.ofReal_add (hG0 x) (hP0 x)]
  simp only [hGe, hPe, hSe]
  set g' : α → ℝ≥0∞ := fun x => ENNReal.ofReal (G x) with hg'
  set p' : α → ℝ≥0∞ := fun x => ENNReal.ofReal (P x) with hp'
  have hg'm : AEMeasurable g' μ := hG.aemeasurable.ennreal_ofReal
  obtain ⟨φ, hφm, hφle, hφeq⟩ :=
    exists_measurable_le_lintegral_eq (μ := μ) (fun x => (g' x + p' x) ^ (2 : ℝ))
  set r : α → ℝ≥0∞ := fun x => φ x ^ (1 / 2 : ℝ) with hr
  set ph : α → ℝ≥0∞ := fun x => r x - g' x with hph
  have hphm : AEMeasurable ph μ := (hφm.pow_const _).aemeasurable.sub hg'm
  have hr_le : ∀ x, r x ≤ g' x + p' x := by
    intro x
    have h1 := ENNReal.rpow_le_rpow (hφle x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h1
  have hph_le : ∀ x, ph x ≤ p' x := fun x => tsub_le_iff_left.2 (hr_le x)
  have hφ_le : ∀ x, φ x ≤ (g' x + ph x) ^ (2 : ℝ) := by
    intro x
    have h1 : r x ≤ g' x + ph x := le_add_tsub
    have h2 := ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
    have h3 : r x ^ (2 : ℝ) = φ x := by
      simp only [hr]
      rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rwa [h3] at h2
  calc (∫⁻ x, (g' x + p' x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      = (∫⁻ x, φ x ∂μ) ^ (1 / 2 : ℝ) := by rw [hφeq]
    _ ≤ (∫⁻ x, (g' + ph) x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun x => hφ_le x) (by norm_num)
    _ ≤ (∫⁻ x, g' x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ x, ph x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_Lp_add_le hg'm hphm one_le_two
    _ ≤ (∫⁻ x, g' x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ x, p' x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        refine add_le_add le_rfl (ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num))
        exact ENNReal.rpow_le_rpow (hph_le x) (by norm_num)

/-! ## 2. The pointwise bound of the residual -/

theorem web_fderiv_le {M : ℝ} {u Y : Space → Space} {y : Space} (hU : ‖u y‖ ≤ M) :
    ‖fderiv ℝ Y y (u y)‖ ≤ M * ∑ k : Fin 3, ‖physPd Y k y‖ := by
  refine (wyl_fderiv_apply_norm_le Y y (u y)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_right ((wyl_abs_apply_le _ k).trans hU) (norm_nonneg _)

theorem web_cdiff_le {M : ℝ} {u X : Space → Space} {y : Space}
    (hdU : ∀ j : Fin 3, ‖physPd u j y‖ ≤ M) (hd2U : ∀ j l : Fin 3, ‖physPd2 u j l y‖ ≤ M) :
    ‖physCdiff u X y‖ ≤
      M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ +
        M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd X j y‖ := by
  unfold physCdiff
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((wyl_abs_apply_le _ l).trans (hdU j)) (norm_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul (wyl_abs_apply_le _ l) (hd2U j l) (norm_nonneg _) (norm_nonneg _)

theorem web_uud2_le {M : ℝ} {u X : Space → Space} {y : Space} (hU : ‖u y‖ ≤ M) :
    ‖physUUD2 u X y‖ ≤ M * M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hU
  unfold physUUD2
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact mul_le_mul ((wyl_abs_apply_le _ j).trans hU) ((wyl_abs_apply_le _ l).trans hU)
    (abs_nonneg _) hM

theorem web_dxp_le {A : ℝ} {X : Space → Space} {q : Space → ℝ} {y : Space}
    (hA : ∀ j : Fin 3, ‖physPd X j y‖ ≤ A) :
    ‖physDXp X q y‖ ≤ 18 * A * ‖physGrad q y‖ := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (wyl_norm_le_sum_abs _).trans ?_
  have hi : ∀ i : Fin 3, |physDXp X q y i| ≤ 6 * A * ‖physGrad q y‖ := by
    intro i
    have hcomp : physDXp X q y i = ∑ j : Fin 3,
        (physPd X j y i + physPd X i y j) * physGrad q y j := by
      simp [physDXp, physGrad]
    rw [hcomp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j : Fin 3, |(physPd X j y i + physPd X i y j) * physGrad q y j| ≤
        2 * A * ‖physGrad q y‖ := by
      intro j
      rw [abs_mul]
      refine mul_le_mul ?_ (wyl_abs_apply_le _ j) (abs_nonneg _) (by positivity)
      refine (abs_add_le _ _).trans ?_
      have h1 := (wyl_abs_apply_le (physPd X j y) i).trans (hA j)
      have h2 := (wyl_abs_apply_le (physPd X i y) j).trans (hA i)
      linarith
    calc ∑ j : Fin 3, |(physPd X j y i + physPd X i y j) * physGrad q y j|
        ≤ ∑ _j : Fin 3, 2 * A * ‖physGrad q y‖ := Finset.sum_le_sum fun j _ => hj j
      _ = 6 * A * ‖physGrad q y‖ := by simp [Finset.sum_const]; ring
  calc ∑ i : Fin 3, |physDXp X q y i| ≤ ∑ _i : Fin 3, 6 * A * ‖physGrad q y‖ :=
        Finset.sum_le_sum fun i _ => hi i
    _ = 18 * A * ‖physGrad q y‖ := by simp [Finset.sum_const]; ring

/-- **The four-term residual on the young support** (source 4276-4280, 5225-5260). -/
theorem web_pointwise {M A ν : ℝ} (hν : 0 ≤ ν) {u X Y : Space → Space} {q : Space → ℝ}
    {y : Space} (hU : ‖u y‖ ≤ M) (hdU : ∀ j : Fin 3, ‖physPd u j y‖ ≤ M)
    (hd2U : ∀ j l : Fin 3, ‖physPd2 u j l y‖ ≤ M) (hA : ∀ j : Fin 3, ‖physPd X j y‖ ≤ A) :
    ‖(2 : ℝ) • fderiv ℝ Y y (u y) - (2 * ν) • physCdiff u X y + physUUD2 u X y -
        physDXp X q y‖ ≤
      2 * M * ∑ k : Fin 3, ‖physPd Y k y‖ +
        2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ +
          M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd X j y‖) +
        M * M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ +
        18 * A * ‖physGrad q y‖ := by
  have h1 : ‖(2 : ℝ) • fderiv ℝ Y y (u y)‖ ≤ 2 * M * ∑ k : Fin 3, ‖physPd Y k y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
    exact mul_le_mul_of_nonneg_left (web_fderiv_le hU) (by norm_num)
  have h2 : ‖(2 * ν) • physCdiff u X y‖ ≤
      2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ +
        M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd X j y‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (web_cdiff_le hdU hd2U) (by positivity)
  have h3 := web_uud2_le (X := X) hU
  have h4 := web_dxp_le (q := q) hA
  calc ‖(2 : ℝ) • fderiv ℝ Y y (u y) - (2 * ν) • physCdiff u X y + physUUD2 u X y -
        physDXp X q y‖
      ≤ ‖(2 : ℝ) • fderiv ℝ Y y (u y) - (2 * ν) • physCdiff u X y + physUUD2 u X y‖ +
          ‖physDXp X q y‖ := norm_sub_le _ _
    _ ≤ ‖(2 : ℝ) • fderiv ℝ Y y (u y) - (2 * ν) • physCdiff u X y‖ + ‖physUUD2 u X y‖ +
          ‖physDXp X q y‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖(2 : ℝ) • fderiv ℝ Y y (u y)‖ + ‖(2 * ν) • physCdiff u X y‖ + ‖physUUD2 u X y‖ +
          ‖physDXp X q y‖ := add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ _ := by linarith

/-! ## 3. Young support of the residual -/

theorem web_E_zero {ν μ R c : ℝ} {χy : ℝ → ℝ} (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (hν : 0 < ν) (hR : 0 < R) (hχy : IsYoungCutoff χy) (g : Chart → Ten3) {q : Chart}
    (hq : 1 < ν * q.1) (τ : ℝ) :
    wardE ν μ R c χy U p g τ (NearInst.chartY R q) = 0 := by
  have hX := (wyl_X_zero_nhds (μ := μ) (c := c) hν hR hχy g hq).self_of_nhds τ
  have hY := wyl_Y_zero_nhds (μ := μ) (c := c) hν hR hχy g hq τ
  have h1 : fderiv ℝ (wardY ν μ R c χy g τ) (NearInst.chartY R q) = 0 := by
    rw [hY.fderiv_eq]
    exact fderiv_const_apply _
  have h2 : ∀ j : Fin 3, physPd (wardX ν μ R c χy g τ) j (NearInst.chartY R q) = 0 :=
    fun j => (wyp_physPd_zero hX j).self_of_nhds
  have h3 : ∀ j l : Fin 3, physPd2 (wardX ν μ R c χy g τ) j l (NearInst.chartY R q) = 0 :=
    fun j l => wyp_physPd2_zero hX j l
  have hC : physCdiff (U τ) (wardX ν μ R c χy g τ) (NearInst.chartY R q) = 0 := by
    unfold physCdiff
    simp [h2, h3]
  have hUU : physUUD2 (U τ) (wardX ν μ R c χy g τ) (NearInst.chartY R q) = 0 := by
    unfold physUUD2
    simp [h3]
  have hD : physDXp (wardX ν μ R c χy g τ) (p τ) (NearInst.chartY R q) = 0 := by
    unfold physDXp
    ext i
    simp [h2]
  unfold wardE
  rw [h1, hC, hUU, hD]
  simp

/-! ## 4. Assembly -/

/-- **`WardEBoundL` from the leaves** (source 4271-4294, 5196-5260, 5296-5297, 2683-2689). -/
theorem wardEBoundL_of (hX : WardXYoungL2) (hX2 : WardD2XYoungL2) (hDY : WardDYYoungL2)
    (hsup : WardDXYoungSup) : WardEBoundL := by
  intro ν μ R c M χy U p hχy hν hR hc hμ hbg
  obtain ⟨C1, hC1⟩ := hX ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C2, hC2⟩ := hX2 ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C3, hC3⟩ := hDY ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C4, hC4⟩ := hsup ν μ R c χy hχy hν hR hc hμ
  have hM : 0 ≤ M := by
    set y₀ : Space := WithLp.toLp 2 ![R * Real.sqrt ν, 0, 0]
    have hy : R * Real.sqrt ν ≤ ϱ y₀ := by
      have h0 : y₀ 0 = R * Real.sqrt ν := by simp [y₀]
      have h1 : y₀ 1 = 0 := by simp [y₀]
      unfold ϱ
      rw [h0, h1, show (R * Real.sqrt ν) ^ 2 + (0 : ℝ) ^ 2 = (R * Real.sqrt ν) ^ 2 by ring,
        Real.sqrt_sq (mul_nonneg hR.le (Real.sqrt_nonneg _))]
    exact (norm_nonneg _).trans (hbg.1 0 y₀ hy).1
  set C1' := max C1 0 with hC1'
  set C2' := max C2 0 with hC2'
  set C3' := max C3 0 with hC3'
  set C4' := max C4 0 with hC4'
  have h1' : 0 ≤ C1' := le_max_right _ _
  have h2' : 0 ≤ C2' := le_max_right _ _
  have h3' : 0 ≤ C3' := le_max_right _ _
  have h4' : 0 ≤ C4' := le_max_right _ _
  set K₁ : ℝ := |2 * M| * ∑ _k : Fin 3, C3' +
    |2 * ν| * (|M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C2' + |M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C1') +
    |M * M| * ∑ _j : Fin 3, ∑ _l : Fin 3, C2' with hK₁
  refine ⟨Real.sqrt Real.pi * K₁ + 18 * C4' * M, fun g hg => ?_⟩
  set N := eLpNorm g 2 (ageμ c (-1 / 2)) with hN
  have hNt : N ≠ ⊤ := hg.memLp.2.ne
  set m := ageμ c (-3 / 2) with hm
  set X := wardX ν μ R c χy g with hXdef
  set Y := wardY ν μ R c χy g with hYdef
  obtain ⟨-, hdX⟩ := hC1 g hg
  have b1 : ∀ j : Fin 3, WylBd m N (wardYoungRead ν R fun τ => physPd (X τ) j) C1' :=
    fun j => wyl_bd_of_young (hdX j)
  have b2 : ∀ j l : Fin 3, WylBd m N (wardYoungRead ν R fun τ => physPd2 (X τ) j l) C2' :=
    fun j l => wyl_bd_of_young (hC2 g hg j l)
  have b3 : ∀ k : Fin 3, WylBd m N (wardYoungRead ν R fun τ => physPd (Y τ) k) C3' :=
    fun k => wyl_bd_of_young (hC3 g hg k)
  have t3 := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C3') (fun _ => h3')
    (fun k _ => b3 k)
  have t2 := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => ∑ _l : Fin 3, C2')
    (fun _ => Finset.sum_nonneg fun _ _ => h2')
    (fun j _ => WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C2') (fun _ => h2')
      (fun l _ => b2 j l))
  have t1 := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => ∑ _l : Fin 3, C1')
    (fun _ => Finset.sum_nonneg fun _ _ => h1')
    (fun j _ => WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C1') (fun _ => h1')
      (fun _ _ => b1 j))
  have s3 : 0 ≤ ∑ _k : Fin 3, C3' := Finset.sum_nonneg fun _ _ => h3'
  have s2 : 0 ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, C2' :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => h2'
  have s1 : 0 ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, C1' :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => h1'
  have tB := (((t3.const_mul (2 * M)).add (((t2.const_mul M).add (t1.const_mul M)
    (mul_nonneg (abs_nonneg _) s2) (mul_nonneg (abs_nonneg _) s1)).const_mul (2 * ν))
    (mul_nonneg (abs_nonneg _) s3) (mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (abs_nonneg _) s2) (mul_nonneg (abs_nonneg _) s1)))).add
    (t2.const_mul (M * M)) (add_nonneg (mul_nonneg (abs_nonneg _) s3) (mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (abs_nonneg _) s2) (mul_nonneg (abs_nonneg _) s1))))
    (mul_nonneg (abs_nonneg _) s2))
  set B : Chart → ℝ := fun q =>
    2 * M * ∑ k : Fin 3, wardYoungRead ν R (fun τ => physPd (Y τ) k) q +
      2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3, wardYoungRead ν R (fun τ => physPd2 (X τ) j l) q +
        M * ∑ j : Fin 3, ∑ _l : Fin 3, wardYoungRead ν R (fun τ => physPd (X τ) j) q) +
      M * M * ∑ j : Fin 3, ∑ l : Fin 3, wardYoungRead ν R (fun τ => physPd2 (X τ) j l) q
    with hBdef
  have tB' : WylBd m N B K₁ := tB
  set A : ℝ := C4' * N.toReal with hAdef
  have hA0 : 0 ≤ A := mul_nonneg h4' ENNReal.toReal_nonneg
  set Pp : Chart → ℝ := wardYoungRead ν R (fun τ y => physGrad (p τ) y) with hPp
  have hB0 : ∀ q, 0 ≤ B q := by
    intro q
    have r1 := fun k => wyl_youngRead_nonneg ν R (fun τ => physPd (Y τ) k) q
    have r2 := fun j l => wyl_youngRead_nonneg ν R (fun τ => physPd2 (X τ) j l) q
    have r3 := fun j => wyl_youngRead_nonneg ν R (fun τ => physPd (X τ) j) q
    have e1 : 0 ≤ ∑ k : Fin 3, wardYoungRead ν R (fun τ => physPd (Y τ) k) q :=
      Finset.sum_nonneg fun k _ => r1 k
    have e2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, wardYoungRead ν R (fun τ => physPd2 (X τ) j l) q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => r2 j l
    have e3 : 0 ≤ ∑ j : Fin 3, ∑ _l : Fin 3, wardYoungRead ν R (fun τ => physPd (X τ) j) q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => r3 j
    simp only [hBdef]
    have := mul_nonneg hM e2
    have := mul_nonneg hM e3
    have := mul_nonneg (mul_nonneg hM hM) e2
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) e1
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν.le)
      (add_nonneg (mul_nonneg hM e2) (mul_nonneg hM e3))
    linarith
  have hP0 : ∀ q, 0 ≤ 18 * A * Pp q := fun q =>
    mul_nonneg (mul_nonneg (by norm_num) hA0) (wyl_youngRead_nonneg _ _ _ q)
  -- pointwise domination of the chart coefficient
  have hpt : ∀ q, ‖coefOf R (wardE ν μ R c χy U p g) q‖ ≤ B q + 18 * A * Pp q := by
    refine wyl_coefOf_le (ν := ν) (fun q => add_nonneg (hB0 q) (hP0 q))
      (fun q hq => web_E_zero U p hν hR hχy g hq _) (fun q hs hq => ?_)
    set τ := NearInst.chartTau R q
    set y := NearInst.chartY R q
    have hy := wyl_young_ϱ hν hR hs hq
    obtain ⟨hU, hdU, hd2U⟩ := hbg.1 τ y hy
    have hAj : ∀ j : Fin 3, ‖physPd (X τ) j y‖ ≤ A := fun j =>
      (hC4 g hg τ y hy j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        ENNReal.toReal_nonneg)
    have key := web_pointwise (Y := Y τ) (q := p τ) hν.le hU hdU hd2U hAj
    have hi : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    simp only [hBdef, hPp, wyl_youngRead_of_young _ hq]
    calc (Real.sqrt q.1)⁻¹ * ‖wardE ν μ R c χy U p g τ y‖
        ≤ (Real.sqrt q.1)⁻¹ * (2 * M * ∑ k : Fin 3, ‖physPd (Y τ) k y‖ +
            2 * ν * (M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 (X τ) j l y‖ +
              M * ∑ j : Fin 3, ∑ _l : Fin 3, ‖physPd (X τ) j y‖) +
            M * M * ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 (X τ) j l y‖ +
            18 * A * ‖physGrad (p τ) y‖) := mul_le_mul_of_nonneg_left key hi
      _ = _ := by
          simp only [← Finset.mul_sum]
          ring
  -- Minkowski with the measurable part
  have hBm : AEStronglyMeasurable B (srcMeasure c) := by
    unfold srcMeasure
    exact tB'.1.smul_measure _
  have hmink := web_eLpNorm_le_add (μ := srcMeasure c) hBm hB0 hP0 hpt
  -- the pressure clause
  have hPpe : eLpNorm Pp 2 (srcMeasure c) ≤ ENNReal.ofReal M := by
    have heq : Pp = fun q => ‖({q : Chart | ν * q.1 ≤ 1}.indicator fun q : Chart =>
        (Real.sqrt q.1)⁻¹ • physGrad (p (NearInst.chartTau R q)) (NearInst.chartY R q)) q‖ := by
      funext q
      simp only [hPp, wardYoungRead, wardYoungSet]
      by_cases hq : q ∈ {q : Chart | ν * q.1 ≤ 1}
      · rw [indicator_of_mem hq, indicator_of_mem hq, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      · rw [indicator_of_notMem hq, indicator_of_notMem hq, norm_zero]
    rw [heq, eLpNorm_norm]
    exact hbg.2
  have hAP : eLpNorm (fun q => 18 * A * Pp q) 2 (srcMeasure c) ≤
      ENNReal.ofReal (18 * C4' * M) * N := by
    calc eLpNorm (fun q => 18 * A * Pp q) 2 (srcMeasure c)
        = eLpNorm ((18 * A) • Pp) 2 (srcMeasure c) := rfl
      _ = ‖18 * A‖ₑ * eLpNorm Pp 2 (srcMeasure c) := eLpNorm_const_smul _ _ _ _
      _ ≤ ‖18 * A‖ₑ * ENNReal.ofReal M := mul_le_mul' le_rfl hPpe
      _ = ENNReal.ofReal (18 * C4' * M) * N := by
          rw [Real.enorm_of_nonneg (by positivity), hAdef, ← ENNReal.ofReal_mul (by positivity)]
          rw [show 18 * (C4' * N.toReal) * M = 18 * C4' * M * N.toReal by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hNt]
  have hBs : eLpNorm B 2 (srcMeasure c) ≤ ENNReal.ofReal (Real.sqrt Real.pi * K₁) * N := by
    rw [wyl_eLpNorm_src]
    calc ENNReal.ofReal (Real.sqrt Real.pi) * eLpNorm B 2 (ageμ c (-3 / 2))
        ≤ ENNReal.ofReal (Real.sqrt Real.pi) * (ENNReal.ofReal K₁ * N) :=
          mul_le_mul' le_rfl tB'.2
      _ = ENNReal.ofReal (Real.sqrt Real.pi * K₁) * N := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  have hK₁ : 0 ≤ K₁ := by
    simp only [hK₁]
    have := mul_nonneg (abs_nonneg (2 * M)) s3
    have := mul_nonneg (abs_nonneg (2 * ν))
      (add_nonneg (mul_nonneg (abs_nonneg M) s2) (mul_nonneg (abs_nonneg M) s1))
    have := mul_nonneg (abs_nonneg (M * M)) s2
    linarith
  calc eLpNorm (coefOf R (wardE ν μ R c χy U p g)) 2 (srcMeasure c)
      ≤ eLpNorm B 2 (srcMeasure c) + eLpNorm (fun q => 18 * A * Pp q) 2 (srcMeasure c) := hmink
    _ ≤ ENNReal.ofReal (Real.sqrt Real.pi * K₁) * N + ENNReal.ofReal (18 * C4' * M) * N :=
        add_le_add hBs hAP
    _ = ENNReal.ofReal (Real.sqrt Real.pi * K₁ + 18 * C4' * M) * N := by
        rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (Real.sqrt_nonneg _) hK₁)
          (by positivity)]

/-- **`WardEBoundL` proved** (`PartIII-b:C/ward/11`, source 4271-4294, 5196-5260, 5296-5297). -/
theorem wardEBoundL_proved : WardEBoundL :=
  wardEBoundL_of wardXYoungL2_proved wardD2XYoungL2_proved wardDYYoungL2_proved
    wardDXYoungSup_proved

end UnforcedLeray.Short.PartIIIb.Concrete
