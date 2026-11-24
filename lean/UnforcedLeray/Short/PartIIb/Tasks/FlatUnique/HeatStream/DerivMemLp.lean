import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Smooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Tail
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Domination

/-!
# Part II-b, leaf `PartII-b:T11/3/9` (`HeatDerivMemLp`): `L^{r'}` membership of the derivatives

Source of record: `the November 2 reference manuscript`, SP 1923-1927.
Uses `heatConvSmooth` (`T11/3/2`), `heatConvTail` (`T11/3/7`) and `heatDerivDomination`
(`T11/3/8`). The `η`-marginal of the age-weighted measure on `[τ₁, τ₂] × ℝ_q × ℝ_η` is computed
as a product measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `η`-marginal of `ageμ c 0` restricted to `[τ₁, τ₂] × univ`. -/
theorem dmm_marginal (c τ₁ τ₂ : ℝ) (hτ₁ : 0 < τ₁) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∫⁻ x : Coord, f x.2.2 ∂((UnforcedLeray.Axi.ageμ c 0).restrict
        (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ))))
        = K * ∫⁻ η, f η := by
  refine ⟨ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (c / 2 - -c / 2) * ENNReal.ofReal (τ₂ - τ₁)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), ?_⟩
  have hsub : Icc τ₁ τ₂ ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hτ₁ ht.1
  have hinner : ∀ τ : ℝ,
      ∫⁻ y : ℝ × ℝ, f y.2 ∂((volume.restrict (Ico (-c / 2) (c / 2))).prod
        (volume.restrict (univ : Set ℝ)))
        = (∫⁻ η, f η) * ENNReal.ofReal (c / 2 - -c / 2) := by
    intro τ
    rw [lintegral_prod (fun y : ℝ × ℝ => f y.2) (hf.comp measurable_snd).aemeasurable]
    simp only [Measure.restrict_univ, lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Ico]
  unfold UnforcedLeray.Axi.ageμ UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  simp only [Real.rpow_zero, ENNReal.ofReal_one, withDensity_const, one_smul]
  rw [Measure.prod_smul_right, Measure.restrict_smul, lintegral_smul_measure]
  rw [← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr hsub, Measure.restrict_univ]
  rw [show UnforcedLeray.Cyl.cell c = Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) from rfl]
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
  rw [lintegral_prod (fun x : ℝ × (ℝ × ℝ) => f x.2.2)
    (hf.comp (measurable_snd.comp measurable_snd)).aemeasurable]
  simp only [smul_eq_mul, hinner 0, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Icc]
  ring

/-- A Gaussian-type integral over `ℝ` is finite. -/
theorem dmm_int_lt_top (A β : ℝ) (hβ : 0 < β) :
    ∫⁻ η : ℝ, ENNReal.ofReal (A * Real.exp (-β * η ^ 2)) < ⊤ :=
  ((integrable_exp_neg_mul_sq hβ).const_mul A).lintegral_lt_top

/-- Pointwise: `max 0 (|η| - L)²` is at least `η²/2 - L²`. -/
theorem dmm_sq_lower (L η : ℝ) :
    η ^ 2 / 2 - L ^ 2 ≤ (max 0 (|η| - L)) ^ 2 := by
  rcases le_or_gt |η| L with h | h
  · have hm : max 0 (|η| - L) = 0 := max_eq_left (by linarith)
    rw [hm]
    nlinarith [abs_nonneg η, sq_abs η, sq_nonneg L]
  · have hm : max 0 (|η| - L) = |η| - L := max_eq_right (by linarith)
    rw [hm]
    nlinarith [sq_nonneg (|η| - 2 * L), sq_abs η]

/-- Monotonicity of the Gaussian tail factor in the cutoff `L`. -/
theorem dmm_exp_mono (ν τ₂ L₁ L₂ η : ℝ) (hd : 0 < 8 * ν * τ₂) (h : L₁ ≤ L₂) :
    Real.exp (-((max 0 (|η| - L₁)) ^ 2) / (8 * ν * τ₂))
      ≤ Real.exp (-((max 0 (|η| - L₂)) ^ 2) / (8 * ν * τ₂)) := by
  apply Real.exp_le_exp.mpr
  have hm : max 0 (|η| - L₂) ≤ max 0 (|η| - L₁) := max_le_max le_rfl (by linarith)
  have hsq : (max 0 (|η| - L₂)) ^ 2 ≤ (max 0 (|η| - L₁)) ^ 2 :=
    pow_le_pow_left₀ (le_max_left _ _) hm 2
  exact div_le_div_of_nonneg_right (by linarith) hd.le

/-- **Leaf `PartII-b:T11/3/9`** (`L^{r'}` membership of the derivatives). -/
theorem heatDerivMemLp : UnforcedLeray.Short.IIb.HeatDerivMemLp := by
  intro c ν r' ζ hc hν hr' hζ n _hn τ₁ τ₂ hτ₁ hτ₁₂
  have hτ₂ : 0 < τ₂ := lt_of_lt_of_le hτ₁ hτ₁₂
  have hd : 0 < 8 * ν * τ₂ := mul_pos (mul_pos (by norm_num) hν) hτ₂
  have hr0 : (0 : ℝ) ≤ r' := by linarith
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hS : MeasurableSet (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hSsub : Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono (fun t ht => lt_of_lt_of_le hτ₁ ht.1) subset_rfl
  -- domination by finitely many nice heat flows
  obtain ⟨m, g, hg, hdom⟩ := heatDerivDomination c ν ζ n hc hν hζ
  have hT : ∀ j : Fin m, ∃ C L : ℝ, ∀ x : Coord, 0 < x.1 → x.1 ≤ τ₂ →
      |heatStreamH ν (g j) x| ≤ C * Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * ν * τ₂)) :=
    fun j => heatConvTail c ν (g j) τ₂ hc hν (hg j) hτ₂
  choose C L hCL using hT
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, ∀ j, L j ≤ Lb :=
    ⟨∑ j, |L j|, fun j => le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun k => |L k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j))⟩
  obtain ⟨Kb, hKbdef⟩ : ∃ Kb : ℝ, Kb = ∑ j, |C j| := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb := by
    rw [hKbdef]; exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
  -- pointwise bound of each term by the common cutoff `Lb`
  have hjb : ∀ j : Fin m, ∀ x : Coord, 0 < x.1 → x.1 ≤ τ₂ →
      |heatStreamH ν (g j) x|
        ≤ |C j| * Real.exp (-((max 0 (|x.2.2| - Lb)) ^ 2) / (8 * ν * τ₂)) := by
    intro j x h0 h1
    calc |heatStreamH ν (g j) x|
        ≤ C j * Real.exp (-((max 0 (|x.2.2| - L j)) ^ 2) / (8 * ν * τ₂)) := hCL j x h0 h1
      _ ≤ |C j| * Real.exp (-((max 0 (|x.2.2| - L j)) ^ 2) / (8 * ν * τ₂)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |C j| * Real.exp (-((max 0 (|x.2.2| - Lb)) ^ 2) / (8 * ν * τ₂)) :=
          mul_le_mul_of_nonneg_left (dmm_exp_mono ν τ₂ (L j) Lb x.2.2 hd (hLb j)) (abs_nonneg _)
  obtain ⟨B, hBdef⟩ : ∃ B : Coord → ℝ, ∀ x, B x =
      Kb * Real.exp (-((max 0 (|x.2.2| - Lb)) ^ 2) / (8 * ν * τ₂)) := ⟨_, fun x => rfl⟩
  have hBnn : ∀ x, 0 ≤ B x := fun x => by
    rw [hBdef x]; exact mul_nonneg hKb0 (Real.exp_pos _).le
  -- pointwise domination of the derivative
  have hbound : ∀ x ∈ Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ)),
      ‖iteratedFDeriv ℝ n (heatStreamH ν ζ) x‖ ≤ B x := by
    intro x hx
    have h0 : 0 < x.1 := lt_of_lt_of_le hτ₁ hx.1.1
    have h1 : x.1 ≤ τ₂ := hx.1.2
    rw [hBdef x, hKbdef, Finset.sum_mul]
    exact le_trans (hdom x h0) (Finset.sum_le_sum (fun j _ => hjb j x h0 h1))
  -- the measurability of the derivative
  have hcont : ContinuousOn (fun x : Coord => iteratedFDeriv ℝ n (heatStreamH ν ζ) x)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    have hsm := heatConvSmooth c ν ζ hc hν hζ
    have hc' := hsm.continuousOn_iteratedFDerivWithin (m := n) (by simp)
      hopen.uniqueDiffOn
    exact hc'.congr (iteratedFDerivWithin_of_isOpen n hopen).symm
  have hmeas : AEStronglyMeasurable (fun x : Coord => iteratedFDeriv ℝ n (heatStreamH ν ζ) x)
      ((UnforcedLeray.Axi.ageμ c 0).restrict (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ)))) :=
    (hcont.aestronglyMeasurable hopen.measurableSet).mono_set hSsub
  -- integrability of the bound
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = r' / (8 * ν * τ₂) := ⟨_, rfl⟩
  have hβ : 0 < β := by
    rw [hβdef]; exact div_pos (by linarith) hd
  have hpt : ∀ x : Coord, B x ^ r' ≤
      Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * x.2.2 ^ 2) := by
    intro x
    rw [hBdef x, Real.mul_rpow hKb0 (Real.exp_pos _).le, ← Real.exp_mul]
    have key := dmm_sq_lower Lb x.2.2
    have e1 : -((max 0 (|x.2.2| - Lb)) ^ 2) / (8 * ν * τ₂) * r'
        = -(β * (max 0 (|x.2.2| - Lb)) ^ 2) := by
      rw [hβdef]; ring
    rw [e1]
    have h2 : -(β * (max 0 (|x.2.2| - Lb)) ^ 2) ≤ β * Lb ^ 2 + -(β / 2) * x.2.2 ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left key hβ.le]
    have h3 : Real.exp (-(β * (max 0 (|x.2.2| - Lb)) ^ 2))
        ≤ Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * x.2.2 ^ 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr h2
    calc Kb ^ r' * Real.exp (-(β * (max 0 (|x.2.2| - Lb)) ^ 2))
        ≤ Kb ^ r' * (Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * x.2.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hKb0 _)
      _ = Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * x.2.2 ^ 2) := by ring

  have hGmeas : Measurable (fun η : ℝ =>
      ENNReal.ofReal (Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * η ^ 2))) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  obtain ⟨K0, hK0, hmarg⟩ := dmm_marginal c τ₁ τ₂ hτ₁
    (fun η : ℝ => ENNReal.ofReal (Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * η ^ 2)))
    hGmeas
  have hGint := dmm_int_lt_top (Kb ^ r' * Real.exp (β * Lb ^ 2)) (β / 2) (by linarith)
  have hBmeas : Measurable B := by
    have : B = fun x : Coord => Kb * Real.exp (-((max 0 (|x.2.2| - Lb)) ^ 2) / (8 * ν * τ₂)) :=
      funext hBdef
    rw [this]
    apply Continuous.measurable
    fun_prop
  have hBlint : ∫⁻ x : Coord, ‖B x‖ₑ ^ (ENNReal.ofReal r').toReal
      ∂((UnforcedLeray.Axi.ageμ c 0).restrict (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ)))) < ⊤ := by
    rw [ENNReal.toReal_ofReal hr0]
    have hle : ∀ x : Coord, ‖B x‖ₑ ^ r' ≤
        ENNReal.ofReal (Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * x.2.2 ^ 2)) := by
      intro x
      rw [Real.enorm_eq_ofReal (hBnn x), ENNReal.ofReal_rpow_of_nonneg (hBnn x) hr0]
      exact ENNReal.ofReal_le_ofReal (hpt x)
    calc ∫⁻ x : Coord, ‖B x‖ₑ ^ r'
          ∂((UnforcedLeray.Axi.ageμ c 0).restrict (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ))))
        ≤ ∫⁻ x : Coord, ENNReal.ofReal
            (Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * x.2.2 ^ 2))
            ∂((UnforcedLeray.Axi.ageμ c 0).restrict (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ)))) :=
          lintegral_mono (fun x => hle x)
      _ = K0 * ∫⁻ η : ℝ, ENNReal.ofReal
            (Kb ^ r' * Real.exp (β * Lb ^ 2) * Real.exp (-(β / 2) * η ^ 2)) := hmarg
      _ < ⊤ := ENNReal.mul_lt_top hK0.lt_top hGint
  refine MemLp.mono' ⟨hBmeas.aestronglyMeasurable, ?_⟩ hmeas ?_
  · exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 (by linarith)).ne'
      ENNReal.ofReal_ne_top).2 hBlint
  · exact ae_restrict_of_forall_mem hS (fun x hx => hbound x hx)

end UnforcedLeray.Short.IIb
