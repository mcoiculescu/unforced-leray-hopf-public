import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_of

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **(3) The continuous representative is measurable in the parameter** (pure measure theory;
see the docstring of `ContRepMeasurable`).  Route: periodise `J` in `q` by `red`, average over
closed balls of radius `1/(n+1)`, and take the limit where it exists.  The averages of a
continuous periodic `H` with `J(σ,·) = H` a.e. on the cell converge to `H(y)` at every `y`,
so `Ψ(σ,·) = H` everywhere, with no separate uniqueness argument. -/
theorem contRepMeasurable : ContRepMeasurable := by
  intro c hc J hJm _hJc
  have hJv : Measurable J := measurable_pi_iff.mpr hJm
  -- periodisation of the `q`-variable into the cell
  obtain ⟨red, hred⟩ : ∃ red : ℝ × ℝ → ℝ × ℝ,
      red = fun z => (z.1 - c * ((⌊z.1 / c + 1 / 2⌋ : ℤ) : ℝ), z.2) := ⟨_, rfl⟩
  have hred_m : Measurable red := by
    rw [hred]
    fun_prop
  have hk : ∀ z : ℝ × ℝ, red z = z + (-(((⌊z.1 / c + 1 / 2⌋ : ℤ) : ℝ) * c), 0) := by
    intro z
    rw [hred]
    ext <;> simp <;> ring
  have hred_cell : ∀ z : ℝ × ℝ, red z ∈ UnforcedLeray.Cyl.cell c := by
    intro z
    rw [hred]
    have hz : z.1 / c * c = z.1 := div_mul_cancel₀ z.1 hc.ne'
    have h1 := Int.floor_le (z.1 / c + 1 / 2)
    have h2 := Int.lt_floor_add_one (z.1 / c + 1 / 2)
    have k1 := mul_le_mul_of_nonneg_left h1 hc.le
    have k2 := mul_lt_mul_of_pos_left h2 hc
    simp only [UnforcedLeray.Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true]
    constructor <;> nlinarith
  -- radii, volumes, averaging operators
  obtain ⟨rr, hrr⟩ : ∃ rr : ℕ → ℝ, rr = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hrr_pos : ∀ n, 0 < rr n := fun n => by
    rw [hrr]
    positivity
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℝ,
      V = fun n => volume.real (Metric.closedBall (0 : ℝ × ℝ) (rr n)) := ⟨_, rfl⟩
  have hVtrans : ∀ n (y : ℝ × ℝ), volume.real (Metric.closedBall y (rr n)) = V n := by
    intro n y
    rw [hV]
    simp only [Measure.real]
    rw [Measure.addHaar_closedBall_center]
  have hVpos : ∀ n, 0 < V n := by
    intro n
    rw [hV]
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos _ _ (hrr_pos n)).ne'
      measure_closedBall_lt_top.ne
  obtain ⟨g, hg_def⟩ : ∃ g : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) → (Fin 2 → ℂ),
      g = fun x => J (x.1.1, red x.2) := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S : ℕ → Set ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)),
      S = fun n => {x | dist x.2 x.1.2 ≤ rr n} := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ × (ℝ × ℝ) → (Fin 2 → ℂ),
      A = fun n p => (V n)⁻¹ • ∫ z, (S n).indicator g (p, z) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ × (ℝ × ℝ) → (Fin 2 → ℂ),
      Ψ = fun p => limUnder atTop (fun n => A n p) := ⟨_, rfl⟩
  have hg_m : Measurable g := by
    rw [hg_def]
    exact hJv.comp ((measurable_fst.comp measurable_fst).prodMk (hred_m.comp measurable_snd))
  have hS_m : ∀ n, MeasurableSet (S n) := by
    intro n
    rw [hS_def]
    exact measurableSet_le
      (continuous_snd.dist (continuous_snd.comp continuous_fst)).measurable measurable_const
  have hA_sm : ∀ n, StronglyMeasurable (A n) := by
    intro n
    rw [hA]
    have hf : StronglyMeasurable ((S n).indicator g) :=
      (hg_m.indicator (hS_m n)).stronglyMeasurable
    exact (StronglyMeasurable.integral_prod_right' hf).const_smul ((V n)⁻¹)
  have hΨm : Measurable Ψ := by
    rw [hΨ]
    exact (StronglyMeasurable.limUnder (fun n => hA_sm n)).measurable
  -- the main convergence statement
  have hconv : ∀ σ : ℝ, ∀ H : ℝ × ℝ → Fin 2 → ℂ, Continuous H →
      (∀ q η, H (q + c, η) = H (q, η)) →
      (fun y => J (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] H →
      ∀ y : ℝ × ℝ, Tendsto (fun n => A n (σ, y)) atTop (𝓝 (H y)) := by
    intro σ H hH hHp hae y
    have hae' : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.Cyl.cell c)), J (σ, x) = H x := hae
    have hcellM : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
      measurableSet_Ico.prod MeasurableSet.univ
    have hcell := (ae_restrict_iff' hcellM).mp hae'
    -- a.e. equality on the whole plane, by periodicity of `H`
    have hplane : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), J (σ, red z) = H z := by
      rw [ae_iff] at hcell ⊢
      have hsub : {z : ℝ × ℝ | ¬ J (σ, red z) = H z} ⊆ ⋃ k : ℤ,
          (fun w : ℝ × ℝ => w + (-((k : ℝ) * c), (0 : ℝ))) ⁻¹'
            {x | ¬ (x ∈ UnforcedLeray.Cyl.cell c → J (σ, x) = H x)} := by
        intro z hz
        simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
        refine ⟨⌊z.1 / c + 1 / 2⌋, ?_⟩
        rw [← hk z]
        intro himp
        apply hz
        have hper : Function.Periodic (fun q => H (q, z.2)) c := fun q => hHp q z.2
        have hs : H (z.1 - ((⌊z.1 / c + 1 / 2⌋ : ℤ) : ℝ) * c, z.2) = H (z.1, z.2) :=
          hper.sub_int_mul_eq (x := z.1) (⌊z.1 / c + 1 / 2⌋)
        have e2 : z + (-(((⌊z.1 / c + 1 / 2⌋ : ℤ) : ℝ) * c), 0) =
            (z.1 - ((⌊z.1 / c + 1 / 2⌋ : ℤ) : ℝ) * c, z.2) := by
          ext <;> simp <;> ring
        have hHred : H (red z) = H z := by
          rw [hk z, e2]
          exact hs
        exact (himp (hred_cell z)).trans hHred
      refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
      rw [measure_preimage_add_right]
      exact hcell
    -- the averages equal integrals of `H` over the balls
    have hint : ∀ n, ∫ z, (S n).indicator g ((σ, y), z) =
        ∫ z in Metric.closedBall y (rr n), H z := by
      intro n
      have e1 : (fun z => (S n).indicator g ((σ, y), z)) =
          (Metric.closedBall y (rr n)).indicator (fun z => J (σ, red z)) := by
        funext z
        by_cases hz : z ∈ Metric.closedBall y (rr n)
        · have hmem : ((σ, y), z) ∈ S n := by
            simp only [hS_def, Set.mem_setOf_eq]
            exact Metric.mem_closedBall.mp hz
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hz, hg_def]
        · have hmem : ((σ, y), z) ∉ S n := by
            simp only [hS_def, Set.mem_setOf_eq]
            exact fun h => hz (Metric.mem_closedBall.mpr h)
          rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hz]
      rw [e1, integral_indicator Metric.isClosed_closedBall.measurableSet]
      apply setIntegral_congr_ae Metric.isClosed_closedBall.measurableSet
      filter_upwards [hplane] with z hz _
      exact hz
    have hAH : ∀ n, A n (σ, y) = (V n)⁻¹ • ∫ z in Metric.closedBall y (rr n), H z := by
      intro n
      rw [hA]
      dsimp only
      rw [hint n]
    -- convergence of the averages
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hH.continuousAt (x := y)) (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hrn : rr n < δ := by
      rw [hrr]
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hIH : IntegrableOn H (Metric.closedBall y (rr n)) :=
      hH.continuousOn.integrableOn_compact (isCompact_closedBall y (rr n))
    have hconst : IntegrableOn (fun _ => H y) (Metric.closedBall y (rr n)) :=
      integrableOn_const measure_closedBall_lt_top.ne
    have hdiff : A n (σ, y) - H y =
        (V n)⁻¹ • ∫ z in Metric.closedBall y (rr n), (H z - H y) := by
      rw [hAH n, integral_sub hIH hconst, setIntegral_const, hVtrans n y, smul_sub, smul_smul,
        inv_mul_cancel₀ (hVpos n).ne', one_smul]
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hVpos n).le)]
    have hbd : ‖∫ z in Metric.closedBall y (rr n), (H z - H y)‖ ≤
        ε / 2 * volume.real (Metric.closedBall y (rr n)) := by
      apply norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top
      intro x hx
      rw [← dist_eq_norm]
      exact (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hrn)).le
    rw [hVtrans n y] at hbd
    calc (V n)⁻¹ * ‖∫ z in Metric.closedBall y (rr n), (H z - H y)‖
        ≤ (V n)⁻¹ * (ε / 2 * V n) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr (hVpos n).le)
      _ = ε / 2 := by rw [mul_comm (ε / 2), ← mul_assoc, inv_mul_cancel₀ (hVpos n).ne', one_mul]
      _ < ε := by linarith
  refine ⟨Ψ, fun i => (measurable_pi_apply i).comp hΨm, ?_⟩
  intro σ _hσ H hH hHp hae y
  rw [hΨ]
  exact (hconv σ H hH hHp hae y).limUnder_eq

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
