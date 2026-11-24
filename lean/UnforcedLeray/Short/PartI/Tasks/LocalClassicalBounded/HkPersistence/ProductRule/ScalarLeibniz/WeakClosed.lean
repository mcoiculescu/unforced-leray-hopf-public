import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1

/-!
# Part I, task `PartI:T02/1/2/3/1/1`: closedness of the periodic weak derivative

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target `bdp_weakClosed : BdpWeakClosed`. Admissible tests of the cylinder are bounded and
continuous, and vanish `μ`-a.e. outside a compact set `K`, so each pairing only sees the
restriction `μ.restrict K`, which is finite. The sequences `fs n` are not assumed measurable, so
the Cauchy-Schwarz step is done through a measurable minorant (`wc_cs_nonmeas`), which needs no
measurability of the integrand. The limit passes through `tendsto_integral_of_L1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Cauchy-Schwarz on a finite measure for an arbitrary `ℝ≥0∞`-valued function. The function
need not be measurable: integrate over a measurable minorant with the same integral. -/
theorem wc_cs_nonmeas {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (h : α → ℝ≥0∞) :
    ∫⁻ x, h x ∂ν ≤ (∫⁻ x, h x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * (ν Set.univ) ^ (1 / (2 : ℝ)) := by
  obtain ⟨m, hm, hmh, hint⟩ := exists_measurable_le_lintegral_eq (μ := ν) h
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (p := 2) (q := 2) Real.HolderConjugate.two_two
    hm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at hCS
  have hmono : ∫⁻ x, m x ^ (2 : ℝ) ∂ν ≤ ∫⁻ x, h x ^ (2 : ℝ) ∂ν :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (hmh x) (by norm_num)
  calc ∫⁻ x, h x ∂ν = ∫⁻ x, m x ∂ν := hint
    _ ≤ (∫⁻ x, m x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * (ν Set.univ) ^ (1 / (2 : ℝ)) := hCS
    _ ≤ (∫⁻ x, h x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * (ν Set.univ) ^ (1 / (2 : ℝ)) := by
      gcongr

/-- Pairings of a fixed test (bounded, continuous, a.e. supported in a compact `K`) with
sequences `g n` converge when `g n → G` in `L²(μ)`; the sequences need not be measurable. -/
theorem wc_tendsto_test {μ : Measure (ℝ × ℝ)} [IsFiniteMeasureOnCompacts μ] {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {ψ G : ℝ × ℝ → ℝ} (hψ : Continuous ψ)
    (hψK : ∀ᵐ x ∂μ, x ∉ K → ψ x = 0) (hG : AEStronglyMeasurable G μ)
    {g : ℕ → ℝ × ℝ → ℝ} (hgi : ∀ n, Integrable (fun x => ψ x * g n x) μ)
    (hconv : Tendsto (fun n => eLpNorm (g n - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ψ x * g n x ∂μ) atTop (𝓝 (∫ x, ψ x * G x ∂μ)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
  haveI : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  set Ce : ℝ≥0∞ := ENNReal.ofReal C with hCe
  have hCe_ne : Ce ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ n, ∀ᵐ x ∂μ, ‖ψ x * g n x - ψ x * G x‖ₑ ≤
      K.indicator (fun x => Ce * ‖(g n - G) x‖ₑ) x := by
    intro n
    filter_upwards [hψK] with x hx
    by_cases hxK : x ∈ K
    · have hbd : ‖ψ x‖ₑ ≤ Ce := by
        rw [hCe, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC x hxK)
      rw [indicator_of_mem hxK, ← mul_sub, enorm_mul]
      show ‖ψ x‖ₑ * ‖g n x - G x‖ₑ ≤ Ce * ‖g n x - G x‖ₑ
      gcongr
    · simp [hxK, hx hxK]
  have hbound : ∀ n, ∫⁻ x, ‖ψ x * g n x - ψ x * G x‖ₑ ∂μ ≤
      Ce * ∫⁻ x, ‖(g n - G) x‖ₑ ∂(μ.restrict K) := by
    intro n
    calc ∫⁻ x, ‖ψ x * g n x - ψ x * G x‖ₑ ∂μ
        ≤ ∫⁻ x, K.indicator (fun x => Ce * ‖(g n - G) x‖ₑ) x ∂μ := lintegral_mono_ae (hpt n)
      _ = ∫⁻ x in K, Ce * ‖(g n - G) x‖ₑ ∂μ := lintegral_indicator hK.isClosed.measurableSet _
      _ = Ce * ∫⁻ x in K, ‖(g n - G) x‖ₑ ∂μ := lintegral_const_mul' Ce _ hCe_ne
  have hS : ∀ n, eLpNorm (g n - G) 2 μ =
      (∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  have hcs : ∀ n, ∫⁻ x, ‖(g n - G) x‖ₑ ∂(μ.restrict K) ≤
      (∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (μ K) ^ (1 / (2 : ℝ)) := by
    intro n
    have h2 : ∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict K) ≤
        ∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂μ :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    calc ∫⁻ x, ‖(g n - G) x‖ₑ ∂(μ.restrict K)
        ≤ (∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict K)) ^ (1 / (2 : ℝ)) *
            ((μ.restrict K) Set.univ) ^ (1 / (2 : ℝ)) := wc_cs_nonmeas _ _
      _ ≤ (∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (μ K) ^ (1 / (2 : ℝ)) := by
        rw [Measure.restrict_apply_univ]
        gcongr
  have hB : Tendsto (fun n => Ce * ((∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
      (μ K) ^ (1 / (2 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (∫⁻ x, ‖(g n - G) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) atTop
        (𝓝 0) := by
      simpa only [hS] using hconv
    have h2 := ENNReal.Tendsto.mul_const h1
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / (2:ℝ)) (hK.measure_lt_top (μ := μ)).ne))
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hCe_ne)
    simpa using h3
  have hL1 : Tendsto (fun n => ∫⁻ x, ‖ψ x * g n x - ψ x * G x‖ₑ ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun n => zero_le)
      (fun n => le_trans (hbound n) (by gcongr; exact hcs n))
  exact tendsto_integral_of_L1 (F := fun n x => ψ x * g n x) (fun x => ψ x * G x)
    (hψ.aestronglyMeasurable.mul hG) (Eventually.of_forall hgi) hL1

/-- A bounded continuous test a.e. supported in a compact set is in `L²(μ)`. -/
theorem wc_memLp_test {μ : Measure (ℝ × ℝ)} [IsFiniteMeasureOnCompacts μ] {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {ψ : ℝ × ℝ → ℝ} (hψ : Continuous ψ)
    (hψK : ∀ᵐ x ∂μ, x ∉ K → ψ x = 0) : MemLp ψ 2 μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
  refine MemLp.of_le (g := K.indicator fun _ => C)
    (memLp_indicator_const 2 hK.isClosed.measurableSet C (Or.inr hK.measure_lt_top.ne))
    hψ.aestronglyMeasurable ?_
  filter_upwards [hψK] with x hx
  by_cases hxK : x ∈ K
  · rw [indicator_of_mem hxK]
    exact (hC x hxK).trans ((le_abs_self C).trans (Real.norm_eq_abs C).symm.le)
  · simp [hxK, hx hxK]

/-- **Closedness** (task `bdp_weakClosed`): the periodic weak derivative relation is closed under
`L²(cylinder)`-convergence of the functions and of their derivatives. -/
theorem bdp_weakClosed : BdpWeakClosed := by
  unfold BdpWeakClosed
  intro c hc j F F' fs fs' hw hF hF' hfs hfs'
  haveI hT : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hint : ∀ ψ G : ℝ × ℝ → ℝ, (Sob.cylinder c).Adm ψ → MemLp G 2 (Sob.cylinder c).μ →
      Integrable (fun x => ψ x * G x) (Sob.cylinder c).μ := by
    intro ψ G hψ hG
    obtain ⟨K, hK, hKψ⟩ := (Sob.cylinder c).supp hψ
    exact MemLp.integrable_mul (wc_memLp_test hK ((Sob.cylinder c).continuous hψ) hKψ) hG
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · simp only [smul_eq_mul]
    exact hint _ F ((Sob.cylinder c).adm_iterDirDeriv hφ _) hF
  · simp only [smul_eq_mul]
    exact hint φ F' hφ hF'
  · have hA := (Sob.cylinder c).adm_iterDirDeriv hφ [(Sob.cylinder c).dir j]
    obtain ⟨K1, hK1, hK1ψ⟩ := (Sob.cylinder c).supp hA
    obtain ⟨K2, hK2, hK2ψ⟩ := (Sob.cylinder c).supp hφ
    have hL : Tendsto (fun n => ∫ x, Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x * fs n x
        ∂(Sob.cylinder c).μ) atTop
        (𝓝 (∫ x, Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x * F x ∂(Sob.cylinder c).μ)) :=
      wc_tendsto_test hK1 ((Sob.cylinder c).continuous hA) hK1ψ hF.1
        (fun n => (hw n).int_left φ hφ) hfs
    have hR : Tendsto (fun n => ∫ x, φ x * fs' n x ∂(Sob.cylinder c).μ) atTop
        (𝓝 (∫ x, φ x * F' x ∂(Sob.cylinder c).μ)) :=
      wc_tendsto_test hK2 ((Sob.cylinder c).continuous hφ) hK2ψ hF'.1
        (fun n => (hw n).int_right φ hφ) hfs'
    have hid : ∀ n, ∫ x, Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x * fs n x
        ∂(Sob.cylinder c).μ = -∫ x, φ x * fs' n x ∂(Sob.cylinder c).μ := by
      intro n
      have h := (hw n).identity φ hφ
      simpa [smul_eq_mul] using h
    have hlim : Tendsto (fun n => ∫ x, Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x * fs n x
        ∂(Sob.cylinder c).μ) atTop (𝓝 (-∫ x, φ x * F' x ∂(Sob.cylinder c).μ)) :=
      Tendsto.congr (fun n => (hid n).symm) hR.neg
    have hEq := tendsto_nhds_unique hL hlim
    simp only [smul_eq_mul, List.length_singleton, pow_one]
    rw [hEq]
    ring

end UnforcedLeray.Short.PartI
