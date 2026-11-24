import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1

/-!
# Part III-a, task `PartIII-a:T18/2/1/3`: completeness of `𝒯` (`CausalCompleteT`)

Source of record: `the November 2 reference manuscript`, lines 3427-3440 (the
`L²` limit of the gradients). Tensor analogue of `CausalCompleteH` (`Sub/T18_2_1.lean`): weight
`s^{-1/2}`, values in `ℂ^{2×2}` with the Frobenius norm `tnorm2`.

Route. Each entry of `g⁻¹ Gₙ` is Cauchy in the scalar `L²(ageμ c (-1/2))`. Scalar completeness
(`MeasureTheory.Lp.instCompleteSpace`, applied to the differences from one fixed index, with a
measurable representative of the limit) gives four measurable entry limits. Then
`tnorm2 T ≤ ‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖` turns entrywise convergence into convergence of
`tCalNorm`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Scalar `L²` completeness -/

/-- Scalar `L²` completeness under a Cauchy bound `K (a n + a m)` with `a → 0`, `K < ∞`. -/
theorem causalCompleteT_scalar {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℂ) (hf : ∀ n, Measurable (f n)) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (a : ℕ → ℝ≥0∞) (ha : Tendsto a atTop (𝓝 0)) (N₀ : ℕ)
    (hN₀ : ∀ n m, N₀ ≤ n → N₀ ≤ m →
      eLpNorm (fun x => f n x - f m x) 2 μ ≤ K * (a n + a m)) :
    ∃ G : α → ℂ, Measurable G ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - G x) 2 μ) atTop (𝓝 0) := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n, N₁ ≤ n → a n < ⊤ :=
    eventually_atTop.1 (ha.eventually (gt_mem_nhds ENNReal.zero_lt_top))
  obtain ⟨M, hM₀, hM₁⟩ : ∃ M : ℕ, N₀ ≤ M ∧ N₁ ≤ M :=
    ⟨max N₀ N₁, le_max_left _ _, le_max_right _ _⟩
  -- differences from the fixed index `M`
  obtain ⟨w, hw⟩ : ∃ w : ℕ → α → ℂ, ∀ k x, w k x = f (k + M) x - f M x :=
    ⟨fun k x => f (k + M) x - f M x, fun _ _ => rfl⟩
  have hwm : ∀ k, Measurable (w k) := by
    intro k
    have hfun : w k = fun x => f (k + M) x - f M x := funext fun x => hw k x
    rw [hfun]
    exact (hf (k + M)).sub (hf M)
  have hwfin : ∀ k, eLpNorm (w k) 2 μ < ⊤ := by
    intro k
    have hfun : w k = fun x => f (k + M) x - f M x := funext fun x => hw k x
    rw [hfun]
    refine lt_of_le_of_lt (hN₀ (k + M) M (by omega) hM₀) ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK)
      (ENNReal.add_lt_top.2 ⟨hN₁ (k + M) (by omega), hN₁ M hM₁⟩)
  have hwL : ∀ k, MemLp (w k) 2 μ := fun k => ⟨(hwm k).aestronglyMeasurable, hwfin k⟩
  have hc : Tendsto (fun k => K * a (k + M)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => a (k + M)) atTop (𝓝 0) := ha.comp (tendsto_add_atTop_nat M)
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hK)
  have hcau : CauchySeq (fun k => (hwL k).toLp (w k)) := by
    refine EMetric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hc.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne')))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [MeasureTheory.Lp.edist_toLp_toLp]
    have hdiff : w m - w n = fun x => f (m + M) x - f (n + M) x := by
      funext x
      simp only [Pi.sub_apply, hw]
      ring
    rw [hdiff]
    calc eLpNorm (fun x => f (m + M) x - f (n + M) x) 2 μ
        ≤ K * (a (m + M) + a (n + M)) := hN₀ (m + M) (n + M) (by omega) (by omega)
      _ = K * a (m + M) + K * a (n + M) := mul_add _ _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hN m hm) (hN n hn)
      _ = ε := ENNReal.add_halves ε
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  have hxm : AEStronglyMeasurable (⇑x) μ := Lp.aestronglyMeasurable x
  obtain ⟨g, hgm, hxg⟩ : ∃ g : α → ℂ, Measurable g ∧ (⇑x) =ᵐ[μ] g :=
    ⟨hxm.mk _, hxm.stronglyMeasurable_mk.measurable, hxm.ae_eq_mk⟩
  have hE : ∀ k, eLpNorm (fun y => w k y - g y) 2 μ = edist ((hwL k).toLp (w k)) x := by
    intro k
    rw [MeasureTheory.Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hwL k).coeFn_toLp, hxg] with y h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have hlim : Tendsto (fun k => eLpNorm (fun y => w k y - g y) 2 μ) atTop (𝓝 0) :=
    Tendsto.congr (fun k => (hE k).symm) (tendsto_iff_edist_tendsto_0.1 hx)
  refine ⟨fun y => f M y + g y, (hf M).add hgm, ?_⟩
  refine (Filter.tendsto_add_atTop_iff_nat M).1 ?_
  refine Tendsto.congr (fun k => ?_) hlim
  congr 1
  funext y
  simp only [hw]
  ring

/-! ## Norm bounds for `ℂ^{2×2}` -/

theorem causalCompleteT_entry_le_tnorm2 (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    ‖T i j‖ ≤ tnorm2 T := by
  unfold tnorm2
  have h1 : ‖T i j‖ ^ 2 ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, ‖T i' j'‖ ^ 2 := by
    calc ‖T i j‖ ^ 2 ≤ ∑ j' : Fin 2, ‖T i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖T i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, ‖T i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j' : Fin 2, ‖T i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖T i j‖ = Real.sqrt (‖T i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i' : Fin 2, ∑ j' : Fin 2, ‖T i' j'‖ ^ 2) := Real.sqrt_le_sqrt h1

theorem causalCompleteT_tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T :=
  Real.sqrt_nonneg _

theorem causalCompleteT_tnorm2_le (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ≤ ‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖ := by
  unfold tnorm2
  have h0 : 0 ≤ ‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖ := by positivity
  refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq h0)
  simp only [Fin.sum_univ_two]
  nlinarith [mul_nonneg (norm_nonneg (T 0 0)) (norm_nonneg (T 0 1)),
    mul_nonneg (norm_nonneg (T 0 0)) (norm_nonneg (T 1 0)),
    mul_nonneg (norm_nonneg (T 0 0)) (norm_nonneg (T 1 1)),
    mul_nonneg (norm_nonneg (T 0 1)) (norm_nonneg (T 1 0)),
    mul_nonneg (norm_nonneg (T 0 1)) (norm_nonneg (T 1 1)),
    mul_nonneg (norm_nonneg (T 1 0)) (norm_nonneg (T 1 1))]

/-- Four-term Minkowski inequality in `L²`. -/
theorem causalCompleteT_eLpNorm_add4 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B C D : α → ℝ) (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hD : Measurable D) :
    eLpNorm (A + B + C + D) 2 μ ≤
      eLpNorm A 2 μ + eLpNorm B 2 μ + eLpNorm C 2 μ + eLpNorm D 2 μ := by
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  calc eLpNorm (A + B + C + D) 2 μ
      ≤ eLpNorm (A + B + C) 2 μ + eLpNorm D 2 μ :=
        eLpNorm_add_le ((hA.add hB).add hC).aestronglyMeasurable hD.aestronglyMeasurable h2
    _ ≤ (eLpNorm (A + B) 2 μ + eLpNorm C 2 μ) + eLpNorm D 2 μ :=
        add_le_add (eLpNorm_add_le (hA.add hB).aestronglyMeasurable
          hC.aestronglyMeasurable h2) le_rfl
    _ ≤ ((eLpNorm A 2 μ + eLpNorm B 2 μ) + eLpNorm C 2 μ) + eLpNorm D 2 μ :=
        add_le_add (add_le_add (eLpNorm_add_le hA.aestronglyMeasurable
          hB.aestronglyMeasurable h2) le_rfl) le_rfl
    _ = eLpNorm A 2 μ + eLpNorm B 2 μ + eLpNorm C 2 μ + eLpNorm D 2 μ := by ring

/-! ## Completeness of `𝒯` -/

/-- **Completeness of `𝒯`** (`PartIII-a:T18/2/1/3`; SP 3427-3440). The tensor analogue of
`CausalCompleteH` (norm `tCalNorm c`, weight `s^{-1/2}`, values in `ℂ^{2×2}` with the Frobenius
norm `tnorm2`). -/
theorem causalCompleteT : UnforcedLeray.Short.IIIa.CausalCompleteT := by
  unfold CausalCompleteT
  intro c ν γ _hc _hν Gn hGm K a hK ha hbd
  obtain ⟨N₀, hN₀⟩ := hbd
  have hgainR : Measurable fun s : ℝ => gainG γ ν s := by
    unfold gainG
    fun_prop
  have hgain : Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 :=
    hgainR.comp measurable_fst
  have hinv : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := hgain.inv
  have hr : ∀ p : ℝ × (ℝ × ℝ), gainG γ ν p.1 ≠ 0 := fun p => by
    unfold gainG
    positivity
  -- each entry of `g⁻¹ Gₙ` converges in the scalar `L²`
  have key : ∀ i j : Fin 2, ∃ g : ℝ × (ℝ × ℝ) → ℂ, Measurable g ∧
      Tendsto (fun n => eLpNorm (fun p => (gainG γ ν p.1)⁻¹ • Gn n p i j - g p) 2
        (ageμ c (-1 / 2))) atTop (𝓝 0) := by
    intro i j
    have hm : ∀ n, Measurable (fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ • Gn n p i j) :=
      fun n => hinv.smul (hGm n i j)
    have hbd' : ∀ n m, N₀ ≤ n → N₀ ≤ m →
        eLpNorm (fun p => (gainG γ ν p.1)⁻¹ • Gn n p i j
          - (gainG γ ν p.1)⁻¹ • Gn m p i j) 2 (ageμ c (-1 / 2)) ≤ K * (a n + a m) := by
      intro n m hn hm'
      have h1 := hN₀ n m hn hm'
      unfold tCalNorm at h1
      have hpt : ∀ p : ℝ × (ℝ × ℝ),
          ‖(gainG γ ν p.1)⁻¹ • Gn n p i j - (gainG γ ν p.1)⁻¹ • Gn m p i j‖
            ≤ tnorm2 (gainConj γ ν (fun p i j => Gn n p i j - Gn m p i j) p) := by
        intro p
        have h2 := causalCompleteT_entry_le_tnorm2
          (gainConj γ ν (fun p i j => Gn n p i j - Gn m p i j) p) i j
        have hT : gainConj γ ν (fun p i j => Gn n p i j - Gn m p i j) p i j
            = (gainG γ ν p.1)⁻¹ • Gn n p i j - (gainG γ ν p.1)⁻¹ • Gn m p i j := by
          simp [gainConj, smul_sub]
        rw [hT] at h2
        exact h2
      exact le_trans (eLpNorm_mono_real hpt) h1
    obtain ⟨g, hgm, hgt⟩ := causalCompleteT_scalar (ageμ c (-1 / 2))
      (fun n p => (gainG γ ν p.1)⁻¹ • Gn n p i j) hm K hK a ha N₀ hbd'
    exact ⟨g, hgm, hgt⟩
  choose g hgm hgt using key
  refine ⟨fun p i j => gainG γ ν p.1 • g i j p, fun i j => hgain.smul (hgm i j), ?_⟩
  -- the identity `g⁻¹(Gₙ - G) = g⁻¹ Gₙ - g` entrywise
  have hpt : ∀ n p i j, gainConj γ ν (fun p i j => Gn n p i j - gainG γ ν p.1 • g i j p) p i j
      = (gainG γ ν p.1)⁻¹ • Gn n p i j - g i j p := by
    intro n p i j
    simp only [gainConj, Pi.smul_apply, smul_sub]
    rw [inv_smul_smul₀ (hr p)]
  have hA : ∀ n i j, Measurable
      (fun p : ℝ × (ℝ × ℝ) => ‖(gainG γ ν p.1)⁻¹ • Gn n p i j - g i j p‖) :=
    fun n i j => ((hinv.smul (hGm n i j)).sub (hgm i j)).norm
  have hbound : ∀ n, tCalNorm c (gainConj γ ν (fun p i j => Gn n p i j - gainG γ ν p.1 • g i j p))
      ≤ eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 0 0 - g 0 0 p‖) 2 (ageμ c (-1 / 2))
        + eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 0 1 - g 0 1 p‖) 2 (ageμ c (-1 / 2))
        + eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 1 0 - g 1 0 p‖) 2 (ageμ c (-1 / 2))
        + eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 1 1 - g 1 1 p‖) 2 (ageμ c (-1 / 2)) := by
    intro n
    unfold tCalNorm
    refine le_trans (eLpNorm_mono_real fun p => ?_)
      (causalCompleteT_eLpNorm_add4 (ageμ c (-1 / 2)) _ _ _ _
        (hA n 0 0) (hA n 0 1) (hA n 1 0) (hA n 1 1))
    have h2 := causalCompleteT_tnorm2_le
      (gainConj γ ν (fun p i j => Gn n p i j - gainG γ ν p.1 • g i j p) p)
    rw [hpt n p 0 0, hpt n p 0 1, hpt n p 1 0, hpt n p 1 1] at h2
    rw [Real.norm_of_nonneg (causalCompleteT_tnorm2_nonneg _)]
    exact h2
  -- each entry norm tends to zero
  have h00 : Tendsto (fun n => eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 0 0 - g 0 0 p‖)
      2 (ageμ c (-1 / 2))) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (eLpNorm_norm _).symm) (hgt 0 0)
  have h01 : Tendsto (fun n => eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 0 1 - g 0 1 p‖)
      2 (ageμ c (-1 / 2))) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (eLpNorm_norm _).symm) (hgt 0 1)
  have h10 : Tendsto (fun n => eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 1 0 - g 1 0 p‖)
      2 (ageμ c (-1 / 2))) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (eLpNorm_norm _).symm) (hgt 1 0)
  have h11 : Tendsto (fun n => eLpNorm (fun p => ‖(gainG γ ν p.1)⁻¹ • Gn n p 1 1 - g 1 1 p‖)
      2 (ageμ c (-1 / 2))) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (eLpNorm_norm _).symm) (hgt 1 1)
  have hB := ((h00.add h01).add h10).add h11
  simp only [add_zero] at hB
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
    (fun _ => zero_le) (fun n => hbound n)

end UnforcedLeray.Short.IIIa
