import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- Summable `L²` errors give almost everywhere convergence to `0`. -/
lemma mpathv_ae_tendsto_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h : ℕ → α → ℂ) (hm : ∀ n, AEMeasurable (h n) μ)
    (hb : ∀ n, eLpNorm (h n) 2 μ ≤ (2⁻¹ : ℝ≥0∞) ^ n) :
    ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0) := by
  have hint : ∀ n, ∫⁻ x, ‖h n x‖ₑ ^ (2 : ℝ) ∂μ ≤ ((2⁻¹ : ℝ≥0∞) ^ 2) ^ n := by
    intro n
    have h1 := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := h n) (p := 2) (by norm_num)
    simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h1
    rw [← h1, ENNReal.rpow_two, ← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left' (hb n) 2
  have hfin : ∫⁻ x, ∑' n, ‖h n x‖ₑ ^ (2 : ℝ) ∂μ ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).enorm.pow_const _)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hint)
    rw [ENNReal.tsum_geometric]
    refine ENNReal.inv_ne_top.2 ?_
    have : ((2⁻¹ : ℝ≥0∞) ^ 2) < 1 := by
      calc ((2⁻¹ : ℝ≥0∞) ^ 2) ≤ 2⁻¹ * 1 := by
            rw [pow_two]; gcongr; exact ENNReal.inv_le_one.2 (by norm_num)
        _ < 1 := by simpa using ENNReal.inv_lt_one.2 (by norm_num)
    exact (tsub_pos_of_lt this).ne'
  have hae := ae_lt_top' (AEMeasurable.tsum fun n => (hm n).enorm.pow_const _) hfin
  filter_upwards [hae] with x hx
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  have h1 : Tendsto (fun n => (‖h n x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h0
    simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    exact this
  have h2 : Tendsto (fun n => ‖h n x‖ₑ) atTop (𝓝 0) := by
    refine h1.congr fun n => ?_
    rw [← ENNReal.rpow_mul]; norm_num
  have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Function.comp_def, toReal_enorm] using h3


set_option maxHeartbeats 800000 in
/-- **Leaf 7a** (SP 3060-3061): a jointly measurable version of an `L²(μ)`-continuous path. -/
theorem measPathVersion : UnforcedLeray.Short.IIIa.MeasPathVersion := by
  intro μ _ t s f hf hc
  classical
  by_cases hne : (Ioo t s).Nonempty
  swap
  · exact ⟨fun _ => 0, measurable_const, fun r hr => absurd ⟨r, hr⟩ hne⟩
  -- the path in `L²`
  let ψ : ℝ → Lp ℂ 2 μ := fun r => if h : r ∈ Ioo t s then (hf r h).toLp (f r) else 0
  have hψ : ∀ r (h : r ∈ Ioo t s), ψ r = (hf r h).toLp (f r) := fun r h => by simp only [ψ]; rw [dif_pos h]
  have hψae : ∀ r (h : r ∈ Ioo t s), (⇑(ψ r) : ℝ × ℝ → ℂ) =ᵐ[μ] f r := fun r h => by
    rw [hψ r h]; exact (hf r h).coeFn_toLp
  have hdist : ∀ r ∈ Ioo t s, ∀ r' ∈ Ioo t s,
      dist (ψ r') (ψ r) = (eLpNorm (f r' - f r) 2 μ).toReal := by
    intro r hr r' hr'
    rw [Lp.dist_def]
    congr 1
    exact eLpNorm_congr_ae ((hψae r' hr').sub (hψae r hr))
  have hcont : ContinuousOn ψ (Ioo t s) := by
    intro r hr
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hc r hr)
    simp only [ENNReal.toReal_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact (hdist r hr r' hr').symm
  -- a dense sequence
  haveI : Nonempty (Ioo t s) := hne.to_subtype
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Ioo t s)
  have happrox : ∀ (ε : ℝ), 0 < ε → ∀ r, ∃ k, r ∉ Ioo t s ∨ dist (ψ (u k)) (ψ r) < ε := by
    intro ε hε r
    by_cases hr : r ∈ Ioo t s
    · obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcont r hr) ε hε
      obtain ⟨k, hk⟩ := hu.exists_dist_lt ⟨r, hr⟩ hδ
      refine ⟨k, Or.inr ?_⟩
      have := hδ' (u k).2 (by rw [dist_comm]; simpa [Subtype.dist_eq] using hk)
      exact this
    · exact ⟨0, Or.inl hr⟩
  let ε : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  let kn : ℕ → ℝ → ℕ := fun n r => Nat.find (happrox (ε n) (hε n) r)
  have hkn_spec : ∀ n, ∀ r ∈ Ioo t s, dist (ψ (u (kn n r))) (ψ r) < ε n := by
    intro n r hr
    have := Nat.find_spec (happrox (ε n) (hε n) r)
    exact this.resolve_left (not_not.2 hr)
  have hkn_meas : ∀ n, Measurable (kn n) := by
    intro n
    refine measurable_find (happrox (ε n) (hε n)) fun k => ?_
    have : {r | r ∉ Ioo t s ∨ dist (ψ (u k)) (ψ r) < ε n}
        = (Ioo t s)ᶜ ∪ (Ioo t s ∩ ψ ⁻¹' Metric.ball (ψ (u k)) (ε n)) := by
      ext r
      simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff, mem_preimage,
        Metric.mem_ball]
      rw [dist_comm]; tauto
    rw [this]
    exact isOpen_Ioo.measurableSet.compl.union
      (hcont.isOpen_inter_preimage isOpen_Ioo Metric.isOpen_ball).measurableSet
  -- representatives
  let ρ : ℕ → ℝ × ℝ → ℂ := fun k => (Lp.aestronglyMeasurable (ψ (u k).1)).mk _
  have hρm : ∀ k, Measurable (ρ k) := fun k =>
    (Lp.aestronglyMeasurable (ψ (u k).1)).stronglyMeasurable_mk.measurable
  have hρae : ∀ k, (⇑(ψ (u k).1) : ℝ × ℝ → ℂ) =ᵐ[μ] ρ k := fun k =>
    (Lp.aestronglyMeasurable (ψ (u k).1)).ae_eq_mk
  clear_value kn ρ
  let g : ℕ → ℝ × (ℝ × ℝ) → ℂ := fun n p => ρ (kn n p.1) p.2
  have hg : ∀ n, Measurable (g n) := by
    intro n
    have H : Measurable (fun q : ℕ × (ℝ × ℝ) => ρ q.1 q.2) :=
      measurable_from_prod_countable_right (fun k => hρm k)
    have hpair : Measurable (fun p : ℝ × (ℝ × ℝ) => (kn n p.1, p.2)) :=
      ((hkn_meas n).comp measurable_fst).prodMk measurable_snd
    exact H.comp hpair
  have hgerr : ∀ n, ∀ r ∈ Ioo t s,
      eLpNorm (fun x => g n (r, x) - f r x) 2 μ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n r hr
    have hk := hkn_spec n r hr
    have h1 : eLpNorm (fun x => g n (r, x) - f r x) 2 μ
        = eLpNorm (⇑(ψ (u (kn n r)).1) - ⇑(ψ r)) 2 μ := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hρae (kn n r), hψae r hr] with x h1 h2
      simp only [Pi.sub_apply, g]
      rw [h1, h2]
    have h2 : eLpNorm (⇑(ψ (u (kn n r)).1) - ⇑(ψ r)) 2 μ
        = ENNReal.ofReal (dist (ψ (u (kn n r)).1) (ψ r)) := by
      have hne : eLpNorm (⇑(ψ (u (kn n r)).1) - ⇑(ψ r)) 2 μ ≠ ⊤ :=
        (((Lp.memLp _).sub (Lp.memLp _)).eLpNorm_lt_top).ne
      rw [Lp.dist_def, ENNReal.ofReal_toReal hne]
    rw [h1, h2]
    have h3 : ENNReal.ofReal (ε n) = (2⁻¹ : ℝ≥0∞) ^ n := by
      simp only [ε]
      rw [ENNReal.ofReal_pow (by norm_num)]
      congr 1
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    rw [← h3]
    exact ENNReal.ofReal_le_ofReal hk.le
  -- the limit
  let C : Set (ℝ × (ℝ × ℝ)) := {p | ∃ l, Tendsto (fun n => g n p) atTop (𝓝 l)}
  have hC : MeasurableSet C := measurableSet_exists_tendsto hg
  let g' : ℕ → ℝ × (ℝ × ℝ) → ℂ := fun n p => if p ∈ C then g n p else 0
  let F : ℝ × (ℝ × ℝ) → ℂ := fun p => if p ∈ C then limUnder atTop (fun n => g n p) else 0
  have hg' : ∀ n, Measurable (g' n) := fun n => Measurable.ite hC (hg n) measurable_const
  have hlim : Tendsto g' atTop (𝓝 F) := by
    rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ C
    · have hl : Tendsto (fun n => g n p) atTop (𝓝 (limUnder atTop (fun n => g n p))) :=
        hp.choose_spec.limUnder_eq ▸ hp.choose_spec
      simpa [g', F, hp] using hl
    · simp [g', F, hp]
  refine ⟨F, measurable_of_tendsto_metrizable hg' hlim, ?_⟩
  intro r hr
  have hm : ∀ n, AEMeasurable (fun x => g n (r, x) - f r x) μ := fun n =>
    (((hg n).comp measurable_prodMk_left).aemeasurable).sub (hf r hr).1.aemeasurable
  filter_upwards [mpathv_ae_tendsto_zero μ _ hm (hgerr · r hr)] with x hx
  have hx' : Tendsto (fun n => g n (r, x)) atTop (𝓝 (f r x)) := by
    have := hx.add_const (f r x)
    simpa using this
  have hpC : (r, x) ∈ C := ⟨_, hx'⟩
  simp only [F, hpC, if_true]
  exact hx'.limUnder_eq

end UnforcedLeray.Short.IIIa
