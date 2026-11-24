import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.CellBridge

/-!
# Part I, task `PartI:T07`, target `cylDerivFinite_proof`: finiteness of all derivatives

Source of record: `the November 2 reference manuscript`, lines 355-374 (the cylinder
interpolation step needs every coordinate derivative to be bounded and to lie in every `L^p`,
`p ≥ 2`). The Prop is `CylDerivFinite` in `Sub/T07.lean`.

Proof. Fix `c ≥ 1`, a smooth `c`-periodic `f` with every `D^j f` in `L²` of the centred cell, and a
word `w`.

1. By `cylJetWord_proof`, `|D_v f z| ≤ ‖D^j f z‖` for every word `v` of length `j`. Hence every
   derivative word of `w`, `true :: w`, `false :: w` and `false :: true :: w` is in `L²` of the
   centred cell.
2. These functions are continuous and `c`-periodic, so they are in `L²` of the library cell
   `(0, c]` (`memLp_cellMeasure_iff`, using `0 < c`).
3. `B0151.enorm_derivWord_le` bounds `‖D_w f z‖ₑ` everywhere by `3` times the sum of the four cell
   `L²` norms, which is finite.
4. For `2 ≤ p < ∞`, `|g|^p ≤ K^(p-2) |g|²` when `|g| ≤ K` gives `L^p`; `p = ∞` follows from the
   bound `K` directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Interpolation: `L² ∩ L^∞ ⊂ L^p` for `2 ≤ p < ∞`, on any measure space. The pointwise bound
`|g|^p ≤ K^(p-2) |g|²`, valid when `|g| ≤ K`, gives `∫ |g|^p ≤ K^(p-2) ∫ |g|² < ∞`. -/
theorem memLp_of_memLp_two_of_enorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg2 : MemLp g 2 μ) {K : ℝ≥0∞} (hK : K ≠ ⊤) (hbd : ∀ x, ‖g x‖ₑ ≤ K)
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p ≠ ⊤) : MemLp g p μ := by
  refine ⟨hg2.1, ?_⟩
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hq2 : (2 : ℝ) ≤ p.toReal := by
    have h := (ENNReal.toReal_le_toReal h2top hpt).2 hp2
    simpa using h
  have hpos : 0 < p.toReal := by linarith
  have hKq : K ^ (p.toReal - 2) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hK
  have hpow : ∀ x, ‖g x‖ₑ ^ p.toReal ≤ K ^ (p.toReal - 2) * ‖g x‖ₑ ^ (2 : ℝ) := by
    intro x
    have hsplit : ‖g x‖ₑ ^ p.toReal = ‖g x‖ₑ ^ (p.toReal - 2) * ‖g x‖ₑ ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_add_of_nonneg (p.toReal - 2) 2 (by linarith) (by norm_num),
        sub_add_cancel]
    have hle : ‖g x‖ₑ ^ (p.toReal - 2) ≤ K ^ (p.toReal - 2) :=
      ENNReal.rpow_le_rpow (hbd x) (by linarith)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hle zero_le
  have hJ : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    intro hJtop
    have hsq : eLpNorm g 2 μ = (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) h2top]
      norm_num
    have hlt := hg2.eLpNorm_lt_top
    rw [hsq, hJtop, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hlt
    exact lt_irrefl _ hlt
  have hI : ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ ≠ ⊤ := by
    have hle : ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ ≤ K ^ (p.toReal - 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ :=
      calc ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ ≤ ∫⁻ x, K ^ (p.toReal - 2) * ‖g x‖ₑ ^ (2 : ℝ) ∂μ :=
            lintegral_mono fun x => hpow x
        _ = K ^ (p.toReal - 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ :=
            lintegral_const_mul' _ _ hKq
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hKq hJ) hle
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_pos.2 hpos).le hI

/-- **Target** `cylDerivFinite_proof`: finiteness of all derivatives (`CylDerivFinite`,
`Sub/T07.lean`). -/
theorem cylDerivFinite_proof : UnforcedLeray.Short.PartI.CylDerivFinite := by
  unfold CylDerivFinite
  intro c hc f hf hper hL w
  have hc0 : 0 < c := by linarith
  have hJ := cylJetWord_proof
  unfold CylJetWord at hJ
  -- Step 1: every derivative word of length `j` lies in `L²` of the centred cell.
  have hA : ∀ (v : List Bool) (j : ℕ), v.length = j →
      MemLp (B0151.derivWord v f) 2 (Cyl.cellμ c) := by
    intro v j hv
    refine MemLp.of_le (hL j) (B0151.contDiff_derivWord hf v).continuous.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs]
    exact (hJ f hf j z).1 v hv
  -- Step 2: periodicity and measurability, then transfer to the library cell `(0, c]`.
  have hfB : B0151.IsPeriodicQ c f := by
    intro q η
    exact hper (q, η)
  have hgM : ∀ v : List Bool, Measurable (B0151.derivWord v f) := fun v =>
    (B0151.contDiff_derivWord hf v).continuous.measurable
  have hgP : ∀ v : List Bool, Cyl.IsPeriodic c (B0151.derivWord v f) := by
    intro v z
    exact B0151.periodic_derivWord hfB v z.1 z.2
  have hB : ∀ (v : List Bool) (j : ℕ), v.length = j →
      MemLp (B0151.derivWord v f) 2 (B0151.cellMeasure c) :=
    fun v j hv => (memLp_cellMeasure_iff hc0 (hgM v) (hgP v) 2).2 (hA v j hv)
  -- Step 3: the pointwise bound by the four cell `L²` norms, and its finiteness.
  have h0 : MemLp (B0151.derivWord w f) 2 (B0151.cellMeasure c) := hB w w.length rfl
  have hq : MemLp (B0151.derivWord (true :: w) f) 2 (B0151.cellMeasure c) :=
    hB (true :: w) (w.length + 1) (by simp)
  have hη : MemLp (B0151.derivWord (false :: w) f) 2 (B0151.cellMeasure c) :=
    hB (false :: w) (w.length + 1) (by simp)
  have hqη : MemLp (B0151.derivWord (false :: true :: w) f) 2 (B0151.cellMeasure c) :=
    hB (false :: true :: w) (w.length + 2) (by simp only [List.length_cons])
  obtain ⟨K, hKtop, hKbd⟩ : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ z, ‖B0151.derivWord w f z‖ₑ ≤ K := by
    refine ⟨_, ?_, fun z => B0151.enorm_derivWord_le hc hf hfB w h0 hq hη hqη z⟩
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨h0.eLpNorm_lt_top.ne, hq.eLpNorm_lt_top.ne⟩, hη.eLpNorm_lt_top.ne⟩,
        hqη.eLpNorm_lt_top.ne⟩)
  -- Step 4: boundedness, and `L^p` for `2 ≤ p ≤ ∞`.
  refine ⟨?_, fun p hp2 => ?_⟩
  · exact ne_top_of_le_ne_top hKtop (iSup_le hKbd)
  · rcases eq_or_ne p ⊤ with rfl | hpt
    · exact memLp_top_of_bound_enorm
        (B0151.contDiff_derivWord hf w).continuous.aestronglyMeasurable K.toNNReal
        (Filter.Eventually.of_forall fun z => (hKbd z).trans_eq (ENNReal.coe_toNNReal hKtop).symm)
    · exact memLp_of_memLp_two_of_enorm_le (hA w w.length rfl) hKtop hKbd hp2 hpt

end UnforcedLeray.Short.PartI
