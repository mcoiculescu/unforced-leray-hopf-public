import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1

/-!
# Part III-a, task `PartIII-a:T18/2/1/3`: a.e. slice convergence (`causalSliceAE`)

Target: `causalSliceAE : CausalSliceAE` (`Sub/T18_2_1.lean`, the Prop at line 85).
Source of record: `the November 2 reference manuscript`, lines 3427-3440.

Route. Write `g(s) = gainG γ ν s`. The hypotheses say that the age integrals of
`‖gainConj …‖ₑ²` against `ageμ c (-3/2)` and `ageμ c (-1/2)` tend to `0`. By `Axi.lintegral_ageμ`
both are integrals over `(0,∞) × cell` of `c⁻¹ s^a` times the squared pointwise norms, so their sum
is `∫⁻ K n → 0` for one measurable `K n` (`sliceAE_core`). A subsequence `φ` with
`∫⁻ K (φ k) ≤ 2⁻¹^k` makes `∑ₖ ∫⁻_cell K (φ k)(s,·)` have finite age integral (Tonelli), so for
a.e. `s` its terms tend to `0`. At a fixed `s > 0` the weights `c⁻¹ s^{-3/2} g(s)⁻²` and
`c⁻¹ s^{-1/2} g(s)⁻²` are positive and finite, which gives the unweighted, unconjugated slice
convergence (`sliceAE_squeeze`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ### Pointwise norm facts -/

theorem sliceAE_vnorm2_nonneg (v : Fin 2 → ℂ) : 0 ≤ vnorm2 v := Real.sqrt_nonneg _

theorem sliceAE_tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T := Real.sqrt_nonneg _

theorem sliceAE_vnorm2_smul {r : ℝ} (hr : 0 ≤ r) (v : Fin 2 → ℂ) :
    vnorm2 (r • v) = r * vnorm2 v := by
  unfold vnorm2
  have h : ∑ i : Fin 2, ‖(r • v) i‖ ^ 2 = r ^ 2 * ∑ i : Fin 2, ‖v i‖ ^ 2 := by
    simp [Fin.sum_univ_two, Pi.smul_apply, Real.norm_of_nonneg hr, mul_pow, mul_add]
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

theorem sliceAE_tnorm2_smul {r : ℝ} (hr : 0 ≤ r) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (r • T) = r * tnorm2 T := by
  unfold tnorm2
  have h : ∑ i : Fin 2, ∑ j : Fin 2, ‖(r • T) i j‖ ^ 2
      = r ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    simp [Fin.sum_univ_two, Pi.smul_apply, Real.norm_of_nonneg hr, mul_pow, mul_add]
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

theorem sliceAE_gainG_pos (γ ν s : ℝ) : 0 < gainG γ ν s := Real.exp_pos _

theorem sliceAE_enorm_vnorm2 (γ ν : ℝ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    ‖vnorm2 (gainConj γ ν f p)‖ₑ = ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * vnorm2 (f p)) := by
  have hg : 0 ≤ (gainG γ ν p.1)⁻¹ := (inv_pos.2 (sliceAE_gainG_pos γ ν p.1)).le
  rw [show gainConj γ ν f p = (gainG γ ν p.1)⁻¹ • f p from rfl, sliceAE_vnorm2_smul hg,
    Real.enorm_eq_ofReal (mul_nonneg hg (sliceAE_vnorm2_nonneg _))]

theorem sliceAE_enorm_tnorm2 (γ ν : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) :
    ‖tnorm2 (gainConj γ ν T p)‖ₑ = ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * tnorm2 (T p)) := by
  have hg : 0 ≤ (gainG γ ν p.1)⁻¹ := (inv_pos.2 (sliceAE_gainG_pos γ ν p.1)).le
  rw [show gainConj γ ν T p = (gainG γ ν p.1)⁻¹ • T p from rfl, sliceAE_tnorm2_smul hg,
    Real.enorm_eq_ofReal (mul_nonneg hg (sliceAE_tnorm2_nonneg _))]

/-- Factor `ofReal (r v)²` against a fixed weight: `α · r² · v² = α · (r v)²`. -/
theorem sliceAE_key (α : ℝ≥0∞) {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) :
    α * ENNReal.ofReal r ^ 2 * ENNReal.ofReal (v ^ 2) = α * ENNReal.ofReal (r * v) ^ 2 := by
  rw [ENNReal.ofReal_mul hr, mul_pow, ENNReal.ofReal_pow hv]
  ring

/-! ### From `eLpNorm → 0` to the squared lower integral -/

theorem sliceAE_lint_sq_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (h : Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have key : ∀ n, eLpNorm (F n) 2 μ ^ 2 = ∫⁻ x, ‖F n x‖ₑ ^ 2 ∂μ := by
    intro n
    have h2 := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := F n) (p := 2) two_ne_zero
    simpa using h2
  have h3 : Tendsto (fun n => eLpNorm (F n) 2 μ ^ 2) atTop (𝓝 ((0 : ℝ≥0∞) ^ 2)) :=
    ((ENNReal.continuous_pow 2).tendsto 0).comp h
  rw [zero_pow two_ne_zero] at h3
  have hk : (fun n => ∫⁻ x, ‖F n x‖ₑ ^ 2 ∂μ) = fun n => eLpNorm (F n) 2 μ ^ 2 :=
    funext fun n => (key n).symm
  rw [hk]
  exact h3

/-! ### Tonelli, the age integral in slice form, and the squeeze -/

/-- Tonelli on `(0,∞) × cell`: the restricted integral is the iterated one. -/
theorem sliceAE_tonelli {c : ℝ} (F : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c, F p
      = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x in UnforcedLeray.Cyl.cell c, F (s, x) := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
    lintegral_prod _ hF.aemeasurable]

/-- The age integral written over `(0,∞) × cell` (`Axi.lintegral_ageμ`, `qCell = Cyl.cell`). -/
theorem sliceAE_lint_ageμ {c : ℝ} (hc : 0 < c) (a : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c, ENNReal.ofReal (c⁻¹ * p.1 ^ a) * f p
      = ∫⁻ p, f p ∂(UnforcedLeray.Axi.ageμ c a) :=
  (UnforcedLeray.Axi.lintegral_ageμ hc a hf).symm

/-- Squeeze by a positive finite factor. -/
theorem sliceAE_squeeze {A : ℝ≥0∞} (hA0 : A ≠ 0) (hAt : A ≠ ⊤) {X Y : ℕ → ℝ≥0∞}
    (hle : ∀ n, A * X n ≤ Y n) (hY : Tendsto Y atTop (𝓝 0)) :
    Tendsto X atTop (𝓝 0) := by
  have hA' : A⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hA0
  have hup : Tendsto (fun n => A⁻¹ * Y n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hY (Or.inr hA')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => zero_le) (fun n => ?_)
  have hn := hle n
  calc X n = A⁻¹ * (A * X n) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 hAt, one_mul]
    _ ≤ A⁻¹ * Y n := by gcongr

/-- **Core lemma.** If the age-cell integrals of `K n` tend to `0`, a subsequence has, for a.e.
`s`, cell integrals `∫⁻_cell K (φ n)(s,·)` tending to `0`. -/
theorem sliceAE_core {c : ℝ} (K : ℕ → ℝ × (ℝ × ℝ) → ℝ≥0∞) (hK : ∀ n, Measurable (K n))
    (hI : Tendsto (fun n => ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c, K n p) atTop
      (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        Tendsto (fun n => ∫⁻ x in UnforcedLeray.Cyl.cell c, K (φ n) (s, x)) atTop (𝓝 0) := by
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨φ, hφmono, hφ⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c, K (φ k) p < 2⁻¹ ^ k := by
    refine Filter.extraction_forall_of_eventually
      (P := fun k n => ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c, K n p < 2⁻¹ ^ k)
      fun k => ?_
    exact hI.eventually (Iio_mem_nhds (ENNReal.pow_pos (ENNReal.inv_pos.2 h2top) k))
  have hS : ∀ k, Measurable fun s : ℝ => ∫⁻ x in UnforcedLeray.Cyl.cell c, K (φ k) (s, x) :=
    fun k => Measurable.lintegral_prod_right' (hK (φ k))
  have hlt : ∫⁻ s in Ioi (0 : ℝ), ∑' k, ∫⁻ x in UnforcedLeray.Cyl.cell c, K (φ k) (s, x)
      = ∑' k, ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x in UnforcedLeray.Cyl.cell c, K (φ k) (s, x) :=
    lintegral_tsum fun k => (hS k).aemeasurable
  have hgeo : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact h2top
  have hsum : ∫⁻ s in Ioi (0 : ℝ), ∑' k, ∫⁻ x in UnforcedLeray.Cyl.cell c, K (φ k) (s, x) ≠ ⊤ := by
    rw [hlt]
    refine ne_top_of_le_ne_top hgeo (ENNReal.tsum_le_tsum fun k => ?_)
    rw [← sliceAE_tonelli (K (φ k)) (hK (φ k))]
    exact (hφ k).le
  have hT : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∑' k, ∫⁻ x in UnforcedLeray.Cyl.cell c, K (φ k) (s, x) < ⊤ :=
    ae_lt_top' (Measurable.ennreal_tsum hS).aemeasurable hsum
  refine ⟨φ, hφmono, hT.mono fun s hs => ?_⟩
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne

/-! ### Measurability of the integrand -/

theorem sliceAE_measurable_gInv (γ ν : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := by
  unfold gainG
  have h1 : Measurable fun p : ℝ × (ℝ × ℝ) => γ * p.1 := measurable_fst.const_mul γ
  have h2 : Measurable fun p : ℝ × (ℝ × ℝ) => 1 + ν * p.1 :=
    (measurable_fst.const_mul ν).const_add 1
  have h3 : Measurable fun p : ℝ × (ℝ × ℝ) => γ * p.1 / (1 + ν * p.1) := h1.div h2
  exact (Real.continuous_exp.measurable.comp h3).inv

theorem sliceAE_meas_weight (c a : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ a) :=
  ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const a).const_mul c⁻¹)

theorem sliceAE_meas_sq_v (γ ν : ℝ) {bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hbn : ∀ n i, Measurable fun p => bn n p i)
    (hb : ∀ i, Measurable fun p => b p i) (n : ℕ) :
    Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * vnorm2 (fun i => bn n p i - b p i)) ^ 2 := by
  have hv : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (fun i => bn n p i - b p i) :=
    causalLin_measurable_vnorm2 (f := fun p i => bn n p i - b p i)
      fun i => (hbn n i).sub (hb i)
  exact (ENNReal.measurable_ofReal.comp ((sliceAE_measurable_gInv γ ν).mul hv)).pow_const 2

theorem sliceAE_meas_sq_t (γ ν : ℝ) {Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hGn : ∀ n i j, Measurable fun p => Gn n p i j)
    (hG : ∀ i j, Measurable fun p => G p i j) (n : ℕ) :
    Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * tnorm2 (fun i j => Gn n p i j - G p i j)) ^ 2 := by
  have hT : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (fun i j => Gn n p i j - G p i j) :=
    causalLin_measurable_tnorm2 (f := fun p i j => Gn n p i j - G p i j)
      fun i j => (hGn n i j).sub (hG i j)
  exact (ENNReal.measurable_ofReal.comp ((sliceAE_measurable_gInv γ ν).mul hT)).pow_const 2

/-- The integrand: the `𝓗`-part (weight `c⁻¹ s^{-3/2}`) plus the `𝒯`-part (weight `c⁻¹ s^{-1/2}`),
both squared on the gain-conjugated differences. -/
def sliceAE_K (γ ν c : ℝ) (bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (n : ℕ) (p : ℝ × (ℝ × ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) *
      ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * vnorm2 (fun i => bn n p i - b p i)) ^ 2 +
    ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
      ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * tnorm2 (fun i j => Gn n p i j - G p i j)) ^ 2

theorem sliceAE_measurable_K (γ ν c : ℝ) {bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hbn : ∀ n i, Measurable fun p => bn n p i) (hb : ∀ i, Measurable fun p => b p i)
    (hGn : ∀ n i j, Measurable fun p => Gn n p i j) (hG : ∀ i j, Measurable fun p => G p i j)
    (n : ℕ) : Measurable fun p => sliceAE_K γ ν c bn Gn b G n p := by
  unfold sliceAE_K
  exact ((sliceAE_meas_weight c (-3 / 2)).mul (sliceAE_meas_sq_v γ ν hbn hb n)).add
    ((sliceAE_meas_weight c (-1 / 2)).mul (sliceAE_meas_sq_t γ ν hGn hG n))

/-! ### The main theorem -/

theorem causalSliceAE : CausalSliceAE := by
  unfold CausalSliceAE
  intro c ν γ hc hν bn Gn b G hbn hb hGn hG hcal htcal
  -- The two hypotheses, as age integrals of squared norms.
  have hJ1 : Tendsto (fun n => ∫⁻ p, ENNReal.ofReal
      ((gainG γ ν p.1)⁻¹ * vnorm2 (fun i => bn n p i - b p i)) ^ 2
      ∂UnforcedLeray.Axi.ageμ c (-3 / 2)) atTop (𝓝 0) := by
    have hcongr : ∀ n, ∫⁻ p, ‖vnorm2 (gainConj γ ν (fun p i => bn n p i - b p i) p)‖ₑ ^ 2
        ∂UnforcedLeray.Axi.ageμ c (-3 / 2)
        = ∫⁻ p, ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * vnorm2 (fun i => bn n p i - b p i)) ^ 2
          ∂UnforcedLeray.Axi.ageμ c (-3 / 2) := fun n =>
      lintegral_congr fun p => by rw [sliceAE_enorm_vnorm2]
    exact Tendsto.congr hcongr
      (sliceAE_lint_sq_tendsto (μ := UnforcedLeray.Axi.ageμ c (-3 / 2))
        (F := fun n p => vnorm2 (gainConj γ ν (fun p i => bn n p i - b p i) p)) hcal)
  have hJ2 : Tendsto (fun n => ∫⁻ p, ENNReal.ofReal
      ((gainG γ ν p.1)⁻¹ * tnorm2 (fun i j => Gn n p i j - G p i j)) ^ 2
      ∂UnforcedLeray.Axi.ageμ c (-1 / 2)) atTop (𝓝 0) := by
    have hcongr : ∀ n, ∫⁻ p, ‖tnorm2 (gainConj γ ν (fun p i j => Gn n p i j - G p i j) p)‖ₑ ^ 2
        ∂UnforcedLeray.Axi.ageμ c (-1 / 2)
        = ∫⁻ p, ENNReal.ofReal
            ((gainG γ ν p.1)⁻¹ * tnorm2 (fun i j => Gn n p i j - G p i j)) ^ 2
          ∂UnforcedLeray.Axi.ageμ c (-1 / 2) := fun n =>
      lintegral_congr fun p => by rw [sliceAE_enorm_tnorm2]
    exact Tendsto.congr hcongr
      (sliceAE_lint_sq_tendsto (μ := UnforcedLeray.Axi.ageμ c (-1 / 2))
        (F := fun n p => tnorm2 (gainConj γ ν (fun p i j => Gn n p i j - G p i j) p)) htcal)
  -- Split the sum of the two age integrals into one integral over `(0,∞) × cell`.
  have hsplit : ∀ n, ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c,
        sliceAE_K γ ν c bn Gn b G n p
      = (∫⁻ p, ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * vnorm2 (fun i => bn n p i - b p i)) ^ 2
            ∂UnforcedLeray.Axi.ageμ c (-3 / 2))
        + ∫⁻ p, ENNReal.ofReal
            ((gainG γ ν p.1)⁻¹ * tnorm2 (fun i j => Gn n p i j - G p i j)) ^ 2
          ∂UnforcedLeray.Axi.ageμ c (-1 / 2) := by
    intro n
    unfold sliceAE_K
    have hf1 : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) *
        ENNReal.ofReal ((gainG γ ν p.1)⁻¹ * vnorm2 (fun i => bn n p i - b p i)) ^ 2 :=
      (sliceAE_meas_weight c (-3 / 2)).mul (sliceAE_meas_sq_v γ ν hbn hb n)
    rw [lintegral_add_left hf1]
    congr 1
    · exact sliceAE_lint_ageμ hc _ (sliceAE_meas_sq_v γ ν hbn hb n)
    · exact sliceAE_lint_ageμ hc _ (sliceAE_meas_sq_t γ ν hGn hG n)
  have hI : Tendsto (fun n => ∫⁻ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c,
      sliceAE_K γ ν c bn Gn b G n p) atTop (𝓝 0) := by
    have hsum := hJ1.add hJ2
    rw [add_zero] at hsum
    exact Tendsto.congr (fun n => (hsplit n).symm) hsum
  have hK : ∀ n, Measurable fun p => sliceAE_K γ ν c bn Gn b G n p := fun n =>
    sliceAE_measurable_K γ ν c hbn hb hGn hG n
  obtain ⟨φ, hφ, hae⟩ := sliceAE_core (c := c) (fun n p => sliceAE_K γ ν c bn Gn b G n p) hK hI
  refine ⟨φ, hφ, ?_⟩
  have hcell : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  simp only [hcell]
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with s hs hspos
  have hs0 : (0 : ℝ) < s := hspos
  have hgs : 0 < (gainG γ ν s)⁻¹ := inv_pos.2 (sliceAE_gainG_pos γ ν s)
  have hcsA : 0 < c⁻¹ * s ^ (-3 / 2 : ℝ) := mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hs0 _)
  have hcsB : 0 < c⁻¹ * s ^ (-1 / 2 : ℝ) := mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hs0 _)
  have hgs2 : ENNReal.ofReal ((gainG γ ν s)⁻¹) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ENNReal.ofReal_pos.2 hgs).ne'
  have hgs2t : ENNReal.ofReal ((gainG γ ν s)⁻¹) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hA0 : ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal ((gainG γ ν s)⁻¹) ^ 2 ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 hcsA).ne' hgs2
  have hAt : ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal ((gainG γ ν s)⁻¹) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgs2t
  have hB0 : ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) * ENNReal.ofReal ((gainG γ ν s)⁻¹) ^ 2 ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 hcsB).ne' hgs2
  have hBt : ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) * ENNReal.ofReal ((gainG γ ν s)⁻¹) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgs2t
  refine ⟨?_, ?_⟩
  · -- the `𝓗`-slices (vnorm2)
    refine sliceAE_squeeze hA0 hAt (fun n => ?_) hs
    rw [← lintegral_const_mul' _ _ hAt]
    refine lintegral_mono fun x => ?_
    unfold sliceAE_K
    exact le_trans (le_of_eq (sliceAE_key _ hgs.le (sliceAE_vnorm2_nonneg _))) le_self_add
  · -- the `𝒯`-slices (tnorm2)
    refine sliceAE_squeeze hB0 hBt (fun n => ?_) hs
    rw [← lintegral_const_mul' _ _ hBt]
    refine lintegral_mono fun x => ?_
    unfold sliceAE_K
    exact le_trans (le_of_eq (sliceAE_key _ hgs.le (sliceAE_tnorm2_nonneg _))) le_add_self

end UnforcedLeray.Short.IIIa
