import UnforcedLeray.Short.PartIIb.Sub.T08

/-!
# Part II-b, task `PartII-b:T08/2` (`DriftApprox`): decomposition into three approximation stages

Source of record: `the November 2 reference manuscript`, lines 1900-1915
(`H_r = L^r(s^{r/2-5/2} ds dq/c dη)`, `S = s∂_s`, `𝒯(√s b) = √s (S + 1/2) b`).  The density of
nice profiles in `{b ∈ H_r : S b ∈ H_r}` for the graph norm is obtained in three stages, each an
`ε`-approximation inside the class produced by the previous one:

1. `DriftSCutApprox`: cut off in `s` to `[s₀, s₁] ⊂ (0, ∞)`;
2. `DriftEtaCutApprox`: cut off in `η` to `|η| ≤ L`;
3. `DriftMollApprox`: mollify in `(log s, q, η)` (periodicity in `q` is preserved).

`driftApprox_of` proves `DriftApprox` from the three stages (triangle inequality in `H_r`
and a diagonal choice `ε = 1/(n+1)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The graph class: `b, Sb ∈ H_r` and `S b = Sb` weakly (`S = s∂_s`). -/
def DriftPair (c r : ℝ) (b Sb : CProf) : Prop :=
  InHr c r b ∧ InHr c r Sb ∧ HasWeakVec vS dZero b Sb

/-- Vanishing outside the `s`-window `[s₀, s₁]`. -/
def SCut (s₀ s₁ : ℝ) (f : CProf) : Prop := ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1) → f x = 0

/-- Vanishing for `|η| > L`. -/
def EtaCut (L : ℝ) (f : CProf) : Prop := ∀ x : Coord, L < |x.2.2| → f x = 0

/-- Graph pairs supported in a compact `s`-window inside `s > 0`. -/
def DriftPairS (c r : ℝ) (b Sb : CProf) : Prop :=
  DriftPair c r b Sb ∧ ∃ s₀ s₁ : ℝ, 0 < s₀ ∧ SCut s₀ s₁ b ∧ SCut s₀ s₁ Sb

/-- Graph pairs supported in a compact `s`-window and a bounded `η`-range. -/
def DriftPairSE (c r : ℝ) (b Sb : CProf) : Prop :=
  DriftPairS c r b Sb ∧ ∃ L : ℝ, EtaCut L b ∧ EtaCut L Sb

/-- Graph-norm `ε`-closeness of `(b', Sb')` to `(b, Sb)` in `H_r`. -/
def DriftClose (c r : ℝ) (b Sb b' Sb' : CProf) (ε : ℝ) : Prop :=
  hNorm c r (fun x => b' x - b x) < ENNReal.ofReal ε ∧
    hNorm c r (fun x => Sb' x - Sb x) < ENNReal.ofReal ε

/-- **Stage 1 (`s`-cutoff)** (SP 1912-1915): a graph pair is `ε`-approximated in the graph norm by
a graph pair supported in a compact window `s ∈ [s₀, s₁] ⊂ (0,∞)`.  Multiply by
`χ_n(log s)`: `S(χ_n b) = χ_n Sb + (Sχ_n) b`, `Sχ_n` bounded and supported where `χ_n` is not `1`,
so `(Sχ_n) b → 0` in `H_r` by dominated convergence. -/
def DriftSCutApprox : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPair c r b Sb →
    ∀ ε : ℝ, 0 < ε → ∃ b' Sb' : CProf, DriftPairS c r b' Sb' ∧ DriftClose c r b Sb b' Sb' ε

/-- **Stage 2 (`η`-cutoff)** (SP 1912-1915): multiply by `χ(η/n)`; it commutes with `S`, and
`∂_η`-free, so only the truncation error `→ 0` in `H_r` by dominated convergence. -/
def DriftEtaCutApprox : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPairS c r b Sb →
    ∀ ε : ℝ, 0 < ε → ∃ b' Sb' : CProf, DriftPairSE c r b' Sb' ∧ DriftClose c r b Sb b' Sb' ε

/-- **Stage 3 (mollification)** (SP 1912-1915): convolve in the variables `(log s, q, η)` with a
product mollifier.  The dilation group `s ↦ λ s` acts on `H_r` by isometries up to the weight and
commutes with `S`, so `S(ρ * b) = ρ * Sb`; convolution in `(q, η)` preserves `c`-periodicity;
the result is smooth, periodic everywhere, and supported in a slightly larger compact window.
Convergence in `H_r` is strong continuity of translations in `L^r` (`1 < r < ∞`). -/
def DriftMollApprox : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → DriftPairSE c r b Sb →
    ∀ ε : ℝ, 0 < ε → ∃ b' Sb' : CProf, NiceProf c b' ∧ DriftPair c r b' Sb' ∧
      DriftClose c r b Sb b' Sb' ε

theorem hNorm_sub_trans_le {c r : ℝ} (hr : 1 < r) {f g h : CProf} (hf : InHr c r f)
    (hg : InHr c r g) (hh : InHr c r h) :
    hNorm c r (fun x => h x - f x) ≤
      hNorm c r (fun x => h x - g x) + hNorm c r (fun x => g x - f x) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have e : (fun x => h x - f x) = (fun x => h x - g x) + (fun x => g x - f x) := by
    funext x; simp
  unfold hNorm
  rw [e]
  exact eLpNorm_add_le (hh.meas.sub hg.meas) (hg.meas.sub hf.meas) hr1

theorem driftClose_trans {c r : ℝ} (hr : 1 < r) {b Sb b' Sb' b'' Sb'' : CProf} {δ₁ δ₂ : ℝ}
    (h₀ : δ₁ ≥ 0) (h₁ : δ₂ ≥ 0)
    (hb : InHr c r b) (hSb : InHr c r Sb) (hb' : InHr c r b') (hSb' : InHr c r Sb')
    (hb'' : InHr c r b'') (hSb'' : InHr c r Sb'')
    (c1 : DriftClose c r b Sb b' Sb' δ₁) (c2 : DriftClose c r b' Sb' b'' Sb'' δ₂) :
    DriftClose c r b Sb b'' Sb'' (δ₁ + δ₂) := by
  rw [DriftClose, add_comm δ₁ δ₂, ENNReal.ofReal_add h₁ h₀]
  refine ⟨lt_of_le_of_lt (hNorm_sub_trans_le hr hb hb' hb'') ?_,
    lt_of_le_of_lt (hNorm_sub_trans_le hr hSb hSb' hSb'') ?_⟩
  · exact ENNReal.add_lt_add c2.1 c1.1
  · exact ENNReal.add_lt_add c2.2 c1.2

/-- The three stages give nice approximants of any graph pair, to any tolerance. -/
theorem drift_nice_approx (h1 : DriftSCutApprox) (h2 : DriftEtaCutApprox) (h3 : DriftMollApprox)
    (c r : ℝ) (b Sb : CProf) (hc : 0 < c) (hr : 1 < r) (hp : DriftPair c r b Sb)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b' Sb' : CProf, NiceProf c b' ∧ DriftPair c r b' Sb' ∧ DriftClose c r b Sb b' Sb' ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨b1, Sb1, hp1, hc1⟩ := h1 c r b Sb hc hr hp (ε / 3) hε3
  obtain ⟨b2, Sb2, hp2, hc2⟩ := h2 c r b1 Sb1 hc hr hp1 (ε / 3) hε3
  obtain ⟨b3, Sb3, hn3, hp3, hc3⟩ := h3 c r b2 Sb2 hc hr hp2 (ε / 3) hε3
  refine ⟨b3, Sb3, hn3, hp3, ?_⟩
  have i1 := hp1.1
  have i2 := hp2.1.1
  have c12 := driftClose_trans (δ₁ := ε / 3) (δ₂ := ε / 3) hr hε3.le hε3.le hp.1 hp.2.1
    i1.1 i1.2.1 i2.1 i2.2.1 hc1 hc2
  have c123 := driftClose_trans (δ₁ := ε / 3 + ε / 3) (δ₂ := ε / 3) hr (by positivity) hε3.le
    hp.1 hp.2.1 i2.1 i2.2.1 hp3.1 hp3.2.1 c12 hc3
  have : ε / 3 + ε / 3 + ε / 3 = ε := by ring
  rwa [this] at c123

/-- **`DriftApprox` from the three approximation stages.** -/
theorem driftApprox_of (h1 : DriftSCutApprox) (h2 : DriftEtaCutApprox) (h3 : DriftMollApprox) :
    DriftApprox := by
  intro c r b Sb hc hr hb hSb hw
  have hp : DriftPair c r b Sb := ⟨hb, hSb, hw⟩
  have key : ∀ n : ℕ, ∃ b' Sb' : CProf, NiceProf c b' ∧ DriftPair c r b' Sb' ∧
      DriftClose c r b Sb b' Sb' (1 / ((n : ℝ) + 1)) := fun n =>
    drift_nice_approx h1 h2 h3 c r b Sb hc hr hp _ (by positivity)
  choose bn Sbn hn hp' hcl using key
  refine ⟨bn, Sbn, fun n => ⟨hn n, (hp' n).2.2, (hp' n).1, (hp' n).2.1⟩, ?_, ?_⟩
  · have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => bot_le) (fun n => (hcl n).1.le)
  · have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => bot_le) (fun n => (hcl n).2.le)

end UnforcedLeray.Short.IIb
