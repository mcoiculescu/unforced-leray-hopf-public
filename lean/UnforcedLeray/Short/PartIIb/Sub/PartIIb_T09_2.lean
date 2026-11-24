import UnforcedLeray.Short.PartIIb.Sub.T09
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_2

/-!
# Part II-b, task `PartII-b:T09/2` (`DivApprox`): density of nice profiles in the graph class

Source of record: `the November 2 reference manuscript`, lines 1639-1668 and
1912-1918.  Same three-stage scheme as `Sub/PartIIb_T08_2.lean`, with the pair `(b, Sb)` replaced
by the triple `(b, Q_ε b, ∂_η b)` and the graph norm
`‖b‖_{H_r} + ‖√s Q_ε b‖_{H_r} + ‖√s ∂_η b‖_{H_r}` (`DivData`):

* `DivSCutApprox` (`T09/2/1`): cut off in `s` (`Q_ε χ(log s) = -2ε Sχ` bounded);
* `DivEtaCutApprox` (`T09/2/2`): cut off in `η` (`Q_ε χ(η/n) = -ε (η/n) χ'(η/n)` bounded,
  `∂_η χ(η/n) = χ'(η/n)/n`);
* `DivMollApprox` (`T09/2/3`): mollify (needs the flow-adapted coordinates / Friedrichs commutator,
  since `Q_ε` has the `η`-dependent coefficient `-εη`).

Proved here: `divApprox_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Compact `s`-window `[s₀, s₁] ⊂ (0, ∞)` for the whole triple. -/
def DivDataS (c r ε : ℝ) (b Qb Eb : CProf) : Prop :=
  DivData c r ε b Qb Eb ∧ ∃ s₀ s₁ : ℝ, 0 < s₀ ∧ SCut s₀ s₁ b ∧ SCut s₀ s₁ Qb ∧ SCut s₀ s₁ Eb

/-- Compact `s`-window and bounded `η`-range for the whole triple. -/
def DivDataSE (c r ε : ℝ) (b Qb Eb : CProf) : Prop :=
  DivDataS c r ε b Qb Eb ∧ ∃ L : ℝ, EtaCut L b ∧ EtaCut L Qb ∧ EtaCut L Eb

/-- Graph-norm `δ`-closeness of a triple `(b', Qb', Eb')` to `(b, Qb, Eb)`. -/
def DivClose (c r : ℝ) (b Qb Eb b' Qb' Eb' : CProf) (δ : ℝ) : Prop :=
  hNorm c r (fun x => b' x - b x) < ENNReal.ofReal δ ∧
    hNorm c r (sqrtS fun x => Qb' x - Qb x) < ENNReal.ofReal δ ∧
    hNorm c r (sqrtS fun x => Eb' x - Eb x) < ENNReal.ofReal δ

/-- **Stage 1 (`T09/2/1`, `s`-cutoff)** (SP 1912-1918): multiply by `χ_n(log s)`.
`Q_ε(χ_n b) = χ_n Q_ε b - 2ε (Sχ_n) b` with `Sχ_n` bounded and supported where `χ_n ≠ 1`;
`∂_η(χ_n b) = χ_n ∂_η b`; the error terms tend to `0` in the graph norm (`√s` weights: on the
support of `Sχ_n` the extra `√s` is absorbed in `χ`-support, dominated convergence).
Mirror of `Tasks/DriftNvC/Approx/SCut.lean` (`DriftSCutApprox`). -/
def DivSCutApprox : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    ∀ δ : ℝ, 0 < δ → ∃ b' Qb' Eb' : CProf, DivDataS c r ε b' Qb' Eb' ∧
      DivClose c r b Qb Eb b' Qb' Eb' δ

/-- **Stage 2 (`T09/2/2`, `η`-cutoff)** (SP 1912-1918): multiply by `χ(η/n)`; mirror of
`Tasks/DriftNvC/Approx/EtaCut.lean` (`DriftEtaCutApprox`), with the extra commutator
`Q_ε χ(η/n) = -ε (η/n) χ'(η/n)` (bounded, supported in `n ≤ |η| ≤ 2n`) and
`∂_η χ(η/n) = χ'(η/n)/n`. -/
def DivEtaCutApprox : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivDataS c r ε b Qb Eb →
    ∀ δ : ℝ, 0 < δ → ∃ b' Qb' Eb' : CProf, DivDataSE c r ε b' Qb' Eb' ∧
      DivClose c r b Qb Eb b' Qb' Eb' δ

/-- **Stage 3 (`T09/2/3`, mollification)** (SP 1912-1918): approximate a compactly supported
triple by nice profiles whose weak derivatives lie in the graph class.  `Q_ε = ∂_q - 2ε ∂_u - εη∂_η
- ε` (`u = log s`) has constant coefficients in the flow coordinates `(u + 2εq, q, η e^{εq})`, where
it is `∂_q - ε`; `∂_η = e^{εq} ∂_ζ`.  Mollify there (or Friedrichs commutator for `-εη∂_η`). -/
def DivMollApprox : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivDataSE c r ε b Qb Eb →
    ∀ δ : ℝ, 0 < δ → ∃ b' Qb' Eb' : CProf, NiceProf c b' ∧ DivData c r ε b' Qb' Eb' ∧
      DivClose c r b Qb Eb b' Qb' Eb' δ

theorem sqrtS_sub (f g : CProf) :
    (sqrtS fun x => f x - g x) = fun x => sqrtS f x - sqrtS g x := by
  funext x; simp [sqrtS, smul_sub]

theorem hNorm_sub_trans_sqrt {c r : ℝ} (hr : 1 < r) {f g h : CProf} (hf : InHr c r (sqrtS f))
    (hg : InHr c r (sqrtS g)) (hh : InHr c r (sqrtS h)) :
    hNorm c r (sqrtS fun x => h x - f x) ≤
      hNorm c r (sqrtS fun x => h x - g x) + hNorm c r (sqrtS fun x => g x - f x) := by
  rw [sqrtS_sub, sqrtS_sub, sqrtS_sub]
  exact hNorm_sub_trans_le hr hf hg hh

theorem lt_trans_close {δ₁ δ₂ : ℝ} (h₀ : 0 ≤ δ₁) (h₁ : 0 ≤ δ₂) {x y z : ℝ≥0∞}
    (hxy : x ≤ y + z) (hy : y < ENNReal.ofReal δ₂) (hz : z < ENNReal.ofReal δ₁) :
    x < ENNReal.ofReal (δ₁ + δ₂) := by
  rw [add_comm δ₁ δ₂, ENNReal.ofReal_add h₁ h₀]
  exact lt_of_le_of_lt hxy (ENNReal.add_lt_add hy hz)

theorem divClose_trans {c r ε : ℝ} (hr : 1 < r) {b Qb Eb b' Qb' Eb' b'' Qb'' Eb'' : CProf}
    {δ₁ δ₂ : ℝ} (h₀ : 0 ≤ δ₁) (h₁ : 0 ≤ δ₂)
    (d0 : DivData c r ε b Qb Eb) (d1 : DivData c r ε b' Qb' Eb')
    (d2 : DivData c r ε b'' Qb'' Eb'')
    (c1 : DivClose c r b Qb Eb b' Qb' Eb' δ₁) (c2 : DivClose c r b' Qb' Eb' b'' Qb'' Eb'' δ₂) :
    DivClose c r b Qb Eb b'' Qb'' Eb'' (δ₁ + δ₂) :=
  ⟨lt_trans_close h₀ h₁ (hNorm_sub_trans_le hr d0.inHr d1.inHr d2.inHr) c2.1 c1.1,
   lt_trans_close h₀ h₁ (hNorm_sub_trans_sqrt hr d0.inQ d1.inQ d2.inQ) c2.2.1 c1.2.1,
   lt_trans_close h₀ h₁ (hNorm_sub_trans_sqrt hr d0.inE d1.inE d2.inE) c2.2.2 c1.2.2⟩

/-- The three stages give nice approximants of any graph triple, to any tolerance. -/
theorem div_nice_approx (h1 : DivSCutApprox) (h2 : DivEtaCutApprox) (h3 : DivMollApprox)
    (c r ε : ℝ) (b Qb Eb : CProf) (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r)
    (hp : DivData c r ε b Qb Eb) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b' Qb' Eb' : CProf, NiceProf c b' ∧ DivData c r ε b' Qb' Eb' ∧
      DivClose c r b Qb Eb b' Qb' Eb' δ := by
  have hr1 : 1 < r := by linarith
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨b1, Q1, E1, hp1, hc1⟩ := h1 c r ε b Qb Eb hc hε hr hp (δ / 3) hδ3
  obtain ⟨b2, Q2, E2, hp2, hc2⟩ := h2 c r ε b1 Q1 E1 hc hε hr hp1 (δ / 3) hδ3
  obtain ⟨b3, Q3, E3, hn3, hp3, hc3⟩ := h3 c r ε b2 Q2 E2 hc hε hr hp2 (δ / 3) hδ3
  refine ⟨b3, Q3, E3, hn3, hp3, ?_⟩
  have c12 := divClose_trans (δ₁ := δ / 3) (δ₂ := δ / 3) hr1 hδ3.le hδ3.le hp hp1.1 hp2.1.1
    hc1 hc2
  have c123 := divClose_trans (δ₁ := δ / 3 + δ / 3) (δ₂ := δ / 3) hr1 (by positivity) hδ3.le
    hp hp2.1.1 hp3 c12 hc3
  have : δ / 3 + δ / 3 + δ / 3 = δ := by ring
  rwa [this] at c123

/-- **`DivApprox` from the three approximation stages.** -/
theorem divApprox_of (h1 : DivSCutApprox) (h2 : DivEtaCutApprox) (h3 : DivMollApprox) :
    DivApprox := by
  intro c ε r b Qb Eb hc hε hr hp
  have key : ∀ n : ℕ, ∃ b' Qb' Eb' : CProf, NiceProf c b' ∧ DivData c r ε b' Qb' Eb' ∧
      DivClose c r b Qb Eb b' Qb' Eb' (1 / ((n : ℝ) + 1)) := fun n =>
    div_nice_approx h1 h2 h3 c r ε b Qb Eb hc hε hr hp _ (by positivity)
  choose bn Qn En hn hp' hcl using key
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  refine ⟨bn, Qn, En, fun n => ⟨hn n, hp' n⟩, ?_, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => bot_le) (fun n => (hcl n).1.le)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => bot_le) (fun n => (hcl n).2.1.le)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => bot_le) (fun n => (hcl n).2.2.le)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divApprox_of
