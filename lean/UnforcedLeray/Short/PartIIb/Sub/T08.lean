import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b, task `PartII-b:T08`: the drift of the ring lift (conditional)

Source of record: `the November 2 reference manuscript`, lines 1912-1915
(`𝒯(√s b) = √s (S + 1/2) b`, `𝒯 = ∂_τ - y·∇/2`).

Target (`hasPtwOp_driftT_NvC`): for `b, Sb ∈ H_r` with `S b = Sb` weakly (`S = s∂_s`),
`HasPtwOp (2εc) driftT (NvC ε⁻¹ b) (NvC ε⁻¹ (Sb + b/2))`.

Route: prove the identity on nice profiles, approximate in `H_r`, pass to the limit by continuity
of the pairing `b ↦ ⟪Φ, N_v b⟫` on `H_r`.

* `DriftSmooth` (`T08/1`): the identity for `NiceProf` `b` (change of variables
  `(τ, y) ↦ (s, q, η)`, `driftT` becomes `-S - 1/2` on the chart, integrate by parts);
* `DriftApprox` (`T08/2`): density of `NiceProf` among `{b ∈ H_r, Sb ∈ H_r}` for the graph norm
  (mollify in `log s` against the multiplicative group, `q, η`-mollify, cut off in `s` and `η`);
* `DriftPairCont` (`T08/3`, uses `T07` `phaseLpNorm_NvC`): `b ↦ pairF P Φ (N_v b)` is continuous for
  the `H_r` norm, for a phase test `Φ`.

Proved here: `hasPtwOp_driftT_NvC_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- A *nice* profile: smooth, `c`-periodic in `q` (everywhere), vanishing outside a compact set of
`(s, η)` inside `s > 0`. -/
def NiceProf (c : ℝ) (b : CProf) : Prop :=
  ContDiff ℝ ∞ b ∧ (∀ x, b (qShift c x) = b x) ∧
    ∃ s₀ s₁ L : ℝ, 0 < s₀ ∧ ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → b x = 0

/-- **Leaf `PartII-b:T08/1`** (SP 1912-1915): the drift identity for nice profiles.  Proof: for a
phase test `Φ` the pairing `pairF P (driftT Φ) (N_v b)` is, in the chart `(τ, y) ↦ (s, q, η)`
(`Axi.chart`, `Lib/Axisymmetric/RingChart.lean`; `e_r, e_z` are dilation invariant), an integral
over `Coord`, and `𝒯ᵗ` is the transpose of `-(S + 1/2)` on `√s b`; `HasWeakVec vS dZero b Sb`
identifies `Sb` a.e. with `s∂_s b`. -/
def DriftSmooth : Prop :=
  ∀ (c ε : ℝ) (b Sb : CProf), 0 < c → 0 < ε → NiceProf c b → HasWeakVec vS dZero b Sb →
    HasPtwOp (2 * ε * c) driftT (NvC ε⁻¹ b) (NvC ε⁻¹ (fun x => Sb x + (1 / 2 : ℂ) • b x))

/-- **Leaf `PartII-b:T08/2`** (graph-norm density; SP 1912-1915): if `b, Sb ∈ H_r` with
`S b = Sb` weakly, there are nice `bₙ` with `S bₙ = Sbₙ` weakly, `bₙ, Sbₙ ∈ H_r`, and
`bₙ → b`, `Sbₙ → Sb` in `H_r`.  Proof: mollify in `log s` (the dilations act isometrically on
`H_r` up to the weights, and commute with `S`), mollify in `(q, η)` keeping `c`-periodicity, and
cut off in `s` and `η`; the cutoff commutators `S χ_n` are bounded and tend to `0` in `L^r`. -/
def DriftApprox : Prop :=
  ∀ (c r : ℝ) (b Sb : CProf), 0 < c → 1 < r → InHr c r b → InHr c r Sb →
    HasWeakVec vS dZero b Sb →
    ∃ bn Sbn : ℕ → CProf, (∀ n, NiceProf c (bn n) ∧ HasWeakVec vS dZero (bn n) (Sbn n) ∧
        InHr c r (bn n) ∧ InHr c r (Sbn n)) ∧
      Tendsto (fun n => hNorm c r (fun x => bn n x - b x)) atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c r (fun x => Sbn n x - Sb x)) atTop (𝓝 0)

/-- **Leaf `PartII-b:T08/3`** (uses `T07`; SP 1902-1906): the pairing with a phase test is
continuous for the `H_r` norm.  Proof: `N_v` is additive (`NvC R (b - b') = NvC R b - NvC R b'`),
`‖N_v b‖_{Y_r} = (πR²)^{1/r}‖b‖_{H_r}` (`phaseLpNorm_NvC`), and Hölder against the compactly
supported smooth `Φ` over one period. -/
def DriftPairCont : Prop :=
  ∀ (c r ε : ℝ) (Φ : ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → IsPhaseTest (2 * ε * c) Φ →
    ∀ (b : CProf) (bn : ℕ → CProf), InHr c r b → (∀ n, InHr c r (bn n)) →
      Tendsto (fun n => hNorm c r (fun x => bn n x - b x)) atTop (𝓝 0) →
      Tendsto (fun n => pairF (2 * ε * c) Φ (NvC ε⁻¹ (bn n))) atTop
        (𝓝 (pairF (2 * ε * c) Φ (NvC ε⁻¹ b)))

/-- Triangle inequality for `f + (1/2) g` (measurability only). -/
theorem elp_add_half_le {μ : Measure Coord} {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : CProf}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f + (1 / 2 : ℂ) • g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  refine (eLpNorm_add_le hf (hg.const_smul (1 / 2 : ℂ)) hp).trans ?_
  gcongr
  refine (eLpNorm_const_smul_le (μ := μ) (p := p) (c := (1 / 2 : ℂ)) (f := g)).trans ?_
  have h1 : ‖(1 / 2 : ℂ)‖ₑ ≤ 1 := by
    rw [enorm_eq_nnnorm]; norm_num
  calc _ ≤ 1 * eLpNorm g p μ := by gcongr
    _ = _ := one_mul _

theorem hNorm_add_smul_le {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r f)
    (hg : InHr c r g) :
    hNorm c r (fun x => f x + (1 / 2 : ℂ) • g x) ≤ hNorm c r f + hNorm c r g := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  exact elp_add_half_le hr1 hf.meas hg.meas

/-- Triangle inequality for differences. -/
theorem hNorm_sub_add_smul_le {c r : ℝ} (hr : 1 < r) {f g f' g' : CProf} (hf : InHr c r f)
    (hg : InHr c r g) (hf' : InHr c r f') (hg' : InHr c r g') :
    hNorm c r (fun x => (f x + (1 / 2 : ℂ) • g x) - (f' x + (1 / 2 : ℂ) • g' x)) ≤
      hNorm c r (fun x => f x - f' x) + hNorm c r (fun x => g x - g' x) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have e : (fun x => (f x + (1 / 2 : ℂ) • g x) - (f' x + (1 / 2 : ℂ) • g' x)) =
      (f - f') + (1 / 2 : ℂ) • (g - g') := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_sub]
    abel
  rw [e]
  exact elp_add_half_le hr1 (hf.meas.sub hf'.meas) (hg.meas.sub hg'.meas)

/-- `H_r` is closed under `f + (1/2) g`. -/
theorem inHr_add_smul {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r f) (hg : InHr c r g) :
    InHr c r (fun x => f x + (1 / 2 : ℂ) • g x) := by
  refine ⟨?_, hf.meas.add (hg.meas.const_smul (1 / 2 : ℂ)), ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x h1 h2
    simp only [h1, h2]
  · exact lt_of_le_of_lt (hNorm_add_smul_le hr hf hg) (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

/-- **Target** `hasPtwOp_driftT_NvC` from its three leaves. -/
theorem hasPtwOp_driftT_NvC_of (h1 : DriftSmooth) (h2 : DriftApprox) (h3 : DriftPairCont)
    {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 1 < r) (b Sb : CProf) (hb : InHr c r b)
    (hSb : InHr c r Sb) (hS : HasWeakVec vS dZero b Sb) :
    HasPtwOp (2 * ε * c) driftT (NvC ε⁻¹ b) (NvC ε⁻¹ (fun x => Sb x + (1 / 2 : ℂ) • b x)) := by
  intro Φ hΦ
  obtain ⟨bn, Sbn, hn, t1, t2⟩ := h2 c r b Sb hc hr hb hSb hS
  have e : ∀ n, pairF (2 * ε * c) (driftT Φ) (NvC ε⁻¹ (bn n)) =
      pairF (2 * ε * c) Φ (NvC ε⁻¹ (fun x => Sbn n x + (1 / 2 : ℂ) • bn n x)) := fun n =>
    h1 c ε (bn n) (Sbn n) hc hε (hn n).1 (hn n).2.1 Φ hΦ
  have l1 := h3 c r ε (driftT Φ) hc hε hr hΦ.driftT b bn hb (fun n => (hn n).2.2.1) t1
  have hsum : InHr c r (fun x => Sb x + (1 / 2 : ℂ) • b x) := inHr_add_smul hr hSb hb
  have t3 : Tendsto (fun n => hNorm c r (fun x =>
      (Sbn n x + (1 / 2 : ℂ) • bn n x) - (Sb x + (1 / 2 : ℂ) • b x))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
      (fun n => hNorm_sub_add_smul_le hr (hn n).2.2.2 (hn n).2.2.1 hSb hb)
    simpa using t2.add t1
  have l2 := h3 c r ε Φ hc hε hr hΦ (fun x => Sb x + (1 / 2 : ℂ) • b x)
    (fun n x => Sbn n x + (1 / 2 : ℂ) • bn n x) hsum
    (fun n => inHr_add_smul hr (hn n).2.2.2 (hn n).2.2.1) t3
  simp only [e] at l1
  exact tendsto_nhds_unique l1 l2

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.hasPtwOp_driftT_NvC_of
