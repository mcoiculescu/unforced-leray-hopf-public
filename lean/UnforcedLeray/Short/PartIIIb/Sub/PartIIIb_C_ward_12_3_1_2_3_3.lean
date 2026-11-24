import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2

/-!
# Decomposition of `GradL2pAssemble` (source 2531)

Source of record `the November 2 reference manuscript`,
line 2531: `‖Dw‖²_{Y_{2p}} ≤ C ‖w‖_∞ ‖D²w‖_{Y_p}` from the slice integration by parts, integrated over
the period, Hölder with exponents `2p/(2p-2)` and `p`, and the mollification limit (Fatou).

`gradL2pAssemble_of` proves `GradL2pAssemble` from `BddMemLpDouble`, `SliceIntegrate`,
`HolderStep`, `FatouLimit`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (rep)

/-- Lemma 0 (Haiku): a bounded `L^{q₀}` function is in `L^{2q₀}` (`|G|^{2q} ≤ K^q |G|^q`). -/
def BddMemLpDouble : Prop :=
  ∀ (μ : Measure (ℝ × UnforcedLeray.Space))
    (G : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    AEStronglyMeasurable G μ → (∃ K : ℝ, ∀ x, ‖G x‖ ≤ K) →
    MemLp G UnforcedLeray.B0412.q0E μ → MemLp G (2 * UnforcedLeray.B0412.q0E) μ

/-- Lemma 1 (Tonelli over the period): the slice inequality `GradL2pSlice` integrated over
`τ ∈ (0,P]` (`phaseμ P = (dτ|_{(0,P]}) ⊗ dy`, `lintegral_prod`; the slice facts hold for every
`τ`). -/
def SliceIntegrate : Prop :=
  GradL2pSlice → ∀ (P : ℝ) [Fact (0 < P)]
    (W G H : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (M : ℝ) (j : Fin 3),
    0 ≤ M →
    (∀ τ, SmoothSlice M j (fun y => W (τ, y)) (fun y => G (τ, y)) (fun y => H (τ, y))) →
    (∀ τ, MemLp (fun y => G (τ, y)) UnforcedLeray.B0412.q0E volume ∧
      MemLp (fun y => H (τ, y)) UnforcedLeray.B0412.q0E volume) →
    AEStronglyMeasurable G (phaseμ P) → AEStronglyMeasurable H (phaseμ P) →
    ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal)) ∂(phaseμ P) ≤
      ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
        ∫⁻ x, ENNReal.ofReal
          (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H x‖) ∂(phaseμ P)

/-- Lemma 2 (Hölder with exponents `2q/(2q-2)` and `q`, then divide by the finite
`‖G‖_{2q}^{2q-... }`): if `G ∈ L^{2q}` and
`∫|G|^{2q} ≤ C ∫|G|^{2q-2}|H|` then `‖G‖_{2q}² ≤ C ‖H‖_q`. (With `X = ∫|G|^{2q} < ∞`,
Hölder gives `X ≤ C X^{(2q-2)/(2q)} ‖H‖_q`, so `X^{1/q} ≤ C‖H‖_q`; `X = 0` trivial.) -/
def HolderStep : Prop :=
  ∀ (μ : Measure (ℝ × UnforcedLeray.Space))
    (G H : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (C : ℝ),
    AEStronglyMeasurable G μ → AEStronglyMeasurable H μ →
    MemLp G (2 * UnforcedLeray.B0412.q0E) μ →
    ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal)) ∂μ ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H x‖) ∂μ →
    eLpNorm G (2 * UnforcedLeray.B0412.q0E) μ ^ 2 ≤
      ENNReal.ofReal C * eLpNorm H UnforcedLeray.B0412.q0E μ

/-- Lemma 3 (limit): if `G n → g`, `H n → h` in `L^{q}(μ)`, `h ∈ L^q`, and
`‖G n‖_{2q}² ≤ C ‖H n‖_q` eventually (`C < ∞`), then `g ∈ L^{2q}` and
`‖g‖_{2q}² ≤ C ‖h‖_q`.  (Subsequence converging a.e., Fatou `lintegral_liminf_le` for
`∫|g|^{2q}`; `‖H n‖_q → ‖h‖_q` by continuity of the norm.) -/
def FatouLimit : Prop :=
  ∀ (μ : Measure (ℝ × UnforcedLeray.Space))
    (G H : ℕ → ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (g h : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (C : ℝ≥0∞),
    C ≠ ⊤ → (∀ n, AEStronglyMeasurable (G n) μ) → AEStronglyMeasurable g μ →
    MemLp h UnforcedLeray.B0412.q0E μ →
    Tendsto (fun n => eLpNorm (G n - g) UnforcedLeray.B0412.q0E μ) atTop (𝓝 0) →
    Tendsto (fun n => eLpNorm (H n - h) UnforcedLeray.B0412.q0E μ) atTop (𝓝 0) →
    (∀ᶠ n in atTop, eLpNorm (G n) (2 * UnforcedLeray.B0412.q0E) μ ^ 2 ≤
      C * eLpNorm (H n) UnforcedLeray.B0412.q0E μ) →
    MemLp g (2 * UnforcedLeray.B0412.q0E) μ ∧
      eLpNorm g (2 * UnforcedLeray.B0412.q0E) μ ^ 2 ≤ C * eLpNorm h UnforcedLeray.B0412.q0E μ

/-- `GradL2pAssemble` from the four lemmas. -/
theorem gradL2pAssemble_of (a0 : BddMemLpDouble) (a1 : SliceIntegrate) (a2 : HolderStep)
    (a3 : FatouLimit) : GradL2pAssemble := by
  intro hMoll hSlice P _ w g h M hM0 hwM hwg hgh j
  set q := UnforcedLeray.B0412.q0E with hq
  obtain ⟨W, G, H, hS, hMem, hbdd, hmeas, hG, hH⟩ :=
    hMoll P w (g j) (h j j) M j hM0 hwM (hwg j) (hgh j j)
  have hgmem := memLp_rep_phase (g j)
  have hhmem := memLp_rep_phase (h j j)
  have hgmeas : AEStronglyMeasurable (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
      (phaseμ P) := hgmem.1
  have ev : ∀ᶠ n in atTop, eLpNorm (fun x => G n x - rep (g j) x.1 x.2) q (phaseμ P) < 1 :=
    (tendsto_order.1 hG).2 1 one_pos
  have hineq : ∀ᶠ n in atTop, eLpNorm (G n) (2 * q) (phaseμ P) ^ 2 ≤
      ENNReal.ofReal ((2 * q.toReal - 1) * M) * eLpNorm (H n) q (phaseμ P) := by
    filter_upwards [ev] with n hn
    have hsub : MemLp (fun x => G n x - rep (g j) x.1 x.2) q (phaseμ P) :=
      ⟨((hmeas n).1.sub hgmeas), hn.trans ENNReal.one_lt_top⟩
    have hGq : MemLp (G n) q (phaseμ P) := by
      have := hsub.add hgmem
      have e : G n = (fun x => G n x - rep (g j) x.1 x.2) + fun x => rep (g j) x.1 x.2 := by
        funext x; simp
      rw [e]; exact this
    have hG2 : MemLp (G n) (2 * q) (phaseμ P) := a0 _ _ (hmeas n).1 (hbdd n) hGq
    exact a2 _ _ _ _ (hmeas n).1 (hmeas n).2 hG2
      (a1 hSlice P (W n) (G n) (H n) M j hM0 (hS n) (hMem n) (hmeas n).1 (hmeas n).2)
  obtain ⟨h1, h2⟩ := a3 (phaseμ P) G H (fun x => rep (g j) x.1 x.2) (fun x => rep (h j j) x.1 x.2)
    (ENNReal.ofReal ((2 * q.toReal - 1) * M)) ENNReal.ofReal_ne_top (fun n => (hmeas n).1) hgmeas
    hhmem hG hH hineq
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_right (Finset.single_le_sum (f := fun k => eLpNorm
    (fun x : ℝ × UnforcedLeray.Space => rep (h j k) x.1 x.2) q (phaseμ P))
    (fun _ _ => zero_le) (Finset.mem_univ j)) _

end UnforcedLeray.Short.PartIIIb.Concrete
