import UnforcedLeray.Short.PartIIb.Sub.T09_2_1.Weak
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Approx.SCut

/-!
# Part II-b, `PartII-b:T09/2/1`: the `s`-cutoff stage, corrected design

Source of record: `the November 2 reference manuscript`, lines 1639-1668 and
1898-1918 (`H_r`, `bg:profile-graph`, `∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`).

## Status of the old decomposition (organizer `oa1`, `PartII-b:T09/2/1/1/org`)

* **Lemma A** (`DivSqrtSb`, old `T09/2/1/1`) is FALSE for every `r > 2`: the graph triple of
  `b = θ(s) s^{-1/2} h(η/√s) e_r` has `‖√s b‖^r_{H_r} = ‖h‖_r^r ∫ θ^r s^{r/2-2} ds = ∞`
  (`Sub/T09_2_1/Counter.lean`, refutation `divSqrtSb_false_of`; task `PartII-b:T09R/1`).  The id
  `PartII-b:T09/2/1/1` now carries the first corrected leaf (`DivSCutWeak`), which replaces it.
* The old stage-1 target `DivSCutApprox` (strong graph norm) and the old `DivApprox` (`T09/2`) are
  FALSE for every `r > 2` (no compactly supported approximant can carry the axis trace of the
  radial lift; `Sub/T09_2_1/Refute.lean`, task `PartII-b:T09R/2`).  `DivSCutApproxSqrt` (old
  `T09/2/1/2`) is true but no longer used: the corrected stage 1 needs no `√s b ∈ H_r`; the id
  `PartII-b:T09/2/1/2` now carries `DivSCutInHr`.

## Corrected stage 1: `DivSCutApproxW` (`Sub/T09_2_1/Weak.lean`)

Cut by `χ_k(s) = sBump k s` (`DriftSCutHelp`, `Tasks/DriftNvC/Approx/SCut.lean`):
`b' = χ_k b`, `Q_ε b' = χ_k Q_ε b + D_k b` with `D_k = [Q_ε, χ_k] = -2ε s χ_k'(s)`,
`∂_η b' = χ_k ∂_η b`.  The weak closeness takes `G = χ_k Qb - Qb` (`‖√s G‖ → 0`) and
`H = D_k b` (`‖H‖_{H_r} ≤ 2ε (M/k) ‖b‖_{H_r} → 0`, no `√s`).  Leaves:
* `DivSCutWeak` (`T09/2/1/1`): weak Leibniz rule for the cut;
* `DivSCutInHr` (`T09/2/1/2`): the cut pieces stay in `H_r` (resp. `√s`-weighted `H_r`);
* `DivSCutConv` (`T09/2/1/3`): the four cut errors tend to `0`.

Proved here: `divSCutApproxW_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## The retired statements (kept for the refutations) -/

/-- **Old Lemma A** (old `T09/2/1/1`): the graph class forces `√s b ∈ H_r`.  FALSE for every
`r > 2` (`Sub/T09_2_1/Counter.lean`). -/
def DivSqrtSb : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    InHr c r (sqrtS b)

/-- **Old Lemma B** (old `T09/2/1/2`): the strong `s`-cutoff approximation under the extra
hypothesis `√s b ∈ H_r`.  True, but retired: the corrected route (`DivSCutApproxW`) does not need
it, and the hypothesis fails for the actual responses (SP 1912-1918 controls only `√s b_r`
through the hoop term of `∇(N_v b)`). -/
def DivSCutApproxSqrt : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    InHr c r (sqrtS b) →
    ∀ δ : ℝ, 0 < δ → ∃ b' Qb' Eb' : CProf, DivDataS c r ε b' Qb' Eb' ∧
      DivClose c r b Qb Eb b' Qb' Eb' δ

/-! ## The cut triple -/

/-- `χ_k(s) f`, `χ_k = DriftSCutHelp.sBump k = bump(log s / k)` (zero for `s ≤ 0`). -/
def sCutB (k : ℝ) (f : CProf) : CProf := fun x => ((DriftSCutHelp.sBump k x.1 : ℝ) : ℂ) • f x

/-- The cutoff commutator `[Q_ε, χ_k] f = -2ε (s χ_k'(s)) f` (`Q_ε = ∂_q - ε(2S + η∂_η + 1)`). -/
def sCutD (ε k : ℝ) (f : CProf) : CProf :=
  fun x => ((-2 * ε * (x.1 * deriv (DriftSCutHelp.sBump k) x.1) : ℝ) : ℂ) • f x

/-- `Q_ε(χ_k b) = χ_k Q_ε b - 2ε (S χ_k) b`. -/
def sCutQ (ε k : ℝ) (b Qb : CProf) : CProf := fun x => sCutB k Qb x + sCutD ε k b x

/-! ## Leaves -/

/-- **Leaf `T09/2/1/1`** (weak Leibniz rule for the `s`-cut; SP 1912-1918).  Proof:
`DivEtaCutHelp.hasWeakVec_cut` (`Tasks/GradLapNvC/DivApprox/EtaCut.lean`) with
`χ = fun y : Coord => DriftSCutHelp.sBump k y.1` (smooth: `DriftSCutHelp.sBump_smooth`, bounded
by `1`), using `cutD (vQ ε) χ x = -2 * ε * (x.1 * deriv (sBump k) x.1)` (only the `s`-coefficient
`-2ε s` of `vQ ε` meets `∂_s χ`; `DriftSCutHelp.sCut_fderiv`, `cdir`) and `cutD vEta χ = 0`. -/
def DivSCutWeak : Prop :=
  ∀ (c r ε k : ℝ) (b Qb Eb : CProf), 0 < c → 1 < r → 0 < k → InHr c r b →
    HasWeakVec (vQ ε) (dQ ε) b Qb → HasWeakVec vEta dZero b Eb →
    HasWeakVec (vQ ε) (dQ ε) (sCutB k b) (sCutQ ε k b Qb) ∧
      HasWeakVec vEta dZero (sCutB k b) (sCutB k Eb)

/-- **Leaf `T09/2/1/2`** (SP 1912-1918): the pieces of the cut triple stay in their spaces.
Proof: `DriftSCutHelp.inHr_smul_bdd` with the bounded continuous multipliers `sBump k s`
(`≤ 1`), `-2ε s χ_k'(s)` (`≤ 2ε M/k`, `DriftSCutHelp.sBump_deriv_bound_exists`) and
`√s · (-2ε s χ_k'(s))` (`χ_k' = 0` for `s > e^{2k}` by `sBump_deriv_zero_of_gt`, so it is
`≤ 2ε e^k M/k`); `sqrtS (sCutB k f) = sCutB k (sqrtS f)` pointwise. -/
def DivSCutInHr : Prop :=
  ∀ (c r ε k : ℝ) (b Qb Eb : CProf), 0 < c → 1 < r → 0 < k → DivData c r ε b Qb Eb →
    InHr c r (sCutB k b) ∧ InHr c r (sqrtS (sCutB k Qb)) ∧ InHr c r (sqrtS (sCutB k Eb)) ∧
      InHr c r (sCutD ε k b) ∧ InHr c r (sqrtS (sCutD ε k b))

/-- **Leaf `T09/2/1/3`** (SP 1912-1918): the cut errors tend to `0` in `H_r`.  Proof:
`DriftSCutHelp.tendsto_sCut_sub` for `b`, for `sqrtS Qb` and for `sqrtS Eb` (rewrite
`sqrtS (sCutB k f - f) = sCutB k (sqrtS f) - sqrtS f` pointwise), and
`DriftSCutHelp.tendsto_dterm` (with `sBump_deriv_bound_exists`) times the constant `-2ε`. -/
def DivSCutConv : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 1 < r → DivData c r ε b Qb Eb →
    Tendsto (fun n : ℕ => hNorm c r (fun x => sCutB ((n : ℝ) + 1) b x - b x)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => hNorm c r (sqrtS fun x => sCutB ((n : ℝ) + 1) Qb x - Qb x))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => hNorm c r (sCutD ε ((n : ℝ) + 1) b)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => hNorm c r (sqrtS fun x => sCutB ((n : ℝ) + 1) Eb x - Eb x))
      atTop (𝓝 0)

/-! ## Assembly -/

open DriftSCutHelp in
/-- **Corrected stage 1** from the three leaves. -/
theorem divSCutApproxW_of (h1 : DivSCutWeak) (h2 : DivSCutInHr) (h3 : DivSCutConv) :
    DivSCutApproxW := by
  intro c r ε b Qb Eb hc hε hr hd δ hδ
  have hr1 : 1 < r := by linarith
  obtain ⟨t1, t2, t3, t4⟩ := h3 c r ε b Qb Eb hc hr1 hd
  have t23 := t2.add t3
  rw [add_zero] at t23
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have ev : ∀ᶠ n : ℕ in atTop,
      hNorm c r (fun x => sCutB ((n : ℝ) + 1) b x - b x) < ENNReal.ofReal δ ∧
      (hNorm c r (sqrtS fun x => sCutB ((n : ℝ) + 1) Qb x - Qb x) +
        hNorm c r (sCutD ε ((n : ℝ) + 1) b) < ENNReal.ofReal δ ∧
      hNorm c r (sqrtS fun x => sCutB ((n : ℝ) + 1) Eb x - Eb x) < ENNReal.ofReal δ) :=
    ((tendsto_order.1 t1).2 _ hδ').and
      (((tendsto_order.1 t23).2 _ hδ').and ((tendsto_order.1 t4).2 _ hδ'))
  obtain ⟨n, hn1, hn2, hn3⟩ := ev.exists
  have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨hwQ, hwE⟩ := h1 c r ε ((n : ℝ) + 1) b Qb Eb hc hr1 hk hd.inHr hd.weakQ hd.weakE
  obtain ⟨hib, hiQ, hiE, hiD, hiDs⟩ := h2 c r ε ((n : ℝ) + 1) b Qb Eb hc hr1 hk hd
  have eQ : sqrtS (sCutQ ε ((n : ℝ) + 1) b Qb) =
      fun x => sqrtS (sCutB ((n : ℝ) + 1) Qb) x + sqrtS (sCutD ε ((n : ℝ) + 1) b) x := by
    funext x; simp only [sqrtS, sCutQ, smul_add]
  have hiQ' : InHr c r (sqrtS (sCutQ ε ((n : ℝ) + 1) b Qb)) := by
    rw [eQ]; exact inHr_add_w hr1 hiQ hiDs
  refine ⟨sCutB ((n : ℝ) + 1) b, sCutQ ε ((n : ℝ) + 1) b Qb, sCutB ((n : ℝ) + 1) Eb,
    ⟨⟨hib, hwQ, hwE, hiQ', hiE⟩, Real.exp (-2 * ((n : ℝ) + 1)), Real.exp (2 * ((n : ℝ) + 1)),
      Real.exp_pos _, ?_, ?_, ?_⟩, hn1,
    ⟨fun x => sCutB ((n : ℝ) + 1) Qb x - Qb x, sCutD ε ((n : ℝ) + 1) b,
      inHr_sqrtS_sub hr1 hiQ hd.inQ, hiD, fun x => ?_, hn2⟩, hn3⟩
  · intro x hx
    rcases hx with h | h
    · simp [sCutB, sBump_zero_of_lt hk h]
    · simp [sCutB, sBump_zero_of_gt hk h]
  · intro x hx
    rcases hx with h | h
    · simp [sCutQ, sCutB, sCutD, sBump_zero_of_lt hk h, sBump_deriv_zero_of_lt hk h]
    · simp [sCutQ, sCutB, sCutD, sBump_zero_of_gt hk h, sBump_deriv_zero_of_gt hk h]
  · intro x hx
    rcases hx with h | h
    · simp [sCutB, sBump_zero_of_lt hk h]
    · simp [sCutB, sBump_zero_of_gt hk h]
  · simp only [sCutQ]
    abel

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSCutApproxW_of
