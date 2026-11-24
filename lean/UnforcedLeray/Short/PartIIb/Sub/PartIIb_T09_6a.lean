import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_6_1

/-!
# Part II-b, task `PartII-b:T09/6a` (`LapAwayAxis`): the Laplacian identity away from the axis

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`A_ε`, `Q_ε = ∂_q - ε(K+1)`; "the domains of `A_ε` and its adjoint are the exact Cartesian domains
under these lifts") and 1902-1921 (`H_r`, the graph class, `∂_ρ(√s b) = s Q_ε b`,
`∂_z(√s b) = s ∂_η b`).

A phase test `Φ` vanishing in the tube `ϱ < δ` has its chart image in a compact window
`s ∈ [R²/Rad², R²/δ²]` (`OffAxisWindow`).  Multiply the graph data by the fixed cutoff
`χ = sBump k (s)` with `χ = 1` for `|log s| ≤ k` (`Sub/PartIIb_T09_6_1.lean`): for every fixed `k`
the cut data are graph data in a compact `s`-window (`LapCutWeak`, `LapCutInHr`, `LapCutSupport`),
and they coincide with the data where `|log s| < k` (`CutLocal`).  Inside the window nice profiles
are dense in the Laplacian graph (`LapEtaCutApprox`, `LapMollApprox`), so `LapSmooth` and the
continuity of the pairing (`DriftPairCont`) give the identity for the cut data and every phase test
(`lapWindow_of`); locality gives it for the original data against `Φ`.

The two geometric leaves `OffAxisWindow`, `CutLocal` are proved here (`offAxisWindow_proof`,
`cutLocal_proof`), as are `lapWindow_of`, `lapAwayAxis_of` and the locality helpers; the remaining
inputs are accepted leaves and `LapSmooth` (`T09/5`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- **Leaf `T09/6a/1`** (geometry of off-axis tests; SP 1639-1643: `s = R²/ρ²`).  For `R > 0` and
an off-axis phase test `Φ` there is `k > 0` such that `Φ` vanishes near every point `(τ, y)` with
`y` on the axis or `|log s| ≥ k` (`s = Axi.age R y = R²/ϱ²`).  Proof: let `Rad₀` be the
bounded-support radius of `Φ` (`IsPhaseTest.bounded_support`), `Rad = max Rad₀ δ`, and
`k = |log(R²/δ²)| + |log(R²/Rad²)| + 1`.  If `δ ≤ ϱ(y) ≤ Rad` then
`R²/Rad² ≤ s ≤ R²/δ²`, so `|log s| < k`; hence `ϱ(y) < δ` (then `Φ = 0` on the open set
`{ϱ < δ}`) or `ϱ(y) > Rad ≥ Rad₀` (then `‖y‖ ≥ ϱ(y)` and `Φ = 0` on the open set
`{Rad₀ < ‖y‖}`). -/
def OffAxisWindow : Prop :=
  ∀ (R P δ : ℝ) (Φ : ℝ × Space → CVec3), 0 < R → OffAxisTest P δ Φ →
    ∃ k : ℝ, 0 < k ∧ ∀ (τ : ℝ) (y : Space), (y ∈ Axi.axis ∨ k ≤ |Real.log (Axi.age R y)|) →
      ∀ᶠ p in 𝓝 ((τ, y) : ℝ × Space), Φ p = 0

/-- **Leaf `T09/6a/2`** (the cut data are the data where the cutoff is `1`; SP 1651-1653).  On the
open set `{s > 0, |log s| < k}` one has `sBump k = 1` (`DriftSCutHelp.sBump_one`), so
`deriv (sBump k) = 0` there and `cutE1 k = 0`; the function `s ↦ s · deriv (sBump k) s`
vanishes on that open set, so its derivative vanishes and `cutE2 k = 0`.  Then all five cut
profiles reduce to the original ones (unfold `cutB`, `cutQ`, `cutEb`, `cutQ2`, `cutE2b`). -/
def CutLocal : Prop :=
  ∀ (k ε : ℝ) (b Qb Eb Q2b E2b : CProf) (x : Coord), 0 < k → 0 < x.1 → |Real.log x.1| < k →
    cutB k b x = b x ∧ cutQ k ε b Qb x = Qb x ∧ cutEb k Eb x = Eb x ∧
      cutQ2 k ε b Qb Q2b x = Q2b x ∧ cutE2b k E2b x = E2b x

/-! ## Proofs of the two geometric leaves -/

theorem rho_le_norm (y : Space) : Axi.ϱ y ≤ ‖y‖ := by
  have h : y 0 ^ 2 + y 1 ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith [sq_nonneg (y 2)]
  calc Axi.ϱ y = √(y 0 ^ 2 + y 1 ^ 2) := rfl
    _ ≤ √(‖y‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖y‖ := Real.sqrt_sq (norm_nonneg y)

theorem offAxisWindow_proof : OffAxisWindow := by
  intro R P δ Φ hR ⟨hΦ, hδ, hz⟩
  obtain ⟨R0, hR0⟩ := hΦ.bounded_support
  have hRad : 0 < max R0 δ := lt_of_lt_of_le hδ (le_max_right _ _)
  refine ⟨|Real.log (R ^ 2 / δ ^ 2)| + |Real.log (R ^ 2 / (max R0 δ) ^ 2)| + 1, by positivity, ?_⟩
  intro τ y hy
  have hU1 : IsOpen {p : ℝ × Space | Axi.ϱ p.2 < δ} :=
    isOpen_lt (Axi.continuous_ϱ.comp continuous_snd) continuous_const
  have hU2 : IsOpen {p : ℝ × Space | R0 < ‖p.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  by_cases h1 : Axi.ϱ y < δ
  · exact Filter.eventually_of_mem (hU1.mem_nhds h1) fun p hp => hz p.1 p.2 hp
  · by_cases h2 : R0 < ‖y‖
    · exact Filter.eventually_of_mem (hU2.mem_nhds h2) fun p hp => hR0 p.1 p.2 hp
    · exfalso
      push Not at h1 h2
      have hρpos : 0 < Axi.ϱ y := lt_of_lt_of_le hδ h1
      have hρle : Axi.ϱ y ≤ max R0 δ := ((rho_le_norm y).trans h2).trans (le_max_left _ _)
      rcases hy with hy | hy
      · have h0 : Axi.ϱ y = 0 := by
          have hy' : y 0 = 0 ∧ y 1 = 0 := hy
          simp [Axi.ϱ, hy'.1, hy'.2]
        linarith
      · have hA1 : R ^ 2 / (max R0 δ) ^ 2 ≤ Axi.age R y :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hρpos.le hρle 2)
        have hA2 : Axi.age R y ≤ R ^ 2 / δ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hδ.le h1 2)
        have hApos : 0 < R ^ 2 / (max R0 δ) ^ 2 := by positivity
        have hl1 := Real.log_le_log hApos hA1
        have hl2 := Real.log_le_log (lt_of_lt_of_le hApos hA1) hA2
        have hb : |Real.log (Axi.age R y)| ≤
            |Real.log (R ^ 2 / δ ^ 2)| + |Real.log (R ^ 2 / (max R0 δ) ^ 2)| := by
          rw [abs_le]
          constructor
          · linarith [neg_abs_le (Real.log (R ^ 2 / (max R0 δ) ^ 2)),
              abs_nonneg (Real.log (R ^ 2 / δ ^ 2))]
          · linarith [le_abs_self (Real.log (R ^ 2 / δ ^ 2)),
              abs_nonneg (Real.log (R ^ 2 / (max R0 δ) ^ 2))]
        linarith

theorem cutLocal_proof : CutLocal := by
  intro k ε b Qb Eb Q2b E2b x hk hx hlog
  have hI : x.1 ∈ Ioo (Real.exp (-k)) (Real.exp k) := by
    rw [abs_lt] at hlog
    exact ⟨(Real.lt_log_iff_exp_lt hx).1 hlog.1, (Real.log_lt_iff_lt_exp hx).1 hlog.2⟩
  have hone : ∀ s ∈ Ioo (Real.exp (-k)) (Real.exp k), DriftSCutHelp.sBump k s = 1 := by
    intro s hs
    have hs0 : 0 < s := lt_trans (Real.exp_pos _) hs.1
    refine DriftSCutHelp.sBump_one hk hs0 ?_
    have l1 := Real.log_lt_log (Real.exp_pos _) hs.1
    have l2 := Real.log_lt_log hs0 hs.2
    rw [Real.log_exp] at l1 l2
    rw [abs_le]
    constructor <;> linarith
  have hd0 : ∀ s ∈ Ioo (Real.exp (-k)) (Real.exp k), deriv (DriftSCutHelp.sBump k) s = 0 := by
    intro s hs
    have hev : DriftSCutHelp.sBump k =ᶠ[𝓝 s] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) hone
    rw [hev.deriv_eq, deriv_const]
  have hE1 : cutE1 k x = 0 := by simp [cutE1, hd0 _ hI]
  have hE2 : cutE2 k x = 0 := by
    have hev : (fun s => s * deriv (DriftSCutHelp.sBump k) s) =ᶠ[𝓝 x.1] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hI) fun s hs => by simp [hd0 s hs]
    simp [cutE2, hev.deriv_eq]
  have h1 := hone _ hI
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [cutB, cutQ, cutEb, cutQ2, cutE2b, h1, hE1, hE2]

/-! ## Locality helpers -/

/-- The pairing only sees the field where the test does not vanish. -/
theorem pairF_congr_pt {P : ℝ} {Φ u u' : ℝ × Space → CVec3}
    (h : ∀ p, Φ p = 0 ∨ u p = u' p) : pairF P Φ u = pairF P Φ u' := by
  have e : (fun x => dotL (Φ x) (u x)) = fun x => dotL (Φ x) (u' x) := by
    funext p
    rcases h p with h | h
    · simp [h]
    · rw [h]
  unfold pairF
  rw [e]

/-- The lift at `(τ, y)` only sees the profile at the chart point. -/
theorem NvC_congr_chart {R τ : ℝ} {y : Space} {b b' : CProf}
    (h : b (Axi.chart R τ y) = b' (Axi.chart R τ y)) : NvC R b (τ, y) = NvC R b' (τ, y) := by
  simp only [NvC, Axi.Nv, h]

/-- Either the window condition of `OffAxisWindow` holds at `y`, or the chart point lies in
`{s > 0, |log s| < k}`. -/
theorem window_or {R : ℝ} (hR : 0 < R) (k τ : ℝ) (y : Space) :
    (y ∈ Axi.axis ∨ k ≤ |Real.log (Axi.age R y)|) ∨
      (0 < (Axi.chart R τ y).1 ∧ |Real.log (Axi.chart R τ y).1| < k) := by
  by_cases hy : y ∈ Axi.axis
  · exact Or.inl (Or.inl hy)
  · by_cases hk : k ≤ |Real.log (Axi.age R y)|
    · exact Or.inl (Or.inr hk)
    · exact Or.inr ⟨Axi.age_pos hR.ne' hy, not_le.1 hk⟩

theorem dy_eventually_zero {Φ : ℝ × Space → CVec3} {p : ℝ × Space}
    (h : ∀ᶠ q in 𝓝 p, Φ q = 0) (j : Fin 3) : ∀ᶠ q in 𝓝 p, dy j Φ q = 0 := by
  have h' : Φ =ᶠ[𝓝 p] fun _ => (0 : CVec3) := h
  filter_upwards [h'.eventuallyEq_nhds] with q hq
  simp [dy, hq.fderiv_eq]

theorem lapT_eq_zero_of_eventually {Φ : ℝ × Space → CVec3} {p : ℝ × Space}
    (h : ∀ᶠ q in 𝓝 p, Φ q = 0) : lapT Φ p = 0 := by
  unfold lapT
  refine Finset.sum_eq_zero fun j _ => ?_
  exact (dy_eventually_zero (dy_eventually_zero h j) j).self_of_nhds

theorem nuLapT_eq_zero_of_eventually (ν : ℝ) {Φ : ℝ × Space → CVec3} {p : ℝ × Space}
    (h : ∀ᶠ q in 𝓝 p, Φ q = 0) : nuLapT ν Φ p = 0 := by
  simp [nuLapT, lapT_eq_zero_of_eventually h]

/-! ## The identity for window data -/

/-- For graph data in a compact `s`-window the Laplacian identity holds against every phase test:
nice approximants in the Laplacian graph norm (`LapEtaCutApprox`, then `LapMollApprox`),
`LapSmooth` for each, and `DriftPairCont` on both sides. -/
theorem lapWindow_of (hS : LapSmooth) (hP : DriftPairCont) (hE : LapEtaCutApprox)
    (hM : LapMollApprox) {c ε r ν : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r)
    {b Qb Eb Q2b E2b : CProf} (hd : LapDataS c r ε ν b Qb Eb Q2b E2b) :
    HasPtwOp (2 * ε * c) (nuLapT ν) (NvC ε⁻¹ b) (NvC ε⁻¹ (lapProf ν ε b Q2b E2b)) := by
  have hr1 : 1 < r := by linarith
  have key : ∀ n : ℕ, ∃ b' Qb' Eb' Q2b' E2b' : CProf, NiceProf c b' ∧
      LapData c r ε ν b' Qb' Eb' Q2b' E2b' ∧
      LapClose c r ε ν b Q2b E2b b' Q2b' E2b' (1 / ((n : ℝ) + 1)) := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 2 := by positivity
    obtain ⟨b1, Q1, E1, Q21, E21, hp1, hc1⟩ := hE c r ε ν b Qb Eb Q2b E2b hc hε hr hd _ hδ
    obtain ⟨b2, Q2, E2, Q22, E22, hn2, hp2, hc2⟩ :=
      hM c r ε ν b1 Q1 E1 Q21 E21 hc hε hr hp1 _ hδ
    refine ⟨b2, Q2, E2, Q22, E22, hn2, hp2, ?_⟩
    have h12 := driftClose_trans (δ₁ := 1 / ((n : ℝ) + 1) / 2) (δ₂ := 1 / ((n : ℝ) + 1) / 2)
      hr1 hδ.le hδ.le hd.1.div.inHr hd.1.inLap hp1.1.1.div.inHr hp1.1.1.inLap hp2.div.inHr
      hp2.inLap hc1 hc2
    rw [add_halves] at h12
    exact h12
  choose bn Qbn Ebn Q2bn E2bn hn hp hcl using key
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have t1 : Tendsto (fun n => hNorm c r (fun x => bn n x - b x)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le)
      (fun n => (hcl n).1.le)
  have t2 : Tendsto (fun n => hNorm c r (fun x => lapProf ν ε (bn n) (Q2bn n) (E2bn n) x -
      lapProf ν ε b Q2b E2b x)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le)
      (fun n => (hcl n).2.le)
  intro Φ hΦ
  have e : ∀ n, pairF (2 * ε * c) (nuLapT ν Φ) (NvC ε⁻¹ (bn n)) =
      pairF (2 * ε * c) Φ (NvC ε⁻¹ (lapProf ν ε (bn n) (Q2bn n) (E2bn n))) := fun n =>
    hS c ε ν (bn n) (Qbn n) (Ebn n) (Q2bn n) (E2bn n) hc hε (hn n) (hp n).div.weakQ
      (hp n).div.weakE (hp n).weakQ2 (hp n).weakE2 Φ hΦ
  have hΦ' : IsPhaseTest (2 * ε * c) (nuLapT ν Φ) := hΦ.lapT.const_smul ν
  have l1 := hP c r ε (nuLapT ν Φ) hc hε hr1 hΦ' b bn hd.1.div.inHr
    (fun n => (hp n).div.inHr) t1
  have l2 := hP c r ε Φ hc hε hr1 hΦ (lapProf ν ε b Q2b E2b)
    (fun n => lapProf ν ε (bn n) (Q2bn n) (E2bn n)) hd.1.inLap (fun n => (hp n).inLap) t2
  simp only [e] at l1
  exact tendsto_nhds_unique l1 l2

/-- The fixed cut of graph data is window data. -/
theorem lapCut_dataS (hW : LapCutWeak) (hI : LapCutInHr) (hSup : LapCutSupport)
    {c r ε ν k : ℝ} (hk : 0 < k) (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r)
    {b Qb Eb Q2b E2b : CProf} (hd : LapData c r ε ν b Qb Eb Q2b E2b) :
    LapDataS c r ε ν (cutB k b) (cutQ k ε b Qb) (cutEb k Eb) (cutQ2 k ε b Qb Q2b)
      (cutE2b k E2b) := by
  obtain ⟨w1, w2, w3, w4⟩ := hW c r ε ν k b Qb Eb Q2b E2b hk hc hε hr hd
  obtain ⟨i1, i2, i3, i4⟩ := hI c r ε ν k b Qb Eb Q2b E2b hk hc hε hr hd
  obtain ⟨s1, s2, s3, s4, s5⟩ := hSup k ε b Qb Eb Q2b E2b hk
  exact ⟨⟨⟨i1, w1, w2, i2, i3⟩, w3, w4, i4⟩, _, _, Real.exp_pos _, s1, s2, s3, s4, s5⟩

/-- **`LapAwayAxis` from the leaves.** -/
theorem lapAwayAxis_of (hS : LapSmooth) (hP : DriftPairCont) (hE : LapEtaCutApprox)
    (hM : LapMollApprox) (hW : LapCutWeak) (hI : LapCutInHr) (hSup : LapCutSupport)
    (hWin : OffAxisWindow) (hLoc : CutLocal) : LapAwayAxis := by
  intro c ε r ν b Qb Eb Q2b E2b hc hε hr hd δ Φ hΦ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨k, hk, hkw⟩ := hWin ε⁻¹ (2 * ε * c) δ Φ hR hΦ
  have key := lapWindow_of hS hP hE hM hc hε hr (lapCut_dataS hW hI hSup hk hc hε hr hd) Φ hΦ.1
  have hL : pairF (2 * ε * c) (nuLapT ν Φ) (NvC ε⁻¹ (cutB k b)) =
      pairF (2 * ε * c) (nuLapT ν Φ) (NvC ε⁻¹ b) := by
    apply pairF_congr_pt
    rintro ⟨τ, y⟩
    rcases window_or hR k τ y with h | ⟨h0, hlog⟩
    · exact Or.inl (nuLapT_eq_zero_of_eventually ν (hkw τ y h))
    · exact Or.inr (NvC_congr_chart (hLoc k ε b Qb Eb Q2b E2b _ hk h0 hlog).1)
  have hRt : pairF (2 * ε * c) Φ
      (NvC ε⁻¹ (lapProf ν ε (cutB k b) (cutQ2 k ε b Qb Q2b) (cutE2b k E2b))) =
      pairF (2 * ε * c) Φ (NvC ε⁻¹ (lapProf ν ε b Q2b E2b)) := by
    apply pairF_congr_pt
    rintro ⟨τ, y⟩
    rcases window_or hR k τ y with h | ⟨h0, hlog⟩
    · exact Or.inl (hkw τ y h).self_of_nhds
    · refine Or.inr (NvC_congr_chart ?_)
      obtain ⟨e1, -, -, e4, e5⟩ := hLoc k ε b Qb Eb Q2b E2b _ hk h0 hlog
      simp only [lapProf, e1, e4, e5]
  rw [← hL, ← hRt]
  exact key

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.offAxisWindow_proof
#print axioms UnforcedLeray.Short.IIb.cutLocal_proof
#print axioms UnforcedLeray.Short.IIb.lapAwayAxis_of
