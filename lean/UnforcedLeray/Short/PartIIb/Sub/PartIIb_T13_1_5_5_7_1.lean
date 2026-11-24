import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7

/-!
# `PartII-b:T13/1/5/5/7/1` decomposition: density of nice periodic functions (`MollDensity`)

Source: `the November 2 reference manuscript`
lines 1932-1935 (standard approximation).  Steps: truncate to a `(s, η)`-box, approximate the
cell restriction by a continuous function supported in a fixed window, periodize, estimate.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The cell strip `ℝ × (cell c)` (`q ∈ [-c/2, c/2)`, `s, η` free) in `Coord`. -/
def moStrip (c : ℝ) : Set Coord := (univ : Set ℝ) ×ˢ UnforcedLeray.Cyl.cell c

/-- The box `[-M,M] × (ℝ × [-M,M])` in `Coord` (same set as `niceBox` in the leaves). -/
def moBox (K : ℝ) : Set Coord := Icc (-K) K ×ˢ (univ ×ˢ Icc (-K) K)

theorem mem_moBox (K : ℝ) (x : Coord) : x ∈ moBox K ↔ |x.1| ≤ K ∧ |x.2.2| ≤ K := by
  simp only [moBox, mem_prod, mem_univ, true_and, mem_Icc, abs_le]

theorem measurableSet_moBox (K : ℝ) : MeasurableSet (moBox K) :=
  measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)

/-- The window `[-M-1, M+1] × ([-c, c] × [-M-1, M+1])` in `Coord = (s, (q, η))`. -/
def moWin (c M : ℝ) : Set Coord := Icc (-M - 1) (M + 1) ×ˢ (Icc (-c) c ×ˢ Icc (-M - 1) (M + 1))

/-- Periodization in `q`: `(perz c h)(s,q,η) = ∑_{k∈ℤ} h(s, q + k c, η)`. -/
def moPerz (c : ℝ) (h : Coord → ℂ) (x : Coord) : ℂ :=
  ∑ᶠ k : ℤ, h (x.1, (x.2.1 + k * c, x.2.2))

/-- Step 1 (truncation to a box, dominated convergence): the tail of `f` outside
`moBox M` is small in `L^r(cylMeas c)` for `M` large. -/
def MollTrunc : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (f : Coord → ℂ), AEStronglyMeasurable f volume →
    eLpNorm f (ENNReal.ofReal r) (cylMeas c) < ⊤ → ∀ δ : ℝ≥0∞, 0 < δ →
    ∃ M : ℝ, eLpNorm (fun x => f x - (moBox M).indicator f x) (ENNReal.ofReal r) (cylMeas c) < δ

/-- Step 2 (restriction to the cell strip is in `L^r(volume)`): finite `L^r(cylMeas c)` norm of
`f` gives `strip.indicator f ∈ L^r(volume)` (`cylMeas c = c⁻¹ • volume.restrict strip`). -/
def MollStripMemLp : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (f : Coord → ℂ), AEStronglyMeasurable f volume →
    eLpNorm f (ENNReal.ofReal r) (cylMeas c) < ⊤ →
    MemLp ((moStrip c).indicator f) (ENNReal.ofReal r) volume

/-- Step 3 (compact-support approximation inside a fixed window): an `L^r(volume)` function `F`
vanishing outside `moBox M ∩ strip` is approximated by a continuous `h` vanishing outside
`moWin c M` (Mathlib `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, then multiply by a
continuous `[0,1]` cutoff equal to `1` on the compact set `Icc(-M,M) × Icc(-c/2,c/2) × Icc(-M,M)`
and supported in `moWin c M`). -/
def MollWinApprox : Prop :=
  ∀ (c r M : ℝ), 0 < c → 1 < r → ∀ F : Coord → ℂ, MemLp F (ENNReal.ofReal r) volume →
    (∀ x, x ∉ moBox M ∩ moStrip c → F x = 0) → ∀ δ : ℝ≥0∞, 0 < δ →
    ∃ h : Coord → ℂ, Continuous h ∧ (∀ x, x ∉ moWin c M → h x = 0) ∧
      eLpNorm (fun x => F x - h x) (ENNReal.ofReal r) volume < δ

/-- Step 4 (periodization of a window function): `moPerz c h` is continuous (locally finite
sum), exactly `q`-periodic (reindex `k ↦ k+1`), bounded (at most `3` nonzero terms), and
vanishes for `|s|` or `|η|` larger than `M+1`. -/
def MollPerzProps : Prop :=
  ∀ (c M : ℝ), 0 < c → ∀ h : Coord → ℂ, Continuous h → (∀ x, x ∉ moWin c M → h x = 0) →
    Continuous (moPerz c h) ∧ (∀ x, moPerz c h (qShift c x) = moPerz c h x) ∧
    (∃ B : ℝ, ∀ x, ‖moPerz c h x‖ ≤ B) ∧
    (∀ x : Coord, M + 1 < |x.1| ∨ M + 1 < |x.2.2| → moPerz c h x = 0)

/-- Step 5 (periodization estimate; at most `3` translates meet the window, and
`f₁ = ∑_k F(·+kc)` a.e. for `F = strip.indicator f₁`, so on the strip
`f₁ - moPerz h = ∑_k (h - F)(·+kc)`; Hölder with `3` terms and
`cylMeas c = c⁻¹ • volume.restrict strip`): there is a finite constant `K` depending only on
`c, r` with `‖f₁ - moPerz c h‖_{L^r(cylMeas c)} ≤ K ‖F - h‖_{L^r(volume)}`. -/
def MollPerzEst : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ (M : ℝ) (f1 : Coord → ℂ), AEStronglyMeasurable f1 volume → QPeriodicS c f1 →
    ∀ h : Coord → ℂ, Continuous h → (∀ x, x ∉ moWin c M → h x = 0) →
    eLpNorm (fun x => f1 x - moPerz c h x) (ENNReal.ofReal r) (cylMeas c) ≤
      K * eLpNorm (fun x => (moStrip c).indicator f1 x - h x) (ENNReal.ofReal r) volume

theorem mollApprox_density_proof_of (h1 : MollTrunc) (h2 : MollStripMemLp)
    (h3 : MollWinApprox) (h4 : MollPerzProps) (h5 : MollPerzEst) : MollDensity := by
  intro c r hc hr f hper hmeas hfin δ hδ
  obtain ⟨K, hK, hKest⟩ := h5 c r hc hr
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨M, hM⟩ := h1 c r hc hr f hmeas hfin (δ / 2) hδ2
  set f1 : Coord → ℂ := (moBox M).indicator f with hf1
  have hf1meas : AEStronglyMeasurable f1 volume :=
    hmeas.indicator (measurableSet_moBox M)
  have hf1per : QPeriodicS c f1 := by
    filter_upwards [hper] with x hx
    have : qShift c x ∈ moBox M ↔ x ∈ moBox M := by
      simp only [mem_moBox, qShift]
    by_cases hx' : x ∈ moBox M
    · rw [hf1, indicator_of_mem hx', indicator_of_mem (this.2 hx'), hx]
    · rw [hf1, indicator_of_notMem hx', indicator_of_notMem (fun h => hx' (this.1 h))]
  have hf1fin : eLpNorm f1 (ENNReal.ofReal r) (cylMeas c) < ⊤ :=
    lt_of_le_of_lt (eLpNorm_indicator_le _) hfin
  have hF := h2 c r hc hr f1 hf1meas hf1fin
  have hFz : ∀ x, x ∉ moBox M ∩ moStrip c → (moStrip c).indicator f1 x = 0 := by
    intro x hx
    by_cases hs : x ∈ moStrip c
    · have : x ∉ moBox M := fun h => hx ⟨h, hs⟩
      simp [hf1, indicator_of_mem hs, indicator_of_notMem this]
    · exact indicator_of_notMem hs _
  obtain ⟨δ', hδ', hKδ⟩ := ENNReal.exists_pos_mul_lt hK hδ2.ne'
  obtain ⟨h, hcont, hsupp, hFh⟩ := h3 c r M hc hr _ hF hFz _ hδ'
  obtain ⟨hgc, hgp, hgb, hgv⟩ := h4 c M hc h hcont hsupp
  refine ⟨moPerz c h, hgc, hgp, hgb, ⟨M + 1, hgv⟩, ?_⟩
  have hgmeas : AEStronglyMeasurable (moPerz c h) volume := hgc.aestronglyMeasurable
  have hsplit : (fun x => f x - moPerz c h x) =
      (fun x => (f x - f1 x)) + (fun x => f1 x - moPerz c h x) := by
    ext x; simp
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r :=
    ENNReal.one_le_ofReal.2 hr.le
  have hA : AEStronglyMeasurable (fun x => f x - f1 x) (cylMeas c) :=
    ((hmeas.sub hf1meas)).mono_ac (mollApprox_cylMeas_ac c)
  have hB : AEStronglyMeasurable (fun x => f1 x - moPerz c h x) (cylMeas c) :=
    (hf1meas.sub hgmeas).mono_ac (mollApprox_cylMeas_ac c)
  have h6 := hKest M f1 hf1meas hf1per h hcont hsupp
  have h7 : K * eLpNorm (fun x => (moStrip c).indicator f1 x - h x) (ENNReal.ofReal r) volume
      < δ / 2 := by
    calc _ ≤ K * δ' := by gcongr
      _ < δ / 2 := by rw [mul_comm]; exact hKδ
  rw [hsplit]
  calc _ ≤ eLpNorm (fun x => f x - f1 x) (ENNReal.ofReal r) (cylMeas c) +
        eLpNorm (fun x => f1 x - moPerz c h x) (ENNReal.ofReal r) (cylMeas c) :=
        eLpNorm_add_le hA hB hp
    _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hM (lt_of_le_of_lt h6 h7)
    _ = δ := ENNReal.add_halves δ

end UnforcedLeray.Short.IIb
