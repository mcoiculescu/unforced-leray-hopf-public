import UnforcedLeray.Short.PartIIIa.Sub.T18_2
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Tri

/-!
# Part III-a, task `PartIII-a:T18/2/3`: density of nice forces (conditional)

Target (`Sub/T18_2.lean`): `NiceForceApprox`. Source of record:
`the November 2 reference manuscript`, lines 3427-3440 ("let `δ → 0`": approximate
the force by smooth forces supported away from `s = 0`).


`NeededSmoothApprox` (`T18_FreeCausal/Existence/NiceForceApprox/NeededProps.lean`). Here the target is
cut into five statements, with the wiring proved in `niceBoxApprox_of` and `niceForceApprox_of`.

* `TCalNormTriangle` (`Sub/T18_2_Tri.lean`): the triangle inequality for `‖g⁻¹·‖_𝒯`.
* `NiceTruncation`: truncation of `F` to the compact box
  `[1/(k+1), k+1] × {|q| ≤ (c/2)(k+1)/(k+2)} × {|η| ≤ k+1}` (inside the OPEN cell in `q`)
  converges in the gain-conjugated `𝒯` norm (dominated convergence).
* `NiceBoxApprox` (target of `niceBoxApprox_of`): a symmetric measurable `F` of finite `𝒯` norm
  vanishing outside such a box is approximated by nice forces. It follows from
  * `NiceWeightCompare`: on fields supported in `α ≤ s ≤ β` (on the cell) the norm
    `‖g⁻¹·‖_𝒯` is comparable with the unweighted `L²(Lebesgue)` norm (`g` is bounded above and below
    on `(0, ∞)`, the weights `s^{-1/2}` are bounded above and below on `[α, β]`);
  * `NiceSmoothDensity`: symmetric `C^∞` fields compactly supported in a slightly larger box are dense
    in unweighted `L²(ℝ³)` among such fields (mollification of the independent entries);
  * `NicePeriodize`: a `C^∞` field supported in `|q| ≤ r' < c/2` extends `c`-periodically in `q` to a
    nice force which agrees with it on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `k`-th truncation box: `s ∈ [1/(k+1), k+1]`, `|q| ≤ (c/2)(k+1)/(k+2)` (strictly inside the
cell `[-c/2, c/2)`), `|η| ≤ k+1`. -/
def niceTruncBox (c : ℝ) (k : ℕ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | 1 / ((k : ℝ) + 1) ≤ p.1 ∧ p.1 ≤ (k : ℝ) + 1 ∧
    |p.2.1| ≤ c / 2 * ((k : ℝ) + 1) / ((k : ℝ) + 2) ∧ |p.2.2| ≤ (k : ℝ) + 1}

/-- The truncation `1_{box_k} F` of a tensor field. -/
def niceTrunc (c : ℝ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (k : ℕ) :
    ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
  fun p i j => (niceTruncBox c k).indicator (fun q => F q i j) p

theorem measurableSet_niceTruncBox (c : ℝ) (k : ℕ) : MeasurableSet (niceTruncBox c k) := by
  unfold niceTruncBox
  simp only [setOf_and]
  refine (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const)))

/-- **Truncation** (`PartIII-a:T18/2/3/1`; SP 3427-3440). For `F` measurable with
`‖g⁻¹F‖_𝒯 < ∞` the truncations `1_{box_k} F` have finite `𝒯` norm and converge to `F`:
`‖g⁻¹(F - 1_{box_k} F)‖_𝒯 → 0`. Proof: `F - 1_{box_k}F = 1_{box_k^c}F`; the boxes increase and
exhaust `{s > 0, |q| < c/2}`; on `(0,∞) × cell` the complement of the union is the null set
`{q = -c/2}`, so `1_{box_k^c} → 0` `ageμ c (-1/2)`-a.e.; dominated convergence
(`tendsto_lintegral_of_dominated_convergence`, majorant `tnorm2 (g⁻¹F)^2`, integrable by
`tCalNorm c (gainConj γ ν F) < ⊤`) on `eLpNorm (·) 2 = (∫⁻ ‖·‖ₑ^2)^(1/2)`; finiteness of the norm of the
truncation is the pointwise bound `tnorm2 (g⁻¹ 1_{box}F) ≤ tnorm2 (g⁻¹F)` (`eLpNorm_mono_ae`). -/
def NiceTruncation : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ i j, Measurable fun p => F p i j) →
      tCalNorm c (gainConj γ ν F) < ⊤ →
      (∀ k : ℕ, tCalNorm c (gainConj γ ν (niceTrunc c F k)) < ⊤) ∧
      Tendsto (fun k : ℕ =>
        tCalNorm c (gainConj γ ν (fun p i j => F p i j - niceTrunc c F k p i j)))
        atTop (𝓝 0)

/-- **Comparison of the weighted `𝒯` norm with the Lebesgue norm** (`PartIII-a:T18/2/3/2`;
SP 3427-3440, "`g` and `s^{-1/2}` are bounded above and below"). For `c, ν > 0`, `α > 0` and `β`
there is `C ≥ 0` such that for every measurable tensor field `H` vanishing for `s < α` and for
`s > β` on the cell,
`‖g⁻¹H‖_𝒯 ≤ C ‖|H|‖_{L²(Ioi 0 × cell, Lebesgue)}` and
`‖|H|‖_{L²(Ioi 0 × cell, Lebesgue)} ≤ C ‖g⁻¹H‖_𝒯`. Proof: `Axi.lintegral_ageμ` writes
`‖g⁻¹H‖_𝒯² = ∫_{(0,∞)×cell} c⁻¹ s^{-1/2} g(s)^{-2} |H|²`; on `[α, β]`,
`e^{-2|γ|/ν} ≤ g^{-2} ≤ e^{2|γ|/ν}` (`ν > 0`, `0 < s/(1+νs) < 1/ν`) and `s^{-1/2}` lies between
`β^{-1/2}` and `α^{-1/2}`; `H = 0` elsewhere on the cell. -/
def NiceWeightCompare : Prop :=
  ∀ (c ν γ α β : ℝ), 0 < c → 0 < ν → 0 < α →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ i j, Measurable fun p => H p i j) →
      (∀ s x i j, x ∈ B0579.cell c → (s < α ∨ β < s) → H (s, x) i j = 0) →
      tCalNorm c (gainConj γ ν H) ≤ ENNReal.ofReal C *
        eLpNorm (fun p => tnorm2 (H p)) 2 (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) ∧
      eLpNorm (fun p => tnorm2 (H p)) 2 (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) ≤
        ENNReal.ofReal C * tCalNorm c (gainConj γ ν H)

/-- **Smooth density in unweighted `L²(ℝ³)`** (`PartIII-a:T18/2/3/3`; SP 3427-3440). A symmetric
measurable tensor field `F` with finite `L²(Lebesgue)` norm vanishing outside the box
`α ≤ s ≤ β`, `|q| ≤ r`, `|η| ≤ R` (`α > 0`, `r < r'`) is approximated in `L²(ℝ × ℝ × ℝ)` by symmetric
`C^∞` tensor fields vanishing outside the larger box `α/2 ≤ s ≤ β+1`, `|q| ≤ r'`, `|η| ≤ R+1`.
Proof: mollify the entries `F₀₀, F₀₁ = F₁₀, F₁₁` (real and imaginary parts) with a
`ContDiffBump.normed` kernel of radius `< min(α/2, r' - r, 1)`
(`ContDiffBump.convolution_tendsto_right`, or density of `C_c^∞` in `L²`), set `G₁₀ := G₀₁`. -/
def NiceSmoothDensity : Prop :=
  ∀ α β r r' R : ℝ, 0 < α → r < r' →
    ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
      (∀ i j, Measurable fun p => F p i j) →
      (∀ s x i j, (s < α ∨ β < s ∨ r < |x.1| ∨ R < |x.2|) → F (s, x) i j = 0) →
      eLpNorm (fun p => tnorm2 (F p)) 2 (volume : Measure (ℝ × (ℝ × ℝ))) < ⊤ →
      ∀ ε : ℝ, 0 < ε → ∃ G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
        (∀ p i j, G p i j = G p j i) ∧ (∀ i j, ContDiff ℝ ∞ fun p => G p i j) ∧
        (∀ s x i j, (s < α / 2 ∨ β + 1 < s ∨ r' < |x.1| ∨ R + 1 < |x.2|) → G (s, x) i j = 0) ∧
        eLpNorm (fun p => tnorm2 (fun i j => G p i j - F p i j)) 2
          (volume : Measure (ℝ × (ℝ × ℝ))) < ENNReal.ofReal ε

/-- **Periodization** (`PartIII-a:T18/2/3/4`; SP 3427-3440). Let `0 < c`, `r' < c/2` and let `G` be a
symmetric `C^∞` tensor field vanishing outside the box `α' ≤ s ≤ β'`, `|q| ≤ r'`, `|η| ≤ R'`
(`α' > 0`). Then there is a nice force `G'` (symmetric, `C^∞`, `c`-periodic in `q`, vanishing for
`s ∉ [a, B]`, `a > 0`, and `|η| > R`) with `G' = G` on `(ℝ × cell)` and `G' = 0` for `s < α'`.
Proof: `G'(s, (q, η)) = G(s, (toIcoMod hc (-c/2) q, η))` (or the locally finite sum
`∑ₙ G(s, (q - n c, η))`); near the cut `q ≡ ±c/2` both sides vanish since `|q| ≤ r' < c/2` on the
support, so `G'` is `C^∞`; all support clauses are inherited from `G`. -/
def NicePeriodize : Prop :=
  ∀ (c α' β' r' R' : ℝ), 0 < c → 0 < α' → r' < c / 2 →
    ∀ G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, G p i j = G p j i) →
      (∀ i j, ContDiff ℝ ∞ fun p => G p i j) →
      (∀ s x i j, (s < α' ∨ β' < s ∨ r' < |x.1| ∨ R' < |x.2|) → G (s, x) i j = 0) →
      ∃ G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, NiceForce c G' ∧
        (∀ s x i j, x ∈ B0579.cell c → G' (s, x) i j = G (s, x) i j) ∧
        (∀ s x i j, s < α' → G' (s, x) i j = 0)

/-- **Approximation of a boxed force by nice forces** (assembled from `NiceWeightCompare`,
`NiceSmoothDensity`, `NicePeriodize`; SP 3427-3440). -/
def NiceBoxApprox : Prop :=
  ∀ (c ν γ : ℝ), 0 < c → 0 < ν →
    ∀ α β r R : ℝ, 0 < α → r < c / 2 →
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        (∀ s x i j, (s < α ∨ β < s ∨ r < |x.1| ∨ R < |x.2|) → F (s, x) i j = 0) →
        tCalNorm c (gainConj γ ν F) < ⊤ →
        ∀ ε : ℝ, 0 < ε → ∃ G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, NiceForce c G ∧
          tCalNorm c (gainConj γ ν (fun p i j => G p i j - F p i j)) < ENNReal.ofReal ε

theorem niceBoxApprox_of (hW : NiceWeightCompare) (hS : NiceSmoothDensity)
    (hP : NicePeriodize) : NiceBoxApprox := by
  intro c ν γ hc hν α β r R hα hr F hsym hmeas hvan hfin ε hε
  obtain ⟨C, hC0, hC⟩ := hW c ν γ (α / 2) (β + 1) hc hν (half_pos hα)
  -- `F` vanishes for `s < α/2` and `s > β + 1` on the cell
  have hFcell : ∀ s x i j, x ∈ B0579.cell c → (s < α / 2 ∨ β + 1 < s) → F (s, x) i j = 0 := by
    intro s x i j _ h
    apply hvan
    rcases h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  obtain ⟨hF1, hF2⟩ := hC F hmeas hFcell
  -- `F` is in unweighted `L²(ℝ³)`
  have hFL2 : eLpNorm (fun p => tnorm2 (F p)) 2 (volume : Measure (ℝ × (ℝ × ℝ))) < ⊤ := by
    have hsupp : (Function.support fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p)) ⊆
        Ioi (0 : ℝ) ×ˢ B0579.cell c := by
      intro p hp
      by_contra hnot
      apply hp
      have hz : ∀ i j, F p i j = 0 := by
        intro i j
        have := hvan p.1 p.2 i j
        apply this
        by_cases h1 : p.1 ∈ Ioi (0 : ℝ)
        · have h2 : p.2 ∉ B0579.cell c := fun h2 => hnot ⟨h1, h2⟩
          right; right; left
          by_contra hle
          push_neg at hle
          apply h2
          simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
          have := abs_le.1 hle
          constructor <;> linarith [this.1, this.2]
        · left
          simp only [mem_Ioi, not_lt] at h1
          linarith
      show tnorm2 (F p) = 0
      unfold tnorm2
      simp [hz]
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    exact lt_of_le_of_lt hF2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  -- parameters
  have hrr' : r < (r + c / 2) / 2 := by linarith
  have hr'c : (r + c / 2) / 2 < c / 2 := by linarith
  have hε' : 0 < ε / (C + 1) := by positivity
  obtain ⟨G, hGsym, hGsm, hGvan, hGnorm⟩ := hS α β r ((r + c / 2) / 2) R hα hrr' F hsym hmeas
    hvan hFL2 (ε / (C + 1)) hε'
  obtain ⟨G', hG'nice, hG'eq, hG'van⟩ := hP c (α / 2) (β + 1) ((r + c / 2) / 2) (R + 1) hc
    (half_pos hα) hr'c G hGsym hGsm hGvan
  refine ⟨G', hG'nice, ?_⟩
  have hG'meas : ∀ i j, Measurable fun p => G' p i j :=
    fun i j => (hG'nice.2.1 i j).continuous.measurable
  have hHvan : ∀ s x i j, x ∈ B0579.cell c → (s < α / 2 ∨ β + 1 < s) →
      G' (s, x) i j - F (s, x) i j = 0 := by
    intro s x i j hx h
    rw [hG'eq s x i j hx, hFcell s x i j hx h, sub_zero]
    apply hGvan
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨hH1, -⟩ := hC (fun p i j => G' p i j - F p i j)
    (fun i j => (hG'meas i j).sub (hmeas i j)) hHvan
  -- the Lebesgue norm of `G' - F` on the region is at most that of `G - F`
  have hS0 : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hcongr : eLpNorm (fun p => tnorm2 (fun i j => G' p i j - F p i j)) 2
      (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) =
      eLpNorm (fun p => tnorm2 (fun i j => G p i j - F p i j)) 2
        (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) := by
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hS0).2 (Eventually.of_forall fun p hp => ?_)
    have : (fun i j => G' p i j - F p i j) = fun i j => G p i j - F p i j := by
      funext i j
      have := hG'eq p.1 p.2 i j hp.2
      simpa using congrArg (fun z => z - F p i j) this
    simp only [this]
  have hmono : eLpNorm (fun p => tnorm2 (fun i j => G p i j - F p i j)) 2
      (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) ≤
      eLpNorm (fun p => tnorm2 (fun i j => G p i j - F p i j)) 2
        (volume : Measure (ℝ × (ℝ × ℝ))) :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hL : eLpNorm (fun p => tnorm2 (fun i j => G' p i j - F p i j)) 2
      (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) ≤ ENNReal.ofReal (ε / (C + 1)) := by
    rw [hcongr]
    exact hmono.trans hGnorm.le
  calc tCalNorm c (gainConj γ ν (fun p i j => G' p i j - F p i j))
      ≤ ENNReal.ofReal C * eLpNorm (fun p => tnorm2 (fun i j => G' p i j - F p i j)) 2
          (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) := hH1
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ε / (C + 1)) := by gcongr
    _ = ENNReal.ofReal (C * (ε / (C + 1))) := (ENNReal.ofReal_mul hC0).symm
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith

theorem niceForceApprox_of (hTri : TCalNormTriangle) (hT : NiceTruncation)
    (hB : NiceBoxApprox) : NiceForceApprox := by
  intro c ν γ hc hν F hsym hmeas hfin
  obtain ⟨hTfin, hTlim⟩ := hT c ν γ hc hν F hmeas hfin
  have hTmeas : ∀ k i j, Measurable fun p => niceTrunc c F k p i j := fun k i j =>
    (hmeas i j).indicator (measurableSet_niceTruncBox c k)
  have hTsym : ∀ k p i j, niceTrunc c F k p i j = niceTrunc c F k p j i := by
    intro k p i j
    unfold niceTrunc
    by_cases h : p ∈ niceTruncBox c k
    · simp only [Set.indicator_of_mem h, hsym p i j]
    · simp only [Set.indicator_of_notMem h]
  have hTvan : ∀ (k : ℕ) s x i j, (s < 1 / ((k : ℝ) + 1) ∨ (k : ℝ) + 1 < s ∨
      c / 2 * ((k : ℝ) + 1) / ((k : ℝ) + 2) < |x.1| ∨ (k : ℝ) + 1 < |x.2|) →
      niceTrunc c F k (s, x) i j = 0 := by
    intro k s x i j h
    unfold niceTrunc
    apply Set.indicator_of_notMem
    intro hmem
    simp only [niceTruncBox, mem_setOf_eq] at hmem
    rcases h with h | h | h | h <;>
      linarith [hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2]
  have hrk : ∀ k : ℕ, c / 2 * ((k : ℝ) + 1) / ((k : ℝ) + 2) < c / 2 := by
    intro k
    have hc2 : 0 < c / 2 := by positivity
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  choose Fk hFk using fun k : ℕ => hB c ν γ hc hν (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1)
    (c / 2 * ((k : ℝ) + 1) / ((k : ℝ) + 2)) ((k : ℝ) + 1) (by positivity) (hrk k)
    (niceTrunc c F k) (hTsym k) (hTmeas k) (hTvan k) (hTfin k) (1 / ((k : ℝ) + 1))
    (by positivity)
  refine ⟨Fk, fun k => (hFk k).1, ?_⟩
  have hbound : ∀ k : ℕ, tCalNorm c (gainConj γ ν (fun p i j => Fk k p i j - F p i j)) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) +
        tCalNorm c (gainConj γ ν (fun p i j => F p i j - niceTrunc c F k p i j)) := by
    intro k
    have h := hTri c ν γ (Fk k) (niceTrunc c F k) F
      (fun i j => ((hFk k).1.2.1 i j).continuous.measurable) (hTmeas k) hmeas
    exact h.trans (add_le_add (hFk k).2.le le_rfl)
  have h1 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1)) +
      tCalNorm c (gainConj γ ν (fun p i j => F p i j - niceTrunc c F k p i j))) atTop (𝓝 0) := by
    simpa using h1.add hTlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k => zero_le) hbound

end UnforcedLeray.Short.IIIa
