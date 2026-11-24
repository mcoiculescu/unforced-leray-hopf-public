import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2

/-!
# Part II-b, task `PartII-b:G4/5/2/2` (`InletProfileJets`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2347-2369
(inlet profile `e_ε = (-χψ_η, χψ_q + ε[(χ - 2sχ')ψ - χηψ_η])`), 2383-2385 (`W^{j,∞}` bounds).


stream must be carried with the transverse decay `exp(-κ|η|/c)` of `FrozenStreamBounds`
(`|η| e^{-κ|η|/c} ≤ c/κ`), not as plain sup bounds.

Five true leaves; the assembly `inletProfileJets_of` is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Leaf 1** (SP 2358, `χ = smoothTransition(2 - 4s/H)`): derivatives of the age cutoff,
`|χ^{(l)}(s)| ≤ C_j H^{-l}` for `l ≤ j`, all `H > 0`, `s ∈ ℝ` (chain rule: `(4/H)^l` times the
bounded derivatives of `Real.smoothTransition`, which are constant outside `[0,1]`). -/
def AgeCutoffJets : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H → ∀ l ≤ j, ∀ s : ℝ,
    ‖iteratedDeriv l (ageCutoff H) s‖ ≤ C * (H⁻¹) ^ l

/-- **Leaf 2** (SP 2347-2358, `frozenStreamBounds`): jets of the frozen streams
`2 Re P_c ψ`, `-2 Im P_c ψ` with the transverse decay, `c ≥ 1`; follows from `frozenStreamBounds`
(take the maximum of the constants over `l ≤ j`; `re`, `im` are continuous linear maps). -/
def FrozenStreamJets : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q → ∀ j : ℕ,
    ∃ (C κ : ℝ) (N : ℕ), 0 < C ∧ 0 < κ ∧ ∀ (p : Params), p.mode = q → 1 ≤ p.c →
      ∀ (i : Fin 2), ∀ l ≤ j, ∀ x : ℝ × ℝ,
        ‖iteratedFDeriv ℝ l (p.frozenStream i) x‖ ≤ C * p.c ^ N * Real.exp (-(κ * |x.2| / p.c))

/-- **Leaf 3** (Leibniz for `cutStream i m = χ(m.1) ψ_i(m.2)`; from Leaves 1 and 2 via
`norm_iteratedFDeriv_mul_le` and composition with `fst`, `snd`). -/
def CutStreamJets : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q → ∀ j : ℕ,
    ∃ (C κ : ℝ) (N : ℕ), 0 < C ∧ 0 < κ ∧ ∀ (p : Params), p.mode = q → 1 ≤ p.c → 0 < p.H →
      ∀ (i : Fin 2), ContDiff ℝ ∞ (p.cutStream i) ∧ ∀ l ≤ j, ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l (p.cutStream i) m‖ ≤
          C * (1 + p.H⁻¹) ^ j * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c))

/-- **Leaf 4** (`ringStreamProfile R φ = (-φ_η, φ_q + R⁻¹(φ - 2sφ_s - ηφ_η))`, Leibniz): if `φ`
vanishes for `s > S` and its derivatives of order `≤ j+1` are bounded by `M e^{-κ|η|/c'}`, then the
derivatives of order `≤ j` of `ringStreamProfile R φ` are bounded by `C_j (1+S)(1 + c'/κ) M`
(`R ≥ 1`; `s ≤ S` on the support of `φ_s`; `|η| e^{-κ|η|/c'} ≤ c'/κ`). -/
def RingStreamJets : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (R S c' κ M : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → 0 < S → 0 < c' → 0 < κ → 0 ≤ M →
      ContDiff ℝ ∞ φ → (∀ x : ℝ × (ℝ × ℝ), S < x.1 → φ x = 0) →
      (∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c'))) →
      ∀ l ≤ j, ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R φ) m‖ ≤ C * (1 + S) * (1 + c' / κ) * M

/-- **Leaf 5** (smoothness and vanishing of the inlet profile; copy of `inletContDiff` /
`hvan` in `Tasks/AffineColumnComparison/InletContDiff.lean`, using `ageCutoff_eq_zero` and
`inletCD_ringStreamProfile`). -/
def InletProfileSmoothVanish : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2), ContDiff ℝ ∞ (p.inletProfile i) ∧
        (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0)

theorem inletProfileJets_of (h3 : CutStreamJets) (h4 : RingStreamJets)
    (h5 : InletProfileSmoothVanish) : InletProfileJets := by
  intro Sig lam q hSig hq dm dp hdm j
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := h3 lam q hq (j + 1)
  obtain ⟨C4, hC4, h4'⟩ := h4 j
  obtain ⟨ν₀, hν₀, h5'⟩ := h5 Sig lam q hSig hq dm dp hdm
  set K : ℝ := C4 * (1 + Sig) * (1 + 1 / κ) * (C3 * (1 + 1 / Sig) ^ (j + 1)) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K, 3 + 2 * N, min ν₀ 1, hKpos, lt_min hν₀ one_pos, ?_⟩
  intro p d hreg hν hSig' hmode i
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  obtain ⟨hsm, hvan⟩ := h5' p d hreg hν0 hSig' hmode i
  refine ⟨hsm, hvan, ?_⟩
  have hH : 0 < p.H := p.H_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hHe : p.H = Sig / p.ν := by rw [Params.H, hSig']
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  have hcpos : 0 < p.c := by linarith
  set M : ℝ := C3 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N with hM
  have hM0 : 0 ≤ M := by positivity
  have hring := h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 (by positivity) hcpos hκ hM0
    hcutsm
    (by
      intro x hx
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun l hl x => hcut l hl x)
  intro l hl x
  have hmain : ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      C4 * (1 + p.H / 2) * (1 + p.c / κ) * M := hring l hl x
  have hS : 1 + p.H / 2 ≤ (1 + Sig) * p.ν⁻¹ := by
    rw [hHe]
    have h1 : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv₀ hνpos |>.mpr hν1
    have e : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by rw [div_eq_mul_inv]; ring
    rw [e]
    nlinarith [div_nonneg hSig.le hνpos.le]
  have hcc : 1 + p.c / κ ≤ (1 + 1 / κ) * p.c := by
    have : p.c / κ = (1 / κ) * p.c := by rw [div_eq_mul_inv]; ring
    rw [this]; nlinarith [mul_nonneg (one_div_pos.2 hκ).le (by linarith : 0 ≤ p.c)]
  have hHi : 1 + p.H⁻¹ ≤ 1 + 1 / Sig := by
    have h1 : p.ν / Sig ≤ 1 / Sig := by gcongr
    have : p.H⁻¹ ≤ 1 / Sig := by
      rw [hHe, inv_div]; exact h1
    linarith
  have hMle : M ≤ C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N := by
    rw [hM]; gcongr
  have hcν : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hfin : C4 * (1 + p.H / 2) * (1 + p.c / κ) * M ≤
      C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N) := by
    gcongr
  have heq : C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N) = K * (p.ν ^ (3 + 2 * N))⁻¹ := by
    have hν' := hνpos.ne'
    have e : (p.ν ^ (3 + 2 * N))⁻¹ = p.ν⁻¹ * (p.ν ^ 2)⁻¹ * ((p.ν ^ 2)⁻¹) ^ N := by
      have e3 : (p.ν ^ 3)⁻¹ = p.ν⁻¹ * (p.ν ^ 2)⁻¹ := by
        rw [← mul_inv]; congr 1; ring
      rw [pow_add p.ν 3 (2 * N), pow_mul, mul_inv, inv_pow, e3]
    rw [e, hK, hcν]
    ring
  calc _ ≤ _ := hmain
    _ ≤ _ := hfin
    _ = _ := heq

end UnforcedLeray.Short.IIb
