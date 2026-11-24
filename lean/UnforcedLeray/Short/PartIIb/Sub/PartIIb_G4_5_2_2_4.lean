import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2

/-!
# Part II-b, task `PartII-b:G4/5/2/2/4/org`: the corrected ring-stream leaf

Source of record: `the November 2 reference manuscript`, lines 2316-2317 (the
inlet carries an age cutoff equal to one near zero and zero before the terminal time), 2356-2366
(exponential transverse decay of the periodized stream and its derivatives; the normalized lift
`e_ε = e_0 + ε e_1`, `e_0 = χ(-ψ_η, ψ_q)`, `e_1 = (0, (χ - 2sχ')ψ - χηψ_η)` of the cut stream
`χ(s)ψ`), 2386-2387 (`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`).

`RingStreamJets` (`Sub/PartII-b_G4_5_2_2.lean`) is false: vanishing of `φ` for `s > S` leaves the
support unbounded as `s → -∞`, where the factor `s` of the `R⁻¹ · 2sφ_s` component is unbounded.
In the source the only stream is `χ(s)ψ`, and `χ = ageCutoff H` is constant for `s ≤ H/4`, so
`φ_s = χ'ψ` vanishes for `s < -H/2` as well. The corrected leaf `RingStreamJetsFix` adds that clause;
`CutStreamSVanish` supplies it for the cut stream; `inletProfileJets_of'` assembles
`InletProfileJets` from them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Corrected Leaf 4** (SP 2360-2366: `ringStreamProfile R φ = (-φ_η, φ_q + R⁻¹(φ - 2sφ_s - ηφ_η))`,
Leibniz). If `φ` is smooth, vanishes for `s > S`, has `φ_s = 0` for `s < -S` (so `|s| ≤ S` on the
support of `φ_s`), and its derivatives of order `≤ j+1` are bounded by `M e^{-κ|η|/c'}`, then the
derivatives of order `≤ j` of `ringStreamProfile R φ` are bounded by `C_j (1+S)(1 + c'/κ) M`
(`R ≥ 1`; `|η| e^{-κ|η|/c'} ≤ c'/κ`). This is `RingStreamJets` with the clause on `s < -S` added. -/
def RingStreamJetsFix : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (R S c' κ M : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → 0 < S → 0 < c' → 0 < κ → 0 ≤ M →
      ContDiff ℝ ∞ φ → (∀ x : ℝ × (ℝ × ℝ), S < x.1 → φ x = 0) →
      (∀ x : ℝ × (ℝ × ℝ), x.1 < -S → fderiv ℝ φ x (1, (0, 0)) = 0) →
      (∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c'))) →
      ∀ l ≤ j, ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R φ) m‖ ≤ C * (1 + S) * (1 + c' / κ) * M

/-- **Leaf 6** (SP 2316-2317, 2360-2366: the cut stream is `χ(s)ψ_i(q, η)` with `χ = ageCutoff H`
equal to `1` for `s ≤ H/4`, `ageCutoff_eq_one`). The age derivative `∂_s(χψ_i) = χ'(s)ψ_i` of the cut stream
vanishes for `s < -H/2`; same quantifier shape as `CutStreamJets`. -/
def CutStreamSVanish : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
    ∀ (p : Params), p.mode = q → 1 ≤ p.c → 0 < p.H →
      ∀ (i : Fin 2) (x : ℝ × (ℝ × ℝ)), x.1 < -(p.H / 2) →
        fderiv ℝ (p.cutStream i) x (1, (0, 0)) = 0

/-- **Assembly of `InletProfileJets`** from the corrected leaf (copy of `inletProfileJets_of`,
passing the clause `s < -H/2` of `CutStreamSVanish` to `RingStreamJetsFix` with `S = H/2`). -/
theorem inletProfileJets_of' (h3 : CutStreamJets) (h4 : RingStreamJetsFix)
    (h5 : InletProfileSmoothVanish) (h6 : CutStreamSVanish) : InletProfileJets := by
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
    (fun x hx => h6 lam q hq p hmode hc1 hH i x hx)
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
