import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2_4

/-!
# `PartII-b:G4/3/7/4` (`InletJetDecay`), decomposition

Source `the November 2 reference manuscript` lines 2347-2358, 2360-2369.
`InletJetDecay` follows from `CutStreamJets` (proved, `cutStreamJets`), `InletProfileSmoothVanish`
(proved), `CutStreamSVanish` (leaf) and the decay-preserving ring-stream Leibniz leaf
`RingStreamJetsDecay` (leaf; decay constant halved by `|η|e^{-κ|η|/c'} ≤ (2c'/(eκ))e^{-κ|η|/(2c')}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Leaf** (SP 2360-2369): decay-preserving version of `RingStreamJetsFix`
(`ringStreamProfile R φ = (-φ_η, φ_q + R⁻¹(φ - 2sφ_s - ηφ_η))`, Leibniz; `|η|` absorbed by halving
`κ`). -/
def RingStreamJetsDecay : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (R S c' κ M : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → 0 < S → 0 < c' → 0 < κ → 0 ≤ M →
      ContDiff ℝ ∞ φ → (∀ x : ℝ × (ℝ × ℝ), S < x.1 → φ x = 0) →
      (∀ x : ℝ × (ℝ × ℝ), x.1 < -S → fderiv ℝ φ x (1, (0, 0)) = 0) →
      (∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c'))) →
      ∀ l ≤ j, ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R φ) m‖ ≤
          C * (1 + S) * (1 + c' / κ) * M * Real.exp (-((κ / 2) * |m.2.2| / c'))

theorem inletJetDecay_of (h3 : CutStreamJets) (h4 : RingStreamJetsDecay)
    (h5 : InletProfileSmoothVanish) (h6 : CutStreamSVanish) : InletJetDecay := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := h3 lam q hq (2 + 1)
  obtain ⟨C4, hC4, h4'⟩ := h4 2
  obtain ⟨ν₀, hν₀, h5'⟩ := h5 Sig lam q hSig hq dm dp hdm
  set K : ℝ := C4 * (1 + Sig) * (1 + 1 / κ) * (C3 * (1 + 1 / Sig) ^ (2 + 1)) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K, κ / 2, 3 + 2 * N, min ν₀ 1, hKpos, half_pos hκ, lt_min hν₀ one_pos, min_le_right _ _, ?_⟩
  intro p d hreg i
  obtain ⟨hreg, hν, hSig', hmode⟩ := hreg
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  obtain ⟨hsm, hvan⟩ := h5' p d hreg hν0 hSig' hmode i
  refine ⟨hsm, ?_⟩
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
  set M : ℝ := C3 * (1 + p.H⁻¹) ^ (2 + 1) * p.c ^ N with hM
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
      C4 * (1 + p.H / 2) * (1 + p.c / κ) * M * Real.exp (-((κ / 2) * |x.2.2| / p.c)) :=
    hring l hl x
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
  have hMle : M ≤ C3 * (1 + 1 / Sig) ^ (2 + 1) * p.c ^ N := by
    rw [hM]; gcongr
  have hcν : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hfin : C4 * (1 + p.H / 2) * (1 + p.c / κ) * M ≤
      C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (2 + 1) * p.c ^ N) := by
    gcongr
  have heq : C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (2 + 1) * p.c ^ N) = K * (p.ν ^ (3 + 2 * N))⁻¹ := by
    have hν' := hνpos.ne'
    have e : (p.ν ^ (3 + 2 * N))⁻¹ = p.ν⁻¹ * (p.ν ^ 2)⁻¹ * ((p.ν ^ 2)⁻¹) ^ N := by
      have e3 : (p.ν ^ 3)⁻¹ = p.ν⁻¹ * (p.ν ^ 2)⁻¹ := by
        rw [← mul_inv]; congr 1; ring
      rw [pow_add p.ν 3 (2 * N), pow_mul, mul_inv, inv_pow, e3]
    rw [e, hK, hcν]
    ring
  calc _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin (Real.exp_pos _).le
    _ = _ := by rw [heq]

end UnforcedLeray.Short.IIb
