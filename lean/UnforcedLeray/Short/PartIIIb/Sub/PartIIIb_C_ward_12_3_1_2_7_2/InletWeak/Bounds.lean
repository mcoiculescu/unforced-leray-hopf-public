import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletJetBound
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# Per-parameter inlet jet bounds (helper of `InletWeak`)

Source `the November 2 reference manuscript`
lines 2360-2366, 2386-2387.  The statements `InletContDiff`, `InletJetBound` quantify the age cutoff
`Sig` before the threshold `ν₀`.  The `GradEq` regime fixes `ν₀` before `p`, so only the
qualitative content is used here: for *each* parameter `p` in the regime with `ν ≤ 1`, the inlet is
smooth and each of its slice jets is bounded (constant depending on `p`).  The proof is the
assembly of `inletProfileWeightedJets_of` / `inletJetBound_of` run for the single `p`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- Smoothness and vanishing of the inlet profile of a single parameter with `ν ≤ 1`. -/
theorem inletProfile_smooth_vanish {q : Planar.Profile} {lam : ℂ}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} (hc1 : 1 ≤ p.c) (hmode : p.mode = q)
    (i : Fin 2) :
    ContDiff ℝ ∞ (p.inletProfile i) ∧
      ∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0 := by
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := p.H_pos
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul ((hfro i).comp contDiff_snd)
  refine ⟨?_, ?_⟩
  · unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  · intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hx.le]
    have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
      (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]
      simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by
      unfold Axi.dS
      rw [hfd]
      simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
      unfold Axi.dQ
      rw [hfd]
      simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by
      unfold Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]

/-- **Per-parameter slice jet bound** of the inlet (SP 2360-2366, 2386-2387): for `ν ≤ 1` in the
background regime every slice jet of every inlet column is bounded, uniformly in `(τ, y)`. -/
theorem inlet_jet_bound_per {q : Planar.Profile} {lam : ℂ}
    (hq : Planar.IsGrowingEigenpair lam q) {dm dp d : ℝ} {p : Params}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) (j : ℕ) :
    ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ j (p.inlet i τ) y‖ ≤ C := by
  obtain ⟨CA, kA, hCA, hA'⟩ := ringLiftJet j
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := cutStreamJets lam q hq (j + 1)
  obtain ⟨C4, hC4, h4'⟩ := ringStreamJetsDecay j
  have hνpos : 0 < p.ν := p.ν_pos
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
  obtain ⟨hsm, hvan⟩ := inletProfile_smooth_vanish hq hc1 hmode i
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
    (fun x hx => cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  set W : ℝ := Real.exp 1 * j.factorial * (1 + 2 / κ) ^ j with hW
  set A : ℝ := C4 * (1 + p.H / 2) * (1 + p.c / κ) * M with hA
  have hA0 : 0 ≤ A := by positivity
  have hWc : 0 ≤ W * p.c ^ j := by positivity
  have hjet : ∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ),
      (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ A * (W * p.c ^ j) := by
    intro l hl x
    have hmain : ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
        A * Real.exp (-((κ / 2) * |x.2.2| / p.c)) := hring l hl x
    have hwt : (1 + |x.2.2|) ^ j * Real.exp (-((κ / 2) * |x.2.2| / p.c)) ≤ W * p.c ^ j := by
      have ha : 0 < κ / 2 / p.c := by positivity
      have e : -((κ / 2) * |x.2.2| / p.c) = -((κ / 2 / p.c) * |x.2.2|) := by ring
      rw [e]
      have h := InletWeightAux.one_add_pow_mul_exp_le j ha (abs_nonneg x.2.2)
      have hinv : (κ / 2 / p.c)⁻¹ = 2 * p.c / κ := by field_simp
      rw [hinv] at h
      have hb : 1 + 2 * p.c / κ ≤ (1 + 2 / κ) * p.c := by
        have e2 : 2 * p.c / κ = (2 / κ) * p.c := by ring
        rw [e2]
        nlinarith [mul_nonneg (div_pos two_pos hκ).le (by linarith : (0 : ℝ) ≤ p.c - 1)]
      calc _ ≤ Real.exp 1 * j.factorial * (1 + 2 * p.c / κ) ^ j := h
        _ ≤ Real.exp 1 * j.factorial * ((1 + 2 / κ) * p.c) ^ j := by gcongr
        _ = W * p.c ^ j := by rw [hW, mul_pow]; ring
    have hw0 : 0 ≤ (1 + |x.2.2|) ^ j := by positivity
    calc (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖
        ≤ (1 + |x.2.2|) ^ j * (A * Real.exp (-((κ / 2) * |x.2.2| / p.c))) :=
          mul_le_mul_of_nonneg_left hmain hw0
      _ = A * ((1 + |x.2.2|) ^ j * Real.exp (-((κ / 2) * |x.2.2| / p.c))) := by ring
      _ ≤ A * (W * p.c ^ j) := mul_le_mul_of_nonneg_left hwt hA0
  refine ⟨CA * (1 + p.H / 2) ^ kA * (A * (W * p.c ^ j)), fun τ y => ?_⟩
  exact hA' (p.H / 2) p.R τ (A * (W * p.c ^ j)) (p.inletProfile i) (by positivity) hR1
    (by positivity) hsm hvan hjet y

end UnforcedLeray.Short.IIb
