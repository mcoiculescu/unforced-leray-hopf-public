import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Defs
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2_w
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.CutStreamSVanish

/-!
# Weighted jets of the inlet profile at one level (source 2347-2369, 2385-2387)

Source of record: `the November 2 reference manuscript` (73 pages).

Leaf of `PartIII-b:C/ward/12` (`BgInletProfileJetsAt`, `Ward/Bg/YoungW2/Defs.lean`).  The
single-level form of `IIb.InletProfileWeightedJets` (orders `≤ 2`, weight `2`): smoothness and
vanishing for `s > H/2` exactly as in `IIb.inletContDiff` (only `c = ν⁻² ≥ 1` and `H > 0` are used),
the jets from the accepted `IIb.cutStreamJets` (the cut stream `χ(s)ψᵢ` and its derivatives decay
like `e^{-κ|η|/c}`, SP 2356-2358), `IIb.ringStreamJetsDecay` (Leibniz for `ringStreamProfile`, decay
rate halved) and `IIb.cutStreamSVanish`, and the weight absorbed by
`(1+t)² e^{-at} ≤ e · 2! · (1 + a⁻¹)²` (`IIb.InletWeightAux.one_add_pow_mul_exp_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params ageCutoff_eq_zero contDiff_ageCutoff)

/-- **`BgInletProfileJetsAt`** (source 2347-2369, 2385-2387). -/
theorem bgInletProfileJetsAt : BgInletProfileJetsAt := by
  intro lam q hq p d dm dp hreg hν hmode i
  obtain ⟨Cf, κf, Nf, -, -, hper⟩ := UnforcedLeray.Short.IIb.frozenStreamBounds lam q hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hcpos : 0 < p.c := by linarith
  have hH : 0 < p.H := p.H_pos
  have hR1 : 1 ≤ p.R := bgRegime_one_le_R hreg
  -- smoothness and vanishing, as in `IIb.inletContDiff`
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => UnforcedLeray.Short.IIb.inletCD_frozenStream (hper p.c hc1).1 hmode k
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul ((hfro i).comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile hcut
  have hvan : ∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0 := by
    intro x hx
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
    have hdS : UnforcedLeray.Axi.dS (p.cutStream i) x = 0 := by
      unfold UnforcedLeray.Axi.dS
      rw [hfd]
      simp
    have hdQ : UnforcedLeray.Axi.dQ (p.cutStream i) x = 0 := by
      unfold UnforcedLeray.Axi.dQ
      rw [hfd]
      simp
    have hdE : UnforcedLeray.Axi.dEta (p.cutStream i) x = 0 := by
      unfold UnforcedLeray.Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, UnforcedLeray.Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  -- the jets
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq 3
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay 2
  obtain ⟨hcutsm, hcutb⟩ := h3' p hmode hc1 hH i
  have hMc0 : 0 ≤ C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N := by positivity
  have hring := h4' p.R (p.H / 2) p.c κ (C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N) (p.cutStream i) hR1
    (by positivity) hcpos hκ hMc0 hcutsm
    (by
      intro x hx
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcutb l hl x)
  have hA0 : 0 ≤ C4 * (1 + p.H / 2) * (1 + p.c / κ) * (C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N) :=
    mul_nonneg (by positivity) hMc0
  refine ⟨hB, hvan, C4 * (1 + p.H / 2) * (1 + p.c / κ) * (C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N) *
    (Real.exp 1 * ((Nat.factorial 2 : ℕ) : ℝ) * (1 + (κ / 2 / p.c)⁻¹) ^ 2), fun l hl x => ?_⟩
  have hmain := hring l hl x
  have ha : 0 < κ / 2 / p.c := by positivity
  have hw := UnforcedLeray.Short.IIb.InletWeightAux.one_add_pow_mul_exp_le 2 ha (abs_nonneg x.2.2)
  have e : -((κ / 2) * |x.2.2| / p.c) = -((κ / 2 / p.c) * |x.2.2|) := by ring
  rw [e] at hmain
  calc (1 + |x.2.2|) ^ 2 * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖
      ≤ (1 + |x.2.2|) ^ 2 * (C4 * (1 + p.H / 2) * (1 + p.c / κ) *
          (C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N) * Real.exp (-((κ / 2 / p.c) * |x.2.2|))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C4 * (1 + p.H / 2) * (1 + p.c / κ) * (C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N) *
          ((1 + |x.2.2|) ^ 2 * Real.exp (-((κ / 2 / p.c) * |x.2.2|))) := by ring
    _ ≤ C4 * (1 + p.H / 2) * (1 + p.c / κ) * (C3 * (1 + p.H⁻¹) ^ 3 * p.c ^ N) *
          (Real.exp 1 * ((Nat.factorial 2 : ℕ) : ℝ) * (1 + (κ / 2 / p.c)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hw hA0

#print axioms bgInletProfileJetsAt

end UnforcedLeray.Short.PartIIIb.Concrete
