import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamSVanish
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# `InletProfGlobal` (task `PartIII-b:C/ward/12/3/1/2/7/6/1/1`)

Source `the November 2 reference manuscript` lines 2385-2387, 2562-2564, 2347-2369.
For each fixed `p` the combination `∑ αᵢ inletProfile i` is smooth, `c`-periodic in `ξ`, zero for
`s ≥ H/2`, and its jets of order `≤ 2` decay like `e^{-(κ/2)|η|/c}`. The jets come from
`cutStreamJets` (order `≤ 3`), `cutStreamSVanish` and `ringStreamJetsDecay` (with `S = H/2`,
`R = p.R ≥ 1`), applied to each profile; the constants are uniform in `i`, so the combination
is bounded by `(∑ |αᵢ|)` times one constant.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- A continuous function vanishing on the open half-space `{a < s}` vanishes on `{s = a}`. -/
theorem zero_at_edge {E : Type*} [NormedAddCommGroup E] (g : ℝ × (ℝ × ℝ) → E) (hg : Continuous g)
    (a : ℝ) (hz : ∀ x : ℝ × (ℝ × ℝ), a < x.1 → g x = 0) (x : ℝ × (ℝ × ℝ)) (hx : x.1 = a) :
    g x = 0 := by
  obtain ⟨s, z⟩ := x
  simp only at hx
  subst hx
  have h1 : Tendsto (fun t : ℝ => g (t, z)) (𝓝[>] s) (𝓝 (g (s, z))) :=
    ((hg.comp (continuous_id.prodMk continuous_const)).tendsto s).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ => g (t, z)) (𝓝[>] s) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hz (t, z) ht).symm
  exact tendsto_nhds_unique h1 h2

/-- **Sub1: the inlet profile combination satisfies the hypotheses.** -/
theorem inletProfGlobal : InletProfGlobal := by
  intro lam q hq dm dp hdm p d hreg hν hmode α
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (pow_pos hνpos 2)]
    nlinarith
  have hcpos : 0 < p.c := lt_of_lt_of_le one_pos hc1
  have hH : 0 < p.H := p.H_pos
  have hHhalf : 0 < p.H / 2 := half_pos hH
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact (one_le_inv₀ p.ε_pos).mpr hε
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq (2 + 1)
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay 2
  set M : ℝ := C3 * (1 + p.H⁻¹) ^ (2 + 1) * p.c ^ N with hM
  have hHinv : 0 ≤ 1 + p.H⁻¹ := by
    have := inv_nonneg.mpr hH.le
    linarith
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg hC3.le (pow_nonneg hHinv _)) (pow_nonneg hcpos.le _)
  have hcutSm : ∀ i : Fin 2, ContDiff ℝ ∞ (p.cutStream i) :=
    fun i => (h3' p hmode hc1 hH i).1
  -- strict vanishing of the inlet profile (as in `inlet_contDiff_joint`)
  have hzS : ∀ i : Fin 2, ∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0 := by
    intro i x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hx.le]
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
        (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hy.le]
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
  have hsm : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inletProfile i) := fun i => by
    unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile (hcutSm i)
  have hvanE : ∀ i : Fin 2, ∀ x : ℝ × (ℝ × ℝ), p.H / 2 ≤ x.1 → p.inletProfile i x = 0 := by
    intro i x hx
    rcases hx.lt_or_eq with h | h
    · exact hzS i x h
    · exact zero_at_edge (p.inletProfile i) (hsm i).continuous (p.H / 2)
        (fun y hy => hzS i y hy) x h.symm
  have hring : ∀ i : Fin 2, ∀ l ≤ 2, ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l (p.inletProfile i) m‖ ≤
        C4 * (1 + p.H / 2) * (1 + p.c / κ) * M * Real.exp (-((κ / 2) * |m.2.2| / p.c)) := by
    intro i l hl m
    exact h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 hHhalf hcpos hκ hM0 (hcutSm i)
      (by
        intro x hx
        unfold Params.cutStream
        simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
      (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
      (fun l hl x => (h3' p hmode hc1 hH i).2 l hl x) l hl m
  have hbapp : ∀ m : ℝ × (ℝ × ℝ),
      (∑ i : Fin 2, α i • p.inletProfile i) m = ∑ i : Fin 2, α i • p.inletProfile i m := by
    intro m
    simp [Finset.sum_apply]
  have hfun : (∑ i : Fin 2, α i • p.inletProfile i) =
      fun m => ∑ i : Fin 2, α i • p.inletProfile i m := by
    funext m
    exact hbapp m
  refine ⟨(∑ i : Fin 2, |α i|) * (C4 * (1 + p.H / 2) * (1 + p.c / κ) * M), κ / 2,
    half_pos hκ, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact ContDiff.sum fun i _ => (hsm i).const_smul (α i)
  · intro s ξ η
    rw [hbapp, hbapp]
    simp only [Params.inletProfile_periodic]
  · intro m hm
    rw [hbapp]
    exact Finset.sum_eq_zero fun i _ => by rw [hvanE i m hm, smul_zero]
  · intro l hl m
    rw [hfun, iteratedFDeriv_sum (fun i _ => ((hsm i).const_smul (α i)).of_le (by exact_mod_cast le_top))]
    simp only [Finset.sum_apply]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j : Fin 2, ‖iteratedFDeriv ℝ l (fun m => α j • p.inletProfile j m) m‖ ≤
        |α j| * (C4 * (1 + p.H / 2) * (1 + p.c / κ) * M * Real.exp (-((κ / 2) * |m.2.2| / p.c))) := by
      intro j
      rw [iteratedFDeriv_const_smul_apply' ((hsm j).of_le (by exact_mod_cast le_top)).contDiffAt,
        norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hring j l hl m) (abs_nonneg _)
    calc ∑ j : Fin 2, ‖iteratedFDeriv ℝ l (fun m => α j • p.inletProfile j m) m‖
        ≤ ∑ j : Fin 2, |α j| * (C4 * (1 + p.H / 2) * (1 + p.c / κ) * M *
            Real.exp (-((κ / 2) * |m.2.2| / p.c))) := Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j : Fin 2, |α j|) * (C4 * (1 + p.H / 2) * (1 + p.c / κ) * M *
            Real.exp (-((κ / 2) * |m.2.2| / p.c))) := (Finset.sum_mul _ _ _).symm
      _ = (∑ j : Fin 2, |α j|) * (C4 * (1 + p.H / 2) * (1 + p.c / κ) * M) *
            Real.exp (-((κ / 2) * |m.2.2| / p.c)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
