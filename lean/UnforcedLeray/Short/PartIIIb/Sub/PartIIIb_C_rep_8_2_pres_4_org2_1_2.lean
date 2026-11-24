import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletJetDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish

/-!
# Organizer task `PartIII-b:C/rep/8/2/pres/4/org2/1/2`: `inletChartJet`

Source `the November 2 reference manuscript` 2347-2356, 2360-2366, 2389-2390.
Ring-lift chart jets (`ringLiftChartPt`) are applied to the inlet profile, whose jets of order
`≤ 2` carry the exponential transverse decay (`IIb.inletJetDecay`); the profile vanishes for
`s > H/2` (`IIb.inletProfileSmoothVanish`), which kills the ring-lift bound there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A function vanishing near `x` has vanishing norm of every iterated derivative at `x`. -/
private lemma norm_iter_zero_of_eventually {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) {x : E}
    (h : ∀ᶠ y in 𝓝 x, f y = 0) (l : ℕ) : ‖iteratedFDeriv ℝ l f x‖ = 0 := by
  have hf : f =ᶠ[𝓝 x] (fun _ => (0 : F)) := h
  rw [(hf.iteratedFDeriv ℝ l).eq_of_nhds]
  cases l with
  | zero => simp
  | succ n => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

theorem inletChartJet : InletChartJet := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨Ca0, ka0, hCa0, h0⟩ := ringLiftChartPt 0
  obtain ⟨Ca1, ka1, hCa1, h1⟩ := ringLiftChartPt 1
  obtain ⟨Ca2, ka2, hCa2, h2⟩ := ringLiftChartPt 2
  obtain ⟨C1, κ, k1, νa, hC1, hκ, hνa, hνa1, hdec⟩ :=
    UnforcedLeray.Short.IIb.inletJetDecay Sig lam q hSig hq dm dp hdm
  obtain ⟨νb, hνb, hvan⟩ :=
    UnforcedLeray.Short.IIb.inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨Cr, hCr⟩ : ∃ c : ℝ, c = Ca0 + Ca1 + Ca2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ n : ℕ, n = ka0 + ka1 + ka2 := ⟨_, rfl⟩
  have hCrpos : 0 < Cr := by linarith
  have hCa0le : Ca0 ≤ Cr := by linarith
  have hCa1le : Ca1 ≤ Cr := by linarith
  have hCa2le : Ca2 ≤ Cr := by linarith
  have hka0 : ka0 ≤ K := by omega
  have hka1 : ka1 ≤ K := by omega
  have hka2 : ka2 ≤ K := by omega
  -- uniform ring-lift bound for the orders `j ≤ 2`
  have lift_unif : ∀ j : ℕ, j ≤ 2 → ∀ (R : ℝ) (b : Chart → Merid), 1 ≤ R →
      ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) → ∀ x : Chart, 0 < x.1 →
        ‖iteratedFDeriv ℝ j (Nv R b (NearInst.chartTau R x)) (NearInst.chartY R x)‖ ≤
          Cr * (1 + x.1) ^ K * (1 + |x.2.2|) ^ j *
            ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b x‖ := by
    intro j hj R b hR hb x hx
    have h1x : (1 : ℝ) ≤ 1 + x.1 := by linarith
    have hsum : ∀ (Ca : ℝ) (ka : ℕ), 0 ≤ Ca → Ca ≤ Cr → ka ≤ K → ∀ (B S' : ℝ), 0 ≤ B →
        0 ≤ S' → Ca * (1 + x.1) ^ ka * B * S' ≤ Cr * (1 + x.1) ^ K * B * S' := by
      intro Ca ka hCa hCale hkale B S' hB0 hS0
      apply mul_le_mul_of_nonneg_right _ hS0
      apply mul_le_mul_of_nonneg_right _ hB0
      exact mul_le_mul hCale (pow_le_pow_right₀ h1x hkale) (pow_nonneg (by linarith) _) hCrpos.le
    interval_cases j
    · exact le_trans (h0 R b hR hb x hx)
        (hsum Ca0 ka0 hCa0.le hCa0le hka0 _ _ (by positivity)
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    · exact le_trans (h1 R b hR hb x hx)
        (hsum Ca1 ka1 hCa1.le hCa1le hka1 _ _ (by positivity)
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    · exact le_trans (h2 R b hR hb x hx)
        (hsum Ca2 ka2 hCa2.le hCa2le hka2 _ _ (by positivity)
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hCpos : 0 < 3 * Cr * C1 * (1 + Sig) ^ K :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCrpos) hC1) (pow_pos (by linarith) K)
  refine ⟨3 * Cr * C1 * (1 + Sig) ^ K, κ, k1 + K, min νa νb, hCpos, hκ, lt_min hνa hνb, ?_⟩
  intro p d hBg hν hSig' hmode i x hx j hj
  have hνp : p.ν ≤ νa := hν.trans (min_le_left _ _)
  have hνp' : p.ν ≤ νb := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := hνp.trans hνa1
  have hνpos : 0 < p.ν := p.ν_pos
  obtain ⟨hsm, hdb⟩ := hdec p d ⟨hBg, hνp, hSig', hmode⟩ i
  obtain ⟨-, hvanp⟩ := hvan p d hBg hνp' hSig' hmode i
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hBg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hBg.dm_pos, hBg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact (one_le_inv₀ p.ε_pos).mpr hε
  have hc : p.c = (p.ν ^ 2)⁻¹ := hBg.c_eq
  have hexp : ∀ y : Chart,
      Real.exp (-(κ * |y.2.2| / p.c)) = Real.exp (-(κ * p.ν ^ 2) * |y.2.2|) := by
    intro y
    congr 1
    rw [hc, div_inv_eq_mul]
    ring
  have hbound : ∀ l : ℕ, l ≤ 2 → ∀ y : Chart,
      ‖iteratedFDeriv ℝ l (p.inletProfile i) y‖ ≤
        C1 * (p.ν ^ k1)⁻¹ * Real.exp (-(κ * p.ν ^ 2) * |y.2.2|) := by
    intro l hl y
    have h := hdb l hl y
    rw [hexp y] at h
    exact h
  have hMnn : 0 ≤ C1 * (p.ν ^ k1)⁻¹ * Real.exp (-(κ * p.ν ^ 2) * |x.2.2|) :=
    mul_nonneg (mul_nonneg hC1.le (inv_nonneg.2 (pow_nonneg hνpos.le _))) (Real.exp_pos _).le
  have hS : ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      3 * (C1 * (p.ν ^ k1)⁻¹ * Real.exp (-(κ * p.ν ^ 2) * |x.2.2|)) := by
    interval_cases j <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;>
      linarith [hbound 0 (by norm_num) x, hbound 1 (by norm_num) x, hbound 2 (by norm_num) x]
  by_cases hs : p.H / 2 < x.1
  · -- beyond the cutoff the inlet profile vanishes near `x`, so the ring-lift bound is zero
    have hopen : IsOpen {y : Chart | p.H / 2 < y.1} := isOpen_lt continuous_const continuous_fst
    have hev : ∀ᶠ y in 𝓝 x, p.inletProfile i y = 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds hs) (fun y hy => hvanp y hy)
    have hS0 : ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ = 0 :=
      Finset.sum_eq_zero (fun l _ => norm_iter_zero_of_eventually _ hev l)
    have hL := lift_unif j hj p.R (p.inletProfile i) hR1 hsm.contDiffOn x hx
    rw [hS0, mul_zero] at hL
    refine le_trans hL ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpos.le
      (inv_nonneg.2 (pow_nonneg hνpos.le _))) (pow_nonneg (by positivity) _)) (Real.exp_pos _).le
  · have hs' : x.1 ≤ p.H / 2 := not_lt.mp hs
    have hHe : p.H = Sig / p.ν := by rw [UnforcedLeray.Cons.C03.Concrete.Params.H, hSig']
    have h1' : (1 : ℝ) ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
    have h2' : 0 ≤ Sig / p.ν := div_nonneg hSig.le hνpos.le
    have e : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by rw [div_eq_mul_inv]; ring
    have e2 : p.H / 2 = Sig / p.ν / 2 := by rw [hHe]
    have hHalf : 1 + x.1 ≤ (1 + Sig) * p.ν⁻¹ := by
      rw [e]
      rw [e2] at hs'
      linarith
    have hA : (1 + x.1) ^ K ≤ ((1 + Sig) * p.ν⁻¹) ^ K :=
      pow_le_pow_left₀ (by linarith) hHalf K
    have hB : (1 + |x.2.2|) ^ j ≤ (1 + |x.2.2|) ^ 2 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg x.2.2]) hj
    have hB0 : 0 ≤ (1 + |x.2.2|) ^ j := pow_nonneg (by linarith [abs_nonneg x.2.2]) _
    have hSnn : 0 ≤ ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hY : 0 ≤ Cr * ((1 + Sig) * p.ν⁻¹) ^ K :=
      mul_nonneg hCrpos.le (pow_nonneg (mul_nonneg (by linarith) (inv_nonneg.2 hνpos.le)) K)
    have hL := lift_unif j hj p.R (p.inletProfile i) hR1 hsm.contDiffOn x hx
    refine le_trans hL ?_
    calc Cr * (1 + x.1) ^ K * (1 + |x.2.2|) ^ j *
          ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖
        ≤ Cr * ((1 + Sig) * p.ν⁻¹) ^ K * (1 + |x.2.2|) ^ 2 *
            (3 * (C1 * (p.ν ^ k1)⁻¹ * Real.exp (-(κ * p.ν ^ 2) * |x.2.2|))) := by
          apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hA hCrpos.le) hB hB0 hY) hS hSnn
          exact mul_nonneg hY (pow_nonneg (by linarith [abs_nonneg x.2.2]) _)
      _ = 3 * Cr * C1 * (1 + Sig) ^ K * (p.ν ^ (k1 + K))⁻¹ * (1 + |x.2.2|) ^ 2 *
            Real.exp (-(κ * p.ν ^ 2) * |x.2.2|) := by
          rw [mul_pow, inv_pow, pow_add, mul_inv]
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
