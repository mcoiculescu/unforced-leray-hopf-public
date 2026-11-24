import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/4` (`DualPsiInfJet`): jet bound for `ψ_∞`.

Source: `the November 2 reference manuscript`
lines 1923-1927.  `ψ_∞ = (a ∘ fst) · g` with `a(σ) = σ^{μ-1}χ(σ)`; Leibniz on the open set
`{z.1 < s}` where `g(z) = H(s-z.1,z.2)` is smooth.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- the scalar factor `a(σ) = σ^{μ-1} χ(σ)`. -/
def dualJetA (μ : ℂ) (χ : ℝ → ℝ) (σ : ℝ) : ℂ := ((σ : ℂ) ^ (μ - 1)) * (χ σ : ℂ)

theorem dualJet_aSmooth (μ : ℂ) (s : ℝ) (χ : ℝ → ℝ) (hχ : DFChi s χ) :
    ContDiff ℝ ∞ (dualJetA μ χ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hx0 : 0 < x := (hχ.2.2 hx).1
    have hQ : ContDiffAt ℝ ∞ (fun y : ℝ => ((χ y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hχ.1.contDiffAt
    have hP : ContDiffAt ℝ ∞ (fun σ : ℝ => ((σ : ℂ)) ^ (μ - 1)) x := by
      have hs : (x : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inl (by rw [Complex.ofReal_re]; exact hx0))
      have h1 : ContDiffAt ℂ ∞ (fun w : ℂ => w ^ (μ - 1)) (x : ℂ) :=
        AnalyticAt.contDiffAt (analyticAt_id.cpow analyticAt_const hs)
      exact (h1.restrict_scalars (𝕜 := ℝ)).comp x Complex.ofRealCLM.contDiff.contDiffAt
    exact hP.mul hQ
  · have hU : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hev : dualJetA μ χ =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      unfold dualJetA
      rw [image_eq_zero_of_notMem_tsupport hy]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem dualJet_sup (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (K : Set ℝ) (hK : IsCompact K) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ K, ‖iteratedFDeriv ℝ k a σ‖ ≤ M := by
  have hc : Continuous (fun σ => iteratedFDeriv ℝ k a σ) :=
    ha.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun σ hσ => (hC σ hσ).trans (le_max_left _ _)⟩

theorem dualJet_fst (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (k : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ k (fun y : Coord => a y.1) x‖ ≤ ‖iteratedFDeriv ℝ k a x.1‖ := by
  have h := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).iteratedFDeriv_comp_right ha x
    (i := k) (by exact_mod_cast le_top)
  have h2 : (fun y : Coord => a y.1) = a ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := rfl
  rw [h2, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin k, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _)
  have e : (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x = x.1 := rfl
  rw [e]
  calc _ ≤ ‖iteratedFDeriv ℝ k a x.1‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem dualPsiInfJet : UnforcedLeray.Short.IIb.DualPsiInfJet := by
  intro c ν μ H s r' χ hc hν hs hH hχ
  have ha := dualJet_aSmooth μ s χ hχ
  have hK : IsCompact (tsupport χ) := hχ.2.1.isCompact
  choose Mk hMk0 hMk using fun k : ℕ => dualJet_sup _ ha _ hK k
  set M : ℝ := ∑ k ∈ Finset.range 4, Mk k with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun k _ => hMk0 k)
  have hMle : ∀ k ∈ Finset.range 4, Mk k ≤ M := fun k hk =>
    Finset.single_le_sum (f := Mk) (fun j _ => hMk0 j) hk
  refine ⟨128 * M, by positivity, ?_⟩
  intro x hx
  have hxI : x.1 ∈ Ioo (0 : ℝ) s := hχ.2.2 hx
  set U : Set Coord := {z | z.1 < s} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_fst continuous_const
  have hxU : x ∈ U := hxI.2
  have hgAt : ∀ z ∈ U, ContDiffAt ℝ ∞ (fun w : Coord => H (s - w.1, w.2)) z := by
    intro z hz
    have hm : ContDiff ℝ ∞ (fun y : Coord => (s - y.1, y.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    have hp : (s - z.1, z.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
      ⟨show (0 : ℝ) < s - z.1 by have : z.1 < s := hz; linarith, mem_univ _⟩
    have hHc : ContDiffAt ℝ ∞ H (s - z.1, z.2) :=
      hH.smooth.contDiffAt (IsOpen.mem_nhds (IsOpen.prod isOpen_Ioi isOpen_univ) hp)
    exact hHc.comp z hm.contDiffAt
  have hGAt : ∀ z ∈ U, ContDiffAt ℝ ∞ (fun w : Coord => ((H (s - w.1, w.2) : ℝ) : ℂ)) z :=
    fun z hz => Complex.ofRealCLM.contDiff.contDiffAt.comp z (hgAt z hz)
  have hGon : ContDiffOn ℝ ∞ (fun w : Coord => ((H (s - w.1, w.2) : ℝ) : ℂ)) U :=
    fun z hz => (hGAt z hz).contDiffWithinAt
  have hFon : ContDiffOn ℝ ∞ (fun w : Coord => dualJetA μ χ w.1) U :=
    (ha.comp contDiff_fst).contDiffOn
  set S : ℝ := ∑ n ∈ Finset.range 4,
    ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖ with hS
  have hSn : ∀ m ∈ Finset.range 4,
      ‖iteratedFDeriv ℝ m (fun z : Coord => H (s - z.1, z.2)) x‖ ≤ S := fun m hm =>
    Finset.single_le_sum (f := fun m => ‖iteratedFDeriv ℝ m (fun z : Coord => H (s - z.1, z.2)) x‖)
      (fun j _ => norm_nonneg _) hm
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hGnorm : ∀ m : ℕ, ‖iteratedFDeriv ℝ m
      (fun w : Coord => ((H (s - w.1, w.2) : ℝ) : ℂ)) x‖ =
      ‖iteratedFDeriv ℝ m (fun z : Coord => H (s - z.1, z.2)) x‖ := by
    intro m
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hgAt x hxU) (by exact_mod_cast le_top)
  have hbound : ∀ n ∈ Finset.range 4,
      ‖iteratedFDeriv ℝ n (dualPsiInf μ χ H s) x‖ ≤ 32 * M * S := by
    intro n hn
    have hn4 : n < 4 := Finset.mem_range.1 hn
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hFon hGon
      hUo.uniqueDiffOn hxU (n := n) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen n hUo hxU] at hmul
    have hpsi : (fun y : Coord => dualJetA μ χ y.1 * ((H (s - y.1, y.2) : ℝ) : ℂ)) =
        dualPsiInf μ χ H s := rfl
    rw [hpsi] at hmul
    refine hmul.trans ?_
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun w : Coord => dualJetA μ χ w.1) U x‖ *
          ‖iteratedFDerivWithin ℝ (n - i) (fun w : Coord => ((H (s - w.1, w.2) : ℝ) : ℂ)) U x‖
          ≤ 8 * M * S := by
      intro i hi
      have hi4 : i < 4 := by have := Finset.mem_range.1 hi; omega
      rw [iteratedFDerivWithin_of_isOpen i hUo hxU, iteratedFDerivWithin_of_isOpen (n - i) hUo hxU,
        hGnorm]
      have h1 : (n.choose i : ℝ) ≤ 8 := by
        have : n.choose i ≤ 2 ^ n := Nat.choose_le_two_pow n i
        have h8 : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast this.trans h8
      have h2 : ‖iteratedFDeriv ℝ i (fun w : Coord => dualJetA μ χ w.1) x‖ ≤ M :=
        (dualJet_fst _ ha i x).trans ((hMk i x.1 hx).trans (hMle i (Finset.mem_range.2 hi4)))
      have h3 := hSn (n - i) (Finset.mem_range.2 (by omega))
      have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun w : Coord => dualJetA μ χ w.1) x)
      have h30 := norm_nonneg (iteratedFDeriv ℝ (n - i) (fun z : Coord => H (s - z.1, z.2)) x)
      have h10 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul h1 h2 h0 (by norm_num)) h3 h30 (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    have hn' : (n : ℝ) + 1 ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
      linarith
    have h8 : 0 ≤ 8 * M * S := by positivity
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    nlinarith
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  linarith

end UnforcedLeray.Short.IIb
