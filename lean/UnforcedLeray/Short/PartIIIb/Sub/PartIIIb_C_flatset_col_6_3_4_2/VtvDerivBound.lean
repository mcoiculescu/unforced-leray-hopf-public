import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-!
`vtvDerivBound` (source 4610 region): uniform `C^k` bounds of `∂_sη(s)` for a stream test, with
`0 < c` (the statement is false for `c = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvDerivBound : VtvDerivBound := by
  intro c hc η hη k
  obtain ⟨hsm, hcyl, s₁, s₂, R, _hs₁, hband⟩ := hη
  set G : ℝ × (ℝ × ℝ) → ℝ := fun q => η q.1 q.2 with hG
  have hGd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := hsm
  have hDG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ G p) :=
    (contDiff_infty_iff_fderiv.1 hGd).2
  have hGdiff : Differentiable ℝ G := hGd.differentiable (by simp)
  set D : ℝ × (ℝ × ℝ) → ℝ := fun p => fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ)) with hD
  have hDd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D := hDG.clm_apply contDiff_const
  have hkey : ∀ s x, deriv (fun s' => η s' x) s = D (s, x) := by
    intro s x
    have hG' : HasFDerivAt G (fderiv ℝ G (s, x)) (s, x) := (hGdiff (s, x)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
    exact (hG'.comp_hasDerivAt s hline).deriv
  -- periodicity
  set a : ℝ × (ℝ × ℝ) := (0, (c, 0)) with ha
  have hGper : ∀ z, G (z + a) = G z := by
    intro z
    obtain ⟨s, x1, x2⟩ := z
    have := (hcyl s).periodic (x1, x2)
    simpa [hG, ha] using this
  have hDper : ∀ z, D (z + a) = D z := by
    intro z
    have h1 : (fun w => G (w + a)) = G := funext hGper
    have : fderiv ℝ G (z + a) = fderiv ℝ G z := by
      rw [← fderiv_comp_add_right, h1]
    simp [hD, this]
  have hPper : ∀ j z, ‖iteratedFDeriv ℝ j D (z + a)‖ = ‖iteratedFDeriv ℝ j D z‖ := by
    intro j z
    have h1 : (fun w => D (w + a)) = D := funext hDper
    rw [← iteratedFDeriv_comp_add_right, h1]
  -- vanishing outside the band
  have hPzero : ∀ j (q : ℝ × (ℝ × ℝ)), (q.1 < s₁ ∨ s₂ < q.1 ∨ R < |q.2.2|) →
      iteratedFDeriv ℝ j D q = 0 := by
    intro j q hq
    have hopen : IsOpen {q : ℝ × (ℝ × ℝ) | q.1 < s₁ ∨ s₂ < q.1 ∨ R < |q.2.2|} := by
      refine (isOpen_lt continuous_fst continuous_const).union ?_
      exact (isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd)))
    have hGz : G =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hq] with w hw
      exact hband w.1 w.2 hw
    have hDz : D =ᶠ[𝓝 q] fun _ => 0 := by
      have hf := hGz.fderiv_eq (𝕜 := ℝ)
      have hev : ∀ᶠ w in 𝓝 q, fderiv ℝ G w = 0 := by
        filter_upwards [hopen.mem_nhds hq] with w hw
        have : G =ᶠ[𝓝 w] fun _ => 0 := by
          filter_upwards [hopen.mem_nhds hw] with v hv
          exact hband v.1 v.2 hv
        rw [this.fderiv_eq]; simp
      filter_upwards [hev] with w hw
      simp [hD, hw]
    have := (hDz.iteratedFDeriv ℝ j).self_of_nhds
    rw [this]
    simp
  -- compact box bound
  have hbox : ∀ j, ∃ B : ℝ, ∀ q : ℝ × (ℝ × ℝ), ‖iteratedFDeriv ℝ j D q‖ ≤ B := by
    intro j
    have hcont : Continuous (fun q => ‖iteratedFDeriv ℝ j D q‖) :=
      (hDd.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have hK : IsCompact (Icc s₁ s₂ ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    obtain ⟨B, hB⟩ := (hK.bddAbove_image hcont.continuousOn)
    have hB' : ∀ q ∈ Icc s₁ s₂ ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R), ‖iteratedFDeriv ℝ j D q‖ ≤ B := by
      intro q hq; exact hB ⟨q, hq, rfl⟩
    refine ⟨max B 0, fun q => ?_⟩
    obtain ⟨s, u, v⟩ := q
    by_cases hout : s < s₁ ∨ s₂ < s ∨ R < |v|
    · rw [hPzero j (s, (u, v)) hout]; simp
    · push Not at hout
      obtain ⟨h1, h2, h3⟩ := hout
      have hv : v ∈ Icc (-R) R := abs_le.1 h3
      set n : ℤ := ⌊u / c⌋ with hn
      have hper : ∀ m : ℤ, ‖iteratedFDeriv ℝ j D (s, (u - m * c, v))‖
          = ‖iteratedFDeriv ℝ j D (s, (u, v))‖ := by
        intro m
        have hp : Function.Periodic (fun t : ℝ => ‖iteratedFDeriv ℝ j D (s, (t, v))‖) c := by
          intro t
          have := hPper j (s, (t, v))
          simpa [ha] using this
        exact hp.sub_int_mul_eq m
      have hu0 : 0 ≤ u - n * c := by
        have := Int.floor_le (u / c)
        rw [← hn] at this
        have := (le_div_iff₀ hc).1 this
        linarith
      have huc : u - n * c ≤ c := by
        have := Int.lt_floor_add_one (u / c)
        rw [← hn] at this
        have := (div_lt_iff₀ hc).1 this
        linarith
      have := hB' (s, (u - n * c, v)) ⟨⟨h1, h2⟩, ⟨hu0, huc⟩, hv⟩
      rw [← hper n]
      exact this.trans (le_max_left _ _)
  choose B hB using hbox
  refine ⟨∑ j ∈ Finset.range (k + 1), |B j|, fun s j hj x => ?_⟩
  have hfun : (fun x => deriv (fun s' => η s' x) s) =
      (fun p : ℝ × (ℝ × ℝ) => D (p + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    funext x; simp [hkey]
  have hDs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => D (p + (s, 0))) :=
    hDd.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hDs x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin j, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ (ℝ × ℝ))
  have h1 : ‖iteratedFDeriv ℝ j (fun p : ℝ × (ℝ × ℝ) => D (p + (s, 0))) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) x)‖ ≤ B j := by
    rw [iteratedFDeriv_comp_add_right]
    exact hB j _
  calc _ ≤ ‖iteratedFDeriv ℝ j (fun p : ℝ × (ℝ × ℝ) => D (p + (s, 0))) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ B j := by simpa using h1
    _ ≤ |B j| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun j => |B j|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
