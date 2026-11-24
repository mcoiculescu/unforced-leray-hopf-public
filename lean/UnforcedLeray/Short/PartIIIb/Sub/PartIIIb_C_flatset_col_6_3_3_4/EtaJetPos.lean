import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.PeriodicStripBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# `VtvEtaJet` for `c > 0` (source 270-288, 4610)

The jets of a stream test `η` are bounded on an age band.  The statement `VtvEtaJet` quantifies
over all `c : ℝ`; for `c = 0` periodicity is vacuous and e.g. `η s x = χ(s) ψ(x.2) x.1` is a stream
test with unbounded `η`, so the bound needs `0 < c` (the periods of the paper are `c ≥ 1`).
Here it is proved for `0 < c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem slice_norm_le (G : ℝ × (ℝ × ℝ) → ℝ) (hG : ContDiff ℝ ∞ G) (s : ℝ) (k : ℕ)
    (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => G (s, y)) x‖ ≤ ‖iteratedFDeriv ℝ k G (s, x)‖ := by
  set F : ℝ × (ℝ × ℝ) → ℝ := fun z => G (z + (s, 0)) with hFdef
  have hF : ContDiff ℝ ∞ F := hG.comp (contDiff_id.add contDiff_const)
  have hfun : (fun y : ℝ × ℝ => G (s, y)) = F ∘ (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    funext y; simp [hFdef]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hF x (by exact_mod_cast le_top)]
  have h1 : iteratedFDeriv ℝ k F (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) x) =
      iteratedFDeriv ℝ k G (s, x) := by
    rw [hFdef, iteratedFDeriv_comp_add_right]; simp
  rw [h1]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp [ContinuousLinearMap.norm_inr]

theorem vtvEtaJet_of_pos (c : ℝ) (hc : 0 < c) (η : ℝ → ℝ × ℝ → ℝ) (hη : IsStreamTest c η)
    (s₁ s₂ : ℝ) : ∃ K : ℝ, ∀ s ∈ Icc s₁ s₂,
    (∀ x j, |B0579.pd j (fun x => deriv (fun s' => η s' x) s) x| ≤ K) ∧
    (∀ x j, |B0579.pd j (η s) x| ≤ K) ∧
    (∀ x, ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (η s) x‖ ≤ K) := by
  obtain ⟨hsm, hcyl, a₁, a₂, R, _ha, hband⟩ := hη
  set G : ℝ × (ℝ × ℝ) → ℝ := fun p => η p.1 p.2 with hGdef
  have hG : ContDiff ℝ ∞ G := hsm
  have hGband : ∀ q : ℝ × (ℝ × ℝ), R < |q.2.2| → G q = 0 := fun q hq =>
    hband q.1 q.2 (Or.inr (Or.inr hq))
  have htsupp : tsupport G ⊆ {q : ℝ × (ℝ × ℝ) | |q.2.2| ≤ R} := by
    apply closure_minimal
    · intro q hq
      by_contra h
      exact hq (hGband q (not_le.1 h))
    · exact isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const
  have hbound : ∀ k : ℕ, ∃ Kk : ℝ, ∀ s ∈ Icc s₁ s₂, ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ k G (s, x)‖ ≤ Kk := by
    intro k
    have hcont : Continuous (fun q : ℝ × (ℝ × ℝ) => ‖iteratedFDeriv ℝ k G q‖) :=
      (hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have hper : ∀ (s : ℝ) (x : ℝ × ℝ), ‖iteratedFDeriv ℝ k G (s, (x.1 + c, x.2))‖ =
        ‖iteratedFDeriv ℝ k G (s, x)‖ := by
      intro s x
      have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := G) k ((0, (c, 0)) : ℝ × (ℝ × ℝ))
        (s, x)
      have hfe : (fun z : ℝ × (ℝ × ℝ) => G (z + (0, (c, 0)))) = G := by
        funext z
        have hz : z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (z.1, (z.2.1 + c, z.2.2)) := by
          ext <;> simp
        rw [hz]
        exact (hcyl z.1).periodic z.2
      rw [hfe] at h
      have hpt : ((s, x) : ℝ × (ℝ × ℝ)) + (0, (c, 0)) = (s, (x.1 + c, x.2)) := by
        ext <;> simp
      rw [hpt] at h
      rw [h]
    have hbd : ∀ (s : ℝ) (x : ℝ × ℝ), R < |x.2| → ‖iteratedFDeriv ℝ k G (s, x)‖ = 0 := by
      intro s x hx
      by_contra hne
      have h1 : (s, x) ∈ Function.support (iteratedFDeriv ℝ k G) := by
        intro h0
        apply hne
        simp [h0]
      have := htsupp (support_iteratedFDeriv_subset k h1)
      simp only [Set.mem_ofPred_eq] at this
      linarith
    obtain ⟨Kk, hKk⟩ := periodic_strip_bound hcont hc hper hbd s₁ s₂
    exact ⟨Kk, fun s hs x => by simpa using hKk s hs x⟩
  choose Kf hKf using hbound
  have hdir : ∀ j : Fin 2, ‖B0579.dir j‖ ≤ 1 := by
    intro j; fin_cases j <;> simp [B0579.dir]
  refine ⟨max (max (Kf 0) (Kf 1)) (max (Kf 2) (Kf 3)), fun s hs => ?_⟩
  have hKk : ∀ k : ℕ, k ≤ 3 → ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ k (η s) x‖ ≤
      max (max (Kf 0) (Kf 1)) (max (Kf 2) (Kf 3)) := by
    intro k hk x
    have h := (slice_norm_le G hG s k x).trans (hKf k s hs x)
    refine h.trans ?_
    interval_cases k <;> simp
  have hGs : (fun y => G (s, y)) = η s := rfl
  refine ⟨?_, ?_, fun x k hk => hKk k hk x⟩
  · intro x j
    have hGdiff : Differentiable ℝ G := hG.differentiable (by simp)
    have hDG : ContDiff ℝ ∞ (fderiv ℝ G) := (contDiff_infty_iff_fderiv.1 hG).2
    have hkey : ∀ y : ℝ × ℝ, deriv (fun s' => η s' y) s =
        fderiv ℝ G (s, y) ((1 : ℝ), (0 : ℝ × ℝ)) := by
      intro y
      have hG' : HasFDerivAt G (fderiv ℝ G (s, y)) (s, y) := (hGdiff (s, y)).hasFDerivAt
      have hline : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
        (hasDerivAt_id' s).prodMk (hasDerivAt_const s y)
      exact (hG'.comp_hasDerivAt s hline).deriv
    have hfun : (fun y : ℝ × ℝ => deriv (fun s' => η s' y) s) =
        (fun y => (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) (s, y)) :=
      funext hkey
    have hh : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) :=
      hDG.clm_apply contDiff_const
    have hpair : Differentiable ℝ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) :=
      (differentiable_const s).prodMk differentiable_id
    have hhd : Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) =>
        fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) := hh.differentiable (by simp)
    unfold B0579.pd
    rw [hfun]
    have hcomp : HasFDerivAt (fun y : ℝ × ℝ => (fun p : ℝ × (ℝ × ℝ) =>
        fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) (s, y))
        ((fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) (s, x)).comp
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := by
      have hpr : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ)))
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x := by
        have h0 := (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
        have h00 : ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) =
            ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) :=
          ContinuousLinearMap.ext fun y => by simp
        rw [h00] at h0
        exact h0
      exact (hhd (s, x)).hasFDerivAt.comp x hpr
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    have hD : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ))) (s, x) =
        (fderiv ℝ (fderiv ℝ G) (s, x)).flip ((1 : ℝ), (0 : ℝ × ℝ)) := by
      rw [fderiv_clm_apply (hDG.differentiable (by simp) _) (differentiableAt_const _)]
      simp
    rw [hD]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.inr_apply]
    have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) G (s, x)
      (![((0 : ℝ), B0579.dir j), ((1 : ℝ), (0 : ℝ × ℝ))] : Fin 2 → ℝ × (ℝ × ℝ))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    rw [← h2]
    have hle := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ 2 G (s, x))
      (![((0 : ℝ), B0579.dir j), ((1 : ℝ), (0 : ℝ × ℝ))] : Fin 2 → ℝ × (ℝ × ℝ))
    rw [Fin.prod_univ_two] at hle
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hle
    have hn0 : ‖((0 : ℝ), B0579.dir j)‖ ≤ 1 := by
      rw [Prod.norm_def]; simpa using hdir j
    have hn1 : ‖((1 : ℝ), (0 : ℝ × ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
    have hmul : ‖((0 : ℝ), B0579.dir j)‖ * ‖((1 : ℝ), (0 : ℝ × ℝ))‖ ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul hn0 hn1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hnn := norm_nonneg (iteratedFDeriv ℝ 2 G (s, x))
    have h3 : ‖iteratedFDeriv ℝ 2 G (s, x)‖ * (‖((0 : ℝ), B0579.dir j)‖ *
        ‖((1 : ℝ), (0 : ℝ × ℝ))‖) ≤ ‖iteratedFDeriv ℝ 2 G (s, x)‖ :=
      mul_le_of_le_one_right hnn hmul
    have h4 : |iteratedFDeriv ℝ 2 G (s, x) ![((0 : ℝ), B0579.dir j), ((1 : ℝ), (0 : ℝ × ℝ))]| ≤
        ‖iteratedFDeriv ℝ 2 G (s, x)‖ := by
      rw [← Real.norm_eq_abs]; exact hle.trans h3
    refine h4.trans ((hKf 2 s hs x).trans ?_)
    simp
  · intro x j
    unfold B0579.pd
    have h1 : |fderiv ℝ (η s) x (B0579.dir j)| ≤ ‖fderiv ℝ (η s) x‖ := by
      rw [← Real.norm_eq_abs]
      exact (((fderiv ℝ (η s) x).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hdir j)))
    refine h1.trans ?_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact hKk 1 (by norm_num) x

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
