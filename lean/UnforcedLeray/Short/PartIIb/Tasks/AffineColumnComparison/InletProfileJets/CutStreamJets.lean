import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.AgeCutoffJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.FrozenStreamJets

/-!
# Part II-b, task `PartII-b:G4/5/2/2/3` (`CutStreamJets`)

Source of record: `the November 2 reference manuscript`, lines 2347-2369, 2383-2385.
`cutStream i m = ageCutoff H m.1 * frozenStream i m.2`. The Leibniz rule
(`norm_iteratedFDeriv_mul_le`) splits the order-`l` derivative into a binomial sum of products of
the age-cutoff derivatives (bounded by `C_χ H⁻ᵃ`, `a ≤ l ≤ j`) and the frozen-stream derivatives
(bounded by `C c^N exp(-κ|η|/c)`). The binomial sum `∑ C(l,a) H⁻ᵃ = (1 + H⁻¹)^l ≤ (1 + H⁻¹)^j`
gives the claimed bound with no `2^l` loss.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-- Composition with a linear map of norm at most one does not increase the iterated derivative
norm (the `k`-th derivative of `f ∘ L` at `m` is the `k`-th derivative of `f` at `L m`
composed with `k` copies of `L`). -/
theorem cutJets_comp_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : G → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] G) (hL : ‖L‖ ≤ 1) (k : ℕ) (m : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) m‖ ≤ ‖iteratedFDeriv ℝ k f (L m)‖ := by
  rw [L.iteratedFDeriv_comp_right hf m (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin k, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hL
  calc _ ≤ ‖iteratedFDeriv ℝ k f (L m)‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := mul_one _

/-- The frozen streams are `C^∞` once the periodized eigenstream is (copy of `inletCD_frozenStream`). -/
theorem cutJets_frozenStream_cd {p : Params} {q : Planar.Profile}
    (hP : ContDiff ℝ ∞ (periodicStream q p.c)) (hmode : p.mode = q) (i : Fin 2) :
    ContDiff ℝ ∞ (p.frozenStream i) := by
  have hP' : ContDiff ℝ ∞ (periodicStream p.mode p.c) := by rw [hmode]; exact hP
  have hre : ContDiff ℝ ∞ (fun x => (periodicStream p.mode p.c x).re) :=
    Complex.reCLM.contDiff.comp hP'
  have him : ContDiff ℝ ∞ (fun x => (periodicStream p.mode p.c x).im) :=
    Complex.imCLM.contDiff.comp hP'
  fin_cases i
  · exact contDiff_const.mul hre
  · exact contDiff_const.mul him

theorem cutStreamJets : UnforcedLeray.Short.IIb.CutStreamJets := by
  intro lam q hq j
  obtain ⟨Cχ, hCχ, hχ⟩ := ageCutoffJets j
  obtain ⟨C, κ, N, hC, hκ, hfro⟩ := frozenStreamJets lam q hq j
  obtain ⟨_Cf, _κf, _Nf, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨Cχ * C, κ, N, mul_pos hCχ hC, hκ, ?_⟩
  intro p hmode hc1 hH i
  have hc0 : 0 ≤ p.c := by linarith
  have hHnn : 0 ≤ p.H⁻¹ := inv_nonneg.2 hH.le
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfroCD : ContDiff ℝ ∞ (p.frozenStream i) := cutJets_frozenStream_cd hP hmode i
  have h1 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => ageCutoff p.H m.1) :=
    (contDiff_ageCutoff p.H).comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => p.frozenStream i m.2) :=
    hfroCD.comp contDiff_snd
  have hbin : ∀ n : ℕ, (1 + p.H⁻¹) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p.H⁻¹ ^ k := by
    intro n
    rw [show (1 + p.H⁻¹ : ℝ) = p.H⁻¹ + 1 from add_comm _ _, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    simp only [one_pow, mul_one]
    ring
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => ageCutoff p.H m.1 * p.frozenStream i m.2)
    exact h1.mul h2
  · intro l hl m
    have hA : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (fun m : ℝ × (ℝ × ℝ) => ageCutoff p.H m.1) m‖ ≤
        Cχ * p.H⁻¹ ^ k := by
      intro k hk
      refine (cutJets_comp_le (contDiff_ageCutoff p.H) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)) k m).trans ?_
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hχ p.H hH k hk m.1
    have hB : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (fun m : ℝ × (ℝ × ℝ) => p.frozenStream i m.2) m‖ ≤
        C * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c)) := by
      intro k hk
      refine (cutJets_comp_le hfroCD (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
        (ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)) k m).trans ?_
      exact hfro p hmode hc1 i k hk m.2
    have hmul := norm_iteratedFDeriv_mul_le h1 h2 m (n := l) (by exact_mod_cast le_top)
    have hnn : 0 ≤ Cχ * C * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCχ.le hC.le) (pow_nonneg hc0 N)) (Real.exp_pos _).le
    refine hmul.trans ?_
    calc _ ≤ ∑ k ∈ Finset.range (l + 1), (l.choose k : ℝ) * (Cχ * p.H⁻¹ ^ k) *
          (C * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hchoose : (0 : ℝ) ≤ (l.choose k : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hA k (hk'.trans hl)) hchoose)
            (hB (l - k) ((Nat.sub_le l k).trans hl)) (norm_nonneg _)
            (mul_nonneg hchoose (mul_nonneg hCχ.le (pow_nonneg hHnn _)))
      _ = (Cχ * C * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c))) *
            ∑ k ∈ Finset.range (l + 1), (l.choose k : ℝ) * p.H⁻¹ ^ k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = (Cχ * C * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c))) * (1 + p.H⁻¹) ^ l := by
          rw [hbin l]
      _ ≤ (Cχ * C * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c))) * (1 + p.H⁻¹) ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right hHnn) hl) hnn
      _ = (Cχ * C) * (1 + p.H⁻¹) ^ j * p.c ^ N * Real.exp (-(κ * |m.2.2| / p.c)) := by
          ring

end UnforcedLeray.Short.IIb
