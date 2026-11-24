import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/1`: the dilation chain rule `DilJetBound`

Source of record: `the November 2 reference manuscript` 5464-5465 (`σ = log s`).
Route: `norm_iteratedFDeriv_comp_le'` for `G ∘ φ`, `φ z = (exp z.1, z.2)`, with the inner
derivative bound `‖D^n φ‖ ≤ exp z.1 + 1` for `n ≥ 1` (product norm of the two components,
`iteratedFDeriv_prodMk`, `ContinuousMultilinearMap.opNorm_prod`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `n`-th derivative of `z ↦ exp z.1` is bounded by `exp z.1` (`exp ∘ fst`, `‖fst‖ ≤ 1`). -/
theorem dil_exp_fst_iter (n : ℕ) (z : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ × (ℝ × ℝ) => Real.exp w.1) z‖ ≤ Real.exp z.1 := by
  have e : (fun w : ℝ × (ℝ × ℝ) => Real.exp w.1) =
      Real.exp ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := rfl
  have hn : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ Real.contDiff_exp z hn]
  have hexp : ‖iteratedFDeriv ℝ n Real.exp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) z)‖ =
      Real.exp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) z) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hprod : ∏ _i : Fin n, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ))
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hm := mul_le_mul (le_of_eq hexp) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Real.exp_pos _).le
  calc _ ≤ Real.exp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) z) * 1 := hm
    _ = Real.exp z.1 := by rw [mul_one]; rfl

/-- The `n`-th derivative of the projection `z ↦ z.2` (`n ≥ 1`) is bounded by `1`. -/
theorem dil_snd_iter (n : ℕ) (hn : 1 ≤ n) (z : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ × (ℝ × ℝ) => w.2) z‖ ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : fderiv ℝ (fun w : ℝ × (ℝ × ℝ) => w.2) =
      fun _ => ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) := by
    funext w
    exact fderiv_snd
  rw [hfd]
  rcases m with _ | k
  · rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  · rw [iteratedFDeriv_succ_const]
    simp

/-- The `n`-th derivative of `φ z = (exp z.1, z.2)` (`n ≥ 1`) is bounded by `exp z.1 + 1`. -/
theorem dil_phi_iter (n : ℕ) (hn : 1 ≤ n) (z : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ × (ℝ × ℝ) => (Real.exp w.1, w.2)) z‖ ≤ Real.exp z.1 + 1 := by
  have hf : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × ℝ) => Real.exp w.1) :=
    Real.contDiff_exp.comp contDiff_fst
  have hg : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × ℝ) => w.2) := contDiff_snd
  have hfA : ContDiffAt ℝ ∞ (fun w : ℝ × (ℝ × ℝ) => Real.exp w.1) z := hf.contDiffAt
  have hgA : ContDiffAt ℝ ∞ (fun w : ℝ × (ℝ × ℝ) => w.2) z := hg.contDiffAt
  have hi : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have key : iteratedFDeriv ℝ n (fun w : ℝ × (ℝ × ℝ) => (Real.exp w.1, w.2)) z =
      (iteratedFDeriv ℝ n (fun w : ℝ × (ℝ × ℝ) => Real.exp w.1) z).prod
        (iteratedFDeriv ℝ n (fun w : ℝ × (ℝ × ℝ) => w.2) z) :=
    iteratedFDeriv_prodMk hfA hgA hi
  rw [key, ContinuousMultilinearMap.opNorm_prod]
  have h1 := dil_exp_fst_iter n z
  have h2 := dil_snd_iter n hn z
  have he := Real.exp_pos z.1
  exact max_le (by linarith) (by linarith)

/-- **(A1) The dilation chain rule** (source 5464-5465: the chart derivatives are taken in
`σ = log s`, `∂_σ = s∂_s`).  For `G` jointly `C^∞` on `(0,∞) × ℝ²`,
`‖D^j_{(σ,x)} G(e^σ, x)‖ ≤ j! (Σ_{i≤j} ‖D^i G(s,x)‖) (1+s)^j` at `σ = log s`. -/
theorem dilJetBound : DilJetBound := by
  unfold DilJetBound
  intro E _ _ G hG j s hs x
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmemG : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hs, Set.mem_univ _⟩
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i G (Ioi 0 ×ˢ univ)
      (Real.exp (Real.log s), x)‖ ≤ ∑ k ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ k G (s, x)‖ := by
    intro i hi
    rw [Real.exp_log hs, iteratedFDerivWithin_of_isOpen i hopen hmemG]
    exact Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k G (s, x)‖)
      (fun k _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hD : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i (fun w : ℝ × (ℝ × ℝ) => (Real.exp w.1, w.2)) (Real.log s, x)‖ ≤
        (1 + s) ^ i := by
    intro i hi1 _hij
    refine (dil_phi_iter i hi1 (Real.log s, x)).trans ?_
    show Real.exp (Real.log s) + 1 ≤ (1 + s) ^ i
    rw [Real.exp_log hs]
    have h1 : (1 : ℝ) ≤ 1 + s := by linarith
    calc s + 1 = (1 + s) ^ 1 := by ring
      _ ≤ (1 + s) ^ i := pow_le_pow_right₀ h1 hi1
  have ht : Set.range (fun w : ℝ × (ℝ × ℝ) => (Real.exp w.1, w.2)) ⊆
      Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨Real.exp_pos _, Set.mem_univ _⟩
  have hf : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × ℝ) => (Real.exp w.1, w.2)) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk contDiff_snd
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  exact norm_iteratedFDeriv_comp_le' (C := ∑ k ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ k G (s, x)‖)
    (D := 1 + s) ht hopen.uniqueDiffOn hG hf hn (Real.log s, x) hC hD

end UnforcedLeray.Short.PartIIIb.Concrete
