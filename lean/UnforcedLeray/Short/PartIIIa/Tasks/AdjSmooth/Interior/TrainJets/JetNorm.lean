import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Words along `List.ofFn` are iterated derivatives within `tjU` in the coordinate directions. -/
theorem tjW_ofFn_eq_iterated {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ × (ℝ × ℝ) → F) (hh : ContDiffOn ℝ ∞ h tjU) (n : ℕ) :
    ∀ (L : Fin n → Fin 3) (p : ℝ × (ℝ × ℝ)), p ∈ tjU →
      tjW (List.ofFn L) h p = iteratedFDerivWithin ℝ n h tjU p (fun i => stDir (L i)) := by
  induction n with
  | zero =>
    intro L p _
    rfl
  | succ n ih =>
    intro L p hp
    rw [List.ofFn_succ]
    show fderivWithin ℝ (tjW (List.ofFn fun i => L i.succ) h) tjU p (stDir (L 0)) = _
    have e : fderivWithin ℝ (tjW (List.ofFn fun i => L i.succ) h) tjU p =
        fderivWithin ℝ (fun q => iteratedFDerivWithin ℝ n h tjU q (fun i => stDir (L i.succ)))
          tjU p :=
      fderivWithin_congr (fun q hq => ih (fun i => L i.succ) q hq) (ih (fun i => L i.succ) p hp)
    have hc : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ n h tjU) tjU p :=
      hh.differentiableOn_iteratedFDerivWithin (m := n) (by exact_mod_cast ENat.natCast_lt_top n) (uniqueDiffOn_tjU) p hp
    rw [e, fderivWithin_continuousMultilinear_apply_const_apply (uniqueDiffOn_tjU p hp) hc]
    rfl

/-- Operator-norm bound of a multilinear map on `ℝ × (ℝ × ℝ)` by its values on the coordinate
words: `‖D‖ ≤ Σ_{L : Fin n → Fin 3} ‖D (stDir ∘ L)‖`. -/
theorem tjJetMultilinear_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (ℝ × ℝ)) F) :
    ‖D‖ ≤ ∑ L : Fin n → Fin 3, ‖D (fun i => stDir (L i))‖ := by
  set c : Fin 3 → ℝ × (ℝ × ℝ) → ℝ := fun j y => ![y.1, y.2.1, y.2.2] j with hcdef
  have hexp : ∀ y : ℝ × (ℝ × ℝ), y = ∑ j : Fin 3, c j y • stDir j := by
    intro y
    ext <;> simp [hcdef, stDir, Fin.sum_univ_three]
  have hc : ∀ (j : Fin 3) (y : ℝ × (ℝ × ℝ)), ‖c j y‖ ≤ ‖y‖ := by
    intro j y
    fin_cases j
    · exact norm_fst_le y
    · exact (norm_fst_le y.2).trans (norm_snd_le y)
    · exact (norm_snd_le y.2).trans (norm_snd_le y)
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun L _ => norm_nonneg _)
  intro m
  have hD : D m = ∑ r : Fin n → Fin 3, (∏ i, c (r i) (m i)) • D (fun i => stDir (r i)) := by
    have hm : m = fun i => ∑ j : Fin 3, c j (m i) • stDir j := funext fun i => hexp (m i)
    conv_lhs => rw [hm]
    rw [ContinuousMultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun r _ =>
      ContinuousMultilinearMap.map_smul_univ D (fun i => c (r i) (m i)) (fun i => stDir (r i))
  calc ‖D m‖ = ‖∑ r : Fin n → Fin 3, (∏ i, c (r i) (m i)) • D (fun i => stDir (r i))‖ := by
        rw [hD]
    _ ≤ ∑ r : Fin n → Fin 3, ‖(∏ i, c (r i) (m i)) • D (fun i => stDir (r i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin n → Fin 3, (∏ i, ‖m i‖) * ‖D (fun i => stDir (r i))‖ := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_smul, norm_prod]
        exact mul_le_mul_of_nonneg_right
          (Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hc _ _) (norm_nonneg _)
    _ = (∑ r : Fin n → Fin 3, ‖D (fun i => stDir (r i))‖) * ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- **The jet norm by the coordinate words** (calculus): for a field `C^∞` on `tjU` and `p ∈ tjU`,
`‖D^n h(p)‖ ≤ K Σ_{|L| = n} ‖tjW L h p‖` (`D^n` within `tjU`). (Induction with
`iteratedFDerivWithin_succ_apply_left`, `fderivWithin_congr` on `tjU` and the derivative of the
evaluation at fixed vectors: `tjW (List.ofFn L) h p = iteratedFDerivWithin ℝ n h tjU p (stDir ∘ L)`;
then expand every argument in the basis `stDir` (coordinates bounded by the sup norm of
`ℝ × (ℝ × ℝ)`) by multilinearity, `ContinuousMultilinearMap.opNorm_le_bound`. `K = 1` works.) -/
theorem tjJetNorm : TjJetNorm := by
  intro n
  refine ⟨1, zero_le_one, ?_⟩
  intro F _ _ h hh p hp
  have hb := tjJetMultilinear_norm n (iteratedFDerivWithin ℝ n h tjU p)
  calc ‖iteratedFDerivWithin ℝ n h tjU p‖
      ≤ ∑ L : Fin n → Fin 3, ‖iteratedFDerivWithin ℝ n h tjU p (fun i => stDir (L i))‖ := hb
    _ = ∑ L : Fin n → Fin 3, ‖tjW (List.ofFn L) h p‖ :=
        Finset.sum_congr rfl fun L _ => by rw [tjW_ofFn_eq_iterated h hh n L p hp]
    _ = 1 * ∑ L : Fin n → Fin 3, ‖tjW (List.ofFn L) h p‖ := (one_mul _).symm

end UnforcedLeray.Short.IIIa
