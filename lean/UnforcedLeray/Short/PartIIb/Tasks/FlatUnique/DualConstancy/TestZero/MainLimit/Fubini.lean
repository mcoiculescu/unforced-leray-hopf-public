import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_5

/-!
# Part II-b, leaf `PartII-b:T11/2/2/5/3` (Fubini identification `DualMainFubini`)

Source: `the November 2 reference manuscript` 1923-1927.

`ageμ c 0` is `(volume.restrict (Ioi 0)) ⊗ Cyl.avgμ c`.  Given integrability of `G`,
Fubini (`integral_prod`) writes `∫ G` as an iterated integral.  For each `σ`, the inner
integral over `p` equals `-χ'(σ) · dualF σ`: for `σ < s` the bridge `DualPerpBridge` turns
`perpC` of the cast of `H(s-·,·)` into `perpGrad`; for `σ ≥ s`, `χ' = 0` near `σ`
(`tsupport χ ⊆ Ioo 0 s`), so both sides vanish.  Finally the `σ`-integral over `Ioi 0` is
restricted to `Ioo 0 s`, the integrand vanishing outside it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dualMainFubini_proof : UnforcedLeray.Short.IIb.DualMainFubini := by
  intro h1 c r ν μ b H s χ hc hν hr hs hb hH hχ hI
  -- the age measure at exponent `0` is a product
  have hm : Axi.ageμ c 0 = (volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c) := by
    unfold Axi.ageμ
    simp only [Real.rpow_zero, ENNReal.ofReal_one, withDensity_const, one_smul]
  rw [hm] at hI ⊢
  -- `χ' = 0` at and beyond `s`
  have hz : ∀ σ : ℝ, s ≤ σ → deriv χ σ = 0 := by
    intro σ hσ
    have hnot : σ ∉ tsupport χ := fun h => absurd (mem_Ioo.1 (hχ.2.2 h)).2 (not_lt.2 hσ)
    have hev : χ =ᶠ[𝓝 σ] 0 := notMem_tsupport_iff_eventuallyEq.1 hnot
    rw [hev.deriv_eq]
    simp
  -- pointwise identity for `σ < s`
  have hpt : ∀ σ : ℝ, σ < s → ∀ p : ℝ × ℝ,
      pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) (σ, p) =
        (-(((σ : ℂ)) ^ μ * ((deriv χ σ : ℝ) : ℂ))) * ∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ) := by
    intro σ hσ p
    unfold pairC dualMain
    dsimp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 c ν (r / (r - 1)) H s hc hν hH (σ, p) i hσ]
    simp only [Complex.ofReal_one, one_mul]
    ring
  -- inner integral over the cell
  have hfib : ∀ σ : ℝ, ∫ p, pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) (σ, p)
        ∂(Cyl.avgμ c) = -((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ := by
    intro σ
    by_cases hσ : σ < s
    · simp only [hpt σ hσ]
      rw [integral_const_mul, dualF]
      ring
    · have hd : deriv χ σ = 0 := hz σ (not_lt.1 hσ)
      simp [pairC, dualMain, hd]
  -- Fubini on the product measure
  haveI hS : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have hF : ∫ x, pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c)) =
      ∫ σ in Ioi (0 : ℝ), ∫ p, pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) (σ, p)
        ∂(Cyl.avgμ c) :=
    integral_prod _ hI
  rw [hF]
  simp only [hfib, neg_mul, integral_neg]
  congr 1
  -- restrict `Ioi 0` to `Ioo 0 s`
  have hzero : ∀ σ ∈ Ioi (0 : ℝ) \ Ioo (0 : ℝ) s,
      ((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ = 0 := by
    intro σ hσ
    have hns : ¬ σ < s := fun h => hσ.2 (mem_Ioo.2 ⟨mem_Ioi.1 hσ.1, h⟩)
    have hd : deriv χ σ = 0 := hz σ (not_lt.1 hns)
    simp [hd]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioo_subset_Ioi_self hzero

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualMainFubini_proof
