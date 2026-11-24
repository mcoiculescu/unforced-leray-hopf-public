import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/7` leaf: `s`-differentiation of the lattice sum of `Ψ_A`

Source `the November 2 reference manuscript`
line 4978: the sum and its `s`-derivative converge by Gaussian decay. The matrix path `M(t)`
is `C¹` on `t > 0`; on `[s/2, 2s]` its value and `t ↦ t M'(t)` are bounded (compactness), and the
weight `t` of `𝒦` (`PsiTSBound`) gives the summable majorant `C' genvT`, `C' = 2K₅(K₁+K₂)/s`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiASTsum : PsiASTsum := by
  intro hD hV hS ν s hν hs hνs Mf hMf x
  obtain ⟨K3, hK3, B3⟩ := hV
  obtain ⟨K5, hK5, B5⟩ := hS
  have hJ : Icc (s / 2) (2 * s) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le (half_pos hs) ht.1
  have hdC : ContinuousOn (deriv Mf) (Icc (s / 2) (2 * s)) :=
    (hMf.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hJ
  have hC : ContinuousOn Mf (Icc (s / 2) (2 * s)) := hMf.continuousOn.mono hJ
  have hfrob : Continuous frob := by
    unfold frob
    fun_prop
  have hc1 : ContinuousOn (fun t : ℝ => frob (Mf t)) (Icc (s / 2) (2 * s)) :=
    hfrob.comp_continuousOn hC
  have hc2 : ContinuousOn (fun t : ℝ => frob (t • deriv Mf t)) (Icc (s / 2) (2 * s)) :=
    hfrob.comp_continuousOn (continuousOn_id.smul hdC)
  obtain ⟨K1, hK1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨K2, hK2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  have hK1' : ∀ t ∈ Icc (s / 2) (2 * s), frob (Mf t) ≤ K1 := fun t ht => by
    have h := hK1 t ht
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hK2' : ∀ t ∈ Icc (s / 2) (2 * s), frob (t • deriv Mf t) ≤ K2 := fun t ht => by
    have h := hK2 t ht
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  -- uniform bound of the `s`-derivative on `(s/2, 2s)`
  have hsum_bd : ∀ t ∈ Ioo (s / 2) (2 * s), ∀ j : ℤ,
      ‖psiTS ν t (Mf t) (deriv Mf t) (xj ν j x)‖
        ≤ 2 * K5 * (K1 + K2) / s * genvT (xj ν j x) := by
    intro t ht j
    have ht0 : 0 < t := lt_trans (half_pos hs) ht.1
    have hνt : ν * t ≤ 5 / 2 := by
      have : ν * t ≤ ν * (2 * s) := mul_le_mul_of_nonneg_left ht.2.le hν.le
      nlinarith
    have hB := B5 ν t hν ht0.le hνt (Mf t) (deriv Mf t) (xj ν j x)
    have hg := pdc_genvT_nonneg (xj ν j x)
    have hF : frob (Mf t) + frob (t • deriv Mf t) ≤ K1 + K2 :=
      add_le_add (hK1' t (Ioo_subset_Icc_self ht)) (hK2' t (Ioo_subset_Icc_self ht))
    have hbd : K5 * (frob (Mf t) + frob (t • deriv Mf t)) * genvT (xj ν j x)
        ≤ K5 * (K1 + K2) * genvT (xj ν j x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hK5) hg
    have hhalf : s / 2 * |psiTS ν t (Mf t) (deriv Mf t) (xj ν j x)| ≤
        t * |psiTS ν t (Mf t) (deriv Mf t) (xj ν j x)| :=
      mul_le_mul_of_nonneg_right ht.1.le (abs_nonneg _)
    rw [Real.norm_eq_abs, div_mul_eq_mul_div, le_div_iff₀ hs]
    linarith
  have hmem : s ∈ Ioo (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  have hu : Summable (fun j : ℤ => 2 * K5 * (K1 + K2) / s * genvT (xj ν j x)) :=
    (pdc_genv_summable hν x).mul_left _
  have hg0 : Summable (fun j : ℤ => psiT ν s (Mf s) (xj ν j x)) :=
    Summable.of_norm_bounded ((pdc_genv_summable hν x).mul_left (K3 * frob (Mf s)))
      (fun j => by
        rw [Real.norm_eq_abs]
        exact B3 ν s hν hs.le (by linarith) (Mf s) (xj ν j x))
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun (j : ℤ) (t : ℝ) => psiT ν t (Mf t) (xj ν j x))
    (g' := fun (j : ℤ) (t : ℝ) => psiTS ν t (Mf t) (deriv Mf t) (xj ν j x))
    (u := fun j : ℤ => 2 * K5 * (K1 + K2) / s * genvT (xj ν j x))
    (t := Ioo (s / 2) (2 * s)) hu isOpen_Ioo isPreconnected_Ioo
    (fun j t ht => by
      have ht0 : 0 < t := lt_trans (half_pos hs) ht.1
      have hdiff : HasDerivAt Mf (deriv Mf t) t :=
        ((hMf.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds ht0)).hasDerivAt
      exact hD ν Mf (deriv Mf t) t
        (lt_of_lt_of_le one_pos (pdc_ageA_ge_one hν.le ht0.le)) hdiff (xj ν j x))
    (fun j t ht => hsum_bd t ht j)
    hmem hg0 hmem
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
