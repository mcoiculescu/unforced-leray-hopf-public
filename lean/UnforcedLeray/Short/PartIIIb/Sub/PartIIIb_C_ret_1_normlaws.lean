import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_closure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `PartIII-b:C/ret/1` norm laws for `affNorm` on `𝒜` (source line 4750)

Proves `AffNormLaws as` from `AffClosure as`: triangle inequality, absolute homogeneity and
definiteness of `affNorm as` on elements of `𝒜`.  The helper lemmas (`affTerm_add_le_aux`,
`sdi_smul_aux`, `frob_smul_aux`, `isAffElem_smul_aux`) come from the closure file.
-/

set_option autoImplicit false

noncomputable section

open Set Real Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem affNormLaws (as : ℝ) (h : AffClosure as) : AffNormLaws as := by
  have hne : (Ioi (0 : ℝ)).Nonempty := ⟨1, by simp⟩
  refine ⟨fun A B hA hB => ?_, fun c A hA => ?_, fun A hA h0 => ?_⟩
  · -- triangle inequality
    unfold affNorm
    apply csSup_le (hne.image (affTerm as 6 (A + B)))
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (0 : ℝ) < s := hs
    have hmA : affTerm as 6 A s ∈ affTerm as 6 A '' Ioi 0 := ⟨s, hs, rfl⟩
    have hmB : affTerm as 6 B s ∈ affTerm as 6 B '' Ioi 0 := ⟨s, hs, rfl⟩
    calc affTerm as 6 (A + B) s
        ≤ affTerm as 6 A s + affTerm as 6 B s :=
          affTerm_add_le_aux as A B hA.smooth hB.smooth s hs'
      _ ≤ sSup (affTerm as 6 A '' Ioi 0) + sSup (affTerm as 6 B '' Ioi 0) :=
          add_le_add (le_csSup hA.bdd hmA) (le_csSup hB.bdd hmB)
  · -- absolute homogeneity
    have key : ∀ s, 0 < s → affTerm as 6 (c • A) s = |c| * affTerm as 6 A s := by
      intro s hs
      unfold affTerm affSum
      have hsum : ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (c • A) s)
          = |c| * ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j A s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj6 : j ≤ 6 := by
          rw [Finset.mem_range] at hj
          omega
        rw [sdi_smul_aux c A hA.smooth j hj6 s hs, frob_smul_aux]
      rw [hsum]
      ring
    have hcA : IsAffElem as (c • A) := isAffElem_smul_aux as c A hA
    have hne1 : (affTerm as 6 (c • A) '' Ioi 0).Nonempty := hne.image (affTerm as 6 (c • A))
    have hne2 : (affTerm as 6 A '' Ioi 0).Nonempty := hne.image (affTerm as 6 A)
    have hup : affNorm as (c • A) ≤ |c| * affNorm as A := by
      unfold affNorm
      apply csSup_le hne1
      rintro _ ⟨s, hs, rfl⟩
      have hs' : (0 : ℝ) < s := hs
      have hmA : affTerm as 6 A s ∈ affTerm as 6 A '' Ioi 0 := ⟨s, hs, rfl⟩
      rw [key s hs']
      exact mul_le_mul_of_nonneg_left (le_csSup hA.bdd hmA) (abs_nonneg c)
    have hdown : |c| * affNorm as A ≤ affNorm as (c • A) := by
      rcases eq_or_ne c 0 with hc | hc
      · have h0nn : 0 ≤ affNorm as (c • A) := affNorm_nonneg_of as _ hcA
        rw [abs_eq_zero.mpr hc, zero_mul]
        exact h0nn
      · have hpos : 0 < |c| := abs_pos.mpr hc
        have hY : affNorm as A ≤ affNorm as (c • A) / |c| := by
          unfold affNorm
          apply csSup_le hne2
          rintro _ ⟨s, hs, rfl⟩
          have hs' : (0 : ℝ) < s := hs
          have hmc : affTerm as 6 (c • A) s ∈ affTerm as 6 (c • A) '' Ioi 0 := ⟨s, hs, rfl⟩
          have h1 : |c| * affTerm as 6 A s ≤ sSup (affTerm as 6 (c • A) '' Ioi 0) := by
            rw [← key s hs']
            exact le_csSup hcA.bdd hmc
          rw [le_div_iff₀ hpos]
          linarith [mul_comm (affTerm as 6 A s) |c|]
        rw [le_div_iff₀ hpos] at hY
        linarith [mul_comm (affNorm as A) |c|]
    exact le_antisymm hup hdown
  · -- definiteness
    unfold affNorm at h0
    have hpt : ∀ s, 0 < s → A s = 0 := by
      intro s hs
      have hmem : affTerm as 6 A s ∈ affTerm as 6 A '' Ioi 0 := ⟨s, hs, rfl⟩
      have hle : affTerm as 6 A s ≤ 0 := by
        have := le_csSup hA.bdd hmem
        linarith
      have hw : 0 < Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) :=
        mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _)
      have hnn : ∀ j ∈ Finset.range (6 + 1), 0 ≤ frob (sDerivIter j A s) :=
        fun j _ => by unfold frob; exact Real.sqrt_nonneg _
      have hge : 0 ≤ affTerm as 6 A s := by
        unfold affTerm affSum
        exact mul_nonneg hw.le (Finset.sum_nonneg hnn)
      have hT : affTerm as 6 A s = 0 := le_antisymm hle hge
      have hS : affSum 6 A s = 0 := by
        unfold affTerm at hT
        rcases mul_eq_zero.mp hT with h1 | h1
        · exact absurd h1 hw.ne'
        · exact h1
      have hzero : frob (sDerivIter 0 A s) = 0 := by
        unfold affSum at hS
        exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS 0 (by simp)
      have h0'' : frob (A s) = 0 := by
        simpa [sDerivIter] using hzero
      have hsq : ∑ i, ∑ j, A s i j ^ 2 = 0 := by
        have hnn2 : 0 ≤ ∑ i, ∑ j, A s i j ^ 2 :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
        unfold frob at h0''
        exact le_antisymm (Real.sqrt_eq_zero'.mp h0'') hnn2
      have hrow : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ∑ j, A s i j ^ 2 :=
        fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      funext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hrow).mp hsq i (Finset.mem_univ i)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A s i j))).mp hi
        j (Finset.mem_univ j)
      simpa using hj
    have hfun : A = 0 := by
      funext s
      rcases le_or_gt s 0 with hs | hs
      · exact hA.zeroOff s hs
      · exact hpt s hs
    exact hfun

end UnforcedLeray.Short.PartIIIb.Concrete
