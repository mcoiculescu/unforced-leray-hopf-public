import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt

/-!
# `PartIII-b:C/ret/1` closure of `𝒜` (source lines 4741-4745)

Proves `AffClosure as`: the zero function lies in `𝒜`, and `𝒜` is closed under sums and scalar
multiples.  The derivative operators `(s ∂_s)^j` are linear on `(0,∞)` for `C^6` data
(`sDerivIter` is differentiated only at points of the open set `Ioi 0`), and the weighted norm
satisfies the triangle inequality and absolute homogeneity for the Frobenius norm.
-/

set_option autoImplicit false

noncomputable section

open Set Real Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Frobenius norm facts -/

lemma frob_smul_aux (c : ℝ) (X : Mat3) : frob (c • X) = |c| * frob X := by
  unfold frob
  have h : ∑ i, ∑ j, (c • X) i j ^ 2 = c ^ 2 * ∑ i, ∑ j, X i j ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma sqrt_sum_add_le_aux {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    Real.sqrt (∑ i, (u i + v i) ^ 2) ≤ Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2) := by
  have hu : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) u v
  have hexp : ∑ i, (u i + v i) ^ 2
      = (∑ i, u i ^ 2) + 2 * (∑ i, u i * v i) + (∑ i, v i ^ 2) := by
    have h1 : ∀ i, (u i + v i) ^ 2 = u i ^ 2 + 2 * (u i * v i) + v i ^ 2 := fun i => by ring
    simp only [h1, Finset.sum_add_distrib, Finset.mul_sum]
  have hab : 0 ≤ Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (∑ i, (u i + v i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hexp]
        nlinarith [hcs, Real.sq_sqrt hu, Real.sq_sqrt hv]
    _ = Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2) := Real.sqrt_sq hab

lemma frob_add_le_aux (X Y : Mat3) : frob (X + Y) ≤ frob X + frob Y := by
  have h := sqrt_sum_add_le_aux (fun p : Fin 3 × Fin 3 => X p.1 p.2) (fun p => Y p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  unfold frob
  simpa [Pi.add_apply] using h

/-! ## Smoothness and linearity of `(s ∂_s)^j` on `(0,∞)` -/

lemma sDeriv_contDiffOn_aux (n : ℕ) (A : ℝ → Mat3)
    (hA : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) A (Ioi 0)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (sDeriv A) (Ioi 0) := by
  have hd : ContDiffOn ℝ (n : WithTop ℕ∞) (deriv A) (Ioi 0) :=
    ContDiffOn.deriv_of_isOpen hA isOpen_Ioi (by norm_cast)
  have e : sDeriv A = fun s => s • deriv A s := rfl
  rw [e]
  exact contDiffOn_id.smul hd

lemma sdi_contDiff_aux (j : ℕ) : ∀ (n : ℕ) (A : ℝ → Mat3),
    ContDiffOn ℝ ((n + j : ℕ) : WithTop ℕ∞) A (Ioi 0) →
    ContDiffOn ℝ (n : WithTop ℕ∞) (sDerivIter j A) (Ioi 0) := by
  induction j with
  | zero =>
    intro n A hA
    simpa [sDerivIter] using hA
  | succ j ih =>
    intro n A hA
    have hA' : ContDiffOn ℝ (((n + 1) + j : ℕ) : WithTop ℕ∞) A (Ioi 0) := by
      have e : n + 1 + j = n + (j + 1) := by omega
      rw [e]
      exact hA
    have h1 := ih (n + 1) A hA'
    show ContDiffOn ℝ (n : WithTop ℕ∞) (sDeriv (sDerivIter j A)) (Ioi 0)
    exact sDeriv_contDiffOn_aux n _ h1

lemma sdi_diff_aux (A : ℝ → Mat3) (hA : ContDiffOn ℝ 6 A (Ioi 0)) (j : ℕ) (hj : j ≤ 5) :
    DifferentiableOn ℝ (sDerivIter j A) (Ioi 0) := by
  have h6 : ContDiffOn ℝ ((1 + j : ℕ) : WithTop ℕ∞) A (Ioi 0) := by
    apply hA.of_le
    exact_mod_cast (by omega : 1 + j ≤ 6)
  have h := sdi_contDiff_aux j 1 A h6
  exact h.differentiableOn (by norm_num)

lemma sdi_add_aux (A B : ℝ → Mat3) (hA : ContDiffOn ℝ 6 A (Ioi 0))
    (hB : ContDiffOn ℝ 6 B (Ioi 0)) :
    ∀ j, j ≤ 6 → ∀ s, 0 < s → sDerivIter j (A + B) s = sDerivIter j A s + sDerivIter j B s := by
  intro j
  induction j with
  | zero => intro _ s _; rfl
  | succ j ih =>
    intro hj s hs
    have hev : sDerivIter j (A + B) =ᶠ[𝓝 s] (sDerivIter j A + sDerivIter j B) := by
      filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs)] with t ht
      exact ih (by omega) t (Set.mem_Ioi.mp ht)
    have hdA : DifferentiableAt ℝ (sDerivIter j A) s :=
      (sdi_diff_aux A hA j (by omega)).differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs))
    have hdB : DifferentiableAt ℝ (sDerivIter j B) s :=
      (sdi_diff_aux B hB j (by omega)).differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs))
    have hsum : deriv (sDerivIter j A + sDerivIter j B) s
        = deriv (sDerivIter j A) s + deriv (sDerivIter j B) s := deriv_add hdA hdB
    show s • deriv (sDerivIter j (A + B)) s
      = s • deriv (sDerivIter j A) s + s • deriv (sDerivIter j B) s
    rw [hev.deriv_eq, hsum, smul_add]

lemma sdi_smul_aux (c : ℝ) (A : ℝ → Mat3) (hA : ContDiffOn ℝ 6 A (Ioi 0)) :
    ∀ j, j ≤ 6 → ∀ s, 0 < s → sDerivIter j (c • A) s = c • sDerivIter j A s := by
  intro j
  induction j with
  | zero => intro _ s _; rfl
  | succ j ih =>
    intro hj s hs
    have hev : sDerivIter j (c • A) =ᶠ[𝓝 s] (c • sDerivIter j A) := by
      filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs)] with t ht
      exact ih (by omega) t (Set.mem_Ioi.mp ht)
    have hdA : DifferentiableAt ℝ (sDerivIter j A) s :=
      (sdi_diff_aux A hA j (by omega)).differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs))
    have hsm : deriv (c • sDerivIter j A) s = c • deriv (sDerivIter j A) s :=
      deriv_const_smul c hdA
    show s • deriv (sDerivIter j (c • A)) s = c • (s • deriv (sDerivIter j A) s)
    rw [hev.deriv_eq, hsm, smul_comm]

lemma sdi_zero_aux (j : ℕ) : sDerivIter j (0 : ℝ → Mat3) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext s
    have hd : deriv (sDerivIter j (0 : ℝ → Mat3)) s = 0 := by
      rw [ih]
      exact deriv_const s (0 : Mat3)
    show s • deriv (sDerivIter j (0 : ℝ → Mat3)) s = (0 : Mat3)
    rw [hd, smul_zero]

/-! ## The three closure facts -/

lemma affTerm_zero_aux (as s : ℝ) : affTerm as 6 (0 : ℝ → Mat3) s = 0 := by
  unfold affTerm affSum
  simp [sdi_zero_aux, frob]

lemma affTerm_add_le_aux (as : ℝ) (A B : ℝ → Mat3) (hA : ContDiffOn ℝ 6 A (Ioi 0))
    (hB : ContDiffOn ℝ 6 B (Ioi 0)) (s : ℝ) (hs : 0 < s) :
    affTerm as 6 (A + B) s ≤ affTerm as 6 A s + affTerm as 6 B s := by
  have hw : 0 ≤ Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.le _)
  have hS : ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (A + B) s)
      ≤ ∑ j ∈ Finset.range (6 + 1), (frob (sDerivIter j A s) + frob (sDerivIter j B s)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj6 : j ≤ 6 := by
      rw [Finset.mem_range] at hj
      omega
    rw [sdi_add_aux A B hA hB j hj6 s hs]
    exact frob_add_le_aux _ _
  rw [Finset.sum_add_distrib] at hS
  have hm := mul_le_mul_of_nonneg_left hS hw
  unfold affTerm affSum
  rw [mul_add] at hm
  exact hm

lemma isAffElem_zero_aux (as : ℝ) : IsAffElem as 0 where
  smooth := contDiffOn_const
  traceFree := fun _ _ => by simp
  noMixedAzimuth := fun _ _ => by simp
  zeroOff := fun _ _ => rfl
  bdd := ⟨0, by
    rintro _ ⟨s, _, rfl⟩
    rw [affTerm_zero_aux]⟩

lemma isAffElem_add_aux (as : ℝ) (A B : ℝ → Mat3) (hA : IsAffElem as A)
    (hB : IsAffElem as B) : IsAffElem as (A + B) where
  smooth := ContDiffOn.add hA.smooth hB.smooth
  traceFree := fun s hs => by
    have h1 := hA.traceFree s hs
    have h2 := hB.traceFree s hs
    simp only [Pi.add_apply]
    linear_combination h1 + h2
  noMixedAzimuth := fun s hs => by
    obtain ⟨a1, a2, a3, a4⟩ := hA.noMixedAzimuth s hs
    obtain ⟨b1, b2, b3, b4⟩ := hB.noMixedAzimuth s hs
    simp [a1, a2, a3, a4, b1, b2, b3, b4]
  zeroOff := fun s hs => by simp [hA.zeroOff s hs, hB.zeroOff s hs]
  bdd := by
    obtain ⟨MA, hMA⟩ := hA.bdd
    obtain ⟨MB, hMB⟩ := hB.bdd
    refine ⟨MA + MB, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs' : 0 < s := Set.mem_Ioi.mp hs
    calc affTerm as 6 (A + B) s
        ≤ affTerm as 6 A s + affTerm as 6 B s :=
          affTerm_add_le_aux as A B hA.smooth hB.smooth s hs'
      _ ≤ MA + MB := add_le_add (hMA ⟨s, hs, rfl⟩) (hMB ⟨s, hs, rfl⟩)

lemma isAffElem_smul_aux (as : ℝ) (c : ℝ) (A : ℝ → Mat3) (hA : IsAffElem as A) :
    IsAffElem as (c • A) where
  smooth := ContDiffOn.const_smul c hA.smooth
  traceFree := fun s hs => by
    have h1 := hA.traceFree s hs
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * h1
  noMixedAzimuth := fun s hs => by
    obtain ⟨a1, a2, a3, a4⟩ := hA.noMixedAzimuth s hs
    simp [a1, a2, a3, a4]
  zeroOff := fun s hs => by simp [hA.zeroOff s hs]
  bdd := by
    obtain ⟨MA, hMA⟩ := hA.bdd
    refine ⟨|c| * MA, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs' : 0 < s := Set.mem_Ioi.mp hs
    have hterm : affTerm as 6 (c • A) s = |c| * affTerm as 6 A s := by
      unfold affTerm affSum
      have hsum : ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (c • A) s)
          = |c| * ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j A s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj6 : j ≤ 6 := by
          rw [Finset.mem_range] at hj
          omega
        rw [sdi_smul_aux c A hA.smooth j hj6 s hs', frob_smul_aux]
      rw [hsum]
      ring
    rw [hterm]
    exact mul_le_mul_of_nonneg_left (hMA ⟨s, hs, rfl⟩) (abs_nonneg c)

/-- The closure of `𝒜` under `0`, sums and scalar multiples (source 4741-4745). -/
theorem affClosure (as : ℝ) : AffClosure as := by
  unfold AffClosure
  refine ⟨isAffElem_zero_aux as, ?_, ?_⟩
  · intro A B hA hB
    exact isAffElem_add_aux as A B hA hB
  · intro c A hA
    exact isAffElem_smul_aux as c A hA

end UnforcedLeray.Short.PartIIIb.Concrete
