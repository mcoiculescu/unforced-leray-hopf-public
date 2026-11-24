import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.Class
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!


Source: `the November 2 reference manuscript`, lines 2100-2105.  No heat kernel in
this file:

* `CB.tsum`: a series of `CB T m` families with summable bounds is of class `CB T m`;
* `neumannX`: the abstract form of the Picard iteration in the class
  `{Z ∈ C¹_b : ψ Z ∈ C²_b}`: if a linear map `A` halves the exponentially weighted norms of this
  class, a `C¹_b` solution of `y = S + A y` with `S` in the class is in the class (the Neumann
  series `∑ Aⁿ S` converges in the class and equals `y` by uniqueness in `C¹_b`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

variable {T : ℝ}

/-- `‖α • fst + β • snd‖ ≤ |α| + |β|`. -/
theorem norm_fderiv_le_pd (f : Pl → ℝ) (x : Pl) :
    ‖fderiv ℝ f x‖ ≤ |B0579.pd 0 f x| + |B0579.pd 1 f x| := by
  rw [fderiv_eq_pd]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)

/-- Summability from a bound, in a slice. -/
theorem summable_of_le {D : ℕ → ℝ} {ε : ℕ → ℝ} (hε : Summable ε) (h : ∀ n, |D n| ≤ ε n) :
    Summable D :=
  Summable.of_norm_bounded hε (fun n => by rw [Real.norm_eq_abs]; exact h n)

theorem abs_tsum_le {D : ℕ → ℝ} {ε : ℕ → ℝ} (hε : Summable ε) (h : ∀ n, |D n| ≤ ε n) :
    |∑' n, D n| ≤ ∑' n, ε n := by
  have := tsum_of_norm_bounded hε.hasSum (f := D) (fun n => by rw [Real.norm_eq_abs]; exact h n)
  rwa [Real.norm_eq_abs] at this

/-- Term by term differentiation of a series of slices. -/
theorem pd_tsum {D : ℕ → Pl → ℝ} {ε : ℕ → ℝ} (hε : Summable ε) (hd : ∀ n, Differentiable ℝ (D n))
    (h0 : ∀ n x, |D n x| ≤ ε n) (h1 : ∀ n (j : Fin 2) x, |B0579.pd j (D n) x| ≤ ε n) (j : Fin 2)
    (x : Pl) :
    Differentiable ℝ (fun y => ∑' n, D n y) ∧
      B0579.pd j (fun y => ∑' n, D n y) x = ∑' n, B0579.pd j (D n) x := by
  have hu : Summable (fun n => ε n + ε n) := hε.add hε
  have hf : ∀ n y, HasFDerivAt (D n) (fderiv ℝ (D n) y) y := fun n y => (hd n y).hasFDerivAt
  have hf' : ∀ n y, ‖fderiv ℝ (D n) y‖ ≤ ε n + ε n := fun n y =>
    (norm_fderiv_le_pd _ _).trans (add_le_add (h1 n 0 y) (h1 n 1 y))
  have hs0 : Summable fun n => D n x := summable_of_le hε fun n => h0 n x
  have hF := hasFDerivAt_tsum hu hf hf' hs0 x
  refine ⟨differentiable_tsum hu hf hf', ?_⟩
  unfold B0579.pd
  rw [hF.fderiv]
  have hsum : Summable (fun n => fderiv ℝ (D n) x) :=
    Summable.of_norm_bounded hu (fun n => hf' n x)
  have := (ContinuousLinearMap.apply ℝ ℝ (B0579.dir j)).map_tsum hsum
  simpa using this

/-- A series of `CB T m` families with summable bounds is of class `CB T m`. -/
theorem CB.tsum : ∀ {m : ℕ} {D : ℕ → ℝ → Pl → ℝ} {ε : ℕ → ℝ}, (∀ n, CB T m (D n)) →
    (∀ n, CBle T m (D n) (fun _ => ε n)) → Summable ε →
    CB T m (fun σ x => ∑' n, D n σ x) ∧ CBle T m (fun σ x => ∑' n, D n σ x) (fun _ => ∑' n, ε n)
  | 0, D, ε, hc, hb, hε => by
      have hcont : ContinuousOn (fun z : ℝ × Pl => ∑' n, D n z.1 z.2) (Icc 0 T ×ˢ univ) :=
        continuousOn_tsum (fun n => (hc n).1) hε (fun n z hz => by
          rw [Real.norm_eq_abs]
          exact hb n z.1 hz.1 z.2)
      have hbd : ∀ σ ∈ Icc 0 T, ∀ x : Pl, |∑' n, D n σ x| ≤ ∑' n, ε n := fun σ hσ x =>
        abs_tsum_le hε fun n => hb n σ hσ x
      exact ⟨⟨hcont, _, hbd⟩, hbd⟩
  | m + 1, D, ε, hc, hb, hε => by
      have h00 : ∀ n, CB T 0 (D n) := fun n => CB.mono (Nat.zero_le _) (hc n)
      have hb0 : ∀ n, CBle T 0 (D n) (fun _ => ε n) := fun n σ hσ x => (hb n).1 σ hσ x
      obtain ⟨hC0, hB0⟩ := CB.tsum h00 hb0 hε
      have hpd : ∀ σ ∈ Icc 0 T, ∀ (j : Fin 2) (x : Pl),
          Differentiable ℝ (fun y => ∑' n, D n σ y) ∧
          B0579.pd j (fun y => ∑' n, D n σ y) x = ∑' n, B0579.pd j (D n σ) x := fun σ hσ j x =>
        pd_tsum hε (fun n => (hc n).2.1 σ hσ) (fun n y => (hb n).1 σ hσ y)
          (fun n j y => CBle.top ((hb n).2 j) σ hσ y) j x
      refine ⟨⟨hC0, fun σ hσ => (hpd σ hσ 0 0).1, fun j => ?_⟩, hB0, fun j => ?_⟩
      · obtain ⟨h1, _⟩ := CB.tsum (fun n => (hc n).2.2 j) (fun n => (hb n).2 j) hε
        exact CB.congr h1 fun σ hσ x => (hpd σ hσ j x).2.symm
      · obtain ⟨_, h1⟩ := CB.tsum (fun n => (hc n).2.2 j) (fun n => (hb n).2 j) hε
        exact CBle.congr h1 fun σ hσ x => (hpd σ hσ j x).2.symm

/-- The exponential weight `M e^{λσ}`. -/
def ew (lam M σ : ℝ) : ℝ := M * Real.exp (lam * σ)

theorem ew_nonneg {lam M σ : ℝ} (hM : 0 ≤ M) : 0 ≤ ew lam M σ :=
  mul_nonneg hM (Real.exp_pos _).le

theorem le_ew {lam M σ : ℝ} (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hσ : 0 ≤ σ) : M ≤ ew lam M σ := by
  unfold ew
  have : 1 ≤ Real.exp (lam * σ) := Real.one_le_exp (mul_nonneg hlam hσ)
  exact le_mul_of_one_le_right hM this

theorem ew_le {lam M σ : ℝ} (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hσ : σ ≤ T) :
    ew lam M σ ≤ M * Real.exp (lam * T) := by
  unfold ew
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ hlam)) hM

/-- **The abstract Neumann iteration in the class `{Z ∈ C¹_b : ψ Z ∈ C²_b}`.** -/
theorem neumannX {lam : ℝ} {ψ : ℝ → ℝ} {A : (ℝ → Pl → ℝ) → ℝ → Pl → ℝ} (hlam : 0 ≤ lam)
    (hadd : ∀ Z Z' : ℝ → Pl → ℝ, CB T 1 Z → CB T 1 Z' → ∀ σ ∈ Icc 0 T, ∀ x : Pl,
      A (fun r y => Z r y + Z' r y) σ x = A Z σ x + A Z' σ x)
    (hsmul : ∀ (Z : ℝ → Pl → ℝ) (c : ℝ), CB T 1 Z → ∀ σ ∈ Icc 0 T, ∀ x : Pl,
      A (fun r y => c * Z r y) σ x = c * A Z σ x)
    (h1 : ∀ (Z : ℝ → Pl → ℝ) (M : ℝ), 0 ≤ M → CB T 1 Z → CBle T 1 Z (ew lam M) →
      CB T 1 (A Z) ∧ CBle T 1 (A Z) (ew lam (M / 2)))
    (h2 : ∀ (Z : ℝ → Pl → ℝ) (M : ℝ), 0 ≤ M → CB T 1 Z → CBle T 1 Z (ew lam M) →
      CB T 2 (mulC ψ Z) → CBle T 2 (mulC ψ Z) (ew lam M) →
      CB T 2 (mulC ψ (A Z)) ∧ CBle T 2 (mulC ψ (A Z)) (ew lam (M / 2)))
    {y S : ℝ → Pl → ℝ} (hy : CB T 1 y) (hS : CB T 1 S) (hψS : CB T 2 (mulC ψ S))
    (he : ∀ σ ∈ Icc 0 T, ∀ x : Pl, y σ x = S σ x + A y σ x) : CB T 2 (mulC ψ y) := by
  -- the constants
  obtain ⟨M1, hM1, hS1⟩ := CB.exists_le hS
  obtain ⟨M2, hM2, hS2⟩ := CB.exists_le hψS
  obtain ⟨M3, hM3, hy3⟩ := CB.exists_le hy
  set M := M1 + M2 + M3 with hMdef
  have hM : 0 ≤ M := by positivity
  have hup : ∀ {m : ℕ} {Z : ℝ → Pl → ℝ} {C : ℝ}, CBle T m Z (fun _ => C) → C ≤ M →
      CBle T m Z (ew lam M) := fun h hC => CBle.mono_b h fun σ hσ =>
    hC.trans (le_ew hlam hM hσ.1)
  have hS1' : CBle T 1 S (ew lam M) := hup hS1 (by linarith)
  have hS2' : CBle T 2 (mulC ψ S) (ew lam M) := hup hS2 (by linarith)
  have hy3' : CBle T 1 y (ew lam M) := hup hy3 (by linarith)
  -- the iterates
  let D : ℕ → ℝ → Pl → ℝ := fun n => Nat.rec S (fun _ Z => A Z) n
  have hD0 : D 0 = S := rfl
  have hDs : ∀ n, D (n + 1) = A (D n) := fun _ => rfl
  have hDcl : ∀ n, CB T 1 (D n) ∧ CBle T 1 (D n) (ew lam (M / 2 ^ n)) ∧ CB T 2 (mulC ψ (D n)) ∧
      CBle T 2 (mulC ψ (D n)) (ew lam (M / 2 ^ n)) := by
    intro n
    induction n with
    | zero =>
        simp only [pow_zero, div_one, hD0]
        exact ⟨hS, hS1', hψS, hS2'⟩
    | succ n ih =>
        obtain ⟨i1, i2, i3, i4⟩ := ih
        have hMn : 0 ≤ M / 2 ^ n := by positivity
        have e : M / 2 ^ n / 2 = M / 2 ^ (n + 1) := by
          rw [pow_succ]
          field_simp
        obtain ⟨a1, a2⟩ := h1 _ _ hMn i1 i2
        obtain ⟨a3, a4⟩ := h2 _ _ hMn i1 i2 i3 i4
        rw [e] at a2 a4
        rw [hDs]
        exact ⟨a1, a2, a3, a4⟩
  -- the summable bound
  let ε : ℕ → ℝ := fun n => M * Real.exp (lam * T) * (1 / 2) ^ n
  have hε : Summable ε :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hε0 : ∀ n, 0 ≤ ε n := fun n => by
    have := Real.exp_pos (lam * T)
    positivity
  have hbdd : ∀ n (σ : ℝ), σ ∈ Icc 0 T → ew lam (M / 2 ^ n) σ ≤ ε n := by
    intro n σ hσ
    have h := ew_le (T := T) (lam := lam) (M := M / 2 ^ n) (σ := σ) hlam (by positivity) hσ.2
    refine h.trans (le_of_eq ?_)
    simp only [ε, one_div, inv_pow]
    field_simp
  have hD1 : ∀ n, CBle T 1 (D n) (fun _ => ε n) := fun n =>
    CBle.mono_b (hDcl n).2.1 fun σ hσ => hbdd n σ hσ
  have hD2 : ∀ n, CBle T 2 (mulC ψ (D n)) (fun _ => ε n) := fun n =>
    CBle.mono_b (hDcl n).2.2.2 fun σ hσ => hbdd n σ hσ
  -- the sum
  let Z : ℝ → Pl → ℝ := fun σ x => ∑' n, D n σ x
  obtain ⟨hZ1, -⟩ := CB.tsum (fun n => (hDcl n).1) hD1 hε
  have hψZ : CB T 2 (mulC ψ Z) := by
    obtain ⟨h, -⟩ := CB.tsum (fun n => (hDcl n).2.2.1) hD2 hε
    refine CB.congr h fun σ hσ x => ?_
    show ∑' n, ψ x.2 * D n σ x = ψ x.2 * ∑' n, D n σ x
    exact tsum_mul_left
  -- partial sums
  let P : ℕ → ℝ → Pl → ℝ := fun N σ x => ∑ n ∈ Finset.range (N + 1), D n σ x
  have hP0 : ∀ σ x, P 0 σ x = S σ x := fun σ x => by simp [P, hD0]
  have hPs : ∀ N σ x, P (N + 1) σ x = P N σ x + D (N + 1) σ x := fun N σ x => by
    simp only [P]
    rw [Finset.sum_range_succ]
  have hPfun : ∀ N, P (N + 1) = fun σ x => P N σ x + D (N + 1) σ x := fun N =>
    funext fun σ => funext fun x => hPs N σ x
  have hPcl : ∀ N, CB T 1 (P N) := by
    intro N
    induction N with
    | zero =>
        have hfun : P 0 = S := funext fun σ => funext fun x => hP0 σ x
        rw [hfun]
        exact hS
    | succ N ih =>
        rw [hPfun]
        exact CB.add ih (hDcl (N + 1)).1
  -- `A` of the partial sums
  have hAP : ∀ N, ∀ σ ∈ Icc 0 T, ∀ x : Pl, S σ x + A (P N) σ x = P (N + 1) σ x := by
    intro N
    induction N with
    | zero =>
        intro σ hσ x
        have hfun : P 0 = S := funext fun σ => funext fun x => hP0 σ x
        rw [hfun, hPs, hP0, hDs, hD0]
    | succ N ih =>
        intro σ hσ x
        rw [hPfun N, hadd _ _ (hPcl N) (hDcl (N + 1)).1 σ hσ x, hPs (N + 1), ← ih σ hσ x, hDs (N + 1)]
        ring
  -- the tails
  have hsum : ∀ σ ∈ Icc 0 T, ∀ x : Pl, Summable fun n => D n σ x := fun σ hσ x =>
    summable_of_le hε fun n => CBle.top (hD1 n) σ hσ x
  let E : ℕ → ℝ → Pl → ℝ := fun N σ x => Z σ x + (-1) * P N σ x
  have hEsplit : ∀ N, Z = fun r w => P N r w + E N r w := fun N =>
    funext fun r => funext fun w => by simp only [E]; ring
  have hEeq : ∀ N, ∀ σ ∈ Icc 0 T, ∀ x : Pl, ∑' n, D (n + (N + 1)) σ x = E N σ x := by
    intro N σ hσ x
    have h := (hsum σ hσ x).sum_add_tsum_nat_add (N + 1)
    simp only [E, Z, P]
    linarith
  have hεtail : ∀ N, Summable fun n => ε (n + (N + 1)) := fun N =>
    (summable_nat_add_iff (N + 1)).2 hε
  have hEcl : ∀ N, CB T 1 (E N) := fun N => by
    obtain ⟨h, -⟩ := CB.tsum (T := T) (m := 1) (D := fun n => D (n + (N + 1)))
      (ε := fun n => ε (n + (N + 1))) (fun n => (hDcl (n + (N + 1))).1)
      (fun n => hD1 (n + (N + 1))) (hεtail N)
    exact CB.congr h (hEeq N)
  have hEle : ∀ N, CBle T 1 (E N) (fun _ => ∑' n, ε (n + (N + 1))) := fun N => by
    obtain ⟨-, h⟩ := CB.tsum (T := T) (m := 1) (D := fun n => D (n + (N + 1)))
      (ε := fun n => ε (n + (N + 1))) (fun n => (hDcl (n + (N + 1))).1)
      (fun n => hD1 (n + (N + 1))) (hεtail N)
    exact CBle.congr h (hEeq N)
  have htail0 : ∀ N, 0 ≤ ∑' n, ε (n + (N + 1)) := fun N => tsum_nonneg fun n => hε0 _
  have htail : Tendsto (fun N => ∑' n, ε (n + (N + 1))) atTop (𝓝 0) := by
    have h := tendsto_sum_nat_add ε
    exact h.comp (tendsto_add_atTop_nat 1)
  -- the fixed point
  have hfix : ∀ σ ∈ Icc 0 T, ∀ x : Pl, Z σ x = S σ x + A Z σ x := by
    intro σ hσ x
    have hbound : ∀ N, |Z σ x - (S σ x + A Z σ x)| ≤
        (∑' n, ε (n + (N + 1 + 1))) + (∑' n, ε (n + (N + 1))) / 2 * Real.exp (lam * T) := by
      intro N
      have h1' := h1 (E N) _ (htail0 N) (hEcl N) (CBle.mono_b (hEle N) fun r hr =>
        le_ew hlam (htail0 N) hr.1)
      have hAE := CBle.top h1'.2 σ hσ x
      have hAZ : A Z σ x = A (P N) σ x + A (E N) σ x := by
        conv_lhs => rw [hEsplit N]
        exact hadd _ _ (hPcl N) (hEcl N) σ hσ x
      have hZP : Z σ x - P (N + 1) σ x = E (N + 1) σ x := by
        simp only [E]
        ring
      have hE1 := CBle.top (hEle (N + 1)) σ hσ x
      have hAP' := hAP N σ hσ x
      have heq : Z σ x - (S σ x + A Z σ x) = E (N + 1) σ x - A (E N) σ x := by
        rw [hAZ, ← hZP, ← hAP']
        ring
      rw [heq]
      refine (abs_sub _ _).trans (add_le_add hE1 (hAE.trans ?_))
      exact ew_le hlam (by have := htail0 N; positivity) hσ.2
    have hlim : Tendsto (fun N => (∑' n, ε (n + (N + 1 + 1))) +
        (∑' n, ε (n + (N + 1))) / 2 * Real.exp (lam * T)) atTop (𝓝 0) := by
      have h1 := htail.comp (tendsto_add_atTop_nat 1)
      have h2 := (htail.div_const 2).mul_const (Real.exp (lam * T))
      have h3 := h1.add h2
      simpa using h3
    have hle := ge_of_tendsto' hlim hbound
    have hz : Z σ x - (S σ x + A Z σ x) = 0 := abs_nonpos_iff.1 hle
    linarith
  -- uniqueness
  let W : ℝ → Pl → ℝ := fun r w => y r w + (-1) * Z r w
  have hW1 : CB T 1 W := CB.add hy (CB.const_mul (-1) hZ1)
  have hWfix : ∀ σ ∈ Icc 0 T, ∀ x : Pl, A W σ x = W σ x := by
    intro σ hσ x
    have h1' := hadd y (fun r w => (-1) * Z r w) hy (CB.const_mul (-1) hZ1) σ hσ x
    have h2' := hsmul Z (-1) hZ1 σ hσ x
    show A (fun r w => y r w + (-1) * Z r w) σ x = y σ x + (-1) * Z σ x
    rw [h1', h2', he σ hσ x, hfix σ hσ x]
    ring
  obtain ⟨M4, hM4, hW4⟩ := CB.exists_le hW1
  have hWn : ∀ n : ℕ, CBle T 1 W (ew lam (M4 / 2 ^ n)) := by
    intro n
    induction n with
    | zero =>
        simp only [pow_zero, div_one]
        exact CBle.mono_b hW4 fun σ hσ => le_ew hlam hM4 hσ.1
    | succ n ih =>
        have hMn : 0 ≤ M4 / 2 ^ n := by positivity
        have e : M4 / 2 ^ n / 2 = M4 / 2 ^ (n + 1) := by
          rw [pow_succ]
          field_simp
        have h := (h1 W _ hMn hW1 ih).2
        rw [e] at h
        exact CBle.congr h hWfix
  have hWzero : ∀ σ ∈ Icc 0 T, ∀ x : Pl, W σ x = 0 := by
    intro σ hσ x
    have hbound : ∀ n : ℕ, |W σ x| ≤ M4 * Real.exp (lam * σ) * (1 / 2) ^ n := by
      intro n
      refine (CBle.top (hWn n) σ hσ x).trans (le_of_eq ?_)
      simp only [ew, one_div, inv_pow]
      field_simp
    have hlim : Tendsto (fun n : ℕ => M4 * Real.exp (lam * σ) * ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 : ℝ) / 2) (by norm_num)
        (by norm_num)).const_mul (M4 * Real.exp (lam * σ))
      simpa using h
    exact abs_nonpos_iff.1 (ge_of_tendsto' hlim hbound)
  refine CB.congr hψZ fun σ hσ x => ?_
  have h0 := hWzero σ hσ x
  have : y σ x = Z σ x := by
    simp only [W] at h0
    linarith
  simp only [mulC, this]

end LS

end UnforcedLeray.Short.IIb.BwdRoute
