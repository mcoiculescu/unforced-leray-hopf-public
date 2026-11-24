import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_1_closure
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Real.Sqrt

/-!
# Completeness of `𝒜` (source lines 4733-4752), task `PartIII-b:C/ret/1/3`

Proves `affCompleteness`: an `affNorm`-Cauchy sequence in `𝒜` converges in `𝒜`.
Outline: the weight `e^{-a_s s} s^{-5/2}` is bounded below on compacts of `(0,∞)`, so each
`(s∂_s)^j f_n`, `j ≤ 6`, converges locally uniformly on `(0,∞)` to `G j`; the derivative
relation `HasDerivAt (G j) (x⁻¹ • G (j+1) x) x` makes `A = G 0` a `C^6` function on `(0,∞)`;
trace and azimuth conditions pass to pointwise limits; the norm convergence follows from the
pointwise weighted estimate.
-/

set_option autoImplicit false

noncomputable section

open Set Real Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Frobenius and sup norms -/

lemma sq_le_frob_sq_aux (X : Mat3) (i j : Fin 3) : X i j ^ 2 ≤ ∑ a, ∑ b, X a b ^ 2 := by
  have h1 : X i j ^ 2 ≤ ∑ b, X i b ^ 2 :=
    Finset.single_le_sum (f := fun b => X i b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ b, X i b ^ 2 ≤ ∑ a, ∑ b, X a b ^ 2 :=
    Finset.single_le_sum (f := fun a => ∑ b, X a b ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

lemma norm_le_frob_aux (X : Mat3) : ‖X‖ ≤ frob X := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (sq_le_frob_sq_aux X i j)

lemma continuous_frob_aux : Continuous frob := by
  unfold frob
  fun_prop

/-! ## The weight -/

/-- `W(x) = e^{a_s x} x^{5/2}`, the inverse of the weight in `affTerm`. -/
def affWt (as x : ℝ) : ℝ := Real.exp (as * x) * x ^ (5 / 2 : ℝ)

lemma affWt_nonneg_aux (as x : ℝ) (hx : 0 < x) : 0 ≤ affWt as x :=
  mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)

lemma affWt_mul_aux (as x : ℝ) (hx : 0 < x) :
    Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) * affWt as x = 1 := by
  have h1 : 0 < Real.exp (as * x) := Real.exp_pos _
  have h2 : 0 < x ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  unfold affWt
  rw [Real.rpow_neg hx.le, neg_mul, Real.exp_neg]
  field_simp

lemma affTerm_le_affNorm_aux (as : ℝ) (D : ℝ → Mat3) (hD : IsAffElem as D) (x : ℝ)
    (hx : 0 < x) : affTerm as 6 D x ≤ affNorm as D := by
  unfold affNorm
  exact le_csSup hD.bdd ⟨x, hx, rfl⟩

/-- Pointwise weighted estimate: `|(s∂_s)^j D(x)| ≤ W(x) ‖D‖_𝒜` for `j ≤ 6`. -/
lemma norm_sdi_le_aux (as : ℝ) (D : ℝ → Mat3) (hD : IsAffElem as D) (j : ℕ) (hj : j ≤ 6)
    (x : ℝ) (hx : 0 < x) :
    ‖sDerivIter j D x‖ ≤ affWt as x * affNorm as D := by
  have hsingle : frob (sDerivIter j D x) ≤ affSum 6 D x := by
    unfold affSum
    exact Finset.single_le_sum (f := fun j => frob (sDerivIter j D x))
      (fun i _ => Real.sqrt_nonneg _) (Finset.mem_range.2 (by omega))
  have hs : affSum 6 D x = affWt as x * affTerm as 6 D x := by
    have hT : affTerm as 6 D x = Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) * affSum 6 D x := rfl
    rw [hT]
    calc affSum 6 D x
        = (Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) * affWt as x) * affSum 6 D x := by
          rw [affWt_mul_aux as x hx, one_mul]
      _ = affWt as x * (Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) * affSum 6 D x) := by ring
  calc ‖sDerivIter j D x‖ ≤ frob (sDerivIter j D x) := norm_le_frob_aux _
    _ ≤ affSum 6 D x := hsingle
    _ = affWt as x * affTerm as 6 D x := hs
    _ ≤ affWt as x * affNorm as D :=
        mul_le_mul_of_nonneg_left (affTerm_le_affNorm_aux as D hD x hx)
          (affWt_nonneg_aux as x hx)

/-! ## Linearity on `(0,∞)` -/

lemma sub_eq_add_smul_aux (A B : ℝ → Mat3) : A - B = A + (-1 : ℝ) • B := by
  funext s
  simp [sub_eq_add_neg]

lemma sdi_sub_aux (A B : ℝ → Mat3) (hA : ContDiffOn ℝ 6 A (Ioi 0))
    (hB : ContDiffOn ℝ 6 B (Ioi 0)) :
    ∀ j, j ≤ 6 → ∀ s, 0 < s → sDerivIter j (A - B) s = sDerivIter j A s - sDerivIter j B s := by
  intro j hj s hs
  have hB' : ContDiffOn ℝ 6 ((-1 : ℝ) • B) (Ioi 0) := ContDiffOn.const_smul (-1 : ℝ) hB
  rw [sub_eq_add_smul_aux A B, sdi_add_aux A _ hA hB' j hj s hs,
    sdi_smul_aux (-1 : ℝ) B hB j hj s hs]
  simp [sub_eq_add_neg]

lemma affTerm_sub_eq_aux (as : ℝ) (D E : ℝ → Mat3) (hD : ContDiffOn ℝ 6 D (Ioi 0))
    (hE : ContDiffOn ℝ 6 E (Ioi 0)) (x : ℝ) (hx : 0 < x) :
    affTerm as 6 (D - E) x = Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) *
      ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j D x - sDerivIter j E x) := by
  have hsum : ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (D - E) x)
      = ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j D x - sDerivIter j E x) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sdi_sub_aux D E hD hE j (by have := Finset.mem_range.1 hj; omega) x hx]
  unfold affTerm affSum
  rw [hsum]

/-! ## Completeness -/

theorem affCompleteness (as : ℝ) (h : AffClosure as) (hn : AffNormLaws as) :
    AffCompleteness as := by
  unfold AffCompleteness
  intro f hf hC
  have hneg : ∀ n, IsAffElem as ((-1 : ℝ) • f n) := fun n => h.2.2 (-1) (f n) (hf n)
  have hD : ∀ m n, IsAffElem as (f m - f n) := fun m n => by
    rw [sub_eq_add_smul_aux]
    exact h.2.1 _ _ (hf m) (hneg n)
  -- weighted estimate for differences of the sequence
  have hest : ∀ j, j ≤ 6 → ∀ x, 0 < x → ∀ m n,
      ‖sDerivIter j (f m) x - sDerivIter j (f n) x‖ ≤ affWt as x * affNorm as (f m - f n) := by
    intro j hj x hx m n
    have := norm_sdi_le_aux as (f m - f n) (hD m n) j hj x hx
    rwa [sdi_sub_aux (f m) (f n) (hf m).smooth (hf n).smooth j hj x hx] at this
  -- pointwise limits exist
  have hpt : ∀ j, j ≤ 6 → ∀ x, 0 < x → ∃ L : Mat3,
      Tendsto (fun n => sDerivIter j (f n) x) atTop (𝓝 L) := by
    intro j hj x hx
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hWpos : 0 ≤ affWt as x := affWt_nonneg_aux as x hx
    obtain ⟨N, hN⟩ := hC (ε / (affWt as x + 1)) (div_pos hε (by linarith))
    refine ⟨N, fun m hm n hn' => ?_⟩
    rw [dist_eq_norm]
    have h1 := hest j hj x hx m n
    have h2 := hN m hm n hn'
    have h3 := affNorm_nonneg_of as (f m - f n) (hD m n)
    calc ‖sDerivIter j (f m) x - sDerivIter j (f n) x‖
        ≤ affWt as x * affNorm as (f m - f n) := h1
      _ ≤ (affWt as x + 1) * affNorm as (f m - f n) :=
          mul_le_mul_of_nonneg_right (by linarith) h3
      _ < (affWt as x + 1) * (ε / (affWt as x + 1)) :=
          mul_lt_mul_of_pos_left h2 (by linarith)
      _ = ε := by field_simp
  -- the limits `G j`
  have hlim : ∀ j, ∃ G : ℝ → Mat3, j ≤ 6 → ∀ x, 0 < x →
      Tendsto (fun n => sDerivIter j (f n) x) atTop (𝓝 (G x)) := by
    intro j
    by_cases hj : j ≤ 6
    · have hex : ∀ x : ℝ, ∃ L : Mat3, 0 < x → Tendsto (fun n => sDerivIter j (f n) x) atTop
          (𝓝 L) := by
        intro x
        by_cases hx : 0 < x
        · obtain ⟨L, hL⟩ := hpt j hj x hx
          exact ⟨L, fun _ => hL⟩
        · exact ⟨0, fun h' => absurd h' hx⟩
      choose G hG using hex
      exact ⟨G, fun _ => hG⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hj⟩
  choose G hG using hlim
  -- uniform convergence on compacts of `(0,∞)`
  have hU : ∀ j, j ≤ 6 → ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K → ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ∀ x ∈ K, ‖sDerivIter j (f n) x - G j x‖ ≤ ε := by
    intro j hj K hK hKc ε hε
    have hWc : ContinuousOn (affWt as) K := by
      unfold affWt
      apply ContinuousOn.mul
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      · exact continuousOn_id.rpow_const (fun x _ => Or.inr (by norm_num))
    obtain ⟨C, hCbd⟩ := hKc.exists_bound_of_continuousOn hWc
    have hCa : ∀ x ∈ K, affWt as x ≤ |C| := fun x hx => by
      have := hCbd x hx
      rw [Real.norm_eq_abs] at this
      exact le_trans (le_abs_self _) (le_trans this (le_abs_self C))
    have hCpos : 0 < |C| + 1 := by positivity
    obtain ⟨N, hN⟩ := hC (ε / (|C| + 1)) (div_pos hε hCpos)
    refine ⟨N, fun n hn' x hx => ?_⟩
    have hxpos : 0 < x := hK hx
    have hδ : ε / (|C| + 1) * (|C| + 1) = ε := div_mul_cancel₀ _ hCpos.ne'
    have hlim' : Tendsto (fun m => ‖sDerivIter j (f n) x - sDerivIter j (f m) x‖) atTop
        (𝓝 ‖sDerivIter j (f n) x - G j x‖) :=
      (tendsto_const_nhds.sub (hG j hj x hxpos)).norm
    apply le_of_tendsto hlim'
    filter_upwards [eventually_ge_atTop N] with m hm
    have h1 := hest j hj x hxpos n m
    have h2 := hN n hn' m hm
    have h3 := affNorm_nonneg_of as (f n - f m) (hD n m)
    have h4 := hCa x hx
    have h5 : affWt as x * affNorm as (f n - f m) ≤ |C| * (ε / (|C| + 1)) :=
      mul_le_mul h4 h2.le h3 (abs_nonneg C)
    have h6 : |C| * (ε / (|C| + 1)) ≤ ε := by
      nlinarith [abs_nonneg C, div_pos hε hCpos]
    linarith
  -- locally uniform convergence on `(0,∞)`
  have hTLU : ∀ j, j ≤ 6 →
      TendstoLocallyUniformlyOn (fun n => sDerivIter j (f n)) (G j) atTop (Ioi 0) := by
    intro j hj
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi]
    intro K hK hKc
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hU j hj K hK hKc (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn' x hx
    rw [dist_comm, dist_eq_norm]
    linarith [hN n hn' x hx]
  -- continuity of `G 6`
  have hcont6 : ContinuousOn (G 6) (Ioi 0) := by
    have hc6 : ∀ n, ContinuousOn (sDerivIter 6 (f n)) (Ioi 0) := fun n =>
      (sdi_contDiff_aux 6 0 (f n) (by simpa using (hf n).smooth)).continuousOn
    exact (hTLU 6 (by norm_num)).continuousOn (Eventually.of_forall hc6).frequently
  -- derivative relation for `G j`
  have hderiv : ∀ j, j ≤ 5 → ∀ x, 0 < x → HasDerivAt (G j) (x⁻¹ • G (j + 1) x) x := by
    intro j hj x hx
    have hTL : TendstoLocallyUniformlyOn (fun n y => y⁻¹ • sDerivIter (j + 1) (f n) y)
        (fun y => y⁻¹ • G (j + 1) y) atTop (Ioi 0) := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi]
      intro K hK hKc
      have hinv : ContinuousOn (fun y : ℝ => y⁻¹) K :=
        continuousOn_id.inv₀ (fun y hy => (hK hy).ne')
      obtain ⟨C, hC'⟩ := hKc.exists_bound_of_continuousOn hinv
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
      have hpos : 0 < |C| + 2 := by positivity
      obtain ⟨N, hN⟩ := hU (j + 1) (by omega) K hK hKc (ε / (|C| + 2)) (div_pos hε hpos)
      filter_upwards [eventually_ge_atTop N] with n hn' y hy
      show dist (y⁻¹ • G (j + 1) y) (y⁻¹ • sDerivIter (j + 1) (f n) y) < ε
      have hyC : ‖y⁻¹‖ ≤ |C| := le_trans (hC' y hy) (le_abs_self C)
      have hN' := hN n hn' y hy
      have hδ : ε / (|C| + 2) * (|C| + 2) = ε := div_mul_cancel₀ _ hpos.ne'
      have hp1 : ‖y⁻¹‖ * ‖sDerivIter (j + 1) (f n) y - G (j + 1) y‖ ≤
          |C| * (ε / (|C| + 2)) := mul_le_mul hyC hN' (norm_nonneg _) (abs_nonneg C)
      have hp2 : |C| * (ε / (|C| + 2)) < ε := by
        nlinarith [div_pos hε hpos]
      rw [dist_eq_norm, ← smul_sub, norm_smul, norm_sub_rev]
      linarith
    refine hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioi hTL ?_
      (fun y hy => hG j (by omega) y hy) hx
    refine Eventually.of_forall fun n y hy => ?_
    have hdiff : DifferentiableOn ℝ (sDerivIter j (f n)) (Ioi 0) :=
      sdi_diff_aux (f n) (hf n).smooth j (by omega)
    have hd := (hdiff.differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
    have e : deriv (sDerivIter j (f n)) y = y⁻¹ • sDerivIter (j + 1) (f n) y := by
      show _ = y⁻¹ • (y • deriv (sDerivIter j (f n)) y)
      rw [smul_smul, inv_mul_cancel₀ (Set.mem_Ioi.mp hy).ne', one_smul]
    show HasDerivAt (sDerivIter j (f n)) (y⁻¹ • sDerivIter (j + 1) (f n) y) y
    rw [← e]
    exact hd
  -- `G j` is `C^{6-j}` on `(0,∞)`
  have hCD : ∀ k : ℕ, ∀ j : ℕ, j + k = 6 → ContDiffOn ℝ (k : WithTop ℕ∞) (G j) (Ioi 0) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have hj6 : j = 6 := by omega
      subst hj6
      have hz0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (G 6) (Ioi 0) :=
        contDiffOn_zero.2 hcont6
      exact hz0
    | succ k ih =>
      intro j hj
      have hj5 : j ≤ 5 := by omega
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by
        push_cast
        rfl
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun y hy => (hderiv j hj5 y hy).differentiableAt.differentiableWithinAt,
        fun h' => absurd h' (by simp), ?_⟩
      refine ContDiffOn.congr (f := fun y => y⁻¹ • G (j + 1) y) ?_
        (fun y hy => (hderiv j hj5 y hy).deriv)
      exact (contDiffOn_id.inv (fun y hy => (Set.mem_Ioi.mp hy).ne')).smul
        (ih (j + 1) (by omega))
  have hC6 : ContDiffOn ℝ 6 (G 0) (Ioi 0) := by
    have := hCD 6 0 (by norm_num)
    simpa using this
  -- the limit function `A` (zero on `s ≤ 0`)
  obtain ⟨A, hA1, hA2⟩ : ∃ A : ℝ → Mat3, (∀ x, 0 < x → A x = G 0 x) ∧ (∀ x, x ≤ 0 → A x = 0) :=
    ⟨fun s => if 0 < s then G 0 s else 0, fun x hx => if_pos hx,
      fun x hx => if_neg (not_lt.2 hx)⟩
  have hAsm : ContDiffOn ℝ 6 A (Ioi 0) := hC6.congr fun x hx => hA1 x hx
  -- the sequence of derivatives converges to `(s∂_s)^j A`
  have hI : ∀ j, j ≤ 6 → ∀ x, 0 < x → sDerivIter j A x = G j x := by
    intro j
    induction j with
    | zero => intro _ x hx; exact hA1 x hx
    | succ j ih =>
      intro hj x hx
      have hev : sDerivIter j A =ᶠ[𝓝 x] G j := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih (by omega) y hy
      have hd : deriv (sDerivIter j A) x = x⁻¹ • G (j + 1) x := by
        rw [hev.deriv_eq]
        exact (hderiv j (by omega) x hx).deriv
      show x • deriv (sDerivIter j A) x = G (j + 1) x
      rw [hd, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  -- pointwise values of the entries
  have hent : ∀ s, 0 < s → ∀ i j : Fin 3,
      Tendsto (fun n => f n s i j) atTop (𝓝 (G 0 s i j)) := fun s hs i j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (hG 0 (by norm_num) s hs) i) j
  have hz : ∀ s, 0 < s → ∀ i j : Fin 3, (∀ n, f n s i j = 0) → G 0 s i j = 0 := by
    intro s hs i j hij
    have hc : (fun n => f n s i j) = fun _ => (0 : ℝ) := funext hij
    have := hent s hs i j
    rw [hc] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  -- an index for the cutoff bound
  obtain ⟨N1, hN1⟩ := hC 1 one_pos
  have hAelem : IsAffElem as A := by
    refine
      { smooth := hAsm
        traceFree := ?_
        noMixedAzimuth := ?_
        zeroOff := fun s hs => hA2 s hs
        bdd := ?_ }
    · intro s hs
      rw [hA1 s hs]
      have htr : Tendsto (fun n => f n s 0 0 + f n s 1 1 + f n s 2 2) atTop
          (𝓝 (G 0 s 0 0 + G 0 s 1 1 + G 0 s 2 2)) :=
        ((hent s hs 0 0).add (hent s hs 1 1)).add (hent s hs 2 2)
      rw [show (fun n => f n s 0 0 + f n s 1 1 + f n s 2 2) = fun _ => (0 : ℝ) from
        funext fun n => (hf n).traceFree s hs] at htr
      exact (tendsto_nhds_unique tendsto_const_nhds htr).symm
    · intro s hs
      rw [hA1 s hs]
      have hm := fun n => (hf n).noMixedAzimuth s hs
      exact ⟨hz s hs 0 1 (fun n => (hm n).1), hz s hs 1 0 (fun n => (hm n).2.1),
        hz s hs 1 2 (fun n => (hm n).2.2.1), hz s hs 2 1 (fun n => (hm n).2.2.2)⟩
    · refine ⟨affNorm as (f N1) + 1, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hxpos : 0 < x := hx
      have e : affTerm as 6 A x = Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) *
          ∑ j ∈ Finset.range (6 + 1), frob (G j x) := by
        have hs' : ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j A x)
            = ∑ j ∈ Finset.range (6 + 1), frob (G j x) :=
          Finset.sum_congr rfl fun j hj => by
            rw [hI j (by have := Finset.mem_range.1 hj; omega) x hxpos]
        unfold affTerm affSum
        rw [hs']
      have hTA : Tendsto (fun n => affTerm as 6 (f n) x) atTop (𝓝 (affTerm as 6 A x)) := by
        have ef : ∀ n, affTerm as 6 (f n) x = Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) *
            ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (f n) x) := fun n => rfl
        simp only [ef]
        rw [e]
        apply Tendsto.const_mul
        apply tendsto_finsetSum
        intro j hj
        exact (continuous_frob_aux.tendsto _).comp
          (hG j (by have := Finset.mem_range.1 hj; omega) x hxpos)
      refine le_of_tendsto hTA (eventually_atTop.2 ⟨N1, fun n hn' => ?_⟩)
      calc affTerm as 6 (f n) x ≤ affNorm as (f n) :=
            affTerm_le_affNorm_aux as (f n) (hf n) x hxpos
        _ = affNorm as ((f n - f N1) + f N1) := by rw [sub_add_cancel]
        _ ≤ affNorm as (f n - f N1) + affNorm as (f N1) := hn.1 _ _ (hD n N1) (hf N1)
        _ ≤ 1 + affNorm as (f N1) := by linarith [hN1 n hn' N1 le_rfl]
        _ = affNorm as (f N1) + 1 := by ring
  refine ⟨A, hAelem, ?_⟩
  have hDA : ∀ n, IsAffElem as (f n - A) := fun n => by
    rw [sub_eq_add_smul_aux]
    exact h.2.1 _ _ (hf n) (h.2.2 (-1) A hAelem)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hC (ε / 2) (by positivity)
  have hclaim : ∀ n, N ≤ n → affNorm as (f n - A) ≤ ε / 2 := by
    intro n hn'
    unfold affNorm
    have hne : (affTerm as 6 (f n - A) '' Ioi 0).Nonempty :=
      ⟨affTerm as 6 (f n - A) 1, 1, (show (0 : ℝ) < 1 by norm_num), rfl⟩
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    have hxpos : 0 < x := hx
    have hlim2 : Tendsto (fun m => affTerm as 6 (f n - f m) x) atTop
        (𝓝 (affTerm as 6 (f n - A) x)) := by
      have ef : ∀ m, affTerm as 6 (f n - f m) x = Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) *
          ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (f n) x - sDerivIter j (f m) x) :=
        fun m => affTerm_sub_eq_aux as _ _ (hf n).smooth (hf m).smooth x hxpos
      have e2 : affTerm as 6 (f n - A) x = Real.exp (-as * x) * x ^ (-(5 / 2 : ℝ)) *
          ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (f n) x - G j x) := by
        rw [affTerm_sub_eq_aux as _ _ (hf n).smooth hAsm x hxpos]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [hI j (by have := Finset.mem_range.1 hj; omega) x hxpos]
      simp only [ef]
      rw [e2]
      apply Tendsto.const_mul
      apply tendsto_finsetSum
      intro j hj
      exact (continuous_frob_aux.tendsto _).comp
        (tendsto_const_nhds.sub (hG j (by have := Finset.mem_range.1 hj; omega) x hxpos))
    refine le_of_tendsto hlim2 (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    calc affTerm as 6 (f n - f m) x ≤ affNorm as (f n - f m) :=
          affTerm_le_affNorm_aux as _ (hD n m) x hxpos
      _ ≤ ε / 2 := (hN n hn' m hm).le
  refine ⟨N, fun n hn' => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (affNorm_nonneg_of as _ (hDA n))]
  linarith [hclaim n hn']

end UnforcedLeray.Short.PartIIIb.Concrete
