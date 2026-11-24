import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_15
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit.Cont

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

namespace PicDerivAux

open PicContAux

lemma dir_decomp (v : Pl) : v = v.1 • B0579.dir 0 + v.2 • B0579.dir 1 := by
  ext <;> simp [B0579.dir]

/-- Operator norm of a derivative on the plane is at most the sum of the two partials. -/
lemma norm_fderiv_le (h : Pl → ℝ) (x : Pl) :
    ‖fderiv ℝ h x‖ ≤ |B0579.pd 0 h x| + |B0579.pd 1 h x| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hv1 : |v.1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_snd_le v
  have e : fderiv ℝ h x v = v.1 * B0579.pd 0 h x + v.2 * B0579.pd 1 h x := by
    conv_lhs => rw [dir_decomp v]
    rw [map_add, map_smul, map_smul]
    simp [B0579.pd]
  rw [Real.norm_eq_abs, e]
  calc |v.1 * B0579.pd 0 h x + v.2 * B0579.pd 1 h x|
      ≤ |v.1 * B0579.pd 0 h x| + |v.2 * B0579.pd 1 h x| := abs_add_le _ _
    _ = |v.1| * |B0579.pd 0 h x| + |v.2| * |B0579.pd 1 h x| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * |B0579.pd 0 h x| + ‖v‖ * |B0579.pd 1 h x| := by
        gcongr
    _ = (|B0579.pd 0 h x| + |B0579.pd 1 h x|) * ‖v‖ := by ring

lemma pd_pd_eq {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) (i j : Fin 2) (x : Pl) :
    B0579.pd i (B0579.pd j g) x
      = fderiv ℝ (fderiv ℝ g) x (B0579.dir i) (B0579.dir j) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x := (h1.differentiable (by norm_num)) x
  have hH : HasFDerivAt (fun y => fderiv ℝ g y (B0579.dir j))
      ((fderiv ℝ (fderiv ℝ g) x).flip (B0579.dir j)) x := by
    have := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (B0579.dir j) x)
    simpa using this
  unfold B0579.pd
  have : (fun y => fderiv ℝ g y (B0579.dir j)) = fun y => fderiv ℝ g y (B0579.dir j) := rfl
  rw [show fderiv ℝ (fun y => fderiv ℝ g y (B0579.dir j)) x
      = (fderiv ℝ (fderiv ℝ g) x).flip (B0579.dir j) from hH.fderiv]
  rfl

/-- Second-order operator norm bound. -/
lemma norm_iter2_le {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) (x : Pl) :
    ‖iteratedFDeriv ℝ 2 g x‖ ≤ (|B0579.pd 0 (B0579.pd 0 g) x| + |B0579.pd 0 (B0579.pd 1 g) x|)
      + (|B0579.pd 1 (B0579.pd 0 g) x| + |B0579.pd 1 (B0579.pd 1 g) x|) := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [iteratedFDeriv_two_apply, Fin.prod_univ_two]
  set B2 := fderiv ℝ (fderiv ℝ g) x
  have hm : ∀ k : Fin 2, ‖m k‖ ≥ 0 := fun k => norm_nonneg _
  have c1 : ∀ k : Fin 2, |(m k).1| ≤ ‖m k‖ := fun k => by
    simpa [Real.norm_eq_abs] using norm_fst_le (m k)
  have c2 : ∀ k : Fin 2, |(m k).2| ≤ ‖m k‖ := fun k => by
    simpa [Real.norm_eq_abs] using norm_snd_le (m k)
  have e : B2 (m 0) (m 1) =
      (m 0).1 * ((m 1).1 * B2 (B0579.dir 0) (B0579.dir 0) + (m 1).2 * B2 (B0579.dir 0) (B0579.dir 1))
      + (m 0).2 * ((m 1).1 * B2 (B0579.dir 1) (B0579.dir 0)
        + (m 1).2 * B2 (B0579.dir 1) (B0579.dir 1)) := by
    conv_lhs => rw [dir_decomp (m 0), dir_decomp (m 1)]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [Real.norm_eq_abs, e]
  rw [pd_pd_eq hg 0 0 x, pd_pd_eq hg 0 1 x, pd_pd_eq hg 1 0 x, pd_pd_eq hg 1 1 x]
  set a := |B2 (B0579.dir 0) (B0579.dir 0)|
  set b := |B2 (B0579.dir 0) (B0579.dir 1)|
  set c := |B2 (B0579.dir 1) (B0579.dir 0)|
  set d := |B2 (B0579.dir 1) (B0579.dir 1)|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hc : 0 ≤ c := abs_nonneg _
  have hd : 0 ≤ d := abs_nonneg _
  set p0 := (m 0).1
  set p1 := (m 0).2
  set q0 := (m 1).1
  set q1 := (m 1).2
  have hp0 : |p0| ≤ ‖m 0‖ := c1 0
  have hp1 : |p1| ≤ ‖m 0‖ := c2 0
  have hq0 : |q0| ≤ ‖m 1‖ := c1 1
  have hq1 : |q1| ≤ ‖m 1‖ := c2 1
  have t : ∀ (u w r : ℝ) , |u| ≤ ‖m 0‖ → |w| ≤ ‖m 1‖ → |u * (w * r)| ≤ ‖m 0‖ * ‖m 1‖ * |r| := by
    intro u w r hu hw
    rw [abs_mul, abs_mul]
    have := abs_nonneg r
    calc |u| * (|w| * |r|) ≤ ‖m 0‖ * (‖m 1‖ * |r|) := by gcongr
      _ = _ := by ring
  have h1 := abs_add_le (p0 * (q0 * B2 (B0579.dir 0) (B0579.dir 0)
      + q1 * B2 (B0579.dir 0) (B0579.dir 1)))
    (p1 * (q0 * B2 (B0579.dir 1) (B0579.dir 0) + q1 * B2 (B0579.dir 1) (B0579.dir 1)))
  have h2 := abs_add_le (q0 * B2 (B0579.dir 0) (B0579.dir 0)) (q1 * B2 (B0579.dir 0) (B0579.dir 1))
  have h3 := abs_add_le (q0 * B2 (B0579.dir 1) (B0579.dir 0)) (q1 * B2 (B0579.dir 1) (B0579.dir 1))
  have u1 : |p0 * (q0 * B2 (B0579.dir 0) (B0579.dir 0) + q1 * B2 (B0579.dir 0) (B0579.dir 1))|
      ≤ ‖m 0‖ * (‖m 1‖ * a + ‖m 1‖ * b) := by
    rw [abs_mul]
    have : |q0 * B2 (B0579.dir 0) (B0579.dir 0) + q1 * B2 (B0579.dir 0) (B0579.dir 1)|
        ≤ ‖m 1‖ * a + ‖m 1‖ * b := by
      refine h2.trans ?_
      rw [abs_mul, abs_mul]
      gcongr
    gcongr
  have u2 : |p1 * (q0 * B2 (B0579.dir 1) (B0579.dir 0) + q1 * B2 (B0579.dir 1) (B0579.dir 1))|
      ≤ ‖m 0‖ * (‖m 1‖ * c + ‖m 1‖ * d) := by
    rw [abs_mul]
    have : |q0 * B2 (B0579.dir 1) (B0579.dir 0) + q1 * B2 (B0579.dir 1) (B0579.dir 1)|
        ≤ ‖m 1‖ * c + ‖m 1‖ * d := by
      refine h3.trans ?_
      rw [abs_mul, abs_mul]
      gcongr
    gcongr
  calc _ ≤ _ := h1
    _ ≤ ‖m 0‖ * (‖m 1‖ * a + ‖m 1‖ * b) + ‖m 0‖ * (‖m 1‖ * c + ‖m 1‖ * d) := add_le_add u1 u2
    _ = _ := by ring

end PicDerivAux

open PicDerivAux PicContAux

/-- **Leaf 1 (`/15/1`).** The uniform limit of the `C²` slices with summable `W2`-increments is
`C²` and its first and second derivatives are the limits of the derivatives. -/
theorem picLimDeriv_proof : UnforcedLeray.Short.IIb.CylPDE.PicLimDeriv := by
  intro c ν s T v f U B ε H
  obtain ⟨hc, hν, hs, hsT, hv, hf, hU, hU0, hUs, hε, hdiff⟩ := H
  intro σ hσ
  have hU2 : ∀ n, ContDiff ℝ 2 (U n σ) := fun n => (hU n).c2 σ hσ
  set g : ℕ → Pl → ℝ := fun n y => U (n + 1) σ y - U n σ y with hgdef
  have hg2 : ∀ n, ContDiff ℝ 2 (g n) := fun n => (hU2 (n + 1)).sub (hU2 n)
  have hW : ∀ n x, W2 (g n) x ≤ ε n := by
    intro n x
    have h1 := hdiff n σ hσ x
    have h2 := W2_nonneg (g n) x
    have h3 := Real.one_le_cosh x.2
    calc W2 (g n) x ≤ W2 (g n) x * Real.cosh x.2 := le_mul_of_one_le_right h2 h3
      _ ≤ ε n := h1
  have hε0 : ∀ n, 0 ≤ ε n := fun n => (W2_nonneg (g n) 0).trans (hW n 0)
  have hε4 : Summable (fun n => 4 * ε n) := hε.mul_left 4
  have hε2 : Summable (fun n => 2 * ε n) := hε.mul_left 2
  have hgd : ∀ n, Differentiable ℝ (g n) := fun n => c2_diff (hg2 n)
  -- first derivative norm bound
  have hn1 : ∀ n x, ‖fderiv ℝ (g n) x‖ ≤ 2 * ε n := by
    intro n x
    refine (norm_fderiv_le (g n) x).trans ?_
    have := abs_pd_le (g n) x 0
    have := abs_pd_le (g n) x 1
    have := hW n x
    linarith
  -- C² of the tail series
  have hS : ContDiff ℝ 2 (fun x => ∑' n, g n x) := by
    refine contDiff_tsum (v := fun _ n => 4 * ε n) hg2 (fun k _ => hε4) ?_
    intro k i x hk
    have hk' : k ≤ 2 := by exact_mod_cast hk
    have hWi := hW i x
    have a0 := abs_Q_le (g i) x 0
    have a1 := abs_pd_le (g i) x 0
    have a2 := abs_pd_le (g i) x 1
    have a3 := abs_pd2_le (g i) x 0 0
    have a4 := abs_pd2_le (g i) x 0 1
    have a5 := abs_pd2_le (g i) x 1 0
    have a6 := abs_pd2_le (g i) x 1 1
    have e0 : |Q (g i) x 0| = |g i x| := rfl
    interval_cases k
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have := hε0 i
      linarith
    · rw [norm_iteratedFDeriv_one]
      have := hn1 i x
      have := hε0 i
      linarith
    · refine (norm_iter2_le (hg2 i) x).trans ?_
      linarith
  have hlim : picLim U σ = fun x => U 0 σ x + ∑' n, g n x := by
    funext x
    rfl
  have hC2 : ContDiff ℝ 2 (picLim U σ) := by
    rw [hlim]
    exact (hU2 0).add hS
  have hsum : ∀ x, Summable (fun n => g n x) := by
    intro x
    refine Summable.of_norm_bounded hε (fun n => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_Q_le (g n) x 0).trans (hW n x)
  have hsumd : ∀ x, Summable (fun n => fderiv ℝ (g n) x) := by
    intro x
    exact Summable.of_norm_bounded hε2 (fun n => hn1 n x)
  have hfd : ∀ x, fderiv ℝ (fun y => ∑' n, g n y) x = ∑' n, fderiv ℝ (g n) x := by
    intro x
    exact fderiv_tsum_apply (𝕜 := ℝ) (u := fun n => 2 * ε n) hε2 hgd hn1 (hsum 0) x
  have hD1 : ∀ (j : Fin 2) (x : Pl), B0579.pd j (picLim U σ) x = picD1 U j σ x := by
    intro j x
    have hA : HasFDerivAt (fun y => U 0 σ y + ∑' n, g n y)
        (fderiv ℝ (U 0 σ) x + fderiv ℝ (fun y => ∑' n, g n y) x) x :=
      ((hU2 0).differentiable (by norm_num) x).hasFDerivAt.add
        ((hS.differentiable (by norm_num) x).hasFDerivAt)
    show (fderiv ℝ (picLim U σ) x) (B0579.dir j) = _
    rw [hlim, hA.fderiv, ContinuousLinearMap.add_apply, hfd x]
    unfold picD1
    congr 1
    have : (∑' n, fderiv ℝ (g n) x) (B0579.dir j) = ∑' n, fderiv ℝ (g n) x (B0579.dir j) := by
      have := ContinuousLinearMap.map_tsum
        (ContinuousLinearMap.apply ℝ ℝ (B0579.dir j)) (hsumd x)
      simpa using this
    rw [this]
    refine tsum_congr (fun n => ?_)
    have := pd_sub' (c2_diff (hU2 (n + 1))) (c2_diff (hU2 n)) j x
    unfold B0579.pd at this
    exact this
  refine ⟨hC2, hD1, ?_⟩
  intro i j x
  -- second derivatives
  have hfun : B0579.pd j (picLim U σ) = picD1 U j σ := funext (hD1 j)
  rw [hfun]
  set h : ℕ → Pl → ℝ := fun n y => B0579.pd j (U (n + 1) σ) y - B0579.pd j (U n σ) y with hhdef
  have hhd : ∀ n, Differentiable ℝ (h n) := fun n =>
    (diff_pd (hU2 (n + 1)) j).sub (diff_pd (hU2 n) j)
  have hhn : ∀ n y, ‖fderiv ℝ (h n) y‖ ≤ 2 * ε n := by
    intro n y
    refine (norm_fderiv_le (h n) y).trans ?_
    have e : B0579.pd j (g n) = h n := by
      funext z
      exact pd_sub' (c2_diff (hU2 (n + 1))) (c2_diff (hU2 n)) j z
    have p0 : B0579.pd 0 (h n) y = B0579.pd 0 (B0579.pd j (U (n + 1) σ)) y
        - B0579.pd 0 (B0579.pd j (U n σ)) y :=
      pd_sub' (diff_pd (hU2 (n + 1)) j) (diff_pd (hU2 n) j) 0 y
    have p1 : B0579.pd 1 (h n) y = B0579.pd 1 (B0579.pd j (U (n + 1) σ)) y
        - B0579.pd 1 (B0579.pd j (U n σ)) y :=
      pd_sub' (diff_pd (hU2 (n + 1)) j) (diff_pd (hU2 n) j) 1 y
    have q0 := abs_pd2_sub_le (hU2 (n + 1)) (hU2 n) 0 j y
    have q1 := abs_pd2_sub_le (hU2 (n + 1)) (hU2 n) 1 j y
    have := hW n y
    rw [p0, p1]
    change _ ≤ W2 (g n) y at q0 q1
    linarith
  have hh0 : Summable (fun n => h n 0) := by
    refine Summable.of_norm_bounded hε (fun n => ?_)
    rw [Real.norm_eq_abs]
    have e : B0579.pd j (g n) 0 = h n 0 :=
      pd_sub' (c2_diff (hU2 (n + 1))) (c2_diff (hU2 n)) j 0
    rw [← e]
    exact (abs_pd_le (g n) 0 j).trans (hW n 0)
  have hH : HasFDerivAt (fun y => ∑' n, h n y) (∑' n, fderiv ℝ (h n) x) x :=
    hasFDerivAt_tsum (u := fun n => 2 * ε n) hε2 (fun n y => (hhd n y).hasFDerivAt) hhn hh0 x
  have hsumh : Summable (fun n => fderiv ℝ (h n) x) :=
    Summable.of_norm_bounded hε2 (fun n => hhn n x)
  have hP : picD1 U j σ = fun y => B0579.pd j (U 0 σ) y + ∑' n, h n y := rfl
  have hA : HasFDerivAt (fun y => B0579.pd j (U 0 σ) y + ∑' n, h n y)
      (fderiv ℝ (B0579.pd j (U 0 σ)) x + ∑' n, fderiv ℝ (h n) x) x :=
    (((diff_pd (hU2 0) j) x).hasFDerivAt).add hH
  show (fderiv ℝ (picD1 U j σ) x) (B0579.dir i) = _
  rw [hP, hA.fderiv, ContinuousLinearMap.add_apply]
  unfold picD2
  congr 1
  have : (∑' n, fderiv ℝ (h n) x) (B0579.dir i) = ∑' n, fderiv ℝ (h n) x (B0579.dir i) := by
    have := ContinuousLinearMap.map_tsum
      (ContinuousLinearMap.apply ℝ ℝ (B0579.dir i)) hsumh
    simpa using this
  rw [this]
  refine tsum_congr (fun n => ?_)
  have := pd_sub' (diff_pd (hU2 (n + 1)) j) (diff_pd (hU2 n) j) i x
  unfold B0579.pd at this
  exact this

end CylPDE

end UnforcedLeray.Short.IIb
