import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# `WtdJetInterp` (SP 494-496): unit-patch interpolation of weighted bounds

Source: `the November 2 reference manuscript`,
SP 494-496.  Proof: induction on the derivative order `k` with the strip shrinking by
`d = 1/(i+1)` at each step.  One step: `G = D^k f`, `H = D^{k+1} f`, `‖fderiv G y‖ = ‖H y‖`,
`fderiv G z = curryLeft (H z)` (isometry), `H` is Lipschitz on a convex patch `B` with constant the
bound of `D^{k+2} f`, and the mean value inequality on `G - fderiv G y` gives
`h ‖fderiv G y w‖ ≤ 2 sup‖G‖ + M h^2` with `h = d / (1+|π y.2|)^m`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff

/-- One step of the interpolation (private helper). -/
private theorem wtdJetInterp_step {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (π : E →L[ℝ] ℝ) (hπ : ‖π‖ ≤ 1) (f : ℝ × E → ℝ) (S d : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) (k : ℕ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y : ℝ × E, 0 < y.1 → y.1 ≤ S + 1 → ‖iteratedFDeriv ℝ (k + 2) f y‖ ≤ M)
    (IH : ∀ m : ℕ, ∃ C : ℝ, ∀ y : ℝ × E, 0 < y.1 → y.1 ≤ S + 1 - k * d →
      (1 + |π y.2|) ^ m * ‖iteratedFDeriv ℝ k f y‖ ≤ C) (m : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ × E, 0 < y.1 → y.1 ≤ S + 1 - (k + 1) * d →
      (1 + |π y.2|) ^ m * ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := IH (2 * m)
  refine ⟨2 * 4 ^ m * C / d + M * d, fun y hy0 hyT => ?_⟩
  have hU : IsOpen (Ioi (0:ℝ) ×ˢ (univ : Set E)) := isOpen_Ioi.prod isOpen_univ
  have hkd : (0:ℝ) ≤ k * d := by positivity
  have hkd1 : ((k:ℝ) + 1) * d = k * d + d := by ring
  have hyT' : y.1 + d ≤ S + 1 - k * d := by linarith
  -- smoothness of `D^k f` and `D^{k+1} f` on the open half-space
  have hGd : ∀ z : ℝ × E, 0 < z.1 → DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z := by
    intro z hz
    have hc : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hU.mem_nhds ⟨hz, mem_univ _⟩)
    exact (hc.iteratedFDeriv_right (m := 1) (i := k) (by exact_mod_cast le_top)).differentiableAt
      one_ne_zero
  have hHd : ∀ z : ℝ × E, 0 < z.1 → DifferentiableAt ℝ (iteratedFDeriv ℝ (k + 1) f) z := by
    intro z hz
    have hc : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hU.mem_nhds ⟨hz, mem_univ _⟩)
    exact (hc.iteratedFDeriv_right (m := 1) (i := k + 1) (by exact_mod_cast le_top)).differentiableAt
      one_ne_zero
  -- the derivative of `D^k f` is the curried `D^{k+1} f`
  have hrel : ∀ z : ℝ × E, fderiv ℝ (iteratedFDeriv ℝ k f) z =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ × E) ℝ)
        (iteratedFDeriv ℝ (k + 1) f z) := by
    intro z
    have h := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := f) (n := k)) z
    simp only [Function.comp_apply] at h
    rw [h, LinearIsometryEquiv.apply_symm_apply]
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ × E) ℝ with he
  have hmapsub : ∀ a b : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℝ × E) ℝ,
      e (a - b) = e a - e b := fun a b => e.toLinearEquiv.toLinearMap.map_sub a b
  -- the weight `a`, the step `h`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (1 + |π y.2|) ^ m := ⟨_, rfl⟩
  rw [← ha]
  have ha1 : 1 ≤ a := by
    rw [ha]; exact one_le_pow₀ (by linarith [abs_nonneg (π y.2)])
  have ha0 : 0 < a := by linarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = d / a := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; exact div_pos hd0 ha0
  have hhd : h ≤ d := by rw [hh]; exact div_le_self hd0.le ha1
  have hh1 : h ≤ 1 := hhd.trans hd1
  have hha : h * a = d := by rw [hh]; exact div_mul_cancel₀ d ha0.ne'
  -- the convex patch
  obtain ⟨B, hB⟩ : ∃ B : Set (ℝ × E),
      B = (Ioc (0:ℝ) (S + 1 - k * d) ×ˢ (univ : Set E)) ∩ Metric.closedBall y h := ⟨_, rfl⟩
  have hBz : ∀ z ∈ B, 0 < z.1 ∧ z.1 ≤ S + 1 - k * d ∧ dist z y ≤ h := by
    intro z hz
    rw [hB] at hz
    obtain ⟨⟨⟨h1, h2⟩, -⟩, h3⟩ := hz
    exact ⟨h1, h2, Metric.mem_closedBall.mp h3⟩
  have hyB : y ∈ B := by
    rw [hB]
    exact ⟨⟨⟨hy0, by linarith⟩, mem_univ _⟩, Metric.mem_closedBall_self hh0.le⟩
  have hBconv : Convex ℝ B := by
    rw [hB]
    exact ((convex_Ioc _ _).prod convex_univ).inter (convex_closedBall y h)
  -- bound on `G = D^k f` over the patch
  have hGB : ∀ z ∈ B, a ^ 2 * ‖iteratedFDeriv ℝ k f z‖ ≤ 4 ^ m * C := by
    intro z hz
    obtain ⟨hz0, hzT, hzd⟩ := hBz z hz
    have hzd' : ‖z - y‖ ≤ h := by rwa [dist_eq_norm] at hzd
    have hyz : ‖y - z‖ ≤ 1 := by rw [norm_sub_rev]; linarith
    have hsnd : ‖y.2 - z.2‖ ≤ 1 := by
      have h1 : ‖(y - z).2‖ ≤ ‖y - z‖ := norm_snd_le (y - z)
      rw [Prod.snd_sub] at h1
      linarith
    have hpi : |π y.2 - π z.2| ≤ 1 := by
      rw [← map_sub, ← Real.norm_eq_abs]
      calc ‖π (y.2 - z.2)‖ ≤ ‖π‖ * ‖y.2 - z.2‖ := π.le_opNorm _
        _ ≤ 1 * 1 := mul_le_mul hπ hsnd (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have hWz : 1 + |π y.2| ≤ 2 * (1 + |π z.2|) := by
      have := abs_sub_abs_le_abs_sub (π y.2) (π z.2)
      have := abs_nonneg (π z.2)
      linarith
    have hapow : a ^ 2 ≤ 4 ^ m * (1 + |π z.2|) ^ (2 * m) := by
      have e1 : a ^ 2 = (1 + |π y.2|) ^ (2 * m) := by
        rw [ha, ← pow_mul, mul_comm]
      have e2 : (4:ℝ) ^ m * (1 + |π z.2|) ^ (2 * m) = (2 * (1 + |π z.2|)) ^ (2 * m) := by
        rw [mul_pow, pow_mul (2:ℝ) 2 m]; norm_num
      rw [e1, e2]
      exact pow_le_pow_left₀ (by positivity) hWz _
    calc a ^ 2 * ‖iteratedFDeriv ℝ k f z‖
        ≤ (4 ^ m * (1 + |π z.2|) ^ (2 * m)) * ‖iteratedFDeriv ℝ k f z‖ :=
          mul_le_mul_of_nonneg_right hapow (norm_nonneg _)
      _ = 4 ^ m * ((1 + |π z.2|) ^ (2 * m) * ‖iteratedFDeriv ℝ k f z‖) := by ring
      _ ≤ 4 ^ m * C := mul_le_mul_of_nonneg_left (hC z hz0 hzT) (by positivity)
  -- Lipschitz bound of `H = D^{k+1} f` on the patch
  have hbdH : ∀ x ∈ B, ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) x‖ ≤ M := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    exact hM x (hBz x hx).1 (by linarith [(hBz x hx).2.1])
  have hHlip : ∀ z ∈ B,
      ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f y‖ ≤ M * ‖z - y‖ :=
    fun z hz => Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := iteratedFDeriv ℝ (k + 1) f) (s := B) (C := M)
      (fun x hx => hHd x (hBz x hx).1) hbdH hBconv hyB hz
  have hGlip : ∀ z ∈ B,
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z - fderiv ℝ (iteratedFDeriv ℝ k f) y‖ ≤ M * ‖z - y‖ := by
    intro z hz
    rw [hrel z, hrel y, ← hmapsub, LinearIsometryEquiv.norm_map]
    exact hHlip z hz
  set L := fderiv ℝ (iteratedFDeriv ℝ k f) y with hLdef
  have hφfd : ∀ x ∈ B, ‖fderiv ℝ (fun z => iteratedFDeriv ℝ k f z - L z) x‖ ≤ M * h := by
    intro x hx
    rw [fderiv_fun_sub (hGd x (hBz x hx).1) L.differentiableAt, ContinuousLinearMap.fderiv]
    have hxy : ‖x - y‖ ≤ h := by
      have := (hBz x hx).2.2
      rwa [dist_eq_norm] at this
    exact (hGlip x hx).trans (mul_le_mul_of_nonneg_left hxy hM0)
  have hφmean : ∀ zh ∈ B,
      ‖(iteratedFDeriv ℝ k f zh - L zh) - (iteratedFDeriv ℝ k f y - L y)‖
        ≤ (M * h) * ‖zh - y‖ := fun zh hzh =>
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => iteratedFDeriv ℝ k f z - L z) (s := B) (C := M * h)
      (fun x hx => (hGd x (hBz x hx).1).sub L.differentiableAt) hφfd hBconv hyB hzh
  -- the core estimate on unit vectors with nonnegative first coordinate
  have hcore : ∀ w : ℝ × E, 0 ≤ w.1 → ‖w‖ ≤ 1 →
      a * ‖L w‖ ≤ 2 * 4 ^ m * C / d + M * d := by
    intro w hw0 hw1
    have hw1' : w.1 ≤ 1 := by
      have := norm_fst_le w
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans hw1)
    have hzB : y + h • w ∈ B := by
      rw [hB]
      refine ⟨⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
      · rw [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith [mul_nonneg hh0.le hw0]
      · rw [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith [mul_le_mul_of_nonneg_left hw1' hh0.le]
      · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hh0]
        exact mul_le_of_le_one_right hh0.le hw1
    have hzy_norm : ‖y + h • w - y‖ ≤ h := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh0]
      exact mul_le_of_le_one_right hh0.le hw1
    have e : (iteratedFDeriv ℝ k f (y + h • w) - L (y + h • w))
        - (iteratedFDeriv ℝ k f y - L y)
        = (iteratedFDeriv ℝ k f (y + h • w) - iteratedFDeriv ℝ k f y) - h • L w := by
      rw [map_add, map_smul]; abel
    have h3 : ‖(iteratedFDeriv ℝ k f (y + h • w) - iteratedFDeriv ℝ k f y) - h • L w‖
        ≤ (M * h) * h := by
      rw [← e]
      exact (hφmean _ hzB).trans
        (mul_le_mul_of_nonneg_left hzy_norm (mul_nonneg hM0 hh0.le))
    have h3' : ‖(iteratedFDeriv ℝ k f (y + h • w) - iteratedFDeriv ℝ k f y) - h • L w‖
        ≤ M * h ^ 2 := by
      have : (M * h) * h = M * h ^ 2 := by ring
      linarith
    have hsplit : ‖h • L w‖ ≤
        ‖iteratedFDeriv ℝ k f (y + h • w)‖ + ‖iteratedFDeriv ℝ k f y‖ + M * h ^ 2 := by
      have h4 := norm_sub_le (iteratedFDeriv ℝ k f (y + h • w) - iteratedFDeriv ℝ k f y)
        ((iteratedFDeriv ℝ k f (y + h • w) - iteratedFDeriv ℝ k f y) - h • L w)
      rw [sub_sub_cancel] at h4
      have h5 := norm_sub_le (iteratedFDeriv ℝ k f (y + h • w)) (iteratedFDeriv ℝ k f y)
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh0] at hsplit
    have hGzh := hGB _ hzB
    have hGy := hGB y hyB
    have hXd : d * a * ‖L w‖ = a ^ 2 * (h * ‖L w‖) := by rw [← hha]; ring
    have hMd : a ^ 2 * (M * h ^ 2) = M * d ^ 2 := by rw [← hha]; ring
    have hmul := mul_le_mul_of_nonneg_left hsplit (sq_nonneg a)
    have hexp : a ^ 2 * (‖iteratedFDeriv ℝ k f (y + h • w)‖ + ‖iteratedFDeriv ℝ k f y‖
        + M * h ^ 2) = a ^ 2 * ‖iteratedFDeriv ℝ k f (y + h • w)‖
          + a ^ 2 * ‖iteratedFDeriv ℝ k f y‖ + a ^ 2 * (M * h ^ 2) := by ring
    have key : d * a * ‖L w‖ ≤ 2 * 4 ^ m * C + M * d ^ 2 := by
      linarith
    have hfin : a * ‖L w‖ ≤ (2 * 4 ^ m * C + M * d ^ 2) / d := by
      rw [le_div_iff₀ hd0]; linarith
    have e3 : (2 * 4 ^ m * C + M * d ^ 2) / d = 2 * 4 ^ m * C / d + M * d := by
      field_simp
    linarith
  have hsign : ∀ w : ℝ × E, ‖w‖ ≤ 1 → a * ‖L w‖ ≤ 2 * 4 ^ m * C / d + M * d := by
    intro w hw
    rcases le_total 0 w.1 with h0 | h0
    · exact hcore w h0 hw
    · have h1 := hcore (-w) (by rw [Prod.fst_neg]; linarith) (by rw [norm_neg]; exact hw)
      rwa [map_neg, norm_neg] at h1
  have hC0 : 0 ≤ C := by
    have hGy := hGB y hyB
    have h0 : 0 ≤ a ^ 2 * ‖iteratedFDeriv ℝ k f y‖ := by positivity
    have h4 : (0:ℝ) < 4 ^ m := by positivity
    by_contra hneg
    rw [not_le] at hneg
    have : 4 ^ m * C < 0 := mul_neg_of_pos_of_neg h4 hneg
    linarith
  have hKnn : 0 ≤ 2 * 4 ^ m * C / d + M * d :=
    add_nonneg (div_nonneg (mul_nonneg (by positivity) hC0) hd0.le) (mul_nonneg hM0 hd0.le)
  have hall : ∀ w : ℝ × E, ‖L w‖ ≤ ((2 * 4 ^ m * C / d + M * d) / a) * ‖w‖ := by
    intro w
    by_cases hw : w = 0
    · rw [hw]; simp
    · have hc : 0 < ‖w‖ := norm_pos_iff.mpr hw
      obtain ⟨v, hv⟩ : ∃ v : ℝ × E, v = ‖w‖⁻¹ • w := ⟨_, rfl⟩
      have hvn : ‖v‖ = 1 := by
        rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
      have hwv : w = ‖w‖ • v := by
        rw [hv, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
      have hLv : ‖L v‖ ≤ (2 * 4 ^ m * C / d + M * d) / a := by
        have := hsign v hvn.le
        rw [le_div_iff₀ ha0]
        linarith
      calc ‖L w‖ = ‖w‖ * ‖L v‖ := by
            conv_lhs => rw [hwv]
            rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖w‖ * ((2 * 4 ^ m * C / d + M * d) / a) := mul_le_mul_of_nonneg_left hLv hc.le
        _ = ((2 * 4 ^ m * C / d + M * d) / a) * ‖w‖ := by ring
  have hLnorm : ‖L‖ ≤ (2 * 4 ^ m * C / d + M * d) / a :=
    ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hKnn ha0.le) hall
  have hyn : ‖iteratedFDeriv ℝ (k + 1) f y‖ = ‖L‖ := by
    rw [hLdef, ← norm_fderiv_iteratedFDeriv]
  rw [hyn]
  calc a * ‖L‖ ≤ a * ((2 * 4 ^ m * C / d + M * d) / a) := mul_le_mul_of_nonneg_left hLnorm ha0.le
    _ = 2 * 4 ^ m * C / d + M * d := by field_simp

/-- **Weighted mixed derivatives, unit-patch interpolation** (SP 494-496). Every weighted
derivative `(1+|π x|)^m ‖D^i f‖` on `0 < s ≤ S` is bounded, from the unweighted bounds of
`D^i f` (`i ≥ 1`) and the weighted bound of `f` on `0 < s ≤ S + 1`. -/
theorem wtdJetInterp : UnforcedLeray.Short.PartIIIb.Concrete.WtdJetInterp := by
  unfold WtdJetInterp
  intro E _ _ π hπ f S hf hD hW m i
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 / ((i : ℝ) + 1) := ⟨_, rfl⟩
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 := by
    rw [hd, div_le_one (by positivity)]; linarith
  have hid : (i:ℝ) * d ≤ 1 := by
    rw [hd, mul_one_div, div_le_one (by positivity)]; linarith
  have key : ∀ k : ℕ, k ≤ i → ∀ m' : ℕ, ∃ C : ℝ, ∀ y : ℝ × E, 0 < y.1 →
      y.1 ≤ S + 1 - k * d → (1 + |π y.2|) ^ m' * ‖iteratedFDeriv ℝ k f y‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      intro _ m'
      obtain ⟨C, hC⟩ := hW m'
      refine ⟨C, fun y hy0 hyS => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      apply hC y hy0
      simpa using hyS
    | succ k ih =>
      intro hk m'
      obtain ⟨M, hM⟩ := hD (k + 2) (by omega)
      have := wtdJetInterp_step π hπ f S d hf k hd0 hd1 (max M 0) (le_max_right _ _)
        (fun y hy0 hyS => (hM y hy0 hyS).trans (le_max_left _ _))
        (fun m'' => ih (by omega) m'') m'
      push_cast
      exact this
  obtain ⟨C, hC⟩ := key i le_rfl m
  exact ⟨C, fun y hy0 hyS => hC y hy0 (by linarith)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
