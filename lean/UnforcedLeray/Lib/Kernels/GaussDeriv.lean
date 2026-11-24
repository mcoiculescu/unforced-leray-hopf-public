import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Iterated derivatives of the heat kernel on ℝ³ (helper for INF22 K1, K4)

Helper module of `Lib/Kernels.lean` (blueprint INF22, scoping note

The note's target G1 belongs to another block; this module proves only what K1–K4 consume:

* `norm_iteratedFDeriv_gaussProfile_le`: ‖Dⁿ e^{-|z|²}‖ ≤ Mₙ e^{-|z|²/2} (Faà di Bruno,
  Mathlib `norm_iteratedFDeriv_comp_le`, as in BP3);
* `iteratedFDeriv_heatKernel_eq`: the dilation formula
  Dⁿ G_a(x) = (4πa)^{-3/2} cₐⁿ (Dⁿ e^{-|·|²})(cₐ x), cₐ = (1/2) a^{-1/2};
* `norm_iteratedFDeriv_heatKernel_le`: ‖Dⁿ G_a(x)‖ ≤ Cₙ a^{-(3+n)/2} e^{-|x|²/(8a)} for a > 0;
* `continuousOn_iteratedFDeriv_heatKernel`: continuity in the time variable a on (0, ∞).

Here `G_a = UnforcedLeray.Heat.kernel a` is the compiled kernel (4πa)^{-3/2} e^{-|x|²/(4a)}.
The two scaling lemmas are copied from NonUniqueEuler,
`NonUniqueEuler/lean/NonUniqueEuler/P/Infra/CkNorm/Scaling.lean` (theorems
`iteratedFDeriv_comp_smul_right_of_ne`, `iteratedFDeriv_const_smul_left`,
`iteratedFDeriv_comp_smul`), with the namespace renamed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology Nat

namespace UnforcedLeray.Kernels

section Scaling

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Right composition with `z ↦ c • z`, `c ≠ 0` (copied from NonUniqueEuler
`P/Infra/CkNorm/Scaling.lean`). -/
theorem iteratedFDeriv_comp_smul_right_of_ne (q : ℕ) (h : E → F) {c : ℝ} (hc : c ≠ 0) (y : E) :
    iteratedFDeriv ℝ q (fun z => h (c • z)) y = c ^ q • iteratedFDeriv ℝ q h (c • y) := by
  set g : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc) with hgdef
  have hg : ∀ z, g z = c • z := fun z => rfl
  have hfun : (fun z => h (c • z)) = h ∘ g := by
    funext z
    simp [hg]
  have key := g.iteratedFDerivWithin_comp_right h uniqueDiffOn_univ (mem_univ (g y)) q
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at key
  rw [hfun, key, hg]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearEquiv.coe_coe, hg]
  rw [show (fun i => c • m i) = fun i => (fun _ : Fin q => c) i • m i from rfl,
    ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

/-- Left multiplication by a scalar commutes with `iteratedFDeriv` (copied from NonUniqueEuler
`P/Infra/CkNorm/Scaling.lean`). -/
theorem iteratedFDeriv_const_smul_left (q : ℕ) (f : E → F) (a : ℝ) (y : E) :
    iteratedFDeriv ℝ q (fun z => a • f z) y = a • iteratedFDeriv ℝ q f y := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul]
    cases q with
    | zero => ext m; simp
    | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; rfl
  · set g : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 a ha) with hgdef
    have hg : ∀ v, g v = a • v := fun v => rfl
    have hfun : (fun z => a • f z) = g ∘ f := by
      funext z
      simp [hg]
    rw [hfun, g.iteratedFDeriv_comp_left]
    ext m
    simp [hg]

/-- The scaling rule `∇^q (a V(c ·))(y) = a c^q (∇^q V)(c y)` (copied from NonUniqueEuler
`P/Infra/CkNorm/Scaling.lean`). -/
theorem iteratedFDeriv_comp_smul (q : ℕ) (h : E → F) (a c : ℝ) (y : E) :
    iteratedFDeriv ℝ q (fun z => a • h (c • z)) y = (a * c ^ q) • iteratedFDeriv ℝ q h (c • y) := by
  rw [iteratedFDeriv_const_smul_left q (fun z => h (c • z)) a y, mul_smul]
  congr 1
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul]
    cases q with
    | zero => ext m; simp
    | succ n =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp
  · exact iteratedFDeriv_comp_smul_right_of_ne q h hc y

end Scaling

/-- The fixed Gaussian profile `z ↦ e^{-|z|²}` on ℝ³. -/
def gaussProfile (z : Space) : ℝ := Real.exp (-‖z‖ ^ 2)

theorem gaussProfile_smooth : ContDiff ℝ ∞ gaussProfile := by
  unfold gaussProfile
  exact ((contDiff_id.norm_sq ℝ).neg).exp

/-- The quadratic exponent `z ↦ -|z|²`. -/
private def negSq (z : Space) : ℝ := -‖z‖ ^ 2

private theorem negSq_smooth : ContDiff ℝ ∞ negSq := (contDiff_id.norm_sq ℝ).neg

private def negSqLin : Space →L[ℝ] Space →L[ℝ] ℝ := -(2 • innerSL ℝ)

private theorem fderiv_negSq : fderiv ℝ negSq = fun z => negSqLin z := by
  funext z
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg
  exact h.fderiv

private theorem norm_negSqLin_le : ‖negSqLin‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  simp only [negSqLin, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, norm_neg]
  calc ‖2 • innerSL ℝ v‖ ≤ 2 * ‖innerSL ℝ v‖ := by
        simpa using norm_nsmul_le (n := 2) (a := innerSL ℝ v)
    _ = 2 * ‖v‖ := by rw [innerSL_apply_norm]

private theorem norm_iteratedFDeriv_negSq_le (i : ℕ) (hi : 1 ≤ i) (z : Space) :
    ‖iteratedFDeriv ℝ i negSq z‖ ≤ (2 * (1 + ‖z‖)) ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, fderiv_negSq]
  have hpos : (1 : ℝ) ≤ 2 * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
  rcases k with _ | _ | k
  · simp only [norm_iteratedFDeriv_zero, zero_add, pow_one]
    calc ‖negSqLin z‖ ≤ ‖negSqLin‖ * ‖z‖ := negSqLin.le_opNorm z
      _ ≤ 2 * ‖z‖ := by gcongr; exact norm_negSqLin_le
      _ ≤ 2 * (1 + ‖z‖) := by linarith
  · rw [norm_iteratedFDeriv_one, negSqLin.fderiv]
    calc ‖negSqLin‖ ≤ 2 := norm_negSqLin_le
      _ ≤ (2 * (1 + ‖z‖)) ^ (0 + 1 + 1) := by
          rw [show (0 + 1 + 1 : ℕ) = 2 from rfl]
          have h2 : (2 : ℝ) ≤ 2 * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
          nlinarith
  · rw [← norm_iteratedFDeriv_fderiv]
    have : fderiv ℝ (fun z => negSqLin z) = fun _ => negSqLin := by
      funext w
      exact negSqLin.fderiv
    rw [this, iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, norm_zero]
    positivity

private theorem norm_iteratedFDeriv_exp_le (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ ≤ Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

/-- `(1 + r)ⁿ e^{-r²/2} ≤ n! e^{3/2}` for `r ≥ 0`. -/
theorem one_add_pow_mul_exp_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ n * Real.exp (-r ^ 2 / 2) ≤ n ! * Real.exp (3 / 2) := by
  have h1 : (1 + r) ^ n ≤ n ! * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + r) (by linarith) n
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hf] at this
    linarith
  calc (1 + r) ^ n * Real.exp (-r ^ 2 / 2)
      ≤ (n ! * Real.exp (1 + r)) * Real.exp (-r ^ 2 / 2) := by gcongr
    _ = n ! * Real.exp (1 + r - r ^ 2 / 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ n ! * Real.exp (3 / 2) := by
        gcongr
        nlinarith [sq_nonneg (r - 1)]

/-- Derivative bound for the Gaussian profile: ‖Dⁿ e^{-|z|²}‖ ≤ (n!)² 2ⁿ e^{3/2} e^{-|z|²/2}
(INF22 BP3). -/
theorem norm_iteratedFDeriv_gaussProfile_le (n : ℕ) (z : Space) :
    ‖iteratedFDeriv ℝ n gaussProfile z‖ ≤
      ((n ! : ℝ) ^ 2 * 2 ^ n * Real.exp (3 / 2)) * Real.exp (-‖z‖ ^ 2 / 2) := by
  have hcomp : gaussProfile = Real.exp ∘ negSq := rfl
  have hFdB := norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp negSq_smooth
    (by exact_mod_cast le_top) z (n := n) (C := Real.exp (negSq z)) (D := 2 * (1 + ‖z‖))
    (fun i _ => norm_iteratedFDeriv_exp_le i (negSq z))
    (fun i hi _ => norm_iteratedFDeriv_negSq_le i hi z)
  rw [hcomp]
  refine hFdB.trans ?_
  have hkey := one_add_pow_mul_exp_le n (norm_nonneg z)
  have he : Real.exp (negSq z) = Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (-‖z‖ ^ 2 / 2) := by
    rw [← Real.exp_add]; unfold negSq; ring_nf
  rw [he, mul_pow]
  have hf : (0 : ℝ) ≤ n ! := by positivity
  have hE : 0 ≤ Real.exp (-‖z‖ ^ 2 / 2) := (Real.exp_pos _).le
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  calc (n ! : ℝ) * (Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (-‖z‖ ^ 2 / 2)) * (2 ^ n * (1 + ‖z‖) ^ n)
      = (n ! : ℝ) * 2 ^ n * Real.exp (-‖z‖ ^ 2 / 2) *
          ((1 + ‖z‖) ^ n * Real.exp (-‖z‖ ^ 2 / 2)) := by ring
    _ ≤ (n ! : ℝ) * 2 ^ n * Real.exp (-‖z‖ ^ 2 / 2) * (n ! * Real.exp (3 / 2)) := by
        gcongr
    _ = ((n ! : ℝ) ^ 2 * 2 ^ n * Real.exp (3 / 2)) * Real.exp (-‖z‖ ^ 2 / 2) := by ring

/-- The dilation factor `cₐ = (1/2) a^{-1/2}` of the heat kernel at time `a`. -/
def heatScale (a : ℝ) : ℝ := (1 / 2) * a ^ (-(1 / 2 : ℝ))

theorem heatScale_sq {a : ℝ} (ha : 0 < a) : heatScale a ^ 2 = (4 * a)⁻¹ := by
  unfold heatScale
  rw [mul_pow, ← Real.rpow_natCast (a ^ _), ← Real.rpow_mul ha.le]
  norm_num [Real.rpow_neg_one]
  ring

theorem heatScale_pow {a : ℝ} (ha : 0 < a) (n : ℕ) :
    heatScale a ^ n = (1 / 2) ^ n * a ^ (-(n : ℝ) / 2) := by
  unfold heatScale
  rw [mul_pow, ← Real.rpow_natCast (a ^ _), ← Real.rpow_mul ha.le]
  congr 2
  ring

/-- The heat kernel as a dilated Gaussian profile. -/
theorem heatKernel_eq_dilate {a : ℝ} (ha : 0 < a) :
    Heat.kernel a = fun x => (4 * Real.pi * a) ^ (-(3 : ℝ) / 2) • gaussProfile (heatScale a • x) := by
  funext x
  rw [Heat.kernel_formula, smul_eq_mul, gaussProfile, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, heatScale_sq ha]
  ring_nf

/-- The dilation formula for the iterated derivatives of the heat kernel. -/
theorem iteratedFDeriv_heatKernel_eq {a : ℝ} (ha : 0 < a) (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (Heat.kernel a) x =
      ((4 * Real.pi * a) ^ (-(3 : ℝ) / 2) * heatScale a ^ n) •
        iteratedFDeriv ℝ n gaussProfile (heatScale a • x) := by
  rw [heatKernel_eq_dilate ha]
  exact iteratedFDeriv_comp_smul n gaussProfile _ _ x

theorem heatKernel_smooth (a : ℝ) : ContDiff ℝ ∞ (Heat.kernel a) :=
  Heat.Gaussian.kernel_smooth (4 * a)

/-- The constant of `norm_iteratedFDeriv_heatKernel_le`. -/
def heatDerivConst (n : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (1 / 2) ^ n * ((n ! : ℝ) ^ 2 * 2 ^ n * Real.exp (3 / 2))

theorem heatDerivConst_pos (n : ℕ) : 0 < heatDerivConst n := by
  unfold heatDerivConst
  have : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  positivity

/-- Gaussian majorant of the heat-kernel derivatives (INF22 G1 at d = 3, BP3):
‖Dⁿ G_a(x)‖ ≤ Cₙ a^{-(3+n)/2} e^{-|x|²/(8a)} for every `a > 0`. -/
theorem norm_iteratedFDeriv_heatKernel_le (n : ℕ) {a : ℝ} (ha : 0 < a) (x : Space) :
    ‖iteratedFDeriv ℝ n (Heat.kernel a) x‖ ≤
      heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a)) := by
  rw [iteratedFDeriv_heatKernel_eq ha, norm_smul]
  have hpos : 0 ≤ (4 * Real.pi * a) ^ (-(3 : ℝ) / 2) * heatScale a ^ n := by
    unfold heatScale; positivity
  rw [Real.norm_of_nonneg hpos]
  have hb := norm_iteratedFDeriv_gaussProfile_le n (heatScale a • x)
  have hexp : Real.exp (-‖heatScale a • x‖ ^ 2 / 2) = Real.exp (-‖x‖ ^ 2 / (8 * a)) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, heatScale_sq ha]
    congr 1
    field_simp
    ring
  rw [hexp] at hb
  calc (4 * Real.pi * a) ^ (-(3 : ℝ) / 2) * heatScale a ^ n *
        ‖iteratedFDeriv ℝ n gaussProfile (heatScale a • x)‖
      ≤ (4 * Real.pi * a) ^ (-(3 : ℝ) / 2) * heatScale a ^ n *
        (((n ! : ℝ) ^ 2 * 2 ^ n * Real.exp (3 / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a))) := by
        gcongr
    _ = heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a)) := by
        rw [heatScale_pow ha, Real.mul_rpow (by positivity) ha.le]
        have hsplit : a ^ (-((3 + n : ℝ) / 2)) = a ^ (-(3 : ℝ) / 2) * a ^ (-(n : ℝ) / 2) := by
          rw [← Real.rpow_add ha]; congr 1; ring
        rw [hsplit, heatDerivConst]
        ring

/-- Continuity of `a ↦ Dⁿ G_a(x)` on `(0, ∞)`. -/
theorem continuousOn_iteratedFDeriv_heatKernel (n : ℕ) (x : Space) :
    ContinuousOn (fun a => iteratedFDeriv ℝ n (Heat.kernel a) x) (Ioi 0) := by
  have hcont : ContinuousOn (fun a : ℝ => ((4 * Real.pi * a) ^ (-(3 : ℝ) / 2) * heatScale a ^ n) •
      iteratedFDeriv ℝ n gaussProfile (heatScale a • x)) (Ioi 0) := by
    have hscale : ContinuousOn heatScale (Ioi 0) := by
      unfold heatScale
      exact continuousOn_const.mul
        (ContinuousOn.rpow_const continuousOn_id (fun a ha => Or.inl (ne_of_gt ha)))
    have hD : Continuous (iteratedFDeriv ℝ n gaussProfile) :=
      gaussProfile_smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have h1 : ContinuousOn (fun a : ℝ => (4 * Real.pi * a) ^ (-(3 : ℝ) / 2) * heatScale a ^ n)
        (Ioi 0) := by
      refine ContinuousOn.mul ?_ (hscale.pow n)
      exact ContinuousOn.rpow_const (continuousOn_const.mul continuousOn_id)
        (fun a ha => Or.inl (ne_of_gt (by have : (0:ℝ) < a := ha; positivity)))
    have h2 : ContinuousOn (fun a : ℝ => iteratedFDeriv ℝ n gaussProfile (heatScale a • x))
        (Ioi 0) := hD.comp_continuousOn (hscale.smul continuousOn_const)
    exact h1.smul h2
  exact hcont.congr (fun a ha => iteratedFDeriv_heatKernel_eq ha n x)

end UnforcedLeray.Kernels
