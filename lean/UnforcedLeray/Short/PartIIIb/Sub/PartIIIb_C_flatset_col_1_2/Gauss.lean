import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A Gaussian Schwartz function on `ℝ × ℝ` (helper of `PartIII-b:C/flatset/col/1/2/3`)

Source `the November 2 reference manuscript` 4976, 4988 (the Gaussian factor
`exp(-(u^2+v^2)/(4a))` of `ftPh`).  Every iterated derivative of `g = exp(-b(u^2+v^2))` is `g` times
a function of temperate growth, which gives the Schwartz decay.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatTermAux

def gq (b : ℝ) (y : ℝ × ℝ) : ℝ := Real.exp (-(b * (y.1 ^ 2 + y.2 ^ 2)))

def gl (b : ℝ) (y : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-(2 * b)) • (y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem gq_hasFDerivAt (b : ℝ) (y : ℝ × ℝ) : HasFDerivAt (gq b) (gq b y • gl b y) y := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    hasFDerivAt_snd
  have h3 : HasFDerivAt (fun y : ℝ × ℝ => Real.exp (-(b * (y.1 * y.1 + y.2 * y.2)))) _ y :=
    (((h1.fun_mul h1).fun_add (h2.fun_mul h2)).const_mul b).fun_neg.exp
  have e : (fun y : ℝ × ℝ => Real.exp (-(b * (y.1 * y.1 + y.2 * y.2)))) = gq b := by
    funext z; simp only [gq]; congr 3; ring
  rw [e] at h3
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  simp [gl, gq, sq]
  ring

theorem gq_fderiv (b : ℝ) : fderiv ℝ (gq b) = fun y => gq b y • gl b y :=
  funext fun y => (gq_hasFDerivAt b y).fderiv

theorem gq_contDiff (b : ℝ) : ContDiff ℝ ∞ (gq b) := by
  unfold gq
  fun_prop

theorem gl_temperate (b : ℝ) : (gl b).HasTemperateGrowth := by
  have hX : (fun y : ℝ × ℝ => y.1).HasTemperateGrowth :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hY : (fun y : ℝ × ℝ => y.2).HasTemperateGrowth :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  have hC : ∀ c : (ℝ × ℝ) →L[ℝ] ℝ, (fun _ : ℝ × ℝ => c).HasTemperateGrowth :=
    fun c => Function.HasTemperateGrowth.const c
  unfold gl
  exact (Function.HasTemperateGrowth.const (-(2 * b))).smul
    ((hX.smul (hC _)).add (hY.smul (hC _)))


theorem tg_fderiv {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {p : ℝ × ℝ → G}
    (hp : p.HasTemperateGrowth) : (fderiv ℝ p).HasTemperateGrowth := by
  refine ⟨hp.1.fderiv_right (by simp), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hp.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h x⟩

theorem key (b : ℝ) : ∀ n : ℕ, ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : ℝ × ℝ → G), p.HasTemperateGrowth →
    ∃ r : ℝ × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) G, r.HasTemperateGrowth ∧
      ∀ y, iteratedFDeriv ℝ n (fun z => gq b z • p z) y = gq b y • r y := by
  intro n
  induction n with
  | zero =>
    intro G _ _ p hp
    refine ⟨fun y => (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) G).symm (p y), ?_, fun y => ?_⟩
    · exact ((continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) G).symm.toContinuousLinearEquiv.hasTemperateGrowth).comp hp
    · rw [iteratedFDeriv_zero_eq_comp]
      simp [map_smul]
  | succ n ih =>
    intro G _ _ p hp
    have hd : Differentiable ℝ p := hp.1.differentiable (by simp)
    obtain ⟨s, hse⟩ : ∃ s : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G),
        s = fun z => fderiv ℝ p z + (gl b z).smulRight (p z) := ⟨_, rfl⟩
    have hs : s.HasTemperateGrowth := by
      rw [hse]
      exact (tg_fderiv hp).add
        (ContinuousLinearMap.bilinear_hasTemperateGrowth
          (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) G) (gl_temperate b) hp)
    have hf : fderiv ℝ (fun z => gq b z • p z) = fun z => gq b z • s z := by
      funext z
      change fderiv ℝ (gq b • p) z = _
      rw [((gq_hasFDerivAt b z).smul (hd z).hasFDerivAt).fderiv, hse]
      refine ContinuousLinearMap.ext fun w => ?_
      simp [smul_smul]
    obtain ⟨r', hr', h⟩ := ih ((ℝ × ℝ) →L[ℝ] G) s hs
    refine ⟨fun y => (continuousMultilinearCurryRightEquiv' ℝ n (ℝ × ℝ) G).symm (r' y), ?_,
      fun y => ?_⟩
    · exact ((continuousMultilinearCurryRightEquiv' ℝ n (ℝ × ℝ) G).symm.toContinuousLinearEquiv.hasTemperateGrowth).comp hr'
    · rw [iteratedFDeriv_succ_eq_comp_right]
      simp only [Function.comp_apply]
      have : (fun y => fderiv ℝ (fun z => gq b z • p z) y) = fun z => gq b z • s z := hf
      rw [this, h y, map_smul]

theorem pow_exp_bound (b : ℝ) (hb : 0 < b) (D : ℕ) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ D * Real.exp (-(b * t ^ 2)) ≤ M := by
  refine ⟨2 ^ D * (1 + (D.factorial : ℝ) / b ^ D), fun t ht => ?_⟩
  have hE0 : 0 < Real.exp (-(b * t ^ 2)) := Real.exp_pos _
  have hE1 : Real.exp (-(b * t ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  have hEE : Real.exp (b * t ^ 2) * Real.exp (-(b * t ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 ≤ (t ^ 2) ^ D := by positivity
  have h1 : (1 + t) ^ D ≤ 2 ^ D * (1 + (t ^ 2) ^ D) := by
    rcases le_total t 1 with h | h
    · calc (1 + t) ^ D ≤ 2 ^ D := pow_le_pow_left₀ (by positivity) (by linarith) D
        _ ≤ 2 ^ D * (1 + (t ^ 2) ^ D) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
    · calc (1 + t) ^ D ≤ (2 * t ^ 2) ^ D :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) D
        _ = 2 ^ D * (t ^ 2) ^ D := mul_pow _ _ _
        _ ≤ 2 ^ D * (1 + (t ^ 2) ^ D) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (b * t ^ 2) ^ D / (D.factorial : ℝ) ≤ Real.exp (b * t ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) D
  have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hbD : (0 : ℝ) < b ^ D := by positivity
  have h3 : (t ^ 2) ^ D ≤ (D.factorial : ℝ) / b ^ D * Real.exp (b * t ^ 2) := by
    rw [div_le_iff₀ hfac, mul_pow] at h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hbD]
    nlinarith [h2]
  have h4 : (t ^ 2) ^ D * Real.exp (-(b * t ^ 2)) ≤ (D.factorial : ℝ) / b ^ D := by
    calc (t ^ 2) ^ D * Real.exp (-(b * t ^ 2))
        ≤ ((D.factorial : ℝ) / b ^ D * Real.exp (b * t ^ 2)) * Real.exp (-(b * t ^ 2)) :=
          mul_le_mul_of_nonneg_right h3 hE0.le
      _ = (D.factorial : ℝ) / b ^ D := by rw [mul_assoc, hEE, mul_one]
  calc (1 + t) ^ D * Real.exp (-(b * t ^ 2))
      ≤ (2 ^ D * (1 + (t ^ 2) ^ D)) * Real.exp (-(b * t ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 hE0.le
    _ = 2 ^ D * (Real.exp (-(b * t ^ 2)) + (t ^ 2) ^ D * Real.exp (-(b * t ^ 2))) := by ring
    _ ≤ 2 ^ D * (1 + (D.factorial : ℝ) / b ^ D) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem gq_le (b : ℝ) (hb : 0 < b) (y : ℝ × ℝ) : gq b y ≤ Real.exp (-(b * ‖y‖ ^ 2)) := by
  unfold gq
  apply Real.exp_le_exp.2
  have : ‖y‖ ^ 2 ≤ y.1 ^ 2 + y.2 ^ 2 := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    rcases le_total |y.1| |y.2| with h | h
    · rw [max_eq_right h]; nlinarith [sq_abs y.1, sq_abs y.2, sq_nonneg y.1, sq_nonneg y.2]
    · rw [max_eq_left h]; nlinarith [sq_abs y.1, sq_abs y.2, sq_nonneg y.1, sq_nonneg y.2]
  nlinarith

theorem gq_decay (b : ℝ) (hb : 0 < b) (k n : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ × ℝ, ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (gq b) y‖ ≤ C := by
  obtain ⟨r, hr, hy⟩ := key b n ℝ (fun _ => (1 : ℝ)) (Function.HasTemperateGrowth.const 1)
  obtain ⟨m, C0, hC0⟩ := hr.2 0
  obtain ⟨M, hM⟩ := pow_exp_bound b hb (k + m)
  have hC0' : 0 ≤ C0 := by
    have := hC0 0
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ 0 r 0‖ := norm_nonneg _
    have : 0 ≤ C0 * (1 + ‖(0 : ℝ × ℝ)‖) ^ m := h0.trans this
    simpa using this
  refine ⟨C0 * M, fun y => ?_⟩
  have e : iteratedFDeriv ℝ n (gq b) y = gq b y • r y := by
    have := hy y
    simpa using this
  have hr0 : ‖r y‖ ≤ C0 * (1 + ‖y‖) ^ m := by
    simpa [norm_iteratedFDeriv_zero] using hC0 y
  have hg0 : 0 ≤ gq b y := (Real.exp_pos _).le
  have ht := hM ‖y‖ (norm_nonneg _)
  have hgle := gq_le b hb y
  rw [e, norm_smul, Real.norm_of_nonneg hg0]
  have hy1 : ‖y‖ ^ k ≤ (1 + ‖y‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
  have hpow : (1 + ‖y‖) ^ k * (1 + ‖y‖) ^ m = (1 + ‖y‖) ^ (k + m) := (pow_add _ _ _).symm
  calc ‖y‖ ^ k * (gq b y * ‖r y‖)
      ≤ (1 + ‖y‖) ^ k * (gq b y * (C0 * (1 + ‖y‖) ^ m)) := by
        apply mul_le_mul hy1 (mul_le_mul_of_nonneg_left hr0 hg0) (by positivity) (by positivity)
    _ = C0 * ((1 + ‖y‖) ^ (k + m) * gq b y) := by rw [← hpow]; ring
    _ ≤ C0 * ((1 + ‖y‖) ^ (k + m) * Real.exp (-(b * ‖y‖ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hC0'
        exact mul_le_mul_of_nonneg_left hgle (by positivity)
    _ ≤ C0 * M := mul_le_mul_of_nonneg_left ht hC0'

theorem gauss_schwartz (b : ℝ) (hb : 0 < b) : ∃ g : SchwartzMap (ℝ × ℝ) ℝ,
    ∀ y : ℝ × ℝ, g y = Real.exp (-(b * (y.1 ^ 2 + y.2 ^ 2))) :=
  ⟨⟨gq b, gq_contDiff b, gq_decay b hb⟩, fun _ => rfl⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatTermAux
