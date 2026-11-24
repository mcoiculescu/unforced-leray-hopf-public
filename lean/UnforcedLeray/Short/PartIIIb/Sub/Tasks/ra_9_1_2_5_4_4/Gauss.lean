import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_3
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Shared Gaussian product bounds for `V_j` and `ψ_j` (helper for `ra_9_1_2_5_4_4`, `ra_9_1_2_5_4_5`)

The chart functions `a^{-m}` and `exp(-|x|^2/(4a))` are replaced near a point `z` (with `z.1 > s0/2`)
by globally smooth functions built from `ageSmoothT`. Derivatives at `z` only depend on the germ at `z`.
The product bound is then the Leibniz rule with the explicit uniform Gaussian rate
`gaussK ν s0 s1 = 1 / (4 (1 + ν max(s1, s0)))`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The uniform Gaussian rate on `s0 ≤ s ≤ s1`. -/
def gaussK (ν s0 s1 : ℝ) : ℝ := 1 / (4 * (1 + ν * max s1 s0))

lemma gaussK_pos (ν s0 s1 : ℝ) (hν : 0 < ν) (hs0 : 0 < s0) : 0 < gaussK ν s0 s1 := by
  unfold gaussK
  have hmax : s0 ≤ max s1 s0 := le_max_right _ _
  have : 0 < ν * max s1 s0 := mul_pos hν (lt_of_lt_of_le hs0 hmax)
  exact div_pos one_pos (by linarith)

lemma gauss_hn : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun i => by
  exact_mod_cast le_top

lemma gauss_eqQ_le (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0) (z : Chart)
    (hz1 : s0 ≤ z.1) (hz2 : z.1 ≤ s1) :
    eqQ ν s0 z ≤ -gaussK ν s0 s1 * ‖z.2‖ ^ 2 := by
  have hsq : ‖z.2‖ ^ 2 ≤ sq2 z.2 := by
    have hn : ‖z.2‖ = max |z.2.1| |z.2.2| := by
      rw [Prod.norm_def]
      simp [Real.norm_eq_abs]
    rw [hn]
    unfold sq2
    rcases max_cases |z.2.1| |z.2.2| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_abs z.2.1, sq_abs z.2.2, sq_nonneg z.2.1, sq_nonneg z.2.2]
  have hAeq : ageSmoothT s0 z.1 = z.1 := ageSmoothT_eq s0 hs0 z.1 (by linarith)
  have hA0 : 0 < 1 + ν * z.1 := by
    have : 0 < ν * z.1 := mul_pos hν (by linarith)
    linarith
  have hAa : 1 + ν * z.1 ≤ 1 + ν * max s1 s0 := by
    have : ν * z.1 ≤ ν * max s1 s0 :=
      mul_le_mul_of_nonneg_left (hz2.trans (le_max_left _ _)) hν.le
    linarith
  have hS0 : 0 ≤ sq2 z.2 := by
    unfold sq2
    positivity
  unfold gaussK eqQ
  rw [hAeq]
  have key : ‖z.2‖ ^ 2 / (4 * (1 + ν * max s1 s0)) ≤ sq2 z.2 / (4 * (1 + ν * z.1)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 : ‖z.2‖ ^ 2 * (4 * (1 + ν * z.1)) ≤ sq2 z.2 * (4 * (1 + ν * z.1)) :=
      mul_le_mul_of_nonneg_right hsq (by linarith)
    have h2 : sq2 z.2 * (4 * (1 + ν * z.1)) ≤ sq2 z.2 * (4 * (1 + ν * max s1 s0)) :=
      mul_le_mul_of_nonneg_left (by linarith) hS0
    linarith
  have e : -(1 / (4 * (1 + ν * max s1 s0))) * ‖z.2‖ ^ 2
      = -(‖z.2‖ ^ 2 / (4 * (1 + ν * max s1 s0))) := by ring
  rw [neg_div, e]
  exact neg_le_neg key

lemma gauss_A_smooth (ν : ℝ) (s0 : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => 1 + ν * ageSmoothT s0 p.1) :=
  contDiff_const.add (contDiff_const.mul ((ageSmoothT_contDiff s0).comp contDiff_fst))

lemma gauss_G1sq_smooth (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹) :=
  ((gauss_A_smooth ν s0).pow 2).inv (fun p => pow_ne_zero 2 (eqd_A_pos ν hν s0 hs0 p.1).ne')

lemma gauss_G1_smooth (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹) :=
  (gauss_A_smooth ν s0).inv (fun p => (eqd_A_pos ν hν s0 hs0 p.1).ne')

lemma gauss_eqQ_smooth (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eqQ ν s0) := by
  rw [eqQ_eq_mul]
  exact eqd_f1_smooth.mul (eqd_g_smooth ν hν s0 hs0)

lemma gauss_exp_smooth (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => Real.exp (eqQ ν s0 p)) :=
  (gauss_eqQ_smooth ν hν s0 hs0).exp

lemma gauss_J_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => Jrot p.2) := by
  unfold Jrot
  fun_prop

lemma gauss_germ_mem (s0 : ℝ) (hs0 : 0 < s0) (z : Chart) (hz : s0 ≤ z.1) :
    {p : Chart | s0 / 2 < p.1} ∈ 𝓝 z :=
  (isOpen_lt continuous_const continuous_fst).mem_nhds (show s0 / 2 < z.1 by linarith)

lemma gauss_G1sq_germ (ν : ℝ) (s0 : ℝ) (hs0 : 0 < s0) (z : Chart) (hz : s0 ≤ z.1) (j : ℕ) :
    iteratedFDeriv ℝ j (fun p : Chart => ((ageA ν p.1) ^ 2)⁻¹) z
      = iteratedFDeriv ℝ j (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹) z := by
  have hev : (fun p : Chart => ((ageA ν p.1) ^ 2)⁻¹) =ᶠ[𝓝 z]
      (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹) := by
    filter_upwards [gauss_germ_mem s0 hs0 z hz] with p hp
    have hp' : s0 / 2 ≤ p.1 := (show s0 / 2 < p.1 from hp).le
    rw [ageSmoothT_eq s0 hs0 p.1 hp']
    rfl
  exact (hev.iteratedFDeriv ℝ j).eq_of_nhds

lemma gauss_V_eq (ν : ℝ) (q : Chart) :
    Vj ν q.1 0 q.2 = ((ageA ν q.1 ^ 2)⁻¹ * Real.exp (-(sq2 q.2) / (4 * ageA ν q.1))) • Jrot q.2 := by
  simp [Vj, xj]

lemma gauss_V_germ (ν : ℝ) (s0 : ℝ) (hs0 : 0 < s0) (z : Chart) (hz : s0 ≤ z.1) :
    (fun q : Chart => Vj ν q.1 0 q.2) =ᶠ[𝓝 z]
      (fun p : Chart => (((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹ * Real.exp (eqQ ν s0 p)) • Jrot p.2) := by
  filter_upwards [gauss_germ_mem s0 hs0 z hz] with p hp
  have hp' : s0 / 2 ≤ p.1 := (show s0 / 2 < p.1 from hp).le
  simp only [gauss_V_eq, eqQ, ageSmoothT_eq s0 hs0 p.1 hp', ageA]

lemma gauss_prod_bd (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0)
    (G1 : Chart → ℝ) (hG1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G1)
    (hG1b : ∀ j : ℕ, ∃ B : ℝ, ∀ z : Chart, s0 ≤ z.1 → ‖iteratedFDeriv ℝ j G1 z‖ ≤ B)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 →
      ‖iteratedFDeriv ℝ n (fun p : Chart => G1 p * Real.exp (eqQ ν s0 p)) z‖
        ≤ C * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) := by
  choose Bj hBj using hG1b
  choose Ce hCe using eqd_exp_bd ν hν s0 hs0
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bj i| * |Ce (n - i)|,
    Finset.sum_nonneg (fun i _ => by positivity), fun z hz1 hz2 => ?_⟩
  have hX : (1 : ℝ) ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hE : Real.exp (eqQ ν s0 z) ≤ Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) :=
    Real.exp_le_exp.mpr (gauss_eqQ_le ν hν s0 s1 hs0 z hz1 hz2)
  have hEpos : 0 ≤ Real.exp (eqQ ν s0 z) := (Real.exp_pos _).le
  refine (norm_iteratedFDeriv_mul_le hG1 (gauss_exp_smooth ν hν s0 hs0) z (gauss_hn n)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  have ha : ‖iteratedFDeriv ℝ i G1 z‖ ≤ |Bj i| := (hBj i z hz1).trans (le_abs_self _)
  have hb : ‖iteratedFDeriv ℝ (n - i) (fun p : Chart => Real.exp (eqQ ν s0 p)) z‖
      ≤ |Ce (n - i)| * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) := by
    refine (hCe (n - i) z hz1).trans ?_
    have hpow : (1 + ‖z.2‖) ^ (2 * (n - i)) ≤ (1 + ‖z.2‖) ^ (2 * n) :=
      pow_le_pow_right₀ hX (by omega)
    have h1 : Ce (n - i) * (1 + ‖z.2‖) ^ (2 * (n - i)) * Real.exp (eqQ ν s0 z)
        ≤ |Ce (n - i)| * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (eqQ ν s0 z) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (le_abs_self _) hpow (by positivity) (abs_nonneg _)) hEpos
    exact h1.trans (mul_le_mul_of_nonneg_left hE (by positivity))
  have hch : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  have hab := mul_le_mul (mul_le_mul_of_nonneg_left ha hch) hb (norm_nonneg _)
    (mul_nonneg hch (abs_nonneg _))
  refine hab.trans (le_of_eq ?_)
  ring

lemma gauss_smul_bd (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0)
    (G : Chart → ℝ) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hGb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 →
      ‖iteratedFDeriv ℝ i G z‖ ≤ C * (1 + ‖z.2‖) ^ (2 * i) * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2))
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 →
      ‖iteratedFDeriv ℝ n (fun p : Chart => G p • Jrot p.2) z‖
        ≤ C * (1 + ‖z.2‖) ^ (2 * n + 1) * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) := by
  choose Cg hCg0 hCg using hGb
  choose Cj hCj using coordPoly_iteratedFDeriv_bound
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cg i * |Cj (n - i)|,
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCg0 i))
      (abs_nonneg _)), fun z hz1 hz2 => ?_⟩
  have hX0 : (0 : ℝ) ≤ 1 + ‖z.2‖ := by positivity
  have hX : (1 : ℝ) ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hEx : 0 ≤ Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) := (Real.exp_pos _).le
  refine (norm_iteratedFDeriv_smul_le hG gauss_J_smooth z (gauss_hn n)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  have ha := hCg i z hz1 hz2
  have hb : ‖iteratedFDeriv ℝ (n - i) (fun p : Chart => Jrot p.2) z‖
      ≤ |Cj (n - i)| * (1 + ‖z.2‖) :=
    (hCj (n - i) z).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  have hch : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  have hpow : (1 + ‖z.2‖) ^ (2 * i) * (1 + ‖z.2‖) ≤ (1 + ‖z.2‖) ^ (2 * n + 1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hX (by omega)
  have hab := mul_le_mul (mul_le_mul_of_nonneg_left ha hch) hb (norm_nonneg _)
    (mul_nonneg hch (mul_nonneg (mul_nonneg (hCg0 i) (by positivity)) hEx))
  refine hab.trans ?_
  calc (n.choose i : ℝ) * (Cg i * (1 + ‖z.2‖) ^ (2 * i) * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2))
        * (|Cj (n - i)| * (1 + ‖z.2‖))
      = (n.choose i : ℝ) * Cg i * |Cj (n - i)| * ((1 + ‖z.2‖) ^ (2 * i) * (1 + ‖z.2‖))
          * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) := by ring
    _ ≤ (n.choose i : ℝ) * Cg i * |Cj (n - i)| * (1 + ‖z.2‖) ^ (2 * n + 1)
          * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hEx
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hch (hCg0 i)) (abs_nonneg _))

end UnforcedLeray.Short.PartIIIb.Concrete
