import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Derivatives of the quadratic `|x|^2` and of the linear map `J` on the meridional variable

Task `ra_9_1_2_5_4_2`: uniform polynomial-type bounds on all iterated derivatives of the chart
functions `p ↦ p.2.1 ^ 2 + p.2.2 ^ 2` and `p ↦ Jrot p.2`, with constants depending only on the
order `k` (source lines 4963-4968, 4991).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Order `k + 2` iterated derivative of a continuous linear map vanishes. -/
lemma cpb_clm_iter_succ_succ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (M : E →L[ℝ] F) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ (k + 1 + 1) (M : E → F) x = 0 := by
  have hd : fderiv ℝ (M : E → F) = fun _ => M := by
    funext y
    exact M.fderiv
  have h0 : iteratedFDeriv ℝ (k + 1) (fun _ : E => M) = 0 :=
    iteratedFDeriv_succ_const (𝕜 := ℝ) k M
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (M : E → F)) (n := k + 1) (x := x)
  rw [hd, h0] at h1
  have h2 : ‖iteratedFDeriv ℝ (k + 1 + 1) (M : E → F) x‖ = 0 := by
    rw [← h1]
    simp
  exact norm_eq_zero.mp h2

/-- First iterated derivative of a continuous linear map is bounded by its operator norm. -/
lemma cpb_clm_norm_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (M : E →L[ℝ] F) (x : E) :
    ‖iteratedFDeriv ℝ 1 (M : E → F) x‖ ≤ ‖M‖ := by
  rw [norm_iteratedFDeriv_one, M.fderiv]

/-- Uniform bound on all iterated derivatives of a continuous linear map, given a bound of its
value at a point. -/
lemma cpb_clm_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (M : E →L[ℝ] F) (K r : ℝ) (hK : 0 ≤ K)
    (hM : ‖M‖ ≤ K) (hr : 0 ≤ r) (x : E) (hx : ‖M x‖ ≤ K * (1 + r)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (M : E → F) x‖ ≤ K * (1 + r) := by
  have hKr : 0 ≤ K * (1 + r) := mul_nonneg hK (by linarith)
  match k with
  | 0 =>
    rw [norm_iteratedFDeriv_zero]
    exact hx
  | 1 =>
    exact (cpb_clm_norm_one M x).trans (hM.trans (le_mul_of_one_le_right hK (by linarith)))
  | k + 1 + 1 =>
    rw [cpb_clm_iter_succ_succ M k x, norm_zero]
    exact hKr

/-- Leibniz bound for the square of a real-valued continuous linear map, given a uniform bound
on the iterated derivatives of the map at a point. -/
lemma cpb_sq_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c) (z : E)
    (h : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (ℓ : E → ℝ) z‖ ≤ c) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => (ℓ : E → ℝ) y * (ℓ : E → ℝ) y) z‖ ≤ 2 ^ k * c ^ 2 := by
  refine (norm_iteratedFDeriv_mul_le (N := ⊤) ℓ.contDiff ℓ.contDiff z le_top).trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ℓ : E → ℝ) z‖
          * ‖iteratedFDeriv ℝ (k - i) (ℓ : E → ℝ) z‖ ≤ (k.choose i : ℝ) * c ^ 2 := by
    intro i _
    have hab : ‖iteratedFDeriv ℝ i (ℓ : E → ℝ) z‖ * ‖iteratedFDeriv ℝ (k - i) (ℓ : E → ℝ) z‖
        ≤ c * c := mul_le_mul (h i) (h (k - i)) (norm_nonneg _) hc
    have hch : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hab hch
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ℓ : E → ℝ) z‖
          * ‖iteratedFDeriv ℝ (k - i) (ℓ : E → ℝ) z‖
        = (k.choose i : ℝ) * (‖iteratedFDeriv ℝ i (ℓ : E → ℝ) z‖
          * ‖iteratedFDeriv ℝ (k - i) (ℓ : E → ℝ) z‖) := by ring
      _ ≤ (k.choose i : ℝ) * (c * c) := this
      _ = (k.choose i : ℝ) * c ^ 2 := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hs]

/-- The coordinate projection `p ↦ p.2.1` on the chart. -/
def cpbS : Chart →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)

/-- The functional `p ↦ p.2.1`. -/
def cpbL1 : Chart →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp cpbS

/-- The functional `p ↦ p.2.2`. -/
def cpbL2 : Chart →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp cpbS

/-- The linear map `Jrot` as a continuous linear map of `ℝ × ℝ`. -/
def cpbJ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := Jrot
      map_add' := fun x y => by ext <;> simp [Jrot] <;> ring
      map_smul' := fun c x => by ext <;> simp [Jrot] <;> ring }

lemma cpbL1_apply (z : Chart) : cpbL1 z = z.2.1 := rfl

lemma cpbL2_apply (z : Chart) : cpbL2 z = z.2.2 := rfl

lemma cpbJ_apply (x : ℝ × ℝ) : cpbJ x = Jrot x := rfl

lemma cpbS_norm : ‖cpbS‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)

lemma cpbL1_norm : ‖cpbL1‖ ≤ 1 := by
  calc ‖cpbL1‖ ≤ ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ * ‖cpbS‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) cpbS_norm
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma cpbL2_norm : ‖cpbL2‖ ≤ 1 := by
  calc ‖cpbL2‖ ≤ ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ * ‖cpbS‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) cpbS_norm
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Iterated derivatives of `p ↦ p.2.1` and `p ↦ p.2.2`, uniform in the order. -/
lemma cpbL1_iter (z : Chart) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (cpbL1 : Chart → ℝ) z‖ ≤ 1 * (1 + ‖z.2‖) := by
  refine cpb_clm_bound cpbL1 1 ‖z.2‖ zero_le_one cpbL1_norm (norm_nonneg _) z ?_ k
  rw [cpbL1_apply, one_mul]
  have := norm_fst_le z.2
  linarith

lemma cpbL2_iter (z : Chart) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (cpbL2 : Chart → ℝ) z‖ ≤ 1 * (1 + ‖z.2‖) := by
  refine cpb_clm_bound cpbL2 1 ‖z.2‖ zero_le_one cpbL2_norm (norm_nonneg _) z ?_ k
  rw [cpbL2_apply, one_mul]
  have := norm_snd_le z.2
  linarith

theorem coordPoly_iteratedFDeriv_bound (k : ℕ) : ∃ C : ℝ, ∀ z : Chart, ‖iteratedFDeriv ℝ k (fun p : Chart => p.2.1 ^ 2 + p.2.2 ^ 2) z‖ ≤ C * (1 + ‖z.2‖) ^ 2 ∧ ‖iteratedFDeriv ℝ k (fun p : Chart => Jrot p.2) z‖ ≤ C * (1 + ‖z.2‖) := by
  refine ⟨2 ^ (k + 1) + ‖cpbJ‖ + 1, fun z => ⟨?_, ?_⟩⟩
  · have hfun : (fun p : Chart => p.2.1 ^ 2 + p.2.2 ^ 2)
        = (fun y => (cpbL1 : Chart → ℝ) y * (cpbL1 : Chart → ℝ) y)
          + (fun y => (cpbL2 : Chart → ℝ) y * (cpbL2 : Chart → ℝ) y) := by
      funext p
      show p.2.1 ^ 2 + p.2.2 ^ 2 = p.2.1 * p.2.1 + p.2.2 * p.2.2
      ring
    have hA : ContDiffAt ℝ k (fun y => (cpbL1 : Chart → ℝ) y * (cpbL1 : Chart → ℝ) y) z :=
      ((cpbL1.contDiff).mul (cpbL1.contDiff)).contDiffAt
    have hB : ContDiffAt ℝ k (fun y => (cpbL2 : Chart → ℝ) y * (cpbL2 : Chart → ℝ) y) z :=
      ((cpbL2.contDiff).mul (cpbL2.contDiff)).contDiffAt
    rw [hfun, iteratedFDeriv_add_apply hA hB]
    have hc : (0 : ℝ) ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
    have h1 := cpb_sq_bound cpbL1 (1 + ‖z.2‖) hc z
      (fun i => (cpbL1_iter z i).trans (le_of_eq (by ring))) k
    have h2 := cpb_sq_bound cpbL2 (1 + ‖z.2‖) hc z
      (fun i => (cpbL2_iter z i).trans (le_of_eq (by ring))) k
    have hpow : (0 : ℝ) ≤ 2 ^ k := by positivity
    calc _ ≤ ‖iteratedFDeriv ℝ k (fun y => (cpbL1 : Chart → ℝ) y * (cpbL1 : Chart → ℝ) y) z‖
          + ‖iteratedFDeriv ℝ k (fun y => (cpbL2 : Chart → ℝ) y * (cpbL2 : Chart → ℝ) y) z‖ :=
          norm_add_le _ _
      _ ≤ 2 ^ k * (1 + ‖z.2‖) ^ 2 + 2 ^ k * (1 + ‖z.2‖) ^ 2 := add_le_add h1 h2
      _ = 2 ^ (k + 1) * (1 + ‖z.2‖) ^ 2 := by ring
      _ ≤ (2 ^ (k + 1) + ‖cpbJ‖ + 1) * (1 + ‖z.2‖) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [norm_nonneg cpbJ]
  · have hfun : (fun p : Chart => Jrot p.2) = ⇑(cpbJ.comp cpbS) := by
      funext p
      rfl
    rw [hfun]
    have hM : ‖cpbJ.comp cpbS‖ ≤ ‖cpbJ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) cpbS_norm)
    have hx : ‖(cpbJ.comp cpbS) z‖ ≤ ‖cpbJ‖ * (1 + ‖z.2‖) := by
      have h0 : (cpbJ.comp cpbS) z = cpbJ z.2 := rfl
      rw [h0]
      have := ContinuousLinearMap.le_opNorm cpbJ z.2
      have h3 : ‖cpbJ‖ * ‖z.2‖ ≤ ‖cpbJ‖ * (1 + ‖z.2‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      linarith
    have hb := cpb_clm_bound (cpbJ.comp cpbS) ‖cpbJ‖ ‖z.2‖ (norm_nonneg _) hM
      (norm_nonneg _) z hx k
    have hc : (0 : ℝ) ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
    have hp : (0 : ℝ) ≤ 2 ^ (k + 1) := by positivity
    calc _ ≤ ‖cpbJ‖ * (1 + ‖z.2‖) := hb
      _ ≤ (2 ^ (k + 1) + ‖cpbJ‖ + 1) * (1 + ‖z.2‖) :=
          mul_le_mul_of_nonneg_right (by linarith) hc

end UnforcedLeray.Short.PartIIIb.Concrete
