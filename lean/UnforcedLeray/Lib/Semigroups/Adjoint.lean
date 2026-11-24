import UnforcedLeray.Lib.Semigroups.Laplace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Adjoint semigroups on Hilbert space (INF07 T7.1 API, T7.2 `adjoint_laplace`)


§5, targets **T7.1** ("adjoint semigroups in `H`") and **T7.2** (`adjoint_laplace`), Wave 1
block 1G. Uses: the adjoint graphs and adjoint-strong convergence of tex 3413, 6540-6547,
7698-7715 (the adjoint version of T7.3 is applied to the adjoint semigroups).

On a complex Hilbert space the adjoints `T(t)^*` of an exponentially bounded strongly continuous
semigroup again form one (`ExpSemigroup.adjoint`, same constants). Strong continuity of
`t ↦ T(t)^* y` is not formal; it is proved here without generator theory:
1. `T(t) R(μ) - R(μ) → 0` in operator norm as `t → 0⁺` (`tendsto_norm_T_comp_laplace_sub`), so
   every vector `R(μ)^* w` is a point of right continuity of the adjoint family;
2. `R(μ)` is injective (if `R(μ) z = 0` then `t ↦ T(t) R(μ) z ≡ 0` has derivative
   `-T(t) z`, so `T(t) z = 0` for `t > 0`, and `z = 0` by continuity at `0`); hence the range of
   `R(μ)^*` is dense (its orthogonal complement is `ker R(μ) = 0`);
3. the set of points of right continuity at `0` is closed under limits (uniform bound), and right
   continuity at `0` plus the semigroup law gives continuity on `[0, ∞)`
   (`continuousOn_of_tendsto_zero`).

`adjoint_laplace`: `R(μ)^* = R^*(conj μ)`, where `R^*` is the Laplace transform of the adjoint
semigroup.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Infra

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Right continuity at `0` and the semigroup law give continuity on `[0, ∞)`. -/
theorem continuousOn_of_tendsto_zero (T : ℝ → E →L[ℂ] E) (hzero : T 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s ∘L T t)
    {M ω : ℝ} (hle : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) (x : E)
    (h0 : Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x)) :
    ContinuousOn (fun t => T t x) (Ici 0) := by
  intro t₀ ht₀
  rw [mem_Ici] at ht₀
  set C : ℝ := max M 0 * Real.exp (|ω| * (t₀ + 1)) + 1 with hC
  have hC0 : 0 < C := by positivity
  have hbd : ∀ s, 0 ≤ s → s ≤ t₀ + 1 → ‖T s‖ ≤ C := by
    intro s hs hs'
    refine (hle s hs).trans ?_
    have h1 : M * Real.exp (ω * s) ≤ max M 0 * Real.exp (|ω| * (t₀ + 1)) := by
      refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        (le_max_right _ _)
      calc ω * s ≤ |ω| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs
        _ ≤ |ω| * (t₀ + 1) := mul_le_mul_of_nonneg_left hs' (abs_nonneg _)
    linarith
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhdsWithin_iff.1
    (h0 (Metric.ball_mem_nhds x (div_pos hε hC0)))
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun t ht hdist => ?_⟩
  rw [mem_Ici] at ht
  rw [Real.dist_eq] at hdist
  have hδ1 : |t - t₀| < δ₀ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hδ2 : |t - t₀| < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hsmall : ∀ h, 0 ≤ h → |h| < δ₀ → ‖T h x - x‖ < ε / C := by
    intro h hh hh'
    have hmem : h ∈ Metric.ball (0 : ℝ) δ₀ ∩ Ici 0 := ⟨by simpa [Real.dist_eq] using hh', hh⟩
    simpa [dist_eq_norm] using hδ₀' hmem
  rcases le_total t₀ t with h | h
  · have hdecomp : T t x - T t₀ x = T t₀ (T (t - t₀) x - x) := by
      have := hadd t₀ (t - t₀) ht₀ (sub_nonneg.2 h)
      rw [add_sub_cancel] at this
      rw [this, map_sub, ContinuousLinearMap.comp_apply]
    rw [dist_eq_norm, hdecomp]
    calc ‖T t₀ (T (t - t₀) x - x)‖ ≤ ‖T t₀‖ * ‖T (t - t₀) x - x‖ := (T t₀).le_opNorm _
      _ < C * (ε / C) := by
          refine mul_lt_mul' (hbd t₀ ht₀ (by linarith)) (hsmall _ (sub_nonneg.2 h) hδ1)
            (norm_nonneg _) hC0
      _ = ε := by field_simp
  · have hdecomp : T t₀ x - T t x = T t (T (t₀ - t) x - x) := by
      have := hadd t (t₀ - t) ht (sub_nonneg.2 h)
      rw [add_sub_cancel] at this
      rw [this, map_sub, ContinuousLinearMap.comp_apply]
    rw [dist_comm, dist_eq_norm, hdecomp]
    calc ‖T t (T (t₀ - t) x - x)‖ ≤ ‖T t‖ * ‖T (t₀ - t) x - x‖ := (T t).le_opNorm _
      _ < C * (ε / C) := by
          refine mul_lt_mul' (hbd t ht (by linarith)) (hsmall _ (sub_nonneg.2 h) ?_)
            (norm_nonneg _) hC0
          rwa [abs_sub_comm]
      _ = ε := by field_simp

end General

namespace ExpSemigroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ExpSemigroup H)

/-- The Laplace transform at a real point `ω + 1` of the half-plane. -/
private theorem re_lt_succ : S.ω < ((S.ω + 1 : ℝ) : ℂ).re := by simp

/-- `R(μ)` is injective. -/
theorem laplace_injective {μ : ℂ} (hμ : S.ω < μ.re) {z : H} (hz : S.laplace μ z = 0) :
    z = 0 := by
  have hT : ∀ t, 0 < t → S.T t z = 0 := by
    intro t ht
    have h := S.hasDerivAt_T_laplace hμ z ht
    have hconst : (fun t => S.T t (S.laplace μ z)) = fun _ => (0 : H) := by
      funext s
      rw [hz, map_zero]
    rw [hconst] at h
    have := h.unique (hasDerivAt_const t (0 : H))
    rw [hz, smul_zero, zero_sub, map_neg, neg_eq_zero] at this
    exact this
  have hlim : Tendsto (fun t => S.T t z) (𝓝[>] 0) (𝓝 z) := by
    have h := (S.T_cont z 0 (mem_Ici.2 le_rfl)).mono (Ioi_subset_Ici_self (a := (0 : ℝ)))
    simpa [ContinuousWithinAt, S.T_zero_apply] using h
  have hlim0 : Tendsto (fun t => S.T t z) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hT t ht).symm)
  exact tendsto_nhds_unique hlim hlim0

/-- The range of `R(μ)^*` is dense. -/
theorem dense_range_adjoint_laplace {μ : ℂ} (hμ : S.ω < μ.re) (y : H) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : H, ‖y - ContinuousLinearMap.adjoint (S.laplace μ) w‖ < δ := by
  set K : Submodule ℂ H := LinearMap.range (ContinuousLinearMap.adjoint (S.laplace μ) : H →ₗ[ℂ] H)
  have hK : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [Submodule.mem_orthogonal] at hz
    have h := hz (ContinuousLinearMap.adjoint (S.laplace μ) (S.laplace μ z)) ⟨_, rfl⟩
    rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_zero] at h
    exact S.laplace_injective hμ h
  have hcl : K.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hK, Submodule.bot_orthogonal_eq_top]
  have hy : y ∈ closure (K : Set H) := by
    rw [← Submodule.topologicalClosure_coe, hcl]
    exact Submodule.mem_top
  obtain ⟨b, hb, hyb⟩ := Metric.mem_closure_iff.1 hy δ hδ
  obtain ⟨w, rfl⟩ := hb
  exact ⟨w, by rwa [← dist_eq_norm]⟩

/-- **Strong continuity of the adjoint semigroup** at `0`. -/
theorem tendsto_adjoint_T_apply (y : H) :
    Tendsto (fun t => ContinuousLinearMap.adjoint (S.T t) y) (𝓝[≥] 0) (𝓝 y) := by
  set μ : ℂ := ((S.ω + 1 : ℝ) : ℂ)
  have hμ : S.ω < μ.re := S.re_lt_succ
  set R := S.laplace μ
  set C : ℝ := S.M * Real.exp (|S.ω|) + 1 with hC
  have hC0 : 0 < C := by have := S.M_nonneg; positivity
  have hbd : ∀ t, 0 ≤ t → t ≤ 1 → ‖ContinuousLinearMap.adjoint (S.T t)‖ ≤ C := by
    intro t ht ht1
    rw [LinearIsometryEquiv.norm_map]
    have := S.norm_T_le_of_le ht ht1
    rw [mul_one] at this
    linarith
  -- vectors in the range of `R^*` are points of right continuity
  have hrange : ∀ w, Tendsto (fun t => ContinuousLinearMap.adjoint (S.T t) (ContinuousLinearMap.adjoint R w))
      (𝓝[≥] 0) (𝓝 (ContinuousLinearMap.adjoint R w)) := by
    intro w
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      ((S.tendsto_norm_T_comp_laplace_sub hμ).mul_const ‖w‖ |>.trans (by simp))
    filter_upwards [self_mem_nhdsWithin] with t ht
    have heq : ContinuousLinearMap.adjoint (S.T t) (ContinuousLinearMap.adjoint R w) -
        ContinuousLinearMap.adjoint R w = ContinuousLinearMap.adjoint (S.T t ∘L R - R) w := by
      rw [map_sub, S.T_comp_laplace hμ ht, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [heq]
    refine ((ContinuousLinearMap.adjoint (S.T t ∘L R - R)).le_opNorm w).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨w, hw⟩ := S.dense_range_adjoint_laplace hμ y hδ0
  set y' := ContinuousLinearMap.adjoint R w
  have h1 := (Metric.tendsto_nhds.1 ((tendsto_iff_norm_sub_tendsto_zero).1 (hrange w)))
    (ε / 2) (half_pos hε)
  have h2 : ∀ᶠ t in 𝓝[≥] (0 : ℝ), t ∈ Icc (0 : ℝ) 1 :=
    Icc_mem_nhdsGE zero_lt_one
  filter_upwards [h1, h2] with t ht ht'
  rw [Real.dist_eq, sub_zero, abs_norm] at ht ⊢
  have hdec : ContinuousLinearMap.adjoint (S.T t) y - y =
      ContinuousLinearMap.adjoint (S.T t) (y - y') +
        (ContinuousLinearMap.adjoint (S.T t) y' - y') + (y' - y) := by
    rw [map_sub]
    abel
  rw [hdec]
  have hA : ‖ContinuousLinearMap.adjoint (S.T t) (y - y')‖ ≤ C * δ :=
    ((ContinuousLinearMap.adjoint (S.T t)).le_opNorm _).trans
      (mul_le_mul (hbd t ht'.1 ht'.2) hw.le (norm_nonneg _) hC0.le)
  have hB : ‖y' - y‖ ≤ δ := by rw [norm_sub_rev]; exact hw.le
  have hCδ : C * δ + δ ≤ ε / 2 := by
    rw [hδ, ← add_one_mul, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  calc _ ≤ ‖ContinuousLinearMap.adjoint (S.T t) (y - y')‖ +
        ‖ContinuousLinearMap.adjoint (S.T t) y' - y'‖ + ‖y' - y‖ := norm_add₃_le
    _ < C * δ + ε / 2 + δ := by
        have := ht
        linarith
    _ ≤ ε := by linarith

/-- **T7.1, adjoint semigroup** on a Hilbert space: `t ↦ T(t)^*`, with the same constants. -/
def adjoint : ExpSemigroup H where
  T t := ContinuousLinearMap.adjoint (S.T t)
  T_zero := by rw [S.T_zero, ContinuousLinearMap.adjoint_one]
  T_add s t hs ht := by
    rw [add_comm, S.T_add t s ht hs, ContinuousLinearMap.adjoint_comp]
  T_cont y := continuousOn_of_tendsto_zero (fun t => ContinuousLinearMap.adjoint (S.T t))
    (by rw [S.T_zero, ContinuousLinearMap.adjoint_one])
    (fun s t hs ht => by rw [add_comm, S.T_add t s ht hs, ContinuousLinearMap.adjoint_comp])
    (M := S.M) (ω := S.ω) (fun t ht => by rw [LinearIsometryEquiv.norm_map]; exact S.T_le t ht)
    y (S.tendsto_adjoint_T_apply y)
  M := S.M
  ω := S.ω
  M_nonneg := S.M_nonneg
  T_le t ht := by rw [LinearIsometryEquiv.norm_map]; exact S.T_le t ht

@[simp] theorem adjoint_T (t : ℝ) : S.adjoint.T t = ContinuousLinearMap.adjoint (S.T t) := rfl
@[simp] theorem adjoint_M : S.adjoint.M = S.M := rfl
@[simp] theorem adjoint_ω : S.adjoint.ω = S.ω := rfl

theorem inner_integral_left {f : ℝ → H} {s : Set ℝ} (hf : IntegrableOn f s) (x : H) :
    ⟪∫ t in s, f t, x⟫_ℂ = ∫ t in s, ⟪f t, x⟫_ℂ := by
  rw [← inner_conj_symm, ← integral_inner (𝕜 := ℂ) hf x, ← integral_conj]
  congr 1
  funext t
  rw [inner_conj_symm]

/-- **T7.2** `R(μ)^* = R^*(conj μ)`: the adjoint of the Laplace transform is the Laplace
transform of the adjoint semigroup. -/
theorem adjoint_laplace {μ : ℂ} (hμ : S.ω < μ.re) :
    ContinuousLinearMap.adjoint (S.laplace μ) = S.adjoint.laplace (starRingEnd ℂ μ) := by
  have hμ' : S.adjoint.ω < (starRingEnd ℂ μ).re := by simpa using hμ
  refine ContinuousLinearMap.ext fun y => ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, S.laplace_apply' hμ,
    S.adjoint.laplace_apply' hμ', ← integral_inner (𝕜 := ℂ) (S.integrableOn_lapInt hμ x) y,
    inner_integral_left (S.adjoint.integrableOn_lapInt hμ' y)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [lapInt_def, adjoint_T, inner_smul_left, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left]
  congr 1
  rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]

end ExpSemigroup

end UnforcedLeray.Infra
