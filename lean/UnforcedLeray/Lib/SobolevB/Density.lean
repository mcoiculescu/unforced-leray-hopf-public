import UnforcedLeray.Lib.SobolevB.Leibniz
import UnforcedLeray.Lib.SobolevB.Smooth

/-!
# Cutoffs and density of `C_c^∞` in `W^{k,p}(ℝⁿ)` (INF11 target S4)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S4, `W.dense_smooth`). Manuscript uses: density
of `C_c^∞` in `H^j_M` (tex 1238–1243, B0063), smooth approximation of Sobolev fields
(tex 13970–13985, B0892), radial cutoffs (tex 7550–7576, B0433).

1. **Cutoff** (`W.tendsto_cutoff`, any weight `ρ`): with `χ` a bump equal to `1` on the unit
   ball and `0` outside the ball of radius `2`, `χ(·/(m+1)) x → x` in `W^{k,p}(ρ)`, `p < ∞`.
   The Leibniz expansion (`W.coeFn_deriv_mulCoeff`) has the diagonal term `χ_m ∂^α x`, which
   converges by dominated convergence (`tendsto_eLpNorm_smul_of_tendsto`), and lower-order
   terms carrying a factor `(m+1)^{-(|α|-|u|)}` (`lcoef_dilate`).
2. **Mollification** (`W.tendsto_mollify`, weight `1`): of a field vanishing outside a compact
   set, it gives smooth compactly supported values.

The weight is `1` in `W.dense_smooth`; the weighted density of the note (weights with bounded
log-derivative and local doubling) and the cylinder density are not proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

/-! ### Dominated convergence in `L^p` -/

/-- **Dominated convergence in `L^p`**, `0 < p < ∞`: if `|c_m| ≤ 1` and `c_m → 0` pointwise,
then `‖c_m f‖_p → 0` for `f ∈ L^p`. -/
theorem tendsto_eLpNorm_smul_of_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) {f : α → F} (hf : MemLp f p μ) {c : ℕ → α → ℝ}
    (hc : ∀ m, AEStronglyMeasurable (c m) μ) (hb : ∀ m x, |c m x| ≤ 1)
    (hl : ∀ x, Tendsto (fun m => c m x) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun x => c m x • f x) p μ) atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto (fun m => ∫⁻ x, ‖c m x • f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun m x => ‖c m x • f x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun x => ‖f x‖ₑ ^ p.toReal)
      (fun m => (((hc m).smul hf.1).enorm).pow_const _)
      (fun m => Eventually.of_forall fun x => by
        refine ENNReal.rpow_le_rpow ?_ hr.le
        rw [enorm_smul]
        refine mul_le_of_le_one_left zero_le ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.mpr (hb m x))
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.2).ne
      (Eventually.of_forall fun x => by
        have h1 : Tendsto (fun m => c m x • f x) atTop (𝓝 0) := by
          simpa using (hl x).smul_const (f x)
        have h2 := (continuous_enorm.tendsto _).comp h1
        have h3 := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto _ |>.comp h2
        simpa [ENNReal.zero_rpow_of_pos hr, Function.comp_def] using h3)
    simpa using h
  have hc' : Tendsto (fun t : ℝ≥0∞ => t ^ (1 / p.toReal)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0
    simpa [ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)] using this
  exact hc'.comp hlim

/-! ### The cutoff -/

section Cutoff

variable {n : ℕ}

/-- The bump `χ`, `1` on the unit ball, `0` outside the ball of radius `2`. -/
def cutBump (n : ℕ) : ContDiffBump (0 : Eucl n) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `χ_m = χ(·/(m+1))`. -/
def cutR (m : ℕ) (x : Eucl n) : ℝ := cutBump n (((m : ℝ) + 1)⁻¹ • x)

theorem bddDerivs_of_hasCompactSupport {r : ℕ} {a : Eucl n → ℝ} (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) : BddDerivs r a := by
  refine ⟨ha, fun j _ => ?_⟩
  exact (ha.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (hc.iteratedFDeriv j)

theorem contDiff_cutBump : ContDiff ℝ ∞ (cutBump n : Eucl n → ℝ) := (cutBump n).contDiff

theorem contDiff_cutR (m : ℕ) : ContDiff ℝ ∞ (cutR (n := n) m) :=
  contDiff_cutBump.comp (contDiff_const_smul _)

theorem hasCompactSupport_cutR (m : ℕ) : HasCompactSupport (cutR (n := n) m) := by
  have hs : ((m : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  exact (cutBump n).hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hs)

theorem bddDerivs_cutR (r m : ℕ) : BddDerivs r (cutR (n := n) m) :=
  bddDerivs_of_hasCompactSupport (contDiff_cutR m) (hasCompactSupport_cutR m)

theorem bddDerivs_cutBump (r : ℕ) : BddDerivs r (cutBump n : Eucl n → ℝ) :=
  bddDerivs_of_hasCompactSupport contDiff_cutBump (cutBump n).hasCompactSupport

theorem cutR_nonneg (m : ℕ) (x : Eucl n) : 0 ≤ cutR m x := (cutBump n).nonneg

theorem cutR_le_one (m : ℕ) (x : Eucl n) : cutR m x ≤ 1 := (cutBump n).le_one

theorem tendsto_cutR (x : Eucl n) : Tendsto (fun m : ℕ => cutR m x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with m hm
  symm
  refine (cutBump n).one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < m + 1))]
  show ((m : ℝ) + 1)⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < m + 1), mul_one]
  have : (N : ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem cutR_eq_zero {m : ℕ} {x : Eucl n} (hx : 2 * ((m : ℝ) + 1) ≤ ‖x‖) : cutR m x = 0 := by
  refine (cutBump n).zero_of_le_dist ?_
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < m + 1))]
  show (2 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ (by positivity : (0 : ℝ) < m + 1)]
  linarith

theorem lcoef_cutR (m : ℕ) (w u : List (Fin n)) (x : Eucl n) :
    lcoef (cutR m) w u x =
      (((m : ℝ) + 1)⁻¹) ^ (w.length - u.length) *
        lcoef (cutBump n) w u (((m : ℝ) + 1)⁻¹ • x) :=
  lcoef_dilate contDiff_cutBump _ w u x

end Cutoff

/-! ### Words and indices -/

theorem Idx.ofList_toList {n k : ℕ} (α : Idx n k) (h : (Idx.toList α).length ≤ k) :
    Idx.ofList (Idx.toList α) h = α := by
  obtain ⟨⟨j, hj⟩, β⟩ := α
  simp only [Idx.ofList, Idx.toList]
  refine Sigma.ext (Fin.ext (by simp)) ?_
  refine (Fin.heq_fun_iff (by simp)).mpr fun i => ?_
  simp

/-! ### Convergence of the cutoffs in `W` -/

section CutoffW

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {ρ : Weight (Eucl n)}

/-- `χ_m · x`. -/
def W.cutoff (m : ℕ) : W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] W (wholeSpace n) ρ 𝕜 F k p :=
  W.mulCoeff (ρ := ρ) (bddDerivs_cutR k m)

theorem derivL_toList (x : W (wholeSpace n) ρ 𝕜 F k p) (α : Idx n k) :
    derivL ρ (Idx.toList α) x = W.deriv (wholeSpace n) ρ 𝕜 F k p α x := by
  have h : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  rw [derivL_of_le _ h, Idx.ofList_toList]

/-- One term of the Leibniz expansion of `χ_m x` tends to its limit in `L^p`. -/
theorem tendsto_cutoff_term (hp : p ≠ ⊤) (x : W (wholeSpace n) ρ 𝕜 F k p) (α : Idx n k)
    (u : List (Fin n)) :
    Tendsto (fun m : ℕ => eLpNorm (fun y => lcoef (cutR m) (Idx.toList α) u y •
        (derivL ρ u x) y - (if u = Idx.toList α then (derivL ρ u x) y else 0)) p
        (wμ volume ρ)) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hf : MemLp (⇑(derivL ρ u x)) p (wμ volume ρ) := Lp.memLp _
  have hα : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  by_cases hu : u = Idx.toList α
  · -- the diagonal term: `(χ_m - 1) ∂^α x`
    subst hu
    have h := tendsto_eLpNorm_smul_of_tendsto hp0 hp hf (c := fun m y => cutR m y - 1)
      (fun m => ((contDiff_cutR m).continuous.sub continuous_const).aestronglyMeasurable)
      (fun m y => by
        rw [abs_le]; constructor <;> linarith [cutR_nonneg m y, cutR_le_one m y])
      (fun y => by simpa using (tendsto_cutR y).sub_const 1)
    refine h.congr fun m => ?_
    congr 1
    funext y
    rw [lcoef_self, if_pos rfl, sub_smul, one_smul]
  · by_cases hlen : u.length < (Idx.toList α).length
    · -- lower order: a factor `(m+1)^{-1}`
      obtain ⟨B, hB⟩ := (bddDerivs_lcoef (bddDerivs_cutBump (n := n) k) (Idx.toList α) hα
        u).bounded
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
      have hbound : ∀ m : ℕ, eLpNorm (fun y => lcoef (cutR m) (Idx.toList α) u y •
          (derivL ρ u x) y - (if u = Idx.toList α then (derivL ρ u x) y else 0)) p
          (wμ volume ρ) ≤ ENNReal.ofReal (((m : ℝ) + 1)⁻¹ * B) * eLpNorm (derivL ρ u x) p
            (wμ volume ρ) := by
        intro m
        simp only [if_neg hu, sub_zero]
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => ?_) p
        have hs0 : 0 ≤ ((m : ℝ) + 1)⁻¹ := by positivity
        have hs1 : ((m : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [m.cast_nonneg (α := ℝ)])
        have hd : 1 ≤ (Idx.toList α).length - u.length := by omega
        have hpow : (((m : ℝ) + 1)⁻¹) ^ ((Idx.toList α).length - u.length) ≤ ((m : ℝ) + 1)⁻¹ :=
          pow_le_of_le_one hs0 hs1 (by omega)
        rw [norm_smul, Real.norm_eq_abs, lcoef_cutR, abs_mul, abs_of_nonneg (pow_nonneg hs0 _)]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul hpow (hB _) (abs_nonneg _) hs0
      have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (((m : ℝ) + 1)⁻¹ * B) *
          eLpNorm (derivL ρ u x) p (wμ volume ρ)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹ * B) atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const B
          simpa [one_div] using this
        have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1)
          (Or.inr (Lp.eLpNorm_ne_top (derivL ρ u x)))
        simpa using h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun m => zero_le) hbound
    · -- `|u| ≥ |α|`, `u ≠ α`: the coefficient vanishes
      have hz : ∀ m : ℕ, lcoef (cutR m) (Idx.toList α) u = 0 := by
        intro m
        rcases Nat.lt_or_ge (Idx.toList α).length u.length with h | h
        · exact lcoef_eq_zero _ h
        · rw [lcoef_diag _ (by omega), if_neg hu]
      refine tendsto_const_nhds.congr fun m => ?_
      simp [hz m, hu]

theorem W.cutoff_apply (m : ℕ) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    W.cutoff m x = W.mulCoeff (ρ := ρ) (bddDerivs_cutR k m) x := rfl

/-- **Cutoffs converge in `W^{k,p}(ρ)`**, `p < ∞`, for every weight. -/
theorem W.tendsto_cutoff (hp : p ≠ ⊤) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    Tendsto (fun m : ℕ => W.cutoff m x) atTop (𝓝 x) := by
  refine W.tendsto_of_deriv fun α => ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hα : Idx.toList α ∈ wordSet (n := n) k := by
    rw [mem_wordSet, Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  set term : ℕ → List (Fin n) → Eucl n → F := fun m u y =>
    lcoef (cutR m) (Idx.toList α) u y • (derivL ρ u x) y -
      (if u = Idx.toList α then (derivL ρ u x) y else 0) with hterm
  have hrep : ∀ m : ℕ, ⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α (W.cutoff m x)) -
      ⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α x) =ᵐ[wμ volume ρ]
        ∑ u ∈ wordSet k, term m u := by
    intro m
    rw [W.cutoff_apply]
    filter_upwards [W.coeFn_deriv_mulCoeff (bddDerivs_cutR k m) x α] with y hy
    rw [Pi.sub_apply, hy, Finset.sum_apply, hterm]
    simp only
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (wordSet k) (Idx.toList α), if_pos hα,
      derivL_toList]
    rfl
  have hmeas : ∀ m : ℕ, ∀ u ∈ wordSet (n := n) k,
      AEStronglyMeasurable (term m u) (wμ volume ρ) := by
    intro m u _
    have h2 : AEStronglyMeasurable (fun y => if u = Idx.toList α then (derivL ρ u x) y else 0)
        (wμ volume ρ) := by
      by_cases h : u = Idx.toList α
      · simp only [h, if_true]; exact Lp.aestronglyMeasurable _
      · simp only [h, if_false]; exact aestronglyMeasurable_const
    exact ((contDiff_lcoef (contDiff_cutR m) _ u).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)).sub h2
  have hle : ∀ m : ℕ, eLpNorm (⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α (W.cutoff m x)) -
      ⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α x)) p (wμ volume ρ) ≤
        ∑ u ∈ wordSet k, eLpNorm (term m u) p (wμ volume ρ) := by
    intro m
    rw [eLpNorm_congr_ae (hrep m)]
    exact eLpNorm_sum_le (hmeas m) Fact.out
  have hsum : Tendsto (fun m : ℕ => ∑ u ∈ wordSet k, eLpNorm (term m u) p (wμ volume ρ))
      atTop (𝓝 0) := by
    have := tendsto_finset_sum (wordSet k) fun u _ => tendsto_cutoff_term hp x α u
    simpa [hterm] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun m => zero_le) hle

/-- The value of `χ_m x` vanishes outside the ball of radius `2(m+1)`. -/
theorem W.cutoff_vanishes (m : ℕ) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ∀ᵐ y ∂volume, y ∉ closedBall (0 : Eucl n) (2 * ((m : ℝ) + 1)) →
      W.value (wholeSpace n) ρ 𝕜 F k p (W.cutoff m x) y = 0 := by
  have h := (ae_eq_wμ_iff volume ρ).mp (W.coeFn_value_mulCoeff (bddDerivs_cutR k m) x)
  rw [← W.cutoff_apply] at h
  filter_upwards [h] with y hy hyK
  rw [hy, cutR_eq_zero, zero_smul]
  rw [mem_closedBall_zero_iff, not_le] at hyK
  exact hyK.le

end CutoffW

/-! ### Density -/

section Density

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The shrinking bumps `rIn = 1/(j+2)`, `rOut = 1/(j+1)`. -/
def shrinkBump (n j : ℕ) : ContDiffBump (0 : Eucl n) :=
  ⟨((j : ℝ) + 2)⁻¹, ((j : ℝ) + 1)⁻¹, by positivity,
    (inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith)⟩

theorem tendsto_shrinkBump_rOut (n : ℕ) :
    Tendsto (fun j : ℕ => (shrinkBump n j).rOut) atTop (𝓝 0) := by
  simpa [shrinkBump, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- Elements whose value is (a.e.) a smooth compactly supported field. -/
def smoothSet (n k : ℕ) (𝕜 F : Type*) [NormedAddCommGroup F] [RCLike 𝕜]
    [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (W (wholeSpace n) 1 𝕜 F k p) :=
  {x | ∃ f : Eucl n → F, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (W.value (wholeSpace n) 1 𝕜 F k p x : Eucl n → F) =ᵐ[volume] f}

/-- **Density of `C_c^∞` in `W^{k,p}(ℝⁿ)`** (S4, `W.dense_smooth`), weight `1`, `1 ≤ p < ∞`:
the elements whose value is a smooth compactly supported field are dense. -/
theorem W.dense_smooth (hp : p ≠ ⊤) :
    Dense {x : W (wholeSpace n) 1 𝕜 F k p | ∃ f : Eucl n → F, ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧ (W.value (wholeSpace n) 1 𝕜 F k p x : Eucl n → F) =ᵐ[volume] f} := by
  set S := {x : W (wholeSpace n) 1 𝕜 F k p | ∃ f : Eucl n → F, ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧ (W.value (wholeSpace n) 1 𝕜 F k p x : Eucl n → F) =ᵐ[volume] f}
  set T := {y : W (wholeSpace n) 1 𝕜 F k p | ∃ K : Set (Eucl n), IsCompact K ∧
      ∀ᵐ z ∂volume, z ∉ K → W.value (wholeSpace n) 1 𝕜 F k p y z = 0}
  have hTS : T ⊆ closure S := by
    rintro y ⟨K, hK, hyK⟩
    refine mem_closure_of_tendsto (W.tendsto_mollify hp (tendsto_shrinkBump_rOut n) y)
      (Eventually.of_forall fun j => ?_)
    exact ⟨_, W.contDiff_mollify (shrinkBump n j) y,
      W.hasCompactSupport_mollify (shrinkBump n j) y hK hyK,
      W.coeFn_value_mollify hp (shrinkBump n j) y⟩
  have hT : ∀ x, x ∈ closure T := by
    intro x
    refine mem_closure_of_tendsto (W.tendsto_cutoff hp x) (Eventually.of_forall fun m => ?_)
    exact ⟨_, isCompact_closedBall 0 _, W.cutoff_vanishes m x⟩
  intro x
  exact closure_minimal hTS isClosed_closure (hT x)

/-- Sequential form of the density: every `x ∈ W^{k,p}(ℝⁿ)` is the limit of elements with
smooth compactly supported values. -/
theorem W.exists_seq_smooth (hp : p ≠ ⊤) (x : W (wholeSpace n) 1 𝕜 F k p) :
    ∃ y : ℕ → W (wholeSpace n) 1 𝕜 F k p, (∀ j, ∃ f : Eucl n → F, ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧ (W.value (wholeSpace n) 1 𝕜 F k p (y j) : Eucl n → F) =ᵐ[volume] f)
        ∧ Tendsto y atTop (𝓝 x) := by
  have h := (W.dense_smooth (𝕜 := 𝕜) (F := F) (k := k) hp).closure_eq ▸ Set.mem_univ x
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp h
  exact ⟨y, hy, hlim⟩

end Density

end UnforcedLeray.Sob
