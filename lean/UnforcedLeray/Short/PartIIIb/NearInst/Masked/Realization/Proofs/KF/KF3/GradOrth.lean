import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.GradOrth.Cutoff

/-!
# `kf3GradOrth` (source 117-120): gradients of decaying periodic functions are orthogonal to the
solenoidal fields

For `p` smooth, `2εc`-periodic in `τ`, with `|p| ≤ C/(1+|x|)` and `∇ₓp ∈ L²`, the cutoffs
`φ_n = cut(n+1) · p` are physical tests, so `physGrad φ_n ∈ (physSolenoidal)ᗮ`.  Their gradients
converge to `∇ₓp` in `L²` by dominated convergence: pointwise `∇ₓφ_n = ∇ₓp` once `n+1 > |x|`
(`gradX_mul_cut_sub`), and the difference is dominated by `2|∇ₓp|² + 18(C K)²(1+|x|)^{-4}`
(`bound_pointwise`).  The orthogonal complement is closed, so the limit lies in it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.B0226 UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.GradOrthAux

/-- Pure algebra: `b ≤ (A/u)(K/N)` with `1 ≤ u ≤ 3N`, `1 ≤ N` gives `b² ≤ 9 (AK)²/u⁴`. -/
theorem sq_bound_aux {A K0 u N b : ℝ} (hA : 0 ≤ A) (hK0 : 0 ≤ K0) (hu : 1 ≤ u) (hN : 1 ≤ N)
    (huN : u ≤ 3 * N) (hb0 : 0 ≤ b) (hb : b ≤ A / u * (K0 / N)) :
    b ^ 2 ≤ 9 * (A * K0) ^ 2 * (u ^ 4)⁻¹ := by
  have hu0 : 0 < u := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : b ^ 2 ≤ (A / u * (K0 / N)) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have h2 : (A / u * (K0 / N)) ^ 2 = (A * K0) ^ 2 / (u ^ 2 * N ^ 2) := by
    rw [div_mul_div_comm, div_pow, mul_pow, mul_pow]
  have hu2 : u ^ 2 ≤ 9 * N ^ 2 := by nlinarith
  have h3 : (A * K0) ^ 2 / (u ^ 2 * N ^ 2) ≤ 9 * (A * K0) ^ 2 * (u ^ 4)⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have hu4 : (u ^ 4)⁻¹ * u ^ 4 = 1 := inv_mul_cancel₀ (by positivity)
    have hkey : (A * K0) ^ 2 ≤ 9 * (A * K0) ^ 2 * (u ^ 4)⁻¹ * (u ^ 2 * N ^ 2) := by
      have hsq : 0 ≤ (A * K0) ^ 2 := sq_nonneg _
      have hpos : 0 ≤ (u ^ 4)⁻¹ := by positivity
      have : 9 * (A * K0) ^ 2 * (u ^ 4)⁻¹ * (u ^ 2 * N ^ 2) =
          (A * K0) ^ 2 * (9 * N ^ 2 * u ^ 2) * (u ^ 4)⁻¹ := by ring
      rw [this]
      have h9 : u ^ 4 ≤ 9 * N ^ 2 * u ^ 2 := by nlinarith
      have : (A * K0) ^ 2 * u ^ 4 * (u ^ 4)⁻¹ ≤ (A * K0) ^ 2 * (9 * N ^ 2 * u ^ 2) * (u ^ 4)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hpos
        exact mul_le_mul_of_nonneg_left h9 hsq
      rwa [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one] at this
    exact hkey
  linarith

/-- Pointwise bound for the cutoff gradient error, uniform in the scale `N ≥ 1`. -/
theorem bound_pointwise (p : Space × ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (C K : ℝ) (hC0 : 0 ≤ C)
    (hK0 : 0 ≤ K) (hK : ∀ z : Space, ‖fderiv ℝ chiB z‖ ≤ K)
    (hC : ∀ y : Space × ℝ, |p y| ≤ C / (1 + ‖y.1‖)) (N : ℝ) (hN : 1 ≤ N) (y : Space × ℝ) :
    ‖gradX (fun z : Space × ℝ => cut N z.1 * p z) y - gradX p y‖ ^ 2 ≤
      2 * ‖gradX p y‖ ^ 2 + 18 * (C * K) ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have h1 := norm_gradX_mul_cut_sub_le p hp N y
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hb : (|p y| * ‖fderiv ℝ (cut N) y.1‖) ^ 2 ≤ 9 * (C * K) ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹ := by
    rcases le_or_gt ‖y.1‖ (2 * N) with h | h
    · have hM : ‖fderiv ℝ (cut N) y.1‖ ≤ K * N⁻¹ := cut_fderiv_bound hK hN0 y.1
      have hpy := hC y
      have hu1 : (1 : ℝ) ≤ 1 + ‖y.1‖ := by linarith [norm_nonneg y.1]
      have huN : 1 + ‖y.1‖ ≤ 3 * N := by linarith
      have hdiv : K * N⁻¹ = K / N := by rw [div_eq_mul_inv]
      have hbound : |p y| * ‖fderiv ℝ (cut N) y.1‖ ≤ C / (1 + ‖y.1‖) * (K / N) := by
        rw [← hdiv]
        exact mul_le_mul hpy hM (norm_nonneg _) (div_nonneg hC0 (by positivity))
      exact sq_bound_aux hC0 hK0 hu1 hN huN (by positivity) hbound
    · have h0 := cut_fderiv_zero_of_gt hN0 h
      have hnn : (0 : ℝ) ≤ 9 * (C * K) ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹ := by positivity
      rw [h0, norm_zero, mul_zero]
      simpa using hnn
  nlinarith [sq_nonneg (‖gradX p y‖ - |p y| * ‖fderiv ℝ (cut N) y.1‖)]

theorem kf3GradOrth : KF3GradOrth := by
  intro ε c p hp hper hdec hp_L2
  obtain ⟨C, hC⟩ := hdec
  have hC' : ∀ y : Space × ℝ, |p y| ≤ |C| / (1 + ‖y.1‖) := fun y =>
    (hC y).trans (div_le_div_of_nonneg_right (le_abs_self C) (by positivity))
  have hC0 : 0 ≤ |C| := abs_nonneg C
  obtain ⟨K, hKb⟩ := chiB_fderiv_bound
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hKb 0)
  -- the approximating tests
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℕ → Space × ℝ → ℝ,
      ∀ n z, φ n z = cut ((n : ℝ) + 1) z.1 * p z := ⟨_, fun _ _ => rfl⟩
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hNge : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfun : ∀ n, φ n = fun z => cut ((n : ℝ) + 1) z.1 * p z := fun n => funext (hφdef n)
  have hφs : ∀ n, IsPhysTest (2 * ε * c) (φ n) := by
    intro n
    refine ⟨?_, ?_, ?_⟩
    · rw [hfun n]
      exact ((cut_contDiff _).comp contDiff_fst).mul hp
    · intro x τ
      rw [hfun n]
      simp only
      rw [hper x τ]
    · refine ⟨2 * ((n : ℝ) + 1), fun y hy => ?_⟩
      by_contra h
      have h2 := not_le.1 h
      apply hy
      rw [hfun n]
      simp only
      rw [cut_eq_zero (hNpos n) h2.le, zero_mul]
  -- pointwise convergence
  have hpt : ∀ y : Space × ℝ,
      Tendsto (fun n : ℕ => ‖gradX (φ n) y - gradX p y‖ ^ 2) atTop (𝓝 0) := by
    intro y
    obtain ⟨m, hm⟩ := exists_nat_gt ‖y.1‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : ‖y.1‖ < (n : ℝ) + 1 := by linarith
    have h0 : gradX (φ n) y - gradX p y = 0 := by
      rw [hfun n, gradX_mul_cut_sub p hp _ y, cut_eq_one (hNpos n) hlt.le,
        cut_fderiv_zero_of_lt (hNpos n) hlt]
      simp
    rw [h0]
    simp
  -- integrable dominator
  have hBint : Integrable (fun y : Space × ℝ =>
      2 * ‖gradX p y‖ ^ 2 + 18 * (|C| * K) ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹)
      (UnforcedLeray.B0220.physMeasure ε c) := by
    refine Integrable.add ?_ ?_
    · exact ((memLp_two_iff_integrable_sq_norm hp_L2.aestronglyMeasurable).1 hp_L2).const_mul 2
    · exact (integrable_decay4 ε c).const_mul _
  have hcontφ : ∀ n, Continuous (gradX (φ n)) := fun n => continuous_gradX (hφs n).smooth
  have hcontp : Continuous (gradX p) := continuous_gradX hp
  -- dominated convergence of the squared errors
  have hdc : Tendsto (fun n : ℕ => ∫ y, ‖gradX (φ n) y - gradX p y‖ ^ 2
      ∂(UnforcedLeray.B0220.physMeasure ε c)) atTop
      (𝓝 (∫ _ : Space × ℝ, (0 : ℝ) ∂(UnforcedLeray.B0220.physMeasure ε c))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y : Space × ℝ => 2 * ‖gradX p y‖ ^ 2 + 18 * (|C| * K) ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹)
      (fun n => ?_) hBint (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => hpt y)
    · exact ((((hcontφ n).sub hcontp).norm.pow 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have hb := bound_pointwise p hp |C| K hC0 hK0 hKb hC' ((n : ℝ) + 1) (hNge n) y
      rw [hfun n]
      exact hb
  rw [integral_zero] at hdc
  -- the same in the `eLpNorm` form
  have hE : ∀ n : ℕ, eLpNorm (gradX (φ n) - gradX p) 2 (UnforcedLeray.B0220.physMeasure ε c) =
      ENNReal.ofReal ((∫ y, ‖gradX (φ n) y - gradX p y‖ ^ 2
        ∂(UnforcedLeray.B0220.physMeasure ε c)) ^ (2 : ℝ)⁻¹) := by
    intro n
    have hmem : MemLp (gradX (φ n) - gradX p) 2 (UnforcedLeray.B0220.physMeasure ε c) :=
      (memLp_gradX (hφs n)).sub hp_L2
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat, Real.rpow_two]
  have hpow : Tendsto (fun n : ℕ => (∫ y, ‖gradX (φ n) y - gradX p y‖ ^ 2
      ∂(UnforcedLeray.B0220.physMeasure ε c)) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := hdc.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    rwa [Real.zero_rpow (by norm_num)] at h
  have hT : Tendsto (fun n : ℕ => eLpNorm (gradX (φ n) - gradX p) 2
      (UnforcedLeray.B0220.physMeasure ε c)) atTop (𝓝 0) := by
    simp_rw [hE]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal hpow
  have hlim : Tendsto (fun n : ℕ => physGrad ε c ⟨φ n, hφs n⟩) atTop
      (𝓝 (hp_L2.toLp (gradX p))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => gradX (φ n))
      (fun n => memLp_gradX (hφs n)) (gradX p) hp_L2).2 hT
  exact (Submodule.isClosed_orthogonal _).mem_of_tendsto hlim
    (Eventually.of_forall fun n => physGrad_mem_orthogonal _)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
