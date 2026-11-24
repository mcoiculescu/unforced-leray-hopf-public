import UnforcedLeray.Lib.ComplexODE.L1Dependence
import UnforcedLeray.Analysis.Rayleigh.Evans.Solution

/-!
# B0034 helper: integral (L¹) dependence of linear ODE solutions on the coefficient

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Tool of the local bifurcation behind B0034 (`paper/main.tex`, lines 1012–1021; Lin
2003, Theorem 5.9). Copied, with a repair, from the draft

(lemma `norm_sub_le_integral_of_isSolOn`, which does not compile in the current
toolchain): two solutions of `F'' = V F` with equal data at `a` differ on `[a, b]`
by at most `(B ∫|V₁ - V₀|) exp((b - a) + ∫|V₁|)`, `B = sup |F₀|`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory Topology
namespace UnforcedLeray.ComplexODEB
open NonUniqueEuler.LinODE UnforcedLeray.Rayleigh.Evans

/-- An integral perturbation estimate for genuine solutions with the same initial data.
The pair carries its standard maximum norm. Only the reference first component
needs a uniform bound. -/
theorem norm_sub_le_integral_of_isSolOn'
    {a b B : ℝ} {V₁ V₀ f₁ g₁ f₀ g₀ : ℝ → ℂ}
    (hab : a ≤ b) (hV₁ : ContinuousOn V₁ (Icc a b))
    (hV₀ : ContinuousOn V₀ (Icc a b))
    (h₁ : IsSolOn V₁ (Icc a b) f₁ g₁)
    (h₀ : IsSolOn V₀ (Icc a b) f₀ g₀)
    (hf : f₁ a = f₀ a) (hg : g₁ a = g₀ a)
    (hB : ∀ t ∈ Icc a b, ‖f₀ t‖ ≤ B) :
    ∀ t ∈ Icc a b,
      ‖(f₁ t - f₀ t, g₁ t - g₀ t)‖ ≤
        (B * ∫ s in a..b, ‖V₁ s - V₀ s‖) *
          Real.exp ((b - a) + ∫ s in a..b, ‖V₁ s‖) := by
  let z : ℝ → ℂ × ℂ := fun t => (f₁ t - f₀ t, g₁ t - g₀ t)
  let z' : ℝ → ℂ × ℂ := fun t => (g₁ t - g₀ t, V₁ t * f₁ t - V₀ t * f₀ t)
  let e : ℝ → ℝ := fun t => ‖z t‖
  let k : ℝ → ℝ := fun t => 1 + ‖V₁ t‖
  let q : ℝ → ℝ := fun t => ‖V₁ t - V₀ t‖
  let ε : ℝ := B * ∫ s in a..b, q s
  have hz : ContinuousOn z (Icc a b) :=
    (h₁.continuousOn.sub h₀.continuousOn).prodMk
      (h₁.continuousOn'.sub h₀.continuousOn')
  have hz' : ContinuousOn z' (Icc a b) :=
    (h₁.continuousOn'.sub h₀.continuousOn').prodMk
      ((hV₁.mul h₁.continuousOn).sub (hV₀.mul h₀.continuousOn))
  have he : ContinuousOn e (Icc a b) := hz.norm
  have hk : ContinuousOn k (Icc a b) := continuousOn_const.add hV₁.norm
  have hq : ContinuousOn q (Icc a b) := (hV₁.sub hV₀).norm
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  have hk0 (t : ℝ) : 0 ≤ k t := by dsimp [k]; positivity
  have hq0 (t : ℝ) : 0 ≤ q t := norm_nonneg _
  have hε0 : 0 ≤ ε := mul_nonneg hB0
    (intervalIntegral.integral_nonneg_of_forall hab hq0)
  have hza : z a = 0 := by simp [z, hf, hg]
  have hdz (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt z (z' t) t :=
    (((h₁.hasDerivWithinAt t (Ioo_subset_Icc_self ht)).sub
      (h₀.hasDerivWithinAt t (Ioo_subset_Icc_self ht))).prodMk
      ((h₁.hasDerivWithinAt' t (Ioo_subset_Icc_self ht)).sub
        (h₀.hasDerivWithinAt' t (Ioo_subset_Icc_self ht)))).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      ‖z' t‖ ≤ k t * e t + B * q t := by
    have hid : z' t = ((z t).2, V₁ t * (z t).1 + (V₁ t - V₀ t) * f₀ t) := by
      dsimp [z, z']; congr 1; ring
    rw [hid]
    apply GronwallAux.norm_deriv_pair_le (by dsimp [k]; linarith [norm_nonneg (V₁ t)])
      (mul_nonneg hB0 (hq0 t))
    · dsimp [k]; linarith [norm_nonneg (V₁ t)]
    · rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB t ht) (hq0 t)
  have hint (t : ℝ) (ht : t ∈ Icc a b) :
      e t ≤ ε + ∫ s in a..t, k s * e s := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hzt : (∫ s in a..t, z' s) = z t := by
      simpa [hza] using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hz.mono hsub) (fun s hs => hdz s ⟨hs.1, hs.2.trans_le ht.2⟩)
        ((hz'.mono hsub).intervalIntegrable_of_Icc ht.1)
    have hqi : (∫ s in a..t, q s) ≤ ∫ s in a..b, q s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (ae_of_all _ hq0) (hq.intervalIntegrable_of_Icc hab)
    calc
      e t = ‖∫ s in a..t, z' s‖ := by rw [hzt]
      _ ≤ ∫ s in a..t, ‖z' s‖ := intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t, k s * e s + B * q s :=
        intervalIntegral.integral_mono_on ht.1
          ((hz'.norm.mono hsub).intervalIntegrable_of_Icc ht.1)
          ((((hk.mul he).add (continuousOn_const.mul hq)).mono hsub).intervalIntegrable_of_Icc ht.1)
          (fun s hs => hbound s (hsub hs))
      _ = (∫ s in a..t, k s * e s) + B * ∫ s in a..t, q s := by
        have i1 : IntervalIntegrable (fun s => k s * e s) volume a t :=
          ((hk.mul he).mono hsub).intervalIntegrable_of_Icc ht.1
        have i2 : IntervalIntegrable (fun s => B * q s) volume a t :=
          ((continuousOn_const.mul hq).mono hsub).intervalIntegrable_of_Icc ht.1
        rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul]
      _ ≤ ε + ∫ s in a..t, k s * e s := by
        dsimp [ε]; linarith [mul_le_mul_of_nonneg_left hqi hB0]
  have hgr := integral_gronwall_of_continuousOn he hk (fun t _ => hk0 t) hε0 hint
  intro t ht
  have hki : (∫ s in a..t, k s) ≤ ∫ s in a..b, k s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ hk0) (hk.intervalIntegrable_of_Icc hab)
  have hkeq : (∫ s in a..b, k s) = (b - a) + ∫ s in a..b, ‖V₁ s‖ := by
    dsimp [k]
    rw [intervalIntegral.integral_add
      (continuous_const.intervalIntegrable a b) (hV₁.norm.intervalIntegrable_of_Icc hab)]
    simp
  exact (hgr t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hki.trans_eq hkeq)) hε0)

end UnforcedLeray.ComplexODEB
