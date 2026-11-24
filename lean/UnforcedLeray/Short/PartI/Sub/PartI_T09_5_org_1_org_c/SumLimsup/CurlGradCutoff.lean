import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.SumLimsup
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# `PartI:T09/5/org/1/org/c/1/1`: the cutoff curl-gradient identity

Source: `the November 2 reference manuscript`, lines 283-286.  Proves the leaf
`CurlGradCutoff` of `Sub/PartI_T09_5_org_1_org_c/SumLimsup.lean`.

Strategy.  With `a = ∂_q g₀`, `b = ∂_η g₀`, `e = ∂_q g₁`, `d = ∂_η g₁` and `a + d = 0`, the
pointwise identity `a² + e² + (b² + d²) = (e - b)² - 2 (a d - b e)` holds.  The mixed partials
commute (`ForcingIBP.comm_QE`), so `a d - b e = ∂_q (g₀ d) - ∂_η (g₀ e)`.  Multiplying by the
`q`-independent cutoff `χ = etaCutoff R` and using `CellDerivZero` on `χ g₀ d` and `χ g₀ e`
(both vanish for `|η| ≥ 2R`) gives `∫ χ (a d - b e) = ∫ χ' g₀ e`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The cutoff facts used here, at radius `R ≥ 1`. -/
theorem cgc_cutoff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (etaCutoff R) ∧ (∀ η : ℝ, 2 * R ≤ |η| → etaCutoff R η = 0) ∧
      (∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0) := by
  obtain ⟨C₀, _, h⟩ := etaCutoffFacts
  obtain ⟨hs, _, _, hz, hd⟩ := h R hR
  refine ⟨hs, hz, fun η hη => ?_⟩
  have h1 := hd η
  rw [hz η hη, Real.sqrt_zero, mul_zero] at h1
  exact abs_nonpos_iff.mp h1

theorem cgc_q_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun w => f w * g w) z = Cyl.partialQ f z * g z + f z * Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).mul (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

theorem cgc_eta_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun w => f w * g w) z = Cyl.partialEta f z * g z + f z * Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

theorem cgc_q_chi (χ : ℝ → ℝ) (f : Plane → ℝ) (hf : Differentiable ℝ f) (z : Plane) :
    Cyl.partialQ (fun w => χ w.2 * f w) z = χ z.2 * Cyl.partialQ f z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).const_mul (χ z.2)).deriv

theorem cgc_eta_chi (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ) (f : Plane → ℝ)
    (hf : Differentiable ℝ f) (z : Plane) :
    Cyl.partialEta (fun w => χ w.2 * f w) z =
      deriv χ z.2 * f z + χ z.2 * Cyl.partialEta f z :=
  ((hχ z.2).hasDerivAt.mul (Cyl.hasDerivAt_sliceEta hf z.1 z.2)).deriv

/-- Splitting a cell integral of a sum. -/
theorem cgc_split (c : ℝ) (T P Q W : Plane → ℝ) (hP : IntegrableOn P (Cyl.cell c))
    (hQ : IntegrableOn Q (Cyl.cell c)) (hW : IntegrableOn W (Cyl.cell c))
    (hTe : ∀ z, T z = P z - Q z + W z) :
    ∫ z in Cyl.cell c, T z = (∫ z in Cyl.cell c, P z) - (∫ z in Cyl.cell c, Q z) +
      ∫ z in Cyl.cell c, W z := by
  simp_rw [hTe]
  have h1 : IntegrableOn (fun z => P z - Q z) (Cyl.cell c) := hP.sub hQ
  rw [integral_add h1 hW, integral_sub hP hQ]

theorem curlGradCutoff_proof : CurlGradCutoff := by
  intro c g₀ g₁ hc hg₀ hg₁ hp₀ hp₁ hdiv R hR
  have hR1 : (1 : ℝ) ≤ R := hR
  have hR0 : 0 < R := by linarith
  obtain ⟨hχs, hχz, hχd⟩ := cgc_cutoff R hR
  have hχD : Differentiable ℝ (etaCutoff R) := hχs.differentiable (by simp)
  have hχC : Continuous (etaCutoff R) := hχs.continuous
  have hχ'C : Continuous (deriv (etaCutoff R)) := hχs.continuous_deriv (by simp)
  have hg₀D : Differentiable ℝ g₀ := hg₀.differentiable (by simp)
  have hg₀C : Continuous g₀ := hg₀.continuous
  have hE₁s : ContDiff ℝ ∞ (Cyl.partialEta g₁) := ForcingIBP.cd_partialEta hg₁
  have hQ₁s : ContDiff ℝ ∞ (Cyl.partialQ g₁) := ForcingIBP.cd_partialQ hg₁
  have hE₀s : ContDiff ℝ ∞ (Cyl.partialEta g₀) := ForcingIBP.cd_partialEta hg₀
  have hQ₀s : ContDiff ℝ ∞ (Cyl.partialQ g₀) := ForcingIBP.cd_partialQ hg₀
  have hE₁D : Differentiable ℝ (Cyl.partialEta g₁) := hE₁s.differentiable (by simp)
  have hQ₁D : Differentiable ℝ (Cyl.partialQ g₁) := hQ₁s.differentiable (by simp)
  have hQ₁C : Continuous (Cyl.partialQ g₁) := hQ₁s.continuous
  have hE₁C : Continuous (Cyl.partialEta g₁) := hE₁s.continuous
  have hQ₀C : Continuous (Cyl.partialQ g₀) := hQ₀s.continuous
  have hE₀C : Continuous (Cyl.partialEta g₀) := hE₀s.continuous
  have hcomm : ∀ z : Plane,
      Cyl.partialQ (Cyl.partialEta g₁) z = Cyl.partialEta (Cyl.partialQ g₁) z :=
    fun z => congrFun (ForcingIBP.comm_QE hg₁) z
  have hG1s : ContDiff ℝ ∞ (fun w : Plane => g₀ w * Cyl.partialEta g₁ w) := hg₀.mul hE₁s
  have hG2s : ContDiff ℝ ∞ (fun w : Plane => g₀ w * Cyl.partialQ g₁ w) := hg₀.mul hQ₁s
  have hH1s : ContDiff ℝ ∞
      (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialEta g₁ w)) :=
    (hχs.comp contDiff_snd).mul hG1s
  have hH2s : ContDiff ℝ ∞
      (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialQ g₁ w)) :=
    (hχs.comp contDiff_snd).mul hG2s
  have hper1 : Cyl.IsPeriodic c
      (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialEta g₁ w)) := by
    intro z
    show etaCutoff R z.2 * (g₀ (z.1 + c, z.2) * Cyl.partialEta g₁ (z.1 + c, z.2)) =
      etaCutoff R z.2 * (g₀ z * Cyl.partialEta g₁ z)
    rw [hp₀ z, hp₁.partialEta z]
  have hper2 : Cyl.IsPeriodic c
      (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialQ g₁ w)) := by
    intro z
    show etaCutoff R z.2 * (g₀ (z.1 + c, z.2) * Cyl.partialQ g₁ (z.1 + c, z.2)) =
      etaCutoff R z.2 * (g₀ z * Cyl.partialQ g₁ z)
    rw [hp₀ z, hp₁.partialQ z]
  have hvan1 : ∀ z : Plane, 2 * R ≤ |z.2| →
      etaCutoff R z.2 * (g₀ z * Cyl.partialEta g₁ z) = 0 := fun z hz => by
    rw [hχz z.2 hz, zero_mul]
  have hvan2 : ∀ z : Plane, 2 * R ≤ |z.2| →
      etaCutoff R z.2 * (g₀ z * Cyl.partialQ g₁ z) = 0 := fun z hz => by
    rw [hχz z.2 hz, zero_mul]
  -- the two cell integration-by-parts identities
  have hP0 : ∫ z in Cyl.cell c,
      Cyl.partialQ (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialEta g₁ w)) z = 0 :=
    (cellDerivZero_of_periodic c R hc hR0 _ (hH1s.of_le (by simp)) hper1 hvan1).1
  have hQ0 : ∫ z in Cyl.cell c,
      Cyl.partialEta (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialQ g₁ w)) z = 0 :=
    (cellDerivZero_of_periodic c R hc hR0 _ (hH2s.of_le (by simp)) hper2 hvan2).2
  -- pointwise derivative formulas
  have hG1D : Differentiable ℝ (fun w : Plane => g₀ w * Cyl.partialEta g₁ w) :=
    hg₀D.mul hE₁D
  have hG2D : Differentiable ℝ (fun w : Plane => g₀ w * Cyl.partialQ g₁ w) :=
    hg₀D.mul hQ₁D
  have hP : ∀ z : Plane,
      Cyl.partialQ (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialEta g₁ w)) z =
        etaCutoff R z.2 * (Cyl.partialQ g₀ z * Cyl.partialEta g₁ z +
          g₀ z * Cyl.partialEta (Cyl.partialQ g₁) z) := by
    intro z
    rw [cgc_q_chi (etaCutoff R) _ hG1D z, cgc_q_mul g₀ _ hg₀D hE₁D z, hcomm z]
  have hQ : ∀ z : Plane,
      Cyl.partialEta (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialQ g₁ w)) z =
        deriv (etaCutoff R) z.2 * (g₀ z * Cyl.partialQ g₁ z) +
          etaCutoff R z.2 * (Cyl.partialEta g₀ z * Cyl.partialQ g₁ z +
            g₀ z * Cyl.partialEta (Cyl.partialQ g₁) z) := by
    intro z
    rw [cgc_eta_chi (etaCutoff R) hχD _ hG2D z, cgc_eta_mul g₀ _ hg₀D hQ₁D z]
  have hTe : ∀ z : Plane,
      etaCutoff R z.2 * (Cyl.partialQ g₀ z * Cyl.partialEta g₁ z -
          Cyl.partialEta g₀ z * Cyl.partialQ g₁ z) =
        Cyl.partialQ (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialEta g₁ w)) z -
          Cyl.partialEta (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialQ g₁ w)) z +
          deriv (etaCutoff R) z.2 * (g₀ z * Cyl.partialQ g₁ z) := by
    intro z
    rw [hP z, hQ z]
    ring
  -- integrability
  have hPi : IntegrableOn (fun z : Plane =>
      Cyl.partialQ (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialEta g₁ w)) z)
      (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _ (ForcingIBP.cd_partialQ hH1s).continuous
      (fun z hz => by simp only [hP z, hχz z.2 hz, zero_mul])
  have hQi : IntegrableOn (fun z : Plane =>
      Cyl.partialEta (fun w : Plane => etaCutoff R w.2 * (g₀ w * Cyl.partialQ g₁ w)) z)
      (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _ (ForcingIBP.cd_partialEta hH2s).continuous
      (fun z hz => by simp only [hQ z, hχz z.2 hz, hχd z.2 hz, zero_mul, add_zero])
  have hWi : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (g₀ z * Cyl.partialQ g₁ z))
      (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _
      ((hχ'C.comp continuous_snd).mul (hg₀C.mul hQ₁C))
      (fun z hz => by simp only [hχd z.2 hz, zero_mul])
  have hTi : IntegrableOn (fun z : Plane => etaCutoff R z.2 * (Cyl.partialQ g₀ z *
      Cyl.partialEta g₁ z - Cyl.partialEta g₀ z * Cyl.partialQ g₁ z)) (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _
      ((hχC.comp continuous_snd).mul ((hQ₀C.mul hE₁C).sub (hE₀C.mul hQ₁C)))
      (fun z hz => by simp only [hχz z.2 hz, zero_mul])
  have hLi : IntegrableOn (fun z : Plane => etaCutoff R z.2 *
      (Cyl.partialQ g₁ z - Cyl.partialEta g₀ z) ^ 2) (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _
      ((hχC.comp continuous_snd).mul ((hQ₁C.sub hE₀C).pow 2))
      (fun z hz => by simp only [hχz z.2 hz, zero_mul])
  -- ∫ T = ∫ W
  have hTW : ∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ g₀ z * Cyl.partialEta g₁ z -
      Cyl.partialEta g₀ z * Cyl.partialQ g₁ z) =
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (g₀ z * Cyl.partialQ g₁ z) := by
    rw [cgc_split c _ _ _ _ hPi hQi hWi hTe, hP0, hQ0, sub_zero, zero_add]
  -- pointwise rewrite of the left integrand
  have hLeq : ∀ z : Plane,
      etaCutoff R z.2 * ((Cyl.partialQ g₀ z) ^ 2 + (Cyl.partialQ g₁ z) ^ 2 +
        ((Cyl.partialEta g₀ z) ^ 2 + (Cyl.partialEta g₁ z) ^ 2)) =
      etaCutoff R z.2 * (Cyl.partialQ g₁ z - Cyl.partialEta g₀ z) ^ 2 -
        2 * (etaCutoff R z.2 * (Cyl.partialQ g₀ z * Cyl.partialEta g₁ z -
          Cyl.partialEta g₀ z * Cyl.partialQ g₁ z)) := by
    intro z
    have hd : Cyl.partialEta g₁ z = -Cyl.partialQ g₀ z := by linarith [hdiv z]
    rw [hd]
    ring
  simp_rw [hLeq]
  rw [integral_sub hLi (hTi.const_mul 2), integral_const_mul, hTW]

end UnforcedLeray.Short.PartI
