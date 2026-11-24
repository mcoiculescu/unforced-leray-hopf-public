import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1

/-!
# Decomposition of `T0gGaussParam`

Source `the November 2 reference manuscript`
1640-1656: smoothness of the Gaussian average `H(r,s,z) = ∫ G1(w) F(s, z - ι(r w)) dw`.
Reduction to (i) polynomial moments of the Gaussian, (ii) polynomial-in-`w` growth of the
derivatives of the integrand family (composition with a linear map of norm `≤ c(1+‖w‖)`),
(iii) the generic parametric-integral smoothness theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Polynomial moments of the standard Gaussian on `ℝ²`. -/
def T0gPolyGauss : Prop :=
  ∀ N : ℕ, MeasureTheory.Integrable (fun w : UnforcedLeray.Gaussian.Euc 2 =>
    (1 + ‖w‖) ^ N * UnforcedLeray.Gaussian.gaussKernel 2 1 w)

/-- Derivatives (in the parameter) of `F(s, z - ι(r w))` grow polynomially in `w`. -/
def T0gGrowthComp : Prop :=
  ∀ (F : UnforcedLeray.B0220.Profile → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
    (∀ k : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k F p‖ ≤ C) → ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ,
      ∀ (x : ℝ × ℝ × (ℝ × ℝ)) (w : UnforcedLeray.Gaussian.Euc 2),
        ‖iteratedFDeriv ℝ k (fun y : ℝ × ℝ × (ℝ × ℝ) =>
          F (y.2.1, y.2.2 - UnforcedLeray.B0224.planeι (y.1 • w))) x‖ ≤ C * (1 + ‖w‖) ^ N

/-- Generic parametric smoothness of the Gaussian average of a jointly smooth family whose
`x`-derivatives of every order grow polynomially in `w`. -/
def T0gContDiffParam : Prop :=
  ∀ (X V : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (n : ℕ)
    (K : X → UnforcedLeray.Gaussian.Euc 2 → V),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × UnforcedLeray.Gaussian.Euc 2 => K p.1 p.2) →
    (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ x w,
      ‖iteratedFDeriv ℝ k (fun y => K y w) x‖ ≤ C * (1 + ‖w‖) ^ N) →
    ContDiff ℝ (n : WithTop ℕ∞)
      (fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • K x w)

/-- One differentiation under the integral sign (dominated by `C (1+‖w‖)^N G1(w)`, integrable
by `T0gPolyGauss`; Mathlib `hasFDerivAt_integral_of_dominated_of_fderiv_le`). -/
def T0gDiffParam : Prop :=
  T0gPolyGauss → ∀ (X V : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (K : X → UnforcedLeray.Gaussian.Euc 2 → V),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × UnforcedLeray.Gaussian.Euc 2 => K p.1 p.2) →
    (∃ C : ℝ, ∃ N : ℕ, ∀ x w, ‖K x w‖ ≤ C * (1 + ‖w‖) ^ N) →
    (∃ C : ℝ, ∃ N : ℕ, ∀ x w, ‖fderiv ℝ (fun y => K y w) x‖ ≤ C * (1 + ‖w‖) ^ N) →
    ∀ x, HasFDerivAt (fun x => ∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • K x w)
      (∫ w, UnforcedLeray.Gaussian.gaussKernel 2 1 w • fderiv ℝ (fun y => K y w) x) x

theorem t0gGaussParam_proof_of (hG : T0gGrowthComp) (hP : T0gContDiffParam) :
    T0gGaussParam := by
  intro F hF hbd
  have hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ × (ℝ × ℝ)) × UnforcedLeray.Gaussian.Euc 2 =>
        F (p.1.2.1, p.1.2.2 - UnforcedLeray.B0224.planeι (p.1.1 • p.2))) := by
    refine hF.comp ?_
    simp only [UnforcedLeray.B0224.planeι_apply, PiLp.smul_apply, smul_eq_mul]
    have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ × (ℝ × ℝ)) × UnforcedLeray.Gaussian.Euc 2 => p.2 0) :=
      ContDiff.comp (g := fun v : UnforcedLeray.Gaussian.Euc 2 => v 0) (f := Prod.snd)
        (by simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff) contDiff_snd
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ × (ℝ × ℝ)) × UnforcedLeray.Gaussian.Euc 2 => p.2 1) :=
      ContDiff.comp (g := fun v : UnforcedLeray.Gaussian.Euc 2 => v 1) (f := Prod.snd)
        (by simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff) contDiff_snd
    have ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ × (ℝ × ℝ)) × UnforcedLeray.Gaussian.Euc 2 => p.1.1) :=
      contDiff_fst.comp contDiff_fst
    have hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ × (ℝ × ℝ)) × UnforcedLeray.Gaussian.Euc 2 => p.1.2.2) :=
      contDiff_snd.comp (contDiff_snd.comp contDiff_fst)
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ × (ℝ × ℝ)) × UnforcedLeray.Gaussian.Euc 2 => p.1.2.1) :=
      contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
    exact hs.prodMk (hz.sub ((ha.mul h0).prodMk (ha.mul h1)))
  rw [contDiff_infty]
  intro n
  have := hP (ℝ × ℝ × (ℝ × ℝ)) ℝ n
    (fun x w => F (x.2.1, x.2.2 - UnforcedLeray.B0224.planeι (x.1 • w))) hK (hG F hF hbd)
  simpa [smul_eq_mul] using this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
