import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.Transfer
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.Integ
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.LapCalc

/-!
# Part II-a, task `PartII-a:F03/3`: `windowBackEquation` (the Laplacian of `w` on the window)

Proves `WindowBackEquation` of `Short/PartII-a/Sub/F03.lean` (source of record
`the November 2 reference manuscript`, lines 1431-1441; old manuscript
`paper/main.tex` lines 7510-7517). Helpers: `Tasks/F03cWindowBackEquation/Transfer.lean` (change of
variables of `∫ u · sLap φ` and `∫ D · φ` through `expChart`, `dilChart`), `Integ.lean`
(integrability), `LapCalc.lean` (`lapT` of vector and complex tests).

Route: for a real smooth compactly supported test `a` with support in the window, the weak
second derivatives of `u_c = windowField χ τ₀ W c` tested against `lapTest τ₀ a` give the identity
`∫ W_c ν sLap a = ∫ Λ_c a` (`real_identity`). Real and imaginary parts of a complex component give
the complex identity (`component_identity`); summing over components gives the vector statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.WinBack

open UnforcedLeray.PhaseSpace UnforcedLeray.Parabolic UnforcedLeray.B0424
  UnforcedLeray.Short.PartIIa.Rep

variable {P : ℝ} [Fact (0 < P)]

/-! ### Elementary chart values -/

theorem lapTest_expChart (τ₀ : ℝ) (a : PS 3 → ℝ) (t : ℝ) (y : Space) :
    lapTest τ₀ a (Real.exp t, y) = Real.exp (-t) * a (τ₀ + t, Real.exp (-(t / 2)) • y) := by
  simp only [lapTest, Real.exp_pos, ite_true, Real.log_exp, neg_div]

/-- The pointwise form of the transport back on the window: where `a ≠ 0` the window indicator
of `windowLap` is `1`. -/
theorem windowLap_shift_eq {ν τ₀ : ℝ} {D : Fin 3 → PS 3 → ℂ} {a : PS 3 → ℝ}
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (c : Fin 3)
    (p : ℝ × Space) :
    windowLap ν τ₀ D (τ₀ + p.1, p.2) c * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ) =
      (ν : ℂ) * (Real.exp (3 * p.1 / 2) •
        (D c (Real.exp p.1, Real.exp (p.1 / 2) • p.2) * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ))) := by
  by_cases ha0 : a (τ₀ + p.1, p.2) = 0
  · simp [ha0]
  · have hmem : (τ₀ + p.1, p.2) ∈ tsupport a := subset_tsupport _ (Function.mem_support.2 ha0)
    have hw : τ₀ + p.1 ∈ Ioo (τ₀ - 1) (τ₀ + 1) := (hsup hmem).1
    have hlt : |p.1| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hw.1, hw.2]
    simp [windowLap, hlt, Complex.real_smul]
    ring

/-! ### The real-test identity -/

theorem integrable_windowField_mul {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    (c : Fin 3) {g : PS 3 → ℝ} (hg : IsSTTest g) :
    Integrable (fun X => windowField χ τ₀ W c X * ((g X : ℝ) : ℂ)) :=
  integrable_of_memLp_mul (windowField_memLp hrt hW hχ τ₀ c)
    (Complex.continuous_ofReal.comp hg.continuous) (hg.2.comp_left Complex.ofReal_zero)

theorem real_identity {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ ν : ℝ)
    (c : Fin 3) (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ)
    (hD2 : ∀ i, MemLp (D2 c i i) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (windowField χ τ₀ W c) i i (D2 c i i))
    {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    ∫ p : ℝ × Space, W p c * ((ν * sLap a p : ℝ) : ℂ) =
      ∫ p : ℝ × Space, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ((a p : ℝ) : ℂ) := by
  have hφ : IsSTTest (lapTest τ₀ a : PS 3 → ℝ) := isSTTest_lapTest ha hsup
  have hI1 : ∀ i, Integrable (fun X => windowField χ τ₀ W c X *
      ((sD2 i i (lapTest τ₀ a) X : ℝ) : ℂ)) := fun i =>
    integrable_windowField_mul hrt hW hχ τ₀ c ((hφ.dirD (sdir i)).dirD (sdir i))
  have hI2 : ∀ i, Integrable (fun X => D2 c i i X * ((lapTest τ₀ a X : ℝ) : ℂ)) := fun i =>
    integrable_of_memLp_mul (hD2 i).1 (Complex.continuous_ofReal.comp hφ.continuous)
      (hφ.2.comp_left Complex.ofReal_zero)
  have hsum : ∫ X, windowField χ τ₀ W c X * ((sLap (lapTest τ₀ a) X : ℝ) : ℂ) =
      ∫ X, (∑ i, D2 c i i X) * ((lapTest τ₀ a X : ℝ) : ℂ) := by
    have e1 : ∀ X, windowField χ τ₀ W c X * ((sLap (lapTest τ₀ a) X : ℝ) : ℂ) =
        ∑ i, windowField χ τ₀ W c X * ((sD2 i i (lapTest τ₀ a) X : ℝ) : ℂ) := by
      intro X
      simp only [sLap, Complex.ofReal_sum, Finset.mul_sum]
    have e2 : ∀ X, (∑ i, D2 c i i X) * ((lapTest τ₀ a X : ℝ) : ℂ) =
        ∑ i, D2 c i i X * ((lapTest τ₀ a X : ℝ) : ℂ) := by
      intro X
      simp only [Finset.sum_mul]
    simp_rw [e1, e2]
    rw [integral_finset_sum _ fun i _ => hI1 i, integral_finset_sum _ fun i _ => hI2 i]
    exact Finset.sum_congr rfl fun i _ => (hD2 i).2 _ hφ
  have hL : ∫ X, windowField χ τ₀ W c X * ((sLap (lapTest τ₀ a) X : ℝ) : ℂ) =
      ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sLap a (τ₀ + p.1, p.2) : ℝ) : ℂ) :=
    integral_windowField_sLap_t χ hχ τ₀ W c ha hsup
  have hR : ∫ X, (∑ i, D2 c i i X) * ((lapTest τ₀ a X : ℝ) : ℂ) =
      ∫ p : ℝ × Space, Real.exp (3 * p.1 / 2) •
        ((∑ i, D2 c i i (Real.exp p.1, Real.exp (p.1 / 2) • p.2)) *
          ((a (τ₀ + p.1, p.2) : ℝ) : ℂ)) :=
    integral_D_lapTest_t τ₀ (fun X => ∑ i, D2 c i i X) ha hsup
  have hkey : ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sLap a (τ₀ + p.1, p.2) : ℝ) : ℂ) =
      ∫ p : ℝ × Space, Real.exp (3 * p.1 / 2) •
        ((∑ i, D2 c i i (Real.exp p.1, Real.exp (p.1 / 2) • p.2)) *
          ((a (τ₀ + p.1, p.2) : ℝ) : ℂ)) :=
    hL.symm.trans (hsum.trans hR)
  have hshift1 : ∫ p : ℝ × Space, W p c * ((ν * sLap a p : ℝ) : ℂ) =
      (ν : ℂ) * ∫ p : ℝ × Space, W p c * ((sLap a p : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hshift2 : ∫ p : ℝ × Space, W p c * ((sLap a p : ℝ) : ℂ) =
      ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sLap a (τ₀ + p.1, p.2) : ℝ) : ℂ) :=
    (integral_shift τ₀ (fun p => W p c * ((sLap a p : ℝ) : ℂ))).symm
  have hshift3 : ∫ p : ℝ × Space, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c *
      ((a p : ℝ) : ℂ) = ∫ p : ℝ × Space, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X)
        (τ₀ + p.1, p.2) c * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ) :=
    (integral_shift τ₀ (fun p => windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c *
      ((a p : ℝ) : ℂ))).symm
  have hpt : ∀ p : ℝ × Space, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) (τ₀ + p.1, p.2) c *
      ((a (τ₀ + p.1, p.2) : ℝ) : ℂ) = (ν : ℂ) * (Real.exp (3 * p.1 / 2) •
        ((∑ i, D2 c i i (Real.exp p.1, Real.exp (p.1 / 2) • p.2)) *
          ((a (τ₀ + p.1, p.2) : ℝ) : ℂ))) :=
    fun p => windowLap_shift_eq hsup c p
  rw [hshift1, hshift2, hkey, hshift3, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_const_mul]

/-! ### Integrability of the transported side for real tests -/

theorem integrable_lambda_real {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) (τ₀ ν : ℝ) (c : Fin 3)
    (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ) (hmem : ∀ i, MemLp (D2 c i i) r volume)
    {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    Integrable (fun p : ℝ × Space => windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c *
      ((a p : ℝ) : ℂ)) := by
  have hMem : MemLp (fun X => ∑ i, D2 c i i X) r volume :=
    memLp_finsetSum Finset.univ fun i _ => hmem i
  have hφ : IsSTTest (lapTest τ₀ a : PS 3 → ℝ) := isSTTest_lapTest ha hsup
  have hf : Integrable (fun X => (∑ i, D2 c i i X) * ((lapTest τ₀ a X : ℝ) : ℂ)) :=
    integrable_of_memLp_mul hMem (Complex.continuous_ofReal.comp hφ.continuous)
      (hφ.2.comp_left Complex.ofReal_zero)
  have hk2 := (integrable_expChart_iff _).1 hf.integrableOn
  have hk2' : Integrable (fun p : ℝ × Space => (∑ i, D2 c i i (Real.exp p.1, p.2)) *
      ((a (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ)) := by
    refine hk2.congr (Filter.Eventually.of_forall fun p => ?_)
    have he : ((Real.exp p.1 : ℝ) : ℂ) * ((Real.exp (-p.1) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    simp only [expChart, lapTest_expChart, Complex.real_smul, Complex.ofReal_mul]
    linear_combination ((∑ i, D2 c i i (Real.exp p.1, p.2)) *
      ((a (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ)) * he
  have hk3 := (integrable_dilChart_iff _).1 hk2'
  have hk4 : Integrable (fun p : ℝ × Space => Real.exp (3 * p.1 / 2) •
      ((∑ i, D2 c i i (Real.exp p.1, Real.exp (p.1 / 2) • p.2)) *
        ((a (τ₀ + p.1, p.2) : ℝ) : ℂ))) := by
    refine hk3.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [dilChart, expNeg_smul_expPos]
  have hk5 := (hk4.const_mul (ν : ℂ)).congr
    (Filter.Eventually.of_forall fun p =>
      (windowLap_shift_eq (D := fun c X => ∑ i, D2 c i i X) hsup c p).symm)
  exact (integrable_shift_iff τ₀ (fun p : ℝ × Space => windowLap ν τ₀
    (fun c X => ∑ i, D2 c i i X) p c * ((a p : ℝ) : ℂ))).1 hk5

/-! ### Components and the complex test -/

theorem sLap_zero_off_window {τ₀ : ℝ} {g : PS 3 → ℝ}
    (hg : tsupport g ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (q : ℝ × Space)
    (hq : q ∉ Icc (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) : sLap g q = 0 := by
  by_contra hne
  have hm := hg (sLap_ne_mem_tsupport hne)
  exact hq ⟨Ioo_subset_Icc_self hm.1, hm.2⟩

theorem integrable_W_mul_real {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ : ℝ) (c : Fin 3) {g : ℝ × Space → ℝ}
    (hg : IsSTTest g) (hz : ∀ q, q ∉ Icc (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) → g q = 0) :
    Integrable (fun p => W p c * ((g p : ℝ) : ℂ)) := by
  have key := integrable_of_memLp_mul (slab_memLp hrt hW τ₀ (τ₀ - 1) (τ₀ + 1) c)
    (Complex.continuous_ofReal.comp hg.continuous) (hg.2.comp_left Complex.ofReal_zero)
  refine key.congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ Icc (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)
  · dsimp only [Function.comp_apply]
    rw [Set.indicator_of_mem hp]
  · dsimp only [Function.comp_apply]
    rw [Set.indicator_of_notMem hp, hz p hp]
    simp

theorem component_identity {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ ν : ℝ)
    (c : Fin 3) (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ)
    (hD2 : ∀ i, MemLp (D2 c i i) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (windowField χ τ₀ W c) i i (D2 c i i))
    {ψc : ℝ × Space → ℂ} (hψc : ContDiff ℝ ∞ ψc) (hψcs : HasCompactSupport ψc)
    (hψw : tsupport ψc ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    Integrable (fun p => W p c * (ν * lapT ψc p)) ∧
      Integrable (fun p => windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p) ∧
      ∫ p, W p c * (ν * lapT ψc p) =
        ∫ p, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p := by
  have hre : ContDiff ℝ ∞ (fun q => (ψc q).re) := Complex.reCLM.contDiff.comp hψc
  have him : ContDiff ℝ ∞ (fun q => (ψc q).im) := Complex.imCLM.contDiff.comp hψc
  have hcsa : HasCompactSupport (fun q => (ψc q).re) := hψcs.comp_left Complex.zero_re
  have hcsb : HasCompactSupport (fun q => (ψc q).im) := hψcs.comp_left Complex.zero_im
  have hsa : tsupport (fun q => (ψc q).re : PS 3 → ℝ) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    (tsupport_comp_subset Complex.zero_re ψc).trans hψw
  have hsb : tsupport (fun q => (ψc q).im : PS 3 → ℝ) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    (tsupport_comp_subset Complex.zero_im ψc).trans hψw
  have ha : IsSTTest (fun q => (ψc q).re : PS 3 → ℝ) := ⟨hre, hcsa⟩
  have hb : IsSTTest (fun q => (ψc q).im : PS 3 → ℝ) := ⟨him, hcsb⟩
  have hIA := real_identity hrt hW hχ τ₀ ν c D2 hD2 ha hsa
  have hIB := real_identity hrt hW hχ τ₀ ν c D2 hD2 hb hsb
  have hJA := integrable_lambda_real hrt τ₀ ν c D2 (fun i => (hD2 i).1) ha hsa
  have hJB := integrable_lambda_real hrt τ₀ ν c D2 (fun i => (hD2 i).1) hb hsb
  have hWA : Integrable (fun p => W p c * ((ν * sLap (fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    have h1 := integrable_W_mul_real hrt hW τ₀ c (UnforcedLeray.Parabolic.isSTTest_sLap ha)
      (fun q hq => sLap_zero_off_window hsa q hq)
    refine (h1.const_mul (ν : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hWB : Integrable (fun p => W p c * ((ν * sLap (fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    have h1 := integrable_W_mul_real hrt hW τ₀ c (UnforcedLeray.Parabolic.isSTTest_sLap hb)
      (fun q hq => sLap_zero_off_window hsb q hq)
    refine (h1.const_mul (ν : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hlapc : ∀ p, lapT ψc p = ((sLap (fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ) +
      ((sLap (fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ) * Complex.I :=
    fun p => lapT_complex hψc p
  have hLHS : ∀ p, W p c * (ν * lapT ψc p) =
      W p c * ((ν * sLap (fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ) +
        Complex.I * (W p c * ((ν * sLap (fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    intro p
    rw [hlapc p]
    push_cast
    ring
  have hdec : ∀ p, ψc p = ((ψc p).re : ℂ) + ((ψc p).im : ℂ) * Complex.I :=
    fun p => (Complex.re_add_im (ψc p)).symm
  have hRHS : ∀ p, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p =
      windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * (((fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ) +
        Complex.I * (windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c *
          (((fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    intro p
    conv_lhs => rw [hdec p]
    simp only []
    ring
  have hiLHS : Integrable (fun p => W p c * (ν * lapT ψc p)) :=
    (hWA.add (hWB.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun p => (hLHS p).symm)
  have hiRHS : Integrable (fun p => windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p) :=
    (hJA.add (hJB.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun p => (hRHS p).symm)
  refine ⟨hiLHS, hiRHS, ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hLHS),
    integral_congr_ae (Filter.Eventually.of_forall hRHS),
    integral_add hWA (hWB.const_mul Complex.I), integral_add hJA (hJB.const_mul Complex.I),
    integral_const_mul, integral_const_mul, hIA, hIB]

/-! ### The vector statement -/

theorem dotL_lap_eq {ν : ℝ} {W : ℝ × Space → CVec3} {ψ : ℝ × Space → CVec3}
    (hψ : ContDiff ℝ ∞ ψ) (p : ℝ × Space) :
    dotL (W p) (ν • lapT ψ p) = ∑ c : Fin 3, W p c * (ν * lapT (fun q => ψ q c) p) := by
  rw [dotL_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lapT_apply_comp hψ c p]
  simp only [PiLp.smul_apply, Complex.real_smul]

/-- **`PartII-a:F03/3`.** The field `windowLap` built from `Σ_i D2 c i i` is a weak Laplacian of
`w` on the window (`IsWindowLaplacian`). -/
theorem windowBackEquation : WindowBackEquation := by
  intro r _ hrt P _ ν w W hW χ hχ τ₀ D2 hD2
  unfold IsWindowLaplacian
  intro ψ hψ hψc hψw
  have hD2' : ∀ c i, MemLp (D2 c i i) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (windowField χ τ₀ W c) i i (D2 c i i) := by
    intro c i
    refine ⟨?_, (hD2 c i i).2⟩
    have h := (hD2 c i i).1
    rwa [ENNReal.ofReal_toReal hrt] at h
  have hψcomp : ∀ c : Fin 3, ContDiff ℝ ∞ (fun q => ψ q c) := fun c =>
    ((EuclideanSpace.proj c : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hψ
  have hcs : ∀ c : Fin 3, HasCompactSupport (fun q => ψ q c) := fun c =>
    hψc.comp_left (g := fun v : CVec3 => v c) (by simp)
  have hsup : ∀ c : Fin 3, tsupport (fun q => ψ q c) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) := fun c =>
    (tsupport_comp_subset (g := fun v : CVec3 => v c) (by simp) ψ).trans hψw
  have hcomp : ∀ c : Fin 3,
      Integrable (fun p => W p c * (ν * lapT (fun q => ψ q c) p)) ∧
      Integrable (fun p => windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψ p c) ∧
      ∫ p, W p c * (ν * lapT (fun q => ψ q c) p) =
        ∫ p, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψ p c := fun c =>
    component_identity hrt hW hχ τ₀ ν c D2 (hD2' c) (hψcomp c) (hcs c) (hsup c)
  have e1 : (fun p => dotL (W p) (ν • lapT ψ p)) =
      fun p => ∑ c : Fin 3, W p c * (ν * lapT (fun q => ψ q c) p) :=
    funext fun p => dotL_lap_eq hψ p
  have e2 : (fun p => dotL (windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p) (ψ p)) =
      fun p => ∑ c : Fin 3, windowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψ p c :=
    funext fun p => dotL_apply _ _
  rw [e1, e2]
  refine ⟨integrable_finsetSum _ fun c _ => (hcomp c).1,
    integrable_finsetSum _ fun c _ => (hcomp c).2.1, ?_⟩
  rw [integral_finsetSum _ fun c _ => (hcomp c).1, integral_finsetSum _ fun c _ => (hcomp c).2.1]
  exact Finset.sum_congr rfl fun c _ => (hcomp c).2.2

end UnforcedLeray.Short.PartIIa.WinBack

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F03/3`** (the target of this task): see `WinBack.windowBackEquation`. -/
theorem windowBackEquation : WindowBackEquation := WinBack.windowBackEquation

end UnforcedLeray.Short.PartIIa
