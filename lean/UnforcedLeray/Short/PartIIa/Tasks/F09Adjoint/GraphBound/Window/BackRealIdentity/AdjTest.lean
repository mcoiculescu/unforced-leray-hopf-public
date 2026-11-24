import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_3
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.AdjChart
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Norms
import UnforcedLeray.Lib.Parabolic.Adjoint

/-!
# Helper for `PartII-a:F09/3/1/3/2` and `/3`: the transported test of the reversed chart

Source `the November 2 reference manuscript`
lines 1431-1441 reversed (`θ = 1 - e^{-t}`, `x = e^{-t/2} y`).

For a real test `a` supported in the window `(τ₀-1, τ₀+1)` the test
`φ(θ, x) = (1-θ)^{-3/2} a(τ₀ + log(1-θ), (1-θ)^{-1/2} x)` (`adjLapTest`) satisfies, at
`(θ, x) = (1 - e^{-t}, e^{-t/2} y)`,
`φ = e^{3t/2} a(τ₀ - t, y)` and `Δ_x φ = e^{5t/2} (Δa)(τ₀ - t, y)`
(the weights `e^{-5t/2}` of the chart cancel exactly).  It is built as the reflection `θ ↦ 1 - θ`
of `lapTest τ₀ ã`, `ã = e^{(τ₀ - s)/2} a`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic UnforcedLeray.B0424
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.Short.PartIIa.WinBack
open UnforcedLeray.Gaussian (Euc)

/-! ### The time weight -/

/-- `ã(s, y) = e^{(τ₀ - s)/2} a(s, y)`. -/
def adjTilde (τ₀ : ℝ) (a : PS 3 → ℝ) (q : PS 3) : ℝ := Real.exp ((τ₀ - q.1) / 2) * a q

theorem contDiff_adjW (τ₀ : ℝ) :
    ContDiff ℝ ∞ (fun q : PS 3 => Real.exp ((τ₀ - q.1) / 2)) :=
  Real.contDiff_exp.comp ((contDiff_const.sub contDiff_fst).div_const 2)

theorem isSTTest_adjTilde {τ₀ : ℝ} {a : PS 3 → ℝ} (ha : IsSTTest a) :
    IsSTTest (adjTilde τ₀ a) :=
  ⟨(contDiff_adjW τ₀).mul ha.1, ha.2.mul_left⟩

theorem tsupport_adjTilde_subset {τ₀ : ℝ} {a : PS 3 → ℝ} :
    tsupport (adjTilde τ₀ a) ⊆ tsupport a :=
  tsupport_mul_subset_right (f := fun q : PS 3 => Real.exp ((τ₀ - q.1) / 2)) (g := a)

theorem sD_timeMul (h : ℝ → ℝ) (hh : Differentiable ℝ h) {g : PS 3 → ℝ}
    (hg : Differentiable ℝ g) (i : Fin 3) :
    sD i (fun X : PS 3 => h X.1 * g X) = fun X => h X.1 * sD i g X := by
  funext X
  simp only [sD, dirD]
  have h1 := (hh X.1).hasFDerivAt.comp X (hasFDerivAt_fst (p := X))
  have h2 := (h1.mul (hg X).hasFDerivAt).fderiv
  rw [show (fun X : PS 3 => h X.1 * g X) = (h ∘ Prod.fst) * g from rfl, h2]
  simp

theorem sLap_adjTilde {τ₀ : ℝ} {a : PS 3 → ℝ} (ha : IsSTTest a) (X : PS 3) :
    sLap (adjTilde τ₀ a) X = Real.exp ((τ₀ - X.1) / 2) * sLap a X := by
  have hw0 : ContDiff ℝ ∞ (fun s : ℝ => Real.exp ((τ₀ - s) / 2)) :=
    Real.contDiff_exp.comp ((contDiff_const.sub contDiff_id).div_const 2)
  have hw : Differentiable ℝ (fun s : ℝ => Real.exp ((τ₀ - s) / 2)) := hw0.differentiable (by simp)
  have e1 : ∀ i : Fin 3, sD i (adjTilde τ₀ a) = fun X => Real.exp ((τ₀ - X.1) / 2) * sD i a X :=
    fun i => sD_timeMul (fun s => Real.exp ((τ₀ - s) / 2)) hw ha.differentiable i
  have e2 : ∀ i : Fin 3, sD2 i i (adjTilde τ₀ a) X = Real.exp ((τ₀ - X.1) / 2) * sD2 i i a X := by
    intro i
    show sD i (sD i (adjTilde τ₀ a)) X = _
    rw [e1 i, sD_timeMul (fun s => Real.exp ((τ₀ - s) / 2)) hw (ha.dirD (sdir i)).differentiable i]
  simp only [sLap, e2, Finset.mul_sum]

/-! ### The reflection `θ ↦ 1 - θ` -/

/-- `X ↦ (1 - X.1, X.2)` as an affine map. -/
def adjRefl : PS 3 → PS 3 := fun X => trevCLM 3 X + ((1 : ℝ), (0 : Euc 3))

theorem adjRefl_apply (X : PS 3) : adjRefl X = (1 - X.1, X.2) :=
  Prod.ext (by simp [adjRefl, trevCLM]; ring) (by simp [adjRefl, trevCLM])

theorem hasFDerivAt_adjRefl (X : PS 3) : HasFDerivAt adjRefl (trevCLM 3) X := by
  have h : HasFDerivAt (fun x : PS 3 => trevCLM 3 x + ((1 : ℝ), (0 : Euc 3))) (trevCLM 3) X :=
    (trevCLM 3).hasFDerivAt.add_const ((1 : ℝ), (0 : Euc 3))
  exact h

theorem continuous_adjRefl : Continuous adjRefl := by
  have h : Continuous (fun x : PS 3 => trevCLM 3 x + ((1 : ℝ), (0 : Euc 3))) :=
    (trevCLM 3).continuous.add continuous_const
  exact h

theorem contDiff_adjRefl : ContDiff ℝ ∞ adjRefl := by
  have h : ContDiff ℝ ∞ (fun x : PS 3 => trevCLM 3 x + ((1 : ℝ), (0 : Euc 3))) :=
    (trevCLM 3).contDiff.add contDiff_const
  exact h

/-- The reflection as a homeomorphism. -/
def adjReflHomeo : PS 3 ≃ₜ PS 3 where
  toFun := adjRefl
  invFun := adjRefl
  left_inv X := by simp [adjRefl_apply]
  right_inv X := by simp [adjRefl_apply]
  continuous_toFun := continuous_adjRefl
  continuous_invFun := continuous_adjRefl

theorem isSTTest_comp_adjRefl {g : PS 3 → ℝ} (hg : IsSTTest g) : IsSTTest (g ∘ adjRefl) :=
  ⟨hg.1.comp contDiff_adjRefl, hg.2.comp_homeomorph adjReflHomeo⟩

theorem sD_comp_adjRefl {g : PS 3 → ℝ} (hg : Differentiable ℝ g) (i : Fin 3) :
    sD i (g ∘ adjRefl) = (sD i g) ∘ adjRefl := by
  funext X
  simp only [sD, dirD, Function.comp_apply]
  have h : HasFDerivAt (g ∘ adjRefl) ((fderiv ℝ g (adjRefl X)).comp (trevCLM 3)) X :=
    (hg (adjRefl X)).hasFDerivAt.comp X (hasFDerivAt_adjRefl X)
  rw [h.fderiv]
  simp [trevCLM]

theorem sLap_comp_adjRefl {g : PS 3 → ℝ} (hg : IsSTTest g) (X : PS 3) :
    sLap (g ∘ adjRefl) X = sLap g (adjRefl X) := by
  have e : ∀ i : Fin 3, sD2 i i (g ∘ adjRefl) X = sD2 i i g (adjRefl X) := by
    intro i
    show sD i (sD i (g ∘ adjRefl)) X = _
    rw [sD_comp_adjRefl hg.differentiable i, sD_comp_adjRefl (hg.dirD (sdir i)).differentiable i]
    rfl
  simp only [sLap, e]

/-! ### The transported test -/

/-- `φ(θ,x) = (1-θ)^{-3/2} a(τ₀ + log(1-θ), (1-θ)^{-1/2} x)` for `θ < 1`, `0` otherwise. -/
def adjLapTest (τ₀ : ℝ) (a : PS 3 → ℝ) (X : PS 3) : ℝ :=
  lapTest τ₀ (adjTilde τ₀ a) (1 - X.1, X.2)

theorem adjLapTest_eq (τ₀ : ℝ) (a : PS 3 → ℝ) :
    adjLapTest τ₀ a = lapTest τ₀ (adjTilde τ₀ a) ∘ adjRefl := by
  funext X
  simp [adjLapTest, adjRefl_apply]

theorem tsupport_adjTilde_window {τ₀ : ℝ} {a : PS 3 → ℝ}
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    tsupport (adjTilde τ₀ a) ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
  tsupport_adjTilde_subset.trans hsup

theorem isSTTest_adjLapTest {τ₀ : ℝ} {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    IsSTTest (adjLapTest τ₀ a) := by
  rw [adjLapTest_eq]
  exact isSTTest_comp_adjRefl
    (isSTTest_lapTest (isSTTest_adjTilde ha) (tsupport_adjTilde_window hsup))

theorem adjLapTest_eq_zero (τ₀ : ℝ) (a : PS 3 → ℝ) {X : PS 3} (hX : 1 ≤ X.1) :
    adjLapTest τ₀ a X = 0 := by
  have : ¬ (0 < 1 - X.1) := by linarith
  simp [adjLapTest, lapTest, this]

theorem adjLapTest_chart (τ₀ : ℝ) (a : PS 3 → ℝ) (p : ℝ × Space) :
    adjLapTest τ₀ a (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) =
      Real.exp (3 * p.1 / 2) * a (τ₀ + -p.1, p.2) := by
  have h1 : (1 : ℝ) - (1 - Real.exp (-p.1)) = Real.exp (-p.1) := sub_sub_cancel _ _
  have h2 : Real.exp (-(-p.1) / 2) • (Real.exp (-(p.1 / 2)) • p.2) = p.2 := by
    rw [smul_smul, ← Real.exp_add]
    have : -(-p.1) / 2 + -(p.1 / 2) = 0 := by ring
    rw [this]; simp
  simp only [adjLapTest, lapTest, h1, Real.exp_pos, ite_true, Real.log_exp, adjTilde, h2]
  rw [← mul_assoc, ← Real.exp_add]
  have : -(-p.1) + (τ₀ - (τ₀ + -p.1)) / 2 = 3 * p.1 / 2 := by ring
  rw [this]

theorem sLap_adjLapTest_chart {τ₀ : ℝ} {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (p : ℝ × Space) :
    sLap (adjLapTest τ₀ a) (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) =
      Real.exp (5 * p.1 / 2) * sLap a (τ₀ + -p.1, p.2) := by
  have hl : IsSTTest (lapTest τ₀ (adjTilde τ₀ a) : PS 3 → ℝ) :=
    isSTTest_lapTest (isSTTest_adjTilde ha) (tsupport_adjTilde_window hsup)
  rw [adjLapTest_eq, sLap_comp_adjRefl hl, adjRefl_apply]
  have h1 : (1 : ℝ) - (1 - Real.exp (-p.1)) = Real.exp (-p.1) := sub_sub_cancel _ _
  have h2 : Real.exp (-(-p.1) / 2) • (Real.exp (-(p.1 / 2)) • p.2) = p.2 := by
    rw [smul_smul, ← Real.exp_add]
    have : -(-p.1) / 2 + -(p.1 / 2) = 0 := by ring
    rw [this]; simp
  simp only [h1]
  rw [sLap_lapTest (isSTTest_adjTilde ha) (tsupport_adjTilde_window hsup)]
  simp only [Real.exp_pos, ite_true, Real.log_exp]
  rw [h2, sLap_adjTilde ha]
  have e : Real.exp (-(-p.1)) * Real.exp (-(-p.1) / 2) ^ 2 *
      (Real.exp ((τ₀ - (τ₀ + -p.1)) / 2) * sLap a (τ₀ + -p.1, p.2)) =
      Real.exp (5 * p.1 / 2) * sLap a (τ₀ + -p.1, p.2) := by
    have e4 : Real.exp (-(-p.1)) * Real.exp (-(-p.1) / 2) * Real.exp (-(-p.1) / 2) *
        Real.exp ((τ₀ - (τ₀ + -p.1)) / 2) = Real.exp (5 * p.1 / 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    rw [sq]
    linear_combination (sLap a (τ₀ + -p.1, p.2)) * e4
  exact e

/-! ### Membership of the transported field -/

theorem adjWindowField_memLp {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤)
    {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ)
    (τ₀ : ℝ) (c : Fin 3) : MemLp (adjWindowField χ τ₀ W c) r volume := by
  have hr0 : 0 < r.toReal := rpow_pos_of_one_le hrt
  obtain ⟨M, hM⟩ := hχ.smooth.continuous.bounded_above_of_compact_support hχ.compact
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h := wn_memLp hr0 (rn_measurable_adjWindowField hχ τ₀ hW.meas.measurable c).aestronglyMeasurable
    (rn_field_lt_top hM0 hM hχ hrt hr0 τ₀ hW c)
  rwa [ENNReal.ofReal_toReal hrt] at h

/-! ### Integrals through the chart -/

theorem integral_adjField_sLap {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    (W : ℝ × Space → CVec3) (c : Fin 3) {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    ∫ X, adjWindowField χ τ₀ W c X * ((sLap (adjLapTest τ₀ a) X : ℝ) : ℂ) =
      ∫ p : ℝ × Space, W p c * ((sLap a p : ℝ) : ℂ) := by
  have hG : ∀ X : PS 3, 1 ≤ X.1 →
      adjWindowField χ τ₀ W c X * ((sLap (adjLapTest τ₀ a) X : ℝ) : ℂ) = 0 := by
    intro X hX
    simp [adjWindowField, not_lt.2 hX]
  rw [integral_adjChart _ hG]
  have hpt : ∀ p : ℝ × Space, Real.exp (-(5 * p.1 / 2)) •
      (adjWindowField χ τ₀ W c (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) *
        ((sLap (adjLapTest τ₀ a) (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ)) =
      W (τ₀ + -p.1, p.2) c * ((sLap a (τ₀ + -p.1, p.2) : ℝ) : ℂ) := by
    intro p
    have hu := rev_windowField_chart χ τ₀ W c p
    simp only [revChart] at hu
    rw [hu, sLap_adjLapTest_chart ha hsup p, ← sub_eq_add_neg]
    by_cases h0 : sLap a (τ₀ - p.1, p.2) = 0
    · simp [h0]
    · have ht : |-p.1| < 1 := abs_lt_of_sLap_ne hsup (t := -p.1) (y := p.2)
        (by rwa [← sub_eq_add_neg])
      have hp : |p.1| < 1 := by rwa [abs_neg] at ht
      have hχ1 : χ p.1 = 1 := hχ.one p.1 ⟨(abs_lt.1 hp).1.le, (abs_lt.1 hp).2.le⟩
      have hc : ((Real.exp (-(5 * p.1 / 2)) * Real.exp (5 * p.1 / 2) : ℝ) : ℂ) = 1 := by
        rw [← Real.exp_add]; simp
      rw [hχ1]
      simp only [Complex.real_smul]
      push_cast at hc ⊢
      linear_combination (W (τ₀ - p.1, p.2) c * (sLap a (τ₀ - p.1, p.2) : ℂ)) * hc
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have h := adjcNeg_mp.integral_comp'
    (fun q : ℝ × Space => W (τ₀ + q.1, q.2) c * ((sLap a (τ₀ + q.1, q.2) : ℝ) : ℂ))
  exact h.trans (integral_shift τ₀ (fun p => W p c * ((sLap a p : ℝ) : ℂ)))

/-- Pointwise transport back through the chart. -/
theorem adjWindowLap_chart_eq {ν τ₀ : ℝ} {D : Fin 3 → PS 3 → ℂ} {a : PS 3 → ℝ}
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (c : Fin 3)
    (p : ℝ × Space) :
    adjWindowLap ν τ₀ D (τ₀ + -p.1, p.2) c * ((a (τ₀ + -p.1, p.2) : ℝ) : ℂ) =
      (ν : ℂ) * (Real.exp (-(5 * p.1 / 2)) •
        (D c (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) *
          ((adjLapTest τ₀ a (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ))) := by
  rw [adjLapTest_chart]
  by_cases ha0 : a (τ₀ + -p.1, p.2) = 0
  · simp [ha0]
  · have hmem : (τ₀ + -p.1, p.2) ∈ tsupport a := subset_tsupport _ (Function.mem_support.2 ha0)
    have hw : τ₀ + -p.1 ∈ Ioo (τ₀ - 1) (τ₀ + 1) := (hsup hmem).1
    have hlt : |τ₀ + -p.1 - τ₀| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hw.1, hw.2]
    have e1 : τ₀ - (τ₀ + -p.1) = p.1 := by ring
    have e2 : -p.1 / 2 = -(p.1 / 2) := by ring
    have hc : ((Real.exp (-(5 * p.1 / 2)) * Real.exp (3 * p.1 / 2) : ℝ) : ℂ) =
        ((Real.exp (-p.1) : ℝ) : ℂ) := by
      rw [← Real.exp_add]
      congr 2
      ring
    simp only [adjWindowLap, hlt, ite_true, e1, neg_neg, e2, Complex.real_smul]
    push_cast at hc ⊢
    linear_combination (ν : ℂ) * (D c (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) *
      (a (τ₀ + -p.1, p.2) : ℂ)) * (-hc)

theorem integral_adjWindowLap_eq (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ) (c : Fin 3) {a : PS 3 → ℝ}
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    ∫ p : ℝ × Space, adjWindowLap ν τ₀ D p c * ((a p : ℝ) : ℂ) =
      (ν : ℂ) * ∫ X, D c X * ((adjLapTest τ₀ a X : ℝ) : ℂ) := by
  have hG : ∀ X : PS 3, 1 ≤ X.1 → D c X * ((adjLapTest τ₀ a X : ℝ) : ℂ) = 0 := by
    intro X hX
    simp [adjLapTest_eq_zero τ₀ a hX]
  rw [integral_adjChart _ hG, ← integral_const_mul]
  rw [← integral_shift τ₀ (fun p => adjWindowLap ν τ₀ D p c * ((a p : ℝ) : ℂ))]
  have h := adjcNeg_mp.integral_comp'
    (fun q : ℝ × Space => adjWindowLap ν τ₀ D (τ₀ + q.1, q.2) c *
      ((a (τ₀ + q.1, q.2) : ℝ) : ℂ))
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => adjWindowLap_chart_eq hsup c p)

end UnforcedLeray.Short.PartIIa
