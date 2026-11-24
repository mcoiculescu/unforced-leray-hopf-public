import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLaplace
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.DivTestIsTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestDecay
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneCutoffExists
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.CutoffIBP
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.BoundaryTermTendsto
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.DominatedCutoffLimit
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PsiDecay
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PsiGrad
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdIBP

/-!
# Leaf `PartII-b:T12/1/1/2/32`: the planar pressure identity on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For test fields `F_0, F_1` put `ψ = N * div F`, `ψ_i = Σ_k S_{ik} F_k`.  Then `∂_i ψ = ψ_i`
(`PsiGrad`), `Δψ = div F` (`NewtonConvLaplace`), and `ψ = O(1/|x|)`, `ψ_i = O(|x|⁻²)`.
Integrating `χ_R`-weighted identities and letting `R → ∞` gives `Σ_i ∫ ψ_i² = -∫ ψ div F`;
integration by parts gives `Σ_i ∫ F_i ψ_i = -∫ ψ div F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- Elementary bound: a constant majorant for `C₀ t` when `C₀ ≤ C` and `t ≥ 0`. -/
theorem le_scaled_of_le {a C C' t : ℝ} (ht : 0 ≤ t) (h : a ≤ C * t) (hC : C ≤ C') : a ≤ C' * t :=
  h.trans (mul_le_mul_of_nonneg_right hC ht)

/-- **Leaf `PartII-b:T12/1/1/2/32`.**  The pressure identity on tests:
`Σ_i ∫ F_i ψ_i = Σ_i ∫ ψ_i²` with `ψ_i = Σ_k S_{ik} F_k`. -/
theorem pressureIdentityTest : UnforcedLeray.Short.IIb.PlaneRiesz.PressureIdentityTest := by
  intro F hF
  obtain ⟨χ, hχ⟩ := planeCutoffExists
  unfold IsCutoffFamily at hχ
  set ψ := newtonConv (divTest F) with hψdef
  have hdivT : IsTest (divTest F) := divTestIsTest F hF
  have hψC : ContDiff ℝ ∞ ψ := newtonConvContDiff _ hdivT
  have hΔ : ∀ x, pd 0 (pd 0 ψ) x + pd 1 (pd 1 ψ) x = divTest F x :=
    newtonConvLaplace _ hdivT
  have hgrad : ∀ i, pd i ψ = fun x => ∑ k, rieszTest i k (F k) x := fun i => psiGrad F hF i
  have hpdx : ∀ i x, pd i ψ x = rieszTest i 0 (F 0) x + rieszTest i 1 (F 1) x := by
    intro i x
    rw [hgrad i]
    simp [Fin.sum_univ_two]
  -- `L²` and decay of `∂_i ψ`
  have hL2 : ∀ i, MemLp (pd i ψ) 2 volume := by
    intro i
    rw [hgrad i]
    exact memLp_finsetSum Finset.univ (fun k _ => rieszTestMemLp i k (F k) (hF k))
  have hdec : ∀ i, ∃ C R : ℝ, ∀ x : Pl, R ≤ ‖x‖ → |pd i ψ x| ≤ C * ‖x‖ ^ (-2 : ℝ) := by
    intro i
    obtain ⟨C0, R0, h0⟩ := rieszTestDecay i 0 (F 0) (hF 0)
    obtain ⟨C1, R1, h1⟩ := rieszTestDecay i 1 (F 1) (hF 1)
    refine ⟨|C0| + |C1|, max R0 R1, fun x hx => ?_⟩
    have hx0 : R0 ≤ ‖x‖ := le_trans (le_max_left _ _) hx
    have hx1 : R1 ≤ ‖x‖ := le_trans (le_max_right _ _) hx
    have ht : 0 ≤ ‖x‖ ^ (-2 : ℝ) := Real.rpow_nonneg (norm_nonneg x) _
    rw [hpdx i x]
    have a := h0 x hx0
    have b := h1 x hx1
    have a' : |rieszTest i 0 (F 0) x| ≤ |C0| * ‖x‖ ^ (-2 : ℝ) :=
      le_scaled_of_le ht a (le_abs_self C0)
    have b' : |rieszTest i 1 (F 1) x| ≤ |C1| * ‖x‖ ^ (-2 : ℝ) :=
      le_scaled_of_le ht b (le_abs_self C1)
    calc |rieszTest i 0 (F 0) x + rieszTest i 1 (F 1) x|
        ≤ |rieszTest i 0 (F 0) x| + |rieszTest i 1 (F 1) x| := abs_add_le _ _
      _ ≤ |C0| * ‖x‖ ^ (-2 : ℝ) + |C1| * ‖x‖ ^ (-2 : ℝ) := add_le_add a' b'
      _ = (|C0| + |C1|) * ‖x‖ ^ (-2 : ℝ) := by ring
  -- boundary hypothesis of `BoundaryTermTendsto`
  have hbd : ∃ C R0 : ℝ, ∀ x : Pl, R0 ≤ ‖x‖ →
      |ψ x| ≤ C * ‖x‖⁻¹ ∧ ∀ i, |pd i ψ x| ≤ C * ‖x‖ ^ (-2 : ℝ) := by
    obtain ⟨Cψ, Rψ, hψb⟩ := psiDecay F hF
    obtain ⟨C0, R0, h0⟩ := hdec 0
    obtain ⟨C1, R1, h1⟩ := hdec 1
    refine ⟨|Cψ| + |C0| + |C1|, max Rψ (max R0 R1), fun x hx => ?_⟩
    have hxψ : Rψ ≤ ‖x‖ := le_trans (le_max_left _ _) hx
    have hx0 : R0 ≤ ‖x‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hx1 : R1 ≤ ‖x‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    have ht : 0 ≤ ‖x‖ ^ (-2 : ℝ) := Real.rpow_nonneg (norm_nonneg x) _
    have hi : 0 ≤ ‖x‖⁻¹ := inv_nonneg.2 (norm_nonneg x)
    refine ⟨?_, fun i => ?_⟩
    · exact le_scaled_of_le hi (hψb x hxψ) (by linarith [le_abs_self Cψ, abs_nonneg C0, abs_nonneg C1])
    · fin_cases i
      · exact le_scaled_of_le ht (h0 x hx0) (by linarith [le_abs_self C0, abs_nonneg Cψ, abs_nonneg C1])
      · exact le_scaled_of_le ht (h1 x hx1) (by linarith [le_abs_self C1, abs_nonneg Cψ, abs_nonneg C0])
  -- integrability
  have hgI : ∀ i, Integrable (fun x => (pd i ψ x) ^ 2) volume := fun i => (hL2 i).integrable_sq
  have hψD : Integrable (fun x => ψ x * divTest F x) volume := by
    have hc : Continuous (fun x => ψ x * divTest F x) := hψC.continuous.mul hdivT.1.continuous
    exact hc.integrable_of_hasCompactSupport hdivT.2.mul_left
  -- the cutoff identity for `R ≥ 1`
  have hIBP : ∀ R, 1 ≤ R → ∑ i, ∫ x, χ R x * (pd i ψ x) ^ 2 =
      -(∫ x, χ R x * ψ x * divTest F x) - ∑ i, ∫ x, ψ x * pd i (χ R) x * pd i ψ x := by
    intro R hR
    have h := cutoffIBP ψ (χ R) hψC (hχ.1 R hR)
    simp only [hΔ] at h
    exact h
  -- the limits
  have T1 : Tendsto (fun R => ∑ i, ∫ x, χ R x * (pd i ψ x) ^ 2) atTop
      (𝓝 (∑ i, ∫ x, (pd i ψ x) ^ 2)) :=
    tendsto_finsetSum _ fun i _ => dominatedCutoffLimit χ hχ _ (hgI i)
  have T2 : Tendsto (fun R => ∫ x, χ R x * ψ x * divTest F x) atTop
      (𝓝 (∫ x, ψ x * divTest F x)) := by
    have h := dominatedCutoffLimit χ hχ (fun x => ψ x * divTest F x) hψD
    refine Tendsto.congr (fun R => ?_) h
    simp only [mul_assoc]
  have T3 : ∀ i, Tendsto (fun R => ∫ x, ψ x * pd i (χ R) x * pd i ψ x) atTop (𝓝 0) :=
    fun i => boundaryTermTendsto χ hχ ψ hψC hbd i
  have hev : (fun R => ∑ i, ∫ x, χ R x * (pd i ψ x) ^ 2) =ᶠ[atTop]
      (fun R => -(∫ x, χ R x * ψ x * divTest F x) -
        ∑ i, ∫ x, ψ x * pd i (χ R) x * pd i ψ x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hIBP R hR
  have hRHS : Tendsto (fun R => -(∫ x, χ R x * ψ x * divTest F x) -
      ∑ i, ∫ x, ψ x * pd i (χ R) x * pd i ψ x) atTop
      (𝓝 (-(∫ x, ψ x * divTest F x) - ∑ i : Fin 2, (0 : ℝ))) :=
    (T2.neg).sub (tendsto_finsetSum _ fun i _ => T3 i)
  have hA : ∑ i, ∫ x, (pd i ψ x) ^ 2 = -(∫ x, ψ x * divTest F x) - ∑ i : Fin 2, (0 : ℝ) :=
    tendsto_nhds_unique T1 (Tendsto.congr' hev.symm hRHS)
  -- integration by parts
  have hb : ∑ i, ∫ x, F i x * pd i ψ x = -(∫ x, ψ x * divTest F x) := by
    have hint : ∀ k, Integrable (fun x => pd k (F k) x * ψ x) volume := by
      intro k
      have hk := pdTest k (F k) (hF k)
      exact (hk.1.continuous.mul hψC.continuous).integrable_of_hasCompactSupport
        (hk.2.mul_right)
    have e1 : ∫ x, ψ x * divTest F x = ∑ k, ∫ x, pd k (F k) x * ψ x := by
      have : (fun x => ψ x * divTest F x) = fun x => ∑ k, pd k (F k) x * ψ x := by
        funext x
        simp only [divTest, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [this]
      exact integral_finsetSum _ fun k _ => hint k
    have e2 : ∀ k, ∫ x, pd k (F k) x * ψ x = -∫ x, F k x * pd k ψ x :=
      fun k => pdIBP k ψ (F k) hψC (hF k)
    rw [e1]
    simp only [e2, Finset.sum_neg_distrib, neg_neg]
  -- conclusion
  have hgoal : ∀ i x, ∑ k, rieszTest i k (F k) x = pd i ψ x :=
    fun i x => (congrFun (hgrad i) x).symm
  simp only [hgoal]
  rw [hb, hA, Finset.sum_const_zero, sub_zero]

end UnforcedLeray.Short.IIb.PlaneRiesz
