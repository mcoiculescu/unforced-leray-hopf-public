import UnforcedLeray.Units.B0224.Dilation
import UnforcedLeray.Units.B0223.Lift

/-!
# Strong continuity at age `0` of the age dilation `D_{e^{-s}}` on `H`

Source `the November 2 reference manuscript` lines 1650-1656.

`D_a` is a contraction for `a ≤ 1` (`norm_dilH_le`), so strong continuity at `a = 1` follows by an
`ε/4` argument from a dense class `ψ = s^{3/4} φ`, `φ` continuous with compact support, on which
the convergence is a dominated-convergence statement for the unweighted `L²` norm of
`a^{3/4} φ(a s, q, η) - φ(s, q, η)` on the cell.  The two analytic inputs are the Props
`DilDenseGood` (density of the class) and `DilGoodConv` (convergence on the class).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.DilStrong

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- Density (tex 1650-1656): `{s^{3/4} φ : φ ∈ C_c}` is dense in `H` (`c > 0`). -/
def DilDenseGood (c : ℝ) : Prop :=
  ∀ (f : HSpace c MeridC) (ε : ℝ), 0 < ε →
    ∃ (phi : Profile → MeridC), Continuous phi ∧ HasCompactSupport phi ∧
      ∃ hψ : MemLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) 2 (measureH c),
        ‖f - hψ.toLp _‖ < ε

/-- Convergence on the class (tex 1650-1656). -/
def DilGoodConv (c : ℝ) : Prop :=
  ∀ (phi : Profile → MeridC), Continuous phi → HasCompactSupport phi →
    ∀ hψ : MemLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) 2 (measureH c),
      Tendsto (fun s : ℝ => UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) (hψ.toLp _))
        (nhdsWithin 0 (Set.Ici 0)) (nhds (hψ.toLp _))

theorem measureH_eq_zero_of_nonpos {c : ℝ} (hc : c ≤ 0) : measureH c = 0 := by
  have h : UnforcedLeray.B0220.cellMeasure c = 0 := by
    unfold UnforcedLeray.B0220.cellMeasure UnforcedLeray.B0220.cell
    rw [Measure.restrict_eq_zero]
    have : Ioc (0 : ℝ) c = ∅ := Ioc_eq_empty (not_lt.2 hc)
    rw [this]; simp
  unfold measureH
  rw [h]; simp

theorem tendsto_dilH_exp_neg_zero_of
    (hd : ∀ c : ℝ, 0 < c → DilDenseGood c) (hv : ∀ c : ℝ, 0 < c → DilGoodConv c)
    (c : ℝ) (g : HSpace c MeridC) :
    Filter.Tendsto (fun s : ℝ => UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g)
      (nhdsWithin 0 (Set.Ici 0)) (nhds g) := by
  by_cases hc : 0 < c
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨phi, h1, h2, hψ, hnorm⟩ := hd c hc g (ε / 4) (by linarith)
    have hconv := hv c hc phi h1 h2 hψ
    rw [Metric.tendsto_nhds] at hconv
    filter_upwards [hconv (ε / 2) (by linarith), self_mem_nhdsWithin] with s hs hs0
    have hs0' : (0 : ℝ) ≤ s := hs0
    generalize hψ.toLp (fun p : Profile => p.1 ^ (3 / 4 : ℝ) • phi p) = ψ at hs hnorm
    set D := (UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) : HSpace c MeridC →L[ℝ] HSpace c MeridC)
    have hDn : ‖D‖ ≤ 1 := by
      refine (UnforcedLeray.B0224.norm_dilH_le (Real.exp_pos (-s))).trans ?_
      apply Real.rpow_le_one (Real.exp_pos _).le _ (by norm_num)
      rw [Real.exp_le_one_iff]; linarith
    have hgψ : ‖g - ψ‖ < ε / 4 := hnorm
    have hD1 : ‖D (g - ψ)‖ ≤ ‖g - ψ‖ :=
      (D.le_opNorm _).trans (by nlinarith [norm_nonneg (g - ψ)])
    have hs' : ‖D ψ - ψ‖ < ε / 2 := by simpa [dist_eq_norm] using hs
    have e : D g - g = D (g - ψ) + (D ψ - ψ) - (g - ψ) := by
      rw [map_sub]; abel
    rw [dist_eq_norm, e]
    calc ‖D (g - ψ) + (D ψ - ψ) - (g - ψ)‖
        ≤ ‖D (g - ψ) + (D ψ - ψ)‖ + ‖g - ψ‖ := norm_sub_le _ _
      _ ≤ ‖D (g - ψ)‖ + ‖D ψ - ψ‖ + ‖g - ψ‖ := by gcongr; exact norm_add_le _ _
      _ < ε := by linarith
  · have hc' : c ≤ 0 := not_lt.1 hc
    have hsub : ∀ f f' : HSpace c MeridC, f = f' := by
      intro f f'
      refine Lp.ext ?_
      have h0 := measureH_eq_zero_of_nonpos hc'
      simp only [Filter.EventuallyEq, h0, ae_zero, Filter.eventually_bot]
    have : (fun s : ℝ => UnforcedLeray.B0224.dilH (Real.exp_pos (-s)) g) = fun _ => g :=
      funext fun s => hsub _ _
    rw [this]
    exact tendsto_const_nhds

end UnforcedLeray.Short.PartIIIb.Concrete.DilStrong
