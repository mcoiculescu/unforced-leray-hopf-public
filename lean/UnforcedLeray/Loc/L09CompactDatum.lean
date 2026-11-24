import UnforcedLeray.Loc.L09CompactDatum.Solenoidal
import UnforcedLeray.Loc.L09CompactDatum.Symmetry

/-!
# Step L9: the compact datum `u_{0,h} = curl(χ A_loc)` and its heat tail

`paper/main.tex` lines 430–461 (`loc:eq:compact-datum`, `loc:eq:heat-correction`), blueprint
units B0717 (`A_loc` and `curl A_loc = u_dss`), B0718 (the datum, `d_loc`, `K_loc`), B0719
(compact, solenoidal, `L²`, nonzero), B0720 (`‖K_loc(τ)‖_{W^{2,∞}} ≤ Ce^{τ/2}`, `τ ≤ 0`).

Main result: `compactDatumStep : CompactDatumStep` (the step proposition of
`Blueprint/Localization/Nonlinear.lean`, line 88). For every unstable background `D` the
cutoff `χ(x) = S(2 - |x|²)` (`cutoff`) is radial, and `u_{0,h} = curl(χ A_loc)` built from
`D.udss` has every property of `IsCompactDatum`.

The proof uses only the package fields of `IsExactBackground` (through `dssField_of_exact`):
smoothness off zero, the DSS law, `|u_dss(x)||x| ≤ C`, distributional solenoidality,
`𝒪`-invariance and nonvanishing, and `h > 0`. Helpers (folder `L09CompactDatum/`):
* `Vector`: cross-product algebra;
* `ParamIntegral`: differentiation under the integral sign, heat smoothing of fields with
  bounded derivatives;
* `Background`: `DSSField`, derivative bounds of `u_dss` at infinity, pointwise `div u_dss = 0`;
* `Potential`: `A_loc = -c x × V(x)`, `curl A_loc = u_dss` off zero (lines 431–440);
* `Defect`: `L¹`/`L²` from `|f(x)||x| ≤ C`, the smoothed defect, the heat-tail bound;
* `Datum`: the cutoff; `u_{0,h}` smooth off zero, `= u_dss` near zero, compactly supported,
  in `L²`, nonzero (lines 441–453);
* `Solenoidal`: `div curl = 0` and distributional solenoidality across zero (line 451);
* `Symmetry`: `𝒪`-invariance (line 436).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

variable {q : ℝ} {u : SpatialField}

namespace DSSField

/-- Derivatives of every order of `u_{0,h}` are bounded on `|x| ≥ 1` (it vanishes on
`|x| > 3/2`). -/
theorem compactDatum_iteratedFDeriv_bounded (hu : DSSField q u) (n : ℕ) :
    ∃ M : ℝ, ∀ x : Space, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (compactDatum cutoff u) x‖ ≤ M := by
  set K : Set Space := {y | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space) 2).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro y hy; simpa [Metric.mem_closedBall, dist_zero_right] using hy.2
  have hK0 : K ⊆ {0}ᶜ := by
    intro y hy h0
    rw [mem_singleton_iff] at h0
    have := hy.1
    rw [h0, norm_zero] at this
    linarith
  have hcont : ContinuousOn (iteratedFDeriv ℝ n (compactDatum cutoff u)) {0}ᶜ :=
    ContinuousOn.continuousOn_iteratedFDeriv (hu.compactDatum_contDiffOn cutoff_contDiff)
      isOpen_compl_singleton (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hK0)
  refine ⟨max M 0, fun x hx => ?_⟩
  by_cases h2 : ‖x‖ ≤ 2
  · exact (hM x ⟨hx, h2⟩).trans (le_max_left _ _)
  · have hzero : compactDatum cutoff u =ᶠ[𝓝 x] fun _ => (0 : Space) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show (3 / 2 : ℝ) < ‖x‖ by linarith [not_le.mp h2])] with y hy
      exact compactDatum_cutoff_eq_zero u hy
    rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp

/-- **The compact datum** (lines 441–461): for a background field `u_dss` with the package
properties and heat diffusivity `h > 0`, `u_{0,h} = curl(χ A_loc)` satisfies
`IsCompactDatum`. -/
theorem isCompactDatum {D : BackgroundData} (hu : DSSField q D.udss) (hh : 0 < D.h) :
    IsCompactDatum D (compactDatum cutoff D.udss) := by
  set u₀ := compactDatum cutoff D.udss with hu₀
  have hs₀ : ContDiffOn ℝ ∞ u₀ {0}ᶜ := hu.compactDatum_contDiffOn cutoff_contDiff
  -- the defect `d_loc = u_{0,h} - u_dss`
  have hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < 1 → (u₀ - D.udss) x = 0 := by
    intro x hx hx1
    rw [Pi.sub_apply, hu₀, hu.compactDatum_eq_near hx hx1, sub_self]
  have hds : ContDiffOn ℝ ∞ (u₀ - D.udss) {0}ᶜ := hs₀.sub hu.smooth
  have hdb : ∀ n : ℕ, ∃ M : ℝ, ∀ x : Space, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n (u₀ - D.udss) x‖ ≤ M := by
    intro n
    obtain ⟨M₀, hM₀⟩ := hu.compactDatum_iteratedFDeriv_bounded n
    obtain ⟨M₁, hM₁⟩ := hu.iteratedFDeriv_bounded_far n
    refine ⟨M₀ + M₁, fun x hx => ?_⟩
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hx; linarith
    have h0 : ContDiffAt ℝ n u₀ x :=
      (hs₀.contDiffAt (isOpen_compl_singleton.mem_nhds hx0)).of_le (by exact_mod_cast le_top)
    have h1 : ContDiffAt ℝ n D.udss x :=
      (hu.smooth.contDiffAt (isOpen_compl_singleton.mem_nhds hx0)).of_le
        (by exact_mod_cast le_top)
    rw [iteratedFDeriv_sub_apply h0 h1]
    exact (norm_sub_le _ _).trans (add_le_add (hM₀ x hx) (hM₁ x hx))
  obtain ⟨C₀, hC₀⟩ := hu.compactDatum_inverse_bound
  obtain ⟨C, hC⟩ := hu.bound
  have hdC : ∀ x : Space, x ≠ 0 → ‖(u₀ - D.udss) x‖ * ‖x‖ ≤ C₀ + C := by
    intro x hx
    rw [Pi.sub_apply]
    calc ‖u₀ x - D.udss x‖ * ‖x‖ ≤ (‖u₀ x‖ + ‖D.udss x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ = ‖u₀ x‖ * ‖x‖ + ‖D.udss x‖ * ‖x‖ := add_mul _ _ _
      _ ≤ C₀ + C := add_le_add (hC₀ x hx) (hC x hx)
  obtain ⟨hsmooth, hbound⟩ := heatProfile_tail (ρ := 1) one_pos hd0 hds hdb hh
  obtain ⟨K0, hK0⟩ := hbound 0
  obtain ⟨K1, hK1⟩ := hbound 1
  obtain ⟨K2, hK2⟩ := hbound 2
  refine
    { datum := ⟨hu.compactDatum_memLp, compactDatum_hasCompactSupport _,
        hu.compactDatum_isSolenoidal, hu.compactDatum_l2Norm_pos⟩
      symmetric := hu.compactDatum_symmetric
      agrees_near_zero := ⟨1, one_pos, fun x hx hx1 => hu.compactDatum_eq_near hx hx1⟩
      smooth_away := hs₀
      defect_heat_integrable := fun s hs x =>
        heat_integrable_of_inverse_bound hds.continuousOn hdC hs x
      tail_smooth := hsmooth
      tail_bound := ⟨max K0 (max K1 K2), fun τ hτ y => ?_⟩ }
  have he : 0 ≤ Real.exp ((1 / 2) * τ) := (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_⟩
  · have h := hK0 τ hτ y
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
  · have h := hK1 τ hτ y
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) he)
  · exact (hK2 τ hτ y).trans
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) he)

end DSSField

/-- **Step L9** `CompactDatumStep` (`paper/main.tex` lines 430–461; blueprint units B0717,
B0718, B0719, B0720): for every unstable background, the radial cutoff `χ(x) = S(2 - |x|²)`
and the explicit datum `u_{0,h} = curl(χ A_loc)`, `A_loc(x) = -∫₀¹ r x × u_dss(rx) dr`, satisfy
`IsCompactDatum`: `u_{0,h}` is a nonzero compactly supported solenoidal `L²` datum,
axisymmetric without swirl, equal to `u_dss` near zero and smooth off zero; the heat integrals
of `d_loc = u_{0,h} - u_dss` converge, and `K_loc = H_h[d_loc]` is smooth with
`‖K_loc(τ)‖_{W^{2,∞}} ≤ Ce^{τ/2}` for `τ ≤ 0` (`loc:eq:heat-correction`). -/
theorem compactDatumStep : CompactDatumStep := by
  intro D hD
  have hB := hD.1
  exact ⟨cutoff, isRadialCutoff_cutoff, (dssField_of_exact hB).isCompactDatum hB.h_pos⟩

end UnforcedLeray.L09

#print axioms UnforcedLeray.L09.compactDatumStep
