import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2

/-!
# Part I, `PartI:T04/9/1/2/2`: `APL2Diff` from three leaves (source lines 285-288)

`the November 2 reference manuscript` lines 285-288.  The differentiated local
vorticity equation `∂_s ω + v·∇ω = νΔω` gives, for `s ∈ (0,T)`,

`∂_s G¹_R = -2ν G²_R - 2 X_R + E_R`,

with the explicit cell integrals
* `X_R = ∫ χ_R Σ_{ij} ∂_iω ∂_iv_j ∂_jω` (`apL2X`, trilinear term),
* `E_R = ∫ χ_R' v_η |Dω|² - 2ν ∫ χ_R' Σ_i ∂_iω ∂_η∂_iω` (`apL2E`, transport and cutoff-derivative
  strip terms; `' = d/dη`),
and `G²_R = apCutG c 2` is the Euclidean `Σ_{ij}∫χ_R(∂_i∂_jω)²` (`eucJet2`), so the viscous term is an
identity.  Leaves: `APL2HasDeriv` (the identity), `APL2TriBound` (`-2X_R ≤ 2 Tri_R`, pointwise
`|Σ ∂_iω ∂_iv_j ∂_jω| ≤ 2 |Dω|² ‖Dv‖`), `APL2StripBound` (`E_R ≤ C R^{-1/2}`).
`apL2Diff_of` assembles `APL2Diff` from them and `APL2Reg` (integrability of the pieces).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The trilinear term `X_R(s) = ∫_cell χ_R Σ_{ij} ∂_iω ∂_iv_j ∂_jω` (`ω = curl v(s)`, `i,j` over
`q, η`, `v_0, v_1` the components of `v`; lines 285-288). -/
def apL2X (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 *
    (Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 0 * Cyl.partialQ (Cyl.curl (v s)) z
      + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
          Cyl.partialEta (Cyl.curl (v s)) z
      + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
          Cyl.partialQ (Cyl.curl (v s)) z
      + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
          Cyl.partialEta (Cyl.curl (v s)) z)

/-- The transport and cutoff-derivative strip term
`E_R(s) = ∫ χ_R' v_η |Dω|² - 2ν ∫ χ_R' (∂_qω ∂_η∂_qω + ∂_ηω ∂_η∂_ηω)` (lines 285-288; cf.
`apEnstrophyRhs`). -/
def apL2E (ν c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 *
      (Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
    - 2 * ν * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
        (Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
          + Cyl.partialEta (Cyl.curl (v s)) z *
              Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z))

/-- The derivative of the cutoff enstrophy `G¹_R`: `-2ν G²_R - 2 X_R + E_R`. -/
def apL2Rhs (ν c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ν * apCutG c 2 v R s - 2 * apL2X c v R s + apL2E ν c v R s

/-- The time derivative under the integral: `W(s) = ∫ χ_R 2 (∂_qω ∂_s∂_qω + ∂_ηω ∂_s∂_ηω)`. -/
def apL2W (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 *
    (2 * (Cyl.partialQ (Cyl.curl (v s)) z *
        deriv (fun t => Cyl.partialQ (Cyl.curl (v t)) z) s
      + Cyl.partialEta (Cyl.curl (v s)) z *
        deriv (fun t => Cyl.partialEta (Cyl.curl (v t)) z) s))

/-- **Leaf 1a (differentiation under the integral)** (lines 285-288): for `R ≥ 1`, `s ∈ (0,T)`,
`G¹_R` has derivative `apL2W`.  Route: compact support of `χ_R` in `η` and `c`-periodicity give a
compact domain `[−c/2,c/2] × [−2R,2R]`; `v` is `C^∞` on `(0,T) × Plane` (`IsClassicalOn.smooth_v`),
so `(s,z) ↦ ∂_iω(s,z)` is `C¹` jointly (`CurlRegularity`); apply the dominated differentiation
theorem as `apHD_deriv_integral` (`Tasks/TrainGlobalExistence/APEnstrophy/HasDeriv.lean`). -/
def APL2HasDerivUnder : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (apCutG c 1 v R) (apL2W c v R s) s

/-- **Leaf 1b (integration by parts)** (lines 285-288): for `s ∈ (0,T)`, `W(s) = -2ν G²_R(s) - 2
X_R(s) + E_R(s)`.  Route: `ω_s = -v·∇ω + νΔω` on `(0,T)` (`localVorticityEquation`,
`Sub/T02_4.lean:71`), differentiated once in `q` and `η` (smoothness on `(0,T) × Plane`, symmetry of
second and third derivatives; `∂_s∂_iω = ∂_i∂_sω`); then
`2χ∂_iω∂_i(-v_j∂_jω) = -2χ∂_iω∂_iv_j∂_jω - χ v_j ∂_j|Dω|²`, with `-∫χ v_j∂_j|Dω|² = ∫χ' v_η |Dω|²`
(`div v = 0`, `q`-periodicity, compact `η`-support), and `2ν∫χ∂_iω∂_iΔω =
-2ν∫χ(∂_k∂_iω)² - 2ν∫χ'∂_iω∂_η∂_iω` (two integrations by parts); compare `apHD_core`. -/
def APL2IBP : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      apL2W c v R s = apL2Rhs ν c v R s

/-- **Leaf 1 (differentiated vorticity identity)** (lines 285-288): for `R ≥ 1` and `s ∈ (0,T)`,
`G¹_R` has derivative `apL2Rhs`; from `APL2HasDerivUnder` and `APL2IBP`. -/
def APL2HasDeriv : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (apCutG c 1 v R) (apL2Rhs ν c v R s) s

theorem apL2HasDeriv_of (h1 : APL2HasDerivUnder) (h2 : APL2IBP) : APL2HasDeriv := by
  intro ν c T v p hν hc hcls R hR s hs
  have := h1 ν c T v p hν hc hcls R hR s hs
  rwa [h2 ν c T v p hν hc hcls R hR s hs] at this

/-- **Leaf 2 (trilinear term)** (lines 285-288): `-2 X_R(s) ≤ 2 Tri_R(s)`.  Pointwise
`|Σ_{ij} ∂_iω ∂_iv_j ∂_jω| ≤ (|∂_qω| + |∂_ηω|)² ‖Dv‖ ≤ 2 eucJet1(ω) ‖Dv‖` (entries
`|∂_iv_j| ≤ ‖iteratedFDeriv ℝ 1 v‖`, `eucJet1` comparison lemmas of `Sub/PartI_T04_9_1_euc.lean`),
integrated against `χ_R ≥ 0` (integrability from `jet_l2`, `HasBoundedDerivsOn`); `apCutTri` is
`4 ∫ χ_R eucJet1(ω) ‖Dv‖`. -/
def APL2TriBound : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      -2 * apL2X c v R s ≤ 2 * apCutTri c v R s

/-- **Leaf 3 (strip error)** (lines 285-288): there is `C ≥ 0` with `E_R(s) ≤ C R^{-1/2}` for all
`R ≥ 1`, `s ∈ (0,T)`.  Route: `|χ_R'| ≤ C₀ R^{-1} 1_{R≤|η|≤2R}` (`etaCutoff` facts of
`ClassicalOdd/EtaCutoffFacts.lean`), strip of measure `≤ 2cR`, Cauchy-Schwarz with `jet_l2` for
`j = 1, 2` (`‖Dω‖ ≤ 2‖D²v‖`, `‖D²ω‖ ≤ 2‖D³v‖`) and `v_η` bounded (`HasBoundedDerivsOn`);
template `APEnstrophy/RhsEstimate.lean`. -/
def APL2StripBound : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      apL2E ν c v R s ≤ C / Real.sqrt R

theorem apL2Diff_of (hA : APL2Reg) (h1 : APL2HasDeriv) (h2 : APL2TriBound)
    (h3 : APL2StripBound) : APL2Diff := by
  intro ν c T v p hν hc hcls
  obtain ⟨C, hC0, hC⟩ := h3 ν c T v p hν hc hcls
  refine ⟨T * C, mul_nonneg hcls.pos.le hC0, fun R hR s hs => ?_⟩
  obtain ⟨hcont, hdiff, hint⟩ := hA ν c T v p hν hc hcls R hR
  obtain ⟨hcG2, hcTri⟩ := apLevel2CutCont ν c T v p hν hc hcls R hR
  have hRpos : 0 < Real.sqrt R := Real.sqrt_pos.2 (by linarith)
  have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hs.2
  have huIcc : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := by
    rw [uIcc_of_le hs.1]; exact hsub
  have hT0 : (0 : ℝ) ≤ T := hs.1.trans hs.2
  have huT : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT0]; exact huIcc
  have hd : IntervalIntegrable (deriv (apCutG c 1 v R)) volume 0 s := hint.mono_set huT
  have hi2 : IntervalIntegrable (fun r => apCutG c 2 v R r) volume 0 s :=
    (hcG2.mono huIcc).intervalIntegrable
  have hiT : IntervalIntegrable (fun r => apCutTri c v R r) volume 0 s :=
    (hcTri.mono huIcc).intervalIntegrable
  have hf : IntervalIntegrable (fun r => deriv (apCutG c 1 v R) r + 2 * ν * apCutG c 2 v R r
        - 2 * apCutTri c v R r) volume 0 s :=
    (hd.add (hi2.const_mul (2 * ν))).sub (hiT.const_mul 2)
  have hg : IntervalIntegrable (fun _ : ℝ => C / Real.sqrt R) volume 0 s :=
    intervalIntegrable_const
  have hmono : ∫ r in (0 : ℝ)..s, (deriv (apCutG c 1 v R) r + 2 * ν * apCutG c 2 v R r
        - 2 * apCutTri c v R r) ≤ ∫ r in (0 : ℝ)..s, C / Real.sqrt R := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hs.1 hf hg (fun r hr => ?_)
    have hrT : r ∈ Ioo (0 : ℝ) T := ⟨hr.1, hr.2.trans_le hs.2⟩
    have hder := (h1 ν c T v p hν hc hcls R hR r hrT).deriv
    have ht := h2 ν c T v p hν hc hcls R hR r hrT
    have he := hC R hR r hrT
    rw [hder]
    unfold apL2Rhs
    linarith
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  calc s * (C / Real.sqrt R) ≤ T * (C / Real.sqrt R) :=
        mul_le_mul_of_nonneg_right hs.2 (div_nonneg hC0 hRpos.le)
    _ = T * C / Real.sqrt R := by ring
    _ = _ := rfl

end UnforcedLeray.Short.PartI
