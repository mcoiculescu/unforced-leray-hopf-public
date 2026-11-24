import UnforcedLeray.Short.PartI.Sub.T04.APriori

/-!
# Part I, `PartI:T04/9`: `APLevel2` (first vorticity jet), reduced to two leaves

Source of record: `the November 2 reference manuscript`, lines 285-288 (vorticity
energy identities, scalar vorticity equation `ω_s + v·∇ω = νΔω`).

* `APLevel2IntegratedW`: the integrated first-jet energy inequality of a classical solution of the
  a priori class (cutoff identity for `∫χ_R |∇ω|²`, then `R → ∞`);
* `APLevel2Static`: the static estimate of the trilinear term (`CylGN`, `APElliptic`, Hölder, Young).

`apLevel2_of` closes `APLevel2` from these two (the datum constant is `vortJet c 1` of
`trainDatum c`, `hcls.classical.initial`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Majorant of the vortex-stretching-type trilinear term `∫ ∂_iω ∂_iv_j ∂_jω` of line 285-288:
`4 ∫_cell |Dω|² |Dv|` (the factor `4` is a universal constant comparing coordinate words with the
operator norms of `iteratedFDeriv`; it is absorbed in the constant `K` of `APLevel2Static`). -/
def triJet1 (c : ℝ) (v : ℝ → Plane → Vec) (r : ℝ) : ℝ :=
  4 * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖

/-- **The integrated first-jet inequality for the operator-norm jets** (constants `2, 4`): the
Euclidean cutoff inequality of lines 285-288 compared with `vortJet`, `triJet1` by
`‖D f‖² ≤ 2 |Df|²`, `‖D²f‖² ≤ 4 |D²f|²`, `|Df|² ≤ ‖Df‖²` (proved in `Sub/PartI_T04_9_1.lean`).
For a classical solution of the a priori class: `r ↦ ‖D²ω(r)‖²₂` and `r ↦ triJet1 r` are
integrable on `[0,T]` and, for `s ∈ [0,T]`,
`‖Dω(s)‖² + ν ∫_0^s ‖D²ω‖² ≤ 2 ‖Dω(0)‖² + 4 ∫_0^s triJet1`. -/
def APLevel2IntegratedW : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 2 v r) (Icc (0 : ℝ) T) ∧
      IntegrableOn (fun r => triJet1 c v r) (Icc (0 : ℝ) T) ∧
      ∀ s ∈ Icc (0 : ℝ) T,
        vortJet c 1 v s + ν * ∫ r in (0 : ℝ)..s, vortJet c 2 v r ≤
          2 * vortJet c 1 v 0 + 4 * ∫ r in (0 : ℝ)..s, triJet1 c v r

/-- **Leaf (static estimate of the trilinear term)** (lines 285-288).  There is a universal `K ≥ 0`
such that for a classical solution of the a priori class, `r ∈ [0,T]`, `‖ω(r)‖²₂ ≤ A`,
`|ω(r)| ≤ A`: `triJet1 r ≤ (ν/4) ‖D²ω(r)‖²₂ + K A³/ν`.
Route: `∫|Dω|²|Dv| ≤ ‖Dv‖₂ ‖Dω‖₄²`; `‖Dv‖₂² ≤ K₀ ‖ω‖₂²` (`apElliptic`, `j = 0`);
`‖Dω‖₄² ≤ C ‖ω‖_∞ ‖D²ω‖₂` (`cylGN_proof`, `m = 2`, `l = 1`, `f = ω`); Young.  The `L²`/jet
finiteness hypotheses of `cylGN_proof`/`apElliptic` come from `jet_l2`, `bounded`, `classical`. -/
def APLevel2Static : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν c T A : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ r ∈ Icc (0 : ℝ) T, vortJet c 0 v r ≤ A →
      (∀ z : Plane, |Cyl.curl (v r) z| ≤ A) →
        triJet1 c v r ≤ (ν / 4) * vortJet c 2 v r + K * A ^ 3 / ν

/-- Restricting integrability on `[0,T]` to `[0,s]`. -/
theorem intervalIntegrable_of_integrableOn_Icc {f : ℝ → ℝ} {T s : ℝ}
    (hf : IntegrableOn f (Icc (0 : ℝ) T)) (hs : s ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable f volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs.1]
  exact hf.mono_set (Icc_subset_Icc le_rfl hs.2)

/-- `PartI:T04/9`, conditional on the two leaves. -/
theorem apLevel2_of (hI : APLevel2IntegratedW) (hS : APLevel2Static) : APLevel2 := by
  obtain ⟨K, hK0, hK⟩ := hS
  intro ν c S A hν hc hS0
  refine ⟨2 * vortJet c 1 (fun _ => B0140.trainDatum c) 0 + 4 * (K * A ^ 3 / ν) * S, ?_⟩
  intro T v p hcls hTS hE hM s hs
  obtain ⟨hint2, hintT, hmain⟩ := hI ν c T v p hν hc hcls
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hcls.pos.le⟩
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (hM 0 h0 (0 : Plane))
  have hY0 : vortJet c 1 v 0 = vortJet c 1 (fun _ => B0140.trainDatum c) 0 := by
    unfold vortJet; rw [hcls.classical.initial]
  have hM0 : 0 ≤ K * A ^ 3 / ν := by positivity
  have key : ∀ r ∈ Icc (0 : ℝ) s, triJet1 c v r ≤ (ν / 4) * vortJet c 2 v r + K * A ^ 3 / ν := by
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hs.2⟩
    exact hK ν c T A v p hν hc hcls r hrT (hE r hrT) (hM r hrT)
  have hi2 := intervalIntegrable_of_integrableOn_Icc hint2 hs
  have hiT := intervalIntegrable_of_integrableOn_Icc hintT hs
  have hmono : ∫ r in (0 : ℝ)..s, triJet1 c v r ≤
      ∫ r in (0 : ℝ)..s, ((ν / 4) * vortJet c 2 v r + K * A ^ 3 / ν) :=
    intervalIntegral.integral_mono_on hs.1 hiT
      ((hi2.const_mul (ν / 4)).add intervalIntegrable_const) key
  rw [intervalIntegral.integral_add (hi2.const_mul (ν / 4)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero] at hmono
  have hm := hmain s hs
  have hSs : K * A ^ 3 / ν * s ≤ K * A ^ 3 / ν * S :=
    mul_le_mul_of_nonneg_left (hs.2.trans hTS) hM0
  rw [hY0] at hm
  nlinarith [hm, hmono, hSs]

end UnforcedLeray.Short.PartI
