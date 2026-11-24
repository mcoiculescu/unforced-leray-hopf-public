import UnforcedLeray.Short.PartI.Sub.PartI_T04_9

/-!
# Part I, `PartI:T04/10`: `APLevel3` (second vorticity jet), reduced to three leaves

Source of record: `the November 2 reference manuscript`, lines 285-288 (vorticity
energy identities, scalar vorticity equation).

* `APLevel3Integrated`: integrated second-jet energy inequality (cutoff identity, `R → ∞`);
* `APLevel3Static`: static commutator estimate (`CylGN`, `CylSupInterp`, `APElliptic`, Young),
  with an arbitrary coefficient `ε > 0` in front of `‖D³ω‖²`;
* `IntegralGronwall`: real-analysis Gronwall inequality in integral form.

`apLevel3_of` closes `APLevel3` from these (datum constant: `vortJet c 2` of `trainDatum c`).

The energy identity of lines 285-287 is an identity for the Euclidean word sums
`Σ_{|u|=j} (∂_uω)²`; `vortJet` uses the operator norm of `iteratedFDeriv` (sup norm on the plane),
comparable with the word sum up to the factor `2^j` (`Sub/PartI_T04_10_1_2_1.lean`).  The
op-norm form of the integrated inequality therefore carries the constants `16` (datum) and `4`
(commutator) and the dissipation `ν ∫ ‖D³ω‖²`; the static estimate is used with `ε = ν/4`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Majorant of the commutator term `∫ ∂²ω · [∂², v·∇]ω` (`[∂², v·∇]ω = ∂²v·∇ω + 2∂v·∇∂ω`):
`16 ∫_cell |D²ω| (|D²v||Dω| + 2|Dv||D²ω|)` (`16` a universal constant comparing coordinate words
with operator norms; absorbed in the constant of `APLevel3Static`). -/
def commJet2 (c : ℝ) (v : ℝ → Plane → Vec) (r : ℝ) : ℝ :=
  16 * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ *
    (‖iteratedFDeriv ℝ 2 (v r) z‖ * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ +
      2 * (‖iteratedFDeriv ℝ 1 (v r) z‖ * ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖))

/-- **Leaf (cutoff identity for `∫ χ_R |∇²ω|²`, `R → ∞`, integrated in time)** (lines 285-288).
For a classical solution of the a priori class: `r ↦ ‖D³ω(r)‖²₂`, `r ↦ commJet2 r` are integrable
on `[0,T]`, `r ↦ ‖D²ω(r)‖²₂` is integrable and bounded on `[0,T]` (qualitative: `jet_l2` and
`apElliptic`), and for `s ∈ [0,T]`,
`‖D²ω(s)‖² + ν ∫_0^s ‖D³ω‖² ≤ 16 ‖D²ω(0)‖² + 4 ∫_0^s commJet2`
(operator norms; the word-sum identity `W₂(s) + 2ν∫W₃ ≤ W₂(0) + ∫ commJet2` with
`W_j = ∫ Σ_{|u|=j} (∂_uω)²` and `2^{-j}‖D^jω‖² ≤ Σ_{|u|=j}(∂_uω)² ≤ 2^j ‖D^jω‖²`).
Route: `apLevel3Integrated_of` (`Sub/PartI_T04_10_1.lean`). -/
def APLevel3Integrated : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 3 v r) (Icc (0 : ℝ) T) ∧
      IntegrableOn (fun r => commJet2 c v r) (Icc (0 : ℝ) T) ∧
      IntegrableOn (fun r => vortJet c 2 v r) (Icc (0 : ℝ) T) ∧
      (∃ M : ℝ, ∀ r ∈ Icc (0 : ℝ) T, vortJet c 2 v r ≤ M) ∧
      ∀ s ∈ Icc (0 : ℝ) T,
        vortJet c 2 v s + ν * ∫ r in (0 : ℝ)..s, vortJet c 3 v r ≤
          16 * vortJet c 2 v 0 + 4 * ∫ r in (0 : ℝ)..s, commJet2 c v r

/-- **Leaf (static commutator estimate)** (lines 285-288).  For `ν > 0`, `A` and `ε > 0` there is
`K ≥ 0` such that for a classical solution of the a priori class, `r ∈ [0,T]`, `‖v(r)‖²₂,
‖ω(r)‖²₂, ‖Dω(r)‖²₂, |ω(r)| ≤ A`: `commJet2 r ≤ ε ‖D³ω(r)‖²₂ + K (1 + ‖D²ω(r)‖²₂)`.
Route: Hölder with `cylGN_proof` (`m = 3`: `‖Dω‖₆ ≤ C|ω|_∞^{2/3}‖D³ω‖^{1/3}`,
`‖D²ω‖₃ ≤ C|ω|_∞^{1/3}‖D³ω‖^{2/3}`; same for `v` via `apElliptic`), `|v|_∞ ≤ C(‖v‖₂,‖D²v‖₂)`
(`cylinder_interpolation_uniform`, `CylSupInterp`), `‖D^{j+1}v‖² ≤ K_j‖D^jω‖²` (`apElliptic`);
Young absorbs `‖D³ω‖` (`apLevel3Static_of`, `Sub/PartI_T04_10_2.lean`, from the slice bounds
with `ε/48`). -/
def APLevel3Static : Prop :=
  ∀ ν A ε : ℝ, 0 < ν → 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ),
    1 ≤ c → IsAPrioriClass ν c T v p → ∀ r ∈ Icc (0 : ℝ) T, velJet c 0 v r ≤ A →
      vortJet c 0 v r ≤ A → vortJet c 1 v r ≤ A → (∀ z : Plane, |Cyl.curl (v r) z| ≤ A) →
        commJet2 c v r ≤ ε * vortJet c 3 v r + K * (1 + vortJet c 2 v r)

/-- **Leaf (Gronwall, integral form)**: a bounded integrable `Z` on `[0,T]` with
`Z(s) ≤ a + ∫_0^s C(1 + Z)` satisfies `Z(s) ≤ (a + 1) e^{C s}`.  (`W = Z + 1` satisfies
`W ≤ (a+1) + C ∫ W`; the standard argument, e.g. via `(∫_0^s W) e^{-Cs}` antitone.) -/
def IntegralGronwall : Prop :=
  ∀ (Z : ℝ → ℝ) (T a C : ℝ), 0 ≤ C → IntegrableOn Z (Icc (0 : ℝ) T) →
    (∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, |Z s| ≤ M) →
    (∀ s ∈ Icc (0 : ℝ) T, Z s ≤ a + ∫ r in (0 : ℝ)..s, C * (1 + Z r)) →
    ∀ s ∈ Icc (0 : ℝ) T, Z s ≤ (a + 1) * Real.exp (C * s)

/-- `PartI:T04/10`, conditional on the three leaves. -/
theorem apLevel3_of (hI : APLevel3Integrated) (hS : APLevel3Static) (hG : IntegralGronwall) :
    APLevel3 := by
  intro ν c S A hν hc hS0
  obtain ⟨K, hK0, hK⟩ := hS ν A (ν / 4) hν (by positivity)
  refine ⟨(16 * vortJet c 2 (fun _ => B0140.trainDatum c) 0 + 1) * Real.exp (4 * K * S), ?_⟩
  intro T v p hcls hTS hV hW hW1 hM s hs
  obtain ⟨hi3, hiC, hi2, ⟨M, hMb⟩, hmain⟩ := hI ν c T v p hν hc hcls
  have hY0 : vortJet c 2 v 0 = vortJet c 2 (fun _ => B0140.trainDatum c) 0 := by
    unfold vortJet; rw [hcls.classical.initial]
  have hnn : ∀ (w : ℝ → Plane → Vec) (j : ℕ) (r : ℝ), 0 ≤ vortJet c j w r := fun w j r =>
    integral_nonneg fun z => sq_nonneg _
  have hZ0 : 0 ≤ vortJet c 2 (fun _ => B0140.trainDatum c) 0 := hnn _ 2 0
  have hsub : ∀ s' ∈ Icc (0 : ℝ) T, vortJet c 2 v s' ≤
      16 * vortJet c 2 v 0 + ∫ r in (0 : ℝ)..s', (4 * K) * (1 + vortJet c 2 v r) := by
    intro s' hs'
    have hi3' := intervalIntegrable_of_integrableOn_Icc hi3 hs'
    have hiC' := intervalIntegrable_of_integrableOn_Icc hiC hs'
    have hi2' := intervalIntegrable_of_integrableOn_Icc hi2 hs'
    have key : ∀ r ∈ Set.Icc (0 : ℝ) s', commJet2 c v r ≤
        ν / 4 * vortJet c 3 v r + K * (1 + vortJet c 2 v r) := by
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hs'.2⟩
      exact hK c T v p hc hcls r hrT (hV r hrT) (hW r hrT) (hW1 r hrT) (hM r hrT)
    have hmono : ∫ r in (0 : ℝ)..s', commJet2 c v r ≤
        ∫ r in (0 : ℝ)..s', (ν / 4 * vortJet c 3 v r + K * (1 + vortJet c 2 v r)) :=
      intervalIntegral.integral_mono_on hs'.1 hiC'
        ((hi3'.const_mul (ν / 4)).add ((intervalIntegrable_const.add hi2').const_mul K)) key
    rw [intervalIntegral.integral_add (hi3'.const_mul (ν / 4))
      ((intervalIntegrable_const.add hi2').const_mul K), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hmono
    have hint4K : ∫ r in (0 : ℝ)..s', (4 * K) * (1 + vortJet c 2 v r) =
        4 * (K * ∫ r in (0 : ℝ)..s', (1 + vortJet c 2 v r)) := by
      rw [intervalIntegral.integral_const_mul]; ring
    rw [hint4K]
    have hm := hmain s' hs'
    linarith [hm, hmono]
  have hG' := hG (fun r => vortJet c 2 v r) T (16 * vortJet c 2 v 0) (4 * K)
    (by positivity) hi2 ⟨max M 0, fun r hr => by
      rw [abs_of_nonneg (hnn v 2 r)]; exact (hMb r hr).trans (le_max_left _ _)⟩ hsub s hs
  rw [hY0] at hG'
  refine hG'.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact Real.exp_le_exp.mpr (by nlinarith [hs.2, hTS, hK0])

end UnforcedLeray.Short.PartI
