import UnforcedLeray.Short.Spine.Statements
import UnforcedLeray.Short.Interface.Statements

/-!
# Composition of the three part outputs: `prop:unstable-background` (shorter proof)

Source: `the November 2 reference manuscript`, the four interfaces (lines
190-222), the phase selection (lines 5922-5985) and the closing paragraph (lines 5977-5988):
"Together with the background and its heat remainder this proves
Proposition `prop:unstable-background`."

The argument, at the level of the source's numbered steps:
1. Part I gives a planar reference `P` and the exact train at `c = ν^{-2}` for small `ν`.
2. Parameter choice (before the scan): `σ₀` with `𝒞(σ₀) ≠ 0` (`ReferenceFromInstability`), the
   phase-locked `ν_n`, `ε_n`, with `-ν_n log ε_n → γ/3` (`ParameterAsymptotics`).
3. Part II at `dLo = γ/6`, `dHi = γ/2` and `m = min(m_II, m_III)` fixes the slow age `Σ` of the
   inlet and `P_ν = Cν^{-N}`, and gives an exact background at `(ν_n, ε_n)` on the train of step 1
   for all large `n`; one background is chosen per level (lines 5951-5952).
4. Part III gives the energy mode on the background of every large level of that sequence.
5. The background half of the package is the library's `IsExactBackground`, from the
   `IsB3Output` of Part II and the proved pressure conversion `pressureProjectionStep`
   (lines 164-167 versus the unprojected equation with `L²` pressure).

Two small facts are separate named hypotheses with their own proofs delegated:
`ReferenceFromInstability` (identity theorem for the holomorphic `𝒥`) and
`ParameterAsymptotics` (`ν_n → 0`, `ε_n > 0`, `-ν_n log ε_n → γ/3`), both in `Params.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

theorem shortPeriod_pos {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) : 0 < shortPeriod ν ε := by
  unfold shortPeriod Train.per
  have : 0 < ν⁻¹ ^ 2 := by positivity
  positivity

/-- Step 5: the background half of `prop:unstable-background` from the output of Part II. -/
theorem isExactBackground_of_short {P : PlanarData} {ν ε m C : ℝ} {N : ℕ} {Sig : ℝ}
    {B : ShortBackground} (h : IsShortBackground P ν ε m C N Sig B) :
    IsExactBackground ⟨ν, shortPeriod ν ε, B.a, B.U, B.Q⟩ :=
  isExactBackground_of_B3 pressureProjectionStep h.nu_pos (shortPeriod_pos h.nu_pos h.eps_pos) h.b3

/-- **`prop:unstable-background` of the shorter proof from the three part outputs.** -/
theorem constructionClaimShort_of_parts (hRef : ReferenceFromInstability)
    (hAsym : ParameterAsymptotics) (hI : PartIOutput) (hII : PartIIOutput)
    (hIII : PartIIIOutput) : Interface.ConstructionClaimShort := by
  classical
  obtain ⟨⟨P, hP⟩, ⟨νI, hνI, hexist⟩⟩ := hI
  obtain ⟨R, -, hRc⟩ := hRef P hP
  obtain ⟨hνpos, hνlim, hεpos, hd⟩ := hAsym R hRc
  have hγ : 0 < R.planar.eigenvalue.re := hRc.1.eigenpair.re_pos
  obtain ⟨m₃, hm₃, hIII'⟩ := hIII R hRc
  obtain ⟨m₂, hm₂, hII'⟩ := hII R.planar hRc.1 (R.planar.eigenvalue.re / 6)
    (R.planar.eigenvalue.re / 2) (by linarith) (by linarith)
  have hm : 0 < min m₂ m₃ := lt_min hm₂ hm₃
  obtain ⟨Sig, hSig, ν₀, C, N, hν₀, -, hbg⟩ := hII' (min m₂ m₃) hm (min_le_left _ _)
  have hev : ∀ᶠ n in atTop, nuSeq R n < min ν₀ νI ∧
      lossExponent R n ∈ Icc (R.planar.eigenvalue.re / 6) (R.planar.eigenvalue.re / 2) :=
    (hνlim.eventually_lt_const (lt_min hν₀ hνI)).and
      (hd.eventually (Icc_mem_nhds (by linarith) (by linarith)))
  -- Part II at every large level, on the train of Part I
  have hgood : ∀ᶠ n in atTop, ∃ B : ShortBackground,
      IsShortBackground R.planar (nuSeq R n) (epsSeq R n) (min m₂ m₃) C N Sig B := by
    filter_upwards [hev] with n hn
    obtain ⟨T, hT⟩ := hexist (nuSeq R n) ⟨hνpos n, (hn.1.trans_le (min_le_right _ _)).le⟩
    obtain ⟨B, -, hB⟩ := hbg (nuSeq R n) ⟨hνpos n, (hn.1.trans_le (min_le_left _ _)).le⟩
      (epsSeq R n) (hεpos n) hn.2 T hT
    exact ⟨B, hB⟩
  -- one background per level (lines 5951-5952)
  obtain ⟨n₁, hn₁⟩ := hgood.exists
  have : Nonempty ShortBackground := ⟨hn₁.choose⟩
  let B : ℕ → ShortBackground := fun n => Classical.epsilon fun B : ShortBackground =>
    IsShortBackground R.planar (nuSeq R n) (epsSeq R n) (min m₂ m₃) C N Sig B
  have hB : ∀ᶠ n in atTop,
      IsShortBackground R.planar (nuSeq R n) (epsSeq R n) (min m₂ m₃) C N Sig (B n) := by
    filter_upwards [hgood] with n hn
    exact Classical.epsilon_spec hn
  obtain ⟨n, ⟨M, hM⟩, hBn⟩ :=
    ((hIII' (min m₂ m₃) hm (min_le_right _ _) Sig C N hSig B hB).and hB).exists
  exact ⟨⟨⟨nuSeq R n, shortPeriod (nuSeq R n) (epsSeq R n), (B n).a, (B n).U, (B n).Q⟩, M⟩,
    isExactBackground_of_short hBn, hM⟩

end UnforcedLeray.Short.Spine
