import UnforcedLeray.Short.PartIIa.Calc.BaseJets

/-!
# Part II-a, task `PartII-a:R02/8`: the `A₁` block of the late table (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 1243-1285: the
coefficient `A₁ = -v₁Kv₁ + H(v₁)_η - v₁² + 2ν(K+1)(v₁)_q - (K+2)p` (line 1251) has size `s^{-2}`,
`(K+3)A₁` size `s^{-2}` (table row 1276), `∂_η A₁` size `s^{-5/2}` (an `η` derivative gains
`s^{-1/2}`, lines 1271-1272), and `∂_q A₁` is exponentially small (line 1281).

Route (jet classes of `Calc/JetClass.lean`): `ψ = S + ψ̃` with `S ∈ JQ (1/2)` and `ψ̃, p ∈ JE`
(`Calc/BaseJets.lean`), so `ψ ∈ JQ (1/2)`, `v₁ = -∂_ηψ ∈ JQ 1`, `Kv₁ ∈ JQ 1`, `∂_ηv₁ ∈ JQ (3/2)`,
`H = (1-K)ψ ∈ JQ (1/2)`; the products `v₁Kv₁, H∂_ηv₁, v₁²` are in `JQ 2`; `(K+1)∂_q v₁` and
`(K+2)p` are in `JE ⊆ JQ 2`.  Hence `A₁ ∈ JQ n 2` for every `n` (`a1Jets_of`), and the block
follows from `JQ 1 2 A₁` by `lateStmt_of_JQ` (`ringLateA1_of_jets`).

Unconditional target `ringLateA1_of (h : LateIngredients) : RingLateA1` (file
`Tasks/R02/BlockA1.lean`): `ringLateA1_of_parts jetToolkit (fluctWords_of h) (meanWords …)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- `v₁ = -∂_η ψ` (`streamV1`). -/
def v1Fam : Fam := fun _ _ tr => streamV1 (trainProfile tr.ψ)

/-- `H = (1-K)ψ` (`ageDefect`). -/
def hFam : Fam := fun _ _ tr => ageDefect (trainProfile tr.ψ)

theorem v1Fam_eq : v1Fam = -(famEta psiFam) := rfl

theorem hFam_eq : hFam = psiFam - famK psiFam := rfl

/-- `A₁` as a combination of jets (line 1251). -/
theorem coeffA1_late :
    LateEq (-(v1Fam * famK v1Fam) + hFam * famEta v1Fam - v1Fam * v1Fam +
        (2 : ℝ) • famNu (famShift 1 (famQ v1Fam)) - famShift 2 presFam) (coefFam coeffA₁) := by
  intro ν c _ _ tr _ x _
  show -(v1Fam ν c tr x * famK v1Fam ν c tr x) + hFam ν c tr x * famEta v1Fam ν c tr x -
      v1Fam ν c tr x * v1Fam ν c tr x + 2 * (ν * famShift 1 (famQ v1Fam) ν c tr x) -
      famShift 2 presFam ν c tr x = coeffA₁ ν (trainProfile tr.ψ) (trainProfile tr.p) x
  simp only [coeffA₁, v1Fam, hFam, famK, famEta, famQ, famShift, presFam]
  ring

/-- **`A₁` is a weighted jet of size `2`** at every depth. -/
theorem a1Jets_of (hJ : JetCalculus) (hψ : ∀ n, JQ n (1 / 2) psiFam)
    (hP : ∀ n, JE n presFam) (n : ℕ) : JQ n 2 (coefFam coeffA₁) := by
  have hv : ∀ n, JQ n 1 v1Fam := fun n => by
    have h := (hψ (n + 1)).eta
    rw [v1Fam_eq]
    exact hJ.qneg (h.cast (by norm_num))
  have hH : ∀ n, JQ n (1 / 2) hFam := fun n => by
    rw [hFam_eq]
    exact hJ.qsub (hψ n) (hψ (n + 1)).k
  have t1 : JQ n 2 (-(v1Fam * famK v1Fam)) :=
    hJ.qneg ((hJ.qmul (by norm_num) (by norm_num) (hv n) (hv (n + 1)).k).cast (by norm_num))
  have t2 : JQ n 2 (hFam * famEta v1Fam) :=
    (hJ.qmul (by norm_num) (by norm_num) (hH n) (hv (n + 1)).eta).cast (by norm_num)
  have t3 : JQ n 2 (v1Fam * v1Fam) :=
    (hJ.qmul (by norm_num) (by norm_num) (hv n) (hv n)).cast (by norm_num)
  have t4 : JQ n 2 ((2 : ℝ) • famNu (famShift 1 (famQ v1Fam))) :=
    hJ.qofE 2 (hJ.esmul 2 (hJ.enu (hJ.eshift 1 (hv (n + 2)).q)))
  have t5 : JQ n 2 (famShift 2 presFam) := hJ.qofE 2 (hJ.eshift 2 (hP (n + 1)))
  exact hJ.qcongr coeffA1_late (hJ.qsub (hJ.qadd (hJ.qsub (hJ.qadd t1 t2) t3) t4) t5)

/-- **The `A₁` block from the jets** (`JQ 1 2 A₁`, block extraction). -/
theorem ringLateA1_of_jets (hJ : JetCalculus) (hψ : ∀ n, JQ n (1 / 2) psiFam)
    (hP : ∀ n, JE n presFam) : RingLateA1 := by
  have h := lateStmt_of_JQ coeffA₁ 2 (a1Jets_of hJ hψ hP 1)
  rw [show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] at h
  exact h

/-- **`PartII-a:R02/8`, conditional on the calculus and the word statements.** -/
theorem ringLateA1_of_parts (hT : JetToolkit) (hF : FluctWords)
    (hM : WordsW (1 / 2) meanFam) : RingLateA1 :=
  ringLateA1_of_jets hT.jc (fun n => (baseJets_of hT.jc hT.wordE hT.wordW hF hM n).2.2.2)
    (fun n => (baseJets_of hT.jc hT.wordE hT.wordW hF hM n).2.2.1)

end UnforcedLeray.Short.PartIIa.Jet
