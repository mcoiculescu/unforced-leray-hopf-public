import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc
import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Sub.R02_2
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MeanStressSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/7`: the words of the mean stress

Source: `the November 2 reference manuscript`, lines 397-404 (`g = \overline{v₁v₂}`)
and 439-446.  The mean stress is smooth for `s > 0` (`MeanStressSmooth`), its words without `∂_q`
are exponentially small (`LateMeanStress`), and it does not depend on `q`, so every word with
`∂_q` vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanStream meanStress)

/-- **The words of the mean stress** (task `PartII-a:R02/12/7`). -/
theorem stressWords_of (h : UnforcedLeray.Short.PartIIa.LateIngredients) :
    UnforcedLeray.Short.PartIIa.Jet.A2.StressWords := by
  have hE0 : partialEta (0 : ProfilePoint → ℝ) = 0 :=
    funext fun y => by
      show fderiv ℝ (fun _ : ProfilePoint => (0 : ℝ)) y eηDir = 0
      simp
  have hQ0 : partialQ (0 : ProfilePoint → ℝ) = 0 :=
    funext fun y => by
      show fderiv ℝ (fun _ : ProfilePoint => (0 : ℝ)) y eqDir = 0
      simp
  have hA0 : partialAge (0 : ProfilePoint → ℝ) = 0 :=
    funext fun y => by
      show fderiv ℝ (fun _ : ProfilePoint => (0 : ℝ)) y esDir = 0
      simp
  have hK0 : ageOperator (0 : ProfilePoint → ℝ) = 0 :=
    funext fun y => by
      show y.2.1 * partialEta (0 : ProfilePoint → ℝ) y
        + 2 * y.2.2 * partialAge (0 : ProfilePoint → ℝ) y = 0
      rw [hE0, hA0]
      simp
  -- the mean stress does not depend on `q`, so `∂_q` of it vanishes
  have hq0 : ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c),
      partialQ (stressFam ν c tr) = 0 := by
    intro ν c tr
    funext x
    have key : ∀ y : ProfilePoint, stressFam ν c tr y = meanStress tr y.2.2 y.2.1 :=
      fun y => rfl
    have hqi : ∀ y z : ProfilePoint, y.2 = z.2 → stressFam ν c tr y = stressFam ν c tr z := by
      intro y z hyz
      have h1 : y.2.1 = z.2.1 := congrArg (fun p => p.1) hyz
      have h2 : y.2.2 = z.2.2 := congrArg (fun p => p.2) hyz
      rw [key, key, h1, h2]
    show fderiv ℝ (stressFam ν c tr) x eqDir = 0
    by_cases hd : DifferentiableAt ℝ (stressFam ν c tr) x
    · rw [← hd.lineDeriv_eq_fderiv]
      have hc' : (fun t : ℝ => stressFam ν c tr (x + t • eqDir))
          = fun _ => stressFam ν c tr x :=
        funext fun t => hqi _ _ (by simp [eqDir])
      unfold lineDeriv
      rw [hc', deriv_const]
    · rw [fderiv_zero_of_not_differentiableAt hd]
      rfl
  unfold StressWords WordsE
  refine ⟨?_, fun ℓ a b => ?_⟩
  · intro ν c hν hc tr htr
    exact UnforcedLeray.Short.PartIIa.contDiffOn_trainProfile_of_eta
      (G := fun s η => meanStress tr s η)
      ((UnforcedLeray.Short.PartIIa.meanStressSmooth_of
        UnforcedLeray.Short.PartI.hmeanContDiff) ν c hν hc tr htr).1
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      intro ρ m hρ
      obtain ⟨C, N, κ, ν₀, hκ, hν₀, hbd⟩ := h.stress ρ m a ℓ hρ
      refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
      intro ν hν hνv tr htr x hx1
      exact hbd ν hν hνv tr htr x hx1
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hL : LateEq (wordE ℓ a (b' + 1) stressFam) 0 := by
        intro ν c _ _ tr _ x _
        have hpart : partialQ^[b' + 1] (stressFam ν c tr) = 0 := by
          rw [Function.iterate_succ_apply, hq0 ν c tr, Function.iterate_fixed hQ0 b']
        show ageOperator^[ℓ] (partialEta^[a] (partialQ^[b' + 1] (stressFam ν c tr))) x
          = (0 : ProfilePoint → ℝ) x
        rw [hpart, Function.iterate_fixed hE0 a, Function.iterate_fixed hK0 ℓ]
      exact WE.congr hL.symm WE.zero

end UnforcedLeray.Short.PartIIa.Jet.A2
