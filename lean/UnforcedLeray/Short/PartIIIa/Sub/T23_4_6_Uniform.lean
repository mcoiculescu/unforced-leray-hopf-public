import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves

/-!
# Part III-a, `PartIII-a:T23/4/6/org`: the Part I transverse tails in the uniform form

Source of record: `the November 2 reference manuscript`, `sct:transverse`
(lines 463-467) with the polynomial convention of lines 255-258 ("The letter `P` denotes a
polynomial in `c, ν^{-1}`, with degree depending only on the fixed collection; `P_S` may also
depend polynomially on `1+S`. All the smallness conditions below are satisfied by first fixing that
collection and then decreasing `e_c`").

`PartI.TrainTransverseTails` (`Short/PartI/StatementsTrain.lean`) fixes `b, C₀, C', C, N, ν₀` before
the horizon `S_*`, as the source does.  Part III-a uses it at `S_* = ε^{-b} = e^{bd/ν}`
(`stress-short:transverse`, lines 2739-2753) through `TrainTransverseTailsUniform`
(`Sub/T23_4_Leaves.lean`), which states the same bound with the period passed as a variable
`c = trainPeriod ρ ν` and `S_*` quantified after the train.  The two statements are equivalent:
`trainTransverseTails_of_uniform` (in `T23_4_Leaves.lean`) and `trainTransverseTailsUniform_of`
(here) are the two directions.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- `PartI.TrainTransverseTails` (SP 463-467, constants fixed before `S_*` as in SP 255-258) gives
the uniform form used in Part III-a: only the order of the quantifiers over `S_*` and the train
changes, and the period is passed as `c` with `c = trainPeriod ρ ν`. -/
theorem trainTransverseTailsUniform_of (h : UnforcedLeray.Short.PartI.TrainTransverseTails) :
    TrainTransverseTailsUniform := by
  intro ρ hρ ℓ j
  obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, hT⟩ := h ρ hρ ℓ j
  refine ⟨b, C₀, C', C, N, ν₀, hb, hC₀, hC', hC, hν₀,
    fun ν hν hνle c hc tr htr S_ hS l hl s hs hsS z hz => ?_⟩
  subst hc
  exact hT S_ hS ν hν hνle tr htr l hl s hs hsS z hz

end UnforcedLeray.Short.IIIa

end
