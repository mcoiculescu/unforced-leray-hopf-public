import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Leaves

/-!
# Complex flows from the real Volterra family (source 2819-2836)

Source of record: `the November 2 reference manuscript` (73 pages).

`flowOfRealFamily_of`: the gluing of `Exist.fullFlowExists_of_family` (`Sub/T21_3.lean`) for one
cocycle `E` of real operators and one complex datum `a + i b`, from the four flow lemmas
`LinFlowComb`, `FlowCongrAE`, `FlowAppend`, `FlowGlobal` (accepted: `PartIII-a:T21/3/9/1`,
`/11`, `/10`, `/12`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Short.IIIa.Exist

/-- **`FlowOfRealFamily`** from the four flow lemmas (source 2819-2836). -/
theorem flowOfRealFamily_of (hL : LinFlowComb) (hCongr : FlowCongrAE) (hApp : FlowAppend)
    (hGlob : FlowGlobal) : FlowOfRealFamily := by
  intro ν c m _ hm tr E hcoc hstrip t ht a b f ω hf hω
  refine hGlob ν c m tr t f ω _ (fun N => ?_)
  induction N with
  | zero =>
    have e : t + ((0 + 1 : ℕ) : ℝ) = t + 1 := by norm_num
    rw [e]
    have h1 := hL ν c m tr t (t + 1) _ _ _ _ _ _ (hstrip t ht a) (hstrip t ht b)
    exact hCongr ν c m tr t (t + 1) _ f _ ω _ _ (by linarith) h1 hf.symm
      (fun s hs => (hω s hs.1).symm) (fun s _ => Filter.EventuallyEq.rfl)
  | succ N ih =>
    set a' : ℝ := t + ((N + 1 : ℕ) : ℝ) with ha'
    have hta' : t ≤ a' := by
      rw [ha']
      have : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have ha'0 : 0 ≤ a' := ht.trans hta'
    have h1 := hL ν c m tr a' (a' + 1) _ _ _ _ _ _ (hstrip a' ha'0 (E a' t a))
      (hstrip a' ha'0 (E a' t b))
    have h2 : IsLinFlowOn ν c m tr a' (a' + 1) (ω a') ω
        (fun s x j => stripVel hm (E s t a) x j + Complex.I * stripVel hm (E s t b) x j) := by
      refine hCongr ν c m tr a' (a' + 1) _ (ω a') _ ω _ _ (by linarith) h1 (hω a' hta').symm
        (fun s hs => ?_) (fun s hs => ?_)
      · show (fun x => cplx (vortFn hm (E s a' (E a' t a))) x +
            Complex.I * cplx (vortFn hm (E s a' (E a' t b))) x) =ᵐ[volume.restrict (B0579.cell c)]
          ω s
        rw [hcoc t a' s ht hta' hs.1 a, hcoc t a' s ht hta' hs.1 b]
        exact (hω s (hta'.trans hs.1)).symm
      · refine Filter.EventuallyEq.of_eq ?_
        show (fun x j => stripVel hm (E s a' (E a' t a)) x j +
            Complex.I * stripVel hm (E s a' (E a' t b)) x j) = _
        rw [hcoc t a' s ht hta' hs.1 a, hcoc t a' s ht hta' hs.1 b]
    have hjoin : t + ((N + 1 + 1 : ℕ) : ℝ) = a' + 1 := by
      rw [ha']
      push_cast
      ring
    rw [hjoin]
    exact hApp ν c m tr t a' (a' + 1) f ω _ hta' (by linarith) ih h2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
